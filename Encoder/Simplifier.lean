import Encoder.Basic

namespace SMT

def subst (x : 𝒱) (t e : Term) : Term :=
  match e with
  | Term.var v => if v = x then t else e
  | Term.mul a b => .mul (subst x t a) (subst x t b)
  | Term.add a b => .add (subst x t a) (subst x t b)
  | Term.sub a b => .sub (subst x t a) (subst x t b)
  | Term.le a b => .le (subst x t a) (subst x t b)
  | Term.pair a b => .pair (subst x t a) (subst x t b)
  | Term.some a => .some (subst x t a)
  | Term.imp a b => .imp (subst x t a) (subst x t b)
  | Term.not a => .not (subst x t a)
  | Term.or a b => .or (subst x t a) (subst x t b)
  | Term.and a b => .and (subst x t a) (subst x t b)
  | Term.eq a b => .eq (subst x t a) (subst x t b)
  | Term.forall vs τs body => if x ∈ vs then .forall vs τs body else .forall vs τs (subst x t body)
  | Term.exists vs τs body => if x ∈ vs then .exists vs τs body else .exists vs τs (subst x t body)
  | Term.lambda vs τs body => if x ∈ vs then .lambda vs τs body else .lambda vs τs (subst x t body)
  | Term.app f a => .app (subst x t f) (subst x t a)
  | Term.distinct ts => .distinct (ts.attach.map (λ ⟨e, _⟩ => subst x t e))
  | Term.snd p => .snd (subst x t p)
  | Term.fst p => .fst (subst x t p)
  | Term.none => .none
  | Term.the e => .the (subst x t e)
  | Term.ite c ct cf => .ite (subst x t c) (subst x t ct) (subst x t cf)
  | Term.as a τ => .as (subst x t a) τ
  | Term.builtin f τ args => .builtin f τ (args.attach.map (λ ⟨e, _⟩ => subst x t e))
  | Term.bool b => .bool b
  | Term.int n => .int n


-- e[xs[i] ← ts[i]] for all i
def substList (xs : List 𝒱) (ts : List Term) (e : Term) : Term :=
  match xs, ts with
  | x :: xs, t :: ts => substList xs ts (subst x t e)
  | _, _ => e

/-! ### One-point elimination

The loosening layer states every cast as "there is a value related to the
source", even when the relation is the identity: `castPath.pair` on two
reflexive components emits `∃ a b. p = ⟨a,b⟩ ∧ a = fst q ∧ b = snd q`, which
says no more than `p = q`.  Every such binder is a variable the solver has to
instantiate, and the shape nests once per level of type structure, so the cost
grows with the type order — exactly where the encoder loses ground.

The rewrites below are the standard one-point rules,

* `∃ v⃗. … ∧ v = t ∧ …`  ⟶  the rest with `t` for `v`   (`v ∉ fv t`),
* `∀ v⃗. … ⇒ v = t ⇒ …`  ⟶  the rest with `t` for `v`,

plus their `Pair` analogues, which hold because `Pair` has a single
constructor and is therefore surjective:

* `∃ a b. … ∧ x = ⟨a,b⟩ ∧ …`  ⟶  the rest with `fst x` / `snd x`.

All four are equivalences, so nothing is gained or lost logically; what changes
is how much the solver has to guess. -/

/-- Terms cheap enough to duplicate at every occurrence of the binder they
replace.  Restricting substitution to these keeps the rule from copying a
lambda — the specification of a cast helper — into a dozen positions, which
would trade quantifiers for size. -/
private def duplicable : Term → Bool
  | .var _ | .int _ | .bool _ | .none => true
  | .fst t | .snd t | .the t | .some t | .as t _ => duplicable t
  | .pair a b => duplicable a && duplicable b
  | _ => false

private def conjuncts : Term → List Term
  | .and a b => conjuncts a ++ conjuncts b
  | t => [t]

private def andAll : List Term → Term
  | [] => .bool true
  | [t] => t
  | t :: ts => .and t (andAll ts)

/-- The antecedents of an implication chain, flattened through conjunctions
(`(p ∧ q) ⇒ r` is `p ⇒ q ⇒ r`), together with the final conclusion. -/
private def antecedents : Term → List Term × Term
  | .imp a b => let (as, c) := antecedents b; (conjuncts a ++ as, c)
  | t => ([], t)

/-- Read one side of an equation as a definition of a single binder. -/
private def solveSideVar (vs : List 𝒱) : Term → Term → Option (List 𝒱 × List (𝒱 × Term))
  | .var v, t =>
    if vs.contains v && duplicable t && !(fv t).contains v then
      some ([v], [(v, t)])
    else none
  | _, _ => none

/-- Read one side of an equation as a definition of a pair of binders, using
that `Pair` is surjective: `x = ⟨a,b⟩` determines `a` and `b` as `fst x` and
`snd x`. -/
private def solveSidePair (vs : List 𝒱) : Term → Term → Option (List 𝒱 × List (𝒱 × Term))
  | .pair (.var a) (.var b), x =>
    if vs.contains a && vs.contains b && a != b && duplicable x
        && !(fv x).contains a && !(fv x).contains b then
      some ([a, b], [(a, .fst x), (b, .snd x)])
    else none
  | _, _ => none

private def solveEq (side : List 𝒱 → Term → Term → Option (List 𝒱 × List (𝒱 × Term)))
    (vs : List 𝒱) : Term → Option (List 𝒱 × List (𝒱 × Term))
  | .eq a b => (side vs a b).orElse fun _ => side vs b a
  | _ => none

/-- The first of `cs` that pins binders of `vs`, as the binders removed, the
substitution it licenses, and the conjuncts left. -/
private def scanFor (side : List 𝒱 → Term → Term → Option (List 𝒱 × List (𝒱 × Term)))
    (vs : List 𝒱) :
    List Term → List Term → Option (List 𝒱 × List (𝒱 × Term) × List Term)
  | _, [] => none
  | seen, c :: rest =>
    match solveEq side vs c with
    | some (elim, σ) => some (elim, σ, seen.reverse ++ rest)
    | none => scanFor side vs (c :: seen) rest

/-- Single-variable equations are tried before pair ones: `p = ⟨a,b⟩` with
`a = fst q` and `b = snd q` alongside collapses to `p = q` when the components
are eliminated first, and to the strictly larger `fst p = fst q ∧ snd p = snd q`
when the pair is. -/
private def firstSolvable (vs : List 𝒱) (cs : List Term) :
    Option (List 𝒱 × List (𝒱 × Term) × List Term) :=
  (scanFor solveSideVar vs [] cs).orElse fun _ => scanFor solveSidePair vs [] cs

private def applySubst (σ : List (𝒱 × Term)) (t : Term) : Term :=
  σ.foldl (fun acc (v, s) => subst v s acc) t

/-- Whether substituting `σ` into `rest` would capture.

`subst` does not rename, so a replacement mentioning a name that `rest` binds
would change what that name refers to.  Encoder-generated names are globally
unique, but source names are not — Atelier B numbers binders per scope, which is
why `saveShadowed` exists — so the check is made rather than assumed. -/
private def capturing (σ : List (𝒱 × Term)) (rest : List Term) : Bool :=
  let bound := (rest.map bv).flatten
  σ.any fun (_, s) => (fv s).any bound.contains

/-- `∃ v⃗. body` with one binder eliminated, or `none` if no conjunct pins one. -/
private def onePointExists (vs : List 𝒱) (τs : List SMTType) (body : Term) :
    Option Term :=
  match firstSolvable vs (conjuncts body) with
  | none => none
  | some (elim, σ, rest) =>
    if capturing σ rest then none else
    let inner := andAll (rest.map (applySubst σ))
    let keep := (vs.zip τs).filter fun (v, _) => !elim.contains v
    some <| if keep.isEmpty then inner
            else .exists (keep.map Prod.fst) (keep.map Prod.snd) inner

/-- `∀ v⃗. body` with one binder eliminated by an antecedent that pins it. -/
private def onePointForall (vs : List 𝒱) (τs : List SMTType) (body : Term) :
    Option Term :=
  let (as, concl) := antecedents body
  match firstSolvable vs as with
  | none => none
  | some (elim, σ, rest) =>
    if capturing σ (concl :: rest) then none else
    let inner := (rest.map (applySubst σ)).foldr (.imp · ·) (applySubst σ concl)
    let keep := (vs.zip τs).filter fun (v, _) => !elim.contains v
    some <| if keep.isEmpty then inner
            else .forall (keep.map Prod.fst) (keep.map Prod.snd) inner

partial def simplifier : Term → Term
  | Term.app (.var "NATURAL") x => .le (.int 0) x
  | Term.app (.var "NATURAL1") x => .le (.int 1) x
  | Term.app (.var "NAT") x => .and (.le (.int 0) x) (.le x (.int B.MAXINT))
  | Term.app (.var "INTEGER") _ => .bool true
  | Term.app (.var "INT") x => .and (.le (.int B.MININT) x) (.le x (.int B.MAXINT))
  | Term.app (.var "BOOL") _ => .bool true
  | Term.app (.lambda [v] [_] e) x => subst v x e
  | Term.app (.lambda (v::vs) (_::τs) e) x => .lambda vs τs (subst v x e)
  | Term.app f x => .app (simplifier f) (simplifier x)
  | Term.mul a b => .mul (simplifier a) (simplifier b)
  | Term.add (.int x) (.int y) => .int (x+y)
  | Term.add a b => .add (simplifier a) (simplifier b)
  | Term.le a b => bif a == b then .bool true else .le (simplifier a) (simplifier b)
  | Term.fst (.pair a b) => simplifier a
  | Term.snd (.pair a b) => simplifier b
  | Term.fst t => .fst (simplifier t)
  | Term.snd t => .snd (simplifier t)
  | Term.pair (.fst x) (.snd x') =>
    let simpx := simplifier x
    let simpx' := simplifier x'
    if simpx == simpx' then simpx else .pair simpx.fst simpx'.snd
  | Term.pair a b => .pair (simplifier a) (simplifier b)
  | Term.some (.the a) => (simplifier a)
  | Term.some a => .some (simplifier a)
  | Term.the (.some t) => simplifier t
  | Term.the t => .the (simplifier t)
  | Term.imp (.bool true) p => p
  | Term.imp (.bool false) _ | .imp _ (.bool true) => .bool true
  | Term.imp p q => .imp (simplifier p) (simplifier q)
  | Term.or (.bool false) p | .or p (.bool false) => p
  | Term.or (.bool true) _ | .or _ (.bool true) => .bool true
  | Term.or (.not p) q => .imp p q
  | Term.or (.exists vs τs p) q => .imp (.forall vs τs (.not p)) q
  | Term.or p q => .or (simplifier p) (simplifier q)
  | Term.not (.not p) => p
  | Term.not (.forall vs τs (.not p)) => .exists vs τs p
  | Term.not (.forall vs τs (.imp p q)) => .exists vs τs (.and p (.not q))
  | Term.not (.exists vs τs p) => .forall vs τs (.not p)
  -- | Term.not (.imp p q) => .and p (.not q)
  | Term.not (.bool b) => .bool !b
  | Term.not (.and p q) => .or (.not p) (.not q)
  | Term.not (.or p q) => .and (.not p) (.not q)
  | Term.not p => .not (simplifier p)
  | Term.and (.bool false) _ | .and _ (.bool false) => .bool false
  | Term.and (.bool true) p | .and p (.bool true) => p
  | Term.and a b => .and (simplifier a) (simplifier b)
  | Term.eq (.pair x y) (.pair u v) => .and (.eq x u) (.eq y v)
  | Term.eq (.bool true) p | .eq p (.bool true) => p
  | Term.eq (.bool false) p | .eq p (.bool false) => .not p
  | Term.eq a b => if a == b then .bool true else .eq (simplifier a) (simplifier b)
  | Term.exists _ _ (.bool b) => .bool b
  | Term.exists vs τs e =>
    match onePointExists vs τs e with
    | some t => t
    | none => .exists vs τs (simplifier e)
  | Term.forall _ _ (.bool b) => .bool b
  | Term.forall vs τs e =>
    match onePointForall vs τs e with
    | some t => t
    | none => .forall vs τs (simplifier e)
  | Term.lambda vs τs e => .lambda vs τs (simplifier e)
  | Term.ite (.bool true) t _ | .ite (.bool false) _ t => t
  | Term.ite c t e => .ite (simplifier c) (simplifier t) (simplifier e)
  | Term.sub a b => .sub (simplifier a) (simplifier b)
  | Term.distinct [] => .bool true
  | Term.distinct [_] => .bool true
  | Term.distinct ts => .distinct (ts.map simplifier)
  | Term.none => .none
  | Term.as e τ => .as e τ
  | Term.builtin f τ args => .builtin f τ (args.map simplifier)
  | Term.bool b => .bool b
  | Term.int n => .int n
  | Term.var v => .var v

partial def simplify_aux (t : Term) : Term := simplifier_aux t <| simplifier t
  where simplifier_aux (t t' : Term) : Term := if t == t' then t else simplifier_aux t' <| simplifier t'

def simplify (i : Instr) : Instr :=
  match i with
  | .assert t => .assert <| simplify_aux t
  | .define_const v τ i => .define_const v τ <| simplify_aux i
  | .define_fun v τ σ i => .define_fun v τ σ <| simplify_aux i
  | _ => i

def simpAsserts : Stages → Stages
  | .instr is => .instr <| is.map simplify
  | .asserts as => .asserts <| as.attach.map (λ ⟨a, _⟩ => simpAsserts a)

/-- Re-scope the helper constants a binder body introduced.

Cast helpers and the constants behind `card`/`min`/`finite` are declared
globally, with their specification asserted at the enclosing position.  Inside
`collect` or `lambda` that is wrong as soon as the specification mentions the
bound variables: the body is about to be abstracted over a fresh tuple `z` with
`vs` substituted away, and a hoisted specification would not follow.

Each helper `h : σ` therefore becomes a function `h^ : τ → σ`; occurrences of
`h` become `h^ z`, and the specification `Φ(h, vs)` becomes
`∀ z : τ. Φ(h^ z, destructure z)`.  That is the skolemised form of "for every
`z` there is a helper satisfying `Φ`", which is what the body already meant, so
nothing is assumed that was not.

`subs` is the destructuring of `z` that the caller will substitute for `vs`.
Returns the body with the helper occurrences rewritten. -/
def rescopeHelpers (before : Nat) (vs : List 𝒱) (subs : List Term)
    (z : 𝒱) (τ : SMTType) (body : Term) : Encoder Term := do
  let st ← get
  let new := st.env.declarations.extract before
  let helpers := new.filterMap fun | .declare_const v _ => some v | _ => none
  if helpers.isEmpty then return body
  let applyRen := fun t =>
    helpers.foldl (fun acc h => subst h (.app (.var s!"{h}^") (.var z)) acc) t
  let new' ← new.mapM fun
    | .declare_const v σ => do
      eraseFromContext v
      addToContext s!"{v}^" (.fun τ σ)
      return .declare_const s!"{v}^" (.fun τ σ)
    -- `addSpec` emits the specification as `define-fun h_spec () Bool …`; the
    -- name is kept so the already-emitted `(assert h_spec)` still refers to it.
    | .define_fun n .unit .bool b =>
      return .define_fun n .unit .bool (.forall [z] [τ] (applyRen (substList vs subs b)))
    | i => return i
  modify fun e =>
    { e with
      env := { e.env with declarations := e.env.declarations.take before ++ new' }
      -- A site recorded while encoding the body now names a constant that no
      -- longer exists under that name; forget it, so a later occurrence of the
      -- same argument introduces a fresh constant rather than referring to a
      -- renamed one.  Costs sharing, not correctness.
      sites := e.sites.filter (fun s => s.name ∉ helpers) }
  return applyRen body

nonrec def Env.simplify (E : Env) : Env :=
  -- dbg_trace "{E.declarations[0]!} ---> {simplify E.declarations[0]!}"
  { E with
    declarations := E.declarations.map simplify
    asserts := simpAsserts E.asserts
  }

end SMT
