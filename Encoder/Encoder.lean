import Encoder.Simplifier
import Encoder.Loosening
import SMT.Check

open Batteries SMT

def B.Term.vars (t : B.Term) : List B.𝒱 :=
  fv t ∪ bv t

namespace B

end B

def B.SimpleGoal.vars (g : B.SimpleGoal) : List B.𝒱 :=
  (g.hyps.map B.Term.vars).flatten ++ g.goal.vars

/-- Every name the obligation mentions.  The local context and flags are listed
too, even though a name that occurs in no term cannot clash with anything the
encoder emits: `freshVar` only consults this set, so a source name missing from
it could be handed out a second time. -/
def B.ProofObligation.vars (po : B.ProofObligation) : List B.𝒱 :=
  (po.defs.map B.Term.vars).flatten ++
  (po.hyps.map B.Term.vars).flatten ++
  (po.goals.map B.SimpleGoal.vars).flatten ++
  po.localContext.keys ++ po.localFlags

def B.Env.initialUsedVars (E : B.Env) : List B.𝒱 := Id.run do
  let mut used := E.context.keys
  used := E.flags ++ used
  for ⟨v, d⟩ in E.defs.entries do
    used := v :: d.vars ++ used
  for ⟨_, hs⟩ in E.hypotheses do
    used := (hs.map B.Term.vars).flatten ++ used
  for ds in E.distinct do
    used := (ds.map B.Term.vars).flatten ++ used
  used := (E.finite.map B.Term.vars).flatten ++ used
  used := (E.po.map B.ProofObligation.vars).flatten ++ used
  return used

/-- `∀ x : τ. S x ⇒ T x` — extensional inclusion of two characteristic
predicates, used to relate cardinality and finiteness sites. -/
private def subsetOf (τ : SMTType) (S T : SMT.Term) : Encoder SMT.Term := do
  let x ← freshVar τ
  SMT.eraseFromContext x
  return .forall [x] [τ] (.imp (.app S (.var x)) (.app T (.var x)))

/-- `∀ x : τ. ¬ S x`. -/
private def emptyOf (τ : SMTType) (S : SMT.Term) : Encoder SMT.Term := do
  let x ← freshVar τ
  SMT.eraseFromContext x
  return .forall [x] [τ] (.not (.app S (.var x)))

/-- Reify an encoded set into characteristic-predicate form, returning it with
its element type.

A B set of pairs may be stored as a partial function `α → Option β`.  Operators
that are about the set itself — `card`, `finite` — mean the set of pairs either
way (`|{0 ↦ 1, 1 ↦ 0}| = 2` is the cardinality of a partial function), so the
graph is materialised first.  This is the same representation join `pow`
performs. -/
private def asCharPred (op : String) (S : SMT.Term) (τS : SMTType) :
    Encoder (SMT.Term × SMTType) := do
  match τS with
  | .fun τ .bool => return (S, τ)
  | .fun α (.option β) => do
    let ⟨Sg, Sg_spec⟩ ← loosenAux_prf s!"{op}!"
      (castPath.graph (castPath.reflexive α) (castPath.reflexive β)) S
    declareConstWithSpec Sg (.fun (.pair α β) .bool) Sg_spec
    return (.var Sg, .pair α β)
  | _ => throw s!"encodeTerm:{op}: Expected a set, got {τS}"

/-- Encode `|S|` for an encoded set `S : τ → bool`.

SMT-LIB has no cardinality operator, and cvc5 has no parametric function
declarations (only parametric *datatypes*), so a single polymorphic `card`
symbol is not expressible.  Instead each occurrence gets its own integer
constant `card!i` constrained by

* `0 ≤ |S|`,
* `|S| = 0 ↔ S = ∅`,
* `S ⊆ T → |S| ≤ |T|` against every cardinality constant already introduced at
  the same element type (which also yields `S = T → |S| = |T|`).

These hold for finite sets.  B only defines `card` on finite sets and Atelier B
discharges the corresponding well-definedness obligations separately, so the
axioms are stated unguarded; the deliberately omitted rule is the successor law
`a ∉ S → |S ∪ {a}| = |S| + 1`, which together with `0 ≤ |S|` is inconsistent
once infinite sets are in scope. -/
private def encodeCard (S : SMT.Term) (τ : SMTType) : Encoder (SMT.Term × SMTType) := do
  if let some c ← SMT.findSite "card" S then
    return (.var c, .int)
  let prev ← SMT.sitesOf "card" τ
  let c ← freshVar .int "card!"
  let base := (.le (.int 0) (.var c)) ∧ˢ (.eq (.eq (.var c) (.int 0)) (← emptyOf τ S))
  let spec ← prev.foldlM (init := base) fun acc s => do
    let sub ← subsetOf τ S s.set
    let sup ← subsetOf τ s.set S
    return acc ∧ˢ (sub ⇒ˢ (.var c ≤ˢ .var s.name)) ∧ˢ (sup ⇒ˢ (.var s.name ≤ˢ .var c))
  declareConstWithSpec c .int spec
  recordSite ⟨"card", S, τ, c⟩
  return (.var c, .int)

/-- Encode `finite(S)` as a boolean constant closed under subsets.

The alternative — the B-Book definition, an existentially quantified injection
into an initial segment of ℕ — is a quantifier alternation per occurrence, and
enumerated SETS clauses emit one for every machine.  An uninterpreted constant
plus the facts that actually get used (∅ is finite, subsets of finite sets are
finite) is strictly weaker and far cheaper. -/
private def encodeFinite (S : SMT.Term) (τ : SMTType) : Encoder (SMT.Term × SMTType) := do
  if let some f ← SMT.findSite "fin" S then
    return (.var f, .bool)
  let prev ← SMT.sitesOf "fin" τ
  let f ← freshVar .bool "fin!"
  let base := (← emptyOf τ S) ⇒ˢ .var f
  let spec ← prev.foldlM (init := base) fun acc s => do
    let sub ← subsetOf τ S s.set
    let sup ← subsetOf τ s.set S
    return acc ∧ˢ ((sub ∧ˢ .var s.name) ⇒ˢ .var f) ∧ˢ ((sup ∧ˢ .var f) ⇒ˢ .var s.name)
  declareConstWithSpec f .bool spec
  recordSite ⟨"fin", S, τ, f⟩
  return (.var f, .bool)

/-- Encode `min S` / `max S` for an encoded set of integers.

`isMin` selects the comparison direction.  The defining property is guarded by
"`S` is non-empty and bounded on the relevant side", which is exactly B's
well-definedness condition for the operator: without the guard, asserting
`S(min S)` would force every set to be inhabited. -/
private def encodeExtremum (isMin : Bool) (S : SMT.Term) : Encoder (SMT.Term × SMTType) := do
  let op := if isMin then "min" else "max"
  if let some m ← SMT.findSite op S then
    return (.var m, .int)
  let m ← freshVar .int s!"{op}!"
  let cmp := fun (a b : SMT.Term) => if isMin then a ≤ˢ b else b ≤ˢ a
  let x ← freshVar .int; SMT.eraseFromContext x
  let b ← freshVar .int; SMT.eraseFromContext b
  let y ← freshVar .int; SMT.eraseFromContext y
  let z ← freshVar .int; SMT.eraseFromContext z
  let nonempty : SMT.Term := .exists [x] [.int] (.app S (.var x))
  let bounded : SMT.Term :=
    .exists [b] [.int] (.forall [y] [.int] (.imp (.app S (.var y)) (cmp (.var b) (.var y))))
  let extremal : SMT.Term :=
    (.app S (.var m)) ∧ˢ
      .forall [z] [.int] (.imp (.app S (.var z)) (cmp (.var m) (.var z)))
  declareConstWithSpec m .int ((nonempty ∧ˢ bounded) ⇒ˢ extremal)
  recordSite ⟨op, S, .int, m⟩
  return (.var m, .int)

/-- Encode `closure(R)` / `closure1(R)` for an encoded relation
`R : (α × α) → bool`.

The closure is a least fixpoint, which first-order SMT cannot define.  The
constant introduced here is instead constrained to be *some* transitive
relation containing `R` (plus reflexive for `closure`), i.e. an arbitrary
superset of the real closure.  That direction is the sound one for validity
checking: an obligation that holds for every such relation holds in particular
for the closure.  What is lost is the induction principle, so goals that need
the closure to be *least* — typically non-membership — stay unproved. -/
private def encodeClosure (refl : Bool) (R : SMT.Term) (α : SMTType) :
    Encoder (SMT.Term × SMTType) := do
  let op := if refl then "closure" else "closure1"
  let τ := SMTType.fun (.pair α α) .bool
  if let some c ← SMT.findSite op R then
    return (.var c, τ)
  let c ← freshVar τ s!"{op}!"
  let x ← freshVar α; SMT.eraseFromContext x
  let y ← freshVar α; SMT.eraseFromContext y
  let z ← freshVar α; SMT.eraseFromContext z
  let cl := fun (a b : SMT.Term) => SMT.Term.app (.var c) (.pair a b)
  let contains : SMT.Term :=
    .forall [x, y] [α, α] (.app R (.pair (.var x) (.var y)) ⇒ˢ cl (.var x) (.var y))
  let trans : SMT.Term :=
    .forall [x, y, z] [α, α, α]
      ((cl (.var x) (.var y) ∧ˢ cl (.var y) (.var z)) ⇒ˢ cl (.var x) (.var z))
  let spec :=
    if refl then contains ∧ˢ trans ∧ˢ .forall [x] [α] (cl (.var x) (.var x))
    else contains ∧ˢ trans
  declareConstWithSpec c τ spec
  recordSite ⟨op, R, α, c⟩
  return (.var c, τ)

/-- Encode `SIGMA`/`PI` over the values of `f`.

A fold has no first-order definition and no useful finite axiomatisation, so the
constant introduced here is only pinned down on the empty function — enough for
an obligation to mention `SIGMA` without the translation failing, not enough to
reason about its value.  Being under-constrained is the safe direction: the
solver may pick any value, so nothing becomes provable that was not. -/
private def encodeFold (isSum : Bool) (f : SMT.Term) (τ : SMTType)
    (isEmpty : SMT.Term) : Encoder (SMT.Term × SMTType) := do
  let op := if isSum then "sigma" else "pi"
  if let some c ← SMT.findSite op f then
    return (.var c, .int)
  let c ← freshVar .int s!"{op}!"
  declareConstWithSpec c .int (isEmpty ⇒ˢ (.var c =ˢ .int (if isSum then 0 else 1)))
  recordSite ⟨op, f, τ, c⟩
  return (.var c, .int)

/-- "`t` denotes the empty sequence", for either representation of one:
a characteristic predicate over pairs, or an option-valued function. -/
private def isEmptySeq (σ : SMTType) (t : SMT.Term) : Encoder (Option SMT.Term) := do
  match σ with
  | .fun (.pair α β) .bool => do
    let x ← freshVar α; SMT.eraseFromContext x
    let y ← freshVar β; SMT.eraseFromContext y
    return some <| .forall [x, y] [α, β] (¬ˢ .app t (.pair (.var x) (.var y)))
  | .fun α (.option β) => do
    let x ← freshVar α; SMT.eraseFromContext x
    return some <| .forall [x] [α] (.app t (.var x) =ˢ none$ β)
  | _ => return none

/-- Encode `conc(ss)`, the sequences in `ss` concatenated in order.

Unrolling the fold would need the length of each partial result inside a
quantified axiom, i.e. cardinality under a quantifier feeding another indexed
family — a shape no solver makes progress on.  The constant is therefore only
pinned down on the empty outer sequence, as for `SIGMA`/`PI`: enough for an
obligation to mention `conc` without the translation failing, and
under-constrained, so nothing becomes provable that was not. -/
private def encodeConc (ss : SMT.Term) (τss σ : SMTType) : Encoder (SMT.Term × SMTType) := do
  if let some c ← SMT.findSite "conc" ss then
    return (.var c, σ)
  let c ← freshVar σ "conc!"
  match ← isEmptySeq τss ss, ← isEmptySeq σ (.var c) with
  | some ssEmpty, some cEmpty => declareConstWithSpec c σ (ssEmpty ⇒ˢ cEmpty)
  | _, _ => declareConst c σ
  recordSite ⟨"conc", ss, σ, c⟩
  return (.var c, σ)

/-- Encode `iterate(R, n)` for a symbolic count.

Unlike `closure`, this one *is* definable: a family of relations indexed by the
iteration count, declared as `it : Int → (α × α) → bool` and pinned down by

* `it 0` is the identity,
* `it k = it (k-1) ; R` for `k > 0`,

which is the same shape as the prelude's `bpow` recursion, with an existential
for the intermediate point.  Negative counts are left unconstrained. -/
private def encodeIterate (R n : SMT.Term) (α : SMTType) :
    Encoder (SMT.Term × SMTType) := do
  let τ := SMTType.fun (.pair α α) .bool
  let c ← match ← SMT.findSite "iterate" R with
    | some c => pure c
    | none => do
      let c ← freshVar (.fun .int τ) "iter!"
      let k ← freshVar .int; SMT.eraseFromContext k
      let x ← freshVar α; SMT.eraseFromContext x
      let y ← freshVar α; SMT.eraseFromContext y
      let z ← freshVar α; SMT.eraseFromContext z
      let it := fun (i a b : SMT.Term) => SMT.Term.app (.app (.var c) i) (.pair a b)
      let base : SMT.Term :=
        .forall [x, y] [α, α] (it (.int 0) (.var x) (.var y) =ˢ (.var x =ˢ .var y))
      let step : SMT.Term :=
        .forall [k, x, y] [.int, α, α]
          ((.int 1 ≤ˢ .var k) ⇒ˢ
            (it (.var k) (.var x) (.var y) =ˢ
              .exists [z] [α]
                (it (.var k -ˢ .int 1) (.var x) (.var z) ∧ˢ
                  .app R (.pair (.var z) (.var y)))))
      declareConstWithSpec c (.fun .int τ) (base ∧ˢ step)
      recordSite ⟨"iterate", R, α, c⟩
      pure c
  return (.app (.var c) n, τ)

def encodeTerm : B.Term → B.Env → Encoder (SMT.Term × SMTType)
  | .var v, E => do
    match (←get).types.get? v with
    | none => throw s!"encodeTerm:var: Unknown variable {v} in SMT context"
    | some τ => do
      return (.var v, τ)
      -- let .some τ' := E.context.lookup v | return (.var v, τ) --FIXME: hack?
      --   -- throw s!"encodeTerm:var: Missing type for {v} in B context"
      -- if τ = τ'.toSMTType then
      --   return (.var v, τ)
      -- else
      --   throw s!"encodeTerm:var: Type mismatch for {v}: expected {τ}, got {τ'.toSMTType}"
  | .int n, _ => return (.int n, .int)
  | .bool b, _ => return (.bool b, .bool)
  -- | .imp x y, E => do
  --   let ⟨x', .bool⟩ ← encodeTerm x E | throw s!"encodeTerm:imp: Expected a boolean, got {← encodeTerm x E}"
  --   let ⟨y', .bool⟩ ← encodeTerm y E | throw s!"encodeTerm:imp: Expected a boolean, got {← encodeTerm y E}"
  --   return (.imp x' y', .bool)
  -- | .or x y, E => do
  --   let ⟨x', .bool⟩ ← encodeTerm x E | throw s!"encodeTerm:or: Expected a boolean, got {← encodeTerm x E}"
  --   let ⟨y', .bool⟩ ← encodeTerm y E | throw s!"encodeTerm:or: Expected a boolean, got {← encodeTerm y E}"
  --   return (.or x' y', .bool)
  | .and x y, E => do
    let ⟨x', .bool⟩ ← encodeTerm x E | throw s!"encodeTerm:and: Expected a boolean, got {← encodeTerm x E}"
    let ⟨y', .bool⟩ ← encodeTerm y E | throw s!"encodeTerm:and: Expected a boolean, got {← encodeTerm y E}"
    return (.and x' y', .bool)
  | .le x y, E => do
    return (.le (← encodeTerm x E).fst (← encodeTerm y E).fst, .bool)
  | .maplet x y, E => do
    let ⟨x', α⟩ ← encodeTerm x E
    let ⟨y', β⟩ ← encodeTerm y E
    return (.pair x' y', .pair α β)
  | .add x y, E => do
    let ⟨x', .int⟩ ← encodeTerm x E | throw s!"encodeTerm:add: Expected an integer, got {← encodeTerm x E}"
    let ⟨y', .int⟩ ← encodeTerm y E | throw s!"encodeTerm:add: Expected an integer, got {← encodeTerm y E}"
    return (.add x' y', .int)
  | .sub x y, E => do
    let ⟨x', .int⟩ ← encodeTerm x E | throw s!"encodeTerm:sub: Expected an integer, got {← encodeTerm x E}"
    let ⟨y', .int⟩ ← encodeTerm y E | throw s!"encodeTerm:sub: Expected an integer, got {← encodeTerm y E}"
    return (.sub x' y', .int)
  | .mul x y, E => do
    let ⟨x', .int⟩ ← encodeTerm x E | throw s!"encodeTerm:mul: Expected an integer, got {← encodeTerm x E}"
    let ⟨y', .int⟩ ← encodeTerm y E | throw s!"encodeTerm:mul: Expected an integer, got {← encodeTerm y E}"
    return (.mul x' y', .int)
  | .div x y, E => do
    let ⟨x', .int⟩ ← encodeTerm x E | throw s!"encodeTerm:div: Expected an integer, got {← encodeTerm x E}"
    let ⟨y', .int⟩ ← encodeTerm y E | throw s!"encodeTerm:div: Expected an integer, got {← encodeTerm y E}"
    return (.builtin "bdiv" .int [x', y'], .int)
  | .mod x y, E => do
    let ⟨x', .int⟩ ← encodeTerm x E | throw s!"encodeTerm:mod: Expected an integer, got {← encodeTerm x E}"
    let ⟨y', .int⟩ ← encodeTerm y E | throw s!"encodeTerm:mod: Expected an integer, got {← encodeTerm y E}"
    return (.builtin "bmod" .int [x', y'], .int)
  | .exp x y, E => do
    let ⟨x', .int⟩ ← encodeTerm x E | throw s!"encodeTerm:exp: Expected an integer, got {← encodeTerm x E}"
    let ⟨y', .int⟩ ← encodeTerm y E | throw s!"encodeTerm:exp: Expected an integer, got {← encodeTerm y E}"
    return (.builtin "bpow" .int [x', y'], .int)
  | .not x, E => do
    let ⟨x', .bool⟩ ← encodeTerm x E | throw s!"encodeTerm:not: Expected a boolean, got {← encodeTerm x E}"
    return (.not x', .bool)
  | .eq A B, E => do
    castEq (← encodeTerm A E) (← encodeTerm B E)
  | .ℤ, _ => do
    let ctx := (←get).types
    let v ← freshVar .int
    modify λ e => { e with types := ctx } -- rollback context but keep freshvarsc incremented
    return (.lambda [v] [.int] (.bool true), .fun .int .bool)
  | .𝔹, _ => do
    let ctx := (←get).types
    let v ← freshVar .bool
    modify λ e => { e with types := ctx } -- rollback context but keep freshvarsc incremented
    return (.lambda [v] [.bool] (.bool true), .fun .bool .bool)
  | .mem x S, E => do
    let x' ← encodeTerm x E
    let S' ← encodeTerm S E
    -- Report which source membership failed: the cast helpers only see SMT
    -- types, which is rarely enough to find the construct responsible.
    try castMembership x' S'
    catch e => throw s!"{e}\n  in: {(toString x).take 120} ∈ {(toString S).take 200}"
  | .pow S, E => do
    let ⟨S', τS⟩ ← encodeTerm S E
    match τS with
    | .fun α .bool => do -- `S` is a set
      let ctx := (←get).types
      let x ← freshVar α
      let ℰ ← freshVar <| .fun α .bool
      modify λ e => { e with types := ctx } -- rollback context but keep freshvarsc incremented
      return (.lambda [ℰ] [.fun α .bool] (.forall [x] [α] (.imp (.app (.var ℰ) (.var x)) (.app S' (.var x)))), .fun (.fun α .bool) .bool)
    | .fun α (.option β) => do -- `S` is a function
      -- Reify the option-function as its canonical relation graph before
      -- forming the powerset. This is the same representation join used by
      -- union/intersection and keeps the result at the canonical set type.
      let ⟨Sg, Sg_spec⟩ ← loosenAux_prf "pow!"
        (castPath.graph (castPath.reflexive α) (castPath.reflexive β)) S'
      declareConstWithSpec Sg (.fun (.pair α β) .bool) Sg_spec
      let ctx := (←get).types
      let p ← freshVar (.pair α β)
      let R ← freshVar <| .fun (.pair α β) .bool
      modify λ e => { e with types := ctx } -- rollback context but keep freshvarsc incremented
      return (.lambda [R] [.fun (.pair α β) .bool]
        (.forall [p] [.pair α β]
          (.imp (.app (.var R) (.var p))
            (.app (.var Sg) (.var p)))),
        .fun (.fun (.pair α β) .bool) .bool)
    | _ => throw s!"encodeTerm:pow: Expected a set or a function, got {τS}"
  | .cprod A B, E => do
    let ⟨A', .fun α .bool⟩ ← encodeTerm A E | throw s!"encodeTerm:cprod: Expected a set, got {← encodeTerm A E}"
    let ⟨B', .fun β .bool⟩ ← encodeTerm B E | throw s!"encodeTerm:cprod: Expected a set, got {← encodeTerm B E}"
    let p ← freshVar (.pair α β); let a ← freshVar α; let b ← freshVar β
    -- `p`, `a`, `b` are only the `λ`/`∃` binders below; erase them from the global
    -- type context so the result stays typeable there (re-introduced by the binders).
    SMT.eraseFromContext p; SMT.eraseFromContext a; SMT.eraseFromContext b
    -- λ p:α×β.∃ a:α,b:β. a ∈ A ∧ b ∈ B ∧ p = a ↦ b
    return (.lambda [p] [.pair α β] (.exists [a, b] [α, β] (.and (.app A' (.var a)) (.and (.app B' (.var b)) (.eq (.var p) (.pair (.var a) (.var b)))))),
      .fun (.pair α β) .bool)
  | .union S T, E => do
    castUnion (← encodeTerm S E) (← encodeTerm T E)
  | .inter S T, E => do
    castInter (← encodeTerm S E) (← encodeTerm T E)
  | .card S, E => do
    let ⟨S', τS⟩ ← encodeTerm S E
    let ⟨Sc, τ⟩ ← asCharPred "card" S' τS
    encodeCard Sc τ
  | .finite S, E => do
    let ⟨S', τS⟩ ← encodeTerm S E
    let ⟨Sc, τ⟩ ← asCharPred "finite" S' τS
    encodeFinite Sc τ
  | .fold isSum f, E => do
    let ⟨f', τf⟩ ← encodeTerm f E
    match τf with
    | .fun τ (.option .int) => do
      let x ← freshVar τ; SMT.eraseFromContext x
      encodeFold isSum f' τ
        (.forall [x] [τ] (.app f' (.var x) =ˢ none$ .int))
    | .fun (.pair τ .int) .bool => do
      let x ← freshVar τ; SMT.eraseFromContext x
      let n ← freshVar .int; SMT.eraseFromContext n
      encodeFold isSum f' τ
        (.forall [x, n] [τ, .int] (¬ˢ .app f' (.pair (.var x) (.var n))))
    | _ => throw s!"encodeTerm:fold: Expected an integer-valued function, got {τf}"
  | .conc _ ss, E => do
    let ⟨ss', τss⟩ ← encodeTerm ss E
    -- The element type of the outer sequence is the type of the result: the
    -- concatenation of sequences of type σ is again a sequence of type σ.
    match τss with
    | .fun (.pair .int σ) .bool | .fun .int (.option σ) => encodeConc ss' τss σ
    | _ => throw s!"encodeTerm:conc: Expected a sequence of sequences, got {τss}"
  | .iterate R n, E => do
    let ⟨n', .int⟩ ← encodeTerm n E
      | throw s!"encodeTerm:iterate: Expected an integer count, got {(← encodeTerm n E).2}"
    let ⟨R', τR⟩ ← encodeTerm R E
    match τR with
    | .fun (.pair α β) .bool =>
      unless α == β do
        throw s!"encodeTerm:iterate: Expected a homogeneous relation, got {τR}"
      encodeIterate R' n' α
    | .fun α (.option β) => do
      unless α == β do
        throw s!"encodeTerm:iterate: Expected a homogeneous relation, got {τR}"
      let ⟨Rg, Rg_spec⟩ ← loosenAux_prf "iter!"
        (castPath.graph (castPath.reflexive α) (castPath.reflexive β)) R'
      declareConstWithSpec Rg (.fun (.pair α β) .bool) Rg_spec
      encodeIterate (.var Rg) n' α
    | _ => throw s!"encodeTerm:iterate: Expected a relation, got {τR}"
  | .closure refl R, E => do
    let ⟨R', τR⟩ ← encodeTerm R E
    match τR with
    | .fun (.pair α β) .bool =>
      unless α == β do
        throw s!"encodeTerm:closure: Expected a homogeneous relation, got {τR}"
      encodeClosure refl R' α
    | .fun α (.option β) => do
      -- A relation stored as a partial function: reify its graph first, the
      -- same representation join `pow` performs.
      unless α == β do
        throw s!"encodeTerm:closure: Expected a homogeneous relation, got {τR}"
      let ⟨Rg, Rg_spec⟩ ← loosenAux_prf "clos!"
        (castPath.graph (castPath.reflexive α) (castPath.reflexive β)) R'
      declareConstWithSpec Rg (.fun (.pair α β) .bool) Rg_spec
      encodeClosure refl (.var Rg) α
    | _ => throw s!"encodeTerm:closure: Expected a relation, got {τR}"
  | .app f x, E => do
    castApp (← encodeTerm f E) (← encodeTerm x E)
  | .collect vs D P, E => do
    /- two cases : `D` is either a set or a function -/
    let ⟨D₀, τD₀⟩ ← encodeTerm D E
    -- A single binder ranges over the *pairs* of the domain, whereas the
    -- option-valued branch below destructures a key and a value and so needs at
    -- least two.  A domain stored as a partial function is therefore reified
    -- into its graph first, which is the set the binder actually ranges over.
    let ⟨D', τD⟩ ←
      if vs.length < 2 then
        do let ⟨Dc, τ⟩ ← asCharPred "collect" D₀ τD₀; pure (Dc, SMTType.fun τ .bool)
      else pure (D₀, τD₀)
    match τD with
    | .fun α (.option β) => do
      -- `D` is a function
      -- {x, y ∈ D | P} = λ x. if P[y ↦ D(x)] then some (D(x)) else none
      let αs := α.fromProdl <| vs.length - 2
      unless αs.length == vs.length - 1 do
        throw s!"encodeTerm:collect: Expected {vs.length - 1} types, got {αs.length}"
      let shadowed ← SMT.saveShadowed vs
      let hidden ← SMT.hideCapturedSites vs
      for ⟨v, ξ⟩ in vs.zip (αs.concat β) do addToContext v ξ
      let decls_snap := (← get).env.declarations
      let ⟨P', .bool⟩ ← encodeTerm P E | throw s!"encodeTerm:collect: Expected a boolean, got {(← encodeTerm P E).2}"
      -- Keep the emitted function at its advertised domain type `α`.  A
      -- multi-variable SMT lambda denotes over a right-associated tuple,
      -- whereas `α` and `toPairl` use the encoder's left-associated tuple
      -- convention.  Binding one tuple and destructuring it here matches the
      -- graph-producing cases and preserves the declared `α → Option β` type.
      let z ← freshVar α
      let Dapp := .app D' (.var z)
      let Dz := .the Dapp
      let subs := (toDestPair vs.dropLast (.var z)).concat Dz
      let P' ← SMT.rescopeHelpers decls_snap.size vs subs z α P'
      let P' := substList vs subs P'
      -- `the` is total in the semantic model, so retain the option equality
      -- guard to rule out its arbitrary value when `Dapp` is `none`.
      let defined := .eq Dapp (.some Dz)
      SMT.eraseFromContext z
      SMT.restoreShadowed shadowed
      SMT.restoreSites hidden
      return (.lambda [z] [α] (.ite (.and defined P') (.some Dz) (none$ β)),
        .fun α β.option)
    | .fun τ .bool => do
      -- `D` is a set
      let τs := τ.fromProdl <| vs.length - 1
      let shadowed ← SMT.saveShadowed vs
      let hidden ← SMT.hideCapturedSites vs
      for ⟨v, ξ⟩ in vs.zip τs do addToContext v ξ
      let decls_snap := (← get).env.declarations
      let ⟨P', .bool⟩ ← encodeTerm P E | throw s!"encodeTerm:collect: Expected a boolean, got {(← encodeTerm P E).2}"
      let z ← freshVar τ
      let subs := toDestPair vs (.var z)
      let P' ← SMT.rescopeHelpers decls_snap.size vs subs z τ P'
      let P' := substList vs subs P'
      SMT.eraseFromContext z
      SMT.restoreShadowed shadowed
      SMT.restoreSites hidden
      return (.lambda [z] [τ] (.ite (.app D' (.var z)) P' (.bool false)), .fun τ .bool)
    | _ => throw s!"encodeTerm:collect: Expected a set or a function, got {τD}"
  | .lambda vs D P, E => do
    /- Encode `λ vs ∈ D. P` (B type `(τ ×ᴮ β).set`) as the option-valued SMT
       function `fun x => if x ∈ D then some P[x/vs] else none`. Its graph is
       the source set of pairs, while the emitted SMT representation preserves
       the fact that the relation is functional.

       `D` must have SMT type `.fun τ .bool` (a set / characteristic function),
       guaranteed by `B.Typing.lambda`'s requirement that `D : .set τ`. -/
    let ⟨D₀, τD₀⟩ ← encodeTerm D E
    -- The domain of a λ is a set; reify it if it arrived as a partial function.
    let ⟨Dc, τDc⟩ ← asCharPred "lambda" D₀ τD₀
    let ⟨D', τD⟩ := (Dc, SMTType.fun τDc .bool)
    match τD with
    | .fun τ .bool => do
      -- `D` is a set of tuples with arity `vs.length`
      let τs := τ.fromProdl <| vs.length - 1
      let shadowed ← SMT.saveShadowed vs
      let hidden ← SMT.hideCapturedSites vs
      for ⟨v, ξ⟩ in vs.zip τs do addToContext v ξ
      let decls_snap := (← get).env.declarations
      let ⟨P', γ⟩ ← encodeTerm P E
      let x ← freshVar τ
      let subs := toDestPair vs (.var x)
      let P' ← SMT.rescopeHelpers decls_snap.size vs subs x τ P'
      let Px := substList vs subs P'
      let x_mem_D' := .app D' (.var x)
      SMT.eraseFromContext x
      SMT.restoreShadowed shadowed
      SMT.restoreSites hidden
      return (.lambda [x] [τ]
        (.ite x_mem_D' (.some Px) (none$ γ)),
        .fun τ (.option γ))
    | _ => throw s!"encodeTerm:lambda: Expected a set (.fun τ .bool), got {τD}"
  | .pfun A B, E => do
    /-
    A ⇸ B = { R ∈ 𝒫(A × B) | R is a partial function }
    Encoded as: λ R : (α × β) → bool.
      (∀ x : α, y : β. R(⟨x,y⟩) ⇒ A(x) ∧ B(y)) ∧
      (∀ x : α, y : β, y' : β. R(⟨x,y⟩) ∧ R(⟨x,y'⟩) ⇒ y = y')
    -/
    let ⟨A', .fun α .bool⟩ ← encodeTerm A E | throw "encodeTerm:pfun: Expected a set for domain"
    let ⟨B', .fun β .bool⟩ ← encodeTerm B E | throw "encodeTerm:pfun: Expected a set for codomain"
    let R ← freshVar (.fun (.pair α β) .bool)
    let x ← freshVar α
    let y ← freshVar β
    let y' ← freshVar β
    -- `R`, `x`, `y`, `y'` are only the `λ`/`∀` binders below; erase them from the global
    -- type context so the result stays typeable there (re-introduced by the binders).
    SMT.eraseFromContext R; SMT.eraseFromContext x; SMT.eraseFromContext y; SMT.eraseFromContext y'
    return (.lambda [R] [.fun (.pair α β) .bool] (.and
      -- (1) R ⊆ A × B: ∀ x y. R(⟨x,y⟩) ⇒ A(x) ∧ B(y)
      (.forall [x, y] [α, β] (.imp (.app (.var R) (.pair (.var x) (.var y)))
        (.and (.app A' (.var x)) (.app B' (.var y)))))
      -- (2) R is functional: ∀ x y y'. R(⟨x,y⟩) ∧ R(⟨x,y'⟩) ⇒ y = y'
      (.forall [x, y, y'] [α, β, β] (.imp
        (.and (.app (.var R) (.pair (.var x) (.var y)))
              (.app (.var R) (.pair (.var x) (.var y'))))
        (.eq (.var y) (.var y'))))
    ), .fun (.fun (.pair α β) .bool) .bool)
  | .min S, E => do
    let ⟨S', τS⟩ ← encodeTerm S E
    let .fun .int .bool := τS
      | throw s!"encodeTerm:min: Expected a set of integers, got {τS}"
    encodeExtremum true S'
  | .max S, E => do
    let ⟨S', τS⟩ ← encodeTerm S E
    let .fun .int .bool := τS
      | throw s!"encodeTerm:max: Expected a set of integers, got {τS}"
    encodeExtremum false S'
  | .all vs D P, E => do
    let ⟨D', τD⟩ ← encodeTerm D E
    match τD with
    | .fun τ .bool =>
      let tmp_τs := τ.fromProdl <| vs.length - 1

      if hlen : vs.length = tmp_τs.length then
        let τs : List SMTType ← tmp_τs.mapFinIdxM fun i τ hi ↦
          if vs[i] ∈ E.flags then
            match τ with
            | .fun (.pair α β) .bool => return .fun α (.option β)
            | .fun α (.option β) => return .fun α (.option β)
            -- The flag only picks a representation, so a type that has no
            -- partial-function form keeps the default one.  Flags are collected
            -- by name and Atelier B reuses names across obligations, so a name
            -- flagged in one obligation can denote something else in another.
            | ξ => return ξ
          else return τ

        let shadowed ← SMT.saveShadowed vs
        for ⟨v, τ⟩ in vs.zip τs do addToContext v τ

        -- Snapshot before encoding body + membership: cast helpers generated here
        -- must be scoped inside the ∀ rather than left as global free constants.
        -- We snapshot types too so freshVar-created cast vars don't leak to finalBulkDeclare.
        let decls_snap := (← get).env.declarations
        let asserts_snap := (← get).env.asserts
        let types_snap := (← get).types
        let sites_snap := (← get).sites
        -- After the snapshot, so the wholesale restore below puts them back.
        let _ ← SMT.hideCapturedSites vs

        let ⟨P', .bool⟩ ← encodeTerm P E | throw s!"encodeTerm:all: Expected a boolean, got {← encodeTerm P E}"
        let zs ← freshVarList τs
        let P' := substList vs (zs.map .var) P'
        let τ' := τs.toProdl
        let (z_mem_D', .bool) ← castMembership (zs.map .var |>.toPairl, τ') (D', .fun τ .bool) | throw s!"encodeTerm:all: Failed to cast {zs} ∈ {D'}"

        -- Collect cast-helper delta and revert: declarations, asserts, and types.
        -- usedVars is kept growing to prevent future freshVar collisions.
        let new_decls := ((← get).env.declarations.extract decls_snap.size).toList
        -- The helper declarations are about to be re-scoped inside the ∀, so a
        -- site recorded while encoding the body must not outlive it: its
        -- constant is no longer declared at this level.
        modify λ e => { e with env := { e.env with declarations := decls_snap, asserts := asserts_snap }, types := types_snap, sites := sites_snap }

        -- Scope cast helpers inside the ∀ as universals guarded by their spec:
        -- `∀ helper. spec(helper) → body`. Using `∃ helper. spec ∧ body` would be
        -- unsound when the surrounding goal is negated: the solver could pick a
        -- helper violating `spec` to make the implication's negation trivially
        -- satisfiable.
        let ex_binders := new_decls.filterMap fun | .declare_const v τ => some (v, τ) | _ => none
        let spec_bodies := new_decls.filterMap fun | .define_fun _ .unit .bool b => some b | _ => none
        -- Spec bodies constrain cast helpers via `vs`; rename to `zs` like `P'`.
        let spec_bodies := spec_bodies.map (substList vs (zs.map .var))
        let inner := spec_bodies.foldr (.imp · ·) (.imp z_mem_D' P')
        let scoped_body := ex_binders.foldr (fun (v, τ) t => .forall [v] [τ] t) inner

        for v in zs do SMT.eraseFromContext v
        SMT.restoreShadowed shadowed
        return (.forall zs τs scoped_body, .bool)
      else throw s!"encodeTerm:all: number of variables {vs.length} does not match number of gathered types {tmp_τs.length}"
    | .fun α (.option β) =>
      let τs := (α.pair β).fromProdl <| vs.length - 1
      unless τs.length == vs.length do
        throw s!"encodeTerm:all: Expected {vs.length - 1} types, got {τs.length}"

      let shadowed ← SMT.saveShadowed vs
      for ⟨v, ξ⟩ in vs.zip τs do addToContext v ξ

      let xs ← freshVarList τs

      -- Snapshot before encoding body + membership (same scoping rationale as .fun τ .bool).
      let decls_snap := (← get).env.declarations
      let asserts_snap := (← get).env.asserts
      let types_snap := (← get).types
      let sites_snap := (← get).sites
      -- After the snapshot, so the wholesale restore below puts them back.
      let _ ← SMT.hideCapturedSites vs

      let ⟨P', .bool⟩ ← encodeTerm P E | throw s!"encodeTerm:all: Expected a boolean, got {← encodeTerm P E}"
      let P' := substList vs (xs.map .var) P'

      let ⟨xsy_mem_D, _⟩ ← castMembership (xs.map .var |>.toPairl, τs.toProdl) (D', .fun α (.option β))

      let new_decls := ((← get).env.declarations.extract decls_snap.size).toList
      modify λ e => { e with env := { e.env with declarations := decls_snap, asserts := asserts_snap }, types := types_snap, sites := sites_snap }

      let ex_binders := new_decls.filterMap fun | .declare_const v τ => some (v, τ) | _ => none
      let spec_bodies := new_decls.filterMap fun | .define_fun _ .unit .bool b => some b | _ => none
      -- Spec bodies constrain cast helpers via `vs`; rename to `xs` like `P'`.
      let spec_bodies := spec_bodies.map (substList vs (xs.map .var))
      let inner := spec_bodies.foldr (.imp · ·) (xsy_mem_D ⇒ˢ P')
      let scoped_body := ex_binders.foldr (fun (v, τ) t => .forall [v] [τ] t) inner

      for v in xs do SMT.eraseFromContext v

      SMT.restoreShadowed shadowed
      return (.forall xs τs scoped_body, .bool)
    | _ => throw s!"encodeTerm:all: Expected a set or a function, got {← encodeTerm D E}"

/-- The SMT type of a source variable.

A *flagged* variable is one the POG reader saw used as a function; it is stored
as `α → Option β` rather than as the characteristic predicate of its graph.  The
flag is only a representation hint: flags are collected by name, and Atelier B
reuses names across obligations, so a flagged name whose type admits no such
form simply keeps the default representation. -/
def smtTypeOf (flagged : Bool) (τ : B.BType) : SMTType :=
  match flagged, τ with
  | true, .set (.prod α β) => .fun α.toSMTType (.option β.toSMTType)
  | _, ξ => ξ.toSMTType

def encodeTypeContext (e : B.Env) : Encoder Unit := do
  for ⟨v, τ⟩ in e.context.entries do
    addToContext v <| smtTypeOf (v ∈ e.flags) τ

def encodeDefs (E : B.Env) : Encoder Unit := do
  let rec aux : List ((_ : B.𝒱) × B.Term) → List SMT.𝒱 → Encoder (List SMT.𝒱)
    | .nil, vs => return vs
    | .cons ⟨v, dv⟩ defs, vs => do
      let .some τ := (←get).types.get? v | throw s!"encodeDefs: missing type for {v}"
      let ⟨t, _⟩ ← encodeTerm dv E
      /-
        NOTE: Using define_fun instead of define_const because cvc5 doesn't
        support define_const for function types.
      -/
      modify (λ e => { e with env := { e.env with declarations := e.env.declarations.push <| Instr.define_fun v .unit τ t } })
      aux defs (v :: vs)
  let declared ← aux E.defs.entries []
  let e ← get
  let Γ : TypeContext := e.types.filter (λ k _ => k ∉ declared)
  -- for ⟨v, τ⟩ in e.types do if v ∉ declared then Γ := Γ.cons v τ
  let decl := Γ.toList.map (λ ⟨v, τ⟩ => Instr.declare_const v τ)
  -- NOTE: per-PO hypotheses come from `po.defs` (populated from each PO's
  -- `<Definition>` list in the POG). Asserting `E.hypotheses` globally is
  -- unsound because categories like `inv`/`ass` are GOALS for some POs
  -- (e.g. `Initialisation` does not list `inv`).
  modify λ e => { e with env := { e.env with
    declarations := decl.reverse.toArray ++ e.env.declarations }}

def encodeDistinctFinite (E : B.Env) : Encoder Unit := do
  let ds ← E.distinct.mapM λ ds => Term.distinct <$> ds.mapM (λ t => Prod.fst <$> (encodeTerm t E))
  let fs ← E.finite.mapM λ fin => (Prod.fst <$> encodeTerm fin E)
  modify λ e => { e with env := { e.env with
    asserts := match e.env.asserts with
    | .asserts as => .asserts <| as.concat (Stages.instr <| (ds ++ fs).map Instr.assert)
    | _ => panic! "encodeDefs: malformed assert in environment" }}

def encodeSimpleGoal (g : B.SimpleGoal) (E : B.Env) : Encoder <| Stages := do
  let lh ← g.hyps.mapM (encodeTerm · E)
  let g ← encodeTerm g.goal E
  return .instr <| (lh.map Prod.fst).concat g.1 |>.map Instr.assert |>.concat .check_sat

def B.SimpleGoal.negate (sg : SimpleGoal) : SimpleGoal :=
  { sg with goal := .not sg.goal }

def B.ProofObligation.negateGoals (po : ProofObligation) : ProofObligation :=
  { po with goals := po.goals.map (·.negate)}

def encodeProofObligation (φ : B.ProofObligation) (E : B.Env) : Encoder Stages := do
  -- Inject this PO's local type bindings into the encoder state and emit a
  -- `declare-const` per local variable. Declarations are scoped inside the
  -- PO's `(push 1) ... (pop 1)` so the same name can have different types
  -- in different POs (Atelier B reuses fresh names like `s392`).
  let typesSnapshot := (← get).types
  -- Sites are keyed by encoded set and their defining assertions live inside
  -- this PO's `(push 1) … (pop 1)`, so they must not leak across POs.
  SMT.clearSites
  -- Helpers created while encoding this obligation may mention its local
  -- variables, which are declared inside the `push` below.  Emitting them into
  -- the global declaration chunk would put them out of scope, so the run of
  -- instructions they add is moved into the obligation itself.
  let declsBefore := (← get).env.declarations.size
  -- Accumulated in reverse: appending to a list per local variable is
  -- quadratic, and obligations can carry thousands of them.
  let mut localDeclsRev : Chunk := []
  for ⟨v, τ⟩ in φ.localContext.entries do
    let smtτ := smtTypeOf (v ∈ φ.localFlags ∨ v ∈ E.flags) τ
    addToContext v smtτ
    localDeclsRev := Instr.declare_const v smtτ :: localDeclsRev
  let localDecls := localDeclsRev.reverse
  -- Augment the B environment with PO-local context/flags so `encodeTerm`'s
  -- B-side lookups succeed for the duration of this PO.
  let E_local : B.Env := φ.extendEnv E
  let defs ← (φ.defs.mapM ((Instr.assert ∘ Prod.fst) <$> encodeTerm · E_local))
  let globalHyps : Chunk ← (φ.hyps.mapM ((Instr.assert ∘ Prod.fst) <$> encodeTerm · E_local))
  let goals : List Stages ← φ.negateGoals.goals.mapM (encodeSimpleGoal · E_local)
  let helpers := ((← get).env.declarations.extract declsBefore).toList
  -- Pop PO-local types so subsequent POs start clean.
  modify λ e => { e with
    types := typesSnapshot
    env := { e.env with declarations := e.env.declarations.take declsBefore } }
  return Stages.asserts <|
    (.instr <| localDecls ++ helpers ++ defs ++ globalHyps) :: goals.map (fun s => Stages.asserts [s])

def encodeProofObligations (E : B.Env) : Encoder Unit := do
  let rec aux : List B.ProofObligation → Encoder Unit
    | [] => pure ()
    | φ::φs => do
      let po ← encodeProofObligation φ E
      modify (λ e =>
        match e.env.asserts with
        | .asserts as => { e with env := { e.env with asserts := .asserts <| as.concat po }}
        | _ => panic! "Malformed environment"
        )
      aux φs
  aux E.po
-- Declare any vars still in `types` that have no declaration yet.
-- Needed for bound B variables (e.g. flagged vars in `finite`) whose
-- cast-helper specs are committed globally during body encoding but whose
-- `addToContext` runs after `encodeDefs`'s bulk-declare pass.
def finalBulkDeclare : Encoder Unit := do
  let e ← get
  let alreadyDeclared : List SMT.𝒱 := e.env.declarations.toList.filterMap fun
    | .declare_const v _ => some v
    | .define_fun v _ _ _ => some v
    | .define_const v _ _ => some v
    | _ => none
  let Γ : TypeContext := e.types.filter (λ k _ => k ∉ alreadyDeclared)
  let decl := Γ.toList.map (λ ⟨v, τ⟩ => Instr.declare_const v τ)
  modify λ e => { e with env := { e.env with
    declarations := decl.reverse.toArray ++ e.env.declarations } }

def encode (e : B.Env) : Encoder Unit := do
  modify λ st => { st with env := { st.env with
    freshvarsc := e.freshvarsc
    usedVars := Std.HashSet.ofList e.initialUsedVars } }
  encodeTypeContext e *> encodeDefs e *> encodeDistinctFinite e *> encodeProofObligations e *> finalBulkDeclare

def EncoderState.toSMTFile : Encoder String := do
  let env := (← get).env.simplify
  -- Refuse to emit a file a solver would reject.  A missed conversion between
  -- the two set representations is otherwise invisible here and only surfaces
  -- as a solver type error, far from the code responsible.
  match SMT.Env.mismatches env with
  | [] => return toString <| Stages.asserts [.instr env.declarations.toList, env.asserts]
  | ps => throw <| "emitted SMT is ill-typed:\n  " ++ String.intercalate "\n  " (ps.take 3)

def encodePOG (pogpath : System.FilePath) (show_encoding := false): IO String := do
  let pog ← readPOG pogpath |>.propagateError
  let ⟨(), st⟩ ← POGtoB pog |>.run ∅ |>.run |>.propagateError
  -- dbg_trace st.env
  let st' ← match encode st.env |>.run ∅ with
    | .ok ⟨(), st'⟩ => pure st'
    | .error e => throw <| IO.userError e
  -- dbg_trace st'.types.toList
  let r ← match EncoderState.toSMTFile |>.run st' with
    | .ok ⟨r, _⟩ => pure r
    | .error e => throw <| IO.userError e
  if show_encoding then
    IO.println r
  return r

-- #eval encodePOG (".."/".."/"benchmark"/"dataset-pog"/"0002"/"00028.pog") >>= cvc5 (timeout := 1000) >>= IO.println
-- #eval MCH2POG "Test/Test.mch" >>= encodePOG (show_encoding := true) >>= cvc5 >>= IO.println
-- #eval encodePOG ("Test"/"Eval.pog") (show_encoding := true) >>= cvc5 >>= IO.println

-- 0010_00006
-- 0015/00132: malformed pog (s89 = s89_1)

-- (Pair (Pair _ (-> Int (Option Int))) _)
-- (Pair (Pair _ (-> (Pair Int Int) Bool)) _)
