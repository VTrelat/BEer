namespace SMT

inductive SMTType where
  | bool
  | int
  | unit
  | «fun» (arg ret : SMTType)
  | option (τ : SMTType)
  | pair (α β : SMTType)
  deriving Inhabited, DecidableEq

abbrev SMTType.rel (α β : SMTType) : SMTType := (α.pair β).fun .bool

instance : LawfulBEq SMTType where
  eq_of_beq := by
    intro a b h
    induction a generalizing b <;> (cases b <;> try trivial) <;> (
      rw [beq_iff_eq] at h
      injections; subst_eqs
      rfl)
  rfl := by
    intro a
    cases a <;>
    first
    | rfl
    | exact ReflBEq.rfl

def SMTType.toString : SMTType → String
  | .bool => "Bool"
  | .int => "Int"
  | .unit => "()"
  | .fun arg ret => s!"(-> {arg.toString} {ret.toString})"
  | .option τ => s!"(Option {toString τ})"
  | .pair α β => s!"(Pair {toString α} {toString β})"

instance : ToString SMTType := ⟨SMTType.toString⟩

abbrev 𝒱 := String

inductive Term where
  -- atomic terms
  | var (v : 𝒱)
  | int (n : Int)
  | bool (b : Bool)
  | app (f : Term) (x : Term)
  -- binders
  | lambda (v : List 𝒱) (τs : List SMTType) (t : Term)
  | forall (v : List 𝒱) (τs : List SMTType) (t : Term)
  | exists (v : List 𝒱) (τs : List SMTType) (t : Term)
  | as (t : Term) (τ : SMTType)
  -- logic
  | eq (t₁ t₂ : Term)
  | and (t₁ t₂ : Term)
  | or (t₁ t₂ : Term)
  | not (t : Term)
  | imp (t₁ t₂ : Term)
  | ite (c t e : Term)
  -- constructors
  | some (t : Term) | the (t : Term) | none
  | pair (t₁ t₂ : Term) | fst (t : Term) | snd (t : Term)
  | distinct (ts : List Term)
  -- arithmetic
  | le (t₁ t₂ : Term)
  | add (t₁ t₂ : Term)
  | sub (t₁ t₂ : Term)
  | mul (t₁ t₂ : Term)
  /-- Saturated application of a symbol supplied by the SMT prelude (`bdiv`,
  `bmod`, `bpow`, …) or declared by the encoder.  `τ` is the *result* type, so
  the term stays self-describing for `getType`.  Prints as `(f a₁ … aₙ)`, or as
  the bare symbol when `args` is empty. -/
  | builtin (f : 𝒱) (τ : SMTType) (args : List Term)
  deriving Inhabited, BEq

def noneCast : SMTType → Term := λ τ => .as .none (.option τ)
prefix:50 "none$" => noneCast

prefix:70 "λˢ " => Term.lambda
infixl:60 " ∧ˢ " => Term.and
infixl:40 " =ˢ " => Term.eq
infixl:50 " ⇒ˢ " => Term.imp
infixl:40 " ≤ˢ " => Term.le
prefix:80 "¬ˢ" => Term.not
prefix:20 "@ˢ" => Term.app
infixl:45 " ∨ˢ " => Term.or
infixl:70 " +ˢ " => Term.add
infixl:70 " -ˢ " => Term.sub
infixl:75 " *ˢ " => Term.mul

def toSMTArgList (vs : List <| 𝒱 × SMTType) :=
  vs.map (λ ⟨v, τ⟩ => s!"({v} {τ.toString})") |>.intersperse " " |>.foldl (·++·) ""

/-- `xs` without the elements of `ys`.

Spelled out rather than via `List.removeAll` because that recurses once per kept
element, and the free-variable list of a large proof obligation is long enough
to exhaust the stack.  Order is not preserved; callers only test membership. -/
def removeAll (xs ys : List 𝒱) : List 𝒱 :=
  xs.foldl (fun acc x => if ys.contains x then acc else x :: acc) []

def fv : Term → List 𝒱
  | .var v => [v]
  | .int _ => []
  | .bool _ => []
  | .app f x => fv f ++ fv x
  | .lambda vs _ t | .forall vs _ t | .exists vs _ t => removeAll (fv t) vs
  | .as t _ => fv t
  | .eq t₁ t₂ => fv t₁ ++ fv t₂
  | .and t₁ t₂ => fv t₁ ++ fv t₂
  | .or t₁ t₂ => fv t₁ ++ fv t₂
  | .not t => fv t
  | .imp t₁ t₂ => fv t₁ ++ fv t₂
  | .le t₁ t₂ => fv t₁ ++ fv t₂
  | .some t => fv t
  | .none => []
  | .the t => fv t
  | .pair t₁ t₂ => fv t₁ ++ fv t₂
  | .fst t => fv t
  | .snd t => fv t
  | .add t₁ t₂ => fv t₁ ++ fv t₂
  | .sub t₁ t₂ => fv t₁ ++ fv t₂
  | .mul t₁ t₂ => fv t₁ ++ fv t₂
  | .ite c t e => fv c ++ fv t ++ fv e
  | .distinct ts => ts.attach.map (λ ⟨x, _⟩ => fv x) |>.flatten
  | .builtin _ _ args => args.attach.map (λ ⟨x, _⟩ => fv x) |>.flatten

/-! ### Instantiation patterns

cvc5 picks triggers itself when a quantifier carries none, and on this encoder's
output it picks badly: supplying them is worth about as much again as every
other change here put together — measured at a 2 s budget: 25 goals gained,
9 lost, and a 1.79x median speedup on the goals both settings prove.

A trigger has to be a *term* headed by a symbol, has to mention no variable
bound below it, and the set chosen has to cover every variable the quantifier
binds.  The search deliberately does not descend into nested binders:
`encodeTerm .all` re-scopes cast helpers as `∀ h. spec ⇒ body`, so a name that
reads like a constant is often a bound variable one level out, and a pattern
naming it is out of scope where it is written.

Triggers *restrict* instantiation, so this direction of error is incompleteness,
not unsoundness: a goal needing an instantiation no pattern matches is lost, and
none becomes provable that was not.  A quantifier with no covering set of
candidates keeps no pattern at all, which leaves cvc5's own choice in place. -/

/-- The head symbol of an application spine, when it is a plain symbol. -/
private def spineHead : Term → Option 𝒱
  | .app f _ => spineHead f
  | .var v => Option.some v
  | _ => Option.none

private def size : Term → Nat
  | .app f x => 1 + size f + size x
  | .pair a b => 1 + size a + size b
  | .fst t | .snd t | .the t | .some t | .as t _ => 1 + size t
  | .builtin _ _ args => args.attach.foldl (fun n ⟨a, _⟩ => n + size a) 1
  | _ => 1

/-- Whether `t` binds anything, i.e. cannot appear inside a pattern. -/
private def bindsSomething : Term → Bool
  | .lambda .. | .forall .. | .exists .. => true
  | .app f x | .pair f x => bindsSomething f || bindsSomething x
  | .fst t | .snd t | .the t | .some t | .as t _ => bindsSomething t
  | .builtin _ _ args => args.attach.any (fun ⟨a, _⟩ => bindsSomething a)
  | _ => false

/-- Application terms under `t` that are usable as triggers for `vs`, each with
the binders it covers.  Nested binders are not entered. -/
private def triggerCands (vs : List 𝒱) : Term → List (Term × List 𝒱)
  | .lambda .. | .forall .. | .exists .. => []
  | t@(.app f x) =>
    let below := triggerCands vs f ++ triggerCands vs x
    match spineHead t with
    | Option.some h =>
      -- A bound variable may not head a pattern, and a λ-redex is not a term.
      if vs.contains h || bindsSomething t then below
      else
        let covered : List 𝒱 := ((fv t).filter vs.contains).eraseDups
        if covered.isEmpty then below else (t, covered) :: below
    | Option.none => below
  | .eq a b | .and a b | .or a b | .imp a b | .le a b | .pair a b
  | .add a b | .sub a b | .mul a b => triggerCands vs a ++ triggerCands vs b
  | .not a | .the a | .some a | .fst a | .snd a | .as a _ => triggerCands vs a
  | .ite c a b => triggerCands vs c ++ triggerCands vs a ++ triggerCands vs b
  | .distinct ts | .builtin _ _ ts =>
    ts.attach.flatMap (fun ⟨u, _⟩ => triggerCands vs u)
  | _ => []

/-- A smallest-first set of candidates covering every binder, or `none` when the
binders cannot all be covered. -/
private def chooseTriggers (vs : List 𝒱) (body : Term) : Option (List Term) :=
  let cands := (triggerCands vs body).mergeSort (fun a b => size a.1 ≤ size b.1)
  let (keep, covered) := cands.foldl (init := ([], ([] : List 𝒱)))
    fun (keep, covered) (t, c) =>
      if c.all covered.contains then (keep, covered)
      else (t :: keep, (covered ++ c).eraseDups)
  if vs.all covered.contains && !keep.isEmpty then Option.some keep.reverse
  else Option.none

partial def Term.toString : Term → String
  | .var v => v
  | .int n => if n < 0 then s!"(- {-n})" else ToString.toString n
  | .bool b => ToString.toString b
  | .app (.lambda v τ t) x => s!"(@ {(Term.lambda v τ t).toString} {x.toString})"
  | .app (.var v) x => s!"({v} {x.toString})"
  | .app f x => s!"(@ {f.toString} {x.toString})"
  | .forall vs τs t =>
    let body := match chooseTriggers vs t with
      | Option.some ps =>
        let ps := ps.map Term.toString |>.intersperse " " |>.foldl (·++·) ""
        s!"(! {Term.toString t} :pattern ({ps}))"
      | Option.none => Term.toString t
    s!"(forall ({toSMTArgList <| vs.zip τs}) {body})"
  | .lambda vs τs t => s!"(lambda ({toSMTArgList <| vs.zip τs}) {Term.toString t})"
  | .exists vs τs t => s!"(exists ({toSMTArgList <| vs.zip τs}) {Term.toString t})"
  | .as t τ => s!"(as {Term.toString t} {SMTType.toString τ})"
  | .eq t₁ t₂ => s!"(= {Term.toString t₁} {Term.toString t₂})"
  | .and t₁ t₂ => s!"(and "++ Term.toString t₁++" "++ Term.toString t₂ ++")"
  | .or t₁ t₂ => s!"(or "++ Term.toString t₁++" "++ Term.toString t₂ ++")"
  | .not t => s!"(not "++ Term.toString t ++")"
  | .imp t₁ t₂ => s!"(=> "++ Term.toString t₁++" "++ Term.toString t₂ ++")"
  | .le t₁ t₂ => s!"(<= "++ Term.toString t₁++" "++ Term.toString t₂ ++")"
  | .some t => s!"(some "++ Term.toString t ++")"
  | .none => "none"
  | .the t => s!"(the "++ Term.toString t ++")"
  | .pair t₁ t₂ => s!"(pair "++ Term.toString t₁++" "++ Term.toString t₂ ++")"
  | .fst t => s!"(fst "++ Term.toString t ++")"
  | .snd t => s!"(snd "++ Term.toString t ++")"
  | .add t₁ t₂ => s!"(+ "++ Term.toString t₁++" "++ Term.toString t₂ ++")"
  | .sub t₁ t₂ => s!"(- "++ Term.toString t₁++" "++ Term.toString t₂ ++")"
  | .mul t₁ t₂ => s!"(* "++ Term.toString t₁++" "++ Term.toString t₂ ++")"
  | .ite c t e => s!"(ite "++ Term.toString c++" "++ Term.toString t++" "++ Term.toString e ++")"
  | .distinct ts =>
    let ds := ts.attach.map (λ ⟨t, _⟩ => Term.toString t) |>.intersperse " " |>.foldl (·++·) ""
    s!"(distinct {ds})"
  | .builtin f _ [] => f
  | .builtin f _ args =>
    let as := args.attach.map (λ ⟨t, _⟩ => Term.toString t) |>.intersperse " " |>.foldl (·++·) ""
    s!"({f} {as})"

instance : ToString Term := ⟨Term.toString⟩

def bv : Term → List 𝒱
  | .var _ => []
  | .int _ => []
  | .bool _ => []
  | .app f x => bv f ++ bv x
  | .lambda vs _ t | .forall vs _ t | .exists vs _ t => vs ++ bv t
  | .as t _ => bv t
  | .eq t₁ t₂ => bv t₁ ++ bv t₂
  | .and t₁ t₂ => bv t₁ ++ bv t₂
  | .or t₁ t₂ => bv t₁ ++ bv t₂
  | .not t => bv t
  | .imp t₁ t₂ => bv t₁ ++ bv t₂
  | .le t₁ t₂ => bv t₁ ++ bv t₂
  | .some t => bv t
  | .none => []
  | .the t => bv t
  | .pair t₁ t₂ => bv t₁ ++ bv t₂
  | .fst t => bv t
  | .snd t => bv t
  | .add t₁ t₂ => bv t₁ ++ bv t₂
  | .sub t₁ t₂ => bv t₁ ++ bv t₂
  | .mul t₁ t₂ => bv t₁ ++ bv t₂
  | .ite c t e => bv c ++ bv t ++ bv e
  | .distinct ts => ts.attach.map (λ ⟨x, _⟩ => bv x) |>.flatten
  | .builtin _ _ args => args.attach.map (λ ⟨x, _⟩ => bv x) |>.flatten
