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

def Term.toString : Term → String
  | .var v => v
  | .int n => if n < 0 then s!"(- {-n})" else ToString.toString n
  | .bool b => ToString.toString b
  | .app (.lambda v τ t) x => s!"(@ {(Term.lambda v τ t).toString} {x.toString})"
  | .app (.var v) x => s!"({v} {x.toString})"
  | .app f x => s!"(@ {f.toString} {x.toString})"
  | .forall vs τs t => s!"(forall ({toSMTArgList <| vs.zip τs}) {Term.toString t})"
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

def fv : Term → List 𝒱
  | .var v => [v]
  | .int _ => []
  | .bool _ => []
  | .app f x => fv f ++ fv x
  | .lambda vs _ t | .forall vs _ t | .exists vs _ t => List.removeAll (fv t) vs
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
