import Mathlib.Logic.Function.OfArity
import SMT.Syntax

namespace SMT.PHOAS

inductive Term.{u} (𝒱 : Type u) : Type u
    -- atomic terms
  | var (v : 𝒱)
  | int (n : Int)
  | bool (b : Bool)
  | app (f x : Term 𝒱)
  -- binders
  | lambda {n} (τs : Fin n → SMTType) (t : (Fin n → 𝒱) → Term 𝒱)
  | forall {n} (τs : Fin n → SMTType) (t : (Fin n → 𝒱) → Term 𝒱)
  -- | exists {n} (τs : Fin n → SMTType) (t : (Fin n → 𝒱) → Term 𝒱)
  -- | as (t : Term 𝒱) (τ : SMTType)
  -- logic
  | eq (t₁ t₂ : Term 𝒱)
  | and (t₁ t₂ : Term 𝒱)
  -- | or (t₁ t₂ : Term 𝒱)
  | not (t : Term 𝒱)
  -- | imp (t₁ t₂ : Term 𝒱)
  | ite (c t e : Term 𝒱)
  -- constructors
  | some (t : Term 𝒱) | the (t : Term 𝒱) | none (τ : SMTType) -- none τ ≜ as none τ
  | «()» -- constructor of unit
  | pair (t₁ t₂ : Term 𝒱) | fst (t : Term 𝒱) | snd (t : Term 𝒱)
  | distinct {n : ℕ} (ts : Fin n → Term 𝒱)
  -- arithmetic
  | le (t₁ t₂ : Term 𝒱)
  | add (t₁ t₂ : Term 𝒱)
  | sub (t₁ t₂ : Term 𝒱)
  | mul (t₁ t₂ : Term 𝒱)
  deriving Inhabited

prefix:20 "@ˢ'" => Term.app
infixl:40 " =ˢ' " => Term.eq
infixl:45 " ∧ˢ' " => Term.and
prefix:80 " ¬ˢ' " => Term.not
infixl:40 " ≤ˢ' " => Term.le
infixl:70 " +ˢ' " => Term.add
infixl:70 " -ˢ' " => Term.sub
infixl:75 " *ˢ' " => Term.mul

@[match_pattern] def Term.or {𝒱} (t₁ t₂ : PHOAS.Term 𝒱) : PHOAS.Term 𝒱 := ¬ˢ' (¬ˢ' t₁ ∧ˢ' ¬ˢ' t₂)
infixl:45 " ∨ˢ' " => Term.or

@[match_pattern] def Term.imp {𝒱} (t₁ t₂ : PHOAS.Term 𝒱) : PHOAS.Term 𝒱 := ¬ˢ' (t₁ ∧ˢ' ¬ˢ' t₂)
infixl:35 " ⇒ˢ' " => Term.imp

@[match_pattern] def Term.«exists» {𝒱} {n} (τs : Fin n → SMTType) (P : (Fin n → 𝒱) → Term 𝒱) : Term 𝒱 :=
  ¬ˢ' .forall τs (¬ˢ' P ·)

def subst.{u} {𝒱 : Type u} [DecidableEq 𝒱] : Term 𝒱 → 𝒱 → Term 𝒱 → Term 𝒱
  | .var w, v, t => if w = v then t else .var w
  | .int n, _, _ => .int n
  | .bool b, _, _ => .bool b
  | .add x y, v, t => .add (subst x v t) (subst y v t)
  | .sub x y, v, t => .sub (subst x v t) (subst y v t)
  | .mul x y, v, t => .mul (subst x v t) (subst y v t)
  | .le x y, v, t => .le (subst x v t) (subst y v t)
  | .and x y, v, t => .and (subst x v t) (subst y v t)
  | .not x, v, t => .not (subst x v t)
  | .eq x y, v, t => .eq (subst x v t) (subst y v t)
  | .lambda τs E, v, t => .lambda τs (λ x => subst (E x) v t)
  | .forall τs P, v, t => .forall τs (λ x => subst (P x) v t)
  | .app f x, v, t => .app (subst f v t) (subst x v t)
  | .distinct xs, v, t => .distinct (fun i ↦ subst (xs i) v t)
  | .pair x y, v, t => .pair (subst x v t) (subst y v t)
  | .fst x, v, t => .fst (subst x v t)
  | .snd x, v, t => .snd (subst x v t)
  | .some x, v, t => .some (subst x v t)
  | .the x, v, t => .the (subst x v t)
  | .none τ, _, _ => .none τ
  | .«()», _, _ => .«()»
  | .ite c x y, v, t => .ite (subst c v t) (subst x v t) (subst y v t)

end SMT.PHOAS
