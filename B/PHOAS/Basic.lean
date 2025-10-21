import Mathlib.Logic.Function.OfArity
import B.Typing.Basic
set_option autoImplicit false

namespace B.PHOAS

inductive Term.{u} (𝒱 : Type u) : Type u
  | var (v : 𝒱)
  | int (n : Int)
  | bool (b : Bool)
  -- pairs
  | maplet (x y : Term 𝒱)
  -- arithmetic
  | add (x y : Term 𝒱)
  | sub (x y : Term 𝒱)
  | mul (x y : Term 𝒱)
  | le (x y : Term 𝒱)
  -- logic
  | and (x y : Term 𝒱)
  | not (x : Term 𝒱)
  | eq (x y : Term 𝒱)
  -- sets
  -- basic sets
  | ℤ
  | 𝔹
  -- set operations
  -- binder
  | collect {n : ℕ} (D : Term 𝒱) (P : (Fin n → 𝒱) → Term 𝒱) : Term 𝒱
  | lambda {n : ℕ} (D : Term 𝒱) (t : (Fin n → 𝒱) → Term 𝒱) : Term 𝒱
  | all {n : ℕ} (D : Term 𝒱) (P : (Fin n → 𝒱) → Term 𝒱) : Term 𝒱
  | mem (x : Term 𝒱) (S : Term 𝒱)
  | pow (S : Term 𝒱)
  | cprod (S T : Term 𝒱)
  | union (S T : Term 𝒱)
  | inter (S T : Term 𝒱)
  | card (S : Term 𝒱)
  -- functions
  | app (f x : Term 𝒱)
  | min (S : Term 𝒱)
  | max (S : Term 𝒱)
  | pfun (A B : Term 𝒱)
  deriving Inhabited

infixl:65 " ↦ᴮ' " => Term.maplet
infixl:70 " +ᴮ' " => Term.add
infixl:70 " -ᴮ' " => Term.sub
infixl:75 " *ᴮ' " => Term.mul
infixl:45 " ∧ᴮ' " => Term.and
prefix:80 " ¬ᴮ' " => Term.not
infixl:40 " =ᴮ' " => Term.eq
infixl:40 " ≤ᴮ' " => Term.le
infixl:65 " ∈ᴮ' " => Term.mem
prefix:70 " 𝒫ᴮ' " => Term.pow
infixl:75 " ⨯ᴮ' " => Term.cprod
infixl:80 " ∪ᴮ' " => Term.union
infixl:85 " ∩ᴮ' " => Term.inter
prefix:20 "@ᴮ'" => Term.app
infixl:90 " ⇸ᴮ' " => Term.pfun
notation:90 "|" S "|ᴮ'" => Term.card S

def squash.{u} {𝒱 : Type u} : Term (Term 𝒱) → Term 𝒱
  | .var x => x
  | .int n => .int n
  | .bool b => .bool b
  | .add t u => .add (squash t) (squash u)
  | .pow S => .pow (squash S)
  | .collect D P => .collect (squash D) (λ x => squash (P (.var ∘ x)))
  | .lambda D P => .lambda (squash D) (λ x => squash (P (.var ∘ x)))
  | .all D P => .all (squash D) (λ x => squash (P (.var ∘ x)))
  | .max S => .max (squash S)
  | .min S => .min (squash S)
  | .app f x => .app (squash f) (squash x)
  | .card S => .card (squash S)
  | .inter S T => .inter (squash S) (squash T)
  | .union S T => .union (squash S) (squash T)
  | .cprod S T => .cprod (squash S) (squash T)
  | .mem x S => .mem (squash x) (squash S)
  | .𝔹 => .𝔹
  | .ℤ => .ℤ
  | .eq x y => .eq (squash x) (squash y)
  | .not x => .not (squash x)
  | .and x y => .and (squash x) (squash y)
  | .le x y => .le (squash x) (squash y)
  | .mul x y => .mul (squash x) (squash y)
  | .sub x y => .sub (squash x) (squash y)
  | .maplet x y => .maplet (squash x) (squash y)
  | .pfun A B => .pfun (squash A) (squash B)

-- def subst.{u} {𝒱 : Type u} (t : Term 𝒱 → Term (Term 𝒱)) (s : Term 𝒱) : Term 𝒱 := squash (t s)

def subst.{u} {𝒱 : Type u} [DecidableEq 𝒱] : Term 𝒱 → 𝒱 → Term 𝒱 → Term 𝒱
  | .var w, v, t => if w = v then t else .var w
  | .int n, _, _ => .int n
  | .bool b, _, _ => .bool b
  | .maplet x y, v, t => .maplet (subst x v t) (subst y v t)
  | .add x y, v, t => .add (subst x v t) (subst y v t)
  | .sub x y, v, t => .sub (subst x v t) (subst y v t)
  | .mul x y, v, t => .mul (subst x v t) (subst y v t)
  | .le x y, v, t => .le (subst x v t) (subst y v t)
  | .and x y, v, t => .and (subst x v t) (subst y v t)
  | .not x, v, t => .not (subst x v t)
  | .eq x y, v, t => .eq (subst x v t) (subst y v t)
  | .ℤ, _, _ => .ℤ
  | .𝔹, _, _ => .𝔹
  | .collect D P, v, t => .collect (subst D v t) (λ x => subst (P x) v t)
  | .lambda D E, v, t => .lambda (subst D v t) (λ x => subst (E x) v t)
  | .all D P, v, t => .all (subst D v t) (λ x => subst (P x) v t)
  | .mem x S, v, t => .mem (subst x v t) (subst S v t)
  | .pow S, v, t => .pow (subst S v t)
  | .cprod S T, v, t => .cprod (subst S v t) (subst T v t)
  | .union S T, v, t => .union (subst S v t) (subst T v t)
  | .inter S T, v, t => .inter (subst S v t) (subst T v t)
  | .card S, v, t => .card (subst S v t)
  | .app f x, v, t => .app (subst f v t) (subst x v t)
  | .min S, v, t => .min (subst S v t)
  | .max S, v, t => .max (subst S v t)
  | .pfun A B, v, t => .pfun (subst A v t) (subst B v t)

end B.PHOAS
