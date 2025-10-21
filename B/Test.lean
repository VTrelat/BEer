import Mathlib.Init.Set
-- Set theory

section Bsyntax

inductive BAtom : Type -> Type where
  | BOOL : Bool -> BAtom Bool
  | NAT : Nat -> BAtom Nat

@[reducible]
def BSet (α : Type u) := α → Prop
macro "{" x:term " | " p:term "}ᴮ" : term => `(BSet (λ $x => $p))
-- macro for patterns {x1, x2, x3, ...} => {λ x => x = x1 ∨ x = x2 ∨ x = x3 ∨ ...}
macro "{" xs:term,* "}ᴮ" : term => `(λ x => x ∈ [ $xs,* ])

infix:50 " ↦ " => Prod.mk

instance : EmptyCollection (BSet α) := ⟨λ _ => False⟩

def univ : BSet α := (λ _ => True)
notation " Ω " => univ

instance BSet.mem : Membership α (BSet α) := ⟨(· |> ·)⟩
instance BSet.subset : HasSubset (BSet α) := ⟨(∀ x, x ∈ · → x ∈ ·)⟩

@[ext]
theorem BSet.ext {α : Type u} (𝓔₁ 𝓔₂ : BSet α) (h : ∀ x, x ∈ 𝓔₁ ↔ x ∈ 𝓔₂) : 𝓔₁ = 𝓔₂ :=
  funext (λ x => propext (h x))

def BSet.pow {α : Type u} : BSet α -> BSet (BSet α) := (· ⊆ ·)

@[simp]
theorem BSet.set_in_pow {α : Type u} (𝓔 : BSet α) : 𝓔 ∈ 𝓔.pow := by
  simp [BSet.pow, HasSubset.Subset, Membership.mem]

@[simp]
theorem BSet.not_mem_empty {α : Type u} (x : α) : x ∉ (∅ : BSet α) := by
  simp [EmptyCollection.emptyCollection, Membership.mem]

@[simp]
theorem BSet.mem_univ {α : Type u} (x : α) : x ∈ Ω := by trivial

example : BAtom.NAT 3 ∈ {.NAT 1, .NAT 2, .NAT 3}ᴮ := by
  simp [BSet.mem]

example : BAtom.NAT 4 ∉ {.NAT 1, .NAT 2, .NAT 3}ᴮ := by
  simp [BSet.mem]

inductive BExpr
  -- atomic propositions
  | atom : BAtom α -> BExpr
  -- logical connectives
  | conj : BExpr -> BExpr -> BExpr
  | disj : BExpr -> BExpr -> BExpr
  | neg : BExpr -> BExpr
  | imp : BExpr -> BExpr -> BExpr
  -- equality
  | eq : BExpr -> BExpr -> BExpr
  -- quantifiers
  | forall : (α -> BExpr) -> BExpr


end Bsyntax
