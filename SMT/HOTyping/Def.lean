import SMT.PHOAS.Basic

namespace SMT.PHOAS

abbrev TypeContext.{u} (𝒱 : Type u) := 𝒱 → Option SMTType

instance {𝒱} : EmptyCollection (TypeContext 𝒱) where
  emptyCollection := λ _ => none

def TypeContext.update {𝒱} [DecidableEq 𝒱] {n} (Γ : TypeContext 𝒱) (v : Fin n → 𝒱) (α : Fin n → SMTType) : TypeContext 𝒱 :=
  Fin.foldl n (λ Δ i => Function.update Δ (v i) (α i)) Γ
