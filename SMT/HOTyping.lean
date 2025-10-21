import SMT.HOTyping.Rules

namespace SMT.PHOAS

abbrev WellTyped.{u} {𝒱 : Type u} [DecidableEq 𝒱] [Inhabited 𝒱] (t : Term 𝒱) := Σ' (Γ : TypeContext 𝒱) (τ : SMTType), Γ ⊢ t : τ

end SMT.PHOAS
