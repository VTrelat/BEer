import SMT.PHOAS.Basic

namespace SMT.PHOAS

abbrev TypeContext.{u} (𝒱 : Type u) := 𝒱 → Option SMTType

instance {𝒱} : EmptyCollection (TypeContext 𝒱) where
  emptyCollection := λ _ => none

def TypeContext.update {𝒱} [DecidableEq 𝒱] {n} (Γ : TypeContext 𝒱) (v : Fin n → 𝒱) (α : Fin n → SMTType) : TypeContext 𝒱 :=
  Fin.foldl n (λ Δ i => Function.update Δ (v i) (α i)) Γ

/-- Class assigning each `𝒱`-variable an intrinsic SMT type. For PHOAS over `Dom`
    (defined later in SMT.Semantics), the intrinsic type is the second component.
    Default instance assigns `SMTType.unit`. -/
class HasType.{u} (𝒱 : Type u) where
  type : 𝒱 → SMTType

instance (priority := 0) {𝒱 : Type _} : HasType 𝒱 where
  type _ := SMTType.unit

/-- A `HasType` instance where every SMT type has an inhabiting variable.
    Used for typing determinism: with a `Rich` instance, we can find vs satisfying
    arbitrary `vs_typed` constraints in lambda/forall bodies. -/
class RichHasType.{u} (𝒱 : Type u) extends HasType 𝒱 where
  rep : SMTType → 𝒱
  rep_type : ∀ τ, type (rep τ) = τ
