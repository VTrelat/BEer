import B.PHOAS.BPHOAS
import B.Typing.Basic

namespace B

def BType.toTerm' {𝒱} : BType → B.PHOAS.Term 𝒱
  | .int => .ℤ
  | .bool => .𝔹
  | .set α => 𝒫ᴮ' α.toTerm'
  | α ×ᴮ β => α.toTerm' ⨯ᴮ' β.toTerm'

namespace PHOAS

/--
  A context is a map from variables to types
-/
abbrev TypeContext.{u} (𝒱 : Type u) := 𝒱 → Option BType

def TypeContext.update {𝒱} [DecidableEq 𝒱] {n} (Γ : TypeContext 𝒱) (v : Fin n → 𝒱) (α : Fin n → BType) : TypeContext 𝒱 :=
  Fin.foldl n (λ Δ i => Function.update Δ (v i) (α i)) Γ

theorem TypeContext.update_lookup_self  {𝒱} [DecidableEq 𝒱] {n} {Γ : TypeContext 𝒱} {vs : Fin n → 𝒱} (vs_inj : Function.Injective vs) {αs : Fin n → BType} {i : Fin n} :
  Γ.update vs αs (vs i) = some (αs i) := by
  induction n with
  | zero => nomatch i
  | succ n ih =>
    by_cases i_eq : i = ⟨n, Nat.lt_add_one n⟩
    · subst i
      rw [TypeContext.update, Fin.foldl_succ_last]
      apply Function.update_self
    · rw [TypeContext.update, Fin.foldl_succ_last, ←TypeContext.update]
      unfold Fin.last Function.update
      split_ifs with vs_i_eq
      · nomatch i_eq <| vs_inj vs_i_eq
      · exact @ih _ (fun _ _ h => Fin.eq_of_val_eq (Fin.noConfusion (vs_inj h) id)) _ ⟨i, Fin.val_lt_last i_eq⟩

theorem TypeContext.update_lookup_not_self  {𝒱} [DecidableEq 𝒱] {n} {Γ : TypeContext 𝒱} {vs : Fin n → 𝒱} {αs : Fin n → BType} {v : 𝒱} (hv : ∀ i, vs i ≠ v) :
  Γ.update vs αs v = Γ v := by
  induction n with
  | zero => rw [TypeContext.update, Fin.foldl_zero]
  | succ n ih =>
    rw [TypeContext.update, Fin.foldl_succ_last, ←TypeContext.update]
    unfold Function.update
    split_ifs with hvs_eq
    · nomatch hv (Fin.last n) hvs_eq.symm
    · exact @ih _ _ (hv ·.castSucc)

theorem TypeContext.update_lookup_iff {𝒱} [DecidableEq 𝒱] {n} {Γ : TypeContext 𝒱} {vs : Fin n → 𝒱} (vs_inj : Function.Injective vs) {αs : Fin n → BType} {v : 𝒱} {τ : BType}:
  Γ.update vs αs v = some τ ↔ (∃ i, vs i = v ∧ αs i = τ) ∨ (∀ i, vs i ≠ v) ∧ Γ v = some τ := by
  constructor
  · intro h
    by_cases hvs : ∃ i, vs i = v
    · obtain ⟨i, rfl⟩ := hvs
      left
      exists i
      rw [TypeContext.update_lookup_self vs_inj, Option.some_inj] at h
      exact ⟨rfl, h⟩
    · push_neg at hvs
      right
      rw [TypeContext.update_lookup_not_self hvs] at h
      exact ⟨hvs, h⟩
  · induction n generalizing v τ with
  | zero =>
    rintro (⟨i, rfl, rfl⟩ | ⟨hvs, τ_eq⟩)
    · nomatch i
    · rwa [TypeContext.update, Fin.foldl_zero]
  | succ n ih =>
    rintro (⟨i, rfl, rfl⟩ | ⟨hvs, τ_eq⟩)
    · by_cases i_eq : i = ⟨n, Nat.lt_add_one n⟩
      · subst i
        rw [TypeContext.update, Fin.foldl_succ_last]
        apply Function.update_self
      · exact update_lookup_self vs_inj
    · rw [←τ_eq]
      exact TypeContext.update_lookup_not_self hvs

end PHOAS

open Classical in
noncomputable def TypeContext.abstract (Γ : TypeContext) {𝒱} [DecidableEq 𝒱] {«Δ» : B.𝒱 → Option 𝒱} :
  PHOAS.TypeContext 𝒱 := fun x : 𝒱 =>
    if h : ∃ k, «Δ» k = .some x ∧ k ∈ Γ then
      Γ.lookup <| choose h
    else .none

end B
