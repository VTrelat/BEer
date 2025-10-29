import Std.Tactic.Do
import SMT.Reasoning.Basic

open Batteries Std.Do B SMT ZFSet

-- Main theorem
open B SMT ZFSet in
theorem encodeTerm_spec (E : B.Env) {Λ : SMT.TypeContext} {t : B.Term} {α : B.BType}
  (typ_t : E.context ⊢ t : α) {«Δ» : B.𝒱 → Option B.Dom}
  (Δ_fv : ∀ v ∈ B.fv t, («Δ» v).isSome)
  {T : ZFSet} {hT : T ∈ ⟦α⟧ᶻ} (den_t : ⟦t.abstract «Δ» Δ_fv⟧ᴮ = Option.some ⟨T, α, hT⟩) {n : ℕ} :
  ⦃ fun ⟨E, Λ'⟩ ↦ ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ n ≤ Λ'.keys.length⌝ ⦄
  encodeTerm t E
  ⦃ ⇓? (⟨t', σ⟩ : SMT.Term × SMTType) ⟨E', Γ'⟩ => ⌜
    n ≤ E'.freshvarsc ∧ E'.freshvarsc ≤ Γ'.keys.length ∧
    Γ' = Λ ∧
    σ = α.toSMTType ∧
    (Γ' ⊢ t' : σ) ∧
    (∃ (hΔ : _) (denT' : SMT.Dom),
      ⟦t'.abstract (B.RenamingContext.toSMT «Δ») hΔ⟧ˢ = Option.some denT'
      ∧ ⟨T, α, hT⟩ ≘ᶻ denT')⌝⦄ := by
  induction t generalizing E n α «Δ» T hT with
  | «ℤ»                      => exact encodeTerm_spec.ℤ E typ_t Δ_fv den_t
  | 𝔹                        => exact encodeTerm_spec.𝔹 E typ_t Δ_fv den_t
  | var v                    => exact encodeTerm_spec.var v E typ_t Δ_fv den_t
  | int i                    => exact encodeTerm_spec.int i E typ_t Δ_fv den_t
  | bool b                   => exact encodeTerm_spec.bool b E typ_t Δ_fv den_t
  | maplet x y x_ih y_ih     => exact encodeTerm_spec.maplet x y x_ih y_ih E typ_t Δ_fv den_t
  | add x y x_ih y_ih        => exact encodeTerm_spec.add x y x_ih y_ih E typ_t Δ_fv den_t
  | sub x y x_ih y_ih        => sorry
  | mul x y x_ih y_ih        => sorry
  | le x y x_ih y_ih         => sorry
  | and x y x_ih y_ih        => sorry
  | not x ih                 => sorry
  | pow S ih                 => sorry
  | min S ih                 => sorry
  | max S ih                 => sorry
  | card S ih                => sorry
  | cprod S T S_ih T_ih      => sorry
  | mem x S x_ih S_ih        => exact encodeTerm_spec.mem x S x_ih S_ih E typ_t Δ_fv den_t
  | eq x y x_ih y_ih         => sorry
  | union S T S_ih T_ih      => sorry
  | inter S T S_ih T_ih      => sorry
  | app f x f_ih x_ih        => sorry
  | pfun A B A_ih B_ih       => sorry
  | collect vs D P D_ih P_ih => sorry
  | lambda vs D P D_ih P_ih  => sorry
  | all vs D P D_ih P_ih     => sorry
