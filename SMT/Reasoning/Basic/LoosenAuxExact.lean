import SMT.Reasoning.Defs
import SMT.Reasoning.LooseningDefs
import SMT.Reasoning.Basic.StateSpecs
import SMT.Reasoning.Basic.LoosenAuxExact.Refl
import SMT.Reasoning.Basic.LoosenAuxExact.Pair
import SMT.Reasoning.Basic.LoosenAuxExact.Opt
import SMT.Reasoning.Basic.LoosenAuxExact.Chpred
import SMT.Reasoning.Basic.LoosenAuxExact.Graph
import SMT.Reasoning.Basic.LoosenAuxExact.Fun

open Std.Do SMT ZFSet Classical

--set_option maxHeartbeats 800000 in
@[spec]
theorem loosenAux_prf_exact
  {Λ : SMT.TypeContext} {n : ℕ} {used : List SMT.𝒱} {name : String}
  {x : SMT.Term} {α β : SMTType}
  (typ_x : Λ ⊢ˢ x : α) (𝕔 : α ~> β)
  («Δ» : RenamingContext.Context)
  (hx : RenamingContext.CoversFV «Δ» x) :
  ⦃ fun ⟨E, Λ'⟩ => ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ Λ'.keys ⊆ E.usedVars ∧ E.usedVars = used⌝ ⦄
    loosenAux_prf name 𝕔 x
  ⦃ ⇓? ⟨x!, x!_spec⟩ ⟨E', Γ'⟩ =>
     ⌜ n ≤ E'.freshvarsc ∧
       Λ.insert x! β ⊆ Γ' ∧ x! ∉ Λ ∧
       x! ∉ used ∧
       used ⊆ E'.usedVars ∧
       AList.keys Γ' ⊆ E'.usedVars ∧
       (∀ v ∈ used, v ∉ Λ → v ∉ Γ') ∧
       (Λ.insert x! β) ⊢ˢ (.var x!) : β ∧
       (Λ.insert x! β) ⊢ˢ x!_spec : .bool ∧
       Γ' ⊢ˢ (.var x!) : β ∧
       Γ' ⊢ˢ x!_spec : .bool ∧
       SMT.fv x!_spec ⊆ SMT.fv x ∪ {x!} ∧
       ∀ (X : SMT.Dom), ⟦x.abstract «Δ» hx⟧ˢ = some X →
         ∃ (Φ X! : SMT.Dom)
           (_ : ⟦(Term.var x!).abstract (Function.update «Δ» x! (some X!)) (fun v hv ↦ by
             rw [fv, List.mem_singleton] at hv
             rw [hv, Function.update_self, Option.isSome_some])⟧ˢ = some X!)
           (hφ : RenamingContext.CoversFV (Function.update «Δ» x! (some X!)) x!_spec)
           (_ : ⟦x!_spec.abstract (Function.update «Δ» x! (some X!)) hφ⟧ˢ = some Φ),
           (Φ.2.1 = SMTType.bool) ∧
           (Φ.1 = zftrue ∧ (X.1.pair X!.1) ∈ (castZF_of_path 𝕔).1) ∧
           (∀ (Y : SMT.Dom) (_ : Y.2.1 = β)
             (hφY : RenamingContext.CoversFV (Function.update «Δ» x! (some Y)) x!_spec),
             (⟦x!_spec.abstract (Function.update «Δ» x! (some Y)) hφY⟧ˢ).isSome = true ∧
             ∀ {ΦY : SMT.Dom},
               ⟦x!_spec.abstract (Function.update «Δ» x! (some Y)) hφY⟧ˢ = some ΦY →
               ΦY.1 = zftrue →
               (X.1.pair Y.1) ∈ (castZF_of_path 𝕔).1)⌝ ⦄ := by
  generalize_proofs pf
  revert «Δ» hx pf
  induction 𝕔 generalizing x Λ n used name with
  | @refl α hα =>
      intro «Δ» hx pf
      exact loosenAux_prf_exact.refl «Δ» hα typ_x hx pf
  | @pair α β α' β' pα pβ pα_ih pβ_ih =>
      intro «Δ» hx pf
      exact loosenAux_prf_exact.pair «Δ» pα pβ pf (pα_ih · «Δ» · pf) (pβ_ih · «Δ» · pf) typ_x hx
  | @opt α α' hα ih =>
      intro «Δ» hx pf
      exact loosenAux_prf_exact.opt «Δ» pf hα ih typ_x hx
  | @chpred α α' p ih =>
      intro «Δ» hx pf
      exact loosenAux_prf_exact.chpred «Δ» pf p ih typ_x hx
  | @graph α β α' β' pα pβ pα_ih pβ_ih =>
      intro «Δ» hx pf
      apply loosenAux_prf_exact.graph pα pβ pα_ih pβ_ih typ_x
  | @«fun» α β α' β' hβ pα pβ pα_ih pβ_ih =>
      intro «Δ» hx pf
      exact loosenAux_prf_exact.fun hβ pα pβ pα_ih pβ_ih typ_x «Δ» hx pf
