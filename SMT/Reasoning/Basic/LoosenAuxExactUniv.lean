import SMT.Reasoning.Basic.LoosenAuxSpec
import SMT.Reasoning.Basic.LoosenAuxExact

open Std.Do SMT ZFSet Classical

/-!
# Delta-universal exactness for loosening helpers

`loosenAux_prf_exact` proves both directions needed by a locally scoped helper:
the selected witness satisfies its specification, and every value satisfying
the specification belongs to the cast relation.  The theorem below reindexes
that contract over arbitrary renaming contexts without rerunning the encoder.
-/

theorem loosenAux_prf_exact_univ
    {Λ : SMT.TypeContext} {n : ℕ} {used : List SMT.𝒱} {name : String}
    {x : SMT.Term} {α β : SMTType}
    (typ_x : Λ ⊢ˢ x : α) (hbv_x : ∀ v ∈ bv x, v ∈ used)
    (𝕔 : α ~> β) :
    ⦃ fun ⟨E, Λ'⟩ =>
        ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ Λ'.keys ⊆ E.usedVars ∧
          E.usedVars = used⌝ ⦄
      loosenAux_prf name 𝕔 x
    ⦃ ⇓? ⟨x!, x!_spec⟩ ⟨E', Γ'⟩ => ⌜
      n ≤ E'.freshvarsc ∧
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
      ∀ («Δ» : RenamingContext.Context)
        (hx : RenamingContext.CoversFV «Δ» x)
        (_respects : SMT.RenamingContext.RespectsTypeContextOnFV «Δ» Λ x)
        (pf : ∀ (x_! : SMT.𝒱) (X! : SMT.Dom),
          ∀ v ∈ SMT.fv (Term.var x_!),
            (Function.update «Δ» x_! (some X!) v).isSome = true),
      ∀ (X : SMT.Dom), ⟦x.abstract «Δ» hx⟧ˢ = some X →
        ∃ (Φ X! : SMT.Dom)
          (_ : ⟦(Term.var x!).abstract
            (Function.update «Δ» x! (some X!)) (pf x! X!)⟧ˢ = some X!)
          (hφ : RenamingContext.CoversFV
            (Function.update «Δ» x! (some X!)) x!_spec)
          (_ : ⟦x!_spec.abstract
            (Function.update «Δ» x! (some X!)) hφ⟧ˢ = some Φ),
          X!.2.1 = β ∧
          Φ.2.1 = SMTType.bool ∧
          (Φ.1 = zftrue ∧
            (X.1.pair X!.1) ∈ (castZF_of_path 𝕔).1) ∧
          ∀ (Y : SMT.Dom) (_ : Y.2.1 = β)
            (hφY : RenamingContext.CoversFV
              (Function.update «Δ» x! (some Y)) x!_spec),
            (⟦x!_spec.abstract
              (Function.update «Δ» x! (some Y)) hφY⟧ˢ).isSome = true ∧
            ∀ {ΦY : SMT.Dom},
              ⟦x!_spec.abstract
                (Function.update «Δ» x! (some Y)) hφY⟧ˢ = some ΦY →
              ΦY.1 = zftrue →
              (X.1.pair Y.1) ∈ (castZF_of_path 𝕔).1⌝ ⦄ := by
  intro st pst
  have key : ∀ (Q' : PostCond _ (.arg EncoderState (.except String .pure))),
      (wp⟦loosenAux_prf name 𝕔 x⟧ Q' st).down =
        match (loosenAux_prf name 𝕔 x st : Except _ _) with
        | .ok r => (Q'.1 r.1 r.2).down
        | .error e => (Q'.2.1 e).down := by
    intro Q'
    simp [WP.wp]
    cases (loosenAux_prf name 𝕔 x st : Except _ _) <;> rfl
  have hi : ∀ («Δ» : RenamingContext.Context)
      (hx : RenamingContext.CoversFV «Δ» x)
      (respects : SMT.RenamingContext.RespectsTypeContextOnFV «Δ» Λ x),
      (wp⟦loosenAux_prf name 𝕔 x⟧
        (PostCond.mayThrow fun ⟨x_!, x_!_spec⟩ ⟨E', Γ'⟩ => ⌜
          n ≤ E'.freshvarsc ∧
          Λ.insert x_! β ⊆ Γ' ∧ x_! ∉ Λ ∧
          x_! ∉ used ∧ used ⊆ E'.usedVars ∧
          AList.keys Γ' ⊆ E'.usedVars ∧
          (∀ v ∈ used, v ∉ Λ → v ∉ Γ') ∧
          (Λ.insert x_! β) ⊢ˢ (.var x_!) : β ∧
          (Λ.insert x_! β) ⊢ˢ x_!_spec : .bool ∧
          Γ' ⊢ˢ (.var x_!) : β ∧
          Γ' ⊢ˢ x_!_spec : .bool ∧
          SMT.fv x_!_spec ⊆ SMT.fv x ∪ {x_!} ∧
          ∀ (X : SMT.Dom), ⟦x.abstract «Δ» hx⟧ˢ = some X →
            ∃ (Φ X! : SMT.Dom)
              (_ : ⟦(Term.var x_!).abstract
                (Function.update «Δ» x_! (some X!)) (fun v hv => by
                  rw [fv, List.mem_singleton] at hv
                  rw [hv, Function.update_self, Option.isSome_some])⟧ˢ = some X!)
              (hφ : RenamingContext.CoversFV
                (Function.update «Δ» x_! (some X!)) x_!_spec)
              (_ : ⟦x_!_spec.abstract
                (Function.update «Δ» x_! (some X!)) hφ⟧ˢ = some Φ),
              X!.2.1 = β ∧
              Φ.2.1 = SMTType.bool ∧
              (Φ.1 = zftrue ∧
                (X.1.pair X!.1) ∈ (castZF_of_path 𝕔).1) ∧
              ∀ (Y : SMT.Dom) (_ : Y.2.1 = β)
                (hφY : RenamingContext.CoversFV
                  (Function.update «Δ» x_! (some Y)) x_!_spec),
                (⟦x_!_spec.abstract
                  (Function.update «Δ» x_! (some Y)) hφY⟧ˢ).isSome = true ∧
                ∀ {ΦY : SMT.Dom},
                  ⟦x_!_spec.abstract
                    (Function.update «Δ» x_! (some Y)) hφY⟧ˢ = some ΦY →
                  ΦY.1 = zftrue →
                  (X.1.pair Y.1) ∈ (castZF_of_path 𝕔).1⌝)
        st).down :=
    fun «Δ» hx respects =>
      loosenAux_prf_exact typ_x hbv_x 𝕔 «Δ» hx respects st pst
  conv at hi =>
    intro «Δ» hx respects
    rw [key]
  show (wp⟦loosenAux_prf name 𝕔 x⟧ _ st).down
  rw [key]
  cases hxst : (loosenAux_prf name 𝕔 x st : Except _ _) with
  | ok r =>
      obtain ⟨⟨x!, x!_spec⟩, ⟨E', Γ'⟩⟩ := r
      let Δdummy : RenamingContext.Context :=
        SMT.RenamingContext.ofTypeContext Λ
      have hresp_dummy : SMT.RenamingContext.RespectsTypeContext Δdummy Λ :=
        SMT.RenamingContext.respectsTypeContext_of_ofTypeContext Λ
      have hcov_dummy : RenamingContext.CoversFV Δdummy x :=
        SMT.RenamingContext.coversFV_of_typing_and_respects typ_x hresp_dummy
      have hresp_dummy_fv :
          SMT.RenamingContext.RespectsTypeContextOnFV Δdummy Λ x :=
        fun _ _ _ hlk => hresp_dummy hlk
      have hd := hi Δdummy hcov_dummy hresp_dummy_fv
      rw [hxst] at hd
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, _⟩ := hd
      refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, ?_⟩
      intro «Δ» hx hresp pf X hX_den
      have hΔ := hi «Δ» hx hresp
      rw [hxst] at hΔ
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hadq⟩ := hΔ
      obtain ⟨Φ, X!, hvar, hφ, hspec, hX!ty, hΦty, hcast, htotal⟩ :=
        hadq X hX_den
      refine ⟨Φ, X!, ?_, hφ, hspec, hX!ty, hΦty, hcast, htotal⟩
      convert hvar
  | error _ => trivial
