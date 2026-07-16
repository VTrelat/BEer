import SMT.Reasoning.EncodeTermRepresentedDefs

open Std.Do B SMT ZFSet

/-! # Representation-aware base cases -/

/-- A functional B relation may be supplied to a variable through its
option-function representation.  The graph cast is the witness required by
`RDomCast`; after graphing, the usual B retraction recovers the source
relation. -/
theorem RDomCast.functionalGraph_as_optionFunction.{u}
    (α β : BType) {X Y : ZFSet.{u}}
    (hX : X ∈ ⟦BType.set (α ×ᴮ β)⟧ᶻ)
    (hY : Y ∈
      ⟦SMTType.fun (SMTType.pair α.toSMTType β.toSMTType) SMTType.bool⟧ᶻ)
    (hfun : (predGraph α.toSMTType β.toSMTType Y).IsPFunc
      ⟦α.toSMTType⟧ᶻ ⟦β.toSMTType⟧ᶻ)
    (hret : retract (BType.set (α ×ᴮ β)) Y = X) :
    RDomCast
      (⟨X, BType.set (α ×ᴮ β), hX⟩ : B.Dom)
      (⟨graphCollapse α.toSMTType β.toSMTType Y,
        SMTType.fun α.toSMTType (SMTType.option β.toSMTType),
        graphCollapse_mem α.toSMTType β.toSMTType Y⟩ : SMT.Dom) := by
  refine ⟨castPath.graph (castPath.reflexive α.toSMTType)
    (castPath.reflexive β.toSMTType), ?_⟩
  change retract (BType.set (α ×ᴮ β))
    (optionGraph α.toSMTType β.toSMTType
      (graphCollapse α.toSMTType β.toSMTType Y)) = X
  rw [optionGraph_graphCollapse α.toSMTType β.toSMTType Y hY hfun, hret]

/-- Concrete Gate A witness: a free relation variable and its option-function
SMT declaration satisfy the representation-aware valuation relation. -/
theorem RValuationCastOnFV.var_optionFunction.{u}
    (v : B.𝒱) (α β : BType) {X Y : ZFSet.{u}}
    (hX : X ∈ ⟦BType.set (α ×ᴮ β)⟧ᶻ)
    (hY : Y ∈
      ⟦SMTType.fun (SMTType.pair α.toSMTType β.toSMTType) SMTType.bool⟧ᶻ)
    (hfun : (predGraph α.toSMTType β.toSMTType Y).IsPFunc
      ⟦α.toSMTType⟧ᶻ ⟦β.toSMTType⟧ᶻ)
    (hret : retract (BType.set (α ×ᴮ β)) Y = X)
    {«Δ» : B.RenamingContext.Context}
    {Δ₀ : SMT.RenamingContext.Context.{u}}
    (hΔ : «Δ» v = some (⟨X, BType.set (α ×ᴮ β), hX⟩ : B.Dom))
    (hΔ₀ : Δ₀ v = some
      (⟨graphCollapse α.toSMTType β.toSMTType Y,
        SMTType.fun α.toSMTType (SMTType.option β.toSMTType),
        graphCollapse_mem α.toSMTType β.toSMTType Y⟩ : SMT.Dom)) :
    RValuationCastOnFV «Δ» Δ₀ (B.Term.var v) := by
  intro w hw
  rw [B.fv, List.mem_singleton] at hw
  subst w
  rw [hΔ, hΔ₀]
  exact RDomCast.functionalGraph_as_optionFunction α β hX hY hfun hret

theorem encodeTerm_rep_spec.var_case.{u}
    (v : B.𝒱) (E : B.Env) {Λ : SMT.TypeContext} {α : BType}
    (_typ_t : E.context ⊢ᴮ B.Term.var v : α)
    {«Δ» : B.RenamingContext.Context}
    (Δ_fv : ∀ w ∈ B.fv (B.Term.var v), («Δ» w).isSome = true)
    {Δ₀ : SMT.RenamingContext.Context.{u}}
    (related : RValuationCastOnFV «Δ» Δ₀ (B.Term.var v))
    {used : List SMT.𝒱}
    (Δ₀_none_out : ∀ w ∉ used, Δ₀ w = none)
    (Δ₀_dom : ∀ w, Δ₀ w ≠ none → w ∈ Λ)
    {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ}
    (den_t : ⟦(B.Term.var v).abstract «Δ» Δ_fv⟧ᴮ =
      some ⟨T, ⟨α, hT⟩⟩)
    (_vars_used : ∀ w ∈ (B.Term.var v).vars, w ∈ used)
    (Λ_inv : ∀ w ∈ (B.Term.var v).vars, w ∈ Λ → w ∈ E.context)
    (_bv_nodup : (B.bv (B.Term.var v)).Nodup)
    (respects : B.RenamingContext.RespectsTypeContextOnFV
      Δ₀ Λ (B.Term.var v))
    (fv_in_Λ : ∀ w ∈ B.fv (B.Term.var v), w ∈ Λ)
    (_wf : B.RenWF E.context «Δ»)
    {n : ℕ} :
    ⦃ fun ⟨E0, Λ'⟩ ↦
      ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧
        Λ.keys ⊆ E0.usedVars ∧ E0.usedVars = used⌝ ⦄
    encodeTerm (B.Term.var v) E
    ⦃ ⇓? (⟨t', σ⟩ : SMT.Term × SMTType) ⟨E', Γ'⟩ =>
      ⌜EncodeTermRepPost (B.Term.var v) α Λ «Δ» Δ₀ used T hT
        E t' σ E' Γ'⌝ ⦄ := by
  mstart
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
  rw [encodeTerm]
  mvcgen
  case vc1 τ τ_lookup =>
    have hv_fv : v ∈ B.fv (B.Term.var v) := by simp [B.fv]
    have hΔ_v : «Δ» v = some (⟨T, α, hT⟩ : B.Dom) := by
      rw [B.Term.abstract, B.denote] at den_t
      simp only [Option.pure_def, Option.some.injEq] at den_t
      have h_isSome := Δ_fv v hv_fv
      exact Option.some_get h_isSome ▸ congrArg some den_t
    have hrel_v := related v hv_fv
    rw [hΔ_v] at hrel_v
    cases hΔ₀_v : Δ₀ v with
    | none =>
        simp [hΔ₀_v] at hrel_v
    | some d =>
        have hR : RDomCast (⟨T, α, hT⟩ : B.Dom) d := by
          simpa [hΔ₀_v] using hrel_v
        obtain ⟨dτ, hdτ, hdτ_ty⟩ := respects hv_fv τ_lookup
        have hd_eq : d = dτ := Option.some.inj (hΔ₀_v.symm.trans hdτ)
        subst dτ
        rcases d with ⟨Y, σ, hY⟩
        dsimp at hdτ_ty
        subst τ
        obtain ⟨c, hc⟩ := hR
        and_intros
        · intro x hx
          simpa [St_used_eq] using hx
        · intro x hx
          simpa using hx
        · intro x hx
          simpa [St_used_eq] using St_sub hx
        · intro x hx
          rw [B.fv, List.mem_singleton] at hx
          subst x
          have hv_in_types : v ∈ St.types :=
            (AList.lookup_isSome).1 (Option.isSome_of_eq_some τ_lookup)
          simpa [St_used_eq] using St_sub hv_in_types
        · exact ⟨c⟩
        · exact SMT.Typing.var St.types v σ τ_lookup
        · exact fun _ _ h _ => h
        · refine ⟨Δ₀, ?_, ?_, related, ?_, respects, Δ₀_dom, ?_⟩
          · intro w hw
            rw [SMT.fv, List.mem_singleton] at hw
            subst w
            simp [hΔ₀_v]
          · exact RenamingContext.extends_refl Δ₀
          · intro w hw
            have hw' : w ∉ used := by
              intro hwu
              exact hw (by simpa [St_used_eq] using hwu)
            exact Δ₀_none_out w hw'
          · refine ⟨⟨Y, σ, hY⟩, ?_, ⟨c, hc⟩, ?_⟩
            · simp [SMT.Term.abstract, SMT.denote, hΔ₀_v]
            · intro Δ_alt Δ_fv_alt Δ₀_alt related_alt wf_alt
                Δ₀_alt_none respects_alt Δ₀_alt_dom T_alt hT_alt den_t_alt
              have hΔ_alt_v :
                  Δ_alt v = some (⟨T_alt, α, hT_alt⟩ : B.Dom) := by
                rw [B.Term.abstract, B.denote] at den_t_alt
                simp only [Option.pure_def, Option.some.injEq] at den_t_alt
                have h_isSome := Δ_fv_alt v hv_fv
                exact Option.some_get h_isSome ▸ congrArg some den_t_alt
              have hrel_alt := related_alt v hv_fv
              rw [hΔ_alt_v] at hrel_alt
              cases hΔ₀_alt_v : Δ₀_alt v with
              | none =>
                  simp [hΔ₀_alt_v] at hrel_alt
              | some d_alt =>
                  have hR_alt :
                      RDomCast (⟨T_alt, α, hT_alt⟩ : B.Dom) d_alt := by
                    simpa [hΔ₀_alt_v] using hrel_alt
                  refine ⟨Δ₀_alt, ?_, d_alt,
                    RenamingContext.extends_refl Δ₀_alt, related_alt,
                    Δ₀_alt_none, respects_alt, Δ₀_alt_dom, ?_, hR_alt⟩
                  · intro w hw
                    rw [SMT.fv, List.mem_singleton] at hw
                    subst w
                    simp [hΔ₀_alt_v]
                  · simp [SMT.Term.abstract, SMT.denote, hΔ₀_alt_v]
