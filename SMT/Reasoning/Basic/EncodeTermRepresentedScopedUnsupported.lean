import SMT.Reasoning.Basic.EncodeTermRepresentedScopedArith

open Std.Do B SMT ZFSet

/-! # Declaration-aware contracts for unsupported arithmetic terms -/

theorem encodeTerm_rep_scoped.min_case_from.{u}
    (S : B.Term) (_ih : EncodeTermRepIH.{u} S)
    (_scoped : EncodeTermRepScopedFromIH.{u} S)
    (E : B.Env) {Λ : SMT.TypeContext} {α : BType}
    (_typ_t : E.context ⊢ᴮ B.Term.min S : α)
    {«Δ» : B.RenamingContext.Context}
    (_Δ_fv : ∀ v ∈ B.fv (B.Term.min S), («Δ» v).isSome = true)
    {Δ₀ : SMT.RenamingContext.Context.{u}}
    (_related : RValuationCastSupportedOnFV «Δ» Δ₀ (B.Term.min S))
    {used : List SMT.𝒱}
    (_Δ₀_none_out : ∀ v ∉ used, Δ₀ v = none)
    (_Δ₀_dom : ∀ v, Δ₀ v ≠ none → v ∈ Λ)
    {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ}
    (_den_t : ⟦(B.Term.min S).abstract «Δ» _Δ_fv⟧ᴮ =
      some ⟨T, ⟨α, hT⟩⟩)
    (_vars_used : ∀ v ∈ (B.Term.min S).vars, v ∈ used)
    (_Λ_inv : ∀ v ∈ (B.Term.min S).vars,
      v ∈ Λ → v ∈ E.context)
    (_bv_nodup : (B.bv (B.Term.min S)).Nodup)
    (_respects : B.RenamingContext.RespectsTypeContextOnFV
      Δ₀ Λ (B.Term.min S))
    (_fv_in_Λ : ∀ v ∈ B.fv (B.Term.min S), v ∈ Λ)
    (_wf : B.RenWF E.context «Δ»)
    {Base : SMT.TypeContext} {Dpre : SMT.Chunk}
    (_input_envelope : DeclarationContextEnvelope Base Dpre Λ)
    (_fv_in_Base : ∀ v ∈ B.fv (B.Term.min S), v ∈ Base)
    (_Dpre_typing : ScopedSpecsTyping Base Dpre)
    {n : ℕ} {decl : SMT.Chunk} :
    ⦃fun ⟨E0, Λ'⟩ ↦
      ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧
        Λ.keys ⊆ E0.usedVars ∧ E0.usedVars = used ∧
        E0.declarations = decl⌝⦄
    encodeTerm (B.Term.min S) E
    ⦃⇓? (⟨t', σ⟩ : SMT.Term × SMTType) ⟨E', Γ'⟩ =>
      ⌜EncodeTermRepScopedPostFrom.{u} (B.Term.min S) E α
        Base Dpre Λ decl t' σ E' Γ'⌝⦄ := by
  exact fun _ _ => trivial

theorem encodeTerm_rep_scoped.max_case_from.{u}
    (S : B.Term) (_ih : EncodeTermRepIH.{u} S)
    (_scoped : EncodeTermRepScopedFromIH.{u} S)
    (E : B.Env) {Λ : SMT.TypeContext} {α : BType}
    (_typ_t : E.context ⊢ᴮ B.Term.max S : α)
    {«Δ» : B.RenamingContext.Context}
    (_Δ_fv : ∀ v ∈ B.fv (B.Term.max S), («Δ» v).isSome = true)
    {Δ₀ : SMT.RenamingContext.Context.{u}}
    (_related : RValuationCastSupportedOnFV «Δ» Δ₀ (B.Term.max S))
    {used : List SMT.𝒱}
    (_Δ₀_none_out : ∀ v ∉ used, Δ₀ v = none)
    (_Δ₀_dom : ∀ v, Δ₀ v ≠ none → v ∈ Λ)
    {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ}
    (_den_t : ⟦(B.Term.max S).abstract «Δ» _Δ_fv⟧ᴮ =
      some ⟨T, ⟨α, hT⟩⟩)
    (_vars_used : ∀ v ∈ (B.Term.max S).vars, v ∈ used)
    (_Λ_inv : ∀ v ∈ (B.Term.max S).vars,
      v ∈ Λ → v ∈ E.context)
    (_bv_nodup : (B.bv (B.Term.max S)).Nodup)
    (_respects : B.RenamingContext.RespectsTypeContextOnFV
      Δ₀ Λ (B.Term.max S))
    (_fv_in_Λ : ∀ v ∈ B.fv (B.Term.max S), v ∈ Λ)
    (_wf : B.RenWF E.context «Δ»)
    {Base : SMT.TypeContext} {Dpre : SMT.Chunk}
    (_input_envelope : DeclarationContextEnvelope Base Dpre Λ)
    (_fv_in_Base : ∀ v ∈ B.fv (B.Term.max S), v ∈ Base)
    (_Dpre_typing : ScopedSpecsTyping Base Dpre)
    {n : ℕ} {decl : SMT.Chunk} :
    ⦃fun ⟨E0, Λ'⟩ ↦
      ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧
        Λ.keys ⊆ E0.usedVars ∧ E0.usedVars = used ∧
        E0.declarations = decl⌝⦄
    encodeTerm (B.Term.max S) E
    ⦃⇓? (⟨t', σ⟩ : SMT.Term × SMTType) ⟨E', Γ'⟩ =>
      ⌜EncodeTermRepScopedPostFrom.{u} (B.Term.max S) E α
        Base Dpre Λ decl t' σ E' Γ'⌝⦄ := by
  exact fun _ _ => trivial

theorem encodeTerm_rep_scoped.card_case_from.{u}
    (S : B.Term) (_ih : EncodeTermRepIH.{u} S)
    (_scoped : EncodeTermRepScopedFromIH.{u} S)
    (E : B.Env) {Λ : SMT.TypeContext} {α : BType}
    (_typ_t : E.context ⊢ᴮ B.Term.card S : α)
    {«Δ» : B.RenamingContext.Context}
    (_Δ_fv : ∀ v ∈ B.fv (B.Term.card S), («Δ» v).isSome = true)
    {Δ₀ : SMT.RenamingContext.Context.{u}}
    (_related : RValuationCastSupportedOnFV «Δ» Δ₀ (B.Term.card S))
    {used : List SMT.𝒱}
    (_Δ₀_none_out : ∀ v ∉ used, Δ₀ v = none)
    (_Δ₀_dom : ∀ v, Δ₀ v ≠ none → v ∈ Λ)
    {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ}
    (_den_t : ⟦(B.Term.card S).abstract «Δ» _Δ_fv⟧ᴮ =
      some ⟨T, ⟨α, hT⟩⟩)
    (_vars_used : ∀ v ∈ (B.Term.card S).vars, v ∈ used)
    (_Λ_inv : ∀ v ∈ (B.Term.card S).vars,
      v ∈ Λ → v ∈ E.context)
    (_bv_nodup : (B.bv (B.Term.card S)).Nodup)
    (_respects : B.RenamingContext.RespectsTypeContextOnFV
      Δ₀ Λ (B.Term.card S))
    (_fv_in_Λ : ∀ v ∈ B.fv (B.Term.card S), v ∈ Λ)
    (_wf : B.RenWF E.context «Δ»)
    {Base : SMT.TypeContext} {Dpre : SMT.Chunk}
    (_input_envelope : DeclarationContextEnvelope Base Dpre Λ)
    (_fv_in_Base : ∀ v ∈ B.fv (B.Term.card S), v ∈ Base)
    (_Dpre_typing : ScopedSpecsTyping Base Dpre)
    {n : ℕ} {decl : SMT.Chunk} :
    ⦃fun ⟨E0, Λ'⟩ ↦
      ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧
        Λ.keys ⊆ E0.usedVars ∧ E0.usedVars = used ∧
        E0.declarations = decl⌝⦄
    encodeTerm (B.Term.card S) E
    ⦃⇓? (⟨t', σ⟩ : SMT.Term × SMTType) ⟨E', Γ'⟩ =>
      ⌜EncodeTermRepScopedPostFrom.{u} (B.Term.card S) E α
        Base Dpre Λ decl t' σ E' Γ'⌝⦄ := by
  exact fun _ _ => trivial
