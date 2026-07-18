import SMT.Reasoning.Basic.EncodeTermRepresentedBase

open Std.Do B SMT ZFSet

/-! # Generated-helper contracts for base terms -/

theorem encodeTerm_rep_scoped.var_case_from.{u}
    (v : B.𝒱) (E : B.Env) {Λ : SMT.TypeContext} {α : BType}
    (_typ_t : E.context ⊢ᴮ B.Term.var v : α)
    {«Δ» : B.RenamingContext.Context}
    (Δ_fv : ∀ w ∈ B.fv (B.Term.var v), («Δ» w).isSome = true)
    {Δ₀ : SMT.RenamingContext.Context.{u}}
    (_related : RValuationCastSupportedOnFV «Δ» Δ₀ (B.Term.var v))
    {used : List SMT.𝒱}
    (_Δ₀_none_out : ∀ w ∉ used, Δ₀ w = none)
    (_Δ₀_dom : ∀ w, Δ₀ w ≠ none → w ∈ Λ)
    {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ}
    (_den_t : ⟦(B.Term.var v).abstract «Δ» Δ_fv⟧ᴮ =
      some ⟨T, ⟨α, hT⟩⟩)
    (_vars_used : ∀ w ∈ (B.Term.var v).vars, w ∈ used)
    (_Λ_inv : ∀ w ∈ (B.Term.var v).vars, w ∈ Λ → w ∈ E.context)
    (_bv_nodup : (B.bv (B.Term.var v)).Nodup)
    (_respects : B.RenamingContext.RespectsTypeContextOnFV
      Δ₀ Λ (B.Term.var v))
    (_fv_in_Λ : ∀ w ∈ B.fv (B.Term.var v), w ∈ Λ)
    (_wf : B.RenWF E.context «Δ»)
    {Base : SMT.TypeContext} {Dpre : SMT.Chunk}
    (input_envelope : DeclarationContextEnvelope Base Dpre Λ)
    (fv_in_Base : ∀ w ∈ B.fv (B.Term.var v), w ∈ Base)
    (Dpre_typing : ScopedSpecsTyping Base Dpre)
    {n : ℕ} {decl : SMT.Chunk} :
    ⦃ fun ⟨E0, Λ'⟩ =>
      ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧
        Λ.keys ⊆ E0.usedVars ∧ E0.usedVars = used ∧
        E0.declarations = decl⌝ ⦄
    encodeTerm (B.Term.var v) E
    ⦃ ⇓? (⟨t', σ⟩ : SMT.Term × SMTType) ⟨E', Γ'⟩ =>
      ⌜EncodeTermRepScopedPostFrom.{u} (B.Term.var v) E α
        Base Dpre Λ decl t' σ E' Γ'⌝ ⦄ := by
  mstart
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_sub, St_used_eq, St_decl_eq⟩ := pre
  rw [encodeTerm]
  mvcgen
  case vc1 τ τ_lookup =>
    refine ⟨[], ?_, (by simpa using input_envelope), ?_, ?_, ?_⟩
    · simpa [St_decl_eq]
    · intro Δ_alt Δ_fv_alt Δ₀_alt related_alt wf_alt
        Δ₀_alt_none respects_alt Δ₀_alt_dom T_alt hT_alt den_t_alt
      have hv_fv : v ∈ B.fv (B.Term.var v) := by simp [B.fv]
      have hΔ_alt_v :
          Δ_alt v = some (⟨T_alt, α, hT_alt⟩ : B.Dom) := by
        rw [B.Term.abstract, B.denote] at den_t_alt
        simp only [Option.pure_def, Option.some.injEq] at den_t_alt
        have h_isSome := Δ_fv_alt v hv_fv
        exact Option.some_get h_isSome ▸ congrArg some den_t_alt
      have hrel_alt := related_alt v hv_fv
      rw [hΔ_alt_v] at hrel_alt
      cases hΔ₀_alt_v : Δ₀_alt v with
      | none => simp [hΔ₀_alt_v] at hrel_alt
      | some d_alt =>
          have hR_alt : RDomCastSupported
              (⟨T_alt, α, hT_alt⟩ : B.Dom) d_alt := by
            simpa [hΔ₀_alt_v] using hrel_alt
          refine ⟨Δ₀_alt, ?_, d_alt,
            RenamingContext.extends_refl Δ₀_alt, related_alt,
            Δ₀_alt_none, respects_alt, ?_, Δ₀_alt_dom, ?_, ?_, ?_, hR_alt⟩
          · intro w hw
            rw [SMT.fv, List.mem_singleton] at hw
            subst w
            simp [hΔ₀_alt_v]
          · intro w ξ hw hlookup
            rw [SMT.fv, List.mem_singleton] at hw
            subst w
            exact respects_alt hv_fv hlookup
          · simp [SpecBodiesTrue, specBodies]
          · simp [SMT.Term.abstract, SMT.denote, hΔ₀_alt_v]
          · obtain ⟨dτ, hdτ, hdτ_type⟩ :=
              respects_alt hv_fv τ_lookup
            have : d_alt = dτ :=
              Option.some.inj (hΔ₀_alt_v.symm.trans hdτ)
            subst dτ
            exact hdτ_type
    · intro Γ_sup Γ_sub Δ_alt Δ_fv_alt Θ related_alt wf_alt
        respects_B respects_SMT specs_true T_alt hT_alt den_t_alt
        hcov denT hdenT hdenT_type
      have hv_fv : v ∈ B.fv (B.Term.var v) := by simp [B.fv]
      have hΔ_alt_v :
          Δ_alt v = some (⟨T_alt, α, hT_alt⟩ : B.Dom) := by
        rw [B.Term.abstract, B.denote] at den_t_alt
        simp only [Option.pure_def, Option.some.injEq] at den_t_alt
        have h_isSome := Δ_fv_alt v hv_fv
        exact Option.some_get h_isSome ▸ congrArg some den_t_alt
      have hrel := related_alt v hv_fv
      rw [hΔ_alt_v] at hrel
      cases hΘv : Θ v with
      | none => simp [hΘv] at hrel
      | some d =>
          have hR : RDomCastSupported
              (⟨T_alt, α, hT_alt⟩ : B.Dom) d := by
            simpa [hΘv] using hrel
          have hden_var :
              ⟦(SMT.Term.var v).abstract Θ hcov⟧ˢ = some d := by
            simp [SMT.Term.abstract, SMT.denote, hΘv]
          rw [hden_var] at hdenT
          cases hdenT
          exact hR
    · constructor
      · intro Γ_sup Γ_sub _result_bv_fresh
        have hv_fv : v ∈ B.fv (B.Term.var v) := by simp [B.fv]
        have hv_Base : v ∈ Base := fv_in_Base v hv_fv
        obtain ⟨τBase, τBase_lookup⟩ :=
          Option.isSome_iff_exists.mp (AList.lookup_isSome.mpr hv_Base)
        have τ_lookup' := AList.lookup_of_subset
          input_envelope.scoped_extends.base τBase_lookup
        rw [τ_lookup] at τ_lookup'
        cases τ_lookup'
        exact SMT.Typing.var Γ_sup v τ
          (AList.lookup_of_subset Γ_sub.base τBase_lookup)
      · simpa using Dpre_typing

theorem encodeTerm_rep_scoped.int_case_from.{u}
    (i : ℤ) (E : B.Env) {Λ : SMT.TypeContext} {α : BType}
    (_typ_t : E.context ⊢ᴮ B.Term.int i : α)
    {«Δ» : B.RenamingContext.Context}
    (_Δ_fv : ∀ w ∈ B.fv (B.Term.int i), («Δ» w).isSome = true)
    {Δ₀ : SMT.RenamingContext.Context.{u}}
    (_related : RValuationCastSupportedOnFV «Δ» Δ₀ (B.Term.int i))
    {used : List SMT.𝒱}
    (_Δ₀_none_out : ∀ w ∉ used, Δ₀ w = none)
    (_Δ₀_dom : ∀ w, Δ₀ w ≠ none → w ∈ Λ)
    {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ}
    (den_t : ⟦(B.Term.int i).abstract «Δ» _Δ_fv⟧ᴮ =
      some ⟨T, ⟨α, hT⟩⟩)
    (_vars_used : ∀ w ∈ (B.Term.int i).vars, w ∈ used)
    (_Λ_inv : ∀ w ∈ (B.Term.int i).vars, w ∈ Λ → w ∈ E.context)
    (_bv_nodup : (B.bv (B.Term.int i)).Nodup)
    (_respects : B.RenamingContext.RespectsTypeContextOnFV
      Δ₀ Λ (B.Term.int i))
    (_fv_in_Λ : ∀ w ∈ B.fv (B.Term.int i), w ∈ Λ)
    (_wf : B.RenWF E.context «Δ»)
    {Base : SMT.TypeContext} {Dpre : SMT.Chunk}
    (input_envelope : DeclarationContextEnvelope Base Dpre Λ)
    (_fv_in_Base : ∀ w ∈ B.fv (B.Term.int i), w ∈ Base)
    (Dpre_typing : ScopedSpecsTyping Base Dpre)
    {n : ℕ} {decl : SMT.Chunk} :
    ⦃ fun ⟨E0, Λ'⟩ =>
      ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧
        Λ.keys ⊆ E0.usedVars ∧ E0.usedVars = used ∧
        E0.declarations = decl⌝ ⦄
    encodeTerm (B.Term.int i) E
    ⦃ ⇓? (⟨t', σ⟩ : SMT.Term × SMTType) ⟨E', Γ'⟩ =>
      ⌜EncodeTermRepScopedPostFrom.{u} (B.Term.int i) E α
        Base Dpre Λ decl t' σ E' Γ'⌝ ⦄ := by
  mstart
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, _St_sub, _St_used_eq, St_decl_eq⟩ := pre
  rw [encodeTerm]
  mspec Std.Do.Spec.pure
  mpure_intro
  rw [B.Term.abstract, B.denote, Option.pure_def,
    Option.some_inj] at den_t
  injection den_t with T_eq type_eq
  subst T
  injection type_eq with α_eq _
  subst α
  refine ⟨[], ?_, (by simpa using input_envelope), ?_, ?_, ?_⟩
  · simpa [St_decl_eq]
  · intro Δ_alt Δ_fv_alt Δ₀_alt related_alt _wf_alt
      Δ₀_alt_none respects_alt Δ₀_alt_dom T_alt hT_alt den_t_alt
    rw [B.Term.abstract, B.denote, Option.pure_def,
      Option.some_inj] at den_t_alt
    have hT_eq : ZFSet.ofInt i = T_alt :=
      congrArg (fun d => d.fst) den_t_alt
    subst T_alt
    refine ⟨Δ₀_alt, ?_, ⟨ZFSet.ofInt i, SMTType.int, hT_alt⟩,
      RenamingContext.extends_refl Δ₀_alt, related_alt,
      Δ₀_alt_none, respects_alt, ?_, Δ₀_alt_dom, ?_, ?_, rfl, ?_⟩
    · intro w hw
      simp [SMT.fv] at hw
    · intro w τ hw
      simp [SMT.fv] at hw
    · simp [SpecBodiesTrue, specBodies]
    · simp [SMT.Term.abstract, SMT.denote]
    · exact RDom.toRDomCastSupported ⟨rfl, by simp [retract]⟩
  · intro Γ_sup Γ_sub Δ_alt Δ_fv_alt Θ related_alt _wf_alt
      _respects_B _respects_SMT _specs_true T_alt hT_alt den_t_alt
      hcov denT hdenT hdenT_type
    rw [B.Term.abstract, B.denote, Option.pure_def,
      Option.some_inj] at den_t_alt
    have hT_eq : ZFSet.ofInt i = T_alt :=
      congrArg (fun d => d.fst) den_t_alt
    subst T_alt
    have hden :
        ⟦(SMT.Term.int i).abstract Θ hcov⟧ˢ =
          some ⟨ZFSet.ofInt i, SMTType.int, hT_alt⟩ := by
      simp [SMT.Term.abstract, SMT.denote]
    rw [hden] at hdenT
    cases hdenT
    exact RDom.toRDomCastSupported ⟨rfl, by simp [retract]⟩
  · constructor
    · intro Γ_sup _Γ_sub _result_bv_fresh
      exact SMT.Typing.int Γ_sup i
    · simpa using Dpre_typing

theorem encodeTerm_rep_scoped.bool_case_from.{u}
    (b : Bool) (E : B.Env) {Λ : SMT.TypeContext} {α : BType}
    (_typ_t : E.context ⊢ᴮ B.Term.bool b : α)
    {«Δ» : B.RenamingContext.Context}
    (_Δ_fv : ∀ w ∈ B.fv (B.Term.bool b), («Δ» w).isSome = true)
    {Δ₀ : SMT.RenamingContext.Context.{u}}
    (_related : RValuationCastSupportedOnFV «Δ» Δ₀ (B.Term.bool b))
    {used : List SMT.𝒱}
    (_Δ₀_none_out : ∀ w ∉ used, Δ₀ w = none)
    (_Δ₀_dom : ∀ w, Δ₀ w ≠ none → w ∈ Λ)
    {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ}
    (den_t : ⟦(B.Term.bool b).abstract «Δ» _Δ_fv⟧ᴮ =
      some ⟨T, ⟨α, hT⟩⟩)
    (_vars_used : ∀ w ∈ (B.Term.bool b).vars, w ∈ used)
    (_Λ_inv : ∀ w ∈ (B.Term.bool b).vars, w ∈ Λ → w ∈ E.context)
    (_bv_nodup : (B.bv (B.Term.bool b)).Nodup)
    (_respects : B.RenamingContext.RespectsTypeContextOnFV
      Δ₀ Λ (B.Term.bool b))
    (_fv_in_Λ : ∀ w ∈ B.fv (B.Term.bool b), w ∈ Λ)
    (_wf : B.RenWF E.context «Δ»)
    {Base : SMT.TypeContext} {Dpre : SMT.Chunk}
    (input_envelope : DeclarationContextEnvelope Base Dpre Λ)
    (_fv_in_Base : ∀ w ∈ B.fv (B.Term.bool b), w ∈ Base)
    (Dpre_typing : ScopedSpecsTyping Base Dpre)
    {n : ℕ} {decl : SMT.Chunk} :
    ⦃ fun ⟨E0, Λ'⟩ =>
      ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧
        Λ.keys ⊆ E0.usedVars ∧ E0.usedVars = used ∧
        E0.declarations = decl⌝ ⦄
    encodeTerm (B.Term.bool b) E
    ⦃ ⇓? (⟨t', σ⟩ : SMT.Term × SMTType) ⟨E', Γ'⟩ =>
      ⌜EncodeTermRepScopedPostFrom.{u} (B.Term.bool b) E α
        Base Dpre Λ decl t' σ E' Γ'⌝ ⦄ := by
  mstart
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, _St_sub, _St_used_eq, St_decl_eq⟩ := pre
  rw [encodeTerm]
  mspec Std.Do.Spec.pure
  mpure_intro
  rw [B.Term.abstract, B.denote, Option.pure_def,
    Option.some_inj] at den_t
  injection den_t with T_eq type_eq
  subst T
  injection type_eq with α_eq _
  subst α
  refine ⟨[], ?_, (by simpa using input_envelope), ?_, ?_, ?_⟩
  · simpa [St_decl_eq]
  · intro Δ_alt Δ_fv_alt Δ₀_alt related_alt _wf_alt
      Δ₀_alt_none respects_alt Δ₀_alt_dom T_alt hT_alt den_t_alt
    rw [B.Term.abstract, B.denote, Option.pure_def,
      Option.some_inj] at den_t_alt
    have hT_eq : ZFBool.ofBool b = T_alt :=
      congrArg (fun d => d.fst) den_t_alt
    subst T_alt
    refine ⟨Δ₀_alt, ?_, ⟨ZFBool.ofBool b, SMTType.bool, hT_alt⟩,
      RenamingContext.extends_refl Δ₀_alt, related_alt,
      Δ₀_alt_none, respects_alt, ?_, Δ₀_alt_dom, ?_, ?_, rfl, ?_⟩
    · intro w hw
      simp [SMT.fv] at hw
    · intro w τ hw
      simp [SMT.fv] at hw
    · simp [SpecBodiesTrue, specBodies]
    · simp [SMT.Term.abstract, SMT.denote]
    · exact RDom.toRDomCastSupported ⟨rfl, by simp [retract]⟩
  · intro Γ_sup Γ_sub Δ_alt Δ_fv_alt Θ related_alt _wf_alt
      _respects_B _respects_SMT _specs_true T_alt hT_alt den_t_alt
      hcov denT hdenT hdenT_type
    rw [B.Term.abstract, B.denote, Option.pure_def,
      Option.some_inj] at den_t_alt
    have hT_eq : ZFBool.ofBool b = T_alt :=
      congrArg (fun d => d.fst) den_t_alt
    subst T_alt
    have hden :
        ⟦(SMT.Term.bool b).abstract Θ hcov⟧ˢ =
          some ⟨ZFBool.ofBool b, SMTType.bool, hT_alt⟩ := by
      simp [SMT.Term.abstract, SMT.denote]
    rw [hden] at hdenT
    cases hdenT
    exact RDom.toRDomCastSupported ⟨rfl, by simp [retract]⟩
  · constructor
    · intro Γ_sup _Γ_sub _result_bv_fresh
      exact SMT.Typing.bool Γ_sup b
    · simpa using Dpre_typing
