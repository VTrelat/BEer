import SMT.Reasoning.EncodeTermRepresentedDefs
import SMT.Reasoning.Basic.EncodeTermCorrectBase

open Std.Do B SMT ZFSet

/-! # Representation-aware base cases -/

private theorem encodeTerm_ℤ_fv_nil
    (E : B.Env) {Λ : SMT.TypeContext} {n : ℕ} {used : List SMT.𝒱} :
    ⦃fun (⟨E0, Λ'⟩ : EncoderState) ↦
      ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧
        Λ.keys ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
    encodeTerm B.Term.ℤ E
    ⦃⇓? (⟨t', _σ⟩ : SMT.Term × SMTType) _St' =>
      ⌜SMT.fv t' = []⌝⦄ := by
  mstart
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, _St_sub, rfl⟩ := pre
  rw [encodeTerm]
  mspec Std.Do.Spec.get_StateT
  mspec SMT.freshVar_spec (Γ := St.types) (τ := .int)
    (n := St.env.freshvarsc) (used := St.env.usedVars)
  next v =>
    mrename_i pre
    mintro ∀St'
    mpure pre
    mspec Std.Do.Spec.modifyGet_StateT
    mspec Std.Do.Spec.pure
    mpure_intro
    simp [SMT.fv]

private theorem encodeTerm_𝔹_fv_nil
    (E : B.Env) {Λ : SMT.TypeContext} {n : ℕ} {used : List SMT.𝒱} :
    ⦃fun (⟨E0, Λ'⟩ : EncoderState) ↦
      ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧
        Λ.keys ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
    encodeTerm B.Term.𝔹 E
    ⦃⇓? (⟨t', _σ⟩ : SMT.Term × SMTType) _St' =>
      ⌜SMT.fv t' = []⌝⦄ := by
  mstart
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, _St_sub, rfl⟩ := pre
  rw [encodeTerm]
  mspec Std.Do.Spec.get_StateT
  mspec SMT.freshVar_spec (Γ := St.types) (τ := .bool)
    (n := St.env.freshvarsc) (used := St.env.usedVars)
  next v =>
    mrename_i pre
    mintro ∀St'
    mpure pre
    mspec Std.Do.Spec.modifyGet_StateT
    mspec Std.Do.Spec.pure
    mpure_intro
    simp [SMT.fv]

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

/-- The option-function witness also carries the preimage condition needed if
the relation is later used as a quantifier domain. -/
theorem RDomCastAdmissible.functionalGraph_as_optionFunction.{u}
    (α β : BType) {X Y : ZFSet.{u}}
    (hX : X ∈ ⟦BType.set (α ×ᴮ β)⟧ᶻ)
    (hY : Y ∈
      ⟦SMTType.fun (SMTType.pair α.toSMTType β.toSMTType) SMTType.bool⟧ᶻ)
    (hfun : (predGraph α.toSMTType β.toSMTType Y).IsPFunc
      ⟦α.toSMTType⟧ᶻ ⟦β.toSMTType⟧ᶻ)
    (hret : retract (BType.set (α ×ᴮ β)) Y = X) :
    RDomCastAdmissible
      (⟨X, BType.set (α ×ᴮ β), hX⟩ : B.Dom)
      (⟨graphCollapse α.toSMTType β.toSMTType Y,
        SMTType.fun α.toSMTType (SMTType.option β.toSMTType),
        graphCollapse_mem α.toSMTType β.toSMTType Y⟩ : SMT.Dom) := by
  refine ⟨castPath.graph (castPath.reflexive α.toSMTType)
    (castPath.reflexive β.toSMTType), ?_, ?_⟩
  · change retract (BType.set (α ×ᴮ β))
      (optionGraph α.toSMTType β.toSMTType
        (graphCollapse α.toSMTType β.toSMTType Y)) = X
    rw [optionGraph_graphCollapse α.toSMTType β.toSMTType Y hY hfun,
      hret]
  · exact ⟨castPath.reflexive (α ×ᴮ β).toSMTType,
      BinderCastAdmissible.reflexive (α ×ᴮ β) hX⟩

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

/-- Binder-admissible form of the concrete Gate A valuation witness. -/
theorem RValuationCastAdmissibleOnFV.var_optionFunction.{u}
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
    RValuationCastAdmissibleOnFV «Δ» Δ₀ (B.Term.var v) := by
  intro w hw
  rw [B.fv, List.mem_singleton] at hw
  subst w
  rw [hΔ, hΔ₀]
  exact RDomCastAdmissible.functionalGraph_as_optionFunction
    α β hX hY hfun hret

theorem encodeTerm_rep_spec.var_case.{u}
    (v : B.𝒱) (E : B.Env) {Λ : SMT.TypeContext} {α : BType}
    (_typ_t : E.context ⊢ᴮ B.Term.var v : α)
    {«Δ» : B.RenamingContext.Context}
    (Δ_fv : ∀ w ∈ B.fv (B.Term.var v), («Δ» w).isSome = true)
    {Δ₀ : SMT.RenamingContext.Context.{u}}
    (related : RValuationCastAdmissibleOnFV «Δ» Δ₀ (B.Term.var v))
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
        have hR : RDomCastAdmissible (⟨T, α, hT⟩ : B.Dom) d := by
          simpa [hΔ₀_v] using hrel_v
        obtain ⟨dτ, hdτ, hdτ_ty⟩ := respects hv_fv τ_lookup
        have hd_eq : d = dτ := Option.some.inj (hΔ₀_v.symm.trans hdτ)
        subst dτ
        rcases d with ⟨Y, σ, hY⟩
        dsimp at hdτ_ty
        subst τ
        obtain ⟨c, hc⟩ := hR.toRDomCast
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
        · simp [EncodeTermResultShape]
        · exact fun _ _ h _ => h
        · refine ⟨Δ₀, ?_, ?_, related, ?_, respects, ?_, Δ₀_dom, ?_⟩
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
          · intro w τ hw hlookup
            rw [SMT.fv, List.mem_singleton] at hw
            subst w
            exact respects hv_fv hlookup
          · refine ⟨⟨Y, σ, hY⟩, ?_, rfl, hR, ?_⟩
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
                      RDomCastAdmissible
                        (⟨T_alt, α, hT_alt⟩ : B.Dom) d_alt := by
                    simpa [hΔ₀_alt_v] using hrel_alt
                  refine ⟨Δ₀_alt, ?_, d_alt,
                    RenamingContext.extends_refl Δ₀_alt, related_alt,
                    Δ₀_alt_none, respects_alt, ?_, Δ₀_alt_dom,
                    ?_, ?_, hR_alt⟩
                  · intro w hw
                    rw [SMT.fv, List.mem_singleton] at hw
                    subst w
                    simp [hΔ₀_alt_v]
                  · intro w τ hw hlookup
                    rw [SMT.fv, List.mem_singleton] at hw
                    subst w
                    exact respects_alt hv_fv hlookup
                  · simp [SMT.Term.abstract, SMT.denote, hΔ₀_alt_v]
                  · obtain ⟨dτ, hdτ, hdτ_type⟩ :=
                      respects_alt hv_fv τ_lookup
                    have : d_alt = dτ :=
                      Option.some.inj (hΔ₀_alt_v.symm.trans hdτ)
                    subst dτ
                    exact hdτ_type

theorem encodeTerm_rep_spec.int_case.{u}
    (i : ℤ) (E : B.Env) {Λ : SMT.TypeContext} {α : BType}
    (_typ_t : E.context ⊢ᴮ B.Term.int i : α)
    {«Δ» : B.RenamingContext.Context}
    (Δ_fv : ∀ w ∈ B.fv (B.Term.int i), («Δ» w).isSome = true)
    {Δ₀ : SMT.RenamingContext.Context.{u}}
    (related : RValuationCastAdmissibleOnFV «Δ» Δ₀ (B.Term.int i))
    {used : List SMT.𝒱}
    (Δ₀_none_out : ∀ w ∉ used, Δ₀ w = none)
    (Δ₀_dom : ∀ w, Δ₀ w ≠ none → w ∈ Λ)
    {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ}
    (den_t : ⟦(B.Term.int i).abstract «Δ» Δ_fv⟧ᴮ =
      some ⟨T, ⟨α, hT⟩⟩)
    (_vars_used : ∀ w ∈ (B.Term.int i).vars, w ∈ used)
    (_Λ_inv : ∀ w ∈ (B.Term.int i).vars, w ∈ Λ → w ∈ E.context)
    (_bv_nodup : (B.bv (B.Term.int i)).Nodup)
    (respects : B.RenamingContext.RespectsTypeContextOnFV
      Δ₀ Λ (B.Term.int i))
    (_fv_in_Λ : ∀ w ∈ B.fv (B.Term.int i), w ∈ Λ)
    (_wf : B.RenWF E.context «Δ»)
    {n : ℕ} :
    ⦃ fun ⟨E0, Λ'⟩ ↦
      ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧
        Λ.keys ⊆ E0.usedVars ∧ E0.usedVars = used⌝ ⦄
    encodeTerm (B.Term.int i) E
    ⦃ ⇓? (⟨t', σ⟩ : SMT.Term × SMTType) ⟨E', Γ'⟩ =>
      ⌜EncodeTermRepPost (B.Term.int i) α Λ «Δ» Δ₀ used T hT
        E t' σ E' Γ'⌝ ⦄ := by
  mstart
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
  rw [encodeTerm]
  mspec Std.Do.Spec.pure
  mpure_intro
  rw [B.Term.abstract, B.denote, Option.pure_def,
    Option.some_inj] at den_t
  injection den_t with T_eq type_eq
  subst T
  injection type_eq with α_eq _
  subst α
  and_intros
  · intro w hw
    simpa [St_used_eq] using hw
  · exact fun _ => id
  · intro w hw
    simpa [St_used_eq] using St_sub hw
  · intro w hw
    simp [B.fv] at hw
  · exact ⟨castPath.reflexive SMTType.int⟩
  · exact SMT.Typing.int _ _
  · simp [EncodeTermResultShape]
  · exact fun _ _ h _ => h
  · refine ⟨Δ₀, ?_, RenamingContext.extends_refl Δ₀, related,
      ?_, respects, ?_, Δ₀_dom, ?_⟩
    · intro w hw
      simp [SMT.fv] at hw
    · intro w hw
      apply Δ₀_none_out w
      intro hused
      apply hw
      simpa [St_used_eq] using hused
    · intro w τ hw
      simp [SMT.fv] at hw
    · refine ⟨⟨ZFSet.ofInt i, SMTType.int, hT⟩, ?_, rfl, ?_, ?_⟩
      · simp [SMT.Term.abstract, SMT.denote]
      · exact RDom.toRDomCastAdmissible ⟨rfl, by simp [retract]⟩
      · intro Δ_alt Δ_fv_alt Δ₀_alt related_alt _wf_alt
          Δ₀_alt_none respects_alt Δ₀_alt_dom T_alt hT_alt den_t_alt
        rw [B.Term.abstract, B.denote, Option.pure_def,
          Option.some_inj] at den_t_alt
        have hT_eq : ZFSet.ofInt i = T_alt :=
          congrArg (fun d => d.fst) den_t_alt
        subst T_alt
        refine ⟨Δ₀_alt, ?_, ⟨ZFSet.ofInt i, SMTType.int, hT_alt⟩,
          RenamingContext.extends_refl Δ₀_alt, related_alt,
          Δ₀_alt_none, respects_alt, ?_, Δ₀_alt_dom, ?_, rfl, ?_⟩
        · intro w hw
          simp [SMT.fv] at hw
        · intro w τ hw
          simp [SMT.fv] at hw
        · simp [SMT.Term.abstract, SMT.denote]
        · exact RDom.toRDomCastAdmissible ⟨rfl, by simp [retract]⟩

theorem encodeTerm_rep_spec.bool_case.{u}
    (b : Bool) (E : B.Env) {Λ : SMT.TypeContext} {α : BType}
    (_typ_t : E.context ⊢ᴮ B.Term.bool b : α)
    {«Δ» : B.RenamingContext.Context}
    (Δ_fv : ∀ w ∈ B.fv (B.Term.bool b), («Δ» w).isSome = true)
    {Δ₀ : SMT.RenamingContext.Context.{u}}
    (related : RValuationCastAdmissibleOnFV «Δ» Δ₀ (B.Term.bool b))
    {used : List SMT.𝒱}
    (Δ₀_none_out : ∀ w ∉ used, Δ₀ w = none)
    (Δ₀_dom : ∀ w, Δ₀ w ≠ none → w ∈ Λ)
    {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ}
    (den_t : ⟦(B.Term.bool b).abstract «Δ» Δ_fv⟧ᴮ =
      some ⟨T, ⟨α, hT⟩⟩)
    (_vars_used : ∀ w ∈ (B.Term.bool b).vars, w ∈ used)
    (_Λ_inv : ∀ w ∈ (B.Term.bool b).vars, w ∈ Λ → w ∈ E.context)
    (_bv_nodup : (B.bv (B.Term.bool b)).Nodup)
    (respects : B.RenamingContext.RespectsTypeContextOnFV
      Δ₀ Λ (B.Term.bool b))
    (_fv_in_Λ : ∀ w ∈ B.fv (B.Term.bool b), w ∈ Λ)
    (_wf : B.RenWF E.context «Δ»)
    {n : ℕ} :
    ⦃ fun ⟨E0, Λ'⟩ ↦
      ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧
        Λ.keys ⊆ E0.usedVars ∧ E0.usedVars = used⌝ ⦄
    encodeTerm (B.Term.bool b) E
    ⦃ ⇓? (⟨t', σ⟩ : SMT.Term × SMTType) ⟨E', Γ'⟩ =>
      ⌜EncodeTermRepPost (B.Term.bool b) α Λ «Δ» Δ₀ used T hT
        E t' σ E' Γ'⌝ ⦄ := by
  mstart
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
  rw [encodeTerm]
  mspec Std.Do.Spec.pure
  mpure_intro
  rw [B.Term.abstract, B.denote, Option.pure_def,
    Option.some_inj] at den_t
  injection den_t with T_eq type_eq
  subst T
  injection type_eq with α_eq _
  subst α
  and_intros
  · intro w hw
    simpa [St_used_eq] using hw
  · exact fun _ => id
  · intro w hw
    simpa [St_used_eq] using St_sub hw
  · intro w hw
    simp [B.fv] at hw
  · exact ⟨castPath.reflexive SMTType.bool⟩
  · exact SMT.Typing.bool _ _
  · simp [EncodeTermResultShape]
  · exact fun _ _ h _ => h
  · refine ⟨Δ₀, ?_, RenamingContext.extends_refl Δ₀, related,
      ?_, respects, ?_, Δ₀_dom, ?_⟩
    · intro w hw
      simp [SMT.fv] at hw
    · intro w hw
      apply Δ₀_none_out w
      intro hused
      apply hw
      simpa [St_used_eq] using hused
    · intro w τ hw
      simp [SMT.fv] at hw
    · refine ⟨⟨ZFBool.ofBool b, SMTType.bool, hT⟩, ?_, rfl, ?_, ?_⟩
      · simp [SMT.Term.abstract, SMT.denote]
      · exact RDom.toRDomCastAdmissible ⟨rfl, by simp [retract]⟩
      · intro Δ_alt Δ_fv_alt Δ₀_alt related_alt _wf_alt
          Δ₀_alt_none respects_alt Δ₀_alt_dom T_alt hT_alt den_t_alt
        rw [B.Term.abstract, B.denote, Option.pure_def,
          Option.some_inj] at den_t_alt
        have hT_eq : ZFBool.ofBool b = T_alt :=
          congrArg (fun d => d.fst) den_t_alt
        subst T_alt
        refine ⟨Δ₀_alt, ?_, ⟨ZFBool.ofBool b, SMTType.bool, hT_alt⟩,
          RenamingContext.extends_refl Δ₀_alt, related_alt,
          Δ₀_alt_none, respects_alt, ?_, Δ₀_alt_dom, ?_, rfl, ?_⟩
        · intro w hw
          simp [SMT.fv] at hw
        · intro w τ hw
          simp [SMT.fv] at hw
        · simp [SMT.Term.abstract, SMT.denote]
        · exact RDom.toRDomCastAdmissible ⟨rfl, by simp [retract]⟩

set_option maxHeartbeats 1200000 in
theorem encodeTerm_rep_spec.ℤ_case.{u}
    (E : B.Env) {Λ : SMT.TypeContext} {α : BType}
    (typ_t : E.context ⊢ᴮ B.Term.ℤ : α)
    {«Δ» : B.RenamingContext.Context}
    (Δ_fv : ∀ v ∈ B.fv B.Term.ℤ, («Δ» v).isSome = true)
    {Δ₀ : SMT.RenamingContext.Context.{u}}
    (related : RValuationCastAdmissibleOnFV «Δ» Δ₀ B.Term.ℤ)
    {used : List SMT.𝒱}
    (Δ₀_none_out : ∀ v ∉ used, Δ₀ v = none)
    (Δ₀_dom : ∀ v, Δ₀ v ≠ none → v ∈ Λ)
    {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ}
    (den_t : ⟦B.Term.ℤ.abstract «Δ» Δ_fv⟧ᴮ =
      some ⟨T, ⟨α, hT⟩⟩)
    (vars_used : ∀ v ∈ B.Term.ℤ.vars, v ∈ used)
    (Λ_inv : ∀ v ∈ B.Term.ℤ.vars, v ∈ Λ → v ∈ E.context)
    (bv_nodup : (B.bv B.Term.ℤ).Nodup)
    (respects : B.RenamingContext.RespectsTypeContextOnFV
      Δ₀ Λ B.Term.ℤ)
    (fv_in_Λ : ∀ v ∈ B.fv B.Term.ℤ, v ∈ Λ)
    (wf : B.RenWF E.context «Δ»)
    {n : ℕ} :
    ⦃fun (⟨E0, Λ'⟩ : EncoderState) ↦
      ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧
        Λ.keys ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
    encodeTerm B.Term.ℤ E
    ⦃⇓? (⟨t', σ⟩ : SMT.Term × SMTType) ⟨E', Γ'⟩ =>
      ⌜EncodeTermRepPost B.Term.ℤ α Λ «Δ» Δ₀ used T hT
        E t' σ E' Γ'⌝⦄ := by
  mstart
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
  have Δ₀_ext : RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» B.Term.ℤ := by
    intro v d hv
    simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
      B.RenamingContext.restrictToFV,
      B.RenamingContext.restrictToVars, B.fv] at hv
  have canonical_respects :
      B.RenamingContext.RespectsTypeContextOnFV
        (B.RenamingContext.toSMT «Δ») St.types B.Term.ℤ := by
    intro v τ hv
    simp [B.fv] at hv
  mspec (Std.Do.Triple.and _
    (encodeTerm_spec.ℤ_case E typ_t Δ_fv Δ₀_ext
      Δ₀_none_out den_t vars_used Λ_inv bv_nodup
      canonical_respects fv_in_Λ wf)
    (encodeTerm_ℤ_fv_nil E))
  rename_i out
  obtain ⟨t', σ⟩ := out
  mrename_i post
  mintro ∀St'
  mpure post
  obtain ⟨old_post, fv_nil⟩ := post
  obtain ⟨used_sub, types_sub, keys_sub, source_used, σ_eq,
    typ_t', preserves, Δold, hcov_old, _Δold_ext,
    _Δold_source, _Δold_none, denOld, hden_old, old_rel,
    _old_total⟩ := old_post
  have hcov₀ : RenamingContext.CoversFV Δ₀ t' := by
    intro v hv
    rw [fv_nil] at hv
    contradiction
  have hagree₀ : RenamingContext.AgreesOnFV Δ₀ Δold t' := by
    intro v hv
    rw [fv_nil] at hv
    contradiction
  have hden₀ := RenamingContext.denote_congr_of_agreesOnFV
    (h1 := hcov₀) (h2 := hcov_old) hagree₀
  have den_type : denOld.snd.fst = σ := by
    rw [RDom] at old_rel
    exact old_rel.1.trans σ_eq.symm
  mpure_intro
  and_intros
  · exact used_sub
  · exact types_sub
  · exact keys_sub
  · exact source_used
  · rw [σ_eq]
    exact ⟨castPath.reflexive α.toSMTType⟩
  · exact typ_t'
  · simpa [EncodeTermResultShape] using fv_nil
  · exact preserves
  · refine ⟨Δ₀, hcov₀, RenamingContext.extends_refl Δ₀,
      related, ?_, ?_, ?_, ?_, denOld, hden₀.trans hden_old,
      den_type, RDom.toRDomCastAdmissible old_rel, ?_⟩
    · intro v hv
      apply Δ₀_none_out v
      intro hused
      exact hv (used_sub hused)
    · intro v τ hv
      simp [B.fv] at hv
    · intro v τ hv
      rw [fv_nil] at hv
      contradiction
    · exact fun v hv => AList.mem_of_subset types_sub (Δ₀_dom v hv)
    · intro Δ_alt Δ_fv_alt Δ₀_alt related_alt _wf_alt
        Δ₀_alt_none _respects_alt Δ₀_alt_dom
        T_alt hT_alt den_t_alt
      have T_alt_eq : T_alt = T := by
        rw [B.Term.abstract, B.denote, Option.pure_def,
          Option.some_inj] at den_t den_t_alt
        exact (congrArg (fun d => d.fst) den_t_alt).symm.trans
          (congrArg (fun d => d.fst) den_t)
      subst T_alt
      have hcov_alt : RenamingContext.CoversFV Δ₀_alt t' := by
        intro v hv
        rw [fv_nil] at hv
        contradiction
      have hagree_alt : RenamingContext.AgreesOnFV Δ₀_alt Δold t' := by
        intro v hv
        rw [fv_nil] at hv
        contradiction
      have hden_alt := RenamingContext.denote_congr_of_agreesOnFV
        (h1 := hcov_alt) (h2 := hcov_old) hagree_alt
      refine ⟨Δ₀_alt, hcov_alt, denOld,
        RenamingContext.extends_refl Δ₀_alt, related_alt,
        Δ₀_alt_none, ?_, ?_, ?_, hden_alt.trans hden_old,
        den_type, ?_⟩
      · intro v τ hv
        simp [B.fv] at hv
      · intro v τ hv
        rw [fv_nil] at hv
        contradiction
      · exact fun v hv =>
          AList.mem_of_subset types_sub (Δ₀_alt_dom v hv)
      · simpa only [proof_irrel_heq] using
          RDom.toRDomCastAdmissible old_rel

set_option maxHeartbeats 1200000 in
theorem encodeTerm_rep_spec.𝔹_case.{u}
    (E : B.Env) {Λ : SMT.TypeContext} {α : BType}
    (typ_t : E.context ⊢ᴮ B.Term.𝔹 : α)
    {«Δ» : B.RenamingContext.Context}
    (Δ_fv : ∀ v ∈ B.fv B.Term.𝔹, («Δ» v).isSome = true)
    {Δ₀ : SMT.RenamingContext.Context.{u}}
    (related : RValuationCastAdmissibleOnFV «Δ» Δ₀ B.Term.𝔹)
    {used : List SMT.𝒱}
    (Δ₀_none_out : ∀ v ∉ used, Δ₀ v = none)
    (Δ₀_dom : ∀ v, Δ₀ v ≠ none → v ∈ Λ)
    {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ}
    (den_t : ⟦B.Term.𝔹.abstract «Δ» Δ_fv⟧ᴮ =
      some ⟨T, ⟨α, hT⟩⟩)
    (vars_used : ∀ v ∈ B.Term.𝔹.vars, v ∈ used)
    (Λ_inv : ∀ v ∈ B.Term.𝔹.vars, v ∈ Λ → v ∈ E.context)
    (bv_nodup : (B.bv B.Term.𝔹).Nodup)
    (respects : B.RenamingContext.RespectsTypeContextOnFV
      Δ₀ Λ B.Term.𝔹)
    (fv_in_Λ : ∀ v ∈ B.fv B.Term.𝔹, v ∈ Λ)
    (wf : B.RenWF E.context «Δ»)
    {n : ℕ} :
    ⦃fun (⟨E0, Λ'⟩ : EncoderState) ↦
      ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧
        Λ.keys ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
    encodeTerm B.Term.𝔹 E
    ⦃⇓? (⟨t', σ⟩ : SMT.Term × SMTType) ⟨E', Γ'⟩ =>
      ⌜EncodeTermRepPost B.Term.𝔹 α Λ «Δ» Δ₀ used T hT
        E t' σ E' Γ'⌝⦄ := by
  mstart
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
  have Δ₀_ext : RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» B.Term.𝔹 := by
    intro v d hv
    simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
      B.RenamingContext.restrictToFV,
      B.RenamingContext.restrictToVars, B.fv] at hv
  have canonical_respects :
      B.RenamingContext.RespectsTypeContextOnFV
        (B.RenamingContext.toSMT «Δ») St.types B.Term.𝔹 := by
    intro v τ hv
    simp [B.fv] at hv
  mspec (Std.Do.Triple.and _
    (encodeTerm_spec.𝔹_case E typ_t Δ_fv Δ₀_ext
      Δ₀_none_out den_t vars_used Λ_inv bv_nodup
      canonical_respects fv_in_Λ wf)
    (encodeTerm_𝔹_fv_nil E))
  rename_i out
  obtain ⟨t', σ⟩ := out
  mrename_i post
  mintro ∀St'
  mpure post
  obtain ⟨old_post, fv_nil⟩ := post
  obtain ⟨used_sub, types_sub, keys_sub, source_used, σ_eq,
    typ_t', preserves, Δold, hcov_old, _Δold_ext,
    _Δold_source, _Δold_none, denOld, hden_old, old_rel,
    _old_total⟩ := old_post
  have hcov₀ : RenamingContext.CoversFV Δ₀ t' := by
    intro v hv
    rw [fv_nil] at hv
    contradiction
  have hagree₀ : RenamingContext.AgreesOnFV Δ₀ Δold t' := by
    intro v hv
    rw [fv_nil] at hv
    contradiction
  have hden₀ := RenamingContext.denote_congr_of_agreesOnFV
    (h1 := hcov₀) (h2 := hcov_old) hagree₀
  have den_type : denOld.snd.fst = σ := by
    rw [RDom] at old_rel
    exact old_rel.1.trans σ_eq.symm
  mpure_intro
  and_intros
  · exact used_sub
  · exact types_sub
  · exact keys_sub
  · exact source_used
  · rw [σ_eq]
    exact ⟨castPath.reflexive α.toSMTType⟩
  · exact typ_t'
  · simpa [EncodeTermResultShape] using fv_nil
  · exact preserves
  · refine ⟨Δ₀, hcov₀, RenamingContext.extends_refl Δ₀,
      related, ?_, ?_, ?_, ?_, denOld, hden₀.trans hden_old,
      den_type, RDom.toRDomCastAdmissible old_rel, ?_⟩
    · intro v hv
      apply Δ₀_none_out v
      intro hused
      exact hv (used_sub hused)
    · intro v τ hv
      simp [B.fv] at hv
    · intro v τ hv
      rw [fv_nil] at hv
      contradiction
    · exact fun v hv => AList.mem_of_subset types_sub (Δ₀_dom v hv)
    · intro Δ_alt Δ_fv_alt Δ₀_alt related_alt _wf_alt
        Δ₀_alt_none _respects_alt Δ₀_alt_dom
        T_alt hT_alt den_t_alt
      have T_alt_eq : T_alt = T := by
        rw [B.Term.abstract, B.denote, Option.pure_def,
          Option.some_inj] at den_t den_t_alt
        exact (congrArg (fun d => d.fst) den_t_alt).symm.trans
          (congrArg (fun d => d.fst) den_t)
      subst T_alt
      have hcov_alt : RenamingContext.CoversFV Δ₀_alt t' := by
        intro v hv
        rw [fv_nil] at hv
        contradiction
      have hagree_alt : RenamingContext.AgreesOnFV Δ₀_alt Δold t' := by
        intro v hv
        rw [fv_nil] at hv
        contradiction
      have hden_alt := RenamingContext.denote_congr_of_agreesOnFV
        (h1 := hcov_alt) (h2 := hcov_old) hagree_alt
      refine ⟨Δ₀_alt, hcov_alt, denOld,
        RenamingContext.extends_refl Δ₀_alt, related_alt,
        Δ₀_alt_none, ?_, ?_, ?_, hden_alt.trans hden_old,
        den_type, ?_⟩
      · intro v τ hv
        simp [B.fv] at hv
      · intro v τ hv
        rw [fv_nil] at hv
        contradiction
      · exact fun v hv =>
          AList.mem_of_subset types_sub (Δ₀_alt_dom v hv)
      · simpa only [proof_irrel_heq] using
          RDom.toRDomCastAdmissible old_rel
