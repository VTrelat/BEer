import SMT.Reasoning.Basic.EncodeTermRepresentedMem

open Std.Do B SMT ZFSet Classical

/-! # Generated-helper contract for represented membership -/

set_option maxHeartbeats 6000000 in
theorem encodeTerm_rep_scoped.mem_case.{u}
    (x S : B.Term)
    (x_ih : EncodeTermRepIH.{u} x)
    (S_ih : EncodeTermRepIH.{u} S)
    (x_scoped : EncodeTermRepScopedIH.{u} x)
    (S_scoped : EncodeTermRepScopedIH.{u} S)
    (E : B.Env) {Λ : SMT.TypeContext}
    (typ_t : E.context ⊢ᴮ x ∈ᴮ S : BType.bool)
    {«Δ» : B.RenamingContext.Context}
    (Δ_fv : ∀ v ∈ B.fv (x ∈ᴮ S), («Δ» v).isSome = true)
    {Δ₀ : SMT.RenamingContext.Context.{u}}
    (related : RValuationCastSupportedOnFV «Δ» Δ₀ (x ∈ᴮ S))
    {used : List SMT.𝒱}
    (Δ₀_none_out : ∀ v ∉ used, Δ₀ v = none)
    (Δ₀_dom : ∀ v, Δ₀ v ≠ none → v ∈ Λ)
    {T : ZFSet.{u}} {hT : T ∈ ⟦BType.bool⟧ᶻ}
    (den_t : ⟦(x ∈ᴮ S).abstract «Δ» Δ_fv⟧ᴮ =
      some ⟨T, BType.bool, hT⟩)
    (vars_used : ∀ v ∈ (x ∈ᴮ S).vars, v ∈ used)
    (Λ_inv : ∀ v ∈ (x ∈ᴮ S).vars,
      v ∈ Λ → v ∈ E.context)
    (bv_nodup : (B.bv (x ∈ᴮ S)).Nodup)
    (respects : B.RenamingContext.RespectsTypeContextOnFV
      Δ₀ Λ (x ∈ᴮ S))
    (fv_in_Λ : ∀ v ∈ B.fv (x ∈ᴮ S), v ∈ Λ)
    (wf : B.RenWF E.context «Δ»)
    {n : ℕ} {decl : SMT.Chunk} :
    ⦃fun ⟨E₀, Λ'⟩ ↦
      ⌜Λ' = Λ ∧ E₀.freshvarsc = n ∧
        Λ.keys ⊆ E₀.usedVars ∧ E₀.usedVars = used ∧
        E₀.declarations = decl⌝⦄
    encodeTerm (x ∈ᴮ S) E
    ⦃⇓? (⟨t', σ⟩ : SMT.Term × SMTType) ⟨E', Γ'⟩ =>
      ⌜EncodeTermRepScopedPost.{u} (x ∈ᴮ S) E BType.bool Λ decl
        t' σ E' Γ'⌝⦄ := by
  mstart
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_sub, St_used_eq, St_decl_eq⟩ := pre
  obtain ⟨_, a, typ_x, typ_S⟩ := B.Typing.memE typ_t
  obtain ⟨X, hX, A, hA, den_x, den_S, T_eq⟩ :=
    B.denote_mem_inv typ_x typ_S Δ_fv wf den_t
  subst T
  rw [encodeTerm]

  have fv_x_sub : B.fv x ⊆ B.fv (x ∈ᴮ S) := by
    intro v hv
    rw [B.fv, List.mem_append]
    exact Or.inl hv
  have fv_S_sub : B.fv S ⊆ B.fv (x ∈ᴮ S) := by
    intro v hv
    rw [B.fv, List.mem_append]
    exact Or.inr hv
  have hx_bv_nodup : (B.bv x).Nodup := by
    have h := bv_nodup
    rw [B.bv, List.nodup_append] at h
    exact h.1
  have hS_bv_nodup : (B.bv S).Nodup := by
    have h := bv_nodup
    rw [B.bv, List.nodup_append] at h
    exact h.2.1
  have hxS_bv_disj : ∀ p ∈ B.bv x, ∀ q ∈ B.bv S, p ≠ q := by
    have h := bv_nodup
    rw [B.bv, List.nodup_append] at h
    exact h.2.2

  mspec (Std.Do.Triple.and _
    (Std.Do.Triple.and _
      (Std.Do.Triple.and _
        (x_ih E typ_x
          (fun v hv => Δ_fv v (fv_x_sub hv))
          (related.mono_fv fv_x_sub)
          Δ₀_none_out Δ₀_dom den_x
          (fun v hv => vars_used v (by
            simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
              List.mem_append] at hv ⊢
            rcases hv with h | h <;> [left; right] <;> exact Or.inl h))
          (fun v hv => Λ_inv v (by
            simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
              List.mem_append] at hv ⊢
            rcases hv with h | h <;> [left; right] <;> exact Or.inl h))
          hx_bv_nodup (respects.mono_fv fv_x_sub)
          (fun v hv => fv_in_Λ v (fv_x_sub hv)) wf
          (n := St.env.freshvarsc))
        (x_scoped E typ_x
          (fun v hv => Δ_fv v (fv_x_sub hv))
          (related.mono_fv fv_x_sub)
          Δ₀_none_out Δ₀_dom den_x
          (fun v hv => vars_used v (by
            simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
              List.mem_append] at hv ⊢
            rcases hv with h | h <;> [left; right] <;> exact Or.inl h))
          (fun v hv => Λ_inv v (by
            simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
              List.mem_append] at hv ⊢
            rcases hv with h | h <;> [left; right] <;> exact Or.inl h))
          hx_bv_nodup (respects.mono_fv fv_x_sub)
          (fun v hv => fv_in_Λ v (fv_x_sub hv)) wf
          (n := St.env.freshvarsc) (decl := decl)))
      (encodeTerm_bv_used E (t := x) (used := St.env.usedVars)
        (n := St.env.freshvarsc) (decl := St.env.declarations)))
    (encodeTerm_bv_notMem_used E (t := x) (used := St.env.usedVars)
      (n := St.env.freshvarsc) (decl := St.env.declarations)))
  clear x_ih x_scoped
  rename_i out_x
  obtain ⟨x_enc, sx⟩ := out_x
  mrename_i pre
  mintro ∀Stx
  mpure pre
  dsimp at pre
  obtain ⟨⟨⟨x_post, ⟨Dltx, x_decl_eq, x_sc_total, x_guard⟩⟩,
      bv_x_used, _⟩, bv_x_not_used, _⟩ := pre
  obtain ⟨used_sub_x, types_sub_x, keys_sub_x, x_used,
      _path_x, typ_x_enc, _shape_x, x_preserves,
      Δx, hcov_x, Δx_ext, _related_x, Δx_none, _respects_x,
      target_respects_x, Δx_dom,
      denX, hden_x, hdenX_type, X_rel, x_total⟩ := x_post
  rcases denX with ⟨Xenc, sxD, hXenc⟩
  dsimp at hdenX_type
  subst sxD

  have related_S : RValuationCastSupportedOnFV «Δ» Δx S :=
    (related.mono_fv fv_S_sub).of_extends Δx_ext
  have respects_S : B.RenamingContext.RespectsTypeContextOnFV
      Δx Stx.types S :=
    respects.of_extends Δx_ext types_sub_x fv_S_sub fv_in_Λ

  mspec (Std.Do.Triple.and _
    (Std.Do.Triple.and _
      (S_ih E typ_S
        (fun v hv => Δ_fv v (fv_S_sub hv)) related_S
        Δx_none Δx_dom den_S
        (fun v hv => used_sub_x (vars_used v (by
          simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
            List.mem_append] at hv ⊢
          rcases hv with h | h <;> [left; right] <;> exact Or.inr h)))
        (fun v hv hΓ => by
          have hv_parent : v ∈ (x ∈ᴮ S).vars := by
            simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
              List.mem_append] at hv ⊢
            rcases hv with h | h <;> [left; right] <;> exact Or.inr h
          by_cases hv_Λ : v ∈ St.types
          · exact Λ_inv v hv_parent hv_Λ
          · have hv_vars_x : v ∈ B.Term.vars x := by
              by_contra hnot
              exact absurd hΓ
                (x_preserves v (vars_used v hv_parent) hv_Λ hnot)
            rcases B.Term.mem_vars_iff.mp hv_vars_x with hx_fv | hx_bv
            · exact B.Typing.typed_by_fv typ_x hx_fv
            · rcases B.Term.mem_vars_iff.mp hv with hS_fv | hS_bv
              · exact absurd (B.Typing.typed_by_fv typ_S hS_fv)
                  (B.Typing.bv_notMem_context typ_x v hx_bv)
              · exact absurd rfl (hxS_bv_disj v hx_bv v hS_bv))
        hS_bv_nodup respects_S
        (fun v hv => AList.mem_of_subset types_sub_x
          (fv_in_Λ v (fv_S_sub hv))) wf
        (n := Stx.env.freshvarsc))
      (S_scoped E typ_S
        (fun v hv => Δ_fv v (fv_S_sub hv)) related_S
        Δx_none Δx_dom den_S
        (fun v hv => used_sub_x (vars_used v (by
          simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
            List.mem_append] at hv ⊢
          rcases hv with h | h <;> [left; right] <;> exact Or.inr h)))
        (fun v hv hΓ => by
          have hv_parent : v ∈ (x ∈ᴮ S).vars := by
            simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
              List.mem_append] at hv ⊢
            rcases hv with h | h <;> [left; right] <;> exact Or.inr h
          by_cases hv_Λ : v ∈ St.types
          · exact Λ_inv v hv_parent hv_Λ
          · have hv_vars_x : v ∈ B.Term.vars x := by
              by_contra hnot
              exact absurd hΓ
                (x_preserves v (vars_used v hv_parent) hv_Λ hnot)
            rcases B.Term.mem_vars_iff.mp hv_vars_x with hx_fv | hx_bv
            · exact B.Typing.typed_by_fv typ_x hx_fv
            · rcases B.Term.mem_vars_iff.mp hv with hS_fv | hS_bv
              · exact absurd (B.Typing.typed_by_fv typ_S hS_fv)
                  (B.Typing.bv_notMem_context typ_x v hx_bv)
              · exact absurd rfl (hxS_bv_disj v hx_bv v hS_bv))
        hS_bv_nodup respects_S
        (fun v hv => AList.mem_of_subset types_sub_x
          (fv_in_Λ v (fv_S_sub hv))) wf
        (n := Stx.env.freshvarsc) (decl := decl ++ Dltx)))
    (encodeTerm_bv_used E (t := S) (used := Stx.env.usedVars)
      (n := Stx.env.freshvarsc) (decl := Stx.env.declarations)))
  clear S_ih S_scoped
  rename_i out_S
  obtain ⟨S_enc, sS⟩ := out_S
  mrename_i pre
  mintro ∀StS
  mpure pre
  dsimp at pre
  obtain ⟨⟨S_post, ⟨DltS, S_decl_eq, S_sc_total, S_guard⟩⟩,
      bv_S_used, _⟩ := pre
  obtain ⟨used_sub_S, types_sub_S, keys_sub_S, S_used,
      _path_S, typ_S_enc, _shape_S, S_preserves,
      ΔS, hcov_S, ΔS_ext, _related_S, ΔS_none, _respects_S,
      target_respects_S, ΔS_dom,
      denA, hden_S, hdenA_type, A_rel, S_total⟩ := S_post
  rcases denA with ⟨Aenc, sSD, hAenc⟩
  dsimp at hdenA_type
  subst sSD

  have bv_x_not_final : ∀ v ∈ SMT.bv x_enc, v ∉ StS.types :=
    fun v hv => S_preserves v (bv_x_used v hv)
      (SMT.Typing.bv_notMem_context typ_x_enc v hv)
      (by
        rw [B.Term.notMem_vars_iff]
        refine ⟨?_, ?_⟩
        · intro hfv
          exact SMT.Typing.bv_notMem_context typ_x_enc v hv
            (AList.mem_of_subset types_sub_x
              (fv_in_Λ v (fv_S_sub hfv)))
        · intro hbS
          exact bv_x_not_used v hv
            (St_used_eq ▸ vars_used v (by
              apply B.Term.mem_vars_iff.mpr
              right
              rw [B.bv, List.mem_append]
              exact Or.inr hbS)))
  have typ_x_final : StS.types ⊢ˢ x_enc : sx :=
    SMT.Typing.weakening types_sub_S typ_x_enc bv_x_not_final
  have hcov_x_final : SMT.RenamingContext.CoversFV ΔS x_enc :=
    SMT.RenamingContext.coversFV_of_extends_of_coversFV ΔS_ext hcov_x
  have hden_x_final : ⟦x_enc.abstract ΔS hcov_x_final⟧ˢ =
      some (⟨Xenc, sx, hXenc⟩ : SMT.Dom) := by
    have hagree :=
      SMT.RenamingContext.agreesOnFV_of_extends_of_coversFV ΔS_ext hcov_x
    exact (SMT.RenamingContext.denote_congr_of_agreesOnFV
      (t := x_enc) (h1 := hcov_x_final) (h2 := hcov_x) hagree).trans
      hden_x
  have target_respects_x_final :
      SMT.RenamingContext.RespectsTypeContextOnFV ΔS StS.types x_enc :=
    target_respects_x.of_extends ΔS_ext types_sub_S typ_x_enc

  mspec castMembership_supported_rep_contract a x_enc S_enc sx sS
    X_rel.supported A_rel.supported typ_x_final typ_S_enc
    (fun v hv => used_sub_S (bv_x_used v hv)) bv_S_used
  rename_i out_mem
  obtain ⟨mem_enc, smem⟩ := out_mem
  mrename_i pre
  mintro ∀StM
  mpure pre
  obtain ⟨used_sub_M, types_sub_M, keys_sub_M, smem_eq,
    typ_mem, fv_x_mem, fv_S_mem, mem_preserves,
    DltM, mem_decl_eq, mem_sem⟩ := pre
  change smem = SMTType.bool at smem_eq
  subst smem
  mpure_intro
  refine ⟨(Dltx ++ DltS) ++ DltM, ?_, ?_, ?_⟩
  · rw [mem_decl_eq, S_decl_eq]
    simp only [List.append_assoc]
  · intro Δ_alt Δ_fv_alt Δ₀_alt related_alt wf_alt
      Δ₀_alt_none respects_alt Δ₀_alt_dom
      T_alt hT_alt den_t_alt
    obtain ⟨X_alt, hX_alt, A_alt, hA_alt,
        den_x_alt, den_S_alt, T_alt_eq⟩ :=
      B.denote_mem_inv typ_x typ_S Δ_fv_alt wf_alt den_t_alt
    subst T_alt
    have Δ₀_alt_none_x : ∀ v ∉ Stx.env.usedVars,
        Δ₀_alt v = none := by
      intro v hv
      by_contra hne
      have hv_Λ := Δ₀_alt_dom v hne
      have hv_used : v ∈ used := by
        simpa [← St_used_eq] using St_sub hv_Λ
      exact hv (used_sub_x hv_used)
    obtain ⟨Δx_alt, hcov_x_alt, denX_alt, Δx_alt_ext,
        _related_x_alt, Δx_alt_none, _respects_x_alt,
        target_respects_x_alt, Δx_alt_dom, specs_x_alt,
        hden_x_alt, hdenX_alt_type, X_alt_rel⟩ :=
      x_sc_total Δ_alt
        (fun v hv => Δ_fv_alt v (fv_x_sub hv)) Δ₀_alt
        (related_alt.mono_fv fv_x_sub) wf_alt Δ₀_alt_none_x
        (respects_alt.mono_fv fv_x_sub) Δ₀_alt_dom
        X_alt hX_alt den_x_alt
    rcases denX_alt with ⟨Xenc_alt, sx_alt, hXenc_alt⟩
    dsimp at hdenX_alt_type
    subst sx_alt
    have Δx_alt_none_S : ∀ v ∉ StS.env.usedVars,
        Δx_alt v = none := by
      intro v hv
      apply Δx_alt_none v
      intro hvx
      exact hv (used_sub_S hvx)
    have related_alt_S : RValuationCastSupportedOnFV Δ_alt Δx_alt S :=
      (related_alt.mono_fv fv_S_sub).of_extends Δx_alt_ext
    have respects_alt_S :
        B.RenamingContext.RespectsTypeContextOnFV
          Δx_alt Stx.types S :=
      respects_alt.of_extends Δx_alt_ext types_sub_x
        fv_S_sub fv_in_Λ
    obtain ⟨ΔS_alt, hcov_S_alt, denA_alt, ΔS_alt_ext,
        _related_S_alt, ΔS_alt_none, _respects_S_alt,
        target_respects_S_alt, ΔS_alt_dom, specs_S_alt,
        hden_S_alt, hdenA_alt_type, A_alt_rel⟩ :=
      S_sc_total Δ_alt
        (fun v hv => Δ_fv_alt v (fv_S_sub hv)) Δx_alt
        related_alt_S wf_alt Δx_alt_none_S respects_alt_S
        Δx_alt_dom A_alt hA_alt den_S_alt
    rcases denA_alt with ⟨Aenc_alt, sS_alt, hAenc_alt⟩
    dsimp at hdenA_alt_type
    subst sS_alt
    have hcov_x_alt_final : SMT.RenamingContext.CoversFV ΔS_alt x_enc :=
      SMT.RenamingContext.coversFV_of_extends_of_coversFV
        ΔS_alt_ext hcov_x_alt
    have hden_x_alt_final : ⟦x_enc.abstract ΔS_alt
        hcov_x_alt_final⟧ˢ =
        some (⟨Xenc_alt, sx, hXenc_alt⟩ : SMT.Dom) := by
      have hagree :=
        SMT.RenamingContext.agreesOnFV_of_extends_of_coversFV
          ΔS_alt_ext hcov_x_alt
      exact (SMT.RenamingContext.denote_congr_of_agreesOnFV
        (t := x_enc) (h1 := hcov_x_alt_final)
        (h2 := hcov_x_alt) hagree).trans hden_x_alt
    have target_respects_x_alt_final :
        SMT.RenamingContext.RespectsTypeContextOnFV
          ΔS_alt StS.types x_enc :=
      target_respects_x_alt.of_extends
        ΔS_alt_ext types_sub_S typ_x_enc
    have target_respects_x_alt_M :
        SMT.RenamingContext.RespectsTypeContextOnFV
          ΔS_alt StM.types x_enc :=
      target_respects_x_alt_final.of_extends
        (SMT.RenamingContext.extends_refl ΔS_alt)
        types_sub_M typ_x_final
    have target_respects_S_alt_M :
        SMT.RenamingContext.RespectsTypeContextOnFV
          ΔS_alt StM.types S_enc :=
      target_respects_S_alt.of_extends
        (SMT.RenamingContext.extends_refl ΔS_alt)
        types_sub_M typ_S_enc
    have ΔS_alt_dom_M : ∀ v, ΔS_alt v ≠ none → v ∈ StM.types :=
      fun v hv => AList.mem_of_subset types_sub_M (ΔS_alt_dom v hv)
    obtain ⟨good_alt, _guarded_alt⟩ := mem_sem StM.types
      (fun _ h => h) ΔS_alt hcov_x_alt_final hcov_S_alt
      ΔS_alt_none target_respects_x_alt_M target_respects_S_alt_M
      ΔS_alt_dom_M X_alt A_alt hX_alt hA_alt
      (⟨Xenc_alt, sx, hXenc_alt⟩ : SMT.Dom)
      (⟨Aenc_alt, sS, hAenc_alt⟩ : SMT.Dom)
      hden_x_alt_final hden_S_alt rfl rfl
      X_alt_rel.toRDomCast A_alt_rel.toRDomCast
    obtain ⟨ΔM_alt, hcov_M_alt, denM_alt, ΔM_alt_ext,
        ΔM_alt_none, target_respects_M_alt, ΔM_alt_dom,
        specs_M_alt, hden_M_alt, hdenM_alt_type, hmem_alt_iff⟩ :=
      good_alt
    have hsource_alt_true :
        (X_alt ∈ᶻ A_alt) = ZFSet.zftrue ↔ X_alt ∈ A_alt := by
      by_cases hXA : X_alt ∈ A_alt
      · simp [overloadUnaryOp, hXA]
      · simpa [overloadUnaryOp, hXA] using
          (Ne.symm ZFSet.zftrue_ne_zffalse)
    have result_alt_rel : RDomCastSupported
        (⟨X_alt ∈ᶻ A_alt, BType.bool,
          overloadUnaryOp_mem⟩ : B.Dom) denM_alt := by
      rcases denM_alt with ⟨Mv, Ms, hMv⟩
      dsimp at hdenM_alt_type
      subst Ms
      exact RDomCastSupported.bool_of_true_iff
        (hsource_alt_true.trans hmem_alt_iff.symm)
    have ΔS_alt_ext₀ :=
      SMT.RenamingContext.extends_trans ΔS_alt_ext Δx_alt_ext
    have ΔM_alt_ext₀ :=
      SMT.RenamingContext.extends_trans ΔM_alt_ext ΔS_alt_ext₀
    have specs_x_at_S : SpecBodiesTrue ΔS_alt StS.types Dltx :=
      specs_x_alt.of_extends ΔS_alt_ext types_sub_S Δx_alt_dom
    have specs_children_at_S :
        SpecBodiesTrue ΔS_alt StS.types (Dltx ++ DltS) :=
      specs_x_at_S.append specs_S_alt
    have specs_children_at_M :
        SpecBodiesTrue ΔM_alt StM.types (Dltx ++ DltS) :=
      specs_children_at_S.of_extends
        ΔM_alt_ext types_sub_M ΔS_alt_dom
    refine ⟨ΔM_alt, hcov_M_alt, denM_alt, ΔM_alt_ext₀,
      related_alt.of_extends ΔM_alt_ext₀, ΔM_alt_none, ?_,
      target_respects_M_alt, ΔM_alt_dom,
      specs_children_at_M.append specs_M_alt,
      hden_M_alt, hdenM_alt_type, result_alt_rel⟩
    exact respects_alt.of_extends ΔM_alt_ext₀
      (fun _ h => types_sub_M (types_sub_S (types_sub_x h)))
      (fun _ h => h) fv_in_Λ
  · intro Γ_sup Γ_sub Δ_alt Δ_fv_alt Θ related_alt wf_alt
      respects_B respects_SMT specs_true T_alt hT_alt den_t_alt
      hcov_mem denOut hdenOut hdenOut_type
    obtain ⟨X_alt, hX_alt, A_alt, hA_alt,
        den_x_alt, den_S_alt, T_alt_eq⟩ :=
      B.denote_mem_inv typ_x typ_S Δ_fv_alt wf_alt den_t_alt
    subst T_alt
    have hcov_x_target : SMT.RenamingContext.CoversFV Θ x_enc := by
      intro v hv
      exact hcov_mem v (fv_x_mem hv)
    have hcov_S_target : SMT.RenamingContext.CoversFV Θ S_enc := by
      intro v hv
      exact hcov_mem v (fv_S_mem hv)
    have target_respects_x_sup :
        SMT.RenamingContext.RespectsTypeContextOnFV Θ Γ_sup x_enc :=
      respects_SMT.mono_fv fv_x_mem
    have target_respects_S_sup :
        SMT.RenamingContext.RespectsTypeContextOnFV Θ Γ_sup S_enc :=
      respects_SMT.mono_fv fv_S_mem
    have specs_children :
        SpecBodiesTrue Θ Γ_sup (Dltx ++ DltS) :=
      specs_true.left_of_append
    have specs_x : SpecBodiesTrue Θ Γ_sup Dltx :=
      specs_children.left_of_append
    have specs_S : SpecBodiesTrue Θ Γ_sup DltS :=
      specs_children.right_of_append
    have specs_M : SpecBodiesTrue Θ Γ_sup DltM :=
      specs_true.right_of_append
    have typ_x_M : StM.types ⊢ˢ x_enc : sx :=
      SMT.Typing.weakening types_sub_M typ_x_final (by
        intro v hv
        exact mem_preserves v (used_sub_S (bv_x_used v hv))
          (SMT.Typing.bv_notMem_context typ_x_final v hv))
    have typ_S_M : StM.types ⊢ˢ S_enc : sS :=
      SMT.Typing.weakening types_sub_M typ_S_enc (by
        intro v hv
        exact mem_preserves v (bv_S_used v hv)
          (SMT.Typing.bv_notMem_context typ_S_enc v hv))
    have target_respects_x_M :
        SMT.RenamingContext.RespectsTypeContextOnFV Θ StM.types x_enc :=
      target_respects_x_sup.of_super Γ_sub
    have target_respects_S_M :
        SMT.RenamingContext.RespectsTypeContextOnFV Θ StM.types S_enc :=
      target_respects_S_sup.of_super Γ_sub
    obtain ⟨denX_target, hdenX_target, hdenX_target_type⟩ :=
      SMT.RenamingContext.denote_exists_of_typing_fv
        typ_x_M target_respects_x_M hcov_x_target
    obtain ⟨denA_target, hdenA_target, hdenA_target_type⟩ :=
      SMT.RenamingContext.denote_exists_of_typing_fv
        typ_S_M target_respects_S_M hcov_S_target
    have StS_sub_sup : StS.types ⊆ Γ_sup :=
      AList.subset_trans types_sub_M Γ_sub
    have Stx_sub_sup : Stx.types ⊆ Γ_sup :=
      AList.subset_trans types_sub_S StS_sub_sup
    have X_rel_target := x_guard Γ_sup Stx_sub_sup Δ_alt
      (fun v hv => Δ_fv_alt v (fv_x_sub hv)) Θ
      (related_alt.mono_fv fv_x_sub) wf_alt
      (respects_B.mono_fv fv_x_sub) target_respects_x_sup
      specs_x X_alt hX_alt den_x_alt
      hcov_x_target denX_target hdenX_target hdenX_target_type
    have A_rel_target := S_guard Γ_sup StS_sub_sup Δ_alt
      (fun v hv => Δ_fv_alt v (fv_S_sub hv)) Θ
      (related_alt.mono_fv fv_S_sub) wf_alt
      (respects_B.mono_fv fv_S_sub) target_respects_S_sup
      specs_S A_alt hA_alt den_S_alt
      hcov_S_target denA_target hdenA_target hdenA_target_type
    have target_respects_x_base_M :
        SMT.RenamingContext.RespectsTypeContextOnFV
          ΔS StM.types x_enc :=
      target_respects_x_final.of_extends
        (SMT.RenamingContext.extends_refl ΔS)
        types_sub_M typ_x_final
    have target_respects_S_base_M :
        SMT.RenamingContext.RespectsTypeContextOnFV
          ΔS StM.types S_enc :=
      target_respects_S.of_extends
        (SMT.RenamingContext.extends_refl ΔS)
        types_sub_M typ_S_enc
    have ΔS_dom_M : ∀ v, ΔS v ≠ none → v ∈ StM.types :=
      fun v hv => AList.mem_of_subset types_sub_M (ΔS_dom v hv)
    obtain ⟨_good_base, mem_guard⟩ := mem_sem StM.types
      (fun _ h => h) ΔS hcov_x_final hcov_S ΔS_none
      target_respects_x_base_M target_respects_S_base_M ΔS_dom_M
      X A hX hA
      (⟨Xenc, sx, hXenc⟩ : SMT.Dom)
      (⟨Aenc, sS, hAenc⟩ : SMT.Dom)
      hden_x_final hden_S rfl rfl
      X_rel.toRDomCast A_rel.toRDomCast
    have hmem_iff := mem_guard Γ_sup Γ_sub Θ
      hcov_x_target hcov_S_target
      target_respects_x_sup target_respects_S_sup
      X_alt A_alt hX_alt hA_alt denX_target denA_target
      hdenX_target hdenA_target hdenX_target_type hdenA_target_type
      X_rel_target.toRDomCast A_rel_target.toRDomCast
      hcov_mem denOut respects_SMT specs_M hdenOut hdenOut_type
    have hsource_alt_true :
        (X_alt ∈ᶻ A_alt) = ZFSet.zftrue ↔ X_alt ∈ A_alt := by
      by_cases hXA : X_alt ∈ A_alt
      · simp [overloadUnaryOp, hXA]
      · simpa [overloadUnaryOp, hXA] using
          (Ne.symm ZFSet.zftrue_ne_zffalse)
    rcases denOut with ⟨Mv, Ms, hMv⟩
    dsimp at hdenOut_type
    subst Ms
    exact RDomCastSupported.bool_of_true_iff
      (hsource_alt_true.trans hmem_iff.symm)
