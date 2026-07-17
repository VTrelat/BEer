import SMT.Reasoning.Basic.EncodeTermRepresentedEq

open Std.Do B SMT ZFSet Classical

/-! # Generated-helper contract for represented equality -/

set_option maxHeartbeats 6000000 in
theorem encodeTerm_rep_scoped.eq_case.{u}
    (x S : B.Term)
    (x_ih : EncodeTermRepIH.{u} x)
    (S_ih : EncodeTermRepIH.{u} S)
    (x_scoped : EncodeTermRepScopedIH.{u} x)
    (S_scoped : EncodeTermRepScopedIH.{u} S)
    (E : B.Env) {Λ : SMT.TypeContext}
    (typ_t : E.context ⊢ᴮ x =ᴮ S : BType.bool)
    {«Δ» : B.RenamingContext.Context}
    (Δ_fv : ∀ v ∈ B.fv (x =ᴮ S), («Δ» v).isSome = true)
    {Δ₀ : SMT.RenamingContext.Context.{u}}
    (related : RValuationCastSupportedOnFV «Δ» Δ₀ (x =ᴮ S))
    {used : List SMT.𝒱}
    (Δ₀_none_out : ∀ v ∉ used, Δ₀ v = none)
    (Δ₀_dom : ∀ v, Δ₀ v ≠ none → v ∈ Λ)
    {T : ZFSet.{u}} {hT : T ∈ ⟦BType.bool⟧ᶻ}
    (den_t : ⟦(x =ᴮ S).abstract «Δ» Δ_fv⟧ᴮ =
      some ⟨T, BType.bool, hT⟩)
    (vars_used : ∀ v ∈ (x =ᴮ S).vars, v ∈ used)
    (Λ_inv : ∀ v ∈ (x =ᴮ S).vars,
      v ∈ Λ → v ∈ E.context)
    (bv_nodup : (B.bv (x =ᴮ S)).Nodup)
    (respects : B.RenamingContext.RespectsTypeContextOnFV
      Δ₀ Λ (x =ᴮ S))
    (fv_in_Λ : ∀ v ∈ B.fv (x =ᴮ S), v ∈ Λ)
    (wf : B.RenWF E.context «Δ»)
    {n : ℕ} {decl : SMT.Chunk} :
    ⦃fun ⟨E₀, Λ'⟩ ↦
      ⌜Λ' = Λ ∧ E₀.freshvarsc = n ∧
        Λ.keys ⊆ E₀.usedVars ∧ E₀.usedVars = used ∧
        E₀.declarations = decl⌝⦄
    encodeTerm (x =ᴮ S) E
    ⦃⇓? (⟨t', σ⟩ : SMT.Term × SMTType) ⟨E', Γ'⟩ =>
      ⌜EncodeTermRepScopedPost.{u} (x =ᴮ S) E BType.bool Λ decl
        t' σ E' Γ'⌝⦄ := by
  mstart
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_sub, St_used_eq, St_decl_eq⟩ := pre
  obtain ⟨_, a, typ_x, typ_S⟩ := B.Typing.eqE typ_t
  obtain ⟨X, Y, hX, hY, den_x, den_S, hTiff⟩ :=
    denote_eq_inv_rep typ_x typ_S Δ_fv wf den_t
  rw [encodeTerm]

  have fv_x_sub : B.fv x ⊆ B.fv (x =ᴮ S) := by
    intro v hv
    rw [B.fv, List.mem_append]
    exact Or.inl hv
  have fv_S_sub : B.fv S ⊆ B.fv (x =ᴮ S) := by
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
  obtain ⟨⟨⟨x_post, ⟨Dltx, x_decl_eq, x_ctx, x_trace, x_sc_total, x_guard,
      x_specs_op, x_sc_typing⟩⟩,
      bv_x_used, _x_used_sub_struct, Dltx_struct,
        x_decl_struct, x_delta_ok⟩,
      bv_x_not_used, _⟩ := pre
  have Dltx_eq : Dltx = Dltx_struct := by
    rw [x_decl_eq, St_decl_eq] at x_decl_struct
    exact (List.append_right_inj decl).mp x_decl_struct
  subst Dltx_struct
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
      (Std.Do.Triple.and _
        (S_ih E typ_S
        (fun v hv => Δ_fv v (fv_S_sub hv)) related_S
        Δx_none Δx_dom den_S
        (fun v hv => used_sub_x (vars_used v (by
          simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
            List.mem_append] at hv ⊢
          rcases hv with h | h <;> [left; right] <;> exact Or.inr h)))
        (fun v hv hΓ => by
          have hv_parent : v ∈ (x =ᴮ S).vars := by
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
          have hv_parent : v ∈ (x =ᴮ S).vars := by
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
    (encodeTerm_bv_notMem_used E (t := S) (used := Stx.env.usedVars)
      (n := Stx.env.freshvarsc) (decl := Stx.env.declarations)))
  clear S_ih S_scoped
  rename_i out_S
  obtain ⟨S_enc, sS⟩ := out_S
  mrename_i pre
  mintro ∀StS
  mpure pre
  dsimp at pre
  obtain ⟨⟨⟨S_post, ⟨DltS, S_decl_eq, S_ctx, S_trace, S_sc_total, S_guard,
      S_specs_op, S_sc_typing⟩⟩,
      bv_S_used, _S_used_sub_struct, DltS_struct,
        S_decl_struct, S_delta_ok⟩,
      _bv_S_not_used, _S_used_sub_notmem, DltS_notmem,
        S_decl_notmem, S_delta_not_used⟩ := pre
  have DltS_eq : DltS = DltS_struct := by
    rw [S_decl_eq, x_decl_eq] at S_decl_struct
    exact (List.append_right_inj (decl ++ Dltx)).mp S_decl_struct
  subst DltS_struct
  have DltS_notmem_eq : DltS = DltS_notmem := by
    rw [S_decl_eq, x_decl_eq] at S_decl_notmem
    exact (List.append_right_inj (decl ++ Dltx)).mp S_decl_notmem
  subst DltS_notmem
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

  mspec castEq_supported_rep_scoped_contract a x_enc S_enc sx sS
    X_rel.supported A_rel.supported typ_x_final typ_S_enc
    (fun v hv => used_sub_S (bv_x_used v hv)) bv_S_used
  rename_i out_eq
  obtain ⟨eq_enc, seq⟩ := out_eq
  mrename_i pre
  mintro ∀StEq
  mpure pre
  obtain ⟨used_sub_Eq, types_sub_Eq, keys_sub_Eq, seq_eq,
    typ_eq, fv_x_eq, fv_S_eq, eq_preserves,
    DltEq, eq_decl_eq, eq_ctx, eq_trace, eq_decl_fresh, eq_sem,
    eq_specs_op, eq_sc_typing⟩ := pre
  change seq = SMTType.bool at seq_eq
  subst seq
  mpure_intro
  have children_ctx : ContextGeneratedByDeclarations St.types
      StS.types (Dltx ++ DltS) :=
    ContextGeneratedByDeclarations.append x_ctx S_ctx
  refine ⟨(Dltx ++ DltS) ++ DltEq, ?_,
    ContextGeneratedByDeclarations.append children_ctx eq_ctx,
    DeclarationContextTrace.append
      (DeclarationContextTrace.append x_trace S_trace) eq_trace,
    ?_, ?_, ?_, ?_⟩
  · rw [eq_decl_eq, S_decl_eq]
    simp only [List.append_assoc]
  · intro Δ_alt Δ_fv_alt Δ₀_alt related_alt wf_alt
      Δ₀_alt_none respects_alt Δ₀_alt_dom
      T_alt hT_alt den_t_alt
    obtain ⟨X_alt, A_alt, hX_alt, hA_alt,
        den_x_alt, den_S_alt, hT_alt_iff⟩ :=
      denote_eq_inv_rep typ_x typ_S Δ_fv_alt wf_alt den_t_alt
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
          ΔS_alt StEq.types x_enc :=
      target_respects_x_alt_final.of_extends
        (SMT.RenamingContext.extends_refl ΔS_alt)
        types_sub_Eq typ_x_final
    have target_respects_S_alt_M :
        SMT.RenamingContext.RespectsTypeContextOnFV
          ΔS_alt StEq.types S_enc :=
      target_respects_S_alt.of_extends
        (SMT.RenamingContext.extends_refl ΔS_alt)
        types_sub_Eq typ_S_enc
    have ΔS_alt_dom_M : ∀ v, ΔS_alt v ≠ none → v ∈ StEq.types :=
      fun v hv => AList.mem_of_subset types_sub_Eq (ΔS_alt_dom v hv)
    obtain ⟨good_alt, _guarded_alt⟩ := eq_sem StEq.types
      (fun _ h => h) ΔS_alt hcov_x_alt_final hcov_S_alt
      ΔS_alt_none target_respects_x_alt_M target_respects_S_alt_M
      ΔS_alt_dom_M X_alt A_alt T_alt hX_alt hA_alt hT_alt
      (⟨Xenc_alt, sx, hXenc_alt⟩ : SMT.Dom)
      (⟨Aenc_alt, sS, hAenc_alt⟩ : SMT.Dom)
      hden_x_alt_final hden_S_alt rfl rfl
      X_alt_rel A_alt_rel hT_alt_iff
    obtain ⟨ΔEq_alt, hcov_Eq_alt, denEq_alt, ΔEq_alt_ext,
        ΔEq_alt_none, target_respects_Eq_alt, ΔEq_alt_dom,
        specs_Eq_alt, hden_Eq_alt, hdenEq_alt_type, result_alt_rel⟩ :=
      good_alt
    have ΔS_alt_ext₀ :=
      SMT.RenamingContext.extends_trans ΔS_alt_ext Δx_alt_ext
    have ΔEq_alt_ext₀ :=
      SMT.RenamingContext.extends_trans ΔEq_alt_ext ΔS_alt_ext₀
    have specs_x_at_S : SpecBodiesTrue ΔS_alt StS.types Dltx :=
      specs_x_alt.of_extends ΔS_alt_ext types_sub_S Δx_alt_dom
    have specs_children_at_S :
        SpecBodiesTrue ΔS_alt StS.types (Dltx ++ DltS) :=
      specs_x_at_S.append specs_S_alt
    have specs_children_at_M :
        SpecBodiesTrue ΔEq_alt StEq.types (Dltx ++ DltS) :=
      specs_children_at_S.of_extends
        ΔEq_alt_ext types_sub_Eq ΔS_alt_dom
    refine ⟨ΔEq_alt, hcov_Eq_alt, denEq_alt, ΔEq_alt_ext₀,
      related_alt.of_extends ΔEq_alt_ext₀, ΔEq_alt_none, ?_,
      target_respects_Eq_alt, ΔEq_alt_dom,
      specs_children_at_M.append specs_Eq_alt,
      hden_Eq_alt, hdenEq_alt_type, result_alt_rel⟩
    exact respects_alt.of_extends ΔEq_alt_ext₀
      (fun _ h => types_sub_Eq (types_sub_S (types_sub_x h)))
      (fun _ h => h) fv_in_Λ
  · intro Γ_sup Γ_sub Δ_alt Δ_fv_alt Θ related_alt wf_alt
      respects_B respects_SMT specs_true T_alt hT_alt den_t_alt
      hcov_eq denOut hdenOut hdenOut_type
    obtain ⟨X_alt, A_alt, hX_alt, hA_alt,
        den_x_alt, den_S_alt, hT_alt_iff⟩ :=
      denote_eq_inv_rep typ_x typ_S Δ_fv_alt wf_alt den_t_alt
    have hcov_x_target : SMT.RenamingContext.CoversFV Θ x_enc := by
      intro v hv
      exact hcov_eq v (fv_x_eq hv)
    have hcov_S_target : SMT.RenamingContext.CoversFV Θ S_enc := by
      intro v hv
      exact hcov_eq v (fv_S_eq hv)
    have target_respects_x_sup :
        SMT.RenamingContext.RespectsTypeContextOnFV Θ Γ_sup x_enc :=
      respects_SMT.mono_fv fv_x_eq
    have target_respects_S_sup :
        SMT.RenamingContext.RespectsTypeContextOnFV Θ Γ_sup S_enc :=
      respects_SMT.mono_fv fv_S_eq
    have specs_children :
        SpecBodiesTrue Θ Γ_sup (Dltx ++ DltS) :=
      specs_true.left_of_append
    have specs_x : SpecBodiesTrue Θ Γ_sup Dltx :=
      specs_children.left_of_append
    have specs_S : SpecBodiesTrue Θ Γ_sup DltS :=
      specs_children.right_of_append
    have specs_M : SpecBodiesTrue Θ Γ_sup DltEq :=
      specs_true.right_of_append
    have typ_x_M : StEq.types ⊢ˢ x_enc : sx :=
      SMT.Typing.weakening types_sub_Eq typ_x_final (by
        intro v hv
        exact eq_preserves v (used_sub_S (bv_x_used v hv))
          (SMT.Typing.bv_notMem_context typ_x_final v hv))
    have typ_S_M : StEq.types ⊢ˢ S_enc : sS :=
      SMT.Typing.weakening types_sub_Eq typ_S_enc (by
        intro v hv
        exact eq_preserves v (bv_S_used v hv)
          (SMT.Typing.bv_notMem_context typ_S_enc v hv))
    have result_ctx : ContextGeneratedByDeclarations St.types
        StEq.types ((Dltx ++ DltS) ++ DltEq) :=
      ContextGeneratedByDeclarations.append children_ctx eq_ctx
    have StEq_sub_sup : StEq.types ⊆ Γ_sup := by
      intro e he
      exact Γ_sub (result_ctx he)
    have target_respects_x_M :
        SMT.RenamingContext.RespectsTypeContextOnFV Θ StEq.types x_enc :=
      target_respects_x_sup.of_super StEq_sub_sup
    have target_respects_S_M :
        SMT.RenamingContext.RespectsTypeContextOnFV Θ StEq.types S_enc :=
      target_respects_S_sup.of_super StEq_sub_sup
    obtain ⟨denX_target, hdenX_target, hdenX_target_type⟩ :=
      SMT.RenamingContext.denote_exists_of_typing_fv
        typ_x_M target_respects_x_M hcov_x_target
    obtain ⟨denA_target, hdenA_target, hdenA_target_type⟩ :=
      SMT.RenamingContext.denote_exists_of_typing_fv
        typ_S_M target_respects_S_M hcov_S_target
    have children_scope : ScopedContextExtends St.types
        (Dltx ++ DltS) Γ_sup := Γ_sub.left_of_append
    have x_scope : ScopedContextExtends St.types Dltx Γ_sup :=
      children_scope.left_of_append
    have S_scope : ScopedContextExtends Stx.types DltS Γ_sup :=
      ScopedContextExtends.right_of_generated x_ctx children_scope
    have eq_scope : ScopedContextExtends StS.types DltEq Γ_sup :=
      ScopedContextExtends.right_of_generated children_ctx Γ_sub
    have X_rel_target := x_guard Γ_sup x_scope Δ_alt
      (fun v hv => Δ_fv_alt v (fv_x_sub hv)) Θ
      (related_alt.mono_fv fv_x_sub) wf_alt
      (respects_B.mono_fv fv_x_sub) target_respects_x_sup
      specs_x X_alt hX_alt den_x_alt
      hcov_x_target denX_target hdenX_target hdenX_target_type
    have A_rel_target := S_guard Γ_sup S_scope Δ_alt
      (fun v hv => Δ_fv_alt v (fv_S_sub hv)) Θ
      (related_alt.mono_fv fv_S_sub) wf_alt
      (respects_B.mono_fv fv_S_sub) target_respects_S_sup
      specs_S A_alt hA_alt den_S_alt
      hcov_S_target denA_target hdenA_target hdenA_target_type
    have target_respects_x_base_M :
        SMT.RenamingContext.RespectsTypeContextOnFV
          ΔS StEq.types x_enc :=
      target_respects_x_final.of_extends
        (SMT.RenamingContext.extends_refl ΔS)
        types_sub_Eq typ_x_final
    have target_respects_S_base_M :
        SMT.RenamingContext.RespectsTypeContextOnFV
          ΔS StEq.types S_enc :=
      target_respects_S.of_extends
        (SMT.RenamingContext.extends_refl ΔS)
        types_sub_Eq typ_S_enc
    have ΔS_dom_M : ∀ v, ΔS v ≠ none → v ∈ StEq.types :=
      fun v hv => AList.mem_of_subset types_sub_Eq (ΔS_dom v hv)
    obtain ⟨_good_base, eq_guard⟩ := eq_sem StEq.types
      (fun _ h => h) ΔS hcov_x_final hcov_S ΔS_none
      target_respects_x_base_M target_respects_S_base_M ΔS_dom_M
      X Y T hX hY hT
      (⟨Xenc, sx, hXenc⟩ : SMT.Dom)
      (⟨Aenc, sS, hAenc⟩ : SMT.Dom)
      hden_x_final hden_S rfl rfl
      X_rel A_rel hTiff
    have result_rel := eq_guard Γ_sup eq_scope Θ
      hcov_x_target hcov_S_target
      target_respects_x_sup target_respects_S_sup
      X_alt A_alt T_alt hX_alt hA_alt hT_alt denX_target denA_target
      hdenX_target hdenA_target hdenX_target_type hdenA_target_type
      X_rel_target A_rel_target hT_alt_iff
      hcov_eq denOut respects_SMT specs_M hdenOut hdenOut_type
    exact result_rel
  · intro body hbody
    rw [specBodies_append, List.mem_append] at hbody
    rcases hbody with hchildren | heq_body
    · rw [specBodies_append, List.mem_append] at hchildren
      rcases hchildren with hxbody | hSbody
      · have typ_at_S : StS.types ⊢ˢ body : SMTType.bool :=
          typing_weakening_generated types_sub_S S_ctx
            S_delta_not_used.1 (x_specs_op body hxbody)
            (fun v hv => x_delta_ok.2 body hxbody v hv)
        exact typing_weakening_generated types_sub_Eq eq_ctx
          eq_decl_fresh typ_at_S
          (fun v hv => used_sub_S (x_delta_ok.2 body hxbody v hv))
      · exact typing_weakening_generated types_sub_Eq eq_ctx
          eq_decl_fresh (S_specs_op body hSbody)
          (fun v hv => S_delta_ok.2 body hSbody v hv)
    · exact eq_specs_op body heq_body
  · constructor
    · intro Γ_sup Γ_sub result_bv_fresh
      have eq_scope : ScopedContextExtends StS.types DltEq Γ_sup :=
        ScopedContextExtends.right_of_generated children_ctx Γ_sub
      exact eq_sc_typing.1 Γ_sup eq_scope result_bv_fresh
    · intro Γ_sup Γ_sub specs_bv_fresh
      have children_scope : ScopedContextExtends St.types
          (Dltx ++ DltS) Γ_sup := Γ_sub.left_of_append
      have x_scope : ScopedContextExtends St.types Dltx Γ_sup :=
        children_scope.left_of_append
      have S_scope : ScopedContextExtends Stx.types DltS Γ_sup :=
        ScopedContextExtends.right_of_generated x_ctx children_scope
      have eq_scope : ScopedContextExtends StS.types DltEq Γ_sup :=
        ScopedContextExtends.right_of_generated children_ctx Γ_sub
      have x_specs_bv_fresh :
          ∀ b ∈ specBodies Dltx, ∀ v ∈ SMT.bv b, v ∉ Γ_sup := by
        intro b hb
        exact specs_bv_fresh b (by
          rw [specBodies_append, List.mem_append]
          exact Or.inl (by
            rw [specBodies_append, List.mem_append]
            exact Or.inl hb))
      have S_specs_bv_fresh :
          ∀ b ∈ specBodies DltS, ∀ v ∈ SMT.bv b, v ∉ Γ_sup := by
        intro b hb
        exact specs_bv_fresh b (by
          rw [specBodies_append, List.mem_append]
          exact Or.inl (by
            rw [specBodies_append, List.mem_append]
            exact Or.inr hb))
      have eq_specs_bv_fresh :
          ∀ b ∈ specBodies DltEq, ∀ v ∈ SMT.bv b, v ∉ Γ_sup := by
        intro b hb
        exact specs_bv_fresh b (by
          rw [specBodies_append, List.mem_append]
          exact Or.inr hb)
      have x_specs :=
        x_sc_typing.2 Γ_sup x_scope x_specs_bv_fresh
      have S_specs :=
        S_sc_typing.2 Γ_sup S_scope S_specs_bv_fresh
      have eq_specs :=
        eq_sc_typing.2 Γ_sup eq_scope eq_specs_bv_fresh
      intro body hbody
      rw [specBodies_append, List.mem_append] at hbody
      rcases hbody with hchildren | heq_body
      · rw [specBodies_append, List.mem_append] at hchildren
        exact hchildren.elim (x_specs body) (S_specs body)
      · exact eq_specs body heq_body
