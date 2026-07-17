import SMT.Reasoning.Basic.EncodeTermRepresentedScopedBase
import SMT.Reasoning.Basic.EncodeTermRepresentedBool

open Std.Do B SMT ZFSet Classical

/-! # Generated-helper contracts for Boolean terms -/

namespace EncodeTermRepresentedBool.CheckedOp

theorem smt_denote_inv.{u} (op : CheckedOp)
    {x y : SMT.Term} {Θ : SMT.RenamingContext.Context.{u}}
    (hcov : SMT.RenamingContext.CoversFV Θ (op.smtTerm x y))
    {d : SMT.Dom.{u}}
    (hden : ⟦(op.smtTerm x y).abstract Θ hcov⟧ˢ = some d) :
    ∃ X, ∃ hX : X ∈ ⟦SMTType.bool⟧ᶻ,
      ⟦x.abstract Θ (fun v hv => hcov v (by
        cases op
        rw [smtTerm, SMT.fv, List.mem_append]
        exact Or.inl hv))⟧ˢ = some ⟨X, SMTType.bool, hX⟩ ∧
      ∃ Y, ∃ hY : Y ∈ ⟦SMTType.bool⟧ᶻ,
        ⟦y.abstract Θ (fun v hv => hcov v (by
          cases op
          rw [smtTerm, SMT.fv, List.mem_append]
          exact Or.inr hv))⟧ˢ = some ⟨Y, SMTType.bool, hY⟩ ∧
        d = ⟨op.eval X Y, SMTType.bool, op.eval_mem hX hY⟩ := by
  cases op
  simp only [smtTerm, eval] at hden ⊢
  rw [SMT.Term.abstract, SMT.denote, Option.pure_def,
    Option.bind_eq_bind, Option.bind_eq_some_iff] at hden
  obtain ⟨⟨X, σX, hX⟩, hdenX, hrest⟩ := hden
  cases σX <;> first
    | rw [Option.bind_eq_some_iff] at hrest
    | exact absurd hrest (by simp)
  obtain ⟨⟨Y, σY, hY⟩, hdenY, hout⟩ := hrest
  cases σY <;> first
    | rw [Option.some_inj] at hout
    | exact absurd hout (by simp)
  refine ⟨X, hX, ?_, Y, hY, ?_, ?_⟩
  · simpa only [proof_irrel_heq] using hdenX
  · simpa only [proof_irrel_heq] using hdenY
  · simpa only [proof_irrel_heq] using hout.symm

end EncodeTermRepresentedBool.CheckedOp

set_option maxHeartbeats 4000000 in
theorem encodeTerm_rep_scoped.checked_bool_case.{u}
    (op : EncodeTermRepresentedBool.CheckedOp)
    (x y : B.Term)
    (x_ih : EncodeTermRepIH.{u} x)
    (y_ih : EncodeTermRepIH.{u} y)
    (x_scoped : EncodeTermRepScopedBoolIH.{u} x)
    (y_scoped : EncodeTermRepScopedBoolIH.{u} y)
    (E : B.Env) {Λ : SMT.TypeContext}
    (typ_t : E.context ⊢ᴮ op.term x y : BType.bool)
    {«Δ» : B.RenamingContext.Context}
    (Δ_fv : ∀ v ∈ B.fv (op.term x y), («Δ» v).isSome = true)
    {Δ₀ : SMT.RenamingContext.Context.{u}}
    (related : RValuationCastSupportedOnFV «Δ» Δ₀ (op.term x y))
    {used : List SMT.𝒱}
    (Δ₀_none_out : ∀ v ∉ used, Δ₀ v = none)
    (Δ₀_dom : ∀ v, Δ₀ v ≠ none → v ∈ Λ)
    {T : ZFSet.{u}} {hT : T ∈ ⟦BType.bool⟧ᶻ}
    (den_t : ⟦(op.term x y).abstract «Δ» Δ_fv⟧ᴮ =
      some ⟨T, ⟨BType.bool, hT⟩⟩)
    (vars_used : ∀ v ∈ (op.term x y).vars, v ∈ used)
    (Λ_inv : ∀ v ∈ (op.term x y).vars,
      v ∈ Λ → v ∈ E.context)
    (bv_nodup : (B.bv (op.term x y)).Nodup)
    (respects : B.RenamingContext.RespectsTypeContextOnFV
      Δ₀ Λ (op.term x y))
    (fv_in_Λ : ∀ v ∈ B.fv (op.term x y), v ∈ Λ)
    (wf : B.RenWF E.context «Δ»)
    {n : ℕ} {decl : SMT.Chunk} :
    ⦃fun ⟨E0, Λ'⟩ ↦
      ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧
        Λ.keys ⊆ E0.usedVars ∧ E0.usedVars = used ∧
        E0.declarations = decl⌝ ⦄
    encodeTerm (op.term x y) E
    ⦃⇓? (⟨t', σ⟩ : SMT.Term × SMTType) ⟨E', Γ'⟩ =>
      ⌜EncodeTermRepScopedPost.{u} (op.term x y) E BType.bool Λ decl
        t' σ E' Γ'⌝ ⦄ := by
  mstart
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_sub, St_used_eq, St_decl_eq⟩ := pre
  rw [EncodeTermRepresentedBool.CheckedOp.encodeTerm_eq_run]
  unfold EncodeTermRepresentedBool.CheckedOp.run

  obtain ⟨_, typ_x, typ_y⟩ := op.typingE typ_t
  obtain ⟨X, hX, den_x, Y, hY, den_y, T_eq⟩ :=
    op.denote_inv (op.typing typ_x typ_y) Δ_fv den_t
  subst T

  have fv_x_sub : B.fv x ⊆ B.fv (op.term x y) := by
    intro v hv
    rw [op.fv_term, List.mem_append]
    exact Or.inl hv
  have fv_y_sub : B.fv y ⊆ B.fv (op.term x y) := by
    intro v hv
    rw [op.fv_term, List.mem_append]
    exact Or.inr hv
  have hx_bv_nodup : (B.bv x).Nodup := by
    have h := bv_nodup
    rw [op.bv_term, List.nodup_append] at h
    exact h.1
  have hy_bv_nodup : (B.bv y).Nodup := by
    have h := bv_nodup
    rw [op.bv_term, List.nodup_append] at h
    exact h.2.1
  have hxy_bv_disj : ∀ a ∈ B.bv x, ∀ b ∈ B.bv y, a ≠ b := by
    have h := bv_nodup
    rw [op.bv_term, List.nodup_append] at h
    exact h.2.2
  have vars_used_x : ∀ v ∈ x.vars, v ∈ used := by
    intro v hv
    apply vars_used v
    rw [op.vars_term]
    simp only [List.mem_union_iff, List.mem_append]
    rcases B.Term.mem_vars_iff.mp hv with h | h
    · exact .inl (.inl h)
    · exact .inr (.inl h)
  have Λ_inv_x : ∀ v ∈ x.vars, v ∈ St.types → v ∈ E.context := by
    intro v hv
    apply Λ_inv v
    rw [op.vars_term]
    simp only [List.mem_union_iff, List.mem_append]
    rcases B.Term.mem_vars_iff.mp hv with h | h
    · exact .inl (.inl h)
    · exact .inr (.inl h)

  mspec (Std.Do.Triple.and _
    (x_ih E typ_x
      (fun v hv => Δ_fv v (fv_x_sub hv))
      (related.mono_fv fv_x_sub)
      Δ₀_none_out Δ₀_dom den_x vars_used_x Λ_inv_x
      hx_bv_nodup (respects.mono_fv fv_x_sub)
      (fun v hv => fv_in_Λ v (fv_x_sub hv)) wf
      (n := St.env.freshvarsc))
    (x_scoped E typ_x
      (fun v hv => Δ_fv v (fv_x_sub hv))
      (related.mono_fv fv_x_sub)
      Δ₀_none_out Δ₀_dom den_x vars_used_x Λ_inv_x
      hx_bv_nodup (respects.mono_fv fv_x_sub)
      (fun v hv => fv_in_Λ v (fv_x_sub hv)) wf
      (n := St.env.freshvarsc) (decl := decl)))
  clear x_ih x_scoped
  rename_i out_x
  obtain ⟨x_enc, σx⟩ := out_x
  mrename_i pre
  mintro ∀Stx
  mpure pre
  dsimp at pre
  obtain ⟨x_post, ⟨Dltx, x_decl_eq, x_ctx, x_sc_total, x_guard,
    x_sc_typing⟩⟩ := pre
  obtain ⟨used_sub_x, types_sub_x, keys_sub_x, x_used,
    path_x, typ_x_enc, _shape_x, x_preserves,
    Δx, hcov_x, Δx_ext, _related_x, Δx_none, _respects_x,
    target_respects_x, Δx_dom,
    denX, hden_x, hdenX_type, X_rel, x_total⟩ := x_post
  rcases denX with ⟨Xenc, σX, hXenc⟩
  dsimp at hdenX_type
  subst σX
  obtain ⟨cx⟩ := path_x
  have hσx : σx = SMTType.bool := castPath.source_eq_bool cx
  subst σx

  have related_y : RValuationCastSupportedOnFV «Δ» Δx y :=
    (related.mono_fv fv_y_sub).of_extends Δx_ext
  have respects_y : B.RenamingContext.RespectsTypeContextOnFV
      Δx Stx.types y :=
    respects.of_extends Δx_ext types_sub_x fv_y_sub fv_in_Λ
  have vars_used_y : ∀ v ∈ y.vars, v ∈ Stx.env.usedVars := by
    intro v hv
    apply used_sub_x
    apply vars_used v
    rw [op.vars_term]
    simp only [List.mem_union_iff, List.mem_append]
    rcases B.Term.mem_vars_iff.mp hv with h | h
    · exact .inl (.inr h)
    · exact .inr (.inr h)
  have Λ_inv_y : ∀ v ∈ y.vars, v ∈ Stx.types → v ∈ E.context := by
    intro v hv hΓ
    have hv_parent : v ∈ (op.term x y).vars := by
      rw [op.vars_term]
      simp only [List.mem_union_iff, List.mem_append]
      rcases B.Term.mem_vars_iff.mp hv with h | h
      · exact .inl (.inr h)
      · exact .inr (.inr h)
    by_cases hv_Λ : v ∈ St.types
    · exact Λ_inv v hv_parent hv_Λ
    · have hv_vars_x : v ∈ B.Term.vars x := by
        by_contra hnot
        exact absurd hΓ
          (x_preserves v (vars_used v hv_parent) hv_Λ hnot)
      rcases B.Term.mem_vars_iff.mp hv_vars_x with hx_fv | hx_bv
      · exact B.Typing.typed_by_fv typ_x hx_fv
      · rcases B.Term.mem_vars_iff.mp hv with hy_fv | hy_bv
        · exact absurd (B.Typing.typed_by_fv typ_y hy_fv)
            (B.Typing.bv_notMem_context typ_x v hx_bv)
        · exact absurd rfl (hxy_bv_disj v hx_bv v hy_bv)

  mspec (Std.Do.Triple.and _
    (y_ih E typ_y
      (fun v hv => Δ_fv v (fv_y_sub hv)) related_y
      Δx_none Δx_dom den_y vars_used_y Λ_inv_y
      hy_bv_nodup respects_y
      (fun v hv => AList.mem_of_subset types_sub_x
        (fv_in_Λ v (fv_y_sub hv))) wf
      (n := Stx.env.freshvarsc))
    (y_scoped E typ_y
      (fun v hv => Δ_fv v (fv_y_sub hv)) related_y
      Δx_none Δx_dom den_y vars_used_y Λ_inv_y
      hy_bv_nodup respects_y
      (fun v hv => AList.mem_of_subset types_sub_x
        (fv_in_Λ v (fv_y_sub hv))) wf
      (n := Stx.env.freshvarsc) (decl := decl ++ Dltx)))
  clear y_ih y_scoped
  rename_i out_y
  obtain ⟨y_enc, σy⟩ := out_y
  mrename_i pre
  mintro ∀Sty
  mpure pre
  dsimp at pre
  obtain ⟨y_post, ⟨Dlty, y_decl_eq, y_ctx, y_sc_total, y_guard,
    y_sc_typing⟩⟩ := pre
  obtain ⟨used_sub_y, types_sub_y, keys_sub_y, y_used,
    path_y, typ_y_enc, _shape_y, y_preserves,
    Δy, hcov_y, Δy_ext, _related_y, Δy_none, _respects_y,
    target_respects_y, Δy_dom,
    denY, hden_y, hdenY_type, Y_rel, y_total⟩ := y_post
  rcases denY with ⟨Yenc, σY, hYenc⟩
  dsimp at hdenY_type
  subst σY
  obtain ⟨cy⟩ := path_y
  have hσy : σy = SMTType.bool := castPath.source_eq_bool cy
  subst σy

  mspec Std.Do.Spec.pure
  mpure_intro
  refine ⟨Dltx ++ Dlty, ?_,
    ContextGeneratedByDeclarations.append x_ctx y_ctx, ?_, ?_, ?_⟩
  · rw [y_decl_eq, List.append_assoc]
  · intro Δ_alt Δ_fv_alt Δ₀_alt related_alt wf_alt
      Δ₀_alt_none respects_alt Δ₀_alt_dom T_alt hT_alt den_t_alt
    obtain ⟨X_alt, hX_alt, den_x_alt, Y_alt, hY_alt,
        den_y_alt, T_alt_eq⟩ :=
      op.denote_inv (op.typing typ_x typ_y) Δ_fv_alt den_t_alt
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
    rcases denX_alt with ⟨Xenc_alt, σX_alt, hXenc_alt⟩
    dsimp at hdenX_alt_type
    subst σX_alt

    have Δx_alt_none_y : ∀ v ∉ Sty.env.usedVars,
        Δx_alt v = none := by
      intro v hv
      apply Δx_alt_none v
      intro hvx
      exact hv (used_sub_y hvx)
    have related_alt_y : RValuationCastSupportedOnFV Δ_alt Δx_alt y :=
      (related_alt.mono_fv fv_y_sub).of_extends Δx_alt_ext
    have respects_alt_y : B.RenamingContext.RespectsTypeContextOnFV
        Δx_alt Stx.types y :=
      respects_alt.of_extends Δx_alt_ext types_sub_x
        fv_y_sub fv_in_Λ
    obtain ⟨Δy_alt, hcov_y_alt, denY_alt, Δy_alt_ext,
        _related_y_alt, Δy_alt_none, _respects_y_alt,
        target_respects_y_alt, Δy_alt_dom, specs_y_alt,
        hden_y_alt, hdenY_alt_type, Y_alt_rel⟩ :=
      y_sc_total Δ_alt
        (fun v hv => Δ_fv_alt v (fv_y_sub hv)) Δx_alt
        related_alt_y wf_alt Δx_alt_none_y respects_alt_y
        Δx_alt_dom Y_alt hY_alt den_y_alt
    rcases denY_alt with ⟨Yenc_alt, σY_alt, hYenc_alt⟩
    dsimp at hdenY_alt_type
    subst σY_alt

    have hcov_x_alt_final : RenamingContext.CoversFV Δy_alt x_enc :=
      RenamingContext.coversFV_of_extends_of_coversFV
        Δy_alt_ext hcov_x_alt
    have hden_x_alt_final :
        ⟦x_enc.abstract Δy_alt hcov_x_alt_final⟧ˢ =
          some (⟨Xenc_alt, SMTType.bool, hXenc_alt⟩ : SMT.Dom) := by
      have hagree := RenamingContext.agreesOnFV_of_extends_of_coversFV
        Δy_alt_ext hcov_x_alt
      have hcongr := RenamingContext.denote_congr_of_agreesOnFV
        (t := x_enc) (h1 := hcov_x_alt_final)
        (h2 := hcov_x_alt) hagree
      simpa [RenamingContext.denote] using hcongr.trans hden_x_alt
    have target_respects_x_alt_final :
        SMT.RenamingContext.RespectsTypeContextOnFV
          Δy_alt Sty.types x_enc :=
      target_respects_x_alt.of_extends
        Δy_alt_ext types_sub_y typ_x_enc
    have hcov_op_alt : RenamingContext.CoversFV Δy_alt
        (op.smtTerm x_enc y_enc) := by
      intro v hv
      cases op <;> simp only [EncodeTermRepresentedBool.CheckedOp.smtTerm,
        SMT.fv, List.mem_append] at hv
      exact hv.elim (hcov_x_alt_final v) (hcov_y_alt v)
    have Δy_alt_ext₀ :=
      RenamingContext.extends_trans Δy_alt_ext Δx_alt_ext
    have specs_x_final : SpecBodiesTrue Δy_alt Sty.types Dltx :=
      specs_x_alt.of_extends Δy_alt_ext types_sub_y Δx_alt_dom
    let denOpAlt : SMT.Dom.{u} :=
      ⟨op.eval Xenc_alt Yenc_alt, SMTType.bool,
        op.eval_mem hXenc_alt hYenc_alt⟩
    refine ⟨Δy_alt, hcov_op_alt, denOpAlt, Δy_alt_ext₀,
      related_alt.of_extends Δy_alt_ext₀, Δy_alt_none, ?_,
      ?_, Δy_alt_dom, specs_x_final.append specs_y_alt, ?_, rfl, ?_⟩
    · exact respects_alt.of_extends Δy_alt_ext₀
        (fun _ h => types_sub_y (types_sub_x h))
        (fun _ h => h) fv_in_Λ
    · intro v τ hv hlookup
      cases op <;> simp only [EncodeTermRepresentedBool.CheckedOp.smtTerm,
        SMT.fv, List.mem_append] at hv
      exact hv.elim
        (fun hx => target_respects_x_alt_final hx hlookup)
        (fun hy => target_respects_y_alt hy hlookup)
    · cases op <;> simp [denOpAlt,
        EncodeTermRepresentedBool.CheckedOp.smtTerm,
        EncodeTermRepresentedBool.CheckedOp.eval,
        SMT.Term.abstract, SMT.denote, hden_x_alt_final,
        hden_y_alt]
    · refine ⟨?_, .bool⟩
      simpa [denOpAlt] using
        op.rdomCast_eval X_alt_rel.toRDomCast Y_alt_rel.toRDomCast
  · intro Γ_sup Γ_sub Δ_alt Δ_fv_alt Θ related_alt wf_alt
      respects_B respects_SMT specs_true T_alt hT_alt den_t_alt
      hcov denOut hdenOut hdenOut_type
    obtain ⟨X_alt, hX_alt, den_x_alt, Y_alt, hY_alt,
        den_y_alt, T_alt_eq⟩ :=
      op.denote_inv (op.typing typ_x typ_y) Δ_fv_alt den_t_alt
    subst T_alt
    obtain ⟨Xenc_alt, hXenc_alt, hden_x_target,
      Yenc_alt, hYenc_alt, hden_y_target, denOut_eq⟩ :=
      op.smt_denote_inv hcov hdenOut
    have x_scope : ScopedContextExtends St.types Dltx Γ_sup :=
      Γ_sub.left_of_append
    have y_scope : ScopedContextExtends Stx.types Dlty Γ_sup :=
      ScopedContextExtends.right_of_generated x_ctx Γ_sub
    have hcov_x_target : RenamingContext.CoversFV Θ x_enc := by
      intro v hv
      apply hcov v
      cases op <;> simp only [EncodeTermRepresentedBool.CheckedOp.smtTerm,
        SMT.fv, List.mem_append]
      exact Or.inl hv
    have hcov_y_target : RenamingContext.CoversFV Θ y_enc := by
      intro v hv
      apply hcov v
      cases op <;> simp only [EncodeTermRepresentedBool.CheckedOp.smtTerm,
        SMT.fv, List.mem_append]
      exact Or.inr hv
    have target_respects_x_sup :
        SMT.RenamingContext.RespectsTypeContextOnFV Θ Γ_sup x_enc :=
      respects_SMT.mono_fv (by
        intro v hv
        cases op <;> simp only [EncodeTermRepresentedBool.CheckedOp.smtTerm,
          SMT.fv, List.mem_append]
        exact Or.inl hv)
    have target_respects_y_sup :
        SMT.RenamingContext.RespectsTypeContextOnFV Θ Γ_sup y_enc :=
      respects_SMT.mono_fv (by
        intro v hv
        cases op <;> simp only [EncodeTermRepresentedBool.CheckedOp.smtTerm,
          SMT.fv, List.mem_append]
        exact Or.inr hv)
    have X_rel_target := x_guard Γ_sup x_scope Δ_alt
      (fun v hv => Δ_fv_alt v (fv_x_sub hv)) Θ
      (related_alt.mono_fv fv_x_sub) wf_alt
      (respects_B.mono_fv fv_x_sub) target_respects_x_sup
      specs_true.left_of_append X_alt hX_alt den_x_alt
      hcov_x_target ⟨Xenc_alt, SMTType.bool, hXenc_alt⟩
      hden_x_target rfl
    have Y_rel_target := y_guard Γ_sup y_scope Δ_alt
      (fun v hv => Δ_fv_alt v (fv_y_sub hv)) Θ
      (related_alt.mono_fv fv_y_sub) wf_alt
      (respects_B.mono_fv fv_y_sub) target_respects_y_sup
      specs_true.right_of_append Y_alt hY_alt den_y_alt
      hcov_y_target ⟨Yenc_alt, SMTType.bool, hYenc_alt⟩
      hden_y_target rfl
    subst denOut
    refine ⟨?_, .bool⟩
    simpa only [proof_irrel_heq] using
      op.rdomCast_eval X_rel_target.toRDomCast Y_rel_target.toRDomCast
  · constructor
    · intro Γ_sup Γ_sub result_bv_fresh
      have x_scope : ScopedContextExtends St.types Dltx Γ_sup :=
        Γ_sub.left_of_append
      have y_scope : ScopedContextExtends Stx.types Dlty Γ_sup :=
        ScopedContextExtends.right_of_generated x_ctx Γ_sub
      have x_bv_fresh : ∀ v ∈ SMT.bv x_enc, v ∉ Γ_sup := by
        intro v hv
        apply result_bv_fresh v
        cases op
        simp only [EncodeTermRepresentedBool.CheckedOp.smtTerm, SMT.bv,
          List.mem_append]
        exact Or.inl hv
      have y_bv_fresh : ∀ v ∈ SMT.bv y_enc, v ∉ Γ_sup := by
        intro v hv
        apply result_bv_fresh v
        cases op
        simp only [EncodeTermRepresentedBool.CheckedOp.smtTerm, SMT.bv,
          List.mem_append]
        exact Or.inr hv
      exact op.smt_typing
        (x_sc_typing.1 Γ_sup x_scope x_bv_fresh)
        (y_sc_typing.1 Γ_sup y_scope y_bv_fresh)
    · intro Γ_sup Γ_sub specs_bv_fresh
      have x_scope : ScopedContextExtends St.types Dltx Γ_sup :=
        Γ_sub.left_of_append
      have y_scope : ScopedContextExtends Stx.types Dlty Γ_sup :=
        ScopedContextExtends.right_of_generated x_ctx Γ_sub
      have x_specs_bv_fresh :
          ∀ b ∈ specBodies Dltx, ∀ v ∈ SMT.bv b, v ∉ Γ_sup := by
        intro b hb
        exact specs_bv_fresh b (by
          rw [specBodies_append, List.mem_append]
          exact Or.inl hb)
      have y_specs_bv_fresh :
          ∀ b ∈ specBodies Dlty, ∀ v ∈ SMT.bv b, v ∉ Γ_sup := by
        intro b hb
        exact specs_bv_fresh b (by
          rw [specBodies_append, List.mem_append]
          exact Or.inr hb)
      have specs_x_sup :=
        x_sc_typing.2 Γ_sup x_scope x_specs_bv_fresh
      have specs_y_sup :=
        y_sc_typing.2 Γ_sup y_scope y_specs_bv_fresh
      intro b hb
      rw [specBodies_append, List.mem_append] at hb
      exact hb.elim (specs_x_sup b) (specs_y_sup b)

theorem smt_denote_not_inv.{u}
    {x : SMT.Term} {Θ : SMT.RenamingContext.Context.{u}}
    (hcov : SMT.RenamingContext.CoversFV Θ (SMT.Term.not x))
    {d : SMT.Dom.{u}}
    (hden : ⟦(SMT.Term.not x).abstract Θ hcov⟧ˢ = some d) :
    ∃ X, ∃ hX : X ∈ ⟦SMTType.bool⟧ᶻ,
      ⟦x.abstract Θ (fun v hv => hcov v (by
        simpa [SMT.fv] using hv))⟧ˢ =
        some ⟨X, SMTType.bool, hX⟩ ∧
      d = ⟨¬ᶻ X, SMTType.bool, overloadUnaryOp_mem⟩ := by
  rw [SMT.Term.abstract, SMT.denote, Option.pure_def,
    Option.bind_eq_bind, Option.bind_eq_some_iff] at hden
  obtain ⟨⟨X, σX, hX⟩, hdenX, hout⟩ := hden
  cases σX <;> first
    | rw [Option.some_inj] at hout
    | exact absurd hout (by simp)
  refine ⟨X, hX, ?_, ?_⟩
  · simpa only [proof_irrel_heq] using hdenX
  · simpa only [proof_irrel_heq] using hout.symm

set_option maxHeartbeats 2400000 in
theorem encodeTerm_rep_scoped.not_case.{u}
    (x : B.Term)
    (x_ih : EncodeTermRepIH.{u} x)
    (x_scoped : EncodeTermRepScopedBoolIH.{u} x)
    (E : B.Env) {Λ : SMT.TypeContext}
    (typ_t : E.context ⊢ᴮ ¬ᴮ x : BType.bool)
    {«Δ» : B.RenamingContext.Context}
    (Δ_fv : ∀ v ∈ B.fv (¬ᴮ x), («Δ» v).isSome = true)
    {Δ₀ : SMT.RenamingContext.Context.{u}}
    (related : RValuationCastSupportedOnFV «Δ» Δ₀ (¬ᴮ x))
    {used : List SMT.𝒱}
    (Δ₀_none_out : ∀ v ∉ used, Δ₀ v = none)
    (Δ₀_dom : ∀ v, Δ₀ v ≠ none → v ∈ Λ)
    {T : ZFSet.{u}} {hT : T ∈ ⟦BType.bool⟧ᶻ}
    (den_t : ⟦(¬ᴮ x).abstract «Δ» Δ_fv⟧ᴮ =
      some ⟨T, ⟨BType.bool, hT⟩⟩)
    (vars_used : ∀ v ∈ (¬ᴮ x).vars, v ∈ used)
    (Λ_inv : ∀ v ∈ (¬ᴮ x).vars, v ∈ Λ → v ∈ E.context)
    (bv_nodup : (B.bv (¬ᴮ x)).Nodup)
    (respects : B.RenamingContext.RespectsTypeContextOnFV
      Δ₀ Λ (¬ᴮ x))
    (fv_in_Λ : ∀ v ∈ B.fv (¬ᴮ x), v ∈ Λ)
    (wf : B.RenWF E.context «Δ»)
    {n : ℕ} {decl : SMT.Chunk} :
    ⦃fun ⟨E0, Λ'⟩ ↦
      ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧
        Λ.keys ⊆ E0.usedVars ∧ E0.usedVars = used ∧
        E0.declarations = decl⌝ ⦄
    encodeTerm (¬ᴮ x) E
    ⦃⇓? (⟨t', σ⟩ : SMT.Term × SMTType) ⟨E', Γ'⟩ =>
      ⌜EncodeTermRepScopedPost.{u} (¬ᴮ x) E BType.bool Λ decl
        t' σ E' Γ'⌝ ⦄ := by
  mstart
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_sub, St_used_eq, St_decl_eq⟩ := pre
  rw [encodeTerm]
  obtain ⟨_, typ_x⟩ := B.Typing.notE typ_t
  obtain ⟨X, hX, den_x, T_eq⟩ :=
    denote_not_inv (B.Typing.not typ_x) Δ_fv den_t
  subst T
  have fv_x_sub : B.fv x ⊆ B.fv (¬ᴮ x) := by
    intro v hv
    simpa [B.fv] using hv
  have hx_bv_nodup : (B.bv x).Nodup := by
    simpa [B.bv] using bv_nodup
  have vars_used_x : ∀ v ∈ x.vars, v ∈ used := by
    intro v hv
    exact vars_used v (by simpa [B.Term.vars, B.fv, B.bv] using hv)
  have Λ_inv_x : ∀ v ∈ x.vars, v ∈ St.types → v ∈ E.context := by
    intro v hv
    exact Λ_inv v (by simpa [B.Term.vars, B.fv, B.bv] using hv)
  mspec (Std.Do.Triple.and _
    (x_ih E typ_x
      (fun v hv => Δ_fv v (fv_x_sub hv))
      (related.mono_fv fv_x_sub)
      Δ₀_none_out Δ₀_dom den_x vars_used_x Λ_inv_x
      hx_bv_nodup (respects.mono_fv fv_x_sub)
      (fun v hv => fv_in_Λ v (fv_x_sub hv)) wf
      (n := St.env.freshvarsc))
    (x_scoped E typ_x
      (fun v hv => Δ_fv v (fv_x_sub hv))
      (related.mono_fv fv_x_sub)
      Δ₀_none_out Δ₀_dom den_x vars_used_x Λ_inv_x
      hx_bv_nodup (respects.mono_fv fv_x_sub)
      (fun v hv => fv_in_Λ v (fv_x_sub hv)) wf
      (n := St.env.freshvarsc) (decl := decl)))
  clear x_ih x_scoped
  rename_i out_x
  obtain ⟨x_enc, σx⟩ := out_x
  mrename_i pre
  mintro ∀Stx
  mpure pre
  dsimp at pre
  obtain ⟨x_post, ⟨Dltx, x_decl_eq, x_ctx, x_sc_total, x_guard,
    x_sc_typing⟩⟩ := pre
  obtain ⟨used_sub_x, types_sub_x, keys_sub_x, x_used,
    path_x, typ_x_enc, _shape_x, x_preserves,
    Δx, hcov_x, Δx_ext, _related_x, Δx_none, _respects_x,
    target_respects_x, Δx_dom,
    denX, hden_x, hdenX_type, X_rel, x_total⟩ := x_post
  rcases denX with ⟨Xenc, σX, hXenc⟩
  dsimp at hdenX_type
  subst σX
  obtain ⟨cx⟩ := path_x
  have hσx : σx = SMTType.bool := castPath.source_eq_bool cx
  subst σx
  mspec Std.Do.Spec.pure
  mpure_intro
  refine ⟨Dltx, x_decl_eq, x_ctx, ?_, ?_, ?_⟩
  · intro Δ_alt Δ_fv_alt Δ₀_alt related_alt wf_alt
      Δ₀_alt_none respects_alt Δ₀_alt_dom T_alt hT_alt den_t_alt
    obtain ⟨X_alt, hX_alt, den_x_alt, T_alt_eq⟩ :=
      denote_not_inv (B.Typing.not typ_x) Δ_fv_alt den_t_alt
    subst T_alt
    obtain ⟨Δx_alt, hcov_x_alt, denX_alt, Δx_alt_ext,
        related_x_alt, Δx_alt_none, respects_x_alt,
        target_respects_x_alt, Δx_alt_dom, specs_x_alt,
        hden_x_alt, hdenX_alt_type, X_alt_rel⟩ :=
      x_sc_total Δ_alt
        (fun v hv => Δ_fv_alt v (fv_x_sub hv)) Δ₀_alt
        (related_alt.mono_fv fv_x_sub) wf_alt Δ₀_alt_none
        (respects_alt.mono_fv fv_x_sub) Δ₀_alt_dom
        X_alt hX_alt den_x_alt
    rcases denX_alt with ⟨Xenc_alt, σX_alt, hXenc_alt⟩
    dsimp at hdenX_alt_type
    subst σX_alt
    have hcov_not_alt : RenamingContext.CoversFV Δx_alt
        (SMT.Term.not x_enc) := by
      intro v hv
      exact hcov_x_alt v (by simpa [SMT.fv] using hv)
    let denNotAlt : SMT.Dom.{u} :=
      ⟨¬ᶻ Xenc_alt, SMTType.bool, overloadUnaryOp_mem⟩
    refine ⟨Δx_alt, hcov_not_alt, denNotAlt, Δx_alt_ext,
      related_alt.of_extends Δx_alt_ext, Δx_alt_none, ?_,
      ?_, Δx_alt_dom, specs_x_alt, ?_, rfl, ?_⟩
    · simpa [B.fv] using respects_x_alt
    · intro v τ hv hlookup
      exact target_respects_x_alt (by simpa [SMT.fv] using hv) hlookup
    · simp [denNotAlt, SMT.Term.abstract, SMT.denote, hden_x_alt]
    · refine ⟨?_, .bool⟩
      simpa [denNotAlt] using rdomCast_not X_alt_rel.toRDomCast
  · intro Γ_sup Γ_sub Δ_alt Δ_fv_alt Θ related_alt wf_alt
      respects_B respects_SMT specs_true T_alt hT_alt den_t_alt
      hcov denOut hdenOut hdenOut_type
    obtain ⟨X_alt, hX_alt, den_x_alt, T_alt_eq⟩ :=
      denote_not_inv (B.Typing.not typ_x) Δ_fv_alt den_t_alt
    subst T_alt
    obtain ⟨Xenc_alt, hXenc_alt, hden_x_target, denOut_eq⟩ :=
      smt_denote_not_inv hcov hdenOut
    have hcov_x_target : RenamingContext.CoversFV Θ x_enc := by
      intro v hv
      exact hcov v (by simpa [SMT.fv] using hv)
    have target_respects_x_sup :
        SMT.RenamingContext.RespectsTypeContextOnFV Θ Γ_sup x_enc :=
      respects_SMT.mono_fv (by
        intro v hv
        simpa [SMT.fv] using hv)
    have X_rel_target := x_guard Γ_sup Γ_sub Δ_alt
      (fun v hv => Δ_fv_alt v (fv_x_sub hv)) Θ
      (related_alt.mono_fv fv_x_sub) wf_alt
      (respects_B.mono_fv fv_x_sub) target_respects_x_sup
      specs_true X_alt hX_alt den_x_alt
      hcov_x_target ⟨Xenc_alt, SMTType.bool, hXenc_alt⟩
      hden_x_target rfl
    subst denOut
    refine ⟨?_, .bool⟩
    simpa only [proof_irrel_heq] using
      rdomCast_not X_rel_target.toRDomCast
  · constructor
    · intro Γ_sup Γ_sub result_bv_fresh
      have typ_x_sup := x_sc_typing.1 Γ_sup Γ_sub (by
        intro v hv
        apply result_bv_fresh v
        simpa [SMT.bv] using hv)
      exact SMT.Typing.not Γ_sup x_enc typ_x_sup
    · exact x_sc_typing.2
