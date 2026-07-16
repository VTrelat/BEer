import SMT.Reasoning.Basic.EncodeTermRepresentedBase
import SMT.Reasoning.Basic.EncodeTermBvUsed

open Std.Do B SMT ZFSet

/-! # Representation-aware arithmetic and pair constructors -/

set_option maxHeartbeats 2000000 in
theorem encodeTerm_rep_spec.maplet_case.{u}
    (x y : B.Term)
    (x_ih : EncodeTermRepIH.{u} x)
    (y_ih : EncodeTermRepIH.{u} y)
    (E : B.Env) {Λ : SMT.TypeContext} {α : BType}
    (typ_t : E.context ⊢ᴮ x ↦ᴮ y : α)
    {«Δ» : B.RenamingContext.Context}
    (Δ_fv : ∀ v ∈ B.fv (x ↦ᴮ y), («Δ» v).isSome = true)
    {Δ₀ : SMT.RenamingContext.Context.{u}}
    (related : RValuationCastOnFV «Δ» Δ₀ (x ↦ᴮ y))
    {used : List SMT.𝒱}
    (Δ₀_none_out : ∀ v ∉ used, Δ₀ v = none)
    (Δ₀_dom : ∀ v, Δ₀ v ≠ none → v ∈ Λ)
    {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ}
    (den_t : ⟦(x ↦ᴮ y).abstract «Δ» Δ_fv⟧ᴮ =
      some ⟨T, ⟨α, hT⟩⟩)
    (vars_used : ∀ v ∈ (x ↦ᴮ y).vars, v ∈ used)
    (Λ_inv : ∀ v ∈ (x ↦ᴮ y).vars, v ∈ Λ → v ∈ E.context)
    (bv_nodup : (B.bv (x ↦ᴮ y)).Nodup)
    (respects : B.RenamingContext.RespectsTypeContextOnFV
      Δ₀ Λ (x ↦ᴮ y))
    (fv_in_Λ : ∀ v ∈ B.fv (x ↦ᴮ y), v ∈ Λ)
    (wf : B.RenWF E.context «Δ»)
    {n : ℕ} :
    ⦃fun ⟨E0, Λ'⟩ ↦
      ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧
        Λ.keys ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
    encodeTerm (x ↦ᴮ y) E
    ⦃⇓? (⟨t', σ⟩ : SMT.Term × SMTType) ⟨E', Γ'⟩ =>
      ⌜EncodeTermRepPost (x ↦ᴮ y) α Λ «Δ» Δ₀ used T hT
        E t' σ E' Γ'⌝⦄ := by
  mstart
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
  rw [encodeTerm]

  apply B.Typing.mapletE at typ_t
  obtain ⟨αx, βx, rfl, typ_x, typ_y⟩ := typ_t

  rw [B.Term.abstract, B.denote, Option.pure_def, Option.bind_eq_bind,
    Option.bind_eq_some_iff] at den_t
  obtain ⟨⟨X, α', hX⟩, den_x, hrest⟩ := den_t
  dsimp at hrest
  rw [Option.bind_eq_some_iff] at hrest
  obtain ⟨⟨Y, β', hY⟩, den_y, hout⟩ := hrest
  rw [Option.some_inj] at hout
  dsimp at hout
  injection hout with T_eq type_eq
  subst T
  injection type_eq with pair_type_eq _
  injection pair_type_eq with α'_eq β'_eq
  subst α' β'

  have fv_x_sub : B.fv x ⊆ B.fv (x ↦ᴮ y) := by
    intro v hv
    simpa [B.fv] using (Or.inl hv : v ∈ B.fv x ∨ v ∈ B.fv y)
  have fv_y_sub : B.fv y ⊆ B.fv (x ↦ᴮ y) := by
    intro v hv
    simpa [B.fv] using (Or.inr hv : v ∈ B.fv x ∨ v ∈ B.fv y)
  have hx_bv_nodup : (B.bv x).Nodup := by
    have h := bv_nodup
    simp only [B.bv, List.nodup_append] at h
    exact h.1
  have hy_bv_nodup : (B.bv y).Nodup := by
    have h := bv_nodup
    simp only [B.bv, List.nodup_append] at h
    exact h.2.1
  have hxy_bv_disj : ∀ a ∈ B.bv x, ∀ b ∈ B.bv y, a ≠ b := by
    have h := bv_nodup
    simp only [B.bv, List.nodup_append] at h
    exact h.2.2

  mspec (Std.Do.Triple.and _
    (Std.Do.Triple.and _
      (x_ih E typ_x
        (fun v hv => Δ_fv v (fv_x_sub hv))
        (related.mono_fv fv_x_sub)
        Δ₀_none_out Δ₀_dom den_x
        (fun v hv => vars_used v (by
          simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
            List.mem_append] at hv ⊢
          rcases hv with h | h <;> [left; right] <;> exact .inl h))
        (fun v hv => Λ_inv v (by
          simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
            List.mem_append] at hv ⊢
          rcases hv with h | h <;> [left; right] <;> exact .inl h))
        hx_bv_nodup (respects.mono_fv fv_x_sub)
        (fun v hv => fv_in_Λ v (fv_x_sub hv)) wf
        (n := St.env.freshvarsc))
      (encodeTerm_bv_used E (t := x) (used := St.env.usedVars)
        (n := St.env.freshvarsc) (decl := St.env.declarations)))
    (encodeTerm_bv_notMem_used E (t := x) (used := St.env.usedVars)
      (n := St.env.freshvarsc) (decl := St.env.declarations)))
  clear x_ih
  rename_i out_x
  obtain ⟨x_enc, σx⟩ := out_x
  mrename_i pre
  mintro ∀Stx
  mpure pre
  dsimp at pre
  obtain ⟨⟨⟨used_sub_x, types_sub_x, keys_sub_x, x_used,
      path_x, typ_x_enc, x_preserves,
      Δx, hcov_x, Δx_ext, _related_x, Δx_none, _respects_x, Δx_dom,
      denX, hden_x, hdenX_type, X_rel, x_total⟩,
      bv_x_used, _⟩,
      bv_x_not_used, _⟩ := pre
  rcases denX with ⟨Xenc, σX, hXenc⟩
  dsimp at hdenX_type
  subst σX
  obtain ⟨cx⟩ := path_x

  have related_y : RValuationCastOnFV «Δ» Δx y :=
    (related.mono_fv fv_y_sub).of_extends Δx_ext
  have respects_y : B.RenamingContext.RespectsTypeContextOnFV
      Δx Stx.types y :=
    respects.of_extends Δx_ext types_sub_x fv_y_sub fv_in_Λ

  mspec y_ih E typ_y
    (fun v hv => Δ_fv v (fv_y_sub hv)) related_y
    Δx_none Δx_dom den_y
    (fun v hv => used_sub_x (vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
        List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inr h)))
    (fun v hv hΓ => by
      have hv_maplet : v ∈ (x ↦ᴮ y).vars := by
        simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
          List.mem_append] at hv ⊢
        rcases hv with h | h <;> [left; right] <;> exact .inr h
      by_cases hv_Λ : v ∈ St.types
      · exact Λ_inv v hv_maplet hv_Λ
      · have hv_vars_x : v ∈ B.Term.vars x := by
          by_contra hnot
          exact absurd hΓ
            (x_preserves v (vars_used v hv_maplet) hv_Λ hnot)
        rcases B.Term.mem_vars_iff.mp hv_vars_x with hx_fv | hx_bv
        · exact B.Typing.typed_by_fv typ_x hx_fv
        · rcases B.Term.mem_vars_iff.mp hv with hy_fv | hy_bv
          · exact absurd (B.Typing.typed_by_fv typ_y hy_fv)
              (B.Typing.bv_notMem_context typ_x v hx_bv)
          · exact absurd rfl (hxy_bv_disj v hx_bv v hy_bv))
    hy_bv_nodup respects_y
    (fun v hv => AList.mem_of_subset types_sub_x
      (fv_in_Λ v (fv_y_sub hv))) wf
    (n := Stx.env.freshvarsc)
  clear y_ih
  rename_i out_y
  obtain ⟨y_enc, σy⟩ := out_y
  mrename_i pre
  mintro ∀Sty
  mpure pre
  dsimp at pre
  obtain ⟨used_sub_y, types_sub_y, keys_sub_y, y_used,
    path_y, typ_y_enc, y_preserves,
    Δy, hcov_y, Δy_ext, _related_y, Δy_none, _respects_y, Δy_dom,
    denY, hden_y, hdenY_type, Y_rel, y_total⟩ := pre
  rcases denY with ⟨Yenc, σY, hYenc⟩
  dsimp at hdenY_type
  subst σY
  obtain ⟨cy⟩ := path_y

  have bv_x_not_final : ∀ v ∈ SMT.bv x_enc, v ∉ Sty.types :=
    fun v hv => y_preserves v (bv_x_used v hv)
      (SMT.Typing.bv_notMem_context typ_x_enc v hv)
      (by
        rw [B.Term.notMem_vars_iff]
        refine ⟨?_, ?_⟩
        · intro hfy
          exact SMT.Typing.bv_notMem_context typ_x_enc v hv
            (AList.mem_of_subset types_sub_x
              (fv_in_Λ v (fv_y_sub hfy)))
        · intro hby
          exact bv_x_not_used v hv
            (St_used_eq ▸ vars_used v (by
              simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
                List.mem_append]
              right
              right
              exact hby)))
  have typ_x_final : Sty.types ⊢ˢ x_enc : σx :=
    SMT.Typing.weakening types_sub_y typ_x_enc bv_x_not_final
  have hcov_x_final : RenamingContext.CoversFV Δy x_enc :=
    RenamingContext.coversFV_of_extends_of_coversFV Δy_ext hcov_x
  have hden_x_final :
      ⟦x_enc.abstract Δy hcov_x_final⟧ˢ =
        some (⟨Xenc, σx, hXenc⟩ : SMT.Dom) := by
    have hagree :=
      RenamingContext.agreesOnFV_of_extends_of_coversFV Δy_ext hcov_x
    have hcongr := RenamingContext.denote_congr_of_agreesOnFV
      (t := x_enc) (h1 := hcov_x_final) (h2 := hcov_x) hagree
    simpa [RenamingContext.denote] using hcongr.trans hden_x

  mspec Std.Do.Spec.pure
  mpure_intro
  have Δy_ext₀ := RenamingContext.extends_trans Δy_ext Δx_ext
  and_intros
  · intro v hv
    exact used_sub_y (used_sub_x (by simpa [St_used_eq] using hv))
  · exact fun _ h => types_sub_y (types_sub_x h)
  · exact keys_sub_y
  · intro v hv
    rw [B.fv, List.mem_append] at hv
    exact hv.elim (fun h => used_sub_y (x_used v h)) (fun h => y_used v h)
  · exact ⟨castPath.pair cx cy⟩
  · apply SMT.Typing.pair
    · exact typ_x_final
    · exact typ_y_enc
  · intro v hv hΛ hvars hΓ
    rw [B.Term.notMem_vars_maplet] at hvars
    have hv_not_Stx : v ∉ Stx.types := by
      intro hΓx
      by_cases hv_St : v ∈ St.types
      · exact hΛ hv_St
      · exact x_preserves v (by simpa [St_used_eq] using hv)
          hv_St hvars.1 hΓx
    exact y_preserves v (used_sub_x (by simpa [St_used_eq] using hv))
      hv_not_Stx hvars.2 hΓ
  · refine ⟨Δy, ?_, Δy_ext₀, related.of_extends Δy_ext₀,
      Δy_none, ?_, Δy_dom, ?_⟩
    · intro v hv
      rw [SMT.fv, List.mem_append] at hv
      exact hv.elim (hcov_x_final v) (hcov_y v)
    · exact respects.of_extends Δy_ext₀
        (fun _ h => types_sub_y (types_sub_x h)) (fun _ h => h) fv_in_Λ
    · let denPair : SMT.Dom.{u} :=
        ⟨Xenc.pair Yenc, SMTType.pair σx σy,
          ZFSet.pair_mem_prod.mpr ⟨hXenc, hYenc⟩⟩
      refine ⟨denPair, ?_, rfl, ?_, ?_⟩
      · simp only [denPair, SMT.Term.abstract, SMT.denote, Option.pure_def,
          Option.bind_eq_bind, hden_x_final, Option.bind_some, hden_y]
      · simpa [denPair] using RDomCast.pair X_rel Y_rel
      · intro Δ_alt Δ_fv_alt Δ₀_alt related_alt wf_alt
          Δ₀_alt_none respects_alt Δ₀_alt_dom T_alt hT_alt den_t_alt
        rw [B.Term.abstract, B.denote, Option.pure_def,
          Option.bind_eq_bind, Option.bind_eq_some_iff] at den_t_alt
        obtain ⟨⟨X_alt, α_alt, hX_alt⟩, den_x_alt, hrest_alt⟩ :=
          den_t_alt
        dsimp at hrest_alt
        rw [Option.bind_eq_some_iff] at hrest_alt
        obtain ⟨⟨Y_alt, β_alt, hY_alt⟩, den_y_alt, hout_alt⟩ :=
          hrest_alt
        rw [Option.some_inj] at hout_alt
        dsimp at hout_alt
        injection hout_alt with T_alt_eq type_alt_eq
        subst T_alt
        injection type_alt_eq with pair_alt_eq _
        injection pair_alt_eq with α_alt_eq β_alt_eq
        subst α_alt β_alt

        have Δ₀_alt_none_x : ∀ v ∉ Stx.env.usedVars,
            Δ₀_alt v = none := by
          intro v hv
          by_contra hne
          have hv_Λ := Δ₀_alt_dom v hne
          have hv_used : v ∈ used := by
            simpa [← St_used_eq] using St_sub hv_Λ
          exact hv (used_sub_x hv_used)
        obtain ⟨Δx_alt, hcov_x_alt, denX_alt, Δx_alt_ext,
            _related_x_alt, Δx_alt_none, _respects_x_alt, Δx_alt_dom,
            hden_x_alt, hdenX_alt_type, X_alt_rel⟩ :=
          x_total Δ_alt
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
        have related_alt_y : RValuationCastOnFV Δ_alt Δx_alt y :=
          (related_alt.mono_fv fv_y_sub).of_extends Δx_alt_ext
        have respects_alt_y :
            B.RenamingContext.RespectsTypeContextOnFV
              Δx_alt Stx.types y :=
          respects_alt.of_extends Δx_alt_ext types_sub_x
            fv_y_sub fv_in_Λ
        obtain ⟨Δy_alt, hcov_y_alt, denY_alt, Δy_alt_ext,
            _related_y_alt, Δy_alt_none, _respects_y_alt, Δy_alt_dom,
            hden_y_alt, hdenY_alt_type, Y_alt_rel⟩ :=
          y_total Δ_alt
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
              some (⟨Xenc_alt, σx, hXenc_alt⟩ : SMT.Dom) := by
          have hagree :=
            RenamingContext.agreesOnFV_of_extends_of_coversFV
              Δy_alt_ext hcov_x_alt
          have hcongr := RenamingContext.denote_congr_of_agreesOnFV
            (t := x_enc) (h1 := hcov_x_alt_final)
            (h2 := hcov_x_alt) hagree
          simpa [RenamingContext.denote] using hcongr.trans hden_x_alt
        have hcov_pair_alt : RenamingContext.CoversFV Δy_alt
            (SMT.Term.pair x_enc y_enc) := by
          intro v hv
          rw [SMT.fv, List.mem_append] at hv
          exact hv.elim (hcov_x_alt_final v) (hcov_y_alt v)
        have Δy_alt_ext₀ :=
          RenamingContext.extends_trans Δy_alt_ext Δx_alt_ext
        let denPairAlt : SMT.Dom.{u} :=
          ⟨Xenc_alt.pair Yenc_alt, SMTType.pair σx σy,
            ZFSet.pair_mem_prod.mpr ⟨hXenc_alt, hYenc_alt⟩⟩
        refine ⟨Δy_alt, hcov_pair_alt, denPairAlt, Δy_alt_ext₀,
          related_alt.of_extends Δy_alt_ext₀, Δy_alt_none, ?_,
          Δy_alt_dom, ?_, rfl, ?_⟩
        · exact respects_alt.of_extends Δy_alt_ext₀
            (fun _ h => types_sub_y (types_sub_x h))
            (fun _ h => h) fv_in_Λ
        · simp only [denPairAlt, SMT.Term.abstract, SMT.denote,
            Option.pure_def, Option.bind_eq_bind, hden_x_alt_final,
            Option.bind_some, hden_y_alt]
        · simpa [denPairAlt] using RDomCast.pair X_alt_rel Y_alt_rel
