import SMT.Reasoning.Basic.EncodeTermRepresentedCollectSupported

open Std.Do B SMT ZFSet

/-! # Representation-aware raw collection encoding -/

/-- The functional collection arm decomposes the input product into every
left component followed by the final right component. -/
private theorem option_collect_fromProdl
    {alpha beta : SMTType} {a b : BType} {n : ℕ}
    (halpha : alpha = a.toSMTType) (hbeta : beta = b.toSMTType)
    (hn : 2 ≤ n) :
    (alpha.fromProdl (n - 2)).concat beta =
      ((a ×ᴮ b).toSMTType.fromProdl (n - 1)) := by
  subst alpha
  subst beta
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero => omega
    | succ n =>
      simp [SMT.SMTType.fromProdl, BType.toSMTType]

set_option maxHeartbeats 8000000 in
theorem encodeTerm_rep_spec.collect_case.{u}
    (vs : List B.𝒱) (D P : B.Term)
    (D_ih : EncodeTermRepIH.{u} D)
    (P_ih : EncodeTermRepIH.{u} P)
    (P_scoped : EncodeTermRepScopedBoolIH.{u} P)
    (E : B.Env) {Lambda : SMT.TypeContext} {alpha : BType}
    (typ_t : E.context ⊢ᴮ B.Term.collect vs D P : alpha)
    {Xi : B.RenamingContext.Context.{u}}
    (Xi_fv : ∀ v ∈ B.fv (B.Term.collect vs D P), (Xi v).isSome = true)
    {Theta0 : SMT.RenamingContext.Context.{u}}
    (related : RValuationCastSupportedOnFV Xi Theta0
      (B.Term.collect vs D P))
    {used : List SMT.𝒱}
    (Theta0_none : ∀ v ∉ used, Theta0 v = none)
    (Theta0_dom : ∀ v, Theta0 v ≠ none → v ∈ Lambda)
    {T : ZFSet.{u}} {hT : T ∈ ⟦alpha⟧ᶻ}
    (den_t : ⟦(B.Term.collect vs D P).abstract Xi Xi_fv⟧ᴮ =
      some ⟨T, ⟨alpha, hT⟩⟩)
    (vars_used : ∀ v ∈ (B.Term.collect vs D P).vars, v ∈ used)
    (Lambda_inv : ∀ v ∈ (B.Term.collect vs D P).vars,
      v ∈ Lambda → v ∈ E.context)
    (bv_nodup : (B.bv (B.Term.collect vs D P)).Nodup)
    (respects : B.RenamingContext.RespectsTypeContextOnFV Theta0 Lambda
      (B.Term.collect vs D P))
    (fv_in_Lambda : ∀ v ∈ B.fv (B.Term.collect vs D P), v ∈ Lambda)
    (wf : B.RenWF E.context Xi)
    {n : ℕ} :
    ⦃fun ⟨E0, Lambda'⟩ ↦
      ⌜Lambda' = Lambda ∧ E0.freshvarsc = n ∧
        Lambda.keys ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
    encodeTerm (B.Term.collect vs D P) E
    ⦃⇓? (⟨t', sigma⟩ : SMT.Term × SMTType) ⟨E', Gamma'⟩ =>
      ⌜EncodeTermRepPost (B.Term.collect vs D P) alpha Lambda Xi Theta0
        used T hT E t' sigma E' Gamma'⌝⦄ := by
  mstart
  mintro pre ∀St0
  mpure pre
  obtain ⟨rfl, rfl, St0_sub, St0_used_eq⟩ := pre
  obtain ⟨alphas, Ds, vs_nemp, vs_alphas_len, vs_Ds_len, alpha_eq,
      vs_nodup, D_eq, typ_Ds, typ_P, vs_context_disj⟩ :=
    B.Typing.collectE typ_t
  subst alpha_eq
  have alphas_nemp : alphas ≠ [] := by
    simpa [vs_alphas_len, ← List.length_pos_iff] using vs_nemp
  let tau := alphas.reduce (· ×ᴮ ·) alphas_nemp
  have typ_D : E.context ⊢ᴮ D : BType.set tau := by
    rw [D_eq]
    exact typing_reduce_cprod E.context _ _ typ_Ds
      (by simpa [vs_Ds_len, ← List.length_pos_iff] using vs_nemp)
      (by simpa [vs_alphas_len, ← List.length_pos_iff] using vs_nemp)
  have tau_hasArity : tau.hasArity vs.length := by
    dsimp [tau]
    rw [List.reduce]
    have hlen : alphas.tail.length + 1 = vs.length := by
      rw [List.length_tail, vs_alphas_len]
      have := List.length_pos_of_ne_nil alphas_nemp
      omega
    convert BType.hasArity_of_foldl
      (α := alphas.head alphas_nemp) (αs := alphas.tail) using 1
    exact hlen.symm
  have Xi_fv_D : ∀ v ∈ B.fv D, (Xi v).isSome = true :=
    fun v hv => Xi_fv v (B.fv.mem_collect (.inl hv))
  have related_D : RValuationCastSupportedOnFV Xi Theta0 D :=
    related.mono_fv (fun _ hv => B.fv.mem_collect (.inl hv))
  have vars_used_D : ∀ v ∈ D.vars, v ∈ used := by
    intro v hv
    apply vars_used v
    simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
      List.append_assoc, List.mem_append, List.mem_removeAll_iff] at hv ⊢
    rcases hv with hv | hv
    · exact .inl (.inl hv)
    · exact .inr (.inr (.inl hv))
  have vars_used_vs : ∀ v ∈ vs, v ∈ used := by
    intro v hv
    apply vars_used v
    simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
      List.append_assoc, List.mem_append, List.mem_removeAll_iff]
    exact .inr (.inl hv)
  have vars_used_P : ∀ v ∈ P.vars, v ∈ used := by
    intro v hv
    apply vars_used v
    simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
      List.append_assoc, List.mem_append, List.mem_removeAll_iff] at hv ⊢
    by_cases hvs : v ∈ vs
    · exact .inr (.inl hvs)
    · rcases hv with hv | hv
      · exact .inl (.inr ⟨hv, hvs⟩)
      · exact .inr (.inr (.inr hv))
  have Lambda_inv_D : ∀ v ∈ D.vars, v ∈ St0.types → v ∈ E.context := by
    intro v hv hctx
    apply Lambda_inv v _ hctx
    simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
      List.append_assoc, List.mem_append, List.mem_removeAll_iff] at hv ⊢
    rcases hv with hv | hv
    · exact .inl (.inl hv)
    · exact .inr (.inr (.inl hv))
  have D_bv_nodup : (B.bv D).Nodup := by
    have h := bv_nodup
    simp only [B.bv] at h
    rw [List.nodup_append, List.nodup_append] at h
    exact h.1.2.1
  have P_bv_nodup : (B.bv P).Nodup := by
    have h := bv_nodup
    simp only [B.bv] at h
    rw [List.nodup_append] at h
    exact h.2.1
  obtain ⟨Dval, hDval, den_D⟩ :=
    B.denote_collect_domain_exists Xi_fv typ_D wf den_t
  rw [encodeTerm]
  mspec (Std.Do.Triple.and _
    (Std.Do.Triple.and _
      (D_ih E typ_D Xi_fv_D related_D Theta0_none Theta0_dom den_D
        vars_used_D Lambda_inv_D D_bv_nodup
        (respects.mono_fv (fun _ hv => B.fv.mem_collect (.inl hv)))
        (fun v hv => fv_in_Lambda v (B.fv.mem_collect (.inl hv))) wf
        (n := St0.env.freshvarsc))
      (SMT.encodeTerm_bv_used E (t := D) (used := St0.env.usedVars)
        (n := St0.env.freshvarsc) (decl := St0.env.declarations)))
    (SMT.encodeTerm_bv_notMem_used E (t := D) (used := St0.env.usedVars)
      (n := St0.env.freshvarsc) (decl := St0.env.declarations)))
  rename_i out_D
  obtain ⟨Denc, sigmaD⟩ := out_D
  mrename_i D_post
  mintro ∀St1
  mpure D_post
  obtain ⟨⟨D_rep, D_bv_used_post⟩, D_bv_not_used_post⟩ := D_post
  obtain ⟨D_used_sub, D_types_sub, D_keys_sub, D_covers, D_path,
    typ_Denc, D_shape, D_preserves, ThetaD, hcov_Denc, ThetaD_ext,
    related_D_out, ThetaD_none, respects_D_out, target_respects_D,
    ThetaD_dom, DencVal, hden_Denc, hDenc_type, D_rel, D_total⟩ := D_rep
  obtain ⟨D_bv_used, D_used_sub_bv, Ddelta_bv, Ddelta_bv_ok⟩ :=
    D_bv_used_post
  obtain ⟨D_bv_not_used, D_used_sub_not_used, Ddelta_not_used,
    Ddelta_not_used_ok⟩ := D_bv_not_used_post
  split
  · rename_i alpha' beta' hDshape
    change sigmaD = alpha'.fun (SMTType.option beta') at hDshape
    subst sigmaD
    rcases DencVal with ⟨DencZF, sigmaVal, hDencMem⟩
    change sigmaVal = alpha'.fun (SMTType.option beta') at hDenc_type
    subst sigmaVal
    split
    · rename_i harity
      set alphas' := alpha'.fromProdl (vs.length - 2) with alphas'_def
      have alphas'_len : alphas'.length = vs.length - 1 :=
        beq_iff_eq.mp harity
      have alphas'_len_pos : 1 ≤ alphas'.length := by
        rw [alphas'_def]
        cases h : vs.length - 2 with
        | zero => cases alpha' <;> simp [SMT.SMTType.fromProdl]
        | succ k =>
          cases alpha' <;>
            simp [SMT.SMTType.fromProdl, List.concat_eq_append,
              List.length_append]
      have vs_len_ge_two : 2 ≤ vs.length := by
        omega
      mspec Std.Do.Spec.pure
      mspec (Std.Do.Triple.and _
        (encodeTerm_state.modifyTypes_forIn_spec
          (vs.zip (alphas'.concat beta'))
          (Γ := St1.types) (n := St1.env.freshvarsc)
          (used := St1.env.usedVars))
        (encodeTerm_state.modifyTypes_forIn_decls
          (vs.zip (alphas'.concat beta'))
          (decl := St1.env.declarations)))
      mrename_i modify_post
      mintro ∀St2
      mpure modify_post
      obtain ⟨⟨St2_types, St2_fresh, St2_used⟩, St2_decl⟩ := modify_post
      set Ebody : B.Env := { E with
        context := vs.zipToAList alphas ∪ E.context } with Ebody_def
      conv in encodeTerm P E =>
        rw [encodeTerm_state.encodeTerm_env_irrel P E Ebody rfl]
      have St2_used_eq : St2.env.usedVars = St1.env.usedVars := St2_used
      have vars_used_P_St2 : ∀ v ∈ P.vars, v ∈ St2.env.usedVars := by
        intro v hv
        rw [St2_used_eq]
        exact D_used_sub (vars_used_P v hv)
      have vs_disj_St1 : ∀ v ∈ vs, v ∉ St1.types := by
        intro v hv
        have vs_not_D_fv : v ∉ B.fv D := fun hv_fv =>
          vs_context_disj v hv
            (AList.lookup_isSome.mp
              (B.Typing.mem_context_of_mem_fv typ_D hv_fv))
        have hv_vars_D : v ∉ B.Term.vars D :=
          B.Term.notMem_vars_iff.mpr ⟨vs_not_D_fv, by
            have h := bv_nodup
            simp only [B.bv] at h
            rw [List.nodup_append, List.nodup_append] at h
            intro h_bv
            exact h.1.2.2 v hv v h_bv rfl⟩
        apply D_preserves v (vars_used_vs v hv) _ hv_vars_D
        intro hv_St0
        have hv_collect : v ∈ (B.Term.collect vs D P).vars := by
          unfold B.Term.vars
          rw [List.mem_union_iff]
          right
          simp only [B.bv, List.mem_append]
          exact .inl (.inl hv)
        exact vs_context_disj v hv (Lambda_inv v hv_collect hv_St0)
      have Lambda_inv_P : ∀ v ∈ P.vars,
          v ∈ St2.types → v ∈ Ebody.context := by
        intro v v_in_P_vars v_in_St2_types
        rw [Ebody_def]
        show v ∈ vs.zipToAList alphas ∪ E.context
        by_cases v_in_vs : v ∈ vs
        · exact AList.mem_union.mpr (.inl
            (AList.mem_zipToAList_of_mem vs_nodup vs_alphas_len v_in_vs))
        · have v_in_St1 : v ∈ St1.types := by
            rw [St2_types] at v_in_St2_types
            refine AList.mem_of_mem_foldl_insert' v_in_St2_types ?_
            intro h
            rw [List.mem_map] at h
            obtain ⟨⟨a, b⟩, hab, rfl⟩ := h
            exact v_in_vs (List.of_mem_zip hab).1
          have v_used : v ∈ used := vars_used_P v v_in_P_vars
          by_cases v_St0 : v ∈ St0.types
          · have v_collect : v ∈ (B.Term.collect vs D P).vars := by
              unfold B.Term.vars at v_in_P_vars ⊢
              rw [List.mem_union_iff]
              rcases List.mem_union_iff.mp v_in_P_vars with h_fv | h_bv
              · exact .inl (by
                  simp only [B.fv, List.mem_append]
                  exact .inr (List.mem_removeAll_iff.mpr ⟨h_fv, v_in_vs⟩))
              · exact .inr (by
                  simp only [B.bv, List.mem_append]
                  exact .inr h_bv)
            exact AList.mem_union.mpr (.inr (Lambda_inv v v_collect v_St0))
          · have v_vars_D : v ∈ B.Term.vars D := by
              by_contra h
              exact absurd v_in_St1
                (D_preserves v v_used v_St0 h)
            rcases B.Term.mem_vars_iff.mp v_vars_D with h | h
            · exact AList.mem_union.mpr (.inr
                (AList.lookup_isSome.mp
                  (B.Typing.mem_context_of_mem_fv typ_D h)))
            · rcases B.Term.mem_vars_iff.mp v_in_P_vars with hv_fv_P | hv_bv_P
              · have h_in_Ebody :
                  ((vs.zipToAList alphas ∪ E.context).lookup v).isSome :=
                    B.Typing.mem_context_of_mem_fv typ_P hv_fv_P
                exact AList.lookup_isSome.mp h_in_Ebody
              · exfalso
                have hbn := bv_nodup
                simp only [B.bv] at hbn
                rw [List.nodup_append] at hbn
                have hin : v ∈ vs ++ B.bv D :=
                  List.mem_append.mpr (.inr h)
                exact hbn.2.2 v hin v hv_bv_P rfl
      have St2_keys_sub : AList.keys St2.types ⊆ St2.env.usedVars := by
        rw [St2_types, St2_used_eq]
        exact encodeTerm_state.keys_foldl_insert_subset_of_fst_mem _ D_keys_sub
          (fun p hp => D_used_sub (vars_used_vs p.1 (List.of_mem_zip hp).1))
      have St1_sub_St2 : St1.types ⊆ St2.types := by
        rw [St2_types]
        refine AList.subset_foldl_insert' ?_ ?_
        · intro p hp
          exact vs_disj_St1 p.1 (List.mem_fst_of_mem_zip hp)
        · exact List.nodup_map_fst_of_nodup_zip vs_nodup
      obtain ⟨a, b, htau, halpha, hbeta⟩ :=
        RDomCastSupported.optionFunctionE D_rel
      have hraw_types : alphas'.concat beta' =
          tau.toSMTType.fromProdl (vs.length - 1) := by
        calc
          alphas'.concat beta' =
              (a ×ᴮ b).toSMTType.fromProdl (vs.length - 1) := by
                rw [alphas'_def]
                exact option_collect_fromProdl halpha hbeta vs_len_ge_two
          _ = tau.toSMTType.fromProdl (vs.length - 1) := by
                rw [htau]
      let xs : Fin vs.length → B.Dom := fun i =>
        ⟨tau.defaultZFSet.get vs.length i, tau.get vs.length i,
          get_mem_type_of_isTuple
            (BType.hasArity_of_foldl_defaultZFSet tau_hasArity)
            tau_hasArity BType.mem_toZFSet_of_defaultZFSet⟩
      have xs_type : ∀ i : Fin vs.length,
          (xs i).snd.fst = alphas[Fin.cast vs_alphas_len i] := by
        intro i
        dsimp [xs]
        exact BType.get_reduce alphas_nemp vs_alphas_len i
      have hbound_type : ∀ i : Fin vs.length,
          St2.types.lookup vs[i] = some (xs i).canonicalSMT.snd.fst := by
        intro i
        have hi_tau : i.val <
            (tau.toSMTType.fromProdl (vs.length - 1)).length := by
          rw [fromProdl_length_of_hasArity tau_hasArity]
          exact i.isLt
        have hlookup : St2.types.lookup vs[i] =
            some ((tau.toSMTType.fromProdl (vs.length - 1))[i.val]'hi_tau) := by
          rw [St2_types, hraw_types]
          exact foldl_insert_lookup_zip vs_nodup i.isLt hi_tau
        have hget := toSMTType_get_eq_fromProdl_getElem
          tau_hasArity i.isLt
        rw [← hget] at hlookup
        simpa [xs, B.Dom.canonicalSMT_type] using hlookup
      let XiP : B.RenamingContext.Context :=
        Function.updates Xi vs (List.ofFn fun i => some (xs i))
      let ThetaP0 : SMT.RenamingContext.Context :=
        Function.updates ThetaD vs
          ((List.ofFn fun i => (xs i).canonicalSMT).map Option.some)
      have hThetaP0_map :
          (List.ofFn fun i => (xs i).canonicalSMT).map Option.some =
            List.ofFn (fun i => some (xs i).canonicalSMT) := by
        rw [List.map_ofFn]
        rfl
      have wf_P : B.RenWF Ebody.context XiP := by
        dsimp [XiP]
        exact B.RenWF.updates_ofFn wf vs_nodup vs_context_disj
          vs_alphas_len xs_type
      have typ_P_body : Ebody.context ⊢ᴮ P : BType.bool := by
        simpa [Ebody] using typ_P
      obtain ⟨XiP_fv, Pval, hPval, den_P⟩ :=
        B.denote_collect_default_predicate_exists Xi_fv vs_nemp vs_nodup
          tau_hasArity den_D den_t typ_P_body wf_P
      have related_collect_out :
          RValuationCastSupportedOnFV Xi ThetaD
            (B.Term.collect vs D P) :=
        related.of_extends ThetaD_ext
      have related_P : RValuationCastSupportedOnFV XiP ThetaP0 P := by
        dsimp [XiP, ThetaP0]
        rw [hThetaP0_map]
        apply RValuationCastSupportedOnFV.updates_of_collect_default
          vs_nodup tau_hasArity
        intro v hv hv_not_vs
        exact related_collect_out v
          (B.fv.mem_collect (.inr ⟨hv, hv_not_vs⟩))
      have ThetaP0_none : ∀ v ∉ St2.env.usedVars, ThetaP0 v = none := by
        intro v hv
        dsimp [ThetaP0]
        apply SMT.RenamingContext.updates_none_of_mem_used
          (fun w hw => by
            rw [St2_used_eq]
            exact D_used_sub (vars_used_vs w hw))
          (fun w hw => ThetaD_none w (by
            rw [← St2_used_eq]
            exact hw)) v hv
      have ThetaP0_dom : ∀ v, ThetaP0 v ≠ none → v ∈ St2.types := by
        dsimp [ThetaP0]
        exact SMT.RenamingContext.updates_dom_of_typed_bounds
          (fun v hv => AList.mem_of_subset St1_sub_St2 (ThetaD_dom v hv))
          hbound_type
      have respects_P : B.RenamingContext.RespectsTypeContextOnFV
          ThetaP0 St2.types P := by
        dsimp [ThetaP0]
        apply B.RenamingContext.RespectsTypeContextOnFV.updates_of_typed_bounds
          vs_nodup
        · intro v hv hv_not_vs sigma hlookup
          have hv_collect : v ∈ B.fv (B.Term.collect vs D P) :=
            B.fv.mem_collect (.inr ⟨hv, hv_not_vs⟩)
          have hv_St0 : v ∈ St0.types := fv_in_Lambda v hv_collect
          obtain ⟨sigma0, hsigma0⟩ := Option.isSome_iff_exists.mp
            (AList.lookup_isSome.mpr hv_St0)
          have hsigma1 : St1.types.lookup v = some sigma0 :=
            AList.lookup_of_subset D_types_sub hsigma0
          have hsigma2 : St2.types.lookup v = some sigma0 := by
            rw [St2_types]
            apply foldl_insert_preserves_lookup hsigma1
            intro p hp hpv
            apply hv_not_vs
            rw [← hpv]
            exact (List.of_mem_zip hp).1
          rw [hsigma2] at hlookup
          cases hlookup
          obtain ⟨d, hd, hdty⟩ := respects hv_collect hsigma0
          exact ⟨d, ThetaD_ext hd, hdty⟩
        · exact hbound_type
      have fv_in_St2_P : ∀ v ∈ B.fv P, v ∈ St2.types := by
        intro v hv
        by_cases hvs : v ∈ vs
        · let i : Fin vs.length :=
            ⟨vs.idxOf v, List.idxOf_lt_length_of_mem hvs⟩
          have hvi : vs[i] = v := List.getElem_idxOf i.isLt
          apply AList.lookup_isSome.mp
          apply Option.isSome_of_eq_some
          have hbound := hbound_type i
          rw [hvi] at hbound
          exact hbound
        · exact AList.mem_of_subset St1_sub_St2
            (AList.mem_of_subset D_types_sub
              (fv_in_Lambda v (B.fv.mem_collect (.inr ⟨hv, hvs⟩))))
      mspec Std.Do.Spec.get_StateT
      mspec (Std.Do.Triple.and _
        (Std.Do.Triple.and _
          (Std.Do.Triple.and _
            (Std.Do.Triple.and _
              (P_ih Ebody typ_P_body XiP_fv related_P ThetaP0_none ThetaP0_dom
                den_P vars_used_P_St2 Lambda_inv_P P_bv_nodup respects_P
                fv_in_St2_P wf_P (n := St2.env.freshvarsc))
              (P_scoped Ebody typ_P_body XiP_fv related_P ThetaP0_none
                ThetaP0_dom den_P vars_used_P_St2 Lambda_inv_P P_bv_nodup
                respects_P fv_in_St2_P wf_P (n := St2.env.freshvarsc)
                (decl := St2.env.declarations)))
            (encodeTerm_decl Ebody typ_P_body vars_used_P_St2 Lambda_inv_P
              P_bv_nodup (n := St2.env.freshvarsc)
              (decl := St2.env.declarations)))
          (SMT.encodeTerm_bv_used Ebody (t := P)
            (used := St2.env.usedVars) (n := St2.env.freshvarsc)
            (decl := St2.env.declarations)))
        (SMT.encodeTerm_bv_notMem_used Ebody (t := P)
          (used := St2.env.usedVars) (n := St2.env.freshvarsc)
          (decl := St2.env.declarations)))
      rename_i out_P
      obtain ⟨Penc, sigmaP⟩ := out_P
      mrename_i P_post
      mintro ∀St3
      mpure P_post
      obtain ⟨⟨⟨⟨P_rep, P_scoped_post⟩, P_decl⟩, P_bv_used_post⟩,
        P_bv_not_used_post⟩ := P_post
      obtain ⟨DltP, P_sc_decl, P_ctx, P_trace, P_sc_total, P_guard,
        P_specs_op, P_sc_typing⟩ := P_scoped_post
      obtain ⟨P_used_sub, P_types_sub, P_keys_sub, P_covers, P_path,
        typ_Penc, P_shape, P_preserves, ThetaP, hcov_Penc, ThetaP_ext,
        related_P_out, ThetaP_none, respects_P_out, target_respects_P,
        ThetaP_dom, PencVal, hden_Penc, hPenc_type, P_rel, P_total⟩ := P_rep
      obtain ⟨Pdelta, St3_decl_eq, Pspec_fv, Penc_fv_delta⟩ := P_decl
      have DltP_eq : DltP = Pdelta := by
        rw [P_sc_decl] at St3_decl_eq
        exact List.append_right_injective _ St3_decl_eq
      subst DltP
      obtain ⟨P_bv_used, P_used_sub_bv, Pdelta_bv, Pdelta_bv_ok⟩ :=
        P_bv_used_post
      obtain ⟨P_bv_not_used, P_used_sub_not_used, Pdelta_not_used,
        Pdelta_not_used_ok⟩ := P_bv_not_used_post
      split
      · rename_i hPshape
        obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hPshape
        mspec (SMT.ensureDeclarationsUnchanged_spec (St := St3))
        mrename_i ensure_post
        mintro ∀St3'
        mpure ensure_post
        obtain ⟨St3'_eq, P_decl_len⟩ := ensure_post
        subst St3'
        have Pdelta_nil : Pdelta = [] :=
          declaration_delta_eq_nil_of_length St3_decl_eq P_decl_len
        subst Pdelta
        have Penc_fv : SMT.fv Penc ⊆ B.Term.vars P := by
          intro v hv
          simpa [declVars] using Penc_fv_delta hv
        mspec (Std.Do.Triple.and (SMT.freshVar alpha')
          (SMT.freshVar_spec (Γ := St3.types) (τ := alpha')
            (n := St3.env.freshvarsc) (used := St3.env.usedVars))
          (SMT.freshVar_decls (τ := alpha')
            (decl := St3.env.declarations)))
        rename_i z
        mrename_i fresh_post
        mintro ∀St4
        mpure fresh_post
        obtain ⟨⟨St4_types, z_fresh, St4_fresh, St4_used, z_not_used⟩,
          St4_decl⟩ := fresh_post
        mspec (Std.Do.Triple.and (SMT.eraseFromContext z)
          (SMT.eraseFromContext_spec (v := z) (Γ := St4.types)
            (n := St4.env.freshvarsc) (used := St4.env.usedVars))
          (SMT.eraseFromContext_decls (v := z)
            (decl := St4.env.declarations)))
        mrename_i erase_post
        mintro ∀St5
        mpure erase_post
        obtain ⟨⟨St5_types, St5_fresh, St5_used⟩, St5_decl⟩ := erase_post
        mspec Std.Do.Spec.pure
        mpure_intro
        have St5_types_eq : St5.types = St3.types := by
          rw [St5_types, St4_types]
          exact encodeTerm_state.erase_insert_self z_fresh
        have St5_used_chain : St5.env.usedVars = z :: St3.env.usedVars := by
          rw [St5_used, St4_used]
        refine encodeTermRepPost_of_state_and_semantic ?_ ?_
        · refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · rw [St5_used_chain]
            intro v hv
            exact List.mem_cons_of_mem _ (P_used_sub (by
              rw [St2_used_eq]
              exact D_used_sub hv))
          · rw [St5_types_eq]
            exact AList.subset_trans
              (AList.subset_trans D_types_sub St1_sub_St2) P_types_sub
          · rw [St5_types_eq, St5_used_chain]
            intro v hv
            exact List.mem_cons_of_mem _ (P_keys_sub hv)
          · intro v hv
            rw [St5_used_chain]
            apply List.mem_cons_of_mem
            rw [B.fv, List.mem_append] at hv
            rcases hv with hv_D | hv_P
            · apply P_used_sub
              rw [St2_used_eq]
              exact D_covers v hv_D
            · exact P_covers v (List.mem_removeAll_iff.mp hv_P).1
          · intro v v_used v_notMem_St0 v_notMem_vars
            obtain ⟨v_notMem_vars_D, v_notMem_vars_P, hv_not_vs⟩ :=
              B.Term.notMem_vars_collect.mp v_notMem_vars
            rw [St5_types_eq]
            intro v_in_St3
            have v_notMem_St1 :=
              D_preserves v v_used v_notMem_St0 v_notMem_vars_D
            have v_notMem_St2 : v ∉ St2.types := by
              rw [St2_types]
              intro h
              refine v_notMem_St1 (AList.mem_of_mem_foldl_insert' h ?_)
              intro hmem
              rw [List.mem_map] at hmem
              obtain ⟨⟨a, b⟩, hab, rfl⟩ := hmem
              exact hv_not_vs (List.of_mem_zip hab).1
            apply P_preserves v (by
              rw [St2_used_eq]
              exact D_used_sub v_used) v_notMem_St2 v_notMem_vars_P
            exact v_in_St3
        · have hbv_D_notMem_St3 : ∀ v ∈ SMT.bv Denc, v ∉ St3.types := by
            intro v hv
            have hv_not_St1 : v ∉ St1.types :=
              SMT.Typing.bv_notMem_context typ_Denc v hv
            have hv_not_used : v ∉ used := by
              rw [← St0_used_eq]
              exact D_bv_not_used v hv
            have hv_not_vs : v ∉ vs := fun hvs =>
              hv_not_used (vars_used_vs v hvs)
            have hv_not_P_vars : v ∉ P.vars := fun hP =>
              hv_not_used (vars_used_P v hP)
            have hv_not_St2 : v ∉ St2.types := by
              rw [St2_types]
              intro hmem
              apply hv_not_St1
              apply AList.mem_of_mem_foldl_insert' hmem
              intro h
              rw [List.mem_map] at h
              obtain ⟨⟨x, sigma⟩, hxs, rfl⟩ := h
              exact hv_not_vs (List.of_mem_zip hxs).1
            apply P_preserves v (by
              rw [St2_used_eq]
              exact D_bv_used v hv) hv_not_St2 hv_not_P_vars
          have typ_Denc_St3 : St3.types ⊢ˢ Denc :
              alpha'.fun (SMTType.option beta') :=
            SMT.Typing.weakening
              (AList.subset_trans St1_sub_St2 P_types_sub) typ_Denc
              hbv_D_notMem_St3
          have z_not_bv_Penc : z ∉ SMT.bv Penc := by
            intro hz
            exact z_not_used (P_bv_used z hz)
          have typ_Penc_z : St3.types.insert z alpha' ⊢ˢ Penc :
              SMTType.bool :=
            SMT.Typing.weakening
              (SMT.TypeContext.entries_subset_insert_of_notMem z_fresh)
              typ_Penc
              (SMT.Typing.bv_notMem_insert_of_fresh typ_Penc z_not_bv_Penc)
          have typ_lambda : St5.types ⊢ˢ (λˢ [z]) [alpha']
              (SMT.Term.ite
                (SMT.Term.and (SMT.Term.eq ((@ˢDenc) (.var z))
                  (SMT.Term.some (SMT.Term.the ((@ˢDenc) (.var z)))))
                (SMT.substList vs
                  ((toDestPair vs.dropLast (.var z)).concat
                    (.the ((@ˢDenc) (.var z)))) Penc))
                (SMT.Term.some (SMT.Term.the ((@ˢDenc) (.var z))))
                (none$ beta')) : alpha'.fun (SMTType.option beta') := by
            rw [St5_types_eq]
            have prefix_nemp : vs.dropLast ≠ [] := by
              intro h
              have hlen : vs.dropLast.length = 0 := by simp [h]
              rw [List.length_dropLast] at hlen
              omega
            have dropLast_lt : ∀ {i : ℕ}, i < vs.dropLast.length →
                i < vs.length - 1 := by
              intro i hi
              simpa only [List.length_dropLast] using hi
            have hprefix_from :
                alpha'.fromProdl (vs.dropLast.length - 1) = alphas' := by
              rw [alphas'_def, List.length_dropLast]
              have hsub : vs.length - 1 - 1 = vs.length - 2 := by
                omega
              rw [hsub]
            have hprefix_from_len :
                (alpha'.fromProdl (vs.dropLast.length - 1)).length =
                  vs.dropLast.length := by
              rw [hprefix_from, alphas'_len, List.length_dropLast]
            have vs_in_St3_used : ∀ v ∈ vs, v ∈ St3.env.usedVars := by
              intro v hv
              apply P_used_sub
              rw [St2_used_eq]
              exact D_used_sub (vars_used_vs v hv)
            have z_ne_vs : ∀ v ∈ vs, v ≠ z := by
              intro v hv heq
              subst z
              exact z_not_used (vs_in_St3_used v hv)
            have prefix_component : ∀ (i : ℕ) (hi : i < vs.dropLast.length),
                (xs ⟨i, by
                  have hlt := dropLast_lt hi
                  omega⟩).canonicalSMT.snd.fst =
                    alphas'[i]'(by
                      have hlt := dropLast_lt hi
                      simpa only [alphas'_len] using hlt) := by
              intro i hi
              let j : Fin vs.length := ⟨i, by
                have hlt := dropLast_lt hi
                omega⟩
              have hi_alpha : i < alphas'.length := by
                have hlt := dropLast_lt hi
                simpa only [alphas'_len] using hlt
              have hraw_i : i <
                  (tau.toSMTType.fromProdl (vs.length - 1)).length := by
                rw [← hraw_types]
                simp only [List.length_concat]
                rw [alphas'_len]
                have hlt := dropLast_lt hi
                omega
              have hconcat_i : i < (alphas'.concat beta').length := by
                simp only [List.length_concat]
                rw [alphas'_len]
                have hlt := dropLast_lt hi
                omega
              have hraw_i_eq :
                  (tau.toSMTType.fromProdl (vs.length - 1))[i]'hraw_i =
                    (alphas'.concat beta')[i]'hconcat_i := by
                have hopt := congrArg (fun l : List SMTType => l[i]?)
                  hraw_types.symm
                simpa only [List.getElem?_eq_getElem hraw_i,
                  List.getElem?_eq_getElem hconcat_i, Option.some.injEq] using hopt
              have hget := toSMTType_get_eq_fromProdl_getElem
                tau_hasArity j.isLt
              calc
                (xs j).canonicalSMT.snd.fst =
                    (tau.get vs.length j).toSMTType := by
                      exact B.Dom.canonicalSMT_type _
                _ = (tau.toSMTType.fromProdl (vs.length - 1))[i]'hraw_i := by
                      simpa [j] using hget
                _ = (alphas'.concat beta')[i]'hconcat_i := hraw_i_eq
                _ = alphas'[i]'hi_alpha := by
                      have hconcat_i' : i < (alphas' ++ [beta']).length := by
                        simpa only [List.concat_eq_append] using hconcat_i
                      simpa only [List.concat_eq_append] using
                        (List.getElem_append_left (as := alphas') (bs := [beta']) hi_alpha :
                          (alphas' ++ [beta'])[i]'hconcat_i' = alphas'[i]'hi_alpha)
            have prefix_lookup : ∀ (i : ℕ) (hi : i < vs.dropLast.length),
                (St3.types.insert z alpha').lookup (vs.dropLast[i]'hi) =
                  some (alphas'[i]'(by
                    have hlt := dropLast_lt hi
                    simpa only [alphas'_len] using hlt)) := by
              intro i hi
              let j : Fin vs.length := ⟨i, by
                have hlt := dropLast_lt hi
                omega⟩
              have hz : (vs[i]'(j.isLt)) ≠ z := z_ne_vs (vs[i]'(j.isLt))
                (List.getElem_mem j.isLt)
              rw [List.getElem_dropLast hi, AList.lookup_insert_ne hz]
              calc
                St3.types.lookup (vs[i]'(j.isLt)) =
                    some (xs j).canonicalSMT.snd.fst :=
                  AList.lookup_of_subset P_types_sub (hbound_type j)
                _ = some (alphas'[i]'(by
                  have hlt := dropLast_lt hi
                  simpa only [alphas'_len] using hlt)) :=
                  congrArg some (prefix_component i hi)
            have last_component :
                (xs ⟨vs.length - 1, by omega⟩).canonicalSMT.snd.fst =
                  beta' := by
              let j : Fin vs.length := ⟨vs.length - 1, by omega⟩
              have hlast_raw : vs.length - 1 <
                  (tau.toSMTType.fromProdl (vs.length - 1)).length := by
                rw [← hraw_types]
                simp only [List.length_concat]
                rw [alphas'_len]
                omega
              have hlast_concat : vs.length - 1 <
                  (alphas'.concat beta').length := by
                simp only [List.length_concat]
                rw [alphas'_len]
                omega
              have hlast_eq :
                  (tau.toSMTType.fromProdl (vs.length - 1))[vs.length - 1]'hlast_raw =
                    (alphas'.concat beta')[vs.length - 1]'hlast_concat := by
                have hopt := congrArg (fun l : List SMTType => l[vs.length - 1]?)
                  hraw_types.symm
                simpa only [List.getElem?_eq_getElem hlast_raw,
                  List.getElem?_eq_getElem hlast_concat, Option.some.injEq] using hopt
              have hget := toSMTType_get_eq_fromProdl_getElem
                tau_hasArity j.isLt
              calc
                (xs j).canonicalSMT.snd.fst =
                    (tau.get vs.length j).toSMTType := by
                      exact B.Dom.canonicalSMT_type _
                _ = (tau.toSMTType.fromProdl (vs.length - 1))[vs.length - 1]'hlast_raw := by
                      simpa [j] using hget
                _ = (alphas'.concat beta')[vs.length - 1]'hlast_concat := hlast_eq
                _ = beta' := by
                      have hlast_concat' : vs.length - 1 <
                          (alphas' ++ [beta']).length := by
                        simpa only [List.concat_eq_append] using hlast_concat
                      simpa only [List.concat_eq_append] using
                        (List.getElem_concat_length (l := alphas') (a := beta')
                          alphas'_len.symm hlast_concat')
            have last_lookup :
                (St3.types.insert z alpha').lookup (vs.getLast vs_nemp) =
                  some beta' := by
              rw [List.getLast_eq_getElem vs_nemp]
              let j : Fin vs.length := ⟨vs.length - 1, by omega⟩
              have hz : vs[vs.length - 1] ≠ z := z_ne_vs _
                (List.getElem_mem j.isLt)
              rw [AList.lookup_insert_ne hz]
              calc
                St3.types.lookup vs[vs.length - 1] =
                    some (xs j).canonicalSMT.snd.fst :=
                  AList.lookup_of_subset P_types_sub (hbound_type j)
                _ = some beta' := congrArg some last_component
            have z_not_bv_Denc : z ∉ SMT.bv Denc := by
              intro hz
              apply z_not_used
              apply P_used_sub
              rw [St2_used_eq]
              exact D_bv_used z hz
            have typ_Denc_z : St3.types.insert z alpha' ⊢ˢ Denc :
                alpha'.fun (SMTType.option beta') :=
              SMT.Typing.weakening
                (SMT.TypeContext.entries_subset_insert_of_notMem z_fresh)
                typ_Denc_St3
                (SMT.Typing.bv_notMem_insert_of_fresh typ_Denc_St3
                  z_not_bv_Denc)
            have typ_z : St3.types.insert z alpha' ⊢ˢ SMT.Term.var z :
                alpha' :=
              SMT.Typing.var _ z alpha' (AList.lookup_insert St3.types)
            have typ_Dapp_z : St3.types.insert z alpha' ⊢ˢ
                ((@ˢDenc) (.var z)) : SMTType.option beta' :=
              SMT.Typing.app _ _ _ _ _ typ_Denc_z typ_z
            have typ_payload : St3.types.insert z alpha' ⊢ˢ
                SMT.Term.the ((@ˢDenc) (.var z)) : beta' :=
              SMT.Typing.the _ _ _ typ_Dapp_z
            have typ_Psub : St3.types.insert z alpha' ⊢ˢ
                SMT.substList vs
                  ((toDestPair vs.dropLast (.var z)).concat
                    (.the ((@ˢDenc) (.var z)))) Penc : SMTType.bool := by
              suffices hsubst : St3.types.insert z alpha' ⊢ˢ
                  SMT.substList (vs.dropLast ++ [vs.getLast vs_nemp])
                    ((toDestPair vs.dropLast (.var z)).concat
                      (.the ((@ˢDenc) (.var z)))) Penc : SMTType.bool by
                simpa only [List.dropLast_append_getLast] using hsubst
              apply SMT_Typing_substList_snoc_of_bv_disjoint
              · exact (toDestPair_length_gen vs.dropLast (.var z)
                  (.var z) [] prefix_nemp).symm
              · exact typ_Penc_z
              · intro q hq
                exact toDestPair_bv_nil q hq
              · intro i hi_x _hi_t hx
                have hlookup := prefix_lookup i hi_x
                have hi_alpha : i < alphas'.length := by
                  have hlt := dropLast_lt hi_x
                  simpa only [alphas'_len] using hlt
                obtain ⟨_, htyp⟩ := toDestPair_typing_gen
                  (St3.types.insert z alpha') vs.dropLast (.var z) (.var z)
                  alpha' [] [] prefix_nemp rfl typ_z hprefix_from_len rfl
                  (by simp) i (alphas'[i]'hi_alpha) (by
                    simp only [List.append_nil]
                    rw [hprefix_from]
                    exact List.getElem?_eq_getElem hi_alpha)
                simpa only [hlookup, Option.get_some] using htyp
              · intro hx
                simpa only [last_lookup, Option.get_some] using typ_payload
              · intro v hv hsub
                have hv_D : v ∈ SMT.bv Denc := by
                  simpa [SMT.bv] using hv
                have hv_P : v ∈ SMT.bv Penc :=
                  SMT_bv_substList_subset
                    (fun q hq => toDestPair_bv_nil q hq) v hsub
                have hv_used : v ∈ St2.env.usedVars := by
                  rw [St2_used_eq]
                  exact D_bv_used v hv_D
                exact P_bv_not_used v hv_P hv_used
            exact SMT_Typing_guarded_option_lambda z_fresh z_not_bv_Denc
              typ_Denc_St3 typ_Psub
          refine ⟨D_path, typ_lambda, trivial, ?_⟩
          let body : SMT.Term := SMT.Term.ite
            (SMT.Term.and (SMT.Term.eq ((@ˢDenc) (.var z))
              (SMT.Term.some (SMT.Term.the ((@ˢDenc) (.var z)))))
              (SMT.substList vs
                ((toDestPair vs.dropLast (.var z)).concat
                  (.the ((@ˢDenc) (.var z)))) Penc))
            (SMT.Term.some (SMT.Term.the ((@ˢDenc) (.var z))))
            (none$ beta')
          have body_def : body = SMT.Term.ite
              (SMT.Term.and (SMT.Term.eq ((@ˢDenc) (.var z))
                (SMT.Term.some (SMT.Term.the ((@ˢDenc) (.var z)))))
                (SMT.substList vs
                  ((toDestPair vs.dropLast (.var z)).concat
                    (.the ((@ˢDenc) (.var z)))) Penc))
              (SMT.Term.some (SMT.Term.the ((@ˢDenc) (.var z))))
              (none$ beta') := rfl
          have ThetaP0_ext : SMT.RenamingContext.Extends ThetaP0 ThetaD := by
            intro v d hv
            dsimp [ThetaP0]
            by_cases hvs : v ∈ vs
            · have hnone : ThetaD v = none := by
                cases hTheta : ThetaD v with
                | none => rfl
                | some d' =>
                    exfalso
                    exact vs_disj_St1 v hvs
                      (ThetaD_dom v (by rw [hTheta]; simp))
              rw [hnone] at hv
              cases hv
            · rw [Function.updates_of_not_mem _ _ _ _ hvs]
              exact hv
          have ThetaP_ext_D : SMT.RenamingContext.Extends ThetaP ThetaD :=
            SMT.RenamingContext.extends_trans ThetaP_ext ThetaP0_ext
          have ThetaP_ext0 : SMT.RenamingContext.Extends ThetaP Theta0 :=
            SMT.RenamingContext.extends_trans ThetaP_ext_D ThetaD_ext
          have St1_sub_St3 : St1.types ⊆ St3.types :=
            AList.subset_trans St1_sub_St2 P_types_sub
          have St0_sub_St5 : St0.types ⊆ St5.types := by
            rw [St5_types_eq]
            exact AList.subset_trans D_types_sub St1_sub_St3
          have related_out : RValuationCastSupportedOnFV Xi ThetaP
              (B.Term.collect vs D P) :=
            related_collect_out.of_extends ThetaP_ext_D
          have respects_collect_out :
              B.RenamingContext.RespectsTypeContextOnFV ThetaP St5.types
                (B.Term.collect vs D P) := by
            apply B.RenamingContext.RespectsTypeContextOnFV.of_extends respects
              ThetaP_ext0 St0_sub_St5
            · intro v hv
              exact hv
            · exact fv_in_Lambda
          have ThetaP_none_out : ∀ v ∉ St5.env.usedVars, ThetaP v = none := by
            intro v hv
            apply ThetaP_none v
            rw [St5_used_chain] at hv
            simp only [List.mem_cons, not_or] at hv
            exact hv.2
          have ThetaP_dom_out : ∀ v, ThetaP v ≠ none → v ∈ St5.types := by
            intro v hv
            rw [St5_types_eq]
            exact ThetaP_dom v hv
          have hD_fv_not_vs : ∀ v ∈ SMT.fv Denc, v ∉ vs := by
            intro v hv hvs
            exact vs_disj_St1 v hvs
              (SMT.Typing.mem_context_of_mem_fv typ_Denc hv)
          have hcov_D_ThetaP0 : SMT.RenamingContext.CoversFV ThetaP0 Denc := by
            intro v hv
            dsimp [ThetaP0]
            rw [Function.updates_of_not_mem _ _ _ _ (hD_fv_not_vs v hv)]
            exact hcov_Denc v hv
          have hcov_D_ThetaP : SMT.RenamingContext.CoversFV ThetaP Denc := by
            intro v hv
            obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (hcov_D_ThetaP0 v hv)
            exact Option.isSome_of_eq_some (ThetaP_ext hd)
          have hagree_D : SMT.RenamingContext.AgreesOnFV ThetaD ThetaP Denc := by
            intro v hv
            obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (hcov_Denc v hv)
            have h0 : ThetaP0 v = some d := by
              dsimp [ThetaP0]
              rw [Function.updates_of_not_mem _ _ _ _ (hD_fv_not_vs v hv)]
              exact hd
            exact hd.trans (ThetaP_ext h0).symm
          have hden_D_ThetaP_eq :
              ⟦Denc.abstract ThetaP hcov_D_ThetaP⟧ˢ =
                ⟦Denc.abstract ThetaD hcov_Denc⟧ˢ := by
            change SMT.RenamingContext.denote ThetaP Denc hcov_D_ThetaP =
              SMT.RenamingContext.denote ThetaD Denc hcov_Denc
            exact (SMT.RenamingContext.denote_congr_of_agreesOnFV
              (h1 := hcov_Denc) (h2 := hcov_D_ThetaP) hagree_D).symm
          have z_not_fv_Denc : z ∉ SMT.fv Denc := by
            intro hz
            exact z_fresh (SMT.Typing.mem_context_of_mem_fv typ_Denc_St3 hz)
          have hcov_D_upd : ∀ W : SMT.Dom,
              SMT.RenamingContext.CoversFV
                (Function.update ThetaP z (some W)) Denc := by
            intro W
            exact SMT.RenamingContext.coversFV_update_of_notMem
              z_not_fv_Denc hcov_D_ThetaP
          have hden_D_upd_eq : ∀ W : SMT.Dom,
              ⟦Denc.abstract (Function.update ThetaP z (some W))
                (hcov_D_upd W)⟧ˢ =
                ⟦Denc.abstract ThetaP hcov_D_ThetaP⟧ˢ := by
            intro W
            change SMT.RenamingContext.denote (Function.update ThetaP z (some W))
              Denc (hcov_D_upd W) =
                SMT.RenamingContext.denote ThetaP Denc hcov_D_ThetaP
            exact (SMT.RenamingContext.denote_update_of_notMem
              (h := hcov_D_ThetaP) z_not_fv_Denc).symm
          have hDenc_func : ⟦alpha'⟧ᶻ.IsFunc ⟦SMTType.option beta'⟧ᶻ DencZF := by
            have hmem := hDencMem
            rw [SMTType.toZFSet] at hmem
            exact ZFSet.mem_funs.mp hmem
          have target_respects_D_ThetaP :
              SMT.RenamingContext.RespectsTypeContextOnFV ThetaP St3.types Denc :=
            SMT.RenamingContext.RespectsTypeContextOnFV.of_extends
              target_respects_D ThetaP_ext_D St1_sub_St3 typ_Denc
          have hcov_lambda : SMT.RenamingContext.CoversFV ThetaP
              ((λˢ [z]) [alpha'] body) := by
            simpa [body] using
              (SMT.RenamingContext.covers_collectOption_lambda
                (D := Denc) (P := Penc) (z := z) (vs := vs)
                (alpha := alpha') (beta := beta') hcov_D_ThetaP hcov_Penc)
          have target_respects_lambda :
              SMT.RenamingContext.RespectsTypeContextOnFV ThetaP St3.types
                ((λˢ [z]) [alpha'] body) := by
            intro v sigma hv hlookup
            have hv' : v ∈ SMT.fv Denc ∪ SMT.fv Penc := by
              simpa [body] using
                (collectOption_lambda_fv Denc Penc z vs alpha' beta' hv)
            rw [List.mem_union_iff] at hv'
            rcases hv' with hv_D | hv_P
            · exact target_respects_D_ThetaP hv_D hlookup
            · exact target_respects_P hv_P hlookup
          obtain ⟨_, hlen_z, gamma, _, _, _, typ_body_update⟩ :=
            SMT.Typing.lambdaE typ_lambda
          have hupdate_z : St5.types.update [z] [alpha'] hlen_z =
              St3.types.insert z alpha' := by
            rw [St5_types_eq]
            simp only [SMT.TypeContext.update, List.length_cons, List.length_nil,
              zero_add, Nat.reduceAdd, Fin.cast_eq_self, Fin.getElem_fin,
              Fin.val_eq_zero, List.getElem_cons_zero, Fin.foldl_succ,
              Fin.foldl_zero]
          have typ_body : St3.types.insert z alpha' ⊢ˢ body : gamma := by
            rw [hupdate_z] at typ_body_update
            simpa [body] using typ_body_update
          have hcov_body_upd : ∀ W : SMT.Dom,
              SMT.RenamingContext.CoversFV
                (Function.update ThetaP z (some W)) body := by
            intro W
            simpa [body] using
              (SMT.RenamingContext.covers_collectOption_body_update
                (D := Denc) (P := Penc) (z := z) (vs := vs)
                (alpha := alpha') (beta := beta') hcov_D_ThetaP hcov_Penc)
          have respects_body_upd : ∀ W : SMT.Dom, W.snd.fst = alpha' →
              SMT.RenamingContext.RespectsTypeContextOnFV
                (Function.update ThetaP z (some W))
                (St3.types.insert z alpha') body := by
            intro W hW
            intro v sigma hv hlookup
            by_cases hvz : v = z
            · subst v
              rw [AList.lookup_insert] at hlookup
              cases hlookup
              exact ⟨W, by simp, hW⟩
            · rw [Function.update_of_ne hvz]
              rw [AList.lookup_insert_ne hvz] at hlookup
              apply target_respects_lambda
              · simp only [SMT.fv, List.mem_removeAll_iff]
                constructor
                · simpa [body] using hv
                · exact List.mem_singleton.not.mpr hvz
              · exact hlookup
          have hbody_total : ∀ W : SMT.Dom, W.snd.fst = alpha' →
              ∃ bodyVal : SMT.Dom,
                ⟦body.abstract (Function.update ThetaP z (some W))
                  (hcov_body_upd W)⟧ˢ = some bodyVal := by
            intro W hW
            obtain ⟨bodyVal, hden, _⟩ :=
              SMT.RenamingContext.denote_exists_of_typing_fv typ_body
                (respects_body_upd W hW) (hcov_body_upd W)
            exact ⟨bodyVal, hden⟩
          have vs_in_St3_used : ∀ v ∈ vs, v ∈ St3.env.usedVars := by
            intro v hv
            apply P_used_sub
            rw [St2_used_eq]
            exact D_used_sub (vars_used_vs v hv)
          have z_not_vs : z ∉ vs := by
            intro hz
            exact z_not_used (vs_in_St3_used z hz)
          have hvs_not_bv : ∀ v ∈ vs, v ∉ SMT.bv Penc := by
            intro v hv hbv
            apply P_bv_not_used v hbv
            rw [St2_used_eq]
            exact D_used_sub (vars_used_vs v hv)
          have hDapp_fv_not_bv : ∀ w ∈ SMT.fv ((@ˢDenc) (.var z)),
              w ∉ SMT.bv Penc := by
            intro w hw hPbv
            simp only [SMT.fv, List.mem_append, List.mem_singleton] at hw
            rcases hw with hw | rfl
            · apply P_bv_not_used w hPbv
              rw [St2_used_eq]
              exact D_keys_sub (AList.mem_keys.mpr
                (SMT.Typing.mem_context_of_mem_fv typ_Denc hw))
            · exact z_not_used (P_bv_used w hPbv)
          have hDapp_fv_disj_vs : ∀ w ∈ SMT.fv ((@ˢDenc) (.var z)),
              w ∉ vs := by
            intro w hw hvs
            simp only [SMT.fv, List.mem_append, List.mem_singleton] at hw
            rcases hw with hw | rfl
            · exact vs_disj_St1 w hvs
                (SMT.Typing.mem_context_of_mem_fv typ_Denc hw)
            · exact z_not_vs hvs
          have z_not_fv_Penc : z ∉ SMT.fv Penc := by
            intro hz
            exact z_fresh (SMT.Typing.mem_context_of_mem_fv typ_Penc hz)
          have hcov_P_upd : ∀ (W : SMT.Dom) (ss : Fin vs.length → SMT.Dom),
              SMT.RenamingContext.CoversFV
                (Function.updates (Function.update ThetaP z (some W)) vs
                  ((List.ofFn ss).map Option.some)) Penc := by
            intro W ss v hv
            by_cases hvs : v ∈ vs
            · rw [Function.updates_eq_if
                (by rw [List.length_map, List.length_ofFn]) vs_nodup,
                dif_pos hvs]
              simp
            · rw [Function.updates_of_not_mem _ vs _ _ hvs,
                Function.update_of_ne (by
                  intro heq
                  exact z_not_fv_Penc (heq ▸ hv))]
              exact hcov_Penc v hv
          have hcov_sub_upd : ∀ W : SMT.Dom,
              SMT.RenamingContext.CoversFV
                (Function.update ThetaP z (some W))
                (SMT.substList vs
                  ((toDestPair vs.dropLast (.var z)).concat
                    (.the ((@ˢDenc) (.var z)))) Penc) := by
            intro W v hv
            apply hcov_body_upd W v
            rw [body_def]
            apply SMT.fv.mem_ite
            exact Or.inl (SMT.fv.mem_and (.inr hv))
          have prefix_nemp_out : vs.dropLast ≠ [] := by
            intro h
            have hlen : vs.dropLast.length = 0 := by simp [h]
            rw [List.length_dropLast] at hlen
            omega
          have hprod_arity_ab : (a ×ᴮ b).hasArity vs.length := by
            simpa only [htau] using tau_hasArity
          have hDval_ab : Dval ∈ ⟦BType.set (a ×ᴮ b)⟧ᶻ := by
            rw [← htau]
            exact hDval
          have den_D_ab :
              ⟦D.abstract Xi
                (fun v hv => Xi_fv v (B.fv.mem_collect (.inl hv)))⟧ᴮ =
                some (⟨Dval, BType.set (a ×ᴮ b), hDval_ab⟩ : B.Dom) := by
            simpa only [htau, proof_irrel_heq] using den_D
          have hT_ab : T ∈ ⟦BType.set (a ×ᴮ b)⟧ᶻ := by
            rw [← htau]
            exact hT
          have den_collect_ab :
              ⟦(B.Term.collect vs D P).abstract Xi Xi_fv⟧ᴮ =
                some (⟨T, BType.set (a ×ᴮ b), hT_ab⟩ : B.Dom) := by
            simpa only [tau, htau, proof_irrel_heq] using den_t
          have bound_expected : ∀ i : Fin vs.length,
              St3.types.lookup vs[i] =
                some (((a ×ᴮ b).get vs.length i).toSMTType) := by
            intro i
            calc
              St3.types.lookup vs[i] =
                  some (xs i).canonicalSMT.snd.fst :=
                AList.lookup_of_subset P_types_sub (hbound_type i)
              _ = some (((a ×ᴮ b).get vs.length i).toSMTType) := by
                apply congrArg some
                rw [B.Dom.canonicalSMT_type]
                dsimp [xs]
                rw [htau]
          have source_respects_upd : ∀ ss : Fin vs.length → SMT.Dom,
              (∀ i, St3.types.lookup vs[i] = some (ss i).snd.fst) →
              B.RenamingContext.RespectsTypeContextOnFV
                (Function.updates ThetaP vs
                  ((List.ofFn ss).map Option.some)) St3.types P := by
            intro ss hss
            apply B.RenamingContext.RespectsTypeContextOnFV.updates_of_typed_bounds
              vs_nodup
            · intro v hv hvs sigma hlookup
              exact respects_P_out hv hlookup
            · exact hss
          have target_respects_upd : ∀ ss : Fin vs.length → SMT.Dom,
              (∀ i, St3.types.lookup vs[i] = some (ss i).snd.fst) →
              SMT.RenamingContext.RespectsTypeContextOnFV
                (Function.updates ThetaP vs
                  ((List.ofFn ss).map Option.some)) St3.types Penc := by
            intro ss hss v sigma hv hlookup
            by_cases hvs : v ∈ vs
            · let i : Fin vs.length :=
                ⟨vs.idxOf v, List.idxOf_lt_length_of_mem hvs⟩
              have hvi : vs[i] = v := List.getElem_idxOf i.isLt
              refine ⟨ss i, ?_, ?_⟩
              · rw [Function.updates_eq_if (by simp) vs_nodup,
                  dif_pos hvs]
                simp only [List.getElem_map, List.getElem_ofFn]
                congr 1
              · have hbound := hss i
                rw [hvi] at hbound
                exact Option.some.inj (hbound.symm.trans hlookup)
            · obtain ⟨d, hd, htype⟩ := target_respects_P hv hlookup
              refine ⟨d, ?_, htype⟩
              rw [Function.updates_of_not_mem ThetaP vs _ v hvs]
              exact hd
          have specs_true_upd : ∀ ss : Fin vs.length → SMT.Dom,
              (∀ i, St3.types.lookup vs[i] = some (ss i).snd.fst) →
              SpecBodiesTrue
                (Function.updates ThetaP vs
                  ((List.ofFn ss).map Option.some)) St3.types [] := by
            intro ss hss
            simp [SpecBodiesTrue, specBodies]
          have ambient_P : ∀ v ∈ B.fv P, v ∉ vs →
              match Xi v, ThetaP v with
              | some d, some d' => RDomCastSupported d d'
              | _, _ => False := by
            intro v hv hvs
            exact related_out v (B.fv.mem_collect (.inr ⟨hv, hvs⟩))
          have wf_bound : ∀ (x y : ZFSet.{u}) (hx : x ∈ ⟦a⟧ᶻ)
              (hy : y ∈ ⟦b⟧ᶻ),
              B.RenWF Ebody.context
                (Function.updates Xi vs (List.ofFn fun i => some
                  (⟨(x.pair y).get vs.length i,
                    (a ×ᴮ b).get vs.length i,
                    get_mem_type_of_isTuple
                      (hasArity_of_mem_toZFSet hprod_arity_ab
                        (ZFSet.pair_mem_prod.mpr ⟨hx, hy⟩))
                      hprod_arity_ab (ZFSet.pair_mem_prod.mpr ⟨hx, hy⟩)⟩ :
                        B.Dom))) := by
            intro x y hx hy
            apply B.RenWF.updates_ofFn wf vs_nodup vs_context_disj
              vs_alphas_len
            intro i
            change (a ×ᴮ b).get vs.length i =
              alphas[Fin.cast vs_alphas_len i]
            rw [← htau]
            exact BType.get_reduce alphas_nemp vs_alphas_len i
          have P_scope : ScopedContextExtends St2.types [] St3.types :=
            P_trace.scoped_extends
          have target_respects_lambda_out :
              SMT.RenamingContext.RespectsTypeContextOnFV ThetaP St5.types
                ((λˢ [z]) [alpha'] body) := by
            rw [St5_types_eq]
            exact target_respects_lambda
          obtain ⟨lamVal, hden_lambda, hlam_type⟩ :=
            SMT.RenamingContext.denote_exists_of_typing_fv typ_lambda
              target_respects_lambda_out hcov_lambda
          refine ⟨ThetaP, hcov_lambda, ThetaP_ext0, related_out,
            ThetaP_none_out, respects_collect_out, target_respects_lambda_out,
            ThetaP_dom_out, lamVal, hden_lambda, hlam_type, ?_, ?_⟩
          · have hrel_ab := represented_collect_option_lambda
              (D := D) (P := P) (alpha := a) (beta := b)
              (Xi := Xi) (Dval := Dval) (hDval := hDval_ab)
              (T := T) (hT := hT_ab) (Denc := Denc) (Penc := Penc)
              (body := body) (z := z) (ThetaD := ThetaP)
              (DencVal := (⟨DencZF, alpha'.fun (SMTType.option beta'),
                hDencMem⟩ : SMT.Dom)) (lamVal := lamVal)
              (Ebody := Ebody) (LambdaP := St2.types) (GammaP := St3.types)
              (DltP := []) (sigmaP := SMTType.bool)
              vs_nemp prefix_nemp_out vs_nodup Xi_fv hprod_arity_ab
              vs_len_ge_two den_D_ab den_collect_ab
              (by simpa only [hbeta] using body_def)
              (by simpa only [halpha, proof_irrel_heq] using hcov_lambda)
              (by simpa only [halpha, proof_irrel_heq] using hden_lambda)
              (by simpa only [halpha, hbeta] using hlam_type)
              (by simpa only [proof_irrel_heq] using hcov_D_upd)
              (by
                intro W
                rw [hden_D_upd_eq W, hden_D_ThetaP_eq]
                exact hden_Denc)
              (by simpa only [halpha, hbeta] using hDenc_type)
              (by simpa only [halpha, hbeta] using hDenc_func)
              (by simpa only [htau, halpha, hbeta, proof_irrel_heq] using D_rel)
              (by simpa only [hbeta, proof_irrel_heq] using hcov_body_upd)
              (by simpa only [halpha, hbeta, proof_irrel_heq] using hbody_total)
              hDapp_fv_not_bv hDapp_fv_disj_vs hvs_not_bv
              (by
                intro hz
                exact z_not_used (P_bv_used z hz))
              z_not_vs hcov_sub_upd hcov_P_upd
              typ_P_body P_guard P_scope typ_Penc rfl ambient_P wf_bound
              bound_expected source_respects_upd target_respects_upd
              specs_true_upd z_not_fv_Penc
            simpa only [tau, htau, proof_irrel_heq] using hrel_ab
          · intro Xi_alt Xi_fv_alt Theta0_alt related_alt wf_alt
              Theta0_alt_none respects_alt Theta0_alt_dom
              T_alt hT_alt den_alt
            have Xi_fv_D_alt : ∀ v ∈ B.fv D,
                (Xi_alt v).isSome = true :=
              fun v hv => Xi_fv_alt v (B.fv.mem_collect (.inl hv))
            have related_D_alt : RValuationCastSupportedOnFV
                Xi_alt Theta0_alt D :=
              related_alt.mono_fv (fun _ hv => B.fv.mem_collect (.inl hv))
            have respects_D_alt :
                B.RenamingContext.RespectsTypeContextOnFV
                  Theta0_alt St0.types D :=
              respects_alt.mono_fv (fun _ hv => B.fv.mem_collect (.inl hv))
            obtain ⟨Dval_alt, hDval_alt, den_D_alt⟩ :=
              B.denote_collect_domain_exists Xi_fv_alt typ_D wf_alt den_alt
            have Theta0_alt_none_D : ∀ v ∉ St1.env.usedVars,
                Theta0_alt v = none := by
              intro v hv
              by_contra hne
              have hv_St0 : v ∈ St0.types := Theta0_alt_dom v hne
              have hv_used : v ∈ used := by
                rw [← St0_used_eq]
                exact St0_sub hv_St0
              exact hv (D_used_sub hv_used)
            obtain ⟨ThetaD_alt, hcov_D_alt, DencVal_alt,
                ThetaD_alt_ext, related_D_alt_out, ThetaD_alt_none,
                respects_D_alt_out, target_respects_D_alt, ThetaD_alt_dom,
                hden_Denc_alt, hDenc_type_alt, D_rel_alt⟩ :=
              D_total Xi_alt Xi_fv_D_alt Theta0_alt related_D_alt wf_alt
                Theta0_alt_none_D respects_D_alt Theta0_alt_dom
                Dval_alt hDval_alt den_D_alt
            let XiP_alt : B.RenamingContext.Context :=
              Function.updates Xi_alt vs
                (List.ofFn fun i => some (xs i))
            let ThetaP0_alt : SMT.RenamingContext.Context :=
              Function.updates ThetaD_alt vs
                ((List.ofFn fun i => (xs i).canonicalSMT).map Option.some)
            have wf_P_alt : B.RenWF Ebody.context XiP_alt := by
              dsimp [XiP_alt]
              exact B.RenWF.updates_ofFn wf_alt vs_nodup vs_context_disj
                vs_alphas_len xs_type
            obtain ⟨XiP_fv_alt, Pval_alt, hPval_alt, den_P_alt⟩ :=
              B.denote_collect_default_predicate_exists Xi_fv_alt vs_nemp
                vs_nodup tau_hasArity den_D_alt den_alt typ_P_body wf_P_alt
            have related_collect_D_alt :
                RValuationCastSupportedOnFV Xi_alt ThetaD_alt
                  (B.Term.collect vs D P) :=
              related_alt.of_extends ThetaD_alt_ext
            have related_P_alt : RValuationCastSupportedOnFV
                XiP_alt ThetaP0_alt P := by
              dsimp [XiP_alt, ThetaP0_alt]
              rw [hThetaP0_map]
              apply RValuationCastSupportedOnFV.updates_of_collect_default
                vs_nodup tau_hasArity
              intro v hv hv_not_vs
              exact related_collect_D_alt v
                (B.fv.mem_collect (.inr ⟨hv, hv_not_vs⟩))
            have ThetaP0_alt_none_St2 : ∀ v ∉ St2.env.usedVars,
                ThetaP0_alt v = none := by
              intro v hv
              dsimp [ThetaP0_alt]
              apply SMT.RenamingContext.updates_none_of_mem_used
                (fun w hw => by
                  rw [St2_used_eq]
                  exact D_used_sub (vars_used_vs w hw))
                (fun w hw => ThetaD_alt_none w (by
                  rw [← St2_used_eq]
                  exact hw)) v hv
            have ThetaP0_alt_none : ∀ v ∉ St3.env.usedVars,
                ThetaP0_alt v = none := by
              intro v hv
              apply ThetaP0_alt_none_St2 v
              intro hv_St2
              exact hv (P_used_sub hv_St2)
            have ThetaP0_alt_dom : ∀ v, ThetaP0_alt v ≠ none →
                v ∈ St2.types := by
              dsimp [ThetaP0_alt]
              exact SMT.RenamingContext.updates_dom_of_typed_bounds
                (fun v hv =>
                  AList.mem_of_subset St1_sub_St2 (ThetaD_alt_dom v hv))
                hbound_type
            have respects_P_alt :
                B.RenamingContext.RespectsTypeContextOnFV
                  ThetaP0_alt St2.types P := by
              dsimp [ThetaP0_alt]
              apply B.RenamingContext.RespectsTypeContextOnFV.updates_of_typed_bounds
                vs_nodup
              · intro v hv hv_not_vs sigma hlookup
                have hv_collect : v ∈ B.fv (B.Term.collect vs D P) :=
                  B.fv.mem_collect (.inr ⟨hv, hv_not_vs⟩)
                have hv_St0 : v ∈ St0.types :=
                  fv_in_Lambda v hv_collect
                obtain ⟨sigma0, hsigma0⟩ := Option.isSome_iff_exists.mp
                  (AList.lookup_isSome.mpr hv_St0)
                have hsigma1 : St1.types.lookup v = some sigma0 :=
                  AList.lookup_of_subset D_types_sub hsigma0
                have hsigma2 : St2.types.lookup v = some sigma0 := by
                  rw [St2_types]
                  apply foldl_insert_preserves_lookup hsigma1
                  intro p hp hpv
                  apply hv_not_vs
                  rw [← hpv]
                  exact (List.of_mem_zip hp).1
                rw [hsigma2] at hlookup
                cases hlookup
                obtain ⟨d, hd, hdty⟩ := respects_alt hv_collect hsigma0
                exact ⟨d, ThetaD_alt_ext hd, hdty⟩
              · exact hbound_type
            obtain ⟨ThetaP_alt, hcov_P_alt, PencVal_alt,
                ThetaP_alt_ext, related_P_alt_out, ThetaP_alt_none,
                respects_P_alt_out, target_respects_P_alt, ThetaP_alt_dom,
                hden_Penc_alt, hPenc_type_alt, P_rel_alt⟩ :=
              P_total XiP_alt XiP_fv_alt ThetaP0_alt related_P_alt wf_P_alt
                ThetaP0_alt_none respects_P_alt ThetaP0_alt_dom
                Pval_alt hPval_alt den_P_alt
            have ThetaP0_alt_ext : SMT.RenamingContext.Extends
                ThetaP0_alt ThetaD_alt := by
              intro v d hv
              dsimp [ThetaP0_alt]
              by_cases hvs : v ∈ vs
              · have hnone : ThetaD_alt v = none := by
                  cases hTheta : ThetaD_alt v with
                  | none => rfl
                  | some d' =>
                      exfalso
                      exact vs_disj_St1 v hvs
                        (ThetaD_alt_dom v (by rw [hTheta]; simp))
                rw [hnone] at hv
                cases hv
              · rw [Function.updates_of_not_mem _ _ _ _ hvs]
                exact hv
            have ThetaP_alt_ext_D : SMT.RenamingContext.Extends
                ThetaP_alt ThetaD_alt :=
              SMT.RenamingContext.extends_trans ThetaP_alt_ext ThetaP0_alt_ext
            have ThetaP_alt_ext0 : SMT.RenamingContext.Extends
                ThetaP_alt Theta0_alt :=
              SMT.RenamingContext.extends_trans ThetaP_alt_ext_D ThetaD_alt_ext
            have related_out_alt : RValuationCastSupportedOnFV
                Xi_alt ThetaP_alt (B.Term.collect vs D P) :=
              related_alt.of_extends ThetaP_alt_ext0
            have respects_collect_alt :
                B.RenamingContext.RespectsTypeContextOnFV
                  ThetaP_alt St5.types (B.Term.collect vs D P) := by
              apply B.RenamingContext.RespectsTypeContextOnFV.of_extends
                respects_alt ThetaP_alt_ext0 St0_sub_St5
              · intro v hv
                exact hv
              · exact fv_in_Lambda
            have ThetaP_alt_none_out : ∀ v ∉ St5.env.usedVars,
                ThetaP_alt v = none := by
              intro v hv
              apply ThetaP_alt_none v
              rw [St5_used_chain] at hv
              simp only [List.mem_cons, not_or] at hv
              exact hv.2
            have ThetaP_alt_dom_out : ∀ v, ThetaP_alt v ≠ none →
                v ∈ St5.types := by
              intro v hv
              rw [St5_types_eq]
              exact ThetaP_alt_dom v hv
            have hcov_D_ThetaP_alt :
                SMT.RenamingContext.CoversFV ThetaP_alt Denc := by
              intro v hv
              obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (hcov_D_alt v hv)
              exact Option.isSome_of_eq_some (ThetaP_alt_ext_D hd)
            have hagree_D_alt : SMT.RenamingContext.AgreesOnFV
                ThetaD_alt ThetaP_alt Denc := by
              intro v hv
              obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (hcov_D_alt v hv)
              exact hd.trans (ThetaP_alt_ext_D hd).symm
            have hden_D_ThetaP_alt_eq :
                ⟦Denc.abstract ThetaP_alt hcov_D_ThetaP_alt⟧ˢ =
                  ⟦Denc.abstract ThetaD_alt hcov_D_alt⟧ˢ := by
              change SMT.RenamingContext.denote ThetaP_alt Denc
                  hcov_D_ThetaP_alt =
                SMT.RenamingContext.denote ThetaD_alt Denc hcov_D_alt
              exact (SMT.RenamingContext.denote_congr_of_agreesOnFV
                (h1 := hcov_D_alt) (h2 := hcov_D_ThetaP_alt)
                hagree_D_alt).symm
            have hcov_D_upd_alt : ∀ W : SMT.Dom,
                SMT.RenamingContext.CoversFV
                  (Function.update ThetaP_alt z (some W)) Denc := by
              intro W
              exact SMT.RenamingContext.coversFV_update_of_notMem
                z_not_fv_Denc hcov_D_ThetaP_alt
            have hden_D_upd_alt : ∀ W : SMT.Dom,
                ⟦Denc.abstract (Function.update ThetaP_alt z (some W))
                  (hcov_D_upd_alt W)⟧ˢ = some DencVal_alt := by
              intro W
              calc
                ⟦Denc.abstract (Function.update ThetaP_alt z (some W))
                    (hcov_D_upd_alt W)⟧ˢ =
                    ⟦Denc.abstract ThetaP_alt hcov_D_ThetaP_alt⟧ˢ := by
                  change SMT.RenamingContext.denote
                      (Function.update ThetaP_alt z (some W)) Denc
                        (hcov_D_upd_alt W) =
                    SMT.RenamingContext.denote ThetaP_alt Denc
                      hcov_D_ThetaP_alt
                  exact (SMT.RenamingContext.denote_update_of_notMem
                    (h := hcov_D_ThetaP_alt) z_not_fv_Denc).symm
                _ = ⟦Denc.abstract ThetaD_alt hcov_D_alt⟧ˢ :=
                  hden_D_ThetaP_alt_eq
                _ = some DencVal_alt := hden_Denc_alt
            have target_respects_D_ThetaP_alt :
                SMT.RenamingContext.RespectsTypeContextOnFV
                  ThetaP_alt St3.types Denc :=
              SMT.RenamingContext.RespectsTypeContextOnFV.of_extends
                target_respects_D_alt ThetaP_alt_ext_D St1_sub_St3 typ_Denc
            have hcov_lambda_alt : SMT.RenamingContext.CoversFV ThetaP_alt
                ((λˢ [z]) [alpha'] body) := by
              simpa [body] using
                (SMT.RenamingContext.covers_collectOption_lambda
                  (D := Denc) (P := Penc) (z := z) (vs := vs)
                  (alpha := alpha') (beta := beta') hcov_D_ThetaP_alt hcov_P_alt)
            have target_respects_lambda_alt :
                SMT.RenamingContext.RespectsTypeContextOnFV
                  ThetaP_alt St3.types ((λˢ [z]) [alpha'] body) := by
              intro v sigma hv hlookup
              have hv' : v ∈ SMT.fv Denc ∪ SMT.fv Penc := by
                simpa [body] using
                  (collectOption_lambda_fv Denc Penc z vs alpha' beta' hv)
              rw [List.mem_union_iff] at hv'
              rcases hv' with hv_D | hv_P
              · exact target_respects_D_ThetaP_alt hv_D hlookup
              · exact target_respects_P_alt hv_P hlookup
            have target_respects_lambda_out_alt :
                SMT.RenamingContext.RespectsTypeContextOnFV
                  ThetaP_alt St5.types ((λˢ [z]) [alpha'] body) := by
              rw [St5_types_eq]
              exact target_respects_lambda_alt
            obtain ⟨lamVal_alt, hden_lambda_alt, hlam_type_alt⟩ :=
              SMT.RenamingContext.denote_exists_of_typing_fv typ_lambda
                target_respects_lambda_out_alt hcov_lambda_alt
            have hDenc_type_alt' : DencVal_alt.snd.fst =
                alpha'.fun (SMTType.option beta') := by
              simpa using hDenc_type_alt
            have hDenc_func_alt : ⟦alpha'⟧ᶻ.IsFunc
                ⟦SMTType.option beta'⟧ᶻ DencVal_alt.fst := by
              have hmem : DencVal_alt.fst ∈
                  ⟦alpha'.fun (SMTType.option beta')⟧ᶻ := by
                rw [← hDenc_type_alt']
                exact DencVal_alt.snd.snd
              rw [SMTType.toZFSet] at hmem
              exact ZFSet.mem_funs.mp hmem
            have hcov_body_upd_alt : ∀ W : SMT.Dom,
                SMT.RenamingContext.CoversFV
                  (Function.update ThetaP_alt z (some W)) body := by
              intro W
              simpa [body] using
                (SMT.RenamingContext.covers_collectOption_body_update
                  (D := Denc) (P := Penc) (z := z) (vs := vs)
                  (alpha := alpha') (beta := beta')
                  hcov_D_ThetaP_alt hcov_P_alt)
            have respects_body_upd_alt : ∀ W : SMT.Dom,
                W.snd.fst = alpha' →
                SMT.RenamingContext.RespectsTypeContextOnFV
                  (Function.update ThetaP_alt z (some W))
                  (St3.types.insert z alpha') body := by
              intro W hW
              intro v sigma hv hlookup
              by_cases hvz : v = z
              · subst v
                rw [AList.lookup_insert] at hlookup
                cases hlookup
                exact ⟨W, by simp, hW⟩
              · rw [Function.update_of_ne hvz]
                rw [AList.lookup_insert_ne hvz] at hlookup
                apply target_respects_lambda_alt
                · simp only [SMT.fv, List.mem_removeAll_iff]
                  constructor
                  · simpa [body] using hv
                  · exact List.mem_singleton.not.mpr hvz
                · exact hlookup
            have hbody_total_alt : ∀ W : SMT.Dom,
                W.snd.fst = alpha' →
                ∃ bodyVal : SMT.Dom,
                  ⟦body.abstract (Function.update ThetaP_alt z (some W))
                    (hcov_body_upd_alt W)⟧ˢ = some bodyVal := by
              intro W hW
              obtain ⟨bodyVal, hden, _⟩ :=
                SMT.RenamingContext.denote_exists_of_typing_fv typ_body
                  (respects_body_upd_alt W hW) (hcov_body_upd_alt W)
              exact ⟨bodyVal, hden⟩
            have hcov_P_upd_alt : ∀ (W : SMT.Dom)
                (ss : Fin vs.length → SMT.Dom),
                SMT.RenamingContext.CoversFV
                  (Function.updates (Function.update ThetaP_alt z (some W)) vs
                    ((List.ofFn ss).map Option.some)) Penc := by
              intro W ss v hv
              by_cases hvs : v ∈ vs
              · rw [Function.updates_eq_if
                    (by rw [List.length_map, List.length_ofFn]) vs_nodup,
                  dif_pos hvs]
                simp
              · rw [Function.updates_of_not_mem _ vs _ _ hvs,
                  Function.update_of_ne (by
                    intro heq
                    exact z_not_fv_Penc (heq ▸ hv))]
                exact hcov_P_alt v hv
            have hcov_sub_upd_alt : ∀ W : SMT.Dom,
                SMT.RenamingContext.CoversFV
                  (Function.update ThetaP_alt z (some W))
                  (SMT.substList vs
                    ((toDestPair vs.dropLast (.var z)).concat
                      (.the ((@ˢDenc) (.var z)))) Penc) := by
              intro W v hv
              apply hcov_body_upd_alt W v
              rw [body_def]
              apply SMT.fv.mem_ite
              exact Or.inl (SMT.fv.mem_and (.inr hv))
            have hDval_alt_ab : Dval_alt ∈
                ⟦BType.set (a ×ᴮ b)⟧ᶻ := by
              rw [← htau]
              exact hDval_alt
            have den_D_alt_ab :
                ⟦D.abstract Xi_alt
                  (fun v hv => Xi_fv_alt v
                    (B.fv.mem_collect (.inl hv)))⟧ᴮ =
                  some (⟨Dval_alt, BType.set (a ×ᴮ b),
                    hDval_alt_ab⟩ : B.Dom) := by
              simpa only [htau, proof_irrel_heq] using den_D_alt
            have hT_alt_ab : T_alt ∈ ⟦BType.set (a ×ᴮ b)⟧ᶻ := by
              rw [← htau]
              exact hT_alt
            have den_collect_alt_ab :
                ⟦(B.Term.collect vs D P).abstract Xi_alt Xi_fv_alt⟧ᴮ =
                  some (⟨T_alt, BType.set (a ×ᴮ b),
                    hT_alt_ab⟩ : B.Dom) := by
              simpa only [tau, htau, proof_irrel_heq] using den_alt
            have ambient_P_alt : ∀ v ∈ B.fv P, v ∉ vs →
                match Xi_alt v, ThetaP_alt v with
                | some d, some d' => RDomCastSupported d d'
                | _, _ => False := by
              intro v hv hvs
              exact related_out_alt v
                (B.fv.mem_collect (.inr ⟨hv, hvs⟩))
            have wf_bound_alt : ∀ (x y : ZFSet.{u})
                (hx : x ∈ ⟦a⟧ᶻ) (hy : y ∈ ⟦b⟧ᶻ),
                B.RenWF Ebody.context
                  (Function.updates Xi_alt vs (List.ofFn fun i => some
                    (⟨(x.pair y).get vs.length i,
                      (a ×ᴮ b).get vs.length i,
                      get_mem_type_of_isTuple
                        (hasArity_of_mem_toZFSet hprod_arity_ab
                          (ZFSet.pair_mem_prod.mpr ⟨hx, hy⟩))
                        hprod_arity_ab
                        (ZFSet.pair_mem_prod.mpr ⟨hx, hy⟩)⟩ : B.Dom))) := by
              intro x y hx hy
              apply B.RenWF.updates_ofFn wf_alt vs_nodup vs_context_disj
                vs_alphas_len
              intro i
              change (a ×ᴮ b).get vs.length i =
                alphas[Fin.cast vs_alphas_len i]
              rw [← htau]
              exact BType.get_reduce alphas_nemp vs_alphas_len i
            have source_respects_upd_alt : ∀ ss : Fin vs.length → SMT.Dom,
                (∀ i, St3.types.lookup vs[i] = some (ss i).snd.fst) →
                B.RenamingContext.RespectsTypeContextOnFV
                  (Function.updates ThetaP_alt vs
                    ((List.ofFn ss).map Option.some)) St3.types P := by
              intro ss hss
              apply B.RenamingContext.RespectsTypeContextOnFV.updates_of_typed_bounds
                vs_nodup
              · intro v hv hvs sigma hlookup
                exact respects_P_alt_out hv hlookup
              · exact hss
            have target_respects_upd_alt : ∀ ss : Fin vs.length → SMT.Dom,
                (∀ i, St3.types.lookup vs[i] = some (ss i).snd.fst) →
                SMT.RenamingContext.RespectsTypeContextOnFV
                  (Function.updates ThetaP_alt vs
                    ((List.ofFn ss).map Option.some)) St3.types Penc := by
              intro ss hss v sigma hv hlookup
              by_cases hvs : v ∈ vs
              · let i : Fin vs.length :=
                  ⟨vs.idxOf v, List.idxOf_lt_length_of_mem hvs⟩
                have hvi : vs[i] = v := List.getElem_idxOf i.isLt
                refine ⟨ss i, ?_, ?_⟩
                · rw [Function.updates_eq_if (by simp) vs_nodup,
                    dif_pos hvs]
                  simp only [List.getElem_map, List.getElem_ofFn]
                  congr 1
                · have hbound := hss i
                  rw [hvi] at hbound
                  exact Option.some.inj (hbound.symm.trans hlookup)
              · obtain ⟨d, hd, htype⟩ :=
                  target_respects_P_alt hv hlookup
                refine ⟨d, ?_, htype⟩
                rw [Function.updates_of_not_mem ThetaP_alt vs _ v hvs]
                exact hd
            have specs_true_upd_alt : ∀ ss : Fin vs.length → SMT.Dom,
                (∀ i, St3.types.lookup vs[i] = some (ss i).snd.fst) →
                SpecBodiesTrue
                  (Function.updates ThetaP_alt vs
                    ((List.ofFn ss).map Option.some)) St3.types [] := by
              intro ss hss
              simp [SpecBodiesTrue, specBodies]
            have P_scope_alt : ScopedContextExtends St2.types [] St3.types :=
              P_trace.scoped_extends
            have hrel_alt := represented_collect_option_lambda
              (D := D) (P := P) (alpha := a) (beta := b)
              (Xi := Xi_alt) (Dval := Dval_alt) (hDval := hDval_alt_ab)
              (T := T_alt) (hT := hT_alt_ab) (Denc := Denc) (Penc := Penc)
              (body := body) (z := z) (ThetaD := ThetaP_alt)
              (DencVal := DencVal_alt) (lamVal := lamVal_alt)
              (Ebody := Ebody) (LambdaP := St2.types) (GammaP := St3.types)
              (DltP := []) (sigmaP := SMTType.bool)
              vs_nemp prefix_nemp_out vs_nodup Xi_fv_alt hprod_arity_ab
              vs_len_ge_two den_D_alt_ab den_collect_alt_ab
              (by simpa only [hbeta] using body_def)
              (by simpa only [halpha, proof_irrel_heq] using hcov_lambda_alt)
              (by simpa only [halpha, proof_irrel_heq] using hden_lambda_alt)
              (by simpa only [halpha, hbeta] using hlam_type_alt)
              (by simpa only [proof_irrel_heq] using hcov_D_upd_alt)
              (by simpa only [proof_irrel_heq] using hden_D_upd_alt)
              (by simpa only [halpha, hbeta] using hDenc_type_alt)
              (by simpa only [halpha, hbeta] using hDenc_func_alt)
              (by
                simpa only [htau, halpha, hbeta, proof_irrel_heq] using
                  D_rel_alt)
              (by simpa only [hbeta, proof_irrel_heq] using hcov_body_upd_alt)
              (by simpa only [halpha, hbeta, proof_irrel_heq] using
                hbody_total_alt)
              hDapp_fv_not_bv hDapp_fv_disj_vs hvs_not_bv
              (by
                intro hz
                exact z_not_used (P_bv_used z hz))
              z_not_vs hcov_sub_upd_alt hcov_P_upd_alt
              typ_P_body P_guard P_scope_alt typ_Penc rfl ambient_P_alt
              wf_bound_alt bound_expected source_respects_upd_alt
              target_respects_upd_alt specs_true_upd_alt z_not_fv_Penc
            refine ⟨ThetaP_alt, hcov_lambda_alt, lamVal_alt,
              ThetaP_alt_ext0, related_out_alt, ThetaP_alt_none_out,
              respects_collect_alt, target_respects_lambda_out_alt,
              ThetaP_alt_dom_out, hden_lambda_alt, hlam_type_alt, ?_⟩
            simpa only [tau, htau, proof_irrel_heq] using hrel_alt
      · exact wp_bind_throw _ _ _ _
    · mvcgen
  · rename_i tau' hDshape
    change sigmaD = tau'.fun SMTType.bool at hDshape
    subst sigmaD
    rcases DencVal with ⟨DencZF, sigmaVal, hDencMem⟩
    change sigmaVal = tau'.fun SMTType.bool at hDenc_type
    subst sigmaVal
    have tau'_supported : BType.SupportedSMT tau tau' := by
      rcases BType.SupportedSMT.setE D_rel.supported with
        ⟨rho, hpred, rho_supported⟩ | ⟨a, b, hab, hoption⟩
      · have hrho := SMTType.fun.inj hpred |>.1
        subst rho
        exact rho_supported
      · have hcod := SMTType.fun.inj hoption |>.2
        cases hcod
    let sigmas := tau'.fromProdl (vs.length - 1)
    have sigmas_len : sigmas.length = vs.length := by
      simpa [sigmas] using
        tau'_supported.fromProdl_length_of_hasArity tau_hasArity
    have vs_sigmas_len : vs.length = sigmas.length := sigmas_len.symm
    have sigmas_toProdl : sigmas.toProdl = tau' := by
      dsimp [sigmas]
      have h_arith : (tau'.fromProdl (vs.length - 1)).length =
          vs.length - 1 + 1 := by
        rw [sigmas_len]
        have := List.length_pos_of_ne_nil vs_nemp
        omega
      exact SMT.SMTType.fromProdl_toProdl_roundtrip _ _ h_arith
    mspec (SMT.addToContext_forIn_spec
      (vs.zip sigmas)
      (Γ := St1.types) (n := St1.env.freshvarsc)
      (used := St1.env.usedVars))
    mrename_i modify_post
    mintro ∀St2
    mpure modify_post
    obtain ⟨St2_types, St2_fresh, St2_used⟩ := modify_post
    set Ebody : B.Env := { E with
      context := vs.zipToAList alphas ∪ E.context } with Ebody_def
    conv in encodeTerm P E =>
      rw [encodeTerm_state.encodeTerm_env_irrel P E Ebody rfl]
    have St1_sub_St2_used : St1.env.usedVars ⊆ St2.env.usedVars := by
      rw [St2_used]
      exact fun v hv => encodeTerm_state.mem_foldl_cons_of_mem _ _ hv
    have vars_used_P_St2 : ∀ v ∈ P.vars, v ∈ St2.env.usedVars :=
      fun v hv => St1_sub_St2_used (D_used_sub (vars_used_P v hv))
    have vs_disj_St1 : ∀ v ∈ vs, v ∉ St1.types := by
      intro v hv
      have vs_not_D_fv : v ∉ B.fv D := fun hv_fv =>
        vs_context_disj v hv
          (AList.lookup_isSome.mp
            (B.Typing.mem_context_of_mem_fv typ_D hv_fv))
      have hv_vars_D : v ∉ B.Term.vars D :=
        B.Term.notMem_vars_iff.mpr ⟨vs_not_D_fv, by
          have h := bv_nodup
          simp only [B.bv] at h
          rw [List.nodup_append, List.nodup_append] at h
          intro h_bv
          exact h.1.2.2 v hv v h_bv rfl⟩
      apply D_preserves v (vars_used_vs v hv) _ hv_vars_D
      intro hv_St0
      have hv_collect : v ∈ (B.Term.collect vs D P).vars := by
        unfold B.Term.vars
        rw [List.mem_union_iff]
        right
        simp only [B.bv, List.mem_append]
        exact .inl (.inl hv)
      exact vs_context_disj v hv (Lambda_inv v hv_collect hv_St0)
    have Lambda_inv_P : ∀ v ∈ P.vars,
        v ∈ St2.types → v ∈ Ebody.context := by
      intro v v_in_P_vars v_in_St2_types
      rw [Ebody_def]
      show v ∈ vs.zipToAList alphas ∪ E.context
      by_cases v_in_vs : v ∈ vs
      · exact AList.mem_union.mpr (.inl
          (AList.mem_zipToAList_of_mem vs_nodup vs_alphas_len v_in_vs))
      · have v_in_St1 : v ∈ St1.types := by
          rw [St2_types] at v_in_St2_types
          refine AList.mem_of_mem_foldl_insert' v_in_St2_types ?_
          intro h
          rw [List.mem_map] at h
          obtain ⟨⟨a, b⟩, hab, rfl⟩ := h
          exact v_in_vs (List.of_mem_zip hab).1
        have v_used : v ∈ used := vars_used_P v v_in_P_vars
        by_cases v_St0 : v ∈ St0.types
        · have v_collect : v ∈ (B.Term.collect vs D P).vars := by
            unfold B.Term.vars at v_in_P_vars ⊢
            rw [List.mem_union_iff]
            rcases List.mem_union_iff.mp v_in_P_vars with h_fv | h_bv
            · exact .inl (by
                simp only [B.fv, List.mem_append]
                exact .inr (List.mem_removeAll_iff.mpr ⟨h_fv, v_in_vs⟩))
            · exact .inr (by
                simp only [B.bv, List.mem_append]
                exact .inr h_bv)
          exact AList.mem_union.mpr (.inr
            (Lambda_inv v v_collect v_St0))
        · have v_vars_D : v ∈ B.Term.vars D := by
            by_contra h
            exact absurd v_in_St1 (D_preserves v v_used v_St0 h)
          rcases B.Term.mem_vars_iff.mp v_vars_D with h | h
          · exact AList.mem_union.mpr (.inr
              (AList.lookup_isSome.mp
                (B.Typing.mem_context_of_mem_fv typ_D h)))
          · rcases B.Term.mem_vars_iff.mp v_in_P_vars with hv_fv_P | hv_bv_P
            · have h_in_Ebody :
                ((vs.zipToAList alphas ∪ E.context).lookup v).isSome :=
                  B.Typing.mem_context_of_mem_fv typ_P hv_fv_P
              exact AList.lookup_isSome.mp h_in_Ebody
            · exfalso
              have hbn := bv_nodup
              simp only [B.bv] at hbn
              rw [List.nodup_append] at hbn
              have hin : v ∈ vs ++ B.bv D :=
                List.mem_append.mpr (.inr h)
              exact hbn.2.2 v hin v hv_bv_P rfl
    have St2_keys_sub : AList.keys St2.types ⊆ St2.env.usedVars := by
      rw [St2_types, St2_used]
      exact encodeTerm_state.keys_foldl_insert_subset_foldl_cons _ D_keys_sub
    have St1_sub_St2 : St1.types ⊆ St2.types := by
      rw [St2_types]
      refine AList.subset_foldl_insert' ?_ ?_
      · intro p hp
        exact vs_disj_St1 p.1 (List.mem_fst_of_mem_zip hp)
      · exact List.nodup_map_fst_of_nodup_zip vs_nodup
    let xs : Fin vs.length → B.Dom := fun i =>
      ⟨tau.defaultZFSet.get vs.length i, tau.get vs.length i,
        get_mem_type_of_isTuple
          (BType.hasArity_of_foldl_defaultZFSet tau_hasArity)
          tau_hasArity BType.mem_toZFSet_of_defaultZFSet⟩
    have xs_type : ∀ i : Fin vs.length,
        (xs i).snd.fst = alphas[Fin.cast vs_alphas_len i] := by
      intro i
      dsimp [xs]
      exact BType.get_reduce alphas_nemp vs_alphas_len i
    have alphas_sigmas_len : alphas.length = sigmas.length :=
      vs_alphas_len.symm.trans vs_sigmas_len
    let Yrun : ZFSet := tau'.defaultZFSet
    have hYrun : Yrun ∈ ⟦tau'⟧ᶻ :=
      SMTType.mem_toZFSet_of_defaultZFSet
    have hYrun_prodl : Yrun ∈ ⟦sigmas.toProdl⟧ᶻ := by
      rw [sigmas_toProdl]
      exact hYrun
    have run_rel : RDomCastSupported
        (⟨tau.defaultZFSet, tau,
          BType.mem_toZFSet_of_defaultZFSet⟩ : B.Dom)
        (⟨Yrun, tau', hYrun⟩ : SMT.Dom) := by
      simpa only [Yrun, proof_irrel_heq] using
        RDomCastSupported.default_of_supported tau'_supported
    have run_rel_prodl : RDomCastSupported
        (⟨tau.defaultZFSet, alphas.reduce (· ×ᴮ ·) alphas_nemp,
          BType.mem_toZFSet_of_defaultZFSet⟩ : B.Dom)
        (⟨Yrun, sigmas.toProdl, hYrun_prodl⟩ : SMT.Dom) := by
      simpa only [tau, sigmas_toProdl, proof_irrel_heq] using run_rel
    let ss : Fin vs.length → SMT.Dom := fun i =>
      let j : Fin sigmas.length := Fin.cast vs_sigmas_len i
      ⟨Yrun.get sigmas.length j, sigmas[j],
        SMTType.mem_get_of_mem_toProdl
          (fun hs => alphas_nemp (List.length_eq_zero_iff.mp
            (alphas_sigmas_len.trans (by simp [hs])))) hYrun_prodl⟩
    have hbound_type : ∀ i : Fin vs.length,
        St2.types.lookup vs[i] = some (ss i).snd.fst := by
      intro i
      have hi_sigma : i.val < sigmas.length :=
        i.isLt.trans_eq vs_sigmas_len
      have hlookup : St2.types.lookup vs[i] =
          some (sigmas[i.val]'hi_sigma) := by
        rw [St2_types]
        exact foldl_insert_lookup_zip vs_nodup i.isLt hi_sigma
      simpa [ss] using hlookup
    let XiP : B.RenamingContext.Context :=
      Function.updates Xi vs (List.ofFn fun i => some (xs i))
    let ThetaP0 : SMT.RenamingContext.Context :=
      Function.updates ThetaD vs
        ((List.ofFn ss).map Option.some)
    have hThetaP0_map :
        (List.ofFn ss).map Option.some =
          List.ofFn (fun i => some (ss i)) := by
      rw [List.map_ofFn]
      rfl
    have wf_P : B.RenWF Ebody.context XiP := by
      dsimp [XiP]
      exact B.RenWF.updates_ofFn wf vs_nodup vs_context_disj
        vs_alphas_len xs_type
    have typ_P_body : Ebody.context ⊢ᴮ P : BType.bool := by
      simpa [Ebody] using typ_P
    obtain ⟨XiP_fv, Pval, hPval, den_P⟩ :=
      B.denote_collect_default_predicate_exists Xi_fv vs_nemp vs_nodup
        tau_hasArity den_D den_t typ_P_body wf_P
    have related_collect_out : RValuationCastSupportedOnFV Xi ThetaD
        (B.Term.collect vs D P) :=
      related.of_extends ThetaD_ext
    have related_P : RValuationCastSupportedOnFV XiP ThetaP0 P := by
      dsimp [XiP, ThetaP0]
      rw [hThetaP0_map]
      apply RValuationCastSupportedOnFV.updates vs_nodup xs ss
      · intro v hv hv_not_vs
        exact related_collect_out v
          (B.fv.mem_collect (.inr ⟨hv, hv_not_vs⟩))
      · intro i
        let jalpha : Fin alphas.length := Fin.cast vs_alphas_len i
        have hcomp := RDomCastSupported.get_of_reduce_toProdl
          alphas_nemp alphas_sigmas_len
          BType.mem_toZFSet_of_defaultZFSet hYrun_prodl
          run_rel_prodl jalpha
        have hsource : xs i =
            (⟨tau.defaultZFSet.get alphas.length jalpha, alphas[jalpha],
              BType.mem_get_of_mem_reduce_toZFSet alphas_nemp
                BType.mem_toZFSet_of_defaultZFSet⟩ : B.Dom) := by
          exact B.Dom.ext_type_value
            (BType.get_reduce alphas_nemp vs_alphas_len i)
            (ZFSet.get_cast vs_alphas_len i)
        rw [hsource]
        simpa [ss, jalpha] using hcomp
    have ThetaP0_none : ∀ v ∉ St2.env.usedVars,
        ThetaP0 v = none := by
      intro v hv
      dsimp [ThetaP0]
      apply SMT.RenamingContext.updates_none_of_mem_used
        (fun w hw => by
          rw [St2_used]
          exact encodeTerm_state.mem_foldl_cons_of_mem _ _
            (D_used_sub (vars_used_vs w hw)))
        (fun w hw => ThetaD_none w (fun h =>
          hw (St1_sub_St2_used h))) v hv
    have ThetaP0_dom : ∀ v, ThetaP0 v ≠ none → v ∈ St2.types := by
      dsimp [ThetaP0]
      exact SMT.RenamingContext.updates_dom_of_typed_bounds
        (fun v hv => AList.mem_of_subset St1_sub_St2 (ThetaD_dom v hv))
        hbound_type
    have respects_P : B.RenamingContext.RespectsTypeContextOnFV
        ThetaP0 St2.types P := by
      dsimp [ThetaP0]
      apply B.RenamingContext.RespectsTypeContextOnFV.updates_of_typed_bounds
        vs_nodup
      · intro v hv hv_not_vs sigma hlookup
        have hv_collect : v ∈ B.fv (B.Term.collect vs D P) :=
          B.fv.mem_collect (.inr ⟨hv, hv_not_vs⟩)
        have hv_St0 : v ∈ St0.types := fv_in_Lambda v hv_collect
        obtain ⟨sigma0, hsigma0⟩ := Option.isSome_iff_exists.mp
          (AList.lookup_isSome.mpr hv_St0)
        have hsigma1 : St1.types.lookup v = some sigma0 :=
          AList.lookup_of_subset D_types_sub hsigma0
        have hsigma2 : St2.types.lookup v = some sigma0 := by
          rw [St2_types]
          apply foldl_insert_preserves_lookup hsigma1
          intro p hp hpv
          apply hv_not_vs
          rw [← hpv]
          exact (List.of_mem_zip hp).1
        rw [hsigma2] at hlookup
        cases hlookup
        obtain ⟨d, hd, hdty⟩ := respects hv_collect hsigma0
        exact ⟨d, ThetaD_ext hd, hdty⟩
      · exact hbound_type
    have fv_in_St2_P : ∀ v ∈ B.fv P, v ∈ St2.types := by
      intro v hv
      by_cases hvs : v ∈ vs
      · let i : Fin vs.length :=
          ⟨vs.idxOf v, List.idxOf_lt_length_of_mem hvs⟩
        have hvi : vs[i] = v := List.getElem_idxOf i.isLt
        apply AList.lookup_isSome.mp
        apply Option.isSome_of_eq_some
        have hbound := hbound_type i
        rw [hvi] at hbound
        exact hbound
      · exact AList.mem_of_subset St1_sub_St2
          (AList.mem_of_subset D_types_sub
            (fv_in_Lambda v (B.fv.mem_collect (.inr ⟨hv, hvs⟩))))
    mspec Std.Do.Spec.get_StateT
    mspec (Std.Do.Triple.and _
      (Std.Do.Triple.and _
        (Std.Do.Triple.and _
          (Std.Do.Triple.and _
            (P_ih Ebody typ_P_body XiP_fv related_P ThetaP0_none ThetaP0_dom
              den_P vars_used_P_St2 Lambda_inv_P P_bv_nodup respects_P
              fv_in_St2_P wf_P (n := St2.env.freshvarsc))
            (P_scoped Ebody typ_P_body XiP_fv related_P ThetaP0_none
              ThetaP0_dom den_P vars_used_P_St2 Lambda_inv_P P_bv_nodup
              respects_P fv_in_St2_P wf_P (n := St2.env.freshvarsc)
              (decl := St2.env.declarations)))
          (encodeTerm_decl Ebody typ_P_body vars_used_P_St2 Lambda_inv_P
            P_bv_nodup (n := St2.env.freshvarsc)
            (decl := St2.env.declarations)))
        (SMT.encodeTerm_bv_used Ebody (t := P)
          (used := St2.env.usedVars) (n := St2.env.freshvarsc)
          (decl := St2.env.declarations)))
      (SMT.encodeTerm_bv_notMem_used Ebody (t := P)
        (used := St2.env.usedVars) (n := St2.env.freshvarsc)
        (decl := St2.env.declarations)))
    rename_i out_P
    obtain ⟨Penc, sigmaP⟩ := out_P
    mrename_i P_post
    mintro ∀St3
    mpure P_post
    obtain ⟨⟨⟨⟨P_rep, P_scoped_post⟩, P_decl⟩, P_bv_used_post⟩,
      P_bv_not_used_post⟩ := P_post
    obtain ⟨DltP, P_sc_decl, P_ctx, P_trace, P_sc_total, P_guard,
      P_specs_op, P_sc_typing⟩ := P_scoped_post
    obtain ⟨P_used_sub, P_types_sub, P_keys_sub, P_covers, P_path,
      typ_Penc, P_shape, P_preserves, ThetaP, hcov_Penc, ThetaP_ext,
      related_P_out, ThetaP_none, respects_P_out, target_respects_P,
      ThetaP_dom, PencVal, hden_Penc, hPenc_type, P_rel, P_total⟩ := P_rep
    obtain ⟨Pdelta, St3_decl_eq, Pspec_fv, Penc_fv_delta⟩ := P_decl
    have DltP_eq : DltP = Pdelta := by
      rw [P_sc_decl] at St3_decl_eq
      exact List.append_right_injective _ St3_decl_eq
    subst DltP
    obtain ⟨P_bv_used, P_used_sub_bv, Pdelta_bv, Pdelta_bv_ok⟩ :=
      P_bv_used_post
    obtain ⟨P_bv_not_used, P_used_sub_not_used, Pdelta_not_used,
      Pdelta_not_used_ok⟩ := P_bv_not_used_post
    split
    · rename_i hPshape
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hPshape
      mspec (SMT.ensureDeclarationsUnchanged_spec (St := St3))
      mrename_i ensure_post
      mintro ∀St3'
      mpure ensure_post
      obtain ⟨St3'_eq, P_decl_len⟩ := ensure_post
      subst St3'
      have Pdelta_nil : Pdelta = [] :=
        declaration_delta_eq_nil_of_length St3_decl_eq P_decl_len
      subst Pdelta
      have Penc_fv : SMT.fv Penc ⊆ B.Term.vars P := by
        intro v hv
        simpa [declVars] using Penc_fv_delta hv
      mspec (Std.Do.Triple.and (SMT.freshVar tau')
        (SMT.freshVar_spec (Γ := St3.types) (τ := tau')
          (n := St3.env.freshvarsc) (used := St3.env.usedVars))
        (SMT.freshVar_decls (τ := tau')
          (decl := St3.env.declarations)))
      rename_i z
      mrename_i fresh_post
      mintro ∀St4
      mpure fresh_post
      obtain ⟨⟨St4_types, z_fresh, St4_fresh, St4_used, z_not_used⟩,
        St4_decl⟩ := fresh_post
      mspec (Std.Do.Triple.and (SMT.eraseFromContext z)
        (SMT.eraseFromContext_spec (v := z) (Γ := St4.types)
          (n := St4.env.freshvarsc) (used := St4.env.usedVars))
        (SMT.eraseFromContext_decls (v := z)
          (decl := St4.env.declarations)))
      mrename_i erase_post
      mintro ∀St5
      mpure erase_post
      obtain ⟨⟨St5_types, St5_fresh, St5_used⟩, St5_decl⟩ := erase_post
      mspec Std.Do.Spec.pure
      mpure_intro
      have St5_types_eq : St5.types = St3.types := by
        rw [St5_types, St4_types]
        exact encodeTerm_state.erase_insert_self z_fresh
      have St5_used_chain : St5.env.usedVars = z :: St3.env.usedVars := by
        rw [St5_used, St4_used]
      have St1_sub_St3 : St1.types ⊆ St3.types :=
        AList.subset_trans St1_sub_St2 P_types_sub
      have St0_sub_St5 : St0.types ⊆ St5.types := by
        rw [St5_types_eq]
        exact AList.subset_trans D_types_sub St1_sub_St3
      refine encodeTermRepPost_of_state_and_semantic ?_ ?_
      · refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · rw [St5_used_chain]
          intro v hv
          exact List.mem_cons_of_mem _
            (P_used_sub (St1_sub_St2_used (D_used_sub hv)))
        · exact St0_sub_St5
        · rw [St5_types_eq, St5_used_chain]
          intro v hv
          exact List.mem_cons_of_mem _ (P_keys_sub hv)
        · intro v hv
          rw [St5_used_chain]
          apply List.mem_cons_of_mem
          rw [B.fv, List.mem_append] at hv
          rcases hv with hv_D | hv_P
          · exact P_used_sub (St1_sub_St2_used (D_covers v hv_D))
          · exact P_covers v (List.mem_removeAll_iff.mp hv_P).1
        · intro v v_used v_notMem_St0 v_notMem_vars
          obtain ⟨v_notMem_vars_D, v_notMem_vars_P, hv_not_vs⟩ :=
            B.Term.notMem_vars_collect.mp v_notMem_vars
          rw [St5_types_eq]
          intro v_in_St3
          have v_notMem_St1 :=
            D_preserves v v_used v_notMem_St0 v_notMem_vars_D
          have v_notMem_St2 : v ∉ St2.types := by
            rw [St2_types]
            intro h
            refine v_notMem_St1 (AList.mem_of_mem_foldl_insert' h ?_)
            intro hmem
            rw [List.mem_map] at hmem
            obtain ⟨⟨a, b⟩, hab, rfl⟩ := hmem
            exact hv_not_vs (List.of_mem_zip hab).1
          exact P_preserves v
            (St1_sub_St2_used (D_used_sub v_used)) v_notMem_St2
            v_notMem_vars_P v_in_St3
      · have hbv_D_notMem_St3 : ∀ v ∈ SMT.bv Denc,
            v ∉ St3.types := by
          intro v hv
          have hv_not_St1 : v ∉ St1.types :=
            SMT.Typing.bv_notMem_context typ_Denc v hv
          have hv_not_used : v ∉ used := by
            rw [← St0_used_eq]
            exact D_bv_not_used v hv
          have hv_not_vs : v ∉ vs := fun hvs =>
            hv_not_used (vars_used_vs v hvs)
          have hv_not_P_vars : v ∉ P.vars := fun hP =>
            hv_not_used (vars_used_P v hP)
          have hv_not_St2 : v ∉ St2.types := by
            rw [St2_types]
            intro hmem
            apply hv_not_St1
            apply AList.mem_of_mem_foldl_insert' hmem
            intro h
            rw [List.mem_map] at h
            obtain ⟨⟨x, sigma⟩, hxs, rfl⟩ := h
            exact hv_not_vs (List.of_mem_zip hxs).1
          apply P_preserves v (St1_sub_St2_used (D_bv_used v hv))
            hv_not_St2 hv_not_P_vars
        have typ_Denc_St3 : St3.types ⊢ˢ Denc :
            tau'.fun SMTType.bool :=
          SMT.Typing.weakening St1_sub_St3 typ_Denc hbv_D_notMem_St3
        have z_not_bv_Penc : z ∉ SMT.bv Penc := by
          intro hz
          exact z_not_used (P_bv_used z hz)
        have typ_Penc_z : St3.types.insert z tau' ⊢ˢ
            Penc : SMTType.bool :=
          SMT.Typing.weakening
            (SMT.TypeContext.entries_subset_insert_of_notMem z_fresh)
            typ_Penc
            (SMT.Typing.bv_notMem_insert_of_fresh typ_Penc z_not_bv_Penc)
        have z_not_bv_Denc : z ∉ SMT.bv Denc := by
          intro hz
          exact z_not_used (P_used_sub
            (St1_sub_St2_used (D_bv_used z hz)))
        have typ_Denc_z : St3.types.insert z tau' ⊢ˢ Denc :
            tau'.fun SMTType.bool :=
          SMT.Typing.weakening
            (SMT.TypeContext.entries_subset_insert_of_notMem z_fresh)
            typ_Denc_St3
            (SMT.Typing.bv_notMem_insert_of_fresh
              typ_Denc_St3 z_not_bv_Denc)
        have typ_z : St3.types.insert z tau' ⊢ˢ
            SMT.Term.var z : tau' :=
          SMT.Typing.var _ z tau'
            (AList.lookup_insert St3.types)
        have typ_Dapp_z : St3.types.insert z tau' ⊢ˢ
            ((@ˢDenc) (.var z)) : SMTType.bool :=
          SMT.Typing.app _ _ _ _ _ typ_Denc_z typ_z
        have typ_Psub : St3.types.insert z tau' ⊢ˢ
            SMT.substList vs (toDestPair vs (.var z)) Penc :
              SMTType.bool := by
          apply SMT_Typing_substList
          · exact typ_Penc_z
          · exact toDestPair_bv_nil
          · intro i hi_x hi_t hx
            have hi_tau : i <
                (tau'.fromProdl (vs.length - 1)).length := by
              rw [tau'_supported.fromProdl_length_of_hasArity tau_hasArity]
              exact hi_x
            have hlookup_St2 : St2.types.lookup vs[i] = some
                ((tau'.fromProdl
                  (vs.length - 1))[i]'hi_tau) := by
              rw [St2_types]
              exact foldl_insert_lookup_zip vs_nodup hi_x hi_tau
            have hlookup_St3 : St3.types.lookup vs[i] = some
                ((tau'.fromProdl
                  (vs.length - 1))[i]'hi_tau) :=
              AList.lookup_of_subset P_types_sub hlookup_St2
            have hne : vs[i] ≠ z := by
              intro heq
              have hvi_used : vs[i] ∈ St3.env.usedVars :=
                P_used_sub (by
                  rw [St2_used]
                  exact encodeTerm_state.mem_foldl_cons_of_mem _ _
                    (D_used_sub (vars_used_vs vs[i]
                      (List.getElem_mem hi_x))))
              exact z_not_used (heq ▸ hvi_used)
            have hlookup : (St3.types.insert z tau').lookup vs[i] =
                some ((tau'.fromProdl
                  (vs.length - 1))[i]'hi_tau) := by
              rw [AList.lookup_insert_ne hne]
              exact hlookup_St3
            have hget : ((St3.types.insert z tau').lookup vs[i]).get
                hx = (tau'.fromProdl
                  (vs.length - 1))[i]'hi_tau := by
              simp [hlookup]
            rw [hget]
            obtain ⟨_, htyp⟩ := toDestPair_typing_gen
              (St3.types.insert z tau') vs (.var z) (.var z)
              tau' [] [] vs_nemp rfl typ_z
              (tau'_supported.fromProdl_length_of_hasArity tau_hasArity) rfl
              (fun j hj => absurd hj (Nat.not_lt_zero j)) i
              ((tau'.fromProdl
                (vs.length - 1))[i]'hi_tau)
              (by
                simp only [List.append_nil]
                rw [List.getElem?_eq_getElem hi_tau])
            exact htyp
        have hupdate : St5.types.update [z] [tau'] rfl =
            St3.types.insert z tau' := by
          rw [St5_types_eq]
          simp only [SMT.TypeContext.update, List.length_cons,
            List.length_nil, zero_add, Nat.reduceAdd, Fin.cast_eq_self,
            Fin.getElem_fin, Fin.val_eq_zero, List.getElem_cons_zero,
            Fin.foldl_succ, Fin.foldl_zero]
        have typ_lambda : St5.types ⊢ˢ
            (λˢ [z]) [tau']
              (SMT.Term.ite ((@ˢDenc) (.var z))
                (SMT.substList vs (toDestPair vs (.var z)) Penc)
                (.bool false)) :
            tau'.fun SMTType.bool := by
          refine SMT.Typing.lambda St5.types [z] [tau'] _
            SMTType.bool ?_ ?_ (Nat.zero_lt_succ 0) rfl ?_
          · intro v hv
            rw [List.mem_singleton] at hv
            subst v
            rw [St5_types_eq]
            exact z_fresh
          · intro v hv
            rw [List.mem_singleton] at hv
            subst v
            simp only [SMT.bv, List.append_nil, List.mem_append, not_or]
            constructor
            · exact z_not_bv_Denc
            · intro hbv
              have hbv_P := SMT_bv_substList_subset
                (fun t ht => toDestPair_bv_nil t ht) z hbv
              exact z_not_bv_Penc hbv_P
          · rw [hupdate]
            exact SMT.Typing.ite _ _ _ _ _ typ_Dapp_z typ_Psub
              (SMT.Typing.bool _ _)
        refine ⟨D_path, typ_lambda, trivial, ?_⟩
        let body : SMT.Term :=
          SMT.Term.ite ((@ˢDenc) (.var z))
            (SMT.substList vs (toDestPair vs (.var z)) Penc)
            (.bool false)
        have body_def : body =
            SMT.Term.ite ((@ˢDenc) (.var z))
              (SMT.substList vs (toDestPair vs (.var z)) Penc)
              (.bool false) := rfl
        have ThetaP0_ext : SMT.RenamingContext.Extends ThetaP0 ThetaD := by
          intro v d hv
          dsimp [ThetaP0]
          by_cases hvs : v ∈ vs
          · have hnone : ThetaD v = none := by
              cases hTheta : ThetaD v with
              | none => rfl
              | some d' =>
                  exfalso
                  exact vs_disj_St1 v hvs
                    (ThetaD_dom v (by rw [hTheta]; simp))
            rw [hnone] at hv
            cases hv
          · rw [Function.updates_of_not_mem _ _ _ _ hvs]
            exact hv
        have ThetaP_ext_D : SMT.RenamingContext.Extends ThetaP ThetaD :=
          SMT.RenamingContext.extends_trans ThetaP_ext ThetaP0_ext
        have ThetaP_ext0 : SMT.RenamingContext.Extends ThetaP Theta0 :=
          SMT.RenamingContext.extends_trans ThetaP_ext_D ThetaD_ext
        have related_out : RValuationCastSupportedOnFV Xi ThetaP
            (B.Term.collect vs D P) :=
          related.of_extends ThetaP_ext0
        have respects_collect_out :
            B.RenamingContext.RespectsTypeContextOnFV ThetaP St5.types
              (B.Term.collect vs D P) := by
          apply B.RenamingContext.RespectsTypeContextOnFV.of_extends respects
            ThetaP_ext0 St0_sub_St5
          · intro v hv
            exact hv
          · exact fv_in_Lambda
        have ThetaP_none_out : ∀ v ∉ St5.env.usedVars,
            ThetaP v = none := by
          intro v hv
          apply ThetaP_none v
          rw [St5_used_chain] at hv
          simp only [List.mem_cons, not_or] at hv
          exact hv.2
        have ThetaP_dom_out : ∀ v, ThetaP v ≠ none → v ∈ St5.types := by
          intro v hv
          rw [St5_types_eq]
          exact ThetaP_dom v hv
        have hD_fv_not_vs : ∀ v ∈ SMT.fv Denc, v ∉ vs := by
          intro v hv hvs
          exact vs_disj_St1 v hvs
            (SMT.Typing.mem_context_of_mem_fv typ_Denc hv)
        have hcov_D_ThetaP0 : SMT.RenamingContext.CoversFV ThetaP0 Denc := by
          intro v hv
          dsimp [ThetaP0]
          rw [Function.updates_of_not_mem _ _ _ _ (hD_fv_not_vs v hv)]
          exact hcov_Denc v hv
        have hcov_D_ThetaP : SMT.RenamingContext.CoversFV ThetaP Denc := by
          intro v hv
          obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp
            (hcov_D_ThetaP0 v hv)
          exact Option.isSome_of_eq_some (ThetaP_ext hd)
        have hagree_D : SMT.RenamingContext.AgreesOnFV ThetaD ThetaP Denc := by
          intro v hv
          obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (hcov_Denc v hv)
          have h0 : ThetaP0 v = some d := by
            dsimp [ThetaP0]
            rw [Function.updates_of_not_mem _ _ _ _ (hD_fv_not_vs v hv)]
            exact hd
          exact hd.trans (ThetaP_ext h0).symm
        have hden_D_ThetaP_eq :
            ⟦Denc.abstract ThetaP hcov_D_ThetaP⟧ˢ =
              ⟦Denc.abstract ThetaD hcov_Denc⟧ˢ := by
          change SMT.RenamingContext.denote ThetaP Denc hcov_D_ThetaP =
            SMT.RenamingContext.denote ThetaD Denc hcov_Denc
          exact (SMT.RenamingContext.denote_congr_of_agreesOnFV
            (h1 := hcov_Denc) (h2 := hcov_D_ThetaP) hagree_D).symm
        have z_not_fv_Denc : z ∉ SMT.fv Denc := by
          intro hz
          exact z_fresh (SMT.Typing.mem_context_of_mem_fv typ_Denc_St3 hz)
        have z_not_fv_Penc : z ∉ SMT.fv Penc := by
          intro hz
          exact z_fresh (SMT.Typing.mem_context_of_mem_fv typ_Penc hz)
        have hcov_D_upd : ∀ W : SMT.Dom,
            SMT.RenamingContext.CoversFV
              (Function.update ThetaP z (some W)) Denc := by
          intro W
          exact SMT.RenamingContext.coversFV_update_of_notMem
            z_not_fv_Denc hcov_D_ThetaP
        have hden_D_upd : ∀ W : SMT.Dom,
            ⟦Denc.abstract (Function.update ThetaP z (some W))
              (hcov_D_upd W)⟧ˢ =
              some (⟨DencZF, tau'.fun SMTType.bool,
                hDencMem⟩ : SMT.Dom) := by
          intro W
          calc
            ⟦Denc.abstract (Function.update ThetaP z (some W))
                (hcov_D_upd W)⟧ˢ =
                ⟦Denc.abstract ThetaP hcov_D_ThetaP⟧ˢ := by
              change SMT.RenamingContext.denote
                  (Function.update ThetaP z (some W)) Denc
                    (hcov_D_upd W) =
                SMT.RenamingContext.denote ThetaP Denc hcov_D_ThetaP
              exact (SMT.RenamingContext.denote_update_of_notMem
                (h := hcov_D_ThetaP) z_not_fv_Denc).symm
            _ = ⟦Denc.abstract ThetaD hcov_Denc⟧ˢ := hden_D_ThetaP_eq
            _ = some (⟨DencZF, tau'.fun SMTType.bool,
                hDencMem⟩ : SMT.Dom) := hden_Denc
        have hDenc_func : ⟦tau'⟧ᶻ.IsFunc 𝔹 DencZF := by
          have hmem := hDencMem
          rw [SMTType.toZFSet] at hmem
          exact ZFSet.mem_funs.mp hmem
        have target_respects_D_ThetaP :
            SMT.RenamingContext.RespectsTypeContextOnFV
              ThetaP St3.types Denc :=
          SMT.RenamingContext.RespectsTypeContextOnFV.of_extends
            target_respects_D ThetaP_ext_D St1_sub_St3 typ_Denc
        have vs_in_St3_used : ∀ v ∈ vs, v ∈ St3.env.usedVars := by
          intro v hv
          apply P_used_sub
          rw [St2_used]
          exact encodeTerm_state.mem_foldl_cons_of_mem _ _
            (D_used_sub (vars_used_vs v hv))
        have z_not_vs : z ∉ vs := by
          intro hz
          exact z_not_used (vs_in_St3_used z hz)
        have hvs_not_bv : ∀ v ∈ vs, v ∉ SMT.bv Penc := by
          intro v hv hbv
          apply P_bv_not_used v hbv
          rw [St2_used]
          exact encodeTerm_state.mem_foldl_cons_of_mem _ _
            (D_used_sub (vars_used_vs v hv))
        have hcov_P_upd : ∀ (W : SMT.Dom)
            (ss : Fin vs.length → SMT.Dom),
            SMT.RenamingContext.CoversFV
              (Function.updates (Function.update ThetaP z (some W)) vs
                ((List.ofFn ss).map Option.some)) Penc := by
          intro W ss v hv
          by_cases hvs : v ∈ vs
          · rw [Function.updates_eq_if
                (by rw [List.length_map, List.length_ofFn]) vs_nodup,
              dif_pos hvs]
            simp
          · rw [Function.updates_of_not_mem _ vs _ _ hvs,
              Function.update_of_ne (by
                intro heq
                exact z_not_fv_Penc (heq ▸ hv))]
            exact hcov_Penc v hv
        have hcov_sub_upd : ∀ W : SMT.Dom,
            SMT.RenamingContext.CoversFV
              (Function.update ThetaP z (some W))
              (SMT.substList vs (toDestPair vs (.var z)) Penc) := by
          intro W v hv
          rcases SMT_mem_fv_substList hv with hv_P | ⟨t, ht, hv_t⟩
          · rw [Function.update_of_ne (by
                intro heq
                exact z_not_fv_Penc (heq ▸ hv_P))]
            exact hcov_Penc v hv_P
          · have hvz := SMT_fv_toDestPair_subset ht hv_t
            subst v
            simp
        have hcov_body_upd : ∀ W : SMT.Dom,
            SMT.RenamingContext.CoversFV
              (Function.update ThetaP z (some W)) body := by
          intro W v hv
          rw [body_def] at hv
          simp only [SMT.fv, List.mem_append, List.mem_singleton,
            List.not_mem_nil, or_false] at hv
          rcases hv with (hv_D | rfl) | hv_sub
          · exact hcov_D_upd W v hv_D
          · simp
          · exact hcov_sub_upd W v hv_sub
        have hcov_lambda : SMT.RenamingContext.CoversFV ThetaP
            ((λˢ [z]) [tau'] body) := by
          intro v hv
          simp only [SMT.fv, List.mem_removeAll_iff] at hv
          obtain ⟨hv_body, hv_ne_z⟩ := hv
          have hvz : v ≠ z := List.mem_singleton.not.mp hv_ne_z
          have hcov := hcov_body_upd PencVal v hv_body
          rw [Function.update_of_ne hvz] at hcov
          exact hcov
        have target_respects_lambda :
            SMT.RenamingContext.RespectsTypeContextOnFV
              ThetaP St3.types ((λˢ [z]) [tau'] body) := by
          intro v sigma hv hlookup
          simp only [SMT.fv, List.mem_removeAll_iff] at hv
          obtain ⟨hv_body, hv_ne_z⟩ := hv
          have hvz : v ≠ z := List.mem_singleton.not.mp hv_ne_z
          rw [body_def] at hv_body
          simp only [SMT.fv, List.mem_append, List.mem_singleton,
            List.not_mem_nil, or_false] at hv_body
          rcases hv_body with (hv_D | hv_var) | hv_sub
          · exact target_respects_D_ThetaP hv_D hlookup
          · exact absurd hv_var hvz
          · rcases SMT_mem_fv_substList hv_sub with hv_P |
                ⟨t, ht, hv_t⟩
            · exact target_respects_P hv_P hlookup
            · exact absurd (SMT_fv_toDestPair_subset ht hv_t) hvz
        have target_respects_lambda_out :
            SMT.RenamingContext.RespectsTypeContextOnFV
              ThetaP St5.types ((λˢ [z]) [tau'] body) := by
          rw [St5_types_eq]
          exact target_respects_lambda
        have typ_ite : St3.types.insert z tau' ⊢ˢ
            body : SMTType.bool := by
          rw [body_def]
          exact SMT.Typing.ite _ _ _ _ _ typ_Dapp_z typ_Psub
            (SMT.Typing.bool _ _)
        have Theta_wt : ∀ v ∈ SMT.fv body, ∀ d : SMT.Dom,
            ThetaP v = some d → ∀ sigma,
              St3.types.lookup v = some sigma → d.snd.fst = sigma := by
          intro v hv d hd sigma hlookup
          by_cases hvz : v = z
          · subst v
            have hz_none : ThetaP z = none := ThetaP_none z z_not_used
            rw [hz_none] at hd
            contradiction
          · obtain ⟨d', hd', htype⟩ := target_respects_lambda
                (by
                  simp only [SMT.fv, List.mem_removeAll_iff]
                  exact ⟨hv, List.mem_singleton.not.mpr hvz⟩)
                hlookup
            rw [hd] at hd'
            cases hd'
            exact htype
        have fv_substList_disj_vs : ∀ v ∈
            SMT.fv (SMT.substList vs (toDestPair vs (.var z)) Penc),
            v ≠ z → v ∉ vs := by
          intro v hv_subst hne hvs
          rcases SMT_mem_fv_substList hv_subst with hv_P |
              ⟨t, ht, hv_t⟩
          · suffices hlen : vs.length ≤ (toDestPair vs (.var z)).length by
              have hts : ∀ t ∈ toDestPair vs (.var z),
                  v ∉ SMT.fv t :=
                fun t ht hv_t => hne (SMT_fv_toDestPair_subset ht hv_t)
              exact absurd hv_subst
                (SMT_not_mem_fv_substList_of_mem_vars hlen hvs hts)
            suffices ∀ (ws : List SMT.𝒱) (zp : SMT.Term)
                (acc : List SMT.Term) (d : SMT.Term),
                ws.length + acc.length ≤ (toDestPair ws zp acc d).length by
              simpa using this vs (.var z) [] (.var z)
            intro ws
            induction ws with
            | nil => intro _ acc _; simp [toDestPair]
            | cons w ws' ih =>
                intro zp acc d
                cases ws' with
                | nil => simp [toDestPair]; omega
                | cons w' ws'' =>
                    simp only [toDestPair]
                    have := ih (.fst d) (.snd d :: acc) (.fst d)
                    simp [List.length] at this ⊢
                    omega
          · have := SMT_fv_toDestPair_subset ht hv_t
            subst this
            exact hne rfl
        have hgo_cov : ∀ x ∈ SMT.fv body, x ∉ [z] →
            (ThetaP x).isSome = true := by
          intro x hx hxz
          apply hcov_lambda x
          simp only [SMT.fv, List.mem_removeAll_iff]
          exact ⟨hx, hxz⟩
        have bound_expected : ∀ i : Fin vs.length,
            St3.types.lookup vs[i] =
              some ((tau'.fromProdl (vs.length - 1))[i.val]'(by
                have hlen :=
                  tau'_supported.fromProdl_length_of_hasArity tau_hasArity
                exact i.isLt.trans_eq hlen.symm)) := by
          intro i
          have hlookup :=
            AList.lookup_of_subset P_types_sub (hbound_type i)
          simpa [ss, sigmas] using hlookup
        have source_respects_upd : ∀ ss : Fin vs.length → SMT.Dom,
            (∀ i, St3.types.lookup vs[i] = some (ss i).snd.fst) →
            B.RenamingContext.RespectsTypeContextOnFV
              (Function.updates ThetaP vs
                ((List.ofFn ss).map Option.some)) St3.types P := by
          intro ss hss
          apply B.RenamingContext.RespectsTypeContextOnFV.updates_of_typed_bounds
            vs_nodup
          · intro v hv hvs sigma hlookup
            exact respects_P_out hv hlookup
          · exact hss
        have target_respects_upd : ∀ ss : Fin vs.length → SMT.Dom,
            (∀ i, St3.types.lookup vs[i] = some (ss i).snd.fst) →
            SMT.RenamingContext.RespectsTypeContextOnFV
              (Function.updates ThetaP vs
                ((List.ofFn ss).map Option.some)) St3.types Penc := by
          intro ss hss v sigma hv hlookup
          by_cases hvs : v ∈ vs
          · let i : Fin vs.length :=
              ⟨vs.idxOf v, List.idxOf_lt_length_of_mem hvs⟩
            have hvi : vs[i] = v := List.getElem_idxOf i.isLt
            refine ⟨ss i, ?_, ?_⟩
            · rw [Function.updates_eq_if (by simp) vs_nodup,
                dif_pos hvs]
              simp only [List.getElem_map, List.getElem_ofFn]
              congr 1
            · have hbound := hss i
              rw [hvi] at hbound
              exact Option.some.inj (hbound.symm.trans hlookup)
          · obtain ⟨d, hd, htype⟩ := target_respects_P hv hlookup
            refine ⟨d, ?_, htype⟩
            rw [Function.updates_of_not_mem ThetaP vs _ v hvs]
            exact hd
        have specs_true_upd : ∀ ss : Fin vs.length → SMT.Dom,
            (∀ i, St3.types.lookup vs[i] = some (ss i).snd.fst) →
            SpecBodiesTrue
              (Function.updates ThetaP vs
                ((List.ofFn ss).map Option.some)) St3.types [] := by
          intro ss hss
          simp [SpecBodiesTrue, specBodies]
        have ambient_P : ∀ v ∈ B.fv P, v ∉ vs →
            match Xi v, ThetaP v with
            | some d, some d' => RDomCastSupported d d'
            | _, _ => False := by
          intro v hv hvs
          exact related_out v (B.fv.mem_collect (.inr ⟨hv, hvs⟩))
        have wf_bound : ∀ (x : ZFSet.{u}) (hx : x ∈ ⟦tau⟧ᶻ)
            (_hx_D : x ∈ Dval),
            B.RenWF Ebody.context
              (Function.updates Xi vs (List.ofFn fun i => some
                (⟨x.get vs.length i, tau.get vs.length i,
                  get_mem_type_of_isTuple
                    (hasArity_of_mem_toZFSet tau_hasArity hx)
                    tau_hasArity hx⟩ : B.Dom))) := by
          intro x hx hx_D
          apply B.RenWF.updates_ofFn wf vs_nodup vs_context_disj
            vs_alphas_len
          intro i
          exact BType.get_reduce alphas_nemp vs_alphas_len i
        have P_scope : ScopedContextExtends St2.types [] St3.types :=
          P_trace.scoped_extends
        have hT_tau : T ∈ ⟦BType.set tau⟧ᶻ := by
          simpa [tau] using hT
        have den_collect_tau :
            ⟦(B.Term.collect vs D P).abstract Xi Xi_fv⟧ᴮ =
              some (⟨T, BType.set tau, hT_tau⟩ : B.Dom) := by
          simpa only [tau, proof_irrel_heq] using den_t
        obtain ⟨lamVal, hden_lambda, hrel_lambda⟩ :=
          represented_collect_set_denote_supported
            (D := D) (P := P) (tau := tau) (rho := tau') (Xi := Xi)
            (Dval := Dval) (hDval := hDval) (T := T) (hT := hT_tau)
            (Denc := Denc) (Penc := Penc) (ite_body := body) (z := z)
            (ThetaD := ThetaP)
            (DencVal := (⟨DencZF, tau'.fun SMTType.bool,
              hDencMem⟩ : SMT.Dom))
            (GammaOut := St5.types) (GammaBody := St3.types)
            (Ebody := Ebody) (LambdaP := St2.types) (GammaP := St3.types)
            (DltP := []) (sigmaP := SMTType.bool)
            vs_nemp vs_nodup tau'_supported Xi_fv tau_hasArity den_D
            den_collect_tau body_def hcov_lambda
            (by simpa [body] using typ_lambda) target_respects_lambda_out
            hcov_D_upd hden_D_upd (by rfl) hDenc_func D_rel
            hcov_body_upd typ_ite Theta_wt hcov_sub_upd
            hcov_P_upd hvs_not_bv
            z_not_bv_Penc z_not_vs typ_P_body P_guard P_scope typ_Penc
            ambient_P wf_bound bound_expected source_respects_upd
            target_respects_upd specs_true_upd z_not_fv_Penc
        have hlam_type : lamVal.snd.fst =
            tau'.fun SMTType.bool :=
          SMT.RenamingContext.denote_type_of_typing_fv
            (by simpa [body] using typ_lambda) target_respects_lambda_out
            hcov_lambda hden_lambda
        refine ⟨ThetaP, hcov_lambda, ThetaP_ext0, related_out,
          ThetaP_none_out, respects_collect_out,
          target_respects_lambda_out, ThetaP_dom_out, lamVal,
          hden_lambda, hlam_type, hrel_lambda, ?_⟩
        intro Xi_alt Xi_fv_alt Theta0_alt related_alt wf_alt
          Theta0_alt_none respects_alt Theta0_alt_dom
          T_alt hT_alt den_alt
        have Xi_fv_D_alt : ∀ v ∈ B.fv D,
            (Xi_alt v).isSome = true :=
          fun v hv => Xi_fv_alt v (B.fv.mem_collect (.inl hv))
        have related_D_alt : RValuationCastSupportedOnFV
            Xi_alt Theta0_alt D :=
          related_alt.mono_fv (fun _ hv => B.fv.mem_collect (.inl hv))
        have respects_D_alt :
            B.RenamingContext.RespectsTypeContextOnFV
              Theta0_alt St0.types D :=
          respects_alt.mono_fv (fun _ hv => B.fv.mem_collect (.inl hv))
        obtain ⟨Dval_alt, hDval_alt, den_D_alt⟩ :=
          B.denote_collect_domain_exists Xi_fv_alt typ_D wf_alt den_alt
        have Theta0_alt_none_D : ∀ v ∉ St1.env.usedVars,
            Theta0_alt v = none := by
          intro v hv
          by_contra hne
          have hv_St0 : v ∈ St0.types := Theta0_alt_dom v hne
          have hv_used : v ∈ used := by
            rw [← St0_used_eq]
            exact St0_sub hv_St0
          exact hv (D_used_sub hv_used)
        obtain ⟨ThetaD_alt, hcov_D_alt, DencVal_alt,
            ThetaD_alt_ext, related_D_alt_out, ThetaD_alt_none,
            respects_D_alt_out, target_respects_D_alt, ThetaD_alt_dom,
            hden_Denc_alt, hDenc_type_alt, D_rel_alt⟩ :=
          D_total Xi_alt Xi_fv_D_alt Theta0_alt related_D_alt wf_alt
            Theta0_alt_none_D respects_D_alt Theta0_alt_dom
            Dval_alt hDval_alt den_D_alt
        let XiP_alt : B.RenamingContext.Context :=
          Function.updates Xi_alt vs
            (List.ofFn fun i => some (xs i))
        let ThetaP0_alt : SMT.RenamingContext.Context :=
          Function.updates ThetaD_alt vs
            ((List.ofFn ss).map Option.some)
        have wf_P_alt : B.RenWF Ebody.context XiP_alt := by
          dsimp [XiP_alt]
          exact B.RenWF.updates_ofFn wf_alt vs_nodup vs_context_disj
            vs_alphas_len xs_type
        obtain ⟨XiP_fv_alt, Pval_alt, hPval_alt, den_P_alt⟩ :=
          B.denote_collect_default_predicate_exists Xi_fv_alt vs_nemp
            vs_nodup tau_hasArity den_D_alt den_alt typ_P_body wf_P_alt
        have related_collect_D_alt :
            RValuationCastSupportedOnFV Xi_alt ThetaD_alt
              (B.Term.collect vs D P) :=
          related_alt.of_extends ThetaD_alt_ext
        have related_P_alt : RValuationCastSupportedOnFV
            XiP_alt ThetaP0_alt P := by
          dsimp [XiP_alt, ThetaP0_alt]
          rw [hThetaP0_map]
          apply RValuationCastSupportedOnFV.updates vs_nodup xs ss
          · intro v hv hv_not_vs
            exact related_collect_D_alt v
              (B.fv.mem_collect (.inr ⟨hv, hv_not_vs⟩))
          · intro i
            let jalpha : Fin alphas.length := Fin.cast vs_alphas_len i
            have hcomp := RDomCastSupported.get_of_reduce_toProdl
              alphas_nemp alphas_sigmas_len
              BType.mem_toZFSet_of_defaultZFSet hYrun_prodl
              run_rel_prodl jalpha
            have hsource : xs i =
                (⟨tau.defaultZFSet.get alphas.length jalpha,
                  alphas[jalpha],
                  BType.mem_get_of_mem_reduce_toZFSet alphas_nemp
                    BType.mem_toZFSet_of_defaultZFSet⟩ : B.Dom) := by
              exact B.Dom.ext_type_value
                (BType.get_reduce alphas_nemp vs_alphas_len i)
                (ZFSet.get_cast vs_alphas_len i)
            rw [hsource]
            simpa [ss, jalpha] using hcomp
        have ThetaP0_alt_none_St2 : ∀ v ∉ St2.env.usedVars,
            ThetaP0_alt v = none := by
          intro v hv
          dsimp [ThetaP0_alt]
          apply SMT.RenamingContext.updates_none_of_mem_used
            (fun w hw => by
              rw [St2_used]
              exact encodeTerm_state.mem_foldl_cons_of_mem _ _
                (D_used_sub (vars_used_vs w hw)))
            (fun w hw => ThetaD_alt_none w (fun h =>
              hw (St1_sub_St2_used h))) v hv
        have ThetaP0_alt_none : ∀ v ∉ St3.env.usedVars,
            ThetaP0_alt v = none := by
          intro v hv
          apply ThetaP0_alt_none_St2 v
          intro hv_St2
          exact hv (P_used_sub hv_St2)
        have ThetaP0_alt_dom : ∀ v, ThetaP0_alt v ≠ none →
            v ∈ St2.types := by
          dsimp [ThetaP0_alt]
          exact SMT.RenamingContext.updates_dom_of_typed_bounds
            (fun v hv =>
              AList.mem_of_subset St1_sub_St2 (ThetaD_alt_dom v hv))
            hbound_type
        have respects_P_alt :
            B.RenamingContext.RespectsTypeContextOnFV
              ThetaP0_alt St2.types P := by
          dsimp [ThetaP0_alt]
          apply B.RenamingContext.RespectsTypeContextOnFV.updates_of_typed_bounds
            vs_nodup
          · intro v hv hv_not_vs sigma hlookup
            have hv_collect : v ∈ B.fv (B.Term.collect vs D P) :=
              B.fv.mem_collect (.inr ⟨hv, hv_not_vs⟩)
            have hv_St0 : v ∈ St0.types := fv_in_Lambda v hv_collect
            obtain ⟨sigma0, hsigma0⟩ := Option.isSome_iff_exists.mp
              (AList.lookup_isSome.mpr hv_St0)
            have hsigma1 : St1.types.lookup v = some sigma0 :=
              AList.lookup_of_subset D_types_sub hsigma0
            have hsigma2 : St2.types.lookup v = some sigma0 := by
              rw [St2_types]
              apply foldl_insert_preserves_lookup hsigma1
              intro p hp hpv
              apply hv_not_vs
              rw [← hpv]
              exact (List.of_mem_zip hp).1
            rw [hsigma2] at hlookup
            cases hlookup
            obtain ⟨d, hd, hdty⟩ := respects_alt hv_collect hsigma0
            exact ⟨d, ThetaD_alt_ext hd, hdty⟩
          · exact hbound_type
        obtain ⟨ThetaP_alt, hcov_P_alt, PencVal_alt,
            ThetaP_alt_ext, related_P_alt_out, ThetaP_alt_none,
            respects_P_alt_out, target_respects_P_alt, ThetaP_alt_dom,
            hden_Penc_alt, hPenc_type_alt, P_rel_alt⟩ :=
          P_total XiP_alt XiP_fv_alt ThetaP0_alt related_P_alt wf_P_alt
            ThetaP0_alt_none respects_P_alt ThetaP0_alt_dom
            Pval_alt hPval_alt den_P_alt
        have ThetaP0_alt_ext : SMT.RenamingContext.Extends
            ThetaP0_alt ThetaD_alt := by
          intro v d hv
          dsimp [ThetaP0_alt]
          by_cases hvs : v ∈ vs
          · have hnone : ThetaD_alt v = none := by
              cases hTheta : ThetaD_alt v with
              | none => rfl
              | some d' =>
                  exfalso
                  exact vs_disj_St1 v hvs
                    (ThetaD_alt_dom v (by rw [hTheta]; simp))
            rw [hnone] at hv
            cases hv
          · rw [Function.updates_of_not_mem _ _ _ _ hvs]
            exact hv
        have ThetaP_alt_ext_D : SMT.RenamingContext.Extends
            ThetaP_alt ThetaD_alt :=
          SMT.RenamingContext.extends_trans ThetaP_alt_ext ThetaP0_alt_ext
        have ThetaP_alt_ext0 : SMT.RenamingContext.Extends
            ThetaP_alt Theta0_alt :=
          SMT.RenamingContext.extends_trans ThetaP_alt_ext_D ThetaD_alt_ext
        have related_out_alt : RValuationCastSupportedOnFV
            Xi_alt ThetaP_alt (B.Term.collect vs D P) :=
          related_alt.of_extends ThetaP_alt_ext0
        have respects_collect_alt :
            B.RenamingContext.RespectsTypeContextOnFV
              ThetaP_alt St5.types (B.Term.collect vs D P) := by
          apply B.RenamingContext.RespectsTypeContextOnFV.of_extends
            respects_alt ThetaP_alt_ext0 St0_sub_St5
          · intro v hv
            exact hv
          · exact fv_in_Lambda
        have ThetaP_alt_none_out : ∀ v ∉ St5.env.usedVars,
            ThetaP_alt v = none := by
          intro v hv
          apply ThetaP_alt_none v
          rw [St5_used_chain] at hv
          simp only [List.mem_cons, not_or] at hv
          exact hv.2
        have ThetaP_alt_dom_out : ∀ v, ThetaP_alt v ≠ none →
            v ∈ St5.types := by
          intro v hv
          rw [St5_types_eq]
          exact ThetaP_alt_dom v hv
        have hcov_D_ThetaP_alt :
            SMT.RenamingContext.CoversFV ThetaP_alt Denc := by
          intro v hv
          obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (hcov_D_alt v hv)
          exact Option.isSome_of_eq_some (ThetaP_alt_ext_D hd)
        have hagree_D_alt : SMT.RenamingContext.AgreesOnFV
            ThetaD_alt ThetaP_alt Denc := by
          intro v hv
          obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (hcov_D_alt v hv)
          exact hd.trans (ThetaP_alt_ext_D hd).symm
        have hden_D_ThetaP_alt_eq :
            ⟦Denc.abstract ThetaP_alt hcov_D_ThetaP_alt⟧ˢ =
              ⟦Denc.abstract ThetaD_alt hcov_D_alt⟧ˢ := by
          change SMT.RenamingContext.denote ThetaP_alt Denc
              hcov_D_ThetaP_alt =
            SMT.RenamingContext.denote ThetaD_alt Denc hcov_D_alt
          exact (SMT.RenamingContext.denote_congr_of_agreesOnFV
            (h1 := hcov_D_alt) (h2 := hcov_D_ThetaP_alt)
            hagree_D_alt).symm
        have hcov_D_upd_alt : ∀ W : SMT.Dom,
            SMT.RenamingContext.CoversFV
              (Function.update ThetaP_alt z (some W)) Denc := by
          intro W
          exact SMT.RenamingContext.coversFV_update_of_notMem
            z_not_fv_Denc hcov_D_ThetaP_alt
        have hden_D_upd_alt : ∀ W : SMT.Dom,
            ⟦Denc.abstract (Function.update ThetaP_alt z (some W))
              (hcov_D_upd_alt W)⟧ˢ = some DencVal_alt := by
          intro W
          calc
            ⟦Denc.abstract (Function.update ThetaP_alt z (some W))
                (hcov_D_upd_alt W)⟧ˢ =
                ⟦Denc.abstract ThetaP_alt hcov_D_ThetaP_alt⟧ˢ := by
              change SMT.RenamingContext.denote
                  (Function.update ThetaP_alt z (some W)) Denc
                    (hcov_D_upd_alt W) =
                SMT.RenamingContext.denote ThetaP_alt Denc
                  hcov_D_ThetaP_alt
              exact (SMT.RenamingContext.denote_update_of_notMem
                (h := hcov_D_ThetaP_alt) z_not_fv_Denc).symm
            _ = ⟦Denc.abstract ThetaD_alt hcov_D_alt⟧ˢ :=
              hden_D_ThetaP_alt_eq
            _ = some DencVal_alt := hden_Denc_alt
        have target_respects_D_ThetaP_alt :
            SMT.RenamingContext.RespectsTypeContextOnFV
              ThetaP_alt St3.types Denc :=
          SMT.RenamingContext.RespectsTypeContextOnFV.of_extends
            target_respects_D_alt ThetaP_alt_ext_D St1_sub_St3 typ_Denc
        have hcov_sub_upd_alt : ∀ W : SMT.Dom,
            SMT.RenamingContext.CoversFV
              (Function.update ThetaP_alt z (some W))
              (SMT.substList vs (toDestPair vs (.var z)) Penc) := by
          intro W v hv
          rcases SMT_mem_fv_substList hv with hv_P | ⟨t, ht, hv_t⟩
          · rw [Function.update_of_ne (by
                intro heq
                exact z_not_fv_Penc (heq ▸ hv_P))]
            exact hcov_P_alt v hv_P
          · have hvz := SMT_fv_toDestPair_subset ht hv_t
            subst v
            simp
        have hcov_body_upd_alt : ∀ W : SMT.Dom,
            SMT.RenamingContext.CoversFV
              (Function.update ThetaP_alt z (some W)) body := by
          intro W v hv
          rw [body_def] at hv
          simp only [SMT.fv, List.mem_append, List.mem_singleton,
            List.not_mem_nil, or_false] at hv
          rcases hv with (hv_D | rfl) | hv_sub
          · exact hcov_D_upd_alt W v hv_D
          · simp
          · exact hcov_sub_upd_alt W v hv_sub
        have hcov_lambda_alt : SMT.RenamingContext.CoversFV ThetaP_alt
            ((λˢ [z]) [tau'] body) := by
          intro v hv
          simp only [SMT.fv, List.mem_removeAll_iff] at hv
          obtain ⟨hv_body, hv_ne_z⟩ := hv
          have hvz : v ≠ z := List.mem_singleton.not.mp hv_ne_z
          have hcov := hcov_body_upd_alt PencVal_alt v hv_body
          rw [Function.update_of_ne hvz] at hcov
          exact hcov
        have target_respects_lambda_alt :
            SMT.RenamingContext.RespectsTypeContextOnFV
              ThetaP_alt St3.types ((λˢ [z]) [tau'] body) := by
          intro v sigma hv hlookup
          simp only [SMT.fv, List.mem_removeAll_iff] at hv
          obtain ⟨hv_body, hv_ne_z⟩ := hv
          have hvz : v ≠ z := List.mem_singleton.not.mp hv_ne_z
          rw [body_def] at hv_body
          simp only [SMT.fv, List.mem_append, List.mem_singleton,
            List.not_mem_nil, or_false] at hv_body
          rcases hv_body with (hv_D | hv_var) | hv_sub
          · exact target_respects_D_ThetaP_alt hv_D hlookup
          · exact absurd hv_var hvz
          · rcases SMT_mem_fv_substList hv_sub with hv_P |
                ⟨t, ht, hv_t⟩
            · exact target_respects_P_alt hv_P hlookup
            · exact absurd (SMT_fv_toDestPair_subset ht hv_t) hvz
        have target_respects_lambda_out_alt :
            SMT.RenamingContext.RespectsTypeContextOnFV
              ThetaP_alt St5.types ((λˢ [z]) [tau'] body) := by
          rw [St5_types_eq]
          exact target_respects_lambda_alt
        have Theta_wt_alt : ∀ v ∈ SMT.fv body, ∀ d : SMT.Dom,
            ThetaP_alt v = some d → ∀ sigma,
              St3.types.lookup v = some sigma → d.snd.fst = sigma := by
          intro v hv d hd sigma hlookup
          by_cases hvz : v = z
          · subst v
            have hz_none : ThetaP_alt z = none :=
              ThetaP_alt_none z z_not_used
            rw [hz_none] at hd
            contradiction
          · obtain ⟨d', hd', htype⟩ := target_respects_lambda_alt
                (by
                  simp only [SMT.fv, List.mem_removeAll_iff]
                  exact ⟨hv, List.mem_singleton.not.mpr hvz⟩)
                hlookup
            rw [hd] at hd'
            cases hd'
            exact htype
        have hgo_cov_alt : ∀ x ∈ SMT.fv body, x ∉ [z] →
            (ThetaP_alt x).isSome = true := by
          intro x hx hxz
          apply hcov_lambda_alt x
          simp only [SMT.fv, List.mem_removeAll_iff]
          exact ⟨hx, hxz⟩
        have hcov_P_upd_alt : ∀ (W : SMT.Dom)
            (ss : Fin vs.length → SMT.Dom),
            SMT.RenamingContext.CoversFV
              (Function.updates (Function.update ThetaP_alt z (some W)) vs
                ((List.ofFn ss).map Option.some)) Penc := by
          intro W ss v hv
          by_cases hvs : v ∈ vs
          · rw [Function.updates_eq_if
                (by rw [List.length_map, List.length_ofFn]) vs_nodup,
              dif_pos hvs]
            simp
          · rw [Function.updates_of_not_mem _ vs _ _ hvs,
              Function.update_of_ne (by
                intro heq
                exact z_not_fv_Penc (heq ▸ hv))]
            exact hcov_P_alt v hv
        have hDenc_type_alt' : DencVal_alt.snd.fst =
            tau'.fun SMTType.bool := by
          simpa using hDenc_type_alt
        have hDenc_func_alt : ⟦tau'⟧ᶻ.IsFunc
            𝔹 DencVal_alt.fst := by
          have hmem : DencVal_alt.fst ∈
              ⟦tau'.fun SMTType.bool⟧ᶻ := by
            rw [← hDenc_type_alt']
            exact DencVal_alt.snd.snd
          rw [SMTType.toZFSet] at hmem
          exact ZFSet.mem_funs.mp hmem
        have source_respects_upd_alt : ∀ ss : Fin vs.length → SMT.Dom,
            (∀ i, St3.types.lookup vs[i] = some (ss i).snd.fst) →
            B.RenamingContext.RespectsTypeContextOnFV
              (Function.updates ThetaP_alt vs
                ((List.ofFn ss).map Option.some)) St3.types P := by
          intro ss hss
          apply B.RenamingContext.RespectsTypeContextOnFV.updates_of_typed_bounds
            vs_nodup
          · intro v hv hvs sigma hlookup
            exact respects_P_alt_out hv hlookup
          · exact hss
        have target_respects_upd_alt : ∀ ss : Fin vs.length → SMT.Dom,
            (∀ i, St3.types.lookup vs[i] = some (ss i).snd.fst) →
            SMT.RenamingContext.RespectsTypeContextOnFV
              (Function.updates ThetaP_alt vs
                ((List.ofFn ss).map Option.some)) St3.types Penc := by
          intro ss hss v sigma hv hlookup
          by_cases hvs : v ∈ vs
          · let i : Fin vs.length :=
              ⟨vs.idxOf v, List.idxOf_lt_length_of_mem hvs⟩
            have hvi : vs[i] = v := List.getElem_idxOf i.isLt
            refine ⟨ss i, ?_, ?_⟩
            · rw [Function.updates_eq_if (by simp) vs_nodup,
                dif_pos hvs]
              simp only [List.getElem_map, List.getElem_ofFn]
              congr 1
            · have hbound := hss i
              rw [hvi] at hbound
              exact Option.some.inj (hbound.symm.trans hlookup)
          · obtain ⟨d, hd, htype⟩ := target_respects_P_alt hv hlookup
            refine ⟨d, ?_, htype⟩
            rw [Function.updates_of_not_mem ThetaP_alt vs _ v hvs]
            exact hd
        have specs_true_upd_alt : ∀ ss : Fin vs.length → SMT.Dom,
            (∀ i, St3.types.lookup vs[i] = some (ss i).snd.fst) →
            SpecBodiesTrue
              (Function.updates ThetaP_alt vs
                ((List.ofFn ss).map Option.some)) St3.types [] := by
          intro ss hss
          simp [SpecBodiesTrue, specBodies]
        have ambient_P_alt : ∀ v ∈ B.fv P, v ∉ vs →
            match Xi_alt v, ThetaP_alt v with
            | some d, some d' => RDomCastSupported d d'
            | _, _ => False := by
          intro v hv hvs
          exact related_out_alt v
            (B.fv.mem_collect (.inr ⟨hv, hvs⟩))
        have wf_bound_alt : ∀ (x : ZFSet.{u})
            (hx : x ∈ ⟦tau⟧ᶻ) (_hx_D : x ∈ Dval_alt),
            B.RenWF Ebody.context
              (Function.updates Xi_alt vs (List.ofFn fun i => some
                (⟨x.get vs.length i, tau.get vs.length i,
                  get_mem_type_of_isTuple
                    (hasArity_of_mem_toZFSet tau_hasArity hx)
                    tau_hasArity hx⟩ : B.Dom))) := by
          intro x hx hx_D
          apply B.RenWF.updates_ofFn wf_alt vs_nodup vs_context_disj
            vs_alphas_len
          intro i
          exact BType.get_reduce alphas_nemp vs_alphas_len i
        have hT_alt_tau : T_alt ∈ ⟦BType.set tau⟧ᶻ := by
          simpa [tau] using hT_alt
        have den_collect_alt_tau :
            ⟦(B.Term.collect vs D P).abstract Xi_alt Xi_fv_alt⟧ᴮ =
              some (⟨T_alt, BType.set tau, hT_alt_tau⟩ : B.Dom) := by
          simpa only [tau, proof_irrel_heq] using den_alt
        obtain ⟨lamVal_alt, hden_lambda_alt, hrel_lambda_alt⟩ :=
          represented_collect_set_denote_supported
            (D := D) (P := P) (tau := tau) (rho := tau') (Xi := Xi_alt)
            (Dval := Dval_alt) (hDval := hDval_alt)
            (T := T_alt) (hT := hT_alt_tau)
            (Denc := Denc) (Penc := Penc) (ite_body := body) (z := z)
            (ThetaD := ThetaP_alt) (DencVal := DencVal_alt)
            (GammaOut := St5.types) (GammaBody := St3.types)
            (Ebody := Ebody) (LambdaP := St2.types) (GammaP := St3.types)
            (DltP := []) (sigmaP := SMTType.bool)
            vs_nemp vs_nodup tau'_supported Xi_fv_alt tau_hasArity
            den_D_alt den_collect_alt_tau body_def hcov_lambda_alt
            (by simpa [body] using typ_lambda)
            target_respects_lambda_out_alt hcov_D_upd_alt hden_D_upd_alt
            hDenc_type_alt' hDenc_func_alt D_rel_alt hcov_body_upd_alt
            typ_ite Theta_wt_alt hcov_sub_upd_alt hcov_P_upd_alt hvs_not_bv
            z_not_bv_Penc z_not_vs typ_P_body P_guard P_scope typ_Penc
            ambient_P_alt wf_bound_alt bound_expected source_respects_upd_alt
            target_respects_upd_alt specs_true_upd_alt z_not_fv_Penc
        have hlam_type_alt : lamVal_alt.snd.fst =
            tau'.fun SMTType.bool :=
          SMT.RenamingContext.denote_type_of_typing_fv
            (by simpa [body] using typ_lambda)
            target_respects_lambda_out_alt hcov_lambda_alt hden_lambda_alt
        refine ⟨ThetaP_alt, hcov_lambda_alt, lamVal_alt,
          ThetaP_alt_ext0, related_out_alt, ThetaP_alt_none_out,
          respects_collect_alt, target_respects_lambda_out_alt,
          ThetaP_alt_dom_out, hden_lambda_alt, hlam_type_alt, ?_⟩
        simpa only [tau, proof_irrel_heq] using hrel_lambda_alt
    · exact wp_bind_throw _ _ _ _
  · mvcgen
