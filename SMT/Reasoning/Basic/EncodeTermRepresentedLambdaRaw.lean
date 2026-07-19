import SMT.Reasoning.Basic.EncodeTermRepresentedLambda

open Std.Do B SMT ZFSet

/-- The lambda proof first establishes the ordinary semantic witnesses together
with the stronger declaration-aware totality theorem.  Keeping the latter in
the same package lets the public and scoped postconditions share the complete
operational proof. -/
private abbrev LambdaScopedSemanticPost.{u}
    (t : B.Term) (alpha : BType) (Lambda : SMT.TypeContext)
    (Xi : B.RenamingContext.Context)
    (Theta0 : SMT.RenamingContext.Context.{u})
    (T : ZFSet.{u}) (hT : T ∈ ⟦alpha⟧ᶻ)
    (E : B.Env) (t' : SMT.Term) (sigma : SMTType)
    (E' : SMT.Env) (Gamma' : SMT.TypeContext)
    (Dlt : SMT.Chunk) : Prop :=
  Nonempty (sigma ~> alpha.toSMTType) ∧
  (Gamma' ⊢ˢ t' : sigma) ∧
  EncodeTermResultShape t t' sigma ∧
  ∃ (Theta' : SMT.RenamingContext.Context.{u})
    (Theta'_covers : RenamingContext.CoversFV Theta' t'),
    RenamingContext.Extends Theta' Theta0 ∧
    RValuationCastSupportedOnFV Xi Theta' t ∧
    (∀ v ∉ E'.usedVars, Theta' v = none) ∧
    B.RenamingContext.RespectsTypeContextOnFV Theta' Gamma' t ∧
    SMT.RenamingContext.RespectsTypeContextOnFV Theta' Gamma' t' ∧
    (∀ v, Theta' v ≠ none → v ∈ Gamma') ∧
    ∃ denT' : SMT.Dom.{u},
      ⟦t'.abstract Theta' Theta'_covers⟧ˢ = some denT' ∧
      denT'.snd.fst = sigma ∧
      RDomCastSupported (⟨T, alpha, hT⟩ : B.Dom) denT' ∧
      EncodeTermRepScopedTotal.{u}
        t E alpha Lambda t' sigma Gamma' E'.usedVars Dlt

set_option maxHeartbeats 8000000 in
theorem encodeTerm_rep_spec.lambda_case_and_scoped.{u}
    (vs : List B.𝒱) (D P : B.Term)
    (D_ih : EncodeTermRepIH.{u} D)
    (P_ih : EncodeTermRepIH.{u} P)
    (D_scoped : EncodeTermRepScopedIH.{u} D)
    (P_scoped : EncodeTermRepScopedFromIH.{u} P)
    (E : B.Env) {Lambda : SMT.TypeContext} {alpha : BType}
    (typ_t : E.context ⊢ᴮ B.Term.lambda vs D P : alpha)
    {Xi : B.RenamingContext.Context.{u}}
    (Xi_fv : ∀ v ∈ B.fv (B.Term.lambda vs D P), (Xi v).isSome = true)
    {Theta0 : SMT.RenamingContext.Context.{u}}
    (related : RValuationCastSupportedOnFV Xi Theta0
      (B.Term.lambda vs D P))
    {used : List SMT.𝒱}
    (Theta0_none : ∀ v ∉ used, Theta0 v = none)
    (Theta0_dom : ∀ v, Theta0 v ≠ none → v ∈ Lambda)
    {T : ZFSet.{u}} {hT : T ∈ ⟦alpha⟧ᶻ}
    (den_t : ⟦(B.Term.lambda vs D P).abstract Xi Xi_fv⟧ᴮ =
      some ⟨T, ⟨alpha, hT⟩⟩)
    (vars_used : ∀ v ∈ (B.Term.lambda vs D P).vars, v ∈ used)
    (Lambda_inv : ∀ v ∈ (B.Term.lambda vs D P).vars,
      v ∈ Lambda → v ∈ E.context)
    (bv_nodup : (B.bv (B.Term.lambda vs D P)).Nodup)
    (respects : B.RenamingContext.RespectsTypeContextOnFV Theta0 Lambda
      (B.Term.lambda vs D P))
    (fv_in_Lambda : ∀ v ∈ B.fv (B.Term.lambda vs D P), v ∈ Lambda)
    (wf : B.RenWF E.context Xi)
    {n : ℕ} {decl : SMT.Chunk} :
    ⦃fun ⟨E0, Lambda'⟩ ↦
      ⌜Lambda' = Lambda ∧ E0.freshvarsc = n ∧
        Lambda.keys ⊆ E0.usedVars ∧ E0.usedVars = used ∧
        E0.declarations = decl⌝⦄
    encodeTerm (B.Term.lambda vs D P) E
    ⦃⇓? (⟨t', sigma⟩ : SMT.Term × SMTType) ⟨E', Gamma'⟩ =>
      ⌜EncodeTermRepPost (B.Term.lambda vs D P) alpha Lambda Xi Theta0
          used T hT E t' sigma E' Gamma' ∧
        EncodeTermRepScopedPost.{u} (B.Term.lambda vs D P) E alpha Lambda
          decl t' sigma E' Gamma'⌝⦄ := by
  mstart
  mintro pre ∀St0
  mpure pre
  obtain ⟨rfl, rfl, St0_keys, St0_used, St0_decl⟩ := pre
  obtain ⟨beta, alphas, Ds, vs_nemp, vs_alphas_len, vs_Ds_len,
      alpha_eq, vs_nodup, D_eq, typ_Ds, typ_P, vs_context_disj⟩ :=
    B.Typing.lambdaE typ_t
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
    dsimp only [tau]
    rw [List.reduce]
    have hlen : alphas.tail.length + 1 = vs.length := by
      rw [List.length_tail, vs_alphas_len]
      have := List.length_pos_of_ne_nil alphas_nemp
      omega
    convert BType.hasArity_of_foldl
      (α := alphas.head alphas_nemp) (αs := alphas.tail) using 1
    exact hlen.symm

  let Xi_fv_D : ∀ v ∈ B.fv D, (Xi v).isSome = true :=
    fun v hv => Xi_fv v (B.fv.mem_lambda (.inl hv))
  obtain ⟨Dval, hDval, den_D⟩ :=
    B.denote_lambda_domain_exists Xi_fv typ_D wf den_t

  have vars_used_D : ∀ v ∈ D.vars, v ∈ used := by
    intro v hv
    apply vars_used v
    simp [B.Term.vars, B.fv, B.bv, List.mem_append,
      List.mem_removeAll_iff] at hv ⊢
    rcases hv with hv | hv
    · left; left; exact hv
    · right; right; left; exact hv
  have vars_used_vs : ∀ v ∈ vs, v ∈ used := by
    intro v hv
    apply vars_used v
    simp [B.Term.vars, B.fv, B.bv, List.mem_append,
      List.mem_removeAll_iff]
    exact Or.inr (Or.inl hv)
  have vars_used_P : ∀ v ∈ P.vars, v ∈ used := by
    intro v hv
    apply vars_used v
    simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
      List.append_assoc, List.mem_append, List.mem_removeAll_iff] at hv ⊢
    by_cases hvs : v ∈ vs
    · right; left; exact hvs
    · rcases hv with hv | hv
      · left; right; exact ⟨hv, hvs⟩
      · right; right; right; exact hv

  have fv_D_sub : B.fv D ⊆ B.fv (B.Term.lambda vs D P) :=
    fun _ hv => B.fv.mem_lambda (.inl hv)
  have related_D : RValuationCastSupportedOnFV Xi Theta0 D :=
    related.mono_fv fv_D_sub
  have Lambda_inv_D : ∀ v ∈ D.vars, v ∈ St0.types → v ∈ E.context := by
    intro v hv hLambda
    apply Lambda_inv v _ hLambda
    simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
      List.append_assoc, List.mem_append, List.mem_removeAll_iff] at hv ⊢
    rcases hv with hv | hv
    · left; left; exact hv
    · right; right; left; exact hv
  have bv_D_nodup : (B.bv D).Nodup := by
    have h := bv_nodup
    simp only [B.bv] at h
    rw [List.nodup_append, List.nodup_append] at h
    exact h.1.2.1
  have bv_P_nodup : (B.bv P).Nodup := by
    have h := bv_nodup
    simp only [B.bv] at h
    rw [List.nodup_append] at h
    exact h.2.1
  have respects_D :
      B.RenamingContext.RespectsTypeContextOnFV Theta0 St0.types D :=
    respects.mono_fv (fun v hv => by
      rw [B.fv]
      exact List.mem_append_left _ hv)
  have fv_D_in : ∀ v ∈ B.fv D, v ∈ St0.types :=
    fun v hv => fv_in_Lambda v (by
      rw [B.fv]
      exact List.mem_append_left _ hv)

  rw [encodeTerm]
  mspec (Std.Do.Triple.and _
    (Std.Do.Triple.and _
      (Std.Do.Triple.and _
        (D_ih E typ_D Xi_fv_D related_D Theta0_none Theta0_dom den_D
        vars_used_D Lambda_inv_D bv_D_nodup respects_D fv_D_in wf
        (n := St0.env.freshvarsc))
        (D_scoped E typ_D Xi_fv_D related_D Theta0_none Theta0_dom den_D
          vars_used_D Lambda_inv_D bv_D_nodup respects_D fv_D_in wf
          (n := St0.env.freshvarsc)
          (decl := St0.env.declarations)))
      (SMT.encodeTerm_bv_used E (t := D)
        (used := St0.env.usedVars) (n := St0.env.freshvarsc)
        (decl := St0.env.declarations)))
    (SMT.encodeTerm_bv_notMem_used E (t := D)
      (used := St0.env.usedVars) (n := St0.env.freshvarsc)
      (decl := St0.env.declarations)))
  rename_i out_D
  obtain ⟨Denc, sigmaD⟩ := out_D
  mrename_i post_D
  mintro ∀St1
  mpure post_D
  dsimp at post_D
  obtain ⟨⟨⟨D_post, D_scoped_post⟩,
        bv_Denc_used, _D_used_sub, DltD_used,
        D_decl_used, D_delta_used⟩,
      bv_Denc_not_used, _D_not_sub, DltD_not,
        D_decl_not, D_delta_not_used⟩ := post_D
  obtain ⟨DltD, D_scoped_decl, D_op_envelope, D_root_envelope,
      D_scoped_total, D_guard, D_specs_op, D_sc_typing⟩ := D_scoped_post
  obtain ⟨DCore, D_root_trace, DCore_sub_St1⟩ := D_root_envelope
  have DltD_eq_used : DltD = DltD_used := by
    rw [D_scoped_decl] at D_decl_used
    exact List.append_right_injective _ D_decl_used
  subst DltD_used
  have DltD_eq_not : DltD = DltD_not := by
    rw [D_scoped_decl] at D_decl_not
    exact List.append_right_injective _ D_decl_not
  subst DltD_not
  obtain ⟨used_sub_St1, St0_sub_St1, St1_keys_sub, covers_D,
      D_path, typ_Denc, D_shape, D_preserves,
      ThetaD, hcov_Denc, ThetaD_ext, related_D_final, ThetaD_none,
      respects_D_final, target_respects_Denc, ThetaD_dom,
      DencVal, hden_Denc, hDenc_type, D_rel, D_total⟩ := D_post
  rcases DencVal with ⟨DencZF, sigmaDVal, hDencZF⟩
  dsimp at hDenc_type
  subst sigmaDVal
  cases sigmaD with
  | bool =>
      simp only [Prod.snd]
      mvcgen
  | int =>
      simp only [Prod.snd]
      mvcgen
  | unit =>
      simp only [Prod.snd]
      mvcgen
  | option sigma =>
      simp only [Prod.snd]
      mvcgen
  | pair sigma gamma =>
      simp only [Prod.snd]
      mvcgen
  | «fun» rho codomain =>
      cases codomain with
      | bool =>
          have rho_supported : BType.SupportedSMT tau rho := by
            rcases D_rel.supported.setE with
              ⟨rho', heq, hsupp⟩ | ⟨a, b, htau, heq⟩
            · injection heq with hrho
              subst rho'
              exact hsupp
            · simp at heq
          simp only [BType.toSMTType] at *
          let sigmas := rho.fromProdl (vs.length - 1)
          have sigmas_len : sigmas.length = vs.length := by
            simpa [sigmas] using
              rho_supported.fromProdl_length_of_hasArity tau_hasArity
          have vs_sigmas_len : vs.length = sigmas.length := sigmas_len.symm
          have sigmas_toProdl : sigmas.toProdl = rho := by
            dsimp [sigmas]
            have h_arith :
                (rho.fromProdl (vs.length - 1)).length =
                  vs.length - 1 + 1 := by
              rw [sigmas_len]
              have := List.length_pos_of_ne_nil vs_nemp
              omega
            exact SMT.SMTType.fromProdl_toProdl_roundtrip _ _ h_arith
          mspec (Std.Do.Triple.and _
            (SMT.addToContext_forIn_spec (pairs := vs.zip sigmas))
            (SMT.addToContext_forIn_decls (vs.zip sigmas)
              (decl := St1.env.declarations)))
          mrename_i post_ctx
          mintro ∀St2
          mpure post_ctx
          obtain ⟨⟨St2_types, St2_fvc, St2_used⟩, St2_decl⟩ := post_ctx
          have vs_not_D_fv : ∀ v ∈ vs, v ∉ B.fv D := by
            intro v hv hv_fv
            exact vs_context_disj v hv <| AList.lookup_isSome.mp <|
              B.Typing.mem_context_of_mem_fv typ_D hv_fv
          have vs_disj_St1 : ∀ v ∈ vs, v ∉ St1.types := by
            intro v hv hSt1
            have hv_vars_D : v ∉ B.Term.vars D :=
              B.Term.notMem_vars_iff.mpr ⟨vs_not_D_fv v hv, by
                have h := bv_nodup
                simp only [B.bv] at h
                rw [List.nodup_append, List.nodup_append] at h
                intro h_bv
                exact h.1.2.2 v hv v h_bv rfl⟩
            apply D_preserves v (vars_used_vs v hv) _ hv_vars_D hSt1
            intro hSt0
            apply vs_context_disj v hv
            apply Lambda_inv v _ hSt0
            unfold B.Term.vars
            rw [List.mem_union_iff]
            exact .inr (by
              simp only [B.bv, List.mem_append]
              exact .inl (.inl hv))
          have St2_update : St2.types =
              St1.types.update vs sigmas vs_sigmas_len := by
            rw [St2_types, SMT.TypeContext.update_eq_zip_foldl]
          have St1_sub_St2_types : St1.types ⊆ St2.types := by
            rw [St2_update]
            exact entries_subset_update_of_fresh
              vs_disj_St1 vs_sigmas_len
          have St1_sub_St2_used : St1.env.usedVars ⊆
              St2.env.usedVars := by
            rw [St2_used]
            intro v hv
            suffices ∀ (ps : List (SMT.𝒱 × SMTType))
                (acc : List SMT.𝒱), v ∈ acc →
                v ∈ ps.foldl (fun us p => p.1 :: us) acc by
              exact this _ _ hv
            intro ps
            induction ps with
            | nil => exact fun _ h => h
            | cons p ps ih =>
                intro acc h
                exact ih _ (List.mem_cons_of_mem p.1 h)
          have St2_keys_sub : St2.types.keys ⊆
              St2.env.usedVars := by
            rw [St2_types, St2_used]
            exact encodeTerm_state.keys_foldl_insert_subset_foldl_cons
              (vs.zip sigmas) St1_keys_sub

          have DCore_update_sub_St2 :
              (DCore.update vs sigmas vs_sigmas_len).entries ⊆
              St2.types.entries := by
            rw [St2_update]
            exact SMT.TypeContext.update_mono DCore St1.types
              vs_sigmas_len DCore_sub_St1
          have P_input_envelope : DeclarationContextEnvelope
              (DCore.update vs sigmas vs_sigmas_len) [] St2.types :=
            (DeclarationContextEnvelope.refl
              (DCore.update vs sigmas vs_sigmas_len)).mono
                DCore_update_sub_St2
          have fv_P_in_body_base : ∀ v ∈ B.fv P,
              v ∈ DCore.update vs sigmas vs_sigmas_len := by
            intro v hv
            rw [SMT.TypeContext.mem_update_iff DCore v vs sigmas
              vs_sigmas_len]
            by_cases hvs : v ∈ vs
            · exact Or.inl hvs
            · exact Or.inr <| AList.mem_of_subset
                D_root_trace.entries_subset <| fv_in_Lambda v <|
                  B.fv.mem_lambda (.inr ⟨hv, hvs⟩)

          let Ebody : B.Env :=
            { E with context := vs.zipToAList alphas ∪ E.context }
          have wf_seed : ∀ (x_fin : Fin vs.length → B.Dom.{u}),
              (∀ i, (x_fin i).snd.fst = tau.get vs.length i) →
              B.RenWF Ebody.context (Function.updates Xi vs
                (List.ofFn fun i => some (x_fin i))) := by
            intro x_fin hx_fin
            exact B.RenWF.updates_ofFn wf vs_nodup vs_context_disj
              vs_alphas_len (fun i => by
                calc
                  (x_fin i).snd.fst = tau.get vs.length i := hx_fin i
                  _ = alphas[Fin.cast vs_alphas_len i] := by
                    simpa [tau] using
                      BType.get_reduce alphas_nemp vs_alphas_len i)
          obtain ⟨x, hx, hx_origin, hseed⟩ :=
            B.denote_lambda_seed_body_exists Xi_fv vs_nemp vs_nodup
              tau_hasArity den_D den_t typ_P wf_seed
          obtain ⟨XiP_fv_seed, Pval, hPval, den_P_seed⟩ := hseed

          obtain ⟨y, hy, hxy⟩ : ∃ (y : ZFSet.{u})
              (hy : y ∈ ⟦rho⟧ᶻ),
              RDomCastSupported
                (⟨x, tau, hx⟩ : B.Dom)
                (⟨y, rho, hy⟩ : SMT.Dom) := by
            rcases hx_origin with hxD | hx_default
            · obtain ⟨y, hy, hrel⟩ :=
                D_rel.setPred_member_preimage hxD
              exact ⟨y, hy, by
                simpa only [proof_irrel_heq] using hrel⟩
            · subst x
              exact ⟨rho.defaultZFSet,
                SMTType.mem_toZFSet_of_defaultZFSet, by
                  simpa only [proof_irrel_heq] using
                    RDomCastSupported.default_of_supported
                      rho_supported⟩
          have alphas_sigmas_len : alphas.length = sigmas.length :=
            vs_alphas_len.symm.trans vs_sigmas_len
          have hy_prodl : y ∈ ⟦sigmas.toProdl⟧ᶻ := by
            rw [sigmas_toProdl]
            exact hy
          have hxy_prodl : RDomCastSupported
              (⟨x, alphas.reduce (· ×ᴮ ·) alphas_nemp, hx⟩ : B.Dom)
              (⟨y, sigmas.toProdl, hy_prodl⟩ : SMT.Dom) := by
            simpa only [tau, sigmas_toProdl, proof_irrel_heq] using hxy
          let bs : Fin vs.length → B.Dom.{u} := fun i =>
            ⟨x.get vs.length i, tau.get vs.length i,
              get_mem_type_of_isTuple
                (hasArity_of_mem_toZFSet tau_hasArity hx)
                tau_hasArity hx⟩
          let ss : Fin vs.length → SMT.Dom.{u} := fun i =>
            let j : Fin sigmas.length := Fin.cast vs_sigmas_len i
            ⟨y.get sigmas.length j, sigmas[j],
              SMTType.mem_get_of_mem_toProdl
                (fun hs => alphas_nemp (List.length_eq_zero_iff.mp
                  (alphas_sigmas_len.trans (by simp [hs]))))
                hy_prodl⟩
          let XiP := Function.updates Xi vs
            (List.ofFn fun i => some (bs i))
          let ThetaP := Function.updates ThetaD vs
            (List.ofFn fun i => some (ss i))
          have ambient_P : ∀ v ∈ B.fv P, v ∉ vs →
              match Xi v, ThetaD v with
              | some source, some target =>
                  RDomCastSupported source target
              | _, _ => False := by
            intro v hv hvs
            exact related.of_extends ThetaD_ext v
              (B.fv.mem_lambda (.inr ⟨hv, hvs⟩))
          have related_P :
              RValuationCastSupportedOnFV XiP ThetaP P := by
            dsimp only [XiP, ThetaP]
            apply RValuationCastSupportedOnFV.updates
              vs_nodup bs ss ambient_P
            intro i
            let jalpha : Fin alphas.length :=
              Fin.cast vs_alphas_len i
            have hcomp :=
              RDomCastSupported.get_of_reduce_toProdl
                alphas_nemp alphas_sigmas_len hx hy_prodl
                hxy_prodl jalpha
            have hsource : bs i =
                (⟨x.get alphas.length jalpha, alphas[jalpha],
                  BType.mem_get_of_mem_reduce_toZFSet
                    alphas_nemp hx⟩ : B.Dom) := by
              exact B.Dom.ext_type_value
                (BType.get_reduce alphas_nemp vs_alphas_len i)
                (ZFSet.get_cast vs_alphas_len i)
            rw [hsource]
            simpa [ss, jalpha] using hcomp
          have XiP_fv : ∀ v ∈ B.fv P, (XiP v).isSome = true := by
            simpa [XiP, bs] using XiP_fv_seed
          have den_P : ⟦P.abstract XiP XiP_fv⟧ᴮ =
              some (⟨Pval, beta, hPval⟩ : B.Dom) := by
            simpa only [XiP, bs, proof_irrel_heq] using den_P_seed
          have vs_used_St2 : ∀ v ∈ vs, v ∈ St2.env.usedVars := by
            intro v hv
            rw [St2_used]
            have hpair : (v, sigmas[vs.idxOf v]'(by
                rw [sigmas_len]
                exact List.idxOf_lt_length_of_mem hv)) ∈
                vs.zip sigmas := by
              have hidx : vs.idxOf v < (vs.zip sigmas).length := by
                simp only [List.length_zip]
                have hvlt := List.idxOf_lt_length_of_mem hv
                omega
              have hm := List.getElem_mem (l := vs.zip sigmas) hidx
              simpa only [List.getElem_zip,
                List.getElem_idxOf (List.idxOf_lt_length_of_mem hv)] using hm
            have hpreserve : ∀ (ps : List (SMT.𝒱 × SMTType))
                (acc : List SMT.𝒱) (w : SMT.𝒱), w ∈ acc →
                w ∈ ps.foldl (fun us q => q.1 :: us) acc := by
              intro ps
              induction ps with
              | nil => exact fun _ _ h => h
              | cons q qs ih =>
                  intro acc w hw
                  exact ih _ _ (List.mem_cons_of_mem q.1 hw)
            have hfold : ∀ (ps : List (SMT.𝒱 × SMTType))
                (acc : List SMT.𝒱) (p : SMT.𝒱 × SMTType),
                p ∈ ps → p.1 ∈
                  ps.foldl (fun us q => q.1 :: us) acc := by
              intro ps
              induction ps with
              | nil => simp
              | cons q qs ih =>
                  intro acc p hp
                  simp only [List.foldl_cons]
                  rcases List.mem_cons.mp hp with hp | hp
                  · subst p
                    exact hpreserve qs _ _ (List.mem_cons_self ..)
                  · exact ih _ _ hp
            exact hfold _ _ _ hpair
          have ThetaP_none : ∀ v ∉ St2.env.usedVars,
              ThetaP v = none := by
            intro v hv
            have hvs : v ∉ vs := fun h => hv (vs_used_St2 v h)
            change Function.updates ThetaD vs
              (List.ofFn fun i => some (ss i)) v = none
            rw [Function.updates_of_not_mem ThetaD vs _ v hvs]
            apply ThetaD_none v
            exact fun h => hv (St1_sub_St2_used h)
          have ThetaP_dom : ∀ v, ThetaP v ≠ none →
              v ∈ St2.types := by
            intro v hv
            by_cases hvs : v ∈ vs
            · rw [St2_update]
              exact (SMT.TypeContext.mem_update_iff
                St1.types v vs sigmas vs_sigmas_len).mpr (.inl hvs)
            · change Function.updates ThetaD vs
                (List.ofFn fun i => some (ss i)) v ≠ none at hv
              rw [Function.updates_of_not_mem ThetaD vs _ v hvs] at hv
              exact AList.mem_of_subset St1_sub_St2_types
                (ThetaD_dom v hv)
          have fv_P_in_St2 : ∀ v ∈ B.fv P, v ∈ St2.types := by
            intro v hv
            by_cases hvs : v ∈ vs
            · rw [St2_update]
              exact (SMT.TypeContext.mem_update_iff
                St1.types v vs sigmas vs_sigmas_len).mpr (.inl hvs)
            · exact AList.mem_of_subset St1_sub_St2_types <|
                AList.mem_of_subset St0_sub_St1 <|
                  fv_in_Lambda v
                    (B.fv.mem_lambda (.inr ⟨hv, hvs⟩))
          have respects_P :
              B.RenamingContext.RespectsTypeContextOnFV
                ThetaP St2.types P := by
            intro v sigma hv hlookup
            by_cases hvs : v ∈ vs
            · let i : Fin vs.length :=
                ⟨vs.idxOf v, List.idxOf_lt_length_of_mem hvs⟩
              have hvi : vs[i] = v :=
                List.getElem_idxOf (List.idxOf_lt_length_of_mem hvs)
              have hctx : St2.types.lookup vs[i] =
                  some sigmas[Fin.cast vs_sigmas_len i] := by
                rw [St2_update]
                exact SMT.TypeContext.lookup_update_of_mem_nodup
                  St1.types vs_nodup vs_sigmas_len i.isLt
              rw [hvi] at hctx
              rw [hctx] at hlookup
              cases hlookup
              refine ⟨ss i, ?_, rfl⟩
              change Function.updates ThetaD vs
                (List.ofFn fun i => some (ss i)) v = some (ss i)
              rw [Function.updates_eq_if (by simp) vs_nodup,
                dif_pos hvs]
              simpa [i, hvi]
            · have hv_lambda : v ∈ B.fv (B.Term.lambda vs D P) :=
                B.fv.mem_lambda (.inr ⟨hv, hvs⟩)
              have hv_St0 := fv_in_Lambda v hv_lambda
              obtain ⟨sigma0, hsigma0⟩ := Option.isSome_iff_exists.mp
                (AList.lookup_isSome.mpr hv_St0)
              have hsigma1 : St1.types.lookup v = some sigma0 :=
                AList.lookup_of_subset St0_sub_St1 hsigma0
              have hsigma2 : St2.types.lookup v = some sigma0 := by
                rw [St2_update,
                  SMT.TypeContext.lookup_update St1.types v vs sigmas
                    vs_sigmas_len hvs]
                exact hsigma1
              rw [hsigma2] at hlookup
              cases hlookup
              obtain ⟨d, hd, hdty⟩ := respects hv_lambda hsigma0
              refine ⟨d, ?_, hdty⟩
              change Function.updates ThetaD vs
                (List.ofFn fun i => some (ss i)) v = some d
              rw [Function.updates_of_not_mem ThetaD vs _ v hvs]
              exact ThetaD_ext hd
          have wf_P : B.RenWF Ebody.context XiP := by
            exact wf_seed bs (fun _ => rfl)
          have vars_used_P_St2 : ∀ v ∈ P.vars,
              v ∈ St2.env.usedVars :=
            fun v hv => St1_sub_St2_used
              (used_sub_St1 (vars_used_P v hv))
          have St2_types_sub_Ebody_on_P_vars :
              ∀ v ∈ P.vars, v ∈ St2.types → v ∈ Ebody.context := by
            intro v hv_P hv_St2
            simp only [Ebody]
            by_cases hvs : v ∈ vs
            · exact AList.mem_union.mpr <| .inl <|
                AList.mem_zipToAList_of_mem
                  vs_nodup vs_alphas_len hvs
            · apply AList.mem_union.mpr
              right
              have hv_St1 : v ∈ St1.types := by
                rw [St2_update] at hv_St2
                exact ((SMT.TypeContext.mem_update_iff
                  St1.types v vs sigmas vs_sigmas_len).mp hv_St2).resolve_left
                    hvs
              have hv_used : v ∈ used := vars_used_P v hv_P
              by_cases hv_St0 : v ∈ St0.types
              · apply Lambda_inv v _ hv_St0
                unfold B.Term.vars at hv_P ⊢
                rw [List.mem_union_iff]
                rcases List.mem_union_iff.mp hv_P with hfv | hbv
                · left
                  simp only [B.fv, List.mem_append]
                  exact .inr (List.mem_removeAll_iff.mpr ⟨hfv, hvs⟩)
                · right
                  simp only [B.bv, List.mem_append]
                  exact .inr hbv
              · have hv_Dvars : v ∈ B.Term.vars D := by
                  by_contra hnot
                  exact (D_preserves v hv_used hv_St0 hnot) hv_St1
                rcases B.Term.mem_vars_iff.mp hv_Dvars with hDfv | hDbv
                · exact AList.lookup_isSome.mp
                    (B.Typing.mem_context_of_mem_fv typ_D hDfv)
                · rcases B.Term.mem_vars_iff.mp hv_P with hPfv | hPbv
                  · have hctx := B.Typing.mem_context_of_mem_fv
                        typ_P hPfv
                    rcases AList.mem_union.mp
                        (AList.lookup_isSome.mp hctx) with hzip | hE
                    · exact absurd (AList.mem_zipToAList hzip) hvs
                    · exact hE
                  · exfalso
                    have hbn := bv_nodup
                    simp only [B.bv] at hbn
                    rw [List.nodup_append, List.nodup_append] at hbn
                    exact hbn.2.2 v
                      (List.mem_append.mpr (.inr hDbv)) v hPbv rfl

          conv in encodeTerm P E =>
            rw [encodeTerm_env_irrel P E Ebody rfl]
          mspec Std.Do.Spec.get_StateT
          mspec (Std.Do.Triple.and _
            (Std.Do.Triple.and _
              (Std.Do.Triple.and _
                (Std.Do.Triple.and _
                  (P_ih Ebody typ_P XiP_fv related_P ThetaP_none
                    ThetaP_dom den_P vars_used_P_St2
                    St2_types_sub_Ebody_on_P_vars bv_P_nodup
                    respects_P fv_P_in_St2 wf_P
                    (n := St2.env.freshvarsc))
                  (P_scoped Ebody typ_P XiP_fv related_P ThetaP_none
                    ThetaP_dom den_P vars_used_P_St2
                    St2_types_sub_Ebody_on_P_vars bv_P_nodup
                    respects_P fv_P_in_St2 wf_P
                    P_input_envelope fv_P_in_body_base
                    (ScopedSpecsTyping.nil
                      (DCore.update vs sigmas vs_sigmas_len))
                    (n := St2.env.freshvarsc)
                    (decl := St2.env.declarations)))
                (encodeTerm_decl Ebody typ_P vars_used_P_St2
                  St2_types_sub_Ebody_on_P_vars bv_P_nodup
                  (n := St2.env.freshvarsc)
                  (decl := St2.env.declarations)))
              (encodeTerm_bv_used Ebody (t := P)
                (used := St2.env.usedVars)
                (n := St2.env.freshvarsc)
                (decl := St2.env.declarations)))
            (encodeTerm_bv_notMem_used Ebody (t := P)
              (used := St2.env.usedVars)
              (n := St2.env.freshvarsc)
              (decl := St2.env.declarations)))
          rename_i out_P
          obtain ⟨Penc, gamma⟩ := out_P
          mrename_i post_P
          mintro ∀St3
          mpure post_P
          dsimp at post_P
          obtain ⟨⟨⟨⟨P_post, P_scoped_post⟩, P_decl_info⟩,
                bv_Penc_used, _, _⟩,
              bv_Penc_not_used, _, _⟩ := post_P
          obtain ⟨used_sub_St3, St2_sub_St3, St3_keys_sub,
              covers_P, P_path, typ_Penc, P_shape, P_preserves,
              ThetaBody, hcov_Penc, ThetaBody_ext, related_P_final,
              ThetaBody_none, respects_P_final,
              target_respects_Penc, ThetaBody_dom,
              PencVal, hden_Penc, hPenc_type, P_rel, P_total⟩ := P_post
          obtain ⟨DltP_scoped, P_scoped_decl, P_trace, _P_envelope,
              P_scoped_total, P_guarded, P_specs_typed,
              P_scoped_typing⟩ := P_scoped_post
          obtain ⟨DltP, P_decl_eq, P_specs_fv, Penc_fv⟩ := P_decl_info
          have DltP_scoped_eq : DltP_scoped = DltP := by
            rw [P_scoped_decl] at P_decl_eq
            exact List.append_right_injective _ P_decl_eq
          subst DltP_scoped
          rcases PencVal with ⟨PencZF, gammaVal, hPencZF⟩
          dsimp at hPenc_type
          subst gammaVal
          have gamma_supported : BType.SupportedSMT beta gamma :=
            P_rel.supported

          mspec (SMT.ensureDeclarationsUnchanged_spec (St := St3))
          mrename_i post_unchanged
          mintro ∀St3'
          mpure post_unchanged
          obtain ⟨St3'_eq, P_decl_len⟩ := post_unchanged
          subst St3'
          have DltP_nil : DltP = [] := by
            have hlen : DltP.length = 0 := by
              rw [P_decl_eq, List.length_append] at P_decl_len
              omega
            exact List.length_eq_zero_iff.mp hlen
          subst DltP
          have P_decl_stable : St3.env.declarations =
              St2.env.declarations := by
            simpa using P_decl_eq
          have Penc_fv_vars : SMT.fv Penc ⊆ B.Term.vars P := by
            intro v hv
            have h := Penc_fv hv
            simpa [List.mem_union_iff] using h
          have typ_Penc_St2 : St2.types ⊢ˢ Penc : gamma := by
            apply P_scoped_typing.1 St2.types
            · simpa using P_input_envelope.scoped_extends
            · intro v hv hvSt2
              exact SMT.Typing.bv_notMem_context typ_Penc v hv
                (AList.mem_of_subset St2_sub_St3 hvSt2)
          have Penc_fv_in_St2 : ∀ v ∈ SMT.fv Penc,
              v ∈ St2.types := by
            intro v hv
            exact SMT.Typing.mem_context_of_mem_fv typ_Penc_St2 hv

          mspec (Std.Do.Triple.and _ SMT.freshVar_spec
            (SMT.freshVar_decls (decl := St3.env.declarations)))
          rename_i z
          mrename_i post_fresh
          mintro ∀St4
          mpure post_fresh
          obtain ⟨⟨St4_types, z_fresh, St4_fvc, St4_used,
              z_not_used⟩, St4_decl⟩ := post_fresh
          let St5 : EncoderState := St4
          have St5_types : St5.types = St4.types := rfl
          have St5_fvc : St5.env.freshvarsc = St4.env.freshvarsc := rfl
          have St5_used : St5.env.usedVars = St4.env.usedVars := rfl
          mspec (Std.Do.Triple.and _ SMT.eraseFromContext_spec
            (SMT.eraseFromContext_decls (decl := St4.env.declarations)))
          mrename_i post_erase
          mintro ∀St6
          mpure post_erase
          obtain ⟨⟨St6_types, St6_fvc, St6_used⟩, St6_decl⟩ :=
            post_erase
          mspec Std.Do.Spec.pure
          mpure_intro
          have St6_used_chain : St6.env.usedVars =
              z :: St3.env.usedVars := by
            rw [St6_used, St5_used, St4_used]
          have St1_sub_St3_types : St1.types ⊆ St3.types :=
            AList.subset_trans St1_sub_St2_types St2_sub_St3
          have St6_sub_St3 : St6.types ⊆ St3.types := by
            rw [St6_types, St5_types, St4_types]
            intro ⟨k, sigma⟩ hentry
            have hk_ne_z : k ≠ z :=
              AList.fst_ne_of_mem_erase_entries hentry
            have hins := AList.erase_entries_subset z _ hentry
            rw [AList.entries_insert_of_notMem z_fresh] at hins
            exact (List.mem_cons.mp hins).elim
              (fun h => absurd (congrArg Sigma.fst h) hk_ne_z) id
          have z_not_bv_Denc : z ∉ SMT.bv Denc := fun hbv =>
            z_not_used (used_sub_St3
              (St1_sub_St2_used (bv_Denc_used z hbv)))
          have z_not_bv_Penc : z ∉ SMT.bv Penc := fun hbv =>
            z_not_used (bv_Penc_used z hbv)
          have bv_Denc_disj_St3 : ∀ v ∈ SMT.bv Denc,
              v ∉ St3.types := by
            intro v hv
            refine P_preserves v
              (St1_sub_St2_used (bv_Denc_used v hv)) ?_ ?_
            · intro hv_St2
              have hv_not_vs : v ∉ vs := fun hvs =>
                bv_Denc_not_used v hv (by
                  rw [St0_used]
                  exact vars_used_vs v hvs)
              rw [St2_update] at hv_St2
              rcases (SMT.TypeContext.mem_update_iff
                St1.types v vs sigmas vs_sigmas_len).mp hv_St2 with
                hvs | hSt1
              · exact hv_not_vs hvs
              · exact SMT.Typing.bv_notMem_context
                  typ_Denc v hv hSt1
            · intro hv_P
              exact bv_Denc_not_used v hv (by
                rw [St0_used]
                exact vars_used_P v hv_P)
          have typ_Denc_St3 : St3.types ⊢ˢ Denc :
              SMTType.fun rho SMTType.bool :=
            SMT.Typing.weakening St1_sub_St3_types typ_Denc
              bv_Denc_disj_St3

          have typ_out_St6 : St6.types ⊢ˢ
              SMT.Term.lambda [z] [rho.pair gamma]
                (SMT.Term.and
                  (SMT.Term.app Denc (SMT.Term.fst (.var z)))
                  (SMT.Term.eq (SMT.Term.snd (.var z))
                    (SMT.substList vs
                      (toDestPair vs (SMT.Term.fst (.var z))) Penc))) :
              SMTType.fun (rho.pair gamma) SMTType.bool := by
            have hupdate : SMT.TypeContext.update St3.types [z]
                [rho.pair gamma] rfl =
                St3.types.insert z (rho.pair gamma) := by
              simp only [SMT.TypeContext.update, List.length_cons,
                List.length_nil, zero_add, Nat.reduceAdd,
                Fin.cast_eq_self, Fin.getElem_fin, Fin.val_eq_zero,
                List.getElem_cons_zero, Fin.foldl_succ, Fin.foldl_zero]
            have typ_out_St3 : St3.types ⊢ˢ
                SMT.Term.lambda [z] [rho.pair gamma]
                  (SMT.Term.and
                    (SMT.Term.app Denc (SMT.Term.fst (.var z)))
                    (SMT.Term.eq (SMT.Term.snd (.var z))
                      (SMT.substList vs
                        (toDestPair vs
                          (SMT.Term.fst (.var z))) Penc))) :
                SMTType.fun (rho.pair gamma) SMTType.bool := by
              refine SMT.Typing.lambda St3.types [z]
                [rho.pair gamma] _ SMTType.bool ?_ ?_
                (by simp) rfl ?_
              · intro v hv
                rw [List.mem_singleton] at hv
                simpa [hv] using z_fresh
              · intro v hv
                rw [List.mem_singleton] at hv
                subst v
                simp only [SMT.bv, List.append_nil, List.nil_append,
                  List.mem_append, not_or]
                refine ⟨z_not_bv_Denc, ?_⟩
                intro hbv
                exact z_not_bv_Penc <|
                  SMT_bv_substList_subset
                    (fun t ht => toDestPair_bv_nil_base
                      (by simp [SMT.bv]) t ht) _ hbv
              · rw [hupdate]
                have h_ins :=
                  SMT.TypeContext.entries_subset_insert_of_notMem
                    (v := z) (τ := rho.pair gamma) z_fresh
                refine SMT.Typing.and _ _ _ ?_ ?_
                · exact SMT.Typing.app _ _ _ _ _
                    (SMT.Typing.weakening h_ins typ_Denc_St3
                      (SMT.Typing.bv_notMem_insert_of_fresh
                        typ_Denc_St3 z_not_bv_Denc))
                    (SMT.Typing.fst _ _ _ _
                      (SMT.Typing.var _ z (rho.pair gamma)
                        (AList.lookup_insert St3.types)))
                · refine SMT.Typing.eq _ _ _ gamma ?_ ?_
                  · exact SMT.Typing.snd _ _ _ _
                      (SMT.Typing.var _ z (rho.pair gamma)
                        (AList.lookup_insert St3.types))
                  · apply SMT_Typing_substList
                    · exact SMT.Typing.weakening h_ins typ_Penc
                        (SMT.Typing.bv_notMem_insert_of_fresh
                          typ_Penc z_not_bv_Penc)
                    · exact toDestPair_bv_nil_base (by simp [SMT.bv])
                    · let GammaZ :=
                          St3.types.insert z (rho.pair gamma)
                      intro i hi_vs hi_terms hlookup
                      have hi_sigmas : i < sigmas.length := by
                        rw [sigmas_len]
                        exact hi_vs
                      have hlookup_St2 : St2.types.lookup vs[i] =
                          some sigmas[i] := by
                        rw [St2_update]
                        exact SMT.TypeContext.lookup_update_of_mem_nodup
                          St1.types vs_nodup vs_sigmas_len hi_vs
                      have hlookup_St3 : St3.types.lookup vs[i] =
                          some sigmas[i] :=
                        AList.mem_lookup_iff.mpr <|
                          St2_sub_St3 <|
                            AList.mem_lookup_iff.mp hlookup_St2
                      have hv_ne_z : vs[i] ≠ z := by
                        intro heq
                        apply z_not_used
                        rw [← heq]
                        exact used_sub_St3
                          (vs_used_St2 vs[i]
                            (List.getElem_mem hi_vs))
                      have hlookup_GammaZ : GammaZ.lookup vs[i] =
                          some sigmas[i] := by
                        change (St3.types.insert z (rho.pair gamma)).lookup
                          vs[i] = some sigmas[i]
                        rw [AList.lookup_insert_ne hv_ne_z]
                        exact hlookup_St3
                      have hget : (GammaZ.lookup vs[i]).get hlookup =
                          sigmas[i] := by
                        simp [hlookup_GammaZ]
                      rw [hget]
                      have hz_lookup : GammaZ.lookup z =
                          some (rho.pair gamma) := by
                        exact AList.lookup_insert St3.types
                      have typ_z : GammaZ ⊢ˢ SMT.Term.var z :
                          rho.pair gamma :=
                        SMT.Typing.var GammaZ z _ hz_lookup
                      have typ_fst : GammaZ ⊢ˢ
                          SMT.Term.fst (.var z) : rho :=
                        SMT.Typing.fst _ _ _ _ typ_z
                      have hdest := toDestPair_typing_gen GammaZ vs
                        (SMT.Term.fst (.var z))
                        (SMT.Term.fst (.var z)) rho [] []
                        vs_nemp rfl typ_fst sigmas_len rfl
                        (fun j hj => absurd hj (Nat.not_lt_zero j))
                        i sigmas[i]
                        (by
                          simp only [List.append_nil]
                          rw [List.getElem?_eq_getElem hi_sigmas])
                      exact hdest.2
            apply SMT.Typing.strengthening_of_fv_subset
              St6_sub_St3 typ_out_St3
            intro v hv
            have hv_St3 := SMT.Typing.mem_context_of_mem_fv
              typ_out_St3 hv
            have hv' := hv
            simp only [SMT.fv] at hv'
            unfold List.removeAll at hv'
            rw [List.mem_filter] at hv'
            have hv_ne_z : v ≠ z := by simpa using hv'.2
            rw [St6_types, St5_types, St4_types]
            obtain ⟨sigma_v, hsigma_v⟩ :=
              Option.isSome_iff_exists.mp
                (AList.lookup_isSome.mpr hv_St3)
            have hentry := AList.mem_lookup_iff.mp hsigma_v
            have hins : ⟨v, sigma_v⟩ ∈
                (AList.insert z (rho.pair gamma) St3.types).entries := by
              rw [AList.entries_insert_of_notMem z_fresh]
              exact List.mem_cons_of_mem _ hentry
            exact AList.mem_keys.mpr <| List.mem_map.mpr
              ⟨⟨v, sigma_v⟩,
                List.mem_kerase_of_ne_key hv_ne_z hins, rfl⟩
          have St6_types_eq : St6.types = St3.types := by
            rw [St6_types, St5_types, St4_types]
            exact encodeTerm_state.erase_insert_self z_fresh
          have St0_sub_St6 : St0.types ⊆ St6.types := by
            rw [St6_types_eq]
            exact AList.subset_trans
              (AList.subset_trans St0_sub_St1 St1_sub_St2_types)
              St2_sub_St3
          have hstate :
              used ⊆ St6.env.usedVars ∧
              St0.types ⊆ St6.types ∧
              St6.types.keys ⊆ St6.env.usedVars ∧
              B.CoversUsedVars St6.env.usedVars
                (B.Term.lambda vs D P) ∧
              (∀ v ∈ used, v ∉ St0.types →
                v ∉ B.Term.vars (B.Term.lambda vs D P) →
                v ∉ St6.types) := by
            refine ⟨?_, St0_sub_St6, ?_, ?_, ?_⟩
            · rw [St6_used_chain]
              intro v hv
              exact List.mem_cons_of_mem _ <|
                used_sub_St3 (St1_sub_St2_used (used_sub_St1 hv))
            · rw [St6_types_eq, St6_used_chain]
              intro v hv
              exact List.mem_cons_of_mem _ (St3_keys_sub hv)
            · intro v hv
              rw [St6_used_chain]
              apply List.mem_cons_of_mem
              rw [B.fv, List.mem_append] at hv
              rcases hv with hv_D | hv_P
              · exact used_sub_St3
                  (St1_sub_St2_used (covers_D v hv_D))
              · exact covers_P v (List.mem_removeAll_iff.mp hv_P).1
            · intro v v_used v_notMem_St0 v_notMem_vars v_mem_St6
              obtain ⟨v_notMem_vars_D, v_notMem_vars_P, hv_not_vs⟩ :=
                B.Term.notMem_vars_lambda.mp v_notMem_vars
              have v_mem_St3 : v ∈ St3.types := by
                rw [St6_types_eq] at v_mem_St6
                exact v_mem_St6
              have v_notMem_St1 :=
                D_preserves v v_used v_notMem_St0 v_notMem_vars_D
              have v_notMem_St2 : v ∉ St2.types := by
                rw [St2_update]
                intro h
                rcases (SMT.TypeContext.mem_update_iff
                  St1.types v vs sigmas vs_sigmas_len).mp h with hvs | hSt1
                · exact hv_not_vs hvs
                · exact v_notMem_St1 hSt1
              exact P_preserves v
                (St1_sub_St2_used (used_sub_St1 v_used))
                v_notMem_St2 v_notMem_vars_P v_mem_St3
          have hT_parent :
              T ∈ ⟦BType.set (tau ×ᴮ beta)⟧ᶻ := by
            simpa [tau] using hT
          have hsemantic_scoped : LambdaScopedSemanticPost.{u}
              (B.Term.lambda vs D P) (BType.set (tau ×ᴮ beta))
              St0.types Xi Theta0 T hT_parent E
              (SMT.Term.lambda [z] [rho.pair gamma]
                (SMT.Term.and
                  (SMT.Term.app Denc (SMT.Term.fst (.var z)))
                  (SMT.Term.eq (SMT.Term.snd (.var z))
                    (SMT.substList vs
                      (toDestPair vs (SMT.Term.fst (.var z))) Penc))))
              (SMTType.fun (rho.pair gamma) SMTType.bool)
              St6.env St6.types DltD := by
            have hpath : Nonempty
                (SMTType.fun (rho.pair gamma) SMTType.bool ~>
                  (BType.set (tau ×ᴮ beta)).toSMTType) :=
                (rho_supported.prod gamma_supported).setPred
                  |>.nonemptyCanonicalCastPath
            refine ⟨by simpa [tau] using hpath, typ_out_St6, trivial, ?_⟩
            let body : SMT.Term :=
              SMT.Term.and
                (SMT.Term.app Denc (SMT.Term.fst (.var z)))
                (SMT.Term.eq (SMT.Term.snd (.var z))
                  (SMT.substList vs
                    (toDestPair vs (SMT.Term.fst (.var z))) Penc))
            have body_def : body =
                SMT.Term.and
                  (SMT.Term.app Denc (SMT.Term.fst (.var z)))
                  (SMT.Term.eq (SMT.Term.snd (.var z))
                    (SMT.substList vs
                      (toDestPair vs (SMT.Term.fst (.var z))) Penc)) := rfl
            have ThetaP_ext_D : SMT.RenamingContext.Extends
                ThetaP ThetaD := by
              intro v d hv
              dsimp [ThetaP]
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
            have ThetaBody_ext_D : SMT.RenamingContext.Extends
                ThetaBody ThetaD :=
              SMT.RenamingContext.extends_trans ThetaBody_ext ThetaP_ext_D
            have ThetaBody_ext0 : SMT.RenamingContext.Extends
                ThetaBody Theta0 :=
              SMT.RenamingContext.extends_trans ThetaBody_ext_D ThetaD_ext
            have related_out : RValuationCastSupportedOnFV
                Xi ThetaBody (B.Term.lambda vs D P) :=
              related.of_extends ThetaBody_ext0
            have respects_out :
                B.RenamingContext.RespectsTypeContextOnFV
                  ThetaBody St6.types (B.Term.lambda vs D P) := by
              apply B.RenamingContext.RespectsTypeContextOnFV.of_extends
                respects ThetaBody_ext0 St0_sub_St6
              · intro v hv
                exact hv
              · exact fv_in_Lambda
            have ThetaBody_none_out : ∀ v ∉ St6.env.usedVars,
                ThetaBody v = none := by
              intro v hv
              apply ThetaBody_none v
              rw [St6_used_chain] at hv
              simp only [List.mem_cons, not_or] at hv
              exact hv.2
            have ThetaBody_dom_out : ∀ v, ThetaBody v ≠ none →
                v ∈ St6.types := by
              intro v hv
              rw [St6_types_eq]
              exact ThetaBody_dom v hv
            have hcov_D_body : SMT.RenamingContext.CoversFV
                ThetaBody Denc :=
              SMT.RenamingContext.coversFV_of_extends_of_coversFV
                ThetaBody_ext_D hcov_Denc
            have hagree_D : SMT.RenamingContext.AgreesOnFV
                ThetaBody ThetaD Denc :=
              SMT.RenamingContext.agreesOnFV_of_extends_of_coversFV
                ThetaBody_ext_D hcov_Denc
            have hden_D_body :
                ⟦Denc.abstract ThetaBody hcov_D_body⟧ˢ =
                  some (⟨DencZF, SMTType.fun rho SMTType.bool,
                    hDencZF⟩ : SMT.Dom) := by
              calc
                ⟦Denc.abstract ThetaBody hcov_D_body⟧ˢ =
                    ⟦Denc.abstract ThetaD hcov_Denc⟧ˢ :=
                  SMT.RenamingContext.denote_congr_of_agreesOnFV
                    (h1 := hcov_D_body) (h2 := hcov_Denc) hagree_D
                _ = some (⟨DencZF, SMTType.fun rho SMTType.bool,
                    hDencZF⟩ : SMT.Dom) := hden_Denc
            have z_not_fv_Denc : z ∉ SMT.fv Denc := by
              intro hz
              exact z_fresh
                (SMT.Typing.mem_context_of_mem_fv typ_Denc_St3 hz)
            have z_not_fv_Penc : z ∉ SMT.fv Penc := by
              intro hz
              exact z_fresh
                (SMT.Typing.mem_context_of_mem_fv typ_Penc hz)
            have hcov_D_upd : ∀ W : SMT.Dom.{u},
                SMT.RenamingContext.CoversFV
                  (Function.update ThetaBody z (some W)) Denc := by
              intro W
              exact SMT.RenamingContext.coversFV_update_of_notMem
                z_not_fv_Denc hcov_D_body
            have hden_D_upd : ∀ W : SMT.Dom.{u},
                ⟦Denc.abstract (Function.update ThetaBody z (some W))
                  (hcov_D_upd W)⟧ˢ =
                    some (⟨DencZF, SMTType.fun rho SMTType.bool,
                      hDencZF⟩ : SMT.Dom) := by
              intro W
              calc
                ⟦Denc.abstract (Function.update ThetaBody z (some W))
                    (hcov_D_upd W)⟧ˢ =
                    ⟦Denc.abstract ThetaBody hcov_D_body⟧ˢ := by
                  exact (SMT.RenamingContext.denote_update_of_notMem
                    (h := hcov_D_body) z_not_fv_Denc).symm
                _ = some (⟨DencZF, SMTType.fun rho SMTType.bool,
                    hDencZF⟩ : SMT.Dom) := hden_D_body
            have hDenc_func : ⟦rho⟧ᶻ.IsFunc 𝔹 DencZF := by
              have hmem := hDencZF
              rw [SMTType.toZFSet] at hmem
              exact ZFSet.mem_funs.mp hmem
            have target_respects_D_body :
                SMT.RenamingContext.RespectsTypeContextOnFV
                  ThetaBody St3.types Denc :=
              SMT.RenamingContext.RespectsTypeContextOnFV.of_extends
                target_respects_Denc ThetaBody_ext_D
                St1_sub_St3_types typ_Denc
            have hcov_P_upd : ∀ (W : SMT.Dom.{u})
                (ss' : Fin vs.length → SMT.Dom.{u}),
                SMT.RenamingContext.CoversFV
                  (Function.updates
                    (Function.update ThetaBody z (some W)) vs
                    ((List.ofFn ss').map Option.some)) Penc := by
              intro W ss' v hv
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
            have hcov_sub_upd : ∀ W : SMT.Dom.{u},
                SMT.RenamingContext.CoversFV
                  (Function.update ThetaBody z (some W))
                  (SMT.substList vs
                    (toDestPair vs (SMT.Term.fst (.var z))) Penc) := by
              intro W v hv
              rcases SMT_mem_fv_substList hv with hv_P |
                  ⟨t, ht, hv_t⟩
              · rw [Function.update_of_ne (by
                    intro heq
                    exact z_not_fv_Penc (heq ▸ hv_P))]
                exact hcov_Penc v hv_P
              · have hvz := SMT_fv_toDestPair_subset_base
                    (t₀ := SMT.Term.fst (.var z))
                    (by
                      intro w hw
                      simpa [SMT.fv] using hw)
                    ht hv_t
                subst v
                simp
            have hcov_body_upd : ∀ W : SMT.Dom.{u},
                SMT.RenamingContext.CoversFV
                  (Function.update ThetaBody z (some W)) body := by
              intro W v hv
              rw [body_def] at hv
              simp only [SMT.fv, List.mem_append, List.mem_singleton,
                List.not_mem_nil, or_false] at hv
              rcases hv with (hv_D | rfl) | (rfl | hv_sub)
              · exact hcov_D_upd W v hv_D
              · simp
              · simp
              · exact hcov_sub_upd W v hv_sub
            have hcov_lambda : SMT.RenamingContext.CoversFV ThetaBody
                ((λˢ [z]) [rho.pair gamma] body) := by
              intro v hv
              simp only [SMT.fv, List.mem_removeAll_iff] at hv
              obtain ⟨hv_body, hv_ne_z⟩ := hv
              have hvz : v ≠ z := List.mem_singleton.not.mp hv_ne_z
              have hcov := hcov_body_upd
                (⟨PencZF, gamma, hPencZF⟩ : SMT.Dom) v hv_body
              rw [Function.update_of_ne hvz] at hcov
              exact hcov
            have target_respects_lambda :
                SMT.RenamingContext.RespectsTypeContextOnFV
                  ThetaBody St3.types
                    ((λˢ [z]) [rho.pair gamma] body) := by
              intro v sigma hv hlookup
              simp only [SMT.fv, List.mem_removeAll_iff] at hv
              obtain ⟨hv_body, hv_ne_z⟩ := hv
              have hvz : v ≠ z := List.mem_singleton.not.mp hv_ne_z
              rw [body_def] at hv_body
              simp only [SMT.fv, List.mem_append, List.mem_singleton,
                List.not_mem_nil, or_false] at hv_body
              rcases hv_body with (hv_D | hv_z1) | (hv_z2 | hv_sub)
              · exact target_respects_D_body hv_D hlookup
              · exact absurd hv_z1 hvz
              · exact absurd hv_z2 hvz
              · rcases SMT_mem_fv_substList hv_sub with hv_P |
                    ⟨t, ht, hv_t⟩
                · exact target_respects_Penc hv_P hlookup
                · exact absurd
                    (SMT_fv_toDestPair_subset_base
                      (t₀ := SMT.Term.fst (.var z))
                      (by
                        intro w hw
                        simpa [SMT.fv] using hw)
                      ht hv_t) hvz
            have target_respects_lambda_out :
                SMT.RenamingContext.RespectsTypeContextOnFV
                  ThetaBody St6.types
                    ((λˢ [z]) [rho.pair gamma] body) := by
              rw [St6_types_eq]
              exact target_respects_lambda
            obtain ⟨_, hlen_z, gamma_body, _, _, htype_out,
                typ_body_update⟩ := SMT.Typing.lambdaE typ_out_St6
            have gamma_body_eq : gamma_body = SMTType.bool := by
              have h := (SMTType.fun.inj htype_out).2
              exact h.symm
            subst gamma_body
            have hupdate_body : St6.types.update [z]
                [rho.pair gamma] hlen_z =
                St3.types.insert z (rho.pair gamma) := by
              rw [St6_types_eq]
              simp only [SMT.TypeContext.update, List.length_cons,
                List.length_nil, zero_add, Nat.reduceAdd,
                Fin.cast_eq_self, Fin.getElem_fin, Fin.val_eq_zero,
                List.getElem_cons_zero, Fin.foldl_succ, Fin.foldl_zero]
            have typ_body : St3.types.insert z (rho.pair gamma) ⊢ˢ
                body : SMTType.bool := by
              rw [hupdate_body] at typ_body_update
              simpa [body] using typ_body_update
            have Theta_wt : ∀ v ∈ SMT.fv body,
                ∀ d : SMT.Dom.{u}, ThetaBody v = some d →
                ∀ sigma, St3.types.lookup v = some sigma →
                  d.snd.fst = sigma := by
              intro v hv d hd sigma hlookup
              by_cases hvz : v = z
              · subst v
                have hz_none : ThetaBody z = none :=
                  ThetaBody_none z z_not_used
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
            obtain ⟨hbody_isSome, _hbody_type⟩ :=
              SMT.RenamingContext.denote_update_total_and_type_of_typing
                typ_body Theta_wt hcov_body_upd
            have hbody_total : ∀ W : SMT.Dom.{u},
                W.snd.fst = rho.pair gamma →
                ∃ bodyVal : SMT.Dom.{u},
                  ⟦body.abstract (Function.update ThetaBody z (some W))
                    (hcov_body_upd W)⟧ˢ = some bodyVal := by
              intro W hW
              exact Option.isSome_iff_exists.mp (hbody_isSome W hW)
            have bound_expected : ∀ i : Fin vs.length,
                St2.types.lookup vs[i] =
                  some ((rho.fromProdl (vs.length - 1))[i.val]'(by
                    have hlen :=
                      rho_supported.fromProdl_length_of_hasArity tau_hasArity
                    exact i.isLt.trans_eq hlen.symm)) := by
              intro i
              have hlookup : St2.types.lookup vs[i] =
                  some (sigmas[i.val]'(by
                    rw [sigmas_len]
                    exact i.isLt)) := by
                rw [St2_update]
                exact SMT.TypeContext.lookup_update_of_mem_nodup
                  St1.types vs_nodup vs_sigmas_len i.isLt
              simpa [sigmas] using hlookup
            have respects_P_St2 :
                B.RenamingContext.RespectsTypeContextOnFV
                  ThetaBody St2.types P := by
              intro v sigma hv hlookup
              exact respects_P_final hv
                (AList.lookup_of_subset St2_sub_St3 hlookup)
            have source_respects_upd :
                ∀ ss' : Fin vs.length → SMT.Dom.{u},
                (∀ i, St2.types.lookup vs[i] = some (ss' i).snd.fst) →
                B.RenamingContext.RespectsTypeContextOnFV
                  (Function.updates ThetaBody vs
                    ((List.ofFn ss').map Option.some)) St2.types P := by
              intro ss' hss
              apply B.RenamingContext.RespectsTypeContextOnFV.updates_of_typed_bounds
                vs_nodup
              · intro v hv hvs sigma hlookup
                exact respects_P_St2 hv hlookup
              · exact hss
            have vs_used_St3 : ∀ v ∈ vs,
                v ∈ St3.env.usedVars :=
              fun v hv => used_sub_St3 (vs_used_St2 v hv)
            have St2_keys_used_St3 : St2.types.keys ⊆
                St3.env.usedVars :=
              fun v hv => used_sub_St3 (St2_keys_sub hv)
            have z_not_vs : z ∉ vs := by
              intro hz
              exact z_not_used (vs_used_St3 z hz)
            have hvs_not_bv : ∀ v ∈ vs, v ∉ SMT.bv Penc := by
              intro v hv hbv
              exact bv_Penc_not_used v hbv (vs_used_St2 v hv)
            have z_not_vars_P : z ∉ B.Term.vars P := by
              intro hz
              exact z_not_used
                (used_sub_St3 (vars_used_P_St2 z hz))
            have ambient_P_final : ∀ v ∈ B.fv P, v ∉ vs →
                match Xi v, ThetaBody v with
                | some source, some target =>
                    RDomCastSupported source target
                | _, _ => False := by
              intro v hv hvs
              exact related_out v
                (B.fv.mem_lambda (.inr ⟨hv, hvs⟩))
            have wf_bound : ∀ (x' : ZFSet.{u})
                (hx' : x' ∈ ⟦tau⟧ᶻ) (_hxD : x' ∈ Dval),
                B.RenWF Ebody.context
                  (Function.updates Xi vs (List.ofFn fun i => some
                    (⟨x'.get vs.length i, tau.get vs.length i,
                      get_mem_type_of_isTuple
                        (hasArity_of_mem_toZFSet tau_hasArity hx')
                        tau_hasArity hx'⟩ : B.Dom))) := by
              intro x' hx' _hxD
              exact wf_seed _ (fun _ => rfl)
            have hT_lambda : T ∈ ⟦BType.set (tau ×ᴮ beta)⟧ᶻ := by
              simpa [tau] using hT
            have den_lambda :
                ⟦(B.Term.lambda vs D P).abstract Xi Xi_fv⟧ᴮ =
                  some (⟨T, BType.set (tau ×ᴮ beta),
                    hT_lambda⟩ : B.Dom) := by
              simpa only [tau, proof_irrel_heq] using den_t
            obtain ⟨lamVal, hden_lambda, hlam_type⟩ :=
              SMT.RenamingContext.denote_exists_of_typing_fv
                (by simpa [body] using typ_out_St6)
                target_respects_lambda_out hcov_lambda
            have hrel_lambda : RDomCastSupported
                (⟨T, BType.set (tau ×ᴮ beta), hT_lambda⟩ : B.Dom)
                lamVal := by
              exact represented_lambda_of_total_body
                (D := D) (P := P) (tau := tau) (beta := beta)
                (Xi := Xi) (Dval := Dval) (hDval := hDval)
                (T := T) (hT := hT_lambda) (sigma := rho)
                (gamma := gamma) (Denc := Denc) (Penc := Penc)
                (body := body) (z := z) (ThetaD := ThetaBody)
                (DencVal := ⟨DencZF, SMTType.fun rho SMTType.bool,
                  hDencZF⟩) (lamVal := lamVal)
                (Ebody := Ebody) (LambdaP := St2.types)
                (GammaP := St3.types) (usedP := St3.env.usedVars)
                vs_nemp vs_nodup Xi_fv tau_hasArity den_D den_lambda
                rho_supported gamma_supported body_def hcov_lambda
                hden_lambda hlam_type hcov_D_upd hden_D_upd rfl
                hDenc_func D_rel hcov_body_upd hbody_total hcov_sub_upd
                hcov_P_upd hvs_not_bv z_not_bv_Penc z_not_vs typ_P
                P_total ambient_P_final wf_bound bound_expected
                source_respects_upd fv_P_in_St2 Penc_fv_in_St2
                St2_keys_used_St3 Penc_fv_vars z_not_vars_P
            refine ⟨ThetaBody, hcov_lambda, ThetaBody_ext0, related_out,
              ThetaBody_none_out, respects_out,
              target_respects_lambda_out, ThetaBody_dom_out,
              lamVal, hden_lambda, hlam_type, ?_, ?_⟩
            · simpa only [tau, proof_irrel_heq] using hrel_lambda
            · intro Xi_alt Xi_fv_alt Theta0_alt related_alt wf_alt
                Theta0_alt_none respects_alt Theta0_alt_dom
                T_alt hT_alt den_alt
              have hT_alt_lambda :
                  T_alt ∈ ⟦BType.set (tau ×ᴮ beta)⟧ᶻ := by
                simpa [tau] using hT_alt
              have den_alt_lambda :
                  ⟦(B.Term.lambda vs D P).abstract
                    Xi_alt Xi_fv_alt⟧ᴮ =
                    some (⟨T_alt, BType.set (tau ×ᴮ beta),
                      hT_alt_lambda⟩ : B.Dom) := by
                simpa only [tau, proof_irrel_heq] using den_alt
              have Xi_fv_D_alt : ∀ v ∈ B.fv D,
                  (Xi_alt v).isSome = true :=
                fun v hv => Xi_fv_alt v (B.fv.mem_lambda (.inl hv))
              have related_D_alt : RValuationCastSupportedOnFV
                  Xi_alt Theta0_alt D :=
                related_alt.mono_fv
                  (fun _ hv => B.fv.mem_lambda (.inl hv))
              have respects_D_alt :
                  B.RenamingContext.RespectsTypeContextOnFV
                    Theta0_alt St0.types D :=
                respects_alt.mono_fv
                  (fun _ hv => B.fv.mem_lambda (.inl hv))
              obtain ⟨Dval_alt, hDval_alt, den_D_alt⟩ :=
                B.denote_lambda_domain_exists Xi_fv_alt typ_D wf_alt
                  den_alt_lambda
              have Theta0_alt_none_D : ∀ v ∉ St1.env.usedVars,
                  Theta0_alt v = none := by
                intro v hv
                by_contra hne
                have hv_St0 : v ∈ St0.types := Theta0_alt_dom v hne
                have hv_used : v ∈ used := by
                  rw [← St0_used]
                  exact St0_keys hv_St0
                exact hv (used_sub_St1 hv_used)
              obtain ⟨ThetaD_alt, hcov_D_alt, DencVal_alt,
                  ThetaD_alt_ext, related_D_alt_out, ThetaD_alt_none,
                  respects_D_alt_out, target_respects_D_alt,
                  ThetaD_alt_dom, D_specs_true_alt, hden_Denc_alt,
                  hDenc_type_alt, D_rel_alt⟩ :=
                D_scoped_total Xi_alt Xi_fv_D_alt Theta0_alt related_D_alt
                  wf_alt Theta0_alt_none_D respects_D_alt
                  Theta0_alt_dom Dval_alt hDval_alt den_D_alt
              let DencVal_alt' : SMT.Dom.{u} :=
                ⟨DencVal_alt.fst, SMTType.fun rho SMTType.bool, by
                  rw [← hDenc_type_alt]
                  exact DencVal_alt.snd.snd⟩
              have DencVal_alt_eq : DencVal_alt = DencVal_alt' :=
                SMT.RenamingContext.Dom_ext' rfl hDenc_type_alt
              have D_rel_alt' : RDomCastSupported
                  (⟨Dval_alt, BType.set tau, hDval_alt⟩ : B.Dom)
                  DencVal_alt' := by
                simpa only [DencVal_alt_eq] using D_rel_alt
              have wf_seed_alt : ∀
                  (x_fin : Fin vs.length → B.Dom.{u}),
                  (∀ i, (x_fin i).snd.fst = tau.get vs.length i) →
                  B.RenWF Ebody.context
                    (Function.updates Xi_alt vs
                      (List.ofFn fun i => some (x_fin i))) := by
                intro x_fin hx_fin
                exact B.RenWF.updates_ofFn wf_alt vs_nodup
                  vs_context_disj vs_alphas_len (fun i => by
                    calc
                      (x_fin i).snd.fst = tau.get vs.length i := hx_fin i
                      _ = alphas[Fin.cast vs_alphas_len i] := by
                        simpa [tau] using
                          BType.get_reduce alphas_nemp vs_alphas_len i)
              obtain ⟨x_alt, hx_alt, hx_origin_alt, hseed_alt⟩ :=
                B.denote_lambda_seed_body_exists Xi_fv_alt vs_nemp
                  vs_nodup tau_hasArity den_D_alt den_alt_lambda
                  typ_P wf_seed_alt
              obtain ⟨XiP_fv_alt_seed, Pval_alt, hPval_alt,
                  den_P_alt_seed⟩ := hseed_alt
              obtain ⟨y_alt, hy_alt, hxy_alt⟩ :
                  ∃ (y : ZFSet.{u}) (hy : y ∈ ⟦rho⟧ᶻ),
                    RDomCastSupported
                      (⟨x_alt, tau, hx_alt⟩ : B.Dom)
                      (⟨y, rho, hy⟩ : SMT.Dom) := by
                rcases hx_origin_alt with hxD | hx_default
                · obtain ⟨y, hy, hrel⟩ :=
                    D_rel_alt'.setPred_member_preimage hxD
                  exact ⟨y, hy, by
                    simpa only [DencVal_alt', proof_irrel_heq] using hrel⟩
                · subst x_alt
                  exact ⟨rho.defaultZFSet,
                    SMTType.mem_toZFSet_of_defaultZFSet, by
                      simpa only [proof_irrel_heq] using
                        RDomCastSupported.default_of_supported
                          rho_supported⟩
              have hy_alt_prodl : y_alt ∈ ⟦sigmas.toProdl⟧ᶻ := by
                rw [sigmas_toProdl]
                exact hy_alt
              have hxy_alt_prodl : RDomCastSupported
                  (⟨x_alt, alphas.reduce (· ×ᴮ ·) alphas_nemp,
                    hx_alt⟩ : B.Dom)
                  (⟨y_alt, sigmas.toProdl, hy_alt_prodl⟩ : SMT.Dom) := by
                simpa only [tau, sigmas_toProdl, proof_irrel_heq] using
                  hxy_alt
              let bs_alt : Fin vs.length → B.Dom.{u} := fun i =>
                ⟨x_alt.get vs.length i, tau.get vs.length i,
                  get_mem_type_of_isTuple
                    (hasArity_of_mem_toZFSet tau_hasArity hx_alt)
                    tau_hasArity hx_alt⟩
              let ss_alt : Fin vs.length → SMT.Dom.{u} := fun i =>
                let j : Fin sigmas.length := Fin.cast vs_sigmas_len i
                ⟨y_alt.get sigmas.length j, sigmas[j],
                  SMTType.mem_get_of_mem_toProdl
                    (fun hs => alphas_nemp (List.length_eq_zero_iff.mp
                      (alphas_sigmas_len.trans (by simp [hs]))))
                    hy_alt_prodl⟩
              let XiP_alt := Function.updates Xi_alt vs
                (List.ofFn fun i => some (bs_alt i))
              let ThetaP0_alt := Function.updates ThetaD_alt vs
                (List.ofFn fun i => some (ss_alt i))
              have related_lambda_D_alt : RValuationCastSupportedOnFV
                  Xi_alt ThetaD_alt (B.Term.lambda vs D P) :=
                related_alt.of_extends ThetaD_alt_ext
              have ambient_P_alt : ∀ v ∈ B.fv P, v ∉ vs →
                  match Xi_alt v, ThetaD_alt v with
                  | some source, some target =>
                      RDomCastSupported source target
                  | _, _ => False := by
                intro v hv hvs
                exact related_lambda_D_alt v
                  (B.fv.mem_lambda (.inr ⟨hv, hvs⟩))
              have related_P_alt : RValuationCastSupportedOnFV
                  XiP_alt ThetaP0_alt P := by
                dsimp only [XiP_alt, ThetaP0_alt]
                apply RValuationCastSupportedOnFV.updates
                  vs_nodup bs_alt ss_alt ambient_P_alt
                intro i
                let jalpha : Fin alphas.length :=
                  Fin.cast vs_alphas_len i
                have hcomp :=
                  RDomCastSupported.get_of_reduce_toProdl
                    alphas_nemp alphas_sigmas_len hx_alt hy_alt_prodl
                    hxy_alt_prodl jalpha
                have hsource : bs_alt i =
                    (⟨x_alt.get alphas.length jalpha, alphas[jalpha],
                      BType.mem_get_of_mem_reduce_toZFSet
                        alphas_nemp hx_alt⟩ : B.Dom) := by
                  exact B.Dom.ext_type_value
                    (BType.get_reduce alphas_nemp vs_alphas_len i)
                    (ZFSet.get_cast vs_alphas_len i)
                rw [hsource]
                simpa [ss_alt, jalpha] using hcomp
              have XiP_fv_alt : ∀ v ∈ B.fv P,
                  (XiP_alt v).isSome = true := by
                simpa [XiP_alt, bs_alt] using XiP_fv_alt_seed
              have den_P_alt :
                  ⟦P.abstract XiP_alt XiP_fv_alt⟧ᴮ =
                    some (⟨Pval_alt, beta, hPval_alt⟩ : B.Dom) := by
                simpa only [XiP_alt, bs_alt, proof_irrel_heq] using
                  den_P_alt_seed
              have wf_P_alt : B.RenWF Ebody.context XiP_alt := by
                exact wf_seed_alt bs_alt (fun _ => rfl)
              have ThetaP0_alt_none_St2 : ∀ v ∉ St2.env.usedVars,
                  ThetaP0_alt v = none := by
                intro v hv
                have hvs : v ∉ vs := fun h => hv (vs_used_St2 v h)
                change Function.updates ThetaD_alt vs
                  (List.ofFn fun i => some (ss_alt i)) v = none
                rw [Function.updates_of_not_mem ThetaD_alt vs _ v hvs]
                apply ThetaD_alt_none v
                exact fun h => hv (St1_sub_St2_used h)
              have ThetaP0_alt_none : ∀ v ∉ St3.env.usedVars,
                  ThetaP0_alt v = none := by
                intro v hv
                exact ThetaP0_alt_none_St2 v
                  (fun h => hv (used_sub_St3 h))
              have ThetaP0_alt_dom : ∀ v, ThetaP0_alt v ≠ none →
                  v ∈ St2.types := by
                intro v hv
                by_cases hvs : v ∈ vs
                · rw [St2_update]
                  exact (SMT.TypeContext.mem_update_iff
                    St1.types v vs sigmas vs_sigmas_len).mpr (.inl hvs)
                · change Function.updates ThetaD_alt vs
                    (List.ofFn fun i => some (ss_alt i)) v ≠ none at hv
                  rw [Function.updates_of_not_mem
                    ThetaD_alt vs _ v hvs] at hv
                  exact AList.mem_of_subset St1_sub_St2_types
                    (ThetaD_alt_dom v hv)
              have respects_P_alt :
                  B.RenamingContext.RespectsTypeContextOnFV
                    ThetaP0_alt St2.types P := by
                intro v sigma hv hlookup
                by_cases hvs : v ∈ vs
                · let i : Fin vs.length :=
                    ⟨vs.idxOf v, List.idxOf_lt_length_of_mem hvs⟩
                  have hvi : vs[i] = v :=
                    List.getElem_idxOf (List.idxOf_lt_length_of_mem hvs)
                  have hctx : St2.types.lookup vs[i] =
                      some sigmas[Fin.cast vs_sigmas_len i] := by
                    rw [St2_update]
                    exact SMT.TypeContext.lookup_update_of_mem_nodup
                      St1.types vs_nodup vs_sigmas_len i.isLt
                  rw [hvi] at hctx
                  rw [hctx] at hlookup
                  cases hlookup
                  refine ⟨ss_alt i, ?_, rfl⟩
                  change Function.updates ThetaD_alt vs
                    (List.ofFn fun i => some (ss_alt i)) v =
                      some (ss_alt i)
                  rw [Function.updates_eq_if (by simp) vs_nodup,
                    dif_pos hvs]
                  simpa [i, hvi]
                · have hv_lambda :
                      v ∈ B.fv (B.Term.lambda vs D P) :=
                    B.fv.mem_lambda (.inr ⟨hv, hvs⟩)
                  have hv_St0 := fv_in_Lambda v hv_lambda
                  obtain ⟨sigma0, hsigma0⟩ :=
                    Option.isSome_iff_exists.mp
                      (AList.lookup_isSome.mpr hv_St0)
                  have hsigma1 : St1.types.lookup v = some sigma0 :=
                    AList.lookup_of_subset St0_sub_St1 hsigma0
                  have hsigma2 : St2.types.lookup v = some sigma0 := by
                    rw [St2_update,
                      SMT.TypeContext.lookup_update
                        St1.types v vs sigmas vs_sigmas_len hvs]
                    exact hsigma1
                  rw [hsigma2] at hlookup
                  cases hlookup
                  obtain ⟨d, hd, hdty⟩ :=
                    respects_alt hv_lambda hsigma0
                  refine ⟨d, ?_, hdty⟩
                  change Function.updates ThetaD_alt vs
                    (List.ofFn fun i => some (ss_alt i)) v = some d
                  rw [Function.updates_of_not_mem
                    ThetaD_alt vs _ v hvs]
                  exact ThetaD_alt_ext hd
              obtain ⟨ThetaBody_alt, hcov_P_alt, PencVal_alt,
                  ThetaBody_alt_ext, related_P_alt_out,
                  ThetaBody_alt_none, respects_P_alt_out,
                  target_respects_P_alt, ThetaBody_alt_dom,
                  hden_Penc_alt, hPenc_type_alt, P_rel_alt⟩ :=
                P_total XiP_alt XiP_fv_alt ThetaP0_alt related_P_alt
                  wf_P_alt ThetaP0_alt_none respects_P_alt
                  ThetaP0_alt_dom Pval_alt hPval_alt den_P_alt
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
              have ThetaBody_alt_ext_D : SMT.RenamingContext.Extends
                  ThetaBody_alt ThetaD_alt :=
                SMT.RenamingContext.extends_trans
                  ThetaBody_alt_ext ThetaP0_alt_ext
              have ThetaBody_alt_ext0 : SMT.RenamingContext.Extends
                  ThetaBody_alt Theta0_alt :=
                SMT.RenamingContext.extends_trans
                  ThetaBody_alt_ext_D ThetaD_alt_ext
              have related_out_alt : RValuationCastSupportedOnFV
                  Xi_alt ThetaBody_alt (B.Term.lambda vs D P) :=
                related_alt.of_extends ThetaBody_alt_ext0
              have respects_out_alt :
                  B.RenamingContext.RespectsTypeContextOnFV
                    ThetaBody_alt St6.types
                      (B.Term.lambda vs D P) := by
                apply B.RenamingContext.RespectsTypeContextOnFV.of_extends
                  respects_alt ThetaBody_alt_ext0 St0_sub_St6
                · intro v hv
                  exact hv
                · exact fv_in_Lambda
              have ThetaBody_alt_none_out : ∀ v ∉ St6.env.usedVars,
                  ThetaBody_alt v = none := by
                intro v hv
                apply ThetaBody_alt_none v
                rw [St6_used_chain] at hv
                simp only [List.mem_cons, not_or] at hv
                exact hv.2
              have ThetaBody_alt_dom_out : ∀ v,
                  ThetaBody_alt v ≠ none → v ∈ St6.types := by
                intro v hv
                rw [St6_types_eq]
                exact ThetaBody_alt_dom v hv
              have D_specs_true_out_alt :
                  SpecBodiesTrue ThetaBody_alt St6.types DltD := by
                apply D_specs_true_alt.of_extends ThetaBody_alt_ext_D
                · rw [St6_types_eq]
                  exact St1_sub_St3_types
                · exact ThetaD_alt_dom
              have hcov_D_body_alt : SMT.RenamingContext.CoversFV
                  ThetaBody_alt Denc :=
                SMT.RenamingContext.coversFV_of_extends_of_coversFV
                  ThetaBody_alt_ext_D hcov_D_alt
              have hagree_D_alt : SMT.RenamingContext.AgreesOnFV
                  ThetaBody_alt ThetaD_alt Denc :=
                SMT.RenamingContext.agreesOnFV_of_extends_of_coversFV
                  ThetaBody_alt_ext_D hcov_D_alt
              have hden_D_body_alt :
                  ⟦Denc.abstract ThetaBody_alt hcov_D_body_alt⟧ˢ =
                    some DencVal_alt := by
                calc
                  ⟦Denc.abstract ThetaBody_alt hcov_D_body_alt⟧ˢ =
                      ⟦Denc.abstract ThetaD_alt hcov_D_alt⟧ˢ :=
                    SMT.RenamingContext.denote_congr_of_agreesOnFV
                      (h1 := hcov_D_body_alt) (h2 := hcov_D_alt)
                      hagree_D_alt
                  _ = some DencVal_alt := hden_Denc_alt
              have hcov_D_upd_alt : ∀ W : SMT.Dom.{u},
                  SMT.RenamingContext.CoversFV
                    (Function.update ThetaBody_alt z (some W)) Denc := by
                intro W
                exact SMT.RenamingContext.coversFV_update_of_notMem
                  z_not_fv_Denc hcov_D_body_alt
              have hden_D_upd_alt : ∀ W : SMT.Dom.{u},
                  ⟦Denc.abstract
                    (Function.update ThetaBody_alt z (some W))
                    (hcov_D_upd_alt W)⟧ˢ = some DencVal_alt := by
                intro W
                calc
                  ⟦Denc.abstract
                      (Function.update ThetaBody_alt z (some W))
                      (hcov_D_upd_alt W)⟧ˢ =
                      ⟦Denc.abstract ThetaBody_alt hcov_D_body_alt⟧ˢ := by
                    exact (SMT.RenamingContext.denote_update_of_notMem
                      (h := hcov_D_body_alt) z_not_fv_Denc).symm
                  _ = some DencVal_alt := hden_D_body_alt
              have hDenc_func_alt :
                  ⟦rho⟧ᶻ.IsFunc 𝔹 DencVal_alt.fst := by
                have hmem : DencVal_alt.fst ∈
                    ⟦SMTType.fun rho SMTType.bool⟧ᶻ := by
                  rw [← hDenc_type_alt]
                  exact DencVal_alt.snd.snd
                rw [SMTType.toZFSet] at hmem
                exact ZFSet.mem_funs.mp hmem
              have target_respects_D_body_alt :
                  SMT.RenamingContext.RespectsTypeContextOnFV
                    ThetaBody_alt St3.types Denc :=
                SMT.RenamingContext.RespectsTypeContextOnFV.of_extends
                  target_respects_D_alt ThetaBody_alt_ext_D
                  St1_sub_St3_types typ_Denc
              have hcov_P_upd_alt : ∀ (W : SMT.Dom.{u})
                  (ss' : Fin vs.length → SMT.Dom.{u}),
                  SMT.RenamingContext.CoversFV
                    (Function.updates
                      (Function.update ThetaBody_alt z (some W)) vs
                      ((List.ofFn ss').map Option.some)) Penc := by
                intro W ss' v hv
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
              have hcov_sub_upd_alt : ∀ W : SMT.Dom.{u},
                  SMT.RenamingContext.CoversFV
                    (Function.update ThetaBody_alt z (some W))
                    (SMT.substList vs
                      (toDestPair vs (SMT.Term.fst (.var z))) Penc) := by
                intro W v hv
                rcases SMT_mem_fv_substList hv with hv_P |
                    ⟨t, ht, hv_t⟩
                · rw [Function.update_of_ne (by
                      intro heq
                      exact z_not_fv_Penc (heq ▸ hv_P))]
                  exact hcov_P_alt v hv_P
                · have hvz := SMT_fv_toDestPair_subset_base
                      (t₀ := SMT.Term.fst (.var z))
                      (by
                        intro w hw
                        simpa [SMT.fv] using hw)
                      ht hv_t
                  subst v
                  simp
              have hcov_body_upd_alt : ∀ W : SMT.Dom.{u},
                  SMT.RenamingContext.CoversFV
                    (Function.update ThetaBody_alt z (some W)) body := by
                intro W v hv
                rw [body_def] at hv
                simp only [SMT.fv, List.mem_append,
                  List.mem_singleton] at hv
                rcases hv with (hv_D | rfl) | (rfl | hv_sub)
                · exact hcov_D_upd_alt W v hv_D
                · simp
                · simp
                · exact hcov_sub_upd_alt W v hv_sub
              have hcov_lambda_alt :
                  SMT.RenamingContext.CoversFV ThetaBody_alt
                    ((λˢ [z]) [rho.pair gamma] body) := by
                intro v hv
                simp only [SMT.fv, List.mem_removeAll_iff] at hv
                obtain ⟨hv_body, hv_ne_z⟩ := hv
                have hvz : v ≠ z :=
                  List.mem_singleton.not.mp hv_ne_z
                have hcov := hcov_body_upd_alt PencVal_alt v hv_body
                rw [Function.update_of_ne hvz] at hcov
                exact hcov
              have target_respects_lambda_alt :
                  SMT.RenamingContext.RespectsTypeContextOnFV
                    ThetaBody_alt St3.types
                      ((λˢ [z]) [rho.pair gamma] body) := by
                intro v sigma hv hlookup
                simp only [SMT.fv, List.mem_removeAll_iff] at hv
                obtain ⟨hv_body, hv_ne_z⟩ := hv
                have hvz : v ≠ z :=
                  List.mem_singleton.not.mp hv_ne_z
                rw [body_def] at hv_body
                simp only [SMT.fv, List.mem_append,
                  List.mem_singleton] at hv_body
                rcases hv_body with (hv_D | hv_z1) | (hv_z2 | hv_sub)
                · exact target_respects_D_body_alt hv_D hlookup
                · exact absurd hv_z1 hvz
                · exact absurd hv_z2 hvz
                · rcases SMT_mem_fv_substList hv_sub with hv_P |
                      ⟨t, ht, hv_t⟩
                  · exact target_respects_P_alt hv_P hlookup
                  · exact absurd
                      (SMT_fv_toDestPair_subset_base
                        (t₀ := SMT.Term.fst (.var z))
                        (by
                          intro w hw
                          simpa [SMT.fv] using hw)
                        ht hv_t) hvz
              have target_respects_lambda_out_alt :
                  SMT.RenamingContext.RespectsTypeContextOnFV
                    ThetaBody_alt St6.types
                      ((λˢ [z]) [rho.pair gamma] body) := by
                rw [St6_types_eq]
                exact target_respects_lambda_alt
              have Theta_wt_alt : ∀ v ∈ SMT.fv body,
                  ∀ d : SMT.Dom.{u}, ThetaBody_alt v = some d →
                  ∀ sigma, St3.types.lookup v = some sigma →
                    d.snd.fst = sigma := by
                intro v hv d hd sigma hlookup
                by_cases hvz : v = z
                · subst v
                  have hz_none : ThetaBody_alt z = none :=
                    ThetaBody_alt_none z z_not_used
                  rw [hz_none] at hd
                  contradiction
                · obtain ⟨d', hd', htype⟩ :=
                      target_respects_lambda_alt
                        (by
                          simp only [SMT.fv, List.mem_removeAll_iff]
                          exact ⟨hv, List.mem_singleton.not.mpr hvz⟩)
                        hlookup
                  rw [hd] at hd'
                  cases hd'
                  exact htype
              obtain ⟨hbody_isSome_alt, _hbody_type_alt⟩ :=
                SMT.RenamingContext.denote_update_total_and_type_of_typing
                  typ_body Theta_wt_alt hcov_body_upd_alt
              have hbody_total_alt : ∀ W : SMT.Dom.{u},
                  W.snd.fst = rho.pair gamma →
                  ∃ bodyVal : SMT.Dom.{u},
                    ⟦body.abstract
                      (Function.update ThetaBody_alt z (some W))
                      (hcov_body_upd_alt W)⟧ˢ = some bodyVal := by
                intro W hW
                exact Option.isSome_iff_exists.mp
                  (hbody_isSome_alt W hW)
              have respects_P_alt_St2 :
                  B.RenamingContext.RespectsTypeContextOnFV
                    ThetaBody_alt St2.types P := by
                intro v sigma hv hlookup
                exact respects_P_alt_out hv
                  (AList.lookup_of_subset St2_sub_St3 hlookup)
              have source_respects_upd_alt :
                  ∀ ss' : Fin vs.length → SMT.Dom.{u},
                  (∀ i, St2.types.lookup vs[i] =
                    some (ss' i).snd.fst) →
                  B.RenamingContext.RespectsTypeContextOnFV
                    (Function.updates ThetaBody_alt vs
                      ((List.ofFn ss').map Option.some))
                    St2.types P := by
                intro ss' hss
                apply B.RenamingContext.RespectsTypeContextOnFV.updates_of_typed_bounds
                  vs_nodup
                · intro v hv hvs sigma hlookup
                  exact respects_P_alt_St2 hv hlookup
                · exact hss
              have ambient_P_final_alt : ∀ v ∈ B.fv P,
                  v ∉ vs →
                  match Xi_alt v, ThetaBody_alt v with
                  | some source, some target =>
                      RDomCastSupported source target
                  | _, _ => False := by
                intro v hv hvs
                exact related_out_alt v
                  (B.fv.mem_lambda (.inr ⟨hv, hvs⟩))
              have wf_bound_alt : ∀ (x' : ZFSet.{u})
                  (hx' : x' ∈ ⟦tau⟧ᶻ)
                  (_hxD : x' ∈ Dval_alt),
                  B.RenWF Ebody.context
                    (Function.updates Xi_alt vs
                      (List.ofFn fun i => some
                        (⟨x'.get vs.length i,
                          tau.get vs.length i,
                          get_mem_type_of_isTuple
                            (hasArity_of_mem_toZFSet tau_hasArity hx')
                            tau_hasArity hx'⟩ : B.Dom))) := by
                intro x' hx' _hxD
                exact wf_seed_alt _ (fun _ => rfl)
              obtain ⟨lamVal_alt, hden_lambda_alt,
                  hlam_type_alt⟩ :=
                SMT.RenamingContext.denote_exists_of_typing_fv
                  (by simpa [body] using typ_out_St6)
                  target_respects_lambda_out_alt hcov_lambda_alt
              have hrel_lambda_alt : RDomCastSupported
                  (⟨T_alt, BType.set (tau ×ᴮ beta),
                    hT_alt_lambda⟩ : B.Dom) lamVal_alt := by
                exact represented_lambda_of_total_body
                  (D := D) (P := P) (tau := tau) (beta := beta)
                  (Xi := Xi_alt) (Dval := Dval_alt)
                  (hDval := hDval_alt) (T := T_alt)
                  (hT := hT_alt_lambda) (sigma := rho)
                  (gamma := gamma) (Denc := Denc) (Penc := Penc)
                  (body := body) (z := z) (ThetaD := ThetaBody_alt)
                  (DencVal := DencVal_alt) (lamVal := lamVal_alt)
                  (Ebody := Ebody) (LambdaP := St2.types)
                  (GammaP := St3.types) (usedP := St3.env.usedVars)
                  vs_nemp vs_nodup Xi_fv_alt tau_hasArity den_D_alt
                  den_alt_lambda rho_supported gamma_supported body_def
                  hcov_lambda_alt hden_lambda_alt hlam_type_alt
                  hcov_D_upd_alt hden_D_upd_alt hDenc_type_alt
                  hDenc_func_alt D_rel_alt hcov_body_upd_alt
                  hbody_total_alt hcov_sub_upd_alt hcov_P_upd_alt
                  hvs_not_bv z_not_bv_Penc z_not_vs typ_P P_total
                  ambient_P_final_alt wf_bound_alt bound_expected
                  source_respects_upd_alt fv_P_in_St2 Penc_fv_in_St2
                  St2_keys_used_St3 Penc_fv_vars z_not_vars_P
              refine ⟨ThetaBody_alt, hcov_lambda_alt, lamVal_alt,
                ThetaBody_alt_ext0, related_out_alt,
                ThetaBody_alt_none_out, respects_out_alt,
                target_respects_lambda_out_alt, ThetaBody_alt_dom_out,
                D_specs_true_out_alt, hden_lambda_alt, hlam_type_alt, ?_⟩
              simpa only [tau, proof_irrel_heq] using hrel_lambda_alt
          obtain ⟨lambda_path, lambda_typing, lambda_shape,
              ThetaOut, hcovOut, ThetaOut_ext, relatedOut,
              ThetaOut_none, respectsOut, targetRespectsOut,
              ThetaOut_dom, denOut, hdenOut, hdenOut_type,
              lambda_rel, lambda_scoped_total⟩ := hsemantic_scoped

          have St1_sub_St6 : St1.types ⊆ St6.types := by
            rw [St6_types_eq]
            exact St1_sub_St3_types
          have DCore_sub_St6 : DCore.entries ⊆ St6.types.entries :=
            AList.subset_trans DCore_sub_St1 St1_sub_St6

          have Denc_bv_not_DCore : ∀ v ∈ SMT.bv Denc,
              v ∉ DCore := by
            intro v hv hvCore
            exact SMT.Typing.bv_notMem_context typ_Denc v hv
              (AList.mem_of_subset DCore_sub_St1 hvCore)
          have typ_Denc_DCore : DCore ⊢ˢ Denc :
              SMTType.fun rho SMTType.bool :=
            D_sc_typing.1 DCore D_root_trace.scoped_extends
              Denc_bv_not_DCore

          have Penc_bv_not_body_base : ∀ v ∈ SMT.bv Penc,
              v ∉ DCore.update vs sigmas vs_sigmas_len := by
            intro v hv hvBase
            exact SMT.Typing.bv_notMem_context typ_Penc_St2 v hv
              (AList.mem_of_subset DCore_update_sub_St2 hvBase)
          have typ_Penc_body_base :
              DCore.update vs sigmas vs_sigmas_len ⊢ˢ Penc : gamma := by
            apply P_scoped_typing.1
            · simpa using
                (DeclarationContextEnvelope.refl
                  (DCore.update vs sigmas vs_sigmas_len)).scoped_extends
            · exact Penc_bv_not_body_base

          have hdest_length : vs.length =
              (toDestPair vs (SMT.Term.fst (.var z))).length := by
            rw [toDestPair_length_gen vs (SMT.Term.fst (.var z))
              (SMT.Term.fst (.var z)) [] vs_nemp]
            simp
          have output_fv_DCore : ∀ v ∈ SMT.fv
              (SMT.Term.lambda [z] [rho.pair gamma]
                (SMT.Term.and
                  (SMT.Term.app Denc (SMT.Term.fst (.var z)))
                  (SMT.Term.eq (SMT.Term.snd (.var z))
                    (SMT.substList vs
                      (toDestPair vs (SMT.Term.fst (.var z))) Penc)))),
              v ∈ DCore := by
            intro v hv
            simp only [SMT.fv, List.mem_removeAll_iff] at hv
            obtain ⟨hv_body, hv_ne_z⟩ := hv
            have hvz : v ≠ z := List.mem_singleton.not.mp hv_ne_z
            simp only [SMT.fv, List.mem_append,
              List.mem_singleton] at hv_body
            rcases hv_body with (hv_D | hv_z1) | (hv_z2 | hv_sub)
            · exact SMT.Typing.mem_context_of_mem_fv typ_Denc_DCore hv_D
            · exact absurd hv_z1 hvz
            · exact absurd hv_z2 hvz
            · have hv_not_vs : v ∉ vs := by
                intro hvs
                exact (SMT_not_mem_fv_substList_of_mem_vars
                  (Nat.le_of_eq hdest_length) hvs
                  (fun t ht hv_t => hvz <|
                    SMT_fv_toDestPair_subset_base
                      (t₀ := SMT.Term.fst (.var z))
                      (by intro w hw; simpa [SMT.fv] using hw)
                      ht hv_t)) hv_sub
              rcases SMT_mem_fv_substList hv_sub with hv_P |
                  ⟨t, ht, hv_t⟩
              · have hvBase := SMT.Typing.mem_context_of_mem_fv
                    typ_Penc_body_base hv_P
                rcases (SMT.TypeContext.mem_update_iff DCore v vs sigmas
                  vs_sigmas_len).mp hvBase with hvs | hCore
                · exact absurd hvs hv_not_vs
                · exact hCore
              · exact absurd
                  (SMT_fv_toDestPair_subset_base
                    (t₀ := SMT.Term.fst (.var z))
                    (by intro w hw; simpa [SMT.fv] using hw)
                    ht hv_t) hvz
          have typ_out_DCore : DCore ⊢ˢ
              SMT.Term.lambda [z] [rho.pair gamma]
                (SMT.Term.and
                  (SMT.Term.app Denc (SMT.Term.fst (.var z)))
                  (SMT.Term.eq (SMT.Term.snd (.var z))
                    (SMT.substList vs
                      (toDestPair vs (SMT.Term.fst (.var z))) Penc))) :
              SMTType.fun (rho.pair gamma) SMTType.bool :=
            SMT.Typing.strengthening_of_fv_subset DCore_sub_St6
              typ_out_St6 output_fv_DCore
          have lambda_scoped_typing : ScopedGeneratedTyping St0.types DltD
              (SMT.Term.lambda [z] [rho.pair gamma]
                (SMT.Term.and
                  (SMT.Term.app Denc (SMT.Term.fst (.var z)))
                  (SMT.Term.eq (SMT.Term.snd (.var z))
                    (SMT.substList vs
                      (toDestPair vs (SMT.Term.fst (.var z))) Penc))))
              (SMTType.fun (rho.pair gamma) SMTType.bool) := by
            constructor
            · intro GammaSup hscope hbv
              have DCore_sub_sup : DCore.entries ⊆ GammaSup.entries := by
                intro e he
                exact hscope (D_root_trace.context_generated he)
              exact SMT.Typing.weakening DCore_sub_sup typ_out_DCore hbv
            · simpa using D_sc_typing.2

          have D_specs_bv_not_St3 : ∀ b ∈ specBodies DltD,
              ∀ v ∈ SMT.bv b, v ∉ St3.types := by
            intro b hb v hv hvSt3
            have hv_used_St2 : v ∈ St2.env.usedVars :=
              St1_sub_St2_used (D_delta_used.2 b hb v hv)
            have hv_not_St1 : v ∉ St1.types :=
              SMT.Typing.bv_notMem_context (D_specs_op b hb) v hv
            have hv_not_vs : v ∉ vs := by
              intro hvs
              exact D_delta_not_used.2 b hb v hv <| by
                rw [St0_used]
                exact vars_used_vs v hvs
            have hv_not_St2 : v ∉ St2.types := by
              rw [St2_update]
              intro hvSt2
              rcases (SMT.TypeContext.mem_update_iff
                St1.types v vs sigmas vs_sigmas_len).mp hvSt2 with
                hvs | hvSt1
              · exact hv_not_vs hvs
              · exact hv_not_St1 hvSt1
            have hv_not_Pvars : v ∉ B.Term.vars P := by
              intro hvP
              exact D_delta_not_used.2 b hb v hv <| by
                rw [St0_used]
                exact vars_used_P v hvP
            exact P_preserves v hv_used_St2 hv_not_St2
              hv_not_Pvars hvSt3
          have D_specs_final : ∀ b ∈ specBodies DltD,
              St6.types ⊢ˢ b : SMTType.bool := by
            intro b hb
            rw [St6_types_eq]
            exact SMT.Typing.weakening St1_sub_St3_types
              (D_specs_op b hb) (D_specs_bv_not_St3 b hb)

          have lambda_guard : EncodeTermRepGuardedSound.{u}
              (B.Term.lambda vs D P) E (BType.set (tau ×ᴮ beta))
              (SMT.Term.lambda [z] [rho.pair gamma]
                (SMT.Term.and
                  (SMT.Term.app Denc (SMT.Term.fst (.var z)))
                  (SMT.Term.eq (SMT.Term.snd (.var z))
                    (SMT.substList vs
                      (toDestPair vs (SMT.Term.fst (.var z))) Penc))))
              (SMTType.fun (rho.pair gamma) SMTType.bool)
              St0.types DltD := by
            intro GammaSup parent_scope Xi_alt Xi_fv_alt Theta
              related_alt wf_alt source_respects_sup target_respects_sup
              specs_true T_alt hT_alt den_alt hcov_lambda_alt lamVal_alt
              hden_lambda_alt hlam_type_alt
            have Xi_fv_D_alt : ∀ v ∈ B.fv D,
                (Xi_alt v).isSome = true :=
              fun v hv => Xi_fv_alt v (B.fv.mem_lambda (.inl hv))
            obtain ⟨Dval_alt, hDval_alt, den_D_alt⟩ :=
              B.denote_lambda_domain_exists Xi_fv_alt typ_D wf_alt den_alt
            have related_D_alt : RValuationCastSupportedOnFV
                Xi_alt Theta D :=
              related_alt.mono_fv
                (fun _ hv => B.fv.mem_lambda (.inl hv))
            have source_respects_D_alt :
                B.RenamingContext.RespectsTypeContextOnFV
                  Theta GammaSup D :=
              source_respects_sup.mono_fv
                (fun _ hv => B.fv.mem_lambda (.inl hv))
            have z_not_fv_Denc_guard : z ∉ SMT.fv Denc := by
              intro hz
              exact z_fresh
                (SMT.Typing.mem_context_of_mem_fv typ_Denc_St3 hz)
            have z_not_fv_Penc_guard : z ∉ SMT.fv Penc := by
              intro hz
              exact z_fresh
                (SMT.Typing.mem_context_of_mem_fv typ_Penc hz)
            have z_not_vs_guard : z ∉ vs := by
              intro hz
              exact z_not_used
                (used_sub_St3 (vs_used_St2 z hz))
            have hvs_not_bv_guard : ∀ v ∈ vs, v ∉ SMT.bv Penc := by
              intro v hv hbv
              exact bv_Penc_not_used v hbv (vs_used_St2 v hv)
            have z_not_vars_P_guard : z ∉ B.Term.vars P := by
              intro hz
              exact z_not_used
                (used_sub_St3 (vars_used_P_St2 z hz))
            have hcov_body_upd_guard : ∀ W : SMT.Dom.{u},
                SMT.RenamingContext.CoversFV
                  (Function.update Theta z (some W))
                  (SMT.Term.and
                    (SMT.Term.app Denc (SMT.Term.fst (.var z)))
                    (SMT.Term.eq (SMT.Term.snd (.var z))
                      (SMT.substList vs
                        (toDestPair vs
                          (SMT.Term.fst (.var z))) Penc))) := by
              intro W v hv
              by_cases hvz : v = z
              · subst v
                simp
              · rw [Function.update_of_ne hvz]
                apply hcov_lambda_alt v
                simp only [SMT.fv, List.mem_removeAll_iff]
                exact ⟨by
                  simpa only [SMT.fv, List.mem_append,
                    List.mem_singleton] using hv,
                  by simpa using hvz⟩
            have Denc_fv_in_lambda_guard : ∀ v ∈ SMT.fv Denc,
                v ∈ SMT.fv
                  (SMT.Term.lambda [z] [rho.pair gamma]
                    (SMT.Term.and
                      (SMT.Term.app Denc (SMT.Term.fst (.var z)))
                      (SMT.Term.eq (SMT.Term.snd (.var z))
                        (SMT.substList vs
                          (toDestPair vs
                            (SMT.Term.fst (.var z))) Penc)))) := by
              intro v hv
              have hvz : v ≠ z := fun h =>
                z_not_fv_Denc_guard (h ▸ hv)
              simp only [SMT.fv, List.mem_removeAll_iff,
                List.mem_append, List.mem_singleton]
              exact ⟨Or.inl (Or.inl hv), by simpa using hvz⟩
            have hcov_D_guard : SMT.RenamingContext.CoversFV
                Theta Denc :=
              fun v hv => hcov_lambda_alt v
                (Denc_fv_in_lambda_guard v hv)
            have target_respects_D_guard :
                SMT.RenamingContext.RespectsTypeContextOnFV
                  Theta GammaSup Denc :=
              fun v sigma hv hlookup => target_respects_sup
                (Denc_fv_in_lambda_guard v hv) hlookup
            obtain ⟨DencVal_guard, hden_D_guard,
                hDenc_type_guard⟩ :=
              lambda_domain_denote_of_lambda_denote
                (Denc := Denc)
                (Psub := SMT.substList vs
                  (toDestPair vs (SMT.Term.fst (.var z))) Penc)
                hcov_lambda_alt hden_lambda_alt hcov_body_upd_guard
                hcov_D_guard z_not_fv_Denc_guard
            have D_rel_guard : RDomCastSupported
                (⟨Dval_alt, BType.set tau, hDval_alt⟩ : B.Dom)
                DencVal_guard := by
              exact D_guard GammaSup (by simpa using parent_scope)
                Xi_alt Xi_fv_D_alt Theta related_D_alt wf_alt
                source_respects_D_alt target_respects_D_guard specs_true
                Dval_alt hDval_alt den_D_alt hcov_D_guard DencVal_guard
                hden_D_guard hDenc_type_guard
            have hcov_D_upd_guard : ∀ W : SMT.Dom.{u},
                SMT.RenamingContext.CoversFV
                  (Function.update Theta z (some W)) Denc := by
              intro W
              exact SMT.RenamingContext.coversFV_update_of_notMem
                z_not_fv_Denc_guard hcov_D_guard
            have hden_D_upd_guard : ∀ W : SMT.Dom.{u},
                ⟦Denc.abstract (Function.update Theta z (some W))
                  (hcov_D_upd_guard W)⟧ˢ = some DencVal_guard := by
              intro W
              calc
                ⟦Denc.abstract (Function.update Theta z (some W))
                    (hcov_D_upd_guard W)⟧ˢ =
                    ⟦Denc.abstract Theta hcov_D_guard⟧ˢ := by
                  exact (SMT.RenamingContext.denote_update_of_notMem
                    (h := hcov_D_guard) z_not_fv_Denc_guard).symm
                _ = some DencVal_guard := hden_D_guard
            have hDenc_func_guard :
                ⟦rho⟧ᶻ.IsFunc 𝔹 DencVal_guard.fst := by
              have hmem : DencVal_guard.fst ∈
                  ⟦SMTType.fun rho SMTType.bool⟧ᶻ := by
                rw [← hDenc_type_guard]
                exact DencVal_guard.snd.snd
              rw [SMTType.toZFSet] at hmem
              exact ZFSet.mem_funs.mp hmem
            have hbody_total_guard : ∀ W : SMT.Dom.{u},
                W.snd.fst = rho.pair gamma →
                ∃ bodyVal : SMT.Dom.{u},
                  ⟦(SMT.Term.and
                    (SMT.Term.app Denc (SMT.Term.fst (.var z)))
                    (SMT.Term.eq (SMT.Term.snd (.var z))
                      (SMT.substList vs
                        (toDestPair vs
                          (SMT.Term.fst (.var z))) Penc))).abstract
                    (Function.update Theta z (some W))
                    (hcov_body_upd_guard W)⟧ˢ = some bodyVal :=
              lambda_body_total_of_denote hcov_lambda_alt
                hden_lambda_alt hcov_body_upd_guard
            have hcov_sub_upd_guard : ∀ W : SMT.Dom.{u},
                SMT.RenamingContext.CoversFV
                  (Function.update Theta z (some W))
                  (SMT.substList vs
                    (toDestPair vs (SMT.Term.fst (.var z))) Penc) := by
              intro W v hv
              apply hcov_body_upd_guard W v
              simp only [SMT.fv, List.mem_append, List.mem_singleton]
              exact Or.inr (Or.inr hv)
            have toDest_fv_disj_vs_guard :
                ∀ q ∈ toDestPair vs (SMT.Term.fst (.var z)),
                  ∀ v ∈ SMT.fv q, v ∉ vs := by
              intro q hq v hv hvs
              have hvz := SMT_fv_toDestPair_subset_base
                (t₀ := SMT.Term.fst (.var z))
                (by intro w hw; simpa [SMT.fv] using hw) hq hv
              subst v
              exact z_not_vs_guard hvs
            have Penc_fv_in_lambda_guard : ∀ v ∈ SMT.fv Penc,
                v ∉ vs →
                v ∈ SMT.fv
                  (SMT.Term.lambda [z] [rho.pair gamma]
                    (SMT.Term.and
                      (SMT.Term.app Denc (SMT.Term.fst (.var z)))
                      (SMT.Term.eq (SMT.Term.snd (.var z))
                        (SMT.substList vs
                          (toDestPair vs
                            (SMT.Term.fst (.var z))) Penc)))) := by
              intro v hv hvs
              have hv_sub :=
                SMT.RenamingContext.fv_mem_fv_substList_no_bv
                  hv hvs toDest_fv_disj_vs_guard
              have hvz : v ≠ z := fun h =>
                z_not_fv_Penc_guard (h ▸ hv)
              simp only [SMT.fv, List.mem_removeAll_iff,
                List.mem_append, List.mem_singleton]
              exact ⟨Or.inr (Or.inr hv_sub), by simpa using hvz⟩
            have hcov_P_upd_guard : ∀ (W : SMT.Dom.{u})
                (ss' : Fin vs.length → SMT.Dom.{u}),
                SMT.RenamingContext.CoversFV
                  (Function.updates
                    (Function.update Theta z (some W)) vs
                    ((List.ofFn ss').map Option.some)) Penc := by
              intro W ss' v hv
              by_cases hvs : v ∈ vs
              · rw [Function.updates_eq_if
                    (by rw [List.length_map, List.length_ofFn]) vs_nodup,
                  dif_pos hvs]
                simp
              · rw [Function.updates_of_not_mem _ vs _ _ hvs,
                  Function.update_of_ne (by
                    intro heq
                    exact z_not_fv_Penc_guard (heq ▸ hv))]
                exact hcov_lambda_alt v
                  (Penc_fv_in_lambda_guard v hv hvs)
            have bound_expected_guard : ∀ i : Fin vs.length,
                St2.types.lookup vs[i] =
                  some ((rho.fromProdl (vs.length - 1))[i.val]'(by
                    have hlen :=
                      rho_supported.fromProdl_length_of_hasArity tau_hasArity
                    exact i.isLt.trans_eq hlen.symm)) := by
              intro i
              have hlookup : St2.types.lookup vs[i] =
                  some (sigmas[i.val]'(by
                    rw [sigmas_len]
                    exact i.isLt)) := by
                rw [St2_update]
                exact SMT.TypeContext.lookup_update_of_mem_nodup
                  St1.types vs_nodup vs_sigmas_len i.isLt
              simpa [sigmas] using hlookup
            have DCore_sub_sup : DCore.entries ⊆ GammaSup.entries := by
              intro e he
              exact parent_scope (D_root_trace.context_generated he)
            have source_respects_upd_guard :
                ∀ ss' : Fin vs.length → SMT.Dom.{u},
                (∀ i, St2.types.lookup vs[i] =
                  some (ss' i).snd.fst) →
                B.RenamingContext.RespectsTypeContextOnFV
                  (Function.updates Theta vs
                    ((List.ofFn ss').map Option.some)) St2.types P := by
              intro ss' hss
              apply B.RenamingContext.RespectsTypeContextOnFV.updates_of_typed_bounds
                vs_nodup
              · intro v hv hvs sigma hlookup
                have hvBase := fv_P_in_body_base v hv
                rcases (SMT.TypeContext.mem_update_iff DCore v vs sigmas
                  vs_sigmas_len).mp hvBase with hv_bound | hvCore
                · exact absurd hv_bound hvs
                · obtain ⟨sigma0, hCore⟩ :=
                    Option.isSome_iff_exists.mp
                      (AList.lookup_isSome.mpr hvCore)
                  have hSt1 : St1.types.lookup v = some sigma0 :=
                    AList.lookup_of_subset DCore_sub_St1 hCore
                  have hSt2 : St2.types.lookup v = some sigma0 := by
                    rw [St2_update,
                      SMT.TypeContext.lookup_update
                        St1.types v vs sigmas vs_sigmas_len hvs]
                    exact hSt1
                  have hSup : GammaSup.lookup v = some sigma0 :=
                    AList.lookup_of_subset DCore_sub_sup hCore
                  obtain ⟨d, hd, hdtype⟩ := source_respects_sup
                    (B.fv.mem_lambda (.inr ⟨hv, hvs⟩)) hSup
                  refine ⟨d, hd, hdtype.trans ?_⟩
                  exact Option.some.inj (hSt2.symm.trans hlookup)
              · exact hss
            have ambient_P_guard : ∀ v ∈ B.fv P, v ∉ vs →
                match Xi_alt v, Theta v with
                | some source, some target =>
                    RDomCastSupported source target
                | _, _ => False := by
              intro v hv hvs
              exact related_alt v
                (B.fv.mem_lambda (.inr ⟨hv, hvs⟩))
            have wf_bound_guard : ∀ (x' : ZFSet.{u})
                (hx' : x' ∈ ⟦tau⟧ᶻ) (_hxD : x' ∈ Dval_alt),
                B.RenWF Ebody.context
                  (Function.updates Xi_alt vs
                    (List.ofFn fun i => some
                      (⟨x'.get vs.length i, tau.get vs.length i,
                        get_mem_type_of_isTuple
                          (hasArity_of_mem_toZFSet tau_hasArity hx')
                          tau_hasArity hx'⟩ : B.Dom))) := by
              intro x' hx' _hxD
              exact B.RenWF.updates_ofFn wf_alt vs_nodup
                vs_context_disj vs_alphas_len (fun i => by
                  calc
                    (⟨x'.get vs.length i, tau.get vs.length i,
                      get_mem_type_of_isTuple
                        (hasArity_of_mem_toZFSet tau_hasArity hx')
                        tau_hasArity hx'⟩ : B.Dom).snd.fst =
                        tau.get vs.length i := rfl
                    _ = alphas[Fin.cast vs_alphas_len i] := by
                      simpa [tau] using
                        BType.get_reduce alphas_nemp vs_alphas_len i)
            have St2_keys_used_St3_guard : St2.types.keys ⊆
                St3.env.usedVars :=
              fun v hv => used_sub_St3 (St2_keys_sub hv)
            exact represented_lambda_of_total_body
              (D := D) (P := P) (tau := tau) (beta := beta)
              (Xi := Xi_alt) (Dval := Dval_alt) (hDval := hDval_alt)
              (T := T_alt) (hT := hT_alt) (sigma := rho)
              (gamma := gamma) (Denc := Denc) (Penc := Penc)
              (body := SMT.Term.and
                (SMT.Term.app Denc (SMT.Term.fst (.var z)))
                (SMT.Term.eq (SMT.Term.snd (.var z))
                  (SMT.substList vs
                    (toDestPair vs (SMT.Term.fst (.var z))) Penc)))
              (z := z) (ThetaD := Theta) (DencVal := DencVal_guard)
              (lamVal := lamVal_alt) (Ebody := Ebody)
              (LambdaP := St2.types) (GammaP := St3.types)
              (usedP := St3.env.usedVars) vs_nemp vs_nodup Xi_fv_alt
              tau_hasArity den_D_alt den_alt rho_supported gamma_supported
              rfl hcov_lambda_alt hden_lambda_alt hlam_type_alt
              hcov_D_upd_guard hden_D_upd_guard hDenc_type_guard
              hDenc_func_guard D_rel_guard hcov_body_upd_guard
              hbody_total_guard hcov_sub_upd_guard hcov_P_upd_guard
              hvs_not_bv_guard z_not_bv_Penc z_not_vs_guard typ_P
              P_total ambient_P_guard wf_bound_guard bound_expected_guard
              source_respects_upd_guard fv_P_in_St2 Penc_fv_in_St2
              St2_keys_used_St3_guard Penc_fv_vars z_not_vars_P_guard

          have lambda_semantic : EncodeTermRepSemanticPost.{u}
              (B.Term.lambda vs D P) (BType.set (tau ×ᴮ beta))
              St0.types Xi Theta0 T hT_parent E
              (SMT.Term.lambda [z] [rho.pair gamma]
                (SMT.Term.and
                  (SMT.Term.app Denc (SMT.Term.fst (.var z)))
                  (SMT.Term.eq (SMT.Term.snd (.var z))
                    (SMT.substList vs
                      (toDestPair vs (SMT.Term.fst (.var z))) Penc))))
              (SMTType.fun (rho.pair gamma) SMTType.bool)
              St6.env St6.types := by
            refine ⟨lambda_path, lambda_typing, lambda_shape,
              ThetaOut, hcovOut, ThetaOut_ext, relatedOut,
              ThetaOut_none, respectsOut, targetRespectsOut,
              ThetaOut_dom, denOut, hdenOut, hdenOut_type,
              lambda_rel, ?_⟩
            exact lambda_scoped_total.to_total

          have scoped_post_tau : EncodeTermRepScopedPost.{u}
              (B.Term.lambda vs D P) E (BType.set (tau ×ᴮ beta))
              St0.types decl
              (SMT.Term.lambda [z] [rho.pair gamma]
                (SMT.Term.and
                  (SMT.Term.app Denc (SMT.Term.fst (.var z)))
                  (SMT.Term.eq (SMT.Term.snd (.var z))
                    (SMT.substList vs
                      (toDestPair vs (SMT.Term.fst (.var z))) Penc))))
              (SMTType.fun (rho.pair gamma) SMTType.bool)
              St6.env St6.types := by
            refine ⟨DltD, ?_, ?_, ?_, lambda_scoped_total, ?_,
              D_specs_final, lambda_scoped_typing⟩
            · rw [St6_decl, St4_decl, P_decl_stable, St2_decl,
                D_scoped_decl, St0_decl]
            · exact D_op_envelope.mono St1_sub_St6
            · exact ⟨DCore, D_root_trace, DCore_sub_St6⟩
            · exact lambda_guard

          refine ⟨?_, ?_⟩
          · simpa only [tau, proof_irrel_heq] using
              (encodeTermRepPost_of_state_and_semantic hstate
                lambda_semantic)
          · simpa only [tau, proof_irrel_heq] using scoped_post_tau
      | int =>
          simp only [Prod.snd]
          mvcgen
      | unit =>
          simp only [Prod.snd]
          mvcgen
      | «fun» sigma gamma =>
          simp only [Prod.snd]
          mvcgen
      | option sigma =>
          simp only [Prod.snd]
          mvcgen
      | pair sigma gamma =>
          simp only [Prod.snd]
          mvcgen
