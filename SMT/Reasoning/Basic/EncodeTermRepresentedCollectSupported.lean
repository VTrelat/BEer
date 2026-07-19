import SMT.Reasoning.Basic.EncodeTermRepresentedLambda

open Std.Do B SMT ZFSet Classical

/-! # Supported collection-predicate semantics

This module lifts the set-valued collection proof from canonical tuple
representatives to every `BType.SupportedSMT` tuple representation.  The
operational raw encoder proof imports these semantic bridges after it has
fixed the concrete represented tuple type emitted by the domain encoder.
-/

/-- A true collection body cannot have taken the generated `false` fallback,
so its encoded domain test was true. -/
theorem collect_ite_true_implies_domain_true.{u}
    {Dapp Psub body : SMT.Term}
    {Theta : SMT.RenamingContext.Context.{u}}
    (hbody_def : body = Dapp.ite Psub (.bool false))
    (hcov_body : SMT.RenamingContext.CoversFV Theta body)
    (hcov_Dapp : SMT.RenamingContext.CoversFV Theta Dapp)
    {dD dBody : SMT.Dom.{u}}
    (hden_Dapp : ⟦Dapp.abstract Theta hcov_Dapp⟧ˢ = some dD)
    (hden_body : ⟦body.abstract Theta hcov_body⟧ˢ = some dBody)
    (hD_type : dD.snd.fst = SMTType.bool)
    (hbody_true : dBody.fst = ZFSet.zftrue) :
    dD.fst = ZFSet.zftrue := by
  rcases dD with ⟨Dval, sigmaD, hDmem⟩
  dsimp at hD_type hbody_true ⊢
  subst sigmaD
  have hDmem_bool : Dval ∈ ZFSet.𝔹 := by
    simpa [SMTType.toZFSet] using hDmem
  rcases ZFSet.ZFBool.mem_𝔹_iff Dval |>.mp hDmem_bool with hfalse | htrue
  · have hfalse_body :
        ⟦body.abstract Theta hcov_body⟧ˢ =
          some (⟨ZFSet.zffalse, SMTType.bool,
            ZFSet.ZFBool.zffalse_mem_𝔹⟩ : SMT.Dom) := by
      subst body
      rw [SMT.Term.abstract, SMT.denote, Option.bind_eq_bind]
      conv_lhs =>
        rw [SMT.RenamingContext.denote_abstract_proof_irrel
          Dapp Theta _ hcov_Dapp]
      rw [hden_Dapp]
      simp only [Option.bind_some]
      have hDval :
          (⟨Dval, hDmem_bool⟩ : ZFSet.ZFBool) =
            ⟨ZFSet.zffalse, ZFSet.ZFBool.zffalse_mem_𝔹⟩ :=
        Subtype.ext hfalse
      rw [hDval, show (⟨ZFSet.zffalse,
        ZFSet.ZFBool.zffalse_mem_𝔹⟩ : ZFSet.ZFBool) = ⊥ by rfl,
        ZFSet.ZFBool.toBool_false]
      simp [SMT.Term.abstract, SMT.denote, ZFSet.ZFBool.ofBool]
    rw [hfalse_body] at hden_body
    have hfst : dBody.fst = ZFSet.zffalse :=
      congrArg (fun d : SMT.Dom => d.fst) (Option.some.inj hden_body).symm
    exact (ZFSet.zftrue_ne_zffalse (hbody_true.symm.trans hfst)).elim
  · exact htrue

/-- Applying a represented domain predicate to a supported representative of
a source member produces SMT `true`. -/
theorem represented_set_app_true_of_mem_supported.{u}
    {tau : BType} {rho : SMTType}
    {S : ZFSet.{u}} {hS : S ∈ ⟦BType.set tau⟧ᶻ}
    {Denc : SMT.Term} {z : SMT.𝒱}
    {Theta : SMT.RenamingContext.Context.{u}} {Dval : SMT.Dom.{u}}
    (hcov_D_upd : ∀ W : SMT.Dom,
      SMT.RenamingContext.CoversFV
        (Function.update Theta z (some W)) Denc)
    (den_D_upd : ∀ W : SMT.Dom,
      ⟦Denc.abstract (Function.update Theta z (some W))
        (hcov_D_upd W)⟧ˢ = some Dval)
    (hD_type : Dval.snd.fst = rho.fun SMTType.bool)
    (hD_func : ⟦rho⟧ᶻ.IsFunc ZFSet.𝔹 Dval.fst)
    (D_rel : RDomCastSupported
      (⟨S, BType.set tau, hS⟩ : B.Dom) Dval)
    {x y : ZFSet.{u}} {hx : x ∈ ⟦tau⟧ᶻ} {hy : y ∈ ⟦rho⟧ᶻ}
    (X_rel : RDomCastSupported
      (⟨x, tau, hx⟩ : B.Dom) (⟨y, rho, hy⟩ : SMT.Dom))
    (hxS : x ∈ S) :
    let W : SMT.Dom := ⟨y, rho, hy⟩
    ∃ (hcov : SMT.RenamingContext.CoversFV
        (Function.update Theta z (some W)) ((@ˢDenc) (.var z)))
      (Dapp : SMT.Dom.{u}),
      ⟦((@ˢDenc) (.var z)).abstract
        (Function.update Theta z (some W)) hcov⟧ˢ = some Dapp ∧
      Dapp.snd.fst = SMTType.bool ∧
      Dapp.fst = ZFSet.zftrue := by
  rcases Dval with ⟨F, sigmaD, hF⟩
  dsimp at hD_type hD_func den_D_upd D_rel
  subst sigmaD
  dsimp only
  let W : SMT.Dom := ⟨y, rho, hy⟩
  obtain ⟨hcov_app, Dapp, hDapp_type, hDapp_value, hden_app⟩ :=
    funDenoteAppAt (Δctx := Theta) (t := Denc) (x := z)
      (α := rho) (β := SMTType.bool)
      (Y := (⟨F, rho.fun SMTType.bool, hF⟩ : SMT.Dom))
      hcov_D_upd den_D_upd rfl hD_func W rfl hy
  refine ⟨hcov_app, Dapp, hden_app, hDapp_type, ?_⟩
  rw [hDapp_value]
  exact (RDomCastSupported.setPred_fapply_eq_zftrue_iff
    X_rel.toRDomCast D_rel).mpr hxS

/-- Transfer one represented collection-body evaluation back to the source
predicate while preserving the actual tuple representation `rho`. -/
theorem represented_collect_pointwise_body_bridge_supported.{u}
    {vs : List B.𝒱} (vs_nemp : vs ≠ []) (vs_nodup : vs.Nodup)
    {D P : B.Term} {tau : BType} {rho : SMTType}
    (rho_supported : BType.SupportedSMT tau rho)
    {Xi : B.RenamingContext.Context.{u}}
    (Xi_fv : ∀ v ∈ B.fv (B.Term.collect vs D P), (Xi v).isSome = true)
    (tau_hasArity : tau.hasArity vs.length)
    {Dval : ZFSet.{u}} {hDval : Dval ∈ ⟦BType.set tau⟧ᶻ}
    (den_D : ⟦D.abstract Xi
      (fun v hv => Xi_fv v (B.fv.mem_collect (.inl hv)))⟧ᴮ =
      some (⟨Dval, BType.set tau, hDval⟩ : B.Dom))
    {T : ZFSet.{u}} {hT : T ∈ ⟦BType.set tau⟧ᶻ}
    (den_collect : ⟦(B.Term.collect vs D P).abstract Xi Xi_fv⟧ᴮ =
      some (⟨T, BType.set tau, hT⟩ : B.Dom))
    {Denc Penc ite_body : SMT.Term} {z : SMT.𝒱}
    {ThetaD : SMT.RenamingContext.Context.{u}} {DencVal : SMT.Dom.{u}}
    (hcov_D_upd : ∀ W : SMT.Dom,
      SMT.RenamingContext.CoversFV
        (Function.update ThetaD z (some W)) Denc)
    (den_D_upd : ∀ W : SMT.Dom,
      ⟦Denc.abstract (Function.update ThetaD z (some W))
        (hcov_D_upd W)⟧ˢ = some DencVal)
    (hDenc_type : DencVal.snd.fst = rho.fun SMTType.bool)
    (hDenc_func : ⟦rho⟧ᶻ.IsFunc 𝔹 DencVal.fst)
    (D_rel : RDomCastSupported
      (⟨Dval, BType.set tau, hDval⟩ : B.Dom) DencVal)
    (ite_body_def : ite_body = ((@ˢDenc) (.var z)).ite
      (SMT.substList vs (toDestPair vs (.var z)) Penc) (.bool false))
    (hcov_ite_upd : ∀ W : SMT.Dom,
      SMT.RenamingContext.CoversFV
        (Function.update ThetaD z (some W)) ite_body)
    (hcov_sub_upd : ∀ W : SMT.Dom,
      SMT.RenamingContext.CoversFV
        (Function.update ThetaD z (some W))
          (SMT.substList vs (toDestPair vs (.var z)) Penc))
    (hcov_P_upd : ∀ (W : SMT.Dom) (ss : Fin vs.length → SMT.Dom),
      SMT.RenamingContext.CoversFV
        (Function.updates (Function.update ThetaD z (some W)) vs
          ((List.ofFn ss).map Option.some)) Penc)
    (hvs_not_bv : ∀ v ∈ vs, v ∉ SMT.bv Penc)
    (hz_not_bv : z ∉ SMT.bv Penc) (hz_not_vs : z ∉ vs)
    {Ebody : B.Env} {LambdaP GammaP : SMT.TypeContext}
    {DltP : SMT.Chunk} {sigmaP : SMTType}
    (typ_P : Ebody.context ⊢ᴮ P : BType.bool)
    (P_guard : EncodeTermRepGuardedSound.{u}
      P Ebody BType.bool Penc sigmaP LambdaP DltP)
    (P_scope : ScopedContextExtends LambdaP DltP GammaP)
    (typ_Penc : GammaP ⊢ˢ Penc : sigmaP)
    (ambient : ∀ v ∈ B.fv P, v ∉ vs →
      match Xi v, ThetaD v with
      | some d, some d' => RDomCastSupported d d'
      | _, _ => False)
    (wf_bound : ∀ (x : ZFSet.{u}) (hx : x ∈ ⟦tau⟧ᶻ)
      (_hx_D : x ∈ Dval),
      B.RenWF Ebody.context
        (Function.updates Xi vs (List.ofFn fun i => some
          (⟨x.get vs.length i, tau.get vs.length i,
            get_mem_type_of_isTuple
              (hasArity_of_mem_toZFSet tau_hasArity hx)
              tau_hasArity hx⟩ : B.Dom))))
    (bound_expected : ∀ i : Fin vs.length,
      GammaP.lookup vs[i] = some
        ((rho.fromProdl (vs.length - 1))[i.val]'(by
          have hlen := rho_supported.fromProdl_length_of_hasArity
            tau_hasArity
          exact i.isLt.trans_eq hlen.symm)))
    (source_respects : ∀ (ss : Fin vs.length → SMT.Dom),
      (∀ i, GammaP.lookup vs[i] = some (ss i).snd.fst) →
      B.RenamingContext.RespectsTypeContextOnFV
        (Function.updates ThetaD vs
          ((List.ofFn ss).map Option.some)) GammaP P)
    (target_respects : ∀ (ss : Fin vs.length → SMT.Dom),
      (∀ i, GammaP.lookup vs[i] = some (ss i).snd.fst) →
      SMT.RenamingContext.RespectsTypeContextOnFV
        (Function.updates ThetaD vs
          ((List.ofFn ss).map Option.some)) GammaP Penc)
    (specs_true : ∀ (ss : Fin vs.length → SMT.Dom),
      (∀ i, GammaP.lookup vs[i] = some (ss i).snd.fst) →
      SpecBodiesTrue
        (Function.updates ThetaD vs
          ((List.ofFn ss).map Option.some)) GammaP DltP)
    (z_not_fv_Penc : z ∉ SMT.fv Penc) :
    ∀ (x : ZFSet.{u}) (hx_mem : x ∈ ⟦tau⟧ᶻ) (_hx_D : x ∈ Dval)
      (y : ZFSet.{u}) (hy : y ∈ ⟦rho⟧ᶻ)
      (_X_rel : RDomCastSupported
        (⟨x, tau, hx_mem⟩ : B.Dom) (⟨y, rho, hy⟩ : SMT.Dom))
      (body_val : SMT.Dom),
      ⟦ite_body.abstract
        (Function.update ThetaD z (some (⟨y, rho, hy⟩ : SMT.Dom)))
        (hcov_ite_upd (⟨y, rho, hy⟩ : SMT.Dom))⟧ˢ = some body_val →
      ∃ (Pval : ZFSet.{u}) (hPval : Pval ∈ ⟦BType.bool⟧ᶻ),
        ⟦(B.Term.abstract.go P vs Xi (fun v hv hvs => Xi_fv v
          (B.fv.mem_collect (.inr ⟨hv, hvs⟩)))).uncurry
          (fun i =>
            (⟨x.get vs.length i, tau.get vs.length i,
              get_mem_type_of_isTuple
                (hasArity_of_mem_toZFSet tau_hasArity hx_mem)
                tau_hasArity hx_mem⟩ : B.Dom))⟧ᴮ =
          some (⟨Pval, BType.bool, hPval⟩ : B.Dom) ∧
        (body_val.fst = ZFSet.zftrue ↔ Pval = ZFSet.zftrue) := by
  intro x hx_mem hx_D y hy X_rel body_val hden_body
  let W : SMT.Dom := ⟨y, rho, hy⟩
  let x_fin : Fin vs.length → B.Dom := fun i =>
    ⟨x.get vs.length i, tau.get vs.length i,
      get_mem_type_of_isTuple
        (hasArity_of_mem_toZFSet tau_hasArity hx_mem)
        tau_hasArity hx_mem⟩
  have hcov_z : SMT.RenamingContext.CoversFV
      (Function.update ThetaD z (some W)) (.var z) := by
    intro v hv
    simp only [SMT.fv, List.mem_singleton] at hv
    subst v
    simp
  have hden_z : ⟦(SMT.Term.var z).abstract
      (Function.update ThetaD z (some W)) hcov_z⟧ˢ = some W := by
    simp only [SMT.Term.abstract, Function.update_self, Option.get_some,
      SMT.denote, Option.pure_def]
  obtain ⟨hcov_Dapp, Dapp, hden_Dapp, hDapp_type, hDapp_true⟩ :=
    represented_set_app_true_of_mem_supported hcov_D_upd den_D_upd
      hDenc_type hDenc_func D_rel X_rel hx_D
  obtain ⟨ss, hcomponents, related_P⟩ :=
    represented_lambda_toDestPair_bound_context vs_nemp vs_nodup
      tau_hasArity rho_supported hx_mem hcov_z hden_z rfl hy X_rel ambient
  have hss_map : (List.ofFn ss).map Option.some =
      List.ofFn (fun i => some (ss i)) := by
    rw [List.map_ofFn]
    rfl
  have related_P' : RValuationCastSupportedOnFV
      (Function.updates Xi vs (List.ofFn fun i => some (x_fin i)))
      (Function.updates ThetaD vs
        ((List.ofFn ss).map Option.some)) P := by
    rw [hss_map]
    simpa [W, x_fin] using related_P
  have hss_type : ∀ i : Fin vs.length,
      GammaP.lookup vs[i] = some (ss i).snd.fst := by
    intro i
    obtain ⟨_, _, _, htype⟩ := hcomponents i
    exact (bound_expected i).trans (congrArg some htype).symm
  have hx_fin_typ : ∀ i, (x_fin i).snd.fst = tau.get vs.length i ∧
      (x_fin i).fst ∈ ⟦tau.get vs.length i⟧ᶻ :=
    fun i => ⟨rfl, (x_fin i).snd.snd⟩
  have hx_fin_eq : ZFSet.ofFinDom x_fin = x := by
    simpa [x_fin] using
      (ZFSet.ofFinDom_get (List.length_pos_iff.mpr vs_nemp)
        (fun i => get_mem_type_of_isTuple
          (hasArity_of_mem_toZFSet tau_hasArity hx_mem)
          tau_hasArity hx_mem)
        (hasArity_of_mem_toZFSet tau_hasArity hx_mem) tau_hasArity)
  have hx_fin_D : ZFSet.ofFinDom x_fin ∈ Dval := by
    rw [hx_fin_eq]
    exact hx_D
  obtain ⟨XiP_fv', Pval, hPval, den_P⟩ :=
    B.denote_collect_predicate_exists Xi_fv vs_nemp vs_nodup tau_hasArity
      den_D den_collect typ_P hx_fin_typ hx_fin_D
      (wf_bound x hx_mem hx_D)
  obtain ⟨Dp, hden_Psub, _hDp_type, htruth_P⟩ :=
    collect_subst_truth_of_guarded_body_toDestPair
      (Penc := Penc) vs_nemp vs_nodup (z := z) (DeltaCtx := ThetaD)
      (W := W) (ss := ss)
      (hcomponents := by
        intro i
        obtain ⟨hcov, hden, _, _⟩ := hcomponents i
        exact ⟨hcov, hden⟩)
      (hcov_sub := hcov_sub_upd W)
      (hcov_upd := hcov_P_upd W ss)
      hvs_not_bv hz_not_bv hz_not_vs P_guard P_scope typ_Penc
      XiP_fv' related_P' (wf_bound x hx_mem hx_D)
      (source_respects ss hss_type) (target_respects ss hss_type)
      (specs_true ss hss_type) den_P z_not_fv_Penc
  have hbody_eq : body_val = Dp :=
    collect_ite_truth_of_true_domain ite_body_def (hcov_ite_upd W)
      hcov_Dapp (hcov_sub_upd W) hden_Dapp hden_Psub hden_body
      hDapp_type hDapp_true
  have den_P_go :
      ⟦(B.Term.abstract.go P vs Xi (fun v hv hvs => Xi_fv v
        (B.fv.mem_collect (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ =
        some (⟨Pval, BType.bool, hPval⟩ : B.Dom) := by
    rw [denote_term_abstract_go_eq_term_abstract vs_nodup vs_nemp x_fin
      XiP_fv']
    exact den_P
  exact ⟨Pval, hPval, by simpa [x_fin] using den_P_go,
    by simpa [hbody_eq] using htruth_P⟩

/-- The Boolean lambda emitted for a set-valued collection represents the
source collection at every supported tuple representation. -/
theorem represented_collect_set_denote_supported.{u}
    {vs : List B.𝒱} (vs_nemp : vs ≠ []) (vs_nodup : vs.Nodup)
    {D P : B.Term} {tau : BType} {rho : SMTType}
    (rho_supported : BType.SupportedSMT tau rho)
    {Xi : B.RenamingContext.Context.{u}}
    (Xi_fv : ∀ v ∈ B.fv (B.Term.collect vs D P), (Xi v).isSome = true)
    (tau_hasArity : tau.hasArity vs.length)
    {Dval : ZFSet.{u}} {hDval : Dval ∈ ⟦BType.set tau⟧ᶻ}
    (den_D : ⟦D.abstract Xi
      (fun v hv => Xi_fv v (B.fv.mem_collect (.inl hv)))⟧ᴮ =
      some (⟨Dval, BType.set tau, hDval⟩ : B.Dom))
    {T : ZFSet.{u}} {hT : T ∈ ⟦BType.set tau⟧ᶻ}
    (den_collect : ⟦(B.Term.collect vs D P).abstract Xi Xi_fv⟧ᴮ =
      some (⟨T, BType.set tau, hT⟩ : B.Dom))
    {Denc Penc ite_body : SMT.Term} {z : SMT.𝒱}
    {ThetaD : SMT.RenamingContext.Context.{u}} {DencVal : SMT.Dom.{u}}
    (ite_body_def : ite_body = ((@ˢDenc) (.var z)).ite
      (SMT.substList vs (toDestPair vs (.var z)) Penc) (.bool false))
    (hcov_lambda : SMT.RenamingContext.CoversFV ThetaD
      ((λˢ [z]) [rho] ite_body))
    {GammaOut : SMT.TypeContext}
    (typ_lambda : GammaOut ⊢ˢ ((λˢ [z]) [rho] ite_body) :
      rho.fun SMTType.bool)
    (respects_lambda : SMT.RenamingContext.RespectsTypeContextOnFV
      ThetaD GammaOut ((λˢ [z]) [rho] ite_body))
    (hcov_D_upd : ∀ W : SMT.Dom,
      SMT.RenamingContext.CoversFV
        (Function.update ThetaD z (some W)) Denc)
    (den_D_upd : ∀ W : SMT.Dom,
      ⟦Denc.abstract (Function.update ThetaD z (some W))
        (hcov_D_upd W)⟧ˢ = some DencVal)
    (hDenc_type : DencVal.snd.fst = rho.fun SMTType.bool)
    (hDenc_func : ⟦rho⟧ᶻ.IsFunc 𝔹 DencVal.fst)
    (D_rel : RDomCastSupported
      (⟨Dval, BType.set tau, hDval⟩ : B.Dom) DencVal)
    (hcov_ite_upd : ∀ W : SMT.Dom,
      SMT.RenamingContext.CoversFV
        (Function.update ThetaD z (some W)) ite_body)
    {GammaBody : SMT.TypeContext}
    (typ_ite : GammaBody.insert z rho ⊢ˢ ite_body : SMTType.bool)
    (Theta_wt : ∀ v ∈ SMT.fv ite_body, ∀ d : SMT.Dom,
      ThetaD v = some d → ∀ sigma, GammaBody.lookup v = some sigma →
        d.snd.fst = sigma)
    (hcov_sub_upd : ∀ W : SMT.Dom,
      SMT.RenamingContext.CoversFV
        (Function.update ThetaD z (some W))
          (SMT.substList vs (toDestPair vs (.var z)) Penc))
    (hcov_P_upd : ∀ (W : SMT.Dom) (ss : Fin vs.length → SMT.Dom),
      SMT.RenamingContext.CoversFV
        (Function.updates (Function.update ThetaD z (some W)) vs
          ((List.ofFn ss).map Option.some)) Penc)
    (hvs_not_bv : ∀ v ∈ vs, v ∉ SMT.bv Penc)
    (hz_not_bv : z ∉ SMT.bv Penc) (hz_not_vs : z ∉ vs)
    {Ebody : B.Env} {LambdaP GammaP : SMT.TypeContext}
    {DltP : SMT.Chunk} {sigmaP : SMTType}
    (typ_P : Ebody.context ⊢ᴮ P : BType.bool)
    (P_guard : EncodeTermRepGuardedSound.{u}
      P Ebody BType.bool Penc sigmaP LambdaP DltP)
    (P_scope : ScopedContextExtends LambdaP DltP GammaP)
    (typ_Penc : GammaP ⊢ˢ Penc : sigmaP)
    (ambient : ∀ v ∈ B.fv P, v ∉ vs →
      match Xi v, ThetaD v with
      | some d, some d' => RDomCastSupported d d'
      | _, _ => False)
    (wf_bound : ∀ (x : ZFSet.{u}) (hx : x ∈ ⟦tau⟧ᶻ)
      (_hx_D : x ∈ Dval),
      B.RenWF Ebody.context
        (Function.updates Xi vs (List.ofFn fun i => some
          (⟨x.get vs.length i, tau.get vs.length i,
            get_mem_type_of_isTuple
              (hasArity_of_mem_toZFSet tau_hasArity hx)
              tau_hasArity hx⟩ : B.Dom))))
    (bound_expected : ∀ i : Fin vs.length,
      GammaP.lookup vs[i] = some
        ((rho.fromProdl (vs.length - 1))[i.val]'(by
          have hlen := rho_supported.fromProdl_length_of_hasArity
            tau_hasArity
          exact i.isLt.trans_eq hlen.symm)))
    (source_respects : ∀ (ss : Fin vs.length → SMT.Dom),
      (∀ i, GammaP.lookup vs[i] = some (ss i).snd.fst) →
      B.RenamingContext.RespectsTypeContextOnFV
        (Function.updates ThetaD vs
          ((List.ofFn ss).map Option.some)) GammaP P)
    (target_respects : ∀ (ss : Fin vs.length → SMT.Dom),
      (∀ i, GammaP.lookup vs[i] = some (ss i).snd.fst) →
      SMT.RenamingContext.RespectsTypeContextOnFV
        (Function.updates ThetaD vs
          ((List.ofFn ss).map Option.some)) GammaP Penc)
    (specs_true : ∀ (ss : Fin vs.length → SMT.Dom),
      (∀ i, GammaP.lookup vs[i] = some (ss i).snd.fst) →
      SpecBodiesTrue
        (Function.updates ThetaD vs
          ((List.ofFn ss).map Option.some)) GammaP DltP)
    (z_not_fv_Penc : z ∉ SMT.fv Penc) :
    ∃ lamVal : SMT.Dom.{u},
      ⟦((λˢ [z]) [rho] ite_body).abstract ThetaD hcov_lambda⟧ˢ =
        some lamVal ∧
      RDomCastSupported (⟨T, BType.set tau, hT⟩ : B.Dom) lamVal := by
  rcases DencVal with ⟨F, sigmaD, hF⟩
  dsimp at hDenc_type hDenc_func den_D_upd D_rel
  subst sigmaD
  obtain ⟨lamVal, hlamVal, hlamVal_type⟩ :=
    SMT.RenamingContext.denote_exists_of_typing_fv typ_lambda
      respects_lambda hcov_lambda
  have hTsub : T ⊆ ⟦tau⟧ᶻ := by
    rwa [BType.toZFSet, ZFSet.mem_powerset] at hT
  obtain ⟨hbody_total, _hbody_type⟩ :=
    SMT.RenamingContext.denote_update_total_and_type_of_typing
      typ_ite Theta_wt hcov_ite_upd
  refine ⟨lamVal, hlamVal, ?_⟩
  apply represented_setPred_lambda_of_pointwise rho_supported hTsub
    hcov_lambda hlamVal hlamVal_type
  · intro y hy
    let W : SMT.Dom := ⟨y, rho, hy⟩
    obtain ⟨bodyVal, hden_body⟩ :=
      Option.isSome_iff_exists.mp (hbody_total W rfl)
    exact ⟨hcov_ite_upd W, bodyVal, hden_body⟩
  · intro y hy hcov_body bodyVal hden_body hbody_true
    let W : SMT.Dom := ⟨y, rho, hy⟩
    have hden_body' :
        ⟦ite_body.abstract (Function.update ThetaD z (some W))
          (hcov_ite_upd W)⟧ˢ = some bodyVal := by
      rw [SMT.RenamingContext.denote_abstract_proof_irrel ite_body
        (Function.update ThetaD z (some W)) hcov_body (hcov_ite_upd W)]
      exact hden_body
    obtain ⟨hcov_Dapp, Dapp, hDapp_type, hDapp_value, hden_Dapp⟩ :=
      funDenoteAppAt (Δctx := ThetaD) (t := Denc) (x := z)
        (α := rho) (β := SMTType.bool)
        (Y := (⟨F, rho.fun SMTType.bool, hF⟩ : SMT.Dom))
        hcov_D_upd den_D_upd rfl hDenc_func W rfl hy
    have hDapp_true : Dapp.fst = ZFSet.zftrue :=
      collect_ite_true_implies_domain_true ite_body_def
        (hcov_ite_upd W) hcov_Dapp hden_Dapp hden_body'
        hDapp_type hbody_true
    have hF_true :
        (ZFSet.fapply F (ZFSet.is_func_is_pfunc hDenc_func)
          ⟨y, by rw [ZFSet.is_func_dom_eq hDenc_func]; exact hy⟩).val =
          ZFSet.zftrue := by
      exact hDapp_value.symm.trans hDapp_true
    obtain ⟨x, hx_D, X_rel⟩ :=
      D_rel.setPred_target_of_true hy hF_true
    have hx_mem : x ∈ ⟦tau⟧ᶻ := by
      have hDsub : Dval ⊆ ⟦tau⟧ᶻ := by
        rwa [BType.toZFSet, ZFSet.mem_powerset] at hDval
      exact hDsub hx_D
    have X_rel' : RDomCastSupported
        (⟨x, tau, hx_mem⟩ : B.Dom) (⟨y, rho, hy⟩ : SMT.Dom) := by
      simpa only [proof_irrel_heq] using X_rel
    obtain ⟨Pval, hPval, den_P, htruth⟩ :=
      represented_collect_pointwise_body_bridge_supported
        (D := D) (P := P) (tau := tau) (rho := rho)
        (Xi := Xi) (Dval := Dval) (T := T) (Denc := Denc)
        (Penc := Penc) (ite_body := ite_body) (z := z)
        (ThetaD := ThetaD)
        (DencVal := (⟨F, rho.fun SMTType.bool, hF⟩ : SMT.Dom))
        (Ebody := Ebody) (LambdaP := LambdaP) (GammaP := GammaP)
        (DltP := DltP) (sigmaP := sigmaP)
        vs_nemp vs_nodup rho_supported Xi_fv tau_hasArity den_D
        den_collect hcov_D_upd den_D_upd rfl hDenc_func D_rel
        ite_body_def hcov_ite_upd hcov_sub_upd hcov_P_upd hvs_not_bv
        hz_not_bv hz_not_vs typ_P P_guard P_scope typ_Penc ambient
        wf_bound bound_expected source_respects target_respects specs_true
        z_not_fv_Penc x hx_mem hx_D y hy X_rel' bodyVal hden_body'
    have hx_arity : x.hasArity vs.length :=
      hasArity_of_mem_toZFSet tau_hasArity hx_mem
    have hx_T : x ∈ T :=
      (B.denote_collect_member_iff Xi_fv tau_hasArity den_D den_collect
        hx_arity hx_mem den_P).mpr ⟨hx_D, htruth.mp hbody_true⟩
    exact ⟨x, hx_T, by simpa only [proof_irrel_heq] using X_rel'⟩
  · intro x hx_T
    have hx_mem : x ∈ ⟦tau⟧ᶻ := hTsub hx_T
    have hx_D : x ∈ Dval :=
      B.denote_collect_mem_domain Xi_fv tau_hasArity den_D den_collect hx_T
    obtain ⟨y, hy, X_rel⟩ := D_rel.setPred_member_preimage hx_D
    have X_rel' : RDomCastSupported
        (⟨x, tau, hx_mem⟩ : B.Dom) (⟨y, rho, hy⟩ : SMT.Dom) := by
      simpa only [proof_irrel_heq] using X_rel
    let W : SMT.Dom := ⟨y, rho, hy⟩
    obtain ⟨bodyVal, hden_body⟩ :=
      Option.isSome_iff_exists.mp (hbody_total W rfl)
    obtain ⟨Pval, hPval, den_P, htruth⟩ :=
      represented_collect_pointwise_body_bridge_supported
        (D := D) (P := P) (tau := tau) (rho := rho)
        (Xi := Xi) (Dval := Dval) (T := T) (Denc := Denc)
        (Penc := Penc) (ite_body := ite_body) (z := z)
        (ThetaD := ThetaD)
        (DencVal := (⟨F, rho.fun SMTType.bool, hF⟩ : SMT.Dom))
        (Ebody := Ebody) (LambdaP := LambdaP) (GammaP := GammaP)
        (DltP := DltP) (sigmaP := sigmaP)
        vs_nemp vs_nodup rho_supported Xi_fv tau_hasArity den_D
        den_collect hcov_D_upd den_D_upd rfl hDenc_func D_rel
        ite_body_def hcov_ite_upd hcov_sub_upd hcov_P_upd hvs_not_bv
        hz_not_bv hz_not_vs typ_P P_guard P_scope typ_Penc ambient
        wf_bound bound_expected source_respects target_respects specs_true
        z_not_fv_Penc x hx_mem hx_D y hy X_rel' bodyVal hden_body
    have hx_arity : x.hasArity vs.length :=
      hasArity_of_mem_toZFSet tau_hasArity hx_mem
    have hP_true : Pval = ZFSet.zftrue :=
      (B.denote_collect_member_iff Xi_fv tau_hasArity den_D den_collect
        hx_arity hx_mem den_P).mp hx_T |>.2
    exact ⟨y, hy, by simpa only [proof_irrel_heq] using X_rel',
      hcov_ite_upd W, bodyVal, hden_body, htruth.mpr hP_true⟩
