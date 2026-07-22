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

/-! ## Supported option-function collection semantics -/

open Classical in
/-- Eliminating an option term known to contain a supported payload preserves
that payload representation, without requiring a canonical codomain. -/
theorem represented_option_payload_of_some_supported.{u}
    {beta : BType} {rho : SMTType}
    {b : ZFSet.{u}} {hb : b ∈ ⟦beta⟧ᶻ}
    {Dapp : SMT.Term} {Theta : SMT.RenamingContext.Context.{u}}
    {DappVal Wb : SMT.Dom.{u}}
    (hcov_Dapp : SMT.RenamingContext.CoversFV Theta Dapp)
    (hden_Dapp : ⟦Dapp.abstract Theta hcov_Dapp⟧ˢ = some DappVal)
    (hDapp_type : DappVal.snd.fst = SMTType.option rho)
    (hWb_type : Wb.snd.fst = rho)
    (Wb_rel : RDomCastSupported (⟨b, beta, hb⟩ : B.Dom) Wb)
    (hDapp_value : DappVal.fst = (ZFSet.Option.some
      (S := ⟦rho⟧ᶻ) ⟨Wb.fst,
        by rw [← hWb_type]; exact Wb.snd.snd⟩).val) :
    ∃ (hcov_the : SMT.RenamingContext.CoversFV Theta (SMT.Term.the Dapp))
      (Dthe : SMT.Dom.{u}),
      ⟦(SMT.Term.the Dapp).abstract Theta hcov_the⟧ˢ = some Dthe ∧
      Dthe.snd.fst = rho ∧
      RDomCastSupported (⟨b, beta, hb⟩ : B.Dom) Dthe := by
  obtain ⟨hcov_the, Dthe, hden_the, hDthe_type, hDthe_value⟩ :=
    denote_the_of_some hcov_Dapp hden_Dapp hDapp_type hWb_type hDapp_value
  have hDthe_eq : Dthe = Wb :=
    SMT.RenamingContext.Dom_ext' hDthe_value
      (hDthe_type.trans hWb_type.symm)
  refine ⟨hcov_the, Dthe, hden_the, hDthe_type, ?_⟩
  rw [hDthe_eq]
  exact Wb_rel

open Classical in
/-- The split tuple used by a function-valued collection represents every
source binder component at the actual supported endpoint representations. -/
theorem represented_option_collect_components_supported.{u}
    {vs : List B.𝒱} (prefix_nemp : vs.dropLast ≠ [])
    {alpha beta : BType} {sigma rho : SMTType}
    (hsigma : BType.SupportedSMT alpha sigma)
    (_hrho : BType.SupportedSMT beta rho)
    {a b : ZFSet.{u}}
    (ha : a ∈ ⟦alpha⟧ᶻ) (hb : b ∈ ⟦beta⟧ᶻ)
    (hvs : 2 ≤ vs.length)
    (hprod_arity : (alpha ×ᴮ beta).hasArity vs.length)
    {z : SMT.𝒱} {Theta : SMT.RenamingContext.Context.{u}}
    {Wa : SMT.Dom.{u}}
    (hcov_z : SMT.RenamingContext.CoversFV Theta (.var z))
    (hden_z : ⟦(SMT.Term.var z).abstract Theta hcov_z⟧ˢ = some Wa)
    (hWa_type : Wa.snd.fst = sigma)
    (hWa_mem : Wa.fst ∈ ⟦sigma⟧ᶻ)
    (Wa_rel : RDomCastSupported (⟨a, alpha, ha⟩ : B.Dom) Wa)
    {Dapp : SMT.Term}
    (hpayload : ∃ hcov_payload : SMT.RenamingContext.CoversFV Theta
        (SMT.Term.the Dapp),
      ∃ Dpayload : SMT.Dom.{u},
        ⟦(SMT.Term.the Dapp).abstract Theta hcov_payload⟧ˢ = some Dpayload ∧
        Dpayload.snd.fst = rho ∧
        RDomCastSupported (⟨b, beta, hb⟩ : B.Dom) Dpayload) :
    let terms : List SMT.Term :=
      toDestPair vs.dropLast (.var z) [(.the Dapp)] (.var z)
    let targetTypes := (sigma.fromProdl (vs.length - 2)).concat rho
    let x_fin : Fin vs.length → B.Dom.{u} := fun i =>
      ⟨(a.pair b).get vs.length i,
        (alpha ×ᴮ beta).get vs.length i,
        get_mem_type_of_isTuple
          (hasArity_of_mem_toZFSet hprod_arity
            (ZFSet.pair_mem_prod.mpr ⟨ha, hb⟩))
          hprod_arity (ZFSet.pair_mem_prod.mpr ⟨ha, hb⟩)⟩
    ∃ ss : Fin vs.length → SMT.Dom.{u},
      ∀ i,
        ∃ hcov : SMT.RenamingContext.CoversFV Theta
            (terms[i.val]'(by
              rw [toDestPair_length_gen vs.dropLast (.var z) (.var z)
                [(.the Dapp)] prefix_nemp]
              rw [List.length_dropLast]
              simp only [List.length_singleton]
              omega)),
          ⟦(terms[i.val]'(by
              rw [toDestPair_length_gen vs.dropLast (.var z) (.var z)
                [(.the Dapp)] prefix_nemp]
              rw [List.length_dropLast]
              simp only [List.length_singleton]
              omega)).abstract Theta hcov⟧ˢ = some (ss i) ∧
          RDomCastSupported (x_fin i) (ss i) ∧
          (ss i).snd.fst = targetTypes[i.val]'(by
            have hprefix_arity : alpha.hasArity vs.dropLast.length :=
              BType.prod_left_hasArity_dropLast hvs hprod_arity
            have hdrop : vs.dropLast.length - 1 = vs.length - 2 := by
              rw [List.length_dropLast]
              omega
            have hlen := hsigma.fromProdl_length_of_hasArity hprefix_arity
            dsimp only [targetTypes, List.concat_eq_append]
            rw [List.length_concat, ← hdrop, hlen, List.length_dropLast]
            omega) := by
  dsimp only
  let terms : List SMT.Term :=
    toDestPair vs.dropLast (.var z) [(.the Dapp)] (.var z)
  let targetTypes := (sigma.fromProdl (vs.length - 2)).concat rho
  let x_fin : Fin vs.length → B.Dom.{u} := fun i =>
    ⟨(a.pair b).get vs.length i,
      (alpha ×ᴮ beta).get vs.length i,
      get_mem_type_of_isTuple
        (hasArity_of_mem_toZFSet hprod_arity
          (ZFSet.pair_mem_prod.mpr ⟨ha, hb⟩))
        hprod_arity (ZFSet.pair_mem_prod.mpr ⟨ha, hb⟩)⟩
  have hterms_len : terms.length = vs.length := by
    dsimp [terms]
    rw [toDestPair_length_gen vs.dropLast (.var z) (.var z)
      [(.the Dapp)] prefix_nemp]
    rw [List.length_dropLast]
    simp only [List.length_singleton]
    omega
  obtain ⟨hcov_payload, Dpayload, hden_payload, hpayload_type,
    hrel_payload⟩ := hpayload
  have hprefix_arity : alpha.hasArity vs.dropLast.length :=
    BType.prod_left_hasArity_dropLast hvs hprod_arity
  have hdrop : vs.dropLast.length - 1 = vs.length - 2 := by
    rw [List.length_dropLast]
    omega
  have hprefix_types_len :
      (sigma.fromProdl (vs.length - 2)).length = vs.dropLast.length := by
    rw [← hdrop]
    exact hsigma.fromProdl_length_of_hasArity hprefix_arity
  have htarget_len : targetTypes.length = vs.length := by
    dsimp [targetTypes]
    simp only [List.length_concat, hprefix_types_len]
    rw [List.length_dropLast]
    omega
  have hcomponent : ∀ i : Fin vs.length,
      ∃ hcov : SMT.RenamingContext.CoversFV Theta
          (terms[i.val]'(by rw [hterms_len]; exact i.isLt)),
        ∃ Di : SMT.Dom.{u},
          ⟦(terms[i.val]'(by rw [hterms_len]; exact i.isLt)).abstract
            Theta hcov⟧ˢ = some Di ∧
          RDomCastSupported (x_fin i) Di ∧
          Di.snd.fst = targetTypes[i.val]'(by rw [htarget_len]; exact i.isLt) := by
    intro i
    by_cases hi_prefix : i.val < vs.dropLast.length
    · obtain ⟨hcov, Di, hden, hrel, hDi_type⟩ :=
        toDestPair_denote_supported_components alpha sigma hsigma
          vs.dropLast a ha (.var z) Wa Theta [(.the Dapp)] [Dpayload]
          prefix_nemp hprefix_arity hcov_z hden_z hWa_type hWa_mem Wa_rel
          (by simp)
          (by
            intro j hj
            have hj_zero : j = 0 := by
              simp only [List.length_singleton] at hj
              omega
            subst j
            refine ⟨?_, ?_⟩
            · simpa only [List.getElem_cons_zero] using hcov_payload
            · exact Option.isSome_iff_exists.mpr ⟨Dpayload, by
                simpa only [List.getElem_cons_zero, proof_irrel_heq] using
                  hden_payload⟩)
          i.val hi_prefix (by rw [hterms_len]; exact i.isLt)
      have hi_types : i.val < (sigma.fromProdl (vs.length - 2)).length := by
        rw [hprefix_types_len]
        exact hi_prefix
      have htarget_get :
          targetTypes[i.val]'(by rw [htarget_len]; exact i.isLt) =
            (sigma.fromProdl (vs.length - 2))[i.val]'hi_types := by
        dsimp [targetTypes]
        simpa only [List.concat_eq_append, proof_irrel_heq] using
          (List.getElem_append_left (bs := [rho]) hi_types)
      refine ⟨?_, Di, ?_, ?_, ?_⟩
      · simpa [terms, proof_irrel_heq] using hcov
      · simpa [terms, proof_irrel_heq] using hden
      · simpa [x_fin] using
          (represented_option_prefix_as_pair_component ha hb hvs hprod_arity
            i.val hi_prefix hrel)
      · rw [htarget_get]
        simpa only [hdrop, proof_irrel_heq] using hDi_type
    · have hi_value : i.val = vs.dropLast.length := by
        have hi_ge : vs.dropLast.length ≤ i.val := Nat.le_of_not_gt hi_prefix
        have hi_lt : i.val < vs.length := i.isLt
        rw [List.length_dropLast] at hi_ge ⊢
        omega
      have hprefix_pos : 0 < vs.dropLast.length := by
        rw [List.length_dropLast]
        omega
      have hlen_last : vs.dropLast.length + 1 = vs.length := by
        rw [List.length_dropLast]
        omega
      let ilast : Fin vs.length :=
        Fin.cast hlen_last (Fin.last vs.dropLast.length)
      have hi_eq : i = ilast := by
        apply Fin.ext
        simpa [ilast, Fin.val_last] using hi_value
      subst i
      have hindex_last : vs.dropLast.length < terms.length := by
        rw [hterms_len, List.length_dropLast]
        omega
      have hterm_last :
          terms[vs.dropLast.length]'hindex_last = SMT.Term.the Dapp := by
        dsimp [terms]
        simpa only [Nat.add_zero] using
          (toDestPair_getElem_acc vs.dropLast (.var z) (.var z)
            [(.the Dapp)] 0 (by simp) prefix_nemp hindex_last)
      have hvalue_last : (a.pair b).get vs.length ilast = b := by
        change (a.pair b).get vs.length
          (Fin.cast hlen_last (Fin.last vs.dropLast.length)) = b
        calc
          _ = (a.pair b).get (vs.dropLast.length + 1)
                (Fin.last vs.dropLast.length) :=
            (ZFSet_get_cast hlen_last (Fin.last vs.dropLast.length)).symm
          _ = b := ZFSet_get_pair_last hprefix_pos
      have htype_last : (alpha ×ᴮ beta).get vs.length ilast = beta := by
        change (alpha ×ᴮ beta).get vs.length
          (Fin.cast hlen_last (Fin.last vs.dropLast.length)) = beta
        calc
          _ = (alpha ×ᴮ beta).get (vs.dropLast.length + 1)
                (Fin.last vs.dropLast.length) :=
            (BType.get_cast hlen_last (Fin.last vs.dropLast.length)).symm
          _ = beta := BType_get_pair_last hprefix_pos
      have hsource_last : x_fin ilast = (⟨b, beta, hb⟩ : B.Dom) := by
        dsimp [x_fin]
        exact B.Dom.ext_type_value htype_last hvalue_last
      let tlast : SMT.Term :=
        terms[ilast.val]'(by rw [hterms_len]; exact ilast.isLt)
      have htlast : tlast = SMT.Term.the Dapp := by
        dsimp [tlast]
        simpa only [ilast, Fin.val_cast, Fin.val_last, proof_irrel_heq] using
          hterm_last
      have hcov_last : SMT.RenamingContext.CoversFV Theta tlast := by
        rw [htlast]
        exact hcov_payload
      have hden_last : ⟦tlast.abstract Theta hcov_last⟧ˢ = some Dpayload := by
        simpa only [htlast, proof_irrel_heq] using hden_payload
      have htarget_last :
          targetTypes[ilast.val]'(by rw [htarget_len]; exact ilast.isLt) = rho := by
        have hlast_eq : ilast.val =
            (sigma.fromProdl (vs.length - 2)).length :=
          hi_value.trans hprefix_types_len.symm
        have hindex_append : ilast.val <
            ((sigma.fromProdl (vs.length - 2)) ++ [rho]).length := by
          simp only [List.length_append, List.length_singleton,
            hprefix_types_len]
          omega
        simpa only [targetTypes, List.concat_eq_append, proof_irrel_heq] using
          (List.getElem_concat_length (l := sigma.fromProdl (vs.length - 2))
            (a := rho) hlast_eq hindex_append)
      refine ⟨?_, Dpayload, ?_, ?_, ?_⟩
      · simpa only [tlast, proof_irrel_heq] using hcov_last
      · simpa only [tlast, proof_irrel_heq] using hden_last
      · rw [hsource_last]
        exact hrel_payload
      · exact hpayload_type.trans htarget_last.symm
  let ss : Fin vs.length → SMT.Dom.{u} := fun i =>
    Classical.choose (Classical.choose_spec (hcomponent i))
  refine ⟨ss, ?_⟩
  intro i
  let hcov := Classical.choose (hcomponent i)
  let Di := Classical.choose (Classical.choose_spec (hcomponent i))
  obtain ⟨hden, hrel, htype⟩ :=
    Classical.choose_spec (Classical.choose_spec (hcomponent i))
  refine ⟨hcov, ?_, ?_, ?_⟩
  · simpa [terms, ss, Di, hcov, proof_irrel_heq] using hden
  · simpa [x_fin, ss, Di, proof_irrel_heq] using hrel
  · simpa [targetTypes, ss, Di, proof_irrel_heq] using htype

open Classical in
/-- Transfer guarded predicate truth through the split option tuple at
arbitrary supported endpoint representations. -/
theorem represented_option_collect_subst_truth_of_some_guarded_supported.{u}
    {Penc Dapp : SMT.Term}
    {vs : List B.𝒱} (prefix_nemp : vs.dropLast ≠ [])
    (vs_nodup : vs.Nodup)
    {alpha beta : BType} {sigma rho : SMTType}
    (hsigma : BType.SupportedSMT alpha sigma)
    (hrho : BType.SupportedSMT beta rho)
    {a b : ZFSet.{u}}
    (ha : a ∈ ⟦alpha⟧ᶻ) (hb : b ∈ ⟦beta⟧ᶻ)
    (hvs : 2 ≤ vs.length)
    (hprod_arity : (alpha ×ᴮ beta).hasArity vs.length)
    {x_fin : Fin vs.length → B.Dom.{u}}
    (hx_fin : ∀ i, x_fin i =
      (⟨(a.pair b).get vs.length i,
        (alpha ×ᴮ beta).get vs.length i,
        get_mem_type_of_isTuple
          (hasArity_of_mem_toZFSet hprod_arity
            (ZFSet.pair_mem_prod.mpr ⟨ha, hb⟩))
          hprod_arity (ZFSet.pair_mem_prod.mpr ⟨ha, hb⟩)⟩ : B.Dom))
    {z : SMT.𝒱} {Theta : SMT.RenamingContext.Context.{u}}
    {Wa : SMT.Dom.{u}}
    (hcov_z : SMT.RenamingContext.CoversFV
      (Function.update Theta z (some Wa)) (.var z))
    (hden_z : ⟦(SMT.Term.var z).abstract
      (Function.update Theta z (some Wa)) hcov_z⟧ˢ = some Wa)
    (hWa_type : Wa.snd.fst = sigma)
    (hWa_mem : Wa.fst ∈ ⟦sigma⟧ᶻ)
    (Wa_rel : RDomCastSupported (⟨a, alpha, ha⟩ : B.Dom) Wa)
    {DappVal Wb : SMT.Dom.{u}}
    (hcov_Dapp : SMT.RenamingContext.CoversFV
      (Function.update Theta z (some Wa)) Dapp)
    (hden_Dapp : ⟦Dapp.abstract
      (Function.update Theta z (some Wa)) hcov_Dapp⟧ˢ = some DappVal)
    (hDapp_type : DappVal.snd.fst = SMTType.option rho)
    (hWb_type : Wb.snd.fst = rho)
    (Wb_rel : RDomCastSupported (⟨b, beta, hb⟩ : B.Dom) Wb)
    (hDapp_value : DappVal.fst = (ZFSet.Option.some
      (S := ⟦rho⟧ᶻ) ⟨Wb.fst,
        by rw [← hWb_type]; exact Wb.snd.snd⟩).val)
    (hDapp_fv_not_bv : ∀ w ∈ SMT.fv Dapp, w ∉ SMT.bv Penc)
    (hDapp_fv_disj_vs : ∀ w ∈ SMT.fv Dapp, w ∉ vs)
    (hvs_not_bv : ∀ v ∈ vs, v ∉ SMT.bv Penc)
    (hz_not_bv : z ∉ SMT.bv Penc) (hz_not_vs : z ∉ vs)
    (hcov_sub : SMT.RenamingContext.CoversFV
      (Function.update Theta z (some Wa))
      (SMT.substList vs
        ((toDestPair vs.dropLast (.var z)).concat (.the Dapp)) Penc))
    (hcov_upd : ∀ ss : Fin vs.length → SMT.Dom.{u},
      SMT.RenamingContext.CoversFV
        (Function.updates (Function.update Theta z (some Wa)) vs
          ((List.ofFn ss).map Option.some)) Penc)
    {Pterm : B.Term} {E : B.Env} {Lambda Gamma : SMT.TypeContext}
    {Dlt : SMT.Chunk} {sigmaP : SMTType}
    (P_guard : EncodeTermRepGuardedSound.{u}
      Pterm E BType.bool Penc sigmaP Lambda Dlt)
    (P_scope : ScopedContextExtends Lambda Dlt Gamma)
    (typ_Penc : Gamma ⊢ˢ Penc : sigmaP)
    {Xi : B.RenamingContext.Context.{u}}
    (Xi_fv : ∀ v ∈ B.fv Pterm,
      (Function.updates Xi vs
        (List.ofFn fun i => some (x_fin i)) v).isSome = true)
    (ambient : ∀ v ∈ B.fv Pterm, v ∉ vs →
      match Xi v, Theta v with
      | some d, some d' => RDomCastSupported d d'
      | _, _ => False)
    (wf : B.RenWF E.context
      (Function.updates Xi vs (List.ofFn fun i => some (x_fin i))))
    (bound_expected : ∀ i : Fin vs.length,
      Gamma.lookup vs[i] = some
        (((sigma.fromProdl (vs.length - 2)).concat rho)[i.val]'(by
          have hprefix_arity : alpha.hasArity vs.dropLast.length :=
            BType.prod_left_hasArity_dropLast hvs hprod_arity
          have hdrop : vs.dropLast.length - 1 = vs.length - 2 := by
            rw [List.length_dropLast]
            omega
          have hlen := hsigma.fromProdl_length_of_hasArity hprefix_arity
          rw [List.length_concat, ← hdrop, hlen, List.length_dropLast]
          omega)))
    (source_respects : ∀ ss : Fin vs.length → SMT.Dom.{u},
      (∀ i, Gamma.lookup vs[i] = some (ss i).snd.fst) →
      B.RenamingContext.RespectsTypeContextOnFV
        (Function.updates Theta vs
          ((List.ofFn ss).map Option.some)) Gamma Pterm)
    (target_respects : ∀ ss : Fin vs.length → SMT.Dom.{u},
      (∀ i, Gamma.lookup vs[i] = some (ss i).snd.fst) →
      SMT.RenamingContext.RespectsTypeContextOnFV
        (Function.updates Theta vs
          ((List.ofFn ss).map Option.some)) Gamma Penc)
    (specs_true : ∀ ss : Fin vs.length → SMT.Dom.{u},
      (∀ i, Gamma.lookup vs[i] = some (ss i).snd.fst) →
      SpecBodiesTrue
        (Function.updates Theta vs
          ((List.ofFn ss).map Option.some)) Gamma Dlt)
    {Pval : ZFSet.{u}} {hPval : Pval ∈ ⟦BType.bool⟧ᶻ}
    (den_P : ⟦Pterm.abstract
      (Function.updates Xi vs (List.ofFn fun i => some (x_fin i)))
      Xi_fv⟧ᴮ = some (⟨Pval, BType.bool, hPval⟩ : B.Dom))
    (z_not_fv_Penc : z ∉ SMT.fv Penc) :
    ∃ dP : SMT.Dom.{u},
      ⟦(SMT.substList vs
        ((toDestPair vs.dropLast (.var z)).concat (.the Dapp)) Penc).abstract
        (Function.update Theta z (some Wa)) hcov_sub⟧ˢ = some dP ∧
      dP.snd.fst = sigmaP ∧
      (dP.fst = ZFSet.zftrue ↔ Pval = ZFSet.zftrue) := by
  obtain ⟨hcov_payload, Dpayload, hden_payload, hpayload_type,
    hrel_payload⟩ :=
    represented_option_payload_of_some_supported hcov_Dapp hden_Dapp
      hDapp_type hWb_type Wb_rel hDapp_value
  obtain ⟨ss, hcomponents⟩ :=
    represented_option_collect_components_supported prefix_nemp hsigma hrho
      ha hb hvs hprod_arity hcov_z hden_z hWa_type hWa_mem Wa_rel
      ⟨hcov_payload, Dpayload, hden_payload, hpayload_type, hrel_payload⟩
  have hss_type : ∀ i : Fin vs.length,
      Gamma.lookup vs[i] = some (ss i).snd.fst := by
    intro i
    obtain ⟨_, _, hrest⟩ := hcomponents i
    obtain ⟨_, htype⟩ := hrest
    exact (bound_expected i).trans (congrArg some htype).symm
  have hcomponents' : ∀ i : Fin vs.length,
      ∃ hcov : SMT.RenamingContext.CoversFV
          (Function.update Theta z (some Wa))
          (((toDestPair vs.dropLast (.var z)).concat (.the Dapp))[i.val]'(by
            rw [toDestPair_optionTuple_length prefix_nemp]
            exact i.isLt)),
        ⟦(((toDestPair vs.dropLast (.var z)).concat (.the Dapp))[i.val]'(by
          rw [toDestPair_optionTuple_length prefix_nemp]
          exact i.isLt)).abstract (Function.update Theta z (some Wa))
            hcov⟧ˢ = some (ss i) := by
    intro i
    obtain ⟨hcov, hden, _⟩ := hcomponents i
    refine ⟨?_, ?_⟩
    · simpa only [toDestPair_concat, proof_irrel_heq] using hcov
    · simpa only [toDestPair_concat, proof_irrel_heq] using hden
  have hss_map : (List.ofFn ss).map Option.some =
      List.ofFn (fun i => some (ss i)) := by
    rw [List.map_ofFn]
    rfl
  have hrelated : RValuationCastSupportedOnFV
      (Function.updates Xi vs (List.ofFn fun i => some (x_fin i)))
      (Function.updates Theta vs
        ((List.ofFn ss).map Option.some)) Pterm := by
    rw [hss_map]
    apply RValuationCastSupportedOnFV.updates vs_nodup
    · exact ambient
    · intro i
      obtain ⟨_, _, hrest⟩ := hcomponents i
      obtain ⟨hrel, _⟩ := hrest
      rw [hx_fin i]
      exact hrel
  exact collect_subst_truth_of_guarded_body_optionTuple
    (Penc := Penc) (Dapp := Dapp) prefix_nemp vs_nodup
    (z := z) (DeltaCtx := Theta) (W := Wa) (ss := ss)
    hDapp_fv_not_bv hDapp_fv_disj_vs hvs_not_bv hz_not_bv hz_not_vs
    hcomponents' hcov_sub (hcov_upd ss) P_guard P_scope typ_Penc Xi_fv
    hrelated wf (source_respects ss hss_type) (target_respects ss hss_type)
    (specs_true ss hss_type) den_P z_not_fv_Penc

open Classical in
/-- Prepare the source and SMT predicate denotations for one represented
option-function graph point. -/
theorem represented_option_collect_predicate_setup_guarded_supported.{u}
    {vs : List B.𝒱} (vs_nemp : vs ≠ []) (prefix_nemp : vs.dropLast ≠ [])
    (vs_nodup : vs.Nodup)
    {D P : B.Term} {alpha beta : BType} {sigma rho : SMTType}
    (hsigma : BType.SupportedSMT alpha sigma)
    (hrho : BType.SupportedSMT beta rho)
    {Xi : B.RenamingContext.Context.{u}}
    (Xi_fv : ∀ v ∈ B.fv (B.Term.collect vs D P), (Xi v).isSome = true)
    (hprod_arity : (alpha ×ᴮ beta).hasArity vs.length)
    {Dval : ZFSet.{u}} {hDval : Dval ∈ ⟦BType.set (alpha ×ᴮ beta)⟧ᶻ}
    (den_D : ⟦D.abstract Xi
      (fun v hv => Xi_fv v (B.fv.mem_collect (.inl hv)))⟧ᴮ =
      some (⟨Dval, BType.set (alpha ×ᴮ beta), hDval⟩ : B.Dom))
    {T : ZFSet.{u}} {hT : T ∈ ⟦BType.set (alpha ×ᴮ beta)⟧ᶻ}
    (den_collect : ⟦(B.Term.collect vs D P).abstract Xi Xi_fv⟧ᴮ =
      some (⟨T, BType.set (alpha ×ᴮ beta), hT⟩ : B.Dom))
    {a b : ZFSet.{u}} (ha : a ∈ ⟦alpha⟧ᶻ) (hb : b ∈ ⟦beta⟧ᶻ)
    (hvs : 2 ≤ vs.length)
    {x_fin : Fin vs.length → B.Dom.{u}}
    (hx_fin : ∀ i, x_fin i =
      (⟨(a.pair b).get vs.length i,
        (alpha ×ᴮ beta).get vs.length i,
        get_mem_type_of_isTuple
          (hasArity_of_mem_toZFSet hprod_arity
            (ZFSet.pair_mem_prod.mpr ⟨ha, hb⟩))
          hprod_arity (ZFSet.pair_mem_prod.mpr ⟨ha, hb⟩)⟩ : B.Dom))
    (hmem_D : a.pair b ∈ Dval)
    {Penc Dapp : SMT.Term} {z : SMT.𝒱}
    {Theta : SMT.RenamingContext.Context.{u}} {Wa : SMT.Dom.{u}}
    (hcov_z : SMT.RenamingContext.CoversFV
      (Function.update Theta z (some Wa)) (.var z))
    (hden_z : ⟦(SMT.Term.var z).abstract
      (Function.update Theta z (some Wa)) hcov_z⟧ˢ = some Wa)
    (hWa_type : Wa.snd.fst = sigma)
    (hWa_mem : Wa.fst ∈ ⟦sigma⟧ᶻ)
    (Wa_rel : RDomCastSupported (⟨a, alpha, ha⟩ : B.Dom) Wa)
    {DappVal Wb : SMT.Dom.{u}}
    (hcov_Dapp : SMT.RenamingContext.CoversFV
      (Function.update Theta z (some Wa)) Dapp)
    (hden_Dapp : ⟦Dapp.abstract
      (Function.update Theta z (some Wa)) hcov_Dapp⟧ˢ = some DappVal)
    (hDapp_type : DappVal.snd.fst = SMTType.option rho)
    (hWb_type : Wb.snd.fst = rho)
    (Wb_rel : RDomCastSupported (⟨b, beta, hb⟩ : B.Dom) Wb)
    (hDapp_value : DappVal.fst = (ZFSet.Option.some
      (S := ⟦rho⟧ᶻ) ⟨Wb.fst,
        by rw [← hWb_type]; exact Wb.snd.snd⟩).val)
    (hDapp_fv_not_bv : ∀ w ∈ SMT.fv Dapp, w ∉ SMT.bv Penc)
    (hDapp_fv_disj_vs : ∀ w ∈ SMT.fv Dapp, w ∉ vs)
    (hvs_not_bv : ∀ v ∈ vs, v ∉ SMT.bv Penc)
    (hz_not_bv : z ∉ SMT.bv Penc) (hz_not_vs : z ∉ vs)
    (hcov_sub : SMT.RenamingContext.CoversFV
      (Function.update Theta z (some Wa))
      (SMT.substList vs
        ((toDestPair vs.dropLast (.var z)).concat (.the Dapp)) Penc))
    (hcov_upd : ∀ ss : Fin vs.length → SMT.Dom.{u},
      SMT.RenamingContext.CoversFV
        (Function.updates (Function.update Theta z (some Wa)) vs
          ((List.ofFn ss).map Option.some)) Penc)
    {Ebody : B.Env} {LambdaP GammaP : SMT.TypeContext}
    {DltP : SMT.Chunk} {sigmaP : SMTType}
    (typ_P : Ebody.context ⊢ᴮ P : BType.bool)
    (P_guard : EncodeTermRepGuardedSound.{u}
      P Ebody BType.bool Penc sigmaP LambdaP DltP)
    (P_scope : ScopedContextExtends LambdaP DltP GammaP)
    (typ_Penc : GammaP ⊢ˢ Penc : sigmaP)
    (hP_sigma : sigmaP = SMTType.bool)
    (ambient : ∀ v ∈ B.fv P, v ∉ vs →
      match Xi v, Theta v with
      | some d, some d' => RDomCastSupported d d'
      | _, _ => False)
    (wf : B.RenWF Ebody.context
      (Function.updates Xi vs (List.ofFn fun i => some (x_fin i))))
    (bound_expected : ∀ i : Fin vs.length,
      GammaP.lookup vs[i] = some
        (((sigma.fromProdl (vs.length - 2)).concat rho)[i.val]'(by
          have hprefix_arity : alpha.hasArity vs.dropLast.length :=
            BType.prod_left_hasArity_dropLast hvs hprod_arity
          have hdrop : vs.dropLast.length - 1 = vs.length - 2 := by
            rw [List.length_dropLast]
            omega
          have hlen := hsigma.fromProdl_length_of_hasArity hprefix_arity
          rw [List.length_concat, ← hdrop, hlen, List.length_dropLast]
          omega)))
    (source_respects : ∀ ss : Fin vs.length → SMT.Dom.{u},
      (∀ i, GammaP.lookup vs[i] = some (ss i).snd.fst) →
      B.RenamingContext.RespectsTypeContextOnFV
        (Function.updates Theta vs
          ((List.ofFn ss).map Option.some)) GammaP P)
    (target_respects : ∀ ss : Fin vs.length → SMT.Dom.{u},
      (∀ i, GammaP.lookup vs[i] = some (ss i).snd.fst) →
      SMT.RenamingContext.RespectsTypeContextOnFV
        (Function.updates Theta vs
          ((List.ofFn ss).map Option.some)) GammaP Penc)
    (specs_true : ∀ ss : Fin vs.length → SMT.Dom.{u},
      (∀ i, GammaP.lookup vs[i] = some (ss i).snd.fst) →
      SpecBodiesTrue
        (Function.updates Theta vs
          ((List.ofFn ss).map Option.some)) GammaP DltP)
    (z_not_fv_Penc : z ∉ SMT.fv Penc) :
    ∃ (Pval : ZFSet.{u}) (hPval : Pval ∈ ⟦BType.bool⟧ᶻ)
      (Dp : SMT.Dom.{u}),
      ⟦(B.Term.abstract.go P vs Xi (fun v hv hvs => Xi_fv v
        (B.fv.mem_collect (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ =
        some (⟨Pval, BType.bool, hPval⟩ : B.Dom) ∧
      ⟦(SMT.substList vs
        ((toDestPair vs.dropLast (.var z)).concat (.the Dapp)) Penc).abstract
        (Function.update Theta z (some Wa)) hcov_sub⟧ˢ = some Dp ∧
      Dp.snd.fst = SMTType.bool ∧
      (Dp.fst = ZFSet.zftrue ↔ Pval = ZFSet.zftrue) := by
  have hpair_type : a.pair b ∈ ⟦alpha ×ᴮ beta⟧ᶻ :=
    ZFSet.pair_mem_prod.mpr ⟨ha, hb⟩
  have hpair_arity : (a.pair b).hasArity vs.length :=
    hasArity_of_mem_toZFSet hprod_arity hpair_type
  have hx_fin_type : ∀ i, (x_fin i).snd.fst =
      (alpha ×ᴮ beta).get vs.length i ∧
      (x_fin i).fst ∈ ⟦(alpha ×ᴮ beta).get vs.length i⟧ᶻ := by
    intro i
    have hmem := (x_fin i).snd.snd
    rw [hx_fin i] at hmem
    rw [hx_fin i]
    exact ⟨rfl, hmem⟩
  have hx_fin_def : x_fin = fun i =>
      (⟨(a.pair b).get vs.length i,
        (alpha ×ᴮ beta).get vs.length i,
        get_mem_type_of_isTuple hpair_arity hprod_arity hpair_type⟩ : B.Dom) := by
    funext i
    simpa only [proof_irrel_heq] using hx_fin i
  have hx_fin_eq : ZFSet.ofFinDom x_fin = a.pair b := by
    rw [hx_fin_def]
    simpa only [proof_irrel_heq] using
      (ZFSet.ofFinDom_get (List.length_pos_iff.mpr vs_nemp)
        (fun i => get_mem_type_of_isTuple hpair_arity hprod_arity hpair_type)
        hpair_arity hprod_arity)
  have hx_fin_D : ZFSet.ofFinDom x_fin ∈ Dval := by
    rw [hx_fin_eq]
    exact hmem_D
  obtain ⟨XiP_fv, Pval, hPval, den_P⟩ :=
    B.denote_collect_predicate_exists Xi_fv vs_nemp vs_nodup hprod_arity
      den_D den_collect typ_P hx_fin_type hx_fin_D wf
  obtain ⟨Dp, hden_Psub, hDp_type, htruth⟩ :=
    represented_option_collect_subst_truth_of_some_guarded_supported
      (Penc := Penc) (Dapp := Dapp) prefix_nemp vs_nodup hsigma hrho
      ha hb hvs hprod_arity hx_fin hcov_z hden_z hWa_type hWa_mem Wa_rel
      hcov_Dapp hden_Dapp hDapp_type hWb_type Wb_rel hDapp_value
      hDapp_fv_not_bv hDapp_fv_disj_vs hvs_not_bv hz_not_bv hz_not_vs
      hcov_sub hcov_upd P_guard P_scope typ_Penc XiP_fv ambient wf
      bound_expected source_respects target_respects specs_true den_P
      z_not_fv_Penc
  have den_P_go :
      ⟦(B.Term.abstract.go P vs Xi (fun v hv hvs => Xi_fv v
        (B.fv.mem_collect (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ =
        some (⟨Pval, BType.bool, hPval⟩ : B.Dom) := by
    rw [denote_term_abstract_go_eq_term_abstract vs_nodup vs_nemp x_fin
      XiP_fv]
    exact den_P
  exact ⟨Pval, hPval, Dp, den_P_go, hden_Psub,
    hDp_type.trans hP_sigma, htruth⟩

open Classical in
/-- The guarded option body characterizes one collected graph point for an
arbitrary represented payload type. -/
theorem represented_option_collect_guarded_body_graph_iff_supported.{u}
    {vs : List B.𝒱} {D P : B.Term} {alpha beta : BType} {rho : SMTType}
    {Xi : B.RenamingContext.Context.{u}}
    (Xi_fv : ∀ v ∈ B.fv (B.Term.collect vs D P), (Xi v).isSome = true)
    (hprod_arity : (alpha ×ᴮ beta).hasArity vs.length)
    {Dval : ZFSet.{u}} {hDval : Dval ∈ ⟦BType.set (alpha ×ᴮ beta)⟧ᶻ}
    (den_D : ⟦D.abstract Xi
      (fun v hv => Xi_fv v (B.fv.mem_collect (.inl hv)))⟧ᴮ =
      some (⟨Dval, BType.set (alpha ×ᴮ beta), hDval⟩ : B.Dom))
    {T : ZFSet.{u}} {hT : T ∈ ⟦BType.set (alpha ×ᴮ beta)⟧ᶻ}
    (den_collect : ⟦(B.Term.collect vs D P).abstract Xi Xi_fv⟧ᴮ =
      some (⟨T, BType.set (alpha ×ᴮ beta), hT⟩ : B.Dom))
    {a b : ZFSet.{u}} (ha : a ∈ ⟦alpha⟧ᶻ) (hb : b ∈ ⟦beta⟧ᶻ)
    {x_fin : Fin vs.length → B.Dom.{u}}
    (hx_fin : ∀ i, x_fin i =
      (⟨(a.pair b).get vs.length i,
        (alpha ×ᴮ beta).get vs.length i,
        get_mem_type_of_isTuple
          (hasArity_of_mem_toZFSet hprod_arity
            (ZFSet.pair_mem_prod.mpr ⟨ha, hb⟩))
          hprod_arity (ZFSet.pair_mem_prod.mpr ⟨ha, hb⟩)⟩ : B.Dom))
    {Dapp Psub : SMT.Term}
    {Theta : SMT.RenamingContext.Context.{u}}
    {Dd Dbody Wb : SMT.Dom.{u}}
    (hcov_Dapp : SMT.RenamingContext.CoversFV Theta Dapp)
    (hden_Dapp : ⟦Dapp.abstract Theta hcov_Dapp⟧ˢ = some Dd)
    (hD_type : Dd.snd.fst = SMTType.option rho)
    (hWb_type : Wb.snd.fst = rho)
    (hcov_Psub : SMT.RenamingContext.CoversFV Theta Psub)
    (hdomain : Dd.fst = (ZFSet.Option.some
      (S := ⟦rho⟧ᶻ) ⟨Wb.fst,
        by rw [← hWb_type]; exact Wb.snd.snd⟩).val ↔
      a.pair b ∈ Dval)
    (hpredicate : a.pair b ∈ Dval →
      ∃ (Pval : ZFSet.{u}) (hPval : Pval ∈ ⟦BType.bool⟧ᶻ)
        (Dp : SMT.Dom.{u}),
        ⟦(B.Term.abstract.go P vs Xi (fun v hv hvs => Xi_fv v
          (B.fv.mem_collect (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ =
          some (⟨Pval, BType.bool, hPval⟩ : B.Dom) ∧
        ⟦Psub.abstract Theta hcov_Psub⟧ˢ = some Dp ∧
        Dp.snd.fst = SMTType.bool ∧
        (Dp.fst = ZFSet.zftrue ↔ Pval = ZFSet.zftrue))
    (hcov_body : SMT.RenamingContext.CoversFV Theta
      (SMT.Term.ite
        (SMT.Term.and (SMT.Term.eq Dapp (SMT.Term.some (SMT.Term.the Dapp)))
          Psub)
        (SMT.Term.some (SMT.Term.the Dapp)) (none$ rho)))
    (hden_body : ⟦(SMT.Term.ite
        (SMT.Term.and (SMT.Term.eq Dapp (SMT.Term.some (SMT.Term.the Dapp)))
          Psub)
        (SMT.Term.some (SMT.Term.the Dapp)) (none$ rho)).abstract
          Theta hcov_body⟧ˢ = some Dbody) :
    Dbody.fst = (ZFSet.Option.some
      (S := ⟦rho⟧ᶻ) ⟨Wb.fst,
        by rw [← hWb_type]; exact Wb.snd.snd⟩).val ↔
      a.pair b ∈ T := by
  have hpair_type : a.pair b ∈ ⟦alpha ×ᴮ beta⟧ᶻ :=
    ZFSet.pair_mem_prod.mpr ⟨ha, hb⟩
  have hpair_arity : (a.pair b).hasArity vs.length :=
    hasArity_of_mem_toZFSet hprod_arity hpair_type
  have hx_fin_eq : x_fin = fun i =>
      (⟨(a.pair b).get vs.length i,
        (alpha ×ᴮ beta).get vs.length i,
        get_mem_type_of_isTuple hpair_arity hprod_arity hpair_type⟩ : B.Dom) := by
    funext i
    simpa only [proof_irrel_heq] using hx_fin i
  by_cases hmem_D : a.pair b ∈ Dval
  · obtain ⟨Pval, hPval, Dp, den_P, hden_Psub, hP_type, htruth⟩ :=
      hpredicate hmem_D
    have den_P' :
        ⟦(B.Term.abstract.go P vs Xi (fun v hv hvs => Xi_fv v
          (B.fv.mem_collect (.inr ⟨hv, hvs⟩)))).uncurry
            (fun i => ⟨(a.pair b).get vs.length i,
              (alpha ×ᴮ beta).get vs.length i,
              get_mem_type_of_isTuple hpair_arity hprod_arity hpair_type⟩)⟧ᴮ =
          some (⟨Pval, BType.bool, hPval⟩ : B.Dom) := by
      rw [← hx_fin_eq]
      exact den_P
    exact represented_option_collect_guarded_body_iff Xi_fv hprod_arity
      den_D den_collect hpair_arity hpair_type den_P' hcov_Dapp hden_Dapp
      hD_type hcov_Psub hden_Psub hP_type hWb_type hcov_body hden_body
      hdomain htruth
  · constructor
    · intro hbody_value
      have hDapp_value :=
        denote_guarded_option_term_some_implies_domain hcov_Dapp hden_Dapp
          hD_type hWb_type hcov_body hden_body hbody_value
      exact (hmem_D (hdomain.mp hDapp_value)).elim
    · intro hmem_T
      exact (hmem_D (B.denote_collect_mem_domain Xi_fv hprod_arity den_D
        den_collect hmem_T)).elim

open Classical in
/-- Semantic core for a function-valued collection at arbitrary supported
domain and payload representations. -/
theorem represented_collect_option_lambda_supported.{u}
    {vs : List B.𝒱} (vs_nemp : vs ≠ []) (prefix_nemp : vs.dropLast ≠ [])
    (vs_nodup : vs.Nodup)
    {D P : B.Term} {alpha beta : BType} {sigma rho : SMTType}
    (hsigma : BType.SupportedSMT alpha sigma)
    (hrho : BType.SupportedSMT beta rho)
    {Xi : B.RenamingContext.Context.{u}}
    (Xi_fv : ∀ v ∈ B.fv (B.Term.collect vs D P), (Xi v).isSome = true)
    (hprod_arity : (alpha ×ᴮ beta).hasArity vs.length)
    (hvs : 2 ≤ vs.length)
    {Dval : ZFSet.{u}} {hDval : Dval ∈ ⟦BType.set (alpha ×ᴮ beta)⟧ᶻ}
    (den_D : ⟦D.abstract Xi
      (fun v hv => Xi_fv v (B.fv.mem_collect (.inl hv)))⟧ᴮ =
      some (⟨Dval, BType.set (alpha ×ᴮ beta), hDval⟩ : B.Dom))
    {T : ZFSet.{u}} {hT : T ∈ ⟦BType.set (alpha ×ᴮ beta)⟧ᶻ}
    (den_collect : ⟦(B.Term.collect vs D P).abstract Xi Xi_fv⟧ᴮ =
      some (⟨T, BType.set (alpha ×ᴮ beta), hT⟩ : B.Dom))
    {Denc Penc body : SMT.Term} {z : SMT.𝒱}
    {ThetaD : SMT.RenamingContext.Context.{u}} {DencVal : SMT.Dom.{u}}
    (body_def : body = SMT.Term.ite
      (SMT.Term.and (SMT.Term.eq ((@ˢDenc) (.var z))
        (SMT.Term.some (SMT.Term.the ((@ˢDenc) (.var z)))))
      (SMT.substList vs
        ((toDestPair vs.dropLast (.var z)).concat
          (.the ((@ˢDenc) (.var z)))) Penc))
      (SMT.Term.some (SMT.Term.the ((@ˢDenc) (.var z))))
      (none$ rho))
    (hcov_lambda : SMT.RenamingContext.CoversFV ThetaD
      ((λˢ [z]) [sigma] body))
    {lamVal : SMT.Dom.{u}}
    (hden_lambda : ⟦((λˢ [z]) [sigma] body).abstract
      ThetaD hcov_lambda⟧ˢ = some lamVal)
    (hlam_type : lamVal.snd.fst = sigma.fun (SMTType.option rho))
    (hcov_D_upd : ∀ W : SMT.Dom,
      SMT.RenamingContext.CoversFV
        (Function.update ThetaD z (some W)) Denc)
    (den_D_upd : ∀ W : SMT.Dom,
      ⟦Denc.abstract (Function.update ThetaD z (some W))
        (hcov_D_upd W)⟧ˢ = some DencVal)
    (hDenc_type : DencVal.snd.fst = sigma.fun (SMTType.option rho))
    (hDenc_func : ⟦sigma⟧ᶻ.IsFunc
      ⟦SMTType.option rho⟧ᶻ DencVal.fst)
    (D_rel : RDomCastSupported
      (⟨Dval, BType.set (alpha ×ᴮ beta), hDval⟩ : B.Dom) DencVal)
    (hcov_body_upd : ∀ W : SMT.Dom,
      SMT.RenamingContext.CoversFV
        (Function.update ThetaD z (some W)) body)
    (hbody_total : ∀ W : SMT.Dom, W.snd.fst = sigma →
      ∃ bodyVal : SMT.Dom,
        ⟦body.abstract (Function.update ThetaD z (some W))
          (hcov_body_upd W)⟧ˢ = some bodyVal)
    (hDapp_fv_not_bv : ∀ w ∈ SMT.fv ((@ˢDenc) (.var z)),
      w ∉ SMT.bv Penc)
    (hDapp_fv_disj_vs : ∀ w ∈ SMT.fv ((@ˢDenc) (.var z)), w ∉ vs)
    (hvs_not_bv : ∀ v ∈ vs, v ∉ SMT.bv Penc)
    (hz_not_bv : z ∉ SMT.bv Penc) (hz_not_vs : z ∉ vs)
    (hcov_sub_upd : ∀ W : SMT.Dom,
      SMT.RenamingContext.CoversFV
        (Function.update ThetaD z (some W))
        (SMT.substList vs
          ((toDestPair vs.dropLast (.var z)).concat
            (.the ((@ˢDenc) (.var z)))) Penc))
    (hcov_P_upd : ∀ (W : SMT.Dom) (ss : Fin vs.length → SMT.Dom),
      SMT.RenamingContext.CoversFV
        (Function.updates (Function.update ThetaD z (some W)) vs
          ((List.ofFn ss).map Option.some)) Penc)
    {Ebody : B.Env} {LambdaP GammaP : SMT.TypeContext}
    {DltP : SMT.Chunk} {sigmaP : SMTType}
    (typ_P : Ebody.context ⊢ᴮ P : BType.bool)
    (P_guard : EncodeTermRepGuardedSound.{u}
      P Ebody BType.bool Penc sigmaP LambdaP DltP)
    (P_scope : ScopedContextExtends LambdaP DltP GammaP)
    (typ_Penc : GammaP ⊢ˢ Penc : sigmaP)
    (hP_sigma : sigmaP = SMTType.bool)
    (ambient : ∀ v ∈ B.fv P, v ∉ vs →
      match Xi v, ThetaD v with
      | some d, some d' => RDomCastSupported d d'
      | _, _ => False)
    (wf_bound : ∀ (a b : ZFSet.{u}) (ha : a ∈ ⟦alpha⟧ᶻ)
      (hb : b ∈ ⟦beta⟧ᶻ),
      B.RenWF Ebody.context
        (Function.updates Xi vs (List.ofFn fun i => some
          (⟨(a.pair b).get vs.length i,
            (alpha ×ᴮ beta).get vs.length i,
            get_mem_type_of_isTuple
              (hasArity_of_mem_toZFSet hprod_arity
                (ZFSet.pair_mem_prod.mpr ⟨ha, hb⟩))
              hprod_arity (ZFSet.pair_mem_prod.mpr ⟨ha, hb⟩)⟩ : B.Dom))))
    (bound_expected : ∀ i : Fin vs.length,
      GammaP.lookup vs[i] = some
        (((sigma.fromProdl (vs.length - 2)).concat rho)[i.val]'(by
          have hprefix_arity : alpha.hasArity vs.dropLast.length :=
            BType.prod_left_hasArity_dropLast hvs hprod_arity
          have hdrop : vs.dropLast.length - 1 = vs.length - 2 := by
            rw [List.length_dropLast]
            omega
          have hlen := hsigma.fromProdl_length_of_hasArity hprefix_arity
          rw [List.length_concat, ← hdrop, hlen, List.length_dropLast]
          omega)))
    (source_respects : ∀ ss : Fin vs.length → SMT.Dom.{u},
      (∀ i, GammaP.lookup vs[i] = some (ss i).snd.fst) →
      B.RenamingContext.RespectsTypeContextOnFV
        (Function.updates ThetaD vs
          ((List.ofFn ss).map Option.some)) GammaP P)
    (target_respects : ∀ ss : Fin vs.length → SMT.Dom.{u},
      (∀ i, GammaP.lookup vs[i] = some (ss i).snd.fst) →
      SMT.RenamingContext.RespectsTypeContextOnFV
        (Function.updates ThetaD vs
          ((List.ofFn ss).map Option.some)) GammaP Penc)
    (specs_true : ∀ ss : Fin vs.length → SMT.Dom.{u},
      (∀ i, GammaP.lookup vs[i] = some (ss i).snd.fst) →
      SpecBodiesTrue
        (Function.updates ThetaD vs
          ((List.ofFn ss).map Option.some)) GammaP DltP)
    (z_not_fv_Penc : z ∉ SMT.fv Penc) :
    RDomCastSupported
      (⟨T, BType.set (alpha ×ᴮ beta), hT⟩ : B.Dom) lamVal := by
  subst body
  rcases lamVal with ⟨F, lamType, hF⟩
  dsimp at hlam_type hden_lambda ⊢
  subst lamType
  have hFfunc : ⟦sigma⟧ᶻ.IsFunc ⟦SMTType.option rho⟧ᶻ F := by
    simpa [SMTType.toZFSet] using hF
  rcases DencVal with ⟨G, DencType, hG⟩
  dsimp at hDenc_type hDenc_func D_rel den_D_upd
  subst DencType
  have pointwise : ∀ (x : ZFSet.{u}) (hx : x ∈ ⟦alpha⟧ᶻ)
      (p : ZFSet.{u}) (hp : p ∈ ⟦beta⟧ᶻ)
      (a : ZFSet.{u}) (ha : a ∈ ⟦sigma⟧ᶻ)
      (b : ZFSet.{u}) (hb : b ∈ ⟦rho⟧ᶻ),
      RDomCastSupported (⟨x, alpha, hx⟩ : B.Dom)
          (⟨a, sigma, ha⟩ : SMT.Dom) →
      RDomCastSupported (⟨p, beta, hp⟩ : B.Dom)
          (⟨b, rho, hb⟩ : SMT.Dom) →
      ((ZFSet.fapply F (ZFSet.is_func_is_pfunc hFfunc)
        ⟨a, by rw [ZFSet.is_func_dom_eq hFfunc]; exact ha⟩).val =
          (ZFSet.Option.some (S := ⟦rho⟧ᶻ) ⟨b, hb⟩).val ↔
        x.pair p ∈ T) := by
    intro x hx p hp a ha b hb Xrel Yrel
    let Wa : SMT.Dom := ⟨a, sigma, ha⟩
    let Wb : SMT.Dom := ⟨b, rho, hb⟩
    obtain ⟨bodyVal, hden_body⟩ := hbody_total Wa rfl
    obtain ⟨hcov_Dapp, DappVal, hDapp_type, hDapp_value, hden_Dapp⟩ :=
      funDenoteAppAt (Δctx := ThetaD) (t := Denc) (x := z)
        (α := sigma) (β := SMTType.option rho)
        (Y := (⟨G, sigma.fun (SMTType.option rho), hG⟩ : SMT.Dom))
        hcov_D_upd den_D_upd rfl hDenc_func Wa rfl ha
    have hdomain : DappVal.fst = (ZFSet.Option.some
        (S := ⟦rho⟧ᶻ) ⟨Wb.fst, Wb.snd.snd⟩).val ↔
        x.pair p ∈ Dval := by
      rw [hDapp_value]
      simpa [Wa, Wb, proof_irrel_heq] using
        (RDomCast.optionFunction_fapply_eq_some_iff D_rel.toRDomCast
          Xrel.toRDomCast Yrel.toRDomCast)
    have hcov_z : SMT.RenamingContext.CoversFV
        (Function.update ThetaD z (some Wa)) (.var z) := by
      intro v hv
      simp only [SMT.fv, List.mem_singleton] at hv
      subst v
      simp
    have hden_z : ⟦(SMT.Term.var z).abstract
        (Function.update ThetaD z (some Wa)) hcov_z⟧ˢ = some Wa := by
      simp only [SMT.Term.abstract, Function.update_self, Option.get_some,
        SMT.denote, Option.pure_def]
    have hgraph := represented_option_collect_guarded_body_graph_iff_supported
      (D := D) (P := P) (alpha := alpha) (beta := beta) (rho := rho)
      Xi_fv hprod_arity den_D den_collect hx hp
      (x_fin := fun i => ⟨(x.pair p).get vs.length i,
        (alpha ×ᴮ beta).get vs.length i,
        get_mem_type_of_isTuple
          (hasArity_of_mem_toZFSet hprod_arity
            (ZFSet.pair_mem_prod.mpr ⟨hx, hp⟩))
          hprod_arity (ZFSet.pair_mem_prod.mpr ⟨hx, hp⟩)⟩)
      (by intro i; rfl)
      hcov_Dapp hden_Dapp hDapp_type rfl (hcov_sub_upd Wa) hdomain
      (by
        intro hmem_D
        exact represented_option_collect_predicate_setup_guarded_supported
          (D := D) (P := P) (alpha := alpha) (beta := beta)
          vs_nemp prefix_nemp vs_nodup hsigma hrho Xi_fv hprod_arity
          den_D den_collect hx hp hvs
          (x_fin := fun i => ⟨(x.pair p).get vs.length i,
            (alpha ×ᴮ beta).get vs.length i,
            get_mem_type_of_isTuple
              (hasArity_of_mem_toZFSet hprod_arity
                (ZFSet.pair_mem_prod.mpr ⟨hx, hp⟩))
              hprod_arity (ZFSet.pair_mem_prod.mpr ⟨hx, hp⟩)⟩)
          (by intro i; rfl) hmem_D hcov_z hden_z rfl ha Xrel
          hcov_Dapp hden_Dapp hDapp_type rfl Yrel
          (hdomain.mpr hmem_D) hDapp_fv_not_bv hDapp_fv_disj_vs
          hvs_not_bv hz_not_bv hz_not_vs (hcov_sub_upd Wa)
          (hcov_P_upd Wa) typ_P P_guard P_scope typ_Penc hP_sigma ambient
          (wf_bound x p hx hp) bound_expected source_respects target_respects
          specs_true z_not_fv_Penc)
      (hcov_body_upd Wa) hden_body
    have happly := single_lambda_fapply_eq_body hcov_lambda hden_lambda
      hFfunc (W := Wa) rfl ha (hcov_body_upd Wa) hden_body
    rw [happly]
    simpa [Wb, proof_irrel_heq] using hgraph
  apply RDomCastSupported.optionFunction_of_pointwise hsigma hrho hT hF hFfunc
  · intro a ha b hb happ
    obtain ⟨x, hx, Xrel⟩ :=
      RDomCastSupported.source_of_supported_target hsigma ha
    obtain ⟨p, hp, Yrel⟩ :=
      RDomCastSupported.source_of_supported_target hrho hb
    refine ⟨x, hx, p, hp, ?_, Xrel, Yrel⟩
    exact (pointwise x hx p hp a ha b hb Xrel Yrel).mp
      (by simpa only [proof_irrel_heq] using happ)
  · intro x hx p hp hmem_T
    have hmem_D := B.denote_collect_mem_domain Xi_fv hprod_arity den_D
      den_collect hmem_T
    let rsigma := castPath.reflexive sigma
    let rrho := castPath.reflexive rho
    have graphRel0 :=
      RDomCastSupported.optionFun_graph_cast_supported
        hsigma hrho hsigma hrho D_rel rsigma rrho
        (fun relx rely => RDomCastSupported.cast_eq_iff relx rely
          (castPath.pair rsigma rrho))
    have graphRel : RDomCastSupported
        (⟨Dval, BType.set (alpha ×ᴮ beta), hDval⟩ : B.Dom)
        (⟨optionGraph sigma rho G,
          SMTType.fun (SMTType.pair sigma rho) SMTType.bool,
          optionGraph_mem sigma rho hG⟩ : SMT.Dom) := by
      simpa only [optionGraph, rsigma, rrho, proof_irrel_heq] using graphRel0
    obtain ⟨q, hq, qrel⟩ := graphRel.setPred_member_preimage hmem_D
    obtain ⟨a, ha, b, hb, rfl⟩ := ZFSet.mem_prod.mp hq
    have qrel' : RDomCastSupported
        (⟨x.pair p, alpha ×ᴮ beta,
          ZFSet.pair_mem_prod.mpr ⟨hx, hp⟩⟩ : B.Dom)
        (⟨a.pair b, SMTType.pair sigma rho,
          ZFSet.pair_mem_prod.mpr ⟨ha, hb⟩⟩ : SMT.Dom) := by
      simpa only [proof_irrel_heq] using qrel
    obtain ⟨Xrel, Yrel⟩ := RDomCastSupported.of_pair
      (hX := hx) (hY := hp) (hX' := ha) (hY' := hb) qrel'
    refine ⟨a, ha, b, hb, Xrel, Yrel, ?_⟩
    exact (pointwise x hx p hp a ha b hb Xrel Yrel).mpr hmem_T
