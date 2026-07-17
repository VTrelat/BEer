import SMT.Reasoning.Basic.EncodeTermRepresentedBinders
import SMT.Reasoning.Basic.CollectCaseHelpers

open B SMT ZFSet

/-!
# Representation-aware collection

The collection encoder builds an SMT lambda whose body is an `ite`: the
encoded domain predicate selects the substituted predicate body.  The lemmas
here isolate this last semantic step from the operational proof that constructs
the represented contexts.
-/

/- Unfold a successful source collection denotation into the separation
equation used by the SMT-lambda retraction proof.  Keeping this source-only
fact independent of the target representation lets the main and alternative
valuation arguments share it. -/
open Classical in
theorem B.denote_collect_eq_sep.{u}
    {vs : List B.𝒱} {D P : B.Term} {tau : BType}
    {Xi : B.RenamingContext.Context.{u}}
    (Xi_fv : ∀ v ∈ B.fv (B.Term.collect vs D P), (Xi v).isSome = true)
    (tau_hasArity : tau.hasArity vs.length)
    {Dval : ZFSet.{u}} {hDval : Dval ∈ ⟦BType.set tau⟧ᶻ}
    (den_D : ⟦D.abstract Xi
      (fun v hv => Xi_fv v (B.fv.mem_collect (.inl hv)))⟧ᴮ =
      some (⟨Dval, BType.set tau, hDval⟩ : B.Dom))
    {T : ZFSet.{u}} {hT : T ∈ ⟦BType.set tau⟧ᶻ}
    (den_collect : ⟦(B.Term.collect vs D P).abstract Xi Xi_fv⟧ᴮ =
      some (⟨T, BType.set tau, hT⟩ : B.Dom)) :
    ZFSet.sep (fun x =>
      if hx : x.hasArity vs.length ∧ tau.hasArity vs.length ∧ x ∈ ⟦tau⟧ᶻ then
        match ⟦(B.Term.abstract.go P vs Xi (fun v hv hvs => Xi_fv v
          (B.fv.mem_collect (.inr ⟨hv, hvs⟩)))).uncurry
          (fun i => ⟨x.get vs.length i, ⟨tau.get vs.length i,
            get_mem_type_of_isTuple hx.1 hx.2.1 hx.2.2⟩⟩)⟧ᴮ with
        | some ⟨Pz, _⟩ => Pz = ZFSet.zftrue
        | none => False
      else False) Dval = T := by
  have h_inv := den_collect
  simp only [B.Term.abstract] at h_inv
  unfold B.denote at h_inv
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h_inv
  obtain ⟨D_dom, hden_d, rest⟩ := h_inv
  have hconv_d : ⟦D.abstract Xi
      (fun v hv => Xi_fv v (B.fv.mem_collect (.inl hv)))⟧ᴮ =
      some D_dom := by
    convert hden_d using 2
  have hD_dom_eq : D_dom =
      (⟨Dval, BType.set tau, hDval⟩ : B.Dom) := by
    rw [hconv_d] at den_D
    exact Option.some.inj den_D
  subst D_dom
  simp only at rest
  split at rest
  · simp only [Option.bind_eq_some_iff] at rest
    obtain ⟨_, denP_eq, rest2⟩ := rest
    split_ifs at rest2 with h_den_P_cond h_typP_det_cond
    · simp only [Option.pure_def, Option.some.injEq, PSigma.mk.injEq] at rest2
      rw [← rest2.1]
      congr 1
      funext x
      simp
      constructor
      · rintro ⟨hx, match_eq⟩
        exact ⟨hx, by
          split at match_eq
          · rename_i h
            erw [h]
            exact match_eq
          · nomatch match_eq⟩
      · rintro ⟨hx, match_eq⟩
        exact ⟨hx, by
          split at match_eq
          · rename_i h
            erw [h]
            exact match_eq
          · nomatch match_eq⟩
  · rename_i h_neg
    exact absurd
      ⟨BType.hasArity_of_foldl_defaultZFSet tau_hasArity, tau_hasArity⟩
      h_neg

/- A successful source collection denotation also supplies the totality of
its predicate at every tuple selected from its source domain.  This is the
second source-side ingredient of the lambda retraction argument, alongside
`B.denote_collect_eq_sep`. -/
open Classical in
theorem B.denote_collect_predicate_total.{u}
    {vs : List B.𝒱} {D P : B.Term} {tau : BType}
    {Xi : B.RenamingContext.Context.{u}}
    (Xi_fv : ∀ v ∈ B.fv (B.Term.collect vs D P), (Xi v).isSome = true)
    (tau_hasArity : tau.hasArity vs.length)
    {Dval : ZFSet.{u}} {hDval : Dval ∈ ⟦BType.set tau⟧ᶻ}
    (den_D : ⟦D.abstract Xi
      (fun v hv => Xi_fv v (B.fv.mem_collect (.inl hv)))⟧ᴮ =
      some (⟨Dval, BType.set tau, hDval⟩ : B.Dom))
    {T : ZFSet.{u}} {hT : T ∈ ⟦BType.set tau⟧ᶻ}
    (den_collect : ⟦(B.Term.collect vs D P).abstract Xi Xi_fv⟧ᴮ =
      some (⟨T, BType.set tau, hT⟩ : B.Dom)) :
    ∀ {x_fin : Fin vs.length → B.Dom.{u}},
      (∀ i, (x_fin i).snd.fst = tau.get vs.length i ∧
        (x_fin i).fst ∈ ⟦tau.get vs.length i⟧ᶻ) →
      ZFSet.ofFinDom x_fin ∈ Dval →
      ⟦(B.Term.abstract.go P vs Xi (fun v hv hvs => Xi_fv v
        (B.fv.mem_collect (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ.isSome = true := by
  intro x_fin hx_typ hx_mem
  have h_inv := den_collect
  simp only [B.Term.abstract] at h_inv
  unfold B.denote at h_inv
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h_inv
  obtain ⟨D_dom, hden_d, rest⟩ := h_inv
  have hconv_d : ⟦D.abstract Xi
      (fun v hv => Xi_fv v (B.fv.mem_collect (.inl hv)))⟧ᴮ =
      some D_dom := by
    convert hden_d using 2
  have hD_dom_eq : D_dom =
      (⟨Dval, BType.set tau, hDval⟩ : B.Dom) := by
    rw [hconv_d] at den_D
    exact Option.some.inj den_D
  subst D_dom
  simp only at rest
  split at rest
  · simp only [Option.bind_eq_some_iff] at rest
    obtain ⟨_, _, rest2⟩ := rest
    split_ifs at rest2 with h_den_P_cond
    exact h_den_P_cond hx_typ hx_mem
  · rename_i h_neg
    exact absurd
      ⟨BType.hasArity_of_foldl_defaultZFSet tau_hasArity, tau_hasArity⟩
      h_neg

/-- If the collection-domain application is true, the generated `ite` has the
same truth value as its substituted predicate branch. -/
theorem collect_ite_truth_of_true_domain.{u}
    {Dapp Psub body : SMT.Term} {Theta : SMT.RenamingContext.Context.{u}}
    (hbody_def : body = Dapp.ite Psub (.bool false))
    (hcov_body : SMT.RenamingContext.CoversFV Theta body)
    (hcov_Dapp : SMT.RenamingContext.CoversFV Theta Dapp)
    (hcov_Psub : SMT.RenamingContext.CoversFV Theta Psub)
    {dD dP dBody : SMT.Dom.{u}}
    (hden_Dapp : ⟦Dapp.abstract Theta hcov_Dapp⟧ˢ = some dD)
    (hden_Psub : ⟦Psub.abstract Theta hcov_Psub⟧ˢ = some dP)
    (hden_body : ⟦body.abstract Theta hcov_body⟧ˢ = some dBody)
    (hD_type : dD.snd.fst = SMTType.bool)
    (hD_true : dD.fst = ZFSet.zftrue) :
    dBody = dP := by
  rcases dD with ⟨Dval, sigmaD, hD_mem⟩
  dsimp at hD_type hD_true
  subst sigmaD
  subst body
  rw [SMT.Term.abstract, SMT.denote, Option.bind_eq_bind] at hden_body
  conv at hden_body =>
    lhs
    rw [SMT.RenamingContext.denote_abstract_proof_irrel Dapp Theta _ hcov_Dapp]
  rw [hden_Dapp] at hden_body
  simp only [Option.bind_some] at hden_body
  have hD_bool : ZFSet.ZFBool.toBool ⟨Dval, hD_mem⟩ = true := by
    rw [show (⟨Dval, hD_mem⟩ : ZFSet.ZFBool) =
      ⟨ZFSet.zftrue, ZFSet.ZFBool.zftrue_mem_𝔹⟩ from Subtype.ext hD_true]
    exact ZFSet.ZFBool.toBool_true
  rw [show ZFSet.ZFBool.toBool ⟨Dval, _⟩ = true from by
    convert hD_bool] at hden_body
  simp only [ite_true] at hden_body
  conv at hden_body =>
    lhs
    rw [SMT.RenamingContext.denote_abstract_proof_irrel Psub Theta _ hcov_Psub]
  rw [hden_Psub] at hden_body
  exact Option.some.inj hden_body.symm

/-- The full collection-body bridge: once the represented predicate body is
transported through its binder substitution, a true domain application makes
the generated `ite` true exactly when the B predicate is true. -/
theorem collect_ite_truth_of_represented_subst.{u}
    {Dapp Penc body : SMT.Term}
    (xs : List SMT.𝒱) (ts : List SMT.Term)
    {Delta ThetaBody : SMT.RenamingContext.Context.{u}}
    (Ds : List SMT.Dom.{u})
    (hbody_def : body = Dapp.ite (SMT.substList xs ts Penc) (.bool false))
    (hcov_body : SMT.RenamingContext.CoversFV Delta body)
    (hcov_Dapp : SMT.RenamingContext.CoversFV Delta Dapp)
    (hlen_xt : xs.length = ts.length) (hlen_xd : xs.length = Ds.length)
    (hnodup : xs.Nodup)
    (hxs_not_bv : ∀ x ∈ xs, x ∉ SMT.bv Penc)
    (hts_bv_nil : ∀ t ∈ ts, SMT.bv t = [])
    (hts_fv_not_bv : ∀ t ∈ ts, ∀ w ∈ SMT.fv t, w ∉ SMT.bv Penc)
    (hts_not_none : ∀ t ∈ ts, t ≠ SMT.Term.none)
    (hts_fv_disj_xs : ∀ t ∈ ts, ∀ w ∈ SMT.fv t, w ∉ xs)
    (hts_den : ∀ (i : ℕ) (_hi_x : i < xs.length) (hi_t : i < ts.length)
      (hi_d : i < Ds.length),
      ∃ (ht_cov : SMT.RenamingContext.CoversFV Delta ts[i]),
        ⟦ts[i].abstract Delta ht_cov⟧ˢ = some Ds[i])
    (hcov_sub : SMT.RenamingContext.CoversFV Delta
      (SMT.substList xs ts Penc))
    (hcov_upd : SMT.RenamingContext.CoversFV
      (Function.updates Delta xs (Ds.map Option.some)) Penc)
    (hcov_body_P : SMT.RenamingContext.CoversFV ThetaBody Penc)
    (hagrees : SMT.RenamingContext.AgreesOnFV
      (Function.updates Delta xs (Ds.map Option.some)) ThetaBody Penc)
    {P : ZFSet.{u}} {hP : P ∈ ⟦BType.bool⟧ᶻ}
    {dP : SMT.Dom.{u}}
    (hden_P : ⟦Penc.abstract ThetaBody hcov_body_P⟧ˢ = some dP)
    (hrel_P : RDomCastSupported
      (⟨P, BType.bool, hP⟩ : B.Dom) dP)
    {dD dBody : SMT.Dom.{u}}
    (hden_D : ⟦Dapp.abstract Delta hcov_Dapp⟧ˢ = some dD)
    (hden_body : ⟦body.abstract Delta hcov_body⟧ˢ = some dBody)
    (hD_type : dD.snd.fst = SMTType.bool)
    (hD_true : dD.fst = ZFSet.zftrue) :
    dBody.fst = ZFSet.zftrue ↔ P = ZFSet.zftrue := by
  obtain ⟨hden_sub, htruth_sub⟩ :=
    SMT.RenamingContext.denote_substList_bool_truth_of_agrees
      Penc xs ts Ds hlen_xt hlen_xd hnodup hxs_not_bv hts_bv_nil
      hts_fv_not_bv hts_not_none hts_fv_disj_xs hts_den hcov_sub
      hcov_upd hcov_body_P hagrees hden_P hrel_P
  have hbody_eq := collect_ite_truth_of_true_domain hbody_def hcov_body
    hcov_Dapp hcov_sub hden_D hden_sub hden_body hD_type hD_true
  rw [hbody_eq]
  exact htruth_sub

/-- Collection-body truth from source-level agreement.  This is the form
consumed by the operational `collect` proof after its body IH supplies the
bound-variable denotations and the stable-body free-variable bound. -/
theorem collect_ite_truth_of_represented_source_fv.{u}
    {Dapp Penc body : SMT.Term}
    (xs : List SMT.𝒱) (ts : List SMT.Term)
    {Delta ThetaBase ThetaBody : SMT.RenamingContext.Context.{u}}
    (Ds : List SMT.Dom.{u}) {source : B.Term}
    (hbody_def : body = Dapp.ite (SMT.substList xs ts Penc) (.bool false))
    (hcov_body : SMT.RenamingContext.CoversFV Delta body)
    (hcov_Dapp : SMT.RenamingContext.CoversFV Delta Dapp)
    (hlen_xt : xs.length = ts.length) (hlen_xd : xs.length = Ds.length)
    (hnodup : xs.Nodup)
    (hxs_not_bv : ∀ x ∈ xs, x ∉ SMT.bv Penc)
    (hts_bv_nil : ∀ t ∈ ts, SMT.bv t = [])
    (hts_fv_not_bv : ∀ t ∈ ts, ∀ w ∈ SMT.fv t, w ∉ SMT.bv Penc)
    (hts_not_none : ∀ t ∈ ts, t ≠ SMT.Term.none)
    (hts_fv_disj_xs : ∀ t ∈ ts, ∀ w ∈ SMT.fv t, w ∉ xs)
    (hts_den : ∀ (i : ℕ) (_hi_x : i < xs.length) (hi_t : i < ts.length)
      (hi_d : i < Ds.length),
      ∃ (ht_cov : SMT.RenamingContext.CoversFV Delta ts[i]),
        ⟦ts[i].abstract Delta ht_cov⟧ˢ = some Ds[i])
    (hcov_sub : SMT.RenamingContext.CoversFV Delta
      (SMT.substList xs ts Penc))
    (hcov_upd : SMT.RenamingContext.CoversFV
      (Function.updates Delta xs (Ds.map Option.some)) Penc)
    (hcov_body_P : SMT.RenamingContext.CoversFV ThetaBody Penc)
    (hvalues : ∀ (i : ℕ) (hi_x : i < xs.length) (hi_d : i < Ds.length),
      ThetaBody xs[i] = some Ds[i])
    (hPenc_fv : SMT.fv Penc ⊆ B.Term.vars source)
    (hctx_source : ∀ v ∈ B.Term.vars source, v ∉ xs →
      Delta v = ThetaBase v)
    (hbody_ext : SMT.RenamingContext.Extends ThetaBody ThetaBase)
    {P : ZFSet.{u}} {hP : P ∈ ⟦BType.bool⟧ᶻ}
    {dP : SMT.Dom.{u}}
    (hden_P : ⟦Penc.abstract ThetaBody hcov_body_P⟧ˢ = some dP)
    (hrel_P : RDomCastSupported
      (⟨P, BType.bool, hP⟩ : B.Dom) dP)
    {dD dBody : SMT.Dom.{u}}
    (hden_D : ⟦Dapp.abstract Delta hcov_Dapp⟧ˢ = some dD)
    (hden_body : ⟦body.abstract Delta hcov_body⟧ˢ = some dBody)
    (hD_type : dD.snd.fst = SMTType.bool)
    (hD_true : dD.fst = ZFSet.zftrue) :
    dBody.fst = ZFSet.zftrue ↔ P = ZFSet.zftrue := by
  exact collect_ite_truth_of_represented_subst
    xs ts Ds hbody_def hcov_body hcov_Dapp hlen_xt hlen_xd hnodup
    hxs_not_bv hts_bv_nil hts_fv_not_bv hts_not_none hts_fv_disj_xs
    hts_den hcov_sub hcov_upd hcov_body_P
    (SMT.RenamingContext.agreesOnFV_updates_of_source_fv
      hlen_xd hnodup hcov_upd hvalues hPenc_fv hctx_source hbody_ext)
    hden_P hrel_P hden_D hden_body hD_type hD_true

/-- The operational form of the represented collection-body bridge.  It runs
the predicate's representation-aware totality theorem at the supplied bound
values, then applies the stable-free-variable substitution bridge.  In
particular, no equality with `B.RenamingContext.toSMT` is required. -/
theorem collect_ite_truth_of_total_body_source_fv.{u}
    {Dapp Penc body : SMT.Term}
    (xs : List SMT.𝒱) (ts : List SMT.Term)
    {Delta ThetaBase : SMT.RenamingContext.Context.{u}}
    (Ds : List SMT.Dom.{u})
    (hbody_def : body = Dapp.ite (SMT.substList xs ts Penc) (.bool false))
    (hcov_body : SMT.RenamingContext.CoversFV Delta body)
    (hcov_Dapp : SMT.RenamingContext.CoversFV Delta Dapp)
    (hlen_xt : xs.length = ts.length) (hlen_xd : xs.length = Ds.length)
    (hnodup : xs.Nodup)
    (hxs_not_bv : ∀ x ∈ xs, x ∉ SMT.bv Penc)
    (hts_bv_nil : ∀ t ∈ ts, SMT.bv t = [])
    (hts_fv_not_bv : ∀ t ∈ ts, ∀ w ∈ SMT.fv t, w ∉ SMT.bv Penc)
    (hts_not_none : ∀ t ∈ ts, t ≠ SMT.Term.none)
    (hts_fv_disj_xs : ∀ t ∈ ts, ∀ w ∈ SMT.fv t, w ∉ xs)
    (hts_den : ∀ (i : ℕ) (_hi_x : i < xs.length) (hi_t : i < ts.length)
      (hi_d : i < Ds.length),
      ∃ (ht_cov : SMT.RenamingContext.CoversFV Delta ts[i]),
        ⟦ts[i].abstract Delta ht_cov⟧ˢ = some Ds[i])
    (hcov_sub : SMT.RenamingContext.CoversFV Delta
      (SMT.substList xs ts Penc))
    (hcov_upd : SMT.RenamingContext.CoversFV
      (Function.updates Delta xs (Ds.map Option.some)) Penc)
    {Pterm : B.Term} {E : B.Env} {Lambda Gamma : SMT.TypeContext}
    {sigma : SMTType} {used : List SMT.𝒱}
    (P_total : EncodeTermRepTotal.{u}
      Pterm E BType.bool Lambda Penc sigma Gamma used)
    {Xi : B.RenamingContext.Context.{u}}
    (Xi_fv : ∀ v ∈ B.fv Pterm, (Xi v).isSome = true)
    (related : RValuationCastSupportedOnFV Xi ThetaBase Pterm)
    (wf : B.RenWF E.context Xi)
    (ThetaBase_none : ∀ v ∉ used, ThetaBase v = none)
    (source_respects : B.RenamingContext.RespectsTypeContextOnFV
      ThetaBase Lambda Pterm)
    (ThetaBase_dom : ∀ v, ThetaBase v ≠ none → v ∈ Lambda)
    {Pval : ZFSet.{u}} {hPval : Pval ∈ ⟦BType.bool⟧ᶻ}
    (den_P : ⟦Pterm.abstract Xi Xi_fv⟧ᴮ =
      some (⟨Pval, BType.bool, hPval⟩ : B.Dom))
    (bound_values : ∀ (i : ℕ) (hi_x : i < xs.length) (hi_d : i < Ds.length),
      ThetaBase xs[i] = some Ds[i])
    (hPenc_fv : SMT.fv Penc ⊆ B.Term.vars Pterm)
    (hctx_source : ∀ v ∈ B.Term.vars Pterm, v ∉ xs →
      Delta v = ThetaBase v)
    {dD dBody : SMT.Dom.{u}}
    (hden_D : ⟦Dapp.abstract Delta hcov_Dapp⟧ˢ = some dD)
    (hden_body : ⟦body.abstract Delta hcov_body⟧ˢ = some dBody)
    (hD_type : dD.snd.fst = SMTType.bool)
    (hD_true : dD.fst = ZFSet.zftrue) :
    dBody.fst = ZFSet.zftrue ↔ Pval = ZFSet.zftrue := by
  obtain ⟨ThetaBody, hcov_P, dP, hbody_ext, hvalues, hbody_rel,
    _hbody_none, _source_respects, _target_respects, _hbody_dom,
    hden_P, _hdP_type, hrel_P⟩ :=
    EncodeTermRepTotal.bound_body P_total Xi_fv related wf ThetaBase_none
      source_respects ThetaBase_dom den_P bound_values
  exact collect_ite_truth_of_represented_source_fv
    xs ts Ds hbody_def hcov_body hcov_Dapp hlen_xt hlen_xd hnodup
    hxs_not_bv hts_bv_nil hts_fv_not_bv hts_not_none hts_fv_disj_xs
    hts_den hcov_sub hcov_upd hcov_P hvalues hPenc_fv hctx_source
    hbody_ext hden_P hrel_P hden_D hden_body hD_type hD_true

/-- A fixed Boolean B denotation is equivalent to the extensional truth
form required by the collection retraction lemma.  The latter quantifies over
all dependent-pair presentations of the same `Option B.Dom`; injectivity of
`some` identifies their underlying values. -/
theorem B.denote_bool_true_iff_forall.{u}
    {e : Option B.Dom.{u}} {P : ZFSet.{u}}
    {hP : P ∈ ⟦BType.bool⟧ᶻ}
    (hden : e = some (⟨P, BType.bool, hP⟩ : B.Dom)) :
    P = ZFSet.zftrue ↔
      ∀ (Px : ZFSet.{u}) (P_ty : BType) (hPx : Px ∈ ⟦P_ty⟧ᶻ),
        e = some (⟨Px, P_ty, hPx⟩ : B.Dom) → Px = ZFSet.zftrue := by
  constructor
  · intro htrue Px P_ty hPx hden'
    have heq : (⟨P, BType.bool, hP⟩ : B.Dom) =
        ⟨Px, P_ty, hPx⟩ :=
      Option.some.inj (hden.symm.trans hden')
    have hvalue : P = Px := congrArg PSigma.fst heq
    rw [← hvalue]
    exact htrue
  · intro h
    exact h P BType.bool hP hden
