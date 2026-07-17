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
