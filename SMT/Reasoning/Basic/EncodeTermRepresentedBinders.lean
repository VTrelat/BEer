import SMT.Reasoning.EncodeTermRepresentedDefs
import SMT.Reasoning.Basic.AbstractSubstDenote
import SMT.Reasoning.Basic.EncodeTermStruct

open Std.Do B SMT ZFSet

/-!
# Common represented-binder semantic bridges

The encoder implements the bodies of `collect` and `lambda` by substituting
the freshly bound SMT variables into an already encoded body.  This file keeps
the substitution/evaluation transfer independent of the representation chosen
for the surrounding free variables.  The callers supply the corresponding
agreement of renaming contexts; this lemma then combines it with the existing
substitution-denotation theorem.
-/

namespace SMT.RenamingContext

/-- A supported representative of a Boolean has exactly the source truth
value.  Keeping this fact separate avoids repeatedly unpacking the canonical
Boolean cast in binder-body proofs. -/
theorem represented_bool_truth_iff.{u}
    {P Q : ZFSet.{u}} {hP : P ∈ ⟦BType.bool⟧ᶻ}
    {sigma : SMTType} {hQ : Q ∈ ⟦sigma⟧ᶻ}
    (hrel : RDomCastSupported
      (⟨P, BType.bool, hP⟩ : B.Dom)
      (⟨Q, sigma, hQ⟩ : SMT.Dom)) :
    Q = ZFSet.zftrue ↔ P = ZFSet.zftrue := by
  have htype : sigma = SMTType.bool :=
    RDomCast.target_type_eq_bool hrel.toRDomCast
  subst sigma
  have hcanonical := (RDomCast.iff_RDom_of_type_eq (α := BType.bool) rfl).mp
    hrel.toRDomCast
  rw [RDom] at hcanonical
  obtain ⟨_, hret⟩ := hcanonical
  simpa [retract] using congrArg (fun X => X = ZFSet.zftrue) hret

/-- Evaluate a substituted body by evaluating the original body in an
agreement-equivalent context.  This is the common last step in the
representation-aware `collect` and `lambda` body bridges. -/
theorem denote_substList_eq_of_denote_and_agrees.{u}
    (e : SMT.Term) (xs : List SMT.𝒱) (ts : List SMT.Term)
    {Delta Theta : Context.{u}} (Ds : List SMT.Dom.{u})
    (hlen_xt : xs.length = ts.length) (hlen_xd : xs.length = Ds.length)
    (hnodup : xs.Nodup)
    (hxs_not_bv : ∀ x ∈ xs, x ∉ SMT.bv e)
    (hts_bv_nil : ∀ t ∈ ts, SMT.bv t = [])
    (hts_fv_not_bv : ∀ t ∈ ts, ∀ w ∈ SMT.fv t, w ∉ SMT.bv e)
    (hts_not_none : ∀ t ∈ ts, t ≠ SMT.Term.none)
    (hts_fv_disj_xs : ∀ t ∈ ts, ∀ w ∈ SMT.fv t, w ∉ xs)
    (hts_den : ∀ (i : ℕ) (_hi_x : i < xs.length) (hi_t : i < ts.length)
      (hi_d : i < Ds.length),
      ∃ (ht_cov : CoversFV Delta ts[i]),
        ⟦ts[i].abstract Delta ht_cov⟧ˢ = some Ds[i])
    (hcov_sub : CoversFV Delta (SMT.substList xs ts e))
    (hcov_upd : CoversFV
      (Function.updates Delta xs (Ds.map Option.some)) e)
    (hcov_Theta : CoversFV Theta e)
    (hagrees : AgreesOnFV
      (Function.updates Delta xs (Ds.map Option.some)) Theta e)
    {d : SMT.Dom.{u}}
    (hden : ⟦e.abstract Theta hcov_Theta⟧ˢ = some d) :
    ⟦(SMT.substList xs ts e).abstract Delta hcov_sub⟧ˢ = some d := by
  rw [abstract_substList_denote e xs ts Ds hlen_xt hlen_xd hnodup
    hxs_not_bv hts_bv_nil hts_fv_not_bv hts_not_none hts_fv_disj_xs
    hts_den hcov_sub hcov_upd]
  exact (denote_congr_of_agreesOnFV
    (h1 := hcov_upd) (h2 := hcov_Theta) hagrees).trans hden

/-- The preceding substitution bridge specialized to a represented Boolean
body.  It exposes the exact truth-value equivalence consumed by the `ite` and
pair-equality bodies emitted for `collect` and `lambda`. -/
theorem denote_substList_bool_truth_of_agrees.{u}
    (e : SMT.Term) (xs : List SMT.𝒱) (ts : List SMT.Term)
    {Delta Theta : Context.{u}} (Ds : List SMT.Dom.{u})
    (hlen_xt : xs.length = ts.length) (hlen_xd : xs.length = Ds.length)
    (hnodup : xs.Nodup)
    (hxs_not_bv : ∀ x ∈ xs, x ∉ SMT.bv e)
    (hts_bv_nil : ∀ t ∈ ts, SMT.bv t = [])
    (hts_fv_not_bv : ∀ t ∈ ts, ∀ w ∈ SMT.fv t, w ∉ SMT.bv e)
    (hts_not_none : ∀ t ∈ ts, t ≠ SMT.Term.none)
    (hts_fv_disj_xs : ∀ t ∈ ts, ∀ w ∈ SMT.fv t, w ∉ xs)
    (hts_den : ∀ (i : ℕ) (_hi_x : i < xs.length) (hi_t : i < ts.length)
      (hi_d : i < Ds.length),
      ∃ (ht_cov : CoversFV Delta ts[i]),
        ⟦ts[i].abstract Delta ht_cov⟧ˢ = some Ds[i])
    (hcov_sub : CoversFV Delta (SMT.substList xs ts e))
    (hcov_upd : CoversFV
      (Function.updates Delta xs (Ds.map Option.some)) e)
    (hcov_Theta : CoversFV Theta e)
    (hagrees : AgreesOnFV
      (Function.updates Delta xs (Ds.map Option.some)) Theta e)
    {P : ZFSet.{u}} {hP : P ∈ ⟦BType.bool⟧ᶻ}
    {d : SMT.Dom.{u}}
    (hden : ⟦e.abstract Theta hcov_Theta⟧ˢ = some d)
    (hrel : RDomCastSupported
      (⟨P, BType.bool, hP⟩ : B.Dom) d) :
    ⟦(SMT.substList xs ts e).abstract Delta hcov_sub⟧ˢ = some d ∧
      (d.fst = ZFSet.zftrue ↔ P = ZFSet.zftrue) := by
  constructor
  · exact denote_substList_eq_of_denote_and_agrees e xs ts Ds
      hlen_xt hlen_xd hnodup hxs_not_bv hts_bv_nil hts_fv_not_bv
      hts_not_none hts_fv_disj_xs hts_den hcov_sub hcov_upd hcov_Theta
      hagrees hden
  · exact represented_bool_truth_iff hrel

/-- Transfer a substituted body from its evaluation context to an extension
of the body-totality context.  The only free variables contributed by the
replacement terms are the freshly bound variable `z`; all remaining body
variables are inherited through the extension. -/
theorem agreesOnFV_substList_update_of_extends.{u}
    {DeltaCtx ThetaBase ThetaBody : Context.{u}}
    {z : SMT.𝒱} {W : SMT.Dom.{u}}
    {xs : List SMT.𝒱} {ts : List SMT.Term} {body : SMT.Term}
    (hcov : CoversFV (Function.update DeltaCtx z (some W))
      (SMT.substList xs ts body))
    (hsubst_not_xs : ∀ v ∈ SMT.fv (SMT.substList xs ts body),
      v ≠ z → v ∉ xs)
    (hts_fv_z : ∀ t ∈ ts, ∀ v ∈ SMT.fv t, v = z)
    (hctx_base : ∀ v ∈ SMT.fv body, v ∉ xs →
      DeltaCtx v = ThetaBase v)
    (hbody_ext : Extends ThetaBody ThetaBase) :
    AgreesOnFV (Function.update DeltaCtx z (some W))
      (Function.update ThetaBody z (some W))
      (SMT.substList xs ts body) := by
  intro v hv
  by_cases hvz : v = z
  · subst hvz
    simp [Function.update_self]
  · rw [Function.update_of_ne hvz, Function.update_of_ne hvz]
    rcases SMT_mem_fv_substList hv with hvbody | ⟨t, ht, hvt⟩
    · have hvxs : v ∉ xs := hsubst_not_xs v hv hvz
      have hbase : DeltaCtx v = ThetaBase v := hctx_base v hvbody hvxs
      cases hctx : DeltaCtx v with
      | none =>
          have hcontr := hcov v hv
          rw [Function.update_of_ne hvz, hctx] at hcontr
          simp at hcontr
      | some d =>
          have hbase_some : ThetaBase v = some d := hbase.symm.trans hctx
          exact (hbody_ext hbase_some).symm
    · exact (hvz (hts_fv_z t ht v hvt)).elim

/-- Source-level agreement suffices for a stable encoded binder body: the
encoder free-variable bound turns it into the encoded-body agreement needed
by `agreesOnFV_substList_update_of_extends`. -/
theorem agreesOnFV_substList_update_of_source_fv.{u}
    {DeltaCtx ThetaBase ThetaBody : Context.{u}}
    {z : SMT.𝒱} {W : SMT.Dom.{u}}
    {xs : List SMT.𝒱} {ts : List SMT.Term} {body : SMT.Term}
    {source : B.Term}
    (hcov : CoversFV (Function.update DeltaCtx z (some W))
      (SMT.substList xs ts body))
    (hsubst_not_xs : ∀ v ∈ SMT.fv (SMT.substList xs ts body),
      v ≠ z → v ∉ xs)
    (hts_fv_z : ∀ t ∈ ts, ∀ v ∈ SMT.fv t, v = z)
    (hbody_fv : SMT.fv body ⊆ B.Term.vars source)
    (hctx_source : ∀ v ∈ B.Term.vars source, v ∉ xs →
      DeltaCtx v = ThetaBase v)
    (hbody_ext : Extends ThetaBody ThetaBase) :
    AgreesOnFV (Function.update DeltaCtx z (some W))
      (Function.update ThetaBody z (some W))
      (SMT.substList xs ts body) := by
  apply agreesOnFV_substList_update_of_extends hcov hsubst_not_xs hts_fv_z
  · intro v hv hvxs
    exact hctx_source v (hbody_fv hv) hvxs
  · exact hbody_ext

end SMT.RenamingContext

/-- A successful binder-body stability check turns the structural declaration
delta of its encoding into an empty delta.  Consequently the returned term
has no generated-helper free variables. -/
theorem encodeTerm_no_new_declarations_fv
    (E : B.Env) {Lambda : SMT.TypeContext} {t : B.Term} {alpha : B.BType}
    (typ_t : E.context ⊢ᴮ t : alpha)
    {used : List SMT.𝒱}
    (vars_used : ∀ v ∈ t.vars, v ∈ used)
    (Lambda_inv : ∀ v ∈ t.vars, v ∈ Lambda → v ∈ E.context)
    (bv_nodup : (B.bv t).Nodup)
    {n : ℕ} {decl : SMT.Chunk} :
    ⦃ fun (S : EncoderState) ↦
        ⌜S.types = Lambda ∧ S.env.freshvarsc = n ∧
          Lambda.keys ⊆ S.env.usedVars ∧ S.env.usedVars = used ∧
          S.env.declarations = decl⌝ ⦄
    do
      let out ← encodeTerm t E
      SMT.ensureDeclarationsUnchanged decl.length "represented binder body"
      pure out
    ⦃ ⇓? (⟨t', _sigma⟩ : SMT.Term × SMTType) (S' : EncoderState) =>
      ⌜S'.env.declarations = decl ∧ SMT.fv t' ⊆ B.Term.vars t⌝ ⦄ := by
  mstart
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_keys, St_used, St_decl⟩ := pre
  mspec (encodeTerm_decl E typ_t vars_used Lambda_inv bv_nodup
    (n := St.env.freshvarsc) (decl := decl))
  rename_i out
  mrename_i post
  mintro ∀St'
  mpure post
  obtain ⟨Dlt, St'_decl, _spec_fv, term_fv⟩ := post
  mspec (SMT.ensureDeclarationsUnchanged_spec (St := St'))
  mrename_i stable
  mintro ∀St''
  mpure stable
  obtain ⟨rfl, hlen⟩ := stable
  have hDlt : Dlt = [] :=
    declaration_delta_eq_nil_of_length St'_decl hlen
  subst Dlt
  mspec Std.Do.Spec.pure
  mpure_intro
  refine ⟨?_, ?_⟩
  · simpa using St'_decl
  · intro v hv
    simpa only [declVars, List.filterMap_nil, List.mem_union_iff,
      List.not_mem_nil, or_false] using term_fv hv

/-- A lambda whose canonical set retraction is the source value is a supported
representative of that set.  The `collect` and `lambda` cases use this after
their semantic body bridges establish the retraction equation. -/
theorem RDomCastSupported.of_canonical_set_retract.{u}
    {tau : BType} {X : ZFSet.{u}} {hX : X ∈ ⟦BType.set tau⟧ᶻ}
    {d : SMT.Dom.{u}}
    (htype : d.snd.fst = (BType.set tau).toSMTType)
    (hretract : retract (BType.set tau) d.fst = X) :
    RDomCastSupported (⟨X, BType.set tau, hX⟩ : B.Dom) d := by
  apply RDom.toRDomCastSupported
  rw [RDom]
  exact ⟨htype, hretract⟩
