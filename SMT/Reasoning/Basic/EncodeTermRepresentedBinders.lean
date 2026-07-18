import SMT.Reasoning.EncodeTermRepresentedDefs
import SMT.Reasoning.Basic.AbstractSubstDenote
import SMT.Reasoning.Basic.EncodeTermStruct
import SMT.Reasoning.Basic.DenotationTotality

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

/-- A body typed after adding one binder denotes for every well-typed bound
value, and every such denotation has the body's declared result type.

Binder encoders repeatedly need these two facts for a context of the form
`Function.update Θ z (some W)`.  Compatibility is required only on the
body's actual free variables, which is exactly what a constructor proof can
recover from the typing data of its encoded subterms. -/
theorem denote_update_total_and_type_of_typing.{u}
    {Theta : Context.{u}} {Gamma : SMT.TypeContext}
    {z : SMT.𝒱} {sigma : SMTType} {body : SMT.Term} {result : SMTType}
    (typ_body : Gamma.insert z sigma ⊢ˢ body : result)
    (Theta_wt : ∀ v ∈ SMT.fv body, ∀ d : SMT.Dom.{u}, Theta v = some d →
      ∀ tau, Gamma.lookup v = some tau → d.snd.fst = tau)
    (hcov : ∀ W : SMT.Dom.{u},
      CoversFV (Function.update Theta z (some W)) body) :
    (∀ W : SMT.Dom.{u}, W.snd.fst = sigma →
      ⟦body.abstract (Function.update Theta z (some W))
        (hcov W)⟧ˢ.isSome = true) ∧
    (∀ W : SMT.Dom.{u}, W.snd.fst = sigma → ∀ d : SMT.Dom.{u},
      ⟦body.abstract (Function.update Theta z (some W))
        (hcov W)⟧ˢ = some d → d.snd.fst = result) := by
  have respects_update : ∀ W : SMT.Dom.{u}, W.snd.fst = sigma →
      RespectsTypeContextOnFV (Function.update Theta z (some W))
        (Gamma.insert z sigma) body := by
    intro W hW_type v tau hv hlookup
    by_cases hvz : v = z
    · subst hvz
      rw [AList.lookup_insert] at hlookup
      cases hlookup
      exact ⟨W, Function.update_self _ _ _, hW_type⟩
    · rw [AList.lookup_insert_ne hvz] at hlookup
      have hsome : (Theta v).isSome = true := by
        have hcovered := hcov W v hv
        rwa [Function.update_of_ne hvz] at hcovered
      obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hsome
      refine ⟨d, ?_, Theta_wt v hv d hd tau hlookup⟩
      rw [Function.update_of_ne hvz]
      exact hd
  constructor
  · intro W hW_type
    have respects : RespectsTypeContextOnFV
        (Function.update Theta z (some W)) (Gamma.insert z sigma) body :=
      respects_update W hW_type
    obtain ⟨d, hden, _⟩ := denote_exists_of_typing_fv typ_body respects
      (hcov W)
    exact Option.isSome_iff_exists.mpr ⟨d, hden⟩
  · intro W hW_type d hden
    have respects : RespectsTypeContextOnFV
        (Function.update Theta z (some W)) (Gamma.insert z sigma) body :=
      respects_update W hW_type
    exact denote_type_of_typing_fv typ_body respects (hcov W) hden

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

/-- The Boolean substitution bridge when only the final replacement payload
may carry binders.  It delegates the capture argument to the representation
independent drop-last substitution theorem. -/
theorem denote_substList_dropLast_bool_truth_of_agrees.{u}
    (e : SMT.Term) (xs : List SMT.𝒱) (ts : List SMT.Term)
    {Delta Theta : Context.{u}} (Ds : List SMT.Dom.{u})
    (hxs : xs ≠ []) (hts : ts ≠ []) (hDs : Ds ≠ [])
    (hlen_xt : xs.length = ts.length) (hlen_xd : xs.length = Ds.length)
    (hnodup : xs.Nodup)
    (hxs_not_bv : ∀ y ∈ xs, y ∉ SMT.bv e)
    (hts_prefix_bv_nil : ∀ q ∈ ts.dropLast, SMT.bv q = [])
    (hts_prefix_fv_not_bv : ∀ q ∈ ts.dropLast,
      ∀ w ∈ SMT.fv q, w ∉ SMT.bv e)
    (ht_last_fv_not_bv : ∀ w ∈ SMT.fv (ts.getLast hts), w ∉ SMT.bv e)
    (hts_prefix_not_none : ∀ q ∈ ts.dropLast, q ≠ SMT.Term.none)
    (ht_last_not_none : ts.getLast hts ≠ SMT.Term.none)
    (hts_prefix_fv_disj : ∀ q ∈ ts.dropLast,
      ∀ w ∈ SMT.fv q, w ∉ xs)
    (ht_last_fv_disj : ∀ w ∈ SMT.fv (ts.getLast hts), w ∉ xs)
    (hts_den : ∀ (i : ℕ) (hi_x : i < xs.length) (hi_t : i < ts.length)
      (hi_d : i < Ds.length),
      ∃ hcov : CoversFV Delta ts[i],
        ⟦ts[i].abstract Delta hcov⟧ˢ = some Ds[i])
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
  · rw [abstract_substList_dropLast_denote e xs ts Ds hxs hts hDs
      hlen_xt hlen_xd hnodup hxs_not_bv hts_prefix_bv_nil
      hts_prefix_fv_not_bv ht_last_fv_not_bv hts_prefix_not_none
      ht_last_not_none hts_prefix_fv_disj ht_last_fv_disj hts_den
      hcov_sub hcov_upd]
    exact (denote_congr_of_agreesOnFV
      (h1 := hcov_upd) (h2 := hcov_Theta) hagrees).trans hden
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

/-- A substitution update agrees with a body context at every bound variable
when that context already holds the corresponding substituted denotation. -/
theorem updates_eq_of_bound_denotations.{u}
    {Delta Theta : Context.{u}} {xs : List SMT.𝒱} {Ds : List SMT.Dom.{u}}
    (hlen : xs.length = Ds.length) (hnodup : xs.Nodup)
    (hvalues : ∀ (i : ℕ) (hi_x : i < xs.length) (hi_d : i < Ds.length),
      Theta xs[i] = some Ds[i])
    (v : SMT.𝒱) (hv : v ∈ xs) :
    Function.updates Delta xs (Ds.map Option.some) v = Theta v := by
  rw [Function.updates_eq_if (by simp [hlen]) hnodup, dif_pos hv]
  have hi_x : xs.idxOf v < xs.length := List.idxOf_lt_length_of_mem hv
  have hi_d : xs.idxOf v < Ds.length := by
    rw [← hlen]
    exact hi_x
  rw [List.getElem_map]
  calc
    some Ds[xs.idxOf v] = Theta xs[xs.idxOf v] :=
      (hvalues (xs.idxOf v) hi_x hi_d).symm
    _ = Theta v := by rw [List.getElem_idxOf hi_x]

/-- The substitution context agrees with the body-totality context on a
stable encoded body.  At binder variables this uses the chosen denotations;
away from binders it uses source-level agreement and extension. -/
theorem agreesOnFV_updates_of_source_fv.{u}
    {Delta ThetaBase ThetaBody : Context.{u}}
    {xs : List SMT.𝒱} {Ds : List SMT.Dom.{u}} {body : SMT.Term}
    {source : B.Term}
    (hlen : xs.length = Ds.length) (hnodup : xs.Nodup)
    (hcov : CoversFV (Function.updates Delta xs (Ds.map Option.some)) body)
    (hvalues : ∀ (i : ℕ) (hi_x : i < xs.length) (hi_d : i < Ds.length),
      ThetaBody xs[i] = some Ds[i])
    (hbody_fv : SMT.fv body ⊆ B.Term.vars source)
    (hctx_source : ∀ v ∈ B.Term.vars source, v ∉ xs →
      Delta v = ThetaBase v)
    (hbody_ext : Extends ThetaBody ThetaBase) :
    AgreesOnFV (Function.updates Delta xs (Ds.map Option.some))
      ThetaBody body := by
  intro v hv
  by_cases hvxs : v ∈ xs
  · exact updates_eq_of_bound_denotations hlen hnodup hvalues v hvxs
  · rw [Function.updates_of_not_mem _ xs _ v hvxs]
    have hbase : Delta v = ThetaBase v :=
      hctx_source v (hbody_fv hv) hvxs
    cases hDelta : Delta v with
    | none =>
        have hcontr := hcov v hv
        rw [Function.updates_of_not_mem _ xs _ v hvxs, hDelta] at hcontr
        simp at hcontr
    | some d =>
        have hThetaBase : ThetaBase v = some d := hbase.symm.trans hDelta
        exact (hbody_ext hThetaBase).symm

end SMT.RenamingContext

/-- Updating a target valuation at names already recorded as used preserves
its outside-support invariant.  Binder encoders use this when they install
arbitrary semantic values for their locally bound variables. -/
theorem SMT.RenamingContext.updates_none_of_mem_used.{u}
    {Theta : SMT.RenamingContext.Context.{u}} {vs : List SMT.𝒱}
    {ss : Fin vs.length -> SMT.Dom.{u}} {used : List SMT.𝒱}
    (vs_used : ∀ v ∈ vs, v ∈ used)
    (Theta_none : ∀ v ∉ used, Theta v = none) :
    ∀ v ∉ used,
      Function.updates Theta vs ((List.ofFn ss).map Option.some) v = none := by
  intro v hv
  have hv_vs : v ∉ vs := by
    intro hvs
    exact hv (vs_used v hvs)
  rw [Function.updates_of_not_mem Theta vs _ v hv_vs]
  exact Theta_none v hv

/-- Updating a target valuation at entries whose types occur in a target
context keeps every assigned variable inside that context. -/
theorem SMT.RenamingContext.updates_dom_of_typed_bounds.{u}
    {Theta : SMT.RenamingContext.Context.{u}} {Gamma : SMT.TypeContext}
    {vs : List SMT.𝒱} {ss : Fin vs.length -> SMT.Dom.{u}}
    (base_dom : ∀ v, Theta v ≠ none -> v ∈ Gamma)
    (bound_type : ∀ i, Gamma.lookup vs[i] = some (ss i).snd.fst) :
    ∀ v,
      Function.updates Theta vs ((List.ofFn ss).map Option.some) v ≠ none ->
        v ∈ Gamma := by
  intro v hv
  by_cases hvs : v ∈ vs
  · let i : Fin vs.length := ⟨vs.idxOf v, List.idxOf_lt_length_of_mem hvs⟩
    have hvi : vs[i] = v := List.getElem_idxOf i.isLt
    apply AList.lookup_isSome.mp
    apply Option.isSome_of_eq_some
    have hbound := bound_type i
    rw [hvi] at hbound
    exact hbound
  · rw [Function.updates_of_not_mem Theta vs _ v hvs] at hv
    exact base_dom v hv

/-- A typed update supplies the B-side free-variable compatibility required
by a body encoder.  Outside the local binder list it delegates to the ambient
compatibility witness. -/
theorem B.RenamingContext.RespectsTypeContextOnFV.updates_of_typed_bounds.{u}
    {Theta : SMT.RenamingContext.Context.{u}} {Gamma : SMT.TypeContext}
    {vs : List SMT.𝒱} (vs_nodup : vs.Nodup)
    {ss : Fin vs.length -> SMT.Dom.{u}} {P : B.Term}
    (ambient : ∀ v ∈ B.fv P, v ∉ vs -> ∀ tau,
      Gamma.lookup v = some tau ->
      ∃ d : SMT.Dom.{u}, Theta v = some d ∧ d.snd.fst = tau)
    (bound_type : ∀ i, Gamma.lookup vs[i] = some (ss i).snd.fst) :
    B.RenamingContext.RespectsTypeContextOnFV
      (Function.updates Theta vs ((List.ofFn ss).map Option.some)) Gamma P := by
  intro v tau hv hlookup
  by_cases hvs : v ∈ vs
  · let i : Fin vs.length := ⟨vs.idxOf v, List.idxOf_lt_length_of_mem hvs⟩
    have hvi : vs[i] = v := List.getElem_idxOf i.isLt
    refine ⟨ss i, ?_, ?_⟩
    · rw [Function.updates_eq_if (by simp) vs_nodup, dif_pos hvs]
      simp only [List.getElem_map, List.getElem_ofFn]
      congr 1
    · have hbound : Gamma.lookup v = some (ss i).snd.fst := by
        have hbound := bound_type i
        rw [hvi] at hbound
        exact hbound
      exact Option.some.inj (hbound.symm.trans hlookup)
  · obtain ⟨d, hd, htype⟩ := ambient v hv hvs tau hlookup
    refine ⟨d, ?_, htype⟩
    rw [Function.updates_of_not_mem Theta vs _ v hvs]
    exact hd

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

open Classical B in
/-- Decompose a supported relation between source and SMT tuples into the
pointwise relation needed by a represented binder body.  Both sides are
obtained by projecting one whole tuple, so this bridge is independent of the
particular binder constructor. -/
theorem RValuationCastSupportedOnFV.updates_of_reduce_toProdl.{u}
    {Ξ : B.RenamingContext.Context.{u}}
    {Θ : SMT.RenamingContext.Context.{u}}
    {vs : List B.𝒱} (vs_nodup : vs.Nodup)
    {αs : List BType} (αs_nemp : αs ≠ [])
    {σs : List SMTType}
    (vs_αs_len : vs.length = αs.length)
    (αs_σs_len : αs.length = σs.length)
    {X Y : ZFSet.{u}}
    (hX : X ∈ ⟦αs.reduce (· ×ᴮ ·) αs_nemp⟧ᶻ)
    (hY : Y ∈ ⟦σs.toProdl⟧ᶻ)
    (hrel : RDomCastSupported
      (⟨X, αs.reduce (· ×ᴮ ·) αs_nemp, hX⟩ : B.Dom)
      (⟨Y, σs.toProdl, hY⟩ : SMT.Dom))
    {t : B.Term}
    (ambient : ∀ v ∈ B.fv t, v ∉ vs →
      match Ξ v, Θ v with
      | some d, some d' => RDomCastSupported d d'
      | _, _ => False) :
    let bs : Fin vs.length → B.Dom.{u} := fun i =>
      let j : Fin αs.length := Fin.cast vs_αs_len i
      ⟨X.get αs.length j, αs[j],
        BType.mem_get_of_mem_reduce_toZFSet αs_nemp hX⟩
    let ss : Fin vs.length → SMT.Dom.{u} := fun i =>
      let j : Fin σs.length := Fin.cast (vs_αs_len.trans αs_σs_len) i
      ⟨Y.get σs.length j, σs[j],
        SMTType.mem_get_of_mem_toProdl
          (fun hs => αs_nemp (List.length_eq_zero_iff.mp
            (αs_σs_len.trans (by simp [hs])))) hY⟩
    RValuationCastSupportedOnFV
      (Function.updates Ξ vs (List.ofFn fun i => some (bs i)))
      (Function.updates Θ vs (List.ofFn fun i => some (ss i))) t := by
  dsimp only
  apply RValuationCastSupportedOnFV.updates vs_nodup
  · exact ambient
  · intro i
    simpa using RDomCastSupported.get_of_reduce_toProdl
      αs_nemp αs_σs_len hX hY hrel (Fin.cast vs_αs_len i)

/-- Run a Boolean body totality theorem at a binder-specific base valuation.
The result extends that base valuation, so any explicitly installed bound
values survive into the valuation used to denote the encoded body. -/
theorem EncodeTermRepTotal.bound_body.{u}
    {P : B.Term} {E : B.Env} {Lambda Gamma : SMT.TypeContext}
    {Penc : SMT.Term} {sigma : SMTType} {used : List SMT.𝒱}
    (P_total : EncodeTermRepTotal.{u}
      P E BType.bool Lambda Penc sigma Gamma used)
    {Xi : B.RenamingContext.Context.{u}}
    (Xi_fv : ∀ v ∈ B.fv P, (Xi v).isSome = true)
    {ThetaBase : SMT.RenamingContext.Context.{u}}
    (related : RValuationCastSupportedOnFV Xi ThetaBase P)
    (wf : B.RenWF E.context Xi)
    (ThetaBase_none : ∀ v ∉ used, ThetaBase v = none)
    (source_respects : B.RenamingContext.RespectsTypeContextOnFV
      ThetaBase Lambda P)
    (ThetaBase_dom : ∀ v, ThetaBase v ≠ none → v ∈ Lambda)
    {Pval : ZFSet.{u}} {hPval : Pval ∈ ⟦BType.bool⟧ᶻ}
    (den_P : ⟦P.abstract Xi Xi_fv⟧ᴮ =
      some (⟨Pval, BType.bool, hPval⟩ : B.Dom))
    {xs : List SMT.𝒱} {Ds : List SMT.Dom.{u}}
    (bound_values : ∀ (i : ℕ) (hi_x : i < xs.length) (hi_d : i < Ds.length),
      ThetaBase xs[i] = some Ds[i]) :
    ∃ (ThetaBody : SMT.RenamingContext.Context.{u})
      (hcov : SMT.RenamingContext.CoversFV ThetaBody Penc)
      (dP : SMT.Dom.{u}),
      SMT.RenamingContext.Extends ThetaBody ThetaBase ∧
      (∀ (i : ℕ) (hi_x : i < xs.length) (hi_d : i < Ds.length),
        ThetaBody xs[i] = some Ds[i]) ∧
      RValuationCastSupportedOnFV Xi ThetaBody P ∧
      (∀ v ∉ used, ThetaBody v = none) ∧
      B.RenamingContext.RespectsTypeContextOnFV ThetaBody Gamma P ∧
      SMT.RenamingContext.RespectsTypeContextOnFV ThetaBody Gamma Penc ∧
      (∀ v, ThetaBody v ≠ none → v ∈ Gamma) ∧
      ⟦Penc.abstract ThetaBody hcov⟧ˢ = some dP ∧
      dP.snd.fst = sigma ∧
      RDomCastSupported (⟨Pval, BType.bool, hPval⟩ : B.Dom) dP := by
  obtain ⟨ThetaBody, hcov, dP, hbody_ext, hbody_rel, hbody_none,
    hsource, htarget, hbody_dom, hden, htype, hrel⟩ :=
    P_total Xi Xi_fv ThetaBase related wf ThetaBase_none source_respects
      ThetaBase_dom Pval hPval den_P
  refine ⟨ThetaBody, hcov, dP, hbody_ext, ?_, hbody_rel, hbody_none,
    hsource, htarget, hbody_dom, hden, htype, hrel⟩
  intro i hi_x hi_d
  exact hbody_ext (bound_values i hi_x hi_d)
