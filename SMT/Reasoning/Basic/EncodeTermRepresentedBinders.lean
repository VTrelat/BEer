import SMT.Reasoning.EncodeTermRepresentedDefs
import SMT.Reasoning.Basic.AbstractSubstDenote

open B SMT ZFSet

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

end SMT.RenamingContext
