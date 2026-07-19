import SMT.Reasoning.ProofObligationRepresented

/-!
# Representation-aware functional-union proof obligation

This file instantiates the represented quantified-term theorem for the shape
emitted by the functional-union regression: every pair in `f ∪ g` belongs to
`X × Y`.  It also connects the proof-obligation assumptions that justify a
functional representation to the selected source-to-target valuation.
-/

open B SMT Batteries Std.Do

namespace B.Term

def functionalUnionSubset
    (z f g X Y : B.𝒱) : B.Term :=
  .all [z]
    (.union (.var f) (.var g))
    (.mem (.var z) (.cprod (.var X) (.var Y)))

end B.Term

namespace B.ProofObligation

/-- Typed, true function hypotheses for a proof obligation construct the
represented target valuation needed by the concrete functional-union term.
Only assigned flagged values require a function hypothesis; decoder-local
bound helper flags do not enter the term's free-variable valuation. -/
theorem exists_selectedValuation_for_functionalUnionSubset.{u}
    (po : B.ProofObligation) (goal : B.SimpleGoal)
    (E : B.Env) {Gamma : SMT.TypeContext}
    {Xi : B.RenamingContext.Context.{u}}
    (z f g X Y : B.𝒱)
    (representation : E.RepresentationContext Gamma)
    (covers : E.AssignedFlagsHaveFunctionHypotheses Xi
      (po.assumptionsFor goal))
    (typed : E.AssumptionsTyped (po.assumptionsFor goal))
    (holds : B.Env.AssumptionsHold Xi (po.assumptionsFor goal))
    (source_covers : ∀ v ∈ B.fv
      (B.Term.functionalUnionSubset z f g X Y),
      (Xi v).isSome = true)
    (source_wf : B.RenWF E.context Xi)
    (fv_context : ∀ v ∈ B.fv
      (B.Term.functionalUnionSubset z f g X Y), v ∈ E.context) :
    ∃ Theta : SMT.RenamingContext.Context.{u},
      RValuationCastSupportedOnFV Xi Theta
        (B.Term.functionalUnionSubset z f g X Y) ∧
      B.RenamingContext.RespectsTypeContextOnFV Theta Gamma
        (B.Term.functionalUnionSubset z f g X Y) ∧
      (∀ v ∉ B.fv (B.Term.functionalUnionSubset z f g X Y),
        Theta v = none) ∧
      ∀ v, Theta v ≠ none → v ∈ Gamma := by
  exact E.exists_selectedValuation_for_term representation source_covers
    source_wf
    (B.ProofObligation.flaggedValuesFunctional_of_assumptions
      (po := po) (goal := goal) covers typed holds source_wf)
    fv_context

end B.ProofObligation

private theorem unionVars_rep_ih.{u} (f g : B.𝒱) :
    EncodeTermRepIH.{u} (.union (.var f) (.var g)) ∧
    EncodeTermRepScopedFromIH.{u} (.union (.var f) (.var g)) := by
  let f_ordinary : EncodeTermRepIH.{u} (.var f) :=
    encodeTerm_rep_spec.var_case f
  let g_ordinary : EncodeTermRepIH.{u} (.var g) :=
    encodeTerm_rep_spec.var_case g
  let f_scoped : EncodeTermRepScopedFromIH.{u} (.var f) :=
    encodeTerm_rep_scoped.var_case_from f
  let g_scoped : EncodeTermRepScopedFromIH.{u} (.var g) :=
    encodeTerm_rep_scoped.var_case_from g
  exact ⟨encodeTerm_rep_spec.union_case (.var f) (.var g)
      f_ordinary g_ordinary,
    EncodeTermRepresentedScopedUnion.encodeTerm_rep_scoped.union_case_from
      (.var f) (.var g) f_ordinary g_ordinary f_scoped g_scoped⟩

private theorem memCprodVars_rep_ih.{u} (z X Y : B.𝒱) :
    EncodeTermRepIH.{u}
      (.mem (.var z) (.cprod (.var X) (.var Y))) ∧
    EncodeTermRepScopedBoolFromIH.{u}
      (.mem (.var z) (.cprod (.var X) (.var Y))) := by
  let z_ordinary : EncodeTermRepIH.{u} (.var z) :=
    encodeTerm_rep_spec.var_case z
  let X_ordinary : EncodeTermRepIH.{u} (.var X) :=
    encodeTerm_rep_spec.var_case X
  let Y_ordinary : EncodeTermRepIH.{u} (.var Y) :=
    encodeTerm_rep_spec.var_case Y
  let z_scoped : EncodeTermRepScopedFromIH.{u} (.var z) :=
    encodeTerm_rep_scoped.var_case_from z
  let X_scoped : EncodeTermRepScopedFromIH.{u} (.var X) :=
    encodeTerm_rep_scoped.var_case_from X
  let Y_scoped : EncodeTermRepScopedFromIH.{u} (.var Y) :=
    encodeTerm_rep_scoped.var_case_from Y
  let XY_ordinary : EncodeTermRepIH.{u}
      (.cprod (.var X) (.var Y)) :=
    encodeTerm_rep_spec.cprod_case (.var X) (.var Y)
      X_ordinary Y_ordinary
  let XY_scoped : EncodeTermRepScopedFromIH.{u}
      (.cprod (.var X) (.var Y)) :=
    encodeTerm_rep_scoped.cprod_case_from (.var X) (.var Y)
      X_ordinary Y_ordinary X_scoped Y_scoped
  exact ⟨encodeTerm_rep_spec.mem_case (.var z)
      (.cprod (.var X) (.var Y)) z_ordinary XY_ordinary,
    encodeTerm_rep_scoped.mem_case_from (.var z)
      (.cprod (.var X) (.var Y)) z_ordinary XY_ordinary
      z_scoped XY_scoped⟩

/-- Ordinary and scoped represented induction hypotheses for the domain and
predicate of `B.Term.functionalUnionSubset`. -/
theorem functionalUnionSubset_rep_components.{u}
    (z f g X Y : B.𝒱) :
    EncodeTermRepIH.{u} (.union (.var f) (.var g)) ∧
    EncodeTermRepScopedIH.{u} (.union (.var f) (.var g)) ∧
    EncodeTermRepIH.{u}
      (.mem (.var z) (.cprod (.var X) (.var Y))) ∧
    EncodeTermRepScopedBoolFromIH.{u}
      (.mem (.var z) (.cprod (.var X) (.var Y))) := by
  obtain ⟨D_ordinary, D_scoped⟩ := unionVars_rep_ih f g
  obtain ⟨P_ordinary, P_scoped⟩ := memCprodVars_rep_ih z X Y
  exact ⟨D_ordinary, D_scoped.to_root,
    P_ordinary, P_scoped⟩

/-- Concrete represented soundness for the functional-union quantifier.  The
term-local premise `z ∉ E.flags` selects the honest unflagged-binder branch. -/
theorem encodeTerm_rep_spec.functionalUnionSubset_case.{u}
    (z f g X Y : B.𝒱)
    (wd_P : B.Term.WellDefined.{u}
      (.mem (.var z) (.cprod (.var X) (.var Y))))
    (E : B.Env) (z_unflagged : z ∉ E.flags)
    {Lambda : SMT.TypeContext} {alpha : BType}
    (typ_t : E.context ⊢ᴮ
      B.Term.functionalUnionSubset z f g X Y : alpha)
    {Xi : B.RenamingContext.Context.{u}}
    (Xi_fv : ∀ v ∈ B.fv
      (B.Term.functionalUnionSubset z f g X Y),
      (Xi v).isSome = true)
    {Theta0 : SMT.RenamingContext.Context.{u}}
    (related : RValuationCastSupportedOnFV Xi Theta0
      (B.Term.functionalUnionSubset z f g X Y))
    {used : List SMT.𝒱}
    (Theta0_none : ∀ v ∉ used, Theta0 v = none)
    (Theta0_dom : ∀ v, Theta0 v ≠ none → v ∈ Lambda)
    {T : ZFSet.{u}} {hT : T ∈ ⟦alpha⟧ᶻ}
    (den_t : ⟦(B.Term.functionalUnionSubset z f g X Y).abstract
      Xi Xi_fv⟧ᴮ = some ⟨T, ⟨alpha, hT⟩⟩)
    (vars_used : ∀ v ∈
      (B.Term.functionalUnionSubset z f g X Y).vars, v ∈ used)
    (Lambda_inv : ∀ v ∈
      (B.Term.functionalUnionSubset z f g X Y).vars,
      v ∈ Lambda → v ∈ E.context)
    (bv_nodup :
      (B.bv (B.Term.functionalUnionSubset z f g X Y)).Nodup)
    (respects : B.RenamingContext.RespectsTypeContextOnFV Theta0 Lambda
      (B.Term.functionalUnionSubset z f g X Y))
    (fv_in_Lambda : ∀ v ∈ B.fv
      (B.Term.functionalUnionSubset z f g X Y), v ∈ Lambda)
    (wf : B.RenWF E.context Xi)
    {n : ℕ} {decl : SMT.Chunk} :
    ⦃fun ⟨E0, Lambda'⟩ ↦
      ⌜Lambda' = Lambda ∧ E0.freshvarsc = n ∧
        Lambda.keys ⊆ E0.usedVars ∧ E0.usedVars = used ∧
        E0.declarations = decl⌝⦄
    encodeTerm (B.Term.functionalUnionSubset z f g X Y) E
    ⦃⇓? (⟨t', sigma⟩ : SMT.Term × SMTType) ⟨E', Gamma'⟩ =>
      ⌜EncodeTermRepPost (B.Term.functionalUnionSubset z f g X Y)
          alpha Lambda Xi Theta0 used T hT E t' sigma E' Gamma' ∧
        EncodeTermRepScopedPost.{u}
          (B.Term.functionalUnionSubset z f g X Y)
          E alpha Lambda decl t' sigma E' Gamma'⌝⦄ := by
  obtain ⟨D_ih, D_scoped, P_ih, P_scoped⟩ :=
    functionalUnionSubset_rep_components z f g X Y
  simpa only [B.Term.functionalUnionSubset] using
    (encodeTerm_rep_spec.all_case_and_scoped_of_oracle_or_unflagged
      [z] (.union (.var f) (.var g))
      (.mem (.var z) (.cprod (.var X) (.var Y)))
      D_ih D_scoped P_ih P_scoped wd_P E
      (.inr (by simpa using z_unflagged)) typ_t Xi_fv related
      Theta0_none Theta0_dom den_t vars_used Lambda_inv bv_nodup
      respects fv_in_Lambda wf (n := n) (decl := decl))
