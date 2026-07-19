import SMT.Reasoning.EncodeTermRepresented
import SMT.Reasoning.Basic.StateSpecs

/-!
# Representation-aware proof-obligation bridge

This file connects the representation-aware term theorem to the type context
selected by the top-level encoder.  The raw term theorem permits any supported
SMT representation.  At proof-obligation level the choice is deterministic:
ordinary identifiers use their canonical SMT type, while identifiers marked
as functional relations use an option-valued function type.
-/

open B SMT Batteries Std.Do

namespace BType

/-- The SMT type selected by `encodeTypeContext` for one B binding.

The result is partial because a flag is meaningful only for a binary relation.
This partiality mirrors the encoder's exception branch exactly. -/
def selectedSMTType? (flagged : Bool) (tau : BType) : Option SMTType :=
  if flagged then
    match tau with
    | .set (.prod alpha beta) =>
        some (.fun alpha.toSMTType (.option beta.toSMTType))
    | _ => none
  else
    some tau.toSMTType

@[simp]
theorem selectedSMTType?_false (tau : BType) :
    selectedSMTType? false tau = some tau.toSMTType := by
  rfl

@[simp]
theorem selectedSMTType?_true_set_prod (alpha beta : BType) :
    selectedSMTType? true (.set (.prod alpha beta)) =
      some (.fun alpha.toSMTType (.option beta.toSMTType)) := by
  rfl

/-- Every type successfully selected by the top-level encoder belongs to the
representation grammar consumed by `encodeTerm_rep_spec`. -/
theorem SupportedSMT.of_selectedSMTType?
    {flagged : Bool} {tau : BType} {sigma : SMTType}
    (h : selectedSMTType? flagged tau = some sigma) :
    BType.SupportedSMT tau sigma := by
  cases flagged with
  | false =>
      simp only [selectedSMTType?, Bool.false_eq_true, if_false,
        Option.some.injEq] at h
      subst sigma
      exact BType.SupportedSMT.canonical tau
  | true =>
      simp only [selectedSMTType?, if_true] at h
      cases tau with
      | int => contradiction
      | bool => contradiction
      | prod => contradiction
      | set gamma =>
          cases gamma with
          | int => contradiction
          | bool => contradiction
          | set => contradiction
          | prod alpha beta =>
              simp only [Option.some.injEq] at h
              subst sigma
              exact .optionFun alpha beta

end BType

namespace B.Dom

/-- A source value may use the option-function representation exactly when it
is a functional binary relation.  This is semantic evidence about the value;
membership of its variable name in `B.Env.flags` is deliberately not enough. -/
def IsFunctional (d : B.Dom) : Prop :=
  match d with
  | ⟨X, BType.set (BType.prod alpha beta), _⟩ =>
      X.IsPFunc ⟦alpha⟧ᶻ ⟦beta⟧ᶻ
  | _ => False

/-- Every source value has a supported representative at the SMT type selected
by `encodeTypeContext`, provided a flagged value carries genuine functionhood
evidence.  The flagged branch constructs the option function by collapsing
the canonical graph; the inverse graph theorem proves representation
agreement without changing the source value. -/
theorem exists_selectedSMT_supported.{u}
    {d : B.Dom.{u}} {flagged : Bool} {sigma : SMTType}
    (hselected : BType.selectedSMTType? flagged d.snd.fst = some sigma)
    (hfunctional : flagged = true → d.IsFunctional) :
    ∃ d' : SMT.Dom.{u}, d'.snd.fst = sigma ∧
      RDomCastSupported d d' := by
  cases flagged with
  | false =>
      simp only [BType.selectedSMTType?_false, Option.some.injEq] at hselected
      subst sigma
      exact ⟨d.canonicalSMT, d.canonicalSMT_type,
        d.rdomCastSupported_canonicalSMT⟩
  | true =>
      rcases d with ⟨X, tau, hX⟩
      simp only [BType.selectedSMTType?, if_true] at hselected
      cases tau with
      | int => contradiction
      | bool => contradiction
      | prod => contradiction
      | set gamma =>
          cases gamma with
          | int => contradiction
          | bool => contradiction
          | set => contradiction
          | prod alpha beta =>
              simp only [Option.some.injEq] at hselected
              subst sigma
              have hsourcefun : X.IsPFunc ⟦alpha⟧ᶻ ⟦beta⟧ᶻ := by
                simpa [B.Dom.IsFunctional] using hfunctional rfl
              let d : B.Dom.{u} :=
                ⟨X, BType.set (BType.prod alpha beta), hX⟩
              have hcanrel : RDomCastSupported d d.canonicalSMT :=
                d.rdomCastSupported_canonicalSMT
              have htargetfun :
                  (predGraph alpha.toSMTType beta.toSMTType
                    d.canonicalSMT.fst).IsPFunc
                    ⟦alpha.toSMTType⟧ᶻ ⟦beta.toSMTType⟧ᶻ :=
                RDomCastSupported.setPred_isPFunc_of_source hcanrel hsourcefun
              have hcanonical := d.rdom_canonicalSMT
              rw [RDom] at hcanonical
              refine ⟨⟨graphCollapse alpha.toSMTType beta.toSMTType
                  d.canonicalSMT.fst,
                SMTType.fun alpha.toSMTType
                  (SMTType.option beta.toSMTType),
                graphCollapse_mem alpha.toSMTType beta.toSMTType
                  d.canonicalSMT.fst⟩, rfl, ?_⟩
              exact RDomCastSupported.functionalGraph_as_optionFunction
                alpha beta hX d.canonicalSMT.snd.snd htargetfun hcanonical.2

end B.Dom

namespace B.Env

/-- Pointwise representation context built from a B environment.

Using source entries rather than only key sets retains the dependent B type
needed to construct related valuations later.  Requiring an explicit selected
target type also records that every flagged entry was accepted by the encoder.
-/
def RepresentationContext (E : B.Env) (Gamma : SMT.TypeContext) : Prop :=
  forall (v : B.𝒱) (tau : BType),
    (Sigma.mk v tau) ∈ E.context.entries ->
      exists sigma, BType.selectedSMTType? (v ∈ E.flags) tau = some sigma /\
        Gamma.lookup v = some sigma

theorem RepresentationContext.supported
    {E : B.Env} {Gamma : SMT.TypeContext}
    (h : E.RepresentationContext Gamma)
    {v : B.𝒱} {tau : BType}
    (hv : (Sigma.mk v tau) ∈ E.context.entries) :
    exists sigma, Gamma.lookup v = some sigma /\
      BType.SupportedSMT tau sigma := by
  obtain ⟨sigma, hselected, hlookup⟩ := h v tau hv
  exact ⟨sigma, hlookup,
    BType.SupportedSMT.of_selectedSMTType? hselected⟩

theorem RepresentationContext.of_lookup
    {E : B.Env} {Gamma : SMT.TypeContext}
    (h : E.RepresentationContext Gamma)
    {v : B.𝒱} {tau : BType}
    (hv : E.context.lookup v = some tau) :
    exists sigma, BType.selectedSMTType? (v ∈ E.flags) tau = some sigma /\
      Gamma.lookup v = some sigma := by
  apply h v tau
  exact AList.mem_lookup_iff.mp hv

/-- Unflagged bindings retain the canonical SMT type. -/
theorem RepresentationContext.lookup_unflagged
    {E : B.Env} {Gamma : SMT.TypeContext}
    (h : E.RepresentationContext Gamma)
    {v : B.𝒱} {tau : BType}
    (hv : E.context.lookup v = some tau)
    (hflag : v ∉ E.flags) :
    Gamma.lookup v = some tau.toSMTType := by
  obtain ⟨sigma, hselected, hlookup⟩ := h.of_lookup hv
  simp [BType.selectedSMTType?, hflag] at hselected
  subst sigma
  exact hlookup

/-- Flagged binary relations receive the option-valued function type emitted
by the encoder. -/
theorem RepresentationContext.lookup_flagged_relation
    {E : B.Env} {Gamma : SMT.TypeContext}
    (h : E.RepresentationContext Gamma)
    {v : B.𝒱} {alpha beta : BType}
    (hv : E.context.lookup v = some (.set (.prod alpha beta)))
    (hflag : v ∈ E.flags) :
    Gamma.lookup v =
      some (.fun alpha.toSMTType (.option beta.toSMTType)) := by
  obtain ⟨sigma, hselected, hlookup⟩ := h.of_lookup hv
  simp [BType.selectedSMTType?, hflag] at hselected
  subst sigma
  exact hlookup

/-- Semantic justification for the option-function representation selected by
the encoder.  Every assigned flagged value must really be a partial function;
the list of flagged names alone carries no such proof. -/
def FlaggedValuesFunctional (E : B.Env)
    (Xi : B.RenamingContext.Context) : Prop :=
  ∀ v d, Xi v = some d → v ∈ E.flags → d.IsFunctional

open Classical in
/-- Construct one SMT valuation on an arbitrary finite source scope.  Values
outside the scope are left unassigned.  Inside it, unflagged values use their
canonical representative and semantically functional flagged relations use
the graph-collapse representative selected by `encodeTypeContext`.

The pointwise conclusion packages target typing and representation agreement
together; downstream script proofs can therefore derive both the term
theorem's relation premise and its target type-context premise from the same
chosen valuation. -/
theorem exists_selectedValuationOn.{u}
    {E : B.Env} {Gamma : SMT.TypeContext}
    {Xi : B.RenamingContext.Context.{u}} {scope : List B.𝒱}
    (representation : E.RepresentationContext Gamma)
    (source_covers : ∀ v ∈ scope, (Xi v).isSome = true)
    (source_wf : B.RenWF E.context Xi)
    (functional : E.FlaggedValuesFunctional Xi)
    (scope_context : ∀ v ∈ scope, v ∈ E.context) :
    ∃ Theta : SMT.RenamingContext.Context.{u},
      (∀ v ∈ scope, ∃ d d' sigma,
        Xi v = some d ∧ Theta v = some d' ∧
          Gamma.lookup v = some sigma ∧ d'.snd.fst = sigma ∧
          RDomCastSupported d d') ∧
      ∀ v ∉ scope, Theta v = none := by
  have witness : ∀ v ∈ scope, ∃ d' d sigma,
      Xi v = some d ∧ Gamma.lookup v = some sigma ∧
        d'.snd.fst = sigma ∧ RDomCastSupported d d' := by
    intro v hv
    have hv_context := scope_context v hv
    obtain ⟨tau, hE⟩ := Option.isSome_iff_exists.mp
      (AList.lookup_isSome.mpr hv_context)
    obtain ⟨d, hXi⟩ := Option.isSome_iff_exists.mp (source_covers v hv)
    have hdtype : d.snd.fst = tau := by
      have htyped := source_wf v d hXi hv_context
      rw [hE] at htyped
      exact Option.some.inj htyped.symm
    obtain ⟨sigma, hselected, hGamma⟩ :=
      representation.of_lookup hE
    have hselected' :
        BType.selectedSMTType? (v ∈ E.flags) d.snd.fst = some sigma := by
      simpa only [hdtype] using hselected
    obtain ⟨d', hd'type, hrelated⟩ :=
      d.exists_selectedSMT_supported hselected' (by
        intro hflag
        apply functional v d hXi
        simpa using hflag)
    exact ⟨d', d, sigma, hXi, hGamma, hd'type, hrelated⟩
  let Theta : SMT.RenamingContext.Context.{u} := fun v =>
    if hv : v ∈ scope then
      some (Classical.choose (witness v hv))
    else none
  refine ⟨Theta, ?_, ?_⟩
  · intro v hv
    obtain ⟨d, sigma, hXi, hGamma, hd'type, hrelated⟩ :=
      Classical.choose_spec (witness v hv)
    exact ⟨d, Classical.choose (witness v hv), sigma, hXi,
      by simp [Theta, hv], hGamma, hd'type, hrelated⟩
  · intro v hv
    simp [Theta, hv]

open Classical in
/-- Term-scoped form of `exists_selectedValuationOn`.  This is the direct
entry point for `encodeTerm_rep_spec`: the chosen SMT valuation is related on
all source free variables, respects the target context there, has no unrelated
assignments, and has domain contained in the encoded target context. -/
theorem exists_selectedValuation_for_term.{u}
    {E : B.Env} {Gamma : SMT.TypeContext}
    {Xi : B.RenamingContext.Context.{u}} {t : B.Term}
    (representation : E.RepresentationContext Gamma)
    (source_covers : ∀ v ∈ B.fv t, (Xi v).isSome = true)
    (source_wf : B.RenWF E.context Xi)
    (functional : E.FlaggedValuesFunctional Xi)
    (fv_context : ∀ v ∈ B.fv t, v ∈ E.context) :
    ∃ Theta : SMT.RenamingContext.Context.{u},
      RValuationCastSupportedOnFV Xi Theta t ∧
      B.RenamingContext.RespectsTypeContextOnFV Theta Gamma t ∧
      (∀ v ∉ B.fv t, Theta v = none) ∧
      ∀ v, Theta v ≠ none → v ∈ Gamma := by
  obtain ⟨Theta, hpoint, hnone⟩ :=
    E.exists_selectedValuationOn representation source_covers source_wf
      functional fv_context
  refine ⟨Theta, ?_, ?_, hnone, ?_⟩
  · intro v hv
    obtain ⟨d, d', sigma, hXi, hTheta, _hGamma, _hd'type, hrelated⟩ :=
      hpoint v hv
    rw [hXi, hTheta]
    exact hrelated
  · intro v sigma hv hlookup
    obtain ⟨d, d', sigma', _hXi, hTheta, hGamma, hd'type, _hrelated⟩ :=
      hpoint v hv
    rw [hGamma] at hlookup
    cases hlookup
    exact ⟨d', hTheta, hd'type⟩
  · intro v hTheta
    have hv : v ∈ B.fv t := by
      by_contra hnot
      exact hTheta (hnone v hnot)
    obtain ⟨d, d', sigma, _hXi, _hTheta, hGamma, _hd'type, _hrelated⟩ :=
      hpoint v hv
    exact AList.lookup_isSome.mp (by rw [hGamma]; simp)

end B.Env

set_option mvcgen.warning false in
@[spec]
theorem encode_type_context_representation_context (E : B.Env) :
    ⦃ fun ⟨_, Gamma⟩ => ⌜Gamma = ∅⌝ ⦄
    encodeTypeContext E
    ⦃ ⇓? () ⟨_, Gamma⟩ => ⌜E.RepresentationContext Gamma⌝ ⦄ := by
  unfold encodeTypeContext
  mvcgen

  case inv1 sigma =>
    exact ⇓? ⟨⟨pref, suff, eq⟩, ()⟩ ⟨E', Gamma⟩ =>
      ⌜pref.keys.Disjoint suff.keys ∧
        forall (v : B.𝒱) (tau : BType),
          (Sigma.mk v tau) ∈ pref ->
            exists rho,
              BType.selectedSMTType? (v ∈ E.flags) tau = some rho /\
                Gamma.lookup v = some rho⌝

  case vc1 _ pref cur suff eq _ fst alpha beta snd _ inv xi =>
    dsimp [xi] at inv ⊢
    constructor
    · rw [List.keys, List.map_append, List.map_singleton,
        List.disjoint_append_left]
      constructor
      · exact List.disjoint_of_disjoint_cons_right inv.1
      · have hnodup := List.NodupKeys.sublist
          (l₁ := cur :: suff)
          (List.sublist_append_right pref (cur :: suff))
          (eq ▸ E.context.nodupKeys)
        rw [List.nodupKeys_cons] at hnodup
        rw [List.disjoint_comm, List.disjoint_singleton]
        exact hnodup.1
    · intro v tau hv
      rw [List.mem_append, List.mem_singleton] at hv
      rcases hv with hv | rfl
      · obtain ⟨rho, hselected, hlookup⟩ := inv.2 v tau hv
        refine ⟨rho, hselected, ?_⟩
        rw [AList.lookup_insert_ne]
        · exact hlookup
        · intro hEq
          subst v
          apply (List.disjoint_cons_right.mp inv.1).1
          rw [List.keys, List.mem_map]
          exact ⟨⟨cur.fst, tau⟩, hv, rfl⟩
      · change tau = (alpha ×ᴮ beta).set at snd
        subst tau
        refine ⟨alpha.toSMTType.fun beta.toSMTType.option, ?_,
          AList.lookup_insert _⟩
        simp [BType.selectedSMTType?, fst]

  case vc7 pref cur suff eq _ not_flagged _ inv xi =>
    dsimp [xi] at inv ⊢
    constructor
    · rw [List.keys, List.map_append, List.map_singleton,
        List.disjoint_append_left]
      constructor
      · exact List.disjoint_of_disjoint_cons_right inv.1
      · have hnodup := List.NodupKeys.sublist
          (l₁ := cur :: suff)
          (List.sublist_append_right pref (cur :: suff))
          (eq ▸ E.context.nodupKeys)
        rw [List.nodupKeys_cons] at hnodup
        rw [List.disjoint_comm, List.disjoint_singleton]
        exact hnodup.1
    · intro v tau hv
      rw [List.mem_append, List.mem_singleton] at hv
      rcases hv with hv | rfl
      · obtain ⟨rho, hselected, hlookup⟩ := inv.2 v tau hv
        refine ⟨rho, hselected, ?_⟩
        rw [AList.lookup_insert_ne]
        · exact hlookup
        · intro hEq
          subst v
          apply (List.disjoint_cons_right.mp inv.1).1
          rw [List.keys, List.mem_map]
          exact ⟨⟨cur.fst, tau⟩, hv, rfl⟩
      · refine ⟨tau.toSMTType, ?_, AList.lookup_insert _⟩
        simp [BType.selectedSMTType?, not_flagged]

  case vc6 => trivial
  case vc8 sigma =>
    exact ⟨List.disjoint_nil_left _, by simp⟩
  case vc9 h =>
    exact h.2

  case vc2 => exact Encoder
  case vc3 =>
    exact PostShape.arg EncoderState
      (PostShape.except String PostShape.pure)
  case vc4 => infer_instance
  case vc5 => infer_instance
