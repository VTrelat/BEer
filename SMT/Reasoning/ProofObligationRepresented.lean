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
