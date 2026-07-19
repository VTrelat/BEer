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

/-- Graphing an option-valued target representative exposes that its source
relation is semantically functional. -/
theorem RDomCastSupported.optionFunction_source_functional.{u}
    {alpha beta : BType} {X F : ZFSet.{u}}
    {hX : X ∈ ⟦BType.set (alpha ×ᴮ beta)⟧ᶻ}
    {hF : F ∈
      ⟦SMTType.fun alpha.toSMTType (SMTType.option beta.toSMTType)⟧ᶻ}
    (hrel : RDomCastSupported
      (⟨X, BType.set (alpha ×ᴮ beta), hX⟩ : B.Dom)
      (⟨F, SMTType.fun alpha.toSMTType
        (SMTType.option beta.toSMTType), hF⟩ : SMT.Dom)) :
    B.Dom.IsFunctional
      (⟨X, BType.set (alpha ×ᴮ beta), hX⟩ : B.Dom) := by
  have hGraph := optionGraph_mem alpha.toSMTType beta.toSMTType hF
  let hs : BType.SupportedSMT (BType.set (alpha ×ᴮ beta))
      (SMTType.fun (SMTType.pair alpha.toSMTType beta.toSMTType)
        SMTType.bool) :=
    .setPred (.prod (.canonical alpha) (.canonical beta))
  have bare : RDomCast
      (⟨X, BType.set (alpha ×ᴮ beta), hX⟩ : B.Dom)
      (⟨optionGraph alpha.toSMTType beta.toSMTType F,
        SMTType.fun (SMTType.pair alpha.toSMTType beta.toSMTType)
          SMTType.bool, hGraph⟩ : SMT.Dom) := by
    refine ⟨castPath.reflexive
      (BType.set (alpha ×ᴮ beta)).toSMTType, ?_⟩
    rw [castZF_apply_self _ hGraph]
    exact hrel.toRDomCast.optionFunction_graph_retract
  have graphRel : RDomCastSupported
      (⟨X, BType.set (alpha ×ᴮ beta), hX⟩ : B.Dom)
      (⟨optionGraph alpha.toSMTType beta.toSMTType F,
        SMTType.fun (SMTType.pair alpha.toSMTType beta.toSMTType)
          SMTType.bool, hGraph⟩ : SMT.Dom) :=
    ⟨bare.toRDomCastAdmissible_of_supported hs, hs⟩
  have htarget := predGraph_optionGraph_isPFunc
    alpha.toSMTType beta.toSMTType F hF
  simpa [B.Dom.IsFunctional] using
    RDomCastSupported.setPred_isPFunc_to_source graphRel htarget

/-- A selected option-function target type transfers semantic functionhood
back to the represented source value. -/
theorem RDomCastSupported.source_functional_of_selected_true.{u}
    {d : B.Dom.{u}} {d' : SMT.Dom.{u}} {sigma : SMTType}
    (hselected : BType.selectedSMTType? true d.snd.fst = some sigma)
    (htype : d'.snd.fst = sigma)
    (hrel : RDomCastSupported d d') :
    B.Dom.IsFunctional d := by
  rcases d with ⟨X, tau, hX⟩
  rcases d' with ⟨F, rho, hF⟩
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
          cases hselected
          cases htype
          exact B.Dom.RDomCastSupported.optionFunction_source_functional hrel

/-- Membership in a partial-function space supplies the semantic
functionality required by the option-function representation.  The relation
is weakened from the denoted domain and range sets to their ambient B types. -/
theorem isFunctional_of_mem_pfunSet.{u}
    {d : B.Dom.{u}} {alpha beta : BType}
    (htype : d.snd.fst = BType.set (alpha ×ᴮ beta))
    {X Y : ZFSet.{u}}
    (hX : X ∈ ⟦BType.set alpha⟧ᶻ)
    (hY : Y ∈ ⟦BType.set beta⟧ᶻ)
    (hmem : d.fst ∈ pfunSet X Y) :
    d.IsFunctional := by
  rcases d with ⟨F, tau, hF⟩
  dsimp at htype
  subst tau
  simp only [B.Dom.IsFunctional]
  apply ZFSet.pfunc_weaken (ZFSet.mem_sep.mp hmem).2
  · exact ZFSet.mem_powerset.mp hX
  · exact ZFSet.mem_powerset.mp hY

/-- If an asserted source predicate `v ∈ S ⇸ T` evaluates to true, then the
value assigned to `v` is genuinely functional.  This is the semantic step
that turns a proof-obligation hypothesis, rather than a representation flag,
into the witness consumed by `exists_selectedSMT_supported`. -/
theorem isFunctional_of_true_pfun_membership.{u}
    {E : B.Env} {Xi : B.RenamingContext.Context.{u}}
    {v : B.𝒱} {S T : B.Term} {alpha beta : BType}
    {d : B.Dom.{u}}
    (hlookup : E.context.lookup v =
      some (BType.set (alpha ×ᴮ beta)))
    (typ_S : E.context ⊢ᴮ S : BType.set alpha)
    (typ_T : E.context ⊢ᴮ T : BType.set beta)
    (Xi_fv : ∀ w ∈ B.fv
      (B.Term.var v ∈ᴮ (B.Term.pfun S T)), (Xi w).isSome = true)
    (wf : B.RenWF E.context Xi)
    (hXi : Xi v = some d)
    (hden : ⟦(B.Term.var v ∈ᴮ (B.Term.pfun S T)).abstract
        Xi Xi_fv⟧ᴮ =
      some ⟨ZFSet.zftrue, BType.bool,
        ZFSet.ZFBool.zftrue_mem_𝔹⟩) :
    d.IsFunctional := by
  let Xi_fv_pfun : ∀ w ∈ B.fv (B.Term.pfun S T),
      (Xi w).isSome = true := fun w hw => Xi_fv w (by
    rw [B.fv, List.mem_append]
    exact Or.inr hw)
  obtain ⟨F, hF, U, hU, hden_F, hden_U, htrue⟩ :=
    B.denote_mem_inv
      (E := E)
      (B.Typing.var hlookup)
      (B.Typing.pfun typ_S typ_T)
      Xi_fv wf hden
  have hXi_F : Xi v =
      some (⟨F, BType.set (alpha ×ᴮ beta), hF⟩ : B.Dom) := by
    rw [B.Term.abstract, B.denote] at hden_F
    simp only [Option.pure_def, Option.some.injEq] at hden_F
    have h_isSome : (Xi v).isSome = true := Xi_fv v (by simp [B.fv])
    exact Option.some_get h_isSome ▸ congrArg some hden_F
  have hd : d =
      (⟨F, BType.set (alpha ×ᴮ beta), hF⟩ : B.Dom) :=
    Option.some.inj (hXi.symm.trans hXi_F)
  subst d
  obtain ⟨X, Y, hX, hY, _hden_X, _hden_Y, hU_eq⟩ :=
    B.denote_pfun_inv_rep Xi_fv_pfun hden_U
  have hFU : F ∈ U := by
    by_contra hnot
    simp [overloadUnaryOp, hnot] at htrue
    exact ZFSet.zftrue_ne_zffalse htrue
  subst U
  exact isFunctional_of_mem_pfunSet rfl hX hY hFU

/-- The total-function encoding used by the POG decoder is a collection over
a partial-function domain.  Truth of `v ∈ {f ∈ S ⇸ T | P}` therefore still
implies that the represented value of `v` is functional: collection
membership first descends to the `S ⇸ T` domain, then the direct partial-
function argument applies. -/
theorem isFunctional_of_true_collect_pfun_membership.{u}
    {E : B.Env} {Xi : B.RenamingContext.Context.{u}}
    {v : B.𝒱} {vs : List B.𝒱} {S T P : B.Term}
    {alpha beta : BType} {d : B.Dom.{u}}
    (hlookup : E.context.lookup v =
      some (BType.set (alpha ×ᴮ beta)))
    (typ_D : E.context ⊢ᴮ B.Term.pfun S T :
      BType.set (BType.set (alpha ×ᴮ beta)))
    (typ_collect : E.context ⊢ᴮ
      B.Term.collect vs (B.Term.pfun S T) P :
        BType.set (BType.set (alpha ×ᴮ beta)))
    (tau_hasArity : (BType.set (alpha ×ᴮ beta)).hasArity vs.length)
    (Xi_fv : ∀ w ∈ B.fv
      (B.Term.var v ∈ᴮ
        B.Term.collect vs (B.Term.pfun S T) P),
        (Xi w).isSome = true)
    (wf : B.RenWF E.context Xi)
    (hXi : Xi v = some d)
    (hden : ⟦(B.Term.var v ∈ᴮ
        B.Term.collect vs (B.Term.pfun S T) P).abstract
          Xi Xi_fv⟧ᴮ =
      some ⟨ZFSet.zftrue, BType.bool,
        ZFSet.ZFBool.zftrue_mem_𝔹⟩) :
    d.IsFunctional := by
  let Xi_fv_collect : ∀ w ∈ B.fv
      (B.Term.collect vs (B.Term.pfun S T) P),
      (Xi w).isSome = true := fun w hw => Xi_fv w (by
    rw [B.fv, List.mem_append]
    exact Or.inr hw)
  let Xi_fv_D : ∀ w ∈ B.fv (B.Term.pfun S T),
      (Xi w).isSome = true := fun w hw =>
    Xi_fv_collect w (B.fv.mem_collect (.inl hw))
  obtain ⟨F, hF, U, hU, hden_F, hden_collect, htrue⟩ :=
    B.denote_mem_inv
      (E := E)
      (B.Typing.var hlookup)
      typ_collect
      Xi_fv wf hden
  have hXi_F : Xi v =
      some (⟨F, BType.set (alpha ×ᴮ beta), hF⟩ : B.Dom) := by
    rw [B.Term.abstract, B.denote] at hden_F
    simp only [Option.pure_def, Option.some.injEq] at hden_F
    have h_isSome : (Xi v).isSome = true := Xi_fv v (by simp [B.fv])
    exact Option.some_get h_isSome ▸ congrArg some hden_F
  have hd : d =
      (⟨F, BType.set (alpha ×ᴮ beta), hF⟩ : B.Dom) :=
    Option.some.inj (hXi.symm.trans hXi_F)
  subst d
  have hFU : F ∈ U := by
    by_contra hnot
    simp [overloadUnaryOp, hnot] at htrue
    exact ZFSet.zftrue_ne_zffalse htrue
  obtain ⟨Dval, hDval, hden_D⟩ :=
    B.denote_collect_domain_exists Xi_fv_collect typ_D wf hden_collect
  have hFD : F ∈ Dval :=
    B.denote_collect_mem_domain Xi_fv_collect tau_hasArity
      hden_D hden_collect hFU
  obtain ⟨X, Y, hX, hY, _hden_X, _hden_Y, hD_eq⟩ :=
    B.denote_pfun_inv_rep Xi_fv_D hden_D
  subst Dval
  exact isFunctional_of_mem_pfunSet rfl hX hY hFD

end B.Dom

namespace B.Term

/-- A source predicate evaluates to B truth under a valuation covering all of
its free variables. -/
def Holds.{u} (Xi : B.RenamingContext.Context.{u}) (t : B.Term) : Prop :=
  ∃ Xi_fv : ∀ v ∈ B.fv t, (Xi v).isSome = true,
    ⟦t.abstract Xi Xi_fv⟧ᴮ =
      some ⟨ZFSet.zftrue, BType.bool,
        ZFSet.ZFBool.zftrue_mem_𝔹⟩

end B.Term

namespace B.Env

/-- Every name marked for option-function representation is also declared in
the source type context.  This is the environment invariant that rules out an
accidental collision between a fresh binder and an unrelated global flag. -/
def FlagsInContext (E : B.Env) : Prop :=
  ∀ v ∈ E.flags, v ∈ E.context

/-- B typing requires the names bound by `all` to be fresh for the ambient
source context.  In a flag-valid environment they are consequently unflagged,
so the encoder leaves their domain-component representations unchanged. -/
theorem FlagsInContext.all_binders_unflagged
    {E : B.Env} (hflags : E.FlagsInContext)
    {vs : List B.𝒱} {D P : B.Term} {tau : BType}
    (htyp : E.context ⊢ᴮ B.Term.all vs D P : tau) :
    ∀ v ∈ vs, v ∉ E.flags := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hdisjoint⟩ :=
    B.Typing.allE htyp
  intro v hv hflag
  exact hdisjoint v hv (hflags v hflag)

/-- Valid proof-obligation environments select the honest no-flag branch of
the generalized quantified-case theorem. -/
theorem FlagsInContext.all_binder_condition.{u}
    {E : B.Env} (hflags : E.FlagsInContext)
    {vs : List B.𝒱} {D P : B.Term} {tau : BType}
    (htyp : E.context ⊢ᴮ B.Term.all vs D P : tau) :
    EncodeTermAllBinderAdmissible.{u} ∨
      ∀ v ∈ vs, v ∉ E.flags :=
  .inr (hflags.all_binders_unflagged htyp)

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

/-- Every *assigned* functional-representation flag has an asserted
function-typing hypothesis in the supplied assumption list.  Restricting to
assigned values is essential because decoded definitions may leave flags for
bound helper names outside the current valuation's source scope.  The second
shape is the collection-over-`pfun` encoding emitted for a total B function. -/
def AssignedFlagsHaveFunctionHypotheses.{u} (E : B.Env)
    (Xi : B.RenamingContext.Context.{u}) (hs : List B.Term) : Prop :=
  ∀ v d, Xi v = some d → v ∈ E.flags →
    (∃ S T, (B.Term.var v ∈ᴮ B.Term.pfun S T) ∈ hs) ∨
    (∃ vs S T P,
      (B.Term.var v ∈ᴮ
        B.Term.collect vs (B.Term.pfun S T) P) ∈ hs)

/-- All supplied source assumptions are well-typed predicates. -/
def AssumptionsTyped (E : B.Env) (hs : List B.Term) : Prop :=
  ∀ h ∈ hs, E.context ⊢ᴮ h : BType.bool

/-- All supplied source assumptions hold under the source valuation. -/
def AssumptionsHold.{u} (Xi : B.RenamingContext.Context.{u})
    (hs : List B.Term) : Prop :=
  ∀ h ∈ hs, h.Holds Xi

/-- The functionality premise of the representation bridge follows from
actual direct or total-function membership assumptions, their typing, and
their truth.  No property is inferred from `E.flags` alone. -/
theorem flaggedValuesFunctional_of_function_hypotheses.{u}
    {E : B.Env} {Xi : B.RenamingContext.Context.{u}}
    {hs : List B.Term}
    (covers : E.AssignedFlagsHaveFunctionHypotheses Xi hs)
    (typed : E.AssumptionsTyped hs)
    (holds : AssumptionsHold Xi hs)
    (wf : B.RenWF E.context Xi) :
    E.FlaggedValuesFunctional Xi := by
  intro v d hXi hflag
  rcases covers v d hXi hflag with direct | collected
  · obtain ⟨S, T, hmem⟩ := direct
    have htyp := typed _ hmem
    obtain ⟨_, alpha, typ_v, typ_pfun⟩ := B.Typing.memE htyp
    obtain ⟨beta, gamma, htype, typ_S, typ_T⟩ :=
      B.Typing.pfunE typ_pfun
    have halpha : alpha = BType.set (beta ×ᴮ gamma) :=
      BType.set.inj htype
    subst alpha
    obtain ⟨Xi_fv, hden⟩ := holds _ hmem
    exact d.isFunctional_of_true_pfun_membership
      (B.Typing.varE typ_v) typ_S typ_T Xi_fv wf hXi hden
  · obtain ⟨vs, S, T, P, hmem⟩ := collected
    have htyp := typed _ hmem
    obtain ⟨_, tau, typ_v, typ_collect⟩ := B.Typing.memE htyp
    obtain ⟨alphas, Ds, vs_nemp, vs_alphas_len, vs_Ds_len,
        result_eq, _vs_nodup, D_eq, typ_Ds, _typ_P,
        _vs_context_disj⟩ := B.Typing.collectE typ_collect
    have alphas_nemp : alphas ≠ [] := by
      simpa [vs_alphas_len, ← List.length_pos_iff] using vs_nemp
    let rho := alphas.reduce (· ×ᴮ ·) alphas_nemp
    have tau_eq : tau = rho := BType.set.inj result_eq
    subst tau
    have typ_D : E.context ⊢ᴮ B.Term.pfun S T : BType.set rho := by
      rw [D_eq]
      exact typing_reduce_cprod E.context _ _ typ_Ds
        (by simpa [vs_Ds_len, ← List.length_pos_iff] using vs_nemp)
        (by simpa [vs_alphas_len, ← List.length_pos_iff] using vs_nemp)
    have rho_hasArity : rho.hasArity vs.length := by
      dsimp [rho]
      rw [List.reduce]
      have hlen : alphas.tail.length + 1 = vs.length := by
        rw [List.length_tail, vs_alphas_len]
        have := List.length_pos_of_ne_nil alphas_nemp
        omega
      convert BType.hasArity_of_foldl
        (α := alphas.head alphas_nemp) (αs := alphas.tail) using 1
      exact hlen.symm
    obtain ⟨alpha, beta, Dtype_eq, _typ_S, _typ_T⟩ :=
      B.Typing.pfunE typ_D
    have rho_eq : rho = BType.set (alpha ×ᴮ beta) :=
      BType.set.inj Dtype_eq
    rw [rho_eq] at typ_v typ_D typ_collect rho_hasArity
    obtain ⟨Xi_fv, hden⟩ := holds _ hmem
    exact d.isFunctional_of_true_collect_pfun_membership
      (alpha := alpha) (beta := beta)
      (B.Typing.varE typ_v) typ_D typ_collect rho_hasArity
      Xi_fv wf hXi hden

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

open Classical in
/-- Reconstruct one source valuation from a target valuation on a finite
source scope.  The selected type equation is retained pointwise so the
flagged branch can recover semantic functionhood from the target option
function rather than treating the flag itself as evidence. -/
theorem exists_sourceValuationOn.{u}
    {E : B.Env} {Gamma : SMT.TypeContext}
    {Theta : SMT.RenamingContext.Context.{u}} {scope : List B.𝒱}
    (representation : E.RepresentationContext Gamma)
    (target_respects : SMT.RenamingContext.RespectsTypeContext Theta Gamma)
    (scope_context : ∀ v ∈ scope, v ∈ E.context) :
    ∃ Xi : B.RenamingContext.Context.{u},
      (∀ v ∈ scope, ∃ d d' tau sigma,
        Xi v = some d ∧ Theta v = some d' ∧
          E.context.lookup v = some tau ∧
          BType.selectedSMTType? (v ∈ E.flags) tau = some sigma ∧
          Gamma.lookup v = some sigma ∧
          d.snd.fst = tau ∧ d'.snd.fst = sigma ∧
          RDomCastSupported d d') ∧
      ∀ v ∉ scope, Xi v = none := by
  have witness : ∀ v ∈ scope, ∃ d d' tau sigma,
      Theta v = some d' ∧ E.context.lookup v = some tau ∧
        BType.selectedSMTType? (v ∈ E.flags) tau = some sigma ∧
        Gamma.lookup v = some sigma ∧ d.snd.fst = tau ∧
        d'.snd.fst = sigma ∧ RDomCastSupported d d' := by
    intro v hv
    have hv_context := scope_context v hv
    obtain ⟨tau, hE⟩ := Option.isSome_iff_exists.mp
      (AList.lookup_isSome.mpr hv_context)
    obtain ⟨sigma, hselected, hGamma⟩ := representation.of_lookup hE
    obtain ⟨d', hTheta, hd'type⟩ := target_respects hGamma
    have hsupported := BType.SupportedSMT.of_selectedSMTType? hselected
    rcases d' with ⟨Y, rho, hY⟩
    change rho = sigma at hd'type
    cases hd'type
    obtain ⟨X, hX, hrelated⟩ :=
      supported_target_preimage hsupported Y hY
    exact ⟨⟨X, tau, hX⟩, ⟨Y, sigma, hY⟩, tau, sigma,
      hTheta, hE, hselected, hGamma, rfl, rfl, hrelated⟩
  let Xi : B.RenamingContext.Context.{u} := fun v =>
    if hv : v ∈ scope then
      some (Classical.choose (witness v hv))
    else none
  refine ⟨Xi, ?_, ?_⟩
  · intro v hv
    obtain ⟨d', tau, sigma, hTheta, hE, hselected, hGamma,
        hdtype, hd'type, hrelated⟩ :=
      Classical.choose_spec (witness v hv)
    exact ⟨Classical.choose (witness v hv), d', tau, sigma,
      by simp [Xi, hv], hTheta, hE, hselected, hGamma, hdtype,
      hd'type, hrelated⟩
  · intro v hv
    simp [Xi, hv]

open Classical in
/-- Term-scoped converse reconstruction, including all source-side invariants
required by the represented term theorem. -/
theorem exists_sourceValuation_for_term.{u}
    {E : B.Env} {Gamma : SMT.TypeContext}
    {Theta : SMT.RenamingContext.Context.{u}} {t : B.Term}
    (representation : E.RepresentationContext Gamma)
    (target_respects : SMT.RenamingContext.RespectsTypeContext Theta Gamma)
    (fv_context : ∀ v ∈ B.fv t, v ∈ E.context) :
    ∃ Xi : B.RenamingContext.Context.{u},
      RValuationCastSupportedOnFV Xi Theta t ∧
      (∀ v ∈ B.fv t, (Xi v).isSome = true) ∧
      B.RenWF E.context Xi ∧
      E.FlaggedValuesFunctional Xi ∧
      (∀ v ∉ B.fv t, Xi v = none) ∧
      ∀ v, Xi v ≠ none → v ∈ E.context := by
  obtain ⟨Xi, hpoint, hnone⟩ :=
    E.exists_sourceValuationOn representation target_respects fv_context
  refine ⟨Xi, ?_, ?_, ?_, ?_, hnone, ?_⟩
  · intro v hv
    obtain ⟨d, d', tau, sigma, hXi, hTheta, hE, hselected,
        hGamma, hdtype, hd'type, hrelated⟩ := hpoint v hv
    rw [hXi, hTheta]
    exact hrelated
  · intro v hv
    obtain ⟨d, d', tau, sigma, hXi, _⟩ := hpoint v hv
    rw [hXi]
    rfl
  · intro v d hXi _hv_context
    have hv : v ∈ B.fv t := by
      by_contra hnot
      rw [hnone v hnot] at hXi
      contradiction
    obtain ⟨d0, d', tau, sigma, hXi0, hTheta, hE, hselected,
        hGamma, hdtype, hd'type, hrelated⟩ := hpoint v hv
    have hdd : d = d0 := Option.some.inj (hXi.symm.trans hXi0)
    rw [hdd, hdtype]
    exact hE
  · intro v d hXi hflag
    have hv : v ∈ B.fv t := by
      by_contra hnot
      rw [hnone v hnot] at hXi
      contradiction
    obtain ⟨d0, d', tau, sigma, hXi0, hTheta, hE, hselected,
        hGamma, hdtype, hd'type, hrelated⟩ := hpoint v hv
    have hdd : d = d0 := Option.some.inj (hXi.symm.trans hXi0)
    have hselected0 :
        BType.selectedSMTType? true tau = some sigma := by
      simpa [hflag] using hselected
    have hselected' :
        BType.selectedSMTType? true d0.snd.fst = some sigma := by
      rw [hdtype]
      exact hselected0
    rw [hdd]
    exact B.Dom.RDomCastSupported.source_functional_of_selected_true
      hselected' hd'type hrelated
  · intro v hXi
    have hv : v ∈ B.fv t := by
      by_contra hnot
      exact hXi (hnone v hnot)
    exact fv_context v hv

end B.Env

namespace B.ProofObligation

/-- Every option-function flag introduced while decoding one proof obligation
also has a PO-local source type binding.  This condition is intentionally
separate from global flag validity: builtins may use flagged bound helpers. -/
def LocalFlagsInContext (po : B.ProofObligation) : Prop :=
  ∀ v ∈ po.localFlags, v ∈ po.localContext

private theorem keys_subset_foldl_insert
    {alpha : Type} {beta : alpha → Type} [DecidableEq alpha]
    (l : List (Sigma beta)) {Gamma : AList beta} :
    AList.keys Gamma ⊆
      AList.keys (l.foldl
        (fun Gamma (p : Sigma beta) => Gamma.insert p.1 p.2) Gamma) := by
  induction l generalizing Gamma with
  | nil => exact fun _ h => h
  | cons p ps ih =>
    simp only [List.foldl_cons]
    intro v hv
    apply ih
    exact AList.mem_keys.mp
      ((AList.mem_insert _).mpr (.inr (AList.mem_keys.mpr hv)))

private theorem mem_keys_foldl_insert_of_fst
    {alpha : Type} {beta : alpha → Type} [DecidableEq alpha]
    (l : List (Sigma beta)) {Gamma : AList beta} {v : alpha}
    (hv : v ∈ l.map Sigma.fst) :
    v ∈ AList.keys (l.foldl
      (fun Gamma (p : Sigma beta) => Gamma.insert p.1 p.2) Gamma) := by
  induction l generalizing Gamma with
  | nil => simp at hv
  | cons p ps ih =>
    simp only [List.foldl_cons]
    simp only [List.map_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact keys_subset_foldl_insert ps
        (by rw [AList.keys_insert]; exact List.mem_cons_self ..)
    · exact ih hv

/-- Combining a flag-valid global environment with flag-valid PO-local
bindings gives the exact extended environment used by `encodeProofObligation`,
and that environment is flag-valid as well. -/
theorem extendEnv_flagsInContext
    {po : B.ProofObligation} {E : B.Env}
    (hglobal : E.FlagsInContext)
    (hlocal : po.LocalFlagsInContext) :
    (po.extendEnv E).FlagsInContext := by
  intro v hv
  rw [B.ProofObligation.extendEnv, List.mem_append] at hv
  rcases hv with hvlocal | hvglobal
  · change v ∈ AList.keys (po.localContext.entries.foldl
      (fun acc ⟨k, tau⟩ => acc.insert k tau) E.context)
    apply mem_keys_foldl_insert_of_fst
    change v ∈ po.localContext.keys
    exact AList.mem_keys.mpr (hlocal v hvlocal)
  · change v ∈ AList.keys (po.localContext.entries.foldl
      (fun acc ⟨k, tau⟩ => acc.insert k tau) E.context)
    apply keys_subset_foldl_insert po.localContext.entries
    exact AList.mem_keys.mpr (hglobal v hvglobal)

/-- Exactly the source assumptions asserted before one simple goal by
`encodeProofObligation`. -/
def assumptionsFor (po : B.ProofObligation) (goal : B.SimpleGoal) :
    List B.Term :=
  po.defs ++ po.hyps ++ goal.hyps

/-- Proof-obligation form of the semantic functionality discharge. -/
theorem flaggedValuesFunctional_of_assumptions.{u}
    {po : B.ProofObligation} {goal : B.SimpleGoal}
    {E : B.Env} {Xi : B.RenamingContext.Context.{u}}
    (covers : E.AssignedFlagsHaveFunctionHypotheses Xi
      (po.assumptionsFor goal))
    (typed : E.AssumptionsTyped (po.assumptionsFor goal))
    (holds : B.Env.AssumptionsHold Xi (po.assumptionsFor goal))
    (wf : B.RenWF E.context Xi) :
    E.FlaggedValuesFunctional Xi :=
  E.flaggedValuesFunctional_of_function_hypotheses covers typed holds wf

end B.ProofObligation

/-- Quantified representation soundness for one proof-obligation binder known
to be unflagged.  The encoded domain relation then discharges binder
admissibility for the current and every alternative valuation.  This
term-local premise is strictly more accurate than requiring every decoder
helper flag to be a global source binding. -/
theorem encodeTerm_rep_spec.all_case_and_scoped_of_unflagged.{u}
    (vs : List B.𝒱) (D P : B.Term)
    (D_ih : EncodeTermRepIH.{u} D)
    (D_scoped : EncodeTermRepScopedIH.{u} D)
    (P_ih : EncodeTermRepIH.{u} P)
    (P_scoped : EncodeTermRepScopedBoolFromIH.{u} P)
    (wd_P : B.Term.WellDefined.{u} P)
    (E : B.Env) (binders_unflagged : ∀ v ∈ vs, v ∉ E.flags)
    {Lambda : SMT.TypeContext} {alpha : BType}
    (typ_t : E.context ⊢ᴮ B.Term.all vs D P : alpha)
    {Xi : B.RenamingContext.Context.{u}}
    (Xi_fv : ∀ v ∈ B.fv (B.Term.all vs D P), (Xi v).isSome = true)
    {Theta0 : SMT.RenamingContext.Context.{u}}
    (related : RValuationCastSupportedOnFV Xi Theta0
      (B.Term.all vs D P))
    {used : List SMT.𝒱}
    (Theta0_none : ∀ v ∉ used, Theta0 v = none)
    (Theta0_dom : ∀ v, Theta0 v ≠ none → v ∈ Lambda)
    {T : ZFSet.{u}} {hT : T ∈ ⟦alpha⟧ᶻ}
    (den_t : ⟦(B.Term.all vs D P).abstract Xi Xi_fv⟧ᴮ =
      some ⟨T, ⟨alpha, hT⟩⟩)
    (vars_used : ∀ v ∈ (B.Term.all vs D P).vars, v ∈ used)
    (Lambda_inv : ∀ v ∈ (B.Term.all vs D P).vars,
      v ∈ Lambda → v ∈ E.context)
    (bv_nodup : (B.bv (B.Term.all vs D P)).Nodup)
    (respects : B.RenamingContext.RespectsTypeContextOnFV Theta0 Lambda
      (B.Term.all vs D P))
    (fv_in_Lambda : ∀ v ∈ B.fv (B.Term.all vs D P), v ∈ Lambda)
    (wf : B.RenWF E.context Xi)
    {n : ℕ} {decl : SMT.Chunk} :
    ⦃fun ⟨E0, Lambda'⟩ ↦
      ⌜Lambda' = Lambda ∧ E0.freshvarsc = n ∧
        Lambda.keys ⊆ E0.usedVars ∧ E0.usedVars = used ∧
        E0.declarations = decl⌝⦄
    encodeTerm (B.Term.all vs D P) E
    ⦃⇓? (⟨t', sigma⟩ : SMT.Term × SMTType) ⟨E', Gamma'⟩ =>
      ⌜EncodeTermRepPost (B.Term.all vs D P) alpha Lambda Xi Theta0
          used T hT E t' sigma E' Gamma' ∧
        EncodeTermRepScopedPost.{u} (B.Term.all vs D P) E alpha Lambda
          decl t' sigma E' Gamma'⌝⦄ :=
  encodeTerm_rep_spec.all_case_and_scoped_of_oracle_or_unflagged
    vs D P D_ih D_scoped P_ih P_scoped wd_P E
    (.inr binders_unflagged) typ_t Xi_fv related
    Theta0_none Theta0_dom den_t vars_used Lambda_inv bv_nodup respects
    fv_in_Lambda wf

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
