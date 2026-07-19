import SMT.Reasoning.Basic.EncodeTermRepresentedSet
import SMT.Reasoning.Basic.EncodeTermRepresentedScopedUnion
import SMT.Reasoning.Basic.LoosenAuxExactUniv

open Std.Do B SMT ZFSet Classical

/-! # Generated-helper contracts for represented powersets -/

/-- Guarded partial correctness for the powerset continuation. -/
abbrev EncodePowTailRepGuardedSemantics.{u} (beta : BType)
    (S out : SMT.Term) (sigmaS sigmaOut : SMTType)
    (Lambda : SMT.TypeContext) (Dlt : SMT.Chunk) : Prop :=
  ∀ (GammaSup : SMT.TypeContext),
    ScopedContextExtends Lambda Dlt GammaSup →
    ∀ (Theta : SMT.RenamingContext.Context.{u})
      (hcovS : RenamingContext.CoversFV Theta S),
      SMT.RenamingContext.RespectsTypeContextOnFV Theta GammaSup S →
      SpecBodiesTrue Theta GammaSup Dlt →
      ∀ (X : ZFSet.{u}) (hX : X ∈ ⟦BType.set beta⟧ᶻ)
        (denS : SMT.Dom.{u}),
        ⟦S.abstract Theta hcovS⟧ˢ = some denS →
        denS.snd.fst = sigmaS →
        RDomCastSupported
          (⟨X, BType.set beta, hX⟩ : B.Dom) denS →
        ∀ (hcovOut : RenamingContext.CoversFV Theta out)
          (denOut : SMT.Dom.{u}),
          SMT.RenamingContext.RespectsTypeContextOnFV
            Theta GammaSup out →
          ⟦out.abstract Theta hcovOut⟧ˢ = some denOut →
          denOut.snd.fst = sigmaOut →
          RDomCastSupported
            (⟨X.powerset, BType.set (BType.set beta),
              powerset_mem_btype hX⟩ : B.Dom) denOut

/-- Totality plus guarded soundness for one successful powerset tail run. -/
abbrev EncodePowTailRepSemantics.{u} (beta : BType)
    (S out : SMT.Term) (sigmaS sigmaOut : SMTType)
    (Lambda Gamma : SMT.TypeContext)
    (used usedOut : List SMT.𝒱) (Dlt : SMT.Chunk) : Prop :=
  (∀ (Theta : SMT.RenamingContext.Context.{u})
      (hcovS : RenamingContext.CoversFV Theta S),
      (∀ v ∉ used, Theta v = none) →
      SMT.RenamingContext.RespectsTypeContextOnFV Theta Lambda S →
      (∀ v, Theta v ≠ none → v ∈ Lambda) →
      ∀ (X : ZFSet.{u}) (hX : X ∈ ⟦BType.set beta⟧ᶻ)
        (denS : SMT.Dom.{u}),
        ⟦S.abstract Theta hcovS⟧ˢ = some denS →
        RDomCastSupported
          (⟨X, BType.set beta, hX⟩ : B.Dom) denS →
        ∃ (Theta' : SMT.RenamingContext.Context.{u})
          (hcovOut : RenamingContext.CoversFV Theta' out)
          (denOut : SMT.Dom.{u}),
          RenamingContext.Extends Theta' Theta ∧
          (∀ v ∉ usedOut, Theta' v = none) ∧
          SMT.RenamingContext.RespectsTypeContextOnFV
            Theta' Gamma out ∧
          (∀ v, Theta' v ≠ none → v ∈ Gamma) ∧
          SpecBodiesTrue Theta' Gamma Dlt ∧
          ⟦out.abstract Theta' hcovOut⟧ˢ = some denOut ∧
          denOut.snd.fst = sigmaOut ∧
          RDomCastSupported
            (⟨X.powerset, BType.set (BType.set beta),
              powerset_mem_btype hX⟩ : B.Dom) denOut) ∧
  EncodePowTailRepGuardedSemantics.{u}
    beta S out sigmaS sigmaOut Lambda Dlt

/-- Operational powerset-tail contract carrying its exact declaration delta. -/
abbrev EncodePowTailRepScopedSpec.{u} (beta : BType)
    (S : SMT.Term) (sigmaS : SMTType) : Prop :=
  ∀ {Lambda : SMT.TypeContext} {n : ℕ} {used : List SMT.𝒱}
    {decl : SMT.Chunk},
    Lambda ⊢ˢ S : sigmaS →
    BType.SupportedSMT (BType.set beta) sigmaS →
    (∀ v ∈ SMT.bv S, v ∈ used) →
    ⦃fun ⟨env, Lambda'⟩ =>
      ⌜Lambda' = Lambda ∧ env.freshvarsc = n ∧
        Lambda.keys ⊆ env.usedVars ∧ env.usedVars = used ∧
        env.declarations = decl⌝⦄
    encodePowTail S sigmaS
    ⦃⇓? ⟨out, sigmaOut⟩ ⟨env', Gamma'⟩ =>
      ⌜used ⊆ env'.usedVars ∧
        Lambda ⊆ Gamma' ∧
        Gamma'.keys ⊆ env'.usedVars ∧
        Nonempty (sigmaOut ~>
          (BType.set (BType.set beta)).toSMTType) ∧
        Gamma' ⊢ˢ out : sigmaOut ∧
        (∀ v ∈ used, v ∉ Lambda → v ∉ Gamma') ∧
        ∃ Dlt : SMT.Chunk,
          env'.declarations = decl ++ Dlt ∧
          ContextGeneratedByDeclarations Lambda Gamma' Dlt ∧
          DeclarationContextTrace Lambda Dlt Gamma' ∧
          (∀ v ∈ declVars Dlt, v ∉ used) ∧
          (∀ v ∈ SMT.fv S, v ∈ SMT.fv out ∨
            ∃ b ∈ specBodies Dlt, v ∈ SMT.fv b) ∧
          (SMT.fv out ⊆ SMT.fv S ∪ declVars Dlt) ∧
          (∀ b ∈ specBodies Dlt,
            SMT.fv b ⊆ SMT.fv S ∪ declVars Dlt) ∧
          EncodePowTailRepSemantics.{u} beta S out sigmaS sigmaOut
            Lambda Gamma' used env'.usedVars Dlt ∧
          (∀ b ∈ specBodies Dlt, Gamma' ⊢ˢ b : SMTType.bool) ∧
          ScopedGeneratedTyping Lambda Dlt out sigmaOut⌝⦄

namespace EncodeTermRepresentedScopedSet

theorem direct_shape_decls
    (rho : SMTType) (S : SMT.Term)
    {Lambda : SMT.TypeContext} {n : ℕ} {used : List SMT.𝒱}
    {decl : SMT.Chunk}
    (typS : Lambda ⊢ˢ S : SMTType.fun rho SMTType.bool) :
    ⦃fun ⟨env, Lambda'⟩ =>
      ⌜Lambda' = Lambda ∧ env.freshvarsc = n ∧
        Lambda.keys ⊆ env.usedVars ∧ env.usedVars = used ∧
        env.declarations = decl⌝⦄
    encodePowTail S (SMTType.fun rho SMTType.bool)
    ⦃⇓? ⟨out, sigmaOut⟩ ⟨env', Gamma'⟩ =>
      ⌜∃ x P : SMT.𝒱,
        out = SMT.Term.lambda [P]
          [SMTType.fun rho SMTType.bool]
          (SMT.Term.forall [x] [rho]
            (.imp (.app (.var P) (.var x))
              (.app S (.var x)))) ∧
        sigmaOut = SMTType.fun
          (SMTType.fun rho SMTType.bool) SMTType.bool ∧
        Gamma' = Lambda ∧ env'.declarations = decl ∧
        x ≠ P ∧ x ∉ SMT.fv S ∧ P ∉ SMT.fv S⌝⦄ := by
  unfold encodePowTail
  mstart
  mintro pre ∀St0
  mpure pre
  obtain ⟨rfl, rfl, St0_keys, rfl, rfl⟩ := pre
  mspec Std.Do.Spec.get_StateT
  mspec (Std.Do.Triple.and _
    (SMT.freshVar_spec (Γ := St0.types)
      (τ := rho) (n := St0.env.freshvarsc)
      (used := St0.env.usedVars))
    (SMT.freshVar_decls (τ := rho)
      (decl := St0.env.declarations)))
  next x =>
    mrename_i pre
    mintro ∀St1
    mpure pre
    obtain ⟨⟨St1_types, x_fresh, _St1_fvc, _St1_used,
      _x_not_used⟩, St1_decl⟩ := pre
    mspec (Std.Do.Triple.and _
      (SMT.freshVar_spec (Γ := St1.types)
        (τ := SMTType.fun rho SMTType.bool)
        (n := St1.env.freshvarsc) (used := St1.env.usedVars))
      (SMT.freshVar_decls
        (τ := SMTType.fun rho SMTType.bool)
        (decl := St1.env.declarations)))
    next P =>
      mrename_i pre
      mintro ∀St2
      mpure pre
      obtain ⟨⟨St2_types, P_fresh, _St2_fvc, _St2_used,
        _P_not_used⟩, St2_decl⟩ := pre
      simp [modify]
      mspec Std.Do.Spec.modifyGet_StateT
      mpure_intro
      refine ⟨trivial, ?_, ?_, ?_, ?_⟩
      · rw [St2_decl, St1_decl]
      · intro h
        subst P
        apply P_fresh
        rw [St1_types, AList.mem_insert]
        exact Or.inl rfl
      · exact funNotMemFvOfNotMemContext typS x_fresh
      · have P_not_Lambda : P ∉ St0.types := by
          intro h
          apply P_fresh
          rw [St1_types, AList.mem_insert]
          exact Or.inr h
        exact funNotMemFvOfNotMemContext typS P_not_Lambda

theorem direct_guarded.{u}
    (beta : BType) (rho : SMTType)
    (hrho : BType.SupportedSMT beta rho)
    (S : SMT.Term) {x P : SMT.𝒱}
    {Lambda : SMT.TypeContext}
    (x_ne_P : x ≠ P) (x_not_fv_S : x ∉ SMT.fv S)
    (P_not_fv_S : P ∉ SMT.fv S)
    (typOut : Lambda ⊢ˢ
      SMT.Term.lambda [P] [SMTType.fun rho SMTType.bool]
        (SMT.Term.forall [x] [rho]
          (.imp (.app (.var P) (.var x))
            (.app S (.var x)))) :
      SMTType.fun (SMTType.fun rho SMTType.bool) SMTType.bool)
    {Theta : SMT.RenamingContext.Context.{u}}
    (hcovS : RenamingContext.CoversFV Theta S)
    (respectsS : SMT.RenamingContext.RespectsTypeContextOnFV
      Theta Lambda S)
    {X : ZFSet.{u}} {hX : X ∈ ⟦BType.set beta⟧ᶻ}
    {denS : SMT.Dom.{u}}
    (hdenS : ⟦S.abstract Theta hcovS⟧ˢ = some denS)
    (hdenS_type : denS.snd.fst =
      SMTType.fun rho SMTType.bool)
    (X_rel : RDomCastSupported
      (⟨X, BType.set beta, hX⟩ : B.Dom) denS)
    (hcovOut : RenamingContext.CoversFV Theta
      (SMT.Term.lambda [P]
        [SMTType.fun rho SMTType.bool]
        (SMT.Term.forall [x] [rho]
          (.imp (.app (.var P) (.var x))
            (.app S (.var x))))))
    (denOut : SMT.Dom.{u})
    (hdenOut :
      ⟦(SMT.Term.lambda [P]
        [SMTType.fun rho SMTType.bool]
        (SMT.Term.forall [x] [rho]
          (.imp (.app (.var P) (.var x))
            (.app S (.var x))))).abstract Theta hcovOut⟧ˢ =
        some denOut)
    (hdenOut_type : denOut.snd.fst =
      SMTType.fun (SMTType.fun rho SMTType.bool) SMTType.bool) :
    RDomCastSupported
      (⟨X.powerset, BType.set (BType.set beta),
        powerset_mem_btype hX⟩ : B.Dom) denOut := by
  let pred : SMT.Term :=
    (.imp (.app (.var P) (.var x)) (.app S (.var x)))
  let out : SMT.Term :=
    SMT.Term.lambda [P]
      [SMTType.fun rho SMTType.bool]
      (SMT.Term.forall [x] [rho] pred)
  have typOut' : Lambda ⊢ˢ out :
      SMTType.fun (SMTType.fun rho SMTType.bool) SMTType.bool := by
    simpa [out, pred] using typOut
  obtain ⟨_, hlenP, gamma, _, _, htypeOut, typForallUpdate⟩ :=
    SMT.Typing.lambdaE typOut'
  have gamma_eq : gamma = SMTType.bool := by
    have h := (SMTType.fun.inj htypeOut).2
    exact h.symm
  subst gamma
  have updateP : Lambda.update [P]
      [SMTType.fun rho SMTType.bool] hlenP =
      Lambda.insert P (SMTType.fun rho SMTType.bool) := by
    simp only [SMT.TypeContext.update, List.length_cons, List.length_nil,
      zero_add, Nat.reduceAdd, Fin.cast_eq_self, Fin.getElem_fin,
      Fin.val_eq_zero, List.getElem_cons_zero, Fin.foldl_succ,
      Fin.foldl_zero]
  rw [updateP] at typForallUpdate
  have typForall : Lambda.insert P (SMTType.fun rho SMTType.bool) ⊢ˢ
      SMT.Term.forall [x] [rho] pred : SMTType.bool := typForallUpdate
  obtain ⟨_, _, _, _, hlenX, typPredUpdate⟩ :=
    SMT.Typing.forallE typForall
  have updateX :
      SMT.TypeContext.update
        (Lambda.insert P (SMTType.fun rho SMTType.bool))
        [x] [rho] hlenX =
      (Lambda.insert P (SMTType.fun rho SMTType.bool)).insert x rho := by
    simp only [SMT.TypeContext.update, List.length_cons, List.length_nil,
      zero_add, Nat.reduceAdd, Fin.cast_eq_self, Fin.getElem_fin,
      Fin.val_eq_zero, List.getElem_cons_zero, Fin.foldl_succ,
      Fin.foldl_zero]
  rw [updateX] at typPredUpdate
  have typPred :
      (Lambda.insert P (SMTType.fun rho SMTType.bool)).insert x rho ⊢ˢ
        pred : SMTType.bool := typPredUpdate
  rcases denS with ⟨Sval, sigmaS, hSval⟩
  dsimp at hdenS_type
  subst sigmaS
  rcases denOut with ⟨U, sigmaOut, hU⟩
  dsimp at hdenOut_type
  subst sigmaOut
  exact represented_powerset_direct_lambda hrho hX hSval hU
    (by simpa [pred] using typPred)
    (by simpa [pred] using typForall)
    x_ne_P P_not_fv_S x_not_fv_S hcovS respectsS
    (by simpa only [proof_irrel_heq] using hdenS)
    X_rel
    (by simpa [out, pred] using hcovOut)
    (by simpa [out, pred, proof_irrel_heq] using hdenOut)

set_option maxHeartbeats 3500000 in
theorem direct_scoped_contract.{u}
    (beta : BType) (rho : SMTType)
    (hrho : BType.SupportedSMT beta rho) (S : SMT.Term) :
    EncodePowTailRepScopedSpec.{u} beta S
      (SMTType.fun rho SMTType.bool) := by
  unfold EncodePowTailRepScopedSpec
  intro Lambda n used decl typS _supported bvS_used
  mstart
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_keys, rfl, rfl⟩ := pre
  mspec (Std.Do.Triple.and _
    (encodePowTail_direct_rep_spec beta rho hrho S typS
      (.setPred hrho) bvS_used)
    (direct_shape_decls rho S typS
      (n := St.env.freshvarsc) (used := St.env.usedVars)
      (decl := St.env.declarations)))
  rename_i outPair
  obtain ⟨out, sigmaOut⟩ := outPair
  mrename_i post
  mintro ∀StOut
  mpure post
  obtain ⟨opPost, shape⟩ := post
  obtain ⟨usedSub, typesSub, keysSub, path, typOut,
    preserves, semantic⟩ := opPost
  obtain ⟨x, P, outEq, sigmaEq, typesEq, declEq,
    xNeP, xNotFv, PNotFv⟩ := shape
  mpure_intro
  dsimp at outEq sigmaEq
  subst out
  subst sigmaOut
  rw [typesEq] at typesSub keysSub typOut preserves semantic ⊢
  refine ⟨usedSub, typesSub, keysSub, path, typOut, preserves,
    [], ?_, ContextGeneratedByDeclarations.refl _,
    DeclarationContextTrace.nil _, (by simp [declVars]), ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · simpa using declEq
  · intro v hv
    refine Or.inl ?_
    have hvx : v ≠ x := by
      intro h
      subst v
      exact xNotFv hv
    have hvP : v ≠ P := by
      intro h
      subst v
      exact PNotFv hv
    simpa [SMT.fv, List.mem_removeAll_iff] using
      (⟨⟨Or.inr (Or.inr (Or.inl hv)), hvx⟩, hvP⟩ :
        ((v = P ∨ v = x ∨ v ∈ SMT.fv S ∨ v = x) ∧ v ≠ x) ∧
          v ≠ P)
  · intro v hv
    have hv' :
        ((v = P ∨ v = x ∨ v ∈ SMT.fv S ∨ v = x) ∧ v ≠ x) ∧
          v ≠ P := by
      simpa [SMT.fv, List.mem_removeAll_iff] using hv
    obtain ⟨⟨hvBody, hvx⟩, hvP⟩ := hv'
    rcases hvBody with hP | hx | hvS | hx
    · exact absurd hP hvP
    · exact absurd hx hvx
    · simpa [declVars] using hvS
    · exact absurd hx hvx
  · simp [specBodies]
  · constructor
    · intro Theta hcovS ThetaNone respectsS ThetaDom X hX denS
        hdenS Xrel
      obtain ⟨Theta', hcovOut, denOut, ThetaExt, ThetaNone',
          respectsOut, ThetaDom', hdenOut, hdenOutType, resultRel⟩ :=
        semantic Theta hcovS ThetaNone respectsS ThetaDom
          X hX denS hdenS Xrel
      exact ⟨Theta', hcovOut, denOut, ThetaExt, ThetaNone',
        respectsOut, ThetaDom', (by simp [SpecBodiesTrue, specBodies]),
        hdenOut, hdenOutType, resultRel⟩
    · intro GammaSup scope Theta hcovS respectsS _specsTrue
        X hX denS hdenS hdenS_type Xrel hcovOut denOut
        _respectsOut hdenOut hdenOutType
      have respectsSBase :
          SMT.RenamingContext.RespectsTypeContextOnFV Theta St.types S :=
        fun _ _ hv hlookup =>
          respectsS hv (AList.lookup_of_subset scope.base hlookup)
      exact direct_guarded beta rho hrho S xNeP xNotFv PNotFv typOut
        hcovS respectsSBase hdenS hdenS_type Xrel hcovOut denOut
        hdenOut hdenOutType
  · simp [specBodies]
  · constructor
    · intro GammaSup scope resultBvFresh
      exact SMT.Typing.weakening scope.base typOut resultBvFresh
    · simp [ScopedSpecsTyping, specBodies]

set_option maxHeartbeats 9000000 in
/-- The option-function powerset branch records the generated graph helper
and then reuses the direct characteristic-predicate continuation. -/
theorem graph_scoped_contract.{u}
    (alpha beta : BType) (S : SMT.Term) :
    EncodePowTailRepScopedSpec.{u} (alpha ×ᴮ beta) S
      (SMTType.fun alpha.toSMTType
        (SMTType.option beta.toSMTType)) := by
  unfold EncodePowTailRepScopedSpec
  intro Lambda n used decl typS _supported bvS_used
  rw [encodePowTail_graph_eq]
  mstart
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_keys, rfl, rfl⟩ := pre
  let graphPath := castPath.graph
    (castPath.reflexive alpha.toSMTType)
    (castPath.reflexive beta.toSMTType)
  mspec (Std.Do.Triple.and _
    (Std.Do.Triple.and _
      (Std.Do.Triple.and _
        (Std.Do.Triple.and _
          (loosenAux_prf_exact_univ
            (Λ := St.types) (n := St.env.freshvarsc)
            (used := St.env.usedVars) typS bvS_used graphPath)
          (loosenAux_prf_fv_of_faithful (castPath.fvFaithful graphPath)
            (used := St.env.usedVars) (n := St.env.freshvarsc)
            (x := S) (by
              intro v hv
              exact St_keys
                (SMT.Typing.mem_context_of_mem_fv typS hv))))
        (loosenAux_prf_decls graphPath
          (decl := St.env.declarations)))
      (loosenAux_prf_types_eq graphPath))
    (SMT.loosenAux_prf_bv graphPath bvS_used))
  next out =>
  obtain ⟨helper, spec⟩ := out
  mrename_i pre
  mintro ∀St1
  mpure pre
  obtain ⟨⟨⟨⟨⟨_hn1, St1_types_sub, helper_fresh, helper_not_used,
      used_sub1, keys_sub1, preserves1, _typ_helper_insert,
      _typ_spec_insert, typ_helper, typ_spec, spec_fv, exactness⟩,
      _helper_not_used_fv, source_fv_spec, _used_sub_fv⟩,
      St1_decl_eq⟩, ⟨St1_types_exact, _⟩⟩,
      ⟨helper_used1, spec_bv_used1, _used_sub_bv⟩⟩ := pre
  mspec SMT.declareConst_addSpec_spec (x! := helper)
    (x!_spec := spec)
    (τ := SMTType.fun
      (SMTType.pair alpha.toSMTType beta.toSMTType) SMTType.bool)
    (decl := St1.env.declarations) (as := St1.env.asserts)
    (n := St1.env.freshvarsc) (Γ := St1.types)
    (used := St1.env.usedVars)
  mrename_i pre
  mintro ∀St2
  mpure pre
  obtain ⟨St2_decl_eq, St2_asserts, _St2_fvc, St2_used, St2_types⟩ := pre
  clear St2_asserts
  have typHelper2 : St2.types ⊢ˢ SMT.Term.var helper :
      SMTType.fun
        (SMTType.pair alpha.toSMTType beta.toSMTType) SMTType.bool := by
    rw [St2_types]
    exact typ_helper
  have keys2 : St2.types.keys ⊆ St2.env.usedVars := by
    rw [St2_types, St2_used]
    exact keys_sub1
  mspec direct_scoped_contract
    (alpha ×ᴮ beta)
    (SMTType.pair alpha.toSMTType beta.toSMTType)
    (BType.SupportedSMT.canonical (alpha ×ᴮ beta))
    (SMT.Term.var helper) typHelper2
    (.setPred (BType.SupportedSMT.canonical (alpha ×ᴮ beta)))
    (by simp [SMT.bv])
  rename_i outPair
  obtain ⟨out, sigmaOut⟩ := outPair
  mrename_i post
  mintro ∀St3
  mpure post
  obtain ⟨used_sub3, types_sub3, keys_sub3, path, typOut,
      preserves3, DltTail, tail_decl_eq, tail_ctx_gen,
      tail_trace, tail_fresh, tail_source_obs, tail_out_fv,
      tail_spec_fv, tail_semantics, tail_specs_typing,
      tail_scoped_typing⟩ := post
  let helperTy := SMTType.fun
    (SMTType.pair alpha.toSMTType beta.toSMTType) SMTType.bool
  let DltHelper := helperSpecChunk helper helperTy spec
  have St_sub1 : St.types ⊆ St1.types := fun v hv =>
    St1_types_sub
      (SMT.TypeContext.entries_subset_insert_of_notMem helper_fresh hv)
  have initial_sub3 : St.types ⊆ St3.types := by
    intro e he
    apply types_sub3
    rw [St2_types]
    exact St_sub1 he
  have used_sub_out : St.env.usedVars ⊆ St3.env.usedVars := by
    intro v hv
    apply used_sub3
    rw [St2_used]
    exact used_sub1 hv
  have preserves_out : ∀ v ∈ St.env.usedVars,
      v ∉ St.types → v ∉ St3.types := by
    intro v hv hnot
    apply preserves3 v
    · rw [St2_used]
      exact used_sub1 hv
    · rw [St2_types]
      exact preserves1 v hv hnot
  have helper_ctx_gen : ContextGeneratedByDeclarations St.types St1.types
      DltHelper := by
    rw [St1_types_exact]
    exact ContextGeneratedByDeclarations.insert_helper
      St.types helper helperTy spec helper_fresh
  have helper_trace : DeclarationContextTrace St.types DltHelper
      St1.types := by
    rw [St1_types_exact]
    exact DeclarationContextTrace.helperSpecChunk
      St.types helper helperTy spec helper_fresh
  have tail_ctx_gen1 : ContextGeneratedByDeclarations St1.types St3.types
      DltTail := by
    simpa [St2_types] using tail_ctx_gen
  have tail_trace1 : DeclarationContextTrace St1.types DltTail
      St3.types := by
    simpa [St2_types] using tail_trace
  have helper_scoped_typing : ScopedGeneratedTyping St.types DltHelper
      (SMT.Term.var helper) helperTy := by
    apply ScopedGeneratedTyping.of_operational helper_ctx_gen typ_helper
    intro body hbody
    simp only [DltHelper, specBodies_helperSpecChunk,
      List.mem_singleton] at hbody
    subst body
    exact typ_spec
  have typ_spec3 : St3.types ⊢ˢ spec : SMTType.bool := by
    apply SMT.Typing.weakening types_sub3
    · rw [St2_types]
      exact typ_spec
    · intro v hv hv_St3
      have hv_used2 : v ∈ St2.env.usedVars := by
        rw [St2_used]
        exact spec_bv_used1 v hv
      obtain ⟨tauv, hlookup⟩ := Option.isSome_iff_exists.mp
        (AList.lookup_isSome.mpr hv_St3)
      have hentry : (⟨v, tauv⟩ : Sigma fun _ : SMT.𝒱 => SMTType) ∈
          St3.types.entries := AList.mem_lookup_iff.mp hlookup
      rcases List.mem_append.mp (tail_ctx_gen hentry) with hbase | hdecl
      · have hv_St2 : v ∈ St2.types :=
          AList.mem_keys.mpr (List.mem_map.mpr
            ⟨⟨v, tauv⟩, hbase, rfl⟩)
        exact SMT.Typing.bv_notMem_context
          (by rw [St2_types]; exact typ_spec) v hv hv_St2
      · exact tail_fresh v
          (mem_declVars_of_mem_declEntries hdecl) hv_used2
  have combined_specs_typing : ∀ b ∈ specBodies (DltHelper ++ DltTail),
      St3.types ⊢ˢ b : SMTType.bool := by
    intro body hbody
    rw [specBodies_append, List.mem_append] at hbody
    rcases hbody with hhelper | htail
    · simp only [DltHelper, specBodies_helperSpecChunk,
        List.mem_singleton] at hhelper
      subst body
      exact typ_spec3
    · exact tail_specs_typing body htail
  have tail_scoped_typing1 : ScopedGeneratedTyping St1.types DltTail
      out sigmaOut := by
    simpa [St2_types] using tail_scoped_typing
  have combined_scoped_typing : ScopedGeneratedTyping St.types
      (DltHelper ++ DltTail) out sigmaOut :=
    ScopedGeneratedTyping.append_prefix helper_trace
      helper_scoped_typing.2 tail_scoped_typing1
  mpure_intro
  refine ⟨used_sub_out, initial_sub3, keys_sub3, path, typOut,
    preserves_out, DltHelper ++ DltTail, ?_,
    ContextGeneratedByDeclarations.append helper_ctx_gen tail_ctx_gen1,
    DeclarationContextTrace.append helper_trace tail_trace1,
    ?_, ?_, ?_, ?_, ?_, combined_specs_typing,
    combined_scoped_typing⟩
  · rw [tail_decl_eq, St2_decl_eq, St1_decl_eq]
    simp [DltHelper, helperTy, helperSpecChunk,
      List.concat_eq_append, List.append_assoc]
  · intro v hv
    rw [declVars_append, List.mem_append] at hv
    rcases hv with hhelper | htail
    · simp only [DltHelper, declVars_helperSpecChunk,
        List.mem_singleton] at hhelper
      subst v
      exact helper_not_used
    · intro hv0
      apply tail_fresh v htail
      rw [St2_used]
      exact used_sub1 hv0
  · intro v hv
    exact Or.inr ⟨spec, (by
      rw [specBodies_append, List.mem_append]
      exact Or.inl (by simp [DltHelper])), source_fv_spec hv⟩
  · intro v hv
    have hv' := tail_out_fv hv
    rw [List.mem_union_iff] at hv' ⊢
    rcases hv' with hhelper | htail
    · simp only [SMT.fv, List.mem_singleton] at hhelper
      subst v
      apply Or.inr
      rw [declVars_append, List.mem_append]
      exact Or.inl (by simp [DltHelper])
    · apply Or.inr
      rw [declVars_append, List.mem_append]
      exact Or.inr htail
  · intro body hbody v hv
    rw [specBodies_append, List.mem_append] at hbody
    rw [List.mem_union_iff]
    rcases hbody with hhelper_body | htail_body
    · simp only [DltHelper, specBodies_helperSpecChunk,
      List.mem_singleton] at hhelper_body
      subst body
      have hv' := spec_fv hv
      rw [List.mem_union_iff] at hv'
      rcases hv' with hsource | hhelper
      · exact Or.inl hsource
      · have hveq : v = helper := List.mem_singleton.mp hhelper
        subst v
        apply Or.inr
        rw [declVars_append, List.mem_append]
        exact Or.inl (by simp [DltHelper])
    · have hv' := tail_spec_fv body htail_body hv
      rw [List.mem_union_iff] at hv'
      rcases hv' with hhelper | htail
      · simp only [SMT.fv, List.mem_singleton] at hhelper
        subst v
        apply Or.inr
        rw [declVars_append, List.mem_append]
        exact Or.inl (by simp [DltHelper])
      · apply Or.inr
        rw [declVars_append, List.mem_append]
        exact Or.inr htail
  · constructor
    · intro Theta hcovS Theta_none respectsS Theta_dom
        X hX denS hdenS X_rel
      let pf : ∀ (x_ : SMT.𝒱) (H : SMT.Dom),
          ∀ v ∈ SMT.fv (SMT.Term.var x_),
            (Function.update Theta x_ (some H) v).isSome = true := by
        intro x_ H v hv
        simp only [SMT.fv, List.mem_singleton] at hv
        subst v
        simp
      obtain ⟨Phi, denHelper, hdenVar, hcovSpec, hdenSpec,
          denHelper_type, Phi_type, ⟨Phi_true, castPair⟩, _guard⟩ :=
        exactness Theta hcovS respectsS pf denS hdenS
      let ThetaHelper := Function.update Theta helper (some denHelper)
      have helper_none : Theta helper = none :=
        Theta_none helper helper_not_used
      have ThetaHelper_ext : RenamingContext.Extends ThetaHelper Theta :=
        RenamingContext.extends_update_of_none helper_none
      have hcovHelper : RenamingContext.CoversFV ThetaHelper
          (SMT.Term.var helper) := by
        intro v hv
        simp only [SMT.fv, List.mem_singleton] at hv
        subst v
        simp [ThetaHelper]
      have hdenHelper :
          ⟦(SMT.Term.var helper).abstract ThetaHelper hcovHelper⟧ˢ =
            some denHelper := by
        simpa only [ThetaHelper] using hdenVar
      have respectsS1 :
          SMT.RenamingContext.RespectsTypeContextOnFV
            Theta St1.types S :=
        respectsS.of_extends (RenamingContext.extends_refl Theta)
          St_sub1 typS
      have helper_lookup : St1.types.lookup helper = some helperTy := by
        simpa [helperTy] using SMT.Typing.varE typ_helper
      have respectsHelper1 :
          SMT.RenamingContext.RespectsTypeContextOnFV
            ThetaHelper St1.types (SMT.Term.var helper) := by
        intro v tauv hv hlookup
        simp only [SMT.fv, List.mem_singleton] at hv
        subst v
        rw [helper_lookup] at hlookup
        injection hlookup with heq
        subst tauv
        exact ⟨denHelper, by simp [ThetaHelper], by
          simpa [helperTy] using denHelper_type⟩
      have respectsSpecHelper :
          SMT.RenamingContext.RespectsTypeContextOnFV
            ThetaHelper St1.types spec :=
        SMT.RenamingContext.respects_update_helper spec_fv respectsS1
          helper_lookup (by simpa [helperTy] using denHelper_type)
      have ThetaHelper_none1 : ∀ v ∉ St1.env.usedVars,
          ThetaHelper v = none := by
        intro v hv
        by_cases hvh : v = helper
        · subst v
          exact absurd helper_used1 hv
        · simp only [ThetaHelper, Function.update_of_ne hvh]
          apply Theta_none
          intro hv0
          exact hv (used_sub1 hv0)
      have ThetaHelper_dom1 : ∀ v, ThetaHelper v ≠ none →
          v ∈ St1.types := by
        intro v hv
        by_cases hvh : v = helper
        · subst v
          exact AList.lookup_isSome.mp
            (Option.isSome_of_eq_some helper_lookup)
        · have hv0 : v ∈ St.types := Theta_dom v (by
            simpa [ThetaHelper, Function.update_of_ne hvh] using hv)
          exact AList.mem_of_subset St_sub1 hv0
      have ThetaHelper_none2 : ∀ v ∉ St2.env.usedVars,
          ThetaHelper v = none := by
        simpa [St2_used] using ThetaHelper_none1
      have ThetaHelper_dom2 : ∀ v, ThetaHelper v ≠ none →
          v ∈ St2.types := by
        simpa [St2_types] using ThetaHelper_dom1
      have respectsHelper2 :
          SMT.RenamingContext.RespectsTypeContextOnFV
            ThetaHelper St2.types (SMT.Term.var helper) := by
        simpa [St2_types] using respectsHelper1
      have denS_type :=
        SMT.RenamingContext.denote_type_of_typing_fv
          typS respectsS hcovS hdenS
      rcases denS with ⟨Sval, sigmaS0, hSval⟩
      dsimp at denS_type
      subst sigmaS0
      rcases denHelper with ⟨Hval, sigmaH, hHval⟩
      dsimp at denHelper_type
      subst sigmaH
      have X_helper_supported : RDomCastSupported
          (⟨X, BType.set (alpha ×ᴮ beta), hX⟩ : B.Dom)
          (⟨Hval, helperTy, hHval⟩ : SMT.Dom) :=
        RDomCastSupported.of_cast_to_supported X_rel
          (.setPred (BType.SupportedSMT.canonical (alpha ×ᴮ beta)))
          graphPath castPair
      obtain ⟨ThetaOut, hcovOut, denOut, ThetaOut_ext,
          ThetaOut_none, respectsOut, ThetaOut_dom, specsTail,
          hdenOut, hdenOut_type, result_rel⟩ :=
        tail_semantics.1 ThetaHelper hcovHelper ThetaHelper_none2
          respectsHelper2 ThetaHelper_dom2 X hX
          (⟨Hval, helperTy, hHval⟩ : SMT.Dom)
          hdenHelper X_helper_supported
      have specsHelper : SpecBodiesTrue ThetaHelper St1.types
          DltHelper := by
        intro body hbody
        simp only [DltHelper, specBodies_helperSpecChunk,
          List.mem_singleton] at hbody
        subst body
        exact ⟨hcovSpec, Phi, respectsSpecHelper, hdenSpec,
          Phi_type, Phi_true⟩
      have specsHelperOut : SpecBodiesTrue ThetaOut St3.types
          DltHelper :=
        specsHelper.of_extends ThetaOut_ext
          tail_trace1.entries_subset ThetaHelper_dom1
      exact ⟨ThetaOut, hcovOut, denOut,
        RenamingContext.extends_trans ThetaOut_ext ThetaHelper_ext,
        ThetaOut_none, respectsOut, ThetaOut_dom,
        specsHelperOut.append specsTail, hdenOut, hdenOut_type,
        result_rel⟩
    · intro GammaSup scope Theta hcovS respectsS specsTrue
        X hX denS hdenS hdenS_type X_rel hcovOut denOut
        respectsOut hdenOut hdenOut_type
      have helper_scope : ScopedContextExtends St.types DltHelper
          GammaSup := scope.left_of_append
      have tail_scope1 : ScopedContextExtends St1.types DltTail
          GammaSup :=
        ScopedContextExtends.right_of_generated helper_ctx_gen scope
      have tail_scope2 : ScopedContextExtends St2.types DltTail
          GammaSup := by
        simpa [St2_types] using tail_scope1
      have specsHelper : SpecBodiesTrue Theta GammaSup DltHelper :=
        specsTrue.left_of_append
      have specsTail : SpecBodiesTrue Theta GammaSup DltTail :=
        specsTrue.right_of_append
      have respectsSBase :
          SMT.RenamingContext.RespectsTypeContextOnFV Theta St.types S :=
        fun _ _ hv hlookup =>
          respectsS hv (AList.lookup_of_subset scope.base hlookup)
      let pf : ∀ (x_ : SMT.𝒱) (H : SMT.Dom),
          ∀ v ∈ SMT.fv (SMT.Term.var x_),
            (Function.update Theta x_ (some H) v).isSome = true := by
        intro x_ H v hv
        simp only [SMT.fv, List.mem_singleton] at hv
        subst v
        simp
      obtain ⟨_PhiW, _helperW, _hdenVarW, _hcovSpecW,
          _hdenSpecW, _helperW_type, _PhiW_type, _castW, guard⟩ :=
        exactness Theta hcovS respectsSBase pf denS hdenS
      have helper_lookup_sup : GammaSup.lookup helper = some helperTy :=
        helper_scope.lookup_of_declared (by
          simp [DltHelper, helperTy, declEntries_helperSpecChunk])
      have helper_observed := tail_source_obs helper
        (show helper ∈ SMT.fv (SMT.Term.var helper) by simp [SMT.fv])
      obtain ⟨helperVal, hhelperVal, helperVal_type⟩ :
          ∃ helperVal : SMT.Dom,
            Theta helper = some helperVal ∧
            helperVal.snd.fst = helperTy := by
        rcases helper_observed with hhelperOut |
            ⟨body, hbody, hhelperBody⟩
        · have helperSome : (Theta helper).isSome = true :=
            hcovOut helper hhelperOut
          obtain ⟨helperVal, hhelperVal⟩ :=
            Option.isSome_iff_exists.mp helperSome
          obtain ⟨d, hd, hdtype⟩ :=
            respectsOut hhelperOut helper_lookup_sup
          rw [hhelperVal] at hd
          injection hd with heq
          subst d
          exact ⟨helperVal, hhelperVal, hdtype⟩
        · obtain ⟨hcovBody, denBody, respectsBody,
              hdenBody, denBody_type, denBody_true⟩ :=
            specsTail body hbody
          have helperSome : (Theta helper).isSome = true :=
            hcovBody helper hhelperBody
          obtain ⟨helperVal, hhelperVal⟩ :=
            Option.isSome_iff_exists.mp helperSome
          obtain ⟨d, hd, hdtype⟩ :=
            respectsBody hhelperBody helper_lookup_sup
          rw [hhelperVal] at hd
          injection hd with heq
          subst d
          exact ⟨helperVal, hhelperVal, hdtype⟩
      have respectsHelper :
          SMT.RenamingContext.RespectsTypeContextOnFV
            Theta GammaSup (SMT.Term.var helper) := by
        intro v tauv hv hlookup
        simp only [SMT.fv, List.mem_singleton] at hv
        subst v
        rw [helper_lookup_sup] at hlookup
        injection hlookup with heq
        subst tauv
        exact ⟨helperVal, hhelperVal, helperVal_type⟩
      have updateEq : Function.update Theta helper (some helperVal) =
          Theta := by
        rw [← hhelperVal]
        exact Function.update_eq_self helper Theta
      have specTrue := specsHelper spec (by
        simp [DltHelper, specBodies_helperSpecChunk])
      obtain ⟨hcovSpec, denSpec, _respectsSpec, hdenSpec,
          _denSpec_type, denSpec_true⟩ := specTrue
      have hcovSpecUpdate : RenamingContext.CoversFV
          (Function.update Theta helper (some helperVal)) spec := by
        rw [updateEq]
        exact hcovSpec
      obtain ⟨_specSome, guardTrue⟩ :=
        guard helperVal (by simpa [helperTy] using helperVal_type)
          hcovSpecUpdate
      have hdenSpecUpdate :
          ⟦spec.abstract (Function.update Theta helper (some helperVal))
            hcovSpecUpdate⟧ˢ = some denSpec := by
        simpa only [updateEq, proof_irrel_heq] using hdenSpec
      have castPair := guardTrue hdenSpecUpdate denSpec_true
      have hcovHelper : RenamingContext.CoversFV Theta
          (SMT.Term.var helper) := by
        intro v hv
        simp only [SMT.fv, List.mem_singleton] at hv
        subst v
        rw [hhelperVal]
        rfl
      have hdenHelper :
          ⟦(SMT.Term.var helper).abstract Theta hcovHelper⟧ˢ =
            some helperVal := by
        rw [SMT.Term.abstract]
        simp only [SMT.denote]
        congr 1
        exact Option.get_of_eq_some _ hhelperVal
      rcases denS with ⟨Sval, sigmaS0, hSval⟩
      dsimp at hdenS_type
      subst sigmaS0
      rcases helperVal with ⟨Hval, sigmaH, hHval⟩
      dsimp [helperTy] at helperVal_type
      subst sigmaH
      have X_helper_supported : RDomCastSupported
          (⟨X, BType.set (alpha ×ᴮ beta), hX⟩ : B.Dom)
          (⟨Hval, helperTy, hHval⟩ : SMT.Dom) :=
        RDomCastSupported.of_cast_to_supported X_rel
          (.setPred (BType.SupportedSMT.canonical (alpha ×ᴮ beta)))
          graphPath castPair
      exact tail_semantics.2 GammaSup tail_scope2 Theta hcovHelper
        respectsHelper specsTail X hX
        (⟨Hval, helperTy, hHval⟩ : SMT.Dom)
        hdenHelper (by simp [helperTy]) X_helper_supported hcovOut
        denOut respectsOut hdenOut hdenOut_type

/-- Select the declaration-aware powerset continuation from the supported
representation carried by the encoded operand. -/
theorem supported_scoped_contract.{u}
    (beta : BType) (S : SMT.Term) (sigmaS : SMTType)
    (supported : BType.SupportedSMT (BType.set beta) sigmaS) :
    EncodePowTailRepScopedSpec.{u} beta S sigmaS := by
  cases supported with
  | @setPred _ rho hrho =>
      exact direct_scoped_contract beta rho hrho S
  | optionFun alpha gamma =>
      exact graph_scoped_contract alpha gamma S

private theorem encodeTerm_pow_via_tail_scoped
    (S : B.Term) (E : B.Env) :
    encodeTerm (B.Term.pow S) E = (do
      let ⟨Senc, sigmaS⟩ ← encodeTerm S E
      encodePowTail Senc sigmaS) := by
  rfl

set_option maxHeartbeats 12000000 in
theorem encodeTerm_rep_scoped.pow_case_from.{u}
    (S : B.Term)
    (S_ih : EncodeTermRepIH.{u} S)
    (S_scoped : EncodeTermRepScopedFromIH.{u} S)
    (E : B.Env) {Lambda : SMT.TypeContext} {alpha : BType}
    (typ_t : E.context ⊢ᴮ B.Term.pow S : alpha)
    {Delta : B.RenamingContext.Context}
    (Delta_fv : ∀ v ∈ B.fv (B.Term.pow S),
      (Delta v).isSome = true)
    {Delta0 : SMT.RenamingContext.Context.{u}}
    (related : RValuationCastSupportedOnFV Delta Delta0
      (B.Term.pow S))
    {used : List SMT.𝒱}
    (Delta0_none : ∀ v ∉ used, Delta0 v = none)
    (Delta0_dom : ∀ v, Delta0 v ≠ none → v ∈ Lambda)
    {T : ZFSet.{u}} {hT : T ∈ ⟦alpha⟧ᶻ}
    (den_t : ⟦(B.Term.pow S).abstract Delta Delta_fv⟧ᴮ =
      some ⟨T, ⟨alpha, hT⟩⟩)
    (vars_used : ∀ v ∈ (B.Term.pow S).vars, v ∈ used)
    (Lambda_inv : ∀ v ∈ (B.Term.pow S).vars,
      v ∈ Lambda → v ∈ E.context)
    (bv_nodup : (B.bv (B.Term.pow S)).Nodup)
    (respects : B.RenamingContext.RespectsTypeContextOnFV
      Delta0 Lambda (B.Term.pow S))
    (fv_in_Lambda : ∀ v ∈ B.fv (B.Term.pow S), v ∈ Lambda)
    (wf : B.RenWF E.context Delta)
    {Base : SMT.TypeContext} {Dpre : SMT.Chunk}
    (input_envelope : DeclarationContextEnvelope Base Dpre Lambda)
    (fv_in_Base : ∀ v ∈ B.fv (B.Term.pow S), v ∈ Base)
    (Dpre_typing : ScopedSpecsTyping Base Dpre)
    {n : ℕ} {decl : SMT.Chunk} :
    ⦃fun ⟨E0, Lambda'⟩ ↦
      ⌜Lambda' = Lambda ∧ E0.freshvarsc = n ∧
        Lambda.keys ⊆ E0.usedVars ∧ E0.usedVars = used ∧
        E0.declarations = decl⌝ ⦄
    encodeTerm (B.Term.pow S) E
    ⦃⇓? (⟨t', sigma⟩ : SMT.Term × SMTType) ⟨E', Gamma'⟩ =>
      ⌜EncodeTermRepScopedPostFrom.{u} (B.Term.pow S) E alpha
        Base Dpre Lambda decl t' sigma E' Gamma'⌝ ⦄ := by
  mstart
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_keys, St_used_eq, St_decl_eq⟩ := pre
  rw [encodeTerm_pow_via_tail_scoped]
  obtain ⟨beta, rfl, typ_S⟩ := B.Typing.powE typ_t
  obtain ⟨X, hX, den_S, rfl⟩ :=
    B.denote_pow_inv_rep Delta_fv den_t
  have fv_S_sub : B.fv S ⊆ B.fv (B.Term.pow S) := by
    intro v hv
    simpa [B.fv] using hv

  mspec (Std.Do.Triple.and _
    (Std.Do.Triple.and _
      (S_ih E typ_S
        (fun v hv => Delta_fv v (fv_S_sub hv))
        (related.mono_fv fv_S_sub)
        Delta0_none Delta0_dom den_S
        (fun v hv => vars_used v (by
          simpa [B.Term.vars, B.fv, B.bv] using hv))
        (fun v hv => Lambda_inv v (by
          simpa [B.Term.vars, B.fv, B.bv] using hv))
        (by simpa [B.bv] using bv_nodup)
        (respects.mono_fv fv_S_sub)
        (fun v hv => fv_in_Lambda v (fv_S_sub hv)) wf
        (n := St.env.freshvarsc))
      (S_scoped E typ_S
        (fun v hv => Delta_fv v (fv_S_sub hv))
        (related.mono_fv fv_S_sub)
        Delta0_none Delta0_dom den_S
        (fun v hv => vars_used v (by
          simpa [B.Term.vars, B.fv, B.bv] using hv))
        (fun v hv => Lambda_inv v (by
          simpa [B.Term.vars, B.fv, B.bv] using hv))
        (by simpa [B.bv] using bv_nodup)
        (respects.mono_fv fv_S_sub)
        (fun v hv => fv_in_Lambda v (fv_S_sub hv)) wf
        input_envelope
        (fun v hv => fv_in_Base v (fv_S_sub hv))
        Dpre_typing (n := St.env.freshvarsc)
        (decl := St.env.declarations)))
    (encodeTerm_bv_used E (t := S)
      (used := St.env.usedVars) (n := St.env.freshvarsc)
      (decl := St.env.declarations)))
  clear S_ih S_scoped
  rename_i out_S
  obtain ⟨Senc, sigmaS⟩ := out_S
  mrename_i post_S
  mintro ∀StS
  mpure post_S
  dsimp at post_S
  obtain ⟨⟨S_post, S_scoped_post⟩, bv_Senc_used,
      _S_used_sub_struct, DltS_struct, S_decl_struct,
      S_delta_ok⟩ := post_S
  obtain ⟨DltS, S_decl_eq, S_trace, S_envelope, S_sc_total,
      S_guard, S_specs_op, S_sc_typing⟩ := S_scoped_post
  have DltS_eq : DltS = DltS_struct := by
    rw [S_decl_eq, St_decl_eq] at S_decl_struct
    exact (List.append_right_inj decl).mp S_decl_struct
  subst DltS_struct
  obtain ⟨used_sub_S, types_sub_S, keys_sub_S, covers_S,
      _path_S, typ_Senc, _shape_S, preserves_S,
      DeltaS, hcov_Senc, DeltaS_ext, _related_S, DeltaS_none,
      _respects_S, target_respects_Senc, DeltaS_dom,
      denSenc, hden_Senc, hdenSenc_type, S_rel,
      _S_total_old⟩ := S_post
  rcases denSenc with ⟨Sval, sigmaSden, hSval⟩
  dsimp at hdenSenc_type
  subst sigmaSden
  have supported_S :
      BType.SupportedSMT (BType.set beta) sigmaS := S_rel.supported

  mspec supported_scoped_contract beta Senc sigmaS supported_S
    typ_Senc supported_S bv_Senc_used
  rename_i outPow
  obtain ⟨PowEnc, sigmaPow⟩ := outPow
  mrename_i postPow
  mintro ∀StPow
  mpure postPow
  obtain ⟨used_sub_Pow, types_sub_Pow, keys_sub_Pow, path_Pow,
      typ_PowEnc, preserves_Pow, DltPow, Pow_decl_eq, Pow_ctx,
      Pow_trace, Pow_decl_fresh, Pow_obs, Pow_fv_dep,
      Pow_specs_fv_dep, Pow_sem, Pow_specs_op,
      _Pow_sc_typing⟩ := postPow
  obtain ⟨Pow_envelope, Pow_sc_typing_clean⟩ :=
    EncodeTermRepresentedScopedUnion.pair_helper_typing
      S_envelope Pow_trace typ_Senc typ_PowEnc Pow_specs_op
      S_sc_typing Pow_fv_dep Pow_specs_fv_dep
  mpure_intro
  refine ⟨DltS ++ DltPow, ?_,
    DeclarationContextTrace.append S_trace Pow_trace,
    (by simpa [List.append_assoc] using Pow_envelope),
    ?_, ?_, ?_, ?_⟩
  · simpa [S_decl_eq, St_decl_eq, List.append_assoc] using Pow_decl_eq
  · intro Delta_alt Delta_fv_alt Delta0_alt related_alt wf_alt
      Delta0_alt_none respects_alt Delta0_alt_dom
      T_alt hT_alt den_t_alt
    obtain ⟨X_alt, hX_alt, den_S_alt, rfl⟩ :=
      B.denote_pow_inv_rep Delta_fv_alt den_t_alt
    have Delta0_alt_none_S : ∀ v ∉ StS.env.usedVars,
        Delta0_alt v = none := by
      intro v hv
      by_contra hne
      have hv_St := Delta0_alt_dom v hne
      have hv_used : v ∈ used := by
        rw [← St_used_eq]
        exact St_keys hv_St
      exact hv (used_sub_S hv_used)
    obtain ⟨DeltaS_alt, hcov_Senc_alt, denSenc_alt,
        DeltaS_alt_ext, _related_S_alt, DeltaS_alt_none,
        _respects_S_alt, target_respects_Senc_alt,
        DeltaS_alt_dom, specsS_alt, hden_Senc_alt,
        hdenSenc_alt_type, S_alt_rel⟩ :=
      S_sc_total Delta_alt
        (fun v hv => Delta_fv_alt v (fv_S_sub hv))
        Delta0_alt (related_alt.mono_fv fv_S_sub) wf_alt
        Delta0_alt_none_S (respects_alt.mono_fv fv_S_sub)
        Delta0_alt_dom X_alt hX_alt den_S_alt
    obtain ⟨goodPow, _guardPow⟩ := Pow_sem
    obtain ⟨DeltaPow_alt, hcov_PowEnc_alt, denPow_alt,
        DeltaPow_alt_ext, DeltaPow_alt_none,
        target_respects_PowEnc_alt, DeltaPow_alt_dom,
        specsPow_alt, hden_PowEnc_alt, hdenPow_alt_type,
        Pow_alt_rel⟩ :=
      goodPow DeltaS_alt hcov_Senc_alt DeltaS_alt_none
        target_respects_Senc_alt DeltaS_alt_dom X_alt hX_alt
        denSenc_alt hden_Senc_alt S_alt_rel
    have DeltaPow_alt_ext0 :=
      RenamingContext.extends_trans DeltaPow_alt_ext DeltaS_alt_ext
    have types_sub0 : St.types ⊆ StPow.types :=
      fun _ h => types_sub_Pow (types_sub_S h)
    have specsS_final : SpecBodiesTrue
        DeltaPow_alt StPow.types DltS :=
      specsS_alt.of_extends DeltaPow_alt_ext
        types_sub_Pow DeltaS_alt_dom
    refine ⟨DeltaPow_alt, hcov_PowEnc_alt, denPow_alt,
      DeltaPow_alt_ext0, related_alt.of_extends DeltaPow_alt_ext0,
      DeltaPow_alt_none, ?_, target_respects_PowEnc_alt,
      DeltaPow_alt_dom, specsS_final.append specsPow_alt,
      hden_PowEnc_alt, hdenPow_alt_type, ?_⟩
    · exact respects_alt.of_extends DeltaPow_alt_ext0 types_sub0
        (fun _ h => h) fv_in_Lambda
    · simpa only [proof_irrel_heq] using Pow_alt_rel
  · intro GammaSup GammaScope Delta_alt Delta_fv_alt Theta
      related_alt wf_alt respectsB respectsSMT specsTrue
      T_alt hT_alt den_alt hcovOut denOut hdenOut hdenOut_type
    have full_scope : ScopedContextExtends Base
        ((Dpre ++ DltS) ++ DltPow) GammaSup := by
      simpa [List.append_assoc] using GammaScope
    have full_specs : SpecBodiesTrue Theta GammaSup
        ((Dpre ++ DltS) ++ DltPow) := by
      simpa [List.append_assoc] using specsTrue
    have S_scope : ScopedContextExtends Base
        (Dpre ++ DltS) GammaSup := full_scope.left_of_append
    have S_specs_true : SpecBodiesTrue Theta GammaSup
        (Dpre ++ DltS) := full_specs.left_of_append
    have Pow_specs_true : SpecBodiesTrue Theta GammaSup DltPow :=
      full_specs.right_of_append
    obtain ⟨X_alt, hX_alt, den_S_alt, rfl⟩ :=
      B.denote_pow_inv_rep Delta_fv_alt den_alt
    have hcovS_target : RenamingContext.CoversFV Theta Senc := by
      intro v hv
      rcases Pow_obs v hv with hout | ⟨body, hbody, hvbody⟩
      · exact hcovOut v hout
      · obtain ⟨hcovBody, _d, _resp, _hden, _hty, _htrue⟩ :=
          Pow_specs_true body hbody
        exact hcovBody v hvbody
    have respectsS_sup : SMT.RenamingContext.RespectsTypeContextOnFV
        Theta GammaSup Senc := by
      intro v xi hv hlookup
      rcases Pow_obs v hv with hout | ⟨body, hbody, hvbody⟩
      · exact respectsSMT hout hlookup
      · obtain ⟨_hcov, _d, respBody, _hden, _hty, _htrue⟩ :=
          Pow_specs_true body hbody
        exact respBody hvbody hlookup
    obtain ⟨PowCore, Pow_clean_trace, PowCore_sub_StPow⟩ :=
      Pow_envelope
    have PowCore_sub_sup : PowCore ⊆ GammaSup := by
      intro e he
      exact full_scope (Pow_clean_trace.context_generated he)
    have S_scope_Core : ScopedContextExtends Base
        (Dpre ++ DltS) PowCore :=
      Pow_clean_trace.scoped_extends.left_of_append
    have S_bv_fresh_Core : ∀ v ∈ SMT.bv Senc, v ∉ PowCore := by
      intro v hv hvCore
      exact preserves_Pow v (bv_Senc_used v hv)
        (SMT.Typing.bv_notMem_context typ_Senc v hv)
        (AList.mem_of_subset PowCore_sub_StPow hvCore)
    have typS_Core : PowCore ⊢ˢ Senc : sigmaS :=
      S_sc_typing.1 PowCore S_scope_Core S_bv_fresh_Core
    have respectsS_Core : SMT.RenamingContext.RespectsTypeContextOnFV
        Theta PowCore Senc := respectsS_sup.of_super PowCore_sub_sup
    obtain ⟨denS_target, hdenS_target, hdenS_target_type⟩ :=
      SMT.RenamingContext.denote_exists_of_typing_fv
        typS_Core respectsS_Core hcovS_target
    have S_target_rel := S_guard GammaSup S_scope Delta_alt
      (fun v hv => Delta_fv_alt v (fv_S_sub hv)) Theta
      (related_alt.mono_fv fv_S_sub) wf_alt
      (respectsB.mono_fv fv_S_sub) respectsS_sup
      S_specs_true X_alt hX_alt den_S_alt
      hcovS_target denS_target hdenS_target hdenS_target_type
    have respectsS_StPow : SMT.RenamingContext.RespectsTypeContextOnFV
        Theta StPow.types Senc :=
      respectsS_Core.of_extends (RenamingContext.extends_refl Theta)
        PowCore_sub_StPow typS_Core
    have dependency_mem_Core :
        ∀ {v}, v ∈ SMT.fv Senc ∪ declVars DltPow → v ∈ PowCore := by
      intro v hv
      rw [List.mem_union_iff] at hv
      rcases hv with hvS | hvdecl
      · exact SMT.Typing.mem_context_of_mem_fv typS_Core hvS
      · apply Pow_clean_trace.declVar_mem
        rw [declVars_append, List.mem_append]
        exact Or.inr hvdecl
    have typPow_Core : PowCore ⊢ˢ PowEnc : sigmaPow :=
      SMT.Typing.strengthening_of_fv_subset PowCore_sub_StPow
        typ_PowEnc (fun v hv => dependency_mem_Core (Pow_fv_dep hv))
    have respectsPow_Core : SMT.RenamingContext.RespectsTypeContextOnFV
        Theta PowCore PowEnc := respectsSMT.of_super PowCore_sub_sup
    have respectsPow_StPow : SMT.RenamingContext.RespectsTypeContextOnFV
        Theta StPow.types PowEnc :=
      respectsPow_Core.of_extends (RenamingContext.extends_refl Theta)
        PowCore_sub_StPow typPow_Core
    have Pow_specs_StPow : SpecBodiesTrue Theta StPow.types DltPow := by
      intro body hbody
      obtain ⟨hcovBody, denBody, respectsBodySup, hdenBody,
          hdenBodyType, hdenBodyTrue⟩ := Pow_specs_true body hbody
      have typBodyCore : PowCore ⊢ˢ body : SMTType.bool :=
        SMT.Typing.strengthening_of_fv_subset PowCore_sub_StPow
          (Pow_specs_op body hbody)
          (fun v hv => dependency_mem_Core
            (Pow_specs_fv_dep body hbody hv))
      have respectsBodyCore :
          SMT.RenamingContext.RespectsTypeContextOnFV
            Theta PowCore body :=
        respectsBodySup.of_super PowCore_sub_sup
      have respectsBodyStPow :
          SMT.RenamingContext.RespectsTypeContextOnFV
            Theta StPow.types body :=
        respectsBodyCore.of_extends
          (RenamingContext.extends_refl Theta)
          PowCore_sub_StPow typBodyCore
      exact ⟨hcovBody, denBody, respectsBodyStPow, hdenBody,
        hdenBodyType, hdenBodyTrue⟩
    obtain ⟨_goodPow, guardPow⟩ := Pow_sem
    have result_rel := guardPow StPow.types
      Pow_trace.scoped_extends Theta hcovS_target respectsS_StPow
      Pow_specs_StPow X_alt hX_alt denS_target hdenS_target
      hdenS_target_type S_target_rel hcovOut denOut
      respectsPow_StPow hdenOut hdenOut_type
    simpa only [proof_irrel_heq] using result_rel
  · intro body hbody
    rw [specBodies_append, List.mem_append] at hbody
    rcases hbody with hSbody | hPowbody
    · exact typing_weakening_generated types_sub_Pow Pow_ctx
        Pow_decl_fresh (S_specs_op body hSbody)
        (fun v hv => S_delta_ok.2 body hSbody v hv)
    · exact Pow_specs_op body hPowbody
  · simpa [List.append_assoc] using Pow_sc_typing_clean

end EncodeTermRepresentedScopedSet
