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

end EncodeTermRepresentedScopedSet
