import SMT.Reasoning.Basic.EncodeTermRepresentedSet
import SMT.Reasoning.Basic.EncodeTermRepresentedBinaryExists
import SMT.Reasoning.Basic.EncodeTermRepresentedLambda

open Std.Do B SMT ZFSet Classical

/-! # Representation-aware Cartesian products -/

theorem cprod_mem_btype.{u} {alpha beta : BType} {X Y : ZFSet.{u}}
    (hX : X ∈ ⟦BType.set alpha⟧ᶻ)
    (hY : Y ∈ ⟦BType.set beta⟧ᶻ) :
    X.prod Y ∈ ⟦BType.set (alpha ×ᴮ beta)⟧ᶻ := by
  rw [BType.toZFSet, ZFSet.mem_powerset] at hX hY ⊢
  intro z hz
  rw [ZFSet.mem_prod] at hz
  obtain ⟨x, hx, y, hy, rfl⟩ := hz
  dsimp [BType.toZFSet]
  rw [ZFSet.pair_mem_prod]
  exact ⟨hX hx, hY hy⟩

theorem B.denote_cprod_inv_rep.{u}
    {S T : B.Term} {alpha beta : BType}
    {Xi : B.RenamingContext.Context}
    (Xi_fv : ∀ v ∈ B.fv (B.Term.cprod S T),
      (Xi v).isSome = true)
    {U : ZFSet.{u}}
    {hU : U ∈ ⟦BType.set (alpha ×ᴮ beta)⟧ᶻ}
    (hden : ⟦(B.Term.cprod S T).abstract Xi Xi_fv⟧ᴮ =
      some ⟨U, BType.set (alpha ×ᴮ beta), hU⟩) :
    ∃ (X Y : ZFSet.{u})
      (hX : X ∈ ⟦BType.set alpha⟧ᶻ)
      (hY : Y ∈ ⟦BType.set beta⟧ᶻ),
      ⟦S.abstract Xi (fun v hv => Xi_fv v (by
        simpa [B.fv] using (Or.inl hv :
          v ∈ B.fv S ∨ v ∈ B.fv T)))⟧ᴮ =
          some ⟨X, BType.set alpha, hX⟩ ∧
      ⟦T.abstract Xi (fun v hv => Xi_fv v (by
        simpa [B.fv] using (Or.inr hv :
          v ∈ B.fv S ∨ v ∈ B.fv T)))⟧ᴮ =
          some ⟨Y, BType.set beta, hY⟩ ∧
      U = X.prod Y := by
  rw [B.Term.abstract, B.denote, Option.pure_def,
    Option.bind_eq_bind, Option.bind_eq_some_iff] at hden
  obtain ⟨⟨X, tauX, hX⟩, hdenX, hrest⟩ := hden
  cases tauX <;> first
    | rw [Option.bind_eq_some_iff] at hrest
    | exact absurd hrest (by simp)
  rename_i gammaX
  obtain ⟨⟨Y, tauY, hY⟩, hdenY, hout⟩ := hrest
  cases tauY <;> first
    | rw [Option.some_inj] at hout
    | exact absurd hout (by simp)
  rename_i gammaY
  injection hout with hvalue htype
  subst U
  simp only [heq_eq_eq, PSigma.mk.injEq, BType.set.injEq,
    BType.prod.injEq] at htype
  obtain ⟨⟨hgammaX, hgammaY⟩, _⟩ := htype
  subst gammaX
  subst gammaY
  refine ⟨X, Y, hX, hY, ?_, ?_, rfl⟩
  · simpa only [proof_irrel_heq] using hdenX
  · simpa only [proof_irrel_heq] using hdenY

private theorem erase_insert_ne_rep_cprod
    {a b : SMT.𝒱} {tau : SMTType} {ctx : SMT.TypeContext}
    (hab : a ≠ b) :
    (ctx.insert b tau).erase a = (ctx.erase a).insert b tau := by
  apply AList.ext
  show List.kerase a (AList.insert b tau ctx).entries =
    (AList.insert b tau (ctx.erase a)).entries
  rw [AList.entries_insert, AList.entries_insert]
  change List.kerase a (⟨b, tau⟩ :: List.kerase b ctx.entries) =
    ⟨b, tau⟩ :: List.kerase b (List.kerase a ctx.entries)
  rw [List.kerase_cons_ne (by simpa using hab), List.kerase_kerase]

private theorem erase_insert_self_rep_cprod
    {a : SMT.𝒱} {tau : SMTType} {ctx : SMT.TypeContext}
    (ha : a ∉ ctx) : (ctx.insert a tau).erase a = ctx := by
  apply AList.ext
  show List.kerase a (AList.insert a tau ctx).entries = ctx.entries
  rw [AList.entries_insert_of_notMem ha]
  exact List.kerase_cons_eq rfl

private theorem erase_three_rep_cprod
    {p a b : SMT.𝒱} {tauP tauA tauB : SMTType}
    {ctx : SMT.TypeContext}
    (hp : p ∉ ctx) (ha : a ∉ ctx.insert p tauP)
    (hb : b ∉ (ctx.insert p tauP).insert a tauA) :
    let ctx3 := ((ctx.insert p tauP).insert a tauA).insert b tauB
    AList.erase b (AList.erase a (AList.erase p ctx3)) =
      ctx := by
  dsimp
  have hpa : p ≠ a := by
    intro h
    subst a
    exact ha (by simp)
  have hpb : p ≠ b := by
    intro h
    subst b
    exact hb (by simp)
  have hab : a ≠ b := by
    intro h
    subst b
    exact hb (by simp)
  have ha0 : a ∉ ctx := by
    intro h
    exact ha (by simp [h])
  have hb0 : b ∉ ctx := by
    intro h
    exact hb (by simp [h])
  rw [erase_insert_ne_rep_cprod hpb,
    erase_insert_ne_rep_cprod hpa,
    erase_insert_self_rep_cprod hp,
    erase_insert_ne_rep_cprod hab,
    erase_insert_self_rep_cprod ha0,
    erase_insert_self_rep_cprod hb0]

private def encodeCprodTail (A B : SMT.Term)
    (alpha beta : SMTType) : Encoder (SMT.Term × SMTType) := do
  let p ← freshVar (.pair alpha beta)
  let a ← freshVar alpha
  let b ← freshVar beta
  SMT.eraseFromContext p
  SMT.eraseFromContext a
  SMT.eraseFromContext b
  let body := .and (.app A (.var a))
    (.and (.app B (.var b))
      (.eq (.var p) (.pair (.var a) (.var b))))
  return (SMT.Term.lambda [p] [.pair alpha beta]
      (.exists [a, b] [alpha, beta] body),
    SMTType.fun (.pair alpha beta) .bool)

private theorem encodeTerm_cprod_via_tail
    (S T : B.Term) (E : B.Env) :
    encodeTerm (B.Term.cprod S T) E = (do
      let ⟨Senc, .fun alpha .bool⟩ ← encodeTerm S E |
        throw s!"encodeTerm:cprod: Expected a set, got {← encodeTerm S E}"
      let ⟨Tenc, .fun beta .bool⟩ ← encodeTerm T E |
        throw s!"encodeTerm:cprod: Expected a set, got {← encodeTerm T E}"
      encodeCprodTail Senc Tenc alpha beta) := by
  rfl

private theorem encodeCprodTail_shape_decls
    (A B : SMT.Term) (alpha beta : SMTType)
    {Lambda : SMT.TypeContext} {n : ℕ} {used : List SMT.𝒱}
    {decl : SMT.Chunk} :
    ⦃fun ⟨env, Lambda'⟩ =>
      ⌜Lambda' = Lambda ∧ env.freshvarsc = n ∧
        Lambda.keys ⊆ env.usedVars ∧ env.usedVars = used ∧
        env.declarations = decl⌝⦄
    encodeCprodTail A B alpha beta
    ⦃⇓? ⟨out, sigmaOut⟩ ⟨env', Gamma'⟩ =>
      ⌜∃ p a b : SMT.𝒱,
        out = .lambda [p] [.pair alpha beta]
          (.exists [a, b] [alpha, beta]
            (.and (.app A (.var a))
              (.and (.app B (.var b))
                (.eq (.var p) (.pair (.var a) (.var b)))))) ∧
        sigmaOut = .fun (.pair alpha beta) .bool ∧
        Gamma' = Lambda ∧ env'.declarations = decl ∧
        p ∉ Lambda ∧ a ∉ Lambda ∧ b ∉ Lambda ∧
        p ≠ a ∧ p ≠ b ∧ a ≠ b⌝⦄ := by
  unfold encodeCprodTail
  mstart
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_keys, rfl, rfl⟩ := pre
  mspec (Std.Do.Triple.and _
    (SMT.freshVar_spec (Γ := St.types)
      (τ := SMTType.pair alpha beta)
      (n := St.env.freshvarsc) (used := St.env.usedVars))
    (SMT.freshVar_decls
      (τ := SMTType.pair alpha beta)
      (decl := St.env.declarations)))
  next p =>
    mrename_i postP
    mintro ∀StP
    mpure postP
    dsimp at postP
    obtain ⟨⟨StP_types, p_fresh, StP_fresh, StP_used,
      p_not_used⟩, StP_decl⟩ := postP
    mspec (Std.Do.Triple.and _
      (SMT.freshVar_spec (Γ := StP.types) (τ := alpha)
        (n := StP.env.freshvarsc) (used := StP.env.usedVars))
      (SMT.freshVar_decls (τ := alpha)
        (decl := StP.env.declarations)))
    next a =>
      mrename_i postA
      mintro ∀StA
      mpure postA
      dsimp at postA
      obtain ⟨⟨StA_types, a_fresh, StA_fresh, StA_used,
        a_not_used⟩, StA_decl⟩ := postA
      mspec (Std.Do.Triple.and _
        (SMT.freshVar_spec (Γ := StA.types) (τ := beta)
          (n := StA.env.freshvarsc) (used := StA.env.usedVars))
        (SMT.freshVar_decls (τ := beta)
          (decl := StA.env.declarations)))
      next b =>
        mrename_i postB
        mintro ∀StB
        mpure postB
        dsimp at postB
        obtain ⟨⟨StB_types, b_fresh, StB_fresh, StB_used,
          b_not_used⟩, StB_decl⟩ := postB
        mspec (Std.Do.Triple.and _ SMT.eraseFromContext_spec
          (SMT.eraseFromContext_decls
            (decl := StB.env.declarations)))
        mrename_i postEP
        mintro ∀StEP
        mpure postEP
        dsimp at postEP
        obtain ⟨⟨StEP_types, StEP_fresh, StEP_used⟩,
          StEP_decl⟩ := postEP
        mspec (Std.Do.Triple.and _ SMT.eraseFromContext_spec
          (SMT.eraseFromContext_decls
            (decl := StEP.env.declarations)))
        mrename_i postEA
        mintro ∀StEA
        mpure postEA
        dsimp at postEA
        obtain ⟨⟨StEA_types, StEA_fresh, StEA_used⟩,
          StEA_decl⟩ := postEA
        mspec (Std.Do.Triple.and _ SMT.eraseFromContext_spec
          (SMT.eraseFromContext_decls
            (decl := StEA.env.declarations)))
        mrename_i postEB
        mintro ∀StEB
        mpure postEB
        dsimp at postEB
        obtain ⟨⟨StEB_types, StEB_fresh, StEB_used⟩,
          StEB_decl⟩ := postEB
        have a_fresh0 : a ∉ St.types.insert p
            (SMTType.pair alpha beta) := by
          simpa [StP_types] using a_fresh
        have b_fresh0 : b ∉
            (St.types.insert p (SMTType.pair alpha beta)).insert
              a alpha := by
          simpa [StA_types, StP_types] using b_fresh
        have StEB_types_final : StEB.types = St.types := by
          rw [StEB_types, StEA_types, StEP_types,
            StB_types, StA_types, StP_types]
          exact erase_three_rep_cprod p_fresh a_fresh0 b_fresh0
        have StEB_decl_final :
            StEB.env.declarations = St.env.declarations := by
          rw [StEB_decl, StEA_decl, StEP_decl,
            StB_decl, StA_decl, StP_decl]
        have hp_ne_a : p ≠ a := by
          intro h
          subst a
          exact a_fresh0 (by simp)
        have hp_ne_b : p ≠ b := by
          intro h
          subst b
          exact b_fresh0 (by simp)
        have ha_ne_b : a ≠ b := by
          intro h
          subst b
          exact b_fresh0 (by simp)
        have a_fresh_ctx : a ∉ St.types := by
          intro h
          exact a_fresh0 (by simp [h])
        have b_fresh_ctx : b ∉ St.types := by
          intro h
          exact b_fresh0 (by simp [h])
        mspec Std.Do.Spec.pure
        mpure_intro
        exact ⟨p, a, b, rfl, trivial, StEB_types_final,
          StEB_decl_final, p_fresh, a_fresh_ctx, b_fresh_ctx,
          hp_ne_a, hp_ne_b, ha_ne_b⟩

private theorem cprod_lambda_fv_subset
    (A B : SMT.Term) (p a b : SMT.𝒱)
    (alpha beta : SMTType) :
    SMT.fv (.lambda [p] [.pair alpha beta]
      (.exists [a, b] [alpha, beta]
        (.and (.app A (.var a))
          (.and (.app B (.var b))
            (.eq (.var p) (.pair (.var a) (.var b))))))) ⊆
      SMT.fv A ++ SMT.fv B := by
  intro v hv
  simp only [SMT.fv, List.mem_removeAll_iff, List.mem_append,
    List.mem_cons, List.mem_nil_iff,
    or_false] at hv ⊢
  aesop

private abbrev EncodeCprodTailRepTotalSemantics.{u}
    (alpha beta : BType) (A B out : SMT.Term)
    (sigmaOut : SMTType) (Lambda Gamma : SMT.TypeContext)
    (used usedOut : List SMT.𝒱) : Prop :=
  ∀ (Theta : SMT.RenamingContext.Context.{u})
    (hA : RenamingContext.CoversFV Theta A)
    (hB : RenamingContext.CoversFV Theta B),
    (∀ v ∉ used, Theta v = none) →
    SMT.RenamingContext.RespectsTypeContextOnFV Theta Lambda A →
    SMT.RenamingContext.RespectsTypeContextOnFV Theta Lambda B →
    (∀ v, Theta v ≠ none → v ∈ Lambda) →
    ∀ (X Y : ZFSet.{u})
      (hX : X ∈ ⟦BType.set alpha⟧ᶻ)
      (hY : Y ∈ ⟦BType.set beta⟧ᶻ)
      (denA denB : SMT.Dom.{u}),
      ⟦A.abstract Theta hA⟧ˢ = some denA →
      ⟦B.abstract Theta hB⟧ˢ = some denB →
      RDomCastSupported
        (⟨X, BType.set alpha, hX⟩ : _root_.B.Dom) denA →
      RDomCastSupported
        (⟨Y, BType.set beta, hY⟩ : _root_.B.Dom) denB →
      ∃ (Theta' : SMT.RenamingContext.Context.{u})
        (hcov : RenamingContext.CoversFV Theta' out)
        (denOut : SMT.Dom.{u}),
        RenamingContext.Extends Theta' Theta ∧
        (∀ v ∉ usedOut, Theta' v = none) ∧
        SMT.RenamingContext.RespectsTypeContextOnFV
          Theta' Gamma out ∧
        (∀ v, Theta' v ≠ none → v ∈ Gamma) ∧
        ⟦out.abstract Theta' hcov⟧ˢ = some denOut ∧
        denOut.snd.fst = sigmaOut ∧
        RDomCastSupported
          (⟨X.prod Y, BType.set (alpha ×ᴮ beta),
            cprod_mem_btype hX hY⟩ : _root_.B.Dom) denOut

private abbrev EncodeCprodTailRepGuardedSemantics.{u}
    (alpha beta : BType) (A B out : SMT.Term)
    (rho sigma sigmaOut : SMTType)
    (Lambda : SMT.TypeContext) (used : List SMT.𝒱) : Prop :=
  ∀ (Core : SMT.TypeContext), Core ⊆ Lambda → Core.keys ⊆ used →
    Core ⊢ˢ A : SMTType.fun rho SMTType.bool →
    Core ⊢ˢ B : SMTType.fun sigma SMTType.bool →
    ∀ (Theta : SMT.RenamingContext.Context.{u})
      (hcovA : RenamingContext.CoversFV Theta A)
      (hcovB : RenamingContext.CoversFV Theta B),
      SMT.RenamingContext.RespectsTypeContextOnFV Theta Core A →
      SMT.RenamingContext.RespectsTypeContextOnFV Theta Core B →
      ∀ (X Y : ZFSet.{u})
        (hX : X ∈ ⟦BType.set alpha⟧ᶻ)
        (hY : Y ∈ ⟦BType.set beta⟧ᶻ)
        (denA denB : SMT.Dom.{u}),
        ⟦A.abstract Theta hcovA⟧ˢ = some denA →
        ⟦B.abstract Theta hcovB⟧ˢ = some denB →
        RDomCastSupported
          (⟨X, BType.set alpha, hX⟩ : _root_.B.Dom) denA →
        RDomCastSupported
          (⟨Y, BType.set beta, hY⟩ : _root_.B.Dom) denB →
        ∀ (hcovOut : RenamingContext.CoversFV Theta out)
          (denOut : SMT.Dom.{u}),
          ⟦out.abstract Theta hcovOut⟧ˢ = some denOut →
          denOut.snd.fst = sigmaOut →
          RDomCastSupported
            (⟨X.prod Y, BType.set (alpha ×ᴮ beta),
              cprod_mem_btype hX hY⟩ : _root_.B.Dom) denOut

abbrev EncodeCprodTailRepSpec.{u}
    (alpha beta : BType) (rho sigma : SMTType)
    (_hrho : BType.SupportedSMT alpha rho)
    (_hsigma : BType.SupportedSMT beta sigma)
    (A B : SMT.Term) : Prop :=
  ∀ {Lambda : SMT.TypeContext} {n : ℕ} {used : List SMT.𝒱},
    Lambda ⊢ˢ A : SMTType.fun rho SMTType.bool →
    Lambda ⊢ˢ B : SMTType.fun sigma SMTType.bool →
    (∀ v ∈ SMT.bv A, v ∈ used) →
    (∀ v ∈ SMT.bv B, v ∈ used) →
    ⦃fun ⟨env, Lambda'⟩ =>
      ⌜Lambda' = Lambda ∧ env.freshvarsc = n ∧
        Lambda.keys ⊆ env.usedVars ∧ env.usedVars = used⌝⦄
    encodeCprodTail A B rho sigma
    ⦃⇓? ⟨t, sigma⟩ ⟨env', Gamma'⟩ =>
      ⌜used ⊆ env'.usedVars ∧
        Lambda ⊆ Gamma' ∧
        Gamma'.keys ⊆ env'.usedVars ∧
        Nonempty (sigma ~> (BType.set (alpha ×ᴮ beta)).toSMTType) ∧
        Gamma' ⊢ˢ t : sigma ∧
        (∀ v ∈ used, v ∉ Lambda → v ∉ Gamma') ∧
        ∀ (Theta : SMT.RenamingContext.Context.{u})
          (hA : RenamingContext.CoversFV Theta A)
          (hB : RenamingContext.CoversFV Theta B),
          (∀ v ∉ used, Theta v = none) →
          SMT.RenamingContext.RespectsTypeContextOnFV Theta Lambda A →
          SMT.RenamingContext.RespectsTypeContextOnFV Theta Lambda B →
          (∀ v, Theta v ≠ none → v ∈ Lambda) →
          ∀ (X Y : ZFSet.{u})
            (hX : X ∈ ⟦BType.set alpha⟧ᶻ)
            (hY : Y ∈ ⟦BType.set beta⟧ᶻ)
            (denA denB : SMT.Dom.{u}),
            ⟦A.abstract Theta hA⟧ˢ = some denA →
            ⟦B.abstract Theta hB⟧ˢ = some denB →
            RDomCastSupported
              (⟨X, BType.set alpha, hX⟩ : _root_.B.Dom) denA →
            RDomCastSupported
              (⟨Y, BType.set beta, hY⟩ : _root_.B.Dom) denB →
            ∃ (Theta' : SMT.RenamingContext.Context.{u})
              (hcov : RenamingContext.CoversFV Theta' t)
              (denOut : SMT.Dom.{u}),
              RenamingContext.Extends Theta' Theta ∧
              (∀ v ∉ env'.usedVars, Theta' v = none) ∧
              SMT.RenamingContext.RespectsTypeContextOnFV
                Theta' Gamma' t ∧
              (∀ v, Theta' v ≠ none → v ∈ Gamma') ∧
              ⟦t.abstract Theta' hcov⟧ˢ = some denOut ∧
              denOut.snd.fst = sigma ∧
              RDomCastSupported
                (⟨X.prod Y, BType.set (alpha ×ᴮ beta),
                  cprod_mem_btype hX hY⟩ : _root_.B.Dom) denOut⌝⦄

set_option maxHeartbeats 5000000 in
theorem encodeCprodTail_rep_spec.{u}
    (alpha beta : BType) (rho sigma : SMTType)
    (hrho : BType.SupportedSMT alpha rho)
    (hsigma : BType.SupportedSMT beta sigma)
    (A B : SMT.Term) :
    EncodeCprodTailRepSpec.{u} alpha beta rho sigma hrho hsigma A B := by
  unfold EncodeCprodTailRepSpec
  intro Lambda n used typ_A typ_B bv_A_used bv_B_used
  unfold encodeCprodTail
  mstart
  mintro pre ∀St₀
  mpure pre
  obtain ⟨rfl, rfl, St₀_keys, rfl⟩ := pre
  mspec SMT.freshVar_spec
  next p =>
    mrename_i post₁
    mintro ∀St₁
    mpure post₁
    obtain ⟨St₁_types_eq, p_fresh, _, St₁_used_eq,
      p_not_used⟩ := post₁
    mspec SMT.freshVar_spec
    next a =>
      mrename_i post₂
      mintro ∀St₂
      mpure post₂
      obtain ⟨St₂_types_eq, a_fresh, _, St₂_used_eq,
        a_not_used⟩ := post₂
      mspec SMT.freshVar_spec
      next b =>
        mrename_i post₃
        mintro ∀St₃
        mpure post₃
        obtain ⟨St₃_types_eq, b_fresh, _, St₃_used_eq,
          b_not_used⟩ := post₃
        mspec SMT.eraseFromContext_spec
        mrename_i postEp
        mintro ∀StEp
        mpure postEp
        obtain ⟨StEp_types_eq, _, StEp_used_eq⟩ := postEp
        mspec SMT.eraseFromContext_spec
        mrename_i postEa
        mintro ∀StEa
        mpure postEa
        obtain ⟨StEa_types_eq, _, StEa_used_eq⟩ := postEa
        mspec SMT.eraseFromContext_spec
        mrename_i postEb
        mintro ∀StEb
        mpure postEb
        obtain ⟨StEb_types_eq, _, StEb_used_eq⟩ := postEb

        have a_fresh₀ : a ∉ St₀.types.insert p
            (SMTType.pair rho sigma) := by
          simpa [St₁_types_eq] using a_fresh
        have b_fresh₀ : b ∉
            (St₀.types.insert p
              (SMTType.pair rho sigma)).insert a rho := by
          simpa [St₂_types_eq, St₁_types_eq] using b_fresh
        have StEb_types_final : StEb.types = St₀.types := by
          rw [StEb_types_eq, StEa_types_eq, StEp_types_eq,
            St₃_types_eq, St₂_types_eq, St₁_types_eq,
            erase_three_rep_cprod p_fresh a_fresh₀ b_fresh₀]
        have hp_ne_a : p ≠ a := by
          intro h
          subst a
          exact a_fresh₀ (by simp)
        have hp_ne_b : p ≠ b := by
          intro h
          subst b
          exact b_fresh₀ (by simp)
        have ha_ne_b : a ≠ b := by
          intro h
          subst b
          exact b_fresh₀ (by simp)
        have ha_not_ctx : a ∉ St₀.types := by
          intro h
          exact a_fresh₀ (by simp [h])
        have hb_not_ctx : b ∉ St₀.types := by
          intro h
          exact b_fresh₀ (by simp [h])
        have hp_not_bv_A : p ∉ SMT.bv A :=
          fun h => p_not_used (bv_A_used p h)
        have hp_not_bv_B : p ∉ SMT.bv B :=
          fun h => p_not_used (bv_B_used p h)
        have hp_not_fv_A : p ∉ SMT.fv A := by
          exact funNotMemFvOfNotMemContext typ_A p_fresh
        have hp_not_fv_B : p ∉ SMT.fv B := by
          exact funNotMemFvOfNotMemContext typ_B p_fresh
        have ha_not_fv_A : a ∉ SMT.fv A := by
          exact funNotMemFvOfNotMemContext typ_A ha_not_ctx
        have ha_not_fv_B : a ∉ SMT.fv B := by
          exact funNotMemFvOfNotMemContext typ_B ha_not_ctx
        have hb_not_fv_A : b ∉ SMT.fv A := by
          exact funNotMemFvOfNotMemContext typ_A hb_not_ctx
        have hb_not_fv_B : b ∉ SMT.fv B := by
          exact funNotMemFvOfNotMemContext typ_B hb_not_ctx
        have ha_not_bv_A : a ∉ SMT.bv A := fun h => by
          apply a_not_used
          rw [St₁_used_eq]
          exact List.mem_cons_of_mem _ (bv_A_used a h)
        have ha_not_bv_B : a ∉ SMT.bv B := fun h => by
          apply a_not_used
          rw [St₁_used_eq]
          exact List.mem_cons_of_mem _ (bv_B_used a h)
        have hb_not_bv_A : b ∉ SMT.bv A := fun h => by
          apply b_not_used
          · rw [St₂_used_eq, St₁_used_eq]
            exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (bv_A_used b h))
        have hb_not_bv_B : b ∉ SMT.bv B := fun h => by
          apply b_not_used
          ·
            rw [St₂_used_eq, St₁_used_eq]
            exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (bv_B_used b h))

        let body : SMT.Term :=
          (.app A (.var a)) ∧ˢ
            ((.app B (.var b)) ∧ˢ
              ((.var p) =ˢ (.pair (.var a) (.var b))))
        let tcprod : SMT.Term :=
          .lambda [p] [SMTType.pair rho sigma]
            (.exists [a, b] [rho, sigma] body)

        have typ_A_p : St₀.types.insert p
            (SMTType.pair rho sigma) ⊢ˢ A :
              SMTType.fun rho SMTType.bool :=
          SMT.Typing.weakening
            (SMT.TypeContext.entries_subset_insert_of_notMem p_fresh)
            typ_A
            (SMT.Typing.bv_notMem_insert_of_fresh typ_A hp_not_bv_A)
        have typ_B_p : St₀.types.insert p
            (SMTType.pair rho sigma) ⊢ˢ B :
              SMTType.fun sigma SMTType.bool :=
          SMT.Typing.weakening
            (SMT.TypeContext.entries_subset_insert_of_notMem p_fresh)
            typ_B
            (SMT.Typing.bv_notMem_insert_of_fresh typ_B hp_not_bv_B)
        have typ_A_pab :
            ((St₀.types.insert p
              (SMTType.pair rho sigma)).insert a rho).insert b sigma ⊢ˢ A :
              SMTType.fun rho SMTType.bool := by
          apply SMT.Typing.weakening
            (SMT.TypeContext.entries_subset_insert_of_notMem b_fresh₀)
          · apply SMT.Typing.weakening
              (SMT.TypeContext.entries_subset_insert_of_notMem a_fresh₀)
              typ_A_p
            exact SMT.Typing.bv_notMem_insert_of_fresh typ_A_p ha_not_bv_A
          · exact SMT.Typing.bv_notMem_insert_of_fresh
              (SMT.Typing.weakening
                (SMT.TypeContext.entries_subset_insert_of_notMem a_fresh₀)
                typ_A_p
                (SMT.Typing.bv_notMem_insert_of_fresh typ_A_p ha_not_bv_A))
              hb_not_bv_A
        have typ_B_pab :
            ((St₀.types.insert p
              (SMTType.pair rho sigma)).insert a rho).insert b sigma ⊢ˢ B :
              SMTType.fun sigma SMTType.bool := by
          apply SMT.Typing.weakening
            (SMT.TypeContext.entries_subset_insert_of_notMem b_fresh₀)
          · apply SMT.Typing.weakening
              (SMT.TypeContext.entries_subset_insert_of_notMem a_fresh₀)
              typ_B_p
            exact SMT.Typing.bv_notMem_insert_of_fresh typ_B_p ha_not_bv_B
          · exact SMT.Typing.bv_notMem_insert_of_fresh
              (SMT.Typing.weakening
                (SMT.TypeContext.entries_subset_insert_of_notMem a_fresh₀)
                typ_B_p
                (SMT.Typing.bv_notMem_insert_of_fresh typ_B_p ha_not_bv_B))
              hb_not_bv_B
        have typ_body :
            ((St₀.types.insert p
              (SMTType.pair rho sigma)).insert a rho).insert b sigma ⊢ˢ body :
              SMTType.bool := by
          dsimp [body]
          apply SMT.Typing.and
          · apply SMT.Typing.app
            · exact typ_A_pab
            · exact SMT.Typing.var _ a _ (by
                rw [AList.lookup_insert_ne ha_ne_b,
                  AList.lookup_insert])
          · apply SMT.Typing.and
            · apply SMT.Typing.app
              · exact typ_B_pab
              · exact SMT.Typing.var _ b _ (by
                  rw [AList.lookup_insert])
            · apply SMT.Typing.eq
              · exact SMT.Typing.var _ p _ (by
                  rw [AList.lookup_insert_ne hp_ne_b,
                    AList.lookup_insert_ne hp_ne_a,
                    AList.lookup_insert])
              · apply SMT.Typing.pair
                · exact SMT.Typing.var _ a _ (by
                    rw [AList.lookup_insert_ne ha_ne_b,
                      AList.lookup_insert])
                · exact SMT.Typing.var _ b _ (by
                    rw [AList.lookup_insert])
        have typ_exists : St₀.types.insert p
            (SMTType.pair rho sigma) ⊢ˢ
              .exists [a, b] [rho, sigma] body :
                SMTType.bool := by
          let lenEq : [a, b].length =
              [rho, sigma].length := by simp
          apply SMT.Typing.exists
              (vs := [a, b])
              (τs := [rho, sigma])
              (len_eq := lenEq)
          · intro v hv
            rw [List.mem_cons, List.mem_singleton] at hv
            rcases hv with rfl | rfl
            · exact a_fresh₀
            · intro h
              exact b_fresh₀ (by simp [h])
          · intro v hv hbv
            exact SMT.Typing.bv_notMem_context typ_body v hbv (by
              rw [List.mem_cons, List.mem_singleton] at hv
              rcases hv with rfl | rfl <;> simp)
          · simp
          · have hupdate : SMT.TypeContext.update
              (St₀.types.insert p
                  (SMTType.pair rho sigma))
                [a, b] [rho, sigma] lenEq =
              ((St₀.types.insert p
                (SMTType.pair rho sigma)).insert a rho).insert b sigma := by
              unfold SMT.TypeContext.update
              simp only [List.length_cons, List.length_nil, zero_add,
                Nat.reduceAdd, Fin.cast_eq_self, Fin.getElem_fin]
              rw [Fin.foldl_succ_last, Fin.foldl_succ_last]
              simp
            rw [hupdate]
            exact typ_body
        have typ_tcprod : St₀.types ⊢ˢ tcprod :
            SMTType.fun (SMTType.pair rho sigma) SMTType.bool := by
          let lenEq : [p].length =
              [SMTType.pair rho sigma].length := by
            simp
          apply SMT.Typing.lambda (vs := [p])
              (τs := [SMTType.pair rho sigma])
              (len_eq := lenEq)
          · simpa using p_fresh
          · intro v hv hbv
            rw [List.mem_singleton] at hv
            subst v
            exact SMT.Typing.bv_notMem_context typ_exists p hbv (by simp)
          · simp
          · have hupdate : SMT.TypeContext.update St₀.types [p]
                [SMTType.pair rho sigma] lenEq =
              St₀.types.insert p
                (SMTType.pair rho sigma) := by
              unfold SMT.TypeContext.update
              simp only [List.length_cons, List.length_nil, zero_add,
                Nat.reduceAdd, Fin.cast_eq_self, Fin.getElem_fin,
                Fin.val_eq_zero, List.getElem_cons_zero, Fin.foldl_succ,
                Fin.foldl_zero]
            rw [hupdate]
            exact typ_exists

        have fv_tcprod_sub : SMT.fv tcprod ⊆ SMT.fv A ++ SMT.fv B := by
          intro v hv
          dsimp [tcprod] at hv
          rw [SMT.fv, List.mem_removeAll_iff] at hv
          obtain ⟨hv, hv_ne_p⟩ := hv
          dsimp [body] at hv
          rw [SMT.fv, List.mem_removeAll_iff] at hv
          obtain ⟨hv, hv_ne_ab⟩ := hv
          rw [SMT.fv, List.mem_append] at hv
          rcases hv with hvAa | hv
          · rw [SMT.fv, List.mem_append] at hvAa
            rcases hvAa with hvA | hva
            · rw [List.mem_append]
              exact Or.inl hvA
            · exfalso
              apply hv_ne_ab
              simp only [SMT.fv, List.mem_singleton] at hva
              simp [hva]
          · rw [SMT.fv, List.mem_append] at hv
            rcases hv with hvBb | hvEq
            · rw [SMT.fv, List.mem_append] at hvBb
              rcases hvBb with hvB | hvb
              · rw [List.mem_append]
                exact Or.inr hvB
              · exfalso
                apply hv_ne_ab
                simp only [SMT.fv, List.mem_singleton] at hvb
                simp [hvb]
            · rw [SMT.fv, List.mem_append] at hvEq
              rcases hvEq with hvp | hvPair
              · exfalso
                apply hv_ne_p
                simpa [SMT.fv] using hvp
              · rw [SMT.fv, List.mem_append] at hvPair
                rcases hvPair with hva | hvb
                · exfalso
                  apply hv_ne_ab
                  simp only [SMT.fv, List.mem_singleton] at hva
                  simp [hva]
                · exfalso
                  apply hv_ne_ab
                  simp only [SMT.fv, List.mem_singleton] at hvb
                  simp [hvb]

        mspec Std.Do.Spec.pure
        mpure_intro
        and_intros
        · intro v hv
          rw [StEb_used_eq, StEa_used_eq, StEp_used_eq,
            St₃_used_eq, St₂_used_eq, St₁_used_eq]
          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ hv))
        · simp [StEb_types_final]
        · intro v hv
          rw [StEb_types_final] at hv
          rw [StEb_used_eq, StEa_used_eq, StEp_used_eq,
            St₃_used_eq, St₂_used_eq, St₁_used_eq]
          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (St₀_keys hv)))
        · exact (BType.SupportedSMT.setPred
            (BType.SupportedSMT.prod hrho hsigma)).nonemptyCanonicalCastPath
        · simpa [StEb_types_final, tcprod, body] using typ_tcprod
        · intro v hv hv_not
          simpa [StEb_types_final] using hv_not
        · intro Theta hcov_A hcov_B Theta_none
            respects_A respects_B Theta_dom X Y hX hY
            denA denB hden_A hden_B A_rel B_rel
          have denA_type :=
            SMT.RenamingContext.denote_type_of_typing_fv
              typ_A respects_A hcov_A hden_A
          have denB_type :=
            SMT.RenamingContext.denote_type_of_typing_fv
              typ_B respects_B hcov_B hden_B
          rcases denA with ⟨Aval, sigmaA, hAval⟩
          rcases denB with ⟨Bval, sigmaB, hBval⟩
          dsimp at denA_type denB_type
          subst sigmaA
          subst sigmaB
          have hcov_tcprod : RenamingContext.CoversFV Theta tcprod := by
            intro v hv
            have hv' := fv_tcprod_sub hv
            rw [List.mem_append] at hv'
            exact hv'.elim (hcov_A v) (hcov_B v)
          have target_respects :
              SMT.RenamingContext.RespectsTypeContextOnFV
                Theta St₀.types tcprod := by
            intro v sigma hv hlookup
            have hv' := fv_tcprod_sub hv
            rw [List.mem_append] at hv'
            exact hv'.elim
              (fun h => respects_A h hlookup)
              (fun h => respects_B h hlookup)
          obtain ⟨denOut, hdenOut, hdenOut_type⟩ :=
            SMT.RenamingContext.denote_exists_of_typing_fv
              typ_tcprod target_respects hcov_tcprod
          have hprod_sub : X.prod Y ⊆ ⟦alpha ×ᴮ beta⟧ᶻ := by
            simpa [BType.toZFSet] using
              ZFSet.mem_powerset.mp (cprod_mem_btype hX hY)
          have fv_body_to_tcprod : ∀ {v : SMT.𝒱},
              v ∈ SMT.fv body → v ≠ p → v ≠ a → v ≠ b →
                v ∈ SMT.fv tcprod := by
            intro v hv hvp hva hvb
            dsimp [tcprod]
            rw [SMT.fv, List.mem_removeAll_iff]
            refine ⟨?_, by simpa using hvp⟩
            rw [SMT.fv, List.mem_removeAll_iff]
            exact ⟨hv, by simp [hva, hvb]⟩
          have hcov_exists : ∀ Wp : SMT.Dom.{u},
              RenamingContext.CoversFV
                (Function.update Theta p (some Wp))
                (SMT.Term.exists [a, b] [rho, sigma] body) := by
            intro Wp v hv
            by_cases hvp : v = p
            · subst v
              simp [Function.update_self]
            · rw [Function.update_of_ne hvp]
              apply hcov_tcprod
              dsimp [tcprod]
              rw [SMT.fv, List.mem_removeAll_iff]
              exact ⟨hv, by simpa using hvp⟩
          have respects_exists : ∀ (Wp : SMT.Dom.{u}),
              Wp.snd.fst = SMTType.pair rho sigma →
              SMT.RenamingContext.RespectsTypeContextOnFV
                (Function.update Theta p (some Wp))
                (St₀.types.insert p (SMTType.pair rho sigma))
                (SMT.Term.exists [a, b] [rho, sigma] body) := by
            intro Wp hWp_type v tau hv hlookup
            by_cases hvp : v = p
            · subst v
              rw [AList.lookup_insert] at hlookup
              cases hlookup
              exact ⟨Wp, Function.update_self _ _ _, hWp_type⟩
            · rw [AList.lookup_insert_ne hvp] at hlookup
              have hv_tcprod : v ∈ SMT.fv tcprod := by
                dsimp [tcprod]
                rw [SMT.fv, List.mem_removeAll_iff]
                exact ⟨hv, by simpa using hvp⟩
              obtain ⟨d, hd, htype⟩ :=
                target_respects hv_tcprod hlookup
              refine ⟨d, ?_, htype⟩
              simpa [Function.update_of_ne hvp] using hd
          have hcov_body : ∀ Wp Wa Wb : SMT.Dom.{u},
              RenamingContext.CoversFV
                (Function.update
                  (Function.update (Function.update Theta p (some Wp))
                    a (some Wa)) b (some Wb)) body := by
            intro Wp Wa Wb v hv
            by_cases hvb : v = b
            · subst v
              simp [Function.update_self]
            · by_cases hva : v = a
              · subst v
                simp [Function.update_of_ne ha_ne_b,
                  Function.update_self]
              · by_cases hvp : v = p
                · subst v
                  simp [Function.update_of_ne hp_ne_b,
                    Function.update_of_ne hp_ne_a,
                    Function.update_self]
                · rw [Function.update_of_ne hvb,
                    Function.update_of_ne hva,
                    Function.update_of_ne hvp]
                  exact hcov_tcprod v
                    (fv_body_to_tcprod hv hvp hva hvb)
          have respects_body : ∀ (Wp Wa Wb : SMT.Dom.{u}),
              Wp.snd.fst = SMTType.pair rho sigma →
              Wa.snd.fst = rho → Wb.snd.fst = sigma →
              SMT.RenamingContext.RespectsTypeContextOnFV
                (Function.update
                  (Function.update (Function.update Theta p (some Wp))
                    a (some Wa)) b (some Wb))
                (((St₀.types.insert p (SMTType.pair rho sigma)).insert a rho).insert b sigma)
                body := by
            intro Wp Wa Wb hWp_type hWa_type hWb_type v tau hv hlookup
            by_cases hvb : v = b
            · subst v
              rw [AList.lookup_insert] at hlookup
              cases hlookup
              exact ⟨Wb, Function.update_self _ _ _, hWb_type⟩
            · rw [AList.lookup_insert_ne hvb] at hlookup
              by_cases hva : v = a
              · subst v
                rw [AList.lookup_insert] at hlookup
                cases hlookup
                refine ⟨Wa, ?_, hWa_type⟩
                rw [Function.update_of_ne ha_ne_b,
                  Function.update_self]
              · rw [AList.lookup_insert_ne hva] at hlookup
                by_cases hvp : v = p
                · subst v
                  rw [AList.lookup_insert] at hlookup
                  cases hlookup
                  refine ⟨Wp, ?_, hWp_type⟩
                  rw [Function.update_of_ne hp_ne_b,
                    Function.update_of_ne hp_ne_a,
                    Function.update_self]
                · rw [AList.lookup_insert_ne hvp] at hlookup
                  obtain ⟨d, hd, htype⟩ := target_respects
                    (fv_body_to_tcprod hv hvp hva hvb) hlookup
                  refine ⟨d, ?_, htype⟩
                  simpa [Function.update_of_ne hvb,
                    Function.update_of_ne hva,
                    Function.update_of_ne hvp] using hd
          have body_den : ∀ (Wp Wa Wb : SMT.Dom.{u}),
              Wp.snd.fst = SMTType.pair rho sigma →
              Wa.snd.fst = rho → Wb.snd.fst = sigma →
              ∃ D : SMT.Dom.{u},
                ⟦body.abstract
                  (Function.update
                    (Function.update (Function.update Theta p (some Wp))
                      a (some Wa)) b (some Wb))
                  (hcov_body Wp Wa Wb)⟧ˢ = some D ∧
                D.snd.fst = SMTType.bool := by
            intro Wp Wa Wb hWp_type hWa_type hWb_type
            exact SMT.RenamingContext.denote_exists_of_typing_fv
              typ_body
              (respects_body Wp Wa Wb hWp_type hWa_type hWb_type)
              (hcov_body Wp Wa Wb)
          have body_total : ∀ (Wp Wa Wb : SMT.Dom.{u}),
              Wp.snd.fst = SMTType.pair rho sigma →
              Wa.snd.fst = rho → Wb.snd.fst = sigma →
              (⟦body.abstract
                (Function.update
                  (Function.update (Function.update Theta p (some Wp))
                    a (some Wa)) b (some Wb))
                (hcov_body Wp Wa Wb)⟧ˢ).isSome = true := by
            intro Wp Wa Wb hWp_type hWa_type hWb_type
            obtain ⟨D, hdenD, _⟩ :=
              body_den Wp Wa Wb hWp_type hWa_type hWb_type
            rw [hdenD]
            rfl
          have body_type : ∀ (Wp Wa Wb : SMT.Dom.{u}),
              Wp.snd.fst = SMTType.pair rho sigma →
              Wa.snd.fst = rho → Wb.snd.fst = sigma →
              ∀ {D : SMT.Dom.{u}},
                ⟦body.abstract
                  (Function.update
                    (Function.update (Function.update Theta p (some Wp))
                      a (some Wa)) b (some Wb))
                  (hcov_body Wp Wa Wb)⟧ˢ = some D →
                D.snd.fst = SMTType.bool := by
            intro Wp Wa Wb hWp_type hWa_type hWb_type D hdenD
            exact SMT.RenamingContext.denote_type_of_typing_fv
              typ_body
              (respects_body Wp Wa Wb hWp_type hWa_type hWb_type)
              (hcov_body Wp Wa Wb) hdenD
          have hgo_body : ∀ (Wp : SMT.Dom.{u}) v,
              v ∈ SMT.fv body → v ∉ [a, b] →
                ((Function.update Theta p (some Wp)) v).isSome = true := by
            intro Wp v hv hv_not_ab
            have hva : v ≠ a := by
              intro h
              subst v
              exact hv_not_ab (by simp)
            have hvb : v ≠ b := by
              intro h
              subst v
              exact hv_not_ab (by simp)
            by_cases hvp : v = p
            · subst v
              simp [Function.update_self]
            · rw [Function.update_of_ne hvp]
              exact hcov_tcprod v
                (fv_body_to_tcprod hv hvp hva hvb)
          have Out_rel : RDomCastSupported
              (⟨X.prod Y, BType.set (alpha ×ᴮ beta),
                cprod_mem_btype hX hY⟩ : _root_.B.Dom) denOut := by
            refine represented_setPred_lambda_of_pointwise
              (alpha := alpha ×ᴮ beta)
              (sigma := SMTType.pair rho sigma)
              (S := X.prod Y) (Theta := Theta) (z := p)
              (body := SMT.Term.exists [a, b] [rho, sigma] body)
              (lamVal := denOut)
              (BType.SupportedSMT.prod hrho hsigma) hprod_sub
              ?_ ?_ ?_ ?_ ?_ ?_
            · simpa [tcprod, body] using hcov_tcprod
            · simpa [tcprod, body] using hdenOut
            · simpa [tcprod, body] using hdenOut_type
            · intro y hy
              let Wp : SMT.Dom.{u} :=
                ⟨y, SMTType.pair rho sigma, hy⟩
              obtain ⟨bodyVal, hden_bodyVal, _⟩ :=
                SMT.RenamingContext.denote_exists_of_typing_fv
                  typ_exists (respects_exists Wp rfl) (hcov_exists Wp)
              exact ⟨hcov_exists Wp, bodyVal, hden_bodyVal⟩
            · intro y hy hcov_exists' bodyVal hden_exists hbody_true
              let Wp : SMT.Dom.{u} :=
                ⟨y, SMTType.pair rho sigma, hy⟩
              obtain ⟨Wa, Wb, hWa_type, hWb_type, Dbody,
                  hden_body, hDbody_true⟩ :=
                funBinaryExistsTrueWitness
                  hcov_exists' (hgo_body Wp)
                  (fun Wa Wb => hcov_body Wp Wa Wb)
                  (fun Wa Wb hWa hWb =>
                    body_total Wp Wa Wb rfl hWa hWb)
                  (fun Wa Wb hWa hWb =>
                    body_type Wp Wa Wb rfl hWa hWb)
                  hden_exists hbody_true
              have hcov_Aapp : RenamingContext.CoversFV
                  (Function.update
                    (Function.update (Function.update Theta p (some Wp))
                      a (some Wa)) b (some Wb))
                  ((@ˢA) (SMT.Term.var a)) := by
                intro v hv
                apply hcov_body Wp Wa Wb v
                simp only [body, SMT.fv, List.mem_append]
                simp only [SMT.fv, List.mem_append] at hv
                exact Or.inl hv
              have hcov_right : RenamingContext.CoversFV
                  (Function.update
                    (Function.update (Function.update Theta p (some Wp))
                      a (some Wa)) b (some Wb))
                  ((@ˢB) (SMT.Term.var b) ∧ˢ
                    (SMT.Term.var p =ˢ
                      (SMT.Term.var a).pair (SMT.Term.var b))) := by
                intro v hv
                apply hcov_body Wp Wa Wb v
                simp only [body, SMT.fv, List.mem_append]
                simp only [SMT.fv, List.mem_append] at hv
                exact Or.inr hv
              obtain ⟨_, typ_Aapp, typ_right⟩ :=
                SMT.Typing.andE typ_body
              have respects_Aapp :
                  SMT.RenamingContext.RespectsTypeContextOnFV
                    (Function.update
                      (Function.update (Function.update Theta p (some Wp))
                        a (some Wa)) b (some Wb))
                    (((St₀.types.insert p (SMTType.pair rho sigma)).insert
                      a rho).insert b sigma)
                    ((@ˢA) (SMT.Term.var a)) := by
                apply SMT.RenamingContext.RespectsTypeContextOnFV.mono_fv
                  (respects_body Wp Wa Wb rfl hWa_type hWb_type)
                intro v hv
                simp only [body, SMT.fv, List.mem_append]
                simp only [SMT.fv, List.mem_append] at hv
                exact Or.inl hv
              have respects_right :
                  SMT.RenamingContext.RespectsTypeContextOnFV
                    (Function.update
                      (Function.update (Function.update Theta p (some Wp))
                        a (some Wa)) b (some Wb))
                    (((St₀.types.insert p (SMTType.pair rho sigma)).insert
                      a rho).insert b sigma)
                    ((@ˢB) (SMT.Term.var b) ∧ˢ
                      (SMT.Term.var p =ˢ
                        (SMT.Term.var a).pair (SMT.Term.var b))) := by
                apply SMT.RenamingContext.RespectsTypeContextOnFV.mono_fv
                  (respects_body Wp Wa Wb rfl hWa_type hWb_type)
                intro v hv
                simp only [body, SMT.fv, List.mem_append]
                simp only [SMT.fv, List.mem_append] at hv
                exact Or.inr hv
              have hden_outer :
                  ⟦(((@ˢA) (SMT.Term.var a)).abstract
                      (Function.update
                        (Function.update (Function.update Theta p (some Wp))
                          a (some Wa)) b (some Wb)) hcov_Aapp) ∧ˢ'
                    (((@ˢB) (SMT.Term.var b) ∧ˢ
                      (SMT.Term.var p =ˢ
                        (SMT.Term.var a).pair (SMT.Term.var b))).abstract
                      (Function.update
                        (Function.update (Function.update Theta p (some Wp))
                          a (some Wa)) b (some Wb)) hcov_right)⟧ˢ =
                    some Dbody := by
                simpa [body, SMT.Term.abstract, proof_irrel_heq] using
                  hden_body
              obtain ⟨DAapp, Dright, hden_Aapp, hDAapp_true,
                  hden_right, hDright_true⟩ :=
                denoteAndTrueComponents
                  (typ_p_bool := by
                    intro D hdenD
                    exact SMT.RenamingContext.denote_type_of_typing_fv
                      typ_Aapp respects_Aapp hcov_Aapp hdenD)
                  (typ_q_bool := by
                    intro D hdenD
                    exact SMT.RenamingContext.denote_type_of_typing_fv
                      typ_right respects_right hcov_right hdenD)
                  hden_outer hDbody_true
              have hcov_Bapp : RenamingContext.CoversFV
                  (Function.update
                    (Function.update (Function.update Theta p (some Wp))
                      a (some Wa)) b (some Wb))
                  ((@ˢB) (SMT.Term.var b)) := by
                intro v hv
                apply hcov_right v
                simp only [SMT.fv, List.mem_append]
                simp only [SMT.fv, List.mem_append] at hv
                exact Or.inl hv
              have hcov_eq : RenamingContext.CoversFV
                  (Function.update
                    (Function.update (Function.update Theta p (some Wp))
                      a (some Wa)) b (some Wb))
                  (SMT.Term.var p =ˢ
                    (SMT.Term.var a).pair (SMT.Term.var b)) := by
                intro v hv
                apply hcov_right v
                simp only [SMT.fv, List.mem_append]
                simp only [SMT.fv, List.mem_append] at hv
                exact Or.inr hv
              obtain ⟨_, typ_Bapp, typ_eq⟩ :=
                SMT.Typing.andE typ_right
              have respects_Bapp :
                  SMT.RenamingContext.RespectsTypeContextOnFV
                    (Function.update
                      (Function.update (Function.update Theta p (some Wp))
                        a (some Wa)) b (some Wb))
                    (((St₀.types.insert p (SMTType.pair rho sigma)).insert
                      a rho).insert b sigma)
                    ((@ˢB) (SMT.Term.var b)) := by
                apply SMT.RenamingContext.RespectsTypeContextOnFV.mono_fv
                  respects_right
                intro v hv
                simp only [SMT.fv, List.mem_append]
                simp only [SMT.fv, List.mem_append] at hv
                exact Or.inl hv
              have respects_eq :
                  SMT.RenamingContext.RespectsTypeContextOnFV
                    (Function.update
                      (Function.update (Function.update Theta p (some Wp))
                        a (some Wa)) b (some Wb))
                    (((St₀.types.insert p (SMTType.pair rho sigma)).insert
                      a rho).insert b sigma)
                    (SMT.Term.var p =ˢ
                      (SMT.Term.var a).pair (SMT.Term.var b)) := by
                apply SMT.RenamingContext.RespectsTypeContextOnFV.mono_fv
                  respects_right
                intro v hv
                simp only [SMT.fv, List.mem_append]
                simp only [SMT.fv, List.mem_append] at hv
                exact Or.inr hv
              have hden_right_split :
                  ⟦(((@ˢB) (SMT.Term.var b)).abstract
                      (Function.update
                        (Function.update (Function.update Theta p (some Wp))
                          a (some Wa)) b (some Wb)) hcov_Bapp) ∧ˢ'
                    ((SMT.Term.var p =ˢ
                      (SMT.Term.var a).pair (SMT.Term.var b)).abstract
                      (Function.update
                        (Function.update (Function.update Theta p (some Wp))
                          a (some Wa)) b (some Wb)) hcov_eq)⟧ˢ =
                    some Dright := by
                simpa [SMT.Term.abstract, proof_irrel_heq] using hden_right
              obtain ⟨DBapp, Deq, hden_Bapp, hDBapp_true,
                  hden_eq, hDeq_true⟩ :=
                denoteAndTrueComponents
                  (typ_p_bool := by
                    intro D hdenD
                    exact SMT.RenamingContext.denote_type_of_typing_fv
                      typ_Bapp respects_Bapp hcov_Bapp hdenD)
                  (typ_q_bool := by
                    intro D hdenD
                    exact SMT.RenamingContext.denote_type_of_typing_fv
                      typ_eq respects_eq hcov_eq hdenD)
                  hden_right_split hDright_true
              have hcov_A_p : RenamingContext.CoversFV
                  (Function.update Theta p (some Wp)) A := by
                exact SMT.RenamingContext.coversFV_update_of_notMem
                  (x := p) (d := Wp) hp_not_fv_A hcov_A
              have hcov_A_pa : RenamingContext.CoversFV
                  (Function.update (Function.update Theta p (some Wp))
                    a (some Wa)) A := by
                exact SMT.RenamingContext.coversFV_update_of_notMem
                  (x := a) (d := Wa) ha_not_fv_A hcov_A_p
              have hcov_A_pab : RenamingContext.CoversFV
                  (Function.update
                    (Function.update (Function.update Theta p (some Wp))
                      a (some Wa)) b (some Wb)) A := by
                exact SMT.RenamingContext.coversFV_update_of_notMem
                  (x := b) (d := Wb) hb_not_fv_A hcov_A_pa
              have hden_A_p_raw :
                  ⟦A.abstract (Function.update Theta p (some Wp))
                      hcov_A_p⟧ˢ =
                    ⟦A.abstract Theta hcov_A⟧ˢ := by
                simpa [SMT.RenamingContext.denote] using
                  (SMT.RenamingContext.denote_update_of_notMem
                    («Δ» := Theta) (t := A) (x := p) (d := Wp)
                    (h := hcov_A) hp_not_fv_A).symm
              have hden_A_pa_raw :
                  ⟦A.abstract
                      (Function.update (Function.update Theta p (some Wp))
                        a (some Wa)) hcov_A_pa⟧ˢ =
                    ⟦A.abstract (Function.update Theta p (some Wp))
                      hcov_A_p⟧ˢ := by
                simpa [SMT.RenamingContext.denote] using
                  (SMT.RenamingContext.denote_update_of_notMem
                    («Δ» := Function.update Theta p (some Wp))
                    (t := A) (x := a) (d := Wa)
                    (h := hcov_A_p) ha_not_fv_A).symm
              have hden_A_pab_raw :
                  ⟦A.abstract
                      (Function.update
                        (Function.update (Function.update Theta p (some Wp))
                          a (some Wa)) b (some Wb)) hcov_A_pab⟧ˢ =
                    ⟦A.abstract
                      (Function.update (Function.update Theta p (some Wp))
                        a (some Wa)) hcov_A_pa⟧ˢ := by
                simpa [SMT.RenamingContext.denote] using
                  (SMT.RenamingContext.denote_update_of_notMem
                    («Δ» := Function.update
                      (Function.update Theta p (some Wp)) a (some Wa))
                    (t := A) (x := b) (d := Wb)
                    (h := hcov_A_pa) hb_not_fv_A).symm
              have hden_A_pab :
                  ⟦A.abstract
                      (Function.update
                        (Function.update (Function.update Theta p (some Wp))
                          a (some Wa)) b (some Wb)) hcov_A_pab⟧ˢ =
                    some ⟨Aval, ⟨rho.fun SMTType.bool, hAval⟩⟩ := by
                exact hden_A_pab_raw.trans
                  (hden_A_pa_raw.trans (hden_A_p_raw.trans hden_A))
              have hAval_func :
                  ZFSet.IsFunc ⟦rho⟧ᶻ ⟦SMTType.bool⟧ᶻ Aval := by
                simpa [SMTType.toZFSet] using hAval
              have hWa_mem : Wa.fst ∈ ⟦rho⟧ᶻ := by
                simpa [hWa_type] using Wa.snd.snd
              have hcov_A_pab_a : ∀ Xarg : SMT.Dom,
                  RenamingContext.CoversFV
                    (Function.update
                      (Function.update
                        (Function.update (Function.update Theta p (some Wp))
                          a (some Wa)) b (some Wb)) a (some Xarg)) A :=
                fun Xarg =>
                  SMT.RenamingContext.coversFV_update_of_notMem
                    (x := a) (d := Xarg) ha_not_fv_A hcov_A_pab
              have hden_A_pab_a_raw (Xarg : SMT.Dom) :
                  ⟦A.abstract
                      (Function.update
                        (Function.update
                          (Function.update
                            (Function.update Theta p (some Wp)) a (some Wa))
                          b (some Wb)) a (some Xarg))
                      (hcov_A_pab_a Xarg)⟧ˢ =
                    ⟦A.abstract
                      (Function.update
                        (Function.update (Function.update Theta p (some Wp))
                          a (some Wa)) b (some Wb)) hcov_A_pab⟧ˢ := by
                simpa [SMT.RenamingContext.denote] using
                  (SMT.RenamingContext.denote_update_of_notMem
                    («Δ» := Function.update
                      (Function.update
                        (Function.update Theta p (some Wp)) a (some Wa))
                      b (some Wb))
                    (t := A) (x := a) (d := Xarg)
                    (h := hcov_A_pab) ha_not_fv_A).symm
              have hden_A_pab_a : ∀ Xarg : SMT.Dom,
                  ⟦A.abstract
                      (Function.update
                        (Function.update
                          (Function.update
                            (Function.update Theta p (some Wp)) a (some Wa))
                          b (some Wb)) a (some Xarg))
                      (hcov_A_pab_a Xarg)⟧ˢ =
                    some ⟨Aval, ⟨rho.fun SMTType.bool, hAval⟩⟩ :=
                fun Xarg => (hden_A_pab_a_raw Xarg).trans hden_A_pab
              obtain ⟨hcov_Aapp_eval, DAeval, hDAeval_type,
                  hDAeval_value, hden_Aapp_eval⟩ :=
                funDenoteAppAt
                  (Δctx := Function.update
                    (Function.update
                      (Function.update Theta p (some Wp)) a (some Wa))
                    b (some Wb))
                  (t := A) (x := a)
                  (α := rho) (β := SMTType.bool)
                  (Y := (⟨Aval, ⟨rho.fun SMTType.bool, hAval⟩⟩ : SMT.Dom))
                  hcov_A_pab_a hden_A_pab_a rfl hAval_func
                  Wa hWa_type hWa_mem
              have hctx_Aeval :
                  Function.update
                      (Function.update
                        (Function.update
                          (Function.update Theta p (some Wp)) a (some Wa))
                        b (some Wb)) a (some Wa) =
                    Function.update
                      (Function.update (Function.update Theta p (some Wp))
                        a (some Wa)) b (some Wb) := by
                funext v
                by_cases hva : v = a
                · subst v
                  simp [Function.update, ha_ne_b]
                · simp [Function.update, hva]
              have hden_Aapp_eval_full :
                  ⟦((@ˢA) (SMT.Term.var a)).abstract
                      (Function.update
                        (Function.update (Function.update Theta p (some Wp))
                          a (some Wa)) b (some Wb)) hcov_Aapp⟧ˢ =
                    some DAeval := by
                simpa [hctx_Aeval, proof_irrel_heq] using hden_Aapp_eval
              have hDAeval_eq_DAapp : DAeval = DAapp := by
                exact Option.some.inj
                  (hden_Aapp_eval_full.symm.trans hden_Aapp)
              have hDAeval_true : DAeval.fst = ZFSet.zftrue := by
                rw [hDAeval_eq_DAapp]
                exact hDAapp_true
              have hAval_app_true :
                  (ZFSet.fapply Aval (ZFSet.is_func_is_pfunc hAval_func)
                    ⟨Wa.fst, by
                      rw [ZFSet.is_func_dom_eq hAval_func]
                      exact hWa_mem⟩).val = ZFSet.zftrue := by
                exact hDAeval_value.symm.trans hDAeval_true
              obtain ⟨xa, hxa_X, Wa_rel⟩ :=
                A_rel.setPred_target_of_true hWa_mem hAval_app_true
              have hcov_B_p : RenamingContext.CoversFV
                  (Function.update Theta p (some Wp)) B := by
                exact SMT.RenamingContext.coversFV_update_of_notMem
                  (x := p) (d := Wp) hp_not_fv_B hcov_B
              have hcov_B_pa : RenamingContext.CoversFV
                  (Function.update (Function.update Theta p (some Wp))
                    a (some Wa)) B := by
                exact SMT.RenamingContext.coversFV_update_of_notMem
                  (x := a) (d := Wa) ha_not_fv_B hcov_B_p
              have hcov_B_pab : RenamingContext.CoversFV
                  (Function.update
                    (Function.update (Function.update Theta p (some Wp))
                      a (some Wa)) b (some Wb)) B := by
                exact SMT.RenamingContext.coversFV_update_of_notMem
                  (x := b) (d := Wb) hb_not_fv_B hcov_B_pa
              have hden_B_p_raw :
                  ⟦B.abstract (Function.update Theta p (some Wp))
                      hcov_B_p⟧ˢ =
                    ⟦B.abstract Theta hcov_B⟧ˢ := by
                simpa [SMT.RenamingContext.denote] using
                  (SMT.RenamingContext.denote_update_of_notMem
                    («Δ» := Theta) (t := B) (x := p) (d := Wp)
                    (h := hcov_B) hp_not_fv_B).symm
              have hden_B_pa_raw :
                  ⟦B.abstract
                      (Function.update (Function.update Theta p (some Wp))
                        a (some Wa)) hcov_B_pa⟧ˢ =
                    ⟦B.abstract (Function.update Theta p (some Wp))
                      hcov_B_p⟧ˢ := by
                simpa [SMT.RenamingContext.denote] using
                  (SMT.RenamingContext.denote_update_of_notMem
                    («Δ» := Function.update Theta p (some Wp))
                    (t := B) (x := a) (d := Wa)
                    (h := hcov_B_p) ha_not_fv_B).symm
              have hden_B_pab_raw :
                  ⟦B.abstract
                      (Function.update
                        (Function.update (Function.update Theta p (some Wp))
                          a (some Wa)) b (some Wb)) hcov_B_pab⟧ˢ =
                    ⟦B.abstract
                      (Function.update (Function.update Theta p (some Wp))
                        a (some Wa)) hcov_B_pa⟧ˢ := by
                simpa [SMT.RenamingContext.denote] using
                  (SMT.RenamingContext.denote_update_of_notMem
                    («Δ» := Function.update
                      (Function.update Theta p (some Wp)) a (some Wa))
                    (t := B) (x := b) (d := Wb)
                    (h := hcov_B_pa) hb_not_fv_B).symm
              have hden_B_pab :
                  ⟦B.abstract
                      (Function.update
                        (Function.update (Function.update Theta p (some Wp))
                          a (some Wa)) b (some Wb)) hcov_B_pab⟧ˢ =
                    some ⟨Bval, ⟨sigma.fun SMTType.bool, hBval⟩⟩ := by
                exact hden_B_pab_raw.trans
                  (hden_B_pa_raw.trans (hden_B_p_raw.trans hden_B))
              have hBval_func :
                  ZFSet.IsFunc ⟦sigma⟧ᶻ ⟦SMTType.bool⟧ᶻ Bval := by
                simpa [SMTType.toZFSet] using hBval
              have hWb_mem : Wb.fst ∈ ⟦sigma⟧ᶻ := by
                simpa [hWb_type] using Wb.snd.snd
              have hcov_B_pab_b : ∀ Xarg : SMT.Dom,
                  RenamingContext.CoversFV
                    (Function.update
                      (Function.update
                        (Function.update
                          (Function.update Theta p (some Wp)) a (some Wa))
                        b (some Wb)) b (some Xarg)) B :=
                fun Xarg =>
                  SMT.RenamingContext.coversFV_update_of_notMem
                    (x := b) (d := Xarg) hb_not_fv_B hcov_B_pab
              have hden_B_pab_b_raw (Xarg : SMT.Dom) :
                  ⟦B.abstract
                      (Function.update
                        (Function.update
                          (Function.update
                            (Function.update Theta p (some Wp)) a (some Wa))
                          b (some Wb)) b (some Xarg))
                      (hcov_B_pab_b Xarg)⟧ˢ =
                    ⟦B.abstract
                      (Function.update
                        (Function.update (Function.update Theta p (some Wp))
                          a (some Wa)) b (some Wb)) hcov_B_pab⟧ˢ := by
                simpa [SMT.RenamingContext.denote] using
                  (SMT.RenamingContext.denote_update_of_notMem
                    («Δ» := Function.update
                      (Function.update
                        (Function.update Theta p (some Wp)) a (some Wa))
                      b (some Wb))
                    (t := B) (x := b) (d := Xarg)
                    (h := hcov_B_pab) hb_not_fv_B).symm
              have hden_B_pab_b : ∀ Xarg : SMT.Dom,
                  ⟦B.abstract
                      (Function.update
                        (Function.update
                          (Function.update
                            (Function.update Theta p (some Wp)) a (some Wa))
                          b (some Wb)) b (some Xarg))
                      (hcov_B_pab_b Xarg)⟧ˢ =
                    some ⟨Bval, ⟨sigma.fun SMTType.bool, hBval⟩⟩ :=
                fun Xarg => (hden_B_pab_b_raw Xarg).trans hden_B_pab
              obtain ⟨hcov_Bapp_eval, DBeval, hDBeval_type,
                  hDBeval_value, hden_Bapp_eval⟩ :=
                funDenoteAppAt
                  (Δctx := Function.update
                    (Function.update
                      (Function.update Theta p (some Wp)) a (some Wa))
                    b (some Wb))
                  (t := B) (x := b)
                  (α := sigma) (β := SMTType.bool)
                  (Y := (⟨Bval, ⟨sigma.fun SMTType.bool, hBval⟩⟩ : SMT.Dom))
                  hcov_B_pab_b hden_B_pab_b rfl hBval_func
                  Wb hWb_type hWb_mem
              have hctx_Beval :
                  Function.update
                      (Function.update
                        (Function.update
                          (Function.update Theta p (some Wp)) a (some Wa))
                        b (some Wb)) b (some Wb) =
                    Function.update
                      (Function.update (Function.update Theta p (some Wp))
                        a (some Wa)) b (some Wb) := by
                funext v
                by_cases hvb : v = b
                · subst v
                  simp [Function.update]
                · simp [Function.update, hvb]
              have hden_Bapp_eval_full :
                  ⟦((@ˢB) (SMT.Term.var b)).abstract
                      (Function.update
                        (Function.update (Function.update Theta p (some Wp))
                          a (some Wa)) b (some Wb)) hcov_Bapp⟧ˢ =
                    some DBeval := by
                simpa [hctx_Beval, proof_irrel_heq] using hden_Bapp_eval
              have hDBeval_eq_DBapp : DBeval = DBapp := by
                exact Option.some.inj
                  (hden_Bapp_eval_full.symm.trans hden_Bapp)
              have hDBeval_true : DBeval.fst = ZFSet.zftrue := by
                rw [hDBeval_eq_DBapp]
                exact hDBapp_true
              have hBval_app_true :
                  (ZFSet.fapply Bval (ZFSet.is_func_is_pfunc hBval_func)
                    ⟨Wb.fst, by
                      rw [ZFSet.is_func_dom_eq hBval_func]
                      exact hWb_mem⟩).val = ZFSet.zftrue := by
                exact hDBeval_value.symm.trans hDBeval_true
              obtain ⟨xb, hxb_Y, Wb_rel⟩ :=
                B_rel.setPred_target_of_true hWb_mem hBval_app_true
              have hcov_var_p : RenamingContext.CoversFV
                  (Function.update
                    (Function.update (Function.update Theta p (some Wp))
                      a (some Wa)) b (some Wb)) (SMT.Term.var p) := by
                intro v hv
                rw [SMT.fv, List.mem_singleton] at hv
                subst v
                simp [Function.update, hp_ne_a, hp_ne_b]
              have hden_var_p :
                  ⟦(SMT.Term.var p).abstract
                      (Function.update
                        (Function.update (Function.update Theta p (some Wp))
                          a (some Wa)) b (some Wb)) hcov_var_p⟧ˢ =
                    some Wp := by
                simp [SMT.Term.abstract.eq_def, SMT.denote,
                  Option.pure_def, Function.update, hp_ne_a, hp_ne_b]
              have hcov_var_a : RenamingContext.CoversFV
                  (Function.update
                    (Function.update (Function.update Theta p (some Wp))
                      a (some Wa)) b (some Wb)) (SMT.Term.var a) := by
                intro v hv
                rw [SMT.fv, List.mem_singleton] at hv
                subst v
                simp [Function.update, ha_ne_b]
              have hden_var_a :
                  ⟦(SMT.Term.var a).abstract
                      (Function.update
                        (Function.update (Function.update Theta p (some Wp))
                          a (some Wa)) b (some Wb)) hcov_var_a⟧ˢ =
                    some Wa := by
                simp [SMT.Term.abstract.eq_def, SMT.denote,
                  Option.pure_def, Function.update, ha_ne_b]
              have hcov_var_b : RenamingContext.CoversFV
                  (Function.update
                    (Function.update (Function.update Theta p (some Wp))
                      a (some Wa)) b (some Wb)) (SMT.Term.var b) := by
                intro v hv
                rw [SMT.fv, List.mem_singleton] at hv
                subst v
                simp [Function.update]
              have hden_var_b :
                  ⟦(SMT.Term.var b).abstract
                      (Function.update
                        (Function.update (Function.update Theta p (some Wp))
                          a (some Wa)) b (some Wb)) hcov_var_b⟧ˢ =
                    some Wb := by
                simp [SMT.Term.abstract.eq_def, SMT.denote,
                  Option.pure_def, Function.update]
              obtain ⟨Dpair, hden_pair_raw, hDpair_type⟩ :=
                denote_pair_some_of_some hden_var_a hden_var_b
              have hWp_Dpair_type : Wp.snd.fst = Dpair.snd.fst := by
                simpa [Wp, hWa_type, hWb_type] using hDpair_type.symm
              have hden_eq_split :
                  ⟦(SMT.Term.var p).abstract
                        (Function.update
                          (Function.update (Function.update Theta p (some Wp))
                            a (some Wa)) b (some Wb)) hcov_var_p =ˢ'
                      ((SMT.Term.var a).abstract
                        (Function.update
                          (Function.update (Function.update Theta p (some Wp))
                            a (some Wa)) b (some Wb)) hcov_var_a).pair
                        ((SMT.Term.var b).abstract
                          (Function.update
                            (Function.update (Function.update Theta p (some Wp))
                              a (some Wa)) b (some Wb)) hcov_var_b)⟧ˢ =
                    some Deq := by
                simpa [SMT.Term.abstract, proof_irrel_heq] using hden_eq
              have hWp_eq_Dpair_fst : Wp.fst = Dpair.fst := by
                exact denote_eq_true_implies_fst_eq
                  hden_var_p hden_pair_raw hWp_Dpair_type hden_eq_split hDeq_true
              have hDpair_fst : Dpair.fst = Wa.fst.pair Wb.fst := by
                have hpair_eq_raw := hden_pair_raw
                rw [SMT.denote, hden_var_a, hden_var_b] at hpair_eq_raw
                simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some,
                  Option.some.injEq] at hpair_eq_raw
                exact (congrArg (fun D : SMT.Dom => D.fst) hpair_eq_raw).symm
              have hy_pair : y = Wa.fst.pair Wb.fst :=
                hWp_eq_Dpair_fst.trans hDpair_fst
              have pair_rel_y :
                  RDomCastSupported
                    (⟨xa.pair xb, ⟨alpha ×ᴮ beta,
                      hprod_sub (ZFSet.pair_mem_prod.mpr
                        ⟨hxa_X, hxb_Y⟩)⟩⟩ : _root_.B.Dom)
                    (⟨y, ⟨rho.pair sigma, hy⟩⟩ : SMT.Dom) := by
                subst y
                exact RDomCastSupported.pair Wa_rel Wb_rel
              exact ⟨xa.pair xb, ZFSet.pair_mem_prod.mpr
                ⟨hxa_X, hxb_Y⟩, pair_rel_y⟩
            intro x hx
            obtain ⟨xa, hxa_X, xb, hxb_Y, rfl⟩ := ZFSet.mem_prod.mp hx
            obtain ⟨ya, hya, ya_rel⟩ :=
              A_rel.setPred_member_preimage hxa_X
            obtain ⟨yb, hyb, yb_rel⟩ :=
              B_rel.setPred_member_preimage hxb_Y
            have hy_pair : ya.pair yb ∈ ⟦rho.pair sigma⟧ᶻ :=
              ZFSet.pair_mem_prod.mpr ⟨hya, hyb⟩
            refine ⟨ya.pair yb, hy_pair, ?_, ?_⟩
            exact RDomCastSupported.pair ya_rel yb_rel
            refine ⟨hcov_exists
              (⟨ya.pair yb, ⟨rho.pair sigma, hy_pair⟩⟩ : SMT.Dom), ?_⟩
            refine ⟨(⟨ZFSet.zftrue, SMTType.bool,
              ZFSet.ZFBool.zftrue_mem_𝔹⟩ : SMT.Dom), ?_, rfl⟩
            let Wp : SMT.Dom :=
              ⟨ya.pair yb, ⟨rho.pair sigma, hy_pair⟩⟩
            let Wa : SMT.Dom := ⟨ya, ⟨rho, hya⟩⟩
            let Wb : SMT.Dom := ⟨yb, ⟨sigma, hyb⟩⟩
            have hAval_app_true :=
              (RDomCastSupported.setPred_fapply_eq_zftrue_iff
                ya_rel.toRDomCast A_rel).2 hxa_X
            have hBval_app_true :=
              (RDomCastSupported.setPred_fapply_eq_zftrue_iff
                yb_rel.toRDomCast B_rel).2 hxb_Y
            have hcov_A_p : RenamingContext.CoversFV
                (Function.update Theta p (some Wp)) A :=
              SMT.RenamingContext.coversFV_update_of_notMem
                (x := p) (d := Wp) hp_not_fv_A hcov_A
            have hcov_A_pa : RenamingContext.CoversFV
                (Function.update (Function.update Theta p (some Wp))
                  a (some Wa)) A :=
              SMT.RenamingContext.coversFV_update_of_notMem
                (x := a) (d := Wa) ha_not_fv_A hcov_A_p
            have hcov_A_pab : RenamingContext.CoversFV
                (Function.update
                  (Function.update (Function.update Theta p (some Wp))
                    a (some Wa)) b (some Wb)) A :=
              SMT.RenamingContext.coversFV_update_of_notMem
                (x := b) (d := Wb) hb_not_fv_A hcov_A_pa
            have hden_A_p_raw :
                ⟦A.abstract (Function.update Theta p (some Wp))
                    hcov_A_p⟧ˢ =
                  ⟦A.abstract Theta hcov_A⟧ˢ := by
              simpa [SMT.RenamingContext.denote] using
                (SMT.RenamingContext.denote_update_of_notMem
                  («Δ» := Theta) (t := A) (x := p) (d := Wp)
                  (h := hcov_A) hp_not_fv_A).symm
            have hden_A_pa_raw :
                ⟦A.abstract
                    (Function.update (Function.update Theta p (some Wp))
                      a (some Wa)) hcov_A_pa⟧ˢ =
                  ⟦A.abstract (Function.update Theta p (some Wp))
                    hcov_A_p⟧ˢ := by
              simpa [SMT.RenamingContext.denote] using
                (SMT.RenamingContext.denote_update_of_notMem
                  («Δ» := Function.update Theta p (some Wp))
                  (t := A) (x := a) (d := Wa)
                  (h := hcov_A_p) ha_not_fv_A).symm
            have hden_A_pab_raw :
                ⟦A.abstract
                    (Function.update
                      (Function.update (Function.update Theta p (some Wp))
                        a (some Wa)) b (some Wb)) hcov_A_pab⟧ˢ =
                  ⟦A.abstract
                    (Function.update (Function.update Theta p (some Wp))
                      a (some Wa)) hcov_A_pa⟧ˢ := by
              simpa [SMT.RenamingContext.denote] using
                (SMT.RenamingContext.denote_update_of_notMem
                  («Δ» := Function.update
                    (Function.update Theta p (some Wp)) a (some Wa))
                  (t := A) (x := b) (d := Wb)
                  (h := hcov_A_pa) hb_not_fv_A).symm
            have hden_A_pab :
                ⟦A.abstract
                    (Function.update
                      (Function.update (Function.update Theta p (some Wp))
                        a (some Wa)) b (some Wb)) hcov_A_pab⟧ˢ =
                  some ⟨Aval, ⟨rho.fun SMTType.bool, hAval⟩⟩ :=
              hden_A_pab_raw.trans
                (hden_A_pa_raw.trans (hden_A_p_raw.trans hden_A))
            have hAval_func :
                ZFSet.IsFunc ⟦rho⟧ᶻ ⟦SMTType.bool⟧ᶻ Aval := by
              simpa [SMTType.toZFSet] using hAval
            have hWa_mem : Wa.fst ∈ ⟦rho⟧ᶻ := by
              simpa [Wa] using hya
            have hcov_A_pab_a : ∀ Xarg : SMT.Dom,
                RenamingContext.CoversFV
                  (Function.update
                    (Function.update
                      (Function.update
                        (Function.update Theta p (some Wp)) a (some Wa))
                      b (some Wb)) a (some Xarg)) A :=
              fun Xarg =>
                SMT.RenamingContext.coversFV_update_of_notMem
                  (x := a) (d := Xarg) ha_not_fv_A hcov_A_pab
            have hden_A_pab_a_raw (Xarg : SMT.Dom) :
                ⟦A.abstract
                    (Function.update
                      (Function.update
                        (Function.update
                          (Function.update Theta p (some Wp)) a (some Wa))
                        b (some Wb)) a (some Xarg))
                    (hcov_A_pab_a Xarg)⟧ˢ =
                  ⟦A.abstract
                    (Function.update
                      (Function.update (Function.update Theta p (some Wp))
                        a (some Wa)) b (some Wb)) hcov_A_pab⟧ˢ := by
              simpa [SMT.RenamingContext.denote] using
                (SMT.RenamingContext.denote_update_of_notMem
                  («Δ» := Function.update
                    (Function.update
                      (Function.update Theta p (some Wp)) a (some Wa))
                    b (some Wb))
                  (t := A) (x := a) (d := Xarg)
                  (h := hcov_A_pab) ha_not_fv_A).symm
            have hden_A_pab_a : ∀ Xarg : SMT.Dom,
                ⟦A.abstract
                    (Function.update
                      (Function.update
                        (Function.update
                          (Function.update Theta p (some Wp)) a (some Wa))
                        b (some Wb)) a (some Xarg))
                    (hcov_A_pab_a Xarg)⟧ˢ =
                  some ⟨Aval, ⟨rho.fun SMTType.bool, hAval⟩⟩ :=
              fun Xarg => (hden_A_pab_a_raw Xarg).trans hden_A_pab
            obtain ⟨hcov_Aapp_eval, DAeval, hDAeval_type,
                hDAeval_value, hden_Aapp_eval⟩ :=
              funDenoteAppAt
                (Δctx := Function.update
                  (Function.update
                    (Function.update Theta p (some Wp)) a (some Wa))
                  b (some Wb))
                (t := A) (x := a)
                (α := rho) (β := SMTType.bool)
                (Y := (⟨Aval, ⟨rho.fun SMTType.bool, hAval⟩⟩ : SMT.Dom))
                hcov_A_pab_a hden_A_pab_a rfl hAval_func
                Wa rfl hWa_mem
            have hDAeval_true : DAeval.fst = ZFSet.zftrue := by
              exact hDAeval_value.trans (by
                simpa [Wa, proof_irrel_heq] using hAval_app_true)
            have hDAeval_eq_true :
                DAeval = (⟨ZFSet.zftrue, SMTType.bool,
                  ZFSet.ZFBool.zftrue_mem_𝔹⟩ : SMT.Dom) :=
              funDomEqOfTyEqAndFstEq hDAeval_type hDAeval_true
            have hctx_Aeval :
                Function.update
                    (Function.update
                      (Function.update
                        (Function.update Theta p (some Wp)) a (some Wa))
                      b (some Wb)) a (some Wa) =
                  Function.update
                    (Function.update (Function.update Theta p (some Wp))
                      a (some Wa)) b (some Wb) := by
              funext v
              by_cases hva : v = a
              · subst v
                simp [Function.update, ha_ne_b]
              · simp [Function.update, hva]
            have hcov_Aapp : RenamingContext.CoversFV
                (Function.update
                  (Function.update (Function.update Theta p (some Wp))
                    a (some Wa)) b (some Wb))
                ((@ˢA) (SMT.Term.var a)) := by
              intro v hv
              apply hcov_body Wp Wa Wb v
              simp only [body, SMT.fv, List.mem_append]
              simp only [SMT.fv, List.mem_append] at hv
              exact Or.inl hv
            have hden_Aapp_eval_full :
                ⟦((@ˢA) (SMT.Term.var a)).abstract
                    (Function.update
                      (Function.update (Function.update Theta p (some Wp))
                        a (some Wa)) b (some Wb)) hcov_Aapp⟧ˢ =
                  some DAeval := by
              simpa [hctx_Aeval, proof_irrel_heq] using hden_Aapp_eval
            have hden_Aapp_true :
                ⟦((@ˢA) (SMT.Term.var a)).abstract
                    (Function.update
                      (Function.update (Function.update Theta p (some Wp))
                        a (some Wa)) b (some Wb)) hcov_Aapp⟧ˢ =
                  some (⟨ZFSet.zftrue, SMTType.bool,
                    ZFSet.ZFBool.zftrue_mem_𝔹⟩ : SMT.Dom) :=
              hden_Aapp_eval_full.trans (congrArg some hDAeval_eq_true)
            have hcov_B_p : RenamingContext.CoversFV
                (Function.update Theta p (some Wp)) B :=
              SMT.RenamingContext.coversFV_update_of_notMem
                (x := p) (d := Wp) hp_not_fv_B hcov_B
            have hcov_B_pa : RenamingContext.CoversFV
                (Function.update (Function.update Theta p (some Wp))
                  a (some Wa)) B :=
              SMT.RenamingContext.coversFV_update_of_notMem
                (x := a) (d := Wa) ha_not_fv_B hcov_B_p
            have hcov_B_pab : RenamingContext.CoversFV
                (Function.update
                  (Function.update (Function.update Theta p (some Wp))
                    a (some Wa)) b (some Wb)) B :=
              SMT.RenamingContext.coversFV_update_of_notMem
                (x := b) (d := Wb) hb_not_fv_B hcov_B_pa
            have hden_B_p_raw :
                ⟦B.abstract (Function.update Theta p (some Wp))
                    hcov_B_p⟧ˢ =
                  ⟦B.abstract Theta hcov_B⟧ˢ := by
              simpa [SMT.RenamingContext.denote] using
                (SMT.RenamingContext.denote_update_of_notMem
                  («Δ» := Theta) (t := B) (x := p) (d := Wp)
                  (h := hcov_B) hp_not_fv_B).symm
            have hden_B_pa_raw :
                ⟦B.abstract
                    (Function.update (Function.update Theta p (some Wp))
                      a (some Wa)) hcov_B_pa⟧ˢ =
                  ⟦B.abstract (Function.update Theta p (some Wp))
                    hcov_B_p⟧ˢ := by
              simpa [SMT.RenamingContext.denote] using
                (SMT.RenamingContext.denote_update_of_notMem
                  («Δ» := Function.update Theta p (some Wp))
                  (t := B) (x := a) (d := Wa)
                  (h := hcov_B_p) ha_not_fv_B).symm
            have hden_B_pab_raw :
                ⟦B.abstract
                    (Function.update
                      (Function.update (Function.update Theta p (some Wp))
                        a (some Wa)) b (some Wb)) hcov_B_pab⟧ˢ =
                  ⟦B.abstract
                    (Function.update (Function.update Theta p (some Wp))
                      a (some Wa)) hcov_B_pa⟧ˢ := by
              simpa [SMT.RenamingContext.denote] using
                (SMT.RenamingContext.denote_update_of_notMem
                  («Δ» := Function.update
                    (Function.update Theta p (some Wp)) a (some Wa))
                  (t := B) (x := b) (d := Wb)
                  (h := hcov_B_pa) hb_not_fv_B).symm
            have hden_B_pab :
                ⟦B.abstract
                    (Function.update
                      (Function.update (Function.update Theta p (some Wp))
                        a (some Wa)) b (some Wb)) hcov_B_pab⟧ˢ =
                  some ⟨Bval, ⟨sigma.fun SMTType.bool, hBval⟩⟩ :=
              hden_B_pab_raw.trans
                (hden_B_pa_raw.trans (hden_B_p_raw.trans hden_B))
            have hBval_func :
                ZFSet.IsFunc ⟦sigma⟧ᶻ ⟦SMTType.bool⟧ᶻ Bval := by
              simpa [SMTType.toZFSet] using hBval
            have hWb_mem : Wb.fst ∈ ⟦sigma⟧ᶻ := by
              simpa [Wb] using hyb
            have hcov_B_pab_b : ∀ Xarg : SMT.Dom,
                RenamingContext.CoversFV
                  (Function.update
                    (Function.update
                      (Function.update
                        (Function.update Theta p (some Wp)) a (some Wa))
                      b (some Wb)) b (some Xarg)) B :=
              fun Xarg =>
                SMT.RenamingContext.coversFV_update_of_notMem
                  (x := b) (d := Xarg) hb_not_fv_B hcov_B_pab
            have hden_B_pab_b_raw (Xarg : SMT.Dom) :
                ⟦B.abstract
                    (Function.update
                      (Function.update
                        (Function.update
                          (Function.update Theta p (some Wp)) a (some Wa))
                        b (some Wb)) b (some Xarg))
                    (hcov_B_pab_b Xarg)⟧ˢ =
                  ⟦B.abstract
                    (Function.update
                      (Function.update (Function.update Theta p (some Wp))
                        a (some Wa)) b (some Wb)) hcov_B_pab⟧ˢ := by
              simpa [SMT.RenamingContext.denote] using
                (SMT.RenamingContext.denote_update_of_notMem
                  («Δ» := Function.update
                    (Function.update
                      (Function.update Theta p (some Wp)) a (some Wa))
                    b (some Wb))
                  (t := B) (x := b) (d := Xarg)
                  (h := hcov_B_pab) hb_not_fv_B).symm
            have hden_B_pab_b : ∀ Xarg : SMT.Dom,
                ⟦B.abstract
                    (Function.update
                      (Function.update
                        (Function.update
                          (Function.update Theta p (some Wp)) a (some Wa))
                        b (some Wb)) b (some Xarg))
                    (hcov_B_pab_b Xarg)⟧ˢ =
                  some ⟨Bval, ⟨sigma.fun SMTType.bool, hBval⟩⟩ :=
              fun Xarg => (hden_B_pab_b_raw Xarg).trans hden_B_pab
            obtain ⟨hcov_Bapp_eval, DBeval, hDBeval_type,
                hDBeval_value, hden_Bapp_eval⟩ :=
              funDenoteAppAt
                (Δctx := Function.update
                  (Function.update
                    (Function.update Theta p (some Wp)) a (some Wa))
                  b (some Wb))
                (t := B) (x := b)
                (α := sigma) (β := SMTType.bool)
                (Y := (⟨Bval, ⟨sigma.fun SMTType.bool, hBval⟩⟩ : SMT.Dom))
                hcov_B_pab_b hden_B_pab_b rfl hBval_func
                Wb rfl hWb_mem
            have hDBeval_true : DBeval.fst = ZFSet.zftrue := by
              exact hDBeval_value.trans (by
                simpa [Wb, proof_irrel_heq] using hBval_app_true)
            have hDBeval_eq_true :
                DBeval = (⟨ZFSet.zftrue, SMTType.bool,
                  ZFSet.ZFBool.zftrue_mem_𝔹⟩ : SMT.Dom) :=
              funDomEqOfTyEqAndFstEq hDBeval_type hDBeval_true
            have hctx_Beval :
                Function.update
                    (Function.update
                      (Function.update
                        (Function.update Theta p (some Wp)) a (some Wa))
                      b (some Wb)) b (some Wb) =
                  Function.update
                    (Function.update (Function.update Theta p (some Wp))
                      a (some Wa)) b (some Wb) := by
              funext v
              by_cases hvb : v = b
              · subst v
                simp [Function.update]
              · simp [Function.update, hvb]
            have hcov_Bapp : RenamingContext.CoversFV
                (Function.update
                  (Function.update (Function.update Theta p (some Wp))
                    a (some Wa)) b (some Wb))
                ((@ˢB) (SMT.Term.var b)) := by
              intro v hv
              apply hcov_body Wp Wa Wb v
              simp only [body, SMT.fv, List.mem_append]
              simp only [SMT.fv, List.mem_append] at hv
              exact Or.inr (Or.inl hv)
            have hden_Bapp_eval_full :
                ⟦((@ˢB) (SMT.Term.var b)).abstract
                    (Function.update
                      (Function.update (Function.update Theta p (some Wp))
                        a (some Wa)) b (some Wb)) hcov_Bapp⟧ˢ =
                  some DBeval := by
              simpa [hctx_Beval, proof_irrel_heq] using hden_Bapp_eval
            have hden_Bapp_true :
                ⟦((@ˢB) (SMT.Term.var b)).abstract
                    (Function.update
                      (Function.update (Function.update Theta p (some Wp))
                        a (some Wa)) b (some Wb)) hcov_Bapp⟧ˢ =
                  some (⟨ZFSet.zftrue, SMTType.bool,
                    ZFSet.ZFBool.zftrue_mem_𝔹⟩ : SMT.Dom) :=
              hden_Bapp_eval_full.trans (congrArg some hDBeval_eq_true)
            have hcov_var_p : RenamingContext.CoversFV
                (Function.update
                  (Function.update (Function.update Theta p (some Wp))
                    a (some Wa)) b (some Wb)) (SMT.Term.var p) := by
              intro v hv
              rw [SMT.fv, List.mem_singleton] at hv
              subst v
              simp [Function.update, hp_ne_a, hp_ne_b]
            have hden_var_p :
                ⟦(SMT.Term.var p).abstract
                    (Function.update
                      (Function.update (Function.update Theta p (some Wp))
                        a (some Wa)) b (some Wb)) hcov_var_p⟧ˢ =
                  some Wp := by
              simp [SMT.Term.abstract.eq_def, SMT.denote,
                Option.pure_def, Function.update, hp_ne_a, hp_ne_b]
            have hcov_var_a : RenamingContext.CoversFV
                (Function.update
                  (Function.update (Function.update Theta p (some Wp))
                    a (some Wa)) b (some Wb)) (SMT.Term.var a) := by
              intro v hv
              rw [SMT.fv, List.mem_singleton] at hv
              subst v
              simp [Function.update, ha_ne_b]
            have hden_var_a :
                ⟦(SMT.Term.var a).abstract
                    (Function.update
                      (Function.update (Function.update Theta p (some Wp))
                        a (some Wa)) b (some Wb)) hcov_var_a⟧ˢ =
                  some Wa := by
              simp [SMT.Term.abstract.eq_def, SMT.denote,
                Option.pure_def, Function.update, ha_ne_b]
            have hcov_var_b : RenamingContext.CoversFV
                (Function.update
                  (Function.update (Function.update Theta p (some Wp))
                    a (some Wa)) b (some Wb)) (SMT.Term.var b) := by
              intro v hv
              rw [SMT.fv, List.mem_singleton] at hv
              subst v
              simp [Function.update]
            have hden_var_b :
                ⟦(SMT.Term.var b).abstract
                    (Function.update
                      (Function.update (Function.update Theta p (some Wp))
                        a (some Wa)) b (some Wb)) hcov_var_b⟧ˢ =
                  some Wb := by
              simp [SMT.Term.abstract.eq_def, SMT.denote,
                Option.pure_def, Function.update]
            obtain ⟨Dpair, hden_pair_raw, hDpair_type⟩ :=
              denote_pair_some_of_some hden_var_a hden_var_b
            have hWp_Dpair_type : Wp.snd.fst = Dpair.snd.fst := by
              simpa [Wp, Wa, Wb] using hDpair_type.symm
            have hDpair_fst : Dpair.fst = Wa.fst.pair Wb.fst := by
              have hpair_eq_raw := hden_pair_raw
              rw [SMT.denote, hden_var_a, hden_var_b] at hpair_eq_raw
              simp only [Option.pure_def, Option.bind_eq_bind,
                Option.bind_some, Option.some.injEq] at hpair_eq_raw
              exact (congrArg (fun D : SMT.Dom => D.fst) hpair_eq_raw).symm
            have hWp_Dpair_fst : Wp.fst = Dpair.fst := by
              simpa [Wp, Wa, Wb] using hDpair_fst.symm
            have hden_eq_true_split :
                ⟦(SMT.Term.var p).abstract
                      (Function.update
                        (Function.update (Function.update Theta p (some Wp))
                          a (some Wa)) b (some Wb)) hcov_var_p =ˢ'
                    ((SMT.Term.var a).abstract
                      (Function.update
                        (Function.update (Function.update Theta p (some Wp))
                          a (some Wa)) b (some Wb)) hcov_var_a).pair
                      ((SMT.Term.var b).abstract
                        (Function.update
                          (Function.update (Function.update Theta p (some Wp))
                            a (some Wa)) b (some Wb)) hcov_var_b)⟧ˢ =
                  some (⟨ZFSet.zftrue, SMTType.bool,
                    ZFSet.ZFBool.zftrue_mem_𝔹⟩ : SMT.Dom) :=
              denote_eq_eq_zftrue_of_fst_eq hden_var_p hden_pair_raw
                hWp_Dpair_type hWp_Dpair_fst
            have hcov_eq : RenamingContext.CoversFV
                (Function.update
                  (Function.update (Function.update Theta p (some Wp))
                    a (some Wa)) b (some Wb))
                ((SMT.Term.var p) =ˢ
                  ((SMT.Term.var a).pair (SMT.Term.var b))) := by
              intro v hv
              apply hcov_body Wp Wa Wb v
              simp only [body, SMT.fv, List.mem_append]
              simp only [SMT.fv, List.mem_append] at hv
              exact Or.inr (Or.inr hv)
            have hden_eq_true :
                ⟦((SMT.Term.var p) =ˢ
                    ((SMT.Term.var a).pair (SMT.Term.var b))).abstract
                    (Function.update
                      (Function.update (Function.update Theta p (some Wp))
                        a (some Wa)) b (some Wb)) hcov_eq⟧ˢ =
                  some (⟨ZFSet.zftrue, SMTType.bool,
                    ZFSet.ZFBool.zftrue_mem_𝔹⟩ : SMT.Dom) := by
              simpa [SMT.Term.abstract, proof_irrel_heq] using
                hden_eq_true_split
            have hden_right_true_split :
                ⟦((@ˢB) (SMT.Term.var b)).abstract
                      (Function.update
                        (Function.update (Function.update Theta p (some Wp))
                          a (some Wa)) b (some Wb)) hcov_Bapp ∧ˢ'
                    (((SMT.Term.var p) =ˢ
                      ((SMT.Term.var a).pair (SMT.Term.var b))).abstract
                      (Function.update
                        (Function.update (Function.update Theta p (some Wp))
                          a (some Wa)) b (some Wb)) hcov_eq)⟧ˢ =
                  some (⟨ZFSet.zftrue, SMTType.bool,
                    ZFSet.ZFBool.zftrue_mem_𝔹⟩ : SMT.Dom) :=
              denote_and_eq_zftrue_of_some_zftrue
                hden_Bapp_true rfl rfl hden_eq_true rfl rfl
            have hden_body_true_split :
                ⟦((@ˢA) (SMT.Term.var a)).abstract
                      (Function.update
                        (Function.update (Function.update Theta p (some Wp))
                          a (some Wa)) b (some Wb)) hcov_Aapp ∧ˢ'
                    (((@ˢB) (SMT.Term.var b)).abstract
                        (Function.update
                          (Function.update (Function.update Theta p (some Wp))
                            a (some Wa)) b (some Wb)) hcov_Bapp ∧ˢ'
                      (((SMT.Term.var p) =ˢ
                        ((SMT.Term.var a).pair (SMT.Term.var b))).abstract
                        (Function.update
                          (Function.update (Function.update Theta p (some Wp))
                            a (some Wa)) b (some Wb)) hcov_eq))⟧ˢ =
                  some (⟨ZFSet.zftrue, SMTType.bool,
                    ZFSet.ZFBool.zftrue_mem_𝔹⟩ : SMT.Dom) :=
              denote_and_eq_zftrue_of_some_zftrue
                hden_Aapp_true rfl rfl hden_right_true_split rfl rfl
            refine funBinaryExistsEqZftrueAtWitness
              (hcov_exists Wp) (hgo_body Wp)
              (fun Wa Wb => hcov_body Wp Wa Wb)
              (fun Wa Wb hWa hWb =>
                body_total Wp Wa Wb rfl hWa hWb)
              (fun Wa Wb hWa hWb D hden =>
                body_type Wp Wa Wb rfl hWa hWb hden)
              (D := (⟨ZFSet.zftrue, SMTType.bool,
                ZFSet.ZFBool.zftrue_mem_𝔹⟩ : SMT.Dom))
              Wa Wb rfl rfl (by
                simpa [body, SMT.Term.abstract, proof_irrel_heq] using
                  hden_body_true_split) rfl
          refine ⟨Theta, (by simpa [tcprod, body] using hcov_tcprod),
            denOut, ?_⟩
          and_intros
          · exact RenamingContext.extends_refl Theta
          · intro v hv
            apply Theta_none
            intro hvused
            apply hv
            rw [StEb_used_eq, StEa_used_eq, StEp_used_eq,
              St₃_used_eq, St₂_used_eq, St₁_used_eq]
            exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ hvused))
          · simpa [StEb_types_final, tcprod, body] using target_respects
          · intro v hv
            rw [StEb_types_final]
            exact Theta_dom v hv
          · simpa [tcprod, body] using hdenOut
          · exact hdenOut_type
          · exact Out_rel.1.1
          · exact Out_rel.1.2
          · exact Out_rel.2

private abbrev EncodeCprodTailRepScopedSpec.{u}
    (alpha beta : BType) (rho sigma : SMTType)
    (_hrho : BType.SupportedSMT alpha rho)
    (_hsigma : BType.SupportedSMT beta sigma)
    (A B : SMT.Term) : Prop :=
  ∀ {Lambda : SMT.TypeContext} {n : ℕ} {used : List SMT.𝒱}
    {decl : SMT.Chunk},
    Lambda ⊢ˢ A : SMTType.fun rho SMTType.bool →
    Lambda ⊢ˢ B : SMTType.fun sigma SMTType.bool →
    (∀ v ∈ SMT.bv A, v ∈ used) →
    (∀ v ∈ SMT.bv B, v ∈ used) →
    ⦃fun ⟨env, Lambda'⟩ =>
      ⌜Lambda' = Lambda ∧ env.freshvarsc = n ∧
        Lambda.keys ⊆ env.usedVars ∧ env.usedVars = used ∧
        env.declarations = decl⌝⦄
    encodeCprodTail A B rho sigma
    ⦃⇓? ⟨out, sigmaOut⟩ ⟨env', Gamma'⟩ =>
      ⌜used ⊆ env'.usedVars ∧
        Lambda ⊆ Gamma' ∧
        Gamma'.keys ⊆ env'.usedVars ∧
        Nonempty (sigmaOut ~>
          (BType.set (alpha ×ᴮ beta)).toSMTType) ∧
        Gamma' ⊢ˢ out : sigmaOut ∧
        (∀ v ∈ used, v ∉ Lambda → v ∉ Gamma') ∧
        EncodeCprodTailRepTotalSemantics.{u}
          alpha beta A B out sigmaOut Lambda Gamma'
          used env'.usedVars ∧
        Gamma' = Lambda ∧ env'.declarations = decl ∧
        (∀ v ∈ SMT.fv A, v ∈ SMT.fv out) ∧
        (∀ v ∈ SMT.fv B, v ∈ SMT.fv out) ∧
        SMT.fv out ⊆ SMT.fv A ++ SMT.fv B ∧
        EncodeCprodTailRepGuardedSemantics.{u}
          alpha beta A B out rho sigma sigmaOut
          Lambda used⌝⦄

set_option maxHeartbeats 7000000 in
private theorem encodeCprodTail_rep_scoped_spec.{u}
    (alpha beta : BType) (rho sigma : SMTType)
    (hrho : BType.SupportedSMT alpha rho)
    (hsigma : BType.SupportedSMT beta sigma)
    (A B : SMT.Term) :
    EncodeCprodTailRepScopedSpec.{u}
      alpha beta rho sigma hrho hsigma A B := by
  unfold EncodeCprodTailRepScopedSpec
  intro Lambda n used decl typA typB bvA_used bvB_used
  mstart
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_keys, rfl, rfl⟩ := pre
  mspec (Std.Do.Triple.and _
    (encodeCprodTail_rep_spec alpha beta rho sigma hrho hsigma A B
      typA typB bvA_used bvB_used)
    (encodeCprodTail_shape_decls A B rho sigma
      (n := St.env.freshvarsc) (used := St.env.usedVars)
      (decl := St.env.declarations)))
  rename_i outPair
  obtain ⟨out, sigmaOut⟩ := outPair
  mrename_i post
  mintro ∀StOut
  mpure post
  obtain ⟨opPost, shape⟩ := post
  obtain ⟨usedSub, typesSub, keysSub, path, typOut,
    preserves, total⟩ := opPost
  obtain ⟨p, a, b, outEq, sigmaEq, typesEq, declEq,
    pFresh, aFresh, bFresh, hp_ne_a, hp_ne_b, ha_ne_b⟩ := shape
  dsimp at outEq sigmaEq
  subst out
  subst sigmaOut
  have p_not_fv_A : p ∉ SMT.fv A :=
    funNotMemFvOfNotMemContext typA pFresh
  have p_not_fv_B : p ∉ SMT.fv B :=
    funNotMemFvOfNotMemContext typB pFresh
  have a_not_fv_A : a ∉ SMT.fv A :=
    funNotMemFvOfNotMemContext typA aFresh
  have a_not_fv_B : a ∉ SMT.fv B :=
    funNotMemFvOfNotMemContext typB aFresh
  have b_not_fv_A : b ∉ SMT.fv A :=
    funNotMemFvOfNotMemContext typA bFresh
  have b_not_fv_B : b ∉ SMT.fv B :=
    funNotMemFvOfNotMemContext typB bFresh
  have observesA : ∀ v ∈ SMT.fv A,
      v ∈ SMT.fv (.lambda [p] [.pair rho sigma]
        (.exists [a, b] [rho, sigma]
          (.and (.app A (.var a))
            (.and (.app B (.var b))
              (.eq (.var p) (.pair (.var a) (.var b))))))) := by
    intro v hv
    apply SMT.fv.mem_lambda
    constructor
    · apply SMT.fv.mem_exists
      constructor
      · exact SMT.fv.mem_and (.inl (SMT.fv.mem_app (.inl hv)))
      · intro h
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
        rcases h with rfl | rfl
        · exact a_not_fv_A hv
        · exact b_not_fv_A hv
    · intro h
      rw [List.mem_singleton] at h
      subst v
      exact p_not_fv_A hv
  have observesB : ∀ v ∈ SMT.fv B,
      v ∈ SMT.fv (.lambda [p] [.pair rho sigma]
        (.exists [a, b] [rho, sigma]
          (.and (.app A (.var a))
            (.and (.app B (.var b))
              (.eq (.var p) (.pair (.var a) (.var b))))))) := by
    intro v hv
    apply SMT.fv.mem_lambda
    constructor
    · apply SMT.fv.mem_exists
      constructor
      · apply SMT.fv.mem_and
        right
        exact SMT.fv.mem_and (.inl (SMT.fv.mem_app (.inl hv)))
      · intro h
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
        rcases h with rfl | rfl
        · exact a_not_fv_B hv
        · exact b_not_fv_B hv
    · intro h
      rw [List.mem_singleton] at h
      subst v
      exact p_not_fv_B hv
  have fvSubset := cprod_lambda_fv_subset A B p a b rho sigma
  mpure_intro
  refine ⟨usedSub, typesSub, keysSub, path, typOut, preserves,
    total, typesEq, declEq, observesA, observesB, fvSubset, ?_⟩
  intro Core Core_sub Core_keys typA_Core typB_Core Theta
    hcovA hcovB respectsA respectsB X Y hX hY denA denB
    hdenA hdenB Xrel Yrel hcovOut denOut hdenOut hdenOutType
  let ThetaR : SMT.RenamingContext.Context.{u} := fun v =>
    if v ∈ Core then Theta v else none
  have A_fv_Core : ∀ v ∈ SMT.fv A, v ∈ Core :=
    fun v hv => SMT.Typing.mem_context_of_mem_fv typA_Core hv
  have B_fv_Core : ∀ v ∈ SMT.fv B, v ∈ Core :=
    fun v hv => SMT.Typing.mem_context_of_mem_fv typB_Core hv
  have hcovA_R : RenamingContext.CoversFV ThetaR A := by
    intro v hv
    simp [ThetaR, A_fv_Core v hv, hcovA v hv]
  have hcovB_R : RenamingContext.CoversFV ThetaR B := by
    intro v hv
    simp [ThetaR, B_fv_Core v hv, hcovB v hv]
  have agreesA : RenamingContext.AgreesOnFV ThetaR Theta A := by
    intro v hv
    simp [ThetaR, A_fv_Core v hv]
  have agreesB : RenamingContext.AgreesOnFV ThetaR Theta B := by
    intro v hv
    simp [ThetaR, B_fv_Core v hv]
  have hdenA_R : ⟦A.abstract ThetaR hcovA_R⟧ˢ = some denA :=
    (RenamingContext.denote_congr_of_agreesOnFV
      (h1 := hcovA_R) (h2 := hcovA) agreesA).trans hdenA
  have hdenB_R : ⟦B.abstract ThetaR hcovB_R⟧ˢ = some denB :=
    (RenamingContext.denote_congr_of_agreesOnFV
      (h1 := hcovB_R) (h2 := hcovB) agreesB).trans hdenB
  have ThetaR_none : ∀ v ∉ St.env.usedVars, ThetaR v = none := by
    intro v hv
    by_cases hvCore : v ∈ Core
    · exact absurd (Core_keys ((AList.mem_keys).mp hvCore)) hv
    · simp [ThetaR, hvCore]
  have ThetaR_dom : ∀ v, ThetaR v ≠ none → v ∈ St.types := by
    intro v hv
    by_cases hvCore : v ∈ Core
    · exact AList.mem_of_subset Core_sub hvCore
    · simp [ThetaR, hvCore] at hv
  have respectsA_R :
      SMT.RenamingContext.RespectsTypeContextOnFV
        ThetaR St.types A := by
    intro v tau hv hlookup
    have hvCore := A_fv_Core v hv
    obtain ⟨tauCore, hlookupCore⟩ := Option.isSome_iff_exists.mp
      (AList.lookup_isSome.mpr hvCore)
    have hlookup' := AList.lookup_of_subset Core_sub hlookupCore
    rw [hlookup'] at hlookup
    cases hlookup
    obtain ⟨d, hd, hdType⟩ := respectsA hv hlookupCore
    exact ⟨d, by simpa [ThetaR, hvCore] using hd, hdType⟩
  have respectsB_R :
      SMT.RenamingContext.RespectsTypeContextOnFV
        ThetaR St.types B := by
    intro v tau hv hlookup
    have hvCore := B_fv_Core v hv
    obtain ⟨tauCore, hlookupCore⟩ := Option.isSome_iff_exists.mp
      (AList.lookup_isSome.mpr hvCore)
    have hlookup' := AList.lookup_of_subset Core_sub hlookupCore
    rw [hlookup'] at hlookup
    cases hlookup
    obtain ⟨d, hd, hdType⟩ := respectsB hv hlookupCore
    exact ⟨d, by simpa [ThetaR, hvCore] using hd, hdType⟩
  obtain ⟨ThetaOut, hcovOutR, denOutR, ThetaOut_ext,
      _ThetaOut_none, _respectsOut, _ThetaOut_dom,
      hdenOutR, _hdenOutRType, OutRel⟩ :=
    total ThetaR hcovA_R hcovB_R ThetaR_none
      respectsA_R respectsB_R ThetaR_dom X Y hX hY denA denB
      hdenA_R hdenB_R Xrel Yrel
  have output_fv_Core : ∀ v ∈ SMT.fv
      (.lambda [p] [.pair rho sigma]
        (.exists [a, b] [rho, sigma]
          (.and (.app A (.var a))
            (.and (.app B (.var b))
              (.eq (.var p) (.pair (.var a) (.var b))))))),
      v ∈ Core := by
    intro v hv
    rcases List.mem_append.mp (fvSubset hv) with hvA | hvB
    · exact A_fv_Core v hvA
    · exact B_fv_Core v hvB
  have hcovOut_R0 : RenamingContext.CoversFV ThetaR
      (.lambda [p] [.pair rho sigma]
        (.exists [a, b] [rho, sigma]
          (.and (.app A (.var a))
            (.and (.app B (.var b))
              (.eq (.var p) (.pair (.var a) (.var b))))))) := by
    intro v hv
    simp [ThetaR, output_fv_Core v hv, hcovOut v hv]
  have agreesOutR : RenamingContext.AgreesOnFV ThetaOut ThetaR
      (.lambda [p] [.pair rho sigma]
        (.exists [a, b] [rho, sigma]
          (.and (.app A (.var a))
            (.and (.app B (.var b))
              (.eq (.var p) (.pair (.var a) (.var b))))))) :=
    RenamingContext.agreesOnFV_of_extends_of_coversFV
      ThetaOut_ext hcovOut_R0
  have agreesRTheta : RenamingContext.AgreesOnFV ThetaR Theta
      (.lambda [p] [.pair rho sigma]
        (.exists [a, b] [rho, sigma]
          (.and (.app A (.var a))
            (.and (.app B (.var b))
              (.eq (.var p) (.pair (.var a) (.var b))))))) := by
    intro v hv
    simp [ThetaR, output_fv_Core v hv]
  have agreesOut : RenamingContext.AgreesOnFV ThetaOut Theta
      (.lambda [p] [.pair rho sigma]
        (.exists [a, b] [rho, sigma]
          (.and (.app A (.var a))
            (.and (.app B (.var b))
              (.eq (.var p) (.pair (.var a) (.var b))))))) :=
    RenamingContext.agreesOnFV_trans agreesOutR agreesRTheta
  have hden_congr := RenamingContext.denote_congr_of_agreesOnFV
    (h1 := hcovOutR) (h2 := hcovOut) agreesOut
  have denOutEq : denOutR = denOut :=
    Option.some.inj (hdenOutR.symm.trans (hden_congr.trans hdenOut))
  subst denOutR
  simpa only [proof_irrel_heq] using OutRel

set_option maxHeartbeats 7000000 in
theorem encodeTerm_rep_spec.cprod_case.{u}
    (S T : B.Term)
    (S_ih : EncodeTermRepIH.{u} S)
    (T_ih : EncodeTermRepIH.{u} T)
    (E : B.Env) {Lambda : SMT.TypeContext} {tau : BType}
    (typ_t : E.context ⊢ᴮ B.Term.cprod S T : tau)
    {Delta : B.RenamingContext.Context}
    (Delta_fv : ∀ v ∈ B.fv (B.Term.cprod S T),
      (Delta v).isSome = true)
    {Delta0 : SMT.RenamingContext.Context.{u}}
    (related : RValuationCastSupportedOnFV Delta Delta0
      (B.Term.cprod S T))
    {used : List SMT.𝒱}
    (Delta0_none : ∀ v ∉ used, Delta0 v = none)
    (Delta0_dom : ∀ v, Delta0 v ≠ none → v ∈ Lambda)
    {U : ZFSet.{u}} {hU : U ∈ ⟦tau⟧ᶻ}
    (den_t : ⟦(B.Term.cprod S T).abstract Delta Delta_fv⟧ᴮ =
      some ⟨U, tau, hU⟩)
    (vars_used : ∀ v ∈ (B.Term.cprod S T).vars, v ∈ used)
    (Lambda_inv : ∀ v ∈ (B.Term.cprod S T).vars,
      v ∈ Lambda → v ∈ E.context)
    (bv_nodup : (B.bv (B.Term.cprod S T)).Nodup)
    (respects : B.RenamingContext.RespectsTypeContextOnFV
      Delta0 Lambda (B.Term.cprod S T))
    (fv_in_Lambda : ∀ v ∈ B.fv (B.Term.cprod S T), v ∈ Lambda)
    (wf : B.RenWF E.context Delta)
    {n : ℕ} :
    ⦃fun ⟨E0, Lambda'⟩ =>
      ⌜Lambda' = Lambda ∧ E0.freshvarsc = n ∧
        Lambda.keys ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
    encodeTerm (B.Term.cprod S T) E
    ⦃⇓? (⟨t', sigma⟩ : SMT.Term × SMTType) ⟨E', Gamma'⟩ =>
      ⌜EncodeTermRepPost (B.Term.cprod S T) tau Lambda Delta Delta0
        used U hU E t' sigma E' Gamma'⌝⦄ := by
  mstart
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_keys, St_used_eq⟩ := pre
  rw [encodeTerm_cprod_via_tail]
  obtain ⟨alpha, beta, rfl, typ_S, typ_T⟩ := B.Typing.cprodE typ_t
  obtain ⟨X, Y, hX, hY, den_S, den_T, rfl⟩ :=
    B.denote_cprod_inv_rep Delta_fv den_t
  have fv_S_sub : B.fv S ⊆ B.fv (B.Term.cprod S T) := by
    intro v hv
    simpa [B.fv] using (Or.inl hv : v ∈ B.fv S ∨ v ∈ B.fv T)
  have fv_T_sub : B.fv T ⊆ B.fv (B.Term.cprod S T) := by
    intro v hv
    simpa [B.fv] using (Or.inr hv : v ∈ B.fv S ∨ v ∈ B.fv T)
  have S_bv_nodup : (B.bv S).Nodup := by
    have h := bv_nodup
    simp only [B.bv, List.nodup_append] at h
    exact h.1
  have T_bv_nodup : (B.bv T).Nodup := by
    have h := bv_nodup
    simp only [B.bv, List.nodup_append] at h
    exact h.2.1
  have ST_bv_disj : ∀ a ∈ B.bv S, ∀ b ∈ B.bv T, a ≠ b := by
    have h := bv_nodup
    simp only [B.bv, List.nodup_append] at h
    exact h.2.2

  mspec (Std.Do.Triple.and _
    (Std.Do.Triple.and _
      (S_ih E typ_S
        (fun v hv => Delta_fv v (fv_S_sub hv))
        (related.mono_fv fv_S_sub)
        Delta0_none Delta0_dom den_S
        (fun v hv => vars_used v (by
          simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
            List.mem_append] at hv ⊢
          rcases hv with h | h <;> [left; right] <;> exact .inl h))
        (fun v hv => Lambda_inv v (by
          simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
            List.mem_append] at hv ⊢
          rcases hv with h | h <;> [left; right] <;> exact .inl h))
        S_bv_nodup (respects.mono_fv fv_S_sub)
        (fun v hv => fv_in_Lambda v (fv_S_sub hv)) wf
        (n := St.env.freshvarsc))
      (encodeTerm_bv_used E (t := S) (used := St.env.usedVars)
        (n := St.env.freshvarsc) (decl := St.env.declarations)))
    (encodeTerm_bv_notMem_used E (t := S) (used := St.env.usedVars)
      (n := St.env.freshvarsc) (decl := St.env.declarations)))
  clear S_ih
  rename_i out_S
  obtain ⟨Senc, sigmaS⟩ := out_S
  mrename_i post_S
  mintro ∀StS
  mpure post_S
  dsimp at post_S
  obtain ⟨⟨S_post, bv_Senc_used, _S_used_sub, _S_decl⟩,
      bv_Senc_not_used, _S_used_sub', _S_decl'⟩ := post_S
  obtain ⟨used_sub_S, types_sub_S, keys_sub_S, covers_S,
    _path_S, typ_Senc, _shape_S, preserves_S,
    DeltaS, hcov_Senc, DeltaS_ext, _related_S, DeltaS_none,
    _respects_S, target_respects_Senc, DeltaS_dom,
    denSenc, hden_Senc, hdenSenc_type, S_rel, S_total⟩ := S_post
  rcases denSenc with ⟨Sval, sigmaSden, hSval⟩
  dsimp at hdenSenc_type
  subst sigmaSden
  cases S_rel.supported with
  | optionFun gamma delta =>
      exact wp_bind_throw _ _ _ _
  | @setPred _ rho hrho =>
    have related_T : RValuationCastSupportedOnFV Delta DeltaS T :=
      (related.mono_fv fv_T_sub).of_extends DeltaS_ext
    have respects_T : B.RenamingContext.RespectsTypeContextOnFV
        DeltaS StS.types T :=
      respects.of_extends DeltaS_ext types_sub_S fv_T_sub fv_in_Lambda
    mspec (Std.Do.Triple.and _
      (T_ih E typ_T
        (fun v hv => Delta_fv v (fv_T_sub hv)) related_T
        DeltaS_none DeltaS_dom den_T
        (fun v hv => used_sub_S (vars_used v (by
          simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
            List.mem_append] at hv ⊢
          rcases hv with h | h <;> [left; right] <;> exact .inr h)))
        (fun v hv hGamma => by
          have hv_cprod : v ∈ (B.Term.cprod S T).vars := by
            simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
              List.mem_append] at hv ⊢
            rcases hv with h | h <;> [left; right] <;> exact .inr h
          by_cases hv_Lambda : v ∈ St.types
          · exact Lambda_inv v hv_cprod hv_Lambda
          · have hv_vars_S : v ∈ B.Term.vars S := by
              by_contra hnot
              exact absurd hGamma
                (preserves_S v (vars_used v hv_cprod) hv_Lambda hnot)
            rcases B.Term.mem_vars_iff.mp hv_vars_S with hSfv | hSbv
            · exact B.Typing.typed_by_fv typ_S hSfv
            · rcases B.Term.mem_vars_iff.mp hv with hTfv | hTbv
              · exact absurd (B.Typing.typed_by_fv typ_T hTfv)
                  (B.Typing.bv_notMem_context typ_S v hSbv)
              · exact absurd rfl (ST_bv_disj v hSbv v hTbv))
        T_bv_nodup respects_T
        (fun v hv => AList.mem_of_subset types_sub_S
          (fv_in_Lambda v (fv_T_sub hv))) wf
        (n := StS.env.freshvarsc))
      (encodeTerm_bv_used E (t := T) (used := StS.env.usedVars)
        (n := StS.env.freshvarsc) (decl := StS.env.declarations)))
    clear T_ih
    rename_i out_T
    obtain ⟨Tenc, sigmaT⟩ := out_T
    mrename_i post_T
    mintro ∀StT
    mpure post_T
    dsimp at post_T
    obtain ⟨T_post, bv_Tenc_used, _T_used_sub, _T_decl⟩ := post_T
    obtain ⟨used_sub_T, types_sub_T, keys_sub_T, covers_T,
      _path_T, typ_Tenc, _shape_T, preserves_T,
      DeltaT, hcov_Tenc, DeltaT_ext, _related_T, DeltaT_none,
      _respects_T, target_respects_Tenc, DeltaT_dom,
      denTenc, hden_Tenc, hdenTenc_type, T_rel, T_total⟩ := T_post
    rcases denTenc with ⟨Tval, sigmaTden, hTval⟩
    dsimp at hdenTenc_type
    subst sigmaTden
    cases T_rel.supported with
    | optionFun gamma delta =>
        exact wp_bind_throw _ _ _ _
    | @setPred _ sigma hsigma =>
      have bv_Senc_final : ∀ v ∈ SMT.bv Senc,
          v ∈ StT.env.usedVars :=
        fun v hv => used_sub_T (bv_Senc_used v hv)
      have bv_Senc_not_final : ∀ v ∈ SMT.bv Senc,
          v ∉ StT.types :=
        fun v hv => preserves_T v (bv_Senc_used v hv)
          (SMT.Typing.bv_notMem_context typ_Senc v hv)
          (by
            rw [B.Term.notMem_vars_iff]
            refine ⟨?_, ?_⟩
            · intro hfvT
              exact SMT.Typing.bv_notMem_context typ_Senc v hv
                (AList.mem_of_subset types_sub_S
                  (fv_in_Lambda v (fv_T_sub hfvT)))
            · intro hbT
              exact bv_Senc_not_used v hv
                (St_used_eq ▸ vars_used v (by
                  simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
                    List.mem_append]
                  right
                  right
                  exact hbT)))
      have typ_Senc_final : StT.types ⊢ˢ Senc :
          SMTType.fun rho SMTType.bool :=
        SMT.Typing.weakening types_sub_T typ_Senc bv_Senc_not_final
      have hcov_Senc_final : RenamingContext.CoversFV DeltaT Senc :=
        RenamingContext.coversFV_of_extends_of_coversFV
          DeltaT_ext hcov_Senc
      have hden_Senc_final :
          ⟦Senc.abstract DeltaT hcov_Senc_final⟧ˢ =
            some (⟨Sval, SMTType.fun rho SMTType.bool, hSval⟩ :
              SMT.Dom) := by
        have hagree := RenamingContext.agreesOnFV_of_extends_of_coversFV
          DeltaT_ext hcov_Senc
        have hcongr := RenamingContext.denote_congr_of_agreesOnFV
          (t := Senc) (h1 := hcov_Senc_final)
          (h2 := hcov_Senc) hagree
        simpa [RenamingContext.denote] using hcongr.trans hden_Senc
      have target_respects_Senc_final :
          SMT.RenamingContext.RespectsTypeContextOnFV
            DeltaT StT.types Senc :=
        target_respects_Senc.of_extends
          DeltaT_ext types_sub_T typ_Senc

      mspec encodeCprodTail_rep_spec alpha beta rho sigma hrho hsigma
        Senc Tenc
        typ_Senc_final typ_Tenc bv_Senc_final bv_Tenc_used
      rename_i out_prod
      obtain ⟨ProdEnc, sigmaProd⟩ := out_prod
      mrename_i post_prod
      mintro ∀StProd
      mpure post_prod
      obtain ⟨used_sub_prod, types_sub_prod, keys_sub_prod, path_prod,
        typ_ProdEnc, preserves_prod, semantic_prod⟩ := post_prod
      obtain ⟨DeltaProd, hcov_ProdEnc, denProd, DeltaProd_ext,
          DeltaProd_none, target_respects_ProdEnc, DeltaProd_dom,
          hden_ProdEnc, hdenProd_type, Prod_rel⟩ :=
        semantic_prod DeltaT hcov_Senc_final hcov_Tenc DeltaT_none
          target_respects_Senc_final target_respects_Tenc DeltaT_dom
          X Y hX hY
          (⟨Sval, SMTType.fun rho SMTType.bool, hSval⟩ : SMT.Dom)
          (⟨Tval, SMTType.fun sigma SMTType.bool, hTval⟩ : SMT.Dom)
          hden_Senc_final hden_Tenc S_rel T_rel
      have DeltaT_ext0 := RenamingContext.extends_trans DeltaT_ext DeltaS_ext
      have DeltaProd_ext0 :=
        RenamingContext.extends_trans DeltaProd_ext DeltaT_ext0
      have types_sub0 : St.types ⊆ StProd.types :=
        fun _ h => types_sub_prod (types_sub_T (types_sub_S h))

      mpure_intro
      and_intros
      · intro v hv
        exact used_sub_prod (used_sub_T
          (used_sub_S (by simpa [St_used_eq] using hv)))
      · exact types_sub0
      · exact keys_sub_prod
      · intro v hv
        rw [B.fv, List.mem_append] at hv
        exact hv.elim
          (fun h => used_sub_prod (used_sub_T (covers_S v h)))
          (fun h => used_sub_prod (covers_T v h))
      · exact path_prod
      · exact typ_ProdEnc
      · trivial
      · intro v hv hLambda hvars
        have hv_StS : v ∈ StS.env.usedVars :=
          used_sub_S (by simpa [St_used_eq] using hv)
        have hv_not_StS : v ∉ StS.types :=
          preserves_S v (by simpa [St_used_eq] using hv) hLambda
            ((B.Term.notMem_vars_cprod.mp hvars).1)
        have hv_not_StT : v ∉ StT.types :=
          preserves_T v hv_StS hv_not_StS
            ((B.Term.notMem_vars_cprod.mp hvars).2)
        exact preserves_prod v (used_sub_T hv_StS) hv_not_StT
      · refine ⟨DeltaProd, hcov_ProdEnc, DeltaProd_ext0,
          related.of_extends DeltaProd_ext0, DeltaProd_none, ?_,
          target_respects_ProdEnc, DeltaProd_dom, denProd,
          hden_ProdEnc, hdenProd_type, ?_, ?_⟩
        · exact respects.of_extends DeltaProd_ext0 types_sub0
            (fun _ h => h) fv_in_Lambda
        · simpa only [proof_irrel_heq] using Prod_rel
        · intro Delta_alt Delta_fv_alt Delta0_alt related_alt wf_alt
            Delta0_alt_none respects_alt Delta0_alt_dom
            U_alt hU_alt den_t_alt
          obtain ⟨X_alt, Y_alt, hX_alt, hY_alt,
              den_S_alt, den_T_alt, rfl⟩ :=
            B.denote_cprod_inv_rep Delta_fv_alt den_t_alt
          have Delta0_alt_none_S : ∀ v ∉ StS.env.usedVars,
              Delta0_alt v = none := by
            intro v hv
            by_contra hne
            have hv_Lambda := Delta0_alt_dom v hne
            have hv_used : v ∈ used := by
              rw [← St_used_eq]
              exact St_keys hv_Lambda
            exact hv (used_sub_S hv_used)
          obtain ⟨DeltaS_alt, hcov_Senc_alt, denSenc_alt,
              DeltaS_alt_ext, _related_S_alt, DeltaS_alt_none,
              _respects_S_alt, target_respects_Senc_alt,
              DeltaS_alt_dom, hden_Senc_alt, _hdenSenc_alt_type,
              S_alt_rel⟩ :=
            S_total Delta_alt
              (fun v hv => Delta_fv_alt v (fv_S_sub hv))
              Delta0_alt (related_alt.mono_fv fv_S_sub) wf_alt
              Delta0_alt_none_S (respects_alt.mono_fv fv_S_sub)
              Delta0_alt_dom X_alt hX_alt den_S_alt
          have DeltaS_alt_none_T : ∀ v ∉ StT.env.usedVars,
              DeltaS_alt v = none := by
            intro v hv
            apply DeltaS_alt_none v
            intro hvS
            exact hv (used_sub_T hvS)
          have related_alt_T : RValuationCastSupportedOnFV
              Delta_alt DeltaS_alt T :=
            (related_alt.mono_fv fv_T_sub).of_extends DeltaS_alt_ext
          have respects_alt_T : B.RenamingContext.RespectsTypeContextOnFV
              DeltaS_alt StS.types T :=
            respects_alt.of_extends DeltaS_alt_ext types_sub_S
              fv_T_sub fv_in_Lambda
          obtain ⟨DeltaT_alt, hcov_Tenc_alt, denTenc_alt,
              DeltaT_alt_ext, _related_T_alt, DeltaT_alt_none,
              _respects_T_alt, target_respects_Tenc_alt,
              DeltaT_alt_dom, hden_Tenc_alt, _hdenTenc_alt_type,
              T_alt_rel⟩ :=
            T_total Delta_alt
              (fun v hv => Delta_fv_alt v (fv_T_sub hv))
              DeltaS_alt related_alt_T wf_alt DeltaS_alt_none_T
              respects_alt_T DeltaS_alt_dom Y_alt hY_alt den_T_alt
          have hcov_Senc_alt_final : RenamingContext.CoversFV
              DeltaT_alt Senc :=
            RenamingContext.coversFV_of_extends_of_coversFV
              DeltaT_alt_ext hcov_Senc_alt
          have hden_Senc_alt_final :
              ⟦Senc.abstract DeltaT_alt hcov_Senc_alt_final⟧ˢ =
                some denSenc_alt := by
            have hagree := RenamingContext.agreesOnFV_of_extends_of_coversFV
              DeltaT_alt_ext hcov_Senc_alt
            have hcongr := RenamingContext.denote_congr_of_agreesOnFV
              (t := Senc) (h1 := hcov_Senc_alt_final)
              (h2 := hcov_Senc_alt) hagree
            simpa [RenamingContext.denote] using
              hcongr.trans hden_Senc_alt
          have target_respects_Senc_alt_final :
              SMT.RenamingContext.RespectsTypeContextOnFV
                DeltaT_alt StT.types Senc :=
            target_respects_Senc_alt.of_extends
              DeltaT_alt_ext types_sub_T typ_Senc
          obtain ⟨DeltaProd_alt, hcov_ProdEnc_alt, denProd_alt,
              DeltaProd_alt_ext, DeltaProd_alt_none,
              target_respects_ProdEnc_alt, DeltaProd_alt_dom,
              hden_ProdEnc_alt, hdenProd_alt_type, Prod_alt_rel⟩ :=
            semantic_prod DeltaT_alt hcov_Senc_alt_final hcov_Tenc_alt
              DeltaT_alt_none target_respects_Senc_alt_final
              target_respects_Tenc_alt DeltaT_alt_dom
              X_alt Y_alt hX_alt hY_alt denSenc_alt denTenc_alt
              hden_Senc_alt_final hden_Tenc_alt S_alt_rel T_alt_rel
          have DeltaT_alt_ext0 :=
            RenamingContext.extends_trans DeltaT_alt_ext DeltaS_alt_ext
          have DeltaProd_alt_ext0 :=
            RenamingContext.extends_trans DeltaProd_alt_ext DeltaT_alt_ext0
          refine ⟨DeltaProd_alt, hcov_ProdEnc_alt, denProd_alt,
            DeltaProd_alt_ext0,
            related_alt.of_extends DeltaProd_alt_ext0,
            DeltaProd_alt_none, ?_, target_respects_ProdEnc_alt,
            DeltaProd_alt_dom, hden_ProdEnc_alt,
            hdenProd_alt_type, ?_⟩
          · exact respects_alt.of_extends DeltaProd_alt_ext0 types_sub0
              (fun _ h => h) fv_in_Lambda
          · simpa only [proof_irrel_heq] using Prod_alt_rel

set_option maxHeartbeats 12000000 in
theorem encodeTerm_rep_scoped.cprod_case_from.{u}
    (S T : B.Term)
    (S_ih : EncodeTermRepIH.{u} S)
    (T_ih : EncodeTermRepIH.{u} T)
    (S_scoped : EncodeTermRepScopedFromIH.{u} S)
    (T_scoped : EncodeTermRepScopedFromIH.{u} T)
    (E : B.Env) {Lambda : SMT.TypeContext} {tau : BType}
    (typ_t : E.context ⊢ᴮ B.Term.cprod S T : tau)
    {Delta : B.RenamingContext.Context}
    (Delta_fv : ∀ v ∈ B.fv (B.Term.cprod S T),
      (Delta v).isSome = true)
    {Delta0 : SMT.RenamingContext.Context.{u}}
    (related : RValuationCastSupportedOnFV Delta Delta0
      (B.Term.cprod S T))
    {used : List SMT.𝒱}
    (Delta0_none : ∀ v ∉ used, Delta0 v = none)
    (Delta0_dom : ∀ v, Delta0 v ≠ none → v ∈ Lambda)
    {U : ZFSet.{u}} {hU : U ∈ ⟦tau⟧ᶻ}
    (den_t : ⟦(B.Term.cprod S T).abstract Delta Delta_fv⟧ᴮ =
      some ⟨U, tau, hU⟩)
    (vars_used : ∀ v ∈ (B.Term.cprod S T).vars, v ∈ used)
    (Lambda_inv : ∀ v ∈ (B.Term.cprod S T).vars,
      v ∈ Lambda → v ∈ E.context)
    (bv_nodup : (B.bv (B.Term.cprod S T)).Nodup)
    (respects : B.RenamingContext.RespectsTypeContextOnFV
      Delta0 Lambda (B.Term.cprod S T))
    (fv_in_Lambda : ∀ v ∈ B.fv (B.Term.cprod S T), v ∈ Lambda)
    (wf : B.RenWF E.context Delta)
    {Base : SMT.TypeContext} {Dpre : SMT.Chunk}
    (input_envelope : DeclarationContextEnvelope Base Dpre Lambda)
    (fv_in_Base : ∀ v ∈ B.fv (B.Term.cprod S T), v ∈ Base)
    (Dpre_typing : ScopedSpecsTyping Base Dpre)
    {n : ℕ} {decl : SMT.Chunk} :
    ⦃fun ⟨E0, Lambda'⟩ =>
      ⌜Lambda' = Lambda ∧ E0.freshvarsc = n ∧
        Lambda.keys ⊆ E0.usedVars ∧ E0.usedVars = used ∧
        E0.declarations = decl⌝⦄
    encodeTerm (B.Term.cprod S T) E
    ⦃⇓? (⟨t', sigma⟩ : SMT.Term × SMTType) ⟨E', Gamma'⟩ =>
      ⌜EncodeTermRepScopedPostFrom.{u} (B.Term.cprod S T) E tau
        Base Dpre Lambda decl t' sigma E' Gamma'⌝⦄ := by
  mstart
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_keys, St_used_eq, St_decl_eq⟩ := pre
  rw [encodeTerm_cprod_via_tail]
  obtain ⟨alpha, beta, rfl, typ_S, typ_T⟩ := B.Typing.cprodE typ_t
  obtain ⟨X, Y, hX, hY, den_S, den_T, rfl⟩ :=
    B.denote_cprod_inv_rep Delta_fv den_t
  have fv_S_sub : B.fv S ⊆ B.fv (B.Term.cprod S T) := by
    intro v hv
    simpa [B.fv] using (Or.inl hv : v ∈ B.fv S ∨ v ∈ B.fv T)
  have fv_T_sub : B.fv T ⊆ B.fv (B.Term.cprod S T) := by
    intro v hv
    simpa [B.fv] using (Or.inr hv : v ∈ B.fv S ∨ v ∈ B.fv T)
  have S_bv_nodup : (B.bv S).Nodup := by
    have h := bv_nodup
    simp only [B.bv, List.nodup_append] at h
    exact h.1
  have T_bv_nodup : (B.bv T).Nodup := by
    have h := bv_nodup
    simp only [B.bv, List.nodup_append] at h
    exact h.2.1
  have ST_bv_disj : ∀ a ∈ B.bv S, ∀ b ∈ B.bv T, a ≠ b := by
    have h := bv_nodup
    simp only [B.bv, List.nodup_append] at h
    exact h.2.2

  mspec (Std.Do.Triple.and _
    (Std.Do.Triple.and _
      (Std.Do.Triple.and _
        (S_ih E typ_S
          (fun v hv => Delta_fv v (fv_S_sub hv))
          (related.mono_fv fv_S_sub)
          Delta0_none Delta0_dom den_S
          (fun v hv => vars_used v (by
            simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
              List.mem_append] at hv ⊢
            rcases hv with h | h <;> [left; right] <;> exact .inl h))
          (fun v hv => Lambda_inv v (by
            simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
              List.mem_append] at hv ⊢
            rcases hv with h | h <;> [left; right] <;> exact .inl h))
          S_bv_nodup (respects.mono_fv fv_S_sub)
          (fun v hv => fv_in_Lambda v (fv_S_sub hv)) wf
          (n := St.env.freshvarsc))
        (S_scoped E typ_S
          (fun v hv => Delta_fv v (fv_S_sub hv))
          (related.mono_fv fv_S_sub)
          Delta0_none Delta0_dom den_S
          (fun v hv => vars_used v (by
            simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
              List.mem_append] at hv ⊢
            rcases hv with h | h <;> [left; right] <;> exact .inl h))
          (fun v hv => Lambda_inv v (by
            simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
              List.mem_append] at hv ⊢
            rcases hv with h | h <;> [left; right] <;> exact .inl h))
          S_bv_nodup (respects.mono_fv fv_S_sub)
          (fun v hv => fv_in_Lambda v (fv_S_sub hv)) wf
          input_envelope (fun v hv => fv_in_Base v (fv_S_sub hv))
          Dpre_typing (n := St.env.freshvarsc)
          (decl := St.env.declarations)))
      (encodeTerm_bv_used E (t := S) (used := St.env.usedVars)
        (n := St.env.freshvarsc) (decl := St.env.declarations)))
    (encodeTerm_bv_notMem_used E (t := S) (used := St.env.usedVars)
      (n := St.env.freshvarsc) (decl := St.env.declarations)))
  clear S_ih S_scoped
  rename_i out_S
  obtain ⟨Senc, sigmaS⟩ := out_S
  mrename_i post_S
  mintro ∀StS
  mpure post_S
  dsimp at post_S
  obtain ⟨⟨⟨S_post, S_scoped_post⟩,
      bv_Senc_used, _S_used_sub_struct, DltS_struct,
      S_decl_struct, S_delta_ok⟩,
    bv_Senc_not_used, _S_used_sub_struct', _DltS_struct',
      _S_decl_struct', S_delta_not_used⟩ := post_S
  obtain ⟨DltS, S_decl_eq, S_op_envelope, S_envelope, S_sc_total,
    S_guard, S_specs_op, S_sc_typing⟩ := S_scoped_post
  have DltS_eq : DltS = DltS_struct := by
    rw [S_decl_eq, St_decl_eq] at S_decl_struct
    exact (List.append_right_inj decl).mp S_decl_struct
  subst DltS_struct
  have DltS_eq' : DltS = _DltS_struct' := by
    rw [S_decl_eq] at _S_decl_struct'
    exact (List.append_right_inj St.env.declarations).mp
      _S_decl_struct'
  subst _DltS_struct'
  obtain ⟨used_sub_S, types_sub_S, keys_sub_S, covers_S,
    _path_S, typ_Senc, _shape_S, preserves_S,
    DeltaS, hcov_Senc, DeltaS_ext, _related_S, DeltaS_none,
    _respects_S, target_respects_Senc, DeltaS_dom,
    denSenc, hden_Senc, hdenSenc_type, S_rel, S_total⟩ := S_post
  rcases denSenc with ⟨Sval, sigmaSden, hSval⟩
  dsimp at hdenSenc_type
  subst sigmaSden
  cases S_rel.supported with
  | optionFun gamma delta =>
      exact wp_bind_throw _ _ _ _
  | @setPred _ rho hrho =>
    have related_T : RValuationCastSupportedOnFV Delta DeltaS T :=
      (related.mono_fv fv_T_sub).of_extends DeltaS_ext
    have respects_T : B.RenamingContext.RespectsTypeContextOnFV
        DeltaS StS.types T :=
      respects.of_extends DeltaS_ext types_sub_S fv_T_sub fv_in_Lambda
    have vars_used_T_input : ∀ v ∈ T.vars, v ∈ used := by
      intro v hv
      apply vars_used v
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
        List.mem_append]
      rcases B.Term.mem_vars_iff.mp hv with h | h
      · exact .inl (.inr h)
      · exact .inr (.inr h)
    have vars_used_T : ∀ v ∈ T.vars, v ∈ StS.env.usedVars :=
      fun v hv => used_sub_S (vars_used_T_input v hv)
    have Lambda_inv_T : ∀ v ∈ T.vars,
        v ∈ StS.types → v ∈ E.context := by
      intro v hv hGamma
      have hv_cprod : v ∈ (B.Term.cprod S T).vars := by
        simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
          List.mem_append]
        rcases B.Term.mem_vars_iff.mp hv with h | h
        · exact .inl (.inr h)
        · exact .inr (.inr h)
      by_cases hv_Lambda : v ∈ St.types
      · exact Lambda_inv v hv_cprod hv_Lambda
      · have hv_vars_S : v ∈ B.Term.vars S := by
          by_contra hnot
          exact absurd hGamma
            (preserves_S v (vars_used v hv_cprod) hv_Lambda hnot)
        rcases B.Term.mem_vars_iff.mp hv_vars_S with hSfv | hSbv
        · exact B.Typing.typed_by_fv typ_S hSfv
        · rcases B.Term.mem_vars_iff.mp hv with hTfv | hTbv
          · exact absurd (B.Typing.typed_by_fv typ_T hTfv)
              (B.Typing.bv_notMem_context typ_S v hSbv)
          · exact absurd rfl (ST_bv_disj v hSbv v hTbv)

    mspec (Std.Do.Triple.and _
      (Std.Do.Triple.and _
        (Std.Do.Triple.and _
          (T_ih E typ_T
            (fun v hv => Delta_fv v (fv_T_sub hv)) related_T
            DeltaS_none DeltaS_dom den_T vars_used_T Lambda_inv_T
            T_bv_nodup respects_T
            (fun v hv => AList.mem_of_subset types_sub_S
              (fv_in_Lambda v (fv_T_sub hv))) wf
            (n := StS.env.freshvarsc))
          (T_scoped E typ_T
            (fun v hv => Delta_fv v (fv_T_sub hv)) related_T
            DeltaS_none DeltaS_dom den_T vars_used_T Lambda_inv_T
            T_bv_nodup respects_T
            (fun v hv => AList.mem_of_subset types_sub_S
              (fv_in_Lambda v (fv_T_sub hv))) wf
            S_envelope (fun v hv => fv_in_Base v (fv_T_sub hv))
            S_sc_typing.2
            (n := StS.env.freshvarsc)
            (decl := StS.env.declarations)))
        (encodeTerm_bv_used E (t := T) (used := StS.env.usedVars)
          (n := StS.env.freshvarsc) (decl := StS.env.declarations)))
      (encodeTerm_bv_notMem_used E (t := T)
        (used := StS.env.usedVars) (n := StS.env.freshvarsc)
        (decl := StS.env.declarations)))
    clear T_ih T_scoped
    rename_i out_T
    obtain ⟨Tenc, sigmaT⟩ := out_T
    mrename_i post_T
    mintro ∀StT
    mpure post_T
    dsimp at post_T
    obtain ⟨⟨⟨T_post, T_scoped_post⟩,
        bv_Tenc_used, _T_used_sub_struct, DltT_struct,
        T_decl_struct, T_delta_ok⟩,
      bv_Tenc_not_used, _T_used_sub_struct', _DltT_struct',
        _T_decl_struct', T_delta_not_used⟩ := post_T
    obtain ⟨DltT, T_decl_eq, T_op_envelope, T_envelope, T_sc_total,
      T_guard, T_specs_op, T_sc_typing⟩ := T_scoped_post
    have DltT_eq : DltT = DltT_struct := by
      rw [T_decl_eq] at T_decl_struct
      exact (List.append_right_inj StS.env.declarations).mp T_decl_struct
    subst DltT_struct
    have DltT_eq' : DltT = _DltT_struct' := by
      rw [T_decl_eq] at _T_decl_struct'
      exact (List.append_right_inj StS.env.declarations).mp
        _T_decl_struct'
    subst _DltT_struct'
    obtain ⟨used_sub_T, types_sub_T, keys_sub_T, covers_T,
      _path_T, typ_Tenc, _shape_T, preserves_T,
      DeltaT, hcov_Tenc, DeltaT_ext, _related_T, DeltaT_none,
      _respects_T, target_respects_Tenc, DeltaT_dom,
      denTenc, hden_Tenc, hdenTenc_type, T_rel, T_total⟩ := T_post
    rcases denTenc with ⟨Tval, sigmaTden, hTval⟩
    dsimp at hdenTenc_type
    subst sigmaTden
    cases T_rel.supported with
    | optionFun gamma delta =>
        exact wp_bind_throw _ _ _ _
    | @setPred _ sigma hsigma =>
      have bv_Senc_final : ∀ v ∈ SMT.bv Senc,
          v ∈ StT.env.usedVars :=
        fun v hv => used_sub_T (bv_Senc_used v hv)
      have bv_Senc_not_final : ∀ v ∈ SMT.bv Senc,
          v ∉ StT.types :=
        fun v hv => preserves_T v (bv_Senc_used v hv)
          (SMT.Typing.bv_notMem_context typ_Senc v hv)
          (by
            rw [B.Term.notMem_vars_iff]
            refine ⟨?_, ?_⟩
            · intro hfvT
              exact SMT.Typing.bv_notMem_context typ_Senc v hv
                (AList.mem_of_subset types_sub_S
                  (fv_in_Lambda v (fv_T_sub hfvT)))
            · intro hbT
              exact bv_Senc_not_used v hv
                (St_used_eq ▸ vars_used v (by
                  simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
                    List.mem_append]
                  right
                  right
                  exact hbT)))
      have typ_Senc_final : StT.types ⊢ˢ Senc :
          SMTType.fun rho SMTType.bool :=
        SMT.Typing.weakening types_sub_T typ_Senc bv_Senc_not_final
      have hcov_Senc_final : RenamingContext.CoversFV DeltaT Senc :=
        RenamingContext.coversFV_of_extends_of_coversFV
          DeltaT_ext hcov_Senc
      have hden_Senc_final :
          ⟦Senc.abstract DeltaT hcov_Senc_final⟧ˢ =
            some (⟨Sval, SMTType.fun rho SMTType.bool, hSval⟩ :
              SMT.Dom) := by
        have hagree := RenamingContext.agreesOnFV_of_extends_of_coversFV
          DeltaT_ext hcov_Senc
        have hcongr := RenamingContext.denote_congr_of_agreesOnFV
          (t := Senc) (h1 := hcov_Senc_final)
          (h2 := hcov_Senc) hagree
        simpa [RenamingContext.denote] using hcongr.trans hden_Senc
      have target_respects_Senc_final :
          SMT.RenamingContext.RespectsTypeContextOnFV
            DeltaT StT.types Senc :=
        target_respects_Senc.of_extends
          DeltaT_ext types_sub_T typ_Senc
      mspec encodeCprodTail_rep_scoped_spec
        alpha beta rho sigma hrho hsigma Senc Tenc
        typ_Senc_final typ_Tenc bv_Senc_final bv_Tenc_used
      rename_i out_cprod
      obtain ⟨CprodEnc, sigmaCprod⟩ := out_cprod
      mrename_i post_cprod
      mintro ∀StCprod
      mpure post_cprod
      obtain ⟨used_sub_Cprod, types_sub_Cprod, keys_sub_Cprod, path_Cprod,
        typ_CprodEnc, preserves_Cprod, tail_total,
        tail_types_eq, tail_decl_eq, tail_obs_S, tail_obs_T,
        tail_fv_dep, tail_guard⟩ := post_cprod
      dsimp at path_Cprod typ_CprodEnc tail_total tail_obs_S tail_obs_T tail_fv_dep tail_guard
      mpure_intro
      refine ⟨DltS ++ DltT, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [tail_decl_eq, T_decl_eq, S_decl_eq, St_decl_eq,
          List.append_assoc]
      · simpa [tail_types_eq] using
          DeclarationContextEnvelope.append S_op_envelope T_op_envelope
      · simpa [tail_types_eq, List.append_assoc] using T_envelope
      · intro Delta_alt Delta_fv_alt Delta0_alt related_alt wf_alt
          Delta0_alt_none respects_alt Delta0_alt_dom
          U_alt hU_alt den_t_alt
        obtain ⟨X_alt, Y_alt, hX_alt, hY_alt,
            den_S_alt, den_T_alt, rfl⟩ :=
          B.denote_cprod_inv_rep Delta_fv_alt den_t_alt
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
        have DeltaS_alt_none_T : ∀ v ∉ StT.env.usedVars,
            DeltaS_alt v = none := by
          intro v hv
          apply DeltaS_alt_none v
          intro hvS
          exact hv (used_sub_T hvS)
        have related_alt_T : RValuationCastSupportedOnFV
            Delta_alt DeltaS_alt T :=
          (related_alt.mono_fv fv_T_sub).of_extends DeltaS_alt_ext
        have respects_alt_T : B.RenamingContext.RespectsTypeContextOnFV
            DeltaS_alt StS.types T :=
          respects_alt.of_extends DeltaS_alt_ext types_sub_S
            fv_T_sub fv_in_Lambda
        obtain ⟨DeltaT_alt, hcov_Tenc_alt, denTenc_alt,
            DeltaT_alt_ext, _related_T_alt, DeltaT_alt_none,
            _respects_T_alt, target_respects_Tenc_alt,
            DeltaT_alt_dom, specsT_alt, hden_Tenc_alt,
            hdenTenc_alt_type, T_alt_rel⟩ :=
          T_sc_total Delta_alt
            (fun v hv => Delta_fv_alt v (fv_T_sub hv))
            DeltaS_alt related_alt_T wf_alt DeltaS_alt_none_T
            respects_alt_T DeltaS_alt_dom Y_alt hY_alt den_T_alt
        have hcov_Senc_alt_final : RenamingContext.CoversFV
            DeltaT_alt Senc :=
          RenamingContext.coversFV_of_extends_of_coversFV
            DeltaT_alt_ext hcov_Senc_alt
        have hden_Senc_alt_final :
            ⟦Senc.abstract DeltaT_alt hcov_Senc_alt_final⟧ˢ =
              some denSenc_alt := by
          have hagree :=
            RenamingContext.agreesOnFV_of_extends_of_coversFV
              DeltaT_alt_ext hcov_Senc_alt
          have hcongr := RenamingContext.denote_congr_of_agreesOnFV
            (t := Senc) (h1 := hcov_Senc_alt_final)
            (h2 := hcov_Senc_alt) hagree
          simpa [RenamingContext.denote] using
            hcongr.trans hden_Senc_alt
        have target_respects_Senc_alt_final :
            SMT.RenamingContext.RespectsTypeContextOnFV
              DeltaT_alt StT.types Senc :=
          target_respects_Senc_alt.of_extends
            DeltaT_alt_ext types_sub_T typ_Senc
        obtain ⟨DeltaCprod_alt, hcov_CprodEnc_alt, denCprod_alt,
            DeltaCprod_alt_ext, DeltaCprod_alt_none,
            target_respects_CprodEnc_alt, DeltaCprod_alt_dom,
            hden_CprodEnc_alt, hdenCprod_alt_type, Cprod_alt_rel⟩ :=
          tail_total DeltaT_alt hcov_Senc_alt_final hcov_Tenc_alt
            DeltaT_alt_none target_respects_Senc_alt_final
            target_respects_Tenc_alt DeltaT_alt_dom
            X_alt Y_alt hX_alt hY_alt denSenc_alt denTenc_alt
            hden_Senc_alt_final hden_Tenc_alt S_alt_rel T_alt_rel
        have DeltaT_alt_ext0 :=
          RenamingContext.extends_trans DeltaT_alt_ext DeltaS_alt_ext
        have DeltaCprod_alt_ext0 :=
          RenamingContext.extends_trans DeltaCprod_alt_ext DeltaT_alt_ext0
        have types_sub0 : St.types ⊆ StCprod.types :=
          fun _ h => types_sub_Cprod (types_sub_T (types_sub_S h))
        have DeltaCprod_alt_extS :=
          RenamingContext.extends_trans DeltaCprod_alt_ext DeltaT_alt_ext
        have specsS_final : SpecBodiesTrue
            DeltaCprod_alt StCprod.types DltS :=
          specsS_alt.of_extends DeltaCprod_alt_extS
            (fun _ h => types_sub_Cprod (types_sub_T h)) DeltaS_alt_dom
        have specsT_final : SpecBodiesTrue
            DeltaCprod_alt StCprod.types DltT :=
          specsT_alt.of_extends DeltaCprod_alt_ext
            types_sub_Cprod DeltaT_alt_dom
        refine ⟨DeltaCprod_alt, hcov_CprodEnc_alt, denCprod_alt,
          DeltaCprod_alt_ext0,
          related_alt.of_extends DeltaCprod_alt_ext0,
          DeltaCprod_alt_none, ?_, target_respects_CprodEnc_alt,
          DeltaCprod_alt_dom, specsS_final.append specsT_final,
          hden_CprodEnc_alt, hdenCprod_alt_type, ?_⟩
        · exact respects_alt.of_extends DeltaCprod_alt_ext0 types_sub0
            (fun _ h => h) fv_in_Lambda
        · simpa only [proof_irrel_heq] using Cprod_alt_rel
      · intro GammaSup GammaScope Delta_alt Delta_fv_alt Theta
          related_alt wf_alt respectsB respectsSMT specsTrue
          U_alt hU_alt den_alt hcovOut denOut hdenOut hdenOut_type
        have full_scope : ScopedContextExtends Base
            ((Dpre ++ DltS) ++ DltT) GammaSup := by
          simpa [List.append_assoc] using GammaScope
        have full_specs : SpecBodiesTrue Theta GammaSup
            ((Dpre ++ DltS) ++ DltT) := by
          simpa [List.append_assoc] using specsTrue
        have S_scope : ScopedContextExtends Base
            (Dpre ++ DltS) GammaSup := full_scope.left_of_append
        have S_specs_true : SpecBodiesTrue Theta GammaSup
            (Dpre ++ DltS) := full_specs.left_of_append
        obtain ⟨X_target, Y_target, hX_target, hY_target,
            den_S_target, den_T_target, rfl⟩ :=
          B.denote_cprod_inv_rep Delta_fv_alt den_alt
        have hcov_S_target : RenamingContext.CoversFV Theta Senc :=
          fun v hv => hcovOut v (tail_obs_S v hv)
        have hcov_T_target : RenamingContext.CoversFV Theta Tenc :=
          fun v hv => hcovOut v (tail_obs_T v hv)
        have respects_S_target :
            SMT.RenamingContext.RespectsTypeContextOnFV
              Theta GammaSup Senc := by
          intro v xi hv hlookup
          exact respectsSMT (tail_obs_S v hv) hlookup
        have respects_T_target :
            SMT.RenamingContext.RespectsTypeContextOnFV
              Theta GammaSup Tenc := by
          intro v xi hv hlookup
          exact respectsSMT (tail_obs_T v hv) hlookup
        obtain ⟨Core, core_trace, Core_sub_StT⟩ := T_envelope
        have Core_sub_sup : Core ⊆ GammaSup := by
          intro e he
          exact full_scope (core_trace.context_generated he)
        have S_scope_Core : ScopedContextExtends Base
            (Dpre ++ DltS) Core :=
          core_trace.scoped_extends.left_of_append
        have S_bv_fresh_Core : ∀ v ∈ SMT.bv Senc, v ∉ Core := by
          intro v hv hvCore
          exact SMT.Typing.bv_notMem_context typ_Senc_final v hv
            (AList.mem_of_subset Core_sub_StT hvCore)
        have T_bv_fresh_Core : ∀ v ∈ SMT.bv Tenc, v ∉ Core := by
          intro v hv hvCore
          exact SMT.Typing.bv_notMem_context typ_Tenc v hv
            (AList.mem_of_subset Core_sub_StT hvCore)
        have typ_S_Core : Core ⊢ˢ Senc : rho.fun SMTType.bool :=
          S_sc_typing.1 Core S_scope_Core S_bv_fresh_Core
        have typ_T_Core : Core ⊢ˢ Tenc : sigma.fun SMTType.bool :=
          T_sc_typing.1 Core core_trace.scoped_extends T_bv_fresh_Core
        have respects_S_Core :
            SMT.RenamingContext.RespectsTypeContextOnFV
              Theta Core Senc :=
          respects_S_target.of_super Core_sub_sup
        have respects_T_Core :
            SMT.RenamingContext.RespectsTypeContextOnFV
              Theta Core Tenc :=
          respects_T_target.of_super Core_sub_sup
        obtain ⟨denS_target, hdenS_target, hdenS_target_type⟩ :=
          SMT.RenamingContext.denote_exists_of_typing_fv
            typ_S_Core respects_S_Core hcov_S_target
        obtain ⟨denT_target, hdenT_target, hdenT_target_type⟩ :=
          SMT.RenamingContext.denote_exists_of_typing_fv
            typ_T_Core respects_T_Core hcov_T_target
        have S_target_rel := S_guard GammaSup S_scope Delta_alt
          (fun v hv => Delta_fv_alt v (fv_S_sub hv)) Theta
          (related_alt.mono_fv fv_S_sub) wf_alt
          (respectsB.mono_fv fv_S_sub) respects_S_target
          S_specs_true X_target hX_target den_S_target
          hcov_S_target denS_target hdenS_target hdenS_target_type
        have T_target_rel := T_guard GammaSup full_scope Delta_alt
          (fun v hv => Delta_fv_alt v (fv_T_sub hv)) Theta
          (related_alt.mono_fv fv_T_sub) wf_alt
          (respectsB.mono_fv fv_T_sub) respects_T_target
          full_specs Y_target hY_target den_T_target
          hcov_T_target denT_target hdenT_target hdenT_target_type
        have Core_keys_used : Core.keys ⊆ StT.env.usedVars := by
          intro v hv
          apply keys_sub_T
          apply (AList.mem_keys).mp
          apply AList.mem_of_subset Core_sub_StT
          exact (AList.mem_keys).mpr hv
        have result_rel := tail_guard Core Core_sub_StT Core_keys_used
          typ_S_Core typ_T_Core Theta hcov_S_target hcov_T_target
          respects_S_Core respects_T_Core
          X_target Y_target hX_target hY_target denS_target denT_target
          hdenS_target hdenT_target S_target_rel T_target_rel
          hcovOut denOut hdenOut hdenOut_type
        simpa only [proof_irrel_heq] using result_rel
      · intro body hbody
        rw [specBodies_append, List.mem_append] at hbody
        rcases hbody with hSbody | hTbody
        · have typ_at_T : StT.types ⊢ˢ body : SMTType.bool :=
            SMT.Typing.weakening types_sub_T
              (S_specs_op body hSbody) (fun v hv =>
                preserves_T v (S_delta_ok.2 body hSbody v hv)
                  (SMT.Typing.bv_notMem_context
                    (S_specs_op body hSbody) v hv)
                  (fun hvT => S_delta_not_used.2 body hSbody v hv
                    (by rw [St_used_eq]; exact vars_used_T_input v hvT)))
          simpa [tail_types_eq] using typ_at_T
        · simpa [tail_types_eq] using T_specs_op body hTbody
      · constructor
        · intro GammaSup GammaScope result_bv_fresh
          have full_scope : ScopedContextExtends Base
              ((Dpre ++ DltS) ++ DltT) GammaSup := by
            simpa [List.append_assoc] using GammaScope
          obtain ⟨Core, core_trace, Core_sub_StT⟩ := T_envelope
          have Core_sub_sup : Core ⊆ GammaSup := by
            intro e he
            exact full_scope (core_trace.context_generated he)
          have S_scope_Core : ScopedContextExtends Base
              (Dpre ++ DltS) Core :=
            core_trace.scoped_extends.left_of_append
          have S_bv_fresh_Core : ∀ v ∈ SMT.bv Senc, v ∉ Core := by
            intro v hv hvCore
            exact SMT.Typing.bv_notMem_context typ_Senc_final v hv
              (AList.mem_of_subset Core_sub_StT hvCore)
          have T_bv_fresh_Core : ∀ v ∈ SMT.bv Tenc, v ∉ Core := by
            intro v hv hvCore
            exact SMT.Typing.bv_notMem_context typ_Tenc v hv
              (AList.mem_of_subset Core_sub_StT hvCore)
          have typ_S_Core : Core ⊢ˢ Senc : rho.fun SMTType.bool :=
            S_sc_typing.1 Core S_scope_Core S_bv_fresh_Core
          have typ_T_Core : Core ⊢ˢ Tenc : sigma.fun SMTType.bool :=
            T_sc_typing.1 Core core_trace.scoped_extends T_bv_fresh_Core
          have Core_sub_StCprod : Core ⊆ StCprod.types := by
            simpa [tail_types_eq] using Core_sub_StT
          have output_fv_Core : ∀ v ∈ SMT.fv CprodEnc, v ∈ Core := by
            intro v hv
            have hv_children := tail_fv_dep hv
            rw [List.mem_append] at hv_children
            rcases hv_children with hvS | hvT
            · exact SMT.Typing.mem_context_of_mem_fv typ_S_Core hvS
            · exact SMT.Typing.mem_context_of_mem_fv typ_T_Core hvT
          have typ_Cprod_Core : Core ⊢ˢ CprodEnc : sigmaCprod :=
            SMT.Typing.strengthening_of_fv_subset
              Core_sub_StCprod typ_CprodEnc output_fv_Core
          exact SMT.Typing.weakening Core_sub_sup typ_Cprod_Core
            result_bv_fresh
        · simpa [List.append_assoc] using T_sc_typing.2
