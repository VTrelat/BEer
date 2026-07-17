import SMT.Reasoning.Basic.EncodeTermRepresentedSet

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

abbrev EncodeCprodTailRepSpec.{u}
    (alpha beta : BType) (A B : SMT.Term) : Prop :=
  ∀ {Lambda : SMT.TypeContext} {n : ℕ} {used : List SMT.𝒱},
    Lambda ⊢ˢ A : (BType.set alpha).toSMTType →
    Lambda ⊢ˢ B : (BType.set beta).toSMTType →
    (∀ v ∈ SMT.bv A, v ∈ used) →
    (∀ v ∈ SMT.bv B, v ∈ used) →
    ⦃fun ⟨env, Lambda'⟩ =>
      ⌜Lambda' = Lambda ∧ env.freshvarsc = n ∧
        Lambda.keys ⊆ env.usedVars ∧ env.usedVars = used⌝⦄
    encodeCprodTail A B alpha.toSMTType beta.toSMTType
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
    (alpha beta : BType) (A B : SMT.Term) :
    EncodeCprodTailRepSpec.{u} alpha beta A B := by
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
            (SMTType.pair alpha.toSMTType beta.toSMTType) := by
          simpa [St₁_types_eq] using a_fresh
        have b_fresh₀ : b ∉
            (St₀.types.insert p
              (SMTType.pair alpha.toSMTType beta.toSMTType)).insert a
                alpha.toSMTType := by
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
          .lambda [p] [SMTType.pair alpha.toSMTType beta.toSMTType]
            (.exists [a, b] [alpha.toSMTType, beta.toSMTType] body)

        have typ_A_p : St₀.types.insert p
            (SMTType.pair alpha.toSMTType beta.toSMTType) ⊢ˢ A :
              (BType.set alpha).toSMTType :=
          SMT.Typing.weakening
            (SMT.TypeContext.entries_subset_insert_of_notMem p_fresh)
            typ_A
            (SMT.Typing.bv_notMem_insert_of_fresh typ_A hp_not_bv_A)
        have typ_B_p : St₀.types.insert p
            (SMTType.pair alpha.toSMTType beta.toSMTType) ⊢ˢ B :
              (BType.set beta).toSMTType :=
          SMT.Typing.weakening
            (SMT.TypeContext.entries_subset_insert_of_notMem p_fresh)
            typ_B
            (SMT.Typing.bv_notMem_insert_of_fresh typ_B hp_not_bv_B)
        have typ_A_pab :
            ((St₀.types.insert p
              (SMTType.pair alpha.toSMTType beta.toSMTType)).insert a
                alpha.toSMTType).insert b beta.toSMTType ⊢ˢ A :
              (BType.set alpha).toSMTType := by
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
              (SMTType.pair alpha.toSMTType beta.toSMTType)).insert a
                alpha.toSMTType).insert b beta.toSMTType ⊢ˢ B :
              (BType.set beta).toSMTType := by
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
              (SMTType.pair alpha.toSMTType beta.toSMTType)).insert a
                alpha.toSMTType).insert b beta.toSMTType ⊢ˢ body :
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
            (SMTType.pair alpha.toSMTType beta.toSMTType) ⊢ˢ
              .exists [a, b] [alpha.toSMTType, beta.toSMTType] body :
                SMTType.bool := by
          let lenEq : [a, b].length =
              [alpha.toSMTType, beta.toSMTType].length := by simp
          apply SMT.Typing.exists
              (vs := [a, b])
              (τs := [alpha.toSMTType, beta.toSMTType])
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
                  (SMTType.pair alpha.toSMTType beta.toSMTType))
                [a, b] [alpha.toSMTType, beta.toSMTType] lenEq =
              ((St₀.types.insert p
                (SMTType.pair alpha.toSMTType beta.toSMTType)).insert a
                  alpha.toSMTType).insert b beta.toSMTType := by
              unfold SMT.TypeContext.update
              simp only [List.length_cons, List.length_nil, zero_add,
                Nat.reduceAdd, Fin.cast_eq_self, Fin.getElem_fin]
              rw [Fin.foldl_succ_last, Fin.foldl_succ_last]
              simp
            rw [hupdate]
            exact typ_body
        have typ_tcprod : St₀.types ⊢ˢ tcprod :
            (BType.set (alpha ×ᴮ beta)).toSMTType := by
          let lenEq : [p].length =
              [SMTType.pair alpha.toSMTType beta.toSMTType].length := by
            simp
          apply SMT.Typing.lambda (vs := [p])
              (τs := [SMTType.pair alpha.toSMTType beta.toSMTType])
              (len_eq := lenEq)
          · simpa using p_fresh
          · intro v hv hbv
            rw [List.mem_singleton] at hv
            subst v
            exact SMT.Typing.bv_notMem_context typ_exists p hbv (by simp)
          · simp
          · have hupdate : SMT.TypeContext.update St₀.types [p]
                [SMTType.pair alpha.toSMTType beta.toSMTType] lenEq =
              St₀.types.insert p
                (SMTType.pair alpha.toSMTType beta.toSMTType) := by
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
        · exact ⟨castPath.reflexive
            (BType.set (alpha ×ᴮ beta)).toSMTType⟩
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
          have retract_A : retract (BType.set alpha) Aval = X :=
            ((RDomCast.iff_RDom_of_type_eq
              (α := BType.set alpha) rfl).mp A_rel.toRDomCast).2
          have retract_B : retract (BType.set beta) Bval = Y :=
            ((RDomCast.iff_RDom_of_type_eq
              (α := BType.set beta) rfl).mp B_rel.toRDomCast).2
          let keep := SMT.fv A ++ SMT.fv B
          let ThetaFull :=
            SMT.RenamingContext.completeOutside Theta St₀.types keep
          have keep_respects : ∀ {v : SMT.𝒱} {sigma : SMTType},
              v ∈ keep → St₀.types.lookup v = some sigma →
                ∃ d : SMT.Dom.{u},
                  Theta v = some d ∧ d.snd.fst = sigma := by
            intro v sigma hv hlookup
            rw [List.mem_append] at hv
            exact hv.elim
              (fun h => respects_A h hlookup)
              (fun h => respects_B h hlookup)
          have ThetaFull_wt :=
            SMT.RenamingContext.completeOutside_wt keep_respects
          have hcov_A_full : RenamingContext.CoversFV ThetaFull A := by
            intro v hv
            change (SMT.RenamingContext.completeOutside
              Theta St₀.types keep v).isSome = true
            rw [SMT.RenamingContext.completeOutside_eq_of_mem
              (by simp [keep, hv])]
            exact hcov_A v hv
          have hcov_B_full : RenamingContext.CoversFV ThetaFull B := by
            intro v hv
            change (SMT.RenamingContext.completeOutside
              Theta St₀.types keep v).isSome = true
            rw [SMT.RenamingContext.completeOutside_eq_of_mem
              (by simp [keep, hv])]
            exact hcov_B v hv
          have hden_A_full :
              ⟦A.abstract ThetaFull hcov_A_full⟧ˢ =
                some (⟨Aval, (BType.set alpha).toSMTType, hAval⟩ :
                  SMT.Dom) := by
            have hagree : RenamingContext.AgreesOnFV ThetaFull Theta A := by
              intro v hv
              change SMT.RenamingContext.completeOutside
                Theta St₀.types keep v = Theta v
              exact SMT.RenamingContext.completeOutside_eq_of_mem
                (by simp [keep, hv])
            have hcongr := RenamingContext.denote_congr_of_agreesOnFV
              (t := A) (h1 := hcov_A_full) (h2 := hcov_A) hagree
            simpa [RenamingContext.denote] using hcongr.trans hden_A
          have hden_B_full :
              ⟦B.abstract ThetaFull hcov_B_full⟧ˢ =
                some (⟨Bval, (BType.set beta).toSMTType, hBval⟩ :
                  SMT.Dom) := by
            have hagree : RenamingContext.AgreesOnFV ThetaFull Theta B := by
              intro v hv
              change SMT.RenamingContext.completeOutside
                Theta St₀.types keep v = Theta v
              exact SMT.RenamingContext.completeOutside_eq_of_mem
                (by simp [keep, hv])
            have hcongr := RenamingContext.denote_congr_of_agreesOnFV
              (t := B) (h1 := hcov_B_full) (h2 := hcov_B) hagree
            simpa [RenamingContext.denote] using hcongr.trans hden_B
          have hcov_tcprod : RenamingContext.CoversFV Theta tcprod := by
            intro v hv
            have hv' := fv_tcprod_sub hv
            rw [List.mem_append] at hv'
            exact hv'.elim (hcov_A v) (hcov_B v)
          have hcov_tcprod_full :
              RenamingContext.CoversFV ThetaFull tcprod := by
            intro v hv
            have hvkeep : v ∈ keep := fv_tcprod_sub hv
            change (SMT.RenamingContext.completeOutside
              Theta St₀.types keep v).isSome = true
            rw [SMT.RenamingContext.completeOutside_eq_of_mem hvkeep]
            exact hcov_tcprod v hv
          obtain ⟨denOut, hdenOut_full, Out_rel⟩ :=
            cprod_case_denotation_aux
              (αx := alpha) (βx := beta)
              (X := X) (Y := Y) (hT := cprod_mem_btype hX hY)
              (ctx := St₀.types) (S_enc := A) (T_enc := B)
              (Δ'' := ThetaFull)
              (typ_T_enc := typ_B) (typ_S_enc_T := typ_A)
              (Δctx_wt := ThetaFull_wt)
              (p := p) (a := a) (b := b)
              (p_fresh := p_fresh) (a_fresh := a_fresh₀)
              (b_fresh := b_fresh₀)
              (hp_not_bv_S := hp_not_bv_A)
              (hp_not_bv_T := hp_not_bv_B)
              (ha_not_bv_S := ha_not_bv_A)
              (ha_not_bv_T := ha_not_bv_B)
              (hb_not_bv_S := hb_not_bv_A)
              (hb_not_bv_T := hb_not_bv_B)
              (hSenc := hAval) (hTenc := hBval)
              (retract_Senc_eq_X := retract_A)
              (retract_Tenc_eq_Y := retract_B)
              (hΔ_S_final := hcov_A_full)
              (Δ''_covers_T := hcov_B_full)
              (den_S_enc_final := hden_A_full)
              (den_T_enc := hden_B_full)
              (hcov_tcprod_in := hcov_tcprod_full)
          have hdenOut : ⟦tcprod.abstract Theta hcov_tcprod⟧ˢ =
              some denOut := by
            have hagree : RenamingContext.AgreesOnFV Theta ThetaFull tcprod := by
              intro v hv
              symm
              exact SMT.RenamingContext.completeOutside_eq_of_mem
                (fv_tcprod_sub hv)
            have hcongr := RenamingContext.denote_congr_of_agreesOnFV
              (t := tcprod) (h1 := hcov_tcprod)
              (h2 := hcov_tcprod_full) hagree
            simpa [RenamingContext.denote] using
              hcongr.trans hdenOut_full
          have target_respects :
              SMT.RenamingContext.RespectsTypeContextOnFV
                Theta St₀.types tcprod := by
            intro v sigma hv hlookup
            have hv' := fv_tcprod_sub hv
            rw [List.mem_append] at hv'
            exact hv'.elim
              (fun h => respects_A h hlookup)
              (fun h => respects_B h hlookup)
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
          · exact Out_rel.1
          · exact (RDom.toRDomCastSupported Out_rel).1
          · exact (RDom.toRDomCastSupported Out_rel).2

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
  | setPred =>
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
    | setPred =>
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
          (BType.set alpha).toSMTType :=
        SMT.Typing.weakening types_sub_T typ_Senc bv_Senc_not_final
      have hcov_Senc_final : RenamingContext.CoversFV DeltaT Senc :=
        RenamingContext.coversFV_of_extends_of_coversFV
          DeltaT_ext hcov_Senc
      have hden_Senc_final :
          ⟦Senc.abstract DeltaT hcov_Senc_final⟧ˢ =
            some (⟨Sval, (BType.set alpha).toSMTType, hSval⟩ :
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

      mspec encodeCprodTail_rep_spec alpha beta Senc Tenc
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
          (⟨Sval, (BType.set alpha).toSMTType, hSval⟩ : SMT.Dom)
          (⟨Tval, (BType.set beta).toSMTType, hTval⟩ : SMT.Dom)
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
