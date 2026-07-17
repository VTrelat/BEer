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
        · simpa [StEb_types_final]
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
