import SMT.Reasoning.Basic.EncodeTermRepresentedCprod
import SMT.Reasoning.Basic.EncodeTermCorrectPFun

open Std.Do B SMT ZFSet Classical

/-! # Representation-aware partial-function spaces -/

def pfunSet (X Y : ZFSet) : ZFSet :=
  (X.prod Y).powerset.sep (fun f => f.IsPFunc X Y)

theorem pfunSet_mem_btype.{u} {alpha beta : BType} {X Y : ZFSet.{u}}
    (hX : X ∈ ⟦BType.set alpha⟧ᶻ)
    (hY : Y ∈ ⟦BType.set beta⟧ᶻ) :
    pfunSet X Y ∈ ⟦BType.set (BType.set (alpha ×ᴮ beta))⟧ᶻ := by
  exact ZFSet.prod_sep_is_pfunc_mem
    (ZFSet.mem_powerset.mp hX) (ZFSet.mem_powerset.mp hY)

theorem B.denote_pfun_inv_rep.{u}
    {S T : B.Term} {alpha beta : BType}
    {Xi : B.RenamingContext.Context}
    (Xi_fv : ∀ v ∈ B.fv (B.Term.pfun S T),
      (Xi v).isSome = true)
    {U : ZFSet.{u}}
    {hU : U ∈ ⟦BType.set (BType.set (alpha ×ᴮ beta))⟧ᶻ}
    (hden : ⟦(B.Term.pfun S T).abstract Xi Xi_fv⟧ᴮ =
      some ⟨U, BType.set (BType.set (alpha ×ᴮ beta)), hU⟩) :
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
      U = pfunSet X Y := by
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

private theorem erase_insert_ne_rep_pfun
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

private theorem erase_insert_self_rep_pfun
    {a : SMT.𝒱} {tau : SMTType} {ctx : SMT.TypeContext}
    (ha : a ∉ ctx) : (ctx.insert a tau).erase a = ctx := by
  apply AList.ext
  show List.kerase a (AList.insert a tau ctx).entries = ctx.entries
  rw [AList.entries_insert_of_notMem ha]
  exact List.kerase_cons_eq rfl

private theorem erase_four_rep_pfun
    {R x y z : SMT.𝒱} {tauR taux tauy tauz : SMTType}
    {ctx : SMT.TypeContext}
    (hR : R ∉ ctx) (hx : x ∉ ctx.insert R tauR)
    (hy : y ∉ (ctx.insert R tauR).insert x taux)
    (hz : z ∉ ((ctx.insert R tauR).insert x taux).insert y tauy) :
    let ctx4 := (((ctx.insert R tauR).insert x taux).insert y tauy).insert z tauz
    AList.erase z (AList.erase y (AList.erase x (AList.erase R ctx4))) =
      ctx := by
  dsimp
  have hRx : R ≠ x := by
    intro h; subst x; exact hx (by simp)
  have hRy : R ≠ y := by
    intro h; subst y; exact hy (by simp)
  have hRz : R ≠ z := by
    intro h; subst z; exact hz (by simp)
  have hxy : x ≠ y := by
    intro h; subst y; exact hy (by simp)
  have hxz : x ≠ z := by
    intro h; subst z; exact hz (by simp)
  have hyz : y ≠ z := by
    intro h; subst z; exact hz (by simp)
  have hx0 : x ∉ ctx := by
    intro h; exact hx (by simp [h])
  have hy0 : y ∉ ctx := by
    intro h; exact hy (by simp [h])
  have hz0 : z ∉ ctx := by
    intro h; exact hz (by simp [h])
  rw [erase_insert_ne_rep_pfun hRz,
    erase_insert_ne_rep_pfun hRy,
    erase_insert_ne_rep_pfun hRx,
    erase_insert_self_rep_pfun hR,
    erase_insert_ne_rep_pfun hxz,
    erase_insert_ne_rep_pfun hxy,
    erase_insert_self_rep_pfun hx0,
    erase_insert_ne_rep_pfun hyz,
    erase_insert_self_rep_pfun hy0,
    erase_insert_self_rep_pfun hz0]

private def encodePFunTail (A B : SMT.Term)
    (alpha beta : SMTType) : Encoder (SMT.Term × SMTType) := do
  let R ← freshVar (.fun (.pair alpha beta) .bool)
  let x ← freshVar alpha
  let y ← freshVar beta
  let y' ← freshVar beta
  SMT.eraseFromContext R
  SMT.eraseFromContext x
  SMT.eraseFromContext y
  SMT.eraseFromContext y'
  return (.lambda [R] [.fun (.pair alpha beta) .bool] (.and
      (.forall [x, y] [alpha, beta]
        (.imp (.app (.var R) (.pair (.var x) (.var y)))
          (.and (.app A (.var x)) (.app B (.var y)))))
      (.forall [x, y, y'] [alpha, beta, beta] (.imp
        (.and (.app (.var R) (.pair (.var x) (.var y)))
              (.app (.var R) (.pair (.var x) (.var y'))))
        (.eq (.var y) (.var y'))))),
    .fun (.fun (.pair alpha beta) .bool) .bool)

private theorem encodeTerm_pfun_via_tail
    (S T : B.Term) (E : B.Env) :
    encodeTerm (B.Term.pfun S T) E = (do
      let ⟨Aenc, .fun alpha .bool⟩ ← encodeTerm S E |
        throw "encodeTerm:pfun: Expected a set for domain"
      let ⟨Benc, .fun beta .bool⟩ ← encodeTerm T E |
        throw "encodeTerm:pfun: Expected a set for codomain"
      encodePFunTail Aenc Benc alpha beta) := by
  rfl

private theorem pfun_lambda_typing
    {alpha beta : SMTType} {A B : SMT.Term}
    {R x y y' : SMT.𝒱} {Gamma : SMT.TypeContext}
    (typ_A : Gamma ⊢ˢ A : .fun alpha .bool)
    (typ_B : Gamma ⊢ˢ B : .fun beta .bool)
    (R_fresh : R ∉ Gamma) (x_fresh : x ∉ Gamma)
    (y_fresh : y ∉ Gamma) (y'_fresh : y' ∉ Gamma)
    (R_not_bv_A : R ∉ SMT.bv A) (R_not_bv_B : R ∉ SMT.bv B)
    (x_not_bv_A : x ∉ SMT.bv A) (x_not_bv_B : x ∉ SMT.bv B)
    (y_not_bv_A : y ∉ SMT.bv A) (y_not_bv_B : y ∉ SMT.bv B)
    (hR_ne_x : R ≠ x) (hR_ne_y : R ≠ y) (hR_ne_y' : R ≠ y')
    (hx_ne_y : x ≠ y) (hx_ne_y' : x ≠ y') (hy_ne_y' : y ≠ y') :
    Gamma ⊢ˢ
      .lambda [R] [.fun (.pair alpha beta) .bool] (.and
        (.forall [x, y] [alpha, beta]
          (.imp (.app (.var R) (.pair (.var x) (.var y)))
            (.and (.app A (.var x)) (.app B (.var y)))))
        (.forall [x, y, y'] [alpha, beta, beta] (.imp
          (.and (.app (.var R) (.pair (.var x) (.var y)))
                (.app (.var R) (.pair (.var x) (.var y'))))
          (.eq (.var y) (.var y'))))) :
      .fun (.fun (.pair alpha beta) .bool) .bool := by
  let tauR := SMTType.fun (SMTType.pair alpha beta) .bool
  let body := SMT.Term.and
    (.forall [x, y] [alpha, beta]
      (.imp (.app (.var R) (.pair (.var x) (.var y)))
        (.and (.app A (.var x)) (.app B (.var y)))))
    (.forall [x, y, y'] [alpha, beta, beta] (.imp
      (.and (.app (.var R) (.pair (.var x) (.var y)))
            (.app (.var R) (.pair (.var x) (.var y'))))
      (.eq (.var y) (.var y'))))
  have x_fresh_R : x ∉ Gamma.insert R tauR := by
    intro h
    rw [AList.mem_insert] at h
    exact h.elim (fun h => hR_ne_x h.symm) x_fresh
  have y_fresh_R : y ∉ Gamma.insert R tauR := by
    intro h
    rw [AList.mem_insert] at h
    exact h.elim (fun h => hR_ne_y h.symm) y_fresh
  have y'_fresh_R : y' ∉ Gamma.insert R tauR := by
    intro h
    rw [AList.mem_insert] at h
    exact h.elim (fun h => hR_ne_y' h.symm) y'_fresh
  have typ_A_R : Gamma.insert R tauR ⊢ˢ A : .fun alpha .bool :=
    SMT.Typing.weakening
      (SMT.TypeContext.entries_subset_insert_of_notMem R_fresh) typ_A
      (SMT.Typing.bv_notMem_insert_of_fresh typ_A R_not_bv_A)
  have typ_B_R : Gamma.insert R tauR ⊢ˢ B : .fun beta .bool :=
    SMT.Typing.weakening
      (SMT.TypeContext.entries_subset_insert_of_notMem R_fresh) typ_B
      (SMT.Typing.bv_notMem_insert_of_fresh typ_B R_not_bv_B)
  have typ_body : Gamma.insert R tauR ⊢ˢ body : .bool := by
    dsimp [body]
    apply SMT.Typing.and
    · refine SMT.Typing.forall (Gamma.insert R tauR) [x, y]
        [alpha, beta] _ ?_ ?_ (by simp) rfl ?_
      · intro v hv
        rw [List.mem_cons, List.mem_singleton] at hv
        exact hv.elim (fun h => h ▸ x_fresh_R)
          (fun h => h ▸ y_fresh_R)
      · intro v hv hbv
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
        simp only [SMT.bv, List.mem_append, List.mem_nil_iff,
          false_or, or_false] at hbv
        rcases hv with rfl | rfl
        · exact hbv.elim x_not_bv_A x_not_bv_B
        · exact hbv.elim y_not_bv_A y_not_bv_B
      · have hupdate : SMT.TypeContext.update (Gamma.insert R tauR)
            [x, y] [alpha, beta] rfl =
            ((Gamma.insert R tauR).insert x alpha).insert y beta := by
          simp only [SMT.TypeContext.update, List.length_cons,
            List.length_nil, zero_add, Fin.foldl_succ_last,
            Fin.getElem_fin, Fin.val_cast, Fin.val_last,
            List.getElem_cons_zero, Fin.val_castSucc, Fin.foldl_zero]
          rfl
        rw [hupdate]
        have y_fresh_Rx : y ∉ (Gamma.insert R tauR).insert x alpha := by
          intro h
          rw [AList.mem_insert] at h
          exact h.elim (fun h => hx_ne_y h.symm) y_fresh_R
        have hsub : (Gamma.insert R tauR).entries ⊆
            (((Gamma.insert R tauR).insert x alpha).insert y beta).entries :=
          (SMT.TypeContext.entries_subset_insert_of_notMem x_fresh_R).trans
            (SMT.TypeContext.entries_subset_insert_of_notMem y_fresh_Rx)
        have hbv_A : ∀ v ∈ SMT.bv A,
            v ∉ ((Gamma.insert R tauR).insert x alpha).insert y beta := by
          intro v hv hmem
          rw [AList.mem_insert] at hmem
          rcases hmem with rfl | hmem
          · exact y_not_bv_A hv
          rw [AList.mem_insert] at hmem
          rcases hmem with rfl | hmem
          · exact x_not_bv_A hv
          rw [AList.mem_insert] at hmem
          rcases hmem with rfl | hmem
          · exact R_not_bv_A hv
          · exact SMT.Typing.bv_notMem_context typ_A v hv hmem
        have hbv_B : ∀ v ∈ SMT.bv B,
            v ∉ ((Gamma.insert R tauR).insert x alpha).insert y beta := by
          intro v hv hmem
          rw [AList.mem_insert] at hmem
          rcases hmem with rfl | hmem
          · exact y_not_bv_B hv
          rw [AList.mem_insert] at hmem
          rcases hmem with rfl | hmem
          · exact x_not_bv_B hv
          rw [AList.mem_insert] at hmem
          rcases hmem with rfl | hmem
          · exact R_not_bv_B hv
          · exact SMT.Typing.bv_notMem_context typ_B v hv hmem
        apply SMT.Typing.imp
        · apply SMT.Typing.app
          · apply SMT.Typing.var
            rw [AList.lookup_insert_ne hR_ne_y,
              AList.lookup_insert_ne hR_ne_x, AList.lookup_insert]
          · apply SMT.Typing.pair
            · apply SMT.Typing.var
              rw [AList.lookup_insert_ne hx_ne_y, AList.lookup_insert]
            · apply SMT.Typing.var
              rw [AList.lookup_insert]
        · apply SMT.Typing.and
          · apply SMT.Typing.app
            · exact SMT.Typing.weakening hsub typ_A_R hbv_A
            · apply SMT.Typing.var
              rw [AList.lookup_insert_ne hx_ne_y, AList.lookup_insert]
          · apply SMT.Typing.app
            · exact SMT.Typing.weakening hsub typ_B_R hbv_B
            · apply SMT.Typing.var
              rw [AList.lookup_insert]
    · refine SMT.Typing.forall (Gamma.insert R tauR) [x, y, y']
        [alpha, beta, beta] _ ?_ ?_ (by simp) rfl ?_
      · intro v hv
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
        rcases hv with rfl | rfl | rfl
        · exact x_fresh_R
        · exact y_fresh_R
        · exact y'_fresh_R
      · intro v _ hbv
        simp only [SMT.bv, List.mem_append, List.mem_nil_iff,
          or_false] at hbv
      · have hupdate : SMT.TypeContext.update (Gamma.insert R tauR)
            [x, y, y'] [alpha, beta, beta] rfl =
            (((Gamma.insert R tauR).insert x alpha).insert y beta).insert y' beta := by
          simp only [SMT.TypeContext.update, List.length_cons,
            List.length_nil, zero_add, Fin.foldl_succ_last,
            Fin.getElem_fin, Fin.val_cast, Fin.val_last,
            List.getElem_cons_zero, Fin.val_castSucc, Fin.foldl_zero]
          rfl
        rw [hupdate]
        apply SMT.Typing.imp
        · apply SMT.Typing.and
          · apply SMT.Typing.app
            · apply SMT.Typing.var
              rw [AList.lookup_insert_ne hR_ne_y',
                AList.lookup_insert_ne hR_ne_y,
                AList.lookup_insert_ne hR_ne_x, AList.lookup_insert]
            · apply SMT.Typing.pair
              · apply SMT.Typing.var
                rw [AList.lookup_insert_ne hx_ne_y',
                  AList.lookup_insert_ne hx_ne_y, AList.lookup_insert]
              · apply SMT.Typing.var
                rw [AList.lookup_insert_ne hy_ne_y', AList.lookup_insert]
          · apply SMT.Typing.app
            · apply SMT.Typing.var
              rw [AList.lookup_insert_ne hR_ne_y',
                AList.lookup_insert_ne hR_ne_y,
                AList.lookup_insert_ne hR_ne_x, AList.lookup_insert]
            · apply SMT.Typing.pair
              · apply SMT.Typing.var
                rw [AList.lookup_insert_ne hx_ne_y',
                  AList.lookup_insert_ne hx_ne_y, AList.lookup_insert]
              · apply SMT.Typing.var
                rw [AList.lookup_insert]
        · apply SMT.Typing.eq
          · apply SMT.Typing.var
            rw [AList.lookup_insert_ne hy_ne_y', AList.lookup_insert]
          · apply SMT.Typing.var
            rw [AList.lookup_insert]
  have typ_lambda : Gamma ⊢ˢ .lambda [R] [tauR] body :
      .fun tauR .bool := by
    refine SMT.Typing.lambda Gamma [R] [tauR] _ .bool ?_ ?_ ?_ ?_ ?_
    · intro v hv
      rw [List.mem_singleton] at hv
      exact hv ▸ R_fresh
    · intro v hv hbv
      rw [List.mem_singleton] at hv
      subst v
      dsimp [body] at hbv
      simp only [SMT.bv, List.append_nil] at hbv
      rcases List.mem_append.mp hbv with hL | hR
      · rcases List.mem_append.mp hL with hLL | hLR
        · rcases List.mem_cons.mp hLL with h | hLL'
          · exact hR_ne_x h
          · rcases List.mem_cons.mp hLL' with h | h
            · exact hR_ne_y h
            · exact List.not_mem_nil h
        · rcases List.mem_append.mp hLR with h | hLR'
          · exact List.not_mem_nil h
          · rcases List.mem_append.mp hLR' with h | h
            · exact R_not_bv_A h
            · exact R_not_bv_B h
      · rcases List.mem_cons.mp hR with h | hR'
        · exact hR_ne_x h
        · rcases List.mem_cons.mp hR' with h | hR''
          · exact hR_ne_y h
          · rcases List.mem_cons.mp hR'' with h | h
            · exact hR_ne_y' h
            · exact List.not_mem_nil h
    · exact Nat.zero_lt_succ 0
    · rfl
    · have hupdate : SMT.TypeContext.update Gamma [R] [tauR] rfl =
          Gamma.insert R tauR := by
        simp only [SMT.TypeContext.update, List.length_cons,
          List.length_nil, zero_add, Nat.reduceAdd, Fin.cast_eq_self,
          Fin.getElem_fin, Fin.val_eq_zero, List.getElem_cons_zero,
          Fin.foldl_succ, Fin.foldl_zero]
      rw [hupdate]
      exact typ_body
  simpa [tauR, body] using typ_lambda

abbrev EncodePFunTailRepSpec.{u}
    (alpha beta : BType) (A B : SMT.Term) : Prop :=
  ∀ {Lambda : SMT.TypeContext} {n : ℕ} {used : List SMT.𝒱},
    Lambda ⊢ˢ A : (BType.set alpha).toSMTType →
    Lambda ⊢ˢ B : (BType.set beta).toSMTType →
    (∀ v ∈ SMT.bv A, v ∈ used) →
    (∀ v ∈ SMT.bv B, v ∈ used) →
    ⦃fun ⟨env, Lambda'⟩ =>
      ⌜Lambda' = Lambda ∧ env.freshvarsc = n ∧
        Lambda.keys ⊆ env.usedVars ∧ env.usedVars = used⌝⦄
    encodePFunTail A B alpha.toSMTType beta.toSMTType
    ⦃⇓? ⟨t, sigma⟩ ⟨env', Gamma'⟩ =>
      ⌜used ⊆ env'.usedVars ∧
        Lambda ⊆ Gamma' ∧
        Gamma'.keys ⊆ env'.usedVars ∧
        Nonempty (sigma ~>
          (BType.set (BType.set (alpha ×ᴮ beta))).toSMTType) ∧
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
                (⟨pfunSet X Y,
                  BType.set (BType.set (alpha ×ᴮ beta)),
                  pfunSet_mem_btype hX hY⟩ : _root_.B.Dom) denOut⌝⦄

set_option maxHeartbeats 7000000 in
theorem encodePFunTail_rep_spec.{u}
    (alpha beta : BType) (A B : SMT.Term) :
    EncodePFunTailRepSpec.{u} alpha beta A B := by
  unfold EncodePFunTailRepSpec
  intro Lambda n used typ_A typ_B bv_A_used bv_B_used
  unfold encodePFunTail
  mstart
  mintro pre ∀St₀
  mpure pre
  obtain ⟨rfl, rfl, St₀_keys, rfl⟩ := pre
  mspec SMT.freshVar_spec
  next R =>
    mrename_i post₁
    mintro ∀St₁
    mpure post₁
    obtain ⟨St₁_types_eq, R_fresh, _, St₁_used_eq,
      R_not_used⟩ := post₁
    mspec SMT.freshVar_spec
    next x =>
      mrename_i post₂
      mintro ∀St₂
      mpure post₂
      obtain ⟨St₂_types_eq, x_fresh, _, St₂_used_eq,
        x_not_used⟩ := post₂
      mspec SMT.freshVar_spec
      next y =>
        mrename_i post₃
        mintro ∀St₃
        mpure post₃
        obtain ⟨St₃_types_eq, y_fresh, _, St₃_used_eq,
          y_not_used⟩ := post₃
        mspec SMT.freshVar_spec
        next y' =>
          mrename_i post₄
          mintro ∀St₄
          mpure post₄
          obtain ⟨St₄_types_eq, y'_fresh, _, St₄_used_eq,
            y'_not_used⟩ := post₄
          mspec SMT.eraseFromContext_spec
          mrename_i postER
          mintro ∀StER
          mpure postER
          obtain ⟨StER_types_eq, _, StER_used_eq⟩ := postER
          mspec SMT.eraseFromContext_spec
          mrename_i postEx
          mintro ∀StEx
          mpure postEx
          obtain ⟨StEx_types_eq, _, StEx_used_eq⟩ := postEx
          mspec SMT.eraseFromContext_spec
          mrename_i postEy
          mintro ∀StEy
          mpure postEy
          obtain ⟨StEy_types_eq, _, StEy_used_eq⟩ := postEy
          mspec SMT.eraseFromContext_spec
          mrename_i postEy'
          mintro ∀StEy'
          mpure postEy'
          obtain ⟨StEy'_types_eq, _, StEy'_used_eq⟩ := postEy'

          let tauR := SMTType.fun
            (SMTType.pair alpha.toSMTType beta.toSMTType) .bool
          have x_fresh₀ : x ∉ St₀.types.insert R tauR := by
            simpa [tauR, St₁_types_eq] using x_fresh
          have y_fresh₀ : y ∉
              (St₀.types.insert R tauR).insert x alpha.toSMTType := by
            simpa [tauR, St₂_types_eq, St₁_types_eq] using y_fresh
          have y'_fresh₀ : y' ∉
              ((St₀.types.insert R tauR).insert x alpha.toSMTType).insert y
                beta.toSMTType := by
            simpa [tauR, St₃_types_eq, St₂_types_eq,
              St₁_types_eq] using y'_fresh
          have StEy'_types_final : StEy'.types = St₀.types := by
            rw [StEy'_types_eq, StEy_types_eq, StEx_types_eq,
              StER_types_eq, St₄_types_eq, St₃_types_eq,
              St₂_types_eq, St₁_types_eq]
            exact erase_four_rep_pfun R_fresh x_fresh₀ y_fresh₀ y'_fresh₀
          have hR_ne_x : R ≠ x := by
            intro h; subst x; exact x_fresh₀ (by simp)
          have hR_ne_y : R ≠ y := by
            intro h; subst y; exact y_fresh₀ (by simp)
          have hR_ne_y' : R ≠ y' := by
            intro h; subst y'; exact y'_fresh₀ (by simp)
          have hx_ne_y : x ≠ y := by
            intro h; subst y; exact y_fresh₀ (by simp)
          have hx_ne_y' : x ≠ y' := by
            intro h; subst y'; exact y'_fresh₀ (by simp)
          have hy_ne_y' : y ≠ y' := by
            intro h; subst y'; exact y'_fresh₀ (by simp)
          have x_fresh_ctx : x ∉ St₀.types := by
            intro h; exact x_fresh₀ (by simp [h])
          have y_fresh_ctx : y ∉ St₀.types := by
            intro h; exact y_fresh₀ (by simp [h])
          have y'_fresh_ctx : y' ∉ St₀.types := by
            intro h; exact y'_fresh₀ (by simp [h])
          have R_not_bv_A : R ∉ SMT.bv A :=
            fun h => R_not_used (bv_A_used R h)
          have R_not_bv_B : R ∉ SMT.bv B :=
            fun h => R_not_used (bv_B_used R h)
          have x_not_bv_A : x ∉ SMT.bv A := fun h => by
            apply x_not_used
            rw [St₁_used_eq]
            exact List.mem_cons_of_mem _ (bv_A_used x h)
          have x_not_bv_B : x ∉ SMT.bv B := fun h => by
            apply x_not_used
            rw [St₁_used_eq]
            exact List.mem_cons_of_mem _ (bv_B_used x h)
          have y_not_bv_A : y ∉ SMT.bv A := fun h => by
            apply y_not_used
            rw [St₂_used_eq, St₁_used_eq]
            exact List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (bv_A_used y h))
          have y_not_bv_B : y ∉ SMT.bv B := fun h => by
            apply y_not_used
            rw [St₂_used_eq, St₁_used_eq]
            exact List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (bv_B_used y h))

          let pfunBody : SMT.Term :=
            .and
              (.forall [x, y] [alpha.toSMTType, beta.toSMTType]
                (.imp (.app (.var R) (.pair (.var x) (.var y)))
                  (.and (.app A (.var x)) (.app B (.var y)))))
              (.forall [x, y, y']
                [alpha.toSMTType, beta.toSMTType, beta.toSMTType] (.imp
                  (.and (.app (.var R) (.pair (.var x) (.var y)))
                        (.app (.var R) (.pair (.var x) (.var y'))))
                  (.eq (.var y) (.var y'))))
          let tpfun : SMT.Term := .lambda [R] [tauR] pfunBody
          have typ_tpfun : St₀.types ⊢ˢ tpfun :
              (BType.set (BType.set (alpha ×ᴮ beta))).toSMTType := by
            simpa [tpfun, pfunBody, tauR] using
              pfun_lambda_typing typ_A typ_B R_fresh x_fresh_ctx
                y_fresh_ctx y'_fresh_ctx R_not_bv_A R_not_bv_B
                x_not_bv_A x_not_bv_B y_not_bv_A y_not_bv_B
                hR_ne_x hR_ne_y hR_ne_y' hx_ne_y hx_ne_y' hy_ne_y'
          have fv_tpfun_sub : SMT.fv tpfun ⊆ SMT.fv A ++ SMT.fv B := by
            intro v hv
            dsimp [tpfun] at hv
            rw [SMT.fv, List.mem_removeAll_iff] at hv
            obtain ⟨hv_body, hv_ne_R⟩ := hv
            dsimp [pfunBody] at hv_body
            rw [SMT.fv, List.mem_append] at hv_body
            rcases hv_body with hv_left | hv_right
            · rw [SMT.fv, List.mem_removeAll_iff] at hv_left
              obtain ⟨hv_imp, hv_ne_xy⟩ := hv_left
              rw [SMT.fv, List.mem_append] at hv_imp
              rcases hv_imp with hv_app | hv_and
              · rw [SMT.fv, List.mem_append] at hv_app
                rcases hv_app with hvR | hvpair
                · exfalso
                  apply hv_ne_R
                  simpa [SMT.fv] using hvR
                · rw [SMT.fv, List.mem_append] at hvpair
                  rcases hvpair with hvx | hvy
                  · exfalso
                    apply hv_ne_xy
                    have : v = x := by simpa [SMT.fv] using hvx
                    simp [this]
                  · exfalso
                    apply hv_ne_xy
                    have : v = y := by simpa [SMT.fv] using hvy
                    simp [this]
              · rw [SMT.fv, List.mem_append] at hv_and
                rcases hv_and with hvAx | hvBy
                · rw [SMT.fv, List.mem_append] at hvAx
                  rcases hvAx with hvA | hvx
                  · exact List.mem_append_left _ hvA
                  · exfalso
                    apply hv_ne_xy
                    have : v = x := by simpa [SMT.fv] using hvx
                    simp [this]
                · rw [SMT.fv, List.mem_append] at hvBy
                  rcases hvBy with hvB | hvy
                  · exact List.mem_append_right _ hvB
                  · exfalso
                    apply hv_ne_xy
                    have : v = y := by simpa [SMT.fv] using hvy
                    simp [this]
            · rw [SMT.fv, List.mem_removeAll_iff] at hv_right
              obtain ⟨hv_imp, hv_ne_xyy'⟩ := hv_right
              rw [SMT.fv, List.mem_append] at hv_imp
              rcases hv_imp with hv_and | hv_eq
              · rw [SMT.fv, List.mem_append] at hv_and
                rcases hv_and with hv1 | hv2
                · rw [SMT.fv, List.mem_append] at hv1
                  rcases hv1 with hvR | hvpair
                  · exfalso
                    apply hv_ne_R
                    simpa [SMT.fv] using hvR
                  · rw [SMT.fv, List.mem_append] at hvpair
                    rcases hvpair with hvx | hvy
                    · exfalso
                      apply hv_ne_xyy'
                      have : v = x := by simpa [SMT.fv] using hvx
                      simp [this]
                    · exfalso
                      apply hv_ne_xyy'
                      have : v = y := by simpa [SMT.fv] using hvy
                      simp [this]
                · rw [SMT.fv, List.mem_append] at hv2
                  rcases hv2 with hvR | hvpair
                  · exfalso
                    apply hv_ne_R
                    simpa [SMT.fv] using hvR
                  · rw [SMT.fv, List.mem_append] at hvpair
                    rcases hvpair with hvx | hvy'
                    · exfalso
                      apply hv_ne_xyy'
                      have : v = x := by simpa [SMT.fv] using hvx
                      simp [this]
                    · exfalso
                      apply hv_ne_xyy'
                      have : v = y' := by simpa [SMT.fv] using hvy'
                      simp [this]
              · rw [SMT.fv, List.mem_append] at hv_eq
                rcases hv_eq with hvy | hvy'
                · exfalso
                  apply hv_ne_xyy'
                  have : v = y := by simpa [SMT.fv] using hvy
                  simp [this]
                · exfalso
                  apply hv_ne_xyy'
                  have : v = y' := by simpa [SMT.fv] using hvy'
                  simp [this]

          mspec Std.Do.Spec.pure
          mpure_intro
          and_intros
          · intro v hv
            rw [StEy'_used_eq, StEy_used_eq, StEx_used_eq,
              StER_used_eq, St₄_used_eq, St₃_used_eq,
              St₂_used_eq, St₁_used_eq]
            exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hv)))
          · simp [StEy'_types_final]
          · intro v hv
            rw [StEy'_types_final] at hv
            rw [StEy'_used_eq, StEy_used_eq, StEx_used_eq,
              StER_used_eq, St₄_used_eq, St₃_used_eq,
              St₂_used_eq, St₁_used_eq]
            exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (St₀_keys hv))))
          · exact ⟨castPath.reflexive
              (BType.set (BType.set (alpha ×ᴮ beta))).toSMTType⟩
          · simpa [StEy'_types_final, tpfun, pfunBody, tauR] using
              typ_tpfun
          · intro v hv hv_not
            simpa [StEy'_types_final] using hv_not
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
            have hcov_tpfun : RenamingContext.CoversFV Theta tpfun := by
              intro v hv
              have hv' := fv_tpfun_sub hv
              rw [List.mem_append] at hv'
              exact hv'.elim (hcov_A v) (hcov_B v)
            have hcov_tpfun_full :
                RenamingContext.CoversFV ThetaFull tpfun := by
              intro v hv
              have hvkeep : v ∈ keep := fv_tpfun_sub hv
              change (SMT.RenamingContext.completeOutside
                Theta St₀.types keep v).isSome = true
              rw [SMT.RenamingContext.completeOutside_eq_of_mem hvkeep]
              exact hcov_tpfun v hv
            have R_not_fv_A : R ∉ SMT.fv A := fun hv =>
              R_fresh (SMT.Typing.mem_context_of_mem_fv typ_A hv)
            have R_not_fv_B : R ∉ SMT.fv B := fun hv =>
              R_fresh (SMT.Typing.mem_context_of_mem_fv typ_B hv)
            have x_not_fv_A : x ∉ SMT.fv A := fun hv =>
              x_fresh_ctx (SMT.Typing.mem_context_of_mem_fv typ_A hv)
            have x_not_fv_B : x ∉ SMT.fv B := fun hv =>
              x_fresh_ctx (SMT.Typing.mem_context_of_mem_fv typ_B hv)
            have y_not_fv_A : y ∉ SMT.fv A := fun hv =>
              y_fresh_ctx (SMT.Typing.mem_context_of_mem_fv typ_A hv)
            have y_not_fv_B : y ∉ SMT.fv B := fun hv =>
              y_fresh_ctx (SMT.Typing.mem_context_of_mem_fv typ_B hv)
            have y'_not_fv_A : y' ∉ SMT.fv A := fun hv =>
              y'_fresh_ctx (SMT.Typing.mem_context_of_mem_fv typ_A hv)
            have y'_not_fv_B : y' ∉ SMT.fv B := fun hv =>
              y'_fresh_ctx (SMT.Typing.mem_context_of_mem_fv typ_B hv)
            obtain ⟨denOut, hdenOut_full, htyOut, hretractOut⟩ :=
              pfun_lambda_denotation
                (αx := alpha) (βx := beta)
                (A_enc := A) (B_enc := B)
                (R := R) (x := x) (y := y) (y' := y')
                (Δctx := ThetaFull)
                (den_A := ⟨Aval, (BType.set alpha).toSMTType, hAval⟩)
                (den_B := ⟨Bval, (BType.set beta).toSMTType, hBval⟩)
                hcov_A_full hcov_B_full hden_A_full hden_B_full
                rfl rfl R_not_fv_A R_not_fv_B
                x_not_fv_A x_not_fv_B y_not_fv_A y_not_fv_B
                y'_not_fv_A y'_not_fv_B R_not_bv_A R_not_bv_B
                x_not_bv_A x_not_bv_B y_not_bv_A y_not_bv_B
                hR_ne_x hR_ne_y hR_ne_y' hx_ne_y hx_ne_y' hy_ne_y'
                (Γ := St₀.types) typ_A typ_B ThetaFull_wt
                R_fresh x_fresh_ctx y_fresh_ctx y'_fresh_ctx
                (by simpa [tpfun, pfunBody, tauR] using hcov_tpfun_full)
            have Out_rel :
                (⟨pfunSet X Y,
                  BType.set (BType.set (alpha ×ᴮ beta)),
                  pfunSet_mem_btype hX hY⟩ : _root_.B.Dom) ≘ᶻ denOut := by
              constructor
              · simpa [tauR] using htyOut
              · simpa [pfunSet, retract_A, retract_B] using hretractOut
            have hdenOut : ⟦tpfun.abstract Theta hcov_tpfun⟧ˢ =
                some denOut := by
              have hagree : RenamingContext.AgreesOnFV Theta ThetaFull tpfun := by
                intro v hv
                symm
                exact SMT.RenamingContext.completeOutside_eq_of_mem
                  (fv_tpfun_sub hv)
              have hcongr := RenamingContext.denote_congr_of_agreesOnFV
                (t := tpfun) (h1 := hcov_tpfun)
                (h2 := hcov_tpfun_full) hagree
              simpa [RenamingContext.denote, tpfun, pfunBody, tauR] using
                hcongr.trans hdenOut_full
            have target_respects :
                SMT.RenamingContext.RespectsTypeContextOnFV
                  Theta St₀.types tpfun := by
              intro v sigma hv hlookup
              have hv' := fv_tpfun_sub hv
              rw [List.mem_append] at hv'
              exact hv'.elim
                (fun h => respects_A h hlookup)
                (fun h => respects_B h hlookup)
            refine ⟨Theta,
              (by simpa [tpfun, pfunBody, tauR] using hcov_tpfun),
              denOut, ?_⟩
            and_intros
            · exact RenamingContext.extends_refl Theta
            · intro v hv
              apply Theta_none
              intro hvused
              apply hv
              rw [StEy'_used_eq, StEy_used_eq, StEx_used_eq,
                StER_used_eq, St₄_used_eq, St₃_used_eq,
                St₂_used_eq, St₁_used_eq]
              exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hvused)))
            · simpa [StEy'_types_final, tpfun, pfunBody, tauR] using
                target_respects
            · intro v hv
              rw [StEy'_types_final]
              exact Theta_dom v hv
            · simpa [tpfun, pfunBody, tauR] using hdenOut
            · simpa [tauR] using htyOut
            · exact (RDom.toRDomCastSupported Out_rel).1
            · exact (RDom.toRDomCastSupported Out_rel).2

set_option maxHeartbeats 9000000 in
theorem encodeTerm_rep_spec.pfun_case.{u}
    (S T : B.Term)
    (S_ih : EncodeTermRepIH.{u} S)
    (T_ih : EncodeTermRepIH.{u} T)
    (E : B.Env) {Lambda : SMT.TypeContext} {tau : BType}
    (typ_t : E.context ⊢ᴮ B.Term.pfun S T : tau)
    {Delta : B.RenamingContext.Context}
    (Delta_fv : ∀ v ∈ B.fv (B.Term.pfun S T),
      (Delta v).isSome = true)
    {Delta0 : SMT.RenamingContext.Context.{u}}
    (related : RValuationCastSupportedOnFV Delta Delta0
      (B.Term.pfun S T))
    {used : List SMT.𝒱}
    (Delta0_none : ∀ v ∉ used, Delta0 v = none)
    (Delta0_dom : ∀ v, Delta0 v ≠ none → v ∈ Lambda)
    {U : ZFSet.{u}} {hU : U ∈ ⟦tau⟧ᶻ}
    (den_t : ⟦(B.Term.pfun S T).abstract Delta Delta_fv⟧ᴮ =
      some ⟨U, tau, hU⟩)
    (vars_used : ∀ v ∈ (B.Term.pfun S T).vars, v ∈ used)
    (Lambda_inv : ∀ v ∈ (B.Term.pfun S T).vars,
      v ∈ Lambda → v ∈ E.context)
    (bv_nodup : (B.bv (B.Term.pfun S T)).Nodup)
    (respects : B.RenamingContext.RespectsTypeContextOnFV
      Delta0 Lambda (B.Term.pfun S T))
    (fv_in_Lambda : ∀ v ∈ B.fv (B.Term.pfun S T), v ∈ Lambda)
    (wf : B.RenWF E.context Delta)
    {n : ℕ} :
    ⦃fun ⟨E0, Lambda'⟩ =>
      ⌜Lambda' = Lambda ∧ E0.freshvarsc = n ∧
        Lambda.keys ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
    encodeTerm (B.Term.pfun S T) E
    ⦃⇓? (⟨t', sigma⟩ : SMT.Term × SMTType) ⟨E', Gamma'⟩ =>
      ⌜EncodeTermRepPost (B.Term.pfun S T) tau Lambda Delta Delta0
        used U hU E t' sigma E' Gamma'⌝⦄ := by
  mstart
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_keys, St_used_eq⟩ := pre
  rw [encodeTerm_pfun_via_tail]
  obtain ⟨alpha, beta, rfl, typ_S, typ_T⟩ := B.Typing.pfunE typ_t
  obtain ⟨X, Y, hX, hY, den_S, den_T, rfl⟩ :=
    B.denote_pfun_inv_rep Delta_fv den_t
  have fv_S_sub : B.fv S ⊆ B.fv (B.Term.pfun S T) := by
    intro v hv
    simpa [B.fv] using (Or.inl hv : v ∈ B.fv S ∨ v ∈ B.fv T)
  have fv_T_sub : B.fv T ⊆ B.fv (B.Term.pfun S T) := by
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
      mspec Std.Do.Spec.throw_StateT
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
          have hv_pfun : v ∈ (B.Term.pfun S T).vars := by
            simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
              List.mem_append] at hv ⊢
            rcases hv with h | h <;> [left; right] <;> exact .inr h
          by_cases hv_Lambda : v ∈ St.types
          · exact Lambda_inv v hv_pfun hv_Lambda
          · have hv_vars_S : v ∈ B.Term.vars S := by
              by_contra hnot
              exact absurd hGamma
                (preserves_S v (vars_used v hv_pfun) hv_Lambda hnot)
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
        mspec Std.Do.Spec.throw_StateT
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

      mspec encodePFunTail_rep_spec alpha beta Senc Tenc
        typ_Senc_final typ_Tenc bv_Senc_final bv_Tenc_used
      rename_i out_pfun
      obtain ⟨PFunEnc, sigmaPFun⟩ := out_pfun
      mrename_i post_pfun
      mintro ∀StPFun
      mpure post_pfun
      obtain ⟨used_sub_pfun, types_sub_pfun, keys_sub_pfun, path_pfun,
        typ_PFunEnc, preserves_pfun, semantic_pfun⟩ := post_pfun
      obtain ⟨DeltaPFun, hcov_PFunEnc, denPFun, DeltaPFun_ext,
          DeltaPFun_none, target_respects_PFunEnc, DeltaPFun_dom,
          hden_PFunEnc, hdenPFun_type, PFun_rel⟩ :=
        semantic_pfun DeltaT hcov_Senc_final hcov_Tenc DeltaT_none
          target_respects_Senc_final target_respects_Tenc DeltaT_dom
          X Y hX hY
          (⟨Sval, (BType.set alpha).toSMTType, hSval⟩ : SMT.Dom)
          (⟨Tval, (BType.set beta).toSMTType, hTval⟩ : SMT.Dom)
          hden_Senc_final hden_Tenc S_rel T_rel
      have DeltaT_ext0 := RenamingContext.extends_trans DeltaT_ext DeltaS_ext
      have DeltaPFun_ext0 :=
        RenamingContext.extends_trans DeltaPFun_ext DeltaT_ext0
      have types_sub0 : St.types ⊆ StPFun.types :=
        fun _ h => types_sub_pfun (types_sub_T (types_sub_S h))

      mpure_intro
      and_intros
      · intro v hv
        exact used_sub_pfun (used_sub_T
          (used_sub_S (by simpa [St_used_eq] using hv)))
      · exact types_sub0
      · exact keys_sub_pfun
      · intro v hv
        rw [B.fv, List.mem_append] at hv
        exact hv.elim
          (fun h => used_sub_pfun (used_sub_T (covers_S v h)))
          (fun h => used_sub_pfun (covers_T v h))
      · exact path_pfun
      · exact typ_PFunEnc
      · trivial
      · intro v hv hLambda hvars
        have hv_StS : v ∈ StS.env.usedVars :=
          used_sub_S (by simpa [St_used_eq] using hv)
        have hv_not_StS : v ∉ StS.types :=
          preserves_S v (by simpa [St_used_eq] using hv) hLambda
            ((B.Term.notMem_vars_pfun.mp hvars).1)
        have hv_not_StT : v ∉ StT.types :=
          preserves_T v hv_StS hv_not_StS
            ((B.Term.notMem_vars_pfun.mp hvars).2)
        exact preserves_pfun v (used_sub_T hv_StS) hv_not_StT
      · refine ⟨DeltaPFun, hcov_PFunEnc, DeltaPFun_ext0,
          related.of_extends DeltaPFun_ext0, DeltaPFun_none, ?_,
          target_respects_PFunEnc, DeltaPFun_dom, denPFun,
          hden_PFunEnc, hdenPFun_type, ?_, ?_⟩
        · exact respects.of_extends DeltaPFun_ext0 types_sub0
            (fun _ h => h) fv_in_Lambda
        · simpa only [proof_irrel_heq] using PFun_rel
        · intro Delta_alt Delta_fv_alt Delta0_alt related_alt wf_alt
            Delta0_alt_none respects_alt Delta0_alt_dom
            U_alt hU_alt den_t_alt
          obtain ⟨X_alt, Y_alt, hX_alt, hY_alt,
              den_S_alt, den_T_alt, rfl⟩ :=
            B.denote_pfun_inv_rep Delta_fv_alt den_t_alt
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
          obtain ⟨DeltaPFun_alt, hcov_PFunEnc_alt, denPFun_alt,
              DeltaPFun_alt_ext, DeltaPFun_alt_none,
              target_respects_PFunEnc_alt, DeltaPFun_alt_dom,
              hden_PFunEnc_alt, hdenPFun_alt_type, PFun_alt_rel⟩ :=
            semantic_pfun DeltaT_alt hcov_Senc_alt_final hcov_Tenc_alt
              DeltaT_alt_none target_respects_Senc_alt_final
              target_respects_Tenc_alt DeltaT_alt_dom
              X_alt Y_alt hX_alt hY_alt denSenc_alt denTenc_alt
              hden_Senc_alt_final hden_Tenc_alt S_alt_rel T_alt_rel
          have DeltaT_alt_ext0 :=
            RenamingContext.extends_trans DeltaT_alt_ext DeltaS_alt_ext
          have DeltaPFun_alt_ext0 :=
            RenamingContext.extends_trans DeltaPFun_alt_ext DeltaT_alt_ext0
          refine ⟨DeltaPFun_alt, hcov_PFunEnc_alt, denPFun_alt,
            DeltaPFun_alt_ext0,
            related_alt.of_extends DeltaPFun_alt_ext0,
            DeltaPFun_alt_none, ?_, target_respects_PFunEnc_alt,
            DeltaPFun_alt_dom, hden_PFunEnc_alt,
            hdenPFun_alt_type, ?_⟩
          · exact respects_alt.of_extends DeltaPFun_alt_ext0 types_sub0
              (fun _ h => h) fv_in_Lambda
          · simpa only [proof_irrel_heq] using PFun_alt_rel
