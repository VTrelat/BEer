import SMT.Reasoning.Defs
import SMT.Reasoning.LooseningDefs
import SMT.Reasoning.Basic.StateSpecs
import SMT.Reasoning.Basic.LoosenAuxExact.FunAux
import SMT.Reasoning.Basic.DenotationTotality
import SMT.Reasoning.Axioms

open Std.Do B SMT ZFSet

-- Copied from EncodeTermCorrectSet.lean (private there); factor later
private theorem mem_retract_set_iff_app_canonical_eq_zftrue
    {α : BType} {F X : ZFSet} (hF : ⟦α.toSMTType⟧ᶻ.IsFunc 𝔹 F)
    (hRetr : retract (BType.set α) F = X) {x : ZFSet} (hx : x ∈ ⟦α⟧ᶻ) :
    x ∈ X ↔
      ZFSet.fapply F (is_func_is_pfunc hF)
        ⟨ZFSet.fapply (BType.canonicalIsoSMTType α).1
            (is_func_is_pfunc (BType.canonicalIsoSMTType α).2.1)
            ⟨x, by rwa [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType α).2.1]⟩,
          by
            rw [ZFSet.is_func_dom_eq hF]
            exact fapply_mem_range _ _⟩ = zftrue := by
  rw [←hRetr, retract, mem_sep]
  constructor
  · intro h
    obtain ⟨hx', hmem⟩ := h
    rw [dif_pos hx', dif_pos hF] at hmem
    simpa using hmem
  · intro h
    refine ⟨hx, ?_⟩
    rw [dif_pos hx, dif_pos hF]
    simpa using h

-- Helper: app of a characteristic predicate applied to a pair of variables denotes as .bool
private theorem denote_app_var_pair_var_var.{u}
    {α β : SMTType} {WR Wx Wy : SMT.Dom.{u}}
    (hWR_ty : WR.2.1 = SMTType.fun (SMTType.pair α β) .bool)
    (hWx_ty : Wx.2.1 = α) (hWx_mem : Wx.1 ∈ ⟦α⟧ᶻ)
    (hWy_ty : Wy.2.1 = β) (hWy_mem : Wy.1 ∈ ⟦β⟧ᶻ) :
    ∃ D : SMT.Dom.{u}, ⟦SMT.PHOAS.Term.app (.var WR) (.pair (.var Wx) (.var Wy))⟧ˢ = some D ∧ D.2.1 = .bool := by
  -- WR is a function from (.pair α β) to .bool
  have hWR_func : ZFSet.IsFunc ⟦SMTType.pair α β⟧ᶻ ⟦SMTType.bool⟧ᶻ WR.1 := by
    have : WR.1 ∈ ⟦WR.2.1⟧ᶻ := WR.2.2
    rw [hWR_ty, SMTType.toZFSet] at this
    exact ZFSet.mem_funs.mp this
  have hWR_pfunc := ZFSet.is_func_is_pfunc hWR_func
  -- The pair has type .pair α β and value Wx.1.pair Wy.1
  have hpair_mem : Wx.1.pair Wy.1 ∈ ⟦SMTType.pair α β⟧ᶻ := by
    rw [SMTType.toZFSet, ZFSet.pair_mem_prod]; exact ⟨hWx_mem, hWy_mem⟩
  have hpair_dom : Wx.1.pair Wy.1 ∈ WR.1.Dom := by
    rw [ZFSet.is_func_dom_eq hWR_func]; exact hpair_mem
  -- Construct the result
  let result := ZFSet.fapply WR.1 hWR_pfunc ⟨Wx.1.pair Wy.1, hpair_dom⟩
  refine ⟨⟨result.1, .bool, result.2⟩, ?_, rfl⟩
  -- Show the denote equals this
  show SMT.denote (SMT.PHOAS.Term.app (.var WR) (.pair (.var Wx) (.var Wy))) = _
  simp only [SMT.denote, Option.pure_def, Option.bind_some]
  obtain ⟨wr, τR', hwr⟩ := WR
  obtain ⟨wx, τx, hwx⟩ := Wx
  obtain ⟨wy, τy, hwy⟩ := Wy
  dsimp at hWR_ty hWx_ty hWy_ty hpair_mem hpair_dom hWR_func hWR_pfunc ⊢
  subst hWx_ty; subst hWy_ty; subst hWR_ty
  simp only [dif_pos hWR_pfunc, dif_pos hpair_dom, ite_true]
  rfl

private theorem denote_not_some_bool_of_some_bool
    {t : SMT.PHOAS.Term SMT.Dom} {D : SMT.Dom}
    (hden : ⟦t⟧ˢ = some D) (hTy : D.2.1 = .bool) :
    ∃ D' : SMT.Dom, ⟦¬ˢ' t⟧ˢ = some D' ∧ D'.2.1 = .bool := by
  obtain ⟨d, τ, hd⟩ := D; cases hTy
  rw [SMT.denote, hden]
  simp only [Option.pure_def, Option.failure_eq_none, Option.bind_eq_bind, Option.bind_some]
  exact ⟨_, rfl, rfl⟩

private theorem denote_imp_some_bool_of_some_bool
    {p q : SMT.PHOAS.Term SMT.Dom} {Dp Dq : SMT.Dom}
    (hp : ⟦p⟧ˢ = some Dp) (hpTy : Dp.2.1 = .bool)
    (hq : ⟦q⟧ˢ = some Dq) (hqTy : Dq.2.1 = .bool) :
    ∃ D : SMT.Dom, ⟦p ⇒ˢ' q⟧ˢ = some D ∧ D.2.1 = .bool := by
  -- imp p q = not (p and not q)
  obtain ⟨Dnq, hDnq, hDnq_ty⟩ := denote_not_some_bool_of_some_bool hq hqTy
  obtain ⟨Dand, hDand, hDand_ty⟩ := denote_and_some_bool_of_some_bool hp hpTy hDnq hDnq_ty
  exact denote_not_some_bool_of_some_bool hDand hDand_ty

-- imp p q = not(and p (not q))
-- When p = zffalse: and(false, not q) = false, not(false) = zftrue
private theorem denote_imp_eq_zftrue_of_zffalse_left
    {p q : SMT.PHOAS.Term SMT.Dom} {Dp Dq : SMT.Dom}
    (hp : ⟦p⟧ˢ = some Dp) (hpTy : Dp.2.1 = .bool) (hpFalse : Dp.1 = zffalse)
    (hq : ⟦q⟧ˢ = some Dq) (hqTy : Dq.2.1 = .bool) :
    ⟦p ⇒ˢ' q⟧ˢ = some ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
  obtain ⟨Dnq, hDnq, hDnq_ty⟩ := denote_not_some_bool_of_some_bool hq hqTy
  have hDand := denote_and_eq_zffalse_of_some_zffalse_left hp hpTy hpFalse hDnq hDnq_ty
  exact denote_not_eq_zftrue_of_some_zffalse hDand rfl rfl

-- When p = zftrue, q = zftrue: not q = false, and(true, false) = false, not(false) = zftrue
private theorem denote_imp_eq_zftrue_of_zftrue_zftrue
    {p q : SMT.PHOAS.Term SMT.Dom} {Dp Dq : SMT.Dom}
    (hp : ⟦p⟧ˢ = some Dp) (hpTy : Dp.2.1 = .bool) (hpTrue : Dp.1 = zftrue)
    (hq : ⟦q⟧ˢ = some Dq) (hqTy : Dq.2.1 = .bool) (hqTrue : Dq.1 = zftrue) :
    ⟦p ⇒ˢ' q⟧ˢ = some ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
  have hDnq := denote_not_eq_zffalse_of_some_zftrue hq hqTy hqTrue
  have hDand := denote_and_eq_zffalse_of_some_zffalse_right hp hpTy hDnq rfl rfl
  exact denote_not_eq_zftrue_of_some_zffalse hDand rfl rfl

-- If imp(p,q) = zftrue and p = zftrue, then q = zftrue.
-- imp p q = not(and(p, not q)). zftrue → and(p, not q) = zffalse → (since p=zftrue) not q = zffalse → q = zftrue.
private theorem denote_imp_consequent_of_antecedent_zftrue
    {p q : SMT.PHOAS.Term SMT.Dom} {Dp Dq : SMT.Dom}
    (hp : ⟦p⟧ˢ = some Dp) (hpTy : Dp.2.1 = .bool) (hpTrue : Dp.1 = zftrue)
    (hq : ⟦q⟧ˢ = some Dq) (hqTy : Dq.2.1 = .bool)
    {Dimp : SMT.Dom}
    (himp : ⟦p ⇒ˢ' q⟧ˢ = some Dimp) (himpTrue : Dimp.1 = zftrue) :
    Dq.1 = zftrue := by
  -- Case analysis on Dq.fst
  have hDq_mem_𝔹 : Dq.fst ∈ 𝔹 := by have := Dq.snd.snd; rwa [hqTy] at this
  rcases ZFSet.ZFBool.mem_𝔹_iff _ |>.mp hDq_mem_𝔹 with hDq_false | hDq_true
  · -- Dq = zffalse → imp(zftrue, zffalse) = zffalse, contradicts himpTrue
    exfalso
    have hDnq := denote_not_eq_zftrue_of_some_zffalse hq hqTy hDq_false
    have hDand := denote_and_eq_zftrue_of_some_zftrue hp hpTy hpTrue hDnq rfl rfl
    have hDnot := denote_not_eq_zffalse_of_some_zftrue hDand rfl rfl
    -- himp and hDnot give the same denotation (imp = not(and(p, not q)) definitionally)
    have hDnot' : ⟦p ⇒ˢ' q⟧ˢ = some ⟨zffalse, .bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ :=
      show ⟦¬ˢ' (p ∧ˢ' ¬ˢ' q)⟧ˢ = _ from hDnot
    have := Option.some_injective _ (himp.symm.trans hDnot')
    rw [this] at himpTrue; exact ZFSet.zftrue_ne_zffalse himpTrue.symm
  · exact hDq_true

-- If and(p,q) = some D with D.fst = zftrue, then Dp.fst = zftrue and Dq.fst = zftrue.
theorem denote_and_both_zftrue_of_zftrue
    {p q : SMT.PHOAS.Term SMT.Dom} {Dp Dq : SMT.Dom}
    (hp : ⟦p⟧ˢ = some Dp) (hpTy : Dp.2.1 = .bool)
    (hq : ⟦q⟧ˢ = some Dq) (hqTy : Dq.2.1 = .bool)
    {Dand : SMT.Dom}
    (hand : ⟦p ∧ˢ' q⟧ˢ = some Dand) (handTrue : Dand.1 = zftrue) :
    Dp.1 = zftrue ∧ Dq.1 = zftrue := by
  have hDp_mem_𝔹 : Dp.fst ∈ 𝔹 := by have := Dp.snd.snd; rwa [hpTy] at this
  have hDq_mem_𝔹 : Dq.fst ∈ 𝔹 := by have := Dq.snd.snd; rwa [hqTy] at this
  constructor
  · rcases ZFSet.ZFBool.mem_𝔹_iff _ |>.mp hDp_mem_𝔹 with hDp_false | hDp_true
    · exfalso
      have hfalse := denote_and_eq_zffalse_of_some_zffalse_left hp hpTy hDp_false hq hqTy
      rw [hfalse] at hand; have := Option.some_injective _ hand
      rw [← congrArg (·.fst) this] at handTrue; exact ZFSet.zftrue_ne_zffalse handTrue.symm
    · exact hDp_true
  · rcases ZFSet.ZFBool.mem_𝔹_iff _ |>.mp hDq_mem_𝔹 with hDq_false | hDq_true
    · exfalso
      have hfalse := denote_and_eq_zffalse_of_some_zffalse_right hp hpTy hq hqTy hDq_false
      rw [hfalse] at hand; have := Option.some_injective _ hand
      rw [← congrArg (·.fst) this] at handTrue; exact ZFSet.zftrue_ne_zffalse handTrue.symm
    · exact hDq_true

private theorem denote_eq_some_bool
    {t₁ t₂ : SMT.PHOAS.Term SMT.Dom} {D₁ D₂ : SMT.Dom}
    (h₁ : ⟦t₁⟧ˢ = some D₁) (h₂ : ⟦t₂⟧ˢ = some D₂) (hty : D₁.2.1 = D₂.2.1) :
    ∃ D : SMT.Dom, ⟦t₁ =ˢ' t₂⟧ˢ = some D ∧ D.2.1 = .bool := by
  obtain ⟨d₁, τ₁, hd₁⟩ := D₁
  obtain ⟨d₂, τ₂, hd₂⟩ := D₂
  dsimp at hty; subst hty
  rw [SMT.denote, h₁, h₂]
  simp only [Option.pure_def, Option.failure_eq_none, Option.bind_eq_bind, Option.bind_some,
    dif_pos rfl]
  exact ⟨_, rfl, rfl⟩

private theorem pair_hasArity_get_mem'
    {τ₁ τ₂ : SMTType} {x₁ x₂ : ZFSet}
    (hx₁ : x₁ ∈ ⟦τ₁⟧ᶻ) (hx₂ : x₂ ∈ ⟦τ₂⟧ᶻ) :
    (x₁.pair x₂).hasArity [τ₁, τ₂].length ∧
      ∀ i : Fin [τ₁, τ₂].length, (x₁.pair x₂).get [τ₁, τ₂].length i ∈ ⟦[τ₁, τ₂][i]⟧ᶻ := by
  constructor
  · simp [ZFSet.hasArity]
  · intro i
    have hi : i.1 = 0 ∨ i.1 = 1 := by have hi_lt : i.1 < 2 := i.2; omega
    rcases hi with hi | hi
    · have hi' : i = ⟨0, by simp⟩ := Fin.ext hi; rw [hi']; simpa [ZFSet.get] using hx₁
    · have hi' : i = ⟨1, by simp⟩ := Fin.ext hi; rw [hi']; simpa [ZFSet.get] using hx₂

set_option maxHeartbeats 8000000 in
private theorem funBinaryForallEqZftrue.{u}
    {Δctx : SMT.RenamingContext.Context.{u}} {a : SMT.Term} {v₁ v₂ : SMT.𝒱} {τ₁ τ₂ : SMTType}
    (hφ_forall : RenamingContext.CoversFV Δctx (SMT.Term.forall [v₁, v₂] [τ₁, τ₂] a))
    (hgo_cov : ∀ x ∈ SMT.fv a, x ∉ [v₁, v₂] → (Δctx x).isSome = true)
    (hcov_a_upd :
      ∀ W₁ W₂ : SMT.Dom.{u},
        RenamingContext.CoversFV
          (Function.update (Function.update Δctx v₁ (some W₁)) v₂ (some W₂)) a)
    (hbody_total :
      ∀ W₁ W₂ : SMT.Dom.{u}, W₁.snd.fst = τ₁ → W₂.snd.fst = τ₂ →
        ⟦a.abstract (Function.update (Function.update Δctx v₁ (some W₁)) v₂ (some W₂))
          (hcov_a_upd W₁ W₂)⟧ˢ.isSome = true)
    (hbody_ty :
      ∀ W₁ W₂ : SMT.Dom.{u}, W₁.snd.fst = τ₁ → W₂.snd.fst = τ₂ →
        ∀ {D : SMT.Dom.{u}},
          ⟦a.abstract (Function.update (Function.update Δctx v₁ (some W₁)) v₂ (some W₂))
            (hcov_a_upd W₁ W₂)⟧ˢ = some D → D.snd.fst = SMTType.bool)
    (hbody_true :
      ∀ W₁ W₂ : SMT.Dom.{u}, W₁.snd.fst = τ₁ → W₂.snd.fst = τ₂ →
        ∃ D : SMT.Dom.{u},
          ⟦a.abstract (Function.update (Function.update Δctx v₁ (some W₁)) v₂ (some W₂))
            (hcov_a_upd W₁ W₂)⟧ˢ = some D ∧ D.fst = zftrue) :
    ⟦(SMT.Term.forall [v₁, v₂] [τ₁, τ₂] a).abstract Δctx hφ_forall⟧ˢ =
      some ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
  rw [SMT.Term.abstract, dif_pos (by rfl), SMT.denote]
  have hlen : [v₁, v₂].length > 0 := by simp
  rw [dif_pos hlen]
  have hbody_total' :
      ∀ {x_1 : Fin [v₁, v₂].length → SMT.Dom.{u}},
        (∀ i,
          ((x_1 i).snd.fst =
              match i with
              | ⟨i, hi⟩ => [τ₁, τ₂][i]) ∧
            (x_1 i).fst ∈
              ⟦match i with
                | ⟨i, hi⟩ => [τ₁, τ₂][i]⟧ᶻ) →
          ⟦(SMT.Term.abstract.go a [v₁, v₂] Δctx hgo_cov).uncurry x_1⟧ˢ.isSome = true := by
    intro x_1 hx_1
    have hgo :=
      funAbstractGoPair
        (Δctx := Δctx) (P := a) (v₁ := v₁) (v₂ := v₂) (τ₁ := τ₁) (τ₂ := τ₂)
        hgo_cov hcov_a_upd x_1 (by
          intro i
          have hi : i.1 = 0 ∨ i.1 = 1 := by have hi_lt : i.1 < 2 := i.2; omega
          rcases hi with hi | hi
          · have hi' : i = ⟨0, by simp⟩ := Fin.ext hi; cases hi'; simpa using hx_1 ⟨0, by simp⟩
          · have hi' : i = ⟨1, by simp⟩ := Fin.ext hi; cases hi'; simpa using hx_1 ⟨1, by simp⟩)
    rw [hgo]
    let W₁ : SMT.Dom := x_1 ⟨0, by simp⟩
    let W₂ : SMT.Dom := x_1 ⟨1, by simp⟩
    have hW₁_ty : W₁.snd.fst = τ₁ := by
      simpa [W₁] using (hx_1 ⟨0, by simp⟩).1
    have hW₂_ty : W₂.snd.fst = τ₂ := by
      simpa [W₂] using (hx_1 ⟨1, by simp⟩).1
    simpa [W₁, W₂] using hbody_total W₁ W₂ hW₁_ty hW₂_ty
  split_ifs with hsome
  · -- Success branch: the sInter equals zftrue
    apply congrArg some
    apply funDomEqOfTyEqAndFstEq rfl
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_one_sub_one,
      List.getElem_cons_succ, Fin.zero_eta, Fin.isValue,
      List.getElem_cons_zero,
      Option.pure_def, Option.bind_some,
      Fin.foldl_succ_last, Fin.foldl_zero]
    apply sInter_sep_eq_zftrue_of_forall_eq_zftrue
    · exact ⟨τ₁.defaultZFSet.pair τ₂.defaultZFSet, by
        rw [ZFSet.pair_mem_prod]
        exact ⟨SMTType.mem_toZFSet_of_defaultZFSet, SMTType.mem_toZFSet_of_defaultZFSet⟩⟩
    · intro x_1 hx_1
      obtain ⟨a₀, ha₀, b₀, hb₀, hab⟩ := ZFSet.mem_prod.mp hx_1
      subst hab
      split_ifs with hx_arity_raw
      · -- Positive branch: body = zftrue
        let W₁ : SMT.Dom := ⟨a₀, τ₁, ha₀⟩
        let W₂ : SMT.Dom := ⟨b₀, τ₂, hb₀⟩
        obtain ⟨D, hden_body, hD_true⟩ := hbody_true W₁ W₂ rfl rfl
        -- Use funAbstractGoPair with Fin-indexed w to get the rewrite
        let w : Fin 2 → SMT.Dom := fun i =>
          ⟨(a₀.pair b₀).get 2 i, [τ₁, τ₂][↑i], hx_arity_raw.2 i⟩
        have hw : ∀ i : Fin [v₁, v₂].length,
            (w i).snd.fst = [τ₁, τ₂][↑i] ∧ (w i).fst ∈ ⟦[τ₁, τ₂][↑i]⟧ᶻ := by
          intro i; exact ⟨rfl, hx_arity_raw.2 i⟩
        have hgo := funAbstractGoPair hgo_cov hcov_a_upd w hw
        -- w ⟨0,...⟩ = W₁ and w ⟨1,...⟩ = W₂
        have hw0 : w ⟨0, by simp⟩ = W₁ :=
          funDomEqOfTyEqAndFstEq rfl (by simp [w, W₁, ZFSet.get])
        have hw1 : w ⟨1, by simp⟩ = W₂ :=
          funDomEqOfTyEqAndFstEq rfl (by simp [w, W₂, ZFSet.get])
        -- Combine: uncurry w denotes as some D
        have hbody_eq :
            ⟦(SMT.Term.abstract.go a [v₁, v₂] Δctx hgo_cov).uncurry w⟧ˢ = some D := by
          rw [hgo, hw0, hw1]; exact hden_body
        -- The goal has the form (... .get proof).fst = zftrue
        -- The goal's function is definitionally w, so change to use w
        change (⟦(SMT.Term.abstract.go a [v₁, v₂] Δctx hgo_cov).uncurry w⟧ˢ.get _).fst = zftrue
        simp only [hbody_eq, Option.get_some]
        exact hD_true
      · -- Negative branch: contradiction — pairs always satisfy the arity condition
        exfalso; apply hx_arity_raw
        exact ⟨by simp [ZFSet.hasArity], fun i => by
          have hi : i.1 = 0 ∨ i.1 = 1 := by have hi_lt : i.1 < 2 := i.2; omega
          rcases hi with hi | hi
          · have hi' : i = ⟨0, by simp⟩ := Fin.ext hi; rw [hi']; simpa [ZFSet.get] using ha₀
          · have hi' : i = ⟨1, by simp⟩ := Fin.ext hi; rw [hi']; simpa [ZFSet.get] using hb₀⟩
  · exfalso
    apply hsome
    intro x_1 hx_1
    have hgo :=
      funAbstractGoPair
        (Δctx := Δctx) (P := a) (v₁ := v₁) (v₂ := v₂) (τ₁ := τ₁) (τ₂ := τ₂)
        hgo_cov hcov_a_upd x_1 (by
          intro i
          have hi : i.1 = 0 ∨ i.1 = 1 := by have hi_lt : i.1 < 2 := i.2; omega
          rcases hi with hi | hi
          · have hi' : i = ⟨0, by simp⟩ := Fin.ext hi; cases hi'; simpa using hx_1 ⟨0, by simp⟩
          · have hi' : i = ⟨1, by simp⟩ := Fin.ext hi; cases hi'; simpa using hx_1 ⟨1, by simp⟩)
    rw [hgo]
    let W₁ : SMT.Dom := x_1 ⟨0, by simp⟩
    let W₂ : SMT.Dom := x_1 ⟨1, by simp⟩
    have hW₁_ty : W₁.snd.fst = τ₁ := by
      simpa [W₁] using (hx_1 ⟨0, by simp⟩).1
    have hW₂_ty : W₂.snd.fst = τ₂ := by
      simpa [W₂] using (hx_1 ⟨1, by simp⟩).1
    simpa [W₁, W₂] using hbody_total W₁ W₂ hW₁_ty hW₂_ty

-- Inversion of funBinaryForallEqZftrue: if the forall denotes to zftrue,
-- then each body value is zftrue.
set_option maxHeartbeats 8000000 in
private theorem funBinaryForallTrueAt.{u}
    {Δctx : SMT.RenamingContext.Context.{u}} {a : SMT.Term} {v₁ v₂ : SMT.𝒱} {τ₁ τ₂ : SMTType}
    (hφ_forall : RenamingContext.CoversFV Δctx (SMT.Term.forall [v₁, v₂] [τ₁, τ₂] a))
    (hgo_cov : ∀ x ∈ SMT.fv a, x ∉ [v₁, v₂] → (Δctx x).isSome = true)
    (hcov_a_upd :
      ∀ W₁ W₂ : SMT.Dom.{u},
        RenamingContext.CoversFV
          (Function.update (Function.update Δctx v₁ (some W₁)) v₂ (some W₂)) a)
    (hbody_total :
      ∀ W₁ W₂ : SMT.Dom.{u}, W₁.snd.fst = τ₁ → W₂.snd.fst = τ₂ →
        ⟦a.abstract (Function.update (Function.update Δctx v₁ (some W₁)) v₂ (some W₂))
          (hcov_a_upd W₁ W₂)⟧ˢ.isSome = true)
    (hbody_ty :
      ∀ W₁ W₂ : SMT.Dom.{u}, W₁.snd.fst = τ₁ → W₂.snd.fst = τ₂ →
        ∀ {D : SMT.Dom.{u}},
          ⟦a.abstract (Function.update (Function.update Δctx v₁ (some W₁)) v₂ (some W₂))
            (hcov_a_upd W₁ W₂)⟧ˢ = some D → D.snd.fst = SMTType.bool)
    {Φ : SMT.Dom.{u}}
    (hden_forall :
      ⟦(SMT.Term.forall [v₁, v₂] [τ₁, τ₂] a).abstract Δctx hφ_forall⟧ˢ = some Φ)
    (htrue : Φ.fst = zftrue)
    (W₁ W₂ : SMT.Dom.{u})
    (hW₁_ty : W₁.snd.fst = τ₁) (hW₂_ty : W₂.snd.fst = τ₂) :
    ∃ D : SMT.Dom.{u},
      ⟦a.abstract (Function.update (Function.update Δctx v₁ (some W₁)) v₂ (some W₂))
        (hcov_a_upd W₁ W₂)⟧ˢ = some D ∧ D.fst = zftrue := by
  obtain ⟨D, hD⟩ := Option.isSome_iff_exists.mp (hbody_total W₁ W₂ hW₁_ty hW₂_ty)
  refine ⟨D, hD, ?_⟩
  have hD_ty := hbody_ty W₁ W₂ hW₁_ty hW₂_ty hD
  have hD_mem_𝔹 : D.fst ∈ 𝔹 := by have := D.snd.snd; rwa [hD_ty] at this
  rcases ZFSet.ZFBool.mem_𝔹_iff _ |>.mp hD_mem_𝔹 with hD_false | hD_true
  · exfalso
    -- If D.fst = zffalse, the sInter in the forall denotation is zffalse, not zftrue
    have hforall_zffalse :
        ⟦(SMT.Term.forall [v₁, v₂] [τ₁, τ₂] a).abstract Δctx hφ_forall⟧ˢ =
        some ⟨zffalse, SMTType.bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
      rw [SMT.Term.abstract, dif_pos (by rfl), SMT.denote]
      have hlen : [v₁, v₂].length > 0 := by simp
      rw [dif_pos hlen]
      have hbody_total' :
          ∀ {x_1 : Fin [v₁, v₂].length → SMT.Dom.{u}},
            (∀ i, ((x_1 i).snd.fst = match i with | ⟨i, hi⟩ => [τ₁, τ₂][i]) ∧
              (x_1 i).fst ∈ ⟦match i with | ⟨i, hi⟩ => [τ₁, τ₂][i]⟧ᶻ) →
            ⟦(SMT.Term.abstract.go a [v₁, v₂] Δctx hgo_cov).uncurry x_1⟧ˢ.isSome = true := by
        intro x_1 hx_1
        have hgo := funAbstractGoPair hgo_cov hcov_a_upd x_1 (by
          intro i; have hi : i.1 = 0 ∨ i.1 = 1 := by have : i.1 < 2 := i.2; omega
          rcases hi with hi | hi
          · have hi' : i = ⟨0, by simp⟩ := Fin.ext hi; cases hi'; simpa using hx_1 ⟨0, by simp⟩
          · have hi' : i = ⟨1, by simp⟩ := Fin.ext hi; cases hi'; simpa using hx_1 ⟨1, by simp⟩)
        rw [hgo]
        let W₁' : SMT.Dom := x_1 ⟨0, by simp⟩
        let W₂' : SMT.Dom := x_1 ⟨1, by simp⟩
        simpa [W₁', W₂'] using hbody_total W₁' W₂'
          (by simpa [W₁'] using (hx_1 ⟨0, by simp⟩).1)
          (by simpa [W₂'] using (hx_1 ⟨1, by simp⟩).1)
      split_ifs with hsome
      · apply congrArg some; apply funDomEqOfTyEqAndFstEq rfl
        simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_one_sub_one,
          List.getElem_cons_succ, Fin.zero_eta, Fin.isValue, List.getElem_cons_zero,
          Option.pure_def, Option.bind_some, Fin.foldl_succ_last, Fin.foldl_zero]
        apply sInter_sep_eq_empty_of_exists_eq_empty
        refine ⟨W₁.fst.pair W₂.fst, by
          rw [ZFSet.pair_mem_prod]
          exact ⟨by rw [← hW₁_ty]; exact W₁.2.2, by rw [← hW₂_ty]; exact W₂.2.2⟩, ?_⟩
        split_ifs with hx_arity
        · let w : Fin 2 → SMT.Dom := fun i =>
            ⟨(W₁.fst.pair W₂.fst).get 2 i, [τ₁, τ₂][↑i], hx_arity.2 i⟩
          have hw : ∀ i : Fin [v₁, v₂].length,
              (w i).snd.fst = [τ₁, τ₂][↑i] ∧ (w i).fst ∈ ⟦[τ₁, τ₂][↑i]⟧ᶻ := by
            intro i; exact ⟨rfl, hx_arity.2 i⟩
          have hgo := funAbstractGoPair hgo_cov hcov_a_upd w hw
          have hw0 : w ⟨0, hlen⟩ = W₁ := by
            apply funDomEqOfTyEqAndFstEq _ (by simp [w, ZFSet.get])
            simp only [Fin.zero_eta, Fin.isValue, Fin.getElem_fin, Nat.reduceAdd,
              Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.getElem_cons_zero]
            symm
            exact hW₁_ty
          have hw1 : w ⟨1, by simp⟩ = W₂ := by
            apply funDomEqOfTyEqAndFstEq _ (by simp [w, ZFSet.get])
            simp only [Fin.mk_one, Fin.isValue, Fin.getElem_fin, Nat.reduceAdd,
              Fin.coe_ofNat_eq_mod, Nat.mod_succ, List.getElem_cons_succ, List.getElem_cons_zero]
            symm
            exact hW₂_ty
          have hbody_eq :
              ⟦(SMT.Term.abstract.go a [v₁, v₂] Δctx hgo_cov).uncurry w⟧ˢ = some D := by
            rw [hgo, hw0, hw1]; exact hD
          change (⟦(SMT.Term.abstract.go a [v₁, v₂] Δctx hgo_cov).uncurry w⟧ˢ.get _).fst = zffalse
          simp only [hbody_eq, Option.get_some]; exact hD_false
        · exfalso; apply hx_arity
          exact pair_hasArity_get_mem'
            (by rw [← hW₁_ty]; exact W₁.2.2) (by rw [← hW₂_ty]; exact W₂.2.2)
      · exfalso; apply hsome; exact hbody_total'
    obtain ⟨Φ, _, _⟩ := Φ
    rw [hforall_zffalse, Option.some_inj, PSigma.mk.injEq] at hden_forall
    obtain ⟨rfl, _⟩ := hden_forall
    symm at htrue
    nomatch ZFSet.zftrue_ne_zffalse htrue
  · exact hD_true

private theorem triple_hasArity_get_mem'
    {τ₁ τ₂ τ₃ : SMTType} {x₁ x₂ x₃ : ZFSet}
    (hx₁ : x₁ ∈ ⟦τ₁⟧ᶻ) (hx₂ : x₂ ∈ ⟦τ₂⟧ᶻ) (hx₃ : x₃ ∈ ⟦τ₃⟧ᶻ) :
    ((x₁.pair x₂).pair x₃).hasArity [τ₁, τ₂, τ₃].length ∧
      ∀ i : Fin [τ₁, τ₂, τ₃].length,
        ((x₁.pair x₂).pair x₃).get [τ₁, τ₂, τ₃].length i ∈ ⟦[τ₁, τ₂, τ₃][i]⟧ᶻ := by
  constructor
  · simp [ZFSet.hasArity]
  · intro i
    have hi : i.1 = 0 ∨ i.1 = 1 ∨ i.1 = 2 := by have hi_lt : i.1 < 3 := i.2; omega
    rcases hi with hi | hi | hi
    · have hi' : i = ⟨0, by simp⟩ := Fin.ext hi; rw [hi']; simpa [ZFSet.get] using hx₁
    · have hi' : i = ⟨1, by simp⟩ := Fin.ext hi; rw [hi']; simpa [ZFSet.get] using hx₂
    · have hi' : i = ⟨2, by simp⟩ := Fin.ext hi; rw [hi']; simpa [ZFSet.get] using hx₃

private theorem funAbstractGoTriple.{u}
    {Δctx : SMT.RenamingContext.Context.{u}} {P : SMT.Term} {v₁ v₂ v₃ : SMT.𝒱}
    {τ₁ τ₂ τ₃ : SMTType}
    (hgo_cov : ∀ x ∈ SMT.fv P, x ∉ [v₁, v₂, v₃] → (Δctx x).isSome = true)
    (hcovP :
      ∀ W₁ W₂ W₃ : SMT.Dom.{u},
        RenamingContext.CoversFV
          (Function.update (Function.update (Function.update Δctx v₁ (some W₁)) v₂ (some W₂)) v₃ (some W₃))
          P) :
    ∀ (w : Fin [v₁, v₂, v₃].length → SMT.Dom.{u})
      (hw : ∀ i, (w i).snd.fst = [τ₁, τ₂, τ₃][i] ∧ (w i).fst ∈ ⟦[τ₁, τ₂, τ₃][i]⟧ᶻ),
      (SMT.Term.abstract.go P [v₁, v₂, v₃] Δctx hgo_cov).uncurry w =
        P.abstract
          (Function.update
            (Function.update
              (Function.update Δctx v₁ (some (w ⟨0, by simp⟩)))
              v₂ (some (w ⟨1, by simp⟩)))
            v₃ (some (w ⟨2, by simp⟩)))
          (hcovP (w ⟨0, by simp⟩) (w ⟨1, by simp⟩) (w ⟨2, by simp⟩)) := by
  intro w hw
  have hgo := SMT.Term.abstract.go.alt_def₂
    (vs := [v₁, v₂, v₃]) (P := P) (Δctx := Δctx)
    (αs := List.ofFn w) (vs_αs_len := by simp)
    (Δ_isSome := hgo_cov)
    (tmp₁ := by
      intro x hx
      by_cases hxv : x ∈ [v₁, v₂, v₃]
      · exact Function.updates_isSome_of_mem_map_some Δctx [v₁, v₂, v₃] (List.ofFn w) x hxv (by simp)
      · rw [Function.updates_of_not_mem
          (f := Δctx)
          (xs := [v₁, v₂, v₃]) (ys := (List.ofFn w).map Option.some) (k := x) hxv]
        exact hgo_cov x hx (by simpa using hxv))
  have h_ofFn_list : List.ofFn w = [w ⟨0, by simp⟩, w ⟨1, by simp⟩, w ⟨2, by simp⟩] := rfl
  have h_ofFn :
      (fun i =>
        match i with
        | ⟨j, _⟩ => (List.ofFn w)[j]) = w := by
    funext i
    rcases i with ⟨j, hj⟩
    exact List.getElem_ofFn (f := w) (h := by simpa [h_ofFn_list] using hj)
  simpa [h_ofFn, Function.updates] using hgo

set_option maxHeartbeats 8000000 in
private theorem funTernaryForallEqZftrue.{u}
    {Δctx : SMT.RenamingContext.Context.{u}} {a : SMT.Term} {v₁ v₂ v₃ : SMT.𝒱} {τ₁ τ₂ τ₃ : SMTType}
    (hφ_forall : RenamingContext.CoversFV Δctx (SMT.Term.forall [v₁, v₂, v₃] [τ₁, τ₂, τ₃] a))
    (hgo_cov : ∀ x ∈ SMT.fv a, x ∉ [v₁, v₂, v₃] → (Δctx x).isSome = true)
    (hcov_a_upd :
      ∀ W₁ W₂ W₃ : SMT.Dom.{u},
        RenamingContext.CoversFV
          (Function.update (Function.update (Function.update Δctx v₁ (some W₁)) v₂ (some W₂)) v₃ (some W₃)) a)
    (hbody_total :
      ∀ W₁ W₂ W₃ : SMT.Dom.{u}, W₁.snd.fst = τ₁ → W₂.snd.fst = τ₂ → W₃.snd.fst = τ₃ →
        ⟦a.abstract (Function.update (Function.update (Function.update Δctx v₁ (some W₁)) v₂ (some W₂)) v₃ (some W₃))
          (hcov_a_upd W₁ W₂ W₃)⟧ˢ.isSome = true)
    (hbody_ty :
      ∀ W₁ W₂ W₃ : SMT.Dom.{u}, W₁.snd.fst = τ₁ → W₂.snd.fst = τ₂ → W₃.snd.fst = τ₃ →
        ∀ {D : SMT.Dom.{u}},
          ⟦a.abstract (Function.update (Function.update (Function.update Δctx v₁ (some W₁)) v₂ (some W₂)) v₃ (some W₃))
            (hcov_a_upd W₁ W₂ W₃)⟧ˢ = some D → D.snd.fst = SMTType.bool)
    (hbody_true :
      ∀ W₁ W₂ W₃ : SMT.Dom.{u}, W₁.snd.fst = τ₁ → W₂.snd.fst = τ₂ → W₃.snd.fst = τ₃ →
        ∃ D : SMT.Dom.{u},
          ⟦a.abstract (Function.update (Function.update (Function.update Δctx v₁ (some W₁)) v₂ (some W₂)) v₃ (some W₃))
            (hcov_a_upd W₁ W₂ W₃)⟧ˢ = some D ∧ D.fst = zftrue) :
    ⟦(SMT.Term.forall [v₁, v₂, v₃] [τ₁, τ₂, τ₃] a).abstract Δctx hφ_forall⟧ˢ =
      some ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
  rw [SMT.Term.abstract, dif_pos (by rfl), SMT.denote]
  have hlen : [v₁, v₂, v₃].length > 0 := by simp
  rw [dif_pos hlen]
  have hbody_total' :
      ∀ {x_1 : Fin [v₁, v₂, v₃].length → SMT.Dom.{u}},
        (∀ i,
          ((x_1 i).snd.fst =
              match i with
              | ⟨i, hi⟩ => [τ₁, τ₂, τ₃][i]) ∧
            (x_1 i).fst ∈
              ⟦match i with
                | ⟨i, hi⟩ => [τ₁, τ₂, τ₃][i]⟧ᶻ) →
          ⟦(SMT.Term.abstract.go a [v₁, v₂, v₃] Δctx hgo_cov).uncurry x_1⟧ˢ.isSome = true := by
    intro x_1 hx_1
    have hgo :=
      funAbstractGoTriple
        (Δctx := Δctx) (P := a) (v₁ := v₁) (v₂ := v₂) (v₃ := v₃) (τ₁ := τ₁) (τ₂ := τ₂) (τ₃ := τ₃)
        hgo_cov hcov_a_upd x_1 (by
          intro i
          have hi : i.1 = 0 ∨ i.1 = 1 ∨ i.1 = 2 := by have hi_lt : i.1 < 3 := i.2; omega
          rcases hi with hi | hi | hi
          · have hi' : i = ⟨0, by simp⟩ := Fin.ext hi; cases hi'; simpa using hx_1 ⟨0, by simp⟩
          · have hi' : i = ⟨1, by simp⟩ := Fin.ext hi; cases hi'; simpa using hx_1 ⟨1, by simp⟩
          · have hi' : i = ⟨2, by simp⟩ := Fin.ext hi; cases hi'; simpa using hx_1 ⟨2, by simp⟩)
    rw [hgo]
    let W₁ : SMT.Dom := x_1 ⟨0, by simp⟩
    let W₂ : SMT.Dom := x_1 ⟨1, by simp⟩
    let W₃ : SMT.Dom := x_1 ⟨2, by simp⟩
    have hW₁_ty : W₁.snd.fst = τ₁ := by simpa [W₁] using (hx_1 ⟨0, by simp⟩).1
    have hW₂_ty : W₂.snd.fst = τ₂ := by simpa [W₂] using (hx_1 ⟨1, by simp⟩).1
    have hW₃_ty : W₃.snd.fst = τ₃ := by simpa [W₃] using (hx_1 ⟨2, by simp⟩).1
    simpa [W₁, W₂, W₃] using hbody_total W₁ W₂ W₃ hW₁_ty hW₂_ty hW₃_ty
  split_ifs with hsome
  · apply congrArg some
    apply funDomEqOfTyEqAndFstEq rfl
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_one_sub_one,
      List.getElem_cons_succ, Fin.zero_eta, Fin.isValue,
      List.getElem_cons_zero,
      Option.pure_def, Option.bind_some,
      Fin.foldl_succ_last, Fin.foldl_zero]
    apply sInter_sep_eq_zftrue_of_forall_eq_zftrue
    · -- D = (τ₁.prod τ₂).prod τ₃ (left-nested), so non-emptiness:
      exact ⟨(τ₁.defaultZFSet.pair τ₂.defaultZFSet).pair τ₃.defaultZFSet, by
        rw [ZFSet.pair_mem_prod]
        exact ⟨by rw [ZFSet.pair_mem_prod]
                  exact ⟨SMTType.mem_toZFSet_of_defaultZFSet, SMTType.mem_toZFSet_of_defaultZFSet⟩,
               SMTType.mem_toZFSet_of_defaultZFSet⟩⟩
    · intro x_1 hx_1
      -- D = (τ₁.prod τ₂).prod τ₃, so elements are pair (pair a₀ b₀) c₀
      obtain ⟨ab, hab, c₀, hc₀, habc⟩ := ZFSet.mem_prod.mp hx_1
      obtain ⟨a₀, ha₀, b₀, hb₀, hab_eq⟩ := ZFSet.mem_prod.mp hab
      subst habc; subst hab_eq
      split_ifs with hx_arity_raw
      · let W₁ : SMT.Dom := ⟨a₀, τ₁, ha₀⟩
        let W₂ : SMT.Dom := ⟨b₀, τ₂, hb₀⟩
        let W₃ : SMT.Dom := ⟨c₀, τ₃, hc₀⟩
        obtain ⟨D, hden_body, hD_true⟩ := hbody_true W₁ W₂ W₃ rfl rfl rfl
        let w : Fin 3 → SMT.Dom := fun i =>
          ⟨((a₀.pair b₀).pair c₀).get 3 i, [τ₁, τ₂, τ₃][↑i], hx_arity_raw.2 i⟩
        have hw : ∀ i : Fin [v₁, v₂, v₃].length,
            (w i).snd.fst = [τ₁, τ₂, τ₃][↑i] ∧ (w i).fst ∈ ⟦[τ₁, τ₂, τ₃][↑i]⟧ᶻ := by
          intro i; exact ⟨rfl, hx_arity_raw.2 i⟩
        have hgo := funAbstractGoTriple hgo_cov hcov_a_upd w hw
        have hw0 : w ⟨0, by simp⟩ = W₁ :=
          funDomEqOfTyEqAndFstEq rfl (by simp [w, W₁, ZFSet.get])
        have hw1 : w ⟨1, by simp⟩ = W₂ :=
          funDomEqOfTyEqAndFstEq rfl (by simp [w, W₂, ZFSet.get])
        have hw2 : w ⟨2, by simp⟩ = W₃ :=
          funDomEqOfTyEqAndFstEq rfl (by simp [w, W₃, ZFSet.get])
        have hbody_eq :
            ⟦(SMT.Term.abstract.go a [v₁, v₂, v₃] Δctx hgo_cov).uncurry w⟧ˢ = some D := by
          rw [hgo, hw0, hw1, hw2]; exact hden_body
        change (⟦(SMT.Term.abstract.go a [v₁, v₂, v₃] Δctx hgo_cov).uncurry w⟧ˢ.get _).fst = zftrue
        simp only [hbody_eq, Option.get_some]
        exact hD_true
      · exfalso; apply hx_arity_raw
        exact (triple_hasArity_get_mem' ha₀ hb₀ hc₀)
  · exfalso
    apply hsome
    intro x_1 hx_1
    have hgo :=
      funAbstractGoTriple
        (Δctx := Δctx) (P := a) (v₁ := v₁) (v₂ := v₂) (v₃ := v₃) (τ₁ := τ₁) (τ₂ := τ₂) (τ₃ := τ₃)
        hgo_cov hcov_a_upd x_1 (by
          intro i
          have hi : i.1 = 0 ∨ i.1 = 1 ∨ i.1 = 2 := by have hi_lt : i.1 < 3 := i.2; omega
          rcases hi with hi | hi | hi
          · have hi' : i = ⟨0, by simp⟩ := Fin.ext hi; cases hi'; simpa using hx_1 ⟨0, by simp⟩
          · have hi' : i = ⟨1, by simp⟩ := Fin.ext hi; cases hi'; simpa using hx_1 ⟨1, by simp⟩
          · have hi' : i = ⟨2, by simp⟩ := Fin.ext hi; cases hi'; simpa using hx_1 ⟨2, by simp⟩)
    rw [hgo]
    let W₁ : SMT.Dom := x_1 ⟨0, by simp⟩
    let W₂ : SMT.Dom := x_1 ⟨1, by simp⟩
    let W₃ : SMT.Dom := x_1 ⟨2, by simp⟩
    have hW₁_ty : W₁.snd.fst = τ₁ := by simpa [W₁] using (hx_1 ⟨0, by simp⟩).1
    have hW₂_ty : W₂.snd.fst = τ₂ := by simpa [W₂] using (hx_1 ⟨1, by simp⟩).1
    have hW₃_ty : W₃.snd.fst = τ₃ := by simpa [W₃] using (hx_1 ⟨2, by simp⟩).1
    simpa [W₁, W₂, W₃] using hbody_total W₁ W₂ W₃ hW₁_ty hW₂_ty hW₃_ty

-- Inversion of funTernaryForallEqZftrue: if the ternary forall denotes to zftrue,
-- then each body value is zftrue.
set_option maxHeartbeats 8000000 in
private theorem funTernaryForallTrueAt.{u}
    {Δctx : SMT.RenamingContext.Context.{u}} {a : SMT.Term} {v₁ v₂ v₃ : SMT.𝒱} {τ₁ τ₂ τ₃ : SMTType}
    (hφ_forall : RenamingContext.CoversFV Δctx (SMT.Term.forall [v₁, v₂, v₃] [τ₁, τ₂, τ₃] a))
    (hgo_cov : ∀ x ∈ SMT.fv a, x ∉ [v₁, v₂, v₃] → (Δctx x).isSome = true)
    (hcov_a_upd :
      ∀ W₁ W₂ W₃ : SMT.Dom.{u},
        RenamingContext.CoversFV
          (Function.update (Function.update (Function.update Δctx v₁ (some W₁)) v₂ (some W₂)) v₃ (some W₃)) a)
    (hbody_total :
      ∀ W₁ W₂ W₃ : SMT.Dom.{u}, W₁.snd.fst = τ₁ → W₂.snd.fst = τ₂ → W₃.snd.fst = τ₃ →
        ⟦a.abstract (Function.update (Function.update (Function.update Δctx v₁ (some W₁)) v₂ (some W₂)) v₃ (some W₃))
          (hcov_a_upd W₁ W₂ W₃)⟧ˢ.isSome = true)
    (hbody_ty :
      ∀ W₁ W₂ W₃ : SMT.Dom.{u}, W₁.snd.fst = τ₁ → W₂.snd.fst = τ₂ → W₃.snd.fst = τ₃ →
        ∀ {D : SMT.Dom.{u}},
          ⟦a.abstract (Function.update (Function.update (Function.update Δctx v₁ (some W₁)) v₂ (some W₂)) v₃ (some W₃))
            (hcov_a_upd W₁ W₂ W₃)⟧ˢ = some D → D.snd.fst = SMTType.bool)
    {Φ : SMT.Dom.{u}}
    (hden_forall :
      ⟦(SMT.Term.forall [v₁, v₂, v₃] [τ₁, τ₂, τ₃] a).abstract Δctx hφ_forall⟧ˢ = some Φ)
    (htrue : Φ.fst = zftrue)
    (W₁ W₂ W₃ : SMT.Dom.{u})
    (hW₁_ty : W₁.snd.fst = τ₁) (hW₂_ty : W₂.snd.fst = τ₂) (hW₃_ty : W₃.snd.fst = τ₃) :
    ∃ D : SMT.Dom.{u},
      ⟦a.abstract (Function.update (Function.update (Function.update Δctx v₁ (some W₁)) v₂ (some W₂)) v₃ (some W₃))
        (hcov_a_upd W₁ W₂ W₃)⟧ˢ = some D ∧ D.fst = zftrue := by
  obtain ⟨D, hD⟩ := Option.isSome_iff_exists.mp (hbody_total W₁ W₂ W₃ hW₁_ty hW₂_ty hW₃_ty)
  refine ⟨D, hD, ?_⟩
  have hD_ty := hbody_ty W₁ W₂ W₃ hW₁_ty hW₂_ty hW₃_ty hD
  have hD_mem_𝔹 : D.fst ∈ 𝔹 := by have := D.snd.snd; rwa [hD_ty] at this
  rcases ZFSet.ZFBool.mem_𝔹_iff _ |>.mp hD_mem_𝔹 with hD_false | hD_true
  · exfalso
    have hforall_zffalse :
        ⟦(SMT.Term.forall [v₁, v₂, v₃] [τ₁, τ₂, τ₃] a).abstract Δctx hφ_forall⟧ˢ =
        some ⟨zffalse, SMTType.bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
      rw [SMT.Term.abstract, dif_pos (by rfl), SMT.denote]
      have hlen : [v₁, v₂, v₃].length > 0 := by simp
      rw [dif_pos hlen]
      have hbody_total' :
          ∀ {x_1 : Fin [v₁, v₂, v₃].length → SMT.Dom.{u}},
            (∀ i, ((x_1 i).snd.fst = match i with | ⟨i, hi⟩ => [τ₁, τ₂, τ₃][i]) ∧
              (x_1 i).fst ∈ ⟦match i with | ⟨i, hi⟩ => [τ₁, τ₂, τ₃][i]⟧ᶻ) →
              ⟦(SMT.Term.abstract.go a [v₁, v₂, v₃] Δctx hgo_cov).uncurry x_1⟧ˢ.isSome = true := by
        intro x_1 hx_1
        have hgo :=
          funAbstractGoTriple
            (Δctx := Δctx) (P := a) (v₁ := v₁) (v₂ := v₂) (v₃ := v₃) (τ₁ := τ₁) (τ₂ := τ₂) (τ₃ := τ₃)
            hgo_cov hcov_a_upd x_1 (by
              intro i
              have hi : i.1 = 0 ∨ i.1 = 1 ∨ i.1 = 2 := by have hi_lt : i.1 < 3 := i.2; omega
              rcases hi with hi | hi | hi
              · have hi' : i = ⟨0, by simp⟩ := Fin.ext hi; cases hi'; simpa using hx_1 ⟨0, by simp⟩
              · have hi' : i = ⟨1, by simp⟩ := Fin.ext hi; cases hi'; simpa using hx_1 ⟨1, by simp⟩
              · have hi' : i = ⟨2, by simp⟩ := Fin.ext hi; cases hi'; simpa using hx_1 ⟨2, by simp⟩)
        rw [hgo]
        let W₁' : SMT.Dom := x_1 ⟨0, by simp⟩
        let W₂' : SMT.Dom := x_1 ⟨1, by simp⟩
        let W₃' : SMT.Dom := x_1 ⟨2, by simp⟩
        simpa [W₁', W₂', W₃'] using hbody_total W₁' W₂' W₃'
          (by simpa [W₁'] using (hx_1 ⟨0, by simp⟩).1)
          (by simpa [W₂'] using (hx_1 ⟨1, by simp⟩).1)
          (by simpa [W₃'] using (hx_1 ⟨2, by simp⟩).1)
      split_ifs with hsome
      · apply congrArg some; apply funDomEqOfTyEqAndFstEq rfl
        simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_one_sub_one,
          List.getElem_cons_succ, Fin.zero_eta, Fin.isValue, List.getElem_cons_zero,
          Option.pure_def, Option.bind_some, Fin.foldl_succ_last, Fin.foldl_zero]
        apply sInter_sep_eq_empty_of_exists_eq_empty
        refine ⟨(W₁.fst.pair W₂.fst).pair W₃.fst, by
          rw [ZFSet.pair_mem_prod]
          exact ⟨by rw [ZFSet.pair_mem_prod]
                    exact ⟨by rw [← hW₁_ty]; exact W₁.2.2, by rw [← hW₂_ty]; exact W₂.2.2⟩,
                 by rw [← hW₃_ty]; exact W₃.2.2⟩, ?_⟩
        split_ifs with hx_arity
        · let w : Fin 3 → SMT.Dom := fun i =>
            ⟨((W₁.fst.pair W₂.fst).pair W₃.fst).get 3 i, [τ₁, τ₂, τ₃][↑i], hx_arity.2 i⟩
          have hw : ∀ i : Fin [v₁, v₂, v₃].length,
              (w i).snd.fst = [τ₁, τ₂, τ₃][↑i] ∧ (w i).fst ∈ ⟦[τ₁, τ₂, τ₃][↑i]⟧ᶻ := by
            intro i; exact ⟨rfl, hx_arity.2 i⟩
          have hgo := funAbstractGoTriple hgo_cov hcov_a_upd w hw
          have hw0 : w ⟨0, hlen⟩ = W₁ := by
            apply funDomEqOfTyEqAndFstEq _ (by simp [w, ZFSet.get])
            simp only [Fin.zero_eta, Fin.isValue, Fin.getElem_fin, Nat.reduceAdd,
              Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.getElem_cons_zero]
            symm
            exact hW₁_ty
          have hw1 : w ⟨1, Nat.one_lt_succ_succ 1⟩ = W₂ := by
            apply funDomEqOfTyEqAndFstEq _ (by simp [w, ZFSet.get])
            simp only [Fin.mk_one, Fin.isValue, Fin.getElem_fin, Nat.reduceAdd,
              Fin.coe_ofNat_eq_mod, Nat.one_mod, List.getElem_cons_succ, List.getElem_cons_zero]
            symm
            exact hW₂_ty
          have hw2 : w ⟨2, Nat.lt_add_one 2⟩ = W₃ := by
            apply funDomEqOfTyEqAndFstEq _ (by simp [w, ZFSet.get])
            simp only [Fin.reduceFinMk, Fin.getElem_fin, Fin.isValue, Fin.coe_ofNat_eq_mod,
              Nat.mod_succ, List.getElem_cons_succ, List.getElem_cons_zero]
            symm
            exact hW₃_ty
          have hbody_eq :
              ⟦(SMT.Term.abstract.go a [v₁, v₂, v₃] Δctx hgo_cov).uncurry w⟧ˢ = some D := by
            rw [hgo, hw0, hw1, hw2]; exact hD
          change (⟦(SMT.Term.abstract.go a [v₁, v₂, v₃] Δctx hgo_cov).uncurry w⟧ˢ.get _).fst = zffalse
          simp only [hbody_eq, Option.get_some]; exact hD_false
        · exfalso; apply hx_arity
          exact triple_hasArity_get_mem'
            (by rw [← hW₁_ty]; exact W₁.2.2) (by rw [← hW₂_ty]; exact W₂.2.2)
            (by rw [← hW₃_ty]; exact W₃.2.2)
      · exfalso; apply hsome; exact hbody_total'
    obtain ⟨Φ, _, _⟩ := Φ
    rw [hforall_zffalse, Option.some_inj, PSigma.mk.injEq] at hden_forall
    obtain ⟨rfl, _⟩ := hden_forall
    symm at htrue
    nomatch ZFSet.zftrue_ne_zffalse htrue
  · exact hD_true

private theorem denote_and_extract_left
    {p q : SMT.PHOAS.Term SMT.Dom} {D : SMT.Dom}
    (hden : ⟦p ∧ˢ' q⟧ˢ = some D) :
    ∃ Dp : SMT.Dom, ⟦p⟧ˢ = some Dp ∧ Dp.snd.fst = .bool := by
  -- p ∧ˢ' q = not (not p ∨ˢ not q) ... actually and is direct in SMT.denote
  -- The and denotation: ⟦p⟧ˢ >>= fun ⟨P, .bool, hP⟩ => ⟦q⟧ˢ >>= fun ⟨Q, .bool, hQ⟩ => ...
  -- If the result is some D, then ⟦p⟧ˢ must have succeeded with type .bool
  simp only [SMT.denote, Option.bind_eq_bind] at hden
  match hp : ⟦p⟧ˢ with
  | none => simp [hp] at hden
  | some ⟨P, .bool, hP⟩ => exact ⟨⟨P, .bool, hP⟩, rfl, rfl⟩
  | some ⟨P, .int, hP⟩ => simp [hp] at hden
  | some ⟨P, .unit, hP⟩ => simp [hp] at hden
  | some ⟨P, .fun _ _, hP⟩ => simp [hp] at hden
  | some ⟨P, .option _, hP⟩ => simp [hp] at hden
  | some ⟨P, .pair _ _, hP⟩ => simp [hp] at hden

private theorem denote_and_extract_right
    {p q : SMT.PHOAS.Term SMT.Dom} {D : SMT.Dom}
    (hden : ⟦p ∧ˢ' q⟧ˢ = some D) :
    ∃ Dq : SMT.Dom, ⟦q⟧ˢ = some Dq ∧ Dq.snd.fst = .bool := by
  obtain ⟨Dp, hDp, hDp_ty⟩ := denote_and_extract_left hden
  simp only [SMT.denote, Option.bind_eq_bind, hDp] at hden
  obtain ⟨dp, τp, hdp⟩ := Dp; cases hDp_ty
  simp only [Option.bind_some] at hden
  match hq : ⟦q⟧ˢ with
  | none => simp [hq] at hden
  | some ⟨Q, .bool, hQ⟩ => exact ⟨⟨Q, .bool, hQ⟩, rfl, rfl⟩
  | some ⟨Q, .int, hQ⟩ => simp [hq] at hden
  | some ⟨Q, .unit, hQ⟩ => simp [hq] at hden
  | some ⟨Q, .fun _ _, hQ⟩ => simp [hq] at hden
  | some ⟨Q, .option _, hQ⟩ => simp [hq] at hden
  | some ⟨Q, .pair _ _, hQ⟩ => simp [hq] at hden

set_option maxHeartbeats 4000000 in
/--
The pfun lambda `λ R. (∀ x y. R(⟨x,y⟩) ⇒ A_enc(x) ∧ B_enc(y)) ∧ (∀ x y y'. R(⟨x,y⟩) ∧ R(⟨x,y'⟩) ⇒ y = y')`
denotes under any renaming context that covers fv(A_enc) and fv(B_enc), and its retract equals
`𝒫(X × Y) ∩ {f | f.IsPFunc X Y}` where X = retract(αx.set, Aenc), Y = retract(βx.set, Benc).
-/
private theorem pfun_lambda_denotation.{u}
    {αx βx : BType}
    {A_enc B_enc : SMT.Term}
    {R x y y' : SMT.𝒱}
    {Δctx : SMT.RenamingContext.Context}
    {den_A den_B : SMT.Dom.{u}}
    (hcov_A : RenamingContext.CoversFV Δctx A_enc)
    (hcov_B : RenamingContext.CoversFV Δctx B_enc)
    (h_den_A : ⟦A_enc.abstract Δctx hcov_A⟧ˢ = some den_A)
    (h_den_B : ⟦B_enc.abstract Δctx hcov_B⟧ˢ = some den_B)
    (den_A_type : den_A.2.1 = .fun αx.toSMTType .bool)
    (den_B_type : den_B.2.1 = .fun βx.toSMTType .bool)
    (R_not_fv_A : R ∉ SMT.fv A_enc) (R_not_fv_B : R ∉ SMT.fv B_enc)
    (x_not_fv_A : x ∉ SMT.fv A_enc) (x_not_fv_B : x ∉ SMT.fv B_enc)
    (y_not_fv_A : y ∉ SMT.fv A_enc) (y_not_fv_B : y ∉ SMT.fv B_enc)
    (y'_not_fv_A : y' ∉ SMT.fv A_enc) (y'_not_fv_B : y' ∉ SMT.fv B_enc)
    (hR_ne_x : R ≠ x) (hR_ne_y : R ≠ y) (hR_ne_y' : R ≠ y')
    (hx_ne_y : x ≠ y) (hx_ne_y' : x ≠ y') (hy_ne_y' : y ≠ y')
    -- Typing parameters for denote_exists_of_typing_fv
    {Γ : SMT.TypeContext}
    (htyp_A : Γ ⊢ˢ A_enc : SMTType.fun αx.toSMTType .bool)
    (htyp_B : Γ ⊢ˢ B_enc : SMTType.fun βx.toSMTType .bool)
    (R_not_in_Γ : R ∉ Γ) (x_not_in_Γ : x ∉ Γ) (y_not_in_Γ : y ∉ Γ) (y'_not_in_Γ : y' ∉ Γ)
    (hcov : RenamingContext.CoversFV Δctx
      (Term.lambda [R] [SMTType.fun (SMTType.pair αx.toSMTType βx.toSMTType) .bool]
        (.and
          (.forall [x, y] [αx.toSMTType, βx.toSMTType]
            (.imp (.app (.var R) (.pair (.var x) (.var y)))
              (.and (.app A_enc (.var x)) (.app B_enc (.var y)))))
          (.forall [x, y, y'] [αx.toSMTType, βx.toSMTType, βx.toSMTType]
            (.imp
              (.and (.app (.var R) (.pair (.var x) (.var y)))
                    (.app (.var R) (.pair (.var x) (.var y'))))
              (.eq (.var y) (.var y'))))))) :
    let τR := SMTType.fun (SMTType.pair αx.toSMTType βx.toSMTType) .bool
    let pfun_body :=
      Term.and
        (.forall [x, y] [αx.toSMTType, βx.toSMTType]
          (.imp (.app (.var R) (.pair (.var x) (.var y)))
            (.and (.app A_enc (.var x)) (.app B_enc (.var y)))))
        (.forall [x, y, y'] [αx.toSMTType, βx.toSMTType, βx.toSMTType]
          (.imp
            (.and (.app (.var R) (.pair (.var x) (.var y)))
                  (.app (.var R) (.pair (.var x) (.var y'))))
            (.eq (.var y) (.var y'))))
    ∃ den_t : SMT.Dom.{u},
      ⟦(Term.lambda [R] [τR] pfun_body).abstract Δctx hcov⟧ˢ = some den_t ∧
      den_t.2.1 = τR.fun .bool ∧
      retract (BType.set (BType.set (BType.prod αx βx))) den_t.1 =
        ((retract (BType.set αx) den_A.1).prod (retract (BType.set βx) den_B.1)).powerset.sep
          (fun f => f.IsPFunc (retract (BType.set αx) den_A.1) (retract (BType.set βx) den_B.1)) := by
  -- Abbreviations
  set τR := SMTType.fun (SMTType.pair αx.toSMTType βx.toSMTType) .bool with hτR_def
  set pfun_body :=
    Term.and
      (.forall [x, y] [αx.toSMTType, βx.toSMTType]
        (.imp (.app (.var R) (.pair (.var x) (.var y)))
          (.and (.app A_enc (.var x)) (.app B_enc (.var y)))))
      (.forall [x, y, y'] [αx.toSMTType, βx.toSMTType, βx.toSMTType]
        (.imp
          (.and (.app (.var R) (.pair (.var x) (.var y)))
                (.app (.var R) (.pair (.var x) (.var y'))))
          (.eq (.var y) (.var y')))) with hpfun_body_def
  -- IsFunc proofs for A_enc and B_enc
  have hdenA_func : ZFSet.IsFunc ⟦αx.toSMTType⟧ᶻ 𝔹 den_A.1 := by
    have hdenA_mem : den_A.1 ∈ ⟦αx.toSMTType⟧ᶻ.funs 𝔹 := by
      simpa [den_A_type, SMTType.toZFSet] using den_A.2.2
    exact ZFSet.mem_funs.mp hdenA_mem
  have hdenB_func : ZFSet.IsFunc ⟦βx.toSMTType⟧ᶻ 𝔹 den_B.1 := by
    have hdenB_mem : den_B.1 ∈ ⟦βx.toSMTType⟧ᶻ.funs 𝔹 := by
      simpa [den_B_type, SMTType.toZFSet] using den_B.2.2
    exact ZFSet.mem_funs.mp hdenB_mem
  -- CoversFV invariance: A_enc and B_enc under updates of R, x, y, y'
  -- A_enc is invariant under R, x, y, y' updates
  have hcov_A_updR : ∀ WR : SMT.Dom,
      RenamingContext.CoversFV (Function.update Δctx R (some WR)) A_enc :=
    fun WR => SMT.RenamingContext.coversFV_update_of_notMem R_not_fv_A hcov_A
  have hcov_A_updRx : ∀ WR Wx : SMT.Dom,
      RenamingContext.CoversFV (Function.update (Function.update Δctx R (some WR)) x (some Wx)) A_enc :=
    fun WR Wx => SMT.RenamingContext.coversFV_update_of_notMem x_not_fv_A (hcov_A_updR WR)
  have hcov_A_updRxy : ∀ WR Wx Wy : SMT.Dom,
      RenamingContext.CoversFV (Function.update (Function.update (Function.update Δctx R (some WR)) x (some Wx)) y (some Wy)) A_enc :=
    fun WR Wx Wy => SMT.RenamingContext.coversFV_update_of_notMem y_not_fv_A (hcov_A_updRx WR Wx)
  have hcov_A_updRxy' : ∀ WR Wx Wy Wy' : SMT.Dom,
      RenamingContext.CoversFV (Function.update (Function.update (Function.update (Function.update Δctx R (some WR)) x (some Wx)) y (some Wy)) y' (some Wy')) A_enc :=
    fun WR Wx Wy Wy' => SMT.RenamingContext.coversFV_update_of_notMem y'_not_fv_A (hcov_A_updRxy WR Wx Wy)
  -- B_enc similarly
  have hcov_B_updR : ∀ WR : SMT.Dom,
      RenamingContext.CoversFV (Function.update Δctx R (some WR)) B_enc :=
    fun WR => SMT.RenamingContext.coversFV_update_of_notMem R_not_fv_B hcov_B
  have hcov_B_updRx : ∀ WR Wx : SMT.Dom,
      RenamingContext.CoversFV (Function.update (Function.update Δctx R (some WR)) x (some Wx)) B_enc :=
    fun WR Wx => SMT.RenamingContext.coversFV_update_of_notMem x_not_fv_B (hcov_B_updR WR)
  have hcov_B_updRxy : ∀ WR Wx Wy : SMT.Dom,
      RenamingContext.CoversFV (Function.update (Function.update (Function.update Δctx R (some WR)) x (some Wx)) y (some Wy)) B_enc :=
    fun WR Wx Wy => SMT.RenamingContext.coversFV_update_of_notMem y_not_fv_B (hcov_B_updRx WR Wx)
  have hcov_B_updRxy' : ∀ WR Wx Wy Wy' : SMT.Dom,
      RenamingContext.CoversFV (Function.update (Function.update (Function.update (Function.update Δctx R (some WR)) x (some Wx)) y (some Wy)) y' (some Wy')) B_enc :=
    fun WR Wx Wy Wy' => SMT.RenamingContext.coversFV_update_of_notMem y'_not_fv_B (hcov_B_updRxy WR Wx Wy)
  -- Denotation invariance: A_enc and B_enc under updates
  have den_A_updR : ∀ WR : SMT.Dom,
      ⟦A_enc.abstract (Function.update Δctx R (some WR)) (hcov_A_updR WR)⟧ˢ = some den_A := by
    intro WR
    have : ⟦A_enc.abstract Δctx hcov_A⟧ˢ =
        ⟦A_enc.abstract (Function.update Δctx R (some WR)) (hcov_A_updR WR)⟧ˢ := by
      rw [←SMT.RenamingContext.denote, ←SMT.RenamingContext.denote]
      exact SMT.RenamingContext.denote_update_of_notMem R_not_fv_A
    rw [←this]; exact h_den_A
  have den_A_updRx : ∀ WR Wx : SMT.Dom,
      ⟦A_enc.abstract (Function.update (Function.update Δctx R (some WR)) x (some Wx)) (hcov_A_updRx WR Wx)⟧ˢ = some den_A := by
    intro WR Wx
    have : ⟦A_enc.abstract (Function.update Δctx R (some WR)) (hcov_A_updR WR)⟧ˢ =
        ⟦A_enc.abstract (Function.update (Function.update Δctx R (some WR)) x (some Wx)) (hcov_A_updRx WR Wx)⟧ˢ := by
      rw [←SMT.RenamingContext.denote, ←SMT.RenamingContext.denote]
      exact SMT.RenamingContext.denote_update_of_notMem x_not_fv_A
    rw [←this]; exact den_A_updR WR
  have den_A_updRxy : ∀ WR Wx Wy : SMT.Dom,
      ⟦A_enc.abstract (Function.update (Function.update (Function.update Δctx R (some WR)) x (some Wx)) y (some Wy)) (hcov_A_updRxy WR Wx Wy)⟧ˢ = some den_A := by
    intro WR Wx Wy
    have : ⟦A_enc.abstract (Function.update (Function.update Δctx R (some WR)) x (some Wx)) (hcov_A_updRx WR Wx)⟧ˢ =
        ⟦A_enc.abstract (Function.update (Function.update (Function.update Δctx R (some WR)) x (some Wx)) y (some Wy)) (hcov_A_updRxy WR Wx Wy)⟧ˢ := by
      rw [←SMT.RenamingContext.denote, ←SMT.RenamingContext.denote]
      exact SMT.RenamingContext.denote_update_of_notMem y_not_fv_A
    rw [←this]; exact den_A_updRx WR Wx
  have den_A_updRxy' : ∀ WR Wx Wy Wy' : SMT.Dom,
      ⟦A_enc.abstract (Function.update (Function.update (Function.update (Function.update Δctx R (some WR)) x (some Wx)) y (some Wy)) y' (some Wy')) (hcov_A_updRxy' WR Wx Wy Wy')⟧ˢ = some den_A := by
    intro WR Wx Wy Wy'
    have : ⟦A_enc.abstract (Function.update (Function.update (Function.update Δctx R (some WR)) x (some Wx)) y (some Wy)) (hcov_A_updRxy WR Wx Wy)⟧ˢ =
        ⟦A_enc.abstract (Function.update (Function.update (Function.update (Function.update Δctx R (some WR)) x (some Wx)) y (some Wy)) y' (some Wy')) (hcov_A_updRxy' WR Wx Wy Wy')⟧ˢ := by
      rw [←SMT.RenamingContext.denote, ←SMT.RenamingContext.denote]
      exact SMT.RenamingContext.denote_update_of_notMem y'_not_fv_A
    rw [←this]; exact den_A_updRxy WR Wx Wy
  have den_B_updR : ∀ WR : SMT.Dom,
      ⟦B_enc.abstract (Function.update Δctx R (some WR)) (hcov_B_updR WR)⟧ˢ = some den_B := by
    intro WR
    have : ⟦B_enc.abstract Δctx hcov_B⟧ˢ =
        ⟦B_enc.abstract (Function.update Δctx R (some WR)) (hcov_B_updR WR)⟧ˢ := by
      rw [←SMT.RenamingContext.denote, ←SMT.RenamingContext.denote]
      exact SMT.RenamingContext.denote_update_of_notMem R_not_fv_B
    rw [←this]; exact h_den_B
  have den_B_updRx : ∀ WR Wx : SMT.Dom,
      ⟦B_enc.abstract (Function.update (Function.update Δctx R (some WR)) x (some Wx)) (hcov_B_updRx WR Wx)⟧ˢ = some den_B := by
    intro WR Wx
    have : ⟦B_enc.abstract (Function.update Δctx R (some WR)) (hcov_B_updR WR)⟧ˢ =
        ⟦B_enc.abstract (Function.update (Function.update Δctx R (some WR)) x (some Wx)) (hcov_B_updRx WR Wx)⟧ˢ := by
      rw [←SMT.RenamingContext.denote, ←SMT.RenamingContext.denote]
      exact SMT.RenamingContext.denote_update_of_notMem x_not_fv_B
    rw [←this]; exact den_B_updR WR
  have den_B_updRxy : ∀ WR Wx Wy : SMT.Dom,
      ⟦B_enc.abstract (Function.update (Function.update (Function.update Δctx R (some WR)) x (some Wx)) y (some Wy)) (hcov_B_updRxy WR Wx Wy)⟧ˢ = some den_B := by
    intro WR Wx Wy
    have : ⟦B_enc.abstract (Function.update (Function.update Δctx R (some WR)) x (some Wx)) (hcov_B_updRx WR Wx)⟧ˢ =
        ⟦B_enc.abstract (Function.update (Function.update (Function.update Δctx R (some WR)) x (some Wx)) y (some Wy)) (hcov_B_updRxy WR Wx Wy)⟧ˢ := by
      rw [←SMT.RenamingContext.denote, ←SMT.RenamingContext.denote]
      exact SMT.RenamingContext.denote_update_of_notMem y_not_fv_B
    rw [←this]; exact den_B_updRx WR Wx
  have den_B_updRxy' : ∀ WR Wx Wy Wy' : SMT.Dom,
      ⟦B_enc.abstract (Function.update (Function.update (Function.update (Function.update Δctx R (some WR)) x (some Wx)) y (some Wy)) y' (some Wy')) (hcov_B_updRxy' WR Wx Wy Wy')⟧ˢ = some den_B := by
    intro WR Wx Wy Wy'
    have : ⟦B_enc.abstract (Function.update (Function.update (Function.update Δctx R (some WR)) x (some Wx)) y (some Wy)) (hcov_B_updRxy WR Wx Wy)⟧ˢ =
        ⟦B_enc.abstract (Function.update (Function.update (Function.update (Function.update Δctx R (some WR)) x (some Wx)) y (some Wy)) y' (some Wy')) (hcov_B_updRxy' WR Wx Wy Wy')⟧ˢ := by
      rw [←SMT.RenamingContext.denote, ←SMT.RenamingContext.denote]
      exact SMT.RenamingContext.denote_update_of_notMem y'_not_fv_B
    rw [←this]; exact den_B_updRxy WR Wx Wy
  -- Abbreviations for the two forall parts of the body
  set P1 := Term.forall [x, y] [αx.toSMTType, βx.toSMTType]
    (.imp (.app (.var R) (.pair (.var x) (.var y)))
      (.and (.app A_enc (.var x)) (.app B_enc (.var y)))) with hP1_def
  set P2 := Term.forall [x, y, y'] [αx.toSMTType, βx.toSMTType, βx.toSMTType]
    (.imp
      (.and (.app (.var R) (.pair (.var x) (.var y)))
            (.app (.var R) (.pair (.var x) (.var y'))))
      (.eq (.var y) (.var y'))) with hP2_def
  -- Helper: for any valid R, app (var R) (pair (var x) (var y)) denotes as fapply
  -- when R is a function from pairs to bools
  -- The inner imp body is a boolean for all valid inputs
  -- We need to show the whole pfun_body = and P1 P2 denotes for valid R as a boolean.
  -- The main conclusion: construct the lambda denotation using the classical bodyFun approach
  -- from castUnion_denotation_direct.
  -- Since the full denotation proof is very deep (outer lambda + two foralls + imp + and + eq),
  -- we use a modular approach:
  -- First, we establish that pfun_body denotes for each valid R, with type .bool.
  -- Then, we assemble the lambda.
  -- Then, we prove the retract equality.
  -- For the body denotation, we need:
  -- 1. P1 denotes with type .bool (forall over imp pattern => sInter)
  -- 2. P2 denotes with type .bool (forall over imp pattern => sInter)
  -- 3. and P1 P2 denotes with type .bool
  -- The retract equality connects the lambda's value to the IsPFunc condition.
  -- Step: CoversFV for pfun_body under R update
  have hcov_body_updR : ∀ WR : SMT.Dom,
      RenamingContext.CoversFV (Function.update Δctx R (some WR)) pfun_body := by
    intro WR v hv
    by_cases hvR : v = R
    · subst hvR; simp [Function.update]
    · rw [Function.update_of_ne hvR]
      -- v ∈ fv pfun_body and v ≠ R, so v ∈ fv(lambda [R] [τR] pfun_body)
      have hv_lambda : v ∈ SMT.fv (Term.lambda [R] [τR] pfun_body) := by
        rw [SMT.fv]
        exact List.mem_filter.mpr ⟨hv, by simp [List.mem_singleton]; exact hvR⟩
      exact hcov v hv_lambda
  -- For the body denotation: we need that pfun_body denotes for each valid R, with type .bool,
  -- and we need to track the VALUE of the denotation to connect it to IsPFunc.
  --
  -- The body is: and P1 P2 where
  -- P1 = forall [x,y] ... (imp (app R (pair x y)) (and (app A_enc x) (app B_enc y)))
  -- P2 = forall [x,y,y'] ... (imp (and (app R (pair x y)) (app R (pair x y'))) (eq y y'))
  --
  -- We establish the body denotation by building the imp inner terms step by step.
  --
  -- The imp denotation: imp t₁ t₂ = not(t₁ ∧ not t₂)
  -- If t₁ = zftrue and t₂ = zftrue → imp = not(true ∧ false) = not(false) = zftrue
  -- If t₁ = zftrue and t₂ = zffalse → imp = not(true ∧ true) = not(true) = zffalse
  -- If t₁ = zffalse → imp = not(false ∧ _) = not(false) = zftrue
  -- i.e., imp is zftrue ↔ t₁ = zffalse ∨ t₂ = zftrue
  --
  -- For the outer lambda to denote, we need:
  -- 1. Body denotes for all valid R inputs
  -- 2. Body type is deterministic (.bool)
  --
  -- We'll compute this indirectly through the forall semantics.
  -- First, let's set up abbreviations for the pair type domain.
  set pairTy := SMTType.pair αx.toSMTType βx.toSMTType with hpairTy_def
  -- Body denotation totality and type + value tracking
  -- For a valid R, the pfun_body value is:
  -- zftrue ↔ (∀ pair in ⟦pairTy⟧ᶻ, R(pair)=true → A(π₁ pair)=true ∧ B(π₂ pair)=true)
  --          ∧ (∀ pair₁ pair₂ in ⟦pairTy⟧ᶻ, R(pair₁)=true ∧ R(pair₂)=true ∧ π₁(pair₁)=π₁(pair₂) → π₂(pair₁)=π₂(pair₂))
  -- CoversFV for pfun_body_upd already established.
  -- We now establish that pfun_body denotes with type .bool for any valid WR.
  -- We use: if the body of the forall denotes for all valid inputs, then the forall denotes.
  -- The forall denotation is: sInter { body_value(inputs) | inputs ∈ D }
  -- which is zftrue iff ∀ inputs, body_value(inputs) = zftrue.
  -- Step: establish go_cov for pfun_body.abstract under R update
  have hgo_cov_body : ∀ v ∈ SMT.fv pfun_body, v ∉ [R] → (Δctx v).isSome = true := by
    intro v hv hvR
    have hvR' : v ≠ R := by simpa [List.mem_singleton] using hvR
    have hv_lambda : v ∈ SMT.fv (Term.lambda [R] [τR] pfun_body) := by
      rw [SMT.fv]
      exact List.mem_filter.mpr ⟨hv, by simp [List.mem_singleton]; exact hvR'⟩
    exact hcov v hv_lambda
  -- Body denotation: for each valid WR, pfun_body denotes with type .bool
  -- AND we track the value relationship.
  -- Body denotation: totality and type .bool.
  -- pfun_body = and P1 P2, where P1 and P2 are forall terms.
  -- Each forall's inner body consists of app/pair/imp/and/eq over boolean-valued terms,
  -- so the body always denotes as a boolean for any valid R input.
  -- We prove both totality and type together, then split.
  -- Helper: for each valid WR, app A_enc (var x) denotes under Rxy context
  have den_app_A_x : ∀ (WR Wx : SMT.Dom) (hWx_ty : Wx.2.1 = αx.toSMTType)
      (hWx_mem : Wx.1 ∈ ⟦αx.toSMTType⟧ᶻ),
      ∃ hcov_app : RenamingContext.CoversFV (Function.update (Function.update Δctx R (some WR)) x (some Wx))
          (.app A_enc (.var x)),
        ∃ DA : SMT.Dom,
          DA.2.1 = .bool ∧
          DA.1 = ZFSet.fapply den_A.1 (ZFSet.is_func_is_pfunc hdenA_func)
            ⟨Wx.1, by rw [ZFSet.is_func_dom_eq hdenA_func]; exact hWx_mem⟩ ∧
          ⟦(Term.app A_enc (.var x)).abstract (Function.update (Function.update Δctx R (some WR)) x (some Wx))
            hcov_app⟧ˢ = some DA := by
    intro WR Wx hWx_ty hWx_mem
    exact funDenoteAppAt
      (Δctx := Function.update Δctx R (some WR))
      (t := A_enc) (x := x)
      (α := αx.toSMTType) (β := .bool) (Y := den_A)
      (hcov_t_upd := hcov_A_updRx WR)
      (den_t_upd := den_A_updRx WR)
      (hY_ty := den_A_type) (hY_func := hdenA_func)
      Wx hWx_ty hWx_mem
  -- Helper: app B_enc (var y) denotes under Rxy context
  have den_app_B_y : ∀ (WR Wx Wy : SMT.Dom) (hWy_ty : Wy.2.1 = βx.toSMTType)
      (hWy_mem : Wy.1 ∈ ⟦βx.toSMTType⟧ᶻ),
      ∃ hcov_app : RenamingContext.CoversFV
          (Function.update (Function.update (Function.update Δctx R (some WR)) x (some Wx)) y (some Wy))
          (.app B_enc (.var y)),
        ∃ DB : SMT.Dom,
          DB.2.1 = .bool ∧
          DB.1 = ZFSet.fapply den_B.1 (ZFSet.is_func_is_pfunc hdenB_func)
            ⟨Wy.1, by rw [ZFSet.is_func_dom_eq hdenB_func]; exact hWy_mem⟩ ∧
          ⟦(Term.app B_enc (.var y)).abstract
            (Function.update (Function.update (Function.update Δctx R (some WR)) x (some Wx)) y (some Wy))
            hcov_app⟧ˢ = some DB := by
    intro WR Wx Wy hWy_ty hWy_mem
    exact funDenoteAppAt
      (Δctx := Function.update (Function.update Δctx R (some WR)) x (some Wx))
      (t := B_enc) (x := y)
      (α := βx.toSMTType) (β := .bool) (Y := den_B)
      (hcov_t_upd := hcov_B_updRxy WR Wx)
      (den_t_upd := den_B_updRxy WR Wx)
      (hY_ty := den_B_type) (hY_func := hdenB_func)
      Wy hWy_ty hWy_mem
  -- Combined body existence: pfun_body denotes with type .bool under Δctx[R:=WR].
  -- pfun_body = and P1 P2 where P1 and P2 are foralls whose inner bodies
  -- are composed of app/pair/imp/and/eq over well-typed terms.
  -- We show each forall's inner body denotes for all valid inputs (totality),
  -- from which the forall denotes (type .bool), then and of two booleans denotes (.bool).
  --
  -- For the imp body of P1 under Δctx[R:=WR][x:=Wx][y:=Wy]:
  -- imp = not(P ∧ not Q), both P and Q are booleans (from app denotations), so imp denotes as bool.
  -- For the imp body of P2 under Δctx[R:=WR][x:=Wx][y:=Wy][y':=Wy']:
  -- similarly, and(app R (pair x y), app R (pair x y')) denotes as bool,
  -- eq(var y, var y') denotes as bool, so imp denotes as bool.
  --
  -- The helper den_app_A_x gives app A_enc (var x) under [R:=WR][x:=Wx].
  -- The helper den_app_B_y gives app B_enc (var y) under [R:=WR][x:=Wx][y:=Wy].
  -- For app (var R) (pair (var x) (var y)), we compute directly since R is a characteristic pred.
  --
  -- We establish imp body totality for each forall, then use the forall denote rule
  -- (dif_pos for n>0 and split_ifs for isSome), then combine with and.
  have hbody_exists : ∀ (WR : SMT.Dom), WR.2.1 = τR →
      ∃ D : SMT.Dom,
        ⟦pfun_body.abstract (Function.update Δctx R (some WR)) (hcov_body_updR WR)⟧ˢ = some D ∧
        D.2.1 = .bool := by
    intro WR hWR_ty
    -- pfun_body = and P1 P2, so pfun_body.abstract unfolds to and of the two abstractions.
    -- We need to show P1 and P2 each denote as booleans, then and gives boolean.
    -- CoversFV for P1 and P2 under R-update
    have hcov_P1 : RenamingContext.CoversFV (Function.update Δctx R (some WR)) P1 :=
      fun v hv => hcov_body_updR WR v (by rw [hpfun_body_def]; exact SMT.fv.mem_and (Or.inl hv))
    have hcov_P2 : RenamingContext.CoversFV (Function.update Δctx R (some WR)) P2 :=
      fun v hv => hcov_body_updR WR v (by rw [hpfun_body_def]; exact SMT.fv.mem_and (Or.inr hv))
    -- Prove body existence via denote_exists_of_typing_fv on pfun_body
    set Γ_R := Γ.insert R τR
    have hΓ_sub : Γ.entries ⊆ Γ_R.entries := TypeContext.entries_subset_insert_of_notMem R_not_in_Γ
    have typ_A_R : Γ_R ⊢ˢ A_enc : .fun αx.toSMTType .bool := Typing.weakening hΓ_sub htyp_A
    have typ_B_R : Γ_R ⊢ˢ B_enc : .fun βx.toSMTType .bool := Typing.weakening hΓ_sub htyp_B
    have x_not_in_ΓR : x ∉ Γ_R := by
      intro h; rw [AList.mem_insert] at h
      rcases h with rfl | h; exact hR_ne_x.symm rfl; exact x_not_in_Γ h
    have y_not_in_ΓR : y ∉ Γ_R := by
      intro h; rw [AList.mem_insert] at h
      rcases h with rfl | h; exact hR_ne_y.symm rfl; exact y_not_in_Γ h
    have y'_not_in_ΓR : y' ∉ Γ_R := by
      intro h; rw [AList.mem_insert] at h
      rcases h with rfl | h; exact hR_ne_y'.symm rfl; exact y'_not_in_Γ h
    have hcompat_body : SMT.RenamingContext.RespectsTypeContextOnFV
        (Function.update Δctx R (some WR)) Γ_R pfun_body := by
      intro v σ hv_fv hlookup
      by_cases hvR : v = R
      · subst hvR; rw [AList.lookup_insert] at hlookup; cases hlookup
        exact ⟨WR, by simp [Function.update], hWR_ty⟩
      · rw [Function.update_of_ne hvR, AList.lookup_insert_ne hvR] at *
        have hv_isSome := hcov_body_updR WR v hv_fv
        rw [Function.update_of_ne hvR] at hv_isSome
        obtain ⟨dv, hdv⟩ := Option.isSome_iff_exists.mp hv_isSome
        have hcov_var : SMT.RenamingContext.CoversFV Δctx (.var v) := by
          intro w hw; simp [SMT.fv] at hw; subst hw; rw [hdv]; simp
        have hden_var : ⟦(SMT.Term.var v).abstract Δctx hcov_var⟧ˢ = some dv := by
          simp [SMT.Term.abstract, SMT.denote, hdv, Option.pure_def]
        exact ⟨dv, hdv, denote_type_eq_of_typing (SMT.Typing.var Γ v σ hlookup) hden_var⟩
    -- Build typing derivation for pfun_body
    have typ_pfun_body : Γ_R ⊢ˢ pfun_body : .bool := by
      rw [hpfun_body_def]
      apply SMT.Typing.and
      · -- P1 typing
        rw [hP1_def]
        refine SMT.Typing.forall Γ_R [x, y] [αx.toSMTType, βx.toSMTType] _ ?_ ?_ (by simp) rfl ?_
        · intro v hv
          rcases List.mem_cons.mp hv with rfl | hv'
          · exact x_not_in_ΓR
          · rcases List.mem_cons.mp hv' with rfl | h
            · exact y_not_in_ΓR
            · exact absurd h (by simp)
        · intro v hv hbv
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
          simp only [SMT.bv, List.mem_append, List.mem_nil_iff, false_or, or_false] at hbv
          have hv_not_in_ΓR : v ∉ Γ_R := by
            rcases hv with rfl | rfl; exact x_not_in_ΓR; exact y_not_in_ΓR
          have hv_typ_A : (Γ_R.insert v αx.toSMTType) ⊢ˢ A_enc : .fun αx.toSMTType .bool :=
            Typing.weakening (TypeContext.entries_subset_insert_of_notMem hv_not_in_ΓR) typ_A_R
          have hv_typ_B : (Γ_R.insert v αx.toSMTType) ⊢ˢ B_enc : .fun βx.toSMTType .bool :=
            Typing.weakening (TypeContext.entries_subset_insert_of_notMem hv_not_in_ΓR) typ_B_R
          have hv_in : v ∈ (Γ_R.insert v αx.toSMTType) := by
            rw [AList.mem_insert]; exact Or.inl rfl
          rcases hbv with hb | hb
          · exact Typing.bv_notMem_context hv_typ_A v hb hv_in
          · exact Typing.bv_notMem_context hv_typ_B v hb hv_in
        · have hupdate_xy : TypeContext.update Γ_R [x, y] [αx.toSMTType, βx.toSMTType] rfl =
              ((Γ_R.insert x αx.toSMTType).insert y βx.toSMTType) := by
            simp only [TypeContext.update, List.length_cons, List.length_nil, zero_add,
              Fin.foldl_succ_last, Fin.getElem_fin, Fin.coe_cast, Fin.val_last,
              List.getElem_append_right, Nat.sub_self, List.getElem_cons_zero,
              Fin.coe_castSucc, Fin.foldl_zero]; rfl
          rw [hupdate_xy]
          have hΓRxy_sub : Γ_R.entries ⊆ ((Γ_R.insert x αx.toSMTType).insert y βx.toSMTType).entries :=
            (TypeContext.entries_subset_insert_of_notMem x_not_in_ΓR).trans
            (TypeContext.entries_subset_insert_of_notMem (by
              intro h; rw [AList.mem_insert] at h
              rcases h with rfl | h; exact hx_ne_y rfl; exact y_not_in_ΓR h))
          apply SMT.Typing.imp
          · apply SMT.Typing.app
            · apply SMT.Typing.var
              rw [AList.lookup_insert_ne hR_ne_y, AList.lookup_insert_ne hR_ne_x, AList.lookup_insert]
            · apply SMT.Typing.pair
              · apply SMT.Typing.var; rw [AList.lookup_insert_ne hx_ne_y, AList.lookup_insert]
              · apply SMT.Typing.var; rw [AList.lookup_insert]
          · apply SMT.Typing.and
            · apply SMT.Typing.app
              · exact Typing.weakening hΓRxy_sub typ_A_R
              · apply SMT.Typing.var
                rw [AList.lookup_insert_ne hx_ne_y, AList.lookup_insert]
            · apply SMT.Typing.app
              · exact Typing.weakening hΓRxy_sub typ_B_R
              · apply SMT.Typing.var; rw [AList.lookup_insert]
      · -- P2 typing
        rw [hP2_def]
        refine SMT.Typing.forall Γ_R [x, y, y'] [αx.toSMTType, βx.toSMTType, βx.toSMTType] _ ?_ ?_ (by simp) rfl ?_
        · intro v hv
          rcases List.mem_cons.mp hv with rfl | hv'
          · exact x_not_in_ΓR
          · rcases List.mem_cons.mp hv' with rfl | hv''
            · exact y_not_in_ΓR
            · rcases List.mem_cons.mp hv'' with rfl | h
              · exact y'_not_in_ΓR
              · exact absurd h (by simp)
        · intro v _ hbv
          simp only [SMT.bv, List.mem_append, List.mem_nil_iff, or_false, false_or] at hbv
        · have hupdate_xyy' : TypeContext.update Γ_R
              [x, y, y'] [αx.toSMTType, βx.toSMTType, βx.toSMTType] rfl =
              (((Γ_R.insert x αx.toSMTType).insert y βx.toSMTType).insert y' βx.toSMTType) := by
            simp only [TypeContext.update, List.length_cons, List.length_nil, zero_add,
              Fin.foldl_succ_last, Fin.getElem_fin, Fin.coe_cast, Fin.val_last,
              List.getElem_append_right, Nat.sub_self, List.getElem_cons_zero,
              Fin.coe_castSucc, Fin.foldl_zero]; rfl
          rw [hupdate_xyy']
          apply SMT.Typing.imp
          · apply SMT.Typing.and
            · apply SMT.Typing.app
              · apply SMT.Typing.var
                rw [AList.lookup_insert_ne hR_ne_y', AList.lookup_insert_ne hR_ne_y,
                  AList.lookup_insert_ne hR_ne_x, AList.lookup_insert]
              · apply SMT.Typing.pair
                · apply SMT.Typing.var
                  rw [AList.lookup_insert_ne hx_ne_y', AList.lookup_insert_ne hx_ne_y, AList.lookup_insert]
                · apply SMT.Typing.var; rw [AList.lookup_insert_ne hy_ne_y', AList.lookup_insert]
            · apply SMT.Typing.app
              · apply SMT.Typing.var
                rw [AList.lookup_insert_ne hR_ne_y', AList.lookup_insert_ne hR_ne_y,
                  AList.lookup_insert_ne hR_ne_x, AList.lookup_insert]
              · apply SMT.Typing.pair
                · apply SMT.Typing.var
                  rw [AList.lookup_insert_ne hx_ne_y', AList.lookup_insert_ne hx_ne_y, AList.lookup_insert]
                · apply SMT.Typing.var; rw [AList.lookup_insert]
          · apply SMT.Typing.eq
            · apply SMT.Typing.var; rw [AList.lookup_insert_ne hy_ne_y', AList.lookup_insert]
            · apply SMT.Typing.var; rw [AList.lookup_insert]
    -- Now use denote_exists_of_typing_fv on the full pfun_body
    obtain ⟨Dbody, hDbody_den, hDbody_ty⟩ :=
      SMT.RenamingContext.denote_exists_of_typing_fv typ_pfun_body hcompat_body (hcov_body_updR WR)
    -- Extract P1/P2 via and decomposition
    have habs_eq_pre : ⟦pfun_body.abstract (Function.update Δctx R (some WR)) (hcov_body_updR WR)⟧ˢ =
        ⟦(P1.abstract (Function.update Δctx R (some WR)) hcov_P1) ∧ˢ'
         (P2.abstract (Function.update Δctx R (some WR)) hcov_P2)⟧ˢ := by
      congr 1; show pfun_body.abstract _ _ = _; simp only [hpfun_body_def, SMT.Term.abstract]
    have hand_den := habs_eq_pre ▸ hDbody_den
    have hP1_den : ∃ D1 : SMT.Dom,
        ⟦P1.abstract (Function.update Δctx R (some WR)) hcov_P1⟧ˢ = some D1 ∧
        D1.2.1 = .bool :=
      denote_and_extract_left hand_den
    have hP2_den : ∃ D2 : SMT.Dom,
        ⟦P2.abstract (Function.update Δctx R (some WR)) hcov_P2⟧ˢ = some D2 ∧
        D2.2.1 = .bool :=
      denote_and_extract_right hand_den
    obtain ⟨D1, hD1_den, hD1_ty⟩ := hP1_den
    obtain ⟨D2, hD2_den, hD2_ty⟩ := hP2_den
    obtain ⟨D, hD_den, hD_ty⟩ := denote_and_some_bool_of_some_bool hD1_den hD1_ty hD2_den hD2_ty
    exact ⟨D, habs_eq_pre ▸ hD_den, hD_ty⟩
  have hbody_total : ∀ WR : SMT.Dom, WR.2.1 = τR →
      ⟦pfun_body.abstract (Function.update Δctx R (some WR)) (hcov_body_updR WR)⟧ˢ.isSome = true := by
    intro WR hWR_ty
    obtain ⟨D, hD, _⟩ := hbody_exists WR hWR_ty
    exact Option.isSome_of_eq_some hD
  have hbody_ty : ∀ (WR : SMT.Dom), WR.2.1 = τR → ∀ D,
      ⟦pfun_body.abstract (Function.update Δctx R (some WR)) (hcov_body_updR WR)⟧ˢ = some D →
      D.snd.fst = .bool := by
    intro WR hWR_ty D hD
    obtain ⟨D', hD', hD'_ty⟩ := hbody_exists WR hWR_ty
    cases hD.symm.trans hD'
    exact hD'_ty
  -- Lambda isSome
  have hsome_lambda : ⟦((λˢ [R]) [τR] pfun_body).abstract Δctx hcov⟧ˢ.isSome = true := by
    rw [SMT.Term.abstract, dif_pos (by rfl), SMT.denote]
    have hlen : [R].length > 0 := by simp
    rw [dif_pos hlen]
    split_ifs with den_t_isSome den_t_typ_det
    · simp
    · exfalso; apply den_t_typ_det
      intro x₀ y₀ hx₀ hy₀
      let Wx : SMT.Dom := x₀ ⟨0, by simp⟩
      let Wy : SMT.Dom := y₀ ⟨0, by simp⟩
      have hWx_ty : Wx.snd.fst = τR := by simpa [Wx] using (hx₀ ⟨0, by simp⟩).1
      have hWy_ty : Wy.snd.fst = τR := by simpa [Wy] using (hy₀ ⟨0, by simp⟩).1
      have hgo_x := funAbstractGoSingle (Δctx := Δctx) (P := pfun_body) (v := R) (τ := τR)
        hgo_cov_body (fun WR => hcov_body_updR WR) x₀ hx₀
      have hgo_y := funAbstractGoSingle (Δctx := Δctx) (P := pfun_body) (v := R) (τ := τR)
        hgo_cov_body (fun WR => hcov_body_updR WR) y₀ hy₀
      obtain ⟨Dx, hDx⟩ := Option.isSome_iff_exists.mp (hbody_total Wx hWx_ty)
      obtain ⟨Dy, hDy⟩ := Option.isSome_iff_exists.mp (hbody_total Wy hWy_ty)
      have hden_x : ⟦(SMT.Term.abstract.go pfun_body [R] Δctx hgo_cov_body).uncurry x₀⟧ˢ = some Dx := by
        rw [hgo_x]; exact hDx
      have hden_y : ⟦(SMT.Term.abstract.go pfun_body [R] Δctx hgo_cov_body).uncurry y₀⟧ˢ = some Dy := by
        rw [hgo_y]; exact hDy
      calc (⟦(SMT.Term.abstract.go pfun_body [R] Δctx hgo_cov_body).uncurry x₀⟧ˢ.get
              (den_t_isSome hx₀)).snd.fst
          = Dx.snd.fst := congrArg (·.snd.fst) (Option.get_of_eq_some (den_t_isSome hx₀) hden_x)
        _ = SMTType.bool := hbody_ty Wx hWx_ty Dx hDx
        _ = Dy.snd.fst := (hbody_ty Wy hWy_ty Dy hDy).symm
        _ = (⟦(SMT.Term.abstract.go pfun_body [R] Δctx hgo_cov_body).uncurry y₀⟧ˢ.get
              (den_t_isSome hy₀)).snd.fst :=
            (congrArg (·.snd.fst) (Option.get_of_eq_some (den_t_isSome hy₀) hden_y)).symm
    · exfalso; apply den_t_isSome
      intro x₀ hx₀
      let Wx : SMT.Dom := x₀ ⟨0, by simp⟩
      have hWx_ty : Wx.snd.fst = τR := by simpa [Wx] using (hx₀ ⟨0, by simp⟩).1
      rw [funAbstractGoSingle (Δctx := Δctx) (P := pfun_body) (v := R) (τ := τR)
        hgo_cov_body (fun WR => hcov_body_updR WR) x₀ hx₀]
      exact hbody_total Wx hWx_ty
  -- Build body function (classical, following union template)
  classical
  set bodyFun : ZFSet → ZFSet := fun x₁ =>
    if hx : x₁.hasArity 1 ∧ x₁ ∈ ⟦τR⟧ᶻ then
      let W : SMT.Dom := ⟨x₁, τR, hx.2⟩
      if hsome : ⟦pfun_body.abstract (Function.update Δctx R (some W))
          (hcov_body_updR W)⟧ˢ.isSome then
        (⟦pfun_body.abstract (Function.update Δctx R (some W))
            (hcov_body_updR W)⟧ˢ.get hsome).fst
      else SMTType.bool.defaultZFSet
    else SMTType.bool.defaultZFSet with hbodyFun_def
  have hbodyFun_range : ∀ {x₁ : ZFSet}, x₁ ∈ ⟦τR⟧ᶻ → bodyFun x₁ ∈ 𝔹 := by
    intro x₁ hx₁
    simp only [bodyFun]
    have hx_cast : x₁.hasArity 1 ∧ x₁ ∈ ⟦τR⟧ᶻ := ⟨(funUnaryTarget hx₁).1, hx₁⟩
    rw [dif_pos hx_cast]
    let W : SMT.Dom := ⟨x₁, τR, hx₁⟩
    have hsome := hbody_total W rfl
    rw [dif_pos hsome]
    obtain ⟨Dbody, hDx⟩ := Option.isSome_iff_exists.mp hsome
    have hDbody_ty := hbody_ty W rfl Dbody hDx
    have hget_eq := Option.get_of_eq_some hsome hDx
    rw [congrArg (·.fst) hget_eq]
    have : Dbody.fst ∈ ⟦Dbody.snd.fst⟧ᶻ := Dbody.snd.snd
    rwa [hDbody_ty] at this
  have hbodyFun_eq : ∀ (w : ZFSet) (hw : w ∈ ⟦τR⟧ᶻ),
      ∃ Dbody : SMT.Dom,
        ⟦pfun_body.abstract (Function.update Δctx R (some ⟨w, τR, hw⟩))
          (hcov_body_updR ⟨w, τR, hw⟩)⟧ˢ = some Dbody ∧
        bodyFun w = Dbody.fst := by
    intro w hw
    let W : SMT.Dom := ⟨w, τR, hw⟩
    obtain ⟨Dbody, hden_body⟩ := Option.isSome_iff_exists.mp (hbody_total W rfl)
    refine ⟨Dbody, hden_body, ?_⟩
    simp only [bodyFun]
    have hx_cast : w.hasArity 1 ∧ w ∈ ⟦τR⟧ᶻ := ⟨(funUnaryTarget hw).1, hw⟩
    rw [dif_pos hx_cast]
    have hsome := hbody_total W rfl
    rw [dif_pos hsome]
    exact congrArg (·.fst) (Option.get_of_eq_some hsome hden_body)
  set lamFun := ZFSet.lambda ⟦τR⟧ᶻ 𝔹 bodyFun with hlamFun_def
  have hlamFun_func : ZFSet.IsFunc ⟦τR⟧ᶻ 𝔹 lamFun :=
    ZFSet.lambda_isFunc (fun {z} hz => hbodyFun_range hz)
  have hlamFun_mem : lamFun ∈ ⟦τR.fun SMTType.bool⟧ᶻ := by
    simp [SMTType.toZFSet]; exact hlamFun_func
  have hlamFun_fapply : ∀ (w : ZFSet) (hw : w ∈ ⟦τR⟧ᶻ),
      ZFSet.fapply lamFun (ZFSet.is_func_is_pfunc hlamFun_func)
        ⟨w, by rw [ZFSet.is_func_dom_eq hlamFun_func]; exact hw⟩ = bodyFun w := by
    intro w hw; exact ZFSet.fapply_lambda (hf := fun {z} hz => hbodyFun_range hz) (ha := hw)
  obtain ⟨lamVal, hlamVal⟩ := Option.isSome_iff_exists.mp hsome_lambda
  have hlamVal_saved := hlamVal
  have hlamVal_ty : lamVal.snd.fst = .fun τR .bool := by
    have hlamVal' := hlamVal
    rw [SMT.Term.abstract, dif_pos (by rfl)] at hlamVal'
    simp only [SMT.denote] at hlamVal'
    rw [dif_pos (show [R].length > 0 by exact Nat.zero_lt_succ 0)] at hlamVal'
    split_ifs at hlamVal' with h_isSome h_typ_det
    · let xd : Fin 1 → SMT.Dom := fun _ => ⟨τR.defaultZFSet, τR, SMTType.mem_toZFSet_of_defaultZFSet⟩
      have hxd_spec : ∀ i, (xd i).2.1 = [τR][↑i] ∧ (xd i).1 ∈ ⟦[τR][↑i]⟧ᶻ := by
        intro ⟨i, hi⟩; simp at hi; subst hi; exact ⟨rfl, SMTType.mem_toZFSet_of_defaultZFSet⟩
      have hgo_d := funAbstractGoSingle (Δctx := Δctx) (P := pfun_body) (v := R) (τ := τR)
        hgo_cov_body (fun WR => hcov_body_updR WR) xd hxd_spec
      obtain ⟨Dd, hDd⟩ := Option.isSome_iff_exists.mp (hbody_total (xd ⟨0, by simp⟩) rfl)
      have hden_d : ⟦(SMT.Term.abstract.go pfun_body [R] Δctx hgo_cov_body).uncurry xd⟧ˢ = some Dd := by
        rw [hgo_d]; exact hDd
      have hγ_out : (⟦(SMT.Term.abstract.go pfun_body [R] Δctx hgo_cov_body).uncurry xd⟧ˢ.get
          (h_isSome hxd_spec)).snd.fst = .bool := by
        rw [congrArg (·.snd.fst) (Option.get_of_eq_some _ hden_d)]
        exact hbody_ty (xd ⟨0, Nat.one_pos⟩) rfl Dd hDd
      simp only [Option.pure_def, Option.some.injEq] at hlamVal'
      rw [show lamVal.snd.fst = _ from congrArg (·.snd.fst) hlamVal'.symm]
      simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.sub_self,
        Fin.foldr_zero, List.getElem_cons_zero]
      exact congrArg (τR.fun ·) hγ_out
  have hlamVal_func : ZFSet.IsFunc ⟦τR⟧ᶻ 𝔹 lamVal.fst := by
    have : lamVal.fst ∈ ⟦τR⟧ᶻ.funs 𝔹 := by
      simpa [hlamVal_ty, SMTType.toZFSet] using lamVal.snd.snd
    exact ZFSet.mem_funs.mp this
  -- Main conclusion
  refine ⟨lamVal, ?_, hlamVal_ty, ?_⟩
  · convert hlamVal using 2
  · -- Retract equality: this is the hard semantic part.
    -- retract (.set (.set (.prod αx βx))) lamVal.1 = 𝒫(X × Y) ∩ {f | IsPFunc f X Y}
    -- where X = retract(αx.set, den_A.1), Y = retract(βx.set, den_B.1)
    -- This requires connecting the lambda body's boolean value to the IsPFunc condition.
    -- The body evaluates to zftrue for R iff:
    -- (∀ pair, R(pair)=true → A(π₁)=true ∧ B(π₂)=true) ∧ (functional condition)
    -- which is exactly R ⊆ X×Y ∧ IsPFunc R X Y (after retracting through canonicalIso).
    -- Establish hlamVal_app: fapply lamVal.fst w = Dbody.fst
    have hlamVal_app : ∀ (w : ZFSet) (hw : w ∈ ⟦τR⟧ᶻ),
        ∃ Dbody : SMT.Dom,
          ⟦pfun_body.abstract (Function.update Δctx R (some ⟨w, τR, hw⟩))
            (hcov_body_updR ⟨w, τR, hw⟩)⟧ˢ = some Dbody ∧
          ZFSet.fapply lamVal.fst (ZFSet.is_func_is_pfunc hlamVal_func)
            ⟨w, by rw [ZFSet.is_func_dom_eq hlamVal_func]; exact hw⟩ = Dbody.fst := by
      intro w hw
      obtain ⟨Dbody, hden_body, hbf_eq⟩ := hbodyFun_eq w hw
      refine ⟨Dbody, hden_body, ?_⟩
      have hlamVal' := hlamVal_saved
      rw [SMT.Term.abstract, dif_pos (by rfl)] at hlamVal'
      simp only [SMT.denote] at hlamVal'
      rw [dif_pos (show [R].length > 0 by exact Nat.zero_lt_succ 0)] at hlamVal'
      split_ifs at hlamVal' with h_isSome h_typ_det
      · have hlamVal_eq_lamFun : lamVal.fst = lamFun :=
          (ZFSet.is_func_ext_iff hlamVal_func hlamFun_func).mpr fun w' hw' => by
            apply Subtype.ext; rw [hlamFun_fapply w' hw']
            obtain ⟨Dbody', hden_body', hbf_eq'⟩ := hbodyFun_eq w' hw'
            rw [hbf_eq']
            simp only [Option.pure_def, Option.some.injEq] at hlamVal'
            have hval_eq : lamVal.fst = _ := congrArg (·.fst) hlamVal'.symm
            have h_pair_mem : w'.pair Dbody'.fst ∈ lamVal.fst := by
              rw [hval_eq]
              simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.sub_self,
                Fin.foldr_zero, List.getElem_cons_zero]
              rw [ZFSet.mem_lambda]; refine ⟨w', Dbody'.fst, rfl, hw', ?_, ?_⟩
              · have hmem := Dbody'.snd.snd
                rw [hbody_ty ⟨w', τR, hw'⟩ rfl Dbody' hden_body'] at hmem
                convert hmem using 2
                let xₐ : Fin 1 → SMT.Dom := fun _ => ⟨τR.defaultZFSet, τR, SMTType.mem_toZFSet_of_defaultZFSet⟩
                let xᵦ : Fin 1 → SMT.Dom := fun _ => ⟨w', τR, hw'⟩
                have hxₐ : ∀ i : Fin 1, (xₐ i).snd.fst = [τR][↑i] ∧ (xₐ i).fst ∈ ⟦[τR][↑i]⟧ᶻ := by
                  intro ⟨i, hi⟩; simp at hi; subst hi; exact ⟨rfl, SMTType.mem_toZFSet_of_defaultZFSet⟩
                have hxᵦ : ∀ i : Fin 1, (xᵦ i).snd.fst = [τR][↑i] ∧ (xᵦ i).fst ∈ ⟦[τR][↑i]⟧ᶻ := by
                  intro ⟨i, hi⟩; simp at hi; subst hi; exact ⟨rfl, hw'⟩
                calc (⟦(SMT.Term.abstract.go pfun_body [R] Δctx hgo_cov_body).uncurry xₐ⟧ˢ.get
                        (h_isSome hxₐ)).snd.fst
                    = (⟦(SMT.Term.abstract.go pfun_body [R] Δctx hgo_cov_body).uncurry xᵦ⟧ˢ.get
                        (h_isSome hxᵦ)).snd.fst := h_typ_det xₐ xᵦ hxₐ hxᵦ
                  _ = Dbody'.snd.fst := by
                      have hgo_xᵦ := funAbstractGoSingle hgo_cov_body (fun WR => hcov_body_updR WR) xᵦ hxᵦ
                      have hden_xᵦ : ⟦(SMT.Term.abstract.go pfun_body [R] Δctx hgo_cov_body).uncurry xᵦ⟧ˢ = some Dbody' := by
                        rw [hgo_xᵦ]; exact hden_body'
                      exact congrArg (·.snd.fst) (Option.get_of_eq_some (h_isSome hxᵦ) hden_xᵦ)
                  _ = SMTType.bool := hbody_ty ⟨w', τR, hw'⟩ rfl Dbody' hden_body'
              · split_ifs with hw'_cond
                · let xₙ := fun i : Fin 1 => (⟨w'.get 1 i, [τR][↑i], hw'_cond.2 i⟩ : SMT.Dom)
                  have hgo' := funAbstractGoSingle (Δctx := Δctx) (P := pfun_body) (v := R) (τ := τR)
                    hgo_cov_body (fun WR => hcov_body_updR WR) xₙ (fun i => ⟨rfl, hw'_cond.2 i⟩)
                  have hxₙ_eq : xₙ ⟨0, Nat.zero_lt_one⟩ = ⟨w', τR, hw'⟩ := rfl
                  have hden' : ⟦(SMT.Term.abstract.go pfun_body [R] Δctx hgo_cov_body).uncurry xₙ⟧ˢ = some Dbody' := by
                    rw [hgo', hxₙ_eq]; exact hden_body'
                  exact (congrArg (·.fst) (Option.get_of_eq_some _ hden')).symm
                · exfalso; apply hw'_cond
                  exact ⟨trivial, fun ⟨i, hi⟩ => by have : i = 0 := Nat.lt_one_iff.mp hi; subst this; exact hw'⟩
            exact Subtype.ext_iff.mp (ZFSet.fapply.of_pair (ZFSet.is_func_is_pfunc hlamVal_func) h_pair_mem)
        rw [(ZFSet.is_func_ext_iff hlamVal_func hlamFun_func).mp hlamVal_eq_lamFun w hw,
          hlamFun_fapply w hw]; exact hbf_eq
    -- Retract equality via ext
    set X := retract (BType.set αx) den_A.fst with hX_def
    set Y := retract (BType.set βx) den_B.fst with hY_def
    set αprod := BType.set (BType.prod αx βx) with hαprod_def
    ext g; simp only [ZFSet.mem_sep]
    let mk_cg (hg_αprod : g ∈ ⟦αprod⟧ᶻ) : ZFSet :=
      ZFSet.fapply (BType.canonicalIsoSMTType αprod).1
        (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType αprod).2.1)
        ⟨g, by rwa [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType αprod).2.1]⟩
    have mk_cg_mem (hg_αprod : g ∈ ⟦αprod⟧ᶻ) : mk_cg hg_αprod ∈ ⟦αprod.toSMTType⟧ᶻ :=
      ZFSet.fapply_mem_range _ _
    have fapply_iff_g (hg_αprod : g ∈ ⟦αprod⟧ᶻ)
        {F : ZFSet} (hF_func : ZFSet.IsFunc ⟦αprod.toSMTType⟧ᶻ 𝔹 F) :
        g ∈ retract αprod.set F ↔
        ZFSet.fapply F (ZFSet.is_func_is_pfunc hF_func)
          ⟨mk_cg hg_αprod, by rw [ZFSet.is_func_dom_eq hF_func]; exact mk_cg_mem hg_αprod⟩ =
            zftrue := by
      rw [retract, ZFSet.mem_sep]; constructor
      · intro ⟨_, hmem⟩; rw [dif_pos hg_αprod, dif_pos hF_func] at hmem; simpa using hmem
      · intro h; exact ⟨hg_αprod, by rw [dif_pos hg_αprod, dif_pos hF_func]; simpa using h⟩
    have retract_cg (hg_αprod : g ∈ ⟦αprod⟧ᶻ) :
        retract αprod (mk_cg hg_αprod) = g := retract_of_canonical αprod hg_αprod
    constructor
    · -- (→) forward direction: g ∈ retract αprod.set lamVal.fst → g ∈ 𝒫(X×Y) ∧ IsPFunc g X Y
      intro hg_mem
      have hg_αprod : g ∈ ⟦αprod⟧ᶻ := by
        rw [retract, ZFSet.mem_sep] at hg_mem; exact hg_mem.1
      rw [fapply_iff_g hg_αprod hlamVal_func] at hg_mem
      -- hg_mem : fapply lamVal.fst (mk_cg hg_αprod) = zftrue
      obtain ⟨Dbody_fwd, hden_body_fwd, hfapply_eq_fwd⟩ :=
        hlamVal_app (mk_cg hg_αprod) (mk_cg_mem hg_αprod)
      have hDbody_fwd_true : Dbody_fwd.fst = zftrue := by
        rw [← hfapply_eq_fwd]; exact hg_mem
      have hg_sub : g ⊆ ⟦BType.prod αx βx⟧ᶻ := ZFSet.mem_powerset.mp hg_αprod
      -- g ⊆ X×Y: for each z ∈ g, z.π₁ ∈ X and z.π₂ ∈ Y.
      -- g.IsPFunc X Y: g ⊆ X×Y and g is functional on X Y.
      -- Both properties are encoded by the body pfun_body = and P1 P2 evaluating to zftrue
      -- at R := canonical(g).
      -- P1 = zftrue encodes g ⊆ X×Y.
      -- P2 = zftrue encodes functionality.
      -- Extracting these requires inverting the forall denotation (sInter = zftrue → inner = zftrue)
      -- which is available via `forall_eq_zftrue_of_sInter_sep_eq_zftrue`, plus decomposing the
      -- body denotation into P1 and P2 parts (which requires the P1_den and P2_den proofs at
      -- lines 415 and 419 to be filled).
      -- Once those prerequisites are available, the proof proceeds as follows:
      -- 1. Split body into P1 and P2, both denote as .bool (from P1_den, P2_den)
      -- 2. Since body = and P1 P2 = zftrue, both P1 and P2 = zftrue (ZFBool case analysis)
      -- 3. P1 = sInter of inner body values = zftrue → each inner body = zftrue (by helper)
      -- 4. For each z ∈ g, take (ca, cb) = canonical (z.π₁, z.π₂):
      --    inner P1 at (ca, cb) = imp(app R (pair ca cb))(and(app A ca)(app B cb))
      --    fapply mk_cg (pair ca cb) = zftrue (since z ∈ g)
      --    So imp(zftrue, Q) = zftrue → Q = zftrue
      --    Q = and(A(ca))(B(cb)) = zftrue → A(ca) = zftrue ∧ B(cb) = zftrue
      --    A(ca) = fapply den_A ca = zftrue → z.π₁ ∈ X
      --    B(cb) = fapply den_B cb = zftrue → z.π₂ ∈ Y
      -- 5. For IsPFunc, P2 = sInter = zftrue → each inner = zftrue
      --    For z₁ = (a, b₁) ∈ g, z₂ = (a, b₂) ∈ g:
      --    inner P2 at (ca, cb₁, cb₂) = imp(and(R(ca,cb₁))(R(ca,cb₂)))(eq cb₁ cb₂)
      --    Both R values = zftrue → imp(zftrue, eq cb₁ cb₂) = zftrue → cb₁ = cb₂
      --    Since canonical is injective: b₁ = b₂.
      -- Step 1: Decompose body denotation into P1 and P2 parts
      let WR_fwd : SMT.Dom := ⟨mk_cg hg_αprod, τR, mk_cg_mem hg_αprod⟩
      have hcov_P1_fwd : RenamingContext.CoversFV (Function.update Δctx R (some WR_fwd)) P1 :=
        fun v hv => hcov_body_updR WR_fwd v (by rw [hpfun_body_def]; exact SMT.fv.mem_and (Or.inl hv))
      have hcov_P2_fwd : RenamingContext.CoversFV (Function.update Δctx R (some WR_fwd)) P2 :=
        fun v hv => hcov_body_updR WR_fwd v (by rw [hpfun_body_def]; exact SMT.fv.mem_and (Or.inr hv))
      have habs_eq_fwd : ⟦pfun_body.abstract (Function.update Δctx R (some WR_fwd)) (hcov_body_updR WR_fwd)⟧ˢ =
          ⟦(P1.abstract (Function.update Δctx R (some WR_fwd)) hcov_P1_fwd) ∧ˢ'
           (P2.abstract (Function.update Δctx R (some WR_fwd)) hcov_P2_fwd)⟧ˢ := by
        congr 1; show pfun_body.abstract _ _ = _; simp only [hpfun_body_def, SMT.Term.abstract]
      have hand_den_fwd := habs_eq_fwd ▸ hden_body_fwd
      obtain ⟨D1_fwd, hD1_fwd_den, hD1_fwd_ty⟩ := denote_and_extract_left hand_den_fwd
      obtain ⟨D2_fwd, hD2_fwd_den, hD2_fwd_ty⟩ := denote_and_extract_right hand_den_fwd
      -- Step 2: Both P1 and P2 values are zftrue (from body = zftrue via ZFBool case analysis)
      have hD1_fwd_mem_𝔹 : D1_fwd.fst ∈ 𝔹 := by
        have := D1_fwd.snd.snd; rwa [hD1_fwd_ty] at this
      have hD2_fwd_mem_𝔹 : D2_fwd.fst ∈ 𝔹 := by
        have := D2_fwd.snd.snd; rwa [hD2_fwd_ty] at this
      have hD1_fwd_true : D1_fwd.fst = zftrue := by
        -- body = and(P1, P2) = zftrue. If P1 = zffalse, and = zffalse ≠ zftrue.
        rcases ZFSet.ZFBool.mem_𝔹_iff _ |>.mp hD1_fwd_mem_𝔹 with h | h
        · exfalso
          have hfalse := denote_and_eq_zffalse_of_some_zffalse_left hD1_fwd_den hD1_fwd_ty h hD2_fwd_den hD2_fwd_ty
          have : Dbody_fwd = ⟨zffalse, .bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ :=
            Option.some_injective _ (hand_den_fwd.symm.trans hfalse)
          rw [this] at hDbody_fwd_true; exact ZFSet.zftrue_ne_zffalse hDbody_fwd_true.symm
        · exact h
      have hD2_fwd_true : D2_fwd.fst = zftrue := by
        rcases ZFSet.ZFBool.mem_𝔹_iff _ |>.mp hD2_fwd_mem_𝔹 with h | h
        · exfalso
          have hfalse := denote_and_eq_zffalse_of_some_zffalse_right hD1_fwd_den hD1_fwd_ty hD2_fwd_den hD2_fwd_ty h
          have : Dbody_fwd = ⟨zffalse, .bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ :=
            Option.some_injective _ (hand_den_fwd.symm.trans hfalse)
          rw [this] at hDbody_fwd_true; exact ZFSet.zftrue_ne_zffalse hDbody_fwd_true.symm
        · exact h
      -- Step 3: From P1 = zftrue, extract g ⊆ X × Y
      -- P1 = forall [x,y] (imp (app R (pair x y)) (and (app A x) (app B y)))
      -- P1 denotation = zftrue means: for all (a,b) ∈ g, a ∈ X ∧ b ∈ Y.
      -- Step 4: From P2 = zftrue, extract functionality
      -- P2 = forall [x,y,y'] (imp (and (app R (pair x y)) (app R (pair x y'))) (eq y y'))
      -- P2 denotation = zftrue means: for all a b₁ b₂, (a,b₁) ∈ g → (a,b₂) ∈ g → b₁ = b₂.
      -- Both require inverting the forall denotation, which is the same PHOAS bridge as the
      -- backward direction.

      -- The key insight: we have P1 = zftrue and P2 = zftrue from hD1_fwd_true and hD2_fwd_true.
      -- These are forall statements that denote to zftrue.
      -- For g ⊆ X × Y: take any z ∈ g and extract its pair structure.
      -- For IsPFunc: use functionality encoded in P2.

      -- ── Forward direction: PHOAS infrastructure for P1 and P2 ──
      -- (Mirrors backward direction with WR_fwd instead of WR_bwd)
      have y_not_fv_appAx_fwd : y ∉ SMT.fv (Term.app A_enc (.var x)) := by
        simp only [SMT.fv, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false]
        push_neg; exact ⟨y_not_fv_A, Ne.symm hx_ne_y⟩
      have hDA_Rxy_fwd : ∀ (W₁ W₂ : SMT.Dom) (hW₁_ty : W₁.snd.fst = αx.toSMTType)
          (hW₁_mem : W₁.fst ∈ ⟦αx.toSMTType⟧ᶻ),
          ∃ DA : SMT.Dom,
            DA.snd.fst = .bool ∧
            DA.fst = (ZFSet.fapply den_A.fst (ZFSet.is_func_is_pfunc hdenA_func)
              ⟨W₁.fst, by rw [ZFSet.is_func_dom_eq hdenA_func]; exact hW₁_mem⟩).1 ∧
            SMT.RenamingContext.denote
              (Function.update (Function.update (Function.update Δctx R (some WR_fwd)) x (some W₁))
                y (some W₂))
              (Term.app A_enc (.var x))
              (SMT.RenamingContext.coversFV_update_of_notMem y_not_fv_appAx_fwd
                (den_app_A_x WR_fwd W₁ hW₁_ty hW₁_mem).choose) = some DA := by
        intro W₁ W₂ hW₁_ty hW₁_mem
        obtain ⟨hcov_appA, DA, hDA_ty, hDA_val, hDA_den⟩ := den_app_A_x WR_fwd W₁ hW₁_ty hW₁_mem
        refine ⟨DA, hDA_ty, hDA_val, ?_⟩
        rw [← SMT.RenamingContext.denote_update_of_notMem y_not_fv_appAx_fwd (h := hcov_appA)]
        exact hDA_den
      set P1_inner_fwd := Term.imp (.app (.var R) (.pair (.var x) (.var y)))
        (.and (.app A_enc (.var x)) (.app B_enc (.var y))) with hP1_inner_def_fwd
      have hcov_P1_inner_updxy_fwd : ∀ W₁ W₂ : SMT.Dom,
          RenamingContext.CoversFV
            (Function.update (Function.update (Function.update Δctx R (some WR_fwd)) x (some W₁))
              y (some W₂)) P1_inner_fwd := by
        intro W₁ W₂ v hv
        rw [hP1_inner_def_fwd, SMT.fv] at hv
        simp only [SMT.fv, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, false_or] at hv
        by_cases hvR : v = R; · subst hvR; simp [Function.update, hR_ne_x, hR_ne_y]
        by_cases hvx : v = x; · subst hvx; simp [Function.update, hx_ne_y]
        by_cases hvy : v = y; · subst hvy; simp [Function.update]
        · rw [Function.update_of_ne hvy, Function.update_of_ne hvx, Function.update_of_ne hvR]
          have hv_body : v ∈ SMT.fv pfun_body := by
            rw [hpfun_body_def]; apply SMT.fv.mem_and; left
            rw [hP1_def]; apply SMT.fv.mem_forall
            refine ⟨?_, by simp; push_neg; exact ⟨hvx, hvy⟩⟩
            simp only [hP1_inner_def_fwd, SMT.fv, List.mem_append, List.mem_cons, List.mem_nil_iff,
              or_false]
            rcases hv with (rfl | rfl | rfl) | (h | rfl) | (h | rfl) <;> simp [hvy, hvx, hvR]
            <;> [left; right] <;> exact h
          have hv_lambda : v ∈ SMT.fv (Term.lambda [R] [τR] pfun_body) := by
            rw [SMT.fv]; exact List.mem_filter.mpr ⟨hv_body, by simpa using hvR⟩
          exact hcov v hv_lambda
      have hgo_cov_P1_inner_fwd : ∀ v ∈ SMT.fv P1_inner_fwd, v ∉ [x, y] →
          ((Function.update Δctx R (some WR_fwd)) v).isSome = true := by
        intro v hv hvxy
        have hvx : v ≠ x := by intro h; exact hvxy (List.mem_cons.mpr (Or.inl h))
        have hvy : v ≠ y := by
          intro h; exact hvxy (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl h))))
        by_cases hvR : v = R; · subst hvR; simp [Function.update]
        · rw [Function.update_of_ne hvR]
          have hv_body : v ∈ SMT.fv pfun_body := by
            rw [hpfun_body_def]; apply SMT.fv.mem_and; left
            rw [hP1_def]; apply SMT.fv.mem_forall; refine ⟨hv, ?_⟩
            simp [List.mem_cons]; push_neg; exact ⟨hvx, hvy⟩
          have hv_lambda : v ∈ SMT.fv (Term.lambda [R] [τR] pfun_body) := by
            rw [SMT.fv]; exact List.mem_filter.mpr ⟨hv_body, by simpa using hvR⟩
          exact hcov v hv_lambda
      have hP1_inner_total_fwd : ∀ W₁ W₂ : SMT.Dom,
          W₁.snd.fst = αx.toSMTType → W₂.snd.fst = βx.toSMTType →
          ⟦P1_inner_fwd.abstract
            (Function.update (Function.update (Function.update Δctx R (some WR_fwd)) x (some W₁))
              y (some W₂))
            (hcov_P1_inner_updxy_fwd W₁ W₂)⟧ˢ.isSome = true := by
        intro W₁ W₂ hW₁_ty hW₂_ty
        have hW₁_mem : W₁.fst ∈ ⟦αx.toSMTType⟧ᶻ := by rw [← hW₁_ty]; exact W₁.2.2
        have hW₂_mem : W₂.fst ∈ ⟦βx.toSMTType⟧ᶻ := by rw [← hW₂_ty]; exact W₂.2.2
        obtain ⟨DR, hDR, hDR_ty⟩ := denote_app_var_pair_var_var rfl hW₁_ty hW₁_mem hW₂_ty hW₂_mem
          (WR := WR_fwd) (Wx := W₁) (Wy := W₂)
        obtain ⟨DA, _, _, hDA_den⟩ := hDA_Rxy_fwd W₁ W₂ hW₁_ty hW₁_mem
        obtain ⟨_, DB, hDB_ty, _, hDB_den⟩ := den_app_B_y WR_fwd W₁ W₂ hW₂_ty hW₂_mem
        change ⟦(Term.app A_enc (.var x)).abstract _ _⟧ˢ = some DA at hDA_den
        obtain ⟨Dand, hDand, _⟩ := denote_and_some_bool_of_some_bool hDA_den ‹_› hDB_den hDB_ty
        obtain ⟨Dimp, hDimp, _⟩ := denote_imp_some_bool_of_some_bool hDR hDR_ty hDand ‹_›
        suffices h : ⟦P1_inner_fwd.abstract _ _⟧ˢ = some Dimp from
          Option.isSome_iff_exists.mpr ⟨Dimp, h⟩
        simp only [hP1_inner_def_fwd, SMT.Term.abstract, Function.update,
          hR_ne_y, hR_ne_x, hx_ne_y, ↓reduceDIte, Option.get_some] at hDimp ⊢
        exact hDimp
      have hP1_inner_ty_fwd : ∀ W₁ W₂ : SMT.Dom,
          W₁.snd.fst = αx.toSMTType → W₂.snd.fst = βx.toSMTType →
          ∀ {D : SMT.Dom},
            ⟦P1_inner_fwd.abstract
              (Function.update (Function.update (Function.update Δctx R (some WR_fwd)) x (some W₁))
                y (some W₂))
              (hcov_P1_inner_updxy_fwd W₁ W₂)⟧ˢ = some D → D.snd.fst = SMTType.bool := by
        intro W₁ W₂ hW₁_ty hW₂_ty D hD
        have hW₁_mem : W₁.fst ∈ ⟦αx.toSMTType⟧ᶻ := by rw [← hW₁_ty]; exact W₁.2.2
        have hW₂_mem : W₂.fst ∈ ⟦βx.toSMTType⟧ᶻ := by rw [← hW₂_ty]; exact W₂.2.2
        obtain ⟨DR, hDR, hDR_ty⟩ := denote_app_var_pair_var_var rfl hW₁_ty hW₁_mem hW₂_ty hW₂_mem
          (WR := WR_fwd) (Wx := W₁) (Wy := W₂)
        obtain ⟨DA, _, _, hDA_den⟩ := hDA_Rxy_fwd W₁ W₂ hW₁_ty hW₁_mem
        change ⟦(Term.app A_enc (.var x)).abstract _ _⟧ˢ = some DA at hDA_den
        obtain ⟨_, DB, hDB_ty, _, hDB_den⟩ := den_app_B_y WR_fwd W₁ W₂ hW₂_ty hW₂_mem
        obtain ⟨Dand, hDand, hDand_ty⟩ := denote_and_some_bool_of_some_bool hDA_den ‹_› hDB_den hDB_ty
        obtain ⟨Dimp, hDimp, hDimp_ty⟩ := denote_imp_some_bool_of_some_bool hDR hDR_ty hDand hDand_ty
        suffices h : ⟦P1_inner_fwd.abstract _ _⟧ˢ = some Dimp by rw [h] at hD; cases hD; exact hDimp_ty
        simp only [hP1_inner_def_fwd, SMT.Term.abstract, Function.update,
          hR_ne_y, hR_ne_x, hx_ne_y, ↓reduceDIte, Option.get_some] at hDimp ⊢
        exact hDimp
      -- ── P2 inner body infrastructure ──
      set P2_inner_fwd := Term.imp
        (.and (.app (.var R) (.pair (.var x) (.var y)))
              (.app (.var R) (.pair (.var x) (.var y'))))
        (.eq (.var y) (.var y')) with hP2_inner_def_fwd
      have hcov_P2_inner_updxyy'_fwd : ∀ W₁ W₂ W₃ : SMT.Dom,
          RenamingContext.CoversFV
            (Function.update (Function.update (Function.update (Function.update Δctx R (some WR_fwd))
              x (some W₁)) y (some W₂)) y' (some W₃)) P2_inner_fwd := by
        intro W₁ W₂ W₃ v hv
        rw [hP2_inner_def_fwd, SMT.fv] at hv
        simp only [SMT.fv, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, false_or] at hv
        by_cases hvR : v = R; · subst hvR; simp [Function.update, hR_ne_x, hR_ne_y, hR_ne_y']
        by_cases hvx : v = x; · subst hvx; simp [Function.update, hx_ne_y, hx_ne_y']
        by_cases hvy : v = y; · subst hvy; simp [Function.update, hy_ne_y']
        by_cases hvy' : v = y'; · subst hvy'; simp [Function.update]
        · rw [Function.update_of_ne hvy', Function.update_of_ne hvy,
              Function.update_of_ne hvx, Function.update_of_ne hvR]
          have hv_body : v ∈ SMT.fv pfun_body := by
            rw [hpfun_body_def]; apply SMT.fv.mem_and; right
            rw [hP2_def]; apply SMT.fv.mem_forall
            refine ⟨?_, by simp; push_neg; exact ⟨hvx, hvy, hvy'⟩⟩
            simp only [hP2_inner_def_fwd, SMT.fv, List.mem_append, List.mem_cons,
              List.mem_nil_iff, or_false]; exact hv
          have hv_lambda : v ∈ SMT.fv (Term.lambda [R] [τR] pfun_body) := by
            rw [SMT.fv]; exact List.mem_filter.mpr ⟨hv_body, by simp [List.mem_singleton]; exact hvR⟩
          exact hcov v hv_lambda
      have hgo_cov_P2_inner_fwd : ∀ v ∈ SMT.fv P2_inner_fwd, v ∉ [x, y, y'] →
          ((Function.update Δctx R (some WR_fwd)) v).isSome = true := by
        intro v hv hvxyy'
        have hvx : v ≠ x := by intro h; exact hvxyy' (List.mem_cons.mpr (Or.inl h))
        have hvy : v ≠ y := by
          intro h; exact hvxyy' (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl h))))
        have hvy' : v ≠ y' := by
          intro h; exact hvxyy' (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr
            (List.mem_cons.mpr (Or.inl h))))))
        by_cases hvR : v = R; · subst hvR; simp [Function.update]
        · rw [Function.update_of_ne hvR]
          have hv_body : v ∈ SMT.fv pfun_body := by
            rw [hpfun_body_def]; apply SMT.fv.mem_and; right
            rw [hP2_def]; apply SMT.fv.mem_forall; refine ⟨hv, ?_⟩
            simp [List.mem_cons]; push_neg; exact ⟨hvx, hvy, hvy'⟩
          have hv_lambda : v ∈ SMT.fv (Term.lambda [R] [τR] pfun_body) := by
            rw [SMT.fv]; exact List.mem_filter.mpr ⟨hv_body, by simpa using hvR⟩
          exact hcov v hv_lambda
      have hP2_inner_total_fwd : ∀ W₁ W₂ W₃ : SMT.Dom,
          W₁.snd.fst = αx.toSMTType → W₂.snd.fst = βx.toSMTType → W₃.snd.fst = βx.toSMTType →
          ⟦P2_inner_fwd.abstract
            (Function.update (Function.update (Function.update (Function.update Δctx R (some WR_fwd))
              x (some W₁)) y (some W₂)) y' (some W₃))
            (hcov_P2_inner_updxyy'_fwd W₁ W₂ W₃)⟧ˢ.isSome = true := by
        intro W₁ W₂ W₃ hW₁_ty hW₂_ty hW₃_ty
        have hW₁_mem : W₁.fst ∈ ⟦αx.toSMTType⟧ᶻ := by rw [← hW₁_ty]; exact W₁.2.2
        have hW₂_mem : W₂.fst ∈ ⟦βx.toSMTType⟧ᶻ := by rw [← hW₂_ty]; exact W₂.2.2
        have hW₃_mem : W₃.fst ∈ ⟦βx.toSMTType⟧ᶻ := by rw [← hW₃_ty]; exact W₃.2.2
        obtain ⟨DRxy, hDRxy, hDRxy_ty⟩ := denote_app_var_pair_var_var rfl hW₁_ty hW₁_mem hW₂_ty hW₂_mem
          (WR := WR_fwd) (Wx := W₁) (Wy := W₂)
        obtain ⟨DRxy', hDRxy', hDRxy'_ty⟩ := denote_app_var_pair_var_var rfl hW₁_ty hW₁_mem hW₃_ty hW₃_mem
          (WR := WR_fwd) (Wx := W₁) (Wy := W₃)
        obtain ⟨Dand, hDand, hDand_ty⟩ :=
          denote_and_some_bool_of_some_bool hDRxy hDRxy_ty hDRxy' hDRxy'_ty
        have hDeq_y : ⟦SMT.PHOAS.Term.var W₂⟧ˢ = some W₂ := rfl
        have hDeq_y' : ⟦SMT.PHOAS.Term.var W₃⟧ˢ = some W₃ := rfl
        obtain ⟨Deq, hDeq, hDeq_ty⟩ := denote_eq_some_bool hDeq_y hDeq_y' (by rw [hW₂_ty, hW₃_ty])
        obtain ⟨Dimp, hDimp, _⟩ := denote_imp_some_bool_of_some_bool hDand hDand_ty hDeq hDeq_ty
        suffices h : ⟦P2_inner_fwd.abstract _ _⟧ˢ = some Dimp from
          Option.isSome_iff_exists.mpr ⟨Dimp, h⟩
        simp only [hP2_inner_def_fwd, SMT.Term.abstract, Function.update,
          hR_ne_y, hR_ne_x, hR_ne_y', hx_ne_y, hx_ne_y', hy_ne_y', ↓reduceDIte,
          Option.get_some] at hDimp ⊢
        exact hDimp
      have hP2_inner_ty_fwd : ∀ W₁ W₂ W₃ : SMT.Dom,
          W₁.snd.fst = αx.toSMTType → W₂.snd.fst = βx.toSMTType → W₃.snd.fst = βx.toSMTType →
          ∀ {D : SMT.Dom},
            ⟦P2_inner_fwd.abstract
              (Function.update (Function.update (Function.update (Function.update Δctx R (some WR_fwd))
                x (some W₁)) y (some W₂)) y' (some W₃))
              (hcov_P2_inner_updxyy'_fwd W₁ W₂ W₃)⟧ˢ = some D → D.snd.fst = SMTType.bool := by
        intro W₁ W₂ W₃ hW₁_ty hW₂_ty hW₃_ty D hD
        have hW₁_mem : W₁.fst ∈ ⟦αx.toSMTType⟧ᶻ := by rw [← hW₁_ty]; exact W₁.2.2
        have hW₂_mem : W₂.fst ∈ ⟦βx.toSMTType⟧ᶻ := by rw [← hW₂_ty]; exact W₂.2.2
        have hW₃_mem : W₃.fst ∈ ⟦βx.toSMTType⟧ᶻ := by rw [← hW₃_ty]; exact W₃.2.2
        obtain ⟨DRxy, hDRxy, hDRxy_ty⟩ := denote_app_var_pair_var_var rfl hW₁_ty hW₁_mem hW₂_ty hW₂_mem
          (WR := WR_fwd) (Wx := W₁) (Wy := W₂)
        obtain ⟨DRxy', hDRxy', hDRxy'_ty⟩ := denote_app_var_pair_var_var rfl hW₁_ty hW₁_mem hW₃_ty hW₃_mem
          (WR := WR_fwd) (Wx := W₁) (Wy := W₃)
        obtain ⟨Dand, hDand, hDand_ty⟩ :=
          denote_and_some_bool_of_some_bool hDRxy hDRxy_ty hDRxy' hDRxy'_ty
        have hDeq_y : ⟦SMT.PHOAS.Term.var W₂⟧ˢ = some W₂ := rfl
        have hDeq_y' : ⟦SMT.PHOAS.Term.var W₃⟧ˢ = some W₃ := rfl
        obtain ⟨Deq, hDeq, hDeq_ty⟩ := denote_eq_some_bool hDeq_y hDeq_y' (by rw [hW₂_ty, hW₃_ty])
        obtain ⟨Dimp, hDimp, hDimp_ty⟩ := denote_imp_some_bool_of_some_bool hDand hDand_ty hDeq hDeq_ty
        suffices h : ⟦P2_inner_fwd.abstract _ _⟧ˢ = some Dimp by rw [h] at hD; cases hD; exact hDimp_ty
        simp only [hP2_inner_def_fwd, SMT.Term.abstract, Function.update,
          hR_ne_y, hR_ne_x, hR_ne_y', hx_ne_y, hx_ne_y', hy_ne_y', ↓reduceDIte,
          Option.get_some] at hDimp ⊢
        exact hDimp
      -- ── Forward: prove g ⊆ X.prod Y using P1 = zftrue ──
      have hmk_func_fwd : ⟦(αx ×ᴮ βx).toSMTType⟧ᶻ.IsFunc 𝔹 (mk_cg hg_αprod) := by
        have h := mk_cg_mem hg_αprod
        rw [hαprod_def] at h; simp only [BType.toSMTType, SMTType.toZFSet] at h
        exact ZFSet.mem_funs.mp h
      have hg_sub_XY : g ⊆ X.prod Y := by
        intro z hz
        have hz_prod := hg_sub hz
        rw [BType.toZFSet, ZFSet.mem_prod] at hz_prod
        obtain ⟨a, ha_mem, b, hb_mem, hab_eq⟩ := hz_prod; subst hab_eq
        rw [ZFSet.mem_prod]
        -- Form canonical witnesses
        have ha_smt : ((BType.canonicalIsoSMTType αx).1.fapply
            (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType αx).2.1)
            ⟨a, by rw [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType αx).2.1]; exact ha_mem⟩).1 ∈
            ⟦αx.toSMTType⟧ᶻ := ZFSet.fapply_mem_range _ _
        have hb_smt : ((BType.canonicalIsoSMTType βx).1.fapply
            (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType βx).2.1)
            ⟨b, by rw [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType βx).2.1]; exact hb_mem⟩).1 ∈
            ⟦βx.toSMTType⟧ᶻ := ZFSet.fapply_mem_range _ _
        set ca := (BType.canonicalIsoSMTType αx).1.fapply
          (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType αx).2.1)
          ⟨a, by rw [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType αx).2.1]; exact ha_mem⟩
        set cb := (BType.canonicalIsoSMTType βx).1.fapply
          (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType βx).2.1)
          ⟨b, by rw [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType βx).2.1]; exact hb_mem⟩
        let W₁ : SMT.Dom := ⟨ca, αx.toSMTType, ha_smt⟩
        let W₂ : SMT.Dom := ⟨cb, βx.toSMTType, hb_smt⟩
        -- Apply funBinaryForallTrueAt
        obtain ⟨D_P1, hD_P1_den, hD_P1_true⟩ := funBinaryForallTrueAt
          hcov_P1_fwd hgo_cov_P1_inner_fwd hcov_P1_inner_updxy_fwd
          hP1_inner_total_fwd hP1_inner_ty_fwd hD1_fwd_den hD1_fwd_true W₁ W₂ rfl rfl
        -- Compute sub-term denotations at (W₁, W₂)
        obtain ⟨DR, hDR, hDR_ty⟩ := denote_app_var_pair_var_var rfl (show W₁.2.1 = _ from rfl) ha_smt
          (show W₂.2.1 = _ from rfl) hb_smt (WR := WR_fwd) (Wx := W₁) (Wy := W₂)
        obtain ⟨DA, hDA_ty, hDA_val, hDA_den⟩ := hDA_Rxy_fwd W₁ W₂ rfl ha_smt
        change ⟦(Term.app A_enc (.var x)).abstract _ _⟧ˢ = some DA at hDA_den
        obtain ⟨_, DB, hDB_ty, hDB_val, hDB_den⟩ := den_app_B_y WR_fwd W₁ W₂ rfl hb_smt
        obtain ⟨Dand, hDand, hDand_ty⟩ := denote_and_some_bool_of_some_bool hDA_den hDA_ty hDB_den hDB_ty
        obtain ⟨Dimp, hDimp, hDimp_ty⟩ := denote_imp_some_bool_of_some_bool hDR hDR_ty hDand hDand_ty
        -- Match D_P1 = Dimp
        have hDimp_abs : ⟦P1_inner_fwd.abstract
            (Function.update (Function.update (Function.update Δctx R (some WR_fwd)) x (some W₁))
              y (some W₂))
            (hcov_P1_inner_updxy_fwd W₁ W₂)⟧ˢ = some Dimp := by
          simp only [hP1_inner_def_fwd, SMT.Term.abstract, Function.update,
            hR_ne_y, hR_ne_x, hx_ne_y, ↓reduceDIte, Option.get_some] at hDimp ⊢; exact hDimp
        have hD_eq : D_P1 = Dimp := Option.some_injective _ (hD_P1_den.symm.trans hDimp_abs)
        rw [hD_eq] at hD_P1_true
        -- Show R(pair W₁ W₂) = zftrue from pair a b ∈ g
        have hpair_ab_mem_g : a.pair b ∈ g := hz
        have hR_true : DR.fst = zftrue := by
          have hpair_ab_in_αprod : a.pair b ∈ ⟦BType.prod αx βx⟧ᶻ := by
            rw [BType.toZFSet, ZFSet.mem_prod]; exact ⟨a, ha_mem, b, hb_mem, rfl⟩
          -- Get fapply = zftrue from membership via mem_retract_set_iff
          have h_fapply_true :=
            (mem_retract_set_iff_app_canonical_eq_zftrue hmk_func_fwd (retract_cg hg_αprod)
              hpair_ab_in_αprod).mp hpair_ab_mem_g
          -- Rewrite canonical(prod, a.pair b) to ca.pair cb
          have hcab_mem_smt : (ca.1).pair (cb.1) ∈ ⟦(BType.prod αx βx).toSMTType⟧ᶻ := by
            rw [BType.toSMTType, SMTType.toZFSet, ZFSet.pair_mem_prod]; exact ⟨ha_smt, hb_smt⟩
          have hretract_prod : retract (.prod αx βx) ((ca.1).pair (cb.1)) = a.pair b := by
            simp only [retract, ZFSet.π₁_pair, ZFSet.π₂_pair, ca, cb]
            congr 1
            · exact retract_of_canonical αx ha_mem
            · exact retract_of_canonical βx hb_mem
          have hcan := canonical_of_retract (.prod αx βx) hcab_mem_smt
          simp only [hretract_prod] at hcan
          simp only [hcan] at h_fapply_true
          -- Construct explicit PHOAS denotation to identify DR.fst
          have hpair_mem_τR : (ca.1).pair (cb.1) ∈ ⟦pairTy⟧ᶻ := by
            rw [hpairTy_def, SMTType.toZFSet, ZFSet.pair_mem_prod]; exact ⟨ha_smt, hb_smt⟩
          have hWR_pfunc : (mk_cg hg_αprod).IsPFunc ⟦pairTy⟧ᶻ ⟦SMTType.bool⟧ᶻ :=
            ZFSet.is_func_is_pfunc hmk_func_fwd
          have hpair_dom : (ca.1).pair (cb.1) ∈ (mk_cg hg_αprod).Dom := by
            erw [ZFSet.is_func_dom_eq hmk_func_fwd]; exact hpair_mem_τR
          have hden_app :
              ⟦SMT.PHOAS.Term.app (.var WR_fwd) (.pair (.var W₁) (.var W₂))⟧ˢ =
              some ⟨(ZFSet.fapply (mk_cg hg_αprod) hWR_pfunc
                      ⟨(ca.1).pair (cb.1), hpair_dom⟩).val,
                    .bool,
                    (ZFSet.fapply (mk_cg hg_αprod) hWR_pfunc
                      ⟨(ca.1).pair (cb.1), hpair_dom⟩).prop⟩ := by
            show SMT.denote (SMT.PHOAS.Term.app (.var WR_fwd)
              (.pair (.var W₁) (.var W₂))) = _
            simp only [SMT.denote, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
              mem_sep, Option.failure_eq_none, dite_eq_ite, WR_fwd, hτR_def, hpairTy_def]
            simp only [show W₁.2.1 = αx.toSMTType from rfl,
              show W₂.2.1 = βx.toSMTType from rfl, if_true]
            unfold pairTy at hWR_pfunc
            rw [dif_pos hWR_pfunc, dif_pos]
            and_intros
            · erw [ZFSet.is_func_dom_eq hmk_func_fwd, BType.toSMTType] at hpair_dom
              exact hpair_dom
            · simp only [ZFSet.Dom, ZFSet.mem_sep] at hpair_dom; exact hpair_dom.2
          rw [hden_app] at hDR
          have hDR_eq := Option.some_injective _ hDR
          rw [← congrArg (·.fst) hDR_eq]
          exact h_fapply_true
        -- Extract a ∈ X and b ∈ Y from hR_true + hD_P1_true
        -- imp(R, and(A,B)) = zftrue and R = zftrue → and(A,B) = zftrue
        have hDand_true : Dand.fst = zftrue :=
          denote_imp_consequent_of_antecedent_zftrue hDR hDR_ty hR_true
            hDand hDand_ty hDimp hD_P1_true
        -- and(A,B) = zftrue → A = zftrue and B = zftrue
        have ⟨hDA_true, hDB_true⟩ := denote_and_both_zftrue_of_zftrue
          hDA_den hDA_ty hDB_den hDB_ty hDand hDand_true
        have ha_X : a ∈ X := by
          rw [hDA_val] at hDA_true
          exact (mem_retract_set_iff_app_canonical_eq_zftrue hdenA_func hX_def.symm
            ha_mem).mpr hDA_true
        have hb_Y : b ∈ Y := by
          rw [hDB_val] at hDB_true
          exact (mem_retract_set_iff_app_canonical_eq_zftrue hdenB_func hY_def.symm
            hb_mem).mpr hDB_true
        exact ⟨a, ha_X, b, hb_Y, rfl⟩
      -- IsPFunc: g ⊆ X.prod Y ∧ functionality from P2 via funTernaryForallTrueAt
      refine ⟨ZFSet.mem_powerset.mpr hg_sub_XY, hg_sub_XY, ?_⟩
      intro a b₁ hab₁ b₂ hab₂
      -- a, b₁, b₂ are in the B type universe
      have hab₁_prod := hg_sub hab₁
      rw [BType.toZFSet, ZFSet.mem_prod] at hab₁_prod
      obtain ⟨a', ha'_mem, b₁', hb₁'_mem, hab₁_eq⟩ := hab₁_prod
      have ha_eq : a = a' := (ZFSet.pair_inj.mp hab₁_eq).1
      have hb₁_eq : b₁ = b₁' := (ZFSet.pair_inj.mp hab₁_eq).2
      subst ha_eq; subst hb₁_eq
      have ha_mem : a ∈ ⟦αx⟧ᶻ := ha'_mem
      have hb₁_mem : b₁ ∈ ⟦βx⟧ᶻ := hb₁'_mem
      have hab₂_prod := hg_sub hab₂
      rw [BType.toZFSet, ZFSet.mem_prod] at hab₂_prod
      obtain ⟨a'', ha''_mem, b₂', hb₂'_mem, hab₂_eq⟩ := hab₂_prod
      have ha_eq₂ : a = a'' := (ZFSet.pair_inj.mp hab₂_eq).1
      have hb₂_eq : b₂ = b₂' := (ZFSet.pair_inj.mp hab₂_eq).2
      subst ha_eq₂; subst hb₂_eq
      have hb₂_mem : b₂ ∈ ⟦βx⟧ᶻ := hb₂'_mem
      -- Form canonical witnesses
      set ca_func := (BType.canonicalIsoSMTType αx).1.fapply
        (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType αx).2.1)
        ⟨a, by rw [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType αx).2.1]; exact ha_mem⟩
      set cb₁_func := (BType.canonicalIsoSMTType βx).1.fapply
        (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType βx).2.1)
        ⟨b₁, by rw [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType βx).2.1]; exact hb₁_mem⟩
      set cb₂_func := (BType.canonicalIsoSMTType βx).1.fapply
        (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType βx).2.1)
        ⟨b₂, by rw [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType βx).2.1]; exact hb₂_mem⟩
      have ha_smt_func : ca_func.val ∈ ⟦αx.toSMTType⟧ᶻ := ZFSet.fapply_mem_range _ _
      have hb₁_smt_func : cb₁_func.val ∈ ⟦βx.toSMTType⟧ᶻ := ZFSet.fapply_mem_range _ _
      have hb₂_smt_func : cb₂_func.val ∈ ⟦βx.toSMTType⟧ᶻ := ZFSet.fapply_mem_range _ _
      let W₁_f : SMT.Dom := ⟨ca_func, αx.toSMTType, ha_smt_func⟩
      let W₂_f : SMT.Dom := ⟨cb₁_func, βx.toSMTType, hb₁_smt_func⟩
      let W₃_f : SMT.Dom := ⟨cb₂_func, βx.toSMTType, hb₂_smt_func⟩
      -- Apply funTernaryForallTrueAt to P2
      obtain ⟨D_P2, hD_P2_den, hD_P2_true⟩ := funTernaryForallTrueAt
        hcov_P2_fwd hgo_cov_P2_inner_fwd hcov_P2_inner_updxyy'_fwd
        hP2_inner_total_fwd hP2_inner_ty_fwd hD2_fwd_den hD2_fwd_true W₁_f W₂_f W₃_f rfl rfl rfl
      -- Compute R(a, b₁) and R(a, b₂) denotations
      obtain ⟨DRxy, hDRxy, hDRxy_ty⟩ := denote_app_var_pair_var_var rfl
        (show W₁_f.2.1 = _ from rfl) ha_smt_func
        (show W₂_f.2.1 = _ from rfl) hb₁_smt_func
        (WR := WR_fwd) (Wx := W₁_f) (Wy := W₂_f)
      obtain ⟨DRxy', hDRxy', hDRxy'_ty⟩ := denote_app_var_pair_var_var rfl
        (show W₁_f.2.1 = _ from rfl) ha_smt_func
        (show W₃_f.2.1 = _ from rfl) hb₂_smt_func
        (WR := WR_fwd) (Wx := W₁_f) (Wy := W₃_f)
      -- eq(y, y') denotation
      have hDeq_y : ⟦SMT.PHOAS.Term.var W₂_f⟧ˢ = some W₂_f := rfl
      have hDeq_y' : ⟦SMT.PHOAS.Term.var W₃_f⟧ˢ = some W₃_f := rfl
      obtain ⟨Deq, hDeq, hDeq_ty⟩ := denote_eq_some_bool hDeq_y hDeq_y' rfl
      -- and(R(a,b₁), R(a,b₂))
      obtain ⟨Dand_P2, hDand_P2, hDand_P2_ty⟩ :=
        denote_and_some_bool_of_some_bool hDRxy hDRxy_ty hDRxy' hDRxy'_ty
      -- imp(and, eq)
      obtain ⟨Dimp_P2, hDimp_P2, hDimp_P2_ty⟩ :=
        denote_imp_some_bool_of_some_bool hDand_P2 hDand_P2_ty hDeq hDeq_ty
      -- Match D_P2 = Dimp_P2
      have hDimp_P2_abs : ⟦P2_inner_fwd.abstract
          (Function.update (Function.update (Function.update (Function.update Δctx R (some WR_fwd))
            x (some W₁_f)) y (some W₂_f)) y' (some W₃_f))
          (hcov_P2_inner_updxyy'_fwd W₁_f W₂_f W₃_f)⟧ˢ = some Dimp_P2 := by
        simp only [hP2_inner_def_fwd, SMT.Term.abstract, Function.update,
          hR_ne_y, hR_ne_x, hR_ne_y', hx_ne_y, hx_ne_y', hy_ne_y', ↓reduceDIte,
          Option.get_some] at hDimp_P2 ⊢; exact hDimp_P2
      have hD_P2_eq : D_P2 = Dimp_P2 :=
        Option.some_injective _ (hD_P2_den.symm.trans hDimp_P2_abs)
      rw [hD_P2_eq] at hD_P2_true
      -- Show R(a, b₁) = zftrue from a.pair b₁ ∈ g
      have hpair_ab₁_in_αprod : a.pair b₁ ∈ ⟦BType.prod αx βx⟧ᶻ := by
        rw [BType.toZFSet, ZFSet.mem_prod]; exact ⟨a, ha_mem, b₁, hb₁_mem, rfl⟩
      have hR_b₁_true : DRxy.fst = zftrue := by
        have h_fapply_true :=
          (mem_retract_set_iff_app_canonical_eq_zftrue hmk_func_fwd (retract_cg hg_αprod)
            hpair_ab₁_in_αprod).mp hab₁
        have hcab₁_mem_smt : ca_func.val.pair cb₁_func.val ∈ ⟦(BType.prod αx βx).toSMTType⟧ᶻ := by
          rw [BType.toSMTType, SMTType.toZFSet, ZFSet.pair_mem_prod]
          exact ⟨ha_smt_func, hb₁_smt_func⟩
        have hretract_prod : retract (.prod αx βx) (ca_func.val.pair cb₁_func.val) = a.pair b₁ := by
          simp only [retract, ZFSet.π₁_pair, ZFSet.π₂_pair]
          congr 1
          · exact retract_of_canonical αx ha_mem
          · exact retract_of_canonical βx hb₁_mem
        have hcan := canonical_of_retract (.prod αx βx) hcab₁_mem_smt
        simp only [hretract_prod] at hcan
        simp only [hcan] at h_fapply_true
        -- Match via PHOAS denotation
        have hpair_mem_τR : ca_func.val.pair cb₁_func.val ∈ ⟦pairTy⟧ᶻ := by
          rw [hpairTy_def, SMTType.toZFSet, ZFSet.pair_mem_prod]
          exact ⟨ha_smt_func, hb₁_smt_func⟩
        have hWR_pfunc : (mk_cg hg_αprod).IsPFunc ⟦pairTy⟧ᶻ ⟦SMTType.bool⟧ᶻ :=
          ZFSet.is_func_is_pfunc hmk_func_fwd
        have hpair_dom : ca_func.val.pair cb₁_func.val ∈ (mk_cg hg_αprod).Dom := by
          erw [ZFSet.is_func_dom_eq hmk_func_fwd]; exact hpair_mem_τR
        have hden_app :
            ⟦SMT.PHOAS.Term.app (.var WR_fwd) (.pair (.var W₁_f) (.var W₂_f))⟧ˢ =
            some ⟨(ZFSet.fapply (mk_cg hg_αprod) hWR_pfunc
                    ⟨ca_func.val.pair cb₁_func.val, hpair_dom⟩).val,
                  .bool,
                  (ZFSet.fapply (mk_cg hg_αprod) hWR_pfunc
                    ⟨ca_func.val.pair cb₁_func.val, hpair_dom⟩).prop⟩ := by
          show SMT.denote (SMT.PHOAS.Term.app (.var WR_fwd)
            (.pair (.var W₁_f) (.var W₂_f))) = _
          simp only [SMT.denote, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
            mem_sep, Option.failure_eq_none, dite_eq_ite, WR_fwd, hτR_def, hpairTy_def]
          simp only [show W₁_f.2.1 = αx.toSMTType from rfl,
            show W₂_f.2.1 = βx.toSMTType from rfl, if_true]
          unfold pairTy at hWR_pfunc
          rw [dif_pos hWR_pfunc, dif_pos]
          and_intros
          · erw [ZFSet.is_func_dom_eq hmk_func_fwd, BType.toSMTType] at hpair_dom
            exact hpair_dom
          · simp only [ZFSet.Dom, ZFSet.mem_sep] at hpair_dom; exact hpair_dom.2
        rw [hden_app] at hDRxy
        have hDRxy_eq := Option.some_injective _ hDRxy
        rw [← congrArg (·.fst) hDRxy_eq]
        exact h_fapply_true
      -- Show R(a, b₂) = zftrue from a.pair b₂ ∈ g
      have hpair_ab₂_in_αprod : a.pair b₂ ∈ ⟦BType.prod αx βx⟧ᶻ := by
        rw [BType.toZFSet, ZFSet.mem_prod]; exact ⟨a, ha_mem, b₂, hb₂_mem, rfl⟩
      have hR_b₂_true : DRxy'.fst = zftrue := by
        have h_fapply_true :=
          (mem_retract_set_iff_app_canonical_eq_zftrue hmk_func_fwd (retract_cg hg_αprod)
            hpair_ab₂_in_αprod).mp hab₂
        have hcab₂_mem_smt : ca_func.val.pair cb₂_func.val ∈ ⟦(BType.prod αx βx).toSMTType⟧ᶻ := by
          rw [BType.toSMTType, SMTType.toZFSet, ZFSet.pair_mem_prod]
          exact ⟨ha_smt_func, hb₂_smt_func⟩
        have hretract_prod : retract (.prod αx βx) (ca_func.val.pair cb₂_func.val) = a.pair b₂ := by
          simp only [retract, ZFSet.π₁_pair, ZFSet.π₂_pair]
          congr 1
          · exact retract_of_canonical αx ha_mem
          · exact retract_of_canonical βx hb₂_mem
        have hcan := canonical_of_retract (.prod αx βx) hcab₂_mem_smt
        simp only [hretract_prod] at hcan
        simp only [hcan] at h_fapply_true
        have hpair_mem_τR : ca_func.val.pair cb₂_func.val ∈ ⟦pairTy⟧ᶻ := by
          rw [hpairTy_def, SMTType.toZFSet, ZFSet.pair_mem_prod]
          exact ⟨ha_smt_func, hb₂_smt_func⟩
        have hWR_pfunc : (mk_cg hg_αprod).IsPFunc ⟦pairTy⟧ᶻ ⟦SMTType.bool⟧ᶻ :=
          ZFSet.is_func_is_pfunc hmk_func_fwd
        have hpair_dom : ca_func.val.pair cb₂_func.val ∈ (mk_cg hg_αprod).Dom := by
          erw [ZFSet.is_func_dom_eq hmk_func_fwd]; exact hpair_mem_τR
        have hden_app :
            ⟦SMT.PHOAS.Term.app (.var WR_fwd) (.pair (.var W₁_f) (.var W₃_f))⟧ˢ =
            some ⟨(ZFSet.fapply (mk_cg hg_αprod) hWR_pfunc
                    ⟨ca_func.val.pair cb₂_func.val, hpair_dom⟩).val,
                  .bool,
                  (ZFSet.fapply (mk_cg hg_αprod) hWR_pfunc
                    ⟨ca_func.val.pair cb₂_func.val, hpair_dom⟩).prop⟩ := by
          show SMT.denote (SMT.PHOAS.Term.app (.var WR_fwd)
            (.pair (.var W₁_f) (.var W₃_f))) = _
          simp only [SMT.denote, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
            mem_sep, Option.failure_eq_none, dite_eq_ite, WR_fwd, hτR_def, hpairTy_def]
          simp only [show W₁_f.2.1 = αx.toSMTType from rfl,
            show W₃_f.2.1 = βx.toSMTType from rfl, if_true]
          unfold pairTy at hWR_pfunc
          rw [dif_pos hWR_pfunc, dif_pos]
          and_intros
          · erw [ZFSet.is_func_dom_eq hmk_func_fwd, BType.toSMTType] at hpair_dom
            exact hpair_dom
          · simp only [ZFSet.Dom, ZFSet.mem_sep] at hpair_dom; exact hpair_dom.2
        rw [hden_app] at hDRxy'
        have hDRxy'_eq := Option.some_injective _ hDRxy'
        rw [← congrArg (·.fst) hDRxy'_eq]
        exact h_fapply_true
      -- From imp(and(R_b₁_true, R_b₂_true), eq(b₁, b₂)) = zftrue, extract eq = zftrue
      have hDand_P2_true : Dand_P2.fst = zftrue := by
        have hand_true := denote_and_eq_zftrue_of_some_zftrue hDRxy hDRxy_ty hR_b₁_true
          hDRxy' hDRxy'_ty hR_b₂_true
        exact congrArg (·.fst) (Option.some_injective _ (hDand_P2.symm.trans hand_true))
      -- imp(and_true, eq) = zftrue and antecedent true → eq = zftrue
      have hDeq_true : Deq.fst = zftrue :=
        denote_imp_consequent_of_antecedent_zftrue hDand_P2 hDand_P2_ty hDand_P2_true
          hDeq hDeq_ty hDimp_P2 hD_P2_true
      -- eq = zftrue → cb₁ = cb₂
      have hcb_eq : (↑cb₁_func : ZFSet) = ↑cb₂_func :=
        denote_eq_true_implies_fst_eq hDeq_y hDeq_y' rfl hDeq hDeq_true
      -- Injectivity of canonical: b₁ = b₂
      have hret_b₁ : retract βx cb₁_func.val = b₁ :=
        retract_of_canonical βx hb₁_mem
      have hret_b₂ : retract βx cb₂_func.val = b₂ :=
        retract_of_canonical βx hb₂_mem
      rw [← hret_b₁, ← hret_b₂, hcb_eq]
    · -- (←) backward direction: g ∈ 𝒫(X×Y) ∧ IsPFunc g X Y → g ∈ retract αprod.set lamVal.fst
      intro ⟨hg_pw, hg_ispfunc⟩
      have hX_sub : X ⊆ ⟦αx⟧ᶻ := fun a ha => by
        change a ∈ retract (BType.set αx) den_A.fst at ha
        simp only [retract, ZFSet.mem_sep] at ha; exact ha.1
      have hY_sub : Y ⊆ ⟦βx⟧ᶻ := fun b hb => by
        change b ∈ retract (BType.set βx) den_B.fst at hb
        simp only [retract, ZFSet.mem_sep] at hb; exact hb.1
      have hg_sub_XY : g ⊆ X.prod Y := ZFSet.mem_powerset.mp hg_pw
      have hg_sub_prod : g ⊆ ⟦BType.prod αx βx⟧ᶻ := by
        intro z hz; have hz' := hg_sub_XY hz
        rw [BType.toZFSet]
        rw [ZFSet.mem_prod] at hz' ⊢
        obtain ⟨a, ha, b, hb, hab⟩ := hz'
        exact ⟨a, hX_sub ha, b, hY_sub hb, hab⟩
      have hg_αprod : g ∈ ⟦αprod⟧ᶻ := ZFSet.mem_powerset.mpr hg_sub_prod
      rw [fapply_iff_g hg_αprod hlamVal_func]
      obtain ⟨Dbody_bwd, hden_body_bwd, hfapply_eq_bwd⟩ :=
        hlamVal_app (mk_cg hg_αprod) (mk_cg_mem hg_αprod)
      rw [hfapply_eq_bwd]
      -- Need: Dbody_bwd.fst = zftrue
      -- The body is and(P1, P2) evaluated at R := canonical(g).
      -- P1 encodes g ⊆ X×Y and P2 encodes functionality. Both follow from hg_ispfunc.
      -- We derive the result by constructing the zftrue denotation explicitly and matching.
      -- Strategy: apply funBinaryForallEqZftrue for P1, funTernaryForallEqZftrue for P2.
      -- The body_true argument uses denote_congr_of_agreesOnFV to lift sub-term denotations.
      let WR_bwd : SMT.Dom := ⟨mk_cg hg_αprod, τR, mk_cg_mem hg_αprod⟩
      have hcov_P1_bwd : RenamingContext.CoversFV (Function.update Δctx R (some WR_bwd)) P1 :=
        fun v hv => hcov_body_updR WR_bwd v (by rw [hpfun_body_def]; exact SMT.fv.mem_and (Or.inl hv))
      have hcov_P2_bwd : RenamingContext.CoversFV (Function.update Δctx R (some WR_bwd)) P2 :=
        fun v hv => hcov_body_updR WR_bwd v (by rw [hpfun_body_def]; exact SMT.fv.mem_and (Or.inr hv))
      have habs_eq_bwd : ⟦pfun_body.abstract (Function.update Δctx R (some WR_bwd)) (hcov_body_updR WR_bwd)⟧ˢ =
          ⟦(P1.abstract (Function.update Δctx R (some WR_bwd)) hcov_P1_bwd) ∧ˢ'
           (P2.abstract (Function.update Δctx R (some WR_bwd)) hcov_P2_bwd)⟧ˢ := by
        congr 1; show pfun_body.abstract _ _ = _; simp only [hpfun_body_def, SMT.Term.abstract]
      -- ── P1 = zftrue via funBinaryForallEqZftrue ──
      -- The inner body of P1 under [R,x,y] needs:
      -- 1) CoversFV (from hcov_body_updR/hcov_P1_bwd)
      -- 2) Totality (from den_app_A_x + den_app_B_y + compose)
      -- 3) Type = .bool (from sub-term types)
      -- 4) Value = zftrue (from IsPFunc via semantic bridge)
      -- We use denote_update_of_notMem to lift den_app_A_x from [R,x] to [R,x,y].
      -- y ∉ fv(app A_enc (var x)) because y ∉ fv(A_enc) and y ≠ x.
      have y_not_fv_appAx : y ∉ SMT.fv (Term.app A_enc (.var x)) := by
        simp only [SMT.fv, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false]
        push_neg; exact ⟨y_not_fv_A, Ne.symm hx_ne_y⟩
      -- Lift den_app_A_x to the [R,x,y] context via denote_update_of_notMem
      have hDA_Rxy : ∀ (W₁ W₂ : SMT.Dom) (hW₁_ty : W₁.snd.fst = αx.toSMTType) (hW₁_mem : W₁.fst ∈ ⟦αx.toSMTType⟧ᶻ),
          ∃ DA : SMT.Dom,
            DA.snd.fst = .bool ∧
            DA.fst = (ZFSet.fapply den_A.fst (ZFSet.is_func_is_pfunc hdenA_func)
              ⟨W₁.fst, by rw [ZFSet.is_func_dom_eq hdenA_func]; exact hW₁_mem⟩).1 ∧
            SMT.RenamingContext.denote
              (Function.update (Function.update (Function.update Δctx R (some WR_bwd)) x (some W₁)) y (some W₂))
              (Term.app A_enc (.var x))
              (SMT.RenamingContext.coversFV_update_of_notMem y_not_fv_appAx
                (den_app_A_x WR_bwd W₁ hW₁_ty hW₁_mem).choose) = some DA := by
        intro W₁ W₂ hW₁_ty hW₁_mem
        obtain ⟨hcov_appA, DA, hDA_ty, hDA_val, hDA_den⟩ := den_app_A_x WR_bwd W₁ hW₁_ty hW₁_mem
        refine ⟨DA, hDA_ty, hDA_val, ?_⟩
        rw [← SMT.RenamingContext.denote_update_of_notMem y_not_fv_appAx (h := hcov_appA)]
        exact hDA_den
      -- ── P1 inner body: totality, type, value ──
      set P1_inner := Term.imp (.app (.var R) (.pair (.var x) (.var y)))
        (.and (.app A_enc (.var x)) (.app B_enc (.var y))) with hP1_inner_def
      -- CoversFV for P1_inner under [R,x,y]
      have hcov_P1_inner_updxy : ∀ W₁ W₂ : SMT.Dom,
          RenamingContext.CoversFV
            (Function.update (Function.update (Function.update Δctx R (some WR_bwd)) x (some W₁)) y (some W₂))
            P1_inner := by
        intro W₁ W₂ v hv
        rw [hP1_inner_def, SMT.fv] at hv
        simp only [SMT.fv, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, false_or] at hv
        by_cases hvR : v = R; · subst hvR; simp [Function.update, hR_ne_x, hR_ne_y]
        by_cases hvx : v = x; · subst hvx; simp [Function.update, hx_ne_y]
        by_cases hvy : v = y; · subst hvy; simp [Function.update]
        · rw [Function.update_of_ne hvy, Function.update_of_ne hvx, Function.update_of_ne hvR]
          have hv_body : v ∈ SMT.fv pfun_body := by
            rw [hpfun_body_def]; apply SMT.fv.mem_and; left
            rw [hP1_def]; apply SMT.fv.mem_forall
            refine ⟨?_, by simp; push_neg; exact ⟨hvx, hvy⟩⟩
            simp only [hP1_inner_def, SMT.fv, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false]
            -- hv was destructured; reconstruct from the disjunction
            rcases hv with (rfl | rfl | rfl) | (h | rfl) | (h | rfl) <;> simp [hvy, hvx, hvR]
            <;> [left; right] <;> exact h
          have hv_lambda : v ∈ SMT.fv (Term.lambda [R] [τR] pfun_body) := by
            rw [SMT.fv]; exact List.mem_filter.mpr ⟨hv_body, by simpa using hvR⟩
          exact hcov v hv_lambda
      have hgo_cov_P1_inner : ∀ v ∈ SMT.fv P1_inner, v ∉ [x, y] →
          ((Function.update Δctx R (some WR_bwd)) v).isSome = true := by
        intro v hv hvxy
        have hvx : v ≠ x := by intro h; exact hvxy (List.mem_cons.mpr (Or.inl h))
        have hvy : v ≠ y := by intro h; exact hvxy (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl h))))
        by_cases hvR : v = R; · subst hvR; simp [Function.update]
        · rw [Function.update_of_ne hvR]
          have hv_body : v ∈ SMT.fv pfun_body := by
            rw [hpfun_body_def]; apply SMT.fv.mem_and; left
            rw [hP1_def]; apply SMT.fv.mem_forall; refine ⟨hv, ?_⟩
            simp [List.mem_cons]; push_neg; exact ⟨hvx, hvy⟩
          have hv_lambda : v ∈ SMT.fv (Term.lambda [R] [τR] pfun_body) := by
            rw [SMT.fv]; exact List.mem_filter.mpr ⟨hv_body, by simpa using hvR⟩
          exact hcov v hv_lambda
      -- P1 inner body totality/type/value via sub-term composition
      have hP1_inner_total : ∀ W₁ W₂ : SMT.Dom, W₁.snd.fst = αx.toSMTType → W₂.snd.fst = βx.toSMTType →
          ⟦P1_inner.abstract
            (Function.update (Function.update (Function.update Δctx R (some WR_bwd)) x (some W₁)) y (some W₂))
            (hcov_P1_inner_updxy W₁ W₂)⟧ˢ.isSome = true := by
        intro W₁ W₂ hW₁_ty hW₂_ty
        have hW₁_mem : W₁.fst ∈ ⟦αx.toSMTType⟧ᶻ := by rw [← hW₁_ty]; exact W₁.2.2
        have hW₂_mem : W₂.fst ∈ ⟦βx.toSMTType⟧ᶻ := by rw [← hW₂_ty]; exact W₂.2.2
        obtain ⟨DR, hDR, hDR_ty⟩ := denote_app_var_pair_var_var rfl hW₁_ty hW₁_mem hW₂_ty hW₂_mem
          (WR := WR_bwd) (Wx := W₁) (Wy := W₂)
        obtain ⟨DA, _, _, hDA_den⟩ := hDA_Rxy W₁ W₂ hW₁_ty hW₁_mem
        obtain ⟨_, DB, hDB_ty, _, hDB_den⟩ := den_app_B_y WR_bwd W₁ W₂ hW₂_ty hW₂_mem
        -- Lift DA_den from RenamingContext.denote to ⟦...abstract...⟧ˢ
        change ⟦(Term.app A_enc (.var x)).abstract _ _⟧ˢ = some DA at hDA_den
        obtain ⟨Dand, hDand, _⟩ := denote_and_some_bool_of_some_bool hDA_den ‹_› hDB_den hDB_ty
        obtain ⟨Dimp, hDimp, _⟩ := denote_imp_some_bool_of_some_bool hDR hDR_ty hDand ‹_›
        -- Connect P1_inner.abstract to the PHOAS imp
        suffices h : ⟦P1_inner.abstract _ _⟧ˢ = some Dimp from
          Option.isSome_iff_exists.mpr ⟨Dimp, h⟩
        simp only [hP1_inner_def, SMT.Term.abstract, Function.update,
          hR_ne_y, hR_ne_x, hx_ne_y, ↓reduceDIte, Option.get_some] at hDimp ⊢
        exact hDimp
      -- ── P1 inner body type = .bool ──
      have hP1_inner_ty : ∀ W₁ W₂ : SMT.Dom, W₁.snd.fst = αx.toSMTType → W₂.snd.fst = βx.toSMTType →
          ∀ {D : SMT.Dom},
            ⟦P1_inner.abstract
              (Function.update (Function.update (Function.update Δctx R (some WR_bwd)) x (some W₁)) y (some W₂))
              (hcov_P1_inner_updxy W₁ W₂)⟧ˢ = some D → D.snd.fst = SMTType.bool := by
        intro W₁ W₂ hW₁_ty hW₂_ty D hD
        have hW₁_mem : W₁.fst ∈ ⟦αx.toSMTType⟧ᶻ := by rw [← hW₁_ty]; exact W₁.2.2
        have hW₂_mem : W₂.fst ∈ ⟦βx.toSMTType⟧ᶻ := by rw [← hW₂_ty]; exact W₂.2.2
        obtain ⟨DR, hDR, hDR_ty⟩ := denote_app_var_pair_var_var rfl hW₁_ty hW₁_mem hW₂_ty hW₂_mem
          (WR := WR_bwd) (Wx := W₁) (Wy := W₂)
        obtain ⟨DA, _, _, hDA_den⟩ := hDA_Rxy W₁ W₂ hW₁_ty hW₁_mem
        change ⟦(Term.app A_enc (.var x)).abstract _ _⟧ˢ = some DA at hDA_den
        obtain ⟨_, DB, hDB_ty, _, hDB_den⟩ := den_app_B_y WR_bwd W₁ W₂ hW₂_ty hW₂_mem
        obtain ⟨Dand, hDand, hDand_ty⟩ := denote_and_some_bool_of_some_bool hDA_den ‹_› hDB_den hDB_ty
        obtain ⟨Dimp, hDimp, hDimp_ty⟩ := denote_imp_some_bool_of_some_bool hDR hDR_ty hDand hDand_ty
        suffices h : ⟦P1_inner.abstract _ _⟧ˢ = some Dimp by
          rw [h] at hD; cases hD; exact hDimp_ty
        simp only [hP1_inner_def, SMT.Term.abstract, Function.update,
          hR_ne_y, hR_ne_x, hx_ne_y, ↓reduceDIte, Option.get_some] at hDimp ⊢
        exact hDimp
      -- ── P1 inner body = zftrue for all W₁, W₂ ──
      have hP1_inner_true : ∀ W₁ W₂ : SMT.Dom, W₁.snd.fst = αx.toSMTType → W₂.snd.fst = βx.toSMTType →
          ∃ D : SMT.Dom,
            ⟦P1_inner.abstract
              (Function.update (Function.update (Function.update Δctx R (some WR_bwd)) x (some W₁)) y (some W₂))
              (hcov_P1_inner_updxy W₁ W₂)⟧ˢ = some D ∧ D.fst = zftrue := by
        intro W₁ W₂ hW₁_ty hW₂_ty
        have hW₁_mem : W₁.fst ∈ ⟦αx.toSMTType⟧ᶻ := by rw [← hW₁_ty]; exact W₁.2.2
        have hW₂_mem : W₂.fst ∈ ⟦βx.toSMTType⟧ᶻ := by rw [← hW₂_ty]; exact W₂.2.2
        obtain ⟨DR, hDR, hDR_ty⟩ := denote_app_var_pair_var_var rfl hW₁_ty hW₁_mem hW₂_ty hW₂_mem
          (WR := WR_bwd) (Wx := W₁) (Wy := W₂)
        obtain ⟨DA, hDA_ty, hDA_val, hDA_den⟩ := hDA_Rxy W₁ W₂ hW₁_ty hW₁_mem
        change ⟦(Term.app A_enc (.var x)).abstract _ _⟧ˢ = some DA at hDA_den
        obtain ⟨_, DB, hDB_ty, hDB_val, hDB_den⟩ := den_app_B_y WR_bwd W₁ W₂ hW₂_ty hW₂_mem
        -- Case analysis on DR.fst (application of R to the pair)
        have hDR_mem_𝔹 : DR.fst ∈ 𝔹 := by
          have := DR.snd.snd; rw [hDR_ty] at this; exact this
        rcases ZFSet.ZFBool.mem_𝔹_iff _ |>.mp hDR_mem_𝔹 with hDR_false | hDR_true
        · -- R(W₁,W₂) = zffalse → imp(false, _) = zftrue
          obtain ⟨Dand, hDand, hDand_ty⟩ := denote_and_some_bool_of_some_bool hDA_den ‹_› hDB_den hDB_ty
          have hDimp := denote_imp_eq_zftrue_of_zffalse_left hDR hDR_ty hDR_false hDand hDand_ty
          exact ⟨_, by simp only [hP1_inner_def, SMT.Term.abstract, Function.update,
            hR_ne_y, hR_ne_x, hx_ne_y, ↓reduceDIte, Option.get_some] at hDimp ⊢; exact hDimp, rfl⟩
        · -- R(W₁,W₂) = zftrue → need A(W₁) = zftrue and B(W₂) = zftrue
          -- DR.fst = fapply WR_bwd.fst (pair W₁.fst W₂.fst) = zftrue
          -- This means (retract αx W₁.fst, retract βx W₂.fst) ∈ g
          have hpair_mem_τR : W₁.fst.pair W₂.fst ∈ ⟦pairTy⟧ᶻ := by
            rw [hpairTy_def, SMTType.toZFSet, ZFSet.pair_mem_prod]; exact ⟨hW₁_mem, hW₂_mem⟩
          -- retract the pair to B-level
          have hz_mem : (retract αx W₁.fst).pair (retract βx W₂.fst) ∈ ⟦BType.prod αx βx⟧ᶻ := by
            rw [BType.toZFSet, ZFSet.mem_prod]
            exact ⟨retract αx W₁.fst, retract_mem_of_canonical αx hW₁_mem,
                   retract βx W₂.fst, retract_mem_of_canonical βx hW₂_mem, rfl⟩
          -- z ∈ g via retract_cg + membership in retract
          have hmk_func : ⟦(αx ×ᴮ βx).toSMTType⟧ᶻ.IsFunc 𝔹 (mk_cg hg_αprod) := by
            have h := mk_cg_mem hg_αprod
            rw [hαprod_def] at h
            simp only [BType.toSMTType, SMTType.toZFSet] at h
            exact ZFSet.mem_funs.mp h
          have hz_in_g : (retract αx W₁.fst).pair (retract βx W₂.fst) ∈ g := by
            rw [← retract_cg hg_αprod]
            rw [retract, ZFSet.mem_sep]
            refine ⟨hz_mem, ?_⟩
            simp only [dif_pos hz_mem]
            rw [dif_pos hmk_func]
            have hretract_prod : retract (.prod αx βx) (W₁.fst.pair W₂.fst) =
                (retract αx W₁.fst).pair (retract βx W₂.fst) := by
              simp only [retract, ZFSet.π₁_pair, ZFSet.π₂_pair]
            have hcan := canonical_of_retract (.prod αx βx) hpair_mem_τR
            simp only [hretract_prod] at hcan
            simp only [hcan]
            -- Goal: fapply (mk_cg hg_αprod) _ ⟨W₁.fst.pair W₂.fst, _⟩ .val = zftrue
            -- hDR_true : DR.fst = zftrue
            -- hDR : ⟦app (var WR_bwd) (pair (var W₁) (var W₂))⟧ˢ = some DR
            -- We need to show the goal's fapply = DR.fst
            -- Unfold hDR to extract DR's concrete value
            have hWR_pfunc : (mk_cg hg_αprod).IsPFunc ⟦pairTy⟧ᶻ ⟦SMTType.bool⟧ᶻ :=
              ZFSet.is_func_is_pfunc hmk_func
            have hpair_dom' : W₁.fst.pair W₂.fst ∈ (mk_cg hg_αprod).Dom := by
              erw [ZFSet.is_func_dom_eq hmk_func]
              exact hpair_mem_τR
            -- Compute the denotation step by step, matching denote_app_var_pair_var_var
            have hden_app :
                ⟦SMT.PHOAS.Term.app (.var WR_bwd) (.pair (.var W₁) (.var W₂))⟧ˢ =
                some ⟨(ZFSet.fapply (mk_cg hg_αprod) hWR_pfunc ⟨W₁.fst.pair W₂.fst, hpair_dom'⟩).val,
                      .bool,
                      (ZFSet.fapply (mk_cg hg_αprod) hWR_pfunc ⟨W₁.fst.pair W₂.fst, hpair_dom'⟩).prop⟩ := by
              show SMT.denote (SMT.PHOAS.Term.app (.var WR_bwd) (.pair (.var W₁) (.var W₂))) = _
              simp only [SMT.denote, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
                mem_sep, Option.failure_eq_none, dite_eq_ite, WR_bwd, hτR_def, hpairTy_def]
              simp only [hW₁_ty, hW₂_ty, if_true]
              unfold pairTy at hWR_pfunc
              rw [dif_pos hWR_pfunc, dif_pos]
              and_intros
              · erw [ZFSet.is_func_dom_eq hmk_func, BType.toSMTType] at hpair_dom'
                exact hpair_dom'
              · simp only [ZFSet.Dom, ZFSet.mem_sep] at hpair_dom'
                exact hpair_dom'.2
            -- Now hden_app and hDR give: some ⟨fapply_val, .bool, ...⟩ = some DR
            rw [hden_app] at hDR
            have hDR_eq := Option.some_injective _ hDR
            -- DR = ⟨fapply_val, .bool, ...⟩, so DR.fst = fapply_val
            rw [← hDR_true, ←congrArg (·.fst) hDR_eq]
          -- g ⊆ X × Y → retract αx W₁.fst ∈ X and retract βx W₂.fst ∈ Y
          have ⟨_, hx_X, _, hy_Y, retract_W₁_W₂_eq⟩ := ZFSet.mem_prod.mp (hg_sub_XY hz_in_g)
          -- hx_X : retract αx W₁.fst ∈ X = retract (αx.set) den_A.fst
          -- This means fapply den_A.fst (canonical αx (retract αx W₁.fst)) = zftrue
          -- = fapply den_A.fst W₁.fst = DA.fst = zftrue
          rw [ZFSet.pair_inj] at retract_W₁_W₂_eq
          obtain ⟨rfl, rfl⟩ := retract_W₁_W₂_eq
          have hDA_true : DA.fst = zftrue := by
            rw [hDA_val]
            have hfapply_true :=
              (mem_retract_set_iff_app_canonical_eq_zftrue hdenA_func hX_def.symm
                (retract_mem_of_canonical αx hW₁_mem)).mp hx_X
            simp only [canonical_of_retract αx hW₁_mem] at hfapply_true
            exact hfapply_true
          have hDB_true : DB.fst = zftrue := by
            rw [hDB_val]
            have hfapply_true :=
              (mem_retract_set_iff_app_canonical_eq_zftrue hdenB_func hY_def.symm
                (retract_mem_of_canonical βx hW₂_mem)).mp hy_Y
            simp only [canonical_of_retract βx hW₂_mem] at hfapply_true
            exact hfapply_true
          have hDand := denote_and_eq_zftrue_of_some_zftrue hDA_den hDA_ty hDA_true hDB_den hDB_ty hDB_true
          have hDimp := denote_imp_eq_zftrue_of_zftrue_zftrue hDR hDR_ty hDR_true hDand rfl rfl
          exact ⟨_, by simp only [hP1_inner_def, SMT.Term.abstract, Function.update,
            hR_ne_y, hR_ne_x, hx_ne_y, ↓reduceDIte, Option.get_some] at hDimp ⊢; exact hDimp, rfl⟩
      -- ── P1 = zftrue via funBinaryForallEqZftrue ──
      have hP1_zftrue : ⟦P1.abstract (Function.update Δctx R (some WR_bwd)) hcov_P1_bwd⟧ˢ =
          some ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ :=
        funBinaryForallEqZftrue hcov_P1_bwd hgo_cov_P1_inner
          hcov_P1_inner_updxy hP1_inner_total hP1_inner_ty hP1_inner_true
      -- ── P2 infrastructure ──
      set P2_inner := Term.imp
        (.and (.app (.var R) (.pair (.var x) (.var y)))
              (.app (.var R) (.pair (.var x) (.var y'))))
        (.eq (.var y) (.var y')) with hP2_inner_def
      -- CoversFV for P2_inner under [R,x,y,y']
      have hcov_P2_inner_updxyy' : ∀ W₁ W₂ W₃ : SMT.Dom,
          RenamingContext.CoversFV
            (Function.update (Function.update (Function.update (Function.update Δctx R (some WR_bwd))
              x (some W₁)) y (some W₂)) y' (some W₃))
            P2_inner := by
        intro W₁ W₂ W₃ v hv
        rw [hP2_inner_def, SMT.fv] at hv
        simp only [SMT.fv, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, false_or] at hv
        by_cases hvR : v = R
        · subst hvR; simp [Function.update, hR_ne_x, hR_ne_y, hR_ne_y']
        by_cases hvx : v = x
        · subst hvx; simp [Function.update, hx_ne_y, hx_ne_y']
        by_cases hvy : v = y
        · subst hvy; simp [Function.update, hy_ne_y']
        by_cases hvy' : v = y'
        · subst hvy'; simp [Function.update]
        · rw [Function.update_of_ne hvy', Function.update_of_ne hvy,
              Function.update_of_ne hvx, Function.update_of_ne hvR]
          have hv_body : v ∈ SMT.fv pfun_body := by
            rw [hpfun_body_def]; apply SMT.fv.mem_and; right
            rw [hP2_def]; apply SMT.fv.mem_forall
            refine ⟨?_, by simp; push_neg; exact ⟨hvx, hvy, hvy'⟩⟩
            simp only [hP2_inner_def, SMT.fv, List.mem_append, List.mem_cons, List.mem_nil_iff,
              or_false]
            exact hv
          have hv_lambda : v ∈ SMT.fv (Term.lambda [R] [τR] pfun_body) := by
            rw [SMT.fv]
            exact List.mem_filter.mpr ⟨hv_body, by simp [List.mem_singleton]; exact hvR⟩
          exact hcov v hv_lambda
      have hgo_cov_P2_inner : ∀ v ∈ SMT.fv P2_inner, v ∉ [x, y, y'] →
          ((Function.update Δctx R (some WR_bwd)) v).isSome = true := by
        intro v hv hvxyy'
        have hvx : v ≠ x := by intro h; exact hvxyy' (List.mem_cons.mpr (Or.inl h))
        have hvy : v ≠ y := by
          intro h; exact hvxyy' (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl h))))
        have hvy' : v ≠ y' := by
          intro h
          exact hvxyy' (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr
            (List.mem_cons.mpr (Or.inl h))))))
        by_cases hvR : v = R; · subst hvR; simp [Function.update]
        · rw [Function.update_of_ne hvR]
          have hv_body : v ∈ SMT.fv pfun_body := by
            rw [hpfun_body_def]; apply SMT.fv.mem_and; right
            rw [hP2_def]; apply SMT.fv.mem_forall; refine ⟨hv, ?_⟩
            simp [List.mem_cons]; push_neg; exact ⟨hvx, hvy, hvy'⟩
          have hv_lambda : v ∈ SMT.fv (Term.lambda [R] [τR] pfun_body) := by
            rw [SMT.fv]; exact List.mem_filter.mpr ⟨hv_body, by simpa using hvR⟩
          exact hcov v hv_lambda
      -- P2 inner body totality
      have hP2_inner_total : ∀ W₁ W₂ W₃ : SMT.Dom,
          W₁.snd.fst = αx.toSMTType → W₂.snd.fst = βx.toSMTType → W₃.snd.fst = βx.toSMTType →
          ⟦P2_inner.abstract
            (Function.update (Function.update (Function.update (Function.update Δctx R (some WR_bwd))
              x (some W₁)) y (some W₂)) y' (some W₃))
            (hcov_P2_inner_updxyy' W₁ W₂ W₃)⟧ˢ.isSome = true := by
        intro W₁ W₂ W₃ hW₁_ty hW₂_ty hW₃_ty
        have hW₁_mem : W₁.fst ∈ ⟦αx.toSMTType⟧ᶻ := by rw [← hW₁_ty]; exact W₁.2.2
        have hW₂_mem : W₂.fst ∈ ⟦βx.toSMTType⟧ᶻ := by rw [← hW₂_ty]; exact W₂.2.2
        have hW₃_mem : W₃.fst ∈ ⟦βx.toSMTType⟧ᶻ := by rw [← hW₃_ty]; exact W₃.2.2
        obtain ⟨DRxy, hDRxy, hDRxy_ty⟩ := denote_app_var_pair_var_var rfl hW₁_ty hW₁_mem hW₂_ty hW₂_mem
          (WR := WR_bwd) (Wx := W₁) (Wy := W₂)
        obtain ⟨DRxy', hDRxy', hDRxy'_ty⟩ := denote_app_var_pair_var_var rfl hW₁_ty hW₁_mem hW₃_ty hW₃_mem
          (WR := WR_bwd) (Wx := W₁) (Wy := W₃)
        obtain ⟨Dand, hDand, hDand_ty⟩ :=
          denote_and_some_bool_of_some_bool hDRxy hDRxy_ty hDRxy' hDRxy'_ty
        have hDeq_y : ⟦SMT.PHOAS.Term.var W₂⟧ˢ = some W₂ := rfl
        have hDeq_y' : ⟦SMT.PHOAS.Term.var W₃⟧ˢ = some W₃ := rfl
        obtain ⟨Deq, hDeq, hDeq_ty⟩ := denote_eq_some_bool hDeq_y hDeq_y' (by rw [hW₂_ty, hW₃_ty])
        obtain ⟨Dimp, hDimp, _⟩ := denote_imp_some_bool_of_some_bool hDand hDand_ty hDeq hDeq_ty
        suffices h : ⟦P2_inner.abstract _ _⟧ˢ = some Dimp from
          Option.isSome_iff_exists.mpr ⟨Dimp, h⟩
        simp only [hP2_inner_def, SMT.Term.abstract, Function.update,
          hR_ne_y, hR_ne_x, hR_ne_y', hx_ne_y, hx_ne_y', hy_ne_y', ↓reduceDIte,
          Option.get_some] at hDimp ⊢
        exact hDimp
      -- P2 inner body type = .bool
      have hP2_inner_ty : ∀ W₁ W₂ W₃ : SMT.Dom,
          W₁.snd.fst = αx.toSMTType → W₂.snd.fst = βx.toSMTType → W₃.snd.fst = βx.toSMTType →
          ∀ {D : SMT.Dom},
            ⟦P2_inner.abstract
              (Function.update (Function.update (Function.update (Function.update Δctx R (some WR_bwd))
                x (some W₁)) y (some W₂)) y' (some W₃))
              (hcov_P2_inner_updxyy' W₁ W₂ W₃)⟧ˢ = some D → D.snd.fst = SMTType.bool := by
        intro W₁ W₂ W₃ hW₁_ty hW₂_ty hW₃_ty D hD
        have hW₁_mem : W₁.fst ∈ ⟦αx.toSMTType⟧ᶻ := by rw [← hW₁_ty]; exact W₁.2.2
        have hW₂_mem : W₂.fst ∈ ⟦βx.toSMTType⟧ᶻ := by rw [← hW₂_ty]; exact W₂.2.2
        have hW₃_mem : W₃.fst ∈ ⟦βx.toSMTType⟧ᶻ := by rw [← hW₃_ty]; exact W₃.2.2
        obtain ⟨DRxy, hDRxy, hDRxy_ty⟩ := denote_app_var_pair_var_var rfl hW₁_ty hW₁_mem hW₂_ty hW₂_mem
          (WR := WR_bwd) (Wx := W₁) (Wy := W₂)
        obtain ⟨DRxy', hDRxy', hDRxy'_ty⟩ := denote_app_var_pair_var_var rfl hW₁_ty hW₁_mem hW₃_ty hW₃_mem
          (WR := WR_bwd) (Wx := W₁) (Wy := W₃)
        obtain ⟨Dand, hDand, hDand_ty⟩ :=
          denote_and_some_bool_of_some_bool hDRxy hDRxy_ty hDRxy' hDRxy'_ty
        have hDeq_y : ⟦SMT.PHOAS.Term.var W₂⟧ˢ = some W₂ := rfl
        have hDeq_y' : ⟦SMT.PHOAS.Term.var W₃⟧ˢ = some W₃ := rfl
        obtain ⟨Deq, hDeq, hDeq_ty⟩ := denote_eq_some_bool hDeq_y hDeq_y' (by rw [hW₂_ty, hW₃_ty])
        obtain ⟨Dimp, hDimp, hDimp_ty⟩ := denote_imp_some_bool_of_some_bool hDand hDand_ty hDeq hDeq_ty
        suffices h : ⟦P2_inner.abstract _ _⟧ˢ = some Dimp by
          rw [h] at hD; cases hD; exact hDimp_ty
        simp only [hP2_inner_def, SMT.Term.abstract, Function.update,
          hR_ne_y, hR_ne_x, hR_ne_y', hx_ne_y, hx_ne_y', hy_ne_y', ↓reduceDIte,
          Option.get_some] at hDimp ⊢
        exact hDimp
      -- P2 inner body = zftrue for all W₁, W₂, W₃
      have hP2_inner_true : ∀ W₁ W₂ W₃ : SMT.Dom,
          W₁.snd.fst = αx.toSMTType → W₂.snd.fst = βx.toSMTType → W₃.snd.fst = βx.toSMTType →
          ∃ D : SMT.Dom,
            ⟦P2_inner.abstract
              (Function.update (Function.update (Function.update (Function.update Δctx R (some WR_bwd))
                x (some W₁)) y (some W₂)) y' (some W₃))
              (hcov_P2_inner_updxyy' W₁ W₂ W₃)⟧ˢ = some D ∧ D.fst = zftrue := by
        intro W₁ W₂ W₃ hW₁_ty hW₂_ty hW₃_ty
        have hW₁_mem : W₁.fst ∈ ⟦αx.toSMTType⟧ᶻ := by rw [← hW₁_ty]; exact W₁.2.2
        have hW₂_mem : W₂.fst ∈ ⟦βx.toSMTType⟧ᶻ := by rw [← hW₂_ty]; exact W₂.2.2
        have hW₃_mem : W₃.fst ∈ ⟦βx.toSMTType⟧ᶻ := by rw [← hW₃_ty]; exact W₃.2.2
        -- PHOAS denotations
        obtain ⟨DRxy, hDRxy, hDRxy_ty⟩ := denote_app_var_pair_var_var rfl hW₁_ty hW₁_mem hW₂_ty hW₂_mem
          (WR := WR_bwd) (Wx := W₁) (Wy := W₂)
        obtain ⟨DRxy', hDRxy', hDRxy'_ty⟩ := denote_app_var_pair_var_var rfl hW₁_ty hW₁_mem hW₃_ty hW₃_mem
          (WR := WR_bwd) (Wx := W₁) (Wy := W₃)
        have hDRxy_mem_𝔹 : DRxy.fst ∈ 𝔹 := by
          have := DRxy.snd.snd; rw [hDRxy_ty] at this; exact this
        have hDRxy'_mem_𝔹 : DRxy'.fst ∈ 𝔹 := by
          have := DRxy'.snd.snd; rw [hDRxy'_ty] at this; exact this
        -- eq (var y) (var y') always denotes
        have hDeq_y : ⟦SMT.PHOAS.Term.var W₂⟧ˢ = some W₂ := rfl
        have hDeq_y' : ⟦SMT.PHOAS.Term.var W₃⟧ˢ = some W₃ := rfl
        obtain ⟨Deq, hDeq, hDeq_ty⟩ := denote_eq_some_bool hDeq_y hDeq_y' (by rw [hW₂_ty, hW₃_ty])
        -- Case analysis on R(x,y) and R(x,y')
        rcases ZFSet.ZFBool.mem_𝔹_iff _ |>.mp hDRxy_mem_𝔹 with hDRxy_false | hDRxy_true
        · -- R(x,y) = false → and(R(x,y), R(x,y')) = false → imp(false, _) = true
          obtain ⟨Dand, hDand, hDand_ty⟩ :=
            denote_and_some_bool_of_some_bool hDRxy hDRxy_ty hDRxy' hDRxy'_ty
          have hDand_false := denote_and_eq_zffalse_of_some_zffalse_left hDRxy hDRxy_ty hDRxy_false
            hDRxy' hDRxy'_ty
          have hDimp := denote_imp_eq_zftrue_of_zffalse_left
            hDand_false rfl rfl hDeq hDeq_ty
          exact ⟨_, by simp only [hP2_inner_def, SMT.Term.abstract, Function.update,
            hR_ne_y, hR_ne_x, hR_ne_y', hx_ne_y, hx_ne_y', hy_ne_y', ↓reduceDIte,
            Option.get_some] at hDimp ⊢; exact hDimp, rfl⟩
        rcases ZFSet.ZFBool.mem_𝔹_iff _ |>.mp hDRxy'_mem_𝔹 with hDRxy'_false | hDRxy'_true
        · -- R(x,y') = false → and = false → imp = true
          obtain ⟨Dand, hDand, hDand_ty⟩ :=
            denote_and_some_bool_of_some_bool hDRxy hDRxy_ty hDRxy' hDRxy'_ty
          have hDand_false := denote_and_eq_zffalse_of_some_zffalse_right hDRxy hDRxy_ty
            hDRxy' hDRxy'_ty hDRxy'_false
          have hDimp := denote_imp_eq_zftrue_of_zffalse_left
            hDand_false rfl rfl hDeq hDeq_ty
          exact ⟨_, by simp only [hP2_inner_def, SMT.Term.abstract, Function.update,
            hR_ne_y, hR_ne_x, hR_ne_y', hx_ne_y, hx_ne_y', hy_ne_y', ↓reduceDIte,
            Option.get_some] at hDimp ⊢; exact hDimp, rfl⟩
        · -- Both R(x,y) = true and R(x,y') = true → functionality gives y = y'
          have hpair_mem_τR_xy : W₁.fst.pair W₂.fst ∈ ⟦pairTy⟧ᶻ := by
            rw [hpairTy_def, SMTType.toZFSet, ZFSet.pair_mem_prod]; exact ⟨hW₁_mem, hW₂_mem⟩
          have hpair_mem_τR_xy' : W₁.fst.pair W₃.fst ∈ ⟦pairTy⟧ᶻ := by
            rw [hpairTy_def, SMTType.toZFSet, ZFSet.pair_mem_prod]; exact ⟨hW₁_mem, hW₃_mem⟩
          have hmk_func : ⟦(αx ×ᴮ βx).toSMTType⟧ᶻ.IsFunc 𝔹 (mk_cg hg_αprod) := by
            have h := mk_cg_mem hg_αprod
            rw [hαprod_def] at h
            simp only [BType.toSMTType, SMTType.toZFSet] at h
            exact ZFSet.mem_funs.mp h
          -- (retract αx W₁.fst, retract βx W₂.fst) ∈ g
          have hz_in_g_xy : (retract αx W₁.fst).pair (retract βx W₂.fst) ∈ g := by
            rw [← retract_cg hg_αprod, retract, ZFSet.mem_sep]
            have hz_mem : (retract αx W₁.fst).pair (retract βx W₂.fst) ∈ ⟦BType.prod αx βx⟧ᶻ := by
              rw [BType.toZFSet, ZFSet.mem_prod]
              exact ⟨_, retract_mem_of_canonical αx hW₁_mem, _, retract_mem_of_canonical βx hW₂_mem, rfl⟩
            refine ⟨hz_mem, ?_⟩
            simp only [dif_pos hz_mem, dif_pos hmk_func]
            have hretract_prod : retract (.prod αx βx) (W₁.fst.pair W₂.fst) =
                (retract αx W₁.fst).pair (retract βx W₂.fst) := by
              simp only [retract, ZFSet.π₁_pair, ZFSet.π₂_pair]
            have hcan := canonical_of_retract (.prod αx βx) hpair_mem_τR_xy
            simp only [hretract_prod] at hcan; simp only [hcan]
            have hWR_pfunc : (mk_cg hg_αprod).IsPFunc ⟦pairTy⟧ᶻ ⟦SMTType.bool⟧ᶻ :=
              ZFSet.is_func_is_pfunc hmk_func
            have hpair_dom : W₁.fst.pair W₂.fst ∈ (mk_cg hg_αprod).Dom := by
              erw [ZFSet.is_func_dom_eq hmk_func]; exact hpair_mem_τR_xy
            have hden_app :
                ⟦SMT.PHOAS.Term.app (.var WR_bwd) (.pair (.var W₁) (.var W₂))⟧ˢ =
                some ⟨(ZFSet.fapply (mk_cg hg_αprod) hWR_pfunc ⟨W₁.fst.pair W₂.fst, hpair_dom⟩).val,
                      .bool,
                      (ZFSet.fapply (mk_cg hg_αprod) hWR_pfunc ⟨W₁.fst.pair W₂.fst, hpair_dom⟩).prop⟩ := by
              show SMT.denote (SMT.PHOAS.Term.app (.var WR_bwd) (.pair (.var W₁) (.var W₂))) = _
              simp only [SMT.denote, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
                mem_sep, Option.failure_eq_none, dite_eq_ite, WR_bwd, hτR_def, hpairTy_def]
              simp only [hW₁_ty, hW₂_ty, if_true]
              unfold pairTy at hWR_pfunc
              rw [dif_pos hWR_pfunc, dif_pos]
              and_intros
              · erw [ZFSet.is_func_dom_eq hmk_func, BType.toSMTType] at hpair_dom; exact hpair_dom
              · simp only [ZFSet.Dom, ZFSet.mem_sep] at hpair_dom; exact hpair_dom.2
            rw [hden_app] at hDRxy
            rw [← hDRxy_true, ← congrArg (·.fst) (Option.some_injective _ hDRxy)]
          -- (retract αx W₁.fst, retract βx W₃.fst) ∈ g
          have hz_in_g_xy' : (retract αx W₁.fst).pair (retract βx W₃.fst) ∈ g := by
            rw [← retract_cg hg_αprod, retract, ZFSet.mem_sep]
            have hz_mem : (retract αx W₁.fst).pair (retract βx W₃.fst) ∈ ⟦BType.prod αx βx⟧ᶻ := by
              rw [BType.toZFSet, ZFSet.mem_prod]
              exact ⟨_, retract_mem_of_canonical αx hW₁_mem, _, retract_mem_of_canonical βx hW₃_mem, rfl⟩
            refine ⟨hz_mem, ?_⟩
            simp only [dif_pos hz_mem, dif_pos hmk_func]
            have hretract_prod : retract (.prod αx βx) (W₁.fst.pair W₃.fst) =
                (retract αx W₁.fst).pair (retract βx W₃.fst) := by
              simp only [retract, ZFSet.π₁_pair, ZFSet.π₂_pair]
            have hcan := canonical_of_retract (.prod αx βx) hpair_mem_τR_xy'
            simp only [hretract_prod] at hcan; simp only [hcan]
            have hWR_pfunc : (mk_cg hg_αprod).IsPFunc ⟦pairTy⟧ᶻ ⟦SMTType.bool⟧ᶻ :=
              ZFSet.is_func_is_pfunc hmk_func
            have hpair_dom : W₁.fst.pair W₃.fst ∈ (mk_cg hg_αprod).Dom := by
              erw [ZFSet.is_func_dom_eq hmk_func]; exact hpair_mem_τR_xy'
            have hden_app :
                ⟦SMT.PHOAS.Term.app (.var WR_bwd) (.pair (.var W₁) (.var W₃))⟧ˢ =
                some ⟨(ZFSet.fapply (mk_cg hg_αprod) hWR_pfunc ⟨W₁.fst.pair W₃.fst, hpair_dom⟩).val,
                      .bool,
                      (ZFSet.fapply (mk_cg hg_αprod) hWR_pfunc ⟨W₁.fst.pair W₃.fst, hpair_dom⟩).prop⟩ := by
              show SMT.denote (SMT.PHOAS.Term.app (.var WR_bwd) (.pair (.var W₁) (.var W₃))) = _
              simp only [SMT.denote, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
                mem_sep, Option.failure_eq_none, dite_eq_ite, WR_bwd, hτR_def, hpairTy_def]
              simp only [hW₁_ty, hW₃_ty, if_true]
              unfold pairTy at hWR_pfunc
              rw [dif_pos hWR_pfunc, dif_pos]
              and_intros
              · erw [ZFSet.is_func_dom_eq hmk_func, BType.toSMTType] at hpair_dom; exact hpair_dom
              · simp only [ZFSet.Dom, ZFSet.mem_sep] at hpair_dom; exact hpair_dom.2
            rw [hden_app] at hDRxy'
            rw [← hDRxy'_true, ← congrArg (·.fst) (Option.some_injective _ hDRxy')]
          -- Functionality: retract βx W₂.fst = retract βx W₃.fst
          have hretract_eq : retract βx W₂.fst = retract βx W₃.fst :=
            hg_ispfunc.2 _ _ hz_in_g_xy _ hz_in_g_xy'
          -- Injectivity via canonical_of_retract: W₂.fst = W₃.fst
          have hW₂_eq_W₃ : W₂.fst = W₃.fst := by
            rw [←canonical_of_retract βx hW₂_mem, ←canonical_of_retract βx hW₃_mem]
            simp only [hretract_eq]
          -- eq(y, y') = zftrue
          have hDeq_true := denote_eq_eq_zftrue_of_fst_eq hDeq_y hDeq_y'
            (by rw [hW₂_ty, hW₃_ty]) hW₂_eq_W₃
          -- and(true, true) = zftrue
          have hDand := denote_and_eq_zftrue_of_some_zftrue hDRxy hDRxy_ty hDRxy_true
            hDRxy' hDRxy'_ty hDRxy'_true
          -- imp(true, true) = zftrue
          have hDimp := denote_imp_eq_zftrue_of_zftrue_zftrue hDand rfl rfl hDeq_true rfl rfl
          exact ⟨_, by simp only [hP2_inner_def, SMT.Term.abstract, Function.update,
            hR_ne_y, hR_ne_x, hR_ne_y', hx_ne_y, hx_ne_y', hy_ne_y', ↓reduceDIte,
            Option.get_some] at hDimp ⊢; exact hDimp, rfl⟩
      -- ── P2 = zftrue via funTernaryForallEqZftrue ──
      have hP2_zftrue : ⟦P2.abstract (Function.update Δctx R (some WR_bwd)) hcov_P2_bwd⟧ˢ =
          some ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ :=
        funTernaryForallEqZftrue hcov_P2_bwd hgo_cov_P2_inner
          hcov_P2_inner_updxyy' hP2_inner_total hP2_inner_ty hP2_inner_true
      -- ── Combine P1 ∧ P2 = zftrue ──
      have hand_den_bwd := habs_eq_bwd ▸ hden_body_bwd
      have hbody_and := denote_and_eq_zftrue_of_some_zftrue hP1_zftrue rfl rfl hP2_zftrue rfl rfl
      exact congrArg (·.fst) (Option.some_injective _ (hand_den_bwd.symm.trans hbody_and))

set_option maxHeartbeats 4000000 in
theorem encodeTerm_spec.pfun_case.{u} (fv_sub_typings : B.FvSubTypings) (A B : B.Term)
  (A_ih :
    ∀ (E : _root_.B.Env) {Λ : SMT.TypeContext} {α : BType},
      E.context ⊢ᴮ A : α →
        ∀ {«Δ» : _root_.B.RenamingContext.Context} (Δ_fv : ∀ v ∈ _root_.B.fv A, («Δ» v).isSome = true)
          {Δ₀ : SMT.RenamingContext.Context},
          RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» A →
            ∀ {used : List SMT.𝒱},
              (∀ v ∉ used, Δ₀ v = none) →
                ∀ {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ},
                  ⟦A.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩ →
                    (∀ v ∈ A.vars, v ∈ used) →
                      (∀ v ∈ A.vars, v ∈ Λ → v ∈ E.context) →
                        ∀ {n : ℕ},
                          ⦃fun x =>
                            match x with
                            | { env := E0, types := Λ' } =>
                              ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
                            encodeTerm A E ⦃PostCond.mayThrow fun x x_1 =>
                              match x with
                              | (t', σ) =>
                                match x_1 with
                                | { env := E', types := Γ' } =>
                                  ⌜used ⊆ E'.usedVars ∧
                                      Λ ⊆ Γ' ∧
                                        AList.keys Γ' ⊆ E'.usedVars ∧
                                          CoversUsedVars E'.usedVars A ∧
                                            σ = α.toSMTType ∧
                                              Γ' ⊢ˢ t' : σ ∧
                                                (∀ v ∈ used, v ∉ Λ → v ∉ _root_.B.fv A → v ∉ Γ') ∧
                                                  ∃ Δ',
                                                    ∃ (Δ'_covers : RenamingContext.CoversFV Δ' t'),
                                                      RenamingContext.Extends Δ' Δ₀ ∧
                                                        RenamingContext.ExtendsOnSourceFV Δ' «Δ» A ∧
                                                          (∀ v ∉ E'.usedVars, Δ' v = none) ∧
                                                            ∃ denT',
                                                              ⟦t'.abstract Δ' Δ'_covers⟧ˢ = some denT' ∧
                                                                ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT' ∧
                                                                  ∀ (Δ_alt : _root_.B.RenamingContext.Context)
                                                                    (Δ_fv_alt :
                                                                      ∀ v ∈ _root_.B.fv A, (Δ_alt v).isSome = true)
                                                                    (Δ₀_alt : SMT.RenamingContext.Context),
                                                                    RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt A →
                                                                      (∀ v ∉ E'.usedVars, Δ₀_alt v = none) →
                                                                      (∀ v (d : SMT.Dom), Δ₀_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) →
                                                                        ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦α⟧ᶻ),
                                                                          ⟦A.abstract Δ_alt Δ_fv_alt⟧ᴮ =
                                                                              some ⟨T_alt, ⟨α, hT_alt⟩⟩ →
                                                                            ∃ Δ'_alt,
                                                                              ∃ (hcov_alt :
                                                                                RenamingContext.CoversFV Δ'_alt t'),
                                                                                ∃ denT_alt,
                                                                                  RenamingContext.Extends Δ'_alt
                                                                                      Δ₀_alt ∧
                                                                                    (∀ v ∉ E'.usedVars, Δ'_alt v = none) ∧
                                                                                      (∀ v (d : SMT.Dom), Δ'_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) ∧
                                                                                      ⟦t'.abstract Δ'_alt hcov_alt⟧ˢ =
                                                                                          some denT_alt ∧
                                                                                        ⟨T_alt, ⟨α, hT_alt⟩⟩ ≘ᶻ
                                                                                          denT_alt ∧
                                                                                        (∀ v, Δ'_alt v ≠ none → v ∈ Γ')⌝⦄)
  (B_ih :
    ∀ (E : _root_.B.Env) {Λ : SMT.TypeContext} {α : BType},
      E.context ⊢ᴮ B : α →
        ∀ {«Δ» : _root_.B.RenamingContext.Context} (Δ_fv : ∀ v ∈ _root_.B.fv B, («Δ» v).isSome = true)
          {Δ₀ : SMT.RenamingContext.Context},
          RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» B →
            ∀ {used : List SMT.𝒱},
              (∀ v ∉ used, Δ₀ v = none) →
                ∀ {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ},
                  ⟦B.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩ →
                    (∀ v ∈ B.vars, v ∈ used) →
                      (∀ v ∈ B.vars, v ∈ Λ → v ∈ E.context) →
                        ∀ {n : ℕ},
                          ⦃fun x =>
                            match x with
                            | { env := E0, types := Λ' } =>
                              ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
                            encodeTerm B E ⦃PostCond.mayThrow fun x x_1 =>
                              match x with
                              | (t', σ) =>
                                match x_1 with
                                | { env := E', types := Γ' } =>
                                  ⌜used ⊆ E'.usedVars ∧
                                      Λ ⊆ Γ' ∧
                                        AList.keys Γ' ⊆ E'.usedVars ∧
                                          CoversUsedVars E'.usedVars B ∧
                                            σ = α.toSMTType ∧
                                              Γ' ⊢ˢ t' : σ ∧
                                                (∀ v ∈ used, v ∉ Λ → v ∉ _root_.B.fv B → v ∉ Γ') ∧
                                                  ∃ Δ',
                                                    ∃ (Δ'_covers : RenamingContext.CoversFV Δ' t'),
                                                      RenamingContext.Extends Δ' Δ₀ ∧
                                                        RenamingContext.ExtendsOnSourceFV Δ' «Δ» B ∧
                                                          (∀ v ∉ E'.usedVars, Δ' v = none) ∧
                                                            ∃ denT',
                                                              ⟦t'.abstract Δ' Δ'_covers⟧ˢ = some denT' ∧
                                                                ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT' ∧
                                                                  ∀ (Δ_alt : _root_.B.RenamingContext.Context)
                                                                    (Δ_fv_alt :
                                                                      ∀ v ∈ _root_.B.fv B, (Δ_alt v).isSome = true)
                                                                    (Δ₀_alt : SMT.RenamingContext.Context),
                                                                    RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt B →
                                                                      (∀ v ∉ E'.usedVars, Δ₀_alt v = none) →
                                                                      (∀ v (d : SMT.Dom), Δ₀_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) →
                                                                        ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦α⟧ᶻ),
                                                                          ⟦B.abstract Δ_alt Δ_fv_alt⟧ᴮ =
                                                                              some ⟨T_alt, ⟨α, hT_alt⟩⟩ →
                                                                            ∃ Δ'_alt,
                                                                              ∃ (hcov_alt :
                                                                                RenamingContext.CoversFV Δ'_alt t'),
                                                                                ∃ denT_alt,
                                                                                  RenamingContext.Extends Δ'_alt
                                                                                      Δ₀_alt ∧
                                                                                    (∀ v ∉ E'.usedVars, Δ'_alt v = none) ∧
                                                                                      (∀ v (d : SMT.Dom), Δ'_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) ∧
                                                                                      ⟦t'.abstract Δ'_alt hcov_alt⟧ˢ =
                                                                                          some denT_alt ∧
                                                                                        ⟨T_alt, ⟨α, hT_alt⟩⟩ ≘ᶻ
                                                                                          denT_alt ∧
                                                                                        (∀ v, Δ'_alt v ≠ none → v ∈ Γ')⌝⦄)
  (E : _root_.B.Env) {Λ : SMT.TypeContext} {α : BType} (typ_t : E.context ⊢ᴮ A ⇸ᴮ B : α)
  {«Δ» : _root_.B.RenamingContext.Context} (Δ_fv : ∀ v ∈ _root_.B.fv (A ⇸ᴮ B), («Δ» v).isSome = true)
  {Δ₀ : SMT.RenamingContext.Context} (Δ₀_ext : RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» (A ⇸ᴮ B)) {used : List SMT.𝒱}
  (Δ₀_none_out : ∀ v ∉ used, Δ₀ v = none) {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ}
  (den_t : ⟦(A ⇸ᴮ B).abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩) (vars_used : ∀ v ∈ (A ⇸ᴮ B).vars, v ∈ used)
  (Λ_inv : ∀ v ∈ (A ⇸ᴮ B).vars, v ∈ Λ → v ∈ E.context) {n : ℕ} :
  ⦃fun x =>
    match x with
    | { env := E0, types := Λ' } => ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
    encodeTerm (A ⇸ᴮ B) E ⦃PostCond.mayThrow fun x x_1 =>
      match x with
      | (t', σ) =>
        match x_1 with
        | { env := E', types := Γ' } =>
          ⌜used ⊆ E'.usedVars ∧
              Λ ⊆ Γ' ∧
                AList.keys Γ' ⊆ E'.usedVars ∧
                  CoversUsedVars E'.usedVars (A ⇸ᴮ B) ∧
                    σ = α.toSMTType ∧
                      Γ' ⊢ˢ t' : σ ∧
                        (∀ v ∈ used, v ∉ Λ → v ∉ _root_.B.fv (A ⇸ᴮ B) → v ∉ Γ') ∧
                          ∃ Δ',
                            ∃ (Δ'_covers : RenamingContext.CoversFV Δ' t'),
                              RenamingContext.Extends Δ' Δ₀ ∧
                                RenamingContext.ExtendsOnSourceFV Δ' «Δ» (A ⇸ᴮ B) ∧
                                  (∀ v ∉ E'.usedVars, Δ' v = none) ∧
                                    ∃ denT',
                                      ⟦t'.abstract Δ' Δ'_covers⟧ˢ = some denT' ∧
                                        ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT' ∧
                                          ∀ (Δ_alt : _root_.B.RenamingContext.Context)
                                            (Δ_fv_alt : ∀ v ∈ _root_.B.fv (A ⇸ᴮ B), (Δ_alt v).isSome = true)
                                            (Δ₀_alt : SMT.RenamingContext.Context),
                                            RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt (A ⇸ᴮ B) →
                                              (∀ v ∉ E'.usedVars, Δ₀_alt v = none) →
                                              (∀ v (d : SMT.Dom), Δ₀_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) →
                                                ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦α⟧ᶻ),
                                                  ⟦(A ⇸ᴮ B).abstract Δ_alt Δ_fv_alt⟧ᴮ = some ⟨T_alt, ⟨α, hT_alt⟩⟩ →
                                                    ∃ Δ'_alt,
                                                      ∃ (hcov_alt : RenamingContext.CoversFV Δ'_alt t'),
                                                        ∃ denT_alt,
                                                          RenamingContext.Extends Δ'_alt Δ₀_alt ∧
                                                            (∀ v ∉ E'.usedVars, Δ'_alt v = none) ∧
                                                              (∀ v (d : SMT.Dom), Δ'_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) ∧
                                                              ⟦t'.abstract Δ'_alt hcov_alt⟧ˢ = some denT_alt ∧
                                                                ⟨T_alt, ⟨α, hT_alt⟩⟩ ≘ᶻ denT_alt ∧
                                                                                        (∀ v, Δ'_alt v ≠ none → v ∈ Γ')⌝⦄ := by
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
  rw [encodeTerm]

  obtain ⟨αx, βx, rfl, typ_A, typ_B⟩ := _root_.B.Typing.pfunE typ_t

  have Δ_fv_A : ∀ v ∈ _root_.B.fv A, («Δ» v).isSome = true := by
    intro v hv
    exact Δ_fv v (by rw [_root_.B.fv, List.mem_append]; exact Or.inl hv)
  have Δ_fv_B : ∀ v ∈ _root_.B.fv B, («Δ» v).isSome = true := by
    intro v hv
    exact Δ_fv v (by rw [_root_.B.fv, List.mem_append]; exact Or.inr hv)

  rw [_root_.B.Term.abstract, _root_.B.denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at den_t
  obtain ⟨⟨X, τX, hX⟩, den_A, eq⟩ := den_t
  have hτX := denote_welltyped_eq
    (t := A.abstract («Δ» := «Δ») Δ_fv_A)
    ?_ den_A
  on_goal 2 =>
    use E.context.abstract («Δ» := «Δ»), WFTC.of_abstract, .set αx
    exact @Typing.of_abstract (_root_.B.Dom) («Δ» := «Δ») ?_ A E.context (.set αx) Δ_fv_A typ_A
  dsimp at hτX
  subst τX

  dsimp at eq
  rw [Option.bind_eq_some_iff] at eq
  obtain ⟨⟨Y, τY, hY⟩, den_B, eq⟩ := eq
  have hτY := denote_welltyped_eq
    (t := B.abstract («Δ» := «Δ») Δ_fv_B)
    ?_ den_B
  on_goal 2 =>
    use E.context.abstract («Δ» := «Δ»), WFTC.of_abstract, .set βx
    exact @Typing.of_abstract (_root_.B.Dom) («Δ» := «Δ») ?_ B E.context (.set βx) Δ_fv_B typ_B
  dsimp at hτY
  subst τY

  rw [Option.some_inj] at eq
  injection eq with T_eq
  subst T

  have Δ₀_ext_A : RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» A := by
    exact RenamingContext.extendsOnSourceFV_of_fv_subset
      (hsub := by
        intro v hv
        simpa [_root_.B.fv] using (Or.inl hv : v ∈ _root_.B.fv A ∨ v ∈ _root_.B.fv B)) Δ₀_ext
  have Δ₀_ext_B : RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» B := by
    exact RenamingContext.extendsOnSourceFV_of_fv_subset
      (hsub := by
        intro v hv
        simpa [_root_.B.fv] using (Or.inr hv : v ∈ _root_.B.fv A ∨ v ∈ _root_.B.fv B)) Δ₀_ext

  mspec A_ih (E := E) (Λ := St.types) (α := .set αx) typ_A
    («Δ» := «Δ») Δ_fv_A
    (Δ₀ := Δ₀) Δ₀_ext_A (used := used) Δ₀_none_out (T := X) (hT := hX)
    den_A (fun v hv => vars_used v (by
      simp only [_root_.B.Term.vars, List.mem_union_iff, _root_.B.fv, _root_.B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h))
    (fun v hv => Λ_inv v (by
      simp only [_root_.B.Term.vars, List.mem_union_iff, _root_.B.fv, _root_.B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h))
    (n := St.env.freshvarsc)
  clear A_ih
  rename_i out_A
  obtain ⟨A_enc, StA⟩ := out_A
  mrename_i pre
  mintro ∀StA
  mpure pre
  dsimp at pre
  obtain ⟨St_used_sub_StA, St_eq_StA, StA_sub, A_cov_StA, rfl, typ_A_enc, A_preserves,
    Δ', Δ'_covers_A, Δ'_extends_Δ₀, Δ'_ext_A, Δ'_none_out,
    ⟨Aenc, _, hAenc⟩, den_A_enc, ⟨rfl, retract_Aenc_eq_X⟩, A_ih_total⟩ := pre

  have Δ'_ext_B : RenamingContext.ExtendsOnSourceFV Δ' «Δ» B := by
    exact RenamingContext.extendsOnSourceFV_of_extends Δ'_extends_Δ₀ Δ₀_ext_B

  rw [BType.toSMTType]
  mspec B_ih (E := E) (Λ := StA.types) (α := .set βx) typ_B
    («Δ» := «Δ») Δ_fv_B
    (Δ₀ := Δ') Δ'_ext_B (used := StA.env.usedVars) Δ'_none_out (T := Y) (hT := hY)
    den_B (fun v hv => St_used_sub_StA (vars_used v (by
      simp only [_root_.B.Term.vars, List.mem_union_iff, _root_.B.fv, _root_.B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inr h)))
    (fun v hv hΛ => by
      have hv_pfun : v ∈ (A ⇸ᴮ B).vars := by
        simp only [_root_.B.Term.vars, List.mem_union_iff, _root_.B.fv, _root_.B.bv, List.mem_append] at hv ⊢
        rcases hv with h | h <;> [left; right] <;> exact .inr h
      by_cases hv_St : v ∈ St.types
      · exact Λ_inv v hv_pfun hv_St
      · have hv_fv_A : v ∈ _root_.B.fv A := by
          by_contra h_neg
          exact absurd hΛ (A_preserves v (vars_used v hv_pfun) hv_St h_neg)
        exact _root_.B.Typing.typed_by_fv typ_A hv_fv_A)
    (n := StA.env.freshvarsc)
  clear B_ih
  rename_i out_B
  obtain ⟨B_enc, StB⟩ := out_B
  mrename_i pre
  mintro ∀StB
  mpure pre
  dsimp at pre
  obtain ⟨StA_used_sub_StB, StA_eq_StB, StB_sub, B_cov_StB, rfl, typ_B_enc, B_preserves,
    Δ'', Δ''_covers_B, Δ''_extends_Δ', Δ''_ext_B, Δ''_none_out,
    ⟨Benc, _, hBenc⟩, den_B_enc, ⟨rfl, retract_Benc_eq_Y⟩, B_ih_total⟩ := pre

  have typ_A_enc_B : StB.types ⊢ˢ A_enc : (BType.set αx).toSMTType :=
    Typing.weakening StA_eq_StB typ_A_enc
  have hΔ_A_final : RenamingContext.CoversFV Δ'' A_enc := by
    exact RenamingContext.coversFV_of_extends_of_coversFV Δ''_extends_Δ' Δ'_covers_A
  have den_A_enc_final : ⟦A_enc.abstract Δ'' hΔ_A_final⟧ˢ = some ⟨Aenc, ⟨(BType.set αx).toSMTType, hAenc⟩⟩ := by
    have hag_A : RenamingContext.AgreesOnFV Δ'' Δ' A_enc := by
      exact RenamingContext.agreesOnFV_of_extends_of_coversFV Δ''_extends_Δ' Δ'_covers_A
    have hden_A_congr := RenamingContext.denote_congr_of_agreesOnFV
      (t := A_enc) (h1 := hΔ_A_final) (h2 := Δ'_covers_A) hag_A
    simpa [RenamingContext.denote] using hden_A_congr.trans den_A_enc

  rw [BType.toSMTType]
  set ctx := StB.types
  -- freshVar R : (.fun (.pair α β) .bool)
  mspec freshVar_spec
    (Γ := ctx)
    (τ := SMTType.fun (SMTType.pair αx.toSMTType βx.toSMTType) .bool)
    (n := StB.env.freshvarsc)
    (used := StB.env.usedVars)
  case post.success R =>
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨St₁_types_eq, R_fresh, St₁_fvc_eq, St₁_used_eq, R_not_used⟩ := pre

    -- freshVar x : α
    mspec freshVar_spec
      (Γ := ctx.insert R (SMTType.fun (SMTType.pair αx.toSMTType βx.toSMTType) .bool))
      (τ := αx.toSMTType)
      (n := St₁.env.freshvarsc)
      (used := St₁.env.usedVars)
    case post.success x =>
      mrename_i pre
      mintro ∀St₂
      mpure pre
      obtain ⟨St₂_types_eq, x_fresh, St₂_fvc_eq, St₂_used_eq, x_not_used⟩ := pre

      -- freshVar y : β
      mspec freshVar_spec
        (Γ := (ctx.insert R (SMTType.fun (SMTType.pair αx.toSMTType βx.toSMTType) .bool)).insert x αx.toSMTType)
        (τ := βx.toSMTType)
        (n := St₂.env.freshvarsc)
        (used := St₂.env.usedVars)
      case post.success y =>
        mrename_i pre
        mintro ∀St₃
        mpure pre
        obtain ⟨St₃_types_eq, y_fresh, St₃_fvc_eq, St₃_used_eq, y_not_used⟩ := pre

        -- freshVar y' : β
        mspec freshVar_spec
          (Γ := ((ctx.insert R (SMTType.fun (SMTType.pair αx.toSMTType βx.toSMTType) .bool)).insert x αx.toSMTType).insert y βx.toSMTType)
          (τ := βx.toSMTType)
          (n := St₃.env.freshvarsc)
          (used := St₃.env.usedVars)
        case post.success y' =>
          mrename_i pre
          mintro ∀St₄
          mpure pre
          obtain ⟨St₄_types_eq, y'_fresh, St₄_fvc_eq, St₄_used_eq, y'_not_used⟩ := pre

          mspec Std.Do.Spec.pure
          mpure_intro
          -- Distinctness facts (needed for typing AND denotation blocks)
          have hR_ne_x : R ≠ x := by
            intro h; subst h; exact x_fresh (by rw [AList.mem_insert]; exact Or.inl rfl)
          have hR_ne_y : R ≠ y := by
            intro h; subst h
            exact y_fresh (by rw [AList.mem_insert]; exact Or.inr (by rw [AList.mem_insert]; exact Or.inl rfl))
          have hR_ne_y' : R ≠ y' := by
            intro h; subst h
            exact y'_fresh (by rw [AList.mem_insert]; exact Or.inr (by rw [AList.mem_insert]; exact Or.inr (by rw [AList.mem_insert]; exact Or.inl rfl)))
          have hx_ne_y : x ≠ y := by
            intro h; subst h; exact y_fresh (by rw [AList.mem_insert]; exact Or.inl rfl)
          have hx_ne_y' : x ≠ y' := by
            intro h; subst h
            exact y'_fresh (by rw [AList.mem_insert]; exact Or.inr (by rw [AList.mem_insert]; exact Or.inl rfl))
          have hy_ne_y' : y ≠ y' := by
            intro h; subst h; exact y'_fresh (by rw [AList.mem_insert]; exact Or.inl rfl)
          and_intros
          · -- used ⊆ E'.usedVars
            intro v hv
            rw [St₄_used_eq, St₃_used_eq, St₂_used_eq, St₁_used_eq]
            exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (StA_used_sub_StB (St_used_sub_StA hv)))))
          · -- Λ ⊆ Γ'
            intro v hv
            have hctx_sub_R :
                ctx ⊆ ctx.insert R (SMTType.fun (SMTType.pair αx.toSMTType βx.toSMTType) .bool) :=
              SMT.TypeContext.entries_subset_insert_of_notMem R_fresh
            rw [St₄_types_eq]
            apply SMT.TypeContext.entries_subset_insert_of_notMem y'_fresh
            apply SMT.TypeContext.entries_subset_insert_of_notMem y_fresh
            apply SMT.TypeContext.entries_subset_insert_of_notMem x_fresh
            apply SMT.TypeContext.entries_subset_insert_of_notMem R_fresh
            exact StA_eq_StB (St_eq_StA hv)
          · -- AList.keys Γ' ⊆ E'.usedVars
            intro v hv
            rw [St₄_used_eq, St₃_used_eq, St₂_used_eq, St₁_used_eq]
            have hv' : v ∈ St₄.types := (AList.mem_keys).mpr hv
            rw [St₄_types_eq] at hv'
            iterate 4 rw [AList.mem_insert] at hv'
            rcases hv' with rfl | rfl | rfl | rfl | hv'
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ List.mem_cons_self
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (StB_sub ((AList.mem_keys).mp hv')))))
          · -- CoversUsedVars
            intro v hv
            rw [_root_.B.fv, List.mem_append] at hv
            rw [St₄_used_eq, St₃_used_eq, St₂_used_eq, St₁_used_eq]
            rcases hv with hv | hv
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (StA_used_sub_StB (A_cov_StA v hv)))))
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (B_cov_StB v hv))))
          · -- σ = α.toSMTType
            rfl
          · -- typing
            -- The full pfun lambda term types as .fun τR .bool in ctx, then weakened
            -- Abbreviate the type
            let τR := SMTType.fun (SMTType.pair αx.toSMTType βx.toSMTType) .bool
            -- Key subset facts
            have hctxR_sub : ctx.entries ⊆ (ctx.insert R τR).entries :=
              TypeContext.entries_subset_insert_of_notMem R_fresh
            have hctxRx_sub : (ctx.insert R τR).entries ⊆ ((ctx.insert R τR).insert x αx.toSMTType).entries :=
              TypeContext.entries_subset_insert_of_notMem x_fresh
            have hctxRxy_sub : ((ctx.insert R τR).insert x αx.toSMTType).entries ⊆
                (((ctx.insert R τR).insert x αx.toSMTType).insert y βx.toSMTType).entries :=
              TypeContext.entries_subset_insert_of_notMem y_fresh
            have hctxRxyy'_sub : (((ctx.insert R τR).insert x αx.toSMTType).insert y βx.toSMTType).entries ⊆
                ((((ctx.insert R τR).insert x αx.toSMTType).insert y βx.toSMTType).insert y' βx.toSMTType).entries :=
              TypeContext.entries_subset_insert_of_notMem y'_fresh
            -- bv freshness helpers: A_enc and B_enc have no bound vars from R/x/y/y'
            have R_not_bv_A : R ∉ SMT.bv A_enc := by
              have htyp : (ctx.insert R τR) ⊢ˢ A_enc : .fun αx.toSMTType .bool :=
                Typing.weakening hctxR_sub typ_A_enc_B
              exact fun h => (Typing.bv_notMem_context htyp R h)
                (by rw [AList.mem_insert]; exact Or.inl rfl)
            have R_not_bv_B : R ∉ SMT.bv B_enc := by
              have htyp : (ctx.insert R τR) ⊢ˢ B_enc : .fun βx.toSMTType .bool :=
                Typing.weakening hctxR_sub typ_B_enc
              exact fun h => (Typing.bv_notMem_context htyp R h)
                (by rw [AList.mem_insert]; exact Or.inl rfl)
            have x_not_bv_A : x ∉ SMT.bv A_enc := by
              have htyp : ((ctx.insert R τR).insert x αx.toSMTType) ⊢ˢ A_enc : .fun αx.toSMTType .bool :=
                Typing.weakening (hctxR_sub.trans hctxRx_sub) typ_A_enc_B
              exact fun h => (Typing.bv_notMem_context htyp x h)
                (by rw [AList.mem_insert]; exact Or.inl rfl)
            have x_not_bv_B : x ∉ SMT.bv B_enc := by
              have htyp : ((ctx.insert R τR).insert x αx.toSMTType) ⊢ˢ B_enc : .fun βx.toSMTType .bool :=
                Typing.weakening (hctxR_sub.trans hctxRx_sub) typ_B_enc
              exact fun h => (Typing.bv_notMem_context htyp x h)
                (by rw [AList.mem_insert]; exact Or.inl rfl)
            have y_not_bv_A : y ∉ SMT.bv A_enc := by
              have htyp : (((ctx.insert R τR).insert x αx.toSMTType).insert y βx.toSMTType) ⊢ˢ A_enc : .fun αx.toSMTType .bool :=
                Typing.weakening ((hctxR_sub.trans hctxRx_sub).trans hctxRxy_sub) typ_A_enc_B
              exact fun h => (Typing.bv_notMem_context htyp y h)
                (by rw [AList.mem_insert]; exact Or.inl rfl)
            have y_not_bv_B : y ∉ SMT.bv B_enc := by
              have htyp : (((ctx.insert R τR).insert x αx.toSMTType).insert y βx.toSMTType) ⊢ˢ B_enc : .fun βx.toSMTType .bool :=
                Typing.weakening ((hctxR_sub.trans hctxRx_sub).trans hctxRxy_sub) typ_B_enc
              exact fun h => (Typing.bv_notMem_context htyp y h)
                (by rw [AList.mem_insert]; exact Or.inl rfl)
            -- Weaken from ctx to St₄.types
            apply Typing.weakening (h := by
              rw [St₄_types_eq]
              exact (((hctxR_sub.trans hctxRx_sub).trans hctxRxy_sub).trans hctxRxyy'_sub))
            -- Build lambda typing in ctx
            refine Typing.lambda ctx [R] [τR] _ .bool ?_ ?_ ?_ ?_ ?_
            · -- R ∉ ctx
              intro v hv
              rw [List.mem_singleton] at hv; subst hv
              exact R_fresh
            · -- R ∉ bv body
              intro v hv
              rw [List.mem_singleton] at hv; subst hv
              intro hbv
              -- bv body = bv left_forall ++ bv right_forall
              -- bv left_forall = [x,y] ++ [] ++ (bv A_enc ++ bv B_enc)
              -- bv right_forall = [x, y, y']
              simp only [SMT.bv, List.append_nil] at hbv
              rcases List.mem_append.mp hbv with hL | hR
              · -- R ∈ [x, y] ++ ([] ++ (bv A_enc ++ bv B_enc))
                rcases List.mem_append.mp hL with hLL | hLR
                · -- R ∈ [x, y]
                  rcases List.mem_cons.mp hLL with h | hLL'
                  · exact hR_ne_x h
                  · rcases List.mem_cons.mp hLL' with h | h
                    · exact hR_ne_y h
                    · exact List.not_mem_nil h
                · -- R ∈ [] ++ (bv A_enc ++ bv B_enc)
                  rcases List.mem_append.mp hLR with h | hLR'
                  · exact List.not_mem_nil h
                  · -- R ∈ bv A_enc ++ bv B_enc
                    rcases List.mem_append.mp hLR' with h | h
                    · exact R_not_bv_A h
                    · exact R_not_bv_B h
              · -- R ∈ [x, y, y']
                rcases List.mem_cons.mp hR with h | hR'
                · exact hR_ne_x h
                · rcases List.mem_cons.mp hR' with h | hR''
                  · exact hR_ne_y h
                  · rcases List.mem_cons.mp hR'' with h | h
                    · exact hR_ne_y' h
                    · exact List.not_mem_nil h
            · exact Nat.zero_lt_succ 0
            · rfl
            · -- (ctx.update [R] [τR]) ⊢ˢ body : .bool
              have hupdate_R : TypeContext.update ctx [R] [τR] rfl = ctx.insert R τR := by
                simp only [TypeContext.update, List.length_cons, List.length_nil, zero_add,
                  Nat.reduceAdd, Fin.cast_eq_self, Fin.getElem_fin, Fin.val_eq_zero,
                  List.getElem_cons_zero, Fin.foldl_succ, Fin.foldl_zero]
              rw [hupdate_R]
              apply SMT.Typing.and
              · -- Left forall: ∀ x y, R(⟨x,y⟩) ⇒ A(x) ∧ B(y)
                refine SMT.Typing.forall (ctx.insert R τR) [x, y]
                  [αx.toSMTType, βx.toSMTType] _ ?_ ?_ ?_ ?_ ?_
                · -- x, y ∉ ctx.insert R τR
                  intro v hv
                  rcases List.mem_cons.mp hv with rfl | hv'
                  · exact x_fresh
                  · rcases List.mem_cons.mp hv' with rfl | hv''
                    · exact fun hy => y_fresh (by rw [AList.mem_insert]; exact Or.inr hy)
                    · exact absurd hv'' List.not_mem_nil
                · -- x, y ∉ bv body_l
                  intro v hv hbv
                  -- bv body_l = bv A_enc ++ bv B_enc (after full reduction)
                  simp only [SMT.bv, List.mem_append, List.mem_nil_iff, or_false, false_or] at hbv
                  -- hbv : v ∈ bv A_enc ∨ v ∈ bv B_enc
                  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
                  rcases hv with rfl | rfl
                  · exact hbv.elim x_not_bv_A x_not_bv_B
                  · exact hbv.elim y_not_bv_A y_not_bv_B
                · exact Nat.zero_lt_succ 1
                · rfl
                · -- (ctxR.update [x, y] [α, β]) ⊢ˢ body_l : .bool
                  have hupdate_xy : TypeContext.update (ctx.insert R τR)
                      [x, y] [αx.toSMTType, βx.toSMTType] rfl =
                      ((ctx.insert R τR).insert x αx.toSMTType).insert y βx.toSMTType := by
                    simp only [TypeContext.update, List.length_cons, List.length_nil, zero_add,
                      Fin.foldl_succ_last, Fin.getElem_fin, Fin.coe_cast, Fin.val_last,
                      List.getElem_append_right, Nat.sub_self, List.getElem_cons_zero,
                      Fin.coe_castSucc, Fin.foldl_zero]
                    rfl
                  rw [hupdate_xy]
                  apply SMT.Typing.imp
                  · -- R(⟨x,y⟩) : .bool
                    apply SMT.Typing.app
                    · -- R : .fun (.pair α β) .bool in ((ctxR.insert x α).insert y β)
                      apply SMT.Typing.var
                      rw [AList.lookup_insert_ne hR_ne_y, AList.lookup_insert_ne hR_ne_x,
                        AList.lookup_insert]
                    · -- ⟨x, y⟩ : .pair α β
                      apply SMT.Typing.pair
                      · apply SMT.Typing.var
                        rw [AList.lookup_insert_ne hx_ne_y, AList.lookup_insert]
                      · apply SMT.Typing.var; rw [AList.lookup_insert]
                  · -- A(x) ∧ B(y) : .bool
                    apply SMT.Typing.and
                    · apply SMT.Typing.app
                      · exact Typing.weakening
                          ((hctxR_sub.trans hctxRx_sub).trans hctxRxy_sub) typ_A_enc_B
                      · apply SMT.Typing.var
                        rw [AList.lookup_insert_ne hx_ne_y, AList.lookup_insert]
                    · apply SMT.Typing.app
                      · exact Typing.weakening
                          ((hctxR_sub.trans hctxRx_sub).trans hctxRxy_sub) typ_B_enc
                      · apply SMT.Typing.var; rw [AList.lookup_insert]
              · -- Right forall: ∀ x y y', R(⟨x,y⟩) ∧ R(⟨x,y'⟩) ⇒ y = y'
                refine SMT.Typing.forall (ctx.insert R τR) [x, y, y']
                  [αx.toSMTType, βx.toSMTType, βx.toSMTType] _ ?_ ?_ ?_ ?_ ?_
                · -- x, y, y' ∉ ctx.insert R τR
                  intro v hv
                  rcases List.mem_cons.mp hv with rfl | hv'
                  · exact x_fresh
                  · rcases List.mem_cons.mp hv' with rfl | hv''
                    · exact fun hy => y_fresh (by rw [AList.mem_insert]; exact Or.inr hy)
                    · rcases List.mem_cons.mp hv'' with rfl | hv'''
                      · intro hy'
                        exact y'_fresh (by
                          rw [AList.mem_insert]; exact Or.inr
                            (by rw [AList.mem_insert]; exact Or.inr hy'))
                      · exact absurd hv''' List.not_mem_nil
                · -- x, y, y' ∉ bv body_r (bv body_r = [])
                  intro v _hv hbv
                  simp only [SMT.bv, List.mem_append, List.mem_nil_iff, or_false, false_or] at hbv
                · exact Nat.zero_lt_succ 2
                · rfl
                · -- (ctxR.update [x, y, y'] [α, β, β]) ⊢ˢ body_r : .bool
                  have hupdate_xyy' : TypeContext.update (ctx.insert R τR)
                      [x, y, y'] [αx.toSMTType, βx.toSMTType, βx.toSMTType] rfl =
                      (((ctx.insert R τR).insert x αx.toSMTType).insert y βx.toSMTType).insert y' βx.toSMTType := by
                    simp only [TypeContext.update, List.length_cons, List.length_nil, zero_add,
                      Fin.foldl_succ_last, Fin.getElem_fin, Fin.coe_cast, Fin.val_last,
                      List.getElem_append_right, Nat.sub_self, List.getElem_cons_zero,
                      Fin.coe_castSucc, Fin.foldl_zero]
                    rfl
                  rw [hupdate_xyy']
                  apply SMT.Typing.imp
                  · -- R(⟨x,y⟩) ∧ R(⟨x,y'⟩) : .bool
                    apply SMT.Typing.and
                    · -- R(⟨x,y⟩) : .bool
                      apply SMT.Typing.app
                      · apply SMT.Typing.var
                        rw [AList.lookup_insert_ne hR_ne_y', AList.lookup_insert_ne hR_ne_y,
                          AList.lookup_insert_ne hR_ne_x, AList.lookup_insert]
                      · apply SMT.Typing.pair
                        · apply SMT.Typing.var
                          rw [AList.lookup_insert_ne hx_ne_y', AList.lookup_insert_ne hx_ne_y,
                            AList.lookup_insert]
                        · apply SMT.Typing.var
                          rw [AList.lookup_insert_ne hy_ne_y', AList.lookup_insert]
                    · -- R(⟨x,y'⟩) : .bool
                      apply SMT.Typing.app
                      · apply SMT.Typing.var
                        rw [AList.lookup_insert_ne hR_ne_y', AList.lookup_insert_ne hR_ne_y,
                          AList.lookup_insert_ne hR_ne_x, AList.lookup_insert]
                      · apply SMT.Typing.pair
                        · apply SMT.Typing.var
                          rw [AList.lookup_insert_ne hx_ne_y', AList.lookup_insert_ne hx_ne_y,
                            AList.lookup_insert]
                        · apply SMT.Typing.var; rw [AList.lookup_insert]
                  · -- y = y' : .bool
                    apply SMT.Typing.eq
                    · apply SMT.Typing.var
                      rw [AList.lookup_insert_ne hy_ne_y', AList.lookup_insert]
                    · apply SMT.Typing.var; rw [AList.lookup_insert]
          · -- preserves_types
            intro v hv h1 h2
            rw [_root_.B.fv, List.mem_append] at h2; push_neg at h2
            have hv_StA : v ∈ StA.env.usedVars := St_used_sub_StA (by simpa [St_used_eq] using hv)
            have hv_not_StA : v ∉ StA.types :=
              A_preserves v (by simpa [St_used_eq] using hv) h1 h2.1
            have hv_not_StB : v ∉ StB.types :=
              B_preserves v hv_StA hv_not_StA h2.2
            rw [St₄_types_eq]
            intro hv_in
            iterate 4 rw [AList.mem_insert] at hv_in
            rcases hv_in with rfl | rfl | rfl | rfl | hv_in
            · apply y'_not_used
              rw [St₃_used_eq, St₂_used_eq, St₁_used_eq]
              exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (StA_used_sub_StB hv_StA)))
            · apply y_not_used
              rw [St₂_used_eq, St₁_used_eq]
              exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (StA_used_sub_StB hv_StA))
            · apply x_not_used
              rw [St₁_used_eq]
              exact List.mem_cons_of_mem _ (StA_used_sub_StB hv_StA)
            · exact R_not_used (StA_used_sub_StB hv_StA)
            · exact hv_not_StB hv_in
          · -- ∃ Δ', ... (renaming context + CoversFV + denotation + ih_total)
            -- The output term t_pfun has free variables = fv(A_enc) ∪ fv(B_enc) only
            -- (R, x, y, y' are all bound by lambda/forall)
            -- So Δ'' covers t_pfun's free variables
            have hcov_pfun : RenamingContext.CoversFV Δ'' (Term.lambda [R]
                [SMTType.fun (SMTType.pair αx.toSMTType βx.toSMTType) .bool]
                (.and
                  (.forall [x, y] [αx.toSMTType, βx.toSMTType]
                    (.imp (.app (.var R) (.pair (.var x) (.var y)))
                      (.and (.app A_enc (.var x)) (.app B_enc (.var y)))))
                  (.forall [x, y, y'] [αx.toSMTType, βx.toSMTType, βx.toSMTType]
                    (.imp
                      (.and (.app (.var R) (.pair (.var x) (.var y)))
                            (.app (.var R) (.pair (.var x) (.var y'))))
                      (.eq (.var y) (.var y')))))) := by
              intro v hv
              -- fv(lambda [R] [τR] body) = removeAll (fv body) [R]
              rw [SMT.fv, List.mem_removeAll_iff] at hv
              obtain ⟨hv_body, hv_ne_R⟩ := hv
              -- fv(and f1 f2) = fv f1 ++ fv f2
              rw [SMT.fv, List.mem_append] at hv_body
              rcases hv_body with hv_f1 | hv_f2
              · -- v in fv(forall [x,y] [...] body1) = removeAll (fv body1) [x,y]
                rw [SMT.fv, List.mem_removeAll_iff] at hv_f1
                obtain ⟨hv_imp, hv_ne_xy⟩ := hv_f1
                -- fv(imp a b) = fv a ++ fv b
                rw [SMT.fv, List.mem_append] at hv_imp
                rcases hv_imp with hv_app | hv_and
                · -- v in fv(.app R ⟨x,y⟩) = fv R ++ fv ⟨x,y⟩
                  rw [SMT.fv, List.mem_append] at hv_app
                  rcases hv_app with hvR | hvpair
                  · have hvR' : v = R := by simpa [SMT.fv] using hvR
                    exfalso; exact hv_ne_R (by simp [hvR'])
                  · rw [SMT.fv, List.mem_append] at hvpair
                    rcases hvpair with hvx | hvy
                    · have hvx' : v = x := by simpa [SMT.fv] using hvx
                      exfalso; exact hv_ne_xy (by simp [hvx'])
                    · have hvy' : v = y := by simpa [SMT.fv] using hvy
                      exfalso; exact hv_ne_xy (by simp [hvy'])
                · -- v in fv(.and (.app A x) (.app B y))
                  rw [SMT.fv, List.mem_append] at hv_and
                  rcases hv_and with hvAx | hvBy
                  · rw [SMT.fv, List.mem_append] at hvAx
                    rcases hvAx with hvA | hvx
                    · exact hΔ_A_final v hvA
                    · have hvx' : v = x := by simpa [SMT.fv] using hvx
                      exfalso; exact hv_ne_xy (by simp [hvx'])
                  · rw [SMT.fv, List.mem_append] at hvBy
                    rcases hvBy with hvB | hvy
                    · exact Δ''_covers_B v hvB
                    · have hvy' : v = y := by simpa [SMT.fv] using hvy
                      exfalso; exact hv_ne_xy (by simp [hvy'])
              · -- v in fv(forall [x,y,y'] [...] body2) = removeAll (fv body2) [x,y,y']
                rw [SMT.fv, List.mem_removeAll_iff] at hv_f2
                obtain ⟨hv_imp, hv_ne_xyy'⟩ := hv_f2
                -- fv(imp a b) = fv a ++ fv b
                rw [SMT.fv, List.mem_append] at hv_imp
                rcases hv_imp with hv_and | hv_eq
                · -- v in fv(.and (.app R ⟨x,y⟩) (.app R ⟨x,y'⟩))
                  rw [SMT.fv, List.mem_append] at hv_and
                  rcases hv_and with hv1 | hv2
                  · rw [SMT.fv, List.mem_append] at hv1
                    rcases hv1 with hvR | hvpair
                    · have hvR' : v = R := by simpa [SMT.fv] using hvR
                      exfalso; exact hv_ne_R (by simp [hvR'])
                    · rw [SMT.fv, List.mem_append] at hvpair
                      rcases hvpair with hvx | hvy
                      · have hvx' : v = x := by simpa [SMT.fv] using hvx
                        exfalso; exact hv_ne_xyy' (by simp [hvx'])
                      · have hvy' : v = y := by simpa [SMT.fv] using hvy
                        exfalso; exact hv_ne_xyy' (by simp [hvy'])
                  · rw [SMT.fv, List.mem_append] at hv2
                    rcases hv2 with hvR | hvpair
                    · have hvR' : v = R := by simpa [SMT.fv] using hvR
                      exfalso; exact hv_ne_R (by simp [hvR'])
                    · rw [SMT.fv, List.mem_append] at hvpair
                      rcases hvpair with hvx | hvy'
                      · have hvx' : v = x := by simpa [SMT.fv] using hvx
                        exfalso; exact hv_ne_xyy' (by simp [hvx'])
                      · have hvy'' : v = y' := by simpa [SMT.fv] using hvy'
                        exfalso; exact hv_ne_xyy' (by simp [hvy''])
                · -- v in fv(.eq y y')
                  rw [SMT.fv, List.mem_append] at hv_eq
                  rcases hv_eq with hvy | hvy'
                  · have hvy' : v = y := by simpa [SMT.fv] using hvy
                    exfalso; exact hv_ne_xyy' (by simp [hvy'])
                  · have hvy'' : v = y' := by simpa [SMT.fv] using hvy'
                    exfalso; exact hv_ne_xyy' (by simp [hvy''])
            refine ⟨Δ'', hcov_pfun, ?_⟩
            and_intros
            · -- Extends Δ'' Δ₀
              exact RenamingContext.extends_trans Δ''_extends_Δ' Δ'_extends_Δ₀
            · -- ExtendsOnSourceFV Δ'' Δ (A ⇸ᴮ B)
              exact RenamingContext.extendsOnSourceFV_of_extends
                (RenamingContext.extends_trans Δ''_extends_Δ' Δ'_extends_Δ₀) Δ₀_ext
            · -- ∀ v ∉ E'.usedVars, Δ'' v = none
              intro v hv
              exact Δ''_none_out v (by
                simp only [St₄_used_eq, St₃_used_eq, St₂_used_eq, St₁_used_eq, List.mem_cons, not_or] at hv
                exact hv.2.2.2.2)
            · -- denotation + ih_total
              -- Derive fv-freshness: R, x, y, y' ∉ fv(A_enc) ∪ fv(B_enc)
              have fv_sub_used_A : ∀ v ∈ SMT.fv A_enc, v ∈ StB.env.usedVars := by
                intro v hv
                have := hΔ_A_final v hv
                by_contra h_neg
                simp [Δ''_none_out v h_neg] at this
              have fv_sub_used_B : ∀ v ∈ SMT.fv B_enc, v ∈ StB.env.usedVars := by
                intro v hv
                have := Δ''_covers_B v hv
                by_contra h_neg
                simp [Δ''_none_out v h_neg] at this
              have R_not_fv_A : R ∉ SMT.fv A_enc := fun h => R_not_used (fv_sub_used_A R h)
              have R_not_fv_B : R ∉ SMT.fv B_enc := fun h => R_not_used (fv_sub_used_B R h)
              have x_not_StB : x ∉ StB.env.usedVars := by
                intro h; exact x_not_used (by rw [St₁_used_eq]; exact List.mem_cons_of_mem _ h)
              have x_not_fv_A : x ∉ SMT.fv A_enc := fun h => x_not_StB (fv_sub_used_A x h)
              have x_not_fv_B : x ∉ SMT.fv B_enc := fun h => x_not_StB (fv_sub_used_B x h)
              have y_not_StB : y ∉ StB.env.usedVars := by
                intro h; exact y_not_used (by
                  rw [St₂_used_eq]; exact List.mem_cons_of_mem _
                    (by rw [St₁_used_eq]; exact List.mem_cons_of_mem _ h))
              have y_not_fv_A : y ∉ SMT.fv A_enc := fun h => y_not_StB (fv_sub_used_A y h)
              have y_not_fv_B : y ∉ SMT.fv B_enc := fun h => y_not_StB (fv_sub_used_B y h)
              have y'_not_StB : y' ∉ StB.env.usedVars := by
                intro h
                apply y'_not_used
                rw [St₃_used_eq]
                apply List.mem_cons_of_mem
                rw [St₂_used_eq]
                apply List.mem_cons_of_mem
                rw [St₁_used_eq]
                exact List.mem_cons_of_mem _ h
              have y'_not_fv_A : y' ∉ SMT.fv A_enc :=
                fun h => y'_not_StB (fv_sub_used_A y' h)
              have y'_not_fv_B : y' ∉ SMT.fv B_enc :=
                fun h => y'_not_StB (fv_sub_used_B y' h)
              -- Apply pfun_lambda_denotation
              obtain ⟨den_pfun, hden_pfun, hty_pfun, hretract_pfun⟩ :=
                pfun_lambda_denotation
                  (αx := αx) (βx := βx)
                  (hcov_A := hΔ_A_final) (hcov_B := Δ''_covers_B)
                  (h_den_A := den_A_enc_final) (h_den_B := den_B_enc)
                  (den_A_type := rfl) (den_B_type := rfl)
                  R_not_fv_A R_not_fv_B x_not_fv_A x_not_fv_B
                  y_not_fv_A y_not_fv_B y'_not_fv_A y'_not_fv_B
                  hR_ne_x hR_ne_y hR_ne_y' hx_ne_y hx_ne_y' hy_ne_y'
                  (htyp_A := typ_A_enc_B) (htyp_B := typ_B_enc)
                  (R_not_in_Γ := R_fresh)
                  (x_not_in_Γ := fun h => x_fresh (by rw [AList.mem_insert]; exact Or.inr h))
                  (y_not_in_Γ := fun h => y_fresh (by rw [AList.mem_insert]; exact Or.inr (by rw [AList.mem_insert]; exact Or.inr h)))
                  (y'_not_in_Γ := fun h => y'_fresh (by rw [AList.mem_insert]; exact Or.inr (by rw [AList.mem_insert]; exact Or.inr (by rw [AList.mem_insert]; exact Or.inr h))))
                  hcov_pfun
              refine ⟨den_pfun, hden_pfun, ?_, ?_⟩
              · -- RDom: ⟨T, ⟨α, hT⟩⟩ ≘ᶻ den_pfun
                exact ⟨by simp only [BType.toSMTType]; exact hty_pfun,
                  by rw [hretract_pfun, retract_Aenc_eq_X, retract_Benc_eq_Y]⟩
              -- ih_total: alt universality
              intro Δ_alt Δ_fv_alt Δ₀_alt Δ₀_alt_ext Δ₀_alt_none_out Δ₀_alt_wt T_alt hT_alt den_t_alt
              -- Decompose B-denotation of (A ⇸ᴮ B) under alt valuation
              rw [_root_.B.Term.abstract, _root_.B.denote, Option.pure_def, Option.bind_eq_bind,
                Option.bind_eq_some_iff] at den_t_alt
              obtain ⟨⟨A_alt, α_alt', hA_alt⟩, den_A_alt, eq_alt⟩ := den_t_alt
              have α_alt_eq := @denote_welltyped_eq
                (A.abstract Δ_alt (fun v hv => Δ_fv_alt v (by rw [_root_.B.fv, List.mem_append]; exact Or.inl hv)))
                A_alt α_alt' hA_alt ?_ den_A_alt
              on_goal 2 =>
                use E.context.abstract («Δ» := Δ_alt), WFTC.of_abstract, .set αx
                exact @Typing.of_abstract (_root_.B.Dom) («Δ» := Δ_alt) ?_ A E.context (.set αx)
                  (fun v hv => Δ_fv_alt v (by rw [_root_.B.fv, List.mem_append]; exact Or.inl hv)) typ_A
              dsimp at α_alt_eq; subst α_alt_eq
              dsimp at eq_alt
              rw [Option.bind_eq_some_iff] at eq_alt
              obtain ⟨⟨B_alt, _, hB_alt⟩, den_B_alt, eq_alt⟩ := eq_alt
              have β_alt_eq := @denote_welltyped_eq
                (_root_.B.Term.abstract B Δ_alt (fun v hv => Δ_fv_alt v (by rw [_root_.B.fv, List.mem_append]; exact Or.inr hv)))
                B_alt _ hB_alt ?_ den_B_alt
              on_goal 2 =>
                use E.context.abstract («Δ» := Δ_alt), WFTC.of_abstract, .set βx
                exact @Typing.of_abstract (_root_.B.Dom) («Δ» := Δ_alt) ?_ B E.context (.set βx)
                  (fun v hv => Δ_fv_alt v (by rw [_root_.B.fv, List.mem_append]; exact Or.inr hv)) typ_B
              dsimp at β_alt_eq; subst β_alt_eq
              dsimp at eq_alt
              rw [Option.some_inj] at eq_alt
              injection eq_alt with T_alt_eq
              subst T_alt
              -- Build restricted base for A IH
              set Δ₀_alt_A : SMT.RenamingContext.Context :=
                fun v => if v ∈ StA.env.usedVars then Δ₀_alt v else none with Δ₀_alt_A_def
              have Δ₀_alt_A_ext : RenamingContext.ExtendsOnSourceFV Δ₀_alt_A Δ_alt A := by
                have hsrc := RenamingContext.extendsOnSourceFV_of_fv_subset
                  (hsub := by intro v hv; simpa [_root_.B.fv] using
                    (Or.inl hv : v ∈ _root_.B.fv A ∨ v ∈ _root_.B.fv B))
                  Δ₀_alt_ext
                intro v d hv
                simp only [Δ₀_alt_A_def]
                have hv_fv : v ∈ _root_.B.fv A := by
                  by_contra hv_not
                  simp [_root_.B.RenamingContext.toSMTOnFV, _root_.B.RenamingContext.toSMT,
                    _root_.B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_not] at hv
                have hv_used : v ∈ StA.env.usedVars :=
                  St_used_sub_StA (vars_used v (by
                    simp only [_root_.B.Term.vars, List.mem_union_iff, _root_.B.fv, _root_.B.bv,
                      List.mem_append]
                    left; left; exact hv_fv))
                rw [if_pos hv_used]
                exact hsrc hv
              have Δ₀_alt_A_none : ∀ v ∉ StA.env.usedVars, Δ₀_alt_A v = none := by
                intro v hv; simp only [Δ₀_alt_A_def]; rw [if_neg hv]
              have Δ₀_alt_A_wt' : ∀ v (d : SMT.Dom), Δ₀_alt_A v = some d → ∀ τ, StA.types.lookup v = some τ → d.snd.fst = τ := by
                intro v d hv τ hτ; simp only [Δ₀_alt_A_def] at hv; split_ifs at hv with h; exact Δ₀_alt_wt v d hv τ (by rw [St₄_types_eq]; exact AList.mem_lookup_iff.mpr (SMT.TypeContext.entries_subset_insert_of_notMem y'_fresh (SMT.TypeContext.entries_subset_insert_of_notMem y_fresh (SMT.TypeContext.entries_subset_insert_of_notMem x_fresh (SMT.TypeContext.entries_subset_insert_of_notMem R_fresh (StA_eq_StB (AList.mem_lookup_iff.mp hτ)))))))
              -- Call A_ih_total
              obtain ⟨Δ'_alt_A, hcov_alt_A, denT_A_alt, hext_alt_A,
                Δ'_alt_A_none_out, Δ'_alt_A_wt_out, den_A_alt_enc, hRDom_A_alt, _⟩ :=
                A_ih_total Δ_alt
                  (fun v hv => Δ_fv_alt v (by rw [_root_.B.fv, List.mem_append]; exact Or.inl hv))
                  Δ₀_alt_A Δ₀_alt_A_ext Δ₀_alt_A_none Δ₀_alt_A_wt' A_alt hA_alt den_A_alt
              -- Build hybrid base for B IH; zero out variables not in StB.env.usedVars
              set Δ₀_alt_B : SMT.RenamingContext.Context :=
                fun v => if v ∈ StB.env.usedVars
                         then (match Δ₀_alt v with
                           | some d => some d
                           | none => if v ∈ StA.types then Δ'_alt_A v else none)
                         else none
                with Δ₀_alt_B_def
              have Δ₀_alt_B_ext : RenamingContext.ExtendsOnSourceFV Δ₀_alt_B Δ_alt B := by
                have hsrc := RenamingContext.extendsOnSourceFV_of_fv_subset
                  (hsub := by intro v hv; simpa [_root_.B.fv] using
                    (Or.inr hv : v ∈ _root_.B.fv A ∨ v ∈ _root_.B.fv B))
                  Δ₀_alt_ext
                intro v d hv
                simp only [Δ₀_alt_B_def]
                have hv_fv : v ∈ _root_.B.fv B := by
                  by_contra hv_not
                  simp [_root_.B.RenamingContext.toSMTOnFV, _root_.B.RenamingContext.toSMT,
                    _root_.B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_not] at hv
                have hv_used : v ∈ StB.env.usedVars :=
                  StA_used_sub_StB (St_used_sub_StA (vars_used v (by
                    simp only [_root_.B.Term.vars, List.mem_union_iff, _root_.B.fv, _root_.B.bv,
                      List.mem_append]
                    left; right; exact hv_fv)))
                rw [if_pos hv_used]
                have hΔ₀_val := hsrc hv
                simp [hΔ₀_val]
              have Δ₀_alt_B_none : ∀ v ∉ StB.env.usedVars, Δ₀_alt_B v = none := by
                intro v hv; simp only [Δ₀_alt_B_def]; rw [if_neg hv]
              have Δ₀_alt_B_wt' : ∀ v (d : SMT.Dom), Δ₀_alt_B v = some d → ∀ τ, StB.types.lookup v = some τ → d.snd.fst = τ := by
                intro v d hv τ hτ
                simp only [Δ₀_alt_B_def] at hv
                have hv_used : v ∈ StB.env.usedVars := by
                  by_contra h; rw [if_neg h] at hv; exact Option.noConfusion hv
                rw [if_pos hv_used] at hv
                cases hΔ : Δ₀_alt v with
                | some d' =>
                  simp [hΔ] at hv; subst hv
                  exact Δ₀_alt_wt v d' hΔ τ (by
                    rw [St₄_types_eq]
                    exact AList.mem_lookup_iff.mpr
                      (SMT.TypeContext.entries_subset_insert_of_notMem y'_fresh
                        (SMT.TypeContext.entries_subset_insert_of_notMem y_fresh
                          (SMT.TypeContext.entries_subset_insert_of_notMem x_fresh
                            (SMT.TypeContext.entries_subset_insert_of_notMem R_fresh
                              (AList.mem_lookup_iff.mp hτ))))))
                | none =>
                  simp [hΔ] at hv
                  obtain ⟨hv_types, hv⟩ := hv
                  apply Δ'_alt_A_wt_out v d hv
                  obtain ⟨τ', hτ'⟩ := Option.isSome_iff_exists.mp (AList.lookup_isSome.mpr hv_types)
                  have h_lkp := AList.lookup_of_subset StA_eq_StB hτ'
                  rw [hτ] at h_lkp; cases h_lkp; exact hτ'
              -- Call B_ih_total
              obtain ⟨Δ'_alt_B, hcov_alt_B, denT_B_alt, hext_alt_B,
                Δ'_alt_B_none_out, Δ'_alt_B_wt_out, den_B_alt_enc, hRDom_B_alt, Δ'_alt_B_dom_out⟩ :=
                B_ih_total Δ_alt
                  (fun v hv => Δ_fv_alt v (by rw [_root_.B.fv, List.mem_append]; exact Or.inr hv))
                  Δ₀_alt_B Δ₀_alt_B_ext Δ₀_alt_B_none Δ₀_alt_B_wt' B_alt hB_alt den_B_alt
              -- Define final Δ'_alt = priority merge(Δ₀_alt, Δ'_alt_B)
              set Δ'_alt : SMT.RenamingContext.Context :=
                fun v => match Δ₀_alt v with | some d => some d | none => Δ'_alt_B v
                with Δ'_alt_def
              -- Extract types from alt denotations
              obtain ⟨Aenc_alt, σ_A_alt, hAenc_alt⟩ := denT_A_alt
              obtain ⟨Benc_alt, σ_B_alt, hBenc_alt⟩ := denT_B_alt
              obtain ⟨rfl, retract_A_alt⟩ := hRDom_A_alt
              obtain ⟨rfl, retract_B_alt⟩ := hRDom_B_alt
              -- Coverage of A_enc and B_enc under Δ'_alt
              have hcov_A_alt : RenamingContext.CoversFV Δ'_alt A_enc := by
                intro v hv; simp only [Δ'_alt_def]
                cases h : Δ₀_alt v with
                | some d => simp
                | none =>
                  have hv_StB : v ∈ StB.env.usedVars :=
                    StA_used_sub_StB (by
                      by_contra hv_not
                      exact absurd (Δ'_covers_A v hv) (by simp [Δ'_none_out v hv_not]))
                  have hv_types : v ∈ StA.types := SMT.Typing.mem_context_of_mem_fv typ_A_enc hv
                  have hΔ₀_alt_B_v : Δ₀_alt_B v = Δ'_alt_A v := by
                    simp [Δ₀_alt_B_def, if_pos hv_StB, h, if_pos hv_types]
                  have hA_some := hcov_alt_A v hv
                  obtain ⟨dA, hdA⟩ := Option.isSome_iff_exists.mp hA_some
                  have := hext_alt_B (by rw [hΔ₀_alt_B_v, hdA])
                  rw [this]; simp
              have hcov_B_alt : RenamingContext.CoversFV Δ'_alt B_enc := by
                intro v hv; simp only [Δ'_alt_def]
                cases h : Δ₀_alt v with
                | some d => simp
                | none => exact hcov_alt_B v hv
              -- Coverage for the pfun lambda under Δ'_alt
              have hcov_pfun_alt : RenamingContext.CoversFV Δ'_alt (Term.lambda [R]
                  [SMTType.fun (SMTType.pair αx.toSMTType βx.toSMTType) .bool]
                  (.and
                    (.forall [x, y] [αx.toSMTType, βx.toSMTType]
                      (.imp (.app (.var R) (.pair (.var x) (.var y)))
                        (.and (.app A_enc (.var x)) (.app B_enc (.var y)))))
                    (.forall [x, y, y'] [αx.toSMTType, βx.toSMTType, βx.toSMTType]
                      (.imp
                        (.and (.app (.var R) (.pair (.var x) (.var y)))
                              (.app (.var R) (.pair (.var x) (.var y'))))
                        (.eq (.var y) (.var y')))))) := by
                intro v hv
                rw [SMT.fv, List.mem_removeAll_iff] at hv
                obtain ⟨hv_body, hv_ne_R⟩ := hv
                rw [SMT.fv, List.mem_append] at hv_body
                rcases hv_body with hv_f1 | hv_f2
                · rw [SMT.fv, List.mem_removeAll_iff] at hv_f1
                  obtain ⟨hv_imp, hv_ne_xy⟩ := hv_f1
                  rw [SMT.fv, List.mem_append] at hv_imp
                  rcases hv_imp with hv_app | hv_and
                  · rw [SMT.fv, List.mem_append] at hv_app
                    rcases hv_app with hvR | hvpair
                    · have hvR' : v = R := by simpa [SMT.fv] using hvR
                      exfalso; exact hv_ne_R (by simp [hvR'])
                    · rw [SMT.fv, List.mem_append] at hvpair
                      rcases hvpair with hvx | hvy
                      · have hvx' : v = x := by simpa [SMT.fv] using hvx
                        exfalso; exact hv_ne_xy (by simp [hvx'])
                      · have hvy' : v = y := by simpa [SMT.fv] using hvy
                        exfalso; exact hv_ne_xy (by simp [hvy'])
                  · rw [SMT.fv, List.mem_append] at hv_and
                    rcases hv_and with hvAx | hvBy
                    · rw [SMT.fv, List.mem_append] at hvAx
                      rcases hvAx with hvA | hvx
                      · exact hcov_A_alt v hvA
                      · have hvx' : v = x := by simpa [SMT.fv] using hvx
                        exfalso; exact hv_ne_xy (by simp [hvx'])
                    · rw [SMT.fv, List.mem_append] at hvBy
                      rcases hvBy with hvB | hvy
                      · exact hcov_B_alt v hvB
                      · have hvy' : v = y := by simpa [SMT.fv] using hvy
                        exfalso; exact hv_ne_xy (by simp [hvy'])
                · rw [SMT.fv, List.mem_removeAll_iff] at hv_f2
                  obtain ⟨hv_imp, hv_ne_xyy'⟩ := hv_f2
                  rw [SMT.fv, List.mem_append] at hv_imp
                  rcases hv_imp with hv_and | hv_eq
                  · rw [SMT.fv, List.mem_append] at hv_and
                    rcases hv_and with hv1 | hv2
                    · rw [SMT.fv, List.mem_append] at hv1
                      rcases hv1 with hvR | hvpair
                      · have hvR' : v = R := by simpa [SMT.fv] using hvR
                        exfalso; exact hv_ne_R (by simp [hvR'])
                      · rw [SMT.fv, List.mem_append] at hvpair
                        rcases hvpair with hvx | hvy
                        · have hvx' : v = x := by simpa [SMT.fv] using hvx
                          exfalso; exact hv_ne_xyy' (by simp [hvx'])
                        · have hvy' : v = y := by simpa [SMT.fv] using hvy
                          exfalso; exact hv_ne_xyy' (by simp [hvy'])
                    · rw [SMT.fv, List.mem_append] at hv2
                      rcases hv2 with hvR | hvpair
                      · have hvR' : v = R := by simpa [SMT.fv] using hvR
                        exfalso; exact hv_ne_R (by simp [hvR'])
                      · rw [SMT.fv, List.mem_append] at hvpair
                        rcases hvpair with hvx | hvy'
                        · have hvx' : v = x := by simpa [SMT.fv] using hvx
                          exfalso; exact hv_ne_xyy' (by simp [hvx'])
                        · have hvy'' : v = y' := by simpa [SMT.fv] using hvy'
                          exfalso; exact hv_ne_xyy' (by simp [hvy''])
                  · rw [SMT.fv, List.mem_append] at hv_eq
                    rcases hv_eq with hvy | hvy'
                    · have hvy' : v = y := by simpa [SMT.fv] using hvy
                      exfalso; exact hv_ne_xyy' (by simp [hvy'])
                    · have hvy'' : v = y' := by simpa [SMT.fv] using hvy'
                      exfalso; exact hv_ne_xyy' (by simp [hvy''])
              -- Transport denotations from Δ'_alt_A / Δ'_alt_B to Δ'_alt
              have hag_A_alt : RenamingContext.AgreesOnFV Δ'_alt Δ'_alt_A A_enc := by
                intro v hv
                simp only [Δ'_alt_def]
                -- v ∈ fv(A_enc) implies v ∈ StA, so Δ₀_alt_A v = Δ₀_alt v (when in StA)
                have hv_StA : v ∈ StA.env.usedVars := by
                  by_contra hv_not
                  exact absurd (Δ'_covers_A v hv) (by simp [Δ'_none_out v hv_not])
                cases hΔ₀ : Δ₀_alt v with
                | some d =>
                  -- Δ'_alt v = some d; Δ'_alt_A extends Δ₀_alt_A, and Δ₀_alt_A v = Δ₀_alt v
                  have : Δ₀_alt_A v = some d := by simp [Δ₀_alt_A_def, if_pos hv_StA, hΔ₀]
                  exact (hext_alt_A this).symm
                | none =>
                  -- Δ'_alt v = Δ'_alt_B v; need Δ'_alt_B v = Δ'_alt_A v
                  have hv_types : v ∈ StA.types := SMT.Typing.mem_context_of_mem_fv typ_A_enc hv
                  have hΔ₀_alt_B_v : Δ₀_alt_B v = Δ'_alt_A v := by
                    simp [Δ₀_alt_B_def, if_pos (StA_used_sub_StB hv_StA), hΔ₀, if_pos hv_types]
                  obtain ⟨dA, hdA⟩ := Option.isSome_iff_exists.mp (hcov_alt_A v hv)
                  have h_extends : Δ'_alt_B v = some dA := hext_alt_B (by rw [hΔ₀_alt_B_v, hdA])
                  rw [h_extends, hdA]
              have den_A_alt_enc_final : ⟦A_enc.abstract Δ'_alt hcov_A_alt⟧ˢ =
                  some ⟨Aenc_alt, (BType.set αx).toSMTType, hAenc_alt⟩ := by
                have hcongr := RenamingContext.denote_congr_of_agreesOnFV
                  (t := A_enc) (h1 := hcov_A_alt) (h2 := hcov_alt_A) hag_A_alt
                simpa [RenamingContext.denote] using hcongr.trans den_A_alt_enc
              have hag_B_alt : RenamingContext.AgreesOnFV Δ'_alt Δ'_alt_B B_enc := by
                intro v hv
                simp only [Δ'_alt_def]
                cases hΔ₀ : Δ₀_alt v with
                | some d =>
                  have hv_StB : v ∈ StB.env.usedVars := by
                    by_contra hv_not
                    exact absurd (Δ''_covers_B v hv) (by simp [Δ''_none_out v hv_not])
                  have : Δ₀_alt_B v = some d := by
                    simp only [Δ₀_alt_B_def, if_pos hv_StB, hΔ₀]
                  exact (hext_alt_B this).symm
                | none => rfl
              have den_B_alt_enc_final : ⟦B_enc.abstract Δ'_alt hcov_B_alt⟧ˢ =
                  some ⟨Benc_alt, (BType.set βx).toSMTType, hBenc_alt⟩ := by
                have hcongr := RenamingContext.denote_congr_of_agreesOnFV
                  (t := B_enc) (h1 := hcov_B_alt) (h2 := hcov_alt_B) hag_B_alt
                simpa [RenamingContext.denote] using hcongr.trans den_B_alt_enc
              -- Apply pfun_lambda_denotation for alt
              obtain ⟨den_pfun_alt, hden_pfun_alt, hty_pfun_alt, hretract_pfun_alt⟩ :=
                pfun_lambda_denotation
                  (αx := αx) (βx := βx)
                  (hcov_A := hcov_A_alt) (hcov_B := hcov_B_alt)
                  (h_den_A := den_A_alt_enc_final) (h_den_B := den_B_alt_enc_final)
                  (den_A_type := rfl) (den_B_type := rfl)
                  R_not_fv_A R_not_fv_B x_not_fv_A x_not_fv_B
                  y_not_fv_A y_not_fv_B y'_not_fv_A y'_not_fv_B
                  hR_ne_x hR_ne_y hR_ne_y' hx_ne_y hx_ne_y' hy_ne_y'
                  (htyp_A := typ_A_enc_B) (htyp_B := typ_B_enc)
                  (R_not_in_Γ := R_fresh)
                  (x_not_in_Γ := fun h => x_fresh (by rw [AList.mem_insert]; exact Or.inr h))
                  (y_not_in_Γ := fun h => y_fresh (by rw [AList.mem_insert]; exact Or.inr (by rw [AList.mem_insert]; exact Or.inr h)))
                  (y'_not_in_Γ := fun h => y'_fresh (by rw [AList.mem_insert]; exact Or.inr (by rw [AList.mem_insert]; exact Or.inr (by rw [AList.mem_insert]; exact Or.inr h))))
                  hcov_pfun_alt
              refine ⟨Δ'_alt, hcov_pfun_alt, den_pfun_alt, ?_, ?_, ?_, ?_, ?_, ?_⟩
              -- Extends Δ'_alt Δ₀_alt
              · intro v d hv; simp only [Δ'_alt_def, hv]
              -- Vanishing: ∀ v ∉ E'.usedVars, Δ'_alt v = none
              · intro v hv
                simp only [Δ'_alt_def]
                rw [Δ₀_alt_none_out v hv]
                exact Δ'_alt_B_none_out v (fun hmem => hv (by
                  rw [St₄_used_eq, St₃_used_eq, St₂_used_eq, St₁_used_eq]
                  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmem)))))
              -- Well-typedness: output wt
              · intro v d hv τ hτ
                simp only [Δ'_alt_def] at hv
                cases hΔ : Δ₀_alt v with
                | some d' => simp [hΔ] at hv; subst hv; exact Δ₀_alt_wt v d' hΔ τ hτ
                | none =>
                  simp [hΔ] at hv
                  apply Δ'_alt_B_wt_out v d hv τ
                  have hv_StB : v ∈ StB.env.usedVars := by
                    by_contra hv_not
                    exact absurd (Δ'_alt_B_none_out v hv_not) (by rw [hv]; exact Option.some_ne_none _)
                  have hv_ne_R : v ≠ R := fun h => R_not_used (h ▸ hv_StB)
                  have hv_ne_x : v ≠ x := fun h => x_not_used (St₁_used_eq ▸ List.mem_cons_of_mem _ (h ▸ hv_StB))
                  have hv_ne_y : v ≠ y := fun h => y_not_used (St₂_used_eq ▸ List.mem_cons_of_mem _ (St₁_used_eq ▸ List.mem_cons_of_mem _ (h ▸ hv_StB)))
                  have hv_ne_y' : v ≠ y' := fun h => y'_not_used (St₃_used_eq ▸ List.mem_cons_of_mem _ (St₂_used_eq ▸ List.mem_cons_of_mem _ (St₁_used_eq ▸ List.mem_cons_of_mem _ (h ▸ hv_StB))))
                  rw [St₄_types_eq] at hτ
                  rwa [AList.lookup_insert_ne hv_ne_y', AList.lookup_insert_ne hv_ne_y,
                    AList.lookup_insert_ne hv_ne_x, AList.lookup_insert_ne hv_ne_R] at hτ
              -- Denotation under Δ'_alt
              · exact hden_pfun_alt
              -- RDom for alt
              · exact ⟨by simp only [BType.toSMTType]; exact hty_pfun_alt,
                  by rw [hretract_pfun_alt, retract_A_alt, retract_B_alt]⟩
              -- dom_out
              · intro v hv
                simp only [Δ'_alt_def] at hv
                cases hΔ : Δ₀_alt v with
                | some d =>
                  exact fv_sub_typings (_root_.B.Typing.pfun typ_A typ_B)
                    (SMT.Typing.bool St₄.types true) v
                    (SMT.RenamingContext.ExtendsOnSourceFV.dom_sub_B_fv Δ₀_alt_ext v
                      (by rw [hΔ]; simp))
                | none =>
                  simp [hΔ] at hv
                  have h_StB := Δ'_alt_B_dom_out v hv
                  rw [St₄_types_eq, AList.mem_insert, AList.mem_insert, AList.mem_insert,
                    AList.mem_insert]
                  exact Or.inr (Or.inr (Or.inr (Or.inr h_StB)))
