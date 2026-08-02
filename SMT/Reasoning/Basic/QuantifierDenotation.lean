import SMT.Reasoning.Defs
import SMT.Reasoning.LooseningDefs
import SMT.Reasoning.Basic.StateSpecs
import SMT.Reasoning.Basic.LoosenAuxExact.FunAux
import SMT.Reasoning.Basic.DenotationTotality
import SMT.Reasoning.Basic.EncodeTermBvUsed

open Std.Do B SMT ZFSet

/-! # Denotation helpers for encoded quantifiers -/

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
theorem denote_app_var_pair_var_var.{u}
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

theorem denote_and_iff_zftrue.{u}
    {p q : SMT.PHOAS.Term SMT.Dom} {Dp Dq : SMT.Dom.{u}}
    (hp : ⟦p⟧ˢ = some Dp) (hpType : Dp.snd.fst = SMTType.bool)
    (hq : ⟦q⟧ˢ = some Dq) (hqType : Dq.snd.fst = SMTType.bool) :
    ∃ D : SMT.Dom.{u},
      ⟦p ∧ˢ' q⟧ˢ = some D ∧
      D.snd.fst = SMTType.bool ∧
      (D.fst = ZFSet.zftrue ↔
        Dp.fst = ZFSet.zftrue ∧ Dq.fst = ZFSet.zftrue) := by
  obtain ⟨D, hD, hDType⟩ :=
    denote_and_some_bool_of_some_bool hp hpType hq hqType
  refine ⟨D, hD, hDType, ?_⟩
  constructor
  · intro htrue
    exact denote_and_both_zftrue_of_zftrue
      hp hpType hq hqType hD htrue
  · intro hparts
    have htrueDen := denote_and_eq_zftrue_of_some_zftrue
      hp hpType hparts.1 hq hqType hparts.2
    have hEq : D =
        (⟨ZFSet.zftrue, SMTType.bool,
          ZFSet.ZFBool.zftrue_mem_𝔹⟩ : SMT.Dom) :=
      Option.some.inj (hD.symm.trans htrueDen)
    exact congrArg (fun d : SMT.Dom => d.fst) hEq

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

theorem funBinaryForallTotal.{u}
    {Delta : SMT.RenamingContext.Context.{u}} {body : SMT.Term}
    {a b : SMT.𝒱} {rho sigma : SMTType}
    (hcovForall : SMT.RenamingContext.CoversFV Delta
      (SMT.Term.forall [a, b] [rho, sigma] body))
    (hgo : ∀ v, v ∈ SMT.fv body → v ∉ [a, b] →
      (Delta v).isSome = true)
    (hcovBody : ∀ A B : SMT.Dom.{u},
      SMT.RenamingContext.CoversFV
        (Function.update (Function.update Delta a (some A)) b (some B))
        body)
    (total : ∀ A B : SMT.Dom.{u}, A.snd.fst = rho →
      B.snd.fst = sigma →
      (⟦body.abstract
        (Function.update (Function.update Delta a (some A)) b (some B))
        (hcovBody A B)⟧ˢ).isSome = true) :
    (⟦(SMT.Term.forall [a, b] [rho, sigma] body).abstract
      Delta hcovForall⟧ˢ).isSome = true := by
  rw [SMT.Term.abstract, dif_pos (by rfl), SMT.denote]
  have hlen : [a, b].length > 0 := by simp
  rw [dif_pos hlen]
  split_ifs with hsome
  · rfl
  · exfalso
    apply hsome
    intro w hw
    have hgoPair := funAbstractGoPair hgo hcovBody w (by
      intro i
      have hi : i.1 = 0 ∨ i.1 = 1 := by
        have hiLt : i.1 < 2 := i.2
        omega
      rcases hi with hi | hi
      · have hi' : i = ⟨0, by simp⟩ := Fin.ext hi
        cases hi'
        simpa using hw ⟨0, by simp⟩
      · have hi' : i = ⟨1, by simp⟩ := Fin.ext hi
        cases hi'
        simpa using hw ⟨1, by simp⟩)
    rw [hgoPair]
    exact total (w ⟨0, by simp⟩) (w ⟨1, by simp⟩)
      (by simpa using (hw ⟨0, by simp⟩).1)
      (by simpa using (hw ⟨1, by simp⟩).1)

set_option maxHeartbeats 8000000 in
theorem funBinaryForallEqZftrue.{u}
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
theorem funBinaryForallTrueAt.{u}
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

theorem funBinaryForallIffZftrue.{u}
    {Delta : SMT.RenamingContext.Context.{u}} {body : SMT.Term}
    {a b : SMT.𝒱} {rho sigma : SMTType}
    (Q : SMT.Dom.{u} → SMT.Dom.{u} → Prop)
    (hcovForall : SMT.RenamingContext.CoversFV Delta
      (SMT.Term.forall [a, b] [rho, sigma] body))
    (hgo : ∀ v, v ∈ SMT.fv body → v ∉ [a, b] →
      (Delta v).isSome = true)
    (hcovBody : ∀ A B : SMT.Dom.{u},
      SMT.RenamingContext.CoversFV
        (Function.update (Function.update Delta a (some A)) b (some B))
        body)
    (bodyTotal : ∀ A B : SMT.Dom.{u}, A.snd.fst = rho →
      B.snd.fst = sigma →
      (⟦body.abstract
        (Function.update (Function.update Delta a (some A)) b (some B))
        (hcovBody A B)⟧ˢ).isSome = true)
    (bodyType : ∀ A B : SMT.Dom.{u}, A.snd.fst = rho →
      B.snd.fst = sigma → ∀ {D : SMT.Dom.{u}},
      ⟦body.abstract
        (Function.update (Function.update Delta a (some A)) b (some B))
        (hcovBody A B)⟧ˢ = some D → D.snd.fst = SMTType.bool)
    (bodyIff : ∀ A B : SMT.Dom.{u}, A.snd.fst = rho →
      B.snd.fst = sigma → ∀ {D : SMT.Dom.{u}},
      ⟦body.abstract
        (Function.update (Function.update Delta a (some A)) b (some B))
        (hcovBody A B)⟧ˢ = some D →
      (D.fst = ZFSet.zftrue ↔ Q A B)) :
    ∃ D : SMT.Dom.{u},
      ⟦(SMT.Term.forall [a, b] [rho, sigma] body).abstract
        Delta hcovForall⟧ˢ = some D ∧
      D.snd.fst = SMTType.bool ∧
      (D.fst = ZFSet.zftrue ↔
        ∀ A B : SMT.Dom.{u}, A.snd.fst = rho →
          B.snd.fst = sigma → Q A B) := by
  obtain ⟨D, hD⟩ := Option.isSome_iff_exists.mp
    (funBinaryForallTotal hcovForall hgo hcovBody bodyTotal)
  refine ⟨D, hD, ?_, ?_⟩
  · have hD' := hD
    rw [SMT.Term.abstract, dif_pos (by rfl)] at hD'
    exact denote_forall_ty hD'
  · constructor
    · intro htrue A B hA hB
      obtain ⟨Db, hDb, hDbTrue⟩ := funBinaryForallTrueAt
        hcovForall hgo hcovBody bodyTotal bodyType
        hD htrue A B hA hB
      exact (bodyIff A B hA hB hDb).mp hDbTrue
    · intro hall
      have htrueDen := funBinaryForallEqZftrue
        hcovForall hgo hcovBody bodyTotal bodyType (by
          intro A B hA hB
          obtain ⟨Db, hDb⟩ := Option.isSome_iff_exists.mp
            (bodyTotal A B hA hB)
          exact ⟨Db, hDb,
            (bodyIff A B hA hB hDb).mpr (hall A B hA hB)⟩)
      have hEq : D =
          (⟨ZFSet.zftrue, SMTType.bool,
            ZFSet.ZFBool.zftrue_mem_𝔹⟩ : SMT.Dom) :=
        Option.some.inj (hD.symm.trans htrueDen)
      exact congrArg (fun d : SMT.Dom => d.fst) hEq

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

theorem funTernaryForallTotal.{u}
    {Delta : SMT.RenamingContext.Context.{u}} {body : SMT.Term}
    {a b c : SMT.𝒱} {rho sigma tau : SMTType}
    (hcovForall : SMT.RenamingContext.CoversFV Delta
      (SMT.Term.forall [a, b, c] [rho, sigma, tau] body))
    (hgo : ∀ v, v ∈ SMT.fv body → v ∉ [a, b, c] →
      (Delta v).isSome = true)
    (hcovBody : ∀ A B C : SMT.Dom.{u},
      SMT.RenamingContext.CoversFV
        (Function.update
          (Function.update
            (Function.update Delta a (some A)) b (some B))
          c (some C))
        body)
    (total : ∀ A B C : SMT.Dom.{u}, A.snd.fst = rho →
      B.snd.fst = sigma → C.snd.fst = tau →
      (⟦body.abstract
        (Function.update
          (Function.update
            (Function.update Delta a (some A)) b (some B))
          c (some C))
        (hcovBody A B C)⟧ˢ).isSome = true) :
    (⟦(SMT.Term.forall [a, b, c] [rho, sigma, tau] body).abstract
      Delta hcovForall⟧ˢ).isSome = true := by
  rw [SMT.Term.abstract, dif_pos (by rfl), SMT.denote]
  have hlen : [a, b, c].length > 0 := by simp
  rw [dif_pos hlen]
  split_ifs with hsome
  · rfl
  · exfalso
    apply hsome
    intro w hw
    have hgoTriple := funAbstractGoTriple
      (Δctx := Delta) (P := body) (v₁ := a) (v₂ := b) (v₃ := c)
      (τ₁ := rho) (τ₂ := sigma) (τ₃ := tau)
      hgo hcovBody w (by
        intro i
        have hi : i.1 = 0 ∨ i.1 = 1 ∨ i.1 = 2 := by
          have hiLt : i.1 < 3 := i.2
          omega
        rcases hi with hi | hi | hi
        · have hi' : i = ⟨0, by simp⟩ := Fin.ext hi
          cases hi'
          simpa using hw ⟨0, by simp⟩
        · have hi' : i = ⟨1, by simp⟩ := Fin.ext hi
          cases hi'
          simpa using hw ⟨1, by simp⟩
        · have hi' : i = ⟨2, by simp⟩ := Fin.ext hi
          cases hi'
          simpa using hw ⟨2, by simp⟩)
    rw [hgoTriple]
    exact total (w ⟨0, by simp⟩) (w ⟨1, by simp⟩) (w ⟨2, by simp⟩)
      (by simpa using (hw ⟨0, by simp⟩).1)
      (by simpa using (hw ⟨1, by simp⟩).1)
      (by simpa using (hw ⟨2, by simp⟩).1)

set_option maxHeartbeats 8000000 in
theorem funTernaryForallEqZftrue.{u}
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
theorem funTernaryForallTrueAt.{u}
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

theorem funTernaryForallIffZftrue.{u}
    {Delta : SMT.RenamingContext.Context.{u}} {body : SMT.Term}
    {a b c : SMT.𝒱} {rho sigma tau : SMTType}
    (Q : SMT.Dom.{u} → SMT.Dom.{u} → SMT.Dom.{u} → Prop)
    (hcovForall : SMT.RenamingContext.CoversFV Delta
      (SMT.Term.forall [a, b, c] [rho, sigma, tau] body))
    (hgo : ∀ v, v ∈ SMT.fv body → v ∉ [a, b, c] →
      (Delta v).isSome = true)
    (hcovBody : ∀ A B C : SMT.Dom.{u},
      SMT.RenamingContext.CoversFV
        (Function.update
          (Function.update
            (Function.update Delta a (some A)) b (some B))
          c (some C))
        body)
    (bodyTotal : ∀ A B C : SMT.Dom.{u}, A.snd.fst = rho →
      B.snd.fst = sigma → C.snd.fst = tau →
      (⟦body.abstract
        (Function.update
          (Function.update
            (Function.update Delta a (some A)) b (some B))
          c (some C))
        (hcovBody A B C)⟧ˢ).isSome = true)
    (bodyType : ∀ A B C : SMT.Dom.{u}, A.snd.fst = rho →
      B.snd.fst = sigma → C.snd.fst = tau →
      ∀ {D : SMT.Dom.{u}},
      ⟦body.abstract
        (Function.update
          (Function.update
            (Function.update Delta a (some A)) b (some B))
          c (some C))
        (hcovBody A B C)⟧ˢ = some D → D.snd.fst = SMTType.bool)
    (bodyIff : ∀ A B C : SMT.Dom.{u}, A.snd.fst = rho →
      B.snd.fst = sigma → C.snd.fst = tau →
      ∀ {D : SMT.Dom.{u}},
      ⟦body.abstract
        (Function.update
          (Function.update
            (Function.update Delta a (some A)) b (some B))
          c (some C))
        (hcovBody A B C)⟧ˢ = some D →
      (D.fst = ZFSet.zftrue ↔ Q A B C)) :
    ∃ D : SMT.Dom.{u},
      ⟦(SMT.Term.forall [a, b, c] [rho, sigma, tau] body).abstract
        Delta hcovForall⟧ˢ = some D ∧
      D.snd.fst = SMTType.bool ∧
      (D.fst = ZFSet.zftrue ↔
        ∀ A B C : SMT.Dom.{u}, A.snd.fst = rho →
          B.snd.fst = sigma → C.snd.fst = tau → Q A B C) := by
  obtain ⟨D, hD⟩ := Option.isSome_iff_exists.mp
    (funTernaryForallTotal hcovForall hgo hcovBody bodyTotal)
  refine ⟨D, hD, ?_, ?_⟩
  · have hD' := hD
    rw [SMT.Term.abstract, dif_pos (by rfl)] at hD'
    exact denote_forall_ty hD'
  · constructor
    · intro htrue A B C hA hB hC
      obtain ⟨Db, hDb, hDbTrue⟩ := funTernaryForallTrueAt
        hcovForall hgo hcovBody bodyTotal bodyType
        hD htrue A B C hA hB hC
      exact (bodyIff A B C hA hB hC hDb).mp hDbTrue
    · intro hall
      have htrueDen := funTernaryForallEqZftrue
        hcovForall hgo hcovBody bodyTotal bodyType (by
          intro A B C hA hB hC
          obtain ⟨Db, hDb⟩ := Option.isSome_iff_exists.mp
            (bodyTotal A B C hA hB hC)
          exact ⟨Db, hDb,
            (bodyIff A B C hA hB hC hDb).mpr
              (hall A B C hA hB hC)⟩)
      have hEq : D =
          (⟨ZFSet.zftrue, SMTType.bool,
            ZFSet.ZFBool.zftrue_mem_𝔹⟩ : SMT.Dom) :=
        Option.some.inj (hD.symm.trans htrueDen)
      exact congrArg (fun d : SMT.Dom => d.fst) hEq
