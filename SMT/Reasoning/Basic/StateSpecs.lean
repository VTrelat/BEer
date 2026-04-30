import SMT.Reasoning.Defs
import SMT.Reasoning.LooseningDefs

set_option mvcgen.warning false

open SMT ZFSet Std.Do

theorem sInter_eq_empty_of_mem_empty {B : ZFSet} (hempty : (∅ : ZFSet) ∈ B) :
    (⋂₀ B : ZFSet) = ∅ := by
  apply ZFSet.subset_of_empty
  intro z hz
  rw [ZFSet.mem_sInter (by exact ⟨∅, hempty⟩)] at hz
  exact hz ∅ hempty

theorem sInter_sep_eq_empty_of_exists_eq_empty
    {D : ZFSet} {F : ZFSet → ZFSet}
    (hex : ∃ x ∈ D, F x = ∅) :
    (⋂₀ (ZFSet.sep (fun y => ∃ x ∈ D, y = F x) 𝔹) : ZFSet) = ∅ := by
  apply sInter_eq_empty_of_mem_empty
  rw [ZFSet.mem_sep]
  rcases hex with ⟨x, hxD, hFx⟩
  refine ⟨ZFSet.ZFBool.zffalse_mem_𝔹, ?_⟩
  exact ⟨x, hxD, hFx.symm⟩

theorem sInter_sep_eq_zftrue_of_forall_eq_zftrue
    {D : ZFSet} {F : ZFSet → ZFSet}
    (hne : ∃ x, x ∈ D)
    (hall : ∀ x ∈ D, F x = zftrue) :
    (⋂₀ (ZFSet.sep (fun y => ∃ x ∈ D, y = F x) 𝔹) : ZFSet) = zftrue := by
  let B : ZFSet := ZFSet.sep (fun y => ∃ x ∈ D, y = F x) 𝔹
  have hB_mem : (⋂₀ B : ZFSet) ∈ 𝔹 := by
    dsimp [B]
    exact ZFSet.sInter_sep_subset_of_𝔹_mem_𝔹 (fun _ ↦ id)
  have hB_nonempty : B.Nonempty := by
    rcases hne with ⟨x, hxD⟩
    refine ⟨zftrue, ?_⟩
    change zftrue ∈ ZFSet.sep (fun y => ∃ x ∈ D, y = F x) 𝔹
    rw [ZFSet.mem_sep]
    refine ⟨ZFSet.ZFBool.zftrue_mem_𝔹, ?_⟩
    exact ⟨x, hxD, (hall x hxD).symm⟩
  have hempty : ∅ ∈ (⋂₀ B : ZFSet) := by
    rw [ZFSet.mem_sInter hB_nonempty]
    intro y hy
    rw [ZFSet.mem_sep] at hy
    obtain ⟨_, x, hxD, rfl⟩ := hy
    rw [hall x hxD]
    exact ZFSet.mem_singleton.mpr rfl
  rw [ZFSet.ZFBool.mem_𝔹_iff] at hB_mem
  rcases hB_mem with hfalse | htrue
  · exfalso
    rw [hfalse] at hempty
    exact ZFSet.notMem_empty _ hempty
  · exact htrue

theorem exists_bool_eval_eq_zftrue_of_exists_true
    {D : ZFSet} {F : ZFSet → ZFSet.ZFBool}
    (hex : ∃ x ∈ D, F x = ⊤) :
    ZFSet.ZFBool.not
        ⟨⋂₀ (ZFSet.sep (fun y => ∃ x ∈ D, y = (ZFSet.ZFBool.not (F x)).1) 𝔹),
          ZFSet.sInter_sep_subset_of_𝔹_mem_𝔹 (fun _ ↦ id)⟩ = ⊤ := by
  have hsInter :
      (⋂₀ (ZFSet.sep (fun y => ∃ x ∈ D, y = (ZFSet.ZFBool.not (F x)).1) 𝔹) : ZFSet) = zffalse := by
    apply sInter_sep_eq_empty_of_exists_eq_empty
    rcases hex with ⟨x, hxD, hFx⟩
    refine ⟨x, hxD, ?_⟩
    rw [hFx, ZFSet.ZFBool.not_true_eq_false]
    rfl
  have hbool :
      (⟨⋂₀ (ZFSet.sep (fun y => ∃ x ∈ D, y = (ZFSet.ZFBool.not (F x)).1) 𝔹),
        ZFSet.sInter_sep_subset_of_𝔹_mem_𝔹 (fun _ ↦ id)⟩ : ZFSet.ZFBool) = ⊥ := by
    rw [Subtype.mk.injEq]
    exact hsInter
  rw [hbool, ZFSet.ZFBool.not_false_eq_true]

theorem exists_bool_eval_eq_zffalse_of_forall_false
    {D : ZFSet} {F : ZFSet → ZFSet.ZFBool}
    (hne : ∃ x, x ∈ D)
    (hall : ∀ x ∈ D, F x = ⊥) :
    ZFSet.ZFBool.not
        ⟨⋂₀ (ZFSet.sep (fun y => ∃ x ∈ D, y = (ZFSet.ZFBool.not (F x)).1) 𝔹),
          ZFSet.sInter_sep_subset_of_𝔹_mem_𝔹 (fun _ ↦ id)⟩ = ⊥ := by
  have hsInter :
      (⋂₀ (ZFSet.sep (fun y => ∃ x ∈ D, y = (ZFSet.ZFBool.not (F x)).1) 𝔹) : ZFSet) = zftrue := by
    apply sInter_sep_eq_zftrue_of_forall_eq_zftrue
    · exact hne
    · intro x hxD
      rw [hall x hxD, ZFSet.ZFBool.not_false_eq_true]
      rfl
  have hbool :
      (⟨⋂₀ (ZFSet.sep (fun y => ∃ x ∈ D, y = (ZFSet.ZFBool.not (F x)).1) 𝔹),
        ZFSet.sInter_sep_subset_of_𝔹_mem_𝔹 (fun _ ↦ id)⟩ : ZFSet.ZFBool) = ⊤ := by
    rw [Subtype.mk.injEq]
    exact hsInter
  rw [hbool, ZFSet.ZFBool.not_true_eq_false]

theorem not_sInter_sep_eq_zftrue_of_exists_eq_zffalse
    {D : ZFSet} {F : ZFSet → ZFSet}
    (hex : ∃ x ∈ D, F x = zffalse) :
    ZFSet.ZFBool.not
        ⟨⋂₀ (ZFSet.sep (fun y => ∃ x ∈ D, y = F x) 𝔹),
          ZFSet.sInter_sep_subset_of_𝔹_mem_𝔹 (fun _ ↦ id)⟩ = ⊤ := by
  have hsInter :
      (⋂₀ (ZFSet.sep (fun y => ∃ x ∈ D, y = F x) 𝔹) : ZFSet) = zffalse := by
    exact sInter_sep_eq_empty_of_exists_eq_empty hex
  have hbool :
      (⟨⋂₀ (ZFSet.sep (fun y => ∃ x ∈ D, y = F x) 𝔹),
        ZFSet.sInter_sep_subset_of_𝔹_mem_𝔹 (fun _ ↦ id)⟩ : ZFSet.ZFBool) = ⊥ := by
    rw [Subtype.mk.injEq]
    exact hsInter
  rw [hbool, ZFSet.ZFBool.not_false_eq_true]

theorem not_sInter_sep_eq_zffalse_of_forall_eq_zftrue
    {D : ZFSet} {F : ZFSet → ZFSet}
    (hne : ∃ x, x ∈ D)
    (hall : ∀ x ∈ D, F x = zftrue) :
    ZFSet.ZFBool.not
        ⟨⋂₀ (ZFSet.sep (fun y => ∃ x ∈ D, y = F x) 𝔹),
          ZFSet.sInter_sep_subset_of_𝔹_mem_𝔹 (fun _ ↦ id)⟩ = ⊥ := by
  have hsInter :
      (⋂₀ (ZFSet.sep (fun y => ∃ x ∈ D, y = F x) 𝔹) : ZFSet) = zftrue := by
    exact sInter_sep_eq_zftrue_of_forall_eq_zftrue hne hall
  have hbool :
      (⟨⋂₀ (ZFSet.sep (fun y => ∃ x ∈ D, y = F x) 𝔹),
        ZFSet.sInter_sep_subset_of_𝔹_mem_𝔹 (fun _ ↦ id)⟩ : ZFSet.ZFBool) = ⊤ := by
    rw [Subtype.mk.injEq]
    exact hsInter
  rw [hbool, ZFSet.ZFBool.not_true_eq_false]

theorem Option.get_fst_eq_of_isSome
    {o : Option SMT.Dom} {h₁ h₂ : o.isSome = true} :
    (o.get h₁).1 = (o.get h₂).1 := by
  cases o with
  | none =>
      simp at h₁
  | some d =>
      rfl

theorem update_swap {α β : Type _} [DecidableEq α] (f : α → β) {x y : α} (hxy : x ≠ y)
    (vx vy : β) :
    Function.update (Function.update f x vx) y vy =
      Function.update (Function.update f y vy) x vx := by
  funext z
  by_cases hz_x : z = x
  · subst hz_x
    simp [Function.update, hxy]
  · by_cases hz_y : z = y
    · subst hz_y
      simp [Function.update, hz_x]
    · simp [Function.update, hz_x, hz_y]

theorem denote_type_eq_of_typing
    {Γ : SMT.TypeContext} {t : SMT.Term} {τ : SMTType}
    {«Δ» : SMT.RenamingContext.Context}
    (typ_t : Γ ⊢ˢ t : τ)
    {hcov : SMT.RenamingContext.CoversFV «Δ» t}
    {D : SMT.Dom}
    (hden : ⟦t.abstract «Δ» hcov⟧ˢ = some D) :
    D.2.1 = τ := by
  have hτ' := SMT.PHOAS.denote_welltyped_eq
    (den_t := hden)
    (t := t.abstract «Δ» hcov)
    ?_
  on_goal 2 =>
    use SMT.TypeContext.abstract (Γ := Γ) («Δ» := «Δ»), PHOAS.WFTC.of_abstract, τ
    · apply PHOAS.Typing.of_abstract
      exact typ_t
  dsimp at hτ'
  exact hτ'.symm

theorem denote_isSome_update_of_notMem
    {«Δ» : SMT.RenamingContext.Context} {t : SMT.Term} {x : SMT.𝒱} {d : SMT.Dom}
    {h : SMT.RenamingContext.CoversFV «Δ» t}
    (hx : x ∉ SMT.fv t) :
    (SMT.RenamingContext.denote «Δ» t h).isSome =
      (SMT.RenamingContext.denote (Function.update «Δ» x (some d)) t
        (SMT.RenamingContext.coversFV_update_of_notMem (x := x) (d := d) hx h)).isSome := by
  simpa using congrArg Option.isSome
    (SMT.RenamingContext.denote_update_of_notMem («Δ» := «Δ») (t := t) (x := x) (d := d) (h := h) hx)

theorem denote_not_isSome_of_some_bool
    {t : SMT.PHOAS.Term SMT.Dom} {D : SMT.Dom}
    (hden : ⟦t⟧ˢ = some D)
    (hTy : D.2.1 = .bool) :
    (⟦¬ˢ' t⟧ˢ).isSome = true := by
  obtain ⟨d, τ, hd⟩ := D
  cases hTy
  rw [SMT.denote, hden]
  simp only [Option.pure_def, Option.failure_eq_none, Option.bind_eq_bind, Option.bind_some]
  rfl

theorem denote_not_eq_zffalse_of_some_zftrue
    {t : SMT.PHOAS.Term SMT.Dom} {D : SMT.Dom}
    (hden : ⟦t⟧ˢ = some D)
    (hTy : D.2.1 = .bool)
    (htrue : D.1 = zftrue) :
    ⟦¬ˢ' t⟧ˢ = some ⟨zffalse, .bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
  obtain ⟨d, τ, hd⟩ := D
  cases hTy
  obtain rfl := htrue
  rw [SMT.denote, hden]
  simp [Option.bind_some, Option.pure_def, overloadUnaryOp]
  congr
  · funext τ
    rw [dif_pos hd]
    simp only [ZFSet.symmDiff_self, subset_refl, subset_of_empty]
  · apply proof_irrel_heq

theorem denote_not_eq_zftrue_of_some_zffalse
    {t : SMT.PHOAS.Term SMT.Dom} {D : SMT.Dom}
    (hden : ⟦t⟧ˢ = some D)
    (hTy : D.2.1 = .bool)
    (hfalse : D.1 = zffalse) :
    ⟦¬ˢ' t⟧ˢ = some ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
  obtain ⟨d, τ, hd⟩ := D
  cases hTy
  obtain rfl := hfalse
  rw [SMT.denote, hden]
  simp [Option.bind_some, Option.pure_def, overloadUnaryOp]
  congr
  · funext τ
    rw [dif_pos hd]
    simp only [symmDiff_empty]
  · apply proof_irrel_heq

theorem denote_and_some_bool_of_some_bool
    {p q : SMT.PHOAS.Term SMT.Dom}
    {Dp Dq : SMT.Dom}
    (hp : ⟦p⟧ˢ = some Dp) (hpTy : Dp.2.1 = .bool)
    (hq : ⟦q⟧ˢ = some Dq) (hqTy : Dq.2.1 = .bool) :
    ∃ D : SMT.Dom, ⟦p ∧ˢ' q⟧ˢ = some D ∧ D.2.1 = .bool := by
  obtain ⟨dp, τp, hdp⟩ := Dp
  obtain ⟨dq, τq, hdq⟩ := Dq
  cases hpTy
  cases hqTy
  rw [SMT.denote, hp, hq]
  simp only [Option.pure_def, Option.failure_eq_none, Option.bind_eq_bind, Option.bind_some,
    Option.some.injEq, exists_eq_left']

theorem denote_and_eq_zftrue_of_some_zftrue
    {p q : SMT.PHOAS.Term SMT.Dom}
    {Dp Dq : SMT.Dom}
    (hp : ⟦p⟧ˢ = some Dp) (hpTy : Dp.2.1 = .bool) (hpTrue : Dp.1 = zftrue)
    (hq : ⟦q⟧ˢ = some Dq) (hqTy : Dq.2.1 = .bool) (hqTrue : Dq.1 = zftrue) :
    ⟦p ∧ˢ' q⟧ˢ = some ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
  obtain ⟨dp, τp, hdp⟩ := Dp
  obtain ⟨dq, τq, hdq⟩ := Dq
  cases hpTy
  cases hqTy
  obtain rfl := hpTrue
  obtain rfl := hqTrue
  rw [SMT.denote, hp, hq]
  simp only [
    overloadBinOp, Function.onFun, Option.pure_def, Option.failure_eq_none,
    Option.bind_eq_bind, Option.bind_some, and_self, Option.some.injEq, PSigma.mk.injEq,
    id_eq]
  conv_lhs =>
    rw [dif_pos ⟨hdp, hdq⟩]
  simp only [ZFSet.inter_self, true_and]
  congr
  · funext τ
    rw [dif_pos ⟨hdp, hdq⟩]
    simp only [ZFSet.inter_self]
  · apply proof_irrel_heq

theorem denote_and_eq_zffalse_of_some_zffalse_left
    {p q : SMT.PHOAS.Term SMT.Dom}
    {Dp Dq : SMT.Dom}
    (hp : ⟦p⟧ˢ = some Dp) (hpTy : Dp.2.1 = .bool) (hpFalse : Dp.1 = zffalse)
    (hq : ⟦q⟧ˢ = some Dq) (hqTy : Dq.2.1 = .bool) :
    ⟦p ∧ˢ' q⟧ˢ = some ⟨zffalse, .bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
  obtain ⟨dp, τp, hdp⟩ := Dp
  obtain ⟨dq, τq, hdq⟩ := Dq
  cases hpTy
  cases hqTy
  obtain rfl := hpFalse
  rw [SMT.denote, hp, hq]
  simp only [Option.pure_def, Option.failure_eq_none, Option.bind_eq_bind, Option.bind_some,
    Option.some.injEq, PSigma.mk.injEq, overloadBinOp, id_eq, Function.onFun]
  conv_lhs =>
    rw [dif_pos ⟨hdp, hdq⟩]
    conv =>
      enter [1]
      change  ⊥ ⋀ ⟨dq, hdq⟩
      rw [ZFBool.and_comm, ZFBool.and_false]
  simp only [ZFBool.bot_eq_false, true_and]
  congr
  · funext τ
    rw [dif_pos ⟨hdp, hdq⟩]
    conv_lhs =>
      enter [2]
      change  ⊥ ⋀ ⟨dq, hdq⟩
      rw [ZFBool.and_comm, ZFBool.and_false]
    simp only [ZFBool.bot_eq_false]
  · apply proof_irrel_heq

theorem denote_and_eq_zffalse_of_some_zffalse_right
    {p q : SMT.PHOAS.Term SMT.Dom}
    {Dp Dq : SMT.Dom}
    (hp : ⟦p⟧ˢ = some Dp) (hpTy : Dp.2.1 = .bool)
    (hq : ⟦q⟧ˢ = some Dq) (hqTy : Dq.2.1 = .bool) (hqFalse : Dq.1 = zffalse) :
    ⟦p ∧ˢ' q⟧ˢ = some ⟨zffalse, .bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
  obtain ⟨dp, τp, hdp⟩ := Dp
  obtain ⟨dq, τq, hdq⟩ := Dq
  cases hpTy
  cases hqTy
  obtain rfl := hqFalse
  rw [SMT.denote, hp, hq]
  simp only [
    Option.pure_def, Option.failure_eq_none, Option.bind_eq_bind, Option.bind_some,
    Option.some.injEq, PSigma.mk.injEq, overloadBinOp, id_eq, Function.onFun]
  conv_lhs =>
    rw [dif_pos ⟨hdp, hdq⟩]
    conv =>
      enter [1]
      change  ⟨dp, hdp⟩ ⋀ ⊥
      rw [ZFBool.and_false]
  simp only [ZFBool.bot_eq_false, true_and]
  congr
  · funext τ
    rw [dif_pos ⟨hdp, hdq⟩]
    conv_lhs =>
      enter [2]
      change  ⟨dp, hdp⟩ ⋀ ⊥
      rw [ZFBool.and_false]
    simp only [ZFBool.bot_eq_false]
  · apply proof_irrel_heq

theorem denote_pair_some_of_some
    {t₁ t₂ : SMT.PHOAS.Term SMT.Dom}
    {D₁ D₂ : SMT.Dom}
    (h₁ : ⟦t₁⟧ˢ = some D₁)
    (h₂ : ⟦t₂⟧ˢ = some D₂) :
    ∃ D : SMT.Dom, ⟦t₁.pair t₂⟧ˢ = some D ∧ D.2.1 = D₁.2.1.pair D₂.2.1 := by
  obtain ⟨X₁, τ₁, hX₁⟩ := D₁
  obtain ⟨X₂, τ₂, hX₂⟩ := D₂
  refine ⟨⟨X₁.pair X₂, τ₁.pair τ₂, ?_⟩, ?_, rfl⟩
  · simpa [SMTType.toZFSet, ZFSet.pair_mem_prod] using And.intro hX₁ hX₂
  · rw [SMT.denote, h₁, h₂]
    rw [Option.pure_def, Option.bind_eq_bind, Option.bind_some]
    rfl

theorem denote_eq_some_of_some
    {t₁ t₂ : SMT.PHOAS.Term SMT.Dom}
    {D₁ D₂ : SMT.Dom}
    (h₁ : ⟦t₁⟧ˢ = some D₁)
    (h₂ : ⟦t₂⟧ˢ = some D₂)
    (hτ : D₁.2.1 = D₂.2.1) :
    ∃ D : SMT.Dom, ⟦t₁ =ˢ' t₂⟧ˢ = some D ∧ D.2.1 = .bool := by
  classical
  obtain ⟨X₁, τ₁, hX₁⟩ := D₁
  obtain ⟨X₂, τ₂, hX₂⟩ := D₂
  cases hτ
  refine ⟨⟨overloadBinOp (A := ⟦τ₁⟧ᶻ) (B := 𝔹)
      (fun x => (↑x : ZFSet))
      (fun p => if p then ZFBool.true else ZFBool.false)
      ⊥ (fun x y => x = y) X₁ X₂, .bool, overloadBinOp_mem hX₁ hX₂⟩, ?_, rfl⟩
  rw [SMT.denote, h₁, h₂]
  dsimp
  rw [dif_pos rfl]

theorem denote_eq_eq_zftrue_of_fst_eq
    {t₁ t₂ : SMT.PHOAS.Term SMT.Dom}
    {D₁ D₂ : SMT.Dom}
    (h₁ : ⟦t₁⟧ˢ = some D₁)
    (h₂ : ⟦t₂⟧ˢ = some D₂)
    (hτ : D₁.2.1 = D₂.2.1)
    (hfst : D₁.1 = D₂.1) :
    ⟦t₁ =ˢ' t₂⟧ˢ = some ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
  obtain ⟨X₁, τ₁, hX₁⟩ := D₁
  obtain ⟨X₂, τ₂, hX₂⟩ := D₂
  cases hτ
  cases hfst
  rw [SMT.denote, h₁, h₂]
  simp only [«Prop».bot_eq_false, overloadBinOp, Function.onFun, dite_eq_ite, if_false_right,
    Option.pure_def, Option.failure_eq_none, Option.bind_eq_bind, Option.bind_some, ↓reduceDIte,
    and_self, and_true, Option.some.injEq, PSigma.mk.injEq]
  conv_lhs =>
    enter [1, 1]
    rw [if_pos (by rw [if_pos ⟨hX₁, hX₁⟩])]
  simp only [true_and]
  congr
  · funext τ
    rw [if_pos (by rw [if_pos ⟨hX₁, hX₁⟩])]
  · apply proof_irrel_heq

theorem denote_eq_true_implies_fst_eq
    {t₁ t₂ : SMT.PHOAS.Term SMT.Dom}
    {D₁ D₂ Deq : SMT.Dom}
    (h₁ : ⟦t₁⟧ˢ = some D₁)
    (h₂ : ⟦t₂⟧ˢ = some D₂)
    (hτ : D₁.2.1 = D₂.2.1)
    (hEq : ⟦t₁ =ˢ' t₂⟧ˢ = some Deq)
    (hTrue : Deq.1 = zftrue) :
    D₁.1 = D₂.1 := by
  obtain ⟨X₁, τ₁, hX₁⟩ := D₁
  obtain ⟨X₂, τ₂, hX₂⟩ := D₂
  cases hτ
  have hEq' := hEq
  rw [SMT.denote, h₁, h₂] at hEq'
  simp only [«Prop».bot_eq_false, overloadBinOp, Function.onFun, dite_eq_ite, Option.pure_def,
    Option.failure_eq_none, Option.bind_eq_bind, Option.bind_some, ↓reduceDIte, Option.some.injEq] at hEq'
  obtain ⟨Deq, τDeq, hDeq⟩ := Deq
  obtain rfl := hTrue
  injection hEq' with hEq'

  simp only [denote, h₁, h₂, «Prop».bot_eq_false, Option.pure_def, Option.failure_eq_none,
    Option.bind_eq_bind, Option.bind_some, ↓reduceDIte, Option.some.injEq, PSigma.mk.injEq, overloadBinOp, Function.onFun] at hEq
  obtain ⟨hEq, _⟩ := hEq
  rw [dif_pos ⟨hX₁, hX₂⟩] at hEq
  split_ifs at hEq with X₁_eq_X₂
  · exact X₁_eq_X₂
  · nomatch ZFSet.zftrue_ne_zffalse hEq.symm

theorem encode_type_context_subset (E : B.Env) :
  ⦃ λ _ ↦ ⌜True⌝ ⦄
  encodeTypeContext E
  ⦃ ⇓? () ⟨_, Γ⟩ => ⌜E.context.keys ⊆ Γ.keys⌝ ⦄ := by
  mintro pre
  unfold encodeTypeContext
  mvcgen

  case inv1 σ => exact ⇓? ⟨⟨pref, suff, eq⟩, ()⟩ ⟨E', Γ⟩ => ⌜pref.keys.Disjoint suff.keys ∧ pref.keys ⊆ Γ.keys⌝
  case vc1 _ pref cur suff eq _ fst _ _ snd _ inv ξ =>
    dsimp [ξ] at inv ⊢
    and_intros
    · intro v h
      rw [List.keys, List.mem_map] at h
      obtain ⟨⟨v, τ⟩, vτ_mem_pref_concat_cur, rfl⟩ := h
      rw [List.mem_append] at vτ_mem_pref_concat_cur
      rcases vτ_mem_pref_concat_cur with vτ_mem_pref | vτ_eq_cur
      · intro contr
        obtain ⟨disj, _⟩ := inv
        rw [List.disjoint_cons_right] at disj
        obtain ⟨_, disj⟩ := disj
        rw [List.disjoint_right] at disj
        nomatch disj contr <| List.mem_keys_of_mem vτ_mem_pref
      · intro contr
        have := List.NodupKeys.sublist (l₁ := cur :: suff) (List.sublist_append_right pref (cur :: suff)) <| eq ▸ E.context.nodupKeys
        rw [List.mem_singleton] at vτ_eq_cur
        subst cur
        rw [List.nodupKeys_cons] at this
        dsimp at this
        nomatch this.1 contr
    · rw [List.keys, List.map_append, List.map_singleton]
      rename EncoderState => σ
      obtain ⟨E', Γ⟩ := σ
      dsimp at inv ⊢
      rw [AList.keys_insert]
      intro z hz
      rw [List.mem_append, List.mem_singleton] at hz
      rcases hz with hz | rfl
      · rw [List.mem_cons, ←@not_not (z = _), ←imp_iff_not_or, ←ne_eq]
        intro z_neq
        refine (List.mem_erase_of_ne z_neq).mpr ?_
        apply inv.2 hz
      · exact List.mem_cons_self
  case vc6 => trivial
  case vc7 pref cur suff eq _ _ σ inv σ' =>
    dsimp [σ'] at inv ⊢
    and_intros
    · intro v h contr
      simp only [List.keys, List.map_append, List.map_cons, List.map_nil, List.mem_append,
        List.mem_map, Sigma.exists, exists_and_right, exists_eq_right, List.mem_cons,
        List.not_mem_nil, or_false] at h
      rcases h with ⟨τ, vτ_mem⟩ | rfl
      · obtain ⟨inv, _⟩ := inv
        rw [List.disjoint_cons_right] at inv
        exact inv.2 (List.mem_keys_of_mem vτ_mem) contr
      · have := List.NodupKeys.sublist (l₁ := cur :: suff) (List.sublist_append_right pref (cur :: suff)) <| eq ▸ E.context.nodupKeys
        rw [List.nodupKeys_cons] at this
        nomatch this.1 contr
    · rw [List.keys, List.map_append, List.map_singleton]
      rename EncoderState => σ
      obtain ⟨E', Γ⟩ := σ
      dsimp at inv ⊢
      rw [AList.keys_insert]
      intro z hz
      rw [List.mem_append, List.mem_singleton] at hz
      rcases hz with hz | rfl
      · rw [List.mem_cons, ←@not_not (z = _), ←imp_iff_not_or, ←ne_eq]
        intro z_neq
        refine (List.mem_erase_of_ne z_neq).mpr ?_
        apply inv.2 hz
      · exact List.mem_cons_self

  case vc8 σ => exact ⟨List.disjoint_nil_left _, List.nil_subset _⟩
  case vc9 h => exact And.casesOn h fun _ => id

  -- should not exist
  case vc2 => exact Encoder
  case vc3 => exact PostShape.arg EncoderState (PostShape.except String PostShape.pure)
  case vc4 => infer_instance
  case vc5 => infer_instance

theorem encode_type_context_keys_eq (E : B.Env) :
  ⦃ λ ⟨_, Γ⟩ ↦ ⌜Γ = ∅⌝ ⦄ encodeTypeContext E ⦃ ⇓? () ⟨_, Γ⟩ => ⌜E.context.keys = Γ.keys.reverse⌝ ⦄ := by
  unfold encodeTypeContext
  mvcgen
  case inv1 σ => exact ⇓? ⟨⟨pref, suff, eq⟩, ()⟩ ⟨E', Γ⟩ => ⌜pref.keys.Disjoint suff.keys ∧ pref.keys = Γ.keys.reverse⌝
  case vc1 pre cur suff eq _ _ _ _ _ σ inv ξ =>
    dsimp [ξ] at inv ⊢
    and_intros
    · rw [List.keys, List.map_append, List.disjoint_append_left, List.map_singleton, List.disjoint_cons_left]
      and_intros
      · exact List.disjoint_cons_right.mp inv.1 |>.2
      · have := List.NodupKeys.sublist (l₁ := cur :: suff) ?_ <| eq ▸ E.context.nodupKeys
        · rw [List.nodupKeys_cons] at this
          exact this.1
        · exact List.sublist_append_right pre (cur :: suff)
      · exact List.disjoint_nil_left (List.map Sigma.fst suff)
    · rw [List.keys, List.map_append, List.map_singleton, AList.keys_insert, List.reverse_cons, List.append_cancel_right_eq]
      rw [List.erase_of_not_mem]
      · exact inv.2
      · intro contr
        rw [←List.mem_reverse, ←inv.2] at contr
        nomatch List.disjoint_cons_right.mp inv.1 |>.1 contr
  case vc6 => trivial
  case vc7 pref cur suff eq _ _ _ inv ξ =>
    dsimp [ξ] at inv ⊢
    obtain ⟨pref_keys_disjoint, pref_keys_eq⟩ := inv
    and_intros
    · rw [List.keys, List.map_append, List.map_singleton, List.disjoint_append_left]
      and_intros
      · exact List.disjoint_of_disjoint_cons_right pref_keys_disjoint
      · have := List.NodupKeys.sublist (l₁ := cur :: suff) ?_ <| eq ▸ E.context.nodupKeys
        · rw [List.nodupKeys_cons] at this
          rw [List.disjoint_comm, List.disjoint_singleton]
          exact this.1
        · exact List.sublist_append_right pref (cur :: suff)
    · rw [List.keys, List.map_append, List.map_singleton, AList.keys_insert, List.reverse_cons, List.append_cancel_right_eq]
      rw [List.erase_of_not_mem]
      · exact pref_keys_eq
      · intro contr
        rw [←List.mem_reverse, ←pref_keys_eq] at contr
        nomatch List.disjoint_cons_right.mp pref_keys_disjoint |>.1 contr
  case vc8 pre =>
    dsimp
    rw [pre]
    exact ⟨List.disjoint_nil_left E.context.entries.keys, rfl⟩
  case vc9 inv =>
    rw [←inv.2]
    rfl
  -- should be inferred
  case vc2 =>
    exact Encoder
  case vc3 =>
    exact PostShape.arg EncoderState (PostShape.except String PostShape.pure)
  case vc4 =>
    infer_instance
  case vc5 =>
    infer_instance

@[spec]
theorem SMT.incrementFreshVarC_spec {n : ℕ} {Γ : TypeContext} {used} :
  ⦃ λ ⟨E, Γ'⟩ ↦ ⌜E.freshvarsc = n ∧ Γ' = Γ ∧ E.usedVars = used⌝ ⦄
  SMT.incrementFreshVarC
  ⦃ ⇓ m ⟨E', Γ'⟩ => ⌜Γ' = Γ ∧ m + 1 = E'.freshvarsc ∧ m = n ∧ E'.usedVars = used⌝ ⦄ := by
  unfold SMT.incrementFreshVarC
  mstart
  mintro pre ∀S
  mpure pre
  obtain ⟨rfl, rfl, rfl⟩ := pre
  mspec Std.Do.Spec.modifyGet_StateT

@[spec]
theorem SMT.freshVar_spec {Γ : TypeContext} {τ : SMTType} {name : String} {n : ℕ} {used : List SMT.𝒱} :
  ⦃ λ ⟨E, Γ'⟩ ↦ ⌜Γ' = Γ ∧ E.freshvarsc = n ∧ E.usedVars = used⌝⦄
  SMT.freshVar τ name
  ⦃ ⇓ v ⟨E', Γ'⟩ =>
    ⌜Γ' = Γ.insert v τ ∧ v ∉ Γ ∧ E'.freshvarsc = n + 1 ∧ E'.usedVars = v :: used ∧ v ∉ used⌝⦄ := by
  mstart
  mintro pre ∀St₀
  mpure pre
  obtain ⟨rfl, rfl, rfl⟩ := pre
  unfold SMT.freshVar
  mspec SMT.incrementFreshVarC_spec
  mrename_i pre
  next i =>
    mintro ∀St₁
    mpure pre
    obtain ⟨types_eq, fv_eq, rfl, used_eq⟩ := pre
    mspec Std.Do.Spec.modifyGet_StateT
    set usedAll : List SMT.𝒱 := St₀.env.usedVars ++ St₀.types.keys
    set v₀ := toString name ++ toString St₀.env.freshvarsc
    set v : SMT.𝒱 := if v₀ ∈ usedAll then SMT.superFresh usedAll else v₀
    have hv_not_usedAll : v ∉ usedAll := by
      dsimp [v]
      by_cases hv₀ : v₀ ∈ usedAll
      · simp [hv₀, SMT.superFresh_not_mem]
      · simp [hv₀]
    have hv_not_used : v ∉ St₀.env.usedVars := by
      intro hv
      exact hv_not_usedAll <| List.mem_append_left _ hv
    have hv_not_types : v ∉ St₀.types := by
      intro hv
      exact hv_not_usedAll <| List.mem_append_right _ ((AList.mem_keys).mp hv)
    mpure_intro
    and_intros
    · rw [types_eq]
    · simpa [v, usedAll, types_eq, used_eq] using hv_not_types
    · rw [fv_eq]
    · rw [used_eq]
    · simpa [v, usedAll, types_eq, used_eq] using hv_not_used

@[spec]
theorem SMT.addToContext_spec {v : SMT.𝒱} {ξ : SMTType} {Γ : TypeContext} {n} {used} :
  ⦃ λ ⟨E, Λ⟩ ↦ ⌜Λ = Γ ∧ E.freshvarsc = n ∧ E.usedVars = used⌝ ⦄
  SMT.addToContext v ξ
  ⦃ ⇓ () ⟨E, Λ⟩ => ⌜Λ = Γ.insert v ξ ∧ E.freshvarsc = n ∧ E.usedVars = v :: used⌝ ⦄ := by
  unfold SMT.addToContext
  mstart
  mintro pre ∀S
  mpure pre
  obtain ⟨rfl, rfl, rfl⟩ := pre
  mspec Std.Do.Spec.modifyGet_StateT

/-- Spec for the forIn loop that adds a list of (variable, type) pairs to the context.
    After the loop, types has all pairs inserted and usedVars has all variables prepended. -/
@[spec]
theorem SMT.addToContext_forIn_spec (pairs : List (SMT.𝒱 × SMTType)) {Γ : TypeContext} {n : ℕ} {used : List SMT.𝒱} :
  ⦃ λ ⟨E, Λ⟩ ↦ ⌜Λ = Γ ∧ E.freshvarsc = n ∧ E.usedVars = used⌝ ⦄
  forIn pairs PUnit.unit (fun (p : SMT.𝒱 × SMTType) _ => do SMT.addToContext p.1 p.2; pure (ForInStep.yield PUnit.unit))
  ⦃ ⇓ () ⟨E, Λ⟩ => ⌜Λ = pairs.foldl (fun Γ (p : SMT.𝒱 × SMTType) => Γ.insert p.1 p.2) Γ ∧
    E.freshvarsc = n ∧
    E.usedVars = pairs.foldl (fun used (p : SMT.𝒱 × SMTType) => p.1 :: used) used⌝ ⦄ := by
  induction pairs generalizing Γ used with
  | nil =>
    mintro pre ∀S; mpure pre; obtain ⟨rfl, rfl, rfl⟩ := pre
    simp only [List.forIn_nil]
    mpure_intro; exact ⟨rfl, rfl, rfl⟩
  | cons p pairs ih =>
    mintro pre ∀S; mpure pre; obtain ⟨rfl, rfl, rfl⟩ := pre
    simp only [List.forIn_cons, bind_assoc]
    mspec SMT.addToContext_spec
    mspec Std.Do.Spec.pure
    simp only [List.foldl_cons]
    exact ih

@[spec]
theorem SMT.eraseFromContext_spec {v : SMT.𝒱} {Γ : TypeContext} {n : ℕ} {used : List SMT.𝒱} :
  ⦃ λ ⟨E, Λ⟩ ↦ ⌜Λ = Γ ∧ E.freshvarsc = n ∧ E.usedVars = used⌝ ⦄
  SMT.eraseFromContext v
  ⦃ ⇓ () ⟨E, Λ⟩ => ⌜Λ = Γ.erase v ∧ E.freshvarsc = n ∧ E.usedVars = used⌝ ⦄ := by
  unfold SMT.eraseFromContext
  mstart
  mintro pre ∀S
  mpure pre
  obtain ⟨rfl, rfl, rfl⟩ := pre
  mspec Std.Do.Spec.modifyGet_StateT

/-- Spec for `freshVarList`: creates one fresh variable per type in the list.
    Returns a list `zs` of pairwise distinct variables, each fresh from the
    original `used` and `Γ`. The state's `freshvarsc` advances by `zs.length`,
    `usedVars` is extended by `zs.reverse`, and `types` is extended by
    inserting each `(zs[i], τs[i])` pair in order. -/
@[spec]
theorem SMT.freshVarList_spec (τs : List SMTType) {Γ : TypeContext} {n : ℕ} {used : List SMT.𝒱} :
  ⦃ λ ⟨E, Γ'⟩ ↦ ⌜Γ' = Γ ∧ E.freshvarsc = n ∧ E.usedVars = used⌝⦄
  SMT.freshVarList τs
  ⦃ ⇓ zs ⟨E', Γ'⟩ =>
    ⌜ zs.length = τs.length
      ∧ zs.Nodup
      ∧ (∀ z ∈ zs, z ∉ used)
      ∧ (∀ z ∈ zs, z ∉ Γ)
      ∧ E'.freshvarsc = n + zs.length
      ∧ E'.usedVars = zs.reverse ++ used
      ∧ Γ' = (zs.zip τs).foldl (fun Γ p => AList.insert p.1 p.2 Γ) Γ ⌝⦄ := by
  induction τs generalizing Γ n used with
  | nil =>
    mintro pre ∀S; mpure pre; obtain ⟨rfl, rfl, rfl⟩ := pre
    show _ ⊢ₛ wp⟦(pure [] : Encoder (List SMT.𝒱))⟧ _ _
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨rfl, List.nodup_nil, ?_, ?_, ?_, ?_, ?_⟩
    · intros _ hm; exact absurd hm List.not_mem_nil
    · intros _ hm; exact absurd hm List.not_mem_nil
    · simp
    · simp
    · simp
  | cons τ τs ih =>
    mintro pre ∀S; mpure pre; obtain ⟨rfl, rfl, rfl⟩ := pre
    show _ ⊢ₛ wp⟦(List.cons <$> SMT.freshVar τ <*> SMT.freshVarList τs : Encoder (List SMT.𝒱))⟧ _ _
    rw [show (List.cons <$> SMT.freshVar τ <*> SMT.freshVarList τs : Encoder (List SMT.𝒱)) =
         (do let v ← SMT.freshVar τ; let vs ← SMT.freshVarList τs; pure (v :: vs)) from rfl]
    mspec SMT.freshVar_spec
    rename_i v
    mrename_i pre; mintro ∀S₁; mpure pre
    obtain ⟨ins_eq, v_not_Γ, fv_eq, used_eq, v_not_used⟩ := pre
    mspec ih
    rename_i zs
    mrename_i pre; mintro ∀S₂; mpure pre
    obtain ⟨zs_len, zs_nodup, zs_not_used, zs_not_Γ, fv₂, used₂, Γ₂⟩ := pre
    have h_v_in_S1 : v ∈ S₁.env.usedVars := by rw [used_eq]; exact List.mem_cons_self ..
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [zs_len]
    · refine List.nodup_cons.mpr ⟨?_, zs_nodup⟩
      intro hv
      exact zs_not_used v hv h_v_in_S1
    · intro z hz h_z_S
      rcases List.mem_cons.mp hz with rfl | hz
      · exact v_not_used h_z_S
      · have h_z_S1 : z ∈ S₁.env.usedVars := by rw [used_eq]; exact List.mem_cons_of_mem _ h_z_S
        exact zs_not_used z hz h_z_S1
    · intro z hz h_z_S
      rcases List.mem_cons.mp hz with rfl | hz
      · exact v_not_Γ h_z_S
      · have h_z_S1 : z ∈ S₁.types := by rw [ins_eq]; exact (AList.mem_insert _).mpr (.inr h_z_S)
        exact zs_not_Γ z hz h_z_S1
    · rw [fv₂, fv_eq]; simp [List.length_cons]; omega
    · rw [used₂, used_eq]; simp [List.reverse_cons]
    · simp only [List.zip_cons_cons, List.foldl_cons]
      rw [Γ₂, ins_eq]

theorem SMT.eraseVars_forIn_spec (vars : List SMT.𝒱) {Γ : TypeContext} {n : ℕ} {used : List SMT.𝒱} :
  ⦃ λ ⟨E, Λ⟩ ↦ ⌜Λ = Γ ∧ E.freshvarsc = n ∧ E.usedVars = used⌝ ⦄
  forIn vars PUnit.unit (fun (v : SMT.𝒱) _ => do SMT.eraseFromContext v; pure (ForInStep.yield PUnit.unit))
  ⦃ ⇓ () ⟨E, Λ⟩ => ⌜Λ = vars.foldl (fun Γ v => Γ.erase v) Γ ∧ E.freshvarsc = n ∧ E.usedVars = used⌝ ⦄ := by
  induction vars generalizing Γ with
  | nil =>
    mintro pre ∀S; mpure pre; obtain ⟨rfl, rfl, rfl⟩ := pre
    simp only [List.forIn_nil]
    mpure_intro; exact ⟨rfl, rfl, rfl⟩
  | cons v vars ih =>
    mintro pre ∀S; mpure pre; obtain ⟨rfl, rfl, rfl⟩ := pre
    simp only [List.forIn_cons, bind_assoc]
    mspec SMT.eraseFromContext_spec
    mspec Std.Do.Spec.pure
    simp only [List.foldl_cons]
    exact ih

@[spec]
theorem SMT.defineFun_spec {v : SMT.𝒱} {τ σ : SMTType} {d : Term} {decl : SMT.Chunk} {as : SMT.Stages} {n} {Γ} {used}:
  ⦃ λ ⟨E, Λ⟩ ↦ ⌜E.declarations = decl ∧ E.asserts = as ∧ E.freshvarsc = n ∧ E.usedVars = used ∧ Λ = Γ⌝ ⦄
  SMT.defineFun v τ σ d
  ⦃ ⇓ () ⟨E, Λ⟩ => ⌜E.declarations = (decl.concat <| .define_fun v τ σ d) ∧ E.asserts = as ∧ E.freshvarsc = n ∧ E.usedVars = used ∧ Λ = Γ⌝ ⦄ := by
  unfold SMT.defineFun
  mstart
  mintro pre ∀S
  mpure pre
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := pre
  mspec Std.Do.Spec.modifyGet_StateT

@[spec]
theorem SMT.declareConst_spec {v : SMT.𝒱} {τ : SMTType} {decl : SMT.Chunk} {as : SMT.Stages} {n : ℕ} {Γ} {used}:
  ⦃ λ ⟨E, Λ⟩ ↦ ⌜E.declarations = decl ∧ E.asserts = as ∧ E.freshvarsc = n ∧ E.usedVars = used ∧ Λ = Γ⌝ ⦄
  SMT.declareConst v τ
  ⦃ ⇓ () ⟨E, Λ⟩ =>
      ⌜E.declarations = (decl.concat <| .declare_const v τ) ∧
        E.asserts = as ∧
        E.freshvarsc = n ∧
        E.usedVars = used ∧
        Λ = Γ⌝ ⦄ := by
  unfold SMT.declareConst
  mstart
  mintro pre ∀S
  mpure pre
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := pre
  mspec Std.Do.Spec.modifyGet_StateT

@[spec]
theorem SMT.addAssert_spec_total {t : Term} {as : SMT.Stages} {n : ℕ} {Γ} {used}:
  ⦃λ ⟨E, Λ⟩ ↦ ⌜(∀ is, E.asserts ≠ .instr is) ∧ E.asserts = as ∧ E.freshvarsc = n ∧ E.usedVars = used ∧ Λ = Γ⌝⦄
  SMT.addAssert t
  ⦃ ⇓ () ⟨E, Λ⟩ => ⌜E.asserts = addAssertAux as [.assert t] ∧ E.freshvarsc = n ∧ E.usedVars = used ∧ Λ = Γ⌝⦄ := by
  unfold SMT.addAssert
  mintro pre
  mspec Std.Do.Spec.get_StateT
  mintro ∀ σ
  intro ⟨pre, rfl, rfl, rfl, rfl⟩
  split using eq | eq
  · exact pre _ eq
  · mstart
    mspec Std.Do.Spec.modifyGet_StateT
    mpure_intro
    rw [eq]
    simp only [and_self]

@[spec]
theorem SMT.addAssert_spec {t : Term} {decl : SMT.Chunk} {as : SMT.Stages} {n : ℕ} {Γ} {used}:
  ⦃λ ⟨E, Λ⟩ ↦ ⌜E.declarations = decl ∧ E.asserts = as ∧ E.freshvarsc = n ∧ E.usedVars = used ∧ Λ = Γ⌝⦄
  SMT.addAssert t
  ⦃ ⇓? () ⟨E, Λ⟩ => ⌜E.declarations = decl ∧ E.asserts = addAssertAux as [.assert t] ∧ E.freshvarsc = n ∧ E.usedVars = used ∧ Λ = Γ⌝⦄ := by
  unfold SMT.addAssert
  mintro pre
  mspec Std.Do.Spec.get_StateT
  mintro ∀σ
  intro ⟨pre, rfl, rfl, rfl, rfl⟩
  split using eq | eq
  · trivial
  · mstart
    mspec Std.Do.Spec.modifyGet_StateT
    mpure_intro
    and_intros
    · rw [←pre]
    · rw [eq]
    · trivial
    · trivial
    · trivial

@[spec]
theorem SMT.addSpec_spec {x! : SMT.𝒱} {x!_spec : Term} {decl : SMT.Chunk} {as : SMT.Stages} {n} {Γ} {used}:
  ⦃ λ ⟨E, Λ⟩ ↦ ⌜E.declarations = decl ∧ E.asserts = as ∧ E.freshvarsc = n ∧ E.usedVars = used ∧ Λ = Γ⌝ ⦄
  SMT.addSpec x! x!_spec
  ⦃ ⇓? () ⟨E, Λ⟩ => ⌜
    E.declarations = (decl.concat <| .define_fun s!"{x!}_spec" .unit .bool x!_spec) ∧
    E.asserts = addAssertAux as [.assert <| .var s!"{x!}_spec"]
    ∧ E.freshvarsc = n ∧ E.usedVars = used ∧ Λ = Γ⌝⦄ := by
  unfold SMT.addSpec
  mstart
  mintro pre
  mintro ∀σ
  mpure pre
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := pre
  mspec SMT.defineFun_spec
  mintro ∀σ'
  mrename_i pre
  mpure pre
  obtain ⟨⟩ := pre
  mspec SMT.addAssert_spec

@[spec]
theorem SMT.Term.getType_spec {Γ : TypeContext} {t : Term} {α : SMTType} (typ_t : Γ ⊢ˢ t : α):
  ⦃ λ ⟨_, Γ'⟩ ↦ ⌜Γ' = Γ⌝ ⦄
  t.getType
  ⦃ ⇓? τ ⟨_, Γ'⟩ => ⌜Γ' = Γ ∧ τ = α⌝ ⦄ := by
  induction t using Term.rec' generalizing Γ α with
  | var v =>
    mintro pre ∀σ
    obtain ⟨E, Γ⟩ := σ
    intro h
    mstart
    unfold getType
    mvcgen
    apply Typing.varE at typ_t
    rw [h, typ_t, Option.get!_some]
    exact ⟨rfl, rfl⟩
  | int n =>
    mintro pre ∀σ
    obtain ⟨E, Γ⟩ := σ
    rintro rfl
    mstart
    unfold getType
    mvcgen
    obtain rfl := Typing.intE typ_t
    exact ⟨trivial, rfl⟩
  | bool b =>
    mintro pre ∀σ
    obtain ⟨E, Γ⟩ := σ
    rintro rfl
    mstart
    unfold getType
    mvcgen
    obtain rfl := Typing.boolE typ_t
    exact ⟨trivial, rfl⟩
  | app f x ihf ihx =>
    apply Typing.appE at typ_t
    obtain ⟨β, typ_f, typ_x⟩ := typ_t

    mstart
    mintro pre ∀σ₀
    mpure pre
    subst Γ
    unfold getType
    mspec ihf typ_f
    mrename_i pre
    mintro ∀σ₁
    mpure pre
    obtain ⟨pre, rfl⟩ := pre
    mspec ihx typ_x

    mrename_i pre
    mintro ∀σ₂
    mpure pre
    obtain ⟨pre, rfl⟩ := pre
    mvcgen
  | as t τ ih =>
    apply Typing.asE at typ_t
    obtain ⟨rfl, rfl, τ, rfl⟩ := typ_t

    mstart
    mintro pre ∀σ₁
    rintro ⟨⟩
    mstart
    mspec Std.Do.Spec.pure
  | eq t₁ t₂ _ _ =>
    apply Typing.eqE at typ_t
    obtain ⟨rfl, σ, typ_t₁, typ_t₂⟩ := typ_t
    mstart
    mintro pre ∀σ₀
    unfold getType
    mspec
  | and t₁ t₂ _ _ =>
    apply Typing.andE at typ_t
    obtain ⟨rfl, typ_t₁, typ_t₂⟩ := typ_t

    mstart
    mintro pre ∀σ₀
    unfold getType
    mspec
  | or t₁ t₂ _ _ =>
    apply Typing.orE at typ_t
    obtain ⟨rfl, typ_t₁, typ_t₂⟩ := typ_t

    mstart
    mintro pre ∀σ₀
    unfold getType
    mspec
  | not t _ =>
    apply Typing.notE at typ_t
    obtain ⟨rfl, typ_t⟩ := typ_t

    mstart
    mintro pre ∀σ₀
    unfold getType
    mspec
  | imp t₁ t₂ _ _ =>
    apply Typing.impE at typ_t
    obtain ⟨rfl, typ_t₁, typ_t₂⟩ := typ_t

    mstart
    mintro pre ∀σ₀
    unfold getType
    mspec
  | ite c t e ihc iht ihe =>
    apply Typing.iteE at typ_t
    obtain ⟨typ_c, typ_t, typ_e⟩ := typ_t

    mstart
    mintro pre ∀σ₀
    unfold getType
    mspec iht typ_t
  | some t ih =>
    apply Typing.someE at typ_t
    obtain ⟨τ, rfl, typ_t⟩ := typ_t

    mstart
    mintro pre ∀σ₀
    unfold getType
    mspec ih typ_t

    mrename_i pre
    mintro ∀σ₁
    mpure pre
    obtain ⟨pre, rfl⟩ := pre
    mspec
  | the t ih =>
    apply Typing.theE at typ_t

    mstart
    mintro pre ∀σ₀
    mpure pre
    subst Γ
    unfold getType
    mspec ih typ_t
    mintro ∀σ₁
    mrename_i pre
    mpure pre
    obtain ⟨pre, rfl⟩ := pre
    conv =>
      enter [2,1,1]
      dsimp
    mspec
  | pair t₁ t₂ iht₁ iht₂ =>
    apply Typing.pairE at typ_t
    obtain ⟨α, β, rfl, typ_t₁, typ_t₂⟩ := typ_t

    mstart
    mintro pre ∀σ₀
    mpure pre
    subst Γ
    unfold getType
    mspec iht₁ typ_t₁
    mrename_i pre
    mintro ∀σ₁
    mpure pre
    obtain ⟨pre, rfl⟩ := pre
    mspec iht₂ typ_t₂
    mintro ∀σ₂
    mrename_i pre
    mpure pre
    obtain ⟨pre, rfl⟩ := pre
    mspec
  | none => nomatch Typing.noneE typ_t
  | fst t ih
  | snd t ih =>
    first
    | apply Typing.fstE at typ_t
    | apply Typing.sndE at typ_t
    obtain ⟨σ, typ_t⟩ := typ_t

    mstart
    mintro pre ∀σ₀
    mpure pre
    subst Γ
    unfold getType
    mspec ih typ_t
    mintro ∀σ₁
    mrename_i pre
    mpure pre
    obtain ⟨pre, rfl⟩ := pre
    conv =>
      enter [2,1,1]
      dsimp
    mspec
  | distinct ts ih
  | le t₁ t₂ _ _
  | add t₁ t₂ _ _
  | sub t₁ t₂ _ _
  | mul t₁ t₂ _ _ =>
    first
    | apply Typing.distinctE at typ_t
    | apply Typing.leE at typ_t
    | apply Typing.addE at typ_t
    | apply Typing.subE at typ_t
    | apply Typing.mulE at typ_t
    obtain ⟨rfl, typ_t₁, typ_t₂⟩ := typ_t

    mstart
    mintro pre ∀σ₀
    unfold getType
    mspec
  | lambda vs τs f ih =>
    apply Typing.lambdaE at typ_t
    obtain ⟨len_pos, len_eq, γ, vs_Γ_disj, vs_fresh, rfl, typ_f⟩ := typ_t

    mstart
    mintro pre ∀σ₀
    mpure pre
    subst Γ
    unfold getType
    conv =>
      enter [2,1,1]
      rw [dite_cond_eq_true (eq_true len_eq)]
    mspec Std.Do.Spec.get_StateT
    mspec Std.Do.Spec.modifyGet_StateT
    mspec ih typ_f

    mintro ∀σ₁
    mrename_i pre
    mpure pre
    obtain ⟨pre, ⟨⟩⟩ := pre

    split <;> mspec
  | «forall» vs τs t
  | «exists» v τs t =>
    first
    | apply Typing.forallE at typ_t
    | apply Typing.existsE at typ_t
    obtain ⟨rfl, vs_Γ_disj, len_pos, len_eq, typ_t⟩ := typ_t
    mstart
    mintro pre ∀σ₀
    unfold getType
    mspec
