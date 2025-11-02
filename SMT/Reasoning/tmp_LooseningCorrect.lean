import Encoder.Loosening
import SMT.Reasoning.Defs
import Std.Tactic.Do

open Classical in
noncomputable def ZFSet.Option.flift {A B : ZFSet} (f : ZFSet) (hf : IsFunc A B f := by zfun) : {f' : ZFSet // IsFunc (Option.toZFSet A) (Option.toZFSet B) f'} :=
  let f' : ZFSet :=
    λᶻ: Option.toZFSet A → Option.toZFSet B
      |          x       ↦ if hx : x ∈ Option.toZFSet A then
                              if isSome : ∃ y, ⟨x, hx⟩ = some y then
                                let ⟨y, hy⟩ := Classical.choose isSome
                                some (S := B) (@ᶻf ⟨y, by rwa [ZFSet.is_func_dom_eq]⟩) |>.val
                              else none (S := B).val
                            else ∅
  have hf' : IsFunc (Option.toZFSet A) (Option.toZFSet B) f' := by
    apply ZFSet.lambda_isFunc
    intro x hx
    rw [dite_cond_eq_true (eq_true hx)]
    split_ifs with isSome <;> apply SetLike.coe_mem
  ⟨f', hf'⟩


open Std.Do SMT ZFSet

namespace ShapeForcing

/- Base sorts only cast to themselves. -/
@[simp] lemma unit_cast_true_iff  {β} :
  ((SMTType.unit ⊑ β) = true) ↔ β = .unit := by
  cases β <;> simp [castable?]
@[simp] lemma cast_unit_true_iff'  {β} :
  ((β ⊑ SMTType.unit) = true) ↔ β = .unit := by
  cases β <;> simp [castable?]

@[simp] lemma int_cast_true_iff   {β} :
  ((SMTType.int  ⊑ β) = true) ↔ β = .int := by
  cases β <;> simp [castable?]
@[simp] lemma cast_int_true_iff   {β} :
  ((β ⊑ SMTType.int) = true) ↔ β = .int := by
  cases β <;> simp [castable?]

@[simp] lemma bool_cast_true_iff  {β} :
  ((SMTType.bool ⊑ β) = true) ↔ β = .bool := by
  cases β <;> simp [castable?]
@[simp] lemma cast_bool_true_iff  {β} :
  ((β ⊑ SMTType.bool) = true) ↔ β = .bool := by
  cases β <;> simp [castable?]

/- Pairs only cast to pairs, componentwise. -/

@[simp] lemma pair_cast_true_iff {α₁ α₂ β} :
  (((.pair α₁ α₂) ⊑ β) = true) ↔
    ∃ β₁ β₂, β = .pair β₁ β₂ ∧ (α₁ ⊑ β₁) = true ∧ (α₂ ⊑ β₂) = true := by
  cases β <;> simp [castable?, Bool.and_eq_true]
@[simp] lemma cast_pair_true_iff {α₁ α₂ β} :
  ((β ⊑ (.pair α₁ α₂)) = true) ↔
    ∃ β₁ β₂, β = .pair β₁ β₂ ∧ (β₁ ⊑ α₁) = true ∧ (β₂ ⊑ α₂) = true := by
  cases β <;> simp [castable?, Bool.and_eq_true]

/- Options only cast to options, pointwise. -/

@[simp] lemma option_cast_true_iff {α β} :
  (((.option α) ⊑ β) = true) ↔ ∃ β', β = .option β' ∧ (α ⊑ β') = true := by
  cases β <;> simp [castable?]
@[simp] lemma cast_option_true_iff {α β} :
  ((β ⊑ (.option α)) = true) ↔ ∃ β', β = .option β' ∧ (β' ⊑ α) = true := by
  cases β <;> simp [castable?]

/- Predicates are covariant in the domain. -/
@[simp] lemma fun_bool_cast_true_iff {α β} :
  (((.fun α .bool) ⊑ β) = true) ↔ ∃ α', β = .fun α' .bool ∧ (α ⊑ α') = true := by
  induction β <;> simp [castable?]
  case «fun» τ σ τ_ih σ_ih =>
    iff_rintro h ⟨rfl, h⟩
    · cases σ with
      | bool =>
        unfold castable? at h
        split at h <;> injections <;>
        · subst_vars
          exact ⟨rfl, h⟩
      | unit | «fun» | option | pair | int => simp only [castable?, Bool.false_eq_true] at h
    · unfold castable?
      split <;> injections
      · subst_vars
        exact h
      · subst_vars
        exact h
      · rename_i contr _ _ _ _ _
        nomatch contr α τ rfl rfl

@[simp] lemma cast_fun_bool_true_iff {α β} :
  ((β ⊑ (.fun α .bool)) = true) ↔
    (∃ α', β = .fun α' .bool ∧ (α' ⊑ α) = true) ∨
    (∃ α' β' α'' β'', β = .fun α' (.option β') ∧ α = .pair α'' β'' ∧ (α' ⊑ α'') = true ∧ (β' ⊑ β'') = true) := by
  induction β generalizing α
  case «fun» τ σ τ_ih σ_ih =>
    iff_rintro h ( ⟨_, ⟨⟩, h⟩ | ⟨α', β', α'', β'', ⟨⟩, rfl, τ_α'', σ_β''⟩ )
    · cases σ with
      | bool =>
        simp only [fun_bool_cast_true_iff, SMTType.fun.injEq, and_true, exists_eq_left'] at h
        left
        use τ
      | pair | int | unit | «fun» => simp only [castable?, Bool.false_eq_true] at h
      | option σ =>
        unfold castable? at h
        split at h <;> injections
        subst_eqs
        rw [Bool.and_eq_true] at h
        rename_i δ γ
        right
        use τ, σ, δ, γ
    · simpa only [fun_bool_cast_true_iff, SMTType.fun.injEq, and_true, exists_eq_left']
    · unfold castable?
      simp only [Bool.and_eq_true]
      exact ⟨τ_α'', σ_β''⟩
  all_goals simp only [castable?, Bool.false_eq_true, reduceCtorEq, false_and, exists_const, or_self]

/- Option-valued functions: either widen to another option-valued function or view as its graph predicate over pairs. -/
@[simp] lemma fun_opt_cast_true_iff {α β γ} :
  (((.fun α (.option β)) ⊑ γ) = true) ↔
    (∃ α' β', γ = .fun α' (.option β') ∧ (α ⊑ α') = true ∧ (β ⊑ β') = true) ∨
    (∃ α' β', γ = .fun (.pair α' β') .bool ∧ (α ⊑ α') = true ∧ (β ⊑ β') = true) := by
  induction γ generalizing α β <;> simp [castable?]
  case «fun» τ σ τ_ih σ_ih =>
    stop
    iff_rintro h ( ⟨α', β', ⟨rfl, rfl⟩, τ_α, β_β'⟩ | ⟨α', β', ⟨rfl, rfl⟩, α'_α, β_β'⟩ )
    · cases σ with
      | «fun» | pair | unit | int => simp only [castable?, Bool.false_eq_true] at h
      | bool =>
        unfold castable? at h
        split at h <;> injections
        subst_vars
        rename_i _ _ δ γ
        rw [Bool.and_eq_true] at h
        right
        use δ, γ
      | option σ =>
        left
        simp only [castable?, Bool.and_eq_true] at h
        use τ, σ
    · unfold castable?
      simp only [Bool.and_eq_true]
      exact ⟨τ_α, β_β'⟩
    · unfold castable?
      simp only [Bool.and_eq_true]
      exact ⟨α'_α, β_β'⟩
@[simp] lemma cast_fun_opt_true_iff {α β γ} :
  ((γ ⊑ (.fun α (.option β))) = true) ↔
    (∃ α' β', γ = .fun α' (.option β') ∧ (α' ⊑ α) = true ∧ (β' ⊑ β) = true) := by
  induction γ generalizing α β <;> simp [castable?]
  case «fun» τ σ τ_ih σ_ih =>
    stop
    iff_rintro h ⟨α', β', ⟨⟩, α_α', β_β'⟩
    · cases σ with
      | bool | «fun» | pair | unit | int => simp only [castable?, Bool.false_eq_true] at h
      | option σ =>
        simp only [fun_opt_cast_true_iff, SMTType.fun.injEq, SMTType.option.injEq, existsAndEq,
          and_true, exists_eq_left', reduceCtorEq, and_false, false_and, exists_const,
          or_false] at h
        use τ, σ
    · subst_eqs
      simp only [fun_opt_cast_true_iff, SMTType.fun.injEq, SMTType.option.injEq, existsAndEq,
        and_true, exists_eq_left', reduceCtorEq, and_false, false_and, exists_const, or_false]
      exact ⟨α_α', β_β'⟩

/-- Pair→Bool predicates -/
@[simp] lemma pairPred_cast_true_iff {α β γ} :
  (((.fun (.pair α β) .bool) ⊑ γ) = true) ↔
    ∃ α' β', γ = .fun (.pair α' β') .bool ∧ (α ⊑ α') = true ∧ (β ⊑ β') = true := by
  induction γ generalizing α β <;> simp [castable?]
  case «fun» τ σ τ_ih σ_ih =>
    iff_rintro h ⟨α', β', ⟨rfl, rfl⟩, α_α', β_β'⟩
    · cases σ with
      | bool =>
        obtain ⟨-, β₁, β₂, rfl, α_β₁, β_β₂⟩ := h
        use β₁, β₂
      | int | unit | «fun» | option | pair => nomatch h.1
    · exact ⟨rfl, α', β', rfl, α_α', β_β'⟩
@[simp] lemma cast_pairPred_true_iff {α β γ} :
  ((γ ⊑ (.fun (.pair α β) .bool)) = true) ↔
    (∃ α' β', γ = .fun (.pair α' β') .bool ∧ (α' ⊑ α) = true ∧ (β' ⊑ β) = true) ∨
    (∃ α' β', γ = .fun α' (.option β') ∧ (α' ⊑ α) = true ∧ (β' ⊑ β) = true) := by
  induction γ generalizing α β <;> simp [castable?]
  case «fun» τ σ τ_ih σ_ih =>
    stop
    iff_rintro h ( ⟨α', β', ⟨rfl, rfl⟩, α_α', β_β'⟩ | ⟨α', β', ⟨rfl, rfl⟩, α_α', β_β'⟩ )
    · cases σ with
      | bool =>
        simp only [true_and, reduceCtorEq, and_false, false_and, exists_const, or_false, and_true] at h ⊢
        exact h
      | «fun» | int | unit | pair => simp only [reduceCtorEq, false_and, and_false, exists_const, or_self] at h
      | option σ =>
        simp only [reduceCtorEq, false_and, SMTType.option.injEq, existsAndEq, and_true,
          exists_eq_left', false_or, and_false, exists_const] at h ⊢
        exact h
    · simp only [SMTType.pair.injEq, existsAndEq, and_true, exists_eq_left', true_and,
      reduceCtorEq, and_false, false_and, exists_const, or_false]
      exact ⟨α_α', β_β'⟩
    · simp only [reduceCtorEq, false_and, SMTType.option.injEq, existsAndEq, and_true,
      exists_eq_left', false_or]
      exact ⟨α_α', β_β'⟩

/-- A data certificate describing *how* α casts to β. -/
inductive CastPath : SMTType → SMTType → Type
| unit  : CastPath .unit .unit
| int   : CastPath .int  .int
| bool  : CastPath .bool .bool
| pair  {a₁ a₂ b₁ b₂} (p₁ : CastPath a₁ b₁) (p₂ : CastPath a₂ b₂) :
  CastPath (.pair a₁ a₂) (.pair b₁ b₂)
| option {a b} (p : CastPath a b) :
  CastPath (.option a) (.option b)

/-- Functions: domain **covariant** -/
| funBool {a a'} (p : CastPath a a')  : CastPath (.fun a .bool) (.fun a' .bool)

/-- Option-valued function widened to *another* option-valued function. -/
| funOpt_fun {a a' b b'} (pd : CastPath a a') (pc : CastPath b b') :
  CastPath (.fun a (.option b)) (.fun a' (.option b'))

/-- Option-valued function viewed as its *graph predicate* over pairs. -/
| funOpt_graph {a a' b b'} (pd : CastPath a a') (pc : CastPath b b') :
  CastPath (.fun a (.option b)) (.fun (.pair a' b') .bool)

/-- Pair→Bool predicate widened componentwise. -/
| pairPred {a a' b b'} (p₁ : CastPath a a') (p₂ : CastPath b b') :
  CastPath (.fun (.pair a b) .bool) (.fun (.pair a' b') .bool)

end ShapeForcing

open ShapeForcing

/-- Build a `CastPath α β` from a truth witness `(α ⊑ β) = true` -/
noncomputable def CastPath.of_true : ∀ α β, ((α ⊑ β) = true) → CastPath α β
| .unit,  β, h => by
    have : β = .unit := unit_cast_true_iff.mp h
    subst this; exact CastPath.unit
| .int,   β, h => by
    have : β = .int := int_cast_true_iff.mp h
    subst this; exact CastPath.int
| .bool,  β, h => by
    have : β = .bool := bool_cast_true_iff.mp h
    subst this; exact CastPath.bool
| .pair a₁ a₂, β, h => by
    -- shape forcing gives us β₁, β₂ and recursive witnesses
    choose β₁ β₂ hβ h₁ h₂ using (pair_cast_true_iff).mp h
    subst hβ
    exact CastPath.pair (CastPath.of_true a₁ β₁ h₁) (CastPath.of_true a₂ β₂ h₂)
| .option a, β, h => by
    choose β' hβ ha using (option_cast_true_iff).mp h
    subst hβ
    exact CastPath.option (CastPath.of_true a β' ha)
| .fun (.pair a b) .bool, γ, h => by
    choose a' b' hγ ha hb using (pairPred_cast_true_iff).mp h
    subst hγ
    exact CastPath.pairPred (CastPath.of_true a a' ha) (CastPath.of_true b b' hb)
| .fun a .bool, β, h => by
    choose a' ha hdom using (fun_bool_cast_true_iff).mp h
    subst ha
    exact CastPath.funBool (CastPath.of_true a a' hdom)
| .fun a (.option b), γ, h => by
    let cases := (fun_opt_cast_true_iff).mp h
    if hcases : ∃ α' β', γ = α'.fun β'.option ∧ a ⊑ α' = true ∧ b ⊑ β' = true then
      choose a' b' hγ ha hb using hcases
      subst hγ
      exact CastPath.funOpt_fun (CastPath.of_true a a' ha) (CastPath.of_true b b' hb)
    else
      choose a' b' hγ ha hb using Or.resolve_left cases hcases
      subst hγ
      exact CastPath.funOpt_graph (CastPath.of_true a a' ha) (CastPath.of_true b b' hb)


open Classical in
/-- Turn a `CastPath α β` into the semantic cast `⟦α⟧ᶻ → ⟦β⟧ᶻ` with an `IsFunc` certificate. -/
noncomputable def castZF_of_path {α β : SMTType} : CastPath α β →
  {f : ZFSet // ∃ (hf : IsFunc ⟦α⟧ᶻ ⟦β⟧ᶻ f), f.IsBijective}
| CastPath.unit  => ⟨𝟙{∅}, Id.IsFunc, Id.IsBijective⟩
| CastPath.int   => ⟨𝟙Int, Id.IsFunc, Id.IsBijective⟩
| CastPath.bool  => ⟨𝟙𝔹, Id.IsFunc, Id.IsBijective⟩

| CastPath.pair p₁ p₂ =>
  let ⟨f₁, hf₁⟩ := castZF_of_path p₁
  let f₁_bij := Classical.choose_spec hf₁
  let hf₁ := hf₁.1
  let ⟨f₂, hf₂⟩ := castZF_of_path p₂
  let f₂_bij := Classical.choose_spec hf₂
  let hf₂ := hf₂.1
  ⟨ZFSet.fprod f₁ f₂, ZFSet.fprod_is_func hf₁ hf₂, fprod_bijective_of_bijective f₁_bij f₂_bij⟩

| @CastPath.option α β p =>
  let ⟨f, hf⟩ := castZF_of_path p
  let f_bij := Classical.choose_spec hf
  let hf := hf.1
  let fopt : ZFSet :=
    λᶻ: ⟦α.option⟧ᶻ → ⟦β.option⟧ᶻ
      |     x       ↦ if hx : x ∈ ⟦α.option⟧ᶻ then
                        if is_none : x = ZFSet.Option.none (S := ⟦α⟧ᶻ).val then
                          ZFSet.Option.none (S := ⟦β⟧ᶻ).val
                        else
                          have y_def : ∃ y, x = (ZFSet.Option.some (S := ⟦α⟧ᶻ) y).val := by
                            obtain ⟨y, hy⟩ := ZFSet.Option.casesOn ⟨x, hx⟩ |>.resolve_left (by rw [Subtype.ext_iff]; exact
                              is_none)
                            rw [Subtype.ext_iff] at hy
                            use y
                          let ⟨y, hy⟩ := Classical.choose y_def
                          ZFSet.Option.some (S := ⟦β⟧ᶻ) (@ᶻf ⟨y, by rwa [ZFSet.is_func_dom_eq]⟩) |>.val
                      else ∅
  have hfopt : IsFunc ⟦α.option⟧ᶻ ⟦β.option⟧ᶻ fopt := by
    apply ZFSet.lambda_isFunc
    intro x hx
    rw [dite_cond_eq_true (eq_true hx)]
    split_ifs with is_none <;> apply SetLike.coe_mem
  have fopt_bij : fopt.IsBijective hfopt := by admit
  ⟨fopt, hfopt, fopt_bij⟩

| @CastPath.funBool α β p =>
  let ⟨f, hf⟩ := castZF_of_path p
  let f_bij := Classical.choose_spec hf
  let hf := hf.1
  let ff : ZFSet :=
    λᶻ: ⟦.fun α .bool⟧ᶻ → ⟦.fun β .bool⟧ᶻ
      |     f_α          ↦ if hf_α : IsFunc ⟦α⟧ᶻ 𝔹 f_α then
                            -- f_α : ⟦α⟧ᶻ → ⟦𝔹⟧ᶻ
                            f_α ∘ᶻ f⁻¹
                            -- build a function ⟦β⟧ᶻ → ⟦𝔹⟧ᶻ
                          else ∅
  have hff : IsFunc ⟦.fun α .bool⟧ᶻ ⟦.fun β .bool⟧ᶻ ff := by admit
  have ff_bij : ff.IsBijective hff := by admit
  ⟨ff, hff, ff_bij⟩

| @CastPath.funOpt_fun α₁ α₂ β₁ β₂ p₁ p₂ =>
  let ⟨f₁, hf₁⟩ := castZF_of_path p₁
  let f₁_bij := Classical.choose_spec hf₁
  let hf₁ := hf₁.1
  let ⟨f₂, hf₂⟩ := castZF_of_path p₂
  let f₂_bij := Classical.choose_spec hf₂
  let hf₂ := hf₂.1
  let ff : ZFSet :=
    (λᶻ : ⟦.fun α₁ (.option β₁)⟧ᶻ → ⟦.fun α₂ (.option β₂)⟧ᶻ
        |              F          ↦ if hF : IsFunc ⟦α₁⟧ᶻ ⟦.option β₁⟧ᶻ F then
                                      let F' := F ∘ᶻ f₁⁻¹ -- F' : ⟦α₂⟧ᶻ → ⟦.option β₁⟧ᶻ
                                      have hF' := IsFunc_of_composition_IsFunc hF (inv_is_func_of_bijective f₁_bij)
                                      have ⟨f₂', hf₂'⟩ := ZFSet.Option.flift f₂ hf₂
                                      f₂' ∘ᶻ F'
                                    else ∅)
  have hff : IsFunc ⟦.fun α₁ (.option β₁)⟧ᶻ ⟦.fun α₂ (.option β₂)⟧ᶻ ff := by admit
  have ff_bij : ff.IsBijective hff := by admit
  ⟨ff, hff, ff_bij⟩

| @CastPath.funOpt_graph α₁ α₂ β₁ β₂ p₁ p₂ =>
  let ⟨f₁, hf₁⟩ := castZF_of_path p₁
  let f₁_bij := Classical.choose_spec hf₁
  let hf₁ := hf₁.1
  let ⟨f₂, hf₂⟩ := castZF_of_path p₂
  let f₂_bij := Classical.choose_spec hf₂
  let hf₂ := hf₂.1
  let ff : ZFSet :=
    (λᶻ : ⟦.fun α₁ (.option β₁)⟧ᶻ → ⟦.fun (.pair α₂ β₂) .bool⟧ᶻ
        |             F           ↦ if hF : IsFunc ⟦α₁⟧ᶻ ⟦.option β₁⟧ᶻ F then
                                      F --FIXME: implement this
                                    else ∅)
  have hff : IsFunc ⟦.fun α₁ (.option β₁)⟧ᶻ ⟦.fun (.pair α₂ β₂) .bool⟧ᶻ ff := by admit
  have ff_bij : ff.IsBijective hff := by admit
  ⟨ff, hff, ff_bij⟩

| @CastPath.pairPred α₁ α₂ β₁ β₂ p₁ p₂ =>
  let ⟨f₁, hf₁⟩ := castZF_of_path p₁
  let f₁_bij := Classical.choose_spec hf₁
  let hf₁ := hf₁.1
  let ⟨f₂, hf₂⟩ := castZF_of_path p₂
  let f₂_bij := Classical.choose_spec hf₂
  let hf₂ := hf₂.1
  let ff : ZFSet :=
    (λᶻ : ⟦.fun (.pair α₁ β₁) .bool⟧ᶻ → ⟦.fun (.pair α₂ β₂) .bool⟧ᶻ
        |               F             ↦ if hF : IsFunc ⟦.pair α₁ β₁⟧ᶻ 𝔹 F then
                                          F -- FIXME: implement this
                                        else ∅)
  have hff : IsFunc ⟦.fun (.pair α₁ β₁) .bool⟧ᶻ ⟦.fun (.pair _ _) .bool⟧ᶻ ff := by admit
  have ff_bij : ff.IsBijective hff := by admit
  ⟨ff, hff, ff_bij⟩
