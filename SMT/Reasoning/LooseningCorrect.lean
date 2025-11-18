import Encoder.Loosening
import SMT.Reasoning.Defs
import Std.Tactic.Do


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
    iff_rintro h (⟨α', rfl, α_τ, β_α'⟩ | ⟨α', β', ⟨rfl, rfl⟩, α_α', β_β'⟩ )
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
        use σ
    · unfold castable?
      simp only [Bool.and_eq_true]
      exact ⟨α_τ, β_α'⟩
    · unfold castable?
      simp only [Bool.and_eq_true]
      exact ⟨α_α', β_β'⟩
@[simp] lemma cast_fun_opt_true_iff {α β γ} :
  ((γ ⊑ (.fun α (.option β))) = true) ↔
    (∃ α' β', γ = .fun α' (.option β') ∧ (α' ⊑ α) = true ∧ (β' ⊑ β) = true) := by
  induction γ generalizing α β <;> simp [castable?]
  case «fun» τ σ τ_ih σ_ih =>
    iff_rintro h ⟨α', rfl, α_τ, α'_β⟩
    · cases σ with
      | bool | «fun» | pair | unit | int => simp only [castable?, Bool.false_eq_true] at h
      | option σ =>
        simp only [fun_opt_cast_true_iff, SMTType.fun.injEq, SMTType.option.injEq, existsAndEq,
          and_true, exists_eq_left', reduceCtorEq, and_false, false_and, exists_const,
          or_false] at h
        use σ
    · simp only [fun_opt_cast_true_iff, SMTType.fun.injEq, SMTType.option.injEq, existsAndEq,
        and_true, exists_eq_left', reduceCtorEq, and_false, false_and, exists_const, or_false]
      exact ⟨α_τ, α'_β⟩

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
    iff_rintro h ( ⟨α', β', ⟨rfl, rfl⟩, α_α', β_β'⟩ | ⟨α', rfl, τ_α, α'_β⟩ )
    · cases σ with
      | bool =>
        simp only [true_and, reduceCtorEq, false_and, exists_const, or_false, and_true] at h ⊢
        exact h
      | «fun» | int | unit | pair => simp only [reduceCtorEq, false_and, exists_const, or_self] at h
      | option σ =>
        simp only [reduceCtorEq, false_and, SMTType.option.injEq,
          exists_eq_left', false_or, and_false, exists_const] at h ⊢
        exact h
    · simp only [SMTType.pair.injEq, existsAndEq, and_true, exists_eq_left', true_and,
      reduceCtorEq, false_and, exists_const, or_false]
      exact ⟨α_α', β_β'⟩
    · simp only [reduceCtorEq, false_and, SMTType.option.injEq, exists_eq_left', false_or]
      exact ⟨τ_α, α'_β⟩

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
| funBool {a a'} (p : CastPath a a') :
    CastPath (.fun a .bool) (.fun a' .bool)
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

noncomputable section CastPathToZF
open Classical

abbrev castZF_pair {α₁ β₁ α₂ β₂ : SMTType} :
  {ζ₁ // ∃ (h₁ : IsFunc ⟦α₁⟧ᶻ ⟦β₁⟧ᶻ ζ₁), ζ₁.IsBijective h₁} →
  {ζ₂ // ∃ (h₂ : IsFunc ⟦α₂⟧ᶻ ⟦β₂⟧ᶻ ζ₂), ζ₂.IsBijective h₂} →
  {f : ZFSet // ∃ (hf : IsFunc ⟦.pair α₁ α₂⟧ᶻ ⟦.pair β₁ β₂⟧ᶻ f), f.IsBijective hf} :=
  fun ⟨ζ₁, hζ₁⟩ ⟨ζ₂, hζ₂⟩ ↦
    let ζ₁_bij := Classical.choose_spec hζ₁
    let hζ₁ := hζ₁.1
    let ζ₂_bij := Classical.choose_spec hζ₂
    let hζ₂ := hζ₂.1
    let fpair := ZFSet.fprod ζ₁ ζ₂
    have hfpair : IsFunc ⟦.pair α₁ α₂⟧ᶻ ⟦.pair β₁ β₂⟧ᶻ fpair :=
      ZFSet.fprod_is_func hζ₁ hζ₂
    have fpair_bij : fpair.IsBijective hfpair :=
      fprod_bijective_of_bijective ζ₁_bij ζ₂_bij
    ⟨fpair, hfpair, fpair_bij⟩

abbrev castZF_option {α β : SMTType} :
  {ζ // ∃ (h : IsFunc ⟦α⟧ᶻ ⟦β⟧ᶻ ζ), ζ.IsBijective h} →
  {f : ZFSet // ∃ (hf : IsFunc ⟦α.option⟧ᶻ ⟦β.option⟧ᶻ f), f.IsBijective hf} := fun ⟨ζ, hζ⟩ ↦
  let ζ_bij := Classical.choose_spec hζ
  let hζ := hζ.1
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
                          ZFSet.Option.some (S := ⟦β⟧ᶻ) (@ᶻζ ⟨y, by rwa [ZFSet.is_func_dom_eq]⟩) |>.val
                      else ∅
  have hfopt : IsFunc ⟦α.option⟧ᶻ ⟦β.option⟧ᶻ fopt := by
    apply ZFSet.lambda_isFunc
    intro x hx
    rw [dite_cond_eq_true (eq_true hx)]
    split_ifs with is_none <;> apply SetLike.coe_mem
  have fopt_bij : fopt.IsBijective hfopt := by
    and_intros
    · intro x y z hx hy hz xz yz
      rw [lambda_spec] at xz yz
      rw [dite_cond_eq_true (eq_true hx)] at xz
      rw [dite_cond_eq_true (eq_true hy)] at yz
      obtain ⟨-, -, rfl⟩ := xz
      obtain ⟨-, -, eq⟩ := yz

      obtain isnone | ⟨w, issome_w⟩ := ZFSet.Option.casesOn ⟨x, hx⟩
      · rw [Subtype.ext_iff] at isnone
        obtain rfl := isnone
        rw [dite_cond_eq_true (eq_true rfl)] at eq

        split_ifs at eq with isnone'
        · exact isnone'.symm
        · simp only [SetLike.coe_eq_coe] at eq
          nomatch ZFSet.Option.some_ne_none _ eq.symm
      · rw [Subtype.ext_iff] at issome_w
        obtain rfl := issome_w
        rw [dite_cond_eq_false (eq_false (fun contr ↦ by rw [←Subtype.ext_iff] at contr; nomatch ZFSet.Option.some_ne_none _ contr))] at eq
        dsimp at eq
        split_ifs at eq with isnone'
        · rw [←Subtype.ext_iff] at eq
          nomatch ZFSet.Option.some_ne_none _ eq
        · rw [←Subtype.ext_iff] at eq
          generalize_proofs _ _ some_w'_eq _ y_eq at eq
          set w' := Classical.choose y_eq
          have hw' := Classical.choose_spec y_eq
          rw [ZFSet.Option.some.injEq] at eq
          injection @ZFSet.IsInjective.apply_inj ζ _ _ ‹_› ζ_bij.1 _ _ eq with eq
          rw [←Subtype.ext_iff] at eq
          rw [hw', ←eq]
          exact Classical.choose_spec some_w'_eq
    · intro y hy
      obtain isnone | ⟨w, hw⟩ := ZFSet.Option.casesOn ⟨y, hy⟩
      · rw [Subtype.ext_iff] at isnone
        obtain rfl := isnone
        use ZFSet.Option.none (S := ⟦α⟧ᶻ).val
        and_intros
        · simp only [SetLike.coe_mem]
        · rw [lambda_spec]
          and_intros
          · simp only [SetLike.coe_mem]
          · exact hy
          · rw [
              dite_cond_eq_true (eq_true (by simp only [SetLike.coe_mem])),
              dite_cond_eq_true (eq_true rfl)]
      · let w' := @ᶻζ⁻¹ ⟨w, by rw [is_func_dom_eq]; apply Subtype.property⟩
        use ZFSet.Option.some (S := ⟦α⟧ᶻ) w' |>.val
        and_intros
        · simp only [SetLike.coe_mem]
        · rw [lambda_spec]
          and_intros
          · simp only [SetLike.coe_mem]
          · exact hy
          · rw [
              dite_cond_eq_true (eq_true (by simp only [SetLike.coe_mem])),
              dite_cond_eq_false (eq_false (fun contr ↦ by rw [←Subtype.ext_iff] at contr; nomatch ZFSet.Option.some_ne_none _ contr))]
            dsimp
            rw [Subtype.ext_iff] at hw
            obtain rfl := hw
            rw [←Subtype.ext_iff, ZFSet.Option.some.injEq]
            have : @ᶻζ ⟨w', by rw [is_func_dom_eq]; apply Subtype.property⟩ = w := by
              unfold w'
              rw [←ZFSet.fapply_composition hζ (inv_is_func_of_bijective ζ_bij) (SetLike.coe_mem w), Subtype.ext_iff]
              conv_lhs =>
                rw [ZFSet.fapply_eq_Image_singleton
                  (IsFunc_of_composition_IsFunc hζ (inv_is_func_of_bijective ζ_bij))
                  (SetLike.coe_mem w)]
                conv =>
                  enter [1,1]
                  rw [←fcomp.eq_def ζ ζ⁻¹ hζ (inv_is_func_of_bijective ζ_bij),
                    composition_inv_self_of_bijective ζ_bij]
                rw [←fapply_eq_Image_singleton Id.IsFunc (SetLike.coe_mem w), fapply_Id (Subtype.property w)]
            rw [←this]
            congr
            generalize_proofs ex_w'
            have := choose_spec ex_w'
            rwa [←Subtype.ext_iff, ZFSet.Option.some.injEq] at this
  ⟨fopt, hfopt, fopt_bij⟩

abbrev castZF_funBool {α β : SMTType} :
  {f // ∃ (h : IsFunc ⟦α⟧ᶻ ⟦β⟧ᶻ f), f.IsBijective h} →
  {ff : ZFSet // ∃ (hff : IsFunc ⟦.fun α .bool⟧ᶻ ⟦.fun β .bool⟧ᶻ ff), ff.IsBijective hff} :=
  fun ⟨f, hf⟩ ↦
    let f_bij := Classical.choose_spec hf
    let hf := hf.1
    let ff : ZFSet :=
      λᶻ: ⟦.fun α .bool⟧ᶻ → ⟦.fun β .bool⟧ᶻ
        |     f_α          ↦ if hf_α : IsFunc ⟦α⟧ᶻ 𝔹 f_α then
                              -- f_α : ⟦α⟧ᶻ → ⟦𝔹⟧ᶻ
                              f_α ∘ᶻ f⁻¹
                              -- build a function ⟦β⟧ᶻ → ⟦𝔹⟧ᶻ
                            else ∅
      let ff : ZFSet :=
      λᶻ: ⟦.fun α .bool⟧ᶻ → ⟦.fun β .bool⟧ᶻ
        |     f_α          ↦ if hf_α : IsFunc ⟦α⟧ᶻ 𝔹 f_α then
                              -- f_α : ⟦α⟧ᶻ → ⟦𝔹⟧ᶻ
                              f_α ∘ᶻ f⁻¹
                              -- build a function ⟦β⟧ᶻ → ⟦𝔹⟧ᶻ
                            else ∅
    have hff : IsFunc ⟦.fun α .bool⟧ᶻ ⟦.fun β .bool⟧ᶻ ff := by
      apply lambda_isFunc
      intro f_α hf_α
      rw [mem_funs] at hf_α
      rw [dite_cond_eq_true (eq_true hf_α), mem_funs]
      exact IsFunc_of_composition_IsFunc hf_α (inv_is_func_of_bijective f_bij)
    have ff_bij : ff.IsBijective hff := by
      and_intros
      · intro f₁ f₂ g hf₁ hf₂ hg f₁g f₂g
        rw [mem_funs] at hf₁ hf₂
        rw [lambda_spec] at f₁g f₂g
        rw [dite_cond_eq_true (eq_true hf₁)] at f₁g
        rw [dite_cond_eq_true (eq_true hf₂)] at f₂g
        obtain ⟨-, -, rfl⟩ := f₁g
        obtain ⟨-, -, eq⟩ := f₂g

        rw [
          lambda_eta hf₁,
          lambda_eta hf₂,
          lambda_ext_iff (fun h ↦ by rw [dite_cond_eq_true (eq_true h)]; apply Subtype.property)]
        intro z hz
        iterate 2 rw [dite_cond_eq_true (eq_true hz)]
        let x := @ᶻf ⟨z, by rwa [is_func_dom_eq]⟩
        have : z = @ᶻf⁻¹ ⟨x, by rw [is_func_dom_eq]; apply Subtype.property⟩ := by
          rw [ZFSet.fapply_inv_of_bijective f_bij hz (Subtype.property _) rfl]
        conv_lhs =>
          rw [fapply_eq_Image_singleton hf₁ hz]
          conv =>
            enter [1,2,1]
            rw [this]
          rw [←fapply_eq_Image_singleton hf₁ (Subtype.property _),
            ←fapply_composition hf₁ (inv_is_func_of_bijective f_bij) (Subtype.property _),
            fapply_eq_Image_singleton (mem_funs.mp hg) (Subtype.property _)]
          conv =>
            enter [1,1]
            rw [eq]
          rw [
            ←fapply_eq_Image_singleton (IsFunc_of_composition_IsFunc hf₂ (inv_is_func_of_bijective f_bij)) (Subtype.property _),
            fapply_composition hf₂ (inv_is_func_of_bijective f_bij) (Subtype.property _),
            fapply_eq_Image_singleton hf₂ (Subtype.property _)]
          conv =>
            enter [1,2,1]
            rw [←this]
          rw [←fapply_eq_Image_singleton hf₂ hz]
      · intro y hy
        rw [mem_funs] at hy
        use y ∘ᶻ f
        and_intros
        · rw [mem_funs]
          exact IsFunc_of_composition_IsFunc hy hf
        · rw [lambda_spec]
          and_intros
          · rw [mem_funs]
            exact IsFunc_of_composition_IsFunc hy hf
          · rwa [mem_funs]
          · rw [dite_cond_eq_true (eq_true (IsFunc_of_composition_IsFunc hy hf)),
              ←fcomp_assoc]
            conv_lhs =>
              rw [←ZFSet.Id.composition_right hy.1, ←fcomp.eq_def _ _ hy Id.IsFunc]
            congr
            rw [composition_inv_self_of_bijective f_bij]
    ⟨ff, hff, ff_bij⟩

abbrev castZF_funOpt {α₁ α₂ β₁ β₂ : SMTType} :
  {ζ₁ // ∃ (h₁ : IsFunc ⟦α₁⟧ᶻ ⟦α₂⟧ᶻ ζ₁), ζ₁.IsBijective h₁} →
  {ζ₂ // ∃ (h₂ : IsFunc ⟦β₁⟧ᶻ ⟦β₂⟧ᶻ ζ₂), ζ₂.IsBijective h₂} →
  {ff : ZFSet //
    ∃ (hff : IsFunc ⟦.fun α₁ (.option β₁)⟧ᶻ ⟦.fun α₂ (.option β₂)⟧ᶻ ff), ff.IsBijective hff} :=
  fun ⟨ζ₁, hζ₁⟩ ⟨ζ₂, hζ₂⟩ ↦
    let ζ₁_bij := Classical.choose_spec hζ₁
    let hζ₁ := hζ₁.1
    let ζ₂_bij := Classical.choose_spec hζ₂
    let hζ₂ := hζ₂.1
    let ζ₂' := ZFSet.Option.flift ζ₂ hζ₂
    let ff : ZFSet :=
      (λᶻ : ⟦.fun α₁ (.option β₁)⟧ᶻ → ⟦.fun α₂ (.option β₂)⟧ᶻ
          |              F          ↦ if hF : IsFunc ⟦α₁⟧ᶻ ⟦.option β₁⟧ᶻ F then
                                        fcomp ζ₂'.val (F ∘ᶻ ζ₁⁻¹) ζ₂'.property
                                      else ∅)
    have hff : IsFunc ⟦.fun α₁ (.option β₁)⟧ᶻ ⟦.fun α₂ (.option β₂)⟧ᶻ ff := by
      apply lambda_isFunc
      intro F hF
      rw [mem_funs] at hF
      rw [dite_cond_eq_true (eq_true hF), mem_funs]
      refine IsFunc_of_composition_IsFunc (Subtype.property _) (IsFunc_of_composition_IsFunc hF (inv_is_func_of_bijective ζ₁_bij))
    have ff_bij : ff.IsBijective hff := by
      and_intros
      · intro x y z hx hy hz xz yz
        rw [mem_funs] at hx hy hz
        rw [lambda_spec] at xz yz
        rw [dite_cond_eq_true (eq_true hx)] at xz
        rw [dite_cond_eq_true (eq_true hy)] at yz
        obtain ⟨-, -, rfl⟩ := xz
        obtain ⟨-, -, eq⟩ := yz
        rwa [
          fcomp_bij_left_cancel_iff (by rwa [ZFSet.Option.flift_bijective]),fcomp_bij_right_cancel_iff (inv_bijective_of_bijective ζ₁_bij)] at eq
      · intro y hy
        rw [mem_funs] at hy
        let F := fcomp (inv ζ₂'.1 (is_rel_of_is_func ζ₂'.property)) (y ∘ᶻ ζ₁)
          (inv_is_func_of_bijective (by rwa [ZFSet.Option.flift_bijective]))
        have hF : F ∈ ⟦α₁.fun β₁.option⟧ᶻ := by
          rw [mem_funs]
          exact IsFunc_of_composition_IsFunc (inv_is_func_of_bijective (by rwa [ZFSet.Option.flift_bijective])) (IsFunc_of_composition_IsFunc hy hζ₁)
        use F
        and_intros
        · exact hF
        · rw [lambda_spec]
          and_intros
          · exact hF
          · rwa [mem_funs]
          · rw [mem_funs] at hF
            rw [dite_cond_eq_true (eq_true hF)]
            unfold F
            conv_rhs =>
              enter [2]
              rw [←fcomp_assoc]
              conv =>
                enter [2]
                rw [←fcomp_assoc]
                conv =>
                  enter [2]
                  rw [composition_inv_self_of_bijective ζ₁_bij]
                rw [fcomp, Id.composition_right (is_rel_of_is_func hy)]
            rw [fcomp_assoc]
            conv =>
              enter [2]
              conv =>
                enter [1]
                rw [composition_inv_self_of_bijective ((Option.flift_bijective hζ₂).mpr ζ₂_bij)]
              rw [fcomp, Id.composition_left (is_rel_of_is_func hy)]
    ⟨ff, hff, ff_bij⟩

def castZF_funOpt_graph_aux {α₁ β₁ α₂ β₂ : SMTType} {ζ₁ ζ₂ : ZFSet}
  {hζ₁ : IsFunc ⟦α₁⟧ᶻ ⟦α₂⟧ᶻ ζ₁} (ζ₁_bij : ζ₁.IsBijective hζ₁)
  {hζ₂ : IsFunc ⟦β₁⟧ᶻ ⟦β₂⟧ᶻ ζ₂} (ζ₂_bij : ζ₂.IsBijective hζ₂)
    : ZFSet :=
  λᶻ : ⟦.fun α₁ (.option β₁)⟧ᶻ → ⟦.fun (.pair α₂ β₂) .bool⟧ᶻ
          |             F           ↦ if hF : IsFunc ⟦α₁⟧ᶻ ⟦.option β₁⟧ᶻ F then
                                        let R : ZFSet :=
                                          ⟦.pair α₂ β₂⟧ᶻ.prod .𝔹 |>.sep fun xyz ↦
                                            if hxyz : xyz ∈ ⟦.pair α₂ β₂⟧ᶻ.prod .𝔹 then
                                              let x := fapply ζ₁⁻¹ (is_func_is_pfunc (inv_is_func_of_bijective ζ₁_bij)) ⟨xyz.π₁.π₁, by
                                                rw [is_func_dom_eq]
                                                rw [pair_eta hxyz, pair_mem_prod, pair_eta hxyz.1, pair_mem_prod] at hxyz
                                                exact hxyz.1.1⟩
                                              let Fx := fapply F (is_func_is_pfunc hF) ⟨x, by
                                                rw [is_func_dom_eq]
                                                apply Subtype.property⟩
                                              let y := fapply ζ₂⁻¹ (is_func_is_pfunc (inv_is_func_of_bijective ζ₂_bij)) ⟨xyz.π₁.π₂, by
                                                rw [is_func_dom_eq]
                                                rw [pair_eta hxyz, pair_mem_prod, pair_eta hxyz.1, pair_mem_prod] at hxyz
                                                exact hxyz.1.2⟩
                                              let b : ZFBool := ⟨xyz.π₂, by
                                                rw [pair_eta hxyz, pair_mem_prod] at hxyz
                                                exact hxyz.2⟩
                                              (Fx = (ZFSet.Option.some (S := ⟦β₁⟧ᶻ) y).val) ↔ (b.toBool = true)
                                            else False
                                        R
                                      else ∅

theorem castZF_funOpt_graph_aux_is_func {α₁ β₁ α₂ β₂ : SMTType} {ζ₁ ζ₂ : ZFSet}
  {hζ₁ : IsFunc ⟦α₁⟧ᶻ ⟦α₂⟧ᶻ ζ₁} (ζ₁_bij : ζ₁.IsBijective hζ₁)
  {hζ₂ : IsFunc ⟦β₁⟧ᶻ ⟦β₂⟧ᶻ ζ₂} (ζ₂_bij : ζ₂.IsBijective hζ₂) :
    IsFunc ⟦.fun α₁ (.option β₁)⟧ᶻ ⟦.fun (.pair α₂ β₂) .bool⟧ᶻ
      (castZF_funOpt_graph_aux ζ₁_bij ζ₂_bij) := by
  apply lambda_isFunc
  intro F hF
  rw [mem_funs] at hF
  rw [dite_cond_eq_true (eq_true hF), mem_funs]
  extract_lets R
  and_intros
  · intro _ hz
    exact ZFSet.sep_subset_self hz
  · intro z hz
    rw [mem_prod] at hz
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    let w : Bool := -- F(ζ₁⁻¹ x) = some (ζ₂⁻¹ y)
      fapply F (is_func_is_pfunc hF)
        ⟨fapply (ζ₁⁻¹) (is_func_is_pfunc (inv_is_func_of_bijective ζ₁_bij))
          ⟨x, by rwa [is_func_dom_eq]⟩,
            by rw [is_func_dom_eq]; apply Subtype.property⟩ =
      (ZFSet.Option.some (S := ⟦β₁⟧ᶻ)
        (fapply (ζ₂⁻¹) (is_func_is_pfunc (inv_is_func_of_bijective ζ₂_bij))
          ⟨y, by rwa [is_func_dom_eq]⟩)).val
    use ZFBool.ofBool w
    and_intros
    · beta_reduce
      rw [mem_sep]
      simp only [mem_prod, pair_inj, ↓existsAndEq, and_true, π₁_pair, π₂_pair, SetLike.coe_eq_coe, Subtype.coe_eta, dite_else_false, and_exists_self]
      use ⟨⟨hx, hy⟩, ZFBool.mem_ofBool_𝔹 w⟩
      rw [ZFBool.to_Bool_ofBool]
      conv_rhs =>
        unfold w
        rw [decide_eq_true_iff, ←Subtype.ext_iff]
    · intro b hb
      rw [mem_sep] at hb
      simp only [mem_prod, pair_inj, ↓existsAndEq, and_true, π₁_pair, π₂_pair, SetLike.coe_eq_coe, dite_else_false, and_exists_self] at hb
      obtain ⟨⟨_, hb⟩, eq⟩ := hb
      rw [←Subtype.ext_iff (p := (· ∈ ZFSet.𝔹)) (a1 := ⟨b, hb⟩)]
      cases h : w <;> subst w
      · rw [decide_eq_false_iff_not, ←Subtype.ext_iff] at h
        rw [iff_false_left h, Bool.not_eq_true] at eq
        rw [←ZFBool.of_Bool_toBool ⟨b, hb⟩]
        congr
      · rw [decide_eq_true_iff, ←Subtype.ext_iff] at h
        rw [iff_true_left h] at eq
        rw [←ZFBool.of_Bool_toBool ⟨b, hb⟩]
        congr

theorem castZF_funOpt_graph_aux_is_bij {α₁ β₁ α₂ β₂ : SMTType} {ζ₁ ζ₂ : ZFSet}
  {hζ₁ : IsFunc ⟦α₁⟧ᶻ ⟦α₂⟧ᶻ ζ₁} (ζ₁_bij : ζ₁.IsBijective hζ₁)
  {hζ₂ : IsFunc ⟦β₁⟧ᶻ ⟦β₂⟧ᶻ ζ₂} (ζ₂_bij : ζ₂.IsBijective hζ₂) :
    (castZF_funOpt_graph_aux ζ₁_bij ζ₂_bij).IsBijective
      (castZF_funOpt_graph_aux_is_func ζ₁_bij ζ₂_bij) := by
  and_intros
  · intro f g R hf hg hR fR gR
    rw [mem_funs] at hf hg hR
    rw [castZF_funOpt_graph_aux, lambda_spec] at fR gR
    rw [dite_cond_eq_true (eq_true hf)] at fR
    rw [dite_cond_eq_true (eq_true hg)] at gR
    obtain ⟨-, -, rfl⟩ := fR
    obtain ⟨-, -, eq⟩ := gR
    rw [
      lambda_eta hf,
      lambda_eta hg,
      lambda_ext_iff (fun h ↦ by rw [dite_cond_eq_true (eq_true h)]; apply Subtype.property)]
    intro z hz
    iterate 2 rw [dite_cond_eq_true (eq_true hz)]
    rw [←Subtype.ext_iff]
    rw [ZFSet.ext_iff] at eq
    simp only [mem_sep, mem_prod, ↓existsAndEq, and_true, SetLike.coe_eq_coe,
      dite_else_false, and_exists_self] at eq
    obtain isnone | ⟨fz, issome_fz⟩ := ZFSet.Option.casesOn (@ᶻf ⟨z, by rwa [is_func_dom_eq]⟩)
    · rw [isnone]
      by_contra! contr
      have ⟨⟨y, hy⟩, issome⟩ := ZFSet.Option.ne_none_is_some _ contr.symm

      obtain ⟨x, hx, hxy⟩ := (inv_bijective_of_bijective ζ₂_bij).2 y hy
      have y_def := fapply.of_pair (is_func_is_pfunc (inv_is_func_of_bijective ζ₂_bij)) hxy
      rw [Subtype.ext_iff, eq_comm] at y_def
      dsimp at y_def
      conv at issome =>
        enter [2,1,1]
        rw [y_def]
      specialize eq (((@ᶻζ₁ ⟨z, by rwa [is_func_dom_eq]⟩).val.pair x).pair zftrue)
      simp only [π₁_pair, π₂_pair, pair_inj, ↓existsAndEq, and_true, SetLike.coe_mem, hx, ZFBool.zftrue_mem_𝔹, exists_true_left, ZFBool.toBool, dite_true, iff_true] at eq

      iterate 2 rw [Subtype.ext_iff] at eq
      conv_lhs at eq =>
        enter [1]
        rw [
          ←fapply_composition hf (inv_is_func_of_bijective ζ₁_bij) (Subtype.property _),
          ←fapply_composition
            (IsFunc_of_composition_IsFunc hf (inv_is_func_of_bijective ζ₁_bij)) hζ₁ hz,
          fapply_eq_Image_singleton
            (IsFunc_of_composition_IsFunc
              (IsFunc_of_composition_IsFunc hf (inv_is_func_of_bijective ζ₁_bij)) hζ₁) hz]
        conv =>
          enter [1,1]
          change f ∘ᶻ ζ₁⁻¹ ∘ᶻ ζ₁
          rw [←fcomp_assoc]
          conv =>
            enter [2]
            rw [composition_self_inv_of_bijective ζ₁_bij]
          rw [fcomp, Id.composition_right (is_rel_of_is_func hf)]
        rw [←fapply_eq_Image_singleton hf hz]
      conv_rhs at eq =>
        enter [1]
        rw [
          ←fapply_composition hg (inv_is_func_of_bijective ζ₁_bij) (Subtype.property _),
          ←fapply_composition
            (IsFunc_of_composition_IsFunc hg (inv_is_func_of_bijective ζ₁_bij)) hζ₁ hz,
          fapply_eq_Image_singleton
            (IsFunc_of_composition_IsFunc
              (IsFunc_of_composition_IsFunc hg (inv_is_func_of_bijective ζ₁_bij)) hζ₁) hz]
        conv =>
          enter [1,1]
          change g ∘ᶻ ζ₁⁻¹ ∘ᶻ ζ₁
          rw [←fcomp_assoc]
          conv =>
            enter [2]
            rw [composition_self_inv_of_bijective ζ₁_bij]
          rw [fcomp, Id.composition_right (is_rel_of_is_func hg)]
        rw [←fapply_eq_Image_singleton hg hz]
      conv_lhs at eq => rw [←Subtype.ext_iff, isnone]
      conv_rhs at eq => rw [←Subtype.ext_iff, issome, ZFSet.Option.some.injEq]
      simp only [Subtype.coe_eta, iff_true] at eq
      nomatch ZFSet.Option.some_ne_none _ eq.symm
    · obtain ⟨fz, hfz⟩ := fz
      obtain ⟨y, hy, hyfz⟩ := inv_bijective_of_bijective ζ₂_bij |>.2 fz hfz
      have y_def := fapply.of_pair (is_func_is_pfunc (inv_is_func_of_bijective ζ₂_bij)) hyfz
      rw [Subtype.ext_iff, eq_comm] at y_def
      dsimp at y_def
      conv at issome_fz =>
        enter [2,1,1]
        rw [y_def]
      specialize eq (((@ᶻζ₁ ⟨z, by rwa [is_func_dom_eq]⟩).val.pair y).pair zftrue)
      simp only [π₁_pair, π₂_pair, pair_inj, ↓existsAndEq, and_true, SetLike.coe_mem, hy, ZFBool.zftrue_mem_𝔹, exists_true_left, ZFBool.toBool, dite_true, iff_true] at eq
      iterate 2 rw [Subtype.ext_iff] at eq
      conv_lhs at eq =>
        enter [1]
        rw [
          ←fapply_composition hf (inv_is_func_of_bijective ζ₁_bij) (Subtype.property _),
          ←fapply_composition
            (IsFunc_of_composition_IsFunc hf (inv_is_func_of_bijective ζ₁_bij)) hζ₁ hz,
          fapply_eq_Image_singleton
            (IsFunc_of_composition_IsFunc
              (IsFunc_of_composition_IsFunc hf (inv_is_func_of_bijective ζ₁_bij)) hζ₁) hz]
        conv =>
          enter [1,1]
          change f ∘ᶻ ζ₁⁻¹ ∘ᶻ ζ₁
          rw [←fcomp_assoc]
          conv =>
            enter [2]
            rw [composition_self_inv_of_bijective ζ₁_bij]
          rw [fcomp, Id.composition_right (is_rel_of_is_func hf)]
        rw [←fapply_eq_Image_singleton hf hz]
      conv_rhs at eq =>
        enter [1]
        rw [
          ←fapply_composition hg (inv_is_func_of_bijective ζ₁_bij) (Subtype.property _),
          ←fapply_composition
            (IsFunc_of_composition_IsFunc hg (inv_is_func_of_bijective ζ₁_bij)) hζ₁ hz,
          fapply_eq_Image_singleton
            (IsFunc_of_composition_IsFunc
              (IsFunc_of_composition_IsFunc hg (inv_is_func_of_bijective ζ₁_bij)) hζ₁) hz]
        conv =>
          enter [1,1]
          change g ∘ᶻ ζ₁⁻¹ ∘ᶻ ζ₁
          rw [←fcomp_assoc]
          conv =>
            enter [2]
            rw [composition_self_inv_of_bijective ζ₁_bij]
          rw [fcomp, Id.composition_right (is_rel_of_is_func hg)]
        rw [←fapply_eq_Image_singleton hg hz]
      conv_lhs at eq => rw [←Subtype.ext_iff, issome_fz, ZFSet.Option.some.injEq]
      conv_rhs at eq => rw [←Subtype.ext_iff]
      simp only [Subtype.coe_eta, true_iff] at eq
      rw [eq, issome_fz]
  · intro R hR
    unfold castZF_funOpt_graph_aux
    simp only [mem_funs, mem_prod, ↓existsAndEq, and_true, SetLike.coe_eq_coe, dite_else_false,
      lambda_spec, and_self_left]

abbrev castZF_funOpt_graph {α₁ α₂ β₁ β₂ : SMTType} :
  {ζ₁ // ∃ (h₁ : IsFunc ⟦α₁⟧ᶻ ⟦α₂⟧ᶻ ζ₁), ζ₁.IsBijective h₁} →
  {ζ₂ // ∃ (h₂ : IsFunc ⟦β₁⟧ᶻ ⟦β₂⟧ᶻ ζ₂), ζ₂.IsBijective h₂} →
  {ff : ZFSet //
    ∃ (hff : IsFunc ⟦.fun α₁ (.option β₁)⟧ᶻ ⟦.fun (.pair α₂ β₂) .bool⟧ᶻ ff), ff.IsBijective hff} :=
  fun ⟨_, hζ₁⟩ ⟨_, hζ₂⟩ ↦
    let ζ₁_bij := Classical.choose_spec hζ₁
    let ζ₂_bij := Classical.choose_spec hζ₂
    ⟨
      castZF_funOpt_graph_aux ζ₁_bij ζ₂_bij,
      castZF_funOpt_graph_aux_is_func ζ₁_bij ζ₂_bij,
      castZF_funOpt_graph_aux_is_bij ζ₁_bij ζ₂_bij⟩

-- abbrev castZF_pairPred {α₁ α₂ β₁ β₂ : SMTType} :
--   {ζ₁ // ∃ (h₁ : IsFunc ⟦α₁⟧ᶻ ⟦α₂⟧ᶻ ζ₁), ζ₁.IsBijective h₁} →
--   {ζ₂ // ∃ (h₂ : IsFunc ⟦β₁⟧ᶻ ⟦β₂⟧ᶻ ζ₂), ζ₂.IsBijective h₂} →
--   {ff : ZFSet //
--     ∃ (hff : IsFunc ⟦.fun (.pair α₁ β₁) .bool⟧ᶻ ⟦.fun (.pair α₂ β₂) .bool⟧ᶻ ff), ff.IsBijective hff} :=
--   fun ⟨ζ₁, hζ₁⟩ ⟨ζ₂, hζ₂⟩ ↦
--     let ζ₁_bij := Classical.choose_spec hζ₁
--     let hζ₁ := hζ₁.1
--     let ζ₂_bij := Classical.choose_spec hζ₂
--     let hζ₂ := hζ₂.1
--     let ff : ZFSet :=
--       (λᶻ : ⟦.fun (.pair α₁ β₁) .bool⟧ᶻ → ⟦.fun (.pair α₂ β₂) .bool⟧ᶻ
--           | F ↦ if hF : IsFunc ⟦.pair α₁ β₁⟧ᶻ 𝔹 F then
--                   let R :=
--                     λᶻ: ⟦α₂.pair β₂⟧ᶻ → .𝔹
--                       |       xy      ↦ if hxy : xy ∈ ⟦.pair α₂ β₂⟧ᶻ then
--                                           let x := fapply ζ₁⁻¹ (is_func_is_pfunc (inv_is_func_of_bijective ζ₁_bij)) ⟨xy.π₁, by
--                                             rw [is_func_dom_eq]
--                                             rw [pair_eta hxy, pair_mem_prod] at hxy
--                                             exact hxy.1⟩
--                                           let y := fapply ζ₂⁻¹ (is_func_is_pfunc (inv_is_func_of_bijective ζ₂_bij)) ⟨xy.π₂, by
--                                             rw [is_func_dom_eq]
--                                             rw [pair_eta hxy, pair_mem_prod] at hxy
--                                             exact hxy.2⟩
--                                           fapply F (is_func_is_pfunc hF) ⟨.pair x y, by
--                                             rw [is_func_dom_eq, SMTType.toZFSet, pair_mem_prod]
--                                             and_intros <;> apply Subtype.property⟩
--                                         else ∅
--                   R
--                 else ∅)
--     have hff : IsFunc ⟦.fun (.pair α₁ β₁) .bool⟧ᶻ ⟦.fun (.pair _ _) .bool⟧ᶻ ff := by admit
--     have ff_bij : ff.IsBijective hff := by admit
--     ⟨ff, hff, ff_bij⟩

end CastPathToZF

-- open Classical in
-- /-- Turn a `CastPath α β` into the semantic cast `⟦α⟧ᶻ → ⟦β⟧ᶻ` with an `IsFunc` certificate. -/
-- noncomputable def castZF_of_path {α β : SMTType} : CastPath α β →
--   {f : ZFSet // ∃ (hf : IsFunc ⟦α⟧ᶻ ⟦β⟧ᶻ f), f.IsBijective}
-- | CastPath.unit               => ⟨𝟙{∅}, Id.IsFunc, Id.IsBijective⟩
-- | CastPath.int                => ⟨𝟙Int, Id.IsFunc, Id.IsBijective⟩
-- | CastPath.bool               => ⟨𝟙𝔹, Id.IsFunc, Id.IsBijective⟩
-- | CastPath.pair p₁ p₂         => castZF_pair (castZF_of_path p₁) (castZF_of_path p₂)
-- | CastPath.option p           => castZF_option (castZF_of_path p)
-- | CastPath.funBool p          => castZF_funBool (castZF_of_path p)
-- | CastPath.funOpt_fun p₁ p₂   => castZF_funOpt (castZF_of_path p₁) (castZF_of_path p₂)
-- | CastPath.funOpt_graph p₁ p₂ => castZF_funOpt_graph (castZF_of_path p₁) (castZF_of_path p₂)
-- | CastPath.pairPred p₁ p₂     => castZF_pairPred (castZF_of_path p₁) (castZF_of_path p₂)


-- open Classical in
-- noncomputable def castZF.{u} (α β : SMTType) (cast? : α ⊑ β) : {f : ZFSet.{u} // ∃ (hf : ⟦α⟧ᶻ.IsFunc ⟦β⟧ᶻ f), f.IsBijective hf} :=
--   castZF_of_path <| CastPath.of_true α β cast?

-- -- denx! = (castZF α β cast?) @ᶻdenx ??
