import Encoder.Loosening
import SMT.Reasoning.Defs
import SMT.Reasoning.Lemmas

set_option linter.style.nameCheck false

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

/-- Pair → Bool predicates -/
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

/-- A data certificate describing *how* `α` casts to `β`. -/
inductive CastPath : SMTType → SMTType → Type
| unit  : CastPath .unit .unit
| int   : CastPath .int  .int
| bool  : CastPath .bool .bool
| pair {a₁ a₂ b₁ b₂} (p₁ : CastPath a₁ b₁) (p₂ : CastPath a₂ b₂) :
  CastPath (.pair a₁ a₂) (.pair b₁ b₂)
| option {a b} (p : CastPath a b) :
  CastPath (.option a) (.option b)
| funBool {a a'} (p : CastPath a a') :
    CastPath (.fun a .bool) (.fun a' .bool)
| funOpt_fun {a a' b b'} (pd : CastPath a a') (pc : CastPath b b') :
    CastPath (.fun a (.option b)) (.fun a' (.option b'))
| funOpt_graph {a a' b b'} (pd : CastPath a a') (pc : CastPath b b') :
    CastPath (.fun a (.option b)) (.fun (.pair a' b') .bool)
| pairPred {a a' b b'} (p₁ : CastPath a a') (p₂ : CastPath b b') :
    CastPath (.fun (.pair a b) .bool) (.fun (.pair a' b') .bool)
  deriving BEq, DecidableEq

end ShapeForcing

open ShapeForcing

/-- Build a `CastPath α β` from a truth witness `(α ⊑ β) = true` -/
noncomputable def CastPath.of_true (α β : SMTType) (h : (α ⊑ β) = true) :
    CastPath α β :=
  match hα : α with
  | .unit => by
      subst hα
      have : β = .unit := unit_cast_true_iff.mp h
      exact this ▸ CastPath.unit
  | .int => by
      subst hα
      have : β = .int := int_cast_true_iff.mp h
      exact this ▸ CastPath.int
  | .bool => by
      subst hα
      have : β = .bool := bool_cast_true_iff.mp h
      exact this ▸ CastPath.bool
  | .pair a₁ a₂ => by
      subst hα
      -- shape forcing gives us β₁, β₂ and recursive witnesses
      choose β₁ β₂ hβ h₁ h₂ using (pair_cast_true_iff).mp h
      subst hβ
      exact CastPath.pair (CastPath.of_true a₁ β₁ h₁) (CastPath.of_true a₂ β₂ h₂)
  | .option a => by
      subst hα
      choose β' hβ ha using (option_cast_true_iff).mp h
      subst hβ
      exact CastPath.option (CastPath.of_true a β' ha)
  | .fun (.pair a b) .bool => by
      subst hα
      choose a' b' hγ ha hb using (pairPred_cast_true_iff).mp h
      subst hγ
      exact CastPath.pairPred (CastPath.of_true a a' ha) (CastPath.of_true b b' hb)
  | .fun a .bool => by
      subst hα
      choose a' ha hdom using (fun_bool_cast_true_iff).mp h
      subst ha
      exact CastPath.funBool (CastPath.of_true a a' hdom)
  | .fun a (.option b) => by
      subst hα
      let cases := (fun_opt_cast_true_iff).mp h
      if hcases : ∃ α' β', β = α'.fun β'.option ∧ a ⊑ α' = true ∧ b ⊑ β' = true then
        choose a' b' hγ ha hb using hcases
        subst hγ
        exact CastPath.funOpt_fun (CastPath.of_true a a' ha) (CastPath.of_true b b' hb)
      else
        choose a' b' hγ ha hb using Or.resolve_left cases hcases
        subst hγ
        exact CastPath.funOpt_graph (CastPath.of_true a a' ha) (CastPath.of_true b b' hb)
  | SMTType.fun (SMTType.pair _ _) (SMTType.pair _ _)
  | SMTType.fun (SMTType.pair _ _) (SMTType.fun _ _)
  | SMTType.fun (SMTType.pair _ _) SMTType.unit
  | SMTType.fun (SMTType.pair _ _) SMTType.int
  | SMTType.fun (SMTType.option _) (SMTType.pair _ _)
  | SMTType.fun (SMTType.option _) (SMTType.fun _ _)
  | SMTType.fun (SMTType.option _) SMTType.unit
  | SMTType.fun (SMTType.option _) SMTType.int
  | SMTType.fun (SMTType.fun _ _) (SMTType.pair _ _)
  | SMTType.fun (SMTType.fun _ _) (SMTType.fun _ _)
  | SMTType.fun (SMTType.fun _ _) SMTType.unit
  | SMTType.fun (SMTType.fun _ _) SMTType.int
  | SMTType.fun SMTType.unit (SMTType.pair _ _)
  | SMTType.fun SMTType.unit (SMTType.fun _ _)
  | SMTType.fun SMTType.unit SMTType.unit
  | SMTType.fun SMTType.unit SMTType.int
  | SMTType.fun SMTType.int (SMTType.pair _ _)
  | SMTType.fun SMTType.int (SMTType.fun _ _)
  | SMTType.fun SMTType.int SMTType.unit
  | SMTType.fun SMTType.int SMTType.int
  | SMTType.fun SMTType.bool (SMTType.pair _ _)
  | SMTType.fun SMTType.bool (SMTType.fun _ _)
  | SMTType.fun SMTType.bool SMTType.unit
  | SMTType.fun SMTType.bool SMTType.int => by
    subst hα
    simp only [castable?, Bool.false_eq_true] at h

noncomputable section CastPathToZF
open Classical

abbrev castZF_pair {α₁ β₁ α₂ β₂ : SMTType} :
  {ζ₁ // IsFunc ⟦α₁⟧ᶻ ⟦β₁⟧ᶻ ζ₁} →
  {ζ₂ // IsFunc ⟦α₂⟧ᶻ ⟦β₂⟧ᶻ ζ₂} →
  {f : ZFSet // IsFunc ⟦.pair α₁ α₂⟧ᶻ ⟦.pair β₁ β₂⟧ᶻ f} :=
  fun ⟨ζ₁, hζ₁⟩ ⟨ζ₂, hζ₂⟩ ↦ ⟨fprod ζ₁ ζ₂, ZFSet.fprod_is_func hζ₁ hζ₂⟩

abbrev castZF_option {α β : SMTType} :
  {ζ // IsFunc ⟦α⟧ᶻ ⟦β⟧ᶻ ζ} →
  {f : ZFSet // IsFunc ⟦α.option⟧ᶻ ⟦β.option⟧ᶻ f} := fun ⟨ζ, hζ⟩ ↦
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
  ⟨fopt, hfopt⟩

abbrev castZF_funBool {α β : SMTType} :
  {f // IsFunc ⟦α⟧ᶻ ⟦β⟧ᶻ f} →
  {ff : ZFSet // IsFunc ⟦.fun α .bool⟧ᶻ ⟦.fun β .bool⟧ᶻ ff} :=
  fun ⟨cast, hcast⟩ ↦
    let ff : ZFSet :=
      λᶻ: ⟦.fun α .bool⟧ᶻ → ⟦.fun β .bool⟧ᶻ
        |     f_α          ↦ if hf_α : IsFunc ⟦α⟧ᶻ 𝔹 f_α then
                              λᶻ: ⟦β⟧ᶻ → .𝔹
                                |   y  ↦ if y_ran : y ∈ cast.Range then
                                            let x := choose (mem_sep.mp y_ran).2
                                            have hx : x ∈ ⟦α⟧ᶻ := by
                                              have ⟨dom, _⟩ := choose_spec (mem_sep.mp y_ran).2
                                              conv at dom =>
                                                enter [1]
                                                rw [is_func_dom_eq]
                                              exact dom
                                            @ᶻf_α ⟨x, by rwa [is_func_dom_eq]⟩
                                          else zffalse
                            else ∅
    have hff : IsFunc ⟦.fun α .bool⟧ᶻ ⟦.fun β .bool⟧ᶻ ff := by
      apply lambda_isFunc
      intro f_α hf_α
      rw [mem_funs] at hf_α
      rw [dite_cond_eq_true (eq_true hf_α), mem_funs]
      apply lambda_isFunc
      intro y hy
      split_ifs with y_ran
      · apply SetLike.coe_mem
      · exact ZFBool.zffalse_mem_𝔹
    ⟨ff, hff⟩

abbrev castZF_funOpt {α₁ α₂ β₁ β₂ : SMTType} :
  {ζ₁ // IsFunc ⟦α₁⟧ᶻ ⟦α₂⟧ᶻ ζ₁} →
  {ζ₂ // IsFunc ⟦β₁⟧ᶻ ⟦β₂⟧ᶻ ζ₂} →
  {ff : ZFSet // IsFunc ⟦.fun α₁ (.option β₁)⟧ᶻ ⟦.fun α₂ (.option β₂)⟧ᶻ ff} :=
  fun ⟨ζ₁, hζ₁⟩ ⟨ζ₂, hζ₂⟩ ↦
    let ⟨ζ₂', hζ₂'⟩ := ZFSet.Option.flift ζ₂ hζ₂
    let ff : ZFSet :=
      (λᶻ : ⟦.fun α₁ (.option β₁)⟧ᶻ → ⟦.fun α₂ (.option β₂)⟧ᶻ
          |              F          ↦ if hF : IsFunc ⟦α₁⟧ᶻ ⟦.option β₁⟧ᶻ F then
                                        -- ζ₂' ∘ᶻ (F ∘ᶻ ζ₁⁻¹)
                                        λᶻ: ⟦α₂⟧ᶻ → ⟦.option β₂⟧ᶻ
                                          |   x   ↦ if hx : x ∈ ζ₁.Range then
                                                      let x' := choose (mem_sep.mp hx).2
                                                      have hx' : x' ∈ ⟦α₁⟧ᶻ := by
                                                        have ⟨dom, _⟩ := choose_spec (mem_sep.mp hx).2
                                                        conv at dom =>
                                                          enter [1]
                                                          rw [is_func_dom_eq]
                                                        exact dom
                                                      let y := fapply F (is_func_is_pfunc hF) ⟨x', by rwa [is_func_dom_eq]⟩
                                                      @ᶻζ₂' ⟨y, by rw [is_func_dom_eq]; apply Subtype.property⟩
                                                    else ZFSet.Option.none (S := ⟦β₂⟧ᶻ).val
                                      else ∅)
    have hff : IsFunc ⟦.fun α₁ (.option β₁)⟧ᶻ ⟦.fun α₂ (.option β₂)⟧ᶻ ff := by
      apply lambda_isFunc
      intro F hF
      rw [mem_funs] at hF
      rw [dite_cond_eq_true (eq_true hF), mem_funs]
      apply lambda_isFunc
      intro y hy
      split_ifs with hy_range <;> apply SetLike.coe_mem
    ⟨ff, hff⟩

abbrev castZF_funOpt_graph {α₁ α₂ β₁ β₂ : SMTType} :
  {ζ₁ // IsFunc ⟦α₁⟧ᶻ ⟦α₂⟧ᶻ ζ₁} →
  {ζ₂ // IsFunc ⟦β₁⟧ᶻ ⟦β₂⟧ᶻ ζ₂} →
  {ff : ZFSet // IsFunc ⟦.fun α₁ (.option β₁)⟧ᶻ ⟦.fun (.pair α₂ β₂) .bool⟧ᶻ ff} :=
  fun ⟨ζ₁, hζ₁⟩ ⟨ζ₂, hζ₂⟩ ↦
    let R :=
      λᶻ: ⟦.fun α₁ (.option β₁)⟧ᶻ → ⟦.fun (.pair α₂ β₂) .bool⟧ᶻ
        | F ↦ if hF : IsFunc ⟦α₁⟧ᶻ ⟦.option β₁⟧ᶻ F then
                λᶻ: ⟦α₂.pair β₂⟧ᶻ → .𝔹
                  | xy ↦ if hxy : xy ∈ ⟦.pair α₂ β₂⟧ᶻ then
                          let x := xy.π₁
                          if x_cast : x ∈ ζ₁.Range then
                            let x' := choose (mem_sep.mp x_cast).2
                            have hx' : x' ∈ ⟦α₁⟧ᶻ := by
                              have ⟨dom, _⟩ := choose_spec (mem_sep.mp x_cast).2
                              conv at dom =>
                                enter [1]
                                rw [is_func_dom_eq]
                              exact dom
                            let y := xy.π₂
                            if y_cast : y ∈ ζ₂.Range then
                              let y' := choose (mem_sep.mp y_cast).2
                              have hy' : y' ∈ ⟦β₁⟧ᶻ := by
                                have ⟨dom, _⟩ := choose_spec (mem_sep.mp y_cast).2
                                conv at dom =>
                                  enter [1]
                                  rw [is_func_dom_eq]
                                exact dom
                              -- now apply F to x' and see if we get some y''
                              ZFSet.ZFBool.ofBool <|
                                @ᶻF ⟨x', by rwa [is_func_dom_eq]⟩ = ZFSet.Option.some (S := ⟦β₁⟧ᶻ) ⟨y', hy'⟩
                            else zffalse
                          else zffalse
                        else ∅
                else ∅
    have hR : IsFunc ⟦.fun α₁ (.option β₁)⟧ᶻ ⟦.fun (.pair α₂ β₂) .bool⟧ᶻ R := by
      apply lambda_isFunc
      intro F hF
      rw [mem_funs] at hF
      rw [dite_cond_eq_true (eq_true hF), mem_funs]
      apply lambda_isFunc
      intro xy hxy
      rw [dite_cond_eq_true (eq_true hxy)]
      dsimp
      split_ifs
      · apply ZFBool.mem_ofBool_𝔹
      · exact ZFBool.zffalse_mem_𝔹
      · exact ZFBool.zffalse_mem_𝔹
    ⟨R, hR⟩

abbrev castZF_pairPred {α₁ α₂ β₁ β₂ : SMTType} :
  {ζ₁ // IsFunc ⟦α₁⟧ᶻ ⟦α₂⟧ᶻ ζ₁} →
  {ζ₂ // IsFunc ⟦β₁⟧ᶻ ⟦β₂⟧ᶻ ζ₂} →
  {ff : ZFSet // IsFunc ⟦.fun (.pair α₁ β₁) .bool⟧ᶻ ⟦.fun (.pair α₂ β₂) .bool⟧ᶻ ff} :=
  fun ⟨ζ₁, hζ₁⟩ ⟨ζ₂, hζ₂⟩ ↦
    let ff : ZFSet :=
      (λᶻ : ⟦.fun (.pair α₁ β₁) .bool⟧ᶻ → ⟦.fun (.pair α₂ β₂) .bool⟧ᶻ
          | F ↦ if hF : IsFunc ⟦.pair α₁ β₁⟧ᶻ 𝔹 F then
                  let R :=
                    λᶻ: ⟦α₂.pair β₂⟧ᶻ → .𝔹
                      |       xy      ↦ if hxy : xy ∈ ⟦.pair α₂ β₂⟧ᶻ then
                                          let x := xy.π₁
                                          if x_cast : x ∈ ζ₁.Range then
                                            let x' := choose (mem_sep.mp x_cast).2
                                            have hx' : x' ∈ ⟦α₁⟧ᶻ := by
                                              have ⟨dom, _⟩ := choose_spec (mem_sep.mp x_cast).2
                                              conv at dom =>
                                                enter [1]
                                                rw [is_func_dom_eq]
                                              exact dom
                                            let y := xy.π₂
                                            if y_cast : y ∈ ζ₂.Range then
                                              let y' := choose (mem_sep.mp y_cast).2
                                              have hy' : y' ∈ ⟦β₁⟧ᶻ := by
                                                have ⟨dom, _⟩ := choose_spec (mem_sep.mp y_cast).2
                                                conv at dom =>
                                                  enter [1]
                                                  rw [is_func_dom_eq]
                                                exact dom
                                                @ᶻF ⟨x'.pair y', by
                                                  rw [is_func_dom_eq, pair_mem_prod]
                                                  exact ⟨hx', hy'⟩⟩
                                            else zffalse
                                          else zffalse
                                        else ∅
                  R
                else ∅)
    have hff : IsFunc ⟦.fun (α₁.pair β₁) .bool⟧ᶻ ⟦.fun (α₂.pair β₂) .bool⟧ᶻ ff := by
      apply lambda_isFunc
      intro F hF
      rw [mem_funs] at hF
      rw [dite_cond_eq_true (eq_true hF), mem_funs]
      apply lambda_isFunc
      intro xy hxy
      rw [dite_cond_eq_true (eq_true hxy)]
      dsimp
      split_ifs
      · apply fapply_mem_range
      · exact ZFBool.zffalse_mem_𝔹
      · exact ZFBool.zffalse_mem_𝔹
    ⟨ff, hff⟩

end CastPathToZF

open Classical in
/-- Turn a `CastPath α β` into the semantic cast `⟦α⟧ᶻ → ⟦β⟧ᶻ` with an `IsFunc` certificate. -/
noncomputable def castZF_of_path {α β : SMTType} : CastPath α β →
  {f : ZFSet // IsFunc ⟦α⟧ᶻ ⟦β⟧ᶻ f}
| CastPath.unit               => ⟨𝟙{∅}, Id.IsFunc⟩
| CastPath.int                => ⟨𝟙Int, Id.IsFunc⟩
| CastPath.bool               => ⟨𝟙𝔹, Id.IsFunc⟩
| CastPath.pair p₁ p₂         => castZF_pair (castZF_of_path p₁) (castZF_of_path p₂)
| CastPath.option p           => castZF_option (castZF_of_path p)
| CastPath.funBool p          => castZF_funBool (castZF_of_path p)
| CastPath.funOpt_fun p₁ p₂   => castZF_funOpt (castZF_of_path p₁) (castZF_of_path p₂)
| CastPath.funOpt_graph p₁ p₂ => castZF_funOpt_graph (castZF_of_path p₁) (castZF_of_path p₂)
| CastPath.pairPred p₁ p₂     => castZF_pairPred (castZF_of_path p₁) (castZF_of_path p₂)

theorem castZF_of_path__funBool_id.{u} {α : SMTType} (hTrue : (α ⊑ α) = true)
  (h : castZF_of_path (CastPath.of_true α α hTrue) = ⟨𝟙(SMTType.toZFSet.{u} α), Id.IsFunc⟩) :
    castZF_funBool (castZF_of_path (CastPath.of_true α α hTrue)) =
      ⟨𝟙(SMTType.toZFSet.{u} (.fun α .bool)), Id.IsFunc⟩ := by
  induction α with
  | bool | int | unit =>
    rw [castZF_funBool]
    congr
    ext1 z
    iff_rintro hz hz
    · rw [mem_lambda] at hz
      obtain ⟨x, y, rfl, hx, hy, rfl⟩ := hz
      rw [mem_funs] at hx
      rw [dite_cond_eq_true (eq_true hx)] at hy ⊢
      rw [pair_mem_Id_iff (mem_funs.mpr hx)]
      conv_lhs =>
        rw [lambda_eta hx]
      rw [lambda_ext_iff (fun hz ↦ by rw [dite_cond_eq_true (eq_true hz)]; apply Subtype.property)]
      intro w hw
      rw [dite_cond_eq_true (eq_true hw)]
      split_ifs with w_ran
      · dsimp
        congr
        generalize_proofs isRel exDom
        have ⟨chs_mem, chs_spec⟩ := Classical.choose_spec exDom
        conv at chs_spec =>
          enter [1]
          simp only [CastPath.of_true]
          rw [castZF_of_path]
          dsimp
        rw [pair_mem_Id_iff] at chs_spec
        · exact chs_spec.symm
        · conv_lhs at chs_mem =>
            rw [is_func_dom_eq]
          exact chs_mem
      · -- contradiction
        conv at w_ran =>
          enter [1,1,1]
          simp only [CastPath.of_true]
          rw [castZF_of_path]
          dsimp
        simp only [range_Id] at w_ran
        nomatch w_ran hw
    · rw [mem_Id_iff] at hz
      obtain ⟨f, hf, rfl⟩ := hz
      rw [lambda_spec]
      refine ⟨hf, hf, ?_⟩
      rw [mem_funs] at hf
      rw [dite_cond_eq_true (eq_true hf)]
      conv_lhs =>
        rw [lambda_eta hf]
      rw [lambda_ext_iff (fun hz ↦ by rw [dite_cond_eq_true (eq_true hz)]; apply Subtype.property)]
      intro z hz
      rw [dite_cond_eq_true (eq_true hz)]
      split_ifs with z_ran
      · dsimp
        congr
        generalize_proofs isRel exDom
        have ⟨chs_mem, chs_spec⟩ := Classical.choose_spec exDom
        conv at chs_spec =>
          enter [1]
          simp only [CastPath.of_true]
          rw [castZF_of_path]
          dsimp
        rw [pair_mem_Id_iff] at chs_spec
        · exact chs_spec.symm
        · conv_lhs at chs_mem =>
            rw [is_func_dom_eq]
          exact chs_mem
      · -- contradiction
        conv at z_ran =>
          enter [1,1,1]
          simp only [CastPath.of_true]
          rw [castZF_of_path]
          dsimp
        simp only [range_Id] at z_ran
        nomatch z_ran hz
  | pair α β α_ih β_ih =>
    simp only [cast_pair_true_iff, SMTType.pair.injEq, ↓existsAndEq, and_true,
      exists_eq_left'] at hTrue
    obtain ⟨hα, hβ⟩ := hTrue
    specialize α_ih hα
    specialize β_ih hβ
    rw [castZF_funBool]
    congr
    rw [ZFSet.ext_iff]
    intro xy
    iff_intro hxy hxy
    · rw [mem_lambda] at hxy
      obtain ⟨x, y, rfl, mem_x, mem_y, rfl⟩ := hxy
      rw [mem_funs] at mem_x
      rw [dite_cond_eq_true (eq_true mem_x)] at mem_y ⊢
      rw [pair_mem_Id_iff (mem_funs.mpr mem_x)]
      conv_lhs =>
        rw [lambda_eta mem_x]
      rw [lambda_ext_iff (fun hz ↦ by rw [dite_cond_eq_true (eq_true hz)]; apply Subtype.property)]
      intro z hz
      rw [dite_cond_eq_true (eq_true hz)]
      split_ifs with z_ran
      · dsimp
        congr
        generalize_proofs isRel exDom
        have ⟨chs_mem, chs_spec⟩ := Classical.choose_spec exDom
        simp [CastPath.of_true] at chs_spec

        generalize_proofs chs₁ chs₂ hTrue₁ hTrue₂ chs_eq chs₃ at chs_spec

        rw [Subtype.ext_iff] at h
        dsimp at h

        let ⟨exDom_mem, z_spec⟩ := Classical.choose_spec exDom
        conv_lhs at z_spec =>
          rw [h]
        conv at exDom_mem =>
          enter [1,1]
          rw [h]
        rw [is_func_dom_eq Id.IsFunc] at exDom_mem
        symm
        rwa [pair_mem_Id_iff exDom_mem] at z_spec
      · -- contradiction
        rw [Subtype.ext_iff] at h
        dsimp at h
        conv at z_ran =>
          enter [1]
          conv =>
            enter [1,1]
            rw [h]
          rw [ZFSet.range_Id]
        nomatch z_ran hz
    · rw [mem_Id_iff] at hxy
      obtain ⟨f, hf, rfl⟩ := hxy
      rw [lambda_spec]
      refine ⟨hf, hf, ?_⟩
      rw [mem_funs] at hf
      rw [dite_cond_eq_true (eq_true hf)]
      conv_lhs =>
        rw [lambda_eta hf]
      rw [lambda_ext_iff (fun hz ↦ by rw [dite_cond_eq_true (eq_true hz)]; apply Subtype.property)]
      intro z hz
      rw [dite_cond_eq_true (eq_true hz)]
      split_ifs with z_ran
      · dsimp
        congr
        generalize_proofs isRel exDom
        have ⟨chs_mem, chs_spec⟩ := Classical.choose_spec exDom
        simp [CastPath.of_true] at chs_spec

        generalize_proofs chs₁ chs₂ hTrue₁ hTrue₂ chs_eq chs₃ at chs_spec

        rw [Subtype.ext_iff] at h
        dsimp at h

        let ⟨exDom_mem, z_spec⟩ := Classical.choose_spec exDom
        conv_lhs at z_spec =>
          rw [h]
        conv at exDom_mem =>
          enter [1,1]
          rw [h]
        rw [is_func_dom_eq Id.IsFunc] at exDom_mem
        symm
        rwa [pair_mem_Id_iff exDom_mem] at z_spec
      · -- contradiction
        rw [Subtype.ext_iff] at h
        dsimp at h
        conv at z_ran =>
          enter [1]
          conv =>
            enter [1,1]
            rw [h]
          rw [ZFSet.range_Id]
        nomatch z_ran hz
  | option τ ih =>
    simp only [cast_option_true_iff, SMTType.option.injEq, exists_eq_left'] at hTrue
    specialize ih hTrue
    rw [castZF_funBool]
    congr
    rw [ZFSet.ext_iff]
    intro xy
    iff_intro hxy hxy
    · rw [mem_lambda] at hxy
      obtain ⟨x, y, rfl, mem_x, mem_y, rfl⟩ := hxy
      rw [mem_funs] at mem_x
      rw [dite_cond_eq_true (eq_true mem_x)] at mem_y ⊢
      rw [pair_mem_Id_iff (mem_funs.mpr mem_x)]
      conv_lhs =>
        rw [lambda_eta mem_x]
      rw [lambda_ext_iff (fun hz ↦ by rw [dite_cond_eq_true (eq_true hz)]; apply Subtype.property)]
      intro z hz
      rw [dite_cond_eq_true (eq_true hz)]
      split_ifs with z_ran
      · dsimp
        congr
        generalize_proofs isRel exDom
        have ⟨chs_mem, chs_spec⟩ := Classical.choose_spec exDom
        simp [CastPath.of_true] at chs_spec

        generalize_proofs chs₁ chs₂ hTrue₁ hTrue₂ chs_eq chs₃ at chs_spec

        rw [Subtype.ext_iff] at h
        dsimp at h

        let ⟨exDom_mem, z_spec⟩ := Classical.choose_spec exDom
        conv_lhs at z_spec =>
          rw [h]
        conv at exDom_mem =>
          enter [1,1]
          rw [h]
        rw [is_func_dom_eq Id.IsFunc] at exDom_mem
        symm
        rwa [pair_mem_Id_iff exDom_mem] at z_spec
      · -- contradiction
        rw [Subtype.ext_iff] at h
        dsimp at h
        conv at z_ran =>
          enter [1]
          conv =>
            enter [1,1]
            rw [h]
          rw [ZFSet.range_Id]
        nomatch z_ran hz
    · rw [mem_Id_iff] at hxy
      obtain ⟨f, hf, rfl⟩ := hxy
      rw [lambda_spec]
      refine ⟨hf, hf, ?_⟩
      rw [mem_funs] at hf
      rw [dite_cond_eq_true (eq_true hf)]
      conv_lhs =>
        rw [lambda_eta hf]
      rw [lambda_ext_iff (fun hz ↦ by rw [dite_cond_eq_true (eq_true hz)]; apply Subtype.property)]
      intro z hz
      rw [dite_cond_eq_true (eq_true hz)]
      split_ifs with z_ran
      · dsimp
        congr
        generalize_proofs isRel exDom
        have ⟨chs_mem, chs_spec⟩ := Classical.choose_spec exDom
        simp [CastPath.of_true] at chs_spec

        generalize_proofs chs₁ chs₂ hTrue₁ hTrue₂ chs_eq chs₃ at chs_spec

        rw [Subtype.ext_iff] at h
        dsimp at h

        let ⟨exDom_mem, z_spec⟩ := Classical.choose_spec exDom
        conv_lhs at z_spec =>
          rw [h]
        conv at exDom_mem =>
          enter [1,1]
          rw [h]
        rw [is_func_dom_eq Id.IsFunc] at exDom_mem
        symm
        rwa [pair_mem_Id_iff exDom_mem] at z_spec
      · -- contradiction
        rw [Subtype.ext_iff] at h
        dsimp at h
        conv at z_ran =>
          enter [1]
          conv =>
            enter [1,1]
            rw [h]
          rw [ZFSet.range_Id]
        nomatch z_ran hz
  | «fun» α β α_ih β_ih =>
    cases β with
    | int | unit | pair α β | «fun» τ σ =>
      simp only [castable?, Bool.false_eq_true] at hTrue
    | option β =>
      simp only [cast_fun_opt_true_iff, SMTType.fun.injEq, SMTType.option.injEq, ↓existsAndEq, and_true, exists_eq_left'] at hTrue
      obtain ⟨hα, hβ⟩ := hTrue
      specialize α_ih hα
      specialize β_ih hβ
      rw [castZF_funBool]
      congr
      rw [ZFSet.ext_iff]
      intro xy
      iff_intro hxy hxy
      · rw [mem_lambda] at hxy
        obtain ⟨x, y, rfl, mem_x, mem_y, rfl⟩ := hxy
        rw [mem_funs] at mem_x
        rw [dite_cond_eq_true (eq_true mem_x)] at mem_y ⊢
        rw [pair_mem_Id_iff (mem_funs.mpr mem_x)]
        conv_lhs =>
          rw [lambda_eta mem_x]
        rw [lambda_ext_iff (fun hz ↦ by rw [dite_cond_eq_true (eq_true hz)]; apply Subtype.property)]
        intro z hz
        rw [dite_cond_eq_true (eq_true hz)]
        split_ifs with z_ran
        · dsimp
          congr
          generalize_proofs isRel exDom
          have ⟨chs_mem, chs_spec⟩ := Classical.choose_spec exDom
          simp [CastPath.of_true] at chs_spec

          generalize_proofs chs₁ chs₂ hTrue₁ hTrue₂ chs_eq chs₃ at chs_spec

          rw [Subtype.ext_iff] at h
          dsimp at h

          let ⟨exDom_mem, z_spec⟩ := Classical.choose_spec exDom
          conv_lhs at z_spec =>
            rw [h]
          conv at exDom_mem =>
            enter [1,1]
            rw [h]
          rw [is_func_dom_eq Id.IsFunc] at exDom_mem
          symm
          rwa [pair_mem_Id_iff exDom_mem] at z_spec
        · -- contradiction
          rw [Subtype.ext_iff] at h
          dsimp at h
          conv at z_ran =>
            enter [1]
            conv =>
              enter [1,1]
              rw [h]
            rw [ZFSet.range_Id]
          nomatch z_ran hz
      · rw [mem_Id_iff] at hxy
        obtain ⟨f, hf, rfl⟩ := hxy
        rw [lambda_spec]
        refine ⟨hf, hf, ?_⟩
        rw [mem_funs] at hf
        rw [dite_cond_eq_true (eq_true hf)]
        conv_lhs =>
          rw [lambda_eta hf]
        rw [lambda_ext_iff (fun hz ↦ by rw [dite_cond_eq_true (eq_true hz)]; apply Subtype.property)]
        intro z hz
        rw [dite_cond_eq_true (eq_true hz)]
        split_ifs with z_ran
        · dsimp
          congr
          generalize_proofs isRel exDom
          have ⟨chs_mem, chs_spec⟩ := Classical.choose_spec exDom
          simp [CastPath.of_true] at chs_spec

          generalize_proofs chs₁ chs₂ hTrue₁ hTrue₂ chs_eq chs₃ at chs_spec

          rw [Subtype.ext_iff] at h
          dsimp at h

          let ⟨exDom_mem, z_spec⟩ := Classical.choose_spec exDom
          conv_lhs at z_spec =>
            rw [h]
          conv at exDom_mem =>
            enter [1,1]
            rw [h]
          rw [is_func_dom_eq Id.IsFunc] at exDom_mem
          symm
          rwa [pair_mem_Id_iff exDom_mem] at z_spec
        · -- contradiction
          rw [Subtype.ext_iff] at h
          dsimp at h
          conv at z_ran =>
            enter [1]
            conv =>
              enter [1,1]
              rw [h]
            rw [ZFSet.range_Id]
          nomatch z_ran hz
    | bool =>
      simp only [cast_fun_bool_true_iff, SMTType.fun.injEq, and_true, exists_eq_left', reduceCtorEq, and_false, false_and, exists_const, or_false] at hTrue
      specialize α_ih hTrue
      rw [castZF_funBool]
      congr
      rw [ZFSet.ext_iff]
      intro xy
      iff_intro hxy hxy
      · rw [mem_lambda] at hxy
        obtain ⟨x, y, rfl, mem_x, mem_y, rfl⟩ := hxy
        rw [mem_funs] at mem_x
        rw [dite_cond_eq_true (eq_true mem_x)] at mem_y ⊢
        rw [pair_mem_Id_iff (mem_funs.mpr mem_x)]
        conv_lhs =>
          rw [lambda_eta mem_x]
        rw [lambda_ext_iff (fun hz ↦ by rw [dite_cond_eq_true (eq_true hz)]; apply Subtype.property)]
        intro z hz
        rw [dite_cond_eq_true (eq_true hz)]
        split_ifs with z_ran
        · dsimp
          congr
          generalize_proofs isRel exDom
          have ⟨chs_mem, chs_spec⟩ := Classical.choose_spec exDom

          generalize_proofs chs₁ chs₂ hTrue₁ hTrue₂ chs_eq chs₃ at chs_spec

          rw [Subtype.ext_iff] at h
          dsimp at h

          let ⟨exDom_mem, z_spec⟩ := Classical.choose_spec exDom
          conv_lhs at z_spec =>
            rw [h]
          conv at exDom_mem =>
            enter [1,1]
            rw [h]
          rw [is_func_dom_eq Id.IsFunc] at exDom_mem
          symm
          rwa [pair_mem_Id_iff exDom_mem] at z_spec
        · -- contradiction
          rw [Subtype.ext_iff] at h
          dsimp at h
          conv at z_ran =>
            enter [1]
            conv =>
              enter [1,1]
              rw [h]
            rw [ZFSet.range_Id]
          nomatch z_ran hz
      · rw [mem_Id_iff] at hxy
        obtain ⟨f, hf, rfl⟩ := hxy
        rw [lambda_spec]
        refine ⟨hf, hf, ?_⟩
        rw [mem_funs] at hf
        rw [dite_cond_eq_true (eq_true hf)]
        conv_lhs =>
          rw [lambda_eta hf]
        rw [lambda_ext_iff (fun hz ↦ by rw [dite_cond_eq_true (eq_true hz)]; apply Subtype.property)]
        intro z hz
        rw [dite_cond_eq_true (eq_true hz)]
        split_ifs with z_ran
        · dsimp
          congr
          generalize_proofs isRel exDom
          have ⟨chs_mem, chs_spec⟩ := Classical.choose_spec exDom

          generalize_proofs chs₁ chs₂ hTrue₁ hTrue₂ chs_eq chs₃ at chs_spec

          rw [Subtype.ext_iff] at h
          dsimp at h

          let ⟨exDom_mem, z_spec⟩ := Classical.choose_spec exDom
          conv_lhs at z_spec =>
            rw [h]
          conv at exDom_mem =>
            enter [1,1]
            rw [h]
          rw [is_func_dom_eq Id.IsFunc] at exDom_mem
          symm
          rwa [pair_mem_Id_iff exDom_mem] at z_spec
        · -- contradiction
          rw [Subtype.ext_iff] at h
          dsimp at h
          conv at z_ran =>
            enter [1]
            conv =>
              enter [1,1]
              rw [h]
            rw [ZFSet.range_Id]
          nomatch z_ran hz

lemma castZF_of_path_of_true_funBool_aux {α : SMTType} (h : (α.fun .bool ⊑ α.fun .bool) = true) :
  castZF_of_path (CastPath.of_true (α.fun SMTType.bool) (α.fun SMTType.bool) h) =
  castZF_funBool (castZF_of_path (CastPath.of_true α α (by simpa using h))) := by
  conv =>
    enter [1,1]
    unfold CastPath.of_true
    simp only [SMTType.fun.injEq, reduceCtorEq, and_false, false_and, exists_const, ↓reduceDIte]
  admit


theorem castZF_of_path_id {α : SMTType} (h : (α ⊑ α) = true) :
    castZF_of_path (CastPath.of_true α α h) = ⟨𝟙⟦α⟧ᶻ, Id.IsFunc⟩ := by
  induction α with
  | bool => rfl
  | int => rfl
  | unit => rfl
  | pair α β α_ih β_ih =>
    simp only [cast_pair_true_iff, SMTType.pair.injEq, ↓existsAndEq, and_true, exists_eq_left'] at h
    obtain ⟨hα, hβ⟩ := h
    specialize α_ih hα
    specialize β_ih hβ
    rw [Subtype.ext_iff]
    dsimp
    ext1 xy
    iff_intro hxy hxy
    · rw [mem_Id_iff]
      admit
    · rw [mem_Id_iff] at hxy
      obtain ⟨x, hx, rfl⟩ := hxy
      admit
  | «fun» α β α_ih β_ih =>
    cases β with
    | int | unit | pair τ σ | «fun» τ σ =>
      simp only [castable?, Bool.false_eq_true] at h
    | bool =>
      have hα := h
      simp only [cast_fun_bool_true_iff, SMTType.fun.injEq, and_true, exists_eq_left', reduceCtorEq, and_false, false_and, exists_const, or_false] at hα
      specialize α_ih hα
      have :
        castZF_of_path (CastPath.of_true (α.fun SMTType.bool) (α.fun SMTType.bool) h) =
        castZF_funBool (castZF_of_path (CastPath.of_true α α hα)) := by
        rw [Subtype.ext_iff]
        ext1 z
        iff_intro hz hz
        · simp only [mem_sep, mem_lambda, ↓existsAndEq, mem_funs, and_true]
          admit
        · admit

      rwa [this, castZF_of_path__funBool_id hα]
    | option β => admit
  | option τ ih => admit



open Classical in
noncomputable def castZF.{u} (α β : SMTType) (cast? : α ⊑ β) :
  {f : ZFSet.{u} // ⟦α⟧ᶻ.IsFunc ⟦β⟧ᶻ f} :=
  castZF_of_path <| CastPath.of_true α β cast?

-- denx! = (castZF α β cast?) @ᶻdenx ??
