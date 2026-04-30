import Encoder.Loosening
import SMT.Reasoning.Defs
import SMT.Reasoning.Lemmas

set_option linter.style.nameCheck false

open Std.Do SMT ZFSet

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

abbrev castZF_chpred {α β : SMTType} :
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

abbrev castZF_fun {α₁ α₂ β₁ β₂ : SMTType} :
  {ζ₁ // IsFunc ⟦α₁⟧ᶻ ⟦α₂⟧ᶻ ζ₁} →
  {ζ₂ // IsFunc ⟦β₁⟧ᶻ ⟦β₂⟧ᶻ ζ₂} →
  {ff : ZFSet // IsFunc ⟦.fun α₁ β₁⟧ᶻ ⟦.fun α₂ β₂⟧ᶻ ff} :=
  fun ⟨ζ₁, hζ₁⟩ ⟨ζ₂, hζ₂⟩ ↦
    let ff : ZFSet :=
      (λᶻ : ⟦.fun α₁ β₁⟧ᶻ → ⟦.fun α₂ β₂⟧ᶻ
          |      F        ↦ if hF : IsFunc ⟦α₁⟧ᶻ ⟦β₁⟧ᶻ F then
                              -- ζ₂ ∘ᶻ (F ∘ᶻ ζ₁⁻¹) : ⟦α₂⟧ᶻ (→ ⟦α₁⟧ᶻ → ⟦β₁⟧ᶻ) → ⟦β₂⟧ᶻ
                              λᶻ: ⟦α₂⟧ᶻ → ⟦β₂⟧ᶻ
                                |   x   ↦ if hx : x ∈ ζ₁.Range then
                                            let x' := choose (mem_sep.mp hx).2
                                            have hx' : x' ∈ ⟦α₁⟧ᶻ := by
                                              have ⟨dom, _⟩ := choose_spec (mem_sep.mp hx).2
                                              conv at dom =>
                                                enter [1]
                                                rw [is_func_dom_eq]
                                              exact dom
                                          let y := fapply F (is_func_is_pfunc hF) ⟨x', by rwa [is_func_dom_eq]⟩
                                          @ᶻζ₂ ⟨y, by rw [is_func_dom_eq]; apply Subtype.property⟩
                                        else
                                            β₂.defaultZFSet
                            else ∅)
    have hff : IsFunc ⟦.fun α₁ β₁⟧ᶻ ⟦.fun α₂ β₂⟧ᶻ ff := by
      apply lambda_isFunc
      intro F hF
      rw [mem_funs] at hF
      rw [dite_cond_eq_true (eq_true hF), mem_funs]
      apply lambda_isFunc
      intro y hy
      split_ifs with hy_range
      · apply fapply_mem_range
      · exact SMTType.mem_toZFSet_of_defaultZFSet
    ⟨ff, hff⟩

abbrev castZF_graph {α₁ α₂ β₁ β₂ : SMTType} :
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
noncomputable def castZF_of_path {α β : SMTType} : α ~> β → {f : ZFSet // IsFunc ⟦α⟧ᶻ ⟦β⟧ᶻ f}
  | @castPath.refl α _ => ⟨𝟙⟦α⟧ᶻ, Id.IsFunc⟩
  | @castPath.chpred α α' 𝕔 => castZF_chpred <| castZF_of_path 𝕔
  | @castPath.graph α β α' β' 𝕔α 𝕔β => castZF_graph (castZF_of_path 𝕔α) (castZF_of_path 𝕔β)
  | @castPath.fun α β α' β' β_ne 𝕔α 𝕔β => castZF_fun (castZF_of_path 𝕔α) (castZF_of_path 𝕔β)
  | @castPath.opt α α' 𝕔 => castZF_option (castZF_of_path 𝕔)
  | @castPath.pair α β α' β' 𝕔α 𝕔β => castZF_pair (castZF_of_path 𝕔α) (castZF_of_path 𝕔β)

theorem castZF_pair_injective {α₁ β₁ α₂ β₂ : SMTType} {ζ₁ ζ₂ : ZFSet}
    {hζ₁ : IsFunc ⟦α₁⟧ᶻ ⟦β₁⟧ᶻ ζ₁} {hζ₂ : IsFunc ⟦α₂⟧ᶻ ⟦β₂⟧ᶻ ζ₂}
    (hζ₁_inj : ζ₁.IsInjective hζ₁) (hζ₂_inj : ζ₂.IsInjective hζ₂) :
    ((castZF_pair ⟨ζ₁, hζ₁⟩ ⟨ζ₂, hζ₂⟩).1).IsInjective
      ((castZF_pair ⟨ζ₁, hζ₁⟩ ⟨ζ₂, hζ₂⟩).2) := by
  simpa [castZF_pair] using
    (ZFSet.fprod_injective_of_injective (hφ := hζ₁) (hψ := hζ₂) hζ₁_inj hζ₂_inj)

theorem castZF_option_injective {α β : SMTType} {ζ : ZFSet}
    {hζ : IsFunc ⟦α⟧ᶻ ⟦β⟧ᶻ ζ}
    (hζ_inj : ζ.IsInjective hζ) :
    ((castZF_option ⟨ζ, hζ⟩).1).IsInjective ((castZF_option ⟨ζ, hζ⟩).2) := by
  classical
  let fopt : ZFSet :=
    λᶻ: ⟦α.option⟧ᶻ → ⟦β.option⟧ᶻ
      | x ↦ if hx : x ∈ ⟦α.option⟧ᶻ then
              if is_none : x = ZFSet.Option.none (S := ⟦α⟧ᶻ).val then
                ZFSet.Option.none (S := ⟦β⟧ᶻ).val
              else
                have y_def : ∃ y, x = (ZFSet.Option.some (S := ⟦α⟧ᶻ) y).val := by
                  obtain ⟨y, hy⟩ := ZFSet.Option.casesOn ⟨x, hx⟩ |>.resolve_left (by
                    rw [Subtype.ext_iff]
                    exact is_none)
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
  have hfopt_inj : fopt.IsInjective hfopt := by
    intro x y z hx hy hz xz yz
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
      rw [dite_cond_eq_false (eq_false (fun contr ↦ by
        rw [←Subtype.ext_iff] at contr
        nomatch ZFSet.Option.some_ne_none _ contr))] at eq
      dsimp at eq
      split_ifs at eq with isnone'
      · rw [←Subtype.ext_iff] at eq
        nomatch ZFSet.Option.some_ne_none _ eq
      · rw [←Subtype.ext_iff] at eq
        generalize_proofs _ _ some_w'_eq _ y_eq at eq
        set w' := Classical.choose y_eq
        have hw' := Classical.choose_spec y_eq
        rw [ZFSet.Option.some.injEq] at eq
        injection @ZFSet.IsInjective.apply_inj ζ _ _ hζ hζ_inj _ _ eq with eq
        rw [←Subtype.ext_iff] at eq
        rw [hw', ←eq]
        exact Classical.choose_spec some_w'_eq
  simpa [castZF_option, fopt, hfopt] using hfopt_inj

theorem castZF_chpred_injective {α β : SMTType} {cast : ZFSet}
    {hcast : IsFunc ⟦α⟧ᶻ ⟦β⟧ᶻ cast}
    (hcast_inj : cast.IsInjective hcast) :
    ((castZF_chpred ⟨cast, hcast⟩).1).IsInjective ((castZF_chpred ⟨cast, hcast⟩).2) := by
  classical
  let ff : ZFSet :=
    λᶻ: ⟦.fun α .bool⟧ᶻ → ⟦.fun β .bool⟧ᶻ
      | f_α ↦ if hf_α : IsFunc ⟦α⟧ᶻ 𝔹 f_α then
                λᶻ: ⟦β⟧ᶻ → .𝔹
                  | y ↦ if y_ran : y ∈ cast.Range then
                          let x := Classical.choose (mem_sep.mp y_ran).2
                          have hx : x ∈ ⟦α⟧ᶻ := by
                            have ⟨dom, _⟩ := Classical.choose_spec (mem_sep.mp y_ran).2
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
    · have hx : Classical.choose (mem_sep.mp y_ran).2 ∈ ⟦α⟧ᶻ := by
        have ⟨dom, _⟩ := Classical.choose_spec (mem_sep.mp y_ran).2
        conv at dom =>
          enter [1]
          rw [is_func_dom_eq]
        exact dom
      exact fapply_mem_range (is_func_is_pfunc hf_α) (by rwa [is_func_dom_eq])
    · exact ZFBool.zffalse_mem_𝔹
  have hff_inj : ff.IsInjective hff := by
    intro f g h hf hg hh fh gh
    rw [mem_funs] at hf hg hh
    rw [lambda_spec] at fh gh
    rw [dite_cond_eq_true (eq_true hf)] at fh
    rw [dite_cond_eq_true (eq_true hg)] at gh
    obtain ⟨-, -, rfl⟩ := fh
    obtain ⟨-, -, eq⟩ := gh
    let bodyf : ZFSet → ZFSet := fun y =>
      if y_ran : y ∈ cast.Range then
        let x := Classical.choose (mem_sep.mp y_ran).2
        have hx : x ∈ ⟦α⟧ᶻ := by
          have ⟨dom, _⟩ := Classical.choose_spec (mem_sep.mp y_ran).2
          conv at dom =>
            enter [1]
            rw [is_func_dom_eq]
          exact dom
        @ᶻf ⟨x, by rwa [is_func_dom_eq]⟩
      else zffalse
    let bodyg : ZFSet → ZFSet := fun y =>
      if y_ran : y ∈ cast.Range then
        let x := Classical.choose (mem_sep.mp y_ran).2
        have hx : x ∈ ⟦α⟧ᶻ := by
          have ⟨dom, _⟩ := Classical.choose_spec (mem_sep.mp y_ran).2
          conv at dom =>
            enter [1]
            rw [is_func_dom_eq]
          exact dom
        @ᶻg ⟨x, by rwa [is_func_dom_eq]⟩
      else zffalse
    have hbodyf : ∀ {y}, y ∈ ⟦β⟧ᶻ → bodyf y ∈ 𝔹 := by
      intro y hy
      by_cases hy_ran : y ∈ cast.Range
      · unfold bodyf
        rw [dif_pos hy_ran]
        dsimp
        have hx : Classical.choose (mem_sep.mp hy_ran).2 ∈ ⟦α⟧ᶻ := by
          exact (mem_sep.mp ((Classical.choose_spec (mem_sep.mp hy_ran).2).1)).1
        exact fapply_mem_range (is_func_is_pfunc hf) (by
          rwa [is_func_dom_eq])
      · unfold bodyf
        rw [dif_neg hy_ran]
        exact ZFBool.zffalse_mem_𝔹
    have hEq : (λᶻ: ⟦β⟧ᶻ → 𝔹 | y ↦ bodyf y) = (λᶻ: ⟦β⟧ᶻ → 𝔹 | y ↦ bodyg y) := by
      simpa [bodyf, bodyg] using eq
    have eq' := (ZFSet.lambda_ext_iff (d := ⟦β⟧ᶻ) (r := 𝔹) (f₁ := bodyf) (f₂ := bodyg) hbodyf).mp hEq
    rw [lambda_eta hf, lambda_eta hg]
    let srcf : ZFSet → ZFSet := fun z =>
      if hz : z ∈ ⟦α⟧ᶻ then @ᶻf ⟨z, by rwa [is_func_dom_eq]⟩ else ∅
    let srcg : ZFSet → ZFSet := fun z =>
      if hz : z ∈ ⟦α⟧ᶻ then @ᶻg ⟨z, by rwa [is_func_dom_eq]⟩ else ∅
    have hsrcf : ∀ {z}, z ∈ ⟦α⟧ᶻ → srcf z ∈ 𝔹 := by
      intro z hz
      unfold srcf
      rw [dif_pos hz]
      exact fapply_mem_range (is_func_is_pfunc hf) (by rwa [is_func_dom_eq])
    change (λᶻ: ⟦α⟧ᶻ → 𝔹 | z ↦ srcf z) = (λᶻ: ⟦α⟧ᶻ → 𝔹 | z ↦ srcg z)
    have hsrcEq : (λᶻ: ⟦α⟧ᶻ → 𝔹 | z ↦ srcf z) = (λᶻ: ⟦α⟧ᶻ → 𝔹 | z ↦ srcg z) := by
      apply (ZFSet.lambda_ext_iff
        (d := ⟦α⟧ᶻ) (r := 𝔹)
        (f₁ := srcf) (f₂ := srcg) hsrcf).2
      intro z hz
      unfold srcf srcg
      rw [dif_pos hz, dif_pos hz]
      let y : ZFSet := (@ᶻcast ⟨z, by rwa [is_func_dom_eq]⟩).val
      have hy : y ∈ ⟦β⟧ᶻ := by
        simpa [y] using fapply_mem_range (is_func_is_pfunc hcast) (by rwa [is_func_dom_eq])
      have hy_range : y ∈ cast.Range := by
        simpa [y] using ZFSet.IsPFunc.mem_range_of_mem (is_func_is_pfunc hcast)
          (fapply.def (is_func_is_pfunc hcast) (by rwa [is_func_dom_eq]))
      specialize eq' y hy
      unfold bodyf bodyg at eq'
      rw [dif_pos hy_range, dif_pos hy_range] at eq'
      dsimp at eq'
      set z' := Classical.choose (mem_sep.mp hy_range).2 with hz'_def
      have hz'_dom : z' ∈ cast.Dom := by
        simpa [hz'_def] using (Classical.choose_spec (mem_sep.mp hy_range).2).1
      have hz'_mem : z' ∈ ⟦α⟧ᶻ := by
        exact (mem_sep.mp hz'_dom).1
      have hz'_pair : z'.pair y ∈ cast := by
        simpa [hz'_def] using (Classical.choose_spec (mem_sep.mp hy_range).2).2
      have hz_pair : z.pair y ∈ cast := by
        simpa [y] using fapply.def (is_func_is_pfunc hcast) (by rwa [is_func_dom_eq])
      have hz'_eq : z' = z := hcast_inj z' z y hz'_mem hz hy hz'_pair hz_pair
      have hz'_dom_f : z' ∈ f.Dom := by
        rwa [is_func_dom_eq]
      have hz'_dom_g : z' ∈ g.Dom := by
        rwa [is_func_dom_eq]
      have eq'' : @ᶻf ⟨z', hz'_dom_f⟩ = @ᶻg ⟨z', hz'_dom_g⟩ := by
        apply Subtype.ext
        simpa [hz'_def] using eq'
      have hargf :
          (⟨z', hz'_dom_f⟩ : {x // x ∈ f.Dom}) = ⟨z, by rwa [is_func_dom_eq]⟩ := by
        apply Subtype.ext
        exact hz'_eq
      have hargg :
          (⟨z', hz'_dom_g⟩ : {x // x ∈ g.Dom}) = ⟨z, by rwa [is_func_dom_eq]⟩ := by
        apply Subtype.ext
        exact hz'_eq
      have hf_eq : @ᶻf ⟨z', hz'_dom_f⟩ = @ᶻf ⟨z, by rwa [is_func_dom_eq]⟩ :=
        congrArg (fun a => @ᶻf a) hargf
      have hg_eq : @ᶻg ⟨z', hz'_dom_g⟩ = @ᶻg ⟨z, by rwa [is_func_dom_eq]⟩ :=
        congrArg (fun a => @ᶻg a) hargg
      have hEq_sub : @ᶻf ⟨z, by rwa [is_func_dom_eq]⟩ = @ᶻg ⟨z, by rwa [is_func_dom_eq]⟩ :=
        hf_eq.symm.trans (eq''.trans hg_eq)
      exact congrArg Subtype.val hEq_sub
    exact hsrcEq
  change ff.IsInjective hff
  exact hff_inj

set_option maxHeartbeats 400000 in
theorem castZF_graph_injective {α₁ α₂ β₁ β₂ : SMTType} {ζ₁ ζ₂ : ZFSet}
    {hζ₁ : IsFunc ⟦α₁⟧ᶻ ⟦α₂⟧ᶻ ζ₁} {hζ₂ : IsFunc ⟦β₁⟧ᶻ ⟦β₂⟧ᶻ ζ₂}
    (hζ₁_inj : ζ₁.IsInjective hζ₁) (hζ₂_inj : ζ₂.IsInjective hζ₂) :
    ((castZF_graph ⟨ζ₁, hζ₁⟩ ⟨ζ₂, hζ₂⟩).1).IsInjective
      ((castZF_graph ⟨ζ₁, hζ₁⟩ ⟨ζ₂, hζ₂⟩).2) := by
  classical
  let R : ZFSet :=
    λᶻ: ⟦.fun α₁ (.option β₁)⟧ᶻ → ⟦.fun (.pair α₂ β₂) .bool⟧ᶻ
      | F ↦ if hF : IsFunc ⟦α₁⟧ᶻ ⟦.option β₁⟧ᶻ F then
              λᶻ: ⟦α₂.pair β₂⟧ᶻ → .𝔹
                | xy ↦ if hxy : xy ∈ ⟦.pair α₂ β₂⟧ᶻ then
                        let x := xy.π₁
                        if x_cast : x ∈ ζ₁.Range then
                          let x' := Classical.choose (mem_sep.mp x_cast).2
                          have hx' : x' ∈ ⟦α₁⟧ᶻ := by
                            have ⟨dom, _⟩ := Classical.choose_spec (mem_sep.mp x_cast).2
                            conv at dom =>
                              enter [1]
                              rw [is_func_dom_eq]
                            exact dom
                          let y := xy.π₂
                          if y_cast : y ∈ ζ₂.Range then
                            let y' := Classical.choose (mem_sep.mp y_cast).2
                            have hy' : y' ∈ ⟦β₁⟧ᶻ := by
                              have ⟨dom, _⟩ := Classical.choose_spec (mem_sep.mp y_cast).2
                              conv at dom =>
                                enter [1]
                                rw [is_func_dom_eq]
                              exact dom
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
  have hR_inj : R.IsInjective hR := by
    intro F G H hF hG hH hFR hGR
    rw [mem_funs] at hF hG hH
    rw [lambda_spec] at hFR hGR
    rw [dite_cond_eq_true (eq_true hF)] at hFR
    rw [dite_cond_eq_true (eq_true hG)] at hGR
    obtain ⟨-, -, rfl⟩ := hFR
    obtain ⟨-, -, hFG_eq⟩ := hGR
    let bodyF : ZFSet → ZFSet := fun xy =>
      if hxy : xy ∈ ⟦.pair α₂ β₂⟧ᶻ then
        let x := xy.π₁
        if x_cast : x ∈ ζ₁.Range then
          let x' := Classical.choose (mem_sep.mp x_cast).2
          have hx' : x' ∈ ⟦α₁⟧ᶻ := by
            have ⟨dom, _⟩ := Classical.choose_spec (mem_sep.mp x_cast).2
            conv at dom =>
              enter [1]
              rw [is_func_dom_eq]
            exact dom
          let y := xy.π₂
          if y_cast : y ∈ ζ₂.Range then
            let y' := Classical.choose (mem_sep.mp y_cast).2
            have hy' : y' ∈ ⟦β₁⟧ᶻ := by
              have ⟨dom, _⟩ := Classical.choose_spec (mem_sep.mp y_cast).2
              conv at dom =>
                enter [1]
                rw [is_func_dom_eq]
              exact dom
            ZFSet.ZFBool.ofBool <|
              @ᶻF ⟨x', by rwa [is_func_dom_eq]⟩ = ZFSet.Option.some (S := ⟦β₁⟧ᶻ) ⟨y', hy'⟩
          else zffalse
        else zffalse
      else ∅
    let bodyG : ZFSet → ZFSet := fun xy =>
      if hxy : xy ∈ ⟦.pair α₂ β₂⟧ᶻ then
        let x := xy.π₁
        if x_cast : x ∈ ζ₁.Range then
          let x' := Classical.choose (mem_sep.mp x_cast).2
          have hx' : x' ∈ ⟦α₁⟧ᶻ := by
            have ⟨dom, _⟩ := Classical.choose_spec (mem_sep.mp x_cast).2
            conv at dom =>
              enter [1]
              rw [is_func_dom_eq]
            exact dom
          let y := xy.π₂
          if y_cast : y ∈ ζ₂.Range then
            let y' := Classical.choose (mem_sep.mp y_cast).2
            have hy' : y' ∈ ⟦β₁⟧ᶻ := by
              have ⟨dom, _⟩ := Classical.choose_spec (mem_sep.mp y_cast).2
              conv at dom =>
                enter [1]
                rw [is_func_dom_eq]
              exact dom
            ZFSet.ZFBool.ofBool <|
              @ᶻG ⟨x', by rwa [is_func_dom_eq]⟩ = ZFSet.Option.some (S := ⟦β₁⟧ᶻ) ⟨y', hy'⟩
          else zffalse
        else zffalse
      else ∅
    have hbodyF : ∀ {xy}, xy ∈ ⟦.pair α₂ β₂⟧ᶻ → bodyF xy ∈ 𝔹 := by
      intro xy hxy
      unfold bodyF
      rw [dif_pos hxy]
      dsimp
      split_ifs
      · apply ZFBool.mem_ofBool_𝔹
      · exact ZFBool.zffalse_mem_𝔹
      · exact ZFBool.zffalse_mem_𝔹
    have hEq :
        (λᶻ: ⟦α₂.pair β₂⟧ᶻ → 𝔹 | xy ↦ bodyF xy) =
          (λᶻ: ⟦α₂.pair β₂⟧ᶻ → 𝔹 | xy ↦ bodyG xy) := by
      simpa [bodyF, bodyG] using hFG_eq
    have eq' := (ZFSet.lambda_ext_iff
      (d := ⟦α₂.pair β₂⟧ᶻ) (r := 𝔹) (f₁ := bodyF) (f₂ := bodyG) hbodyF).mp hEq
    rw [lambda_eta hF, lambda_eta hG]
    let srcF : ZFSet → ZFSet := fun z =>
      if hz : z ∈ ⟦α₁⟧ᶻ then @ᶻF ⟨z, by rwa [is_func_dom_eq]⟩ else ∅
    let srcG : ZFSet → ZFSet := fun z =>
      if hz : z ∈ ⟦α₁⟧ᶻ then @ᶻG ⟨z, by rwa [is_func_dom_eq]⟩ else ∅
    have hsrcF : ∀ {z}, z ∈ ⟦α₁⟧ᶻ → srcF z ∈ ⟦β₁.option⟧ᶻ := by
      intro z hz
      unfold srcF
      rw [dif_pos hz]
      exact fapply_mem_range (is_func_is_pfunc hF) (by rwa [is_func_dom_eq])
    change
      (λᶻ: ⟦α₁⟧ᶻ → ⟦β₁.option⟧ᶻ | z ↦ srcF z) =
        (λᶻ: ⟦α₁⟧ᶻ → ⟦β₁.option⟧ᶻ | z ↦ srcG z)
    apply (ZFSet.lambda_ext_iff
      (d := ⟦α₁⟧ᶻ) (r := ⟦β₁.option⟧ᶻ)
      (f₁ := srcF) (f₂ := srcG) hsrcF).2
    intro z hz
    unfold srcF srcG
    rw [dif_pos hz, dif_pos hz]
    let x : ZFSet := (@ᶻζ₁ ⟨z, by rwa [is_func_dom_eq]⟩).val
    have hx : x ∈ ⟦α₂⟧ᶻ := by
      simpa [x] using fapply_mem_range (is_func_is_pfunc hζ₁) (by rwa [is_func_dom_eq])
    have hx_range : x ∈ ζ₁.Range := by
      simpa [x] using ZFSet.IsPFunc.mem_range_of_mem (is_func_is_pfunc hζ₁)
        (fapply.def (is_func_is_pfunc hζ₁) (by rwa [is_func_dom_eq]))
    let Fz : {u // u ∈ ⟦β₁.option⟧ᶻ} := @ᶻF ⟨z, by rwa [is_func_dom_eq]⟩
    let Gz : {u // u ∈ ⟦β₁.option⟧ᶻ} := @ᶻG ⟨z, by rwa [is_func_dom_eq]⟩
    obtain hFz_none | ⟨y, hFz_some⟩ := ZFSet.Option.casesOn Fz
    · have hGz_none : Gz = ZFSet.Option.none (S := ⟦β₁⟧ᶻ) := by
        by_contra hGz_none
        obtain ⟨y, hGz_some⟩ := Or.resolve_left (ZFSet.Option.casesOn Gz) hGz_none
        let y₂ : ZFSet := (@ᶻζ₂ ⟨y, by rw [is_func_dom_eq]; exact Subtype.property y⟩).val
        have hy₂ : y₂ ∈ ⟦β₂⟧ᶻ := by
          simpa [y₂] using fapply_mem_range (is_func_is_pfunc hζ₂) (by rwa [is_func_dom_eq])
        have hy₂_range : y₂ ∈ ζ₂.Range := by
          simpa [y₂] using ZFSet.IsPFunc.mem_range_of_mem (is_func_is_pfunc hζ₂)
            (fapply.def (is_func_is_pfunc hζ₂) (by rw [is_func_dom_eq]; exact Subtype.property y))
        have eq_xy := eq' (x.pair y₂) (by
          rw [ZFSet.pair_mem_prod]
          exact ⟨hx, hy₂⟩)
        unfold bodyF bodyG at eq_xy
        set z' := Classical.choose (mem_sep.mp hx_range).2 with hz'_def
        set y' := Classical.choose (mem_sep.mp hy₂_range).2 with hy'_def
        have hz'_dom : z' ∈ ζ₁.Dom := by
          simpa [hz'_def] using (Classical.choose_spec (mem_sep.mp hx_range).2).1
        have hy'_dom : y' ∈ ζ₂.Dom := by
          simpa [hy'_def] using (Classical.choose_spec (mem_sep.mp hy₂_range).2).1
        have hz'_mem : z' ∈ ⟦α₁⟧ᶻ := (mem_sep.mp hz'_dom).1
        have hy'_mem : y' ∈ ⟦β₁⟧ᶻ := (mem_sep.mp hy'_dom).1
        have hz'_pair : z'.pair x ∈ ζ₁ := by
          simpa [hz'_def] using (Classical.choose_spec (mem_sep.mp hx_range).2).2
        have hz_pair : z.pair x ∈ ζ₁ := by
          simpa [x] using fapply.def (is_func_is_pfunc hζ₁) (by rwa [is_func_dom_eq])
        have hy'_pair : y'.pair y₂ ∈ ζ₂ := by
          simpa [hy'_def] using (Classical.choose_spec (mem_sep.mp hy₂_range).2).2
        have hy_pair : y.val.pair y₂ ∈ ζ₂ := by
          simpa [y₂] using fapply.def (is_func_is_pfunc hζ₂) (by rw [is_func_dom_eq]; exact Subtype.property y)
        have hz'_eq : z' = z := hζ₁_inj z' z x hz'_mem hz hx hz'_pair hz_pair
        have hy'_eq : y' = y := hζ₂_inj y' y y₂ hy'_mem (Subtype.property y) hy₂ hy'_pair hy_pair
        have hz'_dom_F : z' ∈ F.Dom := by
          rwa [is_func_dom_eq]
        have hz'_dom_G : z' ∈ G.Dom := by
          rwa [is_func_dom_eq]
        have hargF :
            (⟨z', hz'_dom_F⟩ : {x // x ∈ F.Dom}) = ⟨z, by rwa [is_func_dom_eq]⟩ := by
          apply Subtype.ext
          exact hz'_eq
        have hargG :
            (⟨z', hz'_dom_G⟩ : {x // x ∈ G.Dom}) = ⟨z, by rwa [is_func_dom_eq]⟩ := by
          apply Subtype.ext
          exact hz'_eq
        have hF_eq : @ᶻF ⟨z', hz'_dom_F⟩ = Fz := by
          exact congrArg (fun a => @ᶻF a) hargF
        have hG_eq : @ᶻG ⟨z', hz'_dom_G⟩ = Gz := by
          exact congrArg (fun a => @ᶻG a) hargG
        have hy_some :
            (ZFSet.Option.some (S := ⟦β₁⟧ᶻ) ⟨y', hy'_mem⟩ : {x // x ∈ ⟦β₁.option⟧ᶻ}) =
              ZFSet.Option.some y := by
          rw [ZFSet.Option.some.injEq, Subtype.ext_iff]
          exact hy'_eq
        have eq_xy' :
            ZFSet.ZFBool.ofBool
              (decide (@ᶻF ⟨z', hz'_dom_F⟩ = ZFSet.Option.some (S := ⟦β₁⟧ᶻ) ⟨y', hy'_mem⟩)) =
              ZFSet.ZFBool.ofBool
                (decide (@ᶻG ⟨z', hz'_dom_G⟩ = ZFSet.Option.some (S := ⟦β₁⟧ᶻ) ⟨y', hy'_mem⟩)) := by
          simpa [hx, hy₂, ZFSet.π₁_pair, ZFSet.π₂_pair, hx_range, hy₂_range, hz'_def, hy'_def] using eq_xy
        have hF_false :
            ZFSet.ZFBool.ofBool
              (decide (@ᶻF ⟨z', hz'_dom_F⟩ = ZFSet.Option.some (S := ⟦β₁⟧ᶻ) ⟨y', hy'_mem⟩)) = zffalse := by
          conv_rhs => change (⊥ : ZFBool)
          rw [←Subtype.ext_iff, ZFBool.ofBool_decide_eq_false_iff, hF_eq, hy_some]
          intro hEq
          have : ZFSet.Option.none (S := ⟦β₁⟧ᶻ) = ZFSet.Option.some y := by
            rw [←hFz_none]
            exact hEq
          exact ZFSet.Option.some_ne_none y this.symm
        have hG_true :
            ZFSet.ZFBool.ofBool
              (decide (@ᶻG ⟨z', hz'_dom_G⟩ = ZFSet.Option.some (S := ⟦β₁⟧ᶻ) ⟨y', hy'_mem⟩)) = zftrue := by
          conv_rhs => change (⊤ : ZFBool)
          rw [←Subtype.ext_iff, ZFBool.ofBool_decide_eq_true_iff, hG_eq, hy_some, hGz_some]
        conv at eq_xy' =>
          rw [Subtype.ext_iff, hF_false, hG_true]
        exact ZFSet.zftrue_ne_zffalse eq_xy'.symm
      change (Fz : ZFSet) = Gz
      rw [hFz_none, hGz_none]
    · let y₂ : ZFSet := (@ᶻζ₂ ⟨y, by rw [is_func_dom_eq]; exact Subtype.property y⟩).val
      have hy₂ : y₂ ∈ ⟦β₂⟧ᶻ := by
        simpa [y₂] using fapply_mem_range (is_func_is_pfunc hζ₂) (by rwa [is_func_dom_eq])
      have hy₂_range : y₂ ∈ ζ₂.Range := by
        simpa [y₂] using ZFSet.IsPFunc.mem_range_of_mem (is_func_is_pfunc hζ₂)
          (fapply.def (is_func_is_pfunc hζ₂) (by rw [is_func_dom_eq]; exact Subtype.property y))
      have eq_xy := eq' (x.pair y₂) (by
        rw [ZFSet.pair_mem_prod]
        exact ⟨hx, hy₂⟩)
      unfold bodyF bodyG at eq_xy
      set z' := Classical.choose (mem_sep.mp hx_range).2 with hz'_def
      set y' := Classical.choose (mem_sep.mp hy₂_range).2 with hy'_def
      have hz'_dom : z' ∈ ζ₁.Dom := by
        simpa [hz'_def] using (Classical.choose_spec (mem_sep.mp hx_range).2).1
      have hy'_dom : y' ∈ ζ₂.Dom := by
        simpa [hy'_def] using (Classical.choose_spec (mem_sep.mp hy₂_range).2).1
      have hz'_mem : z' ∈ ⟦α₁⟧ᶻ := (mem_sep.mp hz'_dom).1
      have hy'_mem : y' ∈ ⟦β₁⟧ᶻ := (mem_sep.mp hy'_dom).1
      have hz'_pair : z'.pair x ∈ ζ₁ := by
        simpa [hz'_def] using (Classical.choose_spec (mem_sep.mp hx_range).2).2
      have hz_pair : z.pair x ∈ ζ₁ := by
        simpa [x] using fapply.def (is_func_is_pfunc hζ₁) (by rwa [is_func_dom_eq])
      have hy'_pair : y'.pair y₂ ∈ ζ₂ := by
        simpa [hy'_def] using (Classical.choose_spec (mem_sep.mp hy₂_range).2).2
      have hy_pair : y.val.pair y₂ ∈ ζ₂ := by
        simpa [y₂] using fapply.def (is_func_is_pfunc hζ₂) (by rw [is_func_dom_eq]; exact Subtype.property y)
      have hz'_eq : z' = z := hζ₁_inj z' z x hz'_mem hz hx hz'_pair hz_pair
      have hy'_eq : y' = y := hζ₂_inj y' y y₂ hy'_mem (Subtype.property y) hy₂ hy'_pair hy_pair
      have hz'_dom_F : z' ∈ F.Dom := by
        rwa [is_func_dom_eq]
      have hz'_dom_G : z' ∈ G.Dom := by
        rwa [is_func_dom_eq]
      have hargF :
          (⟨z', hz'_dom_F⟩ : {x // x ∈ F.Dom}) = ⟨z, by rwa [is_func_dom_eq]⟩ := by
        apply Subtype.ext
        exact hz'_eq
      have hargG :
          (⟨z', hz'_dom_G⟩ : {x // x ∈ G.Dom}) = ⟨z, by rwa [is_func_dom_eq]⟩ := by
        apply Subtype.ext
        exact hz'_eq
      have hF_eq : @ᶻF ⟨z', hz'_dom_F⟩ = Fz := by
        exact congrArg (fun a => @ᶻF a) hargF
      have hG_eq : @ᶻG ⟨z', hz'_dom_G⟩ = Gz := by
        exact congrArg (fun a => @ᶻG a) hargG
      have hy_some :
          (ZFSet.Option.some (S := ⟦β₁⟧ᶻ) ⟨y', hy'_mem⟩ : {x // x ∈ ⟦β₁.option⟧ᶻ}) =
            ZFSet.Option.some y := by
        rw [ZFSet.Option.some.injEq, Subtype.ext_iff]
        exact hy'_eq
      have eq_xy' :
          ZFSet.ZFBool.ofBool
            (decide (@ᶻF ⟨z', hz'_dom_F⟩ = ZFSet.Option.some (S := ⟦β₁⟧ᶻ) ⟨y', hy'_mem⟩)) =
            ZFSet.ZFBool.ofBool
              (decide (@ᶻG ⟨z', hz'_dom_G⟩ = ZFSet.Option.some (S := ⟦β₁⟧ᶻ) ⟨y', hy'_mem⟩)) := by
        simpa [hx, hy₂, ZFSet.π₁_pair, ZFSet.π₂_pair, hx_range, hy₂_range, hz'_def, hy'_def] using eq_xy
      have hF_true :
          ZFSet.ZFBool.ofBool
            (decide (@ᶻF ⟨z', hz'_dom_F⟩ = ZFSet.Option.some (S := ⟦β₁⟧ᶻ) ⟨y', hy'_mem⟩)) = zftrue := by
        conv_rhs => change (⊤ : ZFBool)
        rw [←Subtype.ext_iff, ZFBool.ofBool_decide_eq_true_iff, hF_eq, hy_some, hFz_some]
      have hGz_some : Gz = ZFSet.Option.some (S := ⟦β₁⟧ᶻ) y := by
        have hG_true :
            ZFSet.ZFBool.ofBool
              (decide (@ᶻG ⟨z', hz'_dom_G⟩ = ZFSet.Option.some (S := ⟦β₁⟧ᶻ) ⟨y', hy'_mem⟩)) = zftrue := by
          conv_rhs => change (⊤ : ZFBool)
          rw [←eq_xy', hF_true]
          rfl
        conv at hG_true =>
          conv => enter [2]; change (⊤ : ZFBool)
          rw [←Subtype.ext_iff, ZFBool.ofBool_decide_eq_true_iff, hG_eq, hy_some]
        exact hG_true
      change (Fz : ZFSet) = Gz
      rw [hFz_some, hGz_some]
  change R.IsInjective hR
  exact hR_inj

set_option maxHeartbeats 400000 in
theorem castZF_fun_injective {α₁ α₂ β₁ β₂ : SMTType} {ζ₁ ζ₂ : ZFSet}
    {hζ₁ : IsFunc ⟦α₁⟧ᶻ ⟦α₂⟧ᶻ ζ₁} {hζ₂ : IsFunc ⟦β₁⟧ᶻ ⟦β₂⟧ᶻ ζ₂}
    (hζ₁_inj : ζ₁.IsInjective hζ₁) (hζ₂_inj : ζ₂.IsInjective hζ₂) :
    ((castZF_fun ⟨ζ₁, hζ₁⟩ ⟨ζ₂, hζ₂⟩).1).IsInjective
      ((castZF_fun ⟨ζ₁, hζ₁⟩ ⟨ζ₂, hζ₂⟩).2) := by
  classical
  let ff : ZFSet :=
    λᶻ: ⟦.fun α₁ β₁⟧ᶻ → ⟦.fun α₂ β₂⟧ᶻ
      | F ↦ if hF : IsFunc ⟦α₁⟧ᶻ ⟦β₁⟧ᶻ F then
               λᶻ: ⟦α₂⟧ᶻ → ⟦β₂⟧ᶻ
                 | x ↦ if hx : x ∈ ζ₁.Range then
                         let x' := Classical.choose (mem_sep.mp hx).2
                         have hx' : x' ∈ ⟦α₁⟧ᶻ := by
                           have ⟨dom, _⟩ := Classical.choose_spec (mem_sep.mp hx).2
                           conv at dom =>
                             enter [1]
                             rw [is_func_dom_eq]
                           exact dom
                       let y := fapply F (is_func_is_pfunc hF) ⟨x', by rwa [is_func_dom_eq]⟩
                       @ᶻζ₂ ⟨y, by rw [is_func_dom_eq]; exact Subtype.property y⟩
                     else
                        β₂.defaultZFSet
             else ∅
  have hff : IsFunc ⟦.fun α₁ β₁⟧ᶻ ⟦.fun α₂ β₂⟧ᶻ ff := by
    apply lambda_isFunc
    intro F hF
    rw [mem_funs] at hF
    rw [dite_cond_eq_true (eq_true hF), mem_funs]
    apply lambda_isFunc
    intro x hx
    split_ifs with hx_range
    · apply fapply_mem_range
    · exact SMTType.mem_toZFSet_of_defaultZFSet
  have hff_inj : ff.IsInjective hff := by
    intro F G H hF hG hH FH GH
    rw [mem_funs] at hF hG hH
    rw [lambda_spec] at FH GH
    rw [dite_cond_eq_true (eq_true hF)] at FH
    rw [dite_cond_eq_true (eq_true hG)] at GH
    obtain ⟨-, -, rfl⟩ := FH
    obtain ⟨-, -, eq⟩ := GH
    let bodyF : ZFSet → ZFSet := fun x =>
      if hx : x ∈ ζ₁.Range then
        let x' := Classical.choose (mem_sep.mp hx).2
        have hx' : x' ∈ ⟦α₁⟧ᶻ := by
          have ⟨dom, _⟩ := Classical.choose_spec (mem_sep.mp hx).2
          conv at dom =>
            enter [1]
            rw [is_func_dom_eq]
          exact dom
        let y := fapply F (is_func_is_pfunc hF) ⟨x', by rwa [is_func_dom_eq]⟩
        @ᶻζ₂ ⟨y, by rw [is_func_dom_eq]; exact Subtype.property y⟩
      else
        β₂.defaultZFSet
    let bodyG : ZFSet → ZFSet := fun x =>
      if hx : x ∈ ζ₁.Range then
        let x' := Classical.choose (mem_sep.mp hx).2
        have hx' : x' ∈ ⟦α₁⟧ᶻ := by
          have ⟨dom, _⟩ := Classical.choose_spec (mem_sep.mp hx).2
          conv at dom =>
            enter [1]
            rw [is_func_dom_eq]
          exact dom
        let y := fapply G (is_func_is_pfunc hG) ⟨x', by rwa [is_func_dom_eq]⟩
        @ᶻζ₂ ⟨y, by rw [is_func_dom_eq]; exact Subtype.property y⟩
      else
        β₂.defaultZFSet
    have hbodyF : ∀ {x}, x ∈ ⟦α₂⟧ᶻ → bodyF x ∈ ⟦β₂⟧ᶻ := by
      intro x hx
      by_cases hx_range : x ∈ ζ₁.Range
      · unfold bodyF
        rw [dif_pos hx_range]
        dsimp
        exact fapply_mem_range (is_func_is_pfunc hζ₂) (by
          rw [is_func_dom_eq]
          exact Subtype.property _)
      · unfold bodyF
        rw [dif_neg hx_range]
        exact SMTType.mem_toZFSet_of_defaultZFSet
    have hEq : (λᶻ: ⟦α₂⟧ᶻ → ⟦β₂⟧ᶻ | x ↦ bodyF x) =
        (λᶻ: ⟦α₂⟧ᶻ → ⟦β₂⟧ᶻ | x ↦ bodyG x) := by
      simpa [bodyF, bodyG] using eq
    have eq' := (ZFSet.lambda_ext_iff
      (d := ⟦α₂⟧ᶻ) (r := ⟦β₂⟧ᶻ) (f₁ := bodyF) (f₂ := bodyG) hbodyF).mp hEq
    rw [lambda_eta hF, lambda_eta hG]
    let srcF : ZFSet → ZFSet := fun z =>
      if hz : z ∈ ⟦α₁⟧ᶻ then @ᶻF ⟨z, by rwa [is_func_dom_eq]⟩ else ∅
    let srcG : ZFSet → ZFSet := fun z =>
      if hz : z ∈ ⟦α₁⟧ᶻ then @ᶻG ⟨z, by rwa [is_func_dom_eq]⟩ else ∅
    have hsrcF : ∀ {z}, z ∈ ⟦α₁⟧ᶻ → srcF z ∈ ⟦β₁⟧ᶻ := by
      intro z hz
      unfold srcF
      rw [dif_pos hz]
      exact fapply_mem_range (is_func_is_pfunc hF) (by rwa [is_func_dom_eq])
    change (λᶻ: ⟦α₁⟧ᶻ → ⟦β₁⟧ᶻ | z ↦ srcF z) = (λᶻ: ⟦α₁⟧ᶻ → ⟦β₁⟧ᶻ | z ↦ srcG z)
    have hsrcEq : (λᶻ: ⟦α₁⟧ᶻ → ⟦β₁⟧ᶻ | z ↦ srcF z) =
        (λᶻ: ⟦α₁⟧ᶻ → ⟦β₁⟧ᶻ | z ↦ srcG z) := by
      apply (ZFSet.lambda_ext_iff
        (d := ⟦α₁⟧ᶻ) (r := ⟦β₁⟧ᶻ)
        (f₁ := srcF) (f₂ := srcG) hsrcF).2
      intro z hz
      unfold srcF srcG
      rw [dif_pos hz, dif_pos hz]
      let x : ZFSet := (@ᶻζ₁ ⟨z, by rwa [is_func_dom_eq]⟩).val
      have hx : x ∈ ⟦α₂⟧ᶻ := by
        simpa [x] using fapply_mem_range (is_func_is_pfunc hζ₁) (by rwa [is_func_dom_eq])
      have hx_range : x ∈ ζ₁.Range := by
        simpa [x] using ZFSet.IsPFunc.mem_range_of_mem (is_func_is_pfunc hζ₁)
          (fapply.def (is_func_is_pfunc hζ₁) (by rwa [is_func_dom_eq]))
      specialize eq' x hx
      unfold bodyF bodyG at eq'
      rw [dif_pos hx_range, dif_pos hx_range] at eq'
      dsimp at eq'
      set z' := Classical.choose (mem_sep.mp hx_range).2 with hz'_def
      have hz'_dom : z' ∈ ζ₁.Dom := by
        simpa [hz'_def] using (Classical.choose_spec (mem_sep.mp hx_range).2).1
      have hz'_mem : z' ∈ ⟦α₁⟧ᶻ := by
        exact (mem_sep.mp hz'_dom).1
      have hz'_pair : z'.pair x ∈ ζ₁ := by
        simpa [hz'_def] using (Classical.choose_spec (mem_sep.mp hx_range).2).2
      have hz_pair : z.pair x ∈ ζ₁ := by
        simpa [x] using fapply.def (is_func_is_pfunc hζ₁) (by rwa [is_func_dom_eq])
      have hz'_eq : z' = z := hζ₁_inj z' z x hz'_mem hz hx hz'_pair hz_pair
      have hz'_dom_F : z' ∈ F.Dom := by
        rwa [is_func_dom_eq]
      have hz'_dom_G : z' ∈ G.Dom := by
        rwa [is_func_dom_eq]
      have hargF :
          (⟨z', hz'_dom_F⟩ : {x // x ∈ F.Dom}) = ⟨z, by rwa [is_func_dom_eq]⟩ := by
        apply Subtype.ext
        exact hz'_eq
      have hargG :
          (⟨z', hz'_dom_G⟩ : {x // x ∈ G.Dom}) = ⟨z, by rwa [is_func_dom_eq]⟩ := by
        apply Subtype.ext
        exact hz'_eq
      have hF_eq : @ᶻF ⟨z', hz'_dom_F⟩ = @ᶻF ⟨z, by rwa [is_func_dom_eq]⟩ :=
        congrArg (fun a => @ᶻF a) hargF
      have hG_eq : @ᶻG ⟨z', hz'_dom_G⟩ = @ᶻG ⟨z, by rwa [is_func_dom_eq]⟩ :=
        congrArg (fun a => @ᶻG a) hargG
      have hFz'_dom_ζ₂ : ↑(@ᶻF ⟨z', hz'_dom_F⟩) ∈ ζ₂.Dom := by
        rw [is_func_dom_eq]
        exact Subtype.property _
      have hGz'_dom_ζ₂ : ↑(@ᶻG ⟨z', hz'_dom_G⟩) ∈ ζ₂.Dom := by
        rw [is_func_dom_eq]
        exact Subtype.property _
      have hFz_dom_ζ₂ : ↑(@ᶻF ⟨z, by rwa [is_func_dom_eq]⟩) ∈ ζ₂.Dom := by
        rw [is_func_dom_eq]
        exact Subtype.property _
      have hGz_dom_ζ₂ : ↑(@ᶻG ⟨z, by rwa [is_func_dom_eq]⟩) ∈ ζ₂.Dom := by
        rw [is_func_dom_eq]
        exact Subtype.property _
      have eqζ' :
          @ᶻζ₂ ⟨↑(@ᶻF ⟨z', hz'_dom_F⟩), hFz'_dom_ζ₂⟩ =
            @ᶻζ₂ ⟨↑(@ᶻG ⟨z', hz'_dom_G⟩), hGz'_dom_ζ₂⟩ := by
        apply Subtype.ext
        simpa [hz'_def] using eq'
      have hζF_eq :
          @ᶻζ₂ ⟨↑(@ᶻF ⟨z', hz'_dom_F⟩), hFz'_dom_ζ₂⟩ =
            @ᶻζ₂ ⟨↑(@ᶻF ⟨z, by rwa [is_func_dom_eq]⟩), hFz_dom_ζ₂⟩ := by
        have hinF :
            (⟨↑(@ᶻF ⟨z', hz'_dom_F⟩), hFz'_dom_ζ₂⟩ : {x // x ∈ ζ₂.Dom}) =
              ⟨↑(@ᶻF ⟨z, by rwa [is_func_dom_eq]⟩), hFz_dom_ζ₂⟩ := by
          apply Subtype.ext
          exact congrArg (fun b : ⟦β₁⟧ᶻ => (b : ZFSet)) hF_eq
        exact congrArg (fun a => @ᶻζ₂ a) hinF
      have hζG_eq :
          @ᶻζ₂ ⟨↑(@ᶻG ⟨z', hz'_dom_G⟩), hGz'_dom_ζ₂⟩ =
            @ᶻζ₂ ⟨↑(@ᶻG ⟨z, by rwa [is_func_dom_eq]⟩), hGz_dom_ζ₂⟩ := by
        have hinG :
            (⟨↑(@ᶻG ⟨z', hz'_dom_G⟩), hGz'_dom_ζ₂⟩ : {x // x ∈ ζ₂.Dom}) =
              ⟨↑(@ᶻG ⟨z, by rwa [is_func_dom_eq]⟩), hGz_dom_ζ₂⟩ := by
          apply Subtype.ext
          exact congrArg (fun b : ⟦β₁⟧ᶻ => (b : ZFSet)) hG_eq
        exact congrArg (fun a => @ᶻζ₂ a) hinG
      have eqζ :
          @ᶻζ₂ ⟨↑(@ᶻF ⟨z, by rwa [is_func_dom_eq]⟩), hFz_dom_ζ₂⟩ =
            @ᶻζ₂ ⟨↑(@ᶻG ⟨z, by rwa [is_func_dom_eq]⟩), hGz_dom_ζ₂⟩ :=
        hζF_eq.symm.trans (eqζ'.trans hζG_eq)
      have hargEq := IsInjective.apply_inj hζ₂ hζ₂_inj eqζ
      simpa using hargEq
    exact hsrcEq
  change ff.IsInjective hff
  exact hff_inj

set_option maxHeartbeats 800000 in
theorem castZF_of_path_injective {α β : SMTType} (p : α ⇝ β) :
    ((castZF_of_path p).1).IsInjective ((castZF_of_path p).2) := by
  induction p with
  | refl =>
      intro x y z hx hy hz hxz hyz
      rw [castZF_of_path] at hxz hyz
      rw [ZFSet.pair_mem_Id_iff hx] at hxz
      rw [ZFSet.pair_mem_Id_iff hy] at hyz
      subst hxz hyz
      rfl
  | chpred p ih =>
      simpa [castZF_of_path] using castZF_chpred_injective (cast := (castZF_of_path p).1)
        (hcast := (castZF_of_path p).2) ih
  | graph pα pβ ihα ihβ =>
      simpa [castZF_of_path] using castZF_graph_injective
        (ζ₁ := (castZF_of_path pα).1) (ζ₂ := (castZF_of_path pβ).1)
        (hζ₁ := (castZF_of_path pα).2) (hζ₂ := (castZF_of_path pβ).2)
        ihα ihβ
  | «fun» _ pα pβ ihα ihβ =>
      simpa [castZF_of_path] using castZF_fun_injective
        (ζ₁ := (castZF_of_path pα).1) (ζ₂ := (castZF_of_path pβ).1)
        (hζ₁ := (castZF_of_path pα).2) (hζ₂ := (castZF_of_path pβ).2)
        ihα ihβ
  | opt p ih =>
      simpa [castZF_of_path] using castZF_option_injective
        (ζ := (castZF_of_path p).1) (hζ := (castZF_of_path p).2) ih
  | pair pα pβ ihα ihβ =>
      simpa [castZF_of_path] using castZF_pair_injective
        (ζ₁ := (castZF_of_path pα).1) (ζ₂ := (castZF_of_path pβ).1)
        (hζ₁ := (castZF_of_path pα).2) (hζ₂ := (castZF_of_path pβ).2)
        ihα ihβ

-- @[push_cast]
-- theorem CastPath.push_cast_left {α β γ : SMTType} {p : CastPath α β} (h : α = γ) :
--     h ▸ p.funBool = (h ▸ p).funBool := by
--   cases h
--   rfl

theorem castZF_of_path_id {α : SMTType} :
    castZF_of_path (@castPath.reflexive α) = ⟨𝟙⟦α⟧ᶻ, Id.IsFunc⟩ := by
  induction α with
  | bool => rfl
  | int => rfl
  | unit => rfl
  | pair α β α_ih β_ih =>
    rw [castPath.reflexive, castZF_of_path, castZF_pair]
    congr
    ext1 xy
    rw [mem_Id_iff]
    iff_intro hxy hxy
    · rw [α_ih, β_ih, mem_fprod] at hxy
      obtain ⟨a, b, ha, hb, rfl⟩ := hxy
      exists a.pair b, ?_
      · rw [pair_mem_prod]
        exact ⟨ha, hb⟩
      · simp only [fapply_Id ha, fapply_Id hb]
    · obtain ⟨x, hx, rfl⟩ := hxy
      rw [mem_fprod, α_ih, β_ih]
      have hx' := hx
      rw [pair_eta hx, pair_mem_prod] at hx
      exists x.π₁, x.π₂, hx.1, hx.2
      simp only [fapply_Id hx.1, fapply_Id hx.2, ←pair_eta hx']
  | «fun» α β α_ih β_ih =>
    cases β with
    | bool =>
      rw [castPath.reflexive, castZF_of_path, α_ih, castZF_chpred]
      congr
      ext1 f
      rw [mem_Id_iff]
      iff_intro hf hf
      · simp only [range_Id, mem_sep, subset_refl, subset_of_empty, mem_lambda, ↓existsAndEq, mem_funs, and_true] at hf
        obtain ⟨f, rfl, hf, hf'⟩ := hf
        rw [dif_pos hf] at hf' ⊢
        exists f, mem_funs.mpr hf
        rw [pair_inj, eq_self, true_and]
        conv_rhs => rw [lambda_eta hf]
        rw [lambda_ext_iff]
        · intro x hx
          rw [dif_pos (by rwa [range_Id]), dif_pos hx]
          congr
          generalize_proofs ch
          obtain ⟨⟨_, _⟩, hy⟩ := Classical.choose_spec ch
          rw [pair_mem_Id_iff] at hy <;> assumption
        · intro x hx
          rw [dif_pos (by rwa [range_Id])]
          apply fapply_mem_range
      · obtain ⟨x, hx, rfl⟩ := hf
        rw [lambda_spec]
        refine ⟨hx, hx, ?_⟩
        rw [mem_funs] at hx
        rw [dif_pos hx]
        conv_lhs => rw [lambda_eta hx]
        rw [lambda_ext_iff]
        · intro z hz
          rw [dif_pos hz, dif_pos (by rwa [range_Id])]
          dsimp
          congr
          generalize_proofs _ ch
          obtain ⟨memDom, hy⟩ := Classical.choose_spec ch
          rw [mem_sep] at memDom
          replace memDom := memDom.1
          symm
          rw [pair_mem_Id_iff] at hy <;> assumption
        · intro z hz
          rw [dif_pos hz]
          apply fapply_mem_range
    | int | unit =>
      rw [castPath.reflexive, castZF_of_path, α_ih, castZF_fun]
      congr
      ext1 f
      rw [mem_Id_iff]
      iff_intro hf hf
      · simp only [range_Id, mem_sep, mem_lambda, ↓existsAndEq, mem_funs, and_true] at hf
        obtain ⟨f, rfl, hf, hf'⟩ := hf
        rw [dif_pos hf] at hf' ⊢
        exists f, mem_funs.mpr hf
        rw [pair_inj, eq_self, true_and]
        conv_rhs => rw [lambda_eta hf]
        rw [lambda_ext_iff]
        · intro x hx
          rw [dif_pos (by rwa [range_Id]), dif_pos hx, castZF_of_path, fapply_Id (by apply fapply_mem_range)]
          congr 2
          generalize_proofs _ _ ch₁ _ ch₂
          obtain ⟨⟨_, _⟩, hch₁⟩ := Classical.choose_spec ch₁
          obtain ⟨_, hch₂⟩ := Classical.choose_spec ch₂
          rw [pair_mem_Id_iff ‹_›] at hch₁
          simp only [hch₁]
          exact fapply.of_pair (is_func_is_pfunc hf) hch₂ |> Subtype.ext_iff.mp
        · intro x hx
          rw [dif_pos (by rwa [range_Id])]
          apply fapply_mem_range
      · obtain ⟨x, hx, rfl⟩ := hf
        rw [lambda_spec]
        refine ⟨hx, hx, ?_⟩
        rw [mem_funs] at hx
        rw [dif_pos hx]
        conv_lhs => rw [lambda_eta hx]
        rw [lambda_ext_iff]
        · intro z hz
          rw [dif_pos hz, dif_pos (by rwa [range_Id])]
          dsimp
          rw [castZF_of_path, fapply_Id (by apply fapply_mem_range)]
          congr
          generalize_proofs _ _ _ _ ch
          obtain ⟨memDom, hy⟩ := Classical.choose_spec ch
          rw [mem_sep] at memDom
          replace memDom := memDom.1
          rw [pair_mem_Id_iff memDom] at hy
          simp only [hy]
        · intro z hz
          rw [dif_pos hz]
          apply fapply_mem_range
    | _ =>
      rw [castPath.reflexive, castZF_of_path, α_ih, β_ih, castZF_fun]
      congr
      ext1 f
      rw [mem_Id_iff]
      iff_intro hf hf
      · simp only [range_Id, mem_sep, mem_lambda, ↓existsAndEq, mem_funs, and_true] at hf
        obtain ⟨f, rfl, hf, hf'⟩ := hf
        rw [dif_pos hf] at hf' ⊢
        exists f, mem_funs.mpr hf
        rw [pair_inj, eq_self, true_and]
        conv_rhs => rw [lambda_eta hf]
        rw [lambda_ext_iff]
        · intro x hx
          rw [dif_pos (by rwa [range_Id]), dif_pos hx, fapply_Id (by apply fapply_mem_range)]
          congr 1
          generalize_proofs _ _ ch₁
          obtain ⟨⟨_, _⟩, hch₁⟩ := Classical.choose_spec ch₁
          rw [pair_mem_Id_iff ‹_›] at hch₁
          simp only [hch₁]
        · intro x hx
          rw [dif_pos (by rwa [range_Id])]
          apply fapply_mem_range
      · obtain ⟨x, hx, rfl⟩ := hf
        rw [lambda_spec]
        refine ⟨hx, hx, ?_⟩
        rw [mem_funs] at hx
        rw [dif_pos hx]
        conv_lhs => rw [lambda_eta hx]
        rw [lambda_ext_iff]
        · intro z hz
          rw [dif_pos hz, dif_pos (by rwa [range_Id])]
          dsimp
          rw [fapply_Id (by apply fapply_mem_range)]
          congr 1
          generalize_proofs _ _ _ _ ch
          obtain ⟨memDom, hy⟩ := Classical.choose_spec ch
          rw [mem_sep] at memDom
          replace memDom := memDom.1
          rw [pair_mem_Id_iff memDom] at hy
          simp only [hy]
        · intro z hz
          rw [dif_pos hz]
          apply fapply_mem_range
  | option τ ih =>
    rw [castPath.reflexive, castZF_of_path, ih, castZF_option]
    congr
    ext1 x
    rw [mem_Id_iff]
    iff_intro hx hx
    · simp only [mem_lambda, ↓existsAndEq, and_true] at hx
      obtain ⟨x, rfl, hx, hx'⟩ := hx
      rw [dif_pos hx]
      exists x, hx
      rw [pair_inj, eq_self, true_and]
      split_ifs with is_none
      · rw [is_none]
      · generalize_proofs _ _ ch
        rw [fapply_Id (SetLike.coe_mem (Classical.choose ch))]
        symm
        exact Classical.choose_spec ch
    · obtain ⟨x, hx, rfl⟩ := hx
      rw [lambda_spec]
      refine ⟨hx, hx, ?_⟩
      rw [dif_pos hx]
      split_ifs with is_none
      · rw [is_none]
      · dsimp
        rw [fapply_Id (SetLike.coe_mem _)]
        generalize_proofs ch
        exact Classical.choose_spec ch

open Classical in
noncomputable def castZF.{u} (α β : SMTType) (cast? : α ⊑ β) :
  {f : ZFSet.{u} // ⟦α⟧ᶻ.IsFunc ⟦β⟧ᶻ f} := castZF_of_path cast?.toCastPath
