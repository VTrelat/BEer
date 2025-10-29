import Encoder.Loosening
import SMT.Reasoning.Defs
import Std.Tactic.Do

open Std.Do SMT ZFSet
/-
NOTE: Specification is in two parts:
-	a semantic cast on ZF-denotations (what the cast means), and
-	a monadic spec for `loosen` (what the procedure must return so that the meaning is enforced).
-/
open Classical in
noncomputable def castZF.{u} (α β : SMTType) (cast? : α ⊑ β) : {f : ZFSet.{u} // IsFunc ⟦α⟧ᶻ ⟦β⟧ᶻ f} :=
  match α with
  | .unit => match β with | .unit => ⟨𝟙{∅}, Id.IsFunc⟩
  | .int => match β with | .int => ⟨𝟙Int, Id.IsFunc⟩
  | .bool => match β with | .bool => ⟨𝟙𝔹, Id.IsFunc⟩
  | .pair α₁ α₂ =>
    match β with
    | .pair β₁ β₂ =>
      have ⟨h₁, h₂⟩ : α₁ ⊑ β₁ ∧ α₂ ⊑ β₂ := Bool.and_eq_true_iff.mp cast?
      let ⟨f₁, hf₁⟩ := castZF α₁ β₁ h₁
      let ⟨f₂, hf₂⟩ := castZF α₂ β₂ h₂
      ⟨fprod f₁ f₂, fprod_is_func hf₁ hf₂⟩
  | .option α =>
    match β with
    | .option β =>
      have h : α ⊑ β := cast?
      let ⟨f, hf⟩ := castZF α β h
      let fopt : ZFSet.{u} :=
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
      ⟨fopt, by
        apply ZFSet.lambda_isFunc
        intro x hx
        rw [dite_cond_eq_true (eq_true hx)]
        split_ifs with is_none <;> apply SetLike.coe_mem
      ⟩
  | .fun τ (.option σ) =>
    match β with
    | .fun (.pair τ' σ') .bool => sorry
    | .fun τ' (.option σ') => sorry
    | _ => sorry
  | .fun (.pair τ σ) .bool =>
    match β with
    | .fun (.pair τ' σ') .bool => sorry
    | _ => sorry
  | .fun α .bool =>
    match β with
    | .fun α' .bool => sorry
    | _ => sorry
