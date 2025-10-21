import SMT.Semantics
import Extra.Utils
import Mathlib.Tactic.LiftLets

open Classical SMT PHOAS ZFSet

private lemma foldl_endo_mem {α} {xs : List α} {f : ZFSet → α → ZFSet} {d : ZFSet} {B : ZFSet} (hd : d ∈ B) (h : ∀ x y, f x y ∈ B) :
  xs.foldl f d ∈ B := by
  induction xs generalizing d with
  | nil => exact hd
  | cons x xs ih => exact ih (h d x)

private lemma foldl_attach_zfand_toBool {xs : List ZFBool} {d : ZFBool} {f : ZFBool → ZFBool} :
  (xs.attach.foldl (λ acc ⟨x, hx⟩ => acc ⋀ (f x)) d).toBool = xs.attach.foldl (λ (acc : Bool) ⟨x, hx⟩ => acc && (f x).toBool) d.toBool := by
  induction xs generalizing d with
  | nil => simp
  | cons x xs ih =>
    rw [List.attach_cons, List.foldl_cons, List.foldl_cons]
    dsimp at ih ⊢
    specialize @ih (d ⋀ f x)
    rw [← ZFBool.toBool_and, List.foldl_map, List.foldl_map]
    exact ih

private lemma foldl_zfor_toBool {xs : List ZFBool} {d : ZFBool} :
  (xs.foldl (λ acc x => acc ⋁ x) d).toBool = xs.foldl (λ (acc : Bool) x => acc ∨ x.toBool) d.toBool := by
  induction xs generalizing d with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, List.foldl_cons]
    rw [@ih (d ⋁ x)]
    congr
    rw [ZFBool.toBool_or, Bool.or_eq_decide]

noncomputable def denote.distinct_alt_def {Γ} {ts : List <| PHOAS.Term ZFSet} (h : Γ ⊢ .distinct ts : .bool) : {x // x ∈ ZFSet.𝔹} :=
  let σ := choose (Typing.distinctE h).2.2
  let hts := choose_spec (Typing.distinctE h).2.2
  ⟨ts.upperDiag.attach.foldl (λ acc ⟨⟨x, y⟩, hxy⟩ =>
    let typ : Γ ⊢ x : σ ∧ Γ ⊢ y : σ := And.casesOn (List.upperDiag_mem hxy) λ hx' hy' => ⟨hts x hx', hts y hy'⟩
    let Z := overloadBinOp (A := σ.toZFSet) (·.val) (λ p => if p then ZFSet.ZFBool.true else ZFSet.ZFBool.false) ⊥ (· = ·) (x := ⟦x⟧ˢ ⟨Γ, σ, typ.1⟩) (y := ⟦y⟧ˢ ⟨Γ, σ, typ.2⟩)
    acc ⋀ᶻ (¬ᶻ Z)) ZFSet.zftrue, by
      dsimp [SMTType.toZFSet]
      apply foldl_endo_mem ZFBool.zftrue_mem_𝔹
      rintro acc ⟨⟨x, y⟩, hxy⟩
      apply Subtype.property⟩

set_option pp.proofs true in
/--
The denotation of `distinct [t₁, ..., tₙ]` is equivalent to `⟦t₁⟧ˢ ≠ ⟦t₂⟧ˢ ∧ ... ∧ ⟦tₙ₋₁⟧ˢ ≠ ⟦tₙ⟧ˢ`.
-/
theorem denote_distinct_alt_def_correct {Γ} {ts} {h : Γ ⊢ .distinct ts : .bool} : ⟦.distinct ts⟧ˢ ⟨Γ, .bool, h⟩ = denote.distinct_alt_def h := by
  induction ts with
  | nil => nomatch Typing.distinctE h
  | cons t ts ih =>
    letI D₁ : ZFBool := ⟦PHOAS.Term.distinct (t :: ts)⟧ˢ ⟨Γ, ⟨SMTType.bool, h⟩⟩
    letI D₂ : ZFBool := denote.distinct_alt_def h
    refold_let D₁ D₂
    cases hD₁ : D₁ using ZFBool.casesOn with
    | false =>
      unfold D₁ at hD₁
      rw [denote, denote_aux.distinct, Subtype.coe_eta, ZFBool.ofBool_decide_eq_false_iff] at hD₁
      push_neg at hD₁
      generalize_proofs typ_ts hσ h_isfun at hD₁

      by_contra contr
      replace contr : D₂ = ⊤ :=  ZFBool.not_bot_iff_top.mp λ h => contr h.symm
      unfold D₂ denote.distinct_alt_def at contr
      lift_lets at contr
      extract_lets σ at contr
      letI hts := choose_spec (denote.distinct_alt_def._proof_1 h)
      sorry
    | true => sorry
