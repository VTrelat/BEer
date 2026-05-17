import SMT.Semantics
import Mathlib.Data.List.FinRange

open Classical SMT SMT.PHOAS ZFSet

namespace SMT

/-- `overloadBinOp_𝔹` applied to two genuine booleans is just the operation. -/
private theorem overloadBinOp_𝔹_val (op : ZFBool → ZFBool → ZFBool) (a b : ZFBool) :
    overloadBinOp_𝔹 op a.val b.val = (op a b).val := by
  unfold overloadBinOp_𝔹 overloadBinOp
  rw [dif_pos ⟨a.2, b.2⟩]
  rfl

/-- A `ZFBool` is `⊤` iff it converts to `true`. -/
private theorem zfbool_eq_top_iff (p : ZFBool) : p = ⊤ ↔ p.toBool = true := by
  constructor
  · rintro rfl; exact ZFBool.toBool_true
  · intro h
    conv_lhs => rw [← ZFBool.of_Bool_toBool p]
    rw [h]; rfl

/-- `⋀` is `⊤` iff both conjuncts are. -/
private theorem zfbool_and_eq_top_iff (a b : ZFBool) : a ⋀ b = ⊤ ↔ a = ⊤ ∧ b = ⊤ := by
  rw [zfbool_eq_top_iff, ZFBool.toBool_and, Bool.and_eq_true, zfbool_eq_top_iff,
    zfbool_eq_top_iff]

/-- Pairwise distinctness of the denotations of `ts` — the property that the
SMT term `distinct ts` is intended to express. -/
def denote.distinct_alt_def {n : ℕ} (ts : Fin n → PHOAS.Term Dom) : Prop :=
  ∀ i j : Fin n, i < j → ⟦ts i⟧ˢ ≠ ⟦ts j⟧ˢ

/-- `denote_distinct` of a list of domain values is `⊤` exactly when the list
has no duplicate entries. -/
theorem denote_distinct_eq_top_iff {Ts : List Dom} :
    denote_distinct Ts = ⊤ ↔ Ts.Nodup := by
  induction Ts with
  | nil => simp [denote_distinct]
  | cons x xs ih =>
    have hd : denote_distinct (x :: xs)
        = ZFBool.ofBool (decide (x ∉ xs)) ⋀ denote_distinct xs := by
      rw [denote_distinct]
      exact Subtype.ext (overloadBinOp_𝔹_val _ _ _)
    rw [hd, zfbool_and_eq_top_iff, List.nodup_cons, ih, ZFBool.ofBool_decide_eq_true_iff]

/-- Cons equation for `List.allSome`. -/
private theorem allSome_cons {α : Type*} (a : Option α) (as : List (Option α)) :
    (a :: as).allSome = a.bind fun x => (as.allSome).map (x :: ·) := by
  show (a :: as).mapM id = _
  rw [List.mapM_cons]
  cases a <;> simp [List.allSome, Option.map_eq_bind]

/-- `List.allSome` succeeds with `Ts` exactly when the input is `Ts.map some`. -/
private theorem allSome_eq_map_some {α : Type*} {l : List (Option α)} {Ts : List α} :
    l.allSome = some Ts ↔ l = Ts.map some := by
  induction l generalizing Ts with
  | nil => cases Ts <;> simp [List.allSome, List.mapM_nil]
  | cons a as ih =>
    rw [allSome_cons]
    cases a with
    | none => cases Ts <;> simp
    | some v =>
      cases Ts with
      | nil => simp
      | cons t ts =>
        simp only [Option.bind_some, Option.map_eq_some_iff, List.map_cons,
          List.cons.injEq, Option.some.injEq, ih]
        aesop

/-- The SMT denotation of `distinct ts` carries the boolean `⊤` exactly when
the `ts` denote pairwise-distinctly (`denote.distinct_alt_def`). -/
theorem denote_distinct_alt_def_correct {n : ℕ} {ts : Fin n → PHOAS.Term Dom} {D : Dom}
    (hD : ⟦PHOAS.Term.distinct ts⟧ˢ = some D) :
    D.1 = (⊤ : ZFBool) ↔ denote.distinct_alt_def ts := by
  simp only [denote] at hD
  cases hAS : (List.ofFn fun i => ⟦ts i⟧ˢ).allSome with
  | none => rw [hAS] at hD; simp at hD
  | some Ts =>
    rw [hAS] at hD
    injection hD with hD
    subst hD
    rw [allSome_eq_map_some] at hAS
    show (denote_distinct Ts : ZFSet) = ((⊤ : ZFBool) : ZFSet) ↔ denote.distinct_alt_def ts
    rw [Subtype.coe_inj, denote_distinct_eq_top_iff]
    have hmap : Ts.Nodup ↔ Function.Injective (fun i : Fin n => ⟦ts i⟧ˢ) := by
      rw [← List.nodup_ofFn (f := fun i : Fin n => ⟦ts i⟧ˢ), hAS,
        List.nodup_map_iff (Option.some_injective Dom)]
    rw [hmap]
    unfold denote.distinct_alt_def
    constructor
    · intro hinj i j hij heq
      exact absurd (hinj heq) (ne_of_lt hij)
    · intro hpair i j heq
      rcases lt_trichotomy i j with h | h | h
      · exact absurd heq (hpair i j h)
      · exact h
      · exact absurd heq.symm (hpair j i h)

end SMT
