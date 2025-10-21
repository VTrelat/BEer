import Mathlib.Order.Defs.LinearOrder
import Mathlib.Tactic.SplitIfs

variable {α} [LinearOrder α] [DecidableLE α]

def le (x : α) (xs : List α) : Prop :=
  ∀ y ∈ xs, x ≤ y

def sorted : List α → Prop
  | [] => True
  | x :: xs => le x xs ∧ sorted xs

def insort (x : α) : List α → List α
  | [] => [x]
  | y :: xs => if x ≤ y then x :: y :: xs else y :: insort x xs

def sort : List α → List α
  | [] => []
  | x :: xs => insort x (sort xs)

@[simp]
theorem mem_insort {z x : α} {xs : List α} : z ∈ insort x xs ↔ z = x ∨ z ∈ xs := by
  induction xs with
  | nil => rw [insort, List.mem_cons]
  | cons y xs ih =>
    rw [insort, List.mem_cons]
    split_ifs with x_le_y
    · simp only [List.mem_cons]
    · rw [List.mem_cons, ih, or_left_comm]

@[simp]
theorem le_insort {x y : α} {xs : List α} : le y (insort x xs) ↔ y ≤ x ∧ le y xs := by
  cases xs with
  | nil =>
    simp only [le, insort, List.mem_cons, List.not_mem_nil, or_false, forall_eq, false_implies, implies_true, and_true]
  | cons z xs =>
    rw [insort]
    split_ifs with x_le_z
    · simp only [le, List.mem_cons, forall_eq_or_imp]
    · constructor
      · intro h
        and_intros
        · apply h x
          rw [List.mem_cons, mem_insort]
          right
          left
          rfl
        · intro w hw
          apply h w
          rw [List.mem_cons] at hw ⊢
          rw [mem_insort, or_left_comm]
          right
          exact hw
      · intro h
        intro w hw
        rw [List.mem_cons, mem_insort] at hw
        rcases hw with rfl | rfl | hw
        · exact h.2 w List.mem_cons_self
        · exact h.1
        · exact h.2 w (List.mem_cons_of_mem z hw)

theorem sorted_insort {x : α} {xs : List α} (h : sorted xs) : sorted (insort x xs) := by
  induction xs with
  | nil =>
    rw [insort, sorted]
    and_intros
    · intro _ h
      rw [List.mem_nil_iff] at h
      nomatch h
    · exact h
  | cons y xs ih =>
    rw [insort]
    split_ifs with x_le_y
    · rw [sorted] at h ⊢
      and_intros
      · intro z hz
        rw [List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact x_le_y
        · trans y
          · exact x_le_y
          · exact h.1 z hz
      · exact h.1
      · exact h.2
    · rw [sorted] at h ⊢
      and_intros
      · rw [le_insort]
        and_intros
        · exact le_of_not_ge x_le_y
        · exact h.1
      · exact ih h.2

theorem sorted_correct (xs : List α) :
    sorted (sort xs) := by
  induction xs with
  | nil => trivial
  | cons x xs ih => exact sorted_insort ih
