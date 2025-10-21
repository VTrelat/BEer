import Batteries
import Mathlib.Data.List.Indexes
import Mathlib.Data.List.AList
import Mathlib.Data.Finmap
import CustomPrelude

def Nat.toPaddedString (n : Nat) (pad : Nat) : String :=
  let s := n.repr
  if s.length < pad then "0" ++ (Nat.toPaddedString n (pad - 1))
  else s

variable {α β : Type _}

theorem List.ne_nil_snoc {xs : List α} : xs ≠ [] ↔ ∃ (x : α) (ys : List α), xs = ys.concat x := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, concat_eq_append, true_iff]
    rcases xs with _ | ⟨y, ys⟩
    · exact ⟨x, [], rfl⟩
    · simp at ih
      obtain ⟨a, as, h⟩ := ih
      exact ⟨a, x::as, congrArg (cons x) h⟩

def List.induction₂ {α β : Type _} {motive : (xs : List α) → (ys : List β) → xs.length = ys.length → Prop}
                    (nil_nil : motive [] [] rfl)
                    (cons_cons : ∀ x xs y ys, (len_eq : xs.length = ys.length) → motive xs ys len_eq → motive (x :: xs) (y :: ys) (Nat.succ_inj.mpr len_eq)) :
  (xs : List α) → (ys : List β) → (len_eq : xs.length = ys.length) → motive xs ys len_eq
  | [], [], _ => nil_nil
  | _ :: _, _ :: _, len_eq => cons_cons _ _ _ _ (Nat.succ_inj.mp len_eq) (List.induction₂ nil_nil cons_cons _ _ _)

@[simp]
theorem List.append_sizeOf {α} [SizeOf α] {xs ys : List α} : 1 + sizeOf (xs ++ ys) = sizeOf xs + sizeOf ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp +arith [List.cons_append, List.cons.sizeOf_spec]
    conv =>
      conv => lhs; rw [add_comm]
      conv => rhs; rw [add_comm]
    exact ih

@[simp]
theorem List.concat_sizeOf {α} [SizeOf α] {xs : List α} {x : α} :
  sizeOf (xs.concat x) = 1 + sizeOf xs + sizeOf x := by
  suffices this : 1 + sizeOf (xs.concat x) = 2 + sizeOf xs + sizeOf x by
    apply Nat.add_left_cancel (n:=1)
    rw [(by simp +arith : 1 + (1 + sizeOf xs + sizeOf x) = 2 + sizeOf xs + sizeOf x)]
    exact this
  rw [List.concat_eq_append, List.append_sizeOf]
  simp +arith [cons.sizeOf_spec, nil.sizeOf_spec]

def List.reverse_induction {α : Type _} {motive : (xs : List α) → Prop}
    (nil : motive [])
    (snoc : ∀ x xs, motive xs → motive (xs.concat x)) :
  (xs : List α) → motive xs
  | [] => nil
  | x :: xs => by
    let ⟨x', xs', heq⟩ := List.ne_nil_snoc.mp (List.cons_ne_nil x xs)
    let cons_app := snoc x' xs' (List.reverse_induction nil snoc xs')
    simp only [← heq] at cons_app
    exact cons_app
termination_by xs => xs
decreasing_by
  rw [heq, List.concat_sizeOf, sizeOf_default, add_zero, Nat.lt_add_left_iff_pos]
  exact Nat.one_pos

def List.reverse_induction₂ {α β : Type _} {motive : (xs : List α) → (ys : List β) → xs.length = ys.length → Prop}
                    (nil_nil : motive [] [] rfl)
                    (cons_cons : ∀ x xs y ys, (len_eq : xs.length = ys.length) → motive xs ys len_eq → motive (xs.concat x) (ys.concat y) (by simpa)) :
  (xs : List α) → (ys : List β) → (len_eq : xs.length = ys.length) → motive xs ys len_eq
  | [], [], _ => nil_nil
  | x :: xs, y :: ys, len_eq => by
    let ⟨x', xs', heq⟩ := List.ne_nil_snoc.mp (List.cons_ne_nil x xs)
    let ⟨y', ys', heq'⟩ := List.ne_nil_snoc.mp (List.cons_ne_nil y ys)
    have len_eq'' : xs'.length = ys'.length := by
      rw [heq, heq', List.length_concat, List.length_concat] at len_eq
      exact Nat.succ_inj.mp len_eq
    let cons_app := cons_cons x' xs' y' ys' len_eq'' (List.reverse_induction₂ nil_nil cons_cons xs' ys' len_eq'')
    simp only [← heq, ← heq'] at cons_app len_eq
    exact cons_app
termination_by xs ys => (xs, ys)
decreasing_by
  rw [heq, heq']
  left
  simp only [List.concat_sizeOf]
  rw [Nat.add_assoc, Nat.add_comm]
  exact Nat.lt_add_of_pos_right Nat.one_pos

abbrev List.Forall₂' {α β} (xs : List α) (ys : List β) (P : α → β → Prop ) (len_eq : xs.length = ys.length) :=
  ∀ i, (h : i < xs.length) → P (xs.get ⟨i, h⟩) (ys.get ⟨i, len_eq ▸ h⟩)

theorem List.Forall₂'_cons {α β} {xs : List α} {ys : List β} {P : α → β → Prop} {x : α} {y : β} (len_eq : (x::xs).length = (y::ys).length) :
  List.Forall₂' (x :: xs) (y :: ys) P len_eq ↔
  P x y ∧ List.Forall₂' xs ys P (by simpa [List.length_cons] using len_eq) := by
  constructor
  · intro h
    constructor
    · exact h 0 (Nat.zero_lt_succ _)
    · intro i hi
      exact h (i + 1) (Nat.add_lt_of_lt_sub hi)
  · rintro ⟨h₁, h₂⟩ i hi
    by_cases i_0 : i = 0
    · subst i_0; exact h₁
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := Nat.exists_eq_succ_of_ne_zero i_0
      exact h₂ j (by rwa [length_cons, Nat.add_lt_add_iff_right] at hi)

def List.induction₂' {α β : Type _} {motive : (xs : List α) → (ys : List β) → Prop}
                    (nil_nil : motive [] [])
                    (nil_cons : ∀ y ys, motive [] (y :: ys))
                    (cons_nil : ∀ x xs, motive (x :: xs) [])
                    (cons_cons : ∀ x xs y ys, motive xs ys → motive (x :: xs) (y :: ys)) :
  (xs : List α) → (ys : List β) → motive xs ys
  | [], [] => nil_nil
  | [], _ :: _ => nil_cons _ _
  | _ :: _, [] => cons_nil _ _
  | _ :: _, _ :: _ => cons_cons _ _ _ _ (List.induction₂' nil_nil nil_cons cons_nil cons_cons _ _)

theorem List.Forall₂_eq_Forall₂' {α β} {xs : List α} {ys : List β} {P : α → β → Prop} (len_eq : xs.length = ys.length) :
  List.Forall₂ P xs ys ↔ List.Forall₂' xs ys P len_eq := by
  induction xs, ys using List.induction₂' with
  | nil_nil => simp [List.Forall₂']
  | nil_cons y ys => contradiction
  | cons_nil x xs => contradiction
  | cons_cons x xs y ys IH =>
    constructor
    · intro Forall i hi
      rw [forall₂_cons] at Forall
      rw [length_cons, Nat.lt_succ] at hi
      by_cases i_0 : i = 0
      · subst i_0
        simp
        exact Forall.left
      · simp
        have ys_i : i-1 < ys.length := by
          simp_rw [length_cons, add_left_inj] at len_eq
          rw [← len_eq]
          have : 1 ≤ i := Nat.le_of_not_lt <| (congrArg Not (Nat.lt_one_iff.eq.symm)) ▸ i_0
          rw [← Nat.sub_add_cancel this] at hi
          exact Nat.lt_of_add_one_le hi
        have : P (x :: xs)[i] (y :: ys)[i] = P xs[i-1] ys[i-1] := by
          simp_rw [List.getElem_cons]
          split_ifs
          rfl
        rw [this]
        rw [forall₂_iff_get] at Forall
        exact Forall.right.right (i-1) (Forall.right.left ▸ ys_i) ys_i
    · exact λ f => forall₂_of_length_eq_of_get len_eq λ i h₁ _ => f i h₁

def AList.induction₂ {_α} {_β} [DecidableEq _α] [DecidableEq _β] {α : _α → Type _} {β : _β → Type _} {motive : (xs : AList α) → (ys : AList β) → Prop}
                    (nil_nil : motive ∅ ∅)
                    (nil_cons : ∀ y v (ys : AList β), motive ∅ (ys.insert y v))
                    (cons_nil : ∀ x u (xs : AList α), motive (xs.insert x u) ∅)
                    (cons_cons : ∀ x u xs y v ys, motive xs ys → motive (xs.insert x u) (ys.insert y v))
    (xs : AList α) (ys : AList β) : motive xs ys := match xs, ys with
    | ⟨[], _⟩, ⟨[], _⟩ => nil_nil
    | ⟨[], _⟩, ⟨⟨y, v⟩ :: ys, hy⟩ => by
      specialize nil_cons y v ⟨ys, (List.nodupKeys_of_nodupKeys_cons hy)⟩
      have : List.kerase y ys = ys := List.kerase_of_notMem_keys (List.nodupKeys_cons.mp hy |>.left)
      conv => enter [2,1,2]; rw [← this]
      exact nil_cons
    | ⟨⟨x, u⟩ :: xs, hx⟩, ⟨[], _⟩ => by
      specialize cons_nil x u ⟨xs, (List.nodupKeys_of_nodupKeys_cons hx)⟩
      have : List.kerase x xs = xs := List.kerase_of_notMem_keys (List.nodupKeys_cons.mp hx |>.left)
      conv => enter [1,1,2]; rw [← this]
      exact cons_nil
    | ⟨⟨x, u⟩ :: xs, hx⟩, ⟨⟨y, v⟩ :: ys, hy⟩ => by
      dsimp [AList.insert] at cons_cons
      have : List.kerase x xs = xs := List.kerase_of_notMem_keys (List.nodupKeys_cons.mp hx |>.left)
      conv => enter [1,1,2]; rw [← this]
      have : List.kerase y ys = ys := List.kerase_of_notMem_keys (List.nodupKeys_cons.mp hy |>.left)
      conv => enter [2,1,2]; rw [← this]
      exact cons_cons x u { entries := xs, nodupKeys := List.nodupKeys_of_nodupKeys_cons hx } y v ⟨ys, List.nodupKeys_of_nodupKeys_cons hy⟩
        (AList.induction₂ nil_nil nil_cons cons_nil cons_cons ⟨xs, List.nodupKeys_of_nodupKeys_cons hx⟩ ⟨ys, List.nodupKeys_of_nodupKeys_cons hy⟩)

theorem List.elem_iff_mem [BEq α] [LawfulBEq α] {x : α} {ys : List α} : List.elem x ys ↔ x ∈ ys :=
  ⟨mem_of_elem_eq_true, elem_eq_true_of_mem⟩

theorem List.notElem_iff_not_mem [BEq α] [LawfulBEq α] {x : α} {ys : List α} : !List.elem x ys ↔ x ∉ ys := by
  simp only [elem_eq_mem, Bool.not_eq_true', decide_eq_false_iff_not]

theorem List.mem_removeAll_iff [BEq α] [LawfulBEq α] {x : α} {xs ys : List α}
  : x ∈ List.removeAll xs ys ↔ x ∈ xs ∧ x ∉ ys := by
  calc
    x ∈ removeAll xs ys ↔ x ∈ filter (λ y => !elem y ys) xs := by rfl
    _ ↔ x ∈ xs ∧ !elem x ys := mem_filter
    _ ↔ x ∈ xs ∧ x ∉ ys := by rw [notElem_iff_not_mem]

def List.reduce {α} (f : α → α → α) : (l : List α) → l ≠ [] → α := λ l h => List.foldl f (l.head ‹_›) l.tail

@[simp] theorem List.reduce_singleton {α} (f : α → α → α) {x : α} :
  ([x]).reduce f (List.cons_ne_nil _ _) = x := rfl

theorem List.reduce_cons_cons {α} (f : α → α → α) {x y : α} {xs : List α} :
  (x :: y :: xs).reduce f (List.cons_ne_nil _ _) = (f x y :: xs).reduce f (List.cons_ne_nil _ _) := by
  simp_rw [List.reduce, List.head, List.tail, List.foldl_cons]

theorem List.foldl_cons_last {α} (f : α → α → α) {x y : α} {xs : List α} :
  (xs.concat y).foldl f x = f (xs.foldl f x) y := by
  induction xs generalizing x y with
  | nil => simp only [concat_eq_append, nil_append, foldl_cons, foldl_nil]
  | cons x' xs ih => rw [List.foldl_cons, List.concat_eq_append, List.cons_append, ←List.concat_eq_append, List.foldl_cons, ih]

def List.zipToAList {α β} [DecidableEq α] (xs : List α) (ys : List β) : AList (λ _ : α => β) :=
  List.zipWith Sigma.mk xs ys |>.toAList

def List.zipToFinmap {α β} [DecidableEq α] (xs : List α) (ys : List β) : Finmap λ _ : α => β :=
  List.zipWith Sigma.mk xs ys |>.toFinmap

theorem List.dedupKeys_subset {α} [DecidableEq α] {β : α → Type _} {xs : List (Sigma β)} : xs.dedupKeys ⊆ xs := by
  induction xs with
  | nil =>
    simp [List.dedupKeys]
  | cons x xs ih =>
    simp [List.dedupKeys_cons]
    intro a ha
    rw [List.mem_cons]
    by_cases a_eq : a = x
    · left; assumption
    · right
      exact ih (List.Sublist.subset (List.kerase_sublist x.fst xs.dedupKeys) ha)

theorem List.mem_zipWith_fst {a : α} {xs : List α} {ys : List β} : a ∈ List.zipWith (λ x _ => x) xs ys → a ∈ xs := by
  intro h
  induction xs, ys using List.induction₂' with
  | nil_nil | nil_cons | cons_nil => contradiction
  | cons_cons x xs y ys ih =>
    rcases h with (_ | ⟨_, h⟩)
    · exact mem_cons_self
    · exact mem_cons_of_mem x (ih h)

theorem AList.zipToAList_cons {α β} [DecidableEq α] {x : α} {y : β} {xs : List α} {ys : List β} : (x :: xs).zipToAList (y :: ys) = (xs.zipToAList ys).insert x y := rfl

theorem AList.mem_zipToAList {α β} [DecidableEq α] {xs : List α} {ys : List β} {x : α} : x ∈ List.zipToAList xs ys → x ∈ xs := by
  intro h
  rw [List.zipToAList, List.toAList, AList.mem_keys, AList.keys] at h
  apply List.map_subset Sigma.fst <| List.dedupKeys_subset (xs:=List.zipWith Sigma.mk xs ys) at h
  rw [List.map_zipWith] at h
  apply List.mem_zipWith_fst h

def AList.filter {α} {β : α → Type _} [DecidableEq α] (p : ∀ a, β a → Bool) (xs : AList β) : AList β where
  entries := xs.entries.filter (λ ⟨a, b⟩ => p a b)
  nodupKeys := by
    induction xs with
    | H0 =>
      rw [empty_entries, List.filter_nil]
      exact List.nodupKeys_nil
    | IH k v xs hk ih =>
      rw [entries_insert, List.filter_cons, List.kerase_of_notMem_keys]
      · split_ifs
        · rw [List.nodupKeys_cons]
          and_intros
          · dsimp
            intro contr
            rw [mem_keys] at hk
            rw [List.mem_keys] at contr
            obtain ⟨v, contr⟩ := contr
            rw [List.mem_filter] at contr
            absurd hk
            refine mem_keys.mpr ?_
            unfold keys
            rw [List.mem_keys]
            exact ⟨v, contr.1⟩
          · exact ih
        · exact ih
      · exact hk

theorem List.reduce_cons {α} {f : α → α → α} [Std.Associative f] {x : α} {xs : List α} (h : xs ≠ []) : (x::xs).reduce f (List.cons_ne_nil _ _) = f x (xs.reduce f h) := by
  let y::xs := xs
  simp [List.reduce, List.foldl_assoc]

theorem List.map_ext {α β} {xs ys : List α} {f : α → β}: Function.Injective f → xs.map f = ys.map f → xs = ys := by
  intro h
  apply List.map_injective_iff.mpr h

@[simp] def List.mapUpperDiag {α β} (f : α → α → β) (l : List α) : List β := go l []
  where @[simp] go : List α → List β → List β
    | [], acc => acc
    | x::xs, acc => go xs <| acc ++ xs.attach.map (λ ⟨y, _⟩ => f x y)

@[simp] def List.upperDiag {α} : List α → List (α × α) := List.mapUpperDiag Prod.mk

theorem List.mapUpperDiag.go_size {α β} {xs : List α} {ys : List β} {f}: (List.mapUpperDiag.go f xs ys).length = ys.length + xs.length * (xs.length - 1) / 2 := by
  induction xs generalizing ys with
  | nil => dsimp
  | cons x xs ih =>
    rw [List.mapUpperDiag.go, ih]
    simp only [length_cons, Nat.add_one_sub_one]
    rw [List.length_append, length_map, add_assoc, add_left_cancel_iff]
    cases xs with
    | nil => exact add_eq_right.mpr rfl
    | cons x' xs =>
      rw [List.length_attach, List.length_cons]
      conv_rhs =>
        conv =>
          enter [1, 1]
          rw [add_assoc]
        rw [Nat.right_distrib, Nat.add_comm, Nat.mul_add_div (Nat.zero_lt_succ 1), mul_comm]
      rfl

theorem List.mapUpperDiag_size {α β} {xs : List α} {f : α → α → β} : (xs.mapUpperDiag f).length = xs.length * (xs.length - 1) / 2 := by
  induction xs with
  | nil => dsimp
  | cons x xs ih =>
    rw [List.mapUpperDiag, List.mapUpperDiag.go_size]
    rw [length_nil, length_cons, Nat.add_one_sub_one, zero_add]

theorem List.upperDiag_size {α} {xs : List α} : xs.upperDiag.length = xs.length * (xs.length - 1) / 2 := by
  induction xs with
  | nil => dsimp
  | cons x xs ih => rw [List.upperDiag, List.mapUpperDiag_size]

theorem List.mapUpperDiag.go_mem {α β} {xs : List α} {ys : List β} {z : β} {f : α → α → β} : z ∈ List.mapUpperDiag.go f xs ys → z ∈ ys ∨ ∃ x y, x ∈ xs ∧ y ∈ xs ∧ z = f x y := by
  intro h
  induction xs generalizing ys with
  | nil => exact Or.inl h
  | cons x xs ih =>
    simp only [go, map_subtype, unattach_attach] at h
    specialize ih h
    rw [List.mem_append, List.mem_map] at ih
    rcases ih with ⟨ih | ⟨a, ha, rfl⟩⟩ | ⟨a, b, ha, hb, rfl⟩
    · exact Or.inl ih
    · right
      exact ⟨x, a, mem_cons_self, mem_cons_of_mem x ha, rfl⟩
    · right
      exact ⟨a, b, mem_cons_of_mem x ha, mem_cons_of_mem x hb, rfl⟩

theorem List.mapUpperDiag_mem {α β} {xs : List α} {z : β} {f : α → α → β} : z ∈ xs.mapUpperDiag f → ∃ x y, x ∈ xs ∧ y ∈ xs ∧ z = f x y := by
  intro h
  induction xs with
  | nil => contradiction
  | cons z xs ih =>
    dsimp at h
    rcases List.mapUpperDiag.go_mem h with h | ⟨x, y, hx, hy, rfl⟩
    · simp only [map_subtype, unattach_attach, mem_map] at h
      obtain ⟨w, hw, rfl⟩ := h
      rcases List.mapUpperDiag.go_mem h with h | ⟨a, b, ha, hb, eq⟩
      · exact ⟨z, w, mem_cons_self, mem_cons_of_mem z hw, rfl⟩
      · exact ⟨a, b, mem_cons_of_mem z ha, mem_cons_of_mem z hb, eq⟩
    · exact ⟨x, y, mem_cons_of_mem z hx, mem_cons_of_mem z hy, rfl⟩

theorem List.upperDiag_mem {x y} {xs : List α} : (x, y) ∈ xs.upperDiag → x ∈ xs ∧ y ∈ xs := by
  intro h
  rw [List.upperDiag] at h
  obtain ⟨x, y, hx, hy, eq⟩ := List.mapUpperDiag_mem h
  injection eq
  subst x y
  exact ⟨hx, hy⟩

theorem List.inter_append_eq_nil {α} [DecidableEq α] {xs ys zs : List α} : xs ∩ (ys ++ zs) = [] → xs ∩ ys = [] ∧ xs ∩ zs = [] := by
  induction ys with
  | nil =>
    rw [List.nil_append, List.inter_nil' xs]
    exact (⟨rfl, ·⟩)
  | cons y ys ih =>
    intro h
    simp_rw [List.eq_nil_iff_forall_not_mem] at *
    and_intros
    · intro s
      specialize h s
      rw [List.mem_inter_iff, not_and_or] at h ⊢
      rcases h with _ | h
      · left; assumption
      · right
        rw [List.mem_append, not_or] at h
        exact h.1
    · intro s
      rw [List.mem_inter_iff, not_and_or]
      specialize h s
      rw [List.mem_inter_iff, not_and_or] at h
      rcases h with _ | h
      · left; assumption
      · right
        rw [List.mem_append, not_or] at h
        exact h.2

theorem List.length_keys {α} {β : α → _} {l : List (Sigma β)} : (l.keys).length = l.length :=
  rec rfl (fun {_ _} => Nat.succ_inj.mpr) l

theorem List.foldr_finRange_eq_foldr {α β} (xs : List α) {f : α → β → β} {init : _} :
  List.foldr (fun i acc ↦ f xs[i] acc) (init := init) (List.finRange xs.length) =
  xs.foldr (fun x acc ↦ f x acc) init := by
  rw [← @Fin.foldr_eq_foldr_finRange]
  induction xs generalizing init with
  | nil => simp only [List.length_nil, Fin.getElem_fin, Fin.foldr_zero, List.foldr_nil]
  | cons x xs ih =>
    simp only [List.length_cons]
    simp_rw [Fin.getElem_fin, List.foldr_cons, Fin.foldr_succ, Fin.val_succ, List.getElem_cons_succ]
    rw [←ih]
    congr

namespace Batteries

def AssocList.insert [BEq α] (l : AssocList α β) (x : α) (y : β) : AssocList α β :=
  match l with
  | .nil => .cons x y .nil
  | .cons k v l' => if x == k then l'.cons k y else .cons k v (l'.insert x y)

def AssocList.append [BEq α] (l₁ l₂ : AssocList α β) : AssocList α β :=
  match l₁ with
  | .nil => l₂
  | .cons k v l => insert (append l l₂) k v

instance [BEq α] : Append (AssocList α β) where
  append := AssocList.append

theorem AssocList.find?_insert_self {α β : Type} [DecidableEq α] (xs : AssocList α β) (k : α) (v : β) :
  (xs.insert k v).find? k = some v := by
  induction xs with
  | nil => rw [insert, find?, BEq.rfl]
  | cons key val xs ih =>
    rw [insert]
    split_ifs with h <;> rw [beq_iff_eq] at h
    · subst k
      rw [find?, BEq.rfl]
    · rw [find?]
      split using h'
      · rw [beq_iff_eq] at h'
        subst k
        contradiction
      · exact ih

theorem AssocList.find?_insert_ne {α β : Type} [DecidableEq α] (xs : AssocList α β) (k₁ k₂ : α) (v : β) (h : k₁ ≠ k₂) :
  (xs.insert k₁ v).find? k₂ = xs.find? k₂ := by
  induction xs with
  | nil =>
    rw [insert, find?, find?]
    split using h'
    · rw [beq_iff_eq] at h'
      contradiction
    · rfl
  | cons key val xs ih =>
    rw [insert, find?]
    split_ifs with h' <;> rw [beq_iff_eq] at h'
    · subst k₁
      split using h''
      · rw [beq_iff_eq] at h''
        subst k₂
        contradiction
      · rw [find?]
        split using h''
        · rw [beq_iff_eq] at h''
          subst key
          contradiction
        · rfl
    · rw [find?]
      split using h'' | h'' <;> simp only [beq_iff_eq, beq_eq_false_iff_ne, ne_eq] at h''
      · rfl
      · exact ih

end Batteries

def IO.propagateError {ε α} [ToString ε] : IO (Except ε α) → IO α := (· >>= IO.ofExcept)

/--
  If `f : γ → δ` and `g : α → β → γ`, then `f ∘₂ g : α → β → δ`
  is the function that applies `g` to its arguments and then `f` to the result.
-/
abbrev Functor.rcomp2 {α β γ δ} : (γ → δ) → (α → β → γ) → α → β → δ := (· ∘ ·) ∘ (· ∘ ·)
infixr:90 " ∘₂ " => Functor.rcomp2

theorem Array.attach_size_eq {a : Array α} : a.attach.size = a.size := by
  unfold attach attachWith
  obtain ⟨as⟩ := a
  induction as <;> simp [List.attachWith, List.pmap]

macro_rules | `(tactic| get_elem_tactic_trivial) => `(tactic| rw [Array.attach_size_eq]; get_elem_tactic_trivial; done)

@[simp]
theorem Array.sizeOf_toArray {α} [SizeOf α] {xs : List α} : sizeOf (List.toArray xs) = 1 + sizeOf xs := by rw [Array.mk.sizeOf_spec]

macro_rules | `(tactic| decreasing_trivial) => `(tactic| first
  | with_reducible apply Array.sizeOf_lt_of_mem; assumption; done
  | with_reducible
      apply Nat.lt_trans (Array.sizeOf_lt_of_mem ?h)
      case' h => assumption
    simp_arith)

def String.dup (s : String) (n : Nat) : String := n.fold (λ _ _ => HAppend.hAppend s) ""

theorem Nat.div2_eq_zero_iff {n : Nat} : n / 2 = 0 ↔ n = 0 ∨ n = 1 := by
  constructor
  · intro h
    cases n with
    | zero => exact Or.inl rfl
    | succ n =>
      right
      rw [Nat.div_eq_zero_iff] at h
      rcases h with _|h
      · contradiction
      · rw [lt_iff_add_one_le, add_assoc] at h
        have := Nat.add_le_add_iff_right.mp h
        obtain ⟨rfl⟩ := le_zero.mp this
        rfl
  · rintro (rfl | rfl) <;> rfl

namespace Equiv


theorem toFun.injective {α β} {E : Equiv α β} : Function.Injective E.toFun := by
  intro x y h
  rw [← E.injective h]

theorem invFun.injective {α β} {E : Equiv α β} : Function.Injective E.invFun := by
  intro x y h
  rw [← E.symm.injective h]

end Equiv

namespace Function
def updates {α β} [DecidableEq α] (f : α → β) (xs : List α) (ys : List β) :=
  match xs, ys with
  | [], _ | _, [] => f
  | x::xs, y::ys => Function.updates (Function.update f x y) xs ys

theorem updates_eq_foldl {α β} [DecidableEq α] {f : α → β} {xs : List α} {ys : List β} :
  Function.updates f xs ys = List.foldl (λ f (p : α × β) => Function.update f p.1 p.2) f (List.zip xs ys) := by
  induction xs generalizing f ys with
  | nil => rw [updates, List.zip_nil_left, List.foldl_nil]
  | cons x xs ih =>
    cases ys with
    | nil =>
      rw [updates, List.zip_nil_right, List.foldl_nil]
      rintro ⟨⟩
    | cons y ys => rw [updates, ih, List.zip_cons_cons, List.foldl_cons]

theorem updates_eq_if {α β} [DecidableEq α] {f : α → β} {xs : List α} {ys : List β} {k : α} (len_eq : xs.length = ys.length) (hxs : xs.Nodup) :
  (Function.updates f xs ys) k = if hk : k ∈ xs
    then
      ys[xs.idxOf k]'(by rw [←len_eq]; exact List.idxOf_lt_length_of_mem hk)
    else f k := by
  induction xs, ys, len_eq using List.induction₂ generalizing f with
  | nil_nil => simp_rw [updates, List.not_mem_nil, dite_false]
  | cons_cons x xs y ys _ ih =>
    simp only [updates, List.mem_cons]
    split_ifs with hk
    · rcases hk with hk | hk
      · rw [ih (List.Nodup.of_cons hxs)]
        subst k
        split_ifs with hk'
        · rw [List.nodup_cons] at hxs
          nomatch hxs.1 hk'
        · simp_rw [update_self, List.idxOf_cons_self, List.getElem_cons_zero]
      · rw [ih (List.Nodup.of_cons hxs), dite_cond_eq_true (eq_true hk)]
        have : x ≠ k := by
          rintro rfl
          nomatch (List.nodup_cons.mp hxs).1 hk
        simp_rw [List.idxOf_cons_ne _ this, Nat.succ_eq_add_one, List.getElem_cons_succ]
    · push_neg at hk
      rw [ih (List.Nodup.of_cons hxs), dite_cond_eq_false (eq_false hk.2), update, dite_cond_eq_false (eq_false hk.1)]
end Function

def MCH2POG (mchPath : String) : IO System.FilePath := do
  let dir : System.FilePath := "/Applications"/"atelierb-free-arm64-24.04.2.app"/"Contents"/"Resources"
  let stdout ← IO.Process.run {
    cmd := dir/"bin"/"bxml" |>.toString
    args := #["-a", mchPath]
  }
  let path ← IO.FS.createTempDir
  let bxml := path/"tmp.bxml"
  let _ ← IO.FS.withFile bxml .write λ f => f.putStr stdout
  let _ ← IO.Process.run {
    cmd := dir/"bin"/"pog" |>.toString
    args := #["-p", dir/"include"/"pog"/"paramGOPSoftware.xsl" |>.toString, bxml.toString]
  }
  return bxml.withExtension "pog"

def cvc5 (raw : String) (timeout := 1000): IO String := do
  let smtFile ← String.append <$> IO.FS.readFile "prelude.smt" <*> pure ("\n"++raw)
  let dir ← IO.FS.createTempDir
  let file := dir/"tmp.smt2"
  let _ ← IO.FS.withFile file .write λ f => f.putStr smtFile
  let proc ← IO.Process.spawn {
    cmd := "cvc5"
    args := #["--incremental", "--mbqi", s!"--tlimit-per={timeout}", file.toString]
    stdout := IO.Process.Stdio.piped
    stderr := IO.Process.Stdio.piped
  }
  let exit ← proc.wait
  match exit with
  | 0 => proc.stdout.readToEnd
  | n => throw <| IO.userError s!"cvc5 failed with exit code {n}\n{← proc.stdout.readToEnd}\n{← proc.stderr.readToEnd}"
