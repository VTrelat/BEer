import B.Syntax.Basic
import Extra.Prettifier
import Extra.Utils

inductive DefinitionType
  | ctx | seext | inv | ass | lprp | inprp | inext | cst | sets | mchcst | aprp | abs | imlprp | imprp | imext
  deriving Inhabited, BEq

instance : ToString DefinitionType where
  toString := λ
    | .ctx => "ctx"
    | .seext => "seext"
    | .inv => "inv"
    | .ass => "ass"
    | .lprp => "lprp"
    | .inprp => "inprp"
    | .inext => "inext"
    | .cst => "cst"
    | .sets => "sets"
    | .mchcst => "mchcst"
    | .aprp => "aprp"
    | .abs => "abs"
    | .imlprp => "imlprp"
    | .imprp => "imprp"
    | .imext => "imext"

def String.toDefinitionType : String → Option DefinitionType
  | "ctx" => some .ctx
  | "seext" => some .seext
  | "inv" => some .inv
  | "ass" => some .ass
  | "lprp" => some .lprp
  | "inprp" => some .inprp
  | "inext" => some .inext
  | "cst" => some .cst
  | "sets" => some .sets
  | "mchcst" => some .mchcst
  | "aprp" => some .aprp
  | "abs" => some .abs
  | "imlprp" => some .imlprp
  | "imprp" => some .imprp
  | "imext" => some .imext
  | _ => none

open Batteries

variable {α β : Type _}

theorem Batteries.AssocList.cons_inj {α β} {Γ Δ : AssocList α β} {x y} {u v} : Γ.cons x u = Δ.cons y v → x = y ∧ u = v ∧ Γ = Δ := by
  rintro ⟨⟩
  exact ⟨rfl, rfl, rfl⟩

def Batteries.AssocList.keys : AssocList α β → List α
  | .nil => []
  | .cons k _ xs => k :: AssocList.keys xs

def Batteries.AssocList.values : AssocList α β → List β
  | .nil => []
  | .cons _ v xs => v :: AssocList.values xs

theorem Batteries.AssocList.mem_insert_neq_keys_mem [BEq α] [LawfulBEq α] {Γ : AssocList α β} {v : β} (a k : α) : a ≠ k → a ∈ (Γ.insert k v).keys → a ∈ Γ.keys := by
  intro a_neq_k a_in
  induction Γ with
  | nil =>
    rw [insert, keys, keys, List.mem_singleton] at a_in
    nomatch a_neq_k a_in
  | cons key val Γ ih =>
    rw [insert] at a_in
    split at a_in
    · rename_i k_eq_key
      simp only [beq_iff_eq] at k_eq_key
      subst k_eq_key
      assumption
    · rename_i k_neq_key
      simp only [beq_iff_eq] at k_neq_key
      rw [keys, List.mem_cons] at a_in
      rcases a_in with rfl | a_in
      · left
      · specialize ih a_in
        right
        exact ih

theorem Batteries.AssocList.insert_keys [BEq α] [LawfulBEq α] {Γ : AssocList α β} {v : β} (k : α) : k ∉ Γ.keys → (Γ.insert k v).keys = Γ.keys.concat k := by
  intro h
  induction Γ with
  | nil => rfl
  | cons key val Γ IH =>
    rw [keys, List.mem_cons, not_or] at h
    specialize IH h.right
    rw [insert]
    cases h' : k == key with
    | false => simp only [Bool.false_eq_true, if_false, keys, IH, List.concat_eq_append, List.cons_append]
    | true =>
      replace h' := eq_of_beq h'
      absurd h.left
      assumption

theorem Batteries.AssocList.insert_keys_of_mem [BEq α] [LawfulBEq α] {Γ : AssocList α β} {v : β} (k : α) : k ∈ Γ.keys → (Γ.insert k v).keys = Γ.keys := by
  intro mem_keys
  induction Γ generalizing k v with
  | nil =>
    rw [AssocList.keys] at mem_keys
    nomatch mem_keys
  | cons k' v' Γ ih =>
    rw [keys, List.mem_cons] at mem_keys
    rcases mem_keys with rfl | mem_keys
    · rw [AssocList.insert, BEq.rfl, ite_cond_eq_true, keys, keys]
      exact eq_true rfl
    · rw [AssocList.insert, AssocList.keys]
      split_ifs with h
      · rw [beq_iff_eq] at h
        subst h
        rw [keys]
      · rw [keys, ih _ mem_keys]

theorem Batteries.AssocList.mem_insert_self_keys [BEq α] [LawfulBEq α] {Γ : AssocList α β} {v : β} (k : α) : k ∈ (Γ.insert k v).keys := by
  induction Γ with
  | nil => exact List.mem_of_getLast? rfl
  | cons key val Γ IH =>
    dsimp [insert]
    rcases h : k == key with _ | h
    · simp only [Bool.false_eq_true, if_false, keys, List.mem_cons]
      exact Or.inr IH
    · replace h := eq_of_beq h
      subst h
      simp only [if_true]
      exact List.mem_cons_self

theorem Batteries.AssocList.mem_insert_cons [BEq α] [LawfulBEq α] {Γ : AssocList α β} {k key : α} {v val : β} : k ∈ ((Γ.cons key val).insert k v).keys := by
  simp only [insert]
  split
  · rename_i h
    simp only [beq_iff_eq] at h
    subst h
    left
  · rename_i h
    simp only [beq_iff_eq] at h
    rw [keys, List.mem_cons]
    right
    exact mem_insert_self_keys k

theorem Batteries.AssocList.mem_insert_keys_dest [BEq α] [LawfulBEq α] {Γ : AssocList α β} {v : β} (k l : α) : k ∈ (Γ.insert l v).keys → k = l ∨ k ∈ Γ.keys := by
  intro h
  induction Γ with
  | nil =>
    rw [insert, keys, keys, List.mem_singleton] at h
    left
    assumption
  | cons key val Γ ih =>
    rw [insert] at h
    split at h
    · rename_i h'
      simp only [beq_iff_eq] at h'
      subst h'
      rw [keys, List.mem_cons] at h ⊢
      exact or_self_left.mpr h
    · rename_i h'
      simp only [beq_iff_eq] at h'
      rw [keys, List.mem_cons] at h
      rcases h with rfl | h
      · right
        rw [keys, List.mem_cons]
        left
        rfl
      · rw [keys, List.mem_cons]
        rcases ih h with rfl | h
        · left; rfl
        · right; right; assumption

theorem Batteries.AssocList.mem_insert_keys [BEq α] [LawfulBEq α] {Γ : AssocList α β} {v : β} (k l : α) : k = l ∨ k ∈ Γ.keys → k ∈ (Γ.insert l v).keys := by
  induction Γ with
  | nil =>
    rintro (rfl | h)
    · rw [insert, keys, keys, List.mem_singleton]
    · exact List.mem_of_mem_tail h
  | cons key val Γ IH =>
    rintro (rfl | h)
    · simp only [true_or, true_implies] at IH
      exact mem_insert_cons
    · simp only [insert]
      split
      · rename_i h'
        simp only [beq_iff_eq] at h'
        subst h'
        exact h
      · rename_i h'
        simp only [beq_iff_eq] at h'
        rw [keys, List.mem_cons] at h ⊢
        rcases h with rfl | h
        · left; rfl
        · specialize IH (Or.inr h)
          right
          exact IH

namespace B

inductive BType where
  | int
  | bool
  | set (α : BType)
  | prod (α β : BType)
  deriving DecidableEq, Inhabited

partial def BType.pretty : BType → Nat → Std.Format
  | int => λ _ => "int"
  | bool => λ _ => "bool"
  | set α => λ _ => "set" ++ .paren (BType.pretty α 0)
  | prod α β => «infixr» BType.pretty 50 "×" α β

instance : ToString BType := ⟨(BType.pretty · 0 |> toString)⟩

infixl:95 " ×ᴮ " => BType.prod

def BType.toTerm : B.BType → B.Term
  | .int => .ℤ
  | .bool => .𝔹
  | .set α => 𝒫ᴮ (toTerm α)
  | α ×ᴮ β => (toTerm α) ⨯ᴮ (toTerm β)

/--
  A context is a map from variables to types
-/
abbrev TypeContext := AList λ _ : 𝒱 => BType

protected def TypeContext.repr (Γ : TypeContext) (n : Nat) : Std.Format :=
  let _ : Lean.ToFormat (𝒱 × BType) := ⟨λ (v, τ) => repr v ++ " : " ++ τ.pretty 0⟩
  match Γ.entries, n with
  | .nil, _ => "[]"
  | as, _ => .bracket "[" (.joinSep as ("," ++ .line)) "]"
instance : Repr TypeContext := ⟨TypeContext.repr⟩

instance : ToString TypeContext := ⟨λ Γ => "[" ++ (", ".intercalate (Γ.entries.map fun ⟨v, τ⟩ => v ++ " : " ++ toString τ)) ++ "]"⟩


abbrev TypeContext.dom (Γ : TypeContext) : List 𝒱 := Γ.keys

abbrev TypeContext.find? (Γ : TypeContext) (v : 𝒱) : Option BType := Γ.lookup v

theorem TypeContext.find_in_dom {v τ} {Γ : TypeContext} : Γ.find? v = some τ → v ∈ Γ.dom := by
  intro h
  apply AList.mem_keys.mp
  change Γ.lookup v = some τ at h
  replace h : (Γ.lookup v).isSome = true := h ▸ rfl
  exact AList.lookup_isSome.mp h

-- theorem TypeContext.dom_insert {x τ} {Γ : TypeContext} : x ∉ Γ → TypeContext.dom (Γ.insert x τ) = {x} ∪ Γ.dom := by
--   intro not_in
--   unfold TypeContext.dom
--   ext1 a
--   simp only [AList.keys_insert]
--   admit

theorem TypeContext.erase_dom {x} {Γ : TypeContext} : TypeContext.dom (Γ.erase x) = Γ.dom.erase x := AList.keys_erase x Γ

end B
