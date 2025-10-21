import Batteries.Data.HashMap.Basic

namespace BSyntax

@[reducible, inline]
def 𝒱 := String

inductive BTerm where
  -- base types
  | var : 𝒱 -> BTerm
  | bool : Bool -> BTerm
  | int : Int -> BTerm
  | Maplet : BTerm -> BTerm -> BTerm
  -- arithmetic
  | Add : BTerm -> BTerm -> BTerm
  | Mul : BTerm -> BTerm -> BTerm
  -- set theory
  | Pow : BTerm -> BTerm
  | Mem : BTerm -> BTerm -> BTerm
  | Union : BTerm -> BTerm -> BTerm
  | Inter : BTerm -> BTerm -> BTerm
  | Collect : 𝒱 -> BTerm -> BTerm -> BTerm
  | UNIV : BTerm
  | Diff : BTerm -> BTerm -> BTerm
  -- | CProd : BTerm -> BTerm -> BTerm
  -- logic
  | And : BTerm -> BTerm -> BTerm
  | Not : BTerm -> BTerm
  | Eq : BTerm -> BTerm -> BTerm

prefix:65 "𝒫" => BTerm.Pow
infixl:65 "∪ᴮ" => BTerm.Union
infixl:65 "∩ᴮ" => BTerm.Inter
-- infixl:65 "⨯ᴮ" => BTerm.CProd
infixl:65 "∈ᴮ" => BTerm.Mem
infixl:65 "↦ᴮ" => BTerm.Maplet
infixl:65 "+ᴮ" => BTerm.Add
infixl:65 "×ᴮ" => BTerm.Mul
infixl:65 "∧ᴮ" => BTerm.And
prefix:75 "¬ᴮ" => BTerm.Not
infixl:65 " =ᴮ " => BTerm.Eq
-- notation for Collect: {x . P | F} => Collect x P F
notation "{" x " : " P " ↦ " F "}" => BTerm.Collect x P F
infixl:65 " \\ᴮ " => BTerm.Diff

inductive BType where
  | ℙ
  | 𝔹
  | ℤ
  | Set : BType -> BType
  | Prod : BType -> BType -> BType
  deriving DecidableEq

infixr:65 "⨯ᴮ" => BType.Prod

def fv : BTerm -> List 𝒱
  | .var x => [x]
  | .bool _ => ∅
  | .int _ => ∅
  | e₁ ↦ᴮ e₂ => fv e₁ ++ fv e₂
  | e₁ +ᴮ e₂ => fv e₁ ++ fv e₂
  | e₁ ×ᴮ e₂ => fv e₁ ++ fv e₂
  | 𝒫 e => fv e
  | e₁ ∈ᴮ e₂ => fv e₁ ++ fv e₂
  | e₁ ∪ᴮ e₂ => fv e₁ ++ fv e₂
  | e₁ ∩ᴮ e₂ => fv e₁ ++ fv e₂
  | { x : P ↦ F } => (fv P ++ fv F).filter (· ≠ x)
  -- | e₁ ⨯ᴮ e₂ => fv e₁ ++ fv e₂
  | e₁ ∧ᴮ e₂ => fv e₁ ++ fv e₂
  | ¬ᴮ e => fv e
  | e₁ =ᴮ e₂ => fv e₁ ++ fv e₂
  | .UNIV => ∅
  | e₁ \ᴮ e₂ => fv e₁ ++ fv e₂

theorem and_or_right_distrib : (p ∨ q) ∧ r ↔ (p ∧ r) ∨ (q ∧ r) := by
  rw [iff_def]
  apply And.intro
  · intro h
    obtain ⟨hpoq, hr⟩ := h
    cases hpoq with
      | inl hp =>
        left
        exact ⟨hp, hr⟩
      | inr hq =>
        right
        exact ⟨hq, hr⟩
  · intro h
    apply Or.elim h
    · intro ⟨hp, hr⟩
      exact ⟨Or.inl hp, hr⟩
    · intro ⟨hq, hr⟩
      exact ⟨Or.inr hq, hr⟩

@[simp] theorem mem_append {a : α} {s t : List α} : a ∈ s ++ t ↔ a ∈ s ∨ a ∈ t := by
  induction s <;> simp_all [or_assoc]

theorem mem_append_eq (a : α) (s t : List α) : (a ∈ s ++ t) = (a ∈ s ∨ a ∈ t) :=
  propext mem_append

theorem fv_collect : v ∈ fv { x : P ↦ F } -> v ≠ x ∧ (v ∈ fv P ∨ v ∈ fv F) := by
  simp [fv, mem_append_eq, List.mem_filter, decide_eq_true, And.comm]

notation Γ "[" x " : " τ "]" => Batteries.AssocList.cons x τ Γ

inductive BTyping : Batteries.AssocList 𝒱 BType -> BTerm -> BType -> Prop where
  -- base types
  | var : Γ.find? x = some τ -> BTyping Γ (.var x) τ
  | bool : BTyping Γ (.bool b) .𝔹
  | int : BTyping Γ (.int n) .ℤ
  | Maplet : BTyping Γ e₁ τ -> BTyping Γ e₂ γ -> BTyping Γ (e₁ ↦ᴮ e₂) (τ ⨯ᴮ γ)
  -- arithmetic
  | Add : BTyping Γ e₁ .ℤ -> BTyping Γ e₂ .ℤ -> BTyping Γ (e₁ +ᴮ e₂) .ℤ
  | Mul : BTyping Γ e₁ .ℤ -> BTyping Γ e₂ .ℤ -> BTyping Γ (e₁ ×ᴮ e₂) .ℤ
  -- set theory
  | Pow : BTyping Γ S (.Set α) -> BTyping Γ (.Pow S) (.Set (.Set α))
  | Mem : BTyping Γ x α -> BTyping Γ S (.Set α) -> BTyping Γ (x ∈ᴮ S) ℙ
  | Union : BTyping Γ A (.Set α) -> BTyping Γ B (.Set α) -> BTyping Γ (A ∪ᴮ B) (.Set α)
  | Inter : BTyping Γ A (.Set α) -> BTyping Γ B (.Set α) -> BTyping Γ (A ∩ᴮ B) (.Set α)
  | Collect :
      BTyping (Γ[x : τ]) P .ℙ ->
      x ∈ fv P ->
      BTyping (Γ[x : τ]) F β ->
      BTyping Γ (.Collect x P F) (.Set β)
  -- | CProd : BTyping Γ A (.Set α) -> BTyping Γ B (.Set β) -> BTyping Γ (A ⨯ᴮ B) (.Set (α ⨯ᴮ β))
  | UNIV : BTyping Γ .UNIV (.Set α)
  | Diff : BTyping Γ A (.Set α) -> BTyping Γ B (.Set α) -> BTyping Γ (A \ᴮ B) (.Set α)
  -- logic
  | And : BTyping Γ e₁ ℙ -> BTyping Γ e₂ ℙ -> BTyping Γ (e₁ ∧ᴮ e₂) ℙ
  | Not : BTyping Γ e ℙ -> BTyping Γ (¬ᴮ e) ℙ
  | Eq : BTyping Γ e₁ τ -> BTyping Γ e₂ τ -> BTyping Γ (e₁ =ᴮ e₂) ℙ

notation:10 Γ " ⊢ " e " : " τ => BTyping Γ e τ

theorem mem_append : x ∈ fv e₁ ++ fv e₂ ↔ x ∈ fv e₁ ∨ x ∈ fv e₂ := by
  induction fv e₁ with
    | nil => simp
    | cons y ys IH =>
      calc
        x ∈ y :: ys ++ fv e₂ ↔ x = y ∨ x ∈ ys ++ fv e₂ := by simp
        _ ↔ x = y ∨ x ∈ ys ∨ x ∈ fv e₂ := by rw [IH]
        _ ↔ x ∈ y :: ys ∨ x ∈ fv e₂ := by simp [<- or_assoc]

theorem not_mem_append : ¬ x ∈ fv e₁ ++ fv e₂ ↔ ¬ x ∈ fv e₁ ∧ ¬ x ∈ fv e₂ := by
  simp [not_congr mem_append]

theorem typctx_weakening (typ : Γ ⊢ e : σ) (h : x ∉ fv e) : Γ[x : τ] ⊢ e : σ := by
  induction e generalizing Γ σ with
    | var y =>
      apply BTyping.var
      obtain ⟨h₁⟩ := typ
      simp [fv] at h
      unfold Batteries.AssocList.find?
      cases h₂ : x == y with
        | false => exact h₁
        | true =>
          let _ := LawfulBEq.eq_of_beq h₂
          contradiction
    | bool b =>
      obtain ⟨⟩ := typ
      exact BTyping.bool
    | int n =>
      obtain ⟨⟩ := typ
      exact BTyping.int
    | Maplet e₁ e₂ ih₁ ih₂ =>
      obtain _ | _ | _ | ⟨ih₁', ih₂'⟩ := typ
      apply BTyping.Maplet
      all_goals
        obtain ⟨h₁, h₂⟩ := not_mem_append.mp h
        first | exact ih₁ ih₁' h₁ | exact ih₂ ih₂' h₂
    | Add e₁ e₂ ih₁ ih₂ =>
      obtain _ | _ | _ | _ | ⟨ih₁', ih₂'⟩ := typ
      apply BTyping.Add
      all_goals
        obtain ⟨h₁, h₂⟩ := not_mem_append.mp h
        first | exact ih₁ ih₁' h₁ | exact ih₂ ih₂' h₂
    | Mul e₁ e₂ ih₁ ih₂ =>
      obtain _ | _ | _ | _ | _ | ⟨ih₁', ih₂'⟩ := typ
      apply BTyping.Mul
      all_goals
        obtain ⟨h₁, h₂⟩ := not_mem_append.mp h
        first | exact ih₁ ih₁' h₁ | exact ih₂ ih₂' h₂
    | Pow e ih =>
      obtain _ | _ | _ | _ | _ | _ | ⟨ih'⟩ := typ
      apply BTyping.Pow
      exact ih ih' h
    | Mem x S ih₁ ih₂ =>
      obtain _ | _ | _ | _ | _ | _ | _ | ⟨ih₁', ih₂'⟩ := typ
      apply BTyping.Mem
      all_goals
        obtain ⟨h₁, h₂⟩ := not_mem_append.mp h
        first | exact ih₁ ih₁' h₁ | exact ih₂ ih₂' h₂
    | Union A B ih₁ ih₂ =>
      obtain _ | _ | _ | _ | _ | _ | _ | _ | ⟨ih₁', ih₂'⟩ := typ
      apply BTyping.Union
      all_goals
        obtain ⟨h₁, h₂⟩ := not_mem_append.mp h
        first | exact ih₁ ih₁' h₁ | exact ih₂ ih₂' h₂
    | Inter A B ih₁ ih₂ =>
      obtain _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨ih₁', ih₂'⟩ := typ
      apply BTyping.Inter
      all_goals
        obtain ⟨h₁, h₂⟩ := not_mem_append.mp h
        first | exact ih₁ ih₁' h₁ | exact ih₂ ih₂' h₂
    | Collect y P F ih₁ ih₂ =>
      obtain _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨ih₁', ih₂', ih₃'⟩ := typ
      apply BTyping.Collect
      · obtain ⟨xy⟩ := fv_collect_neg.mp h
    | UNIV =>
      obtain ⟨⟩ := typ
      exact BTyping.UNIV
    | Diff A B ih₁ ih₂ =>
      obtain _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨ih₁', ih₂'⟩ := typ
      apply BTyping.Diff
      all_goals
        obtain ⟨h₁, h₂⟩ := not_mem_append.mp h
        first | exact ih₁ ih₁' h₁ | exact ih₂ ih₂' h₂
    | And e₁ e₂ ih₁ ih₂ =>
      obtain _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨ih₁', ih₂'⟩ := typ
      apply BTyping.And
      all_goals
        obtain ⟨h₁, h₂⟩ := not_mem_append.mp h
        first | exact ih₁ ih₁' h₁ | exact ih₂ ih₂' h₂
    | Not e ih =>
      obtain _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨ih'⟩ := typ
      apply BTyping.Not
      exact ih ih' h
    | Eq e₁ e₂ ih₁ ih₂ =>
      obtain _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨ih₁', ih₂'⟩ := typ
      apply BTyping.Eq
      all_goals
        obtain ⟨h₁, h₂⟩ := not_mem_append.mp h
        first | exact ih₁ ih₁' h₁ | exact ih₂ ih₂' h₂

end BSyntax

namespace SyntacticSugar

open BSyntax

def Forall (x : 𝒱) (A : BTerm) (P : BTerm) : BTerm :=
  { x : .var x ∈ᴮ A ∧ᴮ P ↦ .var x } =ᴮ A

theorem ForallTyping (h₁ : Γ ⊢ A : .Set α) (h₂ : Γ[x : α] ⊢ P : .ℙ) (wf : x ∉ fv A) : Γ ⊢ Forall x A P : .ℙ := by
  unfold Forall
  apply BTyping.Eq
  · apply BTyping.Collect (τ := α)
    · apply BTyping.And
      · apply BTyping.Mem
        · apply BTyping.var
          simp [Batteries.AssocList.find?]
          rfl
        · exact h₁
  apply BTyping.Collect

def Compl : BTerm -> BTerm := (.UNIV \ᴮ ·)

-- A ⨯ B = {x . x = (a, b) ∧ a ∈ A ∧ b ∈ B | a ↦ b}
def CProd (A B : BTerm) : BTerm :=
  { "x" : ∃ᴮ a, ∃ᴮ b, .var "x" =ᴮ (.var "a" ↦ᴮ .var "b") ∧ᴮ (.var "a" ∈ᴮ A) ∧ᴮ (.var "b" ∈ᴮ B) ↦ .var "x" }


end SyntacticSugar

namespace BExample
open BSyntax
-- checks that {x . x = 1 | x * x} has type Set ℤ
example : ∅ ⊢ { "x" : (.var "x" =ᴮ .int 1) ↦ (.var "x" ×ᴮ .var "x") } : .Set .ℤ := by
  apply BTyping.Collect (τ := .ℤ)
  · apply BTyping.Eq
    · exact BTyping.var (by rfl)
    · exact BTyping.int
  · simp [fv]
  · apply BTyping.Mul <;> exact BTyping.var (by rfl)

end BExample
