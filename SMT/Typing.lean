import SMT.Syntax
import SMT.PHOAS.SMTPHOAS
import SMT.HOTyping.Rules
import Mathlib.Data.List.Basic
import Extra.Utils

namespace SMT

abbrev TypeContext := AList fun _ : 𝒱 ↦ SMTType

def TypeContext.update (Γ : TypeContext) (vs : List 𝒱) (τs : List SMTType) (hlen : vs.length = τs.length := by assumption) : TypeContext :=
  Fin.foldl vs.length (fun Δ i ↦ Δ.insert vs[i] τs[i] ) Γ

open Classical in
noncomputable def TypeContext.abstract (Γ : TypeContext) {𝒯} [DecidableEq 𝒯] («Δ» : SMT.𝒱 → Option 𝒯) :
  PHOAS.TypeContext 𝒯 := fun x : 𝒯 =>
    if h : ∃ k, «Δ» k = .some x ∧ k ∈ Γ then
      Γ.lookup <| choose h
    else .none

section
set_option hygiene false
local notation:90 Γ:90 " ⊢ " x " : " τ:90 => Typing Γ x τ

inductive Typing : TypeContext → Term → SMTType → Prop where
  | var (Γ : TypeContext) (v τ) :
      Γ.lookup v = some τ
    ----------------
    → Γ ⊢ .var v : τ
  | int (Γ) (n : Int) : Γ ⊢ .int n : .int
  | bool (Γ) (b : Bool) : Γ ⊢ .bool b : .bool
  | app (Γ) (f x τ σ) :
      Γ ⊢ f : .fun τ σ
    → Γ ⊢ x : τ
    ------------------
    → Γ ⊢ .app f x : σ
  | lambda (Γ : TypeContext) (vs : List 𝒱) (τs : List SMTType) (t : Term) (γ) :
    (∀ v ∈ vs, v ∉ Γ)
    → (len_pos : 0 < vs.length)
    → (len_eq : vs.length = τs.length)
    → (Γ.update vs τs) ⊢ t : γ
    ------------------------------
    → Γ ⊢ .lambda vs τs t : (τs.dropLast.foldr (init := τs.getLast (by rwa [←List.length_pos_iff, ←len_eq])) fun τ acc ↦ τ.pair acc).fun γ
  | forall (Γ) (vs : List 𝒱) (τs : List SMTType) (P : Term) :
    (∀ v ∈ vs, v ∉ Γ)
    → (len_pos : 0 < vs.length)
    → (len_eq : vs.length = τs.length)
    → (Γ.update vs τs) ⊢ P : .bool
    ------------------------------
    → Γ ⊢ .forall vs τs P : .bool
  | exists (Γ) (vs : List 𝒱) (τs : List SMTType) (P : Term) :
    (∀ v ∈ vs, v ∉ Γ)
    → (len_pos : 0 < vs.length)
    → (len_eq : vs.length = τs.length)
    → (Γ.update vs τs) ⊢ P : .bool
    ------------------------------
    → Γ ⊢ .exists vs τs P : .bool
  | eq (Γ) (t₁ t₂ τ) :
      Γ ⊢ t₁ : τ
    → Γ ⊢ t₂ : τ
    -----------------------
    → Γ ⊢ .eq t₁ t₂ : .bool
  | and (Γ) (t₁ t₂) :
      Γ ⊢ t₁ : .bool
    → Γ ⊢ t₂ : .bool
    ------------------------
    → Γ ⊢ .and t₁ t₂ : .bool
  | or (Γ) (t₁ t₂) :
      Γ ⊢ t₁ : .bool
    → Γ ⊢ t₂ : .bool
    -----------------------
    → Γ ⊢ .or t₁ t₂ : .bool
  | not (Γ) (t) :
      Γ ⊢ t : .bool
    --------------------
    → Γ ⊢ .not t : .bool
  | imp (Γ) (t₁ t₂) :
      Γ ⊢ t₁ : .bool
    → Γ ⊢ t₂ : .bool
    ------------------------
    → Γ ⊢ .imp t₁ t₂ : .bool
  | ite (Γ) (c t e τ) :
      Γ ⊢ c : .bool
    → Γ ⊢ t : τ
    → Γ ⊢ e : τ
    --------------------
    → Γ ⊢ .ite c t e : τ
  | some (Γ) (t τ) :
      Γ ⊢ t : τ
    -----------------
    → Γ ⊢ .some t : .option τ
  | none (Γ τ) : Γ ⊢ .as .none (.option τ) : .option τ
  | the (Γ) (t τ) :
      Γ ⊢ t : .option τ
    -----------------
    → Γ ⊢ .the t : τ
  | pair (Γ) (t₁ τ₁ t₂ τ₂) :
      Γ ⊢ t₁ : τ₁
    → Γ ⊢ t₂ : τ₂
    -----------------------
    → Γ ⊢ .pair t₁ t₂ : .pair τ₁ τ₂
  | fst (Γ) (t τ σ) :
      Γ ⊢ t : .pair τ σ
    -------------------
    → Γ ⊢ .fst t : τ
  | snd (Γ) (t τ σ) :
      Γ ⊢ t : .pair τ σ
    -------------------
    → Γ ⊢ .snd t : σ
  | distinct (Γ) (ts : List Term) (τ) :
      (∀ t ∈ ts, Γ ⊢ t : τ)
    -------------------------
    → Γ ⊢ .distinct ts : .bool
  | le (Γ) (t₁ t₂) :
      Γ ⊢ t₁ : .int
    → Γ ⊢ t₂ : .int
    -----------------------
    → Γ ⊢ .le t₁ t₂ : .bool
  | add (Γ) (t₁ t₂) :
      Γ ⊢ t₁ : .int
    → Γ ⊢ t₂ : .int
    ------------------------
    → Γ ⊢ .add t₁ t₂ : .int
  | sub (Γ) (t₁ t₂) :
      Γ ⊢ t₁ : .int
    → Γ ⊢ t₂ : .int
    ------------------------
    → Γ ⊢ .sub t₁ t₂ : .int
  | mul (Γ) (t₁ t₂) :
      Γ ⊢ t₁ : .int
    → Γ ⊢ t₂ : .int
    ------------------------
    → Γ ⊢ .mul t₁ t₂ : .int
end

notation:90 Γ:90 " ⊢ " x " : " τ:90 => Typing Γ x τ


section RuleInversion
namespace Typing

theorem varE      {Γ : TypeContext} {v τ} : Γ ⊢ .var v : τ → Γ.lookup v = .some τ := λ | var _ _ _ h => h
theorem intE      {Γ : TypeContext} {n τ} : Γ ⊢ .int n : τ → τ = .int := λ | int _ _ => rfl
theorem boolE     {Γ : TypeContext} {b τ} : Γ ⊢ .bool b : τ → τ = .bool := λ | bool _ _ => rfl
theorem appE      {Γ : TypeContext} {f x σ} : Γ ⊢ .app f x : σ → ∃ τ, Γ ⊢ f : .fun τ σ ∧ Γ ⊢ x : τ := λ | app _ _ _ _ _ h₁ h₂ => ⟨_, h₁, h₂⟩
theorem eqE       {Γ : TypeContext} {x y τ} : Γ ⊢ .eq x y : τ → τ = .bool ∧ ∃ σ, Γ ⊢ x : σ ∧ Γ ⊢ y : σ := λ | eq _ _ _ _ hx hy => ⟨rfl, _, hx, hy⟩
theorem andE      {Γ : TypeContext} {x y τ} : Γ ⊢ .and x y : τ → τ = .bool ∧ Γ ⊢ x : .bool ∧ Γ ⊢ y : .bool := λ | and _ _ _ hx hy => ⟨rfl, hx, hy⟩
theorem orE       {Γ : TypeContext} {x y τ} : Γ ⊢ .or x y : τ → τ = .bool ∧ Γ ⊢ x : .bool ∧ Γ ⊢ y : .bool := λ | or _ _ _ hx hy => ⟨rfl, hx, hy⟩
theorem impE      {Γ : TypeContext} {x y τ} : Γ ⊢ .imp x y : τ → τ = .bool ∧ Γ ⊢ x : .bool ∧ Γ ⊢ y : .bool := λ | imp _ _ _ hx hy => ⟨rfl, hx, hy⟩
theorem notE      {Γ : TypeContext} {x τ} : Γ ⊢ .not x : τ → τ = .bool ∧ Γ ⊢ x : .bool := λ | not _ _ h => ⟨rfl, h⟩
theorem iteE      {Γ : TypeContext} {c t f τ} : Γ ⊢ .ite c t f : τ → Γ ⊢ c : .bool ∧ Γ ⊢ t : τ ∧ Γ ⊢ f : τ := λ | ite _ _ _ _ _ hc ht hf => ⟨hc,ht,hf⟩
theorem someE     {Γ : TypeContext} {t τ} : Γ ⊢ .some t : τ → ∃ σ, τ = .option σ ∧ Γ ⊢ t : σ := λ | some _ _ _ h => ⟨_, rfl, h⟩
theorem theE      {Γ : TypeContext} {t τ} : Γ ⊢ .the t : τ → Γ ⊢ t : τ.option := λ | the _ _ _ ht => ht
theorem asE       {Γ : TypeContext} {t ξ τ} : Γ ⊢ .as t ξ : τ → t = .none ∧ ξ = τ ∧ ∃ ζ, τ = .option ζ := λ | .none .. => ⟨rfl, rfl, _, rfl⟩
theorem noneE     {Γ : TypeContext} {τ} : ¬ Γ ⊢ .none : τ := by rintro ⟨⟩
theorem pairE     {Γ : TypeContext} {x y τ} : Γ ⊢ .pair x y : τ → ∃ α β, τ = .pair α β ∧ Γ ⊢ x : α ∧ Γ ⊢ y : β := λ | pair _ _ _ _ _ hx hy => ⟨_,_,rfl,hx,hy⟩
theorem fstE      {Γ : TypeContext} {x τ} : Γ ⊢ .fst x : τ → ∃ σ, Γ ⊢ x : .pair τ σ := λ | fst _ _ _ _ hx => ⟨_,hx⟩
theorem sndE      {Γ : TypeContext} {x τ} : Γ ⊢ .snd x : τ → ∃ σ, Γ ⊢ x : .pair σ τ := λ | snd _ _ _ _ hx => ⟨_,hx⟩
theorem distinctE {Γ : TypeContext} {xs : List Term} {τ} : Γ ⊢ .distinct xs : τ → τ = .bool ∧ ∃ σ, ∀ x ∈ xs, Γ ⊢ x : σ := λ | distinct _ _ σ h => ⟨rfl, σ, h⟩
theorem leE       {Γ : TypeContext} {x y τ} : Γ ⊢ .le x y : τ → τ = .bool ∧ Γ ⊢ x : .int ∧ Γ ⊢ y : .int := λ | le _ _ _ hx hy => ⟨rfl,hx,hy⟩
theorem addE      {Γ : TypeContext} {x y τ} : Γ ⊢ .add x y : τ → τ = .int ∧ Γ ⊢ x : .int ∧ Γ ⊢ y : .int := λ | add _ _ _ hx hy => ⟨rfl,hx,hy⟩
theorem subE      {Γ : TypeContext} {x y τ} : Γ ⊢ .sub x y : τ → τ = .int ∧ Γ ⊢ x : .int ∧ Γ ⊢ y : .int := λ | sub _ _ _ hx hy => ⟨rfl,hx,hy⟩
theorem mulE      {Γ : TypeContext} {x y τ} : Γ ⊢ .mul x y : τ → τ = .int ∧ Γ ⊢ x : .int ∧ Γ ⊢ y : .int := λ | mul _ _ _ hx hy => ⟨rfl,hx,hy⟩
theorem lambdaE   {Γ : TypeContext} {vs : List 𝒱} {τs : List SMTType} {t : Term} {τ} (h : Γ ⊢ .lambda vs τs t : τ) :
  ∃ (len_pos : 0 < vs.length) (len_eq : vs.length = τs.length) (γ : SMTType),
    (∀ v ∈ vs, v ∉ Γ) ∧ τ = (τs.dropLast.foldr (init := τs.getLast (by rwa [←List.length_pos_iff, ←len_eq])) fun τ acc ↦ τ.pair acc).fun γ ∧ (Γ.update vs τs) ⊢ t : γ := by
  obtain ⟨⟩ := h
  exists ‹_›, ‹_›, ‹_›
theorem forallE   {Γ : TypeContext} {vs : List 𝒱} {τs : List SMTType} {P : Term} {τ} (h : Γ ⊢ .forall vs τs P : τ) :
  τ = .bool ∧ (∀ v ∈ vs, v ∉ Γ) ∧ ∃ (_ : 0 < vs.length) (len_eq : vs.length = τs.length), Γ.update vs τs ⊢ P : .bool := by
    obtain ⟨⟩ := h
    apply And.intro rfl
    apply And.intro ‹_›
    exists ‹_›, ‹_›
theorem existsE   {Γ : TypeContext} {vs : List 𝒱} {τs : List SMTType} {P : Term} {τ} (h : Γ ⊢ .exists vs τs P : τ) :
  τ = .bool ∧ (∀ v ∈ vs, v ∉ Γ) ∧ ∃ (_ : 0 < vs.length) (len_eq : vs.length = τs.length), Γ.update vs τs ⊢ P : .bool := by
    obtain ⟨⟩ := h
    apply And.intro rfl
    apply And.intro ‹_›
    exists ‹_›, ‹_›

end Typing
end RuleInversion

end SMT
