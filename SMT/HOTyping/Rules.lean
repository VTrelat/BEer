import SMT.HOTyping.Def
import Mathlib.Tactic.MkIffOfInductiveProp

namespace SMT.PHOAS

section
set_option hygiene false
local notation:90 Γ:90 " ⊢ " x " : " τ:90 => Typing Γ x τ

inductive Typing.{u} {𝒱 : Type u} [DecidableEq 𝒱] : TypeContext 𝒱 → Term 𝒱 → SMTType → Prop where
  | var (Γ) (v τ) :
      Γ v = some τ
    ----------------
    → Γ ⊢ .var v : τ
  | int (Γ) (n : Int) : Γ ⊢ .int n : .int
  | bool (Γ) (b : Bool) : Γ ⊢ .bool b : .bool
  | app (Γ) (f x τ σ) :
      Γ ⊢ f : .fun τ σ
    → Γ ⊢ x : τ
    ------------------
    → Γ ⊢ .app f x : σ
  | lambda (Γ) {n} (τs : Fin n → SMTType) (t : (Fin n → 𝒱) → Term 𝒱) (γ) :
      (∀ vs, (Γ.update vs τs) ⊢ t vs : γ)
    → (n_pos : 0 < n)
    ------------------------------
    → Γ ⊢ .lambda τs t : .fun (Fin.foldr (n-1) (fun ⟨i, hi⟩ acc ↦ (τs ⟨i, Nat.lt_of_lt_pred hi⟩).pair acc) (τs ⟨n-1, Nat.sub_one_lt_of_lt n_pos⟩)) γ
  | forall (Γ) {n} (τs : Fin n → SMTType) (P : (Fin n → 𝒱) → Term 𝒱) :
      (∀ vs, (Γ.update vs τs) ⊢ P vs : .bool)
    → (n_pos : 0 < n)
    ------------------------------
    → Γ ⊢ .forall τs P : .bool
  -- | exists (Γ) {n} (τs : Fin n → SMTType) (P : (Fin n → 𝒱) → Term 𝒱) :
  --     (∀ vs, (Γ.update vs τs) ⊢ P vs : .bool)
  --   → (n_pos : 0 < n)
  --   ------------------------------
  --   → Γ ⊢ .exists τs P : .bool
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
  -- | or (Γ) (t₁ t₂) :
  --     Γ ⊢ t₁ : .bool
  --   → Γ ⊢ t₂ : .bool
  --   -----------------------
  --   → Γ ⊢ .or t₁ t₂ : .bool
  | not (Γ) (t) :
      Γ ⊢ t : .bool
    --------------------
    → Γ ⊢ .not t : .bool
  -- | imp (Γ) (t₁ t₂) :
  --     Γ ⊢ t₁ : .bool
  --   → Γ ⊢ t₂ : .bool
  --   ------------------------
  --   → Γ ⊢ .imp t₁ t₂ : .bool
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
  | none (Γ τ) : Γ ⊢ .none τ : .option τ
  | «()» (Γ) : Γ ⊢ .«()» : .unit
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
  | distinct {n : ℕ} (Γ) (ts : Fin n → Term 𝒱) (τ) :
      (∀ i : Fin n, Γ ⊢ ts i : τ)
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

--NOTE: ⚠️ Typing isn't deterministic: ∀ τ, Γ ⊢ none : .option τ
  --NOTE: Now it is!

section InversionRules
namespace Typing

theorem varE      {𝒱} [DecidableEq 𝒱] {Γ : TypeContext 𝒱} {v τ} : Γ ⊢ .var v : τ → Γ v = .some τ := λ | var _ _ _ h => h
theorem intE      {𝒱} [DecidableEq 𝒱] {Γ : TypeContext 𝒱} {n τ} : Γ ⊢ .int n : τ → τ = .int := λ | int _ _ => rfl
theorem boolE     {𝒱} [DecidableEq 𝒱] {Γ : TypeContext 𝒱} {b τ} : Γ ⊢ .bool b : τ → τ = .bool := λ | bool _ _ => rfl
theorem appE      {𝒱} [DecidableEq 𝒱] {Γ : TypeContext 𝒱} {f x σ} : Γ ⊢ .app f x : σ → ∃ τ, Γ ⊢ f : .fun τ σ ∧ Γ ⊢ x : τ := λ | app _ _ _ _ _ h₁ h₂ => ⟨_, h₁, h₂⟩
theorem eqE       {𝒱} [DecidableEq 𝒱] {Γ : TypeContext 𝒱} {x y τ} : Γ ⊢ .eq x y : τ → τ = .bool ∧ ∃ σ, Γ ⊢ x : σ ∧ Γ ⊢ y : σ := λ | eq _ _ _ _ hx hy => ⟨rfl, _, hx, hy⟩
theorem andE      {𝒱} [DecidableEq 𝒱] {Γ : TypeContext 𝒱} {x y τ} : Γ ⊢ .and x y : τ → τ = .bool ∧ Γ ⊢ x : .bool ∧ Γ ⊢ y : .bool := λ | and _ _ _ hx hy => ⟨rfl, hx, hy⟩
theorem notE      {𝒱} [DecidableEq 𝒱] {Γ : TypeContext 𝒱} {x τ} : Γ ⊢ .not x : τ → τ = .bool ∧ Γ ⊢ x : .bool := λ | not _ _ h => ⟨rfl, h⟩
theorem iteE      {𝒱} [DecidableEq 𝒱] {Γ : TypeContext 𝒱} {c t f τ} : Γ ⊢ .ite c t f : τ → Γ ⊢ c : .bool ∧ Γ ⊢ t : τ ∧ Γ ⊢ f : τ := λ | ite _ _ _ _ _ hc ht hf => ⟨hc,ht,hf⟩
theorem someE     {𝒱} [DecidableEq 𝒱] {Γ : TypeContext 𝒱} {t τ} : Γ ⊢ .some t : τ → ∃ σ, τ = .option σ ∧ Γ ⊢ t : σ := λ | some _ _ _ h => ⟨_, rfl, h⟩
theorem theE      {𝒱} [DecidableEq 𝒱] {Γ : TypeContext 𝒱} {t τ} : Γ ⊢ .the t : τ → Γ ⊢ t : τ.option := λ | the _ _ _ ht => ht
theorem noneE     {𝒱} [DecidableEq 𝒱] {Γ : TypeContext 𝒱} {τ ξ} : Γ ⊢ .none ξ : τ → τ = .option ξ := λ | none .. => rfl
theorem unitE     {𝒱} [DecidableEq 𝒱] {Γ : TypeContext 𝒱} {τ} : Γ ⊢ .«()» : τ → τ = .unit := λ | «()» .. => rfl
theorem pairE     {𝒱} [DecidableEq 𝒱] {Γ : TypeContext 𝒱} {x y τ} : Γ ⊢ .pair x y : τ → ∃ α β, τ = .pair α β ∧ Γ ⊢ x : α ∧ Γ ⊢ y : β := λ | pair _ _ _ _ _ hx hy => ⟨_,_,rfl,hx,hy⟩
theorem fstE      {𝒱} [DecidableEq 𝒱] {Γ : TypeContext 𝒱} {x τ} : Γ ⊢ .fst x : τ → ∃ σ, Γ ⊢ x : .pair τ σ := λ | fst _ _ _ _ hx => ⟨_,hx⟩
theorem sndE      {𝒱} [DecidableEq 𝒱] {Γ : TypeContext 𝒱} {x τ} : Γ ⊢ .snd x : τ → ∃ σ, Γ ⊢ x : .pair σ τ := λ | snd _ _ _ _ hx => ⟨_,hx⟩
theorem distinctE {𝒱} [DecidableEq 𝒱] {Γ : TypeContext 𝒱} {n : ℕ} {xs : Fin n → Term 𝒱} {τ} : Γ ⊢ .distinct xs : τ → τ = .bool ∧ ∃ σ, ∀ i, Γ ⊢ xs i : σ := λ | distinct _ _ σ h => ⟨rfl, σ, h⟩
theorem leE       {𝒱} [DecidableEq 𝒱] {Γ : TypeContext 𝒱} {x y τ} : Γ ⊢ .le x y : τ → τ = .bool ∧ Γ ⊢ x : .int ∧ Γ ⊢ y : .int := λ | le _ _ _ hx hy => ⟨rfl,hx,hy⟩
theorem addE      {𝒱} [DecidableEq 𝒱] {Γ : TypeContext 𝒱} {x y τ} : Γ ⊢ .add x y : τ → τ = .int ∧ Γ ⊢ x : .int ∧ Γ ⊢ y : .int := λ | add _ _ _ hx hy => ⟨rfl,hx,hy⟩
theorem subE      {𝒱} [DecidableEq 𝒱] {Γ : TypeContext 𝒱} {x y τ} : Γ ⊢ .sub x y : τ → τ = .int ∧ Γ ⊢ x : .int ∧ Γ ⊢ y : .int := λ | sub _ _ _ hx hy => ⟨rfl,hx,hy⟩
theorem mulE      {𝒱} [DecidableEq 𝒱] {Γ : TypeContext 𝒱} {x y τ} : Γ ⊢ .mul x y : τ → τ = .int ∧ Γ ⊢ x : .int ∧ Γ ⊢ y : .int := λ | mul _ _ _ hx hy => ⟨rfl,hx,hy⟩
theorem lambdaE   {𝒱} [DecidableEq 𝒱] {Γ : TypeContext 𝒱} {n} {τs : Fin n → SMTType} {t : (Fin n → 𝒱) → Term 𝒱} {τ} : (h : Γ ⊢ .lambda τs t : τ) → 0 < n ∧ ∃ γ, τ = .fun (Fin.foldr (n-1) (fun ⟨i, hi⟩ acc ↦ (τs ⟨i, Nat.lt_of_lt_pred hi⟩).pair acc) (τs ⟨n-1, match h with | lambda _ _ _ _ _ h => Nat.sub_one_lt_of_lt h⟩)) γ ∧ (∀ vs, (Γ.update vs τs) ⊢ t vs : γ) := λ | .lambda _ _ _ γ typt n_pos => ⟨n_pos, γ, rfl, typt⟩
theorem forallE   {𝒱} [DecidableEq 𝒱] {Γ : TypeContext 𝒱} {n} {τs : Fin n → SMTType} {P : (Fin n → 𝒱) → Term 𝒱} {τ} : Γ ⊢ .forall τs P : τ → 0 < n ∧ τ = .bool ∧ (∀ vs, (Γ.update vs τs) ⊢ P vs : .bool) := λ | .forall _ _ _ h n_pos => ⟨n_pos, rfl, h⟩
-- theorem orE       {𝒱} [DecidableEq 𝒱] {Γ : TypeContext 𝒱} {x y τ} : Γ ⊢ .or x y : τ → τ = .bool ∧ Γ ⊢ x : .bool ∧ Γ ⊢ y : .bool := λ | or _ _ _ hx hy => ⟨rfl, hx, hy⟩
-- theorem impE      {𝒱} [DecidableEq 𝒱] {Γ : TypeContext 𝒱} {x y τ} : Γ ⊢ .imp x y : τ → τ = .bool ∧ Γ ⊢ x : .bool ∧ Γ ⊢ y : .bool := λ | imp _ _ _ hx hy => ⟨rfl, hx, hy⟩
-- theorem existsE   {𝒱} [DecidableEq 𝒱] {Γ : TypeContext 𝒱} {n} {τs : Fin n → SMTType} {P : (Fin n → 𝒱) → Term 𝒱} {τ} : Γ ⊢ .exists τs P : τ → 0 < n ∧ τ = .bool ∧ (∀ vs, (Γ.update vs τs) ⊢ P vs : .bool) := λ | .exists _ _ _ h n_pos => ⟨n_pos, rfl, h⟩

end Typing
end InversionRules

instance {n} {𝒱} [Inhabited 𝒱] : Inhabited (Fin n → 𝒱) := inferInstance

theorem Typing.det {𝒱} [DecidableEq 𝒱] [Inhabited 𝒱] {Γ : TypeContext 𝒱} {t : Term 𝒱} {τ σ : SMTType} :
    Γ ⊢ t : τ → Γ ⊢ t : σ → τ = σ := by
  intro typ_τ typ_σ
  induction t generalizing Γ τ σ with
  | var v =>
    apply Typing.varE at typ_τ
    apply Typing.varE at typ_σ
    rw [typ_τ] at typ_σ
    injections typ_σ
  | int n =>
    obtain ⟨⟩ := Typing.intE typ_τ
    obtain ⟨⟩ := Typing.intE typ_σ
    rfl
  | bool b =>
    obtain ⟨⟩ := Typing.boolE typ_τ
    obtain ⟨⟩ := Typing.boolE typ_σ
    rfl
  | app f x f_ih x_ih =>
    obtain ⟨_, typ_f₁, -⟩ := Typing.appE typ_τ
    obtain ⟨_, typ_f₂, -⟩ := Typing.appE typ_σ
    obtain ⟨⟩ := f_ih typ_f₁ typ_f₂
    rfl
  | not t ih =>
    obtain ⟨rfl⟩ := Typing.notE typ_τ
    obtain ⟨rfl⟩ := Typing.notE typ_σ
    rfl
  | eq t₁ t₂ t₁_ih t₂_ih =>
    obtain ⟨rfl⟩ := Typing.eqE typ_τ
    obtain ⟨rfl⟩ := Typing.eqE typ_σ
    rfl
  | and t₁ t₂ t₁_ih t₂_ih =>
    obtain ⟨rfl⟩ := Typing.andE typ_τ
    obtain ⟨rfl⟩ := Typing.andE typ_σ
    rfl
  | some t ih =>
    obtain ⟨_, rfl, _⟩ := Typing.someE typ_τ
    obtain ⟨_, rfl, _⟩ := Typing.someE typ_σ
    congr
    apply ih ‹_› ‹_›
  | the t ih =>
    replace typ_τ := Typing.theE typ_τ
    replace typ_σ := Typing.theE typ_σ
    injection ih typ_τ typ_σ
  | none τ =>
    obtain ⟨⟩ := Typing.noneE typ_τ
    obtain ⟨⟩ := Typing.noneE typ_σ
    rfl
  | «()» =>
    obtain ⟨⟩ := Typing.unitE typ_τ
    obtain ⟨⟩ := Typing.unitE typ_σ
    rfl
  | pair t₁ t₂ t₁_ih t₂_ih =>
    obtain ⟨_, _, rfl, _, _⟩ := Typing.pairE typ_τ
    obtain ⟨_, _, rfl, _, _⟩ := Typing.pairE typ_σ
    congr
    · apply t₁_ih ‹_› ‹_›
    · apply t₂_ih ‹_› ‹_›
  | fst t ih =>
    obtain ⟨_, typ_τ⟩ := Typing.fstE typ_τ
    obtain ⟨_, typ_σ⟩ := Typing.fstE typ_σ
    injection ih typ_τ typ_σ
  | snd t ih =>
    obtain ⟨_, typ_τ⟩ := Typing.sndE typ_τ
    obtain ⟨_, typ_σ⟩ := Typing.sndE typ_σ
    injection ih typ_τ typ_σ
  | le t₁ t₂ t₁_ih t₂_ih =>
    obtain ⟨rfl, _, _⟩ := Typing.leE typ_τ
    obtain ⟨rfl, _, _⟩ := Typing.leE typ_σ
    rfl
  | add t₁ t₂ t₁_ih t₂_ih =>
    obtain ⟨rfl, _, _⟩ := Typing.addE typ_τ
    obtain ⟨rfl, _, _⟩ := Typing.addE typ_σ
    rfl
  | sub t₁ t₂ t₁_ih t₂_ih =>
    obtain ⟨rfl, _, _⟩ := Typing.subE typ_τ
    obtain ⟨rfl, _, _⟩ := Typing.subE typ_σ
    rfl
  | mul t₁ t₂ t₁_ih t₂_ih =>
    obtain ⟨rfl, _, _⟩ := Typing.mulE typ_τ
    obtain ⟨rfl, _, _⟩ := Typing.mulE typ_σ
    rfl
  | distinct ts ih =>
    obtain ⟨rfl, _, _⟩ := Typing.distinctE typ_τ
    obtain ⟨rfl, _, _⟩ := Typing.distinctE typ_σ
    rfl
  | ite _ t _ _ t_ih _ =>
    obtain ⟨-, typ_t, -⟩ := Typing.iteE typ_τ
    obtain ⟨-, typ_t', -⟩ := Typing.iteE typ_σ
    exact t_ih typ_t typ_t'
  | lambda τs t ih =>
    obtain ⟨n_pos, γ, τ_eq, typ_t⟩ := Typing.lambdaE typ_τ
    obtain ⟨-, γ', σ_eq, typ_t'⟩ := Typing.lambdaE typ_σ
    obtain rfl := ih default (typ_t _) (typ_t' _)
    rw [τ_eq, σ_eq]
  | «forall» τs t ih =>
    obtain ⟨n_pos, rfl, typ_t⟩ := Typing.forallE typ_τ
    obtain ⟨-, rfl, typ_t'⟩ := Typing.forallE typ_σ
    rfl
end SMT.PHOAS
