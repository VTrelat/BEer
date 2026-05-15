import SMT.HOTyping.Def

namespace SMT.PHOAS

section
set_option hygiene false
local notation:90 Γ:90 " ⊢ˢ' " x " : " τ:90 => Typing Γ x τ

inductive Typing.{u} {𝒱 : Type u} [DecidableEq 𝒱] [HasType 𝒱] : TypeContext 𝒱 → Term 𝒱 → SMTType → Prop where
  | var (Γ) (v τ) :
      Γ v = some τ
    ----------------
    → Γ ⊢ˢ' .var v : τ
  | int (Γ) (n : Int) : Γ ⊢ˢ' .int n : .int
  | bool (Γ) (b : Bool) : Γ ⊢ˢ' .bool b : .bool
  | app (Γ) (f x τ σ) :
      Γ ⊢ˢ' f : .fun τ σ
    → Γ ⊢ˢ' x : τ
    ------------------
    → Γ ⊢ˢ' .app f x : σ
  | lambda (Γ) {n} (τs : Fin n → SMTType) (t : (Fin n → 𝒱) → Term 𝒱) (γ) :
      (∀ vs, (vs_typed : ∀ i, SMT.PHOAS.HasType.type (vs i) = τs i)
        → (Γ.update vs τs) ⊢ˢ' t vs : γ)
    → (n_pos : 0 < n)
    ------------------------------
    → Γ ⊢ˢ' .lambda τs t : .fun (Fin.foldr (n-1) (fun ⟨i, hi⟩ acc ↦ (τs ⟨i, Nat.lt_of_lt_pred hi⟩).pair acc) (τs ⟨n-1, Nat.sub_one_lt_of_lt n_pos⟩)) γ
  | forall (Γ) {n} (τs : Fin n → SMTType) (P : (Fin n → 𝒱) → Term 𝒱) :
      (∀ vs, (vs_typed : ∀ i, SMT.PHOAS.HasType.type (vs i) = τs i)
        → (Γ.update vs τs) ⊢ˢ' P vs : .bool)
    → (n_pos : 0 < n)
    ------------------------------
    → Γ ⊢ˢ' .forall τs P : .bool
  -- | exists (Γ) {n} (τs : Fin n → SMTType) (P : (Fin n → 𝒱) → Term 𝒱) :
  --     (∀ vs, (Γ.update vs τs) ⊢ˢ' P vs : .bool)
  --   → (n_pos : 0 < n)
  --   ------------------------------
  --   → Γ ⊢ˢ' .exists τs P : .bool
  | eq (Γ) (t₁ t₂ τ) :
      Γ ⊢ˢ' t₁ : τ
    → Γ ⊢ˢ' t₂ : τ
    -----------------------
    → Γ ⊢ˢ' .eq t₁ t₂ : .bool
  | and (Γ) (t₁ t₂) :
      Γ ⊢ˢ' t₁ : .bool
    → Γ ⊢ˢ' t₂ : .bool
    ------------------------
    → Γ ⊢ˢ' .and t₁ t₂ : .bool
  -- | or (Γ) (t₁ t₂) :
  --     Γ ⊢ˢ' t₁ : .bool
  --   → Γ ⊢ˢ' t₂ : .bool
  --   -----------------------
  --   → Γ ⊢ˢ' .or t₁ t₂ : .bool
  | not (Γ) (t) :
      Γ ⊢ˢ' t : .bool
    --------------------
    → Γ ⊢ˢ' .not t : .bool
  -- | imp (Γ) (t₁ t₂) :
  --     Γ ⊢ˢ' t₁ : .bool
  --   → Γ ⊢ˢ' t₂ : .bool
  --   ------------------------
  --   → Γ ⊢ˢ' .imp t₁ t₂ : .bool
  | ite (Γ) (c t e τ) :
      Γ ⊢ˢ' c : .bool
    → Γ ⊢ˢ' t : τ
    → Γ ⊢ˢ' e : τ
    --------------------
    → Γ ⊢ˢ' .ite c t e : τ
  | some (Γ) (t τ) :
      Γ ⊢ˢ' t : τ
    -----------------
    → Γ ⊢ˢ' .some t : .option τ
  | none (Γ τ) : Γ ⊢ˢ' .none τ : .option τ
  | «()» (Γ) : Γ ⊢ˢ' .«()» : .unit
  | the (Γ) (t τ) :
      Γ ⊢ˢ' t : .option τ
    -----------------
    → Γ ⊢ˢ' .the t : τ
  | pair (Γ) (t₁ τ₁ t₂ τ₂) :
      Γ ⊢ˢ' t₁ : τ₁
    → Γ ⊢ˢ' t₂ : τ₂
    -----------------------
    → Γ ⊢ˢ' .pair t₁ t₂ : .pair τ₁ τ₂
  | fst (Γ) (t τ σ) :
      Γ ⊢ˢ' t : .pair τ σ
    -------------------
    → Γ ⊢ˢ' .fst t : τ
  | snd (Γ) (t τ σ) :
      Γ ⊢ˢ' t : .pair τ σ
    -------------------
    → Γ ⊢ˢ' .snd t : σ
  | distinct {n : ℕ} (Γ) (ts : Fin n → Term 𝒱) (τ) :
      (∀ i : Fin n, Γ ⊢ˢ' ts i : τ)
    -------------------------
    → Γ ⊢ˢ' .distinct ts : .bool
  | le (Γ) (t₁ t₂) :
      Γ ⊢ˢ' t₁ : .int
    → Γ ⊢ˢ' t₂ : .int
    -----------------------
    → Γ ⊢ˢ' .le t₁ t₂ : .bool
  | add (Γ) (t₁ t₂) :
      Γ ⊢ˢ' t₁ : .int
    → Γ ⊢ˢ' t₂ : .int
    ------------------------
    → Γ ⊢ˢ' .add t₁ t₂ : .int
  | sub (Γ) (t₁ t₂) :
      Γ ⊢ˢ' t₁ : .int
    → Γ ⊢ˢ' t₂ : .int
    ------------------------
    → Γ ⊢ˢ' .sub t₁ t₂ : .int
  | mul (Γ) (t₁ t₂) :
      Γ ⊢ˢ' t₁ : .int
    → Γ ⊢ˢ' t₂ : .int
    ------------------------
    → Γ ⊢ˢ' .mul t₁ t₂ : .int
end

notation:90 Γ:90 " ⊢ˢ' " x " : " τ:90 => Typing Γ x τ

--NOTE: ⚠️ Typing isn't deterministic: ∀ τ, Γ ⊢ˢ' none : .option τ
  --NOTE: Now it is!

section InversionRules
namespace Typing

theorem varE      {𝒱} [DecidableEq 𝒱] [HasType 𝒱] {Γ : TypeContext 𝒱} {v τ} : Γ ⊢ˢ' .var v : τ → Γ v = .some τ := λ | var _ _ _ h => h
theorem intE      {𝒱} [DecidableEq 𝒱] [HasType 𝒱] {Γ : TypeContext 𝒱} {n τ} : Γ ⊢ˢ' .int n : τ → τ = .int := λ | int _ _ => rfl
theorem boolE     {𝒱} [DecidableEq 𝒱] [HasType 𝒱] {Γ : TypeContext 𝒱} {b τ} : Γ ⊢ˢ' .bool b : τ → τ = .bool := λ | bool _ _ => rfl
theorem appE      {𝒱} [DecidableEq 𝒱] [HasType 𝒱] {Γ : TypeContext 𝒱} {f x σ} : Γ ⊢ˢ' .app f x : σ → ∃ τ, Γ ⊢ˢ' f : .fun τ σ ∧ Γ ⊢ˢ' x : τ := λ | app _ _ _ _ _ h₁ h₂ => ⟨_, h₁, h₂⟩
theorem eqE       {𝒱} [DecidableEq 𝒱] [HasType 𝒱] {Γ : TypeContext 𝒱} {x y τ} : Γ ⊢ˢ' .eq x y : τ → τ = .bool ∧ ∃ σ, Γ ⊢ˢ' x : σ ∧ Γ ⊢ˢ' y : σ := λ | eq _ _ _ _ hx hy => ⟨rfl, _, hx, hy⟩
theorem andE      {𝒱} [DecidableEq 𝒱] [HasType 𝒱] {Γ : TypeContext 𝒱} {x y τ} : Γ ⊢ˢ' .and x y : τ → τ = .bool ∧ Γ ⊢ˢ' x : .bool ∧ Γ ⊢ˢ' y : .bool := λ | and _ _ _ hx hy => ⟨rfl, hx, hy⟩
theorem notE      {𝒱} [DecidableEq 𝒱] [HasType 𝒱] {Γ : TypeContext 𝒱} {x τ} : Γ ⊢ˢ' .not x : τ → τ = .bool ∧ Γ ⊢ˢ' x : .bool := λ | not _ _ h => ⟨rfl, h⟩
theorem iteE      {𝒱} [DecidableEq 𝒱] [HasType 𝒱] {Γ : TypeContext 𝒱} {c t f τ} : Γ ⊢ˢ' .ite c t f : τ → Γ ⊢ˢ' c : .bool ∧ Γ ⊢ˢ' t : τ ∧ Γ ⊢ˢ' f : τ := λ | ite _ _ _ _ _ hc ht hf => ⟨hc,ht,hf⟩
theorem someE     {𝒱} [DecidableEq 𝒱] [HasType 𝒱] {Γ : TypeContext 𝒱} {t τ} : Γ ⊢ˢ' .some t : τ → ∃ σ, τ = .option σ ∧ Γ ⊢ˢ' t : σ := λ | some _ _ _ h => ⟨_, rfl, h⟩
theorem theE      {𝒱} [DecidableEq 𝒱] [HasType 𝒱] {Γ : TypeContext 𝒱} {t τ} : Γ ⊢ˢ' .the t : τ → Γ ⊢ˢ' t : τ.option := λ | the _ _ _ ht => ht
theorem noneE     {𝒱} [DecidableEq 𝒱] [HasType 𝒱] {Γ : TypeContext 𝒱} {τ ξ} : Γ ⊢ˢ' .none ξ : τ → τ = .option ξ := λ | none .. => rfl
theorem unitE     {𝒱} [DecidableEq 𝒱] [HasType 𝒱] {Γ : TypeContext 𝒱} {τ} : Γ ⊢ˢ' .«()» : τ → τ = .unit := λ | «()» .. => rfl
theorem pairE     {𝒱} [DecidableEq 𝒱] [HasType 𝒱] {Γ : TypeContext 𝒱} {x y τ} : Γ ⊢ˢ' .pair x y : τ → ∃ α β, τ = .pair α β ∧ Γ ⊢ˢ' x : α ∧ Γ ⊢ˢ' y : β := λ | pair _ _ _ _ _ hx hy => ⟨_,_,rfl,hx,hy⟩
theorem fstE      {𝒱} [DecidableEq 𝒱] [HasType 𝒱] {Γ : TypeContext 𝒱} {x τ} : Γ ⊢ˢ' .fst x : τ → ∃ σ, Γ ⊢ˢ' x : .pair τ σ := λ | fst _ _ _ _ hx => ⟨_,hx⟩
theorem sndE      {𝒱} [DecidableEq 𝒱] [HasType 𝒱] {Γ : TypeContext 𝒱} {x τ} : Γ ⊢ˢ' .snd x : τ → ∃ σ, Γ ⊢ˢ' x : .pair σ τ := λ | snd _ _ _ _ hx => ⟨_,hx⟩
theorem distinctE {𝒱} [DecidableEq 𝒱] [HasType 𝒱] {Γ : TypeContext 𝒱} {n : ℕ} {xs : Fin n → Term 𝒱} {τ} : Γ ⊢ˢ' .distinct xs : τ → τ = .bool ∧ ∃ σ, ∀ i, Γ ⊢ˢ' xs i : σ := λ | distinct _ _ σ h => ⟨rfl, σ, h⟩
theorem leE       {𝒱} [DecidableEq 𝒱] [HasType 𝒱] {Γ : TypeContext 𝒱} {x y τ} : Γ ⊢ˢ' .le x y : τ → τ = .bool ∧ Γ ⊢ˢ' x : .int ∧ Γ ⊢ˢ' y : .int := λ | le _ _ _ hx hy => ⟨rfl,hx,hy⟩
theorem addE      {𝒱} [DecidableEq 𝒱] [HasType 𝒱] {Γ : TypeContext 𝒱} {x y τ} : Γ ⊢ˢ' .add x y : τ → τ = .int ∧ Γ ⊢ˢ' x : .int ∧ Γ ⊢ˢ' y : .int := λ | add _ _ _ hx hy => ⟨rfl,hx,hy⟩
theorem subE      {𝒱} [DecidableEq 𝒱] [HasType 𝒱] {Γ : TypeContext 𝒱} {x y τ} : Γ ⊢ˢ' .sub x y : τ → τ = .int ∧ Γ ⊢ˢ' x : .int ∧ Γ ⊢ˢ' y : .int := λ | sub _ _ _ hx hy => ⟨rfl,hx,hy⟩
theorem mulE      {𝒱} [DecidableEq 𝒱] [HasType 𝒱] {Γ : TypeContext 𝒱} {x y τ} : Γ ⊢ˢ' .mul x y : τ → τ = .int ∧ Γ ⊢ˢ' x : .int ∧ Γ ⊢ˢ' y : .int := λ | mul _ _ _ hx hy => ⟨rfl,hx,hy⟩
theorem lambdaE   {𝒱} [DecidableEq 𝒱] [HasType 𝒱] {Γ : TypeContext 𝒱} {n} {τs : Fin n → SMTType} {t : (Fin n → 𝒱) → Term 𝒱} {τ} : (h : Γ ⊢ˢ' .lambda τs t : τ) → 0 < n ∧ ∃ γ, τ = .fun (Fin.foldr (n-1) (fun ⟨i, hi⟩ acc ↦ (τs ⟨i, Nat.lt_of_lt_pred hi⟩).pair acc) (τs ⟨n-1, match h with | lambda _ _ _ _ _ h => Nat.sub_one_lt_of_lt h⟩)) γ ∧ (∀ vs, (∀ i, SMT.PHOAS.HasType.type (vs i) = τs i) → (Γ.update vs τs) ⊢ˢ' t vs : γ) := λ | .lambda _ _ _ γ typt n_pos => ⟨n_pos, γ, rfl, typt⟩
theorem forallE   {𝒱} [DecidableEq 𝒱] [HasType 𝒱] {Γ : TypeContext 𝒱} {n} {τs : Fin n → SMTType} {P : (Fin n → 𝒱) → Term 𝒱} {τ} : Γ ⊢ˢ' .forall τs P : τ → 0 < n ∧ τ = .bool ∧ (∀ vs, (∀ i, SMT.PHOAS.HasType.type (vs i) = τs i) → (Γ.update vs τs) ⊢ˢ' P vs : .bool) := λ | .forall _ _ _ h n_pos => ⟨n_pos, rfl, h⟩
-- theorem orE       {𝒱} [DecidableEq 𝒱] [HasType 𝒱] {Γ : TypeContext 𝒱} {x y τ} : Γ ⊢ˢ' .or x y : τ → τ = .bool ∧ Γ ⊢ˢ' x : .bool ∧ Γ ⊢ˢ' y : .bool := λ | or _ _ _ hx hy => ⟨rfl, hx, hy⟩
-- theorem impE      {𝒱} [DecidableEq 𝒱] [HasType 𝒱] {Γ : TypeContext 𝒱} {x y τ} : Γ ⊢ˢ' .imp x y : τ → τ = .bool ∧ Γ ⊢ˢ' x : .bool ∧ Γ ⊢ˢ' y : .bool := λ | imp _ _ _ hx hy => ⟨rfl, hx, hy⟩
-- theorem existsE   {𝒱} [DecidableEq 𝒱] [HasType 𝒱] {Γ : TypeContext 𝒱} {n} {τs : Fin n → SMTType} {P : (Fin n → 𝒱) → Term 𝒱} {τ} : Γ ⊢ˢ' .exists τs P : τ → 0 < n ∧ τ = .bool ∧ (∀ vs, (Γ.update vs τs) ⊢ˢ' P vs : .bool) := λ | .exists _ _ _ h n_pos => ⟨n_pos, rfl, h⟩

end Typing
end InversionRules

instance {n} {𝒱} [Inhabited 𝒱] : Inhabited (Fin n → 𝒱) := inferInstance

theorem Typing.det {𝒱} [DecidableEq 𝒱] [RichHasType 𝒱] [Inhabited 𝒱] {Γ : TypeContext 𝒱} {t : Term 𝒱} {τ σ : SMTType} :
    Γ ⊢ˢ' t : τ → Γ ⊢ˢ' t : σ → τ = σ := by
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
    rw [τ_eq, σ_eq]
    let vs : Fin _ → 𝒱 := fun i => RichHasType.rep (τs i)
    have vs_typed : ∀ i, SMT.PHOAS.HasType.type (vs i) = τs i :=
      fun i => RichHasType.rep_type (τs i)
    have h1 := typ_t vs vs_typed
    have h2 := typ_t' vs vs_typed
    have := ih vs h1 h2
    rw [this]
  | «forall» τs t ih =>
    obtain ⟨n_pos, rfl, typ_t⟩ := Typing.forallE typ_τ
    obtain ⟨-, rfl, typ_t'⟩ := Typing.forallE typ_σ
    rfl
end SMT.PHOAS
