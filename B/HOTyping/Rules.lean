import B.PHOAS.BPHOAS
import B.HOTyping.Def

namespace B.PHOAS

section
set_option hygiene false
local notation:90 Γ:90 " ⊢ᴮ' " x " : " τ:90 => Typing Γ x τ
-- local notation:90 Γ:90 " ⊩ " xs " : " τs:90 => Typing' Γ xs τs
inductive Typing.{u} {𝒱 : Type u} [DecidableEq 𝒱] : TypeContext 𝒱 → Term 𝒱 → BType → Prop where
  | var {Γ v τ} :
      Γ v = some τ
    ----------------------
    → Γ ⊢ᴮ' .var v : τ
  | int {Γ n} : Γ ⊢ᴮ' .int n : .int
  | bool {Γ b} : Γ ⊢ᴮ' .bool b : .bool
  | maplet {Γ α β x y}:
      Γ ⊢ᴮ' x : α
    → Γ ⊢ᴮ' y : β
    ----------------------------
    → Γ ⊢ᴮ' x ↦ᴮ' y : α ×ᴮ β
  | add {Γ x y} :
      Γ ⊢ᴮ' x : .int
    → Γ ⊢ᴮ' y : .int
    -------------------------
    → Γ ⊢ᴮ' x +ᴮ' y : .int
  | sub {Γ x y} :
      Γ ⊢ᴮ' x : .int
    → Γ ⊢ᴮ' y : .int
    -------------------------
    → Γ ⊢ᴮ' x -ᴮ' y : .int
  | mul {Γ x y} :
      Γ ⊢ᴮ' x : .int
    → Γ ⊢ᴮ' y : .int
    -------------------------
    → Γ ⊢ᴮ' x *ᴮ' y : .int
  | and {Γ x y} :
      Γ ⊢ᴮ' x : .bool
    → Γ ⊢ᴮ' y : .bool
    -------------------------
    → Γ ⊢ᴮ' x ∧ᴮ' y : .bool
  | not {Γ x} :
      Γ ⊢ᴮ' x : .bool
    ------------------------
    → Γ ⊢ᴮ' ¬ᴮ' x : .bool
  | eq {Γ α x y} :
      Γ ⊢ᴮ' x : α
    → Γ ⊢ᴮ' y : α
    ------------------------
    → Γ ⊢ᴮ' x =ᴮ' y : .bool
  | le {Γ x y} :
      Γ ⊢ᴮ' x : .int
    → Γ ⊢ᴮ' y : .int
    ------------------------
    → Γ ⊢ᴮ' x ≤ᴮ' y : .bool
  | ℤ {Γ} : Γ ⊢ᴮ' .ℤ : .set .int
  | 𝔹 {Γ} : Γ ⊢ᴮ' .𝔹 : .set .bool
  | mem {Γ α x S}:
      Γ ⊢ᴮ' x : α
    → Γ ⊢ᴮ' S : .set α
    --------------------------
    → Γ ⊢ᴮ' x ∈ᴮ' S : .bool
  | collect {Γ : TypeContext 𝒱} {n : ℕ} (α : Fin n → BType) (D : Fin n → Term 𝒱) (P : (Fin n → 𝒱) → Term 𝒱) :
      (n_pos : 0 < n)
    → (typD : ∀ i : Fin n, Γ ⊢ᴮ' D i : (.set <| α i))
    → (typP : ∀ v : Fin n → 𝒱, Γ.update v α ⊢ᴮ' P v : .bool)
    --------------------------------------------------
    → Γ ⊢ᴮ' .collect (Fin.foldl (n-1) (λ d ⟨i, hi⟩ => d ⨯ᴮ' D ⟨i+1, Nat.add_lt_of_lt_sub hi⟩) (D ⟨0, n_pos⟩)) P : .set (Fin.foldl (n-1) (λ d ⟨i, hi⟩ => d ×ᴮ α ⟨i+1, Nat.add_lt_of_lt_sub hi⟩) (α ⟨0, n_pos⟩))
  | pow {Γ α S}:
      Γ ⊢ᴮ' S : .set α
    ---------------------------------
    → Γ ⊢ᴮ' 𝒫ᴮ' S : .set (.set α)
  | cprod {Γ α β S T}:
      Γ ⊢ᴮ' S : .set α
    → Γ ⊢ᴮ' T : .set β
    -----------------------------
    → Γ ⊢ᴮ' S ⨯ᴮ' T : .set (α ×ᴮ β)
  | union {Γ α S T}:
      Γ ⊢ᴮ' S : .set α
    → Γ ⊢ᴮ' T : .set α
    -----------------------------
    → Γ ⊢ᴮ' S ∪ᴮ' T : .set α
  | inter {Γ α S T}:
      Γ ⊢ᴮ' S : .set α
    → Γ ⊢ᴮ' T : .set α
    -----------------------------
    → Γ ⊢ᴮ' S ∩ᴮ' T : .set α
  | pfun {Γ α β S T}:
      Γ ⊢ᴮ' S : .set α
    → Γ ⊢ᴮ' T : .set β
    -----------------------------
    → Γ ⊢ᴮ' S ⇸ᴮ' T : .set (.set (α ×ᴮ β))
  | all {Γ : TypeContext 𝒱} {n : ℕ} (α : Fin n → BType) (D : Fin n → Term 𝒱) (P : (Fin n → 𝒱) → Term 𝒱) :
      (n_pos : 0 < n)
    → (typD : ∀ i : Fin n, Γ ⊢ᴮ' D i : (.set <| α i))
    → (typP : ∀ v, Γ.update v α ⊢ᴮ' P v : .bool)
    --------------------------------------------------
    → Γ ⊢ᴮ' .all (Fin.foldl (n-1) (λ d ⟨i, hi⟩ => d ⨯ᴮ' D ⟨i+1, Nat.add_lt_of_lt_sub hi⟩) (D ⟨0, n_pos⟩)) P : .bool
  | lambda {Γ : TypeContext 𝒱} {n : ℕ} (α : Fin n → BType) (β : BType) (D : Fin n → Term 𝒱) (E : (Fin n → 𝒱) → Term 𝒱) :
      (n_pos : 0 < n)
    → (typD : ∀ i : Fin n, Γ ⊢ᴮ' D i : (.set <| α i))
    → (typE : ∀ v, Γ.update v α ⊢ᴮ' E v : β)
    --------------------------------------------------
    → Γ ⊢ᴮ' .lambda (Fin.foldl (n-1) (λ d ⟨i, hi⟩ => d ⨯ᴮ' D ⟨i+1, Nat.add_lt_of_lt_sub hi⟩) (D ⟨0, n_pos⟩)) E : .set ((Fin.foldl (n-1) (λ d ⟨i, hi⟩ => d ×ᴮ α ⟨i+1, Nat.add_lt_of_lt_sub hi⟩) (α ⟨0, n_pos⟩)) ×ᴮ β)
  | app {Γ α β f x}:
      Γ ⊢ᴮ' f : .set (α ×ᴮ β)
    → Γ ⊢ᴮ' x : α
    ------------------------
    → Γ ⊢ᴮ' .app f x : β
  | card {Γ α S}:
      Γ ⊢ᴮ' S : .set α
    ------------------------
    → Γ ⊢ᴮ' |S|ᴮ' : .int
  | min {Γ S}:
      Γ ⊢ᴮ' S : .set .int
    ------------------------
    → Γ ⊢ᴮ' .min S : .int
  | max {Γ S}:
      Γ ⊢ᴮ' S : .set .int
    ------------------------
    → Γ ⊢ᴮ' .max S : .int
end

notation:90 Γ:90 " ⊢ᴮ' " x " : " τ:90 => Typing Γ x τ
notation:90 "⊢ᴮ' " x " : "  τ:90 => Typing ∅ x τ

section RuleInversion

-- TODO: Those proofs can be factorized
theorem Fin.foldl_prod_inj {n} {αs βs : Fin n → BType} {α β : BType} :
  Fin.foldl n (fun d x => d ×ᴮ αs x) α = Fin.foldl n (fun d x => d ×ᴮ βs x) β → α = β ∧ αs = βs := by
  intro fold_eq
  induction n generalizing α β with
  | zero =>
    simp only [Fin.foldl_zero] at fold_eq
    and_intros
    · assumption
    · ext ⟨⟩
      contradiction
  | succ n ih =>
    simp only [Fin.foldl_succ] at fold_eq
    specialize @ih (λ ⟨i, hi⟩ => αs ⟨i+1, Nat.add_lt_add_right hi 1⟩) (λ ⟨i, hi⟩ => βs ⟨i+1, Nat.add_lt_add_right hi 1⟩) _ _ fold_eq
    obtain ⟨l, r⟩ := ih
    injection l with α_eq_β αs₀_eq_βs₀
    rw [funext_iff] at r
    and_intros
    · exact α_eq_β
    · ext ⟨i, hi⟩
      cases i with
      | zero => exact αs₀_eq_βs₀
      | succ i => exact r ⟨i, Nat.succ_lt_succ_iff.mp hi⟩

theorem Fin.foldl_cprod_inj {𝒱} {n} {αs βs : Fin n → Term 𝒱} {α β : Term 𝒱} :
  Fin.foldl n (fun d x => d ⨯ᴮ' αs x) α = Fin.foldl n (fun d x => d ⨯ᴮ' βs x) β → α = β ∧ αs = βs := by
  intro fold_eq
  induction n generalizing α β with
  | zero =>
    simp only [Fin.foldl_zero] at fold_eq
    and_intros
    · assumption
    · ext ⟨⟩
      contradiction
  | succ n ih =>
    simp only [Fin.foldl_succ] at fold_eq
    specialize @ih (λ ⟨i, hi⟩ => αs ⟨i+1, Nat.add_lt_add_right hi 1⟩) (λ ⟨i, hi⟩ => βs ⟨i+1, Nat.add_lt_add_right hi 1⟩) _ _ fold_eq
    obtain ⟨l, r⟩ := ih
    injection l with α_eq_β αs₀_eq_βs₀
    rw [funext_iff] at r
    and_intros
    · exact α_eq_β
    · ext ⟨i, hi⟩
      cases i with
      | zero => exact αs₀_eq_βs₀
      | succ i => exact r ⟨i, Nat.succ_lt_succ_iff.mp hi⟩

namespace Typing
theorem 𝔹E       {𝒱} [DecidableEq 𝒱] {Γ : TypeContext 𝒱} {τ} : Γ ⊢ᴮ' .𝔹 : τ → τ = .set .bool := λ h => match h with | .𝔹 => rfl
theorem ℤE       {𝒱} [DecidableEq 𝒱] {Γ : TypeContext 𝒱} {τ} : Γ ⊢ᴮ' .ℤ : τ → τ = .set .int := λ h => match h with | .ℤ => rfl
theorem varE     {𝒱} [DecidableEq 𝒱] {Γ : TypeContext 𝒱} {v τ} : Γ ⊢ᴮ' .var v : τ → Γ v = some τ := λ h => match h with | .var h => h
theorem intE     {𝒱} [DecidableEq 𝒱] {Γ : TypeContext 𝒱} {n τ} : Γ ⊢ᴮ' .int n : τ → τ = .int := λ h => match h with | .int => rfl
theorem boolE    {𝒱} [DecidableEq 𝒱] {Γ : TypeContext 𝒱} {b τ} : Γ ⊢ᴮ' .bool b : τ → τ = .bool := λ h => match h with | .bool => rfl
theorem mapletE  {𝒱} [DecidableEq 𝒱] {Γ : TypeContext 𝒱} {x y τ} : Γ ⊢ᴮ' x ↦ᴮ' y : τ → ∃ α β, τ = α ×ᴮ β ∧ Γ ⊢ᴮ' x : α ∧ Γ ⊢ᴮ' y : β := λ h => match h with | .maplet h h' => ⟨_, _, rfl, h, h'⟩
theorem addE     {𝒱} [DecidableEq 𝒱] {Γ : TypeContext 𝒱} {x y τ} : Γ ⊢ᴮ' x +ᴮ' y : τ → τ = .int ∧ Γ ⊢ᴮ' x : .int ∧ Γ ⊢ᴮ' y : .int := λ h => match h with | .add h h' => ⟨rfl, h, h'⟩
theorem subE     {𝒱} [DecidableEq 𝒱] {Γ : TypeContext 𝒱} {x y τ} : Γ ⊢ᴮ' x -ᴮ' y : τ → τ = .int ∧ Γ ⊢ᴮ' x : .int ∧ Γ ⊢ᴮ' y : .int := λ h => match h with | .sub h h' => ⟨rfl, h, h'⟩
theorem mulE     {𝒱} [DecidableEq 𝒱] {Γ : TypeContext 𝒱} {x y τ} : Γ ⊢ᴮ' x *ᴮ' y : τ → τ = .int ∧ Γ ⊢ᴮ' x : .int ∧ Γ ⊢ᴮ' y : .int := λ h => match h with | .mul h h' => ⟨rfl, h, h'⟩
theorem andE     {𝒱} [DecidableEq 𝒱] {Γ : TypeContext 𝒱} {x y τ} : Γ ⊢ᴮ' x ∧ᴮ' y : τ → τ = .bool ∧ Γ ⊢ᴮ' x : .bool ∧ Γ ⊢ᴮ' y : .bool := λ h => match h with | .and h h' => ⟨rfl, h, h'⟩
theorem notE     {𝒱} [DecidableEq 𝒱] {Γ : TypeContext 𝒱} {x τ} : Γ ⊢ᴮ' ¬ᴮ' x : τ → τ = .bool ∧ Γ ⊢ᴮ' x : .bool := λ h => match h with | .not h => ⟨rfl, h⟩
theorem eqE      {𝒱} [DecidableEq 𝒱] {Γ : TypeContext 𝒱} {x y τ} : Γ ⊢ᴮ' x =ᴮ' y : τ → τ = .bool ∧ ∃ α, Γ ⊢ᴮ' x : α ∧ Γ ⊢ᴮ' y : α := λ h => match h with | .eq h h' => ⟨rfl, _, h, h'⟩
theorem leE      {𝒱} [DecidableEq 𝒱] {Γ : TypeContext 𝒱} {x y τ} : Γ ⊢ᴮ' x ≤ᴮ' y : τ → τ = .bool ∧ Γ ⊢ᴮ' x : .int ∧ Γ ⊢ᴮ' y : .int := λ h => match h with | .le h h' => ⟨rfl, h, h'⟩
theorem memE     {𝒱} [DecidableEq 𝒱] {Γ : TypeContext 𝒱} {x S τ} : Γ ⊢ᴮ' x ∈ᴮ' S : τ → τ  = .bool ∧ ∃ α, Γ ⊢ᴮ' x : α ∧ Γ ⊢ᴮ' S : .set α := λ h => match h with | .mem h h' => ⟨rfl, _, h, h'⟩
theorem powE     {𝒱} [DecidableEq 𝒱] {Γ : TypeContext 𝒱} {S τ} : Γ ⊢ᴮ' 𝒫ᴮ' S : τ → ∃ β, τ = .set (.set β) ∧ Γ ⊢ᴮ' S : .set β := λ h => match h with | .pow h => ⟨_, rfl, h⟩
theorem cprodE   {𝒱} [DecidableEq 𝒱] {Γ : TypeContext 𝒱} {S T τ} : Γ ⊢ᴮ' S ⨯ᴮ' T : τ → ∃ α β, τ = .set (α ×ᴮ β) ∧ Γ ⊢ᴮ' S : .set α ∧ Γ ⊢ᴮ' T : .set β := by rintro ⟨⟩; rename_i α β _ _; exists α, β
theorem unionE   {𝒱} [DecidableEq 𝒱] {Γ : TypeContext 𝒱} {S T τ} : Γ ⊢ᴮ' S ∪ᴮ' T : τ → ∃ α, τ = .set α ∧ Γ ⊢ᴮ' S : .set α ∧ Γ ⊢ᴮ' T : .set α := λ h => match h with | .union h h' => ⟨_, rfl, h, h'⟩
theorem interE   {𝒱} [DecidableEq 𝒱] {Γ : TypeContext 𝒱} {S T τ} : Γ ⊢ᴮ' S ∩ᴮ' T : τ → ∃ α, τ = .set α ∧ Γ ⊢ᴮ' S : .set α ∧ Γ ⊢ᴮ' T : .set α := λ h => match h with | .inter h h' => ⟨_, rfl, h, h'⟩
theorem pfunE    {𝒱} [DecidableEq 𝒱] {Γ : TypeContext 𝒱} {S T τ} : Γ ⊢ᴮ' S ⇸ᴮ' T : τ → ∃ α β, τ = .set (.set (α ×ᴮ β)) ∧ Γ ⊢ᴮ' S : .set α ∧ Γ ⊢ᴮ' T : .set β := λ h => match h with | .pfun h h' => ⟨_, _, rfl, h, h'⟩
theorem collectE {𝒱} [DecidableEq 𝒱] {Γ : TypeContext 𝒱} {n D P τ} : (h : Γ ⊢ᴮ' .collect D P : τ) → 0 < n ∧ (∃! αs_Ds : (Fin n → BType) × (Fin n → Term 𝒱),
    τ = .set (Fin.foldl (n-1) (λ d ⟨i, hi⟩ => d ×ᴮ αs_Ds.1 ⟨i+1, Nat.add_lt_of_lt_sub hi⟩) (αs_Ds.1 ⟨0, by cases h with | collect _ _ _ h => exact h ⟩))
  ∧ (∀ i : Fin n, Γ ⊢ᴮ' αs_Ds.2 i : (.set <| αs_Ds.1 i))
  ∧ (D = (Fin.foldl (n-1) (λ d ⟨i, hi⟩ => d ⨯ᴮ' αs_Ds.2 ⟨i+1, Nat.add_lt_of_lt_sub hi⟩) (αs_Ds.2 ⟨0, by cases h with | collect _ _ _ h => exact h ⟩)))
  ∧ (∀ v, Γ.update v αs_Ds.1 ⊢ᴮ' P v : .bool)) := by
  rintro ⟨⟩
  rename_i αs Ds n_pos typD typP
  and_intros
  · exact n_pos
  · exists ⟨αs, Ds⟩
    simp only [true_and, BType.set.injEq, and_imp, Prod.forall, Prod.mk.injEq]
    and_intros
    · exact typD
    · exact typP
    · intro βs Ts fold_eq_α typT fold_eq_D typP'
      and_intros
      -- TODO: factorize this proof
      · ext ⟨i, hi⟩
        obtain ⟨zero, succ⟩ := Fin.foldl_prod_inj fold_eq_α.symm
        cases i with
        | zero => exact zero
        | succ i =>
          rw [funext_iff] at succ
          exact succ ⟨i, by exact Nat.lt_sub_of_add_lt hi⟩
      · ext ⟨i, hi⟩
        obtain ⟨zero, succ⟩ := Fin.foldl_cprod_inj fold_eq_D.symm
        cases i with
        | zero => exact zero
        | succ i =>
          rw [funext_iff] at succ
          exact succ ⟨i, by exact Nat.lt_sub_of_add_lt hi⟩

theorem lambdaE {𝒱} [DecidableEq 𝒱] {n Γ D E τ} : (h : Γ ⊢ᴮ' .lambda D E : τ) → 0 < n ∧ (∃! (β_αs_Ds : BType × (Fin n → BType) × (Fin n → Term 𝒱)),
    let β := β_αs_Ds.1
    let αs := β_αs_Ds.2.1
    let Ds := β_αs_Ds.2.2
    τ = .set ((Fin.foldl (n-1) (λ d ⟨i, hi⟩ => d ×ᴮ αs ⟨i+1, Nat.add_lt_of_lt_sub hi⟩) (αs ⟨0, by cases h with | lambda _ _ _ _ h => exact h ⟩)) ×ᴮ β)
  ∧ (∀ i : Fin n, Γ ⊢ᴮ' Ds i : (.set <| αs i))
  ∧ (D = (Fin.foldl (n-1) (λ d ⟨i, hi⟩ => d ⨯ᴮ' Ds ⟨i+1, Nat.add_lt_of_lt_sub hi⟩) (Ds ⟨0, by cases h with | lambda _ _ _ _ h => exact h ⟩)))
  ∧ (∀ v, Γ.update v αs ⊢ᴮ' E v : β)) := by
  rintro ⟨⟩
  rename_i β αs Ds n_pos typD typE
  and_intros
  · exact n_pos
  · exists ⟨β, αs, Ds⟩
    and_intros
    · rfl
    · exact typD
    · rfl
    · exact typE
    · rintro ⟨β', αs', Ds'⟩ ⟨fold_αs', typDs', fold_Ds', typ_E'⟩
      simp only [BType.set.injEq, BType.prod.injEq] at fold_αs' typDs' fold_Ds' typ_E'
      congr
      · exact fold_αs'.2.symm
      -- TODO: factorize this proof
      · ext ⟨i, hi⟩
        obtain ⟨zero, succ⟩ := Fin.foldl_prod_inj fold_αs'.1.symm
        cases i with
        | zero => exact zero
        | succ i =>
          rw [funext_iff] at succ
          exact succ ⟨i, by exact Nat.lt_sub_of_add_lt hi⟩
      · ext ⟨i, hi⟩
        obtain ⟨zero, succ⟩ := Fin.foldl_cprod_inj fold_Ds'.symm
        cases i with
        | zero => exact zero
        | succ i =>
          rw [funext_iff] at succ
          exact succ ⟨i, by exact Nat.lt_sub_of_add_lt hi⟩
theorem allE {𝒱} [DecidableEq 𝒱] {n Γ D P τ} : (h : Γ ⊢ᴮ' .all D P : τ) → τ = .bool ∧ 0 < n ∧ (∃ (αs_Ds : (Fin n → BType) × (Fin n → Term 𝒱)),
    let αs := αs_Ds.1; let Ds := αs_Ds.2
    (∀ i : Fin n, Γ ⊢ᴮ' Ds i : (.set <| αs i))
  ∧ (D = (Fin.foldl (n-1) (λ d ⟨i, hi⟩ => d ⨯ᴮ' Ds ⟨i+1, Nat.add_lt_of_lt_sub hi⟩) (Ds ⟨0, by cases h with | all _ _ _ h => exact h ⟩)))
  ∧ (∀ v, Γ.update v αs ⊢ᴮ' P v : .bool)) := by
  rintro ⟨⟩
  rename_i αs Ds n_pos typD typP
  and_intros
  · rfl
  · exact n_pos
  · exists ⟨αs, Ds⟩
    -- and_intros
    -- · exact typD
    -- · rfl
    -- · exact typP
    -- · rintro ⟨αs', Ds'⟩ ⟨typDs', fold_Ds', typP'⟩
    --   simp only [BType.set.injEq, BType.prod.injEq] at typDs' fold_Ds' typP'
    --   have Ds_eq : Ds = Ds' := by
    --     ext ⟨i, hi⟩
    --     obtain ⟨zero, succ⟩ := Fin.foldl_cprod_inj fold_Ds'
    --     cases i with
    --     | zero => exact zero
    --     | succ i =>
    --       rw [funext_iff] at succ
    --       exact succ ⟨i, by exact Nat.lt_sub_of_add_lt hi⟩
    --   congr
    --   · subst Ds_eq
    --   · exact Ds_eq.symm
theorem appE    {𝒱} [DecidableEq 𝒱] {Γ : TypeContext 𝒱} {β f x} : Γ ⊢ᴮ' .app f x : β → ∃ α, Γ ⊢ᴮ' f : .set (α ×ᴮ β) ∧ Γ ⊢ᴮ' x : α := λ h => match h with | .app h h' => ⟨_, h, h'⟩
theorem cardE   {𝒱} [DecidableEq 𝒱] {Γ : TypeContext 𝒱} {S τ} : Γ ⊢ᴮ' |S|ᴮ' : τ → τ = .int ∧ ∃ α, Γ ⊢ᴮ' S : .set α := λ h => match h with | .card h => ⟨rfl, _, h⟩
theorem minE    {𝒱} [DecidableEq 𝒱] {Γ : TypeContext 𝒱} {S τ} : Γ ⊢ᴮ' .min S : τ → τ = .int ∧ Γ ⊢ᴮ' S : .set .int := λ h => match h with | .min h => ⟨rfl, h⟩
theorem maxE    {𝒱} [DecidableEq 𝒱] {Γ : TypeContext 𝒱} {S τ} : Γ ⊢ᴮ' .max S : τ → τ = .int ∧ Γ ⊢ᴮ' S : .set .int := λ h => match h with | .max h => ⟨rfl, h⟩

end Typing

end RuleInversion

theorem BType.prod.fold_injective {αs βs : List BType} {α β : BType} (h : αs.length = βs.length) : αs.foldl (· ×ᴮ ·) α = βs.foldl (· ×ᴮ ·) β ↔ α = β ∧ αs = βs := by
  constructor
  · intro fold_eq
    induction αs, βs, h using List.induction₂ generalizing α β with
    | nil_nil => trivial
    | cons_cons α' αs β' βs _ ih =>
      simp [List.foldl] at fold_eq
      obtain ⟨l, rfl⟩ := ih fold_eq
      injection l with α_eq_β α'_eq_β'
      subst α_eq_β α'_eq_β'
      exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem Typing.reduce_prod_inj {αs αs' : List BType} (h : αs ≠ []) (h' : αs.length = αs'.length) :
  (αs.map .set).reduce (· ×ᴮ ·) (by simpa) = (αs'.map .set).reduce (· ×ᴮ ·) (by simpa using (by rwa [← List.length_pos_iff, ← h', List.length_pos_iff] : αs' ≠ [])) → αs = αs' := by
  let α::αs := αs
  let α'::αs' := αs'
  simp [List.reduce]
  have : (αs.map BType.set).length = (αs'.map BType.set).length := by simpa using h'
  let this := (BType.prod.fold_injective (α := α.set) (β := α'.set) this).mp
  intro h
  obtain ⟨l, r⟩ := this h
  injection l with α_eq_α'
  exact ⟨α_eq_α', List.map_ext @BType.set.inj r⟩

/-
theorem Typing.typing_det {𝒱} [DecidableEq 𝒱] {Γ : TypeContext 𝒱} {x : Term 𝒱} {α β : BType} : Γ ⊢ᴮ' x : α → Γ ⊢ᴮ' x : β → α = β := by
  intro h₁ h₂
  induction h₁ generalizing β with
    | var v₁ =>
      rcases h₂ with ⟨v₂⟩
      rw [v₁] at v₂
      injection v₂
    | int | bool | add | sub | mul | and | not | eq | «ℤ» | 𝔹 | mem | le =>
      cases h₂
      rfl
    | maplet _ _ ih₁ ih₂ =>
      cases h₂ with
      | maplet x₂ y₂ =>
        congr
        exact ih₁ x₂
        exact ih₂ y₂
    | pow _ ih =>
      cases h₂ with
      | pow S₂ =>
        congr
        injection ih S₂
    | cprod _ _ ih₁ ih₂ =>
      cases h₂ with
      | cprod S₂ T₂ =>
        congr
        injection ih₁ S₂
        injection ih₂ T₂
    | union _ _ ih₁ _ =>
      cases h₂ with
      | union S₂ T₂ =>
        exact ih₁ S₂
    | inter _ _ ih₁ _ =>
      cases h₂ with
      | inter S₂ T₂ =>
        exact ih₁ S₂
    | pfun _ _ ihS ihT =>
      cases h₂ with
      | pfun hS' hT' =>
        congr
        injection ihS hS'
        injection ihT hT'
    | app _ _ ihF _ =>
      cases h₂ with
      | app F₂ X₂ =>
        injection ihF F₂
        rename_i h
        injection h
    | card _ _
    | min _ ih
    | max _ ih => cases h₂; rfl
    | all => exact Typing.allE h₂ |>.left.symm
    | @collect Γ n α D P n_pos typD typP IH₁ IH₂ =>
      dsimp at h₂ ⊢ᴮ'
      obtain ⟨α', D', β_eq, typD', D'_eq, typP'⟩ := Typing.collectE h₂
      dsimp at β_eq D'_eq
      have : α = α' := by
        ext ⟨j, hj⟩
        have := (typD' ⟨j, hj⟩)
        have := @IH₁ ⟨j, hj⟩ (α ⟨j, hj⟩).set
        admit
      subst α'
      exact β_eq.symm
    | @lambda Γ n α γ D E n_pos typD typE IH₁ IH₂ =>
      dsimp at h₂ ⊢ᴮ'
      obtain ⟨γ', α', D', β_eq, typD', D'_eq, typE'⟩ := Typing.lambdaE h₂
      dsimp at β_eq D'_eq
      have : γ = γ' := by admit
      subst γ'
      have : α = α' := by
        ext ⟨j, hj⟩
        have := (typD' ⟨j, hj⟩)
        have := @IH₁ ⟨j, hj⟩ (α ⟨j, hj⟩).set
        admit
      subst α'
      exact β_eq.symm

-/

-- theorem TypeContext.mem_union_dom {Γ Δ : TypeContext} {x : 𝒱} : x ∈ (Γ ∪ Δ).dom ↔ x ∈ Γ.dom ∨ x ∈ Δ.dom := by
--   -- simp only [Finmap.keys_union, Finset.mem_union]
--   admit

/-

theorem Finmap.zipToFinmap_keys {Γ : TypeContext} {vs : List 𝒱} {αs : List BType} (h : vs.length = αs.length) : (vs.zipToFinmap αs).keys = vs.toAList := by
  induction vs, αs, h using List.induction₂ with
  | nil_nil => rfl
  | cons_cons v vs α αs _ ih =>
    rw [List.zipToFinmap.eq_def]
    simp only [List.zipWith_cons_cons, List.toFinset_cons]
    rw [Finmap.toFinmap_cons, ← List.zipToFinmap.eq_def, ← ih]
    admit

theorem Typing.typed_by_fv {Γ : TypeContext} {e : Term} {τ : BType} : Γ ⊢ᴮ' e : τ → (fv e).toAList ⊆ Γ.dom := by
  intro h
  induction h with
  | var hv =>
    unfold fv
    simp [List.mem_singleton]
    exact TypeContext.find_in_dom hv
  | int | bool | «ℤ» | 𝔹 =>
    simp [fv]
  | @maplet Γ _ _ _ _ _ _ hx hy
  | @add Γ _ _ _ _ hx hy
  | @sub Γ _ _ _ _ hx hy
  | @mul Γ _ _ _ _ hx hy
  | @and Γ _ _ _ _ hx hy
  | @eq  Γ _ _ _ _ _ hx hy
  | @le Γ _ _ _ _ hx hy
  | @mem Γ _ _ _ _ _ hx hy
  | @cprod Γ _ _ _ _ _ _ hx hy
  | @union Γ _ _ _ _ _ hx hy
  | @inter Γ _ _ _ _ _ hx hy =>
    simp [fv]
    rw [← Finset.union_self Γ.dom]
    apply Finset.union_subset_union hx hy
  | @pow Γ _ _ hx hy | @not Γ _ _ hx =>
    assumption
  | @pfun Γ _ _ _ _ _ _ hS hT | @app Γ _ _ _ _ _ _ hS hT =>
    simp [fv]
    rw [← Finset.union_self Γ.dom]
    apply Finset.union_subset_union hS hT
  | card hS | min hS | max hS => rwa [fv]
  | @collect Γ _ _ _ _ _ _ _ _ ihD ihP =>
    simp [fv]
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact ihD ha
    · simp only [List.mem_toFinset, List.mem_removeAll_iff] at ha
      have := ihP <| List.mem_toFinset.mpr ha.left
      rw [TypeContext.mem_union_dom] at this
      rcases this with this | this
      · admit
      · admit
  | @all Γ _ _ _ _ _ _ _ _ ihD ihP
  | @lambda Γ _ _ _ _ _ _ _ _ _ ihD ihP =>
    simp [fv]
    admit

theorem Typing.union_find?_iff {Γ Δ : TypeContext} {x : 𝒱} {τ : BType} : (Γ ∪ Δ).find? x = τ ↔ Γ.find? x = τ ∨ (x ∉ Γ ∧ Δ.find? x = τ) := by
  simp only [AList.lookup_union_eq_some, TypeContext.find?]
  admit

theorem Typing.union_extend_left {Γ Δ₁ Δ₂ : TypeContext} : Δ₁.find? = Δ₂.find? → ∀ {x : 𝒱}, (Γ ∪ Δ₁).find? x = (Γ ∪ Δ₂).find? x := by
  admit

theorem Typing.context_perm {Γ Δ : TypeContext} {e : Term} {τ : BType}: (∀ x, Γ.find? x = Δ.find? x) → Γ ⊢ᴮ' e : τ → Δ ⊢ᴮ' e : τ := by
  intro h he
  induction e generalizing τ Γ Δ with
  | var v =>
    cases he
    apply Typing.var
    rwa [←h]
  | int _ | bool _ =>
    cases he
    first
    | exact Typing.int
    | exact Typing.bool
  | maplet x y xih yih =>
    rcases he with _ | _ | _ | ⟨hx, hy⟩
    replace hx := xih h hx
    replace hy := yih h hy
    apply Typing.maplet <;> assumption
  | le x y xih yih =>
    rcases he with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |  ⟨hx, hy⟩
    replace hx := xih h hx
    replace hy := yih h hy
    apply Typing.le <;> assumption
  | add x y xih yih =>
    rcases he with _ | _ | _ | _ | ⟨hx, hy⟩
    replace hx := xih h hx
    replace hy := yih h hy
    apply Typing.add <;> assumption
  | sub x y xih yih =>
    rcases he with _ | _ | _ | _ | _ | ⟨hx, hy⟩
    replace hx := xih h hx
    replace hy := yih h hy
    apply Typing.sub <;> assumption
  | mul x y xih yih =>
    rcases he with _ | _ | _ | _ | _ | _ | ⟨hx, hy⟩
    replace hx := xih h hx
    replace hy := yih h hy
    apply Typing.mul <;> assumption
  | and x y xih yih =>
    rcases he with _ | _ | _ | _ | _ | _ | _ | ⟨hx, hy⟩
    replace hx := xih h hx
    replace hy := yih h hy
    apply Typing.and <;> assumption
  | not x xih =>
    rcases he with _ | _ | _ | _ | _ | _ | _ | _ | hx
    replace hx := xih h hx
    apply Typing.not
    assumption
  | eq x y xih yih =>
    rcases he with _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨hx, hy⟩
    replace hx := xih h hx
    replace hy := yih h hy
    apply Typing.eq <;> assumption
  | «ℤ» =>
    cases he
    exact Typing.ℤ
  | 𝔹 =>
    cases he
    exact Typing.𝔹
  | mem x S xih Sih =>
    rcases he with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |_ |  ⟨hx, Sh⟩
    replace hx := xih h hx
    replace Sh := Sih h Sh
    apply Typing.mem <;> assumption
  | collect vs D P Dih Pih =>
    admit
  | all vs D P Dih Pih =>
    admit
  | pow S Sih =>
    rcases he with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨hS⟩
    replace hS := Sih h hS
    apply Typing.pow
    assumption
  | cprod S T Sih Tih =>
    rcases he with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨hS, hT⟩
    replace hS := Sih h hS
    replace hT := Tih h hT
    apply Typing.cprod <;> assumption
  | union S T Sih Tih =>
    rcases he with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨hS, hT⟩
    replace hS := Sih h hS
    replace hT := Tih h hT
    apply Typing.union <;> assumption
  | inter S T Sih Tih =>
    rcases he with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨hS, hT⟩
    replace hS := Sih h hS
    replace hT := Tih h hT
    apply Typing.inter <;> assumption
  | pfun S T Sih Tih =>
    rcases he with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨hS, hT⟩
    apply Typing.pfun
    · exact Sih h hS
    · exact Tih h hT
  | lambda v D P Dih Pih =>
    admit
  | app f x fih xih =>
    rcases he with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨hx, Ph⟩
    apply Typing.app
    · exact fih h hx
    · exact xih h Ph
  | card S Sih =>
    rcases he with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨hS⟩
    apply Typing.card
    exact Sih h hS
  | min S Sih =>
    rcases he with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨hS⟩
    apply Typing.min
    exact Sih h hS
  | max S Sih =>
    rcases he with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨hS⟩
    apply Typing.max
    exact Sih h hS

theorem Typing.context_swap {Γ : TypeContext} {x y} {α β τ} {e} : (Γ.insert x α).insert y β ⊢ᴮ' e : τ → x ≠ y → (Γ.insert y β).insert x α ⊢ᴮ' e : τ := by
  admit

theorem Typing.context_weakening {Γ} {y} {α β} {e} : y ∉ fv e → Γ ⊢ᴮ' e : α → (Γ.insert y β) ⊢ᴮ' e : α := by
  admit

-/

end B.PHOAS
