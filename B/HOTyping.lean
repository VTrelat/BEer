import B.HOTyping.Rules

open B B.PHOAS

abbrev WellTyped.{u} {𝒱 : Type u} [DecidableEq 𝒱] (t : Term 𝒱) :=
  Σ' (Γ : TypeContext 𝒱) (τ : BType), Γ ⊢ᴮ' t : τ

namespace PHOAS.Typing
open PHOAS Typing

theorem toTerm_sound {𝒱} [DecidableEq 𝒱] {Γ : TypeContext 𝒱} {γ : BType} : Γ ⊢ᴮ' γ.toTerm' : γ.set := by
  induction γ with
  | int => exact «ℤ»
  | bool => exact 𝔹
  | set α ih => exact pow ih
  | prod α β α_ih β_ih => exact cprod α_ih β_ih

theorem foldl_aux {𝒱} [DecidableEq 𝒱] {Γ : TypeContext 𝒱} {n : ℕ} (α : Fin (n + 1) → BType) (D : Fin (n + 1) → PHOAS.Term 𝒱) (typD : ∀ (i : Fin (n + 1)), Γ ⊢ᴮ' D i : (α i).set) :
  Γ ⊢ᴮ' Fin.foldl n (λ d ⟨i, hi⟩ => d ⨯ᴮ' D ⟨i + 1, Nat.add_lt_add_right hi 1⟩) (D 0) : (Fin.foldl n (fun d ⟨i, hi⟩ => d ×ᴮ α ⟨i + 1, Nat.add_lt_add_right hi 1⟩) (α 0)).set := by
  dsimp
  induction n with
  | zero =>
    simp
    exact typD 0
  | succ n IH =>
    simp only [Fin.foldl_succ_last, Fin.coe_castSucc, Fin.val_last]
    apply Typing.cprod
    · let α' : Fin (n + 1) → BType := λ ⟨i, hi⟩ => α ⟨i, Nat.lt_add_right 1 hi⟩
      let D' : Fin (n + 1) → PHOAS.Term 𝒱 := λ ⟨i, hi⟩ => D ⟨i, Nat.lt_add_right 1 hi⟩
      specialize IH α' D'
      apply IH
      rintro ⟨i, hi⟩
      exact typD ⟨i, Nat.lt_add_right 1 hi⟩
    · exact typD ⟨n + 1, Nat.lt_add_one (n + 1)⟩

theorem foldl_aux' {𝒱} [DecidableEq 𝒱] {Γ : TypeContext 𝒱} {n : ℕ} (n_pos : 0 < n) (α : Fin n → BType) (D : Fin n → PHOAS.Term 𝒱) (typD : ∀ i : Fin n, Γ ⊢ᴮ' D i : (α i).set) :
  Γ ⊢ᴮ' Fin.foldl (n - 1) (λ d ⟨i, hi⟩ => d ⨯ᴮ' D ⟨i + 1, Nat.add_lt_of_lt_sub hi⟩) (D ⟨0, n_pos⟩) : (Fin.foldl (n - 1) (fun d ⟨i, hi⟩ => d ×ᴮ α ⟨i + 1, Nat.add_lt_of_lt_sub hi⟩) (α ⟨0, n_pos⟩)).set := by
  dsimp
  induction n with
  | zero =>
    simp
    exact typD ⟨0, n_pos⟩
  | succ n IH =>
    -- simp only [lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, forall_const] at IH
    cases n with
    | zero =>
      exact foldl_aux α D typD
    | succ n =>
      simp only [Nat.add_one_sub_one, Fin.foldl_succ_last, Fin.coe_castSucc, Fin.val_last]
      apply Typing.cprod
      · let α' : Fin (n + 1) → BType := λ ⟨i, hi⟩ => α ⟨i, Nat.lt_add_right 1 hi⟩
        let D' : Fin (n + 1) → PHOAS.Term 𝒱 := λ ⟨i, hi⟩ => D ⟨i, Nat.lt_add_right 1 hi⟩
        specialize IH (Nat.zero_lt_succ n) α' D'
        apply IH
        rintro ⟨i, hi⟩
        exact typD ⟨i, Nat.lt_add_right 1 hi⟩
      · exact typD ⟨n + 1, Nat.lt_add_one (n + 1)⟩

theorem collect_dom {𝒱} [DecidableEq 𝒱] (n : ℕ) (D : PHOAS.Term 𝒱) (P : (Fin n → 𝒱) → PHOAS.Term 𝒱) (Γ : TypeContext 𝒱) (τ : BType) {h : Γ ⊢ᴮ' D.collect P : τ} : Γ ⊢ᴮ' D : τ := by
  rcases h
  rename_i α D n_pos typD typP
  obtain ⟨n, rfl⟩ :=  Nat.exists_eq_add_one.mpr n_pos
  simp
  induction n with
  | zero =>
    simp only [Nat.reduceAdd, Fin.isValue, Fin.foldl_zero]
    exact typD 0
  | succ n IH =>
    let α' : Fin (n+1) → BType := λ i => α ⟨i, Nat.lt_add_right 1 i.prop⟩
    let D' : Fin (n+1) → PHOAS.Term 𝒱 := λ ⟨i, hi⟩ => D ⟨i, Nat.lt_add_right 1 hi⟩
    apply foldl_aux α D typD


open Classical in
theorem collect_pred {𝒱} {Γ n z} {D : PHOAS.Term 𝒱} {P : (Fin n → 𝒱) → PHOAS.Term 𝒱} {τ : BType} :
  (h : Γ ⊢ᴮ' D.collect P : τ.set) → Γ.update z (choose (Typing.collectE h).2 |>.1) ⊢ᴮ' P z : BType.bool := by
  intro h
  let ⟨⟨_,_,_,typP⟩,_⟩ := choose_spec (Typing.collectE h).2
  exact typP z

theorem lambda_dom {𝒱} [DecidableEq 𝒱] {n : ℕ} {D : PHOAS.Term 𝒱} {E : (Fin n → 𝒱) → PHOAS.Term 𝒱} {Γ : TypeContext 𝒱} {τ γ : BType}
  (h : Γ ⊢ᴮ' .lambda D E : .set (τ ×ᴮ γ)) : Γ ⊢ᴮ' D : .set τ := by
    rcases h
    rename_i α D n_pos typD typE
    obtain ⟨n, rfl⟩ :=  Nat.exists_eq_add_one.mpr n_pos
    simp
    induction n with
    | zero =>
      simp only [Nat.reduceAdd, Fin.isValue, Fin.foldl_zero]
      exact typD 0
    | succ n IH =>
      let α' : Fin (n+1) → BType := λ i => α ⟨i, Nat.lt_add_right 1 i.prop⟩
      let D' : Fin (n+1) → PHOAS.Term 𝒱 := λ ⟨i, hi⟩ => D ⟨i, Nat.lt_add_right 1 hi⟩
      apply foldl_aux α D typD

open Classical in
theorem lambda_exp {𝒱} [DecidableEq 𝒱] {n : ℕ} {D : PHOAS.Term 𝒱} {E : (Fin n → 𝒱) → PHOAS.Term 𝒱} {Γ : TypeContext 𝒱} {τ γ : BType}
  (h : Γ ⊢ᴮ' .lambda D E : .set (τ ×ᴮ γ)) {z} : Γ.update z (choose (Typing.lambdaE h).2 |>.2.1) ⊢ᴮ' E z : (choose (Typing.lambdaE h).2 |>.1) := by
  let ⟨⟨_,_,_,typE⟩,_⟩ := choose_spec (Typing.lambdaE h).2
  apply typE z

open Classical in
theorem all_pred {𝒱} [DecidableEq 𝒱] {Γ n z} {D : PHOAS.Term 𝒱} {P : (Fin n → 𝒱) → PHOAS.Term 𝒱} :
  (h : Γ ⊢ᴮ' D.all P : .bool) → Γ.update z (choose (Typing.allE h).2.2 |>.1) ⊢ᴮ' P z : BType.bool := by
  intro h
  let ⟨_,_,typP⟩ := choose_spec (Typing.allE h).2.2
  exact typP z

open Classical in
theorem all_dom {𝒱} [DecidableEq 𝒱] {Γ n} {D : PHOAS.Term 𝒱} {P : (Fin n → 𝒱) → PHOAS.Term 𝒱} :
  (h : Γ ⊢ᴮ' D.all P : .bool) →
  let αs_Ds := choose (Typing.allE h).2.2
  let αs := αs_Ds.1
  Γ ⊢ᴮ' D : .set (Fin.foldl (n-1) (λ d ⟨i, hi⟩ => d ×ᴮ αs ⟨i+1, Nat.add_lt_of_lt_sub hi⟩) (αs ⟨0, by cases h with | all _ _ _ h _ => exact h⟩)) := by
  intro h
  obtain n_pos := (Typing.allE h).2.1
  obtain ⟨typD, D_eq, _⟩ := choose_spec (Typing.allE h).2.2
  dsimp
  conv in D => rw [D_eq]
  apply foldl_aux' n_pos
  exact typD

theorem PHOAS.Term.cprod_foldl_succ {𝒱} {n : ℕ} {A : Fin (n + 1) → PHOAS.Term 𝒱} {a : PHOAS.Term 𝒱} :
  Fin.foldl (n + 1) (fun d i => d ⨯ᴮ' A i) a = (Fin.foldl n (fun d ⟨i, hi⟩ => d ⨯ᴮ' A ⟨i, Nat.lt_add_right 1 hi⟩) a) ⨯ᴮ' A ⟨n, Nat.lt_add_one n⟩ :=
  Fin.foldl_succ_last (fun d i => d ⨯ᴮ' A i) a

theorem foldl_cprod_inj {𝒱} {n : ℕ} {A B : Fin n → PHOAS.Term 𝒱} {a b : PHOAS.Term 𝒱}
  (h_eq_fold : Fin.foldl n (fun d i => d ⨯ᴮ' A i) a = Fin.foldl n (fun d i => d ⨯ᴮ' B i) b) :
  a = b ∧ A = B := by
  induction n generalizing a b with
  | zero =>
    and_intros
    · simpa [Fin.foldl_zero] using h_eq_fold
    · ext ⟨_, hi⟩
      nomatch hi
  | succ n ih =>
    simp_rw [PHOAS.Term.cprod_foldl_succ] at h_eq_fold
    injection h_eq_fold with h_eq_fold An_eq_Bn
    specialize ih h_eq_fold
    and_intros
    · exact ih.1
    · rw [funext_iff] at ih
      ext ⟨i, hi⟩
      cases hi with
      | refl => exact An_eq_Bn
      | step hi => exact ih.2 ⟨i, hi⟩

theorem foldl_cprod_inj' {𝒱} [DecidableEq 𝒱] {n : ℕ} {A B : Fin (n + 1) → PHOAS.Term 𝒱}
  (h_eq_fold : Fin.foldl n (fun d i => d ⨯ᴮ' A i.succ) (A 0) = Fin.foldl n (fun d i => d ⨯ᴮ' B i.succ) (B 0)) :
  A = B := by
  let A' := fun i => A (Fin.succ i)
  let B' := fun i => B (Fin.succ i)
  have := @foldl_cprod_inj _ n A' B' (A 0) (B 0) h_eq_fold
  unfold A' B' at this
  rw [funext_iff] at this
  ext ⟨i, hi⟩
  cases i with
  | zero => exact this.1
  | succ i => exact this.2 ⟨i, Nat.succ_lt_succ_iff.mp hi⟩

theorem det {𝒱} [DecidableEq 𝒱] [Nonempty (Π n, Fin n → 𝒱)] {Γ : PHOAS.TypeContext 𝒱} {t : PHOAS.Term 𝒱} {τ σ : BType}
  (hτ : Γ ⊢ᴮ' t : τ) (hσ : Γ ⊢ᴮ' t : σ) : τ = σ := by
  induction hτ generalizing σ with
  | var ih =>
    apply PHOAS.Typing.varE at hσ
    rw [ih] at hσ
    rwa [Option.some.injEq] at hσ
  | int
  | bool =>
    first
    | rcases PHOAS.Typing.intE hσ
    | rcases PHOAS.Typing.boolE hσ
    rfl
  | maplet hx hy xih yih
  | add hx hy xih yih
  | sub hx hy xih yih
  | mul hx hy xih yih
  | and hx hy xih yih
  | eq hx hy xih yih
  | le hx hy xih yih
  | cprod hx hy xih yih
  | union hx hy xih yih
  | inter hx hy xih yih
  | pfun hx hy xih yih
  | app hx hy xih yih =>
    first
    | obtain ⟨α, β, rfl, hx, hy⟩ := PHOAS.Typing.mapletE hσ
    | obtain ⟨rfl, hx, hy⟩ := PHOAS.Typing.addE hσ
    | obtain ⟨rfl, hx, hy⟩ := PHOAS.Typing.subE hσ
    | obtain ⟨rfl, hx, hy⟩ := PHOAS.Typing.mulE hσ
    | obtain ⟨rfl, hx, hy⟩ := PHOAS.Typing.andE hσ
    | obtain ⟨rfl, α, hx, hy⟩ := PHOAS.Typing.eqE hσ
    | obtain ⟨rfl, hx, hy⟩ := PHOAS.Typing.leE hσ
    | obtain ⟨α, β, rfl, hx, hy⟩ := PHOAS.Typing.cprodE hσ
    | obtain ⟨α, rfl, hx, hy⟩ := PHOAS.Typing.unionE hσ
    | obtain ⟨α, rfl, hx, hy⟩ := PHOAS.Typing.interE hσ
    | obtain ⟨α, β, rfl, hx, hy⟩ := PHOAS.Typing.pfunE hσ
    | obtain ⟨α, hx, hy⟩ := PHOAS.Typing.appE hσ
    rcases xih hx
    rcases yih hy
    rfl
  | «ℤ»
  | 𝔹 =>
    first
    | rcases PHOAS.Typing.ℤE hσ
    | rcases PHOAS.Typing.𝔹E hσ
    rfl
  | not hx ih
  | mem hx S ih Sih
  | pow hx ih
  | card hx ih
  | min _ ih
  | max _ ih =>
    first
    | obtain ⟨rfl, hx⟩ := PHOAS.Typing.notE hσ
    | obtain ⟨rfl, α, hS, hT⟩ := PHOAS.Typing.memE hσ
    | obtain ⟨α, rfl, hx⟩ := PHOAS.Typing.powE hσ
    | obtain ⟨rfl, _, hS⟩ := PHOAS.Typing.cardE hσ
    | obtain ⟨rfl, hx⟩ := PHOAS.Typing.minE hσ
    | obtain ⟨rfl, hx⟩ := PHOAS.Typing.maxE hσ
    rcases ih hx
    rfl
  | collect α D P n_pos typD typP typD_ih typP_ih =>
    obtain ⟨n_pos, ⟨αs, Ds⟩, ⟨α_eq, hDs, D_eq, typP⟩, αs_Ds_unq⟩ := PHOAS.Typing.collectE hσ
    clear αs_Ds_unq
    obtain ⟨n, rfl⟩ := Nat.exists_add_one_eq.mpr n_pos
    clear n_pos
    simp only [Nat.add_one_sub_one, Fin.zero_eta] at *

    have : D = Ds := foldl_cprod_inj' D_eq
    subst Ds

    have : α = αs := by
      ext i
      have := typD_ih _ <| hDs i
      injection this

    rw [α_eq, this]
  | all α D P n_pos typD typP typD_ih typP_ih =>
    obtain ⟨rfl, _⟩ := PHOAS.Typing.allE hσ
    rfl
  | lambda α β D E n_pos typD typE typD_ih typE_ih =>
    obtain ⟨-, ⟨γ, αs, Ds⟩, ⟨α_eq, hDs, D_eq, typE'⟩, αs_Ds_unq⟩ := PHOAS.Typing.lambdaE hσ
    clear αs_Ds_unq
    obtain ⟨n, rfl⟩ := Nat.exists_add_one_eq.mpr n_pos
    simp only [Nat.add_one_sub_one, Fin.zero_eta] at *

    have : D = Ds := foldl_cprod_inj' D_eq
    subst Ds

    have : α = αs := by
      ext i
      have := typD_ih _ <| hDs i
      injection this

    rw [α_eq, this]
    congr

    rw [this] at typE_ih
    rename Nonempty _ => inst
    exact typE_ih _ (typE' <| Nonempty.some inst (n+1))


end PHOAS.Typing
