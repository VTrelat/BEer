import SMT.Semantics
import SMT.Typing

open Classical in
noncomputable def SMT.TypeContext.abstract (Γ : SMT.TypeContext) («Δ» : SMT.𝒱 → Option Dom) :
  PHOAS.TypeContext Dom := fun ⟨x, τ, h⟩ ↦
    if h : ∃ k, «Δ» k = .some ⟨x, τ, h⟩ ∧ Γ.lookup k = τ then
      Γ.lookup <| choose h
    else .none

namespace SMT.PHOAS

noncomputable instance : DecidableEq Dom := Classical.typeDecidableEq Dom

class WFTC (Γ : TypeContext Dom) where
  wf v v' : Γ v = some v' → v.2.1 = v'

theorem TypeContext.update1 {Γ : TypeContext Dom} {v : Dom} {α : SMTType} :
  Γ.update (fun _ : Fin 1 => v) (fun _ => α) v = some α := by
  rw [TypeContext.update, Fin.foldl_succ, Fin.foldl_zero, Function.update, dite_cond_eq_true <| eq_true rfl]

theorem WFTC.update1 {Γ} [WFTC Γ] {v : Dom} {α : SMTType} (hv : v.2.1 = α) :
  WFTC (Γ.update (fun _ : Fin 1 => v) (fun _ => α)) where
  wf := by
    rintro x β eq_some
    by_cases hx : x = v
    · subst hx
      rw [TypeContext.update1, Option.some_inj] at eq_some
      rcases eq_some
      exact hv
    · rw [TypeContext.update, Fin.foldl_succ, Fin.foldl_zero, Function.update_apply] at eq_some
      split_ifs at eq_some
      exact WFTC.wf _ _ eq_some

theorem TypeContext.update_succ {Γ : TypeContext Dom} {n} {vs : Fin (n + 1) → Dom} {αs : Fin (n + 1) → SMTType} :
  Γ.update vs αs = (Γ.update (fun _ : Fin 1 => vs 0) (fun _ => αs 0)).update (fun i => vs i.succ) (fun i => αs i.succ) := by
  rw [TypeContext.update, Fin.foldl_succ, ←TypeContext.update]
  have : Function.update Γ (vs 0) (some (αs 0)) = Γ.update (fun _ : Fin 1 => vs 0) (fun _ => αs 0) := by
    rw [TypeContext.update, Fin.foldl_succ, Fin.foldl_zero]
  rw [this]

theorem WFTC.update {Γ} [WFTC Γ] {n} {vs : Fin n → Dom} {τs : Fin n → SMTType} (vs_τs_wf : ∀ i, (vs i).2.1 = τs i) :
  WFTC <| Γ.update vs τs where
    wf := by
      intro v τ eq_some
      induction n generalizing Γ with
      | zero =>
        rw [TypeContext.update, Fin.foldl_zero] at eq_some
        exact WFTC.wf _ _ eq_some
      | succ n ih =>
        rw [TypeContext.update_succ] at eq_some
        apply @ih (Γ.update (fun _ : Fin 1 => vs 0) (fun _ => τs 0)) (WFTC.update1 (vs_τs_wf 0)) (fun i => vs i.succ) (fun i => τs i.succ)
        · exact (vs_τs_wf ·.succ)
        · exact eq_some

theorem WFTC.of_abstract {«Δ» : 𝒱 → Option Dom} {Γ : SMT.TypeContext} : WFTC <| Γ.abstract («Δ» := «Δ») where
  wf := by
    rintro ⟨V, τ, hV⟩ τ' h
    dsimp
    dsimp [TypeContext.abstract] at h
    split_ifs at h with Δ_eq
    obtain ⟨eq, mem_Γ⟩ := Classical.choose_spec Δ_eq
    rw [mem_Γ] at h
    injections

abbrev WellTyped' (t : PHOAS.Term Dom) := Σ' (Γ : TypeContext Dom) (_ : WFTC Γ) (τ : SMTType), Γ ⊢ˢ' t : τ

/-- If d ≠ vs[i] for all i, then `Ξ.update vs αs d = Ξ d`. -/
theorem TypeContext.update_apply_of_not_mem {𝒱} [DecidableEq 𝒱] :
    ∀ {n} (Ξ : PHOAS.TypeContext 𝒱) (vs : Fin n → 𝒱) (αs : Fin n → SMTType) (d : 𝒱),
      (∀ i, d ≠ vs i) → (Ξ.update vs αs) d = Ξ d := by
  intro n
  induction n with
  | zero =>
    intro Ξ vs αs d _
    show Fin.foldl 0 _ Ξ d = Ξ d
    rw [Fin.foldl_zero]
  | succ k ih =>
    intro Ξ vs αs d h
    show Fin.foldl (k+1) (fun D i => Function.update D (vs i) (some (αs i))) Ξ d = Ξ d
    rw [Fin.foldl_succ_last]
    rw [Function.update_apply, if_neg (h (Fin.last k))]
    have := ih Ξ (fun i => vs i.castSucc) (fun i => αs i.castSucc) d (fun i => h i.castSucc)
    show Fin.foldl k (fun (x1 : PHOAS.TypeContext 𝒱) x2 => Function.update x1 (vs x2.castSucc) (some (αs x2.castSucc))) Ξ d = Ξ d
    exact this

/-- If `vs` is injective then `Ξ.update vs αs (vs i) = some (αs i)`. -/
theorem TypeContext.update_apply_self_of_inj {𝒱} [DecidableEq 𝒱] :
    ∀ {n} (Ξ : PHOAS.TypeContext 𝒱) (vs : Fin n → 𝒱) (αs : Fin n → SMTType) (i : Fin n),
      Function.Injective vs → (Ξ.update vs αs) (vs i) = Option.some (αs i) := by
  intro n
  induction n with
  | zero => intro _ _ _ i _; exact i.elim0
  | succ k ih =>
    intro Ξ vs αs i hinj
    show Fin.foldl (k+1) (fun D j => Function.update D (vs j) (αs j)) Ξ (vs i) = Option.some (αs i)
    rw [Fin.foldl_succ_last]
    simp only [Function.update_apply]
    by_cases hieq : vs i = vs (Fin.last k)
    · rw [if_pos hieq]
      have : i = Fin.last k := hinj hieq
      rw [this]
    · rw [if_neg hieq]
      have hi_ne : i ≠ Fin.last k := fun heq => hieq (heq ▸ rfl)
      obtain ⟨j, hj⟩ : ∃ j : Fin k, j.castSucc = i := by
        refine ⟨⟨i.1, ?_⟩, ?_⟩
        · rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp i.2) with h | h
          · exact h
          · exact absurd (Fin.ext h) hi_ne
        · ext; rfl
      rw [← hj]
      have hcastInj : Function.Injective (fun j : Fin k => vs j.castSucc) := by
        intro a b hab
        have := hinj hab
        exact Fin.castSucc_injective k this
      exact ih Ξ (fun j => vs j.castSucc) (fun j => αs j.castSucc) j hcastInj

theorem denote_welltyped_eq {t : PHOAS.Term Dom} {T τ hTτ}
  (wt_t : WellTyped' t)
  (den_t : ⟦t⟧ˢ = some ⟨T, τ, hTτ⟩) : wt_t.2.2.1 = τ := by
  induction t generalizing T τ with
  | var v =>
    obtain ⟨Γ, Γwf, τ, hτ⟩ := wt_t
    obtain ⟨V, σ, hσ⟩ := v
    rcases WFTC.wf _ _ <| PHOAS.Typing.varE hτ
    rcases den_t
    rfl
  | int n =>
    obtain ⟨Γ, _, τ, hτ⟩ := wt_t
    rcases PHOAS.Typing.intE hτ
    rcases den_t
    rfl
  | bool b =>
    obtain ⟨Γ, _, τ, hτ⟩ := wt_t
    rcases PHOAS.Typing.boolE hτ
    rcases den_t
    rfl
  | app f x f_ih x_ih =>
    obtain ⟨Γ, Γwf, σ, hσ⟩ := wt_t
    obtain ⟨α, hf, hx⟩ := PHOAS.Typing.appE hσ
    simp_rw [denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_t
    obtain ⟨F, ξ, Fξ, den_F, other⟩ := den_t
    obtain rfl := f_ih ⟨Γ, Γwf, _, hf⟩ den_F
    simp only [Option.bind_eq_some_iff] at other
    obtain ⟨⟨X, α, Xα⟩, den_X, other⟩ := other
    obtain rfl := x_ih ⟨Γ, Γwf, _, hx⟩ den_X
    simp only [dite_cond_eq_true] at other
    split_ifs at other
    injections
    subst_eqs
    rfl
  | none τ =>
    obtain ⟨Γ, _, τ', hτ'⟩ := wt_t
    rcases PHOAS.Typing.noneE hτ'
    rcases den_t
    rfl
  | eq t₁ t₂ t₁_ih t₂_ih =>
    obtain ⟨Γ, Γwf, τ, hτ⟩ := wt_t

    apply Typing.eqE at hτ
    obtain ⟨rfl, σ, ht₁, ht₂⟩ := hτ

    simp_rw [denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_t
    obtain ⟨T₁, τ₁, hT₁, den_t₁, T₂, τ₂, hT₂, den_t₂, other⟩ := den_t

    obtain rfl := t₁_ih ⟨Γ, Γwf, σ, ht₁⟩ den_t₁
    obtain rfl := t₂_ih ⟨Γ, Γwf, σ, ht₂⟩ den_t₂

    simp_rw [dite_cond_eq_true, Option.some_inj] at other
    injection other with _ heq
    subst T
    injection heq
  | and t₁ t₂ t₁_ih t₂_ih =>
    obtain ⟨Γ, Γwf, τ, hτ⟩ := wt_t
    apply Typing.andE at hτ
    obtain ⟨rfl, ht₁, ht₂⟩ := hτ

    simp_rw [denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_t
    obtain ⟨T₁, τ₁, hT₁, den_t₁, other⟩ := den_t

    obtain rfl := t₁_ih ⟨Γ, Γwf, .bool, ht₁⟩ den_t₁
    simp_rw [Option.bind_eq_some_iff, PSigma.exists] at other
    obtain ⟨T₂, τ₂, hT₂, den_t₂, other⟩ := other
    obtain rfl := t₂_ih ⟨Γ, Γwf, .bool, ht₂⟩ den_t₂
    rw [Option.some_inj] at other
    injection other with _ heq
    subst T
    injection heq
  | not t ih =>
    obtain ⟨Γ, Γwf, τ, hτ⟩ := wt_t
    apply Typing.notE at hτ
    obtain ⟨rfl, ht⟩ := hτ

    simp_rw [denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_t
    obtain ⟨T', τ', hT', den_t, other⟩ := den_t

    obtain rfl := ih ⟨Γ, Γwf, .bool, ht⟩ den_t
    rw [Option.some_inj] at other
    injections
    subst_eqs
    rfl
  | some t ih =>
    obtain ⟨Γ, Γwf, τ, hτ⟩ := wt_t
    apply Typing.someE at hτ
    obtain ⟨σ, rfl, ht⟩ := hτ

    simp_rw [denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_t
    obtain ⟨T', τ', hT', den_t, other⟩ := den_t
    rw [Option.some_inj] at other
    injections
    subst_eqs

    obtain rfl := ih ⟨Γ, Γwf, σ, ht⟩ den_t
    rfl
  | the t ih =>
    obtain ⟨Γ, Γwf, τ, hτ⟩ := wt_t
    replace hτ := Typing.theE hτ

    simp_rw [denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_t
    obtain ⟨T', τ', hT', den_t, other⟩ := den_t

    obtain rfl := ih ⟨Γ, Γwf, .option τ, hτ⟩ den_t
    rw [Option.some_inj] at other
    injections
    subst_eqs
    rfl
  | «()» =>
    obtain ⟨Γ, _, τ, hτ⟩ := wt_t
    rcases PHOAS.Typing.unitE hτ
    rcases den_t
    rfl
  | pair t₁ t₂ t₁_ih t₂_ih =>
    obtain ⟨Γ, Γwf, τ, hτ⟩ := wt_t
    apply Typing.pairE at hτ
    obtain ⟨σ₁, σ₂, rfl, ht₁, ht₂⟩ := hτ

    simp_rw [denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_t
    obtain ⟨T₁, τ₁, hT₁, den_t₁, T₂, τ₂, hT₂, den_t₂, other⟩ := den_t
    rw [Option.some_inj] at other
    injections
    subst_eqs
    dsimp
    congr
    · apply t₁_ih ⟨Γ, Γwf, σ₁, ht₁⟩ den_t₁
    · apply t₂_ih ⟨Γ, Γwf, σ₂, ht₂⟩ den_t₂
  | fst t ih =>
    obtain ⟨Γ, Γwf, τ, hτ⟩ := wt_t
    apply Typing.fstE at hτ
    obtain ⟨σ, ht⟩ := hτ

    simp_rw [denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_t
    obtain ⟨T', τ', hT', den_t, other⟩ := den_t

    obtain rfl := ih ⟨Γ, Γwf, _, ht⟩ den_t
    rw [Option.some_inj] at other
    injections
    subst_eqs
    rfl
  | snd t ih =>
    obtain ⟨Γ, Γwf, τ, hτ⟩ := wt_t
    apply Typing.sndE at hτ
    obtain ⟨σ, ht⟩ := hτ

    simp_rw [denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_t
    obtain ⟨T', τ', hT', den_t, other⟩ := den_t

    obtain rfl := ih ⟨Γ, Γwf, _, ht⟩ den_t
    rw [Option.some_inj] at other
    injections
    subst_eqs
    rfl
  | le t₁ t₂ t₁_ih t₂_ih
  | sub t₁ t₂ t₁_ih t₂_ih
  | add t₁ t₂ t₁_ih t₂_ih
  | mul t₁ t₂ t₁_ih t₂_ih =>
    obtain ⟨Γ, Γwf, τ, hτ⟩ := wt_t
    first
    | apply Typing.leE at hτ
    | apply Typing.subE at hτ
    | apply Typing.addE at hτ
    | apply Typing.mulE at hτ
    obtain ⟨rfl, ht₁, ht₂⟩ := hτ

    simp_rw [denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_t
    obtain ⟨T₁, τ₁, hT₁, den_t₁, other⟩ := den_t

    obtain rfl := t₁_ih ⟨Γ, Γwf, .int, ht₁⟩ den_t₁
    simp_rw [Option.bind_eq_some_iff, PSigma.exists] at other
    obtain ⟨T₂, τ₂, hT₂, den_t₂, other⟩ := other
    obtain rfl := t₂_ih ⟨Γ, Γwf, .int, ht₂⟩ den_t₂
    rw [Option.some_inj] at other
    injection other with _ heq
    subst T
    injection heq
  | ite c t e c_ih t_ih e_ih =>
    obtain ⟨Γ, Γwf, τ, hτ⟩ := wt_t
    apply Typing.iteE at hτ
    obtain ⟨hc, ht, he⟩ := hτ

    simp_rw [denote, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_t
    obtain ⟨C, τC, hC, den_c, den_if⟩ := den_t

    obtain rfl := c_ih ⟨Γ, Γwf, .bool, hc⟩ den_c
    dsimp at den_if
    split_ifs at den_if
    · exact t_ih ⟨Γ, Γwf, τ, ht⟩ den_if
    · exact e_ih ⟨Γ, Γwf, τ, he⟩ den_if
  | distinct ts ih =>
    obtain ⟨Γ, Γwf, τ, hτ⟩ := wt_t
    apply Typing.distinctE at hτ
    obtain ⟨rfl, _, ht⟩ := hτ

    simp_rw [denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at den_t
    obtain ⟨Ts, den_ts, eq⟩ := den_t
    rw [Option.some_inj] at eq
    injections
    subst_eqs
    rfl
  | lambda τs t ih =>
    obtain ⟨Γ, Γwf, τ', hτ'⟩ := wt_t
    apply Typing.lambdaE at hτ'
    obtain ⟨n_pos, γ, τ'_eq, typ_t⟩ := hτ'

    simp_rw [denote, Option.pure_def, dite_cond_eq_true (eq_true n_pos)] at den_t
    split_ifs at den_t with den_is_some typ_det
    rw [Option.some_inj] at den_t
    injection den_t
    subst T
    injections τ_eq
    dsimp
    rw [←τ_eq, τ'_eq]
    congr

    let xₙ : Fin _ → Dom := fun i ↦ ⟨(τs i).defaultZFSet, τs i, SMTType.mem_toZFSet_of_defaultZFSet⟩
    let den_t_xₙ := ⟦t xₙ⟧ˢ.get (den_is_some (fun i ↦ ⟨rfl, SMTType.mem_toZFSet_of_defaultZFSet⟩))
    let ξ := den_t_xₙ.2.1
    have all_ξ (x : Fin _ → Dom) (hx : ∀ i, (x i).2.1 = τs i ∧ (x i).1 ∈ (τs i).toZFSet) :
        ⟦t x⟧ˢ.get (den_is_some hx) |>.2.1 = ξ := by
      specialize typ_det x xₙ hx ?_
      · intro
        exact ⟨rfl, SMTType.mem_toZFSet_of_defaultZFSet⟩
      · exact typ_det
    specialize ih xₙ ⟨Γ.update xₙ τs, WFTC.update (congrFun rfl), γ, typ_t xₙ (by sorry) (by sorry)⟩ (Option.eq_some_iff_get_eq.mpr ⟨den_is_some (fun i => ⟨rfl, SMTType.mem_toZFSet_of_defaultZFSet⟩), rfl⟩)
    obtain rfl : γ = ξ := ih
    apply all_ξ
    exact fun i ↦ ⟨rfl, SMTType.mem_toZFSet_of_defaultZFSet⟩
  | «forall» τs t ih =>
    obtain ⟨Γ, Γwf, τ, hτ⟩ := wt_t
    apply Typing.forallE at hτ
    obtain ⟨n_pos, rfl, typ_t⟩ := hτ

    simp_rw [denote, Option.pure_def, dite_cond_eq_true (eq_true n_pos)] at den_t
    split_ifs at den_t with den_is_some
    rw [Option.some_inj] at den_t
    injection den_t with _ heq
    subst T
    injection heq

/-- Generalized form of `of_abstract` taking an arbitrary PHOAS context `Ξ` compatible with
  the source typing context via `hΞ`. The original `of_abstract` is the specialization
  with `Ξ = Γ.abstract Δ`. -/
theorem Typing.of_abstract_gen
  {t : SMT.Term} {Γ : SMT.TypeContext} {γ : SMTType}
  (typ_t : Γ ⊢ˢ t : γ)
  {«Δ» : 𝒱 → Option Dom}
  (ht : ∀ v ∈ fv t, («Δ» v).isSome = true)
  (Ξ : PHOAS.TypeContext Dom)
  (hΞ : ∀ v ∈ fv t, ∀ d, «Δ» v = Option.some d →
    ∀ σ, Γ.lookup v = Option.some σ → Ξ d = Option.some σ) :
  Ξ ⊢ˢ' t.abstract «Δ» ht : γ := by
  induction typ_t generalizing «Δ» Ξ with
  | var Γ v σ hlk =>
    simp only [fv, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at ht
    unfold Term.abstract
    apply PHOAS.Typing.var
    exact hΞ v (by simp [fv]) _ (Option.eq_some_iff_get_eq.mpr ⟨ht, rfl⟩) σ hlk
  | int =>
    unfold Term.abstract; apply PHOAS.Typing.int
  | bool =>
    unfold Term.abstract; apply PHOAS.Typing.bool
  | app Γ f x τ σ typ_f typ_x f_ih x_ih =>
    simp only [fv, List.mem_append, or_imp] at ht
    unfold Term.abstract
    apply PHOAS.Typing.app
    · apply f_ih _ Ξ
      intro v hv; exact hΞ v (by simp [fv]; left; exact hv)
    · apply x_ih _ Ξ
      intro v hv; exact hΞ v (by simp [fv]; right; exact hv)
  | eq Γ t₁ t₂ τ typ_t₁ typ_t₂ t₁_ih t₂_ih =>
    simp only [fv, List.mem_append, or_imp] at ht
    unfold Term.abstract
    apply PHOAS.Typing.eq
    · apply t₁_ih _ Ξ
      intro v hv; exact hΞ v (by simp [fv]; left; exact hv)
    · apply t₂_ih _ Ξ
      intro v hv; exact hΞ v (by simp [fv]; right; exact hv)
  | and Γ t₁ t₂ typ_t₁ typ_t₂ t₁_ih t₂_ih =>
    simp only [fv, List.mem_append, or_imp] at ht
    unfold Term.abstract
    apply PHOAS.Typing.and
    · apply t₁_ih _ Ξ
      intro v hv; exact hΞ v (by simp [fv]; left; exact hv)
    · apply t₂_ih _ Ξ
      intro v hv; exact hΞ v (by simp [fv]; right; exact hv)
  | or Γ t₁ t₂ typ_t₁ typ_t₂ t₁_ih t₂_ih =>
    simp only [fv, List.mem_append, or_imp] at ht
    unfold Term.abstract
    apply PHOAS.Typing.not
    apply PHOAS.Typing.and
    · apply PHOAS.Typing.not
      apply t₁_ih _ Ξ
      intro v hv; exact hΞ v (by simp [fv]; left; exact hv)
    · apply PHOAS.Typing.not
      apply t₂_ih _ Ξ
      intro v hv; exact hΞ v (by simp [fv]; right; exact hv)
  | not Γ t typ_t t_ih =>
    simp only [fv] at ht
    unfold Term.abstract
    apply PHOAS.Typing.not
    apply t_ih _ Ξ
    intro v hv; exact hΞ v (by simp [fv]; exact hv)
  | imp Γ t₁ t₂ typ_t₁ typ_t₂ t₁_ih t₂_ih =>
    simp only [fv, List.mem_append, or_imp] at ht
    unfold Term.abstract
    apply PHOAS.Typing.not
    apply PHOAS.Typing.and
    · apply t₁_ih _ Ξ
      intro v hv; exact hΞ v (by simp [fv]; left; exact hv)
    · apply PHOAS.Typing.not
      apply t₂_ih _ Ξ
      intro v hv; exact hΞ v (by simp [fv]; right; exact hv)
  | ite Γ c t e τ typ_c typ_t typ_e c_ih t_ih e_ih =>
    simp only [fv, List.mem_append, or_imp] at ht
    unfold Term.abstract
    apply PHOAS.Typing.ite
    · apply c_ih _ Ξ
      intro v hv; exact hΞ v (by simp [fv, List.mem_append]; left; exact hv)
    · apply t_ih _ Ξ
      intro v hv; exact hΞ v (by simp [fv, List.mem_append]; right; left; exact hv)
    · apply e_ih _ Ξ
      intro v hv; exact hΞ v (by simp [fv, List.mem_append]; right; right; exact hv)
  | some Γ t τ typ_t t_ih =>
    simp only [fv] at ht
    unfold Term.abstract
    apply PHOAS.Typing.some
    apply t_ih _ Ξ
    intro v hv; exact hΞ v (by simp [fv]; exact hv)
  | none Γ τ =>
    unfold Term.abstract; apply PHOAS.Typing.none
  | the Γ t τ typ_t t_ih =>
    simp only [fv] at ht
    unfold Term.abstract
    apply PHOAS.Typing.the
    apply t_ih _ Ξ
    intro v hv; exact hΞ v (by simp [fv]; exact hv)
  | pair Γ t₁ τ₁ t₂ τ₂ typ_t₁ typ_t₂ t₁_ih t₂_ih =>
    simp only [fv, List.mem_append, or_imp] at ht
    unfold Term.abstract
    apply PHOAS.Typing.pair
    · apply t₁_ih _ Ξ
      intro v hv; exact hΞ v (by simp [fv]; left; exact hv)
    · apply t₂_ih _ Ξ
      intro v hv; exact hΞ v (by simp [fv]; right; exact hv)
  | fst Γ t τ σ typ_t t_ih =>
    simp only [fv] at ht
    unfold Term.abstract
    apply PHOAS.Typing.fst
    apply t_ih _ Ξ
    intro v hv; exact hΞ v (by simp [fv]; exact hv)
  | snd Γ t τ σ typ_t t_ih =>
    simp only [fv] at ht
    unfold Term.abstract
    apply PHOAS.Typing.snd
    apply t_ih _ Ξ
    intro v hv; exact hΞ v (by simp [fv]; exact hv)
  | le Γ t₁ t₂ typ_t₁ typ_t₂ t₁_ih t₂_ih =>
    simp only [fv, List.mem_append, or_imp] at ht
    unfold Term.abstract
    apply PHOAS.Typing.le
    · apply t₁_ih _ Ξ
      intro v hv; exact hΞ v (by simp [fv]; left; exact hv)
    · apply t₂_ih _ Ξ
      intro v hv; exact hΞ v (by simp [fv]; right; exact hv)
  | add Γ t₁ t₂ typ_t₁ typ_t₂ t₁_ih t₂_ih =>
    simp only [fv, List.mem_append, or_imp] at ht
    unfold Term.abstract
    apply PHOAS.Typing.add
    · apply t₁_ih _ Ξ
      intro v hv; exact hΞ v (by simp [fv]; left; exact hv)
    · apply t₂_ih _ Ξ
      intro v hv; exact hΞ v (by simp [fv]; right; exact hv)
  | sub Γ t₁ t₂ typ_t₁ typ_t₂ t₁_ih t₂_ih =>
    simp only [fv, List.mem_append, or_imp] at ht
    unfold Term.abstract
    apply PHOAS.Typing.sub
    · apply t₁_ih _ Ξ
      intro v hv; exact hΞ v (by simp [fv]; left; exact hv)
    · apply t₂_ih _ Ξ
      intro v hv; exact hΞ v (by simp [fv]; right; exact hv)
  | mul Γ t₁ t₂ typ_t₁ typ_t₂ t₁_ih t₂_ih =>
    simp only [fv, List.mem_append, or_imp] at ht
    unfold Term.abstract
    apply PHOAS.Typing.mul
    · apply t₁_ih _ Ξ
      intro v hv; exact hΞ v (by simp [fv]; left; exact hv)
    · apply t₂_ih _ Ξ
      intro v hv; exact hΞ v (by simp [fv]; right; exact hv)
  | distinct Γ ts τ typ_ts ts_ih =>
    simp only [fv, List.map_subtype, List.unattach_attach, List.mem_flatten, List.mem_map,
      exists_exists_and_eq_and, forall_exists_index, and_imp] at ht
    unfold Term.abstract
    apply PHOAS.Typing.distinct (τ := τ)
    induction ts with
    | nil => simp only [List.length_nil, IsEmpty.forall_iff]
    | cons t ts ih =>
      rintro ⟨i, hi⟩
      simp only [List.length_cons] at hi
      simp only [List.length_cons, Term.abstractList, Fin.zero_eta, Fin.mk_eq_zero]
      split_ifs with i_eq_zero
      · subst i_eq_zero
        apply ts_ih _ List.mem_cons_self _ Ξ
        intro v hv d Δ_eq σ Γ_eq
        exact hΞ v (by
          simp only [fv, List.map_subtype, List.unattach_attach, List.mem_flatten, List.mem_map,
            exists_exists_and_eq_and]
          exact ⟨t, List.mem_cons_self, hv⟩) d Δ_eq σ Γ_eq
      · apply ih
        · intro t' ht'; exact typ_ts t' (List.mem_cons_of_mem _ ht')
        · intros s s_mem _ ht' Ξ' hΞ'
          exact ts_ih _ (List.mem_cons_of_mem t s_mem) ht' Ξ' hΞ'
        · intro v hv
          simp only [fv, List.map_subtype, List.unattach_attach, List.mem_flatten, List.mem_map,
            exists_exists_and_eq_and] at hv
          obtain ⟨tᵢ, htᵢ, v_fv_tᵢ⟩ := hv
          exact ht _ tᵢ (List.mem_cons_of_mem t htᵢ) v_fv_tᵢ
        · intro v hv d Δ_eq σ Γ_eq
          simp only [fv, List.map_subtype, List.unattach_attach, List.mem_flatten, List.mem_map,
            exists_exists_and_eq_and] at hv
          obtain ⟨tᵢ, htᵢ, v_fv_tᵢ⟩ := hv
          apply hΞ v _ d Δ_eq σ Γ_eq
          simp only [fv, List.map_subtype, List.unattach_attach, List.mem_flatten, List.mem_map,
            exists_exists_and_eq_and]
          exact ⟨tᵢ, List.mem_cons_of_mem t htᵢ, v_fv_tᵢ⟩
        · intro _ s hs hfv
          exact ht _ s (List.mem_cons_of_mem _ hs) hfv
  | lambda Γ vs τs t γ vs_Γ fresh len_pos len_eq body_typ body_ih =>
    simp only [fv, List.mem_removeAll_iff, and_imp] at ht
    unfold Term.abstract
    rw [dite_cond_eq_true (eq_true len_eq)]
    have hτs_ne : τs ≠ [] := List.ne_nil_of_length_pos (by omega)
    have hlen_sub : vs.length - 1 = τs.length - 1 := by omega
    have foldr_eq : ∀ (τs : List SMTType) (hne : τs ≠ []),
        (Fin.foldr (τs.length - 1)
          (fun (i : Fin (τs.length - 1)) acc => (τs[i.1]'(by omega)).pair acc)
          (τs[τs.length - 1]'(Nat.sub_lt (List.length_pos_of_ne_nil hne) Nat.one_pos))) =
        List.foldr (fun τ acc => τ.pair acc) (τs.getLast hne) τs.dropLast := by
      intro τs hne
      induction τs with
      | nil => exact absurd rfl hne
      | cons τ τs' ih =>
        match τs' with
        | [] => simp [Fin.foldr, List.dropLast, List.getLast]; rfl
        | τ' :: τs'' =>
          have hne' : τ' :: τs'' ≠ [] := List.cons_ne_nil _ _
          simp only [List.length_cons, Nat.add_sub_cancel,
            List.dropLast_cons₂, List.getLast_cons hne',
            List.foldr_cons, Fin.foldr_succ, List.getElem_cons_succ]
          congr 1
          exact ih hne'
    have type_eq : (List.foldr (fun τ acc => τ.pair acc) (τs.getLast hτs_ne) τs.dropLast).fun γ =
        (Fin.foldr (vs.length - 1)
          (fun (i : Fin (vs.length - 1)) acc => (τs[i.1]'(by omega)).pair acc)
          (τs[vs.length - 1]'(by omega))).fun γ := by
      have h := (foldr_eq τs hτs_ne).symm
      simp only [hlen_sub]
      exact congrArg (·.fun γ) h
    rw [type_eq]
    apply PHOAS.Typing.lambda _ _ _ _ ?_ len_pos
    intro ws vs_inj vs_fresh
    set Δ' := Function.updates «Δ» vs ((List.ofFn ws).map Option.some) with Δ'_def
    have hcov_body : ∀ v ∈ fv t, (Δ' v).isSome = true := by
      intro v hv
      by_cases hvs : v ∈ vs
      · exact Function.updates_isSome_of_mem_map_some «Δ» vs (List.ofFn ws) v hvs (by simp [len_eq])
      · rw [Δ'_def, Function.updates_of_not_mem «Δ» vs ((List.ofFn ws).map Option.some) v hvs]
        exact ht v hv hvs
    have hws_eq : (fun (⟨i, hi⟩ : Fin vs.length) => (List.ofFn ws)[i]'(by simp; exact hi)) = ws := by
      funext ⟨i, hi⟩; simp
    have eq_body :
        (SMT.Term.abstract.go t vs «Δ» (fun v hv h => ht v hv h)).uncurry ws =
        t.abstract Δ' hcov_body := by
      conv_lhs => rw [show ws = (fun (⟨i, hi⟩ : Fin vs.length) => (List.ofFn ws)[i]'(by simp; exact hi)) from hws_eq.symm]
      exact SMT.Term.abstract.go.alt_def₂ vs t (List.ofFn ws)
        (by simp [len_eq]) (fun v hv hvs => ht v hv hvs) hcov_body
    rw [eq_body]
    apply body_ih hcov_body (Ξ.update ws (fun (⟨i, hi⟩ : Fin vs.length) => τs[i]'(by omega)))
    intro v hv d Δ_eq σ Γ_eq
    by_cases hvs : v ∈ vs
    · sorry
    · -- v ∉ vs case
      rw [Δ'_def, Function.updates_of_not_mem _ vs _ v hvs] at Δ_eq
      rw [SMT.TypeContext.lookup_update _ v vs τs len_eq hvs] at Γ_eq
      have hΞ_d : Ξ d = Option.some σ :=
        hΞ v (by simp [fv, List.mem_removeAll_iff]; exact ⟨hv, hvs⟩) d Δ_eq σ Γ_eq
      have hne_ws : ∀ i, d ≠ ws i := by
        intro i heq
        rw [heq] at hΞ_d
        have hnone := vs_fresh i
        rw [Option.isNone_iff_eq_none] at hnone
        rw [hnone] at hΞ_d
        cases hΞ_d
      rw [TypeContext.update_apply_of_not_mem Ξ ws _ d hne_ws]
      exact hΞ_d
  | «forall» Γ vs τs P vs_Γ fresh len_pos len_eq body_typ body_ih =>
    simp only [fv, List.mem_removeAll_iff, and_imp] at ht
    unfold Term.abstract
    rw [dite_cond_eq_true (eq_true len_eq)]
    apply PHOAS.Typing.forall (n_pos := len_pos)
    intro ws vs_inj vs_fresh
    set Δ' := Function.updates «Δ» vs ((List.ofFn ws).map Option.some) with Δ'_def
    have hcov_body : ∀ v ∈ fv P, (Δ' v).isSome = true := by
      intro v hv
      by_cases hvs : v ∈ vs
      · exact Function.updates_isSome_of_mem_map_some «Δ» vs (List.ofFn ws) v hvs (by simp [len_eq])
      · rw [Δ'_def, Function.updates_of_not_mem «Δ» vs ((List.ofFn ws).map Option.some) v hvs]
        exact ht v hv hvs
    have hws_eq : (fun (⟨i, hi⟩ : Fin vs.length) => (List.ofFn ws)[i]'(by simp; exact hi)) = ws := by
      funext ⟨i, hi⟩; simp
    have eq_body :
        (SMT.Term.abstract.go P vs «Δ» (fun v hv h => ht v hv h)).uncurry ws =
        P.abstract Δ' hcov_body := by
      conv_lhs => rw [show ws = (fun (⟨i, hi⟩ : Fin vs.length) => (List.ofFn ws)[i]'(by simp; exact hi)) from hws_eq.symm]
      exact SMT.Term.abstract.go.alt_def₂ vs P (List.ofFn ws)
        (by simp [len_eq]) (fun v hv hvs => ht v hv hvs) hcov_body
    rw [eq_body]
    apply body_ih hcov_body (Ξ.update ws (fun (⟨i, hi⟩ : Fin vs.length) => τs[i]'(by omega)))
    intro v hv d Δ_eq σ Γ_eq
    by_cases hvs : v ∈ vs
    · sorry
    · -- v ∉ vs case
      rw [Δ'_def, Function.updates_of_not_mem _ vs _ v hvs] at Δ_eq
      rw [SMT.TypeContext.lookup_update _ v vs τs len_eq hvs] at Γ_eq
      have hΞ_d : Ξ d = Option.some σ :=
        hΞ v (by simp [fv, List.mem_removeAll_iff]; exact ⟨hv, hvs⟩) d Δ_eq σ Γ_eq
      have hne_ws : ∀ i, d ≠ ws i := by
        intro i heq
        rw [heq] at hΞ_d
        have hnone := vs_fresh i
        rw [Option.isNone_iff_eq_none] at hnone
        rw [hnone] at hΞ_d
        cases hΞ_d
      rw [TypeContext.update_apply_of_not_mem Ξ ws _ d hne_ws]
      exact hΞ_d
  | «exists» Γ vs τs P vs_Γ fresh len_pos len_eq body_typ body_ih =>
    sorry

theorem Typing.of_abstract
  {t : SMT.Term} {«Δ» : SMT.𝒱 → Option Dom} {Γ : SMT.TypeContext} {τ : SMTType}
  (ht : ∀ v ∈ fv t, («Δ» v).isSome = true)
  (hΔΓ : ∀ v, Γ.lookup v = ((«Δ» v).map (·.2.1)))
  (typ_t : Γ ⊢ˢ t : τ) :
  Γ.abstract («Δ» := «Δ») ⊢ˢ' t.abstract «Δ» ht : τ := by
  induction typ_t generalizing «Δ» with
  | var Γ v τ ih =>
    simp only [fv, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at ht
    unfold Term.abstract
    apply PHOAS.Typing.var
    rw [TypeContext.abstract, dite_cond_eq_true (eq_true ?_)]
    · grind
    · grind
  | int
  | bool =>
    simp only [fv, List.not_mem_nil, IsEmpty.forall_iff, implies_true] at ht
    unfold Term.abstract
    apply_rules [PHOAS.Typing.bool, PHOAS.Typing.int]
  | app Γ f x τ σ typ_f typ_x f_ih x_ih =>
    simp only [fv, List.mem_append, or_imp] at ht
    unfold Term.abstract
    apply PHOAS.Typing.app
    · exact f_ih _ hΔΓ
    · exact x_ih _ hΔΓ
  | eq Γ t₁ t₂ τ typ_t₁ typ_t₂ t₁_ih t₂_ih =>
    simp only [fv, List.mem_append, or_imp] at ht
    unfold Term.abstract
    apply PHOAS.Typing.eq
    · exact t₁_ih _ hΔΓ
    · exact t₂_ih _ hΔΓ
  | and Γ t₁ t₂ typ_t₁ typ_t₂ t₁_ih t₂_ih =>
    simp only [fv, List.mem_append, or_imp] at ht
    unfold Term.abstract
    apply PHOAS.Typing.and
    · exact t₁_ih _ hΔΓ
    · exact t₂_ih _ hΔΓ
  | or Γ t₁ t₂ typ_t₁ typ_t₂ t₁_ih t₂_ih =>
    simp only [fv, List.mem_append, or_imp] at ht
    unfold Term.abstract
    apply PHOAS.Typing.not
    apply PHOAS.Typing.and
    · apply PHOAS.Typing.not
      exact t₁_ih _ hΔΓ
    · apply PHOAS.Typing.not
      exact t₂_ih _ hΔΓ
  | not Γ t typ_t t_ih =>
    simp only [fv] at ht
    unfold Term.abstract
    apply PHOAS.Typing.not
    exact t_ih _ hΔΓ
  | imp Γ t₁ t₂ typ_t₁ typ_t₂ t₁_ih t₂_ih =>
    simp only [fv, List.mem_append, or_imp] at ht
    unfold Term.abstract
    apply PHOAS.Typing.not
    apply PHOAS.Typing.and
    · exact t₁_ih _ hΔΓ
    · apply PHOAS.Typing.not
      exact t₂_ih _ hΔΓ
  | ite Γ c t e τ typ_c typ_t typ_e c_ih t_ih e_ih =>
    simp only [fv, List.mem_append, or_imp] at ht
    unfold Term.abstract
    apply PHOAS.Typing.ite
    · exact c_ih _ hΔΓ
    · exact t_ih _ hΔΓ
    · exact e_ih _ hΔΓ
  | some Γ t τ typ_t t_ih =>
    simp only [fv] at ht
    unfold Term.abstract
    apply PHOAS.Typing.some
    exact t_ih _ hΔΓ
  | none Γ τ =>
    simp only [fv, List.not_mem_nil, IsEmpty.forall_iff, implies_true] at ht
    unfold Term.abstract
    apply PHOAS.Typing.none
  | the Γ t τ typ_t t_ih =>
     simp only [fv] at ht
     unfold Term.abstract
     apply PHOAS.Typing.the
     exact t_ih _ hΔΓ
  | pair Γ t₁ τ₁ t₂ τ₂ typ_t₁ typ_t₂ t₁_ih t₂_ih =>
    simp only [fv, List.mem_append, or_imp] at ht
    unfold Term.abstract
    apply PHOAS.Typing.pair
    · exact t₁_ih _ hΔΓ
    · exact t₂_ih _ hΔΓ
  | fst Γ t τ σ typ_t t_ih =>
    simp only [fv] at ht
    unfold Term.abstract
    apply PHOAS.Typing.fst
    exact t_ih _ hΔΓ
  | snd Γ t τ σ typ_t t_ih =>
    simp only [fv] at ht
    unfold Term.abstract
    apply PHOAS.Typing.snd
    exact t_ih _ hΔΓ
  | le Γ t₁ t₂ typ_t₁ typ_t₂ t₁_ih t₂_ih =>
    simp only [fv, List.mem_append, or_imp] at ht
    unfold Term.abstract
    apply PHOAS.Typing.le
    · exact t₁_ih _ hΔΓ
    · exact t₂_ih _ hΔΓ
  | add Γ t₁ t₂ typ_t₁ typ_t₂ t₁_ih t₂_ih =>
    simp only [fv, List.mem_append, or_imp] at ht
    unfold Term.abstract
    apply PHOAS.Typing.add
    · exact t₁_ih _ hΔΓ
    · exact t₂_ih _ hΔΓ
  | sub Γ t₁ t₂ typ_t₁ typ_t₂ t₁_ih t₂_ih =>
    simp only [fv, List.mem_append, or_imp] at ht
    unfold Term.abstract
    apply PHOAS.Typing.sub
    · exact t₁_ih _ hΔΓ
    · exact t₂_ih _ hΔΓ
  | mul Γ t₁ t₂ typ_t₁ typ_t₂ t₁_ih t₂_ih =>
    simp only [fv, List.mem_append, or_imp] at ht
    unfold Term.abstract
    apply PHOAS.Typing.mul
    · exact t₁_ih _ hΔΓ
    · exact t₂_ih _ hΔΓ
  | distinct Γ ts τ typ_ts ts_ih =>
    simp only [fv, List.map_subtype, List.unattach_attach, List.mem_flatten, List.mem_map,
      exists_exists_and_eq_and, forall_exists_index, and_imp] at ht
    unfold Term.abstract
    apply PHOAS.Typing.distinct (τ := τ)
    induction ts with
    | nil => simp only [List.length_nil, IsEmpty.forall_iff]
    | cons t ts ih =>
      rintro ⟨i, hi⟩
      simp only [List.length_cons] at hi
      simp only [List.length_cons, Term.abstractList, Fin.zero_eta, Fin.mk_eq_zero]
      split_ifs with i_eq_zero
      · subst i_eq_zero
        exact ts_ih _ List.mem_cons_self _ hΔΓ
      · apply ih
        · intro t ht
          exact typ_ts t (List.mem_cons_of_mem _ ht)
        · intros s s_mem _ ht'
          exact ts_ih _ (List.mem_cons_of_mem t s_mem) ht'
        · intro v hv
          simp only [fv, List.map_subtype, List.unattach_attach, List.mem_flatten, List.mem_map,
            exists_exists_and_eq_and] at hv
          obtain ⟨tᵢ, htᵢ, v_fv_tᵢ⟩ := hv
          exact ht _ tᵢ (List.mem_cons_of_mem t htᵢ) v_fv_tᵢ
        · intro _ s hs hfv
          exact ht _ s (List.mem_cons_of_mem _ hs) hfv
  | lambda Γ vs τs t γ vs_Γ fresh len_pos len_eq body_typ body_ih =>
    simp only [fv, List.mem_removeAll_iff, and_imp] at ht
    unfold Term.abstract
    rw [dite_cond_eq_true (eq_true len_eq)]
    have hτs_ne : τs ≠ [] := List.ne_nil_of_length_pos (by omega)
    have hlen_sub : vs.length - 1 = τs.length - 1 := by omega
    have foldr_eq : ∀ (τs : List SMTType) (hne : τs ≠ []),
        (Fin.foldr (τs.length - 1)
          (fun (i : Fin (τs.length - 1)) acc => (τs[i.1]'(by omega)).pair acc)
          (τs[τs.length - 1]'(Nat.sub_lt (List.length_pos_of_ne_nil hne) Nat.one_pos))) =
        List.foldr (fun τ acc => τ.pair acc) (τs.getLast hne) τs.dropLast := by
      intro τs hne
      induction τs with
      | nil => exact absurd rfl hne
      | cons τ τs' ih =>
        match τs' with
        | [] => simp [Fin.foldr, List.dropLast, List.getLast]; rfl
        | τ' :: τs'' =>
          have hne' : τ' :: τs'' ≠ [] := List.cons_ne_nil _ _
          simp only [List.length_cons, Nat.add_sub_cancel,
            List.dropLast_cons₂, List.getLast_cons hne',
            List.foldr_cons, Fin.foldr_succ, List.getElem_cons_succ]
          congr 1
          exact ih hne'
    have type_eq : (List.foldr (fun τ acc => τ.pair acc) (τs.getLast hτs_ne) τs.dropLast).fun γ =
        (Fin.foldr (vs.length - 1)
          (fun (i : Fin (vs.length - 1)) acc => (τs[i.1]'(by omega)).pair acc)
          (τs[vs.length - 1]'(by omega))).fun γ := by
      have h := (foldr_eq τs hτs_ne).symm
      simp only [hlen_sub]
      exact congrArg (·.fun γ) h
    rw [type_eq]
    apply PHOAS.Typing.lambda _ _ _ _ ?_ len_pos
    intro ws vs_inj vs_fresh
    set Δ' := Function.updates «Δ» vs ((List.ofFn ws).map Option.some) with Δ'_def
    have hcov_body : ∀ v ∈ fv t, (Δ' v).isSome = true := by
      intro v hv
      by_cases hvs : v ∈ vs
      · exact Function.updates_isSome_of_mem_map_some «Δ» vs (List.ofFn ws) v hvs (by simp [len_eq])
      · rw [Δ'_def, Function.updates_of_not_mem «Δ» vs ((List.ofFn ws).map Option.some) v hvs]
        exact ht v hv hvs
    have hws_eq : (fun (⟨i, hi⟩ : Fin vs.length) => (List.ofFn ws)[i]'(by simp; exact hi)) = ws := by
      funext ⟨i, hi⟩; simp
    have eq_body :
        (SMT.Term.abstract.go t vs «Δ» (fun v hv h => ht v hv h)).uncurry ws =
        t.abstract Δ' hcov_body := by
      conv_lhs => rw [show ws = (fun (⟨i, hi⟩ : Fin vs.length) => (List.ofFn ws)[i]'(by simp; exact hi)) from hws_eq.symm]
      exact SMT.Term.abstract.go.alt_def₂ vs t (List.ofFn ws)
        (by simp [len_eq]) (fun v hv hvs => ht v hv hvs) hcov_body
    rw [eq_body]
    -- Now use of_abstract_gen for the body with Π = Γ.abstract Δ updated by ws.
    apply Typing.of_abstract_gen body_typ hcov_body
    intro v hv d Δ_eq σ Γ_eq
    by_cases hvs : v ∈ vs
    · sorry
    · sorry
  | «forall» Γ vs τs P vs_Γ fresh len_pos len_eq body_typ body_ih =>
    simp only [fv, List.mem_removeAll_iff, and_imp] at ht
    unfold Term.abstract
    rw [dite_cond_eq_true (eq_true len_eq)]
    apply PHOAS.Typing.forall (n_pos := len_pos)
    intro ws vs_inj vs_fresh
    set Δ' := Function.updates «Δ» vs ((List.ofFn ws).map Option.some) with Δ'_def
    have hcov_body : ∀ v ∈ fv P, (Δ' v).isSome = true := by
      intro v hv
      by_cases hvs : v ∈ vs
      · exact Function.updates_isSome_of_mem_map_some «Δ» vs (List.ofFn ws) v hvs (by simp [len_eq])
      · rw [Δ'_def, Function.updates_of_not_mem «Δ» vs ((List.ofFn ws).map Option.some) v hvs]
        exact ht v hv hvs
    have hws_eq : (fun (⟨i, hi⟩ : Fin vs.length) => (List.ofFn ws)[i]'(by simp; exact hi)) = ws := by
      funext ⟨i, hi⟩; simp
    have eq_body :
        (SMT.Term.abstract.go P vs «Δ» (fun v hv h => ht v hv h)).uncurry ws =
        P.abstract Δ' hcov_body := by
      conv_lhs => rw [show ws = (fun (⟨i, hi⟩ : Fin vs.length) => (List.ofFn ws)[i]'(by simp; exact hi)) from hws_eq.symm]
      exact SMT.Term.abstract.go.alt_def₂ vs P (List.ofFn ws)
        (by simp [len_eq]) (fun v hv hvs => ht v hv hvs) hcov_body
    rw [eq_body]
    apply Typing.of_abstract_gen body_typ hcov_body
    intro v hv d Δ_eq σ Γ_eq
    by_cases hvs : v ∈ vs
    · sorry
    · sorry
  | «exists» Γ vs τs P vs_Γ fresh len_pos len_eq body_typ body_ih =>
    simp only [fv, List.mem_removeAll_iff, and_imp] at ht
    unfold Term.abstract
    rw [dite_cond_eq_true (eq_true len_eq)]
    apply PHOAS.Typing.not
    apply PHOAS.Typing.forall (n_pos := len_pos)
    intro ws vs_inj vs_fresh
    sorry


end SMT.PHOAS
