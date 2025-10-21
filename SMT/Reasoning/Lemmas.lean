import SMT.Semantics

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

abbrev WellTyped' (t : PHOAS.Term Dom) := Σ' (Γ : TypeContext Dom) (_ : WFTC Γ) (τ : SMTType), Γ ⊢ t : τ

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
    let den_t_xₙ := ⟦t xₙ⟧ˢ.get (den_is_some (fun i ↦ SMTType.mem_toZFSet_of_defaultZFSet))
    let ξ := den_t_xₙ.2.1
    have all_ξ (x : Fin _ → Dom) (hx : ∀ i, (x i).1 ∈ (τs i).toZFSet) :
        ⟦t x⟧ˢ.get (den_is_some hx) |>.2.1 = ξ := by
      specialize typ_det x xₙ hx ?_
      · intro
        exact SMTType.mem_toZFSet_of_defaultZFSet
      · exact typ_det
    specialize ih xₙ ⟨Γ.update xₙ τs, WFTC.update (congrFun rfl), γ, typ_t xₙ⟩ (Option.eq_some_iff_get_eq.mpr ⟨den_is_some fun i => SMTType.mem_toZFSet_of_defaultZFSet, rfl⟩)
    obtain rfl : γ = ξ := ih
    apply all_ξ
    exact fun i ↦ SMTType.mem_toZFSet_of_defaultZFSet
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
end SMT.PHOAS
