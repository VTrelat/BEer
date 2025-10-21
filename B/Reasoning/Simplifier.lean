import B.Reasoning.SimplifierCorrect.Basic

open Classical B PHOAS ZFSet

/-
example {x : Term} {«Δ»} {Γ}
  (wf_x : x.WF) (typ_x : Γ ⊢ x : .int)
  (h : ∀ v ∈ fv (simplifier (.int 0 *ᴮ x)), («Δ» v).isSome = true)
  (h' : ∀ v ∈ fv (.int 0 *ᴮ x), («Δ» v).isSome = true) :
  ⟦(simplifier (.int 0 *ᴮ x)).abstract «Δ» h⟧ᴮ = ⟦(.int 0 *ᴮ x).abstract «Δ» h'⟧ᴮ := by
  simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_some]

  unfold simplifier simplifier_aux_mul

  conv =>
    enter [1,1]
    conv =>
      arg 1
      rw [simplifier]
    simp only [Term.abstract]
  simp_rw [denote, Option.pure_def]

  cases den_x : ⟦x.abstract «Δ» (fun v hv => h' v (by rw [fv, List.mem_append]; right; exact hv))⟧ᴮ with
  | some X =>
    simp_rw [Option.bind_some]
    obtain ⟨X, τ, hX⟩ := X
    obtain rfl := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, .int,
      Typing.of_abstract (fun v hv => h' v (by rw [fv, List.mem_append]; right; exact hv)) typ_x⟩
      den_x
    rw [Option.some_inj]
    symm
    congr
    · exact overloadBinOp_Int.zero_mul
    · funext
      rw [overloadBinOp_Int.zero_mul]
    · apply proof_irrel_heq
  | none =>
    rw [Option.bind_none]
    -- we're f*cked!
-/

theorem simplifier_partial_correct {t : Term} {«Δ»}
  (ht : ∀ v ∈ fv t, («Δ» v).isSome = true)
  (wf_t : t.WF) {Γ : TypeContext} {τ : BType} (typ_t : Γ ⊢ t : τ)
  {T hTτ}
  (den_t : ⟦t.abstract «Δ» ht⟧ᴮ = some ⟨T, τ, hTτ⟩) :
  ⟦(simplifier t).abstract («Δ» := «Δ») (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ = some ⟨T, τ, hTτ⟩ := by
    induction t generalizing «Δ» Γ T τ hTτ with
    | var | int | bool | «ℤ» | 𝔹 => exact den_t
    | maplet x y x_ih y_ih =>
      exact simplifier_partial_correct.maplet x y x_ih y_ih ht wf_t typ_t den_t
    | add x y x_ih y_ih =>
      exact simplifier_partial_correct.add x y x_ih y_ih ht wf_t typ_t den_t
    | pow S ih =>
      exact simplifier_partial_correct.pow S ih ht wf_t typ_t den_t
    | le x y x_ih y_ih =>
      exact simplifier_partial_correct.le x y x_ih y_ih ht wf_t typ_t den_t
    | mul x y x_ih y_ih =>
      exact simplifier_partial_correct.mul x y x_ih y_ih ht wf_t typ_t den_t
    | min S ih
    | max S ih
    | card S ih =>
      unfold simplifier
      simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind,
        Option.bind_eq_some_iff, PSigma.exists] at den_t
      first
      | obtain ⟨rfl, typS⟩ := Typing.minE typ_t
      | obtain ⟨rfl, typS⟩ := Typing.maxE typ_t
      | obtain ⟨rfl, _, typS⟩ := Typing.cardE typ_t
      obtain ⟨S', β,  hS', den_S, eq⟩ := den_t
      obtain ⟨⟩ := denote_welltyped_eq
        ⟨Γ.abstract («Δ» := «Δ»),
        WFTC.of_abstract, .set _,
        Typing.of_abstract (fun v hv => by apply ht; rw [fv]; exact hv) typS⟩
        den_S
      dsimp at eq
      split_ifs at eq with S'_fin_nemp
      rw [Option.some_inj] at eq
      injection eq
      subst T
      specialize ih _ wf_t typS den_S
      simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, ih,
        Option.bind_some, dite_cond_eq_true (eq_true S'_fin_nemp)]
      try rfl
    | cprod x y x_ih y_ih
    | union x y x_ih y_ih
    | inter x y x_ih y_ih
    | pfun x y x_ih y_ih =>
      unfold simplifier
      simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind,
        Option.bind_eq_some_iff, PSigma.exists] at den_t
      obtain ⟨X, _, hX, den_x, eq⟩ := den_t

      first
      | obtain ⟨α, β, rfl, typx, typy⟩ := Typing.cprodE typ_t
      | obtain ⟨α, rfl, typx, typy⟩ := Typing.unionE typ_t
      | obtain ⟨α, rfl, typx, typy⟩ := Typing.interE typ_t
      | obtain ⟨α, β, rfl, typx, typy⟩ := Typing.pfunE typ_t
      obtain ⟨⟩ := denote_welltyped_eq
        ⟨Γ.abstract («Δ» := «Δ»),
        WFTC.of_abstract, .set _,
        Typing.of_abstract (fun v hv => by apply ht; rw [fv, List.mem_append]; left; exact hv) typx⟩
        den_x

      simp_rw [Option.bind_eq_some_iff, PSigma.exists] at eq
      obtain ⟨Y, _, hY, den_y, eq⟩ := eq
      obtain ⟨⟩ := denote_welltyped_eq
        ⟨Γ.abstract («Δ» := «Δ»),
        WFTC.of_abstract, .set _,
        Typing.of_abstract (fun v hv => by apply ht; rw [fv, List.mem_append]; right; exact hv) typy⟩
        den_y

      simp only [dite_true, Option.some_inj] at eq
      injection eq
      subst T

      specialize x_ih _ wf_t.1 typx den_x
      specialize y_ih _ wf_t.2 typy den_y

      simp only [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind,
        x_ih, Option.bind_some, y_ih, Option.bind_some, dite_true]
    | lambda vs D P D_ih P_ih =>
      exact simplifier_partial_correct.lambda vs D P D_ih P_ih ht wf_t typ_t den_t
    | sub x y x_ih y_ih => sorry
    | and x y x_ih y_ih => sorry
    | not x ih => sorry
    | eq x y x_ih y_ih => sorry
    | mem x S x_ih S_ih => sorry
    | collect vs D P D_ih P_ih => sorry
    | app f x f_ih x_ih => sorry
    | all vs D P D_ih P_ih => sorry
