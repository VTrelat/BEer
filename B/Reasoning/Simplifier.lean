import B.Reasoning.SimplifierCorrect.Basic

open Classical B PHOAS ZFSet

/-
example {x : Term} {«Δ»} {Γ}
  (wf_x : x.WF) (typ_x : Γ ⊢ᴮ x : .int)
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
  (wf_t : t.WF) {Γ : TypeContext} {τ : BType} (typ_t : Γ ⊢ᴮ t : τ)
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
    | sub x y x_ih y_ih =>
      unfold simplifier
      simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind,
        Option.bind_eq_some_iff, PSigma.exists] at den_t
      obtain ⟨X, _, hX, den_x, eq⟩ := den_t
      obtain ⟨rfl, typx, typy⟩ := Typing.subE typ_t
      obtain ⟨⟩ := denote_welltyped_eq
        ⟨Γ.abstract («Δ» := «Δ»),
        WFTC.of_abstract, .int,
        Typing.of_abstract (fun v hv => by apply ht; rw [fv, List.mem_append]; left; exact hv) typx⟩
        den_x
      simp_rw [Option.bind_eq_some_iff, PSigma.exists] at eq
      obtain ⟨Y, _, hY, den_y, eq⟩ := eq
      obtain ⟨⟩ := denote_welltyped_eq
        ⟨Γ.abstract («Δ» := «Δ»),
        WFTC.of_abstract, .int,
        Typing.of_abstract (fun v hv => by apply ht; rw [fv, List.mem_append]; right; exact hv) typy⟩
        den_y
      simp only [Option.some_inj] at eq
      injection eq
      subst T
      specialize x_ih _ wf_t.1 typx den_x
      specialize y_ih _ wf_t.2 typy den_y
      simp only [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind,
        x_ih, Option.bind_some, y_ih, Option.bind_some]
    | and x y x_ih y_ih =>
      -- TODO: provable — case on `simplifier_aux_and` using the forward IHs.
      -- The absorbing arms (`bool false`/`bool true`) need boolean-algebra
      -- identities for `overloadBinOp_𝔹 (· ⋀ ·)` (`false ⋀ᶻ Y = false` etc.),
      -- which are not yet in the codebase (only the `overloadBinOp_Int`
      -- analogues exist, in B/Reasoning/Lemmas.lean) and would need proving.
      sorry
    | not x ih =>
      -- STATEMENT IS FALSE — discovered soundness bug in `simplifier_aux_not`
      -- (B/Simplifier.lean:188). The arm `| .not (.not p) => p` is wrong:
      -- `simplifier_aux_not arg` computes `simplify (¬ arg)`, so for `arg = ¬¬p`
      -- the result must be `simplify (¬¬¬p) = ¬p`, i.e. `.not p`, not `p`.
      -- Consequently `simplifier` collapses triple negation: e.g.
      -- `simplifier (¬ᴮ ¬ᴮ ¬ᴮ (.var v)) = .var v` (verified by `#eval`), while
      -- `⟦¬ᴮ ¬ᴮ ¬ᴮ (.var v)⟧ = ¬ᶻ ⟦.var v⟧`. Hence this `not` case of
      -- `simplifier_partial_correct` is genuinely false. Fix belongs in
      -- B/Simplifier.lean (`simplifier_aux_not`): `.not (.not p) => .not p`.
      -- (Note: `simplifier_partial_correct'` only asserts none-preservation,
      -- which the bug does NOT break, so its `not` case remains true & proven.)
      sorry
    | eq x y x_ih y_ih =>
      -- TODO: provable — case on `simplifier_aux_eq` using the forward IHs.
      -- The absorbing arms collapsing to `bool true`/`¬ᴮ p` need boolean-algebra
      -- identities for `=ᶻ` / `overloadBinOp_𝔹` that are not in the codebase.
      sorry
    | mem x S x_ih S_ih =>
      -- TODO: hard — `simplifier_aux_mem` rewrites set-comprehension membership
      -- via substitution; the forward proof needs a substitution-denotation
      -- soundness lemma (`⟦substList vs ts P⟧` vs `⟦P⟧` under env updates) that
      -- is absent from the codebase.
      sorry
    | collect vs D P D_ih P_ih =>
      -- TODO: hard — `simplifier_aux_collect` (`collect v D (.bool true) ⟿ D`)
      -- plus the value-dependent `dite`s in the `collect` denotation; needs
      -- substantial binder/denotation reasoning.
      sorry
    | app f x f_ih x_ih =>
      unfold simplifier
      simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind,
        Option.bind_eq_some_iff, PSigma.exists] at den_t
      obtain ⟨F, _, hF, den_f, eq⟩ := den_t
      obtain ⟨α, typf, typx⟩ := Typing.appE typ_t
      obtain ⟨⟩ := denote_welltyped_eq
        ⟨Γ.abstract («Δ» := «Δ»),
        WFTC.of_abstract, .set _,
        Typing.of_abstract (fun v hv => by apply ht; rw [fv, List.mem_append]; left; exact hv) typf⟩
        den_f
      simp_rw [Option.bind_eq_some_iff, PSigma.exists] at eq
      obtain ⟨X, _, hX, den_x, eq⟩ := eq
      obtain ⟨⟩ := denote_welltyped_eq
        ⟨Γ.abstract («Δ» := «Δ»),
        WFTC.of_abstract, _,
        Typing.of_abstract (fun v hv => by apply ht; rw [fv, List.mem_append]; right; exact hv) typx⟩
        den_x
      split_ifs at eq with τ_eq F_pfunc X_dom
      rw [Option.some_inj] at eq
      injection eq
      subst T
      specialize f_ih _ wf_t.1 typf den_f
      specialize x_ih _ wf_t.2 typx den_x
      simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind,
        f_ih, Option.bind_some, x_ih, Option.bind_some]
      rw [dite_cond_eq_true (eq_true trivial), dite_cond_eq_true (eq_true F_pfunc),
        dite_cond_eq_true (eq_true X_dom)]
    | all vs D P D_ih P_ih =>
      -- TODO: hard — `simplifier_aux_all` rewrites `∀` over comprehensions and
      -- the `all` denotation has value-dependent `dite`s; needs substantial
      -- binder/denotation reasoning.
      sorry
