import B.Reasoning.SimplifierCorrect.Lemmas

open Classical B PHOAS ZFSet

set_option maxHeartbeats 300000 in
theorem simplifier_partial_correct.mul.var.{u_1} {y : B.Term} {«Δ» : 𝒱 → Option B.Dom} {Γ : B.TypeContext}
  (typ_y : Γ ⊢ᴮ y : BType.int) {X Y : ZFSet.{u_1}}
  {hTτ : X *ᶻ Y ∈ BType.int.toZFSet} {v : 𝒱}
  (ht : ∀ v_1 ∈ fv (B.Term.var v *ᴮ y), («Δ» v_1).isSome = true) (wf_t : (B.Term.var v *ᴮ y).WF)
  (typ_t : Γ ⊢ᴮ B.Term.var v *ᴮ y : BType.int) (hX : X ∈ BType.int.toZFSet)
  (den_x : ⟦(B.Term.var v).abstract «Δ» (fun v hv => ht v (by rw [fv, List.mem_append]; left; exact hv))⟧ᴮ = some ⟨X, BType.int, hX⟩) (hY : Y ∈ BType.int.toZFSet)
  (den_y : ⟦y.abstract «Δ» (fun v hv => ht v (by rw [fv, List.mem_append]; right; exact hv))⟧ᴮ = some ⟨Y, BType.int, hY⟩)
  {x_pf : ∀ v_1 ∈ fv (simplifier (B.Term.var v)), («Δ» v_1).isSome = true}
  (x_ih : ⟦(simplifier (B.Term.var v)).abstract «Δ» x_pf⟧ᴮ = some ⟨X, ⟨BType.int, hX⟩⟩)
  {y_pf : ∀ v ∈ fv (simplifier y), («Δ» v).isSome = true}
  (y_ih : ⟦(simplifier y).abstract «Δ» y_pf⟧ᴮ = some ⟨Y, ⟨BType.int, hY⟩⟩) :
  ⟦(simplifier (B.Term.var v *ᴮ y)).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ =
    some ⟨X *ᶻ Y, ⟨BType.int, hTτ⟩⟩ := by
  cases y with
  | var v' =>
    unfold simplifier simplifier_aux_mul
    simp_rw [simplifier, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.some_inj] at x_ih y_ih ⊢
    rw [x_ih, y_ih]
  | int n =>
    unfold simplifier simplifier_aux_mul
    simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at den_x den_y
    by_cases hn : n = 0
    · subst n
      injection den_y
      subst Y
      simp_rw [simplifier, Term.abstract, denote, Option.pure_def, Option.some_inj]
      symm
      congr
      · exact overloadBinOp_Int.mul_zero
      · funext
        rw [overloadBinOp_Int.mul_zero]
      · apply proof_irrel_heq
    · by_cases hn : n = 1
      · subst n
        injection den_y
        subst Y
        simp_rw [simplifier, Term.abstract, denote, Option.pure_def, Option.some_inj, den_x]
        symm
        congr
        · exact overloadBinOp_Int.mul_one
        · funext
          rw [overloadBinOp_Int.mul_one]
        · apply proof_irrel_heq
      · simp_rw [simplifier]
        conv =>
          enter [1,1,1]
          change ?_match
        have : ?_match = .var v *ᴮ .int n := by
          split <;> (injections; try first | contradiction | rfl)
        simp_rw [this]
        injection den_y
        subst Y
        simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_some, den_x]
  | bool
  | maplet
  | le
  | and
  | not
  | eq
  | «ℤ»
  | 𝔹
  | mem
  | collect
  | pow
  | cprod
  | union
  | inter
  | lambda
  | pfun
  | all =>
    nomatch typ_y
  | add a b =>
    unfold simplifier simplifier_aux_mul
    obtain ⟨-, typ_a, typ_b⟩ := Typing.addE typ_y

    simp_rw [simplifier, Term.abstract, denote, Option.pure_def, Option.some_inj] at x_ih

    by_cases h_simp_add_a_b_eq_0 : simplifier (a +ᴮ b) = .int 0
    · simp_rw [h_simp_add_a_b_eq_0, Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih
      injection y_ih with eq
      simp_rw [h_simp_add_a_b_eq_0, simplifier, Term.abstract, denote, Option.pure_def, Option.some_inj]
      congr
      · rw [←eq, overloadBinOp_Int.mul_zero]
      · funext
        rw [←eq, overloadBinOp_Int.mul_zero]
      · apply proof_irrel_heq
    · by_cases h_simp_add_a_b_eq_1 : simplifier (a +ᴮ b) = .int 1
      · simp_rw [h_simp_add_a_b_eq_1, Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih
        injection y_ih with eq
        simp_rw [h_simp_add_a_b_eq_1, simplifier, Term.abstract, denote, Option.pure_def, Option.some_inj]
        rw [x_ih]
        congr
        · rw [←eq, overloadBinOp_Int.mul_one]
        · funext
          rw [←eq, overloadBinOp_Int.mul_one]
        · apply proof_irrel_heq
      · conv =>
          enter [1,1,1]
          conv => arg 2; unfold simplifier
        simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, x_ih, Option.bind_some, y_ih, Option.bind_some]
  | sub a b =>
    unfold simplifier simplifier_aux_mul
    obtain ⟨-, typ_a, typ_b⟩ := Typing.subE typ_y

    simp_rw [simplifier, Term.abstract, denote, Option.pure_def, Option.some_inj, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at x_ih y_ih

    obtain ⟨A, τA, hX, den_a, eq⟩ := y_ih
    obtain ⟨⟩ := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, _,
      Typing.of_abstract (fun v hv => by apply ht; simp_rw [fv, List.mem_append]; right; left; exact fv_simplifier wf_t.2.1 hv) (B.Typing.simplifier typ_a)⟩
      den_a
    simp_rw [Option.bind_eq_some_iff, PSigma.exists] at eq
    obtain ⟨B, τB, hY, den_b, eq⟩ := eq
    obtain ⟨⟩ := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, _,
      Typing.of_abstract (fun v hv => by apply ht; simp_rw [fv, List.mem_append]; right; right; exact (fv_simplifier wf_t.2.2 hv)) (Typing.simplifier typ_b)⟩
      den_b
    rw [Option.some_inj] at eq
    injection eq with eq

    simp_rw [simplifier, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_some, x_ih, den_a, Option.bind_some, den_b, Option.bind_some, Option.some_inj]
    congr 1
    · rw [eq]
    · congr 1
      · funext
        rw [eq]
      · apply proof_irrel_heq
  | mul a b =>
    unfold simplifier simplifier_aux_mul
    obtain ⟨-, typ_a, typ_b⟩ := Typing.mulE typ_y

    simp_rw [simplifier, Term.abstract, denote, Option.pure_def, Option.some_inj] at x_ih

    by_cases h_simp_mul_a_b_eq_0 : simplifier (a *ᴮ b) = .int 0
    · simp_rw [h_simp_mul_a_b_eq_0, Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih
      injection y_ih with eq
      simp_rw [h_simp_mul_a_b_eq_0, simplifier, Term.abstract, denote, Option.pure_def, Option.some_inj]
      congr
      · rw [←eq, overloadBinOp_Int.mul_zero]
      · funext
        rw [←eq, overloadBinOp_Int.mul_zero]
      · apply proof_irrel_heq
    · by_cases h_simp_mul_a_b_eq_1 : simplifier (a *ᴮ b) = .int 1
      · simp_rw [h_simp_mul_a_b_eq_1, Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih
        injection y_ih with eq
        simp_rw [h_simp_mul_a_b_eq_1, simplifier, Term.abstract, denote, Option.pure_def, Option.some_inj]
        rw [x_ih]
        congr
        · rw [←eq, overloadBinOp_Int.mul_one]
        · funext
          rw [←eq, overloadBinOp_Int.mul_one]
        · apply proof_irrel_heq
      · conv =>
          enter [1,1,1]
          conv => arg 2; unfold simplifier
        simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, x_ih, Option.bind_some, y_ih, Option.bind_some]
  | card S =>
    unfold simplifier simplifier_aux_mul
    obtain ⟨-, τS, typ_S⟩ := Typing.cardE typ_y

    simp_rw [simplifier, Term.abstract, denote, Option.pure_def, Option.some_inj] at x_ih
    simp_rw [simplifier, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at y_ih

    obtain ⟨S', τS', hS', den_simpS, eq⟩ := y_ih
    obtain ⟨⟩ := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, _,
      Typing.of_abstract (fun v hv => by apply ht; simp_rw [fv, List.mem_append]; right; exact fv_simplifier wf_t.2 hv) (Typing.simplifier typ_S)⟩
      den_simpS

    dsimp at eq
    split_ifs at eq with S'_fin
    rw [Option.some_inj] at eq
    injection eq with eq

    simp_rw [simplifier, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_some, x_ih, den_simpS, Option.bind_some, dite_cond_eq_true (eq_true S'_fin), Option.bind_some, Option.some_inj]
    congr 2
    · funext
      rw [←eq]
      congr
    · apply proof_irrel_heq
  | app f s =>
    unfold simplifier simplifier_aux_mul
    obtain ⟨α, typ_f, typ_s⟩ := Typing.appE typ_y

    simp_rw [simplifier, Term.abstract, denote, Option.pure_def, Option.some_inj] at x_ih
    simp_rw [simplifier, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at y_ih
    obtain ⟨simpF, τsimpF, hsimpF, den_simpF, eq⟩ := y_ih

    obtain ⟨⟩ := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, _,
      Typing.of_abstract (fun v hv => by apply ht; simp_rw [fv, List.mem_append]; right; left; exact fv_simplifier wf_t.2.1 hv) (Typing.simplifier typ_f)⟩
      den_simpF

    simp_rw [Option.bind_eq_some_iff, PSigma.exists] at eq
    obtain ⟨simpS, τsimpS, hsimpS, den_simpS, eq⟩ := eq
    obtain ⟨⟩ := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, _,
      Typing.of_abstract (fun v hv => by apply ht; simp_rw [fv, List.mem_append]; right; right; exact fv_simplifier wf_t.2.2 hv) (Typing.simplifier typ_s)⟩
      den_simpS
    simp_rw [dite_true] at eq
    split_ifs at eq with simpF_isfunc simpS_mem_simpF_dom
    rw [Option.some_inj] at eq
    injection eq with eq

    simp_rw [simplifier, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, x_ih, Option.bind_some, den_simpF, Option.bind_some, den_simpS, Option.bind_some, dite_true, dite_cond_eq_true (eq_true simpF_isfunc), dite_cond_eq_true (eq_true simpS_mem_simpF_dom), Option.bind_some, Option.some_inj]

    congr 1
    · rw [eq]
    · congr 1
      · funext
        rw [eq]
      · apply proof_irrel_heq
  | min S
  | max S =>
    simp_rw [simplifier, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.some_inj, Option.bind_eq_some_iff, PSigma.exists] at x_ih y_ih

    first
    | obtain ⟨-, typ_S⟩ := Typing.minE typ_y
    | obtain ⟨-, typ_S⟩ := Typing.maxE typ_y

    obtain ⟨S', τS', hS', den_S', eq⟩ := y_ih
    obtain ⟨⟩ := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, _,
      Typing.of_abstract (fun v hv => by apply ht; simp_rw [fv, List.mem_append]; right; exact fv_simplifier wf_t.2 hv) (Typing.simplifier typ_S)⟩
      den_S'
    dsimp at eq
    split_ifs at eq with S'_fin_nemp
    rw [Option.some_inj] at eq
    injection eq
    subst Y

    simp_rw [simplifier, simplifier_aux_mul, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, x_ih, Option.bind_some, den_S', Option.bind_some, dite_cond_eq_true (eq_true S'_fin_nemp), Option.bind_some]

set_option maxHeartbeats 300000 in
theorem simplifier_partial_correct.mul.int.{u_1} {y : B.Term} {«Δ» : 𝒱 → Option B.Dom} {Γ : B.TypeContext}
  (typ_y : Γ ⊢ᴮ y : BType.int) {X Y : ZFSet.{u_1}}
  {hTτ : overloadBinOp_Int (fun x1 x2 => x1 * x2) X Y ∈ BType.int.toZFSet} {n : ℤ}
  (ht : ∀ v ∈ fv (B.Term.int n *ᴮ y), («Δ» v).isSome = true) (wf_t : (B.Term.int n *ᴮ y).WF)
  (typ_t : Γ ⊢ᴮ B.Term.int n *ᴮ y : BType.int) (typ_x : Γ ⊢ᴮ B.Term.int n : BType.int) (hX : X ∈ BType.int.toZFSet)
  (den_x : ⟦(B.Term.int n).abstract «Δ» (fun v hv => ht v (by rw [fv, List.mem_append]; left; exact hv))⟧ᴮ = some ⟨X, ⟨BType.int, hX⟩⟩) (hY : Y ∈ BType.int.toZFSet)
  (den_y : ⟦y.abstract «Δ» ht⟧ᴮ = some ⟨Y, ⟨BType.int, hY⟩⟩)
  {x_pf : ∀ v ∈ fv (simplifier (B.Term.int n)), («Δ» v).isSome = true}
  (x_ih : ⟦(simplifier (B.Term.int n)).abstract «Δ» x_pf⟧ᴮ = some ⟨X, ⟨BType.int, hX⟩⟩)
  {y_pf : ∀ v ∈ fv (simplifier y), («Δ» v).isSome = true}
  (y_ih : ⟦(simplifier y).abstract «Δ» y_pf⟧ᴮ = some ⟨Y, ⟨BType.int, hY⟩⟩) :
  ⟦(simplifier (B.Term.int n *ᴮ y)).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ =
  some ⟨overloadBinOp_Int (fun x1 x2 => x1 * x2) X Y, ⟨BType.int, hTτ⟩⟩ := by
  unfold simplifier
  simp_rw [simplifier, Term.abstract, denote, Option.pure_def, Option.some_inj] at x_ih
  injection x_ih
  subst X

  by_cases n_eq_0 : n = 0
  · unfold simplifier_aux_mul
    subst n
    simp_rw [simplifier, Term.abstract, denote, Option.pure_def, Option.some_inj] at ⊢

    congr
    · rw [overloadBinOp_Int.zero_mul]
    · rw [overloadBinOp_Int.zero_mul]
    · apply proof_irrel_heq
  · by_cases n_eq_1 : n = 1
    · unfold simplifier_aux_mul
      subst n
      cases y with
      | bool
      | maplet
      | le
      | and
      | not
      | eq
      | «ℤ»
      | 𝔹
      | mem
      | collect
      | pow
      | cprod
      | union
      | inter
      | lambda
      | pfun
      | all =>
        nomatch typ_y
      | int m =>
        by_cases m_eq_0 : m = 0
        · subst m
          simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at den_y
          injection den_y
          subst Y

          simp_rw [simplifier, Term.abstract, denote, Option.pure_def, Option.some_inj]
          congr <;> first | rw [overloadBinOp_Int.mul_zero] | apply proof_irrel_heq
        · by_cases m_eq_1 : m = 1
          · subst m
            simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at den_y
            injection den_y
            subst Y

            simp_rw [simplifier, Term.abstract, denote, Option.pure_def, Option.some_inj]
            congr <;> first | rw [overloadBinOp_Int.mul_one] | apply proof_irrel_heq
          · simp only [simplifier, B.Term.int.injEq, m_eq_0, imp_self]
            simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at den_y
            injection den_y
            subst Y
            simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj]
            congr <;> first | rw [overloadBinOp_Int.one_mul] | apply proof_irrel_heq
      | var v =>
        simp_rw [simplifier, Term.abstract, denote, Option.pure_def, Option.some_inj, den_y] at den_y ⊢
        congr <;> first | rw [overloadBinOp_Int.one_mul] | apply proof_irrel_heq
      | add a b =>
        by_cases add_a_b_eq_0 : simplifier (a +ᴮ b) = .int 0
        · simp_rw [add_a_b_eq_0, simplifier, Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih ⊢
          injection y_ih
          subst Y
          congr <;> first | rw [overloadBinOp_Int.mul_zero] | apply proof_irrel_heq
        · by_cases add_a_b_eq_1 : simplifier (a +ᴮ b) = .int 1
          · simp_rw [add_a_b_eq_1, simplifier, Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih ⊢
            injection y_ih
            subst Y
            congr <;> first | rw [overloadBinOp_Int.one_mul] | apply proof_irrel_heq
          · unfold simplifier at add_a_b_eq_0 add_a_b_eq_1 y_ih ⊢
            simp only
            simp_rw [y_ih, Option.some_inj]
            congr <;> first | rw [overloadBinOp_Int.one_mul] | apply proof_irrel_heq
      | sub a b =>
        by_cases sub_a_b_eq_0 : simplifier (a -ᴮ b) = .int 0
        · simp_rw [sub_a_b_eq_0, simplifier, Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih ⊢
          injection y_ih
          subst Y
          congr <;> first | rw [overloadBinOp_Int.mul_zero] | apply proof_irrel_heq
        · by_cases sub_a_b_eq_1 : simplifier (a -ᴮ b) = .int 1
          · simp_rw [sub_a_b_eq_1, simplifier, Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih ⊢
            injection y_ih
            subst Y
            congr <;> first | rw [overloadBinOp_Int.one_mul] | apply proof_irrel_heq
          · unfold simplifier at sub_a_b_eq_0 sub_a_b_eq_1 y_ih ⊢
            simp only
            simp_rw [y_ih, Option.some_inj]
            congr <;> first | rw [overloadBinOp_Int.one_mul] | apply proof_irrel_heq
      | mul a b =>
        by_cases mul_a_b_eq_0 : simplifier (a *ᴮ b) = .int 0
        · simp_rw [mul_a_b_eq_0, simplifier, Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih ⊢
          injection y_ih
          subst Y
          congr <;> first | rw [overloadBinOp_Int.mul_zero] | apply proof_irrel_heq
        · by_cases mul_a_b_eq_1 : simplifier (a *ᴮ b) = .int 1
          · simp_rw [mul_a_b_eq_1, simplifier, Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih ⊢
            injection y_ih
            subst Y
            congr <;> first | rw [overloadBinOp_Int.one_mul] | apply proof_irrel_heq
          · unfold simplifier at mul_a_b_eq_0 mul_a_b_eq_1 y_ih ⊢
            simp only
            simp_rw [y_ih, Option.some_inj]
            congr <;> first | rw [overloadBinOp_Int.one_mul] | apply proof_irrel_heq
      | card S =>
        obtain ⟨-, _, typ_S⟩ := Typing.cardE typ_y
        simp_rw [simplifier, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at y_ih
        obtain ⟨simpS, _, hsimpS, den_simpS, eq⟩ := y_ih
        obtain ⟨⟩ := denote_welltyped_eq
          ⟨Γ.abstract («Δ» := «Δ»),
          WFTC.of_abstract, _,
          Typing.of_abstract (fun v hv => by apply ht; simp_rw [fv, List.mem_append]; right; exact fv_simplifier wf_t.2 hv) (Typing.simplifier typ_S)⟩
          den_simpS
        dsimp at eq
        split_ifs at eq with simpS_fin
        rw [Option.some_inj] at eq
        injection eq
        subst Y

        simp_rw [simplifier, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, den_simpS, Option.bind_some, dite_cond_eq_true (eq_true simpS_fin), Option.some_inj]

        congr 1
        · rw [overloadBinOp_Int.one_mul]
          rfl
        · congr
          · funext
            rw [overloadBinOp_Int.one_mul]
            rfl
          · apply proof_irrel_heq
      | app f s =>
        obtain ⟨_, typ_f, typ_s⟩ := Typing.appE typ_y
        simp_rw [simplifier, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at y_ih
        obtain ⟨F, _, hF, den_f, eq⟩ := y_ih
        obtain ⟨⟩ := denote_welltyped_eq
          ⟨Γ.abstract («Δ» := «Δ»),
          WFTC.of_abstract, _,
          Typing.of_abstract (fun v hv => by apply ht; simp_rw [fv, List.mem_append]; right; left; exact fv_simplifier wf_t.2.1 hv) (Typing.simplifier typ_f)⟩
          den_f

        simp_rw [Option.bind_eq_some_iff, PSigma.exists] at eq
        obtain ⟨S, _, hS, den_s, eq⟩ := eq
        obtain ⟨⟩ := denote_welltyped_eq
          ⟨Γ.abstract («Δ» := «Δ»),
          WFTC.of_abstract, _,
          Typing.of_abstract (fun v hv => by apply ht; simp_rw [fv, List.mem_append]; right; right; exact fv_simplifier wf_t.2.2 hv) (Typing.simplifier typ_s)⟩
          den_s
        simp only [dite_true] at eq
        split_ifs at eq with F_isfunc S_mem_Fdom
        rw [Option.some_inj] at eq
        injection eq
        subst Y

        simp_rw [simplifier, Term.abstract, denote, Option.bind_eq_bind, Option.pure_def, den_f, Option.bind_some, den_s, Option.bind_some, dite_true, dite_cond_eq_true (eq_true F_isfunc), dite_cond_eq_true (eq_true S_mem_Fdom), Option.some_inj]

        congr 1
        · rw [overloadBinOp_Int.one_mul]
        · congr 1
          · rw [overloadBinOp_Int.one_mul]
          · apply proof_irrel_heq
      | min S
      | max S =>
        first
        | obtain ⟨-, typ_S⟩ := Typing.minE typ_y
        | obtain ⟨-, typ_S⟩ := Typing.maxE typ_y
        simp_rw [simplifier, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at y_ih
        obtain ⟨S', τS', hS', den_S, eq⟩ := y_ih
        obtain ⟨⟩ := denote_welltyped_eq
          ⟨Γ.abstract («Δ» := «Δ»),
          WFTC.of_abstract, _,
          Typing.of_abstract (fun v hv => by apply ht; simp_rw [fv, List.mem_append]; right; exact fv_simplifier wf_t.2 hv) (Typing.simplifier typ_S)⟩
          den_S
        dsimp at eq
        split_ifs at eq with S'_fin_nemp
        rw [Option.some_inj] at eq
        injection eq
        subst Y

        simp_rw [simplifier, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, den_S, Option.bind_some, dite_cond_eq_true (eq_true S'_fin_nemp), Option.some_inj]
        congr <;> first | rw [overloadBinOp_Int.one_mul] | apply proof_irrel_heq
    · by_cases simpy_0 : simplifier y = .int 0
      · simp_rw [simpy_0, Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih
        injection y_ih
        subst Y

        simp [simplifier, simpy_0]
        have : simplifier_aux_mul (.int n) (.int 0) = .int 0 := by
          unfold simplifier_aux_mul
          split <;>
          · injections
            first
            | rfl
            | contradiction
            | (try subst_eqs; contradiction)
        simp_rw [this, Term.abstract, denote, Option.pure_def, Option.some_inj]
        congr <;> first | rw [overloadBinOp_Int.mul_zero] | apply proof_irrel_heq
      · by_cases simpy_1 : simplifier y = .int 1
        · simp_rw [simpy_1, Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih
          injection y_ih
          subst Y

          simp [simplifier, simpy_1]
          have : simplifier_aux_mul (.int n) (.int 1) = .int n := by
            unfold simplifier_aux_mul
            split <;>
            · injections
              first
              | rfl
              | contradiction
              | (try subst_eqs; contradiction)
          simp_rw [this, Term.abstract, denote, Option.pure_def, Option.some_inj]
          congr <;> first | rw [overloadBinOp_Int.mul_one] | apply proof_irrel_heq
        · by_cases simpy_int : ∃ m, simplifier y = .int m
          · obtain ⟨m, simpy_int⟩ := simpy_int

            simp_rw [simpy_int, Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih
            injection y_ih
            subst Y

            simp_rw [simpy_int, simplifier]
            have : simplifier_aux_mul (B.Term.int n) (B.Term.int m) = .int (n * m) := by
              unfold simplifier_aux_mul
              split using _ | _ | _ | _ | _ | _ | contr _  <;> injections
              iterate 5
                · injections
                  subst_vars
                  first
                  | contradiction
                  | rfl
              · nomatch contr n m rfl rfl
            simp_rw [this, Term.abstract, denote, Option.pure_def, Option.some_inj]
            congr <;> first | rw [overloadBinOp_Int.const_folding.mul] | apply proof_irrel_heq
          · simp_rw [simplifier]
            have : simplifier_aux_mul (B.Term.int n) (simplifier y) = .int n *ᴮ (simplifier y) := by
              unfold simplifier_aux_mul
              split using _ | _ | _ | _ | contr <;> (injections; try contradiction)
              · push_neg at simpy_int
                nomatch simpy_int _ contr
              · rfl
            simp_rw [this, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_some, y_ih, Option.bind_some]

set_option maxHeartbeats 600000 in
theorem simplifier_partial_correct.mul.add.{u_1} {y : B.Term} {«Δ» : 𝒱 → Option B.Dom} {Γ : B.TypeContext}
  {X Y : ZFSet.{u_1}}
  {hTτ : overloadBinOp_Int (fun x1 x2 => x1 * x2) X Y ∈ BType.int.toZFSet} {a b : B.Term}
  (ht : ∀ v ∈ fv ((a +ᴮ b) *ᴮ y), («Δ» v).isSome = true) (wf_t : ((a +ᴮ b) *ᴮ y).WF)
  (typ_x : Γ ⊢ᴮ a +ᴮ b : BType.int) (hX : X ∈ BType.int.toZFSet)
  (den_x : ⟦(a +ᴮ b).abstract «Δ» (fun v hv => ht v (by rw [fv, List.mem_append]; left; exact hv))⟧ᴮ = some ⟨X, ⟨BType.int, hX⟩⟩) (hY : Y ∈ BType.int.toZFSet)
  (den_y : ⟦y.abstract «Δ» (fun v hv => ht v (by rw [fv, List.mem_append]; right; exact hv))⟧ᴮ = some ⟨Y, ⟨BType.int, hY⟩⟩)
  {pf : ∀ v ∈ fv (simplifier (a +ᴮ b)), («Δ» v).isSome = true}
  (x_ih : ⟦(simplifier (a +ᴮ b)).abstract «Δ» pf⟧ᴮ = some ⟨X, ⟨BType.int, hX⟩⟩)
  {pf_1 : ∀ v ∈ fv (simplifier y), («Δ» v).isSome = true}
  (y_ih : ⟦(simplifier y).abstract «Δ» pf_1⟧ᴮ = some ⟨Y, ⟨BType.int, hY⟩⟩) :
  ⟦(simplifier ((a +ᴮ b) *ᴮ y)).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ =
    some ⟨overloadBinOp_Int (fun x1 x2 => x1 * x2) X Y, ⟨BType.int, hTτ⟩⟩ := by
  unfold simplifier
  by_cases eq0 : simplifier (a +ᴮ b) = .int 0
  · simp_rw [eq0] at x_ih ⊢
    simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at x_ih
    injection x_ih
    subst X

    simp [simplifier_aux_mul]
    simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj]
    congr <;> first | rw [overloadBinOp_Int.zero_mul] | apply proof_irrel_heq
  · by_cases eq1 : simplifier (a +ᴮ b) = .int 1
    · simp_rw [eq1] at x_ih ⊢
      simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at x_ih
      injection x_ih
      subst X

      have : simplifier_aux_mul (B.Term.int 1) (simplifier y) = simplifier y := by
        unfold simplifier_aux_mul
        split <;> (injections; try contradiction)
        · symm; assumption
        · rfl
        · subst_vars
          contradiction
      simp_rw [this, y_ih, Option.some_inj]
      congr <;> first | rw [overloadBinOp_Int.one_mul] | apply proof_irrel_heq
    · by_cases eq_int : ∃ n, simplifier (a +ᴮ b) = .int n
      · obtain ⟨n,  eq_int⟩ := eq_int
        simp_rw [eq_int] at x_ih ⊢
        simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at x_ih
        injection x_ih
        subst X

        by_cases eq0 : simplifier y = .int 0
        · simp_rw [eq0] at y_ih ⊢
          simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih
          injection y_ih
          subst Y
          have : simplifier_aux_mul (.int n) (.int 0) = .int 0 := by
            unfold simplifier_aux_mul
            split <;> (injections; try first | contradiction | rfl)
            · injections
              subst_vars
              contradiction
          simp_rw [this, Term.abstract, denote, Option.pure_def, Option.some_inj]
          congr <;> first | rw [overloadBinOp_Int.mul_zero] | apply proof_irrel_heq
        · by_cases eq1 : simplifier y = .int 1
          · simp_rw [eq1] at y_ih ⊢
            simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih
            injection y_ih
            subst Y

            have : simplifier_aux_mul (.int n) (.int 1) = .int n := by
              unfold simplifier_aux_mul
              split <;> (injections; try first | contradiction | (injections; subst_vars; contradiction) | rfl)
            simp_rw [this, Term.abstract, denote, Option.pure_def, Option.some_inj]
            congr <;> first | rw [overloadBinOp_Int.mul_one] | apply proof_irrel_heq
          · by_cases eq_int : ∃ m, simplifier y = .int m
            · obtain ⟨m, eq_int⟩ := eq_int
              simp_rw [eq_int] at y_ih ⊢
              simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih
              injection y_ih
              subst Y

              have : simplifier_aux_mul (.int n) (.int m) = .int (n * m) := by
                unfold simplifier_aux_mul
                rw [eq_int, B.Term.int.injEq] at eq0 eq1
                rename_i eq0' eq1' eq_int' _ _
                rw [eq_int', B.Term.int.injEq] at eq0' eq1'
                simp only
              simp_rw [this, Term.abstract, denote, Option.pure_def, Option.some_inj]
              congr <;> first | rw [overloadBinOp_Int.const_folding.mul] | apply proof_irrel_heq
            · push_neg at eq_int
              have : simplifier_aux_mul (.int n) (simplifier y) = .int n *ᴮ simplifier y := by
                unfold simplifier_aux_mul
                rename_i eq0' eq1' eq_int' _
                rw [eq_int', B.Term.int.injEq] at eq0' eq1'
                split <;> (injections; try first | contradiction | rfl)
                · nomatch eq_int _ ‹_›
              simp_rw [this, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_some, y_ih, Option.bind_some]
      · by_cases eq0 : simplifier y = .int 0
        · simp_rw [eq0] at y_ih ⊢
          simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih
          injection y_ih
          subst Y

          simp [simplifier_aux_mul]
          simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj]
          congr <;> first | rw [overloadBinOp_Int.mul_zero] | apply proof_irrel_heq
        · by_cases eq1 : simplifier y = .int 1
          · simp_rw [eq1] at y_ih ⊢
            simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih
            injection y_ih
            subst Y

            have : simplifier_aux_mul (simplifier (a +ᴮ b)) (.int 1) = simplifier (a +ᴮ b) := by
              unfold simplifier_aux_mul
              split <;> (injections; try contradiction)
              · rfl
              · subst_vars
                contradiction
              · subst_vars
                contradiction
            simp_rw [this, x_ih, Option.some_inj]
            congr <;> first | rw [overloadBinOp_Int.mul_one] | apply proof_irrel_heq
          · by_cases eq_int : ∃ m, simplifier y = .int m
            · obtain ⟨m, eq_int⟩ := eq_int
              simp_rw [eq_int] at y_ih ⊢
              simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih
              injection y_ih
              subst Y

              by_cases eq_mul : ∃ u k, simplifier (a +ᴮ b) = u *ᴮ .int k
              · obtain ⟨u, k, eq_mul⟩ := eq_mul
                have typ_ := eq_mul ▸ Typing.simplifier typ_x
                obtain ⟨-, typ_u, -⟩ := Typing.mulE typ_
                simp_rw [eq_mul, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at x_ih
                obtain ⟨U, _, hU, den_u, eq⟩ := x_ih
                obtain ⟨⟩ := denote_welltyped_eq
                  ⟨Γ.abstract («Δ» := «Δ»),
                  WFTC.of_abstract, _,
                  Typing.of_abstract (fun v hv => by
                    have : v ∈ fv (simplifier (a +ᴮ b)) := by
                      rw [eq_mul, fv, List.mem_append]
                      left
                      exact hv
                    apply ht
                    rw [fv, List.mem_append]
                    left
                    exact fv_simplifier wf_t.1 this
                  ) typ_u⟩
                  den_u

                dsimp at eq
                rw [Option.some_inj] at eq
                injection eq
                subst X

                have : simplifier_aux_mul (simplifier (a +ᴮ b)) (.int m) = u *ᴮ .int (k * m) := by
                  rw [eq_mul, simplifier_aux_mul] <;>
                  · rintro rfl
                    contradiction
                simp_rw [this, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, den_u, Option.bind_some, Option.some_inj]
                congr 1
                · conv =>
                    enter [1,3]
                    apply overloadBinOp_Int.const_folding.mul k m
                  rw [overloadBinOp_Int.mul_assoc hU (mem_ofInt_Int k) hY]
                · congr 1
                  · funext
                    conv =>
                      enter [1,2,3]
                      apply overloadBinOp_Int.const_folding.mul k m
                    rw [overloadBinOp_Int.mul_assoc hU (mem_ofInt_Int k) hY]
                  · apply proof_irrel_heq
              · push_neg at eq_mul
                have : simplifier_aux_mul (simplifier (a +ᴮ b)) (B.Term.int m) = simplifier (a +ᴮ b) *ᴮ .int m := by
                  unfold simplifier_aux_mul
                  split <;> (injections; try first | contradiction | (subst_vars; contradiction))
                  · rename simplifier (a +ᴮ b) = _ => contr
                    rename ¬∃_, _ = _ => ne_int
                    push_neg at ne_int
                    nomatch ne_int _ contr
                  · nomatch eq_mul _ _ ‹_›
                  · rfl
                simp_rw [this, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, x_ih, Option.bind_some]
            · have : simplifier_aux_mul (simplifier (a +ᴮ b)) (simplifier y) = simplifier (a +ᴮ b) *ᴮ simplifier y := by
                unfold simplifier_aux_mul
                split <;> try contradiction
                · push_neg at eq_int
                  nomatch eq_int _ ‹_›
                · push_neg at eq_int
                  nomatch eq_int _ ‹_›
                · rfl
              simp_rw [this, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, x_ih, Option.bind_some, y_ih, Option.bind_some]

theorem simplifier_partial_correct.mul.sub.{u_1} {y : B.Term} {«Δ» : 𝒱 → Option B.Dom} {Γ : B.TypeContext}
  {X Y : ZFSet.{u_1}}
  {hTτ : overloadBinOp_Int (fun x1 x2 => x1 * x2) X Y ∈ BType.int.toZFSet} {a b : B.Term}
  (ht : ∀ v ∈ fv ((a -ᴮ b) *ᴮ y), («Δ» v).isSome = true) (wf_t : ((a -ᴮ b) *ᴮ y).WF)
  (typ_x : Γ ⊢ᴮ a -ᴮ b : BType.int) (hX : X ∈ BType.int.toZFSet)
  (den_x : ⟦(a -ᴮ b).abstract «Δ» (fun v hv => ht v (by rw [fv, List.mem_append]; left; exact hv))⟧ᴮ = some ⟨X, ⟨BType.int, hX⟩⟩) (hY : Y ∈ BType.int.toZFSet)
  (den_y : ⟦y.abstract «Δ» (fun v hv => ht v (by rw [fv, List.mem_append]; right; exact hv))⟧ᴮ = some ⟨Y, ⟨BType.int, hY⟩⟩)
  {pf : ∀ v ∈ fv (simplifier (a -ᴮ b)), («Δ» v).isSome = true}
  (x_ih : ⟦(simplifier (a -ᴮ b)).abstract «Δ» pf⟧ᴮ = some ⟨X, ⟨BType.int, hX⟩⟩)
  {pf_1 : ∀ v ∈ fv (simplifier y), («Δ» v).isSome = true}
  (y_ih : ⟦(simplifier y).abstract «Δ» pf_1⟧ᴮ = some ⟨Y, ⟨BType.int, hY⟩⟩) :
  ⟦(simplifier ((a -ᴮ b) *ᴮ y)).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ =
  some ⟨overloadBinOp_Int (fun x1 x2 => x1 * x2) X Y, BType.int, hTτ⟩ := by
  unfold simplifier
  by_cases eq0 : simplifier (a -ᴮ b) = .int 0
  · simp_rw [eq0] at x_ih ⊢
    simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at x_ih
    injection x_ih
    subst X

    simp [simplifier_aux_mul]
    simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj]
    congr <;> first | rw [overloadBinOp_Int.zero_mul] | apply proof_irrel_heq
  · by_cases eq1 : simplifier (a -ᴮ b) = .int 1
    · simp_rw [eq1] at x_ih ⊢
      simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at x_ih
      injection x_ih
      subst X

      have : simplifier_aux_mul (B.Term.int 1) (simplifier y) = simplifier y := by
        unfold simplifier_aux_mul
        split <;> injections
      simp_rw [this, y_ih, Option.some_inj]
      congr <;> first | rw [overloadBinOp_Int.one_mul] | apply proof_irrel_heq
    · by_cases eq_int : ∃ n, simplifier (a -ᴮ b) = .int n
      · obtain ⟨n,  eq_int⟩ := eq_int
        simp_rw [eq_int] at x_ih ⊢
        simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at x_ih
        injection x_ih
        subst X

        by_cases eq0 : simplifier y = .int 0
        · simp_rw [eq0] at y_ih ⊢
          simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih
          injection y_ih
          subst Y
          have : simplifier_aux_mul (.int n) (.int 0) = .int 0 := by
            unfold simplifier_aux_mul
            split <;> injections
          simp_rw [this, Term.abstract, denote, Option.pure_def, Option.some_inj]
          congr <;> first | rw [overloadBinOp_Int.mul_zero] | apply proof_irrel_heq
        · by_cases eq1 : simplifier y = .int 1
          · simp_rw [eq1] at y_ih ⊢
            simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih
            injection y_ih
            subst Y

            have : simplifier_aux_mul (.int n) (.int 1) = .int n := by
              unfold simplifier_aux_mul
              split <;> injections
            simp_rw [this, Term.abstract, denote, Option.pure_def, Option.some_inj]
            congr <;> first | rw [overloadBinOp_Int.mul_one] | apply proof_irrel_heq
          · by_cases eq_int : ∃ m, simplifier y = .int m
            · obtain ⟨m, eq_int⟩ := eq_int
              simp_rw [eq_int] at y_ih ⊢
              simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih
              injection y_ih
              subst Y

              have : simplifier_aux_mul (.int n) (.int m) = .int (n * m) := by
                unfold simplifier_aux_mul
                rw [eq_int, B.Term.int.injEq] at eq0 eq1
                rename_i eq0' eq1' eq_int' _ _
                rw [eq_int', B.Term.int.injEq] at eq0' eq1'
                simp only
              simp_rw [this, Term.abstract, denote, Option.pure_def, Option.some_inj]
              congr <;> first | rw [overloadBinOp_Int.const_folding.mul] | apply proof_irrel_heq
            · push_neg at eq_int
              have : simplifier_aux_mul (.int n) (simplifier y) = .int n *ᴮ simplifier y := by
                unfold simplifier_aux_mul
                rename_i eq0' eq1' eq_int' _
                rw [eq_int', B.Term.int.injEq] at eq0' eq1'
                split <;> injections
              simp_rw [this, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_some, y_ih, Option.bind_some]
      · by_cases eq0 : simplifier y = .int 0
        · simp_rw [eq0] at y_ih ⊢
          simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih
          injection y_ih
          subst Y

          simp [simplifier_aux_mul]
          simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj]
          congr <;> first | rw [overloadBinOp_Int.mul_zero] | apply proof_irrel_heq
        · by_cases eq1 : simplifier y = .int 1
          · simp_rw [eq1] at y_ih ⊢
            simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih
            injection y_ih
            subst Y

            have : simplifier_aux_mul (simplifier (a -ᴮ b)) (.int 1) = simplifier (a -ᴮ b) := by
              unfold simplifier_aux_mul
              split <;> (injections; try first | contradiction | rfl)
            simp_rw [this, x_ih, Option.some_inj]
            congr <;> first | rw [overloadBinOp_Int.mul_one] | apply proof_irrel_heq
          · by_cases eq_int : ∃ m, simplifier y = .int m
            · obtain ⟨m, eq_int⟩ := eq_int
              simp_rw [eq_int] at y_ih ⊢
              simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih
              injection y_ih
              subst Y

              by_cases eq_mul : ∃ u k, simplifier (a -ᴮ b) = u *ᴮ .int k
              · obtain ⟨u, k, eq_mul⟩ := eq_mul
                have typ_ := eq_mul ▸ Typing.simplifier typ_x
                obtain ⟨-, typ_u, -⟩ := Typing.mulE typ_
                simp_rw [eq_mul, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at x_ih
                obtain ⟨U, _, hU, den_u, eq⟩ := x_ih
                obtain ⟨⟩ := denote_welltyped_eq
                  ⟨Γ.abstract («Δ» := «Δ»),
                  WFTC.of_abstract, _,
                  Typing.of_abstract (fun v hv => by
                    have : v ∈ fv (simplifier (a -ᴮ b)) := by
                      rw [eq_mul, fv, List.mem_append]
                      left
                      exact hv
                    apply ht
                    rw [fv, List.mem_append]
                    left
                    exact fv_simplifier wf_t.1 this
                  ) typ_u⟩
                  den_u

                dsimp at eq
                rw [Option.some_inj] at eq
                injection eq
                subst X

                have : simplifier_aux_mul (simplifier (a -ᴮ b)) (.int m) = u *ᴮ .int (k * m) := by
                  rw [eq_mul, simplifier_aux_mul] <;>
                  · rintro rfl
                    contradiction
                simp_rw [this, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, den_u, Option.bind_some, Option.some_inj]
                congr 1
                · conv =>
                    enter [1,3]
                    apply overloadBinOp_Int.const_folding.mul k m
                  rw [overloadBinOp_Int.mul_assoc hU (mem_ofInt_Int k) hY]
                · congr 1
                  · funext
                    conv =>
                      enter [1,2,3]
                      apply overloadBinOp_Int.const_folding.mul k m
                    rw [overloadBinOp_Int.mul_assoc hU (mem_ofInt_Int k) hY]
                  · apply proof_irrel_heq
              · push_neg at eq_mul
                have : simplifier_aux_mul (simplifier (a -ᴮ b)) (B.Term.int m) = simplifier (a -ᴮ b) *ᴮ .int m := by
                  unfold simplifier_aux_mul
                  split <;> (injections; try first | contradiction | (subst_vars; contradiction) | rfl)
                simp_rw [this, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, x_ih, Option.bind_some]
            · have : simplifier_aux_mul (simplifier (a -ᴮ b)) (simplifier y) = simplifier (a -ᴮ b) *ᴮ simplifier y := by
                unfold simplifier_aux_mul
                split <;> (injections; try first | contradiction | rfl)
              simp_rw [this, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, x_ih, Option.bind_some, y_ih, Option.bind_some]

set_option maxHeartbeats 400000 in
theorem simplifier_partial_correct.mul.mul.{u_1} {y : B.Term} {«Δ» : 𝒱 → Option B.Dom} {Γ : B.TypeContext}
  {X Y : ZFSet.{u_1}}
  {hTτ : overloadBinOp_Int (fun x1 x2 => x1 * x2) X Y ∈ BType.int.toZFSet} {a b : B.Term}
  (ht : ∀ v ∈ fv (a *ᴮ b *ᴮ y), («Δ» v).isSome = true) (wf_t : (a *ᴮ b *ᴮ y).WF)
  (typ_x : Γ ⊢ᴮ a *ᴮ b : BType.int) (hX : X ∈ BType.int.toZFSet)
  (den_x : ⟦(a *ᴮ b).abstract «Δ» (fun v hv => ht v (by rw [fv, List.mem_append]; left; exact hv))⟧ᴮ = some ⟨X, BType.int, hX⟩) (hY : Y ∈ BType.int.toZFSet)
  (den_y : ⟦y.abstract «Δ» (fun v hv => ht v (by rw [fv, List.mem_append]; right; exact hv))⟧ᴮ = some ⟨Y, BType.int, hY⟩)
  {pf : ∀ v ∈ fv (simplifier (a *ᴮ b)), («Δ» v).isSome = true}
  (x_ih : ⟦(simplifier (a *ᴮ b)).abstract «Δ» pf⟧ᴮ = some ⟨X, ⟨BType.int, hX⟩⟩)
  {pf_1 : ∀ v ∈ fv (simplifier y), («Δ» v).isSome = true}
  (y_ih : ⟦(simplifier y).abstract «Δ» pf_1⟧ᴮ = some ⟨Y, ⟨BType.int, hY⟩⟩) :
  ⟦(simplifier (a *ᴮ b *ᴮ y)).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ =
  some ⟨overloadBinOp_Int (fun x1 x2 => x1 * x2) X Y, BType.int, hTτ⟩ := by
  unfold simplifier
  by_cases eq0 : simplifier (a *ᴮ b) = .int 0
  · simp_rw [eq0] at x_ih ⊢
    simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at x_ih
    injection x_ih
    subst X

    simp [simplifier_aux_mul]
    simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj]
    congr <;> first | rw [overloadBinOp_Int.zero_mul] | apply proof_irrel_heq
  · by_cases eq1 : simplifier (a *ᴮ b) = .int 1
    · simp_rw [eq1] at x_ih ⊢
      simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at x_ih
      injection x_ih
      subst X

      have : simplifier_aux_mul (B.Term.int 1) (simplifier y) = simplifier y := by
        unfold simplifier_aux_mul
        split <;> (injections; try contradiction)
        · symm; assumption
        · rfl
        · subst_vars
          contradiction
      simp_rw [this, y_ih, Option.some_inj]
      congr <;> first | rw [overloadBinOp_Int.one_mul] | apply proof_irrel_heq
    · by_cases eq_int : ∃ n, simplifier (a *ᴮ b) = .int n
      · obtain ⟨n,  eq_int⟩ := eq_int
        simp_rw [eq_int] at x_ih ⊢
        simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at x_ih
        injection x_ih
        subst X

        by_cases eq0 : simplifier y = .int 0
        · simp_rw [eq0] at y_ih ⊢
          simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih
          injection y_ih
          subst Y
          have : simplifier_aux_mul (.int n) (.int 0) = .int 0 := by
            unfold simplifier_aux_mul
            split <;> (injections; try first | contradiction | rfl)
            · injections
              subst_vars
              contradiction
          simp_rw [this, Term.abstract, denote, Option.pure_def, Option.some_inj]
          congr <;> first | rw [overloadBinOp_Int.mul_zero] | apply proof_irrel_heq
        · by_cases eq1 : simplifier y = .int 1
          · simp_rw [eq1] at y_ih ⊢
            simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih
            injection y_ih
            subst Y

            have : simplifier_aux_mul (.int n) (.int 1) = .int n := by
              unfold simplifier_aux_mul
              split <;> (injections; try first | contradiction | rfl | symm; assumption)
              · injections
                subst_vars
                contradiction
            simp_rw [this, Term.abstract, denote, Option.pure_def, Option.some_inj]
            congr <;> first | rw [overloadBinOp_Int.mul_one] | apply proof_irrel_heq
          · by_cases eq_int : ∃ m, simplifier y = .int m
            · obtain ⟨m, eq_int⟩ := eq_int
              simp_rw [eq_int] at y_ih ⊢
              simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih
              injection y_ih
              subst Y

              have : simplifier_aux_mul (.int n) (.int m) = .int (n * m) := by
                unfold simplifier_aux_mul
                rw [eq_int, B.Term.int.injEq] at eq0 eq1
                rename_i eq0' eq1' eq_int' _ _
                rw [eq_int', B.Term.int.injEq] at eq0' eq1'
                simp only
              simp_rw [this, Term.abstract, denote, Option.pure_def, Option.some_inj]
              congr <;> first | rw [overloadBinOp_Int.const_folding.mul] | apply proof_irrel_heq
            · push_neg at eq_int
              have : simplifier_aux_mul (.int n) (simplifier y) = .int n *ᴮ simplifier y := by
                unfold simplifier_aux_mul
                rename_i eq0' eq1' eq_int' _
                rw [eq_int', B.Term.int.injEq] at eq0' eq1'
                split <;> (injections; try first | contradiction | rfl)
                · subst_vars
                  nomatch eq_int _ ‹_›
              simp_rw [this, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_some, y_ih, Option.bind_some]
      · by_cases eq0 : simplifier y = .int 0
        · simp_rw [eq0] at y_ih ⊢
          simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih
          injection y_ih
          subst Y

          simp [simplifier_aux_mul]
          simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj]
          congr <;> first | rw [overloadBinOp_Int.mul_zero] | apply proof_irrel_heq
        · by_cases eq1 : simplifier y = .int 1
          · simp_rw [eq1] at y_ih ⊢
            simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih
            injection y_ih
            subst Y

            have : simplifier_aux_mul (simplifier (a *ᴮ b)) (.int 1) = simplifier (a *ᴮ b) := by
              unfold simplifier_aux_mul
              split <;> (injections; try first | contradiction | rfl) <;>
              · subst_vars
                contradiction
            simp_rw [this, x_ih, Option.some_inj]
            congr <;> first | rw [overloadBinOp_Int.mul_one] | apply proof_irrel_heq
          · by_cases eq_int : ∃ m, simplifier y = .int m
            · obtain ⟨m, eq_int⟩ := eq_int
              simp_rw [eq_int] at y_ih ⊢
              simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih
              injection y_ih
              subst Y

              by_cases eq_mul : ∃ u k, simplifier (a *ᴮ b) = u *ᴮ .int k
              · obtain ⟨u, k, eq_mul⟩ := eq_mul
                have typ_ := eq_mul ▸ Typing.simplifier typ_x
                obtain ⟨-, typ_u, -⟩ := Typing.mulE typ_
                simp_rw [eq_mul, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at x_ih
                obtain ⟨U, _, hU, den_u, eq⟩ := x_ih
                obtain ⟨⟩ := denote_welltyped_eq
                  ⟨Γ.abstract («Δ» := «Δ»),
                  WFTC.of_abstract, _,
                  Typing.of_abstract (fun v hv => by
                    have : v ∈ fv (simplifier (a *ᴮ b)) := by
                      rw [eq_mul, fv, List.mem_append]
                      left
                      exact hv
                    apply ht
                    rw [fv, List.mem_append]
                    left
                    exact fv_simplifier wf_t.1 this
                  ) typ_u⟩
                  den_u

                dsimp at eq
                rw [Option.some_inj] at eq
                injection eq
                subst X

                have : simplifier_aux_mul (simplifier (a *ᴮ b)) (.int m) = u *ᴮ .int (k * m) := by
                  rw [eq_mul, simplifier_aux_mul] <;>
                  · rintro rfl
                    contradiction
                simp_rw [this, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, den_u, Option.bind_some, Option.some_inj]
                congr 1
                · conv =>
                    enter [1,3]
                    apply overloadBinOp_Int.const_folding.mul k m
                  rw [overloadBinOp_Int.mul_assoc hU (mem_ofInt_Int k) hY]
                · congr 1
                  · funext
                    conv =>
                      enter [1,2,3]
                      apply overloadBinOp_Int.const_folding.mul k m
                    rw [overloadBinOp_Int.mul_assoc hU (mem_ofInt_Int k) hY]
                  · apply proof_irrel_heq
              · push_neg at eq_mul
                have : simplifier_aux_mul (simplifier (a *ᴮ b)) (B.Term.int m) = simplifier (a *ᴮ b) *ᴮ .int m := by
                  unfold simplifier_aux_mul
                  split <;> (injections; try first | contradiction | (subst_vars; contradiction) | rfl)
                  · subst_vars
                    rename ¬∃_, _ = _ => ne_int
                    push_neg at ne_int
                    nomatch ne_int _ ‹_›
                  · nomatch eq_mul _ _ ‹_›
                simp_rw [this, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, x_ih, Option.bind_some]
            · have : simplifier_aux_mul (simplifier (a *ᴮ b)) (simplifier y) = simplifier (a *ᴮ b) *ᴮ simplifier y := by
                unfold simplifier_aux_mul
                split <;> (try first | contradiction | rfl) <;>
                · push_neg at eq_int
                  nomatch eq_int _ ‹_›
              simp_rw [this, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, x_ih, Option.bind_some, y_ih, Option.bind_some]

theorem simplifier_partial_correct.mul.card.{u_1} {y : B.Term} {«Δ» : 𝒱 → Option B.Dom} {Γ : B.TypeContext}
  {X Y : ZFSet.{u_1}}
  {hTτ : overloadBinOp_Int (fun x1 x2 => x1 * x2) X Y ∈ BType.int.toZFSet} {S : B.Term}
  (ht : ∀ v ∈ fv (|S|ᴮ *ᴮ y), («Δ» v).isSome = true) (wf_t : (|S|ᴮ *ᴮ y).WF)
  (typ_x : Γ ⊢ᴮ |S|ᴮ : BType.int) (hX : X ∈ BType.int.toZFSet)
  (den_x : ⟦|S|ᴮ.abstract «Δ» (fun v hv => ht v (by rw [fv, List.mem_append]; left; exact hv))⟧ᴮ = some ⟨X, BType.int, hX⟩) (hY : Y ∈ BType.int.toZFSet)
  (den_y : ⟦y.abstract «Δ» (fun v hv => ht v (by rw [fv, List.mem_append]; right; exact hv))⟧ᴮ = some ⟨Y, BType.int, hY⟩)
  {pf : ∀ v ∈ fv (simplifier (|S|ᴮ)), («Δ» v).isSome = true}
  (x_ih : ⟦(simplifier (|S|ᴮ)).abstract «Δ» pf⟧ᴮ = some ⟨X, ⟨BType.int, hX⟩⟩)
  {pf_1 : ∀ v ∈ fv (simplifier y), («Δ» v).isSome = true}
  (y_ih : ⟦(simplifier y).abstract «Δ» pf_1⟧ᴮ = some ⟨Y, ⟨BType.int, hY⟩⟩) :
  ⟦(simplifier (|S|ᴮ *ᴮ y)).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ = some ⟨X *ᶻ Y, BType.int, hTτ⟩ := by
  unfold simplifier
  by_cases eq0 : simplifier (|S|ᴮ) = .int 0
  · simp_rw [eq0] at x_ih ⊢
    simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at x_ih
    injection x_ih
    subst X

    simp [simplifier_aux_mul]
    simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj]
    congr <;> first | rw [overloadBinOp_Int.zero_mul] | apply proof_irrel_heq
  · by_cases eq1 : simplifier (|S|ᴮ) = .int 1
    · simp_rw [eq1] at x_ih ⊢
      simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at x_ih
      injection x_ih
      subst X

      have : simplifier_aux_mul (B.Term.int 1) (simplifier y) = simplifier y := by
        unfold simplifier_aux_mul
        split <;> injections
      simp_rw [this, y_ih, Option.some_inj]
      congr <;> first | rw [overloadBinOp_Int.one_mul] | apply proof_irrel_heq
    · by_cases eq_int : ∃ n, simplifier (|S|ᴮ) = .int n
      · obtain ⟨n,  eq_int⟩ := eq_int
        simp_rw [eq_int] at x_ih ⊢
        simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at x_ih
        injection x_ih
        subst X

        by_cases eq0 : simplifier y = .int 0
        · simp_rw [eq0] at y_ih ⊢
          simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih
          injection y_ih
          subst Y
          have : simplifier_aux_mul (.int n) (.int 0) = .int 0 := by
            unfold simplifier_aux_mul
            split <;> injections
          simp_rw [this, Term.abstract, denote, Option.pure_def, Option.some_inj]
          congr <;> first | rw [overloadBinOp_Int.mul_zero] | apply proof_irrel_heq
        · by_cases eq1 : simplifier y = .int 1
          · simp_rw [eq1] at y_ih ⊢
            simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih
            injection y_ih
            subst Y

            have : simplifier_aux_mul (.int n) (.int 1) = .int n := by
              unfold simplifier_aux_mul
              split <;> injections
            simp_rw [this, Term.abstract, denote, Option.pure_def, Option.some_inj]
            congr <;> first | rw [overloadBinOp_Int.mul_one] | apply proof_irrel_heq
          · by_cases eq_int : ∃ m, simplifier y = .int m
            · obtain ⟨m, eq_int⟩ := eq_int
              simp_rw [eq_int] at y_ih ⊢
              simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih
              injection y_ih
              subst Y

              have : simplifier_aux_mul (.int n) (.int m) = .int (n * m) := by
                unfold simplifier_aux_mul
                rw [eq_int, B.Term.int.injEq] at eq0 eq1
                rename_i eq0' eq1' eq_int' _ _
                rw [eq_int', B.Term.int.injEq] at eq0' eq1'
                simp only
              simp_rw [this, Term.abstract, denote, Option.pure_def, Option.some_inj]
              congr <;> first | rw [overloadBinOp_Int.const_folding.mul] | apply proof_irrel_heq
            · push_neg at eq_int
              have : simplifier_aux_mul (.int n) (simplifier y) = .int n *ᴮ simplifier y := by
                unfold simplifier_aux_mul
                rename_i eq0' eq1' eq_int' _
                rw [eq_int', B.Term.int.injEq] at eq0' eq1'
                split <;> injections
              simp_rw [this, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_some, y_ih, Option.bind_some]
      · by_cases eq0 : simplifier y = .int 0
        · simp_rw [eq0] at y_ih ⊢
          simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih
          injection y_ih
          subst Y

          simp [simplifier_aux_mul]
          simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj]
          congr <;> first | rw [overloadBinOp_Int.mul_zero] | apply proof_irrel_heq
        · by_cases eq1 : simplifier y = .int 1
          · simp_rw [eq1] at y_ih ⊢
            simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih
            injection y_ih
            subst Y

            have : simplifier_aux_mul (simplifier (|S|ᴮ)) (.int 1) = simplifier (|S|ᴮ) := by
              unfold simplifier_aux_mul
              split <;> (injections; try first | contradiction | rfl)
            simp_rw [this, x_ih, Option.some_inj]
            congr <;> first | rw [overloadBinOp_Int.mul_one] | apply proof_irrel_heq
          · by_cases eq_int : ∃ m, simplifier y = .int m
            · obtain ⟨m, eq_int⟩ := eq_int
              simp_rw [eq_int] at y_ih ⊢
              simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih
              injection y_ih
              subst Y

              by_cases eq_mul : ∃ u k, simplifier (|S|ᴮ) = u *ᴮ .int k
              · obtain ⟨u, k, eq_mul⟩ := eq_mul
                have typ_ := eq_mul ▸ Typing.simplifier typ_x
                obtain ⟨-, typ_u, -⟩ := Typing.mulE typ_
                simp_rw [eq_mul, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at x_ih
                obtain ⟨U, _, hU, den_u, eq⟩ := x_ih
                obtain ⟨⟩ := denote_welltyped_eq
                  ⟨Γ.abstract («Δ» := «Δ»),
                  WFTC.of_abstract, _,
                  Typing.of_abstract (fun v hv => by
                    have : v ∈ fv (simplifier (|S|ᴮ)) := by
                      rw [eq_mul, fv, List.mem_append]
                      left
                      exact hv
                    apply ht
                    rw [fv, List.mem_append]
                    left
                    exact fv_simplifier wf_t.1 this
                  ) typ_u⟩
                  den_u

                dsimp at eq
                rw [Option.some_inj] at eq
                injection eq
                subst X

                have : simplifier_aux_mul (simplifier (|S|ᴮ)) (.int m) = u *ᴮ .int (k * m) := by
                  rw [eq_mul, simplifier_aux_mul] <;>
                  · rintro rfl
                    contradiction
                simp_rw [this, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, den_u, Option.bind_some, Option.some_inj]
                congr 1
                · conv =>
                    enter [1,3]
                    apply overloadBinOp_Int.const_folding.mul k m
                  rw [overloadBinOp_Int.mul_assoc hU (mem_ofInt_Int k) hY]
                · congr 1
                  · funext
                    conv =>
                      enter [1,2,3]
                      apply overloadBinOp_Int.const_folding.mul k m
                    rw [overloadBinOp_Int.mul_assoc hU (mem_ofInt_Int k) hY]
                  · apply proof_irrel_heq
              · push_neg at eq_mul
                have : simplifier_aux_mul (simplifier (|S|ᴮ)) (B.Term.int m) = simplifier (|S|ᴮ) *ᴮ .int m := by
                  unfold simplifier_aux_mul
                  split <;> (injections; try first | contradiction | (subst_vars; contradiction) | rfl)
                simp_rw [this, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, x_ih, Option.bind_some]
            · have : simplifier_aux_mul (simplifier (|S|ᴮ)) (simplifier y) = simplifier (|S|ᴮ) *ᴮ simplifier y := by
                unfold simplifier_aux_mul
                split <;> (injections; try first | contradiction | rfl)
              simp_rw [this, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, x_ih, Option.bind_some, y_ih, Option.bind_some]

theorem simplifier_partial_correct.mul.app.{u_1} {y : B.Term} {«Δ» : 𝒱 → Option B.Dom} {Γ : B.TypeContext}
  {X Y : ZFSet.{u_1}}
  {hTτ : overloadBinOp_Int (fun x1 x2 => x1 * x2) X Y ∈ BType.int.toZFSet} {f x : B.Term}
  (ht : ∀ v ∈ fv ((@ᴮf) x *ᴮ y), («Δ» v).isSome = true) (wf_t : ((@ᴮf) x *ᴮ y).WF)
  (typ_x : Γ ⊢ᴮ (@ᴮf) x : BType.int) (hX : X ∈ BType.int.toZFSet)
  (den_x : ⟦((@ᴮf) x).abstract «Δ» (fun v hv => ht v (by rw [fv, List.mem_append]; left; exact hv))⟧ᴮ = some ⟨X, BType.int, hX⟩) (hY : Y ∈ BType.int.toZFSet)
  (den_y : ⟦y.abstract «Δ» (fun v hv => ht v (by rw [fv, List.mem_append]; right; exact hv))⟧ᴮ = some ⟨Y, BType.int, hY⟩)
  {pf : ∀ v ∈ fv (simplifier ((@ᴮf) x)), («Δ» v).isSome = true}
  (x_ih : ⟦(simplifier ((@ᴮf) x)).abstract «Δ» pf⟧ᴮ = some ⟨X, BType.int, hX⟩)
  {pf_1 : ∀ v ∈ fv (simplifier y), («Δ» v).isSome = true}
  (y_ih : ⟦(simplifier y).abstract «Δ» pf_1⟧ᴮ = some ⟨Y, BType.int, hY⟩) :
  ⟦(simplifier ((@ᴮf) x *ᴮ y)).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ = some ⟨X *ᶻ Y, BType.int, hTτ⟩ := by
  unfold simplifier
  by_cases eq0 : simplifier (.app f x) = .int 0
  · simp_rw [eq0] at x_ih ⊢
    simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at x_ih
    injection x_ih
    subst X

    simp [simplifier_aux_mul]
    simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj]
    congr <;> first | rw [overloadBinOp_Int.zero_mul] | apply proof_irrel_heq
  · by_cases eq1 : simplifier (.app f x) = .int 1
    · simp_rw [eq1] at x_ih ⊢
      simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at x_ih
      injection x_ih
      subst X

      have : simplifier_aux_mul (B.Term.int 1) (simplifier y) = simplifier y := by
        unfold simplifier_aux_mul
        split <;> injections
      simp_rw [this, y_ih, Option.some_inj]
      congr <;> first | rw [overloadBinOp_Int.one_mul] | apply proof_irrel_heq
    · by_cases eq_int : ∃ n, simplifier (.app f x) = .int n
      · obtain ⟨n,  eq_int⟩ := eq_int
        simp_rw [eq_int] at x_ih ⊢
        simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at x_ih
        injection x_ih
        subst X

        by_cases eq0 : simplifier y = .int 0
        · simp_rw [eq0] at y_ih ⊢
          simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih
          injection y_ih
          subst Y
          have : simplifier_aux_mul (.int n) (.int 0) = .int 0 := by
            unfold simplifier_aux_mul
            split <;> injections
          simp_rw [this, Term.abstract, denote, Option.pure_def, Option.some_inj]
          congr <;> first | rw [overloadBinOp_Int.mul_zero] | apply proof_irrel_heq
        · by_cases eq1 : simplifier y = .int 1
          · simp_rw [eq1] at y_ih ⊢
            simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih
            injection y_ih
            subst Y

            have : simplifier_aux_mul (.int n) (.int 1) = .int n := by
              unfold simplifier_aux_mul
              split <;> injections
            simp_rw [this, Term.abstract, denote, Option.pure_def, Option.some_inj]
            congr <;> first | rw [overloadBinOp_Int.mul_one] | apply proof_irrel_heq
          · by_cases eq_int : ∃ m, simplifier y = .int m
            · obtain ⟨m, eq_int⟩ := eq_int
              simp_rw [eq_int] at y_ih ⊢
              simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih
              injection y_ih
              subst Y

              have : simplifier_aux_mul (.int n) (.int m) = .int (n * m) := by
                unfold simplifier_aux_mul
                rw [eq_int, B.Term.int.injEq] at eq0 eq1
                rename_i eq0' eq1' eq_int' _ _
                rw [eq_int', B.Term.int.injEq] at eq0' eq1'
                simp only
              simp_rw [this, Term.abstract, denote, Option.pure_def, Option.some_inj]
              congr <;> first | rw [overloadBinOp_Int.const_folding.mul] | apply proof_irrel_heq
            · push_neg at eq_int
              have : simplifier_aux_mul (.int n) (simplifier y) = .int n *ᴮ simplifier y := by
                unfold simplifier_aux_mul
                rename_i eq0' eq1' eq_int' _
                rw [eq_int', B.Term.int.injEq] at eq0' eq1'
                split <;> injections
              simp_rw [this, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_some, y_ih, Option.bind_some]
      · by_cases eq0 : simplifier y = .int 0
        · simp_rw [eq0] at y_ih ⊢
          simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih
          injection y_ih
          subst Y

          simp [simplifier_aux_mul]
          simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj]
          congr <;> first | rw [overloadBinOp_Int.mul_zero] | apply proof_irrel_heq
        · by_cases eq1 : simplifier y = .int 1
          · simp_rw [eq1] at y_ih ⊢
            simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih
            injection y_ih
            subst Y

            have : simplifier_aux_mul (simplifier (.app f x)) (.int 1) = simplifier (.app f x) := by
              unfold simplifier_aux_mul
              split <;> (injections; try first | contradiction | rfl)
            simp_rw [this, x_ih, Option.some_inj]
            congr <;> first | rw [overloadBinOp_Int.mul_one] | apply proof_irrel_heq
          · by_cases eq_int : ∃ m, simplifier y = .int m
            · obtain ⟨m, eq_int⟩ := eq_int
              simp_rw [eq_int] at y_ih ⊢
              simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih
              injection y_ih
              subst Y

              by_cases eq_mul : ∃ u k, simplifier (.app f x) = u *ᴮ .int k
              · obtain ⟨u, k, eq_mul⟩ := eq_mul
                have typ_ := eq_mul ▸ Typing.simplifier typ_x
                obtain ⟨-, typ_u, -⟩ := Typing.mulE typ_
                simp_rw [eq_mul, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at x_ih
                obtain ⟨U, _, hU, den_u, eq⟩ := x_ih
                obtain ⟨⟩ := denote_welltyped_eq
                  ⟨Γ.abstract («Δ» := «Δ»),
                  WFTC.of_abstract, _,
                  Typing.of_abstract (fun v hv => by
                    have : v ∈ fv (simplifier (.app f x)) := by
                      rw [eq_mul, fv, List.mem_append]
                      left
                      exact hv
                    apply ht
                    rw [fv, List.mem_append]
                    left
                    exact fv_simplifier wf_t.1 this
                  ) typ_u⟩
                  den_u

                dsimp at eq
                rw [Option.some_inj] at eq
                injection eq
                subst X

                have : simplifier_aux_mul (simplifier (.app f x)) (.int m) = u *ᴮ .int (k * m) := by
                  rw [eq_mul, simplifier_aux_mul] <;>
                  · rintro rfl
                    contradiction
                simp_rw [this, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, den_u, Option.bind_some, Option.some_inj]
                congr 1
                · conv =>
                    enter [1,3]
                    apply overloadBinOp_Int.const_folding.mul k m
                  rw [overloadBinOp_Int.mul_assoc hU (mem_ofInt_Int k) hY]
                · congr 1
                  · funext
                    conv =>
                      enter [1,2,3]
                      apply overloadBinOp_Int.const_folding.mul k m
                    rw [overloadBinOp_Int.mul_assoc hU (mem_ofInt_Int k) hY]
                  · apply proof_irrel_heq
              · push_neg at eq_mul
                have : simplifier_aux_mul (simplifier (.app f x)) (B.Term.int m) = simplifier (.app f x) *ᴮ .int m := by
                  unfold simplifier_aux_mul
                  split <;> (injections; try first | contradiction | (subst_vars; contradiction) | rfl)
                simp_rw [this, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, x_ih, Option.bind_some]
            · have : simplifier_aux_mul (simplifier (.app f x)) (simplifier y) = simplifier (.app f x) *ᴮ simplifier y := by
                unfold simplifier_aux_mul
                split <;> (injections; try first | contradiction | rfl)
              simp_rw [this, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, x_ih, Option.bind_some, y_ih, Option.bind_some]

theorem simplifier_partial_correct.mul.min.{u_1} {y : B.Term} {«Δ» : 𝒱 → Option B.Dom} {Γ : B.TypeContext}
  {X Y : ZFSet.{u_1}}
  {hTτ : overloadBinOp_Int (fun x1 x2 => x1 * x2) X Y ∈ BType.int.toZFSet} {S : B.Term}
  (ht : ∀ v ∈ fv (S.min *ᴮ y), («Δ» v).isSome = true) (wf_t : (S.min *ᴮ y).WF)
  (typ_x : Γ ⊢ᴮ S.min : BType.int) (hX : X ∈ BType.int.toZFSet)
  (den_x : ⟦S.min.abstract «Δ» (fun v hv => ht v (by rw [fv, List.mem_append]; left; exact hv))⟧ᴮ = some ⟨X, BType.int, hX⟩) (hY : Y ∈ BType.int.toZFSet)
  (den_y : ⟦y.abstract «Δ» (fun v hv => ht v (by rw [fv, List.mem_append]; right; exact hv))⟧ᴮ = some ⟨Y, BType.int, hY⟩)
  {pf : ∀ v ∈ fv (simplifier S.min), («Δ» v).isSome = true}
  (x_ih : ⟦(simplifier S.min).abstract «Δ» pf⟧ᴮ = some ⟨X, BType.int, hX⟩)
  {pf_1 : ∀ v ∈ fv (simplifier y), («Δ» v).isSome = true}
  (y_ih : ⟦(simplifier y).abstract «Δ» pf_1⟧ᴮ = some ⟨Y, BType.int, hY⟩) :
  ⟦(simplifier (S.min *ᴮ y)).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ = some ⟨X *ᶻ Y, BType.int, hTτ⟩ := by
  unfold simplifier
  by_cases eq0 : simplifier S.min = .int 0
  · simp_rw [eq0] at x_ih ⊢
    simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at x_ih
    injection x_ih
    subst X

    simp [simplifier_aux_mul]
    simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj]
    congr <;> first | rw [overloadBinOp_Int.zero_mul] | apply proof_irrel_heq
  · by_cases eq1 : simplifier S.min = .int 1
    · simp_rw [eq1] at x_ih ⊢
      simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at x_ih
      injection x_ih
      subst X

      have : simplifier_aux_mul (B.Term.int 1) (simplifier y) = simplifier y := by
        unfold simplifier_aux_mul
        split <;> injections
      simp_rw [this, y_ih, Option.some_inj]
      congr <;> first | rw [overloadBinOp_Int.one_mul] | apply proof_irrel_heq
    · by_cases eq_int : ∃ n, simplifier S.min = .int n
      · obtain ⟨n,  eq_int⟩ := eq_int
        simp_rw [eq_int] at x_ih ⊢
        simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at x_ih
        injection x_ih
        subst X

        by_cases eq0 : simplifier y = .int 0
        · simp_rw [eq0] at y_ih ⊢
          simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih
          injection y_ih
          subst Y
          have : simplifier_aux_mul (.int n) (.int 0) = .int 0 := by
            unfold simplifier_aux_mul
            split <;> injections
          simp_rw [this, Term.abstract, denote, Option.pure_def, Option.some_inj]
          congr <;> first | rw [overloadBinOp_Int.mul_zero] | apply proof_irrel_heq
        · by_cases eq1 : simplifier y = .int 1
          · simp_rw [eq1] at y_ih ⊢
            simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih
            injection y_ih
            subst Y

            have : simplifier_aux_mul (.int n) (.int 1) = .int n := by
              unfold simplifier_aux_mul
              split <;> injections
            simp_rw [this, Term.abstract, denote, Option.pure_def, Option.some_inj]
            congr <;> first | rw [overloadBinOp_Int.mul_one] | apply proof_irrel_heq
          · by_cases eq_int : ∃ m, simplifier y = .int m
            · obtain ⟨m, eq_int⟩ := eq_int
              simp_rw [eq_int] at y_ih ⊢
              simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih
              injection y_ih
              subst Y

              have : simplifier_aux_mul (.int n) (.int m) = .int (n * m) := by
                unfold simplifier_aux_mul
                rw [eq_int, B.Term.int.injEq] at eq0 eq1
                rename_i eq0' eq1' eq_int' _ _
                rw [eq_int', B.Term.int.injEq] at eq0' eq1'
                simp only
              simp_rw [this, Term.abstract, denote, Option.pure_def, Option.some_inj]
              congr <;> first | rw [overloadBinOp_Int.const_folding.mul] | apply proof_irrel_heq
            · push_neg at eq_int
              have : simplifier_aux_mul (.int n) (simplifier y) = .int n *ᴮ simplifier y := by
                unfold simplifier_aux_mul
                rename_i eq0' eq1' eq_int' _
                rw [eq_int', B.Term.int.injEq] at eq0' eq1'
                split <;> injections
              simp_rw [this, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_some, y_ih, Option.bind_some]
      · by_cases eq0 : simplifier y = .int 0
        · simp_rw [eq0] at y_ih ⊢
          simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih
          injection y_ih
          subst Y

          simp [simplifier_aux_mul]
          simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj]
          congr <;> first | rw [overloadBinOp_Int.mul_zero] | apply proof_irrel_heq
        · by_cases eq1 : simplifier y = .int 1
          · simp_rw [eq1] at y_ih ⊢
            simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih
            injection y_ih
            subst Y

            have : simplifier_aux_mul (simplifier S.min) (.int 1) = simplifier S.min := by
              unfold simplifier_aux_mul
              split <;> (injections; try first | contradiction | rfl)
            simp_rw [this, x_ih, Option.some_inj]
            congr <;> first | rw [overloadBinOp_Int.mul_one] | apply proof_irrel_heq
          · by_cases eq_int : ∃ m, simplifier y = .int m
            · obtain ⟨m, eq_int⟩ := eq_int
              simp_rw [eq_int] at y_ih ⊢
              simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih
              injection y_ih
              subst Y

              by_cases eq_mul : ∃ u k, simplifier S.min = u *ᴮ .int k
              · obtain ⟨u, k, eq_mul⟩ := eq_mul
                have typ_ := eq_mul ▸ Typing.simplifier typ_x
                obtain ⟨-, typ_u, -⟩ := Typing.mulE typ_
                simp_rw [eq_mul, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at x_ih
                obtain ⟨U, _, hU, den_u, eq⟩ := x_ih
                obtain ⟨⟩ := denote_welltyped_eq
                  ⟨Γ.abstract («Δ» := «Δ»),
                  WFTC.of_abstract, _,
                  Typing.of_abstract (fun v hv => by
                    have : v ∈ fv (simplifier S.min) := by
                      rw [eq_mul, fv, List.mem_append]
                      left
                      exact hv
                    apply ht
                    rw [fv, List.mem_append]
                    left
                    exact fv_simplifier wf_t.1 this
                  ) typ_u⟩
                  den_u

                dsimp at eq
                rw [Option.some_inj] at eq
                injection eq
                subst X

                have : simplifier_aux_mul (simplifier S.min) (.int m) = u *ᴮ .int (k * m) := by
                  rw [eq_mul, simplifier_aux_mul] <;>
                  · rintro rfl
                    contradiction
                simp_rw [this, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, den_u, Option.bind_some, Option.some_inj]
                congr 1
                · conv =>
                    enter [1,3]
                    apply overloadBinOp_Int.const_folding.mul k m
                  rw [overloadBinOp_Int.mul_assoc hU (mem_ofInt_Int k) hY]
                · congr 1
                  · funext
                    conv =>
                      enter [1,2,3]
                      apply overloadBinOp_Int.const_folding.mul k m
                    rw [overloadBinOp_Int.mul_assoc hU (mem_ofInt_Int k) hY]
                  · apply proof_irrel_heq
              · push_neg at eq_mul
                have : simplifier_aux_mul (simplifier S.min) (B.Term.int m) = simplifier S.min *ᴮ .int m := by
                  unfold simplifier_aux_mul
                  split <;> (injections; try first | contradiction | (subst_vars; contradiction) | rfl)
                simp_rw [this, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, x_ih, Option.bind_some]
            · have : simplifier_aux_mul (simplifier S.min) (simplifier y) = simplifier S.min *ᴮ simplifier y := by
                unfold simplifier_aux_mul
                split <;> (injections; try first | contradiction | rfl)
              simp_rw [this, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, x_ih, Option.bind_some, y_ih, Option.bind_some]

theorem simplifier_partial_correct.mul.max.{u_1} {y : B.Term} {«Δ» : 𝒱 → Option B.Dom} {Γ : B.TypeContext}
  {X Y : ZFSet.{u_1}}
  {hTτ : overloadBinOp_Int (fun x1 x2 => x1 * x2) X Y ∈ BType.int.toZFSet} {S : B.Term}
  (ht : ∀ v ∈ fv (S.max *ᴮ y), («Δ» v).isSome = true) (wf_t : (S.max *ᴮ y).WF)
  (typ_x : Γ ⊢ᴮ S.max : BType.int) (hX : X ∈ BType.int.toZFSet)
  (den_x : ⟦S.max.abstract «Δ» (fun v hv => ht v (by rw [fv, List.mem_append]; left; exact hv))⟧ᴮ = some ⟨X, BType.int, hX⟩) (hY : Y ∈ BType.int.toZFSet)
  (den_y : ⟦y.abstract «Δ» (fun v hv => ht v (by rw [fv, List.mem_append]; right; exact hv))⟧ᴮ = some ⟨Y, BType.int, hY⟩)
  {pf : ∀ v ∈ fv (simplifier S.max), («Δ» v).isSome = true}
  (x_ih : ⟦(simplifier S.max).abstract «Δ» pf⟧ᴮ = some ⟨X, BType.int, hX⟩)
  {pf_1 : ∀ v ∈ fv (simplifier y), («Δ» v).isSome = true}
  (y_ih : ⟦(simplifier y).abstract «Δ» pf_1⟧ᴮ = some ⟨Y, BType.int, hY⟩) :
  ⟦(simplifier (S.max *ᴮ y)).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ = some ⟨X *ᶻ Y, BType.int, hTτ⟩ := by
  unfold simplifier
  by_cases eq0 : simplifier S.max = .int 0
  · simp_rw [eq0] at x_ih ⊢
    simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at x_ih
    injection x_ih
    subst X

    simp [simplifier_aux_mul]
    simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj]
    congr <;> first | rw [overloadBinOp_Int.zero_mul] | apply proof_irrel_heq
  · by_cases eq1 : simplifier S.max = .int 1
    · simp_rw [eq1] at x_ih ⊢
      simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at x_ih
      injection x_ih
      subst X

      have : simplifier_aux_mul (B.Term.int 1) (simplifier y) = simplifier y := by
        unfold simplifier_aux_mul
        split <;> injections
      simp_rw [this, y_ih, Option.some_inj]
      congr <;> first | rw [overloadBinOp_Int.one_mul] | apply proof_irrel_heq
    · by_cases eq_int : ∃ n, simplifier S.max = .int n
      · obtain ⟨n,  eq_int⟩ := eq_int
        simp_rw [eq_int] at x_ih ⊢
        simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at x_ih
        injection x_ih
        subst X

        by_cases eq0 : simplifier y = .int 0
        · simp_rw [eq0] at y_ih ⊢
          simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih
          injection y_ih
          subst Y
          have : simplifier_aux_mul (.int n) (.int 0) = .int 0 := by
            unfold simplifier_aux_mul
            split <;> injections
          simp_rw [this, Term.abstract, denote, Option.pure_def, Option.some_inj]
          congr <;> first | rw [overloadBinOp_Int.mul_zero] | apply proof_irrel_heq
        · by_cases eq1 : simplifier y = .int 1
          · simp_rw [eq1] at y_ih ⊢
            simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih
            injection y_ih
            subst Y

            have : simplifier_aux_mul (.int n) (.int 1) = .int n := by
              unfold simplifier_aux_mul
              split <;> injections
            simp_rw [this, Term.abstract, denote, Option.pure_def, Option.some_inj]
            congr <;> first | rw [overloadBinOp_Int.mul_one] | apply proof_irrel_heq
          · by_cases eq_int : ∃ m, simplifier y = .int m
            · obtain ⟨m, eq_int⟩ := eq_int
              simp_rw [eq_int] at y_ih ⊢
              simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih
              injection y_ih
              subst Y

              have : simplifier_aux_mul (.int n) (.int m) = .int (n * m) := by
                unfold simplifier_aux_mul
                rw [eq_int, B.Term.int.injEq] at eq0 eq1
                rename_i eq0' eq1' eq_int' _ _
                rw [eq_int', B.Term.int.injEq] at eq0' eq1'
                simp only
              simp_rw [this, Term.abstract, denote, Option.pure_def, Option.some_inj]
              congr <;> first | rw [overloadBinOp_Int.const_folding.mul] | apply proof_irrel_heq
            · push_neg at eq_int
              have : simplifier_aux_mul (.int n) (simplifier y) = .int n *ᴮ simplifier y := by
                unfold simplifier_aux_mul
                rename_i eq0' eq1' eq_int' _
                rw [eq_int', B.Term.int.injEq] at eq0' eq1'
                split <;> injections
              simp_rw [this, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_some, y_ih, Option.bind_some]
      · by_cases eq0 : simplifier y = .int 0
        · simp_rw [eq0] at y_ih ⊢
          simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih
          injection y_ih
          subst Y

          simp [simplifier_aux_mul]
          simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj]
          congr <;> first | rw [overloadBinOp_Int.mul_zero] | apply proof_irrel_heq
        · by_cases eq1 : simplifier y = .int 1
          · simp_rw [eq1] at y_ih ⊢
            simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih
            injection y_ih
            subst Y

            have : simplifier_aux_mul (simplifier S.max) (.int 1) = simplifier S.max := by
              unfold simplifier_aux_mul
              split <;> (injections; try first | contradiction | rfl)
            simp_rw [this, x_ih, Option.some_inj]
            congr <;> first | rw [overloadBinOp_Int.mul_one] | apply proof_irrel_heq
          · by_cases eq_int : ∃ m, simplifier y = .int m
            · obtain ⟨m, eq_int⟩ := eq_int
              simp_rw [eq_int] at y_ih ⊢
              simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at y_ih
              injection y_ih
              subst Y

              by_cases eq_mul : ∃ u k, simplifier S.max = u *ᴮ .int k
              · obtain ⟨u, k, eq_mul⟩ := eq_mul
                have typ_ := eq_mul ▸ Typing.simplifier typ_x
                obtain ⟨-, typ_u, -⟩ := Typing.mulE typ_
                simp_rw [eq_mul, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at x_ih
                obtain ⟨U, _, hU, den_u, eq⟩ := x_ih
                obtain ⟨⟩ := denote_welltyped_eq
                  ⟨Γ.abstract («Δ» := «Δ»),
                  WFTC.of_abstract, _,
                  Typing.of_abstract (fun v hv => by
                    have : v ∈ fv (simplifier S.max) := by
                      rw [eq_mul, fv, List.mem_append]
                      left
                      exact hv
                    apply ht
                    rw [fv, List.mem_append]
                    left
                    exact fv_simplifier wf_t.1 this
                  ) typ_u⟩
                  den_u

                dsimp at eq
                rw [Option.some_inj] at eq
                injection eq
                subst X

                have : simplifier_aux_mul (simplifier S.max) (.int m) = u *ᴮ .int (k * m) := by
                  rw [eq_mul, simplifier_aux_mul] <;>
                  · rintro rfl
                    contradiction
                simp_rw [this, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, den_u, Option.bind_some, Option.some_inj]
                congr 1
                · conv =>
                    enter [1,3]
                    apply overloadBinOp_Int.const_folding.mul k m
                  rw [overloadBinOp_Int.mul_assoc hU (mem_ofInt_Int k) hY]
                · congr 1
                  · funext
                    conv =>
                      enter [1,2,3]
                      apply overloadBinOp_Int.const_folding.mul k m
                    rw [overloadBinOp_Int.mul_assoc hU (mem_ofInt_Int k) hY]
                  · apply proof_irrel_heq
              · push_neg at eq_mul
                have : simplifier_aux_mul (simplifier S.max) (B.Term.int m) = simplifier S.max *ᴮ .int m := by
                  unfold simplifier_aux_mul
                  split <;> (injections; try first | contradiction | (subst_vars; contradiction) | rfl)
                simp_rw [this, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, x_ih, Option.bind_some]
            · have : simplifier_aux_mul (simplifier S.max) (simplifier y) = simplifier S.max *ᴮ simplifier y := by
                unfold simplifier_aux_mul
                split <;> (injections; try first | contradiction | rfl)
              simp_rw [this, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, x_ih, Option.bind_some, y_ih, Option.bind_some]

theorem simplifier_partial_correct.mul.{u_1} (x y : B.Term)
  (x_ih :
    ∀ {«Δ» : 𝒱 → Option B.Dom} (ht : ∀ v ∈ fv x, («Δ» v).isSome = true) (wf_t : x.WF) {Γ : B.TypeContext} {τ : BType},
      Γ ⊢ᴮ x : τ →
        ∀ {T : ZFSet.{u_1}} {hTτ : T ∈ τ.toZFSet},
          ⟦x.abstract «Δ» ht⟧ᴮ = some ⟨T, ⟨τ, hTτ⟩⟩ → ⟦(simplifier x).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ = some ⟨T, ⟨τ, hTτ⟩⟩)
  (y_ih :
    ∀ {«Δ» : 𝒱 → Option B.Dom} (ht : ∀ v ∈ fv y, («Δ» v).isSome = true) (wf_t : y.WF) {Γ : B.TypeContext} {τ : BType},
      Γ ⊢ᴮ y : τ →
        ∀ {T : ZFSet.{u_1}} {hTτ : T ∈ τ.toZFSet},
          ⟦y.abstract «Δ» ht⟧ᴮ = some ⟨T, ⟨τ, hTτ⟩⟩ → ⟦(simplifier y).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ = some ⟨T, ⟨τ, hTτ⟩⟩)
  {«Δ» : 𝒱 → Option B.Dom} (ht : ∀ v ∈ fv (x *ᴮ y), («Δ» v).isSome = true) (wf_t : (x *ᴮ y).WF) {Γ : B.TypeContext}
  {τ : BType} (typ_t : Γ ⊢ᴮ x *ᴮ y : τ) {T : ZFSet.{u_1}} {hTτ : T ∈ τ.toZFSet}
  (den_t : ⟦(x *ᴮ y).abstract «Δ» ht⟧ᴮ = some ⟨T, ⟨τ, hTτ⟩⟩) :
  ⟦(simplifier (x *ᴮ y)).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ = some ⟨T, ⟨τ, hTτ⟩⟩ := by
  simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_t

  obtain ⟨rfl, typ_x, typ_y⟩ := Typing.mulE typ_t

  obtain ⟨X, τX, hX, den_x, eq⟩ := den_t
  obtain rfl := denote_welltyped_eq
    ⟨Γ.abstract («Δ» := «Δ»),
    WFTC.of_abstract, _,
    Typing.of_abstract (fun v hv => by apply ht; rw [fv, List.mem_append]; left; exact hv) typ_x⟩
    den_x

  simp_rw [Option.bind_eq_some_iff, PSigma.exists] at eq
  obtain ⟨Y, τY, hY, den_y, eq⟩ := eq
  obtain rfl := denote_welltyped_eq
    ⟨Γ.abstract («Δ» := «Δ»),
    WFTC.of_abstract, _,
    Typing.of_abstract (fun v hv => by apply ht; rw [fv, List.mem_append]; right; exact hv) typ_y⟩
    den_y
  rw [Option.some_inj] at eq
  injection eq
  subst T

  specialize x_ih _ wf_t.1 typ_x den_x
  specialize y_ih _ wf_t.2 typ_y den_y

  -- all assumptions have been used

  cases x with
  | var v =>
    exact mul.var typ_y ht wf_t typ_t hX den_x hY den_y den_x y_ih
  | int n =>
    exact mul.int typ_y ht wf_t typ_t typ_x hX den_x hY den_y den_x y_ih
  | add a b =>
    exact mul.add ht wf_t typ_x hX den_x hY den_y x_ih y_ih
  | sub a b =>
    exact mul.sub ht wf_t typ_x hX den_x hY den_y x_ih y_ih
  | mul a b =>
    exact mul.mul ht wf_t typ_x hX den_x hY den_y x_ih y_ih
  | card S =>
    exact mul.card ht wf_t typ_x hX den_x hY den_y x_ih y_ih
  | app f x =>
    exact mul.app ht wf_t typ_x hX den_x hY den_y x_ih y_ih
  | min S =>
    exact mul.min ht wf_t typ_x hX den_x hY den_y x_ih y_ih
  | max S =>
    exact mul.max ht wf_t typ_x hX den_x hY den_y x_ih y_ih
  | bool | maplet | le | and | not | eq | «ℤ» | 𝔹 | mem | collect | pow | cprod | union | inter | lambda | pfun | all =>
    nomatch typ_t
