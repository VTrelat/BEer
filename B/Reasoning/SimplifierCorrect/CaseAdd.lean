import B.Reasoning.SimplifierCorrect.Lemmas

open Classical B PHOAS ZFSet

section simplifier_aux_add

set_option maxHeartbeats 250000 in
theorem simplifier_correct_aux_add.var.{u_1} {«Δ» : 𝒱 → Option B.Dom} {Γ : B.TypeContext} (y : B.Term)
  (fv_y : ∀ v ∈ fv y, («Δ» v).isSome = true) {τ : BType} {X : ZFSet.{u_1}} {hX : X ∈ BType.int.toZFSet}
  {Y : ZFSet.{u_1}} {hY : Y ∈ BType.int.toZFSet} (den_y : ⟦y.abstract «Δ» fv_y⟧ᴮ = some ⟨Y, ⟨BType.int, hY⟩⟩) (v : 𝒱)
  (fv_x : ∀ v_1 ∈ fv (B.Term.var v), («Δ» v_1).isSome = true) (wf_t : (B.Term.var v +ᴮ y).WF)
  (typ_t : Γ ⊢ B.Term.var v +ᴮ y : τ) (den_x : ⟦(B.Term.var v).abstract «Δ» fv_x⟧ᴮ = some ⟨X, ⟨BType.int, hX⟩⟩) :
  ⟦(simplifier_aux_add (B.Term.var v) y).abstract «Δ» (fun v hv => Or.casesOn (List.mem_append.mp (fv_simplifier_aux_add hv)) (fv_x v ·) (fv_y v ·))⟧ᴮ =
    some ⟨X +ᶻ Y, .int, overloadBinOp_mem hX hY⟩ := by
    rw [Term.abstract, denote, Option.pure_def, Option.some_get] at den_x
    cases y with
    | var v =>
      unfold simplifier_aux_add
      rw [Term.abstract, denote, Option.pure_def, Option.some_get] at den_y
      simp_rw [Term.abstract, denote, Option.pure_def, Option.some_get, Option.bind_eq_bind, Option.bind_eq_some_iff]
      exists ⟨X, .int, hX⟩
      simp only [den_x, true_and, Option.bind_eq_some_iff]
      exists ⟨Y, .int, hY⟩
    | int m =>
      rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at den_y
      injection den_y
      subst Y

      rcases eq_or_ne m 0 with rfl | n_ne_zero
      · unfold simplifier_aux_add
        simp_rw [Term.abstract, denote, Option.pure_def, Option.some_get, den_x, Option.some_inj]
        symm
        congr
        · exact overloadBinOp_Int.add_zero hX
        · funext τ
          rw [overloadBinOp_Int.add_zero hX]
        · apply proof_irrel_heq
      · have : simplifier_aux_add (B.Term.var v) (B.Term.int m) = .var v +ᴮ .int m := by
          unfold simplifier_aux_add
          split using _ _ h | _ h _ | _ _ _ _ h | _ _ _ h <;> injections
          · subst m
            contradiction
          · rfl
        simp_rw [this, Term.abstract, denote, Option.pure_def, Option.some_get, Option.bind_eq_bind, Option.bind_eq_some_iff]
        exists ⟨X, .int, hX⟩
    | add a b
    | sub a b
    | mul a b =>
      unfold simplifier_aux_add

      simp only [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_y
      obtain ⟨A, τA, hA, den_a, den_y⟩ := den_y
      rcases typ_t
      rcases ‹Γ ⊢ _ : .int›
      obtain ⟨⟩ := denote_welltyped_eq
        ⟨Γ.abstract («Δ» := «Δ»),
        WFTC.of_abstract, .int,
        Typing.of_abstract (fun v hv => by apply fv_y; rw [fv, List.mem_append]; left; exact hv) ‹_›⟩
        den_a
      simp only [Option.bind_eq_some_iff, PSigma.exists] at den_y
      obtain ⟨B, τB, hB, den_b, den_y⟩ := den_y
      obtain ⟨⟩ := denote_welltyped_eq
        ⟨Γ.abstract («Δ» := «Δ»),
        WFTC.of_abstract, .int,
        Typing.of_abstract (fun v hv => by apply fv_y; rw [fv, List.mem_append]; right; exact hv) ‹_›⟩
        den_b
      simp_rw [Option.some_inj] at den_y
      injection den_y
      subst Y
      simp_rw [Term.abstract, denote, Option.pure_def, Option.some_get, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists]
      exists X, .int, hX
      simp_rw [den_x, true_and, den_a, Option.bind_some, den_b, Option.bind_some]
    | app f z =>
      unfold simplifier_aux_add

      simp only [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_y
      obtain ⟨A, τA, hA, den_a, den_y⟩ := den_y
      rcases typ_t
      rcases ‹Γ ⊢ _ : .int›
      rename_i typ_fz τz typ_z typ_f
      obtain ⟨⟩ := denote_welltyped_eq
        ⟨Γ.abstract («Δ» := «Δ»),
        WFTC.of_abstract, (τz ×ᴮ .int).set,
        Typing.of_abstract (fun v hv => by apply fv_y; rw [fv, List.mem_append]; left; exact hv) typ_f⟩
        den_a
      simp_rw [mem_sUnion, mem_sep, mem_powerset, Option.bind_eq_some_iff] at den_y
      obtain ⟨⟨Z, τz', hZ⟩, den_z, den_z_eq⟩ := den_y
      dsimp at den_z_eq

      split_ifs at den_z_eq with τz_eq_τz' A_pfunc Z_mem_fun
      subst τz'

      rw [Option.some_inj] at den_z_eq
      injection den_z_eq
      subst Y

      simp_rw [Term.abstract, denote, Option.pure_def, Option.some_get, mem_sUnion, mem_sep, mem_powerset, dite_eq_ite, Option.bind_eq_bind, den_x, Option.bind_some, den_a, Option.bind_some, den_z, Option.bind_some, if_true, dite_cond_eq_true (eq_true A_pfunc), dite_cond_eq_true (eq_true Z_mem_fun), Option.bind_some]
    | card
    | min
    | max =>
      unfold simplifier_aux_add

      simp only [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_y
      obtain ⟨A, τA, hA, den_a, den_y⟩ := den_y
      rcases typ_t
      rcases ‹Γ ⊢ _ : .int›
      obtain ⟨⟩ := denote_welltyped_eq
        ⟨Γ.abstract («Δ» := «Δ»),
        WFTC.of_abstract, _,
        Typing.of_abstract (fun v hv => by apply fv_y; rw [fv]; exact hv) ‹_›⟩
        den_a
      simp only [Equiv.toFun_as_coe] at den_y
      split_ifs at den_y with A_fin
      rw [Option.some_inj] at den_y
      injection den_y
      subst Y

      simp only [Term.abstract, denote, Option.pure_def, Option.some_get, Equiv.toFun_as_coe, Option.bind_eq_bind, den_x, Option.bind_some, den_a, Option.bind_some, dite_cond_eq_true (eq_true A_fin)]
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
    | all
    | pfun
    | lambda =>
      rcases typ_t
      rcases ‹Γ ⊢ _ : .int›

set_option maxHeartbeats 250000 in
theorem simplifier_correct_aux_add.int.{u_1} {«Δ» : 𝒱 → Option B.Dom} {Γ : B.TypeContext} (y : B.Term)
  (fv_y : ∀ v ∈ fv y, («Δ» v).isSome = true) {τ : BType} {X : ZFSet.{u_1}} {hX : X ∈ BType.int.toZFSet}
  {Y : ZFSet.{u_1}} {hY : Y ∈ BType.int.toZFSet} (den_y : ⟦y.abstract «Δ» fv_y⟧ᴮ = some ⟨Y, ⟨BType.int, hY⟩⟩) (n : ℤ)
  (fv_x : ∀ v ∈ fv (B.Term.int n), («Δ» v).isSome = true) (wf_t : (B.Term.int n +ᴮ y).WF)
  (typ_t : Γ ⊢ B.Term.int n +ᴮ y : τ) (den_x : ⟦(B.Term.int n).abstract «Δ» fv_x⟧ᴮ = some ⟨X, ⟨BType.int, hX⟩⟩) :
  ⟦(simplifier_aux_add (B.Term.int n) y).abstract «Δ» (fun v hv => Or.casesOn (List.mem_append.mp (fv_simplifier_aux_add hv)) (fv_x v ·) (fv_y v ·))⟧ᴮ =
    some ⟨X +ᶻ Y, .int, overloadBinOp_mem hX hY⟩ := by
    rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at den_x
    injection den_x
    subst X

    rcases eq_or_ne n 0 with rfl | n_ne_zero
    · unfold simplifier_aux_add
      simp only [den_y, Option.some_inj]
      symm
      congr
      · exact overloadBinOp_Int.zero_add hY
      · funext τ
        rw [overloadBinOp_Int.zero_add hY]
      · apply proof_irrel_heq
    · induction y with
      | var v =>
        rw [Term.abstract, denote, Option.pure_def, Option.some_get] at den_y

        have : simplifier_aux_add (B.Term.int n) (B.Term.var v) = .int n +ᴮ .var v := by
          unfold simplifier_aux_add
          split using _ _ h | _ h _ | _ _ _ _ h | _ _ _ h <;> injections
          · subst n
            contradiction
          · rfl
        simp_rw [this, Term.abstract, denote, Option.pure_def, Option.some_get, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists]
        exists ZFSet.ofInt n, .int, hX
        simp_rw [true_and, Option.bind_eq_some_iff, den_y, Option.some_inj, exists_eq_left']
      | int m =>
        rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at den_y
        injection den_y
        subst Y

        have : simplifier_aux_add (B.Term.int n) (B.Term.int m) = .int (n + m) := by
          unfold simplifier_aux_add
          split using _ _ h | _ h _ | _ _ _ _ h | _ _ _ h | h _ <;> injections
          · injections
            subst n
            rw [zero_add]
          · injections
            subst m
            rw [add_zero]
          · injections
            subst n m
            rfl
          · nomatch h n m rfl rfl
        simp_rw [this, Term.abstract, denote, Option.pure_def, Option.some_inj]
        congr
        · exact overloadBinOp_Int.const_folding.add n m
        · funext τ
          rw [overloadBinOp_Int.const_folding.add n m]
        · apply proof_irrel_heq
      | add a b a_ih b_ih =>
        simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_y
        obtain ⟨A, τA, hA, den_a, den_b⟩ := den_y
        rcases typ_t
        rcases ‹Γ ⊢ _ : .int›
        obtain ⟨⟩ := denote_welltyped_eq
          ⟨Γ.abstract («Δ» := «Δ»),
          WFTC.of_abstract, .int,
          Typing.of_abstract (fun v hv => by apply fv_y; rw [fv, List.mem_append]; left; exact hv) ‹_›⟩
          den_a

        simp_rw [Option.bind_eq_some_iff, PSigma.exists] at den_b
        obtain ⟨B, τB, hB, den_b, den_y⟩ := den_b
        obtain ⟨⟩ := denote_welltyped_eq
          ⟨Γ.abstract («Δ» := «Δ»),
          WFTC.of_abstract, .int,
          Typing.of_abstract (fun v hv => by apply fv_y; rw [fv, List.mem_append]; right; exact hv) ‹_›⟩
          den_b

        rw [Option.some_inj] at den_y
        injection den_y
        subst Y

        have : simplifier_aux_add (.int n) (a +ᴮ b)  = .int n +ᴮ (a +ᴮ b) := by
          unfold simplifier_aux_add
          split using _ _ h | _ h _ | _ _ _ _ h | _ _ _ h <;> injections
          · injections
            subst n
            contradiction
          · rfl
        simp_rw [this, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some_inj, exists_eq_left', den_a, Option.bind_some, den_b, Option.bind_some]
      | sub a b a_ih b_ih =>
        simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_y
        obtain ⟨A, τA, hA, den_a, den_b⟩ := den_y
        rcases typ_t
        rcases ‹Γ ⊢ _ : .int›
        obtain ⟨⟩ := denote_welltyped_eq
          ⟨Γ.abstract («Δ» := «Δ»),
          WFTC.of_abstract, .int,
          Typing.of_abstract (fun v hv => by apply fv_y; rw [fv, List.mem_append]; left; exact hv) ‹_›⟩
          den_a

        simp_rw [Option.bind_eq_some_iff, PSigma.exists] at den_b
        obtain ⟨B, τB, hB, den_b, den_y⟩ := den_b
        obtain ⟨⟩ := denote_welltyped_eq
          ⟨Γ.abstract («Δ» := «Δ»),
          WFTC.of_abstract, .int,
          Typing.of_abstract (fun v hv => by apply fv_y; rw [fv, List.mem_append]; right; exact hv) ‹_›⟩
          den_b

        rw [Option.some_inj] at den_y
        injection den_y
        subst Y

        have : simplifier_aux_add (.int n) (a -ᴮ b)  = .int n +ᴮ (a -ᴮ b) := by
          unfold simplifier_aux_add
          split using _ _ h | _ h _ | _ _ _ _ h | _ _ _ h <;> injections
          · injections
            subst n
            contradiction
          · rfl
        simp_rw [this, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some_inj, exists_eq_left', den_a, Option.bind_some, den_b, Option.bind_some]
      | mul a b a_ih b_ih =>
        simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_y
        obtain ⟨A, τA, hA, den_a, den_b⟩ := den_y
        rcases typ_t
        rcases ‹Γ ⊢ _ : .int›
        obtain ⟨⟩ := denote_welltyped_eq
          ⟨Γ.abstract («Δ» := «Δ»),
          WFTC.of_abstract, .int,
          Typing.of_abstract (fun v hv => by apply fv_y; rw [fv, List.mem_append]; left; exact hv) ‹_›⟩
          den_a

        simp_rw [Option.bind_eq_some_iff, PSigma.exists] at den_b
        obtain ⟨B, τB, hB, den_b, den_y⟩ := den_b
        obtain ⟨⟩ := denote_welltyped_eq
          ⟨Γ.abstract («Δ» := «Δ»),
          WFTC.of_abstract, .int,
          Typing.of_abstract (fun v hv => by apply fv_y; rw [fv, List.mem_append]; right; exact hv) ‹_›⟩
          den_b

        rw [Option.some_inj] at den_y
        injection den_y
        subst Y

        have : simplifier_aux_add (.int n) (a *ᴮ b)  = .int n +ᴮ (a *ᴮ b) := by
          unfold simplifier_aux_add
          split using _ _ h | _ h _ | _ _ _ _ h | _ _ _ h <;> injections
          · injections
            subst n
            contradiction
          · rfl
        simp_rw [this, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some_inj, exists_eq_left', den_a, Option.bind_some, den_b, Option.bind_some]
      | card S ih =>
        simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_y
        obtain ⟨A, τA, hA, den_a, den_y⟩ := den_y
        rcases typ_t
        rcases ‹Γ ⊢ _ : .int›
        obtain ⟨⟩ := denote_welltyped_eq
          ⟨Γ.abstract («Δ» := «Δ»),
          WFTC.of_abstract, .set _,
          Typing.of_abstract (fun v hv => by apply fv_y; rw [fv]; exact hv) ‹_›⟩
          den_a

        dsimp at den_y
        split_ifs at den_y with A_fin
        rw [Option.some_inj] at den_y
        injection den_y
        subst Y

        have : simplifier_aux_add (.int n) (B.Term.card S)  = .int n +ᴮ B.Term.card S := by
          unfold simplifier_aux_add
          split using _ _ h | _ h _ | _ _ _ _ h | _ _ _ h <;> injections
          · injections
            subst n
            contradiction
          · rfl
        simp_rw [this, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some_inj, exists_eq_left', den_a, Option.bind_some, dite_cond_eq_true (eq_true A_fin), Option.bind_some, Option.some_inj, Equiv.toFun_as_coe]
      | app f x f_ih x_ih =>
        simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_y
        obtain ⟨F, τF, hF, den_f, den_x⟩ := den_y
        rcases typ_t
        rcases ‹Γ ⊢ _ : .int›
        obtain ⟨⟩ := denote_welltyped_eq
          ⟨Γ.abstract («Δ» := «Δ»),
          WFTC.of_abstract, .set (_ ×ᴮ .int),
          Typing.of_abstract (fun v hv => by apply fv_y; rw [fv, List.mem_append]; left; exact hv) ‹_›⟩
          den_f

        simp_rw [Option.bind_eq_some_iff, PSigma.exists] at den_x
        obtain ⟨X, τX, hX, den_x, den_y⟩ := den_x
        obtain ⟨⟩ := denote_welltyped_eq
          ⟨Γ.abstract («Δ» := «Δ»),
          WFTC.of_abstract, _,
          Typing.of_abstract (fun v hv => by apply fv_y; rw [fv, List.mem_append]; right; exact hv) ‹_›⟩
          den_x

        split_ifs at den_y with _ F_pfunc X_F_dom
        rw [Option.some_inj] at den_y
        injection den_y
        subst Y

        have : simplifier_aux_add (.int n) (B.Term.app f x)  = .int n +ᴮ (B.Term.app f x) := by
          unfold simplifier_aux_add
          split using _ _ h | _ h _ | _ _ _ _ h | _ _ _ h <;> injections
          · injections
            subst n
            contradiction
          · rfl
        simp_rw [this, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some_inj, exists_eq_left', den_f, Option.bind_some, den_x, Option.bind_some, dite_true, dite_cond_eq_true (eq_true F_pfunc), dite_cond_eq_true (eq_true X_F_dom), Option.bind_some]
      | min S ih =>
        simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_y
        obtain ⟨A, τA, hA, den_a, den_y⟩ := den_y
        rcases typ_t
        rcases ‹Γ ⊢ _ : .int›
        obtain ⟨⟩ := denote_welltyped_eq
          ⟨Γ.abstract («Δ» := «Δ»),
          WFTC.of_abstract, .set _,
          Typing.of_abstract (fun v hv => by apply fv_y; rw [fv]; exact hv) ‹_›⟩
          den_a

        dsimp at den_y
        split_ifs at den_y with A_fin
        rw [Option.some_inj] at den_y
        injection den_y
        subst Y

        have : simplifier_aux_add (.int n) (B.Term.min S)  = .int n +ᴮ B.Term.min S := by
          unfold simplifier_aux_add
          split using _ _ h | _ h _ | _ _ _ _ h | _ _ _ h <;> injections
          · injections
            subst n
            contradiction
          · rfl
        simp_rw [this, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some_inj, exists_eq_left', den_a, Option.bind_some, dite_cond_eq_true (eq_true A_fin), Option.bind_some]
      | max S ih =>
        simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_y
        obtain ⟨A, τA, hA, den_a, den_y⟩ := den_y
        rcases typ_t
        rcases ‹Γ ⊢ _ : .int›
        obtain ⟨⟩ := denote_welltyped_eq
          ⟨Γ.abstract («Δ» := «Δ»),
          WFTC.of_abstract, .set _,
          Typing.of_abstract (fun v hv => by apply fv_y; rw [fv]; exact hv) ‹_›⟩
          den_a

        dsimp at den_y
        split_ifs at den_y with A_fin
        rw [Option.some_inj] at den_y
        injection den_y
        subst Y

        have : simplifier_aux_add (.int n) (B.Term.max S)  = .int n +ᴮ B.Term.max S := by
          unfold simplifier_aux_add
          split using _ _ h | _ h _ | _ _ _ _ h | _ _ _ h <;> injections
          · injections
            subst n
            contradiction
          · rfl
        simp_rw [this, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some_inj, exists_eq_left', den_a, Option.bind_some, dite_cond_eq_true (eq_true A_fin), Option.bind_some]
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
      | cprod
      | pow
      | union
      | inter
      | lambda
      | pfun
      | all =>
        rcases typ_t
        rcases ‹Γ ⊢ _ : .int›

set_option maxHeartbeats 250000 in
theorem simplifier_correct_aux_add.add.{u_1} {«Δ» : 𝒱 → Option B.Dom} {Γ : B.TypeContext} (y : B.Term)
  (fv_y : ∀ v ∈ fv y, («Δ» v).isSome = true) {τ : BType} {X : ZFSet.{u_1}} {hX : X ∈ BType.int.toZFSet}
  {Y : ZFSet.{u_1}} {hY : Y ∈ BType.int.toZFSet} (den_y : ⟦y.abstract «Δ» fv_y⟧ᴮ = some ⟨Y, ⟨BType.int, hY⟩⟩)
  (a b : B.Term)
  (fv_x : ∀ v ∈ fv (a +ᴮ b), («Δ» v).isSome = true) (wf_t : (a +ᴮ b +ᴮ y).WF) (typ_t : Γ ⊢ a +ᴮ b +ᴮ y : τ)
  (den_x : ⟦(a +ᴮ b).abstract «Δ» fv_x⟧ᴮ = some ⟨X, ⟨BType.int, hX⟩⟩) :
  ⟦(simplifier_aux_add (a +ᴮ b) y).abstract «Δ» (fun v hv => Or.casesOn (List.mem_append.mp (fv_simplifier_aux_add hv)) (fv_x v ·) (fv_y v ·))⟧ᴮ =
    some ⟨X +ᶻ Y, .int, overloadBinOp_mem hX hY⟩ := by
    simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_x

    obtain ⟨A, τA, hA, den_a, den_y⟩ := den_x

    rcases typ_t
    rename Γ ⊢ y : .int => typ_y
    rcases ‹Γ ⊢ a +ᴮ b : .int›
    obtain ⟨⟩ := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, .int,
      Typing.of_abstract (fun v hv => by apply fv_x; rw [fv, List.mem_append]; left; exact hv) ‹_›⟩
      den_a
    simp_rw [Option.bind_eq_some_iff, PSigma.exists] at den_y
    obtain ⟨B, τB, hB, den_b, den_x⟩ := den_y
    obtain ⟨⟩ := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, .int,
      Typing.of_abstract (fun v hv => by apply fv_x; rw [fv, List.mem_append]; right; exact hv) ‹_›⟩
      den_b
    rw [Option.some_inj] at den_x
    injection den_x
    subst X

    cases y with
    | var v =>
      unfold simplifier_aux_add
      simp_rw [Term.abstract, denote, Option.pure_def, Option.some_get] at den_y
      simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, den_a, Option.some_inj, den_b, Option.bind_some, exists_eq_left', Option.some_inj, exists_eq_left', den_y, Option.get_some]
    | int n =>
      simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at den_y
      injection den_y
      subst Y

      rcases eq_or_ne n 0 with rfl | n_ne_zero
      · simp_rw [simplifier_aux_add, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, den_a, Option.bind_some, den_b, Option.bind_some, Option.some_inj]
        symm
        congr 1
        · exact overloadBinOp_Int.add_zero hX
        · congr 1
          · funext τ
            rw [overloadBinOp_Int.add_zero hX]
          · apply proof_irrel_heq
      · by_cases hb : ∃ k, b = .int k
        · obtain ⟨k, rfl⟩ := hb
          have : simplifier_aux_add (a +ᴮ .int k) (.int n) = a +ᴮ .int (k + n) := by
            rw [simplifier_aux_add]
            exact fun x => n_ne_zero x

          simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at den_b
          injection den_b
          subst B
          simp_rw [this, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_some, den_a, Option.bind_some, Option.some_inj]
          congr 1
          · rw [← overloadBinOp_Int.add_assoc hA hB hY, overloadBinOp_Int.const_folding.add k n]
          · congr 1
            · funext τ
              rw [← overloadBinOp_Int.add_assoc hA hB hY, overloadBinOp_Int.const_folding.add k n]
            · apply proof_irrel_heq
        · have : simplifier_aux_add (a +ᴮ b) (.int n) = a +ᴮ b +ᴮ .int n := by
            unfold simplifier_aux_add
            split <;> injections
            · injections
              subst n
              contradiction
            · injections
              push_neg at hb
              nomatch hb _ ‹b = _›
            · rfl
          simp_rw [this, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_some, den_a, Option.bind_some, den_b, Option.bind_some]
    | add
    | sub
    | mul =>
      unfold simplifier_aux_add

      simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_y
      obtain ⟨C, τC, hC, den_c, den_y⟩ := den_y
      rcases typ_y
      obtain ⟨⟩ := denote_welltyped_eq
        ⟨Γ.abstract («Δ» := «Δ»),
        WFTC.of_abstract, .int,
        Typing.of_abstract (fun v hv => by apply fv_y; rw [fv, List.mem_append]; left; exact hv) ‹_›⟩
        den_c
      simp_rw [Option.bind_eq_some_iff, PSigma.exists] at den_y
      obtain ⟨D, τD, hD, den_d, den_y⟩ := den_y
      obtain ⟨⟩ := denote_welltyped_eq
        ⟨Γ.abstract («Δ» := «Δ»),
        WFTC.of_abstract, .int,
        Typing.of_abstract (fun v hv => by apply fv_y; rw [fv, List.mem_append]; right; exact hv) ‹_›⟩
        den_d
      rw [Option.some_inj] at den_y
      injection den_y
      subst Y

      simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, den_a, Option.bind_some, den_b, Option.bind_some, den_c, Option.bind_some, den_d, Option.bind_some]
    | min S
    | max S
    | card S =>
      unfold simplifier_aux_add

      simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_y
      obtain ⟨C, τC, hC, den_c, den_y⟩ := den_y
      rcases typ_y
      obtain ⟨⟩ := denote_welltyped_eq
        ⟨Γ.abstract («Δ» := «Δ»),
        WFTC.of_abstract, _,
        Typing.of_abstract (fun v hv => by apply fv_y; rw [fv]; exact hv) ‹_›⟩
        den_c
      dsimp at den_y
      split_ifs at den_y with C_fin
      rw [Option.some_inj] at den_y
      injection den_y
      subst Y

      simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, den_a, Option.bind_some, den_b, Option.bind_some, den_c, Option.bind_some, dite_cond_eq_true (eq_true C_fin)]
      rfl
    | app f z =>
      unfold simplifier_aux_add

      simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_y
      obtain ⟨F, τF, hF, den_f, den_y⟩ := den_y
      rcases typ_y
      obtain ⟨⟩ := denote_welltyped_eq
        ⟨Γ.abstract («Δ» := «Δ»),
        WFTC.of_abstract, (_ ×ᴮ .int).set,
        Typing.of_abstract (fun v hv => by apply fv_y; rw [fv, List.mem_append]; left; exact hv) ‹_›⟩
        den_f
      simp_rw [Option.bind_eq_some_iff, PSigma.exists] at den_y
      obtain ⟨Z, τZ, hZ, den_z, den_y⟩ := den_y
      obtain ⟨⟩ := denote_welltyped_eq
        ⟨Γ.abstract («Δ» := «Δ»),
        WFTC.of_abstract, _,
        Typing.of_abstract (fun v hv => by apply fv_y; rw [fv, List.mem_append]; right; exact hv) ‹_›⟩
        den_z
      rw [dite_cond_eq_true (eq_true rfl)] at den_y
      split_ifs at den_y with F_isfunc Z_dom_F
      rw [Option.some_inj] at den_y
      injection den_y
      subst Y

      simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, den_a, Option.bind_some, den_b, Option.bind_some, den_f, Option.bind_some, den_z, Option.bind_some, dite_true, dite_cond_eq_true (eq_true F_isfunc), dite_cond_eq_true (eq_true Z_dom_F), Option.bind_some]
    | bool | maplet | le | and | not | eq | «ℤ» | 𝔹 | mem | collect | pow | cprod | union | inter | lambda | pfun | all =>
      rcases typ_y

theorem simplifier_correct_aux_add.sub.{u_1} {«Δ» : 𝒱 → Option B.Dom} {Γ : B.TypeContext} (y : B.Term)
  (fv_y : ∀ v ∈ fv y, («Δ» v).isSome = true) {X : ZFSet.{u_1}} {hX : X ∈ BType.int.toZFSet} {Y : ZFSet.{u_1}}
  {hY : Y ∈ BType.int.toZFSet} (den_y : ⟦y.abstract «Δ» fv_y⟧ᴮ = some ⟨Y, ⟨BType.int, hY⟩⟩) (a b : B.Term)
  (fv_x : ∀ v ∈ fv (a -ᴮ b), («Δ» v).isSome = true) (wf_t : (a -ᴮ b +ᴮ y).WF) (typ_t : Γ ⊢ a -ᴮ b +ᴮ y : BType.int)
  (den_x : ⟦(a -ᴮ b).abstract «Δ» fv_x⟧ᴮ = some ⟨X, ⟨BType.int, hX⟩⟩) :
  ⟦(simplifier_aux_add (a -ᴮ b) y).abstract «Δ» (fun v hv => Or.casesOn (List.mem_append.mp (fv_simplifier_aux_add hv)) (fv_x v ·) (fv_y v ·))⟧ᴮ =
    some ⟨X +ᶻ Y, .int, overloadBinOp_mem hX hY⟩ := by
  simp_rw [Term.abstract, denote, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff, PSigma.exists] at den_x
  obtain ⟨A, τA, hA, den_a, den⟩ := den_x
  rcases typ_t
  rcases ‹Γ ⊢ _ -ᴮ _ : .int›
  obtain ⟨⟩ := denote_welltyped_eq
    ⟨Γ.abstract («Δ» := «Δ»),
    WFTC.of_abstract, .int,
    Typing.of_abstract (fun v hv => by apply fv_x; rw [fv, List.mem_append]; left; exact hv) ‹_›⟩
    den_a
  simp_rw [Option.bind_eq_some_iff, PSigma.exists] at den
  obtain ⟨B, τB, hB, den_b, den⟩ := den
  obtain ⟨⟩ := denote_welltyped_eq
    ⟨Γ.abstract («Δ» := «Δ»),
    WFTC.of_abstract, _,
    Typing.of_abstract (fun v hv => by apply fv_x; rw [fv, List.mem_append]; right; exact hv) ‹_›⟩
    den_b
  rw [Option.some_inj] at den
  injection den
  subst X

  cases y with
  | var v =>
    simp_rw [Term.abstract, denote, Option.pure_def, Option.some_get] at den_y
    simp_rw [simplifier_aux_add, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, den_a, Option.some_inj, exists_eq_left', den_b, Option.bind_some, Option.some_inj, exists_eq_left', den_y]
    rfl
  | int n =>
    simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at den_y
    injection den_y
    subst Y

    rcases eq_or_ne n 0 with rfl | n_ne_zero
    · simp_rw [simplifier_aux_add, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, den_a, Option.bind_some, den_b, Option.bind_some, Option.some_inj]
      symm
      congr 1
      · exact overloadBinOp_Int.add_zero hX
      · congr 1
        · funext τ
          rw [overloadBinOp_Int.add_zero hX]
        · apply proof_irrel_heq
    · have : simplifier_aux_add (a -ᴮ b) (.int n) = a -ᴮ b +ᴮ .int n := by
        unfold simplifier_aux_add
        split <;> injections
        · injections
          subst n
          contradiction
        · rfl
      simp_rw [this, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, den_a, Option.bind_some, den_b, Option.bind_some]
  | add x y
  | sub x y
  | mul x y =>
    simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_y
    obtain ⟨X, τX, hX, den_x, den_y⟩ := den_y
    rcases ‹Γ ⊢ _ : .int›
    obtain ⟨⟩ := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, .int,
      Typing.of_abstract (fun v hv => by apply fv_y; rw [fv, List.mem_append]; left; exact hv) ‹_›⟩
      den_x

    simp_rw [Option.bind_eq_some_iff, PSigma.exists] at den_y
    obtain ⟨Y, τY, hY, den_y, eq⟩ := den_y
    obtain ⟨⟩ := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, .int,
      Typing.of_abstract (fun v hv => by apply fv_y; rw [fv, List.mem_append]; right; exact hv) ‹_›⟩
      den_y
    simp_rw [Option.some_inj] at eq
    injection eq
    subst_eqs

    simp_rw [simplifier_aux_add, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, den_a, Option.bind_some, den_b, Option.bind_some, den_x, Option.bind_some, den_y, Option.bind_some]
  | app f x =>
    simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_y
    obtain ⟨F, τF, hF, den_f, den_y⟩ := den_y
    rcases ‹Γ ⊢ _ : .int›
    obtain ⟨⟩ := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, _,
      Typing.of_abstract (fun v hv => by apply fv_y; rw [fv, List.mem_append]; left; exact hv) ‹_›⟩
      den_f

    simp_rw [Option.bind_eq_some_iff, PSigma.exists] at den_y
    obtain ⟨X, τX, hX, den_x, eq⟩ := den_y
    obtain ⟨⟩ := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, _,
      Typing.of_abstract (fun v hv => by apply fv_y; rw [fv, List.mem_append]; right; exact hv) ‹_›⟩
      den_x

    split_ifs at eq with _ F_pfunc X_F_dom
    simp_rw [Option.some_inj] at eq
    injection eq
    subst Y

    simp_rw [simplifier_aux_add, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, den_a, Option.bind_some, den_b, Option.bind_some, den_x, Option.bind_some, den_f, Option.bind_some, dite_true, dite_cond_eq_true (eq_true F_pfunc), dite_cond_eq_true (eq_true X_F_dom), Option.bind_some]
  | card S =>
    simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_y
    obtain ⟨S, τS, hS, den_S, den_y⟩ := den_y
    rcases ‹Γ ⊢ _ : .int›
    obtain ⟨⟩ := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, .set _,
      Typing.of_abstract (fun v hv => by apply fv_y; rw [fv]; exact hv) ‹_›⟩
      den_S
    dsimp at den_y
    split_ifs at den_y with A_fin
    rw [Option.some_inj] at den_y
    injection den_y
    subst Y

    simp_rw [simplifier_aux_add, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, den_a, Option.bind_some, den_b, Option.bind_some, den_S, Option.bind_some, dite_cond_eq_true (eq_true A_fin), Option.bind_some, Option.some_inj]
    rfl
  | min S
  | max S =>
    simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_y
    obtain ⟨S, τS, hS, den_S, den_y⟩ := den_y
    rcases ‹Γ ⊢ _ : .int›
    obtain ⟨⟩ := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, .set _,
      Typing.of_abstract (fun v hv => by apply fv_y; rw [fv]; exact hv) ‹_›⟩
      den_S
    dsimp at den_y
    split_ifs at den_y with A_fin
    rw [Option.some_inj] at den_y
    injection den_y
    subst Y

    simp_rw [simplifier_aux_add, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, den_a, Option.bind_some, den_b, Option.bind_some, den_S, Option.bind_some, dite_cond_eq_true (eq_true A_fin), Option.bind_some]
  | bool | maplet | le | and | not | eq | «ℤ» | 𝔹 | mem | collect | pow | cprod | union | inter | lambda | pfun | all =>
    rcases ‹Γ ⊢ _ : .int›

set_option maxHeartbeats 250000 in
theorem simplifier_correct_aux_add.mul.{u_1} {«Δ» : 𝒱 → Option B.Dom} {Γ : B.TypeContext} (y : B.Term)
  (fv_y : ∀ v ∈ fv y, («Δ» v).isSome = true) {X : ZFSet.{u_1}} {hX : X ∈ BType.int.toZFSet} {Y : ZFSet.{u_1}}
  {hY : Y ∈ BType.int.toZFSet} (den_y : ⟦y.abstract «Δ» fv_y⟧ᴮ = some ⟨Y, ⟨BType.int, hY⟩⟩) (a b : B.Term)
  (fv_x : ∀ v ∈ fv (a *ᴮ b), («Δ» v).isSome = true) (wf_t : (a *ᴮ b +ᴮ y).WF) (typ_t : Γ ⊢ a *ᴮ b +ᴮ y : BType.int)
  (den_x : ⟦(a *ᴮ b).abstract «Δ» fv_x⟧ᴮ = some ⟨X, ⟨BType.int, hX⟩⟩) :
  ⟦(simplifier_aux_add (a *ᴮ b) y).abstract «Δ» (fun v hv => Or.casesOn (List.mem_append.mp (fv_simplifier_aux_add hv)) (fv_x v ·) (fv_y v ·))⟧ᴮ =
    some ⟨X +ᶻ Y, .int, overloadBinOp_mem hX hY⟩ := by
  simp_rw [Term.abstract, denote, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff, PSigma.exists] at den_x
  obtain ⟨A, τA, hA, den_a, den⟩ := den_x
  rcases typ_t
  rcases ‹Γ ⊢ _ *ᴮ _ : .int›
  obtain ⟨⟩ := denote_welltyped_eq
    ⟨Γ.abstract («Δ» := «Δ»),
    WFTC.of_abstract, .int,
    Typing.of_abstract (fun v hv => by apply fv_x; rw [fv, List.mem_append]; left; exact hv) ‹_›⟩
    den_a
  simp_rw [Option.bind_eq_some_iff, PSigma.exists] at den
  obtain ⟨B, τB, hB, den_b, den⟩ := den
  obtain ⟨⟩ := denote_welltyped_eq
    ⟨Γ.abstract («Δ» := «Δ»),
    WFTC.of_abstract, .int,
    Typing.of_abstract (fun v hv => by apply fv_x; rw [fv, List.mem_append]; right; exact hv) ‹_›⟩
    den_b
  rw [Option.some_inj] at den
  injection den
  subst X
  cases y with
  | var v =>
    simp_rw [Term.abstract, denote, Option.pure_def, Option.some_get] at den_y
    simp_rw [simplifier_aux_add, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, den_a, Option.some_inj, exists_eq_left', den_b, Option.bind_some, Option.some_inj, exists_eq_left', den_y]
    rfl
  | int n =>
    simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at den_y
    injection den_y
    subst Y

    rcases eq_or_ne n 0 with rfl | n_ne_zero
    · simp_rw [simplifier_aux_add, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, den_a, Option.bind_some, den_b, Option.bind_some, Option.some_inj]
      symm
      congr 1
      · exact overloadBinOp_Int.add_zero hX
      · congr 1
        · funext τ
          rw [overloadBinOp_Int.add_zero hX]
        · apply proof_irrel_heq
    · have : simplifier_aux_add (a *ᴮ b) (.int n) = a *ᴮ b +ᴮ .int n := by
        unfold simplifier_aux_add
        split <;> injections
        · injections
          subst n
          contradiction
        · rfl
      simp_rw [this, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, den_a, Option.bind_some, den_b, Option.bind_some]
  | add x y
  | sub x y
  | mul x y =>
    simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_y
    obtain ⟨X, τX, hX, den_x, den_y⟩ := den_y
    rcases ‹Γ ⊢ _ : .int›
    obtain ⟨⟩ := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, .int,
      Typing.of_abstract (fun v hv => by apply fv_y; rw [fv, List.mem_append]; left; exact hv) ‹_›⟩
      den_x

    simp_rw [Option.bind_eq_some_iff, PSigma.exists] at den_y
    obtain ⟨Y, τY, hY, den_y, eq⟩ := den_y
    obtain ⟨⟩ := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, .int,
      Typing.of_abstract (fun v hv => by apply fv_y; rw [fv, List.mem_append]; right; exact hv) ‹_›⟩
      den_y
    simp_rw [Option.some_inj] at eq
    injection eq
    subst_eqs

    simp_rw [simplifier_aux_add, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, den_a, Option.bind_some, den_b, Option.bind_some, den_x, Option.bind_some, den_y, Option.bind_some]
  | app f x =>
    simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_y
    obtain ⟨F, τF, hF, den_f, den_y⟩ := den_y
    rcases ‹Γ ⊢ _ : .int›
    obtain ⟨⟩ := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, _,
      Typing.of_abstract (fun v hv => by apply fv_y; rw [fv, List.mem_append]; left; exact hv) ‹_›⟩
      den_f

    simp_rw [Option.bind_eq_some_iff, PSigma.exists] at den_y
    obtain ⟨X, τX, hX, den_x, eq⟩ := den_y
    obtain ⟨⟩ := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, _,
      Typing.of_abstract (fun v hv => by apply fv_y; rw [fv, List.mem_append]; right; exact hv) ‹_›⟩
      den_x

    split_ifs at eq with _ F_pfunc X_F_dom
    simp_rw [Option.some_inj] at eq
    injection eq
    subst Y

    simp_rw [simplifier_aux_add, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, den_a, Option.bind_some, den_b, Option.bind_some, den_x, Option.bind_some, den_f, Option.bind_some, dite_true, dite_cond_eq_true (eq_true F_pfunc), dite_cond_eq_true (eq_true X_F_dom), Option.bind_some]
  | card S =>
    simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_y
    obtain ⟨S, τS, hS, den_S, eq⟩ := den_y
    rcases ‹Γ ⊢ _ : .int›
    obtain ⟨⟩ := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, .set _,
      Typing.of_abstract (fun v hv => by apply fv_y; rw [fv]; exact hv) ‹_›⟩
      den_S
    dsimp at eq
    split_ifs at eq with S_fin
    simp_rw [Option.some_inj] at eq
    injection eq
    subst Y
    simp_rw [simplifier_aux_add, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, den_a, Option.bind_some, den_b, Option.bind_some, den_S, Option.bind_some, dite_cond_eq_true (eq_true S_fin), Option.bind_some, Option.some_inj]
    rfl
  | min S
  | max S =>
    simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_y
    obtain ⟨S, τS, hS, den_S, eq⟩ := den_y
    rcases ‹Γ ⊢ _ : .int›
    obtain ⟨⟩ := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, .set _,
      Typing.of_abstract (fun v hv => by apply fv_y; rw [fv]; exact hv) ‹_›⟩
      den_S
    dsimp at eq
    split_ifs at eq with S_fin
    simp_rw [Option.some_inj] at eq
    injection eq
    subst Y

    simp_rw [simplifier_aux_add, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, den_a, Option.bind_some, den_b, Option.bind_some, den_S, Option.bind_some, dite_cond_eq_true (eq_true S_fin), Option.bind_some]
  | bool | maplet | le | and | not | eq | «ℤ» | 𝔹 | mem | collect | pow | cprod | union | inter | lambda | pfun | all =>
    rcases ‹Γ ⊢ _ : .int›

theorem simplifier_correct_aux_add.card.{u_1} {«Δ» : 𝒱 → Option B.Dom} {Γ : B.TypeContext} (y : B.Term)
  (fv_y : ∀ v ∈ fv y, («Δ» v).isSome = true) {X : ZFSet.{u_1}} {hX : X ∈ BType.int.toZFSet} {Y : ZFSet.{u_1}}
  {hY : Y ∈ BType.int.toZFSet} (den_y : ⟦y.abstract «Δ» fv_y⟧ᴮ = some ⟨Y, ⟨BType.int, hY⟩⟩) (S : B.Term)
  (fv_x : ∀ v ∈ fv (|S|ᴮ), («Δ» v).isSome = true) (wf_t : (|S|ᴮ +ᴮ y).WF) (typ_t : Γ ⊢ |S|ᴮ +ᴮ y : BType.int)
  (den_x : ⟦|S|ᴮ.abstract «Δ» fv_x⟧ᴮ = some ⟨X, ⟨BType.int, hX⟩⟩) :
  ⟦(simplifier_aux_add (|S|ᴮ) y).abstract «Δ» (fun v hv => Or.casesOn (List.mem_append.mp (fv_simplifier_aux_add hv)) (fv_x v ·) (fv_y v ·))⟧ᴮ =
    some ⟨X +ᶻ Y, .int, overloadBinOp_mem hX hY⟩ := by
  simp_rw [Term.abstract, denote, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff, PSigma.exists] at den_x
  obtain ⟨S', τS, hS, den_S, den⟩ := den_x
  rcases typ_t
  rcases ‹Γ ⊢ .card _ : .int›
  obtain ⟨⟩ := denote_welltyped_eq
    ⟨Γ.abstract («Δ» := «Δ»),
    WFTC.of_abstract, .set _,
    Typing.of_abstract (fun v hv => by apply fv_x; rw [fv]; exact hv) ‹_›⟩
    den_S
  dsimp at den
  split_ifs at den with S_fin
  rw [Option.some_inj] at den
  injection den
  subst X
  cases y with
  | var v =>
    unfold simplifier_aux_add
    simp_rw [Term.abstract, denote, Option.pure_def, Option.some_get] at den_y
    simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, den_S, Option.bind_some, dite_cond_eq_true (eq_true S_fin), Option.bind_some, den_y, Option.get_some]
    rfl
  | int n =>
    simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at den_y
    injection den_y
    subst Y

    rcases eq_or_ne n 0 with rfl | n_ne_zero
    · simp_rw [simplifier_aux_add, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, den_S, Option.bind_some, dite_cond_eq_true (eq_true S_fin), Option.some_inj]
      symm
      congr 1
      · exact overloadBinOp_Int.add_zero hX
      · congr 1
        · funext τ
          rw [overloadBinOp_Int.add_zero hX]
          rfl
        · apply proof_irrel_heq
    · have : simplifier_aux_add (|S|ᴮ) (.int n) = |S|ᴮ +ᴮ .int n := by
        unfold simplifier_aux_add
        split <;> injections
        · injections
          subst n
          contradiction
        · rfl
      simp_rw [this, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, den_S, Option.bind_some, dite_cond_eq_true (eq_true S_fin), Option.bind_some]
      rfl
  | add x y
  | sub x y
  | mul x y =>
    simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_y
    obtain ⟨X, τX, hX, den_x, den_y⟩ := den_y
    rcases ‹Γ ⊢ _ : .int›
    obtain ⟨⟩ := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, .int,
      Typing.of_abstract (fun v hv => by apply fv_y; rw [fv, List.mem_append]; left; exact hv) ‹_›⟩
      den_x
    simp_rw [Option.bind_eq_some_iff, PSigma.exists] at den_y
    obtain ⟨Y, τY, hY, den_y, eq⟩ := den_y
    obtain ⟨⟩ := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, .int,
      Typing.of_abstract (fun v hv => by apply fv_y; rw [fv, List.mem_append]; right; exact hv) ‹_›⟩
      den_y
    simp_rw [Option.some_inj] at eq
    injection eq
    subst_eqs
    simp_rw [simplifier_aux_add, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, den_S, Option.bind_some, dite_cond_eq_true (eq_true S_fin), den_x, Option.bind_some, den_y, Option.bind_some]
    rfl
  | app f x =>
    simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_y
    obtain ⟨F, τF, hF, den_f, den_y⟩ := den_y
    rcases ‹Γ ⊢ _ : .int›
    obtain ⟨⟩ := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, _,
      Typing.of_abstract (fun v hv => by apply fv_y; rw [fv, List.mem_append]; left; exact hv) ‹_›⟩
      den_f

    simp_rw [Option.bind_eq_some_iff, PSigma.exists] at den_y
    obtain ⟨X, τX, hX, den_x, eq⟩ := den_y
    obtain ⟨⟩ := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, _,
      Typing.of_abstract (fun v hv => by apply fv_y; rw [fv, List.mem_append]; right; exact hv) ‹_›⟩
      den_x

    split_ifs at eq with _ F_pfunc X_F_dom
    simp_rw [Option.some_inj] at eq
    injection eq
    subst Y

    simp_rw [simplifier_aux_add, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, den_S, Option.bind_some, dite_cond_eq_true (eq_true S_fin), Option.bind_some, den_f, Option.bind_some, dite_cond_eq_true (eq_true F_pfunc), den_x, Option.bind_some, dite_true, dite_cond_eq_true (eq_true X_F_dom), Option.bind_some]
    rfl
  | card T =>
    simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_y
    obtain ⟨T', τT, hT, den_T, eq⟩ := den_y
    rcases ‹Γ ⊢ _ : .int›
    obtain ⟨⟩ := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, .set _,
      Typing.of_abstract (fun v hv => by apply fv_y; rw [fv]; exact hv) ‹_›⟩
      den_T
    dsimp at eq
    split_ifs at eq with T_fin
    simp_rw [Option.some_inj] at eq
    injection eq
    subst Y

    simp_rw [simplifier_aux_add, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, den_S, Option.bind_some, dite_cond_eq_true (eq_true S_fin), Option.bind_some, den_T, Option.bind_some, dite_cond_eq_true (eq_true T_fin), Option.bind_some]
    rfl
  | min T
  | max T =>
    simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_y
    obtain ⟨T', τT, hT, den_T, eq⟩ := den_y
    rcases ‹Γ ⊢ _ : .int›
    obtain ⟨⟩ := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, .set _,
      Typing.of_abstract (fun v hv => by apply fv_y; rw [fv]; exact hv) ‹_›⟩
      den_T
    dsimp at eq
    split_ifs at eq with T_fin
    simp_rw [Option.some_inj] at eq
    injection eq
    subst Y

    simp_rw [simplifier_aux_add, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, den_S, Option.bind_some, dite_cond_eq_true (eq_true S_fin), Option.bind_some, den_T, Option.bind_some, dite_cond_eq_true (eq_true T_fin), Option.bind_some]
    rfl
  | bool | maplet | le | and | not | eq | «ℤ» | 𝔹 | mem | collect | pow | cprod | union | inter | lambda | pfun | all =>
    rcases ‹Γ ⊢ _ : .int›

set_option maxHeartbeats 600000 in
theorem simplifier_correct_aux_add.app.{u_1} {«Δ» : 𝒱 → Option B.Dom} {Γ : B.TypeContext} (y : B.Term)
  (fv_y : ∀ v ∈ fv y, («Δ» v).isSome = true) {X : ZFSet.{u_1}} {hX : X ∈ BType.int.toZFSet} {Y : ZFSet.{u_1}}
  {hY : Y ∈ BType.int.toZFSet} (den_y : ⟦y.abstract «Δ» fv_y⟧ᴮ = some ⟨Y, ⟨BType.int, hY⟩⟩) (f x : B.Term)
  (fv_x : ∀ v ∈ fv ((@ᴮf) x), («Δ» v).isSome = true) (wf_t : ((@ᴮf) x +ᴮ y).WF) (typ_t : Γ ⊢ (@ᴮf) x +ᴮ y : BType.int)
  (den_x : ⟦((@ᴮf) x).abstract «Δ» fv_x⟧ᴮ = some ⟨X, ⟨BType.int, hX⟩⟩) :
  ⟦(simplifier_aux_add ((@ᴮf) x) y).abstract «Δ» (fun v hv => Or.casesOn (List.mem_append.mp (fv_simplifier_aux_add hv)) (fv_x v ·) (fv_y v ·))⟧ᴮ =
    some ⟨X +ᶻ Y, .int, overloadBinOp_mem hX hY⟩ := by
  simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_x
  obtain ⟨F, τF, hF, den_f, den_x⟩ := den_x
  rcases typ_t
  rcases ‹Γ ⊢ .app _ _ : .int›
  obtain ⟨⟩ := denote_welltyped_eq
    ⟨Γ.abstract («Δ» := «Δ»),
    WFTC.of_abstract, (_ ×ᴮ .int).set,
    Typing.of_abstract (fun v hv => by apply fv_x; rw [fv, List.mem_append]; left; exact hv) ‹_›⟩
    den_f
  simp_rw [Option.bind_eq_some_iff, PSigma.exists] at den_x
  obtain ⟨X', τX, hX', den_x, eq⟩ := den_x
  obtain ⟨⟩ := denote_welltyped_eq
    ⟨Γ.abstract («Δ» := «Δ»),
    WFTC.of_abstract, _,
    Typing.of_abstract (fun v hv => by apply fv_x; rw [fv, List.mem_append]; right; exact hv) ‹_›⟩
    den_x
  split_ifs at eq with _ F_pfunc X_F_dom
  simp_rw [Option.some_inj] at eq
  injection eq
  subst X
  cases y with
  | var v =>
    simp_rw [Term.abstract, denote, Option.pure_def, Option.some_get] at den_y
    simp_rw [simplifier_aux_add, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, den_f, Option.bind_some, den_x, Option.bind_some, den_y, dite_true, dite_cond_eq_true (eq_true F_pfunc), dite_cond_eq_true (eq_true X_F_dom), Option.bind_some, Option.get_some]
  | int n =>
    simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at den_y
    injection den_y
    subst Y
    rcases eq_or_ne n 0 with rfl | n_ne_zero
    · simp_rw [simplifier_aux_add, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, den_f, Option.bind_some, den_x, Option.bind_some, dite_true,  dite_cond_eq_true (eq_true F_pfunc), dite_cond_eq_true (eq_true X_F_dom), Option.some_inj]
      symm
      congr 1
      · exact overloadBinOp_Int.add_zero hX
      · congr 1
        · funext τ
          rw [overloadBinOp_Int.add_zero hX]
        · apply proof_irrel_heq
    · have : simplifier_aux_add ((@ᴮf) x) (.int n) = (@ᴮf) x +ᴮ .int n := by
        unfold simplifier_aux_add
        split <;> injections
        · injections
          subst n
          contradiction
        · rfl
      simp_rw [this, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, den_f, Option.bind_some, den_x, Option.bind_some, dite_true, dite_cond_eq_true (eq_true F_pfunc), dite_cond_eq_true (eq_true X_F_dom), Option.bind_some]
  | add a b
  | sub a b
  | mul a b =>
    simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_y
    obtain ⟨A, τA, hA, den_a, den_y⟩ := den_y
    rcases ‹Γ ⊢ _ : .int›
    obtain ⟨⟩ := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, .int,
      Typing.of_abstract (fun v hv => by apply fv_y; rw [fv, List.mem_append]; left; exact hv) ‹_›⟩
      den_a
    simp_rw [Option.bind_eq_some_iff, PSigma.exists] at den_y
    obtain ⟨B, τB, hB, den_b, eq'⟩ := den_y
    obtain ⟨⟩ := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, .int,
      Typing.of_abstract (fun v hv => by apply fv_y; rw [fv, List.mem_append]; right; exact hv) ‹_›⟩
      den_b
    simp_rw [Option.some_inj] at eq'
    injection eq'
    subst Y
    simp_rw [simplifier_aux_add, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, den_f, Option.bind_some, den_x, Option.bind_some, dite_true, dite_cond_eq_true (eq_true F_pfunc), dite_cond_eq_true (eq_true X_F_dom), den_a, Option.bind_some, den_b, Option.bind_some]
  | app f' x' =>
    simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_y
    obtain ⟨F', τF', hF', den_f', den_y⟩ := den_y
    rcases ‹Γ ⊢ _ : .int›
    obtain ⟨⟩ := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, (_ ×ᴮ .int).set,
      Typing.of_abstract (fun v hv => by apply fv_y; rw [fv, List.mem_append]; left; exact hv) ‹_›⟩
      den_f'
    simp_rw [Option.bind_eq_some_iff, PSigma.exists] at den_y
    obtain ⟨X', τX', hX', den_x', eq'⟩ := den_y
    obtain ⟨⟩ := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, _,
      Typing.of_abstract (fun v hv => by apply fv_y; rw [fv, List.mem_append]; right; exact hv) ‹_›⟩
      den_x'
    split_ifs at eq' with _ F'_pfunc X'_F'_dom
    simp_rw [Option.some_inj] at eq'
    injection eq'
    subst Y
    simp_rw [simplifier_aux_add, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, den_f, Option.bind_some, den_x, Option.bind_some, dite_true, dite_cond_eq_true (eq_true F_pfunc), dite_cond_eq_true (eq_true X_F_dom), den_f', Option.bind_some, den_x', Option.bind_some, dite_true, dite_cond_eq_true (eq_true F'_pfunc), dite_cond_eq_true (eq_true X'_F'_dom), Option.bind_some]
  | card S =>
    simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_y
    obtain ⟨A, τA, hA, den_a, eq'⟩ := den_y
    rcases ‹Γ ⊢ _ : .int›
    obtain ⟨⟩ := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, .set _,
      Typing.of_abstract (fun v hv => by apply fv_y; rw [fv]; exact hv) ‹_›⟩
      den_a
    dsimp at eq'
    split_ifs at eq' with A_fin
    simp_rw [Option.some_inj] at eq'
    injection eq'
    subst Y
    simp_rw [simplifier_aux_add, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, den_f, Option.bind_some, den_x, Option.bind_some, dite_true, dite_cond_eq_true (eq_true F_pfunc), dite_cond_eq_true (eq_true X_F_dom), Option.bind_some, den_a, Option.bind_some, dite_cond_eq_true (eq_true A_fin), Option.bind_some]
    rfl
  | min S
  | max S =>
    simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_y
    obtain ⟨A, τA, hA, den_a, eq'⟩ := den_y
    rcases ‹Γ ⊢ _ : .int›
    obtain ⟨⟩ := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, .set _,
      Typing.of_abstract (fun v hv => by apply fv_y; rw [fv]; exact hv) ‹_›⟩
      den_a
    dsimp at eq'
    split_ifs at eq' with A_fin
    simp_rw [Option.some_inj] at eq'
    injection eq'
    subst Y
    simp_rw [simplifier_aux_add, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, den_f, Option.bind_some, den_x, Option.bind_some, dite_true, dite_cond_eq_true (eq_true F_pfunc), dite_cond_eq_true (eq_true X_F_dom), Option.bind_some, den_a, Option.bind_some, dite_cond_eq_true (eq_true A_fin), Option.bind_some]
  | bool | maplet | le | and | not | eq | «ℤ» | 𝔹 | mem | collect | pow | cprod | union | inter | lambda | pfun | all =>
    rcases ‹Γ ⊢ _ : .int›

theorem simplifier_correct_aux_add.min.{u_1} {«Δ» : 𝒱 → Option B.Dom} {Γ : B.TypeContext} (y : B.Term)
  (fv_y : ∀ v ∈ fv y, («Δ» v).isSome = true) {X : ZFSet.{u_1}} {hX : X ∈ BType.int.toZFSet} {Y : ZFSet.{u_1}}
  {hY : Y ∈ BType.int.toZFSet} (den_y : ⟦y.abstract «Δ» fv_y⟧ᴮ = some ⟨Y, ⟨BType.int, hY⟩⟩) (S : B.Term)
  (fv_x : ∀ v ∈ fv S.min, («Δ» v).isSome = true) (wf_t : (S.min +ᴮ y).WF) (typ_t : Γ ⊢ S.min +ᴮ y : BType.int)
  (den_x : ⟦S.min.abstract «Δ» fv_x⟧ᴮ = some ⟨X, ⟨BType.int, hX⟩⟩) :
  ⟦(simplifier_aux_add S.min y).abstract «Δ» (fun v hv => Or.casesOn (List.mem_append.mp (fv_simplifier_aux_add hv)) (fv_x v ·) (fv_y v ·))⟧ᴮ =
    some ⟨X +ᶻ Y, .int, overloadBinOp_mem hX hY⟩ := by
  simp_rw [Term.abstract, denote, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff, PSigma.exists] at den_x
  obtain ⟨S', τS, hS, den_S, den⟩ := den_x
  rcases typ_t
  rcases ‹Γ ⊢ .min _ : .int›
  obtain ⟨⟩ := denote_welltyped_eq
    ⟨Γ.abstract («Δ» := «Δ»),
    WFTC.of_abstract, .set _,
    Typing.of_abstract (fun v hv => by apply fv_x; rw [fv]; exact hv) ‹_›⟩
    den_S
  dsimp at den
  split_ifs at den with S_fin
  rw [Option.some_inj] at den
  injection den
  subst X
  cases y with
  | var v =>
    unfold simplifier_aux_add
    simp_rw [Term.abstract, denote, Option.pure_def, Option.some_get] at den_y
    simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, den_S, Option.bind_some, dite_cond_eq_true (eq_true S_fin), Option.bind_some, den_y, Option.get_some]
  | int n =>
    simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at den_y
    injection den_y
    subst Y

    rcases eq_or_ne n 0 with rfl | n_ne_zero
    · simp_rw [simplifier_aux_add, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, den_S, Option.bind_some, dite_cond_eq_true (eq_true S_fin), Option.some_inj]
      symm
      congr 1
      · exact overloadBinOp_Int.add_zero hX
      · congr 1
        · funext τ
          rw [overloadBinOp_Int.add_zero hX]
        · apply proof_irrel_heq
    · have : simplifier_aux_add (S.min) (.int n) = S.min +ᴮ .int n := by
        unfold simplifier_aux_add
        split <;> injections
        · injections
          subst n
          contradiction
        · rfl
      simp_rw [this, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, den_S, Option.bind_some, dite_cond_eq_true (eq_true S_fin), Option.bind_some]
  | add x y
  | sub x y
  | mul x y =>
    simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_y
    obtain ⟨X, τX, hX, den_x, den_y⟩ := den_y
    rcases ‹Γ ⊢ _ : .int›
    obtain ⟨⟩ := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, .int,
      Typing.of_abstract (fun v hv => by apply fv_y; rw [fv, List.mem_append]; left; exact hv) ‹_›⟩
      den_x
    simp_rw [Option.bind_eq_some_iff, PSigma.exists] at den_y
    obtain ⟨Y, τY, hY, den_y, eq⟩ := den_y
    obtain ⟨⟩ := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, .int,
      Typing.of_abstract (fun v hv => by apply fv_y; rw [fv, List.mem_append]; right; exact hv) ‹_›⟩
      den_y
    simp_rw [Option.some_inj] at eq
    injection eq
    subst_eqs
    simp_rw [simplifier_aux_add, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, den_S, Option.bind_some, dite_cond_eq_true (eq_true S_fin), den_x, Option.bind_some, den_y, Option.bind_some]
  | app f x =>
    simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_y
    obtain ⟨F, τF, hF, den_f, den_y⟩ := den_y
    rcases ‹Γ ⊢ _ : .int›
    obtain ⟨⟩ := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, _,
      Typing.of_abstract (fun v hv => by apply fv_y; rw [fv, List.mem_append]; left; exact hv) ‹_›⟩
      den_f

    simp_rw [Option.bind_eq_some_iff, PSigma.exists] at den_y
    obtain ⟨X, τX, hX, den_x, eq⟩ := den_y
    obtain ⟨⟩ := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, _,
      Typing.of_abstract (fun v hv => by apply fv_y; rw [fv, List.mem_append]; right; exact hv) ‹_›⟩
      den_x

    split_ifs at eq with _ F_pfunc X_F_dom
    simp_rw [Option.some_inj] at eq
    injection eq
    subst Y

    simp_rw [simplifier_aux_add, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, den_S, Option.bind_some, dite_cond_eq_true (eq_true S_fin), Option.bind_some, den_f, Option.bind_some, dite_cond_eq_true (eq_true F_pfunc), den_x, Option.bind_some, dite_true, dite_cond_eq_true (eq_true X_F_dom), Option.bind_some]
  | card T =>
    simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_y
    obtain ⟨T', τT, hT, den_T, eq⟩ := den_y
    rcases ‹Γ ⊢ _ : .int›
    obtain ⟨⟩ := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, .set _,
      Typing.of_abstract (fun v hv => by apply fv_y; rw [fv]; exact hv) ‹_›⟩
      den_T
    dsimp at eq
    split_ifs at eq with T_fin
    simp_rw [Option.some_inj] at eq
    injection eq
    subst Y

    simp_rw [simplifier_aux_add, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, den_S, Option.bind_some, dite_cond_eq_true (eq_true S_fin), Option.bind_some, den_T, Option.bind_some, dite_cond_eq_true (eq_true T_fin), Option.bind_some]
    rfl
  | min T
  | max T =>
    simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_y
    obtain ⟨T', τT, hT, den_T, eq⟩ := den_y
    rcases ‹Γ ⊢ _ : .int›
    obtain ⟨⟩ := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, .set _,
      Typing.of_abstract (fun v hv => by apply fv_y; rw [fv]; exact hv) ‹_›⟩
      den_T
    dsimp at eq
    split_ifs at eq with T_fin
    simp_rw [Option.some_inj] at eq
    injection eq
    subst Y

    simp_rw [simplifier_aux_add, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, den_S, Option.bind_some, dite_cond_eq_true (eq_true S_fin), Option.bind_some, den_T, Option.bind_some, dite_cond_eq_true (eq_true T_fin), Option.bind_some]
  | bool | maplet | le | and | not | eq | «ℤ» | 𝔹 | mem | collect | pow | cprod | union | inter | lambda | pfun | all =>
    rcases ‹Γ ⊢ _ : .int›

theorem simplifier_correct_aux_add.max.{u_1} {«Δ» : 𝒱 → Option B.Dom} {Γ : B.TypeContext} (y : B.Term)
  (fv_y : ∀ v ∈ fv y, («Δ» v).isSome = true) {X : ZFSet.{u_1}} {hX : X ∈ BType.int.toZFSet} {Y : ZFSet.{u_1}}
  {hY : Y ∈ BType.int.toZFSet} (den_y : ⟦y.abstract «Δ» fv_y⟧ᴮ = some ⟨Y, ⟨BType.int, hY⟩⟩) (S : B.Term)
  (fv_x : ∀ v ∈ fv S.max, («Δ» v).isSome = true) (wf_t : (S.max +ᴮ y).WF) (typ_t : Γ ⊢ S.max +ᴮ y : BType.int)
  (den_x : ⟦S.max.abstract «Δ» fv_x⟧ᴮ = some ⟨X, ⟨BType.int, hX⟩⟩) :
  ⟦(simplifier_aux_add S.max y).abstract «Δ» (fun v hv => Or.casesOn (List.mem_append.mp (fv_simplifier_aux_add hv)) (fv_x v ·) (fv_y v ·))⟧ᴮ =
    some ⟨X +ᶻ Y, .int, overloadBinOp_mem hX hY⟩ := by
  simp_rw [Term.abstract, denote, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff, PSigma.exists] at den_x
  obtain ⟨S', τS, hS, den_S, den⟩ := den_x
  rcases typ_t
  rcases ‹Γ ⊢ .max _ : .int›
  obtain ⟨⟩ := denote_welltyped_eq
    ⟨Γ.abstract («Δ» := «Δ»),
    WFTC.of_abstract, .set _,
    Typing.of_abstract (fun v hv => by apply fv_x; rw [fv]; exact hv) ‹_›⟩
    den_S
  dsimp at den
  split_ifs at den with S_fin
  rw [Option.some_inj] at den
  injection den
  subst X
  cases y with
  | var v =>
    unfold simplifier_aux_add
    simp_rw [Term.abstract, denote, Option.pure_def, Option.some_get] at den_y
    simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, den_S, Option.bind_some, dite_cond_eq_true (eq_true S_fin), Option.bind_some, den_y, Option.get_some]
  | int n =>
    simp_rw [Term.abstract, denote, Option.pure_def, Option.some_inj] at den_y
    injection den_y
    subst Y

    rcases eq_or_ne n 0 with rfl | n_ne_zero
    · simp_rw [simplifier_aux_add, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, den_S, Option.bind_some, dite_cond_eq_true (eq_true S_fin), Option.some_inj]
      symm
      congr 1
      · exact overloadBinOp_Int.add_zero hX
      · congr 1
        · funext τ
          rw [overloadBinOp_Int.add_zero hX]
        · apply proof_irrel_heq
    · have : simplifier_aux_add (S.max) (.int n) = S.max +ᴮ .int n := by
        unfold simplifier_aux_add
        split <;> injections
        · injections
          subst n
          contradiction
        · rfl
      simp_rw [this, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, den_S, Option.bind_some, dite_cond_eq_true (eq_true S_fin), Option.bind_some]
  | add x y
  | sub x y
  | mul x y =>
    simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_y
    obtain ⟨X, τX, hX, den_x, den_y⟩ := den_y
    rcases ‹Γ ⊢ _ : .int›
    obtain ⟨⟩ := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, .int,
      Typing.of_abstract (fun v hv => by apply fv_y; rw [fv, List.mem_append]; left; exact hv) ‹_›⟩
      den_x
    simp_rw [Option.bind_eq_some_iff, PSigma.exists] at den_y
    obtain ⟨Y, τY, hY, den_y, eq⟩ := den_y
    obtain ⟨⟩ := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, .int,
      Typing.of_abstract (fun v hv => by apply fv_y; rw [fv, List.mem_append]; right; exact hv) ‹_›⟩
      den_y
    simp_rw [Option.some_inj] at eq
    injection eq
    subst_eqs
    simp_rw [simplifier_aux_add, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, den_S, Option.bind_some, dite_cond_eq_true (eq_true S_fin), den_x, Option.bind_some, den_y, Option.bind_some]
  | app f x =>
    simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_y
    obtain ⟨F, τF, hF, den_f, den_y⟩ := den_y
    rcases ‹Γ ⊢ _ : .int›
    obtain ⟨⟩ := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, _,
      Typing.of_abstract (fun v hv => by apply fv_y; rw [fv, List.mem_append]; left; exact hv) ‹_›⟩
      den_f

    simp_rw [Option.bind_eq_some_iff, PSigma.exists] at den_y
    obtain ⟨X, τX, hX, den_x, eq⟩ := den_y
    obtain ⟨⟩ := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, _,
      Typing.of_abstract (fun v hv => by apply fv_y; rw [fv, List.mem_append]; right; exact hv) ‹_›⟩
      den_x

    split_ifs at eq with _ F_pfunc X_F_dom
    simp_rw [Option.some_inj] at eq
    injection eq
    subst Y

    simp_rw [simplifier_aux_add, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, den_S, Option.bind_some, dite_cond_eq_true (eq_true S_fin), Option.bind_some, den_f, Option.bind_some, dite_cond_eq_true (eq_true F_pfunc), den_x, Option.bind_some, dite_true, dite_cond_eq_true (eq_true X_F_dom), Option.bind_some]
  | card T =>
    simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_y
    obtain ⟨T', τT, hT, den_T, eq⟩ := den_y
    rcases ‹Γ ⊢ _ : .int›
    obtain ⟨⟩ := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, .set _,
      Typing.of_abstract (fun v hv => by apply fv_y; rw [fv]; exact hv) ‹_›⟩
      den_T
    dsimp at eq
    split_ifs at eq with T_fin
    simp_rw [Option.some_inj] at eq
    injection eq
    subst Y

    simp_rw [simplifier_aux_add, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, den_S, Option.bind_some, dite_cond_eq_true (eq_true S_fin), Option.bind_some, den_T, Option.bind_some, dite_cond_eq_true (eq_true T_fin), Option.bind_some]
    rfl
  | min T
  | max T =>
    simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_y
    obtain ⟨T', τT, hT, den_T, eq⟩ := den_y
    rcases ‹Γ ⊢ _ : .int›
    obtain ⟨⟩ := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, .set _,
      Typing.of_abstract (fun v hv => by apply fv_y; rw [fv]; exact hv) ‹_›⟩
      den_T
    dsimp at eq
    split_ifs at eq with T_fin
    simp_rw [Option.some_inj] at eq
    injection eq
    subst Y

    simp_rw [simplifier_aux_add, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, den_S, Option.bind_some, dite_cond_eq_true (eq_true S_fin), Option.bind_some, den_T, Option.bind_some, dite_cond_eq_true (eq_true T_fin), Option.bind_some]
  | bool | maplet | le | and | not | eq | «ℤ» | 𝔹 | mem | collect | pow | cprod | union | inter | lambda | pfun | all =>
    rcases ‹Γ ⊢ _ : .int›

end simplifier_aux_add

theorem simplifier_partial_correct_aux_add {«Δ» : 𝒱 → Option B.Dom} {Γ : B.TypeContext} (x y : B.Term)
  (fv_x : ∀ v ∈ fv x, («Δ» v).isSome = true)
  (fv_y : ∀ v ∈ fv y, («Δ» v).isSome = true)
  (wf_t : (x +ᴮ y).WF) (typ_t : Γ ⊢ x +ᴮ y : .int)
  {X hX Y hY}
  (den_x : ⟦x.abstract «Δ» fv_x⟧ᴮ = some ⟨X, .int, hX⟩)
  (den_y : ⟦y.abstract «Δ» fv_y⟧ᴮ = some ⟨Y, .int, hY⟩) :
  ⟦(simplifier_aux_add x y).abstract «Δ» (fun v hv => Or.casesOn (List.mem_append.mp (fv_simplifier_aux_add hv)) (fv_x v ·) (fv_y v ·))⟧ᴮ = some ⟨X +ᶻ Y, .int, overloadBinOp_mem hX hY⟩ := by
  cases x with
  | bool | maplet | le | and | not | eq | «ℤ» | 𝔹 | mem | collect | pow | cprod | union | inter | lambda | pfun | all =>
    rcases typ_t
    rename Γ ⊢ _ : .int => h
    clear ‹Γ ⊢ _ : .int›
    rcases ‹Γ ⊢ _ : .int›
  | var v =>   exact simplifier_correct_aux_add.var y fv_y den_y v fv_x wf_t typ_t den_x
  | int n =>   exact simplifier_correct_aux_add.int y fv_y den_y n fv_x wf_t typ_t den_x
  | add a b => exact simplifier_correct_aux_add.add y fv_y den_y a b fv_x wf_t typ_t den_x
  | sub a b => exact simplifier_correct_aux_add.sub y fv_y den_y a b fv_x wf_t typ_t den_x
  | mul a b => exact simplifier_correct_aux_add.mul y fv_y den_y a b fv_x wf_t typ_t den_x
  | card S =>  exact simplifier_correct_aux_add.card y fv_y den_y S fv_x wf_t typ_t den_x
  | app f x => exact simplifier_correct_aux_add.app y fv_y den_y f x fv_x wf_t typ_t den_x
  | min S =>   exact simplifier_correct_aux_add.min y fv_y den_y S fv_x wf_t typ_t den_x
  | max S =>   exact simplifier_correct_aux_add.max y fv_y den_y S fv_x wf_t typ_t den_x

theorem simplifier_partial_correct_aux_add' {«Δ» : 𝒱 → Option B.Dom} {Γ : B.TypeContext} (x y : B.Term)
  (ht : ∀ v ∈ fv (x +ᴮ y), («Δ» v).isSome = true)
  (wf_t : (x +ᴮ y).WF) {τ : BType} (typ_t : Γ ⊢ x +ᴮ y : τ)
  {X hX Y hY}
  (den_x : ⟦(simplifier x).abstract «Δ» (by
    intro v hv
    apply ht
    rw [fv, List.mem_append]
    exact Or.inl <| fv_simplifier wf_t.1 hv)⟧ᴮ = some ⟨X, .int, hX⟩)
  (den_y : ⟦(simplifier y).abstract «Δ» (by
    intro v hv
    apply ht
    rw [fv, List.mem_append]
    exact Or.inr <| fv_simplifier wf_t.2 hv)⟧ᴮ = some ⟨Y, .int, hY⟩) :
  ⟦(simplifier (x +ᴮ y)).abstract «Δ» (ht · <| fv_simplifier wf_t ·)⟧ᴮ = some ⟨X +ᶻ Y, .int, overloadBinOp_mem hX hY⟩ := by
  unfold simplifier
  apply simplifier_partial_correct_aux_add (Γ := Γ)
  · exact ⟨Term.WF.simplifier wf_t.1, Term.WF.simplifier wf_t.2⟩
  · obtain ⟨-, typ_x, typ_y⟩ := B.Typing.addE typ_t
    apply B.Typing.add
    · exact Typing.simplifier typ_x
    · exact Typing.simplifier typ_y
  · exact den_x
  · exact den_y

theorem simplifier_correct_aux_add {«Δ» : 𝒱 → Option B.Dom} {Γ : B.TypeContext} (x y : B.Term)
  (h : ∀ v ∈ fv (simplifier_aux_add x y), («Δ» v).isSome = true)
  (h' : ∀ v ∈ fv (x +ᴮ y), («Δ» v).isSome = true)
  (wf_t : (x +ᴮ y).WF) {τ : BType} (typ_t : Γ ⊢ x +ᴮ y : τ) :
  ⟦(simplifier_aux_add x y).abstract «Δ» h⟧ᴮ = ⟦(x +ᴮ y).abstract «Δ» h'⟧ᴮ := by
  obtain ⟨rfl, hx, hy⟩ := Typing.addE typ_t
  simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind]
  cases den_x : ⟦x.abstract «Δ» (fun v hv => h' v (by rw [fv, List.mem_append]; left; exact hv))⟧ᴮ with
  | none =>
    simp only [Option.bind_none]
    unfold simplifier_aux_add
    split <;> try (rw [Term.abstract, denote] at den_x; contradiction)
    · exact den_x
    · simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.bind_eq_none_iff] at den_x
      simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_none_iff]
      intro ⟨X, τ, hX⟩ den_x'
      specialize den_x _ den_x'
      simp only [Option.bind_some]
      split
      · repeat
          injections
          subst_vars
        contradiction
      · rfl
    · simp_rw [Term.abstract, denote, den_x, Option.pure_def, Option.bind_eq_bind, Option.bind_none]
  | some X =>
    obtain ⟨X, τ, hX⟩ := X
    obtain ⟨⟩ := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, .int,
      Typing.of_abstract (fun v hv => h' v (by rw [fv, List.mem_append]; left; exact hv)) hx⟩
      den_x
    dsimp
    cases den_y : ⟦y.abstract «Δ» (fun v hv => h' v (by rw [fv, List.mem_append]; right; exact hv))⟧ᴮ with
    | none =>
      simp only [Option.bind_none]
      unfold simplifier_aux_add
      split <;> try (rw [Term.abstract, denote] at den_y; contradiction)
      · exact den_y
      · simp_rw [Term.abstract, denote, den_x, Option.pure_def, Option.bind_eq_bind, Option.bind_some, den_y, Option.bind_none]
    | some Y =>
      obtain ⟨Y, τ, hY⟩ := Y
      obtain ⟨⟩ := denote_welltyped_eq
        ⟨Γ.abstract («Δ» := «Δ»),
        WFTC.of_abstract, .int,
        Typing.of_abstract (fun v hv => h' v (by rw [fv, List.mem_append]; right; exact hv)) hy⟩
        den_y
      dsimp
      apply simplifier_partial_correct_aux_add x y _ _ wf_t typ_t den_x den_y
