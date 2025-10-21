import B.Simplifier
import B.SemanticsPHOAS
import B.Reasoning.Lemmas

open Classical B PHOAS ZFSet

theorem isSome_fv_simplifier_of_fv_isSome {t : Term} {«Δ» : 𝒱 → Option Dom}
  (wf_t : t.WF)
  (ht : ∀ v ∈ fv t, («Δ» v).isSome = true) :
  ∀ v ∈ fv (simplifier t), («Δ» v).isSome = true := by
  intro v hv
  apply ht
  exact fv_simplifier wf_t hv

theorem simplifier_partial_correct' {t : Term} {«Δ»}
  (ht : ∀ v ∈ fv t, («Δ» v).isSome = true)
  (wf_t : t.WF) {Γ : B.TypeContext} {τ : BType} (typ_t : Γ ⊢ t : τ)
  (h : ⟦(simplifier t).abstract («Δ» := «Δ») (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ = none) :
  ⟦t.abstract «Δ» ht⟧ᴮ = none := by
  induction t generalizing «Δ» Γ τ with
  | «ℤ»
  | 𝔹
  | int
  | bool
  | var v => exact h
  | maplet x y x_ih y_ih =>
    unfold simplifier at h
    obtain ⟨_, _, rfl, typx, typy⟩ := Typing.mapletE typ_t
    simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_none_iff] at h ⊢
    intro X den_x Y den_y
    specialize x_ih (fun v hv => ht v (by rw [fv, List.mem_append]; left; exact hv)) wf_t.1 typx
    specialize y_ih (fun v hv => ht v (by rw [fv, List.mem_append]; right; exact hv)) wf_t.2 typy
    rw [←Decidable.not_imp_not, ←ne_eq, Option.ne_none_iff_exists, ←ne_eq, Option.ne_none_iff_exists] at x_ih y_ih
    obtain ⟨simpX, den_simpx⟩ := x_ih ⟨X, den_x.symm⟩
    obtain ⟨simpY, den_simpy⟩ := y_ih ⟨Y, den_y.symm⟩
    nomatch h simpX den_simpx.symm simpY den_simpy.symm
  | sub x y x_ih y_ih =>
    unfold simplifier at h
    obtain ⟨rfl, typx, typy⟩ := Typing.subE typ_t
    simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_none_iff] at h ⊢
    intro ⟨X, _, hX⟩ den_x

    obtain rfl := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, .int,
      Typing.of_abstract (fun v hv => ht v (by rw [fv, List.mem_append]; left; exact hv)) typx⟩
      den_x
    simp_rw [Option.bind_eq_none_iff]
    intro ⟨Y, _, hY⟩ den_y
    obtain rfl := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, .int,
      Typing.of_abstract (fun v hv => ht v (by rw [fv, List.mem_append]; right; exact hv)) typy⟩
      den_y
    specialize x_ih (fun v hv => ht v (by rw [fv, List.mem_append]; left; exact hv)) wf_t.1 typx
    specialize y_ih (fun v hv => ht v (by rw [fv, List.mem_append]; right; exact hv)) wf_t.2 typy
    rw [←Decidable.not_imp_not, ←ne_eq, Option.ne_none_iff_exists, ←ne_eq, Option.ne_none_iff_exists] at x_ih y_ih
    obtain ⟨⟨simpX, _, hsimpX⟩, den_simpx⟩ := x_ih ⟨_, den_x.symm⟩
    obtain ⟨⟨simpY, _, hsimpY⟩, den_simpy⟩ := y_ih ⟨_, den_y.symm⟩

    obtain rfl := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, .int,
      Typing.of_abstract (fun v hv => ht v (by rw [fv, List.mem_append]; left; exact fv_simplifier wf_t.1 hv)) (Typing.simplifier typx)⟩
      den_simpx.symm
    obtain rfl := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, .int,
      Typing.of_abstract (fun v hv => ht v (by rw [fv, List.mem_append]; right; exact fv_simplifier wf_t.2 hv)) (Typing.simplifier typy)⟩
      den_simpy.symm
    specialize h _ den_simpx.symm
    rw [Option.bind_eq_none_iff] at h
    specialize h _ den_simpy.symm
    nomatch h
  | add x y x_ih y_ih => sorry
  | mul x y x_ih y_ih => sorry
  | le x y x_ih y_ih => sorry
  | and x y x_ih y_ih => sorry
  | not x ih => sorry
  | eq x y x_ih y_ih => sorry
  | mem x S x_ih S_ih => sorry
  | collect vs D P D_ih P_ih => sorry
  | pow S ih => sorry
  | cprod S T S_ih T_ih => sorry
  | union S T S_ih T_ih => sorry
  | inter S T S_ih T_ih => sorry
  | card S ih => sorry
  | app f x f_ih x_ih => sorry
  | lambda vs D P D_ih P_ih => sorry
  | pfun A B A_ih B_ih => sorry
  | min S ih => sorry
  | max S ih => sorry
  | all vs D P D_ih P_ih => sorry
