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
  (wf_t : t.WF) {Γ : B.TypeContext} {τ : BType} (typ_t : Γ ⊢ᴮ t : τ)
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
  | le x y x_ih y_ih =>
    unfold simplifier at h
    obtain ⟨rfl, typx, typy⟩ := Typing.leE typ_t
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
  | and x y x_ih y_ih =>
    obtain ⟨rfl, typx, typy⟩ := Typing.andE typ_t
    -- self-contained fact about `simplifier_aux_and`
    have key : ∀ (p q : Term), Γ ⊢ᴮ p : .bool → Γ ⊢ᴮ q : .bool →
        ∀ (hpq : ∀ v ∈ fv (simplifier_aux_and p q), («Δ» v).isSome = true)
          (hp : ∀ v ∈ fv p, («Δ» v).isSome = true)
          (hq : ∀ v ∈ fv q, («Δ» v).isSome = true),
        ⟦(simplifier_aux_and p q).abstract «Δ» hpq⟧ᴮ = none →
        ⟦p.abstract «Δ» hp⟧ᴮ = none ∨ ⟦q.abstract «Δ» hq⟧ᴮ = none := by
      intro p q typp typq hpq hp hq hnone
      unfold simplifier_aux_and at hnone
      split at hnone
      · simp_rw [Term.abstract, denote] at hnone; nomatch hnone
      · simp_rw [Term.abstract, denote] at hnone; nomatch hnone
      · exact Or.inr hnone
      · exact Or.inl hnone
      · simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind,
          Option.bind_eq_none_iff] at hnone
        by_cases hp' : ⟦p.abstract «Δ» hp⟧ᴮ = none
        · exact Or.inl hp'
        · obtain ⟨⟨X, _, hX⟩, den_p⟩ := Option.ne_none_iff_exists'.mp hp'
          obtain rfl := denote_welltyped_eq
            ⟨Γ.abstract («Δ» := «Δ»), WFTC.of_abstract, .bool,
            Typing.of_abstract hp typp⟩
            den_p
          right
          rw [Option.eq_none_iff_forall_ne_some]
          rintro ⟨Y, _, hY⟩ den_q
          obtain rfl := denote_welltyped_eq
            ⟨Γ.abstract («Δ» := «Δ»), WFTC.of_abstract, .bool,
            Typing.of_abstract hq typq⟩
            den_q
          specialize hnone ⟨X, .bool, hX⟩ den_p
          rw [Option.bind_eq_none_iff] at hnone
          exact absurd (hnone ⟨Y, .bool, hY⟩ den_q) (by simp)
    have hx_fv : ∀ v ∈ fv x, («Δ» v).isSome = true :=
      fun v hv => ht v (by rw [fv, List.mem_append]; left; exact hv)
    have hy_fv : ∀ v ∈ fv y, («Δ» v).isSome = true :=
      fun v hv => ht v (by rw [fv, List.mem_append]; right; exact hv)
    have hsx_fv : ∀ v ∈ fv (simplifier x), («Δ» v).isSome = true :=
      fun v hv => hx_fv v (fv_simplifier wf_t.1 hv)
    have hsy_fv : ∀ v ∈ fv (simplifier y), («Δ» v).isSome = true :=
      fun v hv => hy_fv v (fv_simplifier wf_t.2 hv)
    unfold simplifier at h
    rcases key (simplifier x) (simplifier y) (Typing.simplifier typx) (Typing.simplifier typy)
        _ hsx_fv hsy_fv h with hsx | hsy
    · have hx : ⟦x.abstract «Δ» hx_fv⟧ᴮ = none := x_ih hx_fv wf_t.1 typx hsx
      simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, hx, Option.bind_none]
    · have hy : ⟦y.abstract «Δ» hy_fv⟧ᴮ = none := y_ih hy_fv wf_t.2 typy hsy
      rw [Option.eq_none_iff_forall_ne_some]
      rintro ⟨Z, _, hZ⟩ den_t
      simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at den_t
      obtain ⟨⟨X, τX, hX⟩, den_x, hmatch⟩ := den_t
      obtain rfl := denote_welltyped_eq
        ⟨Γ.abstract («Δ» := «Δ»), WFTC.of_abstract, .bool,
        Typing.of_abstract hx_fv typx⟩
        den_x
      simp_rw [Option.bind_eq_some_iff] at hmatch
      obtain ⟨⟨Y, τY, hY⟩, den_y, _⟩ := hmatch
      exact absurd (hy.symm.trans den_y) (by simp)
  | not x ih =>
    obtain ⟨rfl, typx⟩ := Typing.notE typ_t
    -- self-contained fact about `simplifier_aux_not` on a typed boolean term `q`
    have key : ∀ (q : Term), Γ ⊢ᴮ q : .bool →
        ∀ (hq : ∀ v ∈ fv (simplifier_aux_not q), («Δ» v).isSome = true)
          (hq' : ∀ v ∈ fv q, («Δ» v).isSome = true),
        ⟦(simplifier_aux_not q).abstract «Δ» hq⟧ᴮ = none →
        ⟦q.abstract «Δ» hq'⟧ᴮ = none := by
      intro q typq hq hq' hnone
      unfold simplifier_aux_not at hnone
      split at hnone
      · simp_rw [Term.abstract, denote] at hnone; nomatch hnone
      · simp_rw [Term.abstract, denote] at hnone; nomatch hnone
      · rename_i p
        simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, hnone,
          Option.bind_none]
      · rw [Option.eq_none_iff_forall_ne_some]
        rintro ⟨X, _, hX⟩ den_q
        obtain rfl := denote_welltyped_eq
          ⟨Γ.abstract («Δ» := «Δ»), WFTC.of_abstract, .bool,
          Typing.of_abstract hq' typq⟩
          den_q
        simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind,
          Option.bind_eq_none_iff] at hnone
        exact absurd (hnone ⟨X, .bool, hX⟩ den_q) (by simp)
    have hsimpx : ⟦(simplifier x).abstract «Δ»
        (fun v hv => ht v (by rw [fv]; exact fv_simplifier (t := x) wf_t hv))⟧ᴮ = none := by
      unfold simplifier at h
      exact key (simplifier x) (Typing.simplifier typx) _ _ h
    have hx : ⟦x.abstract «Δ» (fun v hv => ht v (by rw [fv]; exact hv))⟧ᴮ = none :=
      ih (fun v hv => ht v (by rw [fv]; exact hv)) wf_t typx hsimpx
    simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, hx, Option.bind_none]
  | eq x y x_ih y_ih => sorry
  | mem x S x_ih S_ih => sorry
  | collect vs D P D_ih P_ih => sorry
  | pow S ih =>
    unfold simplifier at h
    obtain ⟨α, rfl, typS⟩ := Typing.powE typ_t
    simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_none_iff] at h ⊢
    intro ⟨S', _, hS'⟩ den_S
    obtain rfl := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, .set _,
      Typing.of_abstract (fun v hv => by apply ht; rw [fv]; exact hv) typS⟩
      den_S
    specialize ih (fun v hv => by apply ht; rw [fv]; exact hv) wf_t typS
    rw [←Decidable.not_imp_not, ←ne_eq, Option.ne_none_iff_exists, ←ne_eq, Option.ne_none_iff_exists] at ih
    obtain ⟨⟨simpS, _, hsimpS⟩, den_simpS⟩ := ih ⟨_, den_S.symm⟩
    obtain rfl := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, .set _,
      Typing.of_abstract (fun v hv => by apply ht; rw [fv]; exact fv_simplifier wf_t hv) (Typing.simplifier typS)⟩
      den_simpS.symm
    specialize h _ den_simpS.symm
    nomatch h
  | cprod S T S_ih T_ih =>
    unfold simplifier at h
    obtain ⟨α, β, rfl, typS, typT⟩ := Typing.cprodE typ_t
    simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_none_iff] at h ⊢
    intro ⟨S', _, hS'⟩ den_S
    obtain rfl := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, .set α,
      Typing.of_abstract (fun v hv => ht v (by rw [fv, List.mem_append]; left; exact hv)) typS⟩
      den_S
    simp_rw [Option.bind_eq_none_iff]
    intro ⟨T', _, hT'⟩ den_T
    obtain rfl := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, .set β,
      Typing.of_abstract (fun v hv => ht v (by rw [fv, List.mem_append]; right; exact hv)) typT⟩
      den_T
    specialize S_ih (fun v hv => ht v (by rw [fv, List.mem_append]; left; exact hv)) wf_t.1 typS
    specialize T_ih (fun v hv => ht v (by rw [fv, List.mem_append]; right; exact hv)) wf_t.2 typT
    rw [←Decidable.not_imp_not, ←ne_eq, Option.ne_none_iff_exists, ←ne_eq, Option.ne_none_iff_exists] at S_ih T_ih
    obtain ⟨⟨simpS, _, hsimpS⟩, den_simpS⟩ := S_ih ⟨_, den_S.symm⟩
    obtain ⟨⟨simpT, _, hsimpT⟩, den_simpT⟩ := T_ih ⟨_, den_T.symm⟩
    obtain rfl := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, .set α,
      Typing.of_abstract (fun v hv => ht v (by rw [fv, List.mem_append]; left; exact fv_simplifier wf_t.1 hv)) (Typing.simplifier typS)⟩
      den_simpS.symm
    obtain rfl := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, .set β,
      Typing.of_abstract (fun v hv => ht v (by rw [fv, List.mem_append]; right; exact fv_simplifier wf_t.2 hv)) (Typing.simplifier typT)⟩
      den_simpT.symm
    specialize h _ den_simpS.symm
    rw [Option.bind_eq_none_iff] at h
    specialize h _ den_simpT.symm
    nomatch h
  | union S T S_ih T_ih =>
    unfold simplifier at h
    obtain ⟨α, rfl, typS, typT⟩ := Typing.unionE typ_t
    simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_none_iff] at h ⊢
    intro ⟨S', _, hS'⟩ den_S
    obtain rfl := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, .set α,
      Typing.of_abstract (fun v hv => ht v (by rw [fv, List.mem_append]; left; exact hv)) typS⟩
      den_S
    simp_rw [Option.bind_eq_none_iff]
    intro ⟨T', _, hT'⟩ den_T
    obtain rfl := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, .set α,
      Typing.of_abstract (fun v hv => ht v (by rw [fv, List.mem_append]; right; exact hv)) typT⟩
      den_T
    specialize S_ih (fun v hv => ht v (by rw [fv, List.mem_append]; left; exact hv)) wf_t.1 typS
    specialize T_ih (fun v hv => ht v (by rw [fv, List.mem_append]; right; exact hv)) wf_t.2 typT
    rw [←Decidable.not_imp_not, ←ne_eq, Option.ne_none_iff_exists, ←ne_eq, Option.ne_none_iff_exists] at S_ih T_ih
    obtain ⟨⟨simpS, _, hsimpS⟩, den_simpS⟩ := S_ih ⟨_, den_S.symm⟩
    obtain ⟨⟨simpT, _, hsimpT⟩, den_simpT⟩ := T_ih ⟨_, den_T.symm⟩
    obtain rfl := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, .set α,
      Typing.of_abstract (fun v hv => ht v (by rw [fv, List.mem_append]; left; exact fv_simplifier wf_t.1 hv)) (Typing.simplifier typS)⟩
      den_simpS.symm
    obtain rfl := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, .set α,
      Typing.of_abstract (fun v hv => ht v (by rw [fv, List.mem_append]; right; exact fv_simplifier wf_t.2 hv)) (Typing.simplifier typT)⟩
      den_simpT.symm
    specialize h _ den_simpS.symm
    rw [Option.bind_eq_none_iff] at h
    specialize h _ den_simpT.symm
    simp only [↓reduceDIte] at h
    nomatch h
  | inter S T S_ih T_ih =>
    unfold simplifier at h
    obtain ⟨α, rfl, typS, typT⟩ := Typing.interE typ_t
    simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_none_iff] at h ⊢
    intro ⟨S', _, hS'⟩ den_S
    obtain rfl := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, .set α,
      Typing.of_abstract (fun v hv => ht v (by rw [fv, List.mem_append]; left; exact hv)) typS⟩
      den_S
    simp_rw [Option.bind_eq_none_iff]
    intro ⟨T', _, hT'⟩ den_T
    obtain rfl := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, .set α,
      Typing.of_abstract (fun v hv => ht v (by rw [fv, List.mem_append]; right; exact hv)) typT⟩
      den_T
    specialize S_ih (fun v hv => ht v (by rw [fv, List.mem_append]; left; exact hv)) wf_t.1 typS
    specialize T_ih (fun v hv => ht v (by rw [fv, List.mem_append]; right; exact hv)) wf_t.2 typT
    rw [←Decidable.not_imp_not, ←ne_eq, Option.ne_none_iff_exists, ←ne_eq, Option.ne_none_iff_exists] at S_ih T_ih
    obtain ⟨⟨simpS, _, hsimpS⟩, den_simpS⟩ := S_ih ⟨_, den_S.symm⟩
    obtain ⟨⟨simpT, _, hsimpT⟩, den_simpT⟩ := T_ih ⟨_, den_T.symm⟩
    obtain rfl := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, .set α,
      Typing.of_abstract (fun v hv => ht v (by rw [fv, List.mem_append]; left; exact fv_simplifier wf_t.1 hv)) (Typing.simplifier typS)⟩
      den_simpS.symm
    obtain rfl := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, .set α,
      Typing.of_abstract (fun v hv => ht v (by rw [fv, List.mem_append]; right; exact fv_simplifier wf_t.2 hv)) (Typing.simplifier typT)⟩
      den_simpT.symm
    specialize h _ den_simpS.symm
    rw [Option.bind_eq_none_iff] at h
    specialize h _ den_simpT.symm
    simp only [↓reduceDIte] at h
    nomatch h
  | card S ih => sorry
  | app f x f_ih x_ih => sorry
  | lambda vs D P D_ih P_ih => sorry
  | pfun A B A_ih B_ih =>
    unfold simplifier at h
    obtain ⟨α, β, rfl, typA, typB⟩ := Typing.pfunE typ_t
    simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_none_iff] at h ⊢
    intro ⟨A', _, hA'⟩ den_A
    obtain rfl := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, .set α,
      Typing.of_abstract (fun v hv => ht v (by rw [fv, List.mem_append]; left; exact hv)) typA⟩
      den_A
    simp_rw [Option.bind_eq_none_iff]
    intro ⟨B', _, hB'⟩ den_B
    obtain rfl := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, .set β,
      Typing.of_abstract (fun v hv => ht v (by rw [fv, List.mem_append]; right; exact hv)) typB⟩
      den_B
    specialize A_ih (fun v hv => ht v (by rw [fv, List.mem_append]; left; exact hv)) wf_t.1 typA
    specialize B_ih (fun v hv => ht v (by rw [fv, List.mem_append]; right; exact hv)) wf_t.2 typB
    rw [←Decidable.not_imp_not, ←ne_eq, Option.ne_none_iff_exists, ←ne_eq, Option.ne_none_iff_exists] at A_ih B_ih
    obtain ⟨⟨simpA, _, hsimpA⟩, den_simpA⟩ := A_ih ⟨_, den_A.symm⟩
    obtain ⟨⟨simpB, _, hsimpB⟩, den_simpB⟩ := B_ih ⟨_, den_B.symm⟩
    obtain rfl := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, .set α,
      Typing.of_abstract (fun v hv => ht v (by rw [fv, List.mem_append]; left; exact fv_simplifier wf_t.1 hv)) (Typing.simplifier typA)⟩
      den_simpA.symm
    obtain rfl := denote_welltyped_eq
      ⟨Γ.abstract («Δ» := «Δ»),
      WFTC.of_abstract, .set β,
      Typing.of_abstract (fun v hv => ht v (by rw [fv, List.mem_append]; right; exact fv_simplifier wf_t.2 hv)) (Typing.simplifier typB)⟩
      den_simpB.symm
    specialize h _ den_simpA.symm
    rw [Option.bind_eq_none_iff] at h
    specialize h _ den_simpB.symm
    nomatch h
  | min S ih => sorry
  | max S ih => sorry
  | all vs D P D_ih P_ih => sorry
