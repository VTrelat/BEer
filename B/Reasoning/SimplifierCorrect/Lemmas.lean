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
  (h : ⟦(simplifier t).abstract («Δ» := «Δ») (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ = none)
  (wf : B.RenWF Γ «Δ» := by assumption) :
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
    replace x_ih := fun hh => x_ih (fun v hv => ht v (by rw [fv, List.mem_append]; left; exact hv)) wf_t.1 typx hh wf
    replace y_ih := fun hh => y_ih (fun v hv => ht v (by rw [fv, List.mem_append]; right; exact hv)) wf_t.2 typy hh wf
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
    replace x_ih := fun hh => x_ih (fun v hv => ht v (by rw [fv, List.mem_append]; left; exact hv)) wf_t.1 typx hh wf
    replace y_ih := fun hh => y_ih (fun v hv => ht v (by rw [fv, List.mem_append]; right; exact hv)) wf_t.2 typy hh wf
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
  | add x y x_ih y_ih =>
    obtain ⟨rfl, typx, typy⟩ := Typing.addE typ_t
    -- peel `⟦a +ᴮ b⟧ = none` into a disjunction
    have peel_add : ∀ (a b : Term), Γ ⊢ᴮ a : .int → Γ ⊢ᴮ b : .int →
        ∀ (hab : ∀ v ∈ fv (a +ᴮ b), («Δ» v).isSome = true)
          (ha : ∀ v ∈ fv a, («Δ» v).isSome = true)
          (hb : ∀ v ∈ fv b, («Δ» v).isSome = true),
        ⟦(a +ᴮ b).abstract «Δ» hab⟧ᴮ = none →
        ⟦a.abstract «Δ» ha⟧ᴮ = none ∨ ⟦b.abstract «Δ» hb⟧ᴮ = none := by
      intro a b typa typb hab ha hb hnone
      by_cases ha' : ⟦a.abstract «Δ» ha⟧ᴮ = none
      · exact Or.inl ha'
      · obtain ⟨⟨A, _, hA⟩, den_a⟩ := Option.ne_none_iff_exists'.mp ha'
        obtain rfl := denote_welltyped_eq
          ⟨Γ.abstract («Δ» := «Δ»), WFTC.of_abstract, .int,
          Typing.of_abstract ha typa⟩ den_a
        right
        rw [Option.eq_none_iff_forall_ne_some]
        rintro ⟨B, _, hB⟩ den_b
        obtain rfl := denote_welltyped_eq
          ⟨Γ.abstract («Δ» := «Δ»), WFTC.of_abstract, .int,
          Typing.of_abstract hb typb⟩ den_b
        simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind,
          Option.bind_eq_none_iff] at hnone
        specialize hnone ⟨A, .int, hA⟩ den_a
        rw [Option.bind_eq_none_iff] at hnone
        exact absurd (hnone ⟨B, .int, hB⟩ den_b) (by simp)
    -- `⟦a⟧ = none → ⟦a +ᴮ b⟧ = none`
    have add_none_l : ∀ (a b : Term)
        (hab : ∀ v ∈ fv (a +ᴮ b), («Δ» v).isSome = true)
        (ha : ∀ v ∈ fv a, («Δ» v).isSome = true),
        ⟦a.abstract «Δ» ha⟧ᴮ = none → ⟦(a +ᴮ b).abstract «Δ» hab⟧ᴮ = none := by
      intro a b hab ha hnone
      simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, hnone,
        Option.bind_none]
    -- self-contained fact about `simplifier_aux_add`
    have key : ∀ (p q : Term), Γ ⊢ᴮ p : .int → Γ ⊢ᴮ q : .int →
        ∀ (hpq : ∀ v ∈ fv (simplifier_aux_add p q), («Δ» v).isSome = true)
          (hp : ∀ v ∈ fv p, («Δ» v).isSome = true)
          (hq : ∀ v ∈ fv q, («Δ» v).isSome = true),
        ⟦(simplifier_aux_add p q).abstract «Δ» hpq⟧ᴮ = none →
        ⟦p.abstract «Δ» hp⟧ᴮ = none ∨ ⟦q.abstract «Δ» hq⟧ᴮ = none := by
      intro p q typp typq hpq hp hq hnone
      unfold simplifier_aux_add at hnone
      split at hnone
      · exact Or.inr hnone
      · exact Or.inl hnone
      · simp_rw [Term.abstract, denote] at hnone; nomatch hnone
      · -- p = x' +ᴮ int a, q = int b ; result x' +ᴮ int (a+b)
        left
        obtain ⟨_, typx', _⟩ := Typing.addE typp
        refine add_none_l _ _ hp
          (fun v hv => hp v (by rw [fv, List.mem_append]; left; exact hv)) ?_
        rcases peel_add _ _ typx' Typing.int _
          (fun v hv => hp v (by rw [fv, List.mem_append]; left; exact hv))
          (fun v hv => by rw [fv] at hv; nomatch hv) hnone with hx'_n | hint_n
        · exact hx'_n
        · simp_rw [Term.abstract, denote] at hint_n; nomatch hint_n
      · -- catch-all
        exact peel_add _ _ typp typq _ hp hq hnone
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
    · have hx : ⟦x.abstract «Δ» hx_fv⟧ᴮ = none := x_ih hx_fv wf_t.1 typx hsx wf
      simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, hx, Option.bind_none]
    · have hy : ⟦y.abstract «Δ» hy_fv⟧ᴮ = none := y_ih hy_fv wf_t.2 typy hsy wf
      rw [Option.eq_none_iff_forall_ne_some]
      rintro ⟨Z, _, hZ⟩ den_t
      simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at den_t
      obtain ⟨⟨X, τX, hX⟩, den_x, hmatch⟩ := den_t
      obtain rfl := denote_welltyped_eq
        ⟨Γ.abstract («Δ» := «Δ»), WFTC.of_abstract, .int,
        Typing.of_abstract hx_fv typx⟩ den_x
      simp_rw [Option.bind_eq_some_iff] at hmatch
      obtain ⟨⟨Y, τY, hY⟩, den_y, _⟩ := hmatch
      exact absurd (hy.symm.trans den_y) (by simp)
  | mul x y x_ih y_ih =>
    obtain ⟨rfl, typx, typy⟩ := Typing.mulE typ_t
    -- peel `⟦a *ᴮ b⟧ = none` into a disjunction
    have peel_mul : ∀ (a b : Term), Γ ⊢ᴮ a : .int → Γ ⊢ᴮ b : .int →
        ∀ (hab : ∀ v ∈ fv (a *ᴮ b), («Δ» v).isSome = true)
          (ha : ∀ v ∈ fv a, («Δ» v).isSome = true)
          (hb : ∀ v ∈ fv b, («Δ» v).isSome = true),
        ⟦(a *ᴮ b).abstract «Δ» hab⟧ᴮ = none →
        ⟦a.abstract «Δ» ha⟧ᴮ = none ∨ ⟦b.abstract «Δ» hb⟧ᴮ = none := by
      intro a b typa typb hab ha hb hnone
      by_cases ha' : ⟦a.abstract «Δ» ha⟧ᴮ = none
      · exact Or.inl ha'
      · obtain ⟨⟨A, _, hA⟩, den_a⟩ := Option.ne_none_iff_exists'.mp ha'
        obtain rfl := denote_welltyped_eq
          ⟨Γ.abstract («Δ» := «Δ»), WFTC.of_abstract, .int,
          Typing.of_abstract ha typa⟩ den_a
        right
        rw [Option.eq_none_iff_forall_ne_some]
        rintro ⟨B, _, hB⟩ den_b
        obtain rfl := denote_welltyped_eq
          ⟨Γ.abstract («Δ» := «Δ»), WFTC.of_abstract, .int,
          Typing.of_abstract hb typb⟩ den_b
        simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind,
          Option.bind_eq_none_iff] at hnone
        specialize hnone ⟨A, .int, hA⟩ den_a
        rw [Option.bind_eq_none_iff] at hnone
        exact absurd (hnone ⟨B, .int, hB⟩ den_b) (by simp)
    -- `⟦a⟧ = none → ⟦a *ᴮ b⟧ = none`
    have mul_none_l : ∀ (a b : Term)
        (hab : ∀ v ∈ fv (a *ᴮ b), («Δ» v).isSome = true)
        (ha : ∀ v ∈ fv a, («Δ» v).isSome = true),
        ⟦a.abstract «Δ» ha⟧ᴮ = none → ⟦(a *ᴮ b).abstract «Δ» hab⟧ᴮ = none := by
      intro a b hab ha hnone
      simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, hnone,
        Option.bind_none]
    -- self-contained fact about `simplifier_aux_mul`
    have key : ∀ (p q : Term), Γ ⊢ᴮ p : .int → Γ ⊢ᴮ q : .int →
        ∀ (hpq : ∀ v ∈ fv (simplifier_aux_mul p q), («Δ» v).isSome = true)
          (hp : ∀ v ∈ fv p, («Δ» v).isSome = true)
          (hq : ∀ v ∈ fv q, («Δ» v).isSome = true),
        ⟦(simplifier_aux_mul p q).abstract «Δ» hpq⟧ᴮ = none →
        ⟦p.abstract «Δ» hp⟧ᴮ = none ∨ ⟦q.abstract «Δ» hq⟧ᴮ = none := by
      intro p q typp typq hpq hp hq hnone
      unfold simplifier_aux_mul at hnone
      split at hnone
      · simp_rw [Term.abstract, denote] at hnone; nomatch hnone
      · simp_rw [Term.abstract, denote] at hnone; nomatch hnone
      · exact Or.inr hnone
      · exact Or.inl hnone
      · simp_rw [Term.abstract, denote] at hnone; nomatch hnone
      · -- p = x' *ᴮ int a, q = int b ; result x' *ᴮ int (a*b)
        left
        obtain ⟨_, typx', _⟩ := Typing.mulE typp
        refine mul_none_l _ _ hp
          (fun v hv => hp v (by rw [fv, List.mem_append]; left; exact hv)) ?_
        rcases peel_mul _ _ typx' Typing.int _
          (fun v hv => hp v (by rw [fv, List.mem_append]; left; exact hv))
          (fun v hv => by rw [fv] at hv; nomatch hv) hnone with hx'_n | hint_n
        · exact hx'_n
        · simp_rw [Term.abstract, denote] at hint_n; nomatch hint_n
      · -- catch-all
        exact peel_mul _ _ typp typq _ hp hq hnone
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
    · have hx : ⟦x.abstract «Δ» hx_fv⟧ᴮ = none := x_ih hx_fv wf_t.1 typx hsx wf
      simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, hx, Option.bind_none]
    · have hy : ⟦y.abstract «Δ» hy_fv⟧ᴮ = none := y_ih hy_fv wf_t.2 typy hsy wf
      rw [Option.eq_none_iff_forall_ne_some]
      rintro ⟨Z, _, hZ⟩ den_t
      simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at den_t
      obtain ⟨⟨X, τX, hX⟩, den_x, hmatch⟩ := den_t
      obtain rfl := denote_welltyped_eq
        ⟨Γ.abstract («Δ» := «Δ»), WFTC.of_abstract, .int,
        Typing.of_abstract hx_fv typx⟩ den_x
      simp_rw [Option.bind_eq_some_iff] at hmatch
      obtain ⟨⟨Y, τY, hY⟩, den_y, _⟩ := hmatch
      exact absurd (hy.symm.trans den_y) (by simp)
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
    replace x_ih := fun hh => x_ih (fun v hv => ht v (by rw [fv, List.mem_append]; left; exact hv)) wf_t.1 typx hh wf
    replace y_ih := fun hh => y_ih (fun v hv => ht v (by rw [fv, List.mem_append]; right; exact hv)) wf_t.2 typy hh wf
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
    · have hx : ⟦x.abstract «Δ» hx_fv⟧ᴮ = none := x_ih hx_fv wf_t.1 typx hsx wf
      simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, hx, Option.bind_none]
    · have hy : ⟦y.abstract «Δ» hy_fv⟧ᴮ = none := y_ih hy_fv wf_t.2 typy hsy wf
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
      ih (fun v hv => ht v (by rw [fv]; exact hv)) wf_t typx hsimpx wf
    simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, hx, Option.bind_none]
  | eq x y x_ih y_ih =>
    obtain ⟨rfl, α, typx, typy⟩ := Typing.eqE typ_t
    -- peel `⟦a =ᴮ b⟧ = none` into a disjunction, given both sides typed `α`
    have peel_eq : ∀ (a b : Term), Γ ⊢ᴮ a : α → Γ ⊢ᴮ b : α →
        ∀ (hab : ∀ v ∈ fv (a =ᴮ b), («Δ» v).isSome = true)
          (ha : ∀ v ∈ fv a, («Δ» v).isSome = true)
          (hb : ∀ v ∈ fv b, («Δ» v).isSome = true),
        ⟦(a =ᴮ b).abstract «Δ» hab⟧ᴮ = none →
        ⟦a.abstract «Δ» ha⟧ᴮ = none ∨ ⟦b.abstract «Δ» hb⟧ᴮ = none := by
      intro a b typa typb hab ha hb hnone
      by_cases ha' : ⟦a.abstract «Δ» ha⟧ᴮ = none
      · exact Or.inl ha'
      · obtain ⟨⟨A, _, hA⟩, den_a⟩ := Option.ne_none_iff_exists'.mp ha'
        obtain rfl := denote_welltyped_eq
          ⟨Γ.abstract («Δ» := «Δ»), WFTC.of_abstract, α,
          Typing.of_abstract ha typa⟩ den_a
        right
        rw [Option.eq_none_iff_forall_ne_some]
        rintro ⟨B, _, hB⟩ den_b
        obtain rfl := denote_welltyped_eq
          ⟨Γ.abstract («Δ» := «Δ»), WFTC.of_abstract, α,
          Typing.of_abstract hb typb⟩ den_b
        simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind,
          Option.bind_eq_none_iff] at hnone
        specialize hnone ⟨A, α, hA⟩ den_a
        exact absurd (hnone ⟨B, α, hB⟩ den_b) (by simp)
    -- self-contained fact about `simplifier_aux_eq`
    have key : ∀ (p q : Term), Γ ⊢ᴮ p : α → Γ ⊢ᴮ q : α →
        ∀ (hpq : ∀ v ∈ fv (simplifier_aux_eq p q), («Δ» v).isSome = true)
          (hp : ∀ v ∈ fv p, («Δ» v).isSome = true)
          (hq : ∀ v ∈ fv q, («Δ» v).isSome = true),
        ⟦(simplifier_aux_eq p q).abstract «Δ» hpq⟧ᴮ = none →
        ⟦p.abstract «Δ» hp⟧ᴮ = none ∨ ⟦q.abstract «Δ» hq⟧ᴮ = none := by
      intro p q typp typq hpq hp hq hnone
      unfold simplifier_aux_eq at hnone
      split at hnone
      · -- var v', var v
        split_ifs at hnone with hvv
        · simp_rw [Term.abstract, denote] at hnone; nomatch hnone
        · exact peel_eq _ _ typp typq _ hp hq hnone
      · -- e, var v
        exact (peel_eq _ _ typq typp _ hq hp hnone).symm
      · -- p, bool true
        exact Or.inl hnone
      · -- bool true, q
        exact Or.inr hnone
      · -- p, bool false  (q is the literal `bool false`, so α = .bool)
        cases typq
        left
        simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind,
          Option.bind_eq_none_iff] at hnone
        rw [Option.eq_none_iff_forall_ne_some]
        rintro ⟨A, _, hA⟩ den_p
        obtain rfl := denote_welltyped_eq
          ⟨Γ.abstract («Δ» := «Δ»), WFTC.of_abstract, .bool,
          Typing.of_abstract hp typp⟩ den_p
        exact absurd (hnone ⟨A, .bool, hA⟩ den_p) (by simp)
      · -- bool false, q  (p is the literal `bool false`, so α = .bool)
        cases typp
        right
        simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind,
          Option.bind_eq_none_iff] at hnone
        rw [Option.eq_none_iff_forall_ne_some]
        rintro ⟨A, _, hA⟩ den_q
        obtain rfl := denote_welltyped_eq
          ⟨Γ.abstract («Δ» := «Δ»), WFTC.of_abstract, .bool,
          Typing.of_abstract hq typq⟩ den_q
        exact absurd (hnone ⟨A, .bool, hA⟩ den_q) (by simp)
      · -- catch-all p, q
        split_ifs at hnone with hpq'
        · simp_rw [Term.abstract, denote] at hnone; nomatch hnone
        · exact peel_eq _ _ typp typq _ hp hq hnone
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
    · have hx : ⟦x.abstract «Δ» hx_fv⟧ᴮ = none := x_ih hx_fv wf_t.1 typx hsx wf
      simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, hx, Option.bind_none]
    · have hy : ⟦y.abstract «Δ» hy_fv⟧ᴮ = none := y_ih hy_fv wf_t.2 typy hsy wf
      rw [Option.eq_none_iff_forall_ne_some]
      rintro ⟨Z, _, hZ⟩ den_t
      simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at den_t
      obtain ⟨⟨X, τX, hX⟩, den_x, hmatch⟩ := den_t
      obtain rfl := denote_welltyped_eq
        ⟨Γ.abstract («Δ» := «Δ»), WFTC.of_abstract, α,
        Typing.of_abstract hx_fv typx⟩ den_x
      obtain ⟨⟨Y, τY, hY⟩, den_y, _⟩ := hmatch
      exact absurd (hy.symm.trans den_y) (by simp)
  | mem x S x_ih S_ih =>
    -- TODO: blocked — `simplifier_aux_mem` rewrites set-comprehension membership
    -- (`x ∈ᴮ collect vs D P ⟿ (x ∈ᴮ D) ∧ᴮ substList vs xs P`); proving this
    -- preserves the "denotation is none" property requires a substitution-
    -- denotation soundness lemma (`⟦substList vs ts P⟧` vs `⟦P⟧` under env
    -- updates) that does not exist upstream of this file.
    sorry
  | collect vs D P D_ih P_ih =>
    -- TODO: blocked on forward denotation preservation (`simplifier_partial_correct`,
    -- proven downstream in SimplifierCorrect/Basic.lean). The `collect` denotation
    -- guards on value-dependent `dite`s (`den_P`, `typP_det`) over `⟦P x⟧`; relating
    -- `⟦simplifier P⟧` to `⟦P⟧` here needs the forward direction, which would be a
    -- circular import.
    sorry
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
    replace ih := fun hh => ih (fun v hv => by apply ht; rw [fv]; exact hv) wf_t typS hh wf
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
    replace S_ih := fun hh => S_ih (fun v hv => ht v (by rw [fv, List.mem_append]; left; exact hv)) wf_t.1 typS hh wf
    replace T_ih := fun hh => T_ih (fun v hv => ht v (by rw [fv, List.mem_append]; right; exact hv)) wf_t.2 typT hh wf
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
    replace S_ih := fun hh => S_ih (fun v hv => ht v (by rw [fv, List.mem_append]; left; exact hv)) wf_t.1 typS hh wf
    replace T_ih := fun hh => T_ih (fun v hv => ht v (by rw [fv, List.mem_append]; right; exact hv)) wf_t.2 typT hh wf
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
    replace S_ih := fun hh => S_ih (fun v hv => ht v (by rw [fv, List.mem_append]; left; exact hv)) wf_t.1 typS hh wf
    replace T_ih := fun hh => T_ih (fun v hv => ht v (by rw [fv, List.mem_append]; right; exact hv)) wf_t.2 typT hh wf
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
  | card S ih =>
    -- TODO: blocked on forward denotation preservation (`simplifier_partial_correct`,
    -- proven downstream in SimplifierCorrect/Basic.lean). `⟦|S|ᴮ⟧` guards on the
    -- value-dependent test `S'.IsFinite`; the IH only gives the none→none direction,
    -- so the some-but-not-finite subcase needs the forward direction (circular import).
    sorry
  | app f x f_ih x_ih =>
    -- TODO: blocked on forward denotation preservation (`simplifier_partial_correct`,
    -- proven downstream in SimplifierCorrect/Basic.lean). `⟦f x⟧` guards on the
    -- value-dependent tests `F.IsPFunc`/`X ∈ F.Dom`; the some-but-test-fails subcase
    -- needs the forward direction (circular import).
    sorry
  | lambda vs D P D_ih P_ih =>
    -- TODO: blocked on forward denotation preservation (`simplifier_partial_correct`,
    -- proven downstream in SimplifierCorrect/Basic.lean). `⟦lambda⟧` guards on
    -- value-dependent `dite`s (`den_E`, `typE_det`) over `⟦E x⟧`; relating
    -- `⟦simplifier P⟧` to `⟦P⟧` needs the forward direction (circular import).
    sorry
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
    replace A_ih := fun hh => A_ih (fun v hv => ht v (by rw [fv, List.mem_append]; left; exact hv)) wf_t.1 typA hh wf
    replace B_ih := fun hh => B_ih (fun v hv => ht v (by rw [fv, List.mem_append]; right; exact hv)) wf_t.2 typB hh wf
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
  | min S ih =>
    -- TODO: blocked on forward denotation preservation (`simplifier_partial_correct`,
    -- proven downstream in SimplifierCorrect/Basic.lean). `⟦S.min⟧` guards on the
    -- value-dependent test `S'.IsFinite ∧ S'.Nonempty`; the some-but-test-fails
    -- subcase needs the forward direction (circular import).
    sorry
  | max S ih =>
    -- TODO: blocked on forward denotation preservation (`simplifier_partial_correct`,
    -- proven downstream in SimplifierCorrect/Basic.lean). `⟦S.max⟧` guards on the
    -- value-dependent test `S'.IsFinite ∧ S'.Nonempty`; the some-but-test-fails
    -- subcase needs the forward direction (circular import).
    sorry
  | all vs D P D_ih P_ih =>
    -- TODO: blocked on forward denotation preservation (`simplifier_partial_correct`,
    -- proven downstream in SimplifierCorrect/Basic.lean). `simplifier_aux_all` both
    -- rewrites `∀` over comprehensions and the `all` denotation guards on
    -- value-dependent `dite`s over `⟦P x⟧`; both need the forward direction.
    sorry
