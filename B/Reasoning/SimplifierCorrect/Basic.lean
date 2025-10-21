import B.Reasoning.SimplifierCorrect.Lemmas
import B.Reasoning.SimplifierCorrect.CaseAdd
import B.Reasoning.SimplifierCorrect.CaseMul

open Classical B PHOAS ZFSet

section simplifier_correct
/-
  Because some values are absorbed by the simplifier, the correctness of the simplifier is not
  total. For example:
  `simplifier (0 *ᴮ card ℕ) = 0`, though `card ℕ` has no denotation.
  Thus it is wrong to assert that `⟦simplifier (x *ᴮ y)⟧ᴮ = ⟦x *ᴮ y⟧ᴮ`, and more generally
  `⟦simplifier x⟧ᴮ = ⟦x⟧ᴮ` is not true for all `x`.
-/

theorem simplifier_correct.maplet.{u} (x y : B.Term)
  (x_ih :
    ∀ {«Δ» : 𝒱 → Option B.Dom.{u}} (ht : ∀ v ∈ fv x, («Δ» v).isSome = true) (wf_t : x.WF) {Γ : B.TypeContext} {τ : BType},
      Γ ⊢ x : τ → ⟦x.abstract «Δ» ht⟧ᴮ = ⟦(simplifier x).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ)
  (y_ih :
    ∀ {«Δ» : 𝒱 → Option B.Dom.{u}} (ht : ∀ v ∈ fv y, («Δ» v).isSome = true) (wf_t : y.WF) {Γ : B.TypeContext} {τ : BType},
      Γ ⊢ y : τ → ⟦y.abstract «Δ» ht⟧ᴮ = ⟦(simplifier y).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ)
  {«Δ» : 𝒱 → Option B.Dom.{u}} (ht : ∀ v ∈ fv (x ↦ᴮ y), («Δ» v).isSome = true) (wf_t : (x ↦ᴮ y).WF) {Γ : B.TypeContext}
  {τ : BType} (typ_t : Γ ⊢ x ↦ᴮ y : τ) :
  ⟦(x ↦ᴮ y).abstract «Δ» ht⟧ᴮ = ⟦(simplifier (x ↦ᴮ y)).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ := by
  obtain ⟨α, β, rfl, hx, hy⟩ := Typing.mapletE typ_t
  specialize x_ih (fun v hv => ht v (by rw [fv, List.mem_append]; left; exact hv)) wf_t.1 hx
  specialize y_ih (fun v hv => ht v (by rw [fv, List.mem_append]; right; exact hv)) wf_t.2 hy
  simp_rw [simplifier, Term.abstract, denote, x_ih, y_ih]
theorem simplifier_correct.sub.{u} (x y : B.Term)
  (x_ih :
    ∀ {«Δ» : 𝒱 → Option B.Dom.{u}} (ht : ∀ v ∈ fv x, («Δ» v).isSome = true) (wf_t : x.WF) {Γ : B.TypeContext} {τ : BType},
      Γ ⊢ x : τ → ⟦x.abstract «Δ» ht⟧ᴮ = ⟦(simplifier x).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ)
  (y_ih :
    ∀ {«Δ» : 𝒱 → Option B.Dom.{u}} (ht : ∀ v ∈ fv y, («Δ» v).isSome = true) (wf_t : y.WF) {Γ : B.TypeContext} {τ : BType},
      Γ ⊢ y : τ → ⟦y.abstract «Δ» ht⟧ᴮ = ⟦(simplifier y).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ)
  {«Δ» : 𝒱 → Option B.Dom.{u}} (ht : ∀ v ∈ fv (x -ᴮ y), («Δ» v).isSome = true) (wf_t : (x -ᴮ y).WF) {Γ : B.TypeContext}
  {τ : BType} (typ_t : Γ ⊢ x -ᴮ y : τ) :
  ⟦(x -ᴮ y).abstract «Δ» ht⟧ᴮ = ⟦(simplifier (x -ᴮ y)).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ := by
  obtain ⟨rfl, hx, hy⟩ := Typing.subE typ_t
  specialize x_ih (fun v hv => ht v (by rw [fv, List.mem_append]; left; exact hv)) wf_t.1 hx
  specialize y_ih (fun v hv => ht v (by rw [fv, List.mem_append]; right; exact hv)) wf_t.2 hy
  simp_rw [simplifier, Term.abstract, denote, x_ih, y_ih]
theorem simplifier_correct.le.{u} (x y : B.Term)
  (x_ih :
    ∀ {«Δ» : 𝒱 → Option B.Dom.{u}} (ht : ∀ v ∈ fv x, («Δ» v).isSome = true) (wf_t : x.WF) {Γ : B.TypeContext} {τ : BType},
      Γ ⊢ x : τ → ⟦x.abstract «Δ» ht⟧ᴮ = ⟦(simplifier x).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ)
  (y_ih :
    ∀ {«Δ» : 𝒱 → Option B.Dom.{u}} (ht : ∀ v ∈ fv y, («Δ» v).isSome = true) (wf_t : y.WF) {Γ : B.TypeContext} {τ : BType},
      Γ ⊢ y : τ → ⟦y.abstract «Δ» ht⟧ᴮ = ⟦(simplifier y).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ)
  {«Δ» : 𝒱 → Option B.Dom.{u}} (ht : ∀ v ∈ fv (x ≤ᴮ y), («Δ» v).isSome = true) (wf_t : (x -ᴮ y).WF) {Γ : B.TypeContext}
  {τ : BType} (typ_t : Γ ⊢ x ≤ᴮ y : τ) :
  ⟦(x ≤ᴮ y).abstract «Δ» ht⟧ᴮ = ⟦(simplifier (x ≤ᴮ y)).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ := by
  obtain ⟨rfl, hx, hy⟩ := Typing.leE typ_t
  specialize x_ih (fun v hv => ht v (by rw [fv, List.mem_append]; left; exact hv)) wf_t.1 hx
  specialize y_ih (fun v hv => ht v (by rw [fv, List.mem_append]; right; exact hv)) wf_t.2 hy
  simp_rw [simplifier, Term.abstract, denote, x_ih, y_ih]
theorem simplifier_correct.cprod.{u} (x y : B.Term)
  (x_ih :
    ∀ {«Δ» : 𝒱 → Option B.Dom.{u}} (ht : ∀ v ∈ fv x, («Δ» v).isSome = true) (wf_t : x.WF) {Γ : B.TypeContext} {τ : BType},
      Γ ⊢ x : τ → ⟦x.abstract «Δ» ht⟧ᴮ = ⟦(simplifier x).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ)
  (y_ih :
    ∀ {«Δ» : 𝒱 → Option B.Dom.{u}} (ht : ∀ v ∈ fv y, («Δ» v).isSome = true) (wf_t : y.WF) {Γ : B.TypeContext} {τ : BType},
      Γ ⊢ y : τ → ⟦y.abstract «Δ» ht⟧ᴮ = ⟦(simplifier y).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ)
  {«Δ» : 𝒱 → Option B.Dom.{u}} (ht : ∀ v ∈ fv (x ⨯ᴮ y), («Δ» v).isSome = true) (wf_t : (x ⨯ᴮ y).WF) {Γ : B.TypeContext}
  {τ : BType} (typ_t : Γ ⊢ x ⨯ᴮ y : τ) :
  ⟦(x ⨯ᴮ y).abstract «Δ» ht⟧ᴮ = ⟦(simplifier (x ⨯ᴮ y)).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ := by
  obtain ⟨_, _, rfl, hx, hy⟩ := Typing.cprodE typ_t
  specialize x_ih (fun v hv => ht v (by rw [fv, List.mem_append]; left; exact hv)) wf_t.1 hx
  specialize y_ih (fun v hv => ht v (by rw [fv, List.mem_append]; right; exact hv)) wf_t.2 hy
  simp_rw [simplifier, Term.abstract, denote, x_ih, y_ih]
theorem simplifier_correct.union.{u} (x y : B.Term)
  (x_ih :
    ∀ {«Δ» : 𝒱 → Option B.Dom.{u}} (ht : ∀ v ∈ fv x, («Δ» v).isSome = true) (wf_t : x.WF) {Γ : B.TypeContext} {τ : BType},
      Γ ⊢ x : τ → ⟦x.abstract «Δ» ht⟧ᴮ = ⟦(simplifier x).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ)
  (y_ih :
    ∀ {«Δ» : 𝒱 → Option B.Dom.{u}} (ht : ∀ v ∈ fv y, («Δ» v).isSome = true) (wf_t : y.WF) {Γ : B.TypeContext} {τ : BType},
      Γ ⊢ y : τ → ⟦y.abstract «Δ» ht⟧ᴮ = ⟦(simplifier y).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ)
  {«Δ» : 𝒱 → Option B.Dom.{u}} (ht : ∀ v ∈ fv (x ∪ᴮ y), («Δ» v).isSome = true) (wf_t : (x ∪ᴮ y).WF) {Γ : B.TypeContext}
  {τ : BType} (typ_t : Γ ⊢ x ∪ᴮ y : τ) :
  ⟦(x ∪ᴮ y).abstract «Δ» ht⟧ᴮ = ⟦(simplifier (x ∪ᴮ y)).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ := by
  obtain ⟨_, rfl, hx, hy⟩ := Typing.unionE typ_t
  specialize x_ih (fun v hv => ht v (by rw [fv, List.mem_append]; left; exact hv)) wf_t.1 hx
  specialize y_ih (fun v hv => ht v (by rw [fv, List.mem_append]; right; exact hv)) wf_t.2 hy
  simp_rw [simplifier, Term.abstract, denote, x_ih, y_ih]
theorem simplifier_correct.inter.{u} (x y : B.Term)
  (x_ih :
    ∀ {«Δ» : 𝒱 → Option B.Dom.{u}} (ht : ∀ v ∈ fv x, («Δ» v).isSome = true) (wf_t : x.WF) {Γ : B.TypeContext} {τ : BType},
      Γ ⊢ x : τ → ⟦x.abstract «Δ» ht⟧ᴮ = ⟦(simplifier x).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ)
  (y_ih :
    ∀ {«Δ» : 𝒱 → Option B.Dom.{u}} (ht : ∀ v ∈ fv y, («Δ» v).isSome = true) (wf_t : y.WF) {Γ : B.TypeContext} {τ : BType},
      Γ ⊢ y : τ → ⟦y.abstract «Δ» ht⟧ᴮ = ⟦(simplifier y).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ)
  {«Δ» : 𝒱 → Option B.Dom.{u}} (ht : ∀ v ∈ fv (x ∩ᴮ y), («Δ» v).isSome = true) (wf_t : (x ∩ᴮ y).WF) {Γ : B.TypeContext}
  {τ : BType} (typ_t : Γ ⊢ x ∩ᴮ y : τ) :
  ⟦(x ∩ᴮ y).abstract «Δ» ht⟧ᴮ = ⟦(simplifier (x ∩ᴮ y)).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ := by
  obtain ⟨_, rfl, hx, hy⟩ := Typing.interE typ_t
  specialize x_ih (fun v hv => ht v (by rw [fv, List.mem_append]; left; exact hv)) wf_t.1 hx
  specialize y_ih (fun v hv => ht v (by rw [fv, List.mem_append]; right; exact hv)) wf_t.2 hy
  simp_rw [simplifier, Term.abstract, denote, x_ih, y_ih]
theorem simplifier_correct.pfun.{u} (x y : B.Term)
  (x_ih :
    ∀ {«Δ» : 𝒱 → Option B.Dom.{u}} (ht : ∀ v ∈ fv x, («Δ» v).isSome = true) (wf_t : x.WF) {Γ : B.TypeContext} {τ : BType},
      Γ ⊢ x : τ → ⟦x.abstract «Δ» ht⟧ᴮ = ⟦(simplifier x).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ)
  (y_ih :
    ∀ {«Δ» : 𝒱 → Option B.Dom.{u}} (ht : ∀ v ∈ fv y, («Δ» v).isSome = true) (wf_t : y.WF) {Γ : B.TypeContext} {τ : BType},
      Γ ⊢ y : τ → ⟦y.abstract «Δ» ht⟧ᴮ = ⟦(simplifier y).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ)
  {«Δ» : 𝒱 → Option B.Dom.{u}} (ht : ∀ v ∈ fv (x ⇸ᴮ y), («Δ» v).isSome = true) (wf_t : (x ⇸ᴮ y).WF) {Γ : B.TypeContext}
  {τ : BType} (typ_t : Γ ⊢ x ⇸ᴮ y : τ) :
  ⟦(x ⇸ᴮ y).abstract «Δ» ht⟧ᴮ = ⟦(simplifier (x ⇸ᴮ y)).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ := by
  obtain ⟨_, _, rfl, hx, hy⟩ := Typing.pfunE typ_t
  specialize x_ih (fun v hv => ht v (by rw [fv, List.mem_append]; left; exact hv)) wf_t.1 hx
  specialize y_ih (fun v hv => ht v (by rw [fv, List.mem_append]; right; exact hv)) wf_t.2 hy
  simp_rw [simplifier, Term.abstract, denote, x_ih, y_ih]
theorem simplifier_correct.min.{u} (S : B.Term)
  (ih :
    ∀ {«Δ» : 𝒱 → Option B.Dom.{u}} (ht : ∀ v ∈ fv S, («Δ» v).isSome = true) (wf_t : S.WF) {Γ : B.TypeContext} {τ : BType},
      Γ ⊢ S : τ → ⟦S.abstract «Δ» ht⟧ᴮ = ⟦(simplifier S).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ)
  {«Δ» : 𝒱 → Option B.Dom.{u}} (ht : ∀ v ∈ fv S.min, («Δ» v).isSome = true) (wf_t : S.min.WF) {Γ : B.TypeContext}
  {τ : BType} (typ_t : Γ ⊢ S.min : τ) : ⟦S.min.abstract «Δ» ht⟧ᴮ = ⟦(simplifier S.min).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ := by
  unfold simplifier
  obtain ⟨rfl, typS⟩ := Typing.minE typ_t
  specialize ih (fun v hv => ht v hv) wf_t typS
  simp_rw [Term.abstract, denote, ih]
theorem simplifier_correct.max.{u} (S : B.Term)
  (ih :
    ∀ {«Δ» : 𝒱 → Option B.Dom.{u}} (ht : ∀ v ∈ fv S, («Δ» v).isSome = true) (wf_t : S.WF) {Γ : B.TypeContext} {τ : BType},
      Γ ⊢ S : τ → ⟦S.abstract «Δ» ht⟧ᴮ = ⟦(simplifier S).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ)
  {«Δ» : 𝒱 → Option B.Dom.{u}} (ht : ∀ v ∈ fv S.max, («Δ» v).isSome = true) (wf_t : S.max.WF) {Γ : B.TypeContext}
  {τ : BType} (typ_t : Γ ⊢ S.max : τ) : ⟦S.max.abstract «Δ» ht⟧ᴮ = ⟦(simplifier S.max).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ := by
  unfold simplifier
  obtain ⟨rfl, typS⟩ := Typing.maxE typ_t
  specialize ih (fun v hv => ht v hv) wf_t typS
  simp_rw [Term.abstract, denote, ih]
theorem simplifier_correct.card.{u} (S : B.Term)
  (ih :
    ∀ {«Δ» : 𝒱 → Option B.Dom.{u}} (ht : ∀ v ∈ fv S, («Δ» v).isSome = true) (wf_t : S.WF) {Γ : B.TypeContext} {τ : BType},
      Γ ⊢ S : τ → ⟦S.abstract «Δ» ht⟧ᴮ = ⟦(simplifier S).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ)
  {«Δ» : 𝒱 → Option B.Dom.{u}} (ht : ∀ v ∈ fv S.card, («Δ» v).isSome = true) (wf_t : S.card.WF) {Γ : B.TypeContext}
  {τ : BType} (typ_t : Γ ⊢ S.card : τ) : ⟦S.card.abstract «Δ» ht⟧ᴮ = ⟦(simplifier S.card).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ := by
  unfold simplifier
  obtain ⟨rfl, _, typS⟩ := Typing.cardE typ_t
  specialize ih (fun v hv => ht v hv) wf_t typS
  simp_rw [Term.abstract, denote, ih]
theorem simplifier_correct.pow.{u} (S : B.Term)
  (ih :
    ∀ {«Δ» : 𝒱 → Option B.Dom.{u}} (ht : ∀ v ∈ fv S, («Δ» v).isSome = true) (wf_t : S.WF) {Γ : B.TypeContext} {τ : BType},
      Γ ⊢ S : τ → ⟦S.abstract «Δ» ht⟧ᴮ = ⟦(simplifier S).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ)
  {«Δ» : 𝒱 → Option B.Dom.{u}} (ht : ∀ v ∈ fv S.pow, («Δ» v).isSome = true) (wf_t : S.pow.WF) {Γ : B.TypeContext}
  {τ : BType} (typ_t : Γ ⊢ S.pow : τ) : ⟦S.pow.abstract «Δ» ht⟧ᴮ = ⟦(simplifier S.pow).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ := by
  unfold simplifier
  obtain ⟨_, rfl, typS⟩ := Typing.powE typ_t
  specialize ih (fun v hv => ht v hv) wf_t typS
  simp_rw [Term.abstract, denote, ih]

theorem simplifier_correct.lambda.{u_1} (vs : List 𝒱) (D P : B.Term)
  (D_ih :
    ∀ {«Δ» : 𝒱 → Option B.Dom.{u_1}} (ht : ∀ v ∈ fv D, («Δ» v).isSome = true) (wf_t : D.WF) {Γ : B.TypeContext} {τ : BType},
      Γ ⊢ D : τ →
        ⟦D.abstract «Δ» ht⟧ᴮ = ⟦(simplifier D).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ)
  (P_ih :
    ∀ {«Δ» : 𝒱 → Option B.Dom.{u_1}} (ht : ∀ v ∈ fv P, («Δ» v).isSome = true) (wf_t : P.WF) {Γ : B.TypeContext} {τ : BType},
      Γ ⊢ P : τ →
        ⟦P.abstract «Δ» ht⟧ᴮ = ⟦(simplifier P).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ)
  {«Δ» : 𝒱 → Option B.Dom.{u_1}} (ht : ∀ v ∈ fv (B.Term.lambda vs D P), («Δ» v).isSome = true)
  (wf_t : (B.Term.lambda vs D P).WF) {Γ : B.TypeContext} {τ : BType} (typ_t : Γ ⊢ B.Term.lambda vs D P : τ) :
  ⟦(B.Term.lambda vs D P).abstract «Δ» ht⟧ᴮ = ⟦(simplifier (B.Term.lambda vs D P)).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ := by
  stop
  -- unfold definitions
  simp only [Term.abstract, denote, ne_eq, Lean.Elab.WF.paramLet, dite_eq_ite,
    Option.pure_def, Option.bind_eq_bind, dite_not, simplifier]

  -- use D_ih
  obtain ⟨γ, αs, Ds, vs_nemp, vs_αs_len, vs_Ds_len, rfl, rfl, typDs, typP, vs_Γ_disj⟩ := B.Typing.lambdaE typ_t
  rw [
    List.Forall₂_eq_Forall₂' (List.Forall₂.length_eq typDs),
    B.Typing.reduce_of_Forall₂' (by rwa [←List.length_pos_iff, ←vs_Ds_len, List.length_pos_iff])]
    at typDs
  specialize D_ih («Δ» := «Δ») (fun v hv => ht v (by rw [fv, List.mem_append]; left; exact hv)) wf_t.1 typDs
  simp_rw [D_ih]
  congr; ext1 z; congr; ext 𝒟 τ h𝒟 : 3

  have Δ_isSome_P : ∀ v ∈ fv P, v ∉ vs → («Δ» v).isSome = true := by
    intro v hv hvs
    apply ht
    rw [fv, List.mem_append, List.mem_removeAll_iff]
    right
    exact ⟨hv, hvs⟩
  have Δ_isSome_simpP : ∀ v ∈ fv (simplifier P), v ∉ vs → («Δ» v).isSome = true := by
    intro v hv hvs
    apply ht
    rw [fv, List.mem_append, List.mem_removeAll_iff]
    right
    exact ⟨fv_simplifier wf_t.2.1 hv, hvs⟩

  split_ifs with τ_hasArity 𝒟_emp τ_default_hasArity choose_hasArity_mem <;> try rfl
  · let f (i : Fin vs.length) : Dom := ⟨τ.defaultZFSet.get vs.length i, τ.get vs.length i, get_mem_type_of_isTuple (BType.hasArity_of_foldl_defaultZFSet τ_hasArity) τ_hasArity BType.mem_toZFSet_of_defaultZFSet⟩
    -- transform Term.abstract.go into Term.abstract in lhs
    have Δ_update_isSome_P : ∀ v ∈ fv P, (Function.updates «Δ» vs (List.ofFn fun i => some (f i)) v).isSome = true := by
      intro v hv
      rw [Function.updates_eq_if (by rw [List.length_ofFn]) wf_t.2.2.1]
      split_ifs with hvs
      · simp only [List.getElem_ofFn, Option.isSome_some]
      · exact Δ_isSome_P v hv hvs
    rw [denote_term_abstract_go_eq_term_abstract wf_t.2.2.1 vs_nemp f Δ_update_isSome_P]

    -- transform Term.abstract.go into Term.abstract in rhs
    have Δ_update_isSome_simpP : ∀ v ∈ fv (simplifier P), (Function.updates «Δ» vs (List.ofFn fun i => some (f i)) v).isSome = true := by
      intro v hv
      rw [Function.updates_eq_if (by rw [List.length_ofFn]) wf_t.2.2.1]
      split_ifs with hvs
      · simp only [List.getElem_ofFn, Option.isSome_some]
      · exact Δ_isSome_P v (fv_simplifier wf_t.2.1 hv) hvs
    rw [denote_term_abstract_go_eq_term_abstract wf_t.2.2.1 vs_nemp f Δ_update_isSome_simpP]

    -- apply P_ih
    rw [P_ih («Δ» := Function.updates «Δ» vs (List.ofFn fun i => some (f i))) Δ_update_isSome_P wf_t.2.1 typP]

  · generalize_proofs 𝒟_exists pf_f
    let f (i : Fin vs.length) : Dom := ⟨(choose 𝒟_exists).get vs.length i, τ.get vs.length i, pf_f i⟩
    -- transform Term.abstract.go into Term.abstract in lhs
    have Δ_update_isSome_P : ∀ v ∈ fv P, (Function.updates «Δ» vs (List.ofFn fun i => some (f i)) v).isSome = true := by
      intro v hv
      rw [Function.updates_eq_if (by rw [List.length_ofFn]) wf_t.2.2.1]
      split_ifs with hvs
      · simp only [List.getElem_ofFn, Option.isSome_some]
      · exact Δ_isSome_P v hv hvs
    have := @denote_term_abstract_go_eq vs P «Δ» wf_t.2.2.1 vs_nemp f Δ_update_isSome_P
    rw [congr_heq this (x := Δ_isSome_P) (y := Δ_update_isSome_P) (proof_irrel_heq _ _)]
    -- transform Term.abstract.go into Term.abstract in rhs
    have Δ_update_isSome_simpP : ∀ v ∈ fv (simplifier P), (Function.updates «Δ» vs (List.ofFn fun i => some (f i)) v).isSome = true := by
      intro v hv
      rw [Function.updates_eq_if (by rw [List.length_ofFn]) wf_t.2.2.1]
      split_ifs with hvs
      · simp only [List.getElem_ofFn, Option.isSome_some]
      · exact Δ_isSome_P v (fv_simplifier wf_t.2.1 hv) hvs
    rw [denote_term_abstract_go_eq_term_abstract wf_t.2.2.1 vs_nemp f Δ_update_isSome_simpP]
    -- apply P_ih
    rw [P_ih («Δ» := Function.updates «Δ» vs (List.ofFn fun i => some (f i))) Δ_update_isSome_P wf_t.2.1 typP]
    congr
    funext 𝒳
    rw [Option.some_inj]
    congr
    · funext xy
      congr
      funext hxy
      congr 1

      -- transform Term.abstract.go into Term.abstract in lhs
      let f (i : Fin vs.length) : Dom := ⟨xy.π₁.get vs.length i, τ.get vs.length i, by (expose_names; exact pf xy hxy i)⟩
      have Δ_update_isSome_P : ∀ v ∈ fv P, (Function.updates «Δ» vs (List.ofFn fun i => some (f i)) v).isSome = true := by
        intro v hv
        rw [Function.updates_eq_if (by rw [List.length_ofFn]) wf_t.2.2.1]
        split_ifs with hvs
        · simp only [List.getElem_ofFn, Option.isSome_some]
        · exact Δ_isSome_P v hv hvs
      rw [denote_term_abstract_go_eq_term_abstract wf_t.2.2.1 vs_nemp f Δ_update_isSome_P]
      -- transform Term.abstract.go into Term.abstract in rhs
      have Δ_update_isSome_simpP : ∀ v ∈ fv (simplifier P), (Function.updates «Δ» vs (List.ofFn fun i => some (f i)) v).isSome = true := by
        intro v hv
        rw [Function.updates_eq_if (by rw [List.length_ofFn]) wf_t.2.2.1]
        split_ifs with hvs
        · simp only [List.getElem_ofFn, Option.isSome_some]
        · exact Δ_isSome_P v (fv_simplifier wf_t.2.1 hv) hvs
      have := @denote_term_abstract_go_eq vs (simplifier P) «Δ» wf_t.2.2.1 vs_nemp f Δ_update_isSome_simpP
      rw [congr_heq this (x := Δ_isSome_simpP) (y := Δ_update_isSome_simpP) (proof_irrel_heq _ _)]

      -- apply P_ih
      rw [P_ih («Δ» := Function.updates «Δ» vs (List.ofFn fun i => some (f i))) Δ_update_isSome_P wf_t.2.1 typP]

    · funext τ'
      congr
      funext xy
      congr
      funext hxy
      congr 1

      -- transform Term.abstract.go into Term.abstract in lhs
      let f (i : Fin vs.length) : Dom := ⟨xy.π₁.get vs.length i, τ.get vs.length i, by (expose_names; exact pf xy hxy i)⟩
      have Δ_update_isSome_P : ∀ v ∈ fv P, (Function.updates «Δ» vs (List.ofFn fun i => some (f i)) v).isSome = true := by
        intro v hv
        rw [Function.updates_eq_if (by rw [List.length_ofFn]) wf_t.2.2.1]
        split_ifs with hvs
        · simp only [List.getElem_ofFn, Option.isSome_some]
        · exact Δ_isSome_P v hv hvs
      rw [denote_term_abstract_go_eq_term_abstract wf_t.2.2.1 vs_nemp f Δ_update_isSome_P]
      -- transform Term.abstract.go into Term.abstract in rhs
      have Δ_update_isSome_simpP : ∀ v ∈ fv (simplifier P), (Function.updates «Δ» vs (List.ofFn fun i => some (f i)) v).isSome = true := by
        intro v hv
        rw [Function.updates_eq_if (by rw [List.length_ofFn]) wf_t.2.2.1]
        split_ifs with hvs
        · simp only [List.getElem_ofFn, Option.isSome_some]
        · exact Δ_isSome_P v (fv_simplifier wf_t.2.1 hv) hvs
      rw [denote_term_abstract_go_eq_term_abstract wf_t.2.2.1 vs_nemp f Δ_update_isSome_simpP]

      -- apply P_ih
      rw [P_ih («Δ» := Function.updates «Δ» vs (List.ofFn fun i => some (f i))) Δ_update_isSome_P wf_t.2.1 typP]

    · apply proof_irrel_heq

theorem simplifier_partial_correct.maplet.{u_1} (x y : B.Term)
  (x_ih :
    ∀ {«Δ» : 𝒱 → Option B.Dom} (ht : ∀ v ∈ fv x, («Δ» v).isSome = true) (wf_t : x.WF) {Γ : B.TypeContext} {τ : BType},
      Γ ⊢ x : τ →
        ∀ {T : ZFSet.{u_1}} {hTτ : T ∈ τ.toZFSet},
          ⟦x.abstract «Δ» ht⟧ᴮ = some ⟨T, τ, hTτ⟩ → ⟦(simplifier x).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ = some ⟨T, τ, hTτ⟩)
  (y_ih :
    ∀ {«Δ» : 𝒱 → Option B.Dom} (ht : ∀ v ∈ fv y, («Δ» v).isSome = true) (wf_t : y.WF) {Γ : B.TypeContext} {τ : BType},
      Γ ⊢ y : τ →
        ∀ {T : ZFSet.{u_1}} {hTτ : T ∈ τ.toZFSet},
          ⟦y.abstract «Δ» ht⟧ᴮ = some ⟨T, τ, hTτ⟩ → ⟦(simplifier y).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ = some ⟨T, τ, hTτ⟩)
  {«Δ» : 𝒱 → Option B.Dom} (ht : ∀ v ∈ fv (x ↦ᴮ y), («Δ» v).isSome = true) (wf_t : (x ↦ᴮ y).WF) {Γ : B.TypeContext}
  {τ : BType} (typ_t : Γ ⊢ x ↦ᴮ y : τ) {T : ZFSet.{u_1}} {hTτ : T ∈ τ.toZFSet}
  (den_t : ⟦(x ↦ᴮ y).abstract «Δ» ht⟧ᴮ = some ⟨T, τ, hTτ⟩) :
  ⟦(simplifier (x ↦ᴮ y)).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ = some ⟨T, τ, hTτ⟩ := by
  unfold simplifier
  simp_rw [Term.abstract, denote]
  simp only [Option.pure_def, Option.bind_eq_bind]
  rcases typ_t
  rename_i α β hx hy
  simp_rw [Term.abstract, denote, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff, PSigma.exists] at den_t
  obtain ⟨X, τX, hX, den_x, Y, τY, hY, den_y, eq⟩ := den_t
  rw [Option.some_inj] at eq
  injection eq
  subst T

  obtain ⟨⟩ := denote_welltyped_eq
    ⟨Γ.abstract («Δ» := «Δ»),
    WFTC.of_abstract, α,
    Typing.of_abstract (fun v hv => by apply ht; rw [fv, List.mem_append]; left; exact hv) ‹_›⟩
    den_x
  specialize x_ih _ wf_t.1 hx den_x
  obtain ⟨⟩ := denote_welltyped_eq
    ⟨Γ.abstract («Δ» := «Δ»),
    WFTC.of_abstract, β,
    Typing.of_abstract (fun v hv => by apply ht; rw [fv, List.mem_append]; right; exact hv) ‹_›⟩
    den_y
  specialize y_ih _ wf_t.2 hy den_y
  rw [x_ih, y_ih]
  simp_rw [Option.bind_some]

theorem simplifier_partial_correct.add.{u_1} (x y : B.Term)
  (x_ih :
    ∀ {«Δ» : 𝒱 → Option B.Dom} (ht : ∀ v ∈ fv x, («Δ» v).isSome = true) (wf_t : x.WF) {Γ : B.TypeContext} {τ : BType},
      Γ ⊢ x : τ →
        ∀ {T : ZFSet.{u_1}} {hTτ : T ∈ τ.toZFSet},
          ⟦x.abstract «Δ» ht⟧ᴮ = some ⟨T, τ, hTτ⟩ → ⟦(simplifier x).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ = some ⟨T, τ, hTτ⟩)
  (y_ih :
    ∀ {«Δ» : 𝒱 → Option B.Dom} (ht : ∀ v ∈ fv y, («Δ» v).isSome = true) (wf_t : y.WF) {Γ : B.TypeContext} {τ : BType},
      Γ ⊢ y : τ →
        ∀ {T : ZFSet.{u_1}} {hTτ : T ∈ τ.toZFSet},
          ⟦y.abstract «Δ» ht⟧ᴮ = some ⟨T, τ, hTτ⟩ → ⟦(simplifier y).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ = some ⟨T, τ, hTτ⟩)
  {«Δ» : 𝒱 → Option B.Dom} (ht : ∀ v ∈ fv (x +ᴮ y), («Δ» v).isSome = true) (wf_t : (x +ᴮ y).WF) {Γ : B.TypeContext}
  {τ : BType} (typ_t : Γ ⊢ x +ᴮ y : τ) {T : ZFSet.{u_1}} {hTτ : T ∈ τ.toZFSet}
  (den_t : ⟦(x +ᴮ y).abstract «Δ» ht⟧ᴮ = some ⟨T, τ, hTτ⟩) :
  ⟦(simplifier (x +ᴮ y)).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ = some ⟨T, τ, hTτ⟩ := by
  simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_t
  obtain ⟨X, τX, hX, den_x, eq⟩ := den_t

  obtain ⟨rfl, _, _⟩ := Typing.addE typ_t
  obtain ⟨⟩ := denote_welltyped_eq
    ⟨Γ.abstract («Δ» := «Δ»),
    WFTC.of_abstract, .int,
    Typing.of_abstract (fun v hv => by apply ht; rw [fv, List.mem_append]; left; exact hv) ‹_›⟩
    den_x

  simp_rw [Option.bind_eq_some_iff, PSigma.exists] at eq
  obtain ⟨Y, τY, hY, den_y, eq⟩ := eq
  obtain ⟨⟩ := denote_welltyped_eq
    ⟨Γ.abstract («Δ» := «Δ»),
    WFTC.of_abstract, .int,
    Typing.of_abstract (fun v hv => by apply ht; rw [fv, List.mem_append]; right; exact hv) ‹_›⟩
    den_y

  rw [Option.some_inj] at eq
  injection eq
  subst T

  specialize x_ih _ wf_t.1 ‹_› den_x
  specialize y_ih _ wf_t.2 ‹_› den_y

  rw [simplifier_partial_correct_aux_add' x y ht wf_t typ_t x_ih y_ih]

theorem simplifier_partial_correct.pow.{u_1} (S : B.Term)
  (ih :
    ∀ {«Δ» : 𝒱 → Option B.Dom} (ht : ∀ v ∈ fv S, («Δ» v).isSome = true) (wf_t : S.WF) {Γ : B.TypeContext} {τ : BType},
      Γ ⊢ S : τ →
        ∀ {T : ZFSet.{u_1}} {hTτ : T ∈ τ.toZFSet},
          ⟦S.abstract «Δ» ht⟧ᴮ = some ⟨T, τ, hTτ⟩ → ⟦(simplifier S).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ = some ⟨T, τ, hTτ⟩)
  {«Δ» : 𝒱 → Option B.Dom} (ht : ∀ v ∈ fv (𝒫ᴮ S), («Δ» v).isSome = true) (wf_t : ( 𝒫ᴮ S).WF) {Γ : B.TypeContext}
  {τ : BType} (typ_t : Γ ⊢ 𝒫ᴮ S : τ) {T : ZFSet.{u_1}} {hTτ : T ∈ τ.toZFSet}
  (den_t : ⟦( 𝒫ᴮ S).abstract «Δ» ht⟧ᴮ = some ⟨T, τ, hTτ⟩) :
  ⟦(simplifier ( 𝒫ᴮ S)).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ = some ⟨T, τ, hTτ⟩ := by
  unfold simplifier
  simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind,
    Option.bind_eq_some_iff, PSigma.exists] at den_t
  obtain ⟨α, rfl, typS⟩ := Typing.powE typ_t
  obtain ⟨S', β, hS', den_S, eq⟩ := den_t
  obtain ⟨⟩ := denote_welltyped_eq
    ⟨Γ.abstract («Δ» := «Δ»),
    WFTC.of_abstract, α.set,
    Typing.of_abstract (fun v hv => by apply ht; rw [fv]; exact hv) typS⟩
    den_S
  rw [Option.some_inj] at eq
  injection eq
  subst T
  specialize ih _ wf_t typS den_S
  rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, ih, Option.bind_some]

theorem simplifier_partial_correct.le.{u_1} (x y : B.Term)
  (x_ih :
    ∀ {«Δ» : 𝒱 → Option B.Dom} (ht : ∀ v ∈ fv x, («Δ» v).isSome = true) (wf_t : x.WF) {Γ : B.TypeContext} {τ : BType},
      Γ ⊢ x : τ →
        ∀ {T : ZFSet.{u_1}} {hTτ : T ∈ τ.toZFSet},
          ⟦x.abstract «Δ» ht⟧ᴮ = some ⟨T, ⟨τ, hTτ⟩⟩ → ⟦(simplifier x).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ = some ⟨T, τ, hTτ⟩)
  (y_ih :
    ∀ {«Δ» : 𝒱 → Option B.Dom} (ht : ∀ v ∈ fv y, («Δ» v).isSome = true) (wf_t : y.WF) {Γ : B.TypeContext} {τ : BType},
      Γ ⊢ y : τ →
        ∀ {T : ZFSet.{u_1}} {hTτ : T ∈ τ.toZFSet},
          ⟦y.abstract «Δ» ht⟧ᴮ = some ⟨T, τ, hTτ⟩ → ⟦(simplifier y).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ = some ⟨T, τ, hTτ⟩)
  {«Δ» : 𝒱 → Option B.Dom} (ht : ∀ v ∈ fv (x ≤ᴮ y), («Δ» v).isSome = true) (wf_t : (x ≤ᴮ y).WF) {Γ : B.TypeContext}
  {τ : BType} (typ_t : Γ ⊢ x ≤ᴮ y : τ) {T : ZFSet.{u_1}} {hTτ : T ∈ τ.toZFSet}
  (den_t : ⟦(x ≤ᴮ y).abstract «Δ» ht⟧ᴮ = some ⟨T, ⟨τ, hTτ⟩⟩) :
  ⟦(simplifier (x ≤ᴮ y)).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ = some ⟨T, τ, hTτ⟩ := by
  unfold simplifier
  simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind,
    Option.bind_eq_some_iff, PSigma.exists] at den_t
  obtain ⟨rfl, typx, typy⟩ := Typing.leE typ_t
  obtain ⟨X, β, hX, den_x, eq⟩ := den_t
  obtain ⟨⟩ := denote_welltyped_eq
    ⟨Γ.abstract («Δ» := «Δ»),
    WFTC.of_abstract, .int,
    Typing.of_abstract (fun v hv => by apply ht; rw [fv, List.mem_append]; left; exact hv) typx⟩
    den_x
  simp only [Option.bind_eq_some_iff, PSigma.exists] at eq
  obtain ⟨Y, β, hY, den_y, eq⟩ := eq
  obtain ⟨⟩ := denote_welltyped_eq
    ⟨Γ.abstract («Δ» := «Δ»),
    WFTC.of_abstract, .int,
    Typing.of_abstract (fun v hv => by apply ht; rw [fv, List.mem_append]; right; exact hv) typy⟩
    den_y
  rw [Option.some_inj] at eq
  injection eq
  subst T

  specialize x_ih _ wf_t.1 typx den_x
  specialize y_ih _ wf_t.2 typy den_y
  simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind,
    x_ih, Option.bind_some, y_ih, Option.bind_some]


theorem simplifier_partial_correct.lambda.{u_1} (vs : List 𝒱) (D P : B.Term)
  (D_ih :
    ∀ {«Δ» : 𝒱 → Option B.Dom} (ht : ∀ v ∈ fv D, («Δ» v).isSome = true) (wf_t : D.WF) {Γ : B.TypeContext} {τ : BType},
      Γ ⊢ D : τ →
        ∀ {T : ZFSet.{u_1}} {hTτ : T ∈ τ.toZFSet},
          ⟦D.abstract «Δ» ht⟧ᴮ = some ⟨T, ⟨τ, hTτ⟩⟩ → ⟦(simplifier D).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ = some ⟨T, τ, hTτ⟩)
  (P_ih :
    ∀ {«Δ» : 𝒱 → Option B.Dom} (ht : ∀ v ∈ fv P, («Δ» v).isSome = true) (wf_t : P.WF) {Γ : B.TypeContext} {τ : BType},
      Γ ⊢ P : τ →
        ∀ {T : ZFSet.{u_1}} {hTτ : T ∈ τ.toZFSet},
          ⟦P.abstract «Δ» ht⟧ᴮ = some ⟨T, ⟨τ, hTτ⟩⟩ → ⟦(simplifier P).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ = some ⟨T, ⟨τ, hTτ⟩⟩)
  {«Δ» : 𝒱 → Option B.Dom} (ht : ∀ v ∈ fv (B.Term.lambda vs D P), («Δ» v).isSome = true)
  (wf_t : (B.Term.lambda vs D P).WF) {Γ : B.TypeContext} {τ : BType} (typ_t : Γ ⊢ B.Term.lambda vs D P : τ)
  {T : ZFSet.{u_1}} {hTτ : T ∈ τ.toZFSet} (den_t : ⟦(B.Term.lambda vs D P).abstract «Δ» ht⟧ᴮ = some ⟨T, τ, hTτ⟩) :
  ⟦(simplifier (B.Term.lambda vs D P)).abstract «Δ» (isSome_fv_simplifier_of_fv_isSome wf_t ht)⟧ᴮ = some ⟨T, τ, hTτ⟩ := by
  -- destruct types
  obtain ⟨γ, αs, Ds, vs_nemp, vs_αs_len, vs_Ds_len, rfl, vs_nodup, rfl, typ_Dᵢ, typ_P, vs_Γ_disj⟩ := Typing.lambdaE typ_t

  -- use hyp
  simp_rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_t

  obtain ⟨𝒟, β, h𝒟, den_D, eq⟩ := den_t

  rw [
    List.Forall₂_eq_Forall₂' (List.Forall₂.length_eq typ_Dᵢ),
    Typing.reduce_of_Forall₂' (by rwa [←List.length_pos_iff, ←vs_Ds_len, List.length_pos_iff])] at typ_Dᵢ
  obtain rfl := denote_welltyped_eq
    ⟨Γ.abstract («Δ» := «Δ»),
    WFTC.of_abstract, .set _,
    Typing.of_abstract (fun v hv => by apply ht; rw [fv, List.mem_append]; left; exact hv) typ_Dᵢ⟩
    den_D
  specialize D_ih _ wf_t.1 typ_Dᵢ den_D

  dsimp at eq

  have updates_isSome_fv_P {x : Fin vs.length → Dom} :
            ∀ v ∈ fv P, (Function.updates «Δ» vs (List.ofFn fun i => some (x i)) v).isSome = true := by
            intro v hv
            rw [Function.updates_eq_if (by rw [List.length_ofFn]) wf_t.2.2.1]
            split_ifs with v_mem_vs
            · rw [List.getElem_ofFn, Option.isSome_some]
            · apply ht
              rw [fv, List.mem_append, List.mem_removeAll_iff]
              right
              exact ⟨hv, v_mem_vs⟩
  have updates_isSome_fv_simp_P {x : Fin vs.length → Dom} : ∀ v ∈ fv (simplifier P), (Function.updates «Δ» vs (List.ofFn fun i => some (x i)) v).isSome = true := by
    intro v hv
    rw [Function.updates_eq_if (by rw [List.length_ofFn]) wf_t.2.2.1]
    split_ifs with v_mem_vs
    · rw [List.getElem_ofFn, Option.isSome_some]
    · apply ht
      rw [fv, List.mem_append, List.mem_removeAll_iff]
      right
      exact ⟨fv_simplifier wf_t.2.1 hv, v_mem_vs⟩

  split_ifs at eq with αs_hasArity denP_isSome typ_denP_det 𝒟_emp αs_default_hasArity choose_hasArity
  · -- 𝒟 = ∅
    -- transform Term.abstract.go into Term.abstract to make the result usable in the IH
    rw [denote_term_abstract_go_eq_term_abstract (vs_nodup := wf_t.2.2.1) (vs_nemp := vs_nemp) (pf := updates_isSome_fv_P)] at eq
    simp_rw [Option.bind_eq_some_iff, PSigma.exists] at eq
    obtain ⟨ℙ, γ, hℙ, den_P, eq⟩ := eq
    rw [Option.some_inj] at eq
    injection eq with eq heq
    subst T
    injections
    subst γ

    have P_ih' := @P_ih
    specialize P_ih ?_ wf_t.2.1 typ_P den_P

    simp_rw [simplifier, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, D_ih, Option.bind_some, dite_cond_eq_true (eq_true αs_hasArity), ne_eq, dite_cond_eq_false (eq_false (not_not.mpr 𝒟_emp)), dite_cond_eq_true (eq_true αs_default_hasArity)]

    rw [denote_term_abstract_go_eq_term_abstract (vs_nodup := wf_t.2.2.1) (vs_nemp := vs_nemp) (pf := updates_isSome_fv_simp_P)]
    split_ifs with den_simpP_isSome typ_simpP_det
    · rw [P_ih, Option.bind_some]
    · push_neg at typ_simpP_det
      obtain ⟨x, y, x_𝒟, y_𝒟, contr⟩ := typ_simpP_det
      obtain ⟨⟨x₁, α, hx₁⟩, eq₁⟩ := Option.isSome_iff_exists.mp <| denP_isSome x_𝒟
      obtain ⟨⟨x₂, β, hx₂⟩, eq₂⟩ := Option.isSome_iff_exists.mp <| denP_isSome y_𝒟

      generalize_proofs pf_contr₁ pf_contr₂ pf_contr₃ at contr
      obtain ⟨⟨x₁', α', hx₁'⟩, eq₁'⟩ := Option.isSome_iff_exists.mp <| den_simpP_isSome x_𝒟
      generalize_proofs pf_eq₁ at eq₁
      obtain ⟨⟨x₂', β', hx₂'⟩, eq₂'⟩ := Option.isSome_iff_exists.mp <| den_simpP_isSome y_𝒟
      generalize_proofs at eq₂
      rw [Option.get_of_eq_some pf_contr₂ eq₁', Option.get_of_eq_some pf_contr₃ eq₂'] at contr
      dsimp at contr
      specialize typ_denP_det x y x_𝒟 y_𝒟
      generalize_proofs pf₁ pf₂ at typ_denP_det
      rw [Option.get_of_eq_some pf₁ eq₁, Option.get_of_eq_some pf₂ eq₂] at typ_denP_det
      dsimp at typ_denP_det
      subst β

      rw [denote_term_abstract_go_eq_term_abstract (vs_nodup := wf_t.2.2.1) (vs_nemp := vs_nemp) (pf := updates_isSome_fv_P)] at eq₁
      obtain rfl := denote_welltyped_eq
        ⟨TypeContext.abstract (vs.zipToAList αs ∪ Γ) («Δ» := Function.updates «Δ» vs (List.ofFn fun i => some (x i))),
        WFTC.of_abstract, _,
        Typing.of_abstract updates_isSome_fv_P typ_P⟩
        eq₁
      have := @P_ih' («Δ» := Function.updates «Δ» vs (List.ofFn fun i => some (x i))) updates_isSome_fv_P wf_t.2.1 _ _ typ_P x₁ hx₁ eq₁
      rw [←denote_term_abstract_go_eq_term_abstract (vs_nodup := wf_t.2.2.1) (vs_nemp := vs_nemp) (pf := updates_isSome_fv_simp_P)] at this
      rw [eq₁', Option.some_inj] at this
      injection this with eq heq
      subst eq
      injection heq with eq
      subst α'

      rw [denote_term_abstract_go_eq_term_abstract (vs_nodup := wf_t.2.2.1) (vs_nemp := vs_nemp) (pf := updates_isSome_fv_simp_P)] at eq₂'
      rw [denote_term_abstract_go_eq_term_abstract (vs_nodup := wf_t.2.2.1) (vs_nemp := vs_nemp) (pf := updates_isSome_fv_P)] at eq₂
      have := @P_ih' («Δ» := Function.updates «Δ» vs (List.ofFn fun i => some (y i))) updates_isSome_fv_P wf_t.2.1 _ _ typ_P x₂ hx₂ eq₂
      rw [eq₂', Option.some_inj] at this
      injection this with eq heq
      subst eq
      injection heq
      subst β'
      nomatch contr
    · push_neg at den_simpP_isSome
      simp_rw [ne_eq, Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at den_simpP_isSome
      obtain ⟨xs, xs_mem_𝒟, den_simP_eq_none⟩ := den_simpP_isSome

      rw [denote_term_abstract_go_eq_term_abstract (vs_nodup := wf_t.2.2.1) (vs_nemp := vs_nemp) (pf := updates_isSome_fv_simp_P)] at den_simP_eq_none
      specialize @P_ih' («Δ» := Function.updates «Δ» vs (List.ofFn fun i => some (xs i))) updates_isSome_fv_P wf_t.2.1 _ _ typ_P (ZFSet.ofFinDom xs)
      have contr := simplifier_partial_correct' («Δ» := Function.updates «Δ» vs (List.ofFn fun i => some (xs i))) updates_isSome_fv_P wf_t.2.1 typ_P den_simP_eq_none
      specialize denP_isSome xs_mem_𝒟
      rw [denote_term_abstract_go_eq_term_abstract (vs_nodup := wf_t.2.2.1) (vs_nemp := vs_nemp) (pf := updates_isSome_fv_P)] at denP_isSome
      rw [←Option.not_isSome_iff_eq_none] at contr
      nomatch contr denP_isSome
  · -- 𝒟 ≠ ∅
    -- transform Term.abstract.go into Term.abstract to make the result usable in the IH
    rw [denote_term_abstract_go_eq_term_abstract (vs_nodup := wf_t.2.2.1) (vs_nemp := vs_nemp)] at eq
    · simp_rw [Option.bind_eq_some_iff, PSigma.exists] at eq
      obtain ⟨ℙ, γ, hℙ, den_P, eq⟩ := eq
      rw [Option.some_inj] at eq
      injection eq with eq heq
      subst T
      injections
      subst γ

      simp_rw [simplifier, Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, D_ih, Option.bind_some, dite_cond_eq_true (eq_true αs_hasArity), ne_eq, dite_cond_eq_true (eq_true 𝒟_emp), dite_cond_eq_true (eq_true choose_hasArity)]

      rw [denote_term_abstract_go_eq_term_abstract (vs_nodup := wf_t.2.2.1) (vs_nemp := vs_nemp) (pf := updates_isSome_fv_simp_P)]

      split_ifs with den_simpP_isSome typ_den_simpP_det
      · apply P_ih updates_isSome_fv_P wf_t.2.1 typ_P at den_P
        simp_rw [den_P, Option.bind_some, Option.some_inj]
        congr 2
        on_goal 3 => apply proof_irrel_heq
        on_goal 2 =>
          funext τ
          congr
        all_goals
        · funext xy
          congr
          funext xy_hasArity
          congr
          funext hxy
          congr 1

          generalize_proofs pf₁ pf₂ pf₃ pf₄
          have := @denP_isSome fun i => ⟨xy.π₁.get vs.length i, (List.reduce (fun x1 x2 => x1 ×ᴮ x2) αs pf₂).get vs.length i, pf₃ i⟩
          rw [Option.isSome_iff_exists] at this
          specialize this ?_
          · rw [ZFSet.ofFinDom_get (List.length_pos_iff.mpr vs_nemp) pf₃ hxy.1 αs_hasArity]
            exact hxy.2
          · obtain ⟨⟨x₁, α, hx₁⟩, den_P⟩ := this
            rw [den_P]
            rw [denote_term_abstract_go_eq_term_abstract (vs_nodup := wf_t.2.2.1) (vs_nemp := vs_nemp) (pf := updates_isSome_fv_P)] at den_P

            obtain rfl := denote_welltyped_eq
              ⟨TypeContext.abstract (vs.zipToAList αs ∪ Γ) («Δ» := Function.updates «Δ» vs (List.ofFn fun i => some ⟨xy.π₁.get vs.length i, (List.reduce (fun x1 x2 => x1 ×ᴮ x2) αs pf₂).get vs.length i, pf₃ i⟩)),
              WFTC.of_abstract, _,
              Typing.of_abstract updates_isSome_fv_P typ_P⟩
              den_P

            have := P_ih («Δ» := Function.updates «Δ» vs (List.ofFn fun i => some ⟨xy.π₁.get vs.length i, (List.reduce (fun x1 x2 => x1 ×ᴮ x2) αs pf₂).get vs.length i, pf₃ i⟩)) _ wf_t.2.1 typ_P den_P

            rw [denote_term_abstract_go_eq_term_abstract (vs_nodup := wf_t.2.2.1) (vs_nemp := vs_nemp) (pf := updates_isSome_fv_simp_P), this]
      · push_neg at typ_den_simpP_det
        obtain ⟨x, y, x_𝒟, y_𝒟, typ_ne⟩ := typ_den_simpP_det
        specialize typ_denP_det x y x_𝒟 y_𝒟

        obtain ⟨⟨x₁, τ₁, hx₁⟩, den₁⟩ := Option.isSome_iff_exists.mp <| denP_isSome x_𝒟
        obtain ⟨⟨y₁, τ₂, hy₁⟩, den₂⟩ := Option.isSome_iff_exists.mp <| denP_isSome y_𝒟

        generalize_proofs pf₁ pf₂ pf₃ at typ_denP_det den₁ den₂
        rw [Option.get_of_eq_some pf₂ den₁, Option.get_of_eq_some pf₃ den₂] at typ_denP_det
        dsimp at typ_denP_det
        subst τ₂

        rw [denote_term_abstract_go_eq_term_abstract (vs_nodup := wf_t.2.2.1) (vs_nemp := vs_nemp) (pf := updates_isSome_fv_P)] at den₁ den₂

        obtain rfl := denote_welltyped_eq
          ⟨TypeContext.abstract (vs.zipToAList αs ∪ Γ) («Δ» := (Function.updates «Δ» vs (List.ofFn fun i => some (x i)))),
          WFTC.of_abstract, _,
          Typing.of_abstract updates_isSome_fv_P typ_P⟩
          den₁

        apply P_ih updates_isSome_fv_P wf_t.2.1 typ_P at den₁
        apply P_ih updates_isSome_fv_P wf_t.2.1 typ_P at den₂

        rw [←denote_term_abstract_go_eq_term_abstract (vs_nodup := wf_t.2.2.1) (vs_nemp := vs_nemp) (pf := updates_isSome_fv_simp_P)] at den₁ den₂

        generalize_proofs pf₁ pf₂ pf₃ at typ_ne den₁ den₂
        rw [Option.get_of_eq_some pf₂ den₁, Option.get_of_eq_some pf₃ den₂] at typ_ne

        nomatch typ_ne
      · push_neg at den_simpP_isSome
        obtain ⟨x, x_𝒟, den_isNone⟩ := den_simpP_isSome
        rw [ne_eq, Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none,
          denote_term_abstract_go_eq_term_abstract (vs_nodup := wf_t.2.2.1) (vs_nemp := vs_nemp) (pf := updates_isSome_fv_simp_P)] at den_isNone

        specialize denP_isSome x_𝒟
        rw [denote_term_abstract_go_eq_term_abstract (vs_nodup := wf_t.2.2.1) (vs_nemp := vs_nemp) (pf := updates_isSome_fv_P)] at denP_isSome
        absurd simplifier_partial_correct' («Δ» := Function.updates «Δ» vs (List.ofFn fun i => some (x i))) updates_isSome_fv_P wf_t.2.1 typ_P den_isNone
        rwa [←ne_eq, Option.ne_none_iff_isSome]


end simplifier_correct
