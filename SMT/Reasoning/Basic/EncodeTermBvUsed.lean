import SMT.Reasoning.Basic.EncodeTermStruct

/-!
# `encodeTerm` bound-variable / `usedVars` specification

`encodeTerm_bv_used` is the structural invariant that every **bound variable** of
the encoded term lives in the final `usedVars` list, together with `usedVars`
monotonicity. It is the missing ingredient for the sound version of
`SMT.Typing.weakening`: a variable freshly generated *after* a subterm `S` was
encoded (hence `∉ usedVars` at that later point) cannot clash with any bound name
of `S`, because `bv S ⊆ usedVars`.

The proof mirrors the monadic skeleton of `encodeTerm_combined` but carries only
the two facts it needs, so each case is comparatively light: every binder of the
output is created via `freshVar`/`freshVarList` (which append to `usedVars`), and
every recursive subterm's bound variables are covered by the induction
hypothesis lifted through monotonicity.
-/

open Std.Do B SMT ZFSet
set_option mvcgen.warning false

/-- `eraseFromContext` changes neither `usedVars` nor declarations. -/
theorem SMT.eraseFromContext_used_decls {v : SMT.𝒱} {used : List SMT.𝒱}
    {decl : SMT.Chunk} :
    ⦃ fun ⟨E, _⟩ => ⌜E.usedVars = used ∧ E.declarations = decl⌝ ⦄
    SMT.eraseFromContext v
    ⦃ ⇓ _ ⟨E, _⟩ => ⌜E.usedVars = used ∧ E.declarations = decl⌝ ⦄ := by
  unfold SMT.eraseFromContext
  mintro pre ∀S
  mpure pre
  obtain ⟨rfl, rfl⟩ := pre
  mspec Std.Do.Spec.modifyGet_StateT

namespace SMT

/-- General single-substitution bound: a bound variable of `subst x e t` is either
a bound variable of `t` or of the substituted term `e`. -/
theorem bv_subst_mem_or {x : SMT.𝒱} (e : SMT.Term) :
    ∀ {t : SMT.Term} {v : SMT.𝒱}, v ∈ SMT.bv (SMT.subst x e t) → v ∈ SMT.bv t ∨ v ∈ SMT.bv e := by
  intro t
  set be := SMT.bv e with hbe
  induction t with
  | var w =>
    intro v; unfold SMT.subst; split_ifs
    · exact fun hv => Or.inr hv
    · exact fun hv => Or.inl hv
  | int _ | bool _ | none => intro v; unfold SMT.subst; exact fun hv => Or.inl hv
  | app f a ihf iha =>
    intro v hv; unfold SMT.subst at hv; unfold SMT.bv at hv ⊢
    simp only [List.mem_append] at hv ⊢
    rcases hv with hf | ha
    · rcases ihf hf with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rcases iha ha with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  | lambda vs τs body ih =>
    intro v hv; unfold SMT.subst at hv; split_ifs at hv
    · exact Or.inl hv
    · unfold SMT.bv at hv ⊢; simp only [List.mem_append] at hv ⊢
      rcases hv with hvs | hbody
      · exact Or.inl (Or.inl hvs)
      · rcases ih hbody with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
  | «forall» vs τs body ih =>
    intro v hv; unfold SMT.subst at hv; split_ifs at hv
    · exact Or.inl hv
    · unfold SMT.bv at hv ⊢; simp only [List.mem_append] at hv ⊢
      rcases hv with hvs | hbody
      · exact Or.inl (Or.inl hvs)
      · rcases ih hbody with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
  | «exists» vs τs body ih =>
    intro v hv; unfold SMT.subst at hv; split_ifs at hv
    · exact Or.inl hv
    · unfold SMT.bv at hv ⊢; simp only [List.mem_append] at hv ⊢
      rcases hv with hvs | hbody
      · exact Or.inl (Or.inl hvs)
      · rcases ih hbody with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
  | as a τ ih =>
    intro v hv; unfold SMT.subst at hv; unfold SMT.bv at hv ⊢; exact ih hv
  | eq t₁ t₂ ih₁ ih₂ =>
    intro v hv; unfold SMT.subst at hv; unfold SMT.bv at hv ⊢
    simp only [List.mem_append] at hv ⊢
    rcases hv with h1 | h2
    · rcases ih₁ h1 with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rcases ih₂ h2 with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  | and t₁ t₂ ih₁ ih₂ =>
    intro v hv; unfold SMT.subst at hv; unfold SMT.bv at hv ⊢
    simp only [List.mem_append] at hv ⊢
    rcases hv with h1 | h2
    · rcases ih₁ h1 with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rcases ih₂ h2 with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  | or t₁ t₂ ih₁ ih₂ =>
    intro v hv; unfold SMT.subst at hv; unfold SMT.bv at hv ⊢
    simp only [List.mem_append] at hv ⊢
    rcases hv with h1 | h2
    · rcases ih₁ h1 with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rcases ih₂ h2 with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  | not a ih =>
    intro v hv; unfold SMT.subst at hv; unfold SMT.bv at hv ⊢; exact ih hv
  | imp t₁ t₂ ih₁ ih₂ =>
    intro v hv; unfold SMT.subst at hv; unfold SMT.bv at hv ⊢
    simp only [List.mem_append] at hv ⊢
    rcases hv with h1 | h2
    · rcases ih₁ h1 with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rcases ih₂ h2 with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  | ite c a b ihc iha ihb =>
    intro v hv; unfold SMT.subst at hv; unfold SMT.bv at hv ⊢
    simp only [List.mem_append] at hv ⊢
    rcases hv with (hc | ha) | hb
    · rcases ihc hc with h | h
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inr h
    · rcases iha ha with h | h
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inr h
    · rcases ihb hb with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  | some a ih =>
    intro v hv; unfold SMT.subst at hv; unfold SMT.bv at hv ⊢; exact ih hv
  | the a ih =>
    intro v hv; unfold SMT.subst at hv; unfold SMT.bv at hv ⊢; exact ih hv
  | pair t₁ t₂ ih₁ ih₂ =>
    intro v hv; unfold SMT.subst at hv; unfold SMT.bv at hv ⊢
    simp only [List.mem_append] at hv ⊢
    rcases hv with h1 | h2
    · rcases ih₁ h1 with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rcases ih₂ h2 with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  | fst a ih =>
    intro v hv; unfold SMT.subst at hv; unfold SMT.bv at hv ⊢; exact ih hv
  | snd a ih =>
    intro v hv; unfold SMT.subst at hv; unfold SMT.bv at hv ⊢; exact ih hv
  | distinct ts ih =>
    intro v hv; unfold SMT.subst at hv; unfold SMT.bv at hv
    rw [List.mem_flatten] at hv
    obtain ⟨l, hl_mem, hv_l⟩ := hv
    rw [List.mem_map] at hl_mem
    obtain ⟨⟨a, ha_in_substs⟩, _, rfl⟩ := hl_mem
    rw [List.mem_map] at ha_in_substs
    obtain ⟨⟨u, hu_ts⟩, _, rfl⟩ := ha_in_substs
    rcases ih u hu_ts hv_l with h | h
    · refine Or.inl ?_
      unfold SMT.bv; rw [List.mem_flatten]
      exact ⟨SMT.bv u, List.mem_map.mpr ⟨⟨u, hu_ts⟩, List.mem_attach _ _, rfl⟩, h⟩
    · exact Or.inr h
  | le t₁ t₂ ih₁ ih₂ =>
    intro v hv; unfold SMT.subst at hv; unfold SMT.bv at hv ⊢
    simp only [List.mem_append] at hv ⊢
    rcases hv with h1 | h2
    · rcases ih₁ h1 with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rcases ih₂ h2 with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  | add t₁ t₂ ih₁ ih₂ =>
    intro v hv; unfold SMT.subst at hv; unfold SMT.bv at hv ⊢
    simp only [List.mem_append] at hv ⊢
    rcases hv with h1 | h2
    · rcases ih₁ h1 with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rcases ih₂ h2 with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  | sub t₁ t₂ ih₁ ih₂ =>
    intro v hv; unfold SMT.subst at hv; unfold SMT.bv at hv ⊢
    simp only [List.mem_append] at hv ⊢
    rcases hv with h1 | h2
    · rcases ih₁ h1 with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rcases ih₂ h2 with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  | mul t₁ t₂ ih₁ ih₂ =>
    intro v hv; unfold SMT.subst at hv; unfold SMT.bv at hv ⊢
    simp only [List.mem_append] at hv ⊢
    rcases hv with h1 | h2
    · rcases ih₁ h1 with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rcases ih₂ h2 with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h

/-- `substList` keeps bound variables within `U` provided the base term and all
substituted terms do. -/
theorem bv_substList_subset_of {xs : List SMT.𝒱} {ts : List SMT.Term} {e : SMT.Term}
    {U : List SMT.𝒱} (he : ∀ v ∈ SMT.bv e, v ∈ U) (hts : ∀ t ∈ ts, ∀ v ∈ SMT.bv t, v ∈ U) :
    ∀ v ∈ SMT.bv (SMT.substList xs ts e), v ∈ U := by
  induction xs generalizing ts e with
  | nil => cases ts <;> (unfold SMT.substList; exact he)
  | cons x xs ih =>
    cases ts with
    | nil => unfold SMT.substList; exact he
    | cons t' ts' =>
      unfold SMT.substList
      apply ih
      · intro v hv
        rcases bv_subst_mem_or t' hv with h | h
        · exact he v h
        · exact hts t' (List.mem_cons_self ..) v h
      · exact fun t ht => hts t (List.mem_cons_of_mem _ ht)

/-- Freshness companion of `bv_substList_subset_of`: a bound variable of
`substList xs ts e` avoids `a` when every bound variable of `e` and of the
substituting terms `ts` avoids `a`. -/
theorem bv_substList_notMem_of {xs : List SMT.𝒱} {ts : List SMT.Term} {e : SMT.Term}
    {a : List SMT.𝒱} (he : ∀ v ∈ SMT.bv e, v ∉ a) (hts : ∀ t ∈ ts, ∀ v ∈ SMT.bv t, v ∉ a) :
    ∀ v ∈ SMT.bv (SMT.substList xs ts e), v ∉ a := by
  induction xs generalizing ts e with
  | nil => cases ts <;> (unfold SMT.substList; exact he)
  | cons x xs ih =>
    cases ts with
    | nil => unfold SMT.substList; exact he
    | cons t' ts' =>
      unfold SMT.substList
      apply ih
      · intro v hv
        rcases bv_subst_mem_or t' hv with h | h
        · exact he v h
        · exact hts t' (List.mem_cons_self ..) v h
      · exact fun t ht => hts t (List.mem_cons_of_mem _ ht)

/-- Every term produced by `toDestPair` from a seed `t₀` with no bound variables
also has no bound variables (the destructors `.fst`/`.snd` preserve `bv = []`).
Used by `lambda`/`collect` where `substList` substitutes `toDestPair` terms, so
`substList` preserves `bv` via `SMT_bv_substList_eq`. -/
theorem bv_toDestPair_nil {vs : List SMT.𝒱} {t t₀ : SMT.Term} (ht₀ : SMT.bv t₀ = [])
    (ht : t ∈ toDestPair vs t₀) : SMT.bv t = [] := by
  have key : ∀ (vs : List SMT.𝒱) (zp : SMT.Term) (acc : List SMT.Term) (d : SMT.Term),
      SMT.bv zp = [] → (∀ a ∈ acc, SMT.bv a = []) → SMT.bv d = [] →
      ∀ u ∈ toDestPair vs zp acc d, SMT.bv u = [] := by
    intro vs'
    induction vs' with
    | nil => exact fun zp acc d _ hacc _ u hu => hacc u hu
    | cons x xs ih =>
      intro zp acc d hzp hacc hd u hu
      cases xs with
      | nil =>
        unfold toDestPair at hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact hzp
        · exact hacc u hu
      | cons y ys =>
        unfold toDestPair at hu
        exact ih (.fst d) (.snd d :: acc) (.fst d)
          (by rw [SMT.bv]; exact hd)
          (fun a ha => by
            rcases List.mem_cons.mp ha with rfl | ha
            · rw [SMT.bv]; exact hd
            · exact hacc a ha)
          (by rw [SMT.bv]; exact hd)
          u hu
  exact key vs t₀ [] t₀ ht₀ (by simp) ht₀ t ht

/-- `toPairl` of terms with no bound variables has no bound variables. Used in the
function arm of `collect` where the applied argument is `(xs.map .var).toPairl`. -/
theorem bv_toPairl_nil {ts : List SMT.Term} (ht : ∀ t ∈ ts, SMT.bv t = []) :
    SMT.bv (List.toPairl ts) = [] := by
  have aux : ∀ (l : List SMT.Term), (∀ t ∈ l, SMT.bv t = []) →
      SMT.bv (List.toPairl.aux l) = [] := by
    intro l
    induction l with
    | nil => intro _; simp [List.toPairl.aux, SMT.bv]
    | cons x xs ih =>
      cases xs with
      | nil => intro h; exact h x (List.mem_cons_self ..)
      | cons y ys =>
        intro h
        show SMT.bv (SMT.Term.pair (List.toPairl.aux (y :: ys)) x) = []
        rw [SMT.bv, ih (fun t ht => h t (List.mem_cons_of_mem _ ht)),
          h x (List.mem_cons_self ..), List.nil_append]
  unfold List.toPairl
  exact aux ts.reverse (fun t htr => ht t (List.mem_reverse.mp htr))

set_option maxHeartbeats 4000000 in
/-- `defaultSpecM` introduces bound variables only through `freshVar` (the `.fun`
case wraps in `.forall [x]` with `x` fresh), so every bound variable of its
output lives in the final `usedVars`. -/
theorem defaultSpecM_bv (τ : SMTType) :
    ∀ {used : List SMT.𝒱} {n : ℕ} {name : String} {t : SMT.Term},
    (∀ v ∈ SMT.bv t, v ∈ used) →
    ⦃ fun (⟨E, _Λ'⟩ : EncoderState) ↦ ⌜E.freshvarsc = n ∧ E.usedVars = used⌝ ⦄
    defaultSpecM name τ t
    ⦃ ⇓? (d : SMT.Term) (⟨E', _Γ'⟩ : EncoderState) =>
        ⌜(∀ v ∈ SMT.bv d, v ∈ E'.usedVars) ∧ used ⊆ E'.usedVars⌝ ⦄ := by
  induction τ with
  | int | bool =>
    intro used n name t hbvt
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl⟩ := pre
    unfold defaultSpecM
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨?_, fun v hv => hv⟩
    intro v hv
    simp only [SMT.bv, List.append_nil] at hv
    exact hbvt v hv
  | unit =>
    intro used n name t hbvt
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl⟩ := pre
    unfold defaultSpecM
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨?_, fun v hv => hv⟩
    intro v hv
    simp only [SMT.bv, List.not_mem_nil] at hv
  | option σ _ih =>
    intro used n name t hbvt
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl⟩ := pre
    unfold defaultSpecM
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨?_, fun v hv => hv⟩
    intro v hv
    simp only [noneCast, SMT.bv, List.append_nil] at hv
    exact hbvt v hv
  | pair σ ρ σ_ih ρ_ih =>
    intro used n name t hbvt
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl⟩ := pre
    unfold defaultSpecM
    have hbvt_fst : ∀ v ∈ SMT.bv (Term.fst t), v ∈ St.env.usedVars :=
      fun v hv => hbvt v (by rwa [SMT.bv] at hv)
    mspec (σ_ih hbvt_fst)
    mrename_i preF
    mintro ∀St₂
    mpure preF
    obtain ⟨hfst_bv, hfst_used_sub⟩ := preF
    have hbvt_snd : ∀ v ∈ SMT.bv (Term.snd t), v ∈ St₂.env.usedVars :=
      fun v hv => hfst_used_sub (hbvt v (by rwa [SMT.bv] at hv))
    mspec (ρ_ih hbvt_snd)
    mrename_i preS
    mintro ∀St₃
    mpure preS
    obtain ⟨hsnd_bv, hsnd_used_sub⟩ := preS
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨?_, fun v hv => hsnd_used_sub (hfst_used_sub hv)⟩
    intro v hv
    simp only [SMT.bv, List.mem_append] at hv
    rcases hv with hv | hv
    · exact hsnd_used_sub (hfst_bv v hv)
    · exact hsnd_bv v hv
  | «fun» α β _α_ih β_ih =>
    intro used n name t hbvt
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl⟩ := pre
    unfold defaultSpecM
    mspec SMT.freshVar_spec
    case post.success x =>
      mrename_i prex
      mintro ∀St₂
      mpure prex
      obtain ⟨_, x_fresh, _, St₂_used_eq, _⟩ := prex
      have hbvt_app : ∀ v ∈ SMT.bv (Term.app t (Term.var x)), v ∈ St₂.env.usedVars := fun v hv => by
        simp only [SMT.bv, List.append_nil] at hv
        rw [St₂_used_eq]; exact List.mem_cons_of_mem _ (hbvt v hv)
      mspec (β_ih hbvt_app)
      mrename_i prebody
      mintro ∀St₃
      mpure prebody
      obtain ⟨hbody_bv, hbody_used_sub⟩ := prebody
      mspec SMT.eraseFromContext_spec
      mrename_i preE
      mintro ∀StE
      mpure preE
      obtain ⟨_, _, StE_used_eq⟩ := preE
      mspec Std.Do.Spec.pure
      mpure_intro
      rw [StE_used_eq]
      refine ⟨?_, fun v hv => hbody_used_sub (by rw [St₂_used_eq]; exact List.mem_cons_of_mem _ hv)⟩
      intro v hv
      simp only [SMT.bv, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | hv
      · exact hbody_used_sub (by rw [St₂_used_eq]; exact List.mem_cons_self)
      · exact hbody_bv v hv

set_option maxHeartbeats 4000000 in
/-- Pair case of `loosenAux_prf_bv`, taking the two component bv-specs as
hypotheses (mirrors `loosenAux_prf_state_pair`). Used by both the `pair` and
`graph` cases of `loosenAux_prf_bv`. The fresh head variable `x!` and every bound
variable of the produced spec term live in the final `usedVars`. -/
theorem loosenAux_prf_bv_pair {α β α' β' : SMTType} (pα : α ~> α') (pβ : β ~> β')
    (pα_ih : ∀ {used : List SMT.𝒱} {n : ℕ} {name : String} {x : SMT.Term},
      (∀ v ∈ SMT.bv x, v ∈ used) →
      ⦃ fun (⟨E, _Λ'⟩ : EncoderState) ↦ ⌜E.freshvarsc = n ∧ E.usedVars = used⌝ ⦄
      loosenAux_prf name pα x
      ⦃ ⇓? (⟨x!, spec⟩ : 𝒱 × SMT.Term) (⟨E', _Γ'⟩ : EncoderState) =>
          ⌜x! ∈ E'.usedVars ∧ (∀ v ∈ SMT.bv spec, v ∈ E'.usedVars) ∧ used ⊆ E'.usedVars⌝ ⦄)
    (pβ_ih : ∀ {used : List SMT.𝒱} {n : ℕ} {name : String} {x : SMT.Term},
      (∀ v ∈ SMT.bv x, v ∈ used) →
      ⦃ fun (⟨E, _Λ'⟩ : EncoderState) ↦ ⌜E.freshvarsc = n ∧ E.usedVars = used⌝ ⦄
      loosenAux_prf name pβ x
      ⦃ ⇓? (⟨x!, spec⟩ : 𝒱 × SMT.Term) (⟨E', _Γ'⟩ : EncoderState) =>
          ⌜x! ∈ E'.usedVars ∧ (∀ v ∈ SMT.bv spec, v ∈ E'.usedVars) ∧ used ⊆ E'.usedVars⌝ ⦄)
    {used : List SMT.𝒱} {n : ℕ} {name : String} {x : SMT.Term}
    (hbvx : ∀ v ∈ SMT.bv x, v ∈ used) :
    ⦃ fun (⟨E, _Λ'⟩ : EncoderState) ↦ ⌜E.freshvarsc = n ∧ E.usedVars = used⌝ ⦄
    loosenAux_prf name (castPath.pair pα pβ) x
    ⦃ ⇓? (⟨x!, spec⟩ : 𝒱 × SMT.Term) (⟨E', _Γ'⟩ : EncoderState) =>
        ⌜x! ∈ E'.usedVars ∧ (∀ v ∈ SMT.bv spec, v ∈ E'.usedVars) ∧ used ⊆ E'.usedVars⌝ ⦄ := by
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl⟩ := pre
  unfold loosenAux_prf
  mspec SMT.freshVar_spec
  mrename_i prex
  mintro ∀St₂
  mpure prex
  obtain ⟨_, x!_fresh, _, St₂_used_eq, _⟩ := prex
  have hbvfst : ∀ v ∈ SMT.bv (Term.fst x), v ∈ St₂.env.usedVars :=
    fun v hv => by rw [St₂_used_eq]; exact List.mem_cons_of_mem _ (hbvx v (by rwa [SMT.bv] at hv))
  mspec (pα_ih hbvfst)
  mrename_i preF
  mintro ∀St₃
  mpure preF
  obtain ⟨fst!_used, fst!_bv, fst!_used_sub⟩ := preF
  have hbvsnd : ∀ v ∈ SMT.bv (Term.snd x), v ∈ St₃.env.usedVars :=
    fun v hv => fst!_used_sub (by rw [St₂_used_eq]; exact List.mem_cons_of_mem _ (hbvx v (by rwa [SMT.bv] at hv)))
  mspec (pβ_ih hbvsnd)
  mrename_i preS
  mintro ∀St₄
  mpure preS
  obtain ⟨snd!_used, snd!_bv, snd!_used_sub⟩ := preS
  mspec SMT.eraseFromContext_spec
  mrename_i preE
  mintro ∀StE
  mpure preE
  obtain ⟨_, _, StE_used_eq⟩ := preE
  mspec SMT.eraseFromContext_spec
  mrename_i preE2
  mintro ∀StE2
  mpure preE2
  obtain ⟨_, _, StE2_used_eq⟩ := preE2
  mspec Std.Do.Spec.pure
  mpure_intro
  rw [StE2_used_eq, StE_used_eq]
  refine ⟨?_, ?_, ?_⟩
  · exact snd!_used_sub (fst!_used_sub (by rw [St₂_used_eq]; exact List.mem_cons_self))
  · intro v hv
    simp only [SMT.bv, List.append_nil, List.nil_append, List.mem_append, List.mem_cons,
      List.not_mem_nil, false_or, or_false] at hv
    rcases hv with (rfl | rfl) | hvf | hvs
    · exact snd!_used_sub fst!_used
    · exact snd!_used
    · exact snd!_used_sub (fst!_bv v hvf)
    · exact snd!_bv v hvs
  · exact fun v hv => snd!_used_sub (fst!_used_sub
      (by rw [St₂_used_eq]; exact List.mem_cons_of_mem _ hv))

set_option maxHeartbeats 4000000 in
/-- bv/usedVars specification of `loosenAux_prf`: induction on the cast path.
Every bound variable of the produced spec, and the fresh head variable `x!`, live
in the final `usedVars` (all binders are freshly created or come from recursion). -/
theorem loosenAux_prf_bv {α β : SMTType} (c : α ~> β) :
    ∀ {used : List SMT.𝒱} {n : ℕ} {name : String} {x : SMT.Term},
    (∀ v ∈ SMT.bv x, v ∈ used) →
    ⦃ fun (⟨E, _Λ'⟩ : EncoderState) ↦ ⌜E.freshvarsc = n ∧ E.usedVars = used⌝ ⦄
    loosenAux_prf name c x
    ⦃ ⇓? (⟨x!, spec⟩ : 𝒱 × SMT.Term) (⟨E', _Γ'⟩ : EncoderState) =>
        ⌜x! ∈ E'.usedVars ∧ (∀ v ∈ SMT.bv spec, v ∈ E'.usedVars) ∧ used ⊆ E'.usedVars⌝ ⦄ := by
  induction c with
  | @refl α hα =>
    intro used n name x hbvx
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl⟩ := pre
    unfold loosenAux_prf
    mspec SMT.freshVar_spec
    mrename_i prex
    mintro ∀St₂
    mpure prex
    obtain ⟨_, x!_fresh, _, St₂_used_eq, _⟩ := prex
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨?_, ?_, ?_⟩
    · rw [St₂_used_eq]; exact List.mem_cons_self
    · intro v hv
      simp only [SMT.bv, List.nil_append] at hv
      rw [St₂_used_eq]; exact List.mem_cons_of_mem _ (hbvx v hv)
    · rw [St₂_used_eq]; intro v hv; exact List.mem_cons_of_mem _ hv
  | @chpred α α' p ih =>
    intro used n name x hbvx
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl⟩ := pre
    unfold loosenAux_prf
    mspec SMT.freshVar_spec
    mrename_i prex
    mintro ∀St₂
    mpure prex
    obtain ⟨_, x!_fresh, _, St₂_used_eq, _⟩ := prex
    mspec SMT.freshVar_spec
    mrename_i prez
    mintro ∀St₃
    mpure prez
    obtain ⟨_, z_fresh, _, St₃_used_eq, _⟩ := prez
    mspec (ih (by intro v hv; simp only [SMT.bv, List.not_mem_nil] at hv))
    mrename_i prez!
    mintro ∀St₄
    mpure prez!
    obtain ⟨z!_used, z!_bv, z!_used_sub⟩ := prez!
    mspec SMT.eraseFromContext_spec
    mrename_i preE
    mintro ∀StE
    mpure preE
    obtain ⟨_, _, StE_used_eq⟩ := preE
    mspec SMT.eraseFromContext_spec
    mrename_i preE2
    mintro ∀StE2
    mpure preE2
    obtain ⟨_, _, StE2_used_eq⟩ := preE2
    mspec Std.Do.Spec.pure
    mpure_intro
    rw [StE2_used_eq, StE_used_eq]
    refine ⟨?_, ?_, ?_⟩
    · apply z!_used_sub; rw [St₃_used_eq, St₂_used_eq]
      exact List.mem_cons_of_mem _ List.mem_cons_self
    · intro v hv
      simp only [SMT.bv, List.nil_append, List.append_nil, List.mem_append, List.mem_cons,
        List.not_mem_nil, false_or, or_false] at hv
      rcases hv with rfl | rfl | hvx | hvspec
      · exact z!_used
      · apply z!_used_sub; rw [St₃_used_eq]; exact List.mem_cons_self
      · apply z!_used_sub; rw [St₃_used_eq, St₂_used_eq]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hbvx v hvx))
      · exact z!_bv v hvspec
    · intro v hv
      apply z!_used_sub; rw [St₃_used_eq, St₂_used_eq]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hv)
  | @graph α β α' β' pα pβ pα_ih pβ_ih =>
    intro used n name x hbvx
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl⟩ := pre
    unfold loosenAux_prf
    mspec SMT.freshVar_spec
    mrename_i prex
    mintro ∀St₂
    mpure prex
    obtain ⟨_, x!_fresh, _, St₂_used_eq, _⟩ := prex
    mspec SMT.freshVar_spec
    mrename_i prez
    mintro ∀St₃
    mpure prez
    obtain ⟨_, z_fresh, _, St₃_used_eq, _⟩ := prez
    mspec (loosenAux_prf_bv_pair pα pβ pα_ih pβ_ih
      (by intro v hv; simp only [SMT.bv, List.not_mem_nil] at hv))
    mrename_i prez!
    mintro ∀St₄
    mpure prez!
    obtain ⟨z!_used, z!_bv, z!_used_sub⟩ := prez!
    mspec SMT.eraseFromContext_spec
    mrename_i preE
    mintro ∀StE
    mpure preE
    obtain ⟨_, _, StE_used_eq⟩ := preE
    mspec SMT.eraseFromContext_spec
    mrename_i preE2
    mintro ∀StE2
    mpure preE2
    obtain ⟨_, _, StE2_used_eq⟩ := preE2
    mspec Std.Do.Spec.pure
    mpure_intro
    rw [StE2_used_eq, StE_used_eq]
    refine ⟨?_, ?_, ?_⟩
    · apply z!_used_sub; rw [St₃_used_eq, St₂_used_eq]
      exact List.mem_cons_of_mem _ List.mem_cons_self
    · intro v hv
      simp only [SMT.bv, List.nil_append, List.append_nil, List.mem_append, List.mem_cons,
        List.not_mem_nil, false_or, or_false] at hv
      rcases hv with rfl | rfl | hvx | hvspec
      · exact z!_used
      · apply z!_used_sub; rw [St₃_used_eq]; exact List.mem_cons_self
      · apply z!_used_sub; rw [St₃_used_eq, St₂_used_eq]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hbvx v hvx))
      · exact z!_bv v hvspec
    · intro v hv
      apply z!_used_sub; rw [St₃_used_eq, St₂_used_eq]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hv)
  | @pair α β α' β' pα pβ pα_ih pβ_ih =>
    intro used n name x hbvx
    exact loosenAux_prf_bv_pair pα pβ pα_ih pβ_ih hbvx
  | @opt α α' p ih =>
    intro used n name x hbvx
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl⟩ := pre
    unfold loosenAux_prf
    mspec SMT.freshVar_spec
    mrename_i prex
    mintro ∀St₂
    mpure prex
    obtain ⟨_, x!_fresh, _, St₂_used_eq, _⟩ := prex
    split
    · rename_i x!
      mspec Std.Do.Spec.pure
      mpure_intro
      refine ⟨?_, ?_, ?_⟩
      · rw [St₂_used_eq]; exact List.mem_cons_self
      · intro v hv
        simp only [noneCast, SMT.bv, List.append_nil, List.not_mem_nil] at hv
      · rw [St₂_used_eq]; intro v hv; exact List.mem_cons_of_mem _ hv
    · rename_i x! x₀
      mspec (ih (used := St₂.env.usedVars)
        (by intro v hv; rw [St₂_used_eq]
            exact List.mem_cons_of_mem _ (hbvx v (by rw [SMT.bv]; exact hv))))
      mrename_i prew
      mintro ∀St₃
      mpure prew
      obtain ⟨w!_used, w!_bv, w!_used_sub⟩ := prew
      mspec SMT.eraseFromContext_spec
      mrename_i preE
      mintro ∀StE
      mpure preE
      obtain ⟨_, _, StE_used_eq⟩ := preE
      mspec Std.Do.Spec.pure
      mpure_intro
      rw [StE_used_eq]
      refine ⟨?_, ?_, ?_⟩
      · apply w!_used_sub; rw [St₂_used_eq]; exact List.mem_cons_self
      · intro v hv
        simp only [SMT.bv, List.nil_append, List.append_nil, List.mem_append, List.mem_cons,
          List.not_mem_nil, false_or, or_false] at hv
        rcases hv with rfl | hvspec
        · exact w!_used
        · exact w!_bv v hvspec
      · intro v hv; apply w!_used_sub; rw [St₂_used_eq]; exact List.mem_cons_of_mem _ hv
    · rename_i x! x_ne_none x_ne_some
      mspec (ih (used := St₂.env.usedVars)
        (by intro v hv; rw [SMT.bv] at hv; rw [St₂_used_eq]
            exact List.mem_cons_of_mem _ (hbvx v hv)))
      mrename_i prew
      mintro ∀St₃
      mpure prew
      obtain ⟨w!_used, w!_bv, w!_used_sub⟩ := prew
      mspec SMT.eraseFromContext_spec
      mrename_i preE
      mintro ∀StE
      mpure preE
      obtain ⟨_, _, StE_used_eq⟩ := preE
      mspec Std.Do.Spec.pure
      mpure_intro
      rw [StE_used_eq]
      refine ⟨?_, ?_, ?_⟩
      · apply w!_used_sub; rw [St₂_used_eq]; exact List.mem_cons_self
      · intro v hv
        simp only [noneCast, SMT.bv, List.nil_append, List.append_nil, List.mem_append,
          List.mem_cons, List.not_mem_nil, false_or, or_false] at hv
        rcases hv with hvx | rfl | hvspec
        · apply w!_used_sub; rw [St₂_used_eq]; exact List.mem_cons_of_mem _ (hbvx v hvx)
        · exact w!_used
        · exact w!_bv v hvspec
      · intro v hv; apply w!_used_sub; rw [St₂_used_eq]; exact List.mem_cons_of_mem _ hv
  | @«fun» α β α' β' hβ pα pβ pα_ih pβ_ih =>
    intro used n name x hbvx
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl⟩ := pre
    unfold loosenAux_prf
    mspec SMT.freshVar_spec
    mrename_i prex
    mintro ∀St₂
    mpure prex
    obtain ⟨_, x!_fresh, _, St₂_used_eq, _⟩ := prex
    mspec SMT.freshVar_spec
    mrename_i prea
    mintro ∀St₃
    mpure prea
    obtain ⟨_, a_fresh, _, St₃_used_eq, _⟩ := prea
    mspec (pα_ih (used := St₃.env.usedVars)
      (by intro v hv; simp only [SMT.bv, List.not_mem_nil] at hv))
    mrename_i prea!
    mintro ∀St₄
    mpure prea!
    obtain ⟨a!_used, a!_bv, a!_used_sub⟩ := prea!
    mspec SMT.freshVar_spec
    mrename_i preb
    mintro ∀St₅
    mpure preb
    obtain ⟨_, b_fresh, _, St₅_used_eq, _⟩ := preb
    mspec (pβ_ih (used := St₅.env.usedVars)
      (by intro v hv; simp only [SMT.bv, List.not_mem_nil] at hv))
    mrename_i preb!
    mintro ∀St₆
    mpure preb!
    obtain ⟨b!_used, b!_bv, b!_used_sub⟩ := preb!
    mspec (defaultSpecM_bv β' (used := St₆.env.usedVars)
      (by intro v hv; simp only [SMT.bv, List.append_nil, List.not_mem_nil] at hv))
    mrename_i pred
    mintro ∀St₇
    mpure pred
    obtain ⟨hd_bv, hd_used_sub⟩ := pred
    mspec SMT.eraseFromContext_spec
    mrename_i preE
    mintro ∀StE
    mpure preE
    obtain ⟨_, _, StE_used_eq⟩ := preE
    mspec SMT.eraseFromContext_spec
    mrename_i preE2
    mintro ∀StE2
    mpure preE2
    obtain ⟨_, _, StE2_used_eq⟩ := preE2
    mspec SMT.eraseFromContext_spec
    mrename_i preE3
    mintro ∀StE3
    mpure preE3
    obtain ⟨_, _, StE3_used_eq⟩ := preE3
    mspec SMT.eraseFromContext_spec
    mrename_i preE4
    mintro ∀StE4
    mpure preE4
    obtain ⟨_, _, StE4_used_eq⟩ := preE4
    mspec Std.Do.Spec.pure
    mpure_intro
    rw [StE4_used_eq, StE3_used_eq, StE2_used_eq, StE_used_eq]
    have lift4 : ∀ {v}, v ∈ St₄.env.usedVars → v ∈ St₇.env.usedVars := fun {v} h =>
      hd_used_sub (b!_used_sub (by rw [St₅_used_eq]; exact List.mem_cons_of_mem _ h))
    have lift2 : ∀ {v}, v ∈ St₂.env.usedVars → v ∈ St₇.env.usedVars := fun {v} h =>
      lift4 (a!_used_sub (by rw [St₃_used_eq]; exact List.mem_cons_of_mem _ h))
    refine ⟨lift2 (by rw [St₂_used_eq]; exact List.mem_cons_self), ?_,
      fun v hv => lift2 (by rw [St₂_used_eq]; exact List.mem_cons_of_mem _ hv)⟩
    intro v hv
    simp only [SMT.bv, List.append_nil, List.nil_append, List.mem_append, List.mem_cons,
      List.not_mem_nil, false_or, or_false] at hv
    rcases hv with rfl | ((rfl | ha!spec) | (rfl | ((rfl | rfl) | (hx | (ha!spec2 | hb!spec))))) | hhd
    · exact lift4 a!_used
    · exact lift4 (a!_used_sub (by rw [St₃_used_eq]; exact List.mem_cons_self))
    · exact lift4 (a!_bv v ha!spec)
    · exact hd_used_sub b!_used
    · exact lift4 (a!_used_sub (by rw [St₃_used_eq]; exact List.mem_cons_self))
    · exact hd_used_sub (b!_used_sub (by rw [St₅_used_eq]; exact List.mem_cons_self))
    · exact lift2 (by rw [St₂_used_eq]; exact List.mem_cons_of_mem _ (hbvx v hx))
    · exact lift4 (a!_bv v ha!spec2)
    · exact hd_used_sub (b!_bv v hb!spec)
    · exact hd_bv v hhd

set_option maxHeartbeats 4000000 in
/-- bv/usedVars spec of `castEq`. The output equality's bound variables come from
the loosened spec (via `loosenAux_prf_bv`) plus the inputs `A`, `B`. -/
theorem castEq_bv (A B : SMT.Term) (σA σB : SMTType) {used : List SMT.𝒱} {n : ℕ}
    (hbvA : ∀ v ∈ SMT.bv A, v ∈ used) (hbvB : ∀ v ∈ SMT.bv B, v ∈ used) :
    ⦃ fun (⟨E, _Λ'⟩ : EncoderState) ↦ ⌜E.freshvarsc = n ∧ E.usedVars = used⌝ ⦄
    castEq (A, σA) (B, σB)
    ⦃ ⇓? (⟨t', _σ⟩ : SMT.Term × SMTType) (⟨E', _Γ'⟩ : EncoderState) =>
        ⌜(∀ v ∈ SMT.bv t', v ∈ E'.usedVars) ∧ used ⊆ E'.usedVars⌝ ⦄ := by
  unfold castEq
  mvcgen
  · rename_i hpre
    obtain ⟨rfl, rfl⟩ := hpre
    refine ⟨?_, fun v hv => hv⟩
    intro v hv
    simp only [SMT.bv, List.mem_append] at hv
    rcases hv with hv | hv
    · exact hbvA v hv
    · exact hbvB v hv
  · rename_i hpre
    obtain ⟨rfl, rfl⟩ := hpre
    mspec (loosenAux_prf_bv _ hbvA)
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨A!_used, A!_bv, A!_used_sub⟩ := pre
    mspec SMT.declareConst_addSpec_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, _, hd_used, _⟩ := pred
    mspec Std.Do.Spec.pure
    mpure_intro
    rw [hd_used]
    refine ⟨?_, A!_used_sub⟩
    intro v hv
    simp only [SMT.bv, List.nil_append, List.append_nil, List.mem_append,
      List.not_mem_nil, false_or, or_false] at hv
    rcases hv with hvB | hvspec
    · exact A!_used_sub (hbvB v hvB)
    · exact A!_bv v hvspec
  · rename_i hpre
    obtain ⟨rfl, rfl⟩ := hpre
    mspec (loosenAux_prf_bv _ hbvB)
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨B!_used, B!_bv, B!_used_sub⟩ := pre
    mspec SMT.declareConst_addSpec_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, _, hd_used, _⟩ := pred
    mspec Std.Do.Spec.pure
    mpure_intro
    rw [hd_used]
    refine ⟨?_, B!_used_sub⟩
    intro v hv
    simp only [SMT.bv, List.nil_append, List.append_nil, List.mem_append,
      List.not_mem_nil, false_or, or_false] at hv
    rcases hv with hvA | hvspec
    · exact B!_used_sub (hbvA v hvA)
    · exact B!_bv v hvspec

set_option maxHeartbeats 4000000 in
/-- bv/usedVars spec of `castApp`. The output term embeds only `.var`-headed
helpers and the inputs `f`/`x` (loosen specs go to `addSpec`, not the term), so
`SMT.bv` of the result is `bv f`, `bv x`, or `[]`. -/
theorem castApp_bv (f x : SMT.Term) (sf sx : SMTType) {used : List SMT.𝒱} {n : ℕ}
    (hbvf : ∀ v ∈ SMT.bv f, v ∈ used) (hbvx : ∀ v ∈ SMT.bv x, v ∈ used) :
    ⦃ fun (⟨E, _Λ'⟩ : EncoderState) ↦ ⌜E.freshvarsc = n ∧ E.usedVars = used⌝ ⦄
    castApp (f, sf) (x, sx)
    ⦃ ⇓? (⟨t', _σ⟩ : SMT.Term × SMTType) (⟨E', _Γ'⟩ : EncoderState) =>
        ⌜(∀ v ∈ SMT.bv t', v ∈ E'.usedVars) ∧ used ⊆ E'.usedVars⌝ ⦄ := by
  unfold castApp
  mvcgen
  case vc3.h_2.isTrue =>
    rename_i hxeq hfeq _ St hpre
    obtain ⟨rfl, rfl⟩ := hpre
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hxeq
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hfeq
    mspec (loosenAux_prf_bv _ hbvf)
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨L_used, L_bv, L_used_sub⟩ := pre
    unfold SMT.declareConstWithSpec
    mspec Std.Do.Spec.bind
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, _, hd_used, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨_, _, _, hs_used, _⟩ := pres
    mspec Std.Do.Spec.pure
    mpure_intro
    rw [hs_used, hd_used]
    refine ⟨?_, L_used_sub⟩
    intro v hv
    simp only [SMT.bv, List.nil_append, List.append_nil, List.mem_append,
      List.not_mem_nil, false_or, or_false] at hv
    exact L_used_sub (hbvx v hv)
  case vc4.h_2.isFalse.isTrue =>
    rename_i hxeq hfeq _ _ St hpre
    obtain ⟨rfl, rfl⟩ := hpre
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hxeq
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hfeq
    mspec (loosenAux_prf_bv _ hbvx)
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨L_used, L_bv, L_used_sub⟩ := pre
    unfold SMT.declareConstWithSpec
    mspec Std.Do.Spec.bind
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, _, hd_used, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨_, _, _, hs_used, _⟩ := pres
    mspec Std.Do.Spec.pure
    mpure_intro
    rw [hs_used, hd_used]
    refine ⟨?_, L_used_sub⟩
    intro v hv
    simp only [SMT.bv, List.nil_append, List.append_nil, List.mem_append,
      List.not_mem_nil, false_or, or_false] at hv
    exact L_used_sub (hbvf v hv)
  case vc5.h_3.isTrue =>
    rename_i hxeq hfeq _ St hpre
    obtain ⟨rfl, rfl⟩ := hpre
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hxeq
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hfeq
    mspec (loosenAux_prf_bv _ hbvf)
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨L_used, L_bv, L_used_sub⟩ := pre
    unfold SMT.declareConstWithSpec
    mspec Std.Do.Spec.bind
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, _, hd_used, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨_, _, _, hs_used, _⟩ := pres
    mspec Std.Do.Spec.pure
    mpure_intro
    rw [hs_used, hd_used]
    refine ⟨?_, L_used_sub⟩
    intro v hv
    simp only [SMT.bv, List.nil_append, List.append_nil, List.mem_append,
      List.not_mem_nil, false_or, or_false] at hv
    exact L_used_sub (hbvx v hv)
  case vc6.h_3.isFalse.isTrue =>
    rename_i hxeq hfeq _ _ St hpre
    obtain ⟨rfl, rfl⟩ := hpre
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hxeq
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hfeq
    mspec (loosenAux_prf_bv _ hbvx)
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨L_used, L_bv, L_used_sub⟩ := pre
    unfold SMT.declareConstWithSpec
    mspec Std.Do.Spec.bind
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, _, hd_used, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨_, _, _, hs_used, _⟩ := pres
    mspec Std.Do.Spec.pure
    mpure_intro
    rw [hs_used, hd_used]
    refine ⟨?_, L_used_sub⟩
    intro v hv
    simp only [SMT.bv, List.nil_append, List.append_nil, List.mem_append,
      List.not_mem_nil, false_or, or_false] at hv
    exact L_used_sub (hbvf v hv)
  case vc1.h_1.isTrue =>
    rename_i hxeq hfeq _ St hpre
    obtain ⟨rfl, rfl⟩ := hpre
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hxeq
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hfeq
    mspec (loosenAux_prf_bv _ hbvf)
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨L_used, L_bv, L_used_sub⟩ := pre
    unfold SMT.declareConstWithSpec
    mspec Std.Do.Spec.bind
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, _, hd_used, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨_, _, _, hs_used, _⟩ := pres
    mspec SMT.freshVar_spec
    mrename_i pre2
    mintro ∀St₂
    mpure pre2
    obtain ⟨_, _, _, St₂_used_eq, _⟩ := pre2
    mspec SMT.declareConst_spec
    mrename_i pred2
    mintro ∀St₂d
    mpure pred2
    obtain ⟨_, _, _, hd2_used, _⟩ := pred2
    mspec SMT.freshVar_spec
    mrename_i pre3
    mintro ∀St₃
    mpure pre3
    obtain ⟨_, _, _, St₃_used_eq, _⟩ := pre3
    mspec SMT.freshVar_spec
    mrename_i pre4
    mintro ∀St₄
    mpure pre4
    obtain ⟨_, _, _, St₄_used_eq, _⟩ := pre4
    mspec SMT.eraseFromContext_spec (Γ := St₄.types)
    mrename_i pre5
    mintro ∀St5
    mpure pre5
    obtain ⟨_, _, St5_used_eq⟩ := pre5
    mspec SMT.eraseFromContext_spec (Γ := St5.types)
    mrename_i pre6
    mintro ∀St6
    mpure pre6
    obtain ⟨_, _, St6_used_eq⟩ := pre6
    mspec SMT.addSpec_spec
    mrename_i pres2
    mintro ∀St6s
    mpure pres2
    obtain ⟨_, _, _, hs2_used, _⟩ := pres2
    mspec Std.Do.Spec.pure
    mpure_intro
    have lift : ∀ {w}, w ∈ St₁.env.usedVars → w ∈ St6s.env.usedVars := fun {w} h => by
      rw [hs2_used, St6_used_eq, St5_used_eq, St₄_used_eq, St₃_used_eq, hd2_used,
        St₂_used_eq, hs_used, hd_used]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
    refine ⟨?_, fun w hw => lift (L_used_sub hw)⟩
    intro v hv
    simp only [SMT.bv, List.nil_append, List.append_nil, List.mem_append,
      List.not_mem_nil, false_or, or_false] at hv
    exact lift (L_used_sub (hbvx v hv))
  case vc2.h_1.isFalse.isTrue =>
    rename_i hxeq hfeq _ _ St hpre
    obtain ⟨rfl, rfl⟩ := hpre
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hxeq
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hfeq
    mspec (loosenAux_prf_bv _ hbvx)
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨L_used, L_bv, L_used_sub⟩ := pre
    unfold SMT.declareConstWithSpec
    mspec Std.Do.Spec.bind
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, _, hd_used, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨_, _, _, hs_used, _⟩ := pres
    mspec SMT.freshVar_spec
    mrename_i pre2
    mintro ∀St₂
    mpure pre2
    obtain ⟨_, _, _, St₂_used_eq, _⟩ := pre2
    mspec SMT.declareConst_spec
    mrename_i pred2
    mintro ∀St₂d
    mpure pred2
    obtain ⟨_, _, _, hd2_used, _⟩ := pred2
    mspec SMT.freshVar_spec
    mrename_i pre3
    mintro ∀St₃
    mpure pre3
    obtain ⟨_, _, _, St₃_used_eq, _⟩ := pre3
    mspec SMT.freshVar_spec
    mrename_i pre4
    mintro ∀St₄
    mpure pre4
    obtain ⟨_, _, _, St₄_used_eq, _⟩ := pre4
    mspec SMT.eraseFromContext_spec (Γ := St₄.types)
    mrename_i pre5
    mintro ∀St5
    mpure pre5
    obtain ⟨_, _, St5_used_eq⟩ := pre5
    mspec SMT.eraseFromContext_spec (Γ := St5.types)
    mrename_i pre6
    mintro ∀St6
    mpure pre6
    obtain ⟨_, _, St6_used_eq⟩ := pre6
    mspec SMT.addSpec_spec
    mrename_i pres2
    mintro ∀St6s
    mpure pres2
    obtain ⟨_, _, _, hs2_used, _⟩ := pres2
    mspec Std.Do.Spec.pure
    mpure_intro
    have lift : ∀ {w}, w ∈ St₁.env.usedVars → w ∈ St6s.env.usedVars := fun {w} h => by
      rw [hs2_used, St6_used_eq, St5_used_eq, St₄_used_eq, St₃_used_eq, hd2_used,
        St₂_used_eq, hs_used, hd_used]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
    refine ⟨?_, fun w hw => lift (L_used_sub hw)⟩
    intro v hv
    simp only [SMT.bv, List.nil_append, List.append_nil, List.mem_append,
      List.not_mem_nil, false_or, or_false] at hv
set_option maxHeartbeats 4000000 in
/-- bv/usedVars spec of `castMembership`. Unlike `castApp`, the loosen spec is
embedded in the result term (via `∧ˢ`), so the result's bound variables include
those of the loosen spec (`loosenAux_prf_bv`'s `bv` clause) plus the inputs. -/
theorem castMembership_bv (x S : SMT.Term) (sx sS : SMTType) {used : List SMT.𝒱} {n : ℕ}
    (hbvx : ∀ v ∈ SMT.bv x, v ∈ used) (hbvS : ∀ v ∈ SMT.bv S, v ∈ used) :
    ⦃ fun (⟨E, _Λ'⟩ : EncoderState) ↦ ⌜E.freshvarsc = n ∧ E.usedVars = used⌝ ⦄
    castMembership (x, sx) (S, sS)
    ⦃ ⇓? (⟨t', _σ⟩ : SMT.Term × SMTType) (⟨E', _Γ'⟩ : EncoderState) =>
        ⌜(∀ v ∈ SMT.bv t', v ∈ E'.usedVars) ∧ used ⊆ E'.usedVars⌝ ⦄ := by
  unfold castMembership
  mvcgen
  case vc1.h_1.isTrue =>
    rename_i α' hσS hσx St hpre
    obtain ⟨rfl, rfl⟩ := hpre
    refine ⟨?_, fun v hv => hv⟩
    intro v hv
    simp only [SMT.bv, List.append_nil, List.mem_append] at hv
    rcases hv with hvS | hvx
    · exact hbvS v hvS
    · exact hbvx v hvx
  case vc2.h_1.isFalse.isTrue =>
    rename_i α' hσS hσx_ne hσx_le St hpre
    obtain ⟨rfl, rfl⟩ := hpre
    mspec (loosenAux_prf_bv _ hbvx)
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨L_used, L_bv, L_used_sub⟩ := pre
    mspec SMT.declareConst_addSpec_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, _, hd_used, _⟩ := pred
    mspec Std.Do.Spec.pure
    mpure_intro
    rw [hd_used]
    refine ⟨?_, L_used_sub⟩
    intro v hv
    simp only [SMT.bv, List.nil_append, List.append_nil, List.mem_append,
      List.not_mem_nil, false_or, or_false] at hv
    rcases hv with hspec | hvS
    · exact L_bv v hspec
    · exact L_used_sub (hbvS v hvS)
  case vc3.h_1.isFalse.isFalse.isTrue =>
    rename_i α' hσS hσx_ne hσx_nle hα'_le St hpre
    obtain ⟨rfl, rfl⟩ := hpre
    mspec (loosenAux_prf_bv _ hbvS)
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨L_used, L_bv, L_used_sub⟩ := pre
    mspec SMT.declareConst_addSpec_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, _, hd_used, _⟩ := pred
    mspec Std.Do.Spec.pure
    mpure_intro
    rw [hd_used]
    refine ⟨?_, L_used_sub⟩
    intro v hv
    simp only [SMT.bv, List.nil_append, List.append_nil, List.mem_append,
      List.not_mem_nil, false_or, or_false, or_self] at hv
    rcases hv with hspec | hvx
    · exact L_bv v hspec
    · exact L_used_sub (hbvx v hvx)
  case vc4.h_2.h_1.isTrue.isTrue =>
    rename_i α' β' hσS α β hσx hα_le hβ_le St hpre
    obtain ⟨rfl, rfl⟩ := hpre
    mspec (loosenAux_prf_bv _ hbvx)
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨L_used, L_bv, L_used_sub⟩ := pre
    mspec SMT.declareConst_addSpec_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, _, hd_used, _⟩ := pred
    mspec Std.Do.Spec.pure
    mpure_intro
    rw [hd_used]
    refine ⟨?_, L_used_sub⟩
    intro v hv
    simp only [SMT.bv, List.nil_append, List.append_nil, List.mem_append,
      List.not_mem_nil, false_or, or_false] at hv
    rcases hv with hspec | hvS
    · exact L_bv v hspec
    · exact L_used_sub (hbvS v hvS)
  case vc5.h_2.h_1.isTrue.isFalse.isTrue =>
    rename_i α' β' hσS α β hσx hα_le hβ_nle hβ'_le St hpre
    obtain ⟨rfl, rfl⟩ := hpre
    mspec (loosenAux_prf_bv _ (by intro v hv; exact hbvx v (by rwa [SMT.bv] at hv)))
    mrename_i preX
    mintro ∀St₁
    mpure preX
    obtain ⟨x!_used, x!_bv, x!_used_sub⟩ := preX
    mspec SMT.declareConst_addSpec_spec
    mrename_i predX
    mintro ∀St₁d
    mpure predX
    obtain ⟨_, _, _, hdX_used, _⟩ := predX
    mspec (loosenAux_prf_bv _ (used := St₁d.env.usedVars)
      (by intro v hv; rw [hdX_used]; exact x!_used_sub (hbvS v hv)))
    mrename_i preS
    mintro ∀St₂
    mpure preS
    obtain ⟨S!_used, S!_bv, S!_used_sub⟩ := preS
    mspec SMT.declareConst_addSpec_spec
    mrename_i predS
    mintro ∀St₂d
    mpure predS
    obtain ⟨_, _, _, hdS_used, _⟩ := predS
    mspec Std.Do.Spec.pure
    mpure_intro
    rw [hdS_used]
    have lift1 : ∀ {w}, w ∈ St₁.env.usedVars → w ∈ St₂.env.usedVars :=
      fun {w} h => S!_used_sub (by rw [hdX_used]; exact h)
    refine ⟨?_, fun v hv => lift1 (x!_used_sub hv)⟩
    intro v hv
    simp only [SMT.bv, List.nil_append, List.append_nil, List.mem_append,
      List.not_mem_nil, false_or, or_false] at hv
    rcases hv with (hspecX | hspecS) | hvx
    · exact lift1 (x!_bv v hspecX)
    · exact S!_bv v hspecS
    · exact lift1 (x!_used_sub (hbvx v hvx))
  case vc6.h_2.h_1.isFalse.isTrue.isTrue =>
    rename_i α' β' hσS α β hσx hα_nle hα'_le hβ_le St hpre
    obtain ⟨rfl, rfl⟩ := hpre
    mspec (loosenAux_prf_bv _ (by intro v hv; exact hbvx v (by rwa [SMT.bv] at hv)))
    mrename_i preY
    mintro ∀St₁
    mpure preY
    obtain ⟨y!_used, y!_bv, y!_used_sub⟩ := preY
    mspec SMT.declareConst_addSpec_spec
    mrename_i predY
    mintro ∀St₁d
    mpure predY
    obtain ⟨_, _, _, hdY_used, _⟩ := predY
    mspec (loosenAux_prf_bv _ (used := St₁d.env.usedVars)
      (by intro v hv; rw [hdY_used]; exact y!_used_sub (hbvS v hv)))
    mrename_i preS
    mintro ∀St₂
    mpure preS
    obtain ⟨S!_used, S!_bv, S!_used_sub⟩ := preS
    mspec SMT.declareConst_addSpec_spec
    mrename_i predS
    mintro ∀St₂d
    mpure predS
    obtain ⟨_, _, _, hdS_used, _⟩ := predS
    mspec Std.Do.Spec.pure
    mpure_intro
    rw [hdS_used]
    have lift1 : ∀ {w}, w ∈ St₁.env.usedVars → w ∈ St₂.env.usedVars :=
      fun {w} h => S!_used_sub (by rw [hdY_used]; exact h)
    refine ⟨?_, fun v hv => lift1 (y!_used_sub hv)⟩
    intro v hv
    simp only [SMT.bv, List.nil_append, List.append_nil, List.mem_append,
      List.not_mem_nil, false_or, or_false] at hv
    rcases hv with (hspecY | hspecS) | hvx
    · exact lift1 (y!_bv v hspecY)
    · exact S!_bv v hspecS
    · exact lift1 (y!_used_sub (hbvx v hvx))
  case vc7.h_2.h_1.isFalse.isTrue.isFalse.isTrue =>
    rename_i α' β' hσS α β hσx hα_nle hα'_le hβ_nle hβ'_le St hpre
    obtain ⟨rfl, rfl⟩ := hpre
    mspec (loosenAux_prf_bv _ hbvS)
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨L_used, L_bv, L_used_sub⟩ := pre
    mspec SMT.declareConst_addSpec_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, _, hd_used, _⟩ := pred
    mspec Std.Do.Spec.pure
    mpure_intro
    rw [hd_used]
    refine ⟨?_, L_used_sub⟩
    intro v hv
    simp only [SMT.bv, List.nil_append, List.append_nil, List.mem_append,
      List.not_mem_nil, false_or, or_false, or_self] at hv
    rcases hv with hspec | hvx
    · exact L_bv v hspec
    · exact L_used_sub (hbvx v hvx)

set_option maxHeartbeats 4000000 in
/-- bv/usedVars spec of `castUnionAux`. Each non-throw branch loosens `S` (spec to
`addSpec`, head var free) and builds `λ x. S!(x) ∨ T(x)`, so the result's bound
variables are the fresh binder plus `bv T`. -/
theorem castUnionAux_bv {α β : SMTType} (c : α ~> β) (S T : SMT.Term) {used : List SMT.𝒱} {n : ℕ}
    (hbvS : ∀ v ∈ SMT.bv S, v ∈ used) (hbvT : ∀ v ∈ SMT.bv T, v ∈ used) :
    ⦃ fun (⟨E, _Λ'⟩ : EncoderState) ↦ ⌜E.freshvarsc = n ∧ E.usedVars = used⌝ ⦄
    castUnionAux S T c
    ⦃ ⇓? (⟨t', _σ⟩ : SMT.Term × SMTType) (⟨E', _Γ'⟩ : EncoderState) =>
        ⌜(∀ v ∈ SMT.bv t', v ∈ E'.usedVars) ∧ used ⊆ E'.usedVars⌝ ⦄ := by
  cases c with
  | @graph α β α' β' c_α c_β =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl⟩ := pre
    unfold castUnionAux castUnion.graph
    mspec (loosenAux_prf_bv _ hbvS)
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨S!_used, S!_bv, S!_used_sub⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, _, hd_used, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨_, _, _, hs_used, _⟩ := pres
    mspec SMT.freshVar_spec
    case post.success x =>
      mrename_i pre2
      mintro ∀St₂
      mpure pre2
      obtain ⟨_, _, _, St₂_used_eq, _⟩ := pre2
      mspec SMT.eraseFromContext_spec (v := x)
        (Γ := St₂.types) (n := St₂.env.freshvarsc)
        (used := St₂.env.usedVars)
      mrename_i pre3
      mintro ∀St₃
      mpure pre3
      obtain ⟨_, _, St₃_used_eq⟩ := pre3
      mspec Std.Do.Spec.pure
      mpure_intro
      refine ⟨?_, ?_⟩
      · intro v hv
        simp only [SMT.bv, List.nil_append, List.append_nil, List.mem_append, List.mem_cons,
          List.not_mem_nil, false_or, or_false] at hv
        rcases hv with rfl | hvT
        · rw [St₃_used_eq, St₂_used_eq]; exact List.mem_cons_self
        · rw [St₃_used_eq, St₂_used_eq, hs_used, hd_used]
          exact List.mem_cons_of_mem _ (S!_used_sub (hbvT v hvT))
      · intro v hv
        rw [St₃_used_eq, St₂_used_eq, hs_used, hd_used]
        exact List.mem_cons_of_mem _ (S!_used_sub hv)
  | @«fun» α β α' β' hβ c_α c_β =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl⟩ := pre
    unfold castUnionAux castUnion.fun
    mspec (loosenAux_prf_bv _ hbvS)
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨S!_used, S!_bv, S!_used_sub⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, _, hd_used, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨_, _, _, hs_used, _⟩ := pres
    split
    · mspec SMT.freshVar_spec
      mrename_i pre2
      mintro ∀St₂
      mpure pre2
      obtain ⟨_, _, _, St₂_used_eq, _⟩ := pre2
      mspec Std.Do.Spec.pure
      mpure_intro
      refine ⟨?_, ?_⟩
      · intro v hv
        simp only [SMT.bv, List.nil_append, List.append_nil, List.mem_append, List.mem_cons,
          List.not_mem_nil, false_or, or_false, or_self] at hv
        rcases hv with rfl | hvT
        · rw [St₂_used_eq]; exact List.mem_cons_self
        · rw [St₂_used_eq, hs_used, hd_used]
          exact List.mem_cons_of_mem _ (S!_used_sub (hbvT v hvT))
      · intro v hv
        rw [St₂_used_eq, hs_used, hd_used]
        exact List.mem_cons_of_mem _ (S!_used_sub hv)
    · mvcgen
  | @chpred α α' c_α =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl⟩ := pre
    unfold castUnionAux castUnion.chpred
    mspec (loosenAux_prf_bv _ hbvS)
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨S!_used, S!_bv, S!_used_sub⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, _, hd_used, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨_, _, _, hs_used, _⟩ := pres
    mspec SMT.freshVar_spec
    mrename_i pre2
    mintro ∀St₂
    mpure pre2
    obtain ⟨_, _, _, St₂_used_eq, _⟩ := pre2
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨?_, ?_⟩
    · intro v hv
      simp only [SMT.bv, List.nil_append, List.append_nil, List.mem_append, List.mem_cons,
        List.not_mem_nil, false_or, or_false] at hv
      rcases hv with rfl | hvT
      · rw [St₂_used_eq]; exact List.mem_cons_self
      · rw [St₂_used_eq, hs_used, hd_used]
        exact List.mem_cons_of_mem _ (S!_used_sub (hbvT v hvT))
    · intro v hv
      rw [St₂_used_eq, hs_used, hd_used]
      exact List.mem_cons_of_mem _ (S!_used_sub hv)
  | @opt α α' c_α =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl⟩ := pre
    unfold castUnionAux castUnion.opt
    mvcgen
  | @pair α β α' β' c_α c_β =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl⟩ := pre
    unfold castUnionAux castUnion.pair
    mvcgen
  | @refl α hα =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl⟩ := pre
    unfold castUnionAux castUnion.refl
    mvcgen

set_option maxHeartbeats 4000000 in
theorem castUnion_bv (S T : SMT.Term) (sS sT : SMTType) {used : List SMT.𝒱} {n : ℕ}
    (hbvS : ∀ v ∈ SMT.bv S, v ∈ used) (hbvT : ∀ v ∈ SMT.bv T, v ∈ used) :
    ⦃ fun (⟨E, _Λ'⟩ : EncoderState) ↦ ⌜E.freshvarsc = n ∧ E.usedVars = used⌝ ⦄
    castUnion (S, sS) (T, sT)
    ⦃ ⇓? (⟨t', _σ⟩ : SMT.Term × SMTType) (⟨E', _Γ'⟩ : EncoderState) =>
        ⌜(∀ v ∈ SMT.bv t', v ∈ E'.usedVars) ∧ used ⊆ E'.usedVars⌝ ⦄ := by
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl⟩ := pre
  unfold castUnion
  split
  split
  rename_i heqA _ _ _ heqB
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heqA
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heqB
  split_ifs with heq hsub1 hsub2
  · subst heq
    split
    · mspec SMT.freshVar_spec
      mrename_i pre2
      mintro ∀St₂
      mpure pre2
      obtain ⟨_, _, _, St₂_used_eq, _⟩ := pre2
      mspec SMT.eraseFromContext_spec
      mrename_i preE
      mintro ∀StE
      mpure preE
      obtain ⟨_, _, StE_used_eq⟩ := preE
      mspec Std.Do.Spec.pure
      mpure_intro
      rw [StE_used_eq]
      refine ⟨?_, fun v hv => by rw [St₂_used_eq]; exact List.mem_cons_of_mem _ hv⟩
      intro v hv
      simp only [SMT.bv, List.append_nil, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hv
      rcases hv with rfl | hvS | hvT
      · rw [St₂_used_eq]; exact List.mem_cons_self
      · rw [St₂_used_eq]; exact List.mem_cons_of_mem _ (hbvS v hvS)
      · rw [St₂_used_eq]; exact List.mem_cons_of_mem _ (hbvT v hvT)
    all_goals mvcgen
  · mspec (castUnionAux_bv _ S T hbvS hbvT)
  · mspec (castUnionAux_bv _ T S hbvT hbvS)
  · mvcgen

set_option maxHeartbeats 4000000 in
/-- bv/usedVars spec of the `castInter` wrapper (staged `split` + `castInterAux_bv`
dispatch; the direct branch builds `λ x. S(x) ∧ T(x)`). -/
theorem castInter_bv (S T : SMT.Term) (sS sT : SMTType) {used : List SMT.𝒱} {n : ℕ}
    (hbvS : ∀ v ∈ SMT.bv S, v ∈ used) (hbvT : ∀ v ∈ SMT.bv T, v ∈ used) :
    ⦃ fun (⟨E, _Λ'⟩ : EncoderState) ↦ ⌜E.freshvarsc = n ∧ E.usedVars = used⌝ ⦄
    castInter (S, sS) (T, sT)
    ⦃ ⇓? (⟨t', _σ⟩ : SMT.Term × SMTType) (⟨E', _Γ'⟩ : EncoderState) =>
        ⌜(∀ v ∈ SMT.bv t', v ∈ E'.usedVars) ∧ used ⊆ E'.usedVars⌝ ⦄ := by
  have IAux : ∀ {α β : SMTType} (c : α ~> β) (S' T' : SMT.Term),
      (∀ v ∈ SMT.bv S', v ∈ used) → (∀ v ∈ SMT.bv T', v ∈ used) →
      ⦃ fun (⟨E, _Λ'⟩ : EncoderState) ↦ ⌜E.freshvarsc = n ∧ E.usedVars = used⌝ ⦄
      castInterAux S' T' c
      ⦃ ⇓? (⟨t', _σ⟩ : SMT.Term × SMTType) (⟨E', _Γ'⟩ : EncoderState) =>
          ⌜(∀ v ∈ SMT.bv t', v ∈ E'.usedVars) ∧ used ⊆ E'.usedVars⌝ ⦄ := by
    intro α β c S' T' hbvS' hbvT'
    cases c with
    | @graph α β α' β' c_α c_β =>
      mintro pre ∀St
      mpure pre
      obtain ⟨rfl, rfl⟩ := pre
      unfold castInterAux
      mspec (loosenAux_prf_bv _ hbvS')
      mrename_i pre
      mintro ∀St₁
      mpure pre
      obtain ⟨S!_used, S!_bv, S!_used_sub⟩ := pre
      mspec SMT.declareConst_spec
      mrename_i pred
      mintro ∀St₁d
      mpure pred
      obtain ⟨_, _, _, hd_used, _⟩ := pred
      mspec SMT.addSpec_spec
      mrename_i pres
      mintro ∀St₁s
      mpure pres
      obtain ⟨_, _, _, hs_used, _⟩ := pres
      mspec SMT.freshVar_spec
      mrename_i pre2
      mintro ∀St₂
      mpure pre2
      obtain ⟨_, _, _, St₂_used_eq, _⟩ := pre2
      mspec SMT.eraseFromContext_spec
      mrename_i preE
      mintro ∀StE
      mpure preE
      obtain ⟨_, _, StE_used_eq⟩ := preE
      mspec Std.Do.Spec.pure
      mpure_intro
      rw [StE_used_eq]
      refine ⟨?_, ?_⟩
      · intro v hv
        simp only [SMT.bv, List.nil_append, List.append_nil, List.mem_append, List.mem_cons,
          List.not_mem_nil, false_or, or_false] at hv
        rcases hv with rfl | hvT
        · rw [St₂_used_eq]; exact List.mem_cons_self
        · rw [St₂_used_eq, hs_used, hd_used]
          exact List.mem_cons_of_mem _ (S!_used_sub (hbvT' v hvT))
      · intro v hv
        rw [St₂_used_eq, hs_used, hd_used]
        exact List.mem_cons_of_mem _ (S!_used_sub hv)
    | @«fun» α β α' β' hβ c_α c_β =>
      mintro pre ∀St
      mpure pre
      obtain ⟨rfl, rfl⟩ := pre
      unfold castInterAux
      mspec (loosenAux_prf_bv _ hbvS')
      mrename_i pre
      mintro ∀St₁
      mpure pre
      obtain ⟨S!_used, S!_bv, S!_used_sub⟩ := pre
      mspec SMT.declareConst_spec
      mrename_i pred
      mintro ∀St₁d
      mpure pred
      obtain ⟨_, _, _, hd_used, _⟩ := pred
      mspec SMT.addSpec_spec
      mrename_i pres
      mintro ∀St₁s
      mpure pres
      obtain ⟨_, _, _, hs_used, _⟩ := pres
      split
      · mspec SMT.freshVar_spec
        mrename_i pre2
        mintro ∀St₂
        mpure pre2
        obtain ⟨_, _, _, St₂_used_eq, _⟩ := pre2
        mspec Std.Do.Spec.pure
        mpure_intro
        refine ⟨?_, ?_⟩
        · intro v hv
          simp only [SMT.bv, List.nil_append, List.append_nil, List.mem_append, List.mem_cons,
            List.not_mem_nil, false_or, or_false, or_self] at hv
          rcases hv with rfl | hvT
          · rw [St₂_used_eq]; exact List.mem_cons_self
          · rw [St₂_used_eq, hs_used, hd_used]
            exact List.mem_cons_of_mem _ (S!_used_sub (hbvT' v hvT))
        · intro v hv
          rw [St₂_used_eq, hs_used, hd_used]
          exact List.mem_cons_of_mem _ (S!_used_sub hv)
      · mvcgen
    | @chpred α α' c_α =>
      mintro pre ∀St
      mpure pre
      obtain ⟨rfl, rfl⟩ := pre
      unfold castInterAux
      mspec (loosenAux_prf_bv _ hbvS')
      mrename_i pre
      mintro ∀St₁
      mpure pre
      obtain ⟨S!_used, S!_bv, S!_used_sub⟩ := pre
      mspec SMT.declareConst_spec
      mrename_i pred
      mintro ∀St₁d
      mpure pred
      obtain ⟨_, _, _, hd_used, _⟩ := pred
      mspec SMT.addSpec_spec
      mrename_i pres
      mintro ∀St₁s
      mpure pres
      obtain ⟨_, _, _, hs_used, _⟩ := pres
      mspec SMT.freshVar_spec
      mrename_i pre2
      mintro ∀St₂
      mpure pre2
      obtain ⟨_, _, _, St₂_used_eq, _⟩ := pre2
      mspec Std.Do.Spec.pure
      mpure_intro
      refine ⟨?_, ?_⟩
      · intro v hv
        simp only [SMT.bv, List.nil_append, List.append_nil, List.mem_append, List.mem_cons,
          List.not_mem_nil, false_or, or_false] at hv
        rcases hv with rfl | hvT
        · rw [St₂_used_eq]; exact List.mem_cons_self
        · rw [St₂_used_eq, hs_used, hd_used]
          exact List.mem_cons_of_mem _ (S!_used_sub (hbvT' v hvT))
      · intro v hv
        rw [St₂_used_eq, hs_used, hd_used]
        exact List.mem_cons_of_mem _ (S!_used_sub hv)
    | @opt α α' c_α =>
      mintro pre ∀St
      mpure pre
      obtain ⟨rfl, rfl⟩ := pre
      unfold castInterAux
      mvcgen
    | @pair α β α' β' c_α c_β =>
      mintro pre ∀St
      mpure pre
      obtain ⟨rfl, rfl⟩ := pre
      unfold castInterAux
      mvcgen
    | @refl α hα =>
      mintro pre ∀St
      mpure pre
      obtain ⟨rfl, rfl⟩ := pre
      unfold castInterAux
      mvcgen
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl⟩ := pre
  unfold castInter
  split
  split
  rename_i heqA _ _ _ heqB
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heqA
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heqB
  split_ifs with heq hsub1 hsub2
  · subst heq
    split
    · mspec SMT.freshVar_spec
      mrename_i pre2
      mintro ∀St₂
      mpure pre2
      obtain ⟨_, _, _, St₂_used_eq, _⟩ := pre2
      mspec SMT.eraseFromContext_spec
      mrename_i preE
      mintro ∀StE
      mpure preE
      obtain ⟨_, _, StE_used_eq⟩ := preE
      mspec Std.Do.Spec.pure
      mpure_intro
      rw [StE_used_eq]
      refine ⟨?_, fun v hv => by rw [St₂_used_eq]; exact List.mem_cons_of_mem _ hv⟩
      intro v hv
      simp only [SMT.bv, List.append_nil, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hv
      rcases hv with rfl | hvS | hvT
      · rw [St₂_used_eq]; exact List.mem_cons_self
      · rw [St₂_used_eq]; exact List.mem_cons_of_mem _ (hbvS v hvS)
      · rw [St₂_used_eq]; exact List.mem_cons_of_mem _ (hbvT v hvT)
    all_goals mvcgen
  · mspec (IAux _ S T hbvS hbvT)
  · mspec (IAux _ T S hbvT hbvS)
  · mvcgen

/-- `bv` of a right-fold of `⇒ˢ` is the flatMap of the premises' `bv` followed by
the base's `bv`. -/
theorem bv_foldr_imp (ts : List SMT.Term) (base : SMT.Term) :
    SMT.bv (ts.foldr (.imp · ·) base) = ts.flatMap SMT.bv ++ SMT.bv base := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    simp only [List.foldr_cons, SMT.bv, ih, List.flatMap_cons, List.append_assoc]

/-- `bv` of a right-fold of single-binder `∀`s exposes the binder names followed by
the inner term's `bv`. -/
theorem bv_foldr_forall (ps : List (SMT.𝒱 × SMTType)) (inner : SMT.Term) :
    SMT.bv (ps.foldr (fun p t => SMT.Term.forall [p.1] [p.2] t) inner)
      = ps.map Prod.fst ++ SMT.bv inner := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simp only [List.foldr_cons, SMT.bv, ih, List.map_cons, List.cons_append,
      List.singleton_append, List.nil_append]

/-- `loosenAux_prf` bundles `bv`/`usedVars` facts with declarations-invariance
(no `DeclsInv` needed); used by the delta-tracking cast companions. -/
theorem loosenAux_prf_bv_declsEq {α β : SMTType} (c : α ~> β) {used : List SMT.𝒱} {n : ℕ}
    {name : String} {x : SMT.Term} {decl : SMT.Chunk}
    (hx : ∀ v ∈ SMT.bv x, v ∈ used) :
    ⦃ fun (⟨E, _Λ⟩ : EncoderState) ↦
        ⌜E.freshvarsc = n ∧ E.usedVars = used ∧ E.declarations = decl⌝ ⦄
    loosenAux_prf name c x
    ⦃ ⇓? (p : SMT.𝒱 × SMT.Term) (⟨E', _Γ⟩ : EncoderState) =>
        ⌜p.1 ∈ E'.usedVars ∧ (∀ v ∈ SMT.bv p.2, v ∈ E'.usedVars) ∧ used ⊆ E'.usedVars
          ∧ E'.declarations = decl⌝ ⦄ := by
  have hand := Std.Do.Triple.and (loosenAux_prf name c x)
    (loosenAux_prf_bv c (used := used) (n := n) (name := name) (x := x) hx)
    (loosenAux_prf_decls c (name := name) (x := x) (decl := decl))
  mintro pre ∀St
  mpure pre
  obtain ⟨hfvc, hused, hdecl⟩ := pre
  mspec hand
  mrename_i hpost
  mintro ∀St'
  mpure hpost
  mpure_intro
  obtain ⟨⟨x!_used, spec_bv, used_sub⟩, decl_eq⟩ := hpost
  exact ⟨x!_used, spec_bv, used_sub, decl_eq⟩

/-- `freshVar` bundled with declarations-invariance: the only facts the delta
companions need are `usedVars = v :: used` and `declarations = decl`. -/
theorem SMT.freshVar_spec_decls {Γ : SMT.TypeContext} {τ : SMTType} {name : String} {n : ℕ}
    {used : List SMT.𝒱} {decl : SMT.Chunk} :
    ⦃ fun (⟨E, Γ'⟩ : EncoderState) ↦
        ⌜Γ' = Γ ∧ E.freshvarsc = n ∧ E.usedVars = used ∧ E.declarations = decl⌝ ⦄
    SMT.freshVar τ name
    ⦃ ⇓? v (⟨E', _Γ'⟩ : EncoderState) =>
        ⌜E'.usedVars = v :: used ∧ E'.declarations = decl⌝ ⦄ := by
  have hand := Std.Do.Triple.and (SMT.freshVar τ name)
    (SMT.freshVar_spec (Γ := Γ) (τ := τ) (name := name) (n := n) (used := used))
    (SMT.freshVar_decls (τ := τ) (name := name) (decl := decl))
  mintro pre ∀St
  mpure pre
  obtain ⟨hΓ, hfvc, hused, hdecl⟩ := pre
  mspec hand
  mrename_i hpost
  mintro ∀St'
  mpure hpost
  mpure_intro
  obtain ⟨⟨_, _, _, used_eq, _⟩, decl_eq⟩ := hpost
  exact ⟨used_eq, decl_eq⟩

/-- The "good delta" predicate threaded by `encodeTerm_decls_bv`: every name a
declarations-delta `Dl` declares and every bound variable of a `define_fun` spec
body it adds already lives in `U`.  This is exactly the per-delta version of
`DeclsInv`, and it is the data the `all` case needs about the cast-helper
declarations it splices into the result quantifier. -/
def DeltaBvOk (Dl : SMT.Chunk) (U : List SMT.𝒱) : Prop :=
  (∀ v ∈ declVars Dl, v ∈ U) ∧ (∀ b ∈ specBodies Dl, ∀ v ∈ SMT.bv b, v ∈ U)

theorem DeltaBvOk.mono {Dl : SMT.Chunk} {U U' : List SMT.𝒱} (h : DeltaBvOk Dl U)
    (hsub : U ⊆ U') : DeltaBvOk Dl U' :=
  ⟨fun v hv => hsub (h.1 v hv), fun b hb v hv => hsub (h.2 b hb v hv)⟩

theorem DeltaBvOk.append {Δ₁ Δ₂ : SMT.Chunk} {U : List SMT.𝒱}
    (h₁ : DeltaBvOk Δ₁ U) (h₂ : DeltaBvOk Δ₂ U) : DeltaBvOk (Δ₁ ++ Δ₂) U := by
  refine ⟨fun v hv => ?_, fun b hb v hv => ?_⟩
  · rw [declVars_append, List.mem_append] at hv
    exact hv.elim (h₁.1 v) (h₂.1 v)
  · rw [specBodies_append, List.mem_append] at hb
    exact hb.elim (fun hb => h₁.2 b hb v hv) (fun hb => h₂.2 b hb v hv)

@[simp] theorem DeltaBvOk_nil {U : List SMT.𝒱} : DeltaBvOk [] U := by
  simp [DeltaBvOk]

/-- A single `declare_const v` delta is good when `v` is used. -/
theorem DeltaBvOk.declare_const {v : SMT.𝒱} {τ : SMTType} {U : List SMT.𝒱} (hv : v ∈ U) :
    DeltaBvOk [.declare_const v τ] U := by
  refine ⟨fun w hw => ?_, fun b hb => ?_⟩
  · simp only [declVars_declare_const, List.mem_singleton] at hw; exact hw ▸ hv
  · simp only [specBodies_declare_const, List.not_mem_nil] at hb

/-- A single `define_fun _ .unit .bool b` (`addSpec` body) delta is good when every
bound variable of `b` is used. -/
theorem DeltaBvOk.define_fun_spec {nm : String} {b : SMT.Term} {U : List SMT.𝒱}
    (hb : ∀ v ∈ SMT.bv b, v ∈ U) : DeltaBvOk [.define_fun nm .unit .bool b] U := by
  refine ⟨fun w hw => ?_, fun b' hb' w hw => ?_⟩
  · simp only [declVars, SMT.Instr.define_fun, List.filterMap_cons, List.filterMap_nil] at hw
    exact absurd hw List.not_mem_nil
  · rw [show ([SMT.Instr.define_fun nm .unit .bool b]) = [] ++ [SMT.Instr.define_fun nm .unit .bool b]
      from rfl, specBodies_append] at hb'
    simp only [specBodies_nil, List.nil_append, mem_specBodies_define_fun] at hb'
    obtain ⟨nm', hmem⟩ := hb'
    rw [List.mem_singleton] at hmem
    cases hmem
    exact hb w hw

/-- One constrained helper contributes a declaration and its Boolean
specification, both covered by `DeltaBvOk`. -/
theorem DeltaBvOk.helperSpecChunk {v : SMT.𝒱} {τ : SMTType} {b : SMT.Term}
    {U : List SMT.𝒱} (hv : v ∈ U) (hb : ∀ w ∈ SMT.bv b, w ∈ U) :
    DeltaBvOk (_root_.helperSpecChunk v τ b) U := by
  simpa [_root_.helperSpecChunk] using
    DeltaBvOk.append (DeltaBvOk.declare_const (τ := τ) hv)
      (DeltaBvOk.define_fun_spec (nm := s!"{v}_spec") hb)

set_option maxHeartbeats 4000000 in
/-- Declarations-delta spec of `castEq`: every loosened equality helper is paired
with the Boolean specification asserted by `declareConstWithSpec`. -/
theorem castEq_decls_bv (A B : SMT.Term) (σA σB : SMTType) {used : List SMT.𝒱} {n : ℕ}
    {decl : SMT.Chunk}
    (hbvA : ∀ v ∈ SMT.bv A, v ∈ used) (hbvB : ∀ v ∈ SMT.bv B, v ∈ used) :
    ⦃ fun (⟨E, _Λ'⟩ : EncoderState) ↦
        ⌜E.freshvarsc = n ∧ E.usedVars = used ∧ E.declarations = decl⌝ ⦄
    castEq (A, σA) (B, σB)
    ⦃ ⇓? (_ : SMT.Term × SMTType) (⟨E', _Γ'⟩ : EncoderState) =>
        ⌜∃ Dl : SMT.Chunk, E'.declarations = decl ++ Dl ∧ DeltaBvOk Dl E'.usedVars
          ∧ used ⊆ E'.usedVars⌝ ⦄ := by
  unfold castEq
  mvcgen
  · rename_i hpre
    obtain ⟨rfl, rfl, rfl⟩ := hpre
    exact ⟨[], by simp, DeltaBvOk_nil, fun v hv => hv⟩
  · rename_i hpre
    obtain ⟨rfl, rfl, rfl⟩ := hpre
    mspec (loosenAux_prf_bv_declsEq _ hbvA)
    mrename_i pre
    mintro ∀St₁
    rename_i Aout
    obtain ⟨A!, A!_spec⟩ := Aout
    mpure pre
    obtain ⟨A!_used, A!_bv, A!_used_sub, A!_decl⟩ := pre
    mspec SMT.declareConst_addSpec_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, hd_used, _⟩ := pred
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨_root_.helperSpecChunk A! σB A!_spec, ?_, ?_, ?_⟩
    · rw [hd_decl, A!_decl]
      simp [_root_.helperSpecChunk, List.concat_eq_append, List.append_assoc]
    · rw [hd_used]
      exact DeltaBvOk.helperSpecChunk A!_used A!_bv
    · exact fun v hv => by rw [hd_used]; exact A!_used_sub hv
  · rename_i hpre
    obtain ⟨rfl, rfl, rfl⟩ := hpre
    mspec (loosenAux_prf_bv_declsEq _ hbvB)
    mrename_i pre
    mintro ∀St₁
    rename_i Bout
    obtain ⟨B!, B!_spec⟩ := Bout
    mpure pre
    obtain ⟨B!_used, B!_bv, B!_used_sub, B!_decl⟩ := pre
    mspec SMT.declareConst_addSpec_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, hd_used, _⟩ := pred
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨_root_.helperSpecChunk B! σA B!_spec, ?_, ?_, ?_⟩
    · rw [hd_decl, B!_decl]
      simp [_root_.helperSpecChunk, List.concat_eq_append, List.append_assoc]
    · rw [hd_used]
      exact DeltaBvOk.helperSpecChunk B!_used B!_bv
    · exact fun v hv => by rw [hd_used]; exact B!_used_sub hv

set_option maxHeartbeats 4000000 in
/-- Declarations-delta spec of `castMembership`: every loosened helper is paired
with the `define_fun` specification asserted by `declareConstWithSpec`. -/
theorem castMembership_decls_bv (x S : SMT.Term) (sx sS : SMTType) {used : List SMT.𝒱} {n : ℕ}
    {decl : SMT.Chunk}
    (hbvx : ∀ v ∈ SMT.bv x, v ∈ used) (hbvS : ∀ v ∈ SMT.bv S, v ∈ used) :
    ⦃ fun (⟨E, _Λ'⟩ : EncoderState) ↦
        ⌜E.freshvarsc = n ∧ E.usedVars = used ∧ E.declarations = decl⌝ ⦄
    castMembership (x, sx) (S, sS)
    ⦃ ⇓? (_ : SMT.Term × SMTType) (⟨E', _Γ'⟩ : EncoderState) =>
        ⌜∃ Dl : SMT.Chunk, E'.declarations = decl ++ Dl ∧ DeltaBvOk Dl E'.usedVars
          ∧ used ⊆ E'.usedVars⌝ ⦄ := by
  unfold castMembership
  mvcgen
  case vc1.h_1.isTrue =>
    rename_i α' hσS hσx St hpre
    obtain ⟨rfl, rfl, rfl⟩ := hpre
    exact ⟨[], by simp, DeltaBvOk_nil, fun v hv => hv⟩
  case vc2.h_1.isFalse.isTrue =>
    rename_i α' hσS hσx_ne hσx_le St hpre
    obtain ⟨rfl, rfl, rfl⟩ := hpre
    mspec (loosenAux_prf_bv_declsEq _ hbvx)
    mrename_i pre
    mintro ∀St₁
    rename_i xout
    obtain ⟨x!, x!_spec⟩ := xout
    mpure pre
    obtain ⟨x!_used, x!_bv, x!_used_sub, x!_decl⟩ := pre
    mspec SMT.declareConst_addSpec_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, hd_used, _⟩ := pred
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨_root_.helperSpecChunk x! α' x!_spec, ?_, ?_,
      fun v hv => by rw [hd_used]; exact x!_used_sub hv⟩
    · rw [hd_decl, x!_decl]
      simp [_root_.helperSpecChunk, List.concat_eq_append, List.append_assoc]
    · rw [hd_used]
      exact DeltaBvOk.helperSpecChunk x!_used x!_bv
  case vc3.h_1.isFalse.isFalse.isTrue =>
    rename_i α' hσS hσx_ne hσx_nle hα'_le St hpre
    obtain ⟨rfl, rfl, rfl⟩ := hpre
    mspec (loosenAux_prf_bv_declsEq _ hbvS)
    mrename_i pre
    mintro ∀St₁
    rename_i Sout
    obtain ⟨S!, S!_spec⟩ := Sout
    mpure pre
    obtain ⟨S!_used, S!_bv, S!_used_sub, S!_decl⟩ := pre
    mspec SMT.declareConst_addSpec_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, hd_used, _⟩ := pred
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨_root_.helperSpecChunk S! (.fun sx .bool) S!_spec, ?_, ?_,
      fun v hv => by rw [hd_used]; exact S!_used_sub hv⟩
    · rw [hd_decl, S!_decl]
      simp [_root_.helperSpecChunk, List.concat_eq_append, List.append_assoc]
    · rw [hd_used]
      exact DeltaBvOk.helperSpecChunk S!_used S!_bv
  case vc4.h_2.h_1.isTrue.isTrue =>
    rename_i α' β' hσS α β hσx hα_le hβ_le St hpre
    obtain ⟨rfl, rfl, rfl⟩ := hpre
    mspec (loosenAux_prf_bv_declsEq _ hbvx)
    mrename_i pre
    mintro ∀St₁
    rename_i xout
    obtain ⟨x!, x!_spec⟩ := xout
    mpure pre
    obtain ⟨x!_used, x!_bv, x!_used_sub, x!_decl⟩ := pre
    mspec SMT.declareConst_addSpec_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, hd_used, _⟩ := pred
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨_root_.helperSpecChunk x! (.pair α' β') x!_spec, ?_, ?_,
      fun v hv => by rw [hd_used]; exact x!_used_sub hv⟩
    · rw [hd_decl, x!_decl]
      simp [_root_.helperSpecChunk, List.concat_eq_append, List.append_assoc]
    · rw [hd_used]
      exact DeltaBvOk.helperSpecChunk x!_used x!_bv
  case vc5.h_2.h_1.isTrue.isFalse.isTrue =>
    rename_i α' β' hσS α β hσx hα_le hβ_nle hβ'_le St hpre
    obtain ⟨rfl, rfl, rfl⟩ := hpre
    mspec (loosenAux_prf_bv_declsEq _ (by intro v hv; exact hbvx v (by rwa [SMT.bv] at hv)))
    mrename_i preX
    mintro ∀St₁
    rename_i xout
    obtain ⟨x!, x!_spec⟩ := xout
    mpure preX
    obtain ⟨x!_used, x!_bv, x!_used_sub, x!_decl⟩ := preX
    mspec SMT.declareConst_addSpec_spec
    mrename_i predX
    mintro ∀St₁d
    mpure predX
    obtain ⟨hdX_decl, _, _, hdX_used, _⟩ := predX
    mspec (loosenAux_prf_bv_declsEq _ (used := St₁d.env.usedVars)
      (by intro v hv; rw [hdX_used]; exact x!_used_sub (hbvS v hv)))
    mrename_i preS
    mintro ∀St₂
    rename_i Sout
    obtain ⟨S!, S!_spec⟩ := Sout
    mpure preS
    obtain ⟨S!_used, S!_bv, S!_used_sub, S!_decl⟩ := preS
    mspec SMT.declareConst_addSpec_spec
    mrename_i predS
    mintro ∀St₂d
    mpure predS
    obtain ⟨hdS_decl, _, _, hdS_used, _⟩ := predS
    mspec Std.Do.Spec.pure
    mpure_intro
    have lift1 : ∀ {w}, w ∈ St₁.env.usedVars → w ∈ St₂d.env.usedVars :=
      fun {w} h => by rw [hdS_used]; exact S!_used_sub (by rw [hdX_used]; exact h)
    refine ⟨_root_.helperSpecChunk x! α' x!_spec ++
        _root_.helperSpecChunk S! (.fun α' (.option β)) S!_spec,
      ?_, ?_, fun v hv => lift1 (x!_used_sub hv)⟩
    · rw [hdS_decl, S!_decl, hdX_decl, x!_decl]
      simp [_root_.helperSpecChunk, List.concat_eq_append, List.append_assoc]
    · refine DeltaBvOk.append ?_ ?_
      · exact DeltaBvOk.helperSpecChunk (lift1 x!_used)
          (fun v hv => lift1 (x!_bv v hv))
      · rw [hdS_used]
        exact DeltaBvOk.helperSpecChunk S!_used S!_bv
  case vc6.h_2.h_1.isFalse.isTrue.isTrue =>
    rename_i α' β' hσS α β hσx hα_nle hα'_le hβ_le St hpre
    obtain ⟨rfl, rfl, rfl⟩ := hpre
    mspec (loosenAux_prf_bv_declsEq _ (by intro v hv; exact hbvx v (by rwa [SMT.bv] at hv)))
    mrename_i preY
    mintro ∀St₁
    rename_i yout
    obtain ⟨y!, y!_spec⟩ := yout
    mpure preY
    obtain ⟨y!_used, y!_bv, y!_used_sub, y!_decl⟩ := preY
    mspec SMT.declareConst_addSpec_spec
    mrename_i predY
    mintro ∀St₁d
    mpure predY
    obtain ⟨hdY_decl, _, _, hdY_used, _⟩ := predY
    mspec (loosenAux_prf_bv_declsEq _ (used := St₁d.env.usedVars)
      (by intro v hv; rw [hdY_used]; exact y!_used_sub (hbvS v hv)))
    mrename_i preS
    mintro ∀St₂
    rename_i Sout
    obtain ⟨S!, S!_spec⟩ := Sout
    mpure preS
    obtain ⟨S!_used, S!_bv, S!_used_sub, S!_decl⟩ := preS
    mspec SMT.declareConst_addSpec_spec
    mrename_i predS
    mintro ∀St₂d
    mpure predS
    obtain ⟨hdS_decl, _, _, hdS_used, _⟩ := predS
    mspec Std.Do.Spec.pure
    mpure_intro
    have lift1 : ∀ {w}, w ∈ St₁.env.usedVars → w ∈ St₂d.env.usedVars :=
      fun {w} h => by rw [hdS_used]; exact S!_used_sub (by rw [hdY_used]; exact h)
    refine ⟨_root_.helperSpecChunk y! β' y!_spec ++
        _root_.helperSpecChunk S! (.fun α (.option β')) S!_spec,
      ?_, ?_, fun v hv => lift1 (y!_used_sub hv)⟩
    · rw [hdS_decl, S!_decl, hdY_decl, y!_decl]
      simp [_root_.helperSpecChunk, List.concat_eq_append, List.append_assoc]
    · refine DeltaBvOk.append ?_ ?_
      · exact DeltaBvOk.helperSpecChunk (lift1 y!_used)
          (fun v hv => lift1 (y!_bv v hv))
      · rw [hdS_used]
        exact DeltaBvOk.helperSpecChunk S!_used S!_bv
  case vc7.h_2.h_1.isFalse.isTrue.isFalse.isTrue =>
    rename_i α' β' hσS α β hσx hα_nle hα'_le hβ_nle hβ'_le St hpre
    obtain ⟨rfl, rfl, rfl⟩ := hpre
    mspec (loosenAux_prf_bv_declsEq _ hbvS)
    mrename_i pre
    mintro ∀St₁
    rename_i Sout
    obtain ⟨S!, S!_spec⟩ := Sout
    mpure pre
    obtain ⟨S!_used, S!_bv, S!_used_sub, S!_decl⟩ := pre
    mspec SMT.declareConst_addSpec_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, hd_used, _⟩ := pred
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨_root_.helperSpecChunk S! (.fun α (.option β)) S!_spec, ?_, ?_,
      fun v hv => by rw [hd_used]; exact S!_used_sub hv⟩
    · rw [hd_decl, S!_decl]
      simp [_root_.helperSpecChunk, List.concat_eq_append, List.append_assoc]
    · rw [hd_used]
      exact DeltaBvOk.helperSpecChunk S!_used S!_bv

set_option maxHeartbeats 4000000 in
/-- Declarations-delta spec of `castUnionAux`: each non-throw branch loosens `S`
(`declareConst` + `addSpec`), so its delta is `[declare_const S!, define_fun
{S!}_spec _ _ L]` with `S!` used and `bv L ⊆ used`. -/
theorem castUnionAux_decls_bv {α β : SMTType} (c : α ~> β) (S T : SMT.Term) {used : List SMT.𝒱}
    {n : ℕ} {decl : SMT.Chunk} (hbvS : ∀ v ∈ SMT.bv S, v ∈ used) :
    ⦃ fun (⟨E, _Λ'⟩ : EncoderState) ↦
        ⌜E.freshvarsc = n ∧ E.usedVars = used ∧ E.declarations = decl⌝ ⦄
    castUnionAux S T c
    ⦃ ⇓? (_ : SMT.Term × SMTType) (⟨E', _Γ'⟩ : EncoderState) =>
        ⌜∃ Dl : SMT.Chunk, E'.declarations = decl ++ Dl ∧ DeltaBvOk Dl E'.usedVars
          ∧ used ⊆ E'.usedVars⌝ ⦄ := by
  cases c with
  | @graph α β α' β' c_α c_β =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    unfold castUnionAux castUnion.graph
    mspec (loosenAux_prf_bv_declsEq _ hbvS)
    mrename_i pre
    mintro ∀St₁
    rename_i S!_pair
    obtain ⟨S!, S!_spec⟩ := S!_pair
    mpure pre
    obtain ⟨S!_used, S!_bv, S!_used_sub, S!_decl⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, hd_used, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨hs_decl, _, _, hs_used, _⟩ := pres
    mspec SMT.freshVar_spec_decls
    mrename_i pre2
    mintro ∀St₂
    mpure pre2
    obtain ⟨St₂_used_eq, St₂_decl⟩ := pre2
    rename_i x
    mspec SMT.eraseFromContext_used_decls (v := x)
      (used := St₂.env.usedVars) (decl := St₂.env.declarations)
    mrename_i pre3
    mintro ∀St₃
    mpure pre3
    obtain ⟨St₃_used_eq, St₃_decl⟩ := pre3
    mspec Std.Do.Spec.pure
    mpure_intro
    have lift : ∀ {w}, w ∈ St₁.env.usedVars → w ∈ St₃.env.usedVars := fun {w} h => by
      rw [St₃_used_eq, St₂_used_eq, hs_used, hd_used]
      exact List.mem_cons_of_mem _ h
    refine ⟨[.declare_const S! (.fun (.pair α' β') .bool),
      .define_fun s!"{S!}_spec" .unit .bool S!_spec], ?_, ?_, fun v hv => lift (S!_used_sub hv)⟩
    · rw [St₃_decl, St₂_decl, hs_decl, hd_decl, S!_decl,
        List.concat_eq_append, List.concat_eq_append,
        List.append_assoc, List.cons_append, List.nil_append]
    · exact DeltaBvOk.append (DeltaBvOk.declare_const (lift S!_used))
        (DeltaBvOk.define_fun_spec (fun w hw => lift (S!_bv w hw)))
  | @«fun» α β α' β' hβ c_α c_β =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    unfold castUnionAux castUnion.fun
    mspec (loosenAux_prf_bv_declsEq _ hbvS)
    mrename_i pre
    mintro ∀St₁
    rename_i S!_pair
    obtain ⟨S!, S!_spec⟩ := S!_pair
    mpure pre
    obtain ⟨S!_used, S!_bv, S!_used_sub, S!_decl⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, hd_used, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨hs_decl, _, _, hs_used, _⟩ := pres
    split
    · rename_i σ _
      mspec SMT.freshVar_spec_decls
      mrename_i pre2
      mintro ∀St₂
      mpure pre2
      obtain ⟨St₂_used_eq, St₂_decl⟩ := pre2
      mspec Std.Do.Spec.pure
      mpure_intro
      have lift : ∀ {w}, w ∈ St₁.env.usedVars → w ∈ St₂.env.usedVars := fun {w} h => by
        rw [St₂_used_eq, hs_used, hd_used]; exact List.mem_cons_of_mem _ h
      refine ⟨[.declare_const S! (.fun α' (.option σ)),
        .define_fun s!"{S!}_spec" .unit .bool S!_spec], ?_, ?_, fun v hv => lift (S!_used_sub hv)⟩
      · rw [St₂_decl, hs_decl, hd_decl, S!_decl, List.concat_eq_append, List.concat_eq_append,
          List.append_assoc, List.cons_append, List.nil_append]
      · exact DeltaBvOk.append (DeltaBvOk.declare_const (lift S!_used))
          (DeltaBvOk.define_fun_spec (fun w hw => lift (S!_bv w hw)))
    · mvcgen
  | @chpred α α' c_α =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    unfold castUnionAux castUnion.chpred
    mspec (loosenAux_prf_bv_declsEq _ hbvS)
    mrename_i pre
    mintro ∀St₁
    rename_i S!_pair
    obtain ⟨S!, S!_spec⟩ := S!_pair
    mpure pre
    obtain ⟨S!_used, S!_bv, S!_used_sub, S!_decl⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, hd_used, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨hs_decl, _, _, hs_used, _⟩ := pres
    mspec SMT.freshVar_spec_decls
    mrename_i pre2
    mintro ∀St₂
    mpure pre2
    obtain ⟨St₂_used_eq, St₂_decl⟩ := pre2
    mspec Std.Do.Spec.pure
    mpure_intro
    have lift : ∀ {w}, w ∈ St₁.env.usedVars → w ∈ St₂.env.usedVars := fun {w} h => by
      rw [St₂_used_eq, hs_used, hd_used]; exact List.mem_cons_of_mem _ h
    refine ⟨[.declare_const S! (.fun α' .bool),
      .define_fun s!"{S!}_spec" .unit .bool S!_spec], ?_, ?_, fun v hv => lift (S!_used_sub hv)⟩
    · rw [St₂_decl, hs_decl, hd_decl, S!_decl, List.concat_eq_append, List.concat_eq_append,
        List.append_assoc, List.cons_append, List.nil_append]
    · exact DeltaBvOk.append (DeltaBvOk.declare_const (lift S!_used))
        (DeltaBvOk.define_fun_spec (fun w hw => lift (S!_bv w hw)))
  | @opt α α' c_α =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    unfold castUnionAux castUnion.opt
    mvcgen
  | @pair α β α' β' c_α c_β =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    unfold castUnionAux castUnion.pair
    mvcgen
  | @refl α hα =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    unfold castUnionAux castUnion.refl
    mvcgen

set_option maxHeartbeats 4000000 in
/-- Declarations-delta spec of `castInterAux` (identical to `castUnionAux`). -/
theorem castInterAux_decls_bv {α β : SMTType} (c : α ~> β) (S T : SMT.Term) {used : List SMT.𝒱}
    {n : ℕ} {decl : SMT.Chunk} (hbvS : ∀ v ∈ SMT.bv S, v ∈ used) :
    ⦃ fun (⟨E, _Λ'⟩ : EncoderState) ↦
        ⌜E.freshvarsc = n ∧ E.usedVars = used ∧ E.declarations = decl⌝ ⦄
    castInterAux S T c
    ⦃ ⇓? (_ : SMT.Term × SMTType) (⟨E', _Γ'⟩ : EncoderState) =>
        ⌜∃ Dl : SMT.Chunk, E'.declarations = decl ++ Dl ∧ DeltaBvOk Dl E'.usedVars
          ∧ used ⊆ E'.usedVars⌝ ⦄ := by
  cases c with
  | @graph α β α' β' c_α c_β =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    unfold castInterAux
    mspec (loosenAux_prf_bv_declsEq _ hbvS)
    mrename_i pre
    mintro ∀St₁
    rename_i S!_pair
    obtain ⟨S!, S!_spec⟩ := S!_pair
    mpure pre
    obtain ⟨S!_used, S!_bv, S!_used_sub, S!_decl⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, hd_used, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨hs_decl, _, _, hs_used, _⟩ := pres
    mspec SMT.freshVar_spec_decls
    mrename_i pre2
    mintro ∀St₂
    mpure pre2
    obtain ⟨St₂_used_eq, St₂_decl⟩ := pre2
    rename_i x
    mspec SMT.eraseFromContext_used_decls (v := x)
      (used := St₂.env.usedVars) (decl := St₂.env.declarations)
    mrename_i pre3
    mintro ∀St₃
    mpure pre3
    obtain ⟨St₃_used_eq, St₃_decl⟩ := pre3
    mspec Std.Do.Spec.pure
    mpure_intro
    have lift : ∀ {w}, w ∈ St₁.env.usedVars → w ∈ St₃.env.usedVars := fun {w} h => by
      rw [St₃_used_eq, St₂_used_eq, hs_used, hd_used]
      exact List.mem_cons_of_mem _ h
    refine ⟨[.declare_const S! (.fun (.pair α' β') .bool),
      .define_fun s!"{S!}_spec" .unit .bool S!_spec], ?_, ?_, fun v hv => lift (S!_used_sub hv)⟩
    · rw [St₃_decl, St₂_decl, hs_decl, hd_decl, S!_decl,
        List.concat_eq_append, List.concat_eq_append,
        List.append_assoc, List.cons_append, List.nil_append]
    · exact DeltaBvOk.append (DeltaBvOk.declare_const (lift S!_used))
        (DeltaBvOk.define_fun_spec (fun w hw => lift (S!_bv w hw)))
  | @«fun» α β α' β' hβ c_α c_β =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    unfold castInterAux
    mspec (loosenAux_prf_bv_declsEq _ hbvS)
    mrename_i pre
    mintro ∀St₁
    rename_i S!_pair
    obtain ⟨S!, S!_spec⟩ := S!_pair
    mpure pre
    obtain ⟨S!_used, S!_bv, S!_used_sub, S!_decl⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, hd_used, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨hs_decl, _, _, hs_used, _⟩ := pres
    split
    · rename_i σ _
      mspec SMT.freshVar_spec_decls
      mrename_i pre2
      mintro ∀St₂
      mpure pre2
      obtain ⟨St₂_used_eq, St₂_decl⟩ := pre2
      mspec Std.Do.Spec.pure
      mpure_intro
      have lift : ∀ {w}, w ∈ St₁.env.usedVars → w ∈ St₂.env.usedVars := fun {w} h => by
        rw [St₂_used_eq, hs_used, hd_used]; exact List.mem_cons_of_mem _ h
      refine ⟨[.declare_const S! (.fun α' (.option σ)),
        .define_fun s!"{S!}_spec" .unit .bool S!_spec], ?_, ?_, fun v hv => lift (S!_used_sub hv)⟩
      · rw [St₂_decl, hs_decl, hd_decl, S!_decl, List.concat_eq_append, List.concat_eq_append,
          List.append_assoc, List.cons_append, List.nil_append]
      · exact DeltaBvOk.append (DeltaBvOk.declare_const (lift S!_used))
          (DeltaBvOk.define_fun_spec (fun w hw => lift (S!_bv w hw)))
    · mvcgen
  | @chpred α α' c_α =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    unfold castInterAux
    mspec (loosenAux_prf_bv_declsEq _ hbvS)
    mrename_i pre
    mintro ∀St₁
    rename_i S!_pair
    obtain ⟨S!, S!_spec⟩ := S!_pair
    mpure pre
    obtain ⟨S!_used, S!_bv, S!_used_sub, S!_decl⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, hd_used, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨hs_decl, _, _, hs_used, _⟩ := pres
    mspec SMT.freshVar_spec_decls
    mrename_i pre2
    mintro ∀St₂
    mpure pre2
    obtain ⟨St₂_used_eq, St₂_decl⟩ := pre2
    mspec Std.Do.Spec.pure
    mpure_intro
    have lift : ∀ {w}, w ∈ St₁.env.usedVars → w ∈ St₂.env.usedVars := fun {w} h => by
      rw [St₂_used_eq, hs_used, hd_used]; exact List.mem_cons_of_mem _ h
    refine ⟨[.declare_const S! (.fun α' .bool),
      .define_fun s!"{S!}_spec" .unit .bool S!_spec], ?_, ?_, fun v hv => lift (S!_used_sub hv)⟩
    · rw [St₂_decl, hs_decl, hd_decl, S!_decl, List.concat_eq_append, List.concat_eq_append,
        List.append_assoc, List.cons_append, List.nil_append]
    · exact DeltaBvOk.append (DeltaBvOk.declare_const (lift S!_used))
        (DeltaBvOk.define_fun_spec (fun w hw => lift (S!_bv w hw)))
  | @opt α α' c_α =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    unfold castInterAux
    mvcgen
  | @pair α β α' β' c_α c_β =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    unfold castInterAux
    mvcgen
  | @refl α hα =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    unfold castInterAux
    mvcgen

set_option maxHeartbeats 4000000 in
/-- Declarations-delta spec of the `castUnion` wrapper: the direct (equal
char-pred) branch only `freshVar`s (`Dl = []`); the loosening branches delegate to
`castUnionAux_decls_bv`. -/
theorem castUnion_decls_bv (S T : SMT.Term) (sS sT : SMTType) {used : List SMT.𝒱} {n : ℕ}
    {decl : SMT.Chunk}
    (hbvS : ∀ v ∈ SMT.bv S, v ∈ used) (hbvT : ∀ v ∈ SMT.bv T, v ∈ used) :
    ⦃ fun (⟨E, _Λ'⟩ : EncoderState) ↦
        ⌜E.freshvarsc = n ∧ E.usedVars = used ∧ E.declarations = decl⌝ ⦄
    castUnion (S, sS) (T, sT)
    ⦃ ⇓? (_ : SMT.Term × SMTType) (⟨E', _Γ'⟩ : EncoderState) =>
        ⌜∃ Dl : SMT.Chunk, E'.declarations = decl ++ Dl ∧ DeltaBvOk Dl E'.usedVars
          ∧ used ⊆ E'.usedVars⌝ ⦄ := by
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, rfl⟩ := pre
  unfold castUnion
  split
  split
  rename_i heqA _ _ _ heqB
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heqA
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heqB
  split_ifs with heq hsub1 hsub2
  · subst heq
    split
    · mspec SMT.freshVar_spec_decls
      mrename_i pre2
      mintro ∀St₂
      mpure pre2
      obtain ⟨St₂_used_eq, St₂_decl⟩ := pre2
      mspec (Std.Do.Triple.and _ SMT.eraseFromContext_spec
        (SMT.eraseFromContext_decls (decl := St₂.env.declarations)))
      mrename_i preE
      mintro ∀St₃
      mpure preE
      obtain ⟨⟨_, _, St₃_used_eq⟩, St₃_decl⟩ := preE
      mspec Std.Do.Spec.pure
      mpure_intro
      refine ⟨[], ?_, DeltaBvOk_nil, fun v hv => ?_⟩
      · rw [St₃_decl, St₂_decl, List.append_nil]
      · rw [St₃_used_eq, St₂_used_eq]; exact List.mem_cons_of_mem _ hv
    all_goals mvcgen
  · mspec (castUnionAux_decls_bv _ S T hbvS)
  · mspec (castUnionAux_decls_bv _ T S hbvT)
  · mvcgen

set_option maxHeartbeats 4000000 in
/-- Declarations-delta spec of the `castInter` wrapper (identical shape to
`castUnion`). -/
theorem castInter_decls_bv (S T : SMT.Term) (sS sT : SMTType) {used : List SMT.𝒱} {n : ℕ}
    {decl : SMT.Chunk}
    (hbvS : ∀ v ∈ SMT.bv S, v ∈ used) (hbvT : ∀ v ∈ SMT.bv T, v ∈ used) :
    ⦃ fun (⟨E, _Λ'⟩ : EncoderState) ↦
        ⌜E.freshvarsc = n ∧ E.usedVars = used ∧ E.declarations = decl⌝ ⦄
    castInter (S, sS) (T, sT)
    ⦃ ⇓? (_ : SMT.Term × SMTType) (⟨E', _Γ'⟩ : EncoderState) =>
        ⌜∃ Dl : SMT.Chunk, E'.declarations = decl ++ Dl ∧ DeltaBvOk Dl E'.usedVars
          ∧ used ⊆ E'.usedVars⌝ ⦄ := by
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, rfl⟩ := pre
  unfold castInter
  split
  split
  rename_i heqA _ _ _ heqB
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heqA
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heqB
  split_ifs with heq hsub1 hsub2
  · subst heq
    split
    · mspec SMT.freshVar_spec_decls
      mrename_i pre2
      mintro ∀St₂
      mpure pre2
      obtain ⟨St₂_used_eq, St₂_decl⟩ := pre2
      mspec (Std.Do.Triple.and _ SMT.eraseFromContext_spec
        (SMT.eraseFromContext_decls (decl := St₂.env.declarations)))
      mrename_i preE
      mintro ∀St₃
      mpure preE
      obtain ⟨⟨_, _, St₃_used_eq⟩, St₃_decl⟩ := preE
      mspec Std.Do.Spec.pure
      mpure_intro
      refine ⟨[], ?_, DeltaBvOk_nil, fun v hv => ?_⟩
      · rw [St₃_decl, St₂_decl, List.append_nil]
      · rw [St₃_used_eq, St₂_used_eq]; exact List.mem_cons_of_mem _ hv
    all_goals mvcgen
  · mspec (castInterAux_decls_bv _ S T hbvS)
  · mspec (castInterAux_decls_bv _ T S hbvT)
  · mvcgen
set_option maxHeartbeats 4000000 in
/-- Declarations-delta spec of `castApp`. The simple branches loosen one argument
(`declareConst` + `addSpec`); the relation→function branches additionally declare a
function helper `f!!` and `addSpec` a spec `f!!_spec` whose only bound variables are
the freshly-introduced quantifier names `u`, `v`. -/
theorem castApp_decls_bv (f x : SMT.Term) (sf sx : SMTType) {used : List SMT.𝒱} {n : ℕ}
    {decl : SMT.Chunk}
    (hbvf : ∀ v ∈ SMT.bv f, v ∈ used) (hbvx : ∀ v ∈ SMT.bv x, v ∈ used) :
    ⦃ fun (⟨E, _Λ'⟩ : EncoderState) ↦
        ⌜E.freshvarsc = n ∧ E.usedVars = used ∧ E.declarations = decl⌝ ⦄
    castApp (f, sf) (x, sx)
    ⦃ ⇓? (_ : SMT.Term × SMTType) (⟨E', _Γ'⟩ : EncoderState) =>
        ⌜∃ Dl : SMT.Chunk, E'.declarations = decl ++ Dl ∧ DeltaBvOk Dl E'.usedVars
          ∧ used ⊆ E'.usedVars⌝ ⦄ := by
  unfold castApp
  mvcgen
  case vc3.h_2.isTrue =>
    rename_i hxeq hfeq _ St hpre
    obtain ⟨rfl, rfl, rfl⟩ := hpre
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hxeq
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hfeq
    mspec (loosenAux_prf_bv_declsEq _ hbvf)
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨L_used, L_bv, L_used_sub, L_decl⟩ := pre
    unfold SMT.declareConstWithSpec
    mspec Std.Do.Spec.bind
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, hd_used, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨hs_decl, _, _, hs_used, _⟩ := pres
    mspec Std.Do.Spec.pure
    mpure_intro
    have lift : ∀ {w}, w ∈ St₁.env.usedVars → w ∈ St₁s.env.usedVars := fun {w} h => by
      rw [hs_used, hd_used]; exact h
    exact ⟨_,
      by rw [hs_decl, hd_decl, L_decl, List.concat_eq_append, List.concat_eq_append,
        List.append_assoc],
      DeltaBvOk.append (DeltaBvOk.declare_const (lift L_used))
        (DeltaBvOk.define_fun_spec (fun w hw => lift (L_bv w hw))),
      fun v hv => lift (L_used_sub hv)⟩
  case vc4.h_2.isFalse.isTrue =>
    rename_i hxeq hfeq _ _ St hpre
    obtain ⟨rfl, rfl, rfl⟩ := hpre
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hxeq
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hfeq
    mspec (loosenAux_prf_bv_declsEq _ hbvx)
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨L_used, L_bv, L_used_sub, L_decl⟩ := pre
    unfold SMT.declareConstWithSpec
    mspec Std.Do.Spec.bind
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, hd_used, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨hs_decl, _, _, hs_used, _⟩ := pres
    mspec Std.Do.Spec.pure
    mpure_intro
    have lift : ∀ {w}, w ∈ St₁.env.usedVars → w ∈ St₁s.env.usedVars := fun {w} h => by
      rw [hs_used, hd_used]; exact h
    exact ⟨_,
      by rw [hs_decl, hd_decl, L_decl, List.concat_eq_append, List.concat_eq_append,
        List.append_assoc],
      DeltaBvOk.append (DeltaBvOk.declare_const (lift L_used))
        (DeltaBvOk.define_fun_spec (fun w hw => lift (L_bv w hw))),
      fun v hv => lift (L_used_sub hv)⟩
  case vc5.h_3.isTrue =>
    rename_i hxeq hfeq _ St hpre
    obtain ⟨rfl, rfl, rfl⟩ := hpre
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hxeq
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hfeq
    mspec (loosenAux_prf_bv_declsEq _ hbvf)
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨L_used, L_bv, L_used_sub, L_decl⟩ := pre
    unfold SMT.declareConstWithSpec
    mspec Std.Do.Spec.bind
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, hd_used, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨hs_decl, _, _, hs_used, _⟩ := pres
    mspec Std.Do.Spec.pure
    mpure_intro
    have lift : ∀ {w}, w ∈ St₁.env.usedVars → w ∈ St₁s.env.usedVars := fun {w} h => by
      rw [hs_used, hd_used]; exact h
    exact ⟨_,
      by rw [hs_decl, hd_decl, L_decl, List.concat_eq_append, List.concat_eq_append,
        List.append_assoc],
      DeltaBvOk.append (DeltaBvOk.declare_const (lift L_used))
        (DeltaBvOk.define_fun_spec (fun w hw => lift (L_bv w hw))),
      fun v hv => lift (L_used_sub hv)⟩
  case vc6.h_3.isFalse.isTrue =>
    rename_i hxeq hfeq _ _ St hpre
    obtain ⟨rfl, rfl, rfl⟩ := hpre
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hxeq
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hfeq
    mspec (loosenAux_prf_bv_declsEq _ hbvx)
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨L_used, L_bv, L_used_sub, L_decl⟩ := pre
    unfold SMT.declareConstWithSpec
    mspec Std.Do.Spec.bind
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, hd_used, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨hs_decl, _, _, hs_used, _⟩ := pres
    mspec Std.Do.Spec.pure
    mpure_intro
    have lift : ∀ {w}, w ∈ St₁.env.usedVars → w ∈ St₁s.env.usedVars := fun {w} h => by
      rw [hs_used, hd_used]; exact h
    exact ⟨_,
      by rw [hs_decl, hd_decl, L_decl, List.concat_eq_append, List.concat_eq_append,
        List.append_assoc],
      DeltaBvOk.append (DeltaBvOk.declare_const (lift L_used))
        (DeltaBvOk.define_fun_spec (fun w hw => lift (L_bv w hw))),
      fun v hv => lift (L_used_sub hv)⟩
  case vc1.h_1.isTrue =>
    rename_i hxeq hfeq _ St hpre
    obtain ⟨rfl, rfl, rfl⟩ := hpre
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hxeq
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hfeq
    mspec (loosenAux_prf_bv_declsEq _ hbvf)
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨f!_used, f!_bv, f!_used_sub, f!_decl⟩ := pre
    unfold SMT.declareConstWithSpec
    mspec Std.Do.Spec.bind
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, hd_used, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨hs_decl, _, _, hs_used, _⟩ := pres
    mspec SMT.freshVar_spec_decls
    mrename_i pre2
    mintro ∀St₂
    mpure pre2
    obtain ⟨St₂_used_eq, St₂_decl⟩ := pre2
    mspec SMT.declareConst_spec
    mrename_i pred2
    mintro ∀St₂d
    mpure pred2
    obtain ⟨hd2_decl, _, _, hd2_used, _⟩ := pred2
    mspec SMT.freshVar_spec_decls
    mrename_i pre3
    mintro ∀St₃
    mpure pre3
    obtain ⟨St₃_used_eq, St₃_decl⟩ := pre3
    mspec SMT.freshVar_spec_decls
    mrename_i pre4
    mintro ∀St₄
    mpure pre4
    obtain ⟨St₄_used_eq, St₄_decl⟩ := pre4
    mspec SMT.eraseFromContext_used_decls
    mrename_i pre5
    mintro ∀St5
    mpure pre5
    obtain ⟨St5_used_eq, St5_decl⟩ := pre5
    mspec SMT.eraseFromContext_used_decls
    mrename_i pre6
    mintro ∀St6
    mpure pre6
    obtain ⟨St6_used_eq, St6_decl⟩ := pre6
    mspec SMT.addSpec_spec
    mrename_i pres2
    mintro ∀St6s
    mpure pres2
    obtain ⟨hs2_decl, _, _, hs2_used, _⟩ := pres2
    rw [St6_used_eq, St5_used_eq] at hs2_used
    rw [St6_decl, St5_decl] at hs2_decl
    mspec Std.Do.Spec.pure
    mpure_intro
    have lift : ∀ {w}, w ∈ St₁.env.usedVars → w ∈ St6s.env.usedVars := fun {w} h => by
      rw [hs2_used, St₄_used_eq, St₃_used_eq, hd2_used, St₂_used_eq, hs_used, hd_used]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
    exact ⟨_,
      by rw [hs2_decl, St₄_decl, St₃_decl, hd2_decl, St₂_decl, hs_decl, hd_decl, f!_decl]
         simp only [List.concat_eq_append, List.append_assoc, List.cons_append, List.nil_append]
         rfl,
      by
        refine ⟨fun v hv => ?_, fun b hb v hv => ?_⟩
        · simp only [declVars, List.filterMap_cons, List.filterMap_nil, List.mem_cons,
            List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl
          · exact lift f!_used
          · rw [hs2_used, St₄_used_eq, St₃_used_eq, hd2_used, St₂_used_eq]
            exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
        · simp only [specBodies, List.filterMap_cons, List.filterMap_nil, List.mem_cons,
            List.not_mem_nil, or_false] at hb
          rcases hb with rfl | rfl
          · exact lift (f!_bv v hv)
          · simp only [SMT.bv, List.append_nil, List.mem_cons,
              List.not_mem_nil, or_false] at hv
            rcases hv with rfl | rfl
            · rw [hs2_used, St₄_used_eq, St₃_used_eq]
              exact List.mem_cons_of_mem _ List.mem_cons_self
            · rw [hs2_used, St₄_used_eq]; exact List.mem_cons_self,
      fun w hw => lift (f!_used_sub hw)⟩
  case vc2.h_1.isFalse.isTrue =>
    rename_i hxeq hfeq _ _ St hpre
    obtain ⟨rfl, rfl, rfl⟩ := hpre
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hxeq
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hfeq
    mspec (loosenAux_prf_bv_declsEq _ hbvx)
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨x!_used, x!_bv, x!_used_sub, x!_decl⟩ := pre
    unfold SMT.declareConstWithSpec
    mspec Std.Do.Spec.bind
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, hd_used, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨hs_decl, _, _, hs_used, _⟩ := pres
    mspec SMT.freshVar_spec_decls
    mrename_i pre2
    mintro ∀St₂
    mpure pre2
    obtain ⟨St₂_used_eq, St₂_decl⟩ := pre2
    mspec SMT.declareConst_spec
    mrename_i pred2
    mintro ∀St₂d
    mpure pred2
    obtain ⟨hd2_decl, _, _, hd2_used, _⟩ := pred2
    mspec SMT.freshVar_spec_decls
    mrename_i pre3
    mintro ∀St₃
    mpure pre3
    obtain ⟨St₃_used_eq, St₃_decl⟩ := pre3
    mspec SMT.freshVar_spec_decls
    mrename_i pre4
    mintro ∀St₄
    mpure pre4
    obtain ⟨St₄_used_eq, St₄_decl⟩ := pre4
    mspec SMT.eraseFromContext_used_decls
    mrename_i pre5
    mintro ∀St5
    mpure pre5
    obtain ⟨St5_used_eq, St5_decl⟩ := pre5
    mspec SMT.eraseFromContext_used_decls
    mrename_i pre6
    mintro ∀St6
    mpure pre6
    obtain ⟨St6_used_eq, St6_decl⟩ := pre6
    mspec SMT.addSpec_spec
    mrename_i pres2
    mintro ∀St6s
    mpure pres2
    obtain ⟨hs2_decl, _, _, hs2_used, _⟩ := pres2
    rw [St6_used_eq, St5_used_eq] at hs2_used
    rw [St6_decl, St5_decl] at hs2_decl
    mspec Std.Do.Spec.pure
    mpure_intro
    have lift : ∀ {w}, w ∈ St₁.env.usedVars → w ∈ St6s.env.usedVars := fun {w} h => by
      rw [hs2_used, St₄_used_eq, St₃_used_eq, hd2_used, St₂_used_eq, hs_used, hd_used]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
    exact ⟨_,
      by rw [hs2_decl, St₄_decl, St₃_decl, hd2_decl, St₂_decl, hs_decl, hd_decl, x!_decl]
         simp only [List.concat_eq_append, List.append_assoc, List.cons_append, List.nil_append]
         rfl,
      by
        refine ⟨fun v hv => ?_, fun b hb v hv => ?_⟩
        · simp only [declVars, List.filterMap_cons, List.filterMap_nil, List.mem_cons,
            List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl
          · exact lift x!_used
          · rw [hs2_used, St₄_used_eq, St₃_used_eq, hd2_used, St₂_used_eq]
            exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
        · simp only [specBodies, List.filterMap_cons, List.filterMap_nil, List.mem_cons,
            List.not_mem_nil, or_false] at hb
          rcases hb with rfl | rfl
          · exact lift (x!_bv v hv)
          · simp only [SMT.bv, List.append_nil, List.mem_append, List.mem_cons,
              List.not_mem_nil, or_false] at hv
            rcases hv with (rfl | rfl) | hf
            · rw [hs2_used, St₄_used_eq, St₃_used_eq]
              exact List.mem_cons_of_mem _ List.mem_cons_self
            · rw [hs2_used, St₄_used_eq]; exact List.mem_cons_self
            · exact lift (x!_used_sub (hbvf v hf)),
      fun w hw => lift (x!_used_sub hw)⟩

set_option maxHeartbeats 4000000 in
set_option maxHeartbeats 4000000 in
/-- Unified bound-variable / declarations-delta spec of `encodeTerm`: every bound
variable of the result lives in the final `usedVars`, `usedVars` grows, and the
declarations it appends form a chunk `Dl` whose declared names and `define_fun`
spec-body bound variables also live in the final `usedVars`. -/
theorem encodeTerm_bv_used
    (E : B.Env) {t : B.Term} {used : List SMT.𝒱} {n : ℕ} {decl : SMT.Chunk} :
    ⦃ fun (⟨E0, _Λ'⟩ : EncoderState) ↦
        ⌜E0.freshvarsc = n ∧ E0.usedVars = used ∧ E0.declarations = decl⌝ ⦄
    encodeTerm t E
    ⦃ ⇓? (⟨t', _σ⟩ : SMT.Term × SMTType) (⟨E', _Γ'⟩ : EncoderState) => ⌜
      (∀ v ∈ SMT.bv t', v ∈ E'.usedVars) ∧ used ⊆ E'.usedVars ∧
      ∃ Dl : SMT.Chunk, E'.declarations = decl ++ Dl ∧ DeltaBvOk Dl E'.usedVars ⌝⦄ := by
  induction t generalizing E n used decl with
  | int i =>
    mstart
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    rw [encodeTerm]
    mspec Std.Do.Spec.pure
    mpure_intro
    exact ⟨by intro v hv; simp [SMT.bv] at hv, fun _ h => h, [], by simp, DeltaBvOk_nil⟩
  | bool b =>
    mstart
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    rw [encodeTerm]
    mspec Std.Do.Spec.pure
    mpure_intro
    exact ⟨by intro v hv; simp [SMT.bv] at hv, fun _ h => h, [], by simp, DeltaBvOk_nil⟩
  | var v =>
    mstart
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    rw [encodeTerm]
    mvcgen
    case vc1 τ τ_lookup =>
      exact ⟨by intro v hv; simp [SMT.bv] at hv, fun _ h => h, [], by simp, DeltaBvOk_nil⟩
  | «ℤ» =>
    mstart
    mintro pre ∀S
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    rw [encodeTerm]
    mspec Std.Do.Spec.get_StateT
    mspec SMT.freshVar_spec_decls
    case post.success 𝓋 =>
      mrename_i pre
      mintro ∀S'
      mpure pre
      obtain ⟨used_eq, decl_eq⟩ := pre
      mspec Std.Do.Spec.modifyGet_StateT
      mspec Std.Do.Spec.pure
      mpure_intro
      refine ⟨?_, ?_, [], ?_, DeltaBvOk_nil⟩
      · intro v hv
        simp only [SMT.bv, List.append_nil, List.mem_singleton] at hv
        subst hv
        rw [used_eq]; exact List.mem_cons_self
      · rw [used_eq]; intro x hx; exact List.mem_cons_of_mem _ hx
      · rw [decl_eq, List.append_nil]
  | 𝔹 =>
    mstart
    mintro pre ∀S
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    rw [encodeTerm]
    mspec Std.Do.Spec.get_StateT
    mspec SMT.freshVar_spec_decls
    case post.success 𝓋 =>
      mrename_i pre
      mintro ∀S'
      mpure pre
      obtain ⟨used_eq, decl_eq⟩ := pre
      mspec Std.Do.Spec.modifyGet_StateT
      mspec Std.Do.Spec.pure
      mpure_intro
      refine ⟨?_, ?_, [], ?_, DeltaBvOk_nil⟩
      · intro v hv
        simp only [SMT.bv, List.append_nil, List.mem_singleton] at hv
        subst hv
        rw [used_eq]; exact List.mem_cons_self
      · rw [used_eq]; intro x hx; exact List.mem_cons_of_mem _ hx
      · rw [decl_eq, List.append_nil]
  | maplet x y x_ih y_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    rw [encodeTerm]
    mspec x_ih (E := E)
    rename_i out_x
    obtain ⟨x_enc, σx⟩ := out_x
    mrename_i prex
    mintro ∀σ_x
    mpure prex
    obtain ⟨x_bv_used, x_used_sub, Δx, hxdecl, hxok⟩ := prex
    mspec y_ih (E := E) (used := σ_x.env.usedVars) (decl := σ_x.env.declarations)
    rename_i out_y
    obtain ⟨y_enc, σy⟩ := out_y
    mrename_i prey
    mintro ∀σ_y
    mpure prey
    obtain ⟨y_bv_used, y_used_sub, Δy, hydecl, hyok⟩ := prey
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨?_, fun v hv => y_used_sub (x_used_sub hv), Δx ++ Δy, ?_, ?_⟩
    · intro v hv
      simp only [SMT.bv, List.mem_append] at hv
      rcases hv with hv | hv
      · exact y_used_sub (x_bv_used v hv)
      · exact y_bv_used v hv
    · rw [hydecl, hxdecl, List.append_assoc]
    · exact DeltaBvOk.append (hxok.mono y_used_sub) hyok
  | add x y x_ih y_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    rw [encodeTerm]
    mspec x_ih (E := E)
    rename_i out_x
    obtain ⟨x_enc, σx⟩ := out_x
    mrename_i prex
    mintro ∀σ_x
    mpure prex
    obtain ⟨x_bv_used, x_used_sub, Δx, hxdecl, hxok⟩ := prex
    split
    · rename_i heq
      injection heq with hxe hσe
      subst hσe
      subst hxe
      mspec y_ih (E := E) (used := σ_x.env.usedVars) (decl := σ_x.env.declarations)
      rename_i out_y
      obtain ⟨y_enc, σy⟩ := out_y
      mrename_i prey
      mintro ∀σ_y
      mpure prey
      obtain ⟨y_bv_used, y_used_sub, Δy, hydecl, hyok⟩ := prey
      split
      · rename_i heq2
        injection heq2 with hye hσe2
        subst hσe2
        subst hye
        mspec Std.Do.Spec.pure
        mpure_intro
        refine ⟨?_, fun v hv => y_used_sub (x_used_sub hv), Δx ++ Δy, ?_, ?_⟩
        · intro v hv
          simp only [SMT.bv, List.mem_append] at hv
          rcases hv with hv | hv
          · exact y_used_sub (x_bv_used v hv)
          · exact y_bv_used v hv
        · rw [hydecl, hxdecl, List.append_assoc]
        · exact DeltaBvOk.append (hxok.mono y_used_sub) hyok
      · exact wp_bind_throw _ _ _ _
    · exact wp_bind_throw _ _ _ _
  | sub x y x_ih y_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    rw [encodeTerm]
    mspec x_ih (E := E)
    rename_i out_x
    obtain ⟨x_enc, σx⟩ := out_x
    mrename_i prex
    mintro ∀σ_x
    mpure prex
    obtain ⟨x_bv_used, x_used_sub, Δx, hxdecl, hxok⟩ := prex
    split
    · rename_i heq
      injection heq with hxe hσe
      subst hσe
      subst hxe
      mspec y_ih (E := E) (used := σ_x.env.usedVars) (decl := σ_x.env.declarations)
      rename_i out_y
      obtain ⟨y_enc, σy⟩ := out_y
      mrename_i prey
      mintro ∀σ_y
      mpure prey
      obtain ⟨y_bv_used, y_used_sub, Δy, hydecl, hyok⟩ := prey
      split
      · rename_i heq2
        injection heq2 with hye hσe2
        subst hσe2
        subst hye
        mspec Std.Do.Spec.pure
        mpure_intro
        refine ⟨?_, fun v hv => y_used_sub (x_used_sub hv), Δx ++ Δy, ?_, ?_⟩
        · intro v hv
          simp only [SMT.bv, List.mem_append] at hv
          rcases hv with hv | hv
          · exact y_used_sub (x_bv_used v hv)
          · exact y_bv_used v hv
        · rw [hydecl, hxdecl, List.append_assoc]
        · exact DeltaBvOk.append (hxok.mono y_used_sub) hyok
      · exact wp_bind_throw _ _ _ _
    · exact wp_bind_throw _ _ _ _
  | mul x y x_ih y_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    rw [encodeTerm]
    mspec x_ih (E := E)
    rename_i out_x
    obtain ⟨x_enc, σx⟩ := out_x
    mrename_i prex
    mintro ∀σ_x
    mpure prex
    obtain ⟨x_bv_used, x_used_sub, Δx, hxdecl, hxok⟩ := prex
    split
    · rename_i heq
      injection heq with hxe hσe
      subst hσe
      subst hxe
      mspec y_ih (E := E) (used := σ_x.env.usedVars) (decl := σ_x.env.declarations)
      rename_i out_y
      obtain ⟨y_enc, σy⟩ := out_y
      mrename_i prey
      mintro ∀σ_y
      mpure prey
      obtain ⟨y_bv_used, y_used_sub, Δy, hydecl, hyok⟩ := prey
      split
      · rename_i heq2
        injection heq2 with hye hσe2
        subst hσe2
        subst hye
        mspec Std.Do.Spec.pure
        mpure_intro
        refine ⟨?_, fun v hv => y_used_sub (x_used_sub hv), Δx ++ Δy, ?_, ?_⟩
        · intro v hv
          simp only [SMT.bv, List.mem_append] at hv
          rcases hv with hv | hv
          · exact y_used_sub (x_bv_used v hv)
          · exact y_bv_used v hv
        · rw [hydecl, hxdecl, List.append_assoc]
        · exact DeltaBvOk.append (hxok.mono y_used_sub) hyok
      · exact wp_bind_throw _ _ _ _
    · exact wp_bind_throw _ _ _ _
  | le x y x_ih y_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    rw [encodeTerm]
    mspec x_ih (E := E)
    rename_i out_x
    obtain ⟨x_enc, σx⟩ := out_x
    mrename_i prex
    mintro ∀σ_x
    mpure prex
    obtain ⟨x_bv_used, x_used_sub, Δx, hxdecl, hxok⟩ := prex
    mspec y_ih (E := E) (used := σ_x.env.usedVars) (decl := σ_x.env.declarations)
    rename_i out_y
    obtain ⟨y_enc, σy⟩ := out_y
    mrename_i prey
    mintro ∀σ_y
    mpure prey
    obtain ⟨y_bv_used, y_used_sub, Δy, hydecl, hyok⟩ := prey
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨?_, fun v hv => y_used_sub (x_used_sub hv), Δx ++ Δy, ?_, ?_⟩
    · intro v hv
      simp only [SMT.bv, List.mem_append] at hv
      rcases hv with hv | hv
      · exact y_used_sub (x_bv_used v hv)
      · exact y_bv_used v hv
    · rw [hydecl, hxdecl, List.append_assoc]
    · exact DeltaBvOk.append (hxok.mono y_used_sub) hyok
  | and x y x_ih y_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    rw [encodeTerm]
    mspec x_ih (E := E)
    rename_i out_x
    obtain ⟨x_enc, σx⟩ := out_x
    mrename_i prex
    mintro ∀σ_x
    mpure prex
    obtain ⟨x_bv_used, x_used_sub, Δx, hxdecl, hxok⟩ := prex
    split
    · rename_i heq
      injection heq with hxe hσe
      subst hσe
      subst hxe
      mspec y_ih (E := E) (used := σ_x.env.usedVars) (decl := σ_x.env.declarations)
      rename_i out_y
      obtain ⟨y_enc, σy⟩ := out_y
      mrename_i prey
      mintro ∀σ_y
      mpure prey
      obtain ⟨y_bv_used, y_used_sub, Δy, hydecl, hyok⟩ := prey
      split
      · rename_i heq2
        injection heq2 with hye hσe2
        subst hσe2
        subst hye
        mspec Std.Do.Spec.pure
        mpure_intro
        refine ⟨?_, fun v hv => y_used_sub (x_used_sub hv), Δx ++ Δy, ?_, ?_⟩
        · intro v hv
          simp only [SMT.bv, List.mem_append] at hv
          rcases hv with hv | hv
          · exact y_used_sub (x_bv_used v hv)
          · exact y_bv_used v hv
        · rw [hydecl, hxdecl, List.append_assoc]
        · exact DeltaBvOk.append (hxok.mono y_used_sub) hyok
      · exact wp_bind_throw _ _ _ _
    · exact wp_bind_throw _ _ _ _
  | not x ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    rw [encodeTerm]
    mspec ih (E := E)
    rename_i out_x
    obtain ⟨x_enc, σx⟩ := out_x
    mrename_i prex
    mintro ∀σ_x
    mpure prex
    obtain ⟨x_bv_used, x_used_sub, Δx, hxdecl, hxok⟩ := prex
    split
    · rename_i heq
      injection heq with hxe hσe
      subst hσe
      subst hxe
      mspec Std.Do.Spec.pure
      mpure_intro
      refine ⟨?_, x_used_sub, Δx, hxdecl, hxok⟩
      intro v hv
      simp only [SMT.bv] at hv
      exact x_bv_used v hv
    · exact wp_bind_throw _ _ _ _
  | eq x y x_ih y_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    rw [encodeTerm]
    mspec x_ih (E := E)
    rename_i out_x
    obtain ⟨x_enc, σx⟩ := out_x
    mrename_i prex
    mintro ∀σ_x
    mpure prex
    obtain ⟨x_bv_used, x_used_sub, Δx, hxdecl, hxok⟩ := prex
    mspec y_ih (E := E) (used := σ_x.env.usedVars) (decl := σ_x.env.declarations)
    rename_i out_y
    obtain ⟨y_enc, σy⟩ := out_y
    mrename_i prey
    mintro ∀σ_y
    mpure prey
    obtain ⟨y_bv_used, y_used_sub, Δy, hydecl, hyok⟩ := prey
    mspec (Std.Do.Triple.and _
      (castEq_bv x_enc y_enc σx σy
        (fun v hv => y_used_sub (x_bv_used v hv)) y_bv_used)
      (castEq_decls_bv x_enc y_enc σx σy (decl := σ_y.env.declarations)
        (fun v hv => y_used_sub (x_bv_used v hv)) y_bv_used))
    mrename_i prez
    mintro ∀σ_z
    mpure prez
    obtain ⟨⟨z_bv, z_used_sub⟩, Δc, hcdecl, hcok, _⟩ := prez
    mpure_intro
    refine ⟨z_bv, fun v hv => z_used_sub (y_used_sub (x_used_sub hv)),
      Δx ++ Δy ++ Δc, ?_, ?_⟩
    · rw [hcdecl, hydecl, hxdecl]; simp only [List.append_assoc]
    · refine DeltaBvOk.append (DeltaBvOk.append ?_ ?_) hcok
      · exact (hxok.mono y_used_sub).mono z_used_sub
      · exact hyok.mono z_used_sub
  | mem x S x_ih S_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    rw [encodeTerm]
    mspec x_ih (E := E)
    rename_i out_x
    obtain ⟨x_enc, σx⟩ := out_x
    mrename_i prex
    mintro ∀σ_x
    mpure prex
    obtain ⟨x_bv_used, x_used_sub, Δx, hxdecl, hxok⟩ := prex
    mspec S_ih (E := E) (used := σ_x.env.usedVars) (decl := σ_x.env.declarations)
    rename_i out_S
    obtain ⟨S_enc, σS⟩ := out_S
    mrename_i preS
    mintro ∀σ_S
    mpure preS
    obtain ⟨S_bv_used, S_used_sub, ΔS, hSdecl, hSok⟩ := preS
    mspec (Std.Do.Triple.and _
      (castMembership_bv x_enc S_enc σx σS
        (fun v hv => S_used_sub (x_bv_used v hv)) S_bv_used)
      (castMembership_decls_bv x_enc S_enc σx σS (decl := σ_S.env.declarations)
        (fun v hv => S_used_sub (x_bv_used v hv)) S_bv_used))
    mrename_i prez
    mintro ∀σ_z
    mpure prez
    obtain ⟨⟨z_bv, z_used_sub⟩, Δc, hcdecl, hcok, _⟩ := prez
    mpure_intro
    refine ⟨z_bv, fun v hv => z_used_sub (S_used_sub (x_used_sub hv)),
      Δx ++ ΔS ++ Δc, ?_, ?_⟩
    · rw [hcdecl, hSdecl, hxdecl]; simp only [List.append_assoc]
    · refine DeltaBvOk.append (DeltaBvOk.append ?_ ?_) hcok
      · exact (hxok.mono S_used_sub).mono z_used_sub
      · exact hSok.mono z_used_sub
  | pow S ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    rw [encodeTerm]
    mspec ih (E := E)
    rename_i out_S
    obtain ⟨S_enc, σS⟩ := out_S
    mrename_i preS
    mintro ∀σ_S
    mpure preS
    obtain ⟨S_bv_used, S_used_sub, Δs, hsdecl, hsok⟩ := preS
    split
    · rename_i α heq
      subst heq
      mspec Std.Do.Spec.get_StateT
      mspec SMT.freshVar_spec_decls
      case post.success x =>
        mrename_i prex
        mintro ∀St₁
        mpure prex
        obtain ⟨St₁_used_eq, St₁_decl⟩ := prex
        mspec SMT.freshVar_spec_decls
        case post.success ℰ =>
          mrename_i preℰ
          mintro ∀St₂
          mpure preℰ
          obtain ⟨St₂_used_eq, St₂_decl⟩ := preℰ
          simp [modify]
          mspec Std.Do.Spec.modifyGet_StateT
          mpure_intro
          have lift : ∀ {w}, w ∈ σ_S.env.usedVars → w ∈ St₂.env.usedVars := fun {w} h => by
            rw [St₂_used_eq, St₁_used_eq]
            exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
          refine ⟨?_, ?_, Δs, ?_, ?_⟩
          · intro v hv
            simp only [SMT.bv, List.append_nil, List.mem_append, List.mem_cons,
              List.not_mem_nil, false_or, or_false] at hv
            rw [St₂_used_eq, St₁_used_eq]
            rcases hv with rfl | rfl | hvS
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ List.mem_cons_self
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (S_bv_used v hvS))
          · intro v hv
            rw [St₂_used_eq, St₁_used_eq]
            exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (S_used_sub hv))
          · rw [St₂_decl, St₁_decl, hsdecl]
          · exact hsok.mono (fun w hw => lift hw)
    · rename_i α γ heq
      subst heq
      mspec Std.Do.Spec.get_StateT
      mspec SMT.freshVar_spec_decls
      case post.success x =>
        mrename_i prex
        mintro ∀St₁
        mpure prex
        obtain ⟨St₁_used_eq, St₁_decl⟩ := prex
        mspec SMT.freshVar_spec_decls
        case post.success y =>
          mrename_i prey
          mintro ∀St₂
          mpure prey
          obtain ⟨St₂_used_eq, St₂_decl⟩ := prey
          mspec SMT.freshVar_spec_decls
          case post.success f =>
            mrename_i pref
            mintro ∀St₃
            mpure pref
            obtain ⟨St₃_used_eq, St₃_decl⟩ := pref
            simp [modify]
            mspec Std.Do.Spec.modifyGet_StateT
            mpure_intro
            have lift : ∀ {w}, w ∈ σ_S.env.usedVars → w ∈ St₃.env.usedVars := fun {w} h => by
              rw [St₃_used_eq, St₂_used_eq, St₁_used_eq]
              exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
            refine ⟨?_, ?_, Δs, ?_, ?_⟩
            · intro v hv
              simp only [SMT.bv, List.append_nil, List.mem_append, List.mem_cons,
                List.not_mem_nil, false_or, or_false] at hv
              rw [St₃_used_eq, St₂_used_eq, St₁_used_eq]
              rcases hv with rfl | (rfl | rfl) | hvS
              · exact List.mem_cons_self
              · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
              · exact List.mem_cons_of_mem _ List.mem_cons_self
              · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                  (List.mem_cons_of_mem _ (S_bv_used v hvS)))
            · intro v hv
              rw [St₃_used_eq, St₂_used_eq, St₁_used_eq]
              exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ (S_used_sub hv)))
            · rw [St₃_decl, St₂_decl, St₁_decl, hsdecl]
            · exact hsok.mono (fun w hw => lift hw)
    · mvcgen
  | cprod A C A_ih C_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    rw [encodeTerm]
    mspec A_ih (E := E)
    rename_i out_A
    obtain ⟨A_enc, σA⟩ := out_A
    mrename_i preA
    mintro ∀σ_A
    mpure preA
    obtain ⟨A_bv_used, A_used_sub, Δa, hadecl, haok⟩ := preA
    split
    · rename_i heqA
      injection heqA with hAe hσeA
      subst hσeA
      subst hAe
      mspec C_ih (E := E) (used := σ_A.env.usedVars) (decl := σ_A.env.declarations)
      rename_i out_C
      obtain ⟨C_enc, σC⟩ := out_C
      mrename_i preC
      mintro ∀σ_C
      mpure preC
      obtain ⟨C_bv_used, C_used_sub, Δc, hcdecl, hcok⟩ := preC
      split
      · rename_i heqC
        injection heqC with hCe hσeC
        subst hσeC
        subst hCe
        mspec SMT.freshVar_spec_decls
        case post.success p =>
          mrename_i prep
          mintro ∀St₁
          mpure prep
          obtain ⟨St₁_used_eq, St₁_decl⟩ := prep
          mspec SMT.freshVar_spec_decls
          case post.success a =>
            mrename_i prea
            mintro ∀St₂
            mpure prea
            obtain ⟨St₂_used_eq, St₂_decl⟩ := prea
            mspec SMT.freshVar_spec_decls
            case post.success b =>
              mrename_i preb
              mintro ∀St₃
              mpure preb
              obtain ⟨St₃_used_eq, St₃_decl⟩ := preb
              mspec (Std.Do.Triple.and _ SMT.eraseFromContext_spec
                (SMT.eraseFromContext_decls (decl := St₃.env.declarations)))
              mrename_i preEp
              mintro ∀StEp
              mpure preEp
              obtain ⟨⟨_, _, StEp_used_eq⟩, StEp_decl⟩ := preEp
              mspec (Std.Do.Triple.and _ SMT.eraseFromContext_spec
                (SMT.eraseFromContext_decls (decl := StEp.env.declarations)))
              mrename_i preEa
              mintro ∀StEa
              mpure preEa
              obtain ⟨⟨_, _, StEa_used_eq⟩, StEa_decl⟩ := preEa
              mspec (Std.Do.Triple.and _ SMT.eraseFromContext_spec
                (SMT.eraseFromContext_decls (decl := StEa.env.declarations)))
              mrename_i preEb
              mintro ∀StEb
              mpure preEb
              obtain ⟨⟨_, _, StEb_used_eq⟩, StEb_decl⟩ := preEb
              mspec Std.Do.Spec.pure
              mpure_intro
              rw [StEb_used_eq, StEa_used_eq, StEp_used_eq]
              have liftC : ∀ {w}, w ∈ σ_C.env.usedVars → w ∈ St₃.env.usedVars := fun {w} h => by
                rw [St₃_used_eq, St₂_used_eq, St₁_used_eq]
                exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
              refine ⟨?_, ?_, Δa ++ Δc, ?_, ?_⟩
              · intro v hv
                simp only [SMT.bv, List.append_nil, List.mem_append,
                  List.mem_cons, List.not_mem_nil, or_false] at hv
                rw [St₃_used_eq, St₂_used_eq, St₁_used_eq]
                rcases hv with rfl | (rfl | rfl) | hvA | hvC
                · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
                · exact List.mem_cons_of_mem _ List.mem_cons_self
                · exact List.mem_cons_self
                · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                    (List.mem_cons_of_mem _ (C_used_sub (A_bv_used v hvA))))
                · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                    (List.mem_cons_of_mem _ (C_bv_used v hvC)))
              · intro v hv
                rw [St₃_used_eq, St₂_used_eq, St₁_used_eq]
                exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                  (List.mem_cons_of_mem _ (C_used_sub (A_used_sub hv))))
              · rw [StEb_decl, StEa_decl, StEp_decl, St₃_decl, St₂_decl, St₁_decl, hcdecl, hadecl,
                  List.append_assoc]
              · exact DeltaBvOk.append (haok.mono (fun w hw => liftC (C_used_sub hw)))
                  (hcok.mono (fun w hw => liftC hw))
      · exact wp_bind_throw _ _ _ _
    · exact wp_bind_throw _ _ _ _
  | union S T S_ih T_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    rw [encodeTerm]
    mspec S_ih (E := E)
    rename_i out_S
    obtain ⟨S_enc, σS⟩ := out_S
    mrename_i preS
    mintro ∀σ_S
    mpure preS
    obtain ⟨S_bv_used, S_used_sub, ΔS, hSdecl, hSok⟩ := preS
    mspec T_ih (E := E) (used := σ_S.env.usedVars) (decl := σ_S.env.declarations)
    rename_i out_T
    obtain ⟨T_enc, σT⟩ := out_T
    mrename_i preT
    mintro ∀σ_T
    mpure preT
    obtain ⟨T_bv_used, T_used_sub, ΔT, hTdecl, hTok⟩ := preT
    mspec (Std.Do.Triple.and _
      (castUnion_bv S_enc T_enc σS σT
        (fun v hv => T_used_sub (S_bv_used v hv)) T_bv_used)
      (castUnion_decls_bv S_enc T_enc σS σT (decl := σ_T.env.declarations)
        (fun v hv => T_used_sub (S_bv_used v hv)) T_bv_used))
    mrename_i prez
    mintro ∀σ_z
    mpure prez
    obtain ⟨⟨z_bv, z_used_sub⟩, Δc, hcdecl, hcok, _⟩ := prez
    mpure_intro
    refine ⟨z_bv, fun v hv => z_used_sub (T_used_sub (S_used_sub hv)),
      ΔS ++ ΔT ++ Δc, ?_, ?_⟩
    · rw [hcdecl, hTdecl, hSdecl]; simp only [List.append_assoc]
    · refine DeltaBvOk.append (DeltaBvOk.append ?_ ?_) hcok
      · exact (hSok.mono T_used_sub).mono z_used_sub
      · exact hTok.mono z_used_sub
  | inter S T S_ih T_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    rw [encodeTerm]
    mspec S_ih (E := E)
    rename_i out_S
    obtain ⟨S_enc, σS⟩ := out_S
    mrename_i preS
    mintro ∀σ_S
    mpure preS
    obtain ⟨S_bv_used, S_used_sub, ΔS, hSdecl, hSok⟩ := preS
    mspec T_ih (E := E) (used := σ_S.env.usedVars) (decl := σ_S.env.declarations)
    rename_i out_T
    obtain ⟨T_enc, σT⟩ := out_T
    mrename_i preT
    mintro ∀σ_T
    mpure preT
    obtain ⟨T_bv_used, T_used_sub, ΔT, hTdecl, hTok⟩ := preT
    mspec (Std.Do.Triple.and _
      (castInter_bv S_enc T_enc σS σT
        (fun v hv => T_used_sub (S_bv_used v hv)) T_bv_used)
      (castInter_decls_bv S_enc T_enc σS σT (decl := σ_T.env.declarations)
        (fun v hv => T_used_sub (S_bv_used v hv)) T_bv_used))
    mrename_i prez
    mintro ∀σ_z
    mpure prez
    obtain ⟨⟨z_bv, z_used_sub⟩, Δc, hcdecl, hcok, _⟩ := prez
    mpure_intro
    refine ⟨z_bv, fun v hv => z_used_sub (T_used_sub (S_used_sub hv)),
      ΔS ++ ΔT ++ Δc, ?_, ?_⟩
    · rw [hcdecl, hTdecl, hSdecl]; simp only [List.append_assoc]
    · refine DeltaBvOk.append (DeltaBvOk.append ?_ ?_) hcok
      · exact (hSok.mono T_used_sub).mono z_used_sub
      · exact hTok.mono z_used_sub
  | card S ih =>
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    simp only [encodeTerm] <;> mvcgen
  | app f x f_ih x_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    rw [encodeTerm]
    mspec f_ih (E := E)
    rename_i out_f
    obtain ⟨f_enc, σf⟩ := out_f
    mrename_i pref
    mintro ∀σ_f
    mpure pref
    obtain ⟨f_bv_used, f_used_sub, Δf, hfdecl, hfok⟩ := pref
    mspec x_ih (E := E) (used := σ_f.env.usedVars) (decl := σ_f.env.declarations)
    rename_i out_x
    obtain ⟨x_enc, σx⟩ := out_x
    mrename_i prex
    mintro ∀σ_x
    mpure prex
    obtain ⟨x_bv_used, x_used_sub, Δx, hxdecl, hxok⟩ := prex
    mspec (Std.Do.Triple.and _
      (castApp_bv f_enc x_enc σf σx
        (fun v hv => x_used_sub (f_bv_used v hv)) x_bv_used)
      (castApp_decls_bv f_enc x_enc σf σx (decl := σ_x.env.declarations)
        (fun v hv => x_used_sub (f_bv_used v hv)) x_bv_used))
    mrename_i prez
    mintro ∀σ_z
    mpure prez
    obtain ⟨⟨z_bv, z_used_sub⟩, Δc, hcdecl, hcok, _⟩ := prez
    mpure_intro
    refine ⟨z_bv, fun v hv => z_used_sub (x_used_sub (f_used_sub hv)),
      Δf ++ Δx ++ Δc, ?_, ?_⟩
    · rw [hcdecl, hxdecl, hfdecl]; simp only [List.append_assoc]
    · refine DeltaBvOk.append (DeltaBvOk.append ?_ ?_) hcok
      · exact (hfok.mono x_used_sub).mono z_used_sub
      · exact hxok.mono z_used_sub
  | collect vs D P D_ih P_ih =>
    mstart
    mintro pre ∀St₀
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    rw [encodeTerm]
    mspec D_ih (E := E)
    rename_i out_D
    obtain ⟨D_enc, τD⟩ := out_D
    mrename_i preD
    mintro ∀St₁
    mpure preD
    obtain ⟨D_bv_used, D_used_sub, ΔD, hDdecl, hDok⟩ := preD
    split
    · -- function-`D` arm: τD = .fun α' (.option β')
      rename_i α' β' heqD
      split
      · -- arity matches
        rename_i harity
        set αs' := α'.fromProdl (vs.length - 2) with αs'_def
        mspec Std.Do.Spec.pure
        mspec (Std.Do.Triple.and _
          (encodeTerm_state.modifyTypes_forIn_spec (vs.zip (αs'.concat β')))
          (encodeTerm_state.modifyTypes_forIn_decls (vs.zip (αs'.concat β')) (decl := St₁.env.declarations)))
        mrename_i pre2
        mintro ∀St₂
        mpure pre2
        obtain ⟨⟨_, _, St₂_used⟩, St₂_decl⟩ := pre2
        mspec P_ih (E := E) (used := St₂.env.usedVars) (decl := St₂.env.declarations)
        rename_i out_P
        mrename_i preP
        mintro ∀St₃
        mpure preP
        obtain ⟨P_bv_used, P_used_sub, ΔP, hPdecl, hPok⟩ := preP
        split
        · -- P : .bool
          rename_i heqP
          mspec (Std.Do.Triple.and _
            (SMT.freshVarList_spec αs')
            (SMT.freshVarList_decls αs' (decl := St₃.env.declarations)))
          rename_i xs
          mrename_i pre4
          mintro ∀St₄
          mpure pre4
          obtain ⟨⟨_, _, _, _, _, St₄_used, _⟩, St₄_decl⟩ := pre4
          have St₁_to_St₃ : ∀ {v}, v ∈ St₁.env.usedVars → v ∈ St₃.env.usedVars :=
            fun {v} h => P_used_sub (by rw [St₂_used]; exact h)
          have hbvD_lifted : ∀ v ∈ SMT.bv D_enc, v ∈ St₄.env.usedVars :=
            fun v hv => by
              rw [St₄_used]; exact List.mem_append_right _ (St₁_to_St₃ (D_bv_used v hv))
          have hbvXs_lifted : ∀ v ∈ SMT.bv ((xs.map SMT.Term.var).toPairl), v ∈ St₄.env.usedVars :=
            fun v hv => by
              rw [bv_toPairl_nil (fun t ht => by
                rw [List.mem_map] at ht; obtain ⟨z, _, rfl⟩ := ht; simp [SMT.bv])] at hv
              exact absurd hv List.not_mem_nil
          mspec (Std.Do.Triple.and _
            (castApp_bv D_enc ((xs.map SMT.Term.var).toPairl) (α'.fun β'.option)
              αs'.toProdl hbvD_lifted hbvXs_lifted)
            (castApp_decls_bv D_enc ((xs.map SMT.Term.var).toPairl) (α'.fun β'.option)
              αs'.toProdl (decl := St₄.env.declarations) hbvD_lifted hbvXs_lifted))
          mrename_i pre5
          mintro ∀St₅
          mpure pre5
          obtain ⟨⟨Dxs_bv, Dxs_used_sub⟩, Δca, hcadecl, hcaok, _⟩ := pre5
          mspec Std.Do.Spec.pure
          mpure_intro
          have lift3 : ∀ {w}, w ∈ St₃.env.usedVars → w ∈ St₅.env.usedVars := fun {w} h =>
            Dxs_used_sub (by rw [St₄_used]; exact List.mem_append_right _ h)
          have liftXs : ∀ {w}, w ∈ xs → w ∈ St₅.env.usedVars := fun {w} h =>
            Dxs_used_sub (by rw [St₄_used]; exact List.mem_append_left _ (List.mem_reverse.mpr h))
          refine ⟨?_, fun v hv => lift3 (St₁_to_St₃ (D_used_sub hv)), ΔD ++ ΔP ++ Δca, ?_, ?_⟩
          · intro v hv
            simp only [noneCast, SMT.bv, List.nil_append, List.append_nil, List.mem_append,
              List.not_mem_nil, false_or, or_false] at hv
            rcases hv with hvxs | hvP | hvDxs
            · exact liftXs hvxs
            · refine bv_substList_subset_of (U := St₅.env.usedVars) ?_ ?_ v hvP
              · exact fun w hw => lift3 (P_bv_used w hw)
              · intro t ht w hw
                simp only [List.concat_eq_append, List.mem_append, List.mem_singleton] at ht
                rcases ht with hxs | rfl
                · rw [List.mem_map] at hxs
                  obtain ⟨z, _, rfl⟩ := hxs
                  simp only [SMT.bv, List.not_mem_nil] at hw
                · exact Dxs_bv w hw
            · exact Dxs_bv v hvDxs
          · -- declarations: St₅ = St₄ ++ Δca = St₃ ++ Δca = (St₂ ++ ΔP) ++ Δca = decl ++ ΔD ++ ΔP ++ Δca
            rw [hcadecl, St₄_decl, hPdecl, St₂_decl, hDdecl]; simp only [List.append_assoc]
          · -- DeltaBvOk (ΔD ++ ΔP ++ Δca) St₅.usedVars
            refine DeltaBvOk.append (DeltaBvOk.append (hDok.mono (fun w hw => lift3 (St₁_to_St₃ hw)))
              (hPok.mono (fun w hw => lift3 hw))) hcaok
        · first
          | exact wp_bind_throw _ _ _ _
          | (mvcgen)
      · first
        | exact wp_bind_throw _ _ _ _
        | (mvcgen)
    · -- set-`D` arm: τD = .fun τ .bool  (≈ lambda)
      rename_i τ heqD
      mspec (Std.Do.Triple.and _
        (SMT.addToContext_forIn_spec (vs.zip (τ.fromProdl (vs.length - 1))))
        (SMT.addToContext_forIn_decls (vs.zip (τ.fromProdl (vs.length - 1))) (decl := St₁.env.declarations)))
      mrename_i pre2
      mintro ∀St₂
      mpure pre2
      obtain ⟨⟨_, _, St₂_used⟩, St₂_decl⟩ := pre2
      mspec P_ih (E := E) (used := St₂.env.usedVars) (decl := St₂.env.declarations)
      rename_i out_P
      mrename_i preP
      mintro ∀St₃
      mpure preP
      obtain ⟨P_bv_used, P_used_sub, ΔP, hPdecl, hPok⟩ := preP
      split
      · rename_i heqP
        mspec (Std.Do.Triple.and _ SMT.freshVar_spec (SMT.freshVar_decls (decl := St₃.env.declarations)))
        case post.success z =>
          mrename_i prez
          mintro ∀St₄
          mpure prez
          obtain ⟨⟨_, _, _, St₄_used_eq, _⟩, St₄_decl⟩ := prez
          mspec (Std.Do.Triple.and _ SMT.eraseFromContext_spec (SMT.eraseFromContext_decls (decl := St₄.env.declarations)))
          mrename_i pree
          mintro ∀St₅
          mpure pree
          obtain ⟨⟨_, _, St₅_used⟩, St₅_decl⟩ := pree
          mspec Std.Do.Spec.pure
          mpure_intro
          have St₁_sub_St₂ : ∀ {w}, w ∈ St₁.env.usedVars → w ∈ St₂.env.usedVars :=
            fun {w} h => by rw [St₂_used]; exact encodeTerm_state.mem_foldl_cons_of_mem _ _ h
          have lift : ∀ {w}, w ∈ St₃.env.usedVars → w ∈ St₅.env.usedVars := fun {w} h => by
            rw [St₅_used, St₄_used_eq]; exact List.mem_cons_of_mem _ h
          refine ⟨?_, fun v hv => lift (P_used_sub (St₁_sub_St₂ (D_used_sub hv))), ΔD ++ ΔP, ?_, ?_⟩
          · intro v hv
            simp only [SMT.bv, List.nil_append, List.append_nil, List.mem_append, List.mem_cons,
              List.not_mem_nil, false_or, or_false] at hv
            rcases hv with rfl | hvD | hvP
            · rw [St₅_used, St₄_used_eq]; exact List.mem_cons_self
            · exact lift (P_used_sub (St₁_sub_St₂ (D_bv_used v hvD)))
            · rw [SMT_bv_substList_eq (fun t ht => bv_toDestPair_nil (by simp [SMT.bv]) ht)] at hvP
              exact lift (P_bv_used v hvP)
          · -- declarations: St₅ = St₄ = St₃ = St₂ ++ ΔP = St₁ ++ ΔP = decl ++ ΔD ++ ΔP
            rw [St₅_decl, St₄_decl, hPdecl, St₂_decl, hDdecl, List.append_assoc]
          · -- DeltaBvOk (ΔD ++ ΔP) St₅.usedVars
            refine DeltaBvOk.append (hDok.mono (fun w hw => lift (P_used_sub (St₁_sub_St₂ hw))))
              (hPok.mono (fun w hw => lift hw))
      · first
        | exact wp_bind_throw _ _ _ _
        | (mvcgen)
    · first
        | exact wp_bind_throw _ _ _ _
        | (mvcgen)
  | lambda vs D P D_ih P_ih =>
    mstart
    mintro pre ∀St₀
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    rw [encodeTerm]
    mspec D_ih (E := E)
    rename_i out_D
    obtain ⟨D_enc, τD⟩ := out_D
    mrename_i preD
    mintro ∀St₁
    mpure preD
    obtain ⟨D_bv_used, D_used_sub, ΔD, hDdecl, hDok⟩ := preD
    split
    · rename_i τ' heqτD
      mspec (Std.Do.Triple.and _
        (SMT.addToContext_forIn_spec (vs.zip (τ'.fromProdl (vs.length - 1))))
        (SMT.addToContext_forIn_decls (vs.zip (τ'.fromProdl (vs.length - 1))) (decl := St₁.env.declarations)))
      mrename_i pre2
      mintro ∀St₂
      mpure pre2
      obtain ⟨⟨_, _, St₂_used⟩, St₂_decl⟩ := pre2
      mspec P_ih (E := E) (used := St₂.env.usedVars) (decl := St₂.env.declarations)
      rename_i out_P
      obtain ⟨P_enc, σP⟩ := out_P
      mrename_i preP
      mintro ∀St₃
      mpure preP
      obtain ⟨P_bv_used, P_used_sub, ΔP, hPdecl, hPok⟩ := preP
      mspec (Std.Do.Triple.and _ SMT.freshVar_spec (SMT.freshVar_decls (decl := St₃.env.declarations)))
      case post.success xy =>
        mrename_i prexy
        mintro ∀St₄
        mpure prexy
        obtain ⟨⟨_, _, _, St₄_used_eq, _⟩, St₄_decl⟩ := prexy
        mspec (Std.Do.Triple.and _ SMT.eraseFromContext_spec (SMT.eraseFromContext_decls (decl := St₄.env.declarations)))
        mrename_i pree
        mintro ∀St₅
        mpure pree
        obtain ⟨⟨_, _, St₅_used⟩, St₅_decl⟩ := pree
        mspec Std.Do.Spec.pure
        mpure_intro
        have St₁_sub_St₂ : ∀ {v}, v ∈ St₁.env.usedVars → v ∈ St₂.env.usedVars :=
          fun {v} h => by rw [St₂_used]; exact encodeTerm_state.mem_foldl_cons_of_mem _ _ h
        have lift : ∀ {v}, v ∈ St₃.env.usedVars → v ∈ St₅.env.usedVars := fun {v} h => by
          rw [St₅_used, St₄_used_eq]; exact List.mem_cons_of_mem _ h
        refine ⟨?_, fun v hv => lift (P_used_sub (St₁_sub_St₂ (D_used_sub hv))), ΔD ++ ΔP, ?_, ?_⟩
        · intro v hv
          simp only [SMT.bv, List.nil_append, List.append_nil, List.mem_append, List.mem_cons,
            List.not_mem_nil, false_or, or_false] at hv
          rcases hv with rfl | hvD | hvPx
          · rw [St₅_used, St₄_used_eq]; exact List.mem_cons_self
          · exact lift (P_used_sub (St₁_sub_St₂ (D_bv_used v hvD)))
          · rw [SMT_bv_substList_eq (fun t ht => bv_toDestPair_nil (by simp [SMT.bv]) ht)] at hvPx
            exact lift (P_bv_used v hvPx)
        · -- declarations: St₅ = St₄ = St₃ = St₂ ++ ΔP = St₁ ++ ΔP = decl ++ ΔD ++ ΔP
          rw [St₅_decl, St₄_decl, hPdecl, St₂_decl, hDdecl, List.append_assoc]
        · -- DeltaBvOk (ΔD ++ ΔP) St₅.usedVars
          refine DeltaBvOk.append (hDok.mono (fun w hw => ?_)) (hPok.mono (fun w hw => lift hw))
          exact lift (P_used_sub (St₁_sub_St₂ hw))
    · first
      | exact wp_bind_throw _ _ _ _
      | (mvcgen)
  | pfun A B A_ih B_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    rw [encodeTerm]
    mspec A_ih (E := E)
    rename_i out_A
    obtain ⟨A_enc, σA⟩ := out_A
    mrename_i preA
    mintro ∀σ_A
    mpure preA
    obtain ⟨A_bv_used, A_used_sub, Δa, hadecl, haok⟩ := preA
    split
    · rename_i heqA
      injection heqA with hAe hσeA
      subst hσeA
      subst hAe
      mspec B_ih (E := E) (used := σ_A.env.usedVars) (decl := σ_A.env.declarations)
      rename_i out_B
      obtain ⟨B_enc, σB⟩ := out_B
      mrename_i preB
      mintro ∀σ_B
      mpure preB
      obtain ⟨B_bv_used, B_used_sub, Δb, hbdecl, hbok⟩ := preB
      split
      · rename_i heqB
        injection heqB with hBe hσeB
        subst hσeB
        subst hBe
        mspec SMT.freshVar_spec_decls
        mrename_i preR
        mintro ∀St₁
        mpure preR
        obtain ⟨St₁_used_eq, St₁_decl⟩ := preR
        mspec SMT.freshVar_spec_decls
        mrename_i prex
        mintro ∀St₂
        mpure prex
        obtain ⟨St₂_used_eq, St₂_decl⟩ := prex
        mspec SMT.freshVar_spec_decls
        mrename_i prey
        mintro ∀St₃
        mpure prey
        obtain ⟨St₃_used_eq, St₃_decl⟩ := prey
        mspec SMT.freshVar_spec_decls
        mrename_i prey'
        mintro ∀St₄
        mpure prey'
        obtain ⟨St₄_used_eq, St₄_decl⟩ := prey'
        -- erase the four leaked binders `R`, `x`, `y`, `y'`; each leaves `usedVars`
        -- and `declarations` unchanged.
        mspec (Std.Do.Triple.and _ SMT.eraseFromContext_spec
          (SMT.eraseFromContext_decls (decl := St₄.env.declarations)))
        mrename_i preER
        mintro ∀StER
        mpure preER
        obtain ⟨⟨_, _, StER_used_eq⟩, StER_decl⟩ := preER
        mspec (Std.Do.Triple.and _ SMT.eraseFromContext_spec
          (SMT.eraseFromContext_decls (decl := StER.env.declarations)))
        mrename_i preEx
        mintro ∀StEx
        mpure preEx
        obtain ⟨⟨_, _, StEx_used_eq⟩, StEx_decl⟩ := preEx
        mspec (Std.Do.Triple.and _ SMT.eraseFromContext_spec
          (SMT.eraseFromContext_decls (decl := StEx.env.declarations)))
        mrename_i preEy
        mintro ∀StEy
        mpure preEy
        obtain ⟨⟨_, _, StEy_used_eq⟩, StEy_decl⟩ := preEy
        mspec (Std.Do.Triple.and _ SMT.eraseFromContext_spec
          (SMT.eraseFromContext_decls (decl := StEy.env.declarations)))
        mrename_i preEy'
        mintro ∀StEy'
        mpure preEy'
        obtain ⟨⟨_, _, StEy'_used_eq⟩, StEy'_decl⟩ := preEy'
        mspec Std.Do.Spec.pure
        mpure_intro
        rw [StEy'_used_eq, StEy_used_eq, StEx_used_eq, StER_used_eq]
        have lift : ∀ {v}, v ∈ σ_B.env.usedVars → v ∈ St₄.env.usedVars := fun {v} h => by
          rw [St₄_used_eq, St₃_used_eq, St₂_used_eq, St₁_used_eq]
          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)))
        refine ⟨?_, ?_, Δa ++ Δb, ?_, ?_⟩
        · intro v hv
          simp only [SMT.bv, List.nil_append, List.append_nil, List.mem_append, List.mem_cons,
            List.not_mem_nil, false_or, or_false] at hv
          rcases hv with rfl | (((rfl | rfl) | (hA | hB)) | (rfl | (rfl | rfl)))
          · rw [St₄_used_eq, St₃_used_eq, St₂_used_eq, St₁_used_eq]
            exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ List.mem_cons_self))
          · rw [St₄_used_eq, St₃_used_eq, St₂_used_eq]
            exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
          · rw [St₄_used_eq, St₃_used_eq]
            exact List.mem_cons_of_mem _ List.mem_cons_self
          · exact lift (B_used_sub (A_bv_used v hA))
          · exact lift (B_bv_used v hB)
          · rw [St₄_used_eq, St₃_used_eq, St₂_used_eq]
            exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
          · rw [St₄_used_eq, St₃_used_eq]
            exact List.mem_cons_of_mem _ List.mem_cons_self
          · rw [St₄_used_eq]; exact List.mem_cons_self
        · intro v hv
          exact lift (B_used_sub (A_used_sub hv))
        · rw [StEy'_decl, StEy_decl, StEx_decl, StER_decl,
            St₄_decl, St₃_decl, St₂_decl, St₁_decl, hbdecl, hadecl, List.append_assoc]
        · exact DeltaBvOk.append (haok.mono (fun w hw => lift (B_used_sub hw)))
            (hbok.mono (fun w hw => lift hw))
      · mvcgen
    · mvcgen
  | min S ih =>
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    simp only [encodeTerm] <;> mvcgen
  | max S ih =>
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    simp only [encodeTerm] <;> mvcgen
  | all vs D P D_ih P_ih =>
    mstart
    mintro pre ∀St₀
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    rw [encodeTerm]
    mspec D_ih (E := E)
    rename_i out_D
    obtain ⟨D_enc, τD⟩ := out_D
    mrename_i preD
    mintro ∀St₁
    mpure preD
    obtain ⟨D_bv_used, D_used_sub, ΔD, hDdecl, hDok⟩ := preD
    split
    · -- set-arm: τD = .fun τ .bool
      rename_i τ heqD
      split
      · -- arity matches: vs.length = tmp_τs.length
        rename_i hlen
        mspec (Std.Do.Triple.and _
          (encodeTerm_state.mapFinIdxM_all_state vs E.flags (τ.fromProdl (vs.length - 1)) hlen)
          (encodeTerm_state.mapFinIdxM_all_decls vs E.flags (τ.fromProdl (vs.length - 1)) hlen
            (decl := St₁.env.declarations)))
        rename_i τs
        mrename_i pre2
        mintro ∀St₂
        mpure pre2
        obtain ⟨⟨_, _, St₂_used, _⟩, St₂_decl⟩ := pre2
        mspec (Std.Do.Triple.and _
          (SMT.addToContext_forIn_spec (vs.zip τs))
          (SMT.addToContext_forIn_decls (vs.zip τs) (decl := St₂.env.declarations)))
        mrename_i pre3
        mintro ∀St₃
        mpure pre3
        obtain ⟨⟨_, _, St₃_used⟩, St₃_decl⟩ := pre3
        mspec Std.Do.Spec.get_StateT
        mspec Std.Do.Spec.get_StateT
        mspec Std.Do.Spec.get_StateT
        mspec P_ih (E := E) (used := St₃.env.usedVars) (decl := St₃.env.declarations)
        rename_i out_P
        mrename_i preP
        mintro ∀St₄
        mpure preP
        obtain ⟨P_bv_used, P_used_sub, ΔP, hPdecl, hPok⟩ := preP
        split
        · -- P : .bool
          rename_i heqP
          mspec (Std.Do.Triple.and _
            (SMT.freshVarList_spec τs)
            (SMT.freshVarList_decls τs (decl := St₄.env.declarations)))
          rename_i zs
          mrename_i pre5
          mintro ∀St₅
          mpure pre5
          obtain ⟨⟨_, _, _, _, _, St₅_used, _⟩, St₅_decl⟩ := pre5
          -- Lifts: St₁ ⊆ St₂ ⊆ St₃ ⊆ St₄ ⊆ St₅
          have lift12 : ∀ {w}, w ∈ St₁.env.usedVars → w ∈ St₂.env.usedVars :=
            fun {w} h => by rw [St₂_used]; exact h
          have lift23 : ∀ {w}, w ∈ St₂.env.usedVars → w ∈ St₃.env.usedVars :=
            fun {w} h => by rw [St₃_used]; exact encodeTerm_state.mem_foldl_cons_of_mem _ _ h
          have lift45 : ∀ {w}, w ∈ St₄.env.usedVars → w ∈ St₅.env.usedVars :=
            fun {w} h => by rw [St₅_used]; exact List.mem_append_right _ h
          have lift15 : ∀ {w}, w ∈ St₁.env.usedVars → w ∈ St₅.env.usedVars :=
            fun {w} h => lift45 (P_used_sub (lift23 (lift12 h)))
          have lift35 : ∀ {w}, w ∈ St₃.env.usedVars → w ∈ St₅.env.usedVars :=
            fun {w} h => lift45 (P_used_sub h)
          have liftZs : ∀ {w}, w ∈ zs → w ∈ St₅.env.usedVars :=
            fun {w} h => by rw [St₅_used]; exact List.mem_append_left _ (List.mem_reverse.mpr h)
          -- Lift D_enc bv into St₅
          have hbvD5 : ∀ v ∈ SMT.bv D_enc, v ∈ St₅.env.usedVars := fun v hv =>
            lift15 (D_bv_used v hv)
          have hbvX5 : ∀ v ∈ SMT.bv ((zs.map SMT.Term.var).toPairl), v ∈ St₅.env.usedVars :=
            fun v hv => by
              rw [bv_toPairl_nil (fun t ht => by
                rw [List.mem_map] at ht; obtain ⟨z, _, rfl⟩ := ht; simp [SMT.bv])] at hv
              exact absurd hv List.not_mem_nil
          mspec (Std.Do.Triple.and _
            (castMembership_bv ((zs.map SMT.Term.var).toPairl) D_enc τs.toProdl (.fun τ .bool)
              hbvX5 hbvD5)
            (castMembership_decls_bv ((zs.map SMT.Term.var).toPairl) D_enc τs.toProdl (.fun τ .bool)
              (decl := St₅.env.declarations) hbvX5 hbvD5))
          rename_i out_cm
          mrename_i precm
          mintro ∀St₆
          mpure precm
          obtain ⟨⟨zmem_bv, zmem_used_sub⟩, Δcm, hcmdecl, hcmok, _⟩ := precm
          split
          · rename_i heqcm
            mspec Std.Do.Spec.get_StateT
            simp only [modify]
            mspec Std.Do.Spec.modifyGet_StateT
            mspec (Std.Do.Triple.and _
              (SMT.eraseFromContext_forIn_spec zs)
              (SMT.eraseFromContext_forIn_decls zs))
            mrename_i pre8
            mintro ∀St₈
            mpure pre8
            obtain ⟨⟨_, _, St₈_used⟩, St₈_decl⟩ := pre8
            mspec Std.Do.Spec.pure
            mpure_intro
            -- new_decls = St₆.decl.drop St₃.decl.length = ΔP ++ Δcm
            have hSt6_decl : St₆.env.declarations = St₃.env.declarations ++ (ΔP ++ Δcm) := by
              rw [hcmdecl, St₅_decl, hPdecl, List.append_assoc]
            have hnew : List.drop St₃.env.declarations.length St₆.env.declarations = ΔP ++ Δcm := by
              rw [hSt6_decl, List.drop_left]
            -- St₈.used = St₆.used  (revert + erase keep usedVars)
            have hSt8_used : St₈.env.usedVars = St₆.env.usedVars := St₈_used
            -- St₈.decl = St₃.decl  (revert; erase keeps decl)
            have hSt8_decl : St₈.env.declarations = St₃.env.declarations := St₈_decl
            -- St₃.decl = St₀.decl ++ ΔD
            have hSt3_decl : St₃.env.declarations = St₀.env.declarations ++ ΔD := by
              rw [St₃_decl, St₂_decl, hDdecl]
            -- DeltaBvOk (ΔP ++ Δcm) St₆.used
            have hPokc : DeltaBvOk ΔP St₆.env.usedVars :=
              hPok.mono (fun w hw => zmem_used_sub (lift45 hw))
            have hND_ok : DeltaBvOk (ΔP ++ Δcm) St₆.env.usedVars :=
              DeltaBvOk.append hPokc hcmok
            refine ⟨?bvgoal, ?usedgoal, ΔD, ?declgoal, ?deltagoal⟩
            case usedgoal =>
              rw [hSt8_used]
              exact fun v hv => zmem_used_sub (lift15 (D_used_sub hv))
            case declgoal =>
              rw [hSt8_decl, hSt3_decl]
            case deltagoal =>
              rw [hSt8_used]
              exact hDok.mono (fun w hw => zmem_used_sub (lift15 hw))
            case bvgoal =>
              rw [hSt8_used, hnew]
              intro v hv
              -- bv (.forall zs τs scoped_body) = zs ++ bv scoped_body
              rw [SMT.bv, List.mem_append] at hv
              rcases hv with hvzs | hv
              · -- v ∈ zs
                exact zmem_used_sub (liftZs hvzs)
              · -- v ∈ bv scoped_body  (scoped_body = foldr forall ex_binders inner)
                rw [bv_foldr_forall, List.mem_append] at hv
                rcases hv with hvex | hv
                · -- v ∈ ex_binders.map .1 = declVars (ΔP ++ Δcm)
                  rw [List.mem_map] at hvex
                  obtain ⟨⟨v', τ'⟩, hmem, rfl⟩ := hvex
                  rw [List.mem_filterMap] at hmem
                  obtain ⟨i, hi_mem, hi_eq⟩ := hmem
                  cases i with
                  | declare_const w ξ =>
                    simp only [Option.some.injEq, Prod.mk.injEq] at hi_eq
                    obtain ⟨rfl, _⟩ := hi_eq
                    exact hND_ok.1 w (by rw [declVars, List.mem_filterMap]; exact ⟨_, hi_mem, rfl⟩)
                  | _ => exact absurd hi_eq (by simp)
                · -- v ∈ bv inner  (inner = foldr imp spec_bodies (z_mem_D' ⇒ˢ P'_subst))
                  rw [bv_foldr_imp, List.mem_append] at hv
                  rcases hv with hvspec | hvbase
                  · -- v ∈ spec_bodies.flatMap bv
                    rw [List.mem_flatMap] at hvspec
                    obtain ⟨b, hb_mem, hvb⟩ := hvspec
                    -- b ∈ (specBodies (ΔP++Δcm)).map (substList vs (zs.map var))
                    rw [List.mem_map] at hb_mem
                    obtain ⟨b0, hb0_mem, rfl⟩ := hb_mem
                    rw [SMT_bv_substList_eq_of_var_terms] at hvb
                    -- hb0_mem : b0 ∈ filterMap define_fun_body, defeq specBodies (ΔP ++ Δcm)
                    have hb0_spec : b0 ∈ specBodies (ΔP ++ Δcm) := hb0_mem
                    exact hND_ok.2 b0 hb0_spec v hvb
                  · -- v ∈ bv (z_mem_D' ⇒ˢ substList vs (zs.map var) P')
                    rw [SMT.bv, List.mem_append] at hvbase
                    rcases hvbase with hvzmem | hvP
                    · -- v ∈ bv z_mem_D'
                      exact zmem_bv v hvzmem
                    · -- v ∈ bv (substList vs (zs.map var) P')
                      rw [SMT_bv_substList_eq_of_var_terms] at hvP
                      exact zmem_used_sub (lift45 (P_bv_used v hvP))
          · first
            | exact wp_bind_throw _ _ _ _
            | (mvcgen)
        · first
          | exact wp_bind_throw _ _ _ _
          | (mvcgen)
      · first
        | exact wp_bind_throw _ _ _ _
        | (mvcgen)
    · -- function-arm: τD = .fun α (.option β)
      rename_i α β heqD
      split
      · -- τs.length = vs.length  (unless-true branch)
        rename_i harity
        set τs := (α.pair β).fromProdl (vs.length - 1) with τs_def
        mspec Std.Do.Spec.pure
        mspec (Std.Do.Triple.and _
          (SMT.addToContext_forIn_spec (vs.zip τs))
          (SMT.addToContext_forIn_decls (vs.zip τs) (decl := St₁.env.declarations)))
        mrename_i pre2
        mintro ∀St₂
        mpure pre2
        obtain ⟨⟨_, _, St₂_used⟩, St₂_decl⟩ := pre2
        mspec (Std.Do.Triple.and _
          (SMT.freshVarList_spec τs)
          (SMT.freshVarList_decls τs (decl := St₂.env.declarations)))
        rename_i xs
        mrename_i pre3
        mintro ∀St₃
        mpure pre3
        obtain ⟨⟨_, _, _, _, _, St₃_used, _⟩, St₃_decl⟩ := pre3
        mspec Std.Do.Spec.get_StateT
        mspec Std.Do.Spec.get_StateT
        mspec Std.Do.Spec.get_StateT
        mspec P_ih (E := E) (used := St₃.env.usedVars) (decl := St₃.env.declarations)
        rename_i out_P
        mrename_i preP
        mintro ∀St₄
        mpure preP
        obtain ⟨P_bv_used, P_used_sub, ΔP, hPdecl, hPok⟩ := preP
        split
        · -- P : .bool
          rename_i heqP
          -- Lifts St₁ ⊆ St₂ ⊆ St₃ ⊆ St₄
          have lift12 : ∀ {w}, w ∈ St₁.env.usedVars → w ∈ St₂.env.usedVars :=
            fun {w} h => by rw [St₂_used]; exact encodeTerm_state.mem_foldl_cons_of_mem _ _ h
          have lift23 : ∀ {w}, w ∈ St₂.env.usedVars → w ∈ St₃.env.usedVars :=
            fun {w} h => by rw [St₃_used]; exact List.mem_append_right _ h
          have lift34 : ∀ {w}, w ∈ St₃.env.usedVars → w ∈ St₄.env.usedVars := fun {w} h => P_used_sub h
          have lift14 : ∀ {w}, w ∈ St₁.env.usedVars → w ∈ St₄.env.usedVars :=
            fun {w} h => lift34 (lift23 (lift12 h))
          have liftXs : ∀ {w}, w ∈ xs → w ∈ St₄.env.usedVars :=
            fun {w} h => lift34 (by rw [St₃_used]; exact List.mem_append_left _ (List.mem_reverse.mpr h))
          have hbvD4 : ∀ v ∈ SMT.bv D_enc, v ∈ St₄.env.usedVars := fun v hv =>
            lift14 (D_bv_used v hv)
          have hbvX4 : ∀ v ∈ SMT.bv ((xs.map SMT.Term.var).toPairl), v ∈ St₄.env.usedVars :=
            fun v hv => by
              rw [bv_toPairl_nil (fun t ht => by
                rw [List.mem_map] at ht; obtain ⟨z, _, rfl⟩ := ht; simp [SMT.bv])] at hv
              exact absurd hv List.not_mem_nil
          mspec (Std.Do.Triple.and _
            (castMembership_bv ((xs.map SMT.Term.var).toPairl) D_enc τs.toProdl (α.fun β.option)
              hbvX4 hbvD4)
            (castMembership_decls_bv ((xs.map SMT.Term.var).toPairl) D_enc τs.toProdl (α.fun β.option)
              (decl := St₄.env.declarations) hbvX4 hbvD4))
          rename_i out_cm
          mrename_i precm
          mintro ∀St₅
          mpure precm
          obtain ⟨⟨zmem_bv, zmem_used_sub⟩, Δcm, hcmdecl, hcmok, _⟩ := precm
          mspec Std.Do.Spec.get_StateT
          simp only [modify]
          mspec Std.Do.Spec.modifyGet_StateT
          mspec (Std.Do.Triple.and _
            (SMT.eraseFromContext_forIn_spec xs)
            (SMT.eraseFromContext_forIn_decls xs))
          mrename_i pre6
          mintro ∀St₆
          mpure pre6
          obtain ⟨⟨_, _, St₆_used⟩, St₆_decl⟩ := pre6
          mspec Std.Do.Spec.pure
          mpure_intro
          -- new_decls = St₅.decl.drop St₃.decl.length = ΔP ++ Δcm
          have hSt5_decl : St₅.env.declarations = St₃.env.declarations ++ (ΔP ++ Δcm) := by
            rw [hcmdecl, hPdecl, List.append_assoc]
          have hnew : List.drop St₃.env.declarations.length St₅.env.declarations = ΔP ++ Δcm := by
            rw [hSt5_decl, List.drop_left]
          have hSt6_used : St₆.env.usedVars = St₅.env.usedVars := St₆_used
          have hSt6_decl : St₆.env.declarations = St₃.env.declarations := St₆_decl
          have hSt3_decl : St₃.env.declarations = St₀.env.declarations ++ ΔD := by
            rw [St₃_decl, St₂_decl, hDdecl]
          have lift45 : ∀ {w}, w ∈ St₄.env.usedVars → w ∈ St₅.env.usedVars := fun {w} h => zmem_used_sub h
          have hPokc : DeltaBvOk ΔP St₅.env.usedVars :=
            hPok.mono (fun w hw => lift45 hw)
          have hND_ok : DeltaBvOk (ΔP ++ Δcm) St₅.env.usedVars :=
            DeltaBvOk.append hPokc hcmok
          refine ⟨?bvgoal, ?usedgoal, ΔD, ?declgoal, ?deltagoal⟩
          case usedgoal =>
            rw [hSt6_used]
            exact fun v hv => lift45 (lift14 (D_used_sub hv))
          case declgoal =>
            rw [hSt6_decl, hSt3_decl]
          case deltagoal =>
            rw [hSt6_used]
            exact hDok.mono (fun w hw => lift45 (lift14 hw))
          case bvgoal =>
            rw [hSt6_used, hnew]
            intro v hv
            rw [SMT.bv, List.mem_append] at hv
            rcases hv with hvxs | hv
            · exact lift45 (liftXs hvxs)
            · rw [bv_foldr_forall, List.mem_append] at hv
              rcases hv with hvex | hv
              · rw [List.mem_map] at hvex
                obtain ⟨⟨v', τ'⟩, hmem, rfl⟩ := hvex
                rw [List.mem_filterMap] at hmem
                obtain ⟨i, hi_mem, hi_eq⟩ := hmem
                cases i with
                | declare_const w ξ =>
                  simp only [Option.some.injEq, Prod.mk.injEq] at hi_eq
                  obtain ⟨rfl, _⟩ := hi_eq
                  exact hND_ok.1 w (by rw [declVars, List.mem_filterMap]; exact ⟨_, hi_mem, rfl⟩)
                | _ => exact absurd hi_eq (by simp)
              · rw [bv_foldr_imp, List.mem_append] at hv
                rcases hv with hvspec | hvbase
                · rw [List.mem_flatMap] at hvspec
                  obtain ⟨b, hb_mem, hvb⟩ := hvspec
                  rw [List.mem_map] at hb_mem
                  obtain ⟨b0, hb0_mem, rfl⟩ := hb_mem
                  rw [SMT_bv_substList_eq_of_var_terms] at hvb
                  have hb0_spec : b0 ∈ specBodies (ΔP ++ Δcm) := hb0_mem
                  exact hND_ok.2 b0 hb0_spec v hvb
                · rw [SMT.bv, List.mem_append] at hvbase
                  rcases hvbase with hvzmem | hvP
                  · exact zmem_bv v hvzmem
                  · rw [SMT_bv_substList_eq_of_var_terms] at hvP
                    exact lift45 (P_bv_used v hvP)
        · first
          | exact wp_bind_throw _ _ _ _
          | (mvcgen)
      · first
        | exact wp_bind_throw _ _ _ _
        | (mvcgen)
    · first
      | exact wp_bind_throw _ _ _ _
      | (mvcgen)

/-! ## Freshness companions: bound variables avoid the *input* `usedVars`

The `_bv` lemmas above prove every bound variable of the encoded term lives in the
*final* `usedVars`. The `_notMem` companions below prove the dual: every bound
variable is *fresh* w.r.t. the *input* `usedVars` (`∉ used`). Both facts come from
the same `freshVar_spec` (`v ∉ used` at creation time) and `usedVars` monotonicity;
the companions additionally carry `used ⊆ E'.usedVars` so the inductions compose
(a subterm's bound var `∉ usedVars-before-subcall ⊇ used` ⟹ `∉ used`). -/

/-- Dual of `DeltaBvOk`: every name a declarations-delta `Dl` declares and every
bound variable of a `define_fun` spec body it adds avoids `avoid`. This is the
freshness counterpart needed by the binder (`all`/`collect`) `_notMem` cases. -/
def DeltaBvNotMem (Dl : SMT.Chunk) (avoid : List SMT.𝒱) : Prop :=
  (∀ v ∈ declVars Dl, v ∉ avoid) ∧ (∀ b ∈ specBodies Dl, ∀ v ∈ SMT.bv b, v ∉ avoid)

theorem DeltaBvNotMem.mono {Dl : SMT.Chunk} {a a' : List SMT.𝒱} (h : DeltaBvNotMem Dl a)
    (hsub : a' ⊆ a) : DeltaBvNotMem Dl a' :=
  ⟨fun v hv hmem => h.1 v hv (hsub hmem), fun b hb v hv hmem => h.2 b hb v hv (hsub hmem)⟩

theorem DeltaBvNotMem.append {Δ₁ Δ₂ : SMT.Chunk} {a : List SMT.𝒱}
    (h₁ : DeltaBvNotMem Δ₁ a) (h₂ : DeltaBvNotMem Δ₂ a) : DeltaBvNotMem (Δ₁ ++ Δ₂) a := by
  refine ⟨fun v hv => ?_, fun b hb v hv => ?_⟩
  · rw [declVars_append, List.mem_append] at hv
    exact hv.elim (h₁.1 v) (h₂.1 v)
  · rw [specBodies_append, List.mem_append] at hb
    exact hb.elim (fun hb => h₁.2 b hb v hv) (fun hb => h₂.2 b hb v hv)

@[simp] theorem DeltaBvNotMem_nil {a : List SMT.𝒱} : DeltaBvNotMem [] a := by
  simp [DeltaBvNotMem]

theorem DeltaBvNotMem.declare_const {v : SMT.𝒱} {τ : SMTType} {a : List SMT.𝒱} (hv : v ∉ a) :
    DeltaBvNotMem [.declare_const v τ] a := by
  refine ⟨fun w hw => ?_, fun b hb => ?_⟩
  · simp only [declVars_declare_const, List.mem_singleton] at hw; exact hw ▸ hv
  · simp only [specBodies_declare_const, List.not_mem_nil] at hb

theorem DeltaBvNotMem.define_fun_spec {nm : String} {b : SMT.Term} {a : List SMT.𝒱}
    (hb : ∀ v ∈ SMT.bv b, v ∉ a) : DeltaBvNotMem [.define_fun nm .unit .bool b] a := by
  refine ⟨fun w hw => ?_, fun b' hb' w hw => ?_⟩
  · simp only [declVars, SMT.Instr.define_fun, List.filterMap_cons, List.filterMap_nil] at hw
    exact absurd hw List.not_mem_nil
  · rw [show ([SMT.Instr.define_fun nm .unit .bool b]) = [] ++ [SMT.Instr.define_fun nm .unit .bool b]
      from rfl, specBodies_append] at hb'
    simp only [specBodies_nil, List.nil_append, mem_specBodies_define_fun] at hb'
    obtain ⟨nm', hmem⟩ := hb'
    rw [List.mem_singleton] at hmem
    cases hmem
    exact hb w hw

/-- Freshness form of `DeltaBvOk.helperSpecChunk`. -/
theorem DeltaBvNotMem.helperSpecChunk {v : SMT.𝒱} {τ : SMTType} {b : SMT.Term}
    {a : List SMT.𝒱} (hv : v ∉ a) (hb : ∀ w ∈ SMT.bv b, w ∉ a) :
    DeltaBvNotMem (_root_.helperSpecChunk v τ b) a := by
  simpa [_root_.helperSpecChunk] using
    DeltaBvNotMem.append (DeltaBvNotMem.declare_const (τ := τ) hv)
      (DeltaBvNotMem.define_fun_spec (nm := s!"{v}_spec") hb)

/-- Freshness companion of `defaultSpecM_bv`: every bound variable of the produced
default term avoids the *input* `usedVars`. -/
theorem defaultSpecM_bv_notMem (τ : SMTType) :
    ∀ {avoid used : List SMT.𝒱} {n : ℕ} {name : String} {t : SMT.Term},
    avoid ⊆ used → (∀ v ∈ SMT.bv t, v ∉ avoid) →
    ⦃ fun (⟨E, _Λ'⟩ : EncoderState) ↦ ⌜E.freshvarsc = n ∧ E.usedVars = used⌝ ⦄
    defaultSpecM name τ t
    ⦃ ⇓? (d : SMT.Term) (⟨E', _Γ'⟩ : EncoderState) =>
        ⌜(∀ v ∈ SMT.bv d, v ∉ avoid) ∧ used ⊆ E'.usedVars⌝ ⦄ := by
  induction τ with
  | int | bool =>
    intro avoid used n name t havsub hbvt
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl⟩ := pre
    unfold defaultSpecM
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨?_, fun v hv => hv⟩
    intro v hv
    simp only [SMT.bv, List.append_nil] at hv
    exact hbvt v hv
  | unit =>
    intro avoid used n name t havsub hbvt
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl⟩ := pre
    unfold defaultSpecM
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨?_, fun v hv => hv⟩
    intro v hv
    simp only [SMT.bv, List.not_mem_nil] at hv
  | option σ _ih =>
    intro avoid used n name t havsub hbvt
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl⟩ := pre
    unfold defaultSpecM
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨?_, fun v hv => hv⟩
    intro v hv
    simp only [noneCast, SMT.bv, List.append_nil] at hv
    exact hbvt v hv
  | pair σ ρ σ_ih ρ_ih =>
    intro avoid used n name t havsub hbvt
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl⟩ := pre
    unfold defaultSpecM
    have hbvt_fst : ∀ v ∈ SMT.bv (Term.fst t), v ∉ avoid :=
      fun v hv => hbvt v (by rwa [SMT.bv] at hv)
    mspec (σ_ih havsub hbvt_fst)
    mrename_i preF
    mintro ∀St₂
    mpure preF
    obtain ⟨hfst_bv, hfst_used_sub⟩ := preF
    have hbvt_snd : ∀ v ∈ SMT.bv (Term.snd t), v ∉ avoid :=
      fun v hv => hbvt v (by rwa [SMT.bv] at hv)
    mspec (ρ_ih (havsub.trans hfst_used_sub) hbvt_snd)
    mrename_i preS
    mintro ∀St₃
    mpure preS
    obtain ⟨hsnd_bv, hsnd_used_sub⟩ := preS
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨?_, fun v hv => hsnd_used_sub (hfst_used_sub hv)⟩
    intro v hv
    simp only [SMT.bv, List.mem_append] at hv
    rcases hv with hv | hv
    · exact hfst_bv v hv
    · exact hsnd_bv v hv
  | «fun» α β _α_ih β_ih =>
    intro avoid used n name t havsub hbvt
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl⟩ := pre
    unfold defaultSpecM
    mspec SMT.freshVar_spec
    case post.success x =>
      mrename_i prex
      mintro ∀St₂
      mpure prex
      obtain ⟨_, x_fresh, _, St₂_used_eq, x_notMem⟩ := prex
      have x_notMem_avoid : x ∉ avoid := fun h => x_notMem (havsub h)
      have hbvt_app : ∀ v ∈ SMT.bv (Term.app t (Term.var x)), v ∉ avoid := fun v hv => by
        simp only [SMT.bv, List.append_nil] at hv
        exact hbvt v hv
      have havsub₂ : avoid ⊆ St₂.env.usedVars := fun w h => by
        rw [St₂_used_eq]; exact List.mem_cons_of_mem _ (havsub h)
      mspec (β_ih havsub₂ hbvt_app)
      mrename_i prebody
      mintro ∀St₃
      mpure prebody
      obtain ⟨hbody_bv, hbody_used_sub⟩ := prebody
      mspec SMT.eraseFromContext_spec
      mrename_i preE
      mintro ∀StE
      mpure preE
      obtain ⟨_, _, StE_used_eq⟩ := preE
      mspec Std.Do.Spec.pure
      mpure_intro
      have lift : ∀ {w}, w ∈ St.env.usedVars → w ∈ St₂.env.usedVars := fun {w} h => by
        rw [St₂_used_eq]; exact List.mem_cons_of_mem _ h
      refine ⟨?_, fun v hv => by rw [StE_used_eq]; exact hbody_used_sub (lift hv)⟩
      intro v hv
      simp only [SMT.bv, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | hv
      · exact x_notMem_avoid
      · exact hbody_bv v hv

set_option maxHeartbeats 4000000 in
/-- Freshness companion of `loosenAux_prf_bv_pair`: the fresh head variable `x!`
and every bound variable of the produced spec avoid `avoid` (a subset of the
running `usedVars`). -/
theorem loosenAux_prf_bv_notMem_pair {α β α' β' : SMTType} (pα : α ~> α') (pβ : β ~> β')
    (pα_ih : ∀ {avoid used : List SMT.𝒱} {n : ℕ} {name : String} {x : SMT.Term},
      avoid ⊆ used → (∀ v ∈ SMT.bv x, v ∉ avoid) →
      ⦃ fun (⟨E, _Λ'⟩ : EncoderState) ↦ ⌜E.freshvarsc = n ∧ E.usedVars = used⌝ ⦄
      loosenAux_prf name pα x
      ⦃ ⇓? (⟨x!, spec⟩ : 𝒱 × SMT.Term) (⟨E', _Γ'⟩ : EncoderState) =>
          ⌜x! ∉ avoid ∧ (∀ v ∈ SMT.bv spec, v ∉ avoid) ∧ used ⊆ E'.usedVars⌝ ⦄)
    (pβ_ih : ∀ {avoid used : List SMT.𝒱} {n : ℕ} {name : String} {x : SMT.Term},
      avoid ⊆ used → (∀ v ∈ SMT.bv x, v ∉ avoid) →
      ⦃ fun (⟨E, _Λ'⟩ : EncoderState) ↦ ⌜E.freshvarsc = n ∧ E.usedVars = used⌝ ⦄
      loosenAux_prf name pβ x
      ⦃ ⇓? (⟨x!, spec⟩ : 𝒱 × SMT.Term) (⟨E', _Γ'⟩ : EncoderState) =>
          ⌜x! ∉ avoid ∧ (∀ v ∈ SMT.bv spec, v ∉ avoid) ∧ used ⊆ E'.usedVars⌝ ⦄)
    {avoid used : List SMT.𝒱} {n : ℕ} {name : String} {x : SMT.Term}
    (havsub : avoid ⊆ used) (hbvx : ∀ v ∈ SMT.bv x, v ∉ avoid) :
    ⦃ fun (⟨E, _Λ'⟩ : EncoderState) ↦ ⌜E.freshvarsc = n ∧ E.usedVars = used⌝ ⦄
    loosenAux_prf name (castPath.pair pα pβ) x
    ⦃ ⇓? (⟨x!, spec⟩ : 𝒱 × SMT.Term) (⟨E', _Γ'⟩ : EncoderState) =>
        ⌜x! ∉ avoid ∧ (∀ v ∈ SMT.bv spec, v ∉ avoid) ∧ used ⊆ E'.usedVars⌝ ⦄ := by
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl⟩ := pre
  unfold loosenAux_prf
  mspec SMT.freshVar_spec
  mrename_i prex
  mintro ∀St₂
  mpure prex
  obtain ⟨_, x!_fresh, _, St₂_used_eq, x!_notMem⟩ := prex
  have x!_notMem_avoid : _ ∉ avoid := fun h => x!_notMem (havsub h)
  have havsub₂ : avoid ⊆ St₂.env.usedVars := fun w h => by
    rw [St₂_used_eq]; exact List.mem_cons_of_mem _ (havsub h)
  have hbvfst : ∀ v ∈ SMT.bv (Term.fst x), v ∉ avoid :=
    fun v hv => hbvx v (by rwa [SMT.bv] at hv)
  mspec (pα_ih havsub₂ hbvfst)
  mrename_i preF
  mintro ∀St₃
  mpure preF
  obtain ⟨fst!_notMem, fst!_bv, fst!_used_sub⟩ := preF
  have hbvsnd : ∀ v ∈ SMT.bv (Term.snd x), v ∉ avoid :=
    fun v hv => hbvx v (by rwa [SMT.bv] at hv)
  mspec (pβ_ih (havsub₂.trans fst!_used_sub) hbvsnd)
  mrename_i preS
  mintro ∀St₄
  mpure preS
  obtain ⟨snd!_notMem, snd!_bv, snd!_used_sub⟩ := preS
  mspec SMT.eraseFromContext_spec
  mrename_i preE
  mintro ∀StE
  mpure preE
  obtain ⟨_, _, StE_used_eq⟩ := preE
  mspec SMT.eraseFromContext_spec
  mrename_i preE2
  mintro ∀StE2
  mpure preE2
  obtain ⟨_, _, StE2_used_eq⟩ := preE2
  mspec Std.Do.Spec.pure
  mpure_intro
  rw [StE2_used_eq, StE_used_eq]
  refine ⟨x!_notMem_avoid, ?_, ?_⟩
  · intro v hv
    simp only [SMT.bv, List.append_nil, List.nil_append, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hv
    rcases hv with (rfl | rfl) | hvf | hvs
    · exact fst!_notMem
    · exact snd!_notMem
    · exact fst!_bv v hvf
    · exact snd!_bv v hvs
  · exact fun v hv => snd!_used_sub (fst!_used_sub
      (by rw [St₂_used_eq]; exact List.mem_cons_of_mem _ hv))

set_option maxHeartbeats 4000000 in
/-- Freshness companion of `loosenAux_prf_bv`: the fresh head variable `x!` and
every bound variable of the produced spec avoid `avoid` (a subset of the running
`usedVars`). All binders are freshly created (`∉ usedVars ⊇ avoid`) or come from
recursion. -/
theorem loosenAux_prf_bv_notMem {α β : SMTType} (c : α ~> β) :
    ∀ {avoid used : List SMT.𝒱} {n : ℕ} {name : String} {x : SMT.Term},
    avoid ⊆ used → (∀ v ∈ SMT.bv x, v ∉ avoid) →
    ⦃ fun (⟨E, _Λ'⟩ : EncoderState) ↦ ⌜E.freshvarsc = n ∧ E.usedVars = used⌝ ⦄
    loosenAux_prf name c x
    ⦃ ⇓? (⟨x!, spec⟩ : 𝒱 × SMT.Term) (⟨E', _Γ'⟩ : EncoderState) =>
        ⌜x! ∉ avoid ∧ (∀ v ∈ SMT.bv spec, v ∉ avoid) ∧ used ⊆ E'.usedVars⌝ ⦄ := by
  induction c with
  | @refl α hα =>
    intro avoid used n name x havsub hbvx
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl⟩ := pre
    unfold loosenAux_prf
    mspec SMT.freshVar_spec
    mrename_i prex
    mintro ∀St₂
    mpure prex
    obtain ⟨_, x!_fresh, _, St₂_used_eq, x!_notMem⟩ := prex
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨fun h => x!_notMem (havsub h), ?_, ?_⟩
    · intro v hv
      simp only [SMT.bv, List.nil_append] at hv
      exact hbvx v hv
    · rw [St₂_used_eq]; intro v hv; exact List.mem_cons_of_mem _ hv
  | @chpred α α' p ih =>
    intro avoid used n name x havsub hbvx
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl⟩ := pre
    unfold loosenAux_prf
    mspec SMT.freshVar_spec
    mrename_i prex
    mintro ∀St₂
    mpure prex
    obtain ⟨_, x!_fresh, _, St₂_used_eq, x!_notMem⟩ := prex
    mspec SMT.freshVar_spec
    mrename_i prez
    mintro ∀St₃
    mpure prez
    obtain ⟨_, z_fresh, _, St₃_used_eq, z_notMem⟩ := prez
    have havsub₂ : avoid ⊆ St₂.env.usedVars := fun w h => by
      rw [St₂_used_eq]; exact List.mem_cons_of_mem _ (havsub h)
    have havsub₃ : avoid ⊆ St₃.env.usedVars := fun w h => by
      rw [St₃_used_eq]; exact List.mem_cons_of_mem _ (havsub₂ h)
    mspec (ih havsub₃ (by intro v hv; simp only [SMT.bv, List.not_mem_nil] at hv))
    mrename_i prez!
    mintro ∀St₄
    mpure prez!
    obtain ⟨z!_notMem, z!_bv, z!_used_sub⟩ := prez!
    mspec SMT.eraseFromContext_spec
    mrename_i preE
    mintro ∀StE
    mpure preE
    obtain ⟨_, _, StE_used_eq⟩ := preE
    mspec SMT.eraseFromContext_spec
    mrename_i preE2
    mintro ∀StE2
    mpure preE2
    obtain ⟨_, _, StE2_used_eq⟩ := preE2
    mspec Std.Do.Spec.pure
    mpure_intro
    rw [StE2_used_eq, StE_used_eq]
    refine ⟨fun h => x!_notMem (havsub h), ?_, ?_⟩
    · intro v hv
      simp only [SMT.bv, List.nil_append, List.append_nil, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | hvx | hvspec
      · exact z!_notMem
      · exact fun h => z_notMem (havsub₂ h)
      · exact hbvx v hvx
      · exact z!_bv v hvspec
    · intro v hv
      apply z!_used_sub; rw [St₃_used_eq, St₂_used_eq]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hv)
  | @graph α β α' β' pα pβ pα_ih pβ_ih =>
    intro avoid used n name x havsub hbvx
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl⟩ := pre
    unfold loosenAux_prf
    mspec SMT.freshVar_spec
    mrename_i prex
    mintro ∀St₂
    mpure prex
    obtain ⟨_, x!_fresh, _, St₂_used_eq, x!_notMem⟩ := prex
    mspec SMT.freshVar_spec
    mrename_i prez
    mintro ∀St₃
    mpure prez
    obtain ⟨_, z_fresh, _, St₃_used_eq, z_notMem⟩ := prez
    have havsub₂ : avoid ⊆ St₂.env.usedVars := fun w h => by
      rw [St₂_used_eq]; exact List.mem_cons_of_mem _ (havsub h)
    have havsub₃ : avoid ⊆ St₃.env.usedVars := fun w h => by
      rw [St₃_used_eq]; exact List.mem_cons_of_mem _ (havsub₂ h)
    mspec (loosenAux_prf_bv_notMem_pair pα pβ pα_ih pβ_ih havsub₃
      (by intro v hv; simp only [SMT.bv, List.not_mem_nil] at hv))
    mrename_i prez!
    mintro ∀St₄
    mpure prez!
    obtain ⟨z!_notMem, z!_bv, z!_used_sub⟩ := prez!
    mspec SMT.eraseFromContext_spec
    mrename_i preE
    mintro ∀StE
    mpure preE
    obtain ⟨_, _, StE_used_eq⟩ := preE
    mspec SMT.eraseFromContext_spec
    mrename_i preE2
    mintro ∀StE2
    mpure preE2
    obtain ⟨_, _, StE2_used_eq⟩ := preE2
    mspec Std.Do.Spec.pure
    mpure_intro
    rw [StE2_used_eq, StE_used_eq]
    refine ⟨fun h => x!_notMem (havsub h), ?_, ?_⟩
    · intro v hv
      simp only [SMT.bv, List.nil_append, List.append_nil, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | hvx | hvspec
      · exact z!_notMem
      · exact fun h => z_notMem (havsub₂ h)
      · exact hbvx v hvx
      · exact z!_bv v hvspec
    · intro v hv
      apply z!_used_sub; rw [St₃_used_eq, St₂_used_eq]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hv)
  | @pair α β α' β' pα pβ pα_ih pβ_ih =>
    intro avoid used n name x havsub hbvx
    exact loosenAux_prf_bv_notMem_pair pα pβ pα_ih pβ_ih havsub hbvx
  | @opt α α' p ih =>
    intro avoid used n name x havsub hbvx
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl⟩ := pre
    unfold loosenAux_prf
    mspec SMT.freshVar_spec
    mrename_i prex
    mintro ∀St₂
    mpure prex
    obtain ⟨_, x!_fresh, _, St₂_used_eq, x!_notMem⟩ := prex
    have havsub₂ : avoid ⊆ St₂.env.usedVars := fun w h => by
      rw [St₂_used_eq]; exact List.mem_cons_of_mem _ (havsub h)
    split
    · rename_i x!
      mspec Std.Do.Spec.pure
      mpure_intro
      refine ⟨fun h => x!_notMem (havsub h), ?_, ?_⟩
      · intro v hv
        simp only [noneCast, SMT.bv, List.append_nil, List.not_mem_nil] at hv
      · rw [St₂_used_eq]; intro v hv; exact List.mem_cons_of_mem _ hv
    · rename_i x! x₀
      mspec (ih havsub₂
        (by intro v hv; exact hbvx v (by rw [SMT.bv]; exact hv)))
      mrename_i prew
      mintro ∀St₃
      mpure prew
      obtain ⟨w!_notMem, w!_bv, w!_used_sub⟩ := prew
      mspec SMT.eraseFromContext_spec
      mrename_i preE
      mintro ∀StE
      mpure preE
      obtain ⟨_, _, StE_used_eq⟩ := preE
      mspec Std.Do.Spec.pure
      mpure_intro
      rw [StE_used_eq]
      refine ⟨fun h => x!_notMem (havsub h), ?_, ?_⟩
      · intro v hv
        simp only [SMT.bv, List.nil_append, List.append_nil, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false] at hv
        rcases hv with rfl | hvspec
        · exact w!_notMem
        · exact w!_bv v hvspec
      · intro v hv; apply w!_used_sub; rw [St₂_used_eq]; exact List.mem_cons_of_mem _ hv
    · rename_i x! x_ne_none x_ne_some
      mspec (ih havsub₂
        (by intro v hv; rw [SMT.bv] at hv; exact hbvx v hv))
      mrename_i prew
      mintro ∀St₃
      mpure prew
      obtain ⟨w!_notMem, w!_bv, w!_used_sub⟩ := prew
      mspec SMT.eraseFromContext_spec
      mrename_i preE
      mintro ∀StE
      mpure preE
      obtain ⟨_, _, StE_used_eq⟩ := preE
      mspec Std.Do.Spec.pure
      mpure_intro
      rw [StE_used_eq]
      refine ⟨fun h => x!_notMem (havsub h), ?_, ?_⟩
      · intro v hv
        simp only [noneCast, SMT.bv, List.nil_append, List.append_nil, List.mem_append,
          List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with hvx | rfl | hvspec
        · exact hbvx v hvx
        · exact w!_notMem
        · exact w!_bv v hvspec
      · intro v hv; apply w!_used_sub; rw [St₂_used_eq]; exact List.mem_cons_of_mem _ hv
  | @«fun» α β α' β' hβ pα pβ pα_ih pβ_ih =>
    intro avoid used n name x havsub hbvx
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl⟩ := pre
    unfold loosenAux_prf
    mspec SMT.freshVar_spec
    mrename_i prex
    mintro ∀St₂
    mpure prex
    obtain ⟨_, x!_fresh, _, St₂_used_eq, x!_notMem⟩ := prex
    mspec SMT.freshVar_spec
    mrename_i prea
    mintro ∀St₃
    mpure prea
    obtain ⟨_, a_fresh, _, St₃_used_eq, a_notMem⟩ := prea
    have havsub₂ : avoid ⊆ St₂.env.usedVars := fun w h => by
      rw [St₂_used_eq]; exact List.mem_cons_of_mem _ (havsub h)
    have havsub₃ : avoid ⊆ St₃.env.usedVars := fun w h => by
      rw [St₃_used_eq]; exact List.mem_cons_of_mem _ (havsub₂ h)
    mspec (pα_ih havsub₃
      (by intro v hv; simp only [SMT.bv, List.not_mem_nil] at hv))
    mrename_i prea!
    mintro ∀St₄
    mpure prea!
    obtain ⟨a!_notMem, a!_bv, a!_used_sub⟩ := prea!
    mspec SMT.freshVar_spec
    mrename_i preb
    mintro ∀St₅
    mpure preb
    obtain ⟨_, b_fresh, _, St₅_used_eq, b_notMem⟩ := preb
    have havsub₄ : avoid ⊆ St₄.env.usedVars := havsub₃.trans a!_used_sub
    have havsub₅ : avoid ⊆ St₅.env.usedVars := fun w h => by
      rw [St₅_used_eq]; exact List.mem_cons_of_mem _ (havsub₄ h)
    mspec (pβ_ih havsub₅
      (by intro v hv; simp only [SMT.bv, List.not_mem_nil] at hv))
    mrename_i preb!
    mintro ∀St₆
    mpure preb!
    obtain ⟨b!_notMem, b!_bv, b!_used_sub⟩ := preb!
    have havsub₆ : avoid ⊆ St₆.env.usedVars := havsub₅.trans b!_used_sub
    mspec (defaultSpecM_bv_notMem β' havsub₆
      (by intro v hv; simp only [SMT.bv, List.append_nil, List.not_mem_nil] at hv))
    mrename_i pred
    mintro ∀St₇
    mpure pred
    obtain ⟨hd_bv, hd_used_sub⟩ := pred
    mspec SMT.eraseFromContext_spec
    mrename_i preE
    mintro ∀StE
    mpure preE
    obtain ⟨_, _, StE_used_eq⟩ := preE
    mspec SMT.eraseFromContext_spec
    mrename_i preE2
    mintro ∀StE2
    mpure preE2
    obtain ⟨_, _, StE2_used_eq⟩ := preE2
    mspec SMT.eraseFromContext_spec
    mrename_i preE3
    mintro ∀StE3
    mpure preE3
    obtain ⟨_, _, StE3_used_eq⟩ := preE3
    mspec SMT.eraseFromContext_spec
    mrename_i preE4
    mintro ∀StE4
    mpure preE4
    obtain ⟨_, _, StE4_used_eq⟩ := preE4
    mspec Std.Do.Spec.pure
    mpure_intro
    rw [StE4_used_eq, StE3_used_eq, StE2_used_eq, StE_used_eq]
    have lift4 : ∀ {v}, v ∈ St₄.env.usedVars → v ∈ St₇.env.usedVars := fun {v} h =>
      hd_used_sub (b!_used_sub (by rw [St₅_used_eq]; exact List.mem_cons_of_mem _ h))
    have lift2 : ∀ {v}, v ∈ St₂.env.usedVars → v ∈ St₇.env.usedVars := fun {v} h =>
      lift4 (a!_used_sub (by rw [St₃_used_eq]; exact List.mem_cons_of_mem _ h))
    refine ⟨fun h => x!_notMem (havsub h), ?_,
      fun v hv => lift2 (by rw [St₂_used_eq]; exact List.mem_cons_of_mem _ hv)⟩
    intro v hv
    simp only [SMT.bv, List.append_nil, List.nil_append, List.mem_append, List.mem_cons,
      List.not_mem_nil, false_or, or_false] at hv
    rcases hv with rfl | ((rfl | ha!spec) | (rfl | ((rfl | rfl) | (hx | (ha!spec2 | hb!spec))))) | hhd
    · exact a!_notMem
    · exact fun h => a_notMem (havsub₂ h)
    · exact a!_bv v ha!spec
    · exact b!_notMem
    · exact fun h => a_notMem (havsub₂ h)
    · exact fun h => b_notMem (havsub₄ h)
    · exact hbvx v hx
    · exact a!_bv v ha!spec2
    · exact b!_bv v hb!spec
    · exact hd_bv v hhd

/-- Freshness companion of `castApp_bv`: the output term embeds only `.var`-headed
helpers and the inputs `f`/`x` (loosen specs go to `addSpec`, not the term), so every
bound variable of the result avoids `avoid`. -/
theorem castApp_bv_notMem (f x : SMT.Term) (sf sx : SMTType) {avoid used : List SMT.𝒱} {n : ℕ}
    (havsub : avoid ⊆ used)
    (hbvf : ∀ v ∈ SMT.bv f, v ∉ avoid) (hbvx : ∀ v ∈ SMT.bv x, v ∉ avoid) :
    ⦃ fun (⟨E, _Λ'⟩ : EncoderState) ↦ ⌜E.freshvarsc = n ∧ E.usedVars = used⌝ ⦄
    castApp (f, sf) (x, sx)
    ⦃ ⇓? (⟨t', _σ⟩ : SMT.Term × SMTType) (⟨E', _Γ'⟩ : EncoderState) =>
        ⌜(∀ v ∈ SMT.bv t', v ∉ avoid) ∧ used ⊆ E'.usedVars⌝ ⦄ := by
  unfold castApp
  mvcgen
  case vc3.h_2.isTrue =>
    rename_i hxeq hfeq _ St hpre
    obtain ⟨rfl, rfl⟩ := hpre
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hxeq
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hfeq
    mspec (loosenAux_prf_bv_notMem _ havsub hbvf)
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨L_notMem, L_bv, L_used_sub⟩ := pre
    unfold SMT.declareConstWithSpec
    mspec Std.Do.Spec.bind
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, _, hd_used, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨_, _, _, hs_used, _⟩ := pres
    mspec Std.Do.Spec.pure
    mpure_intro
    rw [hs_used, hd_used]
    refine ⟨?_, L_used_sub⟩
    intro v hv
    simp only [SMT.bv, List.nil_append, List.append_nil, List.mem_append,
      List.not_mem_nil, false_or, or_false] at hv
    exact hbvx v hv
  case vc4.h_2.isFalse.isTrue =>
    rename_i hxeq hfeq _ _ St hpre
    obtain ⟨rfl, rfl⟩ := hpre
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hxeq
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hfeq
    mspec (loosenAux_prf_bv_notMem _ havsub hbvx)
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨L_notMem, L_bv, L_used_sub⟩ := pre
    unfold SMT.declareConstWithSpec
    mspec Std.Do.Spec.bind
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, _, hd_used, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨_, _, _, hs_used, _⟩ := pres
    mspec Std.Do.Spec.pure
    mpure_intro
    rw [hs_used, hd_used]
    refine ⟨?_, L_used_sub⟩
    intro v hv
    simp only [SMT.bv, List.nil_append, List.append_nil, List.mem_append,
      List.not_mem_nil, false_or, or_false] at hv
    exact hbvf v hv
  case vc5.h_3.isTrue =>
    rename_i hxeq hfeq _ St hpre
    obtain ⟨rfl, rfl⟩ := hpre
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hxeq
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hfeq
    mspec (loosenAux_prf_bv_notMem _ havsub hbvf)
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨L_notMem, L_bv, L_used_sub⟩ := pre
    unfold SMT.declareConstWithSpec
    mspec Std.Do.Spec.bind
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, _, hd_used, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨_, _, _, hs_used, _⟩ := pres
    mspec Std.Do.Spec.pure
    mpure_intro
    rw [hs_used, hd_used]
    refine ⟨?_, L_used_sub⟩
    intro v hv
    simp only [SMT.bv, List.nil_append, List.append_nil, List.mem_append,
      List.not_mem_nil, false_or, or_false] at hv
    exact hbvx v hv
  case vc6.h_3.isFalse.isTrue =>
    rename_i hxeq hfeq _ _ St hpre
    obtain ⟨rfl, rfl⟩ := hpre
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hxeq
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hfeq
    mspec (loosenAux_prf_bv_notMem _ havsub hbvx)
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨L_notMem, L_bv, L_used_sub⟩ := pre
    unfold SMT.declareConstWithSpec
    mspec Std.Do.Spec.bind
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, _, hd_used, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨_, _, _, hs_used, _⟩ := pres
    mspec Std.Do.Spec.pure
    mpure_intro
    rw [hs_used, hd_used]
    refine ⟨?_, L_used_sub⟩
    intro v hv
    simp only [SMT.bv, List.nil_append, List.append_nil, List.mem_append,
      List.not_mem_nil, false_or, or_false] at hv
    exact hbvf v hv
  case vc1.h_1.isTrue =>
    rename_i hxeq hfeq _ St hpre
    obtain ⟨rfl, rfl⟩ := hpre
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hxeq
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hfeq
    mspec (loosenAux_prf_bv_notMem _ havsub hbvf)
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨L_notMem, L_bv, L_used_sub⟩ := pre
    unfold SMT.declareConstWithSpec
    mspec Std.Do.Spec.bind
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, _, hd_used, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨_, _, _, hs_used, _⟩ := pres
    mspec SMT.freshVar_spec
    mrename_i pre2
    mintro ∀St₂
    mpure pre2
    obtain ⟨_, _, _, St₂_used_eq, _⟩ := pre2
    mspec SMT.declareConst_spec
    mrename_i pred2
    mintro ∀St₂d
    mpure pred2
    obtain ⟨_, _, _, hd2_used, _⟩ := pred2
    mspec SMT.freshVar_spec
    mrename_i pre3
    mintro ∀St₃
    mpure pre3
    obtain ⟨_, _, _, St₃_used_eq, _⟩ := pre3
    mspec SMT.freshVar_spec
    mrename_i pre4
    mintro ∀St₄
    mpure pre4
    obtain ⟨_, _, _, St₄_used_eq, _⟩ := pre4
    mspec SMT.eraseFromContext_spec (Γ := St₄.types)
    mrename_i pre5
    mintro ∀St5
    mpure pre5
    obtain ⟨_, _, St5_used_eq⟩ := pre5
    mspec SMT.eraseFromContext_spec (Γ := St5.types)
    mrename_i pre6
    mintro ∀St6
    mpure pre6
    obtain ⟨_, _, St6_used_eq⟩ := pre6
    mspec SMT.addSpec_spec
    mrename_i pres2
    mintro ∀St6s
    mpure pres2
    obtain ⟨_, _, _, hs2_used, _⟩ := pres2
    mspec Std.Do.Spec.pure
    mpure_intro
    have lift : ∀ {w}, w ∈ St₁.env.usedVars → w ∈ St6s.env.usedVars := fun {w} h => by
      rw [hs2_used, St6_used_eq, St5_used_eq, St₄_used_eq, St₃_used_eq, hd2_used,
        St₂_used_eq, hs_used, hd_used]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
    refine ⟨?_, fun w hw => lift (L_used_sub hw)⟩
    intro v hv
    simp only [SMT.bv, List.nil_append, List.append_nil, List.mem_append,
      List.not_mem_nil, false_or, or_false] at hv
    exact hbvx v hv
  case vc2.h_1.isFalse.isTrue =>
    rename_i hxeq hfeq _ _ St hpre
    obtain ⟨rfl, rfl⟩ := hpre
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hxeq
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hfeq
    mspec (loosenAux_prf_bv_notMem _ havsub hbvx)
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨L_notMem, L_bv, L_used_sub⟩ := pre
    unfold SMT.declareConstWithSpec
    mspec Std.Do.Spec.bind
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, _, hd_used, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨_, _, _, hs_used, _⟩ := pres
    mspec SMT.freshVar_spec
    mrename_i pre2
    mintro ∀St₂
    mpure pre2
    obtain ⟨_, _, _, St₂_used_eq, _⟩ := pre2
    mspec SMT.declareConst_spec
    mrename_i pred2
    mintro ∀St₂d
    mpure pred2
    obtain ⟨_, _, _, hd2_used, _⟩ := pred2
    mspec SMT.freshVar_spec
    mrename_i pre3
    mintro ∀St₃
    mpure pre3
    obtain ⟨_, _, _, St₃_used_eq, _⟩ := pre3
    mspec SMT.freshVar_spec
    mrename_i pre4
    mintro ∀St₄
    mpure pre4
    obtain ⟨_, _, _, St₄_used_eq, _⟩ := pre4
    mspec SMT.eraseFromContext_spec (Γ := St₄.types)
    mrename_i pre5
    mintro ∀St5
    mpure pre5
    obtain ⟨_, _, St5_used_eq⟩ := pre5
    mspec SMT.eraseFromContext_spec (Γ := St5.types)
    mrename_i pre6
    mintro ∀St6
    mpure pre6
    obtain ⟨_, _, St6_used_eq⟩ := pre6
    mspec SMT.addSpec_spec
    mrename_i pres2
    mintro ∀St6s
    mpure pres2
    obtain ⟨_, _, _, hs2_used, _⟩ := pres2
    mspec Std.Do.Spec.pure
    mpure_intro
    have lift : ∀ {w}, w ∈ St₁.env.usedVars → w ∈ St6s.env.usedVars := fun {w} h => by
      rw [hs2_used, St6_used_eq, St5_used_eq, St₄_used_eq, St₃_used_eq, hd2_used,
        St₂_used_eq, hs_used, hd_used]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
    refine ⟨?_, fun w hw => lift (L_used_sub hw)⟩
    intro v hv
    simp only [SMT.bv, List.nil_append, List.append_nil, List.mem_append,
      List.not_mem_nil, false_or, or_false] at hv

set_option maxHeartbeats 4000000 in
/-- Freshness companion of `castMembership_bv`: every bound variable of the result
(loosen spec embedded via `∧ˢ`, plus inputs) avoids `avoid`. -/
theorem castMembership_bv_notMem (x S : SMT.Term) (sx sS : SMTType)
    {avoid used : List SMT.𝒱} {n : ℕ} (havsub : avoid ⊆ used)
    (hbvx : ∀ v ∈ SMT.bv x, v ∉ avoid) (hbvS : ∀ v ∈ SMT.bv S, v ∉ avoid) :
    ⦃ fun (⟨E, _Λ'⟩ : EncoderState) ↦ ⌜E.freshvarsc = n ∧ E.usedVars = used⌝ ⦄
    castMembership (x, sx) (S, sS)
    ⦃ ⇓? (⟨t', _σ⟩ : SMT.Term × SMTType) (⟨E', _Γ'⟩ : EncoderState) =>
        ⌜(∀ v ∈ SMT.bv t', v ∉ avoid) ∧ used ⊆ E'.usedVars⌝ ⦄ := by
  unfold castMembership
  mvcgen
  case vc1.h_1.isTrue =>
    rename_i α' hσS hσx St hpre
    obtain ⟨rfl, rfl⟩ := hpre
    refine ⟨?_, fun v hv => hv⟩
    intro v hv
    simp only [SMT.bv, List.append_nil, List.mem_append] at hv
    rcases hv with hvS | hvx
    · exact hbvS v hvS
    · exact hbvx v hvx
  case vc2.h_1.isFalse.isTrue =>
    rename_i α' hσS hσx_ne hσx_le St hpre
    obtain ⟨rfl, rfl⟩ := hpre
    mspec (loosenAux_prf_bv_notMem _ havsub hbvx)
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨L_notMem, L_bv, L_used_sub⟩ := pre
    mspec SMT.declareConst_addSpec_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, _, hd_used, _⟩ := pred
    mspec Std.Do.Spec.pure
    mpure_intro
    rw [hd_used]
    refine ⟨?_, L_used_sub⟩
    intro v hv
    simp only [SMT.bv, List.nil_append, List.append_nil, List.mem_append,
      List.not_mem_nil, false_or, or_false] at hv
    rcases hv with hspec | hvS
    · exact L_bv v hspec
    · exact hbvS v hvS
  case vc3.h_1.isFalse.isFalse.isTrue =>
    rename_i α' hσS hσx_ne hσx_nle hα'_le St hpre
    obtain ⟨rfl, rfl⟩ := hpre
    mspec (loosenAux_prf_bv_notMem _ havsub hbvS)
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨L_notMem, L_bv, L_used_sub⟩ := pre
    mspec SMT.declareConst_addSpec_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, _, hd_used, _⟩ := pred
    mspec Std.Do.Spec.pure
    mpure_intro
    rw [hd_used]
    refine ⟨?_, L_used_sub⟩
    intro v hv
    simp only [SMT.bv, List.nil_append, List.append_nil, List.mem_append,
      List.not_mem_nil, false_or, or_false, or_self] at hv
    rcases hv with hspec | hvx
    · exact L_bv v hspec
    · exact hbvx v hvx
  case vc4.h_2.h_1.isTrue.isTrue =>
    rename_i α' β' hσS α β hσx hα_le hβ_le St hpre
    obtain ⟨rfl, rfl⟩ := hpre
    mspec (loosenAux_prf_bv_notMem _ havsub hbvx)
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨L_notMem, L_bv, L_used_sub⟩ := pre
    mspec SMT.declareConst_addSpec_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, _, hd_used, _⟩ := pred
    mspec Std.Do.Spec.pure
    mpure_intro
    rw [hd_used]
    refine ⟨?_, L_used_sub⟩
    intro v hv
    simp only [SMT.bv, List.nil_append, List.append_nil, List.mem_append,
      List.not_mem_nil, false_or, or_false] at hv
    rcases hv with hspec | hvS
    · exact L_bv v hspec
    · exact hbvS v hvS
  case vc5.h_2.h_1.isTrue.isFalse.isTrue =>
    rename_i α' β' hσS α β hσx hα_le hβ_nle hβ'_le St hpre
    obtain ⟨rfl, rfl⟩ := hpre
    mspec (loosenAux_prf_bv_notMem _ havsub (by intro v hv; exact hbvx v (by rwa [SMT.bv] at hv)))
    mrename_i preX
    mintro ∀St₁
    mpure preX
    obtain ⟨x!_notMem, x!_bv, x!_used_sub⟩ := preX
    mspec SMT.declareConst_addSpec_spec
    mrename_i predX
    mintro ∀St₁d
    mpure predX
    obtain ⟨_, _, _, hdX_used, _⟩ := predX
    have havsub₁d : avoid ⊆ St₁d.env.usedVars := fun w h => by
      rw [hdX_used]; exact x!_used_sub (havsub h)
    mspec (loosenAux_prf_bv_notMem _ havsub₁d (by intro v hv; exact hbvS v hv))
    mrename_i preS
    mintro ∀St₂
    mpure preS
    obtain ⟨S!_notMem, S!_bv, S!_used_sub⟩ := preS
    mspec SMT.declareConst_addSpec_spec
    mrename_i predS
    mintro ∀St₂d
    mpure predS
    obtain ⟨_, _, _, hdS_used, _⟩ := predS
    mspec Std.Do.Spec.pure
    mpure_intro
    rw [hdS_used]
    have lift1 : ∀ {w}, w ∈ St₁.env.usedVars → w ∈ St₂.env.usedVars :=
      fun {w} h => S!_used_sub (by rw [hdX_used]; exact h)
    refine ⟨?_, fun v hv => lift1 (x!_used_sub hv)⟩
    intro v hv
    simp only [SMT.bv, List.nil_append, List.append_nil, List.mem_append,
      List.not_mem_nil, false_or, or_false] at hv
    rcases hv with (hspecX | hspecS) | hvx
    · exact x!_bv v hspecX
    · exact S!_bv v hspecS
    · exact hbvx v hvx
  case vc6.h_2.h_1.isFalse.isTrue.isTrue =>
    rename_i α' β' hσS α β hσx hα_nle hα'_le hβ_le St hpre
    obtain ⟨rfl, rfl⟩ := hpre
    mspec (loosenAux_prf_bv_notMem _ havsub (by intro v hv; exact hbvx v (by rwa [SMT.bv] at hv)))
    mrename_i preY
    mintro ∀St₁
    mpure preY
    obtain ⟨y!_notMem, y!_bv, y!_used_sub⟩ := preY
    mspec SMT.declareConst_addSpec_spec
    mrename_i predY
    mintro ∀St₁d
    mpure predY
    obtain ⟨_, _, _, hdY_used, _⟩ := predY
    have havsub₁d : avoid ⊆ St₁d.env.usedVars := fun w h => by
      rw [hdY_used]; exact y!_used_sub (havsub h)
    mspec (loosenAux_prf_bv_notMem _ havsub₁d (by intro v hv; exact hbvS v hv))
    mrename_i preS
    mintro ∀St₂
    mpure preS
    obtain ⟨S!_notMem, S!_bv, S!_used_sub⟩ := preS
    mspec SMT.declareConst_addSpec_spec
    mrename_i predS
    mintro ∀St₂d
    mpure predS
    obtain ⟨_, _, _, hdS_used, _⟩ := predS
    mspec Std.Do.Spec.pure
    mpure_intro
    rw [hdS_used]
    have lift1 : ∀ {w}, w ∈ St₁.env.usedVars → w ∈ St₂.env.usedVars :=
      fun {w} h => S!_used_sub (by rw [hdY_used]; exact h)
    refine ⟨?_, fun v hv => lift1 (y!_used_sub hv)⟩
    intro v hv
    simp only [SMT.bv, List.nil_append, List.append_nil, List.mem_append,
      List.not_mem_nil, false_or, or_false] at hv
    rcases hv with (hspecY | hspecS) | hvx
    · exact y!_bv v hspecY
    · exact S!_bv v hspecS
    · exact hbvx v hvx
  case vc7.h_2.h_1.isFalse.isTrue.isFalse.isTrue =>
    rename_i α' β' hσS α β hσx hα_nle hα'_le hβ_nle hβ'_le St hpre
    obtain ⟨rfl, rfl⟩ := hpre
    mspec (loosenAux_prf_bv_notMem _ havsub hbvS)
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨L_notMem, L_bv, L_used_sub⟩ := pre
    mspec SMT.declareConst_addSpec_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, _, hd_used, _⟩ := pred
    mspec Std.Do.Spec.pure
    mpure_intro
    rw [hd_used]
    refine ⟨?_, L_used_sub⟩
    intro v hv
    simp only [SMT.bv, List.nil_append, List.append_nil, List.mem_append,
      List.not_mem_nil, false_or, or_false, or_self] at hv
    rcases hv with hspec | hvx
    · exact L_bv v hspec
    · exact hbvx v hvx

set_option maxHeartbeats 4000000 in
/-- Freshness companion of `castUnionAux_bv`: result is `λ x. S!(x) ∨ T(x)`; its
bound variables (fresh binder plus `bv T`) avoid `avoid`. -/
theorem castUnionAux_bv_notMem {α β : SMTType} (c : α ~> β) (S T : SMT.Term)
    {avoid used : List SMT.𝒱} {n : ℕ} (havsub : avoid ⊆ used)
    (hbvS : ∀ v ∈ SMT.bv S, v ∉ avoid) (hbvT : ∀ v ∈ SMT.bv T, v ∉ avoid) :
    ⦃ fun (⟨E, _Λ'⟩ : EncoderState) ↦ ⌜E.freshvarsc = n ∧ E.usedVars = used⌝ ⦄
    castUnionAux S T c
    ⦃ ⇓? (⟨t', _σ⟩ : SMT.Term × SMTType) (⟨E', _Γ'⟩ : EncoderState) =>
        ⌜(∀ v ∈ SMT.bv t', v ∉ avoid) ∧ used ⊆ E'.usedVars⌝ ⦄ := by
  cases c with
  | @graph α β α' β' c_α c_β =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl⟩ := pre
    unfold castUnionAux castUnion.graph
    mspec (loosenAux_prf_bv_notMem _ havsub hbvS)
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨S!_notMem, S!_bv, S!_used_sub⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, _, hd_used, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨_, _, _, hs_used, _⟩ := pres
    mspec SMT.freshVar_spec
    case post.success x =>
      mrename_i pre2
      mintro ∀St₂
      mpure pre2
      obtain ⟨_, _, _, St₂_used_eq, x_notMem⟩ := pre2
      have havsub₁s : avoid ⊆ St₁s.env.usedVars := fun w h => by
        rw [hs_used, hd_used]; exact S!_used_sub (havsub h)
      mspec SMT.eraseFromContext_spec (v := x)
        (Γ := St₂.types) (n := St₂.env.freshvarsc)
        (used := St₂.env.usedVars)
      mrename_i pre3
      mintro ∀St₃
      mpure pre3
      obtain ⟨_, _, St₃_used_eq⟩ := pre3
      mspec Std.Do.Spec.pure
      mpure_intro
      refine ⟨?_, ?_⟩
      · intro v hv
        simp only [SMT.bv, List.nil_append, List.append_nil, List.mem_append, List.mem_cons,
          List.not_mem_nil, false_or, or_false] at hv
        rcases hv with rfl | hvT
        · exact fun h => x_notMem (havsub₁s h)
        · exact hbvT v hvT
      · intro v hv
        rw [St₃_used_eq, St₂_used_eq, hs_used, hd_used]
        exact List.mem_cons_of_mem _ (S!_used_sub hv)
  | @«fun» α β α' β' hβ c_α c_β =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl⟩ := pre
    unfold castUnionAux castUnion.fun
    mspec (loosenAux_prf_bv_notMem _ havsub hbvS)
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨S!_notMem, S!_bv, S!_used_sub⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, _, hd_used, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨_, _, _, hs_used, _⟩ := pres
    have havsub₁s : avoid ⊆ St₁s.env.usedVars := fun w h => by
      rw [hs_used, hd_used]; exact S!_used_sub (havsub h)
    split
    · mspec SMT.freshVar_spec
      mrename_i pre2
      mintro ∀St₂
      mpure pre2
      obtain ⟨_, _, _, St₂_used_eq, x_notMem⟩ := pre2
      mspec Std.Do.Spec.pure
      mpure_intro
      refine ⟨?_, ?_⟩
      · intro v hv
        simp only [SMT.bv, List.nil_append, List.append_nil, List.mem_append, List.mem_cons,
          List.not_mem_nil, false_or, or_false, or_self] at hv
        rcases hv with rfl | hvT
        · exact fun h => x_notMem (havsub₁s h)
        · exact hbvT v hvT
      · intro v hv
        rw [St₂_used_eq, hs_used, hd_used]
        exact List.mem_cons_of_mem _ (S!_used_sub hv)
    · mvcgen
  | @chpred α α' c_α =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl⟩ := pre
    unfold castUnionAux castUnion.chpred
    mspec (loosenAux_prf_bv_notMem _ havsub hbvS)
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨S!_notMem, S!_bv, S!_used_sub⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, _, hd_used, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨_, _, _, hs_used, _⟩ := pres
    have havsub₁s : avoid ⊆ St₁s.env.usedVars := fun w h => by
      rw [hs_used, hd_used]; exact S!_used_sub (havsub h)
    mspec SMT.freshVar_spec
    mrename_i pre2
    mintro ∀St₂
    mpure pre2
    obtain ⟨_, _, _, St₂_used_eq, x_notMem⟩ := pre2
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨?_, ?_⟩
    · intro v hv
      simp only [SMT.bv, List.nil_append, List.append_nil, List.mem_append, List.mem_cons,
        List.not_mem_nil, false_or, or_false] at hv
      rcases hv with rfl | hvT
      · exact fun h => x_notMem (havsub₁s h)
      · exact hbvT v hvT
    · intro v hv
      rw [St₂_used_eq, hs_used, hd_used]
      exact List.mem_cons_of_mem _ (S!_used_sub hv)
  | @opt α α' c_α =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl⟩ := pre
    unfold castUnionAux castUnion.opt
    mvcgen
  | @pair α β α' β' c_α c_β =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl⟩ := pre
    unfold castUnionAux castUnion.pair
    mvcgen
  | @refl α hα =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl⟩ := pre
    unfold castUnionAux castUnion.refl
    mvcgen

set_option maxHeartbeats 4000000 in
/-- Freshness companion of `castUnion_bv`: every bound variable of the result avoids
`avoid`. -/
theorem castUnion_bv_notMem (S T : SMT.Term) (sS sT : SMTType)
    {avoid used : List SMT.𝒱} {n : ℕ} (havsub : avoid ⊆ used)
    (hbvS : ∀ v ∈ SMT.bv S, v ∉ avoid) (hbvT : ∀ v ∈ SMT.bv T, v ∉ avoid) :
    ⦃ fun (⟨E, _Λ'⟩ : EncoderState) ↦ ⌜E.freshvarsc = n ∧ E.usedVars = used⌝ ⦄
    castUnion (S, sS) (T, sT)
    ⦃ ⇓? (⟨t', _σ⟩ : SMT.Term × SMTType) (⟨E', _Γ'⟩ : EncoderState) =>
        ⌜(∀ v ∈ SMT.bv t', v ∉ avoid) ∧ used ⊆ E'.usedVars⌝ ⦄ := by
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl⟩ := pre
  unfold castUnion
  split
  split
  rename_i heqA _ _ _ heqB
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heqA
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heqB
  split_ifs with heq hsub1 hsub2
  · subst heq
    split
    · mspec SMT.freshVar_spec
      mrename_i pre2
      mintro ∀St₂
      mpure pre2
      obtain ⟨_, _, _, St₂_used_eq, x_notMem⟩ := pre2
      mspec SMT.eraseFromContext_spec
      mrename_i preE
      mintro ∀StE
      mpure preE
      obtain ⟨_, _, StE_used_eq⟩ := preE
      mspec Std.Do.Spec.pure
      mpure_intro
      rw [StE_used_eq]
      refine ⟨?_, fun v hv => by rw [St₂_used_eq]; exact List.mem_cons_of_mem _ hv⟩
      intro v hv
      simp only [SMT.bv, List.append_nil, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hv
      rcases hv with rfl | hvS | hvT
      · exact fun h => x_notMem (havsub h)
      · exact hbvS v hvS
      · exact hbvT v hvT
    all_goals mvcgen
  · mspec (castUnionAux_bv_notMem _ S T havsub hbvS hbvT)
  · mspec (castUnionAux_bv_notMem _ T S havsub hbvT hbvS)
  · mvcgen

set_option maxHeartbeats 4000000 in
/-- Freshness companion of `castInter_bv`: every bound variable of the result avoids
`avoid` (the staged `castInterAux` dispatch builds `λ x. S!(x) ∧ T(x)`). -/
theorem castInter_bv_notMem (S T : SMT.Term) (sS sT : SMTType)
    {avoid used : List SMT.𝒱} {n : ℕ} (havsub : avoid ⊆ used)
    (hbvS : ∀ v ∈ SMT.bv S, v ∉ avoid) (hbvT : ∀ v ∈ SMT.bv T, v ∉ avoid) :
    ⦃ fun (⟨E, _Λ'⟩ : EncoderState) ↦ ⌜E.freshvarsc = n ∧ E.usedVars = used⌝ ⦄
    castInter (S, sS) (T, sT)
    ⦃ ⇓? (⟨t', _σ⟩ : SMT.Term × SMTType) (⟨E', _Γ'⟩ : EncoderState) =>
        ⌜(∀ v ∈ SMT.bv t', v ∉ avoid) ∧ used ⊆ E'.usedVars⌝ ⦄ := by
  have IAux : ∀ {α β : SMTType} (c : α ~> β) (S' T' : SMT.Term),
      (∀ v ∈ SMT.bv S', v ∉ avoid) → (∀ v ∈ SMT.bv T', v ∉ avoid) →
      ⦃ fun (⟨E, _Λ'⟩ : EncoderState) ↦ ⌜E.freshvarsc = n ∧ E.usedVars = used⌝ ⦄
      castInterAux S' T' c
      ⦃ ⇓? (⟨t', _σ⟩ : SMT.Term × SMTType) (⟨E', _Γ'⟩ : EncoderState) =>
          ⌜(∀ v ∈ SMT.bv t', v ∉ avoid) ∧ used ⊆ E'.usedVars⌝ ⦄ := by
    intro α β c S' T' hbvS' hbvT'
    cases c with
    | @graph α β α' β' c_α c_β =>
      mintro pre ∀St
      mpure pre
      obtain ⟨rfl, rfl⟩ := pre
      unfold castInterAux
      mspec (loosenAux_prf_bv_notMem _ havsub hbvS')
      mrename_i pre
      mintro ∀St₁
      mpure pre
      obtain ⟨S!_notMem, S!_bv, S!_used_sub⟩ := pre
      mspec SMT.declareConst_spec
      mrename_i pred
      mintro ∀St₁d
      mpure pred
      obtain ⟨_, _, _, hd_used, _⟩ := pred
      mspec SMT.addSpec_spec
      mrename_i pres
      mintro ∀St₁s
      mpure pres
      obtain ⟨_, _, _, hs_used, _⟩ := pres
      have havsub₁s : avoid ⊆ St₁s.env.usedVars := fun w h => by
        rw [hs_used, hd_used]; exact S!_used_sub (havsub h)
      mspec SMT.freshVar_spec
      case post.success x =>
        mrename_i pre2
        mintro ∀St₂
        mpure pre2
        obtain ⟨_, _, _, St₂_used_eq, x_notMem⟩ := pre2
        mspec SMT.eraseFromContext_spec (v := x)
          (Γ := St₂.types) (n := St₂.env.freshvarsc)
          (used := St₂.env.usedVars)
        mrename_i pre3
        mintro ∀St₃
        mpure pre3
        obtain ⟨_, _, St₃_used_eq⟩ := pre3
        mspec Std.Do.Spec.pure
        mpure_intro
        refine ⟨?_, ?_⟩
        · intro v hv
          simp only [SMT.bv, List.nil_append, List.append_nil, List.mem_append, List.mem_cons,
            List.not_mem_nil, false_or, or_false] at hv
          rcases hv with rfl | hvT
          · exact fun h => x_notMem (havsub₁s h)
          · exact hbvT' v hvT
        · intro v hv
          rw [St₃_used_eq, St₂_used_eq, hs_used, hd_used]
          exact List.mem_cons_of_mem _ (S!_used_sub hv)
    | @«fun» α β α' β' hβ c_α c_β =>
      mintro pre ∀St
      mpure pre
      obtain ⟨rfl, rfl⟩ := pre
      unfold castInterAux
      mspec (loosenAux_prf_bv_notMem _ havsub hbvS')
      mrename_i pre
      mintro ∀St₁
      mpure pre
      obtain ⟨S!_notMem, S!_bv, S!_used_sub⟩ := pre
      mspec SMT.declareConst_spec
      mrename_i pred
      mintro ∀St₁d
      mpure pred
      obtain ⟨_, _, _, hd_used, _⟩ := pred
      mspec SMT.addSpec_spec
      mrename_i pres
      mintro ∀St₁s
      mpure pres
      obtain ⟨_, _, _, hs_used, _⟩ := pres
      have havsub₁s : avoid ⊆ St₁s.env.usedVars := fun w h => by
        rw [hs_used, hd_used]; exact S!_used_sub (havsub h)
      split
      · mspec SMT.freshVar_spec
        mrename_i pre2
        mintro ∀St₂
        mpure pre2
        obtain ⟨_, _, _, St₂_used_eq, x_notMem⟩ := pre2
        mspec Std.Do.Spec.pure
        mpure_intro
        refine ⟨?_, ?_⟩
        · intro v hv
          simp only [SMT.bv, List.nil_append, List.append_nil, List.mem_append, List.mem_cons,
            List.not_mem_nil, false_or, or_false, or_self] at hv
          rcases hv with rfl | hvT
          · exact fun h => x_notMem (havsub₁s h)
          · exact hbvT' v hvT
        · intro v hv
          rw [St₂_used_eq, hs_used, hd_used]
          exact List.mem_cons_of_mem _ (S!_used_sub hv)
      · mvcgen
    | @chpred α α' c_α =>
      mintro pre ∀St
      mpure pre
      obtain ⟨rfl, rfl⟩ := pre
      unfold castInterAux
      mspec (loosenAux_prf_bv_notMem _ havsub hbvS')
      mrename_i pre
      mintro ∀St₁
      mpure pre
      obtain ⟨S!_notMem, S!_bv, S!_used_sub⟩ := pre
      mspec SMT.declareConst_spec
      mrename_i pred
      mintro ∀St₁d
      mpure pred
      obtain ⟨_, _, _, hd_used, _⟩ := pred
      mspec SMT.addSpec_spec
      mrename_i pres
      mintro ∀St₁s
      mpure pres
      obtain ⟨_, _, _, hs_used, _⟩ := pres
      have havsub₁s : avoid ⊆ St₁s.env.usedVars := fun w h => by
        rw [hs_used, hd_used]; exact S!_used_sub (havsub h)
      mspec SMT.freshVar_spec
      mrename_i pre2
      mintro ∀St₂
      mpure pre2
      obtain ⟨_, _, _, St₂_used_eq, x_notMem⟩ := pre2
      mspec Std.Do.Spec.pure
      mpure_intro
      refine ⟨?_, ?_⟩
      · intro v hv
        simp only [SMT.bv, List.nil_append, List.append_nil, List.mem_append, List.mem_cons,
          List.not_mem_nil, false_or, or_false] at hv
        rcases hv with rfl | hvT
        · exact fun h => x_notMem (havsub₁s h)
        · exact hbvT' v hvT
      · intro v hv
        rw [St₂_used_eq, hs_used, hd_used]
        exact List.mem_cons_of_mem _ (S!_used_sub hv)
    | @opt α α' c_α =>
      mintro pre ∀St
      mpure pre
      obtain ⟨rfl, rfl⟩ := pre
      unfold castInterAux
      mvcgen
    | @pair α β α' β' c_α c_β =>
      mintro pre ∀St
      mpure pre
      obtain ⟨rfl, rfl⟩ := pre
      unfold castInterAux
      mvcgen
    | @refl α hα =>
      mintro pre ∀St
      mpure pre
      obtain ⟨rfl, rfl⟩ := pre
      unfold castInterAux
      mvcgen
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl⟩ := pre
  unfold castInter
  split
  split
  rename_i heqA _ _ _ heqB
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heqA
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heqB
  split_ifs with heq hsub1 hsub2
  · subst heq
    split
    · mspec SMT.freshVar_spec
      mrename_i pre2
      mintro ∀St₂
      mpure pre2
      obtain ⟨_, _, _, St₂_used_eq, x_notMem⟩ := pre2
      mspec SMT.eraseFromContext_spec
      mrename_i preE
      mintro ∀StE
      mpure preE
      obtain ⟨_, _, StE_used_eq⟩ := preE
      mspec Std.Do.Spec.pure
      mpure_intro
      rw [StE_used_eq]
      refine ⟨?_, fun v hv => by rw [St₂_used_eq]; exact List.mem_cons_of_mem _ hv⟩
      intro v hv
      simp only [SMT.bv, List.append_nil, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hv
      rcases hv with rfl | hvS | hvT
      · exact fun h => x_notMem (havsub h)
      · exact hbvS v hvS
      · exact hbvT v hvT
    all_goals mvcgen
  · mspec (IAux _ S T hbvS hbvT)
  · mspec (IAux _ T S hbvT hbvS)
  · mvcgen

/-- Freshness companion of `castEq_bv`: the output equality's bound variables
(loosened spec plus inputs `A`, `B`) avoid `avoid`. -/
theorem castEq_bv_notMem (A B : SMT.Term) (σA σB : SMTType)
    {avoid used : List SMT.𝒱} {n : ℕ} (havsub : avoid ⊆ used)
    (hbvA : ∀ v ∈ SMT.bv A, v ∉ avoid) (hbvB : ∀ v ∈ SMT.bv B, v ∉ avoid) :
    ⦃ fun (⟨E, _Λ'⟩ : EncoderState) ↦ ⌜E.freshvarsc = n ∧ E.usedVars = used⌝ ⦄
    castEq (A, σA) (B, σB)
    ⦃ ⇓? (⟨t', _σ⟩ : SMT.Term × SMTType) (⟨E', _Γ'⟩ : EncoderState) =>
        ⌜(∀ v ∈ SMT.bv t', v ∉ avoid) ∧ used ⊆ E'.usedVars⌝ ⦄ := by
  unfold castEq
  mvcgen
  · rename_i hpre
    obtain ⟨rfl, rfl⟩ := hpre
    refine ⟨?_, fun v hv => hv⟩
    intro v hv
    simp only [SMT.bv, List.mem_append] at hv
    rcases hv with hv | hv
    · exact hbvA v hv
    · exact hbvB v hv
  · rename_i hpre
    obtain ⟨rfl, rfl⟩ := hpre
    mspec (loosenAux_prf_bv_notMem _ havsub hbvA)
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨A!_notMem, A!_bv, A!_used_sub⟩ := pre
    mspec SMT.declareConst_addSpec_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, _, hd_used, _⟩ := pred
    mspec Std.Do.Spec.pure
    mpure_intro
    rw [hd_used]
    refine ⟨?_, A!_used_sub⟩
    intro v hv
    simp only [SMT.bv, List.nil_append, List.append_nil, List.mem_append,
      List.not_mem_nil, false_or, or_false] at hv
    rcases hv with hvB | hvspec
    · exact hbvB v hvB
    · exact A!_bv v hvspec
  · rename_i hpre
    obtain ⟨rfl, rfl⟩ := hpre
    mspec (loosenAux_prf_bv_notMem _ havsub hbvB)
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨B!_notMem, B!_bv, B!_used_sub⟩ := pre
    mspec SMT.declareConst_addSpec_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, _, hd_used, _⟩ := pred
    mspec Std.Do.Spec.pure
    mpure_intro
    rw [hd_used]
    refine ⟨?_, B!_used_sub⟩
    intro v hv
    simp only [SMT.bv, List.nil_append, List.append_nil, List.mem_append,
      List.not_mem_nil, false_or, or_false] at hv
    rcases hv with hvA | hvspec
    · exact hbvA v hvA
    · exact B!_bv v hvspec

/-- Freshness companion of `loosenAux_prf_bv_declsEq`: bundles `loosenAux_prf_bv_notMem`
with declarations-invariance. The fresh head `p.1` and every bound variable of the
spec `p.2` avoid `avoid`. -/
theorem loosenAux_prf_bv_declsEq_notMem {α β : SMTType} (c : α ~> β)
    {avoid used : List SMT.𝒱} {n : ℕ} {name : String} {x : SMT.Term} {decl : SMT.Chunk}
    (havsub : avoid ⊆ used) (hx : ∀ v ∈ SMT.bv x, v ∉ avoid) :
    ⦃ fun (⟨E, _Λ⟩ : EncoderState) ↦
        ⌜E.freshvarsc = n ∧ E.usedVars = used ∧ E.declarations = decl⌝ ⦄
    loosenAux_prf name c x
    ⦃ ⇓? (p : SMT.𝒱 × SMT.Term) (⟨E', _Γ⟩ : EncoderState) =>
        ⌜p.1 ∉ avoid ∧ (∀ v ∈ SMT.bv p.2, v ∉ avoid) ∧ used ⊆ E'.usedVars
          ∧ E'.declarations = decl⌝ ⦄ := by
  have hand := Std.Do.Triple.and (loosenAux_prf name c x)
    (loosenAux_prf_bv_notMem c (avoid := avoid) (used := used) (n := n) (name := name) (x := x)
      havsub hx)
    (loosenAux_prf_decls c (name := name) (x := x) (decl := decl))
  mintro pre ∀St
  mpure pre
  obtain ⟨hfvc, hused, hdecl⟩ := pre
  mspec hand
  mrename_i hpost
  mintro ∀St'
  mpure hpost
  mpure_intro
  obtain ⟨⟨x!_notMem, spec_bv, used_sub⟩, decl_eq⟩ := hpost
  exact ⟨x!_notMem, spec_bv, used_sub, decl_eq⟩

set_option maxHeartbeats 4000000 in
/-- Dual declarations-delta spec of `castEq`: each constrained helper and every
bound variable of its recorded specification avoid `avoid`. -/
theorem castEq_decls_bv_notMem (A B : SMT.Term) (σA σB : SMTType)
    {avoid used : List SMT.𝒱} {n : ℕ} {decl : SMT.Chunk} (havsub : avoid ⊆ used)
    (hbvA : ∀ v ∈ SMT.bv A, v ∉ avoid) (hbvB : ∀ v ∈ SMT.bv B, v ∉ avoid) :
    ⦃ fun (⟨E, _Λ'⟩ : EncoderState) ↦
        ⌜E.freshvarsc = n ∧ E.usedVars = used ∧ E.declarations = decl⌝ ⦄
    castEq (A, σA) (B, σB)
    ⦃ ⇓? (_ : SMT.Term × SMTType) (⟨E', _Γ'⟩ : EncoderState) =>
        ⌜∃ Dl : SMT.Chunk, E'.declarations = decl ++ Dl ∧ DeltaBvNotMem Dl avoid
          ∧ used ⊆ E'.usedVars⌝ ⦄ := by
  unfold castEq
  mvcgen
  · rename_i hpre
    obtain ⟨rfl, rfl, rfl⟩ := hpre
    exact ⟨[], by simp, DeltaBvNotMem_nil, fun v hv => hv⟩
  · rename_i hpre
    obtain ⟨rfl, rfl, rfl⟩ := hpre
    mspec (loosenAux_prf_bv_declsEq_notMem _ havsub hbvA)
    mrename_i pre
    mintro ∀St₁
    rename_i Aout
    obtain ⟨A!, A!_spec⟩ := Aout
    mpure pre
    obtain ⟨A!_notMem, A!_bv, A!_used_sub, A!_decl⟩ := pre
    mspec SMT.declareConst_addSpec_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, hd_used, _⟩ := pred
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨_root_.helperSpecChunk A! σB A!_spec, ?_,
      DeltaBvNotMem.helperSpecChunk A!_notMem A!_bv, ?_⟩
    · rw [hd_decl, A!_decl]
      simp [_root_.helperSpecChunk, List.concat_eq_append, List.append_assoc]
    · exact fun v hv => by rw [hd_used]; exact A!_used_sub hv
  · rename_i hpre
    obtain ⟨rfl, rfl, rfl⟩ := hpre
    mspec (loosenAux_prf_bv_declsEq_notMem _ havsub hbvB)
    mrename_i pre
    mintro ∀St₁
    rename_i Bout
    obtain ⟨B!, B!_spec⟩ := Bout
    mpure pre
    obtain ⟨B!_notMem, B!_bv, B!_used_sub, B!_decl⟩ := pre
    mspec SMT.declareConst_addSpec_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, hd_used, _⟩ := pred
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨_root_.helperSpecChunk B! σA B!_spec, ?_,
      DeltaBvNotMem.helperSpecChunk B!_notMem B!_bv, ?_⟩
    · rw [hd_decl, B!_decl]
      simp [_root_.helperSpecChunk, List.concat_eq_append, List.append_assoc]
    · exact fun v hv => by rw [hd_used]; exact B!_used_sub hv

set_option maxHeartbeats 4000000 in
/-- Dual declarations-delta spec of `castMembership`: each constrained helper
and every bound variable of its recorded specification avoid `avoid`. -/
theorem castMembership_decls_bv_notMem (x S : SMT.Term) (sx sS : SMTType)
    {avoid used : List SMT.𝒱} {n : ℕ} {decl : SMT.Chunk} (havsub : avoid ⊆ used)
    (hbvx : ∀ v ∈ SMT.bv x, v ∉ avoid) (hbvS : ∀ v ∈ SMT.bv S, v ∉ avoid) :
    ⦃ fun (⟨E, _Λ'⟩ : EncoderState) ↦
        ⌜E.freshvarsc = n ∧ E.usedVars = used ∧ E.declarations = decl⌝ ⦄
    castMembership (x, sx) (S, sS)
    ⦃ ⇓? (_ : SMT.Term × SMTType) (⟨E', _Γ'⟩ : EncoderState) =>
        ⌜∃ Dl : SMT.Chunk, E'.declarations = decl ++ Dl ∧ DeltaBvNotMem Dl avoid
          ∧ used ⊆ E'.usedVars⌝ ⦄ := by
  unfold castMembership
  mvcgen
  case vc1.h_1.isTrue =>
    rename_i α' hσS hσx St hpre
    obtain ⟨rfl, rfl, rfl⟩ := hpre
    exact ⟨[], by simp, DeltaBvNotMem_nil, fun v hv => hv⟩
  case vc2.h_1.isFalse.isTrue =>
    rename_i α' hσS hσx_ne hσx_le St hpre
    obtain ⟨rfl, rfl, rfl⟩ := hpre
    mspec (loosenAux_prf_bv_declsEq_notMem _ havsub hbvx)
    mrename_i pre
    mintro ∀St₁
    rename_i xout
    obtain ⟨x!, x!_spec⟩ := xout
    mpure pre
    obtain ⟨x!_notMem, x!_bv, x!_used_sub, x!_decl⟩ := pre
    mspec SMT.declareConst_addSpec_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, hd_used, _⟩ := pred
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨_root_.helperSpecChunk x! α' x!_spec, ?_,
      DeltaBvNotMem.helperSpecChunk x!_notMem x!_bv,
      fun v hv => by rw [hd_used]; exact x!_used_sub hv⟩
    rw [hd_decl, x!_decl]
    simp [_root_.helperSpecChunk, List.concat_eq_append, List.append_assoc]
  case vc3.h_1.isFalse.isFalse.isTrue =>
    rename_i α' hσS hσx_ne hσx_nle hα'_le St hpre
    obtain ⟨rfl, rfl, rfl⟩ := hpre
    mspec (loosenAux_prf_bv_declsEq_notMem _ havsub hbvS)
    mrename_i pre
    mintro ∀St₁
    rename_i Sout
    obtain ⟨S!, S!_spec⟩ := Sout
    mpure pre
    obtain ⟨S!_notMem, S!_bv, S!_used_sub, S!_decl⟩ := pre
    mspec SMT.declareConst_addSpec_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, hd_used, _⟩ := pred
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨_root_.helperSpecChunk S! (.fun sx .bool) S!_spec, ?_,
      DeltaBvNotMem.helperSpecChunk S!_notMem S!_bv,
      fun v hv => by rw [hd_used]; exact S!_used_sub hv⟩
    rw [hd_decl, S!_decl]
    simp [_root_.helperSpecChunk, List.concat_eq_append, List.append_assoc]
  case vc4.h_2.h_1.isTrue.isTrue =>
    rename_i α' β' hσS α β hσx hα_le hβ_le St hpre
    obtain ⟨rfl, rfl, rfl⟩ := hpre
    mspec (loosenAux_prf_bv_declsEq_notMem _ havsub hbvx)
    mrename_i pre
    mintro ∀St₁
    rename_i xout
    obtain ⟨x!, x!_spec⟩ := xout
    mpure pre
    obtain ⟨x!_notMem, x!_bv, x!_used_sub, x!_decl⟩ := pre
    mspec SMT.declareConst_addSpec_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, hd_used, _⟩ := pred
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨_root_.helperSpecChunk x! (.pair α' β') x!_spec, ?_,
      DeltaBvNotMem.helperSpecChunk x!_notMem x!_bv,
      fun v hv => by rw [hd_used]; exact x!_used_sub hv⟩
    rw [hd_decl, x!_decl]
    simp [_root_.helperSpecChunk, List.concat_eq_append, List.append_assoc]
  case vc5.h_2.h_1.isTrue.isFalse.isTrue =>
    rename_i α' β' hσS α β hσx hα_le hβ_nle hβ'_le St hpre
    obtain ⟨rfl, rfl, rfl⟩ := hpre
    mspec (loosenAux_prf_bv_declsEq_notMem _ havsub (by intro v hv; exact hbvx v (by rwa [SMT.bv] at hv)))
    mrename_i preX
    mintro ∀St₁
    rename_i xout
    obtain ⟨x!, x!_spec⟩ := xout
    mpure preX
    obtain ⟨x!_notMem, x!_bv, x!_used_sub, x!_decl⟩ := preX
    mspec SMT.declareConst_addSpec_spec
    mrename_i predX
    mintro ∀St₁d
    mpure predX
    obtain ⟨hdX_decl, _, _, hdX_used, _⟩ := predX
    have havsub₁d : avoid ⊆ St₁d.env.usedVars := fun w h => by
      rw [hdX_used]; exact x!_used_sub (havsub h)
    mspec (loosenAux_prf_bv_declsEq_notMem _ havsub₁d (by intro v hv; exact hbvS v hv))
    mrename_i preS
    mintro ∀St₂
    rename_i Sout
    obtain ⟨S!, S!_spec⟩ := Sout
    mpure preS
    obtain ⟨S!_notMem, S!_bv, S!_used_sub, S!_decl⟩ := preS
    mspec SMT.declareConst_addSpec_spec
    mrename_i predS
    mintro ∀St₂d
    mpure predS
    obtain ⟨hdS_decl, _, _, hdS_used, _⟩ := predS
    mspec Std.Do.Spec.pure
    mpure_intro
    have lift1 : ∀ {w}, w ∈ St₁.env.usedVars → w ∈ St₂d.env.usedVars :=
      fun {w} h => by rw [hdS_used]; exact S!_used_sub (by rw [hdX_used]; exact h)
    refine ⟨_root_.helperSpecChunk x! α' x!_spec ++
        _root_.helperSpecChunk S! (.fun α' (.option β)) S!_spec,
      ?_, ?_, fun v hv => lift1 (x!_used_sub hv)⟩
    · rw [hdS_decl, S!_decl, hdX_decl, x!_decl]
      simp [_root_.helperSpecChunk, List.concat_eq_append, List.append_assoc]
    · exact DeltaBvNotMem.append
        (DeltaBvNotMem.helperSpecChunk x!_notMem x!_bv)
        (DeltaBvNotMem.helperSpecChunk S!_notMem S!_bv)
  case vc6.h_2.h_1.isFalse.isTrue.isTrue =>
    rename_i α' β' hσS α β hσx hα_nle hα'_le hβ_le St hpre
    obtain ⟨rfl, rfl, rfl⟩ := hpre
    mspec (loosenAux_prf_bv_declsEq_notMem _ havsub (by intro v hv; exact hbvx v (by rwa [SMT.bv] at hv)))
    mrename_i preY
    mintro ∀St₁
    rename_i yout
    obtain ⟨y!, y!_spec⟩ := yout
    mpure preY
    obtain ⟨y!_notMem, y!_bv, y!_used_sub, y!_decl⟩ := preY
    mspec SMT.declareConst_addSpec_spec
    mrename_i predY
    mintro ∀St₁d
    mpure predY
    obtain ⟨hdY_decl, _, _, hdY_used, _⟩ := predY
    have havsub₁d : avoid ⊆ St₁d.env.usedVars := fun w h => by
      rw [hdY_used]; exact y!_used_sub (havsub h)
    mspec (loosenAux_prf_bv_declsEq_notMem _ havsub₁d (by intro v hv; exact hbvS v hv))
    mrename_i preS
    mintro ∀St₂
    rename_i Sout
    obtain ⟨S!, S!_spec⟩ := Sout
    mpure preS
    obtain ⟨S!_notMem, S!_bv, S!_used_sub, S!_decl⟩ := preS
    mspec SMT.declareConst_addSpec_spec
    mrename_i predS
    mintro ∀St₂d
    mpure predS
    obtain ⟨hdS_decl, _, _, hdS_used, _⟩ := predS
    mspec Std.Do.Spec.pure
    mpure_intro
    have lift1 : ∀ {w}, w ∈ St₁.env.usedVars → w ∈ St₂d.env.usedVars :=
      fun {w} h => by rw [hdS_used]; exact S!_used_sub (by rw [hdY_used]; exact h)
    refine ⟨_root_.helperSpecChunk y! β' y!_spec ++
        _root_.helperSpecChunk S! (.fun α (.option β')) S!_spec,
      ?_, ?_, fun v hv => lift1 (y!_used_sub hv)⟩
    · rw [hdS_decl, S!_decl, hdY_decl, y!_decl]
      simp [_root_.helperSpecChunk, List.concat_eq_append, List.append_assoc]
    · exact DeltaBvNotMem.append
        (DeltaBvNotMem.helperSpecChunk y!_notMem y!_bv)
        (DeltaBvNotMem.helperSpecChunk S!_notMem S!_bv)
  case vc7.h_2.h_1.isFalse.isTrue.isFalse.isTrue =>
    rename_i α' β' hσS α β hσx hα_nle hα'_le hβ_nle hβ'_le St hpre
    obtain ⟨rfl, rfl, rfl⟩ := hpre
    mspec (loosenAux_prf_bv_declsEq_notMem _ havsub hbvS)
    mrename_i pre
    mintro ∀St₁
    rename_i Sout
    obtain ⟨S!, S!_spec⟩ := Sout
    mpure pre
    obtain ⟨S!_notMem, S!_bv, S!_used_sub, S!_decl⟩ := pre
    mspec SMT.declareConst_addSpec_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, hd_used, _⟩ := pred
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨_root_.helperSpecChunk S! (.fun α (.option β)) S!_spec, ?_,
      DeltaBvNotMem.helperSpecChunk S!_notMem S!_bv,
      fun v hv => by rw [hd_used]; exact S!_used_sub hv⟩
    rw [hd_decl, S!_decl]
    simp [_root_.helperSpecChunk, List.concat_eq_append, List.append_assoc]

set_option maxHeartbeats 4000000 in
/-- Dual declarations-delta spec of `castApp`: the spliced declarations' declared
names and `define_fun` spec-body bound variables avoid `avoid`. -/
theorem castApp_decls_bv_notMem (f x : SMT.Term) (sf sx : SMTType)
    {avoid used : List SMT.𝒱} {n : ℕ} {decl : SMT.Chunk} (havsub : avoid ⊆ used)
    (hbvf : ∀ v ∈ SMT.bv f, v ∉ avoid) (hbvx : ∀ v ∈ SMT.bv x, v ∉ avoid) :
    ⦃ fun (⟨E, _Λ'⟩ : EncoderState) ↦
        ⌜E.freshvarsc = n ∧ E.usedVars = used ∧ E.declarations = decl⌝ ⦄
    castApp (f, sf) (x, sx)
    ⦃ ⇓? (_ : SMT.Term × SMTType) (⟨E', _Γ'⟩ : EncoderState) =>
        ⌜∃ Dl : SMT.Chunk, E'.declarations = decl ++ Dl ∧ DeltaBvNotMem Dl avoid
          ∧ used ⊆ E'.usedVars⌝ ⦄ := by
  unfold castApp
  mvcgen
  case vc3.h_2.isTrue =>
    rename_i hxeq hfeq _ St hpre
    obtain ⟨rfl, rfl, rfl⟩ := hpre
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hxeq
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hfeq
    mspec (loosenAux_prf_bv_declsEq_notMem _ havsub hbvf)
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨L_notMem, L_bv, L_used_sub, L_decl⟩ := pre
    unfold SMT.declareConstWithSpec
    mspec Std.Do.Spec.bind
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, hd_used, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨hs_decl, _, _, hs_used, _⟩ := pres
    mspec Std.Do.Spec.pure
    mpure_intro
    exact ⟨_,
      by rw [hs_decl, hd_decl, L_decl, List.concat_eq_append, List.concat_eq_append,
        List.append_assoc],
      DeltaBvNotMem.append (DeltaBvNotMem.declare_const L_notMem)
        (DeltaBvNotMem.define_fun_spec L_bv),
      fun v hv => by rw [hs_used, hd_used]; exact L_used_sub hv⟩
  case vc4.h_2.isFalse.isTrue =>
    rename_i hxeq hfeq _ _ St hpre
    obtain ⟨rfl, rfl, rfl⟩ := hpre
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hxeq
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hfeq
    mspec (loosenAux_prf_bv_declsEq_notMem _ havsub hbvx)
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨L_notMem, L_bv, L_used_sub, L_decl⟩ := pre
    unfold SMT.declareConstWithSpec
    mspec Std.Do.Spec.bind
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, hd_used, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨hs_decl, _, _, hs_used, _⟩ := pres
    mspec Std.Do.Spec.pure
    mpure_intro
    exact ⟨_,
      by rw [hs_decl, hd_decl, L_decl, List.concat_eq_append, List.concat_eq_append,
        List.append_assoc],
      DeltaBvNotMem.append (DeltaBvNotMem.declare_const L_notMem)
        (DeltaBvNotMem.define_fun_spec L_bv),
      fun v hv => by rw [hs_used, hd_used]; exact L_used_sub hv⟩
  case vc5.h_3.isTrue =>
    rename_i hxeq hfeq _ St hpre
    obtain ⟨rfl, rfl, rfl⟩ := hpre
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hxeq
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hfeq
    mspec (loosenAux_prf_bv_declsEq_notMem _ havsub hbvf)
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨L_notMem, L_bv, L_used_sub, L_decl⟩ := pre
    unfold SMT.declareConstWithSpec
    mspec Std.Do.Spec.bind
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, hd_used, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨hs_decl, _, _, hs_used, _⟩ := pres
    mspec Std.Do.Spec.pure
    mpure_intro
    exact ⟨_,
      by rw [hs_decl, hd_decl, L_decl, List.concat_eq_append, List.concat_eq_append,
        List.append_assoc],
      DeltaBvNotMem.append (DeltaBvNotMem.declare_const L_notMem)
        (DeltaBvNotMem.define_fun_spec L_bv),
      fun v hv => by rw [hs_used, hd_used]; exact L_used_sub hv⟩
  case vc6.h_3.isFalse.isTrue =>
    rename_i hxeq hfeq _ _ St hpre
    obtain ⟨rfl, rfl, rfl⟩ := hpre
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hxeq
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hfeq
    mspec (loosenAux_prf_bv_declsEq_notMem _ havsub hbvx)
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨L_notMem, L_bv, L_used_sub, L_decl⟩ := pre
    unfold SMT.declareConstWithSpec
    mspec Std.Do.Spec.bind
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, hd_used, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨hs_decl, _, _, hs_used, _⟩ := pres
    mspec Std.Do.Spec.pure
    mpure_intro
    exact ⟨_,
      by rw [hs_decl, hd_decl, L_decl, List.concat_eq_append, List.concat_eq_append,
        List.append_assoc],
      DeltaBvNotMem.append (DeltaBvNotMem.declare_const L_notMem)
        (DeltaBvNotMem.define_fun_spec L_bv),
      fun v hv => by rw [hs_used, hd_used]; exact L_used_sub hv⟩
  case vc1.h_1.isTrue =>
    rename_i hxeq hfeq _ St hpre
    obtain ⟨rfl, rfl, rfl⟩ := hpre
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hxeq
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hfeq
    mspec (loosenAux_prf_bv_declsEq_notMem _ havsub hbvf)
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨f!_notMem, f!_bv, f!_used_sub, f!_decl⟩ := pre
    unfold SMT.declareConstWithSpec
    mspec Std.Do.Spec.bind
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, hd_used, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨hs_decl, _, _, hs_used, _⟩ := pres
    have havsub₁s : avoid ⊆ St₁s.env.usedVars := fun w h => by
      rw [hs_used, hd_used]; exact f!_used_sub (havsub h)
    mspec (Std.Do.Triple.and _ SMT.freshVar_spec (SMT.freshVar_decls (decl := St₁s.env.declarations)))
    mrename_i pre2
    mintro ∀St₂
    mpure pre2
    obtain ⟨⟨_, _, _, St₂_used_eq, app_notMem⟩, St₂_decl⟩ := pre2
    mspec SMT.declareConst_spec
    mrename_i pred2
    mintro ∀St₂d
    mpure pred2
    obtain ⟨hd2_decl, _, _, hd2_used, _⟩ := pred2
    mspec (Std.Do.Triple.and _ SMT.freshVar_spec (SMT.freshVar_decls (decl := St₂d.env.declarations)))
    mrename_i pre3
    mintro ∀St₃
    mpure pre3
    obtain ⟨⟨_, _, _, St₃_used_eq, a_notMem⟩, St₃_decl⟩ := pre3
    mspec (Std.Do.Triple.and _ SMT.freshVar_spec (SMT.freshVar_decls (decl := St₃.env.declarations)))
    mrename_i pre4
    mintro ∀St₄
    mpure pre4
    obtain ⟨⟨_, _, _, St₄_used_eq, b_notMem⟩, St₄_decl⟩ := pre4
    mspec SMT.eraseFromContext_used_decls
    mrename_i pre5
    mintro ∀St5
    mpure pre5
    obtain ⟨St5_used_eq, St5_decl⟩ := pre5
    mspec SMT.eraseFromContext_used_decls
    mrename_i pre6
    mintro ∀St6
    mpure pre6
    obtain ⟨St6_used_eq, St6_decl⟩ := pre6
    mspec SMT.addSpec_spec
    mrename_i pres2
    mintro ∀St6s
    mpure pres2
    obtain ⟨hs2_decl, _, _, hs2_used, _⟩ := pres2
    mspec Std.Do.Spec.pure
    mpure_intro
    have app_notMem_avoid : _ ∉ avoid := fun h => app_notMem (havsub₁s h)
    have havsub₂d : avoid ⊆ St₂d.env.usedVars := fun w h => by
      rw [hd2_used, St₂_used_eq]; exact List.mem_cons_of_mem _ (havsub₁s h)
    have a_notMem_avoid : _ ∉ avoid := fun h => a_notMem (havsub₂d h)
    have havsub₃ : avoid ⊆ St₃.env.usedVars := fun w h => by
      rw [St₃_used_eq]; exact List.mem_cons_of_mem _ (havsub₂d h)
    have b_notMem_avoid : _ ∉ avoid := fun h => b_notMem (havsub₃ h)
    exact ⟨_,
      by rw [hs2_decl, St6_decl, St5_decl, St₄_decl, St₃_decl, hd2_decl, St₂_decl,
           hs_decl, hd_decl, f!_decl]
         simp only [List.concat_eq_append, List.append_assoc, List.cons_append, List.nil_append]
         rfl,
      by
        refine ⟨fun v hv => ?_, fun b hb v hv => ?_⟩
        · simp only [declVars, List.filterMap_cons, List.filterMap_nil, List.mem_cons,
            List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl
          · exact f!_notMem
          · exact app_notMem_avoid
        · simp only [specBodies, List.filterMap_cons, List.filterMap_nil, List.mem_cons,
            List.not_mem_nil, or_false] at hb
          rcases hb with rfl | rfl
          · exact f!_bv v hv
          · simp only [SMT.bv, List.append_nil, List.mem_cons,
              List.not_mem_nil, or_false] at hv
            rcases hv with rfl | rfl
            · exact a_notMem_avoid
            · exact b_notMem_avoid,
      fun w hw => by
        rw [hs2_used, St6_used_eq, St5_used_eq, St₄_used_eq, St₃_used_eq, hd2_used,
          St₂_used_eq, hs_used, hd_used]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (f!_used_sub hw)))⟩
  case vc2.h_1.isFalse.isTrue =>
    rename_i hxeq hfeq _ _ St hpre
    obtain ⟨rfl, rfl, rfl⟩ := hpre
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hxeq
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hfeq
    mspec (loosenAux_prf_bv_declsEq_notMem _ havsub hbvx)
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨x!_notMem, x!_bv, x!_used_sub, x!_decl⟩ := pre
    unfold SMT.declareConstWithSpec
    mspec Std.Do.Spec.bind
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, hd_used, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨hs_decl, _, _, hs_used, _⟩ := pres
    have havsub₁s : avoid ⊆ St₁s.env.usedVars := fun w h => by
      rw [hs_used, hd_used]; exact x!_used_sub (havsub h)
    mspec (Std.Do.Triple.and _ SMT.freshVar_spec (SMT.freshVar_decls (decl := St₁s.env.declarations)))
    mrename_i pre2
    mintro ∀St₂
    mpure pre2
    obtain ⟨⟨_, _, _, St₂_used_eq, app_notMem⟩, St₂_decl⟩ := pre2
    mspec SMT.declareConst_spec
    mrename_i pred2
    mintro ∀St₂d
    mpure pred2
    obtain ⟨hd2_decl, _, _, hd2_used, _⟩ := pred2
    mspec (Std.Do.Triple.and _ SMT.freshVar_spec (SMT.freshVar_decls (decl := St₂d.env.declarations)))
    mrename_i pre3
    mintro ∀St₃
    mpure pre3
    obtain ⟨⟨_, _, _, St₃_used_eq, a_notMem⟩, St₃_decl⟩ := pre3
    mspec (Std.Do.Triple.and _ SMT.freshVar_spec (SMT.freshVar_decls (decl := St₃.env.declarations)))
    mrename_i pre4
    mintro ∀St₄
    mpure pre4
    obtain ⟨⟨_, _, _, St₄_used_eq, b_notMem⟩, St₄_decl⟩ := pre4
    mspec SMT.eraseFromContext_used_decls
    mrename_i pre5
    mintro ∀St5
    mpure pre5
    obtain ⟨St5_used_eq, St5_decl⟩ := pre5
    mspec SMT.eraseFromContext_used_decls
    mrename_i pre6
    mintro ∀St6
    mpure pre6
    obtain ⟨St6_used_eq, St6_decl⟩ := pre6
    mspec SMT.addSpec_spec
    mrename_i pres2
    mintro ∀St6s
    mpure pres2
    obtain ⟨hs2_decl, _, _, hs2_used, _⟩ := pres2
    mspec Std.Do.Spec.pure
    mpure_intro
    have app_notMem_avoid : _ ∉ avoid := fun h => app_notMem (havsub₁s h)
    have havsub₂d : avoid ⊆ St₂d.env.usedVars := fun w h => by
      rw [hd2_used, St₂_used_eq]; exact List.mem_cons_of_mem _ (havsub₁s h)
    have a_notMem_avoid : _ ∉ avoid := fun h => a_notMem (havsub₂d h)
    have havsub₃ : avoid ⊆ St₃.env.usedVars := fun w h => by
      rw [St₃_used_eq]; exact List.mem_cons_of_mem _ (havsub₂d h)
    have b_notMem_avoid : _ ∉ avoid := fun h => b_notMem (havsub₃ h)
    exact ⟨_,
      by rw [hs2_decl, St6_decl, St5_decl, St₄_decl, St₃_decl, hd2_decl, St₂_decl,
           hs_decl, hd_decl, x!_decl]
         simp only [List.concat_eq_append, List.append_assoc, List.cons_append, List.nil_append]
         rfl,
      by
        refine ⟨fun v hv => ?_, fun b hb v hv => ?_⟩
        · simp only [declVars, List.filterMap_cons, List.filterMap_nil, List.mem_cons,
            List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl
          · exact x!_notMem
          · exact app_notMem_avoid
        · simp only [specBodies, List.filterMap_cons, List.filterMap_nil, List.mem_cons,
            List.not_mem_nil, or_false] at hb
          rcases hb with rfl | rfl
          · exact x!_bv v hv
          · simp only [SMT.bv, List.append_nil, List.mem_append, List.mem_cons,
              List.not_mem_nil, or_false] at hv
            rcases hv with (rfl | rfl) | hf
            · exact a_notMem_avoid
            · exact b_notMem_avoid
            · exact hbvf v hf,
      fun w hw => by
        rw [hs2_used, St6_used_eq, St5_used_eq, St₄_used_eq, St₃_used_eq, hd2_used,
          St₂_used_eq, hs_used, hd_used]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (x!_used_sub hw)))⟩

set_option maxHeartbeats 4000000 in
/-- Dual declarations-delta spec of `castUnionAux`: the spliced delta declares `S!`
(`∉ avoid`) and adds a `define_fun` whose spec-body bound variables avoid `avoid`. -/
theorem castUnionAux_decls_bv_notMem {α β : SMTType} (c : α ~> β) (S T : SMT.Term)
    {avoid used : List SMT.𝒱} {n : ℕ} {decl : SMT.Chunk} (havsub : avoid ⊆ used)
    (hbvS : ∀ v ∈ SMT.bv S, v ∉ avoid) :
    ⦃ fun (⟨E, _Λ'⟩ : EncoderState) ↦
        ⌜E.freshvarsc = n ∧ E.usedVars = used ∧ E.declarations = decl⌝ ⦄
    castUnionAux S T c
    ⦃ ⇓? (_ : SMT.Term × SMTType) (⟨E', _Γ'⟩ : EncoderState) =>
        ⌜∃ Dl : SMT.Chunk, E'.declarations = decl ++ Dl ∧ DeltaBvNotMem Dl avoid
          ∧ used ⊆ E'.usedVars⌝ ⦄ := by
  cases c with
  | @graph α β α' β' c_α c_β =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    unfold castUnionAux castUnion.graph
    mspec (loosenAux_prf_bv_declsEq_notMem _ havsub hbvS)
    mrename_i pre
    mintro ∀St₁
    rename_i S!_pair
    obtain ⟨S!, S!_spec⟩ := S!_pair
    mpure pre
    obtain ⟨S!_notMem, S!_bv, S!_used_sub, S!_decl⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, hd_used, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨hs_decl, _, _, hs_used, _⟩ := pres
    mspec SMT.freshVar_spec_decls
    mrename_i pre2
    mintro ∀St₂
    mpure pre2
    obtain ⟨St₂_used_eq, St₂_decl⟩ := pre2
    rename_i x
    mspec SMT.eraseFromContext_used_decls (v := x)
      (used := St₂.env.usedVars) (decl := St₂.env.declarations)
    mrename_i pre3
    mintro ∀St₃
    mpure pre3
    obtain ⟨St₃_used_eq, St₃_decl⟩ := pre3
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨[.declare_const S! (.fun (.pair α' β') .bool),
      .define_fun s!"{S!}_spec" .unit .bool S!_spec], ?_,
      DeltaBvNotMem.append (DeltaBvNotMem.declare_const S!_notMem)
        (DeltaBvNotMem.define_fun_spec S!_bv),
      fun v hv => by
        rw [St₃_used_eq, St₂_used_eq, hs_used, hd_used]
        exact List.mem_cons_of_mem _ (S!_used_sub hv)⟩
    rw [St₃_decl, St₂_decl, hs_decl, hd_decl, S!_decl,
      List.concat_eq_append, List.concat_eq_append,
      List.append_assoc, List.cons_append, List.nil_append]
  | @«fun» α β α' β' hβ c_α c_β =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    unfold castUnionAux castUnion.fun
    mspec (loosenAux_prf_bv_declsEq_notMem _ havsub hbvS)
    mrename_i pre
    mintro ∀St₁
    rename_i S!_pair
    obtain ⟨S!, S!_spec⟩ := S!_pair
    mpure pre
    obtain ⟨S!_notMem, S!_bv, S!_used_sub, S!_decl⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, hd_used, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨hs_decl, _, _, hs_used, _⟩ := pres
    split
    · rename_i σ _
      mspec SMT.freshVar_spec_decls
      mrename_i pre2
      mintro ∀St₂
      mpure pre2
      obtain ⟨St₂_used_eq, St₂_decl⟩ := pre2
      mspec Std.Do.Spec.pure
      mpure_intro
      refine ⟨[.declare_const S! (.fun α' (.option σ)),
        .define_fun s!"{S!}_spec" .unit .bool S!_spec], ?_,
        DeltaBvNotMem.append (DeltaBvNotMem.declare_const S!_notMem)
          (DeltaBvNotMem.define_fun_spec S!_bv),
        fun v hv => by rw [St₂_used_eq, hs_used, hd_used]; exact List.mem_cons_of_mem _ (S!_used_sub hv)⟩
      rw [St₂_decl, hs_decl, hd_decl, S!_decl, List.concat_eq_append, List.concat_eq_append,
        List.append_assoc, List.cons_append, List.nil_append]
    · mvcgen
  | @chpred α α' c_α =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    unfold castUnionAux castUnion.chpred
    mspec (loosenAux_prf_bv_declsEq_notMem _ havsub hbvS)
    mrename_i pre
    mintro ∀St₁
    rename_i S!_pair
    obtain ⟨S!, S!_spec⟩ := S!_pair
    mpure pre
    obtain ⟨S!_notMem, S!_bv, S!_used_sub, S!_decl⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, hd_used, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨hs_decl, _, _, hs_used, _⟩ := pres
    mspec SMT.freshVar_spec_decls
    mrename_i pre2
    mintro ∀St₂
    mpure pre2
    obtain ⟨St₂_used_eq, St₂_decl⟩ := pre2
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨[.declare_const S! (.fun α' .bool),
      .define_fun s!"{S!}_spec" .unit .bool S!_spec], ?_,
      DeltaBvNotMem.append (DeltaBvNotMem.declare_const S!_notMem)
        (DeltaBvNotMem.define_fun_spec S!_bv),
      fun v hv => by rw [St₂_used_eq, hs_used, hd_used]; exact List.mem_cons_of_mem _ (S!_used_sub hv)⟩
    rw [St₂_decl, hs_decl, hd_decl, S!_decl, List.concat_eq_append, List.concat_eq_append,
      List.append_assoc, List.cons_append, List.nil_append]
  | @opt α α' c_α =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    unfold castUnionAux castUnion.opt
    mvcgen
  | @pair α β α' β' c_α c_β =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    unfold castUnionAux castUnion.pair
    mvcgen
  | @refl α hα =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    unfold castUnionAux castUnion.refl
    mvcgen

set_option maxHeartbeats 4000000 in
/-- Dual declarations-delta spec of `castInterAux` (identical to `castUnionAux`). -/
theorem castInterAux_decls_bv_notMem {α β : SMTType} (c : α ~> β) (S T : SMT.Term)
    {avoid used : List SMT.𝒱} {n : ℕ} {decl : SMT.Chunk} (havsub : avoid ⊆ used)
    (hbvS : ∀ v ∈ SMT.bv S, v ∉ avoid) :
    ⦃ fun (⟨E, _Λ'⟩ : EncoderState) ↦
        ⌜E.freshvarsc = n ∧ E.usedVars = used ∧ E.declarations = decl⌝ ⦄
    castInterAux S T c
    ⦃ ⇓? (_ : SMT.Term × SMTType) (⟨E', _Γ'⟩ : EncoderState) =>
        ⌜∃ Dl : SMT.Chunk, E'.declarations = decl ++ Dl ∧ DeltaBvNotMem Dl avoid
          ∧ used ⊆ E'.usedVars⌝ ⦄ := by
  cases c with
  | @graph α β α' β' c_α c_β =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    unfold castInterAux
    mspec (loosenAux_prf_bv_declsEq_notMem _ havsub hbvS)
    mrename_i pre
    mintro ∀St₁
    rename_i S!_pair
    obtain ⟨S!, S!_spec⟩ := S!_pair
    mpure pre
    obtain ⟨S!_notMem, S!_bv, S!_used_sub, S!_decl⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, hd_used, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨hs_decl, _, _, hs_used, _⟩ := pres
    mspec SMT.freshVar_spec_decls
    mrename_i pre2
    mintro ∀St₂
    mpure pre2
    obtain ⟨St₂_used_eq, St₂_decl⟩ := pre2
    rename_i x
    mspec SMT.eraseFromContext_used_decls (v := x)
      (used := St₂.env.usedVars) (decl := St₂.env.declarations)
    mrename_i pre3
    mintro ∀St₃
    mpure pre3
    obtain ⟨St₃_used_eq, St₃_decl⟩ := pre3
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨[.declare_const S! (.fun (.pair α' β') .bool),
      .define_fun s!"{S!}_spec" .unit .bool S!_spec], ?_,
      DeltaBvNotMem.append (DeltaBvNotMem.declare_const S!_notMem)
        (DeltaBvNotMem.define_fun_spec S!_bv),
      fun v hv => by
        rw [St₃_used_eq, St₂_used_eq, hs_used, hd_used]
        exact List.mem_cons_of_mem _ (S!_used_sub hv)⟩
    rw [St₃_decl, St₂_decl, hs_decl, hd_decl, S!_decl,
      List.concat_eq_append, List.concat_eq_append,
      List.append_assoc, List.cons_append, List.nil_append]
  | @«fun» α β α' β' hβ c_α c_β =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    unfold castInterAux
    mspec (loosenAux_prf_bv_declsEq_notMem _ havsub hbvS)
    mrename_i pre
    mintro ∀St₁
    rename_i S!_pair
    obtain ⟨S!, S!_spec⟩ := S!_pair
    mpure pre
    obtain ⟨S!_notMem, S!_bv, S!_used_sub, S!_decl⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, hd_used, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨hs_decl, _, _, hs_used, _⟩ := pres
    split
    · rename_i σ _
      mspec SMT.freshVar_spec_decls
      mrename_i pre2
      mintro ∀St₂
      mpure pre2
      obtain ⟨St₂_used_eq, St₂_decl⟩ := pre2
      mspec Std.Do.Spec.pure
      mpure_intro
      refine ⟨[.declare_const S! (.fun α' (.option σ)),
        .define_fun s!"{S!}_spec" .unit .bool S!_spec], ?_,
        DeltaBvNotMem.append (DeltaBvNotMem.declare_const S!_notMem)
          (DeltaBvNotMem.define_fun_spec S!_bv),
        fun v hv => by rw [St₂_used_eq, hs_used, hd_used]; exact List.mem_cons_of_mem _ (S!_used_sub hv)⟩
      rw [St₂_decl, hs_decl, hd_decl, S!_decl, List.concat_eq_append, List.concat_eq_append,
        List.append_assoc, List.cons_append, List.nil_append]
    · mvcgen
  | @chpred α α' c_α =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    unfold castInterAux
    mspec (loosenAux_prf_bv_declsEq_notMem _ havsub hbvS)
    mrename_i pre
    mintro ∀St₁
    rename_i S!_pair
    obtain ⟨S!, S!_spec⟩ := S!_pair
    mpure pre
    obtain ⟨S!_notMem, S!_bv, S!_used_sub, S!_decl⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, hd_used, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨hs_decl, _, _, hs_used, _⟩ := pres
    mspec SMT.freshVar_spec_decls
    mrename_i pre2
    mintro ∀St₂
    mpure pre2
    obtain ⟨St₂_used_eq, St₂_decl⟩ := pre2
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨[.declare_const S! (.fun α' .bool),
      .define_fun s!"{S!}_spec" .unit .bool S!_spec], ?_,
      DeltaBvNotMem.append (DeltaBvNotMem.declare_const S!_notMem)
        (DeltaBvNotMem.define_fun_spec S!_bv),
      fun v hv => by rw [St₂_used_eq, hs_used, hd_used]; exact List.mem_cons_of_mem _ (S!_used_sub hv)⟩
    rw [St₂_decl, hs_decl, hd_decl, S!_decl, List.concat_eq_append, List.concat_eq_append,
      List.append_assoc, List.cons_append, List.nil_append]
  | @opt α α' c_α =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    unfold castInterAux
    mvcgen
  | @pair α β α' β' c_α c_β =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    unfold castInterAux
    mvcgen
  | @refl α hα =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    unfold castInterAux
    mvcgen

set_option maxHeartbeats 4000000 in
/-- Dual declarations-delta spec of the `castUnion` wrapper. -/
theorem castUnion_decls_bv_notMem (S T : SMT.Term) (sS sT : SMTType)
    {avoid used : List SMT.𝒱} {n : ℕ} {decl : SMT.Chunk} (havsub : avoid ⊆ used)
    (hbvS : ∀ v ∈ SMT.bv S, v ∉ avoid) (hbvT : ∀ v ∈ SMT.bv T, v ∉ avoid) :
    ⦃ fun (⟨E, _Λ'⟩ : EncoderState) ↦
        ⌜E.freshvarsc = n ∧ E.usedVars = used ∧ E.declarations = decl⌝ ⦄
    castUnion (S, sS) (T, sT)
    ⦃ ⇓? (_ : SMT.Term × SMTType) (⟨E', _Γ'⟩ : EncoderState) =>
        ⌜∃ Dl : SMT.Chunk, E'.declarations = decl ++ Dl ∧ DeltaBvNotMem Dl avoid
          ∧ used ⊆ E'.usedVars⌝ ⦄ := by
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, rfl⟩ := pre
  unfold castUnion
  split
  split
  rename_i heqA _ _ _ heqB
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heqA
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heqB
  split_ifs with heq hsub1 hsub2
  · subst heq
    split
    · mspec SMT.freshVar_spec_decls
      mrename_i pre2
      mintro ∀St₂
      mpure pre2
      obtain ⟨St₂_used_eq, St₂_decl⟩ := pre2
      mspec (Std.Do.Triple.and _ SMT.eraseFromContext_spec
        (SMT.eraseFromContext_decls (decl := St₂.env.declarations)))
      mrename_i preE
      mintro ∀St₃
      mpure preE
      obtain ⟨⟨_, _, St₃_used_eq⟩, St₃_decl⟩ := preE
      mspec Std.Do.Spec.pure
      mpure_intro
      refine ⟨[], ?_, DeltaBvNotMem_nil, fun v hv => ?_⟩
      · rw [St₃_decl, St₂_decl, List.append_nil]
      · rw [St₃_used_eq, St₂_used_eq]; exact List.mem_cons_of_mem _ hv
    all_goals mvcgen
  · mspec (castUnionAux_decls_bv_notMem _ S T havsub hbvS)
  · mspec (castUnionAux_decls_bv_notMem _ T S havsub hbvT)
  · mvcgen

set_option maxHeartbeats 4000000 in
/-- Dual declarations-delta spec of the `castInter` wrapper. -/
theorem castInter_decls_bv_notMem (S T : SMT.Term) (sS sT : SMTType)
    {avoid used : List SMT.𝒱} {n : ℕ} {decl : SMT.Chunk} (havsub : avoid ⊆ used)
    (hbvS : ∀ v ∈ SMT.bv S, v ∉ avoid) (hbvT : ∀ v ∈ SMT.bv T, v ∉ avoid) :
    ⦃ fun (⟨E, _Λ'⟩ : EncoderState) ↦
        ⌜E.freshvarsc = n ∧ E.usedVars = used ∧ E.declarations = decl⌝ ⦄
    castInter (S, sS) (T, sT)
    ⦃ ⇓? (_ : SMT.Term × SMTType) (⟨E', _Γ'⟩ : EncoderState) =>
        ⌜∃ Dl : SMT.Chunk, E'.declarations = decl ++ Dl ∧ DeltaBvNotMem Dl avoid
          ∧ used ⊆ E'.usedVars⌝ ⦄ := by
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, rfl⟩ := pre
  unfold castInter
  split
  split
  rename_i heqA _ _ _ heqB
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heqA
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heqB
  split_ifs with heq hsub1 hsub2
  · subst heq
    split
    · mspec SMT.freshVar_spec_decls
      mrename_i pre2
      mintro ∀St₂
      mpure pre2
      obtain ⟨St₂_used_eq, St₂_decl⟩ := pre2
      mspec (Std.Do.Triple.and _ SMT.eraseFromContext_spec
        (SMT.eraseFromContext_decls (decl := St₂.env.declarations)))
      mrename_i preE
      mintro ∀St₃
      mpure preE
      obtain ⟨⟨_, _, St₃_used_eq⟩, St₃_decl⟩ := preE
      mspec Std.Do.Spec.pure
      mpure_intro
      refine ⟨[], ?_, DeltaBvNotMem_nil, fun v hv => ?_⟩
      · rw [St₃_decl, St₂_decl, List.append_nil]
      · rw [St₃_used_eq, St₂_used_eq]; exact List.mem_cons_of_mem _ hv
    all_goals mvcgen
  · mspec (castInterAux_decls_bv_notMem _ S T havsub hbvS)
  · mspec (castInterAux_decls_bv_notMem _ T S havsub hbvT)
  · mvcgen

set_option maxHeartbeats 4000000 in
/-- Freshness companion of `encodeTerm_bv_used`: every bound variable of the encoded
term avoids the *input* `usedVars`. Carries `usedVars` monotonicity and a
`DeltaBvNotMem` invariant on the spliced declarations so the binder cases compose. -/
theorem encodeTerm_bv_notMem_used
    (E : B.Env) {t : B.Term} {used : List SMT.𝒱} {n : ℕ} {decl : SMT.Chunk} :
    ⦃ fun (⟨E0, _Λ'⟩ : EncoderState) ↦
        ⌜E0.freshvarsc = n ∧ E0.usedVars = used ∧ E0.declarations = decl⌝ ⦄
    encodeTerm t E
    ⦃ ⇓? (⟨t', _σ⟩ : SMT.Term × SMTType) (⟨E', _Γ'⟩ : EncoderState) => ⌜
      (∀ v ∈ SMT.bv t', v ∉ used) ∧ used ⊆ E'.usedVars ∧
      ∃ Dl : SMT.Chunk, E'.declarations = decl ++ Dl ∧ DeltaBvNotMem Dl used ⌝⦄ := by
  induction t generalizing E n used decl with
  | int i =>
    mstart
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    rw [encodeTerm]
    mspec Std.Do.Spec.pure
    mpure_intro
    exact ⟨by intro v hv; simp [SMT.bv] at hv, fun _ h => h, [], by simp, DeltaBvNotMem_nil⟩
  | bool b =>
    mstart
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    rw [encodeTerm]
    mspec Std.Do.Spec.pure
    mpure_intro
    exact ⟨by intro v hv; simp [SMT.bv] at hv, fun _ h => h, [], by simp, DeltaBvNotMem_nil⟩
  | var v =>
    mstart
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    rw [encodeTerm]
    mvcgen
    case vc1 τ τ_lookup =>
      exact ⟨by intro v hv; simp [SMT.bv] at hv, fun _ h => h, [], by simp, DeltaBvNotMem_nil⟩
  | «ℤ» =>
    mstart
    mintro pre ∀S
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    rw [encodeTerm]
    mspec Std.Do.Spec.get_StateT
    mspec (Std.Do.Triple.and _ SMT.freshVar_spec (SMT.freshVar_decls (decl := S.env.declarations)))
    case post.success 𝓋 =>
      mrename_i pre
      mintro ∀S'
      mpure pre
      obtain ⟨⟨_, _, _, used_eq, v_notMem⟩, decl_eq⟩ := pre
      mspec Std.Do.Spec.modifyGet_StateT
      mspec Std.Do.Spec.pure
      mpure_intro
      refine ⟨?_, ?_, [], ?_, DeltaBvNotMem_nil⟩
      · intro v hv
        simp only [SMT.bv, List.append_nil, List.mem_singleton] at hv
        subst hv
        exact v_notMem
      · rw [used_eq]; intro x hx; exact List.mem_cons_of_mem _ hx
      · rw [decl_eq, List.append_nil]
  | 𝔹 =>
    mstart
    mintro pre ∀S
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    rw [encodeTerm]
    mspec Std.Do.Spec.get_StateT
    mspec (Std.Do.Triple.and _ SMT.freshVar_spec (SMT.freshVar_decls (decl := S.env.declarations)))
    case post.success 𝓋 =>
      mrename_i pre
      mintro ∀S'
      mpure pre
      obtain ⟨⟨_, _, _, used_eq, v_notMem⟩, decl_eq⟩ := pre
      mspec Std.Do.Spec.modifyGet_StateT
      mspec Std.Do.Spec.pure
      mpure_intro
      refine ⟨?_, ?_, [], ?_, DeltaBvNotMem_nil⟩
      · intro v hv
        simp only [SMT.bv, List.append_nil, List.mem_singleton] at hv
        subst hv
        exact v_notMem
      · rw [used_eq]; intro x hx; exact List.mem_cons_of_mem _ hx
      · rw [decl_eq, List.append_nil]
  | maplet x y x_ih y_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    rw [encodeTerm]
    mspec x_ih (E := E)
    rename_i out_x
    obtain ⟨x_enc, σx⟩ := out_x
    mrename_i prex
    mintro ∀σ_x
    mpure prex
    obtain ⟨x_bv, x_used_sub, Δx, hxdecl, hxok⟩ := prex
    mspec y_ih (E := E) (used := σ_x.env.usedVars) (decl := σ_x.env.declarations)
    rename_i out_y
    obtain ⟨y_enc, σy⟩ := out_y
    mrename_i prey
    mintro ∀σ_y
    mpure prey
    obtain ⟨y_bv, y_used_sub, Δy, hydecl, hyok⟩ := prey
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨?_, fun v hv => y_used_sub (x_used_sub hv), Δx ++ Δy, ?_, ?_⟩
    · intro v hv
      simp only [SMT.bv, List.mem_append] at hv
      rcases hv with hv | hv
      · exact x_bv v hv
      · exact fun hmem => y_bv v hv (x_used_sub hmem)
    · rw [hydecl, hxdecl, List.append_assoc]
    · exact DeltaBvNotMem.append hxok (hyok.mono x_used_sub)
  | add x y x_ih y_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    rw [encodeTerm]
    mspec x_ih (E := E)
    rename_i out_x
    obtain ⟨x_enc, σx⟩ := out_x
    mrename_i prex
    mintro ∀σ_x
    mpure prex
    obtain ⟨x_bv, x_used_sub, Δx, hxdecl, hxok⟩ := prex
    split
    · rename_i heq
      injection heq with hxe hσe
      subst hσe
      subst hxe
      mspec y_ih (E := E) (used := σ_x.env.usedVars) (decl := σ_x.env.declarations)
      rename_i out_y
      obtain ⟨y_enc, σy⟩ := out_y
      mrename_i prey
      mintro ∀σ_y
      mpure prey
      obtain ⟨y_bv, y_used_sub, Δy, hydecl, hyok⟩ := prey
      split
      · rename_i heq2
        injection heq2 with hye hσe2
        subst hσe2
        subst hye
        mspec Std.Do.Spec.pure
        mpure_intro
        refine ⟨?_, fun v hv => y_used_sub (x_used_sub hv), Δx ++ Δy, ?_, ?_⟩
        · intro v hv
          simp only [SMT.bv, List.mem_append] at hv
          rcases hv with hv | hv
          · exact x_bv v hv
          · exact fun hmem => y_bv v hv (x_used_sub hmem)
        · rw [hydecl, hxdecl, List.append_assoc]
        · exact DeltaBvNotMem.append hxok (hyok.mono x_used_sub)
      · exact wp_bind_throw _ _ _ _
    · exact wp_bind_throw _ _ _ _
  | sub x y x_ih y_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    rw [encodeTerm]
    mspec x_ih (E := E)
    rename_i out_x
    obtain ⟨x_enc, σx⟩ := out_x
    mrename_i prex
    mintro ∀σ_x
    mpure prex
    obtain ⟨x_bv, x_used_sub, Δx, hxdecl, hxok⟩ := prex
    split
    · rename_i heq
      injection heq with hxe hσe
      subst hσe
      subst hxe
      mspec y_ih (E := E) (used := σ_x.env.usedVars) (decl := σ_x.env.declarations)
      rename_i out_y
      obtain ⟨y_enc, σy⟩ := out_y
      mrename_i prey
      mintro ∀σ_y
      mpure prey
      obtain ⟨y_bv, y_used_sub, Δy, hydecl, hyok⟩ := prey
      split
      · rename_i heq2
        injection heq2 with hye hσe2
        subst hσe2
        subst hye
        mspec Std.Do.Spec.pure
        mpure_intro
        refine ⟨?_, fun v hv => y_used_sub (x_used_sub hv), Δx ++ Δy, ?_, ?_⟩
        · intro v hv
          simp only [SMT.bv, List.mem_append] at hv
          rcases hv with hv | hv
          · exact x_bv v hv
          · exact fun hmem => y_bv v hv (x_used_sub hmem)
        · rw [hydecl, hxdecl, List.append_assoc]
        · exact DeltaBvNotMem.append hxok (hyok.mono x_used_sub)
      · exact wp_bind_throw _ _ _ _
    · exact wp_bind_throw _ _ _ _
  | mul x y x_ih y_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    rw [encodeTerm]
    mspec x_ih (E := E)
    rename_i out_x
    obtain ⟨x_enc, σx⟩ := out_x
    mrename_i prex
    mintro ∀σ_x
    mpure prex
    obtain ⟨x_bv, x_used_sub, Δx, hxdecl, hxok⟩ := prex
    split
    · rename_i heq
      injection heq with hxe hσe
      subst hσe
      subst hxe
      mspec y_ih (E := E) (used := σ_x.env.usedVars) (decl := σ_x.env.declarations)
      rename_i out_y
      obtain ⟨y_enc, σy⟩ := out_y
      mrename_i prey
      mintro ∀σ_y
      mpure prey
      obtain ⟨y_bv, y_used_sub, Δy, hydecl, hyok⟩ := prey
      split
      · rename_i heq2
        injection heq2 with hye hσe2
        subst hσe2
        subst hye
        mspec Std.Do.Spec.pure
        mpure_intro
        refine ⟨?_, fun v hv => y_used_sub (x_used_sub hv), Δx ++ Δy, ?_, ?_⟩
        · intro v hv
          simp only [SMT.bv, List.mem_append] at hv
          rcases hv with hv | hv
          · exact x_bv v hv
          · exact fun hmem => y_bv v hv (x_used_sub hmem)
        · rw [hydecl, hxdecl, List.append_assoc]
        · exact DeltaBvNotMem.append hxok (hyok.mono x_used_sub)
      · exact wp_bind_throw _ _ _ _
    · exact wp_bind_throw _ _ _ _
  | le x y x_ih y_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    rw [encodeTerm]
    mspec x_ih (E := E)
    rename_i out_x
    obtain ⟨x_enc, σx⟩ := out_x
    mrename_i prex
    mintro ∀σ_x
    mpure prex
    obtain ⟨x_bv, x_used_sub, Δx, hxdecl, hxok⟩ := prex
    mspec y_ih (E := E) (used := σ_x.env.usedVars) (decl := σ_x.env.declarations)
    rename_i out_y
    obtain ⟨y_enc, σy⟩ := out_y
    mrename_i prey
    mintro ∀σ_y
    mpure prey
    obtain ⟨y_bv, y_used_sub, Δy, hydecl, hyok⟩ := prey
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨?_, fun v hv => y_used_sub (x_used_sub hv), Δx ++ Δy, ?_, ?_⟩
    · intro v hv
      simp only [SMT.bv, List.mem_append] at hv
      rcases hv with hv | hv
      · exact x_bv v hv
      · exact fun hmem => y_bv v hv (x_used_sub hmem)
    · rw [hydecl, hxdecl, List.append_assoc]
    · exact DeltaBvNotMem.append hxok (hyok.mono x_used_sub)
  | and x y x_ih y_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    rw [encodeTerm]
    mspec x_ih (E := E)
    rename_i out_x
    obtain ⟨x_enc, σx⟩ := out_x
    mrename_i prex
    mintro ∀σ_x
    mpure prex
    obtain ⟨x_bv, x_used_sub, Δx, hxdecl, hxok⟩ := prex
    split
    · rename_i heq
      injection heq with hxe hσe
      subst hσe
      subst hxe
      mspec y_ih (E := E) (used := σ_x.env.usedVars) (decl := σ_x.env.declarations)
      rename_i out_y
      obtain ⟨y_enc, σy⟩ := out_y
      mrename_i prey
      mintro ∀σ_y
      mpure prey
      obtain ⟨y_bv, y_used_sub, Δy, hydecl, hyok⟩ := prey
      split
      · rename_i heq2
        injection heq2 with hye hσe2
        subst hσe2
        subst hye
        mspec Std.Do.Spec.pure
        mpure_intro
        refine ⟨?_, fun v hv => y_used_sub (x_used_sub hv), Δx ++ Δy, ?_, ?_⟩
        · intro v hv
          simp only [SMT.bv, List.mem_append] at hv
          rcases hv with hv | hv
          · exact x_bv v hv
          · exact fun hmem => y_bv v hv (x_used_sub hmem)
        · rw [hydecl, hxdecl, List.append_assoc]
        · exact DeltaBvNotMem.append hxok (hyok.mono x_used_sub)
      · exact wp_bind_throw _ _ _ _
    · exact wp_bind_throw _ _ _ _
  | not x ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    rw [encodeTerm]
    mspec ih (E := E)
    rename_i out_x
    obtain ⟨x_enc, σx⟩ := out_x
    mrename_i prex
    mintro ∀σ_x
    mpure prex
    obtain ⟨x_bv, x_used_sub, Δx, hxdecl, hxok⟩ := prex
    split
    · rename_i heq
      injection heq with hxe hσe
      subst hσe
      subst hxe
      mspec Std.Do.Spec.pure
      mpure_intro
      refine ⟨?_, x_used_sub, Δx, hxdecl, hxok⟩
      intro v hv
      simp only [SMT.bv] at hv
      exact x_bv v hv
    · exact wp_bind_throw _ _ _ _
  | eq x y x_ih y_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    rw [encodeTerm]
    mspec x_ih (E := E)
    rename_i out_x
    obtain ⟨x_enc, σx⟩ := out_x
    mrename_i prex
    mintro ∀σ_x
    mpure prex
    obtain ⟨x_bv, x_used_sub, Δx, hxdecl, hxok⟩ := prex
    mspec y_ih (E := E) (used := σ_x.env.usedVars) (decl := σ_x.env.declarations)
    rename_i out_y
    obtain ⟨y_enc, σy⟩ := out_y
    mrename_i prey
    mintro ∀σ_y
    mpure prey
    obtain ⟨y_bv, y_used_sub, Δy, hydecl, hyok⟩ := prey
    mspec (Std.Do.Triple.and _
      (castEq_bv_notMem x_enc y_enc σx σy (x_used_sub.trans y_used_sub)
        x_bv (fun v hv hmem => y_bv v hv (x_used_sub hmem)))
      (castEq_decls_bv_notMem x_enc y_enc σx σy (decl := σ_y.env.declarations)
        (x_used_sub.trans y_used_sub)
        x_bv (fun v hv hmem => y_bv v hv (x_used_sub hmem))))
    mrename_i prez
    mintro ∀σ_z
    mpure prez
    obtain ⟨⟨z_bv, z_used_sub⟩, Δc, hcdecl, hcok, _⟩ := prez
    mpure_intro
    refine ⟨z_bv, fun v hv => z_used_sub (y_used_sub (x_used_sub hv)),
      Δx ++ Δy ++ Δc, ?_, ?_⟩
    · rw [hcdecl, hydecl, hxdecl]; simp only [List.append_assoc]
    · exact DeltaBvNotMem.append (DeltaBvNotMem.append hxok (hyok.mono x_used_sub)) hcok
  | mem x S x_ih S_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    rw [encodeTerm]
    mspec x_ih (E := E)
    rename_i out_x
    obtain ⟨x_enc, σx⟩ := out_x
    mrename_i prex
    mintro ∀σ_x
    mpure prex
    obtain ⟨x_bv, x_used_sub, Δx, hxdecl, hxok⟩ := prex
    mspec S_ih (E := E) (used := σ_x.env.usedVars) (decl := σ_x.env.declarations)
    rename_i out_S
    obtain ⟨S_enc, σS⟩ := out_S
    mrename_i preS
    mintro ∀σ_S
    mpure preS
    obtain ⟨S_bv, S_used_sub, ΔS, hSdecl, hSok⟩ := preS
    mspec (Std.Do.Triple.and _
      (castMembership_bv_notMem x_enc S_enc σx σS (x_used_sub.trans S_used_sub)
        x_bv (fun v hv hmem => S_bv v hv (x_used_sub hmem)))
      (castMembership_decls_bv_notMem x_enc S_enc σx σS (decl := σ_S.env.declarations)
        (x_used_sub.trans S_used_sub)
        x_bv (fun v hv hmem => S_bv v hv (x_used_sub hmem))))
    mrename_i prez
    mintro ∀σ_z
    mpure prez
    obtain ⟨⟨z_bv, z_used_sub⟩, Δc, hcdecl, hcok, _⟩ := prez
    mpure_intro
    refine ⟨z_bv, fun v hv => z_used_sub (S_used_sub (x_used_sub hv)),
      Δx ++ ΔS ++ Δc, ?_, ?_⟩
    · rw [hcdecl, hSdecl, hxdecl]; simp only [List.append_assoc]
    · exact DeltaBvNotMem.append (DeltaBvNotMem.append hxok (hSok.mono x_used_sub)) hcok
  | pow S ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    rw [encodeTerm]
    mspec ih (E := E)
    rename_i out_S
    obtain ⟨S_enc, σS⟩ := out_S
    mrename_i preS
    mintro ∀σ_S
    mpure preS
    obtain ⟨S_bv, S_used_sub, Δs, hsdecl, hsok⟩ := preS
    split
    · rename_i α heq
      subst heq
      mspec Std.Do.Spec.get_StateT
      mspec (Std.Do.Triple.and _ SMT.freshVar_spec (SMT.freshVar_decls (decl := σ_S.env.declarations)))
      case post.success x =>
        mrename_i prex
        mintro ∀St₁
        mpure prex
        obtain ⟨⟨_, _, _, St₁_used_eq, x_notMem⟩, St₁_decl⟩ := prex
        mspec (Std.Do.Triple.and _ SMT.freshVar_spec (SMT.freshVar_decls (decl := St₁.env.declarations)))
        case post.success ℰ =>
          mrename_i preℰ
          mintro ∀St₂
          mpure preℰ
          obtain ⟨⟨_, _, _, St₂_used_eq, e_notMem⟩, St₂_decl⟩ := preℰ
          simp [modify]
          mspec Std.Do.Spec.modifyGet_StateT
          mpure_intro
          refine ⟨?_, ?_, Δs, ?_, ?_⟩
          · intro v hv
            simp only [SMT.bv, List.append_nil, List.mem_append, List.mem_cons,
              List.not_mem_nil, false_or, or_false] at hv
            rcases hv with rfl | rfl | hvS
            · intro h
              refine e_notMem ?_
              rw [St₁_used_eq]; exact List.mem_cons_of_mem _ (S_used_sub h)
            · exact fun h => x_notMem (S_used_sub h)
            · exact S_bv v hvS
          · intro v hv
            rw [St₂_used_eq, St₁_used_eq]
            exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (S_used_sub hv))
          · rw [St₂_decl, St₁_decl, hsdecl]
          · exact hsok
    · rename_i α γ heq
      subst heq
      mspec Std.Do.Spec.get_StateT
      mspec (Std.Do.Triple.and _ SMT.freshVar_spec (SMT.freshVar_decls (decl := σ_S.env.declarations)))
      case post.success x =>
        mrename_i prex
        mintro ∀St₁
        mpure prex
        obtain ⟨⟨_, _, _, St₁_used_eq, x_notMem⟩, St₁_decl⟩ := prex
        mspec (Std.Do.Triple.and _ SMT.freshVar_spec (SMT.freshVar_decls (decl := St₁.env.declarations)))
        case post.success y =>
          mrename_i prey
          mintro ∀St₂
          mpure prey
          obtain ⟨⟨_, _, _, St₂_used_eq, y_notMem⟩, St₂_decl⟩ := prey
          mspec (Std.Do.Triple.and _ SMT.freshVar_spec (SMT.freshVar_decls (decl := St₂.env.declarations)))
          case post.success f =>
            mrename_i pref
            mintro ∀St₃
            mpure pref
            obtain ⟨⟨_, _, _, St₃_used_eq, f_notMem⟩, St₃_decl⟩ := pref
            simp [modify]
            mspec Std.Do.Spec.modifyGet_StateT
            mpure_intro
            refine ⟨?_, ?_, Δs, ?_, ?_⟩
            · intro v hv
              simp only [SMT.bv, List.append_nil, List.mem_append, List.mem_cons,
                List.not_mem_nil, false_or, or_false] at hv
              rcases hv with rfl | (rfl | rfl) | hvS
              · intro h
                refine f_notMem ?_
                rw [St₂_used_eq, St₁_used_eq]
                exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (S_used_sub h))
              · exact fun h => x_notMem (S_used_sub h)
              · intro h
                refine y_notMem ?_
                rw [St₁_used_eq]
                exact List.mem_cons_of_mem _ (S_used_sub h)
              · exact S_bv v hvS
            · intro v hv
              rw [St₃_used_eq, St₂_used_eq, St₁_used_eq]
              exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ (S_used_sub hv)))
            · rw [St₃_decl, St₂_decl, St₁_decl, hsdecl]
            · exact hsok
    · mvcgen
  | cprod A C A_ih C_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    rw [encodeTerm]
    mspec A_ih (E := E)
    rename_i out_A
    obtain ⟨A_enc, σA⟩ := out_A
    mrename_i preA
    mintro ∀σ_A
    mpure preA
    obtain ⟨A_bv, A_used_sub, Δa, hadecl, haok⟩ := preA
    split
    · rename_i heqA
      injection heqA with hAe hσeA
      subst hσeA
      subst hAe
      mspec C_ih (E := E) (used := σ_A.env.usedVars) (decl := σ_A.env.declarations)
      rename_i out_C
      obtain ⟨C_enc, σC⟩ := out_C
      mrename_i preC
      mintro ∀σ_C
      mpure preC
      obtain ⟨C_bv, C_used_sub, Δc, hcdecl, hcok⟩ := preC
      split
      · rename_i heqC
        injection heqC with hCe hσeC
        subst hσeC
        subst hCe
        mspec (Std.Do.Triple.and _ SMT.freshVar_spec (SMT.freshVar_decls (decl := σ_C.env.declarations)))
        case post.success p =>
          mrename_i prep
          mintro ∀St₁
          mpure prep
          obtain ⟨⟨_, _, _, St₁_used_eq, p_notMem⟩, St₁_decl⟩ := prep
          mspec (Std.Do.Triple.and _ SMT.freshVar_spec (SMT.freshVar_decls (decl := St₁.env.declarations)))
          case post.success a =>
            mrename_i prea
            mintro ∀St₂
            mpure prea
            obtain ⟨⟨_, _, _, St₂_used_eq, a_notMem⟩, St₂_decl⟩ := prea
            mspec (Std.Do.Triple.and _ SMT.freshVar_spec (SMT.freshVar_decls (decl := St₂.env.declarations)))
            case post.success b =>
              mrename_i preb
              mintro ∀St₃
              mpure preb
              obtain ⟨⟨_, _, _, St₃_used_eq, b_notMem⟩, St₃_decl⟩ := preb
              mspec (Std.Do.Triple.and _ SMT.eraseFromContext_spec
                (SMT.eraseFromContext_decls (decl := St₃.env.declarations)))
              mrename_i preEp
              mintro ∀StEp
              mpure preEp
              obtain ⟨⟨_, _, StEp_used_eq⟩, StEp_decl⟩ := preEp
              mspec (Std.Do.Triple.and _ SMT.eraseFromContext_spec
                (SMT.eraseFromContext_decls (decl := StEp.env.declarations)))
              mrename_i preEa
              mintro ∀StEa
              mpure preEa
              obtain ⟨⟨_, _, StEa_used_eq⟩, StEa_decl⟩ := preEa
              mspec (Std.Do.Triple.and _ SMT.eraseFromContext_spec
                (SMT.eraseFromContext_decls (decl := StEa.env.declarations)))
              mrename_i preEb
              mintro ∀StEb
              mpure preEb
              obtain ⟨⟨_, _, StEb_used_eq⟩, StEb_decl⟩ := preEb
              mspec Std.Do.Spec.pure
              mpure_intro
              refine ⟨?_, ?_, Δa ++ Δc, ?_, ?_⟩
              · intro v hv
                simp only [SMT.bv, List.append_nil, List.mem_append,
                  List.mem_cons, List.not_mem_nil, or_false] at hv
                rcases hv with rfl | (rfl | rfl) | hvA | hvC
                · intro h
                  exact p_notMem (C_used_sub (A_used_sub h))
                · intro h
                  refine a_notMem ?_
                  rw [St₁_used_eq]
                  exact List.mem_cons_of_mem _ (C_used_sub (A_used_sub h))
                · intro h
                  refine b_notMem ?_
                  rw [St₂_used_eq, St₁_used_eq]
                  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (C_used_sub (A_used_sub h)))
                · exact A_bv v hvA
                · exact fun h => C_bv v hvC (A_used_sub h)
              · intro v hv
                rw [StEb_used_eq, StEa_used_eq, StEp_used_eq, St₃_used_eq, St₂_used_eq, St₁_used_eq]
                exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                  (List.mem_cons_of_mem _ (C_used_sub (A_used_sub hv))))
              · rw [StEb_decl, StEa_decl, StEp_decl, St₃_decl, St₂_decl, St₁_decl, hcdecl, hadecl,
                  List.append_assoc]
              · exact DeltaBvNotMem.append haok (hcok.mono A_used_sub)
      · exact wp_bind_throw _ _ _ _
    · exact wp_bind_throw _ _ _ _
  | union S T S_ih T_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    rw [encodeTerm]
    mspec S_ih (E := E)
    rename_i out_S
    obtain ⟨S_enc, σS⟩ := out_S
    mrename_i preS
    mintro ∀σ_S
    mpure preS
    obtain ⟨S_bv, S_used_sub, ΔS, hSdecl, hSok⟩ := preS
    mspec T_ih (E := E) (used := σ_S.env.usedVars) (decl := σ_S.env.declarations)
    rename_i out_T
    obtain ⟨T_enc, σT⟩ := out_T
    mrename_i preT
    mintro ∀σ_T
    mpure preT
    obtain ⟨T_bv, T_used_sub, ΔT, hTdecl, hTok⟩ := preT
    mspec (Std.Do.Triple.and _
      (castUnion_bv_notMem S_enc T_enc σS σT (S_used_sub.trans T_used_sub)
        S_bv (fun v hv hmem => T_bv v hv (S_used_sub hmem)))
      (castUnion_decls_bv_notMem S_enc T_enc σS σT (decl := σ_T.env.declarations)
        (S_used_sub.trans T_used_sub)
        S_bv (fun v hv hmem => T_bv v hv (S_used_sub hmem))))
    mrename_i prez
    mintro ∀σ_z
    mpure prez
    obtain ⟨⟨z_bv, z_used_sub⟩, Δc, hcdecl, hcok, _⟩ := prez
    mpure_intro
    refine ⟨z_bv, fun v hv => z_used_sub (T_used_sub (S_used_sub hv)),
      ΔS ++ ΔT ++ Δc, ?_, ?_⟩
    · rw [hcdecl, hTdecl, hSdecl]; simp only [List.append_assoc]
    · exact DeltaBvNotMem.append (DeltaBvNotMem.append hSok (hTok.mono S_used_sub)) hcok
  | inter S T S_ih T_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    rw [encodeTerm]
    mspec S_ih (E := E)
    rename_i out_S
    obtain ⟨S_enc, σS⟩ := out_S
    mrename_i preS
    mintro ∀σ_S
    mpure preS
    obtain ⟨S_bv, S_used_sub, ΔS, hSdecl, hSok⟩ := preS
    mspec T_ih (E := E) (used := σ_S.env.usedVars) (decl := σ_S.env.declarations)
    rename_i out_T
    obtain ⟨T_enc, σT⟩ := out_T
    mrename_i preT
    mintro ∀σ_T
    mpure preT
    obtain ⟨T_bv, T_used_sub, ΔT, hTdecl, hTok⟩ := preT
    mspec (Std.Do.Triple.and _
      (castInter_bv_notMem S_enc T_enc σS σT (S_used_sub.trans T_used_sub)
        S_bv (fun v hv hmem => T_bv v hv (S_used_sub hmem)))
      (castInter_decls_bv_notMem S_enc T_enc σS σT (decl := σ_T.env.declarations)
        (S_used_sub.trans T_used_sub)
        S_bv (fun v hv hmem => T_bv v hv (S_used_sub hmem))))
    mrename_i prez
    mintro ∀σ_z
    mpure prez
    obtain ⟨⟨z_bv, z_used_sub⟩, Δc, hcdecl, hcok, _⟩ := prez
    mpure_intro
    refine ⟨z_bv, fun v hv => z_used_sub (T_used_sub (S_used_sub hv)),
      ΔS ++ ΔT ++ Δc, ?_, ?_⟩
    · rw [hcdecl, hTdecl, hSdecl]; simp only [List.append_assoc]
    · exact DeltaBvNotMem.append (DeltaBvNotMem.append hSok (hTok.mono S_used_sub)) hcok
  | card S ih =>
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    simp only [encodeTerm] <;> mvcgen
  | app f x f_ih x_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    rw [encodeTerm]
    mspec f_ih (E := E)
    rename_i out_f
    obtain ⟨f_enc, σf⟩ := out_f
    mrename_i pref
    mintro ∀σ_f
    mpure pref
    obtain ⟨f_bv, f_used_sub, Δf, hfdecl, hfok⟩ := pref
    mspec x_ih (E := E) (used := σ_f.env.usedVars) (decl := σ_f.env.declarations)
    rename_i out_x
    obtain ⟨x_enc, σx⟩ := out_x
    mrename_i prex
    mintro ∀σ_x
    mpure prex
    obtain ⟨x_bv, x_used_sub, Δx, hxdecl, hxok⟩ := prex
    mspec (Std.Do.Triple.and _
      (castApp_bv_notMem f_enc x_enc σf σx (f_used_sub.trans x_used_sub)
        f_bv (fun v hv hmem => x_bv v hv (f_used_sub hmem)))
      (castApp_decls_bv_notMem f_enc x_enc σf σx (decl := σ_x.env.declarations)
        (f_used_sub.trans x_used_sub)
        f_bv (fun v hv hmem => x_bv v hv (f_used_sub hmem))))
    mrename_i prez
    mintro ∀σ_z
    mpure prez
    obtain ⟨⟨z_bv, z_used_sub⟩, Δc, hcdecl, hcok, _⟩ := prez
    mpure_intro
    refine ⟨z_bv, fun v hv => z_used_sub (x_used_sub (f_used_sub hv)),
      Δf ++ Δx ++ Δc, ?_, ?_⟩
    · rw [hcdecl, hxdecl, hfdecl]; simp only [List.append_assoc]
    · exact DeltaBvNotMem.append (DeltaBvNotMem.append hfok (hxok.mono f_used_sub)) hcok
  | collect vs D P D_ih P_ih =>
    mstart
    mintro pre ∀St₀
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    rw [encodeTerm]
    mspec D_ih (E := E)
    rename_i out_D
    obtain ⟨D_enc, τD⟩ := out_D
    mrename_i preD
    mintro ∀St₁
    mpure preD
    obtain ⟨D_bv, D_used_sub, ΔD, hDdecl, hDok⟩ := preD
    split
    · -- function-`D` arm
      rename_i α' β' heqD
      split
      · rename_i harity
        set αs' := α'.fromProdl (vs.length - 2) with αs'_def
        mspec Std.Do.Spec.pure
        mspec (Std.Do.Triple.and _
          (encodeTerm_state.modifyTypes_forIn_spec (vs.zip (αs'.concat β')))
          (encodeTerm_state.modifyTypes_forIn_decls (vs.zip (αs'.concat β')) (decl := St₁.env.declarations)))
        mrename_i pre2
        mintro ∀St₂
        mpure pre2
        obtain ⟨⟨_, _, St₂_used⟩, St₂_decl⟩ := pre2
        mspec P_ih (E := E) (used := St₂.env.usedVars) (decl := St₂.env.declarations)
        rename_i out_P
        mrename_i preP
        mintro ∀St₃
        mpure preP
        obtain ⟨P_bv, P_used_sub, ΔP, hPdecl, hPok⟩ := preP
        split
        · rename_i heqP
          mspec (Std.Do.Triple.and _
            (SMT.freshVarList_spec αs')
            (SMT.freshVarList_decls αs' (decl := St₃.env.declarations)))
          rename_i xs
          mrename_i pre4
          mintro ∀St₄
          mpure pre4
          obtain ⟨⟨_, _, xs_notMem, _, _, St₄_used, _⟩, St₄_decl⟩ := pre4
          have St₁_to_St₃ : ∀ {v}, v ∈ St₁.env.usedVars → v ∈ St₃.env.usedVars :=
            fun {v} h => P_used_sub (by rw [St₂_used]; exact h)
          have used_to_St₂ : St₀.env.usedVars ⊆ St₂.env.usedVars :=
            fun w h => by rw [St₂_used]; exact D_used_sub h
          have used_to_St₃ : St₀.env.usedVars ⊆ St₃.env.usedVars :=
            fun w h => St₁_to_St₃ (D_used_sub h)
          have used_to_St₄ : St₀.env.usedVars ⊆ St₄.env.usedVars :=
            fun w h => by rw [St₄_used]; exact List.mem_append_right _ (used_to_St₃ h)
          have hbvD_lifted : ∀ v ∈ SMT.bv D_enc, v ∉ St₀.env.usedVars := fun v hv => D_bv v hv
          have hbvXs_lifted : ∀ v ∈ SMT.bv ((xs.map SMT.Term.var).toPairl), v ∉ St₀.env.usedVars :=
            fun v hv => by
              rw [bv_toPairl_nil (fun t ht => by
                rw [List.mem_map] at ht; obtain ⟨z, _, rfl⟩ := ht; simp [SMT.bv])] at hv
              exact absurd hv List.not_mem_nil
          mspec (Std.Do.Triple.and _
            (castApp_bv_notMem D_enc ((xs.map SMT.Term.var).toPairl) (α'.fun β'.option)
              αs'.toProdl used_to_St₄ hbvD_lifted hbvXs_lifted)
            (castApp_decls_bv_notMem D_enc ((xs.map SMT.Term.var).toPairl) (α'.fun β'.option)
              αs'.toProdl (decl := St₄.env.declarations) used_to_St₄ hbvD_lifted hbvXs_lifted))
          mrename_i pre5
          mintro ∀St₅
          mpure pre5
          obtain ⟨⟨Dxs_bv, Dxs_used_sub⟩, Δca, hcadecl, hcaok, _⟩ := pre5
          mspec Std.Do.Spec.pure
          mpure_intro
          have lift3 : ∀ {w}, w ∈ St₃.env.usedVars → w ∈ St₅.env.usedVars := fun {w} h =>
            Dxs_used_sub (by rw [St₄_used]; exact List.mem_append_right _ h)
          have liftXs : ∀ {w}, w ∈ xs → w ∈ St₅.env.usedVars := fun {w} h =>
            Dxs_used_sub (by rw [St₄_used]; exact List.mem_append_left _ (List.mem_reverse.mpr h))
          refine ⟨?_, fun v hv => lift3 (St₁_to_St₃ (D_used_sub hv)), ΔD ++ ΔP ++ Δca, ?_, ?_⟩
          · intro v hv
            simp only [noneCast, SMT.bv, List.nil_append, List.append_nil, List.mem_append,
              List.not_mem_nil, false_or, or_false] at hv
            rcases hv with hvxs | hvP | hvDxs
            · intro h; exact xs_notMem v hvxs (used_to_St₃ h)
            · refine bv_substList_notMem_of (a := St₀.env.usedVars) ?_ ?_ v hvP
              · exact fun w hw h => P_bv w hw (used_to_St₂ h)
              · intro t ht w hw
                simp only [List.concat_eq_append, List.mem_append, List.mem_singleton] at ht
                rcases ht with hxs | rfl
                · rw [List.mem_map] at hxs
                  obtain ⟨z, _, rfl⟩ := hxs
                  simp only [SMT.bv, List.not_mem_nil] at hw
                · exact Dxs_bv w hw
            · exact Dxs_bv v hvDxs
          · rw [hcadecl, St₄_decl, hPdecl, St₂_decl, hDdecl]; simp only [List.append_assoc]
          · exact DeltaBvNotMem.append (DeltaBvNotMem.append hDok (hPok.mono used_to_St₂)) hcaok
        · first
          | exact wp_bind_throw _ _ _ _
          | (mvcgen)
      · first
        | exact wp_bind_throw _ _ _ _
        | (mvcgen)
    · -- set-`D` arm (lambda-like)
      rename_i τ heqD
      mspec (Std.Do.Triple.and _
        (SMT.addToContext_forIn_spec (vs.zip (τ.fromProdl (vs.length - 1))))
        (SMT.addToContext_forIn_decls (vs.zip (τ.fromProdl (vs.length - 1))) (decl := St₁.env.declarations)))
      mrename_i pre2
      mintro ∀St₂
      mpure pre2
      obtain ⟨⟨_, _, St₂_used⟩, St₂_decl⟩ := pre2
      mspec P_ih (E := E) (used := St₂.env.usedVars) (decl := St₂.env.declarations)
      rename_i out_P
      mrename_i preP
      mintro ∀St₃
      mpure preP
      obtain ⟨P_bv, P_used_sub, ΔP, hPdecl, hPok⟩ := preP
      split
      · rename_i heqP
        mspec (Std.Do.Triple.and _ SMT.freshVar_spec (SMT.freshVar_decls (decl := St₃.env.declarations)))
        case post.success z =>
          mrename_i prez
          mintro ∀St₄
          mpure prez
          obtain ⟨⟨_, _, _, St₄_used_eq, z_notMem⟩, St₄_decl⟩ := prez
          mspec (Std.Do.Triple.and _ SMT.eraseFromContext_spec (SMT.eraseFromContext_decls (decl := St₄.env.declarations)))
          mrename_i pree
          mintro ∀St₅
          mpure pree
          obtain ⟨⟨_, _, St₅_used⟩, St₅_decl⟩ := pree
          mspec Std.Do.Spec.pure
          mpure_intro
          have St₁_sub_St₂ : ∀ {w}, w ∈ St₁.env.usedVars → w ∈ St₂.env.usedVars :=
            fun {w} h => by rw [St₂_used]; exact encodeTerm_state.mem_foldl_cons_of_mem _ _ h
          have lift : ∀ {w}, w ∈ St₃.env.usedVars → w ∈ St₅.env.usedVars := fun {w} h => by
            rw [St₅_used, St₄_used_eq]; exact List.mem_cons_of_mem _ h
          have used_sub_St₂ : St₀.env.usedVars ⊆ St₂.env.usedVars :=
            fun w h => St₁_sub_St₂ (D_used_sub h)
          have used_sub_St₃ : St₀.env.usedVars ⊆ St₃.env.usedVars :=
            fun w h => P_used_sub (used_sub_St₂ h)
          refine ⟨?_, fun v hv => lift (P_used_sub (St₁_sub_St₂ (D_used_sub hv))), ΔD ++ ΔP, ?_, ?_⟩
          · intro v hv
            simp only [SMT.bv, List.nil_append, List.append_nil, List.mem_append, List.mem_cons,
              List.not_mem_nil, false_or, or_false] at hv
            rcases hv with rfl | hvD | hvP
            · exact fun h => z_notMem (used_sub_St₃ h)
            · exact D_bv v hvD
            · rw [SMT_bv_substList_eq (fun t ht => bv_toDestPair_nil (by simp [SMT.bv]) ht)] at hvP
              exact fun h => P_bv v hvP (used_sub_St₂ h)
          · rw [St₅_decl, St₄_decl, hPdecl, St₂_decl, hDdecl, List.append_assoc]
          · exact DeltaBvNotMem.append hDok (hPok.mono used_sub_St₂)
      · first
        | exact wp_bind_throw _ _ _ _
        | (mvcgen)
    · first
        | exact wp_bind_throw _ _ _ _
        | (mvcgen)
  | lambda vs D P D_ih P_ih =>
    mstart
    mintro pre ∀St₀
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    rw [encodeTerm]
    mspec D_ih (E := E)
    rename_i out_D
    obtain ⟨D_enc, τD⟩ := out_D
    mrename_i preD
    mintro ∀St₁
    mpure preD
    obtain ⟨D_bv, D_used_sub, ΔD, hDdecl, hDok⟩ := preD
    split
    · rename_i τ' heqτD
      mspec (Std.Do.Triple.and _
        (SMT.addToContext_forIn_spec (vs.zip (τ'.fromProdl (vs.length - 1))))
        (SMT.addToContext_forIn_decls (vs.zip (τ'.fromProdl (vs.length - 1))) (decl := St₁.env.declarations)))
      mrename_i pre2
      mintro ∀St₂
      mpure pre2
      obtain ⟨⟨_, _, St₂_used⟩, St₂_decl⟩ := pre2
      mspec P_ih (E := E) (used := St₂.env.usedVars) (decl := St₂.env.declarations)
      rename_i out_P
      obtain ⟨P_enc, σP⟩ := out_P
      mrename_i preP
      mintro ∀St₃
      mpure preP
      obtain ⟨P_bv, P_used_sub, ΔP, hPdecl, hPok⟩ := preP
      mspec (Std.Do.Triple.and _ SMT.freshVar_spec (SMT.freshVar_decls (decl := St₃.env.declarations)))
      case post.success xy =>
        mrename_i prexy
        mintro ∀St₄
        mpure prexy
        obtain ⟨⟨_, _, _, St₄_used_eq, xy_notMem⟩, St₄_decl⟩ := prexy
        mspec (Std.Do.Triple.and _ SMT.eraseFromContext_spec (SMT.eraseFromContext_decls (decl := St₄.env.declarations)))
        mrename_i pree
        mintro ∀St₅
        mpure pree
        obtain ⟨⟨_, _, St₅_used⟩, St₅_decl⟩ := pree
        mspec Std.Do.Spec.pure
        mpure_intro
        have St₁_sub_St₂ : ∀ {v}, v ∈ St₁.env.usedVars → v ∈ St₂.env.usedVars :=
          fun {v} h => by rw [St₂_used]; exact encodeTerm_state.mem_foldl_cons_of_mem _ _ h
        have lift : ∀ {v}, v ∈ St₃.env.usedVars → v ∈ St₅.env.usedVars := fun {v} h => by
          rw [St₅_used, St₄_used_eq]; exact List.mem_cons_of_mem _ h
        have used_sub_St₂ : St₀.env.usedVars ⊆ St₂.env.usedVars :=
          fun w h => St₁_sub_St₂ (D_used_sub h)
        have used_sub_St₃ : St₀.env.usedVars ⊆ St₃.env.usedVars :=
          fun w h => P_used_sub (used_sub_St₂ h)
        refine ⟨?_, fun v hv => lift (P_used_sub (St₁_sub_St₂ (D_used_sub hv))), ΔD ++ ΔP, ?_, ?_⟩
        · intro v hv
          simp only [SMT.bv, List.nil_append, List.append_nil, List.mem_append, List.mem_cons,
            List.not_mem_nil, false_or, or_false] at hv
          rcases hv with rfl | hvD | hvPx
          · exact fun h => xy_notMem (used_sub_St₃ h)
          · exact D_bv v hvD
          · rw [SMT_bv_substList_eq (fun t ht => bv_toDestPair_nil (by simp [SMT.bv]) ht)] at hvPx
            exact fun h => P_bv v hvPx (used_sub_St₂ h)
        · rw [St₅_decl, St₄_decl, hPdecl, St₂_decl, hDdecl, List.append_assoc]
        · exact DeltaBvNotMem.append hDok (hPok.mono used_sub_St₂)
    · first
      | exact wp_bind_throw _ _ _ _
      | (mvcgen)
  | pfun A B A_ih B_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    rw [encodeTerm]
    mspec A_ih (E := E)
    rename_i out_A
    obtain ⟨A_enc, σA⟩ := out_A
    mrename_i preA
    mintro ∀σ_A
    mpure preA
    obtain ⟨A_bv, A_used_sub, Δa, hadecl, haok⟩ := preA
    split
    · rename_i heqA
      injection heqA with hAe hσeA
      subst hσeA
      subst hAe
      mspec B_ih (E := E) (used := σ_A.env.usedVars) (decl := σ_A.env.declarations)
      rename_i out_B
      obtain ⟨B_enc, σB⟩ := out_B
      mrename_i preB
      mintro ∀σ_B
      mpure preB
      obtain ⟨B_bv, B_used_sub, Δb, hbdecl, hbok⟩ := preB
      split
      · rename_i heqB
        injection heqB with hBe hσeB
        subst hσeB
        subst hBe
        mspec (Std.Do.Triple.and _ SMT.freshVar_spec (SMT.freshVar_decls (decl := σ_B.env.declarations)))
        case post.success R =>
          mrename_i preR
          mintro ∀St₁
          mpure preR
          obtain ⟨⟨_, _, _, St₁_used_eq, R_notMem⟩, St₁_decl⟩ := preR
          mspec (Std.Do.Triple.and _ SMT.freshVar_spec (SMT.freshVar_decls (decl := St₁.env.declarations)))
          case post.success xx =>
            mrename_i prex
            mintro ∀St₂
            mpure prex
            obtain ⟨⟨_, _, _, St₂_used_eq, x_notMem⟩, St₂_decl⟩ := prex
            mspec (Std.Do.Triple.and _ SMT.freshVar_spec (SMT.freshVar_decls (decl := St₂.env.declarations)))
            case post.success yy =>
              mrename_i prey
              mintro ∀St₃
              mpure prey
              obtain ⟨⟨_, _, _, St₃_used_eq, y_notMem⟩, St₃_decl⟩ := prey
              mspec (Std.Do.Triple.and _ SMT.freshVar_spec (SMT.freshVar_decls (decl := St₃.env.declarations)))
              case post.success yy' =>
                mrename_i prey'
                mintro ∀St₄
                mpure prey'
                obtain ⟨⟨_, _, _, St₄_used_eq, y'_notMem⟩, St₄_decl⟩ := prey'
                -- erase the four leaked binders `R`, `x`, `y`, `y'`; each leaves
                -- `usedVars` and `declarations` unchanged.
                mspec (Std.Do.Triple.and _ SMT.eraseFromContext_spec
                  (SMT.eraseFromContext_decls (decl := St₄.env.declarations)))
                mrename_i preER
                mintro ∀StER
                mpure preER
                obtain ⟨⟨_, _, StER_used_eq⟩, StER_decl⟩ := preER
                mspec (Std.Do.Triple.and _ SMT.eraseFromContext_spec
                  (SMT.eraseFromContext_decls (decl := StER.env.declarations)))
                mrename_i preEx
                mintro ∀StEx
                mpure preEx
                obtain ⟨⟨_, _, StEx_used_eq⟩, StEx_decl⟩ := preEx
                mspec (Std.Do.Triple.and _ SMT.eraseFromContext_spec
                  (SMT.eraseFromContext_decls (decl := StEx.env.declarations)))
                mrename_i preEy
                mintro ∀StEy
                mpure preEy
                obtain ⟨⟨_, _, StEy_used_eq⟩, StEy_decl⟩ := preEy
                mspec (Std.Do.Triple.and _ SMT.eraseFromContext_spec
                  (SMT.eraseFromContext_decls (decl := StEy.env.declarations)))
                mrename_i preEy'
                mintro ∀StEy'
                mpure preEy'
                obtain ⟨⟨_, _, StEy'_used_eq⟩, StEy'_decl⟩ := preEy'
                mspec Std.Do.Spec.pure
                mpure_intro
                have lift1 : σ.env.usedVars ⊆ St₁.env.usedVars := fun w h => by
                  rw [St₁_used_eq]; exact List.mem_cons_of_mem _ (B_used_sub (A_used_sub h))
                have lift2 : St₁.env.usedVars ⊆ St₂.env.usedVars := fun w h => by
                  rw [St₂_used_eq]; exact List.mem_cons_of_mem _ h
                have lift3 : St₂.env.usedVars ⊆ St₃.env.usedVars := fun w h => by
                  rw [St₃_used_eq]; exact List.mem_cons_of_mem _ h
                have lift4 : St₃.env.usedVars ⊆ St₄.env.usedVars := fun w h => by
                  rw [St₄_used_eq]; exact List.mem_cons_of_mem _ h
                refine ⟨?_, ?_, Δa ++ Δb, ?_, ?_⟩
                · intro v hv
                  simp only [SMT.bv, List.nil_append, List.append_nil, List.mem_append, List.mem_cons,
                    List.not_mem_nil, false_or, or_false] at hv
                  rcases hv with rfl | (((rfl | rfl) | (hA | hB)) | (rfl | (rfl | rfl)))
                  · intro h; exact R_notMem (B_used_sub (A_used_sub h))
                  · intro h; exact x_notMem (lift1 h)
                  · intro h; exact y_notMem (lift2 (lift1 h))
                  · exact A_bv v hA
                  · exact fun h => B_bv v hB (A_used_sub h)
                  · intro h; exact x_notMem (lift1 h)
                  · intro h; exact y_notMem (lift2 (lift1 h))
                  · intro h; exact y'_notMem (lift3 (lift2 (lift1 h)))
                · intro v hv
                  rw [StEy'_used_eq, StEy_used_eq, StEx_used_eq, StER_used_eq,
                    St₄_used_eq, St₃_used_eq, St₂_used_eq, St₁_used_eq]
                  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (B_used_sub (A_used_sub hv)))))
                · rw [StEy'_decl, StEy_decl, StEx_decl, StER_decl,
                    St₄_decl, St₃_decl, St₂_decl, St₁_decl, hbdecl, hadecl, List.append_assoc]
                · exact DeltaBvNotMem.append haok (hbok.mono A_used_sub)
      · mvcgen
    · mvcgen
  | min S ih =>
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    simp only [encodeTerm] <;> mvcgen
  | max S ih =>
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    simp only [encodeTerm] <;> mvcgen
  | all vs D P D_ih P_ih =>
    mstart
    mintro pre ∀St₀
    mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    rw [encodeTerm]
    mspec D_ih (E := E)
    rename_i out_D
    obtain ⟨D_enc, τD⟩ := out_D
    mrename_i preD
    mintro ∀St₁
    mpure preD
    obtain ⟨D_bv, D_used_sub, ΔD, hDdecl, hDok⟩ := preD
    split
    · -- set-arm: τD = .fun τ .bool
      rename_i τ heqD
      split
      · rename_i hlen
        mspec (Std.Do.Triple.and _
          (encodeTerm_state.mapFinIdxM_all_state vs E.flags (τ.fromProdl (vs.length - 1)) hlen)
          (encodeTerm_state.mapFinIdxM_all_decls vs E.flags (τ.fromProdl (vs.length - 1)) hlen
            (decl := St₁.env.declarations)))
        rename_i τs
        mrename_i pre2
        mintro ∀St₂
        mpure pre2
        obtain ⟨⟨_, _, St₂_used, _⟩, St₂_decl⟩ := pre2
        mspec (Std.Do.Triple.and _
          (SMT.addToContext_forIn_spec (vs.zip τs))
          (SMT.addToContext_forIn_decls (vs.zip τs) (decl := St₂.env.declarations)))
        mrename_i pre3
        mintro ∀St₃
        mpure pre3
        obtain ⟨⟨_, _, St₃_used⟩, St₃_decl⟩ := pre3
        mspec Std.Do.Spec.get_StateT
        mspec Std.Do.Spec.get_StateT
        mspec Std.Do.Spec.get_StateT
        mspec P_ih (E := E) (used := St₃.env.usedVars) (decl := St₃.env.declarations)
        rename_i out_P
        mrename_i preP
        mintro ∀St₄
        mpure preP
        obtain ⟨P_bv, P_used_sub, ΔP, hPdecl, hPok⟩ := preP
        split
        · rename_i heqP
          mspec (Std.Do.Triple.and _
            (SMT.freshVarList_spec τs)
            (SMT.freshVarList_decls τs (decl := St₄.env.declarations)))
          rename_i zs
          mrename_i pre5
          mintro ∀St₅
          mpure pre5
          obtain ⟨⟨_, _, zs_notMem, _, _, St₅_used, _⟩, St₅_decl⟩ := pre5
          have lift12 : ∀ {w}, w ∈ St₁.env.usedVars → w ∈ St₂.env.usedVars :=
            fun {w} h => by rw [St₂_used]; exact h
          have lift23 : ∀ {w}, w ∈ St₂.env.usedVars → w ∈ St₃.env.usedVars :=
            fun {w} h => by rw [St₃_used]; exact encodeTerm_state.mem_foldl_cons_of_mem _ _ h
          have lift45 : ∀ {w}, w ∈ St₄.env.usedVars → w ∈ St₅.env.usedVars :=
            fun {w} h => by rw [St₅_used]; exact List.mem_append_right _ h
          have used_to_St₃ : St₀.env.usedVars ⊆ St₃.env.usedVars :=
            fun w h => lift23 (lift12 (D_used_sub h))
          have used_to_St₄ : St₀.env.usedVars ⊆ St₄.env.usedVars :=
            fun w h => P_used_sub (used_to_St₃ h)
          have hbvD4 : ∀ v ∈ SMT.bv D_enc, v ∉ St₀.env.usedVars := fun v hv => D_bv v hv
          have hbvX4 : ∀ v ∈ SMT.bv ((zs.map SMT.Term.var).toPairl), v ∉ St₀.env.usedVars :=
            fun v hv => by
              rw [bv_toPairl_nil (fun t ht => by
                rw [List.mem_map] at ht; obtain ⟨z, _, rfl⟩ := ht; simp [SMT.bv])] at hv
              exact absurd hv List.not_mem_nil
          have used_to_St₅ : St₀.env.usedVars ⊆ St₅.env.usedVars :=
            fun w h => lift45 (used_to_St₄ h)
          mspec (Std.Do.Triple.and _
            (castMembership_bv_notMem ((zs.map SMT.Term.var).toPairl) D_enc τs.toProdl (.fun τ .bool)
              used_to_St₅ hbvX4 hbvD4)
            (castMembership_decls_bv_notMem ((zs.map SMT.Term.var).toPairl) D_enc τs.toProdl (.fun τ .bool)
              (decl := St₅.env.declarations) used_to_St₅ hbvX4 hbvD4))
          rename_i out_cm
          mrename_i precm
          mintro ∀St₆
          mpure precm
          obtain ⟨⟨zmem_bv, zmem_used_sub⟩, Δcm, hcmdecl, hcmok, _⟩ := precm
          split
          · rename_i heqcm
            mspec Std.Do.Spec.get_StateT
            simp only [modify]
            mspec Std.Do.Spec.modifyGet_StateT
            mspec (Std.Do.Triple.and _
              (SMT.eraseFromContext_forIn_spec zs)
              (SMT.eraseFromContext_forIn_decls zs))
            mrename_i pre8
            mintro ∀St₈
            mpure pre8
            obtain ⟨⟨_, _, St₈_used⟩, St₈_decl⟩ := pre8
            mspec Std.Do.Spec.pure
            mpure_intro
            have hSt6_decl : St₆.env.declarations = St₃.env.declarations ++ (ΔP ++ Δcm) := by
              rw [hcmdecl, St₅_decl, hPdecl, List.append_assoc]
            have hnew : List.drop St₃.env.declarations.length St₆.env.declarations = ΔP ++ Δcm := by
              rw [hSt6_decl, List.drop_left]
            have hSt8_used : St₈.env.usedVars = St₆.env.usedVars := St₈_used
            have hSt8_decl : St₈.env.declarations = St₃.env.declarations := St₈_decl
            have hSt3_decl : St₃.env.declarations = St₀.env.declarations ++ ΔD := by
              rw [St₃_decl, St₂_decl, hDdecl]
            have hPokc : DeltaBvNotMem ΔP St₀.env.usedVars := hPok.mono used_to_St₃
            have hND_ok : DeltaBvNotMem (ΔP ++ Δcm) St₀.env.usedVars :=
              DeltaBvNotMem.append hPokc hcmok
            refine ⟨?bvgoal, ?usedgoal, ΔD, ?declgoal, ?deltagoal⟩
            case usedgoal =>
              rw [hSt8_used]
              exact fun v hv => zmem_used_sub (lift45 (used_to_St₄ hv))
            case declgoal =>
              rw [hSt8_decl, hSt3_decl]
            case deltagoal =>
              exact hDok
            case bvgoal =>
              rw [hnew]
              intro v hv
              rw [SMT.bv, List.mem_append] at hv
              rcases hv with hvzs | hv
              · intro h; exact zs_notMem v hvzs (used_to_St₄ h)
              · rw [bv_foldr_forall, List.mem_append] at hv
                rcases hv with hvex | hv
                · rw [List.mem_map] at hvex
                  obtain ⟨⟨v', τ'⟩, hmem, rfl⟩ := hvex
                  rw [List.mem_filterMap] at hmem
                  obtain ⟨i, hi_mem, hi_eq⟩ := hmem
                  cases i with
                  | declare_const w ξ =>
                    simp only [Option.some.injEq, Prod.mk.injEq] at hi_eq
                    obtain ⟨rfl, _⟩ := hi_eq
                    exact hND_ok.1 w (by rw [declVars, List.mem_filterMap]; exact ⟨_, hi_mem, rfl⟩)
                  | _ => exact absurd hi_eq (by simp)
                · rw [bv_foldr_imp, List.mem_append] at hv
                  rcases hv with hvspec | hvbase
                  · rw [List.mem_flatMap] at hvspec
                    obtain ⟨b, hb_mem, hvb⟩ := hvspec
                    rw [List.mem_map] at hb_mem
                    obtain ⟨b0, hb0_mem, rfl⟩ := hb_mem
                    rw [SMT_bv_substList_eq_of_var_terms] at hvb
                    have hb0_spec : b0 ∈ specBodies (ΔP ++ Δcm) := hb0_mem
                    exact hND_ok.2 b0 hb0_spec v hvb
                  · rw [SMT.bv, List.mem_append] at hvbase
                    rcases hvbase with hvzmem | hvP
                    · exact zmem_bv v hvzmem
                    · rw [SMT_bv_substList_eq_of_var_terms] at hvP
                      exact fun h => P_bv v hvP (used_to_St₃ h)
          · first
            | exact wp_bind_throw _ _ _ _
            | (mvcgen)
        · first
          | exact wp_bind_throw _ _ _ _
          | (mvcgen)
      · first
        | exact wp_bind_throw _ _ _ _
        | (mvcgen)
    · -- function-arm: τD = .fun α (.option β)
      rename_i α β heqD
      split
      · rename_i harity
        set τs := (α.pair β).fromProdl (vs.length - 1) with τs_def
        mspec Std.Do.Spec.pure
        mspec (Std.Do.Triple.and _
          (SMT.addToContext_forIn_spec (vs.zip τs))
          (SMT.addToContext_forIn_decls (vs.zip τs) (decl := St₁.env.declarations)))
        mrename_i pre2
        mintro ∀St₂
        mpure pre2
        obtain ⟨⟨_, _, St₂_used⟩, St₂_decl⟩ := pre2
        mspec (Std.Do.Triple.and _
          (SMT.freshVarList_spec τs)
          (SMT.freshVarList_decls τs (decl := St₂.env.declarations)))
        rename_i xs
        mrename_i pre3
        mintro ∀St₃
        mpure pre3
        obtain ⟨⟨_, _, xs_notMem, _, _, St₃_used, _⟩, St₃_decl⟩ := pre3
        mspec Std.Do.Spec.get_StateT
        mspec Std.Do.Spec.get_StateT
        mspec Std.Do.Spec.get_StateT
        mspec P_ih (E := E) (used := St₃.env.usedVars) (decl := St₃.env.declarations)
        rename_i out_P
        mrename_i preP
        mintro ∀St₄
        mpure preP
        obtain ⟨P_bv, P_used_sub, ΔP, hPdecl, hPok⟩ := preP
        split
        · rename_i heqP
          have lift12 : ∀ {w}, w ∈ St₁.env.usedVars → w ∈ St₂.env.usedVars :=
            fun {w} h => by rw [St₂_used]; exact encodeTerm_state.mem_foldl_cons_of_mem _ _ h
          have lift23 : ∀ {w}, w ∈ St₂.env.usedVars → w ∈ St₃.env.usedVars :=
            fun {w} h => by rw [St₃_used]; exact List.mem_append_right _ h
          have used_to_St₂ : St₀.env.usedVars ⊆ St₂.env.usedVars :=
            fun w h => lift12 (D_used_sub h)
          have used_to_St₃ : St₀.env.usedVars ⊆ St₃.env.usedVars :=
            fun w h => lift23 (used_to_St₂ h)
          have used_to_St₄ : St₀.env.usedVars ⊆ St₄.env.usedVars :=
            fun w h => P_used_sub (used_to_St₃ h)
          have hbvD4 : ∀ v ∈ SMT.bv D_enc, v ∉ St₀.env.usedVars := fun v hv => D_bv v hv
          have hbvX4 : ∀ v ∈ SMT.bv ((xs.map SMT.Term.var).toPairl), v ∉ St₀.env.usedVars :=
            fun v hv => by
              rw [bv_toPairl_nil (fun t ht => by
                rw [List.mem_map] at ht; obtain ⟨z, _, rfl⟩ := ht; simp [SMT.bv])] at hv
              exact absurd hv List.not_mem_nil
          mspec (Std.Do.Triple.and _
            (castMembership_bv_notMem ((xs.map SMT.Term.var).toPairl) D_enc τs.toProdl (α.fun β.option)
              used_to_St₄ hbvX4 hbvD4)
            (castMembership_decls_bv_notMem ((xs.map SMT.Term.var).toPairl) D_enc τs.toProdl (α.fun β.option)
              (decl := St₄.env.declarations) used_to_St₄ hbvX4 hbvD4))
          rename_i out_cm
          mrename_i precm
          mintro ∀St₅
          mpure precm
          obtain ⟨⟨zmem_bv, zmem_used_sub⟩, Δcm, hcmdecl, hcmok, _⟩ := precm
          mspec Std.Do.Spec.get_StateT
          simp only [modify]
          mspec Std.Do.Spec.modifyGet_StateT
          mspec (Std.Do.Triple.and _
            (SMT.eraseFromContext_forIn_spec xs)
            (SMT.eraseFromContext_forIn_decls xs))
          mrename_i pre6
          mintro ∀St₆
          mpure pre6
          obtain ⟨⟨_, _, St₆_used⟩, St₆_decl⟩ := pre6
          mspec Std.Do.Spec.pure
          mpure_intro
          have hSt5_decl : St₅.env.declarations = St₃.env.declarations ++ (ΔP ++ Δcm) := by
            rw [hcmdecl, hPdecl, List.append_assoc]
          have hnew : List.drop St₃.env.declarations.length St₅.env.declarations = ΔP ++ Δcm := by
            rw [hSt5_decl, List.drop_left]
          have hSt6_used : St₆.env.usedVars = St₅.env.usedVars := St₆_used
          have hSt6_decl : St₆.env.declarations = St₃.env.declarations := St₆_decl
          have hSt3_decl : St₃.env.declarations = St₀.env.declarations ++ ΔD := by
            rw [St₃_decl, St₂_decl, hDdecl]
          have hPokc : DeltaBvNotMem ΔP St₀.env.usedVars := hPok.mono used_to_St₃
          have hND_ok : DeltaBvNotMem (ΔP ++ Δcm) St₀.env.usedVars :=
            DeltaBvNotMem.append hPokc hcmok
          refine ⟨?bvgoal, ?usedgoal, ΔD, ?declgoal, ?deltagoal⟩
          case usedgoal =>
            rw [hSt6_used]
            exact fun v hv => zmem_used_sub (used_to_St₄ hv)
          case declgoal =>
            rw [hSt6_decl, hSt3_decl]
          case deltagoal =>
            exact hDok
          case bvgoal =>
            rw [hnew]
            intro v hv
            rw [SMT.bv, List.mem_append] at hv
            rcases hv with hvxs | hv
            · intro h; exact xs_notMem v hvxs (used_to_St₂ h)
            · rw [bv_foldr_forall, List.mem_append] at hv
              rcases hv with hvex | hv
              · rw [List.mem_map] at hvex
                obtain ⟨⟨v', τ'⟩, hmem, rfl⟩ := hvex
                rw [List.mem_filterMap] at hmem
                obtain ⟨i, hi_mem, hi_eq⟩ := hmem
                cases i with
                | declare_const w ξ =>
                  simp only [Option.some.injEq, Prod.mk.injEq] at hi_eq
                  obtain ⟨rfl, _⟩ := hi_eq
                  exact hND_ok.1 w (by rw [declVars, List.mem_filterMap]; exact ⟨_, hi_mem, rfl⟩)
                | _ => exact absurd hi_eq (by simp)
              · rw [bv_foldr_imp, List.mem_append] at hv
                rcases hv with hvspec | hvbase
                · rw [List.mem_flatMap] at hvspec
                  obtain ⟨b, hb_mem, hvb⟩ := hvspec
                  rw [List.mem_map] at hb_mem
                  obtain ⟨b0, hb0_mem, rfl⟩ := hb_mem
                  rw [SMT_bv_substList_eq_of_var_terms] at hvb
                  have hb0_spec : b0 ∈ specBodies (ΔP ++ Δcm) := hb0_mem
                  exact hND_ok.2 b0 hb0_spec v hvb
                · rw [SMT.bv, List.mem_append] at hvbase
                  rcases hvbase with hvzmem | hvP
                  · exact zmem_bv v hvzmem
                  · rw [SMT_bv_substList_eq_of_var_terms] at hvP
                    exact fun h => P_bv v hvP (used_to_St₃ h)
        · first
          | exact wp_bind_throw _ _ _ _
          | (mvcgen)
      · first
        | exact wp_bind_throw _ _ _ _
        | (mvcgen)
    · first
      | exact wp_bind_throw _ _ _ _
      | (mvcgen)

end SMT
