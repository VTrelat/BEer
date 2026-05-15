import SMT.Reasoning.Basic.StateSpecs
import SMT.Reasoning.Axioms

/-!
# `encodeTerm` structural specification

`encodeTerm_struct` captures the *structural* postcondition of `encodeTerm`:
state monotonicity, free-variable coverage of the encoded term, source-variable
coverage/preservation, and the existence of a covering renaming context.

Unlike `encodeTerm_spec`, it requires neither the `respects` hypothesis nor any
`B`-typing, and asserts neither `σ = α.toSMTType` nor any denotational fact —
precisely the parts unavailable (indeed false) for a flagged binder. It is
consumed by the HAS-FLAG branch of `encodeTerm_spec.all_case`, which needs
structural facts about the encoding of the binder body `P` without a (false)
`respects`.

The renaming witness is discharged generically (`renaming_witness`): the
encoded term's free variables all live in the final context `Γ' ⊆ usedVars`,
so `Δ₀` padded over `Γ'` covers it.
-/

open Std.Do B SMT ZFSet
set_option mvcgen.warning false

namespace SMT.RenamingContext

/-- Generic structural renaming witness: `Δ₀`, left-biased over the canonical
context induced by the final type context `Γ'`. -/
noncomputable def padWith (Δ₀ : Context) (Γ' : SMT.TypeContext) : Context :=
  fun v => match Δ₀ v with
    | some d => some d
    | none => ofTypeContext Γ' v

end SMT.RenamingContext

/-- The structural `∃ Δ'` clause of `encodeTerm_struct`, discharged generically
from free-variable coverage of the encoded term by the final context. -/
theorem encodeTerm_struct.renaming_witness
    {Δ₀ : SMT.RenamingContext.Context} {«Δ» : B.RenamingContext.Context}
    {t : B.Term} {Γ' : SMT.TypeContext} {t' : SMT.Term}
    {usedVars' used : List SMT.𝒱}
    (Δ₀_ext : SMT.RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» t)
    (Δ₀_none : ∀ v ∉ used, Δ₀ v = none)
    (used_sub : used ⊆ usedVars')
    (keys_sub : AList.keys Γ' ⊆ usedVars')
    (fv_sub : SMT.fv t' ⊆ AList.keys Γ') :
    ∃ (Δ' : SMT.RenamingContext.Context)
      (_ : SMT.RenamingContext.CoversFV Δ' t'),
      SMT.RenamingContext.Extends Δ' Δ₀ ∧
        SMT.RenamingContext.ExtendsOnSourceFV Δ' «Δ» t ∧
        (∀ v ∉ usedVars', Δ' v = none) := by
  refine ⟨SMT.RenamingContext.padWith Δ₀ Γ', ?_, ?_, ?_, ?_⟩
  · -- CoversFV
    intro v hv
    have hvΓ : v ∈ Γ' := AList.mem_keys.mp (fv_sub hv)
    obtain ⟨τv, hτv⟩ := Option.isSome_iff_exists.mp ((AList.lookup_isSome).2 hvΓ)
    simp only [SMT.RenamingContext.padWith]
    cases h : Δ₀ v with
    | some d => simp
    | none => simp [SMT.RenamingContext.ofTypeContext, hτv]
  · -- Extends Δ' Δ₀
    intro v d h
    simp only [SMT.RenamingContext.padWith, h]
  · -- ExtendsOnSourceFV Δ' «Δ» t
    intro v d h
    have h0 : Δ₀ v = some d := Δ₀_ext h
    simp only [SMT.RenamingContext.padWith, h0]
  · -- none outside usedVars'
    intro v hv
    have hvu : v ∉ used := fun hu => hv (used_sub hu)
    have h0 : Δ₀ v = none := Δ₀_none v hvu
    have hvΓ : v ∉ Γ' := fun hg => hv (keys_sub (AList.mem_keys.mpr hg))
    have hlk : AList.lookup v Γ' = none := by
      rcases hl : AList.lookup v Γ' with _ | τ
      · rfl
      · exact absurd (AList.lookup_isSome.mp (by rw [hl]; rfl)) hvΓ
    simp only [SMT.RenamingContext.padWith, h0, SMT.RenamingContext.ofTypeContext, hlk]

/-- If a type context's keys are covered by a used-variable list, inserting a
fresh key keeps the keys covered by the extended list. -/
theorem keys_insert_subset_cons {Γ : SMT.TypeContext} {v : SMT.𝒱} {τ : SMTType}
    {used : List SMT.𝒱} (hsub : AList.keys Γ ⊆ used) :
    AList.keys (Γ.insert v τ) ⊆ v :: used := by
  rw [AList.keys_insert]
  intro w hw
  rw [List.mem_cons] at hw ⊢
  rcases hw with rfl | hw
  · exact Or.inl rfl
  · exact Or.inr (hsub (List.mem_of_mem_erase hw))

set_option maxHeartbeats 4000000 in
/-- Purely structural specification of `defaultSpecM`: it advances `freshvarsc`,
only grows `usedVars`, keeps `keys ⊆ usedVars`, preserves source variables, and
introduces no new free variables beyond those of the input term (all auxiliary
binders are quantified away). Proved by induction on the result type. -/
theorem defaultSpecM_state
    (τ : SMTType) {Λ : SMT.TypeContext} {n : ℕ}
    {used : List SMT.𝒱} {name : String} {t : SMT.Term} :
    ⦃ fun (⟨E, Λ'⟩ : EncoderState) ↦
        ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ AList.keys Λ ⊆ E.usedVars ∧ E.usedVars = used⌝ ⦄
    defaultSpecM name τ t
    ⦃ ⇓? (d : SMT.Term) (⟨E', Γ'⟩ : EncoderState) => ⌜
      n ≤ E'.freshvarsc ∧
      Λ ⊆ Γ' ∧
      used ⊆ E'.usedVars ∧
      AList.keys Γ' ⊆ E'.usedVars ∧
      (∀ v ∈ used, v ∉ Λ → v ∉ Γ') ∧
      SMT.fv d ⊆ SMT.fv t ⌝⦄ := by
  induction τ generalizing Λ n used name t with
  | int | bool =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl⟩ := pre
    unfold defaultSpecM
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨le_refl _, fun e he => he, fun v hv => hv, sub, fun v hv hΛ => hΛ, ?_⟩
    intro v hv
    simp only [SMT.fv, List.mem_append, List.not_mem_nil, or_false] at hv
    exact hv
  | unit =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl⟩ := pre
    unfold defaultSpecM
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨le_refl _, fun e he => he, fun v hv => hv, sub, fun v hv hΛ => hΛ, ?_⟩
    intro v hv
    simp only [SMT.fv, List.not_mem_nil] at hv
  | option σ _ih =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl⟩ := pre
    unfold defaultSpecM
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨le_refl _, fun e he => he, fun v hv => hv, sub, fun v hv hΛ => hΛ, ?_⟩
    intro v hv
    simp only [noneCast, SMT.fv, List.mem_append, List.not_mem_nil, or_false] at hv
    exact hv
  | pair σ ρ σ_ih ρ_ih =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl⟩ := pre
    unfold defaultSpecM
    mspec σ_ih
    mrename_i pre
    mintro ∀St₂
    mpure pre
    obtain ⟨fst_le, fst_Λ_sub, fst_used_sub, fst_keys_sub, fst_preserves, fst_fv_sub⟩ := pre
    mspec ρ_ih
    mrename_i pre
    mintro ∀St₃
    mpure pre
    obtain ⟨snd_le, snd_Λ_sub, snd_used_sub, snd_keys_sub, snd_preserves, snd_fv_sub⟩ := pre
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨le_trans fst_le snd_le, AList.subset_trans fst_Λ_sub snd_Λ_sub,
      fun v hv => snd_used_sub (fst_used_sub hv), snd_keys_sub, ?_, ?_⟩
    · intro v hv hΛ
      exact snd_preserves v (fst_used_sub hv) (fst_preserves v hv hΛ)
    · intro v hv
      simp only [SMT.fv, List.mem_append] at hv
      rcases hv with hv | hv
      · have := fst_fv_sub hv
        simp only [SMT.fv] at this
        exact this
      · have := snd_fv_sub hv
        simp only [SMT.fv] at this
        exact this
  | «fun» σ ρ _σ_ih ρ_ih =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl⟩ := pre
    unfold defaultSpecM
    mspec SMT.freshVar_spec
    mrename_i pre
    mintro ∀St₂
    mpure pre
    obtain ⟨St₂_types_eq, z_fresh, St₂_fvc, St₂_used_eq, z_not_used⟩ := pre
    have St₂_keys_sub : AList.keys St₂.types ⊆ St₂.env.usedVars := by
      rw [St₂_types_eq, St₂_used_eq]; exact keys_insert_subset_cons sub
    mspec (ρ_ih (Λ := St₂.types) (n := St₂.env.freshvarsc) (used := St₂.env.usedVars))
    mrename_i pre
    mintro ∀St₃
    mpure pre
    obtain ⟨body_le, body_Λ_sub, body_used_sub, body_keys_sub, body_preserves, body_fv_sub⟩ := pre
    mspec Std.Do.Spec.pure
    mpure_intro
    rename_i z _
    refine ⟨?_, ?_, ?_, body_keys_sub, ?_, ?_⟩
    · have h : St.env.freshvarsc ≤ St₂.env.freshvarsc := by omega
      exact le_trans h body_le
    · have hz : St₂.types ⊆ St₃.types := body_Λ_sub
      rw [St₂_types_eq] at hz
      exact AList.subset_trans
        (SMT.TypeContext.entries_subset_insert_of_notMem z_fresh) hz
    · intro v hv
      apply body_used_sub
      rw [St₂_used_eq]
      exact List.mem_cons_of_mem _ hv
    · intro v hv hΛ
      have hv_St₂ : v ∈ St₂.env.usedVars := by
        rw [St₂_used_eq]; exact List.mem_cons_of_mem _ hv
      have hv_ne_z : v ≠ z := fun h => z_not_used (h ▸ hv)
      apply body_preserves v hv_St₂
      rw [St₂_types_eq, AList.mem_insert]
      push_neg
      exact ⟨hv_ne_z, hΛ⟩
    · intro v hv
      simp only [SMT.fv, List.mem_removeAll_iff, List.mem_cons,
        List.not_mem_nil, or_false] at hv
      obtain ⟨hv_body, hv_ne_z⟩ := hv
      have hmem := body_fv_sub hv_body
      simp only [SMT.fv, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with hvt | hvz
      · exact hvt
      · exact absurd hvz hv_ne_z

/-- The structural postcondition shape of `loosenAux_prf`, abstracted so it can
be stated both as a goal and as an induction/recursion hypothesis. -/
abbrev LoosenAuxStatePost (β : SMTType) (Λ : SMT.TypeContext) (n : ℕ)
    (used : List SMT.𝒱) (x : SMT.Term) :
    PostCond (SMT.𝒱 × SMT.Term) (.arg EncoderState (.except String .pure)) :=
  ⇓? (⟨x!, x!_spec⟩ : SMT.𝒱 × SMT.Term) (⟨E', Γ'⟩ : EncoderState) => ⌜
    n ≤ E'.freshvarsc ∧
    Λ.insert x! β ⊆ Γ' ∧
    x! ∉ Λ ∧
    x! ∉ used ∧
    used ⊆ E'.usedVars ∧
    AList.keys Γ' ⊆ E'.usedVars ∧
    (∀ v ∈ used, v ∉ Λ → v ∉ Γ') ∧
    SMT.fv x!_spec ⊆ SMT.fv x ∪ {x!} ⌝

/-- The structural precondition shape of `loosenAux_prf`. -/
abbrev LoosenAuxStatePre (Λ : SMT.TypeContext) (n : ℕ) (used : List SMT.𝒱) :
    Assertion (.arg EncoderState (.except String .pure)) :=
  fun (⟨E, Λ'⟩ : EncoderState) ↦
    ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ AList.keys Λ ⊆ E.usedVars ∧ E.usedVars = used⌝

set_option maxHeartbeats 4000000 in
/-- The `pair` case of `loosenAux_prf_state`, factored out so it can be reused
both by the `pair` constructor and the `graph` constructor (whose inner
recursion is on a `castPath.pair`). Takes the structural specs of the component
cast paths as hypotheses. -/
theorem loosenAux_prf_state_pair
    {α β α' β' : SMTType} (pα : α ~> α') (pβ : β ~> β')
    (pα_ih : ∀ {Λ : SMT.TypeContext} {n : ℕ} {used : List SMT.𝒱} {name : String}
      {x : SMT.Term},
      Std.Do.Triple (loosenAux_prf name pα x)
        (LoosenAuxStatePre Λ n used) (LoosenAuxStatePost α' Λ n used x))
    (pβ_ih : ∀ {Λ : SMT.TypeContext} {n : ℕ} {used : List SMT.𝒱} {name : String}
      {x : SMT.Term},
      Std.Do.Triple (loosenAux_prf name pβ x)
        (LoosenAuxStatePre Λ n used) (LoosenAuxStatePost β' Λ n used x))
    {Λ : SMT.TypeContext} {n : ℕ} {used : List SMT.𝒱} {name : String}
    {x : SMT.Term} :
    Std.Do.Triple (loosenAux_prf name (castPath.pair pα pβ) x)
      (LoosenAuxStatePre Λ n used)
      (LoosenAuxStatePost (α'.pair β') Λ n used x) := by
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, sub, rfl⟩ := pre
  unfold loosenAux_prf
  mspec SMT.freshVar_spec
  mrename_i pre
  mintro ∀St₂
  mpure pre
  obtain ⟨St₂_types_eq, x!_fresh, St₂_fvc, St₂_used_eq, x!_not_used⟩ := pre
  have St₂_keys_sub : AList.keys St₂.types ⊆ St₂.env.usedVars := by
    rw [St₂_types_eq, St₂_used_eq]; exact keys_insert_subset_cons sub
  mspec (pα_ih (Λ := St₂.types) (n := St₂.env.freshvarsc) (used := St₂.env.usedVars))
  mrename_i pre
  mintro ∀St₃
  mpure pre
  obtain ⟨fst!_le, fst!_Λ_sub, fst!_fresh, fst!_not_used, fst!_used_sub,
    fst!_keys_sub, fst!_preserves, fst!_fv_sub⟩ := pre
  mspec (pβ_ih (Λ := St₃.types) (n := St₃.env.freshvarsc) (used := St₃.env.usedVars))
  mrename_i pre
  mintro ∀St₄
  mpure pre
  obtain ⟨snd!_le, snd!_Λ_sub, snd!_fresh, snd!_not_used, snd!_used_sub,
    snd!_keys_sub, snd!_preserves, snd!_fv_sub⟩ := pre
  mspec Std.Do.Spec.pure
  mpure_intro
  rename_i x! fst_out snd_out
  obtain ⟨fst!, fst!_spec⟩ := fst_out
  obtain ⟨snd!, snd!_spec⟩ := snd_out
  and_intros
  · have h₁ : St.env.freshvarsc ≤ St₂.env.freshvarsc := by omega
    exact le_trans h₁ (le_trans fst!_le snd!_le)
  · have hf : St₂.types ⊆ AList.insert fst! α' St₂.types :=
      SMT.TypeContext.entries_subset_insert_of_notMem fst!_fresh
    have hs : St₃.types ⊆ AList.insert snd! β' St₃.types :=
      SMT.TypeContext.entries_subset_insert_of_notMem snd!_fresh
    have h₃ : AList.insert x! (α'.pair β') St.types ⊆ St₄.types := by
      rw [← St₂_types_eq]
      exact AList.subset_trans hf (AList.subset_trans fst!_Λ_sub
        (AList.subset_trans hs snd!_Λ_sub))
    exact h₃
  · exact x!_fresh
  · exact x!_not_used
  · intro v hv
    apply snd!_used_sub
    apply fst!_used_sub
    rw [St₂_used_eq]
    exact List.mem_cons_of_mem _ hv
  · exact snd!_keys_sub
  · intro v hv hv_not_St
    have hv_St₂ : v ∈ St₂.env.usedVars := by
      rw [St₂_used_eq]; exact List.mem_cons_of_mem _ hv
    have hv_St₃ : v ∈ St₃.env.usedVars := fst!_used_sub hv_St₂
    have hv_ne_x! : v ≠ x! := fun h => x!_not_used (h ▸ hv)
    have hv_not_St₂ : v ∉ St₂.types := by
      rw [St₂_types_eq, AList.mem_insert]
      push_neg
      exact ⟨hv_ne_x!, hv_not_St⟩
    have hv_not_St₃ : v ∉ St₃.types := fst!_preserves v hv_St₂ hv_not_St₂
    exact snd!_preserves v hv_St₃ hv_not_St₃
  · intro v hv
    simp only [SMT.fv, List.mem_append, List.mem_removeAll_iff,
      List.mem_cons, List.not_mem_nil, or_false] at hv
    rw [List.mem_union_iff]
    obtain ⟨hv_body, hv_ne_fstsnd⟩ := hv
    have hv_ne_fst! : v ≠ fst! := fun h => hv_ne_fstsnd (Or.inl h)
    have hv_ne_snd! : v ≠ snd! := fun h => hv_ne_fstsnd (Or.inr h)
    rcases hv_body with (hvx! | hvfst! | hvsnd!) | (hvfspec | hvsspec)
    · exact Or.inr (List.mem_singleton.mpr hvx!)
    · exact absurd hvfst! hv_ne_fst!
    · exact absurd hvsnd! hv_ne_snd!
    · have hmem := fst!_fv_sub hvfspec
      rw [List.mem_union_iff] at hmem
      rcases hmem with hx | hgv
      · simp only [SMT.fv] at hx; exact Or.inl hx
      · exact absurd (List.mem_singleton.mp hgv) hv_ne_fst!
    · have hmem := snd!_fv_sub hvsspec
      rw [List.mem_union_iff] at hmem
      rcases hmem with hx | hs!
      · simp only [SMT.fv] at hx; exact Or.inl hx
      · exact absurd (List.mem_singleton.mp hs!) hv_ne_snd!

set_option maxHeartbeats 4000000 in
/-- Purely structural specification of `loosenAux_prf` (no `B`-typing, no
`respects`, no denotation): the loosening introduces a fresh head variable `x!`
of type `β`, advances `freshvarsc`, only grows `usedVars`, keeps `keys ⊆
usedVars`, preserves source variables, and the spec term's free variables stay
within `fv x ∪ {x!}`. Proved by induction on the cast path. -/
theorem loosenAux_prf_state
    {α β : SMTType} (c : α ~> β) {Λ : SMT.TypeContext} {n : ℕ}
    {used : List SMT.𝒱} {name : String} {x : SMT.Term} :
    Std.Do.Triple (loosenAux_prf name c x)
      (LoosenAuxStatePre Λ n used)
      (LoosenAuxStatePost β Λ n used x) := by
  induction c generalizing Λ n used name x with
  | @refl α hα =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl⟩ := pre
    unfold loosenAux_prf
    mspec SMT.freshVar_spec
    mrename_i pre
    mintro ∀St₂
    mpure pre
    obtain ⟨St₂_types_eq, x!_fresh, St₂_fvc, St₂_used_eq, x!_not_used⟩ := pre
    mspec Std.Do.Spec.pure
    mpure_intro
    and_intros
    · rw [St₂_fvc]; exact Nat.le_succ _
    · rw [St₂_types_eq]
    · exact x!_fresh
    · exact x!_not_used
    · rw [St₂_used_eq]; intro v hv; exact List.mem_cons_of_mem _ hv
    · rw [St₂_types_eq, St₂_used_eq, AList.keys_insert]
      intro v hv
      rw [List.mem_cons] at hv ⊢
      rcases hv with rfl | hv
      · exact Or.inl rfl
      · exact Or.inr (sub (List.mem_of_mem_erase hv))
    · intro v hv hv_not_Λ
      rw [St₂_types_eq, AList.mem_insert]
      push_neg
      exact ⟨fun h => absurd (h ▸ hv) x!_not_used, hv_not_Λ⟩
    · rw [SMT.fv, SMT.fv]
      intro v hv
      rw [List.cons_append, List.nil_append, List.mem_cons] at hv
      rw [List.mem_union_iff]
      rcases hv with rfl | hv
      · exact Or.inr (List.mem_singleton.mpr rfl)
      · exact Or.inl hv
  | @graph α β α' β' pα pβ pα_ih pβ_ih =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl⟩ := pre
    unfold loosenAux_prf
    mspec SMT.freshVar_spec
    mrename_i pre
    mintro ∀St₂
    mpure pre
    obtain ⟨St₂_types_eq, x!_fresh, St₂_fvc, St₂_used_eq, x!_not_used⟩ := pre
    mspec SMT.freshVar_spec
    mrename_i pre
    mintro ∀St₃
    mpure pre
    obtain ⟨St₃_types_eq, z_fresh, St₃_fvc, St₃_used_eq, z_not_used⟩ := pre
    have St₂_keys_sub : AList.keys St₂.types ⊆ St₂.env.usedVars := by
      rw [St₂_types_eq, St₂_used_eq]; exact keys_insert_subset_cons sub
    have St₃_keys_sub : AList.keys St₃.types ⊆ St₃.env.usedVars := by
      rw [St₃_types_eq, St₃_used_eq]; exact keys_insert_subset_cons St₂_keys_sub
    mspec (loosenAux_prf_state_pair pα pβ pα_ih pβ_ih
      (Λ := St₃.types) (n := St₃.env.freshvarsc) (used := St₃.env.usedVars))
    mrename_i pre
    mintro ∀St₄
    mpure pre
    obtain ⟨z!_le, z!_Λ_sub, z!_fresh, z!_not_used, z!_used_sub,
      z!_keys_sub, z!_preserves, z!_fv_sub⟩ := pre
    mspec Std.Do.Spec.pure
    mpure_intro
    rename_i x! z out
    obtain ⟨z!, z!_spec⟩ := out
    and_intros
    · have h : St.env.freshvarsc ≤ St₃.env.freshvarsc := by omega
      exact le_trans h z!_le
    · have h₁ : St₂.types ⊆ St₃.types := by
        rw [St₃_types_eq]; exact SMT.TypeContext.entries_subset_insert_of_notMem z_fresh
      have h₂ : St₃.types ⊆ AList.insert z! (α'.pair β') St₃.types :=
        SMT.TypeContext.entries_subset_insert_of_notMem z!_fresh
      rw [St₂_types_eq] at h₁
      exact AList.subset_trans h₁ (AList.subset_trans h₂ z!_Λ_sub)
    · exact x!_fresh
    · exact x!_not_used
    · intro v hv
      apply z!_used_sub
      rw [St₃_used_eq, St₂_used_eq]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hv)
    · exact z!_keys_sub
    · intro v hv hv_not_St
      have hv_St₃ : v ∈ St₃.env.usedVars := by
        rw [St₃_used_eq, St₂_used_eq]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hv)
      have hv_ne_x! : v ≠ x! := fun h => x!_not_used (h ▸ hv)
      have hv_ne_z : v ≠ z := fun h => z_not_used (h ▸ (St₂_used_eq ▸ List.mem_cons_of_mem _ hv))
      apply z!_preserves v hv_St₃
      rw [St₃_types_eq, St₂_types_eq, AList.mem_insert, AList.mem_insert]
      push_neg
      exact ⟨hv_ne_z, hv_ne_x!, hv_not_St⟩
    · intro v hv
      simp only [SMT.fv, List.mem_append, List.mem_removeAll_iff,
        List.mem_cons, List.not_mem_nil, or_false] at hv
      rw [List.mem_union_iff]
      rcases hv with hv | ⟨⟨hv_body, hv_ne_z⟩, hv_ne_z!⟩
      · exact Or.inr (List.mem_singleton.mpr hv)
      · rcases hv_body with ((hvx | hvz) | hvz') | hvspec
        · exact Or.inl hvx
        · exact absurd hvz hv_ne_z
        · exact absurd hvz' hv_ne_z
        · have hmem := z!_fv_sub hvspec
          rw [List.mem_union_iff] at hmem
          rcases hmem with hz | hz!
          · simp only [SMT.fv, List.mem_singleton] at hz
            exact absurd hz hv_ne_z
          · exact absurd (List.mem_singleton.mp hz!) hv_ne_z!
  | @chpred α α' p ih =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl⟩ := pre
    unfold loosenAux_prf
    mspec SMT.freshVar_spec
    mrename_i pre
    mintro ∀St₂
    mpure pre
    obtain ⟨St₂_types_eq, x!_fresh, St₂_fvc, St₂_used_eq, x!_not_used⟩ := pre
    mspec SMT.freshVar_spec
    mrename_i pre
    mintro ∀St₃
    mpure pre
    obtain ⟨St₃_types_eq, z_fresh, St₃_fvc, St₃_used_eq, z_not_used⟩ := pre
    have St₂_keys_sub : AList.keys St₂.types ⊆ St₂.env.usedVars := by
      rw [St₂_types_eq, St₂_used_eq]; exact keys_insert_subset_cons sub
    have St₃_keys_sub : AList.keys St₃.types ⊆ St₃.env.usedVars := by
      rw [St₃_types_eq, St₃_used_eq]; exact keys_insert_subset_cons St₂_keys_sub
    mspec (ih (Λ := St₃.types) (n := St₃.env.freshvarsc) (used := St₃.env.usedVars))
    mrename_i pre
    mintro ∀St₄
    mpure pre
    obtain ⟨z!_le, z!_Λ_sub, z!_fresh, z!_not_used, z!_used_sub,
      z!_keys_sub, z!_preserves, z!_fv_sub⟩ := pre
    mspec Std.Do.Spec.pure
    mpure_intro
    rename_i x! z out
    obtain ⟨z!, z!_spec⟩ := out
    and_intros
    · have : St.env.freshvarsc ≤ St₃.env.freshvarsc := by omega
      exact le_trans this z!_le
    · have h₁ : St₂.types ⊆ St₃.types := by
        rw [St₃_types_eq]; exact SMT.TypeContext.entries_subset_insert_of_notMem z_fresh
      have h₂ : St₃.types ⊆ AList.insert z! α' St₃.types :=
        SMT.TypeContext.entries_subset_insert_of_notMem z!_fresh
      rw [St₂_types_eq] at h₁
      exact AList.subset_trans h₁ (AList.subset_trans h₂ z!_Λ_sub)
    · exact x!_fresh
    · exact x!_not_used
    · intro v hv
      apply z!_used_sub
      rw [St₃_used_eq, St₂_used_eq]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hv)
    · exact z!_keys_sub
    · intro v hv hv_not_St
      have hv_St₃ : v ∈ St₃.env.usedVars := by
        rw [St₃_used_eq, St₂_used_eq]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hv)
      have hv_ne_x! : v ≠ x! := fun h => x!_not_used (h ▸ hv)
      have hv_ne_z : v ≠ z := fun h => z_not_used (h ▸ (St₂_used_eq ▸ List.mem_cons_of_mem _ hv))
      apply z!_preserves v hv_St₃
      rw [St₃_types_eq, St₂_types_eq, AList.mem_insert, AList.mem_insert]
      push_neg
      exact ⟨hv_ne_z, hv_ne_x!, hv_not_St⟩
    · intro v hv
      simp only [SMT.fv, List.mem_append, List.mem_removeAll_iff,
        List.mem_cons, List.not_mem_nil, or_false] at hv
      rw [List.mem_union_iff]
      rcases hv with hv | ⟨⟨⟨hv_body, hv_ne_z⟩, hv_ne_z!⟩⟩
      · exact Or.inr (List.mem_singleton.mpr hv)
      · rcases hv_body with (hvx | hvz) | hvspec
        · exact Or.inl hvx
        · exact absurd hvz hv_ne_z
        · have hmem := z!_fv_sub hvspec
          rw [List.mem_union_iff] at hmem
          rcases hmem with hz | hz!
          · simp only [SMT.fv, List.mem_singleton] at hz
            exact absurd hz hv_ne_z
          · exact absurd (List.mem_singleton.mp hz!) hv_ne_z!
  | @«fun» α β α' β' hβ pα pβ pα_ih pβ_ih =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl⟩ := pre
    unfold loosenAux_prf
    mspec SMT.freshVar_spec
    mrename_i pre
    mintro ∀St₂
    mpure pre
    obtain ⟨St₂_types_eq, x!_fresh, St₂_fvc, St₂_used_eq, x!_not_used⟩ := pre
    have St₂_keys_sub : AList.keys St₂.types ⊆ St₂.env.usedVars := by
      rw [St₂_types_eq, St₂_used_eq]; exact keys_insert_subset_cons sub
    mspec SMT.freshVar_spec
    mrename_i pre
    mintro ∀St₃
    mpure pre
    obtain ⟨St₃_types_eq, a_fresh, St₃_fvc, St₃_used_eq, a_not_used⟩ := pre
    have St₃_keys_sub : AList.keys St₃.types ⊆ St₃.env.usedVars := by
      rw [St₃_types_eq, St₃_used_eq]; exact keys_insert_subset_cons St₂_keys_sub
    mspec (pα_ih (Λ := St₃.types) (n := St₃.env.freshvarsc) (used := St₃.env.usedVars))
    mrename_i pre
    mintro ∀St₄
    mpure pre
    obtain ⟨a!_le, a!_Λ_sub, a!_fresh, a!_not_used, a!_used_sub,
      a!_keys_sub, a!_preserves, a!_fv_sub⟩ := pre
    mspec SMT.freshVar_spec
    mrename_i pre
    mintro ∀St₅
    mpure pre
    obtain ⟨St₅_types_eq, b_fresh, St₅_fvc, St₅_used_eq, b_not_used⟩ := pre
    have St₅_keys_sub : AList.keys St₅.types ⊆ St₅.env.usedVars := by
      rw [St₅_types_eq, St₅_used_eq]; exact keys_insert_subset_cons a!_keys_sub
    mspec (pβ_ih (Λ := St₅.types) (n := St₅.env.freshvarsc) (used := St₅.env.usedVars))
    mrename_i pre
    mintro ∀St₆
    mpure pre
    obtain ⟨b!_le, b!_Λ_sub, b!_fresh, b!_not_used, b!_used_sub,
      b!_keys_sub, b!_preserves, b!_fv_sub⟩ := pre
    mspec (defaultSpecM_state β' (Λ := St₆.types) (n := St₆.env.freshvarsc)
      (used := St₆.env.usedVars))
    mrename_i pre
    mintro ∀St₇
    mpure pre
    obtain ⟨hd_le, hd_Λ_sub, hd_used_sub, hd_keys_sub, hd_preserves, hd_fv_sub⟩ := pre
    mspec Std.Do.Spec.pure
    mpure_intro
    rename_i x! a a_out b b_out _hdefault
    obtain ⟨a!, a!_spec⟩ := a_out
    obtain ⟨b!, b!_spec⟩ := b_out
    and_intros
    · have h : St.env.freshvarsc ≤ St₃.env.freshvarsc := by omega
      exact le_trans h (le_trans a!_le (le_trans (by omega : St₄.env.freshvarsc ≤
        St₅.env.freshvarsc) (le_trans b!_le hd_le)))
    · have h23 : St₂.types ⊆ St₃.types := by
        rw [St₃_types_eq]; exact SMT.TypeContext.entries_subset_insert_of_notMem a_fresh
      have h34 : St₃.types ⊆ St₄.types :=
        AList.subset_trans (SMT.TypeContext.entries_subset_insert_of_notMem a!_fresh) a!_Λ_sub
      have h45 : St₄.types ⊆ St₅.types := by
        rw [St₅_types_eq]; exact SMT.TypeContext.entries_subset_insert_of_notMem b_fresh
      have h56 : St₅.types ⊆ St₆.types :=
        AList.subset_trans (SMT.TypeContext.entries_subset_insert_of_notMem b!_fresh) b!_Λ_sub
      have h₃ : AList.insert x! (α'.fun β') St.types ⊆ St₇.types := by
        rw [← St₂_types_eq]
        exact AList.subset_trans h23 (AList.subset_trans h34 (AList.subset_trans h45
          (AList.subset_trans h56 hd_Λ_sub)))
      exact h₃
    · exact x!_fresh
    · exact x!_not_used
    · intro v hv
      apply hd_used_sub
      apply b!_used_sub
      rw [St₅_used_eq]
      apply List.mem_cons_of_mem
      apply a!_used_sub
      rw [St₃_used_eq]
      apply List.mem_cons_of_mem
      rw [St₂_used_eq]
      exact List.mem_cons_of_mem _ hv
    · exact hd_keys_sub
    · intro v hv hv_not_St
      have hv_St₂ : v ∈ St₂.env.usedVars := by
        rw [St₂_used_eq]; exact List.mem_cons_of_mem _ hv
      have hv_St₃ : v ∈ St₃.env.usedVars := by
        rw [St₃_used_eq]; exact List.mem_cons_of_mem _ hv_St₂
      have hv_ne_x! : v ≠ x! := fun h => x!_not_used (h ▸ hv)
      have hv_ne_a : v ≠ a := fun h => a_not_used (h ▸ hv_St₂)
      have hv_not_St₂ : v ∉ St₂.types := by
        rw [St₂_types_eq, AList.mem_insert]
        push_neg
        exact ⟨hv_ne_x!, hv_not_St⟩
      have hv_not_St₃ : v ∉ St₃.types := by
        rw [St₃_types_eq, AList.mem_insert]
        push_neg
        exact ⟨hv_ne_a, hv_not_St₂⟩
      have hv_St₄ : v ∈ St₄.env.usedVars := a!_used_sub hv_St₃
      have hv_not_St₄ : v ∉ St₄.types := a!_preserves v hv_St₃ hv_not_St₃
      have hv_St₅ : v ∈ St₅.env.usedVars := by
        rw [St₅_used_eq]; exact List.mem_cons_of_mem _ hv_St₄
      have hv_ne_b : v ≠ b := fun h => b_not_used (h ▸ hv_St₄)
      have hv_not_St₅ : v ∉ St₅.types := by
        rw [St₅_types_eq, AList.mem_insert]
        push_neg
        exact ⟨hv_ne_b, hv_not_St₄⟩
      have hv_St₆ : v ∈ St₆.env.usedVars := b!_used_sub hv_St₅
      have hv_not_St₆ : v ∉ St₆.types := b!_preserves v hv_St₅ hv_not_St₅
      exact hd_preserves v hv_St₆ hv_not_St₆
    · intro v hv
      simp only [SMT.fv, List.mem_removeAll_iff, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false] at hv
      rw [List.mem_union_iff]
      obtain ⟨hv_body, hv_ne_a!⟩ := hv
      rcases hv_body with (hv_c | hv_t') | hv_e
      · -- v ∈ fv (∃[a][α] a!_spec)
        obtain ⟨hv_aspec, hv_ne_a⟩ := hv_c
        have hmem := a!_fv_sub hv_aspec
        rw [List.mem_union_iff] at hmem
        rcases hmem with ha | ha!
        · simp only [SMT.fv, List.mem_singleton] at ha
          exact absurd ha hv_ne_a
        · exact absurd (List.mem_singleton.mp ha!) hv_ne_a!
      · -- v ∈ fv (forall [b!][β'] body)
        obtain ⟨hv_bodyt, hv_ne_b!⟩ := hv_t'
        rcases hv_bodyt with ((hvx! | hva!) | hvb!) | hv_inner
        · exact Or.inr (List.mem_singleton.mpr hvx!)
        · exact absurd hva! hv_ne_a!
        · exact absurd hvb! hv_ne_b!
        · obtain ⟨hv_inner_body, hv_ne_ab⟩ := hv_inner
          have hv_ne_a : v ≠ a := fun h => hv_ne_ab (Or.inl h)
          have hv_ne_b : v ≠ b := fun h => hv_ne_ab (Or.inr h)
          rcases hv_inner_body with ((hvx | hva) | hvb) | (hvaspec | hvbspec)
          · exact Or.inl hvx
          · exact absurd hva hv_ne_a
          · exact absurd hvb hv_ne_b
          · have hmem := a!_fv_sub hvaspec
            rw [List.mem_union_iff] at hmem
            rcases hmem with ha | ha!
            · simp only [SMT.fv, List.mem_singleton] at ha
              exact absurd ha hv_ne_a
            · exact absurd (List.mem_singleton.mp ha!) hv_ne_a!
          · have hmem := b!_fv_sub hvbspec
            rw [List.mem_union_iff] at hmem
            rcases hmem with hb | hb!
            · simp only [SMT.fv, List.mem_singleton] at hb
              exact absurd hb hv_ne_b
            · exact absurd (List.mem_singleton.mp hb!) hv_ne_b!
      · -- v ∈ fv hdefault
        have hmem := hd_fv_sub hv_e
        simp only [SMT.fv, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with hvx! | hva!
        · exact Or.inr (List.mem_singleton.mpr hvx!)
        · exact absurd hva! hv_ne_a!
  | @pair α β α' β' pα pβ pα_ih pβ_ih =>
    exact loosenAux_prf_state_pair pα pβ pα_ih pβ_ih
  | @opt α α' p ih =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl⟩ := pre
    unfold loosenAux_prf
    mspec SMT.freshVar_spec
    mrename_i pre
    mintro ∀St₂
    mpure pre
    obtain ⟨St₂_types_eq, x!_fresh, St₂_fvc, St₂_used_eq, x!_not_used⟩ := pre
    have St₂_keys_sub : AList.keys St₂.types ⊆ St₂.env.usedVars := by
      rw [St₂_types_eq, St₂_used_eq]; exact keys_insert_subset_cons sub
    split
    · -- x = none
      rename_i x!
      mspec Std.Do.Spec.pure
      mpure_intro
      and_intros
      · rw [St₂_fvc]; exact Nat.le_succ _
      · rw [St₂_types_eq]
      · exact x!_fresh
      · exact x!_not_used
      · rw [St₂_used_eq]; intro v hv; exact List.mem_cons_of_mem _ hv
      · exact St₂_keys_sub
      · intro v hv hv_not_St
        rw [St₂_types_eq, AList.mem_insert]
        push_neg
        exact ⟨fun h => absurd (h ▸ hv) x!_not_used, hv_not_St⟩
      · intro v hv
        rw [List.mem_union_iff]
        refine Or.inr (List.mem_singleton.mpr ?_)
        simpa only [noneCast, SMT.fv, List.mem_append, List.not_mem_nil, or_false,
          List.mem_singleton] using hv
    · -- x = some x₀
      rename_i x! x₀
      mspec (ih (Λ := St₂.types) (n := St₂.env.freshvarsc) (used := St₂.env.usedVars))
      mrename_i pre
      mintro ∀St₃
      mpure pre
      obtain ⟨w!_le, w!_Λ_sub, w!_fresh, w!_not_used, w!_used_sub,
        w!_keys_sub, w!_preserves, w!_fv_sub⟩ := pre
      mspec Std.Do.Spec.pure
      mpure_intro
      rename_i out
      obtain ⟨w!, w!_spec⟩ := out
      and_intros
      · have h : St.env.freshvarsc ≤ St₂.env.freshvarsc := by omega
        exact le_trans h w!_le
      · have h₂ : St₂.types ⊆ AList.insert w! α' St₂.types :=
          SMT.TypeContext.entries_subset_insert_of_notMem w!_fresh
        have h₃ : AList.insert x! α'.option St.types ⊆ St₃.types := by
          rw [← St₂_types_eq]; exact AList.subset_trans h₂ w!_Λ_sub
        exact h₃
      · exact x!_fresh
      · exact x!_not_used
      · intro v hv
        apply w!_used_sub
        rw [St₂_used_eq]
        exact List.mem_cons_of_mem _ hv
      · exact w!_keys_sub
      · intro v hv hv_not_St
        have hv_St₂ : v ∈ St₂.env.usedVars := by
          rw [St₂_used_eq]; exact List.mem_cons_of_mem _ hv
        have hv_ne_x! : v ≠ x! := fun h => x!_not_used (h ▸ hv)
        apply w!_preserves v hv_St₂
        rw [St₂_types_eq, AList.mem_insert]
        push_neg
        exact ⟨hv_ne_x!, hv_not_St⟩
      · intro v hv
        simp only [SMT.fv, List.mem_append, List.mem_removeAll_iff,
          List.mem_cons, List.not_mem_nil, or_false] at hv
        rw [List.mem_union_iff]
        obtain ⟨hv_body, hv_ne_w!⟩ := hv
        rcases hv_body with (hvx! | hvw!) | hvspec
        · exact Or.inr (List.mem_singleton.mpr hvx!)
        · exact absurd hvw! hv_ne_w!
        · have hmem := w!_fv_sub hvspec
          rw [List.mem_union_iff] at hmem
          rcases hmem with hx₀ | hw!
          · left; rw [SMT.fv]; exact hx₀
          · exact absurd (List.mem_singleton.mp hw!) hv_ne_w!
    · -- x = catch-all (the)
      rename_i x! x_ne_none x_ne_some
      mspec (ih (Λ := St₂.types) (n := St₂.env.freshvarsc) (used := St₂.env.usedVars))
      mrename_i pre
      mintro ∀St₃
      mpure pre
      obtain ⟨w!_le, w!_Λ_sub, w!_fresh, w!_not_used, w!_used_sub,
        w!_keys_sub, w!_preserves, w!_fv_sub⟩ := pre
      mspec Std.Do.Spec.pure
      mpure_intro
      rename_i out
      obtain ⟨w!, w!_spec⟩ := out
      and_intros
      · have h : St.env.freshvarsc ≤ St₂.env.freshvarsc := by omega
        exact le_trans h w!_le
      · have h₂ : St₂.types ⊆ AList.insert w! α' St₂.types :=
          SMT.TypeContext.entries_subset_insert_of_notMem w!_fresh
        have h₃ : AList.insert x! α'.option St.types ⊆ St₃.types := by
          rw [← St₂_types_eq]; exact AList.subset_trans h₂ w!_Λ_sub
        exact h₃
      · exact x!_fresh
      · exact x!_not_used
      · intro v hv
        apply w!_used_sub
        rw [St₂_used_eq]
        exact List.mem_cons_of_mem _ hv
      · exact w!_keys_sub
      · intro v hv hv_not_St
        have hv_St₂ : v ∈ St₂.env.usedVars := by
          rw [St₂_used_eq]; exact List.mem_cons_of_mem _ hv
        have hv_ne_x! : v ≠ x! := fun h => x!_not_used (h ▸ hv)
        apply w!_preserves v hv_St₂
        rw [St₂_types_eq, AList.mem_insert]
        push_neg
        exact ⟨hv_ne_x!, hv_not_St⟩
      · intro v hv
        simp only [noneCast, SMT.fv, List.mem_append, List.mem_removeAll_iff,
          List.mem_cons, List.not_mem_nil, or_false] at hv
        rw [List.mem_union_iff]
        rcases hv with (hvc | hvt) | ⟨hv_body, hv_ne_w!⟩
        · exact Or.inl hvc
        · exact Or.inr (List.mem_singleton.mpr hvt)
        · rcases hv_body with (hvx! | hvw!) | hvspec
          · exact Or.inr (List.mem_singleton.mpr hvx!)
          · exact absurd hvw! hv_ne_w!
          · have hmem := w!_fv_sub hvspec
            rw [List.mem_union_iff] at hmem
            rcases hmem with hx | hw!
            · simp only [SMT.fv] at hx
              exact Or.inl hx
            · exact absurd (List.mem_singleton.mp hw!) hv_ne_w!

set_option maxHeartbeats 4000000 in
/-- Purely structural specification of `castUnionAux` (no `B`-typing, no
`respects`, no denotation): given that the free variables of both inputs `S`
and `T` already live in the type context `Λ`, the union encoding advances
`freshvarsc`, only grows `usedVars`, keeps `keys ⊆ usedVars`, preserves source
variables, and the encoded term's free variables stay within the final context.
Proved by cases on the cast path. -/
theorem castUnionAux_state
    {α β : SMTType} (c : α ~> β) (S T : SMT.Term) {Λ : SMT.TypeContext} {n : ℕ}
    {used : List SMT.𝒱} :
    ⦃ fun (⟨E, Λ'⟩ : EncoderState) ↦
        ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ AList.keys Λ ⊆ E.usedVars ∧ E.usedVars = used ∧
          SMT.fv S ⊆ AList.keys Λ ∧ SMT.fv T ⊆ AList.keys Λ⌝ ⦄
    castUnionAux S T c
    ⦃ ⇓? (⟨t', _σ⟩ : SMT.Term × SMTType) (⟨E', Γ'⟩ : EncoderState) => ⌜
      n ≤ E'.freshvarsc ∧
      Λ ⊆ Γ' ∧
      used ⊆ E'.usedVars ∧
      AList.keys Γ' ⊆ E'.usedVars ∧
      SMT.fv t' ⊆ AList.keys Γ' ∧
      (∀ v ∈ used, v ∉ Λ → v ∉ Γ') ⌝⦄ := by
  cases c with
  | @graph α β α' β' c_α c_β =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl, hS_fv, hT_fv⟩ := pre
    unfold castUnionAux castUnion.graph
    mspec loosenAux_prf_state
    mrename_i pre
    mintro ∀St₁
    rename_i S!_pair
    obtain ⟨S!, S!_spec⟩ := S!_pair
    mpure pre
    obtain ⟨S!_le, S!_Λ_sub, S!_fresh, S!_not_used, S!_used_sub,
      S!_keys_sub, S!_preserves, S!_fv_sub⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, hd1_fvc, hd1_used, hd1_types⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨_, _, hs1_fvc, hs1_used, hs1_types⟩ := pres
    mspec SMT.freshVar_spec
    mrename_i pre
    mintro ∀St₂
    mpure pre
    obtain ⟨St₂_types_eq, x_fresh, St₂_fvc, St₂_used_eq, x_not_used⟩ := pre
    mspec Std.Do.Spec.pure
    mpure_intro
    rename_i x
    rw [hs1_types, hd1_types] at St₂_types_eq x_fresh
    rw [hs1_used, hd1_used] at St₂_used_eq x_not_used
    rw [hs1_fvc, hd1_fvc] at St₂_fvc
    have S!_in : S! ∈ AList.keys St₁.types :=
      AList.mem_keys.mp (AList.mem_of_subset S!_Λ_sub (AList.mem_insert _ |>.mpr (Or.inl rfl)))
    and_intros
    · omega
    · refine AList.subset_trans (AList.subset_trans ?_ S!_Λ_sub) ?_
      · exact SMT.TypeContext.entries_subset_insert_of_notMem S!_fresh
      · rw [St₂_types_eq]
        exact SMT.TypeContext.entries_subset_insert_of_notMem x_fresh
    · intro v hv
      rw [St₂_used_eq]
      exact List.mem_cons_of_mem _ (S!_used_sub hv)
    · rw [St₂_types_eq, St₂_used_eq]
      exact keys_insert_subset_cons S!_keys_sub
    · intro v hv
      simp only [SMT.fv, List.mem_removeAll_iff, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hv
      obtain ⟨hv_body, hv_ne_x⟩ := hv
      rw [St₂_types_eq, ← AList.mem_keys, AList.mem_insert]
      refine Or.inr ?_
      rcases hv_body with (hvS! | hvx) | (hvT | hvx)
      · exact hvS! ▸ AList.mem_keys.mpr S!_in
      · exact absurd hvx hv_ne_x
      · exact AList.mem_keys.mpr (AList.mem_of_subset S!_Λ_sub
          (AList.mem_insert _ |>.mpr (Or.inr (AList.mem_keys.mpr (hT_fv hvT)))))
      · exact absurd hvx hv_ne_x
    · intro v hv hΛ
      rw [St₂_types_eq]
      intro hv_in
      rw [AList.mem_insert] at hv_in
      rcases hv_in with rfl | hv_in
      · exact x_not_used (S!_used_sub hv)
      · exact S!_preserves v hv hΛ hv_in
  | @«fun» α β α' β' hβ c_α c_β =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl, hS_fv, hT_fv⟩ := pre
    unfold castUnionAux castUnion.fun
    mspec loosenAux_prf_state
    mrename_i pre
    mintro ∀St₁
    rename_i S!_pair
    obtain ⟨S!, S!_spec⟩ := S!_pair
    mpure pre
    obtain ⟨S!_le, S!_Λ_sub, S!_fresh, S!_not_used, S!_used_sub,
      S!_keys_sub, S!_preserves, S!_fv_sub⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, hd1_fvc, hd1_used, hd1_types⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨_, _, hs1_fvc, hs1_used, hs1_types⟩ := pres
    split
    · mspec SMT.freshVar_spec
      mrename_i pre
      mintro ∀St₂
      mpure pre
      obtain ⟨St₂_types_eq, x_fresh, St₂_fvc, St₂_used_eq, x_not_used⟩ := pre
      mspec Std.Do.Spec.pure
      mpure_intro
      rename_i σ x
      rw [hs1_types, hd1_types] at St₂_types_eq x_fresh
      rw [hs1_used, hd1_used] at St₂_used_eq x_not_used
      rw [hs1_fvc, hd1_fvc] at St₂_fvc
      have S!_in : S! ∈ AList.keys St₁.types :=
        AList.mem_keys.mp (AList.mem_of_subset S!_Λ_sub (AList.mem_insert _ |>.mpr (Or.inl rfl)))
      and_intros
      · omega
      · refine AList.subset_trans (AList.subset_trans ?_ S!_Λ_sub) ?_
        · exact SMT.TypeContext.entries_subset_insert_of_notMem S!_fresh
        · rw [St₂_types_eq]
          exact SMT.TypeContext.entries_subset_insert_of_notMem x_fresh
      · intro v hv
        rw [St₂_used_eq]
        exact List.mem_cons_of_mem _ (S!_used_sub hv)
      · rw [St₂_types_eq, St₂_used_eq]
        exact keys_insert_subset_cons S!_keys_sub
      · intro v hv
        simp only [SMT.fv, List.mem_removeAll_iff, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false] at hv
        obtain ⟨hv_body, hv_ne_x⟩ := hv
        rw [St₂_types_eq, ← AList.mem_keys, AList.mem_insert]
        refine Or.inr ?_
        rcases hv_body with ((hvS! | hvxa) | hvxa') | ((hvT | hvxb) | hvxb')
        · exact hvS! ▸ AList.mem_keys.mpr S!_in
        · exact absurd hvxa hv_ne_x
        · exact absurd hvxa' hv_ne_x
        · exact AList.mem_keys.mpr (AList.mem_of_subset S!_Λ_sub
            (AList.mem_insert _ |>.mpr (Or.inr (AList.mem_keys.mpr (hT_fv hvT)))))
        · exact absurd hvxb hv_ne_x
        · exact absurd hvxb' hv_ne_x
      · intro v hv hΛ
        rw [St₂_types_eq]
        intro hv_in
        rw [AList.mem_insert] at hv_in
        rcases hv_in with rfl | hv_in
        · exact x_not_used (S!_used_sub hv)
        · exact S!_preserves v hv hΛ hv_in
    · mvcgen
  | @chpred α α' c_α =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl, hS_fv, hT_fv⟩ := pre
    unfold castUnionAux castUnion.chpred
    mspec loosenAux_prf_state
    mrename_i pre
    mintro ∀St₁
    rename_i S!_pair
    obtain ⟨S!, S!_spec⟩ := S!_pair
    mpure pre
    obtain ⟨S!_le, S!_Λ_sub, S!_fresh, S!_not_used, S!_used_sub,
      S!_keys_sub, S!_preserves, S!_fv_sub⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, hd1_fvc, hd1_used, hd1_types⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨_, _, hs1_fvc, hs1_used, hs1_types⟩ := pres
    mspec SMT.freshVar_spec
    mrename_i pre
    mintro ∀St₂
    mpure pre
    obtain ⟨St₂_types_eq, x_fresh, St₂_fvc, St₂_used_eq, x_not_used⟩ := pre
    mspec Std.Do.Spec.pure
    mpure_intro
    rename_i x
    rw [hs1_types, hd1_types] at St₂_types_eq x_fresh
    rw [hs1_used, hd1_used] at St₂_used_eq x_not_used
    rw [hs1_fvc, hd1_fvc] at St₂_fvc
    have S!_in : S! ∈ AList.keys St₁.types :=
      AList.mem_keys.mp (AList.mem_of_subset S!_Λ_sub (AList.mem_insert _ |>.mpr (Or.inl rfl)))
    and_intros
    · omega
    · refine AList.subset_trans (AList.subset_trans ?_ S!_Λ_sub) ?_
      · exact SMT.TypeContext.entries_subset_insert_of_notMem S!_fresh
      · rw [St₂_types_eq]
        exact SMT.TypeContext.entries_subset_insert_of_notMem x_fresh
    · intro v hv
      rw [St₂_used_eq]
      exact List.mem_cons_of_mem _ (S!_used_sub hv)
    · rw [St₂_types_eq, St₂_used_eq]
      exact keys_insert_subset_cons S!_keys_sub
    · intro v hv
      simp only [SMT.fv, List.mem_removeAll_iff, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hv
      obtain ⟨hv_body, hv_ne_x⟩ := hv
      rw [St₂_types_eq, ← AList.mem_keys, AList.mem_insert]
      refine Or.inr ?_
      rcases hv_body with (hvS! | hvx) | (hvT | hvx)
      · exact hvS! ▸ AList.mem_keys.mpr S!_in
      · exact absurd hvx hv_ne_x
      · exact AList.mem_keys.mpr (AList.mem_of_subset S!_Λ_sub
          (AList.mem_insert _ |>.mpr (Or.inr (AList.mem_keys.mpr (hT_fv hvT)))))
      · exact absurd hvx hv_ne_x
    · intro v hv hΛ
      rw [St₂_types_eq]
      intro hv_in
      rw [AList.mem_insert] at hv_in
      rcases hv_in with rfl | hv_in
      · exact x_not_used (S!_used_sub hv)
      · exact S!_preserves v hv hΛ hv_in
  | @opt α α' c_α =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl, hS_fv, hT_fv⟩ := pre
    unfold castUnionAux
    mvcgen
  | @pair α β α' β' c_α c_β =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl, hS_fv, hT_fv⟩ := pre
    unfold castUnionAux
    mvcgen
  | @refl α hα =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl, hS_fv, hT_fv⟩ := pre
    unfold castUnionAux
    mvcgen

set_option maxHeartbeats 4000000 in
/-- Purely structural specification of `castInterAux` (no `B`-typing, no
`respects`, no denotation): given that the free variables of both inputs `S`
and `T` already live in the type context `Λ`, the intersection encoding advances
`freshvarsc`, only grows `usedVars`, keeps `keys ⊆ usedVars`, preserves source
variables, and the encoded term's free variables stay within the final context.
Proved by cases on the cast path. -/
theorem castInterAux_state
    {α β : SMTType} (c : α ~> β) (S T : SMT.Term) {Λ : SMT.TypeContext} {n : ℕ}
    {used : List SMT.𝒱} :
    ⦃ fun (⟨E, Λ'⟩ : EncoderState) ↦
        ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ AList.keys Λ ⊆ E.usedVars ∧ E.usedVars = used ∧
          SMT.fv S ⊆ AList.keys Λ ∧ SMT.fv T ⊆ AList.keys Λ⌝ ⦄
    castInterAux S T c
    ⦃ ⇓? (⟨t', _σ⟩ : SMT.Term × SMTType) (⟨E', Γ'⟩ : EncoderState) => ⌜
      n ≤ E'.freshvarsc ∧
      Λ ⊆ Γ' ∧
      used ⊆ E'.usedVars ∧
      AList.keys Γ' ⊆ E'.usedVars ∧
      SMT.fv t' ⊆ AList.keys Γ' ∧
      (∀ v ∈ used, v ∉ Λ → v ∉ Γ') ⌝⦄ := by
  cases c with
  | @graph α β α' β' c_α c_β =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl, hS_fv, hT_fv⟩ := pre
    unfold castInterAux
    mspec loosenAux_prf_state
    mrename_i pre
    mintro ∀St₁
    rename_i S!_pair
    obtain ⟨S!, S!_spec⟩ := S!_pair
    mpure pre
    obtain ⟨S!_le, S!_Λ_sub, S!_fresh, S!_not_used, S!_used_sub,
      S!_keys_sub, S!_preserves, S!_fv_sub⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, hd1_fvc, hd1_used, hd1_types⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨_, _, hs1_fvc, hs1_used, hs1_types⟩ := pres
    mspec SMT.freshVar_spec
    mrename_i pre
    mintro ∀St₂
    mpure pre
    obtain ⟨St₂_types_eq, x_fresh, St₂_fvc, St₂_used_eq, x_not_used⟩ := pre
    mspec Std.Do.Spec.pure
    mpure_intro
    rename_i x
    rw [hs1_types, hd1_types] at St₂_types_eq x_fresh
    rw [hs1_used, hd1_used] at St₂_used_eq x_not_used
    rw [hs1_fvc, hd1_fvc] at St₂_fvc
    have S!_in : S! ∈ AList.keys St₁.types :=
      AList.mem_keys.mp (AList.mem_of_subset S!_Λ_sub (AList.mem_insert _ |>.mpr (Or.inl rfl)))
    and_intros
    · omega
    · refine AList.subset_trans (AList.subset_trans ?_ S!_Λ_sub) ?_
      · exact SMT.TypeContext.entries_subset_insert_of_notMem S!_fresh
      · rw [St₂_types_eq]
        exact SMT.TypeContext.entries_subset_insert_of_notMem x_fresh
    · intro v hv
      rw [St₂_used_eq]
      exact List.mem_cons_of_mem _ (S!_used_sub hv)
    · rw [St₂_types_eq, St₂_used_eq]
      exact keys_insert_subset_cons S!_keys_sub
    · intro v hv
      simp only [SMT.fv, List.mem_removeAll_iff, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hv
      obtain ⟨hv_body, hv_ne_x⟩ := hv
      rw [St₂_types_eq, ← AList.mem_keys, AList.mem_insert]
      refine Or.inr ?_
      rcases hv_body with (hvS! | hvx) | (hvT | hvx)
      · exact hvS! ▸ AList.mem_keys.mpr S!_in
      · exact absurd hvx hv_ne_x
      · exact AList.mem_keys.mpr (AList.mem_of_subset S!_Λ_sub
          (AList.mem_insert _ |>.mpr (Or.inr (AList.mem_keys.mpr (hT_fv hvT)))))
      · exact absurd hvx hv_ne_x
    · intro v hv hΛ
      rw [St₂_types_eq]
      intro hv_in
      rw [AList.mem_insert] at hv_in
      rcases hv_in with rfl | hv_in
      · exact x_not_used (S!_used_sub hv)
      · exact S!_preserves v hv hΛ hv_in
  | @«fun» α β α' β' hβ c_α c_β =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl, hS_fv, hT_fv⟩ := pre
    unfold castInterAux
    mspec loosenAux_prf_state
    mrename_i pre
    mintro ∀St₁
    rename_i S!_pair
    obtain ⟨S!, S!_spec⟩ := S!_pair
    mpure pre
    obtain ⟨S!_le, S!_Λ_sub, S!_fresh, S!_not_used, S!_used_sub,
      S!_keys_sub, S!_preserves, S!_fv_sub⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, hd1_fvc, hd1_used, hd1_types⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨_, _, hs1_fvc, hs1_used, hs1_types⟩ := pres
    split
    · mspec SMT.freshVar_spec
      mrename_i pre
      mintro ∀St₂
      mpure pre
      obtain ⟨St₂_types_eq, x_fresh, St₂_fvc, St₂_used_eq, x_not_used⟩ := pre
      mspec Std.Do.Spec.pure
      mpure_intro
      rename_i σ x
      rw [hs1_types, hd1_types] at St₂_types_eq x_fresh
      rw [hs1_used, hd1_used] at St₂_used_eq x_not_used
      rw [hs1_fvc, hd1_fvc] at St₂_fvc
      have S!_in : S! ∈ AList.keys St₁.types :=
        AList.mem_keys.mp (AList.mem_of_subset S!_Λ_sub (AList.mem_insert _ |>.mpr (Or.inl rfl)))
      and_intros
      · omega
      · refine AList.subset_trans (AList.subset_trans ?_ S!_Λ_sub) ?_
        · exact SMT.TypeContext.entries_subset_insert_of_notMem S!_fresh
        · rw [St₂_types_eq]
          exact SMT.TypeContext.entries_subset_insert_of_notMem x_fresh
      · intro v hv
        rw [St₂_used_eq]
        exact List.mem_cons_of_mem _ (S!_used_sub hv)
      · rw [St₂_types_eq, St₂_used_eq]
        exact keys_insert_subset_cons S!_keys_sub
      · intro v hv
        simp only [SMT.fv, List.mem_removeAll_iff, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false] at hv
        obtain ⟨hv_body, hv_ne_x⟩ := hv
        rw [St₂_types_eq, ← AList.mem_keys, AList.mem_insert]
        refine Or.inr ?_
        rcases hv_body with ((hvS! | hvxa) | hvxa') | ((hvT | hvxb) | hvxb')
        · exact hvS! ▸ AList.mem_keys.mpr S!_in
        · exact absurd hvxa hv_ne_x
        · exact absurd hvxa' hv_ne_x
        · exact AList.mem_keys.mpr (AList.mem_of_subset S!_Λ_sub
            (AList.mem_insert _ |>.mpr (Or.inr (AList.mem_keys.mpr (hT_fv hvT)))))
        · exact absurd hvxb hv_ne_x
        · exact absurd hvxb' hv_ne_x
      · intro v hv hΛ
        rw [St₂_types_eq]
        intro hv_in
        rw [AList.mem_insert] at hv_in
        rcases hv_in with rfl | hv_in
        · exact x_not_used (S!_used_sub hv)
        · exact S!_preserves v hv hΛ hv_in
    · mvcgen
  | @chpred α α' c_α =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl, hS_fv, hT_fv⟩ := pre
    unfold castInterAux
    mspec loosenAux_prf_state
    mrename_i pre
    mintro ∀St₁
    rename_i S!_pair
    obtain ⟨S!, S!_spec⟩ := S!_pair
    mpure pre
    obtain ⟨S!_le, S!_Λ_sub, S!_fresh, S!_not_used, S!_used_sub,
      S!_keys_sub, S!_preserves, S!_fv_sub⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, hd1_fvc, hd1_used, hd1_types⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨_, _, hs1_fvc, hs1_used, hs1_types⟩ := pres
    mspec SMT.freshVar_spec
    mrename_i pre
    mintro ∀St₂
    mpure pre
    obtain ⟨St₂_types_eq, x_fresh, St₂_fvc, St₂_used_eq, x_not_used⟩ := pre
    mspec Std.Do.Spec.pure
    mpure_intro
    rename_i x
    rw [hs1_types, hd1_types] at St₂_types_eq x_fresh
    rw [hs1_used, hd1_used] at St₂_used_eq x_not_used
    rw [hs1_fvc, hd1_fvc] at St₂_fvc
    have S!_in : S! ∈ AList.keys St₁.types :=
      AList.mem_keys.mp (AList.mem_of_subset S!_Λ_sub (AList.mem_insert _ |>.mpr (Or.inl rfl)))
    and_intros
    · omega
    · refine AList.subset_trans (AList.subset_trans ?_ S!_Λ_sub) ?_
      · exact SMT.TypeContext.entries_subset_insert_of_notMem S!_fresh
      · rw [St₂_types_eq]
        exact SMT.TypeContext.entries_subset_insert_of_notMem x_fresh
    · intro v hv
      rw [St₂_used_eq]
      exact List.mem_cons_of_mem _ (S!_used_sub hv)
    · rw [St₂_types_eq, St₂_used_eq]
      exact keys_insert_subset_cons S!_keys_sub
    · intro v hv
      simp only [SMT.fv, List.mem_removeAll_iff, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hv
      obtain ⟨hv_body, hv_ne_x⟩ := hv
      rw [St₂_types_eq, ← AList.mem_keys, AList.mem_insert]
      refine Or.inr ?_
      rcases hv_body with (hvS! | hvx) | (hvT | hvx)
      · exact hvS! ▸ AList.mem_keys.mpr S!_in
      · exact absurd hvx hv_ne_x
      · exact AList.mem_keys.mpr (AList.mem_of_subset S!_Λ_sub
          (AList.mem_insert _ |>.mpr (Or.inr (AList.mem_keys.mpr (hT_fv hvT)))))
      · exact absurd hvx hv_ne_x
    · intro v hv hΛ
      rw [St₂_types_eq]
      intro hv_in
      rw [AList.mem_insert] at hv_in
      rcases hv_in with rfl | hv_in
      · exact x_not_used (S!_used_sub hv)
      · exact S!_preserves v hv hΛ hv_in
  | @opt α α' c_α =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl, hS_fv, hT_fv⟩ := pre
    unfold castInterAux
    mvcgen
  | @pair α β α' β' c_α c_β =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl, hS_fv, hT_fv⟩ := pre
    unfold castInterAux
    mvcgen
  | @refl α hα =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl, hS_fv, hT_fv⟩ := pre
    unfold castInterAux
    mvcgen

set_option maxHeartbeats 4000000 in
/-- Structural postcondition of `encodeTerm` (no `«Δ»`, no `respects`, no
`B`-typing, no denotation): state monotonicity, key coverage, source-FV
coverage, encoded-term FV coverage, and variable preservation. -/
theorem encodeTerm_state
    (E : B.Env) {Λ : SMT.TypeContext} {t : B.Term}
    {used : List SMT.𝒱}
    (vars_used : ∀ v ∈ t.vars, v ∈ used)
    (bv_nodup : (B.bv t).Nodup)
    {n : ℕ} :
    ⦃ fun (⟨E0, Λ'⟩ : EncoderState) ↦
        ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used⌝ ⦄
    encodeTerm t E
    ⦃ ⇓? (⟨t', _σ⟩ : SMT.Term × SMTType) (⟨E', Γ'⟩ : EncoderState) => ⌜
      used ⊆ E'.usedVars ∧
      Λ ⊆ Γ' ∧
      AList.keys Γ' ⊆ E'.usedVars ∧
      B.CoversUsedVars E'.usedVars t ∧
      SMT.fv t' ⊆ AList.keys Γ' ∧
      (∀ v ∈ used, v ∉ Λ → v ∉ B.Term.vars t → v ∉ Γ') ⌝⦄ := by
  induction t generalizing E n used Λ with
  | int i =>
    mstart
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
    rw [encodeTerm]
    mspec Std.Do.Spec.pure
    mpure_intro
    and_intros
    · intro v hv; simpa [St_used_eq] using hv
    · intro v hv; simpa using hv
    · intro v hv; simpa [St_used_eq] using St_sub hv
    · intro v hv; simp [B.fv] at hv
    · intro v hv; simp [SMT.fv] at hv
    · exact fun _ _ h _ => h
  | bool b =>
    mstart
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
    rw [encodeTerm]
    mspec Std.Do.Spec.pure
    mpure_intro
    and_intros
    · intro v hv; simpa [St_used_eq] using hv
    · intro v hv; simpa using hv
    · intro v hv; simpa [St_used_eq] using St_sub hv
    · intro v hv; simp [B.fv] at hv
    · intro v hv; simp [SMT.fv] at hv
    · exact fun _ _ h _ => h
  | var v =>
    mstart
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
    rw [encodeTerm]
    mvcgen
    case vc1 τ τ_lookup =>
      have hv_in_types : v ∈ St.types :=
        AList.lookup_isSome.1 (Option.isSome_of_eq_some τ_lookup)
      and_intros
      · intro x hx; simpa [St_used_eq] using hx
      · intro x hx; simpa using hx
      · intro x hx; simpa [St_used_eq] using St_sub hx
      · intro x hx
        rw [B.fv, List.mem_singleton] at hx
        subst x
        simpa [St_used_eq] using (St_sub (AList.mem_keys.mpr hv_in_types))
      · intro x hx
        rw [SMT.fv, List.mem_singleton] at hx
        subst x
        exact AList.mem_keys.mpr hv_in_types
      · exact fun _ _ h _ => h
  | «ℤ» =>
    mstart
    mintro pre ∀S
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
    rw [encodeTerm]
    mspec Std.Do.Spec.get_StateT
    mspec freshVar_spec (used := S.env.usedVars)
    case post.success 𝓋 =>
      mrename_i pre
      mintro ∀S'
      mpure pre
      obtain ⟨types_eq, 𝓋_notMem, freshvarsc_eq, used_eq, 𝓋_neq_used⟩ := pre
      mspec Std.Do.Spec.modifyGet_StateT
      mspec Std.Do.Spec.pure
      mpure_intro
      and_intros
      · intro x hx; rw [used_eq, St_used_eq]; exact List.mem_cons_of_mem _ hx
      · exact fun _ => id
      · rw [used_eq]; intro x hx; exact List.mem_cons_of_mem _ (St_sub hx)
      · intro x hx; rw [B.fv] at hx; contradiction
      · intro x hx; simp only [SMT.fv, List.mem_removeAll_iff] at hx; nomatch hx.1
      · exact fun _ _ h _ => h
  | 𝔹 =>
    mstart
    mintro pre ∀S
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
    rw [encodeTerm]
    mspec Std.Do.Spec.get_StateT
    mspec freshVar_spec (used := S.env.usedVars)
    case post.success 𝓋 =>
      mrename_i pre
      mintro ∀S'
      mpure pre
      obtain ⟨types_eq, 𝓋_notMem, freshvarsc_eq, used_eq, 𝓋_neq_used⟩ := pre
      mspec Std.Do.Spec.modifyGet_StateT
      mspec Std.Do.Spec.pure
      mpure_intro
      and_intros
      · intro x hx; rw [used_eq, St_used_eq]; exact List.mem_cons_of_mem _ hx
      · exact fun _ => id
      · rw [used_eq]; intro x hx; exact List.mem_cons_of_mem _ (St_sub hx)
      · intro x hx; rw [B.fv] at hx; contradiction
      · intro x hx; simp only [SMT.fv, List.mem_removeAll_iff] at hx; nomatch hx.1
      · exact fun _ _ h _ => h
  | maplet x y x_ih y_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
    rw [encodeTerm]
    have hx_bv_nodup : (B.bv x).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.1
    have hy_bv_nodup : (B.bv y).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.2.1
    have vars_used_x : ∀ v ∈ x.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h)
    have vars_used_y : ∀ v ∈ y.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inr h)
    mspec x_ih (E := E) (Λ := σ.types) vars_used_x hx_bv_nodup
    clear x_ih
    rename_i out_x
    obtain ⟨x_enc, σx⟩ := out_x
    mrename_i pre
    mintro ∀σ_x
    mpure pre
    obtain ⟨x_used_sub, x_Λ_sub, x_keys_sub, x_cov, x_fv_sub, x_preserves⟩ := pre
    mspec y_ih (E := E) (Λ := σ_x.types) (used := σ_x.env.usedVars)
      (fun v hv => x_used_sub (vars_used_y v hv)) hy_bv_nodup
    clear y_ih
    rename_i out_y
    obtain ⟨y_enc, σy⟩ := out_y
    mrename_i pre
    mintro ∀σ_y
    mpure pre
    obtain ⟨y_used_sub, y_Λ_sub, y_keys_sub, y_cov, y_fv_sub, y_preserves⟩ := pre
    mpure_intro
    and_intros
    · exact fun v hv => y_used_sub (x_used_sub hv)
    · exact AList.subset_trans x_Λ_sub y_Λ_sub
    · exact y_keys_sub
    · intro v hv
      rw [B.fv, List.mem_append] at hv
      rcases hv with hv | hv
      · exact y_used_sub (x_cov v hv)
      · exact y_cov v hv
    · intro v hv
      rw [SMT.fv, List.mem_append] at hv
      rcases hv with hv | hv
      · exact AList.mem_keys.mpr (AList.mem_of_subset y_Λ_sub (AList.mem_keys.mp (x_fv_sub hv)))
      · exact y_fv_sub hv
    · intro v hv hΛ hvars
      have hvx : v ∉ B.Term.vars x := fun h => hvars (by
        simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
        rcases h with h | h <;> [left; right] <;> exact .inl h)
      have hvy : v ∉ B.Term.vars y := fun h => hvars (by
        simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
        rcases h with h | h <;> [left; right] <;> exact .inr h)
      exact y_preserves v (x_used_sub hv) (x_preserves v hv hΛ hvx) hvy
  | add x y x_ih y_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
    rw [encodeTerm]
    have hx_bv_nodup : (B.bv x).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.1
    have hy_bv_nodup : (B.bv y).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.2.1
    have vars_used_x : ∀ v ∈ x.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h)
    have vars_used_y : ∀ v ∈ y.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inr h)
    mspec x_ih (E := E) (Λ := σ.types) vars_used_x hx_bv_nodup
    rename_i out_x
    obtain ⟨x_enc, σx⟩ := out_x
    mrename_i prex
    mintro ∀σ_x
    mpure prex
    obtain ⟨x_used_sub, x_Λ_sub, x_keys_sub, x_cov, x_fv_sub, x_preserves⟩ := prex
    split
    · rename_i heq
      injection heq with hxe hσe
      subst hσe
      subst hxe
      mspec y_ih (E := E) (Λ := σ_x.types) (used := σ_x.env.usedVars)
        (fun v hv => x_used_sub (vars_used_y v hv)) hy_bv_nodup
      rename_i out_y
      obtain ⟨y_enc, σy⟩ := out_y
      mrename_i prey
      mintro ∀σ_y
      mpure prey
      obtain ⟨y_used_sub, y_Λ_sub, y_keys_sub, y_cov, y_fv_sub, y_preserves⟩ := prey
      split
      · rename_i heq2
        injection heq2 with hye hσe2
        subst hσe2
        subst hye
        mspec Std.Do.Spec.pure
        mpure_intro
        and_intros
        · exact fun v hv => y_used_sub (x_used_sub hv)
        · exact AList.subset_trans x_Λ_sub y_Λ_sub
        · exact y_keys_sub
        · intro v hv
          rw [B.fv, List.mem_append] at hv
          rcases hv with hv | hv
          · exact y_used_sub (x_cov v hv)
          · exact y_cov v hv
        · intro v hv
          rw [SMT.fv, List.mem_append] at hv
          rcases hv with hv | hv
          · exact AList.mem_keys.mpr
              (AList.mem_of_subset y_Λ_sub (AList.mem_keys.mp (x_fv_sub hv)))
          · exact y_fv_sub hv
        · intro v hv hΛ hvars
          have hvx : v ∉ B.Term.vars x := fun h => hvars (by
            simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
            rcases h with h | h <;> [left; right] <;> exact .inl h)
          have hvy : v ∉ B.Term.vars y := fun h => hvars (by
            simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
            rcases h with h | h <;> [left; right] <;> exact .inr h)
          exact y_preserves v (x_used_sub hv) (x_preserves v hv hΛ hvx) hvy
      · mspec y_ih (E := E) (Λ := σ_y.types) (used := σ_y.env.usedVars)
          (fun v hv => y_used_sub (x_used_sub (vars_used_y v hv))) hy_bv_nodup
        mvcgen
    · mspec x_ih (E := E) (Λ := σ_x.types) (used := σ_x.env.usedVars)
        (fun v hv => x_used_sub (vars_used_x v hv)) hx_bv_nodup
      mvcgen
  | sub x y x_ih y_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
    rw [encodeTerm]
    have hx_bv_nodup : (B.bv x).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.1
    have hy_bv_nodup : (B.bv y).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.2.1
    have vars_used_x : ∀ v ∈ x.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h)
    have vars_used_y : ∀ v ∈ y.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inr h)
    mspec x_ih (E := E) (Λ := σ.types) vars_used_x hx_bv_nodup
    rename_i out_x
    obtain ⟨x_enc, σx⟩ := out_x
    mrename_i prex
    mintro ∀σ_x
    mpure prex
    obtain ⟨x_used_sub, x_Λ_sub, x_keys_sub, x_cov, x_fv_sub, x_preserves⟩ := prex
    split
    · rename_i heq
      injection heq with hxe hσe
      subst hσe
      subst hxe
      mspec y_ih (E := E) (Λ := σ_x.types) (used := σ_x.env.usedVars)
        (fun v hv => x_used_sub (vars_used_y v hv)) hy_bv_nodup
      rename_i out_y
      obtain ⟨y_enc, σy⟩ := out_y
      mrename_i prey
      mintro ∀σ_y
      mpure prey
      obtain ⟨y_used_sub, y_Λ_sub, y_keys_sub, y_cov, y_fv_sub, y_preserves⟩ := prey
      split
      · rename_i heq2
        injection heq2 with hye hσe2
        subst hσe2
        subst hye
        mspec Std.Do.Spec.pure
        mpure_intro
        and_intros
        · exact fun v hv => y_used_sub (x_used_sub hv)
        · exact AList.subset_trans x_Λ_sub y_Λ_sub
        · exact y_keys_sub
        · intro v hv
          rw [B.fv, List.mem_append] at hv
          rcases hv with hv | hv
          · exact y_used_sub (x_cov v hv)
          · exact y_cov v hv
        · intro v hv
          rw [SMT.fv, List.mem_append] at hv
          rcases hv with hv | hv
          · exact AList.mem_keys.mpr
              (AList.mem_of_subset y_Λ_sub (AList.mem_keys.mp (x_fv_sub hv)))
          · exact y_fv_sub hv
        · intro v hv hΛ hvars
          have hvx : v ∉ B.Term.vars x := fun h => hvars (by
            simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
            rcases h with h | h <;> [left; right] <;> exact .inl h)
          have hvy : v ∉ B.Term.vars y := fun h => hvars (by
            simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
            rcases h with h | h <;> [left; right] <;> exact .inr h)
          exact y_preserves v (x_used_sub hv) (x_preserves v hv hΛ hvx) hvy
      · mspec y_ih (E := E) (Λ := σ_y.types) (used := σ_y.env.usedVars)
          (fun v hv => y_used_sub (x_used_sub (vars_used_y v hv))) hy_bv_nodup
        mvcgen
    · mspec x_ih (E := E) (Λ := σ_x.types) (used := σ_x.env.usedVars)
        (fun v hv => x_used_sub (vars_used_x v hv)) hx_bv_nodup
      mvcgen
  | mul x y x_ih y_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
    rw [encodeTerm]
    have hx_bv_nodup : (B.bv x).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.1
    have hy_bv_nodup : (B.bv y).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.2.1
    have vars_used_x : ∀ v ∈ x.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h)
    have vars_used_y : ∀ v ∈ y.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inr h)
    mspec x_ih (E := E) (Λ := σ.types) vars_used_x hx_bv_nodup
    rename_i out_x
    obtain ⟨x_enc, σx⟩ := out_x
    mrename_i prex
    mintro ∀σ_x
    mpure prex
    obtain ⟨x_used_sub, x_Λ_sub, x_keys_sub, x_cov, x_fv_sub, x_preserves⟩ := prex
    split
    · rename_i heq
      injection heq with hxe hσe
      subst hσe
      subst hxe
      mspec y_ih (E := E) (Λ := σ_x.types) (used := σ_x.env.usedVars)
        (fun v hv => x_used_sub (vars_used_y v hv)) hy_bv_nodup
      rename_i out_y
      obtain ⟨y_enc, σy⟩ := out_y
      mrename_i prey
      mintro ∀σ_y
      mpure prey
      obtain ⟨y_used_sub, y_Λ_sub, y_keys_sub, y_cov, y_fv_sub, y_preserves⟩ := prey
      split
      · rename_i heq2
        injection heq2 with hye hσe2
        subst hσe2
        subst hye
        mspec Std.Do.Spec.pure
        mpure_intro
        and_intros
        · exact fun v hv => y_used_sub (x_used_sub hv)
        · exact AList.subset_trans x_Λ_sub y_Λ_sub
        · exact y_keys_sub
        · intro v hv
          rw [B.fv, List.mem_append] at hv
          rcases hv with hv | hv
          · exact y_used_sub (x_cov v hv)
          · exact y_cov v hv
        · intro v hv
          rw [SMT.fv, List.mem_append] at hv
          rcases hv with hv | hv
          · exact AList.mem_keys.mpr
              (AList.mem_of_subset y_Λ_sub (AList.mem_keys.mp (x_fv_sub hv)))
          · exact y_fv_sub hv
        · intro v hv hΛ hvars
          have hvx : v ∉ B.Term.vars x := fun h => hvars (by
            simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
            rcases h with h | h <;> [left; right] <;> exact .inl h)
          have hvy : v ∉ B.Term.vars y := fun h => hvars (by
            simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
            rcases h with h | h <;> [left; right] <;> exact .inr h)
          exact y_preserves v (x_used_sub hv) (x_preserves v hv hΛ hvx) hvy
      · mspec y_ih (E := E) (Λ := σ_y.types) (used := σ_y.env.usedVars)
          (fun v hv => y_used_sub (x_used_sub (vars_used_y v hv))) hy_bv_nodup
        mvcgen
    · mspec x_ih (E := E) (Λ := σ_x.types) (used := σ_x.env.usedVars)
        (fun v hv => x_used_sub (vars_used_x v hv)) hx_bv_nodup
      mvcgen
  | le x y x_ih y_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
    rw [encodeTerm]
    have hx_bv_nodup : (B.bv x).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.1
    have hy_bv_nodup : (B.bv y).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.2.1
    have vars_used_x : ∀ v ∈ x.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h)
    have vars_used_y : ∀ v ∈ y.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inr h)
    mspec x_ih (E := E) (Λ := σ.types) vars_used_x hx_bv_nodup
    clear x_ih
    rename_i out_x
    obtain ⟨x_enc, σx⟩ := out_x
    mrename_i pre
    mintro ∀σ_x
    mpure pre
    obtain ⟨x_used_sub, x_Λ_sub, x_keys_sub, x_cov, x_fv_sub, x_preserves⟩ := pre
    mspec y_ih (E := E) (Λ := σ_x.types) (used := σ_x.env.usedVars)
      (fun v hv => x_used_sub (vars_used_y v hv)) hy_bv_nodup
    clear y_ih
    rename_i out_y
    obtain ⟨y_enc, σy⟩ := out_y
    mrename_i pre
    mintro ∀σ_y
    mpure pre
    obtain ⟨y_used_sub, y_Λ_sub, y_keys_sub, y_cov, y_fv_sub, y_preserves⟩ := pre
    mpure_intro
    and_intros
    · exact fun v hv => y_used_sub (x_used_sub hv)
    · exact AList.subset_trans x_Λ_sub y_Λ_sub
    · exact y_keys_sub
    · intro v hv
      rw [B.fv, List.mem_append] at hv
      rcases hv with hv | hv
      · exact y_used_sub (x_cov v hv)
      · exact y_cov v hv
    · intro v hv
      rw [SMT.fv, List.mem_append] at hv
      rcases hv with hv | hv
      · exact AList.mem_keys.mpr (AList.mem_of_subset y_Λ_sub (AList.mem_keys.mp (x_fv_sub hv)))
      · exact y_fv_sub hv
    · intro v hv hΛ hvars
      have hvx : v ∉ B.Term.vars x := fun h => hvars (by
        simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
        rcases h with h | h <;> [left; right] <;> exact .inl h)
      have hvy : v ∉ B.Term.vars y := fun h => hvars (by
        simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
        rcases h with h | h <;> [left; right] <;> exact .inr h)
      exact y_preserves v (x_used_sub hv) (x_preserves v hv hΛ hvx) hvy
  | min S _ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
    simp only [encodeTerm] <;> mvcgen
  | max S _ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
    simp only [encodeTerm] <;> mvcgen
  | card S _ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
    simp only [encodeTerm] <;> mvcgen
  | and x y x_ih y_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
    rw [encodeTerm]
    have hx_bv_nodup : (B.bv x).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.1
    have hy_bv_nodup : (B.bv y).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.2.1
    have vars_used_x : ∀ v ∈ x.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h)
    have vars_used_y : ∀ v ∈ y.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inr h)
    mspec x_ih (E := E) (Λ := σ.types) vars_used_x hx_bv_nodup
    rename_i out_x
    obtain ⟨x_enc, σx⟩ := out_x
    mrename_i prex
    mintro ∀σ_x
    mpure prex
    obtain ⟨x_used_sub, x_Λ_sub, x_keys_sub, x_cov, x_fv_sub, x_preserves⟩ := prex
    split
    · rename_i heq
      injection heq with hxe hσe
      subst hσe
      subst hxe
      mspec y_ih (E := E) (Λ := σ_x.types) (used := σ_x.env.usedVars)
        (fun v hv => x_used_sub (vars_used_y v hv)) hy_bv_nodup
      rename_i out_y
      obtain ⟨y_enc, σy⟩ := out_y
      mrename_i prey
      mintro ∀σ_y
      mpure prey
      obtain ⟨y_used_sub, y_Λ_sub, y_keys_sub, y_cov, y_fv_sub, y_preserves⟩ := prey
      split
      · rename_i heq2
        injection heq2 with hye hσe2
        subst hσe2
        subst hye
        mspec Std.Do.Spec.pure
        mpure_intro
        and_intros
        · exact fun v hv => y_used_sub (x_used_sub hv)
        · exact AList.subset_trans x_Λ_sub y_Λ_sub
        · exact y_keys_sub
        · intro v hv
          rw [B.fv, List.mem_append] at hv
          rcases hv with hv | hv
          · exact y_used_sub (x_cov v hv)
          · exact y_cov v hv
        · intro v hv
          rw [SMT.fv, List.mem_append] at hv
          rcases hv with hv | hv
          · exact AList.mem_keys.mpr
              (AList.mem_of_subset y_Λ_sub (AList.mem_keys.mp (x_fv_sub hv)))
          · exact y_fv_sub hv
        · intro v hv hΛ hvars
          have hvx : v ∉ B.Term.vars x := fun h => hvars (by
            simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
            rcases h with h | h <;> [left; right] <;> exact .inl h)
          have hvy : v ∉ B.Term.vars y := fun h => hvars (by
            simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
            rcases h with h | h <;> [left; right] <;> exact .inr h)
          exact y_preserves v (x_used_sub hv) (x_preserves v hv hΛ hvx) hvy
      · mspec y_ih (E := E) (Λ := σ_y.types) (used := σ_y.env.usedVars)
          (fun v hv => y_used_sub (x_used_sub (vars_used_y v hv))) hy_bv_nodup
        mvcgen
    · mspec x_ih (E := E) (Λ := σ_x.types) (used := σ_x.env.usedVars)
        (fun v hv => x_used_sub (vars_used_x v hv)) hx_bv_nodup
      mvcgen
  | not x ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
    rw [encodeTerm]
    have hx_bv_nodup : (B.bv x).Nodup := by simpa [B.bv] using bv_nodup
    have vars_used_x : ∀ v ∈ x.vars, v ∈ used := fun v hv => vars_used v (by
      simpa [B.Term.vars, B.fv, B.bv] using hv)
    mspec ih (E := E) (Λ := σ.types) vars_used_x hx_bv_nodup
    rename_i out_x
    obtain ⟨x_enc, σx⟩ := out_x
    mrename_i prex
    mintro ∀σ_x
    mpure prex
    obtain ⟨x_used_sub, x_Λ_sub, x_keys_sub, x_cov, x_fv_sub, x_preserves⟩ := prex
    split
    · rename_i heq
      injection heq with hxe hσe
      subst hσe
      subst hxe
      mspec Std.Do.Spec.pure
      mpure_intro
      and_intros
      · exact x_used_sub
      · exact x_Λ_sub
      · exact x_keys_sub
      · intro v hv; simp only [B.fv] at hv; exact x_cov v hv
      · intro v hv; simp only [SMT.fv] at hv; exact x_fv_sub hv
      · intro v hv hΛ hvars
        exact x_preserves v hv hΛ (fun h => hvars (by
          simpa [B.Term.vars, B.fv, B.bv] using h))
    · mspec ih (E := E) (Λ := σ_x.types) (used := σ_x.env.usedVars)
        (fun v hv => x_used_sub (vars_used_x v hv)) hx_bv_nodup
      mvcgen
  | pow S ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
    rw [encodeTerm]
    have hS_bv_nodup : (B.bv S).Nodup := by simpa [B.bv] using bv_nodup
    have vars_used_S : ∀ v ∈ S.vars, v ∈ used := fun v hv => vars_used v (by
      simpa [B.Term.vars, B.fv, B.bv] using hv)
    mspec ih (E := E) (Λ := σ.types) vars_used_S hS_bv_nodup
    rename_i out_S
    obtain ⟨S_enc, σS⟩ := out_S
    mrename_i preS
    mintro ∀σ_S
    mpure preS
    obtain ⟨S_used_sub, S_Λ_sub, S_keys_sub, S_cov, S_fv_sub, S_preserves⟩ := preS
    split
    · rename_i heq
      subst heq
      set ctx := σ_S.types with hctx
      mspec Std.Do.Spec.get_StateT
      mspec freshVar_spec (Γ := ctx) (used := σ_S.env.usedVars)
      case post.success x =>
        mrename_i pre
        mintro ∀St₁
        mpure pre
        obtain ⟨St₁_types_eq, x_fresh, St₁_fvc_eq, St₁_used_eq, x_not_used⟩ := pre
        mspec freshVar_spec (Γ := ctx.insert x _) (used := St₁.env.usedVars)
        case post.success ℰ =>
          mrename_i pre
          mintro ∀St₂
          mpure pre
          obtain ⟨St₂_types_eq, ℰ_fresh, St₂_fvc_eq, St₂_used_eq, ℰ_not_used⟩ := pre
          simp [modify]
          mspec Std.Do.Spec.modifyGet_StateT
          mpure_intro
          and_intros
          · intro v hv
            rw [St₂_used_eq, St₁_used_eq]
            exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (S_used_sub hv))
          · exact S_Λ_sub
          · intro v hv
            rw [St₂_used_eq, St₁_used_eq]
            exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (S_keys_sub hv))
          · intro v hv
            rw [B.fv] at hv
            rw [St₂_used_eq, St₁_used_eq]
            exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (S_cov v hv))
          · intro v hv
            simp only [SMT.fv, List.mem_removeAll_iff, List.mem_append,
              List.mem_cons, List.not_mem_nil, or_false] at hv
            obtain ⟨⟨hv1, hv_ne_x⟩, hv_ne_ℰ⟩ := hv
            rcases hv1 with (hvℰ | hvx) | hvS | hvx
            · exact absurd hvℰ hv_ne_ℰ
            · exact absurd hvx hv_ne_x
            · exact S_fv_sub hvS
            · exact absurd hvx hv_ne_x
          · intro v hv hΛ hvars
            exact S_preserves v hv hΛ (fun h => hvars (by
              simpa [B.Term.vars, B.fv, B.bv] using h))
    · rename_i heq
      subst heq
      set ctx := σ_S.types with hctx
      mspec Std.Do.Spec.get_StateT
      mspec freshVar_spec (Γ := ctx) (used := σ_S.env.usedVars)
      case post.success x =>
        mrename_i pre
        mintro ∀St₁
        mpure pre
        obtain ⟨St₁_types_eq, x_fresh, St₁_fvc_eq, St₁_used_eq, x_not_used⟩ := pre
        mspec freshVar_spec (Γ := ctx.insert x _) (used := St₁.env.usedVars)
        case post.success y =>
          mrename_i pre
          mintro ∀St₂
          mpure pre
          obtain ⟨St₂_types_eq, y_fresh, St₂_fvc_eq, St₂_used_eq, y_not_used⟩ := pre
          mspec freshVar_spec (Γ := (ctx.insert x _).insert y _) (used := St₂.env.usedVars)
          case post.success f =>
            mrename_i pre
            mintro ∀St₃
            mpure pre
            obtain ⟨St₃_types_eq, f_fresh, St₃_fvc_eq, St₃_used_eq, f_not_used⟩ := pre
            simp [modify]
            mspec Std.Do.Spec.modifyGet_StateT
            mpure_intro
            and_intros
            · intro v hv
              rw [St₃_used_eq, St₂_used_eq, St₁_used_eq]
              exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ (S_used_sub hv)))
            · exact S_Λ_sub
            · intro v hv
              rw [St₃_used_eq, St₂_used_eq, St₁_used_eq]
              exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ (S_keys_sub hv)))
            · intro v hv
              rw [B.fv] at hv
              rw [St₃_used_eq, St₂_used_eq, St₁_used_eq]
              exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ (S_cov v hv)))
            · intro v hv
              simp only [SMT.fv, List.mem_removeAll_iff, List.mem_append,
                List.mem_cons, List.not_mem_nil, or_false] at hv
              obtain ⟨⟨hv1, hv_ne_xy⟩, hv_ne_f⟩ := hv
              rcases hv1 with ((hvf | hvx) | hvy) | (hvS | hvx) | hvy
              · exact absurd hvf hv_ne_f
              · exact absurd (Or.inl hvx) hv_ne_xy
              · exact absurd (Or.inr hvy) hv_ne_xy
              · exact S_fv_sub hvS
              · exact absurd (Or.inl hvx) hv_ne_xy
              · exact absurd (Or.inr hvy) hv_ne_xy
            · intro v hv hΛ hvars
              exact S_preserves v hv hΛ (fun h => hvars (by
                simpa [B.Term.vars, B.fv, B.bv] using h))
    · mvcgen
  | cprod A C A_ih C_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
    rw [encodeTerm]
    have hA_bv_nodup : (B.bv A).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.1
    have hC_bv_nodup : (B.bv C).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.2.1
    have vars_used_A : ∀ v ∈ A.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h)
    have vars_used_C : ∀ v ∈ C.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inr h)
    mspec A_ih (E := E) (Λ := σ.types) vars_used_A hA_bv_nodup
    rename_i out_A
    obtain ⟨A_enc, σA⟩ := out_A
    mrename_i preA
    mintro ∀σ_A
    mpure preA
    obtain ⟨A_used_sub, A_Λ_sub, A_keys_sub, A_cov, A_fv_sub, A_preserves⟩ := preA
    split
    · rename_i heq
      injection heq with hAe hσe
      subst hσe
      subst hAe
      mspec C_ih (E := E) (Λ := σ_A.types) (used := σ_A.env.usedVars)
        (fun v hv => A_used_sub (vars_used_C v hv)) hC_bv_nodup
      rename_i out_C
      obtain ⟨C_enc, σC⟩ := out_C
      mrename_i preC
      mintro ∀σ_C
      mpure preC
      obtain ⟨C_used_sub, C_Λ_sub, C_keys_sub, C_cov, C_fv_sub, C_preserves⟩ := preC
      split
      · rename_i heq2
        injection heq2 with hCe hσe2
        subst hσe2
        subst hCe
        set ctx := σ_C.types with hctx
        mspec freshVar_spec (Γ := ctx) (used := σ_C.env.usedVars)
        case post.success p =>
          mrename_i pre
          mintro ∀St₁
          mpure pre
          obtain ⟨St₁_types_eq, p_fresh, St₁_fvc_eq, St₁_used_eq, p_not_used⟩ := pre
          mspec freshVar_spec (Γ := ctx.insert p _) (used := St₁.env.usedVars)
          case post.success a =>
            mrename_i pre
            mintro ∀St₂
            mpure pre
            obtain ⟨St₂_types_eq, a_fresh, St₂_fvc_eq, St₂_used_eq, a_not_used⟩ := pre
            mspec freshVar_spec (Γ := (ctx.insert p _).insert a _) (used := St₂.env.usedVars)
            case post.success b =>
              mrename_i pre
              mintro ∀St₃
              mpure pre
              obtain ⟨St₃_types_eq, b_fresh, St₃_fvc_eq, St₃_used_eq, b_not_used⟩ := pre
              mspec Std.Do.Spec.pure
              mpure_intro
              and_intros
              · intro v hv
                rw [St₃_used_eq, St₂_used_eq, St₁_used_eq]
                exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                  (List.mem_cons_of_mem _ (C_used_sub (A_used_sub hv))))
              · intro v hv
                rw [St₃_types_eq]
                apply SMT.TypeContext.entries_subset_insert_of_notMem b_fresh
                apply SMT.TypeContext.entries_subset_insert_of_notMem a_fresh
                apply SMT.TypeContext.entries_subset_insert_of_notMem p_fresh
                exact AList.subset_trans A_Λ_sub C_Λ_sub hv
              · intro v hv
                rw [St₃_used_eq, St₂_used_eq, St₁_used_eq]
                have hv' : v ∈ St₃.types := AList.mem_keys.mpr hv
                rw [St₃_types_eq] at hv'
                iterate 3 rw [AList.mem_insert] at hv'
                rcases hv' with rfl | rfl | rfl | hv'
                · exact List.mem_cons_self
                · exact List.mem_cons_of_mem _ List.mem_cons_self
                · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
                · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                    (List.mem_cons_of_mem _ (C_keys_sub (AList.mem_keys.mp hv'))))
              · intro v hv
                rw [B.fv, List.mem_append] at hv
                rw [St₃_used_eq, St₂_used_eq, St₁_used_eq]
                rcases hv with hv | hv
                · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                    (List.mem_cons_of_mem _ (C_used_sub (A_cov v hv))))
                · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                    (List.mem_cons_of_mem _ (C_cov v hv)))
              · intro v hv
                simp only [SMT.fv, List.mem_removeAll_iff, List.mem_append,
                  List.mem_cons, List.not_mem_nil, or_false] at hv
                obtain ⟨⟨hv1, hv_ne_ab⟩, hv_ne_p⟩ := hv
                rw [← AList.mem_keys, St₃_types_eq, AList.mem_insert,
                  AList.mem_insert, AList.mem_insert]
                rcases hv1 with (hvA | hva) | (hvC | hvb) | (hvp | hva | hvb)
                · have hvc : v ∈ ctx :=
                    AList.mem_of_subset C_Λ_sub (AList.mem_keys.mp (A_fv_sub hvA))
                  exact Or.inr (Or.inr (Or.inr hvc))
                · exact absurd (Or.inl hva) hv_ne_ab
                · have hvc : v ∈ ctx := AList.mem_keys.mp (C_fv_sub hvC)
                  exact Or.inr (Or.inr (Or.inr hvc))
                · exact absurd (Or.inr hvb) hv_ne_ab
                · exact absurd hvp hv_ne_p
                · exact absurd (Or.inl hva) hv_ne_ab
                · exact absurd (Or.inr hvb) hv_ne_ab
              · intro v hv hΛ hvars
                have hvA : v ∉ B.Term.vars A := fun h => hvars (by
                  simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
                    List.mem_append] at h ⊢
                  rcases h with h | h <;> [left; right] <;> exact .inl h)
                have hvC : v ∉ B.Term.vars C := fun h => hvars (by
                  simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
                    List.mem_append] at h ⊢
                  rcases h with h | h <;> [left; right] <;> exact .inr h)
                have hv_not_ctx : v ∉ ctx :=
                  C_preserves v (A_used_sub hv) (A_preserves v hv hΛ hvA) hvC
                rw [St₃_types_eq]
                intro hv_in
                iterate 3 rw [AList.mem_insert] at hv_in
                rcases hv_in with rfl | rfl | rfl | hv_in
                · exact b_not_used (by
                    rw [St₂_used_eq, St₁_used_eq]
                    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                      (C_used_sub (A_used_sub hv))))
                · exact a_not_used (by
                    rw [St₁_used_eq]
                    exact List.mem_cons_of_mem _ (C_used_sub (A_used_sub hv)))
                · exact p_not_used (C_used_sub (A_used_sub hv))
                · exact hv_not_ctx hv_in
      · mspec C_ih (E := E) (Λ := σ_C.types) (used := σ_C.env.usedVars)
          (fun v hv => C_used_sub (A_used_sub (vars_used_C v hv))) hC_bv_nodup
        mvcgen
    · mspec A_ih (E := E) (Λ := σ_A.types) (used := σ_A.env.usedVars)
        (fun v hv => A_used_sub (vars_used_A v hv)) hA_bv_nodup
      mvcgen
  | mem x S x_ih S_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
    rw [encodeTerm]
    have hx_bv_nodup : (B.bv x).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.1
    have hS_bv_nodup : (B.bv S).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.2.1
    have vars_used_x : ∀ v ∈ x.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h)
    have vars_used_S : ∀ v ∈ S.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inr h)
    mspec x_ih (E := E) (Λ := σ.types) vars_used_x hx_bv_nodup
    clear x_ih
    rename_i out_x
    obtain ⟨x_enc, σx⟩ := out_x
    mrename_i pre
    mintro ∀σ_x
    mpure pre
    obtain ⟨x_used_sub, x_Λ_sub, x_keys_sub, x_cov, x_fv_sub, x_preserves⟩ := pre
    mspec S_ih (E := E) (Λ := σ_x.types) (used := σ_x.env.usedVars)
      (fun v hv => x_used_sub (vars_used_S v hv)) hS_bv_nodup
    clear S_ih
    rename_i out_S
    obtain ⟨S_enc, σS⟩ := out_S
    mrename_i pre
    mintro ∀σ_S
    mpure pre
    obtain ⟨S_used_sub, S_Λ_sub, S_keys_sub, S_cov, S_fv_sub, S_preserves⟩ := pre
    unfold castMembership
    mvcgen
    · -- σx = α' : direct application
      and_intros
      · exact fun v hv => S_used_sub (x_used_sub hv)
      · exact AList.subset_trans x_Λ_sub S_Λ_sub
      · exact S_keys_sub
      · intro v hv
        rw [B.fv, List.mem_append] at hv
        rcases hv with hv | hv
        · exact S_used_sub (x_cov v hv)
        · exact S_cov v hv
      · intro v hv
        simp only [SMT.fv, List.mem_append] at hv
        rcases hv with hv | hv
        · exact S_fv_sub hv
        · exact AList.mem_keys.mpr (AList.mem_of_subset S_Λ_sub (AList.mem_keys.mp (x_fv_sub hv)))
      · intro v hv hΛ hvars
        have hvx : v ∉ B.Term.vars x := fun h => hvars (by
          simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
          rcases h with h | h <;> [left; right] <;> exact .inl h)
        have hvS : v ∉ B.Term.vars S := fun h => hvars (by
          simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
          rcases h with h | h <;> [left; right] <;> exact .inr h)
        exact S_preserves v (x_used_sub hv) (x_preserves v hv hΛ hvx) hvS
    · -- σx ⊑ α' : loosen x_enc
      mspec loosenAux_prf_state
      mrename_i pre
      mintro ∀S₁
      mpure pre
      obtain ⟨e_le, e_Λ_sub, e_fresh, e_not_used, e_used_sub,
        e_keys_sub, e_preserves, e_fv_sub⟩ := pre
      mvcgen
      rename_i e_pair _u _s hdc
      obtain ⟨e!, e!_spec⟩ := e_pair
      obtain ⟨_, _, _, hs_used, hs_types⟩ := hdc
      rw [hs_used, hs_types]
      and_intros
      · exact fun v hv => e_used_sub (S_used_sub (x_used_sub hv))
      · refine AList.subset_trans (AList.subset_trans x_Λ_sub S_Λ_sub) ?_
        exact AList.subset_trans
          (SMT.TypeContext.entries_subset_insert_of_notMem e_fresh) e_Λ_sub
      · exact e_keys_sub
      · intro v hv
        rw [B.fv, List.mem_append] at hv
        rcases hv with hv | hv
        · exact e_used_sub (S_used_sub (x_cov v hv))
        · exact e_used_sub (S_cov v hv)
      · intro v hv
        simp only [SMT.fv, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
        have key : ∀ w, w ∈ AList.keys σ_S.types → w ∈ AList.keys S₁.types := fun w hw =>
          AList.mem_keys.mp (AList.mem_of_subset e_Λ_sub
            (AList.mem_insert _ |>.mpr (Or.inr (AList.mem_keys.mpr hw))))
        have keyE : e! ∈ AList.keys S₁.types :=
          AList.mem_keys.mp (AList.mem_of_subset e_Λ_sub (AList.mem_insert _ |>.mpr (Or.inl rfl)))
        rcases hv with hvspec | (hvS | hve!)
        · have hmem := e_fv_sub hvspec
          rw [List.mem_union_iff] at hmem
          rcases hmem with hx | he!
          · exact key _ (AList.mem_keys.mp (AList.mem_of_subset S_Λ_sub
              (AList.mem_keys.mpr (x_fv_sub hx))))
          · have he!' := List.mem_singleton.mp he!
            subst he!'; exact keyE
        · exact key _ (S_fv_sub hvS)
        · subst hve!; exact keyE
      · intro v hv hΛ hvars
        have hvx : v ∉ B.Term.vars x := fun h => hvars (by
          simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
          rcases h with h | h <;> [left; right] <;> exact .inl h)
        have hvS : v ∉ B.Term.vars S := fun h => hvars (by
          simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
          rcases h with h | h <;> [left; right] <;> exact .inr h)
        exact e_preserves v (S_used_sub (x_used_sub hv))
          (S_preserves v (x_used_sub hv) (x_preserves v hv hΛ hvx) hvS)
    · -- α' ⊑ σx : loosen S_enc
      mspec loosenAux_prf_state
      mrename_i pre
      mintro ∀S₁
      mpure pre
      obtain ⟨e_le, e_Λ_sub, e_fresh, e_not_used, e_used_sub,
        e_keys_sub, e_preserves, e_fv_sub⟩ := pre
      mvcgen
      rename_i e_pair _u _s hdc
      obtain ⟨e!, e!_spec⟩ := e_pair
      obtain ⟨_, _, _, hs_used, hs_types⟩ := hdc
      rw [hs_used, hs_types]
      and_intros
      · exact fun v hv => e_used_sub (S_used_sub (x_used_sub hv))
      · refine AList.subset_trans (AList.subset_trans x_Λ_sub S_Λ_sub) ?_
        exact AList.subset_trans
          (SMT.TypeContext.entries_subset_insert_of_notMem e_fresh) e_Λ_sub
      · exact e_keys_sub
      · intro v hv
        rw [B.fv, List.mem_append] at hv
        rcases hv with hv | hv
        · exact e_used_sub (S_used_sub (x_cov v hv))
        · exact e_used_sub (S_cov v hv)
      · intro v hv
        simp only [SMT.fv, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
        have key : ∀ w, w ∈ AList.keys σ_S.types → w ∈ AList.keys S₁.types := fun w hw =>
          AList.mem_keys.mp (AList.mem_of_subset e_Λ_sub
            (AList.mem_insert _ |>.mpr (Or.inr (AList.mem_keys.mpr hw))))
        have keyE : e! ∈ AList.keys S₁.types :=
          AList.mem_keys.mp (AList.mem_of_subset e_Λ_sub (AList.mem_insert _ |>.mpr (Or.inl rfl)))
        rcases hv with hvspec | (hve! | hvx)
        · have hmem := e_fv_sub hvspec
          rw [List.mem_union_iff] at hmem
          rcases hmem with hS | he!
          · exact key _ (S_fv_sub hS)
          · have he!' := List.mem_singleton.mp he!
            subst he!'; exact keyE
        · subst hve!; exact keyE
        · exact key _ (AList.mem_keys.mp (AList.mem_of_subset S_Λ_sub
            (AList.mem_keys.mpr (x_fv_sub hvx))))
      · intro v hv hΛ hvars
        have hvx : v ∉ B.Term.vars x := fun h => hvars (by
          simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
          rcases h with h | h <;> [left; right] <;> exact .inl h)
        have hvS : v ∉ B.Term.vars S := fun h => hvars (by
          simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
          rcases h with h | h <;> [left; right] <;> exact .inr h)
        exact e_preserves v (S_used_sub (x_used_sub hv))
          (S_preserves v (x_used_sub hv) (x_preserves v hv hΛ hvx) hvS)
    · -- pair element type, α ⊑ α' ∧ β ⊑ β' : loosen x_enc
      mspec loosenAux_prf_state
      mrename_i pre
      mintro ∀S₁
      mpure pre
      obtain ⟨e_le, e_Λ_sub, e_fresh, e_not_used, e_used_sub,
        e_keys_sub, e_preserves, e_fv_sub⟩ := pre
      mvcgen
      rename_i e_pair _u _s hdc
      obtain ⟨e!, e!_spec⟩ := e_pair
      obtain ⟨_, _, _, hs_used, hs_types⟩ := hdc
      rw [hs_used, hs_types]
      and_intros
      · exact fun v hv => e_used_sub (S_used_sub (x_used_sub hv))
      · refine AList.subset_trans (AList.subset_trans x_Λ_sub S_Λ_sub) ?_
        exact AList.subset_trans
          (SMT.TypeContext.entries_subset_insert_of_notMem e_fresh) e_Λ_sub
      · exact e_keys_sub
      · intro v hv
        rw [B.fv, List.mem_append] at hv
        rcases hv with hv | hv
        · exact e_used_sub (S_used_sub (x_cov v hv))
        · exact e_used_sub (S_cov v hv)
      · intro v hv
        simp only [SMT.fv, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
        have key : ∀ w, w ∈ AList.keys σ_S.types → w ∈ AList.keys S₁.types := fun w hw =>
          AList.mem_keys.mp (AList.mem_of_subset e_Λ_sub
            (AList.mem_insert _ |>.mpr (Or.inr (AList.mem_keys.mpr hw))))
        have keyE : e! ∈ AList.keys S₁.types :=
          AList.mem_keys.mp (AList.mem_of_subset e_Λ_sub (AList.mem_insert _ |>.mpr (Or.inl rfl)))
        rcases hv with hvspec | ((hvS | hve!) | hve!')
        · have hmem := e_fv_sub hvspec
          rw [List.mem_union_iff] at hmem
          rcases hmem with hx | he!
          · exact key _ (AList.mem_keys.mp (AList.mem_of_subset S_Λ_sub
              (AList.mem_keys.mpr (x_fv_sub hx))))
          · have he!' := List.mem_singleton.mp he!
            subst he!'; exact keyE
        · exact key _ (S_fv_sub hvS)
        · subst hve!; exact keyE
        · subst hve!'; exact keyE
      · intro v hv hΛ hvars
        have hvx : v ∉ B.Term.vars x := fun h => hvars (by
          simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
          rcases h with h | h <;> [left; right] <;> exact .inl h)
        have hvS : v ∉ B.Term.vars S := fun h => hvars (by
          simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
          rcases h with h | h <;> [left; right] <;> exact .inr h)
        exact e_preserves v (S_used_sub (x_used_sub hv))
          (S_preserves v (x_used_sub hv) (x_preserves v hv hΛ hvx) hvS)
    · -- pair element type, α ⊑ α' ∧ β' ⊑ β : loosen x_enc.fst then S_enc
      mspec loosenAux_prf_state
      mrename_i pre
      mintro ∀S₁
      rename_i e_pair
      obtain ⟨e!, e!_spec⟩ := e_pair
      mpure pre
      obtain ⟨e_le, e_Λ_sub, e_fresh, e_not_used, e_used_sub,
        e_keys_sub, e_preserves, e_fv_sub⟩ := pre
      mspec (SMT.declareConst_spec (Γ := S₁.types))
      mrename_i pred
      mintro ∀S₁d
      mpure pred
      obtain ⟨_, _, _, hd1_used, hd1_types⟩ := pred
      have S₁d_keys : AList.keys S₁d.types ⊆ S₁d.env.usedVars := by
        rw [hd1_types, hd1_used]; exact e_keys_sub
      mspec loosenAux_prf_state
      mrename_i pre
      mintro ∀S₂
      rename_i f_pair
      obtain ⟨gv, gv_spec⟩ := f_pair
      mpure pre
      obtain ⟨f_le, f_Λ_sub, f_fresh, f_not_used, f_used_sub,
        f_keys_sub, f_preserves, f_fv_sub⟩ := pre
      rw [hd1_types] at f_Λ_sub f_fresh
      rw [hd1_used] at f_used_sub
      mvcgen
      rename_i _u _s hdc
      obtain ⟨_, _, _, hs_used, hs_types⟩ := hdc
      rw [hs_used, hs_types]
      have e_into_S₁ : ∀ w, w ∈ AList.keys σ_S.types → w ∈ AList.keys S₁.types := fun w hw =>
        AList.mem_keys.mp (AList.mem_of_subset e_Λ_sub
          (AList.mem_insert _ |>.mpr (Or.inr (AList.mem_keys.mpr hw))))
      have e!_in_S₁ : e! ∈ AList.keys S₁.types :=
        AList.mem_keys.mp (AList.mem_of_subset e_Λ_sub (AList.mem_insert _ |>.mpr (Or.inl rfl)))
      have S₁_into_S₂ : ∀ w, w ∈ AList.keys S₁.types → w ∈ AList.keys S₂.types := fun w hw =>
        AList.mem_keys.mp (AList.mem_of_subset f_Λ_sub
          (AList.mem_insert _ |>.mpr (Or.inr (AList.mem_keys.mpr hw))))
      have gv_in_S₂ : gv ∈ AList.keys S₂.types :=
        AList.mem_keys.mp (AList.mem_of_subset f_Λ_sub (AList.mem_insert _ |>.mpr (Or.inl rfl)))
      and_intros
      · exact fun v hv => f_used_sub (e_used_sub (S_used_sub (x_used_sub hv)))
      · have he : σ_S.types ⊆ S₁.types :=
          AList.subset_trans (SMT.TypeContext.entries_subset_insert_of_notMem e_fresh) e_Λ_sub
        have hf : S₁.types ⊆ S₂.types :=
          AList.subset_trans (SMT.TypeContext.entries_subset_insert_of_notMem f_fresh) f_Λ_sub
        exact AList.subset_trans (AList.subset_trans x_Λ_sub S_Λ_sub)
          (AList.subset_trans he hf)
      · exact f_keys_sub
      · intro v hv
        rw [B.fv, List.mem_append] at hv
        rcases hv with hv | hv
        · exact f_used_sub (e_used_sub (S_used_sub (x_cov v hv)))
        · exact f_used_sub (e_used_sub (S_cov v hv))
      · intro v hv
        simp only [SMT.fv, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
        have ekey : ∀ w, w ∈ SMT.fv x_enc → w ∈ AList.keys S₂.types := fun w hw =>
          S₁_into_S₂ _ (e_into_S₁ _ (AList.mem_keys.mp (AList.mem_of_subset S_Λ_sub
            (AList.mem_keys.mpr (x_fv_sub hw)))))
        rcases hv with (hvespec | hvfspec) | ((hvgv | hve!) | hvx)
        · have hmem := e_fv_sub hvespec
          rw [List.mem_union_iff] at hmem
          rcases hmem with hx | he!
          · simp only [SMT.fv] at hx; exact ekey _ hx
          · have he!' := List.mem_singleton.mp he!
            subst he!'; exact S₁_into_S₂ _ e!_in_S₁
        · have hmem := f_fv_sub hvfspec
          rw [List.mem_union_iff] at hmem
          rcases hmem with hS | hgv
          · exact S₁_into_S₂ _ (e_into_S₁ _ (S_fv_sub hS))
          · have hgv' := List.mem_singleton.mp hgv
            subst hgv'; exact gv_in_S₂
        · subst hvgv; exact gv_in_S₂
        · subst hve!; exact S₁_into_S₂ _ e!_in_S₁
        · exact ekey _ hvx
      · intro v hv hΛ hvars
        have hvx : v ∉ B.Term.vars x := fun h => hvars (by
          simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
          rcases h with h | h <;> [left; right] <;> exact .inl h)
        have hvS : v ∉ B.Term.vars S := fun h => hvars (by
          simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
          rcases h with h | h <;> [left; right] <;> exact .inr h)
        exact f_preserves v (hd1_used ▸ e_used_sub (S_used_sub (x_used_sub hv)))
          (hd1_types ▸ e_preserves v (S_used_sub (x_used_sub hv))
            (S_preserves v (x_used_sub hv) (x_preserves v hv hΛ hvx) hvS))
    · -- pair element type, α' ⊑ α ∧ β ⊑ β' : loosen x_enc.snd then S_enc
      mspec loosenAux_prf_state
      mrename_i pre
      mintro ∀S₁
      rename_i e_pair
      obtain ⟨e!, e!_spec⟩ := e_pair
      mpure pre
      obtain ⟨e_le, e_Λ_sub, e_fresh, e_not_used, e_used_sub,
        e_keys_sub, e_preserves, e_fv_sub⟩ := pre
      mspec (SMT.declareConst_spec (Γ := S₁.types))
      mrename_i pred
      mintro ∀S₁d
      mpure pred
      obtain ⟨_, _, _, hd1_used, hd1_types⟩ := pred
      have S₁d_keys : AList.keys S₁d.types ⊆ S₁d.env.usedVars := by
        rw [hd1_types, hd1_used]; exact e_keys_sub
      mspec loosenAux_prf_state
      mrename_i pre
      mintro ∀S₂
      rename_i f_pair
      obtain ⟨gv, gv_spec⟩ := f_pair
      mpure pre
      obtain ⟨f_le, f_Λ_sub, f_fresh, f_not_used, f_used_sub,
        f_keys_sub, f_preserves, f_fv_sub⟩ := pre
      rw [hd1_types] at f_Λ_sub f_fresh
      rw [hd1_used] at f_used_sub
      mvcgen
      rename_i _u _s hdc
      obtain ⟨_, _, _, hs_used, hs_types⟩ := hdc
      rw [hs_used, hs_types]
      have e_into_S₁ : ∀ w, w ∈ AList.keys σ_S.types → w ∈ AList.keys S₁.types := fun w hw =>
        AList.mem_keys.mp (AList.mem_of_subset e_Λ_sub
          (AList.mem_insert _ |>.mpr (Or.inr (AList.mem_keys.mpr hw))))
      have e!_in_S₁ : e! ∈ AList.keys S₁.types :=
        AList.mem_keys.mp (AList.mem_of_subset e_Λ_sub (AList.mem_insert _ |>.mpr (Or.inl rfl)))
      have S₁_into_S₂ : ∀ w, w ∈ AList.keys S₁.types → w ∈ AList.keys S₂.types := fun w hw =>
        AList.mem_keys.mp (AList.mem_of_subset f_Λ_sub
          (AList.mem_insert _ |>.mpr (Or.inr (AList.mem_keys.mpr hw))))
      have gv_in_S₂ : gv ∈ AList.keys S₂.types :=
        AList.mem_keys.mp (AList.mem_of_subset f_Λ_sub (AList.mem_insert _ |>.mpr (Or.inl rfl)))
      and_intros
      · exact fun v hv => f_used_sub (e_used_sub (S_used_sub (x_used_sub hv)))
      · have he : σ_S.types ⊆ S₁.types :=
          AList.subset_trans (SMT.TypeContext.entries_subset_insert_of_notMem e_fresh) e_Λ_sub
        have hf : S₁.types ⊆ S₂.types :=
          AList.subset_trans (SMT.TypeContext.entries_subset_insert_of_notMem f_fresh) f_Λ_sub
        exact AList.subset_trans (AList.subset_trans x_Λ_sub S_Λ_sub)
          (AList.subset_trans he hf)
      · exact f_keys_sub
      · intro v hv
        rw [B.fv, List.mem_append] at hv
        rcases hv with hv | hv
        · exact f_used_sub (e_used_sub (S_used_sub (x_cov v hv)))
        · exact f_used_sub (e_used_sub (S_cov v hv))
      · intro v hv
        simp only [SMT.fv, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
        have ekey : ∀ w, w ∈ SMT.fv x_enc → w ∈ AList.keys S₂.types := fun w hw =>
          S₁_into_S₂ _ (e_into_S₁ _ (AList.mem_keys.mp (AList.mem_of_subset S_Λ_sub
            (AList.mem_keys.mpr (x_fv_sub hw)))))
        rcases hv with (hvespec | hvfspec) | ((hvgv | hvx) | hve!)
        · have hmem := e_fv_sub hvespec
          rw [List.mem_union_iff] at hmem
          rcases hmem with hx | he!
          · simp only [SMT.fv] at hx; exact ekey _ hx
          · have he!' := List.mem_singleton.mp he!
            subst he!'; exact S₁_into_S₂ _ e!_in_S₁
        · have hmem := f_fv_sub hvfspec
          rw [List.mem_union_iff] at hmem
          rcases hmem with hS | hgv
          · exact S₁_into_S₂ _ (e_into_S₁ _ (S_fv_sub hS))
          · have hgv' := List.mem_singleton.mp hgv
            subst hgv'; exact gv_in_S₂
        · subst hvgv; exact gv_in_S₂
        · exact ekey _ hvx
        · subst hve!; exact S₁_into_S₂ _ e!_in_S₁
      · intro v hv hΛ hvars
        have hvx : v ∉ B.Term.vars x := fun h => hvars (by
          simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
          rcases h with h | h <;> [left; right] <;> exact .inl h)
        have hvS : v ∉ B.Term.vars S := fun h => hvars (by
          simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
          rcases h with h | h <;> [left; right] <;> exact .inr h)
        exact f_preserves v (hd1_used ▸ e_used_sub (S_used_sub (x_used_sub hv)))
          (hd1_types ▸ e_preserves v (S_used_sub (x_used_sub hv))
            (S_preserves v (x_used_sub hv) (x_preserves v hv hΛ hvx) hvS))
    · -- pair element type, α' ⊑ α ∧ β' ⊑ β : loosen S_enc
      mspec loosenAux_prf_state
      mrename_i pre
      mintro ∀S₁
      mpure pre
      obtain ⟨e_le, e_Λ_sub, e_fresh, e_not_used, e_used_sub,
        e_keys_sub, e_preserves, e_fv_sub⟩ := pre
      mvcgen
      rename_i e_pair _u _s hdc
      obtain ⟨e!, e!_spec⟩ := e_pair
      obtain ⟨_, _, _, hs_used, hs_types⟩ := hdc
      rw [hs_used, hs_types]
      and_intros
      · exact fun v hv => e_used_sub (S_used_sub (x_used_sub hv))
      · refine AList.subset_trans (AList.subset_trans x_Λ_sub S_Λ_sub) ?_
        exact AList.subset_trans
          (SMT.TypeContext.entries_subset_insert_of_notMem e_fresh) e_Λ_sub
      · exact e_keys_sub
      · intro v hv
        rw [B.fv, List.mem_append] at hv
        rcases hv with hv | hv
        · exact e_used_sub (S_used_sub (x_cov v hv))
        · exact e_used_sub (S_cov v hv)
      · intro v hv
        simp only [SMT.fv, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
        have key : ∀ w, w ∈ AList.keys σ_S.types → w ∈ AList.keys S₁.types := fun w hw =>
          AList.mem_keys.mp (AList.mem_of_subset e_Λ_sub
            (AList.mem_insert _ |>.mpr (Or.inr (AList.mem_keys.mpr hw))))
        have keyE : e! ∈ AList.keys S₁.types :=
          AList.mem_keys.mp (AList.mem_of_subset e_Λ_sub (AList.mem_insert _ |>.mpr (Or.inl rfl)))
        have xkey : ∀ w, w ∈ SMT.fv x_enc → w ∈ AList.keys S₁.types := fun w hw =>
          key _ (AList.mem_keys.mp (AList.mem_of_subset S_Λ_sub
            (AList.mem_keys.mpr (x_fv_sub hw))))
        rcases hv with hvspec | ((hve! | hvx1) | hvx2)
        · have hmem := e_fv_sub hvspec
          rw [List.mem_union_iff] at hmem
          rcases hmem with hS | he!
          · exact key _ (S_fv_sub hS)
          · have he!' := List.mem_singleton.mp he!
            subst he!'; exact keyE
        · subst hve!; exact keyE
        · exact xkey _ hvx1
        · exact xkey _ hvx2
      · intro v hv hΛ hvars
        have hvx : v ∉ B.Term.vars x := fun h => hvars (by
          simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
          rcases h with h | h <;> [left; right] <;> exact .inl h)
        have hvS : v ∉ B.Term.vars S := fun h => hvars (by
          simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
          rcases h with h | h <;> [left; right] <;> exact .inr h)
        exact e_preserves v (S_used_sub (x_used_sub hv))
          (S_preserves v (x_used_sub hv) (x_preserves v hv hΛ hvx) hvS)
  | eq x y x_ih y_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
    rw [encodeTerm]
    have hx_bv_nodup : (B.bv x).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.1
    have hy_bv_nodup : (B.bv y).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.2.1
    have vars_used_x : ∀ v ∈ x.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h)
    have vars_used_y : ∀ v ∈ y.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inr h)
    mspec x_ih (E := E) (Λ := σ.types) vars_used_x hx_bv_nodup
    clear x_ih
    rename_i out_x
    obtain ⟨x_enc, σx⟩ := out_x
    mrename_i pre
    mintro ∀σ_x
    mpure pre
    obtain ⟨x_used_sub, x_Λ_sub, x_keys_sub, x_cov, x_fv_sub, x_preserves⟩ := pre
    mspec y_ih (E := E) (Λ := σ_x.types) (used := σ_x.env.usedVars)
      (fun v hv => x_used_sub (vars_used_y v hv)) hy_bv_nodup
    clear y_ih
    rename_i out_y
    obtain ⟨y_enc, σy⟩ := out_y
    mrename_i pre
    mintro ∀σ_y
    mpure pre
    obtain ⟨y_used_sub, y_Λ_sub, y_keys_sub, y_cov, y_fv_sub, y_preserves⟩ := pre
    unfold castEq
    mvcgen
    · -- σx = σy : direct equality
      and_intros
      · exact fun v hv => y_used_sub (x_used_sub hv)
      · exact AList.subset_trans x_Λ_sub y_Λ_sub
      · exact y_keys_sub
      · intro v hv
        rw [B.fv, List.mem_append] at hv
        rcases hv with hv | hv
        · exact y_used_sub (x_cov v hv)
        · exact y_cov v hv
      · intro v hv
        simp only [SMT.fv, List.mem_append] at hv
        rcases hv with hv | hv
        · exact AList.mem_keys.mpr (AList.mem_of_subset y_Λ_sub (AList.mem_keys.mp (x_fv_sub hv)))
        · exact y_fv_sub hv
      · intro v hv hΛ hvars
        have hvx : v ∉ B.Term.vars x := fun h => hvars (by
          simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
          rcases h with h | h <;> [left; right] <;> exact .inl h)
        have hvy : v ∉ B.Term.vars y := fun h => hvars (by
          simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
          rcases h with h | h <;> [left; right] <;> exact .inr h)
        exact y_preserves v (x_used_sub hv) (x_preserves v hv hΛ hvx) hvy
    · -- σx ⊑ σy : loosen x_enc
      mspec loosenAux_prf_state
      mrename_i pre
      mintro ∀S₁
      mpure pre
      obtain ⟨A!_le, A!_Λ_sub, A!_fresh, A!_not_used, A!_used_sub,
        A!_keys_sub, A!_preserves, A!_fv_sub⟩ := pre
      mvcgen
      rename_i A!_pair _u _s hdc
      obtain ⟨A!, A!_spec⟩ := A!_pair
      obtain ⟨_, _, _, hs_used, hs_types⟩ := hdc
      rw [hs_used, hs_types]
      and_intros
      · exact fun v hv => A!_used_sub (y_used_sub (x_used_sub hv))
      · refine AList.subset_trans (AList.subset_trans x_Λ_sub y_Λ_sub) ?_
        exact AList.subset_trans
          (SMT.TypeContext.entries_subset_insert_of_notMem A!_fresh) A!_Λ_sub
      · exact A!_keys_sub
      · intro v hv
        rw [B.fv, List.mem_append] at hv
        rcases hv with hv | hv
        · exact A!_used_sub (y_used_sub (x_cov v hv))
        · exact A!_used_sub (y_cov v hv)
      · intro v hv
        simp only [SMT.fv, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with (hvA! | hvy) | hvspec
        · subst hvA!
          exact AList.mem_keys.mp (AList.mem_of_subset A!_Λ_sub (AList.mem_insert _ |>.mpr (Or.inl rfl)))
        · have : v ∈ AList.keys σ_y.types := y_fv_sub hvy
          exact AList.mem_keys.mp (AList.mem_of_subset A!_Λ_sub
            (AList.mem_insert _ |>.mpr (Or.inr (AList.mem_keys.mpr this))))
        · have hmem := A!_fv_sub hvspec
          rw [List.mem_union_iff] at hmem
          rcases hmem with hx | hA!
          · have hxk : v ∈ AList.keys σ_x.types := x_fv_sub hx
            have : v ∈ AList.keys σ_y.types :=
              AList.mem_keys.mp (AList.mem_of_subset y_Λ_sub (AList.mem_keys.mpr hxk))
            exact AList.mem_keys.mp (AList.mem_of_subset A!_Λ_sub
              (AList.mem_insert _ |>.mpr (Or.inr (AList.mem_keys.mpr this))))
          · have hA!' := List.mem_singleton.mp hA!
            subst hA!'
            exact AList.mem_keys.mp (AList.mem_of_subset A!_Λ_sub
              (AList.mem_insert _ |>.mpr (Or.inl rfl)))
      · intro v hv hΛ hvars
        have hvx : v ∉ B.Term.vars x := fun h => hvars (by
          simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
          rcases h with h | h <;> [left; right] <;> exact .inl h)
        have hvy : v ∉ B.Term.vars y := fun h => hvars (by
          simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
          rcases h with h | h <;> [left; right] <;> exact .inr h)
        exact A!_preserves v (y_used_sub (x_used_sub hv))
          (y_preserves v (x_used_sub hv) (x_preserves v hv hΛ hvx) hvy)
    · -- σy ⊑ σx : loosen y_enc
      mspec loosenAux_prf_state
      mrename_i pre
      mintro ∀S₁
      mpure pre
      obtain ⟨B!_le, B!_Λ_sub, B!_fresh, B!_not_used, B!_used_sub,
        B!_keys_sub, B!_preserves, B!_fv_sub⟩ := pre
      mvcgen
      rename_i B!_pair _u _s hdc
      obtain ⟨B!, B!_spec⟩ := B!_pair
      obtain ⟨_, _, _, hs_used, hs_types⟩ := hdc
      rw [hs_used, hs_types]
      and_intros
      · exact fun v hv => B!_used_sub (y_used_sub (x_used_sub hv))
      · refine AList.subset_trans (AList.subset_trans x_Λ_sub y_Λ_sub) ?_
        exact AList.subset_trans
          (SMT.TypeContext.entries_subset_insert_of_notMem B!_fresh) B!_Λ_sub
      · exact B!_keys_sub
      · intro v hv
        rw [B.fv, List.mem_append] at hv
        rcases hv with hv | hv
        · exact B!_used_sub (y_used_sub (x_cov v hv))
        · exact B!_used_sub (y_cov v hv)
      · intro v hv
        simp only [SMT.fv, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with (hvB! | hvx) | hvspec
        · subst hvB!
          exact AList.mem_keys.mp (AList.mem_of_subset B!_Λ_sub (AList.mem_insert _ |>.mpr (Or.inl rfl)))
        · have hxk : v ∈ AList.keys σ_x.types := x_fv_sub hvx
          have : v ∈ AList.keys σ_y.types :=
            AList.mem_keys.mp (AList.mem_of_subset y_Λ_sub (AList.mem_keys.mpr hxk))
          exact AList.mem_keys.mp (AList.mem_of_subset B!_Λ_sub
            (AList.mem_insert _ |>.mpr (Or.inr (AList.mem_keys.mpr this))))
        · have hmem := B!_fv_sub hvspec
          rw [List.mem_union_iff] at hmem
          rcases hmem with hy | hB!
          · have : v ∈ AList.keys σ_y.types := y_fv_sub hy
            exact AList.mem_keys.mp (AList.mem_of_subset B!_Λ_sub
              (AList.mem_insert _ |>.mpr (Or.inr (AList.mem_keys.mpr this))))
          · have hB!' := List.mem_singleton.mp hB!
            subst hB!'
            exact AList.mem_keys.mp (AList.mem_of_subset B!_Λ_sub
              (AList.mem_insert _ |>.mpr (Or.inl rfl)))
      · intro v hv hΛ hvars
        have hvx : v ∉ B.Term.vars x := fun h => hvars (by
          simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
          rcases h with h | h <;> [left; right] <;> exact .inl h)
        have hvy : v ∉ B.Term.vars y := fun h => hvars (by
          simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
          rcases h with h | h <;> [left; right] <;> exact .inr h)
        exact B!_preserves v (y_used_sub (x_used_sub hv))
          (y_preserves v (x_used_sub hv) (x_preserves v hv hΛ hvx) hvy)
  | union A C A_ih C_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
    rw [encodeTerm]
    have hA_bv_nodup : (B.bv A).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.1
    have hC_bv_nodup : (B.bv C).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.2.1
    have vars_used_A : ∀ v ∈ A.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h)
    have vars_used_C : ∀ v ∈ C.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inr h)
    mspec A_ih (E := E) (Λ := σ.types) vars_used_A hA_bv_nodup
    clear A_ih
    rename_i out_A
    obtain ⟨A_enc, σA⟩ := out_A
    mrename_i pre
    mintro ∀σ_A
    mpure pre
    obtain ⟨A_used_sub, A_Λ_sub, A_keys_sub, A_cov, A_fv_sub, A_preserves⟩ := pre
    mspec C_ih (E := E) (Λ := σ_A.types) (used := σ_A.env.usedVars)
      (fun v hv => A_used_sub (vars_used_C v hv)) hC_bv_nodup
    clear C_ih
    rename_i out_C
    obtain ⟨C_enc, σC⟩ := out_C
    mrename_i pre
    mintro ∀σ_C
    mpure pre
    obtain ⟨C_used_sub, C_Λ_sub, C_keys_sub, C_cov, C_fv_sub, C_preserves⟩ := pre
    unfold castUnion
    split <;> split <;> split <;> split
    · -- direct path : σA = σC = γ → bool
      rename_i _ Senc1 _ Senc2 _ _ _ gamma heqA heqC
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heqA
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heqC
      mspec SMT.freshVar_spec
      mrename_i pre
      mintro ∀St₁
      mpure pre
      obtain ⟨St₁_types_eq, x_fresh, St₁_fvc, St₁_used_eq, x_not_used⟩ := pre
      mspec Std.Do.Spec.pure
      mpure_intro
      rename_i x
      and_intros
      · intro v hv
        rw [St₁_used_eq]
        exact List.mem_cons_of_mem _ (C_used_sub (A_used_sub hv))
      · rw [St₁_types_eq]
        exact AList.subset_trans (AList.subset_trans A_Λ_sub C_Λ_sub)
          (SMT.TypeContext.entries_subset_insert_of_notMem x_fresh)
      · rw [St₁_types_eq, St₁_used_eq]
        exact keys_insert_subset_cons C_keys_sub
      · intro v hv
        rw [B.fv, List.mem_append] at hv
        rw [St₁_used_eq]
        rcases hv with hv | hv
        · exact List.mem_cons_of_mem _ (C_used_sub (A_cov v hv))
        · exact List.mem_cons_of_mem _ (C_cov v hv)
      · intro v hv
        simp only [SMT.fv, List.mem_removeAll_iff, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false] at hv
        obtain ⟨hv_body, hv_ne_x⟩ := hv
        rw [St₁_types_eq, ← AList.mem_keys, AList.mem_insert]
        refine Or.inr ?_
        rcases hv_body with (hvA | hvx) | (hvC | hvx)
        · exact AList.mem_keys.mpr (AList.mem_of_subset C_Λ_sub
            (AList.mem_keys.mpr (A_fv_sub hvA)))
        · exact absurd hvx hv_ne_x
        · exact AList.mem_keys.mpr (AList.mem_keys.mp (C_fv_sub hvC))
        · exact absurd hvx hv_ne_x
      · intro v hv hΛ hvars
        have hvA : v ∉ B.Term.vars A := fun h => hvars (by
          simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
          rcases h with h | h <;> [left; right] <;> exact .inl h)
        have hvC : v ∉ B.Term.vars C := fun h => hvars (by
          simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
          rcases h with h | h <;> [left; right] <;> exact .inr h)
        have hv_not_σC : v ∉ σ_C.types :=
          C_preserves v (A_used_sub hv) (A_preserves v hv hΛ hvA) hvC
        rw [St₁_types_eq]
        intro hv_in
        rw [AList.mem_insert] at hv_in
        rcases hv_in with rfl | hv_in
        · exact x_not_used (C_used_sub (A_used_sub hv))
        · exact hv_not_σC hv_in
    · mvcgen
    · -- σA ⊑ σC : castUnionAux A_enc C_enc
      rename_i _ Senc1 _ heqA _ Senc2 _ heqC _ _
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heqA
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heqC
      mspec castUnionAux_state
      case pre =>
        mpure_intro
        refine ⟨trivial, trivial, C_keys_sub, rfl, ?_, ?_⟩
        · intro v hv
          exact AList.mem_keys.mp (AList.mem_of_subset C_Λ_sub
            (AList.mem_keys.mpr (A_fv_sub hv)))
        · intro v hv
          exact C_fv_sub hv
      case post.success =>
        mrename_i hpost
        mintro ∀St'
        mpure hpost
        obtain ⟨h_le, h_Λ_sub, h_used_sub, h_keys_sub, h_fv_sub, h_preserves⟩ := hpost
        mpure_intro
        and_intros
        · exact fun v hv => h_used_sub (C_used_sub (A_used_sub hv))
        · exact AList.subset_trans (AList.subset_trans A_Λ_sub C_Λ_sub) h_Λ_sub
        · exact h_keys_sub
        · intro v hv
          rw [B.fv, List.mem_append] at hv
          rcases hv with hv | hv
          · exact h_used_sub (C_used_sub (A_cov v hv))
          · exact h_used_sub (C_cov v hv)
        · exact h_fv_sub
        · intro v hv hΛ hvars
          have hvA : v ∉ B.Term.vars A := fun h => hvars (by
            simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
            rcases h with h | h <;> [left; right] <;> exact .inl h)
          have hvC : v ∉ B.Term.vars C := fun h => hvars (by
            simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
            rcases h with h | h <;> [left; right] <;> exact .inr h)
          exact h_preserves v (C_used_sub (A_used_sub hv))
            (C_preserves v (A_used_sub hv) (A_preserves v hv hΛ hvA) hvC)
    · split
      · -- σC ⊑ σA : castUnionAux C_enc A_enc
        rename_i _ Senc1 _ heqA _ Senc2 _ heqC _ _ _
        obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heqA
        obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heqC
        mspec castUnionAux_state
        case pre =>
          mpure_intro
          refine ⟨trivial, trivial, C_keys_sub, rfl, ?_, ?_⟩
          · intro v hv
            exact C_fv_sub hv
          · intro v hv
            exact AList.mem_keys.mp (AList.mem_of_subset C_Λ_sub
              (AList.mem_keys.mpr (A_fv_sub hv)))
        case post.success =>
          mrename_i hpost
          mintro ∀St'
          mpure hpost
          obtain ⟨h_le, h_Λ_sub, h_used_sub, h_keys_sub, h_fv_sub, h_preserves⟩ := hpost
          mpure_intro
          and_intros
          · exact fun v hv => h_used_sub (C_used_sub (A_used_sub hv))
          · exact AList.subset_trans (AList.subset_trans A_Λ_sub C_Λ_sub) h_Λ_sub
          · exact h_keys_sub
          · intro v hv
            rw [B.fv, List.mem_append] at hv
            rcases hv with hv | hv
            · exact h_used_sub (C_used_sub (A_cov v hv))
            · exact h_used_sub (C_cov v hv)
          · exact h_fv_sub
          · intro v hv hΛ hvars
            have hvA : v ∉ B.Term.vars A := fun h => hvars (by
              simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
              rcases h with h | h <;> [left; right] <;> exact .inl h)
            have hvC : v ∉ B.Term.vars C := fun h => hvars (by
              simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
              rcases h with h | h <;> [left; right] <;> exact .inr h)
            exact h_preserves v (C_used_sub (A_used_sub hv))
              (C_preserves v (A_used_sub hv) (A_preserves v hv hΛ hvA) hvC)
      · mvcgen
  | inter A C A_ih C_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
    rw [encodeTerm]
    have hA_bv_nodup : (B.bv A).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.1
    have hC_bv_nodup : (B.bv C).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.2.1
    have vars_used_A : ∀ v ∈ A.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h)
    have vars_used_C : ∀ v ∈ C.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inr h)
    mspec A_ih (E := E) (Λ := σ.types) vars_used_A hA_bv_nodup
    clear A_ih
    rename_i out_A
    obtain ⟨A_enc, σA⟩ := out_A
    mrename_i pre
    mintro ∀σ_A
    mpure pre
    obtain ⟨A_used_sub, A_Λ_sub, A_keys_sub, A_cov, A_fv_sub, A_preserves⟩ := pre
    mspec C_ih (E := E) (Λ := σ_A.types) (used := σ_A.env.usedVars)
      (fun v hv => A_used_sub (vars_used_C v hv)) hC_bv_nodup
    clear C_ih
    rename_i out_C
    obtain ⟨C_enc, σC⟩ := out_C
    mrename_i pre
    mintro ∀σ_C
    mpure pre
    obtain ⟨C_used_sub, C_Λ_sub, C_keys_sub, C_cov, C_fv_sub, C_preserves⟩ := pre
    unfold castInter
    split <;> split <;> split <;> split
    · -- direct path : σA = σC = γ → bool
      rename_i _ Senc1 _ Senc2 _ _ _ gamma heqA heqC
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heqA
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heqC
      mspec SMT.freshVar_spec
      mrename_i pre
      mintro ∀St₁
      mpure pre
      obtain ⟨St₁_types_eq, x_fresh, St₁_fvc, St₁_used_eq, x_not_used⟩ := pre
      mspec Std.Do.Spec.pure
      mpure_intro
      rename_i x
      and_intros
      · intro v hv
        rw [St₁_used_eq]
        exact List.mem_cons_of_mem _ (C_used_sub (A_used_sub hv))
      · rw [St₁_types_eq]
        exact AList.subset_trans (AList.subset_trans A_Λ_sub C_Λ_sub)
          (SMT.TypeContext.entries_subset_insert_of_notMem x_fresh)
      · rw [St₁_types_eq, St₁_used_eq]
        exact keys_insert_subset_cons C_keys_sub
      · intro v hv
        rw [B.fv, List.mem_append] at hv
        rw [St₁_used_eq]
        rcases hv with hv | hv
        · exact List.mem_cons_of_mem _ (C_used_sub (A_cov v hv))
        · exact List.mem_cons_of_mem _ (C_cov v hv)
      · intro v hv
        simp only [SMT.fv, List.mem_removeAll_iff, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false] at hv
        obtain ⟨hv_body, hv_ne_x⟩ := hv
        rw [St₁_types_eq, ← AList.mem_keys, AList.mem_insert]
        refine Or.inr ?_
        rcases hv_body with (hvA | hvx) | (hvC | hvx)
        · exact AList.mem_keys.mpr (AList.mem_of_subset C_Λ_sub
            (AList.mem_keys.mpr (A_fv_sub hvA)))
        · exact absurd hvx hv_ne_x
        · exact AList.mem_keys.mpr (AList.mem_keys.mp (C_fv_sub hvC))
        · exact absurd hvx hv_ne_x
      · intro v hv hΛ hvars
        have hvA : v ∉ B.Term.vars A := fun h => hvars (by
          simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
          rcases h with h | h <;> [left; right] <;> exact .inl h)
        have hvC : v ∉ B.Term.vars C := fun h => hvars (by
          simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
          rcases h with h | h <;> [left; right] <;> exact .inr h)
        have hv_not_σC : v ∉ σ_C.types :=
          C_preserves v (A_used_sub hv) (A_preserves v hv hΛ hvA) hvC
        rw [St₁_types_eq]
        intro hv_in
        rw [AList.mem_insert] at hv_in
        rcases hv_in with rfl | hv_in
        · exact x_not_used (C_used_sub (A_used_sub hv))
        · exact hv_not_σC hv_in
    · mvcgen
    · -- σA ⊑ σC : castInterAux A_enc C_enc
      rename_i _ Senc1 _ heqA _ Senc2 _ heqC _ _
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heqA
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heqC
      mspec castInterAux_state
      case pre =>
        mpure_intro
        refine ⟨trivial, trivial, C_keys_sub, rfl, ?_, ?_⟩
        · intro v hv
          exact AList.mem_keys.mp (AList.mem_of_subset C_Λ_sub
            (AList.mem_keys.mpr (A_fv_sub hv)))
        · intro v hv
          exact C_fv_sub hv
      case post.success =>
        mrename_i hpost
        mintro ∀St'
        mpure hpost
        obtain ⟨h_le, h_Λ_sub, h_used_sub, h_keys_sub, h_fv_sub, h_preserves⟩ := hpost
        mpure_intro
        and_intros
        · exact fun v hv => h_used_sub (C_used_sub (A_used_sub hv))
        · exact AList.subset_trans (AList.subset_trans A_Λ_sub C_Λ_sub) h_Λ_sub
        · exact h_keys_sub
        · intro v hv
          rw [B.fv, List.mem_append] at hv
          rcases hv with hv | hv
          · exact h_used_sub (C_used_sub (A_cov v hv))
          · exact h_used_sub (C_cov v hv)
        · exact h_fv_sub
        · intro v hv hΛ hvars
          have hvA : v ∉ B.Term.vars A := fun h => hvars (by
            simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
            rcases h with h | h <;> [left; right] <;> exact .inl h)
          have hvC : v ∉ B.Term.vars C := fun h => hvars (by
            simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
            rcases h with h | h <;> [left; right] <;> exact .inr h)
          exact h_preserves v (C_used_sub (A_used_sub hv))
            (C_preserves v (A_used_sub hv) (A_preserves v hv hΛ hvA) hvC)
    · split
      · -- σC ⊑ σA : castInterAux C_enc A_enc
        rename_i _ Senc1 _ heqA _ Senc2 _ heqC _ _ _
        obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heqA
        obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heqC
        mspec castInterAux_state
        case pre =>
          mpure_intro
          refine ⟨trivial, trivial, C_keys_sub, rfl, ?_, ?_⟩
          · intro v hv
            exact C_fv_sub hv
          · intro v hv
            exact AList.mem_keys.mp (AList.mem_of_subset C_Λ_sub
              (AList.mem_keys.mpr (A_fv_sub hv)))
        case post.success =>
          mrename_i hpost
          mintro ∀St'
          mpure hpost
          obtain ⟨h_le, h_Λ_sub, h_used_sub, h_keys_sub, h_fv_sub, h_preserves⟩ := hpost
          mpure_intro
          and_intros
          · exact fun v hv => h_used_sub (C_used_sub (A_used_sub hv))
          · exact AList.subset_trans (AList.subset_trans A_Λ_sub C_Λ_sub) h_Λ_sub
          · exact h_keys_sub
          · intro v hv
            rw [B.fv, List.mem_append] at hv
            rcases hv with hv | hv
            · exact h_used_sub (C_used_sub (A_cov v hv))
            · exact h_used_sub (C_cov v hv)
          · exact h_fv_sub
          · intro v hv hΛ hvars
            have hvA : v ∉ B.Term.vars A := fun h => hvars (by
              simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
              rcases h with h | h <;> [left; right] <;> exact .inl h)
            have hvC : v ∉ B.Term.vars C := fun h => hvars (by
              simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
              rcases h with h | h <;> [left; right] <;> exact .inr h)
            exact h_preserves v (C_used_sub (A_used_sub hv))
              (C_preserves v (A_used_sub hv) (A_preserves v hv hΛ hvA) hvC)
      · mvcgen
  | pfun A C A_ih C_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
    rw [encodeTerm]
    have hA_bv_nodup : (B.bv A).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.1
    have hC_bv_nodup : (B.bv C).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.2.1
    have vars_used_A : ∀ v ∈ A.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h)
    have vars_used_C : ∀ v ∈ C.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inr h)
    mspec A_ih (E := E) (Λ := σ.types) vars_used_A hA_bv_nodup
    rename_i out_A
    obtain ⟨A_enc, σA⟩ := out_A
    mrename_i preA
    mintro ∀σ_A
    mpure preA
    obtain ⟨A_used_sub, A_Λ_sub, A_keys_sub, A_cov, A_fv_sub, A_preserves⟩ := preA
    split
    · rename_i heq
      injection heq with hAe hσe
      subst hσe
      subst hAe
      mspec C_ih (E := E) (Λ := σ_A.types) (used := σ_A.env.usedVars)
        (fun v hv => A_used_sub (vars_used_C v hv)) hC_bv_nodup
      rename_i out_C
      obtain ⟨C_enc, σC⟩ := out_C
      mrename_i preC
      mintro ∀σ_C
      mpure preC
      obtain ⟨C_used_sub, C_Λ_sub, C_keys_sub, C_cov, C_fv_sub, C_preserves⟩ := preC
      split
      · rename_i heq2
        injection heq2 with hCe hσe2
        subst hσe2
        subst hCe
        set ctx := σ_C.types with hctx
        mspec freshVar_spec (Γ := ctx) (used := σ_C.env.usedVars)
        case post.success R =>
          mrename_i pre
          mintro ∀St₁
          mpure pre
          obtain ⟨St₁_types_eq, R_fresh, St₁_fvc_eq, St₁_used_eq, R_not_used⟩ := pre
          mspec freshVar_spec (Γ := ctx.insert R _) (used := St₁.env.usedVars)
          case post.success x =>
            mrename_i pre
            mintro ∀St₂
            mpure pre
            obtain ⟨St₂_types_eq, x_fresh, St₂_fvc_eq, St₂_used_eq, x_not_used⟩ := pre
            mspec freshVar_spec (Γ := (ctx.insert R _).insert x _) (used := St₂.env.usedVars)
            case post.success y =>
              mrename_i pre
              mintro ∀St₃
              mpure pre
              obtain ⟨St₃_types_eq, y_fresh, St₃_fvc_eq, St₃_used_eq, y_not_used⟩ := pre
              mspec freshVar_spec
                (Γ := ((ctx.insert R _).insert x _).insert y _) (used := St₃.env.usedVars)
              case post.success y' =>
                mrename_i pre
                mintro ∀St₄
                mpure pre
                obtain ⟨St₄_types_eq, y'_fresh, St₄_fvc_eq, St₄_used_eq, y'_not_used⟩ := pre
                mspec Std.Do.Spec.pure
                mpure_intro
                and_intros
                · intro v hv
                  rw [St₄_used_eq, St₃_used_eq, St₂_used_eq, St₁_used_eq]
                  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                      (C_used_sub (A_used_sub hv)))))
                · intro v hv
                  rw [St₄_types_eq]
                  apply SMT.TypeContext.entries_subset_insert_of_notMem y'_fresh
                  apply SMT.TypeContext.entries_subset_insert_of_notMem y_fresh
                  apply SMT.TypeContext.entries_subset_insert_of_notMem x_fresh
                  apply SMT.TypeContext.entries_subset_insert_of_notMem R_fresh
                  exact AList.subset_trans A_Λ_sub C_Λ_sub hv
                · intro v hv
                  rw [St₄_used_eq, St₃_used_eq, St₂_used_eq, St₁_used_eq]
                  have hv' : v ∈ St₄.types := AList.mem_keys.mpr hv
                  rw [St₄_types_eq] at hv'
                  iterate 4 rw [AList.mem_insert] at hv'
                  rcases hv' with rfl | rfl | rfl | rfl | hv'
                  · exact List.mem_cons_self
                  · exact List.mem_cons_of_mem _ List.mem_cons_self
                  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
                  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                      (List.mem_cons_of_mem _ List.mem_cons_self))
                  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                        (C_keys_sub (AList.mem_keys.mp hv')))))
                · intro v hv
                  rw [B.fv, List.mem_append] at hv
                  rw [St₄_used_eq, St₃_used_eq, St₂_used_eq, St₁_used_eq]
                  rcases hv with hv | hv
                  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                        (C_used_sub (A_cov v hv)))))
                  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (C_cov v hv))))
                · intro v hv
                  simp only [SMT.fv, List.mem_removeAll_iff, List.mem_append,
                    List.mem_cons, List.not_mem_nil, or_false] at hv
                  obtain ⟨hv_body, hv_ne_R⟩ := hv
                  have hv_ctx : v ∈ ctx → v ∈ AList.keys St₄.types := fun hvc =>
                    AList.mem_keys.mp (by
                      rw [St₄_types_eq, AList.mem_insert, AList.mem_insert,
                        AList.mem_insert, AList.mem_insert]
                      exact Or.inr (Or.inr (Or.inr (Or.inr hvc))))
                  rcases hv_body with ⟨hv1, hv_ne_xy⟩ | ⟨hv2, hv_ne_xyy'⟩
                  · rcases hv1 with (hR | hx | hy) | (hvA | hx) | hvC | hy
                    · exact absurd hR hv_ne_R
                    · exact absurd (Or.inl hx) hv_ne_xy
                    · exact absurd (Or.inr hy) hv_ne_xy
                    · exact hv_ctx
                        (AList.mem_of_subset C_Λ_sub (AList.mem_keys.mp (A_fv_sub hvA)))
                    · exact absurd (Or.inl hx) hv_ne_xy
                    · exact hv_ctx (AList.mem_keys.mp (C_fv_sub hvC))
                    · exact absurd (Or.inr hy) hv_ne_xy
                  · rcases hv2 with ((hR | hx | hy) | hR | hx | hy') | hy | hy'
                    · exact absurd hR hv_ne_R
                    · exact absurd (Or.inl hx) hv_ne_xyy'
                    · exact absurd (Or.inr (Or.inl hy)) hv_ne_xyy'
                    · exact absurd hR hv_ne_R
                    · exact absurd (Or.inl hx) hv_ne_xyy'
                    · exact absurd (Or.inr (Or.inr hy')) hv_ne_xyy'
                    · exact absurd (Or.inr (Or.inl hy)) hv_ne_xyy'
                    · exact absurd (Or.inr (Or.inr hy')) hv_ne_xyy'
                · intro v hv hΛ hvars
                  have hvA : v ∉ B.Term.vars A := fun h => hvars (by
                    simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
                      List.mem_append] at h ⊢
                    rcases h with h | h <;> [left; right] <;> exact .inl h)
                  have hvC : v ∉ B.Term.vars C := fun h => hvars (by
                    simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
                      List.mem_append] at h ⊢
                    rcases h with h | h <;> [left; right] <;> exact .inr h)
                  have hv_not_ctx : v ∉ ctx :=
                    C_preserves v (A_used_sub hv) (A_preserves v hv hΛ hvA) hvC
                  rw [St₄_types_eq]
                  intro hv_in
                  iterate 4 rw [AList.mem_insert] at hv_in
                  rcases hv_in with rfl | rfl | rfl | rfl | hv_in
                  · exact y'_not_used (by
                      rw [St₃_used_eq, St₂_used_eq, St₁_used_eq]
                      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                        (List.mem_cons_of_mem _ (C_used_sub (A_used_sub hv)))))
                  · exact y_not_used (by
                      rw [St₂_used_eq, St₁_used_eq]
                      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                        (C_used_sub (A_used_sub hv))))
                  · exact x_not_used (by
                      rw [St₁_used_eq]
                      exact List.mem_cons_of_mem _ (C_used_sub (A_used_sub hv)))
                  · exact R_not_used (C_used_sub (A_used_sub hv))
                  · exact hv_not_ctx hv_in
      · mvcgen
    · mvcgen
  | app f x f_ih x_ih => sorry
  | collect vs D P D_ih P_ih => sorry
  | all vs D P D_ih P_ih => sorry
  | lambda vs D P D_ih P_ih => sorry

set_option maxHeartbeats 4000000 in
/-- Structural specification of `encodeTerm`: `encodeTerm_state` together with a
covering renaming witness. Consumed by the HAS-FLAG branch of `all_case`. -/
theorem encodeTerm_struct
    (E : B.Env) {Λ : SMT.TypeContext} {t : B.Term}
    {«Δ» : B.RenamingContext.Context}
    {Δ₀ : SMT.RenamingContext.Context}
    (Δ₀_ext : SMT.RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» t)
    {used : List SMT.𝒱}
    (Δ₀_none_out : ∀ v ∉ used, Δ₀ v = none)
    (vars_used : ∀ v ∈ t.vars, v ∈ used)
    (bv_nodup : (B.bv t).Nodup)
    {n : ℕ} :
    ⦃ fun (⟨E0, Λ'⟩ : EncoderState) ↦
        ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used⌝ ⦄
    encodeTerm t E
    ⦃ ⇓? (⟨t', _σ⟩ : SMT.Term × SMTType) (⟨E', Γ'⟩ : EncoderState) => ⌜
      used ⊆ E'.usedVars ∧
      Λ ⊆ Γ' ∧
      AList.keys Γ' ⊆ E'.usedVars ∧
      B.CoversUsedVars E'.usedVars t ∧
      SMT.fv t' ⊆ AList.keys Γ' ∧
      (∀ v ∈ used, v ∉ Λ → v ∉ B.Term.vars t → v ∉ Γ') ∧
      ∃ (Δ' : SMT.RenamingContext.Context)
        (_ : SMT.RenamingContext.CoversFV Δ' t'),
        SMT.RenamingContext.Extends Δ' Δ₀ ∧
          SMT.RenamingContext.ExtendsOnSourceFV Δ' «Δ» t ∧
          (∀ v ∉ E'.usedVars, Δ' v = none) ⌝⦄ := by
  mintro hpre ∀S
  mpure hpre
  obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := hpre
  mspec (encodeTerm_state E vars_used bv_nodup)
  mrename_i hpost
  mintro ∀S'
  mpure hpost
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hpost
  mpure_intro
  exact ⟨h1, h2, h3, h4, h5, h6,
    encodeTerm_struct.renaming_witness Δ₀_ext Δ₀_none_out h1 h3 h5⟩
