import SMT.Reasoning.Basic.EncodeTermBvUsed

open Std.Do SMT

/-! # Free-variable faithfulness of supported loosening paths -/

/-- Cast paths preserve source free variables in the generated helper
specification. Structured option and function casts retain the source term in
their guarded specification even when recursive helper binders are erased. -/
inductive castPath.FVFaithful : {a b : SMTType} → (a ~> b) → Prop where
  | refl {a} (h : a = SMTType.int ∨ a = SMTType.bool ∨ a = SMTType.unit) :
      FVFaithful (.refl h)
  | pair {a b a' b'} {ca : a ~> a'} {cb : b ~> b'} :
      FVFaithful ca → FVFaithful cb → FVFaithful (.pair ca cb)
  | graph {a b a' b'} {ca : a ~> a'} {cb : b ~> b'} :
      FVFaithful ca → FVFaithful cb → FVFaithful (.graph ca cb)
  | chpred {a a'} {c : a ~> a'} :
      FVFaithful c → FVFaithful (.chpred c)
  | opt {a a'} {c : a ~> a'} :
      FVFaithful c → FVFaithful (.opt c)
  | «fun» {a b a' b'} {ca : a ~> a'} {cb : b ~> b'}
      (hb : b ≠ SMTType.bool) :
      FVFaithful ca → FVFaithful cb → FVFaithful (.fun hb ca cb)

set_option maxHeartbeats 2000000 in
private theorem loosenAux_prf_fv_pair
    {a b a' b' : SMTType} (ca : a ~> a') (cb : b ~> b')
    (ha : ∀ {used : List SMT.𝒱} {n : ℕ} {name : String}
      {x : SMT.Term},
      SMT.fv x ⊆ used →
      ⦃fun (⟨E, _⟩ : EncoderState) ↦
        ⌜E.freshvarsc = n ∧ E.usedVars = used⌝⦄
      loosenAux_prf name ca x
      ⦃⇓? (⟨v, spec⟩ : SMT.𝒱 × SMT.Term)
          (⟨E', _⟩ : EncoderState) =>
        ⌜v ∉ used ∧ SMT.fv x ⊆ SMT.fv spec ∧
          used ⊆ E'.usedVars⌝⦄)
    (hb : ∀ {used : List SMT.𝒱} {n : ℕ} {name : String}
      {x : SMT.Term},
      SMT.fv x ⊆ used →
      ⦃fun (⟨E, _⟩ : EncoderState) ↦
        ⌜E.freshvarsc = n ∧ E.usedVars = used⌝⦄
      loosenAux_prf name cb x
      ⦃⇓? (⟨v, spec⟩ : SMT.𝒱 × SMT.Term)
          (⟨E', _⟩ : EncoderState) =>
        ⌜v ∉ used ∧ SMT.fv x ⊆ SMT.fv spec ∧
          used ⊆ E'.usedVars⌝⦄)
    {used : List SMT.𝒱} {n : ℕ} {name : String} {x : SMT.Term}
    (hfv : SMT.fv x ⊆ used) :
    ⦃fun (⟨E, _⟩ : EncoderState) ↦
      ⌜E.freshvarsc = n ∧ E.usedVars = used⌝⦄
    loosenAux_prf name (.pair ca cb) x
    ⦃⇓? (⟨v, spec⟩ : SMT.𝒱 × SMT.Term)
        (⟨E', _⟩ : EncoderState) =>
      ⌜v ∉ used ∧ SMT.fv x ⊆ SMT.fv spec ∧
        used ⊆ E'.usedVars⌝⦄ := by
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl⟩ := pre
  unfold loosenAux_prf
  mspec SMT.freshVar_spec
  mrename_i pre
  mintro ∀St₁
  mpure pre
  obtain ⟨_, _, _, St₁_used, head_not_used⟩ := pre
  have hfv_fst : SMT.fv (.fst x) ⊆ St₁.env.usedVars := by
    intro v hv
    rw [St₁_used]
    exact List.mem_cons_of_mem _ (hfv (by simpa only [SMT.fv] using hv))
  mspec (ha hfv_fst)
  mrename_i pre
  mintro ∀St₂
  rename_i fst_out
  obtain ⟨fst!, fst!_spec⟩ := fst_out
  mpure pre
  obtain ⟨fst_fresh, fv_fst, used_sub_fst⟩ := pre
  have hfv_snd : SMT.fv (.snd x) ⊆ St₂.env.usedVars := by
    intro v hv
    exact used_sub_fst (by
      rw [St₁_used]
      exact List.mem_cons_of_mem _ (hfv (by simpa only [SMT.fv] using hv)))
  mspec (hb hfv_snd)
  mrename_i pre
  mintro ∀St₃
  rename_i snd_out
  obtain ⟨snd!, snd!_spec⟩ := snd_out
  mpure pre
  obtain ⟨snd_fresh, fv_snd, used_sub_snd⟩ := pre
  mspec SMT.eraseFromContext_spec
  mrename_i pre
  mintro ∀St₄
  mpure pre
  obtain ⟨_, _, St₄_used⟩ := pre
  mspec SMT.eraseFromContext_spec
  mrename_i pre
  mintro ∀St₅
  mpure pre
  obtain ⟨_, _, St₅_used⟩ := pre
  mspec Std.Do.Spec.pure
  mpure_intro
  rw [St₅_used, St₄_used]
  refine ⟨head_not_used, ?_, ?_⟩
  · intro v hv
    have hv_St₁ : v ∈ St₁.env.usedVars := by
      rw [St₁_used]
      exact List.mem_cons_of_mem _ (hfv hv)
    have hv_St₂ : v ∈ St₂.env.usedVars := used_sub_fst hv_St₁
    have hv_fst : v ∈ SMT.fv fst!_spec :=
      fv_fst (by simpa only [SMT.fv] using hv)
    have hv_ne_fst : v ≠ fst! := fun heq => fst_fresh (heq ▸ hv_St₁)
    have hv_ne_snd : v ≠ snd! := fun heq => snd_fresh (heq ▸ hv_St₂)
    simp only [SMT.fv, List.cons_append, List.nil_append]
    exact List.mem_removeAll_iff.mpr ⟨by
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_append_left _ hv_fst))), by
      intro hmem
      rcases List.mem_cons.mp hmem with h | hmem
      · exact hv_ne_fst h
      · exact hv_ne_snd (List.mem_singleton.mp hmem)⟩
  · intro v hv
    exact used_sub_snd (used_sub_fst (by
      rw [St₁_used]
      exact List.mem_cons_of_mem _ hv))

/-- `defaultSpecM` never removes a used name. This lightweight footprint is
enough for the free-variable proof of function casts and does not require a
type-context invariant. -/
private theorem defaultSpecM_used
    (tau : SMTType) {used : List SMT.𝒱}
    {name : String} {t : SMT.Term} :
    ⦃fun (⟨E, _⟩ : EncoderState) =>
      ⌜E.usedVars = used⌝⦄
    defaultSpecM name tau t
    ⦃⇓? (_ : SMT.Term) (⟨E', _⟩ : EncoderState) =>
      ⌜used ⊆ E'.usedVars⌝⦄ := by
  induction tau generalizing used name t with
  | int | bool | unit | option =>
      mintro pre ∀St
      mpure pre
      subst used
      unfold defaultSpecM
      mspec Std.Do.Spec.pure
      mpure_intro
      exact List.Subset.refl _
  | pair a b iha ihb =>
      mintro pre ∀St
      mpure pre
      subst used
      unfold defaultSpecM
      mspec iha
      mrename_i postA
      mintro ∀St1
      mpure postA
      mspec (ihb (used := St1.env.usedVars))
      mrename_i postB
      mintro ∀St2
      mpure postB
      mspec Std.Do.Spec.pure
      mpure_intro
      exact List.Subset.trans postA postB
  | «fun» a b _iha ihb =>
      mintro pre ∀St
      mpure pre
      subst used
      unfold defaultSpecM
      mspec SMT.freshVar_spec
      mrename_i preFresh
      mintro ∀St1
      mpure preFresh
      obtain ⟨_types, _fresh, _fvc, St1_used, _not_used⟩ := preFresh
      mspec (ihb (used := St1.env.usedVars))
      mrename_i postBody
      mintro ∀St2
      mpure postBody
      mspec SMT.eraseFromContext_spec
      mrename_i preErase
      mintro ∀St3
      mpure preErase
      obtain ⟨_typesErase, _fvcErase, St3_used⟩ := preErase
      mspec Std.Do.Spec.pure
      mpure_intro
      rw [St3_used]
      intro v hv
      apply postBody
      rw [St1_used]
      exact List.mem_cons_of_mem _ hv

set_option maxHeartbeats 4000000 in
/-- `loosenAux_prf` retains every source free variable in the generated
specification for every FV-faithful cast path. -/
theorem loosenAux_prf_fv_of_faithful
    {a b : SMTType} {c : a ~> b} (hc : castPath.FVFaithful c) :
    ∀ {used : List SMT.𝒱} {n : ℕ} {name : String} {x : SMT.Term},
    SMT.fv x ⊆ used →
    ⦃fun (⟨E, _⟩ : EncoderState) ↦
      ⌜E.freshvarsc = n ∧ E.usedVars = used⌝⦄
    loosenAux_prf name c x
    ⦃⇓? (⟨v, spec⟩ : SMT.𝒱 × SMT.Term)
        (⟨E', _⟩ : EncoderState) =>
      ⌜v ∉ used ∧ SMT.fv x ⊆ SMT.fv spec ∧
        used ⊆ E'.usedVars⌝⦄ := by
  induction hc with
  | refl h =>
      intro used n name x hfv
      mintro pre ∀St
      mpure pre
      obtain ⟨rfl, rfl⟩ := pre
      unfold loosenAux_prf
      mspec SMT.freshVar_spec
      mrename_i pre
      mintro ∀St₁
      mpure pre
      obtain ⟨_, _, _, St₁_used, head_not_used⟩ := pre
      mspec Std.Do.Spec.pure
      mpure_intro
      refine ⟨head_not_used, ?_, ?_⟩
      · intro v hv
        simp [SMT.fv, hv]
      · rw [St₁_used]
        exact fun _ hv => List.mem_cons_of_mem _ hv
  | pair ha hb iha ihb =>
      intro used n name x hfv
      exact loosenAux_prf_fv_pair _ _ iha ihb hfv
  | chpred hc ih =>
      intro used n name x hfv
      mintro pre ∀St
      mpure pre
      obtain ⟨rfl, rfl⟩ := pre
      unfold loosenAux_prf
      mspec SMT.freshVar_spec
      mrename_i pre
      mintro ∀St₁
      mpure pre
      obtain ⟨_, _, _, St₁_used, head_not_used⟩ := pre
      mspec SMT.freshVar_spec
      mrename_i pre
      mintro ∀St₂
      rename_i z
      mpure pre
      obtain ⟨_, _, _, St₂_used, z_not_used⟩ := pre
      mspec (ih (used := St₂.env.usedVars) (by
        intro v hv
        simp only [SMT.fv, List.mem_singleton] at hv
        subst v
        rw [St₂_used]
        exact List.mem_cons_self))
      mrename_i pre
      mintro ∀St₃
      rename_i z_out
      obtain ⟨z!, z!_spec⟩ := z_out
      mpure pre
      obtain ⟨z!_fresh, _fv_z, used_sub_z⟩ := pre
      mspec SMT.eraseFromContext_spec
      mrename_i pre
      mintro ∀St₄
      mpure pre
      obtain ⟨_, _, St₄_used⟩ := pre
      mspec SMT.eraseFromContext_spec
      mrename_i pre
      mintro ∀St₅
      mpure pre
      obtain ⟨_, _, St₅_used⟩ := pre
      mspec Std.Do.Spec.pure
      mpure_intro
      rw [St₅_used, St₄_used]
      refine ⟨head_not_used, ?_, ?_⟩
      · intro v hv
        have hv_St₁ : v ∈ St₁.env.usedVars := by
          rw [St₁_used]
          exact List.mem_cons_of_mem _ (hfv hv)
        have hv_ne_z : v ≠ z := fun heq => z_not_used (heq ▸ hv_St₁)
        have hv_St₂ : v ∈ St₂.env.usedVars := by
          rw [St₂_used]
          exact List.mem_cons_of_mem _ hv_St₁
        have hv_ne_z! : v ≠ z! := fun heq => z!_fresh (heq ▸ hv_St₂)
        have hv_not_z : v ∉ [z] := by
          intro hz
          exact hv_ne_z (List.mem_singleton.mp hz)
        have hv_not_z! : v ∉ [z!] := by
          intro hz
          exact hv_ne_z! (List.mem_singleton.mp hz)
        simp only [SMT.fv, List.cons_append, List.nil_append]
        have hv_body₁ : v ∈ SMT.fv x ++ [z] := List.mem_append_left _ hv
        have hv_body : v ∈ (SMT.fv x ++ [z]) ++ SMT.fv z!_spec :=
          List.mem_append_left _ hv_body₁
        exact List.mem_cons_of_mem _ (List.mem_removeAll_iff.mpr ⟨
          List.mem_removeAll_iff.mpr ⟨hv_body, hv_not_z⟩, hv_not_z!⟩)
      · intro v hv
        exact used_sub_z (by
          rw [St₂_used, St₁_used]
          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hv))
  | graph ha hb iha ihb =>
      intro used n name x hfv
      mintro pre ∀St
      mpure pre
      obtain ⟨rfl, rfl⟩ := pre
      unfold loosenAux_prf
      mspec SMT.freshVar_spec
      mrename_i pre
      mintro ∀St₁
      mpure pre
      obtain ⟨_, _, _, St₁_used, head_not_used⟩ := pre
      mspec SMT.freshVar_spec
      mrename_i pre
      mintro ∀St₂
      rename_i z
      mpure pre
      obtain ⟨_, _, _, St₂_used, z_not_used⟩ := pre
      mspec (loosenAux_prf_fv_pair _ _ iha ihb
        (used := St₂.env.usedVars) (by
        intro v hv
        simp only [SMT.fv, List.mem_singleton] at hv
        subst v
        rw [St₂_used]
        exact List.mem_cons_self))
      mrename_i pre
      mintro ∀St₃
      rename_i z_out
      obtain ⟨z!, z!_spec⟩ := z_out
      mpure pre
      obtain ⟨z!_fresh, _fv_z, used_sub_z⟩ := pre
      mspec SMT.eraseFromContext_spec
      mrename_i pre
      mintro ∀St₄
      mpure pre
      obtain ⟨_, _, St₄_used⟩ := pre
      mspec SMT.eraseFromContext_spec
      mrename_i pre
      mintro ∀St₅
      mpure pre
      obtain ⟨_, _, St₅_used⟩ := pre
      mspec Std.Do.Spec.pure
      mpure_intro
      rw [St₅_used, St₄_used]
      refine ⟨head_not_used, ?_, ?_⟩
      · intro v hv
        have hv_St₁ : v ∈ St₁.env.usedVars := by
          rw [St₁_used]
          exact List.mem_cons_of_mem _ (hfv hv)
        have hv_ne_z : v ≠ z := fun heq => z_not_used (heq ▸ hv_St₁)
        have hv_St₂ : v ∈ St₂.env.usedVars := by
          rw [St₂_used]
          exact List.mem_cons_of_mem _ hv_St₁
        have hv_ne_z! : v ≠ z! := fun heq => z!_fresh (heq ▸ hv_St₂)
        have hv_not_z : v ∉ [z] := by
          intro hz
          exact hv_ne_z (List.mem_singleton.mp hz)
        have hv_not_z! : v ∉ [z!] := by
          intro hz
          exact hv_ne_z! (List.mem_singleton.mp hz)
        simp only [SMT.fv, List.cons_append, List.nil_append]
        have hv_body₁ : v ∈ SMT.fv x ++ [z] := List.mem_append_left _ hv
        have hv_body₂ : v ∈ (SMT.fv x ++ [z]) ++ [z] :=
          List.mem_append_left _ hv_body₁
        have hv_body : v ∈ ((SMT.fv x ++ [z]) ++ [z]) ++ SMT.fv z!_spec :=
          List.mem_append_left _ hv_body₂
        exact List.mem_cons_of_mem _ (List.mem_removeAll_iff.mpr ⟨
          List.mem_removeAll_iff.mpr ⟨hv_body, hv_not_z⟩, hv_not_z!⟩)
      · intro v hv
        exact used_sub_z (by
          rw [St₂_used, St₁_used]
          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hv))
  | opt hc ih =>
      intro used n name x hfv
      mintro pre ∀St
      mpure pre
      obtain ⟨rfl, rfl⟩ := pre
      unfold loosenAux_prf
      mspec SMT.freshVar_spec
      mrename_i pre
      mintro ∀St1
      rename_i helper
      mpure pre
      obtain ⟨_, _, _, St1_used, head_not_used⟩ := pre
      split
      · rename_i helper
        mspec Std.Do.Spec.pure
        mpure_intro
        refine ⟨head_not_used, ?_, ?_⟩
        · intro v hv
          simp [SMT.fv] at hv
        · rw [St1_used]
          exact fun _ hv => List.mem_cons_of_mem _ hv
      · rename_i helper x0
        mspec (ih (used := St1.env.usedVars) (by
          intro v hv
          rw [St1_used]
          exact List.mem_cons_of_mem _ (hfv (by
            simpa only [SMT.fv] using hv))))
        mrename_i pre
        mintro ∀St2
        mpure pre
        rename_i out
        obtain ⟨inner, innerSpec⟩ := out
        obtain ⟨inner_fresh, fv_inner, used_sub_inner⟩ := pre
        mspec SMT.eraseFromContext_spec
        mrename_i pre
        mintro ∀St3
        mpure pre
        obtain ⟨_, _, St3_used⟩ := pre
        mspec Std.Do.Spec.pure
        mpure_intro
        rw [St3_used]
        refine ⟨head_not_used, ?_, ?_⟩
        · intro v hv
          have hv_St1 : v ∈ St1.env.usedVars := by
            rw [St1_used]
            exact List.mem_cons_of_mem _ (hfv (by
              simpa only [SMT.fv] using hv))
          have hv_ne_inner : v ≠ inner :=
            fun heq => inner_fresh (heq ▸ hv_St1)
          have hv_spec : v ∈ SMT.fv innerSpec :=
            fv_inner (by simpa only [SMT.fv] using hv)
          simp only [SMT.fv, List.mem_append, List.mem_removeAll_iff,
            List.mem_cons, List.not_mem_nil, or_false]
          exact ⟨Or.inr hv_spec, by
            intro hmem
            exact hv_ne_inner hmem⟩
        · intro v hv
          apply used_sub_inner
          rw [St1_used]
          exact List.mem_cons_of_mem _ hv
      · rename_i helper x_ne_none x_ne_some
        mspec (ih (used := St1.env.usedVars) (by
          intro v hv
          rw [St1_used]
          exact List.mem_cons_of_mem _ (hfv (by
            simpa only [SMT.fv] using hv))))
        mrename_i pre
        mintro ∀St2
        mpure pre
        rename_i out
        obtain ⟨inner, innerSpec⟩ := out
        obtain ⟨_inner_fresh, _fv_inner, used_sub_inner⟩ := pre
        mspec SMT.eraseFromContext_spec
        mrename_i pre
        mintro ∀St3
        mpure pre
        obtain ⟨_, _, St3_used⟩ := pre
        mspec Std.Do.Spec.pure
        mpure_intro
        rw [St3_used]
        refine ⟨head_not_used, ?_, ?_⟩
        · intro v hv
          simp only [noneCast, SMT.fv, List.mem_append,
            List.mem_removeAll_iff, List.mem_cons,
            List.not_mem_nil, or_false]
          exact Or.inl (Or.inl hv)
        · intro v hv
          apply used_sub_inner
          rw [St1_used]
          exact List.mem_cons_of_mem _ hv
  | «fun» hb hca hcb iha ihb =>
      intro used n name x hfv
      mintro pre ∀St
      mpure pre
      obtain ⟨rfl, rfl⟩ := pre
      unfold loosenAux_prf
      mspec SMT.freshVar_spec
      mrename_i pre
      mintro ∀St1
      mpure pre
      obtain ⟨_, _, _, St1_used, helper_not_used⟩ := pre
      mspec SMT.freshVar_spec
      mrename_i pre
      mintro ∀St2
      rename_i arg
      mpure pre
      obtain ⟨_, _, _, St2_used, a_not_used⟩ := pre
      mspec (iha (used := St2.env.usedVars) (by
        intro v hv
        simp only [SMT.fv, List.mem_singleton] at hv
        subst v
        rw [St2_used]
        exact List.mem_cons_self))
      mrename_i pre
      mintro ∀St3
      rename_i aOut
      mpure pre
      obtain ⟨aHelper, aSpec⟩ := aOut
      obtain ⟨aHelper_fresh, _fv_a, used_sub_a⟩ := pre
      mspec SMT.freshVar_spec
      mrename_i pre
      mintro ∀St4
      rename_i ret
      mpure pre
      obtain ⟨_, _, _, St4_used, b_not_used⟩ := pre
      mspec (ihb (used := St4.env.usedVars) (by
        intro v hv
        simp only [SMT.fv, List.mem_singleton] at hv
        subst v
        rw [St4_used]
        exact List.mem_cons_self))
      mrename_i pre
      mintro ∀St5
      rename_i bOut
      mpure pre
      obtain ⟨bHelper, bSpec⟩ := bOut
      obtain ⟨bHelper_fresh, _fv_b, used_sub_b⟩ := pre
      mspec (defaultSpecM_used _ (used := St5.env.usedVars))
      mrename_i pre
      mintro ∀St6
      rename_i defaultSpec
      mpure pre
      have used_sub_default := pre
      mspec SMT.eraseFromContext_spec
      mrename_i pre
      mintro ∀StE1
      mpure pre
      obtain ⟨_, _, StE1_used⟩ := pre
      mspec SMT.eraseFromContext_spec
      mrename_i pre
      mintro ∀StE2
      mpure pre
      obtain ⟨_, _, StE2_used⟩ := pre
      mspec SMT.eraseFromContext_spec
      mrename_i pre
      mintro ∀StE3
      mpure pre
      obtain ⟨_, _, StE3_used⟩ := pre
      mspec SMT.eraseFromContext_spec
      mrename_i pre
      mintro ∀StE4
      mpure pre
      obtain ⟨_, _, StE4_used⟩ := pre
      mspec Std.Do.Spec.pure
      mpure_intro
      rw [StE4_used, StE3_used, StE2_used, StE1_used]
      refine ⟨helper_not_used, ?_, ?_⟩
      · intro v hv
        have hv_St1 : v ∈ St1.env.usedVars := by
          rw [St1_used]
          exact List.mem_cons_of_mem _ (hfv hv)
        have hv_St2 : v ∈ St2.env.usedVars := by
          rw [St2_used]
          exact List.mem_cons_of_mem _ hv_St1
        have hv_St3 : v ∈ St3.env.usedVars := used_sub_a hv_St2
        have hv_St4 : v ∈ St4.env.usedVars := by
          rw [St4_used]
          exact List.mem_cons_of_mem _ hv_St3
        have hv_ne_a : v ≠ arg := fun heq => a_not_used (heq ▸ hv_St1)
        have hv_ne_aHelper : v ≠ aHelper :=
          fun heq => aHelper_fresh (heq ▸ hv_St2)
        have hv_ne_b : v ≠ ret := fun heq => b_not_used (heq ▸ hv_St3)
        have hv_ne_bHelper : v ≠ bHelper :=
          fun heq => bHelper_fresh (heq ▸ hv_St4)
        simp only [SMT.fv, List.mem_removeAll_iff, List.mem_append,
          List.mem_cons, List.not_mem_nil, or_false]
        refine ⟨Or.inl (Or.inr ?_), hv_ne_aHelper⟩
        refine ⟨Or.inr ?_, hv_ne_bHelper⟩
        refine ⟨Or.inl (Or.inl (Or.inl hv)), ?_⟩
        intro hab
        rcases hab with ha | hb
        · exact hv_ne_a ha
        · exact hv_ne_b hb
      · intro v hv
        apply used_sub_default
        apply used_sub_b
        rw [St4_used]
        apply List.mem_cons_of_mem
        apply used_sub_a
        rw [St2_used]
        apply List.mem_cons_of_mem
        rw [St1_used]
        exact List.mem_cons_of_mem _ hv

/-- Every cast path is syntactically free-variable faithful. -/
theorem castPath.fvFaithful {a b : SMTType} (c : a ~> b) :
    castPath.FVFaithful c := by
  induction c with
  | refl h => exact .refl h
  | graph ca cb iha ihb => exact .graph iha ihb
  | chpred c ih => exact .chpred ih
  | «fun» hb ca cb iha ihb => exact .fun hb iha ihb
  | pair ca cb iha ihb => exact .pair iha ihb
  | opt c ih => exact .opt ih

/-- Canonical SMT representations of B types use only FV-faithful casts. -/
theorem B.BType.reflexiveCast_fvFaithful (t : B.BType) :
    castPath.FVFaithful (castPath.reflexive t.toSMTType) := by
  induction t with
  | int => exact .refl (Or.inl rfl)
  | bool => exact .refl (Or.inr (Or.inl rfl))
  | prod a b iha ihb => exact .pair iha ihb
  | set t ih => exact .chpred ih
