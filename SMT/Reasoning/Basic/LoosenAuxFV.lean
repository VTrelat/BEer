import SMT.Reasoning.Basic.EncodeTermBvUsed

open Std.Do SMT

/-! # Free-variable faithfulness of supported loosening paths -/

/-- Cast paths used by the representation grammar preserve source free
variables in the generated helper specification.  General function and option
casts are intentionally excluded: the representation-aware theorem never
selects them for canonicalization. -/
inductive castPath.FVFaithful : {a b : SMTType} → (a ~> b) → Prop where
  | refl {a} (h : a = SMTType.int ∨ a = SMTType.bool ∨ a = SMTType.unit) :
      FVFaithful (.refl h)
  | pair {a b a' b'} {ca : a ~> a'} {cb : b ~> b'} :
      FVFaithful ca → FVFaithful cb → FVFaithful (.pair ca cb)
  | graph {a b a' b'} {ca : a ~> a'} {cb : b ~> b'} :
      FVFaithful ca → FVFaithful cb → FVFaithful (.graph ca cb)
  | chpred {a a'} {c : a ~> a'} :
      FVFaithful c → FVFaithful (.chpred c)

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

set_option maxHeartbeats 4000000 in
/-- `loosenAux_prf` retains every source free variable in the generated
specification for the cast paths selected by `SupportedSMT`. -/
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

/-- Canonical SMT representations of B types use only FV-faithful casts. -/
theorem B.BType.reflexiveCast_fvFaithful (t : B.BType) :
    castPath.FVFaithful (castPath.reflexive t.toSMTType) := by
  induction t with
  | int => exact .refl (Or.inl rfl)
  | bool => exact .refl (Or.inr (Or.inl rfl))
  | prod a b iha ihb => exact .pair iha ihb
  | set t ih => exact .chpred ih
