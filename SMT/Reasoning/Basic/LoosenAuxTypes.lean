import SMT.Reasoning.Basic.EncodeTermStruct

open Std.Do SMT

/-!
# Exact type-context footprint of proof-oriented loosening

The structural loosening specification proves monotonicity, but the `all`
soundness proof also needs the converse footprint fact: all recursive
temporaries are binder-local and erased, so only the returned helper remains
in the operational type context.
-/

private abbrev TypesEqPre (Λ : SMT.TypeContext) :
    Assertion (.arg EncoderState (.except String .pure)) :=
  fun ⟨_, Γ⟩ => ⌜Γ = Λ⌝

private abbrev TypesEqPost (α : Type) (Λ : SMT.TypeContext) :
    PostCond α (.arg EncoderState (.except String .pure)) :=
  ⇓? _ ⟨_, Γ⟩ => ⌜Γ = Λ⌝

private abbrev LoosenAuxTypesSpec
    {s t : SMTType} (c : s ~> t) : Prop :=
  ∀ {name : String} {x : SMT.Term} {Λ : SMT.TypeContext},
    ⦃TypesEqPre Λ⦄
      loosenAux_prf name c x
    ⦃⇓? ⟨v, _⟩ ⟨_, Γ⟩ =>
      ⌜Γ = Λ.insert v t ∧ v ∉ Λ⌝⦄

private theorem notMem_of_eq_insert
    {v w : SMT.𝒱} {τ : SMTType} {Γ Γ' : SMT.TypeContext}
    (hΓ : Γ' = Γ.insert w τ) (hv : v ∉ Γ') : v ∉ Γ := by
  intro h
  apply hv
  rw [hΓ, AList.mem_insert]
  exact Or.inr h

private theorem ne_of_eq_insert
    {v w : SMT.𝒱} {τ : SMTType} {Γ Γ' : SMT.TypeContext}
    (hΓ : Γ' = Γ.insert w τ) (hv : v ∉ Γ') : v ≠ w := by
  intro h
  subst v
  apply hv
  rw [hΓ, AList.mem_insert]
  exact Or.inl rfl

theorem defaultSpecM_types_eq
    (τ : SMTType) {name : String} {t : SMT.Term} {Λ : SMT.TypeContext} :
    ⦃TypesEqPre Λ⦄
      defaultSpecM name τ t
    ⦃TypesEqPost SMT.Term Λ⦄ := by
  induction τ generalizing name t Λ with
  | int | bool | unit | option =>
      mintro pre ∀St
      mpure pre
      subst Λ
      unfold defaultSpecM
      mspec Std.Do.Spec.pure
  | pair α β ihα ihβ =>
      mintro pre ∀St
      mpure pre
      subst Λ
      unfold defaultSpecM
      mspec ihα
      mrename_i pre
      mintro ∀St₁
      mpure pre
      mspec ihβ
  | «fun» α β _ihα ihβ =>
      mintro pre ∀St
      mpure pre
      subst Λ
      unfold defaultSpecM
      mspec SMT.freshVar_spec
      mrename_i pre
      mintro ∀St₁
      mpure pre
      obtain ⟨St₁_types, z_fresh, _, _, _⟩ := pre
      mspec ihβ
      mrename_i pre
      mintro ∀St₂
      mpure pre
      have St₂_types : St₂.types = St₁.types := pre
      mspec SMT.eraseFromContext_spec
      mrename_i pre
      mintro ∀St₃
      mpure pre
      obtain ⟨St₃_types, _, _⟩ := pre
      mspec Std.Do.Spec.pure
      mpure_intro
      rw [St₃_types, St₂_types, St₁_types,
        encodeTerm_state.erase_insert_self z_fresh]

private theorem loosenAux_prf_types_eq_pair
    {a b a' b' : SMTType} (ca : a ~> a') (cb : b ~> b')
    (iha : LoosenAuxTypesSpec ca) (ihb : LoosenAuxTypesSpec cb) :
    LoosenAuxTypesSpec (.pair ca cb) := by
  unfold LoosenAuxTypesSpec at iha ihb ⊢
  intro name x Λ
  mintro pre ∀St
  mpure pre
  subst Λ
  unfold loosenAux_prf
  mspec SMT.freshVar_spec
  rename_i x!
  mrename_i pre
  mintro ∀St₁
  mpure pre
  obtain ⟨St₁_types, x_fresh, _, _, _⟩ := pre
  mspec iha
  rename_i outa
  mrename_i prea
  mintro ∀St₂
  mpure prea
  obtain ⟨a!, _⟩ := outa
  obtain ⟨St₂_types_raw, a!_fresh_raw⟩ := prea
  have St₂_types : St₂.types = St₁.types.insert a! a' := by
    simpa using St₂_types_raw
  have a!_fresh : a! ∉ St₁.types := by
    simpa using a!_fresh_raw
  mspec ihb
  rename_i outb
  mrename_i preb
  mintro ∀St₃
  mpure preb
  obtain ⟨b!, _⟩ := outb
  obtain ⟨St₃_types_raw, b!_fresh_raw⟩ := preb
  have St₃_types : St₃.types = St₂.types.insert b! b' := by
    simpa using St₃_types_raw
  have b!_fresh : b! ∉ St₂.types := by
    simpa using b!_fresh_raw
  mspec SMT.eraseFromContext_spec
  mrename_i preE₁
  mintro ∀StE₁
  mpure preE₁
  obtain ⟨StE₁_types, _, _⟩ := preE₁
  mspec SMT.eraseFromContext_spec
  mrename_i preE₂
  mintro ∀StE₂
  mpure preE₂
  obtain ⟨StE₂_types, _, _⟩ := preE₂
  mspec Std.Do.Spec.pure
  mpure_intro
  have a_ne_b : a! ≠ b! := by
    intro h
    subst b!
    exact b!_fresh (St₂_types ▸
      (AList.mem_insert _ |>.mpr (.inl rfl)))
  refine ⟨?_, x_fresh⟩
  rw [StE₂_types, StE₁_types, St₃_types,
    encodeTerm_state.erase_insert_ne a_ne_b,
    encodeTerm_state.erase_insert_self
      (SMT.TypeContext.notMem_erase b!_fresh),
    St₂_types, encodeTerm_state.erase_insert_self a!_fresh,
    St₁_types]

/-- `loosenAux_prf` leaves exactly the returned helper in the type context;
all variables introduced recursively in its specification are erased. -/
theorem loosenAux_prf_types_eq
    {s t : SMTType} (c : s ~> t) {name : String} {x : SMT.Term}
    {Λ : SMT.TypeContext} :
    ⦃TypesEqPre Λ⦄
      loosenAux_prf name c x
    ⦃⇓? ⟨v, _⟩ ⟨_, Γ⟩ =>
      ⌜Γ = Λ.insert v t ∧ v ∉ Λ⌝⦄ := by
  induction c generalizing name x Λ with
  | refl τ =>
      mintro pre ∀St
      mpure pre
      subst Λ
      unfold loosenAux_prf
      mspec SMT.freshVar_spec
      rename_i x!
      mrename_i pre
      mintro ∀St₁
      mpure pre
      mspec Std.Do.Spec.pure
      mpure_intro
      exact ⟨pre.1, pre.2.1⟩
  | @graph α β α' β' cα cβ ihα ihβ =>
      mintro pre ∀St
      mpure pre
      subst Λ
      unfold loosenAux_prf
      mspec SMT.freshVar_spec
      rename_i x!
      mrename_i pre
      mintro ∀St₁
      mpure pre
      obtain ⟨St₁_types, x_fresh, _, _, _⟩ := pre
      mspec SMT.freshVar_spec
      rename_i z
      mrename_i pre
      mintro ∀St₂
      mpure pre
      obtain ⟨St₂_types, z_fresh, _, _, _⟩ := pre
      mspec (loosenAux_prf_types_eq_pair cα cβ ihα ihβ)
      rename_i zpair
      mrename_i pre
      mintro ∀St₃
      mpure pre
      obtain ⟨z!, _⟩ := zpair
      obtain ⟨St₃_types_raw, z!_fresh_raw⟩ := pre
      have St₃_types : St₃.types = St₂.types.insert z! (α'.pair β') := by
        simpa using St₃_types_raw
      have z!_fresh : z! ∉ St₂.types := by
        simpa using z!_fresh_raw
      mspec SMT.eraseFromContext_spec
      mrename_i preE₁
      mintro ∀StE₁
      mpure preE₁
      obtain ⟨StE₁_types, _, _⟩ := preE₁
      mspec SMT.eraseFromContext_spec
      mrename_i preE₂
      mintro ∀StE₂
      mpure preE₂
      obtain ⟨StE₂_types, _, _⟩ := preE₂
      mspec Std.Do.Spec.pure
      mpure_intro
      have z_ne_z! : z ≠ z! := by
        intro h
        subst z!
        exact z!_fresh (St₂_types ▸
          (AList.mem_insert _ |>.mpr (.inl rfl)))
      refine ⟨?_, x_fresh⟩
      rw [StE₂_types, StE₁_types, St₃_types,
        encodeTerm_state.erase_insert_ne z_ne_z!,
        encodeTerm_state.erase_insert_self
          (SMT.TypeContext.notMem_erase z!_fresh),
        St₂_types, encodeTerm_state.erase_insert_self z_fresh,
        St₁_types]
  | @chpred α α' c ih =>
      mintro pre ∀St
      mpure pre
      subst Λ
      unfold loosenAux_prf
      mspec SMT.freshVar_spec
      rename_i x!
      mrename_i pre
      mintro ∀St₁
      mpure pre
      obtain ⟨St₁_types, x_fresh, _, _, _⟩ := pre
      mspec SMT.freshVar_spec
      rename_i z
      mrename_i pre
      mintro ∀St₂
      mpure pre
      obtain ⟨St₂_types, z_fresh, _, _, _⟩ := pre
      mspec ih
      rename_i zout
      mrename_i pre
      mintro ∀St₃
      mpure pre
      obtain ⟨z!, _⟩ := zout
      obtain ⟨St₃_types_raw, z!_fresh_raw⟩ := pre
      have St₃_types : St₃.types = St₂.types.insert z! α' := by
        simpa using St₃_types_raw
      have z!_fresh : z! ∉ St₂.types := by
        simpa using z!_fresh_raw
      mspec SMT.eraseFromContext_spec
      mrename_i preE₁
      mintro ∀StE₁
      mpure preE₁
      obtain ⟨StE₁_types, _, _⟩ := preE₁
      mspec SMT.eraseFromContext_spec
      mrename_i preE₂
      mintro ∀StE₂
      mpure preE₂
      obtain ⟨StE₂_types, _, _⟩ := preE₂
      mspec Std.Do.Spec.pure
      mpure_intro
      have z_ne_z! : z ≠ z! := by
        intro h
        subst z!
        exact z!_fresh (St₂_types ▸
          (AList.mem_insert _ |>.mpr (.inl rfl)))
      refine ⟨?_, x_fresh⟩
      rw [StE₂_types, StE₁_types, St₃_types,
        encodeTerm_state.erase_insert_ne z_ne_z!,
        encodeTerm_state.erase_insert_self
          (SMT.TypeContext.notMem_erase z!_fresh),
        St₂_types, encodeTerm_state.erase_insert_self z_fresh,
        St₁_types]
  | @opt α α' c ih =>
      mintro pre ∀St
      mpure pre
      subst Λ
      unfold loosenAux_prf
      mspec SMT.freshVar_spec
      rename_i x!
      mrename_i pre
      mintro ∀St₁
      mpure pre
      obtain ⟨St₁_types, x_fresh, _, _, _⟩ := pre
      split <;> rename_i hx
      · mspec Std.Do.Spec.pure
      · mspec ih
        rename_i out
        mrename_i pre
        mintro ∀St₂
        mpure pre
        obtain ⟨y!, _⟩ := out
        obtain ⟨St₂_types_raw, y!_fresh_raw⟩ := pre
        have St₂_types : St₂.types = St₁.types.insert y! α' := by
          simpa using St₂_types_raw
        have y!_fresh : y! ∉ St₁.types := by
          simpa using y!_fresh_raw
        mspec SMT.eraseFromContext_spec
        mrename_i preE
        mintro ∀StE
        mpure preE
        obtain ⟨StE_types, _, _⟩ := preE
        mspec Std.Do.Spec.pure
        mpure_intro
        refine ⟨?_, x_fresh⟩
        rw [StE_types, St₂_types,
          encodeTerm_state.erase_insert_self y!_fresh, St₁_types]
      · mspec ih
        rename_i out
        mrename_i pre
        mintro ∀St₂
        mpure pre
        obtain ⟨y!, _⟩ := out
        obtain ⟨St₂_types_raw, y!_fresh_raw⟩ := pre
        have St₂_types : St₂.types = St₁.types.insert y! α' := by
          simpa using St₂_types_raw
        have y!_fresh : y! ∉ St₁.types := by
          simpa using y!_fresh_raw
        mspec SMT.eraseFromContext_spec
        mrename_i preE
        mintro ∀StE
        mpure preE
        obtain ⟨StE_types, _, _⟩ := preE
        mspec Std.Do.Spec.pure
        mpure_intro
        refine ⟨?_, x_fresh⟩
        rw [StE_types, St₂_types,
          encodeTerm_state.erase_insert_self y!_fresh, St₁_types]
  | @pair α β α' β' cα cβ ihα ihβ =>
      exact loosenAux_prf_types_eq_pair cα cβ ihα ihβ
  | @«fun» α β α' β' hβ cα cβ ihα ihβ =>
      mintro pre ∀St
      mpure pre
      subst Λ
      unfold loosenAux_prf
      mspec SMT.freshVar_spec
      rename_i x!
      mrename_i pre
      mintro ∀St₁
      mpure pre
      obtain ⟨St₁_types, x_fresh, _, _, _⟩ := pre
      mspec SMT.freshVar_spec
      rename_i a
      mrename_i preA
      mintro ∀StA
      mpure preA
      obtain ⟨StA_types, a_fresh, _, _, _⟩ := preA
      mspec ihα
      rename_i outA
      mrename_i preA!
      mintro ∀StA!
      mpure preA!
      obtain ⟨a!, _⟩ := outA
      obtain ⟨StA!_types_raw, a!_fresh_raw⟩ := preA!
      have StA!_types : StA!.types = StA.types.insert a! α' := by
        simpa using StA!_types_raw
      have a!_fresh : a! ∉ StA.types := by
        simpa using a!_fresh_raw
      mspec SMT.freshVar_spec
      rename_i b
      mrename_i preB
      mintro ∀StB
      mpure preB
      obtain ⟨StB_types, b_fresh, _, _, _⟩ := preB
      mspec ihβ
      rename_i outB
      mrename_i preB!
      mintro ∀StB!
      mpure preB!
      obtain ⟨b!, _⟩ := outB
      obtain ⟨StB!_types_raw, b!_fresh_raw⟩ := preB!
      have StB!_types : StB!.types = StB.types.insert b! β' := by
        simpa using StB!_types_raw
      have b!_fresh : b! ∉ StB.types := by
        simpa using b!_fresh_raw
      mspec defaultSpecM_types_eq
      mrename_i preD
      mintro ∀StD
      mpure preD
      have StD_types : StD.types = StB!.types := preD
      mspec SMT.eraseFromContext_spec
      mrename_i preE₁
      mintro ∀StE₁
      mpure preE₁
      obtain ⟨StE₁_types, _, _⟩ := preE₁
      mspec SMT.eraseFromContext_spec
      mrename_i preE₂
      mintro ∀StE₂
      mpure preE₂
      obtain ⟨StE₂_types, _, _⟩ := preE₂
      mspec SMT.eraseFromContext_spec
      mrename_i preE₃
      mintro ∀StE₃
      mpure preE₃
      obtain ⟨StE₃_types, _, _⟩ := preE₃
      mspec SMT.eraseFromContext_spec
      mrename_i preE₄
      mintro ∀StE₄
      mpure preE₄
      obtain ⟨StE₄_types, _, _⟩ := preE₄
      mspec Std.Do.Spec.pure
      mpure_intro
      have a!_fresh_St₁ : a! ∉ St₁.types :=
        notMem_of_eq_insert StA_types a!_fresh
      have b_fresh_StA : b ∉ StA.types :=
        notMem_of_eq_insert StA!_types b_fresh
      have b_fresh_St₁ : b ∉ St₁.types :=
        notMem_of_eq_insert StA_types b_fresh_StA
      have b!_fresh_StA! : b! ∉ StA!.types :=
        notMem_of_eq_insert StB_types b!_fresh
      have b!_fresh_StA : b! ∉ StA.types :=
        notMem_of_eq_insert StA!_types b!_fresh_StA!
      have b!_fresh_St₁ : b! ∉ St₁.types :=
        notMem_of_eq_insert StA_types b!_fresh_StA
      have a!_ne_a : a! ≠ a := ne_of_eq_insert StA_types a!_fresh
      have b_ne_a! : b ≠ a! := ne_of_eq_insert StA!_types b_fresh
      have b_ne_a : b ≠ a := ne_of_eq_insert StA_types b_fresh_StA
      have b!_ne_b : b! ≠ b := ne_of_eq_insert StB_types b!_fresh
      have b!_ne_a! : b! ≠ a! :=
        ne_of_eq_insert StA!_types b!_fresh_StA!
      have b!_ne_a : b! ≠ a :=
        ne_of_eq_insert StA_types b!_fresh_StA
      have hnodup : [a, a!, b, b!].Nodup := by
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
          or_false, not_or]
        exact ⟨⟨a!_ne_a.symm, b_ne_a.symm, b!_ne_a.symm⟩,
          ⟨⟨b_ne_a!.symm, b!_ne_a!.symm⟩,
            ⟨b!_ne_b.symm, ⟨by simp, List.nodup_nil⟩⟩⟩⟩
      have hdisj : ∀ p ∈
          [(a, α), (a!, α'), (b, β), (b!, β')],
          p.1 ∉ St₁.types := by
        intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl
        · exact a_fresh
        · exact a!_fresh_St₁
        · exact b_fresh_St₁
        · exact b!_fresh_St₁
      refine ⟨?_, x_fresh⟩
      rw [StE₄_types, StE₃_types, StE₂_types, StE₁_types,
        StD_types, StB!_types, StB_types, StA!_types, StA_types]
      have herase := encodeTerm_state.foldl_erase_foldl_insert
        [(a, α), (a!, α'), (b, β), (b!, β')]
        hnodup hdisj
      simpa only [List.map_cons, List.map_nil, List.foldl_cons,
        List.foldl_nil] using herase.trans St₁_types
