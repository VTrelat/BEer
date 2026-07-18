import SMT.Reasoning.Basic.CastMembershipSpec
import SMT.Reasoning.Basic.LoosenAuxExactUniv
import SMT.Reasoning.Basic.EncodeTermStruct
import SMT.Reasoning.Basic.LoosenAuxFV
import SMT.Reasoning.Basic.LoosenAuxTypes

open Std.Do

set_option maxHeartbeats 3000000 in
/-- Exact branch-2 specification for membership casting.  Besides producing a
cast witness whose specification is true, every well-typed helper value whose
specification evaluates to true is proved to lie in the cast relation.  This
second direction is what makes universal helper re-scoping sound. -/
theorem castMembership_branch2_exact_spec.{u}
    {α τ : SMT.SMTType} {x S : SMT.Term} {Λ : SMT.TypeContext} {n : ℕ}
    (typ_x : Λ ⊢ˢ x : α) (typ_S : Λ ⊢ˢ S : .fun τ .bool)
    (α_ne_τ : α ≠ τ) (α_le_τ : α ⊑ τ)
    (hfaith : castPath.FVFaithful α_le_τ.toCastPath)
    {used : List SMT.𝒱} {decl : SMT.Chunk}
    (hbv_x : ∀ v ∈ SMT.bv x, v ∈ used)
    (hbv_S : ∀ v ∈ SMT.bv S, v ∈ used) :
    ⦃ fun ⟨E, Λ'⟩ =>
        ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ AList.keys Λ ⊆ E.usedVars ∧
          E.usedVars = used ∧ E.declarations = decl⌝ ⦄
      castMembership ⟨x, α⟩ ⟨S, .fun τ .bool⟩
    ⦃ ⇓? ⟨t, σ⟩ ⟨E', Λ'⟩ => ⌜
      n ≤ E'.freshvarsc ∧ Λ ⊆ Λ' ∧
      AList.keys Λ' ⊆ E'.usedVars ∧ used ⊆ E'.usedVars ∧
      σ = .bool ∧ Λ' ⊢ˢ t : .bool ∧
      (∀ v ∈ SMT.fv t,
        v ∈ SMT.fv x ∨ v ∈ SMT.fv S ∨ v ∉ Λ) ∧
      (∀ v ∈ used, v ∉ Λ → v ∉ Λ') ∧
      (∀ (Δctx : SMT.RenamingContext.Context.{u})
          (hcov_t : SMT.RenamingContext.CoversFV Δctx t)
          (_hcompat : SMT.RenamingContext.RespectsTypeContext Δctx Λ'),
        ∃ denCM : SMT.Dom.{u},
          ⟦t.abstract Δctx hcov_t⟧ˢ = some denCM ∧
          denCM.snd.fst = .bool) ∧
      ∃ (x! : SMT.𝒱) (x!_spec : SMT.Term),
        E'.declarations = decl ++ helperSpecChunk x! τ x!_spec ∧
        t = x!_spec ∧ˢ .app S (.var x!) ∧
        x! ∉ Λ ∧ x! ∉ used ∧
        Λ'.lookup x! = some τ ∧
        Λ' = Λ.insert x! τ ∧
        SMT.fv x!_spec ⊆ SMT.fv x ∪ [x!] ∧
        SMT.fv x ⊆ SMT.fv x!_spec ∧
        ∀ («Δctx» : SMT.RenamingContext.Context.{u})
          (hx : SMT.RenamingContext.CoversFV «Δctx» x)
          (_respects : SMT.RenamingContext.RespectsTypeContextOnFV
            «Δctx» Λ x)
          (pf : ∀ (x_! : SMT.𝒱) (X! : SMT.Dom),
            ∀ v ∈ SMT.fv (SMT.Term.var x_!),
              (Function.update «Δctx» x_! (some X!) v).isSome = true),
        ∀ (X : SMT.Dom), ⟦x.abstract «Δctx» hx⟧ˢ = some X →
          ∃ (Φ X! : SMT.Dom)
            (_ : ⟦(SMT.Term.var x!).abstract
              (Function.update «Δctx» x! (some X!)) (pf x! X!)⟧ˢ = some X!)
            (hφ : SMT.RenamingContext.CoversFV
              (Function.update «Δctx» x! (some X!)) x!_spec)
            (_ : ⟦x!_spec.abstract
              (Function.update «Δctx» x! (some X!)) hφ⟧ˢ = some Φ),
            X!.2.1 = τ ∧
            Φ.2.1 = SMT.SMTType.bool ∧
            (Φ.1 = ZFSet.zftrue ∧
              (X.1.pair X!.1) ∈ (castZF_of_path α_le_τ.toCastPath).1) ∧
            ∀ (Y : SMT.Dom) (_ : Y.2.1 = τ)
              (hφY : SMT.RenamingContext.CoversFV
                (Function.update «Δctx» x! (some Y)) x!_spec),
              (⟦x!_spec.abstract
                (Function.update «Δctx» x! (some Y)) hφY⟧ˢ).isSome = true ∧
              ∀ {ΦY : SMT.Dom},
                ⟦x!_spec.abstract
                  (Function.update «Δctx» x! (some Y)) hφY⟧ˢ = some ΦY →
                ΦY.1 = ZFSet.zftrue →
                (X.1.pair Y.1) ∈
                  (castZF_of_path α_le_τ.toCastPath).1⌝ ⦄ := by
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_sub, St_used_eq, St_decl_eq⟩ := pre
  unfold castMembership
  conv =>
    enter [2, 1, 1]
    simp only [bind_pure_comp]
  rw [dif_neg α_ne_τ, dif_pos α_le_τ]
  mspec (Std.Do.Triple.and _
    (Std.Do.Triple.and _
      (Std.Do.Triple.and _
        (loosenAux_prf_exact_univ
          (Λ := St.types) (n := St.env.freshvarsc)
          (used := St.env.usedVars) typ_x
          (fun v hv => St_used_eq ▸ hbv_x v hv) α_le_τ.toCastPath)
        (loosenAux_prf_fv_of_faithful hfaith
          (used := St.env.usedVars) (n := St.env.freshvarsc)
          (x := x) (by
            intro v hv
            exact St_sub (SMT.Typing.mem_context_of_mem_fv typ_x hv))))
      (loosenAux_prf_decls α_le_τ.toCastPath
        (decl := decl)))
    (loosenAux_prf_types_eq α_le_τ.toCastPath))
  next out =>
  obtain ⟨x!, x!_spec⟩ := out
  mrename_i pre
  mintro ∀St1
  mpure pre
  obtain ⟨⟨⟨⟨hn1, St1_types_eq, x!_fresh, x!_not_used,
    used_sub1, keys_sub1, preserves1, typ_x!, typ_x!_spec,
    typ_x!_St1, typ_x!_spec_St1, fv_x!_spec, hadq_univ⟩,
    _x!_not_used_fv, fv_x_spec, _used_sub_fv⟩,
    St1_decl_eq⟩, ⟨St1_types_exact, _⟩⟩ := pre
  mspec Std.Do.Spec.map
  mspec SMT.declareConst_addSpec_spec
    (x! := x!) (x!_spec := x!_spec) (τ := τ) (decl := St1.env.declarations)
    (as := St1.env.asserts) (n := St1.env.freshvarsc)
    (Γ := St1.types) (used := St1.env.usedVars)
  mrename_i pre
  mintro ∀St2
  mpure pre
  obtain ⟨St2_decl_eq, _, St2_fvc_eq, St2_used_eq, St2_types_eq⟩ := pre
  have typ_full :
      St2.types ⊢ˢ x!_spec ∧ˢ .app S (.var x!) : .bool := by
    rw [St2_types_eq]
    apply SMT.Typing.and
    · exact typ_x!_spec_St1
    · apply SMT.Typing.app
      · exact SMT.Typing.weakening
          (h := fun v hv => St1_types_eq
            (SMT.TypeContext.entries_subset_insert_of_notMem x!_fresh hv))
          typ_S
          (fun v hv => preserves1 v (St_used_eq ▸ hbv_S v hv)
            (SMT.Typing.bv_notMem_context typ_S v hv))
      · exact typ_x!_St1
  mpure_intro
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [St2_fvc_eq]
    exact hn1
  · intro v hv
    rw [St2_types_eq]
    exact St1_types_eq
      (SMT.TypeContext.entries_subset_insert_of_notMem x!_fresh hv)
  · rw [St2_types_eq, St2_used_eq]
    exact keys_sub1
  · rw [← St_used_eq, St2_used_eq]
    exact used_sub1
  · trivial
  · exact typ_full
  · intro v hv
    simp only [SMT.fv, List.mem_append, List.mem_singleton] at hv
    rcases hv with h_spec | h_S | rfl
    · have hmem := fv_x!_spec h_spec
      rcases List.mem_union_iff.mp hmem with hx | hx_in
      · exact Or.inl hx
      · have heq : v = x! := List.mem_singleton.mp hx_in
        subst heq
        exact Or.inr (Or.inr (fun hΛ => x!_fresh hΛ))
    · exact Or.inr (Or.inl h_S)
    · exact Or.inr (Or.inr (fun hΛ => x!_fresh hΛ))
  · intro v hv_used hv_notΛ
    rw [St2_types_eq]
    rw [St_used_eq] at preserves1
    exact preserves1 v hv_used hv_notΛ
  · intro Δctx hcov_t hcompat
    exact SMT.RenamingContext.denote_exists_of_typing
      typ_full hcompat hcov_t
  · refine ⟨x!, x!_spec, ?_, rfl, x!_fresh, ?_, ?_, ?_, fv_x!_spec,
      fv_x_spec, ?_⟩
    · rw [St2_decl_eq, St1_decl_eq]
      simp [helperSpecChunk, List.concat_eq_append, List.append_assoc]
    · rw [St_used_eq] at x!_not_used
      exact x!_not_used
    · rw [St2_types_eq]
      exact SMT.Typing.varE typ_x!_St1
    · rw [St2_types_eq]
      exact St1_types_exact
    · intro Δctx hx respects pf X hX_den
      obtain ⟨Φ, X!, hvar, hφ, hspec, hX!ty,
        hΦty, hcast, htot⟩ :=
        hadq_univ Δctx hx respects pf X hX_den
      exact ⟨Φ, X!, hvar, hφ, hspec, hX!ty, hΦty, hcast, htot⟩

set_option maxHeartbeats 3000000 in
/-- Exact branch-3 specification for membership casting.  The set predicate is
cast to the argument representation, and its helper guard characterizes the
chosen characteristic-predicate cast in both directions. -/
theorem castMembership_branch3_exact_spec.{u}
    {α τ : SMT.SMTType} {x S : SMT.Term} {Λ : SMT.TypeContext} {n : ℕ}
    (typ_x : Λ ⊢ˢ x : α) (typ_S : Λ ⊢ˢ S : .fun τ .bool)
    (α_ne_τ : α ≠ τ) (α_not_le_τ : ¬ α ⊑ τ) (τ_le_α : τ ⊑ α)
    (hfaith : castPath.FVFaithful (castPath.chpred τ_le_α.toCastPath))
    {used : List SMT.𝒱} {decl : SMT.Chunk}
    (hbv_x : ∀ v ∈ SMT.bv x, v ∈ used)
    (hbv_S : ∀ v ∈ SMT.bv S, v ∈ used) :
    ⦃ fun ⟨E, Λ'⟩ =>
        ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ AList.keys Λ ⊆ E.usedVars ∧
          E.usedVars = used ∧ E.declarations = decl⌝ ⦄
      castMembership ⟨x, α⟩ ⟨S, .fun τ .bool⟩
    ⦃ ⇓? ⟨t, σ⟩ ⟨E', Λ'⟩ => ⌜
      n ≤ E'.freshvarsc ∧ Λ ⊆ Λ' ∧
      AList.keys Λ' ⊆ E'.usedVars ∧ used ⊆ E'.usedVars ∧
      σ = .bool ∧ Λ' ⊢ˢ t : .bool ∧
      (∀ v ∈ SMT.fv t,
        v ∈ SMT.fv x ∨ v ∈ SMT.fv S ∨ v ∉ Λ) ∧
      (∀ v ∈ used, v ∉ Λ → v ∉ Λ') ∧
      (∀ (Δctx : SMT.RenamingContext.Context.{u})
          (hcov_t : SMT.RenamingContext.CoversFV Δctx t)
          (_hcompat : SMT.RenamingContext.RespectsTypeContext Δctx Λ'),
        ∃ denCM : SMT.Dom.{u},
          ⟦t.abstract Δctx hcov_t⟧ˢ = some denCM ∧
          denCM.snd.fst = .bool) ∧
      ∃ (S! : SMT.𝒱) (S!_spec : SMT.Term),
        E'.declarations = decl ++
          helperSpecChunk S! (.fun α .bool) S!_spec ∧
        t = S!_spec ∧ˢ .app (.var S!) x ∧
        S! ∉ Λ ∧ S! ∉ used ∧
        Λ'.lookup S! = some (.fun α .bool) ∧
        Λ' = Λ.insert S! (.fun α .bool) ∧
        SMT.fv S!_spec ⊆ SMT.fv S ∪ [S!] ∧
        SMT.fv S ⊆ SMT.fv S!_spec ∧
        ∀ («Δctx» : SMT.RenamingContext.Context.{u})
          (hS : SMT.RenamingContext.CoversFV «Δctx» S)
          (_respects : SMT.RenamingContext.RespectsTypeContextOnFV
            «Δctx» Λ S)
          (pf : ∀ (S_! : SMT.𝒱) (F! : SMT.Dom),
            ∀ v ∈ SMT.fv (SMT.Term.var S_!),
              (Function.update «Δctx» S_! (some F!) v).isSome = true),
        ∀ (F : SMT.Dom), ⟦S.abstract «Δctx» hS⟧ˢ = some F →
          ∃ (Φ F! : SMT.Dom)
            (_ : ⟦(SMT.Term.var S!).abstract
              (Function.update «Δctx» S! (some F!)) (pf S! F!)⟧ˢ = some F!)
            (hφ : SMT.RenamingContext.CoversFV
              (Function.update «Δctx» S! (some F!)) S!_spec)
            (_ : ⟦S!_spec.abstract
              (Function.update «Δctx» S! (some F!)) hφ⟧ˢ = some Φ),
            F!.2.1 = .fun α .bool ∧
            Φ.2.1 = SMT.SMTType.bool ∧
            (Φ.1 = ZFSet.zftrue ∧
              (F.1.pair F!.1) ∈
                (castZF_of_path (castPath.chpred τ_le_α.toCastPath)).1) ∧
            ∀ (G : SMT.Dom) (_ : G.2.1 = .fun α .bool)
              (hφG : SMT.RenamingContext.CoversFV
                (Function.update «Δctx» S! (some G)) S!_spec),
              (⟦S!_spec.abstract
                (Function.update «Δctx» S! (some G)) hφG⟧ˢ).isSome = true ∧
              ∀ {ΦG : SMT.Dom},
                ⟦S!_spec.abstract
                  (Function.update «Δctx» S! (some G)) hφG⟧ˢ = some ΦG →
                ΦG.1 = ZFSet.zftrue →
                (F.1.pair G.1) ∈
                  (castZF_of_path
                    (castPath.chpred τ_le_α.toCastPath)).1⌝ ⦄ := by
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_sub, St_used_eq, St_decl_eq⟩ := pre
  unfold castMembership
  conv =>
    enter [2, 1, 1]
    simp only [bind_pure_comp]
  rw [dif_neg α_ne_τ, dif_neg α_not_le_τ, dif_pos τ_le_α]
  mspec (Std.Do.Triple.and _
    (Std.Do.Triple.and _
      (Std.Do.Triple.and _
        (loosenAux_prf_exact_univ
          (Λ := St.types) (n := St.env.freshvarsc)
          (used := St.env.usedVars) typ_S
          (fun v hv => St_used_eq ▸ hbv_S v hv)
          (castPath.chpred τ_le_α.toCastPath))
        (loosenAux_prf_fv_of_faithful hfaith
          (used := St.env.usedVars) (n := St.env.freshvarsc)
          (x := S) (by
            intro v hv
            exact St_sub (SMT.Typing.mem_context_of_mem_fv typ_S hv))))
      (loosenAux_prf_decls (castPath.chpred τ_le_α.toCastPath)
        (decl := decl)))
    (loosenAux_prf_types_eq (castPath.chpred τ_le_α.toCastPath)))
  next out =>
  obtain ⟨S!, S!_spec⟩ := out
  mrename_i pre
  mintro ∀St1
  mpure pre
  obtain ⟨⟨⟨⟨hn1, St1_types_eq, S!_fresh, S!_not_used,
    used_sub1, keys_sub1, preserves1, typ_S!, typ_S!_spec,
    typ_S!_St1, typ_S!_spec_St1, fv_S!_spec, hadq_univ⟩,
    _S!_not_used_fv, fv_S_spec, _used_sub_fv⟩,
    St1_decl_eq⟩, ⟨St1_types_exact, _⟩⟩ := pre
  mspec Std.Do.Spec.map
  mspec SMT.declareConst_addSpec_spec
    (x! := S!) (x!_spec := S!_spec) (τ := .fun α .bool)
    (decl := St1.env.declarations)
    (as := St1.env.asserts) (n := St1.env.freshvarsc)
    (Γ := St1.types) (used := St1.env.usedVars)
  mrename_i pre
  mintro ∀St2
  mpure pre
  obtain ⟨St2_decl_eq, _, St2_fvc_eq, St2_used_eq, St2_types_eq⟩ := pre
  have typ_full :
      St2.types ⊢ˢ S!_spec ∧ˢ .app (.var S!) x : .bool := by
    rw [St2_types_eq]
    apply SMT.Typing.and
    · exact typ_S!_spec_St1
    · apply SMT.Typing.app
      · exact typ_S!_St1
      · exact SMT.Typing.weakening
          (h := fun v hv => St1_types_eq
            (SMT.TypeContext.entries_subset_insert_of_notMem S!_fresh hv))
          typ_x
          (fun v hv => preserves1 v (St_used_eq ▸ hbv_x v hv)
            (SMT.Typing.bv_notMem_context typ_x v hv))
  mpure_intro
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [St2_fvc_eq]
    exact hn1
  · intro v hv
    rw [St2_types_eq]
    exact St1_types_eq
      (SMT.TypeContext.entries_subset_insert_of_notMem S!_fresh hv)
  · rw [St2_types_eq, St2_used_eq]
    exact keys_sub1
  · rw [← St_used_eq, St2_used_eq]
    exact used_sub1
  · trivial
  · exact typ_full
  · intro v hv
    simp only [SMT.fv, List.mem_append, List.mem_singleton] at hv
    rcases hv with h_spec | rfl | h_x
    · have hmem := fv_S!_spec h_spec
      rcases List.mem_union_iff.mp hmem with hS | hS_in
      · exact Or.inr (Or.inl hS)
      · have heq : v = S! := List.mem_singleton.mp hS_in
        subst heq
        exact Or.inr (Or.inr (fun hΛ => S!_fresh hΛ))
    · exact Or.inr (Or.inr (fun hΛ => S!_fresh hΛ))
    · exact Or.inl h_x
  · intro v hv_used hv_notΛ
    rw [St2_types_eq]
    rw [St_used_eq] at preserves1
    exact preserves1 v hv_used hv_notΛ
  · intro Δctx hcov_t hcompat
    exact SMT.RenamingContext.denote_exists_of_typing
      typ_full hcompat hcov_t
  · refine ⟨S!, S!_spec, ?_, rfl, S!_fresh, ?_, ?_, ?_, fv_S!_spec,
      fv_S_spec, ?_⟩
    · rw [St2_decl_eq, St1_decl_eq]
      simp [helperSpecChunk, List.concat_eq_append, List.append_assoc]
    · rw [St_used_eq] at S!_not_used
      exact S!_not_used
    · rw [St2_types_eq]
      exact SMT.Typing.varE typ_S!_St1
    · rw [St2_types_eq]
      exact St1_types_exact
    · intro Δctx hS respects pf F hF_den
      obtain ⟨Φ, F!, hvar, hφ, hspec, hF!ty,
        hΦty, hcast, htot⟩ :=
        hadq_univ Δctx hS respects pf F hF_den
      exact ⟨Φ, F!, hvar, hφ, hspec, hF!ty, hΦty, hcast, htot⟩

set_option maxHeartbeats 3000000 in
/-- Exact specification for membership in an option-valued function.  The
pair argument is loosened componentwise, and the resulting helper
specification characterizes precisely the pair cast used before the option
lookup. -/
theorem castMembership_option_exact_spec.{u}
    {α β α' β' : SMT.SMTType}
    {x S : SMT.Term} {Λ : SMT.TypeContext} {n : ℕ}
    (typ_x : Λ ⊢ˢ x : .pair α β)
    (typ_S : Λ ⊢ˢ S : .fun α' (.option β'))
    (α_le : α ⊑ α') (β_le : β ⊑ β')
    (hfaith : castPath.FVFaithful
      (.pair α_le.toCastPath β_le.toCastPath))
    {used : List SMT.𝒱} {decl : SMT.Chunk}
    (hbv_x : ∀ v ∈ SMT.bv x, v ∈ used)
    (hbv_S : ∀ v ∈ SMT.bv S, v ∈ used) :
    ⦃ fun ⟨E, Λ'⟩ =>
        ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ AList.keys Λ ⊆ E.usedVars ∧
          E.usedVars = used ∧ E.declarations = decl⌝ ⦄
      castMembership ⟨x, .pair α β⟩ ⟨S, .fun α' (.option β')⟩
    ⦃ ⇓? ⟨t, σ⟩ ⟨E', Λ'⟩ => ⌜
      n ≤ E'.freshvarsc ∧ Λ ⊆ Λ' ∧
      AList.keys Λ' ⊆ E'.usedVars ∧ used ⊆ E'.usedVars ∧
      σ = .bool ∧ Λ' ⊢ˢ t : .bool ∧
      (∀ v ∈ SMT.fv t,
        v ∈ SMT.fv x ∨ v ∈ SMT.fv S ∨ v ∉ Λ) ∧
      (∀ v ∈ used, v ∉ Λ → v ∉ Λ') ∧
      (∀ (Δctx : SMT.RenamingContext.Context.{u})
          (hcov_t : SMT.RenamingContext.CoversFV Δctx t)
          (_hcompat : SMT.RenamingContext.RespectsTypeContext Δctx Λ'),
        ∃ denCM : SMT.Dom.{u},
          ⟦t.abstract Δctx hcov_t⟧ˢ = some denCM ∧
          denCM.snd.fst = .bool) ∧
      ∃ (x! : SMT.𝒱) (x!_spec : SMT.Term),
        E'.declarations = decl ++
          helperSpecChunk x! (.pair α' β') x!_spec ∧
        t = x!_spec ∧ˢ
          ((.app S (.fst (.var x!))) =ˢ (.some (.snd (.var x!)))) ∧
        x! ∉ Λ ∧ x! ∉ used ∧
        Λ'.lookup x! = some (.pair α' β') ∧
        Λ' = Λ.insert x! (.pair α' β') ∧
        SMT.fv x!_spec ⊆ SMT.fv x ∪ [x!] ∧
        SMT.fv x ⊆ SMT.fv x!_spec ∧
        ∀ («Δctx» : SMT.RenamingContext.Context.{u})
          (hx : SMT.RenamingContext.CoversFV «Δctx» x)
          (_respects : SMT.RenamingContext.RespectsTypeContextOnFV
            «Δctx» Λ x)
          (pf : ∀ (x_! : SMT.𝒱) (X! : SMT.Dom),
            ∀ v ∈ SMT.fv (SMT.Term.var x_!),
              (Function.update «Δctx» x_! (some X!) v).isSome = true),
        ∀ (X : SMT.Dom), ⟦x.abstract «Δctx» hx⟧ˢ = some X →
          ∃ (Φ X! : SMT.Dom)
            (_ : ⟦(SMT.Term.var x!).abstract
              (Function.update «Δctx» x! (some X!)) (pf x! X!)⟧ˢ = some X!)
            (hφ : SMT.RenamingContext.CoversFV
              (Function.update «Δctx» x! (some X!)) x!_spec)
            (_ : ⟦x!_spec.abstract
              (Function.update «Δctx» x! (some X!)) hφ⟧ˢ = some Φ),
            X!.2.1 = .pair α' β' ∧
            Φ.2.1 = SMT.SMTType.bool ∧
            (Φ.1 = ZFSet.zftrue ∧
              (X.1.pair X!.1) ∈
                (castZF_of_path
                  (.pair α_le.toCastPath β_le.toCastPath)).1) ∧
            ∀ (Y : SMT.Dom) (_ : Y.2.1 = .pair α' β')
              (hφY : SMT.RenamingContext.CoversFV
                (Function.update «Δctx» x! (some Y)) x!_spec),
              (⟦x!_spec.abstract
                (Function.update «Δctx» x! (some Y)) hφY⟧ˢ).isSome = true ∧
              ∀ {ΦY : SMT.Dom},
                ⟦x!_spec.abstract
                  (Function.update «Δctx» x! (some Y)) hφY⟧ˢ = some ΦY →
                ΦY.1 = ZFSet.zftrue →
                (X.1.pair Y.1) ∈
                  (castZF_of_path
                    (.pair α_le.toCastPath β_le.toCastPath)).1⌝ ⦄ := by
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_sub, St_used_eq, St_decl_eq⟩ := pre
  unfold castMembership
  conv =>
    enter [2, 1, 1]
    simp only [bind_pure_comp]
  rw [dif_pos α_le, dif_pos β_le]
  mspec (Std.Do.Triple.and _
    (Std.Do.Triple.and _
      (Std.Do.Triple.and _
        (loosenAux_prf_exact_univ
          (Λ := St.types) (n := St.env.freshvarsc)
          (used := St.env.usedVars) typ_x
          (fun v hv => St_used_eq ▸ hbv_x v hv)
          (.pair α_le.toCastPath β_le.toCastPath))
        (loosenAux_prf_fv_of_faithful hfaith
          (used := St.env.usedVars) (n := St.env.freshvarsc)
          (x := x) (by
            intro v hv
            exact St_sub (SMT.Typing.mem_context_of_mem_fv typ_x hv))))
      (loosenAux_prf_decls
        (.pair α_le.toCastPath β_le.toCastPath)
        (decl := decl)))
    (loosenAux_prf_types_eq
      (.pair α_le.toCastPath β_le.toCastPath)))
  next out =>
  obtain ⟨x!, x!_spec⟩ := out
  mrename_i pre
  mintro ∀St1
  mpure pre
  obtain ⟨⟨⟨⟨hn1, St1_types_eq, x!_fresh, x!_not_used,
    used_sub1, keys_sub1, preserves1, typ_x!, typ_x!_spec,
    typ_x!_St1, typ_x!_spec_St1, fv_x!_spec, hadq_univ⟩,
    _x!_not_used_fv, fv_x_spec, _used_sub_fv⟩,
    St1_decl_eq⟩, ⟨St1_types_exact, _⟩⟩ := pre
  mspec Std.Do.Spec.map
  mspec SMT.declareConst_addSpec_spec
    (x! := x!) (x!_spec := x!_spec) (τ := .pair α' β')
    (decl := St1.env.declarations)
    (as := St1.env.asserts) (n := St1.env.freshvarsc)
    (Γ := St1.types) (used := St1.env.usedVars)
  mrename_i pre
  mintro ∀St2
  mpure pre
  obtain ⟨St2_decl_eq, _, St2_fvc_eq, St2_used_eq, St2_types_eq⟩ := pre
  have typ_full : St2.types ⊢ˢ
      x!_spec ∧ˢ
        ((SMT.Term.app S (.fst (.var x!))) =ˢ
          (SMT.Term.snd (.var x!)).some) : .bool := by
    rw [St2_types_eq]
    apply SMT.Typing.and
    · exact typ_x!_spec_St1
    · apply SMT.Typing.eq
      · apply SMT.Typing.app
        · exact SMT.Typing.weakening
            (h := fun v hv => St1_types_eq
              (SMT.TypeContext.entries_subset_insert_of_notMem x!_fresh hv))
            typ_S
            (fun v hv => preserves1 v (St_used_eq ▸ hbv_S v hv)
              (SMT.Typing.bv_notMem_context typ_S v hv))
        · apply SMT.Typing.fst
          exact typ_x!_St1
      · apply SMT.Typing.some
        apply SMT.Typing.snd
        exact typ_x!_St1
  mpure_intro
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [St2_fvc_eq]
    exact hn1
  · intro v hv
    rw [St2_types_eq]
    exact St1_types_eq
      (SMT.TypeContext.entries_subset_insert_of_notMem x!_fresh hv)
  · rw [St2_types_eq, St2_used_eq]
    exact keys_sub1
  · rw [← St_used_eq, St2_used_eq]
    exact used_sub1
  · trivial
  · exact typ_full
  · intro v hv
    simp only [SMT.fv, List.mem_append, List.mem_singleton] at hv
    rcases hv with h_spec | (h_S | rfl) | rfl
    · have hmem := fv_x!_spec h_spec
      rcases List.mem_union_iff.mp hmem with hx | hx_in
      · exact Or.inl hx
      · have heq : v = x! := List.mem_singleton.mp hx_in
        subst heq
        exact Or.inr (Or.inr (fun hΛ => x!_fresh hΛ))
    · exact Or.inr (Or.inl h_S)
    · exact Or.inr (Or.inr (fun hΛ => x!_fresh hΛ))
    · exact Or.inr (Or.inr (fun hΛ => x!_fresh hΛ))
  · intro v hv_used hv_notΛ
    rw [St2_types_eq]
    rw [St_used_eq] at preserves1
    exact preserves1 v hv_used hv_notΛ
  · intro Δctx hcov_t hcompat
    exact SMT.RenamingContext.denote_exists_of_typing
      typ_full hcompat hcov_t
  · refine ⟨x!, x!_spec, ?_, rfl, x!_fresh, ?_, ?_, ?_, fv_x!_spec,
      fv_x_spec, ?_⟩
    · rw [St2_decl_eq, St1_decl_eq]
      simp [helperSpecChunk, List.concat_eq_append, List.append_assoc]
    · rw [St_used_eq] at x!_not_used
      exact x!_not_used
    · rw [St2_types_eq]
      exact SMT.Typing.varE typ_x!_St1
    · rw [St2_types_eq]
      exact St1_types_exact
    · intro Δctx hx respects pf X hX_den
      obtain ⟨Φ, X!, hvar, hφ, hspec, hX!ty,
        hΦty, hcast, htot⟩ :=
        hadq_univ Δctx hx respects pf X hX_den
      exact ⟨Φ, X!, hvar, hφ, hspec, hX!ty, hΦty, hcast, htot⟩
