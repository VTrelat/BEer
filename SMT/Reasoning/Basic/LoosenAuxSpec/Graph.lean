import SMT.Reasoning.Defs
import SMT.Reasoning.LooseningDefs
import SMT.Reasoning.Basic.StateSpecs
import SMT.Reasoning.Basic.LoosenAuxExact
import SMT.Reasoning.Basic.LoosenAuxSpec.Pair

open Std.Do SMT ZFSet Classical

private structure GraphTypingPack
    (Γ : TypeContext) (x : Term) (x! z z! : 𝒱)
    (α β α' β' : SMTType) (z!_spec : Term) where
  typ_z!_spec_body :
    (AList.insert z (α.pair β) (AList.insert z! (α'.pair β') Γ)) ⊢ˢ z!_spec : SMTType.bool
  typ_eq_some_body :
    (AList.insert z (α.pair β) (AList.insert z! (α'.pair β') Γ)) ⊢ˢ
      ((@ˢx) (.fst (.var z)) =ˢ .some (.snd (.var z))) : SMTType.bool
  typ_exists :
    (AList.insert z! (α'.pair β') Γ) ⊢ˢ
      (.exists [z] [α.pair β]
        ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)) : SMTType.bool
  typ_lambda :
    Γ ⊢ˢ
      (λˢ [z!]) [α'.pair β']
        (.exists [z] [α.pair β]
          ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)) :
        (α'.pair β').fun SMTType.bool
  typ_eq :
    Γ ⊢ˢ
      (Term.var x! =ˢ
        (λˢ [z!]) [α'.pair β']
          (.exists [z] [α.pair β]
            ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec))) :
        SMTType.bool

private theorem graphTypingPack
    {Γ : TypeContext} {x z!_spec : Term} {x! z z! : 𝒱}
    {α β α' β' : SMTType}
    (typ_x : Γ ⊢ˢ x : α.fun β.option)
    (typ_x! : Γ ⊢ˢ .var x! : (α'.pair β').fun SMTType.bool)
    (z_not : z ∉ Γ)
    (z!_not : z! ∉ Γ)
    (z_ne_z! : z ≠ z!)
    (typ_z!_spec_ctx :
      (AList.insert z! (α'.pair β') (AList.insert z (α.pair β) Γ)) ⊢ˢ z!_spec : SMTType.bool) :
    GraphTypingPack Γ x x! z z! α β α' β' z!_spec := by
  have z_not_insz!Γ : z ∉ (AList.insert z! (α'.pair β') Γ) := by
    rw [AList.mem_insert]
    intro hzmem
    rcases hzmem with hzmem | hzmem
    · exact z_ne_z! hzmem
    · exact z_not hzmem
  have hsub_Γ_insz! :
      Γ.entries ⊆ (AList.insert z! (α'.pair β') Γ).entries :=
    SMT.TypeContext.entries_subset_insert_of_notMem z!_not
  have hsub_insz!_insz_insz! :
      (AList.insert z! (α'.pair β') Γ).entries ⊆
        (AList.insert z (α.pair β) (AList.insert z! (α'.pair β') Γ)).entries :=
    SMT.TypeContext.entries_subset_insert_of_notMem z_not_insz!Γ
  have hsub_Γ_body :
      Γ.entries ⊆
        (AList.insert z (α.pair β) (AList.insert z! (α'.pair β') Γ)).entries := by
    intro v hv
    exact hsub_insz!_insz_insz! (hsub_Γ_insz! hv)
  have typ_x_body :
      (AList.insert z (α.pair β) (AList.insert z! (α'.pair β') Γ)) ⊢ˢ x : α.fun β.option := by
    exact SMT.Typing.weakening (h := hsub_Γ_body) typ_x
  have typ_var_z_body :
      (AList.insert z (α.pair β) (AList.insert z! (α'.pair β') Γ)) ⊢ˢ .var z : α.pair β := by
    apply SMT.Typing.var
    rw [AList.lookup_insert]
  have hperm_ctx :
      (AList.insert z! (α'.pair β') (AList.insert z (α.pair β) Γ)).entries.Perm
        ((AList.insert z (α.pair β) (AList.insert z! (α'.pair β') Γ)).entries) := by
    simpa using
      (AList.insert_insert_of_ne
        (s := Γ) (a := z) (a' := z!)
        (b := α.pair β) (b' := α'.pair β') z_ne_z!)
  have typ_z!_spec_body :
      (AList.insert z (α.pair β) (AList.insert z! (α'.pair β') Γ)) ⊢ˢ z!_spec : SMTType.bool := by
    exact SMT.Typing.weakening (h := hperm_ctx.subset) typ_z!_spec_ctx
  have typ_fst_body :
      (AList.insert z (α.pair β) (AList.insert z! (α'.pair β') Γ)) ⊢ˢ .fst (.var z) : α := by
    exact SMT.Typing.fst _ _ _ _ typ_var_z_body
  have typ_snd_body :
      (AList.insert z (α.pair β) (AList.insert z! (α'.pair β') Γ)) ⊢ˢ .snd (.var z) : β := by
    exact SMT.Typing.snd _ _ _ _ typ_var_z_body
  have typ_some_snd_body :
      (AList.insert z (α.pair β) (AList.insert z! (α'.pair β') Γ)) ⊢ˢ
        .some (.snd (.var z)) : β.option := by
    exact SMT.Typing.some _ _ _ typ_snd_body
  have typ_app_body :
      (AList.insert z (α.pair β) (AList.insert z! (α'.pair β') Γ)) ⊢ˢ
        (@ˢx) (.fst (.var z)) : β.option := by
    exact SMT.Typing.app _ _ _ _ _ typ_x_body typ_fst_body
  have typ_eq_some_body :
      (AList.insert z (α.pair β) (AList.insert z! (α'.pair β') Γ)) ⊢ˢ
        ((@ˢx) (.fst (.var z)) =ˢ .some (.snd (.var z))) : SMTType.bool := by
    exact SMT.Typing.eq _ _ _ _ typ_app_body typ_some_snd_body
  have typ_and_body :
      (AList.insert z (α.pair β) (AList.insert z! (α'.pair β') Γ)) ⊢ˢ
        ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec) : SMTType.bool := by
    exact SMT.Typing.and _ _ _ typ_eq_some_body typ_z!_spec_body
  have z_in_exists_ctx :
      z ∈ (AList.insert z (α.pair β) (AList.insert z! (α'.pair β') Γ)) := by
    rw [AList.mem_insert]
    exact Or.inl rfl
  have fresh_exists :
      ∀ v ∈ [z], v ∉ bv
        ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec) := by
    intro v hv
    rw [List.mem_singleton] at hv
    subst hv
    intro hbv
    exact (SMT.Typing.bv_notMem_context typ_and_body _ hbv) z_in_exists_ctx
  have len_eq_exists : [z].length = [α.pair β].length := by
    simp
  have hupdate_exists :
      SMT.TypeContext.update (AList.insert z! (α'.pair β') Γ) [z] [α.pair β] len_eq_exists =
        AList.insert z (α.pair β) (AList.insert z! (α'.pair β') Γ) := by
    simp only [SMT.TypeContext.update, List.length_cons, List.length_nil, zero_add,
      Fin.cast_eq_self, Fin.getElem_fin, Fin.foldl_succ_last, Fin.coe_ofNat_eq_mod,
      Nat.mod_succ, List.getElem_cons_zero, Fin.last_zero, Fin.isValue, Fin.foldl_zero]
  have typ_exists :
      (AList.insert z! (α'.pair β') Γ) ⊢ˢ
        (.exists [z] [α.pair β]
          ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)) : SMTType.bool := by
    apply SMT.Typing.exists (Γ := (AList.insert z! (α'.pair β') Γ))
      (vs := [z]) (τs := [α.pair β]) (len_eq := len_eq_exists)
    · intro v hv
      rw [List.mem_singleton] at hv
      subst hv
      exact z_not_insz!Γ
    · exact fresh_exists
    · exact Nat.zero_lt_succ 0
    · rwa [hupdate_exists]
  have z!_in_lambda_ctx :
      z! ∈ (AList.insert z! (α'.pair β') Γ) := by
    rw [AList.mem_insert]
    exact Or.inl rfl
  have fresh_lambda :
      ∀ v ∈ [z!], v ∉ bv
        (.exists [z] [α.pair β]
          ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)) := by
    intro v hv
    rw [List.mem_singleton] at hv
    subst hv
    intro hbv
    exact (SMT.Typing.bv_notMem_context typ_exists _ hbv) z!_in_lambda_ctx
  have len_eq_lambda : [z!].length = [α'.pair β'].length := by
    simp
  have hupdate_lambda :
      SMT.TypeContext.update Γ [z!] [α'.pair β'] len_eq_lambda =
        AList.insert z! (α'.pair β') Γ := by
    simp only [SMT.TypeContext.update, List.length_cons, List.length_nil, zero_add,
      Fin.cast_eq_self, Fin.getElem_fin, Fin.foldl_succ_last, Fin.coe_ofNat_eq_mod,
      Nat.mod_succ, List.getElem_cons_zero, Fin.last_zero, Fin.isValue, Fin.foldl_zero]
  have typ_lambda :
      Γ ⊢ˢ
        (λˢ [z!]) [α'.pair β']
          (.exists [z] [α.pair β]
            ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)) :
          (α'.pair β').fun SMTType.bool := by
    apply SMT.Typing.lambda
      (Γ := Γ)
      (vs := [z!]) (τs := [α'.pair β'])
      (t := (.exists [z] [α.pair β]
        ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)))
      (γ := SMTType.bool) (len_eq := len_eq_lambda)
    · intro v hv
      rw [List.mem_singleton] at hv
      subst hv
      exact z!_not
    · exact fresh_lambda
    · exact Nat.zero_lt_succ 0
    · simpa [hupdate_lambda] using typ_exists
  exact ⟨typ_z!_spec_body, typ_eq_some_body, typ_exists, typ_lambda,
    SMT.Typing.eq _ _ _ _ typ_x! typ_lambda⟩

private abbrev GraphPf.{u} («Δ» : RenamingContext.Context.{u}) : Prop :=
  ∀ (x! : 𝒱) (X! : SMT.Dom), ∀ v ∈ fv (Term.var x!),
    (Function.update «Δ» x! (some X!) v).isSome = true

private abbrev GraphOuterIH.{u}
    {τ τ' : SMTType} (p : τ ⇝ τ') : Prop :=
  ∀ {Λ : TypeContext} {n : ℕ} {used : List 𝒱} {name : String} {x : Term},
    Λ ⊢ˢ x : τ →
      ∀ («Δ₀» : RenamingContext.Context.{u}) (hx : RenamingContext.CoversFV «Δ₀» x)
        (pf₀ : GraphPf «Δ₀»),
        ⦃fun x =>
          match x with
          | { env := E, types := Λ' } =>
            ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ AList.keys Λ' ⊆ E.usedVars ∧ E.usedVars = used⌝⦄
        loosenAux_prf name p x
          ⦃PostCond.mayThrow fun x_1 x_2 =>
            match x_1 with
            | (x!, x!_spec) =>
              match x_2 with
              | { env := E', types := Γ' } =>
                ⌜n ≤ E'.freshvarsc ∧
                    AList.insert x! τ' Λ ⊆ Γ' ∧
                      x! ∉ Λ ∧
                        x! ∉ used ∧
                          used ⊆ E'.usedVars ∧
                            AList.keys Γ' ⊆ E'.usedVars ∧
                              (∀ v ∈ used, v ∉ Λ → v ∉ Γ') ∧
                              AList.insert x! τ' Λ ⊢ˢ Term.var x! : τ' ∧
                                AList.insert x! τ' Λ ⊢ˢ x!_spec : SMTType.bool ∧
                                  Γ' ⊢ˢ Term.var x! : τ' ∧
                                    Γ' ⊢ˢ x!_spec : SMTType.bool ∧
                                      fv x!_spec ⊆ fv x ∪ {x!} ∧
                                        ∀ (X : SMT.Dom),
                                          ⟦x.abstract «Δ₀» hx⟧ˢ = some X →
                                            ∃ Φ X!,
                                              ∃ (_ :
                                                ⟦(Term.var x!).abstract
                                                    (Function.update «Δ₀» x! (some X!))
                                                    (pf₀ x! X!)⟧ˢ =
                                                  some X!)
                                                (hφ : RenamingContext.CoversFV
                                                  (Function.update «Δ₀» x! (some X!))
                                                  x!_spec)
                                                (_ :
                                                  ⟦x!_spec.abstract
                                                      (Function.update «Δ₀» x! (some X!))
                                                      hφ⟧ˢ =
                                                    some Φ),
                                                Φ.snd.fst = SMTType.bool ∧
                                                  (Φ.fst = zftrue ∧
                                                    X.fst.pair X!.fst ∈ (castZF_of_path p).1) ∧
                                                    ∀ (Y : SMT.Dom),
                                                      Y.snd.fst = τ' →
                                                        ∀ (hφY : RenamingContext.CoversFV
                                                          (Function.update «Δ₀» x! (some Y))
                                                          x!_spec),
                                                          ⟦x!_spec.abstract
                                                              (Function.update «Δ₀» x! (some Y))
                                                              hφY⟧ˢ.isSome =
                                                            true⌝⦄

private abbrev GraphOuterIHAt.{u}
    («Δ₀» : RenamingContext.Context.{u}) (pf₀ : GraphPf «Δ₀»)
    {τ τ' : SMTType} (p : τ ⇝ τ') : Prop :=
  ∀ {Λ : TypeContext} {n : ℕ} {used : List 𝒱} {name : String} {x : Term},
    Λ ⊢ˢ x : τ →
      ∀ (hx : RenamingContext.CoversFV «Δ₀» x),
        ⦃fun x =>
          match x with
          | { env := E, types := Λ' } =>
            ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ AList.keys Λ' ⊆ E.usedVars ∧ E.usedVars = used⌝⦄
        loosenAux_prf name p x
          ⦃PostCond.mayThrow fun x_1 x_2 =>
            match x_1 with
            | (x!, x!_spec) =>
              match x_2 with
              | { env := E', types := Γ' } =>
                ⌜n ≤ E'.freshvarsc ∧
                    AList.insert x! τ' Λ ⊆ Γ' ∧
                      x! ∉ Λ ∧
                        x! ∉ used ∧
                          used ⊆ E'.usedVars ∧
                            AList.keys Γ' ⊆ E'.usedVars ∧
                              (∀ v ∈ used, v ∉ Λ → v ∉ Γ') ∧
                              AList.insert x! τ' Λ ⊢ˢ Term.var x! : τ' ∧
                                AList.insert x! τ' Λ ⊢ˢ x!_spec : SMTType.bool ∧
                                  Γ' ⊢ˢ Term.var x! : τ' ∧
                                    Γ' ⊢ˢ x!_spec : SMTType.bool ∧
                                      fv x!_spec ⊆ fv x ∪ {x!} ∧
                                        ∀ (X : SMT.Dom),
                                          ⟦x.abstract «Δ₀» hx⟧ˢ = some X →
                                            ∃ Φ X!,
                                              ∃ (_ :
                                                ⟦(Term.var x!).abstract
                                                    (Function.update «Δ₀» x! (some X!))
                                                    (pf₀ x! X!)⟧ˢ =
                                                  some X!)
                                                (hφ : RenamingContext.CoversFV
                                                  (Function.update «Δ₀» x! (some X!))
                                                  x!_spec)
                                                (_ :
                                                  ⟦x!_spec.abstract
                                                      (Function.update «Δ₀» x! (some X!))
                                                      hφ⟧ˢ =
                                                    some Φ),
                                                Φ.snd.fst = SMTType.bool ∧
                                                  (Φ.fst = zftrue ∧
                                                    X.fst.pair X!.fst ∈ (castZF_of_path p).1) ∧
                                                    ∀ (Y : SMT.Dom),
                                                      Y.snd.fst = τ' →
                                                        ∀ (hφY : RenamingContext.CoversFV
                                                          (Function.update «Δ₀» x! (some Y))
                                                          x!_spec),
                                                          ⟦x!_spec.abstract
                                                              (Function.update «Δ₀» x! (some Y))
                                                              hφY⟧ˢ.isSome =
                                                            true⌝⦄

private theorem graphLiftIH.{u}
    {«Δ₀» : RenamingContext.Context.{u}} (pf₀ : GraphPf «Δ₀»)
    {τ τ' : SMTType} {p : τ ⇝ τ'}
    (p_ih : GraphOuterIH.{u} p) :
    GraphOuterIHAt.{u} «Δ₀» pf₀ p := by
  intro Λ n used name x htyp hx
  exact p_ih htyp «Δ₀» hx pf₀

private theorem graphGoExistsCovers
    {«Δ» : RenamingContext.Context} {x z!_spec : Term}
    {x! z z! : 𝒱} {α β : SMTType}
    (hx : RenamingContext.CoversFV «Δ» x)
    (hfv_exists_sub :
      SMT.fv
        (.exists [z] [α.pair β]
          ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)) ⊆
        SMT.fv x ∪ {z!})
    (Yfun : SMT.Dom) :
    ∀ v ∈ SMT.fv
      (.exists [z] [α.pair β]
        ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)),
      v ∉ [z!] → (Function.update «Δ» x! (some Yfun) v).isSome = true := by
  intro v hv hv_not_vs
  have hv' := hfv_exists_sub hv
  rw [List.mem_union_iff] at hv'
  rcases hv' with hvx | hvz!_mem
  · by_cases hvx! : v = x!
    · subst hvx!
      simp
    · rw [Function.update_of_ne hvx!]
      exact hx v hvx
  · exact (hv_not_vs hvz!_mem).elim

private theorem graphExistsCovers
    {«Δ» : RenamingContext.Context} {x z!_spec : Term}
    {x! z z! : 𝒱} {α β : SMTType}
    (hx : RenamingContext.CoversFV «Δ» x)
    (hfv_exists_sub :
      SMT.fv
        (.exists [z] [α.pair β]
          ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)) ⊆
        SMT.fv x ∪ {z!})
    (Yfun W : SMT.Dom) :
    RenamingContext.CoversFV
      (Function.update (Function.update «Δ» x! (some Yfun)) z! (some W))
      (.exists [z] [α.pair β]
        ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)) := by
  intro v hv
  by_cases hvz! : v = z!
  · subst hvz!
    simp
  · rw [Function.update_of_ne hvz!]
    have hv' := hfv_exists_sub hv
    rw [List.mem_union_iff] at hv'
    rcases hv' with hvx | hvz!_mem
    · by_cases hvx! : v = x!
      · subst hvx!
        simp
      · rw [Function.update_of_ne hvx!]
        exact hx v hvx
    · exact (hvz! (List.mem_singleton.mp hvz!_mem)).elim

private theorem graphUnaryTarget
    {τ : SMTType} {y : ZFSet}
    (hy : y ∈ ⟦τ⟧ᶻ) :
    y.hasArity 1 ∧ ∀ i : Fin 1, y ∈ ⟦[τ][i]⟧ᶻ := by
  constructor
  · simp [ZFSet.hasArity]
  · rintro ⟨i, hi⟩
    simp at hi
    subst hi
    simpa using hy

private theorem graphDenAppAt
    {«Δ» : RenamingContext.Context} {x : Term} {x! z z! : 𝒱}
    {α β : SMTType} {X Yfun wy0 : SMT.Dom}
    (hcov_x_upd :
      ∀ Y : SMT.Dom, RenamingContext.CoversFV (Function.update «Δ» x! (some Y)) x)
    (denx_upd :
      ∀ Y : SMT.Dom,
        ⟦x.abstract (Function.update «Δ» x! (some Y)) (hcov_x_upd Y)⟧ˢ = some X)
    (hX_ty : X.snd.fst = α.fun β.option)
    (hX_func : IsFunc ⟦α⟧ᶻ ⟦β.option⟧ᶻ X.fst)
    (z!_not_mem_fv_x : z! ∉ SMT.fv x)
    (z_not_mem_fv_x : z ∉ SMT.fv x)
    (x₀ : SMT.Dom)
    (hx₀_ty : x₀.snd.fst = α.pair β)
    (hx₀_mem : x₀.fst ∈ ⟦α.pair β⟧ᶻ) :
    ∃ hcov_app_goal :
        SMT.RenamingContext.CoversFV
          (Function.update
            (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
            z (some x₀))
          ((@ˢx) (.fst (.var z))),
      ⟦((@ˢx) (.fst (.var z))).abstract
          (Function.update
            (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
            z (some x₀))
          hcov_app_goal⟧ˢ =
        some ⟨(@ᶻX.fst
                ⟨x₀.fst.π₁, by
                  have hx₀_fst_mem : x₀.fst.π₁ ∈ ⟦α⟧ᶻ := by
                    have hx₀_mem' := hx₀_mem
                    rw [SMTType.toZFSet, ZFSet.mem_prod] at hx₀_mem'
                    rcases hx₀_mem' with ⟨X₁, hX₁, X₂, hX₂, hpair⟩
                    rw [hpair, ZFSet.π₁_pair]
                    exact hX₁
                  simpa [ZFSet.is_func_dom_eq hX_func] using hx₀_fst_mem⟩).1,
          β.option,
          (@ᶻX.fst
            ⟨x₀.fst.π₁, by
              have hx₀_fst_mem : x₀.fst.π₁ ∈ ⟦α⟧ᶻ := by
                have hx₀_mem' := hx₀_mem
                rw [SMTType.toZFSet, ZFSet.mem_prod] at hx₀_mem'
                rcases hx₀_mem' with ⟨X₁, hX₁, X₂, hX₂, hpair⟩
                rw [hpair, ZFSet.π₁_pair]
                exact hX₁
              simpa [ZFSet.is_func_dom_eq hX_func] using hx₀_fst_mem⟩).2⟩ := by
  let Δgoal : SMT.RenamingContext.Context :=
    Function.update
      (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
      z (some x₀)
  have hcov_x_z! :
      SMT.RenamingContext.CoversFV
        (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0)) x :=
    SMT.RenamingContext.coversFV_update_of_notMem
      (x := z!) (d := wy0) z!_not_mem_fv_x (hcov_x_upd Yfun)
  have hcov_x_goal : SMT.RenamingContext.CoversFV Δgoal x :=
    SMT.RenamingContext.coversFV_update_of_notMem
      (x := z) (d := x₀) z_not_mem_fv_x hcov_x_z!
  have hdenx_goal :
      ⟦x.abstract Δgoal hcov_x_goal⟧ˢ = some X := by
    have hdenx_z! :
        ⟦x.abstract
            (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
            hcov_x_z!⟧ˢ = some X := by
      rw [←SMT.RenamingContext.denote]
      rw [←SMT.RenamingContext.denote_update_of_notMem
        («Δ» := Function.update «Δ» x! (some Yfun))
        (t := x) (x := z!) (d := wy0) (h := hcov_x_upd Yfun) z!_not_mem_fv_x]
      rw [SMT.RenamingContext.denote]
      exact denx_upd Yfun
    rw [←SMT.RenamingContext.denote]
    rw [←SMT.RenamingContext.denote_update_of_notMem
      («Δ» := Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
      (t := x) (x := z) (d := x₀) (h := hcov_x_z!) z_not_mem_fv_x]
    simpa [SMT.RenamingContext.denote] using hdenx_z!
  have hcov_var_z_goal : SMT.RenamingContext.CoversFV Δgoal (.var z) := by
    intro v hv
    rw [fv, List.mem_singleton] at hv
    subst hv
    simp [Δgoal]
  have hden_var_z_goal :
      ⟦(Term.var z).abstract Δgoal hcov_var_z_goal⟧ˢ = some x₀ := by
    rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some.injEq]
    apply Option.get_of_eq_some
    simp [Δgoal]
  have hcov_fst_var_z_goal :
      SMT.RenamingContext.CoversFV Δgoal (Term.fst (.var z)) := by
    intro v hv
    exact hcov_var_z_goal v (by simpa [fv] using hv)
  have hden_fst_var_z_goal :
      ⟦(Term.fst (.var z)).abstract Δgoal hcov_fst_var_z_goal⟧ˢ =
        some ⟨x₀.fst.π₁, α, by
          have hx₀_mem' := hx₀_mem
          rw [SMTType.toZFSet, ZFSet.mem_prod] at hx₀_mem'
          rcases hx₀_mem' with ⟨X₁, hX₁, X₂, hX₂, hpair⟩
          rw [hpair, ZFSet.π₁_pair]
          exact hX₁⟩ := by
    cases x₀ with
    | mk T Tdata =>
        cases Tdata with
        | mk τ hT =>
            dsimp at hx₀_ty hx₀_mem hden_var_z_goal ⊢
            cases hx₀_ty
            rw [SMT.Term.abstract.eq_def, SMT.denote, Option.pure_def, Option.bind_eq_bind,
              hden_var_z_goal, Option.bind_some]
  have hcov_app_goal : SMT.RenamingContext.CoversFV Δgoal ((@ˢx) (.fst (.var z))) := by
    intro v hv
    simp only [SMT.fv, List.mem_append] at hv
    rcases hv with hvx | hvfst
    · exact hcov_x_goal v hvx
    · exact hcov_var_z_goal v (by simpa [fv] using hvfst)
  let Xfun : SMT.Dom := ⟨X.fst, α.fun β.option, by simpa [hX_ty] using X.snd.snd⟩
  have hdenx_goal_fun :
      ⟦x.abstract Δgoal hcov_x_goal⟧ˢ = some Xfun := by
    rcases X with ⟨Xv, Xτ, hXv⟩
    dsimp [Xfun] at hdenx_goal hX_ty ⊢
    cases hX_ty
    simpa using hdenx_goal
  refine ⟨hcov_app_goal, ?_⟩
  rw [SMT.Term.abstract, SMT.denote, hdenx_goal_fun, hden_fst_var_z_goal]
  have hx₀_fst_mem : x₀.fst.π₁ ∈ ⟦α⟧ᶻ := by
    have hx₀_mem' := hx₀_mem
    rw [SMTType.toZFSet, ZFSet.mem_prod] at hx₀_mem'
    rcases hx₀_mem' with ⟨X₁, hX₁, X₂, hX₂, hpair⟩
    rw [hpair, ZFSet.π₁_pair]
    exact hX₁
  have hx₀_fst_dom : x₀.fst.π₁ ∈ X.fst.Dom := by
    simpa [ZFSet.is_func_dom_eq hX_func] using hx₀_fst_mem
  have hmem_opt' : ∃ y ∈ ⟦β.option⟧ᶻ, x₀.fst.π₁.pair y ∈ X.fst := by
    obtain ⟨y, hy_pair, _⟩ := hX_func.2 (x₀.fst.π₁) hx₀_fst_mem
    have hy_mem : y ∈ ⟦β.option⟧ᶻ := by
      have hy_prod := hX_func.1 hy_pair
      rw [ZFSet.pair_mem_prod] at hy_prod
      exact hy_prod.2
    exact ⟨y, hy_mem, hy_pair⟩
  have hx₀_fst_dom_expanded :
      x₀.fst.π₁ ∈ ⟦α⟧ᶻ ∧
        (x₀.fst.π₁.pair (ZFSet.Option.none (S := ⟦β⟧ᶻ)).1 ∈ X.fst ∨
          ∃ b : {u // u ∈ ⟦β⟧ᶻ},
            x₀.fst.π₁.pair (ZFSet.Option.some (S := ⟦β⟧ᶻ) b).1 ∈ X.fst) := by
    refine ⟨hx₀_fst_mem, ?_⟩
    rcases hmem_opt' with ⟨y, hy, hy_pair⟩
    obtain hy_none | ⟨b, hy_some⟩ := ZFSet.Option.casesOn ⟨y, hy⟩
    · left
      have hy_none_val : y = (ZFSet.Option.none (S := ⟦β⟧ᶻ)).1 :=
        congrArg (fun t : {u // u ∈ ⟦β.option⟧ᶻ} => t.1) hy_none
      simpa [hy_none_val] using hy_pair
    · right
      refine ⟨b, ?_⟩
      have hy_some_val : y = (ZFSet.Option.some (S := ⟦β⟧ᶻ) b).1 :=
        congrArg (fun t : {u // u ∈ ⟦β.option⟧ᶻ} => t.1) hy_some
      simpa [hy_some_val] using hy_pair
  have hx₀_fst_dom_disj :
      x₀.fst.π₁.pair ((∅ : ZFSet).pair ∅) ∈ X.fst ∨
        ∃ b ∈ ⟦β⟧ᶻ, x₀.fst.π₁.pair (zftrue.pair b) ∈ X.fst := by
    simpa [ZFSet.Option.none, ZFSet.Sum.inl, ZFSet.Option.some, ZFSet.Sum.inr] using
      hx₀_fst_dom_expanded.2
  simpa [Xfun, hX_ty, ZFSet.is_func_is_pfunc hX_func, hx₀_fst_mem, hx₀_fst_dom_disj]

private theorem graphDenSpecSomeAt
    {Γ : TypeContext} {«Δ» : RenamingContext.Context} {z!_spec : Term}
    {x! z z! : 𝒱} {σ σ' : SMTType} {p : σ ⇝ σ'} {Yfun wy0 : SMT.Dom}
    (den_z_at :
      ∀ (x₀ : SMT.Dom) (hx₀_ty : x₀.snd.fst = σ) (hx₀_mem : x₀.fst ∈ ⟦σ⟧ᶻ),
        ∃ Φ X₀!,
          ∃ (_ :
            ⟦(Term.var z!).abstract
              (Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some X₀!))
              (by
                intro v hv
                rw [fv, List.mem_singleton] at hv
                subst hv
                simp [Function.update])⟧ˢ = some X₀!)
            (hφ :
              RenamingContext.CoversFV
                (Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some X₀!))
                z!_spec)
            (_ :
              ⟦z!_spec.abstract
                (Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some X₀!)) hφ⟧ˢ =
                some Φ),
            Φ.snd.fst = SMTType.bool ∧
              (Φ.fst = zftrue ∧ x₀.fst.pair X₀!.fst ∈ (castZF_of_path p).1) ∧
                ∀ (Y : SMT.Dom), Y.snd.fst = σ' →
                  ∀ (hφY :
                    RenamingContext.CoversFV
                      (Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some Y))
                      z!_spec),
                    ⟦z!_spec.abstract
                      (Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some Y))
                        hφY⟧ˢ.isSome = true)
    (fv_z!_spec : SMT.fv z!_spec ⊆ SMT.fv (.var z) ∪ {z!})
    (z_ne_z! : z ≠ z!)
    (x_ne_z : x! ≠ z)
    (x_ne_z! : x! ≠ z!)
    (typ_z!_spec_body :
      (AList.insert z σ (AList.insert z! σ' Γ)) ⊢ˢ z!_spec : SMTType.bool)
    (hwy0_ty : wy0.snd.fst = σ')
    (x₀ : SMT.Dom)
    (hx₀_ty : x₀.snd.fst = σ)
    (hx₀_mem : x₀.fst ∈ ⟦σ⟧ᶻ) :
    ∃ hφY :
        RenamingContext.CoversFV
          (Function.update
            (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
            z (some x₀))
          z!_spec,
      ∃ Φ,
        ⟦z!_spec.abstract
            (Function.update
              (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
              z (some x₀))
            hφY⟧ˢ =
          some Φ ∧
        Φ.snd.fst = SMTType.bool := by
  obtain ⟨_, _, _, _, _, _, _, htot0⟩ := den_z_at x₀ hx₀_ty hx₀_mem
  let Δbase : SMT.RenamingContext.Context :=
    Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some wy0)
  have hφ_base : SMT.RenamingContext.CoversFV Δbase z!_spec := by
    intro u hu
    have hu' := fv_z!_spec hu
    rw [List.mem_union_iff] at hu'
    rcases hu' with huz | huz!
    · have huz' : u = z := by
        simpa [fv] using huz
      subst u
      simp [Δbase, z_ne_z!]
    · have huz!' : u = z! := List.mem_singleton.mp huz!
      subst u
      simp [Δbase]
  have hspec_some_base :
      (SMT.RenamingContext.denote Δbase z!_spec hφ_base).isSome = true := by
    simpa [SMT.RenamingContext.denote, Δbase] using htot0 wy0 hwy0_ty hφ_base
  let Δgoal : SMT.RenamingContext.Context :=
    Function.update
      (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
      z (some x₀)
  have hφ_goal : SMT.RenamingContext.CoversFV Δgoal z!_spec := by
    intro u hu
    have hu' := fv_z!_spec hu
    rw [List.mem_union_iff] at hu'
    rcases hu' with huz | huz!
    · have huz' : u = z := by
        simpa [fv] using huz
      subst u
      simp only [Function.update_self, Option.isSome_some, Δgoal]
    · have huz!' : u = z! := List.mem_singleton.mp huz!
      subst u
      rw [show Δgoal z! =
        (Function.update
          (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
          z (some x₀) z!) by rfl]
      rw [Function.update_of_ne z_ne_z!.symm, Function.update_self]
      rfl
  have hag_spec : SMT.RenamingContext.AgreesOnFV Δgoal Δbase z!_spec := by
    intro u hu
    have hu' := fv_z!_spec hu
    rw [List.mem_union_iff] at hu'
    rcases hu' with huz | huz!
    · have huz' : u = z := by
        simpa [fv] using huz
      subst u
      simp only [Function.update_self, ne_eq, z_ne_z!, not_false_eq_true, Function.update_of_ne,
        ↓reduceIte, Δgoal, Δbase]
    · have huz!' : u = z! := List.mem_singleton.mp huz!
      subst u
      rw [show Δgoal z! =
        (Function.update
          (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
          z (some x₀) z!) by rfl]
      rw [show Δbase z! =
        (Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some wy0) z!) by rfl]
      rw [Function.update_of_ne z_ne_z!.symm, Function.update_self, Function.update_self]
  have hspec_eq :
      SMT.RenamingContext.denote Δgoal z!_spec hφ_goal =
        SMT.RenamingContext.denote Δbase z!_spec hφ_base :=
    SMT.RenamingContext.denote_congr_of_agreesOnFV (h1 := hφ_goal) (h2 := hφ_base) hag_spec
  have hspec_some_goal :
      ⟦z!_spec.abstract Δgoal hφ_goal⟧ˢ.isSome = true := by
    have hspec_isSome := congrArg Option.isSome hspec_eq
    rw [hspec_some_base] at hspec_isSome
    simpa [SMT.RenamingContext.denote] using hspec_isSome
  obtain ⟨Φ, hdenΦ⟩ := Option.isSome_iff_exists.mp hspec_some_goal
  refine ⟨hφ_goal, Φ, hdenΦ, ?_⟩
  exact denote_type_eq_of_typing (typ_t := typ_z!_spec_body) (hden := hdenΦ)

private theorem graphDenSomeSndAt
    {«Δ» : RenamingContext.Context} {x! z z! : 𝒱}
    {α β : SMTType} {Yfun wy0 x₀ : SMT.Dom}
    (hx₀_ty : x₀.snd.fst = α.pair β)
    (hx₀_mem : x₀.fst ∈ ⟦α.pair β⟧ᶻ) :
    ∃ hcov_some_goal :
        RenamingContext.CoversFV
          (Function.update
            (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
            z (some x₀))
          (Term.some (Term.snd (.var z))),
      ⟦(Term.some (Term.snd (.var z))).abstract
          (Function.update
            (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
            z (some x₀))
          hcov_some_goal⟧ˢ =
        some ⟨(ZFSet.Option.some (S := ⟦β⟧ᶻ)
                ⟨x₀.fst.π₂, by
                  have hx₀_snd_mem : x₀.fst.π₂ ∈ ⟦β⟧ᶻ := by
                    have hx₀_mem' := hx₀_mem
                    rw [SMTType.toZFSet, ZFSet.mem_prod] at hx₀_mem'
                    rcases hx₀_mem' with ⟨X₁, hX₁, X₂, hX₂, hpair⟩
                    rw [hpair, ZFSet.π₂_pair]
                    exact hX₂
                  exact hx₀_snd_mem⟩).1,
          β.option,
          (ZFSet.Option.some (S := ⟦β⟧ᶻ)
              ⟨x₀.fst.π₂, by
                have hx₀_snd_mem : x₀.fst.π₂ ∈ ⟦β⟧ᶻ := by
                  have hx₀_mem' := hx₀_mem
                  rw [SMTType.toZFSet, ZFSet.mem_prod] at hx₀_mem'
                  rcases hx₀_mem' with ⟨X₁, hX₁, X₂, hX₂, hpair⟩
                  rw [hpair, ZFSet.π₂_pair]
                  exact hX₂
                exact hx₀_snd_mem⟩).2⟩ := by
  let Δgoal : RenamingContext.Context :=
    Function.update
      (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
      z (some x₀)
  have hcov_var_z_goal : RenamingContext.CoversFV Δgoal (.var z) := by
    intro v hv
    rw [fv, List.mem_singleton] at hv
    subst hv
    simp [Δgoal]
  have hden_var_z_goal :
      ⟦(Term.var z).abstract Δgoal hcov_var_z_goal⟧ˢ = some x₀ := by
    rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some.injEq]
    apply Option.get_of_eq_some
    simp [Δgoal]
  have hcov_snd_var_z_goal : RenamingContext.CoversFV Δgoal (Term.snd (.var z)) := by
    intro v hv
    exact hcov_var_z_goal v (by simpa [fv] using hv)
  have hden_snd_var_z_goal :
      ⟦(Term.snd (.var z)).abstract Δgoal hcov_snd_var_z_goal⟧ˢ =
        some ⟨x₀.fst.π₂, β, by
          have hx₀_mem' := hx₀_mem
          rw [SMTType.toZFSet, ZFSet.mem_prod] at hx₀_mem'
          rcases hx₀_mem' with ⟨X₁, hX₁, X₂, hX₂, hpair⟩
          rw [hpair, ZFSet.π₂_pair]
          exact hX₂⟩ := by
    cases x₀ with
    | mk T Tdata =>
        cases Tdata with
        | mk τ hT =>
            dsimp at hx₀_ty hx₀_mem hden_var_z_goal ⊢
            cases hx₀_ty
            rw [SMT.Term.abstract.eq_def, SMT.denote, Option.pure_def, Option.bind_eq_bind,
              hden_var_z_goal, Option.bind_some]
  have hcov_some_goal : RenamingContext.CoversFV Δgoal (Term.some (Term.snd (.var z))) := by
    intro v hv
    exact hcov_snd_var_z_goal v (by simpa [fv] using hv)
  refine ⟨hcov_some_goal, ?_⟩
  rw [SMT.Term.abstract.eq_def, SMT.denote, hden_snd_var_z_goal]
  simp [Option.bind_some, Option.pure_def]

private theorem graphDenSpecTrueAtCast
    {Γ : TypeContext} {«Δ» : RenamingContext.Context} {z!_spec : Term}
    {x! z z! : 𝒱} {σ σ' : SMTType} {p : σ ⇝ σ'} {cast y : ZFSet} {Yfun wy0 : SMT.Dom}
    (den_z_at :
      ∀ (x₀ : SMT.Dom) (hx₀_ty : x₀.snd.fst = σ) (hx₀_mem : x₀.fst ∈ ⟦σ⟧ᶻ),
        ∃ Φ X₀!,
          ∃ (_ :
            ⟦(Term.var z!).abstract
              (Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some X₀!))
              (by
                intro v hv
                rw [fv, List.mem_singleton] at hv
                subst hv
                simp [Function.update])⟧ˢ = some X₀!)
            (hφ :
              RenamingContext.CoversFV
                (Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some X₀!))
                z!_spec)
            (_ :
              ⟦z!_spec.abstract
                (Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some X₀!)) hφ⟧ˢ =
                some Φ),
            Φ.snd.fst = SMTType.bool ∧
              (Φ.fst = zftrue ∧ x₀.fst.pair X₀!.fst ∈ cast) ∧
                ∀ (Y : SMT.Dom), Y.snd.fst = σ' →
                  ∀ (hφY :
                    RenamingContext.CoversFV
                      (Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some Y))
                      z!_spec),
                    ⟦z!_spec.abstract
                      (Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some Y))
                        hφY⟧ˢ.isSome = true)
    (fv_z!_spec : SMT.fv z!_spec ⊆ SMT.fv (.var z) ∪ {z!})
    (z_ne_z! : z ≠ z!)
    (x_ne_z : x! ≠ z)
    (x_ne_z! : x! ≠ z!)
    (typ_z! :
      Γ ⊢ˢ Term.var z! : σ')
    (hcast : IsFunc ⟦σ⟧ᶻ ⟦σ'⟧ᶻ cast)
    (hwy0_ty : wy0.snd.fst = σ')
    (hwy0_val : wy0.fst = y)
    (x₀ : SMT.Dom)
    (hx₀_ty : x₀.snd.fst = σ)
    (hx₀_mem : x₀.fst ∈ ⟦σ⟧ᶻ)
    (hcast_xy : x₀.fst.pair y ∈ cast) :
    ∃ hφY :
        RenamingContext.CoversFV
          (Function.update
            (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
            z (some x₀))
          z!_spec,
      ∃ Φ,
        ⟦z!_spec.abstract
            (Function.update
              (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
              z (some x₀))
            hφY⟧ˢ =
          some Φ ∧
        Φ.fst = zftrue := by
  obtain ⟨Φ0, X₀!, hden_var_z!, hφ0, hden0, _, hΦ0_true_cast, _⟩ := den_z_at x₀ hx₀_ty hx₀_mem
  obtain ⟨hΦ0_true, hcast0⟩ := hΦ0_true_cast
  have hcast_pfunc :
      cast.IsPFunc ⟦σ⟧ᶻ ⟦σ'⟧ᶻ :=
    ZFSet.is_func_is_pfunc hcast
  have hx₀_cast_dom : x₀.fst ∈ cast.Dom := by
    simpa [ZFSet.is_func_dom_eq hcast] using hx₀_mem
  have hX₀_ty : X₀!.snd.fst = σ' :=
    denote_type_eq_of_typing (typ_t := typ_z!) (hden := hden_var_z!)
  have hX₀_val :
      X₀!.fst = (@ᶻcast ⟨x₀.fst, hx₀_cast_dom⟩) := by
    symm
    exact congrArg Subtype.val (ZFSet.fapply.of_pair (hf := hcast_pfunc) hcast0)
  have hy_val :
      y = (@ᶻcast ⟨x₀.fst, hx₀_cast_dom⟩) := by
    symm
    exact congrArg Subtype.val (ZFSet.fapply.of_pair (hf := hcast_pfunc) hcast_xy)
  have hX₀_eq_wy0 : X₀! = wy0 := by
    rcases X₀! with ⟨X₀v, X₀τ, hX₀mem⟩
    rcases wy0 with ⟨wyv, wyτ, hwy0mem⟩
    dsimp at hX₀_ty hwy0_ty hwy0_val hX₀_val hy_val ⊢
    cases hX₀_ty
    cases hwy0_ty
    have hval : X₀v = wyv := by
      calc
        X₀v = (@ᶻcast ⟨x₀.fst, hx₀_cast_dom⟩) := hX₀_val
        _ = y := hy_val.symm
        _ = wyv := hwy0_val.symm
    cases hval
    congr
  let Δbase : SMT.RenamingContext.Context :=
    Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some wy0)
  let Δgoal : SMT.RenamingContext.Context :=
    Function.update
      (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
      z (some x₀)
  have hφ_goal : SMT.RenamingContext.CoversFV Δgoal z!_spec := by
    intro u hu
    have hu' := fv_z!_spec hu
    rw [List.mem_union_iff] at hu'
    rcases hu' with huz | huz!
    · have huz' : u = z := by
        simpa [fv] using huz
      subst u
      simp [Δgoal, z_ne_z!, x_ne_z, x_ne_z!]
    · have huz!' : u = z! := List.mem_singleton.mp huz!
      subst u
      rw [show Δgoal z! =
        (Function.update
          (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
          z (some x₀) z!) by rfl]
      rw [Function.update_of_ne z_ne_z!.symm, Function.update_self]
      rfl
  have hag_spec : SMT.RenamingContext.AgreesOnFV Δgoal Δbase z!_spec := by
    intro u hu
    have hu' := fv_z!_spec hu
    rw [List.mem_union_iff] at hu'
    rcases hu' with huz | huz!
    · have huz' : u = z := by
        simpa [fv] using huz
      subst u
      simp [Δgoal, Δbase, z_ne_z!, x_ne_z, x_ne_z!]
    · have huz!' : u = z! := List.mem_singleton.mp huz!
      subst u
      rw [show Δgoal z! =
        (Function.update
          (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
          z (some x₀) z!) by rfl]
      rw [show Δbase z! =
        (Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some wy0) z!) by rfl]
      rw [Function.update_of_ne z_ne_z!.symm, Function.update_self, Function.update_self]
  have hden0_goal :
      SMT.RenamingContext.denote Δgoal z!_spec hφ_goal = some Φ0 := by
    rw [SMT.RenamingContext.denote_congr_of_agreesOnFV (h1 := hφ_goal) (h2 := by
      simpa [Δbase, hX₀_eq_wy0] using hφ0) hag_spec]
    simpa [SMT.RenamingContext.denote, hX₀_eq_wy0] using hden0
  refine ⟨hφ_goal, Φ0, ?_, hΦ0_true⟩
  simpa [SMT.RenamingContext.denote] using hden0_goal

private theorem graphDenSpecTrueImpliesCast
    {Γ : TypeContext} {«Δ» : RenamingContext.Context} {z!_spec : Term}
    {x! z z! : 𝒱} {σ σ' : SMTType} {p : σ ⇝ σ'} {Yfun wy0 : SMT.Dom}
    (den_z_exact_at :
      ∀ (x₀ : SMT.Dom)
        (hx₀_ty : x₀.snd.fst = σ)
        (hx₀_mem : x₀.fst ∈ ⟦σ⟧ᶻ)
        {Y Φ : SMT.Dom}
        (hY_ty : Y.snd.fst = σ')
        (hφY :
          RenamingContext.CoversFV
            (Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some Y))
            z!_spec)
        (hdenY :
          ⟦z!_spec.abstract
              (Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some Y))
              hφY⟧ˢ =
            some Φ)
        (htrue : Φ.fst = zftrue),
        x₀.fst.pair Y.fst ∈ (castZF_of_path p).1)
    (fv_z!_spec : SMT.fv z!_spec ⊆ SMT.fv (.var z) ∪ {z!})
    (z_ne_z! : z ≠ z!)
    (x_ne_z : x! ≠ z)
    (x_ne_z! : x! ≠ z!)
    (x₀ : SMT.Dom)
    (hwy0_ty : wy0.snd.fst = σ')
    (hx₀_ty : x₀.snd.fst = σ)
    (hx₀_mem : x₀.fst ∈ ⟦σ⟧ᶻ)
    {Φ : SMT.Dom}
    (hφY :
      RenamingContext.CoversFV
        (Function.update
          (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
          z (some x₀))
        z!_spec)
    (hdenY :
      ⟦z!_spec.abstract
          (Function.update
            (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
            z (some x₀))
          hφY⟧ˢ =
        some Φ)
    (htrue : Φ.fst = zftrue) :
    x₀.fst.pair wy0.fst ∈ (castZF_of_path p).1 := by
  let Δbase : SMT.RenamingContext.Context :=
    Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some wy0)
  let Δgoal : SMT.RenamingContext.Context :=
    Function.update
      (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
      z (some x₀)
  have hφ_base : SMT.RenamingContext.CoversFV Δbase z!_spec := by
    intro u hu
    have hu' := fv_z!_spec hu
    rw [List.mem_union_iff] at hu'
    rcases hu' with huz | huz!
    · have huz' : u = z := by
        simpa [fv] using huz
      subst u
      simp [Δbase, z_ne_z!]
    · have huz!' : u = z! := List.mem_singleton.mp huz!
      subst u
      simp [Δbase]
  have hag_spec : SMT.RenamingContext.AgreesOnFV Δgoal Δbase z!_spec := by
    intro u hu
    have hu' := fv_z!_spec hu
    rw [List.mem_union_iff] at hu'
    rcases hu' with huz | huz!
    · have huz' : u = z := by
        simpa [fv] using huz
      subst u
      simp [Δgoal, Δbase, z_ne_z!, x_ne_z, x_ne_z!]
    · have huz!' : u = z! := List.mem_singleton.mp huz!
      subst u
      rw [show Δgoal z! =
        (Function.update
          (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
          z (some x₀) z!) by rfl]
      rw [show Δbase z! =
        (Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some wy0) z!) by rfl]
      rw [Function.update_of_ne z_ne_z!.symm, Function.update_self, Function.update_self]
  have hdenY_base :
      SMT.RenamingContext.denote Δbase z!_spec hφ_base = some Φ := by
    rw [←SMT.RenamingContext.denote_congr_of_agreesOnFV (h1 := hφY) (h2 := hφ_base) hag_spec]
    simpa [SMT.RenamingContext.denote] using hdenY
  exact den_z_exact_at x₀ hx₀_ty hx₀_mem hwy0_ty hφ_base (by
    simpa [SMT.RenamingContext.denote] using hdenY_base) htrue

private theorem graphEqCovers
    {«Δ» : RenamingContext.Context} {x : Term} {z : 𝒱}
    (hcov_app_goal : RenamingContext.CoversFV «Δ» ((@ˢx) (.fst (.var z))))
    (hcov_some_goal : RenamingContext.CoversFV «Δ» (.some (.snd (.var z)))) :
    RenamingContext.CoversFV «Δ»
      ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z)))) := by
  intro v hv
  have hv' :
      v ∈ SMT.fv (((@ˢx) (.fst (.var z)))) ∨
        v ∈ SMT.fv (.some (.snd (.var z))) := by
    simpa [fv] using hv
  rcases hv' with hvapp | hvsome
  · exact hcov_app_goal v (by simpa [fv] using hvapp)
  · exact hcov_some_goal v (by simpa [fv] using hvsome)

private theorem graphEqSpecCovers
    {«Δ» : RenamingContext.Context} {x z!_spec : Term} {z : 𝒱}
    (hcov_eq_goal :
      RenamingContext.CoversFV «Δ»
        ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z)))))
    (hφY : RenamingContext.CoversFV «Δ» z!_spec) :
    RenamingContext.CoversFV «Δ»
      ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec) := by
  intro v hv
  have hv' :
      v ∈ SMT.fv ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z)))) ∨
        v ∈ SMT.fv z!_spec := by
    simpa [fv, or_assoc] using hv
  rcases hv' with hveq | hvspec
  · exact hcov_eq_goal v hveq
  · exact hφY v hvspec

private theorem graphPairCastFstInRange
    {α β α' β' : SMTType} {pα : α ⇝ α'} {pβ : β ⇝ β'}
    {x y : ZFSet}
    (hcast_xy : x.pair y ∈ (castZF_of_path (pα.pair pβ)).1) :
    y.π₁ ∈
      ZFSet.Range ((castZF_of_path pα).1) (A := ⟦α⟧ᶻ) (B := ⟦α'⟧ᶻ)
        (hf := ZFSet.is_rel_of_is_pfunc (ZFSet.is_func_is_pfunc (castZF_of_path pα).2)) := by
  rw [castZF_of_path, castZF_pair, ZFSet.pair_mem_fprod] at hcast_xy
  obtain ⟨a, b, _, _, rfl, rfl⟩ := hcast_xy
  rw [ZFSet.π₁_pair]
  exact ZFSet.IsPFunc.mem_range_of_mem
    (ZFSet.is_func_is_pfunc (castZF_of_path pα).2)
    (ZFSet.fapply.def (ZFSet.is_func_is_pfunc (castZF_of_path pα).2) (by
      rwa [ZFSet.is_func_dom_eq (castZF_of_path pα).2]))

private theorem graphPairCastSndInRange
    {α β α' β' : SMTType} {pα : α ⇝ α'} {pβ : β ⇝ β'}
    {x y : ZFSet}
    (hcast_xy : x.pair y ∈ (castZF_of_path (pα.pair pβ)).1) :
    y.π₂ ∈
      ZFSet.Range ((castZF_of_path pβ).1) (A := ⟦β⟧ᶻ) (B := ⟦β'⟧ᶻ)
        (hf := ZFSet.is_rel_of_is_pfunc (ZFSet.is_func_is_pfunc (castZF_of_path pβ).2)) := by
  rw [castZF_of_path, castZF_pair, ZFSet.pair_mem_fprod] at hcast_xy
  rcases hcast_xy with ⟨a, b, _, _, rfl, rfl⟩
  rw [ZFSet.π₂_pair]
  exact ZFSet.IsPFunc.mem_range_of_mem
    (ZFSet.is_func_is_pfunc (castZF_of_path pβ).2)
    (ZFSet.fapply.def (ZFSet.is_func_is_pfunc (castZF_of_path pβ).2) (by
      rwa [ZFSet.is_func_dom_eq (castZF_of_path pβ).2]))

private theorem graphPairFstMem
    {α β : SMTType} {x : ZFSet}
    (hx : x ∈ ⟦α.pair β⟧ᶻ) :
    x.π₁ ∈ ⟦α⟧ᶻ := by
  rw [SMTType.toZFSet, ZFSet.mem_prod] at hx
  rcases hx with ⟨a, ha, b, hb, rfl⟩
  rw [ZFSet.π₁_pair]
  exact ha

private theorem graphPairSndMem
    {α β : SMTType} {x : ZFSet}
    (hx : x ∈ ⟦α.pair β⟧ᶻ) :
    x.π₂ ∈ ⟦β⟧ᶻ := by
  rw [SMTType.toZFSet, ZFSet.mem_prod] at hx
  rcases hx with ⟨a, ha, b, hb, rfl⟩
  rw [ZFSet.π₂_pair]
  exact hb

private theorem graphSingletonArg
    {τ : SMTType} {x : ZFSet}
    (hx : x ∈ ⟦τ⟧ᶻ) :
    ∀ i : Fin [τ].length,
      (⟨x, τ, hx⟩ : SMT.Dom).snd.fst = [τ][i] ∧
        (⟨x, τ, hx⟩ : SMT.Dom).fst ∈ ⟦[τ][i]⟧ᶻ := by
  intro i
  have hi0 : i = ⟨0, by simp⟩ := by
    apply Fin.ext
    simp
  cases hi0
  exact ⟨rfl, hx⟩

private theorem graphSpecificArg
    {τ : SMTType} {w : Fin [τ].length → SMT.Dom}
    (hw : ∀ i, (w i).snd.fst = [τ][i] ∧ (w i).fst ∈ ⟦[τ][i]⟧ᶻ) :
    ∀ i, (w i).snd.fst = τ ∧ (w i).fst ∈ ⟦τ⟧ᶻ := by
  intro i
  have hi0 : i = ⟨0, by simp⟩ := by
    apply Fin.ext
    simp
  cases hi0
  simpa using hw ⟨0, by simp⟩

private theorem graphBoolOfDecideTrue
    {P : Prop} [Decidable P]
    (hP : P) :
    (↑(ZFSet.ZFBool.ofBool (decide P)) : ZFSet) = zftrue := by
  simpa [ZFSet.ZFBool.ofBool, hP]

private theorem graphBoolOfDecideFalse
    {P : Prop} [Decidable P]
    (hP : ¬ P) :
    (↑(ZFSet.ZFBool.ofBool (decide P)) : ZFSet) = zffalse := by
  simpa [ZFSet.ZFBool.ofBool, hP]

private def graphBoolDom (b : ZFSet.ZFBool) : SMT.Dom :=
  ⟨(b : ZFSet), SMTType.bool, b.2⟩

private theorem graphBoolMemOfTyEqBool
    {D : SMT.Dom}
    (hD_ty : D.snd.fst = SMTType.bool) :
    D.fst ∈ 𝔹 := by
  obtain ⟨Dval, Dty, hD_mem⟩ := D
  cases hD_ty
  exact hD_mem

private theorem graphBoolDomEqZftrueOfSInterEqZffalse
    {D : ZFSet} {F : ZFSet → ZFSet}
    (hsInter :
      (⋂₀ (ZFSet.sep (fun y => ∃ x ∈ D, y = F x) 𝔹) : ZFSet) = zffalse) :
    graphBoolDom
      (ZFSet.ZFBool.not
        ⟨⋂₀ (ZFSet.sep (fun y => ∃ x ∈ D, y = F x) 𝔹),
          ZFSet.sInter_sep_subset_of_𝔹_mem_𝔹 (fun _ ↦ id)⟩) =
      ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
  have hbool :
      (⟨⋂₀ (ZFSet.sep (fun y => ∃ x ∈ D, y = F x) 𝔹),
        ZFSet.sInter_sep_subset_of_𝔹_mem_𝔹 (fun _ ↦ id)⟩ : ZFSet.ZFBool) = ⊥ := by
    rwa [Subtype.mk.injEq]
  simpa [graphBoolDom] using congrArg graphBoolDom <|
    show ZFSet.ZFBool.not
        ⟨⋂₀ (ZFSet.sep (fun y => ∃ x ∈ D, y = F x) 𝔹),
          ZFSet.sInter_sep_subset_of_𝔹_mem_𝔹 (fun _ ↦ id)⟩ = ⊤ by
      rw [hbool, ZFSet.ZFBool.not_false_eq_true]

private theorem graphBoolDomEqZffalseOfSInterEqZftrue
    {D : ZFSet} {F : ZFSet → ZFSet}
    (hsInter :
      (⋂₀ (ZFSet.sep (fun y => ∃ x ∈ D, y = F x) 𝔹) : ZFSet) = zftrue) :
    graphBoolDom
      (ZFSet.ZFBool.not
        ⟨⋂₀ (ZFSet.sep (fun y => ∃ x ∈ D, y = F x) 𝔹),
          ZFSet.sInter_sep_subset_of_𝔹_mem_𝔹 (fun _ ↦ id)⟩) =
      ⟨zffalse, SMTType.bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
  have hbool :
      (⟨⋂₀ (ZFSet.sep (fun y => ∃ x ∈ D, y = F x) 𝔹),
        ZFSet.sInter_sep_subset_of_𝔹_mem_𝔹 (fun _ ↦ id)⟩ : ZFSet.ZFBool) = ⊤ := by
    rwa [Subtype.mk.injEq]
  simpa [graphBoolDom] using congrArg graphBoolDom <|
    show ZFSet.ZFBool.not
        ⟨⋂₀ (ZFSet.sep (fun y => ∃ x ∈ D, y = F x) 𝔹),
          ZFSet.sInter_sep_subset_of_𝔹_mem_𝔹 (fun _ ↦ id)⟩ = ⊥ by
      rw [hbool, ZFSet.ZFBool.not_true_eq_false]

private theorem graphSomeBoolDomEqZftrueOfSInterEqZffalse
    {D : ZFSet} {F : ZFSet → ZFSet}
    (hsInter :
      (⋂₀ (ZFSet.sep (fun y => ∃ x ∈ D, y = F x) 𝔹) : ZFSet) = zffalse) :
    some
      (graphBoolDom
        (if h : (⋂₀ (ZFSet.sep (fun y => ∃ x ∈ D, y = F x) 𝔹) : ZFSet) ∈ 𝔹 then
          ZFSet.ZFBool.not
            ⟨⋂₀ (ZFSet.sep (fun y => ∃ x ∈ D, y = F x) 𝔹), h⟩
         else
          ZFSet.ZFBool.false)) =
      some ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
  rw [dif_pos (ZFSet.sInter_sep_subset_of_𝔹_mem_𝔹 (fun _ ↦ id))]
  exact congrArg some <| graphBoolDomEqZftrueOfSInterEqZffalse hsInter

private theorem graphSomeBoolDomEqZffalseOfSInterEqZftrue
    {D : ZFSet} {F : ZFSet → ZFSet}
    (hsInter :
      (⋂₀ (ZFSet.sep (fun y => ∃ x ∈ D, y = F x) 𝔹) : ZFSet) = zftrue) :
    some
      (graphBoolDom
        (if h : (⋂₀ (ZFSet.sep (fun y => ∃ x ∈ D, y = F x) 𝔹) : ZFSet) ∈ 𝔹 then
          ZFSet.ZFBool.not
            ⟨⋂₀ (ZFSet.sep (fun y => ∃ x ∈ D, y = F x) 𝔹), h⟩
         else
          ZFSet.ZFBool.false)) =
      some ⟨zffalse, SMTType.bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
  rw [dif_pos (ZFSet.sInter_sep_subset_of_𝔹_mem_𝔹 (fun _ ↦ id))]
  exact congrArg some <| graphBoolDomEqZffalseOfSInterEqZftrue hsInter

private theorem graphCastPairDomOfMem
    {α β α' β' : SMTType} {pα : α ⇝ α'} {pβ : β ⇝ β'} {x : ZFSet}
    (hcastpair :
      IsFunc ⟦α.pair β⟧ᶻ ⟦α'.pair β'⟧ᶻ (castZF_of_path (pα.pair pβ)).1)
    (hx : x ∈ ⟦α.pair β⟧ᶻ) :
    x ∈ (castZF_of_path (pα.pair pβ)).1.Dom hcastpair.1 := by
  simpa [ZFSet.is_func_dom_eq hcastpair] using hx

private theorem graphFstRangeSepNotOfNotRange
    {α α' : SMTType} {castα y : ZFSet}
    (hcastα : IsFunc ⟦α⟧ᶻ ⟦α'⟧ᶻ castα)
    (hx_range :
      y.π₁ ∉
        castα.Range
          (A := ⟦α⟧ᶻ) (B := ⟦α'⟧ᶻ)
          (hf := ZFSet.is_rel_of_is_pfunc (ZFSet.is_func_is_pfunc hcastα))) :
    ¬ (y.π₁ ∈ ⟦α'⟧ᶻ ∧
        ∃ x, (x ∈ ⟦α⟧ᶻ ∧ ∃ y' ∈ ⟦α'⟧ᶻ, x.pair y' ∈ castα) ∧
          x.pair y.π₁ ∈ castα) := by
  simpa [ZFSet.mem_sep] using hx_range

private theorem graphSndRangeSepNotOfNotRange
    {β β' : SMTType} {castβ y : ZFSet}
    (hcastβ : IsFunc ⟦β⟧ᶻ ⟦β'⟧ᶻ castβ)
    (hy_range :
      y.π₂ ∉
        castβ.Range
          (A := ⟦β⟧ᶻ) (B := ⟦β'⟧ᶻ)
          (hf := ZFSet.is_rel_of_is_pfunc (ZFSet.is_func_is_pfunc hcastβ))) :
    ¬ (y.π₂ ∈ ⟦β'⟧ᶻ ∧
        ∃ x, (x ∈ ⟦β⟧ᶻ ∧ ∃ y' ∈ ⟦β'⟧ᶻ, x.pair y' ∈ castβ) ∧
          x.pair y.π₂ ∈ castβ) := by
  simpa [ZFSet.mem_sep] using hy_range

private theorem graphDomEqOfTyEqAndFstEq
    {x y : ZFSet} {τ₁ τ₂ : SMTType}
    {hx : x ∈ ⟦τ₁⟧ᶻ} {hy : y ∈ ⟦τ₂⟧ᶻ}
    (hτ : τ₁ = τ₂) (hxy : x = y) :
    (⟨x, τ₁, hx⟩ : SMT.Dom) = ⟨y, τ₂, hy⟩ := by
  cases hτ
  cases hxy
  have hmem : hx = hy := Subsingleton.elim _ _
  cases hmem
  rfl

private theorem graphBodyTyOf
    {Γ : TypeContext} {«Δ» : RenamingContext.Context} {x z!_spec : Term}
    {x! z z! : 𝒱} {σ σ' : SMTType}
    (hgo_cov :
      ∀ Yfun : SMT.Dom,
        ∀ v ∈ SMT.fv (.exists [z] [σ] (((@ˢx) (.fst (.var z)) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)),
          v ∉ [z!] → (Function.update «Δ» x! (some Yfun) v).isSome = true)
    (hexists_cov :
      ∀ (Yfun W : SMT.Dom),
        RenamingContext.CoversFV
          (Function.update (Function.update «Δ» x! (some Yfun)) z! (some W))
          (.exists [z] [σ] (((@ˢx) (.fst (.var z)) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)))
    (hgo_exists :
      ∀ (Yfun : SMT.Dom)
        (w : Fin [z!].length → SMT.Dom)
        (hw : ∀ i, (w i).snd.fst = σ' ∧ (w i).fst ∈ ⟦σ'⟧ᶻ),
          (Term.abstract.go
              (Term.exists [z] [σ] (((@ˢx) (.fst (.var z)) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec))
              [z!]
              (Function.update «Δ» x! (some Yfun))
              (hgo_cov Yfun)).uncurry w =
            (Term.exists [z] [σ] (((@ˢx) (.fst (.var z)) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)).abstract
              (Function.update (Function.update «Δ» x! (some Yfun)) z! (some (w ⟨0, by simp⟩)))
              (hexists_cov Yfun (w ⟨0, by simp⟩)))
    (typ_exists :
      (AList.insert z! σ' Γ) ⊢ˢ
        (.exists [z] [σ] (((@ˢx) (.fst (.var z)) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)) :
        SMTType.bool)
    (hbody_total :
      ∀ (Yfun : SMT.Dom)
        (x_1 : Fin [z!].length → SMT.Dom)
        (hx_1 : ∀ i, (x_1 i).snd.fst = σ' ∧ (x_1 i).fst ∈ ⟦σ'⟧ᶻ),
          ⟦(Term.abstract.go
              (Term.exists [z] [σ] (((@ˢx) (.fst (.var z)) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec))
              [z!]
              (Function.update «Δ» x! (some Yfun))
              (hgo_cov Yfun)).uncurry x_1⟧ˢ.isSome =
            true)
    (Yfun : SMT.Dom)
    (x_1 : Fin [z!].length → SMT.Dom)
    (hx_1 : ∀ i, (x_1 i).snd.fst = σ' ∧ (x_1 i).fst ∈ ⟦σ'⟧ᶻ) :
    (⟦(Term.abstract.go
        (Term.exists [z] [σ] (((@ˢx) (.fst (.var z)) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec))
        [z!]
        (Function.update «Δ» x! (some Yfun))
        (hgo_cov Yfun)).uncurry x_1⟧ˢ.get
        (hbody_total Yfun x_1 hx_1)).snd.fst =
      SMTType.bool := by
  obtain ⟨D0, hden_body⟩ := Option.isSome_iff_exists.mp (hbody_total Yfun x_1 hx_1)
  have hden_exists :
      ⟦(Term.exists [z] [σ] (((@ˢx) (.fst (.var z)) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)).abstract
          (Function.update (Function.update «Δ» x! (some Yfun)) z! (some (x_1 ⟨0, by simp⟩)))
          (hexists_cov Yfun (x_1 ⟨0, by simp⟩))⟧ˢ =
        some D0 := by
    rw [←hgo_exists Yfun x_1 hx_1]
    exact hden_body
  have hD0_ty : D0.snd.fst = SMTType.bool :=
    denote_type_eq_of_typing (typ_t := typ_exists) (hden := hden_exists)
  have hget_eq :
      (⟦(Term.abstract.go
          (Term.exists [z] [σ] (((@ˢx) (.fst (.var z)) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec))
          [z!]
          (Function.update «Δ» x! (some Yfun))
          (hgo_cov Yfun)).uncurry x_1⟧ˢ.get
        (hbody_total Yfun x_1 hx_1)) = D0 := by
    apply Option.get_of_eq_some
    exact hden_body
  rw [hget_eq]
  exact hD0_ty

private theorem graphBodyTotal
    {Γ : TypeContext} {«Δ» : RenamingContext.Context} {x z!_spec : Term}
    {x! z z! : 𝒱} {α β α' β' : SMTType}
    {X : SMT.Dom} {pα : α ⇝ α'} {pβ : β ⇝ β'}
    (hgo_cov :
      ∀ Yfun : SMT.Dom,
        ∀ v ∈ SMT.fv
          (.exists [z] [α.pair β]
            ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)),
          v ∉ [z!] → (Function.update «Δ» x! (some Yfun) v).isSome = true)
    (hexists_cov :
      ∀ (Yfun W : SMT.Dom),
        RenamingContext.CoversFV
          (Function.update (Function.update «Δ» x! (some Yfun)) z! (some W))
          (.exists [z] [α.pair β]
            ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)))
    (hgo_exists :
      ∀ (Yfun : SMT.Dom)
        (w : Fin [z!].length → SMT.Dom)
        (hw : ∀ i, (w i).snd.fst = α'.pair β' ∧ (w i).fst ∈ ⟦α'.pair β'⟧ᶻ),
          (Term.abstract.go
              (Term.exists [z] [α.pair β]
                ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec))
              [z!]
              (Function.update «Δ» x! (some Yfun))
              (hgo_cov Yfun)).uncurry w =
            (Term.exists [z] [α.pair β]
              ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)).abstract
              (Function.update (Function.update «Δ» x! (some Yfun)) z! (some (w ⟨0, by simp⟩)))
              (hexists_cov Yfun (w ⟨0, by simp⟩)))
    (hcov_x_upd :
      ∀ Y : SMT.Dom, RenamingContext.CoversFV (Function.update «Δ» x! (some Y)) x)
    (denx_upd :
      ∀ Y : SMT.Dom, ⟦x.abstract (Function.update «Δ» x! (some Y)) (hcov_x_upd Y)⟧ˢ = some X)
    (hX_ty : X.snd.fst = α.fun β.option)
    (hX_func : IsFunc ⟦α⟧ᶻ ⟦β.option⟧ᶻ X.fst)
    (den_z_at :
      ∀ (x₀ : SMT.Dom)
        (hx₀_ty : x₀.snd.fst = α.pair β)
        (hx₀_mem : x₀.fst ∈ ⟦α.pair β⟧ᶻ),
        ∃ Φ X₀!,
          ∃ (_ :
            ⟦(Term.var z!).abstract
              (Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some X₀!))
              (by
                intro v hv
                rw [fv, List.mem_singleton] at hv
                subst hv
                simp [Function.update])⟧ˢ = some X₀!)
            (hφ :
              RenamingContext.CoversFV
                (Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some X₀!))
                z!_spec)
            (_ :
              ⟦z!_spec.abstract
                (Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some X₀!)) hφ⟧ˢ =
                some Φ),
            Φ.snd.fst = SMTType.bool ∧
              (Φ.fst = zftrue ∧ x₀.fst.pair X₀!.fst ∈ (castZF_of_path (pα.pair pβ)).1) ∧
                ∀ (Y : SMT.Dom),
                  Y.snd.fst = α'.pair β' →
                    ∀ (hφY :
                      RenamingContext.CoversFV
                        (Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some Y))
                        z!_spec),
                      ⟦z!_spec.abstract
                        (Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some Y))
                          hφY⟧ˢ.isSome = true)
    (fv_z!_spec : SMT.fv z!_spec ⊆ SMT.fv (.var z) ∪ {z!})
    (z_ne_z! : z ≠ z!)
    (x_ne_z : x! ≠ z)
    (x_ne_z! : x! ≠ z!)
    (z_not_mem_fv_x : z ∉ SMT.fv x)
    (z!_not_mem_fv_x : z! ∉ SMT.fv x)
    (typ_eq_some_body :
      (AList.insert z (α.pair β) (AList.insert z! (α'.pair β') Γ)) ⊢ˢ
        (((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) : SMTType.bool)
    (typ_z!_spec_body :
      (AList.insert z (α.pair β) (AList.insert z! (α'.pair β') Γ)) ⊢ˢ z!_spec : SMTType.bool)
    (Yfun : SMT.Dom)
    (x_1 : Fin [z!].length → SMT.Dom)
    (hx_1 : ∀ i, (x_1 i).snd.fst = α'.pair β' ∧ (x_1 i).fst ∈ ⟦α'.pair β'⟧ᶻ) :
    ⟦(Term.abstract.go
        (Term.exists [z] [α.pair β]
          ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec))
        [z!]
        (Function.update «Δ» x! (some Yfun))
        (hgo_cov Yfun)).uncurry x_1⟧ˢ.isSome =
      true := by
  let i0 : Fin [z!].length := ⟨0, by simp⟩
  have hx0_ty : (x_1 i0).snd.fst = α'.pair β' := by
    simpa [i0] using (hx_1 i0).1
  have hx0_mem : (x_1 i0).fst ∈ ⟦α'.pair β'⟧ᶻ := by
    simpa [hx0_ty] using (x_1 i0).snd.snd
  rw [hgo_exists Yfun x_1 hx_1]
  rw [SMT.Term.abstract, dite_cond_eq_true (eq_true (by rfl)), SMT.PHOAS.Term.exists, SMT.denote]
  simp only [Option.bind_eq_bind, Option.pure_def]
  have hlen_exists : [z].length > 0 := by
    simp
  rw [SMT.denote, dite_cond_eq_true (eq_true hlen_exists)]
  split_ifs with den_exists_isSome
  · simp
  · exfalso
    apply den_exists_isSome
    intro z_1 hz_1
    let j0 : Fin [z].length := ⟨0, by simp⟩
    have hz0_ty : (z_1 j0).snd.fst = α.pair β := by
      simpa [j0] using (hz_1 j0).1
    have hz0_mem : (z_1 j0).fst ∈ ⟦α.pair β⟧ᶻ := by
      simpa [hz0_ty] using (z_1 j0).snd.snd
    obtain ⟨hcov_app_goal, hden_app⟩ :=
      graphDenAppAt
        (hcov_x_upd := hcov_x_upd) (denx_upd := denx_upd)
        (hX_ty := hX_ty) (hX_func := hX_func)
        (z!_not_mem_fv_x := z!_not_mem_fv_x)
        (z_not_mem_fv_x := z_not_mem_fv_x)
        (Yfun := Yfun) (wy0 := x_1 i0)
        (z_1 j0) hz0_ty hz0_mem
    obtain ⟨hcov_some_goal, hden_some_snd⟩ :=
      graphDenSomeSndAt («Δ» := «Δ») (x! := x!) (z := z) (z! := z!)
        (Yfun := Yfun) (wy0 := x_1 i0) (x₀ := z_1 j0) hz0_ty hz0_mem
    obtain ⟨DeqSome, hden_eqsome, hDeqSome_ty⟩ :=
      denote_eq_some_of_some hden_app hden_some_snd rfl
    obtain ⟨hφY, Dspec, hden_spec, hDspec_ty⟩ :=
      graphDenSpecSomeAt
        (p := pα.pair pβ) (Yfun := Yfun) (wy0 := x_1 i0)
        (den_z_at := den_z_at) (fv_z!_spec := fv_z!_spec)
        (z_ne_z! := z_ne_z!) (x_ne_z := x_ne_z) (x_ne_z! := x_ne_z!)
        (typ_z!_spec_body := typ_z!_spec_body)
        (hwy0_ty := hx0_ty)
        (z_1 j0) hz0_ty hz0_mem
    obtain ⟨Dbody, hDbody, hDbody_ty⟩ :=
      denote_and_some_bool_of_some_bool hden_eqsome hDeqSome_ty hden_spec hDspec_ty
    have hnot_some := denote_not_isSome_of_some_bool (hden := hDbody) (hTy := hDbody_ty)
    rw [denote, Term.abstract.go]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Matrix.head_fin_const,
      Fin.zero_eta, Fin.isValue, Option.pure_def, Option.failure_eq_none, Option.bind_eq_bind,
      Function.OfArity.uncurry, Function.FromTypes.uncurry, Term.abstract.go]
    simpa [SMT.Term.abstract, SMT.denote, Option.bind_eq_bind, Option.pure_def,
      SMT.Term.abstract.go, Function.OfArity.uncurry, Function.FromTypes.uncurry,
      i0, j0, proof_irrel_heq] using hnot_some

private theorem graphLambdaIsSome
    {Γ : TypeContext} {«Δ» : RenamingContext.Context} {x z!_spec : Term}
    {x! z z! : 𝒱} {α β α' β' : SMTType}
    (hcov_lambda_upd :
      ∀ Y : SMT.Dom,
        RenamingContext.CoversFV
          (Function.update «Δ» x! (some Y))
          ((λˢ [z!]) [α'.pair β']
            (.exists [z] [α.pair β]
              ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec))))
    (hgo_cov :
      ∀ Yfun : SMT.Dom,
        ∀ v ∈ SMT.fv
          (.exists [z] [α.pair β]
            ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)),
          v ∉ [z!] → (Function.update «Δ» x! (some Yfun) v).isSome = true)
    (hexists_cov :
      ∀ (Yfun W : SMT.Dom),
        RenamingContext.CoversFV
          (Function.update (Function.update «Δ» x! (some Yfun)) z! (some W))
          (.exists [z] [α.pair β]
            ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)))
    (hgo_exists :
      ∀ (Yfun : SMT.Dom)
        (w : Fin [z!].length → SMT.Dom)
        (hw : ∀ i, (w i).snd.fst = α'.pair β' ∧ (w i).fst ∈ ⟦α'.pair β'⟧ᶻ),
          (Term.abstract.go
              (Term.exists [z] [α.pair β]
                ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec))
              [z!]
              (Function.update «Δ» x! (some Yfun))
              (hgo_cov Yfun)).uncurry w =
            (Term.exists [z] [α.pair β]
              ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)).abstract
              (Function.update (Function.update «Δ» x! (some Yfun)) z! (some (w ⟨0, by simp⟩)))
              (hexists_cov Yfun (w ⟨0, by simp⟩)))
    (typ_exists :
      (AList.insert z! (α'.pair β') Γ) ⊢ˢ
        (.exists [z] [α.pair β]
          ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)) :
        SMTType.bool)
    (hbody_total :
      ∀ (Yfun : SMT.Dom)
        (x_1 : Fin [z!].length → SMT.Dom)
        (hx_1 : ∀ i, (x_1 i).snd.fst = α'.pair β' ∧ (x_1 i).fst ∈ ⟦α'.pair β'⟧ᶻ),
          ⟦(Term.abstract.go
              (Term.exists [z] [α.pair β]
                ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec))
              [z!]
              (Function.update «Δ» x! (some Yfun))
              (hgo_cov Yfun)).uncurry x_1⟧ˢ.isSome =
            true)
    (Y : SMT.Dom) :
    ⟦((λˢ [z!]) [α'.pair β']
          (.exists [z] [α.pair β]
            ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec))).abstract
        (Function.update «Δ» x! (some Y)) (hcov_lambda_upd Y)⟧ˢ.isSome =
      true := by
  rw [SMT.Term.abstract, dite_cond_eq_true (eq_true (by rfl)), SMT.denote]
  split_ifs with hlen_pos den_t_isSome den_t_typ_det
  · simp
  · exfalso
    apply den_t_typ_det
    intro x_1 y_1 hx_1 hy_1
    have hx_1' : ∀ i, (x_1 i).snd.fst = α'.pair β' ∧ (x_1 i).fst ∈ ⟦α'.pair β'⟧ᶻ := by
      intro i
      simpa using hx_1 i
    have hy_1' : ∀ i, (y_1 i).snd.fst = α'.pair β' ∧ (y_1 i).fst ∈ ⟦α'.pair β'⟧ᶻ := by
      intro i
      simpa using hy_1 i
    rw [graphBodyTyOf
          (hgo_cov := hgo_cov) (hexists_cov := hexists_cov) (hgo_exists := hgo_exists)
          (typ_exists := typ_exists) (hbody_total := hbody_total) Y x_1 hx_1',
        graphBodyTyOf
          (hgo_cov := hgo_cov) (hexists_cov := hexists_cov) (hgo_exists := hgo_exists)
          (typ_exists := typ_exists) (hbody_total := hbody_total) Y y_1 hy_1']
  · exfalso
    exact den_t_isSome (fun {x_1} hx_1 => by
      have hx_1' : ∀ i, (x_1 i).snd.fst = α'.pair β' ∧ (x_1 i).fst ∈ ⟦α'.pair β'⟧ᶻ := by
        intro i
        simpa using hx_1 i
      exact hbody_total Y x_1 hx_1')
  · exfalso
    exact hlen_pos (by simp)

private theorem graphInnerNotBodyAllIsSome
    {«Δ» : RenamingContext.Context} {x z!_spec : Term}
    {x! z z! : 𝒱} {α β α' β' : SMTType}
    {Yfun wy0 : SMT.Dom}
    (den_app_at :
      ∀ (Yfun wy0 x₀ : SMT.Dom)
        (hx₀_ty : x₀.snd.fst = α.pair β)
        (hx₀_mem : x₀.fst ∈ ⟦α.pair β⟧ᶻ),
          ∃ hcov_app_goal :
            RenamingContext.CoversFV
              (Function.update
                (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                z (some x₀))
              ((@ˢx) (.fst (.var z))),
          ∃ Dapp,
            Dapp.snd.fst = β.option ∧
            ⟦((@ˢx) (.fst (.var z))).abstract
                (Function.update
                  (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                  z (some x₀))
                hcov_app_goal⟧ˢ =
              some Dapp)
    (den_spec_some_at :
      ∀ (Yfun wy0 x₀ : SMT.Dom)
        (hwy0_ty : wy0.snd.fst = α'.pair β')
        (hx₀_ty : x₀.snd.fst = α.pair β)
        (hx₀_mem : x₀.fst ∈ ⟦α.pair β⟧ᶻ),
        ∃ hφY :
            RenamingContext.CoversFV
              (Function.update
                (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                z (some x₀))
              z!_spec,
          ∃ Φ,
            ⟦z!_spec.abstract
                (Function.update
                  (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                  z (some x₀))
                hφY⟧ˢ =
              some Φ ∧
            Φ.snd.fst = SMTType.bool)
    (hwy0_ty : wy0.snd.fst = α'.pair β')
    (hgo_body_cov :
      ∀ v ∈ SMT.fv ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec),
        v ∉ [z] →
          (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0) v).isSome = true) :
    ∀ {x_1 : Fin [z].length → SMT.Dom},
      (∀ i, (x_1 i).snd.fst = [α.pair β][i] ∧ (x_1 i).fst ∈ ⟦[α.pair β][i]⟧ᶻ) →
        ⟦¬ˢ'
            (Term.abstract.go
                ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)
                [z]
                (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                hgo_body_cov).uncurry
              x_1⟧ˢ.isSome =
          true := by
  intro z_1 hz_1
  let j0 : Fin [z].length := ⟨0, by simp⟩
  have hz0_ty : (z_1 j0).snd.fst = α.pair β := by
    simpa [j0] using (hz_1 j0).1
  have hz0_mem : (z_1 j0).fst ∈ ⟦α.pair β⟧ᶻ := by
    simpa [hz0_ty] using (z_1 j0).snd.snd
  obtain ⟨hcov_app_goal, Dapp, hDapp_ty, hden_app⟩ :=
    den_app_at Yfun wy0 (z_1 j0) hz0_ty hz0_mem
  obtain ⟨hcov_some_goal, hden_some_snd⟩ :=
    graphDenSomeSndAt («Δ» := «Δ») (x! := x!) (z := z) (z! := z!)
      (Yfun := Yfun) (wy0 := wy0) (x₀ := z_1 j0) hz0_ty hz0_mem
  obtain ⟨DeqSome, hden_eqsome, hDeqSome_ty⟩ :=
    denote_eq_some_of_some hden_app hden_some_snd hDapp_ty
  obtain ⟨hφY, Dspec, hden_spec, hDspec_ty⟩ :=
    den_spec_some_at Yfun wy0 (z_1 j0) hwy0_ty hz0_ty hz0_mem
  obtain ⟨Dbody, hDbody, hDbody_ty⟩ :=
    denote_and_some_bool_of_some_bool hden_eqsome hDeqSome_ty hden_spec hDspec_ty
  have hnot_some := denote_not_isSome_of_some_bool (hden := hDbody) (hTy := hDbody_ty)
  rw [denote, Term.abstract.go]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Matrix.head_fin_const,
    Fin.zero_eta, Fin.isValue, Option.pure_def, Option.failure_eq_none,
    Option.bind_eq_bind, Function.OfArity.uncurry, Function.FromTypes.uncurry,
    Term.abstract.go]
  simpa [Term.abstract, proof_irrel_heq] using hnot_some

private theorem graphNotBodyValueEqZftrueOfSpecFalse
    {«Δ» : RenamingContext.Context} {x z!_spec : Term}
    {x! z z! : 𝒱} {α β : SMTType}
    {Yfun wy0 : SMT.Dom}
    (hgo_body_cov :
      ∀ v ∈ SMT.fv ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec),
        v ∉ [z] →
          (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0) v).isSome = true)
    (den_exists_isSome :
      ∀ {x_1 : Fin [z].length → SMT.Dom},
        (∀ i, (x_1 i).snd.fst = [α.pair β][i] ∧ (x_1 i).fst ∈ ⟦[α.pair β][i]⟧ᶻ) →
          ⟦¬ˢ'
              (Term.abstract.go
                  ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)
                  [z]
                  (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                  hgo_body_cov).uncurry
                x_1⟧ˢ.isSome =
            true)
    {x_1 : ZFSet}
    (hx_1 : x_1 ∈ ⟦α.pair β⟧ᶻ)
    {DeqSome Dspec : SMT.Dom}
    {hcov_eq_goal :
      RenamingContext.CoversFV
        (Function.update
          (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
          z (some ⟨x_1, α.pair β, hx_1⟩))
        ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))))}
    {hcov_body_goal :
      RenamingContext.CoversFV
        (Function.update
          (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
          z (some ⟨x_1, α.pair β, hx_1⟩))
        ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)}
    {hφY :
      RenamingContext.CoversFV
        (Function.update
          (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
          z (some ⟨x_1, α.pair β, hx_1⟩))
        z!_spec}
    (hden_eqsome :
      ⟦(((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))).abstract
          (Function.update
            (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
            z (some ⟨x_1, α.pair β, hx_1⟩))
          hcov_eq_goal⟧ˢ =
        some DeqSome)
    (hDeqSome_ty : DeqSome.snd.fst = SMTType.bool)
    (hden_spec :
      ⟦z!_spec.abstract
          (Function.update
            (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
            z (some ⟨x_1, α.pair β, hx_1⟩))
          hφY⟧ˢ =
        some Dspec)
    (hDspec_ty : Dspec.snd.fst = SMTType.bool)
    (hDspec_false : Dspec.fst = zffalse) :
    let w : Fin [z].length → SMT.Dom := fun _ => ⟨x_1, α.pair β, hx_1⟩
    (⟦¬ˢ'
        (Term.abstract.go
            ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)
            [z]
            (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
            hgo_body_cov).uncurry
          w⟧ˢ.get
      (den_exists_isSome (graphSingletonArg hx_1))).fst = zftrue := by
  have hden_and_false :
      ⟦((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec).abstract
          (Function.update
            (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
            z (some ⟨x_1, α.pair β, hx_1⟩))
          hcov_body_goal⟧ˢ =
        some ⟨zffalse, .bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
    rw [Term.abstract]
    exact denote_and_eq_zffalse_of_some_zffalse_right
      hden_eqsome hDeqSome_ty hden_spec hDspec_ty hDspec_false
  have hden_not_true :
      ⟦¬ˢ'
          ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec).abstract
            (Function.update
              (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
              z (some ⟨x_1, α.pair β, hx_1⟩))
            hcov_body_goal⟧ˢ =
        some ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
    exact denote_not_eq_zftrue_of_some_zffalse hden_and_false rfl rfl
  let w : Fin [z].length → SMT.Dom := fun _ => ⟨x_1, α.pair β, hx_1⟩
  have hget_not :
      (⟦¬ˢ'
          (Term.abstract.go
              ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)
              [z]
              (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
              hgo_body_cov).uncurry
          w⟧ˢ.get
        (den_exists_isSome (graphSingletonArg hx_1))) =
        ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
    apply Option.get_of_eq_some
    simp only [Term.abstract.go, Function.OfArity.uncurry,
      Function.FromTypes.uncurry]
    erw [hden_not_true]
  dsimp [w]
  erw [hget_not]

private theorem graphNotBodyValueEqZftrueOfEqFalse
    {«Δ» : RenamingContext.Context} {x z!_spec : Term}
    {x! z z! : 𝒱} {α β : SMTType}
    {Yfun wy0 : SMT.Dom}
    (hgo_body_cov :
      ∀ v ∈ SMT.fv ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec),
        v ∉ [z] →
          (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0) v).isSome = true)
    (den_exists_isSome :
      ∀ {x_1 : Fin [z].length → SMT.Dom},
        (∀ i, (x_1 i).snd.fst = [α.pair β][i] ∧ (x_1 i).fst ∈ ⟦[α.pair β][i]⟧ᶻ) →
          ⟦¬ˢ'
              (Term.abstract.go
                  ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)
                  [z]
                  (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                  hgo_body_cov).uncurry
                x_1⟧ˢ.isSome =
            true)
    {x_1 : ZFSet}
    (hx_1 : x_1 ∈ ⟦α.pair β⟧ᶻ)
    {DeqSome Dspec : SMT.Dom}
    {hcov_eq_goal :
      RenamingContext.CoversFV
        (Function.update
          (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
          z (some ⟨x_1, α.pair β, hx_1⟩))
        ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))))}
    {hcov_body_goal :
      RenamingContext.CoversFV
        (Function.update
          (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
          z (some ⟨x_1, α.pair β, hx_1⟩))
        ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)}
    {hφY :
      RenamingContext.CoversFV
        (Function.update
          (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
          z (some ⟨x_1, α.pair β, hx_1⟩))
        z!_spec}
    (hden_eqsome :
      ⟦(((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))).abstract
          (Function.update
            (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
            z (some ⟨x_1, α.pair β, hx_1⟩))
          hcov_eq_goal⟧ˢ =
        some DeqSome)
    (hDeqSome_ty : DeqSome.snd.fst = SMTType.bool)
    (hDeqSome_false : DeqSome.fst = zffalse)
    (hden_spec :
      ⟦z!_spec.abstract
          (Function.update
            (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
            z (some ⟨x_1, α.pair β, hx_1⟩))
          hφY⟧ˢ =
        some Dspec)
    (hDspec_ty : Dspec.snd.fst = SMTType.bool) :
    let w : Fin [z].length → SMT.Dom := fun _ => ⟨x_1, α.pair β, hx_1⟩
    (⟦¬ˢ'
        (Term.abstract.go
            ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)
            [z]
            (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
            hgo_body_cov).uncurry
          w⟧ˢ.get
      (den_exists_isSome (graphSingletonArg hx_1))).fst = zftrue := by
  have hden_and_false :
      ⟦((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec).abstract
          (Function.update
            (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
            z (some ⟨x_1, α.pair β, hx_1⟩))
          hcov_body_goal⟧ˢ =
        some ⟨zffalse, .bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
    rw [Term.abstract]
    exact denote_and_eq_zffalse_of_some_zffalse_left
      hden_eqsome hDeqSome_ty hDeqSome_false hden_spec hDspec_ty
  have hden_not_true :
      ⟦¬ˢ'
          ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec).abstract
            (Function.update
              (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
              z (some ⟨x_1, α.pair β, hx_1⟩))
            hcov_body_goal⟧ˢ =
        some ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
    exact denote_not_eq_zftrue_of_some_zffalse hden_and_false rfl rfl
  let w : Fin [z].length → SMT.Dom := fun _ => ⟨x_1, α.pair β, hx_1⟩
  have hget_not :
      (⟦¬ˢ'
          (Term.abstract.go
              ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)
              [z]
              (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
              hgo_body_cov).uncurry
          w⟧ˢ.get
        (den_exists_isSome (graphSingletonArg hx_1))) =
        ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
    apply Option.get_of_eq_some
    simp only [Term.abstract.go, Function.OfArity.uncurry,
      Function.FromTypes.uncurry]
    erw [hden_not_true]
  dsimp [w]
  erw [hget_not]

private def graphNotBodySInter
    {«Δ» : RenamingContext.Context} {x z!_spec : Term}
    {x! z z! : 𝒱} {α β : SMTType}
    (Yfun wy0 : SMT.Dom)
    (hgo_body_cov :
      ∀ v ∈ SMT.fv ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec),
        v ∉ [z] →
          (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0) v).isSome = true)
    (den_exists_isSome :
      ∀ {x_1 : Fin [z].length → SMT.Dom},
        (∀ i, (x_1 i).snd.fst = [α.pair β][i] ∧ (x_1 i).fst ∈ ⟦[α.pair β][i]⟧ᶻ) →
          ⟦¬ˢ'
              (Term.abstract.go
                  ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)
                  [z]
                  (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                  hgo_body_cov).uncurry
                x_1⟧ˢ.isSome =
            true) :
    ZFSet :=
  ⋂₀
    ZFSet.sep
      (fun y =>
        ∃ x_1 ∈ ⟦α.pair β⟧ᶻ,
          y =
            if h : x_1.hasArity 1 ∧ x_1 ∈ ⟦α.pair β⟧ᶻ then
              let w : Fin [z].length → SMT.Dom := fun _ => ⟨x_1, α.pair β, h.2⟩
              (⟦¬ˢ'
                    (Term.abstract.go
                        ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)
                        [z]
                        (Function.update
                          (Function.update «Δ» x! (some Yfun))
                          z! (some wy0))
                        hgo_body_cov).uncurry
                    w⟧ˢ.get
                (den_exists_isSome (graphSingletonArg h.2))).fst
            else zffalse)
      𝔹

private theorem graphNotBodyDenSetup
    {«Δ» : RenamingContext.Context} {x z!_spec : Term}
    {x! z z! : 𝒱} {α β α' β' : SMTType}
    {X X! wy0 x₀ : SMT.Dom}
    (hX_func : IsFunc ⟦α⟧ᶻ ⟦β.option⟧ᶻ X.fst)
    (hwy0_ty : wy0.snd.fst = α'.pair β')
    (hx₀_ty : x₀.snd.fst = α.pair β)
    (hx₀_mem : x₀.fst ∈ ⟦α.pair β⟧ᶻ)
    (den_app_at :
      ∀ (Yfun wy0 x₀ : SMT.Dom)
        (hx₀_ty : x₀.snd.fst = α.pair β)
        (hx₀_mem : x₀.fst ∈ ⟦α.pair β⟧ᶻ),
        ∃ hcov_app_goal :
            RenamingContext.CoversFV
              (Function.update
                (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                z (some x₀))
              ((@ˢx) (.fst (.var z))),
          ⟦((@ˢx) (.fst (.var z))).abstract
              (Function.update
                (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                z (some x₀))
              hcov_app_goal⟧ˢ =
            some ⟨↑(@ᶻX.fst
              ⟨x₀.fst.π₁, by
                have hx₀_fst_mem : x₀.fst.π₁ ∈ ⟦α⟧ᶻ :=
                  graphPairFstMem hx₀_mem
                simpa [ZFSet.is_func_dom_eq hX_func] using hx₀_fst_mem⟩), ⟨β.option, by
                  simpa [SMTType.toZFSet] using
                    (ZFSet.option_mem_option.mpr (graphPairSndMem hx₀_mem))⟩⟩)
    (den_spec_some_at :
      ∀ (Yfun wy0 x₀ : SMT.Dom)
        (hwy0_ty : wy0.snd.fst = α'.pair β')
        (hx₀_ty : x₀.snd.fst = α.pair β)
        (hx₀_mem : x₀.fst ∈ ⟦α.pair β⟧ᶻ),
        ∃ hφY :
            RenamingContext.CoversFV
              (Function.update
                (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                z (some x₀))
              z!_spec,
          ∃ Φ,
            ⟦z!_spec.abstract
                (Function.update
                  (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                  z (some x₀))
                hφY⟧ˢ =
              some Φ ∧
            Φ.snd.fst = SMTType.bool) :
    ∃ hcov_app_goal,
      ∃ hden_app :
        ⟦((@ˢx) (.fst (.var z))).abstract
            (Function.update
              (Function.update (Function.update «Δ» x! (some X!)) z! (some wy0))
              z (some x₀))
            hcov_app_goal⟧ˢ =
          some ⟨↑(@ᶻX.fst
            ⟨x₀.fst.π₁, by
              have hx₀_fst_mem : x₀.fst.π₁ ∈ ⟦α⟧ᶻ :=
                graphPairFstMem hx₀_mem
              simpa [ZFSet.is_func_dom_eq hX_func] using hx₀_fst_mem⟩), ⟨β.option, by
                simpa [SMTType.toZFSet] using
                  (ZFSet.option_mem_option.mpr (graphPairSndMem hx₀_mem))⟩⟩,
      ∃ hcov_some_goal,
      ∃ hden_some_snd :
        ⟦(Term.some (Term.snd (.var z))).abstract
            (Function.update
              (Function.update (Function.update «Δ» x! (some X!)) z! (some wy0))
              z (some x₀))
            hcov_some_goal⟧ˢ =
          some ⟨(ZFSet.Option.some (S := ⟦β⟧ᶻ)
                  ⟨x₀.fst.π₂, by
                    have hx₀_snd_mem : x₀.fst.π₂ ∈ ⟦β⟧ᶻ :=
                      graphPairSndMem hx₀_mem
                    exact hx₀_snd_mem⟩).1,
            β.option,
            (ZFSet.Option.some (S := ⟦β⟧ᶻ)
                ⟨x₀.fst.π₂, by
                  have hx₀_snd_mem : x₀.fst.π₂ ∈ ⟦β⟧ᶻ :=
                    graphPairSndMem hx₀_mem
                  exact hx₀_snd_mem⟩).2⟩,
      ∃ DeqSome,
      ∃ hden_eqsome :
        ⟦(((@ˢx) (.fst (.var z))).abstract
              (Function.update
                (Function.update (Function.update «Δ» x! (some X!)) z! (some wy0))
                z (some x₀))
              hcov_app_goal) =ˢ'
            (Term.some (Term.snd (.var z))).abstract
              (Function.update
                (Function.update (Function.update «Δ» x! (some X!)) z! (some wy0))
                z (some x₀))
              hcov_some_goal⟧ˢ =
          some DeqSome,
      ∃ hDeqSome_ty : DeqSome.snd.fst = SMTType.bool,
      ∃ hφY,
      ∃ Dspec,
      ∃ hden_spec :
        ⟦z!_spec.abstract
            (Function.update
              (Function.update (Function.update «Δ» x! (some X!)) z! (some wy0))
              z (some x₀))
            hφY⟧ˢ =
          some Dspec,
        Dspec.snd.fst = SMTType.bool := by
  obtain ⟨hcov_app_goal, hden_app⟩ :=
    den_app_at X! wy0 x₀ hx₀_ty hx₀_mem
  obtain ⟨hcov_some_goal, hden_some_snd⟩ :=
    graphDenSomeSndAt («Δ» := «Δ») (x! := x!) (z := z) (z! := z!)
      (Yfun := X!) (wy0 := wy0) (x₀ := x₀) hx₀_ty hx₀_mem
  obtain ⟨DeqSome, hden_eqsome, hDeqSome_ty⟩ :=
    denote_eq_some_of_some hden_app hden_some_snd rfl
  obtain ⟨hφY, Dspec, hden_spec, hDspec_ty⟩ :=
    den_spec_some_at X! wy0 x₀ hwy0_ty hx₀_ty hx₀_mem
  exact ⟨hcov_app_goal, hden_app, hcov_some_goal, hden_some_snd, DeqSome, hden_eqsome,
    hDeqSome_ty, hφY, Dspec, hden_spec, hDspec_ty⟩

set_option maxHeartbeats 1500000 in
private theorem graphNotBodySInterEqZffalseOfEqTrue
    {«Δ» : RenamingContext.Context} {x z!_spec : Term}
    {x! z z! : 𝒱} {α β α' β' : SMTType} {pα : α ⇝ α'} {pβ : β ⇝ β'}
    {X X! wy0 x₀ : SMT.Dom}
    (hX_func : IsFunc ⟦α⟧ᶻ ⟦β.option⟧ᶻ X.fst)
    (hwy0_ty : wy0.snd.fst = α'.pair β')
    (hx₀_ty : x₀.snd.fst = α.pair β)
    (hx₀_mem : x₀.fst ∈ ⟦α.pair β⟧ᶻ)
    (hgo_body_cov :
      ∀ v ∈ SMT.fv ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec),
        v ∉ [z] →
          (Function.update (Function.update «Δ» x! (some X!)) z! (some wy0) v).isSome = true)
    (den_exists_isSome :
      ∀ {x_1 : Fin [z].length → SMT.Dom},
        (∀ i, (x_1 i).snd.fst = [α.pair β][i] ∧ (x_1 i).fst ∈ ⟦[α.pair β][i]⟧ᶻ) →
          ⟦¬ˢ'
              (Term.abstract.go
                  ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)
                  [z]
                  (Function.update (Function.update «Δ» x! (some X!)) z! (some wy0))
                  hgo_body_cov).uncurry
                x_1⟧ˢ.isSome =
            true)
    (den_app_at :
      ∀ (Yfun wy0 x₀ : SMT.Dom)
        (hx₀_ty : x₀.snd.fst = α.pair β)
        (hx₀_mem : x₀.fst ∈ ⟦α.pair β⟧ᶻ),
        ∃ hcov_app_goal :
            RenamingContext.CoversFV
              (Function.update
                (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                z (some x₀))
              ((@ˢx) (.fst (.var z))),
          ⟦((@ˢx) (.fst (.var z))).abstract
              (Function.update
                (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                z (some x₀))
              hcov_app_goal⟧ˢ =
            some ⟨↑(@ᶻX.fst
              ⟨x₀.fst.π₁, by
                have hx₀_fst_mem : x₀.fst.π₁ ∈ ⟦α⟧ᶻ :=
                  graphPairFstMem hx₀_mem
                simpa [ZFSet.is_func_dom_eq hX_func] using hx₀_fst_mem⟩), ⟨β.option, by
                  simpa [SMTType.toZFSet] using
                    (ZFSet.option_mem_option.mpr (graphPairSndMem hx₀_mem))⟩⟩)
    (den_spec_some_at :
      ∀ (Yfun wy0 x₀ : SMT.Dom)
        (hwy0_ty : wy0.snd.fst = α'.pair β')
        (hx₀_ty : x₀.snd.fst = α.pair β)
        (hx₀_mem : x₀.fst ∈ ⟦α.pair β⟧ᶻ),
        ∃ hφY :
            RenamingContext.CoversFV
              (Function.update
                (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                z (some x₀))
              z!_spec,
          ∃ Φ,
            ⟦z!_spec.abstract
                (Function.update
                  (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                  z (some x₀))
                hφY⟧ˢ =
              some Φ ∧
            Φ.snd.fst = SMTType.bool)
    (den_spec_true_at_cast :
      ∀ (y Yfun wy0 x₀ : SMT.Dom)
        (hwy0_ty : wy0.snd.fst = α'.pair β')
        (hwy0_val : wy0.fst = y.fst)
        (hx₀_ty : x₀.snd.fst = α.pair β)
        (hx₀_mem : x₀.fst ∈ ⟦α.pair β⟧ᶻ)
        (hcast_xy : x₀.fst.pair y.fst ∈ (castZF_of_path (pα.pair pβ)).1),
        ∃ hφY :
            RenamingContext.CoversFV
              (Function.update
                (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                z (some x₀))
              z!_spec,
          ∃ Φ,
            ⟦z!_spec.abstract
                (Function.update
                  (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                  z (some x₀))
                hφY⟧ˢ =
              some Φ ∧
            Φ.fst = zftrue)
    (hcast_xy : x₀.fst.pair wy0.fst ∈ (castZF_of_path (pα.pair pβ)).1)
    (hXeq :
      @ᶻX.fst
        ⟨x₀.fst.π₁, by
          have hx₀_fst_mem : x₀.fst.π₁ ∈ ⟦α⟧ᶻ :=
            graphPairFstMem hx₀_mem
          simpa [ZFSet.is_func_dom_eq hX_func] using hx₀_fst_mem⟩ =
      ZFSet.Option.some (S := ⟦β⟧ᶻ)
        ⟨x₀.fst.π₂, graphPairSndMem hx₀_mem⟩) :
    graphNotBodySInter
      (x := x) (z!_spec := z!_spec) (x! := x!) (z := z) (z! := z!)
      (α := α) (β := β) X! wy0 hgo_body_cov den_exists_isSome = zffalse := by
  obtain ⟨hcov_app_goal, hden_app, hcov_some_goal, hden_some_snd, DeqSome, hden_eqsome,
      hDeqSome_ty, hφY, Dspec, hden_spec, hDspec_ty⟩ :=
    graphNotBodyDenSetup
      (x := x) (z!_spec := z!_spec) (x! := x!) (z := z) (z! := z!)
      (X := X) (X! := X!) (wy0 := wy0) (x₀ := x₀)
      hX_func hwy0_ty hx₀_ty hx₀_mem den_app_at den_spec_some_at
  obtain ⟨_, Φtrue, hden_spec_true, hΦtrue⟩ :=
    den_spec_true_at_cast wy0 X! wy0 x₀ hwy0_ty rfl hx₀_ty hx₀_mem hcast_xy
  have hDspec_true : Dspec.fst = zftrue := by
    have hEq : Dspec = Φtrue := by
      exact Option.some.inj (hden_spec.symm.trans hden_spec_true)
    simpa [hEq] using hΦtrue
  have hcov_eq_goal :
      RenamingContext.CoversFV
        (Function.update
          (Function.update (Function.update «Δ» x! (some X!)) z! (some wy0))
          z (some x₀))
        ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z)))) := by
    intro v hv
    have hv' :
        v ∈ SMT.fv (((@ˢx) (.fst (.var z)))) ∨
          v ∈ SMT.fv (.some (.snd (.var z))) := by
      simpa [fv] using hv
    rcases hv' with hvapp | hvsome
    · exact hcov_app_goal v (by simpa [fv] using hvapp)
    · exact hcov_some_goal v (by simpa [fv] using hvsome)
  have hDeqSome_true : DeqSome.fst = zftrue := by
    have hden_eq_true_phoas :
        ⟦(((@ˢx) (.fst (.var z))).abstract
              (Function.update
                (Function.update (Function.update «Δ» x! (some X!)) z! (some wy0))
                z (some x₀))
              hcov_app_goal) =ˢ'
            (Term.some (Term.snd (.var z))).abstract
              (Function.update
                (Function.update (Function.update «Δ» x! (some X!)) z! (some wy0))
                z (some x₀))
              hcov_some_goal⟧ˢ =
          some ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
      exact denote_eq_eq_zftrue_of_fst_eq hden_app hden_some_snd rfl (by
        simpa using hXeq)
    have hEq :
        DeqSome = ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
      exact Option.some.inj (hden_eqsome.symm.trans hden_eq_true_phoas)
    simpa [hEq]
  have hden_eq_true :
      ⟦(((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))).abstract
          (Function.update
            (Function.update (Function.update «Δ» x! (some X!)) z! (some wy0))
            z (some x₀))
          hcov_eq_goal⟧ˢ =
        some ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
    simpa [SMT.Term.abstract, SMT.denote, Option.bind_eq_bind, Option.pure_def,
      SMT.Term.abstract.go, Function.OfArity.uncurry, Function.FromTypes.uncurry,
      proof_irrel_heq] using
      (denote_eq_eq_zftrue_of_fst_eq hden_app hden_some_snd rfl (by
        simpa using hXeq))
  have hcov_body_goal :
      RenamingContext.CoversFV
        (Function.update
          (Function.update (Function.update «Δ» x! (some X!)) z! (some wy0))
          z (some x₀))
        ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec) := by
    intro v hv
    have hv' :
        v ∈ SMT.fv ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z)))) ∨
          v ∈ SMT.fv z!_spec := by
      rw [fv] at hv
      exact List.mem_append.mp hv
    rcases hv' with hveq | hvspec
    · exact hcov_eq_goal v hveq
    · exact hφY v hvspec
  have hden_and_true :
      ⟦((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec).abstract
          (Function.update
            (Function.update (Function.update «Δ» x! (some X!)) z! (some wy0))
            z (some x₀))
          hcov_body_goal⟧ˢ =
        some ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
    rw [Term.abstract]
    exact denote_and_eq_zftrue_of_some_zftrue
      hden_eq_true rfl rfl hden_spec hDspec_ty hDspec_true
  have hden_not_false :
      ⟦¬ˢ'
          ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec).abstract
            (Function.update
              (Function.update (Function.update «Δ» x! (some X!)) z! (some wy0))
              z (some x₀))
            hcov_body_goal⟧ˢ =
        some ⟨zffalse, .bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
    exact denote_not_eq_zffalse_of_some_zftrue hden_and_true rfl rfl
  let w : Fin [z].length → SMT.Dom := fun _ => x₀
  have hw :
      ∀ i : Fin [z].length, (w i).snd.fst = [α.pair β][i] ∧
        (w i).fst ∈ ⟦[α.pair β][i]⟧ᶻ := by
    intro i
    have hi0 : i = ⟨0, by simp⟩ := by
      apply Fin.ext
      simp
    cases hi0
    exact ⟨hx₀_ty, hx₀_mem⟩
  have hget_not_false :
      (⟦¬ˢ'
          (Term.abstract.go
              ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)
              [z]
              (Function.update
                (Function.update «Δ» x! (some X!))
                z! (some wy0))
              hgo_body_cov).uncurry
          w⟧ˢ.get
        (den_exists_isSome hw)) =
        ⟨zffalse, .bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
    apply Option.get_of_eq_some
    simpa [SMT.Term.abstract, SMT.denote, Option.bind_eq_bind,
      Option.pure_def, SMT.Term.abstract.go, Function.OfArity.uncurry,
      Function.FromTypes.uncurry, proof_irrel_heq, w] using hden_not_false
  have hw_eq : w = (fun _ => ⟨x₀.fst, α.pair β, hx₀_mem⟩) := by
    funext i
    exact graphDomEqOfTyEqAndFstEq hx₀_ty rfl
  have hget_not_false' :
      (⟦¬ˢ'
          (Term.abstract.go
              ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)
              [z]
              (Function.update
                (Function.update «Δ» x! (some X!))
                z! (some wy0))
              hgo_body_cov).uncurry
          (fun _ => ⟨x₀.fst, α.pair β, hx₀_mem⟩)⟧ˢ.get
        (den_exists_isSome (graphSingletonArg hx₀_mem))) =
        ⟨zffalse, .bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
    simpa [hw_eq, proof_irrel_heq] using hget_not_false
  unfold graphNotBodySInter
  apply sInter_sep_eq_empty_of_exists_eq_empty
  refine ⟨x₀.fst, hx₀_mem, ?_⟩
  have hx₀_cast : x₀.fst.hasArity 1 ∧ x₀.fst ∈ ⟦α.pair β⟧ᶻ := by
    constructor
    · exact (graphUnaryTarget (τ := α.pair β) hx₀_mem).1
    · exact hx₀_mem
  rw [dif_pos hx₀_cast]
  exact congrArg (fun D => D.1) hget_not_false'

set_option maxHeartbeats 1500000 in
private theorem graphNotBodySInterEqZftrueOfEqFalse
    {«Δ» : RenamingContext.Context} {x z!_spec : Term}
    {x! z z! : 𝒱} {α β α' β' : SMTType} {pα : α ⇝ α'} {pβ : β ⇝ β'}
    {X X! wy0 x₀ : SMT.Dom}
    (hX_func : IsFunc ⟦α⟧ᶻ ⟦β.option⟧ᶻ X.fst)
    (hwy0_ty : wy0.snd.fst = α'.pair β')
    (hx₀_ty : x₀.snd.fst = α.pair β)
    (hx₀_mem : x₀.fst ∈ ⟦α.pair β⟧ᶻ)
    (hgo_body_cov :
      ∀ v ∈ SMT.fv ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec),
        v ∉ [z] →
          (Function.update (Function.update «Δ» x! (some X!)) z! (some wy0) v).isSome = true)
    (den_exists_isSome :
      ∀ {x_1 : Fin [z].length → SMT.Dom},
        (∀ i, (x_1 i).snd.fst = [α.pair β][i] ∧ (x_1 i).fst ∈ ⟦[α.pair β][i]⟧ᶻ) →
          ⟦¬ˢ'
              (Term.abstract.go
                  ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)
                  [z]
                  (Function.update (Function.update «Δ» x! (some X!)) z! (some wy0))
                  hgo_body_cov).uncurry
                x_1⟧ˢ.isSome =
            true)
    (den_app_at :
      ∀ (Yfun wy0 x₀ : SMT.Dom)
        (hx₀_ty : x₀.snd.fst = α.pair β)
        (hx₀_mem : x₀.fst ∈ ⟦α.pair β⟧ᶻ),
        ∃ hcov_app_goal :
            RenamingContext.CoversFV
              (Function.update
                (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                z (some x₀))
              ((@ˢx) (.fst (.var z))),
          ⟦((@ˢx) (.fst (.var z))).abstract
              (Function.update
                (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                z (some x₀))
              hcov_app_goal⟧ˢ =
            some ⟨↑(@ᶻX.fst
              ⟨x₀.fst.π₁, by
                have hx₀_fst_mem : x₀.fst.π₁ ∈ ⟦α⟧ᶻ :=
                  graphPairFstMem hx₀_mem
                simpa [ZFSet.is_func_dom_eq hX_func] using hx₀_fst_mem⟩), ⟨β.option, by
                  simpa [SMTType.toZFSet] using
                    (ZFSet.option_mem_option.mpr (graphPairSndMem hx₀_mem))⟩⟩)
    (den_spec_some_at :
      ∀ (Yfun wy0 x₀ : SMT.Dom)
        (hwy0_ty : wy0.snd.fst = α'.pair β')
        (hx₀_ty : x₀.snd.fst = α.pair β)
        (hx₀_mem : x₀.fst ∈ ⟦α.pair β⟧ᶻ),
        ∃ hφY :
            RenamingContext.CoversFV
              (Function.update
                (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                z (some x₀))
              z!_spec,
          ∃ Φ,
            ⟦z!_spec.abstract
                (Function.update
                  (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                  z (some x₀))
                hφY⟧ˢ =
              some Φ ∧
            Φ.snd.fst = SMTType.bool)
    (den_spec_true_implies_cast :
      ∀ (Yfun wy0 x₀ : SMT.Dom)
        (hwy0_ty : wy0.snd.fst = α'.pair β')
        (hx₀_ty : x₀.snd.fst = α.pair β)
        (hx₀_mem : x₀.fst ∈ ⟦α.pair β⟧ᶻ)
        {Φ : SMT.Dom}
        (hφY :
          RenamingContext.CoversFV
            (Function.update
              (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
              z (some x₀))
            z!_spec)
        (hdenY :
          ⟦z!_spec.abstract
              (Function.update
                (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                z (some x₀))
              hφY⟧ˢ =
            some Φ)
        (htrue : Φ.fst = zftrue),
        x₀.fst.pair wy0.fst ∈ (castZF_of_path (pα.pair pβ)).1)
    (hcast_xy : x₀.fst.pair wy0.fst ∈ (castZF_of_path (pα.pair pβ)).1)
    (hXeq :
      @ᶻX.fst
        ⟨x₀.fst.π₁, by
          have hx₀_fst_mem : x₀.fst.π₁ ∈ ⟦α⟧ᶻ :=
            graphPairFstMem hx₀_mem
          simpa [ZFSet.is_func_dom_eq hX_func] using hx₀_fst_mem⟩ ≠
      ZFSet.Option.some (S := ⟦β⟧ᶻ)
        ⟨x₀.fst.π₂, graphPairSndMem hx₀_mem⟩) :
    graphNotBodySInter
      (x := x) (z!_spec := z!_spec) (x! := x!) (z := z) (z! := z!)
      (α := α) (β := β) X! wy0 hgo_body_cov den_exists_isSome = zftrue := by
  have hcastpair := (castZF_of_path (pα.pair pβ)).2
  unfold graphNotBodySInter
  apply sInter_sep_eq_zftrue_of_forall_eq_zftrue
  · exact ⟨(α.pair β).defaultZFSet, SMTType.mem_toZFSet_of_defaultZFSet⟩
  · intro x_1 hx_1
    have hx1 := graphUnaryTarget (τ := α.pair β) hx_1
    have hx_cast : x_1.hasArity 1 ∧ x_1 ∈ ⟦α.pair β⟧ᶻ := by
      constructor
      · exact hx1.1
      · exact hx_1
    rw [dif_pos hx_cast]
    obtain ⟨hcov_app_goal, hden_app, hcov_some_goal, hden_some_snd, DeqSome, hden_eqsome,
        hDeqSome_ty, hφY, Dspec, hden_spec, hDspec_ty⟩ :=
      graphNotBodyDenSetup
        (x := x) (z!_spec := z!_spec) (x! := x!) (z := z) (z! := z!)
        (X := X) (X! := X!) (wy0 := wy0) (x₀ := ⟨x_1, α.pair β, hx_1⟩)
        hX_func hwy0_ty rfl hx_1 den_app_at den_spec_some_at
    have hcov_eq_goal :
        RenamingContext.CoversFV
          (Function.update
            (Function.update (Function.update «Δ» x! (some X!)) z! (some wy0))
            z (some ⟨x_1, α.pair β, hx_1⟩))
          ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z)))) :=
      graphEqCovers hcov_app_goal hcov_some_goal
    have hcov_body_goal :
        RenamingContext.CoversFV
          (Function.update
            (Function.update (Function.update «Δ» x! (some X!)) z! (some wy0))
            z (some ⟨x_1, α.pair β, hx_1⟩))
          ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec) :=
      graphEqSpecCovers hcov_eq_goal hφY
    have hDspec_bool : Dspec.fst ∈ 𝔹 := graphBoolMemOfTyEqBool hDspec_ty
    have hden_eq :
        ⟦(((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))).abstract
            (Function.update
              (Function.update (Function.update «Δ» x! (some X!)) z! (some wy0))
              z (some ⟨x_1, α.pair β, hx_1⟩))
            hcov_eq_goal⟧ˢ =
          some DeqSome := by
      rw [Term.abstract]
      exact hden_eqsome
    rw [ZFSet.ZFBool.mem_𝔹_iff] at hDspec_bool
    rcases hDspec_bool with hDspec_false | hDspec_true
    · simpa [proof_irrel_heq] using
        graphNotBodyValueEqZftrueOfSpecFalse
          («Δ» := «Δ») (x := x) (z!_spec := z!_spec)
          (x! := x!) (z := z) (z! := z!)
          (α := α) (β := β) (Yfun := X!) (wy0 := wy0)
          hgo_body_cov den_exists_isSome hx_1
          (hcov_eq_goal := hcov_eq_goal)
          (hcov_body_goal := hcov_body_goal)
          (hφY := hφY)
          hden_eq hDeqSome_ty hden_spec hDspec_ty hDspec_false
    · have hx1_dom_castpair :
          x_1 ∈ (castZF_of_path (pα.pair pβ)).1.Dom hcastpair.1 := by
        exact graphCastPairDomOfMem hcastpair hx_1
      have hx₀_dom_castpair :
          x₀.fst ∈ (castZF_of_path (pα.pair pβ)).1.Dom hcastpair.1 := by
        exact graphCastPairDomOfMem hcastpair hx₀_mem
      have hcast_x1y :
          @ᶻ(castZF_of_path (pα.pair pβ)).1 ⟨x_1, hx1_dom_castpair⟩ = wy0.fst := by
        have := ZFSet.fapply.of_pair
          (hf := ZFSet.is_func_is_pfunc hcastpair)
          (den_spec_true_implies_cast X! wy0 ⟨x_1, α.pair β, hx_1⟩
            hwy0_ty rfl hx_1 hφY hden_spec hDspec_true)
        simpa only [Subtype.ext_iff] using this
      have hcast_x₀y :
          @ᶻ(castZF_of_path (pα.pair pβ)).1 ⟨x₀.fst, hx₀_dom_castpair⟩ = wy0.fst := by
        have := ZFSet.fapply.of_pair
          (hf := ZFSet.is_func_is_pfunc hcastpair) hcast_xy
        simpa only [Subtype.ext_iff] using this
      have hx1_eq_x₀ : x_1 = x₀.fst := by
        rw [← hcast_x1y, ← Subtype.ext_iff] at hcast_x₀y
        have := IsInjective.apply_inj hcastpair
          (castZF_of_path_injective (pα.pair pβ)) hcast_x₀y
        symm
        simpa only [Subtype.mk.injEq] using this
      have hDeqSome_bool : DeqSome.fst ∈ 𝔹 := graphBoolMemOfTyEqBool hDeqSome_ty
      rw [ZFSet.ZFBool.mem_𝔹_iff] at hDeqSome_bool
      have hDeqSome_false : DeqSome.fst = zffalse := by
        rcases hDeqSome_bool with hDeqSome_false | hDeqSome_true
        · exact hDeqSome_false
        · exfalso
          have hEq_app_some :
              (@ᶻX.fst
                  ⟨x_1.π₁, by
                    have hx1_fst_mem : x_1.π₁ ∈ ⟦α⟧ᶻ :=
                      graphPairFstMem hx_1
                    simpa [ZFSet.is_func_dom_eq hX_func] using hx1_fst_mem⟩) =
                ZFSet.Option.some (S := ⟦β⟧ᶻ)
                  ⟨x_1.π₂, graphPairSndMem hx_1⟩ := by
            simpa using
              denote_eq_true_implies_fst_eq
                hden_app hden_some_snd rfl hden_eqsome hDeqSome_true
          have hEq_x₀ :
              @ᶻX.fst
                ⟨x₀.fst.π₁, by
                  have hx₀_fst_mem : x₀.fst.π₁ ∈ ⟦α⟧ᶻ :=
                    graphPairFstMem hx₀_mem
                  simpa [ZFSet.is_func_dom_eq hX_func] using hx₀_fst_mem⟩ =
              ZFSet.Option.some (S := ⟦β⟧ᶻ)
                ⟨x₀.fst.π₂, graphPairSndMem hx₀_mem⟩ := by
            subst hx1_eq_x₀
            simpa [proof_irrel_heq] using hEq_app_some
          exact hXeq hEq_x₀
      simpa [proof_irrel_heq] using
        graphNotBodyValueEqZftrueOfEqFalse
          («Δ» := «Δ») (x := x) (z!_spec := z!_spec)
          (x! := x!) (z := z) (z! := z!)
          (α := α) (β := β) (Yfun := X!) (wy0 := wy0)
          hgo_body_cov den_exists_isSome hx_1
          (hcov_eq_goal := hcov_eq_goal)
          (hcov_body_goal := hcov_body_goal)
          (hφY := hφY)
          hden_eq hDeqSome_ty hDeqSome_false hden_spec hDspec_ty

set_option maxHeartbeats 1500000 in
private theorem graphHsInterTrueOfNoCast
    {«Δ» : RenamingContext.Context} {x z!_spec : Term}
    {x! z z! : 𝒱} {α β α' β' : SMTType} {pα : α ⇝ α'} {pβ : β ⇝ β'}
    {X! wy0 : SMT.Dom}
    (hwy0_ty : wy0.snd.fst = α'.pair β')
    (hgo_body_cov :
      ∀ v ∈ SMT.fv ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec),
        v ∉ [z] →
          (Function.update (Function.update «Δ» x! (some X!)) z! (some wy0) v).isSome = true)
    (den_exists_isSome :
      ∀ {x_1 : Fin [z].length → SMT.Dom},
        (∀ i, (x_1 i).snd.fst = [α.pair β][i] ∧ (x_1 i).fst ∈ ⟦[α.pair β][i]⟧ᶻ) →
          ⟦¬ˢ'
              (Term.abstract.go
                  ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)
                  [z]
                  (Function.update (Function.update «Δ» x! (some X!)) z! (some wy0))
                  hgo_body_cov).uncurry
                x_1⟧ˢ.isSome =
            true)
    (den_app_at :
      ∀ (wy0 x₀ : SMT.Dom)
        (hx₀_ty : x₀.snd.fst = α.pair β)
        (hx₀_mem : x₀.fst ∈ ⟦α.pair β⟧ᶻ),
        ∃ hcov_app_goal :
            RenamingContext.CoversFV
              (Function.update
                (Function.update (Function.update «Δ» x! (some X!)) z! (some wy0))
                z (some x₀))
              ((@ˢx) (.fst (.var z))),
          ∃ Dapp,
            Dapp.snd.fst = β.option ∧
            ⟦((@ˢx) (.fst (.var z))).abstract
                (Function.update
                  (Function.update (Function.update «Δ» x! (some X!)) z! (some wy0))
                  z (some x₀))
                hcov_app_goal⟧ˢ =
              some Dapp)
    (den_spec_some_at :
      ∀ (wy0 x₀ : SMT.Dom)
        (hwy0_ty : wy0.snd.fst = α'.pair β')
        (hx₀_ty : x₀.snd.fst = α.pair β)
        (hx₀_mem : x₀.fst ∈ ⟦α.pair β⟧ᶻ),
        ∃ hφY :
            RenamingContext.CoversFV
              (Function.update
                (Function.update (Function.update «Δ» x! (some X!)) z! (some wy0))
                z (some x₀))
              z!_spec,
          ∃ Φ,
            ⟦z!_spec.abstract
                (Function.update
                  (Function.update (Function.update «Δ» x! (some X!)) z! (some wy0))
                  z (some x₀))
                hφY⟧ˢ =
              some Φ ∧
            Φ.snd.fst = SMTType.bool)
    (den_spec_true_implies_cast :
      ∀ (wy0 x₀ : SMT.Dom)
        (hwy0_ty : wy0.snd.fst = α'.pair β')
        (hx₀_ty : x₀.snd.fst = α.pair β)
        (hx₀_mem : x₀.fst ∈ ⟦α.pair β⟧ᶻ)
        {Φ : SMT.Dom}
        (hφY :
          RenamingContext.CoversFV
            (Function.update
              (Function.update (Function.update «Δ» x! (some X!)) z! (some wy0))
              z (some x₀))
            z!_spec)
        (hdenY :
          ⟦z!_spec.abstract
              (Function.update
                (Function.update (Function.update «Δ» x! (some X!)) z! (some wy0))
                z (some x₀))
              hφY⟧ˢ =
            some Φ)
        (htrue : Φ.fst = zftrue),
        x₀.fst.pair wy0.fst ∈ (castZF_of_path (pα.pair pβ)).1)
    (no_cast :
      ∀ ⦃x_1 : ZFSet⦄,
        x_1 ∈ ⟦α.pair β⟧ᶻ →
          x_1.pair wy0.fst ∈ (castZF_of_path (pα.pair pβ)).1 →
            False) :
    (⋂₀
      ZFSet.sep
        (fun y =>
          ∃ x_1 ∈ ⟦α.pair β⟧ᶻ,
            y =
              if h : x_1.hasArity 1 ∧ x_1 ∈ ⟦α.pair β⟧ᶻ then
                let w : Fin [z].length → SMT.Dom := fun _ => ⟨x_1, α.pair β, h.2⟩
                (⟦¬ˢ'
                      (Term.abstract.go
                          ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)
                          [z]
                          (Function.update
                            (Function.update «Δ» x! (some X!))
                            z! (some wy0))
                          hgo_body_cov).uncurry
                      w⟧ˢ.get
                  (den_exists_isSome (graphSingletonArg h.2))).fst
              else zffalse)
        𝔹 : ZFSet) = zftrue := by
  apply sInter_sep_eq_zftrue_of_forall_eq_zftrue
  · exact ⟨(α.pair β).defaultZFSet, SMTType.mem_toZFSet_of_defaultZFSet⟩
  · intro x_1 hx_1
    have hx1 := graphUnaryTarget (τ := α.pair β) hx_1
    have hx_cast : x_1.hasArity 1 ∧ x_1 ∈ ⟦α.pair β⟧ᶻ := by
      constructor
      · exact hx1.1
      · exact hx_1
    rw [dif_pos hx_cast]
    obtain ⟨hcov_app_goal, Dapp, hDapp_ty, hden_app⟩ :=
      den_app_at wy0 ⟨x_1, α.pair β, hx_1⟩ rfl hx_1
    obtain ⟨hcov_some_goal, hden_some_snd⟩ :=
      graphDenSomeSndAt («Δ» := «Δ») (x! := x!) (z := z) (z! := z!)
        (Yfun := X!) (wy0 := wy0) (x₀ := ⟨x_1, α.pair β, hx_1⟩) rfl hx_1
    obtain ⟨DeqSome, hden_eqsome, hDeqSome_ty⟩ :=
      denote_eq_some_of_some hden_app hden_some_snd hDapp_ty
    obtain ⟨hφY, Dspec, hden_spec, hDspec_ty⟩ :=
      den_spec_some_at wy0 ⟨x_1, α.pair β, hx_1⟩ hwy0_ty rfl hx_1
    have hcov_eq_goal :
        RenamingContext.CoversFV
          (Function.update
            (Function.update (Function.update «Δ» x! (some X!)) z! (some wy0))
            z (some ⟨x_1, α.pair β, hx_1⟩))
          ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z)))) :=
      graphEqCovers hcov_app_goal hcov_some_goal
    have hcov_body_goal :
        RenamingContext.CoversFV
          (Function.update
            (Function.update (Function.update «Δ» x! (some X!)) z! (some wy0))
            z (some ⟨x_1, α.pair β, hx_1⟩))
          ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec) :=
      graphEqSpecCovers hcov_eq_goal hφY
    have hDspec_bool : Dspec.fst ∈ 𝔹 := graphBoolMemOfTyEqBool hDspec_ty
    have hden_eq :
        ⟦(((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))).abstract
            (Function.update
              (Function.update (Function.update «Δ» x! (some X!)) z! (some wy0))
              z (some ⟨x_1, α.pair β, hx_1⟩))
            hcov_eq_goal⟧ˢ =
          some DeqSome := by
      rw [Term.abstract]
      exact hden_eqsome
    rw [ZFSet.ZFBool.mem_𝔹_iff] at hDspec_bool
    have hDspec_false : Dspec.fst = zffalse := by
      rcases hDspec_bool with hDspec_false | hDspec_true
      · exact hDspec_false
      · exfalso
        exact no_cast hx_1 <|
          den_spec_true_implies_cast wy0
            ⟨x_1, α.pair β, hx_1⟩ hwy0_ty rfl hx_1 hφY hden_spec hDspec_true
    simpa [proof_irrel_heq] using
      graphNotBodyValueEqZftrueOfSpecFalse
        («Δ» := «Δ») (x := x) (z!_spec := z!_spec)
        (x! := x!) (z := z) (z! := z!)
        (α := α) (β := β) (Yfun := X!) (wy0 := wy0)
        hgo_body_cov den_exists_isSome hx_1
        (hcov_eq_goal := hcov_eq_goal)
        (hcov_body_goal := hcov_body_goal)
        (hφY := hφY)
        hden_eq hDeqSome_ty hden_spec hDspec_ty hDspec_false

private theorem graphPairVarPre
    {St₁ St₂ St₃ : EncoderState} {x! z : 𝒱} {α β α' β' : SMTType}
    (sub : AList.keys St₁.types ⊆ St₁.env.usedVars)
    (St₂_types_eq :
      St₂.types = AList.insert x! ((α'.pair β').fun SMTType.bool) St₁.types)
    (St₂_used_eq :
      St₂.env.usedVars = x! :: St₁.env.usedVars)
    (St₃_types_eq :
      St₃.types = AList.insert z (α.pair β) St₂.types)
    (St₃_used_eq :
      St₃.env.usedVars = z :: St₂.env.usedVars) :
    St₃.types = St₃.types ∧
      St₃.env.freshvarsc = St₃.env.freshvarsc ∧
        AList.keys St₃.types ⊆ St₃.env.usedVars ∧
          St₃.env.usedVars = St₃.env.usedVars := by
  refine ⟨rfl, rfl, ?_, rfl⟩
  have keys_sub₂ : AList.keys St₂.types ⊆ St₂.env.usedVars := by
    rw [St₂_types_eq, St₂_used_eq, AList.keys_insert]
    intro v hv
    rw [List.mem_cons] at hv ⊢
    rcases hv with rfl | hv
    · exact Or.inl rfl
    · exact Or.inr (sub (List.mem_of_mem_erase hv))
  rw [St₃_types_eq, St₃_used_eq, AList.keys_insert]
  intro v hv
  rw [List.mem_cons] at hv ⊢
  rcases hv with rfl | hv
  · exact Or.inl rfl
  · exact Or.inr (keys_sub₂ (List.mem_of_mem_erase hv))

private theorem graphRunPairVarSpec
    {α β α' β' : SMTType} {pα : α ⇝ α'} {pβ : β ⇝ β'}
    {name : String} {z : 𝒱} {St₃ : EncoderState} :
    ⦃fun st => ⌜st = St₃⌝⦄
      loosenAux_prf s!"{name}_funGraph_pair" (pα.pair pβ) (.var z)
    ⦃PostCond.mayThrow fun out st =>
      ⌜StateT.run (loosenAux_prf s!"{name}_funGraph_pair" (pα.pair pβ) (.var z)) St₃ =
        Except.ok (out, st)⌝⦄ := by
  unfold Std.Do.Triple
  intro st hst
  subst st
  simp only [wp, PredTrans.pushArg_apply, PredTrans.pushExcept_apply, PredTrans.pure_apply]
  cases hrun : Id.run ((loosenAux_prf s!"{name}_funGraph_pair" (pα.pair pβ) (.var z)) St₃) with
  | error e =>
      trivial
  | ok a =>
      simpa using hrun

private theorem graphDenZAt.{u}
    {«Δ» : RenamingContext.Context.{u}}
    {α β α' β' : SMTType} {pα : α ⇝ α'} {pβ : β ⇝ β'}
    (pα_ih : GraphOuterIH.{u} pα)
    (pβ_ih : GraphOuterIH.{u} pβ)
    {St₁ St₂ St₃ St₄ : EncoderState} {name : String} {x! z z! : 𝒱} {z!_spec : Term}
    (sub : AList.keys St₁.types ⊆ St₁.env.usedVars)
    (St₂_types_eq :
      St₂.types = AList.insert x! ((α'.pair β').fun SMTType.bool) St₁.types)
    (St₂_used_eq :
      St₂.env.usedVars = x! :: St₁.env.usedVars)
    (St₃_types_eq :
      St₃.types = AList.insert z (α.pair β) St₂.types)
    (St₃_used_eq :
      St₃.env.usedVars = z :: St₂.env.usedVars)
    (typ_var_z_St₃ : St₃.types ⊢ˢ .var z : α.pair β)
    (hrun :
      Id.run ((loosenAux_prf s!"{name}_funGraph_pair" (pα.pair pβ) (.var z)) St₃) =
        Except.ok ((z!, z!_spec), St₄)) :
    ∀ (x₀ : SMT.Dom)
      (hx₀_ty : x₀.snd.fst = α.pair β)
      (hx₀_mem : x₀.fst ∈ ⟦α.pair β⟧ᶻ),
      ∃ Φ X₀!,
        ∃ (_ :
          ⟦(Term.var z!).abstract
              (Function.update
                (fun v => if v = z then some x₀ else «Δ» v) z! (some X₀!))
              (by
                intro v hv
                rw [fv, List.mem_singleton] at hv
                subst hv
                simp [Function.update])⟧ˢ =
            some X₀!)
          (hφ :
            RenamingContext.CoversFV
              (Function.update
                (fun v => if v = z then some x₀ else «Δ» v) z! (some X₀!))
              z!_spec)
          (_ :
            ⟦z!_spec.abstract
                (Function.update
                  (fun v => if v = z then some x₀ else «Δ» v) z! (some X₀!))
                hφ⟧ˢ =
              some Φ),
          Φ.snd.fst = SMTType.bool ∧
            (Φ.fst = zftrue ∧ x₀.fst.pair X₀!.fst ∈ (castZF_of_path (pα.pair pβ)).1) ∧
              ∀ (Y : SMT.Dom),
                Y.snd.fst = α'.pair β' →
                  ∀ (hφY :
                    RenamingContext.CoversFV
                      (Function.update
                        (fun v => if v = z then some x₀ else «Δ» v) z! (some Y))
                      z!_spec),
                    ⟦z!_spec.abstract
                        (Function.update
                          (fun v => if v = z then some x₀ else «Δ» v) z! (some Y))
                        hφY⟧ˢ.isSome =
                      true := by
  intro x₀ hx₀_ty hx₀_mem
  let Δx₀ : RenamingContext.Context := fun v => if v = z then some x₀ else «Δ» v
  have hcov_var_z_x₀ : RenamingContext.CoversFV Δx₀ (.var z) := by
    intro v hv
    rw [fv, List.mem_singleton] at hv
    subst hv
    simp [Δx₀]
  have pf_var_z_x₀ : GraphPf Δx₀ := by
    intro xz! Xz! v hv
    rw [fv, List.mem_singleton] at hv
    subst hv
    simp [Function.update]
  have ih_pair_z_x₀ := loosenAux_prf_spec.pair
    (Δx₀) (pα := pα) (pβ := pβ) pf_var_z_x₀
    (fun {Λ} {n} {used} {name} {x} htyp hx' => pα_ih htyp Δx₀ hx' pf_var_z_x₀)
    (fun {Λ} {n} {used} {name} {x} htyp hx' => pβ_ih htyp Δx₀ hx' pf_var_z_x₀)
    (Λ := St₃.types) (n := St₃.env.freshvarsc) (used := St₃.env.usedVars)
    (name := s!"{name}_funGraph_pair") (x := .var z) typ_var_z_St₃ hcov_var_z_x₀
  have post_x₀ := ih_pair_z_x₀ St₃ <|
    graphPairVarPre sub St₂_types_eq St₂_used_eq St₃_types_eq St₃_used_eq
  simp only [wp, PredTrans.pushArg_apply, PredTrans.pushExcept_apply, PredTrans.pure_apply] at post_x₀
  rw [hrun] at post_x₀
  have hden_var_z_x₀ :
      ⟦(Term.var z).abstract Δx₀ hcov_var_z_x₀⟧ˢ = some x₀ := by
    rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some_inj]
    apply Option.get_of_eq_some
    simp [Δx₀]
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hden_z_x₀⟩ := post_x₀
  exact hden_z_x₀ x₀ hden_var_z_x₀

private theorem graphDenZExactAt
    {«Δ» : RenamingContext.Context}
    {α β α' β' : SMTType} {pα : α ⇝ α'} {pβ : β ⇝ β'}
    {St₁ St₂ St₃ St₄ : EncoderState} {name : String} {x! z z! : 𝒱} {z!_spec : Term}
    (sub : AList.keys St₁.types ⊆ St₁.env.usedVars)
    (St₂_types_eq :
      St₂.types = AList.insert x! ((α'.pair β').fun SMTType.bool) St₁.types)
    (St₂_used_eq :
      St₂.env.usedVars = x! :: St₁.env.usedVars)
    (St₃_types_eq :
      St₃.types = AList.insert z (α.pair β) St₂.types)
    (St₃_used_eq :
      St₃.env.usedVars = z :: St₂.env.usedVars)
    (typ_var_z_St₃ : St₃.types ⊢ˢ .var z : α.pair β)
    (hrun :
      Id.run ((loosenAux_prf s!"{name}_funGraph_pair" (pα.pair pβ) (.var z)) St₃) =
        Except.ok ((z!, z!_spec), St₄)) :
    ∀ (x₀ : SMT.Dom)
      (hx₀_ty : x₀.snd.fst = α.pair β)
      (hx₀_mem : x₀.fst ∈ ⟦α.pair β⟧ᶻ)
      {Y Φ : SMT.Dom}
      (hY_ty : Y.snd.fst = α'.pair β')
      (hφY :
        RenamingContext.CoversFV
          (Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some Y))
          z!_spec)
      (hdenY :
        ⟦z!_spec.abstract
            (Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some Y))
            hφY⟧ˢ =
          some Φ)
      (htrue : Φ.fst = zftrue),
      x₀.fst.pair Y.fst ∈ (castZF_of_path (pα.pair pβ)).1 := by
  intro x₀ hx₀_ty hx₀_mem Y Φ hY_ty hφY hdenY htrue
  let Δx₀ : RenamingContext.Context := fun v => if v = z then some x₀ else «Δ» v
  have hcov_var_z_x₀ : RenamingContext.CoversFV Δx₀ (.var z) := by
    intro v hv
    rw [fv, List.mem_singleton] at hv
    subst hv
    simp [Δx₀]
  have exact_var_z_x₀ := loosenAux_prf_exact
    (Λ := St₃.types) (n := St₃.env.freshvarsc) (used := St₃.env.usedVars)
    (name := s!"{name}_funGraph_pair") (x := .var z) typ_var_z_St₃ (pα.pair pβ) Δx₀
    hcov_var_z_x₀
  have post_x₀ := exact_var_z_x₀ St₃ <|
    graphPairVarPre sub St₂_types_eq St₂_used_eq St₃_types_eq St₃_used_eq
  simp only [wp, PredTrans.pushArg_apply, PredTrans.pushExcept_apply, PredTrans.pure_apply] at post_x₀
  rw [hrun] at post_x₀
  have hden_var_z_x₀ :
      ⟦(Term.var z).abstract Δx₀ hcov_var_z_x₀⟧ˢ = some x₀ := by
    rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some_inj]
    apply Option.get_of_eq_some
    simp [Δx₀]
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hden_z_x₀⟩ := post_x₀
  obtain ⟨_, _, _, _, _, _, _, htot_x₀⟩ := hden_z_x₀ x₀ hden_var_z_x₀
  exact (htot_x₀ Y hY_ty hφY).2 hdenY htrue

set_option maxHeartbeats 1500000 in
private theorem graphLambdaWitness
    {Γ : TypeContext} {«Δ» : RenamingContext.Context} {x z!_spec : Term}
    {x! z z! : 𝒱} {α β α' β' : SMTType} {pα : α ⇝ α'} {pβ : β ⇝ β'}
    (X : SMT.Dom)
    (hX_mem : X.fst ∈ ⟦α.fun β.option⟧ᶻ)
    (hX_func : IsFunc ⟦α⟧ᶻ ⟦β.option⟧ᶻ X.fst)
    (hcov_lambda_upd :
      ∀ Y : SMT.Dom,
        RenamingContext.CoversFV
          (Function.update «Δ» x! (some Y))
          ((λˢ [z!]) [α'.pair β']
            (.exists [z] [α.pair β]
              ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec))))
    (hgo_cov :
      ∀ Yfun : SMT.Dom,
        ∀ v ∈ SMT.fv
          (.exists [z] [α.pair β]
            ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)),
          v ∉ [z!] → (Function.update «Δ» x! (some Yfun) v).isSome = true)
    (hexists_cov :
      ∀ (Yfun W : SMT.Dom),
        RenamingContext.CoversFV
          (Function.update (Function.update «Δ» x! (some Yfun)) z! (some W))
          (.exists [z] [α.pair β]
            ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)))
    (hgo_exists :
      ∀ (Yfun : SMT.Dom)
        (w : Fin [z!].length → SMT.Dom)
        (hw : ∀ i, (w i).snd.fst = α'.pair β' ∧ (w i).fst ∈ ⟦α'.pair β'⟧ᶻ),
          (Term.abstract.go
              (Term.exists [z] [α.pair β]
                ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec))
              [z!]
              (Function.update «Δ» x! (some Yfun))
              (hgo_cov Yfun)).uncurry w =
            (Term.exists [z] [α.pair β]
              ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)).abstract
              (Function.update (Function.update «Δ» x! (some Yfun)) z! (some (w ⟨0, by simp⟩)))
              (hexists_cov Yfun (w ⟨0, by simp⟩)))
    (typ_exists :
      (AList.insert z! (α'.pair β') Γ) ⊢ˢ
        (.exists [z] [α.pair β]
          ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)) :
        SMTType.bool)
    (hbody_total :
      ∀ (Yfun : SMT.Dom)
        (x_1 : Fin [z!].length → SMT.Dom)
        (hx_1 : ∀ i, (x_1 i).snd.fst = α'.pair β' ∧ (x_1 i).fst ∈ ⟦α'.pair β'⟧ᶻ),
          ⟦(Term.abstract.go
              (Term.exists [z] [α.pair β]
                ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec))
              [z!]
              (Function.update «Δ» x! (some Yfun))
              (hgo_cov Yfun)).uncurry x_1⟧ˢ.isSome =
            true)
    (den_app_at :
      ∀ (Yfun wy0 x₀ : SMT.Dom)
        (hx₀_ty : x₀.snd.fst = α.pair β)
        (hx₀_mem : x₀.fst ∈ ⟦α.pair β⟧ᶻ),
        ∃ hcov_app_goal :
            RenamingContext.CoversFV
              (Function.update
                (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                z (some x₀))
              ((@ˢx) (.fst (.var z))),
          ⟦((@ˢx) (.fst (.var z))).abstract
              (Function.update
                (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                z (some x₀))
              hcov_app_goal⟧ˢ =
            some ⟨(@ᶻX.fst
                    ⟨x₀.fst.π₁, by
                      have hx₀_fst_mem : x₀.fst.π₁ ∈ ⟦α⟧ᶻ := by
                        have hx₀_mem' := hx₀_mem
                        rw [SMTType.toZFSet, ZFSet.mem_prod] at hx₀_mem'
                        rcases hx₀_mem' with ⟨X₁, hX₁, X₂, hX₂, hpair⟩
                        rw [hpair, ZFSet.π₁_pair]
                        exact hX₁
                      simpa [ZFSet.is_func_dom_eq hX_func] using hx₀_fst_mem⟩).1,
              β.option,
              (@ᶻX.fst
                ⟨x₀.fst.π₁, by
                  have hx₀_fst_mem : x₀.fst.π₁ ∈ ⟦α⟧ᶻ := by
                    have hx₀_mem' := hx₀_mem
                    rw [SMTType.toZFSet, ZFSet.mem_prod] at hx₀_mem'
                    rcases hx₀_mem' with ⟨X₁, hX₁, X₂, hX₂, hpair⟩
                    rw [hpair, ZFSet.π₁_pair]
                    exact hX₁
                  simpa [ZFSet.is_func_dom_eq hX_func] using hx₀_fst_mem⟩).2⟩)
    (den_spec_some_at :
      ∀ (Yfun wy0 x₀ : SMT.Dom)
        (hwy0_ty : wy0.snd.fst = α'.pair β')
        (hx₀_ty : x₀.snd.fst = α.pair β)
        (hx₀_mem : x₀.fst ∈ ⟦α.pair β⟧ᶻ),
        ∃ hφY :
            RenamingContext.CoversFV
              (Function.update
                (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                z (some x₀))
              z!_spec,
          ∃ Φ,
            ⟦z!_spec.abstract
                (Function.update
                  (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                  z (some x₀))
                hφY⟧ˢ =
              some Φ ∧
            Φ.snd.fst = SMTType.bool)
    (den_spec_true_at_cast :
      ∀ (y Yfun wy0 x₀ : SMT.Dom)
        (hwy0_ty : wy0.snd.fst = α'.pair β')
        (hwy0_val : wy0.fst = y.fst)
        (hx₀_ty : x₀.snd.fst = α.pair β)
        (hx₀_mem : x₀.fst ∈ ⟦α.pair β⟧ᶻ)
        (hcast_xy : x₀.fst.pair y.fst ∈ (castZF_of_path (pα.pair pβ)).1),
        ∃ hφY :
            RenamingContext.CoversFV
              (Function.update
                (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                z (some x₀))
              z!_spec,
          ∃ Φ,
            ⟦z!_spec.abstract
              (Function.update
                (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                z (some x₀))
              hφY⟧ˢ =
            some Φ ∧
          Φ.fst = zftrue)
    (den_spec_true_implies_cast :
      ∀ (Yfun wy0 x₀ : SMT.Dom)
        (hwy0_ty : wy0.snd.fst = α'.pair β')
        (hx₀_ty : x₀.snd.fst = α.pair β)
        (hx₀_mem : x₀.fst ∈ ⟦α.pair β⟧ᶻ)
        {Φ : SMT.Dom}
        (hφY :
          RenamingContext.CoversFV
            (Function.update
              (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
              z (some x₀))
            z!_spec)
        (hdenY :
          ⟦z!_spec.abstract
              (Function.update
                (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                z (some x₀))
              hφY⟧ˢ =
            some Φ)
        (htrue : Φ.fst = zftrue),
        x₀.fst.pair wy0.fst ∈ (castZF_of_path (pα.pair pβ)).1) :
    ∃ X! : SMT.Dom,
      X.fst.pair X!.fst ∈ (castZF_of_path (pα.graph pβ)).1 ∧
      ⟦((λˢ [z!]) [α'.pair β']
            (.exists [z] [α.pair β]
              ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec))).abstract
          (Function.update «Δ» x! (some X!)) (hcov_lambda_upd X!)⟧ˢ =
        some X! := by
  let castα : ZFSet := (castZF_of_path pα).1
  let castβ : ZFSet := (castZF_of_path pβ).1
  have hcastα : IsFunc ⟦α⟧ᶻ ⟦α'⟧ᶻ castα := (castZF_of_path pα).2
  have hcastβ : IsFunc ⟦β⟧ᶻ ⟦β'⟧ᶻ castβ := (castZF_of_path pβ).2
  let X!zf : ZFSet :=
    λᶻ: ⟦α'.pair β'⟧ᶻ → .𝔹
      | xy ↦ if hxy : xy ∈ ⟦α'.pair β'⟧ᶻ then
                let x := xy.π₁
                if x_cast : x ∈ castα.Range then
                  let x' := Classical.choose (ZFSet.mem_sep.mp x_cast).2
                  have hx' : x' ∈ ⟦α⟧ᶻ := by
                    have ⟨dom, _⟩ := Classical.choose_spec (ZFSet.mem_sep.mp x_cast).2
                    exact (ZFSet.mem_sep.mp dom).1
                  let y := xy.π₂
                  if y_cast : y ∈ castβ.Range then
                    let y' := Classical.choose (ZFSet.mem_sep.mp y_cast).2
                    have hy' : y' ∈ ⟦β⟧ᶻ := by
                      have ⟨dom, _⟩ := Classical.choose_spec (ZFSet.mem_sep.mp y_cast).2
                      exact (ZFSet.mem_sep.mp dom).1
                    ZFSet.ZFBool.ofBool <|
                      @ᶻX.fst
                        ⟨x', by
                          simpa [ZFSet.is_func_dom_eq hX_func] using hx'⟩ =
                        ZFSet.Option.some (S := ⟦β⟧ᶻ) ⟨y', hy'⟩
                  else
                    zffalse
                else
                  zffalse
              else
                ∅
  have hX!zf_mem : X!zf ∈ ⟦(α'.pair β').fun SMTType.bool⟧ᶻ := by
    rw [ZFSet.mem_funs]
    apply ZFSet.lambda_isFunc
    intro xy hxy
    rw [dite_cond_eq_true (eq_true hxy)]
    dsimp
    split_ifs with hx_range hy_range
    · apply ZFSet.ZFBool.mem_ofBool_𝔹
    · exact ZFSet.ZFBool.zffalse_mem_𝔹
    · exact ZFSet.ZFBool.zffalse_mem_𝔹
  let X! : SMT.Dom := ⟨X!zf, (α'.pair β').fun SMTType.bool, hX!zf_mem⟩
  have hden_lambda_X! :
      ⟦((λˢ [z!]) [α'.pair β']
            (.exists [z] [α.pair β]
              ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec))).abstract
          (Function.update «Δ» x! (some X!)) (hcov_lambda_upd X!)⟧ˢ =
        some X! := by
    have hbody_ty_of
        (Yfun : SMT.Dom)
        (x_1 : Fin [z!].length → SMT.Dom)
        (hx_1 : ∀ i, (x_1 i).snd.fst = [α'.pair β'][i] ∧ (x_1 i).fst ∈ ⟦[α'.pair β'][i]⟧ᶻ) :
        (⟦(Term.abstract.go
            (Term.exists [z] [α.pair β]
              ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec))
            [z!]
            (Function.update «Δ» x! (some Yfun))
            (hgo_cov Yfun)).uncurry x_1⟧ˢ.get
            (hbody_total Yfun x_1 (by
              intro i
              exact graphSpecificArg hx_1 i))).snd.fst =
          SMTType.bool := by
      exact graphBodyTyOf
        (hgo_cov := hgo_cov) (hexists_cov := hexists_cov) (hgo_exists := hgo_exists)
        (typ_exists := typ_exists) (hbody_total := hbody_total)
        Yfun x_1 (by
          intro i
          exact graphSpecificArg hx_1 i)
    rw [SMT.Term.abstract, dite_cond_eq_true (eq_true (by rfl)), SMT.denote]
    split_ifs with hlen_pos den_t_isSome den_t_typ_det
    · simp only [Option.pure_def, Option.some.injEq]
      have hbody_ty :
          (⟦(Term.abstract.go
              (Term.exists [z] [α.pair β]
                ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec))
              [z!]
              (Function.update «Δ» x! (some X!))
              (hgo_cov X!)).uncurry
              (fun i => ⟨[α'.pair β'][i].defaultZFSet, [α'.pair β'][i],
                SMTType.mem_toZFSet_of_defaultZFSet⟩)⟧ˢ.get
              (den_t_isSome (fun i => ⟨rfl, SMTType.mem_toZFSet_of_defaultZFSet⟩))).snd.fst =
            SMTType.bool := by
        let w0 : Fin [z!].length → SMT.Dom :=
          fun i => ⟨[α'.pair β'][i].defaultZFSet, [α'.pair β'][i],
            SMTType.mem_toZFSet_of_defaultZFSet⟩
        have hw0 : ∀ i, (w0 i).snd.fst = [α'.pair β'][i] ∧ (w0 i).fst ∈ ⟦[α'.pair β'][i]⟧ᶻ := by
          intro i
          exact ⟨rfl, SMTType.mem_toZFSet_of_defaultZFSet⟩
        obtain ⟨D0, hden_body⟩ := Option.isSome_iff_exists.mp (den_t_isSome hw0)
        have hget_eq_body :
            (⟦(Term.abstract.go
                (Term.exists [z] [α.pair β]
                  ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec))
                [z!]
                (Function.update «Δ» x! (some X!))
                (hgo_cov X!)).uncurry w0⟧ˢ.get
            (hbody_total X! w0 (by
                intro i
                exact graphSpecificArg hw0 i))) = D0 := by
          apply Option.get_of_eq_some
          exact hden_body
        have hget_eq :
            (⟦(Term.abstract.go
                (Term.exists [z] [α.pair β]
                  ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec))
                [z!]
                (Function.update «Δ» x! (some X!))
                (hgo_cov X!)).uncurry w0⟧ˢ.get
              (den_t_isSome hw0)) =
              (⟦(Term.abstract.go
                  (Term.exists [z] [α.pair β]
                    ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec))
                  [z!]
                  (Function.update «Δ» x! (some X!))
                  (hgo_cov X!)).uncurry w0⟧ˢ.get
                (hbody_total X! w0 (by
                  intro i
                  exact graphSpecificArg hw0 i))) := by
          apply Eq.trans
          · apply Option.get_of_eq_some
            exact hden_body
          · symm
            apply Option.get_of_eq_some
            exact hden_body
        rw [hget_eq]
        exact hbody_ty_of X! w0 hw0
      let bodyL : ZFSet → ZFSet := fun y =>
        if hy : y.hasArity 1 ∧ ∀ i : Fin 1, y ∈ ⟦[α'.pair β'][i]⟧ᶻ then
          (⟦(Term.abstract.go
              (Term.exists [z] [α.pair β]
                ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec))
              [z!]
              (Function.update «Δ» x! (some X!))
              (hgo_cov X!)).uncurry
              (fun i => ⟨y, [α'.pair β'][i], hy.2 i⟩)⟧ˢ.get
            (den_t_isSome (fun i => ⟨rfl, hy.2 i⟩))).fst
        else
          (⟦(Term.abstract.go
              (Term.exists [z] [α.pair β]
                ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec))
              [z!]
              (Function.update «Δ» x! (some X!))
              (hgo_cov X!)).uncurry
              (fun i => ⟨[α'.pair β'][i].defaultZFSet, [α'.pair β'][i],
                SMTType.mem_toZFSet_of_defaultZFSet⟩)⟧ˢ.get
            (den_t_isSome (fun i => ⟨rfl, SMTType.mem_toZFSet_of_defaultZFSet⟩))).snd.fst.defaultZFSet
      let bodyR : ZFSet → ZFSet := fun y =>
        if hx_range : y.π₁ ∈ castα.Range then
          let x' := Classical.choose (ZFSet.mem_sep.mp hx_range).2
          have hx' : x' ∈ ⟦α⟧ᶻ := by
            have ⟨dom, _⟩ := Classical.choose_spec (ZFSet.mem_sep.mp hx_range).2
            exact (ZFSet.mem_sep.mp dom).1
          if hy_range : y.π₂ ∈ castβ.Range then
            let y' := Classical.choose (ZFSet.mem_sep.mp hy_range).2
            have hy' : y' ∈ ⟦β⟧ᶻ := by
              have ⟨dom, _⟩ := Classical.choose_spec (ZFSet.mem_sep.mp hy_range).2
              exact (ZFSet.mem_sep.mp dom).1
            ZFSet.ZFBool.ofBool <|
              @ᶻX.fst
                ⟨x', by
                  simpa [ZFSet.is_func_dom_eq hX_func] using hx'⟩ =
                ZFSet.Option.some (S := ⟦β⟧ᶻ) ⟨y', hy'⟩
          else
            zffalse
        else
          zffalse
      have hX!zf_eq :
          (⟦α'.pair β'⟧ᶻ.lambda
            ⟦(⟦(Term.abstract.go
                (Term.exists [z] [α.pair β]
                  ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec))
                [z!]
                (Function.update «Δ» x! (some X!))
                (hgo_cov X!)).uncurry
                (fun i => ⟨[α'.pair β'][i].defaultZFSet, [α'.pair β'][i],
                  SMTType.mem_toZFSet_of_defaultZFSet⟩)⟧ˢ.get
              (den_t_isSome (fun i => ⟨rfl, SMTType.mem_toZFSet_of_defaultZFSet⟩))).snd.fst⟧ᶻ
            bodyL) = X!zf := by
        have hbodyR_mem : ∀ {y}, y ∈ ⟦α'.pair β'⟧ᶻ → bodyR y ∈ 𝔹 := by
          intro y hy
          dsimp [bodyR]
          split_ifs with hx_range hy_range
          · exact ZFSet.ZFBool.mem_ofBool_𝔹 _
          · exact ZFSet.ZFBool.zffalse_mem_𝔹
          · exact ZFSet.ZFBool.zffalse_mem_𝔹
        have hbodyR_eq :
            (⟦α'.pair β'⟧ᶻ.lambda 𝔹 bodyR) = X!zf := by
          unfold X!zf
          apply (ZFSet.lambda_ext_iff hbodyR_mem).2
          intro y hy
          simp [bodyR, hy]
        rw [hbody_ty]
        have hbodyL_mem : ∀ {y}, y ∈ ⟦α'.pair β'⟧ᶻ → bodyL y ∈ 𝔹 := by
          intro y hy
          have hy1 := graphUnaryTarget (τ := α'.pair β') hy
          let wy : Fin [z!].length → SMT.Dom := fun i => ⟨y, [α'.pair β'][i], hy1.2 i⟩
          let hwy :
              ∀ i : Fin [z!].length, (wy i).snd.fst = [α'.pair β'][i] ∧ (wy i).fst ∈ ⟦[α'.pair β'][i]⟧ᶻ :=
            fun i => ⟨rfl, hy1.2 i⟩
          have hbodyL_y :
              bodyL y =
                (⟦(Term.abstract.go
                    (Term.exists [z] [α.pair β]
                      ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec))
                    [z!]
                    (Function.update «Δ» x! (some X!))
                    (hgo_cov X!)).uncurry wy⟧ˢ.get
                  (den_t_isSome hwy)).fst := by
            dsimp [bodyL, wy, hwy]
            split_ifs with h
            · have hh : h = hy1 := Subsingleton.elim _ _
              cases hh
              rfl
            · exfalso
              exact h hy1
          rw [hbodyL_y]
          simpa [hbody_ty_of X! wy hwy] using
            ((⟦(Term.abstract.go
                (Term.exists [z] [α.pair β]
                  ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec))
                [z!]
                (Function.update «Δ» x! (some X!))
                (hgo_cov X!)).uncurry wy⟧ˢ.get
              (den_t_isSome hwy)).snd.snd)
        trans (⟦α'.pair β'⟧ᶻ.lambda 𝔹 bodyR)
        · apply (ZFSet.lambda_ext_iff hbodyL_mem).2
          intro y hy
          have hy1 := graphUnaryTarget (τ := α'.pair β') hy
          let wy : Fin [z!].length → SMT.Dom := fun i => ⟨y, [α'.pair β'][i], hy1.2 i⟩
          let hwy :
              ∀ i : Fin [z!].length, (wy i).snd.fst = [α'.pair β'][i] ∧ (wy i).fst ∈ ⟦[α'.pair β'][i]⟧ᶻ :=
            fun i => ⟨rfl, hy1.2 i⟩
          let wy0 : SMT.Dom := wy ⟨0, by simp⟩
          have hwy0_ty : wy0.snd.fst = α'.pair β' := by
            simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Fin.zero_eta, Fin.isValue,
              Fin.getElem_fin, Fin.val_eq_zero, List.getElem_cons_zero, wy0, wy]
          have hwy0_val : wy0.fst = y := by
            simp [wy0, wy]
          have hgo_body_cov :
              ∀ v ∈ SMT.fv
                ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec),
                v ∉ [z] →
                  (Function.update
                    (Function.update «Δ» x! (some X!))
                    z! (some wy0) v).isSome = true := by
            intro v hv hv_not_z
            have hv' : v ∈ SMT.fv
                (.exists [z] [α.pair β]
                  ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)) := by
              exact SMT.fv.mem_exists ⟨hv, hv_not_z⟩
            by_cases hvz! : v = z!
            · subst hvz!
              simp
            · rw [Function.update_of_ne hvz!]
              exact hgo_cov X! v hv' (by simpa [List.mem_singleton] using hvz!)
          have hbodyL_y :
              bodyL y =
                (⟦(Term.abstract.go
                    (Term.exists [z] [α.pair β]
                      ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec))
                    [z!]
                    (Function.update «Δ» x! (some X!))
                    (hgo_cov X!)).uncurry wy⟧ˢ.get
                  (den_t_isSome hwy)).fst := by
            dsimp [bodyL, wy, hwy]
            split_ifs with h
            · have hh : h = hy1 := Subsingleton.elim _ _
              cases hh
              rfl
            · exfalso
              exact h hy1
          rw [hbodyL_y]
          dsimp [bodyR]
          by_cases hx_range : y.π₁ ∈ castα.Range
          · simp [hx_range]
            by_cases hy_range : y.π₂ ∈ castβ.Range
            · have hy_range_sep :
                  y.π₂ ∈ ⟦β'⟧ᶻ ∧
                    ∃ x, (x ∈ ⟦β⟧ᶻ ∧ ∃ y' ∈ ⟦β'⟧ᶻ, x.pair y' ∈ castβ) ∧
                      x.pair y.π₂ ∈ castβ := by
                simpa [ZFSet.mem_sep] using hy_range
              simp [hy_range_sep]
              let x' := Classical.choose (ZFSet.mem_sep.mp hx_range).2
              have hx' : x' ∈ ⟦α⟧ᶻ := by
                have ⟨dom, _⟩ := Classical.choose_spec (ZFSet.mem_sep.mp hx_range).2
                exact (ZFSet.mem_sep.mp dom).1
              have hx'_dom : x' ∈ X.fst.Dom := by
                simpa [ZFSet.is_func_dom_eq hX_func] using hx'
              have hcast_x : x'.pair y.π₁ ∈ castα := by
                exact (Classical.choose_spec (ZFSet.mem_sep.mp hx_range).2).2
              let y' := Classical.choose (ZFSet.mem_sep.mp hy_range).2
              have hy' : y' ∈ ⟦β⟧ᶻ := by
                have ⟨dom, _⟩ := Classical.choose_spec (ZFSet.mem_sep.mp hy_range).2
                exact (ZFSet.mem_sep.mp dom).1
              have hcast_y : y'.pair y.π₂ ∈ castβ := by
                exact (Classical.choose_spec (ZFSet.mem_sep.mp hy_range).2).2
              let x₀ : SMT.Dom := ⟨x'.pair y', α.pair β, by
                rw [SMTType.toZFSet, ZFSet.pair_mem_prod]
                exact ⟨hx', hy'⟩⟩
              have hx₀_ty : x₀.snd.fst = α.pair β := by
                rfl
              have hx₀_mem : x₀.fst ∈ ⟦α.pair β⟧ᶻ := by
                dsimp [x₀]
                rw [SMTType.toZFSet, ZFSet.pair_mem_prod]
                exact ⟨hx', hy'⟩
              have hcast_xy :
                  x₀.fst.pair wy0.fst ∈ (castZF_of_path (pα.pair pβ)).1 := by
                have hcast_xy0 : x₀.fst.pair y ∈ (castZF_of_path (pα.pair pβ)).1 := by
                  dsimp [x₀]
                  rw [castZF_of_path, castZF_pair]
                  rw [ZFSet.pair_mem_fprod (hf := hcastα) (hg := hcastβ)]
                  refine ⟨x', y', hx', hy', rfl, ?_⟩
                  have hx_val :
                      (@ᶻcastα ⟨x', by rwa [ZFSet.is_func_dom_eq hcastα]⟩) = y.π₁ := by
                    have := ZFSet.fapply.of_pair
                      (hf := ZFSet.is_func_is_pfunc hcastα) hcast_x
                    simpa only [Subtype.ext_iff] using this
                  have hy_val :
                      (@ᶻcastβ ⟨y', by rwa [ZFSet.is_func_dom_eq hcastβ]⟩) = y.π₂ := by
                    have := ZFSet.fapply.of_pair
                      (hf := ZFSet.is_func_is_pfunc hcastβ) hcast_y
                    simpa only [Subtype.ext_iff] using this
                  rw [hx_val, hy_val]
                  exact ZFSet.pair_eta hy
                simpa [hwy0_val] using hcast_xy0
              by_cases hXeq :
                  @ᶻX.fst ⟨x', hx'_dom⟩ =
                    ZFSet.Option.some (S := ⟦β⟧ᶻ) ⟨y', hy'⟩
              · have hden_body_true :
                    ⟦(Term.abstract.go
                        (Term.exists [z] [α.pair β]
                          ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec))
                        [z!]
                        (Function.update «Δ» x! (some X!))
                        (hgo_cov X!)).uncurry wy⟧ˢ =
                      some ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
                  rw [hgo_exists X! wy (by
                    intro i
                    exact graphSpecificArg hwy i)]
                  rw [SMT.Term.abstract, dite_cond_eq_true (eq_true (by rfl)),
                    SMT.PHOAS.Term.exists, SMT.denote]
                  simp only [Option.bind_eq_bind, Option.pure_def]
                  have hlen_exists : [z].length > 0 := by
                    simp
                  rw [SMT.denote, dite_cond_eq_true (eq_true hlen_exists)]
                  split_ifs with den_exists_isSome
                  · simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
                      Nat.add_one_sub_one, List.getElem_cons_succ, Fin.zero_eta, Fin.isValue,
                      Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.getElem_cons_zero,
                      Fin.val_eq_zero, get.eq_1, forall_const, Option.pure_def, overloadUnaryOp,
                      id_eq, Option.failure_eq_none, Option.bind_some, Fin.foldl_zero]
                    obtain ⟨hcov_app_goal, hden_app⟩ :=
                      den_app_at X! wy0 x₀ hx₀_ty hx₀_mem
                    obtain ⟨hcov_some_goal, hden_some_snd⟩ :=
                      graphDenSomeSndAt («Δ» := «Δ») (x! := x!) (z := z) (z! := z!)
                        (Yfun := X!) (wy0 := wy0) (x₀ := x₀) hx₀_ty hx₀_mem
                    obtain ⟨DeqSome, hden_eqsome, hDeqSome_ty⟩ :=
                      denote_eq_some_of_some hden_app hden_some_snd rfl
                    obtain ⟨hφY, Dspec, hden_spec, hDspec_ty⟩ :=
                      den_spec_some_at X! wy0 x₀ hwy0_ty hx₀_ty hx₀_mem
                    obtain ⟨_, Φtrue, hden_spec_true, hΦtrue⟩ :=
                      den_spec_true_at_cast wy0 X! wy0 x₀ hwy0_ty rfl hx₀_ty hx₀_mem hcast_xy
                    have hDspec_true : Dspec.fst = zftrue := by
                      have hEq : Dspec = Φtrue := by
                        exact Option.some.inj (hden_spec.symm.trans hden_spec_true)
                      simpa [hEq] using hΦtrue
                    have hcov_eq_goal :
                        RenamingContext.CoversFV
                          (Function.update
                            (Function.update (Function.update «Δ» x! (some X!)) z! (some wy0))
                            z (some x₀))
                          ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z)))) := by
                      intro v hv
                      have hv' :
                          v ∈ SMT.fv (((@ˢx) (.fst (.var z)))) ∨
                            v ∈ SMT.fv (.some (.snd (.var z))) := by
                        simpa [fv] using hv
                      rcases hv' with hvapp | hvsome
                      · exact hcov_app_goal v (by simpa [fv] using hvapp)
                      · exact hcov_some_goal v (by simpa [fv] using hvsome)
                    have hDeqSome_true : DeqSome.fst = zftrue := by
                      have hden_eq_true_phoas :
                          ⟦(((@ˢx) (.fst (.var z))).abstract
                                (Function.update
                                  (Function.update (Function.update «Δ» x! (some X!)) z! (some wy0))
                                  z (some x₀))
                                hcov_app_goal) =ˢ'
                              (Term.some (Term.snd (.var z))).abstract
                                (Function.update
                                  (Function.update (Function.update «Δ» x! (some X!)) z! (some wy0))
                                  z (some x₀))
                                hcov_some_goal⟧ˢ =
                            some ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
                        exact denote_eq_eq_zftrue_of_fst_eq hden_app hden_some_snd rfl (by
                          simpa [x₀] using hXeq)
                      have hEq :
                          DeqSome = ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
                        exact Option.some.inj (hden_eqsome.symm.trans hden_eq_true_phoas)
                      simpa [hEq]
                    have hden_eq_true :
                        ⟦(((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))).abstract
                            (Function.update
                              (Function.update (Function.update «Δ» x! (some X!)) z! (some wy0))
                              z (some x₀))
                            hcov_eq_goal⟧ˢ =
                          some ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
                      simpa [SMT.Term.abstract, SMT.denote, Option.bind_eq_bind, Option.pure_def,
                        SMT.Term.abstract.go, Function.OfArity.uncurry, Function.FromTypes.uncurry,
                        proof_irrel_heq] using
                        (denote_eq_eq_zftrue_of_fst_eq hden_app hden_some_snd rfl (by
                          simpa [x₀] using hXeq))
                    have hcov_body_goal :
                        RenamingContext.CoversFV
                          (Function.update
                            (Function.update (Function.update «Δ» x! (some X!)) z! (some wy0))
                            z (some x₀))
                          ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec) := by
                      intro v hv
                      have hv' :
                          v ∈ SMT.fv ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z)))) ∨
                            v ∈ SMT.fv z!_spec := by
                        rw [fv] at hv
                        exact List.mem_append.mp hv
                      rcases hv' with hveq | hvspec
                      · exact hcov_eq_goal v hveq
                      · exact hφY v hvspec
                    have hden_and_true :
                        ⟦((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec).abstract
                            (Function.update
                              (Function.update (Function.update «Δ» x! (some X!)) z! (some wy0))
                              z (some x₀))
                            hcov_body_goal⟧ˢ =
                          some ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
                      rw [Term.abstract]
                      exact denote_and_eq_zftrue_of_some_zftrue
                        hden_eq_true rfl rfl hden_spec hDspec_ty hDspec_true
                    have hden_not_false :
                        ⟦¬ˢ'
                            ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec).abstract
                              (Function.update
                                (Function.update (Function.update «Δ» x! (some X!)) z! (some wy0))
                                z (some x₀))
                              hcov_body_goal⟧ˢ =
                          some ⟨zffalse, .bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
                      exact denote_not_eq_zffalse_of_some_zftrue hden_and_true rfl rfl
                    let w : Fin [z].length → SMT.Dom := fun _ => x₀
                    have hw :
                        ∀ i : Fin [z].length, (w i).snd.fst = [α.pair β][i] ∧
                          (w i).fst ∈ ⟦[α.pair β][i]⟧ᶻ := by
                      intro i
                      have hi0 : i = ⟨0, by simp⟩ := by
                        apply Fin.ext
                        simp
                      cases hi0
                      exact ⟨rfl, hx₀_mem⟩
                    have hget_not_false :
                        (⟦¬ˢ'
                            (Term.abstract.go
                                ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)
                                [z]
                                (Function.update
                                  (Function.update «Δ» x! (some X!))
                                  z! (some wy0))
                                hgo_body_cov).uncurry
                            w⟧ˢ.get
                          (den_exists_isSome hw)) =
                          ⟨zffalse, .bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
                      apply Option.get_of_eq_some
                      simpa [SMT.Term.abstract, SMT.denote, Option.bind_eq_bind,
                        Option.pure_def, SMT.Term.abstract.go, Function.OfArity.uncurry,
                        Function.FromTypes.uncurry, proof_irrel_heq, w] using hden_not_false
                    have hsInter_false :
                        (⋂₀
                          ZFSet.sep
                            (fun y =>
                              ∃ x_1 ∈ ⟦α.pair β⟧ᶻ,
                                y =
                                  if h : x_1.hasArity 1 ∧ x_1 ∈ ⟦α.pair β⟧ᶻ then
                                    let w : Fin [z].length → SMT.Dom := fun _ => ⟨x_1, α.pair β, h.2⟩
                                    (⟦¬ˢ'
                                          (Term.abstract.go
                                              ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)
                                              [z]
                                              (Function.update
                                                (Function.update «Δ» x! (some X!))
                                                z! (some (wy ⟨0, by simp⟩)))
                                              hgo_body_cov).uncurry
                                          w⟧ˢ.get
                                      (den_exists_isSome (graphSingletonArg h.2))).fst
                                  else zffalse)
                            𝔹 : ZFSet) = zffalse := by
                      simpa [graphNotBodySInter, wy0] using
                        graphNotBodySInterEqZffalseOfEqTrue
                          (pα := pα) (pβ := pβ) (X := X)
                          (X! := X!) (wy0 := wy0) (x₀ := x₀)
                          hX_func hwy0_ty hx₀_ty hx₀_mem
                          hgo_body_cov den_exists_isSome
                          den_app_at den_spec_some_at den_spec_true_at_cast
                          hcast_xy (by simpa [x₀] using hXeq)
                    apply congrArg some
                    apply graphDomEqOfTyEqAndFstEq rfl
                    rw [dif_pos (ZFSet.sInter_sep_subset_of_𝔹_mem_𝔹 (fun _ ↦ id))]
                    simpa using
                      congrArg (fun D : SMT.Dom => D.1) <|
                        graphBoolDomEqZftrueOfSInterEqZffalse hsInter_false
                  · exfalso
                    exact den_exists_isSome <|
                      graphInnerNotBodyAllIsSome
                        («Δ» := «Δ») (x := x) (z!_spec := z!_spec)
                        (x! := x!) (z := z) (z! := z!)
                        (α := α) (β := β) (α' := α') (β' := β')
                        (Yfun := X!) (wy0 := wy0)
                        (den_app_at := fun Yfun wy0 x₀ hx₀_ty hx₀_mem => by
                          obtain ⟨hcov_app_goal, hden_app⟩ := den_app_at Yfun wy0 x₀ hx₀_ty hx₀_mem
                          exact ⟨hcov_app_goal, _, rfl, hden_app⟩)
                        (den_spec_some_at := den_spec_some_at)
                        hwy0_ty hgo_body_cov
                have hget_body_true :
                    (⟦(Term.abstract.go
                        (Term.exists [z] [α.pair β]
                          ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec))
                        [z!]
                        (Function.update «Δ» x! (some X!))
                        (hgo_cov X!)).uncurry wy⟧ˢ.get
                      (den_t_isSome hwy)) =
                      ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
                  apply Option.get_of_eq_some
                  exact hden_body_true
                have hbodyR_true_choose :
                    (⟦(Term.abstract.go
                        (Term.exists [z] [α.pair β]
                          ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec))
                        [z!]
                        (Function.update «Δ» x! (some X!))
                        (hgo_cov X!)).uncurry wy⟧ˢ.get
                      (den_t_isSome hwy)).fst =
                      (↑(ZFSet.ZFBool.ofBool
                          (decide
                            (@ᶻX.fst ⟨x', hx'_dom⟩ =
                              ZFSet.Option.some (S := ⟦β⟧ᶻ) ⟨y', hy'⟩))) : ZFSet) := by
                  calc
                    (⟦(Term.abstract.go
                        (Term.exists [z] [α.pair β]
                          ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec))
                        [z!]
                        (Function.update «Δ» x! (some X!))
                        (hgo_cov X!)).uncurry wy⟧ˢ.get
                      (den_t_isSome hwy)).fst = zftrue := by
                        exact congrArg (fun D : SMT.Dom => D.1) hget_body_true
                    _ =
                        (↑(ZFSet.ZFBool.ofBool
                          (decide
                            (@ᶻX.fst ⟨x', hx'_dom⟩ =
                              ZFSet.Option.some (S := ⟦β⟧ᶻ) ⟨y', hy'⟩))) : ZFSet) := by
                        symm
                        exact graphBoolOfDecideTrue hXeq
                simpa [x', y', proof_irrel_heq] using hbodyR_true_choose
              · have hden_body_false :
                    ⟦(Term.abstract.go
                        (Term.exists [z] [α.pair β]
                          ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec))
                        [z!]
                        (Function.update «Δ» x! (some X!))
                        (hgo_cov X!)).uncurry wy⟧ˢ =
                      some ⟨zffalse, SMTType.bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
                  rw [hgo_exists X! wy (by
                    intro i
                    exact graphSpecificArg hwy i)]
                  rw [SMT.Term.abstract, dite_cond_eq_true (eq_true (by rfl)), SMT.PHOAS.Term.exists,
                    SMT.denote]
                  simp only [Option.bind_eq_bind, Option.pure_def]
                  have hlen_exists : [z].length > 0 := by
                    simp
                  rw [SMT.denote, dite_cond_eq_true (eq_true hlen_exists)]
                  split_ifs with den_exists_isSome
                  · simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
                      Nat.add_one_sub_one, List.getElem_cons_succ, Fin.zero_eta, Fin.isValue,
                      Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.getElem_cons_zero,
                      Fin.val_eq_zero, get.eq_1, forall_const, Option.pure_def, overloadUnaryOp,
                      id_eq, Option.failure_eq_none, Option.bind_some, Fin.foldl_zero]
                    have hsInter_true :
                        (⋂₀
                          ZFSet.sep
                            (fun y =>
                              ∃ x_1 ∈ ⟦α.pair β⟧ᶻ,
                                y =
                                  if h : x_1.hasArity 1 ∧ x_1 ∈ ⟦α.pair β⟧ᶻ then
                                    let w : Fin [z].length → SMT.Dom := fun _ => ⟨x_1, α.pair β, h.2⟩
                                    (⟦¬ˢ'
                                          (Term.abstract.go
                                              ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)
                                              [z]
                                              (Function.update
                                                (Function.update «Δ» x! (some X!))
                                                z! (some (wy ⟨0, by simp⟩)))
                                              hgo_body_cov).uncurry
                                          w⟧ˢ.get
                                      (den_exists_isSome (graphSingletonArg h.2))).fst
                                  else zffalse)
                            𝔹 : ZFSet) = zftrue := by
                      simpa [graphNotBodySInter, wy0] using
                        graphNotBodySInterEqZftrueOfEqFalse
                          (pα := pα) (pβ := pβ) (X := X)
                          (X! := X!) (wy0 := wy0) (x₀ := x₀)
                          hX_func hwy0_ty hx₀_ty hx₀_mem
                          hgo_body_cov den_exists_isSome
                          den_app_at den_spec_some_at den_spec_true_implies_cast
                          hcast_xy (by simpa [x₀] using hXeq)
                    apply congrArg some
                    apply graphDomEqOfTyEqAndFstEq rfl
                    rw [dif_pos (ZFSet.sInter_sep_subset_of_𝔹_mem_𝔹 (fun _ ↦ id))]
                    simpa using
                      congrArg (fun D : SMT.Dom => D.1) <|
                        graphBoolDomEqZffalseOfSInterEqZftrue hsInter_true
                  · exfalso
                    exact den_exists_isSome <|
                      graphInnerNotBodyAllIsSome
                        («Δ» := «Δ») (x := x) (z!_spec := z!_spec)
                        (x! := x!) (z := z) (z! := z!)
                        (α := α) (β := β) (α' := α') (β' := β')
                        (Yfun := X!) (wy0 := wy0)
                        (den_app_at := fun Yfun wy0 x₀ hx₀_ty hx₀_mem => by
                          obtain ⟨hcov_app_goal, hden_app⟩ := den_app_at Yfun wy0 x₀ hx₀_ty hx₀_mem
                          exact ⟨hcov_app_goal, _, rfl, hden_app⟩)
                        (den_spec_some_at := den_spec_some_at)
                        hwy0_ty hgo_body_cov
                have hget_body_false :
                    (⟦(Term.abstract.go
                        (Term.exists [z] [α.pair β]
                          ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec))
                        [z!]
                        (Function.update «Δ» x! (some X!))
                        (hgo_cov X!)).uncurry wy⟧ˢ.get
                      (den_t_isSome hwy)) =
                      ⟨zffalse, SMTType.bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
                  apply Option.get_of_eq_some
                  exact hden_body_false
                have hbodyR_false_choose :
                    (⟦(Term.abstract.go
                        (Term.exists [z] [α.pair β]
                          ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec))
                        [z!]
                        (Function.update «Δ» x! (some X!))
                        (hgo_cov X!)).uncurry wy⟧ˢ.get
                      (den_t_isSome hwy)).fst =
                      (↑(ZFSet.ZFBool.ofBool
                          (decide
                            (@ᶻX.fst ⟨x', hx'_dom⟩ =
                              ZFSet.Option.some (S := ⟦β⟧ᶻ) ⟨y', hy'⟩))) : ZFSet) := by
                  calc
                    (⟦(Term.abstract.go
                        (Term.exists [z] [α.pair β]
                          ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec))
                        [z!]
                        (Function.update «Δ» x! (some X!))
                        (hgo_cov X!)).uncurry wy⟧ˢ.get
                      (den_t_isSome hwy)).fst = zffalse := by
                        exact congrArg (fun D : SMT.Dom => D.1) hget_body_false
                    _ =
                        (↑(ZFSet.ZFBool.ofBool
                          (decide
                            (@ᶻX.fst ⟨x', hx'_dom⟩ =
                              ZFSet.Option.some (S := ⟦β⟧ᶻ) ⟨y', hy'⟩))) : ZFSet) := by
                        symm
                        exact graphBoolOfDecideFalse hXeq
                simpa [x', y', proof_irrel_heq] using hbodyR_false_choose
            · have hy_range_sep :
                  ¬ (y.π₂ ∈ ⟦β'⟧ᶻ ∧
                      ∃ x, (x ∈ ⟦β⟧ᶻ ∧ ∃ y' ∈ ⟦β'⟧ᶻ, x.pair y' ∈ castβ) ∧
                        x.pair y.π₂ ∈ castβ) :=
                graphSndRangeSepNotOfNotRange hcastβ hy_range
              have hden_body_false :
                  ⟦(Term.abstract.go
                      (Term.exists [z] [α.pair β]
                        ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec))
                      [z!]
                      (Function.update «Δ» x! (some X!))
                      (hgo_cov X!)).uncurry wy⟧ˢ =
                    some ⟨zffalse, SMTType.bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
                rw [hgo_exists X! wy (by
                  intro i
                  exact graphSpecificArg hwy i)]
                rw [SMT.Term.abstract, dite_cond_eq_true (eq_true (by rfl)), SMT.PHOAS.Term.exists,
                  SMT.denote]
                simp only [Option.bind_eq_bind, Option.pure_def]
                have hlen_exists : [z].length > 0 := by
                  simp
                rw [SMT.denote, dite_cond_eq_true (eq_true hlen_exists)]
                split_ifs with den_exists_isSome
                · simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
                    Nat.add_one_sub_one, List.getElem_cons_succ, Fin.zero_eta, Fin.isValue,
                    Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.getElem_cons_zero,
                    Fin.val_eq_zero, get.eq_1, forall_const, Option.pure_def, overloadUnaryOp,
                    id_eq, Option.failure_eq_none, Option.bind_some, Fin.foldl_zero]
                  have hy_range' :
                      wy0.fst.π₂ ∉
                        (castZF_of_path pβ).1.Range
                          (A := ⟦β⟧ᶻ) (B := ⟦β'⟧ᶻ)
                          (hf := ZFSet.is_rel_of_is_pfunc
                            (ZFSet.is_func_is_pfunc (castZF_of_path pβ).2)) := by
                    simpa [castβ, hwy0_val] using hy_range
                  have hsInter_true :=
                    graphHsInterTrueOfNoCast
                      (pα := pα) (pβ := pβ) (X! := X!) (wy0 := wy0)
                      hwy0_ty hgo_body_cov den_exists_isSome
                      (den_app_at := fun wy0 x₀ hx₀_ty hx₀_mem => by
                        obtain ⟨hcov_app_goal, hden_app⟩ :=
                          den_app_at X! wy0 x₀ hx₀_ty hx₀_mem
                        exact ⟨hcov_app_goal, _, rfl, hden_app⟩)
                      (den_spec_some_at := fun wy0 x₀ hwy0_ty hx₀_ty hx₀_mem =>
                        den_spec_some_at X! wy0 x₀ hwy0_ty hx₀_ty hx₀_mem)
                      (den_spec_true_implies_cast := fun wy0 x₀ hwy0_ty hx₀_ty hx₀_mem
                        {Φ} hφY hdenY htrue =>
                          den_spec_true_implies_cast X! wy0 x₀ hwy0_ty hx₀_ty hx₀_mem
                            hφY hdenY htrue)
                      (by
                        intro x_1 hx_1 hcast_xy
                        exact hy_range' <|
                          graphPairCastSndInRange (pα := pα) (pβ := pβ) hcast_xy)
                  apply congrArg some
                  apply graphDomEqOfTyEqAndFstEq rfl
                  rw [dif_pos (ZFSet.sInter_sep_subset_of_𝔹_mem_𝔹 (fun _ ↦ id))]
                  simpa using
                    congrArg (fun D : SMT.Dom => D.1) <|
                      graphBoolDomEqZffalseOfSInterEqZftrue hsInter_true
                · exfalso
                  exact den_exists_isSome <|
                    graphInnerNotBodyAllIsSome
                      («Δ» := «Δ») (x := x) (z!_spec := z!_spec)
                      (x! := x!) (z := z) (z! := z!)
                      (α := α) (β := β) (α' := α') (β' := β')
                      (Yfun := X!) (wy0 := wy0)
                      (den_app_at := fun Yfun wy0 x₀ hx₀_ty hx₀_mem => by
                        obtain ⟨hcov_app_goal, hden_app⟩ := den_app_at Yfun wy0 x₀ hx₀_ty hx₀_mem
                        exact ⟨hcov_app_goal, _, rfl, hden_app⟩)
                      (den_spec_some_at := den_spec_some_at)
                      hwy0_ty hgo_body_cov
              have hget_body_false :
                  (⟦(Term.abstract.go
                      (Term.exists [z] [α.pair β]
                        ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec))
                      [z!]
                      (Function.update «Δ» x! (some X!))
                      (hgo_cov X!)).uncurry wy⟧ˢ.get
                    (den_t_isSome hwy)) =
                    ⟨zffalse, SMTType.bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
                apply Option.get_of_eq_some
                exact hden_body_false
              calc
                (⟦(Term.abstract.go
                    (Term.exists [z] [α.pair β]
                      ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec))
                    [z!]
                    (Function.update «Δ» x! (some X!))
                    (hgo_cov X!)).uncurry wy⟧ˢ.get
                  (den_t_isSome hwy)).fst = zffalse := by
                    exact congrArg (fun D => D.1) hget_body_false
                _ = _ := by
                    simp [hy_range_sep]
          · have hx_range_sep :
                ¬ (y.π₁ ∈ ⟦α'⟧ᶻ ∧
                    ∃ x, (x ∈ ⟦α⟧ᶻ ∧ ∃ y' ∈ ⟦α'⟧ᶻ, x.pair y' ∈ castα) ∧
                      x.pair y.π₁ ∈ castα) :=
              graphFstRangeSepNotOfNotRange hcastα hx_range
            have hbodyR_false : bodyR y = zffalse := by
              dsimp [bodyR]
              by_cases h : y.π₁ ∈ castα.Range
              · exact (hx_range h).elim
              · simp [h]
            have hden_body_false :
                ⟦(Term.abstract.go
                    (Term.exists [z] [α.pair β]
                      ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec))
                    [z!]
                    (Function.update «Δ» x! (some X!))
                    (hgo_cov X!)).uncurry wy⟧ˢ =
                  some ⟨zffalse, SMTType.bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
              rw [hgo_exists X! wy (by
                intro i
                exact graphSpecificArg hwy i)]
              rw [SMT.Term.abstract, dite_cond_eq_true (eq_true (by rfl)), SMT.PHOAS.Term.exists,
                SMT.denote]
              simp only [Option.bind_eq_bind, Option.pure_def]
              have hlen_exists : [z].length > 0 := by
                simp
              rw [SMT.denote, dite_cond_eq_true (eq_true hlen_exists)]
              split_ifs with den_exists_isSome
              · simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
                  Nat.add_one_sub_one, List.getElem_cons_succ, Fin.zero_eta, Fin.isValue,
                  Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.getElem_cons_zero,
                  Fin.val_eq_zero, get.eq_1, forall_const, Option.pure_def, overloadUnaryOp,
                  id_eq, Option.failure_eq_none, Option.bind_some, Fin.foldl_zero]
                have hx_range' :
                    wy0.fst.π₁ ∉
                      (castZF_of_path pα).1.Range
                        (A := ⟦α⟧ᶻ) (B := ⟦α'⟧ᶻ)
                        (hf := ZFSet.is_rel_of_is_pfunc
                          (ZFSet.is_func_is_pfunc (castZF_of_path pα).2)) := by
                  simpa [castα, hwy0_val] using hx_range
                have hsInter_true :=
                  graphHsInterTrueOfNoCast
                    (pα := pα) (pβ := pβ) (X! := X!) (wy0 := wy0)
                    hwy0_ty hgo_body_cov den_exists_isSome
                    (den_app_at := fun wy0 x₀ hx₀_ty hx₀_mem => by
                      obtain ⟨hcov_app_goal, hden_app⟩ :=
                        den_app_at X! wy0 x₀ hx₀_ty hx₀_mem
                      exact ⟨hcov_app_goal, _, rfl, hden_app⟩)
                    (den_spec_some_at := fun wy0 x₀ hwy0_ty hx₀_ty hx₀_mem =>
                      den_spec_some_at X! wy0 x₀ hwy0_ty hx₀_ty hx₀_mem)
                    (den_spec_true_implies_cast := fun wy0 x₀ hwy0_ty hx₀_ty hx₀_mem
                      {Φ} hφY hdenY htrue =>
                        den_spec_true_implies_cast X! wy0 x₀ hwy0_ty hx₀_ty hx₀_mem
                          hφY hdenY htrue)
                    (by
                      intro x_1 hx_1 hcast_xy
                      exact hx_range' <|
                        graphPairCastFstInRange (pα := pα) (pβ := pβ) hcast_xy)
                apply congrArg some
                apply graphDomEqOfTyEqAndFstEq rfl
                rw [dif_pos (ZFSet.sInter_sep_subset_of_𝔹_mem_𝔹 (fun _ ↦ id))]
                simpa using
                  congrArg (fun D : SMT.Dom => D.1) <|
                    graphBoolDomEqZffalseOfSInterEqZftrue hsInter_true
              · exfalso
                exact den_exists_isSome <|
                  graphInnerNotBodyAllIsSome
                    («Δ» := «Δ») (x := x) (z!_spec := z!_spec)
                    (x! := x!) (z := z) (z! := z!)
                    (α := α) (β := β) (α' := α') (β' := β')
                    (Yfun := X!) (wy0 := wy0)
                    (den_app_at := fun Yfun wy0 x₀ hx₀_ty hx₀_mem => by
                      obtain ⟨hcov_app_goal, hden_app⟩ := den_app_at Yfun wy0 x₀ hx₀_ty hx₀_mem
                      exact ⟨hcov_app_goal, _, rfl, hden_app⟩)
                    (den_spec_some_at := den_spec_some_at)
                    hwy0_ty hgo_body_cov
            have hget_body_false :
                (⟦(Term.abstract.go
                    (Term.exists [z] [α.pair β]
                      ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec))
                    [z!]
                    (Function.update «Δ» x! (some X!))
                    (hgo_cov X!)).uncurry wy⟧ˢ.get
                  (den_t_isSome hwy)) =
                  ⟨zffalse, SMTType.bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
              apply Option.get_of_eq_some
              exact hden_body_false
            change (⟦(Term.abstract.go
                (Term.exists [z] [α.pair β]
                  ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec))
                [z!]
                (Function.update «Δ» x! (some X!))
                (hgo_cov X!)).uncurry wy⟧ˢ.get
              (den_t_isSome hwy)).fst = bodyR y
            calc
              (⟦(Term.abstract.go
                    (Term.exists [z] [α.pair β]
                      ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec))
                    [z!]
                    (Function.update «Δ» x! (some X!))
                    (hgo_cov X!)).uncurry wy⟧ˢ.get
                  (den_t_isSome hwy)).fst = zffalse := by
                exact congrArg (fun D => D.1) hget_body_false
              _ = bodyR y := by
                symm
                exact hbodyR_false
        · exact hbodyR_eq
      simp only [List.getElem_singleton, Fin.foldr_zero]
      have hfun_ty :=
        congrArg (fun τ => (α'.pair β').fun τ) hbody_ty
      exact graphDomEqOfTyEqAndFstEq hfun_ty hX!zf_eq
    · exfalso
      apply den_t_typ_det
      intro x_1 y_1 hx_1 hy_1
      rw [hbody_ty_of X! x_1 hx_1, hbody_ty_of X! y_1 hy_1]
    · exfalso
      exact den_t_isSome (fun {x_1} hx_1 => hbody_total X! x_1 (by
        intro i
        exact graphSpecificArg hx_1 i))
    · exfalso
      exact hlen_pos (by simp)
  refine ⟨X!, ?_, hden_lambda_X!⟩
  rw [castZF_of_path, castZF_graph, ZFSet.lambda_spec]
  refine ⟨hX_mem, hX!zf_mem, ?_⟩
  rw [dif_pos hX_func]

private theorem graphLambdaWitnessAt.{u}
    {Γ : TypeContext} {«Δ» : RenamingContext.Context.{u}} {x z!_spec : Term}
    {x! z z! : 𝒱} {α β α' β' : SMTType} {pα : α ⇝ α'} {pβ : β ⇝ β'}
    (pα_ih : GraphOuterIH.{u} pα)
    (pβ_ih : GraphOuterIH.{u} pβ)
    {St₁ St₂ St₃ St₄ : EncoderState} {name : String}
    (sub : AList.keys St₁.types ⊆ St₁.env.usedVars)
    (St₂_types_eq :
      St₂.types = AList.insert x! ((α'.pair β').fun SMTType.bool) St₁.types)
    (St₂_used_eq :
      St₂.env.usedVars = x! :: St₁.env.usedVars)
    (St₃_types_eq :
      St₃.types = AList.insert z (α.pair β) St₂.types)
    (St₃_used_eq :
      St₃.env.usedVars = z :: St₂.env.usedVars)
    (typ_var_z_St₃ : St₃.types ⊢ˢ .var z : α.pair β)
    (hrun :
      Id.run ((loosenAux_prf s!"{name}_funGraph_pair" (pα.pair pβ) (.var z)) St₃) =
        Except.ok ((z!, z!_spec), St₄))
    (typing_pack : GraphTypingPack St₂.types x x! z z! α β α' β' z!_spec)
    (typ_z!_St₄ : St₄.types ⊢ˢ Term.var z! : α'.pair β')
    (X : SMT.Dom)
    (hX_ty : X.snd.fst = α.fun β.option)
    (hX_mem : X.fst ∈ ⟦α.fun β.option⟧ᶻ)
    (hX_func : IsFunc ⟦α⟧ᶻ ⟦β.option⟧ᶻ X.fst)
    (hcov_lambda_upd :
      ∀ Y : SMT.Dom,
        RenamingContext.CoversFV
          (Function.update «Δ» x! (some Y))
          ((λˢ [z!]) [α'.pair β']
            (.exists [z] [α.pair β]
              ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec))))
    (hgo_cov :
      ∀ Yfun : SMT.Dom,
        ∀ v ∈ SMT.fv
          (.exists [z] [α.pair β]
            ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)),
          v ∉ [z!] → (Function.update «Δ» x! (some Yfun) v).isSome = true)
    (hexists_cov :
      ∀ (Yfun W : SMT.Dom),
        RenamingContext.CoversFV
          (Function.update (Function.update «Δ» x! (some Yfun)) z! (some W))
          (.exists [z] [α.pair β]
            ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)))
    (hgo_exists :
      ∀ (Yfun : SMT.Dom)
        (w : Fin [z!].length → SMT.Dom)
        (hw : ∀ i, (w i).snd.fst = α'.pair β' ∧ (w i).fst ∈ ⟦α'.pair β'⟧ᶻ),
          (Term.abstract.go
              (Term.exists [z] [α.pair β]
                ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec))
              [z!]
              (Function.update «Δ» x! (some Yfun))
              (hgo_cov Yfun)).uncurry w =
            (Term.exists [z] [α.pair β]
              ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)).abstract
              (Function.update (Function.update «Δ» x! (some Yfun)) z! (some (w ⟨0, by simp⟩)))
              (hexists_cov Yfun (w ⟨0, by simp⟩)))
    (hcov_x_upd :
      ∀ Y : SMT.Dom, RenamingContext.CoversFV (Function.update «Δ» x! (some Y)) x)
    (denx_upd :
      ∀ Y : SMT.Dom,
        ⟦x.abstract (Function.update «Δ» x! (some Y)) (hcov_x_upd Y)⟧ˢ = some X)
    (fv_z!_spec : SMT.fv z!_spec ⊆ SMT.fv (.var z) ∪ {z!})
    (z_ne_z! : z ≠ z!)
    (x_ne_z : x! ≠ z)
    (x_ne_z! : x! ≠ z!)
    (z_not_mem_fv_x : z ∉ SMT.fv x)
    (z!_not_mem_fv_x : z! ∉ SMT.fv x) :
    ∃ X! : SMT.Dom,
      X.fst.pair X!.fst ∈ (castZF_of_path (pα.graph pβ)).1 ∧
      ⟦((λˢ [z!]) [α'.pair β']
            (.exists [z] [α.pair β]
              ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec))).abstract
          (Function.update «Δ» x! (some X!)) (hcov_lambda_upd X!)⟧ˢ =
        some X! := by
  have den_z_at := graphDenZAt
    («Δ» := «Δ») (pα_ih := pα_ih) (pβ_ih := pβ_ih)
    sub St₂_types_eq St₂_used_eq St₃_types_eq St₃_used_eq typ_var_z_St₃ hrun
  have den_z_exact_at := graphDenZExactAt
    («Δ» := «Δ») (pα := pα) (pβ := pβ)
    sub St₂_types_eq St₂_used_eq St₃_types_eq St₃_used_eq typ_var_z_St₃ hrun
  exact graphLambdaWitness
    (Γ := St₂.types) («Δ» := «Δ») (x := x) (z!_spec := z!_spec)
    (x! := x!) (z := z) (z! := z!)
    (α := α) (β := β) (α' := α') (β' := β')
    (pα := pα) (pβ := pβ)
    X hX_mem hX_func
    hcov_lambda_upd hgo_cov hexists_cov hgo_exists typing_pack.typ_exists
    (graphBodyTotal
      (Γ := St₂.types) («Δ» := «Δ») (x := x) (z!_spec := z!_spec)
      (x! := x!) (z := z) (z! := z!)
      (α := α) (β := β) (α' := α') (β' := β')
      (X := X) (pα := pα) (pβ := pβ)
      (hgo_cov := hgo_cov) (hexists_cov := hexists_cov) (hgo_exists := hgo_exists)
      (hcov_x_upd := hcov_x_upd) (denx_upd := denx_upd)
      (hX_ty := hX_ty) (hX_func := hX_func)
      (den_z_at := den_z_at) (fv_z!_spec := fv_z!_spec)
      (z_ne_z! := z_ne_z!) (x_ne_z := x_ne_z) (x_ne_z! := x_ne_z!)
      (z_not_mem_fv_x := z_not_mem_fv_x)
      (z!_not_mem_fv_x := z!_not_mem_fv_x)
      (typ_eq_some_body := typing_pack.typ_eq_some_body)
      (typ_z!_spec_body := typing_pack.typ_z!_spec_body))
    (fun Yfun wy0 x₀ hx₀_ty hx₀_mem =>
      graphDenAppAt
        (hcov_x_upd := hcov_x_upd) (denx_upd := denx_upd)
        (hX_ty := hX_ty) (hX_func := hX_func)
        (z!_not_mem_fv_x := z!_not_mem_fv_x)
        (z_not_mem_fv_x := z_not_mem_fv_x)
        (Yfun := Yfun) (wy0 := wy0)
        x₀ hx₀_ty hx₀_mem)
    (fun Yfun wy0 x₀ hwy0_ty hx₀_ty hx₀_mem =>
      graphDenSpecSomeAt
        (Γ := St₂.types) («Δ» := «Δ») (z!_spec := z!_spec)
        (x! := x!) (z := z) (z! := z!)
        (p := pα.pair pβ)
        (den_z_at := den_z_at) (fv_z!_spec := fv_z!_spec)
        (z_ne_z! := z_ne_z!) (x_ne_z := x_ne_z) (x_ne_z! := x_ne_z!)
        (typ_z!_spec_body := typing_pack.typ_z!_spec_body)
        (Yfun := Yfun) (wy0 := wy0)
        hwy0_ty x₀ hx₀_ty hx₀_mem)
    (fun y Yfun wy0 x₀ hwy0_ty hwy0_val hx₀_ty hx₀_mem hcast_xy =>
      graphDenSpecTrueAtCast
        (Γ := St₄.types) («Δ» := «Δ») (z!_spec := z!_spec)
        (x! := x!) (z := z) (z! := z!)
        (p := pα.pair pβ)
        (cast := (castZF_of_path (pα.pair pβ)).1) (y := y.fst)
        (den_z_at := den_z_at) (fv_z!_spec := fv_z!_spec)
        (z_ne_z! := z_ne_z!) (x_ne_z := x_ne_z) (x_ne_z! := x_ne_z!)
        (typ_z! := typ_z!_St₄)
        (hcast := (castZF_of_path (pα.pair pβ)).2)
        (Yfun := Yfun) (wy0 := wy0)
        hwy0_ty hwy0_val x₀ hx₀_ty hx₀_mem hcast_xy)
    (fun Yfun wy0 x₀ hwy0_ty hx₀_ty hx₀_mem {Φ} hφY hdenY htrue =>
      graphDenSpecTrueImpliesCast
        (Γ := St₄.types) («Δ» := «Δ») (z!_spec := z!_spec)
        (x! := x!) (z := z) (z! := z!)
        (p := pα.pair pβ)
        (den_z_exact_at := den_z_exact_at)
        (fv_z!_spec := fv_z!_spec)
        (z_ne_z! := z_ne_z!) (x_ne_z := x_ne_z) (x_ne_z! := x_ne_z!)
        x₀ hwy0_ty hx₀_ty hx₀_mem hφY hdenY htrue)

set_option maxHeartbeats 400000
theorem loosenAux_prf_spec.graph.{uGraphSpecProof} («Δ» : RenamingContext.Context.{uGraphSpecProof})
  (pf : ∀ (x! : 𝒱) (X! : SMT.Dom), ∀ v ∈ fv (Term.var x!), (Function.update «Δ» x! (some X!) v).isSome = true)
  {α β α' β' : SMTType} (pα : α ⇝ α') (pβ : β ⇝ β')
  (pα_ih :
    ∀ {Λ : TypeContext} {n : ℕ} {used : List 𝒱} {name : String} {x : Term},
      Λ ⊢ˢ x : α →
        ∀ («Δ₀» : RenamingContext.Context.{uGraphSpecProof}) (hx : RenamingContext.CoversFV «Δ₀» x)
          (pf₀ : ∀ (x! : 𝒱) (X! : SMT.Dom), ∀ v ∈ fv (Term.var x!), (Function.update «Δ₀» x! (some X!) v).isSome = true),
          ⦃fun x =>
            match x with
            | { env := E, types := Λ' } => ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ AList.keys Λ' ⊆ E.usedVars ∧ E.usedVars = used⌝⦄
            loosenAux_prf name pα x ⦃PostCond.mayThrow fun x_1 x_2 =>
              match x_1 with
              | (x!, x!_spec) =>
                match x_2 with
                | { env := E', types := Γ' } =>
                  ⌜n ≤ E'.freshvarsc ∧
                      AList.insert x! α' Λ ⊆ Γ' ∧
                        x! ∉ Λ ∧
                          x! ∉ used ∧
                            used ⊆ E'.usedVars ∧
                              AList.keys Γ' ⊆ E'.usedVars ∧
                                (∀ v ∈ used, v ∉ Λ → v ∉ Γ') ∧
                                AList.insert x! α' Λ ⊢ˢ Term.var x! : α' ∧
                                  AList.insert x! α' Λ ⊢ˢ x!_spec : SMTType.bool ∧
                                    Γ' ⊢ˢ Term.var x! : α' ∧
                                      Γ' ⊢ˢ x!_spec : SMTType.bool ∧
                                        fv x!_spec ⊆ fv x ∪ {x!} ∧
                                          ∀ (X : SMT.Dom),
                                            ⟦x.abstract «Δ₀» hx⟧ˢ = some X →
                                              ∃ Φ X!,
                                                ∃ (_ :
                                                  ⟦(Term.var x!).abstract (Function.update «Δ₀» x! (some X!)) (pf₀ x! X!)⟧ˢ =
                                                    some X!)
                                                  (hφ :
                                                  RenamingContext.CoversFV (Function.update «Δ₀» x! (some X!)) x!_spec)
                                                  (_ :
                                                  ⟦x!_spec.abstract (Function.update «Δ₀» x! (some X!)) hφ⟧ˢ = some Φ),
                                                  Φ.snd.fst = SMTType.bool ∧
                                                    (Φ.fst = zftrue ∧ X.fst.pair X!.fst ∈ (castZF_of_path pα).1) ∧
                                                      ∀ (Y : SMT.Dom),
                                                        Y.snd.fst = α' →
                                                          ∀
                                                            (hφY :
                                                              RenamingContext.CoversFV (Function.update «Δ₀» x! (some Y))
                                                                x!_spec),
                                                            ⟦x!_spec.abstract (Function.update «Δ₀» x! (some Y))
                                                                    hφY⟧ˢ.isSome =
                                                              true⌝⦄)
  (pβ_ih :
    ∀ {Λ : TypeContext} {n : ℕ} {used : List 𝒱} {name : String} {x : Term},
      Λ ⊢ˢ x : β →
        ∀ («Δ₀» : RenamingContext.Context.{uGraphSpecProof}) (hx : RenamingContext.CoversFV «Δ₀» x)
          (pf₀ : ∀ (x! : 𝒱) (X! : SMT.Dom), ∀ v ∈ fv (Term.var x!), (Function.update «Δ₀» x! (some X!) v).isSome = true),
          ⦃fun x =>
            match x with
            | { env := E, types := Λ' } => ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ AList.keys Λ' ⊆ E.usedVars ∧ E.usedVars = used⌝⦄
            loosenAux_prf name pβ x ⦃PostCond.mayThrow fun x_1 x_2 =>
              match x_1 with
              | (x!, x!_spec) =>
                match x_2 with
                | { env := E', types := Γ' } =>
                  ⌜n ≤ E'.freshvarsc ∧
                      AList.insert x! β' Λ ⊆ Γ' ∧
                        x! ∉ Λ ∧
                          x! ∉ used ∧
                            used ⊆ E'.usedVars ∧
                              AList.keys Γ' ⊆ E'.usedVars ∧
                                (∀ v ∈ used, v ∉ Λ → v ∉ Γ') ∧
                                AList.insert x! β' Λ ⊢ˢ Term.var x! : β' ∧
                                  AList.insert x! β' Λ ⊢ˢ x!_spec : SMTType.bool ∧
                                    Γ' ⊢ˢ Term.var x! : β' ∧
                                      Γ' ⊢ˢ x!_spec : SMTType.bool ∧
                                        fv x!_spec ⊆ fv x ∪ {x!} ∧
                                          ∀ (X : SMT.Dom),
                                            ⟦x.abstract «Δ₀» hx⟧ˢ = some X →
                                              ∃ Φ X!,
                                                ∃ (_ :
                                                  ⟦(Term.var x!).abstract (Function.update «Δ₀» x! (some X!)) (pf₀ x! X!)⟧ˢ =
                                                    some X!)
                                                  (hφ :
                                                  RenamingContext.CoversFV (Function.update «Δ₀» x! (some X!)) x!_spec)
                                                  (_ :
                                                  ⟦x!_spec.abstract (Function.update «Δ₀» x! (some X!)) hφ⟧ˢ = some Φ),
                                                  Φ.snd.fst = SMTType.bool ∧
                                                    (Φ.fst = zftrue ∧ X.fst.pair X!.fst ∈ (castZF_of_path pβ).1) ∧
                                                      ∀ (Y : SMT.Dom),
                                                        Y.snd.fst = β' →
                                                          ∀
                                                            (hφY :
                                                              RenamingContext.CoversFV (Function.update «Δ₀» x! (some Y))
                                                                x!_spec),
                                                            ⟦x!_spec.abstract (Function.update «Δ₀» x! (some Y))
                                                                    hφY⟧ˢ.isSome =
                                                              true⌝⦄)
  {Λ : TypeContext} {n : ℕ} {used : List 𝒱} {name : String} {x : Term} (typ_x : Λ ⊢ˢ x : α.fun β.option)
  (hx : RenamingContext.CoversFV «Δ» x) :
  ⦃fun x =>
    match x with
    | { env := E, types := Λ' } => ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ AList.keys Λ' ⊆ E.usedVars ∧ E.usedVars = used⌝⦄
    loosenAux_prf name (pα.graph pβ) x ⦃PostCond.mayThrow fun x_1 x_2 =>
      match x_1 with
      | (x!, x!_spec) =>
        match x_2 with
        | { env := E', types := Γ' } =>
          ⌜n ≤ E'.freshvarsc ∧
              AList.insert x! ((α'.pair β').fun SMTType.bool) Λ ⊆ Γ' ∧
                x! ∉ Λ ∧
                  x! ∉ used ∧
                    used ⊆ E'.usedVars ∧
                      AList.keys Γ' ⊆ E'.usedVars ∧
                        (∀ v ∈ used, v ∉ Λ → v ∉ Γ') ∧
                        AList.insert x! ((α'.pair β').fun SMTType.bool) Λ ⊢ˢ Term.var x! :
                            (α'.pair β').fun SMTType.bool ∧
                          AList.insert x! ((α'.pair β').fun SMTType.bool) Λ ⊢ˢ x!_spec : SMTType.bool ∧
                            Γ' ⊢ˢ Term.var x! : (α'.pair β').fun SMTType.bool ∧
                              Γ' ⊢ˢ x!_spec : SMTType.bool ∧
                                fv x!_spec ⊆ fv x ∪ {x!} ∧
                                  ∀ (X : SMT.Dom),
                                    ⟦x.abstract «Δ» hx⟧ˢ = some X →
                                      ∃ Φ X!,
                                        ∃ (_ : ⟦(Term.var x!).abstract (Function.update «Δ» x! (some X!)) (pf x! X!)⟧ˢ = some X!)
                                          (hφ : RenamingContext.CoversFV (Function.update «Δ» x! (some X!)) x!_spec) (_
                                          : ⟦x!_spec.abstract (Function.update «Δ» x! (some X!)) hφ⟧ˢ = some Φ),
                                          Φ.snd.fst = SMTType.bool ∧
                                            (Φ.fst = zftrue ∧ X.fst.pair X!.fst ∈ (castZF_of_path (pα.graph pβ)).1) ∧
                                              ∀ (Y : SMT.Dom),
                                                Y.snd.fst = (α'.pair β').fun SMTType.bool →
                                                  ∀
                                                    (hφY :
                                                      RenamingContext.CoversFV (Function.update «Δ» x! (some Y))
                                                        x!_spec),
                                                    ⟦x!_spec.abstract (Function.update «Δ» x! (some Y)) hφY⟧ˢ.isSome =
                                                      true⌝⦄ := by
  mintro pre ∀St₁
  mpure pre
  obtain ⟨rfl, rfl, sub, rfl⟩ := pre
  unfold loosenAux_prf
  mspec SMT.freshVar_spec (Γ := St₁.types) (n := St₁.env.freshvarsc) (used := St₁.env.usedVars)
  next x! =>
    mrename_i pre
    mintro ∀St₂
    mcases pre with ⟨St₂_types_eq, x!_fresh, St₂_fvc, St₂_used_eq, x!_not_used⟩
    mspec SMT.freshVar_spec (Γ := St₂.types) (n := St₂.env.freshvarsc) (used := St₂.env.usedVars)
    next z =>
      mrename_i pre
      mintro ∀St₃
      mcases pre with ⟨St₃_types_eq, z_fresh, St₃_fvc, St₃_used_eq, z_not_used⟩
      have typ_var_z_St₃ : St₃.types ⊢ˢ .var z : α.pair β := by
        apply SMT.Typing.var
        rw [St₃_types_eq]
        exact AList.lookup_insert St₂.types
      have hdefault_pair :
          α.defaultZFSet.pair β.defaultZFSet ∈ ⟦α.pair β⟧ᶻ := by
        simpa [SMTType.toZFSet, ZFSet.pair_mem_prod] using
          And.intro SMTType.mem_toZFSet_of_defaultZFSet
            SMTType.mem_toZFSet_of_defaultZFSet
      let Δz : RenamingContext.Context := fun v =>
        if v = z then
          some ⟨α.defaultZFSet.pair β.defaultZFSet, α.pair β, hdefault_pair⟩
        else
          «Δ» v
      have hcov_var_z : RenamingContext.CoversFV Δz (.var z) := by
        intro v hv
        rw [fv, List.mem_singleton] at hv
        subst hv
        simp [Δz]
      have pf_var_z :
          ∀ (xz! : 𝒱) (Xz! : SMT.Dom), ∀ v ∈ fv (Term.var xz!),
            (Function.update Δz xz! (some Xz!) v).isSome = true := by
        intro xz! Xz! v hv
        rw [fv, List.mem_singleton] at hv
        subst hv
        simp [Function.update]
      have ih_pair_z := loosenAux_prf_spec.pair
        (Δz) (pα := pα) (pβ := pβ) pf_var_z
        (graphLiftIH (pf₀ := pf_var_z) pα_ih)
        (graphLiftIH (pf₀ := pf_var_z) pβ_ih)
        (Λ := St₃.types) (n := St₃.env.freshvarsc) (used := St₃.env.usedVars)
        (name := s!"{name}_funGraph_pair") (x := .var z) typ_var_z_St₃ hcov_var_z
      mspec (Std.Do.Triple.and _
        (graphRunPairVarSpec (pα := pα) (pβ := pβ) (name := name) (z := z) (St₃ := St₃))
        ih_pair_z)
      · mpure_intro
        and_intros
        · rfl
        · trivial
        · trivial
        · have keys_sub₂ : AList.keys St₂.types ⊆ St₂.env.usedVars := by
            rw [St₂_types_eq, St₂_used_eq, AList.keys_insert]
            intro v hv
            rw [List.mem_cons] at hv ⊢
            rcases hv with rfl | hv
            · exact Or.inl rfl
            · exact Or.inr (sub (List.mem_of_mem_erase hv))
          rw [St₃_types_eq, St₃_used_eq, AList.keys_insert]
          intro v hv
          rw [List.mem_cons] at hv ⊢
          rcases hv with rfl | hv
          · exact Or.inl rfl
          · exact Or.inr (keys_sub₂ (List.mem_of_mem_erase hv))
        · trivial
      · rename_i out_z
        obtain ⟨z!, z!_spec⟩ := out_z
        mrename_i pre
        mintro ∀St₄
        mpure pre
        obtain ⟨hrun, hn₄, St₄_types_eq, z!_fresh, z!_not_used, used_sub₄, keys_sub₄, preserves₄,
          typ_z!, typ_z!_spec, typ_z!_St₄, typ_z!_spec_St₄, fv_z!_spec, den_z⟩ := pre
        mspec Std.Do.Spec.pure
        have z!_not_St₂ : z! ∉ St₂.types := by
          intro hz!
          apply z!_fresh
          rw [St₃_types_eq, AList.mem_insert]
          exact Or.inr hz!
        have z_ne_z! : z ≠ z! := by
          intro hz
          apply z!_fresh
          rw [St₃_types_eq, hz, AList.mem_insert]
          exact Or.inl rfl
        have hx!_in_St₂ : x! ∈ St₂.types := by
          rw [St₂_types_eq, AList.mem_insert]
          exact Or.inl rfl
        have x_ne_z! : x! ≠ z! := by
          intro hxz
          apply z!_not_St₂
          simpa [hxz] using hx!_in_St₂
        have typ_x_St₂ : St₂.types ⊢ˢ x : α.fun β.option := by
          rw [St₂_types_eq]
          exact SMT.Typing.weakening
            (h := SMT.TypeContext.entries_subset_insert_of_notMem x!_fresh)
            typ_x
        have typ_var_x!_St₂ :
            St₂.types ⊢ˢ .var x! : ((α'.pair β').fun SMTType.bool) := by
          rw [St₂_types_eq]
          apply SMT.Typing.var
          exact AList.lookup_insert St₁.types
        have typ_z!_spec_ctx :
            (AList.insert z! (α'.pair β') (AList.insert z (α.pair β) St₂.types)) ⊢ˢ
              z!_spec : SMTType.bool := by
          simpa [St₃_types_eq] using typ_z!_spec
        have typing_pack := graphTypingPack
          (Γ := St₂.types) (x := x) (x! := x!) (z := z) (z! := z!)
          (α := α) (β := β) (α' := α') (β' := β')
          typ_x_St₂ typ_var_x!_St₂ z_fresh z!_not_St₂ z_ne_z! typ_z!_spec_ctx
        have typ_x!_spec_base := typing_pack.typ_eq
        mpure_intro
        and_intros
        · calc
            St₁.env.freshvarsc ≤ St₂.env.freshvarsc := by rw [St₂_fvc]; exact Nat.le_succ _
            _ ≤ St₃.env.freshvarsc := by rw [St₃_fvc]; exact Nat.le_succ _
            _ ≤ St₄.env.freshvarsc := hn₄
        · intro v hv
          have hv₂ : v ∈ St₂.types.entries := by
            rw [St₂_types_eq]
            exact hv
          have hv₃ : v ∈ St₃.types.entries := by
            rw [St₃_types_eq]
            exact SMT.TypeContext.entries_subset_insert_of_notMem z_fresh hv₂
          exact St₄_types_eq (SMT.TypeContext.entries_subset_insert_of_notMem z!_fresh hv₃)
        · exact x!_fresh
        · exact x!_not_used
        · intro v hv
          have hv₂ : v ∈ St₂.env.usedVars := by
            rw [St₂_used_eq]
            exact List.mem_cons_of_mem _ hv
          exact used_sub₄ (by
            rw [St₃_used_eq]
            exact List.mem_cons_of_mem _ hv₂)
        · exact keys_sub₄
        · -- preserves_types: v ∈ used, v ∉ Λ → v ∉ Γ'
          intro v hv hv_not_Λ
          have hv_in_St₂_used : v ∈ St₂.env.usedVars := by
            rw [St₂_used_eq]
            exact List.mem_cons_of_mem _ hv
          have hv_not_St₂ : v ∉ St₂.types := by
            rw [St₂_types_eq, AList.mem_insert]
            push_neg
            exact ⟨fun h => absurd (h ▸ hv) x!_not_used, hv_not_Λ⟩
          have hv_not_St₃ : v ∉ St₃.types := by
            rw [St₃_types_eq, AList.mem_insert]
            push_neg
            exact ⟨fun h => absurd (h ▸ hv_in_St₂_used) z_not_used, hv_not_St₂⟩
          have hv_in_St₃_used : v ∈ St₃.env.usedVars := by
            rw [St₃_used_eq]
            exact List.mem_cons_of_mem _ hv_in_St₂_used
          exact preserves₄ v hv_in_St₃_used hv_not_St₃
        · apply SMT.Typing.var
          exact AList.lookup_insert St₁.types
        · simpa [St₂_types_eq] using typ_x!_spec_base
        · have typ_x!_base :
            (AList.insert x! ((α'.pair β').fun SMTType.bool) St₁.types) ⊢ˢ
              .var x! : ((α'.pair β').fun SMTType.bool) := by
            apply SMT.Typing.var
            exact AList.lookup_insert St₁.types
          apply SMT.Typing.weakening _ typ_x!_base
          intro v hv
          have hv₂ : v ∈ St₂.types.entries := by
            rwa [St₂_types_eq]
          have hv₃ : v ∈ St₃.types.entries := by
            rw [St₃_types_eq]
            exact SMT.TypeContext.entries_subset_insert_of_notMem z_fresh hv₂
          exact St₄_types_eq (SMT.TypeContext.entries_subset_insert_of_notMem z!_fresh hv₃)
        · have typ_x!_spec_base₁ :
            (AList.insert x! ((α'.pair β').fun SMTType.bool) St₁.types) ⊢ˢ
              (Term.var x! =ˢ
                (λˢ [z!]) [α'.pair β']
                  (.exists [z] [α.pair β]
                    ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec))) :
                SMTType.bool := by
            simpa [St₂_types_eq] using typ_x!_spec_base
          apply SMT.Typing.weakening _ typ_x!_spec_base₁
          intro v hv
          have hv₂ : v ∈ St₂.types.entries := by
            rwa [St₂_types_eq]
          have hv₃ : v ∈ St₃.types.entries := by
            rw [St₃_types_eq]
            exact SMT.TypeContext.entries_subset_insert_of_notMem z_fresh hv₂
          exact St₄_types_eq (SMT.TypeContext.entries_subset_insert_of_notMem z!_fresh hv₃)
        · intro v hv
          simp only [fv, List.cons_append, List.nil_append, List.mem_removeAll_iff, List.mem_cons,
            List.mem_append, List.not_mem_nil, or_false] at hv
          rcases hv with hv | hv
          · rw [List.mem_union_iff]
            exact Or.inr (List.mem_singleton.mpr hv)
          · rcases hv with ⟨hv_main, hv_ne_z!⟩
            rcases hv_main with ⟨hv_main, hv_ne_z⟩
            rcases hv_main with hvx_or_z | hvspec
            · rcases hvx_or_z with hvx | hvz
              · rcases hvx with hvx | hvz
                · rw [List.mem_union_iff]
                  exact Or.inl hvx
                · exact (hv_ne_z hvz).elim
              · exact (hv_ne_z hvz).elim
            · have hv' := fv_z!_spec hvspec
              rw [List.mem_union_iff] at hv'
              rcases hv' with hvz | hvz!
              · exact (hv_ne_z (by simpa [fv] using hvz)).elim
              · exact (hv_ne_z! (List.mem_singleton.mp hvz!)).elim
        · intro X denx
          have hX_ty : X.snd.fst = α.fun β.option := denote_type_eq_of_typing typ_x denx
          have hX_mem : X.fst ∈ ⟦α.fun β.option⟧ᶻ := by
            simpa [hX_ty] using X.snd.snd
          have hX_func : IsFunc ⟦α⟧ᶻ ⟦β.option⟧ᶻ X.fst := by
            rw [ZFSet.mem_funs] at hX_mem
            exact hX_mem
          have x!_not_mem_fv_x : x! ∉ SMT.fv x := by
            intro hx_mem
            exact x!_fresh (SMT.Typing.mem_context_of_mem_fv typ_x hx_mem)
          have hcov_x_upd (Y : SMT.Dom) :
              SMT.RenamingContext.CoversFV (Function.update «Δ» x! (some Y)) x := by
            intro v hv
            by_cases hvx : v = x!
            · subst hvx
              exfalso
              exact x!_not_mem_fv_x hv
            · rw [Function.update_of_ne hvx]
              exact hx v hv
          have denx_upd (Y : SMT.Dom) :
              ⟦x.abstract (Function.update «Δ» x! (some Y)) (hcov_x_upd Y)⟧ˢ = some X := by
            rw [←SMT.RenamingContext.denote]
            rw [←SMT.RenamingContext.denote_update_of_notMem
              («Δ» := «Δ») (t := x) (x := x!) (d := Y) (h := hx) x!_not_mem_fv_x]
            rw [SMT.RenamingContext.denote]
            exact denx
          have z_not_mem_fv_x : z ∉ SMT.fv x := by
            intro hz_mem
            exact z_fresh (SMT.Typing.mem_context_of_mem_fv typ_x_St₂ hz_mem)
          have z!_not_mem_fv_x : z! ∉ SMT.fv x := by
            intro hz!_mem
            exact z!_not_St₂ (SMT.Typing.mem_context_of_mem_fv typ_x_St₂ hz!_mem)
          have x_ne_z : x! ≠ z := by
            intro hxz
            apply z_fresh
            rw [St₂_types_eq, hxz, AList.mem_insert]
            exact Or.inl rfl
          have hfv_lambda_sub :
              SMT.fv
                ((λˢ [z!]) [α'.pair β']
                  (.exists [z] [α.pair β]
                    ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec))) ⊆
                SMT.fv x := by
            intro v hv
            simp only [fv, List.cons_append, List.nil_append, List.mem_removeAll_iff, List.mem_cons,
              List.mem_append, List.not_mem_nil, or_false] at hv
            rcases hv with ⟨hv_main, hv_ne_z!⟩
            rcases hv_main with ⟨hv_main, hv_ne_z⟩
            rcases hv_main with hvx_or_z | hvspec
            · rcases hvx_or_z with hvx | hvz
              · rcases hvx with hvx | hvz
                · exact hvx
                · exact (hv_ne_z hvz).elim
              · exact (hv_ne_z hvz).elim
            · have hv' := fv_z!_spec hvspec
              rw [List.mem_union_iff] at hv'
              rcases hv' with hvz | hvz!
              · exact (hv_ne_z (by simpa [fv] using hvz)).elim
              · exact (hv_ne_z! (List.mem_singleton.mp hvz!)).elim
          have hfv_exists_sub :
              SMT.fv
                (.exists [z] [α.pair β]
                  ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)) ⊆
                SMT.fv x ∪ {z!} := by
            intro v hv
            simp only [fv, List.mem_removeAll_iff, List.mem_cons, List.mem_append,
              List.not_mem_nil, or_false] at hv
            rcases hv with ⟨hv_main, hv_ne_z⟩
            rcases hv_main with hvx_or_z | hvspec
            · rcases hvx_or_z with hvx | hvz
              · rcases hvx with hvx | hvz
                · rw [List.mem_union_iff]
                  exact Or.inl hvx
                · exact (hv_ne_z hvz).elim
              · exact (hv_ne_z hvz).elim
            · have hv' := fv_z!_spec hvspec
              rw [List.mem_union_iff] at hv'
              rcases hv' with hvz | hvz!
              · exact (hv_ne_z (by simpa [fv] using hvz)).elim
              · rw [List.mem_union_iff]
                exact Or.inr hvz!
          have x!_not_mem_fv_lambda :
              x! ∉ SMT.fv
                ((λˢ [z!]) [α'.pair β']
                  (.exists [z] [α.pair β]
                    ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec))) := by
            intro hx_lambda
            exact x!_not_mem_fv_x (hfv_lambda_sub hx_lambda)
          have hcov_lambda_upd (Y : SMT.Dom) :
              RenamingContext.CoversFV
                (Function.update «Δ» x! (some Y))
                ((λˢ [z!]) [α'.pair β']
                  (.exists [z] [α.pair β]
                    ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec))) := by
            intro v hv
            by_cases hvx : v = x!
            · subst hvx
              exfalso
              exact x!_not_mem_fv_lambda hv
            · rw [Function.update_of_ne hvx]
              exact hx v (hfv_lambda_sub hv)
          have hgo_cov (Yfun : SMT.Dom) :
              ∀ v ∈ SMT.fv
                (.exists [z] [α.pair β]
                  ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)),
                v ∉ [z!] → (Function.update «Δ» x! (some Yfun) v).isSome = true :=
            graphGoExistsCovers (x := x) (z!_spec := z!_spec) (x! := x!) (z := z) (z! := z!)
              (α := α) (β := β) hx hfv_exists_sub Yfun
          have hexists_cov (Yfun W : SMT.Dom) :
              RenamingContext.CoversFV
                (Function.update (Function.update «Δ» x! (some Yfun)) z! (some W))
                (.exists [z] [α.pair β]
                  ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)) :=
            graphExistsCovers (x := x) (z!_spec := z!_spec) (x! := x!) (z := z) (z! := z!)
              (α := α) (β := β) hx hfv_exists_sub Yfun W
          have hgo_exists
              (Yfun : SMT.Dom)
              (w : Fin [z!].length → SMT.Dom)
              (hw : ∀ i, (w i).snd.fst = α'.pair β' ∧ (w i).fst ∈ ⟦α'.pair β'⟧ᶻ) :
              (Term.abstract.go
                  (Term.exists [z] [α.pair β]
                    ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec))
                  [z!]
                  (Function.update «Δ» x! (some Yfun))
                  (hgo_cov Yfun)).uncurry w =
                (Term.exists [z] [α.pair β]
                  ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)).abstract
                  (Function.update (Function.update «Δ» x! (some Yfun)) z! (some (w ⟨0, by simp⟩)))
                  (hexists_cov Yfun (w ⟨0, by simp⟩)) := by
            have hgo := SMT.Term.abstract.go.alt_def₂
              (vs := [z!])
              (P := Term.exists [z] [α.pair β]
                ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec))
              (Δctx := Function.update «Δ» x! (some Yfun))
              (αs := List.ofFn w) (vs_αs_len := by simp)
              (Δ_isSome := hgo_cov Yfun)
              (tmp₁ := by
                intro v hv
                have hv' := hfv_exists_sub hv
                rw [List.mem_union_iff] at hv'
                rcases hv' with hvx | hvz!_mem
                · by_cases hvz! : v = z!
                  · subst hvz!
                    exfalso
                    exact z!_not_mem_fv_x hvx
                  · rw [Function.updates_of_not_mem
                      (f := Function.update «Δ» x! (some Yfun))
                      (xs := [z!]) (ys := (List.ofFn w).map Option.some) (k := v)
                      (by simp [hvz!])]
                    by_cases hvx! : v = x!
                    · subst hvx!
                      simp
                    · rw [Function.update_of_ne hvx!]
                      exact hx v hvx
                · exact Function.updates_isSome_of_mem_map_some
                    (Function.update «Δ» x! (some Yfun)) [z!] (List.ofFn w) v
                    hvz!_mem (by simp))
            have h_ofFn_list : List.ofFn w = [w ⟨0, by simp⟩] := by
              simpa using (List.ofFn_succ' (n := 0) w)
            have h_ofFn :
                (fun x =>
                  match x with
                  | ⟨i, hi⟩ => (List.ofFn w)[i]) = w := by
              funext i
              cases i with
              | mk i hi =>
                  simp at hi
                  have hi0 : i = 0 := hi
                  subst hi0
                  simp [h_ofFn_list]
            simpa [h_ofFn, Function.updates] using hgo
          obtain ⟨X!, hcast_mem, hden_lambda_X!⟩ :=
            graphLambdaWitnessAt
              (pα_ih := pα_ih) (pβ_ih := pβ_ih)
              (Γ := St₂.types) («Δ» := «Δ») (x := x) (z!_spec := z!_spec)
              (x! := x!) (z := z) (z! := z!)
              (α := α) (β := β) (α' := α') (β' := β')
              (pα := pα) (pβ := pβ)
              sub St₂_types_eq St₂_used_eq St₃_types_eq St₃_used_eq
              typ_var_z_St₃ hrun typing_pack typ_z!_St₄
              X hX_ty hX_mem hX_func
              hcov_lambda_upd hgo_cov hexists_cov hgo_exists
              hcov_x_upd denx_upd fv_z!_spec
              z_ne_z! x_ne_z x_ne_z!
              z_not_mem_fv_x z!_not_mem_fv_x
          have hvar_X! :
              ⟦(Term.var x!).abstract (Function.update «Δ» x! (some X!)) (pf x! X!)⟧ˢ =
                some X! := by
            rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some_inj]
            apply Option.get_of_eq_some
            exact Function.update_self _ _ _
          let Φtrue : SMT.Dom := ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩
          refine ⟨Φtrue, X!, ?_, ?_, ?_, rfl, ?_⟩
          · exact hvar_X!
          · intro v hv
            simp only [fv, List.mem_append, List.mem_singleton] at hv
            rcases hv with rfl | hv
            · simp
            · have hv_lambda :
                  v ∈
                    SMT.fv
                      ((λˢ [z!]) [α'.pair β']
                        (.exists [z] [α.pair β]
                          ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ
                            z!_spec))) := by
                simpa [fv] using hv
              exact hcov_lambda_upd X! v hv_lambda
          · have hvar :
                ⟦(Term.var x!).abstract (Function.update «Δ» x! (some X!)) (pf x! X!)⟧ˢ = some X! := by
              exact hvar_X!
            rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.bind_eq_bind, hvar, hden_lambda_X!]
            simp only [Option.bind_some, overloadBinOp, Function.onFun, dite_eq_ite, dite_true,
              Option.some_inj]
            congr
            · rw [if_pos (by rw [if_pos (by rw [and_self]; exact X!.2.2)])]
            · funext τ
              conv =>
                enter [1, 2]
                rw [if_pos (by rw [if_pos (by rw [and_self]; exact X!.2.2)])]
            · apply proof_irrel_heq
          · constructor
            · exact ⟨rfl, hcast_mem⟩
            · intro Y hY hφY
              have hvar :
                  ⟦(Term.var x!).abstract (Function.update «Δ» x! (some Y)) (pf x! Y)⟧ˢ = some Y := by
                rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some_inj]
                apply Option.get_of_eq_some
                exact Function.update_self _ _ _
              have hbody_total :=
                graphBodyTotal
                  (Γ := St₂.types) («Δ» := «Δ») (x := x) (z!_spec := z!_spec)
                  (x! := x!) (z := z) (z! := z!)
                  (α := α) (β := β) (α' := α') (β' := β')
                  (X := X) (pα := pα) (pβ := pβ)
                  (hgo_cov := hgo_cov) (hexists_cov := hexists_cov) (hgo_exists := hgo_exists)
                  (hcov_x_upd := hcov_x_upd) (denx_upd := denx_upd)
                  (hX_ty := hX_ty) (hX_func := hX_func)
                  (den_z_at := graphDenZAt
                    («Δ» := «Δ») (pα_ih := pα_ih) (pβ_ih := pβ_ih)
                    sub St₂_types_eq St₂_used_eq St₃_types_eq St₃_used_eq typ_var_z_St₃ hrun)
                  (fv_z!_spec := fv_z!_spec)
                  (z_ne_z! := z_ne_z!) (x_ne_z := x_ne_z) (x_ne_z! := x_ne_z!)
                  (z_not_mem_fv_x := z_not_mem_fv_x)
                  (z!_not_mem_fv_x := z!_not_mem_fv_x)
                  (typ_eq_some_body := typing_pack.typ_eq_some_body)
                  (typ_z!_spec_body := typing_pack.typ_z!_spec_body)
              have hlam_some :
                  ⟦((λˢ [z!]) [α'.pair β']
                        (.exists [z] [α.pair β]
                          ((((@ˢx) (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec))).abstract
                      (Function.update «Δ» x! (some Y)) (hcov_lambda_upd Y)⟧ˢ.isSome =
                    true :=
                graphLambdaIsSome
                  (hcov_lambda_upd := hcov_lambda_upd)
                  (hgo_cov := hgo_cov) (hexists_cov := hexists_cov)
                  (hgo_exists := hgo_exists)
                  (typ_exists := typing_pack.typ_exists)
                  (hbody_total := hbody_total) Y
              obtain ⟨Dlam, hDlam_raw⟩ := Option.isSome_iff_exists.mp hlam_some
              have hDlam_ty : Dlam.snd.fst = (α'.pair β').fun SMTType.bool :=
                denote_type_eq_of_typing (typ_t := typing_pack.typ_lambda) (hden := hDlam_raw)
              have hEq_ty : Y.snd.fst = Dlam.snd.fst := by
                rw [hY, hDlam_ty]
              obtain ⟨Deq, hDeq_raw, hDeq_ty⟩ :=
                denote_eq_some_of_some
                  (h₁ := hvar)
                  (h₂ := hDlam_raw)
                  (hτ := hEq_ty)
              rw [SMT.Term.abstract, SMT.denote, Option.bind_eq_bind, Option.pure_def]
              simpa [proof_irrel_heq] using congrArg Option.isSome hDeq_raw
