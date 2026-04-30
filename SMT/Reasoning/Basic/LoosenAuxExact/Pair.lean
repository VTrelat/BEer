import SMT.Reasoning.Defs
import SMT.Reasoning.LooseningDefs
import SMT.Reasoning.Basic.StateSpecs

open Std.Do SMT ZFSet Classical

set_option maxHeartbeats 2000000
theorem loosenAux_prf_exact.pair («Δ» : RenamingContext.Context) {α β α' β' : SMTType} (pα : α ⇝ α')
  (pβ : β ⇝ β')
  (pf : ∀ (x! : 𝒱) (X! : SMT.Dom), ∀ v ∈ fv (Term.var x!), (Function.update «Δ» x! (some X!) v).isSome = true)
  (pα_ih :
    ∀ {Λ : TypeContext} {n : ℕ} {used : List 𝒱} {name : String} {x : Term},
      Λ ⊢ˢ x : α →
        ∀ (hx : RenamingContext.CoversFV «Δ» x),
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
                                            ⟦x.abstract «Δ» hx⟧ˢ = some X →
                                              ∃ Φ X!,
                                                ∃ (_ :
                                                  ⟦(Term.var x!).abstract (Function.update «Δ» x! (some X!)) (pf x! X!)⟧ˢ =
                                                    some X!)
                                                  (hφ :
                                                  RenamingContext.CoversFV (Function.update «Δ» x! (some X!)) x!_spec)
                                                  (_ :
                                                  ⟦x!_spec.abstract (Function.update «Δ» x! (some X!)) hφ⟧ˢ = some Φ),
                                                  Φ.snd.fst = SMTType.bool ∧
                                                    (Φ.fst = zftrue ∧ X.fst.pair X!.fst ∈ (castZF_of_path pα).1) ∧
                                                      ∀ (Y : SMT.Dom),
                                                        Y.snd.fst = α' →
                                                          ∀
                                                            (hφY :
                                                              RenamingContext.CoversFV (Function.update «Δ» x! (some Y))
                                                                x!_spec),
                                                            ⟦x!_spec.abstract (Function.update «Δ» x! (some Y))
                                                                    hφY⟧ˢ.isSome =
                                                              true ∧
                                                              ∀ {ΦY : SMT.Dom},
                                                                ⟦x!_spec.abstract
                                                                    (Function.update «Δ» x! (some Y)) hφY⟧ˢ =
                                                                  some ΦY →
                                                                ΦY.fst = zftrue →
                                                                  X.fst.pair Y.fst ∈
                                                                    (castZF_of_path pα).1⌝⦄)
  (pβ_ih :
    ∀ {Λ : TypeContext} {n : ℕ} {used : List 𝒱} {name : String} {x : Term},
      Λ ⊢ˢ x : β →
        ∀ (hx : RenamingContext.CoversFV «Δ» x),
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
                                            ⟦x.abstract «Δ» hx⟧ˢ = some X →
                                              ∃ Φ X!,
                                                ∃ (_ :
                                                  ⟦(Term.var x!).abstract (Function.update «Δ» x! (some X!)) (pf x! X!)⟧ˢ =
                                                    some X!)
                                                  (hφ :
                                                  RenamingContext.CoversFV (Function.update «Δ» x! (some X!)) x!_spec)
                                                  (_ :
                                                  ⟦x!_spec.abstract (Function.update «Δ» x! (some X!)) hφ⟧ˢ = some Φ),
                                                  Φ.snd.fst = SMTType.bool ∧
                                                    (Φ.fst = zftrue ∧ X.fst.pair X!.fst ∈ (castZF_of_path pβ).1) ∧
                                                      ∀ (Y : SMT.Dom),
                                                        Y.snd.fst = β' →
                                                          ∀
                                                            (hφY :
                                                              RenamingContext.CoversFV (Function.update «Δ» x! (some Y))
                                                                x!_spec),
                                                            ⟦x!_spec.abstract (Function.update «Δ» x! (some Y))
                                                                    hφY⟧ˢ.isSome =
                                                              true ∧
                                                              ∀ {ΦY : SMT.Dom},
                                                                ⟦x!_spec.abstract
                                                                    (Function.update «Δ» x! (some Y)) hφY⟧ˢ =
                                                                  some ΦY →
                                                                ΦY.fst = zftrue →
                                                                  X.fst.pair Y.fst ∈
                                                                    (castZF_of_path pβ).1⌝⦄)
  {Λ : TypeContext} {n : ℕ} {used : List 𝒱} {name : String} {x : Term} (typ_x : Λ ⊢ˢ x : α.pair β)
  (hx : RenamingContext.CoversFV «Δ» x) :
  ⦃fun x =>
    match x with
    | { env := E, types := Λ' } => ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ AList.keys Λ' ⊆ E.usedVars ∧ E.usedVars = used⌝⦄
    loosenAux_prf name (pα.pair pβ) x ⦃PostCond.mayThrow fun x_1 x_2 =>
      match x_1 with
      | (x!, x!_spec) =>
        match x_2 with
        | { env := E', types := Γ' } =>
          ⌜n ≤ E'.freshvarsc ∧
              AList.insert x! (α'.pair β') Λ ⊆ Γ' ∧
                x! ∉ Λ ∧
                  x! ∉ used ∧
                    used ⊆ E'.usedVars ∧
                      AList.keys Γ' ⊆ E'.usedVars ∧
                        (∀ v ∈ used, v ∉ Λ → v ∉ Γ') ∧
                        AList.insert x! (α'.pair β') Λ ⊢ˢ Term.var x! : α'.pair β' ∧
                          AList.insert x! (α'.pair β') Λ ⊢ˢ x!_spec : SMTType.bool ∧
                            Γ' ⊢ˢ Term.var x! : α'.pair β' ∧
                              Γ' ⊢ˢ x!_spec : SMTType.bool ∧
                                fv x!_spec ⊆ fv x ∪ {x!} ∧
                                  ∀ (X : SMT.Dom),
                                    ⟦x.abstract «Δ» hx⟧ˢ = some X →
                                      ∃ Φ X!,
                                        ∃ (_ : ⟦(Term.var x!).abstract (Function.update «Δ» x! (some X!)) (pf x! X!)⟧ˢ = some X!)
                                          (hφ : RenamingContext.CoversFV (Function.update «Δ» x! (some X!)) x!_spec) (_
                                          : ⟦x!_spec.abstract (Function.update «Δ» x! (some X!)) hφ⟧ˢ = some Φ),
                                          Φ.snd.fst = SMTType.bool ∧
                                            (Φ.fst = zftrue ∧ X.fst.pair X!.fst ∈ (castZF_of_path (pα.pair pβ)).1) ∧
                                              ∀ (Y : SMT.Dom),
                                                Y.snd.fst = α'.pair β' →
                                                  ∀
                                                    (hφY :
                                                      RenamingContext.CoversFV (Function.update «Δ» x! (some Y))
                                                        x!_spec),
                                                    ⟦x!_spec.abstract (Function.update «Δ» x! (some Y)) hφY⟧ˢ.isSome =
                                                      true ∧
                                                      ∀ {ΦY : SMT.Dom},
                                                        ⟦x!_spec.abstract
                                                            (Function.update «Δ» x! (some Y)) hφY⟧ˢ =
                                                          some ΦY →
                                                        ΦY.fst = zftrue →
                                                          X.fst.pair Y.fst ∈
                                                            (castZF_of_path (pα.pair pβ)).1⌝⦄ := by
  mintro pre ∀St₁
  mpure pre
  obtain ⟨rfl, rfl, sub, rfl⟩ := pre
  unfold loosenAux_prf
  mspec SMT.freshVar_spec (Γ := St₁.types) (n := St₁.env.freshvarsc) (used := St₁.env.usedVars)
  next x! =>
  mrename_i pre
  mintro ∀St₂
  mcases pre with ⟨St₂_types_eq, x!_fresh, St₂_fvc, St₂_used_eq, x!_not_used⟩
  have typ_x_St₂ : St₂.types ⊢ˢ x : .pair α β := by
    rw [St₂_types_eq]
    exact SMT.Typing.weakening
      (h := SMT.TypeContext.entries_subset_insert_of_notMem x!_fresh)
      typ_x
  have typ_fst_x_St₂ : St₂.types ⊢ˢ .fst x : α := by
    exact SMT.Typing.fst (Γ := St₂.types) (t := x) (τ := α) (σ := β) typ_x_St₂
  have hx_fst : RenamingContext.CoversFV «Δ» (.fst x) := by
    intro v hv
    exact hx v (by simpa [fv] using hv)
  mspec pα_ih (x := .fst x) (Λ := St₂.types) (n := St₂.env.freshvarsc) (used := St₂.env.usedVars)
    typ_fst_x_St₂ hx_fst
  · mpure_intro
    and_intros
    · trivial
    · trivial
    · rw [St₂_types_eq, St₂_used_eq, AList.keys_insert]
      intro v hv
      rw [List.mem_cons] at hv ⊢
      rcases hv with rfl | hv
      · exact Or.inl rfl
      · exact Or.inr (sub (List.mem_of_mem_erase hv))
    · trivial
  · rename_i out_fst
    obtain ⟨fst!, fst!_spec⟩ := out_fst
    mrename_i pre
    mintro ∀St₃
    mpure pre
    obtain ⟨hn₃, St₃_types_eq, fst!_fresh, fst!_not_used, used_sub₃, keys_sub₃, preserves_fst, typ_fst!, typ_fst!_spec, typ_fst!_St₃, typ_fst!_spec_St₃, fv_fst!_spec, den_fst⟩ := pre
    have typ_snd_x_St₃ : St₃.types ⊢ˢ .snd x : β :=
      SMT.Typing.snd (Γ := St₃.types) (t := x) (τ := α) (σ := β)
        (SMT.Typing.weakening (h := St₃_types_eq) (SMT.Typing.weakening (h := SMT.TypeContext.entries_subset_insert_of_notMem fst!_fresh) typ_x_St₂))
    have hx_snd : RenamingContext.CoversFV «Δ» (.snd x) := by
      intro v hv
      exact hx v (by rwa [fv] at hv)
    mspec pβ_ih (x := .snd x) (Λ := St₃.types) (n := St₃.env.freshvarsc) (used := St₃.env.usedVars)
      typ_snd_x_St₃ hx_snd
    · rename_i out_snd
      obtain ⟨snd!, snd!_spec⟩ := out_snd
      mrename_i pre
      mintro ∀St₄
      mpure pre
      obtain ⟨hn₄, St₄_types_eq, snd!_fresh, snd!_not_used, used_sub₄, keys_sub₄, preserves_snd,
        typ_snd!, typ_snd!_spec, typ_snd!_St₄, typ_snd!_spec_St₄, fv_snd!_spec, den_snd⟩ := pre
      mspec Std.Do.Spec.pure
      have typ_x!_spec_base :
            (AList.insert x! (α'.pair β') St₁.types) ⊢ˢ
              .exists [fst!, snd!] [α', β']
                ((.var x! =ˢ .pair (.var fst!) (.var snd!)) ∧ˢ (fst!_spec ∧ˢ snd!_spec)) : .bool := by
          have typ_snd_x_St₂ : St₂.types ⊢ˢ .snd x : β :=
            SMT.Typing.snd (Γ := St₂.types) (t := x) (τ := α) (σ := β) typ_x_St₂
          have snd!_not_insfstSt₂ : snd! ∉ (AList.insert fst! α' St₂.types) := by
            intro hsnd
            obtain ⟨τsnd, hsnd_lookup⟩ := Option.isSome_iff_exists.mp ((AList.lookup_isSome).2 hsnd)
            exact snd!_fresh ((AList.lookup_isSome).1 (Option.isSome_of_eq_some ((AList.mem_lookup_iff).2 (St₃_types_eq ((AList.mem_lookup_iff).1 hsnd_lookup)))))
          have snd!_not_base : snd! ∉ (AList.insert x! (α'.pair β') St₁.types) := by
            intro hsnd
            apply snd!_not_insfstSt₂
            rw [AList.mem_insert]
            right
            rwa [St₂_types_eq]
          have x_ne_fst : x! ≠ fst! := by
            rintro rfl
            apply fst!_fresh
            rw [St₂_types_eq, AList.mem_insert]
            left
            rfl
          have x_ne_snd : x! ≠ snd! := by
            rintro rfl
            apply snd!_not_base
            rw [AList.mem_insert]
            left
            rfl
          have fst_ne_snd : fst! ≠ snd! := by
            rintro rfl
            apply snd!_not_insfstSt₂
            rw [AList.mem_insert]
            left
            rfl
          have typ_fst!_spec_body :
              (AList.insert snd! β' (AList.insert fst! α' (AList.insert x! (α'.pair β') St₁.types))) ⊢ˢ fst!_spec : .bool := by
            rw [←St₂_types_eq]
            exact SMT.Typing.weakening (h := SMT.TypeContext.entries_subset_insert_of_notMem snd!_not_insfstSt₂) typ_fst!_spec
          have hsub_body :
              (AList.insert snd! β' (AList.insert fst! α' (AList.insert x! (α'.pair β') St₁.types)))
                ⊆ (AList.insert snd! β' St₃.types) := by
            have hsub_base : (AList.insert fst! α' (AList.insert x! (α'.pair β') St₁.types)) ⊆ St₃.types := by
              rw [St₂_types_eq] at St₃_types_eq
              exact St₃_types_eq
            exact SMT.TypeContext.insert_mono (v := snd!) (τ := β') hsub_base
          have hfv_snd_body :
              ∀ v ∈ fv snd!_spec, v ∈ (AList.insert snd! β' (AList.insert fst! α' (AList.insert x! (α'.pair β') St₁.types))) := by
            intro v hv
            have hv' := fv_snd!_spec hv
            rw [List.mem_union_iff] at hv'
            rcases hv' with hvx | hvsnd
            · have hvSt₂ : v ∈ St₂.types := SMT.Typing.mem_context_of_mem_fv typ_snd_x_St₂ hvx
              have hvbase : v ∈ (AList.insert x! (α'.pair β') St₁.types) := by rwa [St₂_types_eq] at hvSt₂
              rw [AList.mem_insert, AList.mem_insert]
              right
              right
              exact hvbase
            · rw [AList.mem_insert]
              exact Or.inl (List.mem_singleton.mp hvsnd)
          have typ_var_x_body :
              (AList.insert snd! β' (AList.insert fst! α' (AList.insert x! (α'.pair β') St₁.types))) ⊢ˢ .var x! : .pair α' β' := by
            apply SMT.Typing.var
            rw [AList.lookup_insert_ne x_ne_snd, AList.lookup_insert_ne x_ne_fst, AList.lookup_insert]
          have typ_var_fst_body :
              (AList.insert snd! β' (AList.insert fst! α' (AList.insert x! (α'.pair β') St₁.types))) ⊢ˢ .var fst! : α' := by
            apply SMT.Typing.var
            rw [AList.lookup_insert_ne fst_ne_snd, AList.lookup_insert]
          have typ_var_snd_body :
              (AList.insert snd! β' (AList.insert fst! α' (AList.insert x! (α'.pair β') St₁.types))) ⊢ˢ .var snd! : β' := by
            apply SMT.Typing.var
            rw [AList.lookup_insert]
          have typ_body :
              (AList.insert snd! β' (AList.insert fst! α' (AList.insert x! (α'.pair β') St₁.types)))
                ⊢ˢ ((.var x! =ˢ .pair (.var fst!) (.var snd!)) ∧ˢ (fst!_spec ∧ˢ snd!_spec)) : .bool :=
            SMT.Typing.and _ _ _
              (SMT.Typing.eq _ _ _ _ typ_var_x_body (SMT.Typing.pair _ _ _ _ _ typ_var_fst_body typ_var_snd_body))
              (SMT.Typing.and _ _ _ typ_fst!_spec_body (SMT.Typing.strengthening_of_fv_subset hsub_body typ_snd!_spec hfv_snd_body))
          have fst!_in_body_ctx :
              fst! ∈ (AList.insert snd! β' (AList.insert fst! α' (AList.insert x! (α'.pair β') St₁.types))) := by
            rw [AList.mem_insert]
            right
            rw [AList.mem_insert]
            left
            rfl
          have snd!_in_body_ctx :
              snd! ∈ (AList.insert snd! β' (AList.insert fst! α' (AList.insert x! (α'.pair β') St₁.types))) := by
            rw [AList.mem_insert]
            left
            rfl
          have fresh_body :
              ∀ v ∈ [fst!, snd!], v ∉ bv ((.var x! =ˢ .pair (.var fst!) (.var snd!)) ∧ˢ (fst!_spec ∧ˢ snd!_spec)) := by
            intro v hv
            rw [List.mem_cons] at hv
            rcases hv with rfl | hv
            · intro hbv
              exact (SMT.Typing.bv_notMem_context typ_body _ hbv) fst!_in_body_ctx
            · rw [List.mem_singleton] at hv
              subst hv
              intro hbv
              exact (SMT.Typing.bv_notMem_context typ_body _ hbv) snd!_in_body_ctx
          have len_eq_vs : [fst!, snd!].length = [α', β'].length := by simp
          apply SMT.Typing.exists
            (Γ := (AList.insert x! (α'.pair β') St₁.types))
            (vs := [fst!, snd!]) (τs := [α', β']) (len_eq := len_eq_vs)
          · intro v hv
            rw [List.mem_cons] at hv
            rcases hv with rfl | hv
            · rw [←St₂_types_eq]
              exact fst!_fresh
            · rw [List.mem_singleton] at hv
              subst hv
              exact snd!_not_base
          · exact fresh_body
          · simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.zero_lt_succ]
          · have hupdate :
              SMT.TypeContext.update (AList.insert x! (α'.pair β') St₁.types) [fst!, snd!] [α', β'] len_eq_vs =
                AList.insert snd! β' (AList.insert fst! α' (AList.insert x! (α'.pair β') St₁.types)) := by
              unfold SMT.TypeContext.update
              simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
                Fin.cast_eq_self, Fin.getElem_fin]
              rw [Fin.foldl_succ_last, Fin.foldl_succ_last]
              simp only [Fin.reduceLast, Fin.coe_ofNat_eq_mod, Nat.mod_succ,
                List.getElem_cons_succ, List.getElem_cons_zero, Fin.last_zero, Fin.isValue,
                Fin.castSucc_zero, Nat.zero_mod, Fin.coe_castSucc, Fin.val_eq_zero,
                Fin.foldl_zero]
            rwa [hupdate]
      mpure_intro
      and_intros
      · calc
          St₁.env.freshvarsc ≤ St₂.env.freshvarsc := by rw [St₂_fvc]; exact Nat.le_succ _
          _ ≤ St₃.env.freshvarsc := hn₃
          _ ≤ St₄.env.freshvarsc := hn₄
      · intro v hv
        have hv₂ : v ∈ St₂.types.entries := by
          rw [St₂_types_eq]
          exact hv
        exact St₄_types_eq (SMT.TypeContext.entries_subset_insert_of_notMem snd!_fresh (St₃_types_eq (SMT.TypeContext.entries_subset_insert_of_notMem fst!_fresh hv₂)))
      · exact x!_fresh
      · exact x!_not_used
      · intro v hv
        have hv₂ : v ∈ St₂.env.usedVars := by
          rw [St₂_used_eq]
          exact List.mem_cons_of_mem _ hv
        exact used_sub₄ (used_sub₃ hv₂)
      · exact keys_sub₄
      · -- preserves_types
        intro v hv hv_not_Λ
        have hv_ne_x : v ≠ x! := fun h => absurd (h ▸ hv) x!_not_used
        have hv_not_St₂ : v ∉ St₂.types := by
          rw [St₂_types_eq, AList.mem_insert]; push_neg
          exact ⟨hv_ne_x, hv_not_Λ⟩
        have hv_in_St₂_used : v ∈ St₂.env.usedVars := by
          rw [St₂_used_eq]; exact List.mem_cons_of_mem _ hv
        have hv_not_St₃ : v ∉ St₃.types := preserves_fst v hv_in_St₂_used hv_not_St₂
        have hv_in_St₃_used : v ∈ St₃.env.usedVars := used_sub₃ hv_in_St₂_used
        exact preserves_snd v hv_in_St₃_used hv_not_St₃
      · apply SMT.Typing.var
        exact AList.lookup_insert St₁.types
      · exact typ_x!_spec_base
      · have typ_x!_base : (AList.insert x! (α'.pair β') St₁.types) ⊢ˢ .var x! : .pair α' β' := by
          apply SMT.Typing.var
          exact AList.lookup_insert St₁.types
        apply SMT.Typing.weakening _ typ_x!_base
        intro v hv
        have hv₂ : v ∈ St₂.types.entries := by
          rwa [St₂_types_eq]
        exact St₄_types_eq (SMT.TypeContext.entries_subset_insert_of_notMem snd!_fresh (St₃_types_eq (SMT.TypeContext.entries_subset_insert_of_notMem fst!_fresh hv₂)))
      · apply SMT.Typing.weakening _ typ_x!_spec_base
        intro v hv
        have hv₂ : v ∈ St₂.types.entries := by
          rwa [St₂_types_eq]
        exact St₄_types_eq
          (SMT.TypeContext.entries_subset_insert_of_notMem snd!_fresh
            (St₃_types_eq
              (SMT.TypeContext.entries_subset_insert_of_notMem fst!_fresh hv₂)))
      · intro v hv
        simp only [fv, List.cons_append, List.nil_append, List.mem_removeAll_iff, List.mem_cons,
          List.mem_append, List.not_mem_nil, or_false, not_or] at hv
        obtain ⟨rfl | rfl | rfl | v_mem_fv_fst!_spec | v_mem_fv_snd!_spec, v_ne_fst!, v_ne_snd!⟩ := hv
        · rw [List.mem_union_iff]
          right
          exact List.mem_of_mem_head? rfl
        · nomatch v_ne_fst!
        · nomatch v_ne_snd!
        · rw [List.mem_union_iff]
          left
          have := fv_fst!_spec v_mem_fv_fst!_spec
          rw [List.mem_union_iff, fv] at this
          apply Or.resolve_right at this
          apply this
          unfold_projs
          dsimp
          change v ∉ [fst!]
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          exact v_ne_fst!
        · rw [List.mem_union_iff]
          left
          have := fv_snd!_spec v_mem_fv_snd!_spec
          rw [List.mem_union_iff, fv] at this
          apply Or.resolve_right at this
          apply this
          unfold_projs
          dsimp
          change v ∉ [snd!]
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          exact v_ne_snd!
      · intro X denx
        classical
        have x!_not_mem_fv_x : x! ∉ SMT.fv x := by
          intro hx_mem
          exact x!_fresh (SMT.Typing.mem_context_of_mem_fv typ_x hx_mem)
        have hXτ' := SMT.PHOAS.denote_welltyped_eq
          (den_t := denx)
          (t := x.abstract «Δ» hx)
          ?_
        on_goal 2 =>
          use SMT.TypeContext.abstract («Δ» := «Δ») ?_, PHOAS.WFTC.of_abstract, (.pair α β)
          · apply PHOAS.Typing.of_abstract
            exact typ_x
        obtain ⟨Xv, τX, hXpair_mem⟩ := X
        obtain rfl : τX = .pair α β := by
          dsimp at hXτ'
          exact hXτ'.symm
        rw [SMTType.toZFSet, ZFSet.mem_prod] at hXpair_mem
        obtain ⟨X₁, hX₁, X₂, hX₂, rfl⟩ := hXpair_mem
        have den_fst_x : ⟦(SMT.Term.fst x).abstract «Δ» hx_fst⟧ˢ = some ⟨X₁, α, hX₁⟩ := by
          rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.bind_eq_bind, denx, Option.bind_some]
          dsimp
          congr
          · rw [π₁_pair]
          · funext τ
            rw [π₁_pair]
          · apply proof_irrel_heq
        have den_snd_x :
            ⟦(SMT.Term.snd x).abstract «Δ» hx_snd⟧ˢ = some ⟨X₂, β, hX₂⟩ := by
          rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.bind_eq_bind, denx, Option.bind_some]
          dsimp
          congr
          · rw [π₂_pair]
          · funext τ
            rw [π₂_pair]
          · apply proof_irrel_heq
        obtain ⟨Φfst, Xfst!, denfst!, hφfst, denφfst, hΦfst_ty, ⟨hΦfst_true, hCastfst⟩, hfst_total⟩ := den_fst _ den_fst_x
        obtain ⟨Φsnd, Xsnd!, densnd!, hφsnd, denφsnd, hΦsnd_ty, ⟨hΦsnd_true, hCastsnd⟩, hsnd_total⟩ := den_snd _ den_snd_x
        have hXfst!_memα' : Xfst!.1 ∈ ⟦α'⟧ᶻ := by
          have hpairmem : X₁.pair Xfst!.1 ∈ ⟦α⟧ᶻ.prod ⟦α'⟧ᶻ := (castZF_of_path pα).2.1 hCastfst
          rw [ZFSet.pair_mem_prod] at hpairmem
          exact hpairmem.2
        have hXsnd!_memβ' : Xsnd!.1 ∈ ⟦β'⟧ᶻ := by
          have hpairmem : X₂.pair Xsnd!.1 ∈ ⟦β⟧ᶻ.prod ⟦β'⟧ᶻ := (castZF_of_path pβ).2.1 hCastsnd
          rw [ZFSet.pair_mem_prod] at hpairmem
          exact hpairmem.2
        let X! : SMT.Dom := ⟨Xfst!.1.pair Xsnd!.1, .pair α' β', by
          rw [SMTType.toZFSet, ZFSet.pair_mem_prod]
          exact ⟨hXfst!_memα', hXsnd!_memβ'⟩⟩
        have fv_x!_spec_sub :
            SMT.fv
                (.exists [fst!, snd!] [α', β']
                  ((.var x! =ˢ .pair (.var fst!) (.var snd!)) ∧ˢ (fst!_spec ∧ˢ snd!_spec))) ⊆
              SMT.fv x ∪ {x!} := by
          intro v hv
          rw [SMT.fv.eq_def] at hv
          rcases List.mem_removeAll_iff.mp hv with ⟨hv_body, hv_not_bound⟩
          have hv_ne_fst : v ≠ fst! := by
            intro h
            apply hv_not_bound
            simp [h]
          have hv_ne_snd : v ≠ snd! := by
            intro h
            apply hv_not_bound
            simp [h]
          have hv_body' : v = x! ∨ v = fst! ∨ v = snd! ∨ v ∈ fv fst!_spec ∨ v ∈ fv snd!_spec := by
            rw [SMT.fv.eq_def] at hv_body
            rw [List.mem_append] at hv_body
            rcases hv_body with hv_eq | hv_specs
            · rw [SMT.fv.eq_def] at hv_eq
              rw [List.mem_append] at hv_eq
              rcases hv_eq with hvx | hvpair
              · rw [SMT.fv.eq_def, List.mem_singleton] at hvx
                exact Or.inl hvx
              · rw [SMT.fv.eq_def] at hvpair
                rw [List.mem_append] at hvpair
                rcases hvpair with hvfst | hvsnd
                · rw [SMT.fv.eq_def, List.mem_singleton] at hvfst
                  exact Or.inr (Or.inl hvfst)
                · rw [SMT.fv.eq_def, List.mem_singleton] at hvsnd
                  exact Or.inr (Or.inr (Or.inl hvsnd))
            · rw [SMT.fv.eq_def] at hv_specs
              rw [List.mem_append] at hv_specs
              rcases hv_specs with hvfstspec | hvsndspec
              · exact Or.inr (Or.inr (Or.inr (Or.inl hvfstspec)))
              · exact Or.inr (Or.inr (Or.inr (Or.inr hvsndspec)))
          rw [List.mem_union_iff]
          rcases hv_body' with hvx | hvfst | hvsnd | hvfstspec | hvsndspec
          · subst hvx
            exact Or.inr (List.mem_singleton.mpr rfl)
          · exact (hv_ne_fst hvfst).elim
          · exact (hv_ne_snd hvsnd).elim
          · have hvfst' := fv_fst!_spec hvfstspec
            rw [List.mem_union_iff] at hvfst'
            rcases hvfst' with hvx_fst | hvfst_single
            · exact Or.inl (by simpa [fv] using hvx_fst)
            · exact (hv_ne_fst (List.mem_singleton.mp hvfst_single)).elim
          · have hvsnd' := fv_snd!_spec hvsndspec
            rw [List.mem_union_iff] at hvsnd'
            rcases hvsnd' with hvx_snd | hvsnd_single
            · exact Or.inl (by simpa [fv] using hvx_snd)
            · exact (hv_ne_snd (List.mem_singleton.mp hvsnd_single)).elim
        refine ⟨⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩, X!, ?_, ?_, ?_, ?_, ?_⟩
        · dsimp [X!]
          rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some_inj]
          apply Option.get_of_eq_some
          apply Function.update_self
        · intro v hv
          by_cases hvx : v = x!
          · subst hvx
            rw [Function.update_self, Option.isSome_some]
          · rw [Function.update_of_ne hvx]
            have hv' := fv_x!_spec_sub hv
            rw [List.mem_union_iff] at hv'
            rcases hv' with hvx_in | hvx_single
            · exact hx v hvx_in
            · exfalso
              exact hvx (List.mem_singleton.mp hvx_single)
        · rw [SMT.Term.abstract, dite_cond_eq_true (eq_true (by rfl)), SMT.PHOAS.Term.exists, SMT.denote, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists]
          refine ⟨zffalse, ⟨SMTType.bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩, ?_, ?_⟩
          · have hlen_pos : [fst!, snd!].length > 0 := by simp
            rw [SMT.denote, dite_cond_eq_true (eq_true hlen_pos)]
            split_ifs with den_t_isSome
            · simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_one_sub_one,
                List.getElem_cons_succ, Fin.zero_eta, Fin.isValue, Nat.zero_mod,
                List.getElem_cons_zero, get.eq_2, Fin.reduceLast, ZFSet.get,
                dite_eq_ite, Fin.forall_fin_two, Fin.coe_ofNat_eq_mod, Fin.zero_eq_one_iff,
                Nat.succ_ne_self, ↓reduceIte, Nat.mod_succ, get.eq_1, Option.pure_def,
                Option.some.injEq, PSigma.mk.injEq, Fin.val_eq_zero]
              let sInter_eq_zffalse : Prop := ?_
              conv_lhs =>
                change sInter_eq_zffalse
              have hsInter_eq_zffalse : sInter_eq_zffalse := by
                ext1 z
                simp only [Fin.isValue, subset_refl, subset_of_empty, notMem_empty, iff_false]
                intro contra
                set sInter_sep : ZFSet.{u_1} := ?_
                conv_lhs at contra =>
                  enter [1]
                  change sInter_sep
                have nemp : sInter_sep.Nonempty := by
                  by_contra emp
                  have sInter_sep_eq_empty := Or.resolve_right (ZFSet.eq_empty_or_nonempty sInter_sep) emp
                  rw [sInter_sep_eq_empty, ZFSet.sInter_empty] at contra
                  nomatch ZFSet.notMem_empty _ contra
                rw [ZFSet.mem_sInter nemp] at contra
                unfold sInter_sep at contra
                clear nemp sInter_sep

                simp only [Fin.isValue, mem_sep, mem_insert_iff,
                  mem_singleton, and_imp, forall_exists_index, forall_eq_or_imp,
                  right_eq_dite_iff, forall_and_index, notMem_empty,
                  imp_false, not_forall, forall_eq] at contra
                obtain ⟨contra1, contra2⟩ := contra

                let w : ZFSet := Xfst!.1.pair Xsnd!.1
                have hw : w ∈ Fin.foldl 1 (fun acc x => acc.prod ⟦β'⟧ᶻ) ⟦α'⟧ᶻ := by
                  rw [Fin.foldl_succ, Fin.foldl_zero, pair_mem_prod]
                  exact ⟨hXfst!_memα', hXsnd!_memβ'⟩

                have hwα : w.π₁ ∈ ⟦α'⟧ᶻ := by
                  unfold w
                  simpa [ZFSet.π₁_pair] using hXfst!_memα'
                obtain ⟨_, _, _, hnotFalse⟩ := contra1 w hw

                have x!_ne_snd! : x! ≠ snd! := by
                  have hx_lookup_St₂ : St₂.types.lookup x! = some (.pair α' β') := by
                    rw [St₂_types_eq]
                    exact AList.lookup_insert St₁.types
                  have hx_entry_St₂ : ⟨x!, .pair α' β'⟩ ∈ St₂.types.entries :=
                    (AList.mem_lookup_iff).1 hx_lookup_St₂
                  have hx_entry_insfst : ⟨x!, .pair α' β'⟩ ∈ (AList.insert fst! α' St₂.types).entries :=
                    SMT.TypeContext.entries_subset_insert_of_notMem fst!_fresh hx_entry_St₂
                  have hx_entry_St₃ : ⟨x!, .pair α' β'⟩ ∈ St₃.types.entries := St₃_types_eq hx_entry_insfst
                  have hx_lookup_St₃ : St₃.types.lookup x! = some (.pair α' β') :=
                    (AList.mem_lookup_iff).2 hx_entry_St₃
                  have hx_mem_St₃ : x! ∈ St₃.types := by
                    exact (AList.lookup_isSome).1 (Option.isSome_of_eq_some hx_lookup_St₃)
                  intro hxs
                  have hsnd_mem_St₃ : snd! ∈ St₃.types := by
                    simpa [hxs] using hx_mem_St₃
                  exact snd!_fresh hsnd_mem_St₃
                have x!_ne_fst! : x! ≠ fst! := by
                  have hx_lookup_St₂ : St₂.types.lookup x! = some (.pair α' β') := by
                    rw [St₂_types_eq]
                    exact AList.lookup_insert St₁.types
                  have hx_mem_St₂ : x! ∈ St₂.types := by
                    exact (AList.lookup_isSome).1 (Option.isSome_of_eq_some hx_lookup_St₂)
                  intro hxf
                  have hfst_mem_St₂ : fst! ∈ St₂.types := by
                    simpa [hxf] using hx_mem_St₂
                  exact fst!_fresh hfst_mem_St₂
                have fst!_ne_snd! : fst! ≠ snd! := by
                  have hfst_lookup_ins : (AList.insert fst! α' St₂.types).lookup fst! = some α' :=
                    AList.lookup_insert St₂.types
                  have hfst_entry_ins : ⟨fst!, α'⟩ ∈ (AList.insert fst! α' St₂.types).entries :=
                    (AList.mem_lookup_iff).1 hfst_lookup_ins
                  have hfst_entry_St₃ : ⟨fst!, α'⟩ ∈ St₃.types.entries := St₃_types_eq hfst_entry_ins
                  have hfst_lookup_St₃ : St₃.types.lookup fst! = some α' :=
                    (AList.mem_lookup_iff).2 hfst_entry_St₃
                  have hfst_mem_St₃ : fst! ∈ St₃.types := by
                    exact (AList.lookup_isSome).1 (Option.isSome_of_eq_some hfst_lookup_St₃)
                  intro hfs
                  have hsnd_mem_St₃ : snd! ∈ St₃.types := by
                    simpa [hfs] using hfst_mem_St₃
                  exact snd!_fresh hsnd_mem_St₃

                apply hnotFalse

                set some_SPEC : Option SMT.Dom := ?_

                conv_rhs =>
                  enter [1, 1]
                  rw [denote]
                  simp only [
                    Fin.isValue, Option.pure_def, Option.failure_eq_none, Option.bind_eq_bind,
                    Function.OfArity.uncurry, Function.FromTypes.uncurry, Fin.isValue,
                    Fin.zero_eq_one_iff, Nat.reduceAdd, Nat.succ_ne_self, ↓dreduceIte,
                    Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.getElem_cons_zero,
                    Term.abstract.go]
                  conv =>
                    enter [1]
                    change some_SPEC
                generalize_proofs some_SPEC_isSome

                obtain ⟨⟨SPEC, τSPEC, hSPEC⟩, SPEC_def⟩ := Option.isSome_iff_exists.mp <| Option.isSome_of_isSome_bind some_SPEC_isSome
                obtain rfl : τSPEC = .bool := by
                  have hsbind := some_SPEC_isSome
                  rw [SPEC_def] at hsbind
                  cases hτ : τSPEC with
                  | bool =>
                    rfl
                  | _ =>
                    simp [hτ] at hsbind
                conv =>
                  conv =>
                    enter [2,1]
                    simp only [SPEC_def, Option.bind_some, Option.get_some, overloadUnaryOp, id_eq]
                  dsimp
                  rw [dif_pos hSPEC]
                  change (⊥ : ZFBool) = (ZFBool.not ⟨SPEC, hSPEC⟩).1
                  rw [←Subtype.ext_iff, eq_comm, ←ZFBool.not_true_eq_false]
                congr

                dsimp at denφfst
                let den_fst!_spec : Option SMT.Dom := ?_

                conv at SPEC_def =>
                  unfold some_SPEC
                  simp only [Fin.isValue, Term.abstract, Function.update_self, Option.get_some]
                  simp only [denote, Fin.isValue, Option.pure_def, Option.some_get,
                    Option.bind_eq_bind, Option.bind_some, Fin.succ_zero_eq_one, ↓dreduceIte,
                    Fin.coe_ofNat_eq_mod, Nat.mod_succ, List.getElem_cons_succ,
                    List.getElem_cons_zero, «Prop».bot_eq_false, Option.failure_eq_none]
                  conv =>
                    enter [1, 1, 1]
                    rw [Function.update_of_ne x!_ne_snd!, Function.update_of_ne x!_ne_fst!, Function.update_self]
                  rw [Option.bind_some]
                  conv =>
                    enter [1, 1, 1, 1]
                    rw [Function.update_of_ne fst!_ne_snd!, Function.update_self]
                  rw [Option.bind_some, Option.bind_some]
                  unfold X!
                  rw [dif_pos rfl, Option.bind_some]
                  dsimp
                  conv =>
                    enter [1, 1, 1]
                    change den_fst!_spec
                have hsnd_not_mem_fv_fstspec : snd! ∉ SMT.fv fst!_spec := by
                  intro hsnd_fstspec
                  exact snd!_fresh (SMT.Typing.mem_context_of_mem_fv typ_fst!_spec_St₃ hsnd_fstspec)
                have hx_not_mem_fv_fstspec : x! ∉ SMT.fv fst!_spec := by
                  intro hx_fstspec
                  have hx' := fv_fst!_spec hx_fstspec
                  rw [List.mem_union_iff] at hx'
                  rcases hx' with hx_in_fv_fstx | hx_eq_fst
                  · have hx_in_fv_x : x! ∈ SMT.fv x := by
                      simpa [SMT.fv] using hx_in_fv_fstx
                    exact x!_not_mem_fv_x hx_in_fv_x
                  · exact x!_ne_fst! (List.mem_singleton.mp hx_eq_fst)
                have hφfst_w :
                    SMT.RenamingContext.CoversFV
                      (Function.update «Δ» fst! (some ⟨w.π₁, ⟨α', hwα⟩⟩))
                      fst!_spec := by
                  intro v hv
                  by_cases hvf : v = fst!
                  · subst hvf
                    simp
                  · simpa [Function.update_of_ne hvf] using hφfst v hv
                have hφfst_x :
                    SMT.RenamingContext.CoversFV
                      (Function.update (Function.update «Δ» fst! (some ⟨w.π₁, ⟨α', hwα⟩⟩)) x! (some X!))
                      fst!_spec :=
                  SMT.RenamingContext.coversFV_update_of_notMem
                    (x := x!) (d := X!) hx_not_mem_fv_fstspec hφfst_w
                have hden_fst!_spec : den_fst!_spec = some Φfst := by
                  rw [←denφfst]
                  unfold den_fst!_spec
                  conv =>
                    enter [1, 1, 2]
                    rw [update_swap (hxy := x!_ne_fst!)]
                  rw [←SMT.RenamingContext.denote]
                  rw [
                    ←SMT.RenamingContext.denote_update_of_notMem (hx := hsnd_not_mem_fv_fstspec) (h := hφfst_x),
                    ←SMT.RenamingContext.denote_update_of_notMem (hx := hx_not_mem_fv_fstspec) (h := hφfst_w),
                    ←SMT.RenamingContext.denote
                  ]
                  congr 4
                  · rw [π₁_pair]
                  · obtain ⟨Xfst!, τXfst!, hXfst!⟩ := Xfst!
                    dsimp
                    obtain rfl := denote_type_eq_of_typing (typ_t := typ_fst!) (hden := denfst!)
                    congr 1
                    · funext τ
                      rw [π₁_pair]
                    · apply proof_irrel_heq

                obtain ⟨Φfst, τΦfst, hΦfst⟩ := Φfst
                obtain rfl := hΦfst_true
                obtain rfl := hΦfst_ty

                dsimp at denφsnd

                let ctx_upd : SMT.RenamingContext.Context := ?_
                let ctx_upd_upd : SMT.RenamingContext.Context := ?_
                conv at SPEC_def =>
                  rw [hden_fst!_spec, Option.bind_some]
                  dsimp
                  conv =>
                    enter [1, 1, 1]
                    conv =>
                      enter [1, 2]
                      rw [update_swap (hxy := fst!_ne_snd!)]
                      conv =>
                        enter [1]
                        rw [update_swap (hxy := x!_ne_snd!)]
                        conv =>
                          enter [1]
                          change ctx_upd
                        change ctx_upd_upd

                have hfst_not_mem_fv_x : fst! ∉ SMT.fv x := by
                  intro hfst_fv_x
                  have hfst_mem_St₂ : fst! ∈ St₂.types :=
                    SMT.Typing.mem_context_of_mem_fv typ_x_St₂ hfst_fv_x
                  exact fst!_fresh hfst_mem_St₂
                have hfst_not_mem_fv_sndspec : fst! ∉ SMT.fv snd!_spec := by
                  intro hfst_sndspec
                  have hfst' := fv_snd!_spec hfst_sndspec
                  rw [List.mem_union_iff] at hfst'
                  rcases hfst' with hfst_in_fv_sndx | hfst_eq_snd
                  · have hfst_in_fv_x : fst! ∈ SMT.fv x := by
                      simpa [SMT.fv] using hfst_in_fv_sndx
                    exact hfst_not_mem_fv_x hfst_in_fv_x
                  · exact fst!_ne_snd! (List.mem_singleton.mp hfst_eq_snd)
                have hx_not_mem_fv_sndspec : x! ∉ SMT.fv snd!_spec := by
                  intro hx_sndspec
                  have hx' := fv_snd!_spec hx_sndspec
                  rw [List.mem_union_iff] at hx'
                  rcases hx' with hx_in_fv_sndx | hx_eq_snd
                  · have hx_in_fv_x : x! ∈ SMT.fv x := by
                      simpa [SMT.fv] using hx_in_fv_sndx
                    exact x!_not_mem_fv_x hx_in_fv_x
                  · exact x!_ne_snd! (List.mem_singleton.mp hx_eq_snd)
                have ctx_upd_upd_coversfv_snd!_spec : RenamingContext.CoversFV ctx_upd_upd snd!_spec := by
                  unfold ctx_upd_upd ctx_upd
                  intro u hu
                  by_cases hus : u = snd!
                  · subst hus
                    simp only [Function.update, eq_rec_constant, ↓reduceDIte, Fin.isValue, dite_eq_ite]
                    split_ifs <;> simp only [Option.isSome_some]
                  · by_cases huf : u = fst!
                    · subst huf
                      exfalso
                      exact hfst_not_mem_fv_sndspec hu
                    · by_cases hux : u = x!
                      · subst hux
                        exfalso
                        exact hx_not_mem_fv_sndspec hu
                      · have hφsnd_u := hφsnd u hu
                        have hΔu : («Δ» u).isSome = true := by
                          simpa [Function.update_of_ne hus] using hφsnd_u
                        simpa [Function.update, hus, huf, hux] using hΔu
                have ctx_upd_coversfv_snd!_spec : RenamingContext.CoversFV ctx_upd snd!_spec := by
                  unfold ctx_upd
                  intro u hu
                  by_cases hus : u = snd!
                  · subst hus
                    simp only [Function.update, ↓reduceDIte, Fin.isValue, Option.isSome_some]
                  · simpa [Function.update_of_ne hus] using hφsnd u hu

                rw [←SMT.RenamingContext.denote.eq_def] at SPEC_def

                have ctx_upd_def : ctx_upd = ctx_upd := rfl
                conv_rhs at ctx_upd_def =>
                  unfold ctx_upd
                  conv =>
                    enter [3, 1]
                    simp only [Function.dcomp, Fin.isValue, Fin.succ_zero_eq_one, ↓dreduceIte,
                      Fin.coe_ofNat_eq_mod, Nat.mod_succ, List.getElem_cons_succ,
                      List.getElem_cons_zero, w, π₂_pair]

                have Xsnd!_eq : ⟨(Xfst!.fst.pair Xsnd!.fst).π₂, ⟨β', ‹w.π₂ ∈ ⟦β'⟧ᶻ›⟩⟩ = Xsnd! := by
                  trans (⟨Xsnd!.fst, β', hXsnd!_memβ'⟩ : SMT.Dom)
                  · congr
                    · rw [π₂_pair]
                    · rw [π₂_pair]
                    · apply proof_irrel_heq
                  · obtain ⟨Xsnd!, τXsnd!, hXsnd!⟩ := Xsnd!
                    dsimp
                    congr
                    symm
                    exact denote_type_eq_of_typing (typ_t := typ_snd!) (hden := densnd!)
                obtain ⟨Φsnd, τΦsnd, hΦsnd⟩ := Φsnd
                obtain rfl := hΦsnd_true
                obtain rfl := hΦsnd_ty

                conv at SPEC_def =>
                  conv =>
                    enter [1, 1, 1]
                    rw [
                      ←SMT.RenamingContext.denote_update_of_notMem (hx := hfst_not_mem_fv_sndspec) (h := ctx_upd_upd_coversfv_snd!_spec),
                      ←SMT.RenamingContext.denote_update_of_notMem (hx := hx_not_mem_fv_sndspec) (h := ctx_upd_coversfv_snd!_spec),
                      SMT.RenamingContext.denote
                    ]
                    conv =>
                      enter [1, 2]
                      rw [ctx_upd_def]
                      enter [3, 1]
                      rw [Xsnd!_eq]
                    rw [denφsnd]
                  simp only [Option.bind_some, Option.some_inj, PSigma.mk.injEq]
                  enter [1]
                  simp only [overloadBinOp_𝔹, overloadBinOp, id_eq]
                  conv =>
                    enter [1, 1]
                    rw [dif_pos ⟨Subtype.property _, Subtype.property _⟩]
                    simp only [Function.onFun, id_eq]
                    conv =>
                      enter [1]
                      simp only [mem_prod, pair_inj, exists_eq_right_right', π₁_pair, π₂_pair,
                        and_self, dite_eq_ite, if_false_right, and_true, Subtype.coe_eta, w]
                      rw [if_pos ⟨hXfst!_memα', hXsnd!_memβ'⟩]
                    conv =>
                      enter [2]
                      simp only [mem_insert_iff, subset_refl, subset_of_empty, mem_singleton,
                        or_true, and_self, ↓reduceDIte]
                      change (⊤ : ZFBool) ⋀ (⊤ : ZFBool)
                      rw [ZFBool.and_true]
                    rw [ZFBool.and_true]
                symm
                exact SPEC_def.1
              refine ⟨hsInter_eq_zffalse, ?_⟩
              congr
              · funext τ
                apply congrArg (fun z => z ∈ ⟦τ⟧ᶻ)
                simp only [Fin.val_eq_zero, List.getElem_cons_zero, Fin.isValue,
                  Fin.forall_fin_two, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Fin.zero_eq_one_iff,
                  Nat.succ_ne_self, ↓reduceIte, Nat.mod_succ, List.getElem_cons_succ]
                exact hsInter_eq_zffalse
              · apply proof_irrel_heq
            · exfalso
              apply den_t_isSome
              intro x_1 hx_1
              simp only [denote, List.length_cons, List.length_nil, Nat.reduceAdd,
                overloadUnaryOp, id_eq, Option.pure_def, Option.failure_eq_none,
                Option.bind_eq_bind]
              unfold SMT.Term.abstract.go
              simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
                Matrix.head_fin_const]
              let i0 : Fin [fst!, snd!].length := ⟨0, hlen_pos⟩
              let i1 : Fin [fst!, snd!].length := ⟨1, Nat.one_lt_succ_succ 0⟩
              have hx0 : (x_1 i0).2.1 = α' ∧ (x_1 i0).1 ∈ ⟦α'⟧ᶻ := by
                simpa [i0] using hx_1 i0
              have hx1 : (x_1 i1).2.1 = β' ∧ (x_1 i1).1 ∈ ⟦β'⟧ᶻ := by
                simpa [i1] using hx_1 i1
              have hφfst0 :
                  SMT.RenamingContext.CoversFV (Function.update «Δ» fst! (some (x_1 i0))) fst!_spec := by
                intro v hv
                by_cases hvf : v = fst!
                · subst hvf
                  simp
                · have hv' := hφfst v hv
                  simpa [Function.update_of_ne hvf] using hv'
              have hφsnd1 :
                  SMT.RenamingContext.CoversFV (Function.update «Δ» snd! (some (x_1 i1))) snd!_spec := by
                intro v hv
                by_cases hvs : v = snd!
                · subst hvs
                  simp
                · have hv' := hφsnd v hv
                  simpa [Function.update_of_ne hvs] using hv'
              have hfst_some := (hfst_total (x_1 i0) hx0.1 hφfst0).1
              have hsnd_some := (hsnd_total (x_1 i1) hx1.1 hφsnd1).1
              have hx_lookup_St₂ : St₂.types.lookup x! = some (.pair α' β') := by
                rw [St₂_types_eq]
                exact AList.lookup_insert St₁.types
              have hx_mem_St₂ : x! ∈ St₂.types := by
                exact (AList.lookup_isSome).1 (Option.isSome_of_eq_some hx_lookup_St₂)
              have hx_entry_St₂ : ⟨x!, .pair α' β'⟩ ∈ St₂.types.entries :=
                (AList.mem_lookup_iff).1 hx_lookup_St₂
              have hx_entry_insfst : ⟨x!, .pair α' β'⟩ ∈ (AList.insert fst! α' St₂.types).entries :=
                SMT.TypeContext.entries_subset_insert_of_notMem fst!_fresh hx_entry_St₂
              have hx_entry_St₃ : ⟨x!, .pair α' β'⟩ ∈ St₃.types.entries := St₃_types_eq hx_entry_insfst
              have hx_lookup_St₃ : St₃.types.lookup x! = some (.pair α' β') :=
                (AList.mem_lookup_iff).2 hx_entry_St₃
              have hx_mem_St₃ : x! ∈ St₃.types := by
                exact (AList.lookup_isSome).1 (Option.isSome_of_eq_some hx_lookup_St₃)
              have x_ne_fst : x! ≠ fst! := by
                intro hxf
                have hfst_mem_St₂ : fst! ∈ St₂.types := by
                  simpa [hxf] using hx_mem_St₂
                exact fst!_fresh hfst_mem_St₂
              have x_ne_snd : x! ≠ snd! := by
                intro hxs
                have hsnd_mem_St₃ : snd! ∈ St₃.types := by
                  simpa [hxs] using hx_mem_St₃
                exact snd!_fresh hsnd_mem_St₃
              have hfst_lookup_ins : (AList.insert fst! α' St₂.types).lookup fst! = some α' :=
                AList.lookup_insert St₂.types
              have hfst_entry_ins : ⟨fst!, α'⟩ ∈ (AList.insert fst! α' St₂.types).entries :=
                (AList.mem_lookup_iff).1 hfst_lookup_ins
              have hfst_entry_St₃ : ⟨fst!, α'⟩ ∈ St₃.types.entries := St₃_types_eq hfst_entry_ins
              have hfst_lookup_St₃ : St₃.types.lookup fst! = some α' :=
                (AList.mem_lookup_iff).2 hfst_entry_St₃
              have hfst_mem_St₃ : fst! ∈ St₃.types := by
                exact (AList.lookup_isSome).1 (Option.isSome_of_eq_some hfst_lookup_St₃)
              have fst_ne_snd : fst! ≠ snd! := by
                intro hfs
                have hsnd_mem_St₃ : snd! ∈ St₃.types := by
                  simpa [hfs] using hfst_mem_St₃
                exact snd!_fresh hsnd_mem_St₃
              have hfst_not_mem_fv_x : fst! ∉ SMT.fv x := by
                intro hfst_fv_x
                have hfst_mem_St₂' : fst! ∈ St₂.types :=
                  SMT.Typing.mem_context_of_mem_fv typ_x_St₂ hfst_fv_x
                exact fst!_fresh hfst_mem_St₂'
              have hx_not_mem_fv_fstspec : x! ∉ SMT.fv fst!_spec := by
                intro hx_fstspec
                have hx' := fv_fst!_spec hx_fstspec
                rw [List.mem_union_iff] at hx'
                rcases hx' with hx_in_fv_fstx | hx_eq_fst
                · have hx_in_fv_x : x! ∈ SMT.fv x := by
                    simpa [SMT.fv] using hx_in_fv_fstx
                  exact x!_not_mem_fv_x hx_in_fv_x
                · exact x_ne_fst (List.mem_singleton.mp hx_eq_fst)
              have hsnd_not_mem_fv_fstspec : snd! ∉ SMT.fv fst!_spec := by
                intro hsnd_fstspec
                have hsnd_mem_St₃ : snd! ∈ St₃.types :=
                  SMT.Typing.mem_context_of_mem_fv typ_fst!_spec_St₃ hsnd_fstspec
                exact snd!_fresh hsnd_mem_St₃
              have hx_not_mem_fv_sndspec : x! ∉ SMT.fv snd!_spec := by
                intro hx_sndspec
                have hx' := fv_snd!_spec hx_sndspec
                rw [List.mem_union_iff] at hx'
                rcases hx' with hx_in_fv_sndx | hx_eq_snd
                · have hx_in_fv_x : x! ∈ SMT.fv x := by
                    simpa [SMT.fv] using hx_in_fv_sndx
                  exact x!_not_mem_fv_x hx_in_fv_x
                · exact x_ne_snd (List.mem_singleton.mp hx_eq_snd)
              have hfst_not_mem_fv_sndspec : fst! ∉ SMT.fv snd!_spec := by
                intro hfst_sndspec
                have hfst' := fv_snd!_spec hfst_sndspec
                rw [List.mem_union_iff] at hfst'
                rcases hfst' with hfst_in_fv_sndx | hfst_eq_snd
                · have hfst_in_fv_x : fst! ∈ SMT.fv x := by
                    simpa [SMT.fv] using hfst_in_fv_sndx
                  exact hfst_not_mem_fv_x hfst_in_fv_x
                · exact fst_ne_snd (List.mem_singleton.mp hfst_eq_snd)
              set Δfst : SMT.RenamingContext.Context := Function.update «Δ» fst! (some (x_1 i0))
              set Δsnd : SMT.RenamingContext.Context := Function.update «Δ» snd! (some (x_1 i1))
              have hφfst_x : SMT.RenamingContext.CoversFV (Function.update Δfst x! (some X!)) fst!_spec :=
                SMT.RenamingContext.coversFV_update_of_notMem
                  (x := x!) (d := X!) hx_not_mem_fv_fstspec hφfst0
              have hφfst_xs :
                  SMT.RenamingContext.CoversFV
                    (Function.update (Function.update Δfst x! (some X!)) snd! (some (x_1 i1))) fst!_spec :=
                SMT.RenamingContext.coversFV_update_of_notMem
                  (x := snd!) (d := (x_1 i1)) hsnd_not_mem_fv_fstspec hφfst_x
              have hfst_some_goal_ctx :
                  (SMT.RenamingContext.denote
                    (Function.update (Function.update (Function.update «Δ» x! (some X!)) fst! (some (x_1 i0))) snd! (some (x_1 i1)))
                    fst!_spec
                    (by
                      simpa only [Δfst, update_swap (f := «Δ») (x := fst!) (y := x!) (hxy := x_ne_fst.symm)
                        (vx := some (x_1 i0)) (vy := some X!)] using hφfst_xs)).isSome = true := by
                have hfst_some_x :
                    (SMT.RenamingContext.denote
                      (Function.update Δfst x! (some X!))
                      fst!_spec hφfst_x).isSome = true := by
                  rw [← denote_isSome_update_of_notMem
                    («Δ» := Δfst) (t := fst!_spec) (x := x!) (d := X!) (h := hφfst0)
                    hx_not_mem_fv_fstspec]
                  simpa only [Δfst] using hfst_some
                have hfst_some_xs :
                    (SMT.RenamingContext.denote
                      (Function.update (Function.update Δfst x! (some X!)) snd! (some (x_1 i1)))
                      fst!_spec hφfst_xs).isSome = true := by
                  rw [← denote_isSome_update_of_notMem
                    («Δ» := Function.update Δfst x! (some X!)) (t := fst!_spec)
                    (x := snd!) (d := (x_1 i1)) (h := hφfst_x) hsnd_not_mem_fv_fstspec]
                  exact hfst_some_x
                simpa only [Δfst, update_swap (f := «Δ») (x := fst!) (y := x!) (hxy := x_ne_fst.symm)
                  (vx := some (x_1 i0)) (vy := some X!)] using hfst_some_xs
              have hφsnd_x : SMT.RenamingContext.CoversFV (Function.update Δsnd x! (some X!)) snd!_spec :=
                SMT.RenamingContext.coversFV_update_of_notMem
                  (x := x!) (d := X!) hx_not_mem_fv_sndspec hφsnd1
              have hφsnd_xf :
                  SMT.RenamingContext.CoversFV
                    (Function.update (Function.update Δsnd x! (some X!)) fst! (some (x_1 i0))) snd!_spec :=
                SMT.RenamingContext.coversFV_update_of_notMem
                  (x := fst!) (d := (x_1 i0)) hfst_not_mem_fv_sndspec hφsnd_x
              have hsnd_some_goal_ctx :
                  (SMT.RenamingContext.denote
                    (Function.update (Function.update (Function.update «Δ» x! (some X!)) fst! (some (x_1 i0))) snd! (some (x_1 i1)))
                    snd!_spec
                    (by
                      simpa only [Δsnd,
                        update_swap (f := «Δ») (x := snd!) (y := x!) (hxy := x_ne_snd.symm)
                          (vx := some (x_1 i1)) (vy := some X!),
                        update_swap (f := Function.update «Δ» x! (some X!)) (x := snd!) (y := fst!)
                          (hxy := fst_ne_snd.symm) (vx := some (x_1 i1)) (vy := some (x_1 i0))] using hφsnd_xf)).isSome = true := by
                have hsnd_some_x :
                    (SMT.RenamingContext.denote
                      (Function.update Δsnd x! (some X!))
                      snd!_spec hφsnd_x).isSome = true := by
                  rw [← denote_isSome_update_of_notMem
                    («Δ» := Δsnd) (t := snd!_spec) (x := x!) (d := X!) (h := hφsnd1)
                    hx_not_mem_fv_sndspec]
                  simpa only [Δsnd] using hsnd_some
                have hsnd_some_xf :
                    (SMT.RenamingContext.denote
                      (Function.update (Function.update Δsnd x! (some X!)) fst! (some (x_1 i0)))
                      snd!_spec hφsnd_xf).isSome = true := by
                  rw [← denote_isSome_update_of_notMem
                    («Δ» := Function.update Δsnd x! (some X!)) (t := snd!_spec)
                    (x := fst!) (d := (x_1 i0)) (h := hφsnd_x) hfst_not_mem_fv_sndspec]
                  exact hsnd_some_x
                simpa only [Δsnd,
                  update_swap (f := «Δ») (x := snd!) (y := x!) (hxy := x_ne_snd.symm)
                    (vx := some (x_1 i1)) (vy := some X!),
                  update_swap (f := Function.update «Δ» x! (some X!)) (x := snd!) (y := fst!)
                    (hxy := fst_ne_snd.symm) (vx := some (x_1 i1)) (vy := some (x_1 i0))] using hsnd_some_xf
              obtain ⟨Dfst, hDfst⟩ := Option.isSome_iff_exists.mp hfst_some_goal_ctx
              obtain ⟨Dsnd, hDsnd⟩ := Option.isSome_iff_exists.mp hsnd_some_goal_ctx
              have hDfst_raw :
                  ⟦fst!_spec.abstract
                    (Function.update (Function.update (Function.update «Δ» x! (some X!)) fst! (some (x_1 i0))) snd! (some (x_1 i1)))
                    (by
                      simpa only [Δfst, update_swap (f := «Δ») (x := fst!) (y := x!) (hxy := x_ne_fst.symm)
                        (vx := some (x_1 i0)) (vy := some X!)] using hφfst_xs)⟧ˢ = some Dfst := by
                simpa [SMT.RenamingContext.denote] using hDfst
              have hDsnd_raw :
                  ⟦snd!_spec.abstract
                    (Function.update (Function.update (Function.update «Δ» x! (some X!)) fst! (some (x_1 i0))) snd! (some (x_1 i1)))
                    (by
                      simpa only [Δsnd,
                        update_swap (f := «Δ») (x := snd!) (y := x!) (hxy := x_ne_snd.symm)
                          (vx := some (x_1 i1)) (vy := some X!),
                        update_swap (f := Function.update «Δ» x! (some X!)) (x := snd!) (y := fst!)
                          (hxy := fst_ne_snd.symm) (vx := some (x_1 i1)) (vy := some (x_1 i0))] using hφsnd_xf)⟧ˢ = some Dsnd := by
                simpa [SMT.RenamingContext.denote] using hDsnd
              have hDfst_ty : Dfst.2.1 = .bool := by
                exact denote_type_eq_of_typing (typ_t := typ_fst!_spec_St₃) (hden := hDfst_raw)
              have hDsnd_ty : Dsnd.2.1 = .bool := by
                exact denote_type_eq_of_typing (typ_t := typ_snd!_spec_St₄) (hden := hDsnd_raw)
              let Δgoal : SMT.RenamingContext.Context :=
                Function.update (Function.update (Function.update «Δ» x! (some X!))
                  fst! (some (x_1 i0))) snd! (some (x_1 i1))
              have hcov_x! : SMT.RenamingContext.CoversFV Δgoal (SMT.Term.var x!) := by
                intro v hv
                rw [SMT.fv, List.mem_singleton] at hv
                subst hv
                simp [Δgoal, Function.update, x_ne_fst, x_ne_snd]
              have hcov_fst : SMT.RenamingContext.CoversFV Δgoal (SMT.Term.var fst!) := by
                intro v hv
                rw [SMT.fv, List.mem_singleton] at hv
                subst hv
                simp [Δgoal, Function.update, fst_ne_snd]
              have hcov_snd : SMT.RenamingContext.CoversFV Δgoal (SMT.Term.var snd!) := by
                intro v hv
                rw [SMT.fv, List.mem_singleton] at hv
                subst hv
                simp only [Function.update_self, Option.isSome_some, Δgoal]
              have hden_x! :
                  ⟦(SMT.Term.var x!).abstract Δgoal hcov_x!⟧ˢ = some X! := by
                rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some_inj]
                apply Option.get_of_eq_some
                simp [Δgoal, Function.update, x_ne_fst, x_ne_snd]
              have hden_fst :
                  ⟦(SMT.Term.var fst!).abstract Δgoal hcov_fst⟧ˢ = some (x_1 i0) := by
                rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some_inj]
                apply Option.get_of_eq_some
                simp [Δgoal, Function.update, fst_ne_snd]
              have hden_snd :
                  ⟦(SMT.Term.var snd!).abstract Δgoal hcov_snd⟧ˢ = some (x_1 i1) := by
                rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some_inj]
                apply Option.get_of_eq_some
                simp only [Function.update_self, Δgoal]
              obtain ⟨Dpair, hDpair_raw, hDpair_ty⟩ :=
                denote_pair_some_of_some hden_fst hden_snd
              have hDpair_ty' : Dpair.2.1 = α'.pair β' := by
                simp only [hDpair_ty, hx0.1, hx1.1]
              have hEq_ty : X!.2.1 = Dpair.2.1 := by
                calc
                  X!.2.1 = α'.pair β' := by rfl
                  _ = Dpair.2.1 := hDpair_ty'.symm
              have hcov_eq : SMT.RenamingContext.CoversFV Δgoal
                  (SMT.Term.var x! =ˢ SMT.Term.pair (SMT.Term.var fst!) (SMT.Term.var snd!)) := by
                intro v hv
                rw [SMT.fv.eq_def] at hv
                rw [List.mem_append] at hv
                rcases hv with hvx | hvpair
                · rw [SMT.fv, List.mem_singleton] at hvx
                  subst hvx
                  simp [Δgoal, Function.update, x_ne_fst, x_ne_snd]
                · have hvpair' :
                    v ∈ SMT.fv (SMT.Term.var fst!) ∨ v ∈ SMT.fv (SMT.Term.var snd!) := by
                    simpa [SMT.fv, List.mem_append] using hvpair
                  rcases hvpair' with hvfst | hvsnd
                  · exact hcov_fst _ hvfst
                  · exact hcov_snd _ hvsnd
              have hden_eq_rhs :
                  ⟦(SMT.Term.pair (SMT.Term.var fst!) (SMT.Term.var snd!)).abstract Δgoal
                    (by
                      intro v hv
                      have hv' :
                          v ∈ SMT.fv (SMT.Term.var fst!) ∨ v ∈ SMT.fv (SMT.Term.var snd!) := by
                        simpa [SMT.fv, List.mem_append] using hv
                      rcases hv' with hvfst | hvsnd
                      · exact hcov_fst _ hvfst
                      · exact hcov_snd _ hvsnd)⟧ˢ = some Dpair := by
                simpa only [SMT.Term.abstract, proof_irrel_heq] using hDpair_raw
              obtain ⟨Deq, hDeq_raw, hDeq_ty⟩ :=
                denote_eq_some_of_some
                  (h₁ := hden_x!)
                  (h₂ := hden_eq_rhs)
                  (hτ := hEq_ty)
              obtain ⟨Dspec, hDspec_raw, hDspec_ty⟩ :=
                denote_and_some_bool_of_some_bool hDfst_raw hDfst_ty hDsnd_raw hDsnd_ty
              obtain ⟨Dbody, hDbody_raw, hDbody_ty⟩ :=
                denote_and_some_bool_of_some_bool hDeq_raw hDeq_ty hDspec_raw hDspec_ty
              have hnot_some :=
                denote_not_isSome_of_some_bool (hden := hDbody_raw) (hTy := hDbody_ty)
              simpa only [SMT.Term.abstract, SMT.denote, Option.bind_eq_bind, Option.pure_def,
                SMT.Term.abstract.go, Function.OfArity.uncurry, Function.FromTypes.uncurry,
                Δgoal, i0, i1, proof_irrel_heq] using hnot_some
          · dsimp
            congr
            · simp only [overloadUnaryOp, subset_refl, subset_of_empty, mem_insert_iff,
              mem_singleton, true_or, id_eq, symmDiff_empty, dite_true]
            · funext τ
              simp only [overloadUnaryOp, subset_refl, subset_of_empty, mem_insert_iff,
                mem_singleton, true_or, dite_true, id_eq, symmDiff_empty]
            · apply proof_irrel_heq
        · rfl
        · constructor
          · dsimp [X!]
            have hmem_fprod :
                (X₁.pair X₂).pair (Xfst!.1.pair Xsnd!.1) ∈
                  fprod (castZF_of_path pα).1 (castZF_of_path pβ).1
                    (hf := (castZF_of_path pα).2) (hg := (castZF_of_path pβ).2) := by
              rw [ZFSet.pair_mem_fprod (hf := (castZF_of_path pα).2) (hg := (castZF_of_path pβ).2)]
              refine ⟨X₁, X₂, hX₁, hX₂, rfl, ?_⟩
              · have hCastfst' : X₁.pair Xfst!.1 ∈ (castZF_of_path pα).1 := hCastfst
                have hcastα_pfunc :
                    ((castZF_of_path pα).1).IsPFunc ⟦α⟧ᶻ ⟦α'⟧ᶻ :=
                  ZFSet.is_func_is_pfunc
                    (f := (castZF_of_path pα).1)
                    (A := ⟦α⟧ᶻ) (B := ⟦α'⟧ᶻ)
                    (castZF_of_path pα).2
                have hfst_val :
                    Xfst!.1 =
                      (@ᶻ(castZF_of_path pα).1
                        ⟨X₁, by
                          rw [ZFSet.is_func_dom_eq (castZF_of_path pα).2]
                          exact hX₁⟩) := by
                  symm
                  exact congrArg Subtype.val (fapply.of_pair (hf := hcastα_pfunc) hCastfst')
                have hcastβ_pfunc :
                    ((castZF_of_path pβ).1).IsPFunc ⟦β⟧ᶻ ⟦β'⟧ᶻ :=
                  ZFSet.is_func_is_pfunc (f := (castZF_of_path pβ).1) (castZF_of_path pβ).2
                have hsnd_val :
                    Xsnd!.1 =
                      (@ᶻ(castZF_of_path pβ).1
                        ⟨X₂, by
                          rw [ZFSet.is_func_dom_eq (castZF_of_path pβ).2]
                          exact hX₂⟩) := by
                  symm
                  exact congrArg Subtype.val (fapply.of_pair (hf := hcastβ_pfunc) hCastsnd)
                rw [hfst_val, hsnd_val]
            rw [eq_self, true_and, castZF_of_path, castZF_pair]
            exact hmem_fprod
          · intro Y hYβ hφY
            rw [SMT.Term.abstract, dite_cond_eq_true (eq_true (by rfl)), SMT.PHOAS.Term.exists, SMT.denote]
            simp only [Option.bind_eq_bind, Option.pure_def]
            have hlen_pos : [fst!, snd!].length > 0 := Nat.zero_lt_succ 1
            rw [SMT.denote, dite_cond_eq_true (eq_true hlen_pos)]
            split_ifs with den_t_isSome
            · constructor
              · simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_one_sub_one,
                List.getElem_cons_succ, Fin.zero_eta, Fin.isValue, Fin.coe_ofNat_eq_mod,
                Nat.zero_mod, List.getElem_cons_zero, ZFSet.get, Fin.reduceLast,
                dite_eq_ite, Option.pure_def, Option.failure_eq_none, Option.bind_some,
                Option.isSome_some]
              · intro ΦY hdenY htrue
                have hdenY' := hdenY
                simp only [Option.pure_def, Option.bind_some] at hdenY'
                have hExistsTrue :=
                  (congrArg (fun d : SMT.Dom => d.fst) (Option.some.inj hdenY')).trans htrue
                by_contra hnotmem
                have hcontra : False := by
                  have hΔ_body :
                      ∀ v ∈ SMT.fv
                        ((SMT.Term.var x! =ˢ SMT.Term.pair (SMT.Term.var fst!) (SMT.Term.var snd!)) ∧ˢ
                          (fst!_spec ∧ˢ snd!_spec)),
                        v ∉ [fst!, snd!] → (Function.update «Δ» x! (some Y) v).isSome = true := by
                    intro v hv hv_not_vs
                    exact hφY v (SMT.fv.mem_exists ⟨hv, hv_not_vs⟩)
                  let bodyF : ZFSet → ZFSet := fun y =>
                    if hy : y.hasArity [fst!, snd!].length ∧
                        ∀ i : Fin [fst!, snd!].length, y.get [fst!, snd!].length i ∈ ⟦[α', β'][i]⟧ᶻ then
                      (⟦¬ˢ'
                          (Term.abstract.go
                            ((SMT.Term.var x! =ˢ SMT.Term.pair (SMT.Term.var fst!) (SMT.Term.var snd!)) ∧ˢ
                              (fst!_spec ∧ˢ snd!_spec))
                            [fst!, snd!]
                            (Function.update «Δ» x! (some Y))
                            hΔ_body).uncurry
                          (fun i => ⟨y.get [fst!, snd!].length i, [α', β'][i], hy.2 i⟩)⟧ˢ.get
                        (den_t_isSome (fun i => ⟨rfl, hy.2 i⟩))).fst
                    else
                      zffalse
                  let D : ZFSet := ⟦α'⟧ᶻ.prod ⟦β'⟧ᶻ
                  have hall :
                      ∀ y ∈ D,
                        bodyF y = zftrue := by
                    intro y hy
                    rw [ZFSet.mem_prod] at hy
                    obtain ⟨a, ha, b, hb, rfl⟩ := hy
                    let i0 : Fin [fst!, snd!].length := ⟨0, hlen_pos⟩
                    let i1 : Fin [fst!, snd!].length := ⟨1, Nat.one_lt_succ_succ 0⟩
                    have hy1 :
                        (a.pair b).hasArity 2 ∧
                          ∀ i : Fin 2,
                            (if i = 1 then (a.pair b).π₂ else (a.pair b).π₁) ∈ ⟦[α', β'][i]⟧ᶻ := by
                      constructor
                      · simp [ZFSet.hasArity]
                      · rw [Fin.forall_fin_two]
                        constructor
                        · simpa
                        · simpa
                    let x_1 : Fin [fst!, snd!].length → SMT.Dom := fun i =>
                      ⟨if i = i1 then (a.pair b).π₂ else (a.pair b).π₁, [α', β'][i], by
                        simpa [i1, List.length_cons, List.length_nil, Nat.reduceAdd] using hy1.2 i⟩
                    have hx_1 :
                        ∀ i : Fin [fst!, snd!].length,
                          (x_1 i).snd.fst = [α', β'][i] ∧ (x_1 i).fst ∈ ⟦[α', β'][i]⟧ᶻ := by
                      intro i
                      exact ⟨rfl, by
                        simpa [x_1, List.length_cons, List.length_nil, Nat.reduceAdd] using hy1.2 i⟩
                    have hbodyF_y :
                        bodyF (a.pair b) =
                          (⟦¬ˢ'
                              (Term.abstract.go
                                ((SMT.Term.var x! =ˢ SMT.Term.pair (SMT.Term.var fst!) (SMT.Term.var snd!)) ∧ˢ
                                  (fst!_spec ∧ˢ snd!_spec))
                                [fst!, snd!]
                                (Function.update «Δ» x! (some Y))
                                hΔ_body).uncurry x_1⟧ˢ.get
                            (den_t_isSome hx_1)).fst := by
                      dsimp [bodyF]
                      split_ifs with hy
                      · exact rfl
                      · exfalso
                        exact hy (by
                          simpa [i1, List.length_cons, List.length_nil, Nat.reduceAdd] using hy1)
                    have hx0 : (x_1 i0).2.1 = α' ∧ (x_1 i0).1 ∈ ⟦α'⟧ᶻ := by
                      simpa [i0] using hx_1 i0
                    have hx1 : (x_1 i1).2.1 = β' ∧ (x_1 i1).1 ∈ ⟦β'⟧ᶻ := by
                      simpa [i1] using hx_1 i1
                    have hφfst0 :
                        SMT.RenamingContext.CoversFV (Function.update «Δ» fst! (some (x_1 i0))) fst!_spec := by
                      intro v hv
                      by_cases hvf : v = fst!
                      · subst hvf
                        simp
                      · have hv' := hφfst v hv
                        simpa [Function.update_of_ne hvf] using hv'
                    have hφsnd1 :
                        SMT.RenamingContext.CoversFV (Function.update «Δ» snd! (some (x_1 i1))) snd!_spec := by
                      intro v hv
                      by_cases hvs : v = snd!
                      · subst hvs
                        simp
                      · have hv' := hφsnd v hv
                        simpa [Function.update_of_ne hvs] using hv'
                    have hfst_some := (hfst_total (x_1 i0) hx0.1 hφfst0).1
                    have hsnd_some := (hsnd_total (x_1 i1) hx1.1 hφsnd1).1
                    have hx_lookup_St₂ : St₂.types.lookup x! = some (.pair α' β') := by
                      rw [St₂_types_eq]
                      exact AList.lookup_insert St₁.types
                    have hx_mem_St₂ : x! ∈ St₂.types := by
                      exact (AList.lookup_isSome).1 (Option.isSome_of_eq_some hx_lookup_St₂)
                    have hx_entry_St₂ : ⟨x!, .pair α' β'⟩ ∈ St₂.types.entries :=
                      (AList.mem_lookup_iff).1 hx_lookup_St₂
                    have hx_entry_insfst : ⟨x!, .pair α' β'⟩ ∈ (AList.insert fst! α' St₂.types).entries :=
                      SMT.TypeContext.entries_subset_insert_of_notMem fst!_fresh hx_entry_St₂
                    have hx_entry_St₃ : ⟨x!, .pair α' β'⟩ ∈ St₃.types.entries := St₃_types_eq hx_entry_insfst
                    have hx_lookup_St₃ : St₃.types.lookup x! = some (.pair α' β') :=
                      (AList.mem_lookup_iff).2 hx_entry_St₃
                    have hx_mem_St₃ : x! ∈ St₃.types := by
                      exact (AList.lookup_isSome).1 (Option.isSome_of_eq_some hx_lookup_St₃)
                    have x_ne_fst : x! ≠ fst! := by
                      intro hxf
                      have hfst_mem_St₂ : fst! ∈ St₂.types := by
                        simpa [hxf] using hx_mem_St₂
                      exact fst!_fresh hfst_mem_St₂
                    have x_ne_snd : x! ≠ snd! := by
                      intro hxs
                      have hsnd_mem_St₃ : snd! ∈ St₃.types := by
                        simpa [hxs] using hx_mem_St₃
                      exact snd!_fresh hsnd_mem_St₃
                    have hfst_lookup_ins : (AList.insert fst! α' St₂.types).lookup fst! = some α' :=
                      AList.lookup_insert St₂.types
                    have hfst_entry_ins : ⟨fst!, α'⟩ ∈ (AList.insert fst! α' St₂.types).entries :=
                      (AList.mem_lookup_iff).1 hfst_lookup_ins
                    have hfst_entry_St₃ : ⟨fst!, α'⟩ ∈ St₃.types.entries := St₃_types_eq hfst_entry_ins
                    have hfst_lookup_St₃ : St₃.types.lookup fst! = some α' :=
                      (AList.mem_lookup_iff).2 hfst_entry_St₃
                    have hfst_mem_St₃ : fst! ∈ St₃.types := by
                      exact (AList.lookup_isSome).1 (Option.isSome_of_eq_some hfst_lookup_St₃)
                    have fst_ne_snd : fst! ≠ snd! := by
                      intro hfs
                      have hsnd_mem_St₃ : snd! ∈ St₃.types := by
                        simpa [hfs] using hfst_mem_St₃
                      exact snd!_fresh hsnd_mem_St₃
                    have hfst_not_mem_fv_x : fst! ∉ SMT.fv x := by
                      intro hfst_fv_x
                      have hfst_mem_St₂' : fst! ∈ St₂.types :=
                        SMT.Typing.mem_context_of_mem_fv typ_x_St₂ hfst_fv_x
                      exact fst!_fresh hfst_mem_St₂'
                    have hx_not_mem_fv_fstspec : x! ∉ SMT.fv fst!_spec := by
                      intro hx_fstspec
                      have hx' := fv_fst!_spec hx_fstspec
                      rw [List.mem_union_iff] at hx'
                      rcases hx' with hx_in_fv_fstx | hx_eq_fst
                      · have hx_in_fv_x : x! ∈ SMT.fv x := by
                          simpa [SMT.fv] using hx_in_fv_fstx
                        exact x!_not_mem_fv_x hx_in_fv_x
                      · exact x_ne_fst (List.mem_singleton.mp hx_eq_fst)
                    have hsnd_not_mem_fv_fstspec : snd! ∉ SMT.fv fst!_spec := by
                      intro hsnd_fstspec
                      have hsnd_mem_St₃ : snd! ∈ St₃.types :=
                        SMT.Typing.mem_context_of_mem_fv typ_fst!_spec_St₃ hsnd_fstspec
                      exact snd!_fresh hsnd_mem_St₃
                    have hx_not_mem_fv_sndspec : x! ∉ SMT.fv snd!_spec := by
                      intro hx_sndspec
                      have hx' := fv_snd!_spec hx_sndspec
                      rw [List.mem_union_iff] at hx'
                      rcases hx' with hx_in_fv_sndx | hx_eq_snd
                      · have hx_in_fv_x : x! ∈ SMT.fv x := by
                          simpa [SMT.fv] using hx_in_fv_sndx
                        exact x!_not_mem_fv_x hx_in_fv_x
                      · exact x_ne_snd (List.mem_singleton.mp hx_eq_snd)
                    have hfst_not_mem_fv_sndspec : fst! ∉ SMT.fv snd!_spec := by
                      intro hfst_sndspec
                      have hfst' := fv_snd!_spec hfst_sndspec
                      rw [List.mem_union_iff] at hfst'
                      rcases hfst' with hfst_in_fv_sndx | hfst_eq_snd
                      · have hfst_in_fv_x : fst! ∈ SMT.fv x := by
                          simpa [SMT.fv] using hfst_in_fv_sndx
                        exact hfst_not_mem_fv_x hfst_in_fv_x
                      · exact fst_ne_snd (List.mem_singleton.mp hfst_eq_snd)
                    set Δfst : SMT.RenamingContext.Context := Function.update «Δ» fst! (some (x_1 i0))
                    set Δsnd : SMT.RenamingContext.Context := Function.update «Δ» snd! (some (x_1 i1))
                    have hφfst_x : SMT.RenamingContext.CoversFV (Function.update Δfst x! (some Y)) fst!_spec :=
                      SMT.RenamingContext.coversFV_update_of_notMem
                        (x := x!) (d := Y) hx_not_mem_fv_fstspec hφfst0
                    have hφfst_xs :
                        SMT.RenamingContext.CoversFV
                          (Function.update (Function.update Δfst x! (some Y)) snd! (some (x_1 i1))) fst!_spec :=
                      SMT.RenamingContext.coversFV_update_of_notMem
                        (x := snd!) (d := (x_1 i1)) hsnd_not_mem_fv_fstspec hφfst_x
                    have hfst_some_goal_ctx :
                        (SMT.RenamingContext.denote
                          (Function.update (Function.update (Function.update «Δ» x! (some Y)) fst! (some (x_1 i0))) snd! (some (x_1 i1)))
                          fst!_spec
                          (by
                            simpa only [Δfst, update_swap (f := «Δ») (x := fst!) (y := x!) (hxy := x_ne_fst.symm)
                              (vx := some (x_1 i0)) (vy := some Y)] using hφfst_xs)).isSome = true := by
                      have hfst_some_x :
                          (SMT.RenamingContext.denote
                            (Function.update Δfst x! (some Y))
                            fst!_spec hφfst_x).isSome = true := by
                        rw [← denote_isSome_update_of_notMem
                          («Δ» := Δfst) (t := fst!_spec) (x := x!) (d := Y) (h := hφfst0)
                          hx_not_mem_fv_fstspec]
                        simpa only [Δfst] using hfst_some
                      have hfst_some_xs :
                          (SMT.RenamingContext.denote
                            (Function.update (Function.update Δfst x! (some Y)) snd! (some (x_1 i1)))
                            fst!_spec hφfst_xs).isSome = true := by
                        rw [← denote_isSome_update_of_notMem
                          («Δ» := Function.update Δfst x! (some Y)) (t := fst!_spec)
                          (x := snd!) (d := (x_1 i1)) (h := hφfst_x) hsnd_not_mem_fv_fstspec]
                        exact hfst_some_x
                      simpa only [Δfst, update_swap (f := «Δ») (x := fst!) (y := x!) (hxy := x_ne_fst.symm)
                        (vx := some (x_1 i0)) (vy := some Y)] using hfst_some_xs
                    have hφsnd_x : SMT.RenamingContext.CoversFV (Function.update Δsnd x! (some Y)) snd!_spec :=
                      SMT.RenamingContext.coversFV_update_of_notMem
                        (x := x!) (d := Y) hx_not_mem_fv_sndspec hφsnd1
                    have hφsnd_xf :
                        SMT.RenamingContext.CoversFV
                          (Function.update (Function.update Δsnd x! (some Y)) fst! (some (x_1 i0))) snd!_spec :=
                      SMT.RenamingContext.coversFV_update_of_notMem
                        (x := fst!) (d := (x_1 i0)) hfst_not_mem_fv_sndspec hφsnd_x
                    have hsnd_some_goal_ctx :
                        (SMT.RenamingContext.denote
                          (Function.update (Function.update (Function.update «Δ» x! (some Y)) fst! (some (x_1 i0))) snd! (some (x_1 i1)))
                          snd!_spec
                          (by
                            simpa only [Δsnd,
                              update_swap (f := «Δ») (x := snd!) (y := x!) (hxy := x_ne_snd.symm)
                                (vx := some (x_1 i1)) (vy := some Y),
                              update_swap (f := Function.update «Δ» x! (some Y)) (x := snd!) (y := fst!)
                                (hxy := fst_ne_snd.symm) (vx := some (x_1 i1)) (vy := some (x_1 i0))] using hφsnd_xf)).isSome = true := by
                      have hsnd_some_x :
                          (SMT.RenamingContext.denote
                            (Function.update Δsnd x! (some Y))
                            snd!_spec hφsnd_x).isSome = true := by
                        rw [← denote_isSome_update_of_notMem
                          («Δ» := Δsnd) (t := snd!_spec) (x := x!) (d := Y) (h := hφsnd1)
                          hx_not_mem_fv_sndspec]
                        simpa only [Δsnd] using hsnd_some
                      have hsnd_some_xf :
                          (SMT.RenamingContext.denote
                            (Function.update (Function.update Δsnd x! (some Y)) fst! (some (x_1 i0)))
                            snd!_spec hφsnd_xf).isSome = true := by
                        rw [← denote_isSome_update_of_notMem
                          («Δ» := Function.update Δsnd x! (some Y)) (t := snd!_spec)
                          (x := fst!) (d := (x_1 i0)) (h := hφsnd_x) hfst_not_mem_fv_sndspec]
                        exact hsnd_some_x
                      simpa only [Δsnd,
                        update_swap (f := «Δ») (x := snd!) (y := x!) (hxy := x_ne_snd.symm)
                          (vx := some (x_1 i1)) (vy := some Y),
                        update_swap (f := Function.update «Δ» x! (some Y)) (x := snd!) (y := fst!)
                          (hxy := fst_ne_snd.symm) (vx := some (x_1 i1)) (vy := some (x_1 i0))] using hsnd_some_xf
                    obtain ⟨Dfst, hDfst⟩ := Option.isSome_iff_exists.mp hfst_some_goal_ctx
                    obtain ⟨Dsnd, hDsnd⟩ := Option.isSome_iff_exists.mp hsnd_some_goal_ctx
                    have hDfst_raw :
                        ⟦fst!_spec.abstract
                          (Function.update (Function.update (Function.update «Δ» x! (some Y)) fst! (some (x_1 i0))) snd! (some (x_1 i1)))
                          (by
                            simpa only [Δfst, update_swap (f := «Δ») (x := fst!) (y := x!) (hxy := x_ne_fst.symm)
                              (vx := some (x_1 i0)) (vy := some Y)] using hφfst_xs)⟧ˢ = some Dfst := by
                      simpa [SMT.RenamingContext.denote] using hDfst
                    have hDsnd_raw :
                        ⟦snd!_spec.abstract
                          (Function.update (Function.update (Function.update «Δ» x! (some Y)) fst! (some (x_1 i0))) snd! (some (x_1 i1)))
                          (by
                            simpa only [Δsnd,
                              update_swap (f := «Δ») (x := snd!) (y := x!) (hxy := x_ne_snd.symm)
                                (vx := some (x_1 i1)) (vy := some Y),
                              update_swap (f := Function.update «Δ» x! (some Y)) (x := snd!) (y := fst!)
                                (hxy := fst_ne_snd.symm) (vx := some (x_1 i1)) (vy := some (x_1 i0))] using hφsnd_xf)⟧ˢ = some Dsnd := by
                      simpa [SMT.RenamingContext.denote] using hDsnd
                    have hDfst_ty : Dfst.2.1 = .bool := by
                      exact denote_type_eq_of_typing (typ_t := typ_fst!_spec_St₃) (hden := hDfst_raw)
                    have hDsnd_ty : Dsnd.2.1 = .bool := by
                      exact denote_type_eq_of_typing (typ_t := typ_snd!_spec_St₄) (hden := hDsnd_raw)
                    let Δgoal : SMT.RenamingContext.Context :=
                      Function.update (Function.update (Function.update «Δ» x! (some Y))
                        fst! (some (x_1 i0))) snd! (some (x_1 i1))
                    have hcov_x! : SMT.RenamingContext.CoversFV Δgoal (SMT.Term.var x!) := by
                      intro v hv
                      rw [SMT.fv, List.mem_singleton] at hv
                      subst hv
                      simp [Δgoal, Function.update, x_ne_fst, x_ne_snd]
                    have hcov_fst : SMT.RenamingContext.CoversFV Δgoal (SMT.Term.var fst!) := by
                      intro v hv
                      rw [SMT.fv, List.mem_singleton] at hv
                      subst hv
                      simp [Δgoal, Function.update, fst_ne_snd]
                    have hcov_snd : SMT.RenamingContext.CoversFV Δgoal (SMT.Term.var snd!) := by
                      intro v hv
                      rw [SMT.fv, List.mem_singleton] at hv
                      subst hv
                      simp only [Function.update_self, Option.isSome_some, Δgoal]
                    have hden_x! :
                        ⟦(SMT.Term.var x!).abstract Δgoal hcov_x!⟧ˢ = some Y := by
                      rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some_inj]
                      apply Option.get_of_eq_some
                      simp [Δgoal, Function.update, x_ne_fst, x_ne_snd]
                    have hden_fst :
                        ⟦(SMT.Term.var fst!).abstract Δgoal hcov_fst⟧ˢ = some (x_1 i0) := by
                      rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some_inj]
                      apply Option.get_of_eq_some
                      simp [Δgoal, Function.update, fst_ne_snd]
                    have hden_snd :
                        ⟦(SMT.Term.var snd!).abstract Δgoal hcov_snd⟧ˢ = some (x_1 i1) := by
                      rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some_inj]
                      apply Option.get_of_eq_some
                      simp only [Δgoal, Function.update_self]
                    obtain ⟨Dpair, hDpair_raw, hDpair_ty⟩ :=
                      denote_pair_some_of_some hden_fst hden_snd
                    have hDpair_ty' : Dpair.2.1 = α'.pair β' := by
                      simp only [hDpair_ty, hx0.1, hx1.1]
                    have hEq_ty : Y.2.1 = Dpair.2.1 := by
                      calc
                        Y.2.1 = α'.pair β' := hYβ
                        _ = Dpair.2.1 := hDpair_ty'.symm
                    have hcov_eq : SMT.RenamingContext.CoversFV Δgoal
                        (SMT.Term.var x! =ˢ SMT.Term.pair (SMT.Term.var fst!) (SMT.Term.var snd!)) := by
                      intro v hv
                      rw [SMT.fv.eq_def] at hv
                      rw [List.mem_append] at hv
                      rcases hv with hvx | hvpair
                      · rw [SMT.fv, List.mem_singleton] at hvx
                        subst hvx
                        simp [Δgoal, Function.update, x_ne_fst, x_ne_snd]
                      · have hvpair' :
                          v ∈ SMT.fv (SMT.Term.var fst!) ∨ v ∈ SMT.fv (SMT.Term.var snd!) := by
                          simpa [SMT.fv, List.mem_append] using hvpair
                        rcases hvpair' with hvfst | hvsnd
                        · exact hcov_fst _ hvfst
                        · exact hcov_snd _ hvsnd
                    have hden_eq_rhs :
                        ⟦(SMT.Term.pair (SMT.Term.var fst!) (SMT.Term.var snd!)).abstract Δgoal
                          (by
                            intro v hv
                            have hv' :
                                v ∈ SMT.fv (SMT.Term.var fst!) ∨ v ∈ SMT.fv (SMT.Term.var snd!) := by
                              simpa [SMT.fv, List.mem_append] using hv
                            rcases hv' with hvfst | hvsnd
                            · exact hcov_fst _ hvfst
                            · exact hcov_snd _ hvsnd)⟧ˢ = some Dpair := by
                      simpa only [SMT.Term.abstract, proof_irrel_heq] using hDpair_raw
                    obtain ⟨Deq, hDeq_raw, hDeq_ty⟩ :=
                      denote_eq_some_of_some
                        (h₁ := hden_x!)
                        (h₂ := hden_eq_rhs)
                        (hτ := hEq_ty)
                    obtain ⟨Dspec, hDspec_raw, hDspec_ty⟩ :=
                      denote_and_some_bool_of_some_bool hDfst_raw hDfst_ty hDsnd_raw hDsnd_ty
                    obtain ⟨Dbody, hDbody_raw, hDbody_ty⟩ :=
                      denote_and_some_bool_of_some_bool hDeq_raw hDeq_ty hDspec_raw hDspec_ty
                    have hDfst_raw_base :
                        ⟦fst!_spec.abstract (Function.update «Δ» fst! (some (x_1 i0))) hφfst0⟧ˢ = some Dfst := by
                      have hctx_x :
                          SMT.RenamingContext.denote (Function.update «Δ» fst! (some (x_1 i0))) fst!_spec hφfst0 =
                            SMT.RenamingContext.denote (Function.update Δfst x! (some Y)) fst!_spec hφfst_x := by
                        exact SMT.RenamingContext.denote_update_of_notMem
                          («Δ» := Δfst) (t := fst!_spec) (x := x!) (d := Y) (h := hφfst0)
                          hx_not_mem_fv_fstspec
                      have hctx_xs :
                          SMT.RenamingContext.denote (Function.update Δfst x! (some Y)) fst!_spec hφfst_x =
                            SMT.RenamingContext.denote
                              (Function.update (Function.update Δfst x! (some Y)) snd! (some (x_1 i1)))
                              fst!_spec hφfst_xs := by
                        exact SMT.RenamingContext.denote_update_of_notMem
                          («Δ» := Function.update Δfst x! (some Y)) (t := fst!_spec)
                          (x := snd!) (d := (x_1 i1)) (h := hφfst_x) hsnd_not_mem_fv_fstspec
                      have hctx_goal :
                          SMT.RenamingContext.denote
                            (Function.update (Function.update Δfst x! (some Y)) snd! (some (x_1 i1)))
                            fst!_spec hφfst_xs =
                            SMT.RenamingContext.denote
                              (Function.update (Function.update (Function.update «Δ» x! (some Y)) fst! (some (x_1 i0)))
                                snd! (some (x_1 i1)))
                              fst!_spec
                              (by
                                simpa only [Δfst,
                                  update_swap (f := «Δ») (x := fst!) (y := x!) (hxy := x_ne_fst.symm)
                                    (vx := some (x_1 i0)) (vy := some Y)] using hφfst_xs) := by
                        simp only [Δfst,
                          update_swap (f := «Δ») (x := fst!) (y := x!) (hxy := x_ne_fst.symm)
                            (vx := some (x_1 i0)) (vy := some Y)]
                      have hDfst_ctx :
                          SMT.RenamingContext.denote (Function.update «Δ» fst! (some (x_1 i0))) fst!_spec hφfst0 =
                            some Dfst := by
                        exact hctx_x.trans (hctx_xs.trans (hctx_goal.trans hDfst))
                      simpa only [SMT.RenamingContext.denote] using hDfst_ctx
                    have hDsnd_raw_base :
                        ⟦snd!_spec.abstract (Function.update «Δ» snd! (some (x_1 i1))) hφsnd1⟧ˢ = some Dsnd := by
                      have hctx_x :
                          SMT.RenamingContext.denote (Function.update «Δ» snd! (some (x_1 i1))) snd!_spec hφsnd1 =
                            SMT.RenamingContext.denote (Function.update Δsnd x! (some Y)) snd!_spec hφsnd_x := by
                        exact SMT.RenamingContext.denote_update_of_notMem
                          («Δ» := Δsnd) (t := snd!_spec) (x := x!) (d := Y) (h := hφsnd1)
                          hx_not_mem_fv_sndspec
                      have hctx_xf :
                          SMT.RenamingContext.denote (Function.update Δsnd x! (some Y)) snd!_spec hφsnd_x =
                            SMT.RenamingContext.denote
                              (Function.update (Function.update Δsnd x! (some Y)) fst! (some (x_1 i0)))
                              snd!_spec hφsnd_xf := by
                        exact SMT.RenamingContext.denote_update_of_notMem
                          («Δ» := Function.update Δsnd x! (some Y)) (t := snd!_spec)
                          (x := fst!) (d := (x_1 i0)) (h := hφsnd_x) hfst_not_mem_fv_sndspec
                      have hctx_goal :
                          SMT.RenamingContext.denote
                            (Function.update (Function.update Δsnd x! (some Y)) fst! (some (x_1 i0)))
                            snd!_spec hφsnd_xf =
                            SMT.RenamingContext.denote
                              (Function.update (Function.update (Function.update «Δ» x! (some Y)) fst! (some (x_1 i0)))
                                snd! (some (x_1 i1)))
                              snd!_spec
                              (by
                                simpa only [Δsnd,
                                  update_swap (f := «Δ») (x := snd!) (y := x!) (hxy := x_ne_snd.symm)
                                    (vx := some (x_1 i1)) (vy := some Y),
                                  update_swap (f := Function.update «Δ» x! (some Y)) (x := snd!) (y := fst!)
                                    (hxy := fst_ne_snd.symm) (vx := some (x_1 i1)) (vy := some (x_1 i0))] using hφsnd_xf) := by
                        simp only [Δsnd,
                          update_swap (f := «Δ») (x := snd!) (y := x!) (hxy := x_ne_snd.symm)
                            (vx := some (x_1 i1)) (vy := some Y),
                          update_swap (f := Function.update «Δ» x! (some Y)) (x := snd!) (y := fst!)
                            (hxy := fst_ne_snd.symm) (vx := some (x_1 i1)) (vy := some (x_1 i0))]
                      have hDsnd_ctx :
                          SMT.RenamingContext.denote (Function.update «Δ» snd! (some (x_1 i1))) snd!_spec hφsnd1 =
                            some Dsnd := by
                        exact hctx_x.trans (hctx_xf.trans (hctx_goal.trans hDsnd))
                      simpa only [SMT.RenamingContext.denote] using hDsnd_ctx
                    have hx1i0_val : (x_1 i0).fst = a := by
                      simp [x_1, i0, i1]
                    have hx1i1_val : (x_1 i1).fst = b := by
                      simp [x_1, i1]
                    have hDpair_eq_x1 :
                        Dpair.fst = (x_1 i0).fst.pair (x_1 i1).fst := by
                      have hDpair_raw_x1 :
                          ⟦((SMT.Term.var fst!).abstract Δgoal hcov_fst).pair
                              ((SMT.Term.var snd!).abstract Δgoal hcov_snd)⟧ˢ =
                            some ⟨(x_1 i0).fst.pair (x_1 i1).fst, (x_1 i0).snd.fst.pair (x_1 i1).snd.fst,
                              by
                                rw [ZFSet.pair_mem_prod]
                                exact ⟨hx0.2, hx1.2⟩⟩ := by
                        rw [SMT.denote, hden_fst, hden_snd]
                        rw [Option.pure_def, Option.bind_eq_bind, Option.bind_some]
                        rfl
                      have hEq : some Dpair =
                          some ⟨(x_1 i0).fst.pair (x_1 i1).fst, (x_1 i0).snd.fst.pair (x_1 i1).snd.fst,
                            by
                              rw [ZFSet.pair_mem_prod]
                              exact ⟨hx0.2, hx1.2⟩⟩ := by
                        exact hDpair_raw.symm.trans hDpair_raw_x1
                      exact congrArg (fun d : SMT.Dom => d.fst) (Option.some.inj hEq)
                    have hDpair_eq_ab : Dpair.fst = a.pair b := by
                      rw [hDpair_eq_x1, hx1i0_val, hx1i1_val]
                    by_cases hYeq : Y.fst = a.pair b
                    · have hDeq_true : Deq.fst = zftrue := by
                        have hYeq_Dpair : Y.fst = Dpair.fst := by
                          rw [hDpair_eq_ab]
                          exact hYeq
                        have hDeq_raw_true :
                            ⟦(SMT.Term.var x!).abstract Δgoal hcov_x! =ˢ'
                                (SMT.Term.pair (SMT.Term.var fst!) (SMT.Term.var snd!)).abstract Δgoal
                                  (by
                                    intro v hv
                                    have hv' :
                                        v ∈ SMT.fv (SMT.Term.var fst!) ∨ v ∈ SMT.fv (SMT.Term.var snd!) := by
                                      simpa [SMT.fv, List.mem_append] using hv
                                    rcases hv' with hvfst | hvsnd
                                    · exact hcov_fst _ hvfst
                                    · exact hcov_snd _ hvsnd)⟧ˢ =
                              some ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
                          exact denote_eq_eq_zftrue_of_fst_eq hden_x! hden_eq_rhs hEq_ty hYeq_Dpair
                        have hEq :
                            some Deq = some ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
                          exact hDeq_raw.symm.trans hDeq_raw_true
                        exact congrArg (fun d : SMT.Dom => d.fst) (Option.some.inj hEq)
                      have hDfst_mem_bool : Dfst.fst ∈ 𝔹 := by
                        simpa [hDfst_ty] using Dfst.snd.snd
                      have hDfst_bool : Dfst.fst = zftrue ∨ Dfst.fst = zffalse := by
                        simpa [ZFSet.ZFBool.mem_𝔹_iff, or_comm] using hDfst_mem_bool
                      have hDsnd_mem_bool : Dsnd.fst ∈ 𝔹 := by
                        simpa [hDsnd_ty] using Dsnd.snd.snd
                      have hDsnd_bool : Dsnd.fst = zftrue ∨ Dsnd.fst = zffalse := by
                        simpa [ZFSet.ZFBool.mem_𝔹_iff, or_comm] using hDsnd_mem_bool
                      have hDspec_false_raw :
                          ⟦fst!_spec.abstract
                              (Function.update (Function.update (Function.update «Δ» x! (some Y)) fst! (some (x_1 i0))) snd! (some (x_1 i1)))
                              (by
                                simpa only [Δfst, update_swap (f := «Δ») (x := fst!) (y := x!) (hxy := x_ne_fst.symm)
                                  (vx := some (x_1 i0)) (vy := some Y)] using hφfst_xs) ∧ˢ'
                            snd!_spec.abstract
                              (Function.update (Function.update (Function.update «Δ» x! (some Y)) fst! (some (x_1 i0))) snd! (some (x_1 i1)))
                              (by
                                simpa only [Δsnd,
                                  update_swap (f := «Δ») (x := snd!) (y := x!) (hxy := x_ne_snd.symm)
                                    (vx := some (x_1 i1)) (vy := some Y),
                                  update_swap (f := Function.update «Δ» x! (some Y)) (x := snd!) (y := fst!)
                                    (hxy := fst_ne_snd.symm) (vx := some (x_1 i1)) (vy := some (x_1 i0))] using hφsnd_xf)⟧ˢ =
                            some ⟨zffalse, SMTType.bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
                        rcases hDfst_bool with hDfst_true | hDfst_false
                        · rcases hDsnd_bool with hDsnd_true | hDsnd_false
                          · exfalso
                            have hcast_fst_raw :
                                X₁.pair (x_1 i0).fst ∈ (castZF_of_path pα).1 := by
                              exact (hfst_total (x_1 i0) hx0.1 hφfst0).2 hDfst_raw_base hDfst_true
                            have hcast_fst :
                                X₁.pair a ∈ (castZF_of_path pα).1 := by
                              simpa [hx1i0_val] using hcast_fst_raw
                            have hcast_snd_raw :
                                X₂.pair (x_1 i1).fst ∈ (castZF_of_path pβ).1 := by
                              exact (hsnd_total (x_1 i1) hx1.1 hφsnd1).2 hDsnd_raw_base hDsnd_true
                            have hcast_snd :
                                X₂.pair b ∈ (castZF_of_path pβ).1 := by
                              simpa [hx1i1_val] using hcast_snd_raw
                            have hmem_fprod :
                                (X₁.pair X₂).pair (a.pair b) ∈
                                  fprod ↑(castZF_of_path pα) ↑(castZF_of_path pβ)
                                    (castZF_of_path pα).2 (castZF_of_path pβ).2 := by
                              rw [ZFSet.pair_mem_fprod (hf := (castZF_of_path pα).2) (hg := (castZF_of_path pβ).2)]
                              refine ⟨X₁, X₂, hX₁, hX₂, rfl, ?_⟩
                              have hcastα_pfunc :
                                  ((castZF_of_path pα).1).IsPFunc ⟦α⟧ᶻ ⟦α'⟧ᶻ :=
                                ZFSet.is_func_is_pfunc (f := (castZF_of_path pα).1) (castZF_of_path pα).2
                              have hfst_val :
                                  a =
                                    (@ᶻ(castZF_of_path pα).1
                                      ⟨X₁, by
                                        rw [ZFSet.is_func_dom_eq (castZF_of_path pα).2]
                                        exact hX₁⟩) := by
                                symm
                                exact congrArg Subtype.val (fapply.of_pair (hf := hcastα_pfunc) hcast_fst)
                              have hcastβ_pfunc :
                                  ((castZF_of_path pβ).1).IsPFunc ⟦β⟧ᶻ ⟦β'⟧ᶻ :=
                                ZFSet.is_func_is_pfunc (f := (castZF_of_path pβ).1) (castZF_of_path pβ).2
                              have hsnd_val :
                                  b =
                                    (@ᶻ(castZF_of_path pβ).1
                                      ⟨X₂, by
                                        rw [ZFSet.is_func_dom_eq (castZF_of_path pβ).2]
                                        exact hX₂⟩) := by
                                symm
                                exact congrArg Subtype.val (fapply.of_pair (hf := hcastβ_pfunc) hcast_snd)
                              rw [hfst_val, hsnd_val]
                            have hpair_mem :
                                (X₁.pair X₂).pair Y.fst ∈ (castZF_of_path (pα.pair pβ)).1 := by
                              rw [hYeq]
                              simpa [castZF_of_path, castZF_pair] using hmem_fprod
                            exact hnotmem hpair_mem
                          · exact denote_and_eq_zffalse_of_some_zffalse_right
                              hDfst_raw hDfst_ty hDsnd_raw hDsnd_ty hDsnd_false
                        · exact denote_and_eq_zffalse_of_some_zffalse_left
                            hDfst_raw hDfst_ty hDfst_false hDsnd_raw hDsnd_ty
                      have hDspec_false : Dspec.fst = zffalse := by
                        have hEq :
                            Dspec = ⟨zffalse, SMTType.bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
                          exact Option.some.inj (hDspec_raw.symm.trans hDspec_false_raw)
                        exact congrArg (fun d : SMT.Dom => d.fst) hEq
                      have hDbody_false_raw :
                          ⟦((SMT.Term.var x!).abstract Δgoal hcov_x! =ˢ'
                              (SMT.Term.pair (SMT.Term.var fst!) (SMT.Term.var snd!)).abstract Δgoal
                                (by
                                  intro v hv
                                  have hv' :
                                      v ∈ SMT.fv (SMT.Term.var fst!) ∨ v ∈ SMT.fv (SMT.Term.var snd!) := by
                                    simpa [SMT.fv, List.mem_append] using hv
                                  rcases hv' with hvfst | hvsnd
                                  · exact hcov_fst _ hvfst
                                  · exact hcov_snd _ hvsnd)) ∧ˢ'
                            (fst!_spec.abstract
                                (Function.update (Function.update (Function.update «Δ» x! (some Y)) fst! (some (x_1 i0))) snd! (some (x_1 i1)))
                                (by
                                  simpa only [Δfst, update_swap (f := «Δ») (x := fst!) (y := x!) (hxy := x_ne_fst.symm)
                                    (vx := some (x_1 i0)) (vy := some Y)] using hφfst_xs) ∧ˢ'
                              snd!_spec.abstract
                                (Function.update (Function.update (Function.update «Δ» x! (some Y)) fst! (some (x_1 i0))) snd! (some (x_1 i1)))
                                (by
                                  simpa only [Δsnd,
                                    update_swap (f := «Δ») (x := snd!) (y := x!) (hxy := x_ne_snd.symm)
                                      (vx := some (x_1 i1)) (vy := some Y),
                                    update_swap (f := Function.update «Δ» x! (some Y)) (x := snd!) (y := fst!)
                                      (hxy := fst_ne_snd.symm) (vx := some (x_1 i1)) (vy := some (x_1 i0))] using hφsnd_xf))⟧ˢ =
                            some ⟨zffalse, SMTType.bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
                        exact denote_and_eq_zffalse_of_some_zffalse_right
                          hDeq_raw hDeq_ty hDspec_raw hDspec_ty hDspec_false
                      have hDbody_false : Dbody.fst = zffalse := by
                        have hEq :
                            Dbody = ⟨zffalse, SMTType.bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
                          exact Option.some.inj (hDbody_raw.symm.trans hDbody_false_raw)
                        exact congrArg (fun d : SMT.Dom => d.fst) hEq
                      have hnot_raw :
                          ⟦¬ˢ'
                              (((SMT.Term.var x!).abstract Δgoal hcov_x! =ˢ'
                                (SMT.Term.pair (SMT.Term.var fst!) (SMT.Term.var snd!)).abstract Δgoal
                                  (by
                                    intro v hv
                                    have hv' :
                                        v ∈ SMT.fv (SMT.Term.var fst!) ∨ v ∈ SMT.fv (SMT.Term.var snd!) := by
                                      simpa [SMT.fv, List.mem_append] using hv
                                    rcases hv' with hvfst | hvsnd
                                    · exact hcov_fst _ hvfst
                                    · exact hcov_snd _ hvsnd)) ∧ˢ'
                                (fst!_spec.abstract
                                    (Function.update (Function.update (Function.update «Δ» x! (some Y)) fst! (some (x_1 i0))) snd! (some (x_1 i1)))
                                    (by
                                      simpa only [Δfst, update_swap (f := «Δ») (x := fst!) (y := x!) (hxy := x_ne_fst.symm)
                                        (vx := some (x_1 i0)) (vy := some Y)] using hφfst_xs) ∧ˢ'
                                  snd!_spec.abstract
                                    (Function.update (Function.update (Function.update «Δ» x! (some Y)) fst! (some (x_1 i0))) snd! (some (x_1 i1)))
                                    (by
                                      simpa only [Δsnd,
                                        update_swap (f := «Δ») (x := snd!) (y := x!) (hxy := x_ne_snd.symm)
                                          (vx := some (x_1 i1)) (vy := some Y),
                                        update_swap (f := Function.update «Δ» x! (some Y)) (x := snd!) (y := fst!)
                                          (hxy := fst_ne_snd.symm) (vx := some (x_1 i1)) (vy := some (x_1 i0))] using hφsnd_xf)))⟧ˢ =
                            some ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
                        exact denote_not_eq_zftrue_of_some_zffalse hDbody_raw hDbody_ty hDbody_false
                      have hnot_get :
                          zftrue =
                            (⟦¬ˢ'
                                (((SMT.Term.var x!).abstract Δgoal hcov_x! =ˢ'
                                  (SMT.Term.pair (SMT.Term.var fst!) (SMT.Term.var snd!)).abstract Δgoal
                                    (by
                                      intro v hv
                                      have hv' :
                                          v ∈ SMT.fv (SMT.Term.var fst!) ∨ v ∈ SMT.fv (SMT.Term.var snd!) := by
                                        simpa [SMT.fv, List.mem_append] using hv
                                      rcases hv' with hvfst | hvsnd
                                      · exact hcov_fst _ hvfst
                                      · exact hcov_snd _ hvsnd)) ∧ˢ'
                                  (fst!_spec.abstract
                                      (Function.update (Function.update (Function.update «Δ» x! (some Y)) fst! (some (x_1 i0))) snd! (some (x_1 i1)))
                                      (by
                                        simpa only [Δfst, update_swap (f := «Δ») (x := fst!) (y := x!) (hxy := x_ne_fst.symm)
                                          (vx := some (x_1 i0)) (vy := some Y)] using hφfst_xs) ∧ˢ'
                                    snd!_spec.abstract
                                      (Function.update (Function.update (Function.update «Δ» x! (some Y)) fst! (some (x_1 i0))) snd! (some (x_1 i1)))
                                      (by
                                        simpa only [Δsnd,
                                          update_swap (f := «Δ») (x := snd!) (y := x!) (hxy := x_ne_snd.symm)
                                            (vx := some (x_1 i1)) (vy := some Y),
                                          update_swap (f := Function.update «Δ» x! (some Y)) (x := snd!) (y := fst!)
                                            (hxy := fst_ne_snd.symm) (vx := some (x_1 i1)) (vy := some (x_1 i0))] using hφsnd_xf)))⟧ˢ.get
                              (denote_not_isSome_of_some_bool hDbody_raw hDbody_ty)).fst := by
                        conv_rhs =>
                          enter [1, 1]
                          rw [hnot_raw]
                        rw [Option.get_some]
                      calc
                        bodyF (a.pair b) =
                            (⟦¬ˢ'
                                (Term.abstract.go
                                  ((SMT.Term.var x! =ˢ SMT.Term.pair (SMT.Term.var fst!) (SMT.Term.var snd!)) ∧ˢ
                                    (fst!_spec ∧ˢ snd!_spec))
                                  [fst!, snd!]
                                  (Function.update «Δ» x! (some Y))
                                  hΔ_body).uncurry x_1⟧ˢ.get
                              (den_t_isSome hx_1)).fst := hbodyF_y
                        _ = zftrue := by
                          simpa [SMT.Term.abstract, SMT.denote, SMT.Term.abstract.go,
                            Function.OfArity.uncurry, Function.FromTypes.uncurry, Δgoal, i0, i1, x_1, hx_1,
                            proof_irrel_heq] using hnot_get.symm
                    · have hDeq_false : Deq.fst = zffalse := by
                        have hDeq_mem_bool : Deq.fst ∈ 𝔹 := by
                          simpa [hDeq_ty] using Deq.snd.snd
                        have hDeq_bool : Deq.fst = zftrue ∨ Deq.fst = zffalse := by
                          simpa [ZFSet.ZFBool.mem_𝔹_iff, or_comm] using hDeq_mem_bool
                        rcases hDeq_bool with hDeq_true | hDeq_false
                        · exfalso
                          have hYeq_ab : Y.fst = a.pair b := by
                            calc
                              Y.fst = Dpair.fst :=
                                denote_eq_true_implies_fst_eq hden_x! hden_eq_rhs hEq_ty hDeq_raw hDeq_true
                              _ = a.pair b := hDpair_eq_ab
                          exact hYeq hYeq_ab
                        · exact hDeq_false
                      have hDbody_false_raw :
                          ⟦((SMT.Term.var x!).abstract Δgoal hcov_x! =ˢ'
                              (SMT.Term.pair (SMT.Term.var fst!) (SMT.Term.var snd!)).abstract Δgoal
                                (by
                                  intro v hv
                                  have hv' :
                                      v ∈ SMT.fv (SMT.Term.var fst!) ∨ v ∈ SMT.fv (SMT.Term.var snd!) := by
                                    simpa [SMT.fv, List.mem_append] using hv
                                  rcases hv' with hvfst | hvsnd
                                  · exact hcov_fst _ hvfst
                                  · exact hcov_snd _ hvsnd)) ∧ˢ'
                            (fst!_spec.abstract
                                (Function.update (Function.update (Function.update «Δ» x! (some Y)) fst! (some (x_1 i0))) snd! (some (x_1 i1)))
                                (by
                                  simpa only [Δfst, update_swap (f := «Δ») (x := fst!) (y := x!) (hxy := x_ne_fst.symm)
                                    (vx := some (x_1 i0)) (vy := some Y)] using hφfst_xs) ∧ˢ'
                              snd!_spec.abstract
                                (Function.update (Function.update (Function.update «Δ» x! (some Y)) fst! (some (x_1 i0))) snd! (some (x_1 i1)))
                                (by
                                  simpa only [Δsnd,
                                    update_swap (f := «Δ») (x := snd!) (y := x!) (hxy := x_ne_snd.symm)
                                      (vx := some (x_1 i1)) (vy := some Y),
                                    update_swap (f := Function.update «Δ» x! (some Y)) (x := snd!) (y := fst!)
                                      (hxy := fst_ne_snd.symm) (vx := some (x_1 i1)) (vy := some (x_1 i0))] using hφsnd_xf))⟧ˢ =
                            some ⟨zffalse, SMTType.bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
                        exact denote_and_eq_zffalse_of_some_zffalse_left
                          hDeq_raw hDeq_ty hDeq_false hDspec_raw hDspec_ty
                      have hDbody_false : Dbody.fst = zffalse := by
                        have hEq :
                            Dbody = ⟨zffalse, SMTType.bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
                          exact Option.some.inj (hDbody_raw.symm.trans hDbody_false_raw)
                        exact congrArg (fun d : SMT.Dom => d.fst) hEq
                      have hnot_raw :
                          ⟦¬ˢ'
                              (((SMT.Term.var x!).abstract Δgoal hcov_x! =ˢ'
                                (SMT.Term.pair (SMT.Term.var fst!) (SMT.Term.var snd!)).abstract Δgoal
                                  (by
                                    intro v hv
                                    have hv' :
                                        v ∈ SMT.fv (SMT.Term.var fst!) ∨ v ∈ SMT.fv (SMT.Term.var snd!) := by
                                      simpa [SMT.fv, List.mem_append] using hv
                                    rcases hv' with hvfst | hvsnd
                                    · exact hcov_fst _ hvfst
                                    · exact hcov_snd _ hvsnd)) ∧ˢ'
                                (fst!_spec.abstract
                                    (Function.update (Function.update (Function.update «Δ» x! (some Y)) fst! (some (x_1 i0))) snd! (some (x_1 i1)))
                                    (by
                                      simpa only [Δfst, update_swap (f := «Δ») (x := fst!) (y := x!) (hxy := x_ne_fst.symm)
                                        (vx := some (x_1 i0)) (vy := some Y)] using hφfst_xs) ∧ˢ'
                                  snd!_spec.abstract
                                    (Function.update (Function.update (Function.update «Δ» x! (some Y)) fst! (some (x_1 i0))) snd! (some (x_1 i1)))
                                    (by
                                      simpa only [Δsnd,
                                        update_swap (f := «Δ») (x := snd!) (y := x!) (hxy := x_ne_snd.symm)
                                          (vx := some (x_1 i1)) (vy := some Y),
                                        update_swap (f := Function.update «Δ» x! (some Y)) (x := snd!) (y := fst!)
                                          (hxy := fst_ne_snd.symm) (vx := some (x_1 i1)) (vy := some (x_1 i0))] using hφsnd_xf)))⟧ˢ =
                            some ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
                        exact denote_not_eq_zftrue_of_some_zffalse hDbody_raw hDbody_ty hDbody_false
                      have hnot_get :
                          zftrue =
                            (⟦¬ˢ'
                                (((SMT.Term.var x!).abstract Δgoal hcov_x! =ˢ'
                                  (SMT.Term.pair (SMT.Term.var fst!) (SMT.Term.var snd!)).abstract Δgoal
                                    (by
                                      intro v hv
                                      have hv' :
                                          v ∈ SMT.fv (SMT.Term.var fst!) ∨ v ∈ SMT.fv (SMT.Term.var snd!) := by
                                        simpa [SMT.fv, List.mem_append] using hv
                                      rcases hv' with hvfst | hvsnd
                                      · exact hcov_fst _ hvfst
                                      · exact hcov_snd _ hvsnd)) ∧ˢ'
                                  (fst!_spec.abstract
                                      (Function.update (Function.update (Function.update «Δ» x! (some Y)) fst! (some (x_1 i0))) snd! (some (x_1 i1)))
                                      (by
                                        simpa only [Δfst, update_swap (f := «Δ») (x := fst!) (y := x!) (hxy := x_ne_fst.symm)
                                          (vx := some (x_1 i0)) (vy := some Y)] using hφfst_xs) ∧ˢ'
                                    snd!_spec.abstract
                                      (Function.update (Function.update (Function.update «Δ» x! (some Y)) fst! (some (x_1 i0))) snd! (some (x_1 i1)))
                                      (by
                                        simpa only [Δsnd,
                                          update_swap (f := «Δ») (x := snd!) (y := x!) (hxy := x_ne_snd.symm)
                                            (vx := some (x_1 i1)) (vy := some Y),
                                          update_swap (f := Function.update «Δ» x! (some Y)) (x := snd!) (y := fst!)
                                            (hxy := fst_ne_snd.symm) (vx := some (x_1 i1)) (vy := some (x_1 i0))] using hφsnd_xf)))⟧ˢ.get
                              (denote_not_isSome_of_some_bool hDbody_raw hDbody_ty)).fst := by
                        conv_rhs =>
                          enter [1, 1]
                          rw [hnot_raw]
                        rw [Option.get_some]
                      calc
                        bodyF (a.pair b) =
                            (⟦¬ˢ'
                                (Term.abstract.go
                                  ((SMT.Term.var x! =ˢ SMT.Term.pair (SMT.Term.var fst!) (SMT.Term.var snd!)) ∧ˢ
                                    (fst!_spec ∧ˢ snd!_spec))
                                  [fst!, snd!]
                                  (Function.update «Δ» x! (some Y))
                                  hΔ_body).uncurry x_1⟧ˢ.get
                              (den_t_isSome hx_1)).fst := hbodyF_y
                        _ = zftrue := by
                          simpa [SMT.Term.abstract, SMT.denote, SMT.Term.abstract.go,
                            Function.OfArity.uncurry, Function.FromTypes.uncurry, Δgoal, i0, i1, x_1, hx_1,
                            proof_irrel_heq] using hnot_get.symm
                  have hne :
                      ∃ y, y ∈ D := by
                    refine ⟨Xfst!.fst.pair Xsnd!.fst, ?_⟩
                    simpa [D, pair_mem_prod] using And.intro hXfst!_memα' hXsnd!_memβ'
                  have houter_false :
                      overloadUnaryOp id id ZFBool.false ZFBool.not
                        (⋂₀ ZFSet.sep
                          (fun y => ∃ x ∈ D, y = bodyF x)
                          𝔹) = zffalse := by
                    have hsInter_mem :
                        (⋂₀ ZFSet.sep
                          (fun y => ∃ x ∈ D, y = bodyF x)
                          𝔹) ∈ 𝔹 :=
                      ZFSet.sInter_sep_subset_of_𝔹_mem_𝔹 (fun _ => id)
                    simpa [overloadUnaryOp, hsInter_mem, id_eq, proof_irrel_heq] using
                      not_sInter_sep_eq_zffalse_of_forall_eq_zftrue hne hall
                  have hExistsTrue_body :
                      overloadUnaryOp id id ZFBool.false ZFBool.not
                        (⋂₀ ZFSet.sep
                          (fun y => ∃ x ∈ D, y = bodyF x)
                          𝔹) = zftrue := by
                    simpa only [D, bodyF, Fin.foldl_succ, Fin.foldl_zero, List.length_cons,
                      List.length_nil, Nat.reduceAdd, Function.OfArity.uncurry,
                      Function.FromTypes.uncurry, ZFSet.get, Fin.forall_fin_two, Fin.isValue,
                      Fin.reduceLast, Fin.coe_ofNat_eq_mod, Fin.zero_eq_one_iff,
                      Nat.succ_ne_self, zero_add, ↓reduceIte, dite_eq_ite] using hExistsTrue
                  have hz : zftrue = zffalse := hExistsTrue_body.symm.trans houter_false
                  exact ZFSet.zftrue_ne_zffalse hz
                exact hcontra
            · exfalso
              apply den_t_isSome
              intro x_1 hx_1
              simp only [denote, List.length_cons, List.length_nil, Nat.reduceAdd, overloadUnaryOp,
                id_eq, Option.pure_def, Option.failure_eq_none, Option.bind_eq_bind]
              unfold SMT.Term.abstract.go
              simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
                Matrix.head_fin_const]
              let i0 : Fin [fst!, snd!].length := ⟨0, hlen_pos⟩
              let i1 : Fin [fst!, snd!].length := ⟨1, Nat.one_lt_succ_succ 0⟩
              have hx0 : (x_1 i0).2.1 = α' ∧ (x_1 i0).1 ∈ ⟦α'⟧ᶻ := by
                simpa [i0] using hx_1 i0
              have hx1 : (x_1 i1).2.1 = β' ∧ (x_1 i1).1 ∈ ⟦β'⟧ᶻ := by
                simpa [i1] using hx_1 i1
              have hφfst0 :
                  SMT.RenamingContext.CoversFV (Function.update «Δ» fst! (some (x_1 i0))) fst!_spec := by
                intro v hv
                by_cases hvf : v = fst!
                · subst hvf
                  simp
                · have hv' := hφfst v hv
                  simpa [Function.update_of_ne hvf] using hv'
              have hφsnd1 :
                  SMT.RenamingContext.CoversFV (Function.update «Δ» snd! (some (x_1 i1))) snd!_spec := by
                intro v hv
                by_cases hvs : v = snd!
                · subst hvs
                  simp
                · have hv' := hφsnd v hv
                  simpa [Function.update_of_ne hvs] using hv'
              have hfst_some := (hfst_total (x_1 i0) hx0.1 hφfst0).1
              have hsnd_some := (hsnd_total (x_1 i1) hx1.1 hφsnd1).1
              have hx_lookup_St₂ : St₂.types.lookup x! = some (.pair α' β') := by
                rw [St₂_types_eq]
                exact AList.lookup_insert St₁.types
              have hx_mem_St₂ : x! ∈ St₂.types := by
                exact (AList.lookup_isSome).1 (Option.isSome_of_eq_some hx_lookup_St₂)
              have hx_entry_St₂ : ⟨x!, .pair α' β'⟩ ∈ St₂.types.entries :=
                (AList.mem_lookup_iff).1 hx_lookup_St₂
              have hx_entry_insfst : ⟨x!, .pair α' β'⟩ ∈ (AList.insert fst! α' St₂.types).entries :=
                SMT.TypeContext.entries_subset_insert_of_notMem fst!_fresh hx_entry_St₂
              have hx_entry_St₃ : ⟨x!, .pair α' β'⟩ ∈ St₃.types.entries := St₃_types_eq hx_entry_insfst
              have hx_lookup_St₃ : St₃.types.lookup x! = some (.pair α' β') :=
                (AList.mem_lookup_iff).2 hx_entry_St₃
              have hx_mem_St₃ : x! ∈ St₃.types := by
                exact (AList.lookup_isSome).1 (Option.isSome_of_eq_some hx_lookup_St₃)
              have x_ne_fst : x! ≠ fst! := by
                intro hxf
                have hfst_mem_St₂ : fst! ∈ St₂.types := by
                  simpa [hxf] using hx_mem_St₂
                exact fst!_fresh hfst_mem_St₂
              have x_ne_snd : x! ≠ snd! := by
                intro hxs
                have hsnd_mem_St₃ : snd! ∈ St₃.types := by
                  simpa [hxs] using hx_mem_St₃
                exact snd!_fresh hsnd_mem_St₃
              have hfst_lookup_ins : (AList.insert fst! α' St₂.types).lookup fst! = some α' :=
                AList.lookup_insert St₂.types
              have hfst_entry_ins : ⟨fst!, α'⟩ ∈ (AList.insert fst! α' St₂.types).entries :=
                (AList.mem_lookup_iff).1 hfst_lookup_ins
              have hfst_entry_St₃ : ⟨fst!, α'⟩ ∈ St₃.types.entries := St₃_types_eq hfst_entry_ins
              have hfst_lookup_St₃ : St₃.types.lookup fst! = some α' :=
                (AList.mem_lookup_iff).2 hfst_entry_St₃
              have hfst_mem_St₃ : fst! ∈ St₃.types := by
                exact (AList.lookup_isSome).1 (Option.isSome_of_eq_some hfst_lookup_St₃)
              have fst_ne_snd : fst! ≠ snd! := by
                intro hfs
                have hsnd_mem_St₃ : snd! ∈ St₃.types := by
                  simpa [hfs] using hfst_mem_St₃
                exact snd!_fresh hsnd_mem_St₃
              have hfst_not_mem_fv_x : fst! ∉ SMT.fv x := by
                intro hfst_fv_x
                have hfst_mem_St₂' : fst! ∈ St₂.types :=
                  SMT.Typing.mem_context_of_mem_fv typ_x_St₂ hfst_fv_x
                exact fst!_fresh hfst_mem_St₂'
              have hx_not_mem_fv_fstspec : x! ∉ SMT.fv fst!_spec := by
                intro hx_fstspec
                have hx' := fv_fst!_spec hx_fstspec
                rw [List.mem_union_iff] at hx'
                rcases hx' with hx_in_fv_fstx | hx_eq_fst
                · have hx_in_fv_x : x! ∈ SMT.fv x := by
                    simpa [SMT.fv] using hx_in_fv_fstx
                  exact x!_not_mem_fv_x hx_in_fv_x
                · exact x_ne_fst (List.mem_singleton.mp hx_eq_fst)
              have hsnd_not_mem_fv_fstspec : snd! ∉ SMT.fv fst!_spec := by
                intro hsnd_fstspec
                have hsnd_mem_St₃ : snd! ∈ St₃.types :=
                  SMT.Typing.mem_context_of_mem_fv typ_fst!_spec_St₃ hsnd_fstspec
                exact snd!_fresh hsnd_mem_St₃
              have hx_not_mem_fv_sndspec : x! ∉ SMT.fv snd!_spec := by
                intro hx_sndspec
                have hx' := fv_snd!_spec hx_sndspec
                rw [List.mem_union_iff] at hx'
                rcases hx' with hx_in_fv_sndx | hx_eq_snd
                · have hx_in_fv_x : x! ∈ SMT.fv x := by
                    simpa [SMT.fv] using hx_in_fv_sndx
                  exact x!_not_mem_fv_x hx_in_fv_x
                · exact x_ne_snd (List.mem_singleton.mp hx_eq_snd)
              have hfst_not_mem_fv_sndspec : fst! ∉ SMT.fv snd!_spec := by
                intro hfst_sndspec
                have hfst' := fv_snd!_spec hfst_sndspec
                rw [List.mem_union_iff] at hfst'
                rcases hfst' with hfst_in_fv_sndx | hfst_eq_snd
                · have hfst_in_fv_x : fst! ∈ SMT.fv x := by
                    simpa [SMT.fv] using hfst_in_fv_sndx
                  exact hfst_not_mem_fv_x hfst_in_fv_x
                · exact fst_ne_snd (List.mem_singleton.mp hfst_eq_snd)
              set Δfst : SMT.RenamingContext.Context := Function.update «Δ» fst! (some (x_1 i0))
              set Δsnd : SMT.RenamingContext.Context := Function.update «Δ» snd! (some (x_1 i1))
              have hφfst_x : SMT.RenamingContext.CoversFV (Function.update Δfst x! (some Y)) fst!_spec :=
                SMT.RenamingContext.coversFV_update_of_notMem
                  (x := x!) (d := Y) hx_not_mem_fv_fstspec hφfst0
              have hφfst_xs :
                  SMT.RenamingContext.CoversFV
                    (Function.update (Function.update Δfst x! (some Y)) snd! (some (x_1 i1))) fst!_spec :=
                SMT.RenamingContext.coversFV_update_of_notMem
                  (x := snd!) (d := (x_1 i1)) hsnd_not_mem_fv_fstspec hφfst_x
              have hfst_some_goal_ctx :
                  (SMT.RenamingContext.denote
                    (Function.update (Function.update (Function.update «Δ» x! (some Y)) fst! (some (x_1 i0))) snd! (some (x_1 i1)))
                    fst!_spec
                    (by
                      simpa only [Δfst, update_swap (f := «Δ») (x := fst!) (y := x!) (hxy := x_ne_fst.symm)
                        (vx := some (x_1 i0)) (vy := some Y)] using hφfst_xs)).isSome = true := by
                have hfst_some_x :
                    (SMT.RenamingContext.denote
                      (Function.update Δfst x! (some Y))
                      fst!_spec hφfst_x).isSome = true := by
                  rw [← denote_isSome_update_of_notMem
                    («Δ» := Δfst) (t := fst!_spec) (x := x!) (d := Y) (h := hφfst0)
                    hx_not_mem_fv_fstspec]
                  simpa only [Δfst] using hfst_some
                have hfst_some_xs :
                    (SMT.RenamingContext.denote
                      (Function.update (Function.update Δfst x! (some Y)) snd! (some (x_1 i1)))
                      fst!_spec hφfst_xs).isSome = true := by
                  rw [← denote_isSome_update_of_notMem
                    («Δ» := Function.update Δfst x! (some Y)) (t := fst!_spec)
                    (x := snd!) (d := (x_1 i1)) (h := hφfst_x) hsnd_not_mem_fv_fstspec]
                  exact hfst_some_x
                simpa only [Δfst, update_swap (f := «Δ») (x := fst!) (y := x!) (hxy := x_ne_fst.symm)
                  (vx := some (x_1 i0)) (vy := some Y)] using hfst_some_xs
              have hφsnd_x : SMT.RenamingContext.CoversFV (Function.update Δsnd x! (some Y)) snd!_spec :=
                SMT.RenamingContext.coversFV_update_of_notMem
                  (x := x!) (d := Y) hx_not_mem_fv_sndspec hφsnd1
              have hφsnd_xf :
                  SMT.RenamingContext.CoversFV
                    (Function.update (Function.update Δsnd x! (some Y)) fst! (some (x_1 i0))) snd!_spec :=
                SMT.RenamingContext.coversFV_update_of_notMem
                  (x := fst!) (d := (x_1 i0)) hfst_not_mem_fv_sndspec hφsnd_x
              have hsnd_some_goal_ctx :
                  (SMT.RenamingContext.denote
                    (Function.update (Function.update (Function.update «Δ» x! (some Y)) fst! (some (x_1 i0))) snd! (some (x_1 i1)))
                    snd!_spec
                    (by
                      simpa only [Δsnd,
                        update_swap (f := «Δ») (x := snd!) (y := x!) (hxy := x_ne_snd.symm)
                          (vx := some (x_1 i1)) (vy := some Y),
                        update_swap (f := Function.update «Δ» x! (some Y)) (x := snd!) (y := fst!)
                          (hxy := fst_ne_snd.symm) (vx := some (x_1 i1)) (vy := some (x_1 i0))] using hφsnd_xf)).isSome = true := by
                have hsnd_some_x :
                    (SMT.RenamingContext.denote
                      (Function.update Δsnd x! (some Y))
                      snd!_spec hφsnd_x).isSome = true := by
                  rw [← denote_isSome_update_of_notMem
                    («Δ» := Δsnd) (t := snd!_spec) (x := x!) (d := Y) (h := hφsnd1)
                    hx_not_mem_fv_sndspec]
                  simpa only [Δsnd] using hsnd_some
                have hsnd_some_xf :
                    (SMT.RenamingContext.denote
                      (Function.update (Function.update Δsnd x! (some Y)) fst! (some (x_1 i0)))
                      snd!_spec hφsnd_xf).isSome = true := by
                  rw [← denote_isSome_update_of_notMem
                    («Δ» := Function.update Δsnd x! (some Y)) (t := snd!_spec)
                    (x := fst!) (d := (x_1 i0)) (h := hφsnd_x) hfst_not_mem_fv_sndspec]
                  exact hsnd_some_x
                simpa only [Δsnd,
                  update_swap (f := «Δ») (x := snd!) (y := x!) (hxy := x_ne_snd.symm)
                    (vx := some (x_1 i1)) (vy := some Y),
                  update_swap (f := Function.update «Δ» x! (some Y)) (x := snd!) (y := fst!)
                    (hxy := fst_ne_snd.symm) (vx := some (x_1 i1)) (vy := some (x_1 i0))] using hsnd_some_xf
              obtain ⟨Dfst, hDfst⟩ := Option.isSome_iff_exists.mp hfst_some_goal_ctx
              obtain ⟨Dsnd, hDsnd⟩ := Option.isSome_iff_exists.mp hsnd_some_goal_ctx
              have hDfst_raw :
                  ⟦fst!_spec.abstract
                    (Function.update (Function.update (Function.update «Δ» x! (some Y)) fst! (some (x_1 i0))) snd! (some (x_1 i1)))
                    (by
                      simpa only [Δfst, update_swap (f := «Δ») (x := fst!) (y := x!) (hxy := x_ne_fst.symm)
                        (vx := some (x_1 i0)) (vy := some Y)] using hφfst_xs)⟧ˢ = some Dfst := by
                simpa [SMT.RenamingContext.denote] using hDfst
              have hDsnd_raw :
                  ⟦snd!_spec.abstract
                    (Function.update (Function.update (Function.update «Δ» x! (some Y)) fst! (some (x_1 i0))) snd! (some (x_1 i1)))
                    (by
                      simpa only [Δsnd,
                        update_swap (f := «Δ») (x := snd!) (y := x!) (hxy := x_ne_snd.symm)
                          (vx := some (x_1 i1)) (vy := some Y),
                        update_swap (f := Function.update «Δ» x! (some Y)) (x := snd!) (y := fst!)
                          (hxy := fst_ne_snd.symm) (vx := some (x_1 i1)) (vy := some (x_1 i0))] using hφsnd_xf)⟧ˢ = some Dsnd := by
                simpa [SMT.RenamingContext.denote] using hDsnd
              have hDfst_ty : Dfst.2.1 = .bool := by
                exact denote_type_eq_of_typing (typ_t := typ_fst!_spec_St₃) (hden := hDfst_raw)
              have hDsnd_ty : Dsnd.2.1 = .bool := by
                exact denote_type_eq_of_typing (typ_t := typ_snd!_spec_St₄) (hden := hDsnd_raw)
              let Δgoal : SMT.RenamingContext.Context :=
                Function.update (Function.update (Function.update «Δ» x! (some Y))
                  fst! (some (x_1 i0))) snd! (some (x_1 i1))
              have hcov_x! : SMT.RenamingContext.CoversFV Δgoal (SMT.Term.var x!) := by
                intro v hv
                rw [SMT.fv, List.mem_singleton] at hv
                subst hv
                simp [Δgoal, Function.update, x_ne_fst, x_ne_snd]
              have hcov_fst : SMT.RenamingContext.CoversFV Δgoal (SMT.Term.var fst!) := by
                intro v hv
                rw [SMT.fv, List.mem_singleton] at hv
                subst hv
                simp [Δgoal, Function.update, fst_ne_snd]
              have hcov_snd : SMT.RenamingContext.CoversFV Δgoal (SMT.Term.var snd!) := by
                intro v hv
                rw [SMT.fv, List.mem_singleton] at hv
                subst hv
                simp only [Function.update_self, Option.isSome_some, Δgoal]
              have hden_x! :
                  ⟦(SMT.Term.var x!).abstract Δgoal hcov_x!⟧ˢ = some Y := by
                rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some_inj]
                apply Option.get_of_eq_some
                simp [Δgoal, Function.update, x_ne_fst, x_ne_snd]
              have hden_fst :
                  ⟦(SMT.Term.var fst!).abstract Δgoal hcov_fst⟧ˢ = some (x_1 i0) := by
                rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some_inj]
                apply Option.get_of_eq_some
                simp [Δgoal, Function.update, fst_ne_snd]
              have hden_snd :
                  ⟦(SMT.Term.var snd!).abstract Δgoal hcov_snd⟧ˢ = some (x_1 i1) := by
                rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some_inj]
                apply Option.get_of_eq_some
                simp only [Δgoal, Function.update_self]
              obtain ⟨Dpair, hDpair_raw, hDpair_ty⟩ :=
                denote_pair_some_of_some hden_fst hden_snd
              have hDpair_ty' : Dpair.2.1 = α'.pair β' := by
                simp only [hDpair_ty, hx0.1, hx1.1]
              have hEq_ty : Y.2.1 = Dpair.2.1 := by
                calc
                  Y.2.1 = α'.pair β' := hYβ
                  _ = Dpair.2.1 := hDpair_ty'.symm
              have hcov_eq : SMT.RenamingContext.CoversFV Δgoal
                  (SMT.Term.var x! =ˢ SMT.Term.pair (SMT.Term.var fst!) (SMT.Term.var snd!)) := by
                intro v hv
                rw [SMT.fv.eq_def] at hv
                rw [List.mem_append] at hv
                rcases hv with hvx | hvpair
                · rw [SMT.fv, List.mem_singleton] at hvx
                  subst hvx
                  simp [Δgoal, Function.update, x_ne_fst, x_ne_snd]
                · have hvpair' :
                    v ∈ SMT.fv (SMT.Term.var fst!) ∨ v ∈ SMT.fv (SMT.Term.var snd!) := by
                    simpa [SMT.fv, List.mem_append] using hvpair
                  rcases hvpair' with hvfst | hvsnd
                  · exact hcov_fst _ hvfst
                  · exact hcov_snd _ hvsnd
              have hden_eq_rhs :
                  ⟦(SMT.Term.pair (SMT.Term.var fst!) (SMT.Term.var snd!)).abstract Δgoal
                    (by
                      intro v hv
                      have hv' :
                          v ∈ SMT.fv (SMT.Term.var fst!) ∨ v ∈ SMT.fv (SMT.Term.var snd!) := by
                        simpa [SMT.fv, List.mem_append] using hv
                      rcases hv' with hvfst | hvsnd
                      · exact hcov_fst _ hvfst
                      · exact hcov_snd _ hvsnd)⟧ˢ = some Dpair := by
                simpa only [SMT.Term.abstract, proof_irrel_heq] using hDpair_raw
              obtain ⟨Deq, hDeq_raw, hDeq_ty⟩ :=
                denote_eq_some_of_some
                  (h₁ := hden_x!)
                  (h₂ := hden_eq_rhs)
                  (hτ := hEq_ty)
              obtain ⟨Dspec, hDspec_raw, hDspec_ty⟩ :=
                denote_and_some_bool_of_some_bool hDfst_raw hDfst_ty hDsnd_raw hDsnd_ty
              obtain ⟨Dbody, hDbody_raw, hDbody_ty⟩ :=
                denote_and_some_bool_of_some_bool hDeq_raw hDeq_ty hDspec_raw hDspec_ty
              have hnot_some :=
                denote_not_isSome_of_some_bool (hden := hDbody_raw) (hTy := hDbody_ty)
              simpa only [SMT.Term.abstract, SMT.denote, Option.bind_eq_bind, Option.pure_def,
                SMT.Term.abstract.go, Function.OfArity.uncurry, Function.FromTypes.uncurry,
                Δgoal, i0, i1, proof_irrel_heq] using hnot_some
