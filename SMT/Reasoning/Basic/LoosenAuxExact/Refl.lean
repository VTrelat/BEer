import SMT.Reasoning.Defs
import SMT.Reasoning.LooseningDefs
import SMT.Reasoning.Basic.StateSpecs

open Std.Do SMT ZFSet Classical

theorem loosenAux_prf_exact.refl («Δ» : RenamingContext.Context) {α : SMTType}
  (hα : α = SMTType.int ∨ α = SMTType.bool ∨ α = SMTType.unit)
  {Λ : TypeContext} {n : ℕ} {used : List 𝒱} {name : String}
  {x : Term} (typ_x : Λ ⊢ˢ x : α) (hx : RenamingContext.CoversFV «Δ» x)
  (pf : ∀ (x! : 𝒱) (X! : SMT.Dom), ∀ v ∈ fv (Term.var x!),
    (Function.update «Δ» x! (some X!) v).isSome = true) :
  ⦃fun x =>
    match x with
    | { env := E, types := Λ' } => ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ AList.keys Λ' ⊆ E.usedVars ∧ E.usedVars = used⌝⦄
    loosenAux_prf name (castPath.refl hα) x ⦃PostCond.mayThrow fun x_1 x_2 =>
      match x_1 with
      | (x!, x!_spec) =>
        match x_2 with
        | { env := E', types := Γ' } =>
          ⌜n ≤ E'.freshvarsc ∧
              AList.insert x! α Λ ⊆ Γ' ∧
                x! ∉ Λ ∧
                  x! ∉ used ∧
                    used ⊆ E'.usedVars ∧
                      AList.keys Γ' ⊆ E'.usedVars ∧
                        (∀ v ∈ used, v ∉ Λ → v ∉ Γ') ∧
                        AList.insert x! α Λ ⊢ˢ Term.var x! : α ∧
                          AList.insert x! α Λ ⊢ˢ x!_spec : SMTType.bool ∧
                            Γ' ⊢ˢ Term.var x! : α ∧
                              Γ' ⊢ˢ x!_spec : SMTType.bool ∧
                                fv x!_spec ⊆ fv x ∪ {x!} ∧
                                  ∀ (X : SMT.Dom),
                                    ⟦x.abstract «Δ» hx⟧ˢ = some X →
                                      ∃ Φ X!,
                                        ∃ (_ :
                                          ⟦(Term.var x!).abstract (Function.update «Δ» x! (some X!))
                                              (pf x! X!)⟧ˢ = some X!)
                                          (hφ : RenamingContext.CoversFV (Function.update «Δ» x! (some X!)) x!_spec)
                                          (_ : ⟦x!_spec.abstract (Function.update «Δ» x! (some X!)) hφ⟧ˢ = some Φ),
                                          Φ.snd.fst = SMTType.bool ∧
                                            (Φ.fst = zftrue ∧
                                                X.fst.pair X!.fst ∈
                                                  (castZF_of_path (castPath.refl hα)).1) ∧
                                              ∀ (Y : SMT.Dom),
                                                Y.snd.fst = α →
                                                  ∀ (hφY :
                                                    RenamingContext.CoversFV
                                                      (Function.update «Δ» x! (some Y)) x!_spec),
                                                    ⟦x!_spec.abstract
                                                        (Function.update «Δ» x! (some Y)) hφY⟧ˢ.isSome = true ∧
                                                      ∀ {ΦY : SMT.Dom},
                                                        ⟦x!_spec.abstract
                                                            (Function.update «Δ» x! (some Y)) hφY⟧ˢ =
                                                          some ΦY →
                                                        ΦY.fst = zftrue →
                                                          X.fst.pair Y.fst ∈
                                                            (castZF_of_path (castPath.refl hα)).1⌝⦄ := by
  mintro pre ∀St₁
  mpure pre
  obtain ⟨rfl, rfl, sub, rfl⟩ := pre
  unfold loosenAux_prf
  mspec SMT.freshVar_spec (Γ := St₁.types) (n := St₁.env.freshvarsc) (used := St₁.env.usedVars)
  next x! =>
    mrename_i pre
    mintro ∀St₂
    mcases pre with ⟨St₂_types_eq, x!_fresh, St₂_fvc, St₂_used_eq, x!_not_used⟩
    mspec Std.Do.Spec.pure
    mpure_intro
    and_intros
    · rw [St₂_fvc]
      exact Nat.le.intro rfl
    · intro v hv
      rw [St₂_types_eq]
      exact hv
    · exact x!_fresh
    · exact x!_not_used
    · rw [St₂_used_eq]
      intro v hv
      exact List.mem_cons_of_mem _ hv
    · rw [St₂_types_eq, St₂_used_eq, AList.keys_insert]
      intro v hv
      rw [List.mem_cons] at hv ⊢
      rcases hv with rfl | hv
      · exact Or.inl rfl
      · exact Or.inr (sub (List.mem_of_mem_erase hv))
    · -- preserves_types
      intro v hv hv_not_Λ
      rw [St₂_types_eq, AList.mem_insert]; push_neg
      exact ⟨fun h => absurd (h ▸ hv) x!_not_used, hv_not_Λ⟩
    · apply Typing.var
      exact AList.lookup_insert St₁.types
    · apply Typing.eq
      · apply Typing.var
        exact AList.lookup_insert St₁.types
      · exact Typing.weakening
          (h := TypeContext.entries_subset_insert_of_notMem x!_fresh)
          (typ := typ_x)
    · rw [St₂_types_eq]
      apply Typing.var
      exact AList.lookup_insert St₁.types
    · rw [St₂_types_eq]
      apply Typing.eq
      · apply Typing.var
        exact AList.lookup_insert St₁.types
      · exact Typing.weakening
          (h := TypeContext.entries_subset_insert_of_notMem x!_fresh)
          (typ := typ_x)
    · rw [fv, fv, List.cons_append, List.nil_append, List.cons_subset, List.mem_union_iff]
      exact ⟨.inr <| List.mem_of_mem_head? rfl, fun _ h ↦ List.mem_union_left h {x!}⟩
    · intro X denx
      classical
      have x!_not_mem_fv_x : x! ∉ SMT.fv x := by
        intro hx_mem
        exact x!_fresh (SMT.Typing.mem_context_of_mem_fv typ_x hx_mem)
      refine ⟨⟨overloadBinOp (A := ⟦X.2.1⟧ᶻ) (B := 𝔹) (fun x => (↑x : ZFSet))
        (fun (p : Prop) => if p then ZFBool.true else ZFBool.false) False
        (fun x1 x2 => x1 = x2) X.1 X.1, .bool, overloadBinOp_mem X.2.2 X.2.2⟩, X, ?_, ?_, ?_, ?_⟩
      · rw [Term.abstract, denote, Option.pure_def, Option.some_inj]
        apply Option.get_of_eq_some
        apply Function.update_self
      · intro v hv
        have hv_cases : v = x! ∨ v ∈ SMT.fv x := by
          rwa [fv, fv, List.mem_append, List.mem_singleton] at hv
        rcases hv_cases with hvx | hvx
        · subst hvx
          rw [Function.update_self, Option.isSome_some]
        · have hv_ne : v ≠ x! := by
            rintro rfl
            exact x!_not_mem_fv_x hvx
          rw [Function.update_of_ne hv_ne]
          exact hx v hvx
      · have denx_upd :
            ⟦x.abstract (Function.update «Δ» x! (some X))
              (SMT.RenamingContext.coversFV_update_of_notMem
                (x := x!) (d := X) x!_not_mem_fv_x hx)⟧ˢ = some X := by
          have hden_raw :
              ⟦x.abstract «Δ» hx⟧ˢ =
                ⟦x.abstract (Function.update «Δ» x! (some X))
                  (SMT.RenamingContext.coversFV_update_of_notMem
                    (x := x!) (d := X) x!_not_mem_fv_x hx)⟧ˢ := by
            rw [←SMT.RenamingContext.denote]
            exact RenamingContext.denote_update_of_notMem x!_not_mem_fv_x
          rw [←hden_raw]
          exact denx
        rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff]
        refine ⟨X, ?_, ?_⟩
        · rw [Term.abstract, denote, Option.pure_def, Option.some_inj]
          apply Option.get_of_eq_some
          apply Function.update_self
        · dsimp
          rw [denx_upd, Option.bind_some]
          rw [dite_cond_eq_true (eq_true rfl)]
      · constructor
        · rfl
        · constructor
          · constructor
            · have hcond : X.1 ∈ ⟦X.2.1⟧ᶻ ∧ X.1 ∈ ⟦X.2.1⟧ᶻ := ⟨X.2.2, X.2.2⟩
              dsimp
              rw [overloadBinOp, dif_pos hcond, Function.onFun, if_pos (by rfl)]
            · have hXτ : α = X.2.1 := by
                have hXτ' := SMT.PHOAS.denote_welltyped_eq
                  (den_t := denx)
                  (t := x.abstract «Δ» hx)
                  ?_
                on_goal 2 =>
                  use SMT.TypeContext.abstract («Δ» := «Δ») ?_, PHOAS.WFTC.of_abstract, α
                  · apply PHOAS.Typing.of_abstract
                    exact typ_x
                dsimp at hXτ'
                exact hXτ'
              have hpair : X.1.pair X.1 ∈ 𝟙⟦α⟧ᶻ := by
                rw [pair_mem_Id_iff]
                subst α
                exact X.2.2
              rwa [castZF_of_path]
          · intro Y hYβ hφY
            have hXτ' := SMT.PHOAS.denote_welltyped_eq
              (den_t := denx)
              (t := x.abstract «Δ» hx)
              ?_
            on_goal 2 =>
              use SMT.TypeContext.abstract («Δ» := «Δ») ?_, PHOAS.WFTC.of_abstract, α
              · apply PHOAS.Typing.of_abstract
                exact typ_x
            have hXτ : α = X.2.1 := by
              dsimp at hXτ'
              exact hXτ'
            have denx_updY :
                ⟦x.abstract (Function.update «Δ» x! (some Y))
                  (SMT.RenamingContext.coversFV_update_of_notMem
                    (x := x!) (d := Y) x!_not_mem_fv_x hx)⟧ˢ = some X := by
              have hden_raw :
                  ⟦x.abstract «Δ» hx⟧ˢ =
                    ⟦x.abstract (Function.update «Δ» x! (some Y))
                      (SMT.RenamingContext.coversFV_update_of_notMem
                        (x := x!) (d := Y) x!_not_mem_fv_x hx)⟧ˢ := by
                rw [←SMT.RenamingContext.denote]
                exact SMT.RenamingContext.denote_update_of_notMem x!_not_mem_fv_x
              rw [←hden_raw]
              exact denx
            have hYX : Y.2.1 = X.2.1 := by
              rw [hYβ, hXτ]
            constructor
            · rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, denx_updY]
              simp only [
                Term.abstract, Function.update_self, Option.get_some, denote, Option.pure_def,
                Option.failure_eq_none, Option.bind_some, hYX, ↓reduceDIte, Option.isSome_some]
            · intro ΦY hdenY htrue
              have hdenY' := hdenY
              rw [Term.abstract, denote, Option.pure_def, Option.bind_eq_bind, denx_updY] at hdenY'
              simp only [
                Term.abstract, Function.update_self, Option.get_some, denote, Option.pure_def,
                Option.failure_eq_none, Option.bind_some, hYX] at hdenY'
              have hX_mem_Y : X.1 ∈ ⟦Y.2.1⟧ᶻ := by
                rw [hYX]
                exact X.2.2
              have hEq : overloadBinOp (A := ⟦Y.2.1⟧ᶻ) (B := 𝔹) (fun x => (↑x : ZFSet))
                  (fun (p : Prop) => if p then ZFBool.true else ZFBool.false) False
                  (fun x1 x2 => x1 = x2) Y.1 X.1 = zftrue := by
                have hdenY'' : some ΦY =
                    some
                      ⟨overloadBinOp (A := ⟦Y.2.1⟧ᶻ) (B := 𝔹) (fun x => (↑x : ZFSet))
                          (fun (p : Prop) => if p then ZFBool.true else ZFBool.false) False
                          (fun x1 x2 => x1 = x2) Y.1 X.1,
                        .bool, overloadBinOp_mem Y.2.2 hX_mem_Y⟩ := by
                  simpa using hdenY'.symm
                rw [Option.some_inj] at hdenY''
                have hfst := congrArg (fun d : SMT.Dom => d.1) hdenY''
                simpa [htrue] using hfst.symm
              have hY_eq_X : Y.1 = X.1 := by
                have hcond : Y.1 ∈ ⟦Y.2.1⟧ᶻ ∧ X.1 ∈ ⟦Y.2.1⟧ᶻ := ⟨Y.2.2, hX_mem_Y⟩
                dsimp [overloadBinOp] at hEq
                rw [dif_pos hcond, Function.onFun] at hEq
                by_cases hYXeq : Y.1 = X.1
                · exact hYXeq
                · rw [if_neg hYXeq] at hEq
                  have hfalse : zftrue = zffalse := by
                    simpa [ZFSet.zffalse, ZFBool.false] using hEq.symm
                  exact False.elim (ZFSet.zftrue_ne_zffalse hfalse)
              have hXα : X.1 ∈ ⟦α⟧ᶻ := by
                rw [hXτ]
                exact X.2.2
              have hpair : X.1.pair Y.1 ∈ 𝟙⟦α⟧ᶻ := by
                rw [hY_eq_X]
                exact (pair_mem_Id_iff hXα).2 rfl
              rwa [castZF_of_path]
