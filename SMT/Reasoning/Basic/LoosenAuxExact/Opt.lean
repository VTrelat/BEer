import SMT.Reasoning.Defs
import SMT.Reasoning.LooseningDefs
import SMT.Reasoning.Basic.StateSpecs

open Std.Do SMT ZFSet Classical

set_option maxHeartbeats 4000000
theorem loosenAux_prf_exact.opt.{u} («Δ» : RenamingContext.Context.{u})
  (pf : ∀ (x! : 𝒱) (X! : SMT.Dom), ∀ v ∈ fv (Term.var x!), (Function.update «Δ» x! (some X!) v).isSome = true)
  {α α' : SMTType} (hα : α ⇝ α')
  (ih :
    ∀ {Λ : TypeContext} {n : ℕ} {used : List 𝒱} {name : String} {x : Term},
      Λ ⊢ˢ x : α →
        ∀ («Δ₀» : RenamingContext.Context.{u}) (hx : RenamingContext.CoversFV «Δ₀» x)
          (pf₀ : ∀ (x! : 𝒱) (X! : SMT.Dom), ∀ v ∈ fv (Term.var x!), (Function.update «Δ₀» x! (some X!) v).isSome = true),
          ⦃fun x =>
            match x with
            | { env := E, types := Λ' } => ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ AList.keys Λ' ⊆ E.usedVars ∧ E.usedVars = used⌝⦄
            loosenAux_prf name hα x ⦃PostCond.mayThrow fun x_1 x_2 =>
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
                                                    (Φ.fst = zftrue ∧ X.fst.pair X!.fst ∈ (castZF_of_path hα).1) ∧
                                                      ∀ (Y : SMT.Dom),
                                                        Y.snd.fst = α' →
                                                          ∀
                                                            (hφY :
                                                              RenamingContext.CoversFV (Function.update «Δ₀» x! (some Y))
                                                                x!_spec),
                                                            ⟦x!_spec.abstract (Function.update «Δ₀» x! (some Y))
                                                                    hφY⟧ˢ.isSome =
                                                              true ∧
                                                              ∀ {ΦY : SMT.Dom},
                                                                ⟦x!_spec.abstract
                                                                    (Function.update «Δ₀» x! (some Y)) hφY⟧ˢ =
                                                                  some ΦY →
                                                                ΦY.fst = zftrue →
                                                                  X.fst.pair Y.fst ∈
                                                                    (castZF_of_path hα).1⌝⦄)
  {Λ : TypeContext} {n : ℕ} {used : List 𝒱} {name : String} {x : Term} (typ_x : Λ ⊢ˢ x : α.option)
  (hx : RenamingContext.CoversFV «Δ» x) :
  ⦃fun x =>
    match x with
    | { env := E, types := Λ' } => ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ AList.keys Λ' ⊆ E.usedVars ∧ E.usedVars = used⌝⦄
    loosenAux_prf name hα.opt x ⦃PostCond.mayThrow fun x_1 x_2 =>
      match x_1 with
      | (x!, x!_spec) =>
        match x_2 with
        | { env := E', types := Γ' } =>
          ⌜n ≤ E'.freshvarsc ∧
              AList.insert x! α'.option Λ ⊆ Γ' ∧
                x! ∉ Λ ∧
                  x! ∉ used ∧
                    used ⊆ E'.usedVars ∧
                      AList.keys Γ' ⊆ E'.usedVars ∧
                        (∀ v ∈ used, v ∉ Λ → v ∉ Γ') ∧
                        AList.insert x! α'.option Λ ⊢ˢ Term.var x! : α'.option ∧
                          AList.insert x! α'.option Λ ⊢ˢ x!_spec : SMTType.bool ∧
                            Γ' ⊢ˢ Term.var x! : α'.option ∧
                              Γ' ⊢ˢ x!_spec : SMTType.bool ∧
                                fv x!_spec ⊆ fv x ∪ {x!} ∧
                                  ∀ (X : SMT.Dom),
                                    ⟦x.abstract «Δ» hx⟧ˢ = some X →
                                      ∃ Φ X!,
                                        ∃ (_ : ⟦(Term.var x!).abstract (Function.update «Δ» x! (some X!)) (pf x! X!)⟧ˢ = some X!)
                                          (hφ : RenamingContext.CoversFV (Function.update «Δ» x! (some X!)) x!_spec) (_
                                          : ⟦x!_spec.abstract (Function.update «Δ» x! (some X!)) hφ⟧ˢ = some Φ),
                                          Φ.snd.fst = SMTType.bool ∧
                                            (Φ.fst = zftrue ∧ X.fst.pair X!.fst ∈ (castZF_of_path hα.opt).1) ∧
                                              ∀ (Y : SMT.Dom),
                                                Y.snd.fst = α'.option →
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
                                                            (castZF_of_path hα.opt).1⌝⦄ := by
  mintro pre ∀St₁
  mpure pre
  obtain ⟨rfl, rfl, sub, rfl⟩ := pre
  have ih_on_Δ :
    ∀ {Λ : TypeContext} {n : ℕ} {used : List 𝒱} {name : String} {x : Term},
      Λ ⊢ˢ x : α →
        ∀ (hx : RenamingContext.CoversFV «Δ» x),
          ⦃fun x =>
            match x with
            | { env := E, types := Λ' } => ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ AList.keys Λ' ⊆ E.usedVars ∧ E.usedVars = used⌝⦄
            loosenAux_prf name hα x ⦃PostCond.mayThrow fun x_1 x_2 =>
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
                                                ∃ (denx! :
                                                  ⟦(Term.var x!).abstract (Function.update «Δ» x! (some X!)) (pf x! X!)⟧ˢ =
                                                    some X!)
                                                  (hφ :
                                                  RenamingContext.CoversFV (Function.update «Δ» x! (some X!)) x!_spec)
                                                  (denφ :
                                                  ⟦x!_spec.abstract (Function.update «Δ» x! (some X!)) hφ⟧ˢ = some Φ),
                                                  Φ.snd.fst = SMTType.bool ∧
                                                    (Φ.fst = zftrue ∧ X.fst.pair X!.fst ∈ (castZF_of_path hα).1) ∧
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
                                                                    (castZF_of_path hα).1⌝⦄ := fun htyp hx => ih htyp «Δ» hx pf
  unfold loosenAux_prf
  mspec SMT.freshVar_spec (Γ := St₁.types) (n := St₁.env.freshvarsc) (used := St₁.env.usedVars)
  next x! =>
    mrename_i pre
    mintro ∀St₂
    mcases pre with ⟨St₂_types_eq, x!_fresh, St₂_fvc, St₂_used_eq, x!_not_used⟩
    have typ_x_St₂ : St₂.types ⊢ˢ x : α.option := by
      rw [St₂_types_eq]
      exact SMT.Typing.weakening
        (h := SMT.TypeContext.entries_subset_insert_of_notMem x!_fresh)
        typ_x
    by_cases hnone : x = .none
    · subst hnone
      exact (SMT.Typing.noneE typ_x_St₂).elim
    · by_cases hsome : ∃ t, x = .some t
      · rcases hsome with ⟨t, rfl⟩
        have typ_t_St₂ : St₂.types ⊢ˢ t : α := by
          have : St₂.types ⊢ˢ .some t : α.option := by simpa using typ_x_St₂
          rcases SMT.Typing.someE this with ⟨σ, hσ, htyp⟩
          cases hσ
          simpa using htyp
        have hx_t : RenamingContext.CoversFV «Δ» t := by
          intro v hv
          exact hx v (by simpa [fv] using hv)
        mspec ih_on_Δ (x := t) (Λ := St₂.types) (n := St₂.env.freshvarsc) (used := St₂.env.usedVars)
          typ_t_St₂ hx_t
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
        · rename_i out_t
          obtain ⟨the_x!, the_x!_spec⟩ := out_t
          mrename_i pre
          mintro ∀St₃
          mpure pre
          obtain ⟨hn₃, St₃_types_eq, the_x!_fresh, the_x!_not_used, used_sub₃, keys_sub₃, preserves_the_x!,
            typ_the_x!, typ_the_x!_spec, typ_the_x!_St₃, typ_the_x!_spec_St₃, fv_the_x!_spec,
            den_the⟩ := pre
          mspec Std.Do.Spec.pure
          have typ_x!_spec_base :
              (AList.insert x! α'.option St₁.types) ⊢ˢ
                .exists [the_x!] [α'] ((.var x! =ˢ .some (.var the_x!)) ∧ˢ the_x!_spec) : .bool := by
            have the_x!_not_base : the_x! ∉ (AList.insert x! α'.option St₁.types) := by
              intro hmem
              apply the_x!_fresh
              rw [St₂_types_eq]
              exact hmem
            have x_ne_the : x! ≠ the_x! := by
              intro h
              apply the_x!_not_base
              rw [h, AList.mem_insert]
              exact Or.inl rfl
            have typ_the_x!_spec_body :
                (AList.insert the_x! α' (AList.insert x! α'.option St₁.types)) ⊢ˢ the_x!_spec : .bool := by
              rw [←St₂_types_eq]
              exact typ_the_x!_spec
            have typ_var_x_body :
                (AList.insert the_x! α' (AList.insert x! α'.option St₁.types)) ⊢ˢ .var x! : α'.option := by
              apply SMT.Typing.var
              rw [AList.lookup_insert_ne x_ne_the, AList.lookup_insert]
            have typ_var_the_body :
                (AList.insert the_x! α' (AList.insert x! α'.option St₁.types)) ⊢ˢ .var the_x! : α' := by
              apply SMT.Typing.var
              rw [AList.lookup_insert]
            have typ_some_the_body :
                (AList.insert the_x! α' (AList.insert x! α'.option St₁.types)) ⊢ˢ .some (.var the_x!) : α'.option := by
              exact SMT.Typing.some _ _ _ typ_var_the_body
            have typ_eq_body :
                (AList.insert the_x! α' (AList.insert x! α'.option St₁.types))
                  ⊢ˢ (.var x! =ˢ .some (.var the_x!)) : .bool := by
              exact SMT.Typing.eq _ _ _ _ typ_var_x_body typ_some_the_body
            have typ_body :
                (AList.insert the_x! α' (AList.insert x! α'.option St₁.types))
                  ⊢ˢ ((.var x! =ˢ .some (.var the_x!)) ∧ˢ the_x!_spec) : .bool := by
              exact SMT.Typing.and _ _ _ typ_eq_body typ_the_x!_spec_body
            have the_x!_in_body_ctx :
                the_x! ∈ (AList.insert the_x! α' (AList.insert x! α'.option St₁.types)) := by
              rw [AList.mem_insert]
              exact Or.inl rfl
            have fresh_body :
                ∀ v ∈ [the_x!], v ∉ bv ((.var x! =ˢ .some (.var the_x!)) ∧ˢ the_x!_spec) := by
              intro v hv
              rw [List.mem_singleton] at hv
              subst hv
              intro hbv
              exact (SMT.Typing.bv_notMem_context typ_body _ hbv) the_x!_in_body_ctx
            have len_eq_vs : [the_x!].length = [α'].length := by simp
            apply SMT.Typing.exists
              (Γ := (AList.insert x! α'.option St₁.types))
              (vs := [the_x!]) (τs := [α']) (len_eq := len_eq_vs)
            · intro v hv
              rw [List.mem_singleton] at hv
              subst hv
              exact the_x!_not_base
            · exact fresh_body
            · exact Nat.zero_lt_succ 0
            · have hupdate :
                SMT.TypeContext.update (AList.insert x! α'.option St₁.types) [the_x!] [α'] len_eq_vs =
                  AList.insert the_x! α' (AList.insert x! α'.option St₁.types) := by
                simp only [SMT.TypeContext.update, List.length_cons, List.length_nil, zero_add, Fin.cast_eq_self, Fin.getElem_fin,
                  Fin.foldl_succ_last, Fin.coe_ofNat_eq_mod, Nat.mod_succ,
                  List.getElem_cons_zero, Fin.last_zero, Fin.isValue, Fin.foldl_zero]
              rwa [hupdate]
          mpure_intro
          and_intros
          · calc
              St₁.env.freshvarsc ≤ St₂.env.freshvarsc := by rw [St₂_fvc]; exact Nat.le_succ _
              _ ≤ St₃.env.freshvarsc := hn₃
          · intro v hv
            have hv₂ : v ∈ St₂.types.entries := by
              simpa [St₂_types_eq] using hv
            exact St₃_types_eq (SMT.TypeContext.entries_subset_insert_of_notMem the_x!_fresh hv₂)
          · exact x!_fresh
          · exact x!_not_used
          · intro v hv
            have hv₂ : v ∈ St₂.env.usedVars := by
              rw [St₂_used_eq]
              exact List.mem_cons_of_mem _ hv
            exact used_sub₃ hv₂
          · exact keys_sub₃
          · -- preserves_types
            intro v hv hv_not_Λ
            have hv_ne_x : v ≠ x! := fun h => absurd (h ▸ hv) x!_not_used
            have hv_not_St₂ : v ∉ St₂.types := by
              rw [St₂_types_eq, AList.mem_insert]; push_neg
              exact ⟨hv_ne_x, hv_not_Λ⟩
            have hv_in_St₂_used : v ∈ St₂.env.usedVars := by
              rw [St₂_used_eq]; exact List.mem_cons_of_mem _ hv
            exact preserves_the_x! v hv_in_St₂_used hv_not_St₂
          · apply SMT.Typing.var
            exact AList.lookup_insert St₁.types
          · exact typ_x!_spec_base
          · have typ_x!_base : (AList.insert x! α'.option St₁.types) ⊢ˢ .var x! : α'.option := by
              apply SMT.Typing.var
              exact AList.lookup_insert St₁.types
            apply SMT.Typing.weakening _ typ_x!_base
            intro v hv
            have hv₂ : v ∈ St₂.types.entries := by rwa [St₂_types_eq]
            exact St₃_types_eq (SMT.TypeContext.entries_subset_insert_of_notMem the_x!_fresh hv₂)
          · apply SMT.Typing.weakening _ typ_x!_spec_base
            intro v hv
            have hv₂ : v ∈ St₂.types.entries := by rwa [St₂_types_eq]
            exact St₃_types_eq (SMT.TypeContext.entries_subset_insert_of_notMem the_x!_fresh hv₂)
          · intro v hv
            rw [SMT.fv.eq_def] at hv
            rcases List.mem_removeAll_iff.mp hv with ⟨hv_body, hv_not_bound⟩
            have hv_ne_the : v ≠ the_x! := by
              intro h
              apply hv_not_bound
              exact List.mem_singleton.mpr h
            have hv_body' : v = x! ∨ v = the_x! ∨ v ∈ fv the_x!_spec := by
              simpa only [fv, List.cons_append, List.nil_append, List.mem_cons] using hv_body
            rw [List.mem_union_iff]
            rcases hv_body' with hvx | hvthe | hvspec
            · subst hvx
              exact Or.inr (List.mem_singleton.mpr rfl)
            · exact (hv_ne_the hvthe).elim
            · have hv' := fv_the_x!_spec hvspec
              rw [List.mem_union_iff] at hv'
              rcases hv' with hvt | hvthe'
              · exact Or.inl (by simpa [fv] using hvt)
              · exact (hv_ne_the (List.mem_singleton.mp hvthe')).elim
          · intro X denx
            have denx' := denx
            rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at denx'
            obtain ⟨Xt, den_t, hXeq⟩ := denx'
            obtain ⟨Φt, Xt!, denXt!, hφt, denφt, hΦt_ty, ⟨hΦt_true, hCast_t⟩, htot_t⟩ := den_the Xt den_t
            have hXt!_ty : Xt!.snd.fst = α' := denote_type_eq_of_typing (typ_t := typ_the_x!) (hden := denXt!)
            have hXt!_memα' : Xt!.fst ∈ ⟦α'⟧ᶻ := by
              simpa only [hXt!_ty] using Xt!.snd.snd
            let X!opt : SMT.Dom :=
              ⟨(ZFSet.Option.some ⟨Xt!.fst, hXt!_memα'⟩).1, α'.option,
                SetLike.coe_mem (ZFSet.Option.some ⟨Xt!.fst, hXt!_memα'⟩)⟩
            have hfv_spec_sub :
                SMT.fv (.exists [the_x!] [α'] ((.var x! =ˢ .some (.var the_x!)) ∧ˢ the_x!_spec)) ⊆
                  SMT.fv t.some ∪ {x!} := by
              intro v hv
              rw [SMT.fv.eq_def] at hv
              rcases List.mem_removeAll_iff.mp hv with ⟨hv_body, hv_not_bound⟩
              have hv_ne_the : v ≠ the_x! := by
                intro h
                apply hv_not_bound
                exact List.mem_singleton.mpr h
              have hv_body' : v = x! ∨ v = the_x! ∨ v ∈ fv the_x!_spec := by
                simpa only [fv, List.cons_append, List.nil_append, List.mem_cons] using hv_body
              rw [List.mem_union_iff]
              rcases hv_body' with hvx | hvthe | hvspec
              · subst hvx
                exact Or.inr (List.mem_singleton.mpr rfl)
              · exact (hv_ne_the hvthe).elim
              · have hv' := fv_the_x!_spec hvspec
                rw [List.mem_union_iff] at hv'
                rcases hv' with hvt | hvthe'
                · exact Or.inl (by rwa [fv])
                · exact (hv_ne_the (List.mem_singleton.mp hvthe')).elim
            refine ⟨⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩, X!opt, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · dsimp [X!opt]
              rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some_inj]
              apply Option.get_of_eq_some
              apply Function.update_self
            · intro v hv
              by_cases hvx : v = x!
              · subst hvx
                rw [Function.update_self, Option.isSome_some]
              · rw [Function.update_of_ne hvx]
                have hv' := hfv_spec_sub hv
                rw [List.mem_union_iff] at hv'
                rcases hv' with hvt | hvx_single
                · exact hx v hvt
                · exfalso
                  exact hvx (List.mem_singleton.mp hvx_single)
            · rw [SMT.Term.abstract, dite_cond_eq_true (eq_true (by rfl)), SMT.PHOAS.Term.exists, SMT.denote]
              simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists, Option.pure_def]
              refine ⟨zffalse, SMTType.bool, ZFSet.ZFBool.zffalse_mem_𝔹, ?_, ?_⟩
              · have hlen_pos : [the_x!].length > 0 := Nat.zero_lt_succ 0
                simp only [SMT.denote, dite_cond_eq_true (eq_true hlen_pos)]
                split_ifs with den_t_isSome
                · simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_one_sub_one,
                  List.getElem_cons_succ, List.getElem_cons_zero, Fin.val_eq_zero,
                  get.eq_1, forall_const, Option.pure_def, Option.failure_eq_none,
                  Option.bind_eq_bind, Option.some.injEq, PSigma.mk.injEq, Fin.foldl_zero,
                  Option.get_bind]
                  let sInter_eq_zffalse : Prop := ?_
                  conv_lhs =>
                    change sInter_eq_zffalse
                  have : sInter_eq_zffalse := by
                    ext1 z
                    simp only [subset_refl, subset_of_empty, notMem_empty, iff_false]
                    intro contra
                    set sInter_sep : ZFSet := ?_
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
                    simp only [mem_sep, mem_insert_iff, mem_singleton, and_imp, forall_exists_index,
                      forall_eq_or_imp, right_eq_dite_iff, forall_and_index, notMem_empty,
                      imp_false, not_forall, forall_eq] at contra
                    obtain ⟨contra1, contra2⟩ := contra
                    obtain ⟨hAr, hMem, hnotFalse⟩ := contra1 Xt!.fst hXt!_memα'
                    apply hnotFalse
                    have hXt!_cast : (⟨Xt!.fst, ⟨α', hXt!_memα'⟩⟩ : SMT.Dom) = Xt! := by
                      cases Xt! with
                      | mk x hx =>
                        cases hx with
                        | mk τ hxmem =>
                          dsimp at hXt!_ty hXt!_memα'
                          cases hXt!_ty
                          rfl
                    conv_rhs =>
                      enter [1, 1]
                      simp only [Option.pure_def, Option.failure_eq_none, Option.bind_eq_bind,
                        SMT.denote, Function.OfArity.uncurry, Function.FromTypes.uncurry, Fin.zero_eq_one_iff,
                        Nat.reduceAdd, Nat.succ_ne_self, ↓dreduceIte, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
                        List.getElem_cons_zero, Term.abstract.go, hXt!_cast]
                    have typ_t_St₁ : St₁.types ⊢ˢ t : α := by
                      have : St₁.types ⊢ˢ .some t : α.option := by simpa using typ_x
                      rcases SMT.Typing.someE this with ⟨σ, hσ, htyp⟩
                      cases hσ
                      simpa only using htyp
                    have x!_not_mem_fv_t : x! ∉ SMT.fv t := by
                      intro hx_mem
                      exact x!_fresh (SMT.Typing.mem_context_of_mem_fv typ_t_St₁ hx_mem)
                    have hx_lookup_St₂ : St₂.types.lookup x! = some α'.option := by
                      rw [St₂_types_eq]
                      exact AList.lookup_insert St₁.types
                    have hx_mem_St₂ : x! ∈ St₂.types := by
                      exact (AList.lookup_isSome).1 (Option.isSome_of_eq_some hx_lookup_St₂)
                    have x!_ne_the : x! ≠ the_x! := by
                      intro h
                      subst h
                      exact the_x!_fresh hx_mem_St₂
                    have x!_not_mem_fv_the_spec : x! ∉ SMT.fv the_x!_spec := by
                      intro hx_mem
                      have hx' := fv_the_x!_spec hx_mem
                      rw [List.mem_union_iff] at hx'
                      rcases hx' with hxt | hxthe
                      · exact x!_not_mem_fv_t hxt
                      · exact x!_ne_the (List.mem_singleton.mp hxthe)
                    let Δgoal : SMT.RenamingContext.Context :=
                      Function.update (Function.update «Δ» x! (some X!opt))
                        the_x! (some Xt!)
                    have hφ_the_x :
                        SMT.RenamingContext.CoversFV
                          (Function.update (Function.update «Δ» the_x! (some Xt!)) x! (some X!opt))
                          the_x!_spec :=
                      SMT.RenamingContext.coversFV_update_of_notMem
                        (x := x!) (d := X!opt) x!_not_mem_fv_the_spec hφt
                    have hφ_goal :
                        SMT.RenamingContext.CoversFV Δgoal the_x!_spec := by
                      simpa only [update_swap (f := «Δ») (x := the_x!) (y := x!) (hxy :=
                            x!_ne_the.symm) (vx := some Xt!) (vy := some X!opt)] using
                        hφ_the_x
                    have hDspec_raw_swapped :
                        ⟦the_x!_spec.abstract
                            (Function.update (Function.update «Δ» the_x! (some Xt!)) x! (some X!opt))
                            hφ_the_x⟧ˢ = some Φt := by
                      rw [
                        ←SMT.RenamingContext.denote,
                        ←SMT.RenamingContext.denote_update_of_notMem
                        («Δ» := Function.update «Δ» the_x! (some Xt!)) (t := the_x!_spec)
                        (x := x!) (d := X!opt) (h := hφt) x!_not_mem_fv_the_spec,
                        SMT.RenamingContext.denote]
                      exact denφt
                    have hDspec_raw :
                        ⟦the_x!_spec.abstract Δgoal hφ_goal⟧ˢ = some Φt := by
                      simpa [Δgoal, update_swap (f := «Δ») (x := the_x!) (y := x!)
                        (hxy := x!_ne_the.symm) (vx := some Xt!) (vy := some X!opt)] using
                        hDspec_raw_swapped
                    have hDspec_ty : Φt.2.1 = .bool := hΦt_ty
                    have hcov_x! : SMT.RenamingContext.CoversFV Δgoal (SMT.Term.var x!) := by
                      intro v hv
                      rw [SMT.fv, List.mem_singleton] at hv
                      subst hv
                      simp only [ne_eq, x!_ne_the, not_false_eq_true, Function.update_of_ne,
                        Function.update, ↓reduceDIte, Option.isSome_some, Δgoal]
                    have hcov_the : SMT.RenamingContext.CoversFV Δgoal (SMT.Term.var the_x!) := by
                      intro v hv
                      rw [SMT.fv, List.mem_singleton] at hv
                      subst hv
                      simp only [Function.update_self, Option.isSome_some, Δgoal]
                    have hden_x! :
                        ⟦(SMT.Term.var x!).abstract Δgoal hcov_x!⟧ˢ = some X!opt := by
                      rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some_inj]
                      apply Option.get_of_eq_some
                      simp [Δgoal, Function.update, x!_ne_the]
                    have hden_the :
                        ⟦(SMT.Term.var the_x!).abstract Δgoal hcov_the⟧ˢ =
                          some Xt! := by
                      rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some_inj]
                      apply Option.get_of_eq_some
                      simp [Δgoal]
                    have hden_some_the :
                        ⟦(SMT.Term.some (SMT.Term.var the_x!)).abstract Δgoal
                            (by
                              intro v hv
                              exact hcov_the v (by simpa [SMT.fv] using hv))⟧ˢ =
                          some X!opt := by
                      rw [SMT.Term.abstract, SMT.denote, Option.bind_eq_bind, Option.pure_def, hden_the]
                      cases hXt!_ty
                      rfl
                    obtain ⟨Deq, hDeq_raw, hDeq_ty⟩ :=
                      denote_eq_some_of_some
                        (h₁ := hden_x!)
                        (h₂ := hden_some_the)
                        (hτ := rfl)
                    obtain ⟨Dbody, hDbody_raw, hDbody_ty⟩ :=
                      denote_and_some_bool_of_some_bool hDeq_raw hDeq_ty hDspec_raw hDspec_ty
                    have hDeq_true : Deq.fst = zftrue := by
                      have hDeq_raw' := hDeq_raw
                      rw [SMT.denote, hden_x!, hden_some_the] at hDeq_raw'
                      simp only [Option.pure_def, Option.failure_eq_none, Option.bind_eq_bind,
                        Option.bind_some] at hDeq_raw'
                      simp at hDeq_raw'
                      have hEq := congrArg (fun d : SMT.Dom => d.fst) hDeq_raw'
                      simpa [overloadBinOp, X!opt, id_eq, Function.onFun, ZFSet.Option.some.injEq]
                        using hEq.symm
                    have hDbody_true : Dbody.fst = zftrue := by
                      have hDbody_raw' := hDbody_raw
                      rw [SMT.denote, hDeq_raw, hDspec_raw] at hDbody_raw'
                      obtain ⟨P, τP, hP⟩ := Deq
                      obtain ⟨Q, τQ, hQ⟩ := Φt
                      dsimp at hDeq_ty hDspec_ty hDbody_raw' hDeq_true hΦt_true
                      cases hDeq_true
                      cases hΦt_true
                      cases hDeq_ty
                      cases hDspec_ty
                      simp at hDbody_raw'
                      have hEq := congrArg (fun d : SMT.Dom => d.fst) hDbody_raw'
                      simpa [overloadBinOp_𝔹, overloadBinOp, id_eq, ZFSet.inter_self]
                        using hEq.symm
                    have hnot_raw :
                        ⟦¬ˢ'
                            (((SMT.Term.var x!).abstract Δgoal hcov_x! =ˢ'
                              (SMT.Term.var the_x!).some.abstract Δgoal
                                (by
                                  intro v hv
                                  exact hcov_the v (by simpa [SMT.fv] using hv))) ∧ˢ'
                              the_x!_spec.abstract Δgoal hφ_goal)⟧ˢ =
                          some ⟨zffalse, SMTType.bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
                      rw [SMT.denote, hDbody_raw]
                      cases hτ : Dbody.snd.fst with
                      | bool =>
                        obtain ⟨B, τB, hB⟩ := Dbody
                        dsimp at hτ hDbody_true ⊢
                        cases hτ
                        subst B
                        simp only [overloadUnaryOp, mem_insert_iff, subset_refl, subset_of_empty, mem_singleton, or_true, id_eq,
                          Option.some.injEq, PSigma.mk.injEq, ↓reduceDIte, ZFSet.symmDiff_self, true_and]
                        congr
                        · funext τ
                          rw [dif_pos hB]
                          simp only [ZFSet.symmDiff_self]
                        · apply proof_irrel_heq
                      | _ =>
                        simp [hτ] at hDbody_ty
                    have hnot_get :
                        zffalse =
                          (⟦¬ˢ'
                              (((SMT.Term.var x!).abstract Δgoal hcov_x! =ˢ'
                                (SMT.Term.var the_x!).some.abstract Δgoal
                                  (by
                                    intro v hv
                                    exact hcov_the v (by simpa [SMT.fv] using hv))) ∧ˢ'
                                the_x!_spec.abstract Δgoal hφ_goal)⟧ˢ.get
                            (denote_not_isSome_of_some_bool hDbody_raw hDbody_ty)).fst := by
                      conv_rhs =>
                        enter [1, 1]
                        rw [hnot_raw]
                      rw [Option.get_some]
                    simpa [SMT.Term.abstract, SMT.denote, Δgoal, proof_irrel_heq] using hnot_get
                  refine ⟨this, ?_⟩
                  congr
                  · funext τ
                    apply congrArg (fun z => z ∈ ⟦τ⟧ᶻ)
                    simp only [Fin.foldl_zero, Fin.val_eq_zero, List.getElem_cons_zero,
                      forall_const, Option.get_bind]
                    exact this
                  · apply proof_irrel_heq
                · exfalso
                  apply den_t_isSome
                  intro x_1 hx_1
                  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, overloadUnaryOp,
                    id_eq, Option.pure_def, Option.failure_eq_none, Option.bind_eq_bind]
                  unfold SMT.Term.abstract.go
                  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Matrix.head_fin_const]
                  let i0 : Fin [the_x!].length := ⟨0, hlen_pos⟩
                  have hx0 : (x_1 i0).2.1 = α' ∧ (x_1 i0).1 ∈ ⟦α'⟧ᶻ := by
                    simpa only [Fin.zero_eta, Fin.isValue, List.getElem_cons_zero] using hx_1 i0
                  have typ_t_St₁ : St₁.types ⊢ˢ t : α := by
                    have : St₁.types ⊢ˢ .some t : α.option := by simpa using typ_x
                    rcases SMT.Typing.someE this with ⟨σ, hσ, htyp⟩
                    cases hσ
                    exact htyp
                  have x!_not_mem_fv_t : x! ∉ SMT.fv t := by
                    intro hx_mem
                    exact x!_fresh (SMT.Typing.mem_context_of_mem_fv typ_t_St₁ hx_mem)
                  have hx_lookup_St₂ : St₂.types.lookup x! = some α'.option := by
                    rw [St₂_types_eq]
                    exact AList.lookup_insert St₁.types
                  have hx_mem_St₂ : x! ∈ St₂.types := by
                    exact (AList.lookup_isSome).1 (Option.isSome_of_eq_some hx_lookup_St₂)
                  have x!_ne_the : x! ≠ the_x! := by
                    intro h
                    subst h
                    exact the_x!_fresh hx_mem_St₂
                  have x!_not_mem_fv_the_spec : x! ∉ SMT.fv the_x!_spec := by
                    intro hx_mem
                    have hx' := fv_the_x!_spec hx_mem
                    rw [List.mem_union_iff] at hx'
                    rcases hx' with hxt | hxthe
                    · exact x!_not_mem_fv_t hxt
                    · exact x!_ne_the (List.mem_singleton.mp hxthe)
                  have hφ_the :
                      SMT.RenamingContext.CoversFV (Function.update «Δ» the_x! (some (x_1 i0))) the_x!_spec := by
                    intro v hv
                    by_cases hvthe : v = the_x!
                    · subst hvthe
                      simp
                    · rw [Function.update_of_ne hvthe]
                      have hv' := fv_the_x!_spec hv
                      rw [List.mem_union_iff] at hv'
                      rcases hv' with hvt | hvthe'
                      · exact hx_t v hvt
                      · exact (hvthe (List.mem_singleton.mp hvthe')).elim
                  have hspec_some_the :
                      (SMT.RenamingContext.denote (Function.update «Δ» the_x! (some (x_1 i0)))
                        the_x!_spec hφ_the).isSome = true := by
                    exact (htot_t (x_1 i0) hx0.1 hφ_the).1
                  have hφ_the_x :
                      SMT.RenamingContext.CoversFV
                        (Function.update (Function.update «Δ» the_x! (some (x_1 i0))) x! (some X!opt)) the_x!_spec :=
                    SMT.RenamingContext.coversFV_update_of_notMem
                      (x := x!) (d := X!opt) x!_not_mem_fv_the_spec hφ_the
                  have hspec_some_the_x :
                      (SMT.RenamingContext.denote
                        (Function.update (Function.update «Δ» the_x! (some (x_1 i0))) x! (some X!opt))
                        the_x!_spec hφ_the_x).isSome = true := by
                    rw [← denote_isSome_update_of_notMem
                      («Δ» := Function.update «Δ» the_x! (some (x_1 i0))) (t := the_x!_spec)
                      (x := x!) (d := X!opt) (h := hφ_the) x!_not_mem_fv_the_spec]
                    exact hspec_some_the
                  have hφ_goal :
                      SMT.RenamingContext.CoversFV
                        (Function.update (Function.update «Δ» x! (some X!opt)) the_x! (some (x_1 i0))) the_x!_spec := by
                    simpa [update_swap (f := «Δ») (x := the_x!) (y := x!) (hxy := x!_ne_the.symm)
                      (vx := some (x_1 i0)) (vy := some X!opt)] using hφ_the_x
                  have hspec_some_goal_ctx :
                      (SMT.RenamingContext.denote
                        (Function.update (Function.update «Δ» x! (some X!opt)) the_x! (some (x_1 i0)))
                        the_x!_spec hφ_goal).isSome = true := by
                    simpa [update_swap (f := «Δ») (x := the_x!) (y := x!) (hxy := x!_ne_the.symm)
                      (vx := some (x_1 i0)) (vy := some X!opt)] using hspec_some_the_x
                  obtain ⟨Dspec, hDspec_ctx⟩ := Option.isSome_iff_exists.mp hspec_some_goal_ctx
                  have hDspec_raw :
                      ⟦the_x!_spec.abstract
                          (Function.update (Function.update «Δ» x! (some X!opt)) the_x! (some (x_1 i0)))
                          hφ_goal⟧ˢ = some Dspec := by
                    simpa [SMT.RenamingContext.denote] using hDspec_ctx
                  have hDspec_ty : Dspec.2.1 = .bool := by
                    exact denote_type_eq_of_typing (typ_t := typ_the_x!_spec_St₃) (hden := hDspec_raw)
                  let Δgoal : SMT.RenamingContext.Context :=
                    Function.update (Function.update «Δ» x! (some X!opt)) the_x! (some (x_1 i0))
                  have hcov_x! : SMT.RenamingContext.CoversFV Δgoal (SMT.Term.var x!) := by
                    intro v hv
                    rw [SMT.fv, List.mem_singleton] at hv
                    subst hv
                    simp [Δgoal, Function.update, x!_ne_the]
                  have hcov_the : SMT.RenamingContext.CoversFV Δgoal (SMT.Term.var the_x!) := by
                    intro v hv
                    rw [SMT.fv, List.mem_singleton] at hv
                    subst hv
                    simp [Δgoal]
                  have hden_x! :
                      ⟦(SMT.Term.var x!).abstract Δgoal hcov_x!⟧ˢ = some X!opt := by
                    rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some_inj]
                    apply Option.get_of_eq_some
                    simp [Δgoal, Function.update, x!_ne_the]
                  have hden_the :
                      ⟦(SMT.Term.var the_x!).abstract Δgoal hcov_the⟧ˢ = some (x_1 i0) := by
                    rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some_inj]
                    apply Option.get_of_eq_some
                    simp [Δgoal]
                  have hden_some_the :
                      ⟦(SMT.Term.some (SMT.Term.var the_x!)).abstract Δgoal
                          (by
                            intro v hv
                            exact hcov_the v (by simpa [SMT.fv] using hv))⟧ˢ =
                        some ⟨(ZFSet.Option.some ⟨(x_1 i0).fst, by simpa [hx0.1] using hx0.2⟩).1, α'.option,
                          SetLike.coe_mem (ZFSet.Option.some ⟨(x_1 i0).fst, by simpa [hx0.1] using hx0.2⟩)⟩ := by
                    rw [SMT.Term.abstract, SMT.denote, Option.bind_eq_bind, Option.pure_def, hden_the]
                    cases hx0.1
                    rfl
                  obtain ⟨Deq, hDeq_raw, hDeq_ty⟩ :=
                    denote_eq_some_of_some
                      (h₁ := hden_x!)
                      (h₂ := hden_some_the)
                      (hτ := rfl)
                  obtain ⟨Dbody, hDbody_raw, hDbody_ty⟩ :=
                    denote_and_some_bool_of_some_bool hDeq_raw hDeq_ty hDspec_raw hDspec_ty
                  have hnot_some :=
                    denote_not_isSome_of_some_bool (hden := hDbody_raw) (hTy := hDbody_ty)
                  simpa [SMT.Term.abstract, SMT.denote, Option.bind_eq_bind, Option.pure_def,
                    SMT.Term.abstract.go, Function.OfArity.uncurry, Function.FromTypes.uncurry,
                    Δgoal, i0, proof_irrel_heq] using hnot_some
              · simp [overloadUnaryOp]
                congr
                simp only [subset_refl, subset_of_empty, mem_insert_iff, mem_singleton, true_or, ↓reduceDIte, symmDiff_empty]
                apply proof_irrel_heq
            · rfl
            · constructor
              · rfl
              · have hXeq' :
                    (match Xt with
                      | ⟨T, ⟨τ, hTτ⟩⟩ =>
                          ⟨(ZFSet.Option.some ⟨T, hTτ⟩).1, τ.option,
                            SetLike.coe_mem (ZFSet.Option.some ⟨T, hTτ⟩)⟩) = X := by
                  exact Option.some.inj hXeq
                have hX_ty : X.snd.fst = α.option := denote_type_eq_of_typing (typ_t := typ_x_St₂) (hden := denx)
                have hX_mem : X.fst ∈ ⟦α.option⟧ᶻ := by
                  simpa [hX_ty] using X.snd.snd
                rw [castZF_of_path, castZF_option]
                rw [ZFSet.lambda_spec]
                refine ⟨hX_mem, ?_, ?_⟩
                · exact SetLike.coe_mem (ZFSet.Option.some ⟨Xt!.fst, hXt!_memα'⟩)
                · have hXt_ty : Xt.snd.fst = α := denote_type_eq_of_typing (typ_t := typ_t_St₂) (hden := den_t)
                  have hXt_memα : Xt.fst ∈ ⟦α⟧ᶻ := by
                    simpa only [hXt_ty] using Xt.snd.snd
                  have hX_fst_eq : X.fst = (ZFSet.Option.some ⟨Xt.fst, hXt_memα⟩).1 := by
                    simpa only using congrArg (fun d => d.fst) hXeq'.symm
                  have hX_not_none : X.fst ≠ (ZFSet.Option.none (S := ⟦α⟧ᶻ)).1 := by
                    rw [hX_fst_eq]
                    intro h
                    exact ZFSet.Option.some_ne_none ⟨Xt.fst, hXt_memα⟩ (Subtype.ext (by simpa using h))
                  simp only [hX_mem, ↓reduceDIte, hX_not_none]
                  let y_def : ∃ y, X.fst = (ZFSet.Option.some (S := ⟦α⟧ᶻ) y).1 := by
                    exact ⟨⟨Xt.fst, hXt_memα⟩, hX_fst_eq⟩
                  have hcast_pfunc :
                      ((castZF_of_path hα).1).IsPFunc ⟦α⟧ᶻ ⟦α'⟧ᶻ :=
                    ZFSet.is_func_is_pfunc (castZF_of_path hα).2
                  change
                    X!opt.fst =
                      (ZFSet.Option.some
                        (ZFSet.fapply (castZF_of_path hα).1 (hf := hcast_pfunc)
                          ⟨(Classical.choose y_def).1,
                            by
                              rw [ZFSet.is_func_dom_eq (castZF_of_path hα).2]
                              exact (Classical.choose y_def).2⟩)).1
                  have hy_choose : X.fst = (ZFSet.Option.some (S := ⟦α⟧ᶻ) (Classical.choose y_def)).1 :=
                    Classical.choose_spec y_def
                  have hchoose_eq : (Classical.choose y_def : {x // x ∈ ⟦α⟧ᶻ}) = ⟨Xt.fst, hXt_memα⟩ := by
                    apply (ZFSet.Option.some.injEq).1
                    apply Subtype.ext
                    exact hy_choose.symm.trans hX_fst_eq
                  have hcast_eq :
                      ZFSet.fapply (castZF_of_path hα).1 (hf := hcast_pfunc)
                        ⟨Xt.fst, by
                          rw [ZFSet.is_func_dom_eq (castZF_of_path hα).2]
                          exact hXt_memα⟩
                        = ⟨Xt!.fst, by simpa [hXt!_ty] using Xt!.snd.snd⟩ := by
                    exact fapply.of_pair (hf := hcast_pfunc) hCast_t
                  have hcast_choose_val :
                      (ZFSet.fapply (castZF_of_path hα).1 (hf := hcast_pfunc)
                        ⟨(Classical.choose y_def).1, by
                          rw [ZFSet.is_func_dom_eq (castZF_of_path hα).2]
                          exact (Classical.choose y_def).2⟩).1 = Xt!.fst := by
                    simpa only [hchoose_eq] using congrArg Subtype.val hcast_eq
                  have hcast_choose :
                      ZFSet.fapply (castZF_of_path hα).1 (hf := hcast_pfunc)
                        ⟨(Classical.choose y_def).1, by
                          rw [ZFSet.is_func_dom_eq (castZF_of_path hα).2]
                          exact (Classical.choose y_def).2⟩
                        = ⟨Xt!.fst, by simpa [hXt!_ty] using Xt!.snd.snd⟩ := by
                    apply Subtype.ext
                    exact hcast_choose_val
                  simp only [hcast_choose, X!opt]
            · intro Y hY hφY
              rw [SMT.Term.abstract, dite_cond_eq_true (eq_true (by rfl)), SMT.PHOAS.Term.exists, SMT.denote]
              simp only [Option.bind_eq_bind, Option.pure_def]
              have hlen_pos : [the_x!].length > 0 := by simp
              rw [SMT.denote, dite_cond_eq_true (eq_true hlen_pos)]
              split_ifs with den_t_isSome
              · constructor
                · simp
                · intro ΦY hdenY hExistsTrue0
                  have hdenY' := hdenY
                  simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_some] at hdenY'
                  have hExistsTrue := by
                    simpa using
                      (congrArg (fun d : SMT.Dom => d.fst) (Option.some.inj hdenY')).trans hExistsTrue0
                  by_contra hnotmem
                  have hcontra : False := by
                    have hΔ_body :
                      ∀ v ∈ SMT.fv ((SMT.Term.var x! =ˢ (SMT.Term.var the_x!).some) ∧ˢ the_x!_spec),
                        v ∉ [the_x!] → (Function.update «Δ» x! (some Y) v).isSome = true := by
                      intro v hv hv_not_vs
                      have hv' : v = x! ∨ v = the_x! ∨ v ∈ SMT.fv the_x!_spec := by
                        simpa [SMT.fv, List.mem_union_iff, List.mem_append, List.mem_singleton, or_assoc]
                          using hv
                      rcases hv' with rfl | rfl | hvspec
                      · simp
                      · exfalso
                        exact hv_not_vs (by simp)
                      · have hvspec' := fv_the_x!_spec hvspec
                        rw [List.mem_union_iff] at hvspec'
                        rcases hvspec' with hvt | hvthe
                        · by_cases hvx : v = x!
                          · subst hvx
                            simp
                          · rw [Function.update_of_ne hvx]
                            exact hx_t v hvt
                        · exfalso
                          exact hv_not_vs (by simpa using List.mem_singleton.mp hvthe)
                    have hXeq' := Option.some.inj hXeq
                    have hXt_ty : Xt.snd.fst = α := by
                      exact denote_type_eq_of_typing (typ_t := typ_t_St₂) (hden := den_t)
                    have hXt_memα : Xt.fst ∈ ⟦α⟧ᶻ := by
                      simpa [hXt_ty] using Xt.snd.snd
                    have hX_ty : X.snd.fst = α.option := by
                      exact denote_type_eq_of_typing (typ_t := typ_x_St₂) (hden := denx)
                    have hX_mem : X.fst ∈ ⟦α.option⟧ᶻ := by
                      simpa [hX_ty] using X.snd.snd
                    have hX_fst_eq : X.fst = (ZFSet.Option.some ⟨Xt.fst, hXt_memα⟩).1 := by
                      simpa only using congrArg (fun d : SMT.Dom => d.fst) hXeq'.symm
                    have hX_not_none : X.fst ≠ (ZFSet.Option.none (S := ⟦α⟧ᶻ)).1 := by
                      rw [hX_fst_eq]
                      intro h
                      exact ZFSet.Option.some_ne_none ⟨Xt.fst, hXt_memα⟩
                        (Subtype.ext (by simpa using h))
                    have hcast_opt_of {y' : {y // y ∈ ⟦α'⟧ᶻ}}
                        (hcast : Xt.fst.pair y'.1 ∈ (castZF_of_path hα).1) :
                        X.fst.pair (ZFSet.Option.some y').1 ∈ (castZF_of_path hα.opt).1 := by
                      rw [castZF_of_path, castZF_option, ZFSet.lambda_spec]
                      refine ⟨hX_mem, SetLike.coe_mem (ZFSet.Option.some y'), ?_⟩
                      simp only [hX_mem, ↓reduceDIte, hX_not_none]
                      let y_def : ∃ y, X.fst = (ZFSet.Option.some (S := ⟦α⟧ᶻ) y).1 := by
                        exact ⟨⟨Xt.fst, hXt_memα⟩, hX_fst_eq⟩
                      have hcast_pfunc :
                          ((castZF_of_path hα).1).IsPFunc ⟦α⟧ᶻ ⟦α'⟧ᶻ :=
                        ZFSet.is_func_is_pfunc (castZF_of_path hα).2
                      change
                        (ZFSet.Option.some y').1 =
                          (ZFSet.Option.some
                            (ZFSet.fapply (castZF_of_path hα).1 (hf := hcast_pfunc)
                              ⟨(Classical.choose y_def).1, by
                                rw [ZFSet.is_func_dom_eq (castZF_of_path hα).2]
                                exact (Classical.choose y_def).2⟩)).1
                      have hy_choose :
                          X.fst = (ZFSet.Option.some (S := ⟦α⟧ᶻ) (Classical.choose y_def)).1 :=
                        Classical.choose_spec y_def
                      have hchoose_eq :
                          (Classical.choose y_def : {x // x ∈ ⟦α⟧ᶻ}) = ⟨Xt.fst, hXt_memα⟩ := by
                        apply (ZFSet.Option.some.injEq).1
                        apply Subtype.ext
                        exact hy_choose.symm.trans hX_fst_eq
                      have hcast_eq :
                          ZFSet.fapply (castZF_of_path hα).1 (hf := hcast_pfunc)
                            ⟨Xt.fst, by
                              rw [ZFSet.is_func_dom_eq (castZF_of_path hα).2]
                              exact hXt_memα⟩
                            = y' := by
                        exact fapply.of_pair (hf := hcast_pfunc) hcast
                      have hcast_choose_val :
                          (ZFSet.fapply (castZF_of_path hα).1 (hf := hcast_pfunc)
                            ⟨(Classical.choose y_def).1, by
                              rw [ZFSet.is_func_dom_eq (castZF_of_path hα).2]
                              exact (Classical.choose y_def).2⟩).1 = y'.1 := by
                        simpa only [hchoose_eq] using congrArg Subtype.val hcast_eq
                      have hcast_choose :
                          ZFSet.fapply (castZF_of_path hα).1 (hf := hcast_pfunc)
                            ⟨(Classical.choose y_def).1, by
                              rw [ZFSet.is_func_dom_eq (castZF_of_path hα).2]
                              exact (Classical.choose y_def).2⟩
                            = y' := by
                        apply Subtype.ext
                        exact hcast_choose_val
                      simpa only [hcast_choose]
                    let bodyF : ZFSet → ZFSet := fun y =>
                      if hy : y.hasArity 1 ∧ y ∈ ⟦α'⟧ᶻ then
                        (⟦¬ˢ'
                            (Term.abstract.go
                              ((SMT.Term.var x! =ˢ (SMT.Term.var the_x!).some) ∧ˢ the_x!_spec)
                              [the_x!]
                              (Function.update «Δ» x! (some Y))
                              hΔ_body).uncurry
                              (fun i => ⟨y, [α'][i], by
                                cases i with
                                | mk i hi =>
                                    simp at hi
                                    subst hi
                                    exact hy.2⟩)⟧ˢ.get
                          (den_t_isSome (fun i => by
                            refine ⟨rfl, ?_⟩
                            cases i with
                            | mk i hi =>
                                simp at hi
                                subst hi
                                exact hy.2))).fst
                      else
                        ∅
                    have typ_t_St₁ : St₁.types ⊢ˢ t : α := by
                      have : St₁.types ⊢ˢ .some t : α.option := by simpa using typ_x
                      rcases SMT.Typing.someE this with ⟨σ, hσ, htyp⟩
                      cases hσ
                      simpa only using htyp
                    have x!_not_mem_fv_t : x! ∉ SMT.fv t := by
                      intro hx_mem
                      exact x!_fresh (SMT.Typing.mem_context_of_mem_fv typ_t_St₁ hx_mem)
                    have hall : ∀ y ∈ ⟦α'⟧ᶻ, bodyF y = zftrue := by
                      intro y hy
                      let wy : Fin [the_x!].length → SMT.Dom := fun i =>
                        ⟨y, [α'][i], by
                          cases i with
                          | mk i hi =>
                              simp at hi
                              subst hi
                              exact hy⟩
                      have hwy : ∀ i : Fin [the_x!].length, (wy i).snd.fst = [α'][i] ∧ (wy i).fst ∈ ⟦[α'][i]⟧ᶻ := by
                        intro i
                        refine ⟨rfl, ?_⟩
                        cases i with
                        | mk i hi =>
                            simp at hi
                            subst hi
                            exact hy
                      have hy1 : y.hasArity 1 ∧ y ∈ ⟦α'⟧ᶻ := by
                        constructor
                        · simp [ZFSet.hasArity]
                        · exact hy
                      have hbodyF_y :
                          bodyF y =
                            (⟦¬ˢ'
                                (Term.abstract.go
                                  ((SMT.Term.var x! =ˢ (SMT.Term.var the_x!).some) ∧ˢ the_x!_spec)
                                  [the_x!]
                                  (Function.update «Δ» x! (some Y))
                                  hΔ_body).uncurry wy⟧ˢ.get
                              (den_t_isSome hwy)).fst := by
                        simpa [bodyF, wy, hwy, hy1, proof_irrel_heq]
                      let i0 : Fin [the_x!].length := ⟨0, hlen_pos⟩
                      have hx0 : (wy i0).2.1 = α' ∧ (wy i0).1 ∈ ⟦α'⟧ᶻ := by
                        simpa only [i0, Fin.zero_eta, Fin.isValue] using hwy i0
                      have hx_lookup_St₂ : St₂.types.lookup x! = some α'.option := by
                        rw [St₂_types_eq]
                        exact AList.lookup_insert St₁.types
                      have hx_mem_St₂ : x! ∈ St₂.types := by
                        exact (AList.lookup_isSome).1 (Option.isSome_of_eq_some hx_lookup_St₂)
                      have x!_ne_the : x! ≠ the_x! := by
                        intro h
                        subst h
                        exact the_x!_fresh hx_mem_St₂
                      have x!_not_mem_fv_the_spec : x! ∉ SMT.fv the_x!_spec := by
                        intro hx_mem
                        have hx' := fv_the_x!_spec hx_mem
                        rw [List.mem_union_iff] at hx'
                        rcases hx' with hxt | hxthe
                        · exact x!_not_mem_fv_t hxt
                        · exact x!_ne_the (List.mem_singleton.mp hxthe)
                      have hφ_the :
                          SMT.RenamingContext.CoversFV (Function.update «Δ» the_x! (some (wy i0))) the_x!_spec := by
                        intro v hv
                        by_cases hvthe : v = the_x!
                        · subst hvthe
                          simp
                        · rw [Function.update_of_ne hvthe]
                          have hv' := fv_the_x!_spec hv
                          rw [List.mem_union_iff] at hv'
                          rcases hv' with hvt | hvthe'
                          · exact hx_t v hvt
                          · exact (hvthe (List.mem_singleton.mp hvthe')).elim
                      have hspec_some_the :
                          (SMT.RenamingContext.denote (Function.update «Δ» the_x! (some (wy i0)))
                            the_x!_spec hφ_the).isSome = true := by
                        exact (htot_t (wy i0) hx0.1 hφ_the).1
                      have hφ_the_x :
                          SMT.RenamingContext.CoversFV
                            (Function.update (Function.update «Δ» the_x! (some (wy i0))) x! (some Y)) the_x!_spec :=
                        SMT.RenamingContext.coversFV_update_of_notMem
                          (x := x!) (d := Y) x!_not_mem_fv_the_spec hφ_the
                      have hspec_some_the_x :
                          (SMT.RenamingContext.denote
                            (Function.update (Function.update «Δ» the_x! (some (wy i0))) x! (some Y))
                            the_x!_spec hφ_the_x).isSome = true := by
                        rw [← denote_isSome_update_of_notMem
                          («Δ» := Function.update «Δ» the_x! (some (wy i0))) (t := the_x!_spec)
                          (x := x!) (d := Y) (h := hφ_the) x!_not_mem_fv_the_spec]
                        exact hspec_some_the
                      have hφ_goal :
                          SMT.RenamingContext.CoversFV
                            (Function.update (Function.update «Δ» x! (some Y)) the_x! (some (wy i0))) the_x!_spec := by
                        simpa [update_swap (f := «Δ») (x := the_x!) (y := x!) (hxy := x!_ne_the.symm)
                          (vx := some (wy i0)) (vy := some Y)] using hφ_the_x
                      obtain ⟨Dspec, hDspec_ctx_the_x⟩ := Option.isSome_iff_exists.mp hspec_some_the_x
                      have hDspec_ctx_the :
                          SMT.RenamingContext.denote (Function.update «Δ» the_x! (some (wy i0)))
                            the_x!_spec hφ_the = some Dspec := by
                        have hctx :
                            SMT.RenamingContext.denote (Function.update «Δ» the_x! (some (wy i0)))
                              the_x!_spec hφ_the =
                              SMT.RenamingContext.denote
                                (Function.update (Function.update «Δ» the_x! (some (wy i0))) x! (some Y))
                                the_x!_spec hφ_the_x := by
                          simpa [hφ_the_x] using
                            (SMT.RenamingContext.denote_update_of_notMem
                              («Δ» := Function.update «Δ» the_x! (some (wy i0))) (t := the_x!_spec)
                              (x := x!) (d := Y) (h := hφ_the) x!_not_mem_fv_the_spec)
                        exact hctx.trans hDspec_ctx_the_x
                      have hDspec_raw_the :
                          ⟦the_x!_spec.abstract (Function.update «Δ» the_x! (some (wy i0))) hφ_the⟧ˢ =
                            some Dspec := by
                        simpa [SMT.RenamingContext.denote] using hDspec_ctx_the
                      have hDspec_raw :
                          ⟦the_x!_spec.abstract
                              (Function.update (Function.update «Δ» x! (some Y)) the_x! (some (wy i0)))
                              hφ_goal⟧ˢ = some Dspec := by
                        simpa [SMT.RenamingContext.denote, update_swap (f := «Δ») (x := the_x!) (y := x!)
                          (hxy := x!_ne_the.symm) (vx := some (wy i0)) (vy := some Y), proof_irrel_heq] using
                          hDspec_ctx_the_x
                      have hDspec_ty : Dspec.2.1 = .bool := by
                        exact denote_type_eq_of_typing (typ_t := typ_the_x!_spec_St₃) (hden := hDspec_raw)
                      let Δgoal : SMT.RenamingContext.Context :=
                        Function.update (Function.update «Δ» x! (some Y)) the_x! (some (wy i0))
                      have hcov_x! : SMT.RenamingContext.CoversFV Δgoal (SMT.Term.var x!) := by
                        intro v hv
                        rw [SMT.fv, List.mem_singleton] at hv
                        subst hv
                        simp [Δgoal, Function.update, x!_ne_the]
                      have hcov_the : SMT.RenamingContext.CoversFV Δgoal (SMT.Term.var the_x!) := by
                        intro v hv
                        rw [SMT.fv, List.mem_singleton] at hv
                        subst hv
                        simp only [Function.update_self, Option.isSome_some, Δgoal]
                      have hden_x! :
                          ⟦(SMT.Term.var x!).abstract Δgoal hcov_x!⟧ˢ = some Y := by
                        rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some_inj]
                        apply Option.get_of_eq_some
                        simp only [ne_eq, x!_ne_the, not_false_eq_true, Function.update_of_ne,
                          Function.update, ↓reduceDIte, Δgoal]
                      have hden_the :
                          ⟦(SMT.Term.var the_x!).abstract Δgoal hcov_the⟧ˢ = some (wy i0) := by
                        rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some_inj]
                        apply Option.get_of_eq_some
                        simp [Δgoal]
                      have hden_some_the :
                          ⟦(SMT.Term.some (SMT.Term.var the_x!)).abstract Δgoal
                              (by
                                intro v hv
                                exact hcov_the v (by simpa [SMT.fv] using hv))⟧ˢ =
                            some ⟨(ZFSet.Option.some ⟨(wy i0).fst, by simpa [hx0.1] using hx0.2⟩).1, α'.option,
                              SetLike.coe_mem (ZFSet.Option.some ⟨(wy i0).fst, by simpa [hx0.1] using hx0.2⟩)⟩ := by
                        rw [SMT.Term.abstract, SMT.denote, Option.bind_eq_bind, Option.pure_def, hden_the]
                        cases hx0.1
                        rfl
                      obtain ⟨Deq, hDeq_raw, hDeq_ty⟩ :=
                        denote_eq_some_of_some
                          (h₁ := hden_x!)
                          (h₂ := hden_some_the)
                          (hτ := hY)
                      obtain ⟨Dbody, hDbody_raw, hDbody_ty⟩ :=
                        denote_and_some_bool_of_some_bool hDeq_raw hDeq_ty hDspec_raw hDspec_ty
                      by_cases hYeq :
                          Y.fst =
                            (ZFSet.Option.some ⟨(wy i0).fst, by simpa [hx0.1] using hx0.2⟩).1
                      · have hDeq_true : Deq.fst = zftrue := by
                          have hDeq_raw_true :
                              ⟦(SMT.Term.var x!).abstract Δgoal hcov_x! =ˢ'
                                  (SMT.Term.var the_x!).some.abstract Δgoal
                                    (by
                                      intro v hv
                                      exact hcov_the v (by simpa [SMT.fv] using hv))⟧ˢ =
                                some ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
                            exact denote_eq_eq_zftrue_of_fst_eq hden_x! hden_some_the hY hYeq
                          have hEq : some Deq = some ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
                            exact hDeq_raw.symm.trans hDeq_raw_true
                          exact congrArg (fun d : SMT.Dom => d.fst) (Option.some.inj hEq)
                        have hDspec_bool : Dspec.fst = zftrue ∨ Dspec.fst = zffalse := by
                          have hDspec_mem_bool : Dspec.fst ∈ 𝔹 := by
                            simpa [hDspec_ty] using Dspec.snd.snd
                          simpa [ZFSet.ZFBool.mem_𝔹_iff, or_comm] using hDspec_mem_bool
                        have hDspec_false : Dspec.fst = zffalse := by
                          rcases hDspec_bool with hDspec_true | hDspec_false
                          · exfalso
                            apply hnotmem
                            have hcast_under :
                                Xt.fst.pair (wy i0).fst ∈ (castZF_of_path hα).1 := by
                              exact (htot_t (wy i0) hx0.1 hφ_the).2 hDspec_raw_the hDspec_true
                            have hcast_opt :
                                X.fst.pair
                                  (ZFSet.Option.some ⟨(wy i0).fst, by simpa [hx0.1] using hx0.2⟩).1 ∈
                                    (castZF_of_path hα.opt).1 :=
                              hcast_opt_of hcast_under
                            simpa [hYeq] using hcast_opt
                          · exact hDspec_false
                        have hDbody_false_raw :
                            ⟦((SMT.Term.var x!).abstract Δgoal hcov_x! =ˢ'
                                (SMT.Term.var the_x!).some.abstract Δgoal
                                  (by
                                    intro v hv
                                    exact hcov_the v (by simpa [SMT.fv] using hv))) ∧ˢ'
                              the_x!_spec.abstract Δgoal hφ_goal⟧ˢ =
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
                                  (SMT.Term.var the_x!).some.abstract Δgoal
                                    (by
                                      intro v hv
                                      exact hcov_the v (by simpa [SMT.fv] using hv))) ∧ˢ'
                                  the_x!_spec.abstract Δgoal hφ_goal)⟧ˢ =
                              some ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
                          exact denote_not_eq_zftrue_of_some_zffalse hDbody_raw hDbody_ty hDbody_false
                        have hnot_get :
                            zftrue =
                              (⟦¬ˢ'
                                  (((SMT.Term.var x!).abstract Δgoal hcov_x! =ˢ'
                                    (SMT.Term.var the_x!).some.abstract Δgoal
                                      (by
                                        intro v hv
                                        exact hcov_the v (by simpa [SMT.fv] using hv))) ∧ˢ'
                                    the_x!_spec.abstract Δgoal hφ_goal)⟧ˢ.get
                                (denote_not_isSome_of_some_bool hDbody_raw hDbody_ty)).fst := by
                          conv_rhs =>
                            enter [1, 1]
                            rw [hnot_raw]
                          rw [Option.get_some]
                        calc
                          bodyF y =
                              (⟦¬ˢ'
                                  (Term.abstract.go
                                    ((SMT.Term.var x! =ˢ (SMT.Term.var the_x!).some) ∧ˢ the_x!_spec)
                                  [the_x!]
                                  (Function.update «Δ» x! (some Y))
                                  hΔ_body).uncurry wy⟧ˢ.get
                                (den_t_isSome hwy)).fst := hbodyF_y
                          _ = zftrue := by
                            simpa [SMT.Term.abstract, SMT.denote, SMT.Term.abstract.go,
                              Function.OfArity.uncurry, Function.FromTypes.uncurry, Δgoal, i0, wy, hwy,
                              proof_irrel_heq] using hnot_get.symm
                      · have hDeq_false : Deq.fst = zffalse := by
                          have hDeq_mem_bool : Deq.fst ∈ 𝔹 := by
                            simpa [hDeq_ty] using Deq.snd.snd
                          have hDeq_bool : Deq.fst = zftrue ∨ Deq.fst = zffalse := by
                            simpa [ZFSet.ZFBool.mem_𝔹_iff, or_comm] using hDeq_mem_bool
                          rcases hDeq_bool with hDeq_true | hDeq_false
                          · exfalso
                            exact hYeq <|
                              denote_eq_true_implies_fst_eq hden_x! hden_some_the hY hDeq_raw hDeq_true
                          · exact hDeq_false
                        have hDbody_false_raw :
                            ⟦((SMT.Term.var x!).abstract Δgoal hcov_x! =ˢ'
                                (SMT.Term.var the_x!).some.abstract Δgoal
                                  (by
                                    intro v hv
                                    exact hcov_the v (by simpa [SMT.fv] using hv))) ∧ˢ'
                              the_x!_spec.abstract Δgoal hφ_goal⟧ˢ =
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
                                  (SMT.Term.var the_x!).some.abstract Δgoal
                                    (by
                                      intro v hv
                                      exact hcov_the v (by simpa [SMT.fv] using hv))) ∧ˢ'
                                  the_x!_spec.abstract Δgoal hφ_goal)⟧ˢ =
                              some ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
                          exact denote_not_eq_zftrue_of_some_zffalse hDbody_raw hDbody_ty hDbody_false
                        have hnot_get :
                            zftrue =
                              (⟦¬ˢ'
                                  (((SMT.Term.var x!).abstract Δgoal hcov_x! =ˢ'
                                    (SMT.Term.var the_x!).some.abstract Δgoal
                                      (by
                                        intro v hv
                                        exact hcov_the v (by simpa [SMT.fv] using hv))) ∧ˢ'
                                    the_x!_spec.abstract Δgoal hφ_goal)⟧ˢ.get
                                (denote_not_isSome_of_some_bool hDbody_raw hDbody_ty)).fst := by
                          conv_rhs =>
                            enter [1, 1]
                            rw [hnot_raw]
                          rw [Option.get_some]
                        calc
                          bodyF y =
                              (⟦¬ˢ'
                                  (Term.abstract.go
                                    ((SMT.Term.var x! =ˢ (SMT.Term.var the_x!).some) ∧ˢ the_x!_spec)
                                  [the_x!]
                                  (Function.update «Δ» x! (some Y))
                                  hΔ_body).uncurry wy⟧ˢ.get
                                (den_t_isSome hwy)).fst := hbodyF_y
                          _ = zftrue := by
                            simpa [SMT.Term.abstract, SMT.denote, SMT.Term.abstract.go,
                              Function.OfArity.uncurry, Function.FromTypes.uncurry, Δgoal, i0, wy, hwy,
                              proof_irrel_heq] using hnot_get.symm
                    have hne : ∃ x, x ∈ ⟦α'⟧ᶻ := ZFSet.nonempty_exists_iff.mp SMTType.toZFSet_nonempty
                    have houter_false :
                        overloadUnaryOp id id ZFBool.false ZFBool.not
                          (⋂₀ ZFSet.sep (fun y => ∃ x ∈ ⟦α'⟧ᶻ, y = bodyF x) 𝔹) = zffalse := by
                      have hsInter_mem :
                          (⋂₀ ZFSet.sep (fun y => ∃ x ∈ ⟦α'⟧ᶻ, y = bodyF x) 𝔹) ∈ 𝔹 :=
                        ZFSet.sInter_sep_subset_of_𝔹_mem_𝔹 (fun _ => id)
                      simpa [overloadUnaryOp, hsInter_mem, id_eq, proof_irrel_heq] using
                        not_sInter_sep_eq_zffalse_of_forall_eq_zftrue hne hall
                    have hExistsTrue_body :
                        overloadUnaryOp id id ZFBool.false ZFBool.not
                          (⋂₀ ZFSet.sep (fun y => ∃ x ∈ ⟦α'⟧ᶻ, y = bodyF x) 𝔹) = zftrue := by
                      simpa [bodyF, SMT.Term.abstract, SMT.denote, SMT.Term.abstract.go,
                        Function.OfArity.uncurry, Function.FromTypes.uncurry, Option.bind_eq_bind,
                        Option.pure_def, overloadUnaryOp, id_eq, proof_irrel_heq] using hExistsTrue
                    have hz : zftrue = zffalse := hExistsTrue_body.symm.trans houter_false
                    exact ZFSet.zftrue_ne_zffalse hz
                  exact hcontra
              · exfalso
                apply den_t_isSome
                intro x_1 hx_1
                simp only [denote, List.length_cons, List.length_nil, Nat.reduceAdd,
                  overloadUnaryOp, id_eq, Option.pure_def, Option.failure_eq_none,
                  Option.bind_eq_bind]
                unfold SMT.Term.abstract.go
                simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Matrix.head_fin_const]
                let i0 : Fin [the_x!].length := ⟨0, hlen_pos⟩
                have hx0 : (x_1 i0).2.1 = α' ∧ (x_1 i0).1 ∈ ⟦α'⟧ᶻ := by
                  simpa only [Fin.zero_eta, Fin.isValue, List.getElem_cons_zero] using hx_1 i0
                have typ_t_St₁ : St₁.types ⊢ˢ t : α := by
                  have : St₁.types ⊢ˢ .some t : α.option := by simpa using typ_x
                  rcases SMT.Typing.someE this with ⟨σ, hσ, htyp⟩
                  cases hσ
                  simpa only using htyp
                have x!_not_mem_fv_t : x! ∉ SMT.fv t := by
                  intro hx_mem
                  exact x!_fresh (SMT.Typing.mem_context_of_mem_fv typ_t_St₁ hx_mem)
                have hx_lookup_St₂ : St₂.types.lookup x! = some α'.option := by
                  rw [St₂_types_eq]
                  exact AList.lookup_insert St₁.types
                have hx_mem_St₂ : x! ∈ St₂.types := by
                  exact (AList.lookup_isSome).1 (Option.isSome_of_eq_some hx_lookup_St₂)
                have x!_ne_the : x! ≠ the_x! := by
                  intro h
                  subst h
                  exact the_x!_fresh hx_mem_St₂
                have x!_not_mem_fv_the_spec : x! ∉ SMT.fv the_x!_spec := by
                  intro hx_mem
                  have hx' := fv_the_x!_spec hx_mem
                  rw [List.mem_union_iff] at hx'
                  rcases hx' with hxt | hxthe
                  · exact x!_not_mem_fv_t hxt
                  · exact x!_ne_the (List.mem_singleton.mp hxthe)
                have hφ_the :
                    SMT.RenamingContext.CoversFV (Function.update «Δ» the_x! (some (x_1 i0))) the_x!_spec := by
                  intro v hv
                  by_cases hvthe : v = the_x!
                  · subst hvthe
                    simp
                  · rw [Function.update_of_ne hvthe]
                    have hv' := fv_the_x!_spec hv
                    rw [List.mem_union_iff] at hv'
                    rcases hv' with hvt | hvthe'
                    · exact hx_t v hvt
                    · exact (hvthe (List.mem_singleton.mp hvthe')).elim
                have hspec_some_the :
                    (SMT.RenamingContext.denote (Function.update «Δ» the_x! (some (x_1 i0)))
                      the_x!_spec hφ_the).isSome = true := by
                  exact (htot_t (x_1 i0) hx0.1 hφ_the).1
                have hφ_the_x :
                    SMT.RenamingContext.CoversFV
                      (Function.update (Function.update «Δ» the_x! (some (x_1 i0))) x! (some Y)) the_x!_spec :=
                  SMT.RenamingContext.coversFV_update_of_notMem
                    (x := x!) (d := Y) x!_not_mem_fv_the_spec hφ_the
                have hspec_some_the_x :
                    (SMT.RenamingContext.denote
                      (Function.update (Function.update «Δ» the_x! (some (x_1 i0))) x! (some Y))
                      the_x!_spec hφ_the_x).isSome = true := by
                  rw [← denote_isSome_update_of_notMem
                    («Δ» := Function.update «Δ» the_x! (some (x_1 i0))) (t := the_x!_spec)
                    (x := x!) (d := Y) (h := hφ_the) x!_not_mem_fv_the_spec]
                  exact hspec_some_the
                have hφ_goal :
                    SMT.RenamingContext.CoversFV
                      (Function.update (Function.update «Δ» x! (some Y)) the_x! (some (x_1 i0))) the_x!_spec := by
                  simpa [update_swap (f := «Δ») (x := the_x!) (y := x!) (hxy := x!_ne_the.symm)
                    (vx := some (x_1 i0)) (vy := some Y)] using hφ_the_x
                have hspec_some_goal_ctx :
                    (SMT.RenamingContext.denote
                      (Function.update (Function.update «Δ» x! (some Y)) the_x! (some (x_1 i0)))
                      the_x!_spec hφ_goal).isSome = true := by
                  simpa [update_swap (f := «Δ») (x := the_x!) (y := x!) (hxy := x!_ne_the.symm)
                    (vx := some (x_1 i0)) (vy := some Y)] using hspec_some_the_x
                obtain ⟨Dspec, hDspec_ctx⟩ := Option.isSome_iff_exists.mp hspec_some_goal_ctx
                have hDspec_raw :
                    ⟦the_x!_spec.abstract
                        (Function.update (Function.update «Δ» x! (some Y)) the_x! (some (x_1 i0)))
                        hφ_goal⟧ˢ = some Dspec := by
                  simpa [SMT.RenamingContext.denote] using hDspec_ctx
                have hDspec_ty : Dspec.2.1 = .bool := by
                  exact denote_type_eq_of_typing (typ_t := typ_the_x!_spec_St₃) (hden := hDspec_raw)
                let Δgoal : SMT.RenamingContext.Context :=
                  Function.update (Function.update «Δ» x! (some Y)) the_x! (some (x_1 i0))
                have hcov_x! : SMT.RenamingContext.CoversFV Δgoal (SMT.Term.var x!) := by
                  intro v hv
                  rw [SMT.fv, List.mem_singleton] at hv
                  subst hv
                  simp [Δgoal, Function.update, x!_ne_the]
                have hcov_the : SMT.RenamingContext.CoversFV Δgoal (SMT.Term.var the_x!) := by
                  intro v hv
                  rw [SMT.fv, List.mem_singleton] at hv
                  subst hv
                  simp only [Function.update_self, Option.isSome_some, Δgoal]
                have hden_x! :
                    ⟦(SMT.Term.var x!).abstract Δgoal hcov_x!⟧ˢ = some Y := by
                  rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some_inj]
                  apply Option.get_of_eq_some
                  simp only [ne_eq, x!_ne_the, not_false_eq_true, Function.update_of_ne,
                    Function.update, ↓reduceDIte, Δgoal]
                have hden_the :
                    ⟦(SMT.Term.var the_x!).abstract Δgoal hcov_the⟧ˢ = some (x_1 i0) := by
                  rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some_inj]
                  apply Option.get_of_eq_some
                  simp only [Function.update_self, Δgoal]
                have hden_some_the :
                    ⟦(SMT.Term.some (SMT.Term.var the_x!)).abstract Δgoal
                        (by
                          intro v hv
                          exact hcov_the v (by simpa [SMT.fv] using hv))⟧ˢ =
                      some ⟨(ZFSet.Option.some ⟨(x_1 i0).fst, by simpa [hx0.1] using hx0.2⟩).1, α'.option,
                        SetLike.coe_mem (ZFSet.Option.some ⟨(x_1 i0).fst, by simpa [hx0.1] using hx0.2⟩)⟩ := by
                  rw [SMT.Term.abstract, SMT.denote, Option.bind_eq_bind, Option.pure_def, hden_the]
                  cases hx0.1
                  rfl
                obtain ⟨Deq, hDeq_raw, hDeq_ty⟩ :=
                  denote_eq_some_of_some
                    (h₁ := hden_x!)
                    (h₂ := hden_some_the)
                    (hτ := hY)
                obtain ⟨Dbody, hDbody_raw, hDbody_ty⟩ :=
                  denote_and_some_bool_of_some_bool hDeq_raw hDeq_ty hDspec_raw hDspec_ty
                have hnot_some :=
                  denote_not_isSome_of_some_bool (hden := hDbody_raw) (hTy := hDbody_ty)
                simpa [SMT.Term.abstract, SMT.denote, Option.bind_eq_bind, Option.pure_def,
                  SMT.Term.abstract.go, Function.OfArity.uncurry, Function.FromTypes.uncurry,
                  Δgoal, i0, proof_irrel_heq] using hnot_some
      · -- fallback branch (`x` is neither `.none` nor `.some _`)
        have hsome' : ∀ t, x ≠ .some t := by
          intro t ht
          exact hsome ⟨t, ht⟩
        simp only [bind_pure_comp, exists_and_left, exists_prop, exists_and_right, PSigma.exists,
          exists_eq_left, mem_insert_iff, subset_refl, subset_of_empty, mem_singleton, WP.map,
          SPred.entails_nil, SPred.down_pure, forall_const]
        have typ_the_x_St₂ : St₂.types ⊢ˢ .the x : α := by
          exact SMT.Typing.the _ _ _ typ_x_St₂
        have hx_the : RenamingContext.CoversFV «Δ» (.the x) := by
          intro v hv
          exact hx v (by simpa [fv] using hv)
        mspec ih_on_Δ (x := .the x) (Λ := St₂.types) (n := St₂.env.freshvarsc) (used := St₂.env.usedVars)
          typ_the_x_St₂ hx_the
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
        · rename_i out_the
          obtain ⟨the_x!, the_x!_spec⟩ := out_the
          mrename_i pre
          mintro ∀St₃
          mpure pre
          obtain ⟨hn₃, St₃_types_eq, the_x!_fresh, the_x!_not_used, used_sub₃, keys_sub₃, preserves_the_x!,
            typ_the_x!, typ_the_x!_spec, typ_the_x!_St₃, typ_the_x!_spec_St₃, fv_the_x!_spec,
            den_the⟩ := pre
          have typ_x!_spec_base :
              (AList.insert x! α'.option St₁.types) ⊢ˢ
                .ite (x =ˢ none$α) (.var x! =ˢ none$α')
                  (.exists [the_x!] [α'] ((.var x! =ˢ .some (.var the_x!)) ∧ˢ the_x!_spec)) : .bool := by
            have the_x!_not_base : the_x! ∉ (AList.insert x! α'.option St₁.types) := by
              intro hmem
              apply the_x!_fresh
              rw [St₂_types_eq]
              exact hmem
            have x_ne_the : x! ≠ the_x! := by
              intro h
              apply the_x!_not_base
              rw [h, AList.mem_insert]
              exact Or.inl rfl
            have typ_the_x!_spec_body :
                (AList.insert the_x! α' (AList.insert x! α'.option St₁.types)) ⊢ˢ the_x!_spec : .bool := by
              rw [←St₂_types_eq]
              exact typ_the_x!_spec
            have typ_var_x_body :
                (AList.insert the_x! α' (AList.insert x! α'.option St₁.types)) ⊢ˢ .var x! : α'.option := by
              apply SMT.Typing.var
              rw [AList.lookup_insert_ne x_ne_the, AList.lookup_insert]
            have typ_var_the_body :
                (AList.insert the_x! α' (AList.insert x! α'.option St₁.types)) ⊢ˢ .var the_x! : α' := by
              apply SMT.Typing.var
              rw [AList.lookup_insert]
            have typ_some_the_body :
                (AList.insert the_x! α' (AList.insert x! α'.option St₁.types)) ⊢ˢ .some (.var the_x!) : α'.option := by
              exact SMT.Typing.some _ _ _ typ_var_the_body
            have typ_eq_body :
                (AList.insert the_x! α' (AList.insert x! α'.option St₁.types))
                  ⊢ˢ (.var x! =ˢ .some (.var the_x!)) : .bool := by
              exact SMT.Typing.eq _ _ _ _ typ_var_x_body typ_some_the_body
            have typ_exists_body :
                (AList.insert x! α'.option St₁.types) ⊢ˢ
                  .exists [the_x!] [α'] ((.var x! =ˢ .some (.var the_x!)) ∧ˢ the_x!_spec) : .bool := by
              have typ_body :
                  (AList.insert the_x! α' (AList.insert x! α'.option St₁.types))
                    ⊢ˢ ((.var x! =ˢ .some (.var the_x!)) ∧ˢ the_x!_spec) : .bool := by
                exact SMT.Typing.and _ _ _ typ_eq_body typ_the_x!_spec_body
              have the_x!_in_body_ctx :
                  the_x! ∈ (AList.insert the_x! α' (AList.insert x! α'.option St₁.types)) := by
                rw [AList.mem_insert]
                exact Or.inl rfl
              have fresh_body :
                  ∀ v ∈ [the_x!], v ∉ bv ((.var x! =ˢ .some (.var the_x!)) ∧ˢ the_x!_spec) := by
                intro v hv
                rw [List.mem_singleton] at hv
                subst hv
                intro hbv
                exact (SMT.Typing.bv_notMem_context typ_body _ hbv) the_x!_in_body_ctx
              have len_eq_vs : [the_x!].length = [α'].length := rfl
              apply SMT.Typing.exists
                (Γ := (AList.insert x! α'.option St₁.types))
                (vs := [the_x!]) (τs := [α']) (len_eq := len_eq_vs)
              · intro v hv
                rw [List.mem_singleton] at hv
                subst hv
                exact the_x!_not_base
              · exact fresh_body
              · simp only [List.length_cons, List.length_nil, zero_add, zero_lt_one]
              · have hupdate :
                  SMT.TypeContext.update (AList.insert x! α'.option St₁.types) [the_x!] [α'] len_eq_vs =
                    AList.insert the_x! α' (AList.insert x! α'.option St₁.types) := by
                  unfold SMT.TypeContext.update
                  simp only [List.length_cons, List.length_nil, zero_add, Fin.cast_eq_self, Fin.getElem_fin,
                    Fin.foldl_succ_last, Fin.coe_ofNat_eq_mod, Nat.mod_succ,
                    List.getElem_cons_zero, Fin.last_zero, Fin.isValue, Fin.foldl_zero]
                rwa [hupdate]
            have typ_x_base :
                (AList.insert x! α'.option St₁.types) ⊢ˢ x : α.option := by
              rwa [←St₂_types_eq]
            have typ_cond_base :
                (AList.insert x! α'.option St₁.types) ⊢ˢ (x =ˢ none$α) : .bool := by
              exact SMT.Typing.eq _ _ _ _ typ_x_base (SMT.Typing.none _ _)
            have typ_then_base :
                (AList.insert x! α'.option St₁.types) ⊢ˢ (.var x! =ˢ none$α') : .bool := by
              have typ_var_x!_base : (AList.insert x! α'.option St₁.types) ⊢ˢ .var x! : α'.option :=
                SMT.Typing.var _ _ _ (AList.lookup_insert St₁.types)
              exact SMT.Typing.eq _ _ _ _ typ_var_x!_base (SMT.Typing.none _ _)
            exact SMT.Typing.ite _ _ _ _ _ typ_cond_base typ_then_base typ_exists_body
          have hfv_exists_sub :
              SMT.fv (.exists [the_x!] [α'] ((.var x! =ˢ .some (.var the_x!)) ∧ˢ the_x!_spec)) ⊆
                SMT.fv x ∪ {x!} := by
            intro v hv
            rw [SMT.fv.eq_def] at hv
            rcases List.mem_removeAll_iff.mp hv with ⟨hv_body, hv_not_bound⟩
            have hv_ne_the : v ≠ the_x! := by
              intro h
              apply hv_not_bound
              simp only [h, List.mem_cons, List.not_mem_nil, or_false]
            have hv_body' : v = x! ∨ v = the_x! ∨ v ∈ fv the_x!_spec := by
              simpa only [fv, List.cons_append, List.nil_append, List.mem_cons] using hv_body
            rw [List.mem_union_iff]
            rcases hv_body' with hvx | hvthe | hvspec
            · subst hvx
              exact Or.inr (List.mem_singleton.mpr rfl)
            · exact (hv_ne_the hvthe).elim
            · have hv' := fv_the_x!_spec hvspec
              rw [List.mem_union_iff] at hv'
              rcases hv' with hvt | hvthe'
              · exact Or.inl (by simpa [fv] using hvt)
              · exact (hv_ne_the (List.mem_singleton.mp hvthe')).elim
          mpure_intro
          and_intros
          · calc
              St₁.env.freshvarsc ≤ St₂.env.freshvarsc := by rw [St₂_fvc]; exact Nat.le_succ _
              _ ≤ St₃.env.freshvarsc := hn₃
          · intro v hv
            have hv₂ : v ∈ St₂.types.entries := by
              simpa [St₂_types_eq] using hv
            exact St₃_types_eq (SMT.TypeContext.entries_subset_insert_of_notMem the_x!_fresh hv₂)
          · exact x!_fresh
          · exact x!_not_used
          · intro v hv
            have hv₂ : v ∈ St₂.env.usedVars := by
              rw [St₂_used_eq]
              exact List.mem_cons_of_mem _ hv
            exact used_sub₃ hv₂
          · exact keys_sub₃
          · -- preserves_types
            intro v hv hv_not_Λ
            have hv_ne_x : v ≠ x! := fun h => absurd (h ▸ hv) x!_not_used
            have hv_not_St₂ : v ∉ St₂.types := by
              rw [St₂_types_eq, AList.mem_insert]; push_neg
              exact ⟨hv_ne_x, hv_not_Λ⟩
            have hv_in_St₂_used : v ∈ St₂.env.usedVars := by
              rw [St₂_used_eq]; exact List.mem_cons_of_mem _ hv
            exact preserves_the_x! v hv_in_St₂_used hv_not_St₂
          · apply SMT.Typing.var
            exact AList.lookup_insert St₁.types
          · exact typ_x!_spec_base
          · have typ_x!_base : (AList.insert x! α'.option St₁.types) ⊢ˢ .var x! : α'.option := by
              apply SMT.Typing.var
              exact AList.lookup_insert St₁.types
            apply SMT.Typing.weakening _ typ_x!_base
            intro v hv
            have hv₂ : v ∈ St₂.types.entries := by
              simpa only [St₂_types_eq, AList.entries_insert, List.mem_cons] using hv
            exact St₃_types_eq (SMT.TypeContext.entries_subset_insert_of_notMem the_x!_fresh hv₂)
          · apply SMT.Typing.weakening _ typ_x!_spec_base
            intro v hv
            have hv₂ : v ∈ St₂.types.entries := by rwa [St₂_types_eq]
            exact St₃_types_eq (SMT.TypeContext.entries_subset_insert_of_notMem the_x!_fresh hv₂)
          · intro u hu
            have hu' :
                u ∈ SMT.fv (x =ˢ none$α) ∨
                  u ∈ SMT.fv (.var x! =ˢ none$α') ∨
                    u ∈ SMT.fv (.exists [the_x!] [α'] ((.var x! =ˢ .some (.var the_x!)) ∧ˢ the_x!_spec)) := by
              simpa only [fv, List.mem_append, List.cons_append, List.nil_append, List.mem_cons,
                or_assoc, List.append_assoc] using hu
            rw [List.mem_union_iff]
            rcases hu' with hucond | huthen | hlelse
            · rcases (by simpa [fv, List.mem_append] using hucond :
                u ∈ SMT.fv x ∨ u ∈ SMT.fv (none$α)) with hux | hunone
              · exact Or.inl hux
              · exfalso
                simp only [noneCast, fv, List.not_mem_nil] at hunone
            · rcases (by simpa [fv, List.mem_append] using huthen :
                u = x! ∨ u ∈ SMT.fv (none$α')) with hux | hunone
              · subst hux
                exact Or.inr (List.mem_singleton.mpr rfl)
              · exfalso
                simp only [noneCast, fv, List.not_mem_nil] at hunone
            · simpa only [List.mem_union_iff] using hfv_exists_sub hlelse
          · intro X denx
            have hX_ty : X.snd.fst = α.option := denote_type_eq_of_typing (typ_t := typ_x_St₂) (hden := denx)
            have hX_mem : X.fst ∈ ⟦α.option⟧ᶻ := by
              simpa [hX_ty] using X.snd.snd
            have x!_not_mem_fv_x : x! ∉ SMT.fv x := by
              intro hx_mem
              exact x!_fresh (SMT.Typing.mem_context_of_mem_fv typ_x hx_mem)
            have hfv_spec_sub :
                SMT.fv
                    ((x =ˢ none$α).ite (.var x! =ˢ none$α')
                      (.exists [the_x!] [α'] ((.var x! =ˢ .some (.var the_x!)) ∧ˢ the_x!_spec))) ⊆
                  SMT.fv x ∪ {x!} := by
              intro u hu
              have hu' :
                  u ∈ SMT.fv (x =ˢ none$α) ∨
                    u ∈ SMT.fv (.var x! =ˢ none$α') ∨
                      u ∈ SMT.fv (.exists [the_x!] [α'] ((.var x! =ˢ .some (.var the_x!)) ∧ˢ the_x!_spec)) := by
                simpa only [fv, List.mem_append, List.cons_append, List.nil_append, List.mem_cons,
                  or_assoc, List.append_assoc] using hu
              rw [List.mem_union_iff]
              rcases hu' with hucond | huthen | hlelse
              · rcases (by simpa [fv, List.mem_append] using hucond :
                  u ∈ SMT.fv x ∨ u ∈ SMT.fv (none$α)) with hux | hunone
                · exact Or.inl hux
                · exfalso
                  simp only [noneCast, fv, List.not_mem_nil] at hunone
              · rcases (by simpa [fv, List.mem_append] using huthen :
                  u = x! ∨ u ∈ SMT.fv (none$α')) with hux | hunone
                · subst hux
                  exact Or.inr (List.mem_singleton.mpr rfl)
                · exfalso
                  simp only [noneCast, fv, List.not_mem_nil] at hunone
              · simpa only [List.mem_union_iff] using hfv_exists_sub hlelse
            by_cases hXnone : X.fst = (ZFSet.Option.none (S := ⟦α⟧ᶻ)).1
            · let X!none : SMT.Dom :=
                ⟨(ZFSet.Option.none (S := ⟦α'⟧ᶻ)).1, α'.option, SetLike.coe_mem ZFSet.Option.none⟩
              have hcast_none : X.fst.pair X!none.fst ∈ (castZF_of_path hα.opt).1 := by
                rw [castZF_of_path, castZF_option, ZFSet.lambda_spec]
                refine ⟨hX_mem, ?_, ?_⟩
                · exact SetLike.coe_mem ZFSet.Option.none
                · rw [hXnone]
                  simp [X!none]
              have hden_x!none :
                  ⟦(SMT.Term.var x!).abstract (Function.update «Δ» x! (some X!none)) (pf x! X!none)⟧ˢ =
                    some X!none := by
                rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some_inj]
                apply Option.get_of_eq_some
                simp [X!none]
              have hφ_none :
                  SMT.RenamingContext.CoversFV
                    (Function.update «Δ» x! (some X!none))
                    ((x =ˢ none$α).ite (.var x! =ˢ none$α')
                      (.exists [the_x!] [α'] ((.var x! =ˢ .some (.var the_x!)) ∧ˢ the_x!_spec))) := by
                intro v hv
                by_cases hvx : v = x!
                · subst hvx
                  rw [Function.update_self, Option.isSome_some]
                · rw [Function.update_of_ne hvx]
                  have hv' := hfv_spec_sub hv
                  rw [List.mem_union_iff] at hv'
                  rcases hv' with hvx_in | hvx_single
                  · exact hx v hvx_in
                  · exfalso
                    exact hvx (List.mem_singleton.mp hvx_single)
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
              have hX_eq_noneDom :
                  X = ⟨(ZFSet.Option.none (S := ⟦α⟧ᶻ)).1, α.option, SetLike.coe_mem ZFSet.Option.none⟩ := by
                cases X with
                | mk x hxX =>
                    cases hxX with
                    | mk τ hxmem =>
                        dsimp at hXnone hX_ty
                        cases hXnone
                        cases hX_ty
                        rfl
              refine ⟨zftrue, Or.inr rfl, X!none.fst, ?_⟩
              refine ⟨⟨rfl, hcast_none⟩, α'.option, X!none.snd.snd, ?_⟩
              refine ⟨?_, hden_x!none, ?_⟩
              · refine ⟨hφ_none, ?_⟩
                have hdenx_none :
                    ⟦x.abstract (Function.update «Δ» x! (some X!none)) (hcov_x_upd X!none)⟧ˢ = some X :=
                  denx_upd X!none
                rw [hX_eq_noneDom] at hdenx_none
                have hden_noneα :
                    ⟦(none$α).abstract (Function.update «Δ» x! (some X!none)) (by
                        intro v hv
                        simp [noneCast, fv] at hv)⟧ˢ =
                      some ⟨(ZFSet.Option.none (S := ⟦α⟧ᶻ)).1, α.option, SetLike.coe_mem ZFSet.Option.none⟩ := by
                  simp [noneCast, SMT.Term.abstract, SMT.denote]
                have hden_noneα' :
                    ⟦(none$α').abstract (Function.update «Δ» x! (some X!none)) (by
                        intro v hv
                        simp [noneCast, fv] at hv)⟧ˢ =
                      some X!none := by
                  simp [noneCast, SMT.Term.abstract, SMT.denote, X!none]
                have hget_x! :
                    ((Function.update «Δ» x! (some X!none) x!).get
                      (pf x! X!none x! (by simp [fv]))) = X!none := by
                  apply Option.get_of_eq_some
                  simp
                simp only [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.bind_eq_bind,
                  Option.bind_some, Option.failure_eq_none, overloadBinOp, Function.onFun]
                simp [hdenx_none, hden_noneα, hden_noneα', X!none]
                have hc :
                    ((Function.update «Δ» x! (some X!none) x!).get
                      (pf x! X!none x! (by simp [fv]))).2.fst = α'.option := by
                  have hc' := congrArg (fun d => d.2.fst) hget_x!
                  simpa [X!none] using hc'
                have hget_x!_rw :
                    ((Function.update «Δ» x! (some
                      ⟨(ZFSet.Option.none (S := ⟦α'⟧ᶻ)).1, α'.option,
                        SetLike.coe_mem ZFSet.Option.none⟩) x!).get
                      (pf x! X!none x! (by simp [fv]))) = X!none := by
                  rw [show X!none =
                    ⟨(ZFSet.Option.none (S := ⟦α'⟧ᶻ)).1, α'.option,
                      SetLike.coe_mem ZFSet.Option.none⟩ by rfl] at hget_x!
                  exact hget_x!
                rw [if_pos (by simp only [ZFBool.toBool, ↓reduceDIte]), dif_pos hc]
                let G : SMT.Dom :=
                  ((Function.update «Δ» x! (some
                    ⟨(ZFSet.Option.none (S := ⟦α'⟧ᶻ)).1, α'.option,
                      SetLike.coe_mem ZFSet.Option.none⟩) x!).get
                    (pf x! X!none x! (by simp [fv])))
                have hG_fst : G.fst = (ZFSet.Option.none (S := ⟦α'⟧ᶻ)).1 := by
                  unfold G
                  exact congrArg (fun d => d.fst) hget_x!_rw
                have hG_ty : G.snd.fst = α'.option := by
                  simpa [G, X!none] using hc
                have hnone_mem : (ZFSet.Option.none (S := ⟦α'⟧ᶻ)).1 ∈ ⟦G.snd.fst⟧ᶻ := by
                  rw [hG_ty]
                  exact SetLike.coe_mem (ZFSet.Option.none (S := ⟦α'⟧ᶻ))
                have hinner :
                    (if G.fst ∈ ⟦G.snd.fst⟧ᶻ ∧ (ZFSet.Option.none (S := ⟦α'⟧ᶻ)).1 ∈ ⟦G.snd.fst⟧ᶻ then
                      G.fst = (ZFSet.Option.none (S := ⟦α'⟧ᶻ)).1
                    else False) := by
                  rw [if_pos ⟨by simpa [hG_fst] using hnone_mem, hnone_mem⟩]
                  exact hG_fst
                rw [Option.some_inj]
                congr
                · rw [if_pos hinner]
                · funext τ
                  rw [if_pos hinner]
                · apply proof_irrel_heq
              · intro Y hY hφY
                have hdenx_Y :
                    ⟦x.abstract (Function.update «Δ» x! (some Y)) (hcov_x_upd Y)⟧ˢ = some X :=
                  denx_upd Y
                rw [hX_eq_noneDom] at hdenx_Y
                have hden_noneα :
                    ⟦(none$α).abstract (Function.update «Δ» x! (some Y)) (by
                        intro v hv
                        simp [noneCast, fv] at hv)⟧ˢ =
                      some ⟨(ZFSet.Option.none (S := ⟦α⟧ᶻ)).1, α.option, SetLike.coe_mem ZFSet.Option.none⟩ := by
                  simp [noneCast, SMT.Term.abstract, SMT.denote]
                have hget_x!Y :
                    ((Function.update «Δ» x! (some Y) x!).get
                      (pf x! Y x! (by simp [fv]))) = Y := by
                  apply Option.get_of_eq_some
                  rw [Function.update_self]
                simp only [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.bind_eq_bind,
                  Option.bind_some, Option.failure_eq_none, overloadBinOp, Function.onFun, hdenx_Y,
                  hden_noneα, «Prop».bot_eq_false, dite_eq_ite, Option.bind_some,
                  ↓reduceDIte, SetLike.coe_mem, and_self, ↓reduceIte, Function.update_self,
                  Option.get_some, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
                  Fin.val_eq_zero, List.getElem_cons_zero]
                rw [if_pos (by simp only [ZFBool.toBool, ↓reduceDIte])]
                simp only [noneCast, Term.abstract, denote, Option.pure_def, Option.bind_some,
                  Option.isSome_dite]
                constructor
                · exact hY
                · intro ΦY hdenY htrueY
                  let Φ0 : SMT.Dom :=
                    ⟨↑(if
                        if Y.fst ∈ ⟦Y.snd.fst⟧ᶻ ∧ X!none.fst ∈ ⟦Y.snd.fst⟧ᶻ then
                          Y.fst = X!none.fst
                        else
                          False
                      then
                        ZFBool.true
                      else
                        ZFBool.false),
                      SMTType.bool, by simp [hY]⟩
                  have hΦ0_true : Φ0.fst = zftrue := by
                    have hfst_opt : some Φ0.fst = some ΦY.fst := by
                      simpa [Φ0, hY, X!none] using
                        congrArg (Option.map (fun d : SMT.Dom => d.fst)) hdenY
                    have hEqFst : Φ0.fst = ΦY.fst := Option.some.inj hfst_opt
                    exact hEqFst.trans htrueY
                  have hY_none : Y.fst = X!none.fst := by
                    have hnone_mem : X!none.fst ∈ ⟦Y.snd.fst⟧ᶻ := by
                      simpa [X!none, hY] using X!none.snd.snd
                    have hinner :
                        (if Y.fst ∈ ⟦Y.snd.fst⟧ᶻ ∧ X!none.fst ∈ ⟦Y.snd.fst⟧ᶻ then
                          Y.fst = X!none.fst
                        else
                          False) := by
                      by_contra hnot
                      have hnot' :
                          ¬((Y.fst ∈ ⟦Y.snd.fst⟧ᶻ ∧ X!none.fst ∈ ⟦Y.snd.fst⟧ᶻ) ∧
                            Y.fst = X!none.fst) := by
                        intro h
                        exact hnot (by
                          rw [if_pos h.1]
                          exact h.2)
                      have hΦ0_false : Φ0.fst = zffalse := by
                        change
                          ↑(if
                              if Y.fst ∈ ⟦Y.snd.fst⟧ᶻ ∧ X!none.fst ∈ ⟦Y.snd.fst⟧ᶻ then
                                Y.fst = X!none.fst
                              else
                                False
                            then
                              ZFBool.true
                            else
                              ZFBool.false) = zffalse
                        rw [if_neg hnot]
                      have hz : zftrue = zffalse := by
                        exact hΦ0_true.symm.trans hΦ0_false
                      exact ZFSet.zftrue_ne_zffalse hz
                    rw [if_pos ⟨Y.snd.snd, hnone_mem⟩] at hinner
                    exact hinner
                  simpa [X!none, hY_none] using hcast_none
            · let Xopt : ZFSet.Option ⟦α⟧ᶻ := ⟨X.fst, hX_mem⟩
              have hXopt_not_none : Xopt ≠ ZFSet.Option.none := by
                intro h
                apply hXnone
                exact Subtype.ext_iff.mp h
              have hXopt_some : ∃ y, Xopt = ZFSet.Option.some y :=
                Or.resolve_left (ZFSet.Option.casesOn Xopt) hXopt_not_none
              let y0 : {y // y ∈ ⟦α⟧ᶻ} := Classical.choose hXopt_some
              have hy0 : Xopt = ZFSet.Option.some y0 := Classical.choose_spec hXopt_some
              have hden_x_the_some :
                  ⟦(SMT.Term.the x).abstract «Δ» hx_the⟧ˢ.isSome = true := by
                rw [SMT.Term.abstract, SMT.denote, denx]
                rcases X with ⟨xv, τv, hmemv⟩
                dsimp at hX_ty
                cases hX_ty
                simp
              obtain ⟨Xthe, hden_x_the⟩ := Option.isSome_iff_exists.mp hden_x_the_some
              obtain ⟨Φt, Xt!, denXt!, hφt, denφt, hΦt_ty, ⟨hΦt_true, hCast_t⟩, htot_t⟩ :=
                den_the Xthe hden_x_the
              have hXt!_ty : Xt!.snd.fst = α' := by
                exact denote_type_eq_of_typing (typ_t := typ_the_x!) (hden := denXt!)
              have hXt!_memα' : Xt!.fst ∈ ⟦α'⟧ᶻ := by
                simpa only [hXt!_ty] using Xt!.snd.snd
              let X!opt : SMT.Dom :=
                ⟨(ZFSet.Option.some ⟨Xt!.fst, hXt!_memα'⟩).1, α'.option,
                  SetLike.coe_mem (ZFSet.Option.some ⟨Xt!.fst, hXt!_memα'⟩)⟩
              refine ⟨zftrue, Or.inr rfl, X!opt.fst, ⟨rfl, ?_⟩, X!opt.snd.fst, X!opt.snd.snd, ?_⟩
              · rw [castZF_of_path, castZF_option]
                rw [ZFSet.lambda_spec]
                refine ⟨hX_mem, ?_, ?_⟩
                · exact SetLike.coe_mem (ZFSet.Option.some ⟨Xt!.fst, hXt!_memα'⟩)
                · have hXthe_ty : Xthe.snd.fst = α := by
                    exact denote_type_eq_of_typing (typ_t := typ_the_x_St₂) (hden := hden_x_the)
                  have hXthe_memα : Xthe.fst ∈ ⟦α⟧ᶻ := by
                    simpa [hXthe_ty] using Xthe.snd.snd
                  have hX_fst_eq : X.fst = (ZFSet.Option.some ⟨Xthe.fst, hXthe_memα⟩).1 := by
                    have hX_fst_eq_y0 : X.fst = (ZFSet.Option.some y0).1 := by
                      simpa [Xopt] using congrArg Subtype.val hy0
                    have hthe_val_eq_y0 :
                        (ZFSet.Option.the SMTType.toZFSet_nonempty Xopt).1 = y0.1 := by
                      rw [hy0]
                      unfold ZFSet.Option.the
                      split_ifs with h
                      · exfalso
                        exact ZFSet.Option.some_ne_none y0 h
                      · have hchoose :
                            ZFSet.Option.some y0 =
                              ZFSet.Option.some
                                (Classical.choose
                                  (Or.resolve_left (ZFSet.Option.casesOn (ZFSet.Option.some y0)) h)) :=
                          Classical.choose_spec
                            (Or.resolve_left (ZFSet.Option.casesOn (ZFSet.Option.some y0)) h)
                        have hchoose_eq :
                            (Classical.choose
                              (Or.resolve_left (ZFSet.Option.casesOn (ZFSet.Option.some y0)) h)) = y0 :=
                          ((ZFSet.Option.some.injEq).1 hchoose).symm
                        exact congrArg Subtype.val hchoose_eq
                    have hthe_dom_eq :
                        (⟨(ZFSet.Option.the SMTType.toZFSet_nonempty Xopt).1, α,
                          SetLike.coe_mem (ZFSet.Option.the SMTType.toZFSet_nonempty Xopt)⟩ : SMT.Dom) = Xthe := by
                      have hden_x_the' := hden_x_the
                      rw [SMT.Term.abstract, SMT.denote, denx] at hden_x_the'
                      rcases X with ⟨xv, τv, hmemv⟩
                      dsimp at hX_ty
                      cases hX_ty
                      simpa [Xopt] using Option.some.inj hden_x_the'
                    have hthe_val_eq_Xthe :
                        (ZFSet.Option.the SMTType.toZFSet_nonempty Xopt).1 = Xthe.fst := by
                      exact congrArg (fun d : SMT.Dom => d.fst) hthe_dom_eq
                    have hy0_eq : y0 = ⟨Xthe.fst, hXthe_memα⟩ := by
                      apply Subtype.ext
                      exact hthe_val_eq_y0.symm.trans hthe_val_eq_Xthe
                    calc
                      X.fst = (ZFSet.Option.some y0).1 := hX_fst_eq_y0
                      _ = (ZFSet.Option.some ⟨Xthe.fst, hXthe_memα⟩).1 := by
                        rw [hy0_eq]
                  have hX_not_none : X.fst ≠ (ZFSet.Option.none (S := ⟦α⟧ᶻ)).1 := by
                    rw [hX_fst_eq]
                    intro h
                    exact ZFSet.Option.some_ne_none ⟨Xthe.fst, hXthe_memα⟩ (Subtype.ext (by simpa using h))
                  simp only [hX_mem, ↓reduceDIte, hX_not_none]
                  let y_def : ∃ y, X.fst = (ZFSet.Option.some (S := ⟦α⟧ᶻ) y).1 := by
                    exact ⟨⟨Xthe.fst, hXthe_memα⟩, hX_fst_eq⟩
                  have hcast_pfunc :
                      ((castZF_of_path hα).1).IsPFunc ⟦α⟧ᶻ ⟦α'⟧ᶻ :=
                    ZFSet.is_func_is_pfunc (castZF_of_path hα).2
                  change
                    X!opt.fst =
                      (ZFSet.Option.some
                        (ZFSet.fapply (castZF_of_path hα).1 (hf := hcast_pfunc)
                          ⟨(Classical.choose y_def).1,
                            by
                              rw [ZFSet.is_func_dom_eq (castZF_of_path hα).2]
                              exact (Classical.choose y_def).2⟩)).1
                  have hy_choose : X.fst = (ZFSet.Option.some (S := ⟦α⟧ᶻ) (Classical.choose y_def)).1 :=
                    Classical.choose_spec y_def
                  have hchoose_eq : (Classical.choose y_def : {x // x ∈ ⟦α⟧ᶻ}) = ⟨Xthe.fst, hXthe_memα⟩ := by
                    apply (ZFSet.Option.some.injEq).1
                    apply Subtype.ext
                    exact hy_choose.symm.trans hX_fst_eq
                  have hcast_eq :
                      ZFSet.fapply (castZF_of_path hα).1 (hf := hcast_pfunc)
                        ⟨Xthe.fst, by
                          rw [ZFSet.is_func_dom_eq (castZF_of_path hα).2]
                          exact hXthe_memα⟩
                        = ⟨Xt!.fst, by simpa [hXt!_ty] using Xt!.snd.snd⟩ := by
                    exact fapply.of_pair (hf := hcast_pfunc) hCast_t
                  have hcast_choose_val :
                      (ZFSet.fapply (castZF_of_path hα).1 (hf := hcast_pfunc)
                        ⟨(Classical.choose y_def).1, by
                          rw [ZFSet.is_func_dom_eq (castZF_of_path hα).2]
                          exact (Classical.choose y_def).2⟩).1 = Xt!.fst := by
                    simpa only [hchoose_eq] using congrArg Subtype.val hcast_eq
                  have hcast_choose :
                      ZFSet.fapply (castZF_of_path hα).1 (hf := hcast_pfunc)
                        ⟨(Classical.choose y_def).1, by
                          rw [ZFSet.is_func_dom_eq (castZF_of_path hα).2]
                          exact (Classical.choose y_def).2⟩
                        = ⟨Xt!.fst, by simpa [hXt!_ty] using Xt!.snd.snd⟩ := by
                    apply Subtype.ext
                    exact hcast_choose_val
                  simp only [hcast_choose, X!opt]
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
              · set_option maxHeartbeats 4000000 in
                constructor
                · have hφ_opt :
                      SMT.RenamingContext.CoversFV
                        (Function.update «Δ» x! (some X!opt))
                        ((x =ˢ none$α).ite (.var x! =ˢ none$α')
                          (.exists [the_x!] [α'] ((.var x! =ˢ .some (.var the_x!)) ∧ˢ the_x!_spec))) := by
                    intro v hv
                    by_cases hvx : v = x!
                    · subst hvx
                      rw [Function.update_self, Option.isSome_some]
                    · rw [Function.update_of_ne hvx]
                      have hv' := hfv_spec_sub hv
                      rw [List.mem_union_iff] at hv'
                      rcases hv' with hvx_in | hvx_single
                      · exact hx v hvx_in
                      · exfalso
                        exact hvx (List.mem_singleton.mp hvx_single)
                  refine ⟨hφ_opt, ?_⟩
                  have hdenx_Xopt :
                      ⟦x.abstract (Function.update «Δ» x! (some X!opt)) (hcov_x_upd X!opt)⟧ˢ = some X :=
                    denx_upd X!opt
                  have hden_noneα :
                      ⟦(none$α).abstract (Function.update «Δ» x! (some X!opt)) (by
                          intro v hv
                          simp [noneCast, fv] at hv)⟧ˢ =
                        some ⟨(ZFSet.Option.none (S := ⟦α⟧ᶻ)).1, α.option,
                          SetLike.coe_mem ZFSet.Option.none⟩ := by
                    simp [noneCast, SMT.Term.abstract, SMT.denote]
                  simp only [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.bind_eq_bind,
                    Option.bind_some, Option.failure_eq_none, overloadBinOp, Function.onFun, hdenx_Xopt,
                    hden_noneα, «Prop».bot_eq_false, dite_eq_ite, Option.bind_some, ↓reduceDIte,
                    Function.update_self, Option.get_some, List.length_cons, List.length_nil, zero_add,
                    Nat.reduceAdd, Fin.val_eq_zero, List.getElem_cons_zero]
                  simp [hX_ty, hX_mem, hXnone]
                  rw [if_neg (by
                    intro h
                    have h' : ZFSet.ZFBool.toBool (⊥ : ZFSet.ZFBool) = true := by
                      simpa using h
                    rw [ZFSet.ZFBool.toBool_false] at h'
                    simp at h')]
                  simp only [Option.bind_eq_some_iff, PSigma.exists]
                  refine ⟨zffalse, SMTType.bool, ZFSet.ZFBool.zffalse_mem_𝔹, ?_, ?_⟩
                  · have hlen_pos : [the_x!].length > 0 := Nat.zero_lt_succ 0
                    split_ifs with den_t_isSome
                    · simp only [forall_const, Option.some.injEq, PSigma.mk.injEq, Fin.foldl_zero,
                        Option.get_bind]
                      let sInter_eq_zffalse : Prop := ?_
                      conv_lhs =>
                        change sInter_eq_zffalse
                      have : sInter_eq_zffalse := by
                        ext1 z
                        simp only [subset_refl, subset_of_empty, notMem_empty, iff_false]
                        intro contra
                        set sInter_sep : ZFSet := ?_
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
                        simp only [mem_sep, mem_insert_iff, mem_singleton, and_imp, forall_exists_index,
                          forall_eq_or_imp, right_eq_dite_iff, forall_and_index, notMem_empty,
                          imp_false, not_forall, forall_eq] at contra
                        obtain ⟨contra1, contra2⟩ := contra
                        obtain ⟨hAr, hMem, hnotFalse⟩ := contra1 Xt!.fst hXt!_memα'
                        apply hnotFalse
                        have hXt!_cast : (⟨Xt!.fst, ⟨α', hXt!_memα'⟩⟩ : SMT.Dom) = Xt! := by
                          cases Xt! with
                          | mk x hx =>
                            cases hx with
                            | mk τ hxmem =>
                              dsimp at hXt!_ty hXt!_memα'
                              cases hXt!_ty
                              rfl
                        conv_rhs =>
                          enter [1, 1]
                          simp only [Option.pure_def, Option.failure_eq_none, Option.bind_eq_bind,
                            SMT.denote, Function.OfArity.uncurry, Function.FromTypes.uncurry, Fin.zero_eq_one_iff,
                            Nat.reduceAdd, Nat.succ_ne_self, ↓dreduceIte, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
                            List.getElem_cons_zero, Term.abstract.go, hXt!_cast]
                        have hx_lookup_St₂ : St₂.types.lookup x! = some α'.option := by
                          rw [St₂_types_eq]
                          exact AList.lookup_insert St₁.types
                        have hx_mem_St₂ : x! ∈ St₂.types := by
                          exact (AList.lookup_isSome).1 (Option.isSome_of_eq_some hx_lookup_St₂)
                        have x!_ne_the : x! ≠ the_x! := by
                          intro h
                          subst h
                          exact the_x!_fresh hx_mem_St₂
                        have x!_not_mem_fv_the_spec : x! ∉ SMT.fv the_x!_spec := by
                          intro hx_mem
                          have hx' := fv_the_x!_spec hx_mem
                          rw [List.mem_union_iff] at hx'
                          rcases hx' with hxt | hxthe
                          · have hx_in_fv_x : x! ∈ SMT.fv x := by
                              simpa [SMT.fv] using hxt
                            exact x!_not_mem_fv_x hx_in_fv_x
                          · exact x!_ne_the (List.mem_singleton.mp hxthe)
                        let Δgoal : SMT.RenamingContext.Context :=
                          Function.update (Function.update «Δ» x! (some X!opt))
                            the_x! (some Xt!)
                        have hφ_the_x :
                            SMT.RenamingContext.CoversFV
                              (Function.update (Function.update «Δ» the_x! (some Xt!)) x! (some X!opt))
                              the_x!_spec :=
                          SMT.RenamingContext.coversFV_update_of_notMem
                            (x := x!) (d := X!opt) x!_not_mem_fv_the_spec hφt
                        have hφ_goal :
                            SMT.RenamingContext.CoversFV Δgoal the_x!_spec := by
                          simpa only [update_swap (f := «Δ») (x := the_x!) (y := x!) (hxy :=
                                x!_ne_the.symm) (vx := some Xt!) (vy := some X!opt)] using
                            hφ_the_x
                        have hDspec_raw_swapped :
                            ⟦the_x!_spec.abstract
                                (Function.update (Function.update «Δ» the_x! (some Xt!)) x! (some X!opt))
                                hφ_the_x⟧ˢ = some Φt := by
                          rw [
                            ←SMT.RenamingContext.denote,
                            ←SMT.RenamingContext.denote_update_of_notMem
                            («Δ» := Function.update «Δ» the_x! (some Xt!)) (t := the_x!_spec)
                            (x := x!) (d := X!opt) (h := hφt) x!_not_mem_fv_the_spec,
                            SMT.RenamingContext.denote]
                          exact denφt
                        have hDspec_raw :
                            ⟦the_x!_spec.abstract Δgoal hφ_goal⟧ˢ = some Φt := by
                          simpa [Δgoal, update_swap (f := «Δ») (x := the_x!) (y := x!)
                            (hxy := x!_ne_the.symm) (vx := some Xt!) (vy := some X!opt)] using
                            hDspec_raw_swapped
                        have hDspec_ty : Φt.2.1 = .bool := hΦt_ty
                        have hcov_x! : SMT.RenamingContext.CoversFV Δgoal (SMT.Term.var x!) := by
                          intro v hv
                          rw [SMT.fv, List.mem_singleton] at hv
                          subst hv
                          simp only [ne_eq, x!_ne_the, not_false_eq_true, Function.update_of_ne,
                            Function.update, ↓reduceDIte, Option.isSome_some, Δgoal]
                        have hcov_the : SMT.RenamingContext.CoversFV Δgoal (SMT.Term.var the_x!) := by
                          intro v hv
                          rw [SMT.fv, List.mem_singleton] at hv
                          subst hv
                          simp only [Function.update_self, Option.isSome_some, Δgoal]
                        have hden_x! :
                            ⟦(SMT.Term.var x!).abstract Δgoal hcov_x!⟧ˢ = some X!opt := by
                          rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some_inj]
                          apply Option.get_of_eq_some
                          simp [Δgoal, Function.update, x!_ne_the]
                        have hden_the :
                            ⟦(SMT.Term.var the_x!).abstract Δgoal hcov_the⟧ˢ =
                              some Xt! := by
                          rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some_inj]
                          apply Option.get_of_eq_some
                          simp [Δgoal]
                        have hden_some_the :
                            ⟦(SMT.Term.some (SMT.Term.var the_x!)).abstract Δgoal
                                (by
                                  intro v hv
                                  exact hcov_the v (by simpa [SMT.fv] using hv))⟧ˢ =
                              some X!opt := by
                          rw [SMT.Term.abstract, SMT.denote, Option.bind_eq_bind, Option.pure_def, hden_the]
                          cases hXt!_ty
                          rfl
                        obtain ⟨Deq, hDeq_raw, hDeq_ty⟩ :=
                          denote_eq_some_of_some
                            (h₁ := hden_x!)
                            (h₂ := hden_some_the)
                            (hτ := rfl)
                        obtain ⟨Dbody, hDbody_raw, hDbody_ty⟩ :=
                          denote_and_some_bool_of_some_bool hDeq_raw hDeq_ty hDspec_raw hDspec_ty
                        have hDeq_true : Deq.fst = zftrue := by
                          have hDeq_raw' := hDeq_raw
                          rw [SMT.denote, hden_x!, hden_some_the] at hDeq_raw'
                          simp only [Option.pure_def, Option.failure_eq_none, Option.bind_eq_bind,
                            Option.bind_some] at hDeq_raw'
                          simp at hDeq_raw'
                          have hEq := congrArg (fun d : SMT.Dom => d.fst) hDeq_raw'
                          simpa [overloadBinOp, X!opt, id_eq, Function.onFun, ZFSet.Option.some.injEq]
                            using hEq.symm
                        have hDbody_true : Dbody.fst = zftrue := by
                          have hDbody_raw' := hDbody_raw
                          rw [SMT.denote, hDeq_raw, hDspec_raw] at hDbody_raw'
                          obtain ⟨P, τP, hP⟩ := Deq
                          obtain ⟨Q, τQ, hQ⟩ := Φt
                          dsimp at hDeq_ty hDspec_ty hDbody_raw' hDeq_true hΦt_true
                          cases hDeq_true
                          cases hΦt_true
                          cases hDeq_ty
                          cases hDspec_ty
                          simp at hDbody_raw'
                          have hEq := congrArg (fun d : SMT.Dom => d.fst) hDbody_raw'
                          simpa [overloadBinOp_𝔹, overloadBinOp, id_eq, ZFSet.inter_self]
                            using hEq.symm
                        have hnot_raw :
                            ⟦¬ˢ'
                                (((SMT.Term.var x!).abstract Δgoal hcov_x! =ˢ'
                                  (SMT.Term.var the_x!).some.abstract Δgoal
                                    (by
                                      intro v hv
                                      exact hcov_the v (by simpa [SMT.fv] using hv))) ∧ˢ'
                                  the_x!_spec.abstract Δgoal hφ_goal)⟧ˢ =
                              some ⟨zffalse, SMTType.bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
                          rw [SMT.denote, hDbody_raw]
                          cases hτ : Dbody.snd.fst with
                          | bool =>
                            obtain ⟨B, τB, hB⟩ := Dbody
                            dsimp at hτ hDbody_true ⊢
                            cases hτ
                            subst B
                            simp only [overloadUnaryOp, mem_insert_iff, subset_refl, subset_of_empty, mem_singleton, or_true, id_eq,
                              Option.some.injEq, PSigma.mk.injEq, ↓reduceDIte, ZFSet.symmDiff_self, true_and]
                            congr
                            · funext τ
                              rw [dif_pos hB]
                              simp only [ZFSet.symmDiff_self]
                            · apply proof_irrel_heq
                          | _ =>
                            simp [hτ] at hDbody_ty
                        have hnot_get :
                            zffalse =
                              (⟦¬ˢ'
                                  (((SMT.Term.var x!).abstract Δgoal hcov_x! =ˢ'
                                    (SMT.Term.var the_x!).some.abstract Δgoal
                                      (by
                                        intro v hv
                                        exact hcov_the v (by simpa [SMT.fv] using hv))) ∧ˢ'
                                    the_x!_spec.abstract Δgoal hφ_goal)⟧ˢ.get
                                (denote_not_isSome_of_some_bool hDbody_raw hDbody_ty)).fst := by
                          conv_rhs =>
                            enter [1, 1]
                            rw [hnot_raw]
                          rw [Option.get_some]
                        simpa [SMT.Term.abstract, SMT.denote, Δgoal, proof_irrel_heq] using hnot_get
                      refine ⟨this, ?_⟩
                      congr
                      · funext τ
                        apply congrArg (fun z => z ∈ ⟦τ⟧ᶻ)
                        simp only [Fin.foldl_zero, forall_const, Option.get_bind]
                        exact this
                      · apply proof_irrel_heq
                    · exfalso
                      apply den_t_isSome
                      intro x_1 hx0_ty hx0_mem
                      simp only [overloadUnaryOp, id_eq]
                      unfold SMT.Term.abstract.go
                      simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Matrix.head_fin_const]
                      let i0 : Fin [the_x!].length := ⟨0, by simp⟩
                      have hx0 : (x_1 i0).2.1 = α' ∧ (x_1 i0).1 ∈ ⟦α'⟧ᶻ := by
                        simpa only [i0, Fin.zero_eta, Fin.isValue] using And.intro hx0_ty hx0_mem
                      have hx_lookup_St₂ : St₂.types.lookup x! = some α'.option := by
                        rw [St₂_types_eq]
                        exact AList.lookup_insert St₁.types
                      have hx_mem_St₂ : x! ∈ St₂.types := by
                        exact (AList.lookup_isSome).1 (Option.isSome_of_eq_some hx_lookup_St₂)
                      have x!_ne_the : x! ≠ the_x! := by
                        intro h
                        subst h
                        exact the_x!_fresh hx_mem_St₂
                      have x!_not_mem_fv_the_spec : x! ∉ SMT.fv the_x!_spec := by
                        intro hx_mem
                        have hx' := fv_the_x!_spec hx_mem
                        rw [List.mem_union_iff] at hx'
                        rcases hx' with hxt | hxthe
                        · have hx_in_fv_x : x! ∈ SMT.fv x := by
                            simpa [SMT.fv] using hxt
                          exact x!_not_mem_fv_x hx_in_fv_x
                        · exact x!_ne_the (List.mem_singleton.mp hxthe)
                      have hφ_the :
                          SMT.RenamingContext.CoversFV (Function.update «Δ» the_x! (some (x_1 i0))) the_x!_spec := by
                        intro v hv
                        by_cases hvthe : v = the_x!
                        · subst hvthe
                          simp
                        · rw [Function.update_of_ne hvthe]
                          have hv' := fv_the_x!_spec hv
                          rw [List.mem_union_iff] at hv'
                          rcases hv' with hvt | hvthe'
                          · exact hx_the v hvt
                          · exact (hvthe (List.mem_singleton.mp hvthe')).elim
                      have hspec_some_the :
                          (SMT.RenamingContext.denote (Function.update «Δ» the_x! (some (x_1 i0)))
                            the_x!_spec hφ_the).isSome = true := by
                        exact (htot_t (x_1 i0) hx0.1 hφ_the).1
                      have hφ_the_x :
                          SMT.RenamingContext.CoversFV
                            (Function.update (Function.update «Δ» the_x! (some (x_1 i0))) x! (some X!opt)) the_x!_spec :=
                        SMT.RenamingContext.coversFV_update_of_notMem
                          (x := x!) (d := X!opt) x!_not_mem_fv_the_spec hφ_the
                      have hspec_some_the_x :
                          (SMT.RenamingContext.denote
                            (Function.update (Function.update «Δ» the_x! (some (x_1 i0))) x! (some X!opt))
                            the_x!_spec hφ_the_x).isSome = true := by
                        rw [← denote_isSome_update_of_notMem
                          («Δ» := Function.update «Δ» the_x! (some (x_1 i0))) (t := the_x!_spec)
                          (x := x!) (d := X!opt) (h := hφ_the) x!_not_mem_fv_the_spec]
                        exact hspec_some_the
                      have hφ_goal :
                          SMT.RenamingContext.CoversFV
                            (Function.update (Function.update «Δ» x! (some X!opt)) the_x! (some (x_1 i0))) the_x!_spec := by
                        simpa [update_swap (f := «Δ») (x := the_x!) (y := x!) (hxy := x!_ne_the.symm)
                          (vx := some (x_1 i0)) (vy := some X!opt)] using hφ_the_x
                      have hspec_some_goal_ctx :
                          (SMT.RenamingContext.denote
                            (Function.update (Function.update «Δ» x! (some X!opt)) the_x! (some (x_1 i0)))
                            the_x!_spec hφ_goal).isSome = true := by
                        simpa [update_swap (f := «Δ») (x := the_x!) (y := x!) (hxy := x!_ne_the.symm)
                          (vx := some (x_1 i0)) (vy := some X!opt)] using hspec_some_the_x
                      obtain ⟨Dspec, hDspec_ctx⟩ := Option.isSome_iff_exists.mp hspec_some_goal_ctx
                      have hDspec_raw :
                          ⟦the_x!_spec.abstract
                              (Function.update (Function.update «Δ» x! (some X!opt)) the_x! (some (x_1 i0)))
                              hφ_goal⟧ˢ = some Dspec := by
                        simpa [SMT.RenamingContext.denote] using hDspec_ctx
                      have hDspec_ty : Dspec.2.1 = .bool := by
                        exact denote_type_eq_of_typing (typ_t := typ_the_x!_spec_St₃) (hden := hDspec_raw)
                      let Δgoal : SMT.RenamingContext.Context :=
                        Function.update (Function.update «Δ» x! (some X!opt)) the_x! (some (x_1 i0))
                      have hcov_x! : SMT.RenamingContext.CoversFV Δgoal (SMT.Term.var x!) := by
                        intro v hv
                        rw [SMT.fv, List.mem_singleton] at hv
                        subst hv
                        simp [Δgoal, Function.update, x!_ne_the]
                      have hcov_the : SMT.RenamingContext.CoversFV Δgoal (SMT.Term.var the_x!) := by
                        intro v hv
                        rw [SMT.fv, List.mem_singleton] at hv
                        subst hv
                        simp only [Function.update_self, Option.isSome_some, Δgoal]
                      have hden_x! :
                          ⟦(SMT.Term.var x!).abstract Δgoal hcov_x!⟧ˢ = some X!opt := by
                        rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some_inj]
                        apply Option.get_of_eq_some
                        simp only [ne_eq, x!_ne_the, not_false_eq_true, Function.update_of_ne,
                          Function.update, ↓reduceDIte, Δgoal]
                      have hden_the :
                          ⟦(SMT.Term.var the_x!).abstract Δgoal hcov_the⟧ˢ = some (x_1 i0) := by
                        rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some_inj]
                        apply Option.get_of_eq_some
                        simp [Δgoal]
                      have hden_some_the :
                          ⟦(SMT.Term.some (SMT.Term.var the_x!)).abstract Δgoal
                              (by
                                intro v hv
                                exact hcov_the v (by simpa [SMT.fv] using hv))⟧ˢ =
                            some ⟨(ZFSet.Option.some ⟨(x_1 i0).fst, by simpa [hx0.1] using hx0.2⟩).1, α'.option,
                              SetLike.coe_mem (ZFSet.Option.some ⟨(x_1 i0).fst, by simpa [hx0.1] using hx0.2⟩)⟩ := by
                        rw [SMT.Term.abstract, SMT.denote, Option.bind_eq_bind, Option.pure_def, hden_the]
                        cases hx0.1
                        rfl
                      obtain ⟨Deq, hDeq_raw, hDeq_ty⟩ :=
                        denote_eq_some_of_some
                          (h₁ := hden_x!)
                          (h₂ := hden_some_the)
                          (hτ := rfl)
                      obtain ⟨Dbody, hDbody_raw, hDbody_ty⟩ :=
                        denote_and_some_bool_of_some_bool hDeq_raw hDeq_ty hDspec_raw hDspec_ty
                      have hnot_some :=
                        denote_not_isSome_of_some_bool (hden := hDbody_raw) (hTy := hDbody_ty)
                      simpa [SMT.Term.abstract, SMT.denote, Option.bind_eq_bind, Option.pure_def,
                        SMT.Term.abstract.go, Function.OfArity.uncurry, Function.FromTypes.uncurry,
                        Δgoal, i0, proof_irrel_heq] using hnot_some
                  · simp [overloadUnaryOp]
                    congr
                    simp only [subset_refl, subset_of_empty, mem_insert_iff, mem_singleton, true_or, ↓reduceDIte, symmDiff_empty]
                    apply proof_irrel_heq
                · constructor
                  · rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some_inj]
                    apply Option.get_of_eq_some
                    simp [X!opt]
                  · intro Y hY hφY
                    have hdenx_Y :
                        ⟦x.abstract (Function.update «Δ» x! (some Y)) (hcov_x_upd Y)⟧ˢ = some X :=
                      denx_upd Y
                    have hden_noneα :
                        ⟦(none$α).abstract (Function.update «Δ» x! (some Y)) (by
                            intro v hv
                            simp [noneCast, fv] at hv)⟧ˢ =
                          some ⟨(ZFSet.Option.none (S := ⟦α⟧ᶻ)).1, α.option,
                            SetLike.coe_mem ZFSet.Option.none⟩ := by
                      simp [noneCast, SMT.Term.abstract, SMT.denote]
                    simp only [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.bind_eq_bind,
                      Option.bind_some, Option.failure_eq_none, overloadBinOp, Function.onFun, hdenx_Y,
                      hden_noneα, «Prop».bot_eq_false, dite_eq_ite, Option.bind_some, ↓reduceDIte,
                      Function.update_self, Option.get_some, List.length_cons, List.length_nil, zero_add,
                      Nat.reduceAdd, Fin.val_eq_zero, List.getElem_cons_zero]
                    simp [hX_ty, hX_mem, hXnone]
                    rw [if_neg (by
                      intro h
                      have h' : ZFSet.ZFBool.toBool (⊥ : ZFSet.ZFBool) = true := by
                        simpa using h
                      rw [ZFSet.ZFBool.toBool_false] at h'
                      simp at h')]
                    split_ifs with hzfalse
                    · constructor
                      · simp
                      · intro ΦY hdenY hExistsTrue0
                        have hdenY' := hdenY
                        simp only [Option.bind_some] at hdenY'
                        have hExistsTrue := by
                          simpa using
                            (congrArg (fun d : SMT.Dom => d.fst) (Option.some.inj hdenY')).trans hExistsTrue0
                        by_contra hnotmem
                        have hXthe_ty : Xthe.snd.fst = α := by
                          exact denote_type_eq_of_typing (typ_t := typ_the_x_St₂) (hden := hden_x_the)
                        have hXthe_memα : Xthe.fst ∈ ⟦α⟧ᶻ := by
                          simpa [hXthe_ty] using Xthe.snd.snd
                        have hX_fst_eq : X.fst = (ZFSet.Option.some ⟨Xthe.fst, hXthe_memα⟩).1 := by
                          have hX_fst_eq_y0 : X.fst = (ZFSet.Option.some y0).1 := by
                            simpa [Xopt] using congrArg Subtype.val hy0
                          have hthe_val_eq_y0 :
                              (ZFSet.Option.the SMTType.toZFSet_nonempty Xopt).1 = y0.1 := by
                            rw [hy0]
                            unfold ZFSet.Option.the
                            split_ifs with h
                            · exfalso
                              exact ZFSet.Option.some_ne_none y0 h
                            · have hchoose :
                                  ZFSet.Option.some y0 =
                                    ZFSet.Option.some
                                      (Classical.choose
                                        (Or.resolve_left (ZFSet.Option.casesOn (ZFSet.Option.some y0)) h)) :=
                                Classical.choose_spec
                                  (Or.resolve_left (ZFSet.Option.casesOn (ZFSet.Option.some y0)) h)
                              have hchoose_eq :
                                  (Classical.choose
                                    (Or.resolve_left (ZFSet.Option.casesOn (ZFSet.Option.some y0)) h)) = y0 :=
                                ((ZFSet.Option.some.injEq).1 hchoose).symm
                              exact congrArg Subtype.val hchoose_eq
                          have hthe_dom_eq :
                              (⟨(ZFSet.Option.the SMTType.toZFSet_nonempty Xopt).1, α,
                                SetLike.coe_mem (ZFSet.Option.the SMTType.toZFSet_nonempty Xopt)⟩ : SMT.Dom) = Xthe := by
                            have hden_x_the' := hden_x_the
                            rw [SMT.Term.abstract, SMT.denote, denx] at hden_x_the'
                            rcases X with ⟨xv, τv, hmemv⟩
                            dsimp at hX_ty
                            cases hX_ty
                            simpa [Xopt] using Option.some.inj hden_x_the'
                          have hthe_val_eq_Xthe :
                              (ZFSet.Option.the SMTType.toZFSet_nonempty Xopt).1 = Xthe.fst := by
                            exact congrArg (fun d : SMT.Dom => d.fst) hthe_dom_eq
                          have hy0_eq : y0 = ⟨Xthe.fst, hXthe_memα⟩ := by
                            apply Subtype.ext
                            exact hthe_val_eq_y0.symm.trans hthe_val_eq_Xthe
                          calc
                            X.fst = (ZFSet.Option.some y0).1 := hX_fst_eq_y0
                            _ = (ZFSet.Option.some ⟨Xthe.fst, hXthe_memα⟩).1 := by
                              rw [hy0_eq]
                        have hX_not_none : X.fst ≠ (ZFSet.Option.none (S := ⟦α⟧ᶻ)).1 := by
                          rw [hX_fst_eq]
                          intro h
                          exact ZFSet.Option.some_ne_none ⟨Xthe.fst, hXthe_memα⟩ (Subtype.ext (by simpa using h))
                        have hcast_opt_of {y' : {y // y ∈ ⟦α'⟧ᶻ}}
                            (hcast : Xthe.fst.pair y'.1 ∈ (castZF_of_path hα).1) :
                            X.fst.pair (ZFSet.Option.some y').1 ∈ (castZF_of_path hα.opt).1 := by
                          rw [castZF_of_path, castZF_option, ZFSet.lambda_spec]
                          refine ⟨hX_mem, SetLike.coe_mem (ZFSet.Option.some y'), ?_⟩
                          simp only [hX_mem, ↓reduceDIte, hX_not_none]
                          let y_def : ∃ y, X.fst = (ZFSet.Option.some (S := ⟦α⟧ᶻ) y).1 := by
                            exact ⟨⟨Xthe.fst, hXthe_memα⟩, hX_fst_eq⟩
                          have hcast_pfunc :
                              ((castZF_of_path hα).1).IsPFunc ⟦α⟧ᶻ ⟦α'⟧ᶻ :=
                            ZFSet.is_func_is_pfunc (castZF_of_path hα).2
                          change
                            (ZFSet.Option.some y').1 =
                              (ZFSet.Option.some
                                (ZFSet.fapply (castZF_of_path hα).1 (hf := hcast_pfunc)
                                  ⟨(Classical.choose y_def).1, by
                                    rw [ZFSet.is_func_dom_eq (castZF_of_path hα).2]
                                    exact (Classical.choose y_def).2⟩)).1
                          have hy_choose :
                              X.fst = (ZFSet.Option.some (S := ⟦α⟧ᶻ) (Classical.choose y_def)).1 :=
                            Classical.choose_spec y_def
                          have hchoose_eq :
                              (Classical.choose y_def : {x // x ∈ ⟦α⟧ᶻ}) = ⟨Xthe.fst, hXthe_memα⟩ := by
                            apply (ZFSet.Option.some.injEq).1
                            apply Subtype.ext
                            exact hy_choose.symm.trans hX_fst_eq
                          have hcast_eq :
                              ZFSet.fapply (castZF_of_path hα).1 (hf := hcast_pfunc)
                                ⟨Xthe.fst, by
                                  rw [ZFSet.is_func_dom_eq (castZF_of_path hα).2]
                                  exact hXthe_memα⟩
                                = y' := by
                            exact fapply.of_pair (hf := hcast_pfunc) hcast
                          have hcast_choose_val :
                              (ZFSet.fapply (castZF_of_path hα).1 (hf := hcast_pfunc)
                                ⟨(Classical.choose y_def).1, by
                                  rw [ZFSet.is_func_dom_eq (castZF_of_path hα).2]
                                  exact (Classical.choose y_def).2⟩).1 = y'.1 := by
                            simpa only [hchoose_eq] using congrArg Subtype.val hcast_eq
                          have hcast_choose :
                              ZFSet.fapply (castZF_of_path hα).1 (hf := hcast_pfunc)
                                ⟨(Classical.choose y_def).1, by
                                  rw [ZFSet.is_func_dom_eq (castZF_of_path hα).2]
                                  exact (Classical.choose y_def).2⟩
                                = y' := by
                            apply Subtype.ext
                            exact hcast_choose_val
                          rw [←hcast_choose]
                        have hΔ_body :
                            ∀ v ∈ SMT.fv ((SMT.Term.var x! =ˢ (SMT.Term.var the_x!).some) ∧ˢ the_x!_spec),
                              v ∉ [the_x!] → (Function.update «Δ» x! (some Y) v).isSome = true := by
                          intro v hv hv_not_vs
                          have hv' : v = x! ∨ v = the_x! ∨ v ∈ SMT.fv the_x!_spec := by
                            simpa [SMT.fv, List.mem_union_iff, List.mem_append, List.mem_singleton, or_assoc] using hv
                          rcases hv' with rfl | rfl | hvspec
                          · simp
                          · exfalso
                            exact hv_not_vs (by simp)
                          · have hvspec' := fv_the_x!_spec hvspec
                            rw [List.mem_union_iff] at hvspec'
                            rcases hvspec' with hvt | hvthe
                            · by_cases hvx : v = x!
                              · subst hvx
                                simp
                              · rw [Function.update_of_ne hvx]
                                exact hx_the v hvt
                            · exfalso
                              exact hv_not_vs (by simpa using List.mem_singleton.mp hvthe)
                        have hlen_pos : [the_x!].length > 0 := by simp
                        let bodyF : ZFSet → ZFSet := fun y =>
                          if hy : y.hasArity 1 ∧ y ∈ ⟦α'⟧ᶻ then
                            let wy : Fin [the_x!].length → SMT.Dom := fun i =>
                              ⟨y, [α'][i], by
                                cases i with
                                | mk i hi =>
                                    simp at hi
                                    subst hi
                                    exact hy.2⟩
                            let i0 : Fin [the_x!].length := ⟨0, hlen_pos⟩
                            (⟦¬ˢ'
                                (Term.abstract.go
                                  ((SMT.Term.var x! =ˢ (SMT.Term.var the_x!).some) ∧ˢ the_x!_spec)
                                  [the_x!]
                                  (Function.update «Δ» x! (some Y))
                                  hΔ_body).uncurry wy⟧ˢ.get
                              (hzfalse (x := wy)
                                (by simpa [i0, Fin.zero_eta, Fin.isValue] using (show (wy i0).snd.fst = α' ∧
                                  (wy i0).fst ∈ ⟦α'⟧ᶻ from by
                                    refine ⟨rfl, ?_⟩
                                    cases i0 with
                                    | mk i hi =>
                                        simp at hi
                                        subst hi
                                        exact hy.2).1)
                                (by simpa [i0, Fin.zero_eta, Fin.isValue] using (show (wy i0).snd.fst = α' ∧
                                  (wy i0).fst ∈ ⟦α'⟧ᶻ from by
                                    refine ⟨rfl, ?_⟩
                                    cases i0 with
                                    | mk i hi =>
                                        simp at hi
                                        subst hi
                                        exact hy.2).2))).fst
                          else
                            ∅
                        have hall : ∀ y ∈ ⟦α'⟧ᶻ, bodyF y = zftrue := by
                          intro y hy
                          let wy : Fin [the_x!].length → SMT.Dom := fun i =>
                            ⟨y, [α'][i], by
                              cases i with
                              | mk i hi =>
                                  simp at hi
                                  subst hi
                                  exact hy⟩
                          have hwy : ∀ i : Fin [the_x!].length, (wy i).snd.fst = [α'][i] ∧ (wy i).fst ∈ ⟦[α'][i]⟧ᶻ := by
                            intro i
                            refine ⟨rfl, ?_⟩
                            cases i with
                            | mk i hi =>
                                simp at hi
                                subst hi
                                exact hy
                          have hy1 : y.hasArity 1 ∧ y ∈ ⟦α'⟧ᶻ := by
                            constructor
                            · simp [ZFSet.hasArity]
                            · exact hy
                          let i0 : Fin [the_x!].length := ⟨0, hlen_pos⟩
                          have hbodyF_y :
                              bodyF y =
                                (⟦¬ˢ'
                                    (Term.abstract.go
                                      ((SMT.Term.var x! =ˢ (SMT.Term.var the_x!).some) ∧ˢ the_x!_spec)
                                      [the_x!]
                                      (Function.update «Δ» x! (some Y))
                                      hΔ_body).uncurry wy⟧ˢ.get
                                  (hzfalse (x := wy)
                                    (by simpa [i0, Fin.zero_eta, Fin.isValue] using (hwy i0).1)
                                    (by simpa [i0, Fin.zero_eta, Fin.isValue] using (hwy i0).2))).fst := by
                            simpa [bodyF, wy, hwy, hy1, proof_irrel_heq]
                          have hx0 : (wy i0).2.1 = α' ∧ (wy i0).1 ∈ ⟦α'⟧ᶻ := by
                            simpa only [i0, Fin.zero_eta, Fin.isValue] using hwy i0
                          have hx_lookup_St₂ : St₂.types.lookup x! = some α'.option := by
                            rw [St₂_types_eq]
                            exact AList.lookup_insert St₁.types
                          have hx_mem_St₂ : x! ∈ St₂.types := by
                            exact (AList.lookup_isSome).1 (Option.isSome_of_eq_some hx_lookup_St₂)
                          have x!_ne_the : x! ≠ the_x! := by
                            intro h
                            subst h
                            exact the_x!_fresh hx_mem_St₂
                          have x!_not_mem_fv_the_spec : x! ∉ SMT.fv the_x!_spec := by
                            intro hx_mem
                            have hx' := fv_the_x!_spec hx_mem
                            rw [List.mem_union_iff] at hx'
                            rcases hx' with hxt | hxthe
                            · have hx_in_fv_x : x! ∈ SMT.fv x := by
                                simpa [SMT.fv] using hxt
                              exact x!_not_mem_fv_x hx_in_fv_x
                            · exact x!_ne_the (List.mem_singleton.mp hxthe)
                          have hφ_the :
                              SMT.RenamingContext.CoversFV (Function.update «Δ» the_x! (some (wy i0))) the_x!_spec := by
                            intro v hv
                            by_cases hvthe : v = the_x!
                            · subst hvthe
                              simp
                            · rw [Function.update_of_ne hvthe]
                              have hv' := fv_the_x!_spec hv
                              rw [List.mem_union_iff] at hv'
                              rcases hv' with hvt | hvthe'
                              · exact hx_the v hvt
                              · exact (hvthe (List.mem_singleton.mp hvthe')).elim
                          have hspec_some_the :
                              (SMT.RenamingContext.denote (Function.update «Δ» the_x! (some (wy i0)))
                                the_x!_spec hφ_the).isSome = true := by
                            exact (htot_t (wy i0) hx0.1 hφ_the).1
                          have hφ_the_x :
                              SMT.RenamingContext.CoversFV
                                (Function.update (Function.update «Δ» the_x! (some (wy i0))) x! (some Y)) the_x!_spec :=
                            SMT.RenamingContext.coversFV_update_of_notMem
                              (x := x!) (d := Y) x!_not_mem_fv_the_spec hφ_the
                          have hspec_some_the_x :
                              (SMT.RenamingContext.denote
                                (Function.update (Function.update «Δ» the_x! (some (wy i0))) x! (some Y))
                                the_x!_spec hφ_the_x).isSome = true := by
                            rw [← denote_isSome_update_of_notMem
                              («Δ» := Function.update «Δ» the_x! (some (wy i0))) (t := the_x!_spec)
                              (x := x!) (d := Y) (h := hφ_the) x!_not_mem_fv_the_spec]
                            exact hspec_some_the
                          obtain ⟨Dspec, hDspec_ctx_the_x⟩ := Option.isSome_iff_exists.mp hspec_some_the_x
                          have hDspec_ctx_the :
                              SMT.RenamingContext.denote (Function.update «Δ» the_x! (some (wy i0)))
                                the_x!_spec hφ_the = some Dspec := by
                            have hctx :
                                SMT.RenamingContext.denote (Function.update «Δ» the_x! (some (wy i0)))
                                  the_x!_spec hφ_the =
                                  SMT.RenamingContext.denote
                                    (Function.update (Function.update «Δ» the_x! (some (wy i0))) x! (some Y))
                                    the_x!_spec hφ_the_x := by
                              simpa [hφ_the_x] using
                                (SMT.RenamingContext.denote_update_of_notMem
                                  («Δ» := Function.update «Δ» the_x! (some (wy i0))) (t := the_x!_spec)
                                  (x := x!) (d := Y) (h := hφ_the) x!_not_mem_fv_the_spec)
                            exact hctx.trans hDspec_ctx_the_x
                          have hφ_goal :
                              SMT.RenamingContext.CoversFV
                                (Function.update (Function.update «Δ» x! (some Y)) the_x! (some (wy i0))) the_x!_spec := by
                            simpa [update_swap (f := «Δ») (x := the_x!) (y := x!) (hxy := x!_ne_the.symm)
                              (vx := some (wy i0)) (vy := some Y)] using hφ_the_x
                          have hDspec_raw :
                              ⟦the_x!_spec.abstract
                                  (Function.update (Function.update «Δ» x! (some Y)) the_x! (some (wy i0)))
                                  hφ_goal⟧ˢ = some Dspec := by
                            simpa [SMT.RenamingContext.denote, update_swap (f := «Δ») (x := the_x!) (y := x!)
                              (hxy := x!_ne_the.symm) (vx := some (wy i0)) (vy := some Y), proof_irrel_heq] using
                              hDspec_ctx_the_x
                          have hDspec_raw_the :
                              ⟦the_x!_spec.abstract (Function.update «Δ» the_x! (some (wy i0))) hφ_the⟧ˢ =
                                some Dspec := by
                            simpa [SMT.RenamingContext.denote] using hDspec_ctx_the
                          have hDspec_ty : Dspec.2.1 = .bool := by
                            exact denote_type_eq_of_typing (typ_t := typ_the_x!_spec_St₃) (hden := hDspec_raw)
                          let Δgoal : SMT.RenamingContext.Context :=
                            Function.update (Function.update «Δ» x! (some Y)) the_x! (some (wy i0))
                          have hcov_x! : SMT.RenamingContext.CoversFV Δgoal (SMT.Term.var x!) := by
                            intro v hv
                            rw [SMT.fv, List.mem_singleton] at hv
                            subst hv
                            simp [Δgoal, Function.update, x!_ne_the]
                          have hcov_the : SMT.RenamingContext.CoversFV Δgoal (SMT.Term.var the_x!) := by
                            intro v hv
                            rw [SMT.fv, List.mem_singleton] at hv
                            subst hv
                            simp only [Function.update_self, Option.isSome_some, Δgoal]
                          have hden_x! :
                              ⟦(SMT.Term.var x!).abstract Δgoal hcov_x!⟧ˢ = some Y := by
                            rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some_inj]
                            apply Option.get_of_eq_some
                            simp only [ne_eq, x!_ne_the, not_false_eq_true, Function.update_of_ne,
                              Function.update, ↓reduceDIte, Δgoal]
                          have hden_the :
                              ⟦(SMT.Term.var the_x!).abstract Δgoal hcov_the⟧ˢ = some (wy i0) := by
                            rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some_inj]
                            apply Option.get_of_eq_some
                            simp [Δgoal]
                          have hden_some_the :
                              ⟦(SMT.Term.some (SMT.Term.var the_x!)).abstract Δgoal
                                  (by
                                    intro v hv
                                    exact hcov_the v (by simpa [SMT.fv] using hv))⟧ˢ =
                                some ⟨(ZFSet.Option.some ⟨(wy i0).fst, by simpa [hx0.1] using hx0.2⟩).1, α'.option,
                                  SetLike.coe_mem (ZFSet.Option.some ⟨(wy i0).fst, by simpa [hx0.1] using hx0.2⟩)⟩ := by
                            rw [SMT.Term.abstract, SMT.denote, Option.bind_eq_bind, Option.pure_def, hden_the]
                            cases hx0.1
                            rfl
                          obtain ⟨Deq, hDeq_raw, hDeq_ty⟩ :=
                            denote_eq_some_of_some
                              (h₁ := hden_x!)
                              (h₂ := hden_some_the)
                              (hτ := hY)
                          obtain ⟨Dbody, hDbody_raw, hDbody_ty⟩ :=
                            denote_and_some_bool_of_some_bool hDeq_raw hDeq_ty hDspec_raw hDspec_ty
                          by_cases hYeq :
                              Y.fst =
                                (ZFSet.Option.some ⟨(wy i0).fst, by simpa [hx0.1] using hx0.2⟩).1
                          · have hDeq_true : Deq.fst = zftrue := by
                              have hDeq_raw_true :
                                  ⟦(SMT.Term.var x!).abstract Δgoal hcov_x! =ˢ'
                                      (SMT.Term.var the_x!).some.abstract Δgoal
                                        (by
                                          intro v hv
                                          exact hcov_the v (by simpa [SMT.fv] using hv))⟧ˢ =
                                    some ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
                                exact denote_eq_eq_zftrue_of_fst_eq hden_x! hden_some_the hY hYeq
                              have hEq : some Deq = some ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
                                exact hDeq_raw.symm.trans hDeq_raw_true
                              exact congrArg (fun d : SMT.Dom => d.fst) (Option.some.inj hEq)
                            have hDspec_mem_bool : Dspec.fst ∈ 𝔹 := by
                              simpa [hDspec_ty] using Dspec.snd.snd
                            have hDspec_bool : Dspec.fst = zftrue ∨ Dspec.fst = zffalse := by
                              simpa [ZFSet.ZFBool.mem_𝔹_iff, or_comm] using hDspec_mem_bool
                            have hDspec_false : Dspec.fst = zffalse := by
                              rcases hDspec_bool with hDspec_true | hDspec_false
                              · exfalso
                                apply hnotmem
                                have hcast_under :
                                    Xthe.fst.pair (wy i0).fst ∈ (castZF_of_path hα).1 := by
                                  exact (htot_t (wy i0) hx0.1 hφ_the).2 hDspec_raw_the hDspec_true
                                have hcast_opt :
                                    X.fst.pair
                                      (ZFSet.Option.some ⟨(wy i0).fst, by simpa [hx0.1] using hx0.2⟩).1 ∈
                                        (castZF_of_path hα.opt).1 :=
                                  hcast_opt_of hcast_under
                                simpa [hYeq] using hcast_opt
                              · exact hDspec_false
                            have hDbody_false_raw :
                                ⟦((SMT.Term.var x!).abstract Δgoal hcov_x! =ˢ'
                                    (SMT.Term.var the_x!).some.abstract Δgoal
                                      (by
                                        intro v hv
                                        exact hcov_the v (by simpa [SMT.fv] using hv))) ∧ˢ'
                                  the_x!_spec.abstract Δgoal hφ_goal⟧ˢ =
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
                                      (SMT.Term.var the_x!).some.abstract Δgoal
                                        (by
                                          intro v hv
                                          exact hcov_the v (by simpa [SMT.fv] using hv))) ∧ˢ'
                                      the_x!_spec.abstract Δgoal hφ_goal)⟧ˢ =
                                  some ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
                              exact denote_not_eq_zftrue_of_some_zffalse hDbody_raw hDbody_ty hDbody_false
                            have hnot_get :
                                zftrue =
                                  (⟦¬ˢ'
                                      (((SMT.Term.var x!).abstract Δgoal hcov_x! =ˢ'
                                        (SMT.Term.var the_x!).some.abstract Δgoal
                                          (by
                                            intro v hv
                                            exact hcov_the v (by simpa [SMT.fv] using hv))) ∧ˢ'
                                        the_x!_spec.abstract Δgoal hφ_goal)⟧ˢ.get
                                    (denote_not_isSome_of_some_bool hDbody_raw hDbody_ty)).fst := by
                              conv_rhs =>
                                enter [1, 1]
                                rw [hnot_raw]
                              rw [Option.get_some]
                            calc
                              bodyF y =
                                  (⟦¬ˢ'
                                      (Term.abstract.go
                                        ((SMT.Term.var x! =ˢ (SMT.Term.var the_x!).some) ∧ˢ the_x!_spec)
                                        [the_x!]
                                        (Function.update «Δ» x! (some Y))
                                        hΔ_body).uncurry wy⟧ˢ.get
                                  (hzfalse (x := wy)
                                    (by simpa [i0, Fin.zero_eta, Fin.isValue] using (hwy i0).1)
                                    (by simpa [i0, Fin.zero_eta, Fin.isValue] using (hwy i0).2))).fst := hbodyF_y
                              _ = zftrue := by
                                simpa [SMT.Term.abstract, SMT.denote, SMT.Term.abstract.go,
                                  Function.OfArity.uncurry, Function.FromTypes.uncurry, Δgoal, i0, wy, hwy,
                                  proof_irrel_heq] using hnot_get.symm
                          · have hDeq_mem_bool : Deq.fst ∈ 𝔹 := by
                              simpa [hDeq_ty] using Deq.snd.snd
                            have hDeq_bool : Deq.fst = zftrue ∨ Deq.fst = zffalse := by
                              simpa [ZFSet.ZFBool.mem_𝔹_iff, or_comm] using hDeq_mem_bool
                            have hDeq_false : Deq.fst = zffalse := by
                              rcases hDeq_bool with hDeq_true | hDeq_false
                              · exfalso
                                exact hYeq <| denote_eq_true_implies_fst_eq hden_x! hden_some_the hY hDeq_raw hDeq_true
                              · exact hDeq_false
                            have hDbody_false_raw :
                                ⟦((SMT.Term.var x!).abstract Δgoal hcov_x! =ˢ'
                                    (SMT.Term.var the_x!).some.abstract Δgoal
                                      (by
                                        intro v hv
                                        exact hcov_the v (by simpa [SMT.fv] using hv))) ∧ˢ'
                                  the_x!_spec.abstract Δgoal hφ_goal⟧ˢ =
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
                                      (SMT.Term.var the_x!).some.abstract Δgoal
                                        (by
                                          intro v hv
                                          exact hcov_the v (by simpa [SMT.fv] using hv))) ∧ˢ'
                                      the_x!_spec.abstract Δgoal hφ_goal)⟧ˢ =
                                  some ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
                              exact denote_not_eq_zftrue_of_some_zffalse hDbody_raw hDbody_ty hDbody_false
                            have hnot_get :
                                zftrue =
                                  (⟦¬ˢ'
                                      (((SMT.Term.var x!).abstract Δgoal hcov_x! =ˢ'
                                        (SMT.Term.var the_x!).some.abstract Δgoal
                                          (by
                                            intro v hv
                                            exact hcov_the v (by simpa [SMT.fv] using hv))) ∧ˢ'
                                        the_x!_spec.abstract Δgoal hφ_goal)⟧ˢ.get
                                    (denote_not_isSome_of_some_bool hDbody_raw hDbody_ty)).fst := by
                              conv_rhs =>
                                enter [1, 1]
                                rw [hnot_raw]
                              rw [Option.get_some]
                            calc
                              bodyF y =
                                  (⟦¬ˢ'
                                      (Term.abstract.go
                                        ((SMT.Term.var x! =ˢ (SMT.Term.var the_x!).some) ∧ˢ the_x!_spec)
                                        [the_x!]
                                        (Function.update «Δ» x! (some Y))
                                        hΔ_body).uncurry wy⟧ˢ.get
                                  (hzfalse (x := wy)
                                    (by simpa [i0, Fin.zero_eta, Fin.isValue] using (hwy i0).1)
                                    (by simpa [i0, Fin.zero_eta, Fin.isValue] using (hwy i0).2))).fst := hbodyF_y
                              _ = zftrue := by
                                simpa [SMT.Term.abstract, SMT.denote, SMT.Term.abstract.go,
                                  Function.OfArity.uncurry, Function.FromTypes.uncurry, Δgoal, i0, wy, hwy,
                                  proof_irrel_heq] using hnot_get.symm
                        have hne : ∃ x, x ∈ ⟦α'⟧ᶻ := ZFSet.nonempty_exists_iff.mp SMTType.toZFSet_nonempty
                        have houter_false :
                            overloadUnaryOp id id ZFBool.false ZFBool.not
                              (⋂₀ ZFSet.sep (fun y => ∃ x ∈ ⟦α'⟧ᶻ, y = bodyF x) 𝔹) = zffalse := by
                          have hsInter_mem :
                              (⋂₀ ZFSet.sep (fun y => ∃ x ∈ ⟦α'⟧ᶻ, y = bodyF x) 𝔹) ∈ 𝔹 :=
                            ZFSet.sInter_sep_subset_of_𝔹_mem_𝔹 (fun _ => id)
                          simpa [overloadUnaryOp, hsInter_mem, id_eq, proof_irrel_heq] using
                            not_sInter_sep_eq_zffalse_of_forall_eq_zftrue hne hall
                        have hExistsTrue_body :
                            overloadUnaryOp id id ZFBool.false ZFBool.not
                              (⋂₀ ZFSet.sep (fun y => ∃ x ∈ ⟦α'⟧ᶻ, y = bodyF x) 𝔹) = zftrue := by
                          simpa [bodyF, SMT.Term.abstract, SMT.denote, SMT.Term.abstract.go,
                            Function.OfArity.uncurry, Function.FromTypes.uncurry, Option.bind_eq_bind,
                            Option.pure_def, overloadUnaryOp, id_eq, proof_irrel_heq] using hExistsTrue
                        have hz : zftrue = zffalse := hExistsTrue_body.symm.trans houter_false
                        exact ZFSet.zftrue_ne_zffalse hz
                    · exfalso
                      apply hzfalse
                      intro x_1 hx0_ty hx0_mem
                      simp only [overloadUnaryOp, id_eq]
                      unfold SMT.Term.abstract.go
                      simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Matrix.head_fin_const]
                      let i0 : Fin [the_x!].length := ⟨0, by simp⟩
                      have hx0 : (x_1 i0).2.1 = α' ∧ (x_1 i0).1 ∈ ⟦α'⟧ᶻ := by
                        simpa only [i0, Fin.zero_eta, Fin.isValue] using And.intro hx0_ty hx0_mem
                      have hx_lookup_St₂ : St₂.types.lookup x! = some α'.option := by
                        rw [St₂_types_eq]
                        exact AList.lookup_insert St₁.types
                      have hx_mem_St₂ : x! ∈ St₂.types := by
                        exact (AList.lookup_isSome).1 (Option.isSome_of_eq_some hx_lookup_St₂)
                      have x!_ne_the : x! ≠ the_x! := by
                        intro h
                        subst h
                        exact the_x!_fresh hx_mem_St₂
                      have x!_not_mem_fv_the_spec : x! ∉ SMT.fv the_x!_spec := by
                        intro hx_mem
                        have hx' := fv_the_x!_spec hx_mem
                        rw [List.mem_union_iff] at hx'
                        rcases hx' with hxt | hxthe
                        · have hx_in_fv_x : x! ∈ SMT.fv x := by
                            simpa [SMT.fv] using hxt
                          exact x!_not_mem_fv_x hx_in_fv_x
                        · exact x!_ne_the (List.mem_singleton.mp hxthe)
                      have hφ_the :
                          SMT.RenamingContext.CoversFV (Function.update «Δ» the_x! (some (x_1 i0))) the_x!_spec := by
                        intro v hv
                        by_cases hvthe : v = the_x!
                        · subst hvthe
                          simp
                        · rw [Function.update_of_ne hvthe]
                          have hv' := fv_the_x!_spec hv
                          rw [List.mem_union_iff] at hv'
                          rcases hv' with hvt | hvthe'
                          · exact hx_the v hvt
                          · exact (hvthe (List.mem_singleton.mp hvthe')).elim
                      have hspec_some_the :
                          (SMT.RenamingContext.denote (Function.update «Δ» the_x! (some (x_1 i0)))
                            the_x!_spec hφ_the).isSome = true := by
                        exact (htot_t (x_1 i0) hx0.1 hφ_the).1
                      have hφ_the_x :
                          SMT.RenamingContext.CoversFV
                            (Function.update (Function.update «Δ» the_x! (some (x_1 i0))) x! (some Y)) the_x!_spec :=
                        SMT.RenamingContext.coversFV_update_of_notMem
                          (x := x!) (d := Y) x!_not_mem_fv_the_spec hφ_the
                      have hspec_some_the_x :
                          (SMT.RenamingContext.denote
                            (Function.update (Function.update «Δ» the_x! (some (x_1 i0))) x! (some Y))
                            the_x!_spec hφ_the_x).isSome = true := by
                        rw [← denote_isSome_update_of_notMem
                          («Δ» := Function.update «Δ» the_x! (some (x_1 i0))) (t := the_x!_spec)
                          (x := x!) (d := Y) (h := hφ_the) x!_not_mem_fv_the_spec]
                        exact hspec_some_the
                      have hφ_goal :
                          SMT.RenamingContext.CoversFV
                            (Function.update (Function.update «Δ» x! (some Y)) the_x! (some (x_1 i0))) the_x!_spec := by
                        simpa [update_swap (f := «Δ») (x := the_x!) (y := x!) (hxy := x!_ne_the.symm)
                          (vx := some (x_1 i0)) (vy := some Y)] using hφ_the_x
                      have hspec_some_goal_ctx :
                          (SMT.RenamingContext.denote
                            (Function.update (Function.update «Δ» x! (some Y)) the_x! (some (x_1 i0)))
                            the_x!_spec hφ_goal).isSome = true := by
                        simpa [update_swap (f := «Δ») (x := the_x!) (y := x!) (hxy := x!_ne_the.symm)
                          (vx := some (x_1 i0)) (vy := some Y)] using hspec_some_the_x
                      obtain ⟨Dspec, hDspec_ctx⟩ := Option.isSome_iff_exists.mp hspec_some_goal_ctx
                      have hDspec_raw :
                          ⟦the_x!_spec.abstract
                              (Function.update (Function.update «Δ» x! (some Y)) the_x! (some (x_1 i0)))
                              hφ_goal⟧ˢ = some Dspec := by
                        simpa [SMT.RenamingContext.denote] using hDspec_ctx
                      have hDspec_ty : Dspec.2.1 = .bool := by
                        exact denote_type_eq_of_typing (typ_t := typ_the_x!_spec_St₃) (hden := hDspec_raw)
                      let Δgoal : SMT.RenamingContext.Context :=
                        Function.update (Function.update «Δ» x! (some Y)) the_x! (some (x_1 i0))
                      have hcov_x! : SMT.RenamingContext.CoversFV Δgoal (SMT.Term.var x!) := by
                        intro v hv
                        rw [SMT.fv, List.mem_singleton] at hv
                        subst hv
                        simp [Δgoal, Function.update, x!_ne_the]
                      have hcov_the : SMT.RenamingContext.CoversFV Δgoal (SMT.Term.var the_x!) := by
                        intro v hv
                        rw [SMT.fv, List.mem_singleton] at hv
                        subst hv
                        simp only [Function.update_self, Option.isSome_some, Δgoal]
                      have hden_x! :
                          ⟦(SMT.Term.var x!).abstract Δgoal hcov_x!⟧ˢ = some Y := by
                        rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some_inj]
                        apply Option.get_of_eq_some
                        simp only [ne_eq, x!_ne_the, not_false_eq_true, Function.update_of_ne,
                          Function.update, ↓reduceDIte, Δgoal]
                      have hden_the :
                          ⟦(SMT.Term.var the_x!).abstract Δgoal hcov_the⟧ˢ = some (x_1 i0) := by
                        rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some_inj]
                        apply Option.get_of_eq_some
                        simp only [Function.update_self, Δgoal]
                      have hden_some_the :
                          ⟦(SMT.Term.some (SMT.Term.var the_x!)).abstract Δgoal
                              (by
                                intro v hv
                                exact hcov_the v (by simpa [SMT.fv] using hv))⟧ˢ =
                            some ⟨(ZFSet.Option.some ⟨(x_1 i0).fst, by simpa [hx0.1] using hx0.2⟩).1, α'.option,
                              SetLike.coe_mem (ZFSet.Option.some ⟨(x_1 i0).fst, by simpa [hx0.1] using hx0.2⟩)⟩ := by
                        rw [SMT.Term.abstract, SMT.denote, Option.bind_eq_bind, Option.pure_def, hden_the]
                        cases hx0.1
                        rfl
                      obtain ⟨Deq, hDeq_raw, hDeq_ty⟩ :=
                        denote_eq_some_of_some
                          (h₁ := hden_x!)
                          (h₂ := hden_some_the)
                          (hτ := hY)
                      obtain ⟨Dbody, hDbody_raw, hDbody_ty⟩ :=
                        denote_and_some_bool_of_some_bool hDeq_raw hDeq_ty hDspec_raw hDspec_ty
                      have hnot_some :=
                        denote_not_isSome_of_some_bool (hden := hDbody_raw) (hTy := hDbody_ty)
                      simpa [SMT.Term.abstract, SMT.denote, Option.bind_eq_bind, Option.pure_def,
                        SMT.Term.abstract.go, Function.OfArity.uncurry, Function.FromTypes.uncurry,
                        Δgoal, i0, proof_irrel_heq] using hnot_some
