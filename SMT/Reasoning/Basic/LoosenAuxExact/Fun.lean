import SMT.Reasoning.Defs
import SMT.Reasoning.LooseningDefs
import SMT.Reasoning.Basic.StateSpecs
import SMT.Reasoning.Basic.LoosenAuxExact.FunDefault
import SMT.Reasoning.Basic.LoosenAuxExact.FunAux

open Std.Do SMT ZFSet Classical

set_option maxHeartbeats 2000000 in
theorem loosenAux_prf_exact.fun.{u} {α β α' β' : SMTType} (hβ : β ≠ SMTType.bool) (pα : α ⇝ α')
  (pβ : β ⇝ β')
  (pα_ih :
    ∀ {Λ : TypeContext} {n : ℕ} {used : List 𝒱} {name : String} {x : Term},
      Λ ⊢ˢ x : α →
        ∀ («Δ» : RenamingContext.Context.{u}) (hx : RenamingContext.CoversFV «Δ» x)
          (pf : ∀ (x! : 𝒱) (X! : SMT.Dom.{u}), ∀ v ∈ fv (Term.var x!), (Function.update «Δ» x! (some X!) v).isSome = true),
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
                                        ∀ (X : SMT.Dom.{u}),
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
                                                    (Φ.fst = zftrue ∧ X.fst.pair X!.fst ∈ ↑(castZF_of_path pα).1) ∧
                                                      ∀ (Y : SMT.Dom.{u}),
                                                        Y.snd.fst = α' →
                                                          ∀
                                                            (hφY :
                                                              RenamingContext.CoversFV (Function.update «Δ» x! (some Y))
                                                                x!_spec),
                                                            ⟦x!_spec.abstract (Function.update «Δ» x! (some Y))
                                                                      hφY⟧ˢ.isSome =
                                                                true ∧
                                                              ∀ {ΦY : SMT.Dom.{u}},
                                                                ⟦x!_spec.abstract (Function.update «Δ» x! (some Y))
                                                                        hφY⟧ˢ =
                                                                    some ΦY →
                                                                  ΦY.fst = zftrue →
                                                                    X.fst.pair Y.fst ∈ ↑(castZF_of_path pα).1⌝⦄)
  (pβ_ih :
    ∀ {Λ : TypeContext} {n : ℕ} {used : List 𝒱} {name : String} {x : Term},
      Λ ⊢ˢ x : β →
        ∀ («Δ» : RenamingContext.Context.{u}) (hx : RenamingContext.CoversFV «Δ» x)
          (pf : ∀ (x! : 𝒱) (X! : SMT.Dom.{u}), ∀ v ∈ fv (Term.var x!), (Function.update «Δ» x! (some X!) v).isSome = true),
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
                                          ∀ (X : SMT.Dom.{u}),
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
                                                    (Φ.fst = zftrue ∧ X.fst.pair X!.fst ∈ ↑(castZF_of_path pβ).1) ∧
                                                      ∀ (Y : SMT.Dom.{u}),
                                                        Y.snd.fst = β' →
                                                          ∀
                                                            (hφY :
                                                              RenamingContext.CoversFV (Function.update «Δ» x! (some Y))
                                                                x!_spec),
                                                            ⟦x!_spec.abstract (Function.update «Δ» x! (some Y))
                                                                      hφY⟧ˢ.isSome =
                                                                true ∧
                                                              ∀ {ΦY : SMT.Dom.{u}},
                                                                ⟦x!_spec.abstract (Function.update «Δ» x! (some Y))
                                                                        hφY⟧ˢ =
                                                                    some ΦY →
                                                                  ΦY.fst = zftrue →
                                                                    X.fst.pair Y.fst ∈ ↑(castZF_of_path pβ).1⌝⦄)
  {Λ : TypeContext} {n : ℕ} {used : List 𝒱} {name : String} {x : Term} (typ_x : Λ ⊢ˢ x : α.fun β)
  («Δ» : RenamingContext.Context.{u}) (hx : RenamingContext.CoversFV «Δ» x)
  (pf : ∀ (x! : 𝒱) (X! : SMT.Dom.{u}), ∀ v ∈ fv (Term.var x!), (Function.update «Δ» x! (some X!) v).isSome = true) :
  ⦃fun x =>
    match x with
    | { env := E, types := Λ' } => ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ AList.keys Λ' ⊆ E.usedVars ∧ E.usedVars = used⌝⦄
    loosenAux_prf name (castPath.fun hβ pα pβ) x ⦃PostCond.mayThrow fun x_1 x_2 =>
      match x_1 with
      | (x!, x!_spec) =>
        match x_2 with
        | { env := E', types := Γ' } =>
          ⌜n ≤ E'.freshvarsc ∧
              AList.insert x! (α'.fun β') Λ ⊆ Γ' ∧
                x! ∉ Λ ∧
                  x! ∉ used ∧
                    used ⊆ E'.usedVars ∧
                      AList.keys Γ' ⊆ E'.usedVars ∧
                        (∀ v ∈ used, v ∉ Λ → v ∉ Γ') ∧
                        AList.insert x! (α'.fun β') Λ ⊢ˢ Term.var x! : α'.fun β' ∧
                          AList.insert x! (α'.fun β') Λ ⊢ˢ x!_spec : SMTType.bool ∧
                            Γ' ⊢ˢ Term.var x! : α'.fun β' ∧
                              Γ' ⊢ˢ x!_spec : SMTType.bool ∧
                                fv x!_spec ⊆ fv x ∪ {x!} ∧
                                  ∀ (X : SMT.Dom.{u}),
                                    ⟦x.abstract «Δ» hx⟧ˢ = some X →
                                      ∃ Φ X!,
                                        ∃ (_ : ⟦(Term.var x!).abstract (Function.update «Δ» x! (some X!)) (pf x! X!)⟧ˢ = some X!)
                                          (hφ : RenamingContext.CoversFV (Function.update «Δ» x! (some X!)) x!_spec) (_
                                          : ⟦x!_spec.abstract (Function.update «Δ» x! (some X!)) hφ⟧ˢ = some Φ),
                                          Φ.snd.fst = SMTType.bool ∧
                                            (Φ.fst = zftrue ∧
                                                X.fst.pair X!.fst ∈ ↑(castZF_of_path (castPath.fun hβ pα pβ)).1) ∧
                                              ∀ (Y : SMT.Dom.{u}),
                                                Y.snd.fst = α'.fun β' →
                                                  ∀
                                                    (hφY :
                                                      RenamingContext.CoversFV (Function.update «Δ» x! (some Y))
                                                        x!_spec),
                                                    ⟦x!_spec.abstract (Function.update «Δ» x! (some Y)) hφY⟧ˢ.isSome =
                                                        true ∧
                                                      ∀ {ΦY : SMT.Dom.{u}},
                                                        ⟦x!_spec.abstract (Function.update «Δ» x! (some Y)) hφY⟧ˢ =
                                                            some ΦY →
                                                          ΦY.fst = zftrue →
                                                            X.fst.pair Y.fst ∈
                                                              ↑(castZF_of_path (castPath.fun hβ pα pβ)).1⌝⦄ := by
  mintro pre ∀St₁
  mpure pre
  obtain ⟨rfl, rfl, sub, rfl⟩ := pre
  have pα_ih_exact : FunExactIH pα := pα_ih
  have pβ_ih_exact : FunExactIH pβ := pβ_ih
  unfold loosenAux_prf
  mspec SMT.freshVar_spec (Γ := St₁.types) (n := St₁.env.freshvarsc) (used := St₁.env.usedVars)
  next x! =>
    mrename_i pre
    mintro ∀St₂
    mcases pre with ⟨St₂_types_eq, x!_fresh, St₂_fvc, St₂_used_eq, x!_not_used⟩
    mspec SMT.freshVar_spec (Γ := St₂.types) (n := St₂.env.freshvarsc) (used := St₂.env.usedVars)
    next a =>
      mrename_i pre
      mintro ∀St₃
      mcases pre with ⟨St₃_types_eq, a_fresh, St₃_fvc, St₃_used_eq, a_not_used⟩
      have keys₂ : AList.keys St₂.types ⊆ St₂.env.usedVars := by
        erw [St₂_types_eq, St₂_used_eq, AList.keys_insert]
        intro v hv
        erw [List.mem_cons] at hv ⊢
        rcases hv with rfl | hv
        · exact Or.inl rfl
        · exact Or.inr (sub (List.mem_of_mem_erase hv))
      have keys₃ : AList.keys St₃.types ⊆ St₃.env.usedVars := by
        erw [St₃_types_eq, St₃_used_eq, AList.keys_insert]
        intro v hv
        erw [List.mem_cons] at hv ⊢
        rcases hv with rfl | hv
        · exact Or.inl rfl
        · exact Or.inr (keys₂ (List.mem_of_mem_erase hv))
      have typ_var_a_St₃ : St₃.types ⊢ˢ .var a : α := by
        apply SMT.Typing.var
        erw [St₃_types_eq]
        exact AList.lookup_insert St₂.types
      let Δa : RenamingContext.Context :=
        Function.update «Δ» a (some ⟨α.defaultZFSet, α, SMTType.mem_toZFSet_of_defaultZFSet⟩)
      have hcov_var_a : RenamingContext.CoversFV Δa (.var a) := by
        intro v hv
        erw [fv, List.mem_singleton] at hv
        subst hv
        simp only [Function.update_self, Option.isSome_some, Δa]
      have pf_var_a : FunPf Δa := by
        intro a₀! A₀! v hv
        erw [fv, List.mem_singleton] at hv
        subst hv
        erw [Function.update_self]
        rfl
      have ih_a :=
        pα_ih_exact
          (Λ := St₃.types) (n := St₃.env.freshvarsc) (used := St₃.env.usedVars)
          (name := s!"{name}_funFun_arg") (x := .var a)
          typ_var_a_St₃ Δa hcov_var_a pf_var_a
      mspec (Std.Do.Triple.and _
        (funRunVarSpec (p := pα) (name := s!"{name}_funFun_arg") (z := a) (St := St₃))
        ih_a)
      · rename_i out_a
        obtain ⟨a!, a!_spec⟩ := out_a
        mrename_i pre
        mintro ∀St₄
        mpure pre
        obtain ⟨hrun_a, hn₄, sub₄, a!_fresh, a!_not_used, used_sub₄, keys₄, preserves_a!,
          typ_var_a!_base, typ_a!_spec_base, typ_var_a!_St₄, typ_a!_spec_St₄,
          fv_a!_spec, den_a⟩ := pre
        mspec SMT.freshVar_spec (Γ := St₄.types) (n := St₄.env.freshvarsc) (used := St₄.env.usedVars)
        next b =>
          mrename_i pre
          mintro ∀St₅
          mcases pre with ⟨St₅_types_eq, b_fresh, St₅_fvc, St₅_used_eq, b_not_used⟩
          have typ_var_b_St₅ : St₅.types ⊢ˢ .var b : β := by
            apply SMT.Typing.var
            erw [St₅_types_eq]
            exact AList.lookup_insert St₄.types
          let Δb : RenamingContext.Context :=
            Function.update «Δ» b (some ⟨β.defaultZFSet, β, SMTType.mem_toZFSet_of_defaultZFSet⟩)
          have hcov_var_b : RenamingContext.CoversFV Δb (.var b) := by
            intro v hv
            erw [fv, List.mem_singleton] at hv
            subst hv
            simp only [Function.update_self, Option.isSome_some, Δb]
          have pf_var_b : FunPf Δb := by
            intro b₀! B₀! v hv
            erw [fv, List.mem_singleton] at hv
            subst hv
            erw [Function.update_self]
            rfl
          have keys₅ : AList.keys St₅.types ⊆ St₅.env.usedVars := by
            erw [St₅_types_eq, St₅_used_eq, AList.keys_insert]
            intro v hv
            erw [List.mem_cons] at hv ⊢
            rcases hv with rfl | hv
            · exact Or.inl rfl
            · exact Or.inr (keys₄ (List.mem_of_mem_erase hv))
          have ih_b :=
            pβ_ih_exact
              (Λ := St₅.types) (n := St₅.env.freshvarsc) (used := St₅.env.usedVars)
              (name := s!"{name}_funFun_ret") (x := .var b)
              typ_var_b_St₅ Δb hcov_var_b pf_var_b
          mspec (Std.Do.Triple.and _
            (funRunVarSpec (p := pβ) (name := s!"{name}_funFun_ret") (z := b) (St := St₅))
            ih_b)
          · rename_i out_b
            obtain ⟨b!, b!_spec⟩ := out_b
            mrename_i pre
            mintro ∀St₆
            mpure pre
            obtain ⟨hrun_b, hn₆, sub₆, b!_fresh, b!_not_used, used_sub₆, keys₆, preserves_b!,
              typ_var_b!_base, typ_b!_spec_base, typ_var_b!_St₆, typ_b!_spec_St₆,
              fv_b!_spec, den_b⟩ := pre
            have hsub_St₂_St₄ : St₂.types ⊆ St₄.types := by
              intro v hv
              exact sub₄ (by
                exact SMT.TypeContext.entries_subset_insert_of_notMem a!_fresh
                  (by
                    erw [St₃_types_eq]
                    exact SMT.TypeContext.entries_subset_insert_of_notMem a_fresh hv))
            have hsub_St₂_St₆ : St₂.types ⊆ St₆.types := by
              intro v hv
              exact sub₆ (by
                exact SMT.TypeContext.entries_subset_insert_of_notMem b!_fresh
                  (by
                    erw [St₅_types_eq]
                    exact SMT.TypeContext.entries_subset_insert_of_notMem b_fresh
                      (hsub_St₂_St₄ hv)))
            have hsub_St₄_St₆ : St₄.types ⊆ St₆.types := by
              intro v hv
              exact sub₆ (by
                exact SMT.TypeContext.entries_subset_insert_of_notMem b!_fresh
                  (by
                    erw [St₅_types_eq]
                    exact SMT.TypeContext.entries_subset_insert_of_notMem b_fresh hv))
            have x!_in_St₃ : x! ∈ St₃.types := by
              erw [St₃_types_eq, AList.mem_insert]
              exact Or.inr (by
                erw [St₂_types_eq, AList.mem_insert]
                exact Or.inl rfl)
            have x!_ne_a! : x! ≠ a! := by
              intro h
              exact a!_fresh (h ▸ x!_in_St₃)
            have x!_in_St₅ : x! ∈ St₅.types := by
              have x!_in_St₄ : x! ∈ St₄.types := by
                exact typeContext_mem_of_subset sub₄ (by
                  erw [AList.mem_insert]
                  exact Or.inr x!_in_St₃)
              erw [St₅_types_eq, AList.mem_insert]
              exact Or.inr x!_in_St₄
            have x!_ne_b! : x! ≠ b! := by
              intro h
              exact b!_fresh (h ▸ x!_in_St₅)
            have typ_var_x!_St₆ : St₆.types ⊢ˢ .var x! : α'.fun β' := by
              have typ_var_x!_St₂ : St₂.types ⊢ˢ .var x! : α'.fun β' := by
                apply SMT.Typing.var
                erw [St₂_types_eq]
                exact AList.lookup_insert St₁.types
              apply SMT.Typing.weakening
                (h := hsub_St₂_St₆)
                typ_var_x!_St₂
            have typ_var_a!_St₆' : St₆.types ⊢ˢ .var a! : α' := by
              apply SMT.Typing.weakening
                (h := hsub_St₄_St₆)
                typ_var_a!_St₄
            have typ_app_default_St₆ : St₆.types ⊢ˢ .app (.var x!) (.var a!) : β' := by
              exact SMT.Typing.app
                (Γ := St₆.types) (f := .var x!) (x := .var a!) (τ := α') (σ := β')
                typ_var_x!_St₆ typ_var_a!_St₆'
            let Δd : RenamingContext.Context :=
              Function.update
                (Function.update «Δ» x! (some ⟨(α'.fun β').defaultZFSet, α'.fun β',
                  SMTType.mem_toZFSet_of_defaultZFSet⟩))
                a! (some ⟨α'.defaultZFSet, α', SMTType.mem_toZFSet_of_defaultZFSet⟩)
            have hcov_default : RenamingContext.CoversFV Δd (.app (.var x!) (.var a!)) := by
              intro v hv
              simp only [fv, List.mem_append, List.mem_singleton] at hv
              rcases hv with hv | hv
              · subst hv
                dsimp [Δd]
                erw [Function.update_of_ne]
                · erw [Function.update_self]
                  rfl
                · exact x!_ne_a!
              · subst hv
                dsimp [Δd]
                erw [Function.update_self]
                rfl
            have hdefault_spec :=
              defaultSpecMSpec.{u}
                (Δd)
                (Γ := St₆.types) (n := St₆.env.freshvarsc) (used := St₆.env.usedVars)
                (name := s!"{name}_funFun_default")
                (t := .app (.var x!) (.var a!))
                typ_app_default_St₆ hcov_default
            mspec (Std.Do.Triple.and _
              (funRunDefaultSpec
                (τ := β')
                (name := s!"{name}_funFun_default")
                (t := .app (.var x!) (.var a!)) (St := St₆))
              hdefault_spec)
            · rename_i hdefault
              mrename_i pre
              mintro ∀St₇
              mpure pre
              obtain ⟨hrun_default, hn₇, sub₇, used_sub₇, keys₇, preserves_default₇, typ_hdefault_St₇,
                fv_hdefault, den_default⟩ := pre
              have hsub_base_St₇ :
                  AList.insert x! (α'.fun β') St₁.types ⊆ St₇.types := by
                intro v hv
                exact sub₇ (hsub_St₂_St₆ (by erw [← St₂_types_eq] at hv; exact hv))
              have typ_var_x!_base :
                  (AList.insert x! (α'.fun β') St₁.types) ⊢ˢ .var x! : α'.fun β' := by
                apply SMT.Typing.var
                exact AList.lookup_insert St₁.types
              have typ_x_base :
                  (AList.insert x! (α'.fun β') St₁.types) ⊢ˢ x : α.fun β := by
                exact SMT.Typing.weakening
                  (h := SMT.TypeContext.entries_subset_insert_of_notMem x!_fresh)
                  typ_x
              have a_not_base :
                  a ∉ AList.insert x! (α'.fun β') St₁.types := by
                erw [← St₂_types_eq]
                exact a_fresh
              have a!_not_base :
                  a! ∉ AList.insert a α (AList.insert x! (α'.fun β') St₁.types) := by
                erw [← St₂_types_eq, ← St₃_types_eq]
                exact a!_fresh
              have a!_not_base_ctx :
                  a! ∉ AList.insert x! (α'.fun β') St₁.types := by
                intro ha!
                exact a!_not_base (by
                  erw [AList.mem_insert]
                  exact Or.inr ha!)
              have a_in_St₃ : a ∈ St₃.types := by
                erw [St₃_types_eq, AList.mem_insert]
                exact Or.inl rfl
              have a_ne_a! : a ≠ a! := by
                intro haa!
                exact a!_fresh (haa! ▸ a_in_St₃)
              have hsub_a!_base_St₄ :
                  AList.insert a! α' (AList.insert a α (AList.insert x! (α'.fun β') St₁.types)) ⊆
                    St₄.types := by
                intro e he
                exact sub₄ (by
                  erw [← St₂_types_eq, ← St₃_types_eq] at he
                  exact he)
              have b_not_base :
                  b ∉ AList.insert a! α' (AList.insert a α (AList.insert x! (α'.fun β') St₁.types)) := by
                intro hb
                exact b_fresh (typeContext_mem_of_subset hsub_a!_base_St₄ hb)
              have hsub_b_a!_base_St₅ :
                  AList.insert b β
                    (AList.insert a! α' (AList.insert a α (AList.insert x! (α'.fun β') St₁.types))) ⊆
                    St₅.types := by
                erw [St₅_types_eq]
                exact SMT.TypeContext.insert_mono hsub_a!_base_St₄
              have b!_not_base :
                  b! ∉ AList.insert b β
                    (AList.insert a! α' (AList.insert a α (AList.insert x! (α'.fun β') St₁.types))) := by
                intro hb!
                exact b!_fresh (typeContext_mem_of_subset hsub_b_a!_base_St₅ hb!)
              have typ_a!_spec_ctx_base :
                  AList.insert a! α' (AList.insert a α (AList.insert x! (α'.fun β') St₁.types)) ⊢ˢ
                    a!_spec : SMTType.bool := by
                have h := typ_a!_spec_base
                erw [St₃_types_eq, St₂_types_eq] at h
                exact h
              have hsub_b!_ctx :
                  (AList.insert b! β'
                      (AList.insert b β
                        (AList.insert a! α' (AList.insert a α (AList.insert x! (α'.fun β') St₁.types))))).entries ⊆
                    (AList.insert b! β' St₅.types).entries := by
                erw [St₅_types_eq]
                apply SMT.TypeContext.insert_mono
                apply SMT.TypeContext.insert_mono
                intro e he
                exact sub₄ (by
                  erw [← St₂_types_eq, ← St₃_types_eq] at he
                  exact he)
              have hfv_b!_spec_ctx :
                  ∀ v ∈ fv b!_spec,
                    v ∈ AList.insert b! β'
                      (AList.insert b β
                        (AList.insert a! α' (AList.insert a α (AList.insert x! (α'.fun β') St₁.types)))) := by
                intro v hv
                have hv' := fv_b!_spec hv
                erw [List.mem_union_iff] at hv'
                rcases hv' with hv | hv
                · erw [fv, List.mem_singleton] at hv
                  subst hv
                  erw [AList.mem_insert]
                  exact Or.inr (by
                    erw [AList.mem_insert]
                    exact Or.inl rfl)
                · have hv' : v = b! := List.mem_singleton.mp hv
                  subst hv'
                  erw [AList.mem_insert]
                  exact Or.inl rfl
              have typ_b!_spec_ctx_base :
                  AList.insert b! β'
                    (AList.insert b β
                      (AList.insert a! α' (AList.insert a α (AList.insert x! (α'.fun β') St₁.types)))) ⊢ˢ
                    b!_spec : SMTType.bool := by
                exact SMT.Typing.strengthening_of_fv_subset
                  hsub_b!_ctx typ_b!_spec_base hfv_b!_spec_ctx
              have typ_var_a!_St₇ :
                  St₇.types ⊢ˢ .var a! : α' := by
                have typ_var_a!_St₆ :
                    St₆.types ⊢ˢ .var a! : α' := by
                  exact SMT.Typing.weakening (h := hsub_St₄_St₆) typ_var_a!_St₄
                exact SMT.Typing.weakening (h := sub₇) typ_var_a!_St₆
              have hlookup_a!_St₇ :
                  St₇.types.lookup a! = some α' := SMT.Typing.varE typ_var_a!_St₇
              have hsub_hdefault_ctx :
                  (AList.insert a! α' (AList.insert x! (α'.fun β') St₁.types)).entries ⊆ St₇.types.entries := by
                intro e he
                erw [AList.entries_insert_of_notMem a!_not_base_ctx, List.mem_cons] at he
                rcases he with he | he
                · cases he
                  exact AList.mem_lookup_iff.mp hlookup_a!_St₇
                · exact hsub_base_St₇ he
              have hfv_hdefault_ctx :
                  ∀ v ∈ fv hdefault,
                    v ∈ AList.insert a! α' (AList.insert x! (α'.fun β') St₁.types) := by
                intro v hv
                have hv' := fv_hdefault hv
                simp only [fv, List.mem_append, List.mem_singleton] at hv'
                rcases hv' with hv' | hv'
                · subst hv'
                  erw [AList.mem_insert]
                  exact Or.inr (by
                    erw [AList.mem_insert]
                    exact Or.inl rfl)
                · subst hv'
                  erw [AList.mem_insert]
                  exact Or.inl rfl
              have typ_hdefault_base :
                  AList.insert a! α' (AList.insert x! (α'.fun β') St₁.types) ⊢ˢ
                    hdefault : SMTType.bool := by
                exact SMT.Typing.strengthening_of_fv_subset
                  hsub_hdefault_ctx typ_hdefault_St₇ hfv_hdefault_ctx
              have typ_fun_spec_base :
                  AList.insert x! (α'.fun β') St₁.types ⊢ˢ
                    funSpecTerm x x! a a! b b! α β α' β' a!_spec b!_spec hdefault : SMTType.bool := by
                exact funSpecTermTyping
                  (Γ := AList.insert x! (α'.fun β') St₁.types)
                  (x := x) (x! := x!) (a := a) (a! := a!) (b := b) (b! := b!)
                  (α := α) (β := β) (α' := α') (β' := β')
                  typ_x_base typ_var_x!_base
                  a_not_base a!_not_base b_not_base b!_not_base a_ne_a!
                  typ_a!_spec_ctx_base typ_b!_spec_ctx_base typ_hdefault_base
              mspec Std.Do.Spec.pure
              mpure_intro
              and_intros
              · calc
                  St₁.env.freshvarsc ≤ St₂.env.freshvarsc := by
                    erw [St₂_fvc]
                    exact Nat.le_succ _
                  _ ≤ St₃.env.freshvarsc := by
                    erw [St₃_fvc]
                    exact Nat.le_succ _
                  _ ≤ St₄.env.freshvarsc := hn₄
                  _ ≤ St₅.env.freshvarsc := by
                    erw [St₅_fvc]
                    exact Nat.le_succ _
                  _ ≤ St₆.env.freshvarsc := hn₆
                  _ ≤ St₇.env.freshvarsc := hn₇
              · exact hsub_base_St₇
              · exact x!_fresh
              · exact x!_not_used
              · intro v hv
                exact used_sub₇ (used_sub₆ (by
                  erw [St₅_used_eq]
                  exact List.mem_cons_of_mem _ (used_sub₄ (by
                    erw [St₃_used_eq]
                    exact List.mem_cons_of_mem _ (by
                      erw [St₂_used_eq]
                      exact List.mem_cons_of_mem _ hv)))))
              · exact keys₇
              · -- preserves_types
                intro v hv hv_not_Λ
                have hv_ne_x : v ≠ x! := fun h => absurd (h ▸ hv) x!_not_used
                have a_not_used_base : a ∉ St₁.env.usedVars := by
                  intro hmem; apply a_not_used; rw [St₂_used_eq]; exact List.mem_cons_of_mem _ hmem
                have hv_ne_a : v ≠ a := fun h => absurd (h ▸ hv) a_not_used_base
                have hv_not_St₂ : v ∉ St₂.types := by
                  rw [St₂_types_eq, AList.mem_insert]; push_neg; exact ⟨hv_ne_x, hv_not_Λ⟩
                have hv_not_St₃ : v ∉ St₃.types := by
                  rw [St₃_types_eq, AList.mem_insert]; push_neg; exact ⟨hv_ne_a, hv_not_St₂⟩
                have hv_in_St₃_used : v ∈ St₃.env.usedVars := by
                  rw [St₃_used_eq]; exact List.mem_cons_of_mem _ (by rw [St₂_used_eq]; exact List.mem_cons_of_mem _ hv)
                have hv_not_St₄ : v ∉ St₄.types := preserves_a! v hv_in_St₃_used hv_not_St₃
                have b_not_used_base : b ∉ St₁.env.usedVars := by
                  intro hmem; apply b_not_used; exact used_sub₄ (by rw [St₃_used_eq]; exact List.mem_cons_of_mem _ (by rw [St₂_used_eq]; exact List.mem_cons_of_mem _ hmem))
                have hv_ne_b : v ≠ b := fun h => absurd (h ▸ hv) b_not_used_base
                have hv_not_St₅ : v ∉ St₅.types := by
                  rw [St₅_types_eq, AList.mem_insert]; push_neg; exact ⟨hv_ne_b, hv_not_St₄⟩
                have hv_in_St₅_used : v ∈ St₅.env.usedVars := by
                  rw [St₅_used_eq]; exact List.mem_cons_of_mem _ (used_sub₄ (by rw [St₃_used_eq]; exact List.mem_cons_of_mem _ (by rw [St₂_used_eq]; exact List.mem_cons_of_mem _ hv)))
                have hv_not_St₆ : v ∉ St₆.types := preserves_b! v hv_in_St₅_used hv_not_St₅
                have hv_in_St₆_used : v ∈ St₆.env.usedVars := used_sub₆ hv_in_St₅_used
                exact preserves_default₇ v hv_in_St₆_used hv_not_St₆
              · change AList.insert x! (α'.fun β') St₁.types ⊢ˢ Term.var x! : α'.fun β'
                exact typ_var_x!_base
              · change
                  AList.insert x! (α'.fun β') St₁.types ⊢ˢ
                    funSpecTerm x x! a a! b b! α β α' β' a!_spec b!_spec hdefault :
                      SMTType.bool
                exact typ_fun_spec_base
              · change St₇.types ⊢ˢ Term.var x! : α'.fun β'
                exact SMT.Typing.weakening (h := hsub_base_St₇) typ_var_x!_base
              · change
                  St₇.types ⊢ˢ
                    funSpecTerm x x! a a! b b! α β α' β' a!_spec b!_spec hdefault :
                      SMTType.bool
                exact SMT.Typing.weakening (h := hsub_base_St₇) typ_fun_spec_base
              · exact funSpecTermFvSubset
                  (x := x) (x! := x!) (a := a) (a! := a!) (b := b) (b! := b!)
                  (α := α) (β := β) (α' := α') (β' := β')
                  fv_a!_spec fv_b!_spec fv_hdefault
              · intro X denx
                have hX_ty : X.snd.fst = α.fun β := by
                  exact denote_type_eq_of_typing (typ_t := typ_x) (hden := denx)
                have hX_mem : X.fst ∈ ⟦α.fun β⟧ᶻ := by
                  erw [← hX_ty]
                  exact X.snd.snd
                have hX_func : ZFSet.IsFunc ⟦α⟧ᶻ ⟦β⟧ᶻ X.fst := by
                  erw [ZFSet.mem_funs] at hX_mem
                  exact hX_mem
                let castα : ZFSet := (castZF_of_path pα).1
                let castβ : ZFSet := (castZF_of_path pβ).1
                have hcastα : ZFSet.IsFunc ⟦α⟧ᶻ ⟦α'⟧ᶻ castα := by
                  exact (castZF_of_path pα).2
                have hcastβ : ZFSet.IsFunc ⟦β⟧ᶻ ⟦β'⟧ᶻ castβ := by
                  exact (castZF_of_path pβ).2
                let X!zf : ZFSet := funCastTargetZF castα castβ X hcastα hcastβ hX_func
                have hX!zf_mem : X!zf ∈ ⟦α'.fun β'⟧ᶻ := by
                  exact funCastTargetZF_mem castα castβ X hcastα hcastβ hX_func
                let X! : SMT.Dom := ⟨X!zf, α'.fun β', hX!zf_mem⟩
                have hden_var_x! :
                    ⟦(Term.var x!).abstract (Function.update «Δ» x! (some X!)) (pf x! X!)⟧ˢ =
                      some X! := by
                  erw [SMT.Term.abstract.eq_def, SMT.denote, Option.pure_def, Option.some.injEq]
                  apply Option.get_of_eq_some
                  erw [Function.update_self]
                let fun_spec : Term :=
                  funSpecTerm x x! a a! b b! α β α' β' a!_spec b!_spec hdefault
                have hfv_fun_spec :
                    fv fun_spec ⊆ fv x ∪ {x!} := by
                  exact funSpecTermFvSubset
                    (x := x) (x! := x!) (a := a) (a! := a!) (b := b) (b! := b!)
                    (α := α) (β := β) (α' := α') (β' := β')
                    fv_a!_spec fv_b!_spec fv_hdefault
                have hφX! :
                    RenamingContext.CoversFV
                      (Function.update «Δ» x! (some X!))
                      fun_spec := by
                  exact funSpecTermCoversUpdate
                    (x := x) (x! := x!) (a := a) (a! := a!) (b := b) (b! := b!)
                    (α := α) (β := β) (α' := α') (β' := β')
                    hx hfv_fun_spec X!
                have hcast_mem :
                    X.fst.pair X!.fst ∈ (castZF_of_path (castPath.fun hβ pα pβ)).1 := by
                  change X.fst.pair X!.fst ∈ (castZF_fun (castZF_of_path pα) (castZF_of_path pβ)).1
                  rw [castZF_fun, ZFSet.lambda_spec]
                  refine ⟨hX_mem, hX!zf_mem, ?_⟩
                  rw [dif_pos hX_func]
                  rfl
                have hX!_func : ZFSet.IsFunc ⟦α'⟧ᶻ ⟦β'⟧ᶻ X!.fst := by
                  simpa [X!, X!zf] using
                    funCastTargetZF_isFunc castα castβ X hcastα hcastβ hX_func
                have hX!_app_default :
                    ∀ (wy0 : SMT.Dom) (hwy0_ty : wy0.snd.fst = α')
                      (hy_not_ran : wy0.fst ∉ castα.Range),
                      ZFSet.fapply X!.fst (ZFSet.is_func_is_pfunc hX!_func)
                        ⟨wy0.fst, by
                          simpa [ZFSet.is_func_dom_eq hX!_func, hwy0_ty] using wy0.snd.snd⟩ =
                        β'.defaultZFSet := by
                  intro wy0 hwy0_ty hy_not_ran
                  simpa [X!, X!zf, castα] using funCastTargetZF_app_default castα castβ X hcastα hcastβ (castZF_of_path_injective pα) hX_func wy0 hwy0_ty hy_not_ran
                have hX!_app_range :
                    ∀ (wy0 : SMT.Dom) (hwy0_ty : wy0.snd.fst = α')
                      (hy_ran : wy0.fst ∈ castα.Range),
                      ∃ (x₀ : ZFSet) (hx₀_mem : x₀ ∈ ⟦α⟧ᶻ),
                        @ᶻcastα
                          ⟨x₀, by
                            rw [ZFSet.is_func_dom_eq hcastα]
                            exact hx₀_mem⟩ = wy0.fst ∧
                        ZFSet.fapply X!.fst (ZFSet.is_func_is_pfunc hX!_func)
                          ⟨wy0.fst, by
                            simpa [ZFSet.is_func_dom_eq hX!_func, hwy0_ty] using wy0.snd.snd⟩ =
                          @ᶻcastβ
                            ⟨@ᶻX.fst
                                ⟨x₀, by
                                  simpa [ZFSet.is_func_dom_eq hX_func] using hx₀_mem⟩, by
                                  rw [ZFSet.is_func_dom_eq (castZF_of_path pβ).2]
                                  exact Subtype.property _⟩ := by
                  intro wy0 hwy0_ty hy_ran
                  simpa [X!, X!zf, castα, castβ] using
                    funCastTargetZF_app_range castα castβ X hcastα hcastβ hX_func
                      wy0 hwy0_ty hy_ran
                have x!_not_mem_fv_x : x! ∉ fv x := by
                  intro hx!_fv
                  exact x!_fresh (SMT.Typing.mem_context_of_mem_fv typ_x hx!_fv)
                have a_not_mem_fv_x : a ∉ fv x := by
                  intro ha_fv
                  exact a_fresh (by
                    rw [St₂_types_eq, AList.mem_insert]
                    exact Or.inr (SMT.Typing.mem_context_of_mem_fv typ_x ha_fv))
                have b_not_mem_fv_x : b ∉ fv x := by
                  intro hb_fv
                  have hb_mem_St₁ : b ∈ St₁.types :=
                    SMT.Typing.mem_context_of_mem_fv typ_x hb_fv
                  have hb_mem_St₂ : b ∈ St₂.types := by
                    rw [St₂_types_eq]
                    exact typeContext_mem_of_subset
                      (SMT.TypeContext.entries_subset_insert_of_notMem x!_fresh) hb_mem_St₁
                  have hb_mem_St₃ : b ∈ St₃.types := by
                    rw [St₃_types_eq]
                    exact typeContext_mem_of_subset
                      (SMT.TypeContext.entries_subset_insert_of_notMem a_fresh) hb_mem_St₂
                  exact b_fresh <| typeContext_mem_of_subset sub₄ <| by
                    rw [AList.mem_insert]
                    exact Or.inr hb_mem_St₃
                have a!_not_mem_fv_x : a! ∉ fv x := by
                  intro ha!_fv
                  have ha!_mem_St₁ : a! ∈ St₁.types :=
                    SMT.Typing.mem_context_of_mem_fv typ_x ha!_fv
                  have ha!_mem_St₂ : a! ∈ St₂.types := by
                    rw [St₂_types_eq]
                    exact typeContext_mem_of_subset
                      (SMT.TypeContext.entries_subset_insert_of_notMem x!_fresh) ha!_mem_St₁
                  have ha!_mem_St₃ : a! ∈ St₃.types := by
                    rw [St₃_types_eq]
                    exact typeContext_mem_of_subset
                      (SMT.TypeContext.entries_subset_insert_of_notMem a_fresh) ha!_mem_St₂
                  exact a!_fresh ha!_mem_St₃
                have b!_not_mem_fv_x : b! ∉ fv x := by
                  intro hb!_fv
                  have hb!_mem_St₁ : b! ∈ St₁.types :=
                    SMT.Typing.mem_context_of_mem_fv typ_x hb!_fv
                  have hb!_mem_St₂ : b! ∈ St₂.types := by
                    rw [St₂_types_eq]
                    exact typeContext_mem_of_subset
                      (SMT.TypeContext.entries_subset_insert_of_notMem x!_fresh) hb!_mem_St₁
                  have hb!_mem_St₃ : b! ∈ St₃.types := by
                    rw [St₃_types_eq]
                    exact typeContext_mem_of_subset
                      (SMT.TypeContext.entries_subset_insert_of_notMem a_fresh) hb!_mem_St₂
                  have hb!_mem_St₄ : b! ∈ St₄.types := by
                    exact typeContext_mem_of_subset sub₄ (by
                      rw [AList.mem_insert]
                      exact Or.inr hb!_mem_St₃)
                  have hb!_mem_St₅ : b! ∈ St₅.types := by
                    rw [St₅_types_eq, AList.mem_insert]
                    exact Or.inr hb!_mem_St₄
                  exact b!_fresh hb!_mem_St₅
                have den_xa_at :
                    ∀ (Yfun x₀ : SMT.Dom) (hx₀_ty : x₀.snd.fst = α)
                      (hx₀_mem : x₀.fst ∈ ⟦α⟧ᶻ),
                      ∃ hcov_app :
                        RenamingContext.CoversFV
                          (Function.update (Function.update «Δ» x! (some Yfun)) a (some x₀))
                          ((@ˢx) (Term.var a)),
                        ∃ Dapp : SMT.Dom,
                          Dapp.snd.fst = β ∧
                            Dapp.fst =
                              @ᶻX.fst
                                ⟨x₀.fst, by
                                  simpa [ZFSet.is_func_dom_eq hX_func] using hx₀_mem⟩ ∧
                            ⟦((@ˢx) (Term.var a)).abstract
                                (Function.update (Function.update «Δ» x! (some Yfun)) a (some x₀))
                                hcov_app⟧ˢ =
                              some Dapp := by
                  intro Yfun x₀ hx₀_ty hx₀_mem
                  exact funDenoteAppAt
                    (Δctx := Function.update «Δ» x! (some Yfun))
                    (t := x) (x := a) (α := α) (β := β) (Y := X)
                    (hcov_t_upd := by
                      intro Xarg
                      exact SMT.RenamingContext.coversFV_update_of_notMem
                        (x := a) (d := Xarg) a_not_mem_fv_x
                        (SMT.RenamingContext.coversFV_update_of_notMem
                          (x := x!) (d := Yfun) x!_not_mem_fv_x hx))
                    (den_t_upd := by
                      intro Xarg
                      calc
                        ⟦x.abstract
                            (Function.update (Function.update «Δ» x! (some Yfun)) a (some Xarg))
                            (SMT.RenamingContext.coversFV_update_of_notMem
                              (x := a) (d := Xarg) a_not_mem_fv_x
                              (SMT.RenamingContext.coversFV_update_of_notMem
                                (x := x!) (d := Yfun) x!_not_mem_fv_x hx))⟧ˢ =
                            SMT.RenamingContext.denote
                              (Function.update (Function.update «Δ» x! (some Yfun)) a (some Xarg))
                              x
                              (SMT.RenamingContext.coversFV_update_of_notMem
                                (x := a) (d := Xarg) a_not_mem_fv_x
                                (SMT.RenamingContext.coversFV_update_of_notMem
                                  (x := x!) (d := Yfun) x!_not_mem_fv_x hx)) := by
                              rfl
                        _ =
                            SMT.RenamingContext.denote (Function.update «Δ» x! (some Yfun)) x
                              (SMT.RenamingContext.coversFV_update_of_notMem
                                (x := x!) (d := Yfun) x!_not_mem_fv_x hx) := by
                              exact (SMT.RenamingContext.denote_update_of_notMem
                                (x := a) (d := Xarg)
                                (h := SMT.RenamingContext.coversFV_update_of_notMem
                                  (x := x!) (d := Yfun) x!_not_mem_fv_x hx)
                                a_not_mem_fv_x).symm
                        _ = SMT.RenamingContext.denote «Δ» x hx := by
                              exact (SMT.RenamingContext.denote_update_of_notMem
                                (x := x!) (d := Yfun) (h := hx) x!_not_mem_fv_x).symm
                        _ = some X := denx)
                    (hY_ty := hX_ty) (hY_func := hX_func) x₀ hx₀_ty hx₀_mem
                have b_ne_b! : b ≠ b! := by
                  intro h
                  have hb!_in_St₅ : b! ∈ St₅.types := by
                    rw [← h]
                    exact SMT.Typing.mem_context_of_mem_fv typ_var_b_St₅ (by simp [fv])
                  exact b!_fresh hb!_in_St₅
                have a!_ne_b! : a! ≠ b! := by
                  intro h
                  have ha!_in_St₄ : a! ∈ St₄.types := by
                    exact typeContext_mem_of_subset sub₄ (by
                      rw [AList.mem_insert]
                      exact Or.inl rfl)
                  have ha!_in_St₅ : a! ∈ St₅.types := by
                    rw [St₅_types_eq, AList.mem_insert]
                    exact Or.inr ha!_in_St₄
                  exact b!_fresh (h ▸ ha!_in_St₅)
                have hφa_at :
                    ∀ (Yfun x₀ wy0 : SMT.Dom),
                      RenamingContext.CoversFV
                        (Function.update
                          (Function.update (Function.update «Δ» x! (some Yfun)) a (some x₀))
                          a! (some wy0))
                        a!_spec := by
                  intro Yfun x₀ wy0
                  exact funASpecCoversAt
                    («Δ» := «Δ») (x! := x!) (a := a) (a! := a!)
                    (a!_spec := a!_spec) fv_a!_spec a_ne_a! Yfun x₀ wy0
                have hφb_at :
                    ∀ (Yfun wy0 y₀ wy1 : SMT.Dom),
                      RenamingContext.CoversFV
                        (Function.update
                          (Function.update
                            (Function.update (Function.update «Δ» x! (some Yfun)) a! (some wy0))
                            b (some y₀))
                          b! (some wy1))
                        b!_spec := by
                  intro Yfun wy0 y₀ wy1
                  exact funBSpecCoversAt
                    («Δ» := «Δ») (x! := x!) (a! := a!) (b := b) (b! := b!)
                    (b!_spec := b!_spec) fv_b!_spec b_ne_b! Yfun wy0 y₀ wy1
                have a_spec_total_at :
                    ∀ (Yfun x₀ wy0 : SMT.Dom)
                      (hx₀_ty : x₀.snd.fst = α)
                      (hwy0_ty : wy0.snd.fst = α'),
                      ⟦a!_spec.abstract
                          (Function.update
                            (Function.update (Function.update «Δ» x! (some Yfun)) a (some x₀))
                            a! (some wy0))
                          (hφa_at Yfun x₀ wy0)⟧ˢ.isSome =
                        true := by
                  intro Yfun x₀ wy0 hx₀_ty hwy0_ty
                  exact funVarSpecTotalAt
                    («Δ» := Function.update «Δ» x! (some Yfun))
                    (p := pα) pα_ih_exact
                    (sub := keys₃) (typ_var_z := typ_var_a_St₃) (hrun := hrun_a)
                    x₀ wy0 hx₀_ty hwy0_ty (hφa_at Yfun x₀ wy0)
                have b_spec_total_at :
                    ∀ (Yfun wy0 y₀ wy1 : SMT.Dom)
                      (hy₀_ty : y₀.snd.fst = β)
                      (hwy1_ty : wy1.snd.fst = β'),
                      ⟦b!_spec.abstract
                          (Function.update
                            (Function.update
                              (Function.update (Function.update «Δ» x! (some Yfun)) a! (some wy0))
                              b (some y₀))
                            b! (some wy1))
                          (hφb_at Yfun wy0 y₀ wy1)⟧ˢ.isSome =
                        true := by
                  intro Yfun wy0 y₀ wy1 hy₀_ty hwy1_ty
                  exact funVarSpecTotalAt
                    («Δ» := Function.update (Function.update «Δ» x! (some Yfun)) a! (some wy0))
                    (p := pβ) pβ_ih_exact
                    (sub := keys₅) (typ_var_z := typ_var_b_St₅) (hrun := hrun_b)
                    y₀ wy1 hy₀_ty hwy1_ty (hφb_at Yfun wy0 y₀ wy1)
                have a_spec_true_at :
                    ∀ (Yfun x₀ wy0 : SMT.Dom)
                      (hx₀_ty : x₀.snd.fst = α)
                      (hwy0_ty : wy0.snd.fst = α')
                      (hcast_x₀w : x₀.fst.pair wy0.fst ∈ ↑(castZF_of_path pα).1),
                      ∃ (hφa :
                        RenamingContext.CoversFV
                          (Function.update
                            (Function.update (Function.update «Δ» x! (some Yfun)) a (some x₀))
                            a! (some wy0))
                          a!_spec)
                        (Φa : SMT.Dom),
                        ⟦a!_spec.abstract
                            (Function.update
                              (Function.update (Function.update «Δ» x! (some Yfun)) a (some x₀))
                              a! (some wy0))
                            hφa⟧ˢ =
                          some Φa ∧
                        Φa.fst = zftrue := by
                  intro Yfun x₀ wy0 hx₀_ty hwy0_ty hcast_x₀w
                  exact funVarSpecTrueAtCast
                    («Δ» := Function.update «Δ» x! (some Yfun))
                    (p := pα) pα_ih_exact
                    (sub := keys₃) (typ_var_z := typ_var_a_St₃)
                    (typ_var_z! := typ_var_a!_St₄) (hrun := hrun_a)
                    x₀ wy0 hx₀_ty hwy0_ty hcast_x₀w
                have b_spec_true_at :
                    ∀ (Yfun wy0 y₀ wy1 : SMT.Dom)
                      (hy₀_ty : y₀.snd.fst = β)
                      (hwy1_ty : wy1.snd.fst = β')
                      (hcast_y₀w : y₀.fst.pair wy1.fst ∈ ↑(castZF_of_path pβ).1),
                      ∃ (hφb :
                        RenamingContext.CoversFV
                          (Function.update
                            (Function.update
                              (Function.update (Function.update «Δ» x! (some Yfun)) a! (some wy0))
                              b (some y₀))
                            b! (some wy1))
                          b!_spec)
                        (Φb : SMT.Dom),
                        ⟦b!_spec.abstract
                            (Function.update
                              (Function.update
                                (Function.update (Function.update «Δ» x! (some Yfun)) a! (some wy0))
                                b (some y₀))
                              b! (some wy1))
                            hφb⟧ˢ =
                          some Φb ∧
                        Φb.fst = zftrue := by
                  intro Yfun wy0 y₀ wy1 hy₀_ty hwy1_ty hcast_y₀w
                  exact funVarSpecTrueAtCast
                    («Δ» := Function.update (Function.update «Δ» x! (some Yfun)) a! (some wy0))
                    (p := pβ) pβ_ih_exact
                    (sub := keys₅) (typ_var_z := typ_var_b_St₅)
                    (typ_var_z! := typ_var_b!_St₆) (hrun := hrun_b)
                    y₀ wy1 hy₀_ty hwy1_ty hcast_y₀w
                have a_spec_true_implies_cast :
                    ∀ (Yfun x₀ wy0 : SMT.Dom)
                      (hx₀_ty : x₀.snd.fst = α)
                      (hwy0_ty : wy0.snd.fst = α')
                      (hφa :
                        RenamingContext.CoversFV
                          (Function.update
                            (Function.update (Function.update «Δ» x! (some Yfun)) a (some x₀))
                            a! (some wy0))
                          a!_spec)
                      {Φa : SMT.Dom},
                      ⟦a!_spec.abstract
                          (Function.update
                            (Function.update (Function.update «Δ» x! (some Yfun)) a (some x₀))
                            a! (some wy0))
                          hφa⟧ˢ =
                        some Φa →
                      Φa.fst = zftrue →
                      x₀.fst.pair wy0.fst ∈ ↑(castZF_of_path pα).1 := by
                  intro Yfun x₀ wy0 hx₀_ty hwy0_ty hφa Φa hdenΦa htrueΦa
                  exact funVarSpecTrueImpliesCast
                    («Δ» := Function.update «Δ» x! (some Yfun))
                    (p := pα) pα_ih_exact
                    (sub := keys₃) (typ_var_z := typ_var_a_St₃) (hrun := hrun_a)
                    x₀ wy0 hx₀_ty hwy0_ty hφa hdenΦa htrueΦa
                have b_spec_true_implies_cast :
                    ∀ (Yfun wy0 y₀ wy1 : SMT.Dom)
                      (hy₀_ty : y₀.snd.fst = β)
                      (hwy1_ty : wy1.snd.fst = β')
                      (hφb :
                        RenamingContext.CoversFV
                          (Function.update
                            (Function.update
                              (Function.update (Function.update «Δ» x! (some Yfun)) a! (some wy0))
                              b (some y₀))
                            b! (some wy1))
                          b!_spec)
                      {Φb : SMT.Dom},
                      ⟦b!_spec.abstract
                          (Function.update
                            (Function.update
                              (Function.update (Function.update «Δ» x! (some Yfun)) a! (some wy0))
                              b (some y₀))
                            b! (some wy1))
                          hφb⟧ˢ =
                        some Φb →
                      Φb.fst = zftrue →
                      y₀.fst.pair wy1.fst ∈ ↑(castZF_of_path pβ).1 := by
                  intro Yfun wy0 y₀ wy1 hy₀_ty hwy1_ty hφb Φb hdenΦb htrueΦb
                  exact funVarSpecTrueImpliesCast
                    («Δ» := Function.update (Function.update «Δ» x! (some Yfun)) a! (some wy0))
                    (p := pβ) pβ_ih_exact
                    (sub := keys₅) (typ_var_z := typ_var_b_St₅) (hrun := hrun_b)
                    y₀ wy1 hy₀_ty hwy1_ty hφb hdenΦb htrueΦb
                have hcov_app_at :
                    ∀ (Yfun wy0 : SMT.Dom),
                      RenamingContext.CoversFV
                        (Function.update (Function.update «Δ» x! (some Yfun)) a! (some wy0))
                        ((@ˢTerm.var x!) (Term.var a!)) := by
                  intro Yfun wy0 v hv
                  simp only [fv, List.mem_append, List.mem_singleton] at hv
                  rcases hv with hv | hv
                  · subst hv
                    rw [Function.update_of_ne x!_ne_a!]
                    rw [Function.update_self]
                    rfl
                  · subst hv
                    rw [Function.update_self]
                    rfl
                have den_app_at :
                    ∀ (Yfun wy0 : SMT.Dom)
                      (hYfun_ty : Yfun.snd.fst = α'.fun β')
                      (hYfun_func : ZFSet.IsFunc ⟦α'⟧ᶻ ⟦β'⟧ᶻ Yfun.fst)
                      (hwy0_ty : wy0.snd.fst = α'),
                      ∃ Dapp : SMT.Dom,
                        Dapp.snd.fst = β' ∧
                          Dapp.fst =
                            @ᶻYfun.fst
                              ⟨wy0.fst, by
                                simpa [ZFSet.is_func_dom_eq hYfun_func, hwy0_ty] using wy0.snd.snd⟩ ∧
                          ⟦((@ˢTerm.var x!) (Term.var a!)).abstract
                              (Function.update (Function.update «Δ» x! (some Yfun)) a! (some wy0))
                              (hcov_app_at Yfun wy0)⟧ˢ =
                            some Dapp := by
                  intro Yfun wy0 hYfun_ty hYfun_func hwy0_ty
                  have hwy0_mem : wy0.fst ∈ ⟦α'⟧ᶻ := by
                    simpa [hwy0_ty] using wy0.snd.snd
                  obtain ⟨hcov_app, Dapp, hDapp_ty, hDapp_val, hden_app⟩ :=
                    funDenoteAppAt
                      (Δctx := Function.update «Δ» x! (some Yfun)) (t := .var x!) (x := a!)
                      (α := α') (β := β') (Y := Yfun)
                      (hcov_t_upd := by
                        intro Xarg v hv
                        rw [fv, List.mem_singleton] at hv
                        subst hv
                        simp [Function.update, x!_ne_a!])
                      (den_t_upd := by
                        intro Xarg
                        rw [SMT.Term.abstract.eq_def, SMT.denote, Option.pure_def, Option.some.injEq]
                        apply Option.get_of_eq_some
                        rw [Function.update_of_ne x!_ne_a!]
                        exact Function.update_self _ _ _)
                      (hY_ty := hYfun_ty) (hY_func := hYfun_func)
                      wy0 hwy0_ty hwy0_mem
                  exact ⟨Dapp, hDapp_ty, hDapp_val, hden_app⟩
                have default_spec_at :
                    ∀ (Yfun wy0 Dapp : SMT.Dom)
                      (hden_app :
                        ⟦((@ˢTerm.var x!) (Term.var a!)).abstract
                            (Function.update (Function.update «Δ» x! (some Yfun)) a! (some wy0))
                            (hcov_app_at Yfun wy0)⟧ˢ =
                          some Dapp),
                      ∃ (hφd :
                        RenamingContext.CoversFV
                          (Function.update (Function.update «Δ» x! (some Yfun)) a! (some wy0))
                          hdefault)
                        (Φd : SMT.Dom),
                        ⟦hdefault.abstract
                            (Function.update (Function.update «Δ» x! (some Yfun)) a! (some wy0))
                            hφd⟧ˢ =
                          some Φd ∧
                        Φd.snd.fst = SMTType.bool ∧
                        (Dapp.fst = β'.defaultZFSet → Φd.fst = zftrue) := by
                  intro Yfun wy0 Dapp hden_app
                  exact funDefaultSpecAt
                    («Δ» := Function.update (Function.update «Δ» x! (some Yfun)) a! (some wy0))
                    (St₁ := St₆) (St₂ := St₇)
                    (name := s!"{name}_funFun_default")
                    (t := .app (.var x!) (.var a!)) (spec := hdefault)
                    keys₆ typ_app_default_St₆ (hcov_app_at Yfun wy0) hrun_default Dapp hden_app
                have hex_fun_spec :
                    ∃ Φ : SMT.Dom,
                      ⟦fun_spec.abstract (Function.update «Δ» x! (some X!)) hφX!⟧ˢ = some Φ ∧
                        Φ.snd.fst = SMTType.bool ∧
                        Φ.fst = zftrue :=
                  funDenSpecTrueAtCast
                    (pα := pα) (pβ := pβ)
                    (hX!_ty := rfl)
                    (typ_fun_spec_base := typ_fun_spec_base)
                    (typ_a!_spec_ctx_base := typ_a!_spec_ctx_base)
                    (typ_b!_spec_ctx_base := typ_b!_spec_ctx_base)
                    (fv_a!_spec := fv_a!_spec)
                    (fv_b!_spec := fv_b!_spec)
                    (hφX! := hφX!)
                    (castα := castα) (castβ := castβ)
                    (hcastα := hcastα) (hcastβ := hcastβ)
                    (hcastα_inj := castZF_of_path_injective pα)
                    (hX_func := hX_func) (hX!_func := hX!_func)
                    (hX!_app_default := hX!_app_default)
                    (hX!_app_range := hX!_app_range)
                    (x!_ne_a! := x!_ne_a!)
                    (x!_ne_b! := x!_ne_b!)
                    (a_ne_a! := a_ne_a!)
                    (b_not_base := b_not_base)
                    (b!_not_base := b!_not_base)
                    (a_not_mem_fv_x := a_not_mem_fv_x)
                    (b_not_mem_fv_x := b_not_mem_fv_x)
                    (a!_not_mem_fv_x := a!_not_mem_fv_x)
                    (b!_not_mem_fv_x := b!_not_mem_fv_x)
                    (den_xa_at := den_xa_at)
                    (hφa_at := hφa_at)
                    (hφb_at := hφb_at)
                    (a_spec_total_at := a_spec_total_at)
                    (b_spec_total_at := b_spec_total_at)
                    (a_spec_true_at := a_spec_true_at)
                    (b_spec_true_at := b_spec_true_at)
                    (a_spec_true_implies_cast := a_spec_true_implies_cast)
                    (b_spec_true_implies_cast := b_spec_true_implies_cast)
                    (den_app_at := den_app_at)
                    (default_spec_at := default_spec_at)
                let Φ : SMT.Dom := Classical.choose hex_fun_spec
                have hfun_spec_total :
                    ∀ (Y : SMT.Dom), Y.snd.fst = α'.fun β' →
                      ∀ (hφY :
                        RenamingContext.CoversFV (Function.update «Δ» x! (some Y)) fun_spec),
                        ⟦fun_spec.abstract (Function.update «Δ» x! (some Y)) hφY⟧ˢ.isSome = true := by
                  intro Y hY_ty hφY
                  have hY_mem : Y.fst ∈ ⟦α'.fun β'⟧ᶻ := by
                    rw [← hY_ty]
                    exact Y.snd.snd
                  have hY_func : ZFSet.IsFunc ⟦α'⟧ᶻ ⟦β'⟧ᶻ Y.fst := by
                    rw [ZFSet.mem_funs] at hY_mem
                    exact hY_mem
                  exact funSpecTotalAt
                    (hY_ty := hY_ty)
                    (hY_func := hY_func)
                    (typ_fun_spec_base := typ_fun_spec_base)
                    (typ_a!_spec_ctx_base := typ_a!_spec_ctx_base)
                    (typ_b!_spec_ctx_base := typ_b!_spec_ctx_base)
                    (fv_a!_spec := fv_a!_spec)
                    (fv_b!_spec := fv_b!_spec)
                    (castα := castα)
                    (hcastα := hcastα)
                    (castα_preimage := by
                      intro wy0 hwy0_ty hy_ran
                      obtain ⟨x₀, hx₀_mem, hcast_x₀_wy0, _⟩ :=
                        hX!_app_range wy0 hwy0_ty hy_ran
                      exact ⟨x₀, hx₀_mem, hcast_x₀_wy0⟩)
                    (x!_ne_a! := x!_ne_a!)
                    (x!_ne_b! := x!_ne_b!)
                    (a_ne_a! := a_ne_a!)
                    (b_not_base := b_not_base)
                    (b!_not_base := b!_not_base)
                    (a_not_mem_fv_x := a_not_mem_fv_x)
                    (b_not_mem_fv_x := b_not_mem_fv_x)
                    (a!_not_mem_fv_x := a!_not_mem_fv_x)
                    (b!_not_mem_fv_x := b!_not_mem_fv_x)
                    (den_xa_at := by
                      intro x₀ hx₀_ty hx₀_mem
                      obtain ⟨hcov_app, Dapp, hDapp_ty, _, hden_xa⟩ :=
                        den_xa_at Y x₀ hx₀_ty hx₀_mem
                      exact ⟨hcov_app, Dapp, hDapp_ty, hden_xa⟩)
                    (hφa_at := by
                      intro x₀ wy0
                      exact hφa_at Y x₀ wy0)
                    (hφb_at := by
                      intro wy0 y₀ wy1
                      exact hφb_at Y wy0 y₀ wy1)
                    (a_spec_total_at := by
                      intro x₀ wy0 hx₀_ty hwy0_ty
                      exact a_spec_total_at Y x₀ wy0 hx₀_ty hwy0_ty)
                    (b_spec_total_at := by
                      intro wy0 y₀ wy1 hy₀_ty hwy1_ty
                      exact b_spec_total_at Y wy0 y₀ wy1 hy₀_ty hwy1_ty)
                    (a_spec_true_at := by
                      intro x₀ wy0 hx₀_ty hwy0_ty hcast_x₀w
                      simpa [castα] using
                        a_spec_true_at Y x₀ wy0 hx₀_ty hwy0_ty hcast_x₀w)
                    (a_spec_true_implies_cast := by
                      intro x₀ wy0 hx₀_ty hwy0_ty hφa Φa hden_a htrue_a
                      simpa [castα] using
                        a_spec_true_implies_cast Y x₀ wy0 hx₀_ty hwy0_ty hφa hden_a htrue_a)
                    (den_app_at := by
                      intro wy0 hwy0_ty
                      obtain ⟨Dapp, hDapp_ty, hDapp_val, hden_app⟩ :=
                        den_app_at Y wy0 hY_ty hY_func hwy0_ty
                      exact ⟨Dapp, hDapp_ty, hDapp_val, hden_app⟩)
                    (default_spec_at := by
                      intro wy0 Dapp hden_app
                      exact default_spec_at Y wy0 Dapp hden_app)
                    (hφY := hφY)
                have hfun_spec_true_implies_cast :
                    ∀ (Y : SMT.Dom), Y.snd.fst = α'.fun β' →
                      ∀ (hφY :
                        RenamingContext.CoversFV (Function.update «Δ» x! (some Y)) fun_spec),
                        ∀ {ΦY : SMT.Dom},
                          ⟦fun_spec.abstract (Function.update «Δ» x! (some Y)) hφY⟧ˢ = some ΦY →
                            ΦY.fst = zftrue →
                              X.fst.pair Y.fst ∈ (castZF_of_path (castPath.fun hβ pα pβ)).1 := by
                  intro Y hY_ty hφY ΦY hdenΦY htrueΦY
                  exact funSpecTrueImpliesCastAt
                    (hβ := hβ)
                    (hY_ty := hY_ty)
                    (hX!_ty := rfl)
                    (typ_fun_spec_base := typ_fun_spec_base)
                    (typ_a!_spec_ctx_base := typ_a!_spec_ctx_base)
                    (typ_b!_spec_ctx_base := typ_b!_spec_ctx_base)
                    (fv_a!_spec := fv_a!_spec)
                    (fv_b!_spec := fv_b!_spec)
                    (castα := castα)
                    (castβ := castβ)
                    (hcastα := hcastα)
                    (hcastβ := hcastβ)
                    (hcastα_eq := rfl)
                    (hcastβ_eq := rfl)
                    (hX_func := hX_func)
                    (hcast_mem := hcast_mem)
                    (hX!_func := hX!_func)
                    (hX!_app_default := hX!_app_default)
                    (hX!_app_range := hX!_app_range)
                    (x!_ne_a! := x!_ne_a!)
                    (x!_ne_b! := x!_ne_b!)
                    (a_ne_a! := a_ne_a!)
                    (b_not_base := b_not_base)
                    (b!_not_base := b!_not_base)
                    (a_not_mem_fv_x := a_not_mem_fv_x)
                    (b_not_mem_fv_x := b_not_mem_fv_x)
                    (a!_not_mem_fv_x := a!_not_mem_fv_x)
                    (b!_not_mem_fv_x := b!_not_mem_fv_x)
                    (den_xa_at := den_xa_at)
                    (hφa_at := hφa_at)
                    (hφb_at := hφb_at)
                    (a_spec_total_at := a_spec_total_at)
                    (b_spec_total_at := b_spec_total_at)
                    (a_spec_true_at := a_spec_true_at)
                    (b_spec_true_at := b_spec_true_at)
                    (a_spec_true_implies_cast := a_spec_true_implies_cast)
                    (b_spec_true_implies_cast := b_spec_true_implies_cast)
                    (den_app_at := den_app_at)
                    (default_spec_at := default_spec_at)
                    (default_true_implies_default_at := by
                      intro Yfun wy0 Dapp hden_app hφd Φd hdenΦd htrueΦd
                      exact funDefaultTrueImpliesDefaultAt
                        («Δ» := Function.update (Function.update «Δ» x! (some Yfun)) a! (some wy0))
                        (St₁ := St₆) (St₂ := St₇)
                        (name := s!"{name}_funFun_default")
                        (t := .app (.var x!) (.var a!)) (spec := hdefault)
                        keys₆ typ_app_default_St₆ (hcov_app_at Yfun wy0) hrun_default
                        Dapp hden_app hφd hdenΦd htrueΦd)
                    (hφY := hφY)
                    (hdenΦY := hdenΦY)
                    (htrue := htrueΦY)
                have hden_fun_spec' :
                    ⟦fun_spec.abstract (Function.update «Δ» x! (some X!)) hφX!⟧ˢ = some Φ := by
                  exact (Classical.choose_spec hex_fun_spec).1
                have hΦ_ty : Φ.snd.fst = SMTType.bool := by
                  exact (Classical.choose_spec hex_fun_spec).2.1
                have hΦ_true : Φ.fst = zftrue := by
                  exact (Classical.choose_spec hex_fun_spec).2.2
                refine ⟨Φ, X!, hden_var_x!, hφX!, hden_fun_spec', hΦ_ty, ?_, ?_⟩
                · exact ⟨hΦ_true, hcast_mem⟩
                · intro Y hY_ty hφY
                  refine ⟨hfun_spec_total Y hY_ty hφY, ?_⟩
                  intro ΦY hdenΦY htrueΦY
                  exact hfun_spec_true_implies_cast Y hY_ty hφY hdenΦY htrueΦY
