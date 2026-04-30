import SMT.Reasoning.Defs
import SMT.Reasoning.LooseningDefs
import SMT.Reasoning.Basic.StateSpecs
import SMT.Reasoning.Basic.LoosenAuxExact

open Std.Do SMT ZFSet Classical

set_option maxHeartbeats 800000 in
theorem loosenAux_prf_spec.fun («Δ» : RenamingContext.Context)
  (pf : ∀ (x! : 𝒱) (X! : SMT.Dom), ∀ v ∈ fv (Term.var x!), (Function.update «Δ» x! (some X!) v).isSome = true)
  {α β α' β' : SMTType} (hβ : β ≠ SMTType.bool) (pα : α ⇝ α') (pβ : β ⇝ β')
  (_pα_ih :
    ∀ {Λ : TypeContext} {n : ℕ} {used : List 𝒱} {name : String} {x : Term},
      Λ ⊢ˢ x : α →
        ∀ («Δ₀» : RenamingContext.Context) (hx : RenamingContext.CoversFV «Δ₀» x)
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
  (_pβ_ih :
    ∀ {Λ : TypeContext} {n : ℕ} {used : List 𝒱} {name : String} {x : Term},
      Λ ⊢ˢ x : β →
        ∀ («Δ₀» : RenamingContext.Context) (hx : RenamingContext.CoversFV «Δ₀» x)
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
  {Λ : TypeContext} {n : ℕ} {used : List 𝒱} {name : String} {x : Term} (typ_x : Λ ⊢ˢ x : α.fun β)
  (hx : RenamingContext.CoversFV «Δ» x) :
  ⦃fun ⟨E, Λ'⟩ ↦ ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ AList.keys Λ' ⊆ E.usedVars ∧ E.usedVars = used⌝⦄
    loosenAux_prf name (castPath.fun hβ pα pβ) x ⦃⇓? ⟨x!, x!_spec⟩ ⟨E', Γ'⟩  =>
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
                                  ∀ (X : SMT.Dom),
                                    ⟦x.abstract «Δ» hx⟧ˢ = some X →
                                      ∃ Φ X!,
                                        ∃ (_denx! : ⟦(Term.var x!).abstract (Function.update «Δ» x! (some X!)) (pf x! X!)⟧ˢ = some X!)
                                          (hφ : RenamingContext.CoversFV (Function.update «Δ» x! (some X!)) x!_spec)
                                          (_denφ : ⟦x!_spec.abstract (Function.update «Δ» x! (some X!)) hφ⟧ˢ = some Φ),
                                            Φ.snd.fst = SMTType.bool ∧
                                            (Φ.fst = zftrue ∧
                                                X.fst.pair X!.fst ∈ (castZF_of_path (castPath.fun hβ pα pβ)).1) ∧
                                              ∀ (Y : SMT.Dom),
                                                Y.snd.fst = α'.fun β' →
                                                  ∀
                                                    (hφY :
                                                      RenamingContext.CoversFV (Function.update «Δ» x! (some Y))
                                                        x!_spec),
                                                    ⟦x!_spec.abstract (Function.update «Δ» x! (some Y)) hφY⟧ˢ.isSome =
                                                      true⌝⦄ := by
  mintro pre ∀st
  mpure pre
  mspec loosenAux_prf_exact
    (Λ := Λ) (n := n) (used := used) (name := name) (x := x)
    (typ_x := typ_x) (𝕔 := castPath.fun hβ pα pβ) («Δ» := «Δ») hx
  rename_i out
  obtain ⟨x!, x!_spec⟩ := out
  mrename_i pre
  mintro ∀st'
  mpure pre
  obtain ⟨h1, h_rest⟩ := pre
  obtain ⟨h2, h_rest⟩ := h_rest
  obtain ⟨h3, h_rest⟩ := h_rest
  obtain ⟨h4, h_rest⟩ := h_rest
  obtain ⟨h5, h_rest⟩ := h_rest
  obtain ⟨h6, h_rest⟩ := h_rest
  obtain ⟨h7, h_rest⟩ := h_rest
  obtain ⟨h8, h_rest⟩ := h_rest
  obtain ⟨h9, h_rest⟩ := h_rest
  obtain ⟨h10, h_rest⟩ := h_rest
  obtain ⟨h11, h_rest⟩ := h_rest
  obtain ⟨h12, h⟩ := h_rest
  mpure_intro
  and_intros <;> try assumption
  intro X denx
  specialize h X denx
  obtain ⟨Φ, X!, denx!, hφ, denφ, hΦ_ty, hΦ_true_cast, hrest⟩ := h
  use Φ, X!, denx!, hφ, denφ, hΦ_ty, hΦ_true_cast
  intro Y hY_ty hφY
  specialize hrest Y hY_ty hφY
  exact hrest.1
