import SMT.Reasoning.Defs
import SMT.Reasoning.LooseningDefs
import SMT.Reasoning.Basic.StateSpecs
import SMT.Reasoning.Basic.LoosenAuxSpec
import SMT.Reasoning.Axioms

set_option mvcgen.warning false

open Std.Do B SMT ZFSet

set_option maxHeartbeats 1000000 in
theorem encodeTerm_spec.eq_case.{u} (fv_sub_typings : B.FvSubTypings) (x y : B.Term)
  (x_ih :
    ∀ (E : B.Env) {Λ : SMT.TypeContext} {α : BType},
      E.context ⊢ᴮ x : α →
        ∀ {«Δ» : B.RenamingContext.Context} (Δ_fv : ∀ v ∈ B.fv x, («Δ» v).isSome = true)
          {Δ₀ : SMT.RenamingContext.Context},
          RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» x →
            ∀ {used : List SMT.𝒱},
              (∀ v ∉ used, Δ₀ v = none) →
                ∀ {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ},
                  ⟦x.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩ →
                    (∀ v ∈ x.vars, v ∈ used) →
                      (∀ v ∈ x.vars, v ∈ Λ → v ∈ E.context) →
                        ∀ {n : ℕ},
                          ⦃fun x =>
                            match x with
                            | { env := E0, types := Λ' } =>
                              ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
                            encodeTerm x E ⦃PostCond.mayThrow fun x_1 x_2 =>
                              match x_1 with
                              | (t', σ) =>
                                match x_2 with
                                | { env := E', types := Γ' } =>
                                  ⌜used ⊆ E'.usedVars ∧
                                      Λ ⊆ Γ' ∧
                                        AList.keys Γ' ⊆ E'.usedVars ∧
                                          CoversUsedVars E'.usedVars x ∧
                                            σ = α.toSMTType ∧
                                              Γ' ⊢ˢ t' : σ ∧
                                                (∀ v ∈ used, v ∉ Λ → v ∉ B.fv x → v ∉ Γ') ∧
                                                  ∃ Δ',
                                                    ∃ (Δ'_covers : RenamingContext.CoversFV Δ' t'),
                                                      RenamingContext.Extends Δ' Δ₀ ∧
                                                        RenamingContext.ExtendsOnSourceFV Δ' «Δ» x ∧
                                                          (∀ v ∉ E'.usedVars, Δ' v = none) ∧
                                                            ∃ denT',
                                                              ⟦t'.abstract Δ' Δ'_covers⟧ˢ = some denT' ∧
                                                                ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT' ∧
                                                                  ∀ (Δ_alt : B.RenamingContext.Context)
                                                                    (Δ_fv_alt : ∀ v ∈ B.fv x, (Δ_alt v).isSome = true)
                                                                    (Δ₀_alt : SMT.RenamingContext.Context),
                                                                    RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt x →
                                                                      (∀ v ∉ E'.usedVars, Δ₀_alt v = none) →
                                                                      (∀ v (d : SMT.Dom), Δ₀_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) →
                                                                        ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦α⟧ᶻ),
                                                                          ⟦x.abstract Δ_alt Δ_fv_alt⟧ᴮ =
                                                                              some ⟨T_alt, ⟨α, hT_alt⟩⟩ →
                                                                            ∃ Δ'_alt,
                                                                              ∃ (hcov_alt :
                                                                                RenamingContext.CoversFV Δ'_alt t'),
                                                                                ∃ denT_alt,
                                                                                  RenamingContext.Extends Δ'_alt
                                                                                      Δ₀_alt ∧
                                                                                    (∀ v ∉ E'.usedVars, Δ'_alt v = none) ∧
                                                                                      (∀ v (d : SMT.Dom), Δ'_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) ∧
                                                                                      ⟦t'.abstract Δ'_alt hcov_alt⟧ˢ =
                                                                                          some denT_alt ∧
                                                                                        ⟨T_alt, ⟨α, hT_alt⟩⟩ ≘ᶻ
                                                                                          denT_alt ∧
                                                                                        (∀ v, Δ'_alt v ≠ none → v ∈ Γ')⌝⦄)
  (y_ih :
    ∀ (E : B.Env) {Λ : SMT.TypeContext} {α : BType},
      E.context ⊢ᴮ y : α →
        ∀ {«Δ» : B.RenamingContext.Context} (Δ_fv : ∀ v ∈ B.fv y, («Δ» v).isSome = true)
          {Δ₀ : SMT.RenamingContext.Context},
          RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» y →
            ∀ {used : List SMT.𝒱},
              (∀ v ∉ used, Δ₀ v = none) →
                ∀ {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ},
                  ⟦y.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩ →
                    (∀ v ∈ y.vars, v ∈ used) →
                      (∀ v ∈ y.vars, v ∈ Λ → v ∈ E.context) →
                        ∀ {n : ℕ},
                          ⦃fun x =>
                            match x with
                            | { env := E0, types := Λ' } =>
                              ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
                            encodeTerm y E ⦃PostCond.mayThrow fun x x_1 =>
                              match x with
                              | (t', σ) =>
                                match x_1 with
                                | { env := E', types := Γ' } =>
                                  ⌜used ⊆ E'.usedVars ∧
                                      Λ ⊆ Γ' ∧
                                        AList.keys Γ' ⊆ E'.usedVars ∧
                                          CoversUsedVars E'.usedVars y ∧
                                            σ = α.toSMTType ∧
                                              Γ' ⊢ˢ t' : σ ∧
                                                (∀ v ∈ used, v ∉ Λ → v ∉ B.fv y → v ∉ Γ') ∧
                                                  ∃ Δ',
                                                    ∃ (Δ'_covers : RenamingContext.CoversFV Δ' t'),
                                                      RenamingContext.Extends Δ' Δ₀ ∧
                                                        RenamingContext.ExtendsOnSourceFV Δ' «Δ» y ∧
                                                          (∀ v ∉ E'.usedVars, Δ' v = none) ∧
                                                            ∃ denT',
                                                              ⟦t'.abstract Δ' Δ'_covers⟧ˢ = some denT' ∧
                                                                ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT' ∧
                                                                  ∀ (Δ_alt : B.RenamingContext.Context)
                                                                    (Δ_fv_alt : ∀ v ∈ B.fv y, (Δ_alt v).isSome = true)
                                                                    (Δ₀_alt : SMT.RenamingContext.Context),
                                                                    RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt y →
                                                                      (∀ v ∉ E'.usedVars, Δ₀_alt v = none) →
                                                                      (∀ v (d : SMT.Dom), Δ₀_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) →
                                                                        ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦α⟧ᶻ),
                                                                          ⟦y.abstract Δ_alt Δ_fv_alt⟧ᴮ =
                                                                              some ⟨T_alt, ⟨α, hT_alt⟩⟩ →
                                                                            ∃ Δ'_alt,
                                                                              ∃ (hcov_alt :
                                                                                RenamingContext.CoversFV Δ'_alt t'),
                                                                                ∃ denT_alt,
                                                                                  RenamingContext.Extends Δ'_alt
                                                                                      Δ₀_alt ∧
                                                                                    (∀ v ∉ E'.usedVars, Δ'_alt v = none) ∧
                                                                                      (∀ v (d : SMT.Dom), Δ'_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) ∧
                                                                                      ⟦t'.abstract Δ'_alt hcov_alt⟧ˢ =
                                                                                          some denT_alt ∧
                                                                                        ⟨T_alt, ⟨α, hT_alt⟩⟩ ≘ᶻ
                                                                                          denT_alt ∧
                                                                                        (∀ v, Δ'_alt v ≠ none → v ∈ Γ')⌝⦄)
  (E : B.Env) {Λ : SMT.TypeContext} {α : BType} (typ_t : E.context ⊢ᴮ x =ᴮ y : α) {«Δ» : B.RenamingContext.Context}
  (Δ_fv : ∀ v ∈ B.fv (x =ᴮ y), («Δ» v).isSome = true) {Δ₀ : SMT.RenamingContext.Context}
  (Δ₀_ext : RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» (x =ᴮ y)) {used : List SMT.𝒱}
  (Δ₀_none_out : ∀ v ∉ used, Δ₀ v = none) {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ}
  (den_t : ⟦(x =ᴮ y).abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩) (vars_used : ∀ v ∈ (x =ᴮ y).vars, v ∈ used)
  (Λ_inv : ∀ v ∈ (x =ᴮ y).vars, v ∈ Λ → v ∈ E.context) {n : ℕ} :
  ⦃fun x =>
    match x with
    | { env := E0, types := Λ' } => ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
    encodeTerm (x =ᴮ y) E ⦃PostCond.mayThrow fun x_1 x_2 =>
      match x_1 with
      | (t', σ) =>
        match x_2 with
        | { env := E', types := Γ' } =>
          ⌜used ⊆ E'.usedVars ∧
              Λ ⊆ Γ' ∧
                AList.keys Γ' ⊆ E'.usedVars ∧
                  CoversUsedVars E'.usedVars (x =ᴮ y) ∧
                    σ = α.toSMTType ∧
                      Γ' ⊢ˢ t' : σ ∧
                        (∀ v ∈ used, v ∉ Λ → v ∉ B.fv (x =ᴮ y) → v ∉ Γ') ∧
                          ∃ Δ',
                            ∃ (Δ'_covers : RenamingContext.CoversFV Δ' t'),
                              RenamingContext.Extends Δ' Δ₀ ∧
                                RenamingContext.ExtendsOnSourceFV Δ' «Δ» (x =ᴮ y) ∧
                                  (∀ v ∉ E'.usedVars, Δ' v = none) ∧
                                    ∃ denT',
                                      ⟦t'.abstract Δ' Δ'_covers⟧ˢ = some denT' ∧
                                        ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT' ∧
                                          ∀ (Δ_alt : B.RenamingContext.Context)
                                            (Δ_fv_alt : ∀ v ∈ B.fv (x =ᴮ y), (Δ_alt v).isSome = true)
                                            (Δ₀_alt : SMT.RenamingContext.Context),
                                            RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt (x =ᴮ y) →
                                              (∀ v ∉ E'.usedVars, Δ₀_alt v = none) →
                                              (∀ v (d : SMT.Dom), Δ₀_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) →
                                                ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦α⟧ᶻ),
                                                  ⟦(x =ᴮ y).abstract Δ_alt Δ_fv_alt⟧ᴮ = some ⟨T_alt, ⟨α, hT_alt⟩⟩ →
                                                    ∃ Δ'_alt,
                                                      ∃ (hcov_alt : RenamingContext.CoversFV Δ'_alt t'),
                                                        ∃ denT_alt,
                                                          RenamingContext.Extends Δ'_alt Δ₀_alt ∧
                                                            (∀ v ∉ E'.usedVars, Δ'_alt v = none) ∧
                                                              (∀ v (d : SMT.Dom), Δ'_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) ∧
                                                              ⟦t'.abstract Δ'_alt hcov_alt⟧ˢ = some denT_alt ∧
                                                                ⟨T_alt, ⟨α, hT_alt⟩⟩ ≘ᶻ denT_alt ∧
                                                                                        (∀ v, Δ'_alt v ≠ none → v ∈ Γ')⌝⦄ := by
  mintro pre ∀σ
  mpure pre
  obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
  rw [encodeTerm]

  obtain ⟨rfl, α, typ_x, typ_y⟩ := Typing.eqE typ_t

  have Δ_fv_x : ∀ v ∈ B.fv x, («Δ» v).isSome = true := by
    intro v hv
    exact Δ_fv v (by rw [B.fv, List.mem_append]; exact Or.inl hv)
  have Δ_fv_y : ∀ v ∈ B.fv y, («Δ» v).isSome = true := by
    intro v hv
    exact Δ_fv v (by rw [B.fv, List.mem_append]; exact Or.inr hv)

  rw [B.Term.abstract, B.denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at den_t
  obtain ⟨⟨X, αx, hX⟩, den_x, eq⟩ := den_t
  have αx_eq := denote_welltyped_eq
    (t := x.abstract («Δ» := «Δ») Δ_fv_x)
    ?_ den_x
  on_goal 2 =>
    use E.context.abstract («Δ» := «Δ»), WFTC.of_abstract, α
    exact @Typing.of_abstract (B.Dom) («Δ» := «Δ») ?_ x E.context α Δ_fv_x typ_x
  dsimp at αx_eq
  subst αx

  dsimp at eq
  rw [Option.bind_eq_some_iff] at eq
  obtain ⟨⟨Y, βy, hY⟩, den_y, eq⟩ := eq
  have := denote_welltyped_eq
    (t := y.abstract («Δ» := «Δ») Δ_fv_y)
    ?_ den_y
  on_goal 2 =>
    use E.context.abstract («Δ» := «Δ»), WFTC.of_abstract, α
    exact @Typing.of_abstract (B.Dom) («Δ» := «Δ») ?_ y E.context α Δ_fv_y typ_y
  dsimp at this
  subst βy

  simp only [↓reduceDIte, Option.some.injEq, PSigma.mk.injEq] at eq
  replace eq := eq.1
  classical
  have eq_T : X =ᶻ Y = T := eq
  simp only [overloadBinOp, hX, hY, and_self, ↓reduceDIte, Function.onFun] at eq

  have Δ₀_ext_x : RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» x := by
    exact RenamingContext.extendsOnSourceFV_of_fv_subset
      (hsub := by
        intro v hv
        simpa [B.fv] using (Or.inl hv : v ∈ B.fv x ∨ v ∈ B.fv y)) Δ₀_ext
  have Δ₀_ext_y : RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» y := by
    exact RenamingContext.extendsOnSourceFV_of_fv_subset
      (hsub := by
        intro v hv
        simpa [B.fv] using (Or.inr hv : v ∈ B.fv x ∨ v ∈ B.fv y)) Δ₀_ext

  -- IH for x
  mspec x_ih (E := E) (Λ := σ.types) (α := α) typ_x
    («Δ» := «Δ»)
    (Δ_fv := Δ_fv_x)
    (Δ₀ := Δ₀) Δ₀_ext_x (used := used) Δ₀_none_out (T := X) (hT := hX)
    den_x
    (fun v hv => vars_used v (by simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢; rcases hv with h | h <;> [left; right] <;> exact .inl h))
    (fun v hv => Λ_inv v (by simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢; rcases hv with h | h <;> [left; right] <;> exact .inl h))
    (n := σ.env.freshvarsc)
  clear x_ih
  rename_i out_x
  obtain ⟨x_enc, σx⟩ := out_x
  mrename_i pre
  mintro ∀σ_x
  mpure pre
  dsimp at pre
  obtain ⟨St_used_sub_St', St_eq_St', St'_sub, x_cov_St', rfl, typ_x_enc, x_preserves,
    Δ', Δ'_covers_x, Δ'_extends_Δ₀, Δ'_ext_x, Δ'_none_out,
    ⟨Xenc, _, hXenc⟩, den_x_enc, ⟨rfl, retract_α_Xenc_eq_X⟩, x_ih_total⟩ := pre

  -- IH for y
  have Δ'_ext_y : RenamingContext.ExtendsOnSourceFV Δ' «Δ» y := by
    exact RenamingContext.extendsOnSourceFV_of_extends Δ'_extends_Δ₀ Δ₀_ext_y

  mspec y_ih (E := E) (Λ := σ_x.types) (α := α) typ_y
    («Δ» := «Δ»)
    (Δ_fv := Δ_fv_y)
    (Δ₀ := Δ') Δ'_ext_y (used := σ_x.env.usedVars) Δ'_none_out (T := Y) (hT := hY)
    den_y
    (fun v hv => St_used_sub_St' (vars_used v (by simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢; rcases hv with h | h <;> [left; right] <;> exact .inr h)))
    (fun v hv hΛ => by
      have hv_mem : v ∈ (x =ᴮ y).vars := by
        simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
        rcases hv with h | h <;> [left; right] <;> exact .inr h
      by_cases hv_St : v ∈ σ.types
      · exact Λ_inv v hv_mem hv_St
      · have hv_fv_x : v ∈ B.fv x := by
          by_contra h_neg
          exact absurd hΛ (x_preserves v (vars_used v hv_mem) hv_St h_neg)
        exact _root_.B.Typing.typed_by_fv typ_x hv_fv_x)
    (n := σ_x.env.freshvarsc)
  rw [BType.toSMTType]
  clear y_ih
  rename_i out_y
  obtain ⟨y_enc, σy⟩ := out_y
  mrename_i pre
  mintro ∀σ_y
  mpure pre
  dsimp at pre
  obtain ⟨St'_used_sub_St'', St'_eq_St'', St''_sub, y_cov_St'', rfl, typ_y_enc, y_preserves,
    Δ'', Δ''_covers_y, Δ''_extends_Δ', Δ''_ext_y, Δ''_none_out,
    ⟨Yenc, _, hYenc⟩, den_y_enc, ⟨rfl, retract_β_Yenc_eq_Y⟩, y_ih_total⟩ := pre

  have hcastEq : castEq (x_enc, α.toSMTType) (y_enc, α.toSMTType) =
      (pure (x_enc =ˢ y_enc, .bool) : Encoder _) := by
    unfold castEq
    simp [dif_pos (rfl : α.toSMTType = α.toSMTType)]
  rw [hcastEq]
  mspec Std.Do.Spec.pure
  -- Final state is σ_y (unchanged), final renaming context is ΔSMT = Δ''
  set ΔSMT := Δ''
  have ΔSMT_fv_x : SMT.RenamingContext.CoversFV ΔSMT x_enc := by
    simpa [ΔSMT] using
      (SMT.RenamingContext.coversFV_of_extends_of_coversFV
        (hext := Δ''_extends_Δ') (hcov := Δ'_covers_x))
  have ΔSMT_fv_y : SMT.RenamingContext.CoversFV ΔSMT y_enc := by
    simpa [ΔSMT] using Δ''_covers_y
  have den_x_enc_ΔSMT : ⟦x_enc.abstract ΔSMT ΔSMT_fv_x⟧ˢ = some ⟨Xenc, α.toSMTType, hXenc⟩ := by
    have hag_x : RenamingContext.AgreesOnFV ΔSMT Δ' x_enc := by
      simpa [ΔSMT] using
        (RenamingContext.agreesOnFV_of_extends_of_coversFV
          (hext := Δ''_extends_Δ') (hcov := Δ'_covers_x))
    have hden_x_congr := RenamingContext.denote_congr_of_agreesOnFV
      (t := x_enc) (h1 := ΔSMT_fv_x) (h2 := Δ'_covers_x) hag_x
    simpa [RenamingContext.denote] using hden_x_congr.trans den_x_enc
  have den_y_enc_ΔSMT : ⟦y_enc.abstract ΔSMT ΔSMT_fv_y⟧ˢ = some ⟨Yenc, α.toSMTType, hYenc⟩ := by
    simpa [SMT.RenamingContext.denote, ΔSMT] using den_y_enc
  have typ_x_enc_final : σ_y.types ⊢ˢ x_enc : α.toSMTType :=
    Typing.weakening St'_eq_St'' typ_x_enc
  mpure_intro
  and_intros
  · -- used ⊆ E'.usedVars
    intro v hv
    exact St'_used_sub_St'' (St_used_sub_St' (by simpa [St_used_eq] using hv))
  · -- Λ ⊆ Γ'
    exact fun _ h => St'_eq_St'' (St_eq_St' h)
  · -- keys_sub
    exact St''_sub
  · -- CoversUsedVars
    intro v hv
    simp only [B.fv, List.mem_append] at hv
    exact hv.elim
      (B.CoversUsedVars.mono (fun v hv => St'_used_sub_St'' hv) x_cov_St' v)
      (y_cov_St'' v)
  · -- .bool = BType.bool.toSMTType
    trivial
  · -- typing: σ_y.types ⊢ˢ (x_enc =ˢ y_enc) : .bool
    exact SMT.Typing.eq _ _ _ _ typ_x_enc_final typ_y_enc
  · -- preserves_types
    intro v hv h1 h2
    rw [B.fv, List.mem_append] at h2; push_neg at h2
    exact y_preserves v (St_used_sub_St' (by simpa [St_used_eq] using hv))
      (x_preserves v (by simpa [St_used_eq] using hv) h1 h2.1) h2.2
  · -- ∃ Δ', ...
    refine ⟨ΔSMT, ?_, ?_⟩
    · -- CoversFV ΔSMT (x_enc =ˢ y_enc)
      intro v hv
      rw [SMT.fv, List.mem_append] at hv
      rcases hv with hv | hv
      · exact ΔSMT_fv_x v hv
      · exact ΔSMT_fv_y v hv
    · and_intros
      · -- Extends ΔSMT Δ₀
        exact RenamingContext.extends_trans (by simpa [ΔSMT] using Δ''_extends_Δ') Δ'_extends_Δ₀
      · -- ExtendsOnSourceFV
        exact RenamingContext.extendsOnSourceFV_of_extends
          (RenamingContext.extends_trans (by simpa [ΔSMT] using Δ''_extends_Δ') Δ'_extends_Δ₀)
          Δ₀_ext
      · -- none_out
        exact fun v hv => by simpa [ΔSMT] using Δ''_none_out v hv
      · -- denotation + RDom + ih_total
        classical
        have eq_mem := overloadBinOp_mem (A := ⟦α.toSMTType⟧ᶻ) hXenc hYenc
          (op := @Eq ZFSet) («↓» := Subtype.val)
          («↑» := fun p => if p then ZFBool.true else ZFBool.false)
          (d := (⊥ : Prop))
        use ⟨overloadBinOp (A := ⟦α.toSMTType⟧ᶻ) Subtype.val
          (fun p => if p then ZFBool.true else ZFBool.false) (⊥ : Prop) (@Eq ZFSet)
          Xenc Yenc, SMTType.bool, eq_mem⟩
        and_intros
        · -- denotation
          rw [SMT.Term.abstract, SMT.denote, Option.pure_def,
              Option.bind_eq_bind, Option.bind_eq_some_iff]
          refine ⟨⟨Xenc, α.toSMTType, hXenc⟩, ?_, ?_⟩
          · simpa [SMT.RenamingContext.denote] using den_x_enc_ΔSMT
          · dsimp
            rw [Option.bind_eq_some_iff]
            refine ⟨⟨Yenc, α.toSMTType, hYenc⟩, ?_, ?_⟩
            · simpa [SMT.RenamingContext.denote] using den_y_enc_ΔSMT
            · rw [dif_pos rfl]
        · -- RDom: type equality
          rfl
        · -- RDom: retract equality
          rw [retract, id_eq, ←eq_T]
          simp only [overloadBinOp, «Prop».bot_eq_false, dite_else_false, Function.onFun]
          congr 1
          simp only [exists_prop, hX, hY, true_and, hXenc, hYenc, true_and]
          split_ifs with h1 h2 h2
          · rfl
          · exact absurd (by rw [←retract_α_Xenc_eq_X, ←retract_β_Yenc_eq_Y, h1]) h2
          · subst h2
            have hinj : Yenc = Xenc := by
              rw [← canonical_of_retract α hYenc, ← canonical_of_retract α hXenc]
              have := (BType.canonicalIsoSMTType α).property.1
              conv =>
                enter [1]
                rw [fapply_eq_Image_singleton this (retract_mem_of_canonical α hYenc)]
                conv =>
                  enter [1,2,1]
                  rw [retract_β_Yenc_eq_Y, ←retract_α_Xenc_eq_X]
                rw [←fapply_eq_Image_singleton this (retract_mem_of_canonical α hXenc)]
            nomatch h1 hinj.symm
          · rfl
        · -- ih_total: alt universality
          intro Δ_alt Δ_fv_alt Δ₀_alt Δ₀_alt_ext Δ₀_alt_none_out Δ₀_alt_wt T_alt hT_alt den_t_alt
          -- Decompose B-denotation of (x =ᴮ y) under alt valuation
          rw [B.Term.abstract, B.denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at den_t_alt
          obtain ⟨⟨X_alt, α_alt', hX_alt⟩, den_x_alt, eq_alt⟩ := den_t_alt
          have α_alt_eq := @denote_welltyped_eq
            (x.abstract Δ_alt (fun v hv => Δ_fv_alt v (by rw [B.fv, List.mem_append]; exact Or.inl hv)))
            X_alt α_alt' hX_alt ?_ den_x_alt
          on_goal 2 =>
            use E.context.abstract («Δ» := Δ_alt), WFTC.of_abstract, α
            exact @Typing.of_abstract (B.Dom) («Δ» := Δ_alt) ?_ x E.context α
              (fun v hv => Δ_fv_alt v (by rw [B.fv, List.mem_append]; exact Or.inl hv)) typ_x
          dsimp at α_alt_eq; subst α_alt_eq
          dsimp at eq_alt
          rw [Option.bind_eq_some_iff] at eq_alt
          obtain ⟨⟨Y_alt, _, hY_alt⟩, den_y_alt, eq_alt⟩ := eq_alt
          have α_set_alt_eq := @denote_welltyped_eq
            (y.abstract Δ_alt (fun v hv => Δ_fv_alt v (by rw [B.fv, List.mem_append]; exact Or.inr hv)))
            Y_alt _ hY_alt ?_ den_y_alt
          on_goal 2 =>
            use E.context.abstract («Δ» := Δ_alt), WFTC.of_abstract, α
            exact @Typing.of_abstract (B.Dom) («Δ» := Δ_alt) ?_ y E.context α
              (fun v hv => Δ_fv_alt v (by rw [B.fv, List.mem_append]; exact Or.inr hv)) typ_y
          dsimp at α_set_alt_eq; subst α_set_alt_eq
          dsimp at eq_alt
          simp only [↓reduceDIte, Option.some.injEq, PSigma.mk.injEq] at eq_alt
          obtain ⟨T_alt_eq, _⟩ := eq_alt
          -- Build restricted base for x IH
          set Δ₀_alt_x : SMT.RenamingContext.Context :=
            fun v => if v ∈ σ_x.env.usedVars then Δ₀_alt v else none with Δ₀_alt_x_def
          have Δ₀_alt_x_ext : RenamingContext.ExtendsOnSourceFV Δ₀_alt_x Δ_alt x := by
            have hsrc := RenamingContext.extendsOnSourceFV_of_fv_subset
              (hsub := by intro v hv; simpa [B.fv] using (Or.inl hv : v ∈ B.fv x ∨ v ∈ B.fv y))
              Δ₀_alt_ext
            intro v d hv
            simp only [Δ₀_alt_x_def]
            have hv_fv_x : v ∈ B.fv x := by
              by_contra hv_not
              simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_not] at hv
            have hv_used : v ∈ σ_x.env.usedVars :=
              St_used_sub_St' (vars_used v (by
                simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append]
                left; left; exact hv_fv_x))
            rw [if_pos hv_used]
            exact hsrc hv
          have Δ₀_alt_x_none : ∀ v ∉ σ_x.env.usedVars, Δ₀_alt_x v = none := by
            intro v hv; simp only [Δ₀_alt_x_def]; rw [if_neg hv]
          have Δ₀_alt_x_wt : ∀ v (d : SMT.Dom), Δ₀_alt_x v = some d → ∀ τ, σ_x.types.lookup v = some τ → d.snd.fst = τ := by
            intro v d hv τ hτ
            simp only [Δ₀_alt_x_def] at hv
            split_ifs at hv with h
            exact Δ₀_alt_wt v d hv τ (AList.mem_lookup_iff.mpr (St'_eq_St'' (AList.mem_lookup_iff.mp hτ)))
          -- Call x_ih_total
          obtain ⟨Δ'_alt_x, hcov_alt_x, denT_x_alt, hext_alt_x, Δ'_alt_x_none_out,
            Δ'_alt_x_wt_out, den_x_alt_enc, hRDom_x_alt, _⟩ :=
            x_ih_total Δ_alt
              (fun v hv => Δ_fv_alt v (by rw [B.fv, List.mem_append]; exact Or.inl hv))
              Δ₀_alt_x Δ₀_alt_x_ext Δ₀_alt_x_none Δ₀_alt_x_wt X_alt hX_alt den_x_alt
          -- Build hybrid base for y IH
          set Δ₀_alt_y : SMT.RenamingContext.Context :=
            fun v => match Δ₀_alt v with
              | some d => some d
              | none => if v ∈ σ_x.types then Δ'_alt_x v else none
            with Δ₀_alt_y_def
          have Δ₀_alt_y_ext : RenamingContext.ExtendsOnSourceFV Δ₀_alt_y Δ_alt y := by
            have hsrc := RenamingContext.extendsOnSourceFV_of_fv_subset
              (hsub := by intro v hv; simpa [B.fv] using (Or.inr hv : v ∈ B.fv x ∨ v ∈ B.fv y))
              Δ₀_alt_ext
            intro v d hv
            simp only [Δ₀_alt_y_def]
            have hΔ₀_val := hsrc hv
            simp [hΔ₀_val]
          have Δ₀_alt_y_none : ∀ v ∉ σ_y.env.usedVars, Δ₀_alt_y v = none := by
            intro v hv
            simp only [Δ₀_alt_y_def]
            have h1 : Δ₀_alt v = none := Δ₀_alt_none_out v hv
            simp only [h1]
            have hv_types : v ∉ σ_x.types :=
              fun h => hv (St'_used_sub_St'' (St'_sub (AList.mem_keys.mp h)))
            simp [if_neg hv_types]
          have Δ₀_alt_y_wt : ∀ v (d : SMT.Dom), Δ₀_alt_y v = some d → ∀ τ, σ_y.types.lookup v = some τ → d.snd.fst = τ := by
            intro v d hv τ hτ
            simp only [Δ₀_alt_y_def] at hv
            cases hΔ : Δ₀_alt v with
            | some d' =>
              simp [hΔ] at hv
              subst hv
              exact Δ₀_alt_wt v d' hΔ τ hτ
            | none =>
              simp [hΔ] at hv
              obtain ⟨h_mem, hv⟩ := hv
              apply Δ'_alt_x_wt_out v d hv
              obtain ⟨τ', hτ'⟩ := Option.isSome_iff_exists.mp (AList.lookup_isSome.mpr h_mem)
              have h_lkp_y := AList.lookup_of_subset St'_eq_St'' hτ'
              rw [hτ] at h_lkp_y; cases h_lkp_y; exact hτ'
          -- Call y_ih_total
          obtain ⟨Δ'_alt_y, hcov_alt_y, denT_y_alt, hext_alt_y, Δ'_alt_y_none_out,
            Δ'_alt_y_wt_out, den_y_alt_enc, hRDom_y_alt, Δ'_alt_y_dom_out⟩ :=
            y_ih_total Δ_alt
              (fun v hv => Δ_fv_alt v (by rw [B.fv, List.mem_append]; exact Or.inr hv))
              Δ₀_alt_y Δ₀_alt_y_ext Δ₀_alt_y_none Δ₀_alt_y_wt Y_alt hY_alt den_y_alt
          -- Define final Δ'_alt
          set Δ'_alt : SMT.RenamingContext.Context :=
            fun v => match Δ₀_alt v with | some d => some d | none => Δ'_alt_y v
            with Δ'_alt_def
          -- Coverage for Δ'_alt on fv(x_enc =ˢ y_enc)
          have hcov_eq_alt : RenamingContext.CoversFV Δ'_alt (x_enc =ˢ y_enc) := by
            intro v hv
            simp only [Δ'_alt_def]
            cases h : Δ₀_alt v with
            | some d => simp
            | none =>
              rw [SMT.fv, List.mem_append] at hv
              rcases hv with hv | hv
              · have hx_some : (Δ'_alt_x v).isSome = true := hcov_alt_x v hv
                have hv_types : v ∈ σ_x.types := SMT.Typing.mem_context_of_mem_fv typ_x_enc hv
                have hΔ₀_alt_y_v : Δ₀_alt_y v = Δ'_alt_x v := by
                  simp [Δ₀_alt_y_def, h, if_pos hv_types]
                obtain ⟨dx, hdx⟩ := Option.isSome_iff_exists.mp hx_some
                have : Δ₀_alt_y v = some dx := by rw [hΔ₀_alt_y_v, hdx]
                have := hext_alt_y this
                rw [this]; simp
              · exact hcov_alt_y v hv
          -- Δ'_alt agrees with Δ'_alt_x on fv(x_enc)
          have hagree_x : RenamingContext.AgreesOnFV Δ'_alt Δ'_alt_x x_enc := by
            intro v hv
            simp only [Δ'_alt_def]
            cases h : Δ₀_alt v with
            | some d =>
              have hv_σx : v ∈ σ_x.env.usedVars := by
                by_contra hv_not
                exact absurd (Δ'_covers_x v hv) (by simp [Δ'_none_out v hv_not])
              have : Δ₀_alt_x v = some d := by simp [Δ₀_alt_x_def, if_pos hv_σx, h]
              symm; exact hext_alt_x this
            | none =>
              have hv_types : v ∈ σ_x.types := SMT.Typing.mem_context_of_mem_fv typ_x_enc hv
              have hΔ₀_alt_y_v : Δ₀_alt_y v = Δ'_alt_x v := by
                simp [Δ₀_alt_y_def, h, if_pos hv_types]
              have hx_some : (Δ'_alt_x v).isSome = true := hcov_alt_x v hv
              obtain ⟨dx, hdx⟩ := Option.isSome_iff_exists.mp hx_some
              have h₁ : Δ₀_alt_y v = some dx := by rw [hΔ₀_alt_y_v, hdx]
              rw [hext_alt_y h₁, hdx]
          -- Δ'_alt agrees with Δ'_alt_y on fv(y_enc)
          have hagree_y : RenamingContext.AgreesOnFV Δ'_alt Δ'_alt_y y_enc := by
            intro v hv
            simp only [Δ'_alt_def]
            cases h : Δ₀_alt v with
            | some d =>
              have : Δ₀_alt_y v = some d := by simp [Δ₀_alt_y_def, h]
              symm; exact hext_alt_y this
            | none => rfl
          -- x_enc denotes under Δ'_alt
          have hcov_x_in_alt : RenamingContext.CoversFV Δ'_alt x_enc := by
            intro v hv
            exact hcov_eq_alt v (by rw [SMT.fv, List.mem_append]; exact Or.inl hv)
          have den_x_alt_final :
              ⟦x_enc.abstract Δ'_alt hcov_x_in_alt⟧ˢ = some denT_x_alt := by
            have := RenamingContext.denote_congr_of_agreesOnFV
              (t := x_enc) (h1 := hcov_x_in_alt) (h2 := hcov_alt_x) hagree_x
            simpa [RenamingContext.denote] using this.trans den_x_alt_enc
          -- y_enc denotes under Δ'_alt
          have hcov_y_in_alt : RenamingContext.CoversFV Δ'_alt y_enc := by
            intro v hv
            exact hcov_eq_alt v (by rw [SMT.fv, List.mem_append]; exact Or.inr hv)
          have den_y_alt_final :
              ⟦y_enc.abstract Δ'_alt hcov_y_in_alt⟧ˢ = some denT_y_alt := by
            have := RenamingContext.denote_congr_of_agreesOnFV
              (t := y_enc) (h1 := hcov_y_in_alt) (h2 := hcov_alt_y) hagree_y
            simpa [RenamingContext.denote] using this.trans den_y_alt_enc
          -- Extract types from alt denotations
          obtain ⟨Xenc_alt, σ_x_alt, hXenc_alt⟩ := denT_x_alt
          obtain ⟨Yenc_alt, σ_y_alt, hYenc_alt⟩ := denT_y_alt
          obtain ⟨rfl, retract_x_alt⟩ := hRDom_x_alt
          obtain ⟨rfl, retract_y_alt⟩ := hRDom_y_alt
          -- Build the equality denotation
          have eq_mem_alt := overloadBinOp_mem (A := ⟦α.toSMTType⟧ᶻ) hXenc_alt hYenc_alt
            (op := @Eq ZFSet) («↓» := Subtype.val)
            («↑» := fun p => if p then ZFBool.true else ZFBool.false)
            (d := (⊥ : Prop))
          refine ⟨Δ'_alt, hcov_eq_alt,
            ⟨overloadBinOp (A := ⟦α.toSMTType⟧ᶻ) Subtype.val
              (fun p => if p then ZFBool.true else ZFBool.false) (⊥ : Prop) (@Eq ZFSet)
              Xenc_alt Yenc_alt, SMTType.bool, eq_mem_alt⟩,
            ?_, ?_, ?_, ?_, ?_, ?_⟩
          -- Extends Δ'_alt Δ₀_alt
          · intro v d hv; simp only [Δ'_alt_def, hv]
          -- Vanishing: ∀ v ∉ E'.usedVars, Δ'_alt v = none
          · intro v hv
            simp only [Δ'_alt_def]
            have h1 := Δ₀_alt_none_out v hv
            simp only [h1]
            exact Δ'_alt_y_none_out v hv
          -- Well-typedness: output wt
          · intro v d hv τ hτ
            simp only [Δ'_alt_def] at hv
            cases hΔ : Δ₀_alt v with
            | some d' => simp [hΔ] at hv; subst hv; exact Δ₀_alt_wt v d' hΔ τ hτ
            | none => simp [hΔ] at hv; exact Δ'_alt_y_wt_out v d hv τ hτ
          -- Denotation of (x_enc =ˢ y_enc) under Δ'_alt
          · rw [SMT.Term.abstract, SMT.denote, Option.pure_def,
                Option.bind_eq_bind, Option.bind_eq_some_iff]
            refine ⟨⟨Xenc_alt, α.toSMTType, hXenc_alt⟩, ?_, ?_⟩
            · simpa [SMT.RenamingContext.denote] using den_x_alt_final
            · dsimp
              rw [Option.bind_eq_some_iff]
              refine ⟨⟨Yenc_alt, α.toSMTType, hYenc_alt⟩, ?_, ?_⟩
              · simpa [SMT.RenamingContext.denote] using den_y_alt_final
              · rw [dif_pos rfl]
          -- RDom for alt
          · constructor
            · rfl
            · rw [retract, id_eq, ←T_alt_eq]
              simp only [overloadBinOp, «Prop».bot_eq_false, dite_else_false, Function.onFun]
              congr 1
              simp only [exists_prop, hX_alt, hY_alt, true_and, hXenc_alt, hYenc_alt, true_and]
              split_ifs with h_enc_eq h_alt_eq h_alt_eq
              · rfl
              · subst h_enc_eq
                rw [retract_x_alt] at retract_y_alt
                nomatch h_alt_eq retract_y_alt
              · subst h_alt_eq
                rw [←retract_x_alt] at retract_y_alt
                have hinj : Yenc_alt = Xenc_alt := by
                  rw [← canonical_of_retract α hYenc_alt, ← canonical_of_retract α hXenc_alt]
                  have := (BType.canonicalIsoSMTType α).property.1
                  conv =>
                    enter [1]
                    rw [fapply_eq_Image_singleton this (retract_mem_of_canonical α hYenc_alt)]
                    conv =>
                      enter [1,2,1]
                      rw [retract_y_alt]
                    rw [←fapply_eq_Image_singleton this (retract_mem_of_canonical α hXenc_alt)]
                nomatch h_enc_eq hinj.symm
              · rfl
          -- dom_out
          · intro v hv
            simp only [Δ'_alt_def] at hv
            cases hΔ : Δ₀_alt v with
            | some d =>
              exact fv_sub_typings (B.Typing.eq typ_x typ_y)
                (SMT.Typing.eq _ _ _ _ typ_x_enc_final typ_y_enc) v
                (SMT.RenamingContext.ExtendsOnSourceFV.dom_sub_B_fv Δ₀_alt_ext v
                  (by rw [hΔ]; simp))
            | none => simp [hΔ] at hv; exact Δ'_alt_y_dom_out v hv
