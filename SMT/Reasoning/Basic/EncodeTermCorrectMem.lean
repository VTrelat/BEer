import SMT.Reasoning.Defs
import SMT.Reasoning.LooseningDefs
import SMT.Reasoning.Basic.StateSpecs
import SMT.Reasoning.Basic.LoosenAuxSpec
import SMT.Reasoning.Axioms

set_option mvcgen.warning false

open Std.Do B SMT ZFSet Classical Classical

set_option maxHeartbeats 1000000 in
theorem encodeTerm_spec.mem_case.{u} (fv_sub_typings : B.FvSubTypings) (x S : B.Term)
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
  (S_ih :
    ∀ (E : B.Env) {Λ : SMT.TypeContext} {α : BType},
      E.context ⊢ᴮ S : α →
        ∀ {«Δ» : B.RenamingContext.Context} (Δ_fv : ∀ v ∈ B.fv S, («Δ» v).isSome = true)
          {Δ₀ : SMT.RenamingContext.Context},
          RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» S →
            ∀ {used : List SMT.𝒱},
              (∀ v ∉ used, Δ₀ v = none) →
                ∀ {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ},
                  ⟦S.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩ →
                    (∀ v ∈ S.vars, v ∈ used) →
                      (∀ v ∈ S.vars, v ∈ Λ → v ∈ E.context) →
                        ∀ {n : ℕ},
                          ⦃fun x =>
                            match x with
                            | { env := E0, types := Λ' } =>
                              ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
                            encodeTerm S E ⦃PostCond.mayThrow fun x x_1 =>
                              match x with
                              | (t', σ) =>
                                match x_1 with
                                | { env := E', types := Γ' } =>
                                  ⌜used ⊆ E'.usedVars ∧
                                      Λ ⊆ Γ' ∧
                                        AList.keys Γ' ⊆ E'.usedVars ∧
                                          CoversUsedVars E'.usedVars S ∧
                                            σ = α.toSMTType ∧
                                              Γ' ⊢ˢ t' : σ ∧
                                                (∀ v ∈ used, v ∉ Λ → v ∉ B.fv S → v ∉ Γ') ∧
                                                  ∃ Δ',
                                                    ∃ (Δ'_covers : RenamingContext.CoversFV Δ' t'),
                                                      RenamingContext.Extends Δ' Δ₀ ∧
                                                        RenamingContext.ExtendsOnSourceFV Δ' «Δ» S ∧
                                                          (∀ v ∉ E'.usedVars, Δ' v = none) ∧
                                                            ∃ denT',
                                                              ⟦t'.abstract Δ' Δ'_covers⟧ˢ = some denT' ∧
                                                                ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT' ∧
                                                                  ∀ (Δ_alt : B.RenamingContext.Context)
                                                                    (Δ_fv_alt : ∀ v ∈ B.fv S, (Δ_alt v).isSome = true)
                                                                    (Δ₀_alt : SMT.RenamingContext.Context),
                                                                    RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt S →
                                                                      (∀ v ∉ E'.usedVars, Δ₀_alt v = none) →
                                                                      (∀ v (d : SMT.Dom), Δ₀_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) →
                                                                        ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦α⟧ᶻ),
                                                                          ⟦S.abstract Δ_alt Δ_fv_alt⟧ᴮ =
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
  (E : B.Env) {Λ : SMT.TypeContext} {α : BType} (typ_t : E.context ⊢ᴮ x ∈ᴮ S : α) {«Δ» : B.RenamingContext.Context}
  (Δ_fv : ∀ v ∈ B.fv (x ∈ᴮ S), («Δ» v).isSome = true) {Δ₀ : SMT.RenamingContext.Context}
  (Δ₀_ext : RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» (x ∈ᴮ S)) {used : List SMT.𝒱}
  (Δ₀_none_out : ∀ v ∉ used, Δ₀ v = none) {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ}
  (den_t : ⟦(x ∈ᴮ S).abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩) (vars_used : ∀ v ∈ (x ∈ᴮ S).vars, v ∈ used)
  (Λ_inv : ∀ v ∈ (x ∈ᴮ S).vars, v ∈ Λ → v ∈ E.context) {n : ℕ} :
  ⦃fun x =>
    match x with
    | { env := E0, types := Λ' } => ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
    encodeTerm (x ∈ᴮ S) E ⦃PostCond.mayThrow fun x_1 x_2 =>
      match x_1 with
      | (t', σ) =>
        match x_2 with
        | { env := E', types := Γ' } =>
          ⌜used ⊆ E'.usedVars ∧
              Λ ⊆ Γ' ∧
                AList.keys Γ' ⊆ E'.usedVars ∧
                  CoversUsedVars E'.usedVars (x ∈ᴮ S) ∧
                    σ = α.toSMTType ∧
                      Γ' ⊢ˢ t' : σ ∧
                        (∀ v ∈ used, v ∉ Λ → v ∉ B.fv (x ∈ᴮ S) → v ∉ Γ') ∧
                          ∃ Δ',
                            ∃ (Δ'_covers : RenamingContext.CoversFV Δ' t'),
                              RenamingContext.Extends Δ' Δ₀ ∧
                                RenamingContext.ExtendsOnSourceFV Δ' «Δ» (x ∈ᴮ S) ∧
                                  (∀ v ∉ E'.usedVars, Δ' v = none) ∧
                                    ∃ denT',
                                      ⟦t'.abstract Δ' Δ'_covers⟧ˢ = some denT' ∧
                                        ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT' ∧
                                          ∀ (Δ_alt : B.RenamingContext.Context)
                                            (Δ_fv_alt : ∀ v ∈ B.fv (x ∈ᴮ S), (Δ_alt v).isSome = true)
                                            (Δ₀_alt : SMT.RenamingContext.Context),
                                            RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt (x ∈ᴮ S) →
                                              (∀ v ∉ E'.usedVars, Δ₀_alt v = none) →
                                              (∀ v (d : SMT.Dom), Δ₀_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) →
                                                ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦α⟧ᶻ),
                                                  ⟦(x ∈ᴮ S).abstract Δ_alt Δ_fv_alt⟧ᴮ = some ⟨T_alt, ⟨α, hT_alt⟩⟩ →
                                                    ∃ Δ'_alt,
                                                      ∃ (hcov_alt : RenamingContext.CoversFV Δ'_alt t'),
                                                        ∃ denT_alt,
                                                          RenamingContext.Extends Δ'_alt Δ₀_alt ∧
                                                            (∀ v ∉ E'.usedVars, Δ'_alt v = none) ∧
                                                              (∀ v (d : SMT.Dom), Δ'_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) ∧
                                                              ⟦t'.abstract Δ'_alt hcov_alt⟧ˢ = some denT_alt ∧
                                                                ⟨T_alt, ⟨α, hT_alt⟩⟩ ≘ᶻ denT_alt ∧
                                                                                        (∀ v, Δ'_alt v ≠ none → v ∈ Γ')⌝⦄ := by
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre

  apply Typing.memE at typ_t
  obtain ⟨rfl, α, typ_x, typ_S⟩ := typ_t

  rw [B.Term.abstract, B.denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at den_t
  obtain ⟨⟨X, α', hX⟩, den_x, eq⟩ := den_t
  have α_eq := @denote_welltyped_eq
    (x.abstract «Δ» (fun v hv ↦ Δ_fv v (by rw [B.fv, List.mem_append]; exact Or.inl hv))) X α' hX ?_ den_x
  on_goal 2 =>
    use E.context.abstract («Δ» := «Δ»), WFTC.of_abstract, α
    exact @Typing.of_abstract (B.Dom) («Δ» := «Δ») ?_ x E.context α (fun v hv ↦ Δ_fv v (by rw [B.fv, List.mem_append]; exact Or.inl hv)) typ_x
  dsimp at α_eq
  subst α'

  dsimp at eq
  rw [Option.bind_eq_some_iff] at eq
  obtain ⟨⟨S', _, hS'⟩, den_S, eq⟩ := eq
  have α_set_eq := @denote_welltyped_eq
    (S.abstract «Δ» (fun v hv ↦ Δ_fv v (by rw [B.fv, List.mem_append]; exact Or.inr hv))) S' _ hS' ?_ den_S
  on_goal 2 =>
    use E.context.abstract («Δ» := «Δ»), WFTC.of_abstract, α.set
    exact @Typing.of_abstract (B.Dom) («Δ» := «Δ») ?_ S E.context α.set (fun v hv ↦ Δ_fv v (by rw [B.fv, List.mem_append]; exact Or.inr hv)) typ_S
  dsimp at α_set_eq
  subst α_set_eq

  dsimp at eq
  rw [ite_cond_eq_true _ _ (eq_true rfl), Option.some_inj] at eq
  injection eq with T_eq heq

  subst T_eq

  rw [encodeTerm]

  have Δ₀_ext_x : RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» x := by
    exact RenamingContext.extendsOnSourceFV_of_fv_subset
      (hsub := B.fv_subset_mem_left x S) Δ₀_ext
  have Δ₀_ext_S : RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» S := by
    exact RenamingContext.extendsOnSourceFV_of_fv_subset
      (hsub := B.fv_subset_mem_right x S) Δ₀_ext

  mspec x_ih (E := E) (Λ := St.types) (α := α) typ_x
    («Δ» := «Δ») (Δ_fv := fun v hv ↦ Δ_fv v (by rw [B.fv, List.mem_append]; exact Or.inl hv))
    (Δ₀ := Δ₀) Δ₀_ext_x (used := used) Δ₀_none_out (T := X) (hT := hX)
    den_x
    (fun v hv => vars_used v (by simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢; rcases hv with h | h <;> [left; right] <;> exact .inl h))
    (fun v hv => Λ_inv v (by simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢; rcases hv with h | h <;> [left; right] <;> exact .inl h))
    (n := St.env.freshvarsc)
  clear x_ih
  rename_i out_x
  obtain ⟨x_enc, α'⟩ := out_x
  mrename_i pre
  mintro ∀St'
  mpure pre
  dsimp at pre
  obtain ⟨St_used_sub_St', St_eq_St', St'_sub, x_cov_St', rfl, typ_x_enc, x_preserves,
    Δ', Δ'_covers_x, Δ'_extends_Δ₀, Δ'_ext_x, Δ'_none_out,
    ⟨Xenc, _, hXenc⟩, den_x_enc, ⟨rfl, retract_Xenc⟩, x_ih_total⟩ := pre

  have Δ'_ext_S : RenamingContext.ExtendsOnSourceFV Δ' «Δ» S := by
    exact RenamingContext.extendsOnSourceFV_of_extends Δ'_extends_Δ₀ Δ₀_ext_S

  mspec S_ih (E := E) (Λ := St'.types) (α := α.set) typ_S
    («Δ» := «Δ») (Δ_fv := fun v hv ↦ Δ_fv v (by rw [B.fv, List.mem_append]; exact Or.inr hv))
    (Δ₀ := Δ') Δ'_ext_S (used := St'.env.usedVars) Δ'_none_out (T := S') (hT := hS')
    den_S
    (fun v hv => St_used_sub_St' (vars_used v (by simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢; rcases hv with h | h <;> [left; right] <;> exact .inr h)))
    (fun v hv hΛ => by
      have hv_mem : v ∈ (x ∈ᴮ S).vars := by
        simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
        rcases hv with h | h <;> [left; right] <;> exact .inr h
      by_cases hv_St : v ∈ St.types
      · exact Λ_inv v hv_mem hv_St
      · have hv_fv_x : v ∈ B.fv x := by
          by_contra h_neg
          exact absurd hΛ (x_preserves v (vars_used v hv_mem) hv_St h_neg)
        exact _root_.B.Typing.typed_by_fv typ_x hv_fv_x)
    (n := St'.env.freshvarsc)
  clear S_ih
  rename_i out_S
  obtain ⟨S_enc, α_set⟩ := out_S
  mrename_i pre
  mintro ∀St''
  mpure pre
  dsimp at pre
  obtain ⟨St'_used_sub_St'', St'_eq_St'', St''_sub, S_cov_St'', rfl, typ_S_enc, S_preserves,
    Δ'', Δ''_covers_S, Δ''_extends_Δ', Δ''_ext_S, Δ''_none_out,
    ⟨Senc, α_set, hSenc⟩, den_S_enc, ⟨rfl, retract_Senc⟩, S_ih_total⟩ := pre
  set ΔSMT := Δ''
  have ΔSMT_fv_x : SMT.RenamingContext.CoversFV ΔSMT x_enc := by
    simpa [ΔSMT] using
      (SMT.RenamingContext.coversFV_of_extends_of_coversFV
        (hext := Δ''_extends_Δ') (hcov := Δ'_covers_x))
  have ΔSMT_fv_S : SMT.RenamingContext.CoversFV ΔSMT S_enc := by
    simpa [ΔSMT] using Δ''_covers_S
  have den_x_enc_ΔSMT : ⟦x_enc.abstract ΔSMT ΔSMT_fv_x⟧ˢ = some ⟨Xenc, α.toSMTType, hXenc⟩ := by
    have hag : SMT.RenamingContext.AgreesOnFV ΔSMT Δ' x_enc := by
      simpa [ΔSMT] using
        (SMT.RenamingContext.agreesOnFV_of_extends_of_coversFV
          (hext := Δ''_extends_Δ') (hcov := Δ'_covers_x))
    have hden_eq :=
      SMT.RenamingContext.denote_congr_of_agreesOnFV
        (h1 := ΔSMT_fv_x) (h2 := Δ'_covers_x) hag
    have hden : SMT.RenamingContext.denote ΔSMT x_enc ΔSMT_fv_x =
        some ⟨Xenc, α.toSMTType, hXenc⟩ := by
      rw [hden_eq]
      simpa [SMT.RenamingContext.denote] using den_x_enc
    simpa [SMT.RenamingContext.denote] using hden
  have den_S_enc_ΔSMT :
      ⟦S_enc.abstract ΔSMT ΔSMT_fv_S⟧ˢ = some ⟨Senc, ⟨α.set.toSMTType, hSenc⟩⟩ := by
    simpa [ΔSMT] using den_S_enc
  unfold castMembership
  conv =>
    enter [2,1,1]
    simp only [bind_pure_comp, BType.toSMTType]
    rw [dif_pos castable?.reflexive, dite_true]
  -- After dif_pos + dite_true, the program is pure (S_enc @ x_enc, .bool)
  mspec Std.Do.Spec.pure
  -- After dif_pos + dite_true, the pure path yields (S_enc @ x_enc, .bool) with no state change.
  -- Final state is St'', final renaming context is ΔSMT = Δ''.
  have typ_x_enc_final : St''.types ⊢ˢ x_enc : α.toSMTType :=
    Typing.weakening St'_eq_St'' typ_x_enc
  mpure_intro
  and_intros
  · -- used ⊆ St''.env.usedVars
    intro v hv
    exact St'_used_sub_St'' (St_used_sub_St' (by simpa [St_used_eq] using hv))
  · -- St.types ⊆ St''.types
    exact fun _ h => St'_eq_St'' (St_eq_St' h)
  · -- keys_sub
    exact St''_sub
  · -- CoversUsedVars
    refine B.CoversUsedVars.mem ?_ ?_
    · exact B.CoversUsedVars.mono (fun v hv => St'_used_sub_St'' hv) x_cov_St'
    · exact S_cov_St''
  · -- .bool = BType.bool.toSMTType
    rfl
  · -- typing: St''.types ⊢ˢ (@ˢS_enc) x_enc : .bool
    exact SMT.Typing.app _ _ _ _ _ typ_S_enc typ_x_enc_final
  · -- preserves_types
    intro v hv h1 h2
    rw [B.fv, List.mem_append] at h2; push_neg at h2
    exact S_preserves v (St_used_sub_St' (by simpa [St_used_eq] using hv))
      (fun h_in => h1 (by
        by_contra h_not
        exact absurd h_in (x_preserves v (by simpa [St_used_eq] using hv) h_not h2.1)))
      h2.2
  · -- ∃ Δ', ...
    refine ⟨ΔSMT, ?_, ?_⟩
    · -- CoversFV ΔSMT ((@ˢS_enc) x_enc)
      intro v hv
      rw [SMT.fv, List.mem_append] at hv
      rcases hv with hv | hv
      · exact ΔSMT_fv_S v hv
      · exact ΔSMT_fv_x v hv
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
        -- First establish Senc is a function from α.toSMTType to .bool
        rw [BType.toSMTType, SMTType.toZFSet, mem_funs] at hSenc
        have Senc_pfun : Senc.IsPFunc ⟦α.toSMTType⟧ᶻ ⟦SMTType.bool⟧ᶻ :=
          is_func_is_pfunc hSenc
        have Xenc_memDom : Xenc ∈ Senc.Dom (is_rel_of_is_func hSenc) := by
          rw [is_func_dom_eq hSenc]; exact hXenc
        -- The SMT denotation of (@ˢS_enc) x_enc
        have den_app : ⟦((@ˢS_enc) x_enc).abstract ΔSMT
            (fun v hv => by rw [SMT.fv, List.mem_append] at hv; rcases hv with h | h; exact ΔSMT_fv_S v h; exact ΔSMT_fv_x v h)⟧ˢ =
            some ⟨↑(fapply Senc Senc_pfun ⟨Xenc, Xenc_memDom⟩), SMTType.bool, Subtype.property _⟩ := by
          rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff]
          refine ⟨⟨Senc, α.set.toSMTType, mem_funs.mpr hSenc⟩, ?_, ?_⟩
          · simpa [SMT.RenamingContext.denote] using den_S_enc_ΔSMT
          · dsimp [BType.toSMTType]
            rw [Option.bind_eq_some_iff]
            refine ⟨⟨Xenc, α.toSMTType, hXenc⟩, ?_, ?_⟩
            · simpa [SMT.RenamingContext.denote] using den_x_enc_ΔSMT
            · simp only [dif_pos Senc_pfun, dif_pos Xenc_memDom, ite_true]
        use ⟨↑(fapply Senc Senc_pfun ⟨Xenc, Xenc_memDom⟩), SMTType.bool, Subtype.property _⟩
        and_intros
        · -- denotation
          exact den_app
        · -- RDom type eq
          rfl
        · -- RDom retract: retract .bool (fapply ...) = X ∈ᶻ S'
          dsimp [retract]
          unfold overloadUnaryOp
          by_cases mem_X_S' : X ∈ S'
          · -- Case X ∈ S'
            rw [dif_pos mem_X_S']
            dsimp
            rw [if_pos mem_X_S']
            -- X ∈ S' means retract α Xenc ∈ retract (set α) Senc
            have hX_in_S' := mem_X_S'
            rw [←retract_Senc, ←retract_Xenc] at hX_in_S'
            rw [retract, mem_sep] at hX_in_S'
            obtain ⟨_, hfx_eq_true⟩ := hX_in_S'
            simp only [dif_pos (by rwa [retract_Xenc] : retract α Xenc ∈ ⟦α⟧ᶻ), dif_pos hSenc] at hfx_eq_true
            rw [fapply_eq_Image_singleton hSenc (fapply_mem_range _ _)] at hfx_eq_true
            simp only [canonical_of_retract α hXenc] at hfx_eq_true
            rw [←fapply_eq_Image_singleton hSenc hXenc] at hfx_eq_true
            rw [hfx_eq_true]
          · -- Case X ∉ S'
            rw [dif_neg mem_X_S']
            -- X ∉ S' means ¬(retract α Xenc ∈ retract (set α) Senc)
            have hX_not_in_S' := mem_X_S'
            rw [←retract_Senc, ←retract_Xenc] at hX_not_in_S'
            rw [retract, mem_sep, not_and] at hX_not_in_S'
            have retract_Xenc_mem_α : retract α Xenc ∈ ⟦α⟧ᶻ := by rwa [retract_Xenc]
            specialize hX_not_in_S' retract_Xenc_mem_α
            simp only [dif_pos retract_Xenc_mem_α, dif_pos hSenc] at hX_not_in_S'
            rw [fapply_eq_Image_singleton hSenc (fapply_mem_range _ _)] at hX_not_in_S'
            simp only [canonical_of_retract α hXenc] at hX_not_in_S'
            rw [←fapply_eq_Image_singleton hSenc hXenc] at hX_not_in_S'
            conv at hX_not_in_S' =>
              enter [1, 2]
              change (⊤ : ZFBool)
            rw [←Subtype.ext_iff, ←ne_eq, ZFBool.not_top_iff_bot] at hX_not_in_S'
            rw [Subtype.ext_iff] at hX_not_in_S'
            rw [hX_not_in_S']
            dsimp
            rw [if_false]
        · -- ih_total: alt universality
          intro Δ_alt Δ_fv_alt Δ₀_alt Δ₀_alt_ext Δ₀_alt_none_out Δ₀_alt_wt T_alt hT_alt den_t_alt
          -- Decompose B-denotation of (x ∈ᴮ S) under alt valuation
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
          obtain ⟨⟨S_alt', _, hS_alt'⟩, den_S_alt, eq_alt⟩ := eq_alt
          have α_set_alt_eq := @denote_welltyped_eq
            (S.abstract Δ_alt (fun v hv => Δ_fv_alt v (by rw [B.fv, List.mem_append]; exact Or.inr hv)))
            S_alt' _ hS_alt' ?_ den_S_alt
          on_goal 2 =>
            use E.context.abstract («Δ» := Δ_alt), WFTC.of_abstract, α.set
            exact @Typing.of_abstract (B.Dom) («Δ» := Δ_alt) ?_ S E.context α.set
              (fun v hv => Δ_fv_alt v (by rw [B.fv, List.mem_append]; exact Or.inr hv)) typ_S
          dsimp at α_set_alt_eq; subst α_set_alt_eq
          dsimp at eq_alt
          rw [ite_cond_eq_true _ _ (eq_true rfl), Option.some_inj] at eq_alt
          injection eq_alt with T_alt_eq _
          subst T_alt_eq
          -- Build restricted base for x IH
          set Δ₀_alt_x : SMT.RenamingContext.Context :=
            fun v => if v ∈ St'.env.usedVars then Δ₀_alt v else none with Δ₀_alt_x_def
          have Δ₀_alt_x_ext : RenamingContext.ExtendsOnSourceFV Δ₀_alt_x Δ_alt x := by
            have hsrc := RenamingContext.extendsOnSourceFV_of_fv_subset
              (hsub := by intro v hv; simpa [B.fv] using (Or.inl hv : v ∈ B.fv x ∨ v ∈ B.fv S))
              Δ₀_alt_ext
            intro v d hv
            simp only [Δ₀_alt_x_def]
            have hv_fv_x : v ∈ B.fv x := by
              by_contra hv_not
              simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_not] at hv
            have hv_used : v ∈ St'.env.usedVars :=
              St_used_sub_St' (vars_used v (by
                simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append]
                left; left; exact hv_fv_x))
            rw [if_pos hv_used]
            exact hsrc hv
          have Δ₀_alt_x_none : ∀ v ∉ St'.env.usedVars, Δ₀_alt_x v = none := by
            intro v hv; simp only [Δ₀_alt_x_def]; rw [if_neg hv]
          have Δ₀_alt_x_wt : ∀ v (d : SMT.Dom), Δ₀_alt_x v = some d → ∀ τ, St'.types.lookup v = some τ → d.snd.fst = τ := by
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
          -- Build hybrid base for S IH
          set Δ₀_alt_S : SMT.RenamingContext.Context :=
            fun v => match Δ₀_alt v with
              | some d => some d
              | none => if v ∈ St'.types then Δ'_alt_x v else none
            with Δ₀_alt_S_def
          have Δ₀_alt_S_ext : RenamingContext.ExtendsOnSourceFV Δ₀_alt_S Δ_alt S := by
            have hsrc := RenamingContext.extendsOnSourceFV_of_fv_subset
              (hsub := by intro v hv; simpa [B.fv] using (Or.inr hv : v ∈ B.fv x ∨ v ∈ B.fv S))
              Δ₀_alt_ext
            intro v d hv
            simp only [Δ₀_alt_S_def]
            have hΔ₀_val := hsrc hv
            simp [hΔ₀_val]
          have Δ₀_alt_S_none : ∀ v ∉ St''.env.usedVars, Δ₀_alt_S v = none := by
            intro v hv
            simp only [Δ₀_alt_S_def]
            have hv_x : v ∉ St'.env.usedVars := fun h => hv (St'_used_sub_St'' h)
            have h1 : Δ₀_alt v = none := Δ₀_alt_none_out v hv
            simp only [h1]
            have hv_types : v ∉ St'.types :=
              fun h => hv_x (St'_sub (AList.mem_keys.mp h))
            simp [if_neg hv_types]
          have Δ₀_alt_S_wt : ∀ v (d : SMT.Dom), Δ₀_alt_S v = some d → ∀ τ, St''.types.lookup v = some τ → d.snd.fst = τ := by
            intro v d hv τ hτ
            simp only [Δ₀_alt_S_def] at hv
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
          -- Call S_ih_total
          obtain ⟨Δ'_alt_S, hcov_alt_S, denT_S_alt, hext_alt_S, Δ'_alt_S_none_out,
            Δ'_alt_S_wt_out, den_S_alt_enc, hRDom_S_alt, Δ'_alt_S_dom_out⟩ :=
            S_ih_total Δ_alt
              (fun v hv => Δ_fv_alt v (by rw [B.fv, List.mem_append]; exact Or.inr hv))
              Δ₀_alt_S Δ₀_alt_S_ext Δ₀_alt_S_none Δ₀_alt_S_wt S_alt' hS_alt' den_S_alt
          -- Define final Δ'_alt
          set Δ'_alt : SMT.RenamingContext.Context :=
            fun v => match Δ₀_alt v with | some d => some d | none => Δ'_alt_S v
            with Δ'_alt_def
          -- Coverage for Δ'_alt on fv((@ˢS_enc) x_enc)
          have hcov_app_alt : RenamingContext.CoversFV Δ'_alt ((@ˢS_enc) x_enc) := by
            intro v hv
            simp only [Δ'_alt_def]
            cases h : Δ₀_alt v with
            | some d => simp
            | none =>
              rw [SMT.fv, List.mem_append] at hv
              rcases hv with hv | hv
              · exact hcov_alt_S v hv
              · have hx_some : (Δ'_alt_x v).isSome = true := hcov_alt_x v hv
                have hv_types : v ∈ St'.types := SMT.Typing.mem_context_of_mem_fv typ_x_enc hv
                have hΔ₀_alt_S_v : Δ₀_alt_S v = Δ'_alt_x v := by
                  simp [Δ₀_alt_S_def, h, if_pos hv_types]
                obtain ⟨dx, hdx⟩ := Option.isSome_iff_exists.mp hx_some
                have : Δ₀_alt_S v = some dx := by rw [hΔ₀_alt_S_v, hdx]
                have := hext_alt_S this
                rw [this]; simp
          -- Δ'_alt agrees with Δ'_alt_x on fv(x_enc)
          have hagree_x : RenamingContext.AgreesOnFV Δ'_alt Δ'_alt_x x_enc := by
            intro v hv
            simp only [Δ'_alt_def]
            cases h : Δ₀_alt v with
            | some d =>
              have hv_σx : v ∈ St'.env.usedVars := by
                by_contra hv_not
                exact absurd (Δ'_covers_x v hv) (by simp [Δ'_none_out v hv_not])
              have : Δ₀_alt_x v = some d := by simp [Δ₀_alt_x_def, if_pos hv_σx, h]
              symm; exact hext_alt_x this
            | none =>
              have hv_types : v ∈ St'.types := SMT.Typing.mem_context_of_mem_fv typ_x_enc hv
              have hΔ₀_alt_S_v : Δ₀_alt_S v = Δ'_alt_x v := by
                simp [Δ₀_alt_S_def, h, if_pos hv_types]
              have hx_some : (Δ'_alt_x v).isSome = true := hcov_alt_x v hv
              obtain ⟨dx, hdx⟩ := Option.isSome_iff_exists.mp hx_some
              have h₁ : Δ₀_alt_S v = some dx := by rw [hΔ₀_alt_S_v, hdx]
              rw [hext_alt_S h₁, hdx]
          -- Δ'_alt agrees with Δ'_alt_S on fv(S_enc)
          have hagree_S : RenamingContext.AgreesOnFV Δ'_alt Δ'_alt_S S_enc := by
            intro v hv
            simp only [Δ'_alt_def]
            cases h : Δ₀_alt v with
            | some d =>
              have : Δ₀_alt_S v = some d := by simp [Δ₀_alt_S_def, h]
              symm; exact hext_alt_S this
            | none => rfl
          -- x_enc denotes under Δ'_alt
          have hcov_x_in_alt : RenamingContext.CoversFV Δ'_alt x_enc := by
            intro v hv
            exact hcov_app_alt v (by rw [SMT.fv, List.mem_append]; exact Or.inr hv)
          have den_x_alt_final :
              ⟦x_enc.abstract Δ'_alt hcov_x_in_alt⟧ˢ = some denT_x_alt := by
            have := RenamingContext.denote_congr_of_agreesOnFV
              (t := x_enc) (h1 := hcov_x_in_alt) (h2 := hcov_alt_x) hagree_x
            simpa [RenamingContext.denote] using this.trans den_x_alt_enc
          -- S_enc denotes under Δ'_alt
          have hcov_S_in_alt : RenamingContext.CoversFV Δ'_alt S_enc := by
            intro v hv
            exact hcov_app_alt v (by rw [SMT.fv, List.mem_append]; exact Or.inl hv)
          have den_S_alt_final :
              ⟦S_enc.abstract Δ'_alt hcov_S_in_alt⟧ˢ = some denT_S_alt := by
            have := RenamingContext.denote_congr_of_agreesOnFV
              (t := S_enc) (h1 := hcov_S_in_alt) (h2 := hcov_alt_S) hagree_S
            simpa [RenamingContext.denote] using this.trans den_S_alt_enc
          -- Extract types from alt denotations
          obtain ⟨Xenc_alt, σ_x_alt, hXenc_alt⟩ := denT_x_alt
          obtain ⟨Senc_alt, σ_S_alt, hSenc_alt⟩ := denT_S_alt
          obtain ⟨rfl, retract_x_alt⟩ := hRDom_x_alt
          obtain ⟨rfl, retract_S_alt⟩ := hRDom_S_alt
          -- Senc_alt is a function
          rw [BType.toSMTType, SMTType.toZFSet, mem_funs] at hSenc_alt
          have Senc_alt_pfun : Senc_alt.IsPFunc ⟦α.toSMTType⟧ᶻ ⟦SMTType.bool⟧ᶻ :=
            is_func_is_pfunc hSenc_alt
          have Xenc_alt_memDom : Xenc_alt ∈ Senc_alt.Dom (is_rel_of_is_func hSenc_alt) := by
            rw [is_func_dom_eq hSenc_alt]; exact hXenc_alt
          refine ⟨Δ'_alt, hcov_app_alt,
            ⟨↑(fapply Senc_alt Senc_alt_pfun ⟨Xenc_alt, Xenc_alt_memDom⟩), SMTType.bool, Subtype.property _⟩,
            ?_, ?_, ?_, ?_, ?_, ?_⟩
          -- Extends Δ'_alt Δ₀_alt
          · intro v d hv; simp only [Δ'_alt_def, hv]
          -- Vanishing: ∀ v ∉ E'.usedVars, Δ'_alt v = none
          · intro v hv
            simp only [Δ'_alt_def]
            have h1 := Δ₀_alt_none_out v hv
            simp only [h1]
            exact Δ'_alt_S_none_out v hv
          -- Well-typedness: output wt
          · intro v d hv τ hτ
            simp only [Δ'_alt_def] at hv
            cases hΔ : Δ₀_alt v with
            | some d' => simp [hΔ] at hv; subst hv; exact Δ₀_alt_wt v d' hΔ τ hτ
            | none => simp [hΔ] at hv; exact Δ'_alt_S_wt_out v d hv τ hτ
          -- Denotation of ((@ˢS_enc) x_enc) under Δ'_alt
          · rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff]
            refine ⟨⟨Senc_alt, α.set.toSMTType, mem_funs.mpr hSenc_alt⟩, ?_, ?_⟩
            · simpa [SMT.RenamingContext.denote] using den_S_alt_final
            · dsimp [BType.toSMTType]
              rw [Option.bind_eq_some_iff]
              refine ⟨⟨Xenc_alt, α.toSMTType, hXenc_alt⟩, ?_, ?_⟩
              · simpa [SMT.RenamingContext.denote] using den_x_alt_final
              · simp only [ite_true, dif_pos Senc_alt_pfun, dif_pos Xenc_alt_memDom]
          -- RDom for alt
          · constructor
            · rfl
            · dsimp [retract]
              unfold overloadUnaryOp
              by_cases mem_X_alt_S_alt : X_alt ∈ S_alt'
              · rw [dif_pos mem_X_alt_S_alt]; dsimp; rw [if_pos mem_X_alt_S_alt]
                have hX_in := mem_X_alt_S_alt
                rw [←retract_S_alt, ←retract_x_alt] at hX_in
                rw [retract, mem_sep] at hX_in
                obtain ⟨_, hfx_eq_true⟩ := hX_in
                simp only [dif_pos (by rwa [retract_x_alt] : retract α Xenc_alt ∈ ⟦α⟧ᶻ), dif_pos hSenc_alt] at hfx_eq_true
                rw [fapply_eq_Image_singleton hSenc_alt (fapply_mem_range _ _)] at hfx_eq_true
                simp only [canonical_of_retract α hXenc_alt] at hfx_eq_true
                rw [←fapply_eq_Image_singleton hSenc_alt hXenc_alt] at hfx_eq_true
                rw [hfx_eq_true]
              · rw [dif_neg mem_X_alt_S_alt]
                have hX_not_in := mem_X_alt_S_alt
                rw [←retract_S_alt, ←retract_x_alt] at hX_not_in
                rw [retract, mem_sep, not_and] at hX_not_in
                have retract_Xenc_alt_mem : retract α Xenc_alt ∈ ⟦α⟧ᶻ := by rwa [retract_x_alt]
                specialize hX_not_in retract_Xenc_alt_mem
                simp only [dif_pos retract_Xenc_alt_mem, dif_pos hSenc_alt] at hX_not_in
                rw [fapply_eq_Image_singleton hSenc_alt (fapply_mem_range _ _)] at hX_not_in
                simp only [canonical_of_retract α hXenc_alt] at hX_not_in
                rw [←fapply_eq_Image_singleton hSenc_alt hXenc_alt] at hX_not_in
                conv at hX_not_in =>
                  enter [1, 2]
                  change (⊤ : ZFBool)
                rw [←Subtype.ext_iff, ←ne_eq, ZFBool.not_top_iff_bot, Subtype.ext_iff] at hX_not_in
                rw [hX_not_in]
                dsimp
                rw [if_false]
          -- dom_out
          · intro v hv
            simp only [Δ'_alt_def] at hv
            cases hΔ : Δ₀_alt v with
            | some d =>
              exact fv_sub_typings (B.Typing.mem typ_x typ_S)
                (SMT.Typing.app _ _ _ _ _ typ_S_enc typ_x_enc_final) v
                (SMT.RenamingContext.ExtendsOnSourceFV.dom_sub_B_fv Δ₀_alt_ext v
                  (by rw [hΔ]; simp))
            | none => simp [hΔ] at hv; exact Δ'_alt_S_dom_out v hv
