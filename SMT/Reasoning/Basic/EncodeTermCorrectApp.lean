import SMT.Reasoning.Defs
import SMT.Reasoning.LooseningDefs
import SMT.Reasoning.Basic.StateSpecs
import SMT.Reasoning.Basic.LoosenAuxSpec
import SMT.Reasoning.Basic.DenotationTotality
import SMT.Reasoning.Axioms

open Std.Do B SMT ZFSet

set_option maxHeartbeats 4000000 in
theorem encodeTerm_spec.app_case.{u} (fv_sub_typings : B.FvSubTypings) (f x : B.Term)
  (f_ih :
    ∀ (E : _root_.B.Env) {Λ : SMT.TypeContext} {α : BType},
      E.context ⊢ᴮ f : α →
        ∀ {«Δ» : _root_.B.RenamingContext.Context} (Δ_fv : ∀ v ∈ _root_.B.fv f, («Δ» v).isSome = true)
          {Δ₀ : SMT.RenamingContext.Context},
          RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» f →
            ∀ {used : List SMT.𝒱},
              (∀ v ∉ used, Δ₀ v = none) →
                ∀ {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ},
                  ⟦f.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩ →
                    (∀ v ∈ f.vars, v ∈ used) →
                      (∀ v ∈ f.vars, v ∈ Λ → v ∈ E.context) →
                        ∀ {n : ℕ},
                          ⦃fun x =>
                            match x with
                            | { env := E0, types := Λ' } =>
                              ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
                            encodeTerm f E ⦃PostCond.mayThrow fun x x_1 =>
                              match x with
                              | (t', σ) =>
                                match x_1 with
                                | { env := E', types := Γ' } =>
                                  ⌜used ⊆ E'.usedVars ∧
                                      Λ ⊆ Γ' ∧
                                        AList.keys Γ' ⊆ E'.usedVars ∧
                                          CoversUsedVars E'.usedVars f ∧
                                            σ = α.toSMTType ∧
                                              Γ' ⊢ˢ t' : σ ∧
                                                (∀ v ∈ used, v ∉ Λ → v ∉ _root_.B.fv f → v ∉ Γ') ∧
                                                  ∃ Δ',
                                                    ∃ (Δ'_covers : RenamingContext.CoversFV Δ' t'),
                                                      RenamingContext.Extends Δ' Δ₀ ∧
                                                        RenamingContext.ExtendsOnSourceFV Δ' «Δ» f ∧
                                                          (∀ v ∉ E'.usedVars, Δ' v = none) ∧
                                                            ∃ denT',
                                                              ⟦t'.abstract Δ' Δ'_covers⟧ˢ = some denT' ∧
                                                                ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT' ∧
                                                                  ∀ (Δ_alt : _root_.B.RenamingContext.Context)
                                                                    (Δ_fv_alt :
                                                                      ∀ v ∈ _root_.B.fv f, (Δ_alt v).isSome = true)
                                                                    (Δ₀_alt : SMT.RenamingContext.Context),
                                                                    RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt f →
                                                                      (∀ v ∉ E'.usedVars, Δ₀_alt v = none) →
                                                                      (∀ v (d : SMT.Dom), Δ₀_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) →
                                                                        ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦α⟧ᶻ),
                                                                          ⟦f.abstract Δ_alt Δ_fv_alt⟧ᴮ =
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
  (x_ih :
    ∀ (E : _root_.B.Env) {Λ : SMT.TypeContext} {α : BType},
      E.context ⊢ᴮ x : α →
        ∀ {«Δ» : _root_.B.RenamingContext.Context} (Δ_fv : ∀ v ∈ _root_.B.fv x, («Δ» v).isSome = true)
          {Δ₀ : SMT.RenamingContext.Context},
          RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» x →
            ∀ {used : List SMT.𝒱},
              (∀ v ∉ used, Δ₀ v = none) →
                ∀ {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ},
                  ⟦x.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩ →
                    (∀ v ∈ x.vars, v ∈ used) →
                      (∀ v ∈ x.vars, v ∈ Λ → v ∈ E.context) →
                        ∀ {n : ℕ},
                          ⦃fun x_1 =>
                            match x_1 with
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
                                                (∀ v ∈ used, v ∉ Λ → v ∉ _root_.B.fv x → v ∉ Γ') ∧
                                                  ∃ Δ',
                                                    ∃ (Δ'_covers : RenamingContext.CoversFV Δ' t'),
                                                      RenamingContext.Extends Δ' Δ₀ ∧
                                                        RenamingContext.ExtendsOnSourceFV Δ' «Δ» x ∧
                                                          (∀ v ∉ E'.usedVars, Δ' v = none) ∧
                                                            ∃ denT',
                                                              ⟦t'.abstract Δ' Δ'_covers⟧ˢ = some denT' ∧
                                                                ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT' ∧
                                                                  ∀ (Δ_alt : _root_.B.RenamingContext.Context)
                                                                    (Δ_fv_alt :
                                                                      ∀ v ∈ _root_.B.fv x, (Δ_alt v).isSome = true)
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
  (E : _root_.B.Env) {Λ : SMT.TypeContext} {α : BType} (typ_t : E.context ⊢ᴮ .app f x : α)
  {«Δ» : _root_.B.RenamingContext.Context} (Δ_fv : ∀ v ∈ _root_.B.fv (.app f x), («Δ» v).isSome = true)
  {Δ₀ : SMT.RenamingContext.Context} (Δ₀_ext : RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» (.app f x)) {used : List SMT.𝒱}
  (Δ₀_none_out : ∀ v ∉ used, Δ₀ v = none) {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ}
  (den_t : ⟦(B.Term.app f x).abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩) (vars_used : ∀ v ∈ (B.Term.app f x).vars, v ∈ used)
  (Λ_inv : ∀ v ∈ (B.Term.app f x).vars, v ∈ Λ → v ∈ E.context) {n : ℕ} :
  ⦃fun x_1 =>
    match x_1 with
    | { env := E0, types := Λ' } => ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
    encodeTerm (.app f x) E ⦃PostCond.mayThrow fun x_1 x_2 =>
      match x_1 with
      | (t', σ) =>
        match x_2 with
        | { env := E', types := Γ' } =>
          ⌜used ⊆ E'.usedVars ∧
              Λ ⊆ Γ' ∧
                AList.keys Γ' ⊆ E'.usedVars ∧
                  CoversUsedVars E'.usedVars (.app f x) ∧
                    σ = α.toSMTType ∧
                      Γ' ⊢ˢ t' : σ ∧
                        (∀ v ∈ used, v ∉ Λ → v ∉ _root_.B.fv (.app f x) → v ∉ Γ') ∧
                          ∃ Δ',
                            ∃ (Δ'_covers : RenamingContext.CoversFV Δ' t'),
                              RenamingContext.Extends Δ' Δ₀ ∧
                                RenamingContext.ExtendsOnSourceFV Δ' «Δ» (.app f x) ∧
                                  (∀ v ∉ E'.usedVars, Δ' v = none) ∧
                                    ∃ denT',
                                      ⟦t'.abstract Δ' Δ'_covers⟧ˢ = some denT' ∧
                                        ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT' ∧
                                          ∀ (Δ_alt : _root_.B.RenamingContext.Context)
                                            (Δ_fv_alt : ∀ v ∈ _root_.B.fv (.app f x), (Δ_alt v).isSome = true)
                                            (Δ₀_alt : SMT.RenamingContext.Context),
                                            RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt (.app f x) →
                                              (∀ v ∉ E'.usedVars, Δ₀_alt v = none) →
                                              (∀ v (d : SMT.Dom), Δ₀_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) →
                                                ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦α⟧ᶻ),
                                                  ⟦(B.Term.app f x).abstract Δ_alt Δ_fv_alt⟧ᴮ = some ⟨T_alt, ⟨α, hT_alt⟩⟩ →
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
  rw [encodeTerm]

  -- Decompose B typing: app f x : α → ∃ γ, f : set(γ ×ᴮ α) ∧ x : γ
  obtain ⟨γ, typ_f, typ_x⟩ := _root_.B.Typing.appE typ_t

  -- Decompose Δ_fv for f and x
  have Δ_fv_f : ∀ v ∈ _root_.B.fv f, («Δ» v).isSome = true := by
    intro v hv
    exact Δ_fv v (by rw [_root_.B.fv, List.mem_append]; exact Or.inl hv)
  have Δ_fv_x : ∀ v ∈ _root_.B.fv x, («Δ» v).isSome = true := by
    intro v hv
    exact Δ_fv v (by rw [_root_.B.fv, List.mem_append]; exact Or.inr hv)

  -- Decompose B denotation of (app f x)
  rw [_root_.B.Term.abstract, _root_.B.denote, Option.pure_def, Option.bind_eq_bind,
    Option.bind_eq_some_iff] at den_t
  obtain ⟨⟨F, τF, hF⟩, den_f, eq⟩ := den_t
  have hτF := denote_welltyped_eq
    (t := f.abstract («Δ» := «Δ») Δ_fv_f)
    ?_ den_f
  on_goal 2 =>
    use E.context.abstract («Δ» := «Δ»), WFTC.of_abstract, .set (γ ×ᴮ α)
    exact @Typing.of_abstract (_root_.B.Dom) («Δ» := «Δ») ?_ f E.context (.set (γ ×ᴮ α)) Δ_fv_f typ_f
  dsimp at hτF
  subst τF

  dsimp at eq
  rw [Option.bind_eq_some_iff] at eq
  obtain ⟨⟨X, τX, hX⟩, den_x, eq⟩ := eq
  have hτX := denote_welltyped_eq
    (t := x.abstract («Δ» := «Δ») Δ_fv_x)
    ?_ den_x
  on_goal 2 =>
    use E.context.abstract («Δ» := «Δ»), WFTC.of_abstract, γ
    exact @Typing.of_abstract (_root_.B.Dom) («Δ» := «Δ») ?_ x E.context γ Δ_fv_x typ_x
  dsimp at hτX
  subst τX

  -- Now eq contains: dif_pos ... → F.fapply ... = ⟨T, α, hT⟩
  dsimp at eq
  rw [if_pos rfl] at eq
  -- eq : (if ispfun : ... then ... else failure) = some ⟨T, α, hT⟩
  split_ifs at eq with ispfun X_dom
  · -- F is a partial function from γ to α, X is in the domain of F
    rw [Option.some_inj] at eq
    obtain ⟨⟩ := eq

    -- ExtendsOnSourceFV for subterms
    have Δ₀_ext_f : RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» f := by
      exact RenamingContext.extendsOnSourceFV_of_fv_subset
        (hsub := by intro v hv; simpa [_root_.B.fv] using (Or.inl hv : v ∈ _root_.B.fv f ∨ v ∈ _root_.B.fv x))
        Δ₀_ext
    have Δ₀_ext_x : RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» x := by
      exact RenamingContext.extendsOnSourceFV_of_fv_subset
        (hsub := by intro v hv; simpa [_root_.B.fv] using (Or.inr hv : v ∈ _root_.B.fv f ∨ v ∈ _root_.B.fv x))
        Δ₀_ext

    -- Apply f_ih
    mspec f_ih (E := E) (Λ := St.types) (α := .set (γ ×ᴮ α)) typ_f
      («Δ» := «Δ») Δ_fv_f (Δ₀ := Δ₀) Δ₀_ext_f (used := used) Δ₀_none_out (T := F) (hT := hF) den_f
      (fun v hv => vars_used v (by
        simp only [_root_.B.Term.vars, List.mem_union_iff, _root_.B.fv, _root_.B.bv, List.mem_append] at hv ⊢
        rcases hv with h | h <;> [left; right] <;> exact .inl h))
      (fun v hv => Λ_inv v (by
        simp only [_root_.B.Term.vars, List.mem_union_iff, _root_.B.fv, _root_.B.bv, List.mem_append] at hv ⊢
        rcases hv with h | h <;> [left; right] <;> exact .inl h))
      (n := St.env.freshvarsc)
    clear f_ih
    rename_i out_f
    obtain ⟨f_enc, Stf⟩ := out_f
    mrename_i pre
    mintro ∀Stf
    mpure pre
    dsimp at pre
    obtain ⟨St_used_sub_Stf, St_eq_Stf, Stf_sub, f_cov_Stf, rfl, typ_f_enc, f_preserves,
      Δ'f, Δ'f_covers_f, Δ'f_extends_Δ₀, Δ'f_ext_f, Δ'f_none_out,
      ⟨Fenc, _, hFenc⟩, den_f_enc, ⟨rfl, retract_Fenc_eq_F⟩, f_ih_total⟩ := pre

    -- Prepare x_ih
    have Δ'f_ext_x : RenamingContext.ExtendsOnSourceFV Δ'f «Δ» x := by
      exact RenamingContext.extendsOnSourceFV_of_extends Δ'f_extends_Δ₀ Δ₀_ext_x

    mspec x_ih (E := E) (Λ := Stf.types) (α := γ) typ_x
      («Δ» := «Δ») Δ_fv_x (Δ₀ := Δ'f) Δ'f_ext_x (used := Stf.env.usedVars) Δ'f_none_out
      (T := X) (hT := hX) den_x
      (fun v hv => St_used_sub_Stf (vars_used v (by
        simp only [_root_.B.Term.vars, List.mem_union_iff, _root_.B.fv, _root_.B.bv, List.mem_append] at hv ⊢
        rcases hv with h | h <;> [left; right] <;> exact .inr h)))
      (fun v hv hΛ => by
        have hv_app : v ∈ (B.Term.app f x).vars := by
          simp only [_root_.B.Term.vars, List.mem_union_iff, _root_.B.fv, _root_.B.bv, List.mem_append] at hv ⊢
          rcases hv with h | h <;> [left; right] <;> exact .inr h
        by_cases hv_St : v ∈ St.types
        · exact Λ_inv v hv_app hv_St
        · have hv_fv_f : v ∈ _root_.B.fv f := by
            by_contra h_neg
            exact absurd hΛ (f_preserves v (vars_used v hv_app) hv_St h_neg)
          exact _root_.B.Typing.typed_by_fv typ_f hv_fv_f)
      (n := Stf.env.freshvarsc)
    clear x_ih
    rename_i out_x
    obtain ⟨x_enc, Stx⟩ := out_x
    mrename_i pre
    mintro ∀Stx
    mpure pre
    dsimp at pre
    obtain ⟨Stf_used_sub_Stx, Stf_eq_Stx, Stx_sub, x_cov_Stx, rfl, typ_x_enc, x_preserves,
      Δ'x, Δ'x_covers_x, Δ'x_extends_Δ'f, Δ'x_ext_x, Δ'x_none_out,
      ⟨Xenc, _, hXenc⟩, den_x_enc, ⟨rfl, retract_Xenc_eq_X⟩, x_ih_total⟩ := pre

    -- Now we need to unfold castApp
    -- After IH: f_enc : (.set (γ ×ᴮ α)).toSMTType = .fun (.pair γ.toSMTType α.toSMTType) .bool
    --           x_enc : γ.toSMTType
    -- castApp matches first arm with τ = γ.toSMTType, σ = α.toSMTType, ξ = γ.toSMTType
    -- Since τ ⊑ ξ (reflexive), the first branch fires

    -- Unfold castApp and resolve the dif_pos branch
    simp only [castApp, BType.toSMTType]
    rw [dif_pos castable?.reflexive]

    -- Weaken f_enc typing to Stx.types
    have typ_f_enc_Stx : Stx.types ⊢ˢ f_enc : (γ ×ᴮ α).set.toSMTType :=
      Typing.weakening Stf_eq_Stx typ_f_enc

    -- The renaming context Δ'x covers f_enc too (since Δ'x extends Δ'f which covers f_enc)
    have Δ'x_covers_f : RenamingContext.CoversFV Δ'x f_enc :=
      RenamingContext.coversFV_of_extends_of_coversFV Δ'x_extends_Δ'f Δ'f_covers_f

    -- Denotation of f_enc under Δ'x agrees with Δ'f
    have den_f_enc_Δ'x : ⟦f_enc.abstract Δ'x Δ'x_covers_f⟧ˢ =
        some ⟨Fenc, ⟨(γ ×ᴮ α).set.toSMTType, hFenc⟩⟩ := by
      have hag : RenamingContext.AgreesOnFV Δ'x Δ'f f_enc :=
        RenamingContext.agreesOnFV_of_extends_of_coversFV Δ'x_extends_Δ'f Δ'f_covers_f
      have hcongr := RenamingContext.denote_congr_of_agreesOnFV
        (t := f_enc) (h1 := Δ'x_covers_f) (h2 := Δ'f_covers_f) hag
      simpa [RenamingContext.denote] using hcongr.trans den_f_enc

    set ctx := Stx.types

    -- Step 1: loosenAux_prf
    mspec loosenAux_prf_spec (Λ := ctx)
      (typ_x := by rw [BType.toSMTType] at typ_f_enc_Stx; exact typ_f_enc_Stx)
      (𝕔 := (castable?.reflexive.toCastPath.pair (castPath.reflexive α.toSMTType)).chpred)
      (hx := Δ'x_covers_f) (n := Stx.env.freshvarsc) (used := Stx.env.usedVars)
    case post.success «f!_out» =>
      obtain ⟨«f!», f!_spec⟩ := «f!_out»
      mrename_i pre
      mintro ∀St₁
      mpure pre
      obtain ⟨n_le_St₁, Λ_insert_f!_sub, f!_not_ctx, f!_not_used, used_sub_St₁,
        St₁_sub, preserves_St₁, typ_var_f!_insert, typ_f!_spec_insert,
        typ_var_f!, typ_f!_spec, fv_f!_spec_sub, f!_den_adequacy⟩ := pre

      -- Step 2: declareConst f!
      mspec SMT.declareConst_spec (v := «f!») (τ := (γ.toSMTType.pair α.toSMTType).fun .bool)
        (decl := St₁.env.declarations) (as := St₁.env.asserts)
        (Γ := St₁.types) (n := St₁.env.freshvarsc) (used := St₁.env.usedVars)
      mrename_i pre
      mintro ∀St₂
      mpure pre
      obtain ⟨_, _, St₂_fvc_eq, St₂_used_eq, St₂_types_eq⟩ := pre

      -- Step 3: addSpec f!
      mspec SMT.addSpec_spec (x! := «f!») (x!_spec := f!_spec)
        (decl := St₂.env.declarations) (as := St₂.env.asserts)
        (Γ := St₂.types) (n := St₂.env.freshvarsc) (used := St₂.env.usedVars)
      mrename_i pre
      mintro ∀St₃
      mpure pre
      obtain ⟨_, _, St₃_fvc_eq, St₃_used_eq, St₃_types_eq⟩ := pre

      -- Step 4: freshVar f!! : γ.toSMTType.fun α.toSMTType.option
      mspec freshVar_spec
        (Γ := St₃.types) (τ := γ.toSMTType.fun α.toSMTType.option)
        (n := St₃.env.freshvarsc) (used := St₃.env.usedVars)
      case post.success f!! =>
        mrename_i pre
        mintro ∀St₄
        mpure pre
        obtain ⟨St₄_types_eq, f!!_fresh, St₄_fvc_eq, St₄_used_eq, f!!_not_used⟩ := pre

        -- Step 5: declareConst f!!
        mspec SMT.declareConst_spec (v := f!!) (τ := γ.toSMTType.fun α.toSMTType.option)
          (decl := St₄.env.declarations) (as := St₄.env.asserts)
          (Γ := St₄.types) (n := St₄.env.freshvarsc) (used := St₄.env.usedVars)
        mrename_i pre
        mintro ∀St₅
        mpure pre
        obtain ⟨_, _, St₅_fvc_eq, St₅_used_eq, St₅_types_eq⟩ := pre

        -- Step 6: freshVar u : γ.toSMTType
        mspec freshVar_spec
          (Γ := St₅.types) (τ := γ.toSMTType)
          (n := St₅.env.freshvarsc) (used := St₅.env.usedVars)
        case post.success u =>
          mrename_i pre
          mintro ∀St₆
          mpure pre
          obtain ⟨St₆_types_eq, u_fresh, St₆_fvc_eq, St₆_used_eq, u_not_used⟩ := pre

          -- Step 7: freshVar v : α.toSMTType
          mspec freshVar_spec
            (Γ := St₆.types) (τ := α.toSMTType)
            (n := St₆.env.freshvarsc) (used := St₆.env.usedVars)
          case post.success v =>
            mrename_i pre
            mintro ∀St₇
            mpure pre
            obtain ⟨St₇_types_eq, v_fresh, St₇_fvc_eq, St₇_used_eq, v_not_used⟩ := pre

            -- Step 8: addSpec f!!
            mspec SMT.addSpec_spec (x! := f!!)
              (decl := St₇.env.declarations) (as := St₇.env.asserts)
              (Γ := St₇.types) (n := St₇.env.freshvarsc) (used := St₇.env.usedVars)
            mrename_i pre
            mintro ∀St₈
            mpure pre
            obtain ⟨_, _, St₈_fvc_eq, St₈_used_eq, St₈_types_eq⟩ := pre

            -- Step 9: pure
            mspec Std.Do.Spec.pure
            mpure_intro

            -- Consolidate helper facts
            have ctx_sub_St₁ : ctx ⊆ St₁.types := fun _ h =>
              Λ_insert_f!_sub (SMT.TypeContext.entries_subset_insert_of_notMem f!_not_ctx h)
            have f!!_fresh_St₁ : f!! ∉ St₁.types := by
              rw [← St₂_types_eq, ← St₃_types_eq]; exact f!!_fresh
            have u_fresh_St₄ : u ∉ St₄.types := by
              rw [← St₅_types_eq]; exact u_fresh
            have St₁_sub_St₈ : St₁.types ⊆ St₈.types := by
              intro w hw
              have h4 : w ∈ St₄.types.entries := by
                rw [St₄_types_eq, St₃_types_eq, St₂_types_eq]
                exact SMT.TypeContext.entries_subset_insert_of_notMem f!!_fresh_St₁ hw
              have h6 : w ∈ St₆.types.entries := by
                rw [St₆_types_eq, St₅_types_eq]
                exact SMT.TypeContext.entries_subset_insert_of_notMem u_fresh_St₄ h4
              rw [St₈_types_eq, St₇_types_eq]
              exact SMT.TypeContext.entries_subset_insert_of_notMem v_fresh h6
            have ctx_sub_St₈ : ctx ⊆ St₈.types := fun _ h => St₁_sub_St₈ (ctx_sub_St₁ h)

            -- usedVars chain
            have Stx_used_sub_St₈ : Stx.env.usedVars ⊆ St₈.env.usedVars := by
              intro w hw
              rw [St₈_used_eq, St₇_used_eq, St₆_used_eq, St₅_used_eq, St₄_used_eq,
                St₃_used_eq, St₂_used_eq]
              exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ (used_sub_St₁ hw)))

            -- Prove postconditions
            and_intros
            · -- 1. used ⊆ St₈.env.usedVars
              exact fun _ hw => Stx_used_sub_St₈ (Stf_used_sub_Stx (St_used_sub_Stf hw))
            · -- 2. St.types ⊆ St₈.types
              exact fun _ hw => ctx_sub_St₈ (Stf_eq_Stx (St_eq_Stf hw))
            · -- 3. AList.keys St₈.types ⊆ St₈.env.usedVars
              intro w hw
              rw [St₈_used_eq, St₇_used_eq, St₆_used_eq, St₅_used_eq, St₄_used_eq,
                St₃_used_eq, St₂_used_eq]
              have hw' : w ∈ St₈.types := (AList.mem_keys).mpr hw
              rw [St₈_types_eq, St₇_types_eq] at hw'
              rw [AList.mem_insert] at hw'
              rcases hw' with rfl | hw'
              · exact List.mem_cons_self
              · rw [St₆_types_eq] at hw'
                rw [AList.mem_insert] at hw'
                rcases hw' with rfl | hw'
                · exact List.mem_cons_of_mem _ List.mem_cons_self
                · rw [St₅_types_eq, St₄_types_eq] at hw'
                  rw [AList.mem_insert] at hw'
                  rcases hw' with rfl | hw'
                  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
                  · rw [St₃_types_eq, St₂_types_eq] at hw'
                    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                      (List.mem_cons_of_mem _ (St₁_sub ((AList.mem_keys).mp hw'))))
            · -- 4. CoversUsedVars
              intro w hw
              rw [B.fv, List.mem_append] at hw
              rcases hw with hw | hw
              · exact Stx_used_sub_St₈ (Stf_used_sub_Stx (f_cov_Stf w hw))
              · exact Stx_used_sub_St₈ (x_cov_Stx w hw)
            · -- 5. True
              trivial
            · -- 6. Typing: St₈.types ⊢ˢ (.the (.app (.var f!!) x_enc)) : α.toSMTType
              apply SMT.Typing.the
              apply SMT.Typing.app
              · apply SMT.Typing.var
                rw [St₈_types_eq, St₇_types_eq]
                have hf_ne_v : f!! ≠ v := by
                  intro h; subst h
                  exact v_not_used (St₆_used_eq ▸ List.mem_cons_of_mem _
                    (St₅_used_eq ▸ St₄_used_eq ▸ List.mem_cons_self))
                have hf_ne_u : f!! ≠ u := by
                  intro h; subst h
                  exact u_not_used (St₅_used_eq ▸ St₄_used_eq ▸ List.mem_cons_self)
                rw [AList.lookup_insert_ne hf_ne_v, St₆_types_eq,
                  AList.lookup_insert_ne hf_ne_u, St₅_types_eq, St₄_types_eq,
                  AList.lookup_insert]
              · exact SMT.Typing.weakening ctx_sub_St₈ typ_x_enc
            · -- 7. preserves_types
              intro w hw h1 h2
              rw [_root_.B.fv, List.mem_append] at h2; push_neg at h2
              have hw_Stf : w ∈ Stf.env.usedVars :=
                St_used_sub_Stf (by simpa [St_used_eq] using hw)
              have hw_not_Stf : w ∉ Stf.types :=
                f_preserves w (by simpa [St_used_eq] using hw) h1 h2.1
              have hw_not_ctx : w ∉ ctx := x_preserves w hw_Stf hw_not_Stf h2.2
              have hw_Stx : w ∈ Stx.env.usedVars := Stf_used_sub_Stx hw_Stf
              have hw_not_St₁ : w ∉ St₁.types := preserves_St₁ w hw_Stx hw_not_ctx
              rw [St₈_types_eq, St₇_types_eq]
              intro hw_in
              rw [AList.mem_insert] at hw_in
              rcases hw_in with rfl | hw_in
              · exact v_not_used (St₆_used_eq ▸ List.mem_cons_of_mem _
                  (St₅_used_eq ▸ St₄_used_eq ▸ List.mem_cons_of_mem _
                  (St₃_used_eq ▸ St₂_used_eq ▸ used_sub_St₁ hw_Stx)))
              · rw [St₆_types_eq, AList.mem_insert] at hw_in
                rcases hw_in with rfl | hw_in
                · exact u_not_used (St₅_used_eq ▸ St₄_used_eq ▸
                    List.mem_cons_of_mem _
                    (St₃_used_eq ▸ St₂_used_eq ▸ used_sub_St₁ hw_Stx))
                · rw [St₅_types_eq, St₄_types_eq, AList.mem_insert] at hw_in
                  rcases hw_in with rfl | hw_in
                  · exact f!!_not_used
                      (St₃_used_eq ▸ St₂_used_eq ▸ used_sub_St₁ hw_Stx)
                  · rw [St₃_types_eq, St₂_types_eq] at hw_in
                    exact hw_not_St₁ hw_in
            · -- 8. ∃ Δ', ...  (denotation + totality)
              -- === Freshness ===
              have f!!_not_Stx : f!! ∉ Stx.env.usedVars := by
                intro h; exact f!!_not_used (St₃_used_eq ▸ St₂_used_eq ▸ used_sub_St₁ h)
              have Δ'x_f!!_none : Δ'x f!! = none := by
                by_contra h; push_neg at h
                obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (Option.ne_none_iff_isSome.mp h)
                exact f!!_not_Stx (by_contra fun h_neg => by simp [Δ'x_none_out f!! h_neg] at hd)
              have f!!_not_fv_x : f!! ∉ SMT.fv x_enc := by
                intro h; exact absurd (Δ'x_covers_x f!! h) (by simp [Δ'x_f!!_none])
              have f!!_not_fv_f : f!! ∉ SMT.fv f_enc := by
                intro h; exact absurd (Δ'x_covers_f f!! h) (by simp [Δ'x_f!!_none])
              have f!!_in_St₈ : f!! ∈ St₈.env.usedVars := by
                rw [St₈_used_eq, St₇_used_eq, St₆_used_eq, St₅_used_eq, St₄_used_eq]
                exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
              -- === Construct Tenc via canonical iso ===
              have ζ_α_isfunc : ZFSet.IsFunc ⟦α⟧ᶻ ⟦α.toSMTType⟧ᶻ (BType.canonicalIsoSMTType α) :=
                (BType.canonicalIsoSMTType α).2.1
              let T : ZFSet := (@ZFSet.fapply F _ _ ispfun ⟨X, X_dom⟩).1
              have T_mem_dom : T ∈ (BType.canonicalIsoSMTType α).1.Dom := by
                rwa [ZFSet.is_func_dom_eq ζ_α_isfunc]
              let Tenc_sub := ZFSet.fapply (BType.canonicalIsoSMTType α).1
                (ZFSet.is_func_is_pfunc ζ_α_isfunc) ⟨T, T_mem_dom⟩
              have hTenc : Tenc_sub.1 ∈ ⟦α.toSMTType⟧ᶻ := ZFSet.fapply_mem_range _ _
              have retract_Tenc : retract α Tenc_sub.1 = T := retract_of_canonical α hT
              -- === Construct g: constant function ⟦γ.toSMTType⟧ᶻ → ⟦α.toSMTType.option⟧ᶻ ===
              let some_Tenc := ZFSet.Option.some (S := ⟦α.toSMTType⟧ᶻ) ⟨Tenc_sub.1, hTenc⟩
              have hg_range : ∀ z, z ∈ ⟦γ.toSMTType⟧ᶻ →
                  some_Tenc.val ∈ ⟦α.toSMTType.option⟧ᶻ :=
                fun _ _ => SetLike.coe_mem some_Tenc
              let g := ZFSet.lambda ⟦γ.toSMTType⟧ᶻ ⟦α.toSMTType.option⟧ᶻ (fun _ => some_Tenc.val)
              have hg_mem : g ∈ ⟦SMTType.fun γ.toSMTType (α.toSMTType.option)⟧ᶻ := by
                rw [SMTType.toZFSet]; exact ZFSet.mem_funs_of_lambda (fun hz => hg_range _ hz)
              -- === Build Δ' ===
              let g_dom : SMT.Dom := ⟨g, .fun γ.toSMTType (.option α.toSMTType), hg_mem⟩
              let Δ' : SMT.RenamingContext.Context :=
                Function.update Δ'x f!! (some g_dom)
              -- === CoversFV ===
              have hcov : RenamingContext.CoversFV Δ' ((@ˢSMT.Term.var f!!) x_enc).the := by
                intro w hw
                rw [SMT.fv] at hw -- fv(.the t) = fv(t)
                rw [SMT.fv, List.mem_append] at hw -- fv(.app f x) = fv(f) ++ fv(x)
                rcases hw with hw_f | hw_x
                · -- w ∈ fv(.var f!!) = [f!!]
                  rw [SMT.fv] at hw_f
                  simp only [List.mem_singleton] at hw_f; subst hw_f
                  simp [Δ', Function.update_self]
                · -- w ∈ fv(x_enc), so w ≠ f!! and Δ'x covers it
                  have hw_ne : w ≠ f!! := fun h => f!!_not_fv_x (h ▸ hw_x)
                  show (Function.update Δ'x f!! (some g_dom) w).isSome
                  rw [Function.update_of_ne hw_ne]
                  exact Δ'x_covers_x w hw_x
              refine ⟨Δ', hcov, ?_⟩
              and_intros
              · -- Extends Δ' Δ₀
                exact RenamingContext.extends_update_of_base_none
                  (RenamingContext.extends_trans Δ'x_extends_Δ'f Δ'f_extends_Δ₀)
                  (Δ₀_none_out f!! (fun h => f!!_not_used
                    (St₃_used_eq ▸ St₂_used_eq ▸ used_sub_St₁ (Stf_used_sub_Stx (St_used_sub_Stf h)))))
              · -- ExtendsOnSourceFV Δ' Δ ((@ᴮf) x)
                apply RenamingContext.extendsOnSourceFV_of_extends _ Δ₀_ext
                exact RenamingContext.extends_update_of_base_none
                  (RenamingContext.extends_trans Δ'x_extends_Δ'f Δ'f_extends_Δ₀)
                  (Δ₀_none_out f!! (fun h => f!!_not_used
                    (St₃_used_eq ▸ St₂_used_eq ▸ used_sub_St₁ (Stf_used_sub_Stx (St_used_sub_Stf h)))))
              · -- ∀ v ∉ St₈.env.usedVars, Δ' v = none
                intro w hw
                show Function.update Δ'x f!! (some g_dom) w = none
                by_cases hwf : w = f!!
                · subst hwf; exact absurd f!!_in_St₈ hw
                · rw [Function.update_of_ne hwf]
                  exact Δ'x_none_out w (fun h => hw (Stx_used_sub_St₈ h))
              · -- denotation + adequacy + totality
                -- Step 1: Transfer x_enc denotation from Δ'x to Δ'
                have Δ'_agrees_x : SMT.RenamingContext.AgreesOnFV Δ'x Δ' x_enc := by
                  intro w hw; show Δ'x w = Function.update Δ'x f!! (some g_dom) w
                  rw [Function.update_of_ne (fun h : w = f!! => f!!_not_fv_x (h ▸ hw))]
                have hΔ'_covers_x : RenamingContext.CoversFV Δ' x_enc := by
                  intro w hw; rw [← Δ'_agrees_x hw]; exact Δ'x_covers_x w hw
                have den_x_enc_Δ' :
                    ⟦x_enc.abstract Δ' hΔ'_covers_x⟧ˢ = some ⟨Xenc, ⟨γ.toSMTType, hXenc⟩⟩ := by
                  have heq := SMT.RenamingContext.denote_congr_of_agreesOnFV
                    (h1 := Δ'x_covers_x) (h2 := hΔ'_covers_x) Δ'_agrees_x
                  unfold SMT.RenamingContext.denote at heq; rw [← heq]; exact den_x_enc
                -- Step 2: g properties
                have g_isFunc : ZFSet.IsFunc ⟦γ.toSMTType⟧ᶻ ⟦α.toSMTType.option⟧ᶻ g :=
                  ZFSet.lambda_isFunc (fun hz => hg_range _ hz)
                have g_isPFunc : g.IsPFunc ⟦γ.toSMTType⟧ᶻ ⟦α.toSMTType.option⟧ᶻ :=
                  ZFSet.is_func_is_pfunc g_isFunc
                have Xenc_in_dom : Xenc ∈ g.Dom :=
                  by rw [ZFSet.is_func_dom_eq g_isFunc]; exact hXenc
                have fapply_g_val_eq :
                    (↑(ZFSet.fapply g g_isPFunc ⟨Xenc, Xenc_in_dom⟩) : ZFSet) =
                    some_Tenc.val := by
                  exact_mod_cast @ZFSet.fapply_lambda ⟦γ.toSMTType⟧ᶻ ⟦α.toSMTType.option⟧ᶻ
                    (fun _ => some_Tenc.val) (fun hz => hg_range _ hz) Xenc hXenc
                have fapply_g_mem :
                    (↑(ZFSet.fapply g g_isPFunc ⟨Xenc, Xenc_in_dom⟩) : ZFSet) ∈
                    ⟦SMTType.option α.toSMTType⟧ᶻ :=
                  (ZFSet.fapply g g_isPFunc ⟨Xenc, Xenc_in_dom⟩).2
                -- Compute the .app denotation as intermediate
                have hcov_app :
                    RenamingContext.CoversFV Δ' ((@ˢSMT.Term.var f!!) x_enc) := by
                  intro w hw; simp only [SMT.fv] at hw
                  rw [List.mem_append] at hw
                  rcases hw with hw | hw
                  · simp only [SMT.fv, List.mem_singleton] at hw
                    subst hw; simp [Δ', Function.update_self]
                  · exact hΔ'_covers_x w hw
                have den_app :
                    ⟦((@ˢSMT.Term.var f!!) x_enc).abstract Δ' hcov_app⟧ˢ =
                    some ⟨↑(ZFSet.fapply g g_isPFunc ⟨Xenc, Xenc_in_dom⟩),
                      ⟨.option α.toSMTType, fapply_g_mem⟩⟩ := by
                  rw [SMT.Term.abstract.eq_def, SMT.denote,
                    SMT.Term.abstract.eq_def, SMT.denote, Option.pure_def,
                    Option.bind_eq_bind, Option.bind_some, den_x_enc_Δ']
                  simp only [Δ', Function.update_self, Option.get_some, g_dom,
                    Option.bind_some, dif_pos g_isPFunc, dif_pos Xenc_in_dom, dite_true]
                -- Compute the full .the denotation
                have den_the :
                    ⟦((@ˢSMT.Term.var f!!) x_enc).the.abstract Δ' hcov⟧ˢ =
                    some ⟨↑(ZFSet.Option.the SMTType.toZFSet_nonempty
                      ⟨↑(ZFSet.fapply g g_isPFunc ⟨Xenc, Xenc_in_dom⟩), fapply_g_mem⟩),
                      ⟨α.toSMTType, SetLike.coe_mem _⟩⟩ := by
                  rw [SMT.Term.abstract.eq_def, SMT.denote, den_app]
                  rfl
                -- The cast: fapply g ... = some_Tenc at ZFSet level
                have h_some_Tenc_mem :
                    some_Tenc.val ∈ ⟦SMTType.option α.toSMTType⟧ᶻ :=
                  SetLike.coe_mem some_Tenc
                have the_cast :
                    (ZFSet.Option.the SMTType.toZFSet_nonempty
                      ⟨↑(ZFSet.fapply g g_isPFunc ⟨Xenc, Xenc_in_dom⟩),
                       fapply_g_mem⟩ : {x // x ∈ ⟦α.toSMTType⟧ᶻ}) =
                    ZFSet.Option.the SMTType.toZFSet_nonempty
                      ⟨some_Tenc.val, h_some_Tenc_mem⟩ := by
                  congr 1; exact Subtype.ext fapply_g_val_eq
                -- Witness
                let denT' : SMT.Dom :=
                  ⟨↑(ZFSet.Option.the SMTType.toZFSet_nonempty
                    ⟨↑(ZFSet.fapply g g_isPFunc ⟨Xenc, Xenc_in_dom⟩), fapply_g_mem⟩),
                   ⟨α.toSMTType, SetLike.coe_mem _⟩⟩
                refine ⟨denT', den_the, ?_, ?_⟩
                · -- RDom: ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT'
                  constructor
                  · rfl
                  · -- retract α (the (fapply g ...)) = T
                    show retract α ↑(ZFSet.Option.the SMTType.toZFSet_nonempty
                      ⟨↑(ZFSet.fapply g g_isPFunc ⟨Xenc, Xenc_in_dom⟩), fapply_g_mem⟩) = T
                    rw [show (↑(ZFSet.Option.the SMTType.toZFSet_nonempty
                      ⟨↑(ZFSet.fapply g g_isPFunc ⟨Xenc, Xenc_in_dom⟩), fapply_g_mem⟩) :
                      ZFSet) =
                      ↑(ZFSet.Option.the SMTType.toZFSet_nonempty
                      ⟨some_Tenc.val, h_some_Tenc_mem⟩) from congrArg Subtype.val the_cast]
                    -- the(some(⟨Tenc, hTenc⟩)) = ⟨Tenc, hTenc⟩
                    have hsub : (⟨some_Tenc.val, h_some_Tenc_mem⟩ :
                        ZFSet.Option ⟦α.toSMTType⟧ᶻ) = some_Tenc :=
                      Subtype.ext rfl
                    unfold ZFSet.Option.the
                    have hne : some_Tenc ≠ ZFSet.Option.none :=
                      ZFSet.Option.some_ne_none ⟨Tenc_sub.val, hTenc⟩
                    rw [hsub, dif_neg hne]
                    have hspec := Classical.choose_spec
                      (Or.resolve_left (ZFSet.Option.casesOn some_Tenc) hne)
                    rw [ZFSet.Option.some.injEq] at hspec
                    rw [show (Classical.choose
                      (Or.resolve_left (ZFSet.Option.casesOn some_Tenc) hne)) =
                      ⟨Tenc_sub.val, hTenc⟩ from hspec.symm]
                    exact retract_Tenc
                · -- totality
                  intro Δ_alt Δ_fv_alt Δ₀_alt Δ₀_alt_ext Δ₀_alt_none_out Δ₀_alt_wt T_alt hT_alt den_t_alt
                  -- Decompose B-denotation of (app f x) under alt valuation
                  have Δ_fv_alt_f : ∀ v ∈ B.fv f, (Δ_alt v).isSome = true :=
                    fun v hv => Δ_fv_alt v (by rw [B.fv, List.mem_append]; exact Or.inl hv)
                  have Δ_fv_alt_x : ∀ v ∈ B.fv x, (Δ_alt v).isSome = true :=
                    fun v hv => Δ_fv_alt v (by rw [B.fv, List.mem_append]; exact Or.inr hv)
                  rw [B.Term.abstract, B.denote, Option.pure_def, Option.bind_eq_bind,
                    Option.bind_eq_some_iff] at den_t_alt
                  obtain ⟨⟨F_alt, τF_alt, hF_alt⟩, den_f_alt, eq_alt⟩ := den_t_alt
                  have hτF_alt := denote_welltyped_eq
                    (t := f.abstract («Δ» := Δ_alt) Δ_fv_alt_f) ?_ den_f_alt
                  on_goal 2 =>
                    use E.context.abstract («Δ» := Δ_alt), WFTC.of_abstract, .set (γ ×ᴮ α)
                    exact @Typing.of_abstract (B.Dom) («Δ» := Δ_alt) ?_ f E.context
                      (.set (γ ×ᴮ α)) Δ_fv_alt_f typ_f
                  dsimp at hτF_alt; subst τF_alt
                  rw [Option.bind_eq_some_iff] at eq_alt
                  obtain ⟨⟨X_alt, τX_alt, hX_alt⟩, den_x_alt, eq_alt2⟩ := eq_alt
                  have hτX_alt := denote_welltyped_eq
                    (t := x.abstract («Δ» := Δ_alt) Δ_fv_alt_x) ?_ den_x_alt
                  on_goal 2 =>
                    use E.context.abstract («Δ» := Δ_alt), WFTC.of_abstract, γ
                    exact @Typing.of_abstract (B.Dom) («Δ» := Δ_alt) ?_ x E.context γ
                      Δ_fv_alt_x typ_x
                  dsimp at hτX_alt; subst τX_alt
                  dsimp at eq_alt2
                  rw [if_pos rfl] at eq_alt2
                  split_ifs at eq_alt2 with ispfun_alt X_alt_dom
                  · -- F_alt is a partial function, X_alt is in its domain
                    rw [Option.some_inj] at eq_alt2
                    obtain ⟨⟩ := eq_alt2
                    -- === Step 1: Restrict Δ₀_alt for f_ih_total ===
                    -- f_ih_total expects vanishing at Stf.env.usedVars, but Δ₀_alt
                    -- only vanishes at St₈.env.usedVars (which is bigger).
                    -- Restrict Δ₀_alt to the Stf scope.
                    set Δ₀_alt_f : SMT.RenamingContext.Context :=
                      fun v => if v ∈ Stf.env.usedVars then Δ₀_alt v else none
                      with Δ₀_alt_f_def
                    have Δ₀_alt_ext_f :
                        RenamingContext.ExtendsOnSourceFV Δ₀_alt_f Δ_alt f := by
                      have hsrc := RenamingContext.extendsOnSourceFV_of_fv_subset
                        (hsub := by intro v hv; simpa [B.fv] using
                          (Or.inl hv : v ∈ B.fv f ∨ v ∈ B.fv x))
                        Δ₀_alt_ext
                      intro v d hv
                      -- hv : toSMTOnFV Δ_alt f v = some d, need: Δ₀_alt_f v = some d
                      have hv_fv : v ∈ B.fv f := by
                        by_contra hv_not
                        simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                          B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_not] at hv
                      have hv_used : v ∈ Stf.env.usedVars := f_cov_Stf v hv_fv
                      show (if v ∈ Stf.env.usedVars then Δ₀_alt v else none) = some d
                      rw [if_pos hv_used]
                      exact hsrc hv
                    have f_none_Stf : ∀ v ∉ Stf.env.usedVars, Δ₀_alt_f v = none := by
                      intro v hv
                      show (if v ∈ Stf.env.usedVars then Δ₀_alt v else none) = none
                      rw [if_neg hv]
                    have Stf_types_sub_St₈ : Stf.types ⊆ St₈.types :=
                      fun _ h => ctx_sub_St₈ (Stf_eq_Stx h)
                    have f_wt_Stf : ∀ v (d : SMT.Dom), Δ₀_alt_f v = some d → ∀ τ, Stf.types.lookup v = some τ → d.snd.fst = τ := by
                      intro v d hv τ hτ
                      have hv' : (if v ∈ Stf.env.usedVars then Δ₀_alt v else none) = some d := hv
                      split_ifs at hv' with h_used
                      exact Δ₀_alt_wt v d hv' τ (AList.lookup_of_subset Stf_types_sub_St₈ hτ)
                    obtain ⟨Δ'_alt_f, hcov_alt_f, denT_f_alt, hext_alt_f,
                      Δ'_alt_f_none_out, Δ'_alt_f_wt_out, den_f_alt_enc, hRDom_f_alt, _⟩ :=
                      f_ih_total Δ_alt Δ_fv_alt_f Δ₀_alt_f Δ₀_alt_ext_f f_none_Stf f_wt_Stf
                        F_alt hF_alt den_f_alt
                    -- === Step 2: Build hybrid base for x_ih_total ===
                    -- x_ih_total expects vanishing at Stx.env.usedVars.
                    -- Guard with Stx membership so vanishing is trivial.
                    set Δ₀_alt_x : SMT.RenamingContext.Context :=
                      fun v => if v ∈ Stx.env.usedVars
                        then (match Δ₀_alt v with
                          | some d => some d
                          | none => if v ∈ Stf.types then Δ'_alt_f v else none)
                        else none
                      with Δ₀_alt_x_def
                    -- ExtendsOnSourceFV Δ₀_alt_x Δ_alt x
                    have Δ₀_alt_x_ext :
                        RenamingContext.ExtendsOnSourceFV Δ₀_alt_x Δ_alt x := by
                      have hsrc := RenamingContext.extendsOnSourceFV_of_fv_subset
                        (hsub := by intro v hv; simpa [B.fv] using
                          (Or.inr hv : v ∈ B.fv f ∨ v ∈ B.fv x))
                        Δ₀_alt_ext
                      intro v d hv
                      have hv_fv : v ∈ B.fv x := by
                        by_contra hv_not
                        simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                          B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_not] at hv
                      have hv_used : v ∈ Stx.env.usedVars := x_cov_Stx v hv_fv
                      simp only [Δ₀_alt_x_def, if_pos hv_used]
                      have hΔ₀_val := hsrc hv
                      simp [hΔ₀_val]
                    -- none_out for Δ₀_alt_x at Stx.env.usedVars
                    have Δ₀_alt_x_none :
                        ∀ v ∉ Stx.env.usedVars, Δ₀_alt_x v = none := by
                      intro v hv
                      simp only [Δ₀_alt_x_def, if_neg hv]
                    have Δ₀_alt_x_wt :
                        ∀ v (d : SMT.Dom), Δ₀_alt_x v = some d → ∀ τ, Stx.types.lookup v = some τ → d.snd.fst = τ := by
                      intro v d hv_eq τ hτ
                      simp only [Δ₀_alt_x_def] at hv_eq
                      by_cases h_used : v ∈ Stx.env.usedVars
                      · rw [if_pos h_used] at hv_eq
                        cases hΔ₀ : Δ₀_alt v with
                        | some d' =>
                          simp only [hΔ₀, Option.some.injEq] at hv_eq; subst hv_eq
                          exact Δ₀_alt_wt v d' hΔ₀ τ (AList.lookup_of_subset ctx_sub_St₈ hτ)
                        | none =>
                          simp only [hΔ₀] at hv_eq
                          split_ifs at hv_eq with h_mem
                          · -- v ∈ Stf.types; bridge Stf → ctx types
                            have ⟨τ', hτ'⟩ := Option.isSome_iff_exists.mp
                              (AList.lookup_isSome.mpr h_mem)
                            have : τ = τ' := by
                              have := AList.lookup_of_subset Stf_eq_Stx hτ'
                              rw [this] at hτ; exact (Option.some.inj hτ).symm
                            rw [this]
                            exact Δ'_alt_f_wt_out v d hv_eq τ' hτ'
                      · simp only [if_neg h_used] at hv_eq; exact absurd hv_eq nofun
                    -- Call x_ih_total
                    obtain ⟨Δ'_alt_x, hcov_alt_x, denT_x_alt, hext_alt_x,
                      Δ'_alt_x_none_out, Δ'_alt_x_wt_out, den_x_alt_enc, hRDom_x_alt, Δ'_alt_x_dom_out⟩ :=
                      x_ih_total Δ_alt Δ_fv_alt_x Δ₀_alt_x Δ₀_alt_x_ext Δ₀_alt_x_none Δ₀_alt_x_wt
                        X_alt hX_alt den_x_alt
                    -- === Step 3: Construct g_alt (constant lambda for alt values) ===
                    have ζ_α_isfunc_alt : ZFSet.IsFunc ⟦α⟧ᶻ ⟦α.toSMTType⟧ᶻ
                        (BType.canonicalIsoSMTType α) :=
                      (BType.canonicalIsoSMTType α).2.1
                    let T_alt_val : ZFSet :=
                      (@ZFSet.fapply F_alt _ _ ispfun_alt ⟨X_alt, X_alt_dom⟩).1
                    have T_alt_mem_dom_alt :
                        T_alt_val ∈ (BType.canonicalIsoSMTType α).1.Dom := by
                      rwa [ZFSet.is_func_dom_eq ζ_α_isfunc_alt]
                    let Tenc_alt_sub := ZFSet.fapply (BType.canonicalIsoSMTType α).1
                      (ZFSet.is_func_is_pfunc ζ_α_isfunc_alt) ⟨T_alt_val, T_alt_mem_dom_alt⟩
                    have hTenc_alt : Tenc_alt_sub.1 ∈ ⟦α.toSMTType⟧ᶻ :=
                      ZFSet.fapply_mem_range _ _
                    let some_Tenc_alt :=
                      ZFSet.Option.some (S := ⟦α.toSMTType⟧ᶻ) ⟨Tenc_alt_sub.1, hTenc_alt⟩
                    have hg_range_alt : ∀ z, z ∈ ⟦γ.toSMTType⟧ᶻ →
                        some_Tenc_alt.val ∈ ⟦α.toSMTType.option⟧ᶻ :=
                      fun _ _ => SetLike.coe_mem some_Tenc_alt
                    let g_alt := ZFSet.lambda ⟦γ.toSMTType⟧ᶻ ⟦α.toSMTType.option⟧ᶻ
                      (fun _ => some_Tenc_alt.val)
                    have hg_alt_mem :
                        g_alt ∈ ⟦SMTType.fun γ.toSMTType (α.toSMTType.option)⟧ᶻ := by
                      rw [SMTType.toZFSet]
                      exact ZFSet.mem_funs_of_lambda (fun hz => hg_range_alt _ hz)
                    let g_alt_dom : SMT.Dom :=
                      ⟨g_alt, .fun γ.toSMTType (.option α.toSMTType), hg_alt_mem⟩
                    -- === Step 4: Build Δ'_alt (match-first, no Function.update) ===
                    -- Key fact via axiom: Δ₀_alt f!! = none (f!! ∉ B.fv (.app f x))
                    have Δ₀_alt_f!!_none : Δ₀_alt f!! = none := by
                      by_contra h
                      have hf!!_fv : f!! ∈ B.fv (.app f x) :=
                        SMT.RenamingContext.ExtendsOnSourceFV.dom_sub_B_fv Δ₀_alt_ext f!! h
                      have hf!!_vars : f!! ∈ (B.Term.app f x).vars := by
                        simp only [B.Term.vars, List.mem_union_iff, B.bv, List.mem_append]
                        left; exact hf!!_fv
                      exact f!!_not_used (St₃_used_eq ▸ St₂_used_eq ▸ used_sub_St₁
                        (Stf_used_sub_Stx (St_used_sub_Stf (vars_used f!! hf!!_vars))))
                    set Δ'_alt : SMT.RenamingContext.Context :=
                      fun v => match Δ₀_alt v with
                        | some d => some d
                        | none => if v = f!! then some g_alt_dom else Δ'_alt_x v
                      with Δ'_alt_def
                    -- === Step 5: CoversFV ===
                    have hcov_alt :
                        RenamingContext.CoversFV Δ'_alt ((@ˢSMT.Term.var f!!) x_enc).the := by
                      intro w hw
                      rw [SMT.fv] at hw
                      rw [SMT.fv, List.mem_append] at hw
                      rcases hw with hw_f | hw_x
                      · rw [SMT.fv] at hw_f
                        simp only [List.mem_singleton] at hw_f; subst hw_f
                        simp only [Δ'_alt_def]; split <;> simp
                      · have hw_ne : w ≠ f!! := fun h => f!!_not_fv_x (h ▸ hw_x)
                        simp only [Δ'_alt_def]
                        cases h : Δ₀_alt w with
                        | some d => simp
                        | none => simp [hw_ne]; exact hcov_alt_x w hw_x
                    refine ⟨Δ'_alt, hcov_alt, ?_⟩
                    -- === Step 6: Extends, vanishing, denotation, RDom ===
                    -- g_alt properties
                    have g_alt_isFunc :
                        ZFSet.IsFunc ⟦γ.toSMTType⟧ᶻ ⟦α.toSMTType.option⟧ᶻ g_alt :=
                      ZFSet.lambda_isFunc (fun hz => hg_range_alt _ hz)
                    have g_alt_isPFunc :
                        g_alt.IsPFunc ⟦γ.toSMTType⟧ᶻ ⟦α.toSMTType.option⟧ᶻ :=
                      ZFSet.is_func_is_pfunc g_alt_isFunc
                    -- x_enc denotation under Δ'_alt_x
                    obtain ⟨Xenc_alt, σ_x_alt, hXenc_alt⟩ := denT_x_alt
                    obtain ⟨rfl, retract_x_alt⟩ := hRDom_x_alt
                    -- f_enc denotation under Δ'_alt_f
                    obtain ⟨Fenc_alt, σ_f_alt, hFenc_alt⟩ := denT_f_alt
                    obtain ⟨rfl, retract_f_alt⟩ := hRDom_f_alt
                    -- Xenc_alt ∈ g_alt.Dom
                    have Xenc_alt_in_dom : Xenc_alt ∈ g_alt.Dom := by
                      rw [ZFSet.is_func_dom_eq g_alt_isFunc]; exact hXenc_alt
                    -- fapply g_alt at Xenc_alt = some_Tenc_alt
                    have fapply_g_alt_val_eq :
                        (↑(ZFSet.fapply g_alt g_alt_isPFunc
                          ⟨Xenc_alt, Xenc_alt_in_dom⟩) : ZFSet) =
                        some_Tenc_alt.val := by
                      exact_mod_cast @ZFSet.fapply_lambda ⟦γ.toSMTType⟧ᶻ ⟦α.toSMTType.option⟧ᶻ
                        (fun _ => some_Tenc_alt.val) (fun hz => hg_range_alt _ hz)
                        Xenc_alt hXenc_alt
                    have fapply_g_alt_mem :
                        (↑(ZFSet.fapply g_alt g_alt_isPFunc
                          ⟨Xenc_alt, Xenc_alt_in_dom⟩) : ZFSet) ∈
                        ⟦SMTType.option α.toSMTType⟧ᶻ :=
                      (ZFSet.fapply g_alt g_alt_isPFunc ⟨Xenc_alt, Xenc_alt_in_dom⟩).2
                    -- Δ'_alt_x agrees with Δ'_alt on fv(x_enc)
                    -- (direction: Δ'_alt_x is Δ₁, Δ'_alt is Δ₂)
                    have Δ'_alt_agrees_x :
                        RenamingContext.AgreesOnFV Δ'_alt_x Δ'_alt x_enc := by
                      intro w hw
                      have hw_ne : w ≠ f!! := fun h => f!!_not_fv_x (h ▸ hw)
                      have hw_used : w ∈ Stx.env.usedVars := by
                        by_contra h_neg
                        have h_none := Δ'_alt_x_none_out w h_neg
                        have h_cov := hcov_alt_x w hw
                        simp [h_none] at h_cov
                      simp only [Δ'_alt_def]
                      cases h : Δ₀_alt w with
                      | some d =>
                        have hΔ₀_alt_x_w : Δ₀_alt_x w = some d := by
                          simp [Δ₀_alt_x_def, if_pos hw_used, h]
                        exact hext_alt_x hΔ₀_alt_x_w
                      | none => simp [hw_ne]
                    -- Δ'_alt covers fv(x_enc)
                    have hΔ'_alt_covers_x :
                        RenamingContext.CoversFV Δ'_alt x_enc := by
                      intro w hw
                      rw [← Δ'_alt_agrees_x hw]; exact hcov_alt_x w hw
                    -- x_enc denotation under Δ'_alt
                    have den_x_alt_Δ'_alt :
                        ⟦x_enc.abstract Δ'_alt hΔ'_alt_covers_x⟧ˢ =
                        some ⟨Xenc_alt, ⟨γ.toSMTType, hXenc_alt⟩⟩ := by
                      have heq := SMT.RenamingContext.denote_congr_of_agreesOnFV
                        (h1 := hcov_alt_x) (h2 := hΔ'_alt_covers_x) Δ'_alt_agrees_x
                      unfold SMT.RenamingContext.denote at heq
                      rw [← heq]; exact den_x_alt_enc
                    -- Compute .app denotation
                    have hcov_app_alt :
                        RenamingContext.CoversFV Δ'_alt ((@ˢSMT.Term.var f!!) x_enc) := by
                      intro w hw; simp only [SMT.fv] at hw
                      rw [List.mem_append] at hw
                      rcases hw with hw | hw
                      · simp only [SMT.fv, List.mem_singleton] at hw; subst hw
                        simp only [Δ'_alt_def]; split <;> simp
                      · exact hΔ'_alt_covers_x w hw
                    have den_app_alt :
                        ⟦((@ˢSMT.Term.var f!!) x_enc).abstract Δ'_alt hcov_app_alt⟧ˢ =
                        some ⟨↑(ZFSet.fapply g_alt g_alt_isPFunc
                          ⟨Xenc_alt, Xenc_alt_in_dom⟩),
                          ⟨.option α.toSMTType, fapply_g_alt_mem⟩⟩ := by
                      have Δ'_alt_f!! : Δ'_alt f!! = some g_alt_dom := by
                        simp [Δ'_alt_def, Δ₀_alt_f!!_none]
                      rw [SMT.Term.abstract.eq_def, SMT.denote,
                        SMT.Term.abstract.eq_def, SMT.denote, Option.pure_def,
                        Option.bind_eq_bind, Option.bind_some, den_x_alt_Δ'_alt]
                      simp only [Δ'_alt_f!!, Option.get_some,
                        g_alt_dom, Option.bind_some, dif_pos g_alt_isPFunc,
                        dif_pos Xenc_alt_in_dom, dite_true]
                    -- Compute the full .the denotation
                    have den_the_alt :
                        ⟦((@ˢSMT.Term.var f!!) x_enc).the.abstract Δ'_alt hcov_alt⟧ˢ =
                        some ⟨↑(ZFSet.Option.the SMTType.toZFSet_nonempty
                          ⟨↑(ZFSet.fapply g_alt g_alt_isPFunc
                            ⟨Xenc_alt, Xenc_alt_in_dom⟩), fapply_g_alt_mem⟩),
                          ⟨α.toSMTType, SetLike.coe_mem _⟩⟩ := by
                      rw [SMT.Term.abstract.eq_def, SMT.denote, den_app_alt]
                      rfl
                    -- The cast: fapply g_alt ... = some_Tenc_alt
                    have h_some_Tenc_alt_mem :
                        some_Tenc_alt.val ∈ ⟦SMTType.option α.toSMTType⟧ᶻ :=
                      SetLike.coe_mem some_Tenc_alt
                    have the_cast_alt :
                        (ZFSet.Option.the SMTType.toZFSet_nonempty
                          ⟨↑(ZFSet.fapply g_alt g_alt_isPFunc
                            ⟨Xenc_alt, Xenc_alt_in_dom⟩),
                           fapply_g_alt_mem⟩ : {x // x ∈ ⟦α.toSMTType⟧ᶻ}) =
                        ZFSet.Option.the SMTType.toZFSet_nonempty
                          ⟨some_Tenc_alt.val, h_some_Tenc_alt_mem⟩ := by
                      congr 1; exact Subtype.ext fapply_g_alt_val_eq
                    -- retract α (the(some(Tenc_alt))) = T_alt
                    have retract_Tenc_alt : retract α Tenc_alt_sub.1 = T_alt_val := by
                      exact retract_of_canonical α hT_alt
                    -- Witness
                    let denT_alt : SMT.Dom :=
                      ⟨↑(ZFSet.Option.the SMTType.toZFSet_nonempty
                        ⟨↑(ZFSet.fapply g_alt g_alt_isPFunc
                          ⟨Xenc_alt, Xenc_alt_in_dom⟩), fapply_g_alt_mem⟩),
                       ⟨α.toSMTType, SetLike.coe_mem _⟩⟩
                    refine ⟨denT_alt, ?_, ?_, ?_, den_the_alt, ?_, ?_⟩
                    · -- Extends Δ'_alt Δ₀_alt
                      intro v d hv
                      simp only [Δ'_alt_def, hv]
                    · -- ∀ v ∉ St₈.env.usedVars, Δ'_alt v = none
                      intro w hw
                      simp only [Δ'_alt_def]
                      have hwf : w ≠ f!! := fun h => hw (h ▸ f!!_in_St₈)
                      have h1 : Δ₀_alt w = none := Δ₀_alt_none_out w hw
                      simp only [h1, hwf, ite_false]
                      exact Δ'_alt_x_none_out w
                        (fun hmem => hw (Stx_used_sub_St₈ hmem))
                    · -- output wt: ∀ v d, Δ'_alt v = some d → ∀ τ, St₈.types.lookup v = some τ → d.snd.fst = τ
                      intro w d hv_eq τ hτ
                      simp only [Δ'_alt_def] at hv_eq
                      cases hΔ₀ : Δ₀_alt w with
                      | some d' =>
                        simp only [hΔ₀, Option.some.injEq] at hv_eq; subst hv_eq
                        exact Δ₀_alt_wt w d' hΔ₀ τ hτ
                      | none =>
                        simp only [hΔ₀] at hv_eq
                        split_ifs at hv_eq with h_eq
                        · -- w = f!!; d = g_alt_dom; need d.snd.fst = τ
                          -- where τ is from St₈.types.lookup f!! = some (γ.toSMTType.fun α.toSMTType.option)
                          simp only [Option.some.injEq] at hv_eq; subst hv_eq
                          simp only [g_alt_dom, h_eq]
                          rw [St₈_types_eq, St₇_types_eq] at hτ
                          have hf_ne_v : w ≠ v := by
                            rw [h_eq]; intro heq
                            exact v_not_used (heq ▸ St₆_used_eq ▸ List.mem_cons_of_mem _
                              (St₅_used_eq ▸ St₄_used_eq ▸ List.mem_cons_self))
                          have hf_ne_u : w ≠ u := by
                            rw [h_eq]; intro heq
                            exact u_not_used (heq ▸ St₅_used_eq ▸ St₄_used_eq ▸ List.mem_cons_self)
                          rw [AList.lookup_insert_ne hf_ne_v, St₆_types_eq,
                            AList.lookup_insert_ne hf_ne_u, St₅_types_eq, St₄_types_eq] at hτ
                          rw [h_eq, AList.lookup_insert] at hτ
                          exact Option.some.inj hτ
                        · -- w ≠ f!!; d = Δ'_alt_x w; use axiom for wt at St₈
                          -- Δ₀_alt_x satisfies ExtendsOnSourceFV x, Δ'_alt_x extends it
                          have hext_alt_x_src : RenamingContext.ExtendsOnSourceFV Δ'_alt_x Δ_alt x :=
                            RenamingContext.extendsOnSourceFV_of_extends hext_alt_x Δ₀_alt_x_ext
                          have typ_x_in_St₈ : St₈.types ⊢ˢ x_enc : γ.toSMTType :=
                            SMT.Typing.weakening ctx_sub_St₈ typ_x_enc
                          exact SMT.RenamingContext.ExtendsOnSourceFV.wt hext_alt_x_src
                            typ_x_in_St₈ w d hv_eq τ hτ
                    · -- RDom: ⟨T_alt, ⟨α, hT_alt⟩⟩ ≘ᶻ denT_alt
                      constructor
                      · rfl
                      · show retract α ↑(ZFSet.Option.the SMTType.toZFSet_nonempty
                          ⟨↑(ZFSet.fapply g_alt g_alt_isPFunc
                            ⟨Xenc_alt, Xenc_alt_in_dom⟩),
                            fapply_g_alt_mem⟩) = T_alt_val
                        rw [show (↑(ZFSet.Option.the SMTType.toZFSet_nonempty
                          ⟨↑(ZFSet.fapply g_alt g_alt_isPFunc
                            ⟨Xenc_alt, Xenc_alt_in_dom⟩), fapply_g_alt_mem⟩) :
                          ZFSet) =
                          ↑(ZFSet.Option.the SMTType.toZFSet_nonempty
                          ⟨some_Tenc_alt.val, h_some_Tenc_alt_mem⟩)
                          from congrArg Subtype.val the_cast_alt]
                        have hsub : (⟨some_Tenc_alt.val, h_some_Tenc_alt_mem⟩ :
                            ZFSet.Option ⟦α.toSMTType⟧ᶻ) = some_Tenc_alt :=
                          Subtype.ext rfl
                        unfold ZFSet.Option.the
                        have hne : some_Tenc_alt ≠ ZFSet.Option.none :=
                          ZFSet.Option.some_ne_none ⟨Tenc_alt_sub.val, hTenc_alt⟩
                        rw [hsub, dif_neg hne]
                        have hspec := Classical.choose_spec
                          (Or.resolve_left (ZFSet.Option.casesOn some_Tenc_alt) hne)
                        rw [ZFSet.Option.some.injEq] at hspec
                        rw [show (Classical.choose
                          (Or.resolve_left (ZFSet.Option.casesOn some_Tenc_alt) hne)) =
                          ⟨Tenc_alt_sub.val, hTenc_alt⟩ from hspec.symm]
                        exact retract_Tenc_alt
                    · -- dom_out: ∀ w, Δ'_alt w ≠ none → w ∈ St₈.types
                      intro w hw
                      simp only [Δ'_alt_def] at hw
                      cases hΔ : Δ₀_alt w with
                      | some d =>
                        exact fv_sub_typings (_root_.B.Typing.app typ_f typ_x)
                          (SMT.Typing.bool St₈.types true) w
                          (SMT.RenamingContext.ExtendsOnSourceFV.dom_sub_B_fv Δ₀_alt_ext w
                            (by rw [hΔ]; simp))
                      | none =>
                        simp only [hΔ] at hw
                        split_ifs at hw with h_eq
                        · -- w = f!!; show w ∈ St₈.types
                          rw [h_eq, St₈_types_eq, St₇_types_eq]
                          refine (AList.mem_insert _).mpr (Or.inr ?_)
                          rw [St₆_types_eq]
                          refine (AList.mem_insert _).mpr (Or.inr ?_)
                          rw [St₅_types_eq, St₄_types_eq]
                          exact (AList.mem_insert _).mpr (Or.inl rfl)
                        · -- w ≠ f!!: use Δ'_alt_x_dom_out
                          have h_x := Δ'_alt_x_dom_out w hw
                          rw [AList.mem_keys] at h_x ⊢
                          obtain ⟨s, hs, hs_eq⟩ := List.mem_map.mp h_x
                          rcases s with ⟨k, τ⟩
                          simp only at hs_eq
                          subst hs_eq
                          exact List.mem_map.mpr ⟨⟨k, τ⟩, ctx_sub_St₈ hs, rfl⟩
