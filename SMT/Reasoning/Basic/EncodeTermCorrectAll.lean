import SMT.Reasoning.Basic.CollectCaseHelpers
import SMT.Reasoning.Basic.AllCaseHelpers
import SMT.Reasoning.Basic.CastMembershipSpec
import SMT.Reasoning.Basic.EncodeTermStruct
import SMT.Reasoning.Axioms
import B.Reasoning.DenotationTotality

open Std.Do B SMT ZFSet

/-!
# Correctness of `encodeTerm` for the `all` constructor

The all case encodes `∀ vs ∈ D . P` as an SMT term of type `.bool`, using the
SMT-level `forall` binder. Structurally analogous to `collect_case` but produces
a universally-quantified formula rather than a characteristic function.
-/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1024 in
theorem encodeTerm_spec.all_case.{u} (fv_sub_typings : B.FvSubTypings)
  (vs : List B.𝒱) (D P : B.Term)
  (D_ih :
    ∀ (E : B.Env) {Λ : SMT.TypeContext} {α : BType},
      E.context ⊢ᴮ D : α →
        ∀ {«Δ» : B.RenamingContext.Context} (Δ_fv : ∀ v ∈ B.fv D, («Δ» v).isSome = true)
          {Δ₀ : SMT.RenamingContext.Context},
          RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» D →
            ∀ {used : List SMT.𝒱},
              (∀ v ∉ used, Δ₀ v = none) →
                ∀ {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ},
                  ⟦D.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩ →
                    (∀ v ∈ D.vars, v ∈ used) →
                      (∀ v ∈ D.vars, v ∈ Λ → v ∈ E.context) →
                      ((B.bv D).Nodup) →
                        B.RenamingContext.RespectsTypeContextOnFV (B.RenamingContext.toSMT «Δ») Λ D →
                        (∀ v ∈ B.fv D, v ∈ Λ) →
                        ∀ {n : ℕ},
                          ⦃fun x =>
                            match x with
                            | { env := E0, types := Λ' } =>
                              ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
                            encodeTerm D E ⦃PostCond.mayThrow fun x x_1 =>
                              match x with
                              | (t', σ) =>
                                match x_1 with
                                | { env := E', types := Γ' } =>
                                  ⌜used ⊆ E'.usedVars ∧
                                      Λ ⊆ Γ' ∧
                                        AList.keys Γ' ⊆ E'.usedVars ∧
                                          CoversUsedVars E'.usedVars D ∧
                                            σ = α.toSMTType ∧
                                              Γ' ⊢ˢ t' : σ ∧
                                                (∀ v ∈ used, v ∉ Λ → v ∉ B.Term.vars D → v ∉ Γ') ∧
                                                  ∃ Δ',
                                                    ∃ (Δ'_covers : RenamingContext.CoversFV Δ' t'),
                                                      RenamingContext.Extends Δ' Δ₀ ∧
                                                        RenamingContext.ExtendsOnSourceFV Δ' «Δ» D ∧
                                                          (∀ v ∉ E'.usedVars, Δ' v = none) ∧
                                                            ∃ denT',
                                                              ⟦t'.abstract Δ' Δ'_covers⟧ˢ = some denT' ∧
                                                                ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT' ∧
                                                                  ∀ (Δ_alt : B.RenamingContext.Context)
                                                                    (Δ_fv_alt : ∀ v ∈ B.fv D, (Δ_alt v).isSome = true)
                                                                    (Δ₀_alt : SMT.RenamingContext.Context),
                                                                    RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt D →
                                                                      (∀ v ∉ E'.usedVars, Δ₀_alt v = none) →
                                                                      (∀ v (d : SMT.Dom), Δ₀_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) →
                                                                        ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦α⟧ᶻ),
                                                                          ⟦D.abstract Δ_alt Δ_fv_alt⟧ᴮ =
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
  (P_ih :
    ∀ (E : B.Env) {Λ : SMT.TypeContext} {α : BType},
      E.context ⊢ᴮ P : α →
        ∀ {«Δ» : B.RenamingContext.Context} (Δ_fv : ∀ v ∈ B.fv P, («Δ» v).isSome = true)
          {Δ₀ : SMT.RenamingContext.Context},
          RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» P →
            ∀ {used : List SMT.𝒱},
              (∀ v ∉ used, Δ₀ v = none) →
                ∀ {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ},
                  ⟦P.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩ →
                    (∀ v ∈ P.vars, v ∈ used) →
                      (∀ v ∈ P.vars, v ∈ Λ → v ∈ E.context) →
                      ((B.bv P).Nodup) →
                        B.RenamingContext.RespectsTypeContextOnFV (B.RenamingContext.toSMT «Δ») Λ P →
                        (∀ v ∈ B.fv P, v ∈ Λ) →
                        ∀ {n : ℕ},
                          ⦃fun x =>
                            match x with
                            | { env := E0, types := Λ' } =>
                              ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
                            encodeTerm P E ⦃PostCond.mayThrow fun x x_1 =>
                              match x with
                              | (t', σ) =>
                                match x_1 with
                                | { env := E', types := Γ' } =>
                                  ⌜used ⊆ E'.usedVars ∧
                                      Λ ⊆ Γ' ∧
                                        AList.keys Γ' ⊆ E'.usedVars ∧
                                          CoversUsedVars E'.usedVars P ∧
                                            σ = α.toSMTType ∧
                                              Γ' ⊢ˢ t' : σ ∧
                                                (∀ v ∈ used, v ∉ Λ → v ∉ B.Term.vars P → v ∉ Γ') ∧
                                                  ∃ Δ',
                                                    ∃ (Δ'_covers : RenamingContext.CoversFV Δ' t'),
                                                      RenamingContext.Extends Δ' Δ₀ ∧
                                                        RenamingContext.ExtendsOnSourceFV Δ' «Δ» P ∧
                                                          (∀ v ∉ E'.usedVars, Δ' v = none) ∧
                                                            ∃ denT',
                                                              ⟦t'.abstract Δ' Δ'_covers⟧ˢ = some denT' ∧
                                                                ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT' ∧
                                                                  ∀ (Δ_alt : B.RenamingContext.Context)
                                                                    (Δ_fv_alt : ∀ v ∈ B.fv P, (Δ_alt v).isSome = true)
                                                                    (Δ₀_alt : SMT.RenamingContext.Context),
                                                                    RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt P →
                                                                      (∀ v ∉ E'.usedVars, Δ₀_alt v = none) →
                                                                      (∀ v (d : SMT.Dom), Δ₀_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) →
                                                                        ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦α⟧ᶻ),
                                                                          ⟦P.abstract Δ_alt Δ_fv_alt⟧ᴮ =
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
  (E : B.Env) {Λ : SMT.TypeContext} {α : BType} (typ_t : E.context ⊢ᴮ Term.all vs D P : α)
  {«Δ» : B.RenamingContext.Context} (Δ_fv : ∀ v ∈ B.fv (Term.all vs D P), («Δ» v).isSome = true)
  {Δ₀ : SMT.RenamingContext.Context} (Δ₀_ext : RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» (Term.all vs D P))
  {used : List SMT.𝒱} (Δ₀_none_out : ∀ v ∉ used, Δ₀ v = none)
  {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ}
  (den_t : ⟦(Term.all vs D P).abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩)
  (vars_used : ∀ v ∈ (Term.all vs D P).vars, v ∈ used)
  (Λ_inv : ∀ v ∈ (Term.all vs D P).vars, v ∈ Λ → v ∈ E.context)
  (bv_nodup : (B.bv (Term.all vs D P)).Nodup)
  (respects : B.RenamingContext.RespectsTypeContextOnFV (B.RenamingContext.toSMT «Δ») Λ ((Term.all vs D P)))
  (fv_in_Λ : ∀ v ∈ B.fv ((Term.all vs D P)), v ∈ Λ)
  -- Path-A R3e: SPLIT existential_witness_hasflag into two hypotheses for
  -- finer-grained discharge. The original bundled witness packaged three
  -- conjuncts (existence + RDom + Δ-universal totality). R3e separates
  -- existence + RDom (semantically tied to the SAME `denT'`) from the
  -- Δ-universal totality clause (independent of `denT'`).
  --
  -- Future work can discharge each independently:
  -- * `existence_rdom_witness_hasflag` is dischargeable inline using
  --   `forallVal_isSome_helper` (existence) + `retract_forallVal_eq_sInter_sep_hasflag`
  --   (RDom), once the use site swaps `castMembership_spec` →
  --   `castMembership_branch2_spec` for the Δ-universal adequacy `hbridge` needs.
  -- * `totality_witness_hasflag` is the deeper ~1500-line Δ-universal totality
  --   construction (deferred to a follow-up round).
  --
  -- Both hypotheses are parameterized over the variables that vary at the use
  -- site (`vs`, `D`, `P`, `Δ`, `T`, `hT`, `used`, `Λ`, `Δ₀`, `zs`, `τs`,
  -- `imp_body`, `Δ_ctx`, `hcov_forall`).
  --
  -- HISTORICAL NOTE (audit follow-up): three companion clauses were previously
  -- declared on this signature but never consumed in the proof body — they
  -- have been removed: (1) `cast_preimage_witness_hasflag` (R3e2-split),
  -- (2) `pfun_inv` (R1 E.po-functional invariant on flagged binders), and
  -- (3) `hzmem_iff_witness_hasflag` (R3e2-split Δ-universal adequacy clause
  -- feeding `hbridge_hasflag`). These were intended as building blocks for
  -- future inline-discharge of `existence_rdom_witness_hasflag`, but the
  -- present proof body only consumes the two witnesses below. They can be
  -- reintroduced when `existence_rdom_witness_hasflag` is actually
  -- discharged inline via composition with `case_b_preimage_of_pfun_inv`,
  -- `hbridge_hasflag`, `forallVal_isSome_helper`, and
  -- `retract_forallVal_eq_sInter_sep_hasflag`.
  (existence_rdom_witness_hasflag :
    ∀ {zs : List SMT.𝒱} {τs : List SMTType}
      {imp_body : SMT.Term}
      {Δ_ctx : SMT.RenamingContext.Context.{u}}
      (hcov_forall : SMT.RenamingContext.CoversFV Δ_ctx
        (SMT.Term.forall zs τs imp_body))
      (T' : ZFSet.{u}) (hT' : T' ∈ ⟦BType.bool⟧ᶻ),
      ∃ denT' : SMT.Dom.{u},
        ⟦(SMT.Term.forall zs τs imp_body).abstract Δ_ctx hcov_forall⟧ˢ
          = some denT' ∧
        (⟨T', ⟨BType.bool, hT'⟩⟩ : B.Dom) ≘ᶻ denT')
  (totality_witness_hasflag :
    ∀ {zs : List SMT.𝒱} {τs : List SMTType}
      {imp_body : SMT.Term}
      {Δ_ctx : SMT.RenamingContext.Context.{u}}
      (_hcov_forall : SMT.RenamingContext.CoversFV Δ_ctx
        (SMT.Term.forall zs τs imp_body))
      {used' : List SMT.𝒱} {Λ' : SMT.TypeContext},
      ∀ (Δ_alt : B.RenamingContext.Context)
        (Δ_fv_alt : ∀ v ∈ B.fv (B.Term.all vs D P), (Δ_alt v).isSome = true)
        (Δ₀_alt : SMT.RenamingContext.Context.{u}),
        SMT.RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt (B.Term.all vs D P) →
          (∀ v ∉ used', Δ₀_alt v = none) →
            (∀ (v : SMT.𝒱) (d : SMT.Dom.{u}),
                Δ₀_alt v = some d →
                  ∀ (τ_v : SMTType), AList.lookup v Λ' = some τ_v →
                    d.snd.fst = τ_v) →
              ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦BType.bool⟧ᶻ),
                ⟦(B.Term.all vs D P).abstract Δ_alt Δ_fv_alt⟧ᴮ =
                    some ⟨T_alt, ⟨BType.bool, hT_alt⟩⟩ →
                  ∃ Δ'_alt : SMT.RenamingContext.Context.{u},
                    ∃ (hcov_alt : SMT.RenamingContext.CoversFV Δ'_alt
                        (SMT.Term.forall zs τs imp_body)),
                      ∃ denT_alt : SMT.Dom.{u},
                        SMT.RenamingContext.Extends Δ'_alt Δ₀_alt ∧
                          (∀ v ∉ used', Δ'_alt v = none) ∧
                            (∀ (v : SMT.𝒱) (d : SMT.Dom.{u}),
                                Δ'_alt v = some d →
                                  ∀ (τ_v : SMTType), AList.lookup v Λ' = some τ_v →
                                    d.snd.fst = τ_v) ∧
                              ⟦(SMT.Term.forall zs τs imp_body).abstract Δ'_alt
                                  hcov_alt⟧ˢ = some denT_alt ∧
                                (⟨T_alt, ⟨BType.bool, hT_alt⟩⟩ : B.Dom)
                                  ≘ᶻ denT_alt ∧
                                  ∀ (v : SMT.𝒱), Δ'_alt v ≠ none → v ∈ Λ')
  {n : ℕ} :
  ⦃fun x =>
    match x with
    | { env := E0, types := Λ' } => ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
    encodeTerm (Term.all vs D P) E ⦃PostCond.mayThrow fun x x_1 =>
      match x with
      | (t', σ) =>
        match x_1 with
        | { env := E', types := Γ' } =>
          ⌜used ⊆ E'.usedVars ∧
              Λ ⊆ Γ' ∧
                AList.keys Γ' ⊆ E'.usedVars ∧
                  CoversUsedVars E'.usedVars (Term.all vs D P) ∧
                    σ = α.toSMTType ∧
                      Γ' ⊢ˢ t' : σ ∧
                        (∀ v ∈ used, v ∉ Λ → v ∉ B.Term.vars (Term.all vs D P) → v ∉ Γ') ∧
                          ∃ Δ',
                            ∃ (Δ'_covers : RenamingContext.CoversFV Δ' t'),
                              RenamingContext.Extends Δ' Δ₀ ∧
                                RenamingContext.ExtendsOnSourceFV Δ' «Δ» (Term.all vs D P) ∧
                                  (∀ v ∉ E'.usedVars, Δ' v = none) ∧
                                    ∃ denT',
                                      ⟦t'.abstract Δ' Δ'_covers⟧ˢ = some denT' ∧
                                        ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT' ∧
                                          ∀ (Δ_alt : B.RenamingContext.Context)
                                            (Δ_fv_alt : ∀ v ∈ B.fv (Term.all vs D P), (Δ_alt v).isSome = true)
                                            (Δ₀_alt : SMT.RenamingContext.Context),
                                            RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt (Term.all vs D P) →
                                              (∀ v ∉ E'.usedVars, Δ₀_alt v = none) →
                                              (∀ v (d : SMT.Dom), Δ₀_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) →
                                                ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦α⟧ᶻ),
                                                  ⟦(Term.all vs D P).abstract Δ_alt Δ_fv_alt⟧ᴮ =
                                                      some ⟨T_alt, ⟨α, hT_alt⟩⟩ →
                                                    ∃ Δ'_alt,
                                                      ∃ (hcov_alt : RenamingContext.CoversFV Δ'_alt t'),
                                                        ∃ denT_alt,
                                                          RenamingContext.Extends Δ'_alt Δ₀_alt ∧
                                                            (∀ v ∉ E'.usedVars, Δ'_alt v = none) ∧
                                                              (∀ v (d : SMT.Dom), Δ'_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) ∧
                                                            ⟦t'.abstract Δ'_alt hcov_alt⟧ˢ = some denT_alt ∧
                                                              ⟨T_alt, ⟨α, hT_alt⟩⟩ ≘ᶻ denT_alt ∧
                                                                (∀ v, Δ'_alt v ≠ none → v ∈ Γ')⌝⦄ := by
  mintro pre ∀St₀
  mpure pre
  obtain ⟨rfl, rfl, St₀_sub, St₀_used_eq⟩ := pre
  obtain ⟨α_eq, vs_nemp, αs, Ds, vs_αs_len, vs_Ds_len, D_eq, vs_nodup, typDs, typP, vs_Γ_disj⟩ :=
    Typing.allE typ_t
  subst α_eq
  have Δ_fv_D : ∀ v ∈ B.fv D, («Δ» v).isSome := fun v hv =>
    Δ_fv v (fv.mem_all (.inl hv))
  have Δ₀_ext_D : RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» D :=
    RenamingContext.extendsOnSourceFV_of_fv_subset
      (hsub := fun v hv => fv.mem_all (.inl hv)) Δ₀_ext
  set τ := αs.reduce (· ×ᴮ ·) (by simpa [vs_αs_len, ← List.length_pos_iff] using vs_nemp)
    with τ_def
  have typ_D : E.context ⊢ᴮ D : .set τ := by
    rw [D_eq]
    exact typing_reduce_cprod E.context _ _ typDs
      (by simpa [vs_Ds_len, ← List.length_pos_iff] using vs_nemp)
      (by simpa [vs_αs_len, ← List.length_pos_iff] using vs_nemp)
  have vars_used_D : ∀ v ∈ D.vars, v ∈ used := by
    intro v hv
    apply vars_used v
    simp [B.Term.vars, B.fv, B.bv, List.mem_append, List.mem_removeAll_iff] at hv ⊢
    rcases hv with hv | hv
    · left; left; exact hv
    · right; right; left; exact hv
  have vars_used_vs : ∀ v ∈ vs, v ∈ used := by
    intro v hv
    apply vars_used v
    simp [B.Term.vars, B.fv, B.bv, List.mem_append, List.mem_removeAll_iff] at hv ⊢
    right; left; exact hv
  have vars_used_P : ∀ v ∈ P.vars, v ∈ used := by
    intro v hv
    apply vars_used v
    simp only [Term.vars, List.mem_union_iff, B.fv, B.bv, List.append_assoc, List.mem_append,
      List.mem_removeAll_iff] at hv ⊢
    by_cases v_in_vs : v ∈ vs
    · right; left; exact v_in_vs
    · rcases hv with hv | hv
      · left; right; exact ⟨hv, v_in_vs⟩
      · right; right; right; exact hv
  -- Extract D denotation from den_t
  have denote_all_inv := den_t
  simp only [B.Term.abstract] at denote_all_inv
  unfold B.denote at denote_all_inv
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at denote_all_inv
  obtain ⟨⟨𝒟', τ_D', h𝒟'⟩, den_D', rest_all⟩ := denote_all_inv
  have den_D_eq : ⟦D.abstract «Δ» Δ_fv_D⟧ᴮ = some ⟨𝒟', ⟨τ_D', h𝒟'⟩⟩ := by
    convert den_D' using 2
  have rfl_τ' : τ_D' = .set τ := by
    have h_wt := denote_welltyped_eq
      (t := D.abstract «Δ» Δ_fv_D)
      ⟨_, WFTC.of_abstract, .set τ, by convert Typing.of_abstract Δ_fv_D typ_D⟩
      den_D_eq
    exact h_wt.symm
  subst rfl_τ'
  obtain ⟨𝒟, h𝒟, den_D⟩ : ∃ (𝒟 : ZFSet) (h𝒟 : 𝒟 ∈ ⟦τ.set⟧ᶻ),
      ⟦D.abstract «Δ» Δ_fv_D⟧ᴮ = some ⟨𝒟, ⟨τ.set, h𝒟⟩⟩ :=
    ⟨𝒟', h𝒟', den_D_eq⟩
  rw [encodeTerm]
  have St₀_types_sub_E_ctx_on_D_vars : ∀ v ∈ D.vars, v ∈ St₀.types → v ∈ E.context := by
    intro v v_in_D_vars v_in_St₀_types
    apply Λ_inv v _ v_in_St₀_types
    simp only [Term.vars, List.mem_union_iff, B.fv, B.bv, List.append_assoc, List.mem_append,
      List.mem_removeAll_iff] at v_in_D_vars ⊢
    rcases v_in_D_vars with hv | hv
    · left; left; exact hv
    · right; right; left; exact hv
  have hD_bv_nodup : (B.bv D).Nodup := by
    have h := bv_nodup
    simp only [B.bv] at h
    rw [List.nodup_append, List.nodup_append] at h
    exact h.1.2.1
  have hP_bv_nodup : (B.bv P).Nodup := by
    have h := bv_nodup
    simp only [B.bv] at h
    rw [List.nodup_append] at h
    exact h.2.1
  mspec D_ih (E := E) (Λ := St₀.types) (α := .set τ) typ_D
      («Δ» := «Δ») Δ_fv_D
      (Δ₀ := Δ₀) Δ₀_ext_D (used := used) Δ₀_none_out (T := 𝒟) (hT := h𝒟)
      den_D vars_used_D (n := St₀.env.freshvarsc)
      St₀_types_sub_E_ctx_on_D_vars
      hD_bv_nodup
      (respects.mono_fv (fun v hv => by rw [B.fv]; exact List.mem_append_left _ hv))
      (fun v hv => fv_in_Λ v (by rw [B.fv]; exact List.mem_append_left _ hv))
  clear D_ih
  rename_i out_D
  obtain ⟨D_enc, τD⟩ := out_D
  mrename_i pre
  mintro ∀St₁
  mpure pre
  obtain ⟨used_sub_St₁, St₀_sub_St₁, St₁_keys_sub, covers_D, rfl, typ_D_enc,
    D_preserves_types,
    Δ_D, Δ_D_covers, Δ_D_extends, Δ_D_src_ext, Δ_D_none, denD', den_D_enc, D_RDom⟩ := pre
  have Δ_D_wt : ∀ v (d : SMT.Dom), Δ_D v = some d →
      ∀ τ_v, St₁.types.lookup v = some τ_v → d.snd.fst = τ_v :=
    SMT.RenamingContext.ExtendsOnSourceFV.wt Δ_D_src_ext typ_D_enc
  have Δ_D_dom : ∀ v, Δ_D v ≠ none → v ∈ St₁.types := fun v hv =>
    fv_sub_typings typ_D typ_D_enc v
      (SMT.RenamingContext.ExtendsOnSourceFV.dom_sub_B_fv Δ_D_src_ext v hv)
  simp only [BType.toSMTType] at *
  have αs_nemp : αs ≠ [] := by simpa [vs_αs_len, ← List.length_pos_iff] using vs_nemp
  have τ_hasArity : τ.hasArity vs.length := by
    rw [τ_def, List.reduce]
    have h_len : αs.tail.length + 1 = vs.length := by
      rw [List.length_tail, vs_αs_len]
      have := List.length_pos_of_ne_nil αs_nemp
      omega
    convert BType.hasArity_of_foldl (α := αs.head αs_nemp) (αs := αs.tail) using 1
    exact h_len.symm
  have hlen_eq : vs.length = (τ.toSMTType.fromProdl (vs.length - 1)).length :=
    (fromProdl_length_of_hasArity τ_hasArity).symm
  rw [dif_pos hlen_eq]
  by_cases h_noflag : ∀ i (hi : i < (τ.toSMTType.fromProdl (vs.length - 1)).length),
      vs[i]'(by rw [hlen_eq]; exact hi) ∉ E.flags
  swap
  · -- HAS-FLAG BRANCH
    mspec SMT.mapFinIdxM_all_body_spec vs E.flags
      (τ.toSMTType.fromProdl (vs.length - 1)) hlen_eq
    rename_i τs
    mrename_i pre
    mintro ∀St₂
    mpure pre
    obtain ⟨St₂_types, St₂_fvc, St₂_used, τs_len_eq, τs_flag_rel⟩ := pre
    have vs_τs_len : vs.length = τs.length := by rw [τs_len_eq]; exact hlen_eq
    mspec SMT.addToContext_forIn_spec (pairs := vs.zip τs)
    mrename_i pre
    mintro ∀St₃
    mpure pre
    obtain ⟨St₃_types, St₃_fvc, St₃_used⟩ := pre
    set E' : B.Env := { E with context := vs.zipToAList αs ∪ E.context }
    conv in encodeTerm P E => rw [encodeTerm_env_irrel P E E' rfl]
    have St₁_sub_St₃_used : St₁.env.usedVars ⊆ St₃.env.usedVars := by
      rw [St₃_used, St₂_used]
      intro v hv
      suffices ∀ (pairs : List (SMT.𝒱 × SMTType)) (acc : List SMT.𝒱),
          v ∈ acc → v ∈ pairs.foldl (fun used p => p.1 :: used) acc by
        exact this _ _ hv
      intro pairs
      induction pairs with
      | nil => intro acc hmem; exact hmem
      | cons p ps ih => intro acc hmem; exact ih _ (List.mem_cons_of_mem _ hmem)
    have Δ_D_none_St₃ : ∀ v ∉ St₃.env.usedVars, Δ_D v = none :=
      fun v hv => Δ_D_none v (fun hmem => hv (St₁_sub_St₃_used hmem))
    have St₃_keys_sub : AList.keys St₃.types ⊆ St₃.env.usedVars := by
      rw [St₃_types, St₃_used, St₂_types, St₂_used]
      suffices h : ∀ (l : List (SMT.𝒱 × SMTType)) (Γ : SMT.TypeContext) (used : List SMT.𝒱),
          AList.keys Γ ⊆ used →
          AList.keys (l.foldl (fun Γ p => Γ.insert p.1 p.2) Γ) ⊆
            l.foldl (fun used p => p.1 :: used) used from
        h _ _ _ St₁_keys_sub
      intro l; induction l with
      | nil => intro Γ used h; exact h
      | cons p ps ih =>
        intro Γ used h; simp only [List.foldl_cons]
        apply ih; intro v hv
        simp only [AList.keys_insert] at hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (h (List.mem_of_mem_erase hv))
    have vars_used_P_St₃ : ∀ v ∈ P.vars, v ∈ St₃.env.usedVars :=
      fun v hv => St₁_sub_St₃_used (used_sub_St₁ (vars_used_P v hv))
    have St₃_types_sub_E'_ctx_on_P_vars : ∀ v ∈ P.vars, v ∈ St₃.types → v ∈ E'.context := by
      intro v v_in_P_vars v_in_St₃_types
      simp [E']
      by_cases v_in_vs : v ∈ vs
      · left
        exact AList.mem_zipToAList_of_mem vs_nodup vs_αs_len v_in_vs
      · right
        have v_in_St₁ : v ∈ St₁.types := by
          rw [St₃_types, St₂_types] at v_in_St₃_types
          exact AList.mem_of_mem_foldl_insert' v_in_St₃_types (by
            intro h
            rw [List.mem_map] at h
            obtain ⟨⟨a, b⟩, hab, rfl⟩ := h
            exact v_in_vs (List.of_mem_zip hab).1)
        have v_used : v ∈ used := vars_used_P v v_in_P_vars
        by_cases v_St₀ : v ∈ St₀.types
        · have v_all : v ∈ (Term.all vs D P).vars := by
            unfold B.Term.vars at v_in_P_vars ⊢
            rw [List.mem_union_iff]
            rcases List.mem_union_iff.mp v_in_P_vars with h_fv | h_bv
            · left; simp only [B.fv, List.mem_append]
              right
              unfold List.removeAll; rw [List.mem_filter]
              exact ⟨h_fv, by simp [v_in_vs]⟩
            · right; simp only [B.bv, List.mem_append]
              right; exact h_bv
          exact Λ_inv v v_all v_St₀
        · have v_vars_D : v ∈ B.Term.vars D := by
            by_contra h
            exact absurd v_in_St₁ (D_preserves_types v v_used v_St₀ h)
          rcases B.Term.mem_vars_iff.mp v_vars_D with h | h
          · exact AList.lookup_isSome.mp (B.Typing.mem_context_of_mem_fv typ_D h)
          · rcases B.Term.mem_vars_iff.mp v_in_P_vars with hv_fv_P | hv_bv_P
            · have h_in_E' : ((vs.zipToAList αs ∪ E.context).lookup v).isSome :=
                B.Typing.mem_context_of_mem_fv typP hv_fv_P
              have h_in_union : v ∈ vs.zipToAList αs ∪ E.context :=
                AList.lookup_isSome.mp h_in_E'
              rcases AList.mem_union.mp h_in_union with h_vs_in | h_E_in
              · exact absurd (AList.mem_zipToAList h_vs_in) v_in_vs
              · exact h_E_in
            · exfalso
              have hbn := bv_nodup
              simp only [B.bv] at hbn
              rw [List.nodup_append, List.nodup_append] at hbn
              have hin : v ∈ vs ++ B.bv D := List.mem_append.mpr (Or.inr h)
              exact hbn.2.2 v hin v hv_bv_P rfl
    rw [dif_pos τ_hasArity] at rest_all
    split_ifs at rest_all with den_P_cond typP_det_cond h𝒟_empty
    rotate_left
    · -- has-flag NONEMPTY case
      have 𝒟'_nonempty : 𝒟'.Nonempty := 𝒟'.eq_empty_or_nonempty.resolve_left h𝒟_empty
      obtain ⟨x_raw, hx_raw⟩ := 𝒟'_nonempty
      have 𝒟'_sub_τ : 𝒟' ⊆ ⟦τ⟧ᶻ := by rwa [BType.toZFSet, ZFSet.mem_powerset] at h𝒟'
      have hx_raw_mem : x_raw ∈ ⟦τ⟧ᶻ := 𝒟'_sub_τ hx_raw
      have hx_raw_arity : x_raw.hasArity vs.length :=
        hasArity_of_mem_toZFSet τ_hasArity hx_raw_mem
      let x_fin : Fin vs.length → B.Dom := fun i =>
        ⟨x_raw.get vs.length i, τ.get vs.length i,
         get_mem_type_of_isTuple hx_raw_arity τ_hasArity hx_raw_mem⟩
      set Δ_ext : B.RenamingContext.Context :=
        Function.updates «Δ» vs (List.ofFn fun i => some (x_fin i)) with Δ_ext_def
      have Δ_fv_P := Δ_fv_P_helper vs_nodup Δ_ext_def D P Δ_fv
      have hx_fin_in_𝒟 : ZFSet.ofFinDom x_fin ∈ 𝒟' := by
        have h_ofFinDom_eq : ZFSet.ofFinDom x_fin = x_raw :=
          ZFSet.ofFinDom_get (List.length_pos_iff.mpr vs_nemp)
            (fun _ => get_mem_type_of_isTuple hx_raw_arity τ_hasArity hx_raw_mem)
            hx_raw_arity τ_hasArity
        exact h_ofFinDom_eq ▸ hx_raw
      have hx_fin_typ : ∀ i, (x_fin i).snd.fst = τ.get vs.length i ∧
          (x_fin i).fst ∈ ⟦τ.get vs.length i⟧ᶻ :=
        fun i => ⟨rfl, (x_fin i).snd.snd⟩
      have hP_isSome : ⟦(B.Term.abstract.go P vs «Δ» _).uncurry x_fin⟧ᴮ.isSome = true :=
        den_P_cond hx_fin_typ hx_fin_in_𝒟
      obtain ⟨⟨P_val, P_ty, hP_val⟩, hP_den_raw⟩ := Option.isSome_iff_exists.mp hP_isSome
      have hP_den : ⟦P.abstract Δ_ext Δ_fv_P⟧ᴮ = some ⟨P_val, P_ty, hP_val⟩ := by
        rw [← denote_term_abstract_go_eq_term_abstract vs_nodup vs_nemp x_fin Δ_fv_P]
        exact hP_den_raw
      have hP_ty_bool : P_ty = BType.bool := by
        exact (denote_welltyped_eq
          (t := P.abstract Δ_ext Δ_fv_P)
          ⟨_, WFTC.of_abstract, .bool, by convert Typing.of_abstract Δ_fv_P typP⟩
          hP_den).symm
      subst hP_ty_bool
      set Δ_D_ext : SMT.RenamingContext.Context :=
        Function.updates Δ_D vs (List.ofFn fun (i : Fin vs.length) =>
          B.RenamingContext.toSMT Δ_ext vs[i])
        with Δ_D_ext_def
      have Δ_D_ext_none_St₃ : ∀ v ∉ St₃.env.usedVars, Δ_D_ext v = none :=
        Δ_D_ext_none_helper (ΔDD := Δ_D) (ΔDDext := Δ_D_ext)
          (vs := vs) (vs_nodup := vs_nodup) (vs_τs_len := vs_τs_len)
          (used0 := St₁.env.usedVars) (used1 := St₂.env.usedVars)
          (used2 := St₃.env.usedVars)
          (St_used_def := St₃_used) (used1_eq_used0 := St₂_used)
          (ΔDDext_def := Δ_D_ext_def) (ΔDD_none_outside := Δ_D_none_St₃)
      have Δ₀_ext_P : RenamingContext.ExtendsOnSourceFV Δ_D_ext Δ_ext P :=
        Δ₀_ext_P_helper vs_nodup Δ_ext_def Δ_D_ext_def D P
          (lift := fun hv => Δ_D_extends (Δ₀_ext hv))
      mspec Std.Do.Spec.get_StateT
      mspec Std.Do.Spec.get_StateT
      mspec Std.Do.Spec.get_StateT
      mspec encodeTerm_struct (E := E') (Λ := St₃.types) («Δ» := Δ_ext) (Δ₀ := Δ_D_ext)
        Δ₀_ext_P (used := St₃.env.usedVars) Δ_D_ext_none_St₃ vars_used_P_St₃ hP_bv_nodup
        (n := St₃.env.freshvarsc)
      rename_i out_P
      obtain ⟨P_enc, σP⟩ := out_P
      mrename_i pre
      mintro ∀St₄
      mpure pre
      obtain ⟨St₃_sub_St₄, St₃_sub_St₄_types, St₄_keys_sub, covers_P, P_fv_sub,
        P_preserves_types,
        Δ_P, Δ_P_covers, Δ_P_extends, Δ_P_src_ext, Δ_P_none⟩ := pre
      split
      rename_i heq
      injection heq with hPe hσe
      subst hσe
      subst hPe
      simp only [BType.toSMTType] at *
      mspec SMT.freshVarList_spec τs
      rename_i zs
      mrename_i pre
      mintro ∀St₅
      mpure pre
      obtain ⟨zs_len, zs_nodup, zs_not_used, zs_not_types, St₅_fvc, St₅_used, St₅_types⟩ := pre
      have zs_nemp : zs ≠ [] := zs_nemp_helper zs_len vs_τs_len vs_nemp
      have zs_typing := zs_typing_helper (St₅types := St₅.types) zs_nodup zs_len St₅_types
      have toPairl_typ : St₅.types ⊢ˢ (zs.map SMT.Term.var).toPairl : τs.toProdl :=
        toPairl_typ_helper zs_len zs_nemp zs_typing
      obtain ⟨vs_not_D_fv, vs_disj_St₁⟩ :=
        vs_disj_St₁_helper (P := P) typ_D vs_Γ_disj Λ_inv vars_used_vs D_preserves_types bv_nodup
      obtain ⟨St₁_sub_St₂_types, St₂_sub_St₃_types, St₄_sub_St₅_types, St₁_sub_St₅_types⟩ :=
        St_chain_helper vs_nodup zs_nodup St₂_types St₃_types St₅_types
          St₃_sub_St₄_types vs_disj_St₁ zs_not_types
      have typ_D_enc_St₅ : St₅.types ⊢ˢ D_enc : τ.toSMTType.fun SMTType.bool :=
        SMT.Typing.weakening St₁_sub_St₅_types typ_D_enc
      have St₅_keys_sub : AList.keys St₅.types ⊆ St₅.env.usedVars := by
        rw [St₅_used]
        intro v hv
        rw [St₅_types] at hv
        have hv_cases : v ∈ zs ∨ v ∈ St₄.types := by
          by_cases h : v ∈ zs
          · left; exact h
          · right
            apply AList.mem_of_mem_foldl_insert' (l := zs.zip τs)
            · exact hv
            · intro hmap
              rw [List.mem_map] at hmap
              obtain ⟨⟨a, b⟩, hab, rfl⟩ := hmap
              exact h (List.of_mem_zip hab).1
        rcases hv_cases with h_zs | h_St₄
        · exact List.mem_append_left _ (List.mem_reverse.mpr h_zs)
        · exact List.mem_append_right _ (St₄_keys_sub h_St₄)
      mspec castMembership_spec.{u} (n := St₅.env.freshvarsc) (used := St₅.env.usedVars)
        toPairl_typ typ_D_enc_St₅
      rename_i out_cm
      obtain ⟨z_mem_D', τ_cm⟩ := out_cm
      mrename_i pre_cm
      mintro ∀St₆
      mpure pre_cm
      obtain ⟨St₅_fvc_le_St₆, St₅_sub_St₆_types, St₆_keys_sub, St₅_used_sub_St₆,
        τ_cm_eq, typ_cm, fv_z_mem, St₆_preserves, cm_total⟩ := pre_cm
      subst τ_cm_eq
      mspec Std.Do.Spec.get_StateT
      mspec Std.Do.Spec.modifyGet_StateT
      beta_reduce
      mspec SMT.eraseVars_forIn_spec (vars := zs)
      mrename_i pre_e2
      mintro ∀St₈
      mpure pre_e2
      obtain ⟨St₈_types, St₈_fvc, St₈_used⟩ := pre_e2
      mpure_intro
      have St₁_sub_St₂_used : St₁.env.usedVars ⊆ St₂.env.usedVars := by
        rw [St₂_used]; exact fun _ h => h
      have St₂_sub_St₃_used : St₂.env.usedVars ⊆ St₃.env.usedVars := by
        intro v hv
        rw [St₃_used]
        suffices h : ∀ (l : List (SMT.𝒱 × SMTType)) (acc : List SMT.𝒱),
            v ∈ acc → v ∈ l.foldl (fun used p => p.1 :: used) acc from h _ _ hv
        intro l; induction l with
        | nil => intro acc hmem; exact hmem
        | cons p ps ih => intro acc hmem; exact ih _ (List.mem_cons_of_mem _ hmem)
      have St₃_sub_St₅_used : St₃.env.usedVars ⊆ St₅.env.usedVars := by
        intro v hv
        rw [St₅_used]
        exact List.mem_append_right _ (St₃_sub_St₄ hv)
      have St₅_sub_St₆_used : St₅.env.usedVars ⊆ St₆.env.usedVars := St₅_used_sub_St₆
      have St₆_sub_St₈_used : St₆.env.usedVars ⊆ St₈.env.usedVars := by
        rw [St₈_used]; exact fun _ h => h
      have St₁_sub_St₈_used : St₁.env.usedVars ⊆ St₈.env.usedVars := fun v hv =>
        St₆_sub_St₈_used (St₅_sub_St₆_used
          (St₃_sub_St₅_used (St₂_sub_St₃_used (St₁_sub_St₂_used hv))))
      have St₁_sub_St₄_types : St₁.types ⊆ St₄.types :=
        AList.subset_trans St₁_sub_St₂_types
          (AList.subset_trans St₂_sub_St₃_types St₃_sub_St₄_types)
      have St₀_sub_St₄_types : St₀.types ⊆ St₄.types :=
        AList.subset_trans St₀_sub_St₁ St₁_sub_St₄_types
      have St₀_sub_St₅_types : St₀.types ⊆ St₅.types :=
        AList.subset_trans St₀_sub_St₄_types St₄_sub_St₅_types
      have St₀_sub_St₆_types : St₀.types ⊆ St₆.types :=
        AList.subset_trans St₀_sub_St₅_types St₅_sub_St₆_types
      have zs_not_St₀ : ∀ z ∈ zs, z ∉ St₀.types := fun z hz hz_St₀ =>
        zs_not_types z hz (AList.mem_of_subset St₀_sub_St₄_types hz_St₀)
      refine ⟨?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_⟩
      · -- used ⊆ St₈.usedVars
        exact fun v hv => St₆_sub_St₈_used (St₅_sub_St₆_used
          (St₃_sub_St₅_used (St₂_sub_St₃_used (St₁_sub_St₂_used (used_sub_St₁ hv)))))
      · -- St₀.types ⊆ St₈.types
        intro ⟨k, τ_k⟩ hk_St₀
        have hk_St₃ : ⟨k, τ_k⟩ ∈ St₃.types.entries := by
          have h1 : ⟨k, τ_k⟩ ∈ St₁.types.entries := St₀_sub_St₁ hk_St₀
          have h2 : ⟨k, τ_k⟩ ∈ St₂.types.entries := St₁_sub_St₂_types h1
          exact St₂_sub_St₃_types h2
        have hk_St₀_mem : k ∈ St₀.types :=
          AList.mem_keys.mpr (List.mem_map.mpr ⟨⟨k, τ_k⟩, hk_St₀, rfl⟩)
        have hk_not_zs : k ∉ zs := fun hk_zs => zs_not_St₀ k hk_zs hk_St₀_mem
        rw [St₈_types]
        exact AList.mem_foldl_erase_of_not_mem_keys hk_St₃ hk_not_zs
      · -- AList.keys St₈.types ⊆ St₈.usedVars
        intro v hv
        obtain ⟨τ_v, hτ_v⟩ := Option.isSome_iff_exists.mp (AList.lookup_isSome.mpr hv)
        have h_St₈ : ⟨v, τ_v⟩ ∈ St₈.types.entries := AList.mem_lookup_iff.1 hτ_v
        rw [St₈_types] at h_St₈
        have h_St₃ : ⟨v, τ_v⟩ ∈ St₃.types.entries :=
          AList.foldl_erase_entries_subset zs _ h_St₈
        have hv_St₃ : v ∈ St₃.types :=
          AList.mem_keys.mpr (List.mem_map.mpr ⟨⟨v, τ_v⟩, h_St₃, rfl⟩)
        exact St₆_sub_St₈_used (St₅_sub_St₆_used (St₃_sub_St₅_used (St₃_keys_sub hv_St₃)))
      · -- CoversUsedVars
        intro v hv
        rw [B.fv, List.mem_append] at hv
        rcases hv with hv_D | hv_P
        · exact St₁_sub_St₈_used (covers_D v hv_D)
        · rw [List.mem_removeAll_iff] at hv_P
          obtain ⟨hv_fv_P, _⟩ := hv_P
          have hv_used_P : v ∈ St₄.env.usedVars := covers_P v hv_fv_P
          have hv_used_St₅ : v ∈ St₅.env.usedVars := by
            rw [St₅_used]; exact List.mem_append_right _ hv_used_P
          exact St₆_sub_St₈_used (St₅_sub_St₆_used hv_used_St₅)
      · exact SMT.encoder_all_result_well_typed _ _ _ _
      · -- preservation
        intro v v_used v_not_St₀ v_not_vars hv_St₈
        obtain ⟨τ_v, hτ_v⟩ := Option.isSome_iff_exists.mp (AList.lookup_isSome.mpr hv_St₈)
        have h_St₈ : ⟨v, τ_v⟩ ∈ St₈.types.entries := AList.mem_lookup_iff.1 hτ_v
        rw [St₈_types] at h_St₈
        have h_St₃ : ⟨v, τ_v⟩ ∈ St₃.types.entries :=
          AList.foldl_erase_entries_subset zs _ h_St₈
        have hv_St₃ : v ∈ St₃.types :=
          AList.mem_keys.mpr (List.mem_map.mpr ⟨⟨v, τ_v⟩, h_St₃, rfl⟩)
        by_cases hv_vs : v ∈ vs
        · apply v_not_vars
          unfold B.Term.vars; rw [List.mem_union_iff]; right
          simp only [B.bv, List.mem_append]; left; left; exact hv_vs
        · have hv_St₁ : v ∈ St₁.types := by
            rw [St₃_types, St₂_types] at hv_St₃
            exact AList.mem_of_mem_foldl_insert' hv_St₃ (by
              intro h
              rw [List.mem_map] at h
              obtain ⟨⟨a, b⟩, hab, rfl⟩ := h
              exact hv_vs (List.of_mem_zip hab).1)
          have hv_vars_D : v ∈ B.Term.vars D := by
            by_contra h
            exact absurd hv_St₁ (D_preserves_types v v_used v_not_St₀ h)
          apply v_not_vars
          unfold B.Term.vars at hv_vars_D ⊢
          rw [List.mem_union_iff] at hv_vars_D ⊢
          rcases hv_vars_D with h_fv_D | h_bv_D
          · left; simp only [B.fv, List.mem_append]; left; exact h_fv_D
          · right; simp only [B.bv, List.mem_append]; left; right; exact h_bv_D
      · -- ∃ Δ' ...
        have hΔ_ext_outside : ∀ v ∉ vs, Δ_ext v = «Δ» v := fun v hv => by
          rw [Δ_ext_def]; exact Function.updates_of_not_mem «Δ» vs _ v hv
        have hΔ_D_ext_outside : ∀ v ∉ vs, Δ_D_ext v = Δ_D v := fun v hv => by
          rw [Δ_D_ext_def]; exact Function.updates_of_not_mem Δ_D vs _ v hv
        have Δ_D_ext_extends : SMT.RenamingContext.Extends Δ_D_ext Δ_D := by
          intro v d hv
          rw [Δ_D_ext_def]
          have hv_not_vs : v ∉ vs := by
            intro hvs
            exact vs_disj_St₁ v hvs (Δ_D_dom v (Option.ne_none_iff_exists.mpr ⟨d, hv.symm⟩))
          rw [Function.updates_of_not_mem _ _ _ _ hv_not_vs]
          exact hv
        have Δ_P_extends_Δ₀ : SMT.RenamingContext.Extends Δ_P Δ₀ := fun v d hv =>
          Δ_P_extends (Δ_D_ext_extends (Δ_D_extends hv))
        have St₄_sub_St₈_used : St₄.env.usedVars ⊆ St₈.env.usedVars := by
          intro v hv
          have h1 : v ∈ St₅.env.usedVars := by
            rw [St₅_used]; exact List.mem_append_right _ hv
          exact St₆_sub_St₈_used (St₅_sub_St₆_used h1)
        set imp_body : SMT.Term :=
          (List.foldr (fun x t => Term.forall [x.1] [x.2] t)
            (List.foldr (fun x1 x2 => x1 ⇒ˢ x2)
              (z_mem_D' ⇒ˢ SMT.substList vs (List.map SMT.Term.var zs) P_enc)
              (List.filterMap
                (fun x => match x with
                  | Instr.define_fun v SMTType.unit SMTType.bool b => some b
                  | _ => none)
                (List.drop (List.length St₃.env.declarations) St₆.env.declarations)))
            (List.filterMap
              (fun x => match x with
                | Instr.declare_const v τ => some (v, τ)
                | _ => none)
              (List.drop (List.length St₃.env.declarations) St₆.env.declarations)))
          with imp_body_def
        have fv_foldr_forall : ∀ (xs : List (SMT.𝒱 × SMTType)) (base : SMT.Term) v,
            v ∈ SMT.fv (List.foldr (fun x t => Term.forall [x.1] [x.2] t) base xs) →
            v ∈ SMT.fv base ∧ v ∉ xs.map (·.1) := by
          intro xs base v
          induction xs with
          | nil => intro hv; refine ⟨hv, ?_⟩; simp
          | cons x xs ih =>
            intro hv
            simp only [List.foldr, SMT.fv, List.mem_removeAll_iff,
              List.mem_singleton] at hv
            obtain ⟨hv_t, hv_ne⟩ := hv
            have ⟨hv_base, hv_not_xs⟩ := ih hv_t
            refine ⟨hv_base, ?_⟩
            simp only [List.map_cons, List.mem_cons]
            exact fun h => h.elim hv_ne hv_not_xs
        have fv_foldr_imp : ∀ (ts : List SMT.Term) (base : SMT.Term) v,
            v ∈ SMT.fv (List.foldr (fun x1 x2 => x1 ⇒ˢ x2) base ts) →
            v ∈ SMT.fv base ∨ ∃ t ∈ ts, v ∈ SMT.fv t := by
          intro ts base v
          induction ts with
          | nil => intro hv; exact Or.inl hv
          | cons t ts ih =>
            intro hv
            simp only [List.foldr, SMT.fv, List.mem_append] at hv
            rcases hv with hv_t | hv_rest
            · exact Or.inr ⟨t, List.mem_cons_self, hv_t⟩
            · rcases ih hv_rest with h | ⟨t', ht', hv_t'⟩
              · exact Or.inl h
              · exact Or.inr ⟨t', List.mem_cons_of_mem _ ht', hv_t'⟩
        have hcov_D : SMT.RenamingContext.CoversFV Δ_P D_enc := by
          intro v hv_D
          have hD_some : (Δ_D v).isSome = true := Δ_D_covers v hv_D
          obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hD_some
          have : Δ_D_ext v = some d := Δ_D_ext_extends hd
          have : Δ_P v = some d := Δ_P_extends this
          rw [this]; rfl
        have hcov : RenamingContext.CoversFV Δ_P (Term.forall zs τs imp_body) := by
          intro v hv
          simp only [SMT.fv, List.mem_removeAll_iff] at hv
          obtain ⟨hv_body, hv_not_zs⟩ := hv
          have ⟨hv_inner, hv_not_ex⟩ := fv_foldr_forall _ _ v hv_body
          rcases fv_foldr_imp _ _ v hv_inner with hv_base | ⟨sb, hsb_mem, hv_sb⟩
          · simp only [SMT.fv, List.mem_append] at hv_base
            rcases hv_base with hv_zmem | hv_subst
            · rcases fv_z_mem v hv_zmem with hv_pairl | hv_D_or | hv_notΛ
              · exact absurd (fv_pairl_sub_zs_helper zs v hv_pairl) hv_not_zs
              · exact hcov_D v hv_D_or
              · -- v ∉ St₅.types via castMembership_fresh_in_declared
                rcases SMT.castMembership_fresh_in_declared
                    (List.map SMT.Term.var zs).toPairl D_enc z_mem_D' St₅.types
                    St₃.env.declarations St₆.env.declarations v hv_zmem hv_notΛ with
                  h_x | h_S | h_decls
                · exact absurd (fv_pairl_sub_zs_helper zs v h_x) hv_not_zs
                · exact hcov_D v h_S
                · exfalso
                  apply hv_not_ex
                  exact h_decls
            · rcases SMT_mem_fv_substList hv_subst with hv_P | ⟨t, ht, hv_t⟩
              · exact Δ_P_covers v hv_P
              · rw [List.mem_map] at ht
                obtain ⟨z, hz, rfl⟩ := ht
                simp only [SMT.fv, List.mem_singleton] at hv_t
                exact absurd (hv_t ▸ hz) hv_not_zs
          · -- v ∈ fv spec_body via scoping axiom
            have h_in_decls : ∃ name, .define_fun name SMTType.unit SMTType.bool sb ∈
                (St₆.env.declarations).drop (St₃.env.declarations).length := by
              rw [List.mem_filterMap] at hsb_mem
              obtain ⟨inst, h_inst_mem, h_inst_eq⟩ := hsb_mem
              match inst, h_inst_eq with
              | .define_fun name SMTType.unit SMTType.bool b, h =>
                simp only [Option.some.injEq] at h
                exact ⟨name, h ▸ h_inst_mem⟩
            rcases SMT.encoder_spec_body_fv_in_ex_binders_or_renaming
              St₃.env.declarations St₆.env.declarations Δ_P sb v h_in_decls hv_sb with
              h_ex | h_Δ
            · exact absurd h_ex hv_not_ex
            · exact h_Δ
        refine ⟨Δ_P, hcov, ?_, ?_, ?_, ?_⟩
        · exact Δ_P_extends_Δ₀
        · -- ExtendsOnSourceFV Δ_P Δ (Term.all vs D P)
          intro v d hv_eq
          have hv_fv : v ∈ B.fv (Term.all vs D P) := by
            by_contra hv_not
            have : B.RenamingContext.toSMTOnFV «Δ» (Term.all vs D P) v = none := by
              simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_not]
            rw [this] at hv_eq; exact absurd hv_eq (by simp)
          simp only [B.fv, List.mem_append] at hv_fv
          rcases hv_fv with hv_fvD | hv_fvP_minus_vs
          · have h_toSMT_D : B.RenamingContext.toSMTOnFV «Δ» D v =
                B.RenamingContext.toSMTOnFV «Δ» (Term.all vs D P) v := by
              simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                B.RenamingContext.restrictToFV_eq_of_mem hv_fvD,
                B.RenamingContext.restrictToFV_eq_of_mem (fv.mem_all (.inl hv_fvD))]
            have h1 : Δ_D v = some d := Δ_D_src_ext (h_toSMT_D ▸ hv_eq)
            exact Δ_P_extends (Δ_D_ext_extends h1)
          · rw [List.mem_removeAll_iff] at hv_fvP_minus_vs
            obtain ⟨hv_fvP, hv_not_vs⟩ := hv_fvP_minus_vs
            have hΔ_ext_eq : Δ_ext v = «Δ» v := hΔ_ext_outside v hv_not_vs
            have h_toSMT_P : B.RenamingContext.toSMTOnFV Δ_ext P v =
                B.RenamingContext.toSMTOnFV «Δ» (Term.all vs D P) v := by
              simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                B.RenamingContext.restrictToFV_eq_of_mem hv_fvP,
                B.RenamingContext.restrictToFV_eq_of_mem (fv.mem_all (.inr ⟨hv_fvP, hv_not_vs⟩)),
                hΔ_ext_eq]
            exact Δ_P_src_ext (h_toSMT_P ▸ hv_eq)
        · exact fun v hv_out => Δ_P_none v (fun hv_in => hv_out (St₄_sub_St₈_used hv_in))
        · -- ∃ denT' + RDom + totality via passed-in witnesses
          obtain ⟨denT', hden_eq, hrdom⟩ :=
            existence_rdom_witness_hasflag hcov T hT
          refine ⟨denT', hden_eq, hrdom, ?_⟩
          intro Δ_alt Δ_fv_alt Δ₀_alt hext_alt hnone_alt hwt_alt T_alt hT_alt hden_alt
          exact totality_witness_hasflag (used' := St₈.env.usedVars) (Λ' := St₈.types) hcov
            Δ_alt Δ_fv_alt Δ₀_alt hext_alt hnone_alt hwt_alt T_alt hT_alt hden_alt
      -- non-`.bool` arm of `let ⟨P', .bool⟩ ← encodeTerm P E' | throw`
      mspec encodeTerm_struct (E := E) (Λ := St₄.types) («Δ» := Δ_ext) (Δ₀ := Δ_D_ext)
        Δ₀_ext_P (used := St₄.env.usedVars)
        (fun v hv => Δ_D_ext_none_St₃ v (fun h => hv (St₃_sub_St₄ h)))
        (fun v hv => St₃_sub_St₄ (vars_used_P_St₃ v hv)) hP_bv_nodup
        (n := St₄.env.freshvarsc) <;> mvcgen
    · -- has-flag EMPTY case
      have h𝒟_eq : 𝒟 = 𝒟' := by
        have := den_D_eq ▸ den_D
        simp only [Option.some.injEq, PSigma.mk.injEq] at this
        exact this.1.symm
      have h𝒟_empty_eq : 𝒟 = ∅ := h𝒟_eq.trans h𝒟_empty
      let x_fin_default : Fin vs.length → B.Dom.{u} := fun i =>
        ⟨(τ.get vs.length i).defaultZFSet, ⟨τ.get vs.length i,
          BType.mem_toZFSet_of_defaultZFSet⟩⟩
      set Δ_ext : B.RenamingContext.Context :=
        Function.updates «Δ» vs (List.ofFn fun i => some (x_fin_default i)) with Δ_ext_def
      have Δ_fv_P := Δ_fv_P_helper vs_nodup Δ_ext_def D P Δ_fv
      classical
      by_cases hP_den_cond : ∃ (P_val : ZFSet.{u}) (hP_val : P_val ∈ ⟦BType.bool⟧ᶻ),
          ⟦P.abstract Δ_ext Δ_fv_P⟧ᴮ = some ⟨P_val, BType.bool, hP_val⟩
      · obtain ⟨P_val, hP_val, hP_den⟩ := hP_den_cond
        set Δ_D_ext : SMT.RenamingContext.Context :=
          Function.updates Δ_D vs (List.ofFn fun (i : Fin vs.length) =>
            B.RenamingContext.toSMT Δ_ext vs[i])
          with Δ_D_ext_def
        have Δ_D_ext_none_St₃ : ∀ v ∉ St₃.env.usedVars, Δ_D_ext v = none :=
          Δ_D_ext_none_helper (ΔDD := Δ_D) (ΔDDext := Δ_D_ext)
            (vs := vs) (vs_nodup := vs_nodup) (vs_τs_len := vs_τs_len)
            (used0 := St₁.env.usedVars) (used1 := St₂.env.usedVars)
            (used2 := St₃.env.usedVars)
            (St_used_def := St₃_used) (used1_eq_used0 := St₂_used)
            (ΔDDext_def := Δ_D_ext_def) (ΔDD_none_outside := Δ_D_none_St₃)
        have Δ₀_ext_P : RenamingContext.ExtendsOnSourceFV Δ_D_ext Δ_ext P :=
          Δ₀_ext_P_helper vs_nodup Δ_ext_def Δ_D_ext_def D P
            (lift := fun hv => Δ_D_extends (Δ₀_ext hv))
        mspec Std.Do.Spec.get_StateT
        mspec Std.Do.Spec.get_StateT
        mspec Std.Do.Spec.get_StateT
        mspec encodeTerm_struct (E := E') (Λ := St₃.types) («Δ» := Δ_ext) (Δ₀ := Δ_D_ext)
          Δ₀_ext_P (used := St₃.env.usedVars) Δ_D_ext_none_St₃ vars_used_P_St₃ hP_bv_nodup
          (n := St₃.env.freshvarsc)
        rename_i out_P
        obtain ⟨P_enc, σP⟩ := out_P
        mrename_i pre
        mintro ∀St₄
        mpure pre
        obtain ⟨St₃_sub_St₄, St₃_sub_St₄_types, St₄_keys_sub, covers_P, P_fv_sub,
          P_preserves_types,
          Δ_P, Δ_P_covers, Δ_P_extends, Δ_P_src_ext, Δ_P_none⟩ := pre
        split
        rename_i heq
        injection heq with hPe hσe
        subst hσe
        subst hPe
        simp only [BType.toSMTType] at *
        mspec SMT.freshVarList_spec τs
        rename_i zs
        mrename_i pre
        mintro ∀St₅
        mpure pre
        obtain ⟨zs_len, zs_nodup, zs_not_used, zs_not_types, St₅_fvc, St₅_used, St₅_types⟩ := pre
        have zs_nemp : zs ≠ [] := zs_nemp_helper zs_len vs_τs_len vs_nemp
        have zs_typing := zs_typing_helper (St₅types := St₅.types) zs_nodup zs_len St₅_types
        have toPairl_typ : St₅.types ⊢ˢ (zs.map SMT.Term.var).toPairl : τs.toProdl :=
          toPairl_typ_helper zs_len zs_nemp zs_typing
        obtain ⟨vs_not_D_fv, vs_disj_St₁⟩ :=
          vs_disj_St₁_helper (P := P) typ_D vs_Γ_disj Λ_inv vars_used_vs D_preserves_types bv_nodup
        obtain ⟨St₁_sub_St₂_types, St₂_sub_St₃_types, St₄_sub_St₅_types, St₁_sub_St₅_types⟩ :=
          St_chain_helper vs_nodup zs_nodup St₂_types St₃_types St₅_types
            St₃_sub_St₄_types vs_disj_St₁ zs_not_types
        have typ_D_enc_St₅ : St₅.types ⊢ˢ D_enc : τ.toSMTType.fun SMTType.bool :=
          SMT.Typing.weakening St₁_sub_St₅_types typ_D_enc
        have St₅_keys_sub : AList.keys St₅.types ⊆ St₅.env.usedVars := by
          rw [St₅_used]
          intro v hv
          rw [St₅_types] at hv
          have hv_cases : v ∈ zs ∨ v ∈ St₄.types := by
            by_cases h : v ∈ zs
            · left; exact h
            · right
              apply AList.mem_of_mem_foldl_insert' (l := zs.zip τs)
              · exact hv
              · intro hmap
                rw [List.mem_map] at hmap
                obtain ⟨⟨a, b⟩, hab, rfl⟩ := hmap
                exact h (List.of_mem_zip hab).1
          rcases hv_cases with h_zs | h_St₄
          · exact List.mem_append_left _ (List.mem_reverse.mpr h_zs)
          · exact List.mem_append_right _ (St₄_keys_sub h_St₄)
        mspec castMembership_spec.{u} (n := St₅.env.freshvarsc) (used := St₅.env.usedVars)
          toPairl_typ typ_D_enc_St₅
        rename_i out_cm
        obtain ⟨z_mem_D', τ_cm⟩ := out_cm
        mrename_i pre_cm
        mintro ∀St₆
        mpure pre_cm
        obtain ⟨St₅_fvc_le_St₆, St₅_sub_St₆_types, St₆_keys_sub, St₅_used_sub_St₆,
          τ_cm_eq, typ_cm, fv_z_mem, St₆_preserves, cm_total⟩ := pre_cm
        subst τ_cm_eq
        mspec Std.Do.Spec.get_StateT
        mspec Std.Do.Spec.modifyGet_StateT
        beta_reduce
        mspec SMT.eraseVars_forIn_spec (vars := zs)
        mrename_i pre_e2
        mintro ∀St₈
        mpure pre_e2
        obtain ⟨St₈_types, St₈_fvc, St₈_used⟩ := pre_e2
        mpure_intro
        have St₁_sub_St₂_used : St₁.env.usedVars ⊆ St₂.env.usedVars := by
          rw [St₂_used]; exact fun _ h => h
        have St₂_sub_St₃_used : St₂.env.usedVars ⊆ St₃.env.usedVars := by
          intro v hv
          rw [St₃_used]
          suffices h : ∀ (l : List (SMT.𝒱 × SMTType)) (acc : List SMT.𝒱),
              v ∈ acc → v ∈ l.foldl (fun used p => p.1 :: used) acc from h _ _ hv
          intro l; induction l with
          | nil => intro acc hmem; exact hmem
          | cons p ps ih => intro acc hmem; exact ih _ (List.mem_cons_of_mem _ hmem)
        have St₃_sub_St₅_used : St₃.env.usedVars ⊆ St₅.env.usedVars := by
          intro v hv
          rw [St₅_used]
          exact List.mem_append_right _ (St₃_sub_St₄ hv)
        have St₅_sub_St₆_used : St₅.env.usedVars ⊆ St₆.env.usedVars := St₅_used_sub_St₆
        have St₆_sub_St₈_used : St₆.env.usedVars ⊆ St₈.env.usedVars := by
          rw [St₈_used]; exact fun _ h => h
        have St₁_sub_St₈_used : St₁.env.usedVars ⊆ St₈.env.usedVars := fun v hv =>
          St₆_sub_St₈_used (St₅_sub_St₆_used
            (St₃_sub_St₅_used (St₂_sub_St₃_used (St₁_sub_St₂_used hv))))
        have St₁_sub_St₄_types : St₁.types ⊆ St₄.types :=
          AList.subset_trans St₁_sub_St₂_types
            (AList.subset_trans St₂_sub_St₃_types St₃_sub_St₄_types)
        have St₀_sub_St₄_types : St₀.types ⊆ St₄.types :=
          AList.subset_trans St₀_sub_St₁ St₁_sub_St₄_types
        have St₀_sub_St₅_types : St₀.types ⊆ St₅.types :=
          AList.subset_trans St₀_sub_St₄_types St₄_sub_St₅_types
        have St₀_sub_St₆_types : St₀.types ⊆ St₆.types :=
          AList.subset_trans St₀_sub_St₅_types St₅_sub_St₆_types
        have zs_not_St₀ : ∀ z ∈ zs, z ∉ St₀.types := fun z hz hz_St₀ =>
          zs_not_types z hz (AList.mem_of_subset St₀_sub_St₄_types hz_St₀)
        have Δ_D_ext_extends : SMT.RenamingContext.Extends Δ_D_ext Δ_D := by
          intro v d hv
          rw [Δ_D_ext_def]
          have hv_not_vs : v ∉ vs := by
            intro hvs
            exact vs_disj_St₁ v hvs (Δ_D_dom v (Option.ne_none_iff_exists.mpr ⟨d, hv.symm⟩))
          rw [Function.updates_of_not_mem _ _ _ _ hv_not_vs]
          exact hv
        have Δ_P_extends_Δ₀ : SMT.RenamingContext.Extends Δ_P Δ₀ := fun v d hv =>
          Δ_P_extends (Δ_D_ext_extends (Δ_D_extends hv))
        have hΔ_ext_outside : ∀ v ∉ vs, Δ_ext v = «Δ» v := fun v hv => by
          rw [Δ_ext_def]; exact Function.updates_of_not_mem «Δ» vs _ v hv
        have St₄_sub_St₈_used : St₄.env.usedVars ⊆ St₈.env.usedVars := by
          intro v hv
          have h1 : v ∈ St₅.env.usedVars := by
            rw [St₅_used]; exact List.mem_append_right _ hv
          exact St₆_sub_St₈_used (St₅_sub_St₆_used h1)
        set imp_body : SMT.Term :=
          (List.foldr (fun x t => Term.forall [x.1] [x.2] t)
            (List.foldr (fun x1 x2 => x1 ⇒ˢ x2)
              (z_mem_D' ⇒ˢ SMT.substList vs (List.map SMT.Term.var zs) P_enc)
              (List.filterMap
                (fun x => match x with
                  | Instr.define_fun v SMTType.unit SMTType.bool b => some b
                  | _ => none)
                (List.drop (List.length St₃.env.declarations) St₆.env.declarations)))
            (List.filterMap
              (fun x => match x with
                | Instr.declare_const v τ => some (v, τ)
                | _ => none)
              (List.drop (List.length St₃.env.declarations) St₆.env.declarations)))
          with imp_body_def
        have fv_foldr_forall : ∀ (xs : List (SMT.𝒱 × SMTType)) (base : SMT.Term) v,
            v ∈ SMT.fv (List.foldr (fun x t => Term.forall [x.1] [x.2] t) base xs) →
            v ∈ SMT.fv base ∧ v ∉ xs.map (·.1) := by
          intro xs base v
          induction xs with
          | nil => intro hv; refine ⟨hv, ?_⟩; simp
          | cons x xs ih =>
            intro hv
            simp only [List.foldr, SMT.fv, List.mem_removeAll_iff,
              List.mem_singleton] at hv
            obtain ⟨hv_t, hv_ne⟩ := hv
            have ⟨hv_base, hv_not_xs⟩ := ih hv_t
            refine ⟨hv_base, ?_⟩
            simp only [List.map_cons, List.mem_cons]
            exact fun h => h.elim hv_ne hv_not_xs
        have fv_foldr_imp : ∀ (ts : List SMT.Term) (base : SMT.Term) v,
            v ∈ SMT.fv (List.foldr (fun x1 x2 => x1 ⇒ˢ x2) base ts) →
            v ∈ SMT.fv base ∨ ∃ t ∈ ts, v ∈ SMT.fv t := by
          intro ts base v
          induction ts with
          | nil => intro hv; exact Or.inl hv
          | cons t ts ih =>
            intro hv
            simp only [List.foldr, SMT.fv, List.mem_append] at hv
            rcases hv with hv_t | hv_rest
            · exact Or.inr ⟨t, List.mem_cons_self, hv_t⟩
            · rcases ih hv_rest with h | ⟨t', ht', hv_t'⟩
              · exact Or.inl h
              · exact Or.inr ⟨t', List.mem_cons_of_mem _ ht', hv_t'⟩
        have hcov_D : SMT.RenamingContext.CoversFV Δ_P D_enc := by
          intro v hv_D
          have hD_some : (Δ_D v).isSome = true := Δ_D_covers v hv_D
          obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hD_some
          have : Δ_D_ext v = some d := Δ_D_ext_extends hd
          have : Δ_P v = some d := Δ_P_extends this
          rw [this]; rfl
        have hcov : RenamingContext.CoversFV Δ_P (Term.forall zs τs imp_body) := by
          intro v hv
          simp only [SMT.fv, List.mem_removeAll_iff] at hv
          obtain ⟨hv_body, hv_not_zs⟩ := hv
          have ⟨hv_inner, hv_not_ex⟩ := fv_foldr_forall _ _ v hv_body
          rcases fv_foldr_imp _ _ v hv_inner with hv_base | ⟨sb, hsb_mem, hv_sb⟩
          · simp only [SMT.fv, List.mem_append] at hv_base
            rcases hv_base with hv_zmem | hv_subst
            · rcases fv_z_mem v hv_zmem with hv_pairl | hv_D_or | hv_notΛ
              · exact absurd (fv_pairl_sub_zs_helper zs v hv_pairl) hv_not_zs
              · exact hcov_D v hv_D_or
              · rcases SMT.castMembership_fresh_in_declared
                    (List.map SMT.Term.var zs).toPairl D_enc z_mem_D' St₅.types
                    St₃.env.declarations St₆.env.declarations v hv_zmem hv_notΛ with
                  h_x | h_S | h_decls
                · exact absurd (fv_pairl_sub_zs_helper zs v h_x) hv_not_zs
                · exact hcov_D v h_S
                · exact absurd h_decls hv_not_ex
            · rcases SMT_mem_fv_substList hv_subst with hv_P | ⟨t, ht, hv_t⟩
              · exact Δ_P_covers v hv_P
              · rw [List.mem_map] at ht
                obtain ⟨z, hz, rfl⟩ := ht
                simp only [SMT.fv, List.mem_singleton] at hv_t
                exact absurd (hv_t ▸ hz) hv_not_zs
          · have h_in_decls : ∃ name, .define_fun name SMTType.unit SMTType.bool sb ∈
                (St₆.env.declarations).drop (St₃.env.declarations).length := by
              rw [List.mem_filterMap] at hsb_mem
              obtain ⟨inst, h_inst_mem, h_inst_eq⟩ := hsb_mem
              match inst, h_inst_eq with
              | .define_fun name SMTType.unit SMTType.bool b, h =>
                simp only [Option.some.injEq] at h
                exact ⟨name, h ▸ h_inst_mem⟩
            rcases SMT.encoder_spec_body_fv_in_ex_binders_or_renaming
              St₃.env.declarations St₆.env.declarations Δ_P sb v h_in_decls hv_sb with
              h_ex | h_Δ
            · exact absurd h_ex hv_not_ex
            · exact h_Δ
        refine ⟨?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_⟩
        · exact fun v hv => St₁_sub_St₈_used (used_sub_St₁ hv)
        · intro ⟨k, τ_k⟩ hk_St₀
          have hk_St₃ : ⟨k, τ_k⟩ ∈ St₃.types.entries := by
            have h1 : ⟨k, τ_k⟩ ∈ St₁.types.entries := St₀_sub_St₁ hk_St₀
            have h2 : ⟨k, τ_k⟩ ∈ St₂.types.entries := St₁_sub_St₂_types h1
            exact St₂_sub_St₃_types h2
          have hk_St₀_mem : k ∈ St₀.types :=
            AList.mem_keys.mpr (List.mem_map.mpr ⟨⟨k, τ_k⟩, hk_St₀, rfl⟩)
          have hk_not_zs : k ∉ zs := fun hk_zs => zs_not_St₀ k hk_zs hk_St₀_mem
          rw [St₈_types]
          exact AList.mem_foldl_erase_of_not_mem_keys hk_St₃ hk_not_zs
        · intro v hv
          obtain ⟨τ_v, hτ_v⟩ := Option.isSome_iff_exists.mp (AList.lookup_isSome.mpr hv)
          have h_St₈ : ⟨v, τ_v⟩ ∈ St₈.types.entries := AList.mem_lookup_iff.1 hτ_v
          rw [St₈_types] at h_St₈
          have h_St₃ : ⟨v, τ_v⟩ ∈ St₃.types.entries :=
            AList.foldl_erase_entries_subset zs _ h_St₈
          have hv_St₃ : v ∈ St₃.types :=
            AList.mem_keys.mpr (List.mem_map.mpr ⟨⟨v, τ_v⟩, h_St₃, rfl⟩)
          exact St₆_sub_St₈_used (St₅_sub_St₆_used (St₃_sub_St₅_used (St₃_keys_sub hv_St₃)))
        · intro v hv
          rw [B.fv, List.mem_append] at hv
          rcases hv with hv_D | hv_P
          · exact St₁_sub_St₈_used (covers_D v hv_D)
          · rw [List.mem_removeAll_iff] at hv_P
            obtain ⟨hv_fv_P, _⟩ := hv_P
            have hv_used_P : v ∈ St₄.env.usedVars := covers_P v hv_fv_P
            have hv_used_St₅ : v ∈ St₅.env.usedVars := by
              rw [St₅_used]; exact List.mem_append_right _ hv_used_P
            exact St₆_sub_St₈_used (St₅_sub_St₆_used hv_used_St₅)
        · exact SMT.encoder_all_result_well_typed _ _ _ _
        · intro v v_used v_not_St₀ v_not_vars hv_St₈
          obtain ⟨τ_v, hτ_v⟩ := Option.isSome_iff_exists.mp (AList.lookup_isSome.mpr hv_St₈)
          have h_St₈ : ⟨v, τ_v⟩ ∈ St₈.types.entries := AList.mem_lookup_iff.1 hτ_v
          rw [St₈_types] at h_St₈
          have h_St₃ : ⟨v, τ_v⟩ ∈ St₃.types.entries :=
            AList.foldl_erase_entries_subset zs _ h_St₈
          have hv_St₃ : v ∈ St₃.types :=
            AList.mem_keys.mpr (List.mem_map.mpr ⟨⟨v, τ_v⟩, h_St₃, rfl⟩)
          by_cases hv_vs : v ∈ vs
          · apply v_not_vars
            unfold B.Term.vars; rw [List.mem_union_iff]; right
            simp only [B.bv, List.mem_append]; left; left; exact hv_vs
          · have hv_St₁ : v ∈ St₁.types := by
              rw [St₃_types, St₂_types] at hv_St₃
              exact AList.mem_of_mem_foldl_insert' hv_St₃ (by
                intro h
                rw [List.mem_map] at h
                obtain ⟨⟨a, b⟩, hab, rfl⟩ := h
                exact hv_vs (List.of_mem_zip hab).1)
            have hv_vars_D : v ∈ B.Term.vars D := by
              by_contra h
              exact absurd hv_St₁ (D_preserves_types v v_used v_not_St₀ h)
            apply v_not_vars
            unfold B.Term.vars at hv_vars_D ⊢
            rw [List.mem_union_iff] at hv_vars_D ⊢
            rcases hv_vars_D with h_fv_D | h_bv_D
            · left; simp only [B.fv, List.mem_append]; left; exact h_fv_D
            · right; simp only [B.bv, List.mem_append]; left; right; exact h_bv_D
        · refine ⟨Δ_P, hcov, ?_, ?_, ?_, ?_⟩
          · exact Δ_P_extends_Δ₀
          · intro v d hv_eq
            have hv_fv : v ∈ B.fv (Term.all vs D P) := by
              by_contra hv_not
              have : B.RenamingContext.toSMTOnFV «Δ» (Term.all vs D P) v = none := by
                simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                  B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_not]
              rw [this] at hv_eq; exact absurd hv_eq (by simp)
            simp only [B.fv, List.mem_append] at hv_fv
            rcases hv_fv with hv_fvD | hv_fvP_minus_vs
            · have h_toSMT_D : B.RenamingContext.toSMTOnFV «Δ» D v =
                  B.RenamingContext.toSMTOnFV «Δ» (Term.all vs D P) v := by
                simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                  B.RenamingContext.restrictToFV_eq_of_mem hv_fvD,
                  B.RenamingContext.restrictToFV_eq_of_mem (fv.mem_all (.inl hv_fvD))]
              have h1 : Δ_D v = some d := Δ_D_src_ext (h_toSMT_D ▸ hv_eq)
              exact Δ_P_extends (Δ_D_ext_extends h1)
            · rw [List.mem_removeAll_iff] at hv_fvP_minus_vs
              obtain ⟨hv_fvP, hv_not_vs⟩ := hv_fvP_minus_vs
              have hΔ_ext_eq : Δ_ext v = «Δ» v := hΔ_ext_outside v hv_not_vs
              have h_toSMT_P : B.RenamingContext.toSMTOnFV Δ_ext P v =
                  B.RenamingContext.toSMTOnFV «Δ» (Term.all vs D P) v := by
                simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                  B.RenamingContext.restrictToFV_eq_of_mem hv_fvP,
                  B.RenamingContext.restrictToFV_eq_of_mem (fv.mem_all (.inr ⟨hv_fvP, hv_not_vs⟩)),
                  hΔ_ext_eq]
              exact Δ_P_src_ext (h_toSMT_P ▸ hv_eq)
          · exact fun v hv_out => Δ_P_none v (fun hv_in => hv_out (St₄_sub_St₈_used hv_in))
          · obtain ⟨denT', hden_eq, hrdom⟩ :=
              existence_rdom_witness_hasflag hcov T hT
            refine ⟨denT', hden_eq, hrdom, ?_⟩
            intro Δ_alt Δ_fv_alt Δ₀_alt hext_alt hnone_alt hwt_alt T_alt hT_alt hden_alt
            exact totality_witness_hasflag (used' := St₈.env.usedVars) (Λ' := St₈.types) hcov
              Δ_alt Δ_fv_alt Δ₀_alt hext_alt hnone_alt hwt_alt T_alt hT_alt hden_alt
        -- non-`.bool` arm of `let ⟨P', .bool⟩ ← encodeTerm P E' | throw`
        mspec encodeTerm_struct (E := E) (Λ := St₄.types) («Δ» := Δ_ext) (Δ₀ := Δ_D_ext)
          Δ₀_ext_P (used := St₄.env.usedVars)
          (fun v hv => Δ_D_ext_none_St₃ v (fun h => hv (St₃_sub_St₄ h)))
          (fun v hv => St₃_sub_St₄ (vars_used_P_St₃ v hv)) hP_bv_nodup
          (n := St₄.env.freshvarsc) <;> mvcgen
      · exfalso
        apply hP_den_cond
        exact B.denote_exists_of_typing typP Δ_ext Δ_fv_P (@WFTC.wf _ WFTC.of_abstract)
  -- NO-FLAG BRANCH
  mspec SMT.mapFinIdxM_all_body_spec_noflag vs E.flags
    (τ.toSMTType.fromProdl (vs.length - 1)) hlen_eq h_noflag
  rename_i τs
  mrename_i pre
  mintro ∀St₂
  mpure pre
  obtain ⟨St₂_types, St₂_fvc, St₂_used, τs_eq⟩ := pre
  have τs_len : τs.length = (τ.toSMTType.fromProdl (vs.length - 1)).length := by
    rw [τs_eq]
  have vs_τs_len : vs.length = τs.length := by rw [τs_len]; exact hlen_eq
  mspec SMT.addToContext_forIn_spec (pairs := vs.zip τs)
  mrename_i pre
  mintro ∀St₃
  mpure pre
  obtain ⟨St₃_types, St₃_fvc, St₃_used⟩ := pre
  set E' : B.Env := { E with context := vs.zipToAList αs ∪ E.context }
  conv in encodeTerm P E => rw [encodeTerm_env_irrel P E E' rfl]
  have St₁_sub_St₃_used : St₁.env.usedVars ⊆ St₃.env.usedVars := by
    rw [St₃_used, St₂_used]
    intro v hv
    suffices ∀ (pairs : List (SMT.𝒱 × SMTType)) (acc : List SMT.𝒱),
        v ∈ acc → v ∈ pairs.foldl (fun used p => p.1 :: used) acc by
      exact this _ _ hv
    intro pairs
    induction pairs with
    | nil => intro acc hmem; exact hmem
    | cons p ps ih => intro acc hmem; exact ih _ (List.mem_cons_of_mem _ hmem)
  have Δ_D_none_St₃ : ∀ v ∉ St₃.env.usedVars, Δ_D v = none :=
    fun v hv => Δ_D_none v (fun hmem => hv (St₁_sub_St₃_used hmem))
  have St₃_keys_sub : AList.keys St₃.types ⊆ St₃.env.usedVars := by
    rw [St₃_types, St₃_used, St₂_types, St₂_used]
    suffices h : ∀ (l : List (SMT.𝒱 × SMTType)) (Γ : SMT.TypeContext) (used : List SMT.𝒱),
        AList.keys Γ ⊆ used →
        AList.keys (l.foldl (fun Γ p => Γ.insert p.1 p.2) Γ) ⊆
          l.foldl (fun used p => p.1 :: used) used from
      h _ _ _ St₁_keys_sub
    intro l; induction l with
    | nil => intro Γ used h; exact h
    | cons p ps ih =>
      intro Γ used h; simp only [List.foldl_cons]
      apply ih; intro v hv
      simp only [AList.keys_insert] at hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (h (List.mem_of_mem_erase hv))
  have vars_used_P_St₃ : ∀ v ∈ P.vars, v ∈ St₃.env.usedVars :=
    fun v hv => St₁_sub_St₃_used (used_sub_St₁ (vars_used_P v hv))
  have St₃_types_sub_E'_ctx_on_P_vars : ∀ v ∈ P.vars, v ∈ St₃.types → v ∈ E'.context := by
    intro v v_in_P_vars v_in_St₃_types
    simp [E']
    by_cases v_in_vs : v ∈ vs
    · left
      exact AList.mem_zipToAList_of_mem vs_nodup vs_αs_len v_in_vs
    · right
      have v_in_St₁ : v ∈ St₁.types := by
        rw [St₃_types, St₂_types] at v_in_St₃_types
        exact AList.mem_of_mem_foldl_insert' v_in_St₃_types (by
          intro h
          rw [List.mem_map] at h
          obtain ⟨⟨a, b⟩, hab, rfl⟩ := h
          exact v_in_vs (List.of_mem_zip hab).1)
      have v_used : v ∈ used := vars_used_P v v_in_P_vars
      by_cases v_St₀ : v ∈ St₀.types
      · have v_all : v ∈ (Term.all vs D P).vars := by
          unfold B.Term.vars at v_in_P_vars ⊢
          rw [List.mem_union_iff]
          rcases List.mem_union_iff.mp v_in_P_vars with h_fv | h_bv
          · left; simp only [B.fv, List.mem_append]
            right
            unfold List.removeAll; rw [List.mem_filter]
            exact ⟨h_fv, by simp [v_in_vs]⟩
          · right; simp only [B.bv, List.mem_append]
            right; exact h_bv
        exact Λ_inv v v_all v_St₀
      · have v_vars_D : v ∈ B.Term.vars D := by
          by_contra h
          exact absurd v_in_St₁ (D_preserves_types v v_used v_St₀ h)
        rcases B.Term.mem_vars_iff.mp v_vars_D with h | h
        · exact AList.lookup_isSome.mp (B.Typing.mem_context_of_mem_fv typ_D h)
        · rcases B.Term.mem_vars_iff.mp v_in_P_vars with hv_fv_P | hv_bv_P
          · have h_in_E' : ((vs.zipToAList αs ∪ E.context).lookup v).isSome :=
              B.Typing.mem_context_of_mem_fv typP hv_fv_P
            have h_in_union : v ∈ vs.zipToAList αs ∪ E.context :=
              AList.lookup_isSome.mp h_in_E'
            rcases AList.mem_union.mp h_in_union with h_vs_in | h_E_in
            · exact absurd (AList.mem_zipToAList h_vs_in) v_in_vs
            · exact h_E_in
          · exfalso
            have hbn := bv_nodup
            simp only [B.bv] at hbn
            rw [List.nodup_append, List.nodup_append] at hbn
            have hin : v ∈ vs ++ B.bv D := List.mem_append.mpr (Or.inr h)
            exact hbn.2.2 v hin v hv_bv_P rfl
  rw [dif_pos τ_hasArity] at rest_all
  split_ifs at rest_all with den_P_cond typP_det_cond h𝒟_empty
  rotate_left
  · -- NONEMPTY 𝒟' (no-flag)
    have 𝒟'_nonempty : 𝒟'.Nonempty := 𝒟'.eq_empty_or_nonempty.resolve_left h𝒟_empty
    obtain ⟨x_raw, hx_raw⟩ := 𝒟'_nonempty
    have 𝒟'_sub_τ : 𝒟' ⊆ ⟦τ⟧ᶻ := by rwa [BType.toZFSet, ZFSet.mem_powerset] at h𝒟'
    have hx_raw_mem : x_raw ∈ ⟦τ⟧ᶻ := 𝒟'_sub_τ hx_raw
    have hx_raw_arity : x_raw.hasArity vs.length :=
      hasArity_of_mem_toZFSet τ_hasArity hx_raw_mem
    let x_fin : Fin vs.length → B.Dom := fun i =>
      ⟨x_raw.get vs.length i, τ.get vs.length i,
       get_mem_type_of_isTuple hx_raw_arity τ_hasArity hx_raw_mem⟩
    have h_ofFinDom_eq : ZFSet.ofFinDom x_fin = x_raw :=
      ZFSet.ofFinDom_get (List.length_pos_iff.mpr vs_nemp)
        (fun _ => get_mem_type_of_isTuple hx_raw_arity τ_hasArity hx_raw_mem)
        hx_raw_arity τ_hasArity
    set Δ_ext : B.RenamingContext.Context :=
      Function.updates «Δ» vs (List.ofFn fun i => some (x_fin i)) with Δ_ext_def
    have Δ_fv_P := Δ_fv_P_helper vs_nodup Δ_ext_def D P Δ_fv
    have hx_fin_in_𝒟 : ZFSet.ofFinDom x_fin ∈ 𝒟' := h_ofFinDom_eq ▸ hx_raw
    have hx_fin_typ : ∀ i, (x_fin i).snd.fst = τ.get vs.length i ∧
        (x_fin i).fst ∈ ⟦τ.get vs.length i⟧ᶻ :=
      fun i => ⟨rfl, (x_fin i).snd.snd⟩
    have hP_isSome : ⟦(B.Term.abstract.go P vs «Δ» _).uncurry x_fin⟧ᴮ.isSome = true :=
      den_P_cond hx_fin_typ hx_fin_in_𝒟
    obtain ⟨⟨P_val, P_ty, hP_val⟩, hP_den_raw⟩ := Option.isSome_iff_exists.mp hP_isSome
    have hP_den : ⟦P.abstract Δ_ext Δ_fv_P⟧ᴮ = some ⟨P_val, P_ty, hP_val⟩ := by
      rw [← denote_term_abstract_go_eq_term_abstract vs_nodup vs_nemp x_fin Δ_fv_P]
      exact hP_den_raw
    have hP_ty_bool : P_ty = BType.bool := by
      exact (denote_welltyped_eq
        (t := P.abstract Δ_ext Δ_fv_P)
        ⟨_, WFTC.of_abstract, .bool, by convert Typing.of_abstract Δ_fv_P typP⟩
        hP_den).symm
    subst hP_ty_bool
    set Δ_D_ext : SMT.RenamingContext.Context :=
      Function.updates Δ_D vs (List.ofFn fun (i : Fin vs.length) =>
        B.RenamingContext.toSMT Δ_ext vs[i])
      with Δ_D_ext_def
    have Δ_D_ext_none_St₃ : ∀ v ∉ St₃.env.usedVars, Δ_D_ext v = none :=
      Δ_D_ext_none_helper (ΔDD := Δ_D) (ΔDDext := Δ_D_ext)
        (vs := vs) (vs_nodup := vs_nodup) (vs_τs_len := vs_τs_len)
        (used0 := St₁.env.usedVars) (used1 := St₂.env.usedVars)
        (used2 := St₃.env.usedVars)
        (St_used_def := St₃_used) (used1_eq_used0 := St₂_used)
        (ΔDDext_def := Δ_D_ext_def) (ΔDD_none_outside := Δ_D_none_St₃)
    have Δ₀_ext_P : RenamingContext.ExtendsOnSourceFV Δ_D_ext Δ_ext P :=
      Δ₀_ext_P_helper vs_nodup Δ_ext_def Δ_D_ext_def D P
        (lift := fun hv => Δ_D_extends (Δ₀_ext hv))
    mspec Std.Do.Spec.get_StateT
    mspec Std.Do.Spec.get_StateT
    mspec Std.Do.Spec.get_StateT
    mspec P_ih (E := E') (Λ := St₃.types) (α := .bool) typP
      («Δ» := Δ_ext) Δ_fv_P
      (Δ₀ := Δ_D_ext) Δ₀_ext_P (used := St₃.env.usedVars) Δ_D_ext_none_St₃
      (T := P_val) (hT := hP_val) hP_den vars_used_P_St₃ (n := St₃.env.freshvarsc)
      St₃_types_sub_E'_ctx_on_P_vars
      hP_bv_nodup
      (by
        intro v σ_v hv hτ_v
        by_cases hvs : v ∈ vs
        · have hv_idx : vs.idxOf v < vs.length := List.idxOf_lt_length_of_mem hvs
          have hΔ_ext_v : Δ_ext v = some (x_fin ⟨vs.idxOf v, hv_idx⟩) := by
            rw [Δ_ext_def, Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup, dif_pos hvs]
            simp only [List.getElem_ofFn]
          have hToSMT_isSome : (B.RenamingContext.toSMT Δ_ext v).isSome = true := by
            unfold B.RenamingContext.toSMT
            rw [hΔ_ext_v]; simp
          obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hToSMT_isSome
          refine ⟨d, hd, ?_⟩
          have hd' := hd
          rw [B.RenamingContext.toSMT, Option.pure_def, Option.bind_eq_bind,
            hΔ_ext_v, Option.bind_some] at hd'
          have hd_inj := Option.some_injective _ hd'
          have hd_ty : d.snd.fst = (τ.get vs.length ⟨vs.idxOf v, hv_idx⟩).toSMTType := by
            rw [← hd_inj]
          have hτs_len : τs.length = vs.length := by rw [τs_eq]; exact fromProdl_length_of_hasArity τ_hasArity
          have hv_idx_τ : vs.idxOf v < τs.length := hτs_len ▸ hv_idx
          have h_St₃ : St₃.types.lookup v = some τs[vs.idxOf v] := by
            have h := foldl_insert_lookup_zip (Γ := St₂.types) vs_nodup hv_idx hv_idx_τ
            rwa [← St₃_types, List.getElem_idxOf hv_idx] at h
          have hσ_v_eq : τs[vs.idxOf v]'hv_idx_τ = σ_v :=
            Option.some_inj.mp (h_St₃.symm.trans hτ_v)
          rw [hd_ty, ← hσ_v_eq]
          have h := toSMTType_get_eq_fromProdl_getElem τ_hasArity hv_idx
          rw [h]
          have : τs[vs.idxOf v]'hv_idx_τ
              = (τ.toSMTType.fromProdl (vs.length - 1))[vs.idxOf v]'(τs_eq ▸ hv_idx_τ) := by
            congr 1
          exact this.symm
        · have hv_all : v ∈ B.fv (Term.all vs D P) := by
            rw [B.fv]; rw [List.mem_append]; right
            rw [List.mem_removeAll_iff]; exact ⟨hv, hvs⟩
          have hΔ_ext_eq : Δ_ext v = «Δ» v := by
            rw [Δ_ext_def, Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup, dif_neg hvs]
          have hToSMT_eq : (B.RenamingContext.toSMT Δ_ext) v
              = (B.RenamingContext.toSMT «Δ») v := by
            unfold B.RenamingContext.toSMT
            rw [hΔ_ext_eq]
          have hv_Λ : v ∈ St₀.types := fv_in_Λ v hv_all
          obtain ⟨τ', hτ'⟩ := Option.isSome_iff_exists.mp (AList.lookup_isSome.mpr hv_Λ)
          have hτ'_St₁ : St₁.types.lookup v = some τ' :=
            AList.lookup_of_subset St₀_sub_St₁ hτ'
          have hτ'_St₂ : St₂.types.lookup v = some τ' := by
            rw [St₂_types]; exact hτ'_St₁
          have hτ'_St₃ : St₃.types.lookup v = some τ' := by
            rw [St₃_types]
            apply foldl_insert_preserves_lookup hτ'_St₂
            intro p hp heq
            exact hvs (heq ▸ (List.of_mem_zip hp).1)
          have hσ_v_eq : τ' = σ_v :=
            Option.some_inj.mp (hτ'_St₃.symm.trans hτ_v)
          rw [hσ_v_eq] at hτ'
          rw [hToSMT_eq]
          exact respects hv_all hτ')
      (by
        intro v hv
        by_cases hvs : v ∈ vs
        · have hv_idx : vs.idxOf v < vs.length := List.idxOf_lt_length_of_mem hvs
          have hτs_len : τs.length = vs.length := by rw [τs_eq]; exact fromProdl_length_of_hasArity τ_hasArity
          have hv_idx_τ : vs.idxOf v < τs.length := hτs_len ▸ hv_idx
          have h_St₃ : St₃.types.lookup v = some τs[vs.idxOf v] := by
            have h := foldl_insert_lookup_zip (Γ := St₂.types) vs_nodup hv_idx hv_idx_τ
            rwa [← St₃_types, List.getElem_idxOf hv_idx] at h
          exact AList.lookup_isSome.mp (Option.isSome_of_mem h_St₃)
        · have hv_all : v ∈ B.fv (Term.all vs D P) := by
            rw [B.fv]; rw [List.mem_append]; right
            rw [List.mem_removeAll_iff]; exact ⟨hv, hvs⟩
          have hv_Λ : v ∈ St₀.types := fv_in_Λ v hv_all
          have hv_St₁ : v ∈ St₁.types := AList.mem_of_subset St₀_sub_St₁ hv_Λ
          obtain ⟨τ', hτ'⟩ := Option.isSome_iff_exists.mp (AList.lookup_isSome.mpr hv_St₁)
          have hτ'_St₂ : St₂.types.lookup v = some τ' := by
            rw [St₂_types]; exact hτ'
          have hτ'_St₃ : St₃.types.lookup v = some τ' := by
            rw [St₃_types]
            apply foldl_insert_preserves_lookup hτ'_St₂
            intro p hp heq
            exact hvs (heq ▸ (List.of_mem_zip hp).1)
          exact AList.lookup_isSome.mp (Option.isSome_of_mem hτ'_St₃))
    rename_i out_P
    obtain ⟨P_enc, σP⟩ := out_P
    mrename_i pre
    mintro ∀St₄
    mpure pre
    obtain ⟨St₃_sub_St₄, St₃_sub_St₄_types, St₄_keys_sub, covers_P, rfl, typ_P_enc,
      P_preserves_types,
      Δ_P, Δ_P_covers, Δ_P_extends, Δ_P_src_ext, Δ_P_none, denP', den_P_enc, P_RDom,
      P_enc_total⟩ := pre
    have Δ_P_wt : ∀ v (d : SMT.Dom), Δ_P v = some d →
        ∀ τ_v, St₄.types.lookup v = some τ_v → d.snd.fst = τ_v :=
      SMT.RenamingContext.ExtendsOnSourceFV.wt Δ_P_src_ext typ_P_enc
    have Δ_P_dom : ∀ v, Δ_P v ≠ none → v ∈ St₄.types := fun v hv =>
      fv_sub_typings typP typ_P_enc v
        (SMT.RenamingContext.ExtendsOnSourceFV.dom_sub_B_fv Δ_P_src_ext v hv)
    simp only [BType.toSMTType] at *
    mspec SMT.freshVarList_spec τs
    rename_i zs
    mrename_i pre
    mintro ∀St₅
    mpure pre
    obtain ⟨zs_len, zs_nodup, zs_not_used, zs_not_types, St₅_fvc, St₅_used, St₅_types⟩ := pre
    have zs_nemp : zs ≠ [] := zs_nemp_helper zs_len vs_τs_len vs_nemp
    have zs_typing := zs_typing_helper (St₅types := St₅.types) zs_nodup zs_len St₅_types
    have toPairl_typ : St₅.types ⊢ˢ (zs.map SMT.Term.var).toPairl : τs.toProdl :=
      toPairl_typ_helper zs_len zs_nemp zs_typing
    obtain ⟨vs_not_D_fv, vs_disj_St₁⟩ :=
      vs_disj_St₁_helper (P := P) typ_D vs_Γ_disj Λ_inv vars_used_vs D_preserves_types bv_nodup
    obtain ⟨St₁_sub_St₂_types, St₂_sub_St₃_types, St₄_sub_St₅_types, St₁_sub_St₅_types⟩ :=
      St_chain_helper vs_nodup zs_nodup St₂_types St₃_types St₅_types
        St₃_sub_St₄_types vs_disj_St₁ zs_not_types
    have typ_D_enc_St₅ : St₅.types ⊢ˢ D_enc : τ.toSMTType.fun SMTType.bool :=
      SMT.Typing.weakening St₁_sub_St₅_types typ_D_enc
    have τs_toProdl_eq : τs.toProdl = τ.toSMTType := by
      rw [τs_eq]
      have h_arith : (τ.toSMTType.fromProdl (vs.length - 1)).length = vs.length - 1 + 1 := by
        rw [← hlen_eq]
        have := List.length_pos_of_ne_nil vs_nemp
        omega
      exact SMT.SMTType.fromProdl_toProdl_roundtrip _ _ h_arith
    unfold castMembership
    simp only [bind_pure_comp]
    rw [dif_pos τs_toProdl_eq]
    mspec Std.Do.Spec.pure
    mspec Std.Do.Spec.get_StateT
    mspec Std.Do.Spec.modifyGet_StateT
    beta_reduce
    mspec Std.Do.Spec.map
    mspec SMT.eraseVars_forIn_spec (vars := zs)
    mrename_i pre_e2
    mintro ∀St₈
    mpure pre_e2
    obtain ⟨St₈_types, St₈_fvc, St₈_used⟩ := pre_e2
    mpure_intro
    -- Used chain: used = St₀.used ⊆ St₁.used ⊆ St₂.used ⊆ St₃.used ⊆ St₅.used = St₈.used
    have St₁_sub_St₂_used : St₁.env.usedVars ⊆ St₂.env.usedVars := by
      rw [St₂_used]; exact fun _ h => h
    have St₂_sub_St₃_used : St₂.env.usedVars ⊆ St₃.env.usedVars := by
      intro v hv
      rw [St₃_used]
      suffices h : ∀ (l : List (SMT.𝒱 × SMTType)) (acc : List SMT.𝒱),
          v ∈ acc → v ∈ l.foldl (fun used p => p.1 :: used) acc from h _ _ hv
      intro l; induction l with
      | nil => intro acc hmem; exact hmem
      | cons p ps ih => intro acc hmem; exact ih _ (List.mem_cons_of_mem _ hmem)
    have St₃_sub_St₅_used : St₃.env.usedVars ⊆ St₅.env.usedVars := by
      intro v hv
      rw [St₅_used]
      exact List.mem_append_right _ (St₃_sub_St₄ hv)
    have St₅_sub_St₈_used : St₅.env.usedVars ⊆ St₈.env.usedVars := by
      rw [St₈_used]; exact fun _ h => h
    have St₁_sub_St₈_used : St₁.env.usedVars ⊆ St₈.env.usedVars := fun v hv =>
      St₅_sub_St₈_used (St₃_sub_St₅_used (St₂_sub_St₃_used (St₁_sub_St₂_used hv)))
    -- Types subset chains
    have St₁_sub_St₄_types : St₁.types ⊆ St₄.types :=
      AList.subset_trans St₁_sub_St₂_types
        (AList.subset_trans St₂_sub_St₃_types St₃_sub_St₄_types)
    have St₀_sub_St₄_types : St₀.types ⊆ St₄.types :=
      AList.subset_trans St₀_sub_St₁ St₁_sub_St₄_types
    have St₀_sub_St₅_types : St₀.types ⊆ St₅.types :=
      AList.subset_trans St₀_sub_St₄_types St₄_sub_St₅_types
    have zs_not_St₀ : ∀ z ∈ zs, z ∉ St₀.types := fun z hz hz_St₀ =>
      zs_not_types z hz (AList.mem_of_subset St₀_sub_St₄_types hz_St₀)
    refine ⟨?_, ?_, ?_, ?_, trivial, ?_, ?_, ?_⟩
    · -- 1. used ⊆ St₈.env.usedVars
      exact fun v hv => St₁_sub_St₈_used (used_sub_St₁ hv)
    · -- 2. St₀.types ⊆ St₈.types
      intro ⟨k, τ_k⟩ hk_St₀
      have hk_St₃ : ⟨k, τ_k⟩ ∈ St₃.types.entries := by
        have h1 : ⟨k, τ_k⟩ ∈ St₁.types.entries := St₀_sub_St₁ hk_St₀
        have h2 : ⟨k, τ_k⟩ ∈ St₂.types.entries := St₁_sub_St₂_types h1
        exact St₂_sub_St₃_types h2
      have hk_St₀_mem : k ∈ St₀.types :=
        AList.mem_keys.mpr (List.mem_map.mpr ⟨⟨k, τ_k⟩, hk_St₀, rfl⟩)
      have hk_not_zs : k ∉ zs := fun hk_zs => zs_not_St₀ k hk_zs hk_St₀_mem
      rw [St₈_types]
      exact AList.mem_foldl_erase_of_not_mem_keys hk_St₃ hk_not_zs
    · -- 3. AList.keys St₈.types ⊆ St₈.env.usedVars
      intro v hv
      obtain ⟨τ_v, hτ_v⟩ := Option.isSome_iff_exists.mp (AList.lookup_isSome.mpr hv)
      have h_St₈ : ⟨v, τ_v⟩ ∈ St₈.types.entries := AList.mem_lookup_iff.1 hτ_v
      rw [St₈_types] at h_St₈
      have h_St₃ : ⟨v, τ_v⟩ ∈ St₃.types.entries :=
        AList.foldl_erase_entries_subset zs _ h_St₈
      have hv_St₃ : v ∈ St₃.types :=
        AList.mem_keys.mpr (List.mem_map.mpr ⟨⟨v, τ_v⟩, h_St₃, rfl⟩)
      exact St₅_sub_St₈_used (St₃_sub_St₅_used (St₃_keys_sub hv_St₃))
    · -- 4. CoversUsedVars St₈.env.usedVars (Term.all vs D P)
      intro v hv
      rw [B.fv, List.mem_append] at hv
      rcases hv with hv_D | hv_P
      · have hv_used_D : v ∈ St₁.env.usedVars := covers_D v hv_D
        exact St₁_sub_St₈_used hv_used_D
      · rw [List.mem_removeAll_iff] at hv_P
        obtain ⟨hv_fv_P, _⟩ := hv_P
        have hv_used_P : v ∈ St₄.env.usedVars := covers_P v hv_fv_P
        have hv_used_St₅ : v ∈ St₅.env.usedVars := by
          rw [St₅_used]; exact List.mem_append_right _ hv_used_P
        exact St₅_sub_St₈_used hv_used_St₅
    · exact SMT.encoder_all_result_well_typed _ _ _ _
    · -- 7. preservation
      intro v v_used v_not_St₀ v_not_vars
      intro hv_St₈
      obtain ⟨τ_v, hτ_v⟩ := Option.isSome_iff_exists.mp (AList.lookup_isSome.mpr hv_St₈)
      have h_St₈ : ⟨v, τ_v⟩ ∈ St₈.types.entries := AList.mem_lookup_iff.1 hτ_v
      rw [St₈_types] at h_St₈
      have h_St₃ : ⟨v, τ_v⟩ ∈ St₃.types.entries :=
        AList.foldl_erase_entries_subset zs _ h_St₈
      have hv_St₃ : v ∈ St₃.types :=
        AList.mem_keys.mpr (List.mem_map.mpr ⟨⟨v, τ_v⟩, h_St₃, rfl⟩)
      by_cases hv_vs : v ∈ vs
      · apply v_not_vars
        unfold B.Term.vars; rw [List.mem_union_iff]; right
        simp only [B.bv, List.mem_append]; left; left; exact hv_vs
      · have hv_St₁ : v ∈ St₁.types := by
          rw [St₃_types, St₂_types] at hv_St₃
          exact AList.mem_of_mem_foldl_insert' hv_St₃ (by
            intro h
            rw [List.mem_map] at h
            obtain ⟨⟨a, b⟩, hab, rfl⟩ := h
            exact hv_vs (List.of_mem_zip hab).1)
        have hv_vars_D : v ∈ B.Term.vars D := by
          by_contra h
          exact absurd hv_St₁ (D_preserves_types v v_used v_not_St₀ h)
        apply v_not_vars
        unfold B.Term.vars at hv_vars_D ⊢
        rw [List.mem_union_iff] at hv_vars_D ⊢
        rcases hv_vars_D with h_fv_D | h_bv_D
        · left; simp only [B.fv, List.mem_append]; left; exact h_fv_D
        · right; simp only [B.bv, List.mem_append]; left; right; exact h_bv_D
    · -- 8. ∃ Δ' ...
      have St₄_sub_St₈_used : St₄.env.usedVars ⊆ St₈.env.usedVars := by
        intro v hv
        have : v ∈ St₅.env.usedVars := by rw [St₅_used]; exact List.mem_append_right _ hv
        exact St₅_sub_St₈_used this
      -- Δ_D_ext extends Δ_D (since vs ∉ Δ_D's source by vs_disj_St₁)
      have Δ_D_ext_extends : SMT.RenamingContext.Extends Δ_D_ext Δ_D := by
        intro v d hv
        rw [Δ_D_ext_def]
        have hv_not_vs : v ∉ vs := by
          intro hvs
          exact vs_disj_St₁ v hvs (Δ_D_dom v (Option.ne_none_iff_exists.mpr ⟨d, hv.symm⟩))
        rw [Function.updates_of_not_mem _ _ _ _ hv_not_vs]
        exact hv
      have Δ_P_extends_Δ₀ : SMT.RenamingContext.Extends Δ_P Δ₀ := fun v d hv =>
        Δ_P_extends (Δ_D_ext_extends (Δ_D_extends hv))
      have hΔ_ext_outside : ∀ v ∉ vs, Δ_ext v = «Δ» v := fun v hv => by
        rw [Δ_ext_def]; exact Function.updates_of_not_mem «Δ» vs _ v hv
      have hΔ_D_ext_outside : ∀ v ∉ vs, Δ_D_ext v = Δ_D v := fun v hv => by
        rw [Δ_D_ext_def]; exact Function.updates_of_not_mem Δ_D vs _ v hv
      set imp_body : SMT.Term :=
        (List.foldr (fun x t => Term.forall [x.1] [x.2] t)
          (List.foldr (fun x1 x2 => x1 ⇒ˢ x2)
            ((@ˢD_enc) (List.map SMT.Term.var zs).toPairl ⇒ˢ
              SMT.substList vs (List.map SMT.Term.var zs) P_enc)
            (List.filterMap
              (fun x => match x with
                | Instr.define_fun v SMTType.unit SMTType.bool b => some b
                | _ => none)
              (List.drop (List.length St₃.env.declarations) St₅.env.declarations)))
          (List.filterMap
            (fun x => match x with
              | Instr.declare_const v τ => some (v, τ)
              | _ => none)
            (List.drop (List.length St₃.env.declarations) St₅.env.declarations)))
        with imp_body_def
      have fv_foldr_forall : ∀ (xs : List (SMT.𝒱 × SMTType)) (base : SMT.Term) v,
          v ∈ SMT.fv (List.foldr (fun x t => Term.forall [x.1] [x.2] t) base xs) →
          v ∈ SMT.fv base ∧ v ∉ xs.map (·.1) := by
        intro xs base v
        induction xs with
        | nil => intro hv; refine ⟨hv, ?_⟩; simp
        | cons x xs ih =>
          intro hv
          simp only [List.foldr, SMT.fv, List.mem_removeAll_iff,
            List.mem_singleton] at hv
          obtain ⟨hv_t, hv_ne⟩ := hv
          have ⟨hv_base, hv_not_xs⟩ := ih hv_t
          refine ⟨hv_base, ?_⟩
          simp only [List.map_cons, List.mem_cons]
          exact fun h => h.elim hv_ne hv_not_xs
      have fv_foldr_imp : ∀ (ts : List SMT.Term) (base : SMT.Term) v,
          v ∈ SMT.fv (List.foldr (fun x1 x2 => x1 ⇒ˢ x2) base ts) →
          v ∈ SMT.fv base ∨ ∃ t ∈ ts, v ∈ SMT.fv t := by
        intro ts base v
        induction ts with
        | nil => intro hv; exact Or.inl hv
        | cons t ts ih =>
          intro hv
          simp only [List.foldr, SMT.fv, List.mem_append] at hv
          rcases hv with hv_t | hv_rest
          · exact Or.inr ⟨t, List.mem_cons_self, hv_t⟩
          · rcases ih hv_rest with h | ⟨t', ht', hv_t'⟩
            · exact Or.inl h
            · exact Or.inr ⟨t', List.mem_cons_of_mem _ ht', hv_t'⟩
      -- Δ_P covers fv P_enc, and via Δ_D_extends_Δ_P, covers fv D_enc.
      have hcov_D : SMT.RenamingContext.CoversFV Δ_P D_enc := by
        intro v hv_D
        have hD_some : (Δ_D v).isSome = true := Δ_D_covers v hv_D
        obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hD_some
        have : Δ_D_ext v = some d := Δ_D_ext_extends hd
        have : Δ_P v = some d := Δ_P_extends this
        rw [this]; rfl
      have hcov : RenamingContext.CoversFV Δ_P (Term.forall zs τs imp_body) := by
        intro v hv
        simp only [SMT.fv, List.mem_removeAll_iff] at hv
        obtain ⟨hv_body, hv_not_zs⟩ := hv
        have ⟨hv_inner, hv_not_ex⟩ := fv_foldr_forall _ _ v hv_body
        rcases fv_foldr_imp _ _ v hv_inner with hv_base | ⟨sb, hsb_mem, hv_sb⟩
        · -- v ∈ fv base = fv (D_enc.app zs.toPairl ⇒ˢ substList vs (zs.map .var) P_enc)
          simp only [SMT.fv, List.mem_append] at hv_base
          rcases hv_base with (hv_D | hv_pairl) | hv_subst
          · exact hcov_D v hv_D
          · -- v ∈ fv (zs.map .var).toPairl ⊆ zs
            exact absurd (fv_pairl_sub_zs_helper zs v hv_pairl) hv_not_zs
          · -- v ∈ fv (substList vs (zs.map .var) P_enc)
            rcases SMT_mem_fv_substList hv_subst with hv_P | ⟨t, ht, hv_t⟩
            · exact Δ_P_covers v hv_P
            · rw [List.mem_map] at ht
              obtain ⟨z, hz, rfl⟩ := ht
              simp only [SMT.fv, List.mem_singleton] at hv_t
              exact absurd (hv_t ▸ hz) hv_not_zs
        · -- v ∈ fv spec_body: use scoping axiom
          have h_in_decls : ∃ name, .define_fun name SMTType.unit SMTType.bool sb ∈
              (St₅.env.declarations).drop (St₃.env.declarations).length := by
            rw [List.mem_filterMap] at hsb_mem
            obtain ⟨inst, h_inst_mem, h_inst_eq⟩ := hsb_mem
            match inst, h_inst_eq with
            | .define_fun name SMTType.unit SMTType.bool b, h =>
              simp only [Option.some.injEq] at h
              exact ⟨name, h ▸ h_inst_mem⟩
          rcases SMT.encoder_spec_body_fv_in_ex_binders_or_renaming
            St₃.env.declarations St₅.env.declarations Δ_P sb v h_in_decls hv_sb with
            h_ex | h_Δ
          · exact absurd h_ex hv_not_ex
          · exact h_Δ
      refine ⟨Δ_P, hcov, ?_, ?_, ?_, ?_⟩
      · exact Δ_P_extends_Δ₀
      · -- ExtendsOnSourceFV Δ_P Δ (Term.all vs D P)
        intro v d hv_eq
        have hv_fv : v ∈ B.fv (Term.all vs D P) := by
          by_contra hv_not
          have : B.RenamingContext.toSMTOnFV «Δ» (Term.all vs D P) v = none := by
            simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
              B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_not]
          rw [this] at hv_eq; exact absurd hv_eq (by simp)
        simp only [B.fv, List.mem_append] at hv_fv
        rcases hv_fv with hv_fvD | hv_fvP_minus_vs
        · -- v ∈ B.fv D
          have h_toSMT_D : B.RenamingContext.toSMTOnFV «Δ» D v =
              B.RenamingContext.toSMTOnFV «Δ» (Term.all vs D P) v := by
            simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
              B.RenamingContext.restrictToFV_eq_of_mem hv_fvD,
              B.RenamingContext.restrictToFV_eq_of_mem (fv.mem_all (.inl hv_fvD))]
          have : Δ_D v = some d := Δ_D_src_ext (h_toSMT_D ▸ hv_eq)
          have : Δ_D_ext v = some d := Δ_D_ext_extends this
          exact Δ_P_extends this
        · -- v ∈ (B.fv P).removeAll vs
          rw [List.mem_removeAll_iff] at hv_fvP_minus_vs
          obtain ⟨hv_fvP, hv_not_vs⟩ := hv_fvP_minus_vs
          have hΔ_ext_eq : Δ_ext v = «Δ» v := hΔ_ext_outside v hv_not_vs
          have h_toSMT_P : B.RenamingContext.toSMTOnFV Δ_ext P v =
              B.RenamingContext.toSMTOnFV «Δ» (Term.all vs D P) v := by
            simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
              B.RenamingContext.restrictToFV_eq_of_mem hv_fvP,
              B.RenamingContext.restrictToFV_eq_of_mem (fv.mem_all (.inr ⟨hv_fvP, hv_not_vs⟩)),
              hΔ_ext_eq]
          exact Δ_P_src_ext (h_toSMT_P ▸ hv_eq)
      · exact fun v hv_out => Δ_P_none v (fun hv_in => hv_out (St₄_sub_St₈_used hv_in))
      · -- ∃ denT' + RDom + totality via passed-in witnesses
        obtain ⟨denT', hden_eq, hrdom⟩ :=
          existence_rdom_witness_hasflag hcov T hT
        refine ⟨denT', hden_eq, hrdom, ?_⟩
        intro Δ_alt Δ_fv_alt Δ₀_alt hext_alt hnone_alt hwt_alt T_alt hT_alt hden_alt
        exact totality_witness_hasflag (used' := St₈.env.usedVars) (Λ' := St₈.types) hcov
          Δ_alt Δ_fv_alt Δ₀_alt hext_alt hnone_alt hwt_alt T_alt hT_alt hden_alt
  · -- EMPTY 𝒟' case (no-flag): D denotes empty, all-quantification trivially true
    have h𝒟_eq : 𝒟 = 𝒟' := by
      have := den_D_eq ▸ den_D
      simp only [Option.some.injEq, PSigma.mk.injEq] at this
      exact this.1.symm
    have h𝒟_empty_eq : 𝒟 = ∅ := h𝒟_eq.trans h𝒟_empty
    let x_fin_default : Fin vs.length → B.Dom.{u} := fun i =>
      ⟨(τ.get vs.length i).defaultZFSet, ⟨τ.get vs.length i,
        BType.mem_toZFSet_of_defaultZFSet⟩⟩
    set Δ_ext : B.RenamingContext.Context :=
      Function.updates «Δ» vs (List.ofFn fun i => some (x_fin_default i)) with Δ_ext_def
    have Δ_fv_P := Δ_fv_P_helper vs_nodup Δ_ext_def D P Δ_fv
    classical
    by_cases hP_den_cond : ∃ (P_val : ZFSet.{u}) (hP_val : P_val ∈ ⟦BType.bool⟧ᶻ),
        ⟦P.abstract Δ_ext Δ_fv_P⟧ᴮ = some ⟨P_val, BType.bool, hP_val⟩
    · -- Phase A1: P denotes at default x_fin
      obtain ⟨P_val, hP_val, hP_den⟩ := hP_den_cond
      set Δ_D_ext : SMT.RenamingContext.Context :=
        Function.updates Δ_D vs (List.ofFn fun (i : Fin vs.length) =>
          B.RenamingContext.toSMT Δ_ext vs[i])
        with Δ_D_ext_def
      have Δ_D_ext_none_St₃ : ∀ v ∉ St₃.env.usedVars, Δ_D_ext v = none :=
        Δ_D_ext_none_helper (ΔDD := Δ_D) (ΔDDext := Δ_D_ext)
          (vs := vs) (vs_nodup := vs_nodup) (vs_τs_len := vs_τs_len)
          (used0 := St₁.env.usedVars) (used1 := St₂.env.usedVars)
          (used2 := St₃.env.usedVars)
          (St_used_def := St₃_used) (used1_eq_used0 := St₂_used)
          (ΔDDext_def := Δ_D_ext_def) (ΔDD_none_outside := Δ_D_none_St₃)
      have Δ₀_ext_P : RenamingContext.ExtendsOnSourceFV Δ_D_ext Δ_ext P :=
        Δ₀_ext_P_helper vs_nodup Δ_ext_def Δ_D_ext_def D P
          (lift := fun hv => Δ_D_extends (Δ₀_ext hv))
      mspec Std.Do.Spec.get_StateT
      mspec Std.Do.Spec.get_StateT
      mspec Std.Do.Spec.get_StateT
      mspec P_ih (E := E') (Λ := St₃.types) (α := .bool) typP
        («Δ» := Δ_ext) Δ_fv_P
        (Δ₀ := Δ_D_ext) Δ₀_ext_P (used := St₃.env.usedVars) Δ_D_ext_none_St₃
        (T := P_val) (hT := hP_val) hP_den vars_used_P_St₃ (n := St₃.env.freshvarsc)
        St₃_types_sub_E'_ctx_on_P_vars
        hP_bv_nodup
        (by
          intro v σ_v hv hτ_v
          by_cases hvs : v ∈ vs
          · have hv_idx : vs.idxOf v < vs.length := List.idxOf_lt_length_of_mem hvs
            have hΔ_ext_v : Δ_ext v = some (x_fin_default ⟨vs.idxOf v, hv_idx⟩) := by
              rw [Δ_ext_def, Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup, dif_pos hvs]
              simp only [List.getElem_ofFn]
            have hToSMT_isSome : (B.RenamingContext.toSMT Δ_ext v).isSome = true := by
              unfold B.RenamingContext.toSMT
              rw [hΔ_ext_v]; simp
            obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hToSMT_isSome
            refine ⟨d, hd, ?_⟩
            have hd' := hd
            rw [B.RenamingContext.toSMT, Option.pure_def, Option.bind_eq_bind,
              hΔ_ext_v, Option.bind_some] at hd'
            have hd_inj := Option.some_injective _ hd'
            have hd_ty : d.snd.fst = (τ.get vs.length ⟨vs.idxOf v, hv_idx⟩).toSMTType := by
              rw [← hd_inj]
            have hτs_len : τs.length = vs.length := by
              rw [τs_eq]; exact fromProdl_length_of_hasArity τ_hasArity
            have hv_idx_τ : vs.idxOf v < τs.length := hτs_len ▸ hv_idx
            have h_St₃ : St₃.types.lookup v = some τs[vs.idxOf v] := by
              have h := foldl_insert_lookup_zip (Γ := St₂.types) vs_nodup hv_idx hv_idx_τ
              rwa [← St₃_types, List.getElem_idxOf hv_idx] at h
            have hσ_v_eq : τs[vs.idxOf v]'hv_idx_τ = σ_v :=
              Option.some_inj.mp (h_St₃.symm.trans hτ_v)
            rw [hd_ty, ← hσ_v_eq]
            have h := toSMTType_get_eq_fromProdl_getElem τ_hasArity hv_idx
            rw [h]
            have : τs[vs.idxOf v]'hv_idx_τ
                = (τ.toSMTType.fromProdl (vs.length - 1))[vs.idxOf v]'(τs_eq ▸ hv_idx_τ) := by
              congr 1
            exact this.symm
          · have hv_all : v ∈ B.fv (Term.all vs D P) := by
              rw [B.fv]; rw [List.mem_append]; right
              rw [List.mem_removeAll_iff]; exact ⟨hv, hvs⟩
            have hΔ_ext_eq : Δ_ext v = «Δ» v := by
              rw [Δ_ext_def, Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup, dif_neg hvs]
            have hToSMT_eq : (B.RenamingContext.toSMT Δ_ext) v
                = (B.RenamingContext.toSMT «Δ») v := by
              unfold B.RenamingContext.toSMT
              rw [hΔ_ext_eq]
            have hv_Λ : v ∈ St₀.types := fv_in_Λ v hv_all
            obtain ⟨τ', hτ'⟩ := Option.isSome_iff_exists.mp (AList.lookup_isSome.mpr hv_Λ)
            have hτ'_St₁ : St₁.types.lookup v = some τ' :=
              AList.lookup_of_subset St₀_sub_St₁ hτ'
            have hτ'_St₂ : St₂.types.lookup v = some τ' := by
              rw [St₂_types]; exact hτ'_St₁
            have hτ'_St₃ : St₃.types.lookup v = some τ' := by
              rw [St₃_types]
              apply foldl_insert_preserves_lookup hτ'_St₂
              intro p hp heq
              exact hvs (heq ▸ (List.of_mem_zip hp).1)
            have hσ_v_eq : τ' = σ_v :=
              Option.some_inj.mp (hτ'_St₃.symm.trans hτ_v)
            rw [hσ_v_eq] at hτ'
            rw [hToSMT_eq]
            exact respects hv_all hτ')
        (by
          intro v hv
          by_cases hvs : v ∈ vs
          · have hv_idx : vs.idxOf v < vs.length := List.idxOf_lt_length_of_mem hvs
            have hτs_len : τs.length = vs.length := by
              rw [τs_eq]; exact fromProdl_length_of_hasArity τ_hasArity
            have hv_idx_τ : vs.idxOf v < τs.length := hτs_len ▸ hv_idx
            have h_St₃ : St₃.types.lookup v = some τs[vs.idxOf v] := by
              have h := foldl_insert_lookup_zip (Γ := St₂.types) vs_nodup hv_idx hv_idx_τ
              rwa [← St₃_types, List.getElem_idxOf hv_idx] at h
            exact AList.lookup_isSome.mp (Option.isSome_of_mem h_St₃)
          · have hv_all : v ∈ B.fv (Term.all vs D P) := by
              rw [B.fv]; rw [List.mem_append]; right
              rw [List.mem_removeAll_iff]; exact ⟨hv, hvs⟩
            have hv_Λ : v ∈ St₀.types := fv_in_Λ v hv_all
            have hv_St₁ : v ∈ St₁.types := AList.mem_of_subset St₀_sub_St₁ hv_Λ
            obtain ⟨τ', hτ'⟩ := Option.isSome_iff_exists.mp (AList.lookup_isSome.mpr hv_St₁)
            have hτ'_St₂ : St₂.types.lookup v = some τ' := by
              rw [St₂_types]; exact hτ'
            have hτ'_St₃ : St₃.types.lookup v = some τ' := by
              rw [St₃_types]
              apply foldl_insert_preserves_lookup hτ'_St₂
              intro p hp heq
              exact hvs (heq ▸ (List.of_mem_zip hp).1)
            exact AList.lookup_isSome.mp (Option.isSome_of_mem hτ'_St₃))
      rename_i out_P
      obtain ⟨P_enc, σP⟩ := out_P
      mrename_i pre
      mintro ∀St₄
      mpure pre
      obtain ⟨St₃_sub_St₄, St₃_sub_St₄_types, St₄_keys_sub, covers_P, rfl, typ_P_enc,
        P_preserves_types,
        Δ_P, Δ_P_covers, Δ_P_extends, Δ_P_src_ext, Δ_P_none, denP', den_P_enc, P_RDom,
        P_enc_total⟩ := pre
      simp only [BType.toSMTType] at *
      mspec SMT.freshVarList_spec τs
      rename_i zs
      mrename_i pre
      mintro ∀St₅
      mpure pre
      obtain ⟨zs_len, zs_nodup, zs_not_used, zs_not_types, St₅_fvc, St₅_used, St₅_types⟩ := pre
      have zs_nemp : zs ≠ [] := zs_nemp_helper zs_len vs_τs_len vs_nemp
      have zs_typing := zs_typing_helper (St₅types := St₅.types) zs_nodup zs_len St₅_types
      have toPairl_typ : St₅.types ⊢ˢ (zs.map SMT.Term.var).toPairl : τs.toProdl :=
        toPairl_typ_helper zs_len zs_nemp zs_typing
      obtain ⟨vs_not_D_fv, vs_disj_St₁⟩ :=
        vs_disj_St₁_helper (P := P) typ_D vs_Γ_disj Λ_inv vars_used_vs D_preserves_types bv_nodup
      obtain ⟨St₁_sub_St₂_types, St₂_sub_St₃_types, St₄_sub_St₅_types, St₁_sub_St₅_types⟩ :=
        St_chain_helper vs_nodup zs_nodup St₂_types St₃_types St₅_types
          St₃_sub_St₄_types vs_disj_St₁ zs_not_types
      have typ_D_enc_St₅ : St₅.types ⊢ˢ D_enc : τ.toSMTType.fun SMTType.bool :=
        SMT.Typing.weakening St₁_sub_St₅_types typ_D_enc
      have τs_toProdl_eq : τs.toProdl = τ.toSMTType := by
        rw [τs_eq]
        have h_arith : (τ.toSMTType.fromProdl (vs.length - 1)).length = vs.length - 1 + 1 := by
          rw [← hlen_eq]
          have := List.length_pos_of_ne_nil vs_nemp
          omega
        exact SMT.SMTType.fromProdl_toProdl_roundtrip _ _ h_arith
      unfold castMembership
      simp only [bind_pure_comp]
      rw [dif_pos τs_toProdl_eq]
      mspec Std.Do.Spec.pure
      mspec Std.Do.Spec.get_StateT
      mspec Std.Do.Spec.modifyGet_StateT
      beta_reduce
      mspec Std.Do.Spec.map
      mspec SMT.eraseVars_forIn_spec (vars := zs)
      mrename_i pre_e2
      mintro ∀St₈
      mpure pre_e2
      obtain ⟨St₈_types, St₈_fvc, St₈_used⟩ := pre_e2
      mpure_intro
      have St₁_sub_St₂_used : St₁.env.usedVars ⊆ St₂.env.usedVars := by
        rw [St₂_used]; exact fun _ h => h
      have St₂_sub_St₃_used : St₂.env.usedVars ⊆ St₃.env.usedVars := by
        intro v hv
        rw [St₃_used]
        suffices h : ∀ (l : List (SMT.𝒱 × SMTType)) (acc : List SMT.𝒱),
            v ∈ acc → v ∈ l.foldl (fun used p => p.1 :: used) acc from h _ _ hv
        intro l; induction l with
        | nil => intro acc hmem; exact hmem
        | cons p ps ih => intro acc hmem; exact ih _ (List.mem_cons_of_mem _ hmem)
      have St₃_sub_St₅_used : St₃.env.usedVars ⊆ St₅.env.usedVars := by
        intro v hv
        rw [St₅_used]
        exact List.mem_append_right _ (St₃_sub_St₄ hv)
      have St₅_sub_St₈_used : St₅.env.usedVars ⊆ St₈.env.usedVars := by
        rw [St₈_used]; exact fun _ h => h
      have St₁_sub_St₈_used : St₁.env.usedVars ⊆ St₈.env.usedVars := fun v hv =>
        St₅_sub_St₈_used (St₃_sub_St₅_used (St₂_sub_St₃_used (St₁_sub_St₂_used hv)))
      have St₁_sub_St₄_types : St₁.types ⊆ St₄.types :=
        AList.subset_trans St₁_sub_St₂_types
          (AList.subset_trans St₂_sub_St₃_types St₃_sub_St₄_types)
      have St₀_sub_St₄_types : St₀.types ⊆ St₄.types :=
        AList.subset_trans St₀_sub_St₁ St₁_sub_St₄_types
      have zs_not_St₀ : ∀ z ∈ zs, z ∉ St₀.types := fun z hz hz_St₀ =>
        zs_not_types z hz (AList.mem_of_subset St₀_sub_St₄_types hz_St₀)
      refine ⟨?_, ?_, ?_, ?_, trivial, ?_, ?_, ?_⟩
      · exact fun v hv => St₁_sub_St₈_used (used_sub_St₁ hv)
      · intro ⟨k, τ_k⟩ hk_St₀
        have hk_St₃ : ⟨k, τ_k⟩ ∈ St₃.types.entries := by
          have h1 : ⟨k, τ_k⟩ ∈ St₁.types.entries := St₀_sub_St₁ hk_St₀
          have h2 : ⟨k, τ_k⟩ ∈ St₂.types.entries := St₁_sub_St₂_types h1
          exact St₂_sub_St₃_types h2
        have hk_St₀_mem : k ∈ St₀.types :=
          AList.mem_keys.mpr (List.mem_map.mpr ⟨⟨k, τ_k⟩, hk_St₀, rfl⟩)
        have hk_not_zs : k ∉ zs := fun hk_zs => zs_not_St₀ k hk_zs hk_St₀_mem
        rw [St₈_types]
        exact AList.mem_foldl_erase_of_not_mem_keys hk_St₃ hk_not_zs
      · intro v hv
        obtain ⟨τ_v, hτ_v⟩ := Option.isSome_iff_exists.mp (AList.lookup_isSome.mpr hv)
        have h_St₈ : ⟨v, τ_v⟩ ∈ St₈.types.entries := AList.mem_lookup_iff.1 hτ_v
        rw [St₈_types] at h_St₈
        have h_St₃ : ⟨v, τ_v⟩ ∈ St₃.types.entries :=
          AList.foldl_erase_entries_subset zs _ h_St₈
        have hv_St₃ : v ∈ St₃.types :=
          AList.mem_keys.mpr (List.mem_map.mpr ⟨⟨v, τ_v⟩, h_St₃, rfl⟩)
        exact St₅_sub_St₈_used (St₃_sub_St₅_used (St₃_keys_sub hv_St₃))
      · intro v hv
        rw [B.fv, List.mem_append] at hv
        rcases hv with hv_D | hv_P
        · exact St₁_sub_St₈_used (covers_D v hv_D)
        · rw [List.mem_removeAll_iff] at hv_P
          obtain ⟨hv_fv_P, _⟩ := hv_P
          have hv_used_P : v ∈ St₄.env.usedVars := covers_P v hv_fv_P
          have hv_used_St₅ : v ∈ St₅.env.usedVars := by
            rw [St₅_used]; exact List.mem_append_right _ hv_used_P
          exact St₅_sub_St₈_used hv_used_St₅
      · exact SMT.encoder_all_result_well_typed _ _ _ _
      · intro v v_used v_not_St₀ v_not_vars hv_St₈
        obtain ⟨τ_v, hτ_v⟩ := Option.isSome_iff_exists.mp (AList.lookup_isSome.mpr hv_St₈)
        have h_St₈ : ⟨v, τ_v⟩ ∈ St₈.types.entries := AList.mem_lookup_iff.1 hτ_v
        rw [St₈_types] at h_St₈
        have h_St₃ : ⟨v, τ_v⟩ ∈ St₃.types.entries :=
          AList.foldl_erase_entries_subset zs _ h_St₈
        have hv_St₃ : v ∈ St₃.types :=
          AList.mem_keys.mpr (List.mem_map.mpr ⟨⟨v, τ_v⟩, h_St₃, rfl⟩)
        by_cases hv_vs : v ∈ vs
        · apply v_not_vars
          unfold B.Term.vars; rw [List.mem_union_iff]; right
          simp only [B.bv, List.mem_append]; left; left; exact hv_vs
        · have hv_St₁ : v ∈ St₁.types := by
            rw [St₃_types, St₂_types] at hv_St₃
            exact AList.mem_of_mem_foldl_insert' hv_St₃ (by
              intro h
              rw [List.mem_map] at h
              obtain ⟨⟨a, b⟩, hab, rfl⟩ := h
              exact hv_vs (List.of_mem_zip hab).1)
          have hv_vars_D : v ∈ B.Term.vars D := by
            by_contra h
            exact absurd hv_St₁ (D_preserves_types v v_used v_not_St₀ h)
          apply v_not_vars
          unfold B.Term.vars at hv_vars_D ⊢
          rw [List.mem_union_iff] at hv_vars_D ⊢
          rcases hv_vars_D with h_fv_D | h_bv_D
          · left; simp only [B.fv, List.mem_append]; left; exact h_fv_D
          · right; simp only [B.bv, List.mem_append]; left; right; exact h_bv_D
      · -- ∃ Δ' ...
        have St₄_sub_St₈_used : St₄.env.usedVars ⊆ St₈.env.usedVars := by
          intro v hv
          have : v ∈ St₅.env.usedVars := by rw [St₅_used]; exact List.mem_append_right _ hv
          exact St₅_sub_St₈_used this
        have Δ_D_ext_extends : SMT.RenamingContext.Extends Δ_D_ext Δ_D := by
          intro v d hv
          rw [Δ_D_ext_def]
          have hv_not_vs : v ∉ vs := by
            intro hvs
            exact vs_disj_St₁ v hvs (Δ_D_dom v (Option.ne_none_iff_exists.mpr ⟨d, hv.symm⟩))
          rw [Function.updates_of_not_mem _ _ _ _ hv_not_vs]
          exact hv
        have Δ_P_extends_Δ₀ : SMT.RenamingContext.Extends Δ_P Δ₀ := fun v d hv =>
          Δ_P_extends (Δ_D_ext_extends (Δ_D_extends hv))
        have hΔ_ext_outside : ∀ v ∉ vs, Δ_ext v = «Δ» v := fun v hv => by
          rw [Δ_ext_def]; exact Function.updates_of_not_mem «Δ» vs _ v hv
        set imp_body : SMT.Term :=
          (List.foldr (fun x t => Term.forall [x.1] [x.2] t)
            (List.foldr (fun x1 x2 => x1 ⇒ˢ x2)
              ((@ˢD_enc) (List.map SMT.Term.var zs).toPairl ⇒ˢ
                SMT.substList vs (List.map SMT.Term.var zs) P_enc)
              (List.filterMap
                (fun x => match x with
                  | Instr.define_fun v SMTType.unit SMTType.bool b => some b
                  | _ => none)
                (List.drop (List.length St₃.env.declarations) St₅.env.declarations)))
            (List.filterMap
              (fun x => match x with
                | Instr.declare_const v τ => some (v, τ)
                | _ => none)
              (List.drop (List.length St₃.env.declarations) St₅.env.declarations)))
          with imp_body_def
        have fv_foldr_forall : ∀ (xs : List (SMT.𝒱 × SMTType)) (base : SMT.Term) v,
            v ∈ SMT.fv (List.foldr (fun x t => Term.forall [x.1] [x.2] t) base xs) →
            v ∈ SMT.fv base ∧ v ∉ xs.map (·.1) := by
          intro xs base v
          induction xs with
          | nil => intro hv; refine ⟨hv, ?_⟩; simp
          | cons x xs ih =>
            intro hv
            simp only [List.foldr, SMT.fv, List.mem_removeAll_iff,
              List.mem_singleton] at hv
            obtain ⟨hv_t, hv_ne⟩ := hv
            have ⟨hv_base, hv_not_xs⟩ := ih hv_t
            refine ⟨hv_base, ?_⟩
            simp only [List.map_cons, List.mem_cons]
            exact fun h => h.elim hv_ne hv_not_xs
        have fv_foldr_imp : ∀ (ts : List SMT.Term) (base : SMT.Term) v,
            v ∈ SMT.fv (List.foldr (fun x1 x2 => x1 ⇒ˢ x2) base ts) →
            v ∈ SMT.fv base ∨ ∃ t ∈ ts, v ∈ SMT.fv t := by
          intro ts base v
          induction ts with
          | nil => intro hv; exact Or.inl hv
          | cons t ts ih =>
            intro hv
            simp only [List.foldr, SMT.fv, List.mem_append] at hv
            rcases hv with hv_t | hv_rest
            · exact Or.inr ⟨t, List.mem_cons_self, hv_t⟩
            · rcases ih hv_rest with h | ⟨t', ht', hv_t'⟩
              · exact Or.inl h
              · exact Or.inr ⟨t', List.mem_cons_of_mem _ ht', hv_t'⟩
        have hcov_D : SMT.RenamingContext.CoversFV Δ_P D_enc := by
          intro v hv_D
          have hD_some : (Δ_D v).isSome = true := Δ_D_covers v hv_D
          obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hD_some
          have : Δ_D_ext v = some d := Δ_D_ext_extends hd
          have : Δ_P v = some d := Δ_P_extends this
          rw [this]; rfl
        have hcov : RenamingContext.CoversFV Δ_P (Term.forall zs τs imp_body) := by
          intro v hv
          simp only [SMT.fv, List.mem_removeAll_iff] at hv
          obtain ⟨hv_body, hv_not_zs⟩ := hv
          have ⟨hv_inner, hv_not_ex⟩ := fv_foldr_forall _ _ v hv_body
          rcases fv_foldr_imp _ _ v hv_inner with hv_base | ⟨sb, hsb_mem, hv_sb⟩
          · simp only [SMT.fv, List.mem_append] at hv_base
            rcases hv_base with (hv_D | hv_pairl) | hv_subst
            · exact hcov_D v hv_D
            · exact absurd (fv_pairl_sub_zs_helper zs v hv_pairl) hv_not_zs
            · rcases SMT_mem_fv_substList hv_subst with hv_P | ⟨t, ht, hv_t⟩
              · exact Δ_P_covers v hv_P
              · rw [List.mem_map] at ht
                obtain ⟨z, hz, rfl⟩ := ht
                simp only [SMT.fv, List.mem_singleton] at hv_t
                exact absurd (hv_t ▸ hz) hv_not_zs
          · have h_in_decls : ∃ name, .define_fun name SMTType.unit SMTType.bool sb ∈
                (St₅.env.declarations).drop (St₃.env.declarations).length := by
              rw [List.mem_filterMap] at hsb_mem
              obtain ⟨inst, h_inst_mem, h_inst_eq⟩ := hsb_mem
              match inst, h_inst_eq with
              | .define_fun name SMTType.unit SMTType.bool b, h =>
                simp only [Option.some.injEq] at h
                exact ⟨name, h ▸ h_inst_mem⟩
            rcases SMT.encoder_spec_body_fv_in_ex_binders_or_renaming
              St₃.env.declarations St₅.env.declarations Δ_P sb v h_in_decls hv_sb with
              h_ex | h_Δ
            · exact absurd h_ex hv_not_ex
            · exact h_Δ
        refine ⟨Δ_P, hcov, ?_, ?_, ?_, ?_⟩
        · exact Δ_P_extends_Δ₀
        · -- ExtendsOnSourceFV Δ_P Δ (Term.all vs D P)
          intro v d hv_eq
          have hv_fv : v ∈ B.fv (Term.all vs D P) := by
            by_contra hv_not
            have : B.RenamingContext.toSMTOnFV «Δ» (Term.all vs D P) v = none := by
              simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_not]
            rw [this] at hv_eq; exact absurd hv_eq (by simp)
          simp only [B.fv, List.mem_append] at hv_fv
          rcases hv_fv with hv_fvD | hv_fvP_minus_vs
          · have h_toSMT_D : B.RenamingContext.toSMTOnFV «Δ» D v =
                B.RenamingContext.toSMTOnFV «Δ» (Term.all vs D P) v := by
              simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                B.RenamingContext.restrictToFV_eq_of_mem hv_fvD,
                B.RenamingContext.restrictToFV_eq_of_mem (fv.mem_all (.inl hv_fvD))]
            have h1 : Δ_D v = some d := Δ_D_src_ext (h_toSMT_D ▸ hv_eq)
            exact Δ_P_extends (Δ_D_ext_extends h1)
          · rw [List.mem_removeAll_iff] at hv_fvP_minus_vs
            obtain ⟨hv_fvP, hv_not_vs⟩ := hv_fvP_minus_vs
            have hΔ_ext_eq : Δ_ext v = «Δ» v := hΔ_ext_outside v hv_not_vs
            have h_toSMT_P : B.RenamingContext.toSMTOnFV Δ_ext P v =
                B.RenamingContext.toSMTOnFV «Δ» (Term.all vs D P) v := by
              simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                B.RenamingContext.restrictToFV_eq_of_mem hv_fvP,
                B.RenamingContext.restrictToFV_eq_of_mem (fv.mem_all (.inr ⟨hv_fvP, hv_not_vs⟩)),
                hΔ_ext_eq]
            exact Δ_P_src_ext (h_toSMT_P ▸ hv_eq)
        · exact fun v hv_out => Δ_P_none v (fun hv_in => hv_out (St₄_sub_St₈_used hv_in))
        · -- ∃ denT' + RDom + totality via passed-in witnesses
          obtain ⟨denT', hden_eq, hrdom⟩ :=
            existence_rdom_witness_hasflag hcov T hT
          refine ⟨denT', hden_eq, hrdom, ?_⟩
          intro Δ_alt Δ_fv_alt Δ₀_alt hext_alt hnone_alt hwt_alt T_alt hT_alt hden_alt
          exact totality_witness_hasflag (used' := St₈.env.usedVars) (Λ' := St₈.types) hcov
            Δ_alt Δ_fv_alt Δ₀_alt hext_alt hnone_alt hwt_alt T_alt hT_alt hden_alt
    · -- Phase A2: P doesn't denote at default → contradiction via B-side totality
      exfalso
      apply hP_den_cond
      exact B.denote_exists_of_typing typP Δ_ext Δ_fv_P (@WFTC.wf _ WFTC.of_abstract)
