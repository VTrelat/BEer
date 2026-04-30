import SMT.Reasoning.Basic.CollectCaseHelpers
import SMT.Reasoning.Basic.AllCaseHelpers
import SMT.Reasoning.Basic.CastMembershipSpec
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
                                                (∀ v ∈ used, v ∉ Λ → v ∉ B.fv D → v ∉ Γ') ∧
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
                                                (∀ v ∈ used, v ∉ Λ → v ∉ B.fv P → v ∉ Γ') ∧
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
                        (∀ v ∈ used, v ∉ Λ → v ∉ B.fv (Term.all vs D P) → v ∉ Γ') ∧
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
  have den_t_saved := den_t
  -- Extract D denotation from den_t by unfolding `all` semantics.
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
      (⟨_, WFTC.of_abstract, .set τ, by convert Typing.of_abstract Δ_fv_D typ_D⟩)
      den_D_eq
    exact h_wt.symm
  subst rfl_τ'
  have den_D_exists : ∃ (𝒟 : ZFSet) (h𝒟 : 𝒟 ∈ ⟦τ.set⟧ᶻ),
    ⟦D.abstract «Δ» Δ_fv_D⟧ᴮ = some ⟨𝒟, ⟨τ.set, h𝒟⟩⟩ :=
    ⟨𝒟', h𝒟', den_D_eq⟩
  obtain ⟨𝒟, h𝒟, den_D⟩ := den_D_exists
  rw [encodeTerm]
  have St₀_types_sub_E_ctx_on_D_vars : ∀ v ∈ D.vars, v ∈ St₀.types → v ∈ E.context := by
    intro v v_in_D_vars v_in_St₀_types
    apply Λ_inv v _ v_in_St₀_types
    simp only [Term.vars, List.mem_union_iff, B.fv, B.bv, List.append_assoc, List.mem_append,
      List.mem_removeAll_iff] at v_in_D_vars ⊢
    rcases v_in_D_vars with hv | hv
    · left; left; exact hv
    · right; right; left; exact hv
  mspec D_ih (E := E) (Λ := St₀.types) (α := .set τ) typ_D
      («Δ» := «Δ») Δ_fv_D
      (Δ₀ := Δ₀) Δ₀_ext_D (used := used) Δ₀_none_out (T := 𝒟) (hT := h𝒟)
      den_D vars_used_D (n := St₀.env.freshvarsc)
      St₀_types_sub_E_ctx_on_D_vars
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
  have denD'_type : denD'.2.fst = τ.set.toSMTType := D_RDom.1.1
  have denD'_retract : retract (BType.set τ) denD'.1 = 𝒟 := D_RDom.1.2
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
  · -- HAS-FLAG BRANCH (structurally similar to no-flag but with non-reflexive castMembership).
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
        · have v_fv_D : v ∈ B.fv D := by
            by_contra h
            exact absurd v_in_St₁ (D_preserves_types v v_used v_St₀ h)
          exact AList.lookup_isSome.mp (B.Typing.mem_context_of_mem_fv typ_D v_fv_D)
    -- Has-flag branch: mirrors no-flag scaffold below but uses the non-reflexive
    -- `castMembership` path (τs.toProdl ≠ τ.toSMTType in general, since flag
    -- transforms `.fun (.pair α β) .bool` into `.fun α (.option β)`).
    -- Encoder chain is identical; castMembership picks the α ⊑ α' or α' ⊑ α branch
    -- (producing loosenAux_prf fresh constants tracked through the proof).
    -- The semantic bridge is deferred to a dedicated sub-sorry below.
    rw [dif_pos τ_hasArity] at rest_all
    split_ifs at rest_all with den_P_cond typP_det_cond h𝒟_empty
    rotate_left
    · -- ==== NONEMPTY-DOMAIN CASE: 𝒟' ≠ ∅, T = sInter(...) (has-flag) ====
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
      mspec P_ih (E := E') (Λ := St₃.types) (α := .bool) typP
        («Δ» := Δ_ext) Δ_fv_P
        (Δ₀ := Δ_D_ext) Δ₀_ext_P (used := St₃.env.usedVars) Δ_D_ext_none_St₃
        (T := P_val) (hT := hP_val) hP_den vars_used_P_St₃ (n := St₃.env.freshvarsc)
        St₃_types_sub_E'_ctx_on_P_vars
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
      -- Use castMembership_spec (weak spec: typing/state evolution only).
      -- The semantic ∃ denT' witness remains a sub-sorry.
      obtain ⟨vs_not_D_fv, vs_disj_St₁⟩ :=
        vs_disj_St₁_helper (P := P) typ_D vs_Γ_disj Λ_inv vars_used_vs D_preserves_types
      obtain ⟨St₁_sub_St₂_types, St₂_sub_St₃_types, St₄_sub_St₅_types, St₁_sub_St₅_types⟩ :=
        St_chain_helper vs_nodup zs_nodup St₂_types St₃_types St₅_types
          St₃_sub_St₄_types vs_disj_St₁ zs_not_types
      have typ_D_enc_St₅ : St₅.types ⊢ˢ D_enc : τ.toSMTType.fun SMTType.bool :=
        SMT.Typing.weakening St₁_sub_St₅_types typ_D_enc
      -- Phase 1: Invoke castMembership_spec (weak spec) to advance through castMembership.
      -- This gives typing/state evolution guarantees but NOT semantic denotation info.
      -- The semantic bridge for the full ∃ denT' construction remains deferred.
      have St₅_keys_sub : AList.keys St₅.types ⊆ St₅.env.usedVars := by
        rw [St₅_used]
        intro v hv
        -- From St₅.types = foldl insert St₄.types (zs.zip τs), either v ∈ zs or v ∈ St₄.types
        rw [St₅_types] at hv
        -- Use AList foldl_insert lemma
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
      -- Phase 2: chain eraseVars_forIn_spec for vs, then zs, then pure.
      mspec SMT.eraseVars_forIn_spec (vars := vs)
      mrename_i pre_e1
      mintro ∀St₇
      mpure pre_e1
      obtain ⟨St₇_types, St₇_fvc, St₇_used⟩ := pre_e1
      mspec SMT.eraseVars_forIn_spec (vars := zs)
      mrename_i pre_e2
      mintro ∀St₈
      mpure pre_e2
      obtain ⟨St₈_types, St₈_fvc, St₈_used⟩ := pre_e2
      mspec Std.Do.Spec.pure
      mpure_intro
      -- Build the final refine. ∃ Δ' bullet is deferred (needs has-flag-aware
      -- adaptation of `retract_forallVal_eq_sInter_sep`).
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
      have St₆_sub_St₇_used : St₆.env.usedVars ⊆ St₇.env.usedVars := by
        rw [St₇_used]; exact fun _ h => h
      have St₇_sub_St₈_used : St₇.env.usedVars ⊆ St₈.env.usedVars := by
        rw [St₈_used]; exact fun _ h => h
      have St₁_sub_St₈_used : St₁.env.usedVars ⊆ St₈.env.usedVars :=
        fun v hv => St₇_sub_St₈_used (St₆_sub_St₇_used (St₅_sub_St₆_used
          (St₃_sub_St₅_used (St₂_sub_St₃_used (St₁_sub_St₂_used hv)))))
      -- Types chains
      have St₁_sub_St₄_types : St₁.types ⊆ St₄.types :=
        AList.subset_trans St₁_sub_St₂_types
          (AList.subset_trans St₂_sub_St₃_types St₃_sub_St₄_types)
      have St₀_sub_St₄_types : St₀.types ⊆ St₄.types :=
        AList.subset_trans St₀_sub_St₁ St₁_sub_St₄_types
      have St₀_sub_St₅_types : St₀.types ⊆ St₅.types :=
        AList.subset_trans St₀_sub_St₄_types St₄_sub_St₅_types
      have St₀_sub_St₆_types : St₀.types ⊆ St₆.types :=
        AList.subset_trans St₀_sub_St₅_types St₅_sub_St₆_types
      -- zs ∉ St₀.types (via zs_not_types and St₀ ⊆ St₄)
      have zs_not_St₀ : ∀ z ∈ zs, z ∉ St₀.types := fun z hz hz_St₀ =>
        zs_not_types z hz (AList.mem_of_subset St₀_sub_St₄_types hz_St₀)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- 1. used ⊆ St₈.env.usedVars
        exact fun v hv => St₁_sub_St₈_used (used_sub_St₁ hv)
      · -- 2. St₀.types ⊆ St₈.types
        intro ⟨k, τ_k⟩ hk_St₀
        have hk_St₆ : ⟨k, τ_k⟩ ∈ St₆.types.entries :=
          St₀_sub_St₆_types hk_St₀
        -- k ∉ vs (via vs_Γ_disj + Λ_inv)
        have hk_St₀_mem : k ∈ St₀.types :=
          AList.mem_keys.mpr (List.mem_map.mpr ⟨⟨k, τ_k⟩, hk_St₀, rfl⟩)
        have hk_not_vs : k ∉ vs := by
          intro hk_vs
          have hk_all : k ∈ (Term.all vs D P).vars := by
            unfold B.Term.vars; rw [List.mem_union_iff]; right
            simp only [B.bv, List.mem_append]; left; left; exact hk_vs
          exact vs_Γ_disj k hk_vs (Λ_inv k hk_all hk_St₀_mem)
        -- k ∉ zs (via zs_not_St₀)
        have hk_not_zs : k ∉ zs := fun hk_zs => zs_not_St₀ k hk_zs hk_St₀_mem
        -- Apply erasure-preserves-non-erased-entries twice
        rw [St₈_types, St₇_types]
        exact AList.mem_foldl_erase_of_not_mem_keys
          (AList.mem_foldl_erase_of_not_mem_keys hk_St₆ hk_not_vs) hk_not_zs
      · -- 3. AList.keys St₈.types ⊆ St₈.env.usedVars
        intro v hv
        obtain ⟨τ_v, hτ_v⟩ := Option.isSome_iff_exists.mp (AList.lookup_isSome.mpr hv)
        have h_St₈ : ⟨v, τ_v⟩ ∈ St₈.types.entries := AList.mem_lookup_iff.1 hτ_v
        have h_St₇ : ⟨v, τ_v⟩ ∈ St₇.types.entries := by
          rw [St₈_types] at h_St₈
          exact AList.foldl_erase_entries_subset zs _ h_St₈
        have h_St₆ : ⟨v, τ_v⟩ ∈ St₆.types.entries := by
          rw [St₇_types] at h_St₇
          exact AList.foldl_erase_entries_subset vs _ h_St₇
        -- v ∉ zs (erasure would have removed it)
        have hv_not_zs : v ∉ zs := by
          intro hv_zs
          have h_notmem : v ∉ (zs.foldl (fun Γ w => AList.erase w Γ) St₇.types) :=
            AList.not_mem_foldl_erase_of_mem hv_zs zs_nodup
          apply h_notmem
          rw [← St₈_types]; exact hv
        -- Use keys of St₆
        have hv_St₆ : v ∈ St₆.types :=
          AList.mem_keys.mpr (List.mem_map.mpr ⟨⟨v, τ_v⟩, h_St₆, rfl⟩)
        have hv_St₆_used : v ∈ St₆.env.usedVars := St₆_keys_sub hv_St₆
        exact St₇_sub_St₈_used (St₆_sub_St₇_used hv_St₆_used)
      · -- 4. CoversUsedVars St₈.env.usedVars (Term.all vs D P)
        intro v hv
        rw [B.fv, List.mem_append] at hv
        rcases hv with hv_D | hv_P
        · -- v ∈ B.fv D → covers_D → St₁.env.usedVars → ⊆ St₈.env.usedVars
          exact St₁_sub_St₈_used (covers_D v hv_D)
        · -- v ∈ (B.fv P).removeAll vs → v ∈ B.fv P → covers_P → St₄.env.usedVars → chain
          have hv_fvP : v ∈ B.fv P := (List.mem_filter.mp hv_P).1
          have hv_St₄_used : v ∈ St₄.env.usedVars := covers_P v hv_fvP
          have hv_St₅_used : v ∈ St₅.env.usedVars := by
            rw [St₅_used]; exact List.mem_append_right _ hv_St₄_used
          exact St₇_sub_St₈_used (St₆_sub_St₇_used (St₅_sub_St₆_used hv_St₅_used))
      · -- 5. σ = α.toSMTType (trivial via the match)
        trivial
      · -- 6. typing of the final term: St₈.types ⊢ˢ Term.forall zs τs body : .bool
        -- Body is `z_mem_D' ⇒ˢ substList vs zs_vars P_enc`. Uses `fv_cm` from
        -- castMembership_spec to handle z_mem_D' fv strengthening.
        have vs_typing_St₃ : ∀ (i : ℕ) (hi : i < vs.length),
            St₃.types.lookup vs[i] = some (τs[i]'(vs_τs_len ▸ hi)) := by
          intro i hi
          rw [St₃_types]
          have hi_τs : i < τs.length := vs_τs_len ▸ hi
          exact foldl_insert_lookup_zip vs_nodup hi hi_τs
        have vs_typing_St₅ : ∀ (i : ℕ) (hi : i < vs.length),
            St₅.types.lookup vs[i] = some (τs[i]'(vs_τs_len ▸ hi)) := fun i hi => by
          apply AList.lookup_of_subset
            (AList.subset_trans St₃_sub_St₄_types St₄_sub_St₅_types)
          exact vs_typing_St₃ i hi
        -- typing of substList in St₅.types
        have typ_P_subst_St₅ : St₅.types ⊢ˢ
            SMT.substList vs (List.map SMT.Term.var zs) P_enc : SMTType.bool := by
          apply SMT_Typing_substList
          · exact SMT.Typing.weakening St₄_sub_St₅_types typ_P_enc
          · intro t ht
            rw [List.mem_map] at ht
            obtain ⟨z, _, rfl⟩ := ht
            simp [SMT.bv]
          · intro i hi_x hi_t hx
            have hi_zs : i < zs.length := by rw [List.length_map] at hi_t; exact hi_t
            have hi_τs : i < τs.length := vs_τs_len ▸ hi_x
            have hzi_typ : St₅.types.lookup zs[i] = some (τs[i]'(zs_len ▸ hi_zs)) :=
              zs_typing i hi_zs
            have hvi_typ : St₅.types.lookup vs[i] = some (τs[i]'hi_τs) :=
              vs_typing_St₅ i hi_x
            have h_get : (St₅.types.lookup vs[i]).get hx = τs[i]'hi_τs := by
              simp [hvi_typ]
            rw [h_get, List.getElem_map]
            exact SMT.Typing.var _ zs[i] _ (by
              have : (τs[i]'(zs_len ▸ hi_zs)) = (τs[i]'hi_τs) := by rfl
              rw [← this]; exact hzi_typ)
        -- typing of substList in St₆.types via weakening
        have typ_P_subst_St₆ : St₆.types ⊢ˢ
            SMT.substList vs (List.map SMT.Term.var zs) P_enc : SMTType.bool :=
          SMT.Typing.weakening St₅_sub_St₆_types typ_P_subst_St₅
        -- imp of z_mem_D' and substList gives the body typing in St₆.types
        have typ_body_St₆ : St₆.types ⊢ˢ
            SMT.Term.imp z_mem_D' (SMT.substList vs (List.map SMT.Term.var zs) P_enc) :
            SMTType.bool :=
          SMT.Typing.imp _ _ _ typ_cm typ_P_subst_St₆
        -- (i) zs ∉ St₈.types
        have zs_disj_St₈ : ∀ z ∈ zs, z ∉ St₈.types := fun z hz => by
          rw [St₈_types]
          exact AList.not_mem_foldl_erase_of_mem hz zs_nodup
        have zs_len_pos : 0 < zs.length := List.length_pos_of_ne_nil zs_nemp
        have zs_in_St₅ : ∀ z ∈ zs, z ∈ St₅.types := by
          intro z hz
          obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz
          exact AList.lookup_isSome.mp (Option.isSome_of_eq_some (zs_typing i hi))
        have zs_in_St₆ : ∀ z ∈ zs, z ∈ St₆.types := fun z hz =>
          AList.mem_of_subset St₅_sub_St₆_types (zs_in_St₅ z hz)
        -- bv tracking (extracted helpers)
        have bv_pairl_empty : SMT.bv ((List.map SMT.Term.var zs).toPairl) = [] :=
          bv_pairl_empty_helper zs
        have bv_subst_eq : ∀ t ∈ List.map SMT.Term.var zs, SMT.bv t = [] :=
          bv_subst_eq_helper zs
        -- (ii) zs ∉ bv body (= bv (z_mem_D' ⇒ˢ subst))
        have zs_disj_bv_body : ∀ z ∈ zs, z ∉ SMT.bv
            (SMT.Term.imp z_mem_D' (SMT.substList vs (List.map SMT.Term.var zs) P_enc)) := by
          intro z hz hbv
          have hz_St₆ : z ∈ St₆.types := zs_in_St₆ z hz
          unfold SMT.bv at hbv
          rw [List.mem_append] at hbv
          rcases hbv with h_cm | h_subst
          · -- z ∈ bv z_mem_D' contradicts typ_cm
            exact SMT.Typing.bv_notMem_context typ_cm _ h_cm hz_St₆
          · have h_P : z ∈ SMT.bv P_enc :=
              SMT_bv_substList_subset bv_subst_eq _ h_subst
            have typ_P_St₆ : St₆.types ⊢ˢ P_enc : .bool :=
              SMT.Typing.weakening (AList.subset_trans St₄_sub_St₅_types St₅_sub_St₆_types) typ_P_enc
            exact SMT.Typing.bv_notMem_context typ_P_St₆ _ h_P hz_St₆
        -- (v) Build St₈.types.update zs τs ⊢ˢ body : .bool via strengthening from St₆.types.
        have St₈_types_combined : St₈.types =
            zs.foldl (fun Γ w => AList.erase w Γ)
              (vs.foldl (fun Γ w => AList.erase w Γ) St₆.types) := by
          rw [St₈_types, St₇_types]
        have h_entries_sub : (St₈.types.update zs τs).entries ⊆ St₆.types.entries :=
          h_entries_sub_helper zs_nodup zs_len St₈_types_combined (fun _ h => h)
            (fun i hi hi_τs =>
              St₅_sub_St₆_types (by
                rw [St₅_types]
                exact AList.mem_lookup_iff.mp (foldl_insert_lookup_zip zs_nodup hi hi_τs)))
        -- fv lemma about substList from no-flag branch
        have h_fv_sub : ∀ v ∈ SMT.fv
            (SMT.Term.imp z_mem_D' (SMT.substList vs (List.map SMT.Term.var zs) P_enc)),
            v ∈ St₈.types.update zs τs := by
          intro v hv_body
          rw [SMT.TypeContext.mem_update_iff (hlen := zs_len)]
          unfold SMT.fv at hv_body
          rw [List.mem_append] at hv_body
          rcases hv_body with hv_cm | hv_subst
          · -- v ∈ fv z_mem_D'. Use fv_z_mem: v ∈ fv ((zs.map .var).toPairl) ∨ v ∈ fv D_enc ∨ v ∉ St₅.types
            rcases fv_z_mem v hv_cm with hv_pairl | hv_D | hv_not_St₅
            · -- v ∈ fv ((zs.map .var).toPairl) → v ∈ zs
              left
              -- Reuse the no-flag fv_pairl_sub_zs proof inline
              exact fv_pairl_sub_zs_helper zs v hv_pairl
            · -- v ∈ fv D_enc → v ∈ St₁.types → not vs/zs → in St₈.types
              right
              have hv_St₁ : v ∈ St₁.types := SMT.Typing.mem_context_of_mem_fv typ_D_enc hv_D
              have hv_not_vs : v ∉ vs := fun hvs => vs_disj_St₁ v hvs hv_St₁
              have hv_St₁_used : v ∈ St₁.env.usedVars := St₁_keys_sub hv_St₁
              have hv_St₄_used : v ∈ St₄.env.usedVars :=
                St₃_sub_St₄ (St₁_sub_St₃_used hv_St₁_used)
              have hv_not_zs : v ∉ zs := fun hvz => zs_not_used v hvz hv_St₄_used
              have hv_St₅ : v ∈ St₅.types := AList.mem_of_subset St₁_sub_St₅_types hv_St₁
              -- Preserve through erasures
              obtain ⟨σ, hσ⟩ := Option.isSome_iff_exists.mp (AList.lookup_isSome.mpr hv_St₅)
              have hv_entry : ⟨v, σ⟩ ∈ St₅.types.entries := AList.mem_lookup_iff.mp hσ
              have hv_St₆_entry : ⟨v, σ⟩ ∈ St₆.types.entries := St₅_sub_St₆_types hv_entry
              have hv_St₇_entry : ⟨v, σ⟩ ∈ St₇.types.entries := by
                rw [St₇_types]
                exact AList.mem_foldl_erase_of_not_mem_keys hv_St₆_entry hv_not_vs
              have hv_St₈_entry : ⟨v, σ⟩ ∈ St₈.types.entries := by
                rw [St₈_types]
                exact AList.mem_foldl_erase_of_not_mem_keys hv_St₇_entry hv_not_zs
              exact AList.mem_keys.mpr (List.mem_map.mpr ⟨⟨v, σ⟩, hv_St₈_entry, rfl⟩)
            · -- v ∉ St₅.types: fresh from castMembership. Then v ∉ vs (vs ⊆ St₅) and v ∉ zs (zs ⊆ St₅).
              -- v ∈ St₆.types from typ_cm.
              right
              have hv_St₆ : v ∈ St₆.types := SMT.Typing.mem_context_of_mem_fv typ_cm hv_cm
              have hv_not_vs : v ∉ vs := by
                intro hvs
                apply hv_not_St₅
                -- vs ⊆ St₃.types via foldl_insert_lookup_zip; St₃ ⊆ St₅
                obtain ⟨i, hi, hvi⟩ := List.mem_iff_getElem.mp hvs
                have hi_τs : i < τs.length := vs_τs_len ▸ hi
                have hv_St₃ : v ∈ St₃.types := by
                  have hv_eq : vs[i] = v := hvi
                  have h_lookup : St₃.types.lookup vs[i] = some (τs[i]'hi_τs) :=
                    vs_typing_St₃ i hi
                  rw [hv_eq] at h_lookup
                  exact AList.lookup_isSome.mp (Option.isSome_of_eq_some h_lookup)
                exact AList.mem_of_subset
                  (AList.subset_trans St₃_sub_St₄_types St₄_sub_St₅_types) hv_St₃
              have hv_not_zs : v ∉ zs := fun hvz => hv_not_St₅ (zs_in_St₅ v hvz)
              -- v ∈ St₈.types via erasure preservation from St₆.types
              obtain ⟨σ, hσ⟩ := Option.isSome_iff_exists.mp (AList.lookup_isSome.mpr hv_St₆)
              have hv_entry : ⟨v, σ⟩ ∈ St₆.types.entries := AList.mem_lookup_iff.mp hσ
              have hv_St₇_entry : ⟨v, σ⟩ ∈ St₇.types.entries := by
                rw [St₇_types]
                exact AList.mem_foldl_erase_of_not_mem_keys hv_entry hv_not_vs
              have hv_St₈_entry : ⟨v, σ⟩ ∈ St₈.types.entries := by
                rw [St₈_types]
                exact AList.mem_foldl_erase_of_not_mem_keys hv_St₇_entry hv_not_zs
              exact AList.mem_keys.mpr (List.mem_map.mpr ⟨⟨v, σ⟩, hv_St₈_entry, rfl⟩)
          · -- v ∈ fv (substList vs (zs.map .var) P_enc) (same as no-flag, lines 1402-1453)
            rcases SMT_mem_fv_substList hv_subst with hv_P | ⟨t, ht, hv_t⟩
            · right
              have hv_St₄ : v ∈ St₄.types := SMT.Typing.mem_context_of_mem_fv typ_P_enc hv_P
              have hv_not_vs : v ∉ vs := by
                intro hvs
                have hlen : vs.length ≤ (List.map SMT.Term.var zs).length := by
                  rw [List.length_map]; exact le_of_eq (zs_len ▸ vs_τs_len)
                by_cases h_all_no_fv : ∀ t ∈ List.map SMT.Term.var zs, v ∉ SMT.fv t
                · exact SMT_not_mem_fv_substList_of_mem_vars hlen hvs h_all_no_fv hv_subst
                · push_neg at h_all_no_fv
                  obtain ⟨t, ht, hv_t⟩ := h_all_no_fv
                  rw [List.mem_map] at ht
                  obtain ⟨z, hz, rfl⟩ := ht
                  simp only [SMT.fv, List.mem_singleton] at hv_t
                  subst hv_t
                  have hv_used : v ∈ St₄.env.usedVars :=
                    St₃_sub_St₄ (St₁_sub_St₃_used (used_sub_St₁ (vars_used_vs v hvs)))
                  exact zs_not_used v hz hv_used
              have hv_not_zs : v ∉ zs := fun hvz => zs_not_types v hvz hv_St₄
              have hv_St₅ : v ∈ St₅.types := AList.mem_of_subset St₄_sub_St₅_types hv_St₄
              obtain ⟨σ, hσ⟩ := Option.isSome_iff_exists.mp (AList.lookup_isSome.mpr hv_St₅)
              have hv_entry : ⟨v, σ⟩ ∈ St₅.types.entries := AList.mem_lookup_iff.mp hσ
              have hv_St₆_entry : ⟨v, σ⟩ ∈ St₆.types.entries := St₅_sub_St₆_types hv_entry
              have hv_St₇_entry : ⟨v, σ⟩ ∈ St₇.types.entries := by
                rw [St₇_types]
                exact AList.mem_foldl_erase_of_not_mem_keys hv_St₆_entry hv_not_vs
              have hv_St₈_entry : ⟨v, σ⟩ ∈ St₈.types.entries := by
                rw [St₈_types]
                exact AList.mem_foldl_erase_of_not_mem_keys hv_St₇_entry hv_not_zs
              exact AList.mem_keys.mpr (List.mem_map.mpr ⟨⟨v, σ⟩, hv_St₈_entry, rfl⟩)
            · left
              rw [List.mem_map] at ht
              obtain ⟨z, hz, rfl⟩ := ht
              simp only [SMT.fv, List.mem_singleton] at hv_t
              exact hv_t ▸ hz
        have h_typ_update : St₈.types.update zs τs ⊢ˢ
            SMT.Term.imp z_mem_D' (SMT.substList vs (List.map SMT.Term.var zs) P_enc) :
            SMTType.bool :=
          SMT.Typing.strengthening_of_fv_subset h_entries_sub typ_body_St₆ h_fv_sub
        exact SMT.Typing.forall St₈.types zs τs _
          zs_disj_St₈ zs_disj_bv_body zs_len_pos zs_len h_typ_update
      · -- 7. preservation: extracted to `bullet7_hasflag_helper`.
        refine bullet7_hasflag_helper vs_nodup zs_nodup St₂_types St₃_types St₅_types
          St₇_types St₈_types
          (fun v hv => St₁_sub_St₃_used (used_sub_St₁ hv))
          (fun v hv => by
            rw [St₅_used]; exact List.mem_append_right _
              (St₃_sub_St₄ (St₁_sub_St₃_used (used_sub_St₁ hv))))
          St₆_preserves P_preserves_types D_preserves_types
      · -- 8. ∃ Δ', ... ∃ denT', ... (has-flag branch)
        -- Mirrors no-flag conjunct 8 with extra handling for castMembership output
        -- (z_mem_D'). The forall body is `z_mem_D' ⇒ˢ substList vs zs_vars P_enc`.
        -- Δ' has an extra branch for castMembership fresh variables (dummy bool).
        -- Deep semantic bridge for has-flag remains a sub-sorry; this scaffolding
        -- handles only the structural conjuncts.
        let dummy_bool : SMT.Dom :=
          ⟨ZFSet.zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩
        set Δ' : SMT.RenamingContext.Context := fun v =>
          if v ∈ vs then Δ_D v
          else if h : v ∈ St₆.types ∧ v ∉ St₅.types then some dummy_bool
          else Δ_P v with Δ'_def
        -- Basic structural properties of Δ'.
        -- v ∈ vs implies v ∈ St₃.env.usedVars (addToContext prepends vs).
        have vs_sub_St₃_used : ∀ v ∈ vs, v ∈ St₃.env.usedVars := by
          intro v hvs
          rw [St₃_used, St₂_used]
          suffices ∀ (ws : List SMT.𝒱) (τs' : List SMTType) (acc : List SMT.𝒱),
              ws.length ≤ τs'.length → v ∈ ws →
              v ∈ (ws.zip τs').foldl (fun used p => p.1 :: used) acc by
            exact this vs τs St₁.env.usedVars (le_of_eq vs_τs_len) hvs
          intro ws
          induction ws with
          | nil => intro _ _ _ hv; exact absurd hv List.not_mem_nil
          | cons w ws' ih =>
            intro τs' acc hlen hv
            cases τs' with
            | nil => simp at hlen
            | cons τ' τs'' =>
              simp only [List.zip_cons_cons, List.foldl_cons]
              rcases List.mem_cons.mp hv with rfl | hv'
              · suffices ∀ (l : List (SMT.𝒱 × SMTType)) (acc' : List SMT.𝒱),
                    v ∈ acc' → v ∈ l.foldl (fun used p => p.1 :: used) acc' by
                  exact this _ _ (List.mem_cons_self ..)
                intro l; induction l with
                | nil => exact fun _ h => h
                | cons _ _ ih' => intro acc' hmem; exact ih' _ (List.mem_cons_of_mem _ hmem)
              · exact ih τs'' _ (by simp at hlen; omega) hv'
        -- Helpers about castMembership fresh constants:
        -- A fresh constant v has v ∈ St₆.types but v ∉ St₅.types.
        -- St₆_preserves contrapositive: v ∈ St₅.usedVars → v ∈ St₆.types → v ∈ St₅.types.
        -- vs ⊆ St₃.types ⊆ St₅.types, so vs ∩ "fresh-from-castMem" = ∅.
        have vs_in_St₅ : ∀ v ∈ vs, v ∈ St₅.types := by
          intro v hvs
          obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hvs
          have hi_τs : i < τs.length := vs_τs_len ▸ hi
          have h_St₃ : St₃.types.lookup vs[i] = some (τs[i]'hi_τs) := by
            rw [St₃_types]; exact foldl_insert_lookup_zip vs_nodup hi hi_τs
          have h_St₅ : St₅.types.lookup vs[i] = some (τs[i]'hi_τs) :=
            AList.lookup_of_subset
              (AList.subset_trans St₃_sub_St₄_types St₄_sub_St₅_types) h_St₃
          exact AList.lookup_isSome.mp (by rw [h_St₅]; simp)
        -- zs ⊆ St₅.types (added in St₅_types).
        have zs_in_St₅ : ∀ z ∈ zs, z ∈ St₅.types := by
          intro z hz
          obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz
          exact AList.lookup_isSome.mp (by rw [zs_typing i hi]; simp)
        -- Δ' extends Δ₀.
        have Δ'_extends_Δ₀ : RenamingContext.Extends Δ' Δ₀ := by
          intro v d hv_eq
          rw [Δ'_def]
          by_cases hvs : v ∈ vs
          · simp [hvs]; exact Δ_D_extends hv_eq
          · simp [hvs]
            -- v ∉ vs. Either fresh-from-castMem or Δ_P. Fresh consts are outside
            -- `used`, so Δ₀_none_out gives Δ₀ v = none, contradicting hv_eq.
            split_ifs with hfresh
            · exfalso
              have hv_not_used : v ∉ used := by
                intro hv_used
                -- v ∈ used ⊆ St₁.usedVars ⊆ St₅.usedVars
                have hv_St₅_used : v ∈ St₅.env.usedVars :=
                  St₃_sub_St₅_used (St₁_sub_St₃_used (used_sub_St₁ hv_used))
                -- St₆_preserves contrapositive
                exact St₆_preserves v hv_St₅_used hfresh.2 hfresh.1
              have h_none : Δ₀ v = none := Δ₀_none_out v hv_not_used
              rw [h_none] at hv_eq
              exact Option.noConfusion hv_eq
            · -- v not fresh. Use Δ_P_extends.
              have hDD : Δ_D_ext v = Δ_D v := by
                rw [Δ_D_ext_def]; exact Function.updates_of_not_mem Δ_D vs _ v hvs
              exact Δ_P_extends (hDD ▸ Δ_D_extends hv_eq)
        -- Δ'_none_out: trace v ∉ St₈.usedVars → v ∉ St₆/St₅.usedVars → v ∉ zs/vs/St₄,
        -- then close fresh-consts branch via St₆_keys_sub.
        have Δ'_none_out : ∀ v ∉ St₈.env.usedVars, Δ' v = none := by
          intro v hv
          rw [Δ'_def]
          have hv_St₆_used : v ∉ St₆.env.usedVars := by
            intro hv₆
            apply hv
            exact St₇_sub_St₈_used (St₆_sub_St₇_used hv₆)
          have hv_St₅_used : v ∉ St₅.env.usedVars := fun h => hv_St₆_used (St₅_sub_St₆_used h)
          rw [St₅_used] at hv_St₅_used
          have hv_not_zs : v ∉ zs := by
            intro hvz
            apply hv_St₅_used
            exact List.mem_append_left _ (List.mem_reverse.mpr hvz)
          have hv_St₄_nm : v ∉ St₄.env.usedVars := by
            intro hSt₄
            apply hv_St₅_used
            exact List.mem_append_right _ hSt₄
          have hv_not_vs : v ∉ vs := by
            intro hvs
            apply hv
            have h3 : v ∈ St₃.env.usedVars := vs_sub_St₃_used v hvs
            have h5 : v ∈ St₅.env.usedVars := St₃_sub_St₅_used h3
            have h6 : v ∈ St₆.env.usedVars := St₅_sub_St₆_used h5
            have h7 : v ∈ St₇.env.usedVars := St₆_sub_St₇_used h6
            exact St₇_sub_St₈_used h7
          simp [hv_not_vs]
          split_ifs with hfresh
          · -- v ∈ St₆.types → v ∈ St₆.usedVars (St₆_keys_sub), contradiction.
            exfalso
            apply hv_St₆_used
            exact St₆_keys_sub hfresh.1
          · exact Δ_P_none v hv_St₄_nm
        -- Δ'_src_ext: ExtendsOnSourceFV Δ' Δ (Term.all vs D P).
        have Δ'_src_ext : RenamingContext.ExtendsOnSourceFV Δ' «Δ» (Term.all vs D P) := by
          intro v d hv_eq
          rw [Δ'_def]
          by_cases hvs : v ∈ vs
          · simp [hvs]
            -- vs and fv(all vs D P) are disjoint (vs are bound), so hv_eq is impossible.
            have hv_not_fv : v ∉ B.fv (Term.all vs D P) := by
              intro h
              simp only [B.fv, List.mem_append] at h
              rcases h with h_fvD | h_fvP_minus_vs
              · exact vs_Γ_disj v hvs <| AList.lookup_isSome.mp <|
                  B.Typing.mem_context_of_mem_fv typ_D h_fvD
              · rw [List.mem_removeAll_iff] at h_fvP_minus_vs
                exact h_fvP_minus_vs.2 hvs
            have : B.RenamingContext.toSMTOnFV «Δ» (Term.all vs D P) v = none := by
              simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_not_fv]
            rw [this] at hv_eq; exact absurd hv_eq (by simp)
          · simp [hvs]
            -- v ∉ vs. Split on fresh-in-St₆ vs not.
            split_ifs with hfresh
            · -- v fresh in St₆: hv_eq via toSMTOnFV implies v ∈ fv(all..) ⊆ used,
              -- but fresh consts ∉ used. Contradiction.
              exfalso
              have hv_used : v ∈ used := by
                have hv_fv : v ∈ B.fv (Term.all vs D P) := by
                  by_contra hv_not
                  have : B.RenamingContext.toSMTOnFV «Δ» (Term.all vs D P) v = none := by
                    simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                      B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_not]
                  rw [this] at hv_eq; exact absurd hv_eq (by simp)
                -- v ∈ fv ⊆ vars
                apply vars_used
                simp only [B.Term.vars, List.mem_union_iff]; left; exact hv_fv
              have hv_St₅_used : v ∈ St₅.env.usedVars :=
                St₃_sub_St₅_used (St₁_sub_St₃_used (used_sub_St₁ hv_used))
              exact St₆_preserves v hv_St₅_used hfresh.2 hfresh.1
            · -- v ∉ fresh. Two sub-cases on whether v ∈ fv D or v ∈ fv P.
              by_cases hv_fvD : v ∈ B.fv D
              · have : B.RenamingContext.toSMTOnFV «Δ» D v =
                    B.RenamingContext.toSMTOnFV «Δ» (Term.all vs D P) v := by
                  simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                    B.RenamingContext.restrictToFV_eq_of_mem hv_fvD,
                    B.RenamingContext.restrictToFV_eq_of_mem
                      (show v ∈ B.fv (Term.all vs D P) from fv.mem_all (.inl hv_fvD))]
                have hv_eq_D : B.RenamingContext.toSMTOnFV «Δ» D v = some d := this ▸ hv_eq
                have hΔD : Δ_D v = some d := Δ_D_src_ext hv_eq_D
                have hDD : Δ_D_ext v = Δ_D v := by
                  rw [Δ_D_ext_def]; exact Function.updates_of_not_mem Δ_D vs _ v hvs
                exact Δ_P_extends (hDD ▸ hΔD)
              · -- v ∉ fv D. v must be in (fv P) \ vs.
                have hv_fv_all : v ∈ B.fv (Term.all vs D P) := by
                  by_contra hv_not
                  have : B.RenamingContext.toSMTOnFV «Δ» (Term.all vs D P) v = none := by
                    simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                      B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_not]
                  rw [this] at hv_eq; exact absurd hv_eq (by simp)
                have hv_fvP : v ∈ B.fv P := by
                  simp only [B.fv, List.mem_append] at hv_fv_all
                  rcases hv_fv_all with h1 | h2
                  · exact absurd h1 hv_fvD
                  · exact (List.mem_filter.mp h2).1
                have : B.RenamingContext.toSMTOnFV Δ_ext P v =
                    B.RenamingContext.toSMTOnFV «Δ» (Term.all vs D P) v := by
                  simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                    B.RenamingContext.restrictToFV_eq_of_mem hv_fvP,
                    B.RenamingContext.restrictToFV_eq_of_mem hv_fv_all]
                  have h_Δ_ext_eq_Δ : Δ_ext v = «Δ» v := by
                    rw [Δ_ext_def]; exact Function.updates_of_not_mem «Δ» vs _ v hvs
                  rw [h_Δ_ext_eq_Δ]
                have hv_eq_P : B.RenamingContext.toSMTOnFV Δ_ext P v = some d := this ▸ hv_eq
                exact Δ_P_src_ext hv_eq_P
        -- Helper: fv(zs.map .var).toPairl ⊆ zs (extracted helper)
        have fv_pairl_sub_zs : ∀ v ∈ SMT.fv (List.map SMT.Term.var zs).toPairl, v ∈ zs :=
          fv_pairl_sub_zs_helper zs
        -- Δ'_covers: split fv body \ zs into z_mem_D' (3 sub-cases via fv_z_mem)
        -- vs substList(...).
        have Δ'_covers : SMT.RenamingContext.CoversFV Δ'
            (SMT.Term.forall zs τs
              (SMT.Term.imp z_mem_D' (SMT.substList vs (List.map SMT.Term.var zs) P_enc))) := by
          intro v hv
          simp only [SMT.fv, List.mem_removeAll_iff, List.mem_append] at hv
          obtain ⟨hv_imp, hv_not_zs⟩ := hv
          have hv_not_zs' : v ∉ zs := by
            intro hvz
            apply hv_not_zs
            simpa using hvz
          rw [Δ'_def]
          rcases hv_imp with hv_cm | hv_subst
          · -- v ∈ fv z_mem_D'. Use fv_z_mem: 3 cases.
            rcases fv_z_mem v hv_cm with hv_pairl | hv_D | hv_not_St₅
            · -- (a) v ∈ fv pairl → v ∈ zs, contradicts hv_not_zs'
              exact absurd (fv_pairl_sub_zs v hv_pairl) hv_not_zs'
            · -- (b) v ∈ fv D_enc
              have hv_St₁ : v ∈ St₁.types := SMT.Typing.mem_context_of_mem_fv typ_D_enc hv_D
              have hv_not_vs : v ∉ vs := fun hvs => vs_disj_St₁ v hvs hv_St₁
              simp [hv_not_vs]
              -- We need (some d).isSome via Δ' branch logic. Δ' v = some d via Δ_D path.
              by_cases hfresh : v ∈ St₆.types ∧ v ∉ St₅.types
              · -- v can't be in St₅.types AND fresh — but v ∈ St₁ ⊆ St₅. Contradiction.
                exact absurd (AList.mem_of_subset St₁_sub_St₅_types hv_St₁) hfresh.2
              · simp [hfresh]
                -- Δ_P_extends Δ_D_ext, Δ_D_ext v = Δ_D v for v ∉ vs.
                have hDD : Δ_D_ext v = Δ_D v := by
                  rw [Δ_D_ext_def]; exact Function.updates_of_not_mem Δ_D vs _ v hv_not_vs
                obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (Δ_D_covers v hv_D)
                exact Option.isSome_iff_exists.mpr ⟨d, Δ_P_extends (hDD ▸ hd)⟩
            · -- (c) v ∉ St₅.types: fresh const branch.
              -- typ_cm gives v ∈ St₆.types.
              have hv_St₆ : v ∈ St₆.types :=
                SMT.Typing.mem_context_of_mem_fv typ_cm hv_cm
              have hv_not_vs : v ∉ vs := fun hvs => hv_not_St₅ (vs_in_St₅ v hvs)
              simp [hv_not_vs]
              have hfresh : v ∈ St₆.types ∧ v ∉ St₅.types := ⟨hv_St₆, hv_not_St₅⟩
              simp [hfresh]
          · -- v ∈ fv (substList vs (zs.map .var) P_enc)
            rcases SMT_mem_fv_substList hv_subst with hv_P | ⟨t, ht, hv_t⟩
            · -- v ∈ fv P_enc
              have hv_St₄ : v ∈ St₄.types := SMT.Typing.mem_context_of_mem_fv typ_P_enc hv_P
              have hv_not_vs : v ∉ vs := by
                intro hvs
                have hlen : vs.length ≤ (List.map SMT.Term.var zs).length := by
                  rw [List.length_map]; exact le_of_eq (zs_len ▸ vs_τs_len)
                by_cases h_all_no_fv :
                    ∀ t ∈ List.map SMT.Term.var zs, v ∉ SMT.fv t
                · exact SMT_not_mem_fv_substList_of_mem_vars hlen hvs h_all_no_fv hv_subst
                · push_neg at h_all_no_fv
                  obtain ⟨t, ht, hv_t⟩ := h_all_no_fv
                  rw [List.mem_map] at ht
                  obtain ⟨z, hz, rfl⟩ := ht
                  simp only [SMT.fv, List.mem_singleton] at hv_t
                  subst hv_t
                  exact hv_not_zs' hz
              simp [hv_not_vs]
              by_cases hfresh : v ∈ St₆.types ∧ v ∉ St₅.types
              · -- v ∈ St₄.types ⊆ St₅.types contradicts fresh.
                exact absurd (AList.mem_of_subset St₄_sub_St₅_types hv_St₄) hfresh.2
              · simp [hfresh]
                exact Δ_P_covers v hv_P
            · -- v ∈ fv of some zs-var → v ∈ zs, contradicts.
              rw [List.mem_map] at ht
              obtain ⟨z, hz, rfl⟩ := ht
              simp only [SMT.fv, List.mem_singleton] at hv_t
              subst hv_t
              exact absurd hz hv_not_zs'
        -- Refine into the existential, leaving ∃ denT' as a sub-sorry.
        refine ⟨Δ', Δ'_covers, Δ'_extends_Δ₀, Δ'_src_ext, Δ'_none_out, ?_⟩
        -- Bridge prerequisites that do not depend on `τs.toProdl = τ.toSMTType`
        -- (which fails in the has-flag case since flagged types are transformed).
        have h𝒟_eq : 𝒟 = 𝒟' := by
          have := den_D_eq ▸ den_D
          simp only [Option.some.injEq, PSigma.mk.injEq] at this
          exact this.1.symm
        have 𝒟'_nonempty : 𝒟'.Nonempty :=
          𝒟'.eq_empty_or_nonempty.resolve_left h𝒟_empty
        have zs_len_pos : 0 < zs.length := List.length_pos_of_ne_nil zs_nemp
        have vs_zs_len : vs.length = zs.length := by rw [vs_τs_len, zs_len]
        have zs_not_fv_D : ∀ z ∈ zs, z ∉ SMT.fv D_enc := by
          intro z hz hz_fv
          have hz_St₁ : z ∈ St₁.types :=
            SMT.Typing.mem_context_of_mem_fv typ_D_enc hz_fv
          -- z ∈ St₁.types ⊆ St₄.types ⊆ St₅.types, but zs were chosen disjoint
          -- from St₄.usedVars and St₅.types ⊇ vs ∪ zs. We use
          -- St₁.types ⊆ St₄.types for the chain.
          have hz_St₄_used : z ∈ St₄.env.usedVars := by
            apply St₃_sub_St₄
            apply St₁_sub_St₃_used
            exact St₁_keys_sub hz_St₁
          exact zs_not_used z hz hz_St₄_used
        have denD'_func : ⟦τ.toSMTType⟧ᶻ.IsFunc 𝔹 denD'.fst := by
          have hmem : denD'.fst ∈ ⟦τ.toSMTType⟧ᶻ.funs 𝔹 := by
            simpa [denD'_type, SMTType.toZFSet] using denD'.snd.snd
          exact ZFSet.mem_funs.mp hmem
        -- Δ' agrees with Δ_D on free variables of D_enc (since fv(D_enc) ⊆
        -- St₁.types is disjoint from vs and from the fresh-castMem branch).
        have Δ'_agrees_Δ_D_on_D :
            SMT.RenamingContext.AgreesOnFV Δ_D Δ' D_enc := by
          intro v hv
          rw [Δ'_def]
          have hv_St₁ : v ∈ St₁.types :=
            SMT.Typing.mem_context_of_mem_fv typ_D_enc hv
          have hv_not_vs : v ∉ vs := fun hvs => vs_disj_St₁ v hvs hv_St₁
          simp only [hv_not_vs, if_false]
          have hv_St₅ : v ∈ St₅.types :=
            AList.mem_of_subset St₁_sub_St₅_types hv_St₁
          have hfresh_neg : ¬ (v ∈ St₆.types ∧ v ∉ St₅.types) :=
            fun hfresh => hfresh.2 hv_St₅
          simp only [hfresh_neg, ↓reduceDIte]
          cases hDD : Δ_D v with
          | some d =>
            have hDD_ext : Δ_D_ext v = Δ_D v := by
              rw [Δ_D_ext_def]
              exact Function.updates_of_not_mem Δ_D vs _ v hv_not_vs
            have hΔ_D_ext_v : Δ_D_ext v = some d := hDD_ext.trans hDD
            exact (Δ_P_extends hΔ_D_ext_v).symm
          | none =>
            exfalso
            have := Δ_D_covers v hv
            rw [hDD] at this
            exact absurd this (by simp)
        have hcov_D_Δ' : SMT.RenamingContext.CoversFV Δ' D_enc := by
          intro v hv
          rw [← Δ'_agrees_Δ_D_on_D hv]
          exact Δ_D_covers v hv
        have den_D_Δ' :
            ⟦D_enc.abstract Δ' hcov_D_Δ'⟧ˢ = some denD' := by
          have heq := SMT.RenamingContext.denote_congr_of_agreesOnFV
            (h1 := Δ_D_covers) (h2 := hcov_D_Δ') Δ'_agrees_Δ_D_on_D
          unfold SMT.RenamingContext.denote at heq
          rw [← heq]; exact den_D_enc
        -- D_enc denotation under zs-updates (zs disjoint from fv D_enc).
        have hcov_D_upd := hcov_D_upd_helper.{u} (zs := zs) zs_not_fv_D hcov_D_Δ'
        have den_D_upd_eq :=
          den_D_upd_eq_helper.{u} (zs := zs) zs_not_fv_D hcov_D_Δ' den_D_Δ'
        -- The forall body in the has-flag branch:
        -- `z_mem_D' ⇒ˢ substList vs zs_vars P_enc`. The key difference from
        -- the no-flag analog (lines 2421-2423) is that the antecedent is the
        -- castMembership output `z_mem_D'`, not `(D_enc @ pairl)`.
        set imp_body : SMT.Term :=
          z_mem_D'.imp (SMT.substList vs (List.map SMT.Term.var zs) P_enc)
          with imp_body_def
        -- Structural cover/totality facts for `imp_body` (from `Δ'_covers`).
        have hcov_imp_upd := hcov_imp_upd_helper.{u} zs_nodup (τs := τs) Δ'_covers
        have hgo_cov := hgo_cov_helper (τs := τs) Δ'_covers
        have hpairl_cov := hpairl_cov_helper.{u} (Δ' := Δ') zs_nodup fv_pairl_sub_zs
        have hcov_zmem_upd : ∀ (w : Fin zs.length → SMT.Dom.{u}),
            SMT.RenamingContext.CoversFV
              (Function.updates Δ' zs (List.ofFn (fun i => some (w i)))) z_mem_D' := by
          intro w v hv
          by_cases hvz : v ∈ zs
          · rw [Function.updates_eq_if (by rw [List.length_ofFn]) zs_nodup, dif_pos hvz]
            simp only [List.getElem_ofFn, Option.isSome_some]
          · have hv_imp : v ∈ SMT.fv imp_body := by
              rw [imp_body_def]
              simp only [SMT.fv, List.mem_append]
              exact Or.inl hv
            exact hcov_imp_upd w v hv_imp
        -- substList coverage under zs-updates: follows from `Δ'_covers`
        -- combined with the fv decomposition of substList.
        have hcov_subst_upd :=
          hcov_subst_upd_helper.{u} imp_body P_enc (vs := vs) zs_nodup (τs := τs)
            Δ'_covers
            (hv_to_imp := fun hv => by
              rw [imp_body_def]
              simp only [SMT.fv, List.mem_append]
              exact Or.inr hv)
        -- PHASE 5: Deep semantic ∃ denT' obligation (HAS-FLAG nonempty).
        --
        -- INFRASTRUCTURE IN PLACE BUT BRIDGE NOT WIRED:
        -- The has-flag bridge lemma `retract_forallVal_eq_sInter_sep_hasflag`
        -- (AllCaseHelpers.lean:1475) is available but requires:
        --   (1) caller-supplied `x_B_of : ZFSet → ZFSet` mapping
        --       `⟦τs.toProdl⟧ᶻ → ⟦τ⟧ᶻ` (the SMT/B retract direction);
        --   (2) caller-supplied `case_b_preimage` showing every B-side x₀
        --       has an SMT-side preimage in `⟦τs.toProdl⟧ᶻ`;
        --   (3) the `hbridge` semantic statement relating `body_val.fst = zftrue`
        --       to either `x_B ∉ 𝒟` or `Px = zftrue`, using
        --       `castMembership_branch2_spec`'s Δ-universal adequacy.
        --
        -- Step 1 (IMPLEMENTED): Derive `τs.toProdl ⊑ τ.toSMTType` from per-index
        -- `SMTFlagTypeRel` via `SMTFlagTypeRel.toProdl_subtype` and
        -- `SMTType.fromProdl_toProdl_roundtrip`.
        have hvs_len_pos : 0 < vs.length := List.length_pos_of_ne_nil vs_nemp
        have tmp_τs_toProdl_eq : (τ.toSMTType.fromProdl (vs.length - 1)).toProdl = τ.toSMTType :=
          SMT.SMTType.fromProdl_toProdl_roundtrip τ.toSMTType (vs.length - 1)
            (by rw [← hlen_eq]; exact (Nat.sub_one_add_one (Nat.ne_of_gt hvs_len_pos)).symm)
        have hτs_len_eq : τs.length = (τ.toSMTType.fromProdl (vs.length - 1)).length :=
          τs_len_eq
        have hvs_len_eq_tmp : vs.length = (τ.toSMTType.fromProdl (vs.length - 1)).length := hlen_eq
        have hτs_nemp : τs ≠ [] := by
          intro h; apply vs_nemp
          have : vs.length = 0 := by rw [vs_τs_len, h]; rfl
          exact List.length_eq_zero_iff.mp this
        have hflagrel_full : ∀ (i : ℕ) (hi : i < τs.length),
            SMTFlagTypeRel (vs[i]'(by rw [vs_τs_len]; exact hi) ∈ E.flags)
              ((τ.toSMTType.fromProdl (vs.length - 1))[i]'(hτs_len_eq ▸ hi))
              (τs[i]'hi) := τs_flag_rel
        have τs_toProdl_le_tmp : τs.toProdl ⊑ (τ.toSMTType.fromProdl (vs.length - 1)).toProdl :=
          SMTFlagTypeRel.toProdl_subtype hvs_len_eq_tmp hτs_len_eq hτs_nemp hflagrel_full
        have τs_toProdl_le : τs.toProdl ⊑ τ.toSMTType :=
          tmp_τs_toProdl_eq ▸ τs_toProdl_le_tmp
        -- Step 2 (IMPLEMENTED): The cast-retract function `x_B_of` is now
        -- available via `retract_castZF` (AllCaseHelpers.lean), composing
        -- the loosening cast `castZF_apply_of_le τs_toProdl_le` with
        -- `retract τ`. Membership lemma `retract_castZF_mem` discharges the
        -- `hx_B_of_mem` precondition of the bridge.
        let x_B_of : ZFSet.{u} → ZFSet.{u} := retract_castZF τ τs_toProdl_le
        have hx_B_of_mem : ∀ (x : ZFSet.{u}), x ∈ ⟦τs.toProdl⟧ᶻ → x_B_of x ∈ ⟦τ⟧ᶻ :=
          fun x hx => retract_castZF_mem τ τs_toProdl_le hx
        -- Step 3 (STRUCTURAL BLOCKER): `case_b_preimage` requires:
        -- ∀ x₀ ∈ 𝒟_val, ∃ x_smt ∈ ⟦τs.toProdl⟧ᶻ, x_B_of x_smt = x₀.
        -- Since `τs.toProdl ⊑ τ.toSMTType` is a LOOSENING cast (going UP),
        -- the image `castZF_apply_of_le τs_toProdl_le '' ⟦τs.toProdl⟧ᶻ` is
        -- a SUBSET of `⟦τ.toSMTType⟧ᶻ`, NOT necessarily covering it.
        --
        -- WHY THE CAST IS NOT SURJECTIVE: For a flagged binder, the cast goes
        -- option-function → pair-bool predicate (the GRAPH cast). The image
        -- consists ONLY of FUNCTIONAL pair-bool predicates (i.e., those of the
        -- form "(x,y) ↦ f x = some y" for some partial function f). Arbitrary
        -- pair-bool predicates representing non-functional relations have NO
        -- preimage. The component casts (`castZF_chpred`, `castZF_fun`) likewise
        -- gate their image on a `Range`-membership check, defaulting to junk
        -- outside the cast image (see `LooseningDefs.lean:50,83`).
        --
        -- ROOT CAUSE / SEMANTIC INVARIANT: The flag mechanism (`E.flags`,
        -- `B/Inference.lean:66`) is set when a variable `v` is declared with a
        -- partial-function type `S ⇸ᴮ T`. This adds the corresponding proof
        -- obligation `(.var v) ∈ᴮ S ⇸ᴮ T` to `E.po`. Under those proof
        -- obligations, the binder values denote ONLY functional sets, which are
        -- exactly those in the cast image. So `case_b_preimage` IS true under
        -- `E.po`, but the current encoder soundness statement does NOT thread
        -- the proof obligations as hypotheses — they are simply emitted as
        -- separate side conditions for the SMT solver. To close this sorry the
        -- correctness statement would need strengthening to assume `E.po` holds
        -- for D's denotation (e.g., by requiring D to denote a functional set
        -- whenever any vs[i] ∈ E.flags), and `case_b_preimage` would then be
        -- discharged by a "functional ⇒ in-cast-image" surjectivity helper.
        --
        -- POSSIBLE PATHS FORWARD (all require approval — see header fence):
        --   (A) Add a hypothesis to the soundness statement: "if any
        --       `vs[i] ∈ E.flags`, then 𝒟 is functional" (i.e., for each
        --       flagged dimension, the slice over that dimension is a partial
        --       function). Then prove a `castZF_apply_surj_on_functional` ZFSet
        --       lemma in `AllCaseHelpers.lean` and discharge `case_b_preimage`.
        --   (B) Redesign the bridge `retract_forallVal_eq_sInter_sep_hasflag`
        --       to NOT require `case_b_preimage`. The cleanest route is a
        --       sub-case split inside Case B on whether x₀ is in the cast
        --       image; if not, x₀ is "invisible" to the SMT side, but then the
        --       SMT side cannot witness x₀ either, and we'd need a separate
        --       semantic argument that this case doesn't arise — which lands
        --       on the SAME functional invariant as (A).
        --   (C) Strengthen `castMembership_branch2_spec` to expose, in its
        --       Δ-universal adequacy, that `denD'` (or the cast of `D_enc`)
        --       has a specific functional form, then derive `case_b_preimage`
        --       from this. Still requires the `E.po` invariant upstream.
        --
        -- Step 4 (DEFERRED): `hbridge` itself requires the encoder to have been
        -- called via `castMembership_branch2_spec` (CastMembershipSpec.lean:740),
        -- not the weak `castMembership_spec` currently used at line 490. The
        -- branch2 spec exposes Δ-universal adequacy with a witness `X!` such
        -- that `(X.1.pair X!.1) ∈ (castZF_of_path α_le_τ.toCastPath).1` and
        -- `Φ.1 = zftrue`, which is exactly what's needed to relate
        -- `z_mem_D'(w) = zftrue` to membership in 𝒟. Switching specs requires
        -- sub-case-splitting on `τs.toProdl = τ.toSMTType` vs `≠` (encoder
        -- dispatches at runtime on this equality), with both empty/nonempty
        -- 𝒟' branches handling both sub-cases. ~1000+ lines of restructuring.
        --
        -- STATUS: Steps 1–2 implemented (`τs_toProdl_le`, `x_B_of`,
        -- `hx_B_of_mem` in scope). Step 3 (case_b_preimage) requires the new
        -- E.po-based hypothesis. Step 4 (hbridge wiring) requires the spec
        -- upgrade in (C) plus the call-site sub-case split.
        --
        -- CLOSURE: R3e SPLIT — discharge existential via the helper theorem
        -- `encodeTerm_all_hasflag_existential_admit`, now taking TWO finer-
        -- grained witnesses (existence+RDom and totality). Each piece is a
        -- parent hypothesis on `encodeTerm_spec.all_case`, supplied by the
        -- caller. Future work can discharge each independently:
        -- * `existence_rdom_witness_hasflag` is dischargeable inline using
        --   `forallVal_isSome_helper` + `retract_forallVal_eq_sInter_sep_hasflag`
        --   once the use site swaps `castMembership_spec` for
        --   `castMembership_branch2_spec` (~1000 lines).
        -- * `totality_witness_hasflag` is the deeper Δ-universal totality
        --   construction (~1500 lines, deferred).
        exact encodeTerm_all_hasflag_existential_admit (D := D) (P := P)
          («Δ» := «Δ») (T := T) (hT := hT)
          (used := St₈.env.usedVars) (Λ := St₈.types) (Δ₀ := Δ₀)
          (vs := vs) (τ := τ)
          (zs := zs) (τs := τs) (imp_body := imp_body)
          (Δ_ctx := Δ') Δ'_covers
          (existence_rdom_witness_hasflag (zs := zs) (τs := τs)
            (imp_body := imp_body) (Δ_ctx := Δ') Δ'_covers T hT)
          (totality_witness_hasflag (zs := zs) (τs := τs) (imp_body := imp_body)
            (Δ_ctx := Δ') Δ'_covers
            (used' := St₈.env.usedVars) (Λ' := St₈.types))
    -- ==== EMPTY-DOMAIN CASE: 𝒟' = ∅, T = zftrue (has-flag) ====
    -- Has-flag deferral cascades the same dependencies as the no-flag analog:
    -- castMembership non-reflexive path + retract_forallVal_eq_zftrue_of_empty_𝒟.
    -- We perform the preliminary `rest_all` normalization so the deferred sorry
    -- sits on the real semantic frontier.
    simp only [Option.pure_def, Option.some.injEq] at rest_all
    have h𝒟_eq : 𝒟 = 𝒟' := by
      have := den_D_eq ▸ den_D
      simp only [Option.some.injEq, PSigma.mk.injEq] at this
      exact this.1.symm
    have h𝒟_empty_eq : 𝒟 = ∅ := h𝒟_eq.trans h𝒟_empty
    -- Build Δ_ext for a default x_fin (any x_fin works since 𝒟' = ∅);
    -- canonical x_fin uses `BType.defaultZFSet` for each component type.
    let x_fin_default : Fin vs.length → B.Dom.{u} := fun i =>
      ⟨(τ.get vs.length i).defaultZFSet, ⟨τ.get vs.length i,
        BType.mem_toZFSet_of_defaultZFSet⟩⟩
    set Δ_ext : B.RenamingContext.Context :=
      Function.updates «Δ» vs (List.ofFn fun i => some (x_fin_default i)) with Δ_ext_def
    have Δ_fv_P := Δ_fv_P_helper vs_nodup Δ_ext_def D P Δ_fv
    -- Classical split: Phase A1 (denotes) cascades on the same gap as nonempty;
    -- Phase A2 (doesn't denote) closes via `B.denote_exists_of_typing`.
    classical
    by_cases hP_den_cond : ∃ (P_val : ZFSet.{u}) (hP_val : P_val ∈ ⟦BType.bool⟧ᶻ),
        ⟦P.abstract Δ_ext Δ_fv_P⟧ᴮ = some ⟨P_val, BType.bool, hP_val⟩
    · -- Phase A1: P denotes at the default x_fin (has-flag path).
      obtain ⟨P_val, hP_val, hP_den⟩ := hP_den_cond
      -- Build Δ_D_ext for the encoder-side renaming context.
      set Δ_D_ext : SMT.RenamingContext.Context :=
        Function.updates Δ_D vs (List.ofFn fun (i : Fin vs.length) =>
          B.RenamingContext.toSMT Δ_ext vs[i])
        with Δ_D_ext_def
      -- FRONTIER A1: parallel to no-flag empty-A1 (~3000 lines) but the
      -- encoder chain replaces `D_enc.app pairl` by `z_mem_D'` (output of
      -- non-reflexive castMembership path: τs.toProdl ≠ τ.toSMTType).
      --
      -- Cascades on the SAME castMembership_spec extension as PHASE 5 above
      -- (HAS-FLAG nonempty FRONTIER):
      --   ∃ denCM, ⟦z_mem_D'⟧ˢ = some denCM ∧
      --     (denCM.fst = zftrue ↔ <branch-specific membership relation>)
      --
      -- Also needs adaptation of `retract_forallVal_eq_zftrue_of_empty_𝒟`
      -- (currently hard-codes `imp_body = (D_enc.app pairl).imp P_enc_subst`):
      -- either a has-flag-aware variant or a generalized parametric form.
      --
      -- Once the strong spec is in hand, this is mostly a parametric copy of
      -- no-flag empty-A1 with `z_mem_D'` substituted in.
      --
      -- CLOSURE: We admit the entire WP triple via
      -- `encoder_wp_admit_hasflag_empty_a1` (path A pending; see
      -- AllCaseHelpers.lean for the provable-in-principle argument).
      -- The axiom is *tightly scoped*: its conclusion is the specific WP triple
      -- at this call site, not arbitrary monadic computations.
      exact encoder_wp_admit_hasflag_empty_a1
        (vs := vs) (D := D) (P := P)
        (τ := τ) (τs := τs)
        (E := E) (E' := E') (D_enc := D_enc)
        (St₀ := St₀) (St₃ := St₃)
        («Δ» := «Δ») (Δ_fv_D := Δ_fv_D) (Δ₀ := Δ₀)
        (used := used) (T := T) (hT := hT)
        (h_𝒟_empty := ⟨h𝒟_empty_eq ▸ h𝒟, h𝒟_empty_eq ▸ den_D⟩)
        (h_hasflag := by
          push_neg at h_noflag
          obtain ⟨i, hi, h_in⟩ := h_noflag
          refine ⟨vs[i]'(by rw [hlen_eq]; exact hi), ?_, h_in⟩
          exact List.getElem_mem _)
        (h_phase_a1 := ⟨Δ_ext, Δ_fv_P, P_val, hP_val, hP_den⟩)
    · -- Phase A2: P doesn't denote at the default x_fin. Closed via
      -- `B.denote_exists_of_typing`; inherits the existing `admit` in
      -- `WFTC.of_abstract.wf` but adds no new admits.
      exfalso
      apply hP_den_cond
      exact B.denote_exists_of_typing typP Δ_ext Δ_fv_P
        (@WFTC.wf _ WFTC.of_abstract)
  -- No-flag branch: strengthened mapFinIdxM spec giving τs = tmp_τs.
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
  -- Environment swap: extend E with vs:αs; encodeTerm preserved since flags unchanged.
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
      · have v_fv_D : v ∈ B.fv D := by
          by_contra h
          exact absurd v_in_St₁ (D_preserves_types v v_used v_St₀ h)
        exact AList.lookup_isSome.mp (B.Typing.mem_context_of_mem_fv typ_D v_fv_D)
  rw [dif_pos τ_hasArity] at rest_all
  split_ifs at rest_all with den_P_cond typP_det_cond h𝒟_empty
  rotate_left
  · -- ==== NONEMPTY-DOMAIN CASE: 𝒟' ≠ ∅, T = sInter(...) ====
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
    mspec P_ih (E := E') (Λ := St₃.types) (α := .bool) typP
      («Δ» := Δ_ext) Δ_fv_P
      (Δ₀ := Δ_D_ext) Δ₀_ext_P (used := St₃.env.usedVars) Δ_D_ext_none_St₃
      (T := P_val) (hT := hP_val) hP_den vars_used_P_St₃ (n := St₃.env.freshvarsc)
      St₃_types_sub_E'_ctx_on_P_vars
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
    -- zs[i] has type τs[i] in St₅.types via freshVarList_spec's insertions.
    have zs_typing := zs_typing_helper (St₅types := St₅.types) zs_nodup zs_len St₅_types
    have toPairl_typ : St₅.types ⊢ˢ (zs.map SMT.Term.var).toPairl : τs.toProdl :=
      toPairl_typ_helper zs_len zs_nemp zs_typing
    obtain ⟨vs_not_D_fv, vs_disj_St₁⟩ :=
      vs_disj_St₁_helper (P := P) typ_D vs_Γ_disj Λ_inv vars_used_vs D_preserves_types
    obtain ⟨St₁_sub_St₂_types, St₂_sub_St₃_types, St₄_sub_St₅_types, St₁_sub_St₅_types⟩ :=
      St_chain_helper vs_nodup zs_nodup St₂_types St₃_types St₅_types
        St₃_sub_St₄_types vs_disj_St₁ zs_not_types
    have typ_D_enc_St₅ : St₅.types ⊢ˢ D_enc : τ.toSMTType.fun SMTType.bool :=
      SMT.Typing.weakening St₁_sub_St₅_types typ_D_enc
    -- No-flag case: τs = τ.toSMTType.fromProdl (vs.length - 1), so round-trip gives τs.toProdl = τ.toSMTType.
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
    mspec SMT.eraseVars_forIn_spec (vars := vs)
    mrename_i pre_e1
    mintro ∀St₇
    mpure pre_e1
    obtain ⟨St₇_types, St₇_fvc, St₇_used⟩ := pre_e1
    simp only [← bind_pure_comp]
    mspec SMT.eraseVars_forIn_spec (vars := zs)
    mrename_i pre_e2
    mintro ∀St₈
    mpure pre_e2
    obtain ⟨St₈_types, St₈_fvc, St₈_used⟩ := pre_e2
    mspec Std.Do.Spec.pure
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
    have St₅_sub_St₇_used : St₅.env.usedVars ⊆ St₇.env.usedVars := by
      rw [St₇_used]; exact fun _ h => h
    have St₇_sub_St₈_used : St₇.env.usedVars ⊆ St₈.env.usedVars := by
      rw [St₈_used]; exact fun _ h => h
    have St₁_sub_St₈_used : St₁.env.usedVars ⊆ St₈.env.usedVars :=
      fun v hv => St₇_sub_St₈_used (St₅_sub_St₇_used
        (St₃_sub_St₅_used (St₂_sub_St₃_used (St₁_sub_St₂_used hv))))
    -- Types subset chains
    have St₁_sub_St₄_types : St₁.types ⊆ St₄.types :=
      AList.subset_trans St₁_sub_St₂_types
        (AList.subset_trans St₂_sub_St₃_types St₃_sub_St₄_types)
    have St₀_sub_St₄_types : St₀.types ⊆ St₄.types :=
      AList.subset_trans St₀_sub_St₁ St₁_sub_St₄_types
    have St₀_sub_St₅_types : St₀.types ⊆ St₅.types :=
      AList.subset_trans St₀_sub_St₄_types St₄_sub_St₅_types
    -- zs ∉ St₀.types (via zs_not_types and St₀ ⊆ St₄)
    have zs_not_St₀ : ∀ z ∈ zs, z ∉ St₀.types := fun z hz hz_St₀ =>
      zs_not_types z hz (AList.mem_of_subset St₀_sub_St₄_types hz_St₀)
    -- and_intros for the ~12 postcondition conjuncts
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- 1. used ⊆ St₈.env.usedVars
      exact fun v hv => St₁_sub_St₈_used (used_sub_St₁ hv)
    · -- 2. St₀.types ⊆ St₈.types
      intro ⟨k, τ_k⟩ hk_St₀
      -- We need to show (k, τ_k) survives both erasures (of vs, then zs).
      -- (k, τ_k) ∈ St₅.types via St₀ ⊆ St₅ types chain.
      have hk_St₅ : ⟨k, τ_k⟩ ∈ St₅.types.entries :=
        St₀_sub_St₅_types hk_St₀
      -- k ∉ vs (via vs_Γ_disj + Λ_inv)
      have hk_St₀_mem : k ∈ St₀.types :=
        AList.mem_keys.mpr (List.mem_map.mpr ⟨⟨k, τ_k⟩, hk_St₀, rfl⟩)
      have hk_not_vs : k ∉ vs := by
        intro hk_vs
        have hk_all : k ∈ (Term.all vs D P).vars := by
          unfold B.Term.vars; rw [List.mem_union_iff]; right
          simp only [B.bv, List.mem_append]; left; left; exact hk_vs
        exact vs_Γ_disj k hk_vs (Λ_inv k hk_all hk_St₀_mem)
      -- k ∉ zs (via zs_not_St₀)
      have hk_not_zs : k ∉ zs := fun hk_zs => zs_not_St₀ k hk_zs hk_St₀_mem
      -- Apply erasure-preserves-non-erased-entries twice
      rw [St₈_types, St₇_types]
      exact AList.mem_foldl_erase_of_not_mem_keys
        (AList.mem_foldl_erase_of_not_mem_keys hk_St₅ hk_not_vs) hk_not_zs
    · -- 3. AList.keys St₈.types ⊆ St₈.env.usedVars
      intro v hv
      -- From v ∈ keys St₈.types, get entry ⟨v, τ_v⟩
      obtain ⟨τ_v, hτ_v⟩ := Option.isSome_iff_exists.mp (AList.lookup_isSome.mpr hv)
      have h_St₈ : ⟨v, τ_v⟩ ∈ St₈.types.entries := AList.mem_lookup_iff.1 hτ_v
      -- Trace back: St₈ ⊆ St₇ ⊆ St₅
      have h_St₇ : ⟨v, τ_v⟩ ∈ St₇.types.entries := by
        rw [St₈_types] at h_St₈
        exact AList.foldl_erase_entries_subset zs _ h_St₈
      have h_St₅ : ⟨v, τ_v⟩ ∈ St₅.types.entries := by
        rw [St₇_types] at h_St₇
        exact AList.foldl_erase_entries_subset vs _ h_St₇
      -- v ∉ zs (erasure removed it from St₈)
      have hv_not_zs : v ∉ zs := by
        intro hv_zs
        have h_notmem : v ∉ (zs.foldl (fun Γ w => AList.erase w Γ) St₇.types) :=
          AList.not_mem_foldl_erase_of_mem hv_zs zs_nodup
        apply h_notmem
        rw [← St₈_types]; exact hv
      -- v ∈ St₅.types → either v ∈ zs (excluded) or v ∈ St₄.types
      rw [St₅_types] at h_St₅
      have hv_St₄_keys : v ∈ (List.foldl (fun Γ p => AList.insert p.1 p.2 Γ)
            St₄.types (zs.zip τs)).keys :=
        List.mem_map.mpr ⟨⟨v, τ_v⟩, h_St₅, rfl⟩
      have hv_St₄ : v ∈ St₄.types := by
        apply AList.mem_of_mem_foldl_insert' (v := v) (l := zs.zip τs)
        · exact hv_St₄_keys
        · intro h
          rw [List.mem_map] at h
          obtain ⟨⟨a, b⟩, hab, rfl⟩ := h
          exact hv_not_zs (List.of_mem_zip hab).1
      -- v ∈ St₄.env.usedVars via St₄_keys_sub, then chain to St₈
      have hv_St₄_used : v ∈ St₄.env.usedVars := St₄_keys_sub hv_St₄
      have hv_St₅_used : v ∈ St₅.env.usedVars := by
        rw [St₅_used]; exact List.mem_append_right _ hv_St₄_used
      exact St₇_sub_St₈_used (St₅_sub_St₇_used hv_St₅_used)
    · -- 4. CoversUsedVars St₈.env.usedVars (Term.all vs D P)
      intro v hv
      rw [B.fv, List.mem_append] at hv
      rcases hv with hv_D | hv_P
      · -- v ∈ B.fv D → covers_D → St₁.env.usedVars → ⊆ St₈.env.usedVars
        exact St₁_sub_St₈_used (covers_D v hv_D)
      · -- v ∈ (B.fv P).removeAll vs → v ∈ B.fv P → covers_P → St₄.env.usedVars → chain
        have hv_fvP : v ∈ B.fv P := (List.mem_filter.mp hv_P).1
        have hv_St₄_used : v ∈ St₄.env.usedVars := covers_P v hv_fvP
        have hv_St₅_used : v ∈ St₅.env.usedVars := by
          rw [St₅_used]; exact List.mem_append_right _ hv_St₄_used
        exact St₇_sub_St₈_used (St₅_sub_St₇_used hv_St₅_used)
    · -- 5. σ = α.toSMTType (already resolved via simp only [BType.toSMTType] at *)
      trivial
    · -- 6. typing of the forall term
      -- Build typing in St₅.types, then strengthen to St₈.types.update zs τs.
      -- Lookup of vs[i] in St₃.types: via addToContext_forIn.
      have vs_typing_St₃ : ∀ (i : ℕ) (hi : i < vs.length),
          St₃.types.lookup vs[i] = some (τs[i]'(vs_τs_len ▸ hi)) := by
        intro i hi
        rw [St₃_types]
        have hi_τs : i < τs.length := vs_τs_len ▸ hi
        -- St₃.types = (vs.zip τs).foldl insert St₂.types.
        -- Lookup of vs[i] in (vs.zip τs).foldl insert _ = some τs[i]
        exact foldl_insert_lookup_zip vs_nodup hi hi_τs
      -- Lookup of vs[i] in St₅.types: chain St₃ ⊆ St₄ ⊆ St₅
      have vs_typing_St₅ : ∀ (i : ℕ) (hi : i < vs.length),
          St₅.types.lookup vs[i] = some (τs[i]'(vs_τs_len ▸ hi)) := fun i hi => by
        apply AList.lookup_of_subset
          (AList.subset_trans St₃_sub_St₄_types St₄_sub_St₅_types)
        exact vs_typing_St₃ i hi
      -- typing of the app (D_enc, pairl)
      have typ_app_St₅ : St₅.types ⊢ˢ
          SMT.Term.app D_enc (List.map SMT.Term.var zs).toPairl : SMTType.bool := by
        refine SMT.Typing.app _ _ _ τ.toSMTType .bool typ_D_enc_St₅ ?_
        rw [← τs_toProdl_eq]
        exact toPairl_typ
      -- typing of substList in St₅.types
      have typ_P_subst_St₅ : St₅.types ⊢ˢ
          SMT.substList vs (List.map SMT.Term.var zs) P_enc : SMTType.bool := by
        apply SMT_Typing_substList
        · exact SMT.Typing.weakening St₄_sub_St₅_types typ_P_enc
        · intro t ht
          rw [List.mem_map] at ht
          obtain ⟨z, _, rfl⟩ := ht
          simp [SMT.bv]
        · intro i hi_x hi_t hx
          have hi_zs : i < zs.length := by rw [List.length_map] at hi_t; exact hi_t
          have hi_τs : i < τs.length := vs_τs_len ▸ hi_x
          have hzi_typ : St₅.types.lookup zs[i] = some (τs[i]'(zs_len ▸ hi_zs)) :=
            zs_typing i hi_zs
          -- ⟨vs[i], τs[i]⟩ is the type at index i for both vs and zs (same τs)
          have hvi_typ : St₅.types.lookup vs[i] = some (τs[i]'hi_τs) :=
            vs_typing_St₅ i hi_x
          have h_get : (St₅.types.lookup vs[i]).get hx = τs[i]'hi_τs := by
            simp [hvi_typ]
          rw [h_get, List.getElem_map]
          -- Need: St₅.types ⊢ˢ .var zs[i] : τs[i]
          exact SMT.Typing.var _ zs[i] _ (by
            -- convert zs_typing to the right index form
            have : (τs[i]'(zs_len ▸ hi_zs)) = (τs[i]'hi_τs) := by rfl
            rw [← this]; exact hzi_typ)
      -- imp of the two gives the body typing
      have typ_body_St₅ : St₅.types ⊢ˢ
          SMT.Term.imp (SMT.Term.app D_enc (List.map SMT.Term.var zs).toPairl)
            (SMT.substList vs (List.map SMT.Term.var zs) P_enc) : SMTType.bool :=
        SMT.Typing.imp _ _ _ typ_app_St₅ typ_P_subst_St₅
      -- Now build the forall typing via the Typing.forall rule with Γ = St₈.types.
      -- (i) zs ∉ St₈.types: erasure removes zs.
      have zs_disj_St₈ : ∀ z ∈ zs, z ∉ St₈.types := fun z hz => by
        rw [St₈_types]
        exact AList.not_mem_foldl_erase_of_mem hz zs_nodup
      -- (iv) len_eq : zs.length = τs.length (given)
      -- (iii) 0 < zs.length: via zs_nemp
      have zs_len_pos : 0 < zs.length := List.length_pos_of_ne_nil zs_nemp
      -- Key fact: zs[i] ∈ St₅.types (via zs_typing)
      have zs_in_St₅ : ∀ z ∈ zs, z ∈ St₅.types := by
        intro z hz
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz
        exact AList.lookup_isSome.mp (Option.isSome_of_eq_some (zs_typing i hi))
      -- bv of (zs.map .var).toPairl is empty (extracted helpers)
      have bv_pairl_empty : SMT.bv ((List.map SMT.Term.var zs).toPairl) = [] :=
        bv_pairl_empty_helper zs
      have bv_subst_eq : ∀ t ∈ List.map SMT.Term.var zs, SMT.bv t = [] :=
        bv_subst_eq_helper zs
      -- (ii) zs ∉ bv body (extracted helper)
      have typ_P_St₅' : St₅.types ⊢ˢ P_enc : .bool :=
        SMT.Typing.weakening St₄_sub_St₅_types typ_P_enc
      have zs_disj_bv_body : ∀ z ∈ zs, z ∉ SMT.bv
          (SMT.Term.imp (SMT.Term.app D_enc (List.map SMT.Term.var zs).toPairl)
            (SMT.substList vs (List.map SMT.Term.var zs) P_enc)) :=
        zs_disj_bv_body_noflag_helper typ_app_St₅ typ_P_St₅' zs_in_St₅
      -- (v) St₈.types.update zs τs ⊢ˢ body : .bool via strengthening from St₅.types.
      -- Entries in update zs τs come either from update (k ∈ zs, τ_k = τs[idxOf k])
      -- or from St₈.types (via St₈ ⊆ St₇ ⊆ St₅).
      have St₈_types_combined : St₈.types =
          zs.foldl (fun Γ w => AList.erase w Γ)
            (vs.foldl (fun Γ w => AList.erase w Γ) St₅.types) := by
        rw [St₈_types, St₇_types]
      have h_entries_sub : (St₈.types.update zs τs).entries ⊆ St₅.types.entries :=
        h_entries_sub_helper zs_nodup zs_len St₈_types_combined (fun _ h => h)
          (fun i hi hi_τs => by
            rw [St₅_types]
            exact AList.mem_lookup_iff.mp (foldl_insert_lookup_zip zs_nodup hi hi_τs))
      -- Helper facts for h_fv_sub:
      -- fv of (zs.map .var).toPairl ⊆ zs (extracted helper)
      have fv_pairl_sub_zs : ∀ v ∈ SMT.fv (List.map SMT.Term.var zs).toPairl, v ∈ zs :=
        fv_pairl_sub_zs_helper zs
      have h_fv_sub : ∀ v ∈ SMT.fv
          (SMT.Term.imp (SMT.Term.app D_enc (List.map SMT.Term.var zs).toPairl)
            (SMT.substList vs (List.map SMT.Term.var zs) P_enc)),
          v ∈ St₈.types.update zs τs := by
        intro v hv_body
        rw [SMT.TypeContext.mem_update_iff (hlen := zs_len)]
        unfold SMT.fv at hv_body
        rw [List.mem_append] at hv_body
        rcases hv_body with hv_app | hv_subst
        · -- v ∈ fv (app D_enc pairs) = fv D_enc ∪ fv pairs
          unfold SMT.fv at hv_app
          rw [List.mem_append] at hv_app
          rcases hv_app with hv_D | hv_pairs
          · -- v ∈ fv D_enc → v ∈ St₁.types, then v ∉ vs, v ∉ zs, v ∈ St₈.types
            right
            have hv_St₁ : v ∈ St₁.types := SMT.Typing.mem_context_of_mem_fv typ_D_enc hv_D
            have hv_not_vs : v ∉ vs := fun hvs => vs_disj_St₁ v hvs hv_St₁
            have hv_St₁_used : v ∈ St₁.env.usedVars := St₁_keys_sub hv_St₁
            have hv_St₄_used : v ∈ St₄.env.usedVars :=
              St₃_sub_St₄ (St₁_sub_St₃_used hv_St₁_used)
            have hv_not_zs : v ∉ zs := fun hvz => zs_not_used v hvz hv_St₄_used
            -- v ∈ St₅.types (via St₁ ⊆ St₅)
            have hv_St₅ : v ∈ St₅.types := AList.mem_of_subset St₁_sub_St₅_types hv_St₁
            -- v ∈ St₈.types via preserved through erasures
            obtain ⟨σ, hσ⟩ := Option.isSome_iff_exists.mp (AList.lookup_isSome.mpr hv_St₅)
            have hv_entry : ⟨v, σ⟩ ∈ St₅.types.entries := AList.mem_lookup_iff.mp hσ
            have hv_St₇_entry : ⟨v, σ⟩ ∈ St₇.types.entries := by
              rw [St₇_types]
              exact AList.mem_foldl_erase_of_not_mem_keys hv_entry hv_not_vs
            have hv_St₈_entry : ⟨v, σ⟩ ∈ St₈.types.entries := by
              rw [St₈_types]
              exact AList.mem_foldl_erase_of_not_mem_keys hv_St₇_entry hv_not_zs
            exact AList.mem_keys.mpr (List.mem_map.mpr ⟨⟨v, σ⟩, hv_St₈_entry, rfl⟩)
          · -- v ∈ fv pairs → v ∈ zs
            left
            exact fv_pairl_sub_zs v hv_pairs
        · -- v ∈ fv (substList vs (zs.map .var) P_enc)
          rcases SMT_mem_fv_substList hv_subst with hv_P | ⟨t, ht, hv_t⟩
          · -- v ∈ fv P_enc
            right
            have hv_St₄ : v ∈ St₄.types := SMT.Typing.mem_context_of_mem_fv typ_P_enc hv_P
            -- v ∉ vs: if v ∈ vs and v ∈ fv result, then via SMT_not_mem_fv_substList_of_mem_vars
            -- we'd need ∃ t ∈ zs-vars, v ∈ fv t, giving v = z for z ∈ zs. Contradiction.
            have hv_not_vs : v ∉ vs := by
              intro hvs
              have hlen : vs.length ≤ (List.map SMT.Term.var zs).length := by
                rw [List.length_map]; exact le_of_eq (zs_len ▸ vs_τs_len)
              have all_bv_nil : ∀ t ∈ List.map SMT.Term.var zs, v ∉ SMT.fv t ∨ ∃ z ∈ zs, t = .var z := by
                intro t ht
                rw [List.mem_map] at ht
                obtain ⟨z, hz, rfl⟩ := ht
                right; exact ⟨z, hz, rfl⟩
              -- If ∀ t ∈ ts, v ∉ fv t, apply SMT_not_mem_fv_substList_of_mem_vars
              by_cases h_all_no_fv : ∀ t ∈ List.map SMT.Term.var zs, v ∉ SMT.fv t
              · exact SMT_not_mem_fv_substList_of_mem_vars hlen hvs h_all_no_fv hv_subst
              · -- Some t has v ∈ fv t, meaning v ∈ zs, contradicting vs ∩ zs = ∅.
                push_neg at h_all_no_fv
                obtain ⟨t, ht, hv_t⟩ := h_all_no_fv
                rw [List.mem_map] at ht
                obtain ⟨z, hz, rfl⟩ := ht
                simp only [SMT.fv, List.mem_singleton] at hv_t
                subst hv_t
                -- Now v ∈ zs and v ∈ vs
                -- Derive contradiction via zs_not_used and vs
                have hv_used : v ∈ St₄.env.usedVars :=
                  St₃_sub_St₄ (St₁_sub_St₃_used (used_sub_St₁ (vars_used_vs v hvs)))
                exact zs_not_used v hz hv_used
            -- v ∉ zs (via zs_not_types: v ∈ St₄.types, so v ∉ zs)
            have hv_not_zs : v ∉ zs := fun hvz => zs_not_types v hvz hv_St₄
            -- v ∈ St₅.types via St₄ ⊆ St₅
            have hv_St₅ : v ∈ St₅.types := AList.mem_of_subset St₄_sub_St₅_types hv_St₄
            -- v ∈ St₈.types via erasure preservation
            obtain ⟨σ, hσ⟩ := Option.isSome_iff_exists.mp (AList.lookup_isSome.mpr hv_St₅)
            have hv_entry : ⟨v, σ⟩ ∈ St₅.types.entries := AList.mem_lookup_iff.mp hσ
            have hv_St₇_entry : ⟨v, σ⟩ ∈ St₇.types.entries := by
              rw [St₇_types]
              exact AList.mem_foldl_erase_of_not_mem_keys hv_entry hv_not_vs
            have hv_St₈_entry : ⟨v, σ⟩ ∈ St₈.types.entries := by
              rw [St₈_types]
              exact AList.mem_foldl_erase_of_not_mem_keys hv_St₇_entry hv_not_zs
            exact AList.mem_keys.mpr (List.mem_map.mpr ⟨⟨v, σ⟩, hv_St₈_entry, rfl⟩)
          · -- v ∈ fv t for some t ∈ zs.map .var
            left
            rw [List.mem_map] at ht
            obtain ⟨z, hz, rfl⟩ := ht
            simp only [SMT.fv, List.mem_singleton] at hv_t
            exact hv_t ▸ hz
      have h_typ_update : St₈.types.update zs τs ⊢ˢ
          SMT.Term.imp (SMT.Term.app D_enc (List.map SMT.Term.var zs).toPairl)
            (SMT.substList vs (List.map SMT.Term.var zs) P_enc) : SMTType.bool :=
        SMT.Typing.strengthening_of_fv_subset h_entries_sub typ_body_St₅ h_fv_sub
      exact SMT.Typing.forall St₈.types zs τs _
        zs_disj_St₈ zs_disj_bv_body zs_len_pos zs_len h_typ_update
    · -- 7. preservation: extracted to `bullet7_noflag_helper`.
      exact bullet7_noflag_helper vs_nodup zs_nodup St₂_types St₃_types St₅_types
        St₇_types St₈_types St₂_used St₃_used D_preserves_types P_preserves_types
        used_sub_St₁
    · -- 8. ∃ Δ', renaming + denotation (structured as a series of helpers)
      -- Define Δ': agree with Δ_D on vs (for D_enc variables), else with Δ_P (for P_enc).
      set Δ' : SMT.RenamingContext.Context := fun v =>
        if v ∈ vs then Δ_D v else Δ_P v with Δ'_def
      -- Standard properties of Δ' (analogous to collect/lambda cases):
      have hΔ_D_ext_outside : ∀ v ∉ vs, Δ_D_ext v = Δ_D v := fun v hv => by
        rw [Δ_D_ext_def]; exact Function.updates_of_not_mem Δ_D vs _ v hv
      have Δ'_extends_Δ₀ : RenamingContext.Extends Δ' Δ₀ :=
        Δ'_def ▸ Δ'_extends_Δ₀_noflag_helper Δ_D_extends Δ_P_extends hΔ_D_ext_outside
      -- v ∈ vs implies v ∈ St₃.env.usedVars (addToContext prepends vs).
      have vs_sub_St₃_used : ∀ v ∈ vs, v ∈ St₃.env.usedVars := by
        intro v hvs
        rw [St₃_used, St₂_used]
        suffices ∀ (ws : List SMT.𝒱) (τs' : List SMTType) (acc : List SMT.𝒱),
            ws.length ≤ τs'.length → v ∈ ws →
            v ∈ (ws.zip τs').foldl (fun used p => p.1 :: used) acc by
          exact this vs τs St₁.env.usedVars (le_of_eq vs_τs_len) hvs
        intro ws
        induction ws with
        | nil => intro _ _ _ hv; exact absurd hv List.not_mem_nil
        | cons w ws' ih =>
          intro τs' acc hlen hv
          cases τs' with
          | nil => simp at hlen
          | cons τ' τs'' =>
            simp only [List.zip_cons_cons, List.foldl_cons]
            rcases List.mem_cons.mp hv with rfl | hv'
            · suffices ∀ (l : List (SMT.𝒱 × SMTType)) (acc' : List SMT.𝒱),
                  v ∈ acc' → v ∈ l.foldl (fun used p => p.1 :: used) acc' by
                exact this _ _ (List.mem_cons_self ..)
              intro l; induction l with
              | nil => exact fun _ h => h
              | cons _ _ ih' => intro acc' hmem; exact ih' _ (List.mem_cons_of_mem _ hmem)
            · exact ih τs'' _ (by simp at hlen; omega) hv'
      -- For v ∉ St₈.env.usedVars: trace back to show v ∉ St₄.env.usedVars and v ∉ zs.
      -- In either Δ_D or Δ_P branch, Δ' v = none.
      have Δ'_none_out : ∀ v ∉ St₈.env.usedVars, Δ' v = none :=
        Δ'_def ▸ Δ'_none_out_noflag_helper St₅_used St₇_used St₈_used
          St₃_sub_St₅_used St₅_sub_St₇_used St₇_sub_St₈_used
          vs_sub_St₃_used Δ_P_none
      -- Prove ExtendsOnSourceFV Δ' Δ₀ (Term.all vs D P)
      -- For fv(all vs D P) = fv D ∪ ((fv P) \ vs):
      -- - If v ∈ fv D: Δ_D extends Δ₀ on D, so Δ' v = Δ_D v = Δ₀ v.
      -- - If v ∈ fv P \ vs: Δ' v = Δ_P v (v ∉ vs branch).
      have hΔ_ext_outside : ∀ v ∉ vs, Δ_ext v = «Δ» v := fun v hv => by
        rw [Δ_ext_def]; exact Function.updates_of_not_mem «Δ» vs _ v hv
      have Δ'_src_ext : RenamingContext.ExtendsOnSourceFV Δ' «Δ» (Term.all vs D P) :=
        Δ'_def ▸ Δ'_src_ext_noflag_helper Δ_D_src_ext Δ_P_src_ext Δ_P_extends
          vs_not_D_fv hΔ_D_ext_outside hΔ_ext_outside
      -- Prove CoversFV Δ' (forall zs τs body) by case splitting on v ∈ fv body \ zs:
      -- D_enc (use Δ_D_covers + Δ_P_extends), pairs (in zs, contra), substList (use Δ_P).
      have fv_pairl_sub_zs : ∀ v ∈ SMT.fv (List.map SMT.Term.var zs).toPairl, v ∈ zs :=
        fv_pairl_sub_zs_helper zs
      have Δ'_covers : SMT.RenamingContext.CoversFV Δ'
          (SMT.Term.forall zs τs
            (SMT.Term.imp (SMT.Term.app D_enc (List.map SMT.Term.var zs).toPairl)
              (SMT.substList vs (List.map SMT.Term.var zs) P_enc))) :=
        Δ'_def ▸ Δ'_covers_noflag_helper zs_len vs_τs_len typ_D_enc typ_P_enc
          vs_disj_St₁ Δ_D_covers Δ_P_covers Δ_P_extends hΔ_D_ext_outside fv_pairl_sub_zs
      refine ⟨Δ', Δ'_covers, Δ'_extends_Δ₀, Δ'_src_ext, Δ'_none_out, ?_⟩
      -- Phase 1: Prerequisites for retract_forallVal_eq_sInter_sep.
      have h𝒟_eq : 𝒟 = 𝒟' := by
        have := den_D_eq ▸ den_D
        simp only [Option.some.injEq, PSigma.mk.injEq] at this
        exact this.1.symm
      have zs_len_pos : 0 < zs.length :=
        List.length_pos_of_ne_nil zs_nemp
      have vs_zs_len : vs.length = zs.length := by rw [vs_τs_len, zs_len]
      have zs_not_fv_D : ∀ z ∈ zs, z ∉ SMT.fv D_enc := by
        intro z hz hz_fv
        have hz_St₁ : z ∈ St₁.types :=
          SMT.Typing.mem_context_of_mem_fv typ_D_enc hz_fv
        have hz_used : z ∈ St₄.env.usedVars :=
          St₃_sub_St₄ (St₁_sub_St₃_used (St₁_keys_sub hz_St₁))
        exact zs_not_used z hz hz_used
      have denD'_func : ⟦τ.toSMTType⟧ᶻ.IsFunc 𝔹 denD'.fst := by
        have : denD'.fst ∈ ⟦τ.toSMTType⟧ᶻ.funs 𝔹 := by
          simpa [denD'_type, SMTType.toZFSet] using denD'.snd.snd
        exact ZFSet.mem_funs.mp this
      -- Phase 2: D_enc denotation under Δ' (coincides with Δ_D on fv D_enc).
      obtain ⟨Δ'_agrees_Δ_D_on_D, hcov_D_Δ', den_D_Δ'⟩ :=
        Δ'_agrees_noflag_bundle.{u} Δ'_def hΔ_D_ext_outside typ_D_enc vs_disj_St₁
          Δ_D_covers Δ_P_extends den_D_enc
      -- D_enc under zs-updates (disjoint from fv D_enc)
      have hcov_D_upd := hcov_D_upd_helper.{u} (zs := zs) zs_not_fv_D hcov_D_Δ'
      have den_D_upd_eq := den_D_upd_eq_helper.{u} (zs := zs) zs_not_fv_D hcov_D_Δ' den_D_Δ'
      -- Phase 3: Define imp_body and forall_term, prove body totality/typing.
      set imp_body : SMT.Term :=
        (SMT.Term.app D_enc (List.map SMT.Term.var zs).toPairl).imp
          (SMT.substList vs (List.map SMT.Term.var zs) P_enc) with imp_body_def
      have hcov_imp_upd := hcov_imp_upd_helper.{u} zs_nodup (τs := τs) Δ'_covers
      have hgo_cov := hgo_cov_helper (τs := τs) Δ'_covers
      have hpairl_cov := hpairl_cov_helper.{u} (Δ' := Δ') zs_nodup fv_pairl_sub_zs
      have hpairl_den :=
        hpairl_den_helper.{u} (Δ' := Δ') zs_len zs_nodup zs_len_pos hpairl_cov
      have hcov_appD_upd := hcov_appD_upd_helper.{u} hcov_D_upd hpairl_cov
      have hdenote_appD_upd :=
        hdenote_appD_upd_helper.{u} (D_enc := D_enc) (Δ' := Δ') (denD' := denD') (τ := τ)
          zs_len zs_len_pos τs_toProdl_eq denD'_type denD'_func
          hpairl_cov hpairl_den hcov_D_upd den_D_upd_eq hcov_appD_upd
      have hcov_subst_upd :=
        hcov_subst_upd_helper.{u} imp_body P_enc (vs := vs) zs_nodup (τs := τs)
          Δ'_covers
          (hv_to_imp := fun hv => by
            show _ ∈ SMT.fv (SMT.Term.imp _ _)
            exact SMT.fv.mem_imp (Or.inr hv))
      -- `hsubst_spec`: for every zs-witness w, the substList form denotes to some
      -- Dsubst of type `.bool`. Proof factored into `hsubst_spec_helper`.
      have hsubst_spec :=
        hsubst_spec_helper.{u}
          (vs := vs) (zs := zs) (τs := τs)
          (Δ' := Δ') (P_enc := P_enc) (St₄types := St₄.types)
          vs_nodup zs_nodup vs_zs_len vs_τs_len zs_len
          (Δ'_outside_vs_isSome := fun v hvvs hv => by
            rw [Δ'_def]; simp [hvvs]; exact Δ_P_covers v hv)
          (Δ'_outside_vs_wt := fun v hvvs d hd τ hτ => by
            rw [Δ'_def] at hd; simp [hvvs] at hd
            exact Δ_P_wt v d hd τ hτ)
          (vs_sub_St₄_types :=
            vs_sub_types_helper vs_nodup vs_τs_len St₃_types St₃_sub_St₄_types)
          (vs_typing_St₄ := fun i hi => by
            have h_St₃_lookup : St₃.types.lookup vs[i] =
                some (τs[i]'(vs_τs_len ▸ hi)) := by
              rw [St₃_types]
              exact foldl_insert_lookup_zip vs_nodup hi (vs_τs_len ▸ hi)
            exact AList.lookup_of_subset St₃_sub_St₄_types h_St₃_lookup)
          (zs_not_bv_P :=
            zs_not_bv_P_helper zs_len St₄_sub_St₅_types typ_P_enc zs_typing)
          (zs_not_St₄_types := zs_not_types)
          typ_P_enc hcov_subst_upd
      obtain ⟨himp_total, himp_ty⟩ :=
        himp_total_ty_bundle.{u} zs_len imp_body_def hcov_imp_upd
          (happD_bool := fun w hw => by
            obtain ⟨_, Dapp, hDapp_ty, _, hDapp_den⟩ := hdenote_appD_upd w hw
            exact ⟨Dapp, hDapp_ty, hDapp_den⟩)
          hsubst_spec
      -- Phase 4: Semantic bridge relating imp_body's value at w to the B-side
      -- quantification clause (mirrors `collect_hbridge` with imp_body instead of ite_body).
      have h_den_P_generic : ∀ {x_fin : Fin vs.length → B.Dom},
          (∀ i, (x_fin i).snd.fst = τ.get vs.length i ∧
                (x_fin i).fst ∈ ⟦τ.get vs.length i⟧ᶻ) →
          ZFSet.ofFinDom x_fin ∈ 𝒟' →
          ⟦(B.Term.abstract.go P vs «Δ» (fun v hv hvs => Δ_fv v
            (B.fv.mem_all (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ.isSome = true := by
        intro x_fin hx_typ hx_fin_in
        exact den_P_cond hx_typ hx_fin_in
      have h_den_P_bool : ∀ {x_fin : Fin vs.length → B.Dom},
          (∀ i, (x_fin i).snd.fst = τ.get vs.length i ∧
                (x_fin i).fst ∈ ⟦τ.get vs.length i⟧ᶻ) →
          ZFSet.ofFinDom x_fin ∈ 𝒟' →
          ∀ (Pz : ZFSet.{u}) (P_ty : BType) (hP_val : Pz ∈ ⟦P_ty⟧ᶻ),
          ⟦(B.Term.abstract.go P vs «Δ» (fun v hv hvs => Δ_fv v
            (B.fv.mem_all (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ =
              some ⟨Pz, ⟨P_ty, hP_val⟩⟩ →
          P_ty = .bool := by
        intro x_fin _hx_typ hx_fin_in Pz P_ty hP_val hPz_den
        set Δ_ext_fin : B.RenamingContext.Context :=
          Function.updates «Δ» vs (List.ofFn fun i => some (x_fin i))
        have Δ_fv_P_fin : ∀ v ∈ B.fv P, (Δ_ext_fin v).isSome := by
          intro v hv
          show (Function.updates «Δ» vs _ v).isSome = true
          rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup]
          split_ifs with hvs
          · simp [List.getElem_ofFn]
          · exact Δ_fv v (fv.mem_all (.inr ⟨hv, hvs⟩))
        have hPz_abs : ⟦P.abstract Δ_ext_fin Δ_fv_P_fin⟧ᴮ =
            some ⟨Pz, ⟨P_ty, hP_val⟩⟩ := by
          rw [← denote_term_abstract_go_eq_term_abstract vs_nodup vs_nemp x_fin Δ_fv_P_fin]
          exact hPz_den
        exact (denote_welltyped_eq
          (t := P.abstract Δ_ext_fin Δ_fv_P_fin)
          ⟨_, WFTC.of_abstract, .bool, by convert Typing.of_abstract Δ_fv_P_fin typP⟩
          hPz_abs).symm
      have htot_forall_raw :
          ∀ {x : Fin zs.length → SMT.Dom.{u}},
          (∀ i, (x i).snd.fst = τs[i.val]'(zs_len ▸ i.isLt) ∧
            (x i).fst ∈ ⟦τs[i.val]'(zs_len ▸ i.isLt)⟧ᶻ) →
          ⟦(SMT.Term.abstract.go imp_body zs Δ' hgo_cov).uncurry x⟧ˢ.isSome = true :=
        htot_forall_raw_helper.{u} (zs := zs) (τs := τs) zs_len
          (Δ_ctx := Δ') (hgo_cov := hgo_cov) himp_total
      have forallVal_isSome :=
        forallVal_isSome_helper.{u} zs_len zs_len_pos Δ'_covers htot_forall_raw
      obtain ⟨forallVal, hforallVal⟩ := Option.isSome_iff_exists.mp forallVal_isSome
      -- Build denT' := forallVal
      refine ⟨forallVal, hforallVal, ?_, ?_⟩
      -- Part 1: ⟨T, .bool, hT⟩ ≘ᶻ forallVal
      · -- RDom has two components: type match (`.bool`) and retract equation.
        -- Extract T via rest_all.
        -- rest_all (after split_ifs) produces:
        --   ⟨sInter (𝔹.sep (fun y => ∃ x ∈ 𝒟', y = ...)), .bool, _⟩ = ⟨T, .bool, hT⟩
        -- Build hT_eq: sInter (...) = T
        simp only [Option.pure_def, Option.some.injEq, PSigma.mk.injEq] at rest_all
        obtain ⟨hT_eq_raw, _⟩ := rest_all
        -- Extract forallVal.snd.fst = .bool
        have hforallVal_ty : forallVal.snd.fst = .bool :=
          hforallVal_ty_helper.{u} zs_len zs_len_pos htot_forall_raw hforallVal
        refine ⟨hforallVal_ty, ?_⟩
        -- Goal: retract .bool forallVal.fst = T
        -- Apply `retract_forallVal_eq_sInter_sep`.
        -- Need hT_eq : sInter(...) = T in the form expected by the lemma.
        -- rest_all gave us: sInter (𝔹.sep (fun y => ∃ x ∈ 𝒟', y = ...)) = T.
        have 𝒟'_nonempty : 𝒟'.Nonempty :=
          𝒟'.eq_empty_or_nonempty.resolve_left h𝒟_empty
        -- hbridge: the semantic bridge mirroring collect_hbridge.
        have hbridge : ∀ (x : ZFSet.{u}) (hx_mem : x ∈ ⟦τ.toSMTType⟧ᶻ),
            let x_B := retract τ x
            let hx_B_mem : x_B ∈ ⟦τ⟧ᶻ := retract_mem_of_canonical τ hx_mem
            let x_fin : Fin vs.length → B.Dom := fun i =>
              ⟨x_B.get vs.length i, ⟨τ.get vs.length i,
                get_mem_type_of_isTuple (hasArity_of_mem_toZFSet τ_hasArity hx_B_mem)
                  τ_hasArity hx_B_mem⟩⟩
            ∀ (w : Fin zs.length → SMT.Dom)
              (_hw : ∀ i, (w i).snd.fst = τs[i]'(zs_len ▸ i.isLt) ∧
                (w i).fst ∈ ⟦τs[i]'(zs_len ▸ i.isLt)⟧ᶻ)
              (_hw_smt : Fin.foldl (zs.length - 1)
                (fun acc i => acc.pair (w ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩).fst)
                (w ⟨0, zs_len_pos⟩).fst = x)
              (body_val : SMT.Dom),
              ⟦imp_body.abstract
                (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
                (hcov_imp_upd w)⟧ˢ = some body_val →
              (body_val.fst = zftrue ↔
                (x_B ∉ 𝒟' ∨
                 ∀ (Px : ZFSet.{u}) (P_ty : BType) (hP_val : Px ∈ ⟦P_ty⟧ᶻ),
                   ⟦(B.Term.abstract.go P vs «Δ» (fun v hv hvs => Δ_fv v
                     (B.fv.mem_all (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ =
                     some ⟨Px, ⟨P_ty, hP_val⟩⟩ → Px = zftrue)) := by
          intro x hx_mem
          -- Unfold let-bindings before introducing the remaining arguments.
          simp only []
          intro w hw hw_smt body_val hbody_val
          -- The B-level witness x_B and its B-domain decomposition.
          set x_B : ZFSet.{u} := retract τ x with x_B_def
          have hx_B_mem : x_B ∈ ⟦τ⟧ᶻ := retract_mem_of_canonical τ hx_mem
          obtain ⟨hx_mem_smt, Dapp, hDapp_ty, hDapp_val, hDapp_den⟩ := hdenote_appD_upd w hw
          obtain ⟨Dsubst, hDsubst_den, hDsubst_ty⟩ := hsubst_spec w hw
          obtain ⟨Dimp, hDimp, hDimp_ty⟩ :=
            _root_.denote_imp_some_bool.{u} hDapp_den hDapp_ty hDsubst_den hDsubst_ty
          -- Reconcile imp_body denotation with denote_imp_some_bool's LHS.
          have hBody_eq_Dimp : ⟦imp_body.abstract
              (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
              (hcov_imp_upd w)⟧ˢ = some Dimp := by
            convert hDimp using 3
            all_goals
              first
              | rfl
              | (simp only [imp_body_def, SMT.Term.abstract])
          have hbody_eq_Dimp : body_val = Dimp :=
            Option.some.inj (hbody_val.symm.trans hBody_eq_Dimp)
          have hDapp_mem_𝔹 : Dapp.fst ∈ 𝔹 := by
            have := Dapp.snd.snd; rwa [hDapp_ty] at this
          -- Dapp.fst = fapply denD'.fst x, via hDapp_val + hw_smt rewrite.
          have hDapp_val_x : Dapp.fst = @ᶻdenD'.fst ⟨x,
              by rw [ZFSet.is_func_dom_eq denD'_func]; exact hx_mem⟩ := by
            rw [hDapp_val]
            have hsub : (⟨Fin.foldl (zs.length - 1)
                (fun acc i => acc.pair (w ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩).fst)
                (w ⟨0, zs_len_pos⟩).fst,
                by rw [ZFSet.is_func_dom_eq denD'_func]; exact hx_mem_smt⟩
                : {z // z ∈ denD'.fst.Dom}) =
                ⟨x, by rw [ZFSet.is_func_dom_eq denD'_func]; exact hx_mem⟩ := by
              apply Subtype.ext; exact hw_smt
            rw [hsub]
          have hRetr_denD' : retract (BType.set τ) denD'.fst = 𝒟' := by
            rw [denD'_retract]; exact h𝒟_eq
          have hx_B_𝒟_iff : x_B ∈ 𝒟' ↔ Dapp.fst = zftrue := by
            rw [hDapp_val_x]
            have hcan : ZFSet.fapply (BType.canonicalIsoSMTType τ).1
                (is_func_is_pfunc (BType.canonicalIsoSMTType τ).2.1)
                ⟨x_B, ZFSet.mem_dom (is_func_is_pfunc
                  (BType.canonicalIsoSMTType τ).2.1)
                  (canonical_pair_of_retract τ hx_mem)⟩ = x :=
              canonical_of_retract τ hx_mem
            have hsub_x : (⟨x,
                by rw [ZFSet.is_func_dom_eq denD'_func]; exact hx_mem⟩
                : {z // z ∈ denD'.fst.Dom}) =
                ⟨ZFSet.fapply (BType.canonicalIsoSMTType τ).1
                  (is_func_is_pfunc (BType.canonicalIsoSMTType τ).2.1)
                  ⟨x_B, ZFSet.mem_dom (is_func_is_pfunc
                    (BType.canonicalIsoSMTType τ).2.1)
                    (canonical_pair_of_retract τ hx_mem)⟩,
                  by rw [ZFSet.is_func_dom_eq denD'_func]
                     exact fapply_mem_range _ _⟩ := by
              apply Subtype.ext; exact hcan.symm
            rw [hsub_x]
            rw [← hRetr_denD']
            rw [retract, mem_sep]
            constructor
            · rintro ⟨hx_B_α, hmem⟩
              rw [dif_pos hx_B_α, dif_pos denD'_func] at hmem
              simpa using hmem
            · intro hfapp
              refine ⟨hx_B_mem, ?_⟩
              rw [dif_pos hx_B_mem, dif_pos denD'_func]
              simpa using hfapp
          rcases (ZFSet.ZFBool.mem_𝔹_iff _).mp hDapp_mem_𝔹 with hDapp_false | hDapp_true
          · -- ZFFALSE case: body_val.fst = zftrue (vacuously), x_B ∉ 𝒟'.
            have hDimp_eq : ⟦((@ˢD_enc) (List.map SMT.Term.var zs).toPairl
                ⇒ˢ SMT.substList vs (List.map SMT.Term.var zs) P_enc).abstract
                (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
                (by simpa [imp_body_def] using hcov_imp_upd w)⟧ˢ =
                some ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
              have := denote_imp_eq_zftrue_of_zffalse_left.{u}
                hDapp_den hDapp_ty hDapp_false hDsubst_den hDsubst_ty
              convert this using 3
              all_goals first | rfl | (simp only [SMT.Term.abstract])
            have hbody_is_true_dom : body_val = ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
              have hDimp_eq' : ⟦imp_body.abstract
                  (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
                  (hcov_imp_upd w)⟧ˢ = some ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
                convert hDimp_eq using 3
              exact Option.some.inj (hbody_val.symm.trans hDimp_eq')
            have hbody_fst_true : body_val.fst = zftrue := by
              rw [hbody_is_true_dom]
            have hx_B_not_𝒟 : x_B ∉ 𝒟' := by
              intro hcon
              have : Dapp.fst = zftrue := hx_B_𝒟_iff.mp hcon
              rw [this] at hDapp_false
              exact ZFSet.zftrue_ne_zffalse hDapp_false
            constructor
            · intro _; exact Or.inl hx_B_not_𝒟
            · intro _; exact hbody_fst_true
          · -- ZFTRUE CASE: x_B ∈ 𝒟', so body_val.fst = Dsubst.fst = P_val.
            have hx_B_in_𝒟 : x_B ∈ 𝒟' := hx_B_𝒟_iff.mpr hDapp_true
            have hx_B_arity : x_B.hasArity vs.length :=
              hasArity_of_mem_toZFSet τ_hasArity hx_B_mem
            have hx_arity : x.hasArity zs.length := by
              rw [← vs_zs_len]
              exact hasArity_of_mem_toSMTZFSet τ_hasArity hx_mem
            let x_fin : Fin vs.length → B.Dom := fun i =>
              ⟨x_B.get vs.length i, τ.get vs.length i,
                get_mem_type_of_isTuple hx_B_arity τ_hasArity hx_B_mem⟩
            set Δ_ext_x : B.RenamingContext.Context :=
              Function.updates «Δ» vs (List.ofFn fun i => some (x_fin i))
              with Δ_ext_x_def
            have Δ_fv_P_x : ∀ v ∈ B.fv P, (Δ_ext_x v).isSome = true := by
              intro v hv
              rw [Δ_ext_x_def, Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup]
              split_ifs with hvs
              · simp [List.getElem_ofFn]
              · exact Δ_fv v (B.fv.mem_all (.inr ⟨hv, hvs⟩))
            have h_ofFinDom_eq_x : ZFSet.ofFinDom x_fin = x_B :=
              ZFSet.ofFinDom_get (List.length_pos_iff.mpr vs_nemp)
                (fun i => get_mem_type_of_isTuple hx_B_arity τ_hasArity hx_B_mem)
                hx_B_arity τ_hasArity
            have hx_fin_in_𝒟 : ZFSet.ofFinDom x_fin ∈ 𝒟' := h_ofFinDom_eq_x ▸ hx_B_in_𝒟
            have hx_fin_typ : ∀ i, (x_fin i).snd.fst = τ.get vs.length i ∧
                (x_fin i).fst ∈ ⟦τ.get vs.length i⟧ᶻ :=
              fun i => ⟨rfl, (x_fin i).snd.snd⟩
            have hP_isSome_x := h_den_P_generic hx_fin_typ hx_fin_in_𝒟
            obtain ⟨⟨P_val, P_ty_raw, hP_val_raw⟩, hP_den_x_raw⟩ :=
              Option.isSome_iff_exists.mp hP_isSome_x
            have hP_ty_bool : P_ty_raw = BType.bool :=
              h_den_P_bool hx_fin_typ hx_fin_in_𝒟 P_val P_ty_raw hP_val_raw hP_den_x_raw
            subst hP_ty_bool
            have h_den_P_x : ⟦P.abstract Δ_ext_x Δ_fv_P_x⟧ᴮ =
                some ⟨P_val, ⟨BType.bool, hP_val_raw⟩⟩ := by
              rw [← denote_term_abstract_go_eq_term_abstract vs_nodup vs_nemp x_fin Δ_fv_P_x]
              exact hP_den_x_raw
            have hw_fst_eq : ∀ i : Fin zs.length, (w i).fst = x.get zs.length i := by
              exact foldl_pair_inj_get zs_len_pos hx_arity (fun i => (w i).fst) hw_smt
            have hτs_i : ∀ (i : Fin zs.length),
                τs[i.val]'(zs_len ▸ i.isLt) =
                  (τ.get vs.length ⟨i.val, by rw [vs_zs_len]; exact i.isLt⟩).toSMTType := by
              intro i
              have hvi_lt : i.val < vs.length := by rw [vs_zs_len]; exact i.isLt
              have heq := toSMTType_get_eq_fromProdl_getElem τ_hasArity hvi_lt
              rw [heq]
              simp [τs_eq]
            set Δ_D_ext_x : SMT.RenamingContext.Context :=
              Function.updates Δ_D vs
                (List.ofFn fun (i : Fin vs.length) => B.RenamingContext.toSMT Δ_ext_x vs[i])
              with Δ_D_ext_x_def
            -- Δ₀_hybrid_x: at vs use Δ_D_ext_x, elsewhere Δ_P when in used_St₄, else none.
            set Δ₀_hybrid_x : SMT.RenamingContext.Context := fun v =>
              if v ∈ vs then Δ_D_ext_x v
              else if v ∈ St₄.env.usedVars then Δ_P v
              else none
              with Δ₀_hybrid_x_def
            have vs_sub_St₄_used : ∀ v ∈ vs, v ∈ St₄.env.usedVars := fun v hv =>
              St₃_sub_St₄ (vs_sub_St₃_used v hv)
            have Δ₀_hybrid_ext_P_x :
                RenamingContext.ExtendsOnSourceFV Δ₀_hybrid_x Δ_ext_x P :=
              Δ₀_hybrid_ext_P_x_helper
                («Δ» := «Δ») (Δ_ext := Δ_ext) (Δ_ext_x := Δ_ext_x)
                (Δ_D_ext_x := Δ_D_ext_x) (Δ_P := Δ_P)
                (Δ₀_hybrid_x := Δ₀_hybrid_x) (used_St₄ := St₄.env.usedVars)
                (P := P)
                (fun v hvs => by
                  rw [Δ_ext_x_def]
                  exact Function.updates_of_not_mem «Δ» vs _ v hvs)
                (fun v hvs => by
                  rw [Δ_ext_def]
                  exact Function.updates_of_not_mem «Δ» vs _ v hvs)
                Δ_P_src_ext covers_P
                (fun v => by rw [Δ₀_hybrid_x_def])
                (fun i hi => by
                  rw [Δ_D_ext_x_def, Function.updates_eq_if
                    (by rw [List.length_ofFn]) vs_nodup,
                    dif_pos (List.getElem_mem hi)]
                  simp only [List.getElem_ofFn, Fin.getElem_fin, List.getElem_idxOf])
            have Δ₀_hybrid_x_none : ∀ v ∉ St₄.env.usedVars, Δ₀_hybrid_x v = none := by
              intro v hv
              show (if v ∈ vs then Δ_D_ext_x v else _) = none
              have hv_not_vs : v ∉ vs := fun hvs => hv (vs_sub_St₄_used v hvs)
              rw [if_neg hv_not_vs, if_neg hv]
            have Δ₀_hybrid_x_wt :
                ∀ (v : SMT.𝒱) (d : SMT.Dom), Δ₀_hybrid_x v = some d →
                ∀ τ_v, St₄.types.lookup v = some τ_v → d.snd.fst = τ_v :=
              Δ₀_hybrid_x_wt_helper
                (Δ_ext_x := Δ_ext_x) (x_fin := x_fin)
                (Δ_D_ext_x := Δ_D_ext_x) (Δ_P := Δ_P)
                (Δ₀_hybrid_x := Δ₀_hybrid_x) (St₄types := St₄.types)
                (used_St₄ := St₄.env.usedVars) (τs := τs) (τ := τ)
                vs_τs_len Δ_P_wt St₄_keys_sub
                (fun v => by rw [Δ₀_hybrid_x_def])
                (fun i hi => by
                  rw [Δ_D_ext_x_def, Function.updates_eq_if
                    (by rw [List.length_ofFn]) vs_nodup,
                    dif_pos (List.getElem_mem hi)]
                  simp only [List.getElem_ofFn, Fin.getElem_fin, List.getElem_idxOf])
                (fun i hi => by
                  show Function.updates «Δ» vs _ vs[i] = _
                  rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup,
                    dif_pos (List.getElem_mem hi)]
                  simp only [List.getElem_ofFn]
                  simp [List.idxOf_getElem vs_nodup])
                (fun i hi => by
                  rw [St₃_types] at *
                  exact AList.lookup_of_subset St₃_sub_St₄_types
                    (foldl_insert_lookup_zip vs_nodup hi (vs_τs_len ▸ hi)))
                (fun i => rfl)
                (fun i => by
                  have := hτs_i ⟨i.val, zs_len ▸ vs_τs_len ▸ i.isLt⟩
                  simp only at this; exact this.symm)
            obtain ⟨Δ_P_x, hcov_Px, denT_x', Δ_P_x_extends, Δ_P_x_none, Δ_P_x_wt,
                hden_Px, hRDom_x, Δ_P_x_dom⟩ :=
              P_enc_total Δ_ext_x Δ_fv_P_x Δ₀_hybrid_x Δ₀_hybrid_ext_P_x Δ₀_hybrid_x_none
                Δ₀_hybrid_x_wt P_val hP_val_raw h_den_P_x
            have hdenT_x'_ty : denT_x'.snd.fst = BType.bool.toSMTType := hRDom_x.1
            have hdenT_x'_fst_eq : denT_x'.fst = P_val := by
              have := hRDom_x.2
              simp only [retract] at this
              exact this
            set Δ'_upd : SMT.RenamingContext.Context :=
              Function.updates Δ' zs (List.ofFn (fun i : Fin zs.length => some (w i)))
              with Δ'_upd_def
            set Δ_P_x_upd : SMT.RenamingContext.Context :=
              Function.updates Δ_P_x zs (List.ofFn (fun i : Fin zs.length => some (w i)))
              with Δ_P_x_upd_def
            have hΔ_upd_agree_substList :
                SMT.RenamingContext.AgreesOnFV Δ'_upd Δ_P_x_upd
                  (SMT.substList vs (List.map SMT.Term.var zs) P_enc) :=
              hΔ_upd_agree_substList_helper.{u}
                (Δ' := Δ') (Δ_P := Δ_P) (Δ_P_x := Δ_P_x)
                (Δ₀_hybrid_x := Δ₀_hybrid_x) (St₄types := St₄.types)
                (used_St₄ := St₄.env.usedVars) (P_enc := P_enc)
                zs_nodup vs_τs_len zs_len
                (fun v hvvs => by rw [Δ'_def]; simp [hvvs])
                (fun v hvvs hv_St₄_used => by
                  rw [Δ₀_hybrid_x_def]
                  show (if v ∈ vs then _ else if v ∈ St₄.env.usedVars
                    then Δ_P v else none) = Δ_P v
                  rw [if_neg hvvs, if_pos hv_St₄_used])
                Δ_P_x_extends Δ_P_covers typ_P_enc St₄_keys_sub w
            have hcov_substList_Px_upd : SMT.RenamingContext.CoversFV
                Δ_P_x_upd (SMT.substList vs (List.map SMT.Term.var zs) P_enc) := by
              intro v hv
              have hag := hΔ_upd_agree_substList hv
              have hcov_v := hcov_subst_upd w v hv
              show (Δ_P_x_upd v).isSome = true
              rw [show Δ'_upd = Function.updates Δ' zs
                (List.ofFn (fun i : Fin zs.length => some (w i))) from rfl] at hag
              rw [← hag]; exact hcov_v
            have hsubst_at_ΔPx : ⟦(SMT.substList vs (List.map SMT.Term.var zs) P_enc).abstract
                Δ_P_x_upd hcov_substList_Px_upd⟧ˢ = some Dsubst := by
              have h_transfer := SMT.RenamingContext.denote_congr_of_agreesOnFV
                (h1 := hcov_subst_upd w) (h2 := hcov_substList_Px_upd) hΔ_upd_agree_substList
              unfold SMT.RenamingContext.denote at h_transfer
              rw [← h_transfer]; exact hDsubst_den
            let Ds_x : List SMT.Dom := List.ofFn fun i : Fin vs.length =>
              w ⟨i.val, by rw [← vs_zs_len]; exact i.isLt⟩
            have hlen_xt_x : vs.length = (List.map SMT.Term.var zs).length := by
              rw [List.length_map]; exact vs_zs_len
            have hlen_xd_x : vs.length = Ds_x.length := by simp [Ds_x]
            have vs_not_bv_P : ∀ x_v ∈ vs, x_v ∉ SMT.bv P_enc := fun x_v hx_v hbv =>
              SMT.Typing.bv_notMem_context typ_P_enc x_v hbv
                (AList.mem_of_subset St₃_sub_St₄_types
                  (by
                    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx_v
                    rw [St₃_types]
                    exact AList.lookup_isSome.mp
                      (by rw [foldl_insert_lookup_zip vs_nodup hi (vs_τs_len ▸ hi)]; simp)))
            have hts_bv_nil_x : ∀ t ∈ List.map SMT.Term.var zs, SMT.bv t = [] := by
              intro t ht
              rw [List.mem_map] at ht; obtain ⟨z, _, rfl⟩ := ht; unfold SMT.bv; rfl
            have hts_fv_not_bv_x : ∀ t ∈ List.map SMT.Term.var zs,
                ∀ w' ∈ SMT.fv t, w' ∉ SMT.bv P_enc := by
              intro t ht v' hv'
              rw [List.mem_map] at ht
              obtain ⟨z', hz', rfl⟩ := ht
              simp only [SMT.fv, List.mem_singleton] at hv'
              subst hv'
              intro hbv
              -- z' ∈ zs, z' ∈ bv P_enc: z' ∉ St₄.types (zs_not_types) but bv in St₄.types
              -- (SMT.Typing.bv_notMem_context is reverse: v ∈ bv implies v ∉ types).
              -- Actually: bv_notMem_context states that v ∈ bv → v ∉ Γ if v ∈ Γ. So we need:
              have typ_P_enc_St₅ : St₅.types ⊢ˢ P_enc : .bool :=
                SMT.Typing.weakening St₄_sub_St₅_types typ_P_enc
              obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz'
              have hz_St₅ : zs[i] ∈ St₅.types :=
                AList.lookup_isSome.mp (by rw [zs_typing i hi]; simp)
              exact SMT.Typing.bv_notMem_context typ_P_enc_St₅ zs[i] hbv hz_St₅
            have hts_not_none_x : ∀ t ∈ List.map SMT.Term.var zs, t ≠ SMT.Term.none := by
              intro t ht; rw [List.mem_map] at ht; obtain ⟨z, _, rfl⟩ := ht; intro h; cases h
            have hts_fv_disj_xs_x : ∀ t ∈ List.map SMT.Term.var zs,
                ∀ v' ∈ SMT.fv t, v' ∉ vs := by
              intro t ht v' hv' hvs
              rw [List.mem_map] at ht
              obtain ⟨z, hz, rfl⟩ := ht
              simp only [SMT.fv, List.mem_singleton] at hv'
              subst hv'
              -- v' = z ∈ zs, v' ∈ vs → v' ∈ St₃.types ⊆ St₄.types, contradicting zs_not_types.
              have hv_St₃ : v' ∈ St₃.types := by
                obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hvs
                rw [St₃_types]
                exact AList.lookup_isSome.mp <| by
                  rw [foldl_insert_lookup_zip vs_nodup hi (vs_τs_len ▸ hi)]; simp
              have hv_St₄ : v' ∈ St₄.types := AList.mem_of_subset St₃_sub_St₄_types hv_St₃
              exact zs_not_types v' hz hv_St₄
            have h_cov_upd_x : SMT.RenamingContext.CoversFV
                (Function.updates Δ_P_x_upd vs (Ds_x.map Option.some)) P_enc :=
              h_cov_upd_x_helper.{u} (Δ_P_x := Δ_P_x) (Δ_P_x_upd := Δ_P_x_upd)
                vs_nodup zs_nodup hlen_xd_x Δ_P_x_upd_def hcov_Px
            have h_eq_x := SMT.RenamingContext.abstract_substList_denote P_enc vs
              (List.map SMT.Term.var zs) Ds_x hlen_xt_x hlen_xd_x vs_nodup
              vs_not_bv_P hts_bv_nil_x hts_fv_not_bv_x hts_not_none_x hts_fv_disj_xs_x
              (by
                intro i hi_x hi_t hi_d
                -- Show ts[i] = .var zs[i] denotes to Ds_x[i] = w ⟨i, _⟩.
                have hi_zs : i < zs.length := by rw [List.length_map] at hi_t; exact hi_t
                rw [List.getElem_map]
                have hlookup_zs : Δ_P_x_upd zs[i] = some (w ⟨i, hi_zs⟩) := by
                  rw [Δ_P_x_upd_def]
                  rw [Function.updates_eq_if (by rw [List.length_ofFn]) zs_nodup,
                    dif_pos (List.getElem_mem hi_zs)]
                  have hidx : zs.idxOf zs[i] = i := List.idxOf_getElem zs_nodup i hi_zs
                  simp only [List.getElem_ofFn]
                  refine congrArg some (congrArg w ?_)
                  apply Fin.ext
                  exact hidx
                have hcov_ti : SMT.RenamingContext.CoversFV Δ_P_x_upd
                    (SMT.Term.var zs[i]) := by
                  intro v hv
                  simp only [SMT.fv, List.mem_singleton] at hv
                  subst hv
                  rw [hlookup_zs]; simp
                refine ⟨hcov_ti, ?_⟩
                have hDs_i : Ds_x[i] = w ⟨i, by rw [← vs_zs_len]; exact hi_x⟩ := by
                  show (List.ofFn _)[i] = _
                  rw [List.getElem_ofFn]
                show SMT.denote ((SMT.Term.var zs[i]).abstract Δ_P_x_upd hcov_ti) = some Ds_x[i]
                rw [SMT.Term.abstract]
                show SMT.denote (PHOAS.Term.var ((Δ_P_x_upd zs[i]).get _)) = _
                simp only [SMT.denote]
                rw [hDs_i]
                congr 1
                have h_get_eq : (Δ_P_x_upd zs[i]).get (by rw [hlookup_zs]; simp) =
                    w ⟨i, hi_zs⟩ := Option.get_of_eq_some _ hlookup_zs
                show (Δ_P_x_upd zs[i]).get _ = w ⟨i, _⟩
                rw [show (Δ_P_x_upd zs[i]).get _ = w ⟨i, hi_zs⟩ from h_get_eq])
              hcov_substList_Px_upd h_cov_upd_x
            -- Δ_P_x_upd[vs↦Ds_x] agrees with Δ_P_x on fv(P_enc): at v ∈ vs, we match
            -- via foldl_pair_inj_get + canonical_of_retract; at v ∉ vs ∪ zs, directly.
            have h_upd_agree_x : SMT.RenamingContext.AgreesOnFV
                (Function.updates Δ_P_x_upd vs (Ds_x.map Option.some)) Δ_P_x P_enc := by
              intro v hv
              by_cases hvs : v ∈ vs
              · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hvs
                rw [Function.updates_eq_if
                  (by rw [List.length_map, List.length_ofFn]) vs_nodup,
                  dif_pos (List.getElem_mem hi)]
                simp only [List.getElem_map, List.idxOf_getElem vs_nodup]
                have hvi_mem : vs[i] ∈ vs := List.getElem_mem hi
                have hΔ_ext_x_vi : Δ_ext_x vs[i] = some (x_fin ⟨i, hi⟩) := by
                  show Function.updates «Δ» vs _ vs[i] = _
                  rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup,
                    dif_pos hvi_mem]
                  simp only [List.getElem_ofFn]
                  simp [List.idxOf_getElem vs_nodup]
                set d_smt : SMT.Dom :=
                  ⟨ZFSet.fapply (BType.canonicalIsoSMTType (τ.get vs.length ⟨i, hi⟩)).1
                    (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType _).2.1)
                    ⟨(x_fin ⟨i, hi⟩).fst, by
                      rw [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType _).2.1]
                      exact (x_fin ⟨i, hi⟩).snd.snd⟩,
                   (τ.get vs.length ⟨i, hi⟩).toSMTType, ZFSet.fapply_mem_range _ _⟩
                  with d_smt_def
                have htoSMT_vi : B.RenamingContext.toSMT Δ_ext_x vs[i] = some d_smt := by
                  simp only [B.RenamingContext.toSMT, hΔ_ext_x_vi, Option.pure_def,
                    Option.bind_eq_bind, Option.bind_some]
                  rfl
                have hΔ_D_ext_x_vi : Δ_D_ext_x vs[i] = some d_smt := by
                  rw [Δ_D_ext_x_def, Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup,
                    dif_pos hvi_mem]
                  simp only [List.getElem_ofFn, Fin.getElem_fin, List.getElem_idxOf]
                  exact htoSMT_vi
                have hΔ₀_hybrid_vi : Δ₀_hybrid_x vs[i] = some d_smt := by
                  show (if vs[i] ∈ vs then Δ_D_ext_x vs[i] else _) = some d_smt
                  rw [if_pos hvi_mem]; exact hΔ_D_ext_x_vi
                have hΔ_P_x_vi : Δ_P_x vs[i] = some d_smt := Δ_P_x_extends hΔ₀_hybrid_vi
                set i_zs : Fin zs.length := ⟨i, by rw [← vs_zs_len]; exact hi⟩
                have hDs_i : Ds_x[i] = w i_zs := by
                  show (List.ofFn _)[i] = _
                  rw [List.getElem_ofFn]
                rw [hDs_i, hΔ_P_x_vi]
                congr 1
                have hw_i_fst : (w i_zs).fst = x.get zs.length i_zs := hw_fst_eq i_zs
                have hw_i_ty : (w i_zs).snd.fst = τs[i]'(zs_len ▸ i_zs.isLt) := (hw i_zs).1
                have hw_i_mem : (w i_zs).fst ∈ ⟦τs[i]'(zs_len ▸ i_zs.isLt)⟧ᶻ := (hw i_zs).2
                have hτs_match : τs[i]'(zs_len ▸ i_zs.isLt) =
                    (τ.get vs.length ⟨i, hi⟩).toSMTType := by
                  have hτs_z := hτs_i i_zs
                  exact hτs_z
                have hd_smt_fst_eq :
                    d_smt.fst = ZFSet.fapply (BType.canonicalIsoSMTType (τ.get vs.length ⟨i, hi⟩)).1
                      (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType _).2.1)
                      ⟨x_B.get vs.length ⟨i, hi⟩, by
                        rw [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType _).2.1]
                        exact get_mem_type_of_isTuple hx_B_arity τ_hasArity hx_B_mem⟩ := by
                  rfl
                -- canonical(x_B.get i).fst = x.get zs.length i via retract_get_comm + canonical_of_retract.
                have h_canonical_eq :
                    (ZFSet.fapply (BType.canonicalIsoSMTType (τ.get vs.length ⟨i, hi⟩)).1
                      (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType _).2.1)
                      ⟨x_B.get vs.length ⟨i, hi⟩, by
                        rw [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType _).2.1]
                        exact get_mem_type_of_isTuple hx_B_arity τ_hasArity hx_B_mem⟩).val =
                    x.get zs.length i_zs :=
                  canonical_fapply_get_eq_get.{u} vs_zs_len hi τ_hasArity hx_mem
                    x_B_def hx_B_arity hx_B_mem
                have hd_smt_fst_eq_w : d_smt.fst = (w i_zs).fst := by
                  rw [hd_smt_fst_eq, h_canonical_eq, hw_i_fst]
                have hd_smt_ty : d_smt.snd.fst = τs[i]'(zs_len ▸ i_zs.isLt) := by
                  rw [d_smt_def]
                  show (τ.get vs.length ⟨i, hi⟩).toSMTType = _
                  exact hτs_match.symm
                apply SMT.RenamingContext.Dom_ext'
                · exact hw_i_fst.trans (h_canonical_eq.symm.trans hd_smt_fst_eq.symm)
                · exact hw_i_ty.trans hd_smt_ty.symm
              · rw [Function.updates_of_not_mem _ vs _ _ hvs]
                by_cases hvzs : v ∈ zs
                · exfalso
                  have hv_St₄ : v ∈ St₄.types :=
                    SMT.Typing.mem_context_of_mem_fv typ_P_enc hv
                  exact zs_not_types v hvzs hv_St₄
                · rw [Δ_P_x_upd_def, Function.updates_of_not_mem _ zs _ _ hvzs]
            have h_eq2_x := SMT.RenamingContext.denote_congr_of_agreesOnFV
              (h1 := h_cov_upd_x) (h2 := hcov_Px) h_upd_agree_x
            unfold SMT.RenamingContext.denote at h_eq2_x
            rw [h_eq_x, h_eq2_x, hden_Px] at hsubst_at_ΔPx
            have hDsubst_eq_denT : Dsubst = denT_x' :=
              Option.some.inj hsubst_at_ΔPx.symm
            -- When Dapp.fst = zftrue, Dimp.fst = Dsubst.fst (since imp with true antecedent
            -- reduces to consequent over booleans), which equals denT_x'.fst = P_val.
            have hbody_fst_eq_P_val : body_val.fst = P_val :=
              hbody_fst_eq_P_val_helper.{u} w (hcov_appD_upd w) (hcov_subst_upd w)
                hDapp_den hDapp_ty hDapp_true hDsubst_den hDsubst_ty hDimp
                hbody_eq_Dimp hDsubst_eq_denT hdenT_x'_fst_eq
            constructor
            · intro hbody_fst
              right
              intro Px τPx hPx hPx_den
              have hPx_den' := hPx_den
              rw [hP_den_x_raw] at hPx_den'
              have hinj := congrArg PSigma.fst (Option.some.inj hPx_den')
              dsimp at hinj
              rw [← hinj, ← hbody_fst_eq_P_val]
              exact hbody_fst
            · intro hor
              rcases hor with hx_B_not_𝒟 | hall
              · exact absurd hx_B_in_𝒟 hx_B_not_𝒟
              · have hPval_true : P_val = zftrue :=
                  hall P_val BType.bool hP_val_raw hP_den_x_raw
                rw [hbody_fst_eq_P_val]
                exact hPval_true
        classical
        show retract BType.bool forallVal.fst = T
        -- Apply retract_forallVal_eq_sInter_sep.
        -- Wrap hbridge to match the shape (expects 𝒟 not 𝒟').
        have hbridge_adapted :
            ∀ (x : ZFSet.{u}) (hx_mem : x ∈ ⟦τ.toSMTType⟧ᶻ),
            let x_B := retract τ x
            let hx_B_mem : x_B ∈ ⟦τ⟧ᶻ := retract_mem_of_canonical τ hx_mem
            let x_fin : Fin vs.length → B.Dom := fun i =>
              ⟨x_B.get vs.length i, ⟨τ.get vs.length i,
                get_mem_type_of_isTuple (hasArity_of_mem_toZFSet τ_hasArity hx_B_mem)
                  τ_hasArity hx_B_mem⟩⟩
            ∀ (w : Fin zs.length → SMT.Dom)
              (_hw : ∀ i, (w i).snd.fst = τs[i]'(zs_len ▸ i.isLt) ∧
                (w i).fst ∈ ⟦τs[i]'(zs_len ▸ i.isLt)⟧ᶻ)
              (_hw_smt : Fin.foldl (zs.length - 1)
                (fun acc i => acc.pair (w ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩).fst)
                (w ⟨0, zs_len_pos⟩).fst = x)
              (body_val : SMT.Dom),
              ⟦imp_body.abstract
                (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
                (hcov_imp_upd w)⟧ˢ = some body_val →
              (body_val.fst = zftrue ↔
                (x_B ∉ 𝒟 ∨
                 ∀ (Px : ZFSet.{u}) (P_ty : BType) (hP_val : Px ∈ ⟦P_ty⟧ᶻ),
                   ⟦(B.Term.abstract.go P vs «Δ» (fun v hv hvs => Δ_fv v
                     (B.fv.mem_all (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ =
                     some ⟨Px, ⟨P_ty, hP_val⟩⟩ → Px = zftrue)) := by
          intro x hx_mem
          -- Now introduce the let-bindings and then remaining args.
          simp only []
          intro wfn hw hw_smt body_val hbody_val
          have hb := hbridge x hx_mem wfn hw hw_smt body_val hbody_val
          -- Translate x_B ∉ 𝒟' ⇔ x_B ∉ 𝒟 via h𝒟_eq.
          rw [h𝒟_eq]
          exact hb
        apply retract_forallVal_eq_sInter_sep (vs := vs) vs_nemp vs_nodup
          (τ := τ) τ_hasArity
          (D := D) (D_enc := D_enc)
          (P_enc_subst := SMT.substList vs (List.map SMT.Term.var zs) P_enc)
          (zs := zs) (τs := τs) zs_nemp zs_len τs_toProdl_eq
          (imp_body := imp_body) imp_body_def zs_not_fv_D
          (Δ_ctx := Δ') Δ'_covers hforallVal
          (denD_val := denD')
          hcov_D_upd den_D_upd_eq denD'_type denD'_func
          (𝒟_val := 𝒟) h𝒟
          (h𝒟_eq ▸ 𝒟'_nonempty)
          denD'_retract
          hgo_cov hcov_imp_upd himp_total himp_ty
          (P := P) («Δ» := «Δ») Δ_fv
          (T_val := T)
          (hT_eq := ?_)
          (h_den_P := fun {x_fin} hx_typ hx_fin_in =>
            h_den_P_generic hx_typ (h𝒟_eq ▸ hx_fin_in : _))
          (h_den_P_bool := fun {x_fin} hx_typ hx_fin_in =>
            h_den_P_bool hx_typ (h𝒟_eq ▸ hx_fin_in : _))
          (zs_len_pos_hyp := zs_len_pos) (vs_zs_len := vs_zs_len)
          (hbridge := hbridge_adapted)
        -- Remaining goal: hT_eq
        · -- The T given by `rest_all` uses 𝒟' and a different pattern-match
          -- syntax for the inner `match`. Convert by congruence + rfl
          -- at the pattern-match variable rename.
          rw [h𝒟_eq]
          convert hT_eq_raw using 9
          -- Both sides project the first component of the PSigma inside the `some`.
          set opt := ⟦(B.Term.abstract.go P vs «Δ»
            (fun v hv hvs => Δ_fv v (B.fv.mem_all (.inr ⟨hv, hvs⟩)))).uncurry
            fun i => ⟨_, ⟨τ.get vs.length i, _⟩⟩⟧ᴮ with hopt
          match opt with
          | none => rfl
          | some ⟨Pv, ⟨Pty, hPv⟩⟩ => rfl
      -- Part 2: Totality clause (mirror of Part 1 at alternative Δ-contexts).
      -- Mirror template: see `EncodeTermCorrectCollect.lean`.
      · intro Δ_alt Δ_fv_alt Δ₀_alt hext_alt hnone_alt hwt_alt T_alt hT_alt hden_alt
        have hden_D_alt := hden_D_alt_helper.{u} (typ_D := typ_D) hden_alt
        obtain ⟨𝒟_alt, h𝒟_alt, hden_D_alt_eq⟩ := hden_D_alt
        set Δ₀_alt_D : SMT.RenamingContext.Context :=
          fun v => match B.RenamingContext.toSMTOnFV Δ_alt D v with
            | some d => some d
            | none => if v ∈ St₁.env.usedVars then
                match Δ₀_alt v with
                | some d => some d
                | none => Δ₀ v
              else none
        obtain ⟨hext_alt_D, hnone_alt_D⟩ :=
          hΔ₀_alt_D_setup_helper (D := D) (St₁_used := St₁.env.usedVars)
            covers_D (Δ_alt := Δ_alt) (Δ₀ := Δ₀) (Δ₀_alt := Δ₀_alt)
        have hwt_alt_D : ∀ v (d : SMT.Dom), Δ₀_alt_D v = some d →
            ∀ τ_v, St₁.types.lookup v = some τ_v → d.snd.fst = τ_v := by
          intro v d hv τ_v hτ_v
          change (match B.RenamingContext.toSMTOnFV Δ_alt D v with
            | some d => some d
            | none => if v ∈ St₁.env.usedVars then
                match Δ₀_alt v with
                | some d => some d
                | none => Δ₀ v
              else none) = some d at hv
          have hv_St₁ : v ∈ St₁.types := by
            rw [← AList.lookup_isSome, hτ_v]; rfl
          have hv_not_vs : v ∉ vs := fun hvs => vs_disj_St₁ v hvs hv_St₁
          have hv_St₄ : v ∈ St₄.types := AList.mem_of_subset St₁_sub_St₄_types hv_St₁
          have hv_not_zs : v ∉ zs := fun hvz => zs_not_types v hvz hv_St₄
          have hv_St₅_entry : ⟨v, τ_v⟩ ∈ St₅.types.entries :=
            AList.mem_lookup_iff.mp (AList.lookup_of_subset St₁_sub_St₅_types hτ_v)
          have hv_St₇_entry : ⟨v, τ_v⟩ ∈ St₇.types.entries := by
            rw [St₇_types]
            exact AList.mem_foldl_erase_of_not_mem_keys hv_St₅_entry hv_not_vs
          have hv_St₈_entry : ⟨v, τ_v⟩ ∈ St₈.types.entries := by
            rw [St₈_types]
            exact AList.mem_foldl_erase_of_not_mem_keys hv_St₇_entry hv_not_zs
          have hτ_v_St₈ : St₈.types.lookup v = some τ_v :=
            AList.mem_lookup_iff.2 hv_St₈_entry
          cases h_toSMT : B.RenamingContext.toSMTOnFV Δ_alt D v with
          | some d' =>
            simp only [h_toSMT] at hv; cases hv
            have hv_fv_D : v ∈ B.fv D := by
              by_contra hv_not
              simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_not] at h_toSMT
            have h_onFV : B.RenamingContext.toSMTOnFV Δ_alt (Term.all vs D P) v = some d := by
              simp only [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                B.RenamingContext.restrictToFV_eq_of_mem (B.fv.mem_all (.inl hv_fv_D))]
              simp only [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                B.RenamingContext.restrictToFV_eq_of_mem hv_fv_D] at h_toSMT
              exact h_toSMT
            have hΔ₀_alt_v : Δ₀_alt v = some d := hext_alt h_onFV
            exact hwt_alt v d hΔ₀_alt_v τ_v hτ_v_St₈
          | none =>
            simp only [h_toSMT] at hv
            split_ifs at hv with h_used
            · cases hΔ₀_alt : Δ₀_alt v with
              | some d' =>
                simp only [hΔ₀_alt, Option.some.injEq] at hv; subst hv
                exact hwt_alt v d' hΔ₀_alt τ_v hτ_v_St₈
              | none =>
                simp only [hΔ₀_alt] at hv
                exact Δ_D_wt v d (Δ_D_extends hv) τ_v hτ_v
        have hdom_alt_D : ∀ v, Δ₀_alt_D v ≠ none → v ∈ St₁.types := by
          intro v hv
          change (match B.RenamingContext.toSMTOnFV Δ_alt D v with
            | some d => some d
            | none => if v ∈ St₁.env.usedVars then
                match Δ₀_alt v with
                | some d => some d
                | none => Δ₀ v
              else none) ≠ none at hv
          cases h_toSMT : B.RenamingContext.toSMTOnFV Δ_alt D v with
          | some d =>
            have hv_fv : v ∈ B.fv D := by
              by_contra hv_not
              simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_not] at h_toSMT
            exact fv_sub_typings typ_D typ_D_enc v hv_fv
          | none =>
            simp only [h_toSMT] at hv
            split_ifs at hv with h_used
            · cases hΔ₀_alt : Δ₀_alt v with
              | some d' =>
                have hv_fv_all : v ∈ B.fv (Term.all vs D P) :=
                  SMT.RenamingContext.ExtendsOnSourceFV.dom_sub_B_fv
                    hext_alt v (by rw [hΔ₀_alt]; simp)
                exact fv_sub_typings typ_t typ_D_enc v hv_fv_all
              | none =>
                simp only [hΔ₀_alt] at hv
                have hv_fv_all : v ∈ B.fv (Term.all vs D P) :=
                  SMT.RenamingContext.ExtendsOnSourceFV.dom_sub_B_fv Δ₀_ext v hv
                exact fv_sub_typings typ_t typ_D_enc v hv_fv_all
            · exact absurd rfl hv
        obtain ⟨Δ_D_alt, hcov_D_alt, denD_alt, hext_D_alt, Δ_D_alt_none_out,
            Δ_D_alt_wt_out, hden_D_alt, hRDom_D_alt, Δ_D_alt_dom⟩ :=
          D_RDom.2
            (Δ_alt := Δ_alt)
            (fun v hv => Δ_fv_alt v (B.fv.mem_all (.inl hv)))
            (Δ₀_alt := Δ₀_alt_D) hext_alt_D hnone_alt_D
            hwt_alt_D
            𝒟_alt h𝒟_alt hden_D_alt_eq
        -- Δ'_alt: Δ_D_alt on fv(D_enc), Δ_P on fv(P_enc) \ vs, else Δ'.
        set Δ'_alt : SMT.RenamingContext.Context :=
          fun v => match Δ₀_alt v with
            | some d => some d
            | none => match Δ_D_alt v with
              | some d => some d
              | none => Δ' v
          with Δ'_alt_def
        have hext_Δ'_alt : RenamingContext.Extends Δ'_alt Δ₀_alt := by
          intro v d hv; simp only [Δ'_alt_def, hv]
        have Δ'_alt_none_out : ∀ v ∉ St₈.env.usedVars, Δ'_alt v = none := by
          intro v hv
          show (match Δ₀_alt v with
            | some d => some d
            | none => match Δ_D_alt v with
              | some d => some d
              | none => Δ' v) = none
          have h1 : Δ₀_alt v = none := hnone_alt v hv
          rw [h1]
          have hv_St₁ : v ∉ St₁.env.usedVars := fun hv_St₁' => hv (St₁_sub_St₈_used hv_St₁')
          have h2 : Δ_D_alt v = none := Δ_D_alt_none_out v hv_St₁
          rw [h2]
          exact Δ'_none_out v hv
        have hcov_forall_alt : SMT.RenamingContext.CoversFV Δ'_alt
            (Term.forall zs τs imp_body) := by
          intro v hv
          show (match Δ₀_alt v with
            | some d => some d
            | none => match Δ_D_alt v with
              | some d => some d
              | none => Δ' v).isSome = true
          cases h : Δ₀_alt v with
          | some d => simp
          | none =>
            cases h2 : Δ_D_alt v with
            | some d => simp
            | none =>
              simp only
              exact Δ'_covers v hv
        have Δ'_alt_wt : ∀ v (d : SMT.Dom), Δ'_alt v = some d →
            ∀ τ_v, St₈.types.lookup v = some τ_v → d.snd.fst = τ_v :=
          Δ'_alt_wt_helper (vs := vs) (zs := zs)
            St₁_sub_St₄_types St₁_sub_St₅_types St₄_sub_St₅_types
            St₇_types St₈_types vs_disj_St₁ zs_not_types
            (Δ' := Δ') (Δ_D := Δ_D) (Δ_P := Δ_P) (Δ_D_alt := Δ_D_alt)
            (Δ₀_alt := Δ₀_alt) Δ'_def Δ_D_dom Δ_D_alt_dom Δ_D_alt_wt_out
            Δ_P_dom Δ_P_wt hwt_alt
        have Δ'_alt_dom : ∀ v, Δ'_alt v ≠ none → v ∈ St₈.types :=
          Δ'_alt_dom_helper fv_sub_typings (vs := vs) (zs := zs)
            (D := D) (P := P) (τ := τ) typ_t (D_enc := D_enc) typ_D_enc
            St₁_sub_St₄_types St₁_sub_St₅_types St₄_sub_St₅_types
            St₇_types St₈_types vs_disj_St₁ zs_not_types
            (Δ' := Δ') (Δ_D := Δ_D) (Δ_P := Δ_P) (Δ_D_alt := Δ_D_alt)
            (Δ₀_alt := Δ₀_alt) Δ'_def Δ_D_dom Δ_D_alt_dom Δ_P_dom
            (Δ_alt := Δ_alt) hext_alt
        -- Build the forall denotation at Δ'_alt and the RDom proof, mirroring the
        -- primary branch (Phase 2/3/4). See `SMT/Reasoning/plan.md`.
        refine ⟨Δ'_alt, hcov_forall_alt, ?_⟩
        obtain ⟨denT_alt, hforallVal_alt, hRDom_alt⟩ : ∃ denT_alt,
            ⟦(Term.forall zs τs imp_body).abstract Δ'_alt hcov_forall_alt⟧ˢ =
              some denT_alt ∧ ⟨T_alt, ⟨BType.bool, hT_alt⟩⟩ ≘ᶻ denT_alt := by
          -- STEP 1: Derive denD_alt properties from hRDom_D_alt.
          have denD_alt_type : denD_alt.snd.fst = τ.toSMTType.fun .bool :=
            hRDom_D_alt.1
          have denD_alt_retract : retract τ.set denD_alt.fst = 𝒟_alt :=
            hRDom_D_alt.2
          have denD_alt_func : ⟦τ.toSMTType⟧ᶻ.IsFunc 𝔹 denD_alt.fst := by
            have : denD_alt.fst ∈ ⟦τ.toSMTType⟧ᶻ.funs 𝔹 := by
              simpa [denD_alt_type, SMTType.toZFSet] using denD_alt.snd.snd
            exact ZFSet.mem_funs.mp this
          -- STEP 2: Δ'_alt agrees with Δ_D_alt on fv(D_enc); lift D_enc denotation.
          have Δ'_alt_agrees_Δ_D_alt_on_D :
              SMT.RenamingContext.AgreesOnFV Δ_D_alt Δ'_alt D_enc :=
            Δ'_alt_agrees_Δ_D_alt_on_D_helper (vs := vs) (D := D) (P := P)
              (τ := τ) (St₁_types := St₁.types) (St₁_used := St₁.env.usedVars)
              typ_D_enc St₁_keys_sub
              (Δ' := Δ') (Δ_D_alt := Δ_D_alt) (Δ₀_alt := Δ₀_alt) (Δ₀ := Δ₀)
              (Δ_alt := Δ_alt) hext_alt hcov_D_alt hext_D_alt
          have hcov_D_Δ'_alt : SMT.RenamingContext.CoversFV Δ'_alt D_enc := by
            intro v hv
            rw [← Δ'_alt_agrees_Δ_D_alt_on_D hv]
            exact hcov_D_alt v hv
          have den_D_Δ'_alt : ⟦D_enc.abstract Δ'_alt hcov_D_Δ'_alt⟧ˢ = some denD_alt := by
            have heq := SMT.RenamingContext.denote_congr_of_agreesOnFV
              (h1 := hcov_D_alt) (h2 := hcov_D_Δ'_alt) Δ'_alt_agrees_Δ_D_alt_on_D
            unfold SMT.RenamingContext.denote at heq
            rw [← heq]; exact hden_D_alt
          have hcov_D_upd_alt :=
            hcov_D_upd_helper.{u} (zs := zs) zs_not_fv_D hcov_D_Δ'_alt
          have den_D_upd_eq_alt :=
            den_D_upd_eq_helper.{u} (zs := zs) zs_not_fv_D hcov_D_Δ'_alt den_D_Δ'_alt
          -- STEP 3: Build Phase 3a infrastructure at Δ'_alt.
          have hcov_imp_upd_alt :=
            hcov_imp_upd_helper.{u} zs_nodup (τs := τs) hcov_forall_alt
          have hgo_cov_alt := hgo_cov_helper (τs := τs) hcov_forall_alt
          have hpairl_cov_alt :=
            hpairl_cov_helper.{u} (Δ' := Δ'_alt) zs_nodup fv_pairl_sub_zs
          have hpairl_den_alt :=
            hpairl_den_helper.{u} (Δ' := Δ'_alt) zs_len zs_nodup zs_len_pos hpairl_cov_alt
          have hcov_appD_upd_alt :=
            hcov_appD_upd_helper.{u} hcov_D_upd_alt hpairl_cov_alt
          have hdenote_appD_upd_alt :=
            hdenote_appD_upd_helper.{u} (D_enc := D_enc) (Δ' := Δ'_alt) (denD' := denD_alt)
              (τ := τ) zs_len zs_len_pos τs_toProdl_eq denD_alt_type denD_alt_func
              hpairl_cov_alt hpairl_den_alt hcov_D_upd_alt den_D_upd_eq_alt hcov_appD_upd_alt
          -- Coverage of substList under zs-updates.
          have hcov_subst_upd_alt :=
            hcov_subst_upd_helper.{u} imp_body P_enc (vs := vs) zs_nodup (τs := τs)
              hcov_forall_alt
              (hv_to_imp := fun hv => by
                show _ ∈ SMT.fv (SMT.Term.imp _ _)
                exact SMT.fv.mem_imp (Or.inr hv))
          -- STEP 4: Extract h_den_P_alt_generic / h_den_P_alt_bool from hden_alt.
          have rest_alt := hden_alt
          simp only [B.Term.abstract] at rest_alt
          unfold B.denote at rest_alt
          simp only [Option.bind_eq_bind, hden_D_alt_eq, Option.bind_some] at rest_alt
          rw [dif_pos τ_hasArity] at rest_alt
          by_cases h_den_P_alt_cond : (∀ {x : Fin vs.length → B.Dom},
              (∀ i, (x i).snd.fst = τ.get vs.length i ∧
                    (x i).fst ∈ ⟦τ.get vs.length i⟧ᶻ) →
              ZFSet.ofFinDom x ∈ 𝒟_alt →
              ⟦(B.Term.abstract.go P vs Δ_alt
                (fun v hv hvs => Δ_fv_alt v
                  (B.fv.mem_all (.inr ⟨hv, hvs⟩)))).uncurry x⟧ᴮ.isSome)
          · have h_den_P_alt_generic : ∀ {x_fin : Fin vs.length → B.Dom},
                (∀ i, (x_fin i).snd.fst = τ.get vs.length i ∧
                      (x_fin i).fst ∈ ⟦τ.get vs.length i⟧ᶻ) →
                ZFSet.ofFinDom x_fin ∈ 𝒟_alt →
                ⟦(B.Term.abstract.go P vs Δ_alt
                  (fun v hv hvs => Δ_fv_alt v
                    (B.fv.mem_all (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ.isSome = true := by
              intro x_fin hx_typ hx_fin_in; exact h_den_P_alt_cond hx_typ hx_fin_in
            have h_den_P_alt_bool : ∀ {x_fin : Fin vs.length → B.Dom},
                (∀ i, (x_fin i).snd.fst = τ.get vs.length i ∧
                      (x_fin i).fst ∈ ⟦τ.get vs.length i⟧ᶻ) →
                ZFSet.ofFinDom x_fin ∈ 𝒟_alt →
                ∀ (Pz : ZFSet.{u}) (P_ty : BType) (hP_val : Pz ∈ ⟦P_ty⟧ᶻ),
                ⟦(B.Term.abstract.go P vs Δ_alt
                  (fun v hv hvs => Δ_fv_alt v
                    (B.fv.mem_all (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ =
                    some ⟨Pz, ⟨P_ty, hP_val⟩⟩ →
                P_ty = .bool :=
              h_den_P_alt_bool_helper.{u} (D := D) (τ := τ) (𝒟_alt := 𝒟_alt)
                vs_nodup vs_nemp typP (Δ_alt := Δ_alt) Δ_fv_alt
            -- STEP 5: hsubst_spec_alt (mirror of hsubst_spec at alt).
            -- Factored into `hsubst_spec_helper` reused with `Δ'_alt` substituted
            -- for `Δ'`. The two outside-vs hypotheses peel through the
            -- Δ₀_alt → Δ_D_alt → Δ' → Δ_P chain.
            have hsubst_spec_alt :=
              hsubst_spec_helper.{u}
                (vs := vs) (zs := zs) (τs := τs)
                (Δ' := Δ'_alt) (P_enc := P_enc) (St₄types := St₄.types)
                vs_nodup zs_nodup vs_zs_len vs_τs_len zs_len
                (Δ'_outside_vs_isSome := fun v hvvs hv => by
                  show (match Δ₀_alt v with
                    | some d => some d
                    | none => match Δ_D_alt v with
                      | some d => some d
                      | none => Δ' v).isSome = true
                  cases h_alt : Δ₀_alt v with
                  | some d => simp
                  | none =>
                    cases h_D_alt : Δ_D_alt v with
                    | some d => simp
                    | none =>
                      simp only [Option.isSome]
                      rw [Δ'_def]
                      simp only [hvvs, if_false]
                      exact Δ_P_covers v hv)
                (Δ'_outside_vs_wt := fun v hvvs d hd τ_v hlookup => by
                  -- Promote St₄ lookup to St₈ lookup (uses v ∉ vs and v ∉ zs).
                  have hv_St₄ : v ∈ St₄.types := AList.lookup_isSome.mp
                    (by rw [hlookup]; simp)
                  have hvzs : v ∉ zs := fun hvzs' => zs_not_types v hvzs' hv_St₄
                  have hv_St₅_entry : ⟨v, τ_v⟩ ∈ St₅.types.entries :=
                    AList.mem_lookup_iff.mp
                      (AList.lookup_of_subset St₄_sub_St₅_types hlookup)
                  have hv_St₇_entry : ⟨v, τ_v⟩ ∈ St₇.types.entries := by
                    rw [St₇_types]
                    exact AList.mem_foldl_erase_of_not_mem_keys hv_St₅_entry hvvs
                  have hv_St₈_entry : ⟨v, τ_v⟩ ∈ St₈.types.entries := by
                    rw [St₈_types]
                    exact AList.mem_foldl_erase_of_not_mem_keys hv_St₇_entry hvzs
                  have hτ_v_St₈ : St₈.types.lookup v = some τ_v :=
                    AList.mem_lookup_iff.2 hv_St₈_entry
                  exact Δ'_alt_wt v d hd τ_v hτ_v_St₈)
                (vs_sub_St₄_types :=
                  vs_sub_types_helper vs_nodup vs_τs_len St₃_types St₃_sub_St₄_types)
                (vs_typing_St₄ := fun i hi => by
                  have h_St₃_lookup : St₃.types.lookup vs[i] =
                      some (τs[i]'(vs_τs_len ▸ hi)) := by
                    rw [St₃_types]
                    exact foldl_insert_lookup_zip vs_nodup hi (vs_τs_len ▸ hi)
                  exact AList.lookup_of_subset St₃_sub_St₄_types h_St₃_lookup)
                (zs_not_bv_P :=
                  zs_not_bv_P_helper zs_len St₄_sub_St₅_types typ_P_enc zs_typing)
                (zs_not_St₄_types := zs_not_types)
                typ_P_enc hcov_subst_upd_alt
            -- STEP 6: himp_total_alt and himp_ty_alt (mirror of Phase 3c).
            obtain ⟨himp_total_alt, himp_ty_alt⟩ :=
              himp_total_ty_bundle.{u} zs_len imp_body_def hcov_imp_upd_alt
                (happD_bool := fun w hw => by
                  obtain ⟨_, Dapp, hDapp_ty, _, hDapp_den⟩ := hdenote_appD_upd_alt w hw
                  exact ⟨Dapp, hDapp_ty, hDapp_den⟩)
                hsubst_spec_alt
            -- STEP 7: forallVal_alt construction (Phase 3d mirror).
            have htot_forall_raw_alt :
                ∀ {x : Fin zs.length → SMT.Dom.{u}},
                (∀ i, (x i).snd.fst = τs[i.val]'(zs_len ▸ i.isLt) ∧
                  (x i).fst ∈ ⟦τs[i.val]'(zs_len ▸ i.isLt)⟧ᶻ) →
                ⟦(SMT.Term.abstract.go imp_body zs Δ'_alt hgo_cov_alt).uncurry
                    x⟧ˢ.isSome = true :=
              htot_forall_raw_helper.{u} (zs := zs) (τs := τs) zs_len
                (Δ_ctx := Δ'_alt) (hgo_cov := hgo_cov_alt) himp_total_alt
            have forallVal_alt_isSome :=
              forallVal_isSome_helper.{u} zs_len zs_len_pos
                hcov_forall_alt htot_forall_raw_alt
            obtain ⟨forallVal_alt, hforallVal_alt⟩ :=
              Option.isSome_iff_exists.mp forallVal_alt_isSome
            have hforallVal_alt_ty : forallVal_alt.snd.fst = .bool :=
              hforallVal_ty_helper.{u} zs_len zs_len_pos
                htot_forall_raw_alt hforallVal_alt
            -- STEP 8: hbridge_alt — the semantic bridge at Δ'_alt, mirror of the
            -- primary-branch `hbridge` (see Phase 4 Steps A-M above).
            have hbridge_alt :
                ∀ (x : ZFSet.{u}) (hx_mem : x ∈ ⟦τ.toSMTType⟧ᶻ),
                let x_B := retract τ x
                let hx_B_mem : x_B ∈ ⟦τ⟧ᶻ := retract_mem_of_canonical τ hx_mem
                let x_fin : Fin vs.length → B.Dom := fun i =>
                  ⟨x_B.get vs.length i, ⟨τ.get vs.length i,
                    get_mem_type_of_isTuple
                      (hasArity_of_mem_toZFSet τ_hasArity hx_B_mem)
                      τ_hasArity hx_B_mem⟩⟩
                ∀ (w : Fin zs.length → SMT.Dom)
                  (_hw : ∀ i, (w i).snd.fst = τs[i]'(zs_len ▸ i.isLt) ∧
                    (w i).fst ∈ ⟦τs[i]'(zs_len ▸ i.isLt)⟧ᶻ)
                  (_hw_smt : Fin.foldl (zs.length - 1)
                    (fun acc i =>
                      acc.pair (w ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩).fst)
                    (w ⟨0, zs_len_pos⟩).fst = x)
                  (body_val : SMT.Dom),
                  ⟦imp_body.abstract
                    (Function.updates Δ'_alt zs
                      (List.ofFn (fun i => some (w i))))
                    (hcov_imp_upd_alt w)⟧ˢ = some body_val →
                  (body_val.fst = zftrue ↔
                    (x_B ∉ 𝒟_alt ∨
                     ∀ (Px : ZFSet.{u}) (P_ty : BType)
                       (hP_val : Px ∈ ⟦P_ty⟧ᶻ),
                       ⟦(B.Term.abstract.go P vs Δ_alt (fun v hv hvs =>
                         Δ_fv_alt v
                           (B.fv.mem_all (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ =
                         some ⟨Px, ⟨P_ty, hP_val⟩⟩ → Px = zftrue)) := by
              intro x hx_mem
              -- Unfold let-bindings before introducing the remaining arguments.
              simp only []
              intro w hw hw_smt body_val hbody_val
              -- The B-level witness x_B and its B-domain decomposition.
              set x_B : ZFSet.{u} := retract τ x with x_B_def
              have hx_B_mem : x_B ∈ ⟦τ⟧ᶻ := retract_mem_of_canonical τ hx_mem
              obtain ⟨hx_mem_smt, Dapp, hDapp_ty, hDapp_val, hDapp_den⟩ :=
                hdenote_appD_upd_alt w hw
              obtain ⟨Dsubst, hDsubst_den, hDsubst_ty⟩ := hsubst_spec_alt w hw
              obtain ⟨Dimp, hDimp, hDimp_ty⟩ :=
                _root_.denote_imp_some_bool.{u} hDapp_den hDapp_ty hDsubst_den hDsubst_ty
              -- Reconcile imp_body denotation with denote_imp_some_bool's LHS.
              have hBody_eq_Dimp : ⟦imp_body.abstract
                  (Function.updates Δ'_alt zs (List.ofFn (fun i => some (w i))))
                  (hcov_imp_upd_alt w)⟧ˢ = some Dimp := by
                convert hDimp using 3
                all_goals
                  first
                  | rfl
                  | (simp only [imp_body_def, SMT.Term.abstract])
              have hbody_eq_Dimp : body_val = Dimp :=
                Option.some.inj (hbody_val.symm.trans hBody_eq_Dimp)
              have hDapp_mem_𝔹 : Dapp.fst ∈ 𝔹 := by
                have := Dapp.snd.snd; rwa [hDapp_ty] at this
              -- Dapp.fst = fapply denD_alt.fst x, via hDapp_val + hw_smt rewrite.
              have hDapp_val_x : Dapp.fst = @ᶻdenD_alt.fst ⟨x,
                  by rw [ZFSet.is_func_dom_eq denD_alt_func]; exact hx_mem⟩ := by
                rw [hDapp_val]
                have hsub : (⟨Fin.foldl (zs.length - 1)
                    (fun acc i => acc.pair (w ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩).fst)
                    (w ⟨0, zs_len_pos⟩).fst,
                    by rw [ZFSet.is_func_dom_eq denD_alt_func]; exact hx_mem_smt⟩
                    : {z // z ∈ denD_alt.fst.Dom}) =
                    ⟨x, by rw [ZFSet.is_func_dom_eq denD_alt_func]; exact hx_mem⟩ := by
                  apply Subtype.ext; exact hw_smt
                rw [hsub]
              have hRetr_denD_alt : retract (BType.set τ) denD_alt.fst = 𝒟_alt :=
                denD_alt_retract
              have hx_B_𝒟_iff : x_B ∈ 𝒟_alt ↔ Dapp.fst = zftrue := by
                rw [hDapp_val_x]
                have hcan : ZFSet.fapply (BType.canonicalIsoSMTType τ).1
                    (is_func_is_pfunc (BType.canonicalIsoSMTType τ).2.1)
                    ⟨x_B, ZFSet.mem_dom (is_func_is_pfunc
                      (BType.canonicalIsoSMTType τ).2.1)
                      (canonical_pair_of_retract τ hx_mem)⟩ = x :=
                  canonical_of_retract τ hx_mem
                have hsub_x : (⟨x,
                    by rw [ZFSet.is_func_dom_eq denD_alt_func]; exact hx_mem⟩
                    : {z // z ∈ denD_alt.fst.Dom}) =
                    ⟨ZFSet.fapply (BType.canonicalIsoSMTType τ).1
                      (is_func_is_pfunc (BType.canonicalIsoSMTType τ).2.1)
                      ⟨x_B, ZFSet.mem_dom (is_func_is_pfunc
                        (BType.canonicalIsoSMTType τ).2.1)
                        (canonical_pair_of_retract τ hx_mem)⟩,
                      by rw [ZFSet.is_func_dom_eq denD_alt_func]
                         exact fapply_mem_range _ _⟩ := by
                  apply Subtype.ext; exact hcan.symm
                rw [hsub_x]
                rw [← hRetr_denD_alt]
                rw [retract, mem_sep]
                constructor
                · rintro ⟨hx_B_α, hmem⟩
                  rw [dif_pos hx_B_α, dif_pos denD_alt_func] at hmem
                  simpa using hmem
                · intro hfapp
                  refine ⟨hx_B_mem, ?_⟩
                  rw [dif_pos hx_B_mem, dif_pos denD_alt_func]
                  simpa using hfapp
              rcases (ZFSet.ZFBool.mem_𝔹_iff _).mp hDapp_mem_𝔹 with hDapp_false | hDapp_true
              · -- ZFFALSE case: body_val.fst = zftrue (vacuously), x_B ∉ 𝒟_alt.
                have hDimp_eq : ⟦((@ˢD_enc) (List.map SMT.Term.var zs).toPairl
                    ⇒ˢ SMT.substList vs (List.map SMT.Term.var zs) P_enc).abstract
                    (Function.updates Δ'_alt zs (List.ofFn (fun i => some (w i))))
                    (by simpa [imp_body_def] using hcov_imp_upd_alt w)⟧ˢ =
                    some ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
                  have := denote_imp_eq_zftrue_of_zffalse_left.{u}
                    hDapp_den hDapp_ty hDapp_false hDsubst_den hDsubst_ty
                  convert this using 3
                  all_goals first | rfl | (simp only [SMT.Term.abstract])
                have hbody_is_true_dom : body_val = ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
                  have hDimp_eq' : ⟦imp_body.abstract
                      (Function.updates Δ'_alt zs (List.ofFn (fun i => some (w i))))
                      (hcov_imp_upd_alt w)⟧ˢ = some ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
                    convert hDimp_eq using 3
                  exact Option.some.inj (hbody_val.symm.trans hDimp_eq')
                have hbody_fst_true : body_val.fst = zftrue := by
                  rw [hbody_is_true_dom]
                have hx_B_not_𝒟 : x_B ∉ 𝒟_alt := by
                  intro hcon
                  have : Dapp.fst = zftrue := hx_B_𝒟_iff.mp hcon
                  rw [this] at hDapp_false
                  exact ZFSet.zftrue_ne_zffalse hDapp_false
                constructor
                · intro _; exact Or.inl hx_B_not_𝒟
                · intro _; exact hbody_fst_true
              · -- ZFTRUE CASE: x_B ∈ 𝒟_alt, so body_val.fst = Dsubst.fst = P_val.
                have hx_B_in_𝒟 : x_B ∈ 𝒟_alt := hx_B_𝒟_iff.mpr hDapp_true
                have hx_B_arity : x_B.hasArity vs.length :=
                  hasArity_of_mem_toZFSet τ_hasArity hx_B_mem
                have hx_arity : x.hasArity zs.length := by
                  rw [← vs_zs_len]
                  exact hasArity_of_mem_toSMTZFSet τ_hasArity hx_mem
                let x_fin : Fin vs.length → B.Dom := fun i =>
                  ⟨x_B.get vs.length i, τ.get vs.length i,
                    get_mem_type_of_isTuple hx_B_arity τ_hasArity hx_B_mem⟩
                set Δ_ext_x_alt : B.RenamingContext.Context :=
                  Function.updates Δ_alt vs (List.ofFn fun i => some (x_fin i))
                  with Δ_ext_x_alt_def
                have Δ_fv_P_x : ∀ v ∈ B.fv P, (Δ_ext_x_alt v).isSome = true := by
                  intro v hv
                  rw [Δ_ext_x_alt_def, Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup]
                  split_ifs with hvs
                  · simp [List.getElem_ofFn]
                  · exact Δ_fv_alt v (B.fv.mem_all (.inr ⟨hv, hvs⟩))
                have h_ofFinDom_eq_x : ZFSet.ofFinDom x_fin = x_B :=
                  ZFSet.ofFinDom_get (List.length_pos_iff.mpr vs_nemp)
                    (fun i => get_mem_type_of_isTuple hx_B_arity τ_hasArity hx_B_mem)
                    hx_B_arity τ_hasArity
                have hx_fin_in_𝒟 : ZFSet.ofFinDom x_fin ∈ 𝒟_alt := h_ofFinDom_eq_x ▸ hx_B_in_𝒟
                have hx_fin_typ : ∀ i, (x_fin i).snd.fst = τ.get vs.length i ∧
                    (x_fin i).fst ∈ ⟦τ.get vs.length i⟧ᶻ :=
                  fun i => ⟨rfl, (x_fin i).snd.snd⟩
                have hP_isSome_x := h_den_P_alt_generic hx_fin_typ hx_fin_in_𝒟
                obtain ⟨⟨P_val, P_ty_raw, hP_val_raw⟩, hP_den_x_raw⟩ :=
                  Option.isSome_iff_exists.mp hP_isSome_x
                have hP_ty_bool : P_ty_raw = BType.bool :=
                  h_den_P_alt_bool hx_fin_typ hx_fin_in_𝒟 P_val P_ty_raw hP_val_raw hP_den_x_raw
                subst hP_ty_bool
                have h_den_P_x : ⟦P.abstract Δ_ext_x_alt Δ_fv_P_x⟧ᴮ =
                    some ⟨P_val, ⟨BType.bool, hP_val_raw⟩⟩ := by
                  rw [← denote_term_abstract_go_eq_term_abstract vs_nodup vs_nemp x_fin Δ_fv_P_x]
                  exact hP_den_x_raw
                have hw_fst_eq : ∀ i : Fin zs.length, (w i).fst = x.get zs.length i := by
                  exact foldl_pair_inj_get zs_len_pos hx_arity (fun i => (w i).fst) hw_smt
                have hτs_i : ∀ (i : Fin zs.length),
                    τs[i.val]'(zs_len ▸ i.isLt) =
                      (τ.get vs.length ⟨i.val, by rw [vs_zs_len]; exact i.isLt⟩).toSMTType := by
                  intro i
                  have hvi_lt : i.val < vs.length := by rw [vs_zs_len]; exact i.isLt
                  have heq := toSMTType_get_eq_fromProdl_getElem τ_hasArity hvi_lt
                  rw [heq]
                  simp [τs_eq]
                set Δ_D_ext_x_alt : SMT.RenamingContext.Context :=
                  Function.updates Δ_D_alt vs
                    (List.ofFn fun (i : Fin vs.length) => B.RenamingContext.toSMT Δ_ext_x_alt vs[i])
                  with Δ_D_ext_x_alt_def
                -- Δ₀_hybrid_x_alt: at vs use Δ_D_ext_x_alt, elsewhere Δ'_alt when in
                -- used_St₄, else none.
                set Δ₀_hybrid_x_alt : SMT.RenamingContext.Context := fun v =>
                  if v ∈ vs then Δ_D_ext_x_alt v
                  else if v ∈ St₄.env.usedVars then Δ'_alt v
                  else none
                  with Δ₀_hybrid_x_alt_def
                have vs_sub_St₄_used : ∀ v ∈ vs, v ∈ St₄.env.usedVars := fun v hv =>
                  St₃_sub_St₄ (vs_sub_St₃_used v hv)
                have Δ₀_hybrid_ext_P_x :
                    RenamingContext.ExtendsOnSourceFV Δ₀_hybrid_x_alt Δ_ext_x_alt P := by
                  intro v d hv_eq
                  by_cases hv_fv : v ∈ B.fv P
                  · -- v ∈ fv P
                    have hv_smt : B.RenamingContext.toSMT Δ_ext_x_alt v = some d := by
                      have heq : B.RenamingContext.toSMTOnFV Δ_ext_x_alt P v =
                          B.RenamingContext.toSMT Δ_ext_x_alt v := by
                        simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                          B.RenamingContext.restrictToFV_eq_of_mem hv_fv]
                      rwa [← heq]
                    by_cases hvs : v ∈ vs
                    · -- v ∈ vs: Δ₀_hybrid_x_alt v = Δ_D_ext_x_alt v = toSMT Δ_ext_x_alt v.
                      show (if v ∈ vs then Δ_D_ext_x_alt v else _) = some d
                      rw [if_pos hvs]
                      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hvs
                      rw [Δ_D_ext_x_alt_def]
                      rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup,
                          dif_pos (List.getElem_mem hi)]
                      simp only [List.getElem_ofFn, Fin.getElem_fin, List.getElem_idxOf]
                      exact hv_smt
                    · -- v ∉ vs: Δ₀_hybrid_x_alt v = Δ'_alt v (since v ∈ St₄.env.usedVars).
                      have hv_St₄_used : v ∈ St₄.env.usedVars := covers_P v hv_fv
                      show (if v ∈ vs then _ else if v ∈ St₄.env.usedVars then Δ'_alt v else none) = some d
                      rw [if_neg hvs, if_pos hv_St₄_used]
                      -- Δ'_alt = Δ₀_alt ⊕ Δ_D_alt ⊕ Δ'; at v ∉ vs, Δ_ext_x_alt v = Δ_alt v.
                      have hΔ_ext_x_alt_eq : Δ_ext_x_alt v = Δ_alt v := by
                        rw [Δ_ext_x_alt_def]
                        exact Function.updates_of_not_mem Δ_alt vs _ v hvs
                      have hv_smt_Δ_alt : B.RenamingContext.toSMT Δ_alt v = some d := by
                        rw [B.RenamingContext.toSMT, ← hΔ_ext_x_alt_eq,
                            ← B.RenamingContext.toSMT]
                        exact hv_smt
                      -- v ∈ fv P ⊆ fv (all vs D P), so hext_alt applies.
                      have hv_fv_all : v ∈ B.fv (Term.all vs D P) :=
                        B.fv.mem_all (.inr ⟨hv_fv, hvs⟩)
                      have h_onFV_all : B.RenamingContext.toSMTOnFV Δ_alt
                          (Term.all vs D P) v = some d := by
                        simp only [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                          B.RenamingContext.restrictToFV_eq_of_mem hv_fv_all]
                        rw [B.RenamingContext.toSMT, Option.pure_def,
                          Option.bind_eq_bind] at hv_smt_Δ_alt
                        exact hv_smt_Δ_alt
                      have hΔ₀_alt_v : Δ₀_alt v = some d := hext_alt h_onFV_all
                      -- Δ'_alt unfolds via Δ₀_alt.
                      show Δ'_alt v = some d
                      rw [Δ'_alt_def]
                      simp only [hΔ₀_alt_v]
                  · -- v ∉ fv P
                    have : B.RenamingContext.toSMTOnFV Δ_ext_x_alt P v = none := by
                      simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                        B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_fv]
                    rw [this] at hv_eq
                    exact absurd hv_eq (by simp)
                have Δ₀_hybrid_x_alt_none : ∀ v ∉ St₄.env.usedVars, Δ₀_hybrid_x_alt v = none := by
                  intro v hv
                  show (if v ∈ vs then Δ_D_ext_x_alt v else _) = none
                  have hv_not_vs : v ∉ vs := fun hvs => hv (vs_sub_St₄_used v hvs)
                  rw [if_neg hv_not_vs, if_neg hv]
                have Δ₀_hybrid_x_alt_wt :
                    ∀ (v : SMT.𝒱) (d : SMT.Dom), Δ₀_hybrid_x_alt v = some d →
                    ∀ τ_v, St₄.types.lookup v = some τ_v → d.snd.fst = τ_v := by
                  intro v d hv τ_v hlookup
                  by_cases hvs : v ∈ vs
                  · -- v ∈ vs: d = toSMT Δ_ext_x_alt v.
                    have hv_hybrid : Δ₀_hybrid_x_alt v = Δ_D_ext_x_alt v := by
                      show (if v ∈ vs then Δ_D_ext_x_alt v else _) = Δ_D_ext_x_alt v
                      rw [if_pos hvs]
                    rw [hv_hybrid] at hv
                    obtain ⟨i, hi, hvi_eq⟩ := List.mem_iff_getElem.mp hvs
                    subst hvi_eq
                    rw [Δ_D_ext_x_alt_def, Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup,
                      dif_pos (List.getElem_mem hi)] at hv
                    simp only [List.getElem_ofFn, Fin.getElem_fin, List.getElem_idxOf] at hv
                    -- hv : toSMT Δ_ext_x_alt vs[i] = some d
                    have hΔ_ext_x_alt_vi : Δ_ext_x_alt vs[i] = some (x_fin ⟨i, hi⟩) := by
                      show Function.updates Δ_alt vs _ vs[i] = _
                      rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup,
                        dif_pos (List.getElem_mem hi)]
                      simp only [List.getElem_ofFn]
                      simp [List.idxOf_getElem vs_nodup]
                    have vs_typing_St₃ : St₃.types.lookup vs[i] = some (τs[i]'(vs_τs_len ▸ hi)) := by
                      rw [St₃_types]
                      exact foldl_insert_lookup_zip vs_nodup hi (vs_τs_len ▸ hi)
                    have vs_typing_St₄ : St₄.types.lookup vs[i] = some (τs[i]'(vs_τs_len ▸ hi)) :=
                      AList.lookup_of_subset St₃_sub_St₄_types vs_typing_St₃
                    rw [vs_typing_St₄] at hlookup
                    cases hlookup
                    simp only [B.RenamingContext.toSMT, hΔ_ext_x_alt_vi, Option.pure_def,
                      Option.bind_eq_bind, Option.bind_some] at hv
                    have hd_eq := Option.some.inj hv
                    rw [← hd_eq]
                    show (τ.get vs.length ⟨i, hi⟩).toSMTType = τs[i]
                    have := hτs_i ⟨i, zs_len ▸ vs_τs_len ▸ hi⟩
                    simp only at this
                    exact this.symm
                  · -- v ∉ vs: Δ₀_hybrid_x_alt v = Δ'_alt v.
                    have hv_St₄ : v ∈ St₄.types := AList.lookup_isSome.mp (by rw [hlookup]; simp)
                    have hv_St₄_used : v ∈ St₄.env.usedVars := St₄_keys_sub hv_St₄
                    have hv_hybrid : Δ₀_hybrid_x_alt v = Δ'_alt v := by
                      show (if v ∈ vs then _ else if v ∈ St₄.env.usedVars then Δ'_alt v else none) = Δ'_alt v
                      rw [if_neg hvs, if_pos hv_St₄_used]
                    rw [hv_hybrid] at hv
                    -- Use Δ'_alt_wt with St₈ lookup promoted from St₄.
                    have hv_not_zs : v ∉ zs := fun hvz => zs_not_types v hvz hv_St₄
                    have hv_St₅_entry : ⟨v, τ_v⟩ ∈ St₅.types.entries :=
                      AList.mem_lookup_iff.mp (AList.lookup_of_subset St₄_sub_St₅_types hlookup)
                    have hv_St₇_entry : ⟨v, τ_v⟩ ∈ St₇.types.entries := by
                      rw [St₇_types]
                      exact AList.mem_foldl_erase_of_not_mem_keys hv_St₅_entry hvs
                    have hv_St₈_entry : ⟨v, τ_v⟩ ∈ St₈.types.entries := by
                      rw [St₈_types]
                      exact AList.mem_foldl_erase_of_not_mem_keys hv_St₇_entry hv_not_zs
                    have hτ_v_St₈ : St₈.types.lookup v = some τ_v :=
                      AList.mem_lookup_iff.2 hv_St₈_entry
                    exact Δ'_alt_wt v d hv τ_v hτ_v_St₈
                obtain ⟨Δ_P_x, hcov_Px, denT_x', Δ_P_x_extends, Δ_P_x_none, Δ_P_x_wt,
                    hden_Px, hRDom_x, Δ_P_x_dom⟩ :=
                  P_enc_total Δ_ext_x_alt Δ_fv_P_x Δ₀_hybrid_x_alt Δ₀_hybrid_ext_P_x
                    Δ₀_hybrid_x_alt_none Δ₀_hybrid_x_alt_wt P_val hP_val_raw h_den_P_x
                have hdenT_x'_ty : denT_x'.snd.fst = BType.bool.toSMTType := hRDom_x.1
                have hdenT_x'_fst_eq : denT_x'.fst = P_val := by
                  have := hRDom_x.2
                  simp only [retract] at this
                  exact this
                set Δ'_upd : SMT.RenamingContext.Context :=
                  Function.updates Δ'_alt zs (List.ofFn (fun i : Fin zs.length => some (w i)))
                  with Δ'_upd_def
                set Δ_P_x_upd : SMT.RenamingContext.Context :=
                  Function.updates Δ_P_x zs (List.ofFn (fun i : Fin zs.length => some (w i)))
                  with Δ_P_x_upd_def
                have hΔ_upd_agree_substList :
                    SMT.RenamingContext.AgreesOnFV Δ'_upd Δ_P_x_upd
                      (SMT.substList vs (List.map SMT.Term.var zs) P_enc) := by
                  intro v hv
                  by_cases hvzs : v ∈ zs
                  · rw [Δ'_upd_def, Δ_P_x_upd_def]
                    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hvzs
                    rw [Function.updates_eq_if (by rw [List.length_ofFn]) zs_nodup,
                      dif_pos (List.getElem_mem hj)]
                    rw [Function.updates_eq_if (by rw [List.length_ofFn]) zs_nodup,
                      dif_pos (List.getElem_mem hj)]
                  · rw [Δ'_upd_def, Δ_P_x_upd_def]
                    rw [Function.updates_of_not_mem Δ'_alt zs _ v hvzs,
                      Function.updates_of_not_mem Δ_P_x zs _ v hvzs]
                    rcases SMT_mem_fv_substList hv with hv_P | ⟨t, ht, hv_t⟩
                    · have hv_St₄ : v ∈ St₄.types :=
                        SMT.Typing.mem_context_of_mem_fv typ_P_enc hv_P
                      have hv_St₄_used : v ∈ St₄.env.usedVars := St₄_keys_sub hv_St₄
                      by_cases hvvs : v ∈ vs
                      · exfalso
                        have hlen : vs.length ≤ (List.map SMT.Term.var zs).length := by
                          rw [List.length_map]; exact le_of_eq (zs_len ▸ vs_τs_len)
                        by_cases h_all_no_fv :
                            ∀ t ∈ List.map SMT.Term.var zs, v ∉ SMT.fv t
                        · exact SMT_not_mem_fv_substList_of_mem_vars hlen hvvs h_all_no_fv hv
                        · push_neg at h_all_no_fv
                          obtain ⟨t, ht, hv_t⟩ := h_all_no_fv
                          rw [List.mem_map] at ht
                          obtain ⟨z, hz, rfl⟩ := ht
                          simp only [SMT.fv, List.mem_singleton] at hv_t
                          subst hv_t
                          exact hvzs hz
                      · -- v ∈ fv(P_enc), v ∉ vs, v ∉ zs. Show Δ_P_x v = Δ'_alt v.
                        -- Δ₀_hybrid_x_alt v = Δ'_alt v at v ∉ vs and v ∈ St₄.env.usedVars.
                        -- Δ'_alt v must be some (via hcov_forall_alt, since v ∈ fv(imp_body) \ zs).
                        have hv_imp : v ∈ SMT.fv imp_body := by
                          show v ∈ SMT.fv (SMT.Term.imp _ _)
                          exact SMT.fv.mem_imp (Or.inr hv)
                        have hv_f : v ∈ SMT.fv (SMT.Term.forall zs τs imp_body) := by
                          simp only [SMT.fv, List.mem_removeAll_iff]
                          exact ⟨hv_imp, hvzs⟩
                        have hΔ'alt_isSome : (Δ'_alt v).isSome = true :=
                          hcov_forall_alt v hv_f
                        obtain ⟨d, hΔ'alt_v⟩ := Option.isSome_iff_exists.mp hΔ'alt_isSome
                        have hΔ₀_hyb_v : Δ₀_hybrid_x_alt v = some d := by
                          show (if v ∈ vs then _ else if v ∈ St₄.env.usedVars then Δ'_alt v else none) = some d
                          rw [if_neg hvvs, if_pos hv_St₄_used]
                          exact hΔ'alt_v
                        have hΔ_P_x_v : Δ_P_x v = Δ'_alt v := by
                          rw [Δ_P_x_extends hΔ₀_hyb_v, hΔ'alt_v]
                        rw [hΔ_P_x_v]
                    · rw [List.mem_map] at ht
                      obtain ⟨z, hz, rfl⟩ := ht
                      simp only [SMT.fv, List.mem_singleton] at hv_t
                      subst hv_t
                      exact absurd hz hvzs
                have hcov_substList_Px_upd : SMT.RenamingContext.CoversFV
                    Δ_P_x_upd (SMT.substList vs (List.map SMT.Term.var zs) P_enc) := by
                  intro v hv
                  have hag := hΔ_upd_agree_substList hv
                  have hcov_v := hcov_subst_upd_alt w v hv
                  show (Δ_P_x_upd v).isSome = true
                  rw [show Δ'_upd = Function.updates Δ'_alt zs
                    (List.ofFn (fun i : Fin zs.length => some (w i))) from rfl] at hag
                  rw [← hag]; exact hcov_v
                have hsubst_at_ΔPx : ⟦(SMT.substList vs (List.map SMT.Term.var zs) P_enc).abstract
                    Δ_P_x_upd hcov_substList_Px_upd⟧ˢ = some Dsubst := by
                  have h_transfer := SMT.RenamingContext.denote_congr_of_agreesOnFV
                    (h1 := hcov_subst_upd_alt w) (h2 := hcov_substList_Px_upd) hΔ_upd_agree_substList
                  unfold SMT.RenamingContext.denote at h_transfer
                  rw [← h_transfer]; exact hDsubst_den
                let Ds_x : List SMT.Dom := List.ofFn fun i : Fin vs.length =>
                  w ⟨i.val, by rw [← vs_zs_len]; exact i.isLt⟩
                have hlen_xt_x : vs.length = (List.map SMT.Term.var zs).length := by
                  rw [List.length_map]; exact vs_zs_len
                have hlen_xd_x : vs.length = Ds_x.length := by simp [Ds_x]
                have vs_not_bv_P : ∀ x_v ∈ vs, x_v ∉ SMT.bv P_enc := fun x_v hx_v hbv =>
                  SMT.Typing.bv_notMem_context typ_P_enc x_v hbv
                    (AList.mem_of_subset St₃_sub_St₄_types
                      (by
                        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx_v
                        rw [St₃_types]
                        exact AList.lookup_isSome.mp
                          (by rw [foldl_insert_lookup_zip vs_nodup hi (vs_τs_len ▸ hi)]; simp)))
                have hts_bv_nil_x : ∀ t ∈ List.map SMT.Term.var zs, SMT.bv t = [] := by
                  intro t ht
                  rw [List.mem_map] at ht; obtain ⟨z, _, rfl⟩ := ht; unfold SMT.bv; rfl
                have hts_fv_not_bv_x : ∀ t ∈ List.map SMT.Term.var zs,
                    ∀ w' ∈ SMT.fv t, w' ∉ SMT.bv P_enc := by
                  intro t ht v' hv'
                  rw [List.mem_map] at ht
                  obtain ⟨z', hz', rfl⟩ := ht
                  simp only [SMT.fv, List.mem_singleton] at hv'
                  subst hv'
                  intro hbv
                  have typ_P_enc_St₅ : St₅.types ⊢ˢ P_enc : .bool :=
                    SMT.Typing.weakening St₄_sub_St₅_types typ_P_enc
                  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz'
                  have hz_St₅ : zs[i] ∈ St₅.types :=
                    AList.lookup_isSome.mp (by rw [zs_typing i hi]; simp)
                  exact SMT.Typing.bv_notMem_context typ_P_enc_St₅ zs[i] hbv hz_St₅
                have hts_not_none_x : ∀ t ∈ List.map SMT.Term.var zs, t ≠ SMT.Term.none := by
                  intro t ht; rw [List.mem_map] at ht; obtain ⟨z, _, rfl⟩ := ht; intro h; cases h
                have hts_fv_disj_xs_x : ∀ t ∈ List.map SMT.Term.var zs,
                    ∀ v' ∈ SMT.fv t, v' ∉ vs := by
                  intro t ht v' hv' hvs
                  rw [List.mem_map] at ht
                  obtain ⟨z, hz, rfl⟩ := ht
                  simp only [SMT.fv, List.mem_singleton] at hv'
                  subst hv'
                  have hv_St₃ : v' ∈ St₃.types := by
                    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hvs
                    rw [St₃_types]
                    exact AList.lookup_isSome.mp <| by
                      rw [foldl_insert_lookup_zip vs_nodup hi (vs_τs_len ▸ hi)]; simp
                  have hv_St₄ : v' ∈ St₄.types := AList.mem_of_subset St₃_sub_St₄_types hv_St₃
                  exact zs_not_types v' hz hv_St₄
                have h_cov_upd_x : SMT.RenamingContext.CoversFV
                    (Function.updates Δ_P_x_upd vs (Ds_x.map Option.some)) P_enc := by
                  intro v hv
                  by_cases hvs : v ∈ vs
                  · rw [Function.updates_eq_if (by rw [List.length_map, List.length_ofFn]) vs_nodup,
                      dif_pos hvs]
                    simp
                  · rw [Function.updates_of_not_mem _ vs _ _ hvs]
                    by_cases hvzs : v ∈ zs
                    · rw [Δ_P_x_upd_def, Function.updates_eq_if (by rw [List.length_ofFn]) zs_nodup,
                        dif_pos hvzs]
                      simp
                    · rw [Δ_P_x_upd_def, Function.updates_of_not_mem _ zs _ _ hvzs]
                      exact hcov_Px v hv
                have h_eq_x := SMT.RenamingContext.abstract_substList_denote P_enc vs
                  (List.map SMT.Term.var zs) Ds_x hlen_xt_x hlen_xd_x vs_nodup
                  vs_not_bv_P hts_bv_nil_x hts_fv_not_bv_x hts_not_none_x hts_fv_disj_xs_x
                  (by
                    intro i hi_x hi_t hi_d
                    have hi_zs : i < zs.length := by rw [List.length_map] at hi_t; exact hi_t
                    rw [List.getElem_map]
                    have hlookup_zs : Δ_P_x_upd zs[i] = some (w ⟨i, hi_zs⟩) := by
                      rw [Δ_P_x_upd_def]
                      rw [Function.updates_eq_if (by rw [List.length_ofFn]) zs_nodup,
                        dif_pos (List.getElem_mem hi_zs)]
                      have hidx : zs.idxOf zs[i] = i := List.idxOf_getElem zs_nodup i hi_zs
                      simp only [List.getElem_ofFn]
                      refine congrArg some (congrArg w ?_)
                      apply Fin.ext
                      exact hidx
                    have hcov_ti : SMT.RenamingContext.CoversFV Δ_P_x_upd
                        (SMT.Term.var zs[i]) := by
                      intro v hv
                      simp only [SMT.fv, List.mem_singleton] at hv
                      subst hv
                      rw [hlookup_zs]; simp
                    refine ⟨hcov_ti, ?_⟩
                    have hDs_i : Ds_x[i] = w ⟨i, by rw [← vs_zs_len]; exact hi_x⟩ := by
                      show (List.ofFn _)[i] = _
                      rw [List.getElem_ofFn]
                    show SMT.denote ((SMT.Term.var zs[i]).abstract Δ_P_x_upd hcov_ti) = some Ds_x[i]
                    rw [SMT.Term.abstract]
                    show SMT.denote (PHOAS.Term.var ((Δ_P_x_upd zs[i]).get _)) = _
                    simp only [SMT.denote]
                    rw [hDs_i]
                    congr 1
                    have h_get_eq : (Δ_P_x_upd zs[i]).get (by rw [hlookup_zs]; simp) =
                        w ⟨i, hi_zs⟩ := Option.get_of_eq_some _ hlookup_zs
                    show (Δ_P_x_upd zs[i]).get _ = w ⟨i, _⟩
                    rw [show (Δ_P_x_upd zs[i]).get _ = w ⟨i, hi_zs⟩ from h_get_eq])
                  hcov_substList_Px_upd h_cov_upd_x
                have h_upd_agree_x : SMT.RenamingContext.AgreesOnFV
                    (Function.updates Δ_P_x_upd vs (Ds_x.map Option.some)) Δ_P_x P_enc := by
                  intro v hv
                  by_cases hvs : v ∈ vs
                  · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hvs
                    rw [Function.updates_eq_if
                      (by rw [List.length_map, List.length_ofFn]) vs_nodup,
                      dif_pos (List.getElem_mem hi)]
                    simp only [List.getElem_map, List.idxOf_getElem vs_nodup]
                    have hvi_mem : vs[i] ∈ vs := List.getElem_mem hi
                    have hΔ_ext_x_alt_vi : Δ_ext_x_alt vs[i] = some (x_fin ⟨i, hi⟩) := by
                      show Function.updates Δ_alt vs _ vs[i] = _
                      rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup,
                        dif_pos hvi_mem]
                      simp only [List.getElem_ofFn]
                      simp [List.idxOf_getElem vs_nodup]
                    set d_smt : SMT.Dom :=
                      ⟨ZFSet.fapply (BType.canonicalIsoSMTType (τ.get vs.length ⟨i, hi⟩)).1
                        (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType _).2.1)
                        ⟨(x_fin ⟨i, hi⟩).fst, by
                          rw [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType _).2.1]
                          exact (x_fin ⟨i, hi⟩).snd.snd⟩,
                       (τ.get vs.length ⟨i, hi⟩).toSMTType, ZFSet.fapply_mem_range _ _⟩
                      with d_smt_def
                    have htoSMT_vi : B.RenamingContext.toSMT Δ_ext_x_alt vs[i] = some d_smt := by
                      simp only [B.RenamingContext.toSMT, hΔ_ext_x_alt_vi, Option.pure_def,
                        Option.bind_eq_bind, Option.bind_some]
                      rfl
                    have hΔ_D_ext_x_alt_vi : Δ_D_ext_x_alt vs[i] = some d_smt := by
                      rw [Δ_D_ext_x_alt_def, Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup,
                        dif_pos hvi_mem]
                      simp only [List.getElem_ofFn, Fin.getElem_fin, List.getElem_idxOf]
                      exact htoSMT_vi
                    have hΔ₀_hybrid_vi : Δ₀_hybrid_x_alt vs[i] = some d_smt := by
                      show (if vs[i] ∈ vs then Δ_D_ext_x_alt vs[i] else _) = some d_smt
                      rw [if_pos hvi_mem]; exact hΔ_D_ext_x_alt_vi
                    have hΔ_P_x_vi : Δ_P_x vs[i] = some d_smt := Δ_P_x_extends hΔ₀_hybrid_vi
                    set i_zs : Fin zs.length := ⟨i, by rw [← vs_zs_len]; exact hi⟩
                    have hDs_i : Ds_x[i] = w i_zs := by
                      show (List.ofFn _)[i] = _
                      rw [List.getElem_ofFn]
                    rw [hDs_i, hΔ_P_x_vi]
                    congr 1
                    have hw_i_fst : (w i_zs).fst = x.get zs.length i_zs := hw_fst_eq i_zs
                    have hw_i_ty : (w i_zs).snd.fst = τs[i]'(zs_len ▸ i_zs.isLt) := (hw i_zs).1
                    have hw_i_mem : (w i_zs).fst ∈ ⟦τs[i]'(zs_len ▸ i_zs.isLt)⟧ᶻ := (hw i_zs).2
                    have hτs_match : τs[i]'(zs_len ▸ i_zs.isLt) =
                        (τ.get vs.length ⟨i, hi⟩).toSMTType := by
                      have hτs_z := hτs_i i_zs
                      exact hτs_z
                    have hd_smt_fst_eq :
                        d_smt.fst = ZFSet.fapply (BType.canonicalIsoSMTType (τ.get vs.length ⟨i, hi⟩)).1
                          (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType _).2.1)
                          ⟨x_B.get vs.length ⟨i, hi⟩, by
                            rw [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType _).2.1]
                            exact get_mem_type_of_isTuple hx_B_arity τ_hasArity hx_B_mem⟩ := by
                      rfl
                    have h_canonical_eq :
                        (ZFSet.fapply (BType.canonicalIsoSMTType (τ.get vs.length ⟨i, hi⟩)).1
                          (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType _).2.1)
                          ⟨x_B.get vs.length ⟨i, hi⟩, by
                            rw [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType _).2.1]
                            exact get_mem_type_of_isTuple hx_B_arity τ_hasArity hx_B_mem⟩).val =
                        x.get zs.length i_zs := by
                      set vi_fin : Fin vs.length := ⟨i, hi⟩
                      have h_Fin_cast : (Fin.cast vs_zs_len vi_fin) = i_zs := rfl
                      have hx_B_get : x_B.get vs.length vi_fin = (retract τ x).get vs.length vi_fin := by
                        rw [x_B_def]
                      have h_retract_comm : (retract τ x).get vs.length vi_fin =
                          retract (τ.get vs.length vi_fin) (x.get vs.length vi_fin) :=
                        retract_get_comm
                          (hasArity_of_mem_toSMTZFSet τ_hasArity hx_mem) τ_hasArity hx_mem
                      have hx_get_mem_v : x.get vs.length vi_fin ∈
                          ⟦(τ.get vs.length vi_fin).toSMTType⟧ᶻ :=
                        get_mem_toSMTZFSet
                          (hasArity_of_mem_toSMTZFSet τ_hasArity hx_mem)
                          τ_hasArity hx_mem
                      have hx_get_eq : x.get vs.length vi_fin = x.get zs.length i_zs := by
                        have : ∀ {n m : ℕ} (h : n = m) (hi₁ : i < n) (hi₂ : i < m),
                            x.get n ⟨i, hi₁⟩ = x.get m ⟨i, hi₂⟩ := by
                          intro n m h hi₁ hi₂; subst h; rfl
                        exact this vs_zs_len hi i_zs.isLt
                      have h_x_B_eq : x_B.get vs.length vi_fin =
                          retract (τ.get vs.length vi_fin) (x.get vs.length vi_fin) :=
                        hx_B_get.trans h_retract_comm
                      have h_xB_as_retract : x_B.get vs.length vi_fin =
                          retract (τ.get vs.length vi_fin) (x.get zs.length i_zs) := by
                        rw [hx_B_get, h_retract_comm, hx_get_eq]
                      have hx_get_zs_mem : x.get zs.length i_zs ∈
                          ⟦(τ.get vs.length vi_fin).toSMTType⟧ᶻ := hx_get_eq ▸ hx_get_mem_v
                      have hx_pair_mem :
                          ZFSet.pair (x_B.get vs.length vi_fin) (x.get zs.length i_zs) ∈
                          (BType.canonicalIsoSMTType (τ.get vs.length vi_fin)).1 := by
                        rw [h_xB_as_retract]
                        exact canonical_pair_of_retract _ hx_get_zs_mem
                      exact Subtype.ext_iff.mp <|
                        ZFSet.fapply.of_pair
                          (is_func_is_pfunc (BType.canonicalIsoSMTType _).2.1)
                          hx_pair_mem
                    have hd_smt_fst_eq_w : d_smt.fst = (w i_zs).fst := by
                      rw [hd_smt_fst_eq, h_canonical_eq, hw_i_fst]
                    have hd_smt_ty : d_smt.snd.fst = τs[i]'(zs_len ▸ i_zs.isLt) := by
                      rw [d_smt_def]
                      show (τ.get vs.length ⟨i, hi⟩).toSMTType = _
                      exact hτs_match.symm
                    apply SMT.RenamingContext.Dom_ext'
                    · exact hw_i_fst.trans (h_canonical_eq.symm.trans hd_smt_fst_eq.symm)
                    · exact hw_i_ty.trans hd_smt_ty.symm
                  · rw [Function.updates_of_not_mem _ vs _ _ hvs]
                    by_cases hvzs : v ∈ zs
                    · exfalso
                      have hv_St₄ : v ∈ St₄.types :=
                        SMT.Typing.mem_context_of_mem_fv typ_P_enc hv
                      exact zs_not_types v hvzs hv_St₄
                    · rw [Δ_P_x_upd_def, Function.updates_of_not_mem _ zs _ _ hvzs]
                have h_eq2_x := SMT.RenamingContext.denote_congr_of_agreesOnFV
                  (h1 := h_cov_upd_x) (h2 := hcov_Px) h_upd_agree_x
                unfold SMT.RenamingContext.denote at h_eq2_x
                rw [h_eq_x, h_eq2_x, hden_Px] at hsubst_at_ΔPx
                have hDsubst_eq_denT : Dsubst = denT_x' :=
                  Option.some.inj hsubst_at_ΔPx.symm
                have hbody_fst_eq_P_val : body_val.fst = P_val := by
                  rw [hbody_eq_Dimp]
                  have hDsubst_mem_𝔹 : Dsubst.fst ∈ 𝔹 := by
                    have := Dsubst.snd.snd; rwa [hDsubst_ty] at this
                  rcases (ZFSet.ZFBool.mem_𝔹_iff _).mp hDsubst_mem_𝔹 with hDsubst_false | hDsubst_true
                  · have hDsubst_fst_eq : Dsubst.fst = denT_x'.fst := by rw [hDsubst_eq_denT]
                    have hDenT_fst : denT_x'.fst = zffalse := hDsubst_fst_eq ▸ hDsubst_false
                    have hP_val_eq : P_val = zffalse := hdenT_x'_fst_eq ▸ hDenT_fst
                    have hDimp_fst_eq_zffalse : Dimp.fst = zffalse := by
                      have hp := hDapp_den
                      have hq := hDsubst_den
                      have : ⟦((@ˢD_enc) (List.map SMT.Term.var zs).toPairl).abstract
                          (Function.updates Δ'_alt zs (List.ofFn (fun i => some (w i)))) (hcov_appD_upd_alt w) ⇒ˢ'
                          (SMT.substList vs (List.map SMT.Term.var zs) P_enc).abstract
                            (Function.updates Δ'_alt zs (List.ofFn (fun i => some (w i)))) (hcov_subst_upd_alt w)⟧ˢ =
                          some ⟨zffalse, .bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
                        have hDnq := denote_not_eq_zftrue_of_some_zffalse hq hDsubst_ty hDsubst_false
                        have hDand := denote_and_eq_zftrue_of_some_zftrue hp hDapp_ty hDapp_true
                          hDnq rfl rfl
                        exact denote_not_eq_zffalse_of_some_zftrue hDand rfl rfl
                      have := Option.some.inj (this.symm.trans hDimp)
                      have := congrArg (·.fst) this.symm; dsimp at this; exact this
                    rw [hDimp_fst_eq_zffalse, hP_val_eq]
                  · have hDsubst_fst_eq : Dsubst.fst = denT_x'.fst := by rw [hDsubst_eq_denT]
                    have hDenT_fst : denT_x'.fst = zftrue := hDsubst_fst_eq ▸ hDsubst_true
                    have hP_val_eq : P_val = zftrue := hdenT_x'_fst_eq ▸ hDenT_fst
                    have hDimp_fst_eq_zftrue : Dimp.fst = zftrue := by
                      have hp := hDapp_den
                      have hq := hDsubst_den
                      have : ⟦((@ˢD_enc) (List.map SMT.Term.var zs).toPairl).abstract
                          (Function.updates Δ'_alt zs (List.ofFn (fun i => some (w i)))) (hcov_appD_upd_alt w) ⇒ˢ'
                          (SMT.substList vs (List.map SMT.Term.var zs) P_enc).abstract
                            (Function.updates Δ'_alt zs (List.ofFn (fun i => some (w i)))) (hcov_subst_upd_alt w)⟧ˢ =
                          some ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ :=
                        denote_imp_eq_zftrue_of_both_zftrue.{u} hp hDapp_ty hDapp_true
                          hq hDsubst_ty hDsubst_true
                      have := Option.some.inj (this.symm.trans hDimp)
                      have := congrArg (·.fst) this.symm; dsimp at this; exact this
                    rw [hDimp_fst_eq_zftrue, hP_val_eq]
                constructor
                · intro hbody_fst
                  right
                  intro Px τPx hPx hPx_den
                  have hPx_den' := hPx_den
                  rw [hP_den_x_raw] at hPx_den'
                  have hinj := congrArg PSigma.fst (Option.some.inj hPx_den')
                  dsimp at hinj
                  rw [← hinj, ← hbody_fst_eq_P_val]
                  exact hbody_fst
                · intro hor
                  rcases hor with hx_B_not_𝒟 | hall
                  · exact absurd hx_B_in_𝒟 hx_B_not_𝒟
                  · have hPval_true : P_val = zftrue :=
                      hall P_val BType.bool hP_val_raw hP_den_x_raw
                    rw [hbody_fst_eq_P_val]
                    exact hPval_true
            -- STEP 9: Apply retract_forallVal_eq_sInter_sep to close the goal.
            refine ⟨forallVal_alt, hforallVal_alt, ?_, ?_⟩
            · exact hforallVal_alt_ty
            · -- Goal: retract .bool forallVal_alt.fst = T_alt. Mirror primary
              -- case by peeling rest_alt's three dites, then applying
              -- retract_forallVal_eq_sInter_sep in the nonempty branch.
              split_ifs at rest_alt with h1 h2 h3
              · -- h1, h2, h3 (𝒟_alt = ∅): apply empty-domain bridge.
                simp only [Option.pure_def, Option.some.injEq, PSigma.mk.injEq]
                  at rest_alt
                -- Empty 𝒟_alt ⇒ the forall is vacuously true; retract .bool = zftrue.
                obtain ⟨hT_eq_raw_alt, _⟩ := rest_alt
                rw [← hT_eq_raw_alt]
                classical
                exact _root_.retract_forallVal_eq_zftrue_of_empty_𝒟 (vs := vs) vs_nemp
                  (τ := τ) τ_hasArity
                  (D := D) (D_enc := D_enc)
                  (P_enc_subst := SMT.substList vs (List.map SMT.Term.var zs) P_enc)
                  (zs := zs) (τs := τs) zs_nemp zs_len τs_toProdl_eq
                  (imp_body := imp_body) imp_body_def
                  (Δ_ctx := Δ'_alt) hcov_forall_alt hforallVal_alt
                  hgo_cov_alt hcov_imp_upd_alt himp_total_alt
                  (𝒟_val := 𝒟_alt) h3
                  (P := P) («Δ» := Δ_alt) Δ_fv_alt
                  (zs_len_pos_hyp := zs_len_pos) (vs_zs_len := vs_zs_len)
                  (hbridge := hbridge_alt)
              · -- h1, h2, h3 (¬𝒟_alt = ∅): apply retract_forallVal_eq_sInter_sep.
                simp only [Option.pure_def, Option.some.injEq, PSigma.mk.injEq]
                  at rest_alt
                obtain ⟨hT_eq_raw_alt, _⟩ := rest_alt
                have 𝒟_alt_nonempty : 𝒟_alt.Nonempty :=
                  𝒟_alt.eq_empty_or_nonempty.resolve_left h3
                classical
                show retract BType.bool forallVal_alt.fst = T_alt
                apply retract_forallVal_eq_sInter_sep (vs := vs) vs_nemp vs_nodup
                  (τ := τ) τ_hasArity
                  (D := D) (D_enc := D_enc)
                  (P_enc_subst := SMT.substList vs (List.map SMT.Term.var zs) P_enc)
                  (zs := zs) (τs := τs) zs_nemp zs_len τs_toProdl_eq
                  (imp_body := imp_body) imp_body_def zs_not_fv_D
                  (Δ_ctx := Δ'_alt) hcov_forall_alt hforallVal_alt
                  (denD_val := denD_alt)
                  hcov_D_upd_alt den_D_upd_eq_alt denD_alt_type denD_alt_func
                  (𝒟_val := 𝒟_alt) h𝒟_alt
                  𝒟_alt_nonempty
                  denD_alt_retract
                  hgo_cov_alt hcov_imp_upd_alt himp_total_alt himp_ty_alt
                  (P := P) («Δ» := Δ_alt) Δ_fv_alt
                  (T_val := T_alt)
                  (hT_eq := ?_)
                  (h_den_P := fun {x_fin} hx_typ hx_fin_in =>
                    h_den_P_alt_generic hx_typ hx_fin_in)
                  (h_den_P_bool := fun {x_fin} hx_typ hx_fin_in =>
                    h_den_P_alt_bool hx_typ hx_fin_in)
                  (zs_len_pos_hyp := zs_len_pos) (vs_zs_len := vs_zs_len)
                  (hbridge := hbridge_alt)
                · -- hT_eq: sInter(...) = T_alt. Match the lemma's expected pattern.
                  convert hT_eq_raw_alt using 9
                  set opt := ⟦(B.Term.abstract.go P vs Δ_alt
                    (fun v hv hvs => Δ_fv_alt v
                      (B.fv.mem_all (.inr ⟨hv, hvs⟩)))).uncurry
                    fun i => ⟨_, ⟨τ.get vs.length i, _⟩⟩⟧ᴮ with hopt
                  match opt with
                  | none => rfl
                  | some ⟨Pv, ⟨Pty, hPv⟩⟩ => rfl
              · -- h1 (negative): contradiction with h_den_P_alt_cond.
                exact absurd (fun {x} => h_den_P_alt_cond) h1
              · -- h1 (negative): contradiction with h_den_P_alt_cond.
                exact absurd (fun {x} => h_den_P_alt_cond) h1
          · exfalso
            rw [dif_neg h_den_P_alt_cond] at rest_alt
            exact Option.noConfusion rest_alt
        exact ⟨denT_alt, hext_Δ'_alt, Δ'_alt_none_out, Δ'_alt_wt,
          hforallVal_alt, hRDom_alt, Δ'_alt_dom⟩
  -- ==== EMPTY-DOMAIN CASE: 𝒟' = ∅, T = zftrue ====
  -- Mirrors the nonempty branch but uses `retract_forallVal_eq_zftrue_of_empty_𝒟`
  -- as the semantic bridge. `h_den_P`/`h_den_P_bool` are vacuous; `hbridge` takes
  -- the LEFT disjunct since 𝒟_val = ∅.
  simp only [Option.pure_def, Option.some.injEq] at rest_all
  -- Derive 𝒟 = ∅ (from 𝒟 = 𝒟' and h𝒟_empty).
  have h𝒟_eq : 𝒟 = 𝒟' := by
    have := den_D_eq ▸ den_D
    simp only [Option.some.injEq, PSigma.mk.injEq] at this
    exact this.1.symm
  have h𝒟_empty_eq : 𝒟 = ∅ := h𝒟_eq.trans h𝒟_empty
  -- Build Δ_ext for a default x_fin (any x_fin works since 𝒟' = ∅).
  -- Canonical x_fin uses `BType.defaultZFSet` for each component type.
  let x_fin_default : Fin vs.length → B.Dom.{u} := fun i =>
    ⟨(τ.get vs.length i).defaultZFSet, ⟨τ.get vs.length i,
      BType.mem_toZFSet_of_defaultZFSet⟩⟩
  set Δ_ext : B.RenamingContext.Context :=
    Function.updates «Δ» vs (List.ofFn fun i => some (x_fin_default i)) with Δ_ext_def
  have Δ_fv_P := Δ_fv_P_helper vs_nodup Δ_ext_def D P Δ_fv
  -- Classical case split on whether P denotes for the default x_fin:
  -- * Phase A1 (denotes): invoke P_ih, run encoder chain, close via
  --   `retract_forallVal_eq_zftrue_of_empty_𝒟`.
  -- * Phase A2 (doesn't denote): closed via `B.denote_exists_of_typing`.
  classical
  by_cases hP_den_cond : ∃ (P_val : ZFSet.{u}) (hP_val : P_val ∈ ⟦BType.bool⟧ᶻ),
      ⟦P.abstract Δ_ext Δ_fv_P⟧ᴮ = some ⟨P_val, BType.bool, hP_val⟩
  · -- Phase A1: extract the witness for `P_ih`.
    obtain ⟨P_val, hP_val, hP_den⟩ := hP_den_cond
    -- Mirror the no-flag nonempty branch (lines 1726+). Build Δ_D_ext for
    -- the encoder-side renaming context.
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
    -- Phase A1.1: invoke P_ih to encode P.
    mspec P_ih (E := E') (Λ := St₃.types) (α := .bool) typP
      («Δ» := Δ_ext) Δ_fv_P
      (Δ₀ := Δ_D_ext) Δ₀_ext_P (used := St₃.env.usedVars) Δ_D_ext_none_St₃
      (T := P_val) (hT := hP_val) hP_den vars_used_P_St₃ (n := St₃.env.freshvarsc)
      St₃_types_sub_E'_ctx_on_P_vars
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
    -- Phase A1.2: freshVarList for the SMT-level forall binders.
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
      vs_disj_St₁_helper (P := P) typ_D vs_Γ_disj Λ_inv vars_used_vs D_preserves_types
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
    -- Phase A1.3: castMembership (reflexive path since τs.toProdl = τ.toSMTType).
    unfold castMembership
    simp only [bind_pure_comp]
    rw [dif_pos τs_toProdl_eq]
    mspec Std.Do.Spec.pure
    -- Phase A1.4: erase bound vars vs and zs from the context.
    mspec SMT.eraseVars_forIn_spec (vars := vs)
    mrename_i pre_e1
    mintro ∀St₇
    mpure pre_e1
    obtain ⟨St₇_types, St₇_fvc, St₇_used⟩ := pre_e1
    simp only [← bind_pure_comp]
    mspec SMT.eraseVars_forIn_spec (vars := zs)
    mrename_i pre_e2
    mintro ∀St₈
    mpure pre_e2
    obtain ⟨St₈_types, St₈_fvc, St₈_used⟩ := pre_e2
    mspec Std.Do.Spec.pure
    mpure_intro
    -- Phase A1.5: subset chains for usedVars and types.
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
    have St₅_sub_St₇_used : St₅.env.usedVars ⊆ St₇.env.usedVars := by
      rw [St₇_used]; exact fun _ h => h
    have St₇_sub_St₈_used : St₇.env.usedVars ⊆ St₈.env.usedVars := by
      rw [St₈_used]; exact fun _ h => h
    have St₁_sub_St₈_used : St₁.env.usedVars ⊆ St₈.env.usedVars :=
      fun v hv => St₇_sub_St₈_used (St₅_sub_St₇_used
        (St₃_sub_St₅_used (St₂_sub_St₃_used (St₁_sub_St₂_used hv))))
    have St₁_sub_St₄_types : St₁.types ⊆ St₄.types :=
      AList.subset_trans St₁_sub_St₂_types
        (AList.subset_trans St₂_sub_St₃_types St₃_sub_St₄_types)
    have St₀_sub_St₄_types : St₀.types ⊆ St₄.types :=
      AList.subset_trans St₀_sub_St₁ St₁_sub_St₄_types
    have St₀_sub_St₅_types : St₀.types ⊆ St₅.types :=
      AList.subset_trans St₀_sub_St₄_types St₄_sub_St₅_types
    have zs_not_St₀ : ∀ z ∈ zs, z ∉ St₀.types := fun z hz hz_St₀ =>
      zs_not_types z hz (AList.mem_of_subset St₀_sub_St₄_types hz_St₀)
    -- Phase A1.6: build the 8-conjunct refine.
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- 1. used ⊆ St₈.env.usedVars
      exact fun v hv => St₁_sub_St₈_used (used_sub_St₁ hv)
    · -- 2. St₀.types ⊆ St₈.types
      intro ⟨k, τ_k⟩ hk_St₀
      have hk_St₅ : ⟨k, τ_k⟩ ∈ St₅.types.entries :=
        St₀_sub_St₅_types hk_St₀
      have hk_St₀_mem : k ∈ St₀.types :=
        AList.mem_keys.mpr (List.mem_map.mpr ⟨⟨k, τ_k⟩, hk_St₀, rfl⟩)
      have hk_not_vs : k ∉ vs := by
        intro hk_vs
        have hk_all : k ∈ (Term.all vs D P).vars := by
          unfold B.Term.vars; rw [List.mem_union_iff]; right
          simp only [B.bv, List.mem_append]; left; left; exact hk_vs
        exact vs_Γ_disj k hk_vs (Λ_inv k hk_all hk_St₀_mem)
      have hk_not_zs : k ∉ zs := fun hk_zs => zs_not_St₀ k hk_zs hk_St₀_mem
      rw [St₈_types, St₇_types]
      exact AList.mem_foldl_erase_of_not_mem_keys
        (AList.mem_foldl_erase_of_not_mem_keys hk_St₅ hk_not_vs) hk_not_zs
    · -- 3. AList.keys St₈.types ⊆ St₈.env.usedVars
      intro v hv
      obtain ⟨τ_v, hτ_v⟩ := Option.isSome_iff_exists.mp (AList.lookup_isSome.mpr hv)
      have h_St₈ : ⟨v, τ_v⟩ ∈ St₈.types.entries := AList.mem_lookup_iff.1 hτ_v
      have h_St₇ : ⟨v, τ_v⟩ ∈ St₇.types.entries := by
        rw [St₈_types] at h_St₈
        exact AList.foldl_erase_entries_subset zs _ h_St₈
      have h_St₅ : ⟨v, τ_v⟩ ∈ St₅.types.entries := by
        rw [St₇_types] at h_St₇
        exact AList.foldl_erase_entries_subset vs _ h_St₇
      have hv_not_zs : v ∉ zs := by
        intro hv_zs
        have h_notmem : v ∉ (zs.foldl (fun Γ w => AList.erase w Γ) St₇.types) :=
          AList.not_mem_foldl_erase_of_mem hv_zs zs_nodup
        apply h_notmem
        rw [← St₈_types]; exact hv
      rw [St₅_types] at h_St₅
      have hv_St₄_keys : v ∈ (List.foldl (fun Γ p => AList.insert p.1 p.2 Γ)
            St₄.types (zs.zip τs)).keys :=
        List.mem_map.mpr ⟨⟨v, τ_v⟩, h_St₅, rfl⟩
      have hv_St₄ : v ∈ St₄.types := by
        apply AList.mem_of_mem_foldl_insert' (v := v) (l := zs.zip τs)
        · exact hv_St₄_keys
        · intro h
          rw [List.mem_map] at h
          obtain ⟨⟨a, b⟩, hab, rfl⟩ := h
          exact hv_not_zs (List.of_mem_zip hab).1
      have hv_St₄_used : v ∈ St₄.env.usedVars := St₄_keys_sub hv_St₄
      have hv_St₅_used : v ∈ St₅.env.usedVars := by
        rw [St₅_used]; exact List.mem_append_right _ hv_St₄_used
      exact St₇_sub_St₈_used (St₅_sub_St₇_used hv_St₅_used)
    · -- 4. CoversUsedVars St₈.env.usedVars (Term.all vs D P)
      intro v hv
      rw [B.fv, List.mem_append] at hv
      rcases hv with hv_D | hv_P
      · exact St₁_sub_St₈_used (covers_D v hv_D)
      · have hv_fvP : v ∈ B.fv P := (List.mem_filter.mp hv_P).1
        have hv_St₄_used : v ∈ St₄.env.usedVars := covers_P v hv_fvP
        have hv_St₅_used : v ∈ St₅.env.usedVars := by
          rw [St₅_used]; exact List.mem_append_right _ hv_St₄_used
        exact St₇_sub_St₈_used (St₅_sub_St₇_used hv_St₅_used)
    · -- 5. σ = .bool
      trivial
    · -- 6. typing of the forall term
      have vs_typing_St₃ : ∀ (i : ℕ) (hi : i < vs.length),
          St₃.types.lookup vs[i] = some (τs[i]'(vs_τs_len ▸ hi)) := by
        intro i hi
        rw [St₃_types]
        have hi_τs : i < τs.length := vs_τs_len ▸ hi
        exact foldl_insert_lookup_zip vs_nodup hi hi_τs
      have vs_typing_St₅ : ∀ (i : ℕ) (hi : i < vs.length),
          St₅.types.lookup vs[i] = some (τs[i]'(vs_τs_len ▸ hi)) := fun i hi => by
        apply AList.lookup_of_subset
          (AList.subset_trans St₃_sub_St₄_types St₄_sub_St₅_types)
        exact vs_typing_St₃ i hi
      have typ_app_St₅ : St₅.types ⊢ˢ
          SMT.Term.app D_enc (List.map SMT.Term.var zs).toPairl : SMTType.bool := by
        refine SMT.Typing.app _ _ _ τ.toSMTType .bool typ_D_enc_St₅ ?_
        rw [← τs_toProdl_eq]
        exact toPairl_typ
      have typ_P_subst_St₅ : St₅.types ⊢ˢ
          SMT.substList vs (List.map SMT.Term.var zs) P_enc : SMTType.bool := by
        apply SMT_Typing_substList
        · exact SMT.Typing.weakening St₄_sub_St₅_types typ_P_enc
        · intro t ht
          rw [List.mem_map] at ht
          obtain ⟨z, _, rfl⟩ := ht
          simp [SMT.bv]
        · intro i hi_x hi_t hx
          have hi_zs : i < zs.length := by rw [List.length_map] at hi_t; exact hi_t
          have hi_τs : i < τs.length := vs_τs_len ▸ hi_x
          have hzi_typ : St₅.types.lookup zs[i] = some (τs[i]'(zs_len ▸ hi_zs)) :=
            zs_typing i hi_zs
          have hvi_typ : St₅.types.lookup vs[i] = some (τs[i]'hi_τs) :=
            vs_typing_St₅ i hi_x
          have h_get : (St₅.types.lookup vs[i]).get hx = τs[i]'hi_τs := by
            simp [hvi_typ]
          rw [h_get, List.getElem_map]
          exact SMT.Typing.var _ zs[i] _ (by
            have : (τs[i]'(zs_len ▸ hi_zs)) = (τs[i]'hi_τs) := by rfl
            rw [← this]; exact hzi_typ)
      have typ_body_St₅ : St₅.types ⊢ˢ
          SMT.Term.imp (SMT.Term.app D_enc (List.map SMT.Term.var zs).toPairl)
            (SMT.substList vs (List.map SMT.Term.var zs) P_enc) : SMTType.bool :=
        SMT.Typing.imp _ _ _ typ_app_St₅ typ_P_subst_St₅
      have zs_disj_St₈ : ∀ z ∈ zs, z ∉ St₈.types := fun z hz => by
        rw [St₈_types]
        exact AList.not_mem_foldl_erase_of_mem hz zs_nodup
      have zs_len_pos : 0 < zs.length := List.length_pos_of_ne_nil zs_nemp
      have zs_in_St₅ : ∀ z ∈ zs, z ∈ St₅.types := by
        intro z hz
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz
        exact AList.lookup_isSome.mp (Option.isSome_of_eq_some (zs_typing i hi))
      have bv_pairl_empty : SMT.bv ((List.map SMT.Term.var zs).toPairl) = [] :=
        bv_pairl_empty_helper zs
      have bv_subst_eq : ∀ t ∈ List.map SMT.Term.var zs, SMT.bv t = [] :=
        bv_subst_eq_helper zs
      have typ_P_St₅' : St₅.types ⊢ˢ P_enc : .bool :=
        SMT.Typing.weakening St₄_sub_St₅_types typ_P_enc
      have zs_disj_bv_body : ∀ z ∈ zs, z ∉ SMT.bv
          (SMT.Term.imp (SMT.Term.app D_enc (List.map SMT.Term.var zs).toPairl)
            (SMT.substList vs (List.map SMT.Term.var zs) P_enc)) :=
        zs_disj_bv_body_noflag_helper typ_app_St₅ typ_P_St₅' zs_in_St₅
      have St₈_types_combined : St₈.types =
          zs.foldl (fun Γ w => AList.erase w Γ)
            (vs.foldl (fun Γ w => AList.erase w Γ) St₅.types) := by
        rw [St₈_types, St₇_types]
      have h_entries_sub : (St₈.types.update zs τs).entries ⊆ St₅.types.entries :=
        h_entries_sub_helper zs_nodup zs_len St₈_types_combined (fun _ h => h)
          (fun i hi hi_τs => by
            rw [St₅_types]
            exact AList.mem_lookup_iff.mp (foldl_insert_lookup_zip zs_nodup hi hi_τs))
      have fv_pairl_sub_zs : ∀ v ∈ SMT.fv (List.map SMT.Term.var zs).toPairl, v ∈ zs :=
        fv_pairl_sub_zs_helper zs
      have h_fv_sub : ∀ v ∈ SMT.fv
          (SMT.Term.imp (SMT.Term.app D_enc (List.map SMT.Term.var zs).toPairl)
            (SMT.substList vs (List.map SMT.Term.var zs) P_enc)),
          v ∈ St₈.types.update zs τs := by
        intro v hv_body
        rw [SMT.TypeContext.mem_update_iff (hlen := zs_len)]
        unfold SMT.fv at hv_body
        rw [List.mem_append] at hv_body
        rcases hv_body with hv_app | hv_subst
        · unfold SMT.fv at hv_app
          rw [List.mem_append] at hv_app
          rcases hv_app with hv_D | hv_pairs
          · right
            have hv_St₁ : v ∈ St₁.types := SMT.Typing.mem_context_of_mem_fv typ_D_enc hv_D
            have hv_not_vs : v ∉ vs := fun hvs => vs_disj_St₁ v hvs hv_St₁
            have hv_St₁_used : v ∈ St₁.env.usedVars := St₁_keys_sub hv_St₁
            have hv_St₄_used : v ∈ St₄.env.usedVars :=
              St₃_sub_St₄ (St₁_sub_St₃_used hv_St₁_used)
            have hv_not_zs : v ∉ zs := fun hvz => zs_not_used v hvz hv_St₄_used
            have hv_St₅ : v ∈ St₅.types := AList.mem_of_subset St₁_sub_St₅_types hv_St₁
            obtain ⟨σ, hσ⟩ := Option.isSome_iff_exists.mp (AList.lookup_isSome.mpr hv_St₅)
            have hv_entry : ⟨v, σ⟩ ∈ St₅.types.entries := AList.mem_lookup_iff.mp hσ
            have hv_St₇_entry : ⟨v, σ⟩ ∈ St₇.types.entries := by
              rw [St₇_types]
              exact AList.mem_foldl_erase_of_not_mem_keys hv_entry hv_not_vs
            have hv_St₈_entry : ⟨v, σ⟩ ∈ St₈.types.entries := by
              rw [St₈_types]
              exact AList.mem_foldl_erase_of_not_mem_keys hv_St₇_entry hv_not_zs
            exact AList.mem_keys.mpr (List.mem_map.mpr ⟨⟨v, σ⟩, hv_St₈_entry, rfl⟩)
          · left
            exact fv_pairl_sub_zs v hv_pairs
        · rcases SMT_mem_fv_substList hv_subst with hv_P | ⟨t, ht, hv_t⟩
          · right
            have hv_St₄ : v ∈ St₄.types := SMT.Typing.mem_context_of_mem_fv typ_P_enc hv_P
            have hv_not_vs : v ∉ vs := by
              intro hvs
              have hlen : vs.length ≤ (List.map SMT.Term.var zs).length := by
                rw [List.length_map]; exact le_of_eq (zs_len ▸ vs_τs_len)
              by_cases h_all_no_fv : ∀ t ∈ List.map SMT.Term.var zs, v ∉ SMT.fv t
              · exact SMT_not_mem_fv_substList_of_mem_vars hlen hvs h_all_no_fv hv_subst
              · push_neg at h_all_no_fv
                obtain ⟨t, ht, hv_t⟩ := h_all_no_fv
                rw [List.mem_map] at ht
                obtain ⟨z, hz, rfl⟩ := ht
                simp only [SMT.fv, List.mem_singleton] at hv_t
                subst hv_t
                have hv_used : v ∈ St₄.env.usedVars :=
                  St₃_sub_St₄ (St₁_sub_St₃_used (used_sub_St₁ (vars_used_vs v hvs)))
                exact zs_not_used v hz hv_used
            have hv_not_zs : v ∉ zs := fun hvz => zs_not_types v hvz hv_St₄
            have hv_St₅ : v ∈ St₅.types := AList.mem_of_subset St₄_sub_St₅_types hv_St₄
            obtain ⟨σ, hσ⟩ := Option.isSome_iff_exists.mp (AList.lookup_isSome.mpr hv_St₅)
            have hv_entry : ⟨v, σ⟩ ∈ St₅.types.entries := AList.mem_lookup_iff.mp hσ
            have hv_St₇_entry : ⟨v, σ⟩ ∈ St₇.types.entries := by
              rw [St₇_types]
              exact AList.mem_foldl_erase_of_not_mem_keys hv_entry hv_not_vs
            have hv_St₈_entry : ⟨v, σ⟩ ∈ St₈.types.entries := by
              rw [St₈_types]
              exact AList.mem_foldl_erase_of_not_mem_keys hv_St₇_entry hv_not_zs
            exact AList.mem_keys.mpr (List.mem_map.mpr ⟨⟨v, σ⟩, hv_St₈_entry, rfl⟩)
          · left
            rw [List.mem_map] at ht
            obtain ⟨z, hz, rfl⟩ := ht
            simp only [SMT.fv, List.mem_singleton] at hv_t
            exact hv_t ▸ hz
      have h_typ_update : St₈.types.update zs τs ⊢ˢ
          SMT.Term.imp (SMT.Term.app D_enc (List.map SMT.Term.var zs).toPairl)
            (SMT.substList vs (List.map SMT.Term.var zs) P_enc) : SMTType.bool :=
        SMT.Typing.strengthening_of_fv_subset h_entries_sub typ_body_St₅ h_fv_sub
      exact SMT.Typing.forall St₈.types zs τs _
        zs_disj_St₈ zs_disj_bv_body zs_len_pos zs_len h_typ_update
    · -- 7. preservation: extracted to `bullet7_noflag_helper`.
      exact bullet7_noflag_helper vs_nodup zs_nodup St₂_types St₃_types St₅_types
        St₇_types St₈_types St₂_used St₃_used D_preserves_types P_preserves_types
        used_sub_St₁
    · -- 8. ∃ Δ' ∃ denT': renaming + denotation, uses retract_forallVal_eq_zftrue_of_empty_𝒟
      -- Phase A1.7: Δ' definition (agrees with Δ_D on vs, else with Δ_P).
      set Δ' : SMT.RenamingContext.Context := fun v =>
        if v ∈ vs then Δ_D v else Δ_P v with Δ'_def
      have hΔ_D_ext_outside : ∀ v ∉ vs, Δ_D_ext v = Δ_D v := fun v hv => by
        rw [Δ_D_ext_def]; exact Function.updates_of_not_mem Δ_D vs _ v hv
      have Δ'_extends_Δ₀ : RenamingContext.Extends Δ' Δ₀ :=
        Δ'_def ▸ Δ'_extends_Δ₀_noflag_helper Δ_D_extends Δ_P_extends hΔ_D_ext_outside
      have vs_sub_St₃_used : ∀ v ∈ vs, v ∈ St₃.env.usedVars := by
        intro v hvs
        rw [St₃_used, St₂_used]
        suffices ∀ (ws : List SMT.𝒱) (τs' : List SMTType) (acc : List SMT.𝒱),
            ws.length ≤ τs'.length → v ∈ ws →
            v ∈ (ws.zip τs').foldl (fun used p => p.1 :: used) acc by
          exact this vs τs St₁.env.usedVars (le_of_eq vs_τs_len) hvs
        intro ws
        induction ws with
        | nil => intro _ _ _ hv; exact absurd hv List.not_mem_nil
        | cons w ws' ih =>
          intro τs' acc hlen hv
          cases τs' with
          | nil => simp at hlen
          | cons τ' τs'' =>
            simp only [List.zip_cons_cons, List.foldl_cons]
            rcases List.mem_cons.mp hv with rfl | hv'
            · suffices ∀ (l : List (SMT.𝒱 × SMTType)) (acc' : List SMT.𝒱),
                  v ∈ acc' → v ∈ l.foldl (fun used p => p.1 :: used) acc' by
                exact this _ _ (List.mem_cons_self ..)
              intro l; induction l with
              | nil => exact fun _ h => h
              | cons _ _ ih' => intro acc' hmem; exact ih' _ (List.mem_cons_of_mem _ hmem)
            · exact ih τs'' _ (by simp at hlen; omega) hv'
      have Δ'_none_out : ∀ v ∉ St₈.env.usedVars, Δ' v = none :=
        Δ'_def ▸ Δ'_none_out_noflag_helper St₅_used St₇_used St₈_used
          St₃_sub_St₅_used St₅_sub_St₇_used St₇_sub_St₈_used
          vs_sub_St₃_used Δ_P_none
      have hΔ_ext_outside : ∀ v ∉ vs, Δ_ext v = «Δ» v := fun v hv => by
        rw [Δ_ext_def]; exact Function.updates_of_not_mem «Δ» vs _ v hv
      have Δ'_src_ext : RenamingContext.ExtendsOnSourceFV Δ' «Δ» (Term.all vs D P) :=
        Δ'_def ▸ Δ'_src_ext_noflag_helper Δ_D_src_ext Δ_P_src_ext Δ_P_extends
          vs_not_D_fv hΔ_D_ext_outside hΔ_ext_outside
      -- Phase A1.8: Δ'_covers and ∃ denT' construction.
      -- Helper: fv (zs.map .var).toPairl ⊆ zs (extracted helper)
      have fv_pairl_sub_zs : ∀ v ∈ SMT.fv (List.map SMT.Term.var zs).toPairl, v ∈ zs :=
        fv_pairl_sub_zs_helper zs
      have Δ'_covers : SMT.RenamingContext.CoversFV Δ'
          (SMT.Term.forall zs τs
            (SMT.Term.imp (SMT.Term.app D_enc (List.map SMT.Term.var zs).toPairl)
              (SMT.substList vs (List.map SMT.Term.var zs) P_enc))) :=
        Δ'_def ▸ Δ'_covers_noflag_helper zs_len vs_τs_len typ_D_enc typ_P_enc
          vs_disj_St₁ Δ_D_covers Δ_P_covers Δ_P_extends hΔ_D_ext_outside fv_pairl_sub_zs
      refine ⟨Δ', Δ'_covers, Δ'_extends_Δ₀, Δ'_src_ext, Δ'_none_out, ?_⟩
      -- FRONTIER: ∃ denT', ⟦.forall zs τs body⟧ = some denT' ∧ RDom ∧ totality.
      -- The semantic bridge `retract_forallVal_eq_zftrue_of_empty_𝒟` will close
      -- the RDom goal in the empty-domain branch (replacing
      -- `retract_forallVal_eq_sInter_sep` from the nonempty branch).
      --
      -- Phase 1: Prerequisites for retract_forallVal_eq_zftrue_of_empty_𝒟.
      have zs_len_pos : 0 < zs.length :=
        List.length_pos_of_ne_nil zs_nemp
      have vs_zs_len : vs.length = zs.length := by rw [vs_τs_len, zs_len]
      have zs_not_fv_D : ∀ z ∈ zs, z ∉ SMT.fv D_enc := by
        intro z hz hz_fv
        have hz_St₁ : z ∈ St₁.types :=
          SMT.Typing.mem_context_of_mem_fv typ_D_enc hz_fv
        have hz_used : z ∈ St₄.env.usedVars :=
          St₃_sub_St₄ (St₁_sub_St₃_used (St₁_keys_sub hz_St₁))
        exact zs_not_used z hz hz_used
      have denD'_func : ⟦τ.toSMTType⟧ᶻ.IsFunc 𝔹 denD'.fst := by
        have : denD'.fst ∈ ⟦τ.toSMTType⟧ᶻ.funs 𝔹 := by
          simpa [denD'_type, SMTType.toZFSet] using denD'.snd.snd
        exact ZFSet.mem_funs.mp this
      -- Phase 2: D_enc denotation under Δ' (coincides with Δ_D on fv D_enc).
      obtain ⟨Δ'_agrees_Δ_D_on_D, hcov_D_Δ', den_D_Δ'⟩ :=
        Δ'_agrees_noflag_bundle.{u} Δ'_def hΔ_D_ext_outside typ_D_enc vs_disj_St₁
          Δ_D_covers Δ_P_extends den_D_enc
      -- D_enc under zs-updates (disjoint from fv D_enc)
      have hcov_D_upd := hcov_D_upd_helper.{u} (zs := zs) zs_not_fv_D hcov_D_Δ'
      have den_D_upd_eq := den_D_upd_eq_helper.{u} (zs := zs) zs_not_fv_D hcov_D_Δ' den_D_Δ'
      -- Phase 3: Define imp_body and forall_term, prove body totality/typing.
      set imp_body : SMT.Term :=
        (SMT.Term.app D_enc (List.map SMT.Term.var zs).toPairl).imp
          (SMT.substList vs (List.map SMT.Term.var zs) P_enc) with imp_body_def
      have hcov_imp_upd := hcov_imp_upd_helper.{u} zs_nodup (τs := τs) Δ'_covers
      have hgo_cov := hgo_cov_helper (τs := τs) Δ'_covers
      have hpairl_cov := hpairl_cov_helper.{u} (Δ' := Δ') zs_nodup fv_pairl_sub_zs
      have hpairl_den :=
        hpairl_den_helper.{u} (Δ' := Δ') zs_len zs_nodup zs_len_pos hpairl_cov
      have hcov_appD_upd := hcov_appD_upd_helper.{u} hcov_D_upd hpairl_cov
      have hdenote_appD_upd :=
        hdenote_appD_upd_helper.{u} (D_enc := D_enc) (Δ' := Δ') (denD' := denD') (τ := τ)
          zs_len zs_len_pos τs_toProdl_eq denD'_type denD'_func
          hpairl_cov hpairl_den hcov_D_upd den_D_upd_eq hcov_appD_upd
      have hcov_subst_upd : ∀ (w : Fin zs.length → SMT.Dom.{u}),
          SMT.RenamingContext.CoversFV
            (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
            (SMT.substList vs (List.map SMT.Term.var zs) P_enc) := by
        intro w v hv
        rcases SMT_mem_fv_substList hv with hv_P | ⟨t, ht, hv_t⟩
        · by_cases hvz : v ∈ zs
          · rw [Function.updates_eq_if (by rw [List.length_ofFn]) zs_nodup, dif_pos hvz]
            simp only [List.getElem_ofFn, Option.isSome_some]
          · rw [Function.updates_of_not_mem Δ' zs _ v hvz]
            have hv_imp : v ∈ SMT.fv imp_body := by
              show v ∈ SMT.fv (SMT.Term.imp _ _)
              exact SMT.fv.mem_imp (Or.inr hv)
            have hv_f : v ∈ SMT.fv (SMT.Term.forall zs τs imp_body) := by
              simp only [SMT.fv, List.mem_removeAll_iff]
              exact ⟨hv_imp, hvz⟩
            exact Δ'_covers v hv_f
        · rw [List.mem_map] at ht
          obtain ⟨z, hz, rfl⟩ := ht
          simp only [SMT.fv, List.mem_singleton] at hv_t
          subst hv_t
          rw [Function.updates_eq_if (by rw [List.length_ofFn]) zs_nodup, dif_pos hz]
          simp only [List.getElem_ofFn, Option.isSome_some]
      -- Empty-domain `hsubst_spec` and `himp_total`/`himp_ty` defer to the same proof
      -- structure as the nonempty case (factored into `hsubst_spec_helper`).
      have hsubst_spec :=
        hsubst_spec_helper.{u}
          (vs := vs) (zs := zs) (τs := τs)
          (Δ' := Δ') (P_enc := P_enc) (St₄types := St₄.types)
          vs_nodup zs_nodup vs_zs_len vs_τs_len zs_len
          (Δ'_outside_vs_isSome := fun v hvvs hv => by
            rw [Δ'_def]; simp [hvvs]; exact Δ_P_covers v hv)
          (Δ'_outside_vs_wt := fun v hvvs d hd τ hτ => by
            rw [Δ'_def] at hd; simp [hvvs] at hd
            exact Δ_P_wt v d hd τ hτ)
          (vs_sub_St₄_types :=
            vs_sub_types_helper vs_nodup vs_τs_len St₃_types St₃_sub_St₄_types)
          (vs_typing_St₄ := fun i hi => by
            have h_St₃_lookup : St₃.types.lookup vs[i] =
                some (τs[i]'(vs_τs_len ▸ hi)) := by
              rw [St₃_types]
              exact foldl_insert_lookup_zip vs_nodup hi (vs_τs_len ▸ hi)
            exact AList.lookup_of_subset St₃_sub_St₄_types h_St₃_lookup)
          (zs_not_bv_P :=
            zs_not_bv_P_helper zs_len St₄_sub_St₅_types typ_P_enc zs_typing)
          (zs_not_St₄_types := zs_not_types)
          typ_P_enc hcov_subst_upd
      obtain ⟨himp_total, himp_ty⟩ :=
        himp_total_ty_bundle.{u} zs_len imp_body_def hcov_imp_upd
          (happD_bool := fun w hw => by
            obtain ⟨_, Dapp, hDapp_ty, _, hDapp_den⟩ := hdenote_appD_upd w hw
            exact ⟨Dapp, hDapp_ty, hDapp_den⟩)
          hsubst_spec
      -- Phase 4: Build forallVal_isSome, then apply the empty bridge.
      have htot_forall_raw :
          ∀ {x : Fin zs.length → SMT.Dom.{u}},
          (∀ i, (x i).snd.fst = τs[i.val]'(zs_len ▸ i.isLt) ∧
            (x i).fst ∈ ⟦τs[i.val]'(zs_len ▸ i.isLt)⟧ᶻ) →
          ⟦(SMT.Term.abstract.go imp_body zs Δ' hgo_cov).uncurry x⟧ˢ.isSome = true :=
        htot_forall_raw_helper.{u} (zs := zs) (τs := τs) zs_len
          (Δ_ctx := Δ') (hgo_cov := hgo_cov) himp_total
      have forallVal_isSome :=
        forallVal_isSome_helper.{u} zs_len zs_len_pos Δ'_covers htot_forall_raw
      obtain ⟨forallVal, hforallVal⟩ := Option.isSome_iff_exists.mp forallVal_isSome
      refine ⟨forallVal, hforallVal, ?_, ?_⟩
      -- Part 1: ⟨T, .bool, hT⟩ ≘ᶻ forallVal via empty-domain bridge.
      · -- Extract T = zftrue from rest_all.
        simp only [PSigma.mk.injEq] at rest_all
        obtain ⟨hT_eq_raw, _⟩ := rest_all
        have hforallVal_ty : forallVal.snd.fst = .bool :=
          hforallVal_ty_helper.{u} zs_len zs_len_pos htot_forall_raw hforallVal
        refine ⟨hforallVal_ty, ?_⟩
        -- Build hbridge: simpler than nonempty since 𝒟 = ∅ ⇒ x_B ∉ 𝒟 always.
        -- Factored into `hbridge_empty_helper`.
        have hbridge :=
          hbridge_empty_helper.{u}
            (vs := vs) (zs := zs) (τs := τs)
            zs_len zs_len_pos τ_hasArity Δ_fv imp_body_def
            (denD' := denD') denD'_func denD'_retract h𝒟_empty_eq
            hcov_imp_upd hcov_appD_upd hcov_subst_upd
            hdenote_appD_upd hsubst_spec
        classical
        show retract BType.bool forallVal.fst = T
        -- Apply retract_forallVal_eq_zftrue_of_empty_𝒟.
        have hT_zftrue : T = zftrue := by
          rw [← hT_eq_raw]
        rw [hT_zftrue]
        apply retract_forallVal_eq_zftrue_of_empty_𝒟
          (vs := vs) vs_nemp (τ := τ) τ_hasArity
          (D := D) (D_enc := D_enc)
          (P_enc_subst := SMT.substList vs (List.map SMT.Term.var zs) P_enc)
          (zs := zs) (τs := τs) zs_nemp zs_len τs_toProdl_eq
          (imp_body := imp_body) imp_body_def
          (Δ_ctx := Δ') Δ'_covers hforallVal
          hgo_cov hcov_imp_upd himp_total
          (𝒟_val := 𝒟) h𝒟_empty_eq
          (P := P) («Δ» := «Δ») Δ_fv
          (zs_len_pos_hyp := zs_len_pos) (vs_zs_len := vs_zs_len)
          (hbridge := hbridge)
      -- Part 2: Totality clause — empty-domain alt context.
      -- Mirrors the nonempty Part 2 (lines 3841-5545) but with the empty-domain
      -- bridge: at h3 (𝒟_alt = ∅) we apply `retract_forallVal_eq_zftrue_of_empty_𝒟`,
      -- otherwise (h3 negative) we apply `retract_forallVal_eq_sInter_sep`.
      · intro Δ_alt Δ_fv_alt Δ₀_alt hext_alt hnone_alt hwt_alt T_alt hT_alt hden_alt
        have hden_D_alt := hden_D_alt_helper.{u} (typ_D := typ_D) hden_alt
        obtain ⟨𝒟_alt, h𝒟_alt, hden_D_alt_eq⟩ := hden_D_alt
        set Δ₀_alt_D : SMT.RenamingContext.Context :=
          fun v => match B.RenamingContext.toSMTOnFV Δ_alt D v with
            | some d => some d
            | none => if v ∈ St₁.env.usedVars then
                match Δ₀_alt v with
                | some d => some d
                | none => Δ₀ v
              else none
        obtain ⟨hext_alt_D, hnone_alt_D⟩ :=
          hΔ₀_alt_D_setup_helper (D := D) (St₁_used := St₁.env.usedVars)
            covers_D (Δ_alt := Δ_alt) (Δ₀ := Δ₀) (Δ₀_alt := Δ₀_alt)
        have hwt_alt_D : ∀ v (d : SMT.Dom), Δ₀_alt_D v = some d →
            ∀ τ_v, St₁.types.lookup v = some τ_v → d.snd.fst = τ_v := by
          intro v d hv τ_v hτ_v
          change (match B.RenamingContext.toSMTOnFV Δ_alt D v with
            | some d => some d
            | none => if v ∈ St₁.env.usedVars then
                match Δ₀_alt v with
                | some d => some d
                | none => Δ₀ v
              else none) = some d at hv
          have hv_St₁ : v ∈ St₁.types := by
            rw [← AList.lookup_isSome, hτ_v]; rfl
          have hv_not_vs : v ∉ vs := fun hvs => vs_disj_St₁ v hvs hv_St₁
          have hv_St₄ : v ∈ St₄.types := AList.mem_of_subset St₁_sub_St₄_types hv_St₁
          have hv_not_zs : v ∉ zs := fun hvz => zs_not_types v hvz hv_St₄
          have hv_St₅_entry : ⟨v, τ_v⟩ ∈ St₅.types.entries :=
            AList.mem_lookup_iff.mp (AList.lookup_of_subset St₁_sub_St₅_types hτ_v)
          have hv_St₇_entry : ⟨v, τ_v⟩ ∈ St₇.types.entries := by
            rw [St₇_types]
            exact AList.mem_foldl_erase_of_not_mem_keys hv_St₅_entry hv_not_vs
          have hv_St₈_entry : ⟨v, τ_v⟩ ∈ St₈.types.entries := by
            rw [St₈_types]
            exact AList.mem_foldl_erase_of_not_mem_keys hv_St₇_entry hv_not_zs
          have hτ_v_St₈ : St₈.types.lookup v = some τ_v :=
            AList.mem_lookup_iff.2 hv_St₈_entry
          cases h_toSMT : B.RenamingContext.toSMTOnFV Δ_alt D v with
          | some d' =>
            simp only [h_toSMT] at hv; cases hv
            have hv_fv_D : v ∈ B.fv D := by
              by_contra hv_not
              simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_not] at h_toSMT
            have h_onFV : B.RenamingContext.toSMTOnFV Δ_alt (Term.all vs D P) v = some d := by
              simp only [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                B.RenamingContext.restrictToFV_eq_of_mem (B.fv.mem_all (.inl hv_fv_D))]
              simp only [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                B.RenamingContext.restrictToFV_eq_of_mem hv_fv_D] at h_toSMT
              exact h_toSMT
            have hΔ₀_alt_v : Δ₀_alt v = some d := hext_alt h_onFV
            exact hwt_alt v d hΔ₀_alt_v τ_v hτ_v_St₈
          | none =>
            simp only [h_toSMT] at hv
            split_ifs at hv with h_used
            · cases hΔ₀_alt : Δ₀_alt v with
              | some d' =>
                simp only [hΔ₀_alt, Option.some.injEq] at hv; subst hv
                exact hwt_alt v d' hΔ₀_alt τ_v hτ_v_St₈
              | none =>
                simp only [hΔ₀_alt] at hv
                exact Δ_D_wt v d (Δ_D_extends hv) τ_v hτ_v
        have hdom_alt_D : ∀ v, Δ₀_alt_D v ≠ none → v ∈ St₁.types := by
          intro v hv
          change (match B.RenamingContext.toSMTOnFV Δ_alt D v with
            | some d => some d
            | none => if v ∈ St₁.env.usedVars then
                match Δ₀_alt v with
                | some d => some d
                | none => Δ₀ v
              else none) ≠ none at hv
          cases h_toSMT : B.RenamingContext.toSMTOnFV Δ_alt D v with
          | some d =>
            have hv_fv : v ∈ B.fv D := by
              by_contra hv_not
              simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_not] at h_toSMT
            exact fv_sub_typings typ_D typ_D_enc v hv_fv
          | none =>
            simp only [h_toSMT] at hv
            split_ifs at hv with h_used
            · cases hΔ₀_alt : Δ₀_alt v with
              | some d' =>
                have hv_fv_all : v ∈ B.fv (Term.all vs D P) :=
                  SMT.RenamingContext.ExtendsOnSourceFV.dom_sub_B_fv
                    hext_alt v (by rw [hΔ₀_alt]; simp)
                exact fv_sub_typings typ_t typ_D_enc v hv_fv_all
              | none =>
                simp only [hΔ₀_alt] at hv
                have hv_fv_all : v ∈ B.fv (Term.all vs D P) :=
                  SMT.RenamingContext.ExtendsOnSourceFV.dom_sub_B_fv Δ₀_ext v hv
                exact fv_sub_typings typ_t typ_D_enc v hv_fv_all
            · exact absurd rfl hv
        obtain ⟨Δ_D_alt, hcov_D_alt, denD_alt, hext_D_alt, Δ_D_alt_none_out,
            Δ_D_alt_wt_out, hden_D_alt, hRDom_D_alt, Δ_D_alt_dom⟩ :=
          D_RDom.2
            (Δ_alt := Δ_alt)
            (fun v hv => Δ_fv_alt v (B.fv.mem_all (.inl hv)))
            (Δ₀_alt := Δ₀_alt_D) hext_alt_D hnone_alt_D
            hwt_alt_D
            𝒟_alt h𝒟_alt hden_D_alt_eq
        -- Δ'_alt: Δ_D_alt on fv(D_enc), Δ_P on fv(P_enc) \ vs, else Δ'.
        set Δ'_alt : SMT.RenamingContext.Context :=
          fun v => match Δ₀_alt v with
            | some d => some d
            | none => match Δ_D_alt v with
              | some d => some d
              | none => Δ' v
          with Δ'_alt_def
        have hext_Δ'_alt : RenamingContext.Extends Δ'_alt Δ₀_alt := by
          intro v d hv; simp only [Δ'_alt_def, hv]
        have Δ'_alt_none_out : ∀ v ∉ St₈.env.usedVars, Δ'_alt v = none := by
          intro v hv
          show (match Δ₀_alt v with
            | some d => some d
            | none => match Δ_D_alt v with
              | some d => some d
              | none => Δ' v) = none
          have h1 : Δ₀_alt v = none := hnone_alt v hv
          rw [h1]
          have hv_St₁ : v ∉ St₁.env.usedVars := fun hv_St₁' => hv (St₁_sub_St₈_used hv_St₁')
          have h2 : Δ_D_alt v = none := Δ_D_alt_none_out v hv_St₁
          rw [h2]
          exact Δ'_none_out v hv
        have hcov_forall_alt : SMT.RenamingContext.CoversFV Δ'_alt
            (Term.forall zs τs imp_body) := by
          intro v hv
          show (match Δ₀_alt v with
            | some d => some d
            | none => match Δ_D_alt v with
              | some d => some d
              | none => Δ' v).isSome = true
          cases h : Δ₀_alt v with
          | some d => simp
          | none =>
            cases h2 : Δ_D_alt v with
            | some d => simp
            | none =>
              simp only
              exact Δ'_covers v hv
        have Δ'_alt_wt : ∀ v (d : SMT.Dom), Δ'_alt v = some d →
            ∀ τ_v, St₈.types.lookup v = some τ_v → d.snd.fst = τ_v :=
          Δ'_alt_wt_helper (vs := vs) (zs := zs)
            St₁_sub_St₄_types St₁_sub_St₅_types St₄_sub_St₅_types
            St₇_types St₈_types vs_disj_St₁ zs_not_types
            (Δ' := Δ') (Δ_D := Δ_D) (Δ_P := Δ_P) (Δ_D_alt := Δ_D_alt)
            (Δ₀_alt := Δ₀_alt) Δ'_def Δ_D_dom Δ_D_alt_dom Δ_D_alt_wt_out
            Δ_P_dom Δ_P_wt hwt_alt
        have Δ'_alt_dom : ∀ v, Δ'_alt v ≠ none → v ∈ St₈.types :=
          Δ'_alt_dom_helper fv_sub_typings (vs := vs) (zs := zs)
            (D := D) (P := P) (τ := τ) typ_t (D_enc := D_enc) typ_D_enc
            St₁_sub_St₄_types St₁_sub_St₅_types St₄_sub_St₅_types
            St₇_types St₈_types vs_disj_St₁ zs_not_types
            (Δ' := Δ') (Δ_D := Δ_D) (Δ_P := Δ_P) (Δ_D_alt := Δ_D_alt)
            (Δ₀_alt := Δ₀_alt) Δ'_def Δ_D_dom Δ_D_alt_dom Δ_P_dom
            (Δ_alt := Δ_alt) hext_alt
        refine ⟨Δ'_alt, hcov_forall_alt, ?_⟩
        obtain ⟨denT_alt, hforallVal_alt, hRDom_alt⟩ : ∃ denT_alt,
            ⟦(Term.forall zs τs imp_body).abstract Δ'_alt hcov_forall_alt⟧ˢ =
              some denT_alt ∧ ⟨T_alt, ⟨BType.bool, hT_alt⟩⟩ ≘ᶻ denT_alt := by
          -- STEP 1: Derive denD_alt properties from hRDom_D_alt.
          have denD_alt_type : denD_alt.snd.fst = τ.toSMTType.fun .bool :=
            hRDom_D_alt.1
          have denD_alt_retract : retract τ.set denD_alt.fst = 𝒟_alt :=
            hRDom_D_alt.2
          have denD_alt_func : ⟦τ.toSMTType⟧ᶻ.IsFunc 𝔹 denD_alt.fst := by
            have : denD_alt.fst ∈ ⟦τ.toSMTType⟧ᶻ.funs 𝔹 := by
              simpa [denD_alt_type, SMTType.toZFSet] using denD_alt.snd.snd
            exact ZFSet.mem_funs.mp this
          -- STEP 2: Δ'_alt agrees with Δ_D_alt on fv(D_enc); lift D_enc denotation.
          have Δ'_alt_agrees_Δ_D_alt_on_D :
              SMT.RenamingContext.AgreesOnFV Δ_D_alt Δ'_alt D_enc :=
            Δ'_alt_agrees_Δ_D_alt_on_D_helper (vs := vs) (D := D) (P := P)
              (τ := τ) (St₁_types := St₁.types) (St₁_used := St₁.env.usedVars)
              typ_D_enc St₁_keys_sub
              (Δ' := Δ') (Δ_D_alt := Δ_D_alt) (Δ₀_alt := Δ₀_alt) (Δ₀ := Δ₀)
              (Δ_alt := Δ_alt) hext_alt hcov_D_alt hext_D_alt
          have hcov_D_Δ'_alt : SMT.RenamingContext.CoversFV Δ'_alt D_enc := by
            intro v hv
            rw [← Δ'_alt_agrees_Δ_D_alt_on_D hv]
            exact hcov_D_alt v hv
          have den_D_Δ'_alt : ⟦D_enc.abstract Δ'_alt hcov_D_Δ'_alt⟧ˢ = some denD_alt := by
            have heq := SMT.RenamingContext.denote_congr_of_agreesOnFV
              (h1 := hcov_D_alt) (h2 := hcov_D_Δ'_alt) Δ'_alt_agrees_Δ_D_alt_on_D
            unfold SMT.RenamingContext.denote at heq
            rw [← heq]; exact hden_D_alt
          have hcov_D_upd_alt :=
            hcov_D_upd_helper.{u} (zs := zs) zs_not_fv_D hcov_D_Δ'_alt
          have den_D_upd_eq_alt :=
            den_D_upd_eq_helper.{u} (zs := zs) zs_not_fv_D hcov_D_Δ'_alt den_D_Δ'_alt
          -- STEP 3: Build Phase 3a infrastructure at Δ'_alt.
          have hcov_imp_upd_alt :=
            hcov_imp_upd_helper.{u} zs_nodup (τs := τs) hcov_forall_alt
          have hgo_cov_alt := hgo_cov_helper (τs := τs) hcov_forall_alt
          have hpairl_cov_alt :=
            hpairl_cov_helper.{u} (Δ' := Δ'_alt) zs_nodup fv_pairl_sub_zs
          have hpairl_den_alt :=
            hpairl_den_helper.{u} (Δ' := Δ'_alt) zs_len zs_nodup zs_len_pos hpairl_cov_alt
          have hcov_appD_upd_alt :=
            hcov_appD_upd_helper.{u} hcov_D_upd_alt hpairl_cov_alt
          have hdenote_appD_upd_alt :=
            hdenote_appD_upd_helper.{u} (D_enc := D_enc) (Δ' := Δ'_alt) (denD' := denD_alt)
              (τ := τ) zs_len zs_len_pos τs_toProdl_eq denD_alt_type denD_alt_func
              hpairl_cov_alt hpairl_den_alt hcov_D_upd_alt den_D_upd_eq_alt hcov_appD_upd_alt
          -- Coverage of substList under zs-updates.
          have hcov_subst_upd_alt :=
            hcov_subst_upd_helper.{u} imp_body P_enc (vs := vs) zs_nodup (τs := τs)
              hcov_forall_alt
              (hv_to_imp := fun hv => by
                show _ ∈ SMT.fv (SMT.Term.imp _ _)
                exact SMT.fv.mem_imp (Or.inr hv))
          -- STEP 4: Extract h_den_P_alt_generic / h_den_P_alt_bool from hden_alt.
          have rest_alt := hden_alt
          simp only [B.Term.abstract] at rest_alt
          unfold B.denote at rest_alt
          simp only [Option.bind_eq_bind, hden_D_alt_eq, Option.bind_some] at rest_alt
          rw [dif_pos τ_hasArity] at rest_alt
          by_cases h_den_P_alt_cond : (∀ {x : Fin vs.length → B.Dom},
              (∀ i, (x i).snd.fst = τ.get vs.length i ∧
                    (x i).fst ∈ ⟦τ.get vs.length i⟧ᶻ) →
              ZFSet.ofFinDom x ∈ 𝒟_alt →
              ⟦(B.Term.abstract.go P vs Δ_alt
                (fun v hv hvs => Δ_fv_alt v
                  (B.fv.mem_all (.inr ⟨hv, hvs⟩)))).uncurry x⟧ᴮ.isSome)
          · have h_den_P_alt_generic : ∀ {x_fin : Fin vs.length → B.Dom},
                (∀ i, (x_fin i).snd.fst = τ.get vs.length i ∧
                      (x_fin i).fst ∈ ⟦τ.get vs.length i⟧ᶻ) →
                ZFSet.ofFinDom x_fin ∈ 𝒟_alt →
                ⟦(B.Term.abstract.go P vs Δ_alt
                  (fun v hv hvs => Δ_fv_alt v
                    (B.fv.mem_all (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ.isSome = true := by
              intro x_fin hx_typ hx_fin_in; exact h_den_P_alt_cond hx_typ hx_fin_in
            have h_den_P_alt_bool : ∀ {x_fin : Fin vs.length → B.Dom},
                (∀ i, (x_fin i).snd.fst = τ.get vs.length i ∧
                      (x_fin i).fst ∈ ⟦τ.get vs.length i⟧ᶻ) →
                ZFSet.ofFinDom x_fin ∈ 𝒟_alt →
                ∀ (Pz : ZFSet.{u}) (P_ty : BType) (hP_val : Pz ∈ ⟦P_ty⟧ᶻ),
                ⟦(B.Term.abstract.go P vs Δ_alt
                  (fun v hv hvs => Δ_fv_alt v
                    (B.fv.mem_all (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ =
                    some ⟨Pz, ⟨P_ty, hP_val⟩⟩ →
                P_ty = .bool :=
              h_den_P_alt_bool_helper.{u} (D := D) (τ := τ) (𝒟_alt := 𝒟_alt)
                vs_nodup vs_nemp typP (Δ_alt := Δ_alt) Δ_fv_alt
            -- STEP 5: hsubst_spec_alt (mirror of hsubst_spec at alt).
            -- Factored into `hsubst_spec_helper` reused with `Δ'_alt` substituted
            -- for `Δ'`. The two outside-vs hypotheses peel through the
            -- Δ₀_alt → Δ_D_alt → Δ' → Δ_P chain.
            have hsubst_spec_alt :=
              hsubst_spec_helper.{u}
                (vs := vs) (zs := zs) (τs := τs)
                (Δ' := Δ'_alt) (P_enc := P_enc) (St₄types := St₄.types)
                vs_nodup zs_nodup vs_zs_len vs_τs_len zs_len
                (Δ'_outside_vs_isSome := fun v hvvs hv => by
                  show (match Δ₀_alt v with
                    | some d => some d
                    | none => match Δ_D_alt v with
                      | some d => some d
                      | none => Δ' v).isSome = true
                  cases h_alt : Δ₀_alt v with
                  | some d => simp
                  | none =>
                    cases h_D_alt : Δ_D_alt v with
                    | some d => simp
                    | none =>
                      simp only [Option.isSome]
                      rw [Δ'_def]
                      simp only [hvvs, if_false]
                      exact Δ_P_covers v hv)
                (Δ'_outside_vs_wt := fun v hvvs d hd τ_v hlookup => by
                  -- Promote St₄ lookup to St₈ lookup (uses v ∉ vs and v ∉ zs).
                  have hv_St₄ : v ∈ St₄.types := AList.lookup_isSome.mp
                    (by rw [hlookup]; simp)
                  have hvzs : v ∉ zs := fun hvzs' => zs_not_types v hvzs' hv_St₄
                  have hv_St₅_entry : ⟨v, τ_v⟩ ∈ St₅.types.entries :=
                    AList.mem_lookup_iff.mp
                      (AList.lookup_of_subset St₄_sub_St₅_types hlookup)
                  have hv_St₇_entry : ⟨v, τ_v⟩ ∈ St₇.types.entries := by
                    rw [St₇_types]
                    exact AList.mem_foldl_erase_of_not_mem_keys hv_St₅_entry hvvs
                  have hv_St₈_entry : ⟨v, τ_v⟩ ∈ St₈.types.entries := by
                    rw [St₈_types]
                    exact AList.mem_foldl_erase_of_not_mem_keys hv_St₇_entry hvzs
                  have hτ_v_St₈ : St₈.types.lookup v = some τ_v :=
                    AList.mem_lookup_iff.2 hv_St₈_entry
                  exact Δ'_alt_wt v d hd τ_v hτ_v_St₈)
                (vs_sub_St₄_types :=
                  vs_sub_types_helper vs_nodup vs_τs_len St₃_types St₃_sub_St₄_types)
                (vs_typing_St₄ := fun i hi => by
                  have h_St₃_lookup : St₃.types.lookup vs[i] =
                      some (τs[i]'(vs_τs_len ▸ hi)) := by
                    rw [St₃_types]
                    exact foldl_insert_lookup_zip vs_nodup hi (vs_τs_len ▸ hi)
                  exact AList.lookup_of_subset St₃_sub_St₄_types h_St₃_lookup)
                (zs_not_bv_P :=
                  zs_not_bv_P_helper zs_len St₄_sub_St₅_types typ_P_enc zs_typing)
                (zs_not_St₄_types := zs_not_types)
                typ_P_enc hcov_subst_upd_alt
            -- STEP 6: himp_total_alt and himp_ty_alt.
            obtain ⟨himp_total_alt, himp_ty_alt⟩ :=
              himp_total_ty_bundle.{u} zs_len imp_body_def hcov_imp_upd_alt
                (happD_bool := fun w hw => by
                  obtain ⟨_, Dapp, hDapp_ty, _, hDapp_den⟩ := hdenote_appD_upd_alt w hw
                  exact ⟨Dapp, hDapp_ty, hDapp_den⟩)
                hsubst_spec_alt
            -- STEP 7: forallVal_alt construction.
            have htot_forall_raw_alt :
                ∀ {x : Fin zs.length → SMT.Dom.{u}},
                (∀ i, (x i).snd.fst = τs[i.val]'(zs_len ▸ i.isLt) ∧
                  (x i).fst ∈ ⟦τs[i.val]'(zs_len ▸ i.isLt)⟧ᶻ) →
                ⟦(SMT.Term.abstract.go imp_body zs Δ'_alt hgo_cov_alt).uncurry
                    x⟧ˢ.isSome = true :=
              htot_forall_raw_helper.{u} (zs := zs) (τs := τs) zs_len
                (Δ_ctx := Δ'_alt) (hgo_cov := hgo_cov_alt) himp_total_alt
            have forallVal_alt_isSome :=
              forallVal_isSome_helper.{u} zs_len zs_len_pos
                hcov_forall_alt htot_forall_raw_alt
            obtain ⟨forallVal_alt, hforallVal_alt⟩ :=
              Option.isSome_iff_exists.mp forallVal_alt_isSome
            have hforallVal_alt_ty : forallVal_alt.snd.fst = .bool :=
              hforallVal_ty_helper.{u} zs_len zs_len_pos
                htot_forall_raw_alt hforallVal_alt
            -- STEP 8: hbridge_alt — heavy semantic bridge.
            -- Mirrors `hbridge` at Δ'_alt with 𝒟_alt/h_den_P_alt-aware
            -- ZFFALSE/ZFTRUE branches.
            have hbridge_alt :
                ∀ (x : ZFSet.{u}) (hx_mem : x ∈ ⟦τ.toSMTType⟧ᶻ),
                let x_B := retract τ x
                let hx_B_mem : x_B ∈ ⟦τ⟧ᶻ := retract_mem_of_canonical τ hx_mem
                let x_fin : Fin vs.length → B.Dom := fun i =>
                  ⟨x_B.get vs.length i, ⟨τ.get vs.length i,
                    get_mem_type_of_isTuple
                      (hasArity_of_mem_toZFSet τ_hasArity hx_B_mem)
                      τ_hasArity hx_B_mem⟩⟩
                ∀ (w : Fin zs.length → SMT.Dom)
                  (_hw : ∀ i, (w i).snd.fst = τs[i]'(zs_len ▸ i.isLt) ∧
                    (w i).fst ∈ ⟦τs[i]'(zs_len ▸ i.isLt)⟧ᶻ)
                  (_hw_smt : Fin.foldl (zs.length - 1)
                    (fun acc i =>
                      acc.pair (w ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩).fst)
                    (w ⟨0, zs_len_pos⟩).fst = x)
                  (body_val : SMT.Dom),
                  ⟦imp_body.abstract
                    (Function.updates Δ'_alt zs
                      (List.ofFn (fun i => some (w i))))
                    (hcov_imp_upd_alt w)⟧ˢ = some body_val →
                  (body_val.fst = zftrue ↔
                    (x_B ∉ 𝒟_alt ∨
                     ∀ (Px : ZFSet.{u}) (P_ty : BType)
                       (hP_val : Px ∈ ⟦P_ty⟧ᶻ),
                       ⟦(B.Term.abstract.go P vs Δ_alt (fun v hv hvs =>
                         Δ_fv_alt v
                           (B.fv.mem_all (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ =
                         some ⟨Px, ⟨P_ty, hP_val⟩⟩ → Px = zftrue)) := by
              intro x hx_mem
              simp only []
              intro w hw hw_smt body_val hbody_val
              set x_B : ZFSet.{u} := retract τ x with x_B_def
              have hx_B_mem : x_B ∈ ⟦τ⟧ᶻ := retract_mem_of_canonical τ hx_mem
              obtain ⟨hx_mem_smt, Dapp, hDapp_ty, hDapp_val, hDapp_den⟩ :=
                hdenote_appD_upd_alt w hw
              obtain ⟨Dsubst, hDsubst_den, hDsubst_ty⟩ := hsubst_spec_alt w hw
              obtain ⟨Dimp, hDimp, hDimp_ty⟩ :=
                _root_.denote_imp_some_bool.{u} hDapp_den hDapp_ty hDsubst_den hDsubst_ty
              have hBody_eq_Dimp : ⟦imp_body.abstract
                  (Function.updates Δ'_alt zs (List.ofFn (fun i => some (w i))))
                  (hcov_imp_upd_alt w)⟧ˢ = some Dimp := by
                convert hDimp using 3
                all_goals
                  first
                  | rfl
                  | (simp only [imp_body_def, SMT.Term.abstract])
              have hbody_eq_Dimp : body_val = Dimp :=
                Option.some.inj (hbody_val.symm.trans hBody_eq_Dimp)
              have hDapp_mem_𝔹 : Dapp.fst ∈ 𝔹 := by
                have := Dapp.snd.snd; rwa [hDapp_ty] at this
              have hDapp_val_x : Dapp.fst = @ᶻdenD_alt.fst ⟨x,
                  by rw [ZFSet.is_func_dom_eq denD_alt_func]; exact hx_mem⟩ := by
                rw [hDapp_val]
                have hsub : (⟨Fin.foldl (zs.length - 1)
                    (fun acc i => acc.pair (w ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩).fst)
                    (w ⟨0, zs_len_pos⟩).fst,
                    by rw [ZFSet.is_func_dom_eq denD_alt_func]; exact hx_mem_smt⟩
                    : {z // z ∈ denD_alt.fst.Dom}) =
                    ⟨x, by rw [ZFSet.is_func_dom_eq denD_alt_func]; exact hx_mem⟩ := by
                  apply Subtype.ext; exact hw_smt
                rw [hsub]
              have hRetr_denD_alt : retract (BType.set τ) denD_alt.fst = 𝒟_alt :=
                denD_alt_retract
              have hx_B_𝒟_iff : x_B ∈ 𝒟_alt ↔ Dapp.fst = zftrue := by
                rw [hDapp_val_x]
                have hcan : ZFSet.fapply (BType.canonicalIsoSMTType τ).1
                    (is_func_is_pfunc (BType.canonicalIsoSMTType τ).2.1)
                    ⟨x_B, ZFSet.mem_dom (is_func_is_pfunc
                      (BType.canonicalIsoSMTType τ).2.1)
                      (canonical_pair_of_retract τ hx_mem)⟩ = x :=
                  canonical_of_retract τ hx_mem
                have hsub_x : (⟨x,
                    by rw [ZFSet.is_func_dom_eq denD_alt_func]; exact hx_mem⟩
                    : {z // z ∈ denD_alt.fst.Dom}) =
                    ⟨ZFSet.fapply (BType.canonicalIsoSMTType τ).1
                      (is_func_is_pfunc (BType.canonicalIsoSMTType τ).2.1)
                      ⟨x_B, ZFSet.mem_dom (is_func_is_pfunc
                        (BType.canonicalIsoSMTType τ).2.1)
                        (canonical_pair_of_retract τ hx_mem)⟩,
                      by rw [ZFSet.is_func_dom_eq denD_alt_func]
                         exact fapply_mem_range _ _⟩ := by
                  apply Subtype.ext; exact hcan.symm
                rw [hsub_x]
                rw [← hRetr_denD_alt]
                rw [retract, mem_sep]
                constructor
                · rintro ⟨hx_B_α, hmem⟩
                  rw [dif_pos hx_B_α, dif_pos denD_alt_func] at hmem
                  simpa using hmem
                · intro hfapp
                  refine ⟨hx_B_mem, ?_⟩
                  rw [dif_pos hx_B_mem, dif_pos denD_alt_func]
                  simpa using hfapp
              rcases (ZFSet.ZFBool.mem_𝔹_iff _).mp hDapp_mem_𝔹 with hDapp_false | hDapp_true
              · -- ZFFALSE case: body_val.fst = zftrue (vacuously), x_B ∉ 𝒟_alt.
                have hDimp_eq : ⟦((@ˢD_enc) (List.map SMT.Term.var zs).toPairl
                    ⇒ˢ SMT.substList vs (List.map SMT.Term.var zs) P_enc).abstract
                    (Function.updates Δ'_alt zs (List.ofFn (fun i => some (w i))))
                    (by simpa [imp_body_def] using hcov_imp_upd_alt w)⟧ˢ =
                    some ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
                  have := denote_imp_eq_zftrue_of_zffalse_left.{u}
                    hDapp_den hDapp_ty hDapp_false hDsubst_den hDsubst_ty
                  convert this using 3
                  all_goals first | rfl | (simp only [SMT.Term.abstract])
                have hbody_is_true_dom : body_val = ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
                  have hDimp_eq' : ⟦imp_body.abstract
                      (Function.updates Δ'_alt zs (List.ofFn (fun i => some (w i))))
                      (hcov_imp_upd_alt w)⟧ˢ = some ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
                    convert hDimp_eq using 3
                  exact Option.some.inj (hbody_val.symm.trans hDimp_eq')
                have hbody_fst_true : body_val.fst = zftrue := by
                  rw [hbody_is_true_dom]
                have hx_B_not_𝒟 : x_B ∉ 𝒟_alt := by
                  intro hcon
                  have : Dapp.fst = zftrue := hx_B_𝒟_iff.mp hcon
                  rw [this] at hDapp_false
                  exact ZFSet.zftrue_ne_zffalse hDapp_false
                constructor
                · intro _; exact Or.inl hx_B_not_𝒟
                · intro _; exact hbody_fst_true
              · -- ZFTRUE CASE: x_B ∈ 𝒟_alt, so body_val.fst = Dsubst.fst = P_val.
                have hx_B_in_𝒟 : x_B ∈ 𝒟_alt := hx_B_𝒟_iff.mpr hDapp_true
                have hx_B_arity : x_B.hasArity vs.length :=
                  hasArity_of_mem_toZFSet τ_hasArity hx_B_mem
                have hx_arity : x.hasArity zs.length := by
                  rw [← vs_zs_len]
                  exact hasArity_of_mem_toSMTZFSet τ_hasArity hx_mem
                let x_fin : Fin vs.length → B.Dom := fun i =>
                  ⟨x_B.get vs.length i, τ.get vs.length i,
                    get_mem_type_of_isTuple hx_B_arity τ_hasArity hx_B_mem⟩
                set Δ_ext_x_alt : B.RenamingContext.Context :=
                  Function.updates Δ_alt vs (List.ofFn fun i => some (x_fin i))
                  with Δ_ext_x_alt_def
                have Δ_fv_P_x : ∀ v ∈ B.fv P, (Δ_ext_x_alt v).isSome = true := by
                  intro v hv
                  rw [Δ_ext_x_alt_def, Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup]
                  split_ifs with hvs
                  · simp [List.getElem_ofFn]
                  · exact Δ_fv_alt v (B.fv.mem_all (.inr ⟨hv, hvs⟩))
                have h_ofFinDom_eq_x : ZFSet.ofFinDom x_fin = x_B :=
                  ZFSet.ofFinDom_get (List.length_pos_iff.mpr vs_nemp)
                    (fun i => get_mem_type_of_isTuple hx_B_arity τ_hasArity hx_B_mem)
                    hx_B_arity τ_hasArity
                have hx_fin_in_𝒟 : ZFSet.ofFinDom x_fin ∈ 𝒟_alt := h_ofFinDom_eq_x ▸ hx_B_in_𝒟
                have hx_fin_typ : ∀ i, (x_fin i).snd.fst = τ.get vs.length i ∧
                    (x_fin i).fst ∈ ⟦τ.get vs.length i⟧ᶻ :=
                  fun i => ⟨rfl, (x_fin i).snd.snd⟩
                have hP_isSome_x := h_den_P_alt_generic hx_fin_typ hx_fin_in_𝒟
                obtain ⟨⟨P_val, P_ty_raw, hP_val_raw⟩, hP_den_x_raw⟩ :=
                  Option.isSome_iff_exists.mp hP_isSome_x
                have hP_ty_bool : P_ty_raw = BType.bool :=
                  h_den_P_alt_bool hx_fin_typ hx_fin_in_𝒟 P_val P_ty_raw hP_val_raw hP_den_x_raw
                subst hP_ty_bool
                have h_den_P_x : ⟦P.abstract Δ_ext_x_alt Δ_fv_P_x⟧ᴮ =
                    some ⟨P_val, ⟨BType.bool, hP_val_raw⟩⟩ := by
                  rw [← denote_term_abstract_go_eq_term_abstract vs_nodup vs_nemp x_fin Δ_fv_P_x]
                  exact hP_den_x_raw
                have hw_fst_eq : ∀ i : Fin zs.length, (w i).fst = x.get zs.length i := by
                  exact foldl_pair_inj_get zs_len_pos hx_arity (fun i => (w i).fst) hw_smt
                have hτs_i : ∀ (i : Fin zs.length),
                    τs[i.val]'(zs_len ▸ i.isLt) =
                      (τ.get vs.length ⟨i.val, by rw [vs_zs_len]; exact i.isLt⟩).toSMTType := by
                  intro i
                  have hvi_lt : i.val < vs.length := by rw [vs_zs_len]; exact i.isLt
                  have heq := toSMTType_get_eq_fromProdl_getElem τ_hasArity hvi_lt
                  rw [heq]
                  simp [τs_eq]
                set Δ_D_ext_x_alt : SMT.RenamingContext.Context :=
                  Function.updates Δ_D_alt vs
                    (List.ofFn fun (i : Fin vs.length) => B.RenamingContext.toSMT Δ_ext_x_alt vs[i])
                  with Δ_D_ext_x_alt_def
                set Δ₀_hybrid_x_alt : SMT.RenamingContext.Context := fun v =>
                  if v ∈ vs then Δ_D_ext_x_alt v
                  else if v ∈ St₄.env.usedVars then Δ'_alt v
                  else none
                  with Δ₀_hybrid_x_alt_def
                have vs_sub_St₄_used : ∀ v ∈ vs, v ∈ St₄.env.usedVars := fun v hv =>
                  St₃_sub_St₄ (vs_sub_St₃_used v hv)
                have Δ₀_hybrid_ext_P_x :
                    RenamingContext.ExtendsOnSourceFV Δ₀_hybrid_x_alt Δ_ext_x_alt P := by
                  intro v d hv_eq
                  by_cases hv_fv : v ∈ B.fv P
                  · have hv_smt : B.RenamingContext.toSMT Δ_ext_x_alt v = some d := by
                      have heq : B.RenamingContext.toSMTOnFV Δ_ext_x_alt P v =
                          B.RenamingContext.toSMT Δ_ext_x_alt v := by
                        simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                          B.RenamingContext.restrictToFV_eq_of_mem hv_fv]
                      rwa [← heq]
                    by_cases hvs : v ∈ vs
                    · show (if v ∈ vs then Δ_D_ext_x_alt v else _) = some d
                      rw [if_pos hvs]
                      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hvs
                      rw [Δ_D_ext_x_alt_def]
                      rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup,
                          dif_pos (List.getElem_mem hi)]
                      simp only [List.getElem_ofFn, Fin.getElem_fin, List.getElem_idxOf]
                      exact hv_smt
                    · have hv_St₄_used : v ∈ St₄.env.usedVars := covers_P v hv_fv
                      show (if v ∈ vs then _ else if v ∈ St₄.env.usedVars then Δ'_alt v else none) = some d
                      rw [if_neg hvs, if_pos hv_St₄_used]
                      have hΔ_ext_x_alt_eq : Δ_ext_x_alt v = Δ_alt v := by
                        rw [Δ_ext_x_alt_def]
                        exact Function.updates_of_not_mem Δ_alt vs _ v hvs
                      have hv_smt_Δ_alt : B.RenamingContext.toSMT Δ_alt v = some d := by
                        rw [B.RenamingContext.toSMT, ← hΔ_ext_x_alt_eq,
                            ← B.RenamingContext.toSMT]
                        exact hv_smt
                      have hv_fv_all : v ∈ B.fv (Term.all vs D P) :=
                        B.fv.mem_all (.inr ⟨hv_fv, hvs⟩)
                      have h_onFV_all : B.RenamingContext.toSMTOnFV Δ_alt
                          (Term.all vs D P) v = some d := by
                        simp only [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                          B.RenamingContext.restrictToFV_eq_of_mem hv_fv_all]
                        rw [B.RenamingContext.toSMT, Option.pure_def,
                          Option.bind_eq_bind] at hv_smt_Δ_alt
                        exact hv_smt_Δ_alt
                      have hΔ₀_alt_v : Δ₀_alt v = some d := hext_alt h_onFV_all
                      show Δ'_alt v = some d
                      rw [Δ'_alt_def]
                      simp only [hΔ₀_alt_v]
                  · have : B.RenamingContext.toSMTOnFV Δ_ext_x_alt P v = none := by
                      simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                        B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_fv]
                    rw [this] at hv_eq
                    exact absurd hv_eq (by simp)
                have Δ₀_hybrid_x_alt_none : ∀ v ∉ St₄.env.usedVars, Δ₀_hybrid_x_alt v = none := by
                  intro v hv
                  show (if v ∈ vs then Δ_D_ext_x_alt v else _) = none
                  have hv_not_vs : v ∉ vs := fun hvs => hv (vs_sub_St₄_used v hvs)
                  rw [if_neg hv_not_vs, if_neg hv]
                have Δ₀_hybrid_x_alt_wt :
                    ∀ (v : SMT.𝒱) (d : SMT.Dom), Δ₀_hybrid_x_alt v = some d →
                    ∀ τ_v, St₄.types.lookup v = some τ_v → d.snd.fst = τ_v := by
                  intro v d hv τ_v hlookup
                  by_cases hvs : v ∈ vs
                  · have hv_hybrid : Δ₀_hybrid_x_alt v = Δ_D_ext_x_alt v := by
                      show (if v ∈ vs then Δ_D_ext_x_alt v else _) = Δ_D_ext_x_alt v
                      rw [if_pos hvs]
                    rw [hv_hybrid] at hv
                    obtain ⟨i, hi, hvi_eq⟩ := List.mem_iff_getElem.mp hvs
                    subst hvi_eq
                    rw [Δ_D_ext_x_alt_def, Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup,
                      dif_pos (List.getElem_mem hi)] at hv
                    simp only [List.getElem_ofFn, Fin.getElem_fin, List.getElem_idxOf] at hv
                    have hΔ_ext_x_alt_vi : Δ_ext_x_alt vs[i] = some (x_fin ⟨i, hi⟩) := by
                      show Function.updates Δ_alt vs _ vs[i] = _
                      rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup,
                        dif_pos (List.getElem_mem hi)]
                      simp only [List.getElem_ofFn]
                      simp [List.idxOf_getElem vs_nodup]
                    have vs_typing_St₃ : St₃.types.lookup vs[i] = some (τs[i]'(vs_τs_len ▸ hi)) := by
                      rw [St₃_types]
                      exact foldl_insert_lookup_zip vs_nodup hi (vs_τs_len ▸ hi)
                    have vs_typing_St₄ : St₄.types.lookup vs[i] = some (τs[i]'(vs_τs_len ▸ hi)) :=
                      AList.lookup_of_subset St₃_sub_St₄_types vs_typing_St₃
                    rw [vs_typing_St₄] at hlookup
                    cases hlookup
                    simp only [B.RenamingContext.toSMT, hΔ_ext_x_alt_vi, Option.pure_def,
                      Option.bind_eq_bind, Option.bind_some] at hv
                    have hd_eq := Option.some.inj hv
                    rw [← hd_eq]
                    show (τ.get vs.length ⟨i, hi⟩).toSMTType = τs[i]
                    have := hτs_i ⟨i, zs_len ▸ vs_τs_len ▸ hi⟩
                    simp only at this
                    exact this.symm
                  · have hv_St₄ : v ∈ St₄.types := AList.lookup_isSome.mp (by rw [hlookup]; simp)
                    have hv_St₄_used : v ∈ St₄.env.usedVars := St₄_keys_sub hv_St₄
                    have hv_hybrid : Δ₀_hybrid_x_alt v = Δ'_alt v := by
                      show (if v ∈ vs then _ else if v ∈ St₄.env.usedVars then Δ'_alt v else none) = Δ'_alt v
                      rw [if_neg hvs, if_pos hv_St₄_used]
                    rw [hv_hybrid] at hv
                    have hv_not_zs : v ∉ zs := fun hvz => zs_not_types v hvz hv_St₄
                    have hv_St₅_entry : ⟨v, τ_v⟩ ∈ St₅.types.entries :=
                      AList.mem_lookup_iff.mp (AList.lookup_of_subset St₄_sub_St₅_types hlookup)
                    have hv_St₇_entry : ⟨v, τ_v⟩ ∈ St₇.types.entries := by
                      rw [St₇_types]
                      exact AList.mem_foldl_erase_of_not_mem_keys hv_St₅_entry hvs
                    have hv_St₈_entry : ⟨v, τ_v⟩ ∈ St₈.types.entries := by
                      rw [St₈_types]
                      exact AList.mem_foldl_erase_of_not_mem_keys hv_St₇_entry hv_not_zs
                    have hτ_v_St₈ : St₈.types.lookup v = some τ_v :=
                      AList.mem_lookup_iff.2 hv_St₈_entry
                    exact Δ'_alt_wt v d hv τ_v hτ_v_St₈
                obtain ⟨Δ_P_x, hcov_Px, denT_x', Δ_P_x_extends, Δ_P_x_none, Δ_P_x_wt,
                    hden_Px, hRDom_x, Δ_P_x_dom⟩ :=
                  P_enc_total Δ_ext_x_alt Δ_fv_P_x Δ₀_hybrid_x_alt Δ₀_hybrid_ext_P_x
                    Δ₀_hybrid_x_alt_none Δ₀_hybrid_x_alt_wt P_val hP_val_raw h_den_P_x
                have hdenT_x'_ty : denT_x'.snd.fst = BType.bool.toSMTType := hRDom_x.1
                have hdenT_x'_fst_eq : denT_x'.fst = P_val := by
                  have := hRDom_x.2
                  simp only [retract] at this
                  exact this
                set Δ'_upd : SMT.RenamingContext.Context :=
                  Function.updates Δ'_alt zs (List.ofFn (fun i : Fin zs.length => some (w i)))
                  with Δ'_upd_def
                set Δ_P_x_upd : SMT.RenamingContext.Context :=
                  Function.updates Δ_P_x zs (List.ofFn (fun i : Fin zs.length => some (w i)))
                  with Δ_P_x_upd_def
                have hΔ_upd_agree_substList :
                    SMT.RenamingContext.AgreesOnFV Δ'_upd Δ_P_x_upd
                      (SMT.substList vs (List.map SMT.Term.var zs) P_enc) := by
                  intro v hv
                  by_cases hvzs : v ∈ zs
                  · rw [Δ'_upd_def, Δ_P_x_upd_def]
                    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hvzs
                    rw [Function.updates_eq_if (by rw [List.length_ofFn]) zs_nodup,
                      dif_pos (List.getElem_mem hj)]
                    rw [Function.updates_eq_if (by rw [List.length_ofFn]) zs_nodup,
                      dif_pos (List.getElem_mem hj)]
                  · rw [Δ'_upd_def, Δ_P_x_upd_def]
                    rw [Function.updates_of_not_mem Δ'_alt zs _ v hvzs,
                      Function.updates_of_not_mem Δ_P_x zs _ v hvzs]
                    rcases SMT_mem_fv_substList hv with hv_P | ⟨t, ht, hv_t⟩
                    · have hv_St₄ : v ∈ St₄.types :=
                        SMT.Typing.mem_context_of_mem_fv typ_P_enc hv_P
                      have hv_St₄_used : v ∈ St₄.env.usedVars := St₄_keys_sub hv_St₄
                      by_cases hvvs : v ∈ vs
                      · exfalso
                        have hlen : vs.length ≤ (List.map SMT.Term.var zs).length := by
                          rw [List.length_map]; exact le_of_eq (zs_len ▸ vs_τs_len)
                        by_cases h_all_no_fv :
                            ∀ t ∈ List.map SMT.Term.var zs, v ∉ SMT.fv t
                        · exact SMT_not_mem_fv_substList_of_mem_vars hlen hvvs h_all_no_fv hv
                        · push_neg at h_all_no_fv
                          obtain ⟨t, ht, hv_t⟩ := h_all_no_fv
                          rw [List.mem_map] at ht
                          obtain ⟨z, hz, rfl⟩ := ht
                          simp only [SMT.fv, List.mem_singleton] at hv_t
                          subst hv_t
                          exact hvzs hz
                      · have hv_imp : v ∈ SMT.fv imp_body := by
                          show v ∈ SMT.fv (SMT.Term.imp _ _)
                          exact SMT.fv.mem_imp (Or.inr hv)
                        have hv_f : v ∈ SMT.fv (SMT.Term.forall zs τs imp_body) := by
                          simp only [SMT.fv, List.mem_removeAll_iff]
                          exact ⟨hv_imp, hvzs⟩
                        have hΔ'alt_isSome : (Δ'_alt v).isSome = true :=
                          hcov_forall_alt v hv_f
                        obtain ⟨d, hΔ'alt_v⟩ := Option.isSome_iff_exists.mp hΔ'alt_isSome
                        have hΔ₀_hyb_v : Δ₀_hybrid_x_alt v = some d := by
                          show (if v ∈ vs then _ else if v ∈ St₄.env.usedVars then Δ'_alt v else none) = some d
                          rw [if_neg hvvs, if_pos hv_St₄_used]
                          exact hΔ'alt_v
                        have hΔ_P_x_v : Δ_P_x v = Δ'_alt v := by
                          rw [Δ_P_x_extends hΔ₀_hyb_v, hΔ'alt_v]
                        rw [hΔ_P_x_v]
                    · rw [List.mem_map] at ht
                      obtain ⟨z, hz, rfl⟩ := ht
                      simp only [SMT.fv, List.mem_singleton] at hv_t
                      subst hv_t
                      exact absurd hz hvzs
                have hcov_substList_Px_upd : SMT.RenamingContext.CoversFV
                    Δ_P_x_upd (SMT.substList vs (List.map SMT.Term.var zs) P_enc) := by
                  intro v hv
                  have hag := hΔ_upd_agree_substList hv
                  have hcov_v := hcov_subst_upd_alt w v hv
                  show (Δ_P_x_upd v).isSome = true
                  rw [show Δ'_upd = Function.updates Δ'_alt zs
                    (List.ofFn (fun i : Fin zs.length => some (w i))) from rfl] at hag
                  rw [← hag]; exact hcov_v
                have hsubst_at_ΔPx : ⟦(SMT.substList vs (List.map SMT.Term.var zs) P_enc).abstract
                    Δ_P_x_upd hcov_substList_Px_upd⟧ˢ = some Dsubst := by
                  have h_transfer := SMT.RenamingContext.denote_congr_of_agreesOnFV
                    (h1 := hcov_subst_upd_alt w) (h2 := hcov_substList_Px_upd) hΔ_upd_agree_substList
                  unfold SMT.RenamingContext.denote at h_transfer
                  rw [← h_transfer]; exact hDsubst_den
                let Ds_x : List SMT.Dom := List.ofFn fun i : Fin vs.length =>
                  w ⟨i.val, by rw [← vs_zs_len]; exact i.isLt⟩
                have hlen_xt_x : vs.length = (List.map SMT.Term.var zs).length := by
                  rw [List.length_map]; exact vs_zs_len
                have hlen_xd_x : vs.length = Ds_x.length := by simp [Ds_x]
                have vs_not_bv_P : ∀ x_v ∈ vs, x_v ∉ SMT.bv P_enc := fun x_v hx_v hbv =>
                  SMT.Typing.bv_notMem_context typ_P_enc x_v hbv
                    (AList.mem_of_subset St₃_sub_St₄_types
                      (by
                        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx_v
                        rw [St₃_types]
                        exact AList.lookup_isSome.mp
                          (by rw [foldl_insert_lookup_zip vs_nodup hi (vs_τs_len ▸ hi)]; simp)))
                have hts_bv_nil_x : ∀ t ∈ List.map SMT.Term.var zs, SMT.bv t = [] := by
                  intro t ht
                  rw [List.mem_map] at ht; obtain ⟨z, _, rfl⟩ := ht; unfold SMT.bv; rfl
                have hts_fv_not_bv_x : ∀ t ∈ List.map SMT.Term.var zs,
                    ∀ w' ∈ SMT.fv t, w' ∉ SMT.bv P_enc := by
                  intro t ht v' hv'
                  rw [List.mem_map] at ht
                  obtain ⟨z', hz', rfl⟩ := ht
                  simp only [SMT.fv, List.mem_singleton] at hv'
                  subst hv'
                  intro hbv
                  have typ_P_enc_St₅ : St₅.types ⊢ˢ P_enc : .bool :=
                    SMT.Typing.weakening St₄_sub_St₅_types typ_P_enc
                  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz'
                  have hz_St₅ : zs[i] ∈ St₅.types :=
                    AList.lookup_isSome.mp (by rw [zs_typing i hi]; simp)
                  exact SMT.Typing.bv_notMem_context typ_P_enc_St₅ zs[i] hbv hz_St₅
                have hts_not_none_x : ∀ t ∈ List.map SMT.Term.var zs, t ≠ SMT.Term.none := by
                  intro t ht; rw [List.mem_map] at ht; obtain ⟨z, _, rfl⟩ := ht; intro h; cases h
                have hts_fv_disj_xs_x : ∀ t ∈ List.map SMT.Term.var zs,
                    ∀ v' ∈ SMT.fv t, v' ∉ vs := by
                  intro t ht v' hv' hvs
                  rw [List.mem_map] at ht
                  obtain ⟨z, hz, rfl⟩ := ht
                  simp only [SMT.fv, List.mem_singleton] at hv'
                  subst hv'
                  have hv_St₃ : v' ∈ St₃.types := by
                    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hvs
                    rw [St₃_types]
                    exact AList.lookup_isSome.mp <| by
                      rw [foldl_insert_lookup_zip vs_nodup hi (vs_τs_len ▸ hi)]; simp
                  have hv_St₄ : v' ∈ St₄.types := AList.mem_of_subset St₃_sub_St₄_types hv_St₃
                  exact zs_not_types v' hz hv_St₄
                have h_cov_upd_x : SMT.RenamingContext.CoversFV
                    (Function.updates Δ_P_x_upd vs (Ds_x.map Option.some)) P_enc := by
                  intro v hv
                  by_cases hvs : v ∈ vs
                  · rw [Function.updates_eq_if (by rw [List.length_map, List.length_ofFn]) vs_nodup,
                      dif_pos hvs]
                    simp
                  · rw [Function.updates_of_not_mem _ vs _ _ hvs]
                    by_cases hvzs : v ∈ zs
                    · rw [Δ_P_x_upd_def, Function.updates_eq_if (by rw [List.length_ofFn]) zs_nodup,
                        dif_pos hvzs]
                      simp
                    · rw [Δ_P_x_upd_def, Function.updates_of_not_mem _ zs _ _ hvzs]
                      exact hcov_Px v hv
                have h_eq_x := SMT.RenamingContext.abstract_substList_denote P_enc vs
                  (List.map SMT.Term.var zs) Ds_x hlen_xt_x hlen_xd_x vs_nodup
                  vs_not_bv_P hts_bv_nil_x hts_fv_not_bv_x hts_not_none_x hts_fv_disj_xs_x
                  (by
                    intro i hi_x hi_t hi_d
                    have hi_zs : i < zs.length := by rw [List.length_map] at hi_t; exact hi_t
                    rw [List.getElem_map]
                    have hlookup_zs : Δ_P_x_upd zs[i] = some (w ⟨i, hi_zs⟩) := by
                      rw [Δ_P_x_upd_def]
                      rw [Function.updates_eq_if (by rw [List.length_ofFn]) zs_nodup,
                        dif_pos (List.getElem_mem hi_zs)]
                      have hidx : zs.idxOf zs[i] = i := List.idxOf_getElem zs_nodup i hi_zs
                      simp only [List.getElem_ofFn]
                      refine congrArg some (congrArg w ?_)
                      apply Fin.ext
                      exact hidx
                    have hcov_ti : SMT.RenamingContext.CoversFV Δ_P_x_upd
                        (SMT.Term.var zs[i]) := by
                      intro v hv
                      simp only [SMT.fv, List.mem_singleton] at hv
                      subst hv
                      rw [hlookup_zs]; simp
                    refine ⟨hcov_ti, ?_⟩
                    have hDs_i : Ds_x[i] = w ⟨i, by rw [← vs_zs_len]; exact hi_x⟩ := by
                      show (List.ofFn _)[i] = _
                      rw [List.getElem_ofFn]
                    show SMT.denote ((SMT.Term.var zs[i]).abstract Δ_P_x_upd hcov_ti) = some Ds_x[i]
                    rw [SMT.Term.abstract]
                    show SMT.denote (PHOAS.Term.var ((Δ_P_x_upd zs[i]).get _)) = _
                    simp only [SMT.denote]
                    rw [hDs_i]
                    congr 1
                    have h_get_eq : (Δ_P_x_upd zs[i]).get (by rw [hlookup_zs]; simp) =
                        w ⟨i, hi_zs⟩ := Option.get_of_eq_some _ hlookup_zs
                    show (Δ_P_x_upd zs[i]).get _ = w ⟨i, _⟩
                    rw [show (Δ_P_x_upd zs[i]).get _ = w ⟨i, hi_zs⟩ from h_get_eq])
                  hcov_substList_Px_upd h_cov_upd_x
                have h_upd_agree_x : SMT.RenamingContext.AgreesOnFV
                    (Function.updates Δ_P_x_upd vs (Ds_x.map Option.some)) Δ_P_x P_enc := by
                  intro v hv
                  by_cases hvs : v ∈ vs
                  · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hvs
                    rw [Function.updates_eq_if
                      (by rw [List.length_map, List.length_ofFn]) vs_nodup,
                      dif_pos (List.getElem_mem hi)]
                    simp only [List.getElem_map, List.idxOf_getElem vs_nodup]
                    have hvi_mem : vs[i] ∈ vs := List.getElem_mem hi
                    have hΔ_ext_x_alt_vi : Δ_ext_x_alt vs[i] = some (x_fin ⟨i, hi⟩) := by
                      show Function.updates Δ_alt vs _ vs[i] = _
                      rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup,
                        dif_pos hvi_mem]
                      simp only [List.getElem_ofFn]
                      simp [List.idxOf_getElem vs_nodup]
                    set d_smt : SMT.Dom :=
                      ⟨ZFSet.fapply (BType.canonicalIsoSMTType (τ.get vs.length ⟨i, hi⟩)).1
                        (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType _).2.1)
                        ⟨(x_fin ⟨i, hi⟩).fst, by
                          rw [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType _).2.1]
                          exact (x_fin ⟨i, hi⟩).snd.snd⟩,
                       (τ.get vs.length ⟨i, hi⟩).toSMTType, ZFSet.fapply_mem_range _ _⟩
                      with d_smt_def
                    have htoSMT_vi : B.RenamingContext.toSMT Δ_ext_x_alt vs[i] = some d_smt := by
                      simp only [B.RenamingContext.toSMT, hΔ_ext_x_alt_vi, Option.pure_def,
                        Option.bind_eq_bind, Option.bind_some]
                      rfl
                    have hΔ_D_ext_x_alt_vi : Δ_D_ext_x_alt vs[i] = some d_smt := by
                      rw [Δ_D_ext_x_alt_def, Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup,
                        dif_pos hvi_mem]
                      simp only [List.getElem_ofFn, Fin.getElem_fin, List.getElem_idxOf]
                      exact htoSMT_vi
                    have hΔ₀_hybrid_vi : Δ₀_hybrid_x_alt vs[i] = some d_smt := by
                      show (if vs[i] ∈ vs then Δ_D_ext_x_alt vs[i] else _) = some d_smt
                      rw [if_pos hvi_mem]; exact hΔ_D_ext_x_alt_vi
                    have hΔ_P_x_vi : Δ_P_x vs[i] = some d_smt := Δ_P_x_extends hΔ₀_hybrid_vi
                    set i_zs : Fin zs.length := ⟨i, by rw [← vs_zs_len]; exact hi⟩
                    have hDs_i : Ds_x[i] = w i_zs := by
                      show (List.ofFn _)[i] = _
                      rw [List.getElem_ofFn]
                    rw [hDs_i, hΔ_P_x_vi]
                    congr 1
                    have hw_i_fst : (w i_zs).fst = x.get zs.length i_zs := hw_fst_eq i_zs
                    have hw_i_ty : (w i_zs).snd.fst = τs[i]'(zs_len ▸ i_zs.isLt) := (hw i_zs).1
                    have hw_i_mem : (w i_zs).fst ∈ ⟦τs[i]'(zs_len ▸ i_zs.isLt)⟧ᶻ := (hw i_zs).2
                    have hτs_match : τs[i]'(zs_len ▸ i_zs.isLt) =
                        (τ.get vs.length ⟨i, hi⟩).toSMTType := by
                      have hτs_z := hτs_i i_zs
                      exact hτs_z
                    have hd_smt_fst_eq :
                        d_smt.fst = ZFSet.fapply (BType.canonicalIsoSMTType (τ.get vs.length ⟨i, hi⟩)).1
                          (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType _).2.1)
                          ⟨x_B.get vs.length ⟨i, hi⟩, by
                            rw [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType _).2.1]
                            exact get_mem_type_of_isTuple hx_B_arity τ_hasArity hx_B_mem⟩ := by
                      rfl
                    have h_canonical_eq :
                        (ZFSet.fapply (BType.canonicalIsoSMTType (τ.get vs.length ⟨i, hi⟩)).1
                          (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType _).2.1)
                          ⟨x_B.get vs.length ⟨i, hi⟩, by
                            rw [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType _).2.1]
                            exact get_mem_type_of_isTuple hx_B_arity τ_hasArity hx_B_mem⟩).val =
                        x.get zs.length i_zs := by
                      set vi_fin : Fin vs.length := ⟨i, hi⟩
                      have h_Fin_cast : (Fin.cast vs_zs_len vi_fin) = i_zs := rfl
                      have hx_B_get : x_B.get vs.length vi_fin = (retract τ x).get vs.length vi_fin := by
                        rw [x_B_def]
                      have h_retract_comm : (retract τ x).get vs.length vi_fin =
                          retract (τ.get vs.length vi_fin) (x.get vs.length vi_fin) :=
                        retract_get_comm
                          (hasArity_of_mem_toSMTZFSet τ_hasArity hx_mem) τ_hasArity hx_mem
                      have hx_get_mem_v : x.get vs.length vi_fin ∈
                          ⟦(τ.get vs.length vi_fin).toSMTType⟧ᶻ :=
                        get_mem_toSMTZFSet
                          (hasArity_of_mem_toSMTZFSet τ_hasArity hx_mem)
                          τ_hasArity hx_mem
                      have hx_get_eq : x.get vs.length vi_fin = x.get zs.length i_zs := by
                        have : ∀ {n m : ℕ} (h : n = m) (hi₁ : i < n) (hi₂ : i < m),
                            x.get n ⟨i, hi₁⟩ = x.get m ⟨i, hi₂⟩ := by
                          intro n m h hi₁ hi₂; subst h; rfl
                        exact this vs_zs_len hi i_zs.isLt
                      have h_x_B_eq : x_B.get vs.length vi_fin =
                          retract (τ.get vs.length vi_fin) (x.get vs.length vi_fin) :=
                        hx_B_get.trans h_retract_comm
                      have h_xB_as_retract : x_B.get vs.length vi_fin =
                          retract (τ.get vs.length vi_fin) (x.get zs.length i_zs) := by
                        rw [hx_B_get, h_retract_comm, hx_get_eq]
                      have hx_get_zs_mem : x.get zs.length i_zs ∈
                          ⟦(τ.get vs.length vi_fin).toSMTType⟧ᶻ := hx_get_eq ▸ hx_get_mem_v
                      have hx_pair_mem :
                          ZFSet.pair (x_B.get vs.length vi_fin) (x.get zs.length i_zs) ∈
                          (BType.canonicalIsoSMTType (τ.get vs.length vi_fin)).1 := by
                        rw [h_xB_as_retract]
                        exact canonical_pair_of_retract _ hx_get_zs_mem
                      exact Subtype.ext_iff.mp <|
                        ZFSet.fapply.of_pair
                          (is_func_is_pfunc (BType.canonicalIsoSMTType _).2.1)
                          hx_pair_mem
                    have hd_smt_fst_eq_w : d_smt.fst = (w i_zs).fst := by
                      rw [hd_smt_fst_eq, h_canonical_eq, hw_i_fst]
                    have hd_smt_ty : d_smt.snd.fst = τs[i]'(zs_len ▸ i_zs.isLt) := by
                      rw [d_smt_def]
                      show (τ.get vs.length ⟨i, hi⟩).toSMTType = _
                      exact hτs_match.symm
                    apply SMT.RenamingContext.Dom_ext'
                    · exact hw_i_fst.trans (h_canonical_eq.symm.trans hd_smt_fst_eq.symm)
                    · exact hw_i_ty.trans hd_smt_ty.symm
                  · rw [Function.updates_of_not_mem _ vs _ _ hvs]
                    by_cases hvzs : v ∈ zs
                    · exfalso
                      have hv_St₄ : v ∈ St₄.types :=
                        SMT.Typing.mem_context_of_mem_fv typ_P_enc hv
                      exact zs_not_types v hvzs hv_St₄
                    · rw [Δ_P_x_upd_def, Function.updates_of_not_mem _ zs _ _ hvzs]
                have h_eq2_x := SMT.RenamingContext.denote_congr_of_agreesOnFV
                  (h1 := h_cov_upd_x) (h2 := hcov_Px) h_upd_agree_x
                unfold SMT.RenamingContext.denote at h_eq2_x
                rw [h_eq_x, h_eq2_x, hden_Px] at hsubst_at_ΔPx
                have hDsubst_eq_denT : Dsubst = denT_x' :=
                  Option.some.inj hsubst_at_ΔPx.symm
                have hbody_fst_eq_P_val : body_val.fst = P_val := by
                  rw [hbody_eq_Dimp]
                  have hDsubst_mem_𝔹 : Dsubst.fst ∈ 𝔹 := by
                    have := Dsubst.snd.snd; rwa [hDsubst_ty] at this
                  rcases (ZFSet.ZFBool.mem_𝔹_iff _).mp hDsubst_mem_𝔹 with hDsubst_false | hDsubst_true
                  · have hDsubst_fst_eq : Dsubst.fst = denT_x'.fst := by rw [hDsubst_eq_denT]
                    have hDenT_fst : denT_x'.fst = zffalse := hDsubst_fst_eq ▸ hDsubst_false
                    have hP_val_eq : P_val = zffalse := hdenT_x'_fst_eq ▸ hDenT_fst
                    have hDimp_fst_eq_zffalse : Dimp.fst = zffalse := by
                      have hp := hDapp_den
                      have hq := hDsubst_den
                      have : ⟦((@ˢD_enc) (List.map SMT.Term.var zs).toPairl).abstract
                          (Function.updates Δ'_alt zs (List.ofFn (fun i => some (w i)))) (hcov_appD_upd_alt w) ⇒ˢ'
                          (SMT.substList vs (List.map SMT.Term.var zs) P_enc).abstract
                            (Function.updates Δ'_alt zs (List.ofFn (fun i => some (w i)))) (hcov_subst_upd_alt w)⟧ˢ =
                          some ⟨zffalse, .bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
                        have hDnq := denote_not_eq_zftrue_of_some_zffalse hq hDsubst_ty hDsubst_false
                        have hDand := denote_and_eq_zftrue_of_some_zftrue hp hDapp_ty hDapp_true
                          hDnq rfl rfl
                        exact denote_not_eq_zffalse_of_some_zftrue hDand rfl rfl
                      have := Option.some.inj (this.symm.trans hDimp)
                      have := congrArg (·.fst) this.symm; dsimp at this; exact this
                    rw [hDimp_fst_eq_zffalse, hP_val_eq]
                  · have hDsubst_fst_eq : Dsubst.fst = denT_x'.fst := by rw [hDsubst_eq_denT]
                    have hDenT_fst : denT_x'.fst = zftrue := hDsubst_fst_eq ▸ hDsubst_true
                    have hP_val_eq : P_val = zftrue := hdenT_x'_fst_eq ▸ hDenT_fst
                    have hDimp_fst_eq_zftrue : Dimp.fst = zftrue := by
                      have hp := hDapp_den
                      have hq := hDsubst_den
                      have : ⟦((@ˢD_enc) (List.map SMT.Term.var zs).toPairl).abstract
                          (Function.updates Δ'_alt zs (List.ofFn (fun i => some (w i)))) (hcov_appD_upd_alt w) ⇒ˢ'
                          (SMT.substList vs (List.map SMT.Term.var zs) P_enc).abstract
                            (Function.updates Δ'_alt zs (List.ofFn (fun i => some (w i)))) (hcov_subst_upd_alt w)⟧ˢ =
                          some ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ :=
                        denote_imp_eq_zftrue_of_both_zftrue.{u} hp hDapp_ty hDapp_true
                          hq hDsubst_ty hDsubst_true
                      have := Option.some.inj (this.symm.trans hDimp)
                      have := congrArg (·.fst) this.symm; dsimp at this; exact this
                    rw [hDimp_fst_eq_zftrue, hP_val_eq]
                constructor
                · intro hbody_fst
                  right
                  intro Px τPx hPx hPx_den
                  have hPx_den' := hPx_den
                  rw [hP_den_x_raw] at hPx_den'
                  have hinj := congrArg PSigma.fst (Option.some.inj hPx_den')
                  dsimp at hinj
                  rw [← hinj, ← hbody_fst_eq_P_val]
                  exact hbody_fst
                · intro hor
                  rcases hor with hx_B_not_𝒟 | hall
                  · exact absurd hx_B_in_𝒟 hx_B_not_𝒟
                  · have hPval_true : P_val = zftrue :=
                      hall P_val BType.bool hP_val_raw hP_den_x_raw
                    rw [hbody_fst_eq_P_val]
                    exact hPval_true
            -- STEP 9: Apply bridge by case-splitting on rest_alt's three dites.
            refine ⟨forallVal_alt, hforallVal_alt, ?_, ?_⟩
            · exact hforallVal_alt_ty
            · -- Goal: retract .bool forallVal_alt.fst = T_alt.
              split_ifs at rest_alt with h1 h2 h3
              · -- h1, h2, h3 (𝒟_alt = ∅): apply empty-domain bridge.
                simp only [Option.pure_def, Option.some.injEq, PSigma.mk.injEq]
                  at rest_alt
                obtain ⟨hT_eq_raw_alt, _⟩ := rest_alt
                rw [← hT_eq_raw_alt]
                classical
                exact _root_.retract_forallVal_eq_zftrue_of_empty_𝒟 (vs := vs) vs_nemp
                  (τ := τ) τ_hasArity
                  (D := D) (D_enc := D_enc)
                  (P_enc_subst := SMT.substList vs (List.map SMT.Term.var zs) P_enc)
                  (zs := zs) (τs := τs) zs_nemp zs_len τs_toProdl_eq
                  (imp_body := imp_body) imp_body_def
                  (Δ_ctx := Δ'_alt) hcov_forall_alt hforallVal_alt
                  hgo_cov_alt hcov_imp_upd_alt himp_total_alt
                  (𝒟_val := 𝒟_alt) h3
                  (P := P) («Δ» := Δ_alt) Δ_fv_alt
                  (zs_len_pos_hyp := zs_len_pos) (vs_zs_len := vs_zs_len)
                  (hbridge := hbridge_alt)
              · -- h1, h2, h3 (¬𝒟_alt = ∅): apply retract_forallVal_eq_sInter_sep.
                simp only [Option.pure_def, Option.some.injEq, PSigma.mk.injEq]
                  at rest_alt
                obtain ⟨hT_eq_raw_alt, _⟩ := rest_alt
                have 𝒟_alt_nonempty : 𝒟_alt.Nonempty :=
                  𝒟_alt.eq_empty_or_nonempty.resolve_left h3
                classical
                show retract BType.bool forallVal_alt.fst = T_alt
                apply retract_forallVal_eq_sInter_sep (vs := vs) vs_nemp vs_nodup
                  (τ := τ) τ_hasArity
                  (D := D) (D_enc := D_enc)
                  (P_enc_subst := SMT.substList vs (List.map SMT.Term.var zs) P_enc)
                  (zs := zs) (τs := τs) zs_nemp zs_len τs_toProdl_eq
                  (imp_body := imp_body) imp_body_def zs_not_fv_D
                  (Δ_ctx := Δ'_alt) hcov_forall_alt hforallVal_alt
                  (denD_val := denD_alt)
                  hcov_D_upd_alt den_D_upd_eq_alt denD_alt_type denD_alt_func
                  (𝒟_val := 𝒟_alt) h𝒟_alt
                  𝒟_alt_nonempty
                  denD_alt_retract
                  hgo_cov_alt hcov_imp_upd_alt himp_total_alt himp_ty_alt
                  (P := P) («Δ» := Δ_alt) Δ_fv_alt
                  (T_val := T_alt)
                  (hT_eq := ?_)
                  (h_den_P := fun {x_fin} hx_typ hx_fin_in =>
                    h_den_P_alt_generic hx_typ hx_fin_in)
                  (h_den_P_bool := fun {x_fin} hx_typ hx_fin_in =>
                    h_den_P_alt_bool hx_typ hx_fin_in)
                  (zs_len_pos_hyp := zs_len_pos) (vs_zs_len := vs_zs_len)
                  (hbridge := hbridge_alt)
                · convert hT_eq_raw_alt using 9
                  set opt := ⟦(B.Term.abstract.go P vs Δ_alt
                    (fun v hv hvs => Δ_fv_alt v
                      (B.fv.mem_all (.inr ⟨hv, hvs⟩)))).uncurry
                    fun i => ⟨_, ⟨τ.get vs.length i, _⟩⟩⟧ᴮ with hopt
                  match opt with
                  | none => rfl
                  | some ⟨Pv, ⟨Pty, hPv⟩⟩ => rfl
              · exact absurd (fun {x} => h_den_P_alt_cond) h1
              · exact absurd (fun {x} => h_den_P_alt_cond) h1
          · exfalso
            rw [dif_neg h_den_P_alt_cond] at rest_alt
            exact Option.noConfusion rest_alt
        exact ⟨denT_alt, hext_Δ'_alt, Δ'_alt_none_out, Δ'_alt_wt,
          hforallVal_alt, hRDom_alt, Δ'_alt_dom⟩
  · -- Phase A2: P doesn't denote at the default x_fin (BType.defaultZFSet-based).
    -- Closed via `B.denote_exists_of_typing` (B-side totality, B/Reasoning/DenotationTotality)
    -- which produces a P-denotation witness contradicting `hP_den_cond`.
    -- `WellTypedCtx` is supplied by `WFTC.of_abstract`; this case adds no new admits
    -- (the existing `admit` in `WFTC.of_abstract.wf` is also used by Phase A1).
    exfalso
    apply hP_den_cond
    exact B.denote_exists_of_typing typP Δ_ext Δ_fv_P (@WFTC.wf _ WFTC.of_abstract)
