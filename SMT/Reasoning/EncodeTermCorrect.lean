import SMT.Reasoning.Basic

open Std.Do B SMT ZFSet
set_option pp.deepTerms true

-- Main theorem
open B SMT ZFSet in
theorem encodeTerm_spec.{u} (fv_sub_typings : B.FvSubTypings)
  (E : B.Env) {Λ : SMT.TypeContext} {t : B.Term} {α : B.BType}
  (typ_t : E.context ⊢ᴮ t : α) {«Δ» : B.RenamingContext.Context}
  (Δ_fv : ∀ v ∈ B.fv t, («Δ» v).isSome)
  {Δ₀ : SMT.RenamingContext.Context}
  (Δ₀_ext : RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» t)
  {used : List SMT.𝒱}
  (Δ₀_none_out : ∀ v ∉ used, Δ₀ v = none)
  {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ} (den_t : ⟦t.abstract «Δ» Δ_fv⟧ᴮ = Option.some ⟨T, α, hT⟩)
  (vars_used : ∀ v ∈ t.vars, v ∈ used)
  (Λ_inv : ∀ v ∈ t.vars, v ∈ Λ → v ∈ E.context)
  -- Path-A R3e: SPLIT existential witness into two finer-grained hypotheses:
  -- existence + RDom (sharing same `denT'`) and Δ-universal totality
  -- (independent of `denT'`). Each is parameterized over `vs`, `D`, `P` so
  -- it can be reused across inductive cases of `t`. Universally quantified
  -- over the binder body so it applies at every has-flag `all` site,
  -- including nested ones via the IH.
  --
  -- HISTORICAL NOTE (audit follow-up): three companion clauses were previously
  -- declared on this signature but never consumed by `encodeTerm_spec.all_case`
  -- — they have been removed: (1) `cast_preimage_witness_hasflag` (R3e2-split),
  -- (2) `pfun_inv` (R1 E.po-functional invariant on flagged binders), and
  -- (3) `hzmem_iff_witness_hasflag` (R3e2-split Δ-universal adequacy clause
  -- feeding `hbridge_hasflag`). They were intended as building blocks for
  -- future inline-discharge of `existence_rdom_witness_hasflag`; see the
  -- companion historical note in `EncodeTermCorrectAll.lean`.
  (existence_rdom_witness_hasflag :
    ∀ (_vs_inner : List B.𝒱) (_D_inner _P_inner : B.Term)
      {zs : List SMT.𝒱} {τs : List SMTType}
      {imp_body : SMT.Term}
      {Δ_ctx : SMT.RenamingContext.Context.{u}}
      (hcov_forall : SMT.RenamingContext.CoversFV Δ_ctx
        (SMT.Term.forall zs τs imp_body))
      (T' : ZFSet.{u}) (hT' : T' ∈ ⟦B.BType.bool⟧ᶻ),
      ∃ denT' : SMT.Dom.{u},
        ⟦(SMT.Term.forall zs τs imp_body).abstract Δ_ctx hcov_forall⟧ˢ
          = some denT' ∧
        (⟨T', ⟨B.BType.bool, hT'⟩⟩ : B.Dom) ≘ᶻ denT')
  (totality_witness_hasflag :
    ∀ (vs_inner : List B.𝒱) (D_inner P_inner : B.Term)
      {zs : List SMT.𝒱} {τs : List SMTType}
      {imp_body : SMT.Term}
      {Δ_ctx : SMT.RenamingContext.Context.{u}}
      (_hcov_forall : SMT.RenamingContext.CoversFV Δ_ctx
        (SMT.Term.forall zs τs imp_body))
      {used' : List SMT.𝒱} {Λ' : SMT.TypeContext},
      ∀ (Δ_alt : B.RenamingContext.Context)
        (Δ_fv_alt : ∀ v ∈ B.fv (B.Term.all vs_inner D_inner P_inner),
          (Δ_alt v).isSome = true)
        (Δ₀_alt : SMT.RenamingContext.Context.{u}),
        SMT.RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt
            (B.Term.all vs_inner D_inner P_inner) →
          (∀ v ∉ used', Δ₀_alt v = none) →
            (∀ (v : SMT.𝒱) (d : SMT.Dom.{u}),
                Δ₀_alt v = some d →
                  ∀ (τ_v : SMTType), AList.lookup v Λ' = some τ_v →
                    d.snd.fst = τ_v) →
              ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦B.BType.bool⟧ᶻ),
                ⟦(B.Term.all vs_inner D_inner P_inner).abstract Δ_alt Δ_fv_alt⟧ᴮ =
                    some ⟨T_alt, ⟨B.BType.bool, hT_alt⟩⟩ →
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
                                (⟨T_alt, ⟨B.BType.bool, hT_alt⟩⟩ : B.Dom)
                                  ≘ᶻ denT_alt ∧
                                  ∀ (v : SMT.𝒱), Δ'_alt v ≠ none → v ∈ Λ')
  {n : ℕ} :
  ⦃ fun ⟨E0, Λ'⟩ ↦ ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ Λ.keys ⊆ E0.usedVars ∧ E0.usedVars = used⌝ ⦄
  encodeTerm t E
  ⦃ ⇓? (⟨t', σ⟩ : SMT.Term × SMTType) ⟨E', Γ'⟩ => ⌜
    used ⊆ E'.usedVars ∧
    Λ ⊆ Γ' ∧
    Γ'.keys ⊆ E'.usedVars ∧
    B.CoversUsedVars E'.usedVars t ∧
    σ = α.toSMTType ∧
    (Γ' ⊢ˢ t' : σ) ∧
    (∀ v ∈ used, v ∉ Λ → v ∉ B.fv t → v ∉ Γ') ∧
    ∃ (Δ' : SMT.RenamingContext.Context),
      ∃ (Δ'_covers : RenamingContext.CoversFV Δ' t'),
        RenamingContext.Extends Δ' Δ₀ ∧
          RenamingContext.ExtendsOnSourceFV Δ' («Δ») t ∧
          (∀ v ∉ E'.usedVars, Δ' v = none) ∧
          ∃ denT', ⟦t'.abstract Δ' Δ'_covers⟧ˢ = some denT' ∧ ⟨T, α, hT⟩ ≘ᶻ denT' ∧
    -- Totality: t' denotes under any alternative valid B-level denotation
    (∀ (Δ_alt : B.RenamingContext.Context) (Δ_fv_alt : ∀ v ∈ B.fv t, (Δ_alt v).isSome = true)
        (Δ₀_alt : SMT.RenamingContext.Context),
        RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt t →
        (∀ v ∉ E'.usedVars, Δ₀_alt v = none) →
        (∀ v (d : SMT.Dom), Δ₀_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) →
        ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦α⟧ᶻ),
        ⟦t.abstract Δ_alt Δ_fv_alt⟧ᴮ = some ⟨T_alt, ⟨α, hT_alt⟩⟩ →
        ∃ (Δ'_alt : SMT.RenamingContext.Context) (hcov_alt : RenamingContext.CoversFV Δ'_alt t')
          (denT_alt : SMT.Dom),
          RenamingContext.Extends Δ'_alt Δ₀_alt ∧
          (∀ v ∉ E'.usedVars, Δ'_alt v = none) ∧
          (∀ v (d : SMT.Dom), Δ'_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) ∧
          ⟦t'.abstract Δ'_alt hcov_alt⟧ˢ = some denT_alt ∧ ⟨T_alt, ⟨α, hT_alt⟩⟩ ≘ᶻ denT_alt ∧
          (∀ v, Δ'_alt v ≠ none → v ∈ Γ'))⌝⦄ := by
  induction t generalizing E n α «Δ» T hT Λ Δ₀ used with
  | «ℤ»                      => exact encodeTerm_spec.ℤ_case E typ_t Δ_fv Δ₀_ext Δ₀_none_out den_t vars_used Λ_inv
  | 𝔹                        => exact encodeTerm_spec.𝔹_case E typ_t Δ_fv Δ₀_ext Δ₀_none_out den_t vars_used Λ_inv
  | var v                    => exact encodeTerm_spec.var_case v E typ_t Δ_fv Δ₀_ext Δ₀_none_out den_t vars_used Λ_inv
  | int i                    => exact encodeTerm_spec.int_case i E typ_t Δ_fv Δ₀_ext Δ₀_none_out den_t vars_used Λ_inv
  | bool b                   => exact encodeTerm_spec.bool_case b E typ_t Δ_fv Δ₀_ext Δ₀_none_out den_t vars_used Λ_inv
  | maplet x y x_ih y_ih     => exact encodeTerm_spec.maplet_case fv_sub_typings x y x_ih y_ih E typ_t Δ_fv Δ₀_ext Δ₀_none_out den_t vars_used Λ_inv
  | add x y x_ih y_ih        => exact encodeTerm_spec.add_case fv_sub_typings x y x_ih y_ih E typ_t Δ_fv Δ₀_ext Δ₀_none_out den_t vars_used Λ_inv
  | sub x y x_ih y_ih        => exact encodeTerm_spec.sub_case fv_sub_typings x y x_ih y_ih E typ_t Δ_fv Δ₀_ext Δ₀_none_out den_t vars_used Λ_inv
  | mul x y x_ih y_ih        => exact encodeTerm_spec.mul_case fv_sub_typings x y x_ih y_ih E typ_t Δ_fv Δ₀_ext Δ₀_none_out den_t vars_used Λ_inv
  | le x y x_ih y_ih         => exact encodeTerm_spec.le_case fv_sub_typings x y x_ih y_ih E typ_t Δ_fv Δ₀_ext Δ₀_none_out den_t vars_used Λ_inv
  | min S ih                 => exact encodeTerm_spec.min_case S ih E typ_t Δ_fv Δ₀_ext Δ₀_none_out den_t vars_used Λ_inv
  | max S ih                 => exact encodeTerm_spec.max_case S ih E typ_t Δ_fv Δ₀_ext Δ₀_none_out den_t vars_used Λ_inv
  | card S ih                => exact encodeTerm_spec.card_case S ih E typ_t Δ_fv Δ₀_ext Δ₀_none_out den_t vars_used Λ_inv
  | and x y x_ih y_ih        => exact encodeTerm_spec.and_case fv_sub_typings x y x_ih y_ih E typ_t Δ_fv Δ₀_ext Δ₀_none_out den_t vars_used Λ_inv
  | not x ih                 => exact encodeTerm_spec.not_case fv_sub_typings x ih E typ_t Δ_fv Δ₀_ext Δ₀_none_out den_t vars_used Λ_inv
  | pow S ih                 => exact encodeTerm_spec.pow_case fv_sub_typings S ih E typ_t Δ_fv Δ₀_ext Δ₀_none_out den_t vars_used Λ_inv
  | cprod A B A_ih B_ih      => exact encodeTerm_spec.cprod_case fv_sub_typings A B A_ih B_ih E typ_t Δ_fv Δ₀_ext Δ₀_none_out den_t vars_used Λ_inv
  | mem x S x_ih S_ih        => exact encodeTerm_spec.mem_case fv_sub_typings x S x_ih S_ih E typ_t Δ_fv Δ₀_ext Δ₀_none_out den_t vars_used Λ_inv
  | eq x y x_ih y_ih         => exact encodeTerm_spec.eq_case fv_sub_typings x y x_ih y_ih E typ_t Δ_fv Δ₀_ext Δ₀_none_out den_t vars_used Λ_inv
  | union A B A_ih B_ih      => exact encodeTerm_spec.union_case fv_sub_typings A B A_ih B_ih E typ_t Δ_fv Δ₀_ext Δ₀_none_out den_t vars_used Λ_inv
  | inter A B A_ih B_ih      => exact encodeTerm_spec.inter_case fv_sub_typings A B A_ih B_ih E typ_t Δ_fv Δ₀_ext Δ₀_none_out den_t vars_used Λ_inv
  | pfun A B A_ih B_ih       => exact encodeTerm_spec.pfun_case fv_sub_typings A B A_ih B_ih E typ_t Δ_fv Δ₀_ext Δ₀_none_out den_t vars_used Λ_inv
  | app f x f_ih x_ih        => exact encodeTerm_spec.app_case fv_sub_typings f x f_ih x_ih E typ_t Δ_fv Δ₀_ext Δ₀_none_out den_t vars_used Λ_inv
  | collect vs D P D_ih P_ih => exact encodeTerm_spec.collect_case fv_sub_typings vs D P D_ih P_ih E typ_t Δ_fv Δ₀_ext Δ₀_none_out den_t vars_used Λ_inv
  | all vs D P D_ih P_ih     => exact encodeTerm_spec.all_case fv_sub_typings vs D P D_ih P_ih E typ_t Δ_fv Δ₀_ext Δ₀_none_out den_t vars_used Λ_inv (existence_rdom_witness_hasflag vs D P) (totality_witness_hasflag vs D P)
  | lambda vs D P D_ih P_ih  => exact encodeTerm_spec.lambda_case fv_sub_typings vs D P D_ih P_ih E typ_t Δ_fv Δ₀_ext Δ₀_none_out den_t vars_used Λ_inv
