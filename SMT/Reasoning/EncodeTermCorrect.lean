import SMT.Reasoning.Basic

open Std.Do B SMT ZFSet
set_option pp.deepTerms true

-- Main theorem
open B SMT ZFSet in
theorem encodeTerm_spec.{u} (fv_sub_typings : B.FvSubTypings)
  {t : B.Term} (wd_t : B.Term.WellDefined.{u} t)
  (E : B.Env) {Λ : SMT.TypeContext} {α : B.BType}
  (typ_t : E.context ⊢ᴮ t : α) {«Δ» : B.RenamingContext.Context}
  (Δ_fv : ∀ v ∈ B.fv t, («Δ» v).isSome)
  {Δ₀ : SMT.RenamingContext.Context}
  (Δ₀_ext : RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» t)
  {used : List SMT.𝒱}
  (Δ₀_none_out : ∀ v ∉ used, Δ₀ v = none)
  {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ} (den_t : ⟦t.abstract «Δ» Δ_fv⟧ᴮ = Option.some ⟨T, α, hT⟩)
  (vars_used : ∀ v ∈ t.vars, v ∈ used)
  (Λ_inv : ∀ v ∈ t.vars, v ∈ Λ → v ∈ E.context)
  (bv_nodup : (B.bv t).Nodup)
  (respects : B.RenamingContext.RespectsTypeContextOnFV (B.RenamingContext.toSMT «Δ») Λ t)
  (fv_in_Λ : ∀ v ∈ B.fv t, v ∈ Λ)
  (wf : B.RenWF E.context «Δ»)
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
    (∀ v ∈ used, v ∉ Λ → v ∉ B.Term.vars t → v ∉ Γ') ∧
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
        B.RenWF E.context Δ_alt →
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
  | «ℤ»                      => exact encodeTerm_spec.ℤ_case E typ_t Δ_fv Δ₀_ext Δ₀_none_out den_t vars_used Λ_inv bv_nodup respects fv_in_Λ
  | 𝔹                        => exact encodeTerm_spec.𝔹_case E typ_t Δ_fv Δ₀_ext Δ₀_none_out den_t vars_used Λ_inv bv_nodup respects fv_in_Λ
  | var v                    => exact encodeTerm_spec.var_case v E typ_t Δ_fv Δ₀_ext Δ₀_none_out den_t vars_used Λ_inv bv_nodup respects fv_in_Λ
  | int i                    => exact encodeTerm_spec.int_case i E typ_t Δ_fv Δ₀_ext Δ₀_none_out den_t vars_used Λ_inv bv_nodup respects fv_in_Λ
  | bool b                   => exact encodeTerm_spec.bool_case b E typ_t Δ_fv Δ₀_ext Δ₀_none_out den_t vars_used Λ_inv bv_nodup respects fv_in_Λ
  | maplet x y x_ih y_ih     => exact encodeTerm_spec.maplet_case fv_sub_typings x y (x_ih wd_t.1) (y_ih wd_t.2) E typ_t Δ_fv Δ₀_ext Δ₀_none_out den_t vars_used Λ_inv bv_nodup respects fv_in_Λ
  | add x y x_ih y_ih        => exact encodeTerm_spec.add_case fv_sub_typings x y (x_ih wd_t.1) (y_ih wd_t.2) E typ_t Δ_fv Δ₀_ext Δ₀_none_out den_t vars_used Λ_inv bv_nodup respects fv_in_Λ
  | sub x y x_ih y_ih        => exact encodeTerm_spec.sub_case fv_sub_typings x y (x_ih wd_t.1) (y_ih wd_t.2) E typ_t Δ_fv Δ₀_ext Δ₀_none_out den_t vars_used Λ_inv bv_nodup respects fv_in_Λ
  | mul x y x_ih y_ih        => exact encodeTerm_spec.mul_case fv_sub_typings x y (x_ih wd_t.1) (y_ih wd_t.2) E typ_t Δ_fv Δ₀_ext Δ₀_none_out den_t vars_used Λ_inv bv_nodup respects fv_in_Λ
  | le x y x_ih y_ih         => exact encodeTerm_spec.le_case fv_sub_typings x y (x_ih wd_t.1) (y_ih wd_t.2) E typ_t Δ_fv Δ₀_ext Δ₀_none_out den_t vars_used Λ_inv bv_nodup respects fv_in_Λ
  | min S ih                 => exact encodeTerm_spec.min_case S (ih wd_t.1) E typ_t Δ_fv Δ₀_ext Δ₀_none_out den_t vars_used Λ_inv bv_nodup respects fv_in_Λ
  | max S ih                 => exact encodeTerm_spec.max_case S (ih wd_t.1) E typ_t Δ_fv Δ₀_ext Δ₀_none_out den_t vars_used Λ_inv bv_nodup respects fv_in_Λ
  | card S ih                => exact encodeTerm_spec.card_case S (ih wd_t.1) E typ_t Δ_fv Δ₀_ext Δ₀_none_out den_t vars_used Λ_inv bv_nodup respects fv_in_Λ
  | and x y x_ih y_ih        => exact encodeTerm_spec.and_case fv_sub_typings x y (x_ih wd_t.1) (y_ih wd_t.2) E typ_t Δ_fv Δ₀_ext Δ₀_none_out den_t vars_used Λ_inv bv_nodup respects fv_in_Λ
  | not x ih                 => exact encodeTerm_spec.not_case fv_sub_typings x (ih wd_t) E typ_t Δ_fv Δ₀_ext Δ₀_none_out den_t vars_used Λ_inv bv_nodup respects fv_in_Λ
  | pow S ih                 => exact encodeTerm_spec.pow_case fv_sub_typings S (ih wd_t) E typ_t Δ_fv Δ₀_ext Δ₀_none_out den_t vars_used Λ_inv bv_nodup respects fv_in_Λ
  | cprod A B A_ih B_ih      => exact encodeTerm_spec.cprod_case fv_sub_typings A B (A_ih wd_t.1) (B_ih wd_t.2) E typ_t Δ_fv Δ₀_ext Δ₀_none_out den_t vars_used Λ_inv bv_nodup respects fv_in_Λ
  | mem x S x_ih S_ih        => exact encodeTerm_spec.mem_case fv_sub_typings x S (x_ih wd_t.1) (S_ih wd_t.2) E typ_t Δ_fv Δ₀_ext Δ₀_none_out den_t vars_used Λ_inv bv_nodup respects fv_in_Λ
  | eq x y x_ih y_ih         => exact encodeTerm_spec.eq_case fv_sub_typings x y (x_ih wd_t.1) (y_ih wd_t.2) E typ_t Δ_fv Δ₀_ext Δ₀_none_out den_t vars_used Λ_inv bv_nodup respects fv_in_Λ
  | union A B A_ih B_ih      => exact encodeTerm_spec.union_case fv_sub_typings A B (A_ih wd_t.1) (B_ih wd_t.2) E typ_t Δ_fv Δ₀_ext Δ₀_none_out den_t vars_used Λ_inv bv_nodup respects fv_in_Λ
  | inter A B A_ih B_ih      => exact encodeTerm_spec.inter_case fv_sub_typings A B (A_ih wd_t.1) (B_ih wd_t.2) E typ_t Δ_fv Δ₀_ext Δ₀_none_out den_t vars_used Λ_inv bv_nodup respects fv_in_Λ
  | pfun A B A_ih B_ih       => exact encodeTerm_spec.pfun_case fv_sub_typings A B (A_ih wd_t.1) (B_ih wd_t.2) E typ_t Δ_fv Δ₀_ext Δ₀_none_out den_t vars_used Λ_inv bv_nodup respects fv_in_Λ
  | app f x f_ih x_ih        => exact encodeTerm_spec.app_case fv_sub_typings f x (f_ih wd_t.1) (x_ih wd_t.2.1) E typ_t Δ_fv Δ₀_ext Δ₀_none_out den_t vars_used Λ_inv bv_nodup respects fv_in_Λ
  | collect vs D P D_ih P_ih => exact encodeTerm_spec.collect_case fv_sub_typings vs D P (D_ih wd_t.1) (P_ih wd_t.2) E typ_t Δ_fv Δ₀_ext Δ₀_none_out den_t vars_used Λ_inv bv_nodup respects fv_in_Λ
  | all vs D P D_ih P_ih     => exact encodeTerm_spec.all_case fv_sub_typings vs D P (D_ih wd_t.1) (P_ih wd_t.2) E typ_t Δ_fv Δ₀_ext Δ₀_none_out den_t vars_used Λ_inv bv_nodup respects fv_in_Λ wf wd_t.2 (existence_rdom_witness_hasflag vs D P) (totality_witness_hasflag vs D P)
  | lambda vs D P D_ih P_ih  => exact encodeTerm_spec.lambda_case fv_sub_typings vs D P (D_ih wd_t.1) (P_ih wd_t.2) E typ_t Δ_fv Δ₀_ext Δ₀_none_out den_t vars_used Λ_inv bv_nodup respects fv_in_Λ
