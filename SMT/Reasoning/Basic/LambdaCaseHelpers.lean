import SMT.Reasoning.Basic.CollectCaseHelpers
import SMT.Reasoning.Basic.EncodeTermCorrectPFun
import SMT.Reasoning.Axioms

open Std.Do B SMT ZFSet

/-- Public version of `EncodeTermCorrectPFun.denote_eq_some_bool`. Produces Deq
witnessing that the EQ of two same-typed terms denotes to a bool result. -/
theorem lambda_denote_eq_some_bool
    {t₁ t₂ : SMT.PHOAS.Term SMT.Dom} {D₁ D₂ : SMT.Dom}
    (h₁ : ⟦t₁⟧ˢ = some D₁) (h₂ : ⟦t₂⟧ˢ = some D₂) (hty : D₁.2.1 = D₂.2.1) :
    ∃ D : SMT.Dom, ⟦t₁ =ˢ' t₂⟧ˢ = some D ∧ D.2.1 = .bool := by
  obtain ⟨d₁, τ₁, hd₁⟩ := D₁
  obtain ⟨d₂, τ₂, hd₂⟩ := D₂
  dsimp at hty; subst hty
  rw [SMT.denote, h₁, h₂]
  simp only [Option.pure_def, Option.failure_eq_none, Option.bind_eq_bind, Option.bind_some]
  exact ⟨_, rfl, rfl⟩

/-!
# Helper lemmas for `encodeTerm_spec.lambda_case`

This file collects lemmas mirroring `CollectCaseHelpers.lean` but specialized
for the `lambda` case. Specifically, we provide `lambda_hbridge`, the
analogue of `collect_hbridge` for the lambda's AND/EQ body and pair codomain.

Structure mirrors `collect_hbridge` (in `CollectCaseHelpers.lean`). The
key adaptations are:
* SMT body is `D_enc(z.fst) ∧ˢ (z.snd =ˢ substList vs (toDestPair vs z.fst) P_enc)`
  rather than `(D_enc z).ite (substList ...) false`.
* The bound variable `z` has type `(τ.toSMTType.pair β.toSMTType)` rather
  than `τ.toSMTType` — i.e., `z` is a pair of the codomain element and the
  domain tuple.
* The semantic conclusion expresses ℰ(xy) where xy is decomposed into
  `(xy.π₁, xy.π₂)` and the bridge constrains the second component.
-/

/-! ### Semantic bridge for the lambda case

For each `xy ∈ ⟦τ⟧ᶻ.prod ⟦β⟧ᶻ` (canonically embedded as `Wxy : SMT.Dom`
of type `τ.toSMTType.pair β.toSMTType`), the SMT lambda body
`D_enc(z.fst) ∧ˢ (z.snd =ˢ substList vs (toDestPair vs z.fst) P_enc)`
evaluates to `zftrue` at `z↦Wxy` if and only if:
* `xy.π₁ ∈ 𝒟_val` (the chosen-branch domain), AND
* `P` evaluated at the variables-bound version of `xy.π₁.get vs.length`
  yields `xy.π₂` with type `β`.

This is the analogue of `collect_hbridge` adapted for the AND/EQ body and
pair codomain.
-/
open Classical in
set_option maxHeartbeats 4000000 in
theorem lambda_hbridge.{u}
    -- Type infrastructure
    {vs : List B.𝒱} (vs_nemp : vs ≠ []) (vs_nodup : vs.Nodup)
    {τ β : BType} (τ_hasArity : τ.hasArity vs.length)
    -- SMT terms
    {D : B.Term}
    {D_enc P_enc : SMT.Term} {z : SMT.𝒱}
    -- z not free in D_enc/P_enc, z ∉ vs
    (z_not_fv_D : z ∉ SMT.fv D_enc)
    (z_not_fv_P : z ∉ SMT.fv P_enc)
    (z_not_vs : z ∉ vs)
    -- vs disjoint from B.fv D
    (vs_not_D_fv : ∀ v ∈ vs, v ∉ B.fv D)
    -- BV constraints (from typing: bv of well-typed terms are disjoint from context)
    (hvs_not_bv_P : ∀ v ∈ vs, v ∉ SMT.bv P_enc)
    (z_not_bv_P : z ∉ SMT.bv P_enc)
    -- Renaming context for body evaluation (z is bound to a pair-typed witness)
    {Δ_ctx : SMT.RenamingContext.Context}
    -- Body coverage: parametric in z-update.
    (hcov_body_upd : ∀ W : SMT.Dom,
      SMT.RenamingContext.CoversFV (Function.update Δ_ctx z (some W))
        ((@ˢD_enc) (SMT.Term.var z).fst ∧ˢ
          ((SMT.Term.var z).snd =ˢ
            SMT.substList vs (toDestPair vs (SMT.Term.var z).fst) P_enc)))
    -- D_enc denotation data (parametric in z-update).
    {denD_val : SMT.Dom}
    (hcov_D_upd : ∀ Xarg : SMT.Dom,
      SMT.RenamingContext.CoversFV (Function.update Δ_ctx z (some Xarg)) D_enc)
    (den_D_upd_eq : ∀ Xarg : SMT.Dom,
      ⟦D_enc.abstract (Function.update Δ_ctx z (some Xarg)) (hcov_D_upd Xarg)⟧ˢ = some denD_val)
    (denD_val_type : denD_val.snd.fst = τ.toSMTType.fun SMTType.bool)
    (denD_val_func : ⟦τ.toSMTType⟧ᶻ.IsFunc 𝔹 denD_val.fst)
    {𝒟_val : ZFSet.{u}} (h𝒟_val : 𝒟_val ∈ ⟦τ.set⟧ᶻ)
    (denD_val_retract : retract τ.set denD_val.fst = 𝒟_val)
    -- substList coverage and FV
    (hcov_substList_upd : ∀ W : SMT.Dom,
      SMT.RenamingContext.CoversFV (Function.update Δ_ctx z (some W))
        (SMT.substList vs (toDestPair vs (SMT.Term.var z).fst) P_enc))
    (fv_substList_disj_vs : ∀ v ∈ SMT.fv (SMT.substList vs
        (toDestPair vs (SMT.Term.var z).fst) P_enc),
      v ≠ z → v ∉ vs)
    -- B-level data
    {P : B.Term} {«Δ» : B.RenamingContext.Context}
    (Δ_fv_lambda : ∀ v ∈ B.fv (Term.lambda vs D P), («Δ» v).isSome = true)
    -- B typing
    {E_ctx : B.TypeContext}
    (typP : E_ctx ⊢ᴮ P : β)
    -- SMT renaming: Δ_D_eval extends toSMTOnFV «Δ» (lambda vs D P)
    {Δ_D_eval : SMT.RenamingContext.Context}
    (Δ_D_eval_extends : SMT.RenamingContext.Extends Δ_D_eval
      (B.RenamingContext.toSMTOnFV «Δ» (Term.lambda vs D P)))
    -- Δ_ctx agrees with toSMT «Δ» on source-level P variables not in vs
    (Δ_ctx_source : ∀ v ∈ B.fv P, v ∉ vs → Δ_ctx v = B.RenamingContext.toSMT «Δ» v)
    -- Δ_D_eval vanishes outside used vars
    {used_St₂ : List SMT.𝒱}
    (Δ_D_eval_none_St₂ : ∀ v ∉ used_St₂, Δ_D_eval v = none)
    -- vs ⊆ used (for contradiction in none_out)
    (vars_used_vs : ∀ v ∈ vs, v ∈ used_St₂)
    -- used_St₂ ⊆ used_St₃ (subsumption)
    {used_St₃ : List SMT.𝒱}
    (St₂_sub_St₃ : ∀ v ∈ used_St₂, v ∈ used_St₃)
    -- fv(P_enc) ⊆ used_St₃ (P was encoded within St₃)
    (fv_P_enc_used : ∀ v ∈ SMT.fv P_enc, v ∈ used_St₃)
    -- P_enc_total: simplified (no agreement clause)
    (P_enc_total :
      ∀ (Δ_alt : B.RenamingContext.Context)
        (Δ_fv_alt : ∀ v ∈ B.fv P, (Δ_alt v).isSome = true)
        (Δ₀_alt : SMT.RenamingContext.Context),
        RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt P →
        (∀ v ∉ used_St₃, Δ₀_alt v = none) →
        ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦β⟧ᶻ),
          ⟦P.abstract Δ_alt Δ_fv_alt⟧ᴮ = some ⟨T_alt, ⟨β, hT_alt⟩⟩ →
          ∃ (Δ'_alt : SMT.RenamingContext.Context)
            (hcov_alt : SMT.RenamingContext.CoversFV Δ'_alt P_enc)
            (denT_alt : SMT.Dom),
            SMT.RenamingContext.Extends Δ'_alt Δ₀_alt ∧
            ⟦P_enc.abstract Δ'_alt hcov_alt⟧ˢ = some denT_alt ∧
            ⟨T_alt, ⟨β, hT_alt⟩⟩ ≘ᶻ denT_alt)
    -- P denotability for all x ∈ 𝒟_val
    (h_den_P : ∀ {x_fin : Fin vs.length → B.Dom},
      (∀ i, (x_fin i).snd.fst = τ.get vs.length i ∧
            (x_fin i).fst ∈ ⟦τ.get vs.length i⟧ᶻ) →
      ofFinDom x_fin ∈ 𝒟_val →
      ⟦(B.Term.abstract.go P vs «Δ» (fun v hv hvs => Δ_fv_lambda v
        (B.fv.mem_lambda (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ.isSome = true)
    : ∀ (xy : ZFSet.{u}) (hx_mem : xy.π₁ ∈ ⟦τ⟧ᶻ) (hy_mem : xy.π₂ ∈ ⟦β⟧ᶻ)
        (hxy_pair : xy = xy.π₁.pair xy.π₂)
        (hxy_π₁_arity : xy.π₁.hasArity vs.length)
        (hxy_𝒟 : xy.π₁ ∈ 𝒟_val),
      let hxy_mem : xy ∈ ⟦(τ ×ᴮ β)⟧ᶻ := by
        rw [BType.toZFSet, ZFSet.mem_prod]
        exact ⟨xy.π₁, hx_mem, xy.π₂, hy_mem, hxy_pair⟩
      let Wxy : SMT.Dom := ⟨(ZFSet.fapply (BType.canonicalIsoSMTType (τ ×ᴮ β)).1
        (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType (τ ×ᴮ β)).2.1)
        ⟨xy, by rwa [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType (τ ×ᴮ β)).2.1]⟩).1,
        (τ ×ᴮ β).toSMTType, ZFSet.fapply_mem_range _ _⟩
      let x_fin : Fin vs.length → B.Dom := fun i =>
        ⟨xy.π₁.get vs.length i, ⟨τ.get vs.length i,
          get_mem_type_of_isTuple hxy_π₁_arity τ_hasArity hx_mem⟩⟩
      ∀ body_val : SMT.Dom,
        ⟦(((@ˢD_enc) (SMT.Term.var z).fst ∧ˢ
            ((SMT.Term.var z).snd =ˢ
              SMT.substList vs (toDestPair vs (SMT.Term.var z).fst) P_enc))).abstract
          (Function.update Δ_ctx z (some Wxy)) (hcov_body_upd Wxy)⟧ˢ = some body_val →
        (body_val.fst = zftrue ↔
          (∃ (Px : ZFSet.{u}) (hP_val : Px ∈ ⟦β⟧ᶻ),
            ⟦(B.Term.abstract.go P vs «Δ» (fun v hv hvs => Δ_fv_lambda v
              (B.fv.mem_lambda (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ =
              some ⟨Px, ⟨β, hP_val⟩⟩ ∧ Px = xy.π₂)) := by
  intro xy hx_mem hy_mem hxy_pair hxy_π₁_arity hxy_𝒟 hxy_mem Wxy x_fin body_val hbody_val
  -- The proof closely mirrors `collect_hbridge`. Here we set up the same
  -- structural infrastructure (Δ_ext_x, Δ₀_hybrid_x, P_enc_total invocation)
  -- adapted for the lambda case where `xy.π₁` plays the role of `x`.
  have hWxy_ty : Wxy.snd.fst = (τ ×ᴮ β).toSMTType := rfl
  have hWxy_mem : Wxy.fst ∈ ⟦(τ ×ᴮ β).toSMTType⟧ᶻ := Wxy.snd.snd
  -- Step B: Build x_fin-derived B context
  set Δ_ext_x := Function.updates «Δ» vs (List.ofFn fun i => some (x_fin i))
  have Δ_fv_P_x : ∀ v ∈ B.fv P, (Δ_ext_x v).isSome = true := by
    intro v hv; show (Function.updates «Δ» vs _ v).isSome = true
    rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup]
    split_ifs with hvs
    · simp [List.getElem_ofFn]
    · exact Δ_fv_lambda v (B.fv.mem_lambda (.inr ⟨hv, hvs⟩))
  -- Step C: Get B-level P denotation at x_fin
  have h_ofFinDom_eq : ZFSet.ofFinDom x_fin = xy.π₁ :=
    ZFSet.ofFinDom_get (List.length_pos_iff.mpr vs_nemp)
      (fun i => get_mem_type_of_isTuple hxy_π₁_arity τ_hasArity hx_mem)
      hxy_π₁_arity τ_hasArity
  have hx_fin_in_𝒟 : ZFSet.ofFinDom x_fin ∈ 𝒟_val := h_ofFinDom_eq ▸ hxy_𝒟
  have hx_fin_typ : ∀ i, (x_fin i).snd.fst = τ.get vs.length i ∧
      (x_fin i).fst ∈ ⟦τ.get vs.length i⟧ᶻ :=
    fun i => ⟨rfl, (x_fin i).snd.snd⟩
  have hP_isSome := h_den_P hx_fin_typ hx_fin_in_𝒟
  obtain ⟨⟨P_val, P_ty, hP_val⟩, hP_den⟩ := Option.isSome_iff_exists.mp hP_isSome
  have hP_go_den : ⟦(B.Term.abstract.go P vs «Δ» (by
        intro v hv hvs; exact Δ_fv_lambda v (B.fv.mem_lambda (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ
      = some ⟨P_val, ⟨P_ty, hP_val⟩⟩ := by convert hP_den using 2
  have hτPx_β : P_ty = β := by
    rw [denote_term_abstract_go_eq_term_abstract vs_nodup vs_nemp x_fin Δ_fv_P_x] at hP_go_den
    exact (denote_welltyped_eq (t := P.abstract Δ_ext_x Δ_fv_P_x)
      ⟨_, WFTC.of_abstract, β, by convert Typing.of_abstract Δ_fv_P_x typP⟩ hP_go_den).symm
  -- Recover hP_go_den/hP_den at the substituted type β.
  cases hτPx_β
  have h_den_P_x : ⟦P.abstract Δ_ext_x Δ_fv_P_x⟧ᴮ = some ⟨P_val, ⟨β, hP_val⟩⟩ := by
    rw [← denote_term_abstract_go_eq_term_abstract vs_nodup vs_nemp x_fin Δ_fv_P_x]; exact hP_go_den
  -- Step W: Decompose Wxy.fst into canonical(τ, xy.π₁).pair canonical(β, xy.π₂).
  have hζ_τ := (BType.canonicalIsoSMTType τ).2.1
  have hζ_β := (BType.canonicalIsoSMTType β).2.1
  have hfp := ZFSet.fapply_fprod (hf := hζ_τ) (hg := hζ_β)
    (a := xy.π₁) (b := xy.π₂) hx_mem hy_mem
  -- Rewrite Wxy.fst by replacing inner xy with xy.π₁.pair xy.π₂ in the canonical iso.
  have hWxy_pair : Wxy.fst =
      ((ZFSet.fapply (BType.canonicalIsoSMTType τ).1
          (ZFSet.is_func_is_pfunc hζ_τ)
          ⟨xy.π₁, by rwa [ZFSet.is_func_dom_eq hζ_τ]⟩).1).pair
      ((ZFSet.fapply (BType.canonicalIsoSMTType β).1
          (ZFSet.is_func_is_pfunc hζ_β)
          ⟨xy.π₂, by rwa [ZFSet.is_func_dom_eq hζ_β]⟩).1) := by
    -- The argument xy gets re-expressed as xy.π₁.pair xy.π₂ via hxy_pair.
    -- We then apply hfp on the canonical iso of the pair form.
    have h_lhs' : Wxy.fst = (ZFSet.fapply (BType.canonicalIsoSMTType (τ ×ᴮ β)).1
        (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType (τ ×ᴮ β)).2.1)
        ⟨xy.π₁.pair xy.π₂, by
          rw [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType (τ ×ᴮ β)).2.1]
          rw [BType.toZFSet, ZFSet.mem_prod]; exact ⟨xy.π₁, hx_mem, xy.π₂, hy_mem, rfl⟩⟩).1 := by
      show Wxy.fst = _
      -- congr 1 on `Subtype.val a = Subtype.val b` works if we set up correctly.
      apply congrArg Subtype.val
      apply congrArg
      apply Subtype.ext
      exact hxy_pair
    rw [h_lhs']; exact hfp
  have hWxy_π₁ : Wxy.fst.π₁ = (ZFSet.fapply (BType.canonicalIsoSMTType τ).1
      (ZFSet.is_func_is_pfunc hζ_τ)
      ⟨xy.π₁, by rwa [ZFSet.is_func_dom_eq hζ_τ]⟩).1 := by
    rw [hWxy_pair, ZFSet.π₁_pair]
  have hWxy_π₂ : Wxy.fst.π₂ = (ZFSet.fapply (BType.canonicalIsoSMTType β).1
      (ZFSet.is_func_is_pfunc hζ_β)
      ⟨xy.π₂, by rwa [ZFSet.is_func_dom_eq hζ_β]⟩).1 := by
    rw [hWxy_pair, ZFSet.π₂_pair]
  -- Step D: Build Δ_D_ext_x extending Δ_D_eval at vs to canonical SMT translations.
  set Δ_D_ext_x := Function.updates Δ_D_eval vs
    (List.ofFn fun (i : Fin vs.length) => B.RenamingContext.toSMT Δ_ext_x vs[i])
  -- Step E: Build hybrid Δ₀_hybrid_x.
  set Δ₀_hybrid_x : SMT.RenamingContext.Context :=
    fun v => if v ∈ vs then Δ_D_ext_x v
             else if v ∈ used_St₃ then Δ_ctx v
             else none
  -- Step E.1: ExtendsOnSourceFV for Δ₀_hybrid_x
  have Δ₀_hybrid_ext_P_x : RenamingContext.ExtendsOnSourceFV Δ₀_hybrid_x Δ_ext_x P := by
    intro v d hv_eq
    by_cases hv_fv : v ∈ B.fv P
    · have hv_smt : B.RenamingContext.toSMT Δ_ext_x v = some d := by
        have : B.RenamingContext.toSMTOnFV Δ_ext_x P v = B.RenamingContext.toSMT Δ_ext_x v := by
          simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
            B.RenamingContext.restrictToFV_eq_of_mem hv_fv]
        rwa [← this]
      by_cases hvs : v ∈ vs
      · show (if v ∈ vs then Δ_D_ext_x v else _) = some d
        rw [if_pos hvs]
        show Function.updates Δ_D_eval vs _ v = some d
        rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup, dif_pos hvs]
        simp only [List.getElem_ofFn, Fin.getElem_fin, List.getElem_idxOf]; exact hv_smt
      · -- v ∉ vs, v ∈ B.fv P: Δ₀_hybrid_x v = Δ_ctx v (since v ∈ used_St₃)
        have hv_lambda : v ∈ B.fv (Term.lambda vs D P) := fv.mem_lambda (.inr ⟨hv_fv, hvs⟩)
        have hv_used : v ∈ used_St₃ := by
          have hΔ_ext_x_eq : Δ_ext_x v = «Δ» v := by
            show Function.updates «Δ» vs _ v = «Δ» v; exact Function.updates_of_not_mem «Δ» vs _ v hvs
          obtain ⟨bdom, hbdom⟩ := Option.isSome_iff_exists.mp (Δ_fv_lambda v hv_lambda)
          have h_toSMT_v : ∃ d', B.RenamingContext.toSMT «Δ» v = some d' := by
            simp only [B.RenamingContext.toSMT, hbdom, Option.pure_def]; exact ⟨_, rfl⟩
          obtain ⟨d', hd'⟩ := h_toSMT_v
          have h_toSMTOnFV_v : B.RenamingContext.toSMTOnFV «Δ» (Term.lambda vs D P) v = some d' := by
            simp only [RenamingContext.toSMTOnFV, RenamingContext.toSMT,
              B.RenamingContext.restrictToFV_eq_of_mem hv_lambda, Option.pure_def, Option.bind_eq_bind,
              hbdom, Option.bind_some]
            rw [B.RenamingContext.toSMT, Option.pure_def, Option.bind_eq_bind, hbdom, Option.bind_some] at hd'
            exact hd'
          have hΔ_D_eval_v : Δ_D_eval v = some d' := Δ_D_eval_extends h_toSMTOnFV_v
          by_contra hv_not_used
          exact absurd (Δ_D_eval_none_St₂ v (fun h => hv_not_used (St₂_sub_St₃ v h)))
            (by rw [hΔ_D_eval_v]; simp)
        show (if v ∈ vs then _ else if v ∈ used_St₃ then Δ_ctx v else none) = some d
        rw [if_neg hvs, if_pos hv_used]
        rw [Δ_ctx_source v hv_fv hvs]
        have hΔ_ext_x_eq : Δ_ext_x v = «Δ» v := by
          show Function.updates «Δ» vs _ v = «Δ» v; exact Function.updates_of_not_mem «Δ» vs _ v hvs
        simpa only [B.RenamingContext.toSMT, hΔ_ext_x_eq, Option.pure_def, Option.bind_eq_bind] using hv_smt
    · have : B.RenamingContext.toSMTOnFV Δ_ext_x P v = none := by
        simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
          B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_fv]
      rw [this] at hv_eq; exact absurd hv_eq (not_eq_of_beq_eq_false rfl)
  -- Step E.2: none_out for Δ₀_hybrid_x
  have Δ₀_hybrid_x_none_St₃ : ∀ v ∉ used_St₃, Δ₀_hybrid_x v = none := by
    intro v hv
    show (if v ∈ vs then Δ_D_ext_x v else if v ∈ used_St₃ then Δ_ctx v else none) = none
    have hv_not_vs : v ∉ vs := fun hvs => hv (St₂_sub_St₃ v (vars_used_vs v hvs))
    rw [if_neg hv_not_vs, if_neg hv]
  -- Step F: Invoke P_enc_total
  obtain ⟨Δ_P_x, hcov_Px, denT_x', Δ_P_x_extends, hden_Px, hRDom_x⟩ :=
    P_enc_total Δ_ext_x Δ_fv_P_x Δ₀_hybrid_x Δ₀_hybrid_ext_P_x Δ₀_hybrid_x_none_St₃
      P_val hP_val h_den_P_x
  have hdenT_x'_ty : denT_x'.snd.fst = β.toSMTType := hRDom_x.1
  have hdenT_x'_retract : retract β denT_x'.fst = P_val := hRDom_x.2
  have hdenT_x'_mem : denT_x'.fst ∈ ⟦β.toSMTType⟧ᶻ := hdenT_x'_ty ▸ denT_x'.snd.snd
  -- Step G: Decompose body into D_enc_app ∧ˢ' EQ_part.
  set body : SMT.Term :=
    ((@ˢD_enc) (SMT.Term.var z).fst ∧ˢ
      ((SMT.Term.var z).snd =ˢ
        SMT.substList vs (toDestPair vs (SMT.Term.var z).fst) P_enc)) with body_def
  set D_enc_app_term : SMT.Term :=
    (@ˢD_enc) (SMT.Term.var z).fst with D_enc_app_def
  set eq_part : SMT.Term :=
    ((SMT.Term.var z).snd =ˢ
      SMT.substList vs (toDestPair vs (SMT.Term.var z).fst) P_enc) with eq_part_def
  have hcov_D_app_upd : ∀ W : SMT.Dom,
      SMT.RenamingContext.CoversFV (Function.update Δ_ctx z (some W)) D_enc_app_term := by
    intro W x hx
    have hx_in_body : x ∈ SMT.fv body := by
      simp only [body_def, D_enc_app_def, SMT.fv, List.mem_append] at hx ⊢
      left; exact hx
    exact hcov_body_upd W x hx_in_body
  have hcov_eq_part_upd : ∀ W : SMT.Dom,
      SMT.RenamingContext.CoversFV (Function.update Δ_ctx z (some W)) eq_part := by
    intro W x hx
    have hx_in_body : x ∈ SMT.fv body := by
      simp only [body_def, eq_part_def, SMT.fv, List.mem_append] at hx ⊢
      right; exact hx
    exact hcov_body_upd W x hx_in_body
  -- Body decomposition: body.abstract = (D_enc_app.abstract) ∧ˢ' (eq_part.abstract).
  have hbody_decomp :
      ⟦body.abstract (Function.update Δ_ctx z (some Wxy)) (hcov_body_upd Wxy)⟧ˢ =
      ⟦(D_enc_app_term.abstract (Function.update Δ_ctx z (some Wxy)) (hcov_D_app_upd Wxy)) ∧ˢ'
        (eq_part.abstract (Function.update Δ_ctx z (some Wxy)) (hcov_eq_part_upd Wxy))⟧ˢ := by
    simp only [body_def, D_enc_app_def, eq_part_def, SMT.Term.abstract]
  -- Step H: Get Dapp via funDenoteAppAtFst.
  obtain ⟨_, Dapp, hDapp_ty, hDapp_val, hDapp_den⟩ :=
    funDenoteAppAtFst (Δctx := Δ_ctx) (t := D_enc) (x := z)
      (α := τ.toSMTType) (β := SMTType.bool) (γ := β.toSMTType) (Y := denD_val)
      hcov_D_upd den_D_upd_eq denD_val_type denD_val_func Wxy hWxy_ty hWxy_mem
  have hDapp_den' : ⟦D_enc_app_term.abstract (Function.update Δ_ctx z (some Wxy))
                      (hcov_D_app_upd Wxy)⟧ˢ = some Dapp := by
    simp only [D_enc_app_def]
    convert hDapp_den using 1
  have hDapp_mem_𝔹 : Dapp.fst ∈ 𝔹 := by have := Dapp.snd.snd; rw [hDapp_ty] at this; exact this
  -- Step I: DIRECT transfer substList from Δ_ctx[z↦Wxy] to Δ_P_x[z↦Wxy]
  have hΔ_agree_substList_direct : SMT.RenamingContext.AgreesOnFV
      (Function.update Δ_ctx z (some Wxy)) (Function.update Δ_P_x z (some Wxy))
      (SMT.substList vs (toDestPair vs (SMT.Term.var z).fst) P_enc) := by
    intro v hv; by_cases hvz : v = z
    · subst hvz; simp [Function.update_self]
    · rw [Function.update_of_ne hvz, Function.update_of_ne hvz]
      have hv_not_vs := fv_substList_disj_vs v hv hvz
      rcases SMT_mem_fv_substList hv with hv_P | ⟨t, ht, hv_t⟩
      · -- v ∈ fv(P_enc), v ∉ vs
        have hv_used : v ∈ used_St₃ := fv_P_enc_used v hv_P
        have hΔ₀_v : Δ₀_hybrid_x v = Δ_ctx v := by
          show (if v ∈ vs then _ else if v ∈ used_St₃ then Δ_ctx v else none) = Δ_ctx v
          rw [if_neg hv_not_vs, if_pos hv_used]
        cases hctx : Δ_ctx v with
        | some d =>
          have hΔ_P_x_v : Δ_P_x v = some d := Δ_P_x_extends (hΔ₀_v ▸ hctx)
          exact hΔ_P_x_v.symm
        | none =>
          exfalso
          -- v ∈ fv(substList ...) ⊆ fv(eq_part) ⊆ fv(body).
          have hv_eq_part : v ∈ SMT.fv eq_part := by
            simp only [eq_part_def, SMT.fv, List.mem_append]
            right; exact hv
          have hv_body : v ∈ SMT.fv body := by
            simp only [body_def, SMT.fv, List.mem_append]
            right; exact hv_eq_part
          have hcov := hcov_body_upd Wxy v hv_body
          rw [Function.update_of_ne hvz, hctx] at hcov; exact absurd hcov (by simp)
      · exact absurd (SMT_fv_toDestPair_subset_base
          (t₀ := (SMT.Term.var z).fst)
          (by intro w hw; simp only [SMT.fv, List.mem_singleton] at hw; exact hw)
          ht hv_t) hvz
  have hcov_substList_Px : SMT.RenamingContext.CoversFV
      (Function.update Δ_P_x z (some Wxy)) (SMT.substList vs (toDestPair vs (SMT.Term.var z).fst) P_enc) := by
    intro v hv; by_cases hvz : v = z
    · subst hvz; simp [Function.update_self]
    · rw [Function.update_of_ne hvz]
      have hagr := hΔ_agree_substList_direct hv
      rw [Function.update_of_ne hvz, Function.update_of_ne hvz] at hagr; rw [← hagr]
      have := hcov_substList_upd Wxy v hv; rwa [Function.update_of_ne hvz] at this
  -- Step J: Setup for abstract_substList_denote.
  have hΔ_Px_vs_isSome : ∀ (i : Fin vs.length), (Δ_P_x vs[i]).isSome = true := by
    intro ⟨i, hi⟩; have hvi_mem : vs[i] ∈ vs := List.getElem_mem hi
    have hΔ_ext_x_vi : (Δ_ext_x vs[i]).isSome = true := by
      show (Function.updates «Δ» vs _ vs[i]).isSome = true
      rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup, dif_pos hvi_mem]
      simp only [List.getElem_ofFn, Option.isSome]
    obtain ⟨bval, hbval⟩ := Option.isSome_iff_exists.mp hΔ_ext_x_vi
    obtain ⟨V, τ_v, hV⟩ := bval
    have htoSMT_some : ∃ d, B.RenamingContext.toSMT Δ_ext_x vs[i] = some d := by
      simp only [B.RenamingContext.toSMT, hbval, Option.pure_def]; exact ⟨_, rfl⟩
    obtain ⟨d, hd⟩ := htoSMT_some
    have hΔ_D_ext_x_vi : Δ_D_ext_x vs[i] = some d := by
      show Function.updates Δ_D_eval vs _ vs[i] = some d
      rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup, dif_pos hvi_mem]
      simp only [List.getElem_ofFn, Fin.getElem_fin, List.getElem_idxOf]; exact hd
    have hΔ₀_hybrid_vi : Δ₀_hybrid_x vs[i] = some d := by
      show (if vs[i] ∈ vs then Δ_D_ext_x vs[i] else _) = some d
      rw [if_pos hvi_mem]; exact hΔ_D_ext_x_vi
    exact Option.isSome_iff_exists.mpr ⟨d, Δ_P_x_extends hΔ₀_hybrid_vi⟩
  let Ds_x : List SMT.Dom := List.ofFn fun i : Fin vs.length => (Δ_P_x vs[i]).get (hΔ_Px_vs_isSome i)
  have h_cov_upd_x : SMT.RenamingContext.CoversFV
      (Function.updates (Function.update Δ_P_x z (some Wxy)) vs (Ds_x.map Option.some)) P_enc := by
    intro v hv; by_cases hvs : v ∈ vs
    · rw [Function.updates_eq_if (by rw [List.length_map, List.length_ofFn]) vs_nodup, dif_pos hvs]; simp
    · rw [Function.updates_of_not_mem _ vs _ _ hvs,
        Function.update_of_ne (by intro heq; exact z_not_fv_P (heq ▸ hv))]; exact hcov_Px v hv
  have hlen_xt' : vs.length = (toDestPair vs (SMT.Term.var z).fst).length := by
    rw [toDestPair_length_gen vs (SMT.Term.var z).fst (SMT.Term.var z).fst [] vs_nemp]; simp
  have hlen_xd' : vs.length = Ds_x.length := by simp [Ds_x, List.length_ofFn]
  -- Have to compute the canonical decomposition of Wxy.fst.π₁ for toDestPair_denote_gen.
  have hretract_Wxy_π₁ : retract τ Wxy.fst.π₁ = xy.π₁ := by
    rw [hWxy_π₁]; exact retract_of_canonical τ hx_mem
  -- For abstract_substList_denote, we need a SMT.Dom whose .fst = Wxy.fst.π₁ and .snd.fst = τ.toSMTType.
  -- We use `(Term.var z).fst` which denotes to ⟨Wxy.fst.π₁, τ.toSMTType, _⟩.
  have hvar_z_π₁_mem : Wxy.fst.π₁ ∈ ⟦τ.toSMTType⟧ᶻ := by
    rw [hWxy_π₁]; exact ZFSet.fapply_mem_range _ _
  let var_z_fst_dom : SMT.Dom := ⟨Wxy.fst.π₁, τ.toSMTType, hvar_z_π₁_mem⟩
  have hcov_var_z_fst : SMT.RenamingContext.CoversFV
      (Function.update Δ_P_x z (some Wxy)) (SMT.Term.var z).fst := by
    intro v hv
    simp only [SMT.fv] at hv
    rw [List.mem_singleton] at hv
    subst hv; simp [Function.update_self]
  have hden_var_z_fst : ⟦((SMT.Term.var z).fst).abstract
      (Function.update Δ_P_x z (some Wxy)) hcov_var_z_fst⟧ˢ = some var_z_fst_dom := by
    simp only [SMT.Term.abstract, SMT.denote, Function.update_self]
    rfl
  -- Need Wxy.fst.π₁ also has arity vs.length.
  have hWxy_π₁_hasArity : Wxy.fst.π₁.hasArity vs.length :=
    hasArity_of_mem_toSMTZFSet τ_hasArity hvar_z_π₁_mem
  -- Step K: Apply abstract_substList_denote.
  have h_eq_x := SMT.RenamingContext.abstract_substList_denote P_enc vs
    (toDestPair vs (SMT.Term.var z).fst) Ds_x hlen_xt' hlen_xd' vs_nodup hvs_not_bv_P
    (toDestPair_bv_nil_base (t₀ := (SMT.Term.var z).fst) (by simp [SMT.bv]))
    (fun t ht w hw hbv => by
      rw [SMT_fv_toDestPair_subset_base (t₀ := (SMT.Term.var z).fst)
        (by intro w' hw'; simp only [SMT.fv, List.mem_singleton] at hw'; exact hw') ht hw] at hbv
      exact z_not_bv_P hbv)
    (by
      -- toDestPair vs (.fst (.var z)) contains no .none element
      -- Generalize the auxiliary lemma to work with t₀ := (.var z).fst.
      suffices h : ∀ (vs : List SMT.𝒱) (zp : SMT.Term) (acc : List SMT.Term) (d : SMT.Term),
          zp ≠ SMT.Term.none → (∀ a ∈ acc, a ≠ SMT.Term.none) → d ≠ SMT.Term.none →
          ∀ t ∈ toDestPair vs zp acc d, t ≠ SMT.Term.none from by
        exact h vs (SMT.Term.var z).fst [] (SMT.Term.var z).fst (by simp)
          (fun _ h' => absurd h' List.not_mem_nil) (by simp)
      intro vs'; induction vs' with
      | nil => intro _ acc _ _ hacc _; exact hacc
      | cons x xs ih =>
        intro zp acc d hzp hacc hd
        cases xs with
        | nil =>
          unfold toDestPair; intro t ht
          rcases List.mem_cons.mp ht with rfl | ht
          · exact hzp
          · exact hacc t ht
        | cons y ys =>
          unfold toDestPair
          exact ih (.fst d) (.snd d :: acc) (.fst d) (by simp)
            (fun a ha => by
              rcases List.mem_cons.mp ha with rfl | ha
              · simp
              · exact hacc a ha)
            (by simp))
    (fun t ht w hw => by
      rw [SMT_fv_toDestPair_subset_base (t₀ := (SMT.Term.var z).fst)
        (by intro w' hw'; simp only [SMT.fv, List.mem_singleton] at hw'; exact hw') ht hw]
      exact z_not_vs)
    (by
      intro i hi_x hi_t hi_d
      have hcov_ti : SMT.RenamingContext.CoversFV
          (Function.update Δ_P_x z (some Wxy)) (toDestPair vs (SMT.Term.var z).fst)[i] := by
        intro v hv
        have hvz := SMT_fv_toDestPair_subset_base (t₀ := (SMT.Term.var z).fst)
          (by intro w' hw'; simp only [SMT.fv, List.mem_singleton] at hw'; exact hw')
          (List.getElem_mem hi_t) hv
        subst hvz; simp [Function.update_self]
      refine ⟨hcov_ti, ?_⟩
      obtain ⟨hcov_j, D_j, hden_j, hfst_j, hty_j⟩ :=
        toDestPair_denote_gen τ vs (SMT.Term.var z).fst var_z_fst_dom
          (Function.update Δ_P_x z (some Wxy)) [] [] vs_nemp
          hcov_var_z_fst hden_var_z_fst rfl hvar_z_π₁_mem τ_hasArity rfl (by simp) i hi_x hi_t
      rw [SMT.RenamingContext.denote_abstract_proof_irrel _ _ hcov_ti hcov_j, hden_j]
      have hvi_mem : vs[i] ∈ vs := List.getElem_mem hi_x
      have hΔ_ext_x_vi : Δ_ext_x vs[i] = some (x_fin ⟨i, hi_x⟩) := by
        show Function.updates «Δ» vs _ vs[i] = _
        rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup, dif_pos hvi_mem]
        simp only [List.getElem_ofFn]
        simp [List.idxOf_getElem vs_nodup]
      obtain ⟨d_smt, hd_smt⟩ : ∃ d, B.RenamingContext.toSMT Δ_ext_x vs[i] = some d := by
        simp only [B.RenamingContext.toSMT, hΔ_ext_x_vi, Option.pure_def]; exact ⟨_, rfl⟩
      have htoSMT_unf : B.RenamingContext.toSMT Δ_ext_x vs[i] = some d_smt := hd_smt
      rw [B.RenamingContext.toSMT, Option.pure_def, Option.bind_eq_bind, hΔ_ext_x_vi, Option.bind_some] at htoSMT_unf
      have hd_inj := Option.some_injective _ htoSMT_unf
      have hd_ty : d_smt.snd.fst = (τ.get vs.length ⟨i, hi_x⟩).toSMTType :=
        (congr_arg (·.snd.fst) hd_inj).symm
      have hd_retract : retract (τ.get vs.length ⟨i, hi_x⟩) d_smt.fst =
          (retract τ Wxy.fst.π₁).get vs.length ⟨i, hi_x⟩ := by
        have hfst_inj := congr_arg (·.fst) hd_inj; dsimp at hfst_inj
        rw [← hfst_inj, hretract_Wxy_π₁]
        exact retract_of_canonical (τ.get vs.length ⟨i, hi_x⟩)
          (get_mem_type_of_isTuple hxy_π₁_arity τ_hasArity hx_mem)
      have hΔ_D_ext_x_vi : Δ_D_ext_x vs[i] = some d_smt := by
        show Function.updates Δ_D_eval vs _ vs[i] = some d_smt
        rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup, dif_pos hvi_mem]
        simp only [List.getElem_ofFn, Fin.getElem_fin, List.getElem_idxOf]; exact hd_smt
      have hΔ₀_hybrid_vi : Δ₀_hybrid_x vs[i] = some d_smt := by
        show (if vs[i] ∈ vs then Δ_D_ext_x vs[i] else _) = some d_smt
        rw [if_pos hvi_mem]; exact hΔ_D_ext_x_vi
      have hΔ_Px_vi : Δ_P_x vs[i] = some d_smt := Δ_P_x_extends hΔ₀_hybrid_vi
      have hWi_mem : Wxy.fst.π₁.get vs.length ⟨i, hi_x⟩ ∈ ⟦(τ.get vs.length ⟨i, hi_x⟩).toSMTType⟧ᶻ :=
        get_mem_toSMTZFSet hWxy_π₁_hasArity τ_hasArity hvar_z_π₁_mem
      have hd_fst : d_smt.fst = Wxy.fst.π₁.get vs.length ⟨i, hi_x⟩ := by
        have hd_mem : d_smt.fst ∈ ⟦(τ.get vs.length ⟨i, hi_x⟩).toSMTType⟧ᶻ := hd_ty ▸ d_smt.snd.snd
        have h_retract_eq : retract (τ.get vs.length ⟨i, hi_x⟩) d_smt.fst =
            retract (τ.get vs.length ⟨i, hi_x⟩) (Wxy.fst.π₁.get vs.length ⟨i, hi_x⟩) := by
          rw [hd_retract, retract_get_comm hWxy_π₁_hasArity τ_hasArity hvar_z_π₁_mem]
        calc d_smt.fst
            = fapply (BType.canonicalIsoSMTType (τ.get vs.length ⟨i, hi_x⟩)).1
                (is_func_is_pfunc (BType.canonicalIsoSMTType _).2.1)
                ⟨retract (τ.get vs.length ⟨i, hi_x⟩) d_smt.fst, _⟩ := (canonical_of_retract _ hd_mem).symm
          _ = fapply (BType.canonicalIsoSMTType (τ.get vs.length ⟨i, hi_x⟩)).1
                (is_func_is_pfunc (BType.canonicalIsoSMTType _).2.1)
                ⟨retract (τ.get vs.length ⟨i, hi_x⟩) (Wxy.fst.π₁.get vs.length ⟨i, hi_x⟩), _⟩ := by
              simp [h_retract_eq]
          _ = Wxy.fst.π₁.get vs.length ⟨i, hi_x⟩ := canonical_of_retract _ hWi_mem
      have hD_j_eq : D_j = d_smt := by
        rcases D_j with ⟨z1, τ1, hz1⟩; rcases d_smt with ⟨z2, τ2, hz2⟩
        exact SMT.RenamingContext.Dom_ext'
          (show z1 = z2 by simpa using hfst_j.trans hd_fst.symm)
          (show τ1 = τ2 by simpa using hty_j.trans hd_ty.symm)
      have hDs_eq : Ds_x[i] = d_smt := by
        simp only [Ds_x, List.getElem_ofFn, Fin.getElem_fin, hΔ_Px_vi, Option.get_some]
      rw [show D_j = Ds_x[i] from hD_j_eq.trans hDs_eq.symm])
    hcov_substList_Px h_cov_upd_x
  -- Step L: updates agrees with Δ_P_x on fv(P_enc)
  have h_upd_agree_x : SMT.RenamingContext.AgreesOnFV
      (Function.updates (Function.update Δ_P_x z (some Wxy)) vs (Ds_x.map Option.some)) Δ_P_x P_enc := by
    intro v hv; by_cases hvs : v ∈ vs
    · rw [Function.updates_eq_if (by rw [List.length_map, List.length_ofFn]) vs_nodup, dif_pos hvs]
      simp only [Ds_x, List.getElem_map, List.getElem_ofFn, Fin.getElem_fin, List.getElem_idxOf]
      exact Option.some_get _
    · rw [Function.updates_of_not_mem _ vs _ _ hvs,
        Function.update_of_ne (by intro heq; exact z_not_fv_P (heq ▸ hv))]
  have h_eq2_x := SMT.RenamingContext.denote_congr_of_agreesOnFV
    (h1 := h_cov_upd_x) (h2 := hcov_Px) h_upd_agree_x
  unfold SMT.RenamingContext.denote at h_eq2_x
  -- Step M: Combine to derive substList denotation under (Δ_P_x[z↦Wxy]) = denT_x'.
  have hsubst_at_ΔPx : ⟦(SMT.substList vs (toDestPair vs (SMT.Term.var z).fst) P_enc).abstract
      (Function.update Δ_P_x z (some Wxy)) hcov_substList_Px⟧ˢ = some denT_x' := by
    rw [h_eq_x, h_eq2_x]; exact hden_Px
  -- Then transfer to under (Δ_ctx[z↦Wxy]).
  have hsubst_at_Δctx : ⟦(SMT.substList vs (toDestPair vs (SMT.Term.var z).fst) P_enc).abstract
      (Function.update Δ_ctx z (some Wxy)) (hcov_substList_upd Wxy)⟧ˢ = some denT_x' := by
    have h_transfer := SMT.RenamingContext.denote_congr_of_agreesOnFV
      (h1 := hcov_substList_upd Wxy) (h2 := hcov_substList_Px) hΔ_agree_substList_direct
    unfold SMT.RenamingContext.denote at h_transfer
    rw [h_transfer]; exact hsubst_at_ΔPx
  -- Step N: Compute denotation of (Term.var z).snd at Wxy.
  let var_z_snd_dom : SMT.Dom := ⟨Wxy.fst.π₂, β.toSMTType, by
    rw [hWxy_π₂]; exact ZFSet.fapply_mem_range _ _⟩
  have hcov_var_z_snd : SMT.RenamingContext.CoversFV
      (Function.update Δ_ctx z (some Wxy)) (SMT.Term.var z).snd := by
    intro v hv
    simp only [SMT.fv] at hv
    rw [List.mem_singleton] at hv
    subst hv; simp [Function.update_self]
  have hden_var_z_snd : ⟦((SMT.Term.var z).snd).abstract
      (Function.update Δ_ctx z (some Wxy)) hcov_var_z_snd⟧ˢ = some var_z_snd_dom := by
    simp only [SMT.Term.abstract, SMT.denote, Function.update_self]
    rfl
  -- Step O: Compute denotation of EQ part.
  have hcov_substList_in_eq : SMT.RenamingContext.CoversFV
      (Function.update Δ_ctx z (some Wxy))
      (SMT.substList vs (toDestPair vs (SMT.Term.var z).fst) P_enc) := hcov_substList_upd Wxy
  -- Step P: Forward and Backward proof using the chain above.
  refine Iff.intro ?fwd ?bwd
  case fwd =>
    intro hbody_fst
    refine ⟨P_val, hP_val, hP_go_den, ?_⟩
    -- Goal: P_val = xy.π₂.
    -- Prepare type-match.
    have hty_match : var_z_snd_dom.snd.fst = denT_x'.snd.fst := by
      show β.toSMTType = _; rw [hdenT_x'_ty]
    -- The abstract of `(.var z).snd =ˢ substList` reduces (definitionally) to
    -- `(.var z).snd.abstract _ _ =ˢ' substList.abstract _ _` modulo proof irrelevance
    -- on the coverage proofs. We identify the result via `denote_abstract_proof_irrel`.
    have hDeq_eq : ⟦eq_part.abstract (Function.update Δ_ctx z (some Wxy))
                    (hcov_eq_part_upd Wxy)⟧ˢ = ⟦((SMT.Term.var z).snd).abstract
                    (Function.update Δ_ctx z (some Wxy)) hcov_var_z_snd =ˢ'
                  (SMT.substList vs (toDestPair vs (SMT.Term.var z).fst) P_enc).abstract
                    (Function.update Δ_ctx z (some Wxy)) hcov_substList_in_eq⟧ˢ := by
      simp only [eq_part_def, SMT.Term.abstract]
    -- Use lambda_denote_eq_some_bool to get Deq.
    obtain ⟨Deq, hDeq_den_raw, hDeq_ty⟩ :=
      lambda_denote_eq_some_bool hden_var_z_snd hsubst_at_Δctx hty_match
    have hDeq_den' : ⟦eq_part.abstract (Function.update Δ_ctx z (some Wxy))
                      (hcov_eq_part_upd Wxy)⟧ˢ = some Deq := by
      rw [hDeq_eq]; exact hDeq_den_raw
    -- Now we have body = D_enc_app ∧ˢ EQ_part. Apply AND decomposition.
    have hbody_val_zftrue : ⟦(D_enc_app_term.abstract (Function.update Δ_ctx z (some Wxy))
                              (hcov_D_app_upd Wxy)) ∧ˢ'
                            (eq_part.abstract (Function.update Δ_ctx z (some Wxy))
                              (hcov_eq_part_upd Wxy))⟧ˢ = some body_val := by
      rw [← hbody_decomp]; exact hbody_val
    have hDp_Dq_true :=
      denote_and_both_zftrue_of_zftrue (p := D_enc_app_term.abstract _ (hcov_D_app_upd Wxy))
        (q := eq_part.abstract _ (hcov_eq_part_upd Wxy)) (Dp := Dapp) (Dq := Deq)
        hDapp_den' hDapp_ty hDeq_den' hDeq_ty hbody_val_zftrue hbody_fst
    obtain ⟨_, hDeq_true⟩ := hDp_Dq_true
    -- 2) From EQ_part = zftrue, derive var_z_snd_dom.fst = denT_x'.fst.
    have hfst_eq : var_z_snd_dom.fst = denT_x'.fst :=
      denote_eq_true_implies_fst_eq hden_var_z_snd hsubst_at_Δctx hty_match
        hDeq_den_raw hDeq_true
    -- hfst_eq : var_z_snd_dom.fst = denT_x'.fst, i.e., Wxy.fst.π₂ = denT_x'.fst.
    -- 3) Apply retract β to both sides.
    have hretract_eq : retract β Wxy.fst.π₂ = retract β denT_x'.fst := by
      change retract β var_z_snd_dom.fst = _; rw [hfst_eq]
    -- 4) retract β Wxy.fst.π₂ = xy.π₂ (by hWxy_π₂ + retract_of_canonical).
    have hretract_Wxy_π₂ : retract β Wxy.fst.π₂ = xy.π₂ := by
      rw [hWxy_π₂]; exact retract_of_canonical β hy_mem
    -- 5) Combine: xy.π₂ = retract β Wxy.fst.π₂ = retract β denT_x'.fst = P_val.
    have : xy.π₂ = P_val := by rw [← hretract_Wxy_π₂, hretract_eq]; exact hdenT_x'_retract
    exact this.symm
  case bwd =>
    rintro ⟨Px, hPx_mem, hPx_den, hPx_eq⟩
    -- From hPx_den : ⟦P.uncurry x_fin⟧ᴮ = some ⟨Px, β, hPx_mem⟩, and
    -- hP_go_den : ⟦same⟧ᴮ = some ⟨P_val, β, hP_val⟩ get Px = P_val.
    have hPx_eq_P_val : Px = P_val := by
      have h1 : (⟨Px, β, hPx_mem⟩ : B.Dom) = ⟨P_val, β, hP_val⟩ := by
        have := hPx_den.symm.trans hP_go_den
        exact Option.some.inj this
      exact congrArg (·.fst) h1
    subst hPx_eq_P_val
    -- Now: hPx_eq : P_val = xy.π₂, so we want body_val.fst = zftrue.
    -- Strategy: derive Dapp.fst = zftrue (from xy.π₁ ∈ 𝒟_val + denD_val_retract),
    -- and Deq.fst = zftrue (from var_z_snd_dom.fst = denT_x'.fst, using hPx_eq via hdenT_x'_retract).
    -- Then AND construction gives body has fst = zftrue, equals body_val.
    -- Step 1: Dapp.fst = zftrue.
    have hDapp_true : Dapp.fst = zftrue := by
      have hxy_π₁_in_retract : xy.π₁ ∈ retract τ.set denD_val.fst := by
        rw [denD_val_retract]; exact hxy_𝒟
      rw [retract, ZFSet.mem_sep] at hxy_π₁_in_retract
      obtain ⟨_, hxy_retract_pred⟩ := hxy_π₁_in_retract
      rw [dif_pos hx_mem, dif_pos denD_val_func] at hxy_retract_pred
      -- hxy_retract_pred : ↑(fapply denD_val.fst _ ⟨canonical(τ, xy.π₁), _⟩) = zftrue
      rw [hDapp_val]
      -- Goal: ↑(fapply denD_val.fst _ ⟨Wxy.fst.π₁, _⟩) = zftrue
      -- Bridge via hWxy_π₁ : Wxy.fst.π₁ = canonical(τ, xy.π₁) on the inner Subtype value.
      convert hxy_retract_pred using 3
      apply Subtype.ext
      exact hWxy_π₁
    -- Step 2: Wxy.fst.π₂ = denT_x'.fst (because P_val = xy.π₂).
    have hπ₂_eq_denT : Wxy.fst.π₂ = denT_x'.fst := by
      -- canonical(β, xy.π₂) = denT_x'.fst, since both have type β.toSMTType and same retract.
      rw [hWxy_π₂]
      -- LHS: canonical(β, xy.π₂)  RHS: denT_x'.fst
      -- Use that retract β (canonical β xy.π₂) = xy.π₂ = P_val = retract β denT_x'.fst,
      -- and canonical_of_retract gives both equal canonical(β, retract β denT_x'.fst).
      have h_retract_lhs : retract β (ZFSet.fapply (BType.canonicalIsoSMTType β).1
          (ZFSet.is_func_is_pfunc hζ_β)
          ⟨xy.π₂, by rwa [ZFSet.is_func_dom_eq hζ_β]⟩).1 = xy.π₂ :=
        retract_of_canonical β hy_mem
      have h_retract_rhs : retract β denT_x'.fst = xy.π₂ := by rw [hdenT_x'_retract]; exact hPx_eq
      have h_retract_eq : retract β (ZFSet.fapply (BType.canonicalIsoSMTType β).1
          (ZFSet.is_func_is_pfunc hζ_β)
          ⟨xy.π₂, by rwa [ZFSet.is_func_dom_eq hζ_β]⟩).1 = retract β denT_x'.fst := by
        rw [h_retract_lhs, h_retract_rhs]
      have h_lhs_mem : (ZFSet.fapply (BType.canonicalIsoSMTType β).1
          (ZFSet.is_func_is_pfunc hζ_β)
          ⟨xy.π₂, by rwa [ZFSet.is_func_dom_eq hζ_β]⟩).1 ∈ ⟦β.toSMTType⟧ᶻ :=
        ZFSet.fapply_mem_range _ _
      calc (ZFSet.fapply (BType.canonicalIsoSMTType β).1
            (ZFSet.is_func_is_pfunc hζ_β)
            ⟨xy.π₂, by rwa [ZFSet.is_func_dom_eq hζ_β]⟩).1
          = fapply (BType.canonicalIsoSMTType β).1
              (is_func_is_pfunc (BType.canonicalIsoSMTType β).2.1)
              ⟨retract β _, _⟩ := (canonical_of_retract β h_lhs_mem).symm
        _ = fapply (BType.canonicalIsoSMTType β).1
              (is_func_is_pfunc (BType.canonicalIsoSMTType β).2.1)
              ⟨retract β denT_x'.fst, _⟩ := by simp [h_retract_eq]
        _ = denT_x'.fst := canonical_of_retract β hdenT_x'_mem
    -- Step 3: EQ_part.abstract denotes to a value with fst = zftrue.
    have hty_match : var_z_snd_dom.snd.fst = denT_x'.snd.fst := by
      show β.toSMTType = _; rw [hdenT_x'_ty]
    have hDeq_eq : ⟦eq_part.abstract (Function.update Δ_ctx z (some Wxy))
                    (hcov_eq_part_upd Wxy)⟧ˢ = ⟦((SMT.Term.var z).snd).abstract
                    (Function.update Δ_ctx z (some Wxy)) hcov_var_z_snd =ˢ'
                  (SMT.substList vs (toDestPair vs (SMT.Term.var z).fst) P_enc).abstract
                    (Function.update Δ_ctx z (some Wxy)) hcov_substList_in_eq⟧ˢ := by
      simp only [eq_part_def, SMT.Term.abstract]
    have hDeq_built' : ⟦eq_part.abstract (Function.update Δ_ctx z (some Wxy))
                        (hcov_eq_part_upd Wxy)⟧ˢ =
                      some ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
      rw [hDeq_eq]
      exact denote_eq_eq_zftrue_of_fst_eq hden_var_z_snd hsubst_at_Δctx hty_match
        (by show var_z_snd_dom.fst = denT_x'.fst; exact hπ₂_eq_denT)
    -- Step 4: AND construction: body's denotation = zftrue.
    have hand_built := denote_and_eq_zftrue_of_some_zftrue hDapp_den' hDapp_ty hDapp_true
      hDeq_built' rfl rfl
    -- Combine with hbody_decomp + hbody_val.
    have hbody_decomp' :
        ⟦body.abstract (Function.update Δ_ctx z (some Wxy)) (hcov_body_upd Wxy)⟧ˢ =
        some ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
      rw [hbody_decomp]; exact hand_built
    -- hbody_val + hbody_decomp' give body_val = ⟨zftrue, _, _⟩.
    have h_body_val_eq : body_val = ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
      have := hbody_val.symm.trans hbody_decomp'
      exact Option.some.inj this
    rw [h_body_val_eq]
