import SMT.Reasoning.Basic.CollectCaseHelpers
import SMT.Reasoning.Basic.EncodeTermCorrectPFun
import SMT.Reasoning.Basic.LambdaCaseHelpers
import SMT.Reasoning.Axioms

open Std.Do B SMT ZFSet

/-!
# Correctness of `encodeTerm` for the `lambda` constructor

The lambda case encodes `λ vs ∈ D . P` as an SMT term of type `τ → option γ`.
Structurally analogous to `collect_case` but produces a partial function rather
than a characteristic function.

## Differences from collect

1. **Option-valued codomain**: lambda produces `.fun τ (.option γ)` rather than
   `.fun τ .bool`. The SMT term is `λ z. ite z∈D (some P) (none$γ)` instead of
   `λ z. ite z∈D P false`.
2. **P-before-D encoder order**: the encoder evaluates `P` first (with bound
   variables `vs` already in context), then `D`. The state chain shifts.
3. **Richer PHOAS semantics** (`B/SemanticsPHOAS.lean:546`): extracting `den_D`
   from `den_t` navigates a multi-layer dite/match that enforces non-empty
   domain, type consistency, and computes the return type from a witness.

The encoder (see `Encoder/Encoder.lean`, lines 156–186) has two sub-branches on
the type of `D`:
- `.fun τ .bool` (D is a set) — the case that arises from B-typing, since
  `B.Typing.lambda` constrains `D` to be a set.
- `.fun α (.option β)` (D is a function) — unreachable in well-typed programs.

A full proof only needs to handle the "D is a set" branch, closely mirroring
`collect_case`'s structure.
-/

/-! ### Helpers for `lambda_case` sub-obligations

The lambda case in `encodeTerm_spec.lambda_case` (below) splits into a chosen
branch (𝒟 ≠ ∅) and a defaults branch (𝒟 = ∅). Each branch has two structural
sub-obligations: an RDom relation (or contradiction in defaults) and a
totality clause for alternative valuations. Together these mirror the
`collect_case` helpers in `CollectCaseHelpers.lean` but with the AND/EQ
lambda body replacing collect's ITE body.

Helpers:
* `lambda_chosen_retract_eq` mirrors `retract_lamVal_eq_collect`'s Step 3
  for the AND/EQ body: derive the bijection between B-side sep-product
  elements and zftrue evaluations of the SMT lambda.
* `lambda_chosen_totality` mirrors `collect_case`'s totality branch:
  assemble `Δ'_alt`, `denT_alt` from D_RDom.2 + P_enc_total via
  `Function.update` + `denote_exists_of_typing_fv`.
* `lambda_defaults_retract_empty_contradiction` unfolds the SMT lambda body
  via `ZFSet.fapply_lambda_eq_iff` + `funAbstractGoSingle` to derive False
  from `hDapp_not_zftrue ∧ hxy_cond`.
* `lambda_defaults_totality` mirrors `lambda_chosen_totality` with the
  empty-domain hypothesis. -/

open Classical B in
/--
Chosen-branch RDom relation for the lambda case.

Closes the `8th-conjunct.RDom` goal at the chosen-branch (𝒟 ≠ ∅) call site.
The conclusion is `⟨T_chosen, ⟨(τ ×ᴮ β).set, hT⟩⟩ ≘ᶻ denT'`, where
`T_chosen` is the B-level sep-product `(𝒟_val.prod ⟦β⟧ᶻ).sep ℰ` (related
to `T_chosen` via `hT_eq`) and `denT'` is the SMT-side lambda denotation.

The first conjunct of `RDom` (the type-level equation
`denT'.snd.fst = (τ ×ᴮ β).set.toSMTType`) is discharged from `hden_ty` and
`h_toSMT`. The second conjunct `retract (τ ×ᴮ β).set denT'.fst = T_chosen`
follows from the `hbridge` parameter (a semantic bridge supplied at the
call site mirroring `retract_lamVal_eq_collect` adapted to the lambda's
AND/EQ body and pair codomain).
-/
private theorem lambda_chosen_retract_eq.{u}
    {vs : List B.𝒱} {τ β : BType}
    {D_enc P_enc : SMT.Term}
    {z : SMT.𝒱}
    {Δ' : SMT.RenamingContext.Context}
    {denT' denD_val : SMT.Dom}
    {𝒟_val : ZFSet.{u}}
    {T_chosen : ZFSet.{u}}
    (ℰ : ZFSet.{u} → Prop)
    (vs_nemp : vs ≠ []) (vs_nodup : vs.Nodup)
    (h_toSMT : (τ ×ᴮ β).toSMTType = τ.toSMTType.pair β.toSMTType)
    (hcov_lambda : SMT.RenamingContext.CoversFV Δ'
      ((λˢ [z]) [τ.toSMTType.pair β.toSMTType]
        ((@ˢD_enc) (SMT.Term.var z).fst ∧ˢ
          ((SMT.Term.var z).snd =ˢ
            SMT.substList vs (toDestPair vs (SMT.Term.var z).fst) P_enc))))
    (hden_eq :
      ⟦((λˢ [z]) [τ.toSMTType.pair β.toSMTType]
              ((@ˢD_enc) (SMT.Term.var z).fst ∧ˢ
                ((SMT.Term.var z).snd =ˢ
                  SMT.substList vs (toDestPair vs (SMT.Term.var z).fst) P_enc))).abstract
          Δ' hcov_lambda⟧ˢ = some denT')
    (hden_ty : denT'.snd.fst = (τ.toSMTType.pair β.toSMTType).fun SMTType.bool)
    (hdenT_func : ⟦τ.toSMTType.pair β.toSMTType⟧ᶻ.IsFunc 𝔹 denT'.fst)
    (hcov_D_upd : ∀ W : SMT.Dom,
      SMT.RenamingContext.CoversFV (Function.update Δ' z (some W)) D_enc)
    (hden_D_upd : ∀ W : SMT.Dom,
      ⟦D_enc.abstract (Function.update Δ' z (some W)) (hcov_D_upd W)⟧ˢ = some denD_val)
    (denD_val_type : denD_val.snd.fst = τ.toSMTType.fun SMTType.bool)
    (denD_val_func : ⟦τ.toSMTType⟧ᶻ.IsFunc 𝔹 denD_val.fst)
    (h𝒟 : 𝒟_val ∈ ⟦τ.set⟧ᶻ)
    (denD_val_retract : retract τ.set denD_val.fst = 𝒟_val)
    (hT : T_chosen ∈ ⟦(τ ×ᴮ β).set⟧ᶻ)
    (hT_eq : (𝒟_val.prod ⟦β⟧ᶻ).sep ℰ = T_chosen)
    -- The semantic bridge: for any xy in ⟦τ ×ᴮ β⟧ᶻ, the SMT lambda's
    -- pointwise evaluation at the canonical embedding of xy returns
    -- zftrue iff xy lies in the B-level sep-product (𝒟_val × β.toZFSet).sep ℰ.
    -- This is constructed at the call site via `lambda_hbridge` plus
    -- the lambda-to-body unwrapping (mirroring
    -- `lambda_defaults_retract_empty_contradiction`).
    (hbridge : ∀ (xy : ZFSet.{u}) (hxy_mem : xy ∈ ⟦(τ ×ᴮ β)⟧ᶻ),
      ZFSet.fapply denT'.fst (ZFSet.is_func_is_pfunc hdenT_func)
          ⟨ZFSet.fapply (BType.canonicalIsoSMTType (τ ×ᴮ β)).1
              (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType (τ ×ᴮ β)).2.1)
              ⟨xy, by rwa [ZFSet.is_func_dom_eq
                (BType.canonicalIsoSMTType (τ ×ᴮ β)).2.1]⟩,
            by
              rw [ZFSet.is_func_dom_eq hdenT_func, ← h_toSMT]
              exact ZFSet.fapply_mem_range _ _⟩ = zftrue ↔
        xy ∈ (𝒟_val.prod ⟦β⟧ᶻ).sep ℰ) :
    (⟨T_chosen, ⟨(τ ×ᴮ β).set, hT⟩⟩ : B.Dom) ≘ᶻ denT' := by
  -- The B-side type is `(τ ×ᴮ β).set`; the SMT-side type from
  -- `hden_ty` is `(τ.toSMTType.pair β.toSMTType).fun .bool`. By
  -- `h_toSMT`, these match up via `BType.toSMTType` so the first
  -- conjunct of `RDom` is discharged. The second conjunct
  -- `retract (τ ×ᴮ β).set denT'.fst = T_chosen` is proved via
  -- `ZFSet.ext` + retract unfolding + pointwise application of `hbridge`.
  refine ⟨?_, ?_⟩
  · -- denT'.snd.fst = (τ ×ᴮ β).set.toSMTType
    rw [hden_ty]
    show (τ.toSMTType.pair β.toSMTType).fun SMTType.bool =
      (τ ×ᴮ β).set.toSMTType
    rw [show (τ ×ᴮ β).set.toSMTType =
      ((τ ×ᴮ β).toSMTType).fun SMTType.bool from rfl, h_toSMT]
  · -- retract (τ ×ᴮ β).set denT'.fst = T_chosen.
    -- Strategy: set extensionality + retract unfold + bridge pointwise.
    rw [← hT_eq]
    apply ZFSet.ext; intro xy
    rw [retract, ZFSet.mem_sep, ZFSet.mem_sep]
    -- Bridge the IsFunc proof to the canonical form for retract's dite.
    have hdenT_func' : ⟦(τ ×ᴮ β).toSMTType⟧ᶻ.IsFunc 𝔹 denT'.fst := by
      rw [show ((τ ×ᴮ β).toSMTType : SMTType) =
        τ.toSMTType.pair β.toSMTType from h_toSMT]
      exact hdenT_func
    -- 𝒟_val ⊆ ⟦τ⟧ᶻ
    have h𝒟_sub : 𝒟_val ⊆ ⟦τ⟧ᶻ := by
      rwa [BType.toZFSet, ZFSet.mem_powerset] at h𝒟
    -- Goal is now an iff between two structured propositions about xy.
    constructor
    · -- Forward: xy ∈ retract → xy ∈ T_chosen
      rintro ⟨hxy_mem, hxy_pred⟩
      -- hxy_pred is the dite branch from retract definition.
      rw [dif_pos hxy_mem, dif_pos hdenT_func'] at hxy_pred
      -- Apply hbridge to get xy ∈ ZFSet.sep ℰ (𝒟_val.prod ⟦β⟧ᶻ).
      have hb_in : xy ∈ ZFSet.sep ℰ (𝒟_val.prod ⟦β⟧ᶻ) := by
        apply (hbridge xy hxy_mem).mp
        convert hxy_pred using 2
      rw [ZFSet.mem_sep] at hb_in
      exact hb_in
    · -- Backward: xy ∈ T_chosen → xy ∈ retract
      rintro ⟨hxy_prod, hℰ⟩
      have hxy_T_sep : xy ∈ ZFSet.sep ℰ (𝒟_val.prod ⟦β⟧ᶻ) :=
        ZFSet.mem_sep.mpr ⟨hxy_prod, hℰ⟩
      have hxy_mem : xy ∈ ⟦(τ ×ᴮ β)⟧ᶻ := by
        rw [ZFSet.mem_prod] at hxy_prod
        obtain ⟨a, ha_mem, b, hb_mem, hxy_eq⟩ := hxy_prod
        rw [hxy_eq, BType.toZFSet, ZFSet.mem_prod]
        exact ⟨a, h𝒟_sub ha_mem, b, hb_mem, rfl⟩
      refine ⟨hxy_mem, ?_⟩
      rw [dif_pos hxy_mem, dif_pos hdenT_func']
      have hb := (hbridge xy hxy_mem).mpr hxy_T_sep
      convert hb using 2

set_option maxHeartbeats 4000000 in
open Classical B in
/--
Defaults-branch retract-empty contradiction for the lambda case.

Closes the contradiction obligation in the defaults branch (𝒟 = ∅). Given
that `D_enc` at the canonical embedding of any `x ∈ ⟦τ⟧ᶻ` is NOT zftrue
(because `retract τ.set denD_val.fst = ∅`), and given that some
`xy ∈ ⟦(τ ×ᴮ β)⟧ᶻ` would yield zftrue from the lambda body, derives
`False`.

The proof unfolds the SMT lambda application via `ZFSet.fapply_lambda_eq_iff`
+ `funAbstractGoSingle` to reduce the lambda body's evaluation to the AND
of `D_enc`'s evaluation and the EQ obligation. The `hDapp_not_zftrue`
hypothesis then forces the AND-conjunct false, contradicting `hxy_cond`.
-/
private theorem lambda_defaults_retract_empty_contradiction.{u}
    {vs : List B.𝒱} {τ β : BType}
    {D_enc P_enc : SMT.Term}
    {z : SMT.𝒱}
    {Δ' : SMT.RenamingContext.Context}
    {denT' denD_val : SMT.Dom}
    (vs_nemp : vs ≠ []) (vs_nodup : vs.Nodup)
    (h_toSMT : (τ ×ᴮ β).toSMTType = τ.toSMTType.pair β.toSMTType)
    (hcov_lambda : SMT.RenamingContext.CoversFV Δ'
      ((λˢ [z]) [τ.toSMTType.pair β.toSMTType]
        ((@ˢD_enc) (SMT.Term.var z).fst ∧ˢ
          ((SMT.Term.var z).snd =ˢ
            SMT.substList vs (toDestPair vs (SMT.Term.var z).fst) P_enc))))
    (hden_eq :
      ⟦((λˢ [z]) [τ.toSMTType.pair β.toSMTType]
              ((@ˢD_enc) (SMT.Term.var z).fst ∧ˢ
                ((SMT.Term.var z).snd =ˢ
                  SMT.substList vs (toDestPair vs (SMT.Term.var z).fst) P_enc))).abstract
          Δ' hcov_lambda⟧ˢ = some denT')
    (hden_ty : denT'.snd.fst = (τ.toSMTType.pair β.toSMTType).fun SMTType.bool)
    (hdenT_func : ⟦τ.toSMTType.pair β.toSMTType⟧ᶻ.IsFunc 𝔹 denT'.fst)
    (hdenD_type : denD_val.snd.fst = τ.toSMTType.fun SMTType.bool)
    (hdenD_func : ⟦τ.toSMTType⟧ᶻ.IsFunc 𝔹 denD_val.fst)
    (hcov_D_upd : ∀ W : SMT.Dom,
      SMT.RenamingContext.CoversFV (Function.update Δ' z (some W)) D_enc)
    (hden_D_upd : ∀ W : SMT.Dom,
      ⟦D_enc.abstract (Function.update Δ' z (some W)) (hcov_D_upd W)⟧ˢ = some denD_val)
    (hDapp_not_zftrue : ∀ (x : ZFSet.{u}) (hx : x ∈ ⟦τ⟧ᶻ),
      ZFSet.fapply denD_val.fst (ZFSet.is_func_is_pfunc hdenD_func)
        ⟨ZFSet.fapply (BType.canonicalIsoSMTType τ).1
            (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType τ).2.1)
            ⟨x, by rwa [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType τ).2.1]⟩,
          by
            rw [ZFSet.is_func_dom_eq hdenD_func]
            exact ZFSet.fapply_mem_range _ _⟩ ≠ zftrue)
    {xy : ZFSet.{u}} (hxy_mem : xy ∈ ⟦(τ ×ᴮ β)⟧ᶻ)
    (hxy_cond : ZFSet.fapply denT'.fst (ZFSet.is_func_is_pfunc hdenT_func)
      ⟨ZFSet.fapply (BType.canonicalIsoSMTType (τ ×ᴮ β)).1
          (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType (τ ×ᴮ β)).2.1)
          ⟨xy, by rwa [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType (τ ×ᴮ β)).2.1]⟩,
        by
          rw [ZFSet.is_func_dom_eq hdenT_func]
          exact ZFSet.fapply_mem_range _ _⟩ = zftrue) :
    False := by
  -- Step 1: Decompose xy = a.pair b via mem_prod.
  have hxy_mem' : xy ∈ ⟦τ⟧ᶻ.prod ⟦β⟧ᶻ := hxy_mem
  rw [ZFSet.mem_prod] at hxy_mem'
  obtain ⟨a, ha_mem, b, hb_mem, hxy_eq⟩ := hxy_mem'
  -- Step 2: Build canonical Wxy : SMT.Dom = canonical image of xy.
  -- Wxy.fst is what hxy_cond directly bridges with.
  have hcanon_xy_mem_pair :
      (ZFSet.fapply (BType.canonicalIsoSMTType (τ ×ᴮ β)).1
        (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType (τ ×ᴮ β)).2.1)
        ⟨xy, by rwa [ZFSet.is_func_dom_eq
          (BType.canonicalIsoSMTType (τ ×ᴮ β)).2.1]⟩).1 ∈
        ⟦τ.toSMTType.pair β.toSMTType⟧ᶻ := by
    have h : (ZFSet.fapply (BType.canonicalIsoSMTType (τ ×ᴮ β)).1
        (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType (τ ×ᴮ β)).2.1)
        ⟨xy, by rwa [ZFSet.is_func_dom_eq
          (BType.canonicalIsoSMTType (τ ×ᴮ β)).2.1]⟩).1 ∈
          ⟦(τ ×ᴮ β).toSMTType⟧ᶻ := ZFSet.fapply_mem_range _ _
    have h_set_eq : ⟦(τ ×ᴮ β).toSMTType⟧ᶻ = ⟦τ.toSMTType.pair β.toSMTType⟧ᶻ :=
      congrArg SMTType.toZFSet h_toSMT
    rw [← h_set_eq]; exact h
  let Wxy : SMT.Dom :=
    ⟨(ZFSet.fapply (BType.canonicalIsoSMTType (τ ×ᴮ β)).1
        (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType (τ ×ᴮ β)).2.1)
        ⟨xy, by rwa [ZFSet.is_func_dom_eq
          (BType.canonicalIsoSMTType (τ ×ᴮ β)).2.1]⟩).1,
      τ.toSMTType.pair β.toSMTType, hcanon_xy_mem_pair⟩
  have hWxy_ty : Wxy.snd.fst = τ.toSMTType.pair β.toSMTType := rfl
  have hWxy_mem : Wxy.fst ∈ ⟦τ.toSMTType.pair β.toSMTType⟧ᶻ := hcanon_xy_mem_pair
  -- Step 3: The body — D_enc(z.fst) AND (z.snd = substList...).
  set body : SMT.Term :=
    ((@ˢD_enc) (SMT.Term.var z).fst ∧ˢ
      ((SMT.Term.var z).snd =ˢ
        SMT.substList vs (toDestPair vs (SMT.Term.var z).fst) P_enc)) with body_def
  -- hgo_cov derived from hcov_lambda by mem_lambda.
  have hgo_cov : ∀ x ∈ SMT.fv body, x ∉ [z] → (Δ' x).isSome = true := by
    intro x hx hxz
    have hx_in_lam : x ∈ SMT.fv ((λˢ [z]) [τ.toSMTType.pair β.toSMTType] body) :=
      SMT.fv.mem_lambda ⟨hx, hxz⟩
    exact hcov_lambda x hx_in_lam
  have hcov_body_upd : ∀ W : SMT.Dom,
      SMT.RenamingContext.CoversFV (Function.update Δ' z (some W)) body := by
    intro W x hx
    by_cases hxz : x = z
    · subst hxz; simp [Function.update]
    · rw [Function.update_of_ne hxz]
      exact hgo_cov x hx (by simp [hxz])
  -- Step 4: Unfold hden_eq to expose lambda denotation structure.
  have hlamVal' := hden_eq
  rw [SMT.Term.abstract, dif_pos (by rfl)] at hlamVal'
  simp only [SMT.denote] at hlamVal'
  rw [dif_pos (show [z].length > 0 by exact Nat.zero_lt_succ 0)] at hlamVal'
  split_ifs at hlamVal' with h_isSome h_typ_det
  · -- Body is total + bool-typed under fresh-default substitution.
    -- Build Wxy-specific body denotation.
    let xₙ : Fin 1 → SMT.Dom := fun _ => Wxy
    have hxₙ_spec : ∀ i, (xₙ i).snd.fst = [τ.toSMTType.pair β.toSMTType][↑i] ∧
        (xₙ i).fst ∈ ⟦[τ.toSMTType.pair β.toSMTType][↑i]⟧ᶻ := by
      intro ⟨i, hi⟩
      simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.lt_one_iff] at hi
      subst hi
      exact ⟨rfl, hWxy_mem⟩
    have hgo_xy := funAbstractGoSingle (Δctx := Δ') (P := body) (v := z)
      (τ := τ.toSMTType.pair β.toSMTType) hgo_cov hcov_body_upd xₙ hxₙ_spec
    have hbody_isSome : (⟦body.abstract (Function.update Δ' z (some Wxy))
                              (hcov_body_upd Wxy)⟧ˢ).isSome = true := by
      rw [← hgo_xy]; exact h_isSome hxₙ_spec
    obtain ⟨body_val, hbody_val⟩ := Option.isSome_iff_exists.mp hbody_isSome
    -- Body's type is bool: derive via h_typ_det at xₙ vs default.
    -- We know body has bool output type at xₙ via the type-determination step.
    -- Approach: use hbody_val directly + AND-decomposition to get types.
    -- Step 5: body_val.fst = zftrue.
    have hbody_val_eq_zftrue : body_val.fst = zftrue := by
      simp only [Option.pure_def, Option.some.injEq] at hlamVal'
      have hlamVal_fst_eq : denT'.fst = _ := congrArg (·.fst) hlamVal'.symm
      simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.sub_self,
        Fin.foldr_zero, List.getElem_cons_zero] at hlamVal_fst_eq
      have h_pair_mem : Wxy.fst.pair body_val.fst ∈ denT'.fst := by
        rw [hlamVal_fst_eq, ZFSet.mem_lambda]
        refine ⟨Wxy.fst, body_val.fst, rfl, hWxy_mem, ?_, ?_⟩
        · -- body_val.fst ∈ γ.toZFSet (γ = .bool from h_typ_det at default xd)
          -- The codomain γ in the lambda denotation is bool (from hden_ty).
          -- Use body_val.snd.snd as our type proof.
          -- We need to show body_val.fst ∈ ⟦γ⟧ᶻ where γ is the lambda's output type.
          -- The output type γ is the type computed at default xd (Semantics.lean:140).
          -- Goal: body_val.fst ∈ γ.toZFSet where γ is the lambda's output type.
          -- This goal arises from the lambda-construct-based hlamVal_fst_eq.
          -- The actual γ here matches the snd.fst value we get from body_val.
          -- Easiest: use that body_val.snd.snd : body_val.fst ∈ ⟦body_val.snd.fst⟧ᶻ.
          -- And via h_typ_det we know body_val.snd.fst = γ (the determined type).
          -- Actually via the lambda denotation, the goal is exactly body_val.fst ∈ γ.
          -- Let γ_default be the type at xd (the default-arg). Use hbody_val as the
          -- evaluation at xₙ = Wxy and use h_typ_det xₙ xd.
          let xd : Fin 1 → SMT.Dom :=
            fun _ ↦ ⟨(τ.toSMTType.pair β.toSMTType).defaultZFSet,
                     τ.toSMTType.pair β.toSMTType,
                     SMTType.mem_toZFSet_of_defaultZFSet⟩
          have hxd_spec : ∀ i, (xd i).snd.fst = [τ.toSMTType.pair β.toSMTType][↑i] ∧
              (xd i).fst ∈ ⟦[τ.toSMTType.pair β.toSMTType][↑i]⟧ᶻ := by
            intro ⟨i, hi⟩
            simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.lt_one_iff] at hi
            subst hi
            exact ⟨rfl, SMTType.mem_toZFSet_of_defaultZFSet⟩
          have hγ_eq :
              (⟦(SMT.Term.abstract.go body [z] Δ' hgo_cov).uncurry xₙ⟧ˢ.get
                (h_isSome hxₙ_spec)).snd.fst =
              (⟦(SMT.Term.abstract.go body [z] Δ' hgo_cov).uncurry xd⟧ˢ.get
                (h_isSome hxd_spec)).snd.fst :=
            h_typ_det xₙ xd hxₙ_spec hxd_spec
          have hden_xy : ⟦(SMT.Term.abstract.go body [z] Δ' hgo_cov).uncurry xₙ⟧ˢ
              = some body_val := by rw [hgo_xy]; exact hbody_val
          rw [congrArg (·.snd.fst) (Option.get_of_eq_some _ hden_xy)] at hγ_eq
          have := body_val.snd.snd
          rw [hγ_eq] at this
          convert this using 2
        · split_ifs with hw'_cond
          · let xₙ' := fun i : Fin 1 =>
              (⟨Wxy.fst.get 1 i, [τ.toSMTType.pair β.toSMTType][↑i], hw'_cond.2 i⟩ : SMT.Dom)
            have hgo' := funAbstractGoSingle (Δctx := Δ') (P := body) (v := z)
              (τ := τ.toSMTType.pair β.toSMTType)
              hgo_cov hcov_body_upd xₙ' (fun i => ⟨rfl, hw'_cond.2 i⟩)
            have hxₙ'_eq : xₙ' ⟨0, Nat.zero_lt_one⟩ = Wxy := rfl
            have hden' : ⟦(SMT.Term.abstract.go body [z] Δ' hgo_cov).uncurry xₙ'⟧ˢ
                = some body_val := by rw [hgo', hxₙ'_eq]; exact hbody_val
            exact (congrArg (·.fst) (Option.get_of_eq_some _ hden')).symm
          · exfalso; apply hw'_cond
            exact ⟨trivial, fun ⟨i, hi⟩ => by
              have : i = 0 := Nat.lt_one_iff.mp hi; subst this; exact hWxy_mem⟩
      -- Now use fapply.of_pair to bridge with hxy_cond.
      have h_fapply := ZFSet.fapply.of_pair (ZFSet.is_func_is_pfunc hdenT_func) h_pair_mem
      rw [Subtype.ext_iff] at h_fapply
      -- h_fapply : (fapply denT' Wxy.fst).val = body_val.fst
      -- hxy_cond : (fapply denT' (canonical xy)).val = zftrue
      -- Wxy.fst IS (canonical xy).fst by definition.
      exact h_fapply.symm.trans hxy_cond
    -- Step 6: AND decomposition: body = (D_enc app) ∧ˢ (EQ part).
    -- Apply funDenoteAppAtFst to get Dp = D_enc(z.fst) at Wxy.
    obtain ⟨_, Dp, hDp_ty, hDp_val, hDp_den⟩ :=
      funDenoteAppAtFst (Δctx := Δ') (t := D_enc) (x := z)
        (α := τ.toSMTType) (β := SMTType.bool) (γ := β.toSMTType) (Y := denD_val)
        hcov_D_upd hden_D_upd hdenD_type hdenD_func Wxy hWxy_ty hWxy_mem
    set eq_part : SMT.Term :=
      ((SMT.Term.var z).snd =ˢ
        SMT.substList vs (toDestPair vs (SMT.Term.var z).fst) P_enc) with eq_part_def
    set D_enc_app_term : SMT.Term :=
      (@ˢD_enc) (SMT.Term.var z).fst with D_enc_app_def
    have hcov_eq_part_upd : ∀ W : SMT.Dom,
        SMT.RenamingContext.CoversFV (Function.update Δ' z (some W)) eq_part := by
      intro W x hx
      have hx_in_body : x ∈ SMT.fv body := by
        show x ∈ SMT.fv ((@ˢD_enc) (SMT.Term.var z).fst ∧ˢ
          ((SMT.Term.var z).snd =ˢ
            SMT.substList vs (toDestPair vs (SMT.Term.var z).fst) P_enc))
        simp only [SMT.fv, List.mem_append]
        right
        simp only [eq_part_def, SMT.fv, List.mem_append] at hx
        exact hx
      exact hcov_body_upd W x hx_in_body
    have hcov_D_app_upd : ∀ W : SMT.Dom,
        SMT.RenamingContext.CoversFV (Function.update Δ' z (some W)) D_enc_app_term := by
      intro W x hx
      have hx_in_body : x ∈ SMT.fv body := by
        show x ∈ SMT.fv ((@ˢD_enc) (SMT.Term.var z).fst ∧ˢ
          ((SMT.Term.var z).snd =ˢ
            SMT.substList vs (toDestPair vs (SMT.Term.var z).fst) P_enc))
        simp only [SMT.fv, List.mem_append]
        left
        simp only [D_enc_app_def, SMT.fv, List.mem_append] at hx
        exact hx
      exact hcov_body_upd W x hx_in_body
    -- body = D_enc_app_term ∧ˢ eq_part. Decompose denotation.
    have hbody_decomp :
        ⟦body.abstract (Function.update Δ' z (some Wxy)) (hcov_body_upd Wxy)⟧ˢ =
        ⟦(D_enc_app_term.abstract (Function.update Δ' z (some Wxy)) (hcov_D_app_upd Wxy)) ∧ˢ'
          (eq_part.abstract (Function.update Δ' z (some Wxy)) (hcov_eq_part_upd Wxy))⟧ˢ := by
      simp only [body_def, D_enc_app_def, eq_part_def, SMT.Term.abstract]
    rw [hbody_decomp] at hbody_val
    have hDp_den' : ⟦D_enc_app_term.abstract (Function.update Δ' z (some Wxy))
                      (hcov_D_app_upd Wxy)⟧ˢ = some Dp := by
      simp only [D_enc_app_def]
      convert hDp_den using 1
    -- Extract Dq : SMT.Dom and its properties from the AND denotation.
    have hDq_exists : ∃ Dq : SMT.Dom,
        ⟦eq_part.abstract (Function.update Δ' z (some Wxy)) (hcov_eq_part_upd Wxy)⟧ˢ = some Dq
          ∧ Dq.snd.fst = .bool := by
      have hbv := hbody_val
      simp only [SMT.denote, Option.bind_eq_bind, hDp_den'] at hbv
      obtain ⟨dp, _, hdp⟩ := Dp
      cases hDp_ty
      simp only [Option.bind_some] at hbv
      match hq : ⟦eq_part.abstract (Function.update Δ' z (some Wxy))
          (hcov_eq_part_upd Wxy)⟧ˢ with
      | none => simp [hq] at hbv
      | some ⟨Q, .bool, hQ⟩ => exact ⟨⟨Q, .bool, hQ⟩, rfl, rfl⟩
      | some ⟨Q, .int, hQ⟩ => simp [hq] at hbv
      | some ⟨Q, .unit, hQ⟩ => simp [hq] at hbv
      | some ⟨Q, .fun _ _, hQ⟩ => simp [hq] at hbv
      | some ⟨Q, .option _, hQ⟩ => simp [hq] at hbv
      | some ⟨Q, .pair _ _, hQ⟩ => simp [hq] at hbv
    obtain ⟨Dq, hDq_den, hDq_ty⟩ := hDq_exists
    have hDq_isSome : (⟦eq_part.abstract (Function.update Δ' z (some Wxy))
        (hcov_eq_part_upd Wxy)⟧ˢ).isSome = true :=
      Option.isSome_iff_exists.mpr ⟨Dq, hDq_den⟩
    have hDp_Dq_true :=
      denote_and_both_zftrue_of_zftrue (p := D_enc_app_term.abstract _ (hcov_D_app_upd Wxy))
        (q := eq_part.abstract _ (hcov_eq_part_upd Wxy)) (Dp := Dp) (Dq := Dq)
        hDp_den' hDp_ty hDq_den hDq_ty hbody_val hbody_val_eq_zftrue
    obtain ⟨hDp_true, _⟩ := hDp_Dq_true
    -- Step 7: Wxy.fst.π₁ = canonical τ a.
    have hWxy_π₁_eq :
        Wxy.fst.π₁ = (ZFSet.fapply (BType.canonicalIsoSMTType τ).1
          (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType τ).2.1)
          ⟨a, by rwa [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType τ).2.1]⟩).1 := by
      have hζ := (BType.canonicalIsoSMTType τ).2.1
      have hξ := (BType.canonicalIsoSMTType β).2.1
      have hfp := ZFSet.fapply_fprod (hf := hζ) (hg := hξ) (a := a) (b := b) ha_mem hb_mem
      have hWxy_pair : Wxy.fst =
          ((ZFSet.fapply (BType.canonicalIsoSMTType τ).1
              (ZFSet.is_func_is_pfunc hζ)
              ⟨a, by rwa [ZFSet.is_func_dom_eq hζ]⟩).1).pair
          ((ZFSet.fapply (BType.canonicalIsoSMTType β).1
              (ZFSet.is_func_is_pfunc hξ)
              ⟨b, by rwa [ZFSet.is_func_dom_eq hξ]⟩).1) := by
        subst hxy_eq
        exact hfp
      rw [hWxy_pair, ZFSet.π₁_pair]
    -- Step 8: Final contradiction.
    apply hDapp_not_zftrue a ha_mem
    have hgoal :
        ZFSet.fapply denD_val.fst (ZFSet.is_func_is_pfunc hdenD_func)
          ⟨ZFSet.fapply (BType.canonicalIsoSMTType τ).1
              (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType τ).2.1)
              ⟨a, by rwa [ZFSet.is_func_dom_eq
                (BType.canonicalIsoSMTType τ).2.1]⟩,
            by rw [ZFSet.is_func_dom_eq hdenD_func]; exact ZFSet.fapply_mem_range _ _⟩ =
          ZFSet.fapply denD_val.fst (ZFSet.is_func_is_pfunc hdenD_func)
          ⟨Wxy.fst.π₁, by
            rw [ZFSet.is_func_dom_eq hdenD_func, hWxy_π₁_eq]
            exact ZFSet.fapply_mem_range _ _⟩ := by
      congr 1
      apply Subtype.ext
      exact hWxy_π₁_eq.symm
    rw [hgoal]
    -- Goal now: fapply denD_val ⟨Wxy.fst.π₁, _⟩ = zftrue
    rw [← hDp_val]
    exact hDp_true
set_option maxHeartbeats 4000000 in
open Classical B in
/--
Chosen-branch totality clause for the lambda case.

Closes the totality clause at the chosen-branch call site. For any
alternative valuation `Δ_alt` of the lambda's free variables, produces
the matching `Δ'_alt`, `denT_alt`, and all the auxiliary preservation
properties.

Mirrors `collect_case`'s totality branch: construct `Δ'_alt` from `Δ_alt`,
`Δ_D`, `Δ_P` via `Function.update`; re-invoke `D_RDom.2` and `P_enc_total`
for D's and P's alternative denotations; assemble `denT_alt` via
`denote_exists_of_typing_fv`. The AND/EQ body and pair codomain are the
only structural difference from `collect_case`'s ITE body.
-/
private theorem lambda_chosen_totality.{u}
    {vs : List B.𝒱} {τ β : BType} {αs : List BType}
    {E_ctx : B.TypeContext} {D P : B.Term}
    {D_enc P_enc : SMT.Term}
    {z : SMT.𝒱}
    {Δ' : SMT.RenamingContext.Context.{u}}
    {denT' : SMT.Dom.{u}}
    {Γ_D Γ_P Γ' : SMT.TypeContext}
    {used_D used_P used' : List SMT.𝒱}
    (vs_nemp : vs ≠ []) (vs_nodup : vs.Nodup)
    (h_toSMT : (τ ×ᴮ β).toSMTType = τ.toSMTType.pair β.toSMTType)
    (typ_t : E_ctx ⊢ᴮ B.Term.lambda vs D P : (τ ×ᴮ β).set)
    (typ_D : E_ctx ⊢ᴮ D : .set τ)
    (typP : (vs.zipToAList αs ∪ E_ctx) ⊢ᴮ P : β)
    (typ_D_enc : Γ_D ⊢ˢ D_enc : τ.toSMTType.fun SMTType.bool)
    (typ_P_enc : Γ_P ⊢ˢ P_enc : β.toSMTType)
    (τ_hasArity : τ.hasArity vs.length)
    (vs_not_D_fv : ∀ v ∈ vs, v ∉ B.fv D)
    (vs_disj_Γ_D : ∀ v ∈ vs, v ∉ Γ_D)
    (vs_disj_Γ' : ∀ v ∈ vs, v ∉ Γ')
    (vs_used_P : ∀ v ∈ vs, v ∈ used_P)
    (vs_lookup_Γ_P : ∀ (i : Fin vs.length),
      AList.lookup vs[i] Γ_P = some ((τ.toSMTType.fromProdl (vs.length - 1))[i]'(by
        rw [fromProdl_length_of_hasArity τ_hasArity]; exact i.2)))
    (z_not_Γ_P : z ∉ Γ_P)
    (z_not_Γ' : z ∉ Γ')
    (z_not_used_P : z ∉ used_P)
    (z_not_fv_D : z ∉ SMT.fv D_enc)
    (z_not_fv_P : z ∉ SMT.fv P_enc)
    (z_not_vs : z ∉ vs)
    (hcov_lambda : SMT.RenamingContext.CoversFV Δ'
      ((λˢ [z]) [τ.toSMTType.pair β.toSMTType]
        ((@ˢD_enc) (SMT.Term.var z).fst ∧ˢ
          ((SMT.Term.var z).snd =ˢ
            SMT.substList vs (toDestPair vs (SMT.Term.var z).fst) P_enc))))
    (hden_eq :
      ⟦((λˢ [z]) [τ.toSMTType.pair β.toSMTType]
              ((@ˢD_enc) (SMT.Term.var z).fst ∧ˢ
                ((SMT.Term.var z).snd =ˢ
                  SMT.substList vs (toDestPair vs (SMT.Term.var z).fst) P_enc))).abstract
          Δ' hcov_lambda⟧ˢ = some denT')
    (hden_ty : denT'.snd.fst = (τ.toSMTType.pair β.toSMTType).fun SMTType.bool)
    (Δ'_none_out_used' : ∀ v ∉ used', Δ' v = none)
    (Δ'_dom_Γ' : ∀ v, Δ' v ≠ none → v ∈ Γ')
    (Δ'_wt_Γ' : ∀ v (d : SMT.Dom), Δ' v = some d →
      ∀ τ_v, AList.lookup v Γ' = some τ_v → d.snd.fst = τ_v)
    (D_total :
      ∀ (Δ_alt : B.RenamingContext.Context) (Δ_fv_alt : ∀ v ∈ B.fv D, (Δ_alt v).isSome = true)
        (Δ₀_alt : SMT.RenamingContext.Context),
        SMT.RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt D →
          (∀ v ∉ used_D, Δ₀_alt v = none) →
            (∀ (v : SMT.𝒱) (d : SMT.Dom),
                Δ₀_alt v = some d → ∀ (τ : SMTType), AList.lookup v Γ_D = some τ → d.snd.fst = τ) →
              ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦τ.set⟧ᶻ),
                ⟦D.abstract Δ_alt Δ_fv_alt⟧ᴮ = some ⟨T_alt, ⟨τ.set, hT_alt⟩⟩ →
                  ∃ Δ'_alt,
                    ∃ (h : SMT.RenamingContext.CoversFV Δ'_alt D_enc),
                      ∃ denT_alt,
                        SMT.RenamingContext.Extends Δ'_alt Δ₀_alt ∧
                          (∀ v ∉ used_D, Δ'_alt v = none) ∧
                            (∀ (v : SMT.𝒱) (d : SMT.Dom),
                                Δ'_alt v = some d → ∀ (τ : SMTType),
                                  AList.lookup v Γ_D = some τ → d.snd.fst = τ) ∧
                              ⟦D_enc.abstract Δ'_alt h⟧ˢ = some denT_alt ∧
                                ⟨T_alt, ⟨τ.set, hT_alt⟩⟩ ≘ᶻ denT_alt ∧
                                  ∀ (v : SMT.𝒱), Δ'_alt v ≠ none → v ∈ Γ_D)
    (P_enc_total :
      ∀ (Δ_alt : B.RenamingContext.Context) (Δ_fv_alt : ∀ v ∈ B.fv P, (Δ_alt v).isSome = true)
        (Δ₀_alt : SMT.RenamingContext.Context),
        SMT.RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt P →
          (∀ v ∉ used_P, Δ₀_alt v = none) →
            (∀ (v : SMT.𝒱) (d : SMT.Dom),
                Δ₀_alt v = some d → ∀ (τ : SMTType), AList.lookup v Γ_P = some τ → d.snd.fst = τ) →
              ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦β⟧ᶻ),
                ⟦P.abstract Δ_alt Δ_fv_alt⟧ᴮ = some ⟨T_alt, ⟨β, hT_alt⟩⟩ →
                  ∃ Δ'_alt,
                    ∃ (hcov_alt : SMT.RenamingContext.CoversFV Δ'_alt P_enc),
                      ∃ denT_alt,
                        SMT.RenamingContext.Extends Δ'_alt Δ₀_alt ∧
                          (∀ v ∉ used_P, Δ'_alt v = none) ∧
                            (∀ (v : SMT.𝒱) (d : SMT.Dom),
                                Δ'_alt v = some d → ∀ (τ : SMTType),
                                  AList.lookup v Γ_P = some τ → d.snd.fst = τ) ∧
                              ⟦P_enc.abstract Δ'_alt hcov_alt⟧ˢ = some denT_alt ∧
                                ⟨T_alt, ⟨β, hT_alt⟩⟩ ≘ᶻ denT_alt ∧
                                  ∀ (v : SMT.𝒱), Δ'_alt v ≠ none → v ∈ Γ_P)
    (Γ_D_lookup_sub_Γ' : ∀ v τ_v, AList.lookup v Γ_D = some τ_v → AList.lookup v Γ' = some τ_v)
    (Γ_D_lookup_sub_Γ_P : ∀ v τ_v, AList.lookup v Γ_D = some τ_v → AList.lookup v Γ_P = some τ_v)
    (Γ'_lookup_sub_Γ_P : ∀ v τ_v, AList.lookup v Γ' = some τ_v → AList.lookup v Γ_P = some τ_v)
    (used_D_sub_used' : used_D ⊆ used')
    (Γ_P_lookup_sub_Γ'_P : ∀ v ∉ vs, ∀ τ_v,
      AList.lookup v Γ_P = some τ_v → AList.lookup v Γ' = some τ_v)
    (used_P_sub_used' : used_P ⊆ used')
    (covers_D : CoversUsedVars used_D D)
    (covers_P : CoversUsedVars used_P P)
    (Γ_D_dom_sub_Γ' : ∀ v, v ∈ Γ_D → v ∈ Γ')
    (Γ_P_dom_sub_Γ' : ∀ v, v ∈ Γ_P → v ∉ vs → v ∈ Γ')
    (fv_lambda_sub : ∀ v ∈ B.fv (B.Term.lambda vs D P), v ∈ Γ')
    (used_D_sub_used_P : used_D ⊆ used_P) :
    ∀ (Δ_alt : B.RenamingContext.Context)
      (Δ_fv_alt : ∀ v ∈ B.fv (B.Term.lambda vs D P), (Δ_alt v).isSome = true)
      (Δ₀_alt : SMT.RenamingContext.Context),
      SMT.RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt (B.Term.lambda vs D P) →
        (∀ v ∉ used', Δ₀_alt v = none) →
          (∀ (v : SMT.𝒱) (d : SMT.Dom),
              Δ₀_alt v = some d → ∀ (τ_v : SMTType), AList.lookup v Γ' = some τ_v → d.snd.fst = τ_v) →
            ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦(τ ×ᴮ β).set⟧ᶻ),
              ⟦(B.Term.lambda vs D P).abstract Δ_alt Δ_fv_alt⟧ᴮ =
                  some ⟨T_alt, ⟨(τ ×ᴮ β).set, hT_alt⟩⟩ →
                ∃ Δ'_alt,
                  ∃ (hcov_alt : SMT.RenamingContext.CoversFV Δ'_alt
                    ((λˢ [z]) [τ.toSMTType.pair β.toSMTType]
                      ((@ˢD_enc) (SMT.Term.var z).fst ∧ˢ
                        ((SMT.Term.var z).snd =ˢ
                          SMT.substList vs (toDestPair vs (SMT.Term.var z).fst) P_enc)))),
                    ∃ denT_alt,
                      SMT.RenamingContext.Extends Δ'_alt Δ₀_alt ∧
                        (∀ v ∉ used', Δ'_alt v = none) ∧
                          (∀ (v : SMT.𝒱) (d : SMT.Dom),
                              Δ'_alt v = some d → ∀ (τ_v : SMTType),
                                AList.lookup v Γ' = some τ_v → d.snd.fst = τ_v) ∧
                            ⟦((λˢ [z]) [τ.toSMTType.pair β.toSMTType]
                                        ((@ˢD_enc) (SMT.Term.var z).fst ∧ˢ
                                          ((SMT.Term.var z).snd =ˢ
                                            SMT.substList vs (toDestPair vs (SMT.Term.var z).fst) P_enc))).abstract
                                    Δ'_alt hcov_alt⟧ˢ = some denT_alt ∧
                              (⟨T_alt, ⟨(τ ×ᴮ β).set, hT_alt⟩⟩ : B.Dom) ≘ᶻ denT_alt ∧
                                ∀ (v : SMT.𝒱), Δ'_alt v ≠ none → v ∈ Γ' := by
  intro Δ_alt Δ_fv_alt Δ₀_alt hext_alt hnone_alt hwt_alt T_alt hT_alt hden_alt
  -- Extract B-level D denotation from lambda denotation
  -- Lambda's B-side denotation begins with ⟨𝒟, .set τ, h𝒟⟩ ← ⟦D⟧ᴮ | failure,
  -- so we can pattern-match exactly as collect does for D-extraction.
  have hden_D_alt : ∃ (𝒟_alt : ZFSet.{u}) (h𝒟_alt : 𝒟_alt ∈ ⟦τ.set⟧ᶻ),
      ⟦D.abstract Δ_alt (fun v hv => Δ_fv_alt v (B.fv.mem_lambda (.inl hv)))⟧ᴮ =
      some ⟨𝒟_alt, ⟨τ.set, h𝒟_alt⟩⟩ := by
    have h_inv := hden_alt
    simp only [B.Term.abstract] at h_inv
    unfold B.denote at h_inv
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h_inv
    obtain ⟨⟨d_val, d_ty, d_mem⟩, h_den_d, _⟩ := h_inv
    have h_conv : ⟦D.abstract Δ_alt
        (fun v hv => Δ_fv_alt v (B.fv.mem_lambda (.inl hv)))⟧ᴮ =
        some ⟨d_val, ⟨d_ty, d_mem⟩⟩ := by convert h_den_d using 2
    have : d_ty = .set τ := by
      have h_wt := denote_welltyped_eq
        (t := D.abstract Δ_alt
          (fun v hv => Δ_fv_alt v (B.fv.mem_lambda (.inl hv))))
        ⟨_, WFTC.of_abstract, .set τ,
          by convert Typing.of_abstract _ typ_D⟩
        h_conv
      exact h_wt.symm
    subst this
    exact ⟨d_val, d_mem, h_conv⟩
  obtain ⟨𝒟_alt, h𝒟_alt, hden_D_alt_eq⟩ := hden_D_alt
  -- Build Δ₀_alt_D restricted context for D's totality invocation.
  -- Same pattern as collect (3190-3197): toSMTOnFV D, fallback to Δ₀_alt on used_D.
  set Δ₀_alt_D : SMT.RenamingContext.Context :=
    fun v => match B.RenamingContext.toSMTOnFV Δ_alt D v with
      | some d => some d
      | none => if v ∈ used_D then
          match Δ₀_alt v with
          | some d => some d
          | none => none
        else none
  -- ExtendsOnSourceFV: Δ₀_alt_D extends Δ_alt on D's free vars.
  have hext_alt_D : SMT.RenamingContext.ExtendsOnSourceFV Δ₀_alt_D Δ_alt D := by
    intro v d hv; simp only [Δ₀_alt_D, hv]
  -- None-out: Δ₀_alt_D v = none for v ∉ used_D.
  have hnone_alt_D : ∀ v ∉ used_D, Δ₀_alt_D v = none := by
    intro v hv
    show (match B.RenamingContext.toSMTOnFV Δ_alt D v with
      | some d => some d
      | none => if v ∈ used_D then
          match Δ₀_alt v with
          | some d => some d
          | none => none
        else none) = none
    have hv_not_fv_D : v ∉ B.fv D := B.not_mem_fv_of_not_mem_used covers_D hv
    have h_toSMT_none : B.RenamingContext.toSMTOnFV Δ_alt D v = none := by
      simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
        B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_not_fv_D]
    rw [h_toSMT_none, if_neg hv]
  -- Well-typed: Δ₀_alt_D v = some d ⇒ d's type matches Γ_D's lookup.
  have hwt_alt_D : ∀ v (d : SMT.Dom), Δ₀_alt_D v = some d →
      ∀ τ_v, AList.lookup v Γ_D = some τ_v → d.snd.fst = τ_v := by
    intro v d hv τ_v hτ_v
    change (match B.RenamingContext.toSMTOnFV Δ_alt D v with
      | some d => some d
      | none => if v ∈ used_D then
          match Δ₀_alt v with
          | some d => some d
          | none => none
        else none) = some d at hv
    cases h_toSMT : B.RenamingContext.toSMTOnFV Δ_alt D v with
    | some d' =>
      simp only [h_toSMT] at hv; cases hv
      -- v ∈ B.fv D, so v ∈ B.fv (lambda) via fv.mem_lambda.
      have hv_fv_D : v ∈ B.fv D := by
        by_contra hv_not
        simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
          B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_not] at h_toSMT
      have h_onFV : B.RenamingContext.toSMTOnFV Δ_alt (B.Term.lambda vs D P) v = some d := by
        simp only [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
          B.RenamingContext.restrictToFV_eq_of_mem (B.fv.mem_lambda (.inl hv_fv_D))]
        simp only [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
          B.RenamingContext.restrictToFV_eq_of_mem hv_fv_D] at h_toSMT
        exact h_toSMT
      have hΔ₀_alt_v : Δ₀_alt v = some d := hext_alt h_onFV
      -- Lift Γ_D's lookup to Γ' via Γ_D_lookup_sub_Γ'.
      have hτ_v_Γ' : AList.lookup v Γ' = some τ_v := Γ_D_lookup_sub_Γ' v τ_v hτ_v
      exact hwt_alt v d hΔ₀_alt_v τ_v hτ_v_Γ'
    | none =>
      simp only [h_toSMT] at hv
      split_ifs at hv with h_used
      · cases hΔ₀_alt : Δ₀_alt v with
        | some d' =>
          simp only [hΔ₀_alt, Option.some.injEq] at hv
          subst hv
          -- Use hwt_alt with the lifted lookup.
          have hτ_v_Γ' : AList.lookup v Γ' = some τ_v := Γ_D_lookup_sub_Γ' v τ_v hτ_v
          exact hwt_alt v d' hΔ₀_alt τ_v hτ_v_Γ'
        | none =>
          simp only [hΔ₀_alt] at hv
          nomatch hv
  -- Invoke D_total to obtain the alternative D-side covering data.
  obtain ⟨Δ_D_alt, hcov_D_alt, denD_alt, hext_D_alt, Δ_D_alt_none_out,
      Δ_D_alt_wt_out, hden_D_alt, hRDom_D_alt, Δ_D_alt_dom⟩ :=
    D_total Δ_alt
      (fun v hv => Δ_fv_alt v (B.fv.mem_lambda (.inl hv)))
      Δ₀_alt_D hext_alt_D hnone_alt_D hwt_alt_D
      𝒟_alt h𝒟_alt hden_D_alt_eq
  -- Build Δ'_alt cascade = Δ₀_alt → Δ_D_alt → Δ'.
  -- Mirrors collect's pattern (EncodeTermCorrectCollect.lean:3338-3343),
  -- adapted for the lambda's separate D + P + AND/EQ body. The Δ' fall-through
  -- layer relies on the invariants `Δ'_none_out_used'`, `Δ'_dom_Γ'`,
  -- `Δ'_wt_Γ'`.
  set Δ'_alt : SMT.RenamingContext.Context :=
    fun v => match Δ₀_alt v with
      | some d => some d
      | none => match Δ_D_alt v with
        | some d => some d
        | none => Δ' v
    with Δ'_alt_def
  -- Δ'_alt extends Δ₀_alt.
  have Δ'_alt_extends_Δ₀_alt : SMT.RenamingContext.Extends Δ'_alt Δ₀_alt := by
    intro v d hv; simp only [Δ'_alt, hv]
  -- Δ'_alt vanishes outside used'.
  have Δ'_alt_none_out : ∀ v ∉ used', Δ'_alt v = none := by
    intro v hv
    simp only [Δ'_alt]
    have h1 : Δ₀_alt v = none := hnone_alt v hv
    rw [h1]
    have hv_not_used_D : v ∉ used_D := fun hmem => hv (used_D_sub_used' hmem)
    have h2 : Δ_D_alt v = none := Δ_D_alt_none_out v hv_not_used_D
    rw [h2]
    exact Δ'_none_out_used' v hv
  -- Δ'_alt is well-typed against Γ'.
  have Δ'_alt_wt : ∀ v (d : SMT.Dom), Δ'_alt v = some d →
      ∀ τ_v, AList.lookup v Γ' = some τ_v → d.snd.fst = τ_v := by
    intro v d hv τ_v hτ_v
    -- Unfold Δ'_alt v = match cascade.
    change (match Δ₀_alt v with
      | some d => some d
      | none => match Δ_D_alt v with
        | some d => some d
        | none => Δ' v) = some d at hv
    cases hΔ₀ : Δ₀_alt v with
    | some d₀ =>
      simp only [hΔ₀] at hv; cases hv
      exact hwt_alt v d hΔ₀ τ_v hτ_v
    | none =>
      simp only [hΔ₀] at hv
      cases hΔ_D : Δ_D_alt v with
      | some d' =>
        simp only [hΔ_D] at hv; cases hv
        -- Need Γ_D's lookup: v ∈ Γ_D from Δ_D_alt_dom; lift Γ_D to Γ'
        have hv_Γ_D : v ∈ Γ_D := Δ_D_alt_dom v (by rw [hΔ_D]; simp)
        -- Get Γ_D's lookup at v via Γ_D_dom_sub_Γ' transitivity isn't direct...
        -- Use Δ_D_alt_wt_out: needs Γ_D's lookup at v.
        obtain ⟨τ_v_D, hτ_v_D⟩ := Option.isSome_iff_exists.mp
          (AList.lookup_isSome.mpr hv_Γ_D)
        have hτ_v_Γ' : AList.lookup v Γ' = some τ_v_D :=
          Γ_D_lookup_sub_Γ' v τ_v_D hτ_v_D
        rw [hτ_v_Γ'] at hτ_v; cases hτ_v
        exact Δ_D_alt_wt_out v d hΔ_D τ_v hτ_v_D
      | none =>
        simp only [hΔ_D] at hv
        exact Δ'_wt_Γ' v d hv τ_v hτ_v
  -- Δ'_alt's domain is in Γ'.
  have Δ'_alt_dom_Γ' : ∀ v, Δ'_alt v ≠ none → v ∈ Γ' := by
    intro v hv_ne
    simp only [Δ'_alt] at hv_ne
    cases hΔ₀ : Δ₀_alt v with
    | some d₀ =>
      -- Δ₀_alt v ≠ none → v ∈ used' (contrapositive of hnone_alt).
      -- But used' ↔ Γ' membership isn't direct; use hwt_alt-derived membership.
      -- hwt_alt only constrains type; we need Γ' membership.
      -- Strategy: Δ₀_alt extends toSMTOnFV Δ_alt (lambda), so v ∈ B.fv (lambda)
      -- ⇒ v ∈ Γ' via fv_lambda_sub.
      have hv_fv_lambda : v ∈ B.fv (B.Term.lambda vs D P) := by
        -- Δ₀_alt v = some d₀ and Δ₀_alt extends toSMTOnFV Δ_alt (lambda).
        -- Need to show that Δ₀_alt v = some d₀ implies the toSMTOnFV image is some d₀ also.
        -- This is the converse direction: ExtendsOnSourceFV says only that toSMT ⇒ Δ₀.
        -- We need Δ₀ ⇒ B.fv. This requires the .dom_sub_B_fv axiom-style lemma.
        exact SMT.RenamingContext.ExtendsOnSourceFV.dom_sub_B_fv hext_alt v
          (by rw [hΔ₀]; simp)
      exact fv_lambda_sub v hv_fv_lambda
    | none =>
      simp only [hΔ₀] at hv_ne
      cases hΔ_D : Δ_D_alt v with
      | some d_D =>
        simp only [hΔ_D] at hv_ne
        have hv_Γ_D : v ∈ Γ_D := Δ_D_alt_dom v (by rw [hΔ_D]; simp)
        exact Γ_D_dom_sub_Γ' v hv_Γ_D
      | none =>
        simp only [hΔ_D] at hv_ne
        exact Δ'_dom_Γ' v hv_ne
  -- Δ'_alt covers fv(lambda). For each v ∈ fv(lambda), there are three sub-cases:
  -- (1) v ∈ fv(D_enc) ⇒ Δ_D_alt covers (we may need the cascade fall-through).
  -- (2) v = z (impossible, z is the bound variable, removed by removeAll).
  -- (3) v ∈ fv(substList vs ... P_enc) — substituted-into terms.
  -- All covered: cascade defaults to Δ' which covers the lambda.
  have Δ'_alt_covers_lambda : SMT.RenamingContext.CoversFV Δ'_alt
      ((λˢ [z]) [τ.toSMTType.pair β.toSMTType]
        ((@ˢD_enc) (SMT.Term.var z).fst ∧ˢ
          ((SMT.Term.var z).snd =ˢ
            SMT.substList vs (toDestPair vs (SMT.Term.var z).fst) P_enc))) := by
    intro v hv
    simp only [Δ'_alt]
    cases hΔ₀ : Δ₀_alt v with
    | some d₀ => simp
    | none =>
      cases hΔ_D : Δ_D_alt v with
      | some d_D => simp
      | none =>
        -- Fall through to Δ'.
        exact hcov_lambda v hv
  -- =========================================================================
  -- Witness extraction + P_enc_total invocation + denote_exists_of_typing_fv.
  -- =========================================================================
  -- Step 1: Extract a typed witness from hden_alt that can drive P denotation.
  -- The lambda denote (B/SemanticsPHOAS.lean:552-595) has the structure
  --   `let ⟨𝒟, .set τ, _⟩ ← ⟦D⟧ᴮ`
  --   `if hτ then if den_E then if typE_det then if 𝒟_nemp then ... else (defaults)`
  -- In BOTH branches a typed `x_fin_alt : Fin vs.length → B.Dom` exists with
  --   (i) (x_fin_alt i).snd.fst = τ.get vs.length i,
  --   (ii) (x_fin_alt i).fst ∈ ⟦τ.get vs.length i⟧ᶻ,
  -- and `den_E` provides ⟦P.abstract Δ_ext_alt _⟧ᴮ = some _ at this witness
  -- (after going through `denote_term_abstract_go_eq_term_abstract`).
  --
  -- In the chosen branch (𝒟_alt ≠ ∅), the witness comes from Classical.choose
  -- on h_nemp. In the defaults branch (𝒟_alt = ∅), the witness comes from
  -- τ.defaultZFSet.get which is well-typed by hτ and hτ.hasArity.
  --
  -- Below we extract `den_E` (the universally-quantified P-denotation hypothesis)
  -- and `typE_det` from `hden_alt` via split_ifs. These are the SAME data the
  -- main proof extracts at lines 1306-1348.
  have hden_alt_data : ∃ (f_alt : Fin vs.length → B.Dom),
      (∀ i, (f_alt i).snd.fst = τ.get vs.length i ∧ (f_alt i).fst ∈ ⟦τ.get vs.length i⟧ᶻ) ∧
      ∃ (P_val_alt : ZFSet.{u}) (hP_val_alt : P_val_alt ∈ ⟦β⟧ᶻ),
      ⟦(B.Term.abstract.go P vs Δ_alt
        (fun v hv hvs => Δ_fv_alt v (B.fv.mem_lambda (.inr ⟨hv, hvs⟩)))).uncurry f_alt⟧ᴮ
        = some ⟨P_val_alt, ⟨β, hP_val_alt⟩⟩ := by
    have h_inv := hden_alt
    simp only [B.Term.abstract] at h_inv
    unfold B.denote at h_inv
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h_inv
    obtain ⟨D_dom_pkg, h_den_d, rest_alt⟩ := h_inv
    have h_conv_d : ⟦D.abstract Δ_alt
        (fun v hv => Δ_fv_alt v (B.fv.mem_lambda (.inl hv)))⟧ᴮ =
        some D_dom_pkg := by convert h_den_d using 2
    have hD_dom_eq : D_dom_pkg = ⟨𝒟_alt, ⟨τ.set, h𝒟_alt⟩⟩ := by
      rw [h_conv_d] at hden_D_alt_eq
      exact Option.some.inj hden_D_alt_eq
    subst hD_dom_eq
    simp only at rest_alt
    rw [dif_pos τ_hasArity] at rest_alt
    split_ifs at rest_alt with h_den_E h_typE_det h_nemp h_chosen_arity h_default_arity
    · -- Chosen branch: 𝒟_alt ≠ ∅, witness via Classical.choose.
      let x_choose := Classical.choose (ZFSet.nonempty_exists_iff.mp h_nemp)
      have x_choose_mem : x_choose ∈ 𝒟_alt :=
        Classical.choose_spec (ZFSet.nonempty_exists_iff.mp h_nemp)
      let f_alt : Fin vs.length → B.Dom := fun i =>
        ⟨x_choose.get vs.length i, τ.get vs.length i,
         get_mem_type_of_isTuple h_chosen_arity.1 τ_hasArity h_chosen_arity.2⟩
      have hf_alt_typ : ∀ i, (f_alt i).snd.fst = τ.get vs.length i ∧
          (f_alt i).fst ∈ ⟦τ.get vs.length i⟧ᶻ :=
        fun i => ⟨rfl, (f_alt i).snd.snd⟩
      have hx_fin_in_𝒟_alt : ZFSet.ofFinDom f_alt ∈ 𝒟_alt := by
        have h_eq : ZFSet.ofFinDom f_alt = x_choose :=
          ZFSet.ofFinDom_get (List.length_pos_iff.mpr vs_nemp)
            (fun i => get_mem_type_of_isTuple h_chosen_arity.1 τ_hasArity h_chosen_arity.2)
            h_chosen_arity.1 τ_hasArity
        rw [h_eq]; exact x_choose_mem
      have hP_isSome := h_den_E hf_alt_typ hx_fin_in_𝒟_alt
      obtain ⟨⟨P_val, P_ty, hP_val⟩, hP_den⟩ := Option.isSome_iff_exists.mp hP_isSome
      have Δ_fv_alt_P : ∀ v ∈ B.fv P, (Function.updates Δ_alt vs
          (List.ofFn fun i => some (f_alt i)) v).isSome = true := by
        intro v hv
        rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup]
        split_ifs with hvs
        · simp [List.getElem_ofFn]
        · exact Δ_fv_alt v (B.fv.mem_lambda (.inr ⟨hv, hvs⟩))
      have hP_den_at_abs : ⟦P.abstract (Function.updates Δ_alt vs
            (List.ofFn fun i => some (f_alt i))) Δ_fv_alt_P⟧ᴮ =
          some ⟨P_val, ⟨P_ty, hP_val⟩⟩ := by
        rw [← denote_term_abstract_go_eq_term_abstract vs_nodup vs_nemp f_alt Δ_fv_alt_P]
        convert hP_den using 2
      have hτP_β : P_ty = β := by
        exact (denote_welltyped_eq
          (t := P.abstract (Function.updates Δ_alt vs
            (List.ofFn fun i => some (f_alt i))) Δ_fv_alt_P)
          ⟨_, WFTC.of_abstract, β,
            by convert Typing.of_abstract Δ_fv_alt_P typP⟩
          hP_den_at_abs).symm
      subst hτP_β
      refine ⟨f_alt, hf_alt_typ, P_val, hP_val, ?_⟩
      convert hP_den using 2
    · -- Defaults branch: 𝒟_alt = ∅, witness via τ.defaultZFSet.
      let f_alt : Fin vs.length → B.Dom := fun i =>
        ⟨τ.defaultZFSet.get vs.length i, τ.get vs.length i,
         get_mem_type_of_isTuple h_default_arity.1 h_default_arity.2
           BType.mem_toZFSet_of_defaultZFSet⟩
      have hf_alt_typ : ∀ i, (f_alt i).snd.fst = τ.get vs.length i ∧
          (f_alt i).fst ∈ ⟦τ.get vs.length i⟧ᶻ :=
        fun i => ⟨rfl, (f_alt i).snd.snd⟩
      -- rest_alt : bind (P at f_alt) (...) = some ⟨T_alt, (τ ×ᴮ β).set, _⟩
      simp only [Option.bind_eq_some_iff] at rest_alt
      obtain ⟨P_dom, hP_den, _⟩ := rest_alt
      obtain ⟨P_val, P_ty, hP_val⟩ := P_dom
      have Δ_fv_alt_P : ∀ v ∈ B.fv P, (Function.updates Δ_alt vs
          (List.ofFn fun i => some (f_alt i)) v).isSome = true := by
        intro v hv
        rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup]
        split_ifs with hvs
        · simp [List.getElem_ofFn]
        · exact Δ_fv_alt v (B.fv.mem_lambda (.inr ⟨hv, hvs⟩))
      have hP_den_at_abs : ⟦P.abstract (Function.updates Δ_alt vs
            (List.ofFn fun i => some (f_alt i))) Δ_fv_alt_P⟧ᴮ =
          some ⟨P_val, ⟨P_ty, hP_val⟩⟩ := by
        rw [← denote_term_abstract_go_eq_term_abstract vs_nodup vs_nemp f_alt Δ_fv_alt_P]
        convert hP_den using 2
      have hτP_β : P_ty = β := by
        exact (denote_welltyped_eq
          (t := P.abstract (Function.updates Δ_alt vs
            (List.ofFn fun i => some (f_alt i))) Δ_fv_alt_P)
          ⟨_, WFTC.of_abstract, β,
            by convert Typing.of_abstract Δ_fv_alt_P typP⟩
          hP_den_at_abs).symm
      subst hτP_β
      refine ⟨f_alt, hf_alt_typ, P_val, hP_val, ?_⟩
      convert hP_den using 2
  obtain ⟨f_alt, hf_alt_typ, P_val_alt, hP_val_alt, hP_go_den_alt⟩ := hden_alt_data
  -- Step 2: Build B-side ext context Δ_ext_alt and SMT-side ext Δ_D_ext_alt.
  -- These mirror lambda_hbridge's `Δ_ext_x` and `Δ_D_ext_x` patterns for the
  -- alternative valuation rather than the chosen one.
  set Δ_ext_alt : B.RenamingContext.Context :=
    Function.updates Δ_alt vs (List.ofFn fun i => some (f_alt i)) with Δ_ext_alt_def
  have Δ_fv_P_alt : ∀ v ∈ B.fv P, (Δ_ext_alt v).isSome = true := by
    intro v hv
    show (Function.updates Δ_alt vs _ v).isSome = true
    rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup]
    split_ifs with hvs
    · simp [List.getElem_ofFn]
    · exact Δ_fv_alt v (B.fv.mem_lambda (.inr ⟨hv, hvs⟩))
  -- Lift hP_go_den_alt to a P.abstract denotation.
  have h_den_P_alt : ⟦P.abstract Δ_ext_alt Δ_fv_P_alt⟧ᴮ =
      some ⟨P_val_alt, ⟨β, hP_val_alt⟩⟩ := by
    rw [← denote_term_abstract_go_eq_term_abstract vs_nodup vs_nemp f_alt Δ_fv_P_alt]
    convert hP_go_den_alt using 2
  -- Δ_D_ext_alt: SMT-side ext extending Δ_D_alt at vs to canonical SMT translations.
  set Δ_D_ext_alt : SMT.RenamingContext.Context :=
    Function.updates Δ_D_alt vs
      (List.ofFn fun (i : Fin vs.length) => B.RenamingContext.toSMT Δ_ext_alt vs[i])
    with Δ_D_ext_alt_def
  -- Step 3: Build Δ₀_hybrid_alt for P_enc_total invocation.
  -- Simplest hybrid: use B.RenamingContext.toSMTOnFV Δ_ext_alt P directly. This
  -- gives values exactly on B.fv P (via Δ_ext_alt's vs-updates and Δ_alt for
  -- non-vs fv) and none elsewhere. ExtendsOnSourceFV is trivial.
  set Δ₀_hybrid_alt : SMT.RenamingContext.Context :=
    B.RenamingContext.toSMTOnFV Δ_ext_alt P with Δ₀_hybrid_alt_def
  have Δ₀_hybrid_ext_P_alt : SMT.RenamingContext.ExtendsOnSourceFV Δ₀_hybrid_alt
      Δ_ext_alt P := by
    intro v d hv_eq; exact hv_eq
  -- none_out: v ∉ used_P ⇒ v ∉ B.fv P (via covers_P) ⇒ toSMTOnFV = none.
  have Δ₀_hybrid_alt_none_used_P : ∀ v ∉ used_P, Δ₀_hybrid_alt v = none := by
    intro v hv
    show B.RenamingContext.toSMTOnFV Δ_ext_alt P v = none
    have hv_not_fv_P : v ∉ B.fv P := fun hv_fv => hv (covers_P v hv_fv)
    simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
      B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_not_fv_P]
  -- wt: for v ∈ B.fv P, type tag of toSMT Δ_ext_alt v matches Γ_P's lookup.
  -- Case split on v ∈ vs vs v ∉ vs.
  have Δ₀_hybrid_alt_wt : ∀ v (d : SMT.Dom), Δ₀_hybrid_alt v = some d →
      ∀ τ_v, AList.lookup v Γ_P = some τ_v → d.snd.fst = τ_v := by
    intro v d hv τ_v hτ_v
    change B.RenamingContext.toSMTOnFV Δ_ext_alt P v = some d at hv
    -- v ∈ B.fv P (else toSMTOnFV = none).
    have hv_fv_P : v ∈ B.fv P := by
      by_contra hv_not
      simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
        B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_not] at hv
    by_cases hvs : v ∈ vs
    · -- v ∈ vs: Δ_ext_alt v = some (f_alt vs.idxOf v); type tag = (τ.get _ i).toSMTType.
      -- vs_lookup_Γ_P gives Γ_P's actual lookup at vs[i] = (τ.toSMTType.fromProdl _)[i].
      have hidx : vs.idxOf v < vs.length := List.idxOf_lt_length_of_mem hvs
      have hΔ_ext_alt_v : Δ_ext_alt v = some (f_alt ⟨vs.idxOf v, hidx⟩) := by
        show Function.updates Δ_alt vs _ v = _
        rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup, dif_pos hvs]
        simp only [List.getElem_ofFn]
      have hv_eq_toSMT : B.RenamingContext.toSMTOnFV Δ_ext_alt P v =
          B.RenamingContext.toSMT Δ_ext_alt v := by
        simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
          B.RenamingContext.restrictToFV_eq_of_mem hv_fv_P]
      rw [hv_eq_toSMT] at hv
      rw [B.RenamingContext.toSMT, hΔ_ext_alt_v, Option.pure_def, Option.bind_eq_bind,
        Option.bind_some] at hv
      cases hv
      simp only
      rw [(hf_alt_typ ⟨vs.idxOf v, hidx⟩).1]
      -- Goal: (τ.get vs.length ⟨vs.idxOf v, hidx⟩).toSMTType = τ_v
      have h_lookup := vs_lookup_Γ_P ⟨vs.idxOf v, hidx⟩
      have h_v_eq : (vs.get ⟨vs.idxOf v, hidx⟩) = v := List.getElem_idxOf hidx
      -- vs[i] in the helper signature uses the Fin-index. Unify.
      have h_lookup' : AList.lookup v Γ_P = some
          ((τ.toSMTType.fromProdl (vs.length - 1))[vs.idxOf v]'(by
            rw [fromProdl_length_of_hasArity τ_hasArity]; exact hidx)) := by
        convert h_lookup using 1
        · exact congrArg (AList.lookup · _) h_v_eq.symm
      rw [hτ_v] at h_lookup'
      injection h_lookup' with h_eq
      rw [h_eq]
      exact toSMTType_get_eq_fromProdl_getElem τ_hasArity hidx
    · -- v ∉ vs: Δ_ext_alt v = Δ_alt v. Use hext_alt to get Δ₀_alt v = some d.
      have hΔ_ext_alt_v : Δ_ext_alt v = Δ_alt v := by
        show Function.updates Δ_alt vs _ v = Δ_alt v
        exact Function.updates_of_not_mem Δ_alt vs _ v hvs
      have hv_eq_toSMT : B.RenamingContext.toSMTOnFV Δ_ext_alt P v =
          B.RenamingContext.toSMT Δ_alt v := by
        simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
          B.RenamingContext.restrictToFV_eq_of_mem hv_fv_P, hΔ_ext_alt_v]
      rw [hv_eq_toSMT] at hv
      -- hv : toSMT Δ_alt v = some d
      have hv_lambda : v ∈ B.fv (B.Term.lambda vs D P) :=
        B.fv.mem_lambda (.inr ⟨hv_fv_P, hvs⟩)
      have h_toSMTOnFV_lambda : B.RenamingContext.toSMTOnFV Δ_alt
          (B.Term.lambda vs D P) v = some d := by
        simp only [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
          B.RenamingContext.restrictToFV_eq_of_mem hv_lambda, Option.pure_def,
          Option.bind_eq_bind]
        rw [B.RenamingContext.toSMT, Option.pure_def, Option.bind_eq_bind] at hv
        exact hv
      have hΔ₀_alt_v : Δ₀_alt v = some d := hext_alt h_toSMTOnFV_lambda
      have hτ_v_Γ' : AList.lookup v Γ' = some τ_v := Γ_P_lookup_sub_Γ'_P v hvs τ_v hτ_v
      exact hwt_alt v d hΔ₀_alt_v τ_v hτ_v_Γ'
  -- Step 3: Invoke P_enc_total.
  obtain ⟨Δ_P_alt, hcov_P_alt, denT_P_alt, Δ_P_alt_extends, Δ_P_alt_none_out_used_P,
      Δ_P_alt_wt_out, hden_P_alt, hRDom_P_alt, Δ_P_alt_dom⟩ :=
    P_enc_total Δ_ext_alt Δ_fv_P_alt Δ₀_hybrid_alt Δ₀_hybrid_ext_P_alt
      Δ₀_hybrid_alt_none_used_P Δ₀_hybrid_alt_wt P_val_alt hP_val_alt h_den_P_alt
  -- =========================================================================
  -- Build h_typ_alt typing for the lambda under Γ', use
  -- denote_exists_of_typing_fv to obtain denT_alt, and discharge RDom via
  -- lambda_chosen_retract_eq + lambda_hbridge.
  -- =========================================================================
  -- Convert helper lookup-sub hypotheses to entries-subset form.
  have Γ_D_entries_sub_Γ_P : Γ_D.entries ⊆ Γ_P.entries := by
    intro ⟨v, τ_v⟩ hmem
    have hl1 : AList.lookup v Γ_D = some τ_v := AList.mem_lookup_iff.mpr hmem
    have hl2 : AList.lookup v Γ_P = some τ_v := Γ_D_lookup_sub_Γ_P v τ_v hl1
    exact AList.mem_lookup_iff.mp hl2
  have Γ'_entries_sub_Γ_P : Γ'.entries ⊆ Γ_P.entries := by
    intro ⟨v, τ_v⟩ hmem
    have hl1 : AList.lookup v Γ' = some τ_v := AList.mem_lookup_iff.mpr hmem
    have hl2 : AList.lookup v Γ_P = some τ_v := Γ'_lookup_sub_Γ_P v τ_v hl1
    exact AList.mem_lookup_iff.mp hl2
  -- Build h_typ_alt by first proving typing under Γ_P, then strengthening to Γ'.
  set lambda_term : SMT.Term :=
    SMT.Term.lambda [z] [τ.toSMTType.pair β.toSMTType]
      (SMT.Term.and
        (SMT.Term.app D_enc (SMT.Term.fst (.var z)))
        (SMT.Term.eq (SMT.Term.snd (.var z))
          (SMT.substList vs (toDestPair vs (SMT.Term.fst (.var z))) P_enc)))
    with lambda_term_def
  -- Build h_typ_Γ_P : Γ_P ⊢ˢ lambda_term using SMT.Typing.lambda + body typing.
  have h_typ_Γ_P : Γ_P ⊢ˢ lambda_term :
      SMTType.fun (τ.toSMTType.pair β.toSMTType) .bool := by
    have hupdate : SMT.TypeContext.update Γ_P [z] [τ.toSMTType.pair β.toSMTType] rfl =
        Γ_P.insert z (τ.toSMTType.pair β.toSMTType) := by
      simp only [SMT.TypeContext.update, List.length_cons, List.length_nil, zero_add,
        Nat.reduceAdd, Fin.cast_eq_self, Fin.getElem_fin, Fin.val_eq_zero,
        List.getElem_cons_zero, Fin.foldl_succ, Fin.foldl_zero]
    refine SMT.Typing.lambda Γ_P [z] [τ.toSMTType.pair β.toSMTType] _ .bool ?_ ?_ ?_ ?_ ?_
    · intro v hv; rw [List.mem_singleton] at hv; subst hv; exact z_not_Γ_P
    · intro v hv; simp only [List.mem_singleton] at hv; subst hv
      simp only [SMT.bv, List.append_nil, List.nil_append, List.mem_append, not_or]
      refine ⟨?_, ?_⟩
      · intro hbv
        have typ_D_enc_Γ_P_ins := SMT.Typing.weakening
          (SMT.TypeContext.entries_subset_insert_of_notMem
            (τ := τ.toSMTType.pair β.toSMTType) z_not_Γ_P)
          (SMT.Typing.weakening Γ_D_entries_sub_Γ_P typ_D_enc)
        exact SMT.Typing.bv_notMem_context typ_D_enc_Γ_P_ins _ hbv
          ((AList.mem_insert _).mpr (Or.inl rfl))
      · intro hbv
        have hbv_P := SMT_bv_substList_subset
          (fun t ht => toDestPair_bv_nil_base (by simp [SMT.bv]) t ht) _ hbv
        have typ_P_enc_ins := SMT.Typing.weakening
          (SMT.TypeContext.entries_subset_insert_of_notMem
            (τ := τ.toSMTType.pair β.toSMTType) z_not_Γ_P) typ_P_enc
        exact SMT.Typing.bv_notMem_context typ_P_enc_ins _ hbv_P
          ((AList.mem_insert _).mpr (Or.inl rfl))
    · exact Nat.zero_lt_succ 0
    · rfl
    · -- Body typing under Γ_P.insert z (...).
      rw [hupdate]
      set Γ_z := Γ_P.insert z (τ.toSMTType.pair β.toSMTType) with Γ_z_def
      have h_ins := SMT.TypeContext.entries_subset_insert_of_notMem
        (v := z) (τ := τ.toSMTType.pair β.toSMTType) z_not_Γ_P
      have hz_lookup : Γ_z.lookup z = some (τ.toSMTType.pair β.toSMTType) :=
        AList.lookup_insert Γ_P
      have h_z_var : Γ_z ⊢ˢ SMT.Term.var z : τ.toSMTType.pair β.toSMTType :=
        SMT.Typing.var Γ_z z _ hz_lookup
      have h_z_fst : Γ_z ⊢ˢ SMT.Term.fst (.var z) : τ.toSMTType :=
        SMT.Typing.fst _ _ _ _ h_z_var
      have h_z_snd : Γ_z ⊢ˢ SMT.Term.snd (.var z) : β.toSMTType :=
        SMT.Typing.snd _ _ _ _ h_z_var
      refine SMT.Typing.and _ _ _ ?_ ?_
      · -- D_app: weaken D_enc from Γ_D to Γ_P (via new hypothesis), then to Γ_z.
        exact SMT.Typing.app _ _ _ _ _
          (SMT.Typing.weakening h_ins
            (SMT.Typing.weakening Γ_D_entries_sub_Γ_P typ_D_enc))
          h_z_fst
      · -- eq_t: z.snd =ˢ substList vs (toDestPair vs z.fst) P_enc.
        refine SMT.Typing.eq _ _ _ β.toSMTType h_z_snd ?_
        -- Apply SMT_Typing_substList under Γ_z.
        -- P_enc weakened from Γ_P to Γ_z (insert z).
        apply SMT_Typing_substList
        · exact SMT.Typing.weakening h_ins typ_P_enc
        · exact toDestPair_bv_nil_base (by simp [SMT.bv])
        · -- hpairs for vs[i].
          set τs := τ.toSMTType.fromProdl (vs.length - 1) with τs_def
          have τs_len : τs.length = vs.length := fromProdl_length_of_hasArity τ_hasArity
          intro i hi_x hi_t hx
          have hi_τs : i < τs.length := τs_len ▸ hi_x
          -- Γ_z.lookup vs[i] = (Γ_P.insert z).lookup vs[i].
          -- Since vs[i] ≠ z (z ∉ vs), this equals Γ_P.lookup vs[i] = some τs[i] (vs_lookup_Γ_P).
          have hvs_i_ne_z : vs[i] ≠ z := by
            intro heq; exact z_not_vs (heq ▸ List.getElem_mem hi_x)
          have h_Γ_z_lookup : Γ_z.lookup vs[i] = some τs[i] := by
            rw [Γ_z_def, AList.lookup_insert_ne hvs_i_ne_z]
            have h := vs_lookup_Γ_P ⟨i, hi_x⟩
            simpa using h
          have h_get : (Γ_z.lookup vs[i]).get hx = τs[i] := by
            simp [h_Γ_z_lookup]
          rw [h_get]
          -- Apply toDestPair_typing_gen.
          have h_result := toDestPair_typing_gen Γ_z vs
            (SMT.Term.fst (.var z)) (SMT.Term.fst (.var z))
            τ.toSMTType [] []
            vs_nemp rfl h_z_fst
            (by rw [τs_def] at τs_len; exact τs_len) rfl
            (fun j hj => absurd hj (Nat.not_lt_zero j))
            i τs[i]
            (by simp only [List.append_nil]; rw [List.getElem?_eq_getElem hi_τs])
          obtain ⟨_, htyp⟩ := h_result
          exact htyp
  -- Strengthen h_typ_Γ_P to h_typ_alt : Γ' ⊢ˢ lambda_term.
  have h_typ_alt : Γ' ⊢ˢ lambda_term :
      SMTType.fun (τ.toSMTType.pair β.toSMTType) .bool := by
    apply SMT.Typing.strengthening_of_fv_subset Γ'_entries_sub_Γ_P h_typ_Γ_P
    intro v hv_fv
    -- v ∈ fv(lambda_term) = fv(lambda) ⊆ Γ' via fv_lambda_sub.
    -- But fv(lambda_term) is the SMT-side fv; we need to equate with B-side fv.
    -- Actually fv_lambda_sub uses B.fv (B.Term.lambda vs D P), not SMT-side.
    -- Need: every SMT free var v of lambda_term is in Γ'.
    -- Strategy: cases on the structure of fv(lambda_term).
    simp only [lambda_term_def, SMT.fv, List.mem_removeAll_iff] at hv_fv
    obtain ⟨hv_body, hv_nz⟩ := hv_fv
    have hv_ne_z : v ≠ z := by
      intro rfl; exact hv_nz (List.mem_singleton.mpr rfl)
    simp only [List.mem_append] at hv_body
    rcases hv_body with (hv_D | hv_z1) | (hv_z2 | hv_subst)
    · -- v ∈ fv D_enc. v ∈ Γ_D → v ∈ Γ' via Γ_D_dom_sub_Γ'.
      have hv_Γ_D : v ∈ Γ_D := Typing.mem_context_of_mem_fv typ_D_enc hv_D
      exact Γ_D_dom_sub_Γ' v hv_Γ_D
    · simp only [List.mem_singleton] at hv_z1
      exact absurd hv_z1 hv_ne_z
    · simp only [List.mem_singleton] at hv_z2
      exact absurd hv_z2 hv_ne_z
    · -- v ∈ fv(substList vs (toDestPair vs (z.fst)) P_enc).
      rcases SMT_mem_fv_substList hv_subst with hv_P | ⟨t, ht, hv_t⟩
      · -- v ∈ fv P_enc. Need v ∈ Γ'.
        have hv_Γ_P : v ∈ Γ_P := Typing.mem_context_of_mem_fv typ_P_enc hv_P
        -- Need v ∉ vs (else contradiction with substList).
        have hv_not_vs : v ∉ vs := by
          intro hvs
          suffices hlen : vs.length ≤ (toDestPair vs (SMT.Term.fst (.var z))).length by
            have hts : ∀ t ∈ toDestPair vs (SMT.Term.fst (.var z)), v ∉ SMT.fv t := by
              intro t ht hv_t
              have := SMT_fv_toDestPair_subset_base (v := v) (z := z)
                (t₀ := SMT.Term.fst (.var z))
                (by intro w hw; simp only [SMT.fv, List.mem_singleton] at hw; exact hw)
                ht hv_t
              exact hv_ne_z this
            exact absurd hv_subst
              (SMT_not_mem_fv_substList_of_mem_vars hlen hvs hts)
          suffices ∀ (ws : List SMT.𝒱) (zp : SMT.Term) (acc : List SMT.Term)
              (d : SMT.Term),
              ws.length + acc.length ≤ (toDestPair ws zp acc d).length by
            simpa using this vs (SMT.Term.fst (.var z)) [] (SMT.Term.fst (.var z))
          intro ws
          induction ws with
          | nil => intro _ acc _; simp [toDestPair]
          | cons w ws' ih =>
            intro zp acc d
            cases ws' with
            | nil => simp [toDestPair]; omega
            | cons w' ws'' =>
              simp only [toDestPair]
              have := ih (.fst d) (.snd d :: acc) (.fst d)
              simp [List.length] at this ⊢; omega
        exact Γ_P_dom_sub_Γ' v hv_Γ_P hv_not_vs
      · -- v ∈ fv(toDestPair_elt). v = z (impossible since v ≠ z).
        have hv_eq_z : v = z := SMT_fv_toDestPair_subset_base (v := v) (z := z)
          (t₀ := SMT.Term.fst (.var z))
          (by intro w hw; simp only [SMT.fv, List.mem_singleton] at hw; exact hw)
          ht hv_t
        exact absurd hv_eq_z hv_ne_z
  -- Build hcompat for denote_exists_of_typing_fv.
  have hcompat : SMT.RenamingContext.RespectsTypeContextOnFV Δ'_alt Γ'
      ((λˢ [z]) [τ.toSMTType.pair β.toSMTType]
        ((@ˢD_enc) (SMT.Term.var z).fst ∧ˢ
          ((SMT.Term.var z).snd =ˢ
            SMT.substList vs (toDestPair vs (SMT.Term.var z).fst) P_enc))) := by
    intro v τ_v hv_fv hlookup
    have hcov_v := Δ'_alt_covers_lambda v hv_fv
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hcov_v
    refine ⟨d, hd, ?_⟩
    exact Δ'_alt_wt v d hd τ_v hlookup
  -- Apply denote_exists_of_typing_fv to obtain denT_alt.
  have hden_exists := SMT.RenamingContext.denote_exists_of_typing_fv
    h_typ_alt hcompat Δ'_alt_covers_lambda
  obtain ⟨denT_alt, hden_alt_eq, hden_alt_ty⟩ := hden_exists
  -- Discharge the existential.
  refine ⟨Δ'_alt, Δ'_alt_covers_lambda, denT_alt, Δ'_alt_extends_Δ₀_alt,
    Δ'_alt_none_out, Δ'_alt_wt, hden_alt_eq, ?_, Δ'_alt_dom_Γ'⟩
  -- RDom — discharge via case-analysis on 𝒟_alt = ∅.
  -- Branch (a): 𝒟_alt ≠ ∅ → use lambda_chosen_retract_eq with lambda_hbridge.
  -- Branch (b): 𝒟_alt = ∅ → derive T_alt = ∅ and use the empty-retract result.
  have denD_alt_type : denD_alt.snd.fst = τ.toSMTType.fun SMTType.bool := hRDom_D_alt.1
  have denD_alt_func : ⟦τ.toSMTType⟧ᶻ.IsFunc 𝔹 denD_alt.fst := by
    have := denD_alt.snd.snd
    rw [denD_alt_type, SMTType.toZFSet] at this
    exact ZFSet.mem_funs.mp this
  have denD_alt_retract : retract τ.set denD_alt.fst = 𝒟_alt := hRDom_D_alt.2
  have hdenT_alt_func : ⟦τ.toSMTType.pair β.toSMTType⟧ᶻ.IsFunc 𝔹 denT_alt.fst := by
    have := denT_alt.snd.snd
    rw [hden_alt_ty, SMTType.toZFSet] at this
    exact ZFSet.mem_funs.mp this
  -- Build hcov_D_upd_alt and hden_D_upd_alt for lambda_chosen_retract_eq.
  -- The key step is showing Δ'_alt agrees with Δ_D_alt on fv D_enc.
  have Δ'_alt_agrees_Δ_D_alt :
      ∀ v ∈ SMT.fv D_enc, Δ'_alt v = Δ_D_alt v := by
    intro v hv_fv
    -- v ∈ fv D_enc ⇒ v ∈ Γ_D (via typing)
    have hv_Γ_D : v ∈ Γ_D := Typing.mem_context_of_mem_fv typ_D_enc hv_fv
    -- Δ_D_alt covers fv D_enc
    have hΔ_D_alt_some : ∃ d, Δ_D_alt v = some d :=
      Option.isSome_iff_exists.mp (hcov_D_alt v hv_fv)
    obtain ⟨d_D, hd_D⟩ := hΔ_D_alt_some
    -- Cascade analysis on Δ'_alt
    show (match Δ₀_alt v with
      | some d => some d
      | none => match Δ_D_alt v with
        | some d => some d
        | none => Δ' v) = Δ_D_alt v
    rw [hd_D]
    cases hΔ₀ : Δ₀_alt v with
    | none => simp only [hΔ₀, hd_D]
    | some d₀ =>
      simp only [hΔ₀]
      -- Need d₀ = d_D
      -- Case: v ∈ used_D (since Δ_D_alt v = some d_D, by Δ_D_alt_none_out contrapositive).
      have hv_used_D : v ∈ used_D := by
        by_contra hv_not
        rw [Δ_D_alt_none_out v hv_not] at hd_D
        exact Option.noConfusion hd_D
      -- Case split on v ∈ B.fv D vs not.
      by_cases hv_fv_D : v ∈ B.fv D
      · -- v ∈ B.fv D ⇒ Δ_alt v is some, both Δ₀_alt and Δ_D_alt equal canonical(Δ_alt v).
        have hv_lambda : v ∈ B.fv (B.Term.lambda vs D P) :=
          B.fv.mem_lambda (.inl hv_fv_D)
        have hΔ_alt_v : (Δ_alt v).isSome = true := Δ_fv_alt v hv_lambda
        obtain ⟨bdom, hbdom⟩ := Option.isSome_iff_exists.mp hΔ_alt_v
        -- toSMTOnFV Δ_alt D v = toSMT Δ_alt v (since v ∈ B.fv D)
        have h_onFV_D_eq : B.RenamingContext.toSMTOnFV Δ_alt D v =
            B.RenamingContext.toSMT Δ_alt v := by
          show B.RenamingContext.toSMT (B.RenamingContext.restrictToFV Δ_alt D) v =
              B.RenamingContext.toSMT Δ_alt v
          unfold B.RenamingContext.toSMT
          rw [B.RenamingContext.restrictToFV_eq_of_mem hv_fv_D]
        -- toSMTOnFV Δ_alt lambda v = toSMT Δ_alt v
        have h_onFV_lambda_eq :
            B.RenamingContext.toSMTOnFV Δ_alt (B.Term.lambda vs D P) v =
            B.RenamingContext.toSMT Δ_alt v := by
          show B.RenamingContext.toSMT
              (B.RenamingContext.restrictToFV Δ_alt (B.Term.lambda vs D P)) v =
              B.RenamingContext.toSMT Δ_alt v
          unfold B.RenamingContext.toSMT
          rw [B.RenamingContext.restrictToFV_eq_of_mem hv_lambda]
        -- toSMT Δ_alt v = some d_smt for some d_smt (since Δ_alt v is some)
        have h_toSMT_some : ∃ d_smt,
            B.RenamingContext.toSMT Δ_alt v = some d_smt := by
          simp only [B.RenamingContext.toSMT, hbdom, Option.pure_def]
          exact ⟨_, rfl⟩
        obtain ⟨d_smt, hd_smt⟩ := h_toSMT_some
        have h_onFV_D : B.RenamingContext.toSMTOnFV Δ_alt D v = some d_smt :=
          h_onFV_D_eq.trans hd_smt
        have h_onFV_lambda :
            B.RenamingContext.toSMTOnFV Δ_alt (B.Term.lambda vs D P) v = some d_smt :=
          h_onFV_lambda_eq.trans hd_smt
        -- Δ₀_alt v = some d_smt (via hext_alt)
        have hΔ₀_alt_v : Δ₀_alt v = some d_smt := hext_alt h_onFV_lambda
        rw [hΔ₀] at hΔ₀_alt_v; cases hΔ₀_alt_v
        -- Δ₀_alt_D v = some d₀ (definition)
        have hΔ₀_alt_D_v : Δ₀_alt_D v = some d₀ := by
          show (match B.RenamingContext.toSMTOnFV Δ_alt D v with
            | some d => some d
            | none => if v ∈ used_D then
                match Δ₀_alt v with
                | some d => some d
                | none => none
              else none) = some d₀
          rw [h_onFV_D]
        -- Δ_D_alt v = some d₀ (via hext_D_alt)
        have hΔ_D_alt_v : Δ_D_alt v = some d₀ := hext_D_alt hΔ₀_alt_D_v
        rw [hd_D] at hΔ_D_alt_v
        cases hΔ_D_alt_v; rfl
      · -- v ∉ B.fv D ⇒ toSMTOnFV Δ_alt D v = none, Δ₀_alt_D uses Δ₀_alt path.
        have h_onFV_D_none : B.RenamingContext.toSMTOnFV Δ_alt D v = none := by
          simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
            B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_fv_D]
        have hΔ₀_alt_D_v : Δ₀_alt_D v = some d₀ := by
          show (match B.RenamingContext.toSMTOnFV Δ_alt D v with
            | some d => some d
            | none => if v ∈ used_D then
                match Δ₀_alt v with
                | some d => some d
                | none => none
              else none) = some d₀
          rw [h_onFV_D_none]; simp [hv_used_D, hΔ₀]
        have hΔ_D_alt_v : Δ_D_alt v = some d₀ := hext_D_alt hΔ₀_alt_D_v
        rw [hd_D] at hΔ_D_alt_v
        cases hΔ_D_alt_v; rfl
  -- z ∉ fv D_enc (from helper signature)
  have z_not_fv_D_alt : z ∉ SMT.fv D_enc := z_not_fv_D
  -- Build hcov_D_upd_alt and hden_D_upd_alt.
  have hcov_D_upd_alt : ∀ W : SMT.Dom,
      SMT.RenamingContext.CoversFV (Function.update Δ'_alt z (some W)) D_enc := by
    intro W v hv
    by_cases hvz : v = z
    · subst hvz; simp [Function.update]
    · rw [Function.update_of_ne hvz]
      rw [Δ'_alt_agrees_Δ_D_alt v hv]
      exact hcov_D_alt v hv
  have hden_D_upd_alt : ∀ W : SMT.Dom,
      ⟦D_enc.abstract (Function.update Δ'_alt z (some W)) (hcov_D_upd_alt W)⟧ˢ
        = some denD_alt := by
    intro W
    have h_agree : SMT.RenamingContext.AgreesOnFV
        (Function.update Δ'_alt z (some W)) Δ_D_alt D_enc := by
      intro v hv
      have hvz : v ≠ z := by intro heq; subst heq; exact z_not_fv_D_alt hv
      rw [Function.update_of_ne hvz]
      exact Δ'_alt_agrees_Δ_D_alt v hv
    have heq := SMT.RenamingContext.denote_congr_of_agreesOnFV
      (h1 := hcov_D_upd_alt W) (h2 := hcov_D_alt) h_agree
    unfold SMT.RenamingContext.denote at heq
    rw [heq]
    exact hden_D_alt
  -- Case-split on 𝒟_alt = ∅ to discharge RDom.
  -- Show RDom: ⟨T_alt, ⟨(τ ×ᴮ β).set, hT_alt⟩⟩ ≘ᶻ denT_alt = (denT_alt.snd.fst = ...) ∧
  --   (retract (τ ×ᴮ β).set denT_alt.fst = T_alt).
  -- The first conjunct is hden_alt_ty (modulo a type-equality rewrite).
  -- The second requires case analysis on whether 𝒟_alt = ∅.
  show denT_alt.snd.fst = (τ ×ᴮ β).set.toSMTType ∧
      retract (τ ×ᴮ β).set denT_alt.fst = T_alt
  refine ⟨?_, ?_⟩
  · -- denT_alt.snd.fst = (τ ×ᴮ β).set.toSMTType
    rw [hden_alt_ty]
    show (τ.toSMTType.pair β.toSMTType).fun SMTType.bool = (τ ×ᴮ β).set.toSMTType
    rw [show (τ ×ᴮ β).set.toSMTType =
      ((τ ×ᴮ β).toSMTType).fun SMTType.bool from rfl, h_toSMT]
  · -- retract (τ ×ᴮ β).set denT_alt.fst = T_alt
    -- Extract T_alt's structure from hden_alt by case-analysis on 𝒟_alt = ∅.
    -- Re-derive lambda B-side structure (mirroring hden_alt_data's split_ifs).
    have h_inv := hden_alt
    simp only [B.Term.abstract] at h_inv
    unfold B.denote at h_inv
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h_inv
    obtain ⟨D_dom_pkg, h_den_d, rest_alt⟩ := h_inv
    have h_conv_d : ⟦D.abstract Δ_alt
        (fun v hv => Δ_fv_alt v (B.fv.mem_lambda (.inl hv)))⟧ᴮ =
        some D_dom_pkg := by convert h_den_d using 2
    have hD_dom_eq : D_dom_pkg = ⟨𝒟_alt, ⟨τ.set, h𝒟_alt⟩⟩ := by
      rw [h_conv_d] at hden_D_alt_eq
      exact Option.some.inj hden_D_alt_eq
    subst hD_dom_eq
    simp only at rest_alt
    rw [dif_pos τ_hasArity] at rest_alt
    split_ifs at rest_alt with h_den_E h_typE_det h_nemp h_chosen_arity h_default_arity
    · -- Chosen branch: 𝒟_alt ≠ ∅. Apply lambda_chosen_retract_eq.
      -- Extract T_alt = (𝒟_alt.prod ⟦β⟧ᶻ).sep ℰ_alt from rest_alt.
      simp only [Option.bind_eq_some_iff] at rest_alt
      obtain ⟨P_dom_alt, hP_den_alt_choose, hT_eq⟩ := rest_alt
      simp only [Option.pure_def, Option.some.injEq] at hT_eq
      -- Apply lambda_chosen_retract_eq with the B-side sep predicate as ℰ.
      -- hT_eq tells us T_alt is built from 𝒟_alt.prod and a sep predicate;
      -- we mirror that predicate so hT_eq becomes definitional.
      -- First, derive P_dom_alt.2.fst = β from typing.
      have hP_ty_eq : P_dom_alt.2.fst = β := by
        -- f_alt setup as in chosen branch witness construction.
        let x_choose := Classical.choose (ZFSet.nonempty_exists_iff.mp h_nemp)
        have x_choose_mem : x_choose ∈ 𝒟_alt :=
          Classical.choose_spec (ZFSet.nonempty_exists_iff.mp h_nemp)
        let f_alt : Fin vs.length → B.Dom := fun i =>
          ⟨x_choose.get vs.length i, τ.get vs.length i,
           get_mem_type_of_isTuple h_chosen_arity.1 τ_hasArity h_chosen_arity.2⟩
        have Δ_fv_alt_P : ∀ v ∈ B.fv P, (Function.updates Δ_alt vs
            (List.ofFn fun i => some (f_alt i)) v).isSome = true := by
          intro v hv
          rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup]
          split_ifs with hvs
          · simp [List.getElem_ofFn]
          · exact Δ_fv_alt v (B.fv.mem_lambda (.inr ⟨hv, hvs⟩))
        have hP_den_at_abs : ⟦P.abstract (Function.updates Δ_alt vs
              (List.ofFn fun i => some (f_alt i))) Δ_fv_alt_P⟧ᴮ =
            some P_dom_alt := by
          rw [← denote_term_abstract_go_eq_term_abstract vs_nodup vs_nemp f_alt Δ_fv_alt_P]
          convert hP_den_alt_choose using 2
        obtain ⟨P_v, P_t, hP_v⟩ := P_dom_alt
        have h_wt := denote_welltyped_eq
          (t := P.abstract (Function.updates Δ_alt vs
            (List.ofFn fun i => some (f_alt i))) Δ_fv_alt_P)
          ⟨_, WFTC.of_abstract, β,
            by convert Typing.of_abstract Δ_fv_alt_P typP⟩
          hP_den_at_abs
        exact h_wt.symm
      have hT_alt_chosen :=
        congrArg (fun (p : B.Dom) => p.1) hT_eq
      simp only at hT_alt_chosen
      rw [hP_ty_eq] at hT_alt_chosen
      refine (lambda_chosen_retract_eq
        (vs := vs) (τ := τ) (β := β) (D_enc := D_enc) (P_enc := P_enc)
        (z := z) (Δ' := Δ'_alt) (denT' := denT_alt) (denD_val := denD_alt)
        (𝒟_val := 𝒟_alt) (ℰ := ?ℰ)
        vs_nemp vs_nodup rfl Δ'_alt_covers_lambda hden_alt_eq hden_alt_ty
        hdenT_alt_func hcov_D_upd_alt hden_D_upd_alt
        denD_alt_type denD_alt_func h𝒟_alt denD_alt_retract
        hT_alt ?hT_eq_alt ?hbridge_alt).2
      case ℰ =>
        classical
        exact fun xy =>
          if hxy : xy.hasArity 2 then
            if hx : xy.π₁.hasArity vs.length ∧ xy.π₁ ∈ 𝒟_alt then
              match (motive := Option B.Dom → Prop) ⟦(B.Term.abstract.go P vs Δ_alt
                  (fun v hv hvs =>
                    Δ_fv_alt v (B.fv.mem_lambda (.inr ⟨hv, hvs⟩)))).uncurry
                  (fun i => ⟨xy.π₁.get vs.length i, ⟨τ.get vs.length i,
                    get_mem_type_of_isTuple hx.1 τ_hasArity (by
                      rw [BType.toZFSet, ZFSet.mem_powerset] at h𝒟_alt
                      exact h𝒟_alt hx.2)⟩⟩)⟧ᴮ with
              | some ⟨ex, ⟨ξ, _⟩⟩ => if ξ = β then ex = xy.π₂ else False
              | none => False
            else False
          else False
      case hT_eq_alt =>
        -- (𝒟_alt.prod ⟦β⟧ᶻ).sep ℰ = T_alt
        -- This follows from hT_eq directly (P_dom_alt.2.fst = β derivation).
        -- We rebuild the matching dependence to recover T_alt.
        exact hT_alt_chosen
      case hbridge_alt =>
        -- Mirror main proof's hbridge case (lines 2625-3018) adapted for alt-Δ.
        -- All ingredients assembled from local context.
        intro xy hxy_mem
        -- Decompose xy ∈ ⟦τ ×ᴮ β⟧ᶻ = ⟦τ⟧ᶻ.prod ⟦β⟧ᶻ.
        have hxy_prod : xy ∈ ⟦τ⟧ᶻ.prod ⟦β⟧ᶻ := hxy_mem
        rw [ZFSet.mem_prod] at hxy_prod
        obtain ⟨a, ha_mem, b, hb_mem, hxy_eq⟩ := hxy_prod
        have hxy_pair : xy = a.pair b := hxy_eq
        have hxy_π₁_eq : xy.π₁ = a := by rw [hxy_pair, ZFSet.π₁_pair]
        have hxy_π₂_eq : xy.π₂ = b := by rw [hxy_pair, ZFSet.π₂_pair]
        have hx_mem : xy.π₁ ∈ ⟦τ⟧ᶻ := hxy_π₁_eq ▸ ha_mem
        have hy_mem : xy.π₂ ∈ ⟦β⟧ᶻ := hxy_π₂_eq ▸ hb_mem
        have hxy_pair' : xy = xy.π₁.pair xy.π₂ := by
          rw [hxy_π₁_eq, hxy_π₂_eq, ← hxy_pair]
        have hxy_π₁_arity : xy.π₁.hasArity vs.length :=
          hasArity_of_mem_toZFSet τ_hasArity hx_mem
        -- z ∉ fv(P_enc) (helper signature).
        have z_not_fv_P_loc : z ∉ SMT.fv P_enc := z_not_fv_P
        -- vs ∉ bv(P_enc) using typing of P_enc under Γ_P.
        have hvs_not_bv_P : ∀ v ∈ vs, v ∉ SMT.bv P_enc := by
          intro v hv hbv
          have hidx : vs.idxOf v < vs.length := List.idxOf_lt_length_of_mem hv
          have hv_Γ_P : v ∈ Γ_P := by
            have h := vs_lookup_Γ_P ⟨vs.idxOf v, hidx⟩
            have hv_eq : vs[(⟨vs.idxOf v, hidx⟩ : Fin vs.length)] = v :=
              List.getElem_idxOf hidx
            rw [hv_eq] at h
            exact AList.lookup_isSome.mp (by simp [h])
          exact SMT.Typing.bv_notMem_context typ_P_enc v hbv hv_Γ_P
        have z_not_bv_P : z ∉ SMT.bv P_enc := by
          intro hbv
          exact SMT.Typing.bv_notMem_context
            (SMT.Typing.weakening
              (SMT.TypeContext.entries_subset_insert_of_notMem (τ := τ.toSMTType) z_not_Γ_P)
              typ_P_enc)
            z hbv ((AList.mem_insert _).mpr (Or.inl rfl))
        have fv_substList_disj_vs :
            ∀ v ∈ SMT.fv (SMT.substList vs (toDestPair vs (SMT.Term.var z).fst) P_enc),
            v ≠ z → v ∉ vs := by
          intro v hv hne hvs
          rcases SMT_mem_fv_substList hv with hv_P | ⟨t, ht, hv_t⟩
          · have hts : ∀ t ∈ toDestPair vs (SMT.Term.fst (.var z)), v ∉ SMT.fv t :=
              fun t ht hv_t => hne (SMT_fv_toDestPair_subset_base
                (t₀ := (SMT.Term.var z).fst)
                (by intro w hw; simp only [SMT.fv, List.mem_singleton] at hw; exact hw)
                ht hv_t)
            have hlen : vs.length ≤ (toDestPair vs (SMT.Term.fst (.var z))).length := by
              suffices ∀ (ws : List SMT.𝒱) (zp : SMT.Term) (acc : List SMT.Term)
                  (d : SMT.Term),
                  ws.length + acc.length ≤ (toDestPair ws zp acc d).length by
                simpa using this vs (SMT.Term.fst (.var z)) [] (SMT.Term.fst (.var z))
              intro ws; induction ws with
              | nil => intro _ acc _; simp [toDestPair]
              | cons w ws' ih =>
                intro zp acc d; cases ws' with
                | nil => simp [toDestPair]; omega
                | cons w' ws'' =>
                  simp only [toDestPair]
                  have := ih (.fst d) (.snd d :: acc) (.fst d)
                  simp [List.length] at this ⊢; omega
            exact absurd hv (SMT_not_mem_fv_substList_of_mem_vars hlen hvs hts)
          · exact hne (SMT_fv_toDestPair_subset_base
              (t₀ := (SMT.Term.var z).fst)
              (by intro w hw; simp only [SMT.fv, List.mem_singleton] at hw; exact hw)
              ht hv_t)
        -- body_t and supporting coverage lemmas.
        set body_t : SMT.Term :=
          ((@ˢD_enc) (SMT.Term.var z).fst ∧ˢ
            ((SMT.Term.var z).snd =ˢ
              SMT.substList vs (toDestPair vs (SMT.Term.var z).fst) P_enc)) with body_t_def
        have hgo_cov : ∀ x ∈ SMT.fv body_t, x ∉ [z] → (Δ'_alt x).isSome = true :=
          fun x hx hxz => Δ'_alt_covers_lambda x (SMT.fv.mem_lambda ⟨hx, hxz⟩)
        have hcov_body_upd : ∀ W : SMT.Dom,
            SMT.RenamingContext.CoversFV (Function.update Δ'_alt z (some W)) body_t := by
          intro W x hx
          by_cases hxz : x = z
          · subst hxz; simp [Function.update]
          · rw [Function.update_of_ne hxz]; exact hgo_cov x hx (by simp [hxz])
        have hcov_substList_upd : ∀ W : SMT.Dom,
            SMT.RenamingContext.CoversFV (Function.update Δ'_alt z (some W))
              (SMT.substList vs (toDestPair vs (SMT.Term.var z).fst) P_enc) := fun W x hx =>
          hcov_body_upd W x (by
            simp only [body_t_def, SMT.fv, List.mem_append]
            exact Or.inr (Or.inr hx))
        -- Δ_ctx_source: Δ'_alt = toSMT Δ_alt for fv P, v ∉ vs.
        have Δ_ctx_source : ∀ v ∈ B.fv P, v ∉ vs →
            Δ'_alt v = B.RenamingContext.toSMT Δ_alt v := by
          intro v hv_fv_P hvs
          have hv_lambda : v ∈ B.fv (B.Term.lambda vs D P) :=
            B.fv.mem_lambda (.inr ⟨hv_fv_P, hvs⟩)
          have hΔ_alt_v : (Δ_alt v).isSome = true := Δ_fv_alt v hv_lambda
          obtain ⟨bdom, hbdom⟩ := Option.isSome_iff_exists.mp hΔ_alt_v
          -- toSMTOnFV Δ_alt (lambda) v = toSMT Δ_alt v (since v ∈ B.fv lambda).
          have h_onFV : B.RenamingContext.toSMTOnFV Δ_alt
              (B.Term.lambda vs D P) v = B.RenamingContext.toSMT Δ_alt v := by
            simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
              B.RenamingContext.restrictToFV_eq_of_mem hv_lambda]
          have h_smt_some : ∃ d, B.RenamingContext.toSMT Δ_alt v = some d := by
            simp only [B.RenamingContext.toSMT, hbdom, Option.pure_def]; exact ⟨_, rfl⟩
          obtain ⟨d_smt, hd_smt⟩ := h_smt_some
          have hΔ₀_alt_v : Δ₀_alt v = some d_smt :=
            hext_alt (h_onFV.trans hd_smt)
          -- Δ'_alt v = match Δ₀_alt v with | some d => some d | _ => ...
          show Δ'_alt v = B.RenamingContext.toSMT Δ_alt v
          rw [Δ'_alt_def]
          show (match Δ₀_alt v with
            | some d => some d
            | none => match Δ_D_alt v with
                | some d => some d
                | none => Δ' v) = B.RenamingContext.toSMT Δ_alt v
          rw [hΔ₀_alt_v, hd_smt]
        -- P_enc_total_simple: simplified P_enc_total signature for lambda_hbridge.
        -- Operates on the `used_P` constraint directly (used_St₃ := used_P in lambda_hbridge).
        -- This obviates the need for a `used' ⊆ used_P` translation.
        have P_enc_total_simple :
            ∀ (Δ_a : B.RenamingContext.Context)
              (Δ_fv_a : ∀ v ∈ B.fv P, (Δ_a v).isSome = true)
              (Δ₀_a : SMT.RenamingContext.Context),
              SMT.RenamingContext.ExtendsOnSourceFV Δ₀_a Δ_a P →
              (∀ v ∉ used_P, Δ₀_a v = none) →
              ∀ (T_a : ZFSet) (hT_a : T_a ∈ ⟦β⟧ᶻ),
                ⟦P.abstract Δ_a Δ_fv_a⟧ᴮ = some ⟨T_a, ⟨β, hT_a⟩⟩ →
                ∃ (Δ'_a : SMT.RenamingContext.Context)
                  (hcov_a : SMT.RenamingContext.CoversFV Δ'_a P_enc)
                  (denT_a : SMT.Dom),
                  SMT.RenamingContext.Extends Δ'_a Δ₀_a ∧
                  ⟦P_enc.abstract Δ'_a hcov_a⟧ˢ = some denT_a ∧
                  (⟨T_a, ⟨β, hT_a⟩⟩ : B.Dom) ≘ᶻ denT_a := by
          intro Δ_a Δ_fv_a Δ₀_a hext' hnone' T_a hT_a hden'
          obtain ⟨Δ'_out, hcov_out, denT_out, hext_out, _, _, hden_out, hRDom_out, _⟩ :=
            P_enc_total Δ_a Δ_fv_a Δ₀_a hext' hnone'
              (SMT.RenamingContext.ExtendsOnSourceFV.wt hext' typ_P_enc) T_a hT_a hden'
          exact ⟨Δ'_out, hcov_out, denT_out, hext_out, hden_out, hRDom_out⟩
        -- Now case-split on xy.π₁ ∈ 𝒟_alt.
        by_cases hxy_𝒟 : xy.π₁ ∈ 𝒟_alt
        · -- Case: xy.π₁ ∈ 𝒟_alt. Apply lambda_hbridge directly.
          have hcanon_mem : (ZFSet.fapply (BType.canonicalIsoSMTType (τ ×ᴮ β)).1
              (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType (τ ×ᴮ β)).2.1)
              ⟨xy, by rwa [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType (τ ×ᴮ β)).2.1]⟩).1 ∈
              ⟦τ.toSMTType.pair β.toSMTType⟧ᶻ :=
            (ZFSet.fapply (BType.canonicalIsoSMTType (τ ×ᴮ β)).1
              (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType (τ ×ᴮ β)).2.1)
              ⟨xy, by rwa [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType (τ ×ᴮ β)).2.1]⟩).2
          let Wxy : SMT.Dom := ⟨_, τ.toSMTType.pair β.toSMTType, hcanon_mem⟩
          have hWxy_mem : Wxy.fst ∈ ⟦τ.toSMTType.pair β.toSMTType⟧ᶻ := hcanon_mem
          -- Unfold lambda denotation.
          have hlamVal' := hden_alt_eq
          rw [SMT.Term.abstract, dif_pos (by rfl)] at hlamVal'
          simp only [SMT.denote] at hlamVal'
          rw [dif_pos (show [z].length > 0 from Nat.zero_lt_succ 0)] at hlamVal'
          split_ifs at hlamVal' with h_isSome h_typ_det
          · let xₙ : Fin 1 → SMT.Dom := fun _ => Wxy
            have hxₙ_spec : ∀ i, (xₙ i).snd.fst = [τ.toSMTType.pair β.toSMTType][↑i] ∧
                (xₙ i).fst ∈ ⟦[τ.toSMTType.pair β.toSMTType][↑i]⟧ᶻ :=
              fun ⟨i, hi⟩ => by
                simp only [List.length_cons, List.length_nil, Nat.lt_one_iff] at hi
                subst hi; exact ⟨rfl, hWxy_mem⟩
            have hgo_xy := funAbstractGoSingle (Δctx := Δ'_alt) (P := body_t) (v := z)
              (τ := τ.toSMTType.pair β.toSMTType) hgo_cov hcov_body_upd xₙ hxₙ_spec
            obtain ⟨body_val, hbody_val⟩ :=
              Option.isSome_iff_exists.mp (show (⟦body_t.abstract _ _⟧ˢ).isSome = true by
                rw [← hgo_xy]; exact h_isSome hxₙ_spec)
            -- Build h_pair_mem: Wxy.fst.pair body_val.fst ∈ denT_alt.fst.
            have h_pair_mem : Wxy.fst.pair body_val.fst ∈ denT_alt.fst := by
              simp only [Option.pure_def, Option.some.injEq] at hlamVal'
              have hlamVal_fst : denT_alt.fst = _ := congrArg (·.fst) hlamVal'.symm
              simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.sub_self,
                Fin.foldr_zero, List.getElem_cons_zero] at hlamVal_fst
              rw [hlamVal_fst, ZFSet.mem_lambda]
              refine ⟨Wxy.fst, body_val.fst, rfl, hWxy_mem, ?_, ?_⟩
              · have hden_xₙ : ⟦(SMT.Term.abstract.go body_t [z] Δ'_alt hgo_cov).uncurry xₙ⟧ˢ
                    = some body_val := by rw [hgo_xy]; exact hbody_val
                have hγ := h_typ_det xₙ
                  (fun _ => ⟨(τ.toSMTType.pair β.toSMTType).defaultZFSet,
                           τ.toSMTType.pair β.toSMTType, SMTType.mem_toZFSet_of_defaultZFSet⟩)
                  hxₙ_spec
                  (fun ⟨i, hi⟩ => by
                    simp only [List.length_cons, List.length_nil] at hi
                    have hi' : i = 0 := by omega
                    subst hi'; exact ⟨rfl, SMTType.mem_toZFSet_of_defaultZFSet⟩)
                rw [congrArg (·.snd.fst) (Option.get_of_eq_some _ hden_xₙ)] at hγ
                exact hγ ▸ body_val.snd.snd
              · split_ifs with hw'
                · let xₙ' := fun i : Fin 1 =>
                      (⟨Wxy.fst.get 1 i, [τ.toSMTType.pair β.toSMTType][↑i], hw'.2 i⟩ : SMT.Dom)
                  have hgo' := funAbstractGoSingle (Δctx := Δ'_alt) (P := body_t) (v := z)
                    (τ := τ.toSMTType.pair β.toSMTType)
                    hgo_cov hcov_body_upd xₙ' (fun i => ⟨rfl, hw'.2 i⟩)
                  have hden' : ⟦(SMT.Term.abstract.go body_t [z] Δ'_alt hgo_cov).uncurry xₙ'⟧ˢ
                      = some body_val := by
                    rw [hgo', show xₙ' ⟨0, Nat.zero_lt_one⟩ = Wxy from rfl]; exact hbody_val
                  exact (congrArg (·.fst) (Option.get_of_eq_some _ hden')).symm
                · exact absurd ⟨trivial, fun ⟨i, hi⟩ => by
                    simp only [Nat.lt_one_iff] at hi; subst hi; exact hWxy_mem⟩ hw'
            -- Connect fapply to body_val.fst.
            have h_fap_eq : (ZFSet.fapply denT_alt.fst (ZFSet.is_func_is_pfunc hdenT_alt_func)
                ⟨Wxy.fst, by rw [ZFSet.is_func_dom_eq hdenT_alt_func]; exact hWxy_mem⟩).1 =
                body_val.fst :=
              congrArg Subtype.val
                (ZFSet.fapply.of_pair (ZFSet.is_func_is_pfunc hdenT_alt_func) h_pair_mem)
            -- Apply lambda_hbridge with `used_St₂ := used_St₃ := used_P`.
            -- Use a custom Δ_D_eval := Δ'_alt masked by used_P.
            -- This sidesteps the issue that Δ_D_alt cannot directly extend
            -- toSMTOnFV Δ_alt lambda (which requires coverage on fv P \ vs).
            have fv_P_enc_used_P : ∀ v ∈ SMT.fv P_enc, v ∈ used_P := by
              intro v hv_fv
              have hΔ_P_some : Δ_P_alt v ≠ none := by
                have ⟨_, hd⟩ := Option.isSome_iff_exists.mp (hcov_P_alt v hv_fv)
                rw [hd]; simp
              by_contra hv_not
              exact hΔ_P_some (Δ_P_alt_none_out_used_P v hv_not)
            -- Custom Δ_D_eval: Δ'_alt masked by used_P.
            -- Outside used_P → none. Inside used_P → Δ'_alt's value.
            let Δ_D_eval' : SMT.RenamingContext.Context := fun v =>
              if v ∈ used_P then Δ'_alt v else none
            -- Δ_D_eval' vanishes outside used_P.
            have Δ_D_eval'_none_St₂ : ∀ v ∉ used_P, Δ_D_eval' v = none := by
              intro v hv
              show (if v ∈ used_P then _ else none) = none
              rw [if_neg hv]
            -- Δ_D_eval' extends toSMTOnFV Δ_alt lambda.
            -- For v ∈ B.fv lambda, we have v ∈ used_P (via covers_D + used_D_sub_used_P
            -- for fv D, or covers_P for fv P \ vs), and Δ'_alt v = some d via hext_alt.
            have Δ_D_eval'_extends : SMT.RenamingContext.Extends Δ_D_eval'
                (B.RenamingContext.toSMTOnFV Δ_alt (B.Term.lambda vs D P)) := by
              intro v d hv_eq
              have hv_lambda_fv : v ∈ B.fv (B.Term.lambda vs D P) := by
                by_contra hv_not
                simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                  B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_not] at hv_eq
              have hv_used_P : v ∈ used_P := by
                rw [B.fv, List.mem_append] at hv_lambda_fv
                rcases hv_lambda_fv with hv_D | hv_P_minus_vs
                · exact used_D_sub_used_P (covers_D v hv_D)
                · rw [List.mem_removeAll_iff] at hv_P_minus_vs
                  exact covers_P v hv_P_minus_vs.1
              have hΔ₀_v : Δ₀_alt v = some d := hext_alt hv_eq
              have hΔ'_v : Δ'_alt v = some d := Δ'_alt_extends_Δ₀_alt hΔ₀_v
              show (if v ∈ used_P then Δ'_alt v else none) = some d
              rw [if_pos hv_used_P, hΔ'_v]
            have hbridge_iff := lambda_hbridge vs_nemp vs_nodup τ_hasArity
              z_not_fv_D z_not_fv_P_loc z_not_vs vs_not_D_fv hvs_not_bv_P z_not_bv_P
              (Δ_ctx := Δ'_alt) hcov_body_upd hcov_D_upd_alt hden_D_upd_alt
              denD_alt_type denD_alt_func h𝒟_alt denD_alt_retract
              hcov_substList_upd fv_substList_disj_vs
              Δ_fv_alt typP
              Δ_D_eval'_extends
              Δ_ctx_source
              Δ_D_eval'_none_St₂ vs_used_P (fun _ h => h)
              fv_P_enc_used_P
              P_enc_total_simple
              (fun hx hxD => h_den_E hx hxD)
              xy hx_mem hy_mem hxy_pair' hxy_π₁_arity hxy_𝒟
              body_val hbody_val
            -- Convert the iff.
            rw [show (↑(ZFSet.fapply denT_alt.fst (ZFSet.is_func_is_pfunc hdenT_alt_func)
                ⟨↑(ZFSet.fapply (BType.canonicalIsoSMTType (τ ×ᴮ β)).1
                  (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType (τ ×ᴮ β)).2.1)
                  ⟨xy, by rwa [ZFSet.is_func_dom_eq
                    (BType.canonicalIsoSMTType (τ ×ᴮ β)).2.1]⟩), _⟩)) =
                body_val.fst from h_fap_eq]
            rw [ZFSet.mem_sep]
            constructor
            · intro hbody_true
              refine ⟨?_, ?_⟩
              · rw [ZFSet.mem_prod]
                exact ⟨xy.π₁, hxy_𝒟, xy.π₂, hy_mem, hxy_pair'⟩
              · have hxy_arity2 : xy.hasArity 2 := hxy_pair ▸ ZFSet.isTuple_pair
                have hx_cond : xy.π₁.hasArity vs.length ∧ xy.π₁ ∈ 𝒟_alt :=
                  ⟨hxy_π₁_arity, hxy_𝒟⟩
                simp only [dif_pos hxy_arity2, dif_pos hx_cond]
                obtain ⟨Px, hPx_mem, hPx_den, hPx_eq⟩ := hbridge_iff.mp hbody_true
                simp only [hPx_den, hPx_eq, ↓reduceIte]
            · intro ⟨hprod, hℰ⟩
              rw [ZFSet.mem_prod] at hprod
              have hxy_arity2 : xy.hasArity 2 := hxy_pair ▸ ZFSet.isTuple_pair
              have hx_cond : xy.π₁.hasArity vs.length ∧ xy.π₁ ∈ 𝒟_alt :=
                ⟨hxy_π₁_arity, hxy_𝒟⟩
              simp only [dif_pos hxy_arity2, dif_pos hx_cond] at hℰ
              apply hbridge_iff.mpr
              rcases h_match : ⟦(B.Term.abstract.go P vs Δ_alt
                  (fun v hv hvs =>
                    Δ_fv_alt v (B.fv.mem_lambda (.inr ⟨hv, hvs⟩)))).uncurry
                  fun i => ⟨xy.π₁.get vs.length i,
                    ⟨τ.get vs.length i, by
                      rw [BType.toZFSet, ZFSet.mem_powerset] at h𝒟_alt
                      exact get_mem_type_of_isTuple hxy_π₁_arity τ_hasArity hx_mem⟩⟩⟧ᴮ with
                _ | ⟨Px_val, ξ, hPx_mem⟩
              · simp [h_match] at hℰ
              · simp only [h_match] at hℰ
                split_ifs at hℰ with hξ
                exact ⟨Px_val, hξ ▸ hPx_mem, by subst hξ; rfl, hℰ⟩
        · -- Case: xy.π₁ ∉ 𝒟_alt.
          constructor
          · intro hfap_true
            -- Build body_val and use AND-decomposition.
            have hcanon_mem : (ZFSet.fapply (BType.canonicalIsoSMTType (τ ×ᴮ β)).1
                (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType (τ ×ᴮ β)).2.1)
                ⟨xy, by rwa [ZFSet.is_func_dom_eq
                  (BType.canonicalIsoSMTType (τ ×ᴮ β)).2.1]⟩).1 ∈
                ⟦τ.toSMTType.pair β.toSMTType⟧ᶻ :=
              (ZFSet.fapply (BType.canonicalIsoSMTType (τ ×ᴮ β)).1
                (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType (τ ×ᴮ β)).2.1)
                ⟨xy, by rwa [ZFSet.is_func_dom_eq
                  (BType.canonicalIsoSMTType (τ ×ᴮ β)).2.1]⟩).2
            let Wxy : SMT.Dom := ⟨_, τ.toSMTType.pair β.toSMTType, hcanon_mem⟩
            have hWxy_mem : Wxy.fst ∈ ⟦τ.toSMTType.pair β.toSMTType⟧ᶻ := hcanon_mem
            have hlamVal' := hden_alt_eq
            rw [SMT.Term.abstract, dif_pos (by rfl)] at hlamVal'
            simp only [SMT.denote] at hlamVal'
            rw [dif_pos (show [z].length > 0 from Nat.zero_lt_succ 0)] at hlamVal'
            split_ifs at hlamVal' with h_isSome h_typ_det
            · let xₙ : Fin 1 → SMT.Dom := fun _ => Wxy
              have hxₙ_spec : ∀ i, (xₙ i).snd.fst = [τ.toSMTType.pair β.toSMTType][↑i] ∧
                  (xₙ i).fst ∈ ⟦[τ.toSMTType.pair β.toSMTType][↑i]⟧ᶻ :=
                fun ⟨i, hi⟩ => by
                  simp only [List.length_cons, List.length_nil, Nat.lt_one_iff] at hi
                  subst hi; exact ⟨rfl, hWxy_mem⟩
              have hgo_xy := funAbstractGoSingle (Δctx := Δ'_alt) (P := body_t) (v := z)
                (τ := τ.toSMTType.pair β.toSMTType) hgo_cov hcov_body_upd xₙ hxₙ_spec
              obtain ⟨body_val, hbody_val⟩ :=
                Option.isSome_iff_exists.mp (show (⟦body_t.abstract _ _⟧ˢ).isSome = true by
                  rw [← hgo_xy]; exact h_isSome hxₙ_spec)
              have h_pair_mem : Wxy.fst.pair body_val.fst ∈ denT_alt.fst := by
                simp only [Option.pure_def, Option.some.injEq] at hlamVal'
                have hlamVal_fst : denT_alt.fst = _ := congrArg (·.fst) hlamVal'.symm
                simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.sub_self,
                  Fin.foldr_zero, List.getElem_cons_zero] at hlamVal_fst
                rw [hlamVal_fst, ZFSet.mem_lambda]
                refine ⟨Wxy.fst, body_val.fst, rfl, hWxy_mem, ?_, ?_⟩
                · have hden_xₙ : ⟦(SMT.Term.abstract.go body_t [z] Δ'_alt hgo_cov).uncurry xₙ⟧ˢ
                      = some body_val := by rw [hgo_xy]; exact hbody_val
                  have hγ := h_typ_det xₙ
                    (fun _ => ⟨(τ.toSMTType.pair β.toSMTType).defaultZFSet,
                             τ.toSMTType.pair β.toSMTType, SMTType.mem_toZFSet_of_defaultZFSet⟩)
                    hxₙ_spec
                    (fun ⟨i, hi⟩ => by
                      simp only [List.length_cons, List.length_nil] at hi
                      have hi' : i = 0 := by omega
                      subst hi'; exact ⟨rfl, SMTType.mem_toZFSet_of_defaultZFSet⟩)
                  rw [congrArg (·.snd.fst) (Option.get_of_eq_some _ hden_xₙ)] at hγ
                  exact hγ ▸ body_val.snd.snd
                · split_ifs with hw'
                  · let xₙ' := fun i : Fin 1 =>
                        (⟨Wxy.fst.get 1 i, [τ.toSMTType.pair β.toSMTType][↑i], hw'.2 i⟩ : SMT.Dom)
                    have hgo' := funAbstractGoSingle (Δctx := Δ'_alt) (P := body_t) (v := z)
                      (τ := τ.toSMTType.pair β.toSMTType)
                      hgo_cov hcov_body_upd xₙ' (fun i => ⟨rfl, hw'.2 i⟩)
                    have hden' : ⟦(SMT.Term.abstract.go body_t [z] Δ'_alt hgo_cov).uncurry xₙ'⟧ˢ
                        = some body_val := by
                      rw [hgo', show xₙ' ⟨0, Nat.zero_lt_one⟩ = Wxy from rfl]; exact hbody_val
                    exact (congrArg (·.fst) (Option.get_of_eq_some _ hden')).symm
                  · exact absurd ⟨trivial, fun ⟨i, hi⟩ => by
                      simp only [Nat.lt_one_iff] at hi; subst hi; exact hWxy_mem⟩ hw'
              have h_fap_body : (ZFSet.fapply denT_alt.fst
                  (ZFSet.is_func_is_pfunc hdenT_alt_func)
                  ⟨Wxy.fst, by rw [ZFSet.is_func_dom_eq hdenT_alt_func]; exact hWxy_mem⟩).1 =
                  body_val.fst :=
                congrArg Subtype.val
                  (ZFSet.fapply.of_pair (ZFSet.is_func_is_pfunc hdenT_alt_func) h_pair_mem)
              have hbody_true : body_val.fst = zftrue := by
                convert hfap_true using 1; exact h_fap_body.symm
              -- AND-decomposition.
              obtain ⟨_, Dapp, hDapp_ty, hDapp_val, hDapp_den⟩ :=
                funDenoteAppAtFst (Δctx := Δ'_alt) (t := D_enc) (x := z)
                  (α := τ.toSMTType) (β := SMTType.bool) (γ := β.toSMTType) (Y := denD_alt)
                  hcov_D_upd_alt hden_D_upd_alt denD_alt_type denD_alt_func Wxy rfl hWxy_mem
              set D_app_t : SMT.Term := (@ˢD_enc) (SMT.Term.var z).fst with D_app_def
              set eq_t : SMT.Term :=
                (SMT.Term.var z).snd =ˢ
                  SMT.substList vs (toDestPair vs (SMT.Term.var z).fst) P_enc with eq_def
              have hcov_D_app : ∀ W : SMT.Dom,
                  SMT.RenamingContext.CoversFV (Function.update Δ'_alt z (some W)) D_app_t :=
                fun W x hx => hcov_body_upd W x (by
                  simp only [body_t_def, D_app_def, SMT.fv, List.mem_append] at hx ⊢
                  exact Or.inl hx)
              have hcov_eq_t : ∀ W : SMT.Dom,
                  SMT.RenamingContext.CoversFV (Function.update Δ'_alt z (some W)) eq_t :=
                fun W x hx => hcov_body_upd W x (by
                  simp only [body_t_def, eq_def, SMT.fv, List.mem_append] at hx ⊢
                  exact Or.inr hx)
              have hDapp_den' : ⟦D_app_t.abstract (Function.update Δ'_alt z (some Wxy))
                                  (hcov_D_app Wxy)⟧ˢ = some Dapp := by
                simp only [D_app_def]; convert hDapp_den using 1
              have hbody_decomp :
                  ⟦body_t.abstract (Function.update Δ'_alt z (some Wxy)) (hcov_body_upd Wxy)⟧ˢ =
                  ⟦(D_app_t.abstract (Function.update Δ'_alt z (some Wxy)) (hcov_D_app Wxy)) ∧ˢ'
                    (eq_t.abstract (Function.update Δ'_alt z (some Wxy)) (hcov_eq_t Wxy))⟧ˢ := by
                simp only [body_t_def, D_app_def, eq_def, SMT.Term.abstract]
              have hDapp_ty_bool : Dapp.snd.fst = SMTType.bool := hDapp_ty
              have hbody_val_decomp :
                  ⟦(D_app_t.abstract (Function.update Δ'_alt z (some Wxy)) (hcov_D_app Wxy)) ∧ˢ'
                    (eq_t.abstract (Function.update Δ'_alt z (some Wxy)) (hcov_eq_t Wxy))⟧ˢ =
                    some body_val := by
                rw [← hbody_decomp]; exact hbody_val
              -- Extract eq_t denotation from the AND.
              obtain ⟨Deq, hDeq_den, hDeq_ty⟩ : ∃ Deq : SMT.Dom,
                  ⟦eq_t.abstract (Function.update Δ'_alt z (some Wxy)) (hcov_eq_t Wxy)⟧ˢ =
                    some Deq ∧ Deq.snd.fst = .bool := by
                obtain ⟨dp, τp, hdp⟩ := Dapp
                simp only [] at hDapp_ty_bool
                subst hDapp_ty_bool
                simp only [SMT.denote, Option.bind_eq_bind, hDapp_den'] at hbody_val_decomp
                match hq : ⟦eq_t.abstract (Function.update Δ'_alt z (some Wxy))
                    (hcov_eq_t Wxy)⟧ˢ with
                | none => simp [hq] at hbody_val_decomp
                | some ⟨Q, .bool, hQ⟩ => exact ⟨⟨Q, .bool, hQ⟩, rfl, rfl⟩
                | some ⟨Q, .int, hQ⟩ => simp [hq] at hbody_val_decomp
                | some ⟨Q, .unit, hQ⟩ => simp [hq] at hbody_val_decomp
                | some ⟨Q, .fun _ _, hQ⟩ => simp [hq] at hbody_val_decomp
                | some ⟨Q, .option _, hQ⟩ => simp [hq] at hbody_val_decomp
                | some ⟨Q, .pair _ _, hQ⟩ => simp [hq] at hbody_val_decomp
              have hDq_den' : ⟦eq_t.abstract (Function.update Δ'_alt z (some Wxy))
                  (hcov_eq_t Wxy)⟧ˢ = some _ := hDeq_den
              obtain ⟨hDapp_true, _⟩ := denote_and_both_zftrue_of_zftrue
                hDapp_den' hDapp_ty_bool hDq_den' hDeq_ty hbody_val_decomp hbody_true
              -- hDapp_true : Dapp.fst = zftrue → xy.π₁ ∈ retract = 𝒟_alt.
              have hπ₁_in_retract : xy.π₁ ∈ retract τ.set denD_alt.fst := by
                rw [retract, ZFSet.mem_sep]
                refine ⟨hx_mem, ?_⟩
                rw [dif_pos hx_mem, dif_pos denD_alt_func]
                have hWxy_π₁_eq :
                    Wxy.fst.π₁ = (ZFSet.fapply (BType.canonicalIsoSMTType τ).1
                      (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType τ).2.1)
                      ⟨a, by rwa [ZFSet.is_func_dom_eq
                        (BType.canonicalIsoSMTType τ).2.1]⟩).1 := by
                  have hζ := (BType.canonicalIsoSMTType τ).2.1
                  have hξ := (BType.canonicalIsoSMTType β).2.1
                  have hfp := ZFSet.fapply_fprod (hf := hζ) (hg := hξ)
                    (a := a) (b := b) ha_mem hb_mem
                  rw [show Wxy.fst = ((ZFSet.fapply (BType.canonicalIsoSMTType τ).1
                          (ZFSet.is_func_is_pfunc hζ)
                          ⟨a, by rwa [ZFSet.is_func_dom_eq hζ]⟩).1).pair
                      ((ZFSet.fapply (BType.canonicalIsoSMTType β).1
                          (ZFSet.is_func_is_pfunc hξ)
                          ⟨b, by rwa [ZFSet.is_func_dom_eq hξ]⟩).1) from by
                    subst hxy_eq; exact hfp, ZFSet.π₁_pair]
                simp only []
                have h := hDapp_val ▸ hDapp_true
                convert h using 4
                simp [hxy_π₁_eq, hWxy_π₁_eq]
              rw [denD_alt_retract] at hπ₁_in_retract
              exact absurd hπ₁_in_retract hxy_𝒟
          · intro hmem_sep
            rw [ZFSet.mem_sep, ZFSet.mem_prod] at hmem_sep
            obtain ⟨⟨a', hπ₁_𝒟, b', _, hxy_eq'⟩, _⟩ := hmem_sep
            have hπ₁_eq : xy.π₁ = a' := by simp [hxy_eq']
            exact absurd (hπ₁_eq ▸ hπ₁_𝒟) hxy_𝒟
    · -- Defaults branch: 𝒟_alt = ∅. T_alt = ∅, retract = ∅.
      -- Extract T_alt = ∅ from rest_alt.
      simp only [Option.bind_eq_some_iff] at rest_alt
      obtain ⟨P_dom, _, hT_eq⟩ := rest_alt
      simp only [Option.pure_def, Option.some.injEq] at hT_eq
      have hT_alt_eq : T_alt = ∅ := by
        have h := hT_eq
        cases h
        rfl
      -- Show retract _ denT_alt.fst = ∅.
      rw [hT_alt_eq]
      -- 𝒟_alt = ∅ and denD_alt_retract gives retract τ.set denD_alt.fst = ∅.
      have h𝒟_alt_empty : 𝒟_alt = ∅ := Classical.byContradiction h_nemp
      have hDretract : retract τ.set denD_alt.fst = ∅ :=
        denD_alt_retract.trans h𝒟_alt_empty
      -- D_enc at canonical of any x ∈ ⟦τ⟧ᶻ is NOT zftrue.
      have hDapp_not_zftrue : ∀ (x : ZFSet.{u}) (hx : x ∈ ⟦τ⟧ᶻ),
          ZFSet.fapply denD_alt.fst (ZFSet.is_func_is_pfunc denD_alt_func)
            ⟨ZFSet.fapply (BType.canonicalIsoSMTType τ).1
                (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType τ).2.1)
                ⟨x, by rwa [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType τ).2.1]⟩,
              by
                rw [ZFSet.is_func_dom_eq denD_alt_func]
                exact ZFSet.fapply_mem_range _ _⟩ ≠ zftrue := by
        intro x hx hEq
        have hcontra : x ∈ retract τ.set denD_alt.1 := by
          rw [retract, ZFSet.mem_sep]
          refine ⟨hx, ?_⟩
          rw [dif_pos hx, dif_pos denD_alt_func]
          simpa using hEq
        rw [hDretract] at hcontra
        exact absurd hcontra (ZFSet.notMem_empty x)
      -- Show retract = ∅ via ZFSet.ext.
      apply ZFSet.ext
      intro xy
      constructor
      · -- Forward: xy ∈ retract → xy ∈ ∅ (contradiction).
        intro hxy
        exfalso
        rw [retract, ZFSet.mem_sep] at hxy
        obtain ⟨hxy_mem, hxy_cond⟩ := hxy
        simp only [dif_pos hxy_mem] at hxy_cond
        have hdenT_func' : ⟦(τ ×ᴮ β).toSMTType⟧ᶻ.IsFunc 𝔹 denT_alt.fst := by
          rw [show ((τ ×ᴮ β).toSMTType : SMTType) =
            τ.toSMTType.pair β.toSMTType from h_toSMT]
          exact hdenT_alt_func
        rw [dif_pos hdenT_func'] at hxy_cond
        exact lambda_defaults_retract_empty_contradiction
          vs_nemp vs_nodup rfl Δ'_alt_covers_lambda hden_alt_eq hden_alt_ty
          hdenT_alt_func denD_alt_type denD_alt_func hcov_D_upd_alt hden_D_upd_alt
          hDapp_not_zftrue hxy_mem hxy_cond
      · -- Backward: xy ∈ ∅ is impossible.
        intro hxy
        exact absurd hxy (ZFSet.notMem_empty xy)


open Classical B in
/--
Defaults-branch totality clause for the lambda case.

Bit-identical signature to `lambda_chosen_totality`. The defaults-branch
call site (where `𝒟 = ∅`) supplies the same set of hypotheses as the
chosen-branch call site, so the defaults helper delegates entirely to
`lambda_chosen_totality`. The proof goes through verbatim because the
totality clause is for *alternative* valuations `Δ_alt`: the alternative
B-side `T_alt` may yield non-empty `𝒟_alt` even though the *original*
`𝒟 = ∅`. Therefore the chosen-branch construction works for both.
-/
private theorem lambda_defaults_totality.{u}
    {vs : List B.𝒱} {τ β : BType} {αs : List BType}
    {E_ctx : B.TypeContext} {D P : B.Term}
    {D_enc P_enc : SMT.Term}
    {z : SMT.𝒱}
    {Δ' : SMT.RenamingContext.Context.{u}}
    {denT' : SMT.Dom.{u}}
    {Γ_D Γ_P Γ' : SMT.TypeContext}
    {used_D used_P used' : List SMT.𝒱}
    (vs_nemp : vs ≠ []) (vs_nodup : vs.Nodup)
    (h_toSMT : (τ ×ᴮ β).toSMTType = τ.toSMTType.pair β.toSMTType)
    (typ_t : E_ctx ⊢ᴮ B.Term.lambda vs D P : (τ ×ᴮ β).set)
    (typ_D : E_ctx ⊢ᴮ D : .set τ)
    (typP : (vs.zipToAList αs ∪ E_ctx) ⊢ᴮ P : β)
    (typ_D_enc : Γ_D ⊢ˢ D_enc : τ.toSMTType.fun SMTType.bool)
    (typ_P_enc : Γ_P ⊢ˢ P_enc : β.toSMTType)
    (τ_hasArity : τ.hasArity vs.length)
    (vs_not_D_fv : ∀ v ∈ vs, v ∉ B.fv D)
    (vs_disj_Γ_D : ∀ v ∈ vs, v ∉ Γ_D)
    (vs_disj_Γ' : ∀ v ∈ vs, v ∉ Γ')
    (vs_used_P : ∀ v ∈ vs, v ∈ used_P)
    (vs_lookup_Γ_P : ∀ (i : Fin vs.length),
      AList.lookup vs[i] Γ_P = some ((τ.toSMTType.fromProdl (vs.length - 1))[i]'(by
        rw [fromProdl_length_of_hasArity τ_hasArity]; exact i.2)))
    (z_not_Γ_P : z ∉ Γ_P)
    (z_not_Γ' : z ∉ Γ')
    (z_not_used_P : z ∉ used_P)
    (z_not_fv_D : z ∉ SMT.fv D_enc)
    (z_not_fv_P : z ∉ SMT.fv P_enc)
    (z_not_vs : z ∉ vs)
    (hcov_lambda : SMT.RenamingContext.CoversFV Δ'
      ((λˢ [z]) [τ.toSMTType.pair β.toSMTType]
        ((@ˢD_enc) (SMT.Term.var z).fst ∧ˢ
          ((SMT.Term.var z).snd =ˢ
            SMT.substList vs (toDestPair vs (SMT.Term.var z).fst) P_enc))))
    (hden_eq :
      ⟦((λˢ [z]) [τ.toSMTType.pair β.toSMTType]
              ((@ˢD_enc) (SMT.Term.var z).fst ∧ˢ
                ((SMT.Term.var z).snd =ˢ
                  SMT.substList vs (toDestPair vs (SMT.Term.var z).fst) P_enc))).abstract
          Δ' hcov_lambda⟧ˢ = some denT')
    (hden_ty : denT'.snd.fst = (τ.toSMTType.pair β.toSMTType).fun SMTType.bool)
    (Δ'_none_out_used' : ∀ v ∉ used', Δ' v = none)
    (Δ'_dom_Γ' : ∀ v, Δ' v ≠ none → v ∈ Γ')
    (Δ'_wt_Γ' : ∀ v (d : SMT.Dom), Δ' v = some d →
      ∀ τ_v, AList.lookup v Γ' = some τ_v → d.snd.fst = τ_v)
    (D_total :
      ∀ (Δ_alt : B.RenamingContext.Context) (Δ_fv_alt : ∀ v ∈ B.fv D, (Δ_alt v).isSome = true)
        (Δ₀_alt : SMT.RenamingContext.Context),
        SMT.RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt D →
          (∀ v ∉ used_D, Δ₀_alt v = none) →
            (∀ (v : SMT.𝒱) (d : SMT.Dom),
                Δ₀_alt v = some d → ∀ (τ : SMTType), AList.lookup v Γ_D = some τ → d.snd.fst = τ) →
              ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦τ.set⟧ᶻ),
                ⟦D.abstract Δ_alt Δ_fv_alt⟧ᴮ = some ⟨T_alt, ⟨τ.set, hT_alt⟩⟩ →
                  ∃ Δ'_alt,
                    ∃ (h : SMT.RenamingContext.CoversFV Δ'_alt D_enc),
                      ∃ denT_alt,
                        SMT.RenamingContext.Extends Δ'_alt Δ₀_alt ∧
                          (∀ v ∉ used_D, Δ'_alt v = none) ∧
                            (∀ (v : SMT.𝒱) (d : SMT.Dom),
                                Δ'_alt v = some d → ∀ (τ : SMTType),
                                  AList.lookup v Γ_D = some τ → d.snd.fst = τ) ∧
                              ⟦D_enc.abstract Δ'_alt h⟧ˢ = some denT_alt ∧
                                ⟨T_alt, ⟨τ.set, hT_alt⟩⟩ ≘ᶻ denT_alt ∧
                                  ∀ (v : SMT.𝒱), Δ'_alt v ≠ none → v ∈ Γ_D)
    (P_enc_total :
      ∀ (Δ_alt : B.RenamingContext.Context) (Δ_fv_alt : ∀ v ∈ B.fv P, (Δ_alt v).isSome = true)
        (Δ₀_alt : SMT.RenamingContext.Context),
        SMT.RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt P →
          (∀ v ∉ used_P, Δ₀_alt v = none) →
            (∀ (v : SMT.𝒱) (d : SMT.Dom),
                Δ₀_alt v = some d → ∀ (τ : SMTType), AList.lookup v Γ_P = some τ → d.snd.fst = τ) →
              ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦β⟧ᶻ),
                ⟦P.abstract Δ_alt Δ_fv_alt⟧ᴮ = some ⟨T_alt, ⟨β, hT_alt⟩⟩ →
                  ∃ Δ'_alt,
                    ∃ (hcov_alt : SMT.RenamingContext.CoversFV Δ'_alt P_enc),
                      ∃ denT_alt,
                        SMT.RenamingContext.Extends Δ'_alt Δ₀_alt ∧
                          (∀ v ∉ used_P, Δ'_alt v = none) ∧
                            (∀ (v : SMT.𝒱) (d : SMT.Dom),
                                Δ'_alt v = some d → ∀ (τ : SMTType),
                                  AList.lookup v Γ_P = some τ → d.snd.fst = τ) ∧
                              ⟦P_enc.abstract Δ'_alt hcov_alt⟧ˢ = some denT_alt ∧
                                ⟨T_alt, ⟨β, hT_alt⟩⟩ ≘ᶻ denT_alt ∧
                                  ∀ (v : SMT.𝒱), Δ'_alt v ≠ none → v ∈ Γ_P)
    (Γ_D_lookup_sub_Γ' : ∀ v τ_v, AList.lookup v Γ_D = some τ_v → AList.lookup v Γ' = some τ_v)
    (Γ_D_lookup_sub_Γ_P : ∀ v τ_v, AList.lookup v Γ_D = some τ_v → AList.lookup v Γ_P = some τ_v)
    (Γ'_lookup_sub_Γ_P : ∀ v τ_v, AList.lookup v Γ' = some τ_v → AList.lookup v Γ_P = some τ_v)
    (used_D_sub_used' : used_D ⊆ used')
    (Γ_P_lookup_sub_Γ'_P : ∀ v ∉ vs, ∀ τ_v,
      AList.lookup v Γ_P = some τ_v → AList.lookup v Γ' = some τ_v)
    (used_P_sub_used' : used_P ⊆ used')
    (covers_D : CoversUsedVars used_D D)
    (covers_P : CoversUsedVars used_P P)
    (Γ_D_dom_sub_Γ' : ∀ v, v ∈ Γ_D → v ∈ Γ')
    (Γ_P_dom_sub_Γ' : ∀ v, v ∈ Γ_P → v ∉ vs → v ∈ Γ')
    (fv_lambda_sub : ∀ v ∈ B.fv (B.Term.lambda vs D P), v ∈ Γ')
    (used_D_sub_used_P : used_D ⊆ used_P) :
    ∀ (Δ_alt : B.RenamingContext.Context)
      (Δ_fv_alt : ∀ v ∈ B.fv (B.Term.lambda vs D P), (Δ_alt v).isSome = true)
      (Δ₀_alt : SMT.RenamingContext.Context),
      SMT.RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt (B.Term.lambda vs D P) →
        (∀ v ∉ used', Δ₀_alt v = none) →
          (∀ (v : SMT.𝒱) (d : SMT.Dom),
              Δ₀_alt v = some d → ∀ (τ_v : SMTType), AList.lookup v Γ' = some τ_v → d.snd.fst = τ_v) →
            ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦(τ ×ᴮ β).set⟧ᶻ),
              ⟦(B.Term.lambda vs D P).abstract Δ_alt Δ_fv_alt⟧ᴮ =
                  some ⟨T_alt, ⟨(τ ×ᴮ β).set, hT_alt⟩⟩ →
                ∃ Δ'_alt,
                  ∃ (hcov_alt : SMT.RenamingContext.CoversFV Δ'_alt
                    ((λˢ [z]) [τ.toSMTType.pair β.toSMTType]
                      ((@ˢD_enc) (SMT.Term.var z).fst ∧ˢ
                        ((SMT.Term.var z).snd =ˢ
                          SMT.substList vs (toDestPair vs (SMT.Term.var z).fst) P_enc)))),
                    ∃ denT_alt,
                      SMT.RenamingContext.Extends Δ'_alt Δ₀_alt ∧
                        (∀ v ∉ used', Δ'_alt v = none) ∧
                          (∀ (v : SMT.𝒱) (d : SMT.Dom),
                              Δ'_alt v = some d → ∀ (τ_v : SMTType),
                                AList.lookup v Γ' = some τ_v → d.snd.fst = τ_v) ∧
                            ⟦((λˢ [z]) [τ.toSMTType.pair β.toSMTType]
                                        ((@ˢD_enc) (SMT.Term.var z).fst ∧ˢ
                                          ((SMT.Term.var z).snd =ˢ
                                            SMT.substList vs (toDestPair vs (SMT.Term.var z).fst) P_enc))).abstract
                                    Δ'_alt hcov_alt⟧ˢ = some denT_alt ∧
                              (⟨T_alt, ⟨(τ ×ᴮ β).set, hT_alt⟩⟩ : B.Dom) ≘ᶻ denT_alt ∧
                                ∀ (v : SMT.𝒱), Δ'_alt v ≠ none → v ∈ Γ' :=
  lambda_chosen_totality (vs := vs) (τ := τ) (β := β) (αs := αs) (E_ctx := E_ctx)
    (D := D) (P := P)
    (D_enc := D_enc) (P_enc := P_enc) (z := z) (Δ' := Δ') (denT' := denT')
    (Γ_D := Γ_D) (Γ_P := Γ_P) (Γ' := Γ') (used_D := used_D) (used_P := used_P)
    (used' := used') vs_nemp vs_nodup h_toSMT typ_t typ_D typP typ_D_enc typ_P_enc
    τ_hasArity vs_not_D_fv vs_disj_Γ_D vs_disj_Γ' vs_used_P vs_lookup_Γ_P z_not_Γ_P
    z_not_Γ' z_not_used_P z_not_fv_D z_not_fv_P z_not_vs hcov_lambda hden_eq hden_ty
    Δ'_none_out_used' Δ'_dom_Γ' Δ'_wt_Γ' D_total P_enc_total Γ_D_lookup_sub_Γ'
    Γ_D_lookup_sub_Γ_P Γ'_lookup_sub_Γ_P
    used_D_sub_used' Γ_P_lookup_sub_Γ'_P used_P_sub_used' covers_D covers_P
    Γ_D_dom_sub_Γ' Γ_P_dom_sub_Γ' fv_lambda_sub used_D_sub_used_P

set_option maxHeartbeats 4000000 in
theorem encodeTerm_spec.lambda_case.{u} (fv_sub_typings : B.FvSubTypings)
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
  (E : B.Env) {Λ : SMT.TypeContext} {α : BType} (typ_t : E.context ⊢ᴮ Term.lambda vs D P : α)
  {«Δ» : B.RenamingContext.Context} (Δ_fv : ∀ v ∈ B.fv (Term.lambda vs D P), («Δ» v).isSome = true)
  {Δ₀ : SMT.RenamingContext.Context} (Δ₀_ext : RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» (Term.lambda vs D P))
  {used : List SMT.𝒱} (Δ₀_none_out : ∀ v ∉ used, Δ₀ v = none)
  {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ}
  (den_t : ⟦(Term.lambda vs D P).abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩)
  (vars_used : ∀ v ∈ (Term.lambda vs D P).vars, v ∈ used)
  (Λ_inv : ∀ v ∈ (Term.lambda vs D P).vars, v ∈ Λ → v ∈ E.context) {n : ℕ} :
  ⦃fun x =>
    match x with
    | { env := E0, types := Λ' } => ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
    encodeTerm (Term.lambda vs D P) E ⦃PostCond.mayThrow fun x x_1 =>
      match x with
      | (t', σ) =>
        match x_1 with
        | { env := E', types := Γ' } =>
          ⌜used ⊆ E'.usedVars ∧
              Λ ⊆ Γ' ∧
                AList.keys Γ' ⊆ E'.usedVars ∧
                  CoversUsedVars E'.usedVars (Term.lambda vs D P) ∧
                    σ = α.toSMTType ∧
                      Γ' ⊢ˢ t' : σ ∧
                        (∀ v ∈ used, v ∉ Λ → v ∉ B.fv (Term.lambda vs D P) → v ∉ Γ') ∧
                          ∃ Δ',
                            ∃ (Δ'_covers : RenamingContext.CoversFV Δ' t'),
                              RenamingContext.Extends Δ' Δ₀ ∧
                                RenamingContext.ExtendsOnSourceFV Δ' «Δ» (Term.lambda vs D P) ∧
                                  (∀ v ∉ E'.usedVars, Δ' v = none) ∧
                                    ∃ denT',
                                      ⟦t'.abstract Δ' Δ'_covers⟧ˢ = some denT' ∧
                                        ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT' ∧
                                          ∀ (Δ_alt : B.RenamingContext.Context)
                                            (Δ_fv_alt : ∀ v ∈ B.fv (Term.lambda vs D P), (Δ_alt v).isSome = true)
                                            (Δ₀_alt : SMT.RenamingContext.Context),
                                            RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt (Term.lambda vs D P) →
                                              (∀ v ∉ E'.usedVars, Δ₀_alt v = none) →
                                              (∀ v (d : SMT.Dom), Δ₀_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) →
                                                ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦α⟧ᶻ),
                                                  ⟦(Term.lambda vs D P).abstract Δ_alt Δ_fv_alt⟧ᴮ =
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
  -- Initial setup: destructure typing, introduce auxiliary hypotheses.
  mintro pre ∀St₀
  mpure pre
  obtain ⟨rfl, rfl, St₀_sub, St₀_used_eq⟩ := pre
  obtain ⟨β, αs, Ds, vs_nemp, vs_αs_len, vs_Ds_len, α_eq, vs_nodup, D_eq, typDs, typP, vs_Γ_disj⟩ :=
    Typing.lambdaE typ_t
  subst α_eq
  have Δ_fv_D : ∀ v ∈ B.fv D, («Δ» v).isSome := fun v hv =>
    Δ_fv v (fv.mem_lambda (.inl hv))
  have Δ₀_ext_D : RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» D :=
    RenamingContext.extendsOnSourceFV_of_fv_subset
      (hsub := fun v hv => fv.mem_lambda (.inl hv)) Δ₀_ext
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
  -- Extract `den_D` (the denotation of D) from `den_t`.
  -- The lambda denotation (B/SemanticsPHOAS.lean:546) unfolds as:
  --   `⟦D⟧ᴮ = some ⟨𝒟, .set τ, h𝒟⟩` (from the first bind)
  -- plus nested conditionals enforcing arity, totality, type consistency of E,
  -- domain non-emptiness, and a witness check.
  have den_t_saved := den_t
  have denote_lambda_inv := den_t
  simp only [B.Term.abstract] at denote_lambda_inv
  unfold B.denote at denote_lambda_inv
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at denote_lambda_inv
  -- Examine: denote_lambda_inv now has the nested dite/match form.
  -- Step 1: extract the D denotation, which is the outer `do let ⟨𝒟, .set τ, h𝒟⟩ ← ⟦D⟧ᴮ | failure`.
  obtain ⟨⟨𝒟', τ_D', h𝒟'⟩, den_D', rest_lambda⟩ := denote_lambda_inv
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
  -- Rewrite encoder, invoke D_ih.
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
  -- Derive Δ_D_wt and Δ_D_dom via axioms (for later use)
  have Δ_D_wt : ∀ v (d : SMT.Dom), Δ_D v = some d →
      ∀ τ_v, St₁.types.lookup v = some τ_v → d.snd.fst = τ_v :=
    SMT.RenamingContext.ExtendsOnSourceFV.wt Δ_D_src_ext typ_D_enc
  have Δ_D_dom : ∀ v, Δ_D v ≠ none → v ∈ St₁.types := fun v hv =>
    fv_sub_typings typ_D typ_D_enc v
      (SMT.RenamingContext.ExtendsOnSourceFV.dom_sub_B_fv Δ_D_src_ext v hv)
  simp only [BType.toSMTType] at *
  -- Add vs to context (now with τs derived from D's SMT type τ.toSMTType).
  mspec addToContext_forIn_spec
      (pairs := vs.zip (τ.toSMTType.fromProdl (vs.length - 1)))
  mrename_i pre
  mintro ∀St₂
  mpure pre
  obtain ⟨St₂_types, St₂_fvc, St₂_used⟩ := pre
  -- Set up E', Δ_ext, Δ_D_ext for P encoding.
  set E' : B.Env := { E with context := vs.zipToAList αs ∪ E.context } with E'_def
  conv in encodeTerm P E => rw [encodeTerm_env_irrel P E E' rfl]
  have St₁_sub_St₂_used : St₁.env.usedVars ⊆ St₂.env.usedVars := by
    rw [St₂_used]; intro v hv
    have : ∀ (l : List (SMT.𝒱 × SMTType)) (acc : List SMT.𝒱),
        v ∈ acc → v ∈ l.foldl (fun used p => p.1 :: used) acc := by
      intro l
      induction l with
      | nil => intro acc hmem; exact hmem
      | cons p ps ih => intro acc hmem; exact ih _ (List.mem_cons_of_mem _ hmem)
    exact this _ _ hv
  have Δ_D_none_St₂ : ∀ v ∉ St₂.env.usedVars, Δ_D v = none :=
    fun v hv => Δ_D_none v (fun hmem => hv (St₁_sub_St₂_used hmem))
  have St₂_keys_sub : AList.keys St₂.types ⊆ St₂.env.usedVars := by
    rw [St₂_types, St₂_used]
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
  -- Derive τ.hasArity vs.length
  have αs_nemp : αs ≠ [] := by simpa [vs_αs_len, ← List.length_pos_iff] using vs_nemp
  have τ_hasArity : τ.hasArity vs.length := by
    rw [τ_def, List.reduce]
    have h_len : αs.tail.length + 1 = vs.length := by
      rw [List.length_tail, vs_αs_len]
      have := List.length_pos_of_ne_nil αs_nemp
      omega
    convert BType.hasArity_of_foldl (α := αs.head αs_nemp) (αs := αs.tail) using 1
    exact h_len.symm
  -- Navigate nested dites in rest_lambda via split_ifs.
  -- Lambda's denote (B/SemanticsPHOAS.lean:546+) has the structure:
  --   `if hτ then if den_E then if typE_det then if 𝒟_nemp then ... else (defaults) else ...`
  -- After `split_ifs` on the 5 dite layers, only 2 valid branches remain:
  -- (1) chosen branch (𝒟 ≠ ∅, uses Classical.choose), (2) defaults branch (𝒟 = ∅).
  -- The contradictory cases (failure = some ...) are closed automatically.
  rw [dif_pos τ_hasArity] at rest_lambda
  split_ifs at rest_lambda with h_den_E h_typE_det h_nemp h_chosen_arity h_default_arity
  · -- Chosen branch: 𝒟' ≠ ∅, valuation uses Classical.choose witness.
    -- Define f/Δ_ext using the Classical.choose witness.
    let x_choose := Classical.choose (ZFSet.nonempty_exists_iff.mp h_nemp)
    have x_choose_mem : x_choose ∈ 𝒟' :=
      Classical.choose_spec (ZFSet.nonempty_exists_iff.mp h_nemp)
    let f : Fin vs.length → B.Dom := fun i =>
      ⟨x_choose.get vs.length i, τ.get vs.length i,
       get_mem_type_of_isTuple h_chosen_arity.1 τ_hasArity h_chosen_arity.2⟩
    set Δ_ext : B.RenamingContext.Context :=
      Function.updates «Δ» vs (List.ofFn fun i => some (f i)) with Δ_ext_def
    have Δ_fv_P : ∀ v ∈ B.fv P, (Δ_ext v).isSome := by
      intro v hv
      rw [Δ_ext_def, Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup]
      split_ifs with hvs
      · simp only [List.getElem_ofFn, Option.isSome_some]
      · exact Δ_fv v (fv.mem_lambda (.inr ⟨hv, hvs⟩))
    set Δ_D_ext : SMT.RenamingContext.Context :=
      Function.updates Δ_D vs
        (List.ofFn fun (i : Fin vs.length) => B.RenamingContext.toSMT Δ_ext vs[i])
      with Δ_D_ext_def
    have Δ_D_ext_none_St₂ : ∀ v ∉ St₂.env.usedVars, Δ_D_ext v = none :=
      Δ_D_ext_none_helper_shared (ΔDD := Δ_D) (ΔDDext := Δ_D_ext)
        (vs := vs) (vs_nodup := vs_nodup)
        (vs_τs_len := by rw [fromProdl_length_of_hasArity τ_hasArity])
        (used0 := St₁.env.usedVars) (used1 := St₁.env.usedVars)
        (used2 := St₂.env.usedVars)
        (St_used_def := St₂_used) (used1_eq_used0 := rfl)
        (ΔDDext_def := Δ_D_ext_def) (ΔDD_none_outside := Δ_D_none_St₂)
    have Δ₀_ext_P : RenamingContext.ExtendsOnSourceFV Δ_D_ext Δ_ext P :=
      Δ₀_ext_P_helper_shared vs_nodup Δ_ext_def Δ_D_ext_def (Term.lambda vs D P) P
        (mem_binder := fun hv hvs => fv.mem_lambda (.inr ⟨hv, hvs⟩))
        (lift := fun hv => Δ_D_extends (Δ₀_ext hv))
    -- Now extract den_P from rest_lambda using denote_term_abstract_go_eq_term_abstract.
    rw [denote_term_abstract_go_eq_term_abstract vs_nodup vs_nemp f Δ_fv_P,
        Option.bind_eq_some_iff] at rest_lambda
    obtain ⟨⟨P_val, P_typ, P_mem_typ⟩, den_P, P_eq⟩ := rest_lambda
    -- In the chosen branch, P_eq has form:
    --   pure ⟨ZFSet.sep ... (𝒟'.prod ⟦P_typ⟧ᶻ), ⟨(τ ×ᴮ P_typ).set, _⟩⟩ = some ⟨T, ⟨(τ ×ᴮ β).set, hT⟩⟩
    -- So P_typ = β and T = ZFSet.sep ... (𝒟'.prod ⟦β⟧ᶻ).
    simp only [Option.pure_def, Option.some.injEq] at P_eq
    obtain ⟨_, _⟩ := P_eq
    -- Step: Prepare to invoke P_ih (same as defaults branch)
    have vars_used_P_St₂ : ∀ v ∈ P.vars, v ∈ St₂.env.usedVars :=
      fun v hv => St₁_sub_St₂_used (used_sub_St₁ (vars_used_P v hv))
    have St₂_types_sub_E_ctx_on_P_vars : ∀ v ∈ P.vars, v ∈ St₂.types → v ∈ E'.context := by
      intro v v_in_P_vars v_in_St₂_types
      simp [E']
      by_cases v_in_vs : v ∈ vs
      · left
        exact AList.mem_zipToAList_of_mem vs_nodup vs_αs_len v_in_vs
      · right
        have v_in_St₁ : v ∈ St₁.types := by
          rw [St₂_types] at v_in_St₂_types
          exact AList.mem_of_mem_foldl_insert' v_in_St₂_types (by
            intro h
            rw [List.mem_map] at h
            obtain ⟨⟨a, b⟩, hab, rfl⟩ := h
            exact v_in_vs (List.of_mem_zip hab).1)
        have v_used : v ∈ used := vars_used_P v v_in_P_vars
        by_cases v_St₀ : v ∈ St₀.types
        · have v_lambda : v ∈ (Term.lambda vs D P).vars := by
            unfold B.Term.vars at v_in_P_vars ⊢
            rw [List.mem_union_iff]
            rcases List.mem_union_iff.mp v_in_P_vars with h_fv | h_bv
            · left; simp only [B.fv, List.mem_append]
              right
              unfold List.removeAll; rw [List.mem_filter]
              exact ⟨h_fv, by simp [v_in_vs]⟩
            · right; simp only [B.bv, List.mem_append]
              right; exact h_bv
          exact Λ_inv v v_lambda v_St₀
        · have v_fv_D : v ∈ B.fv D := by
            by_contra h
            exact absurd v_in_St₁ (D_preserves_types v v_used v_St₀ h)
          exact AList.lookup_isSome.mp (B.Typing.mem_context_of_mem_fv typ_D v_fv_D)
    -- Apply P_ih (same as defaults branch)
    mspec P_ih (E := E') (Λ := St₂.types) (α := β) typP
      («Δ» := Δ_ext) Δ_fv_P
      (Δ₀ := Δ_D_ext) Δ₀_ext_P (used := St₂.env.usedVars) Δ_D_ext_none_St₂
      (T := P_val) (hT := P_mem_typ) den_P vars_used_P_St₂ (n := St₂.env.freshvarsc)
      St₂_types_sub_E_ctx_on_P_vars
    clear P_ih
    rename_i out_P
    obtain ⟨P_enc, σP⟩ := out_P
    mrename_i pre
    mintro ∀St₃
    mpure pre
    obtain ⟨St₂_sub_St₃, St₂_sub_St₃_types, St₃_keys_sub, covers_P, rfl, typ_P_enc,
      P_preserves_types,
      Δ_P, Δ_P_covers, Δ_P_extends, Δ_P_src_ext, Δ_P_none, denP', den_P_enc, P_RDom,
      P_enc_total⟩ := pre
    have Δ_P_wt : ∀ v (d : SMT.Dom), Δ_P v = some d →
        ∀ τ_v, St₃.types.lookup v = some τ_v → d.snd.fst = τ_v :=
      SMT.RenamingContext.ExtendsOnSourceFV.wt Δ_P_src_ext typ_P_enc
    have Δ_P_dom : ∀ v, Δ_P v ≠ none → v ∈ St₃.types := fun v hv =>
      fv_sub_typings typP typ_P_enc v
        (SMT.RenamingContext.ExtendsOnSourceFV.dom_sub_B_fv Δ_P_src_ext v hv)
    mspec freshVar_spec
    rename_i z
    mrename_i pre
    mintro ∀St₄
    mpure pre
    obtain ⟨St₄_types, z_fresh, St₄_fvc, St₄_used, z_not_used⟩ := pre
    mspec SMT.eraseVars_forIn_spec (vars := vs)
    mrename_i pre_erase_vs
    mintro ∀St₅
    mpure pre_erase_vs
    obtain ⟨St₅_types, St₅_fvc, St₅_used⟩ := pre_erase_vs
    mspec SMT.eraseFromContext_spec
    mrename_i pre_erase_z
    mintro ∀St₆
    mpure pre_erase_z
    obtain ⟨St₆_types, St₆_fvc, St₆_used⟩ := pre_erase_z
    mspec Std.Do.Spec.pure
    mpure_intro
    have St₆_used_chain : St₆.env.usedVars = z :: St₃.env.usedVars := by
      rw [St₆_used, St₅_used, St₄_used]
    have z_not_St₀ : z ∉ St₀.types := by
      intro hz
      have := St₀_sub hz
      rw [St₀_used_eq] at this
      exact z_not_used (St₂_sub_St₃ (St₁_sub_St₂_used (used_sub_St₁ this)))
    have vs_not_D_fv : ∀ v ∈ vs, v ∉ B.fv D := by
      intro v hv hv_fv
      nomatch vs_Γ_disj v hv <| AList.lookup_isSome.mp <|
        B.Typing.mem_context_of_mem_fv typ_D hv_fv
    have vs_disj_St₁ : ∀ v ∈ vs, v ∉ St₁.types := by
      intro v hv
      apply D_preserves_types v (vars_used_vs v hv) _ (vs_not_D_fv v hv)
      intro hv_St₀
      have hv_lambda : v ∈ (Term.lambda vs D P).vars := by
        unfold B.Term.vars; rw [List.mem_union_iff]; right
        simp only [B.bv, List.mem_append]; left; left; exact hv
      exact vs_Γ_disj v hv (Λ_inv v hv_lambda hv_St₀)
    have St₁_sub_St₃_types : St₁.types ⊆ St₃.types := by
      apply AList.subset_trans _ St₂_sub_St₃_types
      rw [St₂_types]
      apply AList.subset_foldl_insert'
      · intro ⟨v, ξ⟩ hv
        exact vs_disj_St₁ v (List.mem_fst_of_mem_zip hv)
      · exact List.nodup_map_fst_of_nodup_zip vs_nodup
    have St₆_sub_St₃ : St₆.types ⊆ St₃.types := by
      rw [St₆_types, St₅_types, St₄_types]
      intro ⟨k, v⟩ hkv
      have hk_ne_z : k ≠ z := AList.fst_ne_of_mem_erase_entries hkv
      have hkv_foldl := AList.erase_entries_subset z _ hkv
      have hkv_ins := AList.foldl_erase_entries_subset vs _ hkv_foldl
      rw [AList.entries_insert_of_notMem z_fresh] at hkv_ins
      exact (List.mem_cons.mp hkv_ins).elim
        (fun h => absurd (congrArg Sigma.fst h) hk_ne_z) id
    -- Typing proof (same construction as defaults branch).
    have h_typ_St₆ : St₆.types ⊢ˢ
        (SMT.Term.lambda [z] [τ.toSMTType.pair β.toSMTType]
          (SMT.Term.and
            (SMT.Term.app D_enc (SMT.Term.fst (.var z)))
            (SMT.Term.eq (SMT.Term.snd (.var z))
              (SMT.substList vs (toDestPair vs (SMT.Term.fst (.var z))) P_enc)))) :
        SMTType.fun (τ.toSMTType.pair β.toSMTType) .bool := by
      have hupdate : SMT.TypeContext.update St₃.types [z] [τ.toSMTType.pair β.toSMTType] rfl =
          St₃.types.insert z (τ.toSMTType.pair β.toSMTType) := by
        simp only [SMT.TypeContext.update, List.length_cons, List.length_nil, zero_add,
          Nat.reduceAdd, Fin.cast_eq_self, Fin.getElem_fin, Fin.val_eq_zero,
          List.getElem_cons_zero, Fin.foldl_succ, Fin.foldl_zero]
      have h_St₁_sub_St₃ := St₁_sub_St₃_types
      suffices h_typ_St₃ : St₃.types ⊢ˢ
          (SMT.Term.lambda [z] [τ.toSMTType.pair β.toSMTType]
            (SMT.Term.and
              (SMT.Term.app D_enc (SMT.Term.fst (.var z)))
              (SMT.Term.eq (SMT.Term.snd (.var z))
                (SMT.substList vs (toDestPair vs (SMT.Term.fst (.var z))) P_enc)))) :
          SMTType.fun (τ.toSMTType.pair β.toSMTType) .bool from
        Typing.strengthening_of_fv_subset St₆_sub_St₃ h_typ_St₃ (by
          have h_surv : ∀ v, v ∈ St₃.types → v ∉ vs → v ≠ z → v ∈ St₆.types := by
            intro v hv_St₃ hv_not_vs hv_ne_z
            rw [St₆_types, St₅_types, St₄_types]
            obtain ⟨τ_v, hτ_v⟩ := Option.isSome_iff_exists.mp (AList.lookup_isSome.2 hv_St₃)
            have hentry := AList.mem_lookup_iff.1 hτ_v
            have h_ins : ⟨v, τ_v⟩ ∈ (AList.insert z (τ.toSMTType.pair β.toSMTType)
                St₃.types).entries := by
              rw [AList.entries_insert_of_notMem z_fresh]
              exact List.mem_cons_of_mem _ hentry
            exact AList.mem_keys.mpr (List.mem_map.mpr ⟨⟨v, τ_v⟩,
              List.mem_kerase_of_ne_key hv_ne_z
                (AList.mem_foldl_erase_of_not_mem_keys h_ins hv_not_vs), rfl⟩)
          intro v hv_lam
          simp only [SMT.fv] at hv_lam
          unfold List.removeAll at hv_lam
          rw [List.mem_filter] at hv_lam
          obtain ⟨hv_body, hv_nz⟩ := hv_lam
          have hv_ne_z : v ≠ z := by simpa using hv_nz
          simp only [List.mem_append] at hv_body
          rcases hv_body with (hv_D | hv_z1) | (hv_z2 | hv_subst)
          · have hv_St₁ : v ∈ St₁.types :=
              Typing.mem_context_of_mem_fv typ_D_enc hv_D
            exact h_surv v (typeContext_mem_of_subset h_St₁_sub_St₃ hv_St₁)
              (fun hvs => vs_disj_St₁ v hvs hv_St₁) hv_ne_z
          · rw [List.mem_singleton] at hv_z1
            exact absurd hv_z1 hv_ne_z
          · rw [List.mem_singleton] at hv_z2
            exact absurd hv_z2 hv_ne_z
          · rcases SMT_mem_fv_substList hv_subst with hv_P | ⟨t, ht, hv_t⟩
            · have hv_St₃ := Typing.mem_context_of_mem_fv typ_P_enc hv_P
              have hv_not_vs : v ∉ vs := by
                intro hvs
                suffices hlen : vs.length ≤ (toDestPair vs (SMT.Term.fst (.var z))).length by
                  have hts : ∀ t ∈ toDestPair vs (SMT.Term.fst (.var z)), v ∉ SMT.fv t := by
                    intro t ht hv_t
                    have := SMT_fv_toDestPair_subset_base (v := v) (z := z)
                      (t₀ := SMT.Term.fst (.var z))
                      (by intro w hw; simp only [SMT.fv, List.mem_singleton] at hw; exact hw)
                      ht hv_t
                    exact hv_ne_z this
                  exact absurd hv_subst (SMT_not_mem_fv_substList_of_mem_vars hlen hvs hts)
                suffices ∀ (ws : List SMT.𝒱) (zp : SMT.Term) (acc : List SMT.Term)
                    (d : SMT.Term),
                    ws.length + acc.length ≤ (toDestPair ws zp acc d).length by
                  simpa using this vs (SMT.Term.fst (.var z)) [] (SMT.Term.fst (.var z))
                intro ws
                induction ws with
                | nil => intro _ acc _; simp [toDestPair]
                | cons w ws' ih =>
                  intro zp acc d
                  cases ws' with
                  | nil => simp [toDestPair]; omega
                  | cons w' ws'' =>
                    simp only [toDestPair]
                    have := ih (.fst d) (.snd d :: acc) (.fst d)
                    simp [List.length] at this ⊢; omega
              exact h_surv v hv_St₃ hv_not_vs hv_ne_z
            · have := SMT_fv_toDestPair_subset_base (v := v) (z := z)
                (t₀ := SMT.Term.fst (.var z))
                (by intro w hw; simp only [SMT.fv, List.mem_singleton] at hw; exact hw)
                ht hv_t
              exact absurd this hv_ne_z)
      refine SMT.Typing.lambda St₃.types [z] [τ.toSMTType.pair β.toSMTType] _ .bool ?_ ?_ ?_ ?_ ?_
      · intro v hv; rw [List.mem_singleton] at hv; subst hv; exact z_fresh
      · intro v hv; simp only [List.mem_singleton] at hv; subst hv
        simp only [SMT.bv, List.append_nil, List.nil_append, List.mem_append, not_or]
        refine ⟨?_, ?_⟩
        · intro hbv
          have typ_D_enc_St₃ := SMT.Typing.weakening
            (SMT.TypeContext.entries_subset_insert_of_notMem
              (τ := τ.toSMTType.pair β.toSMTType) z_fresh)
            (SMT.Typing.weakening h_St₁_sub_St₃ typ_D_enc)
          exact SMT.Typing.bv_notMem_context typ_D_enc_St₃ _ hbv
            ((AList.mem_insert _).mpr (Or.inl rfl))
        · intro hbv
          have hbv_P := SMT_bv_substList_subset
            (fun t ht => toDestPair_bv_nil_base (by simp [SMT.bv]) t ht) _ hbv
          have typ_P_enc_ins := SMT.Typing.weakening
            (SMT.TypeContext.entries_subset_insert_of_notMem
              (τ := τ.toSMTType.pair β.toSMTType) z_fresh) typ_P_enc
          exact SMT.Typing.bv_notMem_context typ_P_enc_ins _ hbv_P
            ((AList.mem_insert _).mpr (Or.inl rfl))
      · exact Nat.zero_lt_succ 0
      · rfl
      · rw [hupdate]
        have h_ins := SMT.TypeContext.entries_subset_insert_of_notMem
          (v := z) (τ := τ.toSMTType.pair β.toSMTType) z_fresh
        refine SMT.Typing.and _ _ _ ?_ ?_
        · exact SMT.Typing.app _ _ _ _ _
            (SMT.Typing.weakening h_ins
              (SMT.Typing.weakening h_St₁_sub_St₃ typ_D_enc))
            (SMT.Typing.fst _ _ _ _
              (SMT.Typing.var _ z (τ.toSMTType.pair β.toSMTType)
                (AList.lookup_insert St₃.types)))
        · refine SMT.Typing.eq _ _ _ β.toSMTType ?_ ?_
          · exact SMT.Typing.snd _ _ _ _
              (SMT.Typing.var _ z (τ.toSMTType.pair β.toSMTType)
                (AList.lookup_insert St₃.types))
          · apply SMT_Typing_substList
            · exact SMT.Typing.weakening h_ins typ_P_enc
            · exact toDestPair_bv_nil_base (by simp [SMT.bv])
            · set Γ_z := St₃.types.insert z (τ.toSMTType.pair β.toSMTType) with Γ_z_def
              set τs := τ.toSMTType.fromProdl (vs.length - 1) with τs_def
              have τs_len : τs.length = vs.length := fromProdl_length_of_hasArity τ_hasArity
              intro i hi_x hi_t hx
              have hi_τs : i < τs.length := τs_len ▸ hi_x
              have h_St₂_lookup : St₂.types.lookup vs[i] = some τs[i] := by
                rw [St₂_types]; exact foldl_insert_lookup_zip vs_nodup hi_x hi_τs
              have h_St₃_lookup : St₃.types.lookup vs[i] = some τs[i] :=
                AList.mem_lookup_iff.2
                  (St₂_sub_St₃_types (AList.mem_lookup_iff.1 h_St₂_lookup))
              have hne : vs[i] ≠ z := by
                intro heq
                have hvi_used : vs[i] ∈ St₃.env.usedVars :=
                  St₂_sub_St₃
                    (St₁_sub_St₂_used
                      (used_sub_St₁ (vars_used_vs vs[i] (List.getElem_mem hi_x))))
                exact z_not_used (heq ▸ hvi_used)
              have h_lookup : Γ_z.lookup vs[i] = some τs[i] := by
                rw [Γ_z_def, AList.lookup_insert_ne hne]; exact h_St₃_lookup
              have h_get : (Γ_z.lookup vs[i]).get hx = τs[i] := by simp [h_lookup]
              rw [h_get]
              have hz_lookup : Γ_z.lookup z = some (τ.toSMTType.pair β.toSMTType) :=
                AList.lookup_insert St₃.types
              have h_z_var : Γ_z ⊢ˢ SMT.Term.var z : τ.toSMTType.pair β.toSMTType :=
                SMT.Typing.var Γ_z z _ hz_lookup
              have h_z_fst : Γ_z ⊢ˢ SMT.Term.fst (.var z) : τ.toSMTType :=
                SMT.Typing.fst _ _ _ _ h_z_var
              have h_result := toDestPair_typing_gen Γ_z vs
                (SMT.Term.fst (.var z)) (SMT.Term.fst (.var z))
                τ.toSMTType [] []
                vs_nemp rfl h_z_fst
                (by rw [τs_def] at τs_len; exact τs_len) rfl
                (fun j hj => absurd hj (Nat.not_lt_zero j))
                i τs[i]
                (by simp only [List.append_nil]; rw [List.getElem?_eq_getElem hi_τs])
              obtain ⟨hj, htyp⟩ := h_result
              exact htyp
    refine ⟨?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_⟩
    · -- 1. used ⊆ St₆.env.usedVars
      rw [St₆_used_chain]
      exact fun v hv => List.mem_cons_of_mem _
        (St₂_sub_St₃ (St₁_sub_St₂_used (used_sub_St₁ hv)))
    · -- 2. St₀.types ⊆ St₆.types
      intro ⟨k, τ_k⟩ hk_St₀
      rw [St₆_types, St₅_types, St₄_types]
      have hk_not_vs : k ∉ vs := by
        intro hk_in_vs
        have hk_St₀_mem : k ∈ St₀.types :=
          AList.mem_keys.mpr (List.mem_map.mpr ⟨⟨k, τ_k⟩, hk_St₀, rfl⟩)
        have hk_lambda : k ∈ (Term.lambda vs D P).vars := by
          unfold B.Term.vars; rw [List.mem_union_iff]; right
          simp only [B.bv, List.mem_append]; left; left; exact hk_in_vs
        exact vs_Γ_disj k hk_in_vs (Λ_inv k hk_lambda hk_St₀_mem)
      have hk_ne_z : k ≠ z := by
        intro rfl
        have : k ∈ St₀.types :=
          AList.mem_keys.mpr (List.mem_map.mpr ⟨⟨k, τ_k⟩, hk_St₀, rfl⟩)
        nomatch z_not_St₀ this
      have hk_St₃_kerase :
          ⟨k, τ_k⟩ ∈ (AList.insert z (τ.toSMTType.pair β.toSMTType) St₃.types).entries := by
        rw [AList.entries_insert_of_notMem z_fresh, List.mem_cons]
        right
        exact St₁_sub_St₃_types (St₀_sub_St₁ hk_St₀)
      have hk_foldl := AList.mem_foldl_erase_of_not_mem_keys hk_St₃_kerase hk_not_vs
      exact List.mem_kerase_of_ne_key hk_ne_z hk_foldl
    · -- 3. AList.keys St₆.types ⊆ St₆.env.usedVars
      rw [St₆_used_chain]
      intro v hv
      apply List.mem_cons_of_mem
      have hv_St₃ : v ∈ St₃.types :=
        (List.map_subset _ St₆_sub_St₃) hv
      exact St₃_keys_sub hv_St₃
    · -- 4. CoversUsedVars St₆.env.usedVars (lambda vs D P)
      rw [St₆_used_chain]
      intro v hv
      apply List.mem_cons_of_mem
      rw [B.fv, List.mem_append] at hv
      rcases hv with hv_D | hv_P
      · exact St₂_sub_St₃ (St₁_sub_St₂_used (covers_D v hv_D))
      · exact covers_P v (List.mem_filter.mp hv_P).1
    · -- 6. typing (extracted as h_typ_St₆)
      exact h_typ_St₆
    · -- 7. preserves types (same as defaults branch)
      intro v v_used v_notMem_St₀ v_notMem_vars v_mem_St₆
      simp only [B.fv, List.mem_append, not_or] at v_notMem_vars
      have v_notMem_fvD := v_notMem_vars.1
      have v_mem_St₃ : v ∈ St₃.types :=
        typeContext_mem_of_subset St₆_sub_St₃ v_mem_St₆
      have hv_not_vs : v ∉ vs := by
        intro hv_vs
        have : v ∉ St₆.types := by
          rw [St₆_types]; intro h_erase_z
          have h_in_St₅ : v ∈ St₅.types := (AList.mem_erase.mp h_erase_z).2
          rw [St₅_types] at h_in_St₅
          exact absurd h_in_St₅ (AList.not_mem_foldl_erase_of_mem hv_vs vs_nodup)
        exact this v_mem_St₆
      have v_notMem_fvP : v ∉ B.fv P := by
        intro hv_fvP
        apply v_notMem_vars.2
        unfold List.removeAll; rw [List.mem_filter]
        exact ⟨hv_fvP, by simp [hv_not_vs]⟩
      exfalso
      have v_notMem_St₁ := D_preserves_types v v_used v_notMem_St₀ v_notMem_fvD
      have v_notMem_St₂ : v ∉ St₂.types := by
        rw [St₂_types]; intro h
        exact v_notMem_St₁ (AList.mem_of_mem_foldl_insert' h (by
          intro hmem; rw [List.mem_map] at hmem
          obtain ⟨⟨a, b⟩, hab, rfl⟩ := hmem
          exact hv_not_vs (List.of_mem_zip hab).1))
      exact P_preserves_types v (St₁_sub_St₂_used (used_sub_St₁ v_used))
        v_notMem_St₂ v_notMem_fvP v_mem_St₃
    · -- 8. existential block: define Δ' using Δ_D for vs, else Δ_P (same as defaults)
      set Δ' : SMT.RenamingContext.Context := fun v =>
        if v ∈ vs then Δ_D v else Δ_P v with Δ'_def
      have Δ'_extends_Δ₀ : RenamingContext.Extends Δ' Δ₀ := by
        intro v d hv_eq
        rw [Δ'_def]
        by_cases hvs : v ∈ vs
        · simp [hvs]; exact Δ_D_extends hv_eq
        · simp [hvs]
          have hDD : Δ_D_ext v = Δ_D v := by
            rw [Δ_D_ext_def]; exact Function.updates_of_not_mem Δ_D vs _ v hvs
          exact Δ_P_extends (hDD ▸ Δ_D_extends hv_eq)
      have Δ'_none_out : ∀ v ∉ St₆.env.usedVars, Δ' v = none := by
        intro v hv_out
        rw [St₆_used_chain, List.mem_cons, not_or] at hv_out
        obtain ⟨hv_ne_z, hv_not_St₃⟩ := hv_out
        rw [Δ'_def]
        by_cases hvs : v ∈ vs
        · exfalso; apply hv_not_St₃
          have v_in_St₂ : v ∈ St₂.env.usedVars := by
            rw [St₂_used]
            suffices ∀ (ws : List SMT.𝒱) (τs' : List SMTType) (acc : List SMT.𝒱),
                ws.length ≤ τs'.length → v ∈ ws →
                v ∈ (ws.zip τs').foldl (fun used p => p.1 :: used) acc by
              exact this vs (τ.toSMTType.fromProdl (vs.length - 1)) St₁.env.usedVars
                (by rw [fromProdl_length_of_hasArity τ_hasArity]) hvs
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
          exact St₂_sub_St₃ v_in_St₂
        · simp [hvs]; exact Δ_P_none v hv_not_St₃
      have hcov_lambda : RenamingContext.CoversFV Δ'
          ((λˢ [z]) [τ.toSMTType.pair β.toSMTType]
            ((@ˢD_enc) (SMT.Term.var z).fst ∧ˢ
              ((SMT.Term.var z).snd =ˢ
                SMT.substList vs (toDestPair vs (SMT.Term.var z).fst) P_enc))) := by
        intro v hv
        simp only [SMT.fv, List.mem_removeAll_iff] at hv
        obtain ⟨hv_body, hv_ne_z⟩ := hv
        have hv_ne : v ≠ z := List.mem_singleton.not.mp hv_ne_z
        simp only [List.mem_append, List.mem_singleton] at hv_body
        rcases hv_body with ((hv_D | hv_z1) | (hv_z2 | hv_subst))
        · rw [Δ'_def]
          by_cases hvs : v ∈ vs
          · simp [hvs]; exact Δ_D_covers v hv_D
          · simp [hvs]
            have hDD_ext : Δ_D_ext v = Δ_D v := by
              rw [Δ_D_ext_def]; exact Function.updates_of_not_mem Δ_D vs _ v hvs
            have ⟨d, hd⟩ := Option.isSome_iff_exists.mp (Δ_D_covers v hv_D)
            exact Option.isSome_iff_exists.mpr ⟨d, Δ_P_extends (hDD_ext ▸ hd)⟩
        · exact absurd hv_z1 hv_ne
        · exact absurd hv_z2 hv_ne
        · rcases SMT_mem_fv_substList hv_subst with hv_P | ⟨t, ht, hv_t⟩
          · have hv_not_vs : v ∉ vs := by
              intro hvs
              suffices hlen : vs.length ≤ (toDestPair vs (SMT.Term.fst (.var z))).length by
                have hts : ∀ t ∈ toDestPair vs (SMT.Term.fst (.var z)), v ∉ SMT.fv t := by
                  intro t ht hv_t
                  exact hv_ne
                    (SMT_fv_toDestPair_subset_base (t₀ := .fst (.var z))
                      (by intro w hw; simp only [SMT.fv, List.mem_singleton] at hw; exact hw)
                      ht hv_t)
                exact absurd hv_subst (SMT_not_mem_fv_substList_of_mem_vars hlen hvs hts)
              suffices ∀ (ws : List SMT.𝒱) (zp : SMT.Term) (acc : List SMT.Term)
                  (d : SMT.Term),
                  ws.length + acc.length ≤ (toDestPair ws zp acc d).length by
                simpa using this vs (SMT.Term.fst (.var z)) [] (SMT.Term.fst (.var z))
              intro ws
              induction ws with
              | nil => intro _ acc _; simp [toDestPair]
              | cons w ws' ih =>
                intro zp acc d
                cases ws' with
                | nil => simp [toDestPair]; omega
                | cons w' ws'' =>
                  simp only [toDestPair]
                  have := ih (.fst d) (.snd d :: acc) (.fst d)
                  simp [List.length] at this ⊢; omega
            rw [Δ'_def]; simp [hv_not_vs]
            exact Δ_P_covers v hv_P
          · have := SMT_fv_toDestPair_subset_base (t₀ := .fst (.var z))
              (by intro w hw; simp only [SMT.fv, List.mem_singleton] at hw; exact hw)
              ht hv_t
            exact absurd this hv_ne
      refine ⟨Δ', hcov_lambda, Δ'_extends_Δ₀, ?_, Δ'_none_out, ?_⟩
      · exact RenamingContext.extendsOnSourceFV_of_extends Δ'_extends_Δ₀ Δ₀_ext
      · -- Chosen-branch denotation/RDom/totality. Hcompat + denT' existence parallel
        -- the defaults branch. RDom uses `lambda_chosen_retract_eq`, which mirrors
        -- `retract_lamVal_eq` adapted to lambda's and-body and chosen-branch sep
        -- construction.
        have hcompat : SMT.RenamingContext.RespectsTypeContextOnFV Δ' St₆.types
            ((λˢ [z]) [τ.toSMTType.pair β.toSMTType]
              ((@ˢD_enc) (SMT.Term.var z).fst ∧ˢ
                ((SMT.Term.var z).snd =ˢ
                  SMT.substList vs (toDestPair vs (SMT.Term.var z).fst) P_enc))) := by
          intro v τ_v hv_fv hlookup
          have hcov_v := hcov_lambda v hv_fv
          obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hcov_v
          refine ⟨d, hd, ?_⟩
          have hv_ne_z : v ≠ z := by
            simp only [SMT.fv, List.mem_removeAll_iff] at hv_fv
            intro rfl
            exact hv_fv.2 (List.mem_singleton.mpr rfl)
          have hv_not_vs : v ∉ vs := by
            simp only [SMT.fv, List.mem_removeAll_iff] at hv_fv
            obtain ⟨hv_body, _⟩ := hv_fv
            simp only [List.mem_append] at hv_body
            rcases hv_body with (hv_D | hv_z1) | (hv_z2 | hv_subst)
            · intro hvs
              exact vs_disj_St₁ v hvs (Typing.mem_context_of_mem_fv typ_D_enc hv_D)
            · simp only [List.mem_singleton] at hv_z1
              exact absurd hv_z1 hv_ne_z
            · simp only [List.mem_singleton] at hv_z2
              exact absurd hv_z2 hv_ne_z
            · intro hvs
              rcases SMT_mem_fv_substList hv_subst with hv_P | ⟨t, ht, hv_t⟩
              · suffices hlen : vs.length ≤ (toDestPair vs (SMT.Term.fst (.var z))).length by
                  have hts : ∀ t ∈ toDestPair vs (SMT.Term.fst (.var z)), v ∉ SMT.fv t := by
                    intro t ht hv_t
                    have hvz := SMT_fv_toDestPair_subset_base (v := v) (z := z)
                      (t₀ := SMT.Term.fst (.var z))
                      (by intro w hw; simp only [SMT.fv, List.mem_singleton] at hw; exact hw)
                      ht hv_t
                    exact hv_ne_z hvz
                  exact absurd hv_subst
                    (SMT_not_mem_fv_substList_of_mem_vars hlen hvs hts)
                suffices ∀ (ws : List SMT.𝒱) (zp : SMT.Term) (acc : List SMT.Term)
                    (d' : SMT.Term),
                    ws.length + acc.length ≤ (toDestPair ws zp acc d').length by
                  simpa using this vs (SMT.Term.fst (.var z)) [] (SMT.Term.fst (.var z))
                intro ws
                induction ws with
                | nil => intro _ acc _; simp [toDestPair]
                | cons w ws' ih =>
                  intro zp acc d'
                  cases ws' with
                  | nil => simp [toDestPair]; omega
                  | cons w' ws'' =>
                    simp only [toDestPair]
                    have := ih (.fst d') (.snd d' :: acc) (.fst d')
                    simp [List.length] at this ⊢; omega
              · have := SMT_fv_toDestPair_subset_base (v := v) (z := z)
                  (t₀ := SMT.Term.fst (.var z))
                  (by intro w hw; simp only [SMT.fv, List.mem_singleton] at hw; exact hw)
                  ht hv_t
                exact hv_ne_z this
          have hΔ'_eq : Δ' v = Δ_P v := by
            rw [Δ'_def]; simp [hv_not_vs]
          have hd_P : Δ_P v = some d := by rw [← hΔ'_eq]; exact hd
          have hlookup_St₃ : St₃.types.lookup v = some τ_v :=
            AList.mem_lookup_iff.2 (St₆_sub_St₃ (AList.mem_lookup_iff.1 hlookup))
          exact Δ_P_wt v d hd_P τ_v hlookup_St₃
        have hden_exists := SMT.RenamingContext.denote_exists_of_typing_fv
          h_typ_St₆ hcompat hcov_lambda
        obtain ⟨denT', hden_eq, hden_ty⟩ := hden_exists
        refine ⟨denT', hden_eq, ?_, ?_⟩
        · -- RDom: T = (𝒟.prod β.toZFSet).sep ℰ (non-empty in chosen branch).
          -- Requires showing retract (τ ×ᴮ β).set denT'.1 = T_chosen.
          -- Delegated to `lambda_chosen_retract_eq` helper which expects the
          -- semantic bridges (D/P data, ℰ predicate, hbridge).
          -- Derive hdenT_func: denT'.fst is a function ⟦τ.pair β⟧ᶻ → 𝔹.
          have hdenT_func : ⟦τ.toSMTType.pair β.toSMTType⟧ᶻ.IsFunc 𝔹 denT'.fst := by
            have := denT'.snd.snd
            rw [hden_ty, SMTType.toZFSet] at this
            exact ZFSet.mem_funs.mp this
          -- Derive z_not_fv_D, hcov_D_upd, hden_D_upd from Δ_D / den_D_enc.
          have z_not_fv_D : z ∉ SMT.fv D_enc := by
            intro hz_fv_D
            have hz_St₁ := Typing.mem_context_of_mem_fv typ_D_enc hz_fv_D
            have hz_St₃ : z ∈ St₃.types :=
              typeContext_mem_of_subset St₁_sub_St₃_types hz_St₁
            exact z_fresh hz_St₃
          have hcov_D_upd : ∀ W : SMT.Dom,
              SMT.RenamingContext.CoversFV
                (Function.update Δ' z (some W)) D_enc := by
            intro W v hv
            rw [Function.update_of_ne (by intro rfl; exact z_not_fv_D hv)]
            rw [Δ'_def]
            by_cases hvs : v ∈ vs
            · simp [hvs]; exact Δ_D_covers v hv
            · simp [hvs]
              have hDD : Δ_D_ext v = Δ_D v := by
                rw [Δ_D_ext_def]
                exact Function.updates_of_not_mem Δ_D vs _ v hvs
              have ⟨d, hd⟩ := Option.isSome_iff_exists.mp (Δ_D_covers v hv)
              exact Option.isSome_iff_exists.mpr ⟨d, Δ_P_extends (hDD ▸ hd)⟩
          have hden_D_upd : ∀ W : SMT.Dom,
              ⟦D_enc.abstract (Function.update Δ' z (some W))
                  (hcov_D_upd W)⟧ˢ = some denD' := by
            intro W
            have h_agree : SMT.RenamingContext.AgreesOnFV
                (Function.update Δ' z (some W)) Δ_D D_enc := by
              intro v hv
              have hvz : v ≠ z := by intro heq; subst heq; exact z_not_fv_D hv
              rw [Function.update_of_ne hvz]
              rw [Δ'_def]
              by_cases hvs : v ∈ vs
              · simp [hvs]
              · simp [hvs]
                have hDD : Δ_D_ext v = Δ_D v := by
                  rw [Δ_D_ext_def]
                  exact Function.updates_of_not_mem Δ_D vs _ v hvs
                have ⟨d, hd⟩ := Option.isSome_iff_exists.mp (Δ_D_covers v hv)
                have := Δ_P_extends (hDD ▸ hd)
                rw [hd, this]
            have heq := SMT.RenamingContext.denote_congr_of_agreesOnFV
              (h1 := hcov_D_upd W) (h2 := Δ_D_covers) h_agree
            unfold SMT.RenamingContext.denote at heq
            rw [heq]
            exact den_D_enc
          -- Derive D-level RDom data from D_RDom.
          have denD_val_type : denD'.snd.fst = τ.toSMTType.fun SMTType.bool :=
            D_RDom.1.1
          have denD_val_func : ⟦τ.toSMTType⟧ᶻ.IsFunc 𝔹 denD'.fst := by
            have := denD'.snd.snd
            rw [denD_val_type, SMTType.toZFSet] at this
            exact ZFSet.mem_funs.mp this
          have denD_val_retract : retract τ.set denD'.fst = 𝒟 := D_RDom.1.2
          -- Establish 𝒟 = 𝒟'.
          have h𝒟_eq : 𝒟 = 𝒟' := by
            have : ⟦D.abstract «Δ» Δ_fv_D⟧ᴮ = some ⟨𝒟', ⟨τ.set, h𝒟'⟩⟩ := den_D_eq
            rw [den_D] at this
            exact congrArg (fun (p : B.Dom) => p.1) (Option.some.inj this)
          -- Apply the helper using the real B-level sep predicate as ℰ
          -- so that `hT_eq` reduces to `rfl` (modulo `𝒟 = 𝒟'`) and the
          -- substantive `retract = T_chosen` obligation lives in the
          -- helper body itself.
          refine lambda_chosen_retract_eq
            (vs := vs) (τ := τ) (β := β) (D_enc := D_enc) (P_enc := P_enc)
            (z := z) (Δ' := Δ') (denT' := denT') (denD_val := denD') (𝒟_val := 𝒟)
            (ℰ := ?ℰ)
            vs_nemp vs_nodup rfl hcov_lambda hden_eq hden_ty hdenT_func
            hcov_D_upd hden_D_upd denD_val_type denD_val_func h𝒟 denD_val_retract
            hT ?hT_eq ?hbridge
          case ℰ =>
            -- The sep predicate from the B-level lambda denotation
            -- (B/SemanticsPHOAS.lean:563+):
            -- ℰ(xy) iff xy is a 2-tuple, xy.π₁ ∈ 𝒟', and P-eval at xy.π₁
            -- matches xy.π₂ with type β. We mirror this exactly so that
            -- `(𝒟.prod ⟦β⟧ᶻ).sep ℰ = T_chosen` is essentially reflexive.
            classical
            exact fun xy =>
              if hxy : xy.hasArity 2 then
                if hx : xy.π₁.hasArity vs.length ∧ xy.π₁ ∈ 𝒟' then
                  match (motive := Option B.Dom → Prop) ⟦(B.Term.abstract.go P vs «Δ»
                      (fun v hv hvs =>
                        Δ_fv v (fv.mem_lambda (.inr ⟨hv, hvs⟩)))).uncurry
                      (fun i => ⟨xy.π₁.get vs.length i, ⟨τ.get vs.length i,
                        get_mem_type_of_isTuple hx.1 τ_hasArity (by
                          rw [BType.toZFSet, ZFSet.mem_powerset] at h𝒟'
                          exact h𝒟' hx.2)⟩⟩)⟧ᴮ with
                  | some ⟨ex, ⟨ξ, _⟩⟩ => if ξ = β then ex = xy.π₂ else False
                  | none => False
                else False
              else False
          case hT_eq =>
            -- hT_eq: (𝒟.prod ⟦β⟧ᶻ).sep ℰ = T_chosen
            -- With the chosen ℰ matching the B-level predicate exactly,
            -- this reduces to reflexivity modulo `𝒟 = 𝒟'` (h𝒟_eq).
            subst h𝒟_eq
            rfl
          case hbridge =>
            -- The helper's `hbridge` parameter requires a real semantic bridge.
            -- Proof strategy: unfold lambda denotation → body_val, use
            -- lambda_hbridge for the body-level iff, convert to sep membership.
            -- All ingredients assembled here from the local context.
            intro xy hxy_mem
            -- Decompose xy ∈ ⟦τ ×ᴮ β⟧ᶻ = ⟦τ⟧ᶻ.prod ⟦β⟧ᶻ.
            have hxy_prod : xy ∈ ⟦τ⟧ᶻ.prod ⟦β⟧ᶻ := hxy_mem
            rw [ZFSet.mem_prod] at hxy_prod
            obtain ⟨a, ha_mem, b, hb_mem, hxy_eq⟩ := hxy_prod
            have hxy_pair : xy = a.pair b := hxy_eq
            have hxy_π₁_eq : xy.π₁ = a := by rw [hxy_pair, ZFSet.π₁_pair]
            have hxy_π₂_eq : xy.π₂ = b := by rw [hxy_pair, ZFSet.π₂_pair]
            have hx_mem : xy.π₁ ∈ ⟦τ⟧ᶻ := hxy_π₁_eq ▸ ha_mem
            have hy_mem : xy.π₂ ∈ ⟦β⟧ᶻ := hxy_π₂_eq ▸ hb_mem
            have hxy_pair' : xy = xy.π₁.pair xy.π₂ := by rw [hxy_π₁_eq, hxy_π₂_eq, ← hxy_pair]
            have hxy_π₁_arity : xy.π₁.hasArity vs.length := hasArity_of_mem_toZFSet τ_hasArity hx_mem
            -- Build prerequisites for lambda_hbridge.
            have z_not_fv_P : z ∉ SMT.fv P_enc :=
              fun hz => z_fresh (Typing.mem_context_of_mem_fv typ_P_enc hz)
            have z_not_vs : z ∉ vs := fun hz =>
              z_not_used (St₂_sub_St₃ (St₁_sub_St₂_used (used_sub_St₁ (vars_used_vs z hz))))
            have hvs_not_bv_P : ∀ v ∈ vs, v ∉ SMT.bv P_enc := by
              intro v hv hbv
              have hv_St₃ : v ∈ St₃.types := typeContext_mem_of_subset St₂_sub_St₃_types (by
                rw [St₂_types]
                have hτs_len := fromProdl_length_of_hasArity τ_hasArity
                have hv_idx : vs.idxOf v < vs.length := List.idxOf_lt_length_of_mem hv
                have hv_idx_τ : vs.idxOf v < (τ.toSMTType.fromProdl (vs.length - 1)).length := by
                  rw [hτs_len]; exact hv_idx
                have h := foldl_insert_lookup_zip (Γ := St₁.types) vs_nodup hv_idx hv_idx_τ
                rw [List.getElem_idxOf hv_idx] at h
                exact AList.mem_keys.mpr (AList.lookup_isSome.mp (by simp [h])))
              exact SMT.Typing.bv_notMem_context typ_P_enc v hbv hv_St₃
            have z_not_bv_P : z ∉ SMT.bv P_enc := by
              intro hbv
              exact SMT.Typing.bv_notMem_context
                (SMT.Typing.weakening
                  (SMT.TypeContext.entries_subset_insert_of_notMem (τ := τ.toSMTType) z_fresh)
                  typ_P_enc)
                z hbv ((AList.mem_insert _).mpr (Or.inl rfl))
            have fv_substList_disj_vs :
                ∀ v ∈ SMT.fv (SMT.substList vs (toDestPair vs (SMT.Term.var z).fst) P_enc),
                v ≠ z → v ∉ vs := by
              intro v hv hne hvs
              rcases SMT_mem_fv_substList hv with hv_P | ⟨t, ht, hv_t⟩
              · have hts : ∀ t ∈ toDestPair vs (SMT.Term.fst (.var z)), v ∉ SMT.fv t :=
                  fun t ht hv_t => hne (SMT_fv_toDestPair_subset_base
                    (t₀ := (SMT.Term.var z).fst)
                    (by intro w hw; simp only [SMT.fv, List.mem_singleton] at hw; exact hw) ht hv_t)
                have hlen : vs.length ≤ (toDestPair vs (SMT.Term.fst (.var z))).length :=
                  (fun _ => by
                    suffices ∀ (ws : List SMT.𝒱) (zp : SMT.Term) (acc : List SMT.Term) (d : SMT.Term),
                        ws.length + acc.length ≤ (toDestPair ws zp acc d).length by
                      simpa using this vs (SMT.Term.fst (.var z)) [] (SMT.Term.fst (.var z))
                    intro ws; induction ws with
                    | nil => intro _ acc _; simp [toDestPair]
                    | cons w ws' ih =>
                      intro zp acc d; cases ws' with
                      | nil => simp [toDestPair]; omega
                      | cons w' ws'' =>
                        simp only [toDestPair]
                        have := ih (.fst d) (.snd d :: acc) (.fst d)
                        simp [List.length] at this ⊢; omega) ()
                exact absurd hv (SMT_not_mem_fv_substList_of_mem_vars hlen hvs hts)
              · exact hne (SMT_fv_toDestPair_subset_base
                  (t₀ := (SMT.Term.var z).fst)
                  (by intro w hw; simp only [SMT.fv, List.mem_singleton] at hw; exact hw) ht hv_t)
            set body_t : SMT.Term :=
              ((@ˢD_enc) (SMT.Term.var z).fst ∧ˢ
                ((SMT.Term.var z).snd =ˢ
                  SMT.substList vs (toDestPair vs (SMT.Term.var z).fst) P_enc)) with body_t_def
            have hgo_cov : ∀ x ∈ SMT.fv body_t, x ∉ [z] → (Δ' x).isSome = true :=
              fun x hx hxz => hcov_lambda x (SMT.fv.mem_lambda ⟨hx, hxz⟩)
            have hcov_body_upd : ∀ W : SMT.Dom,
                SMT.RenamingContext.CoversFV (Function.update Δ' z (some W)) body_t := by
              intro W x hx
              by_cases hxz : x = z
              · subst hxz; simp [Function.update]
              · rw [Function.update_of_ne hxz]; exact hgo_cov x hx (by simp [hxz])
            have hcov_substList_upd : ∀ W : SMT.Dom,
                SMT.RenamingContext.CoversFV (Function.update Δ' z (some W))
                  (SMT.substList vs (toDestPair vs (SMT.Term.var z).fst) P_enc) := fun W x hx =>
              hcov_body_upd W x (by
                simp only [body_t_def, SMT.fv, List.mem_append]
                exact Or.inr (Or.inr hx))
            have Δ_ctx_source : ∀ v ∈ B.fv P, v ∉ vs → Δ' v = B.RenamingContext.toSMT «Δ» v := by
              intro v hv hvs
              rw [Δ'_def]; simp [hvs]
              have h1 : B.RenamingContext.toSMTOnFV Δ_ext P v = B.RenamingContext.toSMT Δ_ext v :=
                by simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                  B.RenamingContext.restrictToFV_eq_of_mem hv]
              have hΔ_ext_v : Δ_ext v = «Δ» v :=
                Δ_ext_def ▸ Function.updates_of_not_mem «Δ» vs (List.ofFn fun i => some (f i)) v hvs
              have hsome : ∃ d, B.RenamingContext.toSMT Δ_ext v = some d := by
                obtain ⟨bdom, hbdom⟩ := Option.isSome_iff_exists.mp (Δ_fv_P v hv)
                simp only [B.RenamingContext.toSMT, hbdom, Option.pure_def]
                exact ⟨_, rfl⟩
              obtain ⟨d, hd⟩ := hsome
              have hΔ_P_v_eq : Δ_P v = some d :=
                Δ_P_src_ext (h1 ▸ hd : B.RenamingContext.toSMTOnFV Δ_ext P v = some d)
              exact hΔ_P_v_eq.trans (hd.symm.trans (by simp [B.RenamingContext.toSMT, hΔ_ext_v]))
            have P_enc_total_simple :
                ∀ (Δ_alt : B.RenamingContext.Context)
                  (Δ_fv_alt : ∀ v ∈ B.fv P, (Δ_alt v).isSome = true)
                  (Δ₀_alt : SMT.RenamingContext.Context),
                  SMT.RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt P →
                  (∀ v ∉ St₃.env.usedVars, Δ₀_alt v = none) →
                  ∀ (T_alt : ZFSet) (hT_alt : T_alt ∈ ⟦β⟧ᶻ),
                    ⟦P.abstract Δ_alt Δ_fv_alt⟧ᴮ = some ⟨T_alt, ⟨β, hT_alt⟩⟩ →
                    ∃ (Δ'_alt : SMT.RenamingContext.Context)
                      (hcov_alt : SMT.RenamingContext.CoversFV Δ'_alt P_enc)
                      (denT_alt : SMT.Dom),
                      SMT.RenamingContext.Extends Δ'_alt Δ₀_alt ∧
                      ⟦P_enc.abstract Δ'_alt hcov_alt⟧ˢ = some denT_alt ∧
                      (⟨T_alt, ⟨β, hT_alt⟩⟩ : B.Dom) ≘ᶻ denT_alt := by
              intro Δ_alt Δ_fv_alt Δ₀_alt hext' hnone' T_alt hT_alt hden'
              obtain ⟨Δ'_out, hcov_out, denT_out, hext_out, _, _, hden_out, hRDom_out, _⟩ :=
                P_enc_total Δ_alt Δ_fv_alt Δ₀_alt hext' hnone'
                  (SMT.RenamingContext.ExtendsOnSourceFV.wt hext' typ_P_enc) T_alt hT_alt hden'
              exact ⟨Δ'_out, hcov_out, denT_out, hext_out, hden_out, hRDom_out⟩
            -- Now apply lambda_hbridge.
            -- lambda_hbridge needs hxy_𝒟 : xy.π₁ ∈ 𝒟_val. We handle both directions
            -- of the iff by case-splitting on xy.π₁ ∈ 𝒟 ∨ xy.π₁ ∉ 𝒟.
            by_cases hxy_𝒟 : xy.π₁ ∈ 𝒟
            · -- Case: xy.π₁ ∈ 𝒟. Apply lambda_hbridge directly.
              -- Build Wxy : SMT.Dom = canonical image of xy.
              have hcanon_mem : (ZFSet.fapply (BType.canonicalIsoSMTType (τ ×ᴮ β)).1
                  (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType (τ ×ᴮ β)).2.1)
                  ⟨xy, by rwa [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType (τ ×ᴮ β)).2.1]⟩).1 ∈
                  ⟦τ.toSMTType.pair β.toSMTType⟧ᶻ := by
                exact (ZFSet.fapply (BType.canonicalIsoSMTType (τ ×ᴮ β)).1
                    (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType (τ ×ᴮ β)).2.1)
                    ⟨xy, by rwa [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType (τ ×ᴮ β)).2.1]⟩).2
              let Wxy : SMT.Dom := ⟨_, τ.toSMTType.pair β.toSMTType, hcanon_mem⟩
              have hWxy_mem : Wxy.fst ∈ ⟦τ.toSMTType.pair β.toSMTType⟧ᶻ := hcanon_mem
              -- Unfold lambda denotation.
              have hlamVal' := hden_eq
              rw [SMT.Term.abstract, dif_pos (by rfl)] at hlamVal'
              simp only [SMT.denote] at hlamVal'
              rw [dif_pos (show [z].length > 0 from Nat.zero_lt_succ 0)] at hlamVal'
              split_ifs at hlamVal' with h_isSome h_typ_det
              · let xₙ : Fin 1 → SMT.Dom := fun _ => Wxy
                have hxₙ_spec : ∀ i, (xₙ i).snd.fst = [τ.toSMTType.pair β.toSMTType][↑i] ∧
                    (xₙ i).fst ∈ ⟦[τ.toSMTType.pair β.toSMTType][↑i]⟧ᶻ :=
                  fun ⟨i, hi⟩ => by
                    simp only [List.length_cons, List.length_nil, Nat.lt_one_iff] at hi
                    subst hi; exact ⟨rfl, hWxy_mem⟩
                have hgo_xy := funAbstractGoSingle (Δctx := Δ') (P := body_t) (v := z)
                  (τ := τ.toSMTType.pair β.toSMTType) hgo_cov hcov_body_upd xₙ hxₙ_spec
                obtain ⟨body_val, hbody_val⟩ :=
                  Option.isSome_iff_exists.mp (show (⟦body_t.abstract _ _⟧ˢ).isSome = true by
                    rw [← hgo_xy]; exact h_isSome hxₙ_spec)
                -- Build h_pair_mem: Wxy.fst.pair body_val.fst ∈ denT'.fst.
                have h_pair_mem : Wxy.fst.pair body_val.fst ∈ denT'.fst := by
                  simp only [Option.pure_def, Option.some.injEq] at hlamVal'
                  have hlamVal_fst : denT'.fst = _ := congrArg (·.fst) hlamVal'.symm
                  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.sub_self,
                    Fin.foldr_zero, List.getElem_cons_zero] at hlamVal_fst
                  rw [hlamVal_fst, ZFSet.mem_lambda]
                  refine ⟨Wxy.fst, body_val.fst, rfl, hWxy_mem, ?_, ?_⟩
                  · have hden_xₙ : ⟦(SMT.Term.abstract.go body_t [z] Δ' hgo_cov).uncurry xₙ⟧ˢ
                        = some body_val := by rw [hgo_xy]; exact hbody_val
                    have hγ := h_typ_det xₙ
                      (fun _ => ⟨(τ.toSMTType.pair β.toSMTType).defaultZFSet,
                               τ.toSMTType.pair β.toSMTType, SMTType.mem_toZFSet_of_defaultZFSet⟩)
                      hxₙ_spec
                      (fun ⟨i, hi⟩ => by
                        simp only [List.length_cons, List.length_nil] at hi
                        have hi' : i = 0 := by omega
                        subst hi'; exact ⟨rfl, SMTType.mem_toZFSet_of_defaultZFSet⟩)
                    rw [congrArg (·.snd.fst) (Option.get_of_eq_some _ hden_xₙ)] at hγ
                    exact hγ ▸ body_val.snd.snd
                  · split_ifs with hw'
                    · let xₙ' := fun i : Fin 1 =>
                          (⟨Wxy.fst.get 1 i, [τ.toSMTType.pair β.toSMTType][↑i], hw'.2 i⟩ : SMT.Dom)
                      have hgo' := funAbstractGoSingle (Δctx := Δ') (P := body_t) (v := z)
                        (τ := τ.toSMTType.pair β.toSMTType)
                        hgo_cov hcov_body_upd xₙ' (fun i => ⟨rfl, hw'.2 i⟩)
                      have hden' : ⟦(SMT.Term.abstract.go body_t [z] Δ' hgo_cov).uncurry xₙ'⟧ˢ
                          = some body_val := by rw [hgo', show xₙ' ⟨0, Nat.zero_lt_one⟩ = Wxy from rfl]; exact hbody_val
                      exact (congrArg (·.fst) (Option.get_of_eq_some _ hden')).symm
                    · exact absurd ⟨trivial, fun ⟨i, hi⟩ => by
                        simp only [Nat.lt_one_iff] at hi; subst hi; exact hWxy_mem⟩ hw'
                -- Connect fapply to body_val.fst.
                have h_fap_eq : (ZFSet.fapply denT'.fst (ZFSet.is_func_is_pfunc hdenT_func)
                    ⟨Wxy.fst, by rw [ZFSet.is_func_dom_eq hdenT_func]; exact hWxy_mem⟩).1 =
                    body_val.fst := by
                  have := ZFSet.fapply.of_pair (ZFSet.is_func_is_pfunc hdenT_func) h_pair_mem
                  exact congrArg Subtype.val this
                -- Get hxy_𝒟 for lambda_hbridge (in 𝒟' = 𝒟 sense).
                have hxy_𝒟' : xy.π₁ ∈ 𝒟 := hxy_𝒟
                -- Apply lambda_hbridge.
                have hbridge_iff := lambda_hbridge vs_nemp vs_nodup τ_hasArity
                  z_not_fv_D z_not_fv_P z_not_vs vs_not_D_fv hvs_not_bv_P z_not_bv_P
                  (Δ_ctx := Δ') hcov_body_upd hcov_D_upd hden_D_upd
                  denD_val_type denD_val_func h𝒟 denD_val_retract
                  hcov_substList_upd fv_substList_disj_vs
                  Δ_fv typP (SMT.RenamingContext.extends_trans Δ_D_extends Δ₀_ext) Δ_ctx_source
                  Δ_D_none_St₂ (fun v hv => St₁_sub_St₂_used (used_sub_St₁ (vars_used_vs v hv))) St₂_sub_St₃
                  (fun v hv => St₃_keys_sub (Typing.mem_context_of_mem_fv typ_P_enc hv))
                  P_enc_total_simple
                  (fun hx hxD => h_den_E hx (h𝒟_eq ▸ hxD))
                  xy hx_mem hy_mem hxy_pair' hxy_π₁_arity hxy_𝒟'
                  body_val hbody_val
                -- Convert the iff.
                -- hbridge_iff : body_val.fst = zftrue ↔ ∃ Px hP, P-go-uncurry ... = ... ∧ Px = xy.π₂
                -- Goal: fapply denT'.fst canonical(xy) = zftrue ↔ xy ∈ sep ℰ (𝒟.prod ⟦β⟧ᶻ)
                rw [show (↑(ZFSet.fapply denT'.fst (ZFSet.is_func_is_pfunc hdenT_func)
                    ⟨↑(ZFSet.fapply (BType.canonicalIsoSMTType (τ ×ᴮ β)).1
                      (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType (τ ×ᴮ β)).2.1)
                      ⟨xy, by rwa [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType (τ ×ᴮ β)).2.1]⟩), _⟩)) =
                    body_val.fst from h_fap_eq]
                rw [ZFSet.mem_sep]
                constructor
                · intro hbody_true
                  refine ⟨?_, ?_⟩
                  · -- xy ∈ 𝒟.prod ⟦β⟧ᶻ
                    rw [ZFSet.mem_prod]
                    exact ⟨xy.π₁, hxy_𝒟', xy.π₂, hy_mem, hxy_pair'⟩
                  · -- ℰ xy
                    have hxy_arity2 : xy.hasArity 2 := hxy_pair ▸ ZFSet.isTuple_pair
                    have hx_cond : xy.π₁.hasArity vs.length ∧ xy.π₁ ∈ 𝒟' :=
                      ⟨hxy_π₁_arity, h𝒟_eq ▸ hxy_𝒟'⟩
                    simp only [dif_pos hxy_arity2, dif_pos hx_cond]
                    obtain ⟨Px, hPx_mem, hPx_den, hPx_eq⟩ := hbridge_iff.mp hbody_true
                    simp only [hPx_den, hPx_eq, ↓reduceIte]
                · intro ⟨hprod, hℰ⟩
                  rw [ZFSet.mem_prod] at hprod
                  have hxy_arity2 : xy.hasArity 2 := hxy_pair ▸ ZFSet.isTuple_pair
                  have hx_cond : xy.π₁.hasArity vs.length ∧ xy.π₁ ∈ 𝒟' :=
                    ⟨hxy_π₁_arity, h𝒟_eq ▸ hxy_𝒟'⟩
                  simp only [dif_pos hxy_arity2, dif_pos hx_cond] at hℰ
                  apply hbridge_iff.mpr
                  rcases h_match : ⟦(B.Term.abstract.go P vs «Δ» ⋯).uncurry
                      fun i => ⟨xy.π₁.get vs.length i, ⟨τ.get vs.length i, ⋯⟩⟩⟧ᴮ with
                    _ | ⟨Px_val, ξ, hPx_mem⟩
                  · simp [h_match] at hℰ
                  · simp only [h_match] at hℰ
                    split_ifs at hℰ with hξ
                    exact ⟨Px_val, hξ ▸ hPx_mem, by subst hξ; rfl, hℰ⟩
            · -- Case: xy.π₁ ∉ 𝒟.
              -- Forward: fapply = zftrue → contradiction (D_enc would require xy.π₁ ∈ 𝒟).
              -- Backward: xy ∈ sep ℰ → xy.π₁ ∈ 𝒟.prod → xy.π₁ ∈ 𝒟 → contradiction.
              constructor
              · intro hfap_true
                -- Build body_val and use AND-decomposition.
                have hcanon_mem : (ZFSet.fapply (BType.canonicalIsoSMTType (τ ×ᴮ β)).1
                    (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType (τ ×ᴮ β)).2.1)
                    ⟨xy, by rwa [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType (τ ×ᴮ β)).2.1]⟩).1 ∈
                    ⟦τ.toSMTType.pair β.toSMTType⟧ᶻ :=
                  (ZFSet.fapply (BType.canonicalIsoSMTType (τ ×ᴮ β)).1
                    (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType (τ ×ᴮ β)).2.1)
                    ⟨xy, by rwa [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType (τ ×ᴮ β)).2.1]⟩).2
                let Wxy : SMT.Dom := ⟨_, τ.toSMTType.pair β.toSMTType, hcanon_mem⟩
                have hWxy_mem : Wxy.fst ∈ ⟦τ.toSMTType.pair β.toSMTType⟧ᶻ := hcanon_mem
                have hlamVal' := hden_eq
                rw [SMT.Term.abstract, dif_pos (by rfl)] at hlamVal'
                simp only [SMT.denote] at hlamVal'
                rw [dif_pos (show [z].length > 0 from Nat.zero_lt_succ 0)] at hlamVal'
                split_ifs at hlamVal' with h_isSome h_typ_det
                · let xₙ : Fin 1 → SMT.Dom := fun _ => Wxy
                  have hxₙ_spec : ∀ i, (xₙ i).snd.fst = [τ.toSMTType.pair β.toSMTType][↑i] ∧
                      (xₙ i).fst ∈ ⟦[τ.toSMTType.pair β.toSMTType][↑i]⟧ᶻ :=
                    fun ⟨i, hi⟩ => by
                      simp only [List.length_cons, List.length_nil, Nat.lt_one_iff] at hi
                      subst hi; exact ⟨rfl, hWxy_mem⟩
                  have hgo_xy := funAbstractGoSingle (Δctx := Δ') (P := body_t) (v := z)
                    (τ := τ.toSMTType.pair β.toSMTType) hgo_cov hcov_body_upd xₙ hxₙ_spec
                  obtain ⟨body_val, hbody_val⟩ :=
                    Option.isSome_iff_exists.mp (show (⟦body_t.abstract _ _⟧ˢ).isSome = true by
                      rw [← hgo_xy]; exact h_isSome hxₙ_spec)
                  -- Connect fapply to body_val.fst.
                  have h_pair_mem : Wxy.fst.pair body_val.fst ∈ denT'.fst := by
                    simp only [Option.pure_def, Option.some.injEq] at hlamVal'
                    have hlamVal_fst : denT'.fst = _ := congrArg (·.fst) hlamVal'.symm
                    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.sub_self,
                      Fin.foldr_zero, List.getElem_cons_zero] at hlamVal_fst
                    rw [hlamVal_fst, ZFSet.mem_lambda]
                    refine ⟨Wxy.fst, body_val.fst, rfl, hWxy_mem, ?_, ?_⟩
                    · have hden_xₙ : ⟦(SMT.Term.abstract.go body_t [z] Δ' hgo_cov).uncurry xₙ⟧ˢ
                          = some body_val := by rw [hgo_xy]; exact hbody_val
                      have hγ := h_typ_det xₙ
                        (fun _ => ⟨(τ.toSMTType.pair β.toSMTType).defaultZFSet,
                                 τ.toSMTType.pair β.toSMTType, SMTType.mem_toZFSet_of_defaultZFSet⟩)
                        hxₙ_spec
                        (fun ⟨i, hi⟩ => by
                          simp only [List.length_cons, List.length_nil] at hi
                          have hi' : i = 0 := by omega
                          subst hi'; exact ⟨rfl, SMTType.mem_toZFSet_of_defaultZFSet⟩)
                      rw [congrArg (·.snd.fst) (Option.get_of_eq_some _ hden_xₙ)] at hγ
                      exact hγ ▸ body_val.snd.snd
                    · split_ifs with hw'
                      · let xₙ' := fun i : Fin 1 =>
                            (⟨Wxy.fst.get 1 i, [τ.toSMTType.pair β.toSMTType][↑i], hw'.2 i⟩ : SMT.Dom)
                        have hgo' := funAbstractGoSingle (Δctx := Δ') (P := body_t) (v := z)
                          (τ := τ.toSMTType.pair β.toSMTType)
                          hgo_cov hcov_body_upd xₙ' (fun i => ⟨rfl, hw'.2 i⟩)
                        have hden' : ⟦(SMT.Term.abstract.go body_t [z] Δ' hgo_cov).uncurry xₙ'⟧ˢ
                            = some body_val := by
                          rw [hgo', show xₙ' ⟨0, Nat.zero_lt_one⟩ = Wxy from rfl]; exact hbody_val
                        exact (congrArg (·.fst) (Option.get_of_eq_some _ hden')).symm
                      · exact absurd ⟨trivial, fun ⟨i, hi⟩ => by
                          simp only [Nat.lt_one_iff] at hi; subst hi; exact hWxy_mem⟩ hw'
                  have h_fap_body : (ZFSet.fapply denT'.fst (ZFSet.is_func_is_pfunc hdenT_func)
                      ⟨Wxy.fst, by rw [ZFSet.is_func_dom_eq hdenT_func]; exact hWxy_mem⟩).1 =
                      body_val.fst :=
                    congrArg Subtype.val (ZFSet.fapply.of_pair (ZFSet.is_func_is_pfunc hdenT_func) h_pair_mem)
                  -- body_val.fst = zftrue from fapply = zftrue.
                  have hbody_true : body_val.fst = zftrue := by convert hfap_true using 1; exact h_fap_body.symm
                  -- AND-decomposition: D_enc part = zftrue → xy.π₁ ∈ retract = 𝒟.
                  obtain ⟨_, Dapp, hDapp_ty, hDapp_val, hDapp_den⟩ :=
                    funDenoteAppAtFst (Δctx := Δ') (t := D_enc) (x := z)
                      (α := τ.toSMTType) (β := SMTType.bool) (γ := β.toSMTType) (Y := denD')
                      hcov_D_upd hden_D_upd denD_val_type denD_val_func Wxy rfl hWxy_mem
                  set D_app_t : SMT.Term := (@ˢD_enc) (SMT.Term.var z).fst with D_app_def
                  set eq_t : SMT.Term :=
                    (SMT.Term.var z).snd =ˢ
                      SMT.substList vs (toDestPair vs (SMT.Term.var z).fst) P_enc with eq_def
                  have hcov_D_app : ∀ W : SMT.Dom,
                      SMT.RenamingContext.CoversFV (Function.update Δ' z (some W)) D_app_t :=
                    fun W x hx => hcov_body_upd W x (by
                      simp only [body_t_def, D_app_def, SMT.fv, List.mem_append] at hx ⊢
                      exact Or.inl hx)
                  have hcov_eq_t : ∀ W : SMT.Dom,
                      SMT.RenamingContext.CoversFV (Function.update Δ' z (some W)) eq_t :=
                    fun W x hx => hcov_body_upd W x (by
                      simp only [body_t_def, eq_def, SMT.fv, List.mem_append] at hx ⊢
                      exact Or.inr hx)
                  have hDapp_den' : ⟦D_app_t.abstract (Function.update Δ' z (some Wxy))
                                      (hcov_D_app Wxy)⟧ˢ = some Dapp := by
                    simp only [D_app_def]; convert hDapp_den using 1
                  have hbody_decomp :
                      ⟦body_t.abstract (Function.update Δ' z (some Wxy)) (hcov_body_upd Wxy)⟧ˢ =
                      ⟦(D_app_t.abstract (Function.update Δ' z (some Wxy)) (hcov_D_app Wxy)) ∧ˢ'
                        (eq_t.abstract (Function.update Δ' z (some Wxy)) (hcov_eq_t Wxy))⟧ˢ := by
                    simp only [body_t_def, D_app_def, eq_def, SMT.Term.abstract]
                  -- AND decomposition gives Dapp.fst = zftrue.
                  have hDapp_ty_bool : Dapp.snd.fst = SMTType.bool := hDapp_ty
                  have hbody_val_decomp :
                      ⟦(D_app_t.abstract (Function.update Δ' z (some Wxy)) (hcov_D_app Wxy)) ∧ˢ'
                        (eq_t.abstract (Function.update Δ' z (some Wxy)) (hcov_eq_t Wxy))⟧ˢ = some body_val := by
                    rw [← hbody_decomp]; exact hbody_val
                  -- Extract eq_t denotation from the AND (inline denote_and_extract_right).
                  obtain ⟨Deq, hDeq_den, hDeq_ty⟩ : ∃ Deq : SMT.Dom,
                      ⟦eq_t.abstract (Function.update Δ' z (some Wxy)) (hcov_eq_t Wxy)⟧ˢ = some Deq ∧
                      Deq.snd.fst = .bool := by
                    obtain ⟨dp, τp, hdp⟩ := Dapp
                    simp only [] at hDapp_ty_bool
                    subst hDapp_ty_bool
                    simp only [SMT.denote, Option.bind_eq_bind, hDapp_den'] at hbody_val_decomp
                    match hq : ⟦eq_t.abstract (Function.update Δ' z (some Wxy)) (hcov_eq_t Wxy)⟧ˢ with
                    | none => simp [hq] at hbody_val_decomp
                    | some ⟨Q, .bool, hQ⟩ => exact ⟨⟨Q, .bool, hQ⟩, rfl, rfl⟩
                    | some ⟨Q, .int, hQ⟩ => simp [hq] at hbody_val_decomp
                    | some ⟨Q, .unit, hQ⟩ => simp [hq] at hbody_val_decomp
                    | some ⟨Q, .fun _ _, hQ⟩ => simp [hq] at hbody_val_decomp
                    | some ⟨Q, .option _, hQ⟩ => simp [hq] at hbody_val_decomp
                    | some ⟨Q, .pair _ _, hQ⟩ => simp [hq] at hbody_val_decomp
                  -- Use denote_and_both_zftrue_of_zftrue.
                  have hDq_den' : ⟦eq_t.abstract (Function.update Δ' z (some Wxy)) (hcov_eq_t Wxy)⟧ˢ =
                      some _ := hDeq_den
                  obtain ⟨hDapp_true, _⟩ := denote_and_both_zftrue_of_zftrue
                    hDapp_den' hDapp_ty_bool hDq_den' hDeq_ty hbody_val_decomp hbody_true
                  -- hDapp_true : Dapp.fst = zftrue → xy.π₁ ∈ retract = 𝒟.
                  have hπ₁_in_retract : xy.π₁ ∈ retract τ.set denD'.fst := by
                    rw [retract, ZFSet.mem_sep]
                    refine ⟨hx_mem, ?_⟩
                    rw [dif_pos hx_mem, dif_pos denD_val_func]
                    have hWxy_π₁_eq :
                        Wxy.fst.π₁ = (ZFSet.fapply (BType.canonicalIsoSMTType τ).1
                          (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType τ).2.1)
                          ⟨a, by rwa [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType τ).2.1]⟩).1 := by
                      have hζ := (BType.canonicalIsoSMTType τ).2.1
                      have hξ := (BType.canonicalIsoSMTType β).2.1
                      have hfp := ZFSet.fapply_fprod (hf := hζ) (hg := hξ) (a := a) (b := b) ha_mem hb_mem
                      rw [show Wxy.fst = ((ZFSet.fapply (BType.canonicalIsoSMTType τ).1
                              (ZFSet.is_func_is_pfunc hζ)
                              ⟨a, by rwa [ZFSet.is_func_dom_eq hζ]⟩).1).pair
                          ((ZFSet.fapply (BType.canonicalIsoSMTType β).1
                              (ZFSet.is_func_is_pfunc hξ)
                              ⟨b, by rwa [ZFSet.is_func_dom_eq hξ]⟩).1) from by
                        subst hxy_eq; exact hfp, ZFSet.π₁_pair]
                    simp only []
                    have h := hDapp_val ▸ hDapp_true
                    convert h using 4
                    simp [hxy_π₁_eq, hWxy_π₁_eq]
                  rw [denD_val_retract] at hπ₁_in_retract
                  exact absurd hπ₁_in_retract hxy_𝒟
              · intro hmem_sep
                rw [ZFSet.mem_sep, ZFSet.mem_prod] at hmem_sep
                obtain ⟨⟨a', hπ₁_𝒟, b', _, hxy_eq'⟩, _⟩ := hmem_sep
                have hπ₁_eq : xy.π₁ = a' := by simp [hxy_eq']
                exact absurd (hπ₁_eq ▸ hπ₁_𝒟) hxy_𝒟
        · -- Totality clause for alternative valuations.
          -- Delegated to `lambda_chosen_totality` helper which parallels
          -- `collect_case`'s totality branch (for the AND/EQ lambda body and
          -- the pair codomain), matching the pattern of
          -- `lambda_defaults_totality` for the defaults branch.
          -- Context-relationship helpers: St₁ ⊆ St₆ (entries survive).
          have St₁_sub_St₆ : St₁.types ⊆ St₆.types := by
            rw [St₆_types, St₅_types, St₄_types]
            intro ⟨k, τ_k⟩ hk_St₁
            have hk_St₃ := St₁_sub_St₃_types hk_St₁
            have hk_not_vs : k ∉ vs := fun hk_in_vs =>
              vs_disj_St₁ k hk_in_vs (AList.mem_keys.mpr
                (List.mem_map.mpr ⟨⟨k, τ_k⟩, hk_St₁, rfl⟩))
            have hk_ne_z : k ≠ z := by
              intro rfl
              exact z_not_used (St₂_sub_St₃ (St₁_sub_St₂_used (St₁_keys_sub
                (AList.mem_keys.mpr (List.mem_map.mpr ⟨⟨k, τ_k⟩, hk_St₁, rfl⟩)))))
            have hk_ins : ⟨k, τ_k⟩ ∈ (AList.insert z
                (τ.toSMTType.pair β.toSMTType) St₃.types).entries := by
              rw [AList.entries_insert_of_notMem z_fresh, List.mem_cons]
              exact Or.inr hk_St₃
            exact List.mem_kerase_of_ne_key hk_ne_z
              (AList.mem_foldl_erase_of_not_mem_keys hk_ins hk_not_vs)
          have St₁_sub_St₆_used : St₁.env.usedVars ⊆ St₆.env.usedVars := by
            intro v hv
            rw [St₆_used_chain]
            exact List.mem_cons_of_mem _ (St₂_sub_St₃ (St₁_sub_St₂_used hv))
          have St₃_lookup_sub_St₆_P : ∀ v, v ∉ vs → ∀ τ_v,
              AList.lookup v St₃.types = some τ_v →
              AList.lookup v St₆.types = some τ_v := by
            intro v hv_not_vs τ_v h3
            have hv_ne_z : v ≠ z := by
              intro rfl
              have hv_St₃ : v ∈ St₃.types := AList.lookup_isSome.mp (h3 ▸ rfl : (St₃.types.lookup v).isSome = true)
              exact z_fresh hv_St₃
            rw [St₆_types, St₅_types, St₄_types]
            have hentry_St₃ : ⟨v, τ_v⟩ ∈ St₃.types.entries :=
              AList.mem_lookup_iff.1 h3
            have h_ins : ⟨v, τ_v⟩ ∈ (AList.insert z
                (τ.toSMTType.pair β.toSMTType) St₃.types).entries := by
              rw [AList.entries_insert_of_notMem z_fresh]
              exact List.mem_cons_of_mem _ hentry_St₃
            have hentry_St₆ := List.mem_kerase_of_ne_key hv_ne_z
                (AList.mem_foldl_erase_of_not_mem_keys h_ins hv_not_vs)
            exact AList.mem_lookup_iff.2 hentry_St₆
          have St₃_sub_St₆_used : St₃.env.usedVars ⊆ St₆.env.usedVars := by
            intro v hv; rw [St₆_used_chain]
            exact List.mem_cons_of_mem _ hv
          have St₁_dom_sub_St₆ : ∀ v, v ∈ St₁.types → v ∈ St₆.types := by
            intro v hv
            exact AList.mem_of_subset St₁_sub_St₆ hv
          have St₃_dom_sub_St₆ : ∀ v, v ∈ St₃.types → v ∉ vs → v ∈ St₆.types := by
            intro v hv hv_not_vs
            have hv_ne_z : v ≠ z := by
              intro rfl
              exact z_fresh hv
            rw [St₆_types, St₅_types, St₄_types]
            obtain ⟨τ_v, hτ_v⟩ := Option.isSome_iff_exists.mp (AList.lookup_isSome.2 hv)
            have hentry := AList.mem_lookup_iff.1 hτ_v
            have h_ins : ⟨v, τ_v⟩ ∈ (AList.insert z
                (τ.toSMTType.pair β.toSMTType) St₃.types).entries := by
              rw [AList.entries_insert_of_notMem z_fresh]
              exact List.mem_cons_of_mem _ hentry
            exact AList.mem_keys.mpr (List.mem_map.mpr ⟨⟨v, τ_v⟩,
              List.mem_kerase_of_ne_key hv_ne_z
                (AList.mem_foldl_erase_of_not_mem_keys h_ins hv_not_vs), rfl⟩)
          have z_not_fv_D_aux : z ∉ SMT.fv D_enc := by
            intro hz_fv_D
            have hz_St₁ := Typing.mem_context_of_mem_fv typ_D_enc hz_fv_D
            have hz_St₃ : z ∈ St₃.types := AList.mem_of_subset St₁_sub_St₃_types hz_St₁
            exact z_fresh hz_St₃
          have z_not_fv_P_aux : z ∉ SMT.fv P_enc :=
            fun hz => z_fresh (Typing.mem_context_of_mem_fv typ_P_enc hz)
          have z_not_vs_aux : z ∉ vs := fun hz =>
            z_not_used (St₂_sub_St₃ (St₁_sub_St₂_used (used_sub_St₁ (vars_used_vs z hz))))
          -- v ∈ St₆.types ⇒ v ∉ vs (St₆.types = erase z (foldl erase vs (insert z _ St₃)))
          have St₆_not_vs : ∀ v, v ∈ St₆.types → v ∉ vs := by
            intro v hv hvs
            rw [St₆_types, St₅_types] at hv
            have hv_St₅ : v ∈ AList.erase z (List.foldl (fun Γ w => AList.erase w Γ)
                St₄.types vs) := hv
            have hv_foldl := (AList.mem_erase.mp hv_St₅).2
            exact AList.not_mem_foldl_erase_of_mem hvs vs_nodup hv_foldl
          -- Δ'_dom_Γ' : ∀ v, Δ' v ≠ none → v ∈ St₆.types
          have Δ'_dom_Γ' : ∀ v, Δ' v ≠ none → v ∈ St₆.types := by
            intro v hv_ne
            by_cases hvs : v ∈ vs
            · -- v ∈ vs ⇒ Δ' v = Δ_D v ⇒ v ∈ St₁.types ⊆ St₆.types
              have hΔ'_eq : Δ' v = Δ_D v := by rw [Δ'_def]; simp [hvs]
              have hΔ_D_ne : Δ_D v ≠ none := hΔ'_eq ▸ hv_ne
              exact St₁_dom_sub_St₆ v (Δ_D_dom v hΔ_D_ne)
            · -- v ∉ vs ⇒ Δ' v = Δ_P v ⇒ v ∈ St₃.types ⊆ St₆.types
              have hΔ'_eq : Δ' v = Δ_P v := by rw [Δ'_def]; simp [hvs]
              have hΔ_P_ne : Δ_P v ≠ none := hΔ'_eq ▸ hv_ne
              exact St₃_dom_sub_St₆ v (Δ_P_dom v hΔ_P_ne) hvs
          -- Δ'_wt_Γ' : ∀ v d, Δ' v = some d → ∀ τ_v, lookup v St₆.types = some τ_v → d.snd.fst = τ_v
          have Δ'_wt_Γ' : ∀ v (d : SMT.Dom), Δ' v = some d →
              ∀ τ_v, AList.lookup v St₆.types = some τ_v → d.snd.fst = τ_v := by
            intro v d hv τ_v hlookup
            -- v ∈ St₆.types, so v ∉ vs
            have hv_in_St₆ : v ∈ St₆.types :=
              AList.lookup_isSome.mp (hlookup ▸ rfl : (St₆.types.lookup v).isSome = true)
            have hv_not_vs : v ∉ vs := St₆_not_vs v hv_in_St₆
            -- Δ' v = Δ_P v
            have hΔ'_eq : Δ' v = Δ_P v := by rw [Δ'_def]; simp [hv_not_vs]
            have hd_P : Δ_P v = some d := hΔ'_eq ▸ hv
            -- lookup v St₃.types = some τ_v via St₆_sub_St₃
            have hlookup_St₃ : AList.lookup v St₃.types = some τ_v :=
              AList.mem_lookup_iff.2 (St₆_sub_St₃ (AList.mem_lookup_iff.1 hlookup))
            exact Δ_P_wt v d hd_P τ_v hlookup_St₃
          have vs_used_St₃ : ∀ v ∈ vs, v ∈ St₃.env.usedVars :=
            fun v hv => St₂_sub_St₃ (St₁_sub_St₂_used (used_sub_St₁ (vars_used_vs v hv)))
          have vs_lookup_St₃ : ∀ (i : Fin vs.length),
              AList.lookup vs[i] St₃.types = some
                ((τ.toSMTType.fromProdl (vs.length - 1))[i]'(by
                  rw [fromProdl_length_of_hasArity τ_hasArity]; exact i.2)) := by
            intro ⟨i, hi⟩
            set τs := τ.toSMTType.fromProdl (vs.length - 1) with τs_def
            have τs_len : τs.length = vs.length := fromProdl_length_of_hasArity τ_hasArity
            have hi_τs : i < τs.length := τs_len ▸ hi
            have h_St₂_lookup : St₂.types.lookup vs[i] = some τs[i] := by
              rw [St₂_types]; exact foldl_insert_lookup_zip vs_nodup hi hi_τs
            exact AList.mem_lookup_iff.2
              (St₂_sub_St₃_types (AList.mem_lookup_iff.1 h_St₂_lookup))
          have vs_disj_St₆ : ∀ v ∈ vs, v ∉ St₆.types := fun v hv h_in =>
            St₆_not_vs v h_in hv
          have z_not_St₆ : z ∉ St₆.types := by
            rw [St₆_types]
            intro h_erase
            exact (AList.mem_erase.mp h_erase).1 rfl
          exact lambda_chosen_totality (D := D) (P := P) (D_enc := D_enc)
            (P_enc := P_enc) (z := z) (vs := vs) (τ := τ) (β := β)
            (αs := αs) (E_ctx := E.context)
            (Δ' := Δ') (denT' := denT')
            (Γ_D := St₁.types) (used_D := St₁.env.usedVars)
            (Γ_P := St₃.types) (used_P := St₃.env.usedVars)
            (Γ' := St₆.types) (used' := St₆.env.usedVars)
            vs_nemp vs_nodup rfl typ_t typ_D typP typ_D_enc typ_P_enc
            τ_hasArity vs_not_D_fv vs_disj_St₁ vs_disj_St₆ vs_used_St₃ vs_lookup_St₃
            z_fresh z_not_St₆ z_not_used
            z_not_fv_D_aux z_not_fv_P_aux z_not_vs_aux
            hcov_lambda hden_eq hden_ty Δ'_none_out Δ'_dom_Γ' Δ'_wt_Γ'
            D_RDom.2 P_enc_total
            (fun _ _ h => AList.lookup_of_subset St₁_sub_St₆ h)
            (fun _ _ h => AList.lookup_of_subset St₁_sub_St₃_types h)
            (fun _ _ h => AList.lookup_of_subset St₆_sub_St₃ h)
            St₁_sub_St₆_used
            St₃_lookup_sub_St₆_P
            St₃_sub_St₆_used
            covers_D
            covers_P
            St₁_dom_sub_St₆
            St₃_dom_sub_St₆
            (fv_sub_typings typ_t h_typ_St₆)
            (fun v hv => St₂_sub_St₃ (St₁_sub_St₂_used hv))
  · -- Defaults branch: 𝒟' = ∅, valuation uses τ.defaultZFSet.get.
    -- Define f/Δ_ext using defaults.
    let f : Fin vs.length → B.Dom := fun i =>
      ⟨τ.defaultZFSet.get vs.length i, τ.get vs.length i,
       get_mem_type_of_isTuple h_default_arity.1 h_default_arity.2
         BType.mem_toZFSet_of_defaultZFSet⟩
    set Δ_ext : B.RenamingContext.Context :=
      Function.updates «Δ» vs (List.ofFn fun i => some (f i)) with Δ_ext_def
    have Δ_fv_P : ∀ v ∈ B.fv P, (Δ_ext v).isSome := by
      intro v hv
      rw [Δ_ext_def, Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup]
      split_ifs with hvs
      · simp only [List.getElem_ofFn, Option.isSome_some]
      · exact Δ_fv v (fv.mem_lambda (.inr ⟨hv, hvs⟩))
    set Δ_D_ext : SMT.RenamingContext.Context :=
      Function.updates Δ_D vs
        (List.ofFn fun (i : Fin vs.length) => B.RenamingContext.toSMT Δ_ext vs[i])
      with Δ_D_ext_def
    have Δ_D_ext_none_St₂ : ∀ v ∉ St₂.env.usedVars, Δ_D_ext v = none :=
      Δ_D_ext_none_helper_shared (ΔDD := Δ_D) (ΔDDext := Δ_D_ext)
        (vs := vs) (vs_nodup := vs_nodup)
        (vs_τs_len := by rw [fromProdl_length_of_hasArity τ_hasArity])
        (used0 := St₁.env.usedVars) (used1 := St₁.env.usedVars)
        (used2 := St₂.env.usedVars)
        (St_used_def := St₂_used) (used1_eq_used0 := rfl)
        (ΔDDext_def := Δ_D_ext_def) (ΔDD_none_outside := Δ_D_none_St₂)
    have Δ₀_ext_P : RenamingContext.ExtendsOnSourceFV Δ_D_ext Δ_ext P :=
      Δ₀_ext_P_helper_shared vs_nodup Δ_ext_def Δ_D_ext_def (Term.lambda vs D P) P
        (mem_binder := fun hv hvs => fv.mem_lambda (.inr ⟨hv, hvs⟩))
        (lift := fun hv => Δ_D_extends (Δ₀_ext hv))
    -- Now extract den_P from rest_lambda using denote_term_abstract_go_eq_term_abstract.
    rw [denote_term_abstract_go_eq_term_abstract vs_nodup vs_nemp f Δ_fv_P,
        Option.bind_eq_some_iff] at rest_lambda
    obtain ⟨⟨P_val, P_typ, P_mem_typ⟩, den_P, P_eq⟩ := rest_lambda
    -- P_eq : pure ⟨∅, ⟨(τ ×ᴮ P_typ).set, ⋯⟩⟩ = some ⟨T, ⟨(τ ×ᴮ β).set, hT⟩⟩
    simp only [Option.pure_def, Option.some.injEq] at P_eq
    obtain ⟨rfl, _⟩ := P_eq
    -- Step: Prepare to invoke P_ih.
    have vars_used_P_St₂ : ∀ v ∈ P.vars, v ∈ St₂.env.usedVars :=
      fun v hv => St₁_sub_St₂_used (used_sub_St₁ (vars_used_P v hv))
    have St₂_types_sub_E_ctx_on_P_vars : ∀ v ∈ P.vars, v ∈ St₂.types → v ∈ E'.context := by
      intro v v_in_P_vars v_in_St₂_types
      simp [E']
      by_cases v_in_vs : v ∈ vs
      · left
        exact AList.mem_zipToAList_of_mem vs_nodup vs_αs_len v_in_vs
      · right
        have v_in_St₁ : v ∈ St₁.types := by
          rw [St₂_types] at v_in_St₂_types
          exact AList.mem_of_mem_foldl_insert' v_in_St₂_types (by
            intro h
            rw [List.mem_map] at h
            obtain ⟨⟨a, b⟩, hab, rfl⟩ := h
            exact v_in_vs (List.of_mem_zip hab).1)
        have v_used : v ∈ used := vars_used_P v v_in_P_vars
        by_cases v_St₀ : v ∈ St₀.types
        · have v_lambda : v ∈ (Term.lambda vs D P).vars := by
            unfold B.Term.vars at v_in_P_vars ⊢
            rw [List.mem_union_iff]
            rcases List.mem_union_iff.mp v_in_P_vars with h_fv | h_bv
            · left; simp only [B.fv, List.mem_append]
              right
              unfold List.removeAll; rw [List.mem_filter]
              exact ⟨h_fv, by simp [v_in_vs]⟩
            · right; simp only [B.bv, List.mem_append]
              right; exact h_bv
          exact Λ_inv v v_lambda v_St₀
        · have v_fv_D : v ∈ B.fv D := by
            by_contra h
            exact absurd v_in_St₁ (D_preserves_types v v_used v_St₀ h)
          exact AList.lookup_isSome.mp (B.Typing.mem_context_of_mem_fv typ_D v_fv_D)
    -- Apply P_ih
    mspec P_ih (E := E') (Λ := St₂.types) (α := β) typP
      («Δ» := Δ_ext) Δ_fv_P
      (Δ₀ := Δ_D_ext) Δ₀_ext_P (used := St₂.env.usedVars) Δ_D_ext_none_St₂
      (T := P_val) (hT := P_mem_typ) den_P vars_used_P_St₂ (n := St₂.env.freshvarsc)
      St₂_types_sub_E_ctx_on_P_vars
    clear P_ih
    rename_i out_P
    obtain ⟨P_enc, σP⟩ := out_P
    mrename_i pre
    mintro ∀St₃
    mpure pre
    obtain ⟨St₂_sub_St₃, St₂_sub_St₃_types, St₃_keys_sub, covers_P, rfl, typ_P_enc,
      P_preserves_types,
      Δ_P, Δ_P_covers, Δ_P_extends, Δ_P_src_ext, Δ_P_none, denP', den_P_enc, P_RDom,
      P_enc_total⟩ := pre
    have Δ_P_wt : ∀ v (d : SMT.Dom), Δ_P v = some d →
        ∀ τ_v, St₃.types.lookup v = some τ_v → d.snd.fst = τ_v :=
      SMT.RenamingContext.ExtendsOnSourceFV.wt Δ_P_src_ext typ_P_enc
    have Δ_P_dom : ∀ v, Δ_P v ≠ none → v ∈ St₃.types := fun v hv =>
      fv_sub_typings typP typ_P_enc v
        (SMT.RenamingContext.ExtendsOnSourceFV.dom_sub_B_fv Δ_P_src_ext v hv)
    -- Fresh variable z for the lambda binding
    mspec freshVar_spec
    rename_i z
    mrename_i pre
    mintro ∀St₄
    mpure pre
    obtain ⟨St₄_types, z_fresh, St₄_fvc, St₄_used, z_not_used⟩ := pre
    -- Erase vs, then erase z
    mspec SMT.eraseVars_forIn_spec (vars := vs)
    mrename_i pre_erase_vs
    mintro ∀St₅
    mpure pre_erase_vs
    obtain ⟨St₅_types, St₅_fvc, St₅_used⟩ := pre_erase_vs
    mspec SMT.eraseFromContext_spec
    mrename_i pre_erase_z
    mintro ∀St₆
    mpure pre_erase_z
    obtain ⟨St₆_types, St₆_fvc, St₆_used⟩ := pre_erase_z
    mspec Std.Do.Spec.pure
    mpure_intro
    -- Bridge facts: chain usedVars through erasure states
    have St₆_used_chain : St₆.env.usedVars = z :: St₃.env.usedVars := by
      rw [St₆_used, St₅_used, St₄_used]
    have z_not_St₀ : z ∉ St₀.types := by
      intro hz
      have := St₀_sub hz
      rw [St₀_used_eq] at this
      exact z_not_used (St₂_sub_St₃ (St₁_sub_St₂_used (used_sub_St₁ this)))
    have vs_not_D_fv : ∀ v ∈ vs, v ∉ B.fv D := by
      intro v hv hv_fv
      nomatch vs_Γ_disj v hv <| AList.lookup_isSome.mp <|
        B.Typing.mem_context_of_mem_fv typ_D hv_fv
    have vs_disj_St₁ : ∀ v ∈ vs, v ∉ St₁.types := by
      intro v hv
      apply D_preserves_types v (vars_used_vs v hv) _ (vs_not_D_fv v hv)
      intro hv_St₀
      have hv_lambda : v ∈ (Term.lambda vs D P).vars := by
        unfold B.Term.vars; rw [List.mem_union_iff]; right
        simp only [B.bv, List.mem_append]; left; left; exact hv
      exact vs_Γ_disj v hv (Λ_inv v hv_lambda hv_St₀)
    have St₁_sub_St₃_types : St₁.types ⊆ St₃.types := by
      apply AList.subset_trans _ St₂_sub_St₃_types
      rw [St₂_types]
      apply AList.subset_foldl_insert'
      · intro ⟨v, ξ⟩ hv
        exact vs_disj_St₁ v (List.mem_fst_of_mem_zip hv)
      · exact List.nodup_map_fst_of_nodup_zip vs_nodup
    have St₆_sub_St₃ : St₆.types ⊆ St₃.types := by
      rw [St₆_types, St₅_types, St₄_types]
      intro ⟨k, v⟩ hkv
      have hk_ne_z : k ≠ z := AList.fst_ne_of_mem_erase_entries hkv
      have hkv_foldl := AList.erase_entries_subset z _ hkv
      have hkv_ins := AList.foldl_erase_entries_subset vs _ hkv_foldl
      rw [AList.entries_insert_of_notMem z_fresh] at hkv_ins
      exact (List.mem_cons.mp hkv_ins).elim
        (fun h => absurd (congrArg Sigma.fst h) hk_ne_z) id
    -- Extract typing proof so it's reusable in conjuncts 6 and 8.
    have h_typ_St₆ : St₆.types ⊢ˢ
        (SMT.Term.lambda [z] [τ.toSMTType.pair β.toSMTType]
          (SMT.Term.and
            (SMT.Term.app D_enc (SMT.Term.fst (.var z)))
            (SMT.Term.eq (SMT.Term.snd (.var z))
              (SMT.substList vs (toDestPair vs (SMT.Term.fst (.var z))) P_enc)))) :
        SMTType.fun (τ.toSMTType.pair β.toSMTType) .bool := by
      have hupdate : SMT.TypeContext.update St₃.types [z] [τ.toSMTType.pair β.toSMTType] rfl =
          St₃.types.insert z (τ.toSMTType.pair β.toSMTType) := by
        simp only [SMT.TypeContext.update, List.length_cons, List.length_nil, zero_add,
          Nat.reduceAdd, Fin.cast_eq_self, Fin.getElem_fin, Fin.val_eq_zero,
          List.getElem_cons_zero, Fin.foldl_succ, Fin.foldl_zero]
      have h_St₁_sub_St₃ := St₁_sub_St₃_types
      suffices h_typ_St₃ : St₃.types ⊢ˢ
          (SMT.Term.lambda [z] [τ.toSMTType.pair β.toSMTType]
            (SMT.Term.and
              (SMT.Term.app D_enc (SMT.Term.fst (.var z)))
              (SMT.Term.eq (SMT.Term.snd (.var z))
                (SMT.substList vs (toDestPair vs (SMT.Term.fst (.var z))) P_enc)))) :
          SMTType.fun (τ.toSMTType.pair β.toSMTType) .bool from
        Typing.strengthening_of_fv_subset St₆_sub_St₃ h_typ_St₃ (by
          have h_surv : ∀ v, v ∈ St₃.types → v ∉ vs → v ≠ z → v ∈ St₆.types := by
            intro v hv_St₃ hv_not_vs hv_ne_z
            rw [St₆_types, St₅_types, St₄_types]
            obtain ⟨τ_v, hτ_v⟩ := Option.isSome_iff_exists.mp (AList.lookup_isSome.2 hv_St₃)
            have hentry := AList.mem_lookup_iff.1 hτ_v
            have h_ins : ⟨v, τ_v⟩ ∈ (AList.insert z (τ.toSMTType.pair β.toSMTType)
                St₃.types).entries := by
              rw [AList.entries_insert_of_notMem z_fresh]
              exact List.mem_cons_of_mem _ hentry
            exact AList.mem_keys.mpr (List.mem_map.mpr ⟨⟨v, τ_v⟩,
              List.mem_kerase_of_ne_key hv_ne_z
                (AList.mem_foldl_erase_of_not_mem_keys h_ins hv_not_vs), rfl⟩)
          intro v hv_lam
          simp only [SMT.fv] at hv_lam
          unfold List.removeAll at hv_lam
          rw [List.mem_filter] at hv_lam
          obtain ⟨hv_body, hv_nz⟩ := hv_lam
          have hv_ne_z : v ≠ z := by simpa using hv_nz
          simp only [List.mem_append] at hv_body
          rcases hv_body with (hv_D | hv_z1) | (hv_z2 | hv_subst)
          · have hv_St₁ : v ∈ St₁.types :=
              Typing.mem_context_of_mem_fv typ_D_enc hv_D
            exact h_surv v (typeContext_mem_of_subset h_St₁_sub_St₃ hv_St₁)
              (fun hvs => vs_disj_St₁ v hvs hv_St₁) hv_ne_z
          · rw [List.mem_singleton] at hv_z1
            exact absurd hv_z1 hv_ne_z
          · rw [List.mem_singleton] at hv_z2
            exact absurd hv_z2 hv_ne_z
          · rcases SMT_mem_fv_substList hv_subst with hv_P | ⟨t, ht, hv_t⟩
            · have hv_St₃ := Typing.mem_context_of_mem_fv typ_P_enc hv_P
              have hv_not_vs : v ∉ vs := by
                intro hvs
                suffices hlen : vs.length ≤ (toDestPair vs (SMT.Term.fst (.var z))).length by
                  have hts : ∀ t ∈ toDestPair vs (SMT.Term.fst (.var z)), v ∉ SMT.fv t := by
                    intro t ht hv_t
                    have := SMT_fv_toDestPair_subset_base (v := v) (z := z)
                      (t₀ := SMT.Term.fst (.var z))
                      (by intro w hw; simp only [SMT.fv, List.mem_singleton] at hw; exact hw)
                      ht hv_t
                    exact hv_ne_z this
                  exact absurd hv_subst (SMT_not_mem_fv_substList_of_mem_vars hlen hvs hts)
                suffices ∀ (ws : List SMT.𝒱) (zp : SMT.Term) (acc : List SMT.Term)
                    (d : SMT.Term),
                    ws.length + acc.length ≤ (toDestPair ws zp acc d).length by
                  simpa using this vs (SMT.Term.fst (.var z)) [] (SMT.Term.fst (.var z))
                intro ws
                induction ws with
                | nil => intro _ acc _; simp [toDestPair]
                | cons w ws' ih =>
                  intro zp acc d
                  cases ws' with
                  | nil => simp [toDestPair]; omega
                  | cons w' ws'' =>
                    simp only [toDestPair]
                    have := ih (.fst d) (.snd d :: acc) (.fst d)
                    simp [List.length] at this ⊢; omega
              exact h_surv v hv_St₃ hv_not_vs hv_ne_z
            · have := SMT_fv_toDestPair_subset_base (v := v) (z := z)
                (t₀ := SMT.Term.fst (.var z))
                (by intro w hw; simp only [SMT.fv, List.mem_singleton] at hw; exact hw)
                ht hv_t
              exact absurd this hv_ne_z)
      refine SMT.Typing.lambda St₃.types [z] [τ.toSMTType.pair β.toSMTType] _ .bool ?_ ?_ ?_ ?_ ?_
      · intro v hv; rw [List.mem_singleton] at hv; subst hv; exact z_fresh
      · intro v hv; simp only [List.mem_singleton] at hv; subst hv
        simp only [SMT.bv, List.append_nil, List.nil_append, List.mem_append, not_or]
        refine ⟨?_, ?_⟩
        · intro hbv
          have typ_D_enc_St₃ := SMT.Typing.weakening
            (SMT.TypeContext.entries_subset_insert_of_notMem
              (τ := τ.toSMTType.pair β.toSMTType) z_fresh)
            (SMT.Typing.weakening h_St₁_sub_St₃ typ_D_enc)
          exact SMT.Typing.bv_notMem_context typ_D_enc_St₃ _ hbv
            ((AList.mem_insert _).mpr (Or.inl rfl))
        · intro hbv
          have hbv_P := SMT_bv_substList_subset
            (fun t ht => toDestPair_bv_nil_base (by simp [SMT.bv]) t ht) _ hbv
          have typ_P_enc_ins := SMT.Typing.weakening
            (SMT.TypeContext.entries_subset_insert_of_notMem
              (τ := τ.toSMTType.pair β.toSMTType) z_fresh) typ_P_enc
          exact SMT.Typing.bv_notMem_context typ_P_enc_ins _ hbv_P
            ((AList.mem_insert _).mpr (Or.inl rfl))
      · exact Nat.zero_lt_succ 0
      · rfl
      · rw [hupdate]
        have h_ins := SMT.TypeContext.entries_subset_insert_of_notMem
          (v := z) (τ := τ.toSMTType.pair β.toSMTType) z_fresh
        refine SMT.Typing.and _ _ _ ?_ ?_
        · exact SMT.Typing.app _ _ _ _ _
            (SMT.Typing.weakening h_ins
              (SMT.Typing.weakening h_St₁_sub_St₃ typ_D_enc))
            (SMT.Typing.fst _ _ _ _
              (SMT.Typing.var _ z (τ.toSMTType.pair β.toSMTType)
                (AList.lookup_insert St₃.types)))
        · refine SMT.Typing.eq _ _ _ β.toSMTType ?_ ?_
          · exact SMT.Typing.snd _ _ _ _
              (SMT.Typing.var _ z (τ.toSMTType.pair β.toSMTType)
                (AList.lookup_insert St₃.types))
          · apply SMT_Typing_substList
            · exact SMT.Typing.weakening h_ins typ_P_enc
            · exact toDestPair_bv_nil_base (by simp [SMT.bv])
            · set Γ_z := St₃.types.insert z (τ.toSMTType.pair β.toSMTType) with Γ_z_def
              set τs := τ.toSMTType.fromProdl (vs.length - 1) with τs_def
              have τs_len : τs.length = vs.length := fromProdl_length_of_hasArity τ_hasArity
              intro i hi_x hi_t hx
              have hi_τs : i < τs.length := τs_len ▸ hi_x
              have h_St₂_lookup : St₂.types.lookup vs[i] = some τs[i] := by
                rw [St₂_types]; exact foldl_insert_lookup_zip vs_nodup hi_x hi_τs
              have h_St₃_lookup : St₃.types.lookup vs[i] = some τs[i] :=
                AList.mem_lookup_iff.2
                  (St₂_sub_St₃_types (AList.mem_lookup_iff.1 h_St₂_lookup))
              have hne : vs[i] ≠ z := by
                intro heq
                have hvi_used : vs[i] ∈ St₃.env.usedVars :=
                  St₂_sub_St₃
                    (St₁_sub_St₂_used
                      (used_sub_St₁ (vars_used_vs vs[i] (List.getElem_mem hi_x))))
                exact z_not_used (heq ▸ hvi_used)
              have h_lookup : Γ_z.lookup vs[i] = some τs[i] := by
                rw [Γ_z_def, AList.lookup_insert_ne hne]; exact h_St₃_lookup
              have h_get : (Γ_z.lookup vs[i]).get hx = τs[i] := by simp [h_lookup]
              rw [h_get]
              have hz_lookup : Γ_z.lookup z = some (τ.toSMTType.pair β.toSMTType) :=
                AList.lookup_insert St₃.types
              have h_z_var : Γ_z ⊢ˢ SMT.Term.var z : τ.toSMTType.pair β.toSMTType :=
                SMT.Typing.var Γ_z z _ hz_lookup
              have h_z_fst : Γ_z ⊢ˢ SMT.Term.fst (.var z) : τ.toSMTType :=
                SMT.Typing.fst _ _ _ _ h_z_var
              have h_result := toDestPair_typing_gen Γ_z vs
                (SMT.Term.fst (.var z)) (SMT.Term.fst (.var z))
                τ.toSMTType [] []
                vs_nemp rfl h_z_fst
                (by rw [τs_def] at τs_len; exact τs_len) rfl
                (fun j hj => absurd hj (Nat.not_lt_zero j))
                i τs[i]
                (by simp only [List.append_nil]; rw [List.getElem?_eq_getElem hi_τs])
              obtain ⟨hj, htyp⟩ := h_result
              exact htyp
    refine ⟨?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_⟩
    · -- 1. used ⊆ St₆.env.usedVars
      rw [St₆_used_chain]
      exact fun v hv => List.mem_cons_of_mem _
        (St₂_sub_St₃ (St₁_sub_St₂_used (used_sub_St₁ hv)))
    · -- 2. St₀.types ⊆ St₆.types
      intro ⟨k, τ_k⟩ hk_St₀
      rw [St₆_types, St₅_types, St₄_types]
      have hk_not_vs : k ∉ vs := by
        intro hk_in_vs
        have hk_St₀_mem : k ∈ St₀.types :=
          AList.mem_keys.mpr (List.mem_map.mpr ⟨⟨k, τ_k⟩, hk_St₀, rfl⟩)
        have hk_lambda : k ∈ (Term.lambda vs D P).vars := by
          unfold B.Term.vars; rw [List.mem_union_iff]; right
          simp only [B.bv, List.mem_append]; left; left; exact hk_in_vs
        exact vs_Γ_disj k hk_in_vs (Λ_inv k hk_lambda hk_St₀_mem)
      have hk_ne_z : k ≠ z := by
        intro rfl
        have : k ∈ St₀.types :=
          AList.mem_keys.mpr (List.mem_map.mpr ⟨⟨k, τ_k⟩, hk_St₀, rfl⟩)
        nomatch z_not_St₀ this
      have hk_St₃_kerase :
          ⟨k, τ_k⟩ ∈ (AList.insert z (τ.toSMTType.pair β.toSMTType) St₃.types).entries := by
        rw [AList.entries_insert_of_notMem z_fresh, List.mem_cons]
        right
        exact St₁_sub_St₃_types (St₀_sub_St₁ hk_St₀)
      have hk_foldl := AList.mem_foldl_erase_of_not_mem_keys hk_St₃_kerase hk_not_vs
      exact List.mem_kerase_of_ne_key hk_ne_z hk_foldl
    · -- 3. AList.keys St₆.types ⊆ St₆.env.usedVars
      rw [St₆_used_chain]
      intro v hv
      apply List.mem_cons_of_mem
      have hv_St₃ : v ∈ St₃.types :=
        (List.map_subset _ St₆_sub_St₃) hv
      exact St₃_keys_sub hv_St₃
    · -- 4. CoversUsedVars St₆.env.usedVars (lambda vs D P)
      rw [St₆_used_chain]
      intro v hv
      apply List.mem_cons_of_mem
      rw [B.fv, List.mem_append] at hv
      rcases hv with hv_D | hv_P
      · exact St₂_sub_St₃ (St₁_sub_St₂_used (covers_D v hv_D))
      · exact covers_P v (List.mem_filter.mp hv_P).1
    · -- 6. typing of the lambda term (extracted as h_typ_St₆)
      exact h_typ_St₆
    · -- 7. preserves types
      intro v v_used v_notMem_St₀ v_notMem_vars v_mem_St₆
      simp only [B.fv, List.mem_append, not_or] at v_notMem_vars
      have v_notMem_fvD := v_notMem_vars.1
      have v_mem_St₃ : v ∈ St₃.types :=
        typeContext_mem_of_subset St₆_sub_St₃ v_mem_St₆
      have hv_not_vs : v ∉ vs := by
        intro hv_vs
        have : v ∉ St₆.types := by
          rw [St₆_types]; intro h_erase_z
          have h_in_St₅ : v ∈ St₅.types := (AList.mem_erase.mp h_erase_z).2
          rw [St₅_types] at h_in_St₅
          exact absurd h_in_St₅ (AList.not_mem_foldl_erase_of_mem hv_vs vs_nodup)
        exact this v_mem_St₆
      have v_notMem_fvP : v ∉ B.fv P := by
        intro hv_fvP
        apply v_notMem_vars.2
        unfold List.removeAll; rw [List.mem_filter]
        exact ⟨hv_fvP, by simp [hv_not_vs]⟩
      exfalso
      have v_notMem_St₁ := D_preserves_types v v_used v_notMem_St₀ v_notMem_fvD
      have v_notMem_St₂ : v ∉ St₂.types := by
        rw [St₂_types]; intro h
        exact v_notMem_St₁ (AList.mem_of_mem_foldl_insert' h (by
          intro hmem; rw [List.mem_map] at hmem
          obtain ⟨⟨a, b⟩, hab, rfl⟩ := hmem
          exact hv_not_vs (List.of_mem_zip hab).1))
      exact P_preserves_types v (St₁_sub_St₂_used (used_sub_St₁ v_used))
        v_notMem_St₂ v_notMem_fvP v_mem_St₃
    · -- 8. existential block: define Δ' using Δ_D for vs, else Δ_P
      set Δ' : SMT.RenamingContext.Context := fun v =>
        if v ∈ vs then Δ_D v else Δ_P v with Δ'_def
      have Δ'_extends_Δ₀ : RenamingContext.Extends Δ' Δ₀ := by
        intro v d hv_eq
        rw [Δ'_def]
        by_cases hvs : v ∈ vs
        · simp [hvs]; exact Δ_D_extends hv_eq
        · simp [hvs]
          have hDD : Δ_D_ext v = Δ_D v := by
            rw [Δ_D_ext_def]; exact Function.updates_of_not_mem Δ_D vs _ v hvs
          exact Δ_P_extends (hDD ▸ Δ_D_extends hv_eq)
      have Δ'_none_out : ∀ v ∉ St₆.env.usedVars, Δ' v = none := by
        intro v hv_out
        rw [St₆_used_chain, List.mem_cons, not_or] at hv_out
        obtain ⟨hv_ne_z, hv_not_St₃⟩ := hv_out
        rw [Δ'_def]
        by_cases hvs : v ∈ vs
        · exfalso; apply hv_not_St₃
          -- v ∈ vs means v ∈ St₂.env.usedVars ⊆ St₃.env.usedVars
          have v_in_St₂ : v ∈ St₂.env.usedVars := by
            rw [St₂_used]
            suffices ∀ (ws : List SMT.𝒱) (τs' : List SMTType) (acc : List SMT.𝒱),
                ws.length ≤ τs'.length → v ∈ ws →
                v ∈ (ws.zip τs').foldl (fun used p => p.1 :: used) acc by
              exact this vs (τ.toSMTType.fromProdl (vs.length - 1)) St₁.env.usedVars
                (by rw [fromProdl_length_of_hasArity τ_hasArity]) hvs
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
          exact St₂_sub_St₃ v_in_St₂
        · simp [hvs]; exact Δ_P_none v hv_not_St₃
      have hcov_lambda : RenamingContext.CoversFV Δ'
          ((λˢ [z]) [τ.toSMTType.pair β.toSMTType]
            ((@ˢD_enc) (SMT.Term.var z).fst ∧ˢ
              ((SMT.Term.var z).snd =ˢ
                SMT.substList vs (toDestPair vs (SMT.Term.var z).fst) P_enc))) := by
        intro v hv
        simp only [SMT.fv, List.mem_removeAll_iff] at hv
        obtain ⟨hv_body, hv_ne_z⟩ := hv
        have hv_ne : v ≠ z := List.mem_singleton.not.mp hv_ne_z
        simp only [List.mem_append, List.mem_singleton] at hv_body
        rcases hv_body with ((hv_D | hv_z1) | (hv_z2 | hv_subst))
        · -- v ∈ fv D_enc
          rw [Δ'_def]
          by_cases hvs : v ∈ vs
          · simp [hvs]; exact Δ_D_covers v hv_D
          · simp [hvs]
            have hDD_ext : Δ_D_ext v = Δ_D v := by
              rw [Δ_D_ext_def]; exact Function.updates_of_not_mem Δ_D vs _ v hvs
            have ⟨d, hd⟩ := Option.isSome_iff_exists.mp (Δ_D_covers v hv_D)
            exact Option.isSome_iff_exists.mpr ⟨d, Δ_P_extends (hDD_ext ▸ hd)⟩
        · -- v = z: contradicts hv_ne
          exact absurd hv_z1 hv_ne
        · -- v = z: contradicts hv_ne
          exact absurd hv_z2 hv_ne
        · -- v ∈ fv(substList ...)
          rcases SMT_mem_fv_substList hv_subst with hv_P | ⟨t, ht, hv_t⟩
          · have hv_not_vs : v ∉ vs := by
              intro hvs
              suffices hlen : vs.length ≤ (toDestPair vs (SMT.Term.fst (.var z))).length by
                have hts : ∀ t ∈ toDestPair vs (SMT.Term.fst (.var z)), v ∉ SMT.fv t := by
                  intro t ht hv_t
                  exact hv_ne
                    (SMT_fv_toDestPair_subset_base (t₀ := .fst (.var z))
                      (by intro w hw; simp only [SMT.fv, List.mem_singleton] at hw; exact hw)
                      ht hv_t)
                exact absurd hv_subst (SMT_not_mem_fv_substList_of_mem_vars hlen hvs hts)
              suffices ∀ (ws : List SMT.𝒱) (zp : SMT.Term) (acc : List SMT.Term)
                  (d : SMT.Term),
                  ws.length + acc.length ≤ (toDestPair ws zp acc d).length by
                simpa using this vs (SMT.Term.fst (.var z)) [] (SMT.Term.fst (.var z))
              intro ws
              induction ws with
              | nil => intro _ acc _; simp [toDestPair]
              | cons w ws' ih =>
                intro zp acc d
                cases ws' with
                | nil => simp [toDestPair]; omega
                | cons w' ws'' =>
                  simp only [toDestPair]
                  have := ih (.fst d) (.snd d :: acc) (.fst d)
                  simp [List.length] at this ⊢; omega
            rw [Δ'_def]; simp [hv_not_vs]
            exact Δ_P_covers v hv_P
          · have := SMT_fv_toDestPair_subset_base (t₀ := .fst (.var z))
              (by intro w hw; simp only [SMT.fv, List.mem_singleton] at hw; exact hw)
              ht hv_t
            exact absurd this hv_ne
      refine ⟨Δ', hcov_lambda, Δ'_extends_Δ₀, ?_, Δ'_none_out, ?_⟩
      · exact RenamingContext.extendsOnSourceFV_of_extends Δ'_extends_Δ₀ Δ₀_ext
      · -- ∃ denT', ... ≘ᶻ ... ∧ totality. We split into the three components:
        -- (a) existence of denT' and that the SMT lambda denotes to it,
        -- (b) ⟨∅, ⟨(τ ×ᴮ β).set, _⟩⟩ ≘ᶻ denT' (RDom), and
        -- (c) totality for alternative valuations.
        -- In the defaults (𝒟 = ∅) branch, the SMT lambda denotes to the empty
        -- relation on (τ × β), which matches the empty set on the B side.
        -- (a) existence of denT' with denotation equation via
        -- `denote_exists_of_typing_fv` using h_typ_St₆.
        have hcompat : SMT.RenamingContext.RespectsTypeContextOnFV Δ' St₆.types
            ((λˢ [z]) [τ.toSMTType.pair β.toSMTType]
              ((@ˢD_enc) (SMT.Term.var z).fst ∧ˢ
                ((SMT.Term.var z).snd =ˢ
                  SMT.substList vs (toDestPair vs (SMT.Term.var z).fst) P_enc))) := by
          intro v τ_v hv_fv hlookup
          -- v ∈ fv(lambda) → Δ' v is some (via hcov_lambda)
          have hcov_v := hcov_lambda v hv_fv
          obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hcov_v
          refine ⟨d, hd, ?_⟩
          -- Show d.2.1 = τ_v: use Δ_P_wt after showing Δ' v = Δ_P v (i.e., v ∉ vs)
          -- v ∈ fv(lambda) means v ≠ z (it's removed by binding)
          have hv_ne_z : v ≠ z := by
            simp only [SMT.fv, List.mem_removeAll_iff] at hv_fv
            intro rfl
            exact hv_fv.2 (List.mem_singleton.mpr rfl)
          -- v ∉ vs: follows from the fv-analysis below
          have hv_not_vs : v ∉ vs := by
            simp only [SMT.fv, List.mem_removeAll_iff] at hv_fv
            obtain ⟨hv_body, _⟩ := hv_fv
            simp only [List.mem_append] at hv_body
            rcases hv_body with (hv_D | hv_z1) | (hv_z2 | hv_subst)
            · -- v ∈ fv D_enc: v ∈ St₁.types, disjoint from vs
              intro hvs
              exact vs_disj_St₁ v hvs (Typing.mem_context_of_mem_fv typ_D_enc hv_D)
            · simp only [List.mem_singleton] at hv_z1
              exact absurd hv_z1 hv_ne_z
            · simp only [List.mem_singleton] at hv_z2
              exact absurd hv_z2 hv_ne_z
            · -- v ∈ fv(substList ...): either v ∈ fv(P_enc) \ vs or v ∈ fv(destruct) ⊆ {z}
              intro hvs
              rcases SMT_mem_fv_substList hv_subst with hv_P | ⟨t, ht, hv_t⟩
              · -- v ∈ fv(P_enc) ∧ v ∈ vs: contradiction via SMT_not_mem_fv_substList_of_mem_vars
                suffices hlen : vs.length ≤ (toDestPair vs (SMT.Term.fst (.var z))).length by
                  have hts : ∀ t ∈ toDestPair vs (SMT.Term.fst (.var z)), v ∉ SMT.fv t := by
                    intro t ht hv_t
                    have hvz := SMT_fv_toDestPair_subset_base (v := v) (z := z)
                      (t₀ := SMT.Term.fst (.var z))
                      (by intro w hw; simp only [SMT.fv, List.mem_singleton] at hw; exact hw)
                      ht hv_t
                    exact hv_ne_z hvz
                  exact absurd hv_subst
                    (SMT_not_mem_fv_substList_of_mem_vars hlen hvs hts)
                suffices ∀ (ws : List SMT.𝒱) (zp : SMT.Term) (acc : List SMT.Term)
                    (d' : SMT.Term),
                    ws.length + acc.length ≤ (toDestPair ws zp acc d').length by
                  simpa using this vs (SMT.Term.fst (.var z)) [] (SMT.Term.fst (.var z))
                intro ws
                induction ws with
                | nil => intro _ acc _; simp [toDestPair]
                | cons w ws' ih =>
                  intro zp acc d'
                  cases ws' with
                  | nil => simp [toDestPair]; omega
                  | cons w' ws'' =>
                    simp only [toDestPair]
                    have := ih (.fst d') (.snd d' :: acc) (.fst d')
                    simp [List.length] at this ⊢; omega
              · have := SMT_fv_toDestPair_subset_base (v := v) (z := z)
                  (t₀ := SMT.Term.fst (.var z))
                  (by intro w hw; simp only [SMT.fv, List.mem_singleton] at hw; exact hw)
                  ht hv_t
                exact hv_ne_z this
          -- Now Δ' v = Δ_P v
          have hΔ'_eq : Δ' v = Δ_P v := by
            rw [Δ'_def]; simp [hv_not_vs]
          -- Δ_P v = some d (from hd via hΔ'_eq)
          have hd_P : Δ_P v = some d := by rw [← hΔ'_eq]; exact hd
          -- Lookup in St₃.types is some τ_v too (since St₆ ⊆ St₃)
          have hlookup_St₃ : St₃.types.lookup v = some τ_v :=
            AList.mem_lookup_iff.2 (St₆_sub_St₃ (AList.mem_lookup_iff.1 hlookup))
          -- Apply Δ_P_wt
          exact Δ_P_wt v d hd_P τ_v hlookup_St₃
        have hden_exists := SMT.RenamingContext.denote_exists_of_typing_fv
          h_typ_St₆ hcompat hcov_lambda
        obtain ⟨denT', hden_eq, hden_ty⟩ := hden_exists
        refine ⟨denT', hden_eq, ?_, ?_⟩
        · -- (b) ⟨∅, ⟨(τ ×ᴮ β).set, _⟩⟩ ≘ᶻ denT'
          -- The RDom relation unfolds to a conjunction of:
          -- (1) denT'.2.1 = (τ ×ᴮ β).set.toSMTType (from hden_ty)
          -- (2) retract (τ ×ᴮ β).set denT'.1 = ∅
          -- Since 𝒟 = ∅ (h_nemp), D_RDom gives retract τ.set denD'.1 = ∅.
          -- We need to show the lambda's retract is also empty.
          show denT'.2.fst = _ ∧ retract _ denT'.1 = ∅
          refine ⟨?_, ?_⟩
          · -- Part 1: type equality.
            -- denT'.2.1 = (τ.toSMTType.pair β.toSMTType).fun .bool = (τ ×ᴮ β).set.toSMTType
            rw [hden_ty]
            rfl
          · -- Part 2: retract is empty.
            -- Strategy: Use ZFSet.eq_empty to show nothing is in the retract.
            -- Since 𝒟 = 𝒟' = ∅, retract τ.set denD'.1 = ∅ (from D_RDom).
            -- The lambda's body contains D_enc(z.fst) ∧ˢ ..., so if D's retract is empty,
            -- the lambda's retract is also empty because D_enc can never return zftrue
            -- at the canonical point of any z.fst.
            --
            -- Extract 𝒟 = ∅ from h_nemp.
            have h𝒟_empty : 𝒟 = ∅ := by
              -- 𝒟 and 𝒟' are both the same denotation result
              have h_eq : 𝒟 = 𝒟' := by
                have : (⟦D.abstract «Δ» Δ_fv_D⟧ᴮ).isSome := by rw [den_D]; simp
                rw [den_D] at den_D_eq
                have := Option.some.inj den_D_eq
                exact congrArg (fun (p : B.Dom) => p.1) this
              rw [h_eq]
              exact Classical.byContradiction h_nemp
            have hDretract : retract τ.set denD'.1 = ∅ := by
              have : retract τ.set denD'.1 = 𝒟 := D_RDom.1.2
              rw [this, h𝒟_empty]
            -- denD'.1 is a function ⟦τ.toSMTType⟧ᶻ → 𝔹
            have hdenD_type : denD'.snd.fst = τ.toSMTType.fun SMTType.bool := by
              exact D_RDom.1.1
            have hdenD_func : ⟦τ.toSMTType⟧ᶻ.IsFunc 𝔹 denD'.fst := by
              have := denD'.snd.snd
              rw [hdenD_type, SMTType.toZFSet] at this
              exact ZFSet.mem_funs.mp this
            -- Key consequence: D_enc at canonical point of any x ∈ ⟦τ⟧ᶻ is NOT zftrue.
            -- This follows from `retract τ.set denD'.1 = ∅` + `mem_retract_set_iff_...`
            have hDapp_not_zftrue : ∀ (x : ZFSet.{u}) (hx : x ∈ ⟦τ⟧ᶻ),
                ZFSet.fapply denD'.fst (ZFSet.is_func_is_pfunc hdenD_func)
                  ⟨ZFSet.fapply (BType.canonicalIsoSMTType τ).1
                      (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType τ).2.1)
                      ⟨x, by rwa [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType τ).2.1]⟩,
                    by
                      rw [ZFSet.is_func_dom_eq hdenD_func]
                      exact ZFSet.fapply_mem_range _ _⟩ ≠ zftrue := by
              intro x hx hEq
              -- From the iff, x ∈ retract τ.set denD'.1 = ∅; contradiction
              have hcontra : x ∈ retract τ.set denD'.1 := by
                rw [retract, ZFSet.mem_sep]
                refine ⟨hx, ?_⟩
                rw [dif_pos hx, dif_pos hdenD_func]
                simpa using hEq
              rw [hDretract] at hcontra
              exact absurd hcontra (ZFSet.notMem_empty x)
            -- Now show the lambda's retract is empty.
            -- A point `xy ∈ retract (τ ×ᴮ β).set denT'.1` iff the lambda value
            -- at canonical(xy) is zftrue. But the lambda body is
            -- `D_enc(z.fst) ∧ˢ ...`, and z.fst at canonical(xy) is canonical(τ)(xy.fst).
            -- The body is zftrue iff both conjuncts are zftrue, but the first
            -- conjunct is D_enc at canonical(xy.fst), which is NOT zftrue.
            --
            -- Strategy:
            -- 1. Unfolding retract for (τ ×ᴮ β).set = .fun ((τ×β).toSMTType) .bool
            -- 2. Extensionality via ZFSet.ext on the sep.
            -- 3. Showing the lambda at canonical(xy) evaluates to something ≠ zftrue,
            --    which follows from the D_enc conjunct failing.
            -- 4. Connecting the lambda's SMT denotation (ZFSet.lambda) with the body
            --    evaluation via ZFSet.fapply + ZFSet.mem_lambda + funAbstractGoSingle.
            --
            -- The technical machinery mirrors `retract_lamVal_eq_collect` but for
            -- the lambda-with-eq body rather than the collect-with-ite body.
            -- It is encapsulated in `lambda_defaults_retract_empty_contradiction`.
            --
            -- Show emptiness via ZFSet.ext, with backward trivial.
            apply ZFSet.ext
            intro xy
            constructor
            · -- Forward: xy ∈ retract → xy ∈ ∅ (contradiction).
              intro hxy
              exfalso
              -- xy is in the sep: xy ∈ ⟦(τ×β)⟧ᶻ ∧ (the body condition is zftrue)
              rw [retract, ZFSet.mem_sep] at hxy
              obtain ⟨hxy_mem, hxy_cond⟩ := hxy
              -- denT'.1 is a function ⟦(τ×β).toSMTType⟧ᶻ → 𝔹
              have hdenT_func : ⟦(τ.toSMTType.pair β.toSMTType)⟧ᶻ.IsFunc 𝔹 denT'.fst := by
                have h := denT'.snd.snd
                rw [hden_ty, SMTType.toZFSet] at h
                exact ZFSet.mem_funs.mp h
              -- Simplify hxy_cond by feeding in the dependent hypotheses.
              simp only [dif_pos hxy_mem] at hxy_cond
              -- After simplification, hxy_cond says (modulo the type conversion):
              --   (denT'.fst @ᶻ canonical(xy)) = zftrue
              -- where the if now has `⟦(τ×β).toSMTType⟧ᶻ.IsFunc 𝔹 denT'.fst` as condition.
              -- Since (τ×β).toSMTType = τ.toSMTType.pair β.toSMTType, we can use hdenT_func.
              have hdenT_func' : ⟦(τ ×ᴮ β).toSMTType⟧ᶻ.IsFunc 𝔹 denT'.fst := hdenT_func
              -- Extract the fapply equation from hxy_cond by removing the dite on the
              -- function-predicate, using hdenT_func'.
              rw [dif_pos hdenT_func'] at hxy_cond
              -- Apply the isolated bridge lemma: the D-enc conjunct at canonical(xy).fst
              -- cannot be zftrue, contradicting the lambda-value = zftrue.
              -- The bridge mirrors the collect-with-ite analogue
              -- `retract_lamVal_eq_collect`, captured in
              -- `lambda_defaults_retract_empty_contradiction`.
              -- Derive hcov_D_upd and hden_D_upd from Δ_D / den_D_enc via agreement on fv(D_enc).
              -- z ∉ fv(D_enc) (since D encoding uses St₁.types, which doesn't contain z).
              have z_not_fv_D : z ∉ SMT.fv D_enc := by
                intro hz_fv_D
                have hz_St₁ := Typing.mem_context_of_mem_fv typ_D_enc hz_fv_D
                have hz_St₃ : z ∈ St₃.types :=
                  typeContext_mem_of_subset St₁_sub_St₃_types hz_St₁
                exact z_fresh hz_St₃
              have hcov_D_upd : ∀ W : SMT.Dom,
                  SMT.RenamingContext.CoversFV
                    (Function.update Δ' z (some W)) D_enc := by
                intro W v hv
                rw [Function.update_of_ne (by intro rfl; exact z_not_fv_D hv)]
                rw [Δ'_def]
                by_cases hvs : v ∈ vs
                · simp [hvs]; exact Δ_D_covers v hv
                · simp [hvs]
                  have hDD : Δ_D_ext v = Δ_D v := by
                    rw [Δ_D_ext_def]
                    exact Function.updates_of_not_mem Δ_D vs _ v hvs
                  have ⟨d, hd⟩ := Option.isSome_iff_exists.mp (Δ_D_covers v hv)
                  exact Option.isSome_iff_exists.mpr ⟨d, Δ_P_extends (hDD ▸ hd)⟩
              have hden_D_upd : ∀ W : SMT.Dom,
                  ⟦D_enc.abstract (Function.update Δ' z (some W))
                      (hcov_D_upd W)⟧ˢ = some denD' := by
                intro W
                have h_agree : SMT.RenamingContext.AgreesOnFV
                    (Function.update Δ' z (some W)) Δ_D D_enc := by
                  intro v hv
                  have hvz : v ≠ z := by intro heq; subst heq; exact z_not_fv_D hv
                  rw [Function.update_of_ne hvz]
                  rw [Δ'_def]
                  by_cases hvs : v ∈ vs
                  · simp [hvs]
                  · simp [hvs]
                    have hDD : Δ_D_ext v = Δ_D v := by
                      rw [Δ_D_ext_def]
                      exact Function.updates_of_not_mem Δ_D vs _ v hvs
                    have ⟨d, hd⟩ := Option.isSome_iff_exists.mp (Δ_D_covers v hv)
                    have := Δ_P_extends (hDD ▸ hd)
                    rw [hd, this]
                have heq := SMT.RenamingContext.denote_congr_of_agreesOnFV
                  (h1 := hcov_D_upd W) (h2 := Δ_D_covers) h_agree
                unfold SMT.RenamingContext.denote at heq
                rw [heq]
                exact den_D_enc
              exact lambda_defaults_retract_empty_contradiction
                vs_nemp vs_nodup rfl hcov_lambda hden_eq hden_ty hdenT_func
                hdenD_type hdenD_func hcov_D_upd hden_D_upd hDapp_not_zftrue hxy_mem hxy_cond
            · -- Backward: xy ∈ ∅ is impossible.
              intro hxy
              exact absurd hxy (ZFSet.notMem_empty xy)
        · -- (c) totality for alternative valuations.
          -- Delegated to `lambda_defaults_totality` helper which parallels
          -- `collect_case`'s totality branch.
          -- Context-relationship helpers: St₁ ⊆ St₆ (entries survive).
          have St₁_sub_St₆ : St₁.types ⊆ St₆.types := by
            rw [St₆_types, St₅_types, St₄_types]
            intro ⟨k, τ_k⟩ hk_St₁
            have hk_St₃ := St₁_sub_St₃_types hk_St₁
            have hk_not_vs : k ∉ vs := fun hk_in_vs =>
              vs_disj_St₁ k hk_in_vs (AList.mem_keys.mpr
                (List.mem_map.mpr ⟨⟨k, τ_k⟩, hk_St₁, rfl⟩))
            have hk_ne_z : k ≠ z := by
              intro rfl
              exact z_not_used (St₂_sub_St₃ (St₁_sub_St₂_used (St₁_keys_sub
                (AList.mem_keys.mpr (List.mem_map.mpr ⟨⟨k, τ_k⟩, hk_St₁, rfl⟩)))))
            have hk_ins : ⟨k, τ_k⟩ ∈ (AList.insert z
                (τ.toSMTType.pair β.toSMTType) St₃.types).entries := by
              rw [AList.entries_insert_of_notMem z_fresh, List.mem_cons]
              exact Or.inr hk_St₃
            exact List.mem_kerase_of_ne_key hk_ne_z
              (AList.mem_foldl_erase_of_not_mem_keys hk_ins hk_not_vs)
          have St₁_sub_St₆_used : St₁.env.usedVars ⊆ St₆.env.usedVars := by
            intro v hv
            rw [St₆_used_chain]
            exact List.mem_cons_of_mem _ (St₂_sub_St₃ (St₁_sub_St₂_used hv))
          have St₃_lookup_sub_St₆_P : ∀ v, v ∉ vs → ∀ τ_v,
              AList.lookup v St₃.types = some τ_v →
              AList.lookup v St₆.types = some τ_v := by
            intro v hv_not_vs τ_v h3
            have hv_ne_z : v ≠ z := by
              intro rfl
              have hv_St₃ : v ∈ St₃.types := AList.lookup_isSome.mp (h3 ▸ rfl : (St₃.types.lookup v).isSome = true)
              exact z_fresh hv_St₃
            rw [St₆_types, St₅_types, St₄_types]
            have hentry_St₃ : ⟨v, τ_v⟩ ∈ St₃.types.entries :=
              AList.mem_lookup_iff.1 h3
            have h_ins : ⟨v, τ_v⟩ ∈ (AList.insert z
                (τ.toSMTType.pair β.toSMTType) St₃.types).entries := by
              rw [AList.entries_insert_of_notMem z_fresh]
              exact List.mem_cons_of_mem _ hentry_St₃
            have hentry_St₆ := List.mem_kerase_of_ne_key hv_ne_z
                (AList.mem_foldl_erase_of_not_mem_keys h_ins hv_not_vs)
            exact AList.mem_lookup_iff.2 hentry_St₆
          have St₃_sub_St₆_used : St₃.env.usedVars ⊆ St₆.env.usedVars := by
            intro v hv; rw [St₆_used_chain]
            exact List.mem_cons_of_mem _ hv
          have St₁_dom_sub_St₆ : ∀ v, v ∈ St₁.types → v ∈ St₆.types := by
            intro v hv
            exact AList.mem_of_subset St₁_sub_St₆ hv
          have St₃_dom_sub_St₆ : ∀ v, v ∈ St₃.types → v ∉ vs → v ∈ St₆.types := by
            intro v hv hv_not_vs
            have hv_ne_z : v ≠ z := by
              intro rfl
              exact z_fresh hv
            rw [St₆_types, St₅_types, St₄_types]
            obtain ⟨τ_v, hτ_v⟩ := Option.isSome_iff_exists.mp (AList.lookup_isSome.2 hv)
            have hentry := AList.mem_lookup_iff.1 hτ_v
            have h_ins : ⟨v, τ_v⟩ ∈ (AList.insert z
                (τ.toSMTType.pair β.toSMTType) St₃.types).entries := by
              rw [AList.entries_insert_of_notMem z_fresh]
              exact List.mem_cons_of_mem _ hentry
            exact AList.mem_keys.mpr (List.mem_map.mpr ⟨⟨v, τ_v⟩,
              List.mem_kerase_of_ne_key hv_ne_z
                (AList.mem_foldl_erase_of_not_mem_keys h_ins hv_not_vs), rfl⟩)
          have z_not_fv_D_aux : z ∉ SMT.fv D_enc := by
            intro hz_fv_D
            have hz_St₁ := Typing.mem_context_of_mem_fv typ_D_enc hz_fv_D
            have hz_St₃ : z ∈ St₃.types := AList.mem_of_subset St₁_sub_St₃_types hz_St₁
            exact z_fresh hz_St₃
          have z_not_fv_P_aux : z ∉ SMT.fv P_enc :=
            fun hz => z_fresh (Typing.mem_context_of_mem_fv typ_P_enc hz)
          have z_not_vs_aux : z ∉ vs := fun hz =>
            z_not_used (St₂_sub_St₃ (St₁_sub_St₂_used (used_sub_St₁ (vars_used_vs z hz))))
          -- v ∈ St₆.types ⇒ v ∉ vs (St₆.types = erase z (foldl erase vs (insert z _ St₃)))
          have St₆_not_vs : ∀ v, v ∈ St₆.types → v ∉ vs := by
            intro v hv hvs
            rw [St₆_types, St₅_types] at hv
            have hv_St₅ : v ∈ AList.erase z (List.foldl (fun Γ w => AList.erase w Γ)
                St₄.types vs) := hv
            have hv_foldl := (AList.mem_erase.mp hv_St₅).2
            exact AList.not_mem_foldl_erase_of_mem hvs vs_nodup hv_foldl
          -- Δ'_dom_Γ' : ∀ v, Δ' v ≠ none → v ∈ St₆.types
          have Δ'_dom_Γ' : ∀ v, Δ' v ≠ none → v ∈ St₆.types := by
            intro v hv_ne
            by_cases hvs : v ∈ vs
            · -- v ∈ vs ⇒ Δ' v = Δ_D v ⇒ v ∈ St₁.types ⊆ St₆.types
              have hΔ'_eq : Δ' v = Δ_D v := by rw [Δ'_def]; simp [hvs]
              have hΔ_D_ne : Δ_D v ≠ none := hΔ'_eq ▸ hv_ne
              exact St₁_dom_sub_St₆ v (Δ_D_dom v hΔ_D_ne)
            · -- v ∉ vs ⇒ Δ' v = Δ_P v ⇒ v ∈ St₃.types ⊆ St₆.types
              have hΔ'_eq : Δ' v = Δ_P v := by rw [Δ'_def]; simp [hvs]
              have hΔ_P_ne : Δ_P v ≠ none := hΔ'_eq ▸ hv_ne
              exact St₃_dom_sub_St₆ v (Δ_P_dom v hΔ_P_ne) hvs
          -- Δ'_wt_Γ' : ∀ v d, Δ' v = some d → ∀ τ_v, lookup v St₆.types = some τ_v → d.snd.fst = τ_v
          have Δ'_wt_Γ' : ∀ v (d : SMT.Dom), Δ' v = some d →
              ∀ τ_v, AList.lookup v St₆.types = some τ_v → d.snd.fst = τ_v := by
            intro v d hv τ_v hlookup
            -- v ∈ St₆.types, so v ∉ vs
            have hv_in_St₆ : v ∈ St₆.types :=
              AList.lookup_isSome.mp (hlookup ▸ rfl : (St₆.types.lookup v).isSome = true)
            have hv_not_vs : v ∉ vs := St₆_not_vs v hv_in_St₆
            -- Δ' v = Δ_P v
            have hΔ'_eq : Δ' v = Δ_P v := by rw [Δ'_def]; simp [hv_not_vs]
            have hd_P : Δ_P v = some d := hΔ'_eq ▸ hv
            -- lookup v St₃.types = some τ_v via St₆_sub_St₃
            have hlookup_St₃ : AList.lookup v St₃.types = some τ_v :=
              AList.mem_lookup_iff.2 (St₆_sub_St₃ (AList.mem_lookup_iff.1 hlookup))
            exact Δ_P_wt v d hd_P τ_v hlookup_St₃
          have vs_used_St₃ : ∀ v ∈ vs, v ∈ St₃.env.usedVars :=
            fun v hv => St₂_sub_St₃ (St₁_sub_St₂_used (used_sub_St₁ (vars_used_vs v hv)))
          have vs_lookup_St₃ : ∀ (i : Fin vs.length),
              AList.lookup vs[i] St₃.types = some
                ((τ.toSMTType.fromProdl (vs.length - 1))[i]'(by
                  rw [fromProdl_length_of_hasArity τ_hasArity]; exact i.2)) := by
            intro ⟨i, hi⟩
            set τs := τ.toSMTType.fromProdl (vs.length - 1) with τs_def
            have τs_len : τs.length = vs.length := fromProdl_length_of_hasArity τ_hasArity
            have hi_τs : i < τs.length := τs_len ▸ hi
            have h_St₂_lookup : St₂.types.lookup vs[i] = some τs[i] := by
              rw [St₂_types]; exact foldl_insert_lookup_zip vs_nodup hi hi_τs
            exact AList.mem_lookup_iff.2
              (St₂_sub_St₃_types (AList.mem_lookup_iff.1 h_St₂_lookup))
          have vs_disj_St₆ : ∀ v ∈ vs, v ∉ St₆.types := fun v hv h_in =>
            St₆_not_vs v h_in hv
          have z_not_St₆ : z ∉ St₆.types := by
            rw [St₆_types]
            intro h_erase
            exact (AList.mem_erase.mp h_erase).1 rfl
          exact lambda_defaults_totality (D := D) (P := P) (D_enc := D_enc)
            (P_enc := P_enc) (z := z) (vs := vs) (τ := τ) (β := β)
            (αs := αs) (E_ctx := E.context)
            (Δ' := Δ') (denT' := denT')
            (Γ_D := St₁.types) (used_D := St₁.env.usedVars)
            (Γ_P := St₃.types) (used_P := St₃.env.usedVars)
            (Γ' := St₆.types) (used' := St₆.env.usedVars)
            vs_nemp vs_nodup rfl typ_t typ_D typP typ_D_enc typ_P_enc
            τ_hasArity vs_not_D_fv vs_disj_St₁ vs_disj_St₆ vs_used_St₃ vs_lookup_St₃
            z_fresh z_not_St₆ z_not_used
            z_not_fv_D_aux z_not_fv_P_aux z_not_vs_aux
            hcov_lambda hden_eq hden_ty Δ'_none_out Δ'_dom_Γ' Δ'_wt_Γ'
            D_RDom.2 P_enc_total
            (fun _ _ h => AList.lookup_of_subset St₁_sub_St₆ h)
            (fun _ _ h => AList.lookup_of_subset St₁_sub_St₃_types h)
            (fun _ _ h => AList.lookup_of_subset St₆_sub_St₃ h)
            St₁_sub_St₆_used
            St₃_lookup_sub_St₆_P
            St₃_sub_St₆_used
            covers_D
            covers_P
            St₁_dom_sub_St₆
            St₃_dom_sub_St₆
            (fv_sub_typings typ_t h_typ_St₆)
            (fun v hv => St₂_sub_St₃ (St₁_sub_St₂_used hv))
