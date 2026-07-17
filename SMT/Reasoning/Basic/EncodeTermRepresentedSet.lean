import SMT.Reasoning.Basic.EncodeTermRepresentedApp
import SMT.Reasoning.Basic.EncodeTermCorrectSet

open Std.Do B SMT ZFSet Classical

/-! # Representation-aware set constructors -/

namespace SMT.RenamingContext

/-- Complete a valuation with canonical defaults away from a selected list of
variables.  On the selected variables the original represented values are
preserved exactly. -/
noncomputable def completeOutside.{u} (Theta : Context.{u})
    (Gamma : SMT.TypeContext) (keep : List SMT.𝒱) : Context.{u} :=
  fun v =>
    if v ∈ keep then Theta v
    else
      match Gamma.lookup v with
      | some sigma => some ⟨sigma.defaultZFSet, sigma,
          SMTType.mem_toZFSet_of_defaultZFSet⟩
      | none => none

@[simp]
theorem completeOutside_eq_of_mem.{u}
    {Theta : Context.{u}} {Gamma : SMT.TypeContext}
    {keep : List SMT.𝒱} {v : SMT.𝒱} (hv : v ∈ keep) :
    completeOutside Theta Gamma keep v = Theta v := by
  simp [completeOutside, hv]

/-- The completed valuation is fully type-correct when the values retained on
`keep` already respect their type-context lookups. -/
theorem completeOutside_wt.{u}
    {Theta : Context.{u}} {Gamma : SMT.TypeContext}
    {keep : List SMT.𝒱}
    (hkeep : ∀ {v : SMT.𝒱} {sigma : SMTType},
      v ∈ keep → Gamma.lookup v = some sigma →
        ∃ d : SMT.Dom.{u}, Theta v = some d ∧ d.snd.fst = sigma) :
    ∀ v (d : SMT.Dom.{u}),
      completeOutside Theta Gamma keep v = some d →
      ∀ sigma, Gamma.lookup v = some sigma → d.snd.fst = sigma := by
  intro v d hden sigma hlookup
  by_cases hv : v ∈ keep
  · rw [completeOutside_eq_of_mem hv] at hden
    obtain ⟨d', hd', htype⟩ := hkeep hv hlookup
    have hdd : d = d' := Option.some.inj (hden.symm.trans hd')
    subst d'
    exact htype
  · unfold completeOutside at hden
    rw [if_neg hv, hlookup] at hden
    have hd :
        (⟨sigma.defaultZFSet, sigma,
          SMTType.mem_toZFSet_of_defaultZFSet⟩ : SMT.Dom) = d :=
      Option.some.inj hden
    rw [← hd]

end SMT.RenamingContext

/-- The powerset of a well-typed B set has the expected B set type. -/
theorem powerset_mem_btype.{u} {beta : BType} {X : ZFSet.{u}}
    (hX : X ∈ ⟦BType.set beta⟧ᶻ) :
    X.powerset ∈ ⟦BType.set (BType.set beta)⟧ᶻ := by
  dsimp [BType.toZFSet] at hX ⊢
  rw [ZFSet.mem_powerset] at hX ⊢
  exact powerset_mono.mpr hX

/-- The continuation of the powerset encoder after its operand has been
encoded.  Keeping the continuation named lets the representation proof state
one reusable contract for both supported operand representations. -/
private def encodePowTail (S : SMT.Term) (sigma : SMTType) :
    Encoder (SMT.Term × SMTType) :=
  match sigma with
  | .fun alpha .bool => do
      let ctx := (← get).types
      let x ← freshVar alpha
      let P ← freshVar <| .fun alpha .bool
      modify fun e => { e with types := ctx }
      return (.lambda [P] [.fun alpha .bool]
        (.forall [x] [alpha]
          (.imp (.app (.var P) (.var x)) (.app S (.var x)))),
        .fun (.fun alpha .bool) .bool)
  | .fun alpha (.option beta) => do
      let ⟨Sg, Sg_spec⟩ ← loosenAux_prf "pow!"
        (castPath.graph (castPath.reflexive alpha)
          (castPath.reflexive beta)) S
      declareConstWithSpec Sg (.fun (.pair alpha beta) .bool) Sg_spec
      let ctx := (← get).types
      let p ← freshVar (.pair alpha beta)
      let R ← freshVar <| .fun (.pair alpha beta) .bool
      modify fun e => { e with types := ctx }
      return (.lambda [R] [.fun (.pair alpha beta) .bool]
        (.forall [p] [.pair alpha beta]
          (.imp (.app (.var R) (.var p))
            (.app (.var Sg) (.var p)))),
        .fun (.fun (.pair alpha beta) .bool) .bool)
  | _ => throw s!"encodeTerm:pow: Expected a set or a function, got {sigma}"

/-- Invert a successful B powerset denotation into the operand set and the
definitional powerset result. -/
theorem B.denote_pow_inv_rep.{u}
    {S : B.Term} {beta : BType}
    {Xi : B.RenamingContext.Context}
    (Xi_fv : ∀ v ∈ B.fv (𝒫ᴮ S), (Xi v).isSome = true)
    {T : ZFSet.{u}} {hT : T ∈ ⟦BType.set (BType.set beta)⟧ᶻ}
    (hden : ⟦(𝒫ᴮ S).abstract Xi Xi_fv⟧ᴮ =
      some ⟨T, BType.set (BType.set beta), hT⟩) :
    ∃ (X : ZFSet.{u}) (hX : X ∈ ⟦BType.set beta⟧ᶻ),
      ⟦S.abstract Xi (fun v hv => Xi_fv v (by
        simpa [B.fv] using hv))⟧ᴮ =
          some ⟨X, BType.set beta, hX⟩ ∧
      T = X.powerset := by
  rw [B.Term.abstract, B.denote, Option.pure_def,
    Option.bind_eq_bind, Option.bind_eq_some_iff] at hden
  obtain ⟨⟨X, tau, hX⟩, hdenX, hout⟩ := hden
  cases tau <;> first
    | rw [Option.some_inj] at hout
    | exact absurd hout (by simp)
  rename_i gamma
  injection hout with hvalue htype
  subst T
  simp only [heq_eq_eq, PSigma.mk.injEq, BType.set.injEq] at htype
  obtain ⟨htype, _⟩ := htype
  subst gamma
  refine ⟨X, hX, ?_, rfl⟩
  simpa only [proof_irrel_heq] using hdenX

private theorem erase_insert_self_rep_pow {a : SMT.𝒱} {tau : SMTType}
    {ctx : SMT.TypeContext} (ha : a ∉ ctx) :
    (ctx.insert a tau).erase a = ctx := by
  apply AList.ext
  show List.kerase a (AList.insert a tau ctx).entries = ctx.entries
  rw [AList.entries_insert_of_notMem ha]
  exact List.kerase_cons_eq rfl

/-- Representation-aware contract for the powerset continuation.  Its
semantic clause is valuation-universal so the same operational run serves
both the current denotation and the induction theorem's totality clause. -/
abbrev EncodePowTailRepSpec.{u} (beta : BType)
    (S : SMT.Term) (sigmaS : SMTType) : Prop :=
  ∀ {Lambda : SMT.TypeContext} {n : ℕ} {used : List SMT.𝒱},
    Lambda ⊢ˢ S : sigmaS →
    BType.SupportedSMT (BType.set beta) sigmaS →
    (∀ v ∈ SMT.bv S, v ∈ used) →
    ⦃ fun ⟨env, Lambda'⟩ =>
      ⌜Lambda' = Lambda ∧ env.freshvarsc = n ∧
        Lambda.keys ⊆ env.usedVars ∧ env.usedVars = used⌝ ⦄
    encodePowTail S sigmaS
    ⦃ ⇓? ⟨t, sigma⟩ ⟨env', Gamma'⟩ =>
      ⌜used ⊆ env'.usedVars ∧
        Lambda ⊆ Gamma' ∧
        Gamma'.keys ⊆ env'.usedVars ∧
        Nonempty (sigma ~> (BType.set (BType.set beta)).toSMTType) ∧
        Gamma' ⊢ˢ t : sigma ∧
        (∀ v ∈ used, v ∉ Lambda → v ∉ Gamma') ∧
        ∀ (Theta : SMT.RenamingContext.Context.{u})
          (hS : RenamingContext.CoversFV Theta S),
          (∀ v ∉ used, Theta v = none) →
          SMT.RenamingContext.RespectsTypeContextOnFV Theta Lambda S →
          (∀ v, Theta v ≠ none → v ∈ Lambda) →
          ∀ (X : ZFSet.{u}) (hX : X ∈ ⟦BType.set beta⟧ᶻ)
            (denS : SMT.Dom.{u}),
            ⟦S.abstract Theta hS⟧ˢ = some denS →
            RDomCastSupported
              (⟨X, BType.set beta, hX⟩ : B.Dom) denS →
            ∃ (Theta' : SMT.RenamingContext.Context.{u})
              (hcov : RenamingContext.CoversFV Theta' t)
              (denPow : SMT.Dom.{u}),
              RenamingContext.Extends Theta' Theta ∧
              (∀ v ∉ env'.usedVars, Theta' v = none) ∧
              SMT.RenamingContext.RespectsTypeContextOnFV
                Theta' Gamma' t ∧
              (∀ v, Theta' v ≠ none → v ∈ Gamma') ∧
              ⟦t.abstract Theta' hcov⟧ˢ = some denPow ∧
              denPow.snd.fst = sigma ∧
              RDomCastSupported
                (⟨X.powerset, BType.set (BType.set beta),
                  powerset_mem_btype hX⟩ : B.Dom) denPow⌝ ⦄

set_option maxHeartbeats 2400000 in
theorem encodePowTail_direct_rep_spec.{u}
    (beta : BType) (S : SMT.Term) :
    EncodePowTailRepSpec.{u} beta S
      (SMTType.fun beta.toSMTType SMTType.bool) := by
  unfold EncodePowTailRepSpec
  intro Lambda n used typ_S _supported bv_S_used
  unfold encodePowTail
  mstart
  mintro pre ∀St₀
  mpure pre
  obtain ⟨rfl, rfl, St₀_sub, rfl⟩ := pre
  mspec Std.Do.Spec.get_StateT
  mspec SMT.freshVar_spec
  next x =>
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨St₁_types_eq, x_fresh, St₁_fvc_eq,
      St₁_used_eq, x_not_used⟩ := pre
    mspec SMT.freshVar_spec
    next P =>
      mrename_i pre
      mintro ∀St₂
      mpure pre
      obtain ⟨St₂_types_eq, P_fresh, St₂_fvc_eq,
        St₂_used_eq, P_not_used⟩ := pre
      simp [modify]
      mspec Std.Do.Spec.modifyGet_StateT

      let pred : SMT.Term :=
        ((@ˢSMT.Term.var P) (SMT.Term.var x) ⇒ˢ
          (@ˢS) (SMT.Term.var x))
      let tpow : SMT.Term :=
        (λˢ [P]) [beta.toSMTType.fun SMTType.bool]
          (Term.forall [x] [beta.toSMTType] pred)

      have hP_not_ctx : P ∉ St₀.types := by
        intro h
        apply P_fresh
        rw [St₁_types_eq, AList.mem_insert]
        exact Or.inr h
      have hx_ne_P : x ≠ P := by
        intro h
        apply P_fresh
        rw [St₁_types_eq, AList.mem_insert]
        exact Or.inl h.symm
      have hx_not_ctx : x ∉ St₀.types := x_fresh
      have hP_not_bv_S : P ∉ SMT.bv S := by
        intro h
        apply P_not_used
        rw [St₁_used_eq]
        exact List.mem_cons_of_mem _ (bv_S_used P h)
      have hx_not_bv_S : x ∉ SMT.bv S :=
        fun h => x_not_used (bv_S_used x h)
      have hP_not_fv_S : P ∉ SMT.fv S :=
        funNotMemFvOfNotMemContext typ_S hP_not_ctx
      have hx_not_fv_S : x ∉ SMT.fv S :=
        funNotMemFvOfNotMemContext typ_S hx_not_ctx

      have hx_not_ctxP :
          x ∉ St₀.types.insert P (.fun beta.toSMTType .bool) := by
        rw [AList.mem_insert]
        simp [hx_ne_P, hx_not_ctx]
      have typ_S_P :
          St₀.types.insert P (.fun beta.toSMTType .bool) ⊢ˢ
            S : (BType.set beta).toSMTType :=
        SMT.Typing.weakening
          (SMT.TypeContext.entries_subset_insert_of_notMem hP_not_ctx)
          typ_S
          (SMT.Typing.bv_notMem_insert_of_fresh typ_S hP_not_bv_S)
      have typ_S_Px :
          (St₀.types.insert P (.fun beta.toSMTType .bool)).insert
              x beta.toSMTType ⊢ˢ
            S : (BType.set beta).toSMTType :=
        SMT.Typing.weakening
          (SMT.TypeContext.entries_subset_insert_of_notMem hx_not_ctxP)
          typ_S_P
          (SMT.Typing.bv_notMem_insert_of_fresh typ_S_P hx_not_bv_S)
      have typ_pred :
          (St₀.types.insert P (.fun beta.toSMTType .bool)).insert
              x beta.toSMTType ⊢ˢ pred : .bool := by
        rw [show pred =
          ((@ˢSMT.Term.var P) (SMT.Term.var x) ⇒ˢ
            (@ˢS) (SMT.Term.var x)) from rfl]
        apply SMT.Typing.imp
        · apply SMT.Typing.app
          · apply SMT.Typing.var
            rw [AList.lookup_insert_ne hx_ne_P.symm,
              AList.lookup_insert]
          · apply SMT.Typing.var
            rw [AList.lookup_insert]
        · apply SMT.Typing.app
          · exact typ_S_Px
          · apply SMT.Typing.var
            rw [AList.lookup_insert]
      have typ_forall :
          St₀.types.insert P (.fun beta.toSMTType .bool) ⊢ˢ
            Term.forall [x] [beta.toSMTType] pred : .bool := by
        refine SMT.Typing.forall _ _ _ _ ?_ ?_ ?_ ?_ ?_
        · intro v hv
          rw [List.mem_singleton] at hv
          subst v
          exact hx_not_ctxP
        · intro v hv
          rw [List.mem_singleton] at hv
          subst v
          simp [SMT.bv, pred, hx_not_bv_S]
        · exact Nat.zero_lt_succ 0
        · rfl
        · have hupdate :
              SMT.TypeContext.update
                  (St₀.types.insert P (.fun beta.toSMTType .bool))
                  [x] [beta.toSMTType] rfl =
                (St₀.types.insert P
                  (.fun beta.toSMTType .bool)).insert
                    x beta.toSMTType := by
            simp only [TypeContext.update, List.length_cons,
              List.length_nil, zero_add, Nat.reduceAdd,
              Fin.cast_eq_self, Fin.getElem_fin, Fin.val_eq_zero,
              List.getElem_cons_zero, Fin.foldl_succ, Fin.foldl_zero]
          rw [hupdate]
          exact typ_pred
      have typ_tpow :
          St₀.types ⊢ˢ tpow :
            .fun (.fun beta.toSMTType .bool) .bool := by
        rw [show tpow =
          (λˢ [P]) [beta.toSMTType.fun SMTType.bool]
            (Term.forall [x] [beta.toSMTType] pred) from rfl]
        refine SMT.Typing.lambda _ _ _ _ _ ?_ ?_ ?_ ?_ ?_
        · intro v hv
          rw [List.mem_singleton] at hv
          subst v
          exact hP_not_ctx
        · intro v hv
          rw [List.mem_singleton] at hv
          subst v
          simp [SMT.bv, pred, hP_not_bv_S]
          exact hx_ne_P.symm
        · exact Nat.zero_lt_succ 0
        · rfl
        · have hupdate :
              SMT.TypeContext.update St₀.types [P]
                  [.fun beta.toSMTType .bool] rfl =
                St₀.types.insert P (.fun beta.toSMTType .bool) := by
            simp only [TypeContext.update, List.length_cons,
              List.length_nil, zero_add, Nat.reduceAdd,
              Fin.cast_eq_self, Fin.getElem_fin, Fin.val_eq_zero,
              List.getElem_cons_zero, Fin.foldl_succ, Fin.foldl_zero]
          rw [hupdate]
          exact typ_forall

      mpure_intro
      and_intros
      · intro v hv
        rw [St₂_used_eq, St₁_used_eq]
        exact List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ hv)
      · exact fun _ h => h
      · intro v hv
        rw [St₂_used_eq, St₁_used_eq]
        exact List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (St₀_sub hv))
      · exact ⟨castPath.reflexive
          (BType.set (BType.set beta)).toSMTType⟩
      · simpa [tpow, pred] using typ_tpow
      · intro v hv hv_not
        exact hv_not
      · intro Theta hcov_S Theta_none respects_S Theta_dom
          X hX denS hden_S X_rel
        have hcov_tpow : RenamingContext.CoversFV Theta tpow := by
          intro v hv
          have hv' :
              ((v = P ∨ v = x ∨ v ∈ SMT.fv S ∨ v = x) ∧
                  v ≠ x) ∧ v ≠ P := by
            simpa [tpow, pred, SMT.fv, List.mem_removeAll_iff]
              using hv
          obtain ⟨⟨hv_body, hvx⟩, hvP⟩ := hv'
          rcases hv_body with hP | hx | hvS | hx
          · exact absurd hP hvP
          · exact absurd hx hvx
          · exact hcov_S v hvS
          · exact absurd hx hvx
        have target_respects :
            SMT.RenamingContext.RespectsTypeContextOnFV
              Theta St₀.types tpow := by
          intro v tau hv hlookup
          have hvS : v ∈ SMT.fv S := by
            have hv' :
                ((v = P ∨ v = x ∨ v ∈ SMT.fv S ∨ v = x) ∧
                    v ≠ x) ∧ v ≠ P := by
              simpa [tpow, pred, SMT.fv, List.mem_removeAll_iff]
                using hv
            obtain ⟨⟨hv_body, hvx⟩, hvP⟩ := hv'
            rcases hv_body with hP | hx | hvS | hx
            · exact absurd hP hvP
            · exact absurd hx hvx
            · exact hvS
            · exact absurd hx hvx
          exact respects_S hvS hlookup
        have denS_type :=
          SMT.RenamingContext.denote_type_of_typing_fv
            typ_S respects_S hcov_S hden_S
        rcases denS with ⟨Sval, sigmaS, hSval⟩
        dsimp at denS_type
        subst sigmaS
        have hret :
            retract (BType.set beta) Sval = X :=
          ((RDomCast.iff_RDom_of_type_eq
            (α := BType.set beta) rfl).mp
              X_rel.toRDomCast).2
        obtain ⟨a, sigmaPow, ha, hden_pow, hRDom_pow⟩ :=
          pow_denotation_aux pred rfl tpow rfl hx_ne_P
            hP_not_fv_S hx_not_fv_S
            hP_not_bv_S hx_not_bv_S
            typ_S hP_not_ctx hx_not_ctx
            (Δ_ctx := Theta)
            (Δctx_respects := respects_S)
            hcov_S hcov_tpow hSval hden_S hX hret
            (powerset_mem_btype hX)
        refine Exists.intro Theta ?_
        and_intros
        · exact RenamingContext.extends_refl Theta
        · intro v hv_final
          apply Theta_none
          intro hv_used
          apply hv_final
          rw [St₂_used_eq, St₁_used_eq]
          exact List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ hv_used)
        · simpa [tpow, pred] using target_respects
        · exact Theta_dom
        · refine ⟨(by simpa [tpow, pred] using hcov_tpow),
            a, sigmaPow, ha, ?_, ?_, ?_⟩
          · simpa [tpow, pred] using hden_pow
          · exact hRDom_pow.1
          · exact RDom.toRDomCastSupported hRDom_pow

private theorem encodePowTail_graph_eq
    (alpha beta : BType) (S : SMT.Term) :
    encodePowTail S
        (SMTType.fun alpha.toSMTType
          (SMTType.option beta.toSMTType)) = (do
      let ⟨helper, helperSpec⟩ ← loosenAux_prf "pow!"
        (castPath.graph (castPath.reflexive alpha.toSMTType)
          (castPath.reflexive beta.toSMTType)) S
      declareConstWithSpec helper
        (SMTType.fun
          (SMTType.pair alpha.toSMTType beta.toSMTType) SMTType.bool)
        helperSpec
      encodePowTail (SMT.Term.var helper)
        (SMTType.fun
          (SMTType.pair alpha.toSMTType beta.toSMTType)
          SMTType.bool)) := by
  rfl

set_option maxHeartbeats 2400000 in
theorem encodePowTail_graph_rep_spec.{u}
    (alpha beta : BType) (S : SMT.Term) :
    EncodePowTailRepSpec.{u} (alpha ×ᴮ beta) S
      (SMTType.fun alpha.toSMTType
        (SMTType.option beta.toSMTType)) := by
  unfold EncodePowTailRepSpec
  intro Lambda n used typ_S _supported bv_S_used
  rw [encodePowTail_graph_eq alpha beta S]
  mstart
  mintro pre ∀St₀
  mpure pre
  obtain ⟨rfl, rfl, St₀_sub, rfl⟩ := pre
  let graphPath := castPath.graph
    (castPath.reflexive alpha.toSMTType)
    (castPath.reflexive beta.toSMTType)
  mspec loosenAux_prf_spec_univ (Λ := St₀.types)
    (n := St₀.env.freshvarsc) (used := St₀.env.usedVars)
    typ_S bv_S_used graphPath
  next out =>
    obtain ⟨helper, helperSpec⟩ := out
    mrename_i post₁
    mintro ∀St₁
    mpure post₁
    obtain ⟨_, St₁_types_sub, helper_fresh, helper_not_used,
      used_sub₁, St₁_keys_sub, preserves₁, _, _,
      typ_helper_St₁, _, _, adequacy⟩ := post₁
    mspec SMT.declareConst_addSpec_spec (x! := helper)
      (x!_spec := helperSpec)
      (τ := SMTType.fun
        (SMTType.pair alpha.toSMTType beta.toSMTType) SMTType.bool)
      (decl := St₁.env.declarations) (as := St₁.env.asserts)
      (n := St₁.env.freshvarsc) (Γ := St₁.types)
      (used := St₁.env.usedVars)
    mrename_i post₂
    mintro ∀St₂
    mpure post₂
    obtain ⟨_, _, _, St₂_used_eq, St₂_types_eq⟩ := post₂
    have typ_helper_St₂ : St₂.types ⊢ˢ SMT.Term.var helper :
        SMTType.fun (SMTType.pair alpha.toSMTType beta.toSMTType)
          SMTType.bool := by
      rwa [St₂_types_eq]
    have St₂_keys_sub : St₂.types.keys ⊆ St₂.env.usedVars := by
      intro v hv
      rw [St₂_types_eq] at hv
      rw [St₂_used_eq]
      exact St₁_keys_sub hv
    have helper_lookup_St₁ : St₁.types.lookup helper = some
        (SMTType.fun (SMTType.pair alpha.toSMTType beta.toSMTType)
          SMTType.bool) := SMT.Typing.varE typ_helper_St₁
    have helper_used_St₁ : helper ∈ St₁.env.usedVars :=
      St₁_keys_sub (AList.lookup_isSome.mp
        (Option.isSome_of_eq_some helper_lookup_St₁))
    mspec encodePowTail_direct_rep_spec (alpha ×ᴮ beta)
      (SMT.Term.var helper) typ_helper_St₂
      (.setPred (alpha ×ᴮ beta)) (by simp [SMT.bv])
    rename_i outPow
    obtain ⟨tPow, sigmaPow⟩ := outPow
    mrename_i postPow
    mintro ∀StPow
    mpure postPow
    obtain ⟨used_subPow, types_subPow, keys_subPow, pathPow,
      typ_tPow, preservesPow, semanticPow⟩ := postPow
    mpure_intro
    and_intros
    · intro v hv
      apply used_subPow
      rw [St₂_used_eq]
      exact used_sub₁ hv
    · intro e he
      apply types_subPow
      rw [St₂_types_eq]
      exact St₁_types_sub
        (SMT.TypeContext.entries_subset_insert_of_notMem helper_fresh he)
    · exact keys_subPow
    · exact pathPow
    · exact typ_tPow
    · intro v hv hv_not
      apply preservesPow v (by
        rw [St₂_used_eq]
        exact used_sub₁ hv)
      rw [St₂_types_eq]
      exact preserves₁ v hv hv_not
    · intro Theta hcov_S Theta_none respects_S Theta_dom
        X hX denS hden_S X_rel
      have denS_type :=
        SMT.RenamingContext.denote_type_of_typing_fv
          typ_S respects_S hcov_S hden_S
      rcases denS with ⟨Sval, Ssigma, hSval⟩
      dsimp at denS_type
      subst Ssigma
      have pf : ∀ (x! : SMT.𝒱) (X! : SMT.Dom.{u}),
          ∀ v ∈ SMT.fv (SMT.Term.var x!),
            (Function.update Theta x! (some X!) v).isSome = true := by
        intro x! X! v hv
        rw [SMT.fv, List.mem_singleton] at hv
        subst v
        simp [Function.update_self]
      obtain ⟨Phi, denHelper, hden_var, _hphi, _hden_phi,
          denHelper_type, _Phi_type, ⟨_Phi_true, cast_pair⟩,
          _helper_total⟩ :=
        adequacy Theta hcov_S respects_S pf
          (⟨Sval,
            SMTType.fun alpha.toSMTType
              (SMTType.option beta.toSMTType), hSval⟩ : SMT.Dom)
          hden_S
      rcases denHelper with ⟨Hval, Hsigma, hHval⟩
      dsimp at denHelper_type
      subst Hsigma
      let ThetaH := Function.update Theta helper
        (some (⟨Hval,
          SMTType.fun (SMTType.pair alpha.toSMTType beta.toSMTType)
            SMTType.bool, hHval⟩ : SMT.Dom))
      have helper_none : Theta helper = none :=
        Theta_none helper helper_not_used
      have ThetaH_ext : RenamingContext.Extends ThetaH Theta :=
        RenamingContext.extends_update_of_none helper_none
      have hcov_helper : RenamingContext.CoversFV ThetaH
          (SMT.Term.var helper) := by
        intro v hv
        rw [SMT.fv, List.mem_singleton] at hv
        subst v
        simp [ThetaH, Function.update_self]
      have hden_helper :
          ⟦(SMT.Term.var helper).abstract ThetaH hcov_helper⟧ˢ =
            some (⟨Hval,
              SMTType.fun
                (SMTType.pair alpha.toSMTType beta.toSMTType)
                SMTType.bool, hHval⟩ : SMT.Dom) := by
        simpa only [ThetaH, proof_irrel_heq] using hden_var
      have respects_helper :
          SMT.RenamingContext.RespectsTypeContextOnFV
            ThetaH St₂.types (SMT.Term.var helper) := by
        intro v sigma hv hlookup
        rw [SMT.fv, List.mem_singleton] at hv
        subst v
        have helper_lookup_St₂ : St₂.types.lookup helper = some
            (SMTType.fun
              (SMTType.pair alpha.toSMTType beta.toSMTType)
              SMTType.bool) := SMT.Typing.varE typ_helper_St₂
        rw [helper_lookup_St₂] at hlookup
        cases hlookup
        refine ⟨(⟨Hval,
          SMTType.fun
            (SMTType.pair alpha.toSMTType beta.toSMTType)
            SMTType.bool, hHval⟩ : SMT.Dom), ?_, rfl⟩
        simp [ThetaH, Function.update_self]
      have ThetaH_none : ∀ v ∉ St₂.env.usedVars,
          ThetaH v = none := by
        intro v hv
        have hv_ne : v ≠ helper := by
          intro h
          subst v
          apply hv
          rw [St₂_used_eq]
          exact helper_used_St₁
        simp only [ThetaH, Function.update_of_ne hv_ne]
        apply Theta_none
        intro hv_used
        apply hv
        rw [St₂_used_eq]
        exact used_sub₁ hv_used
      have Lambda_sub_St₂ : St₀.types ⊆ St₂.types := by
        intro e he
        rw [St₂_types_eq]
        exact St₁_types_sub
          (SMT.TypeContext.entries_subset_insert_of_notMem helper_fresh he)
      have ThetaH_dom : ∀ v, ThetaH v ≠ none → v ∈ St₂.types := by
        intro v hv
        by_cases hvh : v = helper
        · subst v
          exact AList.lookup_isSome.mp (Option.isSome_of_eq_some
            (SMT.Typing.varE typ_helper_St₂))
        · have hv₀ : v ∈ St₀.types := Theta_dom v (by
            simpa only [ThetaH, Function.update_of_ne hvh] using hv)
          obtain ⟨tau, hlookup⟩ := Option.isSome_iff_exists.mp
            (AList.lookup_isSome.mpr hv₀)
          exact AList.lookup_isSome.mp (Option.isSome_of_eq_some
            (AList.lookup_of_subset Lambda_sub_St₂ hlookup))
      have X_rel_canonical :
          RDomCastSupported
            (⟨X, BType.set (alpha ×ᴮ beta), hX⟩ : B.Dom)
            (⟨Hval,
              SMTType.fun
                (SMTType.pair alpha.toSMTType beta.toSMTType)
                SMTType.bool, hHval⟩ : SMT.Dom) :=
        RDomCastSupported.of_cast_to_canonical X_rel graphPath cast_pair
      obtain ⟨ThetaPow, hcovPow, denPow, ThetaPow_ext,
          ThetaPow_none, respectsPow, ThetaPow_dom, hdenPow,
          denPow_type, Pow_rel⟩ :=
        semanticPow ThetaH hcov_helper ThetaH_none respects_helper
          ThetaH_dom X hX
          (⟨Hval,
            SMTType.fun
              (SMTType.pair alpha.toSMTType beta.toSMTType)
              SMTType.bool, hHval⟩ : SMT.Dom)
          hden_helper X_rel_canonical
      exact ⟨ThetaPow, hcovPow, denPow,
        RenamingContext.extends_trans ThetaPow_ext ThetaH_ext,
        ThetaPow_none, respectsPow, ThetaPow_dom, hdenPow,
        denPow_type, Pow_rel⟩

theorem encodePowTail_supported_rep_spec.{u}
    (beta : BType) (S : SMT.Term) (sigmaS : SMTType)
    (supported : BType.SupportedSMT (BType.set beta) sigmaS) :
    EncodePowTailRepSpec.{u} beta S sigmaS := by
  cases supported with
  | setPred =>
      exact encodePowTail_direct_rep_spec beta S
  | optionFun alpha gamma =>
      exact encodePowTail_graph_rep_spec alpha gamma S

private theorem encodeTerm_pow_via_tail (S : B.Term) (E : B.Env) :
    encodeTerm (B.Term.pow S) E = (do
      let ⟨Senc, sigmaS⟩ ← encodeTerm S E
      encodePowTail Senc sigmaS) := by
  rfl

set_option maxHeartbeats 5000000 in
theorem encodeTerm_rep_spec.pow_case.{u}
    (S : B.Term)
    (S_ih : EncodeTermRepIH.{u} S)
    (E : B.Env) {Lambda : SMT.TypeContext} {alpha : BType}
    (typ_t : E.context ⊢ᴮ B.Term.pow S : alpha)
    {Delta : B.RenamingContext.Context}
    (Delta_fv : ∀ v ∈ B.fv (B.Term.pow S),
      (Delta v).isSome = true)
    {Delta0 : SMT.RenamingContext.Context.{u}}
    (related : RValuationCastSupportedOnFV Delta Delta0
      (B.Term.pow S))
    {used : List SMT.𝒱}
    (Delta0_none_out : ∀ v ∉ used, Delta0 v = none)
    (Delta0_dom : ∀ v, Delta0 v ≠ none → v ∈ Lambda)
    {T : ZFSet.{u}} {hT : T ∈ ⟦alpha⟧ᶻ}
    (den_t : ⟦(B.Term.pow S).abstract Delta Delta_fv⟧ᴮ =
      some ⟨T, ⟨alpha, hT⟩⟩)
    (vars_used : ∀ v ∈ (B.Term.pow S).vars, v ∈ used)
    (Lambda_inv : ∀ v ∈ (B.Term.pow S).vars,
      v ∈ Lambda → v ∈ E.context)
    (bv_nodup : (B.bv (B.Term.pow S)).Nodup)
    (respects : B.RenamingContext.RespectsTypeContextOnFV
      Delta0 Lambda (B.Term.pow S))
    (fv_in_Lambda : ∀ v ∈ B.fv (B.Term.pow S), v ∈ Lambda)
    (wf : B.RenWF E.context Delta)
    {n : ℕ} :
    ⦃fun ⟨E0, Lambda'⟩ ↦
      ⌜Lambda' = Lambda ∧ E0.freshvarsc = n ∧
        Lambda.keys ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
    encodeTerm (B.Term.pow S) E
    ⦃⇓? (⟨t', sigma⟩ : SMT.Term × SMTType) ⟨E', Gamma'⟩ =>
      ⌜EncodeTermRepPost (B.Term.pow S) alpha Lambda Delta Delta0
        used T hT E t' sigma E' Gamma'⌝⦄ := by
  mstart
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
  rw [encodeTerm_pow_via_tail]

  obtain ⟨beta, rfl, typ_S⟩ := B.Typing.powE typ_t
  obtain ⟨X, hX, den_S, rfl⟩ :=
    B.denote_pow_inv_rep Delta_fv den_t
  have fv_S_sub : B.fv S ⊆ B.fv (B.Term.pow S) := by
    intro v hv
    simpa [B.fv] using hv

  mspec (Std.Do.Triple.and _
    (S_ih E typ_S
      (fun v hv => Delta_fv v (fv_S_sub hv))
      (related.mono_fv fv_S_sub)
      Delta0_none_out Delta0_dom den_S
      (fun v hv => vars_used v (by
        simpa [B.Term.vars, B.fv, B.bv] using hv))
      (fun v hv => Lambda_inv v (by
        simpa [B.Term.vars, B.fv, B.bv] using hv))
      (by simpa [B.bv] using bv_nodup)
      (respects.mono_fv fv_S_sub)
      (fun v hv => fv_in_Lambda v (fv_S_sub hv)) wf
      (n := St.env.freshvarsc))
    (encodeTerm_bv_used E (t := S)
      (used := St.env.usedVars) (n := St.env.freshvarsc)
      (decl := St.env.declarations)))
  clear S_ih
  rename_i out_S
  obtain ⟨Senc, sigmaS⟩ := out_S
  mrename_i post_S
  mintro ∀StS
  mpure post_S
  dsimp at post_S
  obtain ⟨S_post, bv_Senc_used, _bv_used_sub, _bv_delta⟩ := post_S
  obtain ⟨used_sub, types_sub, keys_sub, covers_used,
    _path_S, typ_Senc, _shape_S, preserves,
    DeltaS, hcov_Senc, DeltaS_ext, _related_S, DeltaS_none,
    _respects_S, target_respects_Senc, DeltaS_dom,
    denSenc, hden_Senc, hdenSenc_type, S_rel, S_total⟩ := S_post
  rcases denSenc with ⟨Sval, sigmaSden, hSval⟩
  dsimp at hdenSenc_type
  subst sigmaSden
  have supported_S :
      BType.SupportedSMT (BType.set beta) sigmaS := S_rel.supported

  mspec encodePowTail_supported_rep_spec beta Senc sigmaS supported_S
    typ_Senc supported_S bv_Senc_used
  rename_i out_pow
  obtain ⟨PowEnc, sigmaPow⟩ := out_pow
  mrename_i post_pow
  mintro ∀StPow
  mpure post_pow
  obtain ⟨used_sub_pow, types_sub_pow, keys_sub_pow, path_pow,
    typ_PowEnc, preserves_pow, semantic_pow⟩ := post_pow
  obtain ⟨DeltaPow, hcov_PowEnc, denPow, DeltaPow_ext,
      DeltaPow_none, target_respects_PowEnc, DeltaPow_dom,
      hden_PowEnc, hdenPow_type, Pow_rel⟩ :=
    semantic_pow DeltaS hcov_Senc DeltaS_none
      target_respects_Senc DeltaS_dom X hX
      (⟨Sval, sigmaS, hSval⟩ : SMT.Dom)
      hden_Senc S_rel
  have DeltaPow_ext0 :=
    RenamingContext.extends_trans DeltaPow_ext DeltaS_ext
  have types_sub0 : St.types ⊆ StPow.types :=
    fun _ h => types_sub_pow (types_sub h)

  mpure_intro
  and_intros
  · intro v hv
    exact used_sub_pow (used_sub (by simpa [St_used_eq] using hv))
  · exact types_sub0
  · exact keys_sub_pow
  · simpa [B.fv] using
      (B.CoversUsedVars.mono used_sub_pow covers_used)
  · exact path_pow
  · exact typ_PowEnc
  · trivial
  · intro v hv hLambda hvars
    apply preserves_pow v (used_sub (by simpa [St_used_eq] using hv))
    exact preserves v (by simpa [St_used_eq] using hv) hLambda
      (by simpa [B.Term.vars, B.fv, B.bv] using hvars)
  · refine ⟨DeltaPow, hcov_PowEnc, DeltaPow_ext0,
      related.of_extends DeltaPow_ext0, DeltaPow_none, ?_,
      target_respects_PowEnc, DeltaPow_dom, denPow, hden_PowEnc,
      hdenPow_type, ?_, ?_⟩
    · exact respects.of_extends DeltaPow_ext0 types_sub0
        (fun _ h => h) fv_in_Lambda
    · simpa only [proof_irrel_heq] using Pow_rel
    · intro Delta_alt Delta_fv_alt Delta0_alt related_alt wf_alt
        Delta0_alt_none respects_alt Delta0_alt_dom
        T_alt hT_alt den_t_alt
      obtain ⟨X_alt, hX_alt, den_S_alt, rfl⟩ :=
        B.denote_pow_inv_rep Delta_fv_alt den_t_alt
      have Delta0_alt_none_S : ∀ v ∉ StS.env.usedVars,
          Delta0_alt v = none := by
        intro v hv
        by_contra hne
        have hv_Lambda := Delta0_alt_dom v hne
        have hv_used : v ∈ used := by
          rw [← St_used_eq]
          exact St_sub hv_Lambda
        exact hv (used_sub hv_used)
      obtain ⟨DeltaS_alt, hcov_Senc_alt, denSenc_alt,
          DeltaS_alt_ext, _related_S_alt, DeltaS_alt_none,
          _respects_S_alt, target_respects_Senc_alt,
          DeltaS_alt_dom, hden_Senc_alt, _hdenSenc_alt_type,
          S_alt_rel⟩ :=
        S_total Delta_alt
          (fun v hv => Delta_fv_alt v (fv_S_sub hv))
          Delta0_alt (related_alt.mono_fv fv_S_sub) wf_alt
          Delta0_alt_none_S (respects_alt.mono_fv fv_S_sub)
          Delta0_alt_dom X_alt hX_alt den_S_alt
      obtain ⟨DeltaPow_alt, hcov_PowEnc_alt, denPow_alt,
          DeltaPow_alt_ext, DeltaPow_alt_none,
          target_respects_PowEnc_alt, DeltaPow_alt_dom,
          hden_PowEnc_alt, hdenPow_alt_type, Pow_alt_rel⟩ :=
        semantic_pow DeltaS_alt hcov_Senc_alt DeltaS_alt_none
          target_respects_Senc_alt DeltaS_alt_dom X_alt hX_alt
          denSenc_alt hden_Senc_alt S_alt_rel
      have DeltaPow_alt_ext0 :=
        RenamingContext.extends_trans DeltaPow_alt_ext DeltaS_alt_ext
      refine ⟨DeltaPow_alt, hcov_PowEnc_alt, denPow_alt,
        DeltaPow_alt_ext0, related_alt.of_extends DeltaPow_alt_ext0,
        DeltaPow_alt_none, ?_, target_respects_PowEnc_alt,
        DeltaPow_alt_dom, hden_PowEnc_alt, hdenPow_alt_type, ?_⟩
      · exact respects_alt.of_extends DeltaPow_alt_ext0 types_sub0
          (fun _ h => h) fv_in_Lambda
      · simpa only [proof_irrel_heq] using Pow_alt_rel
