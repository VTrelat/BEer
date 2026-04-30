import SMT.Reasoning.Defs
import SMT.Reasoning.LooseningDefs
import SMT.Reasoning.Basic.StateSpecs
import SMT.Reasoning.Basic.LoosenAuxExact.FunAux
import SMT.Reasoning.Axioms

open Std.Do B SMT ZFSet

private theorem mem_retract_set_iff_app_canonical_eq_zftrue
    {α : BType} {F X : ZFSet} (hF : ⟦α.toSMTType⟧ᶻ.IsFunc 𝔹 F)
    (hRetr : retract (BType.set α) F = X) {x : ZFSet} (hx : x ∈ ⟦α⟧ᶻ) :
    x ∈ X ↔
      ZFSet.fapply F (is_func_is_pfunc hF)
        ⟨ZFSet.fapply (BType.canonicalIsoSMTType α).1
            (is_func_is_pfunc (BType.canonicalIsoSMTType α).2.1)
            ⟨x, by rwa [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType α).2.1]⟩,
          by
            rw [ZFSet.is_func_dom_eq hF]
            exact fapply_mem_range _ _⟩ = zftrue := by
  rw [←hRetr, retract, mem_sep]
  constructor
  · intro h
    obtain ⟨hx', hmem⟩ := h
    rw [dif_pos hx', dif_pos hF] at hmem
    simpa using hmem
  · intro h
    refine ⟨hx, ?_⟩
    rw [dif_pos hx, dif_pos hF]
    simpa using h

private theorem retract_mem_of_toSMTType
    {τ : BType} {x : ZFSet} (hx : x ∈ ⟦τ.toSMTType⟧ᶻ) :
    retract τ x ∈ ⟦τ⟧ᶻ := by
  let ζ := (BType.canonicalIsoSMTType τ).1
  have hζ : ⟦τ⟧ᶻ.IsFunc ⟦τ.toSMTType⟧ᶻ ζ :=
    (BType.canonicalIsoSMTType τ).2.1
  have hζ_bij : ZFSet.IsBijective ζ hζ :=
    (BType.canonicalIsoSMTType τ).2.2
  obtain ⟨y, hy, hyx⟩ := hζ_bij.2 x hx
  have hx_eq := ZFSet.fapply.of_pair (ZFSet.is_func_is_pfunc hζ) hyx
  rw [Subtype.ext_iff] at hx_eq
  dsimp at hx_eq
  have hretract_eq : retract τ x = y := by
    rw [← hx_eq, retract_of_canonical τ hy]
  exact hretract_eq ▸ hy

private theorem mem_toZFSet_pair_inv
    {τ₁ τ₂ : SMTType} {x : ZFSet} (hx : x ∈ ⟦τ₁.pair τ₂⟧ᶻ) :
    x.hasArity 1 ∧
      ∃ x₁ ∈ ⟦τ₁⟧ᶻ, ∃ x₂ ∈ ⟦τ₂⟧ᶻ, x = x₁.pair x₂ := by
  rw [SMTType.toZFSet, ZFSet.mem_prod] at hx
  rcases hx with ⟨x₁, hx₁, x₂, hx₂, rfl⟩
  exact ⟨by simp [ZFSet.hasArity], x₁, hx₁, x₂, hx₂, rfl⟩

private theorem pair_hasArity_get_mem
    {τ₁ τ₂ : SMTType} {x₁ x₂ : ZFSet}
    (hx₁ : x₁ ∈ ⟦τ₁⟧ᶻ) (hx₂ : x₂ ∈ ⟦τ₂⟧ᶻ) :
    (x₁.pair x₂).hasArity [τ₁, τ₂].length ∧
      ∀ i : Fin [τ₁, τ₂].length, (x₁.pair x₂).get [τ₁, τ₂].length i ∈ ⟦[τ₁, τ₂][i]⟧ᶻ := by
  constructor
  · simp [ZFSet.hasArity]
  · intro i
    have hi : i.1 = 0 ∨ i.1 = 1 := by
      have hi_lt : i.1 < 2 := i.2
      omega
    rcases hi with hi | hi
    · have hi' : i = ⟨0, by simp⟩ := by
        apply Fin.ext
        exact hi
      rw [hi']
      simpa using hx₁
    · have hi' : i = ⟨1, by simp⟩ := by
        apply Fin.ext
        exact hi
      rw [hi']
      simpa using hx₂

private theorem cprod_update_eq
    {Δctx : SMT.RenamingContext.Context} {Wp Wa Wb : SMT.Dom} {p a b : SMT.𝒱}
    (hp_ne_a : p ≠ a) (hp_ne_b : p ≠ b) (ha_ne_b : a ≠ b) :
    Function.update (Function.update (Function.update Δctx p (some Wp)) b (some Wb)) a (some Wa) =
      Function.update (Function.update (Function.update Δctx p (some Wp)) a (some Wa)) b
        (some Wb) := by
  funext x
  by_cases hx_a : x = a
  · subst hx_a
    simp [Function.update, ha_ne_b]
  · by_cases hx_b : x = b
    · subst hx_b
      simp [Function.update, hx_a, ha_ne_b]
    · by_cases hx_p : x = p
      · subst hx_p
        simp [Function.update, hx_a, hx_b, hp_ne_a, hp_ne_b]
      · simp [Function.update, hx_a, hx_b, hx_p]

private theorem cprod_body_covers_left
    {«Δ» : SMT.RenamingContext.Context} {Wp Wa Wb : SMT.Dom} {p a b : SMT.𝒱}
    {S_enc T_enc : SMT.Term}
    (hcov_body_upd :
      RenamingContext.CoversFV
        (Function.update (Function.update (Function.update «Δ» p (some Wp)) a (some Wa)) b
          (some Wb))
        (((@ˢS_enc) (SMT.Term.var a)) ∧ˢ
          (((@ˢT_enc) (SMT.Term.var b)) ∧ˢ
            ((SMT.Term.var p) =ˢ (SMT.Term.var a).pair (SMT.Term.var b))))) :
    RenamingContext.CoversFV
      (Function.update (Function.update (Function.update «Δ» p (some Wp)) a (some Wa)) b
        (some Wb))
      ((@ˢS_enc) (SMT.Term.var a)) := by
  intro x hx
  rw [SMT.fv, List.mem_append, SMT.fv, List.mem_singleton] at hx
  cases hx with
  | inl hvS =>
      exact hcov_body_upd x (by simp [SMT.fv, hvS])
  | inr hxa =>
      subst hxa
      exact hcov_body_upd _ (by simp [SMT.fv])

private theorem cprod_body_covers_eq
    {«Δ» : SMT.RenamingContext.Context} {Wp Wa Wb : SMT.Dom} {p a b : SMT.𝒱}
    {S_enc T_enc : SMT.Term}
    (hcov_body_upd :
      RenamingContext.CoversFV
        (Function.update (Function.update (Function.update «Δ» p (some Wp)) a (some Wa)) b
          (some Wb))
        (((@ˢS_enc) (SMT.Term.var a)) ∧ˢ
          (((@ˢT_enc) (SMT.Term.var b)) ∧ˢ
            ((SMT.Term.var p) =ˢ (SMT.Term.var a).pair (SMT.Term.var b))))) :
    RenamingContext.CoversFV
      (Function.update (Function.update (Function.update «Δ» p (some Wp)) a (some Wa)) b
        (some Wb))
      ((SMT.Term.var p) =ˢ (SMT.Term.var a).pair (SMT.Term.var b)) := by
  intro x hx
  exact hcov_body_upd x (by
    simpa [SMT.fv] using (Or.inr (Or.inr (Or.inr (Or.inr hx)))))

private theorem cprod_body_covers_right
    {«Δ» : SMT.RenamingContext.Context} {Wp Wa Wb : SMT.Dom} {p a b : SMT.𝒱}
    {S_enc T_enc : SMT.Term}
    (hcov_body_upd :
      RenamingContext.CoversFV
        (Function.update (Function.update (Function.update «Δ» p (some Wp)) a (some Wa)) b
          (some Wb))
        (((@ˢS_enc) (SMT.Term.var a)) ∧ˢ
          (((@ˢT_enc) (SMT.Term.var b)) ∧ˢ
            ((SMT.Term.var p) =ˢ (SMT.Term.var a).pair (SMT.Term.var b))))) :
    RenamingContext.CoversFV
      (Function.update (Function.update (Function.update «Δ» p (some Wp)) a (some Wa)) b
        (some Wb))
      (((@ˢT_enc) (SMT.Term.var b)) ∧ˢ
        ((SMT.Term.var p) =ˢ (SMT.Term.var a).pair (SMT.Term.var b))) := by
  intro x hx
  exact hcov_body_upd x (by
    simpa [SMT.fv] using (Or.inr (Or.inr hx)))

private theorem cprod_covers_var_p
    {Δctx : SMT.RenamingContext.Context} {Wp Wa Wb : SMT.Dom} {p a b : SMT.𝒱}
    (hp_ne_a : p ≠ a) (hp_ne_b : p ≠ b) :
    RenamingContext.CoversFV
      (Function.update (Function.update (Function.update Δctx p (some Wp)) a (some Wa)) b
        (some Wb))
      (SMT.Term.var p) := by
  intro x hx
  rw [SMT.fv, List.mem_singleton] at hx
  subst hx
  simp [Function.update, hp_ne_a, hp_ne_b]

private theorem cprod_denote_var_p
    {Δctx : SMT.RenamingContext.Context} {Wp Wa Wb : SMT.Dom} {p a b : SMT.𝒱}
    (hp_ne_a : p ≠ a) (hp_ne_b : p ≠ b) :
    ⟦(SMT.Term.var p).abstract
        (Function.update (Function.update (Function.update Δctx p (some Wp)) a (some Wa)) b
          (some Wb))
        (cprod_covers_var_p (Δctx := Δctx) (Wp := Wp) (Wa := Wa) (Wb := Wb)
          (p := p) (a := a) (b := b) hp_ne_a hp_ne_b)⟧ˢ = some Wp := by
  simp [SMT.Term.abstract.eq_def, SMT.denote, Option.pure_def, Function.update, hp_ne_a, hp_ne_b]

private theorem cprod_covers_var_a
    {Δctx : SMT.RenamingContext.Context} {Wp Wa Wb : SMT.Dom} {p a b : SMT.𝒱}
    (ha_ne_b : a ≠ b) :
    RenamingContext.CoversFV
      (Function.update (Function.update (Function.update Δctx p (some Wp)) a (some Wa)) b
        (some Wb))
      (SMT.Term.var a) := by
  intro x hx
  rw [SMT.fv, List.mem_singleton] at hx
  subst hx
  simp [Function.update, ha_ne_b]

private theorem cprod_denote_var_a
    {Δctx : SMT.RenamingContext.Context} {Wp Wa Wb : SMT.Dom} {p a b : SMT.𝒱}
    (ha_ne_b : a ≠ b) :
    ⟦(SMT.Term.var a).abstract
        (Function.update (Function.update (Function.update Δctx p (some Wp)) a (some Wa)) b
          (some Wb))
        (cprod_covers_var_a (Δctx := Δctx) (Wp := Wp) (Wa := Wa) (Wb := Wb)
          (p := p) (a := a) (b := b) ha_ne_b)⟧ˢ = some Wa := by
  simp [SMT.Term.abstract.eq_def, SMT.denote, Option.pure_def, Function.update, ha_ne_b]

private theorem cprod_covers_var_b
    {Δctx : SMT.RenamingContext.Context} {Wp Wa Wb : SMT.Dom} {p a b : SMT.𝒱} :
    RenamingContext.CoversFV
      (Function.update (Function.update (Function.update Δctx p (some Wp)) a (some Wa)) b
        (some Wb))
      (SMT.Term.var b) := by
  intro x hx
  rw [SMT.fv, List.mem_singleton] at hx
  subst hx
  simp [Function.update]

private theorem cprod_denote_var_b
    {Δctx : SMT.RenamingContext.Context} {Wp Wa Wb : SMT.Dom} {p a b : SMT.𝒱} :
    ⟦(SMT.Term.var b).abstract
        (Function.update (Function.update (Function.update Δctx p (some Wp)) a (some Wa)) b
          (some Wb))
        (cprod_covers_var_b (Δctx := Δctx) (Wp := Wp) (Wa := Wa) (Wb := Wb)
          (p := p) (a := a) (b := b))⟧ˢ = some Wb := by
  simp [SMT.Term.abstract.eq_def, SMT.denote, Option.pure_def, Option.some.injEq, Function.update]

/-! ### Factored powerset denotation lemma

This lemma abstracts the ~1050-line denotation proof for `tpow` over a generic
renaming context `Δ_ctx` and S_enc denotation. It is called for both the original
and alt cases.
-/
set_option maxHeartbeats 1200000 in
private theorem pow_denotation_aux.{u}
    {β : BType}
    {S_enc : SMT.Term} {x E : SMT.𝒱}
    -- pred and tpow definitions
    (pred : SMT.Term)
    (hpred_def : pred = ((@ˢSMT.Term.var E) (SMT.Term.var x) ⇒ˢ (@ˢS_enc) (SMT.Term.var x)))
    (tpow : SMT.Term)
    (htpow_def : tpow = (λˢ [E]) [β.toSMTType.fun SMTType.bool]
      (Term.forall [x] [β.toSMTType] pred))
    -- x ≠ E, E/x not in fv/bv of S_enc
    (hx_ne_E : x ≠ E)
    (hE_not_mem_fv_S_enc : E ∉ SMT.fv S_enc)
    (hx_not_mem_fv_S_enc : x ∉ SMT.fv S_enc)
    (hE_not_bv_S_enc : E ∉ SMT.bv S_enc)
    (hx_not_bv_S_enc : x ∉ SMT.bv S_enc)
    -- Typing
    {ctx : SMT.TypeContext}
    (typ_S_enc : ctx ⊢ˢ S_enc : β.set.toSMTType)
    (hE_not_ctx : E ∉ ctx) (hx_not_ctx : x ∉ ctx)
    -- Generic renaming context
    {Δ_ctx : SMT.RenamingContext.Context}
    (hΔ_covers_S : RenamingContext.CoversFV Δ_ctx S_enc)
    (hΔ_covers_tpow : RenamingContext.CoversFV Δ_ctx tpow)
    -- S_enc denotation under Δ_ctx
    {Sval : ZFSet.{u}} (hSval : Sval ∈ ⟦β.set.toSMTType⟧ᶻ)
    (den_S : ⟦S_enc.abstract Δ_ctx hΔ_covers_S⟧ˢ = some ⟨Sval, ⟨β.set.toSMTType, hSval⟩⟩)
    -- X = retract β.set Sval
    {X : ZFSet.{u}} (hX : X ∈ ⟦β.set⟧ᶻ)
    (retract_eq : retract β.set Sval = X)
    (hT : X.powerset ∈ ⟦β.set.set⟧ᶻ)
    : ∃ (a : ZFSet.{u}) (a_1 : SMTType) (h : a ∈ ⟦a_1⟧ᶻ),
        ⟦tpow.abstract Δ_ctx hΔ_covers_tpow⟧ˢ = some ⟨a, ⟨a_1, h⟩⟩ ∧
          ⟨X.powerset, ⟨β.set.set, hT⟩⟩ ≘ᶻ ⟨a, ⟨a_1, h⟩⟩ := by
  have hx_not_ctxE : x ∉ ctx.insert E (.fun β.toSMTType .bool) := by
    rw [AList.mem_insert]
    simp [hx_ne_E, hx_not_ctx]
  have typ_S_enc_E_insert :
      ctx.insert E (.fun β.toSMTType .bool) ⊢ˢ S_enc : β.set.toSMTType :=
    Typing.weakening
      (h := SMT.TypeContext.entries_subset_insert_of_notMem hE_not_ctx)
      typ_S_enc
  have typ_S_enc_Ex_insert :
      (ctx.insert E (.fun β.toSMTType .bool)).insert x β.toSMTType ⊢ˢ S_enc :
        β.set.toSMTType :=
    Typing.weakening
      (h := SMT.TypeContext.entries_subset_insert_of_notMem hx_not_ctxE)
      typ_S_enc_E_insert
  have typ_pred :
      (ctx.insert E (.fun β.toSMTType .bool)).insert x β.toSMTType ⊢ˢ pred : .bool := by
    rw [hpred_def]
    apply SMT.Typing.imp
    · apply SMT.Typing.app
      · apply SMT.Typing.var
        rw [AList.lookup_insert_ne hx_ne_E.symm, AList.lookup_insert]
      · apply SMT.Typing.var
        rw [AList.lookup_insert]
    · apply SMT.Typing.app
      · exact typ_S_enc_Ex_insert
      · apply SMT.Typing.var
        rw [AList.lookup_insert]
  have typ_app_rhs :
      (ctx.insert E (.fun β.toSMTType .bool)).insert x β.toSMTType ⊢ˢ
        ((@ˢS_enc) (SMT.Term.var x)) : .bool := by
    apply SMT.Typing.app
    · exact typ_S_enc_Ex_insert
    · apply SMT.Typing.var
      rw [AList.lookup_insert]
  have typ_not_rhs :
      (ctx.insert E (.fun β.toSMTType .bool)).insert x β.toSMTType ⊢ˢ
        (¬ˢ ((@ˢS_enc) (SMT.Term.var x))) : .bool := by
    apply SMT.Typing.not
    exact typ_app_rhs
  have typ_forall :
      ctx.insert E (.fun β.toSMTType .bool) ⊢ˢ
        Term.forall [x] [β.toSMTType] pred : .bool := by
    refine SMT.Typing.forall _ _ _ _ ?_ ?_ ?_ ?_ ?_
    · intro v hv
      rw [List.mem_singleton] at hv
      subst hv
      exact hx_not_ctxE
    · intro v hv
      rw [List.mem_singleton] at hv
      subst hv
      simp [SMT.bv, hpred_def, hx_not_bv_S_enc]
    · exact Nat.zero_lt_succ 0
    · rfl
    · have hupdateEx :
          SMT.TypeContext.update (ctx.insert E (.fun β.toSMTType .bool)) [x] [β.toSMTType] rfl =
            (ctx.insert E (.fun β.toSMTType .bool)).insert x β.toSMTType := by
        simp only [TypeContext.update, List.length_cons, List.length_nil,
          zero_add, Nat.reduceAdd, Fin.cast_eq_self, Fin.getElem_fin,
          Fin.val_eq_zero, List.getElem_cons_zero, Fin.foldl_succ,
          Fin.foldl_zero]
      rw [hupdateEx]
      simpa [hpred_def] using typ_pred
  have typ_tpow : ctx ⊢ˢ tpow : .fun (.fun β.toSMTType .bool) .bool := by
    rw [htpow_def]
    refine SMT.Typing.lambda _ _ _ _ _ ?_ ?_ ?_ ?_ ?_
    · intro v hv
      rw [List.mem_singleton] at hv
      subst hv
      exact hE_not_ctx
    · intro v hv
      rw [List.mem_singleton] at hv
      subst hv
      simp [SMT.bv, hpred_def, hE_not_bv_S_enc]
      exact hx_ne_E.symm
    · exact Nat.zero_lt_succ 0
    · rfl
    · have hupdateE :
          SMT.TypeContext.update ctx [E] [.fun β.toSMTType .bool] rfl =
            ctx.insert E (.fun β.toSMTType .bool) := by
        simp only [TypeContext.update, List.length_cons, List.length_nil, zero_add,
          Nat.reduceAdd, Fin.cast_eq_self, Fin.getElem_fin, Fin.val_eq_zero,
          List.getElem_cons_zero, Fin.foldl_succ, Fin.foldl_zero]
      rw [hupdateE]
      simpa [htpow_def] using typ_forall
  have hgo_cov_forall :
      ∀ z ∈ SMT.fv (Term.forall [x] [β.toSMTType] pred), z ∉ [E] →
        (Δ_ctx z).isSome = true := by
    intro z hz hzE
    have hz' : z ∈ SMT.fv pred ∧ ¬ z = x := by
      simpa [SMT.fv, List.mem_removeAll_iff] using hz
    have hzE' : ¬ z = E := by
      simpa [List.mem_singleton] using hzE
    exact hΔ_covers_tpow z (by
      simpa [htpow_def, SMT.fv, List.mem_removeAll_iff] using ⟨hz', hzE'⟩)
  have hcov_forall_upd :
      ∀ F : SMT.Dom,
        RenamingContext.CoversFV (Function.update Δ_ctx E (some F))
          (Term.forall [x] [β.toSMTType] pred) := by
    intro F z hz
    by_cases hzE : z = E
    · subst hzE
      simp
    · rw [Function.update_of_ne hzE]
      apply hgo_cov_forall z hz
      simp only [List.mem_cons, hzE, List.not_mem_nil, or_self, not_false_eq_true]
  have hcov_pred_upd :
      ∀ F W : SMT.Dom,
        RenamingContext.CoversFV
          (Function.update (Function.update Δ_ctx E (some F)) x (some W)) pred := by
    intro F W z hz
    simp [hpred_def, SMT.fv, List.mem_append, Function.update] at hz ⊢
    rcases hz with rfl | rfl | hzS | rfl
    · by_cases hEx : z = x
      · simp [hEx]
      · simp [hEx]
    · simp
    · by_cases hzx : z = x
      · subst hzx
        exact False.elim (hx_not_mem_fv_S_enc hzS)
      · by_cases hzE : z = E
        · subst hzE
          exact False.elim (hE_not_mem_fv_S_enc hzS)
        · simp [hzx, hzE, hΔ_covers_S z hzS]
    · simp
  have hpred_total :
      ∀ F W : SMT.Dom, F.snd.fst = β.toSMTType.fun SMTType.bool →
        W.snd.fst = β.toSMTType →
        ⟦pred.abstract
            (Function.update (Function.update Δ_ctx E (some F)) x (some W))
            (hcov_pred_upd F W)⟧ˢ.isSome = true := by
    intro F W hF_ty hW_ty
    have hE_ne_x : E ≠ x := by
      intro hEx
      exact hx_ne_E hEx.symm
    have hF_func : ZFSet.IsFunc ⟦β.toSMTType⟧ᶻ ⟦SMTType.bool⟧ᶻ F.fst := by
      have hF_mem : F.fst ∈ ⟦β.toSMTType⟧ᶻ.funs ⟦SMTType.bool⟧ᶻ := by
        simpa [hF_ty, SMTType.toZFSet] using F.snd.snd
      rw [ZFSet.mem_funs] at hF_mem
      exact hF_mem
    have hW_mem : W.fst ∈ ⟦β.toSMTType⟧ᶻ := by
      simpa [hW_ty] using W.snd.snd
    obtain ⟨_, Dlhs, hDlhs_ty, _, hden_lhs⟩ :=
      funDenoteAppAt
        (Δctx := Function.update Δ_ctx E (some F))
        (t := .var E) (x := x)
        (α := β.toSMTType) (β := SMTType.bool) (Y := F)
        (hcov_t_upd := by
          intro Xarg v hv
          rw [SMT.fv, List.mem_singleton] at hv
          subst hv
          rw [Function.update_of_ne hE_ne_x, Function.update_self]
          simp)
        (den_t_upd := by
          intro Xarg
          rw [SMT.Term.abstract.eq_def, SMT.denote, Option.pure_def,
            Option.some.injEq]
          apply Option.get_of_eq_some
          rw [Function.update_of_ne hE_ne_x, Function.update_self])
        (hY_ty := hF_ty)
        (hY_func := hF_func)
        (Xarg := W)
        (hXarg_ty := hW_ty)
        (hXarg_mem := hW_mem)
    have hSval_func :
        ZFSet.IsFunc ⟦β.toSMTType⟧ᶻ ⟦SMTType.bool⟧ᶻ Sval := by
      have hSval_mem : Sval ∈ ⟦β.toSMTType⟧ᶻ.funs ⟦SMTType.bool⟧ᶻ := by
        simpa [BType.toSMTType, SMTType.toZFSet] using hSval
      rw [ZFSet.mem_funs] at hSval_mem
      exact hSval_mem
    have hcov_S_enc_E :
        RenamingContext.CoversFV (Function.update Δ_ctx E (some F)) S_enc := by
      exact SMT.RenamingContext.coversFV_update_of_notMem
        (x := E) (d := F) hE_not_mem_fv_S_enc hΔ_covers_S
    have den_S_E :
        ⟦S_enc.abstract
            (Function.update Δ_ctx E (some F))
            hcov_S_enc_E⟧ˢ =
          some ⟨Sval, ⟨β.set.toSMTType, hSval⟩⟩ := by
      have hden_S_E_raw :
          ⟦S_enc.abstract Δ_ctx hΔ_covers_S⟧ˢ =
            ⟦S_enc.abstract
                (Function.update Δ_ctx E (some F))
                hcov_S_enc_E⟧ˢ := by
        simpa [SMT.RenamingContext.denote] using
          (SMT.RenamingContext.denote_update_of_notMem
            («Δ» := Δ_ctx) (t := S_enc) (x := E) (d := F)
            (h := hΔ_covers_S) hE_not_mem_fv_S_enc)
      rw [←hden_S_E_raw]
      simpa [SMT.RenamingContext.denote] using den_S
    obtain ⟨_, Drhs, hDrhs_ty, _, hden_rhs⟩ :=
      funDenoteAppAt
        (Δctx := Function.update Δ_ctx E (some F))
        (t := S_enc) (x := x)
        (α := β.toSMTType) (β := SMTType.bool)
        (Y := ⟨Sval, ⟨β.set.toSMTType, hSval⟩⟩)
        (hcov_t_upd := by
          intro Xarg
          exact SMT.RenamingContext.coversFV_update_of_notMem
            (x := x) (d := Xarg) hx_not_mem_fv_S_enc hcov_S_enc_E)
        (den_t_upd := by
          intro Xarg
          have hden_S_EX_raw :
              ⟦S_enc.abstract
                  (Function.update Δ_ctx E (some F))
                  hcov_S_enc_E⟧ˢ =
                ⟦S_enc.abstract
                    (Function.update
                      (Function.update Δ_ctx E (some F)) x (some Xarg))
                    (SMT.RenamingContext.coversFV_update_of_notMem
                      (x := x) (d := Xarg) hx_not_mem_fv_S_enc hcov_S_enc_E)⟧ˢ := by
            simpa [SMT.RenamingContext.denote] using
              (SMT.RenamingContext.denote_update_of_notMem
                («Δ» := Function.update Δ_ctx E (some F))
                (t := S_enc) (x := x) (d := Xarg)
                (h := hcov_S_enc_E) hx_not_mem_fv_S_enc)
          rw [←hden_S_EX_raw]
          exact den_S_E)
        (hY_ty := rfl)
        (hY_func := hSval_func)
        (Xarg := W)
        (hXarg_ty := hW_ty)
        (hXarg_mem := hW_mem)
    have hnot_rhs_isSome :
        ⟦(¬ˢ ((@ˢS_enc) (SMT.Term.var x))).abstract
            (Function.update (Function.update Δ_ctx E (some F)) x (some W))
            (by
              intro v hv
              have hv' : v ∈ SMT.fv ((@ˢS_enc) (SMT.Term.var x)) := by
                simpa [SMT.fv] using hv
              have hv'' : v ∈ SMT.fv S_enc ∨ v = x := by
                simpa [SMT.fv] using hv'
              exact hcov_pred_upd F W v (by
                rw [hpred_def]
                simp only [SMT.fv, List.mem_append, List.mem_singleton]
                exact Or.inr hv''))⟧ˢ.isSome = true := by
      simpa [SMT.Term.abstract, proof_irrel_heq] using
        denote_not_isSome_of_some_bool hden_rhs hDrhs_ty
    obtain ⟨Dnot, hden_not⟩ := Option.isSome_iff_exists.mp hnot_rhs_isSome
    have hDnot_ty : Dnot.snd.fst = SMTType.bool := by
      exact denote_type_eq_of_typing (typ_t := typ_not_rhs) (hden := hden_not)
    obtain ⟨Dbody, hden_body, hDbody_ty⟩ :=
      denote_and_some_bool_of_some_bool hden_lhs hDlhs_ty hden_not hDnot_ty
    simpa [hpred_def, SMT.Term.abstract, proof_irrel_heq] using
      denote_not_isSome_of_some_bool hden_body hDbody_ty
  have hpred_ty :
      ∀ F W : SMT.Dom, F.snd.fst = β.toSMTType.fun SMTType.bool →
        W.snd.fst = β.toSMTType →
        ∀ {D : SMT.Dom},
          ⟦pred.abstract
              (Function.update (Function.update Δ_ctx E (some F)) x (some W))
              (hcov_pred_upd F W)⟧ˢ = some D →
            D.snd.fst = SMTType.bool := by
    intro F W hF_ty hW_ty D hD
    exact denote_type_eq_of_typing (typ_t := typ_pred) (hden := hD)
  have hforall_total :
      ∀ F : SMT.Dom,
        F.snd.fst = β.toSMTType.fun SMTType.bool →
        ⟦(Term.forall [x] [β.toSMTType] pred).abstract
            (Function.update Δ_ctx E (some F)) (hcov_forall_upd F)⟧ˢ.isSome = true := by
    intro F hF_ty
    refine funUnaryForallTotal
      (hφ_forall := hcov_forall_upd F)
      (hgo_cov := ?_)
      (hcov_a_upd := ?_)
      (hbody_total := ?_)
    · intro z hz hzx
      have hzx' : z ≠ x := by
        simpa [List.mem_singleton] using hzx
      have hcov :=
        hcov_pred_upd F ⟨β.toSMTType.defaultZFSet, β.toSMTType,
          SMTType.mem_toZFSet_of_defaultZFSet⟩ z (by
            simpa [SMT.fv, List.mem_removeAll_iff] using hz)
      simpa [Function.update_of_ne hzx'] using hcov
    · intro W
      exact hcov_pred_upd F W
    · intro W hW_ty
      exact hpred_total F W hF_ty hW_ty
  have hsome_tpow :
      (⟦tpow.abstract Δ_ctx hΔ_covers_tpow⟧ˢ).isSome = true := by
    have hcov_unf : RenamingContext.CoversFV Δ_ctx
        ((λˢ [E]) [β.toSMTType.fun SMTType.bool] (Term.forall [x] [β.toSMTType] pred)) :=
      htpow_def ▸ hΔ_covers_tpow
    have habstr_eq : tpow.abstract Δ_ctx hΔ_covers_tpow =
        ((λˢ [E]) [β.toSMTType.fun SMTType.bool] (Term.forall [x] [β.toSMTType] pred)).abstract
          Δ_ctx hcov_unf := by
      cases htpow_def; rfl
    rw [habstr_eq]
    rw [SMT.Term.abstract, dif_pos (by rfl), SMT.denote]
    split_ifs with hlen_pos den_t_isSome den_t_typ_det
    · simp
    · exfalso
      apply den_t_typ_det
      intro x_1 y_1 hx_1 hy_1
      have hgo_x :=
        funAbstractGoSingle
          (Δctx := Δ_ctx) (P := Term.forall [x] [β.toSMTType] pred)
          (v := E) (τ := β.toSMTType.fun SMTType.bool)
          hgo_cov_forall hcov_forall_upd x_1 (by
            intro i
            have hi0 : i = ⟨0, by simp⟩ := by
              apply Fin.ext
              simp
            cases hi0
            simpa using hx_1 ⟨0, by simp⟩)
      have hgo_y :=
        funAbstractGoSingle
          (Δctx := Δ_ctx) (P := Term.forall [x] [β.toSMTType] pred)
          (v := E) (τ := β.toSMTType.fun SMTType.bool)
          hgo_cov_forall hcov_forall_upd y_1 (by
            intro i
            have hi0 : i = ⟨0, by simp⟩ := by
              apply Fin.ext
              simp
            cases hi0
            simpa using hy_1 ⟨0, by simp⟩)
      let Fx : SMT.Dom := x_1 ⟨0, by simp⟩
      let Fy : SMT.Dom := y_1 ⟨0, by simp⟩
      have hFx_ty : Fx.snd.fst = β.toSMTType.fun SMTType.bool := by
        simpa [Fx] using (hx_1 ⟨0, by simp⟩).1
      have hFy_ty : Fy.snd.fst = β.toSMTType.fun SMTType.bool := by
        simpa [Fy] using (hy_1 ⟨0, by simp⟩).1
      obtain ⟨Dx, hDx⟩ := Option.isSome_iff_exists.mp (hforall_total Fx hFx_ty)
      obtain ⟨Dy, hDy⟩ := Option.isSome_iff_exists.mp (hforall_total Fy hFy_ty)
      have hden_x :
          ⟦(SMT.Term.abstract.go
              (Term.forall [x] [β.toSMTType] pred) [E] Δ_ctx hgo_cov_forall).uncurry x_1⟧ˢ =
            some Dx := by
        rw [hgo_x]
        exact hDx
      have hden_y :
          ⟦(SMT.Term.abstract.go
              (Term.forall [x] [β.toSMTType] pred) [E] Δ_ctx hgo_cov_forall).uncurry y_1⟧ˢ =
            some Dy := by
        rw [hgo_y]
        exact hDy
      calc
        (⟦(SMT.Term.abstract.go
            (Term.forall [x] [β.toSMTType] pred) [E] Δ_ctx hgo_cov_forall).uncurry x_1⟧ˢ.get
          (den_t_isSome hx_1)).snd.fst = Dx.snd.fst := by
            exact congrArg (fun d : SMT.Dom => d.snd.fst)
              (Option.get_of_eq_some (den_t_isSome hx_1) hden_x)
        _ = SMTType.bool := denote_type_eq_of_typing (typ_t := typ_forall) (hden := hDx)
        _ = Dy.snd.fst := (denote_type_eq_of_typing (typ_t := typ_forall) (hden := hDy)).symm
        _ = (⟦(SMT.Term.abstract.go
            (Term.forall [x] [β.toSMTType] pred) [E] Δ_ctx hgo_cov_forall).uncurry y_1⟧ˢ.get
          (den_t_isSome hy_1)).snd.fst := by
            exact (congrArg (fun d : SMT.Dom => d.snd.fst)
              (Option.get_of_eq_some (den_t_isSome hy_1) hden_y)).symm
    · exfalso
      apply den_t_isSome
      intro x_1 hx_1
      have hgo :=
        funAbstractGoSingle
          (Δctx := Δ_ctx) (P := Term.forall [x] [β.toSMTType] pred)
          (v := E) (τ := β.toSMTType.fun SMTType.bool)
          hgo_cov_forall hcov_forall_upd x_1 (by
            rintro ⟨i, hi⟩
            simp only [List.length_cons, List.length_nil, zero_add,
              Nat.lt_one_iff] at hi
            subst hi
            exact hx_1 ⟨0, Nat.zero_lt_succ 0⟩)
      rw [hgo]
      let F : SMT.Dom := x_1 ⟨0, Nat.zero_lt_succ 0⟩
      exact hforall_total F (hx_1 ⟨0, Nat.zero_lt_succ 0⟩).1
    · nomatch hlen_pos (Nat.zero_lt_succ 0)
  have hden :
      ∃ a : ZFSet,
        ∃ h : a ∈ ⟦(.fun (.fun β.toSMTType .bool) .bool)⟧ᶻ,
          ⟦tpow.abstract Δ_ctx hΔ_covers_tpow⟧ˢ =
            some ⟨a, ⟨(.fun (.fun β.toSMTType .bool) .bool), h⟩⟩ := by
    obtain ⟨D, hD⟩ := Option.isSome_iff_exists.mp hsome_tpow
    obtain ⟨a, τa, ha⟩ := D
    have hτa : τa = .fun (.fun β.toSMTType .bool) .bool := by
      exact denote_type_eq_of_typing (typ_t := typ_tpow) (hden := hD)
    cases hτa
    exact ⟨a, ha, hD⟩
  rcases hden with ⟨a, h, hden⟩
  refine ⟨a, .fun (.fun β.toSMTType .bool) .bool, h, hden, ?_⟩
  rw [RDom]
  constructor
  · rfl
  · classical
    have ha_func : ZFSet.IsFunc ⟦β.set.toSMTType⟧ᶻ ⟦SMTType.bool⟧ᶻ a := by
      have ha_mem : a ∈ ⟦β.set.toSMTType⟧ᶻ.funs ⟦SMTType.bool⟧ᶻ := by
        simpa [BType.toSMTType, SMTType.toZFSet] using h
      rw [ZFSet.mem_funs] at ha_mem
      exact ha_mem
    have hSval_func :
        ZFSet.IsFunc ⟦β.toSMTType⟧ᶻ ⟦SMTType.bool⟧ᶻ Sval := by
      have hSval_mem : Sval ∈ ⟦β.toSMTType⟧ᶻ.funs ⟦SMTType.bool⟧ᶻ := by
        simpa [BType.toSMTType, SMTType.toZFSet] using hSval
      rw [ZFSet.mem_funs] at hSval_mem
      exact hSval_mem
    let setDom : ∀ {Y : ZFSet}, Y ∈ ⟦β.set⟧ᶻ → SMT.Dom
      | Y, hY_mem =>
          ⟨ZFSet.fapply (BType.canonicalIsoSMTType β.set).1
              (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType β.set).2.1)
              ⟨Y, by rwa [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType β.set).2.1]⟩,
            β.set.toSMTType,
            fapply_mem_range _ _⟩
    let elemDom : ∀ {y : ZFSet}, y ∈ ⟦β⟧ᶻ → SMT.Dom
      | y, hy =>
          ⟨ZFSet.fapply (BType.canonicalIsoSMTType β).1
              (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType β).2.1)
              ⟨y, by rwa [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType β).2.1]⟩,
            β.toSMTType,
            fapply_mem_range _ _⟩
    have setDom_ty {Y : ZFSet} (hY_mem : Y ∈ ⟦β.set⟧ᶻ) :
        (setDom hY_mem).snd.fst = β.toSMTType.fun SMTType.bool := by
      rfl
    have setDom_mem {Y : ZFSet} (hY_mem : Y ∈ ⟦β.set⟧ᶻ) :
        (setDom hY_mem).fst ∈ ⟦β.toSMTType.fun SMTType.bool⟧ᶻ := by
      simp only [SMTType.toZFSet, BType.toSMTType, SetLike.coe_mem, setDom]
    have setDom_func {Y : ZFSet} (hY_mem : Y ∈ ⟦β.set⟧ᶻ) :
        ZFSet.IsFunc ⟦β.toSMTType⟧ᶻ ⟦SMTType.bool⟧ᶻ (setDom hY_mem).fst := by
      have hset_mem :
          (setDom hY_mem).fst ∈ ⟦β.toSMTType⟧ᶻ.funs ⟦SMTType.bool⟧ᶻ := by
        simp only [SMTType.toZFSet, BType.toSMTType, SetLike.coe_mem, setDom]
      rw [ZFSet.mem_funs] at hset_mem
      exact hset_mem
    have setDom_retract {Y : ZFSet} (hY_mem : Y ∈ ⟦β.set⟧ᶻ) :
        retract β.set (setDom hY_mem).fst = Y := by
      simpa [setDom] using (retract_of_canonical (τ := β.set) hY_mem rfl)
    have elemDom_ty {y : ZFSet} (hy : y ∈ ⟦β⟧ᶻ) :
        (elemDom hy).snd.fst = β.toSMTType := by
      rfl
    have elemDom_mem {y : ZFSet} (hy : y ∈ ⟦β⟧ᶻ) :
        (elemDom hy).fst ∈ ⟦β.toSMTType⟧ᶻ := by
      simp only [elemDom, SetLike.coe_mem]
    have elemDom_retract {y : ZFSet} (hy : y ∈ ⟦β⟧ᶻ) :
        retract β (elemDom hy).fst = y := by
      simpa [elemDom] using (retract_of_canonical (τ := β) hy rfl)
    have hgo_cov_pred :
        ∀ F : SMT.Dom, ∀ z ∈ SMT.fv pred, z ∉ [x] →
          (Function.update Δ_ctx E (some F) z).isSome = true := by
      intro F z hz hzx
      have hzx' : z ≠ x := by
        simpa [List.mem_singleton] using hzx
      have hcov :=
        hcov_pred_upd F
          ⟨β.toSMTType.defaultZFSet, β.toSMTType,
            SMTType.mem_toZFSet_of_defaultZFSet⟩ z hz
      simpa [Function.update_of_ne hzx'] using hcov
    have hcov_unf' : RenamingContext.CoversFV Δ_ctx
        ((λˢ [E]) [β.toSMTType.fun SMTType.bool] (Term.forall [x] [β.toSMTType] pred)) :=
      htpow_def ▸ hΔ_covers_tpow
    have habstr_eq' : tpow.abstract Δ_ctx hΔ_covers_tpow =
        ((λˢ [E]) [β.toSMTType.fun SMTType.bool] (Term.forall [x] [β.toSMTType] pred)).abstract
          Δ_ctx hcov_unf' := by
      cases htpow_def; rfl
    have hden' : ⟦((λˢ [E]) [β.toSMTType.fun SMTType.bool] (Term.forall [x] [β.toSMTType] pred)).abstract
        Δ_ctx hcov_unf'⟧ˢ = some ⟨a, ⟨.fun (.fun β.toSMTType .bool) .bool, h⟩⟩ :=
      habstr_eq' ▸ hden
    rw [SMT.Term.abstract, dif_pos (by rfl), SMT.denote] at hden'
    split_ifs at hden' with hlen_pos den_t_isSome den_t_typ_det
    · simp at hden'
      let defaultArg : Fin [E].length → SMT.Dom := fun i =>
        ⟨[β.toSMTType.fun SMTType.bool][↑i].defaultZFSet,
          ⟨[β.toSMTType.fun SMTType.bool][↑i],
            SMTType.mem_toZFSet_of_defaultZFSet⟩⟩
      have hdefaultArg :
          ∀ i : Fin [E].length,
            ((defaultArg i).snd.fst =
                match i with
                | ⟨i, _⟩ => [β.toSMTType.fun SMTType.bool][i]) ∧
              (defaultArg i).fst ∈
                ⟦match i with
                  | ⟨i, _⟩ => [β.toSMTType.fun SMTType.bool][i]⟧ᶻ := by
        rintro ⟨i, hi⟩
        have hi0 : i = 0 := by
          simp at hi
          exact hi
        have hiFin : (⟨i, hi⟩ : Fin [E].length) = ⟨0, by simp⟩ := by
          apply Fin.ext
          exact hi0
        cases hiFin
        exact ⟨rfl, SMTType.mem_toZFSet_of_defaultZFSet⟩
      set γ : SMTType :=
        ((⟦(SMT.Term.abstract.go
              (Term.forall [x] [β.toSMTType] pred) [E] Δ_ctx hgo_cov_forall).uncurry
            defaultArg⟧ˢ).get
          (den_t_isSome hdefaultArg)).snd.fst
      let argOk : ZFSet → Prop := fun x_1 =>
        x_1.hasArity 1 ∧
          ZFSet.IsFunc ⟦β.toSMTType⟧ᶻ ⟦SMTType.bool⟧ᶻ x_1
      set bodyFun : ZFSet → ZFSet := fun x_1 =>
        if hx : argOk x_1 then
          let hx_mem : x_1 ∈ ⟦β.toSMTType.fun SMTType.bool⟧ᶻ := by
            simpa [SMTType.toZFSet, ZFSet.mem_funs] using hx.2
          ((⟦(SMT.Term.abstract.go
                (Term.forall [x] [β.toSMTType] pred) [E] Δ_ctx hgo_cov_forall).uncurry
              (fun _ => ⟨x_1, ⟨β.toSMTType.fun SMTType.bool, hx_mem⟩⟩)⟧ˢ).get
            (den_t_isSome (by
              rintro ⟨i, hi⟩
              have hi0 : i = 0 := by
                simp at hi
                exact hi
              subst i
              exact ⟨rfl, hx_mem⟩))).fst
        else
          γ.defaultZFSet
      have ha_eq :
          ⟦β.toSMTType.fun SMTType.bool⟧ᶻ.lambda ⟦γ⟧ᶻ bodyFun = a := by
        simpa [γ, argOk, bodyFun, defaultArg, SMTType.toZFSet, ZFSet.mem_funs]
          using hden'.1
      have hbody_range :
          ∀ {x_1 : ZFSet}, x_1 ∈ ⟦β.toSMTType.fun SMTType.bool⟧ᶻ →
            bodyFun x_1 ∈ ⟦γ⟧ᶻ := by
        intro x_1 hx_1
        by_cases hx : argOk x_1
        · have hx_mem : x_1 ∈ ⟦β.toSMTType.fun SMTType.bool⟧ᶻ := by
            simpa [SMTType.toZFSet, ZFSet.mem_funs] using hx.2
          let Dx : SMT.Dom :=
            ((⟦(SMT.Term.abstract.go
                  (Term.forall [x] [β.toSMTType] pred) [E] Δ_ctx hgo_cov_forall).uncurry
                (fun _ => ⟨x_1, ⟨β.toSMTType.fun SMTType.bool, hx_mem⟩⟩)⟧ˢ).get
              (den_t_isSome (by
                rintro ⟨i, hi⟩
                have hi0 : i = 0 := by
                  simp at hi
                  exact hi
                subst i
                exact ⟨rfl, hx_mem⟩)))
          have hDx_ty : Dx.snd.fst = γ := by
            dsimp [Dx, γ]
            exact den_t_typ_det
              (fun _ => ⟨x_1, ⟨β.toSMTType.fun SMTType.bool, hx_mem⟩⟩)
              defaultArg
              (by
                rintro ⟨i, hi⟩
                have hi0 : i = 0 := by
                  simp at hi
                  exact hi
                subst i
                exact ⟨rfl, hx_mem⟩)
              hdefaultArg
          have hDx_mem : Dx.fst ∈ ⟦γ⟧ᶻ := by
            simpa [hDx_ty] using Dx.snd.snd
          simpa [bodyFun, hx, hx_mem, Dx] using hDx_mem
        · simpa [bodyFun, hx] using
            (SMTType.mem_toZFSet_of_defaultZFSet (α := γ))
      have hAppEqForall :
          ∀ {Y : ZFSet} (hY_mem : Y ∈ ⟦β.set⟧ᶻ),
            let FY := setDom hY_mem
            ∃ Dforall : SMT.Dom,
              ⟦(Term.forall [x] [β.toSMTType] pred).abstract
                  (Function.update Δ_ctx E (some FY)) (hcov_forall_upd FY)⟧ˢ =
                some Dforall ∧
                ZFSet.fapply a (ZFSet.is_func_is_pfunc ha_func)
                  ⟨FY.fst, by
                    rw [ZFSet.is_func_dom_eq ha_func]
                    exact setDom_mem hY_mem⟩ = Dforall.fst := by
        intro Y hY_mem
        let FY := setDom hY_mem
        obtain ⟨Dforall, hden_forall⟩ := Option.isSome_iff_exists.mp
          (hforall_total FY (setDom_ty hY_mem))
        have htarget :=
          funUnaryTarget (α := β.toSMTType.fun SMTType.bool) (setDom_mem hY_mem)
        have hFY_ok : argOk FY.fst := by
          constructor
          · exact htarget.1
          · exact setDom_func hY_mem
        have hgo_FY :=
          funAbstractGoSingle
            (Δctx := Δ_ctx) (P := Term.forall [x] [β.toSMTType] pred)
            (v := E) (τ := β.toSMTType.fun SMTType.bool)
            hgo_cov_forall hcov_forall_upd (fun _ => FY) (by
              intro i
              have hi0 : i = ⟨0, by simp⟩ := by
                apply Fin.ext
                simp
              cases hi0
              exact ⟨rfl, setDom_mem hY_mem⟩)
        have hden_go_FY :
            ⟦(SMT.Term.abstract.go
                (Term.forall [x] [β.toSMTType] pred) [E] Δ_ctx
                hgo_cov_forall).uncurry (fun _ => FY)⟧ˢ =
              some Dforall := by
          rw [hgo_FY]
          simpa [FY, proof_irrel_heq] using hden_forall
        have hγ_eq_bool : γ = SMTType.bool := by
          have hFY_arg :
              ∀ i : Fin [E].length,
                (((fun _ => FY) i).snd.fst =
                    match i with
                    | ⟨i, _⟩ => [β.toSMTType.fun SMTType.bool][i]) ∧
                  (((fun _ => FY) i).fst ∈
                    ⟦match i with
                      | ⟨i, _⟩ => [β.toSMTType.fun SMTType.bool][i]⟧ᶻ) := by
            rintro ⟨i, hi⟩
            have hi0 : i = 0 := by
              simp at hi
              exact hi
            have hiFin : (⟨i, hi⟩ : Fin [E].length) = ⟨0, by simp⟩ := by
              apply Fin.ext
              exact hi0
            cases hiFin
            exact ⟨rfl, setDom_mem hY_mem⟩
          have hDforall_ty : Dforall.snd.fst = SMTType.bool := by
            exact denote_type_eq_of_typing (typ_t := typ_forall) (hden := hden_forall)
          have hγ_eq_Dforall_ty :
              ((⟦(SMT.Term.abstract.go
                  (Term.forall [x] [β.toSMTType] pred) [E] Δ_ctx
                  hgo_cov_forall).uncurry defaultArg⟧ˢ).get
                  (den_t_isSome hdefaultArg)).snd.fst =
                Dforall.snd.fst := by
            calc
              ((⟦(SMT.Term.abstract.go
                  (Term.forall [x] [β.toSMTType] pred) [E] Δ_ctx
                  hgo_cov_forall).uncurry defaultArg⟧ˢ).get
                  (den_t_isSome hdefaultArg)).snd.fst
                  =
                ((⟦(SMT.Term.abstract.go
                  (Term.forall [x] [β.toSMTType] pred) [E] Δ_ctx
                  hgo_cov_forall).uncurry (fun _ => FY)⟧ˢ).get
                  (den_t_isSome hFY_arg)).snd.fst := by
                    exact den_t_typ_det defaultArg (fun _ => FY)
                      hdefaultArg hFY_arg
              _ = Dforall.snd.fst := by
                    exact congrArg (fun d : SMT.Dom => d.snd.fst)
                      (Option.get_of_eq_some (den_t_isSome hFY_arg) hden_go_FY)
          unfold γ
          exact hγ_eq_Dforall_ty.trans hDforall_ty
        refine ⟨Dforall, hden_forall, ?_⟩
        have hLamFunc :
            ZFSet.IsFunc ⟦β.toSMTType.fun SMTType.bool⟧ᶻ ⟦γ⟧ᶻ
              (⟦β.toSMTType.fun SMTType.bool⟧ᶻ.lambda ⟦γ⟧ᶻ bodyFun) := by
          apply ZFSet.lambda_isFunc
          intro z hz
          exact hbody_range hz
        have hbody_range_bool :
            ∀ {x_1 : ZFSet}, x_1 ∈ ⟦β.toSMTType.fun SMTType.bool⟧ᶻ →
              bodyFun x_1 ∈ ⟦SMTType.bool⟧ᶻ := by
          intro x_1 hx_1
          simpa [hγ_eq_bool] using hbody_range hx_1
        have hLamFuncBool' :
            ZFSet.IsFunc ⟦β.toSMTType.fun SMTType.bool⟧ᶻ ⟦SMTType.bool⟧ᶻ
              (⟦β.toSMTType.fun SMTType.bool⟧ᶻ.lambda
                ⟦SMTType.bool⟧ᶻ bodyFun) := by
          exact ZFSet.lambda_isFunc (fun {z} hz => hbody_range_bool hz)
        have hden_go_FY_isSome :
            ⟦(SMT.Term.abstract.go
                (Term.forall [x] [β.toSMTType] pred) [E] Δ_ctx
                hgo_cov_forall).uncurry (fun _ => FY)⟧ˢ.isSome = true := by
          exact den_t_isSome (by
            rintro ⟨i, hi⟩
            have hi0 : i = 0 := by
              simp at hi
              exact hi
            subst i
            exact ⟨rfl, setDom_mem hY_mem⟩)
        have hget_go_FY :
            ((⟦(SMT.Term.abstract.go
                (Term.forall [x] [β.toSMTType] pred) [E] Δ_ctx
                hgo_cov_forall).uncurry (fun _ => FY)⟧ˢ).get
              hden_go_FY_isSome).fst = Dforall.fst := by
          exact congrArg (fun d : SMT.Dom => d.fst)
            (Option.get_of_eq_some hden_go_FY_isSome hden_go_FY)
        have happ_lambda_bool :
            ZFSet.fapply
              (⟦β.toSMTType.fun SMTType.bool⟧ᶻ.lambda
                ⟦SMTType.bool⟧ᶻ bodyFun)
              (ZFSet.is_func_is_pfunc hLamFuncBool')
              ⟨FY.fst, by
                rw [ZFSet.is_func_dom_eq hLamFuncBool']
                exact setDom_mem hY_mem⟩ = Dforall.fst := by
          rw [ZFSet.fapply_lambda
            (hf := by
              intro z hz
              exact hbody_range_bool hz)
            (ha := setDom_mem hY_mem)]
          simpa [FY, bodyFun, hFY_ok, proof_irrel_heq] using hget_go_FY
        have ha_eq_bool :
            a =
              (⟦β.toSMTType.fun SMTType.bool⟧ᶻ.lambda
                ⟦SMTType.bool⟧ᶻ bodyFun) := by
          simpa [hγ_eq_bool] using ha_eq.symm
        have happ_a_eq_lambda :
            ZFSet.fapply a (ZFSet.is_func_is_pfunc ha_func)
                ⟨FY.fst, by
                  rw [ZFSet.is_func_dom_eq ha_func]
                  exact setDom_mem hY_mem⟩ =
              ZFSet.fapply
                (⟦β.toSMTType.fun SMTType.bool⟧ᶻ.lambda
                  ⟦SMTType.bool⟧ᶻ bodyFun)
                (ZFSet.is_func_is_pfunc hLamFuncBool')
                ⟨FY.fst, by
                  rw [ZFSet.is_func_dom_eq hLamFuncBool']
                  exact setDom_mem hY_mem⟩ := by
          cases ha_eq_bool
          rfl
        change
          (((ZFSet.fapply a (ZFSet.is_func_is_pfunc ha_func)
              ⟨FY.fst, by
                rw [ZFSet.is_func_dom_eq ha_func]
                exact setDom_mem hY_mem⟩) : {x // x ∈ ⟦SMTType.bool⟧ᶻ}) : ZFSet)
            = Dforall.fst
        calc
          (((ZFSet.fapply a (ZFSet.is_func_is_pfunc ha_func)
              ⟨FY.fst, by
                rw [ZFSet.is_func_dom_eq ha_func]
                exact setDom_mem hY_mem⟩) : {x // x ∈ ⟦SMTType.bool⟧ᶻ}) : ZFSet) =
            (((ZFSet.fapply
                (⟦β.toSMTType.fun SMTType.bool⟧ᶻ.lambda
                  ⟦SMTType.bool⟧ᶻ bodyFun)
                (ZFSet.is_func_is_pfunc hLamFuncBool')
                ⟨FY.fst, by
                  rw [ZFSet.is_func_dom_eq hLamFuncBool']
                  exact setDom_mem hY_mem⟩) : {x // x ∈ ⟦SMTType.bool⟧ᶻ}) : ZFSet) := by
              exact congrArg Subtype.val happ_a_eq_lambda
          _ = Dforall.fst := happ_lambda_bool
      ext Y
      constructor
      swap
      · intro hY
        rw [ZFSet.mem_powerset] at hY
        have hY_mem : Y ∈ ⟦β.set⟧ᶻ := by
          rw [BType.toZFSet, ZFSet.mem_powerset] at hX ⊢
          intro z hz
          exact hX (hY hz)
        apply (mem_retract_set_iff_app_canonical_eq_zftrue
          (α := β.set) ha_func rfl hY_mem).mpr
        obtain ⟨Dforall, hden_forall, happ_eq⟩ := hAppEqForall hY_mem
        rw [happ_eq]
        have hforall_true_den :
            ⟦(Term.forall [x] [β.toSMTType] pred).abstract
                (Function.update Δ_ctx E (some (setDom hY_mem)))
                (hcov_forall_upd (setDom hY_mem))⟧ˢ =
              some ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
          refine funUnaryForallEqZftrue
            (Δctx := Function.update Δ_ctx E (some (setDom hY_mem)))
            (a := pred) (v := x) (τ := β.toSMTType)
            (hφ_forall := hcov_forall_upd (setDom hY_mem))
            (hgo_cov := hgo_cov_pred (setDom hY_mem))
            (hcov_a_upd := hcov_pred_upd (setDom hY_mem))
            (hbody_total := by
              intro W hW_ty
              exact hpred_total (setDom hY_mem) W (setDom_ty hY_mem) hW_ty)
            (hbody_ty := by
              intro W hW_ty D hden_body
              exact hpred_ty (setDom hY_mem) W (setDom_ty hY_mem) hW_ty
                hden_body)
            (hbody_true := by
              intro W hW_ty
              have hE_ne_x : E ≠ x := by
                intro hEx
                exact hx_ne_E hEx.symm
              have hW_mem : W.fst ∈ ⟦β.toSMTType⟧ᶻ := by
                simpa [hW_ty] using W.snd.snd
              have hW_retract_mem : retract β W.fst ∈ ⟦β⟧ᶻ := by
                exact retract_mem_of_toSMTType hW_mem
              have hcanonW :
                  (elemDom hW_retract_mem).fst = W.fst := by
                simpa [elemDom] using canonical_of_retract β hW_mem
              have hcanonW_zf :
                  ZFSet.fapply (BType.canonicalIsoSMTType β).1
                    (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType β).2.1)
                    ⟨retract β W.fst, by
                      rw [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType β).2.1]
                      exact hW_retract_mem⟩ = W.fst := by
                simpa using canonical_of_retract β hW_mem
              obtain ⟨_, Dlhs, hDlhs_ty, hDlhs_val, hden_lhs⟩ :=
                funDenoteAppAt
                  (Δctx := Function.update Δ_ctx E (some (setDom hY_mem)))
                  (t := .var E) (x := x)
                  (α := β.toSMTType) (β := SMTType.bool)
                  (Y := setDom hY_mem)
                  (hcov_t_upd := by
                    intro Xarg v hv
                    rw [SMT.fv, List.mem_singleton] at hv
                    subst hv
                    rw [Function.update_of_ne hE_ne_x, Function.update_self]
                    simp)
                  (den_t_upd := by
                    intro Xarg
                    rw [SMT.Term.abstract.eq_def, SMT.denote, Option.pure_def,
                      Option.some.injEq]
                    apply Option.get_of_eq_some
                    rw [Function.update_of_ne hE_ne_x, Function.update_self])
                  (hY_ty := setDom_ty hY_mem)
                  (hY_func := setDom_func hY_mem)
                  (Xarg := W)
                  (hXarg_ty := hW_ty)
                  (hXarg_mem := hW_mem)
              have hcov_S_enc_E :
                  RenamingContext.CoversFV
                    (Function.update Δ_ctx E (some (setDom hY_mem))) S_enc := by
                exact SMT.RenamingContext.coversFV_update_of_notMem
                  (x := E) (d := setDom hY_mem) hE_not_mem_fv_S_enc hΔ_covers_S
              have den_S_E :
                  ⟦S_enc.abstract
                      (Function.update Δ_ctx E (some (setDom hY_mem)))
                      hcov_S_enc_E⟧ˢ =
                    some ⟨Sval, ⟨β.set.toSMTType, hSval⟩⟩ := by
                have hden_S_E_raw :
                    ⟦S_enc.abstract Δ_ctx hΔ_covers_S⟧ˢ =
                      ⟦S_enc.abstract
                          (Function.update Δ_ctx E (some (setDom hY_mem)))
                          hcov_S_enc_E⟧ˢ := by
                  simpa [SMT.RenamingContext.denote] using
                    (SMT.RenamingContext.denote_update_of_notMem
                      («Δ» := Δ_ctx) (t := S_enc) (x := E) (d := setDom hY_mem)
                      (h := hΔ_covers_S) hE_not_mem_fv_S_enc)
                rw [←hden_S_E_raw]
                simpa [SMT.RenamingContext.denote] using den_S
              obtain ⟨_, Drhs, hDrhs_ty, hDrhs_val, hden_rhs⟩ :=
                funDenoteAppAt
                  (Δctx := Function.update Δ_ctx E (some (setDom hY_mem)))
                  (t := S_enc) (x := x)
                  (α := β.toSMTType) (β := SMTType.bool)
                  (Y := ⟨Sval, ⟨β.set.toSMTType, hSval⟩⟩)
                  (hcov_t_upd := by
                    intro Xarg
                    exact SMT.RenamingContext.coversFV_update_of_notMem
                      (x := x) (d := Xarg) hx_not_mem_fv_S_enc hcov_S_enc_E)
                  (den_t_upd := by
                    intro Xarg
                    have hden_S_EX_raw :
                        ⟦S_enc.abstract
                            (Function.update Δ_ctx E (some (setDom hY_mem)))
                            hcov_S_enc_E⟧ˢ =
                          ⟦S_enc.abstract
                              (Function.update
                                (Function.update Δ_ctx E (some (setDom hY_mem))) x
                                (some Xarg))
                              (SMT.RenamingContext.coversFV_update_of_notMem
                                (x := x) (d := Xarg) hx_not_mem_fv_S_enc
                                hcov_S_enc_E)⟧ˢ := by
                      simpa [SMT.RenamingContext.denote] using
                        (SMT.RenamingContext.denote_update_of_notMem
                          («Δ» := Function.update Δ_ctx E (some (setDom hY_mem)))
                          (t := S_enc) (x := x) (d := Xarg)
                          (h := hcov_S_enc_E) hx_not_mem_fv_S_enc)
                    rw [←hden_S_EX_raw]
                    exact den_S_E)
                  (hY_ty := rfl)
                  (hY_func := hSval_func)
                  (Xarg := W)
                  (hXarg_ty := hW_ty)
                  (hXarg_mem := hW_mem)
              have hDlhs_mem_bool : Dlhs.fst ∈ 𝔹 := by
                simpa [hDlhs_ty] using Dlhs.snd.snd
              have hDlhs_bool : Dlhs.fst = zftrue ∨ Dlhs.fst = zffalse := by
                simpa [ZFSet.ZFBool.mem_𝔹_iff, or_comm] using hDlhs_mem_bool
              rcases hDlhs_bool with hDlhs_true | hDlhs_false
              · have hmemY : retract β W.fst ∈ Y := by
                  apply (mem_retract_set_iff_app_canonical_eq_zftrue
                    (α := β) (setDom_func hY_mem) (setDom_retract hY_mem)
                    hW_retract_mem).mpr
                  simpa [proof_irrel_heq, hcanonW_zf] using
                    (hDlhs_val.symm.trans hDlhs_true)
                have hmemX : retract β W.fst ∈ X := hY hmemY
                have hDrhs_true : Drhs.fst = zftrue := by
                  have hSval_true := (mem_retract_set_iff_app_canonical_eq_zftrue
                    (α := β) hSval_func retract_eq hW_retract_mem).mp hmemX
                  simpa [proof_irrel_heq, hcanonW_zf, hDrhs_val] using hSval_true
                have hden_not_rhs_false :
                    ⟦(¬ˢ ((@ˢS_enc) (SMT.Term.var x))).abstract
                        (Function.update
                          (Function.update Δ_ctx E (some (setDom hY_mem))) x (some W))
                        (by
                          intro v hv
                          have hv' : v ∈ SMT.fv ((@ˢS_enc) (SMT.Term.var x)) := by
                            simpa [SMT.fv] using hv
                          have hv'' : v ∈ SMT.fv S_enc ∨ v = x := by
                            simpa [SMT.fv] using hv'
                          exact hcov_pred_upd (setDom hY_mem) W v (by
                            rw [hpred_def]
                            simp only [SMT.fv, List.mem_append, List.mem_singleton]
                            exact Or.inr hv''))⟧ˢ =
                      some ⟨zffalse, SMTType.bool,
                        ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
                  simpa [SMT.Term.abstract, proof_irrel_heq] using
                    denote_not_eq_zffalse_of_some_zftrue hden_rhs hDrhs_ty hDrhs_true
                have hden_body_false :
                    ⟦(((@ˢSMT.Term.var E) (SMT.Term.var x)) ∧ˢ
                          (¬ˢ ((@ˢS_enc) (SMT.Term.var x)))).abstract
                        (Function.update
                          (Function.update Δ_ctx E (some (setDom hY_mem))) x (some W))
                        (by
                          intro v hv
                          exact hcov_pred_upd (setDom hY_mem) W v (by
                            rw [hpred_def]
                            simpa [SMT.fv] using hv))⟧ˢ =
                      some ⟨zffalse, SMTType.bool,
                        ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
                  simpa [SMT.Term.abstract, proof_irrel_heq] using
                    denote_and_eq_zffalse_of_some_zffalse_right
                      hden_lhs hDlhs_ty hden_not_rhs_false rfl rfl
                refine ⟨⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩, ?_, rfl⟩
                simpa [hpred_def, SMT.Term.abstract, proof_irrel_heq] using
                  denote_not_eq_zftrue_of_some_zffalse hden_body_false rfl rfl
              · have hnot_isSome :
                    ⟦(¬ˢ ((@ˢS_enc) (SMT.Term.var x))).abstract
                        (Function.update
                          (Function.update Δ_ctx E (some (setDom hY_mem))) x
                          (some W))
                        (by
                          intro v hv
                          have hv' : v ∈ SMT.fv ((@ˢS_enc) (SMT.Term.var x)) := by
                            simpa [SMT.fv] using hv
                          have hv'' : v ∈ SMT.fv S_enc ∨ v = x := by
                            simpa [SMT.fv] using hv'
                          exact hcov_pred_upd (setDom hY_mem) W v (by
                            rw [hpred_def]
                            simp only [SMT.fv, List.mem_append, List.mem_singleton]
                            exact Or.inr hv''))⟧ˢ.isSome = true := by
                    simpa [SMT.Term.abstract, proof_irrel_heq] using
                      (denote_not_isSome_of_some_bool (hden := hden_rhs)
                        (hTy := hDrhs_ty))
                obtain ⟨Dnot, hden_not⟩ := Option.isSome_iff_exists.mp hnot_isSome
                have hDnot_ty : Dnot.snd.fst = SMTType.bool := by
                  exact denote_type_eq_of_typing (typ_t := typ_not_rhs) (hden := hden_not)
                have hden_body_false :
                    ⟦(((@ˢSMT.Term.var E) (SMT.Term.var x)) ∧ˢ
                          (¬ˢ ((@ˢS_enc) (SMT.Term.var x)))).abstract
                        (Function.update
                          (Function.update Δ_ctx E (some (setDom hY_mem))) x (some W))
                        (by
                          intro v hv
                          exact hcov_pred_upd (setDom hY_mem) W v (by
                            rw [hpred_def]
                            simpa [SMT.fv] using hv))⟧ˢ =
                      some ⟨zffalse, SMTType.bool,
                        ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
                  simpa [SMT.Term.abstract, proof_irrel_heq] using
                    denote_and_eq_zffalse_of_some_zffalse_left
                      hden_lhs hDlhs_ty hDlhs_false hden_not hDnot_ty
                refine ⟨⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩, ?_, rfl⟩
                simpa [hpred_def, SMT.Term.abstract, proof_irrel_heq] using
                  denote_not_eq_zftrue_of_some_zffalse hden_body_false rfl rfl
            )
        have hDforall_eq : Dforall = ⟨zftrue, SMTType.bool,
              ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
          exact Option.some.inj (hden_forall.symm.trans hforall_true_den)
        simpa using congrArg (fun d => d.fst) hDforall_eq
      · intro hY
        have hY_mem : Y ∈ ⟦β.set⟧ᶻ := by
          have hY' := hY
          unfold retract at hY'
          exact (ZFSet.mem_sep.mp hY').1
        have happ_true :
            ZFSet.fapply a (ZFSet.is_func_is_pfunc ha_func)
              ⟨(setDom hY_mem).fst, by
                rw [ZFSet.is_func_dom_eq ha_func]
                exact setDom_mem hY_mem⟩ = zftrue := by
          exact (mem_retract_set_iff_app_canonical_eq_zftrue
            (α := β.set) ha_func rfl hY_mem).mp hY
        rw [ZFSet.mem_powerset]
        intro y hy
        have hY_subset : Y ⊆ ⟦β⟧ᶻ := by
          simpa [BType.toZFSet, ZFSet.mem_powerset] using hY_mem
        have hy_mem : y ∈ ⟦β⟧ᶻ := hY_subset hy
        obtain ⟨Dforall, hden_forall, happ_eq⟩ := hAppEqForall hY_mem
        have hforall_true : Dforall.fst = zftrue := by
          rw [←happ_eq]
          exact happ_true
        have hbody_total' :
            ∀ W : SMT.Dom,
              W.snd.fst = β.toSMTType →
                ⟦pred.abstract
                    (Function.update
                      (Function.update Δ_ctx E (some (setDom hY_mem))) x
                      (some W))
                    (hcov_pred_upd (setDom hY_mem) W)⟧ˢ.isSome = true := by
          intro W hW_ty
          exact hpred_total (setDom hY_mem) W (setDom_ty hY_mem) hW_ty
        have hbody_ty' :
            ∀ W : SMT.Dom,
              W.snd.fst = β.toSMTType →
                ∀ {D : SMT.Dom},
                  ⟦pred.abstract
                      (Function.update
                        (Function.update Δ_ctx E (some (setDom hY_mem))) x
                        (some W))
                      (hcov_pred_upd (setDom hY_mem) W)⟧ˢ =
                    some D →
                      D.snd.fst = SMTType.bool := by
          intro W hW_ty D hden_body
          exact hpred_ty (setDom hY_mem) W (setDom_ty hY_mem) hW_ty
            hden_body
        have hpred_true :=
          funUnaryForallTrueImpliesAt
            (Δctx := Function.update Δ_ctx E (some (setDom hY_mem)))
            (a := pred) (v := x) (τ := β.toSMTType)
            (hcov_forall_upd (setDom hY_mem))
            (hgo_cov_pred (setDom hY_mem))
            (hcov_pred_upd (setDom hY_mem))
            hbody_total' hbody_ty'
            hden_forall hforall_true (elemDom hy_mem) (elemDom_ty hy_mem)
        rcases hpred_true with ⟨Dpred, hden_pred, hDpred_true⟩
        have hE_ne_x : E ≠ x := by
          intro hEx
          exact hx_ne_E hEx.symm
        have hWy_mem : (elemDom hy_mem).fst ∈ ⟦β.toSMTType⟧ᶻ := elemDom_mem hy_mem
        obtain ⟨_, Dlhs, hDlhs_ty, hDlhs_val, hden_lhs⟩ :=
          funDenoteAppAt
            (Δctx := Function.update Δ_ctx E (some (setDom hY_mem)))
            (t := .var E) (x := x)
            (α := β.toSMTType) (β := SMTType.bool)
            (Y := setDom hY_mem)
            (hcov_t_upd := by
              intro Xarg v hv
              rw [SMT.fv, List.mem_singleton] at hv
              subst hv
              rw [Function.update_of_ne hE_ne_x, Function.update_self]
              simp)
            (den_t_upd := by
              intro Xarg
              rw [SMT.Term.abstract.eq_def, SMT.denote, Option.pure_def,
                Option.some.injEq]
              apply Option.get_of_eq_some
              rw [Function.update_of_ne hE_ne_x, Function.update_self])
            (hY_ty := setDom_ty hY_mem)
            (hY_func := setDom_func hY_mem)
            (Xarg := elemDom hy_mem)
            (hXarg_ty := elemDom_ty hy_mem)
            (hXarg_mem := hWy_mem)
        have hcov_S_enc_E :
            RenamingContext.CoversFV
              (Function.update Δ_ctx E (some (setDom hY_mem))) S_enc := by
          exact SMT.RenamingContext.coversFV_update_of_notMem
            (x := E) (d := setDom hY_mem) hE_not_mem_fv_S_enc hΔ_covers_S
        have den_S_E :
            ⟦S_enc.abstract
                (Function.update Δ_ctx E (some (setDom hY_mem)))
                hcov_S_enc_E⟧ˢ =
              some ⟨Sval, ⟨β.set.toSMTType, hSval⟩⟩ := by
          have hden_S_E_raw :
              ⟦S_enc.abstract Δ_ctx hΔ_covers_S⟧ˢ =
                ⟦S_enc.abstract
                    (Function.update Δ_ctx E (some (setDom hY_mem)))
                    hcov_S_enc_E⟧ˢ := by
            simpa [SMT.RenamingContext.denote] using
              (SMT.RenamingContext.denote_update_of_notMem
                («Δ» := Δ_ctx) (t := S_enc) (x := E) (d := setDom hY_mem)
                (h := hΔ_covers_S) hE_not_mem_fv_S_enc)
          rw [←hden_S_E_raw]
          simpa [SMT.RenamingContext.denote] using den_S
        obtain ⟨_, Drhs, hDrhs_ty, hDrhs_val, hden_rhs⟩ :=
          funDenoteAppAt
            (Δctx := Function.update Δ_ctx E (some (setDom hY_mem)))
            (t := S_enc) (x := x)
            (α := β.toSMTType) (β := SMTType.bool)
            (Y := ⟨Sval, ⟨β.set.toSMTType, hSval⟩⟩)
            (hcov_t_upd := by
              intro Xarg
              exact SMT.RenamingContext.coversFV_update_of_notMem
                (x := x) (d := Xarg) hx_not_mem_fv_S_enc hcov_S_enc_E)
            (den_t_upd := by
              intro Xarg
              have hden_S_EX_raw :
                  ⟦S_enc.abstract
                      (Function.update Δ_ctx E (some (setDom hY_mem)))
                      hcov_S_enc_E⟧ˢ =
                    ⟦S_enc.abstract
                        (Function.update
                          (Function.update Δ_ctx E (some (setDom hY_mem))) x
                          (some Xarg))
                        (SMT.RenamingContext.coversFV_update_of_notMem
                          (x := x) (d := Xarg) hx_not_mem_fv_S_enc
                          hcov_S_enc_E)⟧ˢ := by
                simpa [SMT.RenamingContext.denote] using
                  (SMT.RenamingContext.denote_update_of_notMem
                    («Δ» := Function.update Δ_ctx E (some (setDom hY_mem)))
                    (t := S_enc) (x := x) (d := Xarg)
                    (h := hcov_S_enc_E) hx_not_mem_fv_S_enc)
              rw [←hden_S_EX_raw]
              exact den_S_E)
            (hY_ty := rfl)
            (hY_func := hSval_func)
            (Xarg := elemDom hy_mem)
            (hXarg_ty := elemDom_ty hy_mem)
            (hXarg_mem := hWy_mem)
        have hcanon_y_zf :
            ZFSet.fapply (BType.canonicalIsoSMTType β).1
              (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType β).2.1)
              ⟨y, by
                rw [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType β).2.1]
                exact hy_mem⟩ = (elemDom hy_mem).fst := by
          simpa [elemDom_retract hy_mem] using
            canonical_of_retract β (elemDom_mem hy_mem)
        have hDlhs_true : Dlhs.fst = zftrue := by
          have := (mem_retract_set_iff_app_canonical_eq_zftrue
            (α := β) (setDom_func hY_mem) (setDom_retract hY_mem) hy_mem).mp hy
          simpa [proof_irrel_heq, hcanon_y_zf, hDlhs_val] using this
        have hDrhs_mem_bool : Drhs.fst ∈ 𝔹 := by
          simpa [hDrhs_ty] using Drhs.snd.snd
        have hDrhs_bool : Drhs.fst = zftrue ∨ Drhs.fst = zffalse := by
          simpa [ZFSet.ZFBool.mem_𝔹_iff, or_comm] using hDrhs_mem_bool
        rcases hDrhs_bool with hDrhs_true | hDrhs_false
        · apply (mem_retract_set_iff_app_canonical_eq_zftrue
            (α := β) hSval_func retract_eq hy_mem).mpr
          simpa [proof_irrel_heq, hcanon_y_zf, hDrhs_val] using hDrhs_true
        · have hden_not_rhs_true :
            ⟦(¬ˢ ((@ˢS_enc) (SMT.Term.var x))).abstract
                (Function.update
                  (Function.update Δ_ctx E (some (setDom hY_mem))) x
                  (some (elemDom hy_mem)))
                (by
                  intro v hv
                  have hv' : v ∈ SMT.fv ((@ˢS_enc) (SMT.Term.var x)) := by
                    simpa [SMT.fv] using hv
                  have hv'' : v ∈ SMT.fv S_enc ∨ v = x := by
                    simpa [SMT.fv] using hv'
                  exact hcov_pred_upd (setDom hY_mem) (elemDom hy_mem) v (by
                    rw [hpred_def]
                    simp only [SMT.fv, List.mem_append, List.mem_singleton]
                    exact Or.inr hv''))⟧ˢ =
              some ⟨zftrue, SMTType.bool,
                ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
            simpa [SMT.Term.abstract, proof_irrel_heq] using
              denote_not_eq_zftrue_of_some_zffalse hden_rhs hDrhs_ty hDrhs_false
          have hden_body_true :
              ⟦(((@ˢSMT.Term.var E) (SMT.Term.var x)) ∧ˢ
                    (¬ˢ ((@ˢS_enc) (SMT.Term.var x)))).abstract
                  (Function.update
                    (Function.update Δ_ctx E (some (setDom hY_mem))) x
                    (some (elemDom hy_mem)))
                  (by
                    intro v hv
                    exact hcov_pred_upd (setDom hY_mem) (elemDom hy_mem) v (by
                      rw [hpred_def]
                      simpa [SMT.fv] using hv))⟧ˢ =
                some ⟨zftrue, SMTType.bool,
                  ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
            simpa [SMT.Term.abstract, proof_irrel_heq] using
              denote_and_eq_zftrue_of_some_zftrue
                hden_lhs hDlhs_ty hDlhs_true hden_not_rhs_true rfl rfl
          have hden_pred_false :
              ⟦pred.abstract
                  (Function.update
                    (Function.update Δ_ctx E (some (setDom hY_mem))) x
                    (some (elemDom hy_mem)))
                  (hcov_pred_upd (setDom hY_mem) (elemDom hy_mem))⟧ˢ =
                some ⟨zffalse, SMTType.bool,
                  ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
            simpa [hpred_def, SMT.Term.abstract, proof_irrel_heq] using
              denote_not_eq_zffalse_of_some_zftrue
                hden_body_true rfl rfl
          have hEq := Option.some.inj (hden_pred.symm.trans hden_pred_false)
          have hDpred_false : Dpred.fst = zffalse := by
            exact congrArg (fun d : SMT.Dom => d.fst) hEq
          exact (zftrue_ne_zffalse <| hDpred_true.symm.trans hDpred_false).elim

set_option maxHeartbeats 1000000 in
theorem encodeTerm_spec.pow_case.{u} (fv_sub_typings : B.FvSubTypings) (S : B.Term)
  (ih :
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
  (E : B.Env) {Λ : SMT.TypeContext} {α : BType} (typ_t : E.context ⊢ᴮ 𝒫ᴮ S : α) {«Δ» : B.RenamingContext.Context}
  (Δ_fv : ∀ v ∈ B.fv ( 𝒫ᴮ S), («Δ» v).isSome = true) {Δ₀ : SMT.RenamingContext.Context}
  (Δ₀_ext : RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» ( 𝒫ᴮ S)) {used : List SMT.𝒱}
  (Δ₀_none_out : ∀ v ∉ used, Δ₀ v = none) {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ}
  (den_t : ⟦( 𝒫ᴮ S).abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩) (vars_used : ∀ v ∈ ( 𝒫ᴮ S).vars, v ∈ used)
  (Λ_inv : ∀ v ∈ ( 𝒫ᴮ S).vars, v ∈ Λ → v ∈ E.context) {n : ℕ} :
  ⦃fun x =>
    match x with
    | { env := E0, types := Λ' } => ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
    encodeTerm ( 𝒫ᴮ S) E ⦃PostCond.mayThrow fun x x_1 =>
      match x with
      | (t', σ) =>
        match x_1 with
        | { env := E', types := Γ' } =>
          ⌜used ⊆ E'.usedVars ∧
              Λ ⊆ Γ' ∧
                AList.keys Γ' ⊆ E'.usedVars ∧
                  CoversUsedVars E'.usedVars ( 𝒫ᴮ S) ∧
                    σ = α.toSMTType ∧
                      Γ' ⊢ˢ t' : σ ∧
                        (∀ v ∈ used, v ∉ Λ → v ∉ B.fv ( 𝒫ᴮ S) → v ∉ Γ') ∧
                          ∃ Δ',
                            ∃ (Δ'_covers : RenamingContext.CoversFV Δ' t'),
                              RenamingContext.Extends Δ' Δ₀ ∧
                                RenamingContext.ExtendsOnSourceFV Δ' «Δ» ( 𝒫ᴮ S) ∧
                                  (∀ v ∉ E'.usedVars, Δ' v = none) ∧
                                    ∃ denT',
                                      ⟦t'.abstract Δ' Δ'_covers⟧ˢ = some denT' ∧
                                        ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT' ∧
                                          ∀ (Δ_alt : B.RenamingContext.Context)
                                            (Δ_fv_alt : ∀ v ∈ B.fv ( 𝒫ᴮ S), (Δ_alt v).isSome = true)
                                            (Δ₀_alt : SMT.RenamingContext.Context),
                                            RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt ( 𝒫ᴮ S) →
                                              (∀ v ∉ E'.usedVars, Δ₀_alt v = none) →
                                              (∀ v (d : SMT.Dom), Δ₀_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) →
                                                ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦α⟧ᶻ),
                                                  ⟦( 𝒫ᴮ S).abstract Δ_alt Δ_fv_alt⟧ᴮ = some ⟨T_alt, ⟨α, hT_alt⟩⟩ →
                                                    ∃ Δ'_alt,
                                                      ∃ (hcov_alt : RenamingContext.CoversFV Δ'_alt t'),
                                                        ∃ denT_alt,
                                                          RenamingContext.Extends Δ'_alt Δ₀_alt ∧
                                                            (∀ v ∉ E'.usedVars, Δ'_alt v = none) ∧
                                                              (∀ v (d : SMT.Dom), Δ'_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) ∧
                                                              ⟦t'.abstract Δ'_alt hcov_alt⟧ˢ = some denT_alt ∧
                                                                ⟨T_alt, ⟨α, hT_alt⟩⟩ ≘ᶻ denT_alt ∧
                                                                                        (∀ v, Δ'_alt v ≠ none → v ∈ Γ')⌝⦄ := by
  mstart
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre

  rw [encodeTerm]

  obtain ⟨β, rfl, typ_S⟩ := B.Typing.powE typ_t
  have Δ_fv_S : ∀ v ∈ B.fv S, («Δ» v).isSome = true := by
    intro v hv
    simpa [B.fv] using Δ_fv v hv

  rw [B.Term.abstract, B.denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at den_t
  obtain ⟨⟨X, τX, hX⟩, den_S, eq⟩ := den_t
  have hτX := denote_welltyped_eq
    (t := S.abstract («Δ» := «Δ») Δ_fv_S)
    ?_ den_S
  on_goal 2 =>
    use E.context.abstract («Δ» := «Δ»), WFTC.of_abstract, .set β
    exact @Typing.of_abstract (B.Dom) («Δ» := «Δ») ?_ S E.context (.set β) Δ_fv_S typ_S
  dsimp at hτX
  subst τX

  rw [Option.some_inj] at eq
  injection eq with T_eq _
  subst T

  have Δ₀_ext_S : RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» S := by
    exact RenamingContext.extendsOnSourceFV_of_fv_subset
      (hsub := by
        intro v hv
        simpa [B.fv] using hv) Δ₀_ext

  mspec ih (E := E) (Λ := St.types) (α := .set β) typ_S
    («Δ» := «Δ») Δ_fv_S
    (Δ₀ := Δ₀) Δ₀_ext_S (used := used) Δ₀_none_out (T := X) (hT := hX)
    den_S (fun v hv => vars_used v (show v ∈ (𝒫ᴮ S).vars by simpa [B.Term.vars] using hv))
    (fun v hv => Λ_inv v (show v ∈ (𝒫ᴮ S).vars by simpa [B.Term.vars] using hv))
    (n := St.env.freshvarsc)
  clear ih
  rename_i out_S
  obtain ⟨S_enc, τS⟩ := out_S
  mrename_i pre
  mintro ∀St'
  mpure pre
  dsimp at pre
  obtain ⟨St_used_sub_St', St_eq_St', St'_sub, S_cov_St', rfl, typ_S_enc, S_preserves,
    Δ', Δ'_covers_S, Δ'_extends_Δ₀, Δ'_ext_S, Δ'_none_out,
    ⟨Senc, _, hSenc⟩, den_S_enc, ⟨rfl, retract_Senc_eq_X⟩, ih_total⟩ := pre

  rw [BType.toSMTType]
  conv =>
    enter [2,1,1]
    dsimp
  set ctx := St'.types
  mspec Std.Do.Spec.get_StateT
  mspec freshVar_spec (Γ := ctx) (τ := β.toSMTType) (n := St'.env.freshvarsc) (used := St'.env.usedVars)
  case post.success x =>
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨St₁_types_eq, x_fresh, St₁_fvc_eq, St₁_used_eq, x_not_used⟩ := pre

    have hx_not_mem_fv_S_enc : x ∉ SMT.fv S_enc := by
      intro hx
      have hnone : Δ' x = none := Δ'_none_out x x_not_used
      have hisSome : (Δ' x).isSome = true := Δ'_covers_S x hx
      rw [hnone] at hisSome
      simp at hisSome

    mspec freshVar_spec
      (Γ := ctx.insert x β.toSMTType)
      (τ := .fun β.toSMTType .bool)
      (n := St₁.env.freshvarsc)
      (used := St₁.env.usedVars)
    case post.success E =>
      mrename_i pre
      mintro ∀St₂
      mpure pre
      obtain ⟨St₂_types_eq, E_fresh, St₂_fvc_eq, St₂_used_eq, E_not_used⟩ := pre

      simp [modify]
      change used ⊆ St₂.env.usedVars ∧
          St.types ⊆ St'.types ∧
            AList.keys St'.types ⊆ St₂.env.usedVars ∧
              CoversUsedVars St₂.env.usedVars ( 𝒫ᴮ S) ∧
                _
      constructor
      · intro v hv
        rw [St₂_used_eq, St₁_used_eq]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (St_used_sub_St' hv))
      · constructor
        · intro v hv
          simpa [ctx] using St_eq_St' hv
        · constructor
          · intro v hv
            rw [St₂_used_eq, St₁_used_eq]
            exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (St'_sub (by simpa [ctx] using hv)))
          · constructor
            · intro v hv
              rw [St₂_used_eq, St₁_used_eq]
              exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (by simpa [B.fv] using S_cov_St' v hv))
            · constructor
              · rfl
              · set pred : SMT.Term :=
                  ((@ˢSMT.Term.var E) (SMT.Term.var x) ⇒ˢ (@ˢS_enc) (SMT.Term.var x))
                set tpow : SMT.Term :=
                  (λˢ [E]) [β.toSMTType.fun SMTType.bool]
                    (Term.forall [x] [β.toSMTType] pred)
                have hE_not_ctx : E ∉ ctx := by
                  intro h
                  exact E_fresh (by rw [AList.mem_insert]; exact Or.inr h)
                have hx_ne_E : x ≠ E := by
                  intro hxe
                  subst hxe
                  exact E_fresh (by rw [AList.mem_insert]; exact Or.inl rfl)
                have hx_not_ctx : x ∉ ctx := x_fresh
                have hx_not_ctxE : x ∉ ctx.insert E (.fun β.toSMTType .bool) := by
                  rw [AList.mem_insert]
                  simp [hx_ne_E, hx_not_ctx]
                have typ_S_enc_E_insert :
                    ctx.insert E (.fun β.toSMTType .bool) ⊢ˢ S_enc : β.set.toSMTType :=
                  Typing.weakening
                    (h := SMT.TypeContext.entries_subset_insert_of_notMem hE_not_ctx)
                    typ_S_enc
                have typ_S_enc_Ex_insert :
                    (ctx.insert E (.fun β.toSMTType .bool)).insert x β.toSMTType ⊢ˢ S_enc :
                      β.set.toSMTType :=
                  Typing.weakening
                    (h := SMT.TypeContext.entries_subset_insert_of_notMem hx_not_ctxE)
                    typ_S_enc_E_insert
                have hE_not_bv_S_enc : E ∉ SMT.bv S_enc := by
                  intro hEbv
                  exact SMT.Typing.bv_notMem_context typ_S_enc_E_insert E hEbv (by
                    rw [AList.mem_insert]
                    exact Or.inl rfl)
                have hE_not_mem_fv_S_enc : E ∉ SMT.fv S_enc := by
                  exact funNotMemFvOfNotMemContext typ_S_enc hE_not_ctx
                have hx_not_bv_S_enc : x ∉ SMT.bv S_enc := by
                  intro hxbv
                  exact SMT.Typing.bv_notMem_context typ_S_enc_Ex_insert x hxbv (by
                    rw [AList.mem_insert]
                    exact Or.inl rfl)
                have typ_pred :
                    (ctx.insert E (.fun β.toSMTType .bool)).insert x β.toSMTType ⊢ˢ pred : .bool := by
                  change (ctx.insert E (.fun β.toSMTType .bool)).insert x β.toSMTType ⊢ˢ
                    ((@ˢSMT.Term.var E) (SMT.Term.var x) ⇒ˢ (@ˢS_enc) (SMT.Term.var x)) : .bool
                  apply SMT.Typing.imp
                  · apply SMT.Typing.app
                    · apply SMT.Typing.var
                      rw [AList.lookup_insert_ne hx_ne_E.symm, AList.lookup_insert]
                    · apply SMT.Typing.var
                      rw [AList.lookup_insert]
                  · apply SMT.Typing.app
                    · exact typ_S_enc_Ex_insert
                    · apply SMT.Typing.var
                      rw [AList.lookup_insert]
                have typ_app_rhs :
                    (ctx.insert E (.fun β.toSMTType .bool)).insert x β.toSMTType ⊢ˢ
                      ((@ˢS_enc) (SMT.Term.var x)) : .bool := by
                  apply SMT.Typing.app
                  · exact typ_S_enc_Ex_insert
                  · apply SMT.Typing.var
                    rw [AList.lookup_insert]
                have typ_not_rhs :
                    (ctx.insert E (.fun β.toSMTType .bool)).insert x β.toSMTType ⊢ˢ
                      (¬ˢ ((@ˢS_enc) (SMT.Term.var x))) : .bool := by
                  apply SMT.Typing.not
                  exact typ_app_rhs
                have typ_forall :
                    ctx.insert E (.fun β.toSMTType .bool) ⊢ˢ
                      Term.forall [x] [β.toSMTType] pred : .bool := by
                  refine SMT.Typing.forall _ _ _ _ ?_ ?_ ?_ ?_ ?_
                  · intro v hv
                    rw [List.mem_singleton] at hv
                    subst hv
                    exact hx_not_ctxE
                  · intro v hv
                    rw [List.mem_singleton] at hv
                    subst hv
                    simp [SMT.bv, pred, hx_not_bv_S_enc]
                  · exact Nat.zero_lt_succ 0
                  · rfl
                  · have hupdateEx :
                      SMT.TypeContext.update (ctx.insert E (.fun β.toSMTType .bool)) [x] [β.toSMTType] rfl =
                        (ctx.insert E (.fun β.toSMTType .bool)).insert x β.toSMTType := by
                      simp only [TypeContext.update, List.length_cons, List.length_nil,
                        zero_add, Nat.reduceAdd, Fin.cast_eq_self, Fin.getElem_fin,
                        Fin.val_eq_zero, List.getElem_cons_zero, Fin.foldl_succ,
                        Fin.foldl_zero]
                    rw [hupdateEx]
                    simpa [pred] using typ_pred
                have typ_tpow : ctx ⊢ˢ tpow : .fun (.fun β.toSMTType .bool) .bool := by
                  refine SMT.Typing.lambda _ _ _ _ _ ?_ ?_ ?_ ?_ ?_
                  · intro v hv
                    rw [List.mem_singleton] at hv
                    subst hv
                    exact hE_not_ctx
                  · intro v hv
                    rw [List.mem_singleton] at hv
                    subst hv
                    simp [SMT.bv, pred, hE_not_bv_S_enc]
                    exact hx_ne_E.symm
                  · exact Nat.zero_lt_succ 0
                  · rfl
                  · have hupdateE :
                      SMT.TypeContext.update St'.types [E] [.fun β.toSMTType .bool] rfl =
                        ctx.insert E (.fun β.toSMTType .bool) := by
                      simp only [TypeContext.update, List.length_cons, List.length_nil, zero_add,
                        Nat.reduceAdd, Fin.cast_eq_self, Fin.getElem_fin, Fin.val_eq_zero,
                        List.getElem_cons_zero, ctx, Fin.foldl_succ, Fin.foldl_zero]
                    rw [hupdateE]
                    simpa [tpow] using typ_forall
                constructor
                · exact typ_tpow
                · constructor
                  · -- preserves_types
                    intro v hv h1 h2
                    simp [B.fv] at h2
                    exact S_preserves v (by simpa [St_used_eq] using hv) h1 h2
                  · have hpow_cov : RenamingContext.CoversFV Δ' tpow := by
                      intro v hv
                      have hv' :
                          ((v = E ∨ v = x ∨ v ∈ SMT.fv S_enc ∨ v = x) ∧ ¬v = x) ∧ ¬v = E := by
                        simpa [tpow, pred, SMT.fv, List.mem_removeAll_iff] using hv
                      rcases hv' with ⟨hv', hv_ne_E⟩
                      rcases hv' with ⟨hv', hv_ne_x⟩
                      rcases hv' with hE | hx | hvS | hx
                      · contradiction
                      · contradiction
                      · exact Δ'_covers_S v hvS
                      · contradiction
                    refine ⟨Δ', ?_⟩
                    constructor
                    · exact Δ'_extends_Δ₀
                    · constructor
                      · exact RenamingContext.extendsOnSourceFV_of_extends Δ'_extends_Δ₀ Δ₀_ext
                      · constructor
                        · intro v hv
                          simp only [St₂_used_eq, St₁_used_eq, List.mem_cons, not_or] at hv
                          apply Δ'_none_out
                          exact hv.2.2
                        · refine ⟨hpow_cov, ?_⟩
                          -- Use pow_denotation_aux for both the original and alt cases
                          change ∃ a : ZFSet, ∃ a_1 : SMTType, ∃ (h : a ∈ ⟦a_1⟧ᶻ),
                                ⟦tpow.abstract Δ' hpow_cov⟧ˢ = some ⟨a, ⟨a_1, h⟩⟩ ∧
                                  ⟨X.powerset, ⟨β.set.set, hT⟩⟩ ≘ᶻ ⟨a, ⟨a_1, h⟩⟩ ∧ _
                          obtain ⟨a, a_1, h, hden, hRDom⟩ :=
                            pow_denotation_aux pred rfl tpow rfl hx_ne_E
                              hE_not_mem_fv_S_enc hx_not_mem_fv_S_enc
                              hE_not_bv_S_enc hx_not_bv_S_enc
                              typ_S_enc hE_not_ctx hx_not_ctx
                              Δ'_covers_S hpow_cov hSenc den_S_enc
                              hX retract_Senc_eq_X hT
                          refine ⟨a, a_1, h, hden, hRDom, ?_⟩
                          · -- alt universality for pow
                            intro Δ_alt Δ_fv_alt Δ₀_alt Δ₀_alt_ext Δ₀_alt_none_out Δ₀_alt_wt T_alt hT_alt den_t_alt
                            -- Extract alt S denotation from alt pow denotation
                            rw [B.Term.abstract, B.denote, Option.bind_eq_bind,
                              Option.bind_eq_some_iff] at den_t_alt
                            obtain ⟨⟨X_alt, α_alt, hX_alt⟩, den_S_alt, eq_alt⟩ := den_t_alt
                            have hα_eq : α_alt = .set β :=
                              (denote_welltyped_eq
                                (t := S.abstract Δ_alt (fun v hv => Δ_fv_alt v (by simp [B.fv]; exact hv)))
                                ⟨_, WFTC.of_abstract, .set β, by convert Typing.of_abstract _ typ_S⟩
                                (by convert den_S_alt using 2)).symm
                            subst hα_eq
                            dsimp at eq_alt
                            rw [Option.some.injEq, PSigma.mk.injEq] at eq_alt
                            obtain ⟨hT_eq, _⟩ := eq_alt
                            subst hT_eq
                            -- Use ih_total to get alt S encoding
                            have Δ₀_alt_ext_S : RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt S :=
                              RenamingContext.extendsOnSourceFV_of_fv_subset
                                (hsub := fun v hv => by simp [B.fv]; exact hv) Δ₀_alt_ext
                            -- Restrict Δ₀_alt to St'.env.usedVars
                            set Δ₀_alt_S : SMT.RenamingContext.Context :=
                              fun v => if v ∈ St'.env.usedVars then Δ₀_alt v else none
                            have Δ₀_alt_S_ext : RenamingContext.ExtendsOnSourceFV Δ₀_alt_S Δ_alt S := by
                              intro v d hv
                              simp only [Δ₀_alt_S]
                              have hv_fv : v ∈ B.fv S := by
                                by_contra h_neg; simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                                  B.RenamingContext.restrictToFV_eq_none_of_not_mem h_neg] at hv
                              rw [if_pos (St_used_sub_St' (vars_used v (by simp [B.Term.vars]; left; exact hv_fv)))]
                              exact Δ₀_alt_ext_S hv
                            have Δ₀_alt_S_none : ∀ v ∉ St'.env.usedVars, Δ₀_alt_S v = none :=
                              fun v hv => by simp only [Δ₀_alt_S]; rw [if_neg hv]
                            have Δ₀_alt_S_wt : ∀ v (d : SMT.Dom), Δ₀_alt_S v = some d → ∀ τ, St'.types.lookup v = some τ → d.snd.fst = τ := by
                              intro v d hv τ hτ; simp only [Δ₀_alt_S] at hv; split_ifs at hv with h; exact Δ₀_alt_wt v d hv τ hτ
                            obtain ⟨Δ'_alt_S, hcov_alt_S, denT_S_alt, hext_alt_S,
                              Δ'_alt_S_none_out, Δ'_alt_S_wt_out, den_S_alt_enc, hRDom_S_alt, Δ'_alt_S_dom_out⟩ :=
                              ih_total Δ_alt (fun v hv => Δ_fv_alt v (by simp [B.fv]; exact hv))
                                Δ₀_alt_S Δ₀_alt_S_ext Δ₀_alt_S_none Δ₀_alt_S_wt X_alt hX_alt
                                (by convert den_S_alt using 2)
                            -- Build Δ'_alt := Δ₀_alt priority over Δ'_alt_S
                            set Δ'_alt : SMT.RenamingContext.Context :=
                              fun v => match Δ₀_alt v with | some d => some d | none => Δ'_alt_S v
                            -- Extends
                            have hext_alt : RenamingContext.Extends Δ'_alt Δ₀_alt :=
                              fun v d hv => by simp only [Δ'_alt, hv]
                            -- S_enc agrees between Δ'_alt and Δ'_alt_S
                            have hagree_S : RenamingContext.AgreesOnFV Δ'_alt Δ'_alt_S S_enc := by
                              intro v hv; simp only [Δ'_alt]
                              cases h : Δ₀_alt v with
                              | some d =>
                                have hv_St' : v ∈ St'.env.usedVars := by
                                  by_contra hv_not
                                  exact absurd (Δ'_covers_S v hv) (by simp [Δ'_none_out v hv_not])
                                symm; exact hext_alt_S (show Δ₀_alt_S v = some d by
                                  simp [Δ₀_alt_S, if_pos hv_St', h])
                              | none => rfl
                            -- Coverage of S_enc under Δ'_alt
                            have hcov_S_alt : RenamingContext.CoversFV Δ'_alt S_enc := by
                              intro v hv; simp only [Δ'_alt]
                              cases h : Δ₀_alt v with
                              | some d => simp
                              | none => exact hcov_alt_S v hv
                            -- S_enc denotes under Δ'_alt
                            have den_S_alt_final :
                                ⟦S_enc.abstract Δ'_alt hcov_S_alt⟧ˢ = some denT_S_alt := by
                              have := RenamingContext.denote_congr_of_agreesOnFV
                                (t := S_enc) (h1 := hcov_S_alt) (h2 := hcov_alt_S) hagree_S
                              simpa [RenamingContext.denote] using this.trans den_S_alt_enc
                            -- Coverage of tpow under Δ'_alt
                            -- fv(tpow) = fv(S_enc) (E, x bound)
                            have hcov_tpow_alt : RenamingContext.CoversFV Δ'_alt tpow := by
                              intro v hv
                              have hv' :
                                  ((v = E ∨ v = x ∨ v ∈ SMT.fv S_enc ∨ v = x) ∧ ¬v = x) ∧ ¬v = E := by
                                simpa [tpow, pred, SMT.fv, List.mem_removeAll_iff] using hv
                              rcases hv' with ⟨⟨hE | hx | hvS | hx, _⟩, _⟩
                              · contradiction
                              · contradiction
                              · exact hcov_S_alt v hvS
                              · contradiction
                            -- Use pow_denotation_aux for denotation + RDom
                            obtain ⟨Sval_alt, ⟨σ_alt, hSval_alt⟩⟩ := denT_S_alt
                            obtain ⟨hRDom_ty, hRDom_retract⟩ := hRDom_S_alt
                            subst hRDom_ty
                            obtain ⟨a_alt, a_1_alt, h_alt, hden_alt, hRDom_alt⟩ :=
                              pow_denotation_aux pred rfl tpow rfl hx_ne_E
                                hE_not_mem_fv_S_enc hx_not_mem_fv_S_enc
                                hE_not_bv_S_enc hx_not_bv_S_enc
                                typ_S_enc hE_not_ctx hx_not_ctx
                                hcov_S_alt hcov_tpow_alt hSval_alt den_S_alt_final
                                hX_alt hRDom_retract hT_alt
                            refine ⟨Δ'_alt, hext_alt, ?_, ?_, hcov_tpow_alt,
                              a_alt, a_1_alt, h_alt, hden_alt, hRDom_alt, ?_⟩
                            -- Vanishing: ∀ v ∉ E'.usedVars, Δ'_alt v = none
                            · intro v hv; simp only [Δ'_alt]
                              rw [Δ₀_alt_none_out v hv]
                              apply Δ'_alt_S_none_out
                              intro hmem; exact hv (by rw [St₂_used_eq, St₁_used_eq]; exact .tail _ (.tail _ hmem))
                            -- Well-typedness: output wt
                            · intro v d hv τ hτ
                              simp only [Δ'_alt] at hv
                              cases hΔ : Δ₀_alt v with
                              | some d' => simp [hΔ] at hv; subst hv; exact Δ₀_alt_wt v d' hΔ τ hτ
                              | none =>
                                simp [hΔ] at hv
                                exact Δ'_alt_S_wt_out v d hv τ hτ
                            -- dom_out
                            · intro v hv
                              simp only [Δ'_alt] at hv
                              cases hΔ : Δ₀_alt v with
                              | some d =>
                                exact fv_sub_typings (_root_.B.Typing.pow typ_S)
                                  (SMT.Typing.bool ctx true) v
                                  (SMT.RenamingContext.ExtendsOnSourceFV.dom_sub_B_fv Δ₀_alt_ext v
                                    (by rw [hΔ]; simp))
                              | none =>
                                simp [hΔ] at hv
                                exact Δ'_alt_S_dom_out v hv

set_option maxHeartbeats 4000000 in
private theorem cprod_case_denotation_aux.{u_1}
    {αx βx : BType} {X Y : ZFSet.{u_1}}
    {hT : X.prod Y ∈ ⟦(αx ×ᴮ βx).set⟧ᶻ}
    {ctx : SMT.TypeContext} {S_enc T_enc : SMT.Term}
    {Δ'' : SMT.RenamingContext.Context}
    (typ_T_enc : ctx ⊢ˢ T_enc : βx.set.toSMTType)
    (typ_S_enc_T : ctx ⊢ˢ S_enc : αx.set.toSMTType)
    (p a b : SMT.𝒱)
    (p_fresh : p ∉ ctx)
    (a_fresh : a ∉ ctx.insert p (αx.toSMTType.pair βx.toSMTType))
    (b_fresh : b ∉ (ctx.insert p (αx.toSMTType.pair βx.toSMTType)).insert a αx.toSMTType)
    {Senc Tenc : ZFSet.{u_1}}
    (hSenc : Senc ∈ ⟦αx.set.toSMTType⟧ᶻ)
    (hTenc : Tenc ∈ ⟦βx.set.toSMTType⟧ᶻ)
    (retract_Senc_eq_X : retract αx.set Senc = X)
    (retract_Tenc_eq_Y : retract βx.set Tenc = Y)
    (hΔ_S_final : RenamingContext.CoversFV Δ'' S_enc)
    (Δ''_covers_T : RenamingContext.CoversFV Δ'' T_enc)
    (den_S_enc_final :
      ⟦S_enc.abstract Δ'' hΔ_S_final⟧ˢ = some ⟨Senc, ⟨αx.set.toSMTType, hSenc⟩⟩)
    (den_T_enc :
      ⟦T_enc.abstract Δ'' Δ''_covers_T⟧ˢ = some ⟨Tenc, ⟨βx.set.toSMTType, hTenc⟩⟩)
    (hcov_tcprod_in :
      RenamingContext.CoversFV Δ''
        ((λˢ [p]) [αx.toSMTType.pair βx.toSMTType]
          (.exists [a, b] [αx.toSMTType, βx.toSMTType]
            (((@ˢS_enc) (SMT.Term.var a)) ∧ˢ
              (((@ˢT_enc) (SMT.Term.var b)) ∧ˢ
                ((SMT.Term.var p) =ˢ (SMT.Term.pair (SMT.Term.var a) (SMT.Term.var b)))))))) :
    ∃ denT',
      ⟦((λˢ [p]) [αx.toSMTType.pair βx.toSMTType]
          (.exists [a, b] [αx.toSMTType, βx.toSMTType]
            (((@ˢS_enc) (SMT.Term.var a)) ∧ˢ
              (((@ˢT_enc) (SMT.Term.var b)) ∧ˢ
                ((SMT.Term.var p) =ˢ (SMT.Term.pair (SMT.Term.var a) (SMT.Term.var b))))))).abstract
          Δ'' hcov_tcprod_in⟧ˢ = some denT' ∧
        ⟨X.prod Y, ⟨(αx ×ᴮ βx).set, hT⟩⟩ ≘ᶻ denT' := by
  let body : SMT.Term :=
    ((@ˢS_enc) (SMT.Term.var a)) ∧ˢ
      (((@ˢT_enc) (SMT.Term.var b)) ∧ˢ
        ((SMT.Term.var p) =ˢ (SMT.Term.pair (SMT.Term.var a) (SMT.Term.var b))))
  let tcprod : SMT.Term :=
    (λˢ [p]) [αx.toSMTType.pair βx.toSMTType]
      (.exists [a, b] [αx.toSMTType, βx.toSMTType] body)
  have hcov_tcprod : RenamingContext.CoversFV Δ'' tcprod := by
    simpa [body, tcprod] using hcov_tcprod_in
  have hmain :
      ∃ denT',
        ⟦tcprod.abstract Δ'' hcov_tcprod⟧ˢ = some denT' ∧
          ⟨X.prod Y, ⟨(αx ×ᴮ βx).set, hT⟩⟩ ≘ᶻ denT' := by
              classical
              have hSenc_func :
                  ZFSet.IsFunc ⟦αx.toSMTType⟧ᶻ ⟦SMTType.bool⟧ᶻ Senc := by
                have hSenc_mem : Senc ∈ ⟦αx.toSMTType⟧ᶻ.funs ⟦SMTType.bool⟧ᶻ := by
                  simpa [BType.toSMTType, SMTType.toZFSet] using hSenc
                rw [ZFSet.mem_funs] at hSenc_mem
                exact hSenc_mem
              have hTenc_func :
                  ZFSet.IsFunc ⟦βx.toSMTType⟧ᶻ ⟦SMTType.bool⟧ᶻ Tenc := by
                have hTenc_mem : Tenc ∈ ⟦βx.toSMTType⟧ᶻ.funs ⟦SMTType.bool⟧ᶻ := by
                  simpa [BType.toSMTType, SMTType.toZFSet] using hTenc
                rw [ZFSet.mem_funs] at hTenc_mem
                exact hTenc_mem
              have hp_ne_a : p ≠ a := by
                intro h
                subst h
                exact a_fresh (by rw [AList.mem_insert]; exact Or.inl rfl)
              have ha_ne_p : a ≠ p := hp_ne_a.symm
              have hb_ne_p : b ≠ p := by
                intro h
                subst h
                exact b_fresh (by
                  rw [AList.mem_insert, AList.mem_insert]
                  exact Or.inr (Or.inl rfl))
              have hp_ne_b : p ≠ b := hb_ne_p.symm
              have hb_ne_a : b ≠ a := by
                intro h
                subst h
                exact b_fresh (by
                  rw [AList.mem_insert]
                  exact Or.inl rfl)
              have ha_ne_b : a ≠ b := hb_ne_a.symm
              have ha_not_ctx : a ∉ ctx := by
                intro ha_in
                exact a_fresh (by rw [AList.mem_insert]; exact Or.inr ha_in)
              have hb_not_ctx : b ∉ ctx := by
                intro hb_in
                exact b_fresh (by
                  rw [AList.mem_insert, AList.mem_insert]
                  exact Or.inr (Or.inr hb_in))
              have hp_not_ctxa :
                  p ∉ (ctx.insert a αx.toSMTType) := by
                intro hp_in
                rw [AList.mem_insert] at hp_in
                rcases hp_in with hp_eq | hp_ctx
                · exact hp_ne_a hp_eq
                · exact p_fresh hp_ctx
              have hp_not_ctxab :
                  p ∉ ((ctx.insert a αx.toSMTType).insert b βx.toSMTType) := by
                intro hp_in
                rw [AList.mem_insert] at hp_in
                rcases hp_in with hp_eq | hp_ctxa
                · exact hp_ne_b hp_eq
                · exact hp_not_ctxa hp_ctxa
              have hp_not_fv_S_enc : p ∉ SMT.fv S_enc := by
                exact funNotMemFvOfNotMemContext typ_S_enc_T p_fresh
              have hp_not_fv_T_enc : p ∉ SMT.fv T_enc := by
                exact funNotMemFvOfNotMemContext typ_T_enc p_fresh
              have ha_not_fv_S_enc : a ∉ SMT.fv S_enc := by
                exact funNotMemFvOfNotMemContext typ_S_enc_T ha_not_ctx
              have hb_not_fv_S_enc : b ∉ SMT.fv S_enc := by
                exact funNotMemFvOfNotMemContext typ_S_enc_T hb_not_ctx
              have ha_not_fv_T_enc : a ∉ SMT.fv T_enc := by
                exact funNotMemFvOfNotMemContext typ_T_enc ha_not_ctx
              have hb_not_fv_T_enc : b ∉ SMT.fv T_enc := by
                exact funNotMemFvOfNotMemContext typ_T_enc hb_not_ctx
              have typ_S_enc_p :
                  ctx.insert p (αx.toSMTType.pair βx.toSMTType) ⊢ˢ S_enc : αx.set.toSMTType :=
                Typing.weakening
                  (h := SMT.TypeContext.entries_subset_insert_of_notMem p_fresh)
                  typ_S_enc_T
              have typ_T_enc_p :
                  ctx.insert p (αx.toSMTType.pair βx.toSMTType) ⊢ˢ T_enc : βx.set.toSMTType :=
                Typing.weakening
                  (h := SMT.TypeContext.entries_subset_insert_of_notMem p_fresh)
                  typ_T_enc
              have typ_S_enc_pab :
                  ((ctx.insert p (αx.toSMTType.pair βx.toSMTType)).insert a αx.toSMTType).insert b βx.toSMTType ⊢ˢ
                    S_enc : αx.set.toSMTType :=
                Typing.weakening
                  (h := SMT.TypeContext.entries_subset_insert_of_notMem b_fresh)
                  (Typing.weakening
                    (h := SMT.TypeContext.entries_subset_insert_of_notMem a_fresh)
                    typ_S_enc_p)
              have typ_T_enc_pab :
                  ((ctx.insert p (αx.toSMTType.pair βx.toSMTType)).insert a αx.toSMTType).insert b βx.toSMTType ⊢ˢ
                    T_enc : βx.set.toSMTType :=
                Typing.weakening
                  (h := SMT.TypeContext.entries_subset_insert_of_notMem b_fresh)
                  (Typing.weakening
                    (h := SMT.TypeContext.entries_subset_insert_of_notMem a_fresh)
                    typ_T_enc_p)
              have typ_body :
                  ((ctx.insert p (αx.toSMTType.pair βx.toSMTType)).insert a αx.toSMTType).insert b βx.toSMTType ⊢ˢ
                    body : .bool := by
                dsimp [body]
                apply SMT.Typing.and
                · apply SMT.Typing.app
                  · exact typ_S_enc_pab
                  · apply SMT.Typing.var
                    rw [AList.lookup_insert_ne ha_ne_b, AList.lookup_insert]
                · apply SMT.Typing.and
                  · apply SMT.Typing.app
                    · exact typ_T_enc_pab
                    · apply SMT.Typing.var
                      rw [AList.lookup_insert]
                  · apply SMT.Typing.eq
                    · apply SMT.Typing.var
                      rw [AList.lookup_insert_ne hp_ne_b]
                      rw [AList.lookup_insert_ne hp_ne_a]
                      rw [AList.lookup_insert]
                    · apply SMT.Typing.pair
                      · apply SMT.Typing.var
                        rw [AList.lookup_insert_ne ha_ne_b]
                        rw [AList.lookup_insert]
                      · apply SMT.Typing.var
                        rw [AList.lookup_insert]
              have typ_exists :
                  ctx.insert p (αx.toSMTType.pair βx.toSMTType) ⊢ˢ
                    .exists [a, b] [αx.toSMTType, βx.toSMTType] body : .bool := by
                have ha_in_body_ctx :
                    a ∈ ((ctx.insert p (αx.toSMTType.pair βx.toSMTType)).insert a αx.toSMTType).insert b βx.toSMTType := by
                  rw [AList.mem_insert, AList.mem_insert]
                  exact Or.inr (Or.inl rfl)
                have hb_in_body_ctx :
                    b ∈ ((ctx.insert p (αx.toSMTType.pair βx.toSMTType)).insert a αx.toSMTType).insert b βx.toSMTType := by
                  rw [AList.mem_insert]
                  exact Or.inl rfl
                have fresh_body :
                    ∀ v ∈ [a, b], v ∉ SMT.bv body := by
                  intro v hv
                  rw [List.mem_cons] at hv
                  rcases hv with rfl | hv
                  · intro hbv
                    exact (SMT.Typing.bv_notMem_context typ_body _ hbv) ha_in_body_ctx
                  · rw [List.mem_singleton] at hv
                    subst hv
                    intro hbv
                    exact (SMT.Typing.bv_notMem_context typ_body _ hbv) hb_in_body_ctx
                have len_eq_ab : [a, b].length = [αx.toSMTType, βx.toSMTType].length := by
                  simp
                apply SMT.Typing.exists
                  (Γ := ctx.insert p (αx.toSMTType.pair βx.toSMTType))
                  (vs := [a, b]) (τs := [αx.toSMTType, βx.toSMTType]) (len_eq := len_eq_ab)
                · intro v hv
                  rw [List.mem_cons] at hv
                  rcases hv with rfl | hv
                  · exact a_fresh
                  · rw [List.mem_singleton] at hv
                    subst hv
                    intro hb_in
                    exact b_fresh (by
                      rw [AList.mem_insert]
                      exact Or.inr hb_in)
                · exact fresh_body
                · simp
                · have hupdate_ab :
                      SMT.TypeContext.update
                        (ctx.insert p (αx.toSMTType.pair βx.toSMTType))
                        [a, b] [αx.toSMTType, βx.toSMTType] len_eq_ab =
                        ((ctx.insert p (αx.toSMTType.pair βx.toSMTType)).insert a αx.toSMTType).insert b βx.toSMTType := by
                    unfold SMT.TypeContext.update
                    simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
                      Fin.cast_eq_self, Fin.getElem_fin]
                    rw [Fin.foldl_succ_last, Fin.foldl_succ_last]
                    simp only [Fin.reduceLast, Fin.coe_ofNat_eq_mod, Nat.mod_succ,
                      List.getElem_cons_succ, List.getElem_cons_zero, Fin.last_zero, Fin.isValue,
                      Fin.castSucc_zero, Nat.zero_mod, Fin.coe_castSucc, Fin.val_eq_zero,
                      Fin.foldl_zero]
                  rw [hupdate_ab]
                  exact typ_body
              let pairTy : SMTType := αx.toSMTType.pair βx.toSMTType
              have hφ_exists_at :
                  ∀ Wp : SMT.Dom,
                    Wp.snd.fst = pairTy →
                      RenamingContext.CoversFV
                        (Function.update Δ'' p (some Wp))
                        (.exists [a, b] [αx.toSMTType, βx.toSMTType] body) := by
                intro Wp hWp_ty v hv
                have hv' : v ∈ SMT.fv body ∧ v ∉ [a, b] := by
                  simpa [SMT.fv, List.mem_removeAll_iff] using hv
                rcases hv' with ⟨hv, hv_not_ab⟩
                dsimp [body] at hv
                rw [SMT.fv, List.mem_append] at hv
                rcases hv with hvSa | hv
                · rw [SMT.fv, List.mem_append] at hvSa
                  rcases hvSa with hvS | hva
                  · by_cases hpp : v = p
                    · subst hpp
                      exact False.elim (hp_not_fv_S_enc hvS)
                    · rw [Function.update_of_ne hpp]
                      exact hΔ_S_final v hvS
                  · exfalso
                    have : v = a := by
                      simpa [SMT.fv] using hva
                    exact hv_not_ab (by simp [this])
                · rw [SMT.fv, List.mem_append] at hv
                  rcases hv with hvTb | hvEq
                  · rw [SMT.fv, List.mem_append] at hvTb
                    rcases hvTb with hvT | hvb
                    · by_cases hpp : v = p
                      · subst hpp
                        exact False.elim (hp_not_fv_T_enc hvT)
                      · rw [Function.update_of_ne hpp]
                        exact Δ''_covers_T v hvT
                    · exfalso
                      have : v = b := by
                        simpa [SMT.fv] using hvb
                      exact hv_not_ab (by simp [this])
                  · rw [SMT.fv, List.mem_append] at hvEq
                    rcases hvEq with hvp | hvPair
                    · rw [SMT.fv, List.mem_singleton] at hvp
                      subst hvp
                      simp [Function.update]
                    · rw [SMT.fv, List.mem_append] at hvPair
                      rcases hvPair with hva | hvb
                      · exfalso
                        have : v = a := by
                          simpa [SMT.fv] using hva
                        exact hv_not_ab (by simp [this])
                      · exfalso
                        have : v = b := by
                          simpa [SMT.fv] using hvb
                        exact hv_not_ab (by simp [this])
              have hcov_body_upd :
                  ∀ Wp Wa Wb : SMT.Dom,
                    RenamingContext.CoversFV
                      (Function.update
                        (Function.update
                          (Function.update Δ'' p (some Wp))
                          a (some Wa))
                        b (some Wb))
                      body := by
                intro Wp Wa Wb v hv
                dsimp [body] at hv
                rw [SMT.fv, List.mem_append] at hv
                rcases hv with hvSa | hv
                · rw [SMT.fv, List.mem_append] at hvSa
                  rcases hvSa with hvS | hva
                  · by_cases hbp : v = b
                    · subst hbp
                      exact False.elim (hb_not_fv_S_enc hvS)
                    · by_cases hap : v = a
                      · subst hap
                        exact False.elim (ha_not_fv_S_enc hvS)
                      · by_cases hpp : v = p
                        · subst hpp
                          exact False.elim (hp_not_fv_S_enc hvS)
                        · simp [Function.update, hbp, hap, hpp, hΔ_S_final _ hvS]
                  · rw [SMT.fv, List.mem_singleton] at hva
                    subst hva
                    simp [Function.update, ha_ne_b]
                · rw [SMT.fv, List.mem_append] at hv
                  rcases hv with hvTb | hvEq
                  · rw [SMT.fv, List.mem_append] at hvTb
                    rcases hvTb with hvT | hvb
                    · by_cases hbp : v = b
                      · subst hbp
                        exact False.elim (hb_not_fv_T_enc hvT)
                      · by_cases hap : v = a
                        · subst hap
                          exact False.elim (ha_not_fv_T_enc hvT)
                        · by_cases hpp : v = p
                          · subst hpp
                            exact False.elim (hp_not_fv_T_enc hvT)
                          · simp [Function.update, hbp, hap, hpp, Δ''_covers_T _ hvT]
                    · rw [SMT.fv, List.mem_singleton] at hvb
                      subst hvb
                      simp [Function.update]
                  · rw [SMT.fv, List.mem_append] at hvEq
                    rcases hvEq with hvp | hvPair
                    · rw [SMT.fv, List.mem_singleton] at hvp
                      subst hvp
                      simp [Function.update, hp_ne_a, hp_ne_b]
                    · rw [SMT.fv, List.mem_append] at hvPair
                      rcases hvPair with hva | hvb
                      · rw [SMT.fv, List.mem_singleton] at hva
                        subst hva
                        simp [Function.update, ha_ne_b]
                      · rw [SMT.fv, List.mem_singleton] at hvb
                        subst hvb
                        simp [Function.update]
              have den_body_some :
                  ∀ (Wp : SMT.Dom)
                    (hWp_ty : Wp.snd.fst = pairTy)
                    {w : Fin [a, b].length → SMT.Dom},
                      (∀ i, (w i).snd.fst = [αx.toSMTType, βx.toSMTType][i] ∧
                        (w i).fst ∈ ⟦[αx.toSMTType, βx.toSMTType][i]⟧ᶻ) →
                        ∃ Dbody : SMT.Dom,
                          ⟦(Term.abstract.go body [a, b]
                              (Function.update Δ'' p (some Wp))
                              (by
                                intro v hv hv_not_ab
                                exact hφ_exists_at Wp hWp_ty v
                                  (by
                                    have hv_not_ab' : ¬ v = a ∧ ¬ v = b := by
                                      simpa [List.mem_cons, List.mem_singleton, not_or] using hv_not_ab
                                    simpa [SMT.fv, List.mem_removeAll_iff] using ⟨hv, hv_not_ab'⟩))
                              ).uncurry w⟧ˢ = some Dbody ∧
                            Dbody.snd.fst = SMTType.bool := by
                intro Wp hWp_ty w hw
                have hgo :=
                  funAbstractGoPair
                    (Δctx := Function.update Δ'' p (some Wp))
                    (P := body) (v₁ := a) (v₂ := b)
                    (τ₁ := αx.toSMTType) (τ₂ := βx.toSMTType)
                    (hgo_cov := by
                      intro v hv hv_not_ab
                      exact hφ_exists_at Wp hWp_ty v
                        (by
                          have hv_not_ab' : ¬ v = a ∧ ¬ v = b := by
                            simpa [List.mem_cons, List.mem_singleton, not_or] using hv_not_ab
                          simpa [SMT.fv, List.mem_removeAll_iff] using ⟨hv, hv_not_ab'⟩))
                    (hcovP := fun W₁ W₂ => hcov_body_upd Wp W₁ W₂)
                    w hw
                rw [hgo]
                let Δw : SMT.RenamingContext.Context :=
                  Function.update
                    (Function.update
                      (Function.update Δ'' p (some Wp))
                      a (some (w ⟨0, by simp⟩)))
                    b (some (w ⟨1, by simp⟩))
                have hcov_var_a :
                    RenamingContext.CoversFV Δw (SMT.Term.var a) := by
                  intro v hv
                  rw [SMT.fv, List.mem_singleton] at hv
                  subst hv
                  simp [Δw, Function.update, ha_ne_b]
                have hden_var_a :
                    ⟦(SMT.Term.var a).abstract Δw hcov_var_a⟧ˢ = some (w ⟨0, by simp⟩) := by
                  rw [SMT.Term.abstract.eq_def, SMT.denote, Option.pure_def, Option.some.injEq]
                  apply Option.get_of_eq_some
                  simp [Δw, Function.update, ha_ne_b]
                have hcov_S_enc_p :
                    RenamingContext.CoversFV
                      (Function.update Δ'' p (some Wp))
                      S_enc := by
                  exact SMT.RenamingContext.coversFV_update_of_notMem
                    (x := p) (d := Wp) hp_not_fv_S_enc hΔ_S_final
                have den_S_enc_p :
                    ⟦S_enc.abstract
                        (Function.update Δ'' p (some Wp))
                        hcov_S_enc_p⟧ˢ =
                      some ⟨Senc, ⟨αx.set.toSMTType, hSenc⟩⟩ := by
                  have hden0 :
                      ⟦S_enc.abstract Δ'' hΔ_S_final⟧ˢ =
                        ⟦S_enc.abstract
                            (Function.update Δ'' p (some Wp))
                            hcov_S_enc_p⟧ˢ := by
                    simpa [SMT.RenamingContext.denote] using
                      (SMT.RenamingContext.denote_update_of_notMem
                        («Δ» := Δ'') (t := S_enc) (x := p) (d := Wp)
                        (h := hΔ_S_final) hp_not_fv_S_enc)
                  rw [← hden0]
                  exact den_S_enc_final
                have hb_not_fv_S_app :
                    b ∉ SMT.fv ((@ˢS_enc) (SMT.Term.var a)) := by
                  intro hv
                  simp only [SMT.fv, List.mem_append, List.mem_singleton] at hv
                  rcases hv with hvS | hvb
                  · exact hb_not_fv_S_enc hvS
                  · exact hb_ne_a hvb
                obtain ⟨hcov_S_app_pa, DSa, hDSa_ty, _, hden_Sa_pa⟩ :=
                  funDenoteAppAt
                    (Δctx := Function.update Δ'' p (some Wp))
                    (t := S_enc) (x := a)
                    (α := αx.toSMTType) (β := SMTType.bool)
                    (Y := ⟨Senc, ⟨αx.set.toSMTType, hSenc⟩⟩)
                    (hcov_t_upd := by
                      intro Xarg
                      exact SMT.RenamingContext.coversFV_update_of_notMem
                        (x := a) (d := Xarg) ha_not_fv_S_enc hcov_S_enc_p)
                    (den_t_upd := by
                      intro Xarg
                      have htmp :
                          ⟦S_enc.abstract
                              (Function.update Δ'' p (some Wp))
                              hcov_S_enc_p⟧ˢ =
                            ⟦S_enc.abstract
                                (Function.update
                                  (Function.update Δ'' p (some Wp))
                                  a (some Xarg))
                                (SMT.RenamingContext.coversFV_update_of_notMem
                                  (x := a) (d := Xarg) ha_not_fv_S_enc hcov_S_enc_p)⟧ˢ := by
                        simpa [SMT.RenamingContext.denote] using
                          (SMT.RenamingContext.denote_update_of_notMem
                            («Δ» := Function.update Δ'' p (some Wp))
                            (t := S_enc) (x := a) (d := Xarg)
                            (h := hcov_S_enc_p) ha_not_fv_S_enc)
                      rw [← htmp]
                      exact den_S_enc_p)
                    (hY_ty := rfl)
                    (hY_func := hSenc_func)
                    (Xarg := w ⟨0, by simp⟩)
                    (hXarg_ty := (hw ⟨0, by simp⟩).1)
                    (hXarg_mem := (hw ⟨0, by simp⟩).2)
                have hcov_S_app :
                    RenamingContext.CoversFV Δw ((@ˢS_enc) (SMT.Term.var a)) := by
                  simpa [Δw] using
                    SMT.RenamingContext.coversFV_update_of_notMem
                      (x := b) (d := w ⟨1, by simp⟩) hb_not_fv_S_app hcov_S_app_pa
                have hden_Sa :
                    ⟦((@ˢS_enc) (SMT.Term.var a)).abstract Δw hcov_S_app⟧ˢ = some DSa := by
                  have htmp :
                      ⟦((@ˢS_enc) (SMT.Term.var a)).abstract
                          (Function.update (Function.update Δ'' p (some Wp)) a (some (w ⟨0, by simp⟩)))
                          hcov_S_app_pa⟧ˢ =
                        ⟦((@ˢS_enc) (SMT.Term.var a)).abstract Δw hcov_S_app⟧ˢ := by
                    simpa [Δw, SMT.RenamingContext.denote] using
                      (SMT.RenamingContext.denote_update_of_notMem
                        («Δ» := Function.update (Function.update Δ'' p (some Wp)) a (some (w ⟨0, by simp⟩)))
                        (t := ((@ˢS_enc) (SMT.Term.var a))) (x := b) (d := w ⟨1, by simp⟩)
                        (h := hcov_S_app_pa) hb_not_fv_S_app)
                  rw [← htmp]
                  exact hden_Sa_pa
                have hcov_var_b :
                    RenamingContext.CoversFV Δw (SMT.Term.var b) := by
                  intro v hv
                  rw [SMT.fv, List.mem_singleton] at hv
                  subst hv
                  simp [Δw]
                have hden_var_b :
                    ⟦(SMT.Term.var b).abstract Δw hcov_var_b⟧ˢ = some (w ⟨1, by simp⟩) := by
                  rw [SMT.Term.abstract.eq_def, SMT.denote, Option.pure_def, Option.some.injEq]
                  apply Option.get_of_eq_some
                  simp [Δw]
                have hcov_T_enc_pa :
                    RenamingContext.CoversFV
                      (Function.update (Function.update Δ'' p (some Wp)) a (some (w ⟨0, by simp⟩)))
                      T_enc := by
                  exact SMT.RenamingContext.coversFV_update_of_notMem
                    (x := a) (d := w ⟨0, by simp⟩) ha_not_fv_T_enc
                    (SMT.RenamingContext.coversFV_update_of_notMem
                      (x := p) (d := Wp) hp_not_fv_T_enc Δ''_covers_T)
                have den_T_enc_pa :
                    ⟦T_enc.abstract
                        (Function.update (Function.update Δ'' p (some Wp)) a (some (w ⟨0, by simp⟩)))
                        hcov_T_enc_pa⟧ˢ =
                      some ⟨Tenc, ⟨βx.set.toSMTType, hTenc⟩⟩ := by
                  have hden0 :
                      ⟦T_enc.abstract Δ'' Δ''_covers_T⟧ˢ =
                        ⟦T_enc.abstract
                            (Function.update (Function.update Δ'' p (some Wp)) a (some (w ⟨0, by simp⟩)))
                            hcov_T_enc_pa⟧ˢ := by
                    have h1 :
                        ⟦T_enc.abstract Δ'' Δ''_covers_T⟧ˢ =
                          ⟦T_enc.abstract
                              (Function.update Δ'' p (some Wp))
                              (SMT.RenamingContext.coversFV_update_of_notMem
                                (x := p) (d := Wp) hp_not_fv_T_enc Δ''_covers_T)⟧ˢ := by
                      simpa [SMT.RenamingContext.denote] using
                        (SMT.RenamingContext.denote_update_of_notMem
                          («Δ» := Δ'') (t := T_enc) (x := p) (d := Wp)
                          (h := Δ''_covers_T) hp_not_fv_T_enc)
                    have h2 :
                        ⟦T_enc.abstract
                            (Function.update Δ'' p (some Wp))
                            (SMT.RenamingContext.coversFV_update_of_notMem
                              (x := p) (d := Wp) hp_not_fv_T_enc Δ''_covers_T)⟧ˢ =
                          ⟦T_enc.abstract
                              (Function.update (Function.update Δ'' p (some Wp)) a (some (w ⟨0, by simp⟩)))
                              hcov_T_enc_pa⟧ˢ := by
                      simpa [SMT.RenamingContext.denote] using
                        (SMT.RenamingContext.denote_update_of_notMem
                          («Δ» := Function.update Δ'' p (some Wp)) (t := T_enc)
                          (x := a) (d := w ⟨0, by simp⟩)
                          (h := SMT.RenamingContext.coversFV_update_of_notMem
                            (x := p) (d := Wp) hp_not_fv_T_enc Δ''_covers_T)
                          ha_not_fv_T_enc)
                    exact h1.trans h2
                  rw [← hden0]
                  exact den_T_enc
                obtain ⟨hcov_T_app, DTb, hDTb_ty, _, hden_Tb⟩ :=
                  funDenoteAppAt
                    (Δctx := Function.update (Function.update Δ'' p (some Wp)) a (some (w ⟨0, by simp⟩)))
                    (t := T_enc) (x := b)
                    (α := βx.toSMTType) (β := SMTType.bool)
                    (Y := ⟨Tenc, ⟨βx.set.toSMTType, hTenc⟩⟩)
                    (hcov_t_upd := by
                      intro Xarg
                      exact SMT.RenamingContext.coversFV_update_of_notMem
                        (x := b) (d := Xarg) hb_not_fv_T_enc hcov_T_enc_pa)
                    (den_t_upd := by
                      intro Xarg
                      have htmp :
                          ⟦T_enc.abstract
                              (Function.update (Function.update Δ'' p (some Wp)) a (some (w ⟨0, by simp⟩)))
                              hcov_T_enc_pa⟧ˢ =
                            ⟦T_enc.abstract
                                (Function.update
                                  (Function.update (Function.update Δ'' p (some Wp)) a (some (w ⟨0, by simp⟩)))
                                  b (some Xarg))
                                (SMT.RenamingContext.coversFV_update_of_notMem
                                  (x := b) (d := Xarg) hb_not_fv_T_enc hcov_T_enc_pa)⟧ˢ := by
                        simpa [SMT.RenamingContext.denote] using
                          (SMT.RenamingContext.denote_update_of_notMem
                            («Δ» := Function.update (Function.update Δ'' p (some Wp)) a (some (w ⟨0, by simp⟩)))
                            (t := T_enc) (x := b) (d := Xarg)
                            (h := hcov_T_enc_pa) hb_not_fv_T_enc)
                      rw [← htmp]
                      exact den_T_enc_pa)
                    (hY_ty := rfl)
                    (hY_func := hTenc_func)
                    (Xarg := w ⟨1, by simp⟩)
                    (hXarg_ty := (hw ⟨1, by simp⟩).1)
                    (hXarg_mem := (hw ⟨1, by simp⟩).2)
                have hcov_var_p :
                    RenamingContext.CoversFV Δw (SMT.Term.var p) := by
                  intro v hv
                  rw [SMT.fv, List.mem_singleton] at hv
                  subst hv
                  simp [Δw, Function.update, hp_ne_a, hp_ne_b]
                have hden_var_p :
                    ⟦(SMT.Term.var p).abstract Δw hcov_var_p⟧ˢ = some Wp := by
                  rw [SMT.Term.abstract.eq_def, SMT.denote, Option.pure_def, Option.some.injEq]
                  apply Option.get_of_eq_some
                  simp [Δw, Function.update, hp_ne_a, hp_ne_b]
                obtain ⟨Dpair, hden_pair_raw, hDpair_ty⟩ :=
                  denote_pair_some_of_some hden_var_a hden_var_b
                have hden_pair :
                    ⟦(SMT.Term.pair (SMT.Term.var a) (SMT.Term.var b)).abstract Δw
                        (by
                          intro v hv
                          have hv' :
                              v ∈ SMT.fv (SMT.Term.var a) ∨ v ∈ SMT.fv (SMT.Term.var b) := by
                            simpa [SMT.fv, List.mem_append] using hv
                          rcases hv' with hva | hvb
                          · exact hcov_var_a _ hva
                          · exact hcov_var_b _ hvb)⟧ˢ = some Dpair := by
                  simpa [SMT.Term.abstract, proof_irrel_heq] using hden_pair_raw
                have hcov_eq :
                    RenamingContext.CoversFV Δw
                      ((SMT.Term.var p) =ˢ (SMT.Term.pair (SMT.Term.var a) (SMT.Term.var b))) := by
                  intro v hv
                  have hv' :
                      v ∈ SMT.fv (SMT.Term.var p) ∨
                        v ∈ SMT.fv (SMT.Term.pair (SMT.Term.var a) (SMT.Term.var b)) := by
                    simpa [SMT.fv, or_assoc] using hv
                  rcases hv' with hvp | hvpair
                  · exact hcov_var_p _ hvp
                  · have hcov_pair :
                        RenamingContext.CoversFV Δw (SMT.Term.pair (SMT.Term.var a) (SMT.Term.var b)) := by
                      intro v hv'
                      have hv'' :
                          v ∈ SMT.fv (SMT.Term.var a) ∨ v ∈ SMT.fv (SMT.Term.var b) := by
                        simpa [SMT.fv, List.mem_append] using hv'
                      rcases hv'' with hva | hvb
                      · exact hcov_var_a _ hva
                      · exact hcov_var_b _ hvb
                    exact hcov_pair _ hvpair
                obtain ⟨Deq, hden_eq_raw, hDeq_ty⟩ :=
                  denote_eq_some_of_some hden_var_p hden_pair (by
                    rw [hWp_ty, hDpair_ty, (hw ⟨0, by simp⟩).1, (hw ⟨1, by simp⟩).1]
                    rfl)
                have hden_eq :
                    ⟦((SMT.Term.var p) =ˢ (SMT.Term.pair (SMT.Term.var a) (SMT.Term.var b))).abstract
                        Δw hcov_eq⟧ˢ =
                      some Deq := by
                  simpa [SMT.Term.abstract, proof_irrel_heq] using hden_eq_raw
                have hcov_right :
                    RenamingContext.CoversFV Δw
                      (((@ˢT_enc) (SMT.Term.var b)) ∧ˢ
                        ((SMT.Term.var p) =ˢ (SMT.Term.pair (SMT.Term.var a) (SMT.Term.var b)))) := by
                  intro v hv
                  have hv' :
                      v ∈ SMT.fv ((@ˢT_enc) (SMT.Term.var b)) ∨
                        v ∈ SMT.fv ((SMT.Term.var p) =ˢ (SMT.Term.pair (SMT.Term.var a) (SMT.Term.var b))) := by
                    simpa [SMT.fv, List.mem_append, or_assoc] using hv
                  rcases hv' with hvT | hvEq
                  · exact hcov_T_app _ hvT
                  · exact hcov_eq _ hvEq
                obtain ⟨Dright, hden_right_raw, hDright_ty⟩ :=
                  denote_and_some_bool_of_some_bool hden_Tb hDTb_ty hden_eq hDeq_ty
                have hden_right :
                    ⟦(((@ˢT_enc) (SMT.Term.var b)) ∧ˢ
                        ((SMT.Term.var p) =ˢ (SMT.Term.pair (SMT.Term.var a) (SMT.Term.var b)))).abstract
                        Δw hcov_right⟧ˢ =
                      some Dright := by
                  simpa [Δw, SMT.Term.abstract, proof_irrel_heq] using hden_right_raw
                obtain ⟨Dbody, hden_body_raw, hDbody_ty⟩ :=
                  denote_and_some_bool_of_some_bool hden_Sa hDSa_ty hden_right hDright_ty
                have hden_body :
                    ⟦body.abstract Δw (hcov_body_upd Wp (w ⟨0, by simp⟩) (w ⟨1, by simp⟩))⟧ˢ =
                      some Dbody := by
                  simpa [body, Δw, SMT.Term.abstract, proof_irrel_heq] using hden_body_raw
                exact ⟨Dbody, hden_body, hDbody_ty⟩
              have hgo_cov_exists :
                  ∀ (Wp : SMT.Dom) (hWp_ty : Wp.snd.fst = pairTy),
                    ∀ v ∈ SMT.fv body, v ∉ [a, b] →
                      (Function.update Δ'' p (some Wp) v).isSome = true := by
                intro Wp hWp_ty v hv hv_not_ab
                exact hφ_exists_at Wp hWp_ty v
                  (by
                    have hv_not_ab' : ¬ v = a ∧ ¬ v = b := by
                      simpa [List.mem_cons, List.mem_singleton, not_or] using hv_not_ab
                    simpa [SMT.fv, List.mem_removeAll_iff] using ⟨hv, hv_not_ab'⟩)
              have den_body_isSome :
                  ∀ (Wp : SMT.Dom) (hWp_ty : Wp.snd.fst = pairTy)
                    {w : Fin [a, b].length → SMT.Dom},
                      (∀ i, (w i).snd.fst = [αx.toSMTType, βx.toSMTType][i] ∧
                        (w i).fst ∈ ⟦[αx.toSMTType, βx.toSMTType][i]⟧ᶻ) →
                        ⟦(Term.abstract.go body [a, b]
                            (Function.update Δ'' p (some Wp))
                            (hgo_cov_exists Wp hWp_ty)).uncurry w⟧ˢ.isSome = true := by
                intro Wp hWp_ty w hw
                obtain ⟨Dbody, hden_body, _⟩ := den_body_some Wp hWp_ty (w := w) hw
                exact Option.isSome_of_eq_some hden_body
              have den_not_body_isSome :
                  ∀ (Wp : SMT.Dom) (hWp_ty : Wp.snd.fst = pairTy)
                    {w : Fin [a, b].length → SMT.Dom},
                      (∀ i, (w i).snd.fst = [αx.toSMTType, βx.toSMTType][i] ∧
                        (w i).fst ∈ ⟦[αx.toSMTType, βx.toSMTType][i]⟧ᶻ) →
                        ⟦¬ˢ' (Term.abstract.go body [a, b]
                            (Function.update Δ'' p (some Wp))
                            (hgo_cov_exists Wp hWp_ty)).uncurry w⟧ˢ.isSome = true := by
                intro Wp hWp_ty w hw
                obtain ⟨Dbody, hden_body, hDbody_ty⟩ := den_body_some Wp hWp_ty (w := w) hw
                exact denote_not_isSome_of_some_bool hden_body hDbody_ty
              have hsome_exists_at :
                  ∀ (Wp : SMT.Dom) (hWp_ty : Wp.snd.fst = pairTy),
                    ⟦(SMT.Term.exists [a, b] [αx.toSMTType, βx.toSMTType] body).abstract
                        (Function.update Δ'' p (some Wp))
                        (hφ_exists_at Wp hWp_ty)⟧ˢ.isSome = true := by
                intro Wp hWp_ty
                rw [SMT.Term.abstract, dite_cond_eq_true (eq_true (by rfl)), SMT.PHOAS.Term.exists,
                  SMT.denote]
                simp only [Option.bind_eq_bind, Option.pure_def]
                have hlen_exists : [a, b].length > 0 := by
                  simp
                rw [SMT.denote, dite_cond_eq_true (eq_true hlen_exists)]
                split_ifs with den_exists_isSome
                · simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_one_sub_one,
                    List.getElem_cons_succ, Fin.zero_eta, Fin.isValue, Fin.coe_ofNat_eq_mod,
                    Nat.zero_mod, List.getElem_cons_zero, ZFSet.get, Fin.reduceLast,
                    dite_eq_ite, Option.pure_def, Option.failure_eq_none, Option.bind_some,
                    Option.isSome_some]
                · exfalso
                  apply den_exists_isSome
                  intro w hw
                  change
                    ⟦¬ˢ'
                        (Term.abstract.go body [a, b]
                          (Function.update Δ'' p (some Wp))
                          (hgo_cov_exists Wp hWp_ty)).uncurry w⟧ˢ.isSome = true
                  exact den_not_body_isSome Wp hWp_ty (w := w) hw
              let existsTerm : SMT.Term :=
                SMT.Term.exists [a, b] [αx.toSMTType, βx.toSMTType] body
              have hcov_exists_upd :
                  ∀ Wp : SMT.Dom,
                    RenamingContext.CoversFV
                      (Function.update Δ'' p (some Wp))
                      existsTerm := by
                intro Wp v hv
                by_cases hvp : v = p
                · subst hvp
                  simp [Function.update]
                · have hcov0 :=
                    hφ_exists_at
                      ⟨pairTy.defaultZFSet, pairTy,
                        SMTType.mem_toZFSet_of_defaultZFSet⟩
                      rfl v hv
                  simpa [Function.update_of_ne hvp] using hcov0
              have hgo_cov_tcprod :
                  ∀ v ∈ SMT.fv existsTerm, v ∉ [p] →
                    (Δ'' v).isSome = true := by
                intro v hv hvp
                have hvp' : v ≠ p := by
                  simpa [List.mem_singleton] using hvp
                have hcov0 :=
                  hφ_exists_at
                    ⟨pairTy.defaultZFSet, pairTy,
                      SMTType.mem_toZFSet_of_defaultZFSet⟩
                    rfl v hv
                simpa [Function.update_of_ne hvp'] using hcov0
              have hcov_tcprod :
                  RenamingContext.CoversFV Δ'' tcprod := by
                intro v hv
                dsimp [tcprod, existsTerm] at hv
                rw [SMT.fv, List.mem_removeAll_iff] at hv
                rcases hv with ⟨hv, hvp⟩
                have hvp' : v ≠ p := by
                  simpa [List.mem_singleton] using hvp
                have hcov0 :=
                  hcov_exists_upd
                    ⟨pairTy.defaultZFSet, pairTy,
                      SMTType.mem_toZFSet_of_defaultZFSet⟩
                    v hv
                simpa [Function.update_of_ne hvp'] using hcov0
              have typ_tcprod_ctx :
                  ctx ⊢ˢ tcprod : (BType.set (αx ×ᴮ βx)).toSMTType := by
                dsimp [tcprod, existsTerm]
                have hp_in_exists_ctx :
                    p ∈ ctx.insert p pairTy := by
                  rw [AList.mem_insert]
                  exact Or.inl rfl
                have fresh_exists :
                    ∀ v ∈ [p], v ∉ SMT.bv
                      (SMT.Term.exists [a, b] [αx.toSMTType, βx.toSMTType] body) := by
                  intro v hv
                  rw [List.mem_singleton] at hv
                  subst hv
                  intro hbv
                  exact (SMT.Typing.bv_notMem_context typ_exists _ hbv) hp_in_exists_ctx
                have len_eq_p : [p].length = [pairTy].length := by
                  simp [pairTy]
                apply SMT.Typing.lambda
                  (Γ := ctx) (vs := [p]) (τs := [pairTy]) (len_eq := len_eq_p)
                · intro v hv
                  rw [List.mem_singleton] at hv
                  subst hv
                  exact p_fresh
                · exact fresh_exists
                · simp
                · have hupdate_p :
                      SMT.TypeContext.update ctx [p] [pairTy] len_eq_p =
                        ctx.insert p pairTy := by
                    unfold SMT.TypeContext.update
                    simp only [List.length_cons, List.length_nil, zero_add,
                      Nat.reduceAdd, Fin.cast_eq_self, Fin.getElem_fin,
                      Fin.val_eq_zero, List.getElem_cons_zero, Fin.foldl_succ,
                      Fin.foldl_zero]
                  rw [hupdate_p]
                  exact typ_exists
              have hsome_tcprod :
                  ⟦tcprod.abstract Δ'' hcov_tcprod⟧ˢ.isSome = true := by
                dsimp [tcprod, existsTerm]
                rw [SMT.Term.abstract, dite_cond_eq_true (eq_true (by rfl)),
                  SMT.denote]
                have hlen_p : [p].length > 0 := by
                  simp
                rw [dite_cond_eq_true (eq_true hlen_p)]
                split_ifs with den_t_isSome den_t_typ_det
                · simp
                · exfalso
                  apply den_t_typ_det
                  intro x y hx hy
                  let Wx : SMT.Dom := x ⟨0, by simp⟩
                  let Wy : SMT.Dom := y ⟨0, by simp⟩
                  have hWx_ty : Wx.snd.fst = pairTy := by
                    simpa [Wx, pairTy] using (hx ⟨0, by simp⟩).1
                  have hWy_ty : Wy.snd.fst = pairTy := by
                    simpa [Wy, pairTy] using (hy ⟨0, by simp⟩).1
                  obtain ⟨Dx, hDx⟩ := Option.isSome_iff_exists.mp
                    (hsome_exists_at Wx hWx_ty)
                  obtain ⟨Dy, hDy⟩ := Option.isSome_iff_exists.mp
                    (hsome_exists_at Wy hWy_ty)
                  have hgo_x :=
                    funAbstractGoSingle
                      (Δctx := Δ'') (P := existsTerm) (v := p) (τ := pairTy)
                      hgo_cov_tcprod hcov_exists_upd x hx
                  have hgo_y :=
                    funAbstractGoSingle
                      (Δctx := Δ'') (P := existsTerm) (v := p) (τ := pairTy)
                      hgo_cov_tcprod hcov_exists_upd y hy
                  have hden_x :
                      ⟦(SMT.Term.abstract.go existsTerm [p] Δ'' hgo_cov_tcprod).uncurry x⟧ˢ =
                        some Dx := by
                    rw [hgo_x]
                    exact hDx
                  have hden_y :
                      ⟦(SMT.Term.abstract.go existsTerm [p] Δ'' hgo_cov_tcprod).uncurry y⟧ˢ =
                        some Dy := by
                    rw [hgo_y]
                    exact hDy
                  calc
                    (⟦(SMT.Term.abstract.go existsTerm [p] Δ'' hgo_cov_tcprod).uncurry x⟧ˢ.get
                        (den_t_isSome hx)).snd.fst = Dx.snd.fst := by
                          exact congrArg (fun d : SMT.Dom => d.snd.fst)
                            (Option.get_of_eq_some (den_t_isSome hx) hden_x)
                    _ = SMTType.bool := by
                      exact denote_type_eq_of_typing (typ_t := typ_exists) (hden := hDx)
                    _ = Dy.snd.fst := by
                      exact (denote_type_eq_of_typing (typ_t := typ_exists)
                        (hden := hDy)).symm
                    _ =
                      (⟦(SMT.Term.abstract.go existsTerm [p] Δ'' hgo_cov_tcprod).uncurry y⟧ˢ.get
                        (den_t_isSome hy)).snd.fst := by
                          exact (congrArg (fun d : SMT.Dom => d.snd.fst)
                            (Option.get_of_eq_some (den_t_isSome hy) hden_y)).symm
                · exfalso
                  apply den_t_isSome
                  intro x hx
                  let Wx : SMT.Dom := x ⟨0, by simp⟩
                  have hWx_ty : Wx.snd.fst = pairTy := by
                    simpa [Wx, pairTy] using (hx ⟨0, by simp⟩).1
                  have hgo_x :=
                    funAbstractGoSingle
                      (Δctx := Δ'') (P := existsTerm) (v := p) (τ := pairTy)
                      hgo_cov_tcprod hcov_exists_upd x hx
                  rw [hgo_x]
                  exact hsome_exists_at Wx hWx_ty
              have hden :
                  ∃ a : ZFSet,
                    ∃ h : a ∈ ⟦pairTy.fun SMTType.bool⟧ᶻ,
                      ⟦tcprod.abstract Δ'' hcov_tcprod⟧ˢ =
                        some ⟨a, ⟨pairTy.fun SMTType.bool, h⟩⟩ := by
                obtain ⟨D, hD⟩ := Option.isSome_iff_exists.mp hsome_tcprod
                rcases D with ⟨a, τa, ha⟩
                have hτa : τa = pairTy.fun SMTType.bool := by
                  exact denote_type_eq_of_typing (typ_t := typ_tcprod_ctx) (hden := hD)
                cases hτa
                exact ⟨a, ha, hD⟩
              rcases hden with ⟨tcprodVal, ha, hden⟩
              refine ⟨⟨tcprodVal, ⟨pairTy.fun SMTType.bool, ha⟩⟩, hden, ?_⟩
              rw [RDom]
              constructor
              · rfl
              · have ha_func :
                    ZFSet.IsFunc ⟦pairTy⟧ᶻ ⟦SMTType.bool⟧ᶻ tcprodVal := by
                  have ha_mem :
                      tcprodVal ∈ ⟦pairTy⟧ᶻ.funs ⟦SMTType.bool⟧ᶻ := by
                    simpa [pairTy, SMTType.toZFSet] using ha
                  rw [ZFSet.mem_funs] at ha_mem
                  exact ha_mem
                have hden' := hden
                dsimp [tcprod, existsTerm] at hden'
                rw [SMT.Term.abstract, dite_cond_eq_true (eq_true (by rfl)),
                  SMT.denote] at hden'
                have hlen_p : [p].length > 0 := by
                  simp
                rw [dite_cond_eq_true (eq_true hlen_p)] at hden'
                split_ifs at hden' with den_t_isSome den_t_typ_det
                · simp at hden'
                  let defaultArg : Fin [p].length → SMT.Dom := fun i =>
                    ⟨[pairTy][↑i].defaultZFSet,
                      ⟨[pairTy][↑i], SMTType.mem_toZFSet_of_defaultZFSet⟩⟩
                  have hdefaultArg :
                      ∀ i : Fin [p].length,
                        ((defaultArg i).snd.fst =
                            match i with
                            | ⟨i, _⟩ => [pairTy][i]) ∧
                          (defaultArg i).fst ∈
                            ⟦match i with
                              | ⟨i, _⟩ => [pairTy][i]⟧ᶻ := by
                    rintro ⟨i, hi⟩
                    have hi0 : i = 0 := by
                      simp at hi
                      exact hi
                    have hiFin : (⟨i, hi⟩ : Fin [p].length) = ⟨0, by simp⟩ := by
                      apply Fin.ext
                      exact hi0
                    cases hiFin
                    exact ⟨rfl, SMTType.mem_toZFSet_of_defaultZFSet⟩
                  set γ : SMTType :=
                    ((⟦(SMT.Term.abstract.go existsTerm [p] Δ'' hgo_cov_tcprod).uncurry
                        defaultArg⟧ˢ).get
                      (den_t_isSome hdefaultArg)).snd.fst
                  set bodyFun : ZFSet → ZFSet := fun x_1 =>
                    if hx : x_1.hasArity 1 ∧
                        ∃ a₀ ∈ ⟦αx.toSMTType⟧ᶻ, ∃ b₀ ∈ ⟦βx.toSMTType⟧ᶻ, x_1 = a₀.pair b₀ then
                      let hx_mem : x_1 ∈ ⟦pairTy⟧ᶻ := by
                        rcases hx.2 with ⟨a₀, ha₀, b₀, hb₀, rfl⟩
                        simpa [pairTy, SMTType.toZFSet, ZFSet.pair_mem_prod] using
                          And.intro ha₀ hb₀
                      (⟦(SMT.Term.abstract.go existsTerm [p] Δ'' hgo_cov_tcprod).uncurry
                          (fun _ => ⟨x_1, ⟨pairTy, hx_mem⟩⟩)⟧ˢ.get
                        (den_t_isSome (by
                          intro i
                          have hi0 : i = ⟨0, by simp⟩ := by
                            apply Fin.ext
                            simp
                          cases hi0
                          exact ⟨rfl, hx_mem⟩))).fst
                    else
                      γ.defaultZFSet
                  have hgo_default :=
                    funAbstractGoSingle
                      (Δctx := Δ'') (P := existsTerm) (v := p) (τ := pairTy)
                      hgo_cov_tcprod hcov_exists_upd defaultArg hdefaultArg
                  let Wdefault : SMT.Dom := defaultArg ⟨0, by simp⟩
                  have hWdefault_ty : Wdefault.snd.fst = pairTy := by
                    rfl
                  obtain ⟨Ddefault, hDdefault⟩ := Option.isSome_iff_exists.mp
                    (hsome_exists_at Wdefault hWdefault_ty)
                  have hden_default :
                      ⟦(SMT.Term.abstract.go existsTerm [p] Δ'' hgo_cov_tcprod).uncurry
                          defaultArg⟧ˢ =
                        some Ddefault := by
                    rw [hgo_default]
                    exact hDdefault
                  have hγ_eq_bool : γ = SMTType.bool := by
                    unfold γ
                    calc
                      ((⟦(SMT.Term.abstract.go existsTerm [p] Δ'' hgo_cov_tcprod).uncurry
                          defaultArg⟧ˢ).get
                        (den_t_isSome hdefaultArg)).snd.fst = Ddefault.snd.fst := by
                          exact congrArg (fun d : SMT.Dom => d.snd.fst)
                            (Option.get_of_eq_some (den_t_isSome hdefaultArg) hden_default)
                      _ = SMTType.bool := by
                        exact denote_type_eq_of_typing (typ_t := typ_exists)
                          (hden := hDdefault)
                  have ha_eq :
                      ⟦pairTy⟧ᶻ.lambda ⟦γ⟧ᶻ bodyFun = tcprodVal := by
                    simpa [γ, bodyFun, defaultArg, SMTType.toZFSet] using hden'.1
                  have hbody_bool :
                      ∀ {x_1 : ZFSet}, x_1 ∈ ⟦pairTy⟧ᶻ →
                        bodyFun x_1 ∈ ⟦SMTType.bool⟧ᶻ := by
                    intro x_1 hx_1
                    have hx_cast :
                        x_1.hasArity 1 ∧
                          ∃ a₀ ∈ ⟦αx.toSMTType⟧ᶻ, ∃ b₀ ∈ ⟦βx.toSMTType⟧ᶻ,
                            x_1 = a₀.pair b₀ := by
                      dsimp [pairTy] at hx_1
                      rw [SMTType.toZFSet, ZFSet.mem_prod] at hx_1
                      rcases hx_1 with ⟨a₀, ha₀, b₀, hb₀, rfl⟩
                      constructor
                      · simp [ZFSet.hasArity]
                      · exact ⟨a₀, ha₀, b₀, hb₀, rfl⟩
                    have hx_arg :
                        ∀ i : Fin [p].length,
                          ((fun _ => (⟨x_1, ⟨pairTy, hx_1⟩⟩ : SMT.Dom)) i).snd.fst =
                              [pairTy][i] ∧
                            ((fun _ => (⟨x_1, ⟨pairTy, hx_1⟩⟩ : SMT.Dom)) i).fst ∈
                              ⟦[pairTy][i]⟧ᶻ := by
                      rintro ⟨i, hi⟩
                      have hi0 : i = 0 := by
                        simp at hi
                        exact hi
                      subst i
                      exact ⟨rfl, hx_1⟩
                    simp only [bodyFun, hx_cast, dite_cond_eq_true (eq_true hx_cast)]
                    let Dx : SMT.Dom :=
                      ((⟦(SMT.Term.abstract.go existsTerm [p] Δ'' hgo_cov_tcprod).uncurry
                          (fun _ => ⟨x_1, ⟨pairTy, hx_1⟩⟩)⟧ˢ).get
                        (den_t_isSome hx_arg))
                    have hDx_ty : Dx.snd.fst = γ := by
                      exact den_t_typ_det
                        (fun _ => ⟨x_1, ⟨pairTy, hx_1⟩⟩)
                        defaultArg
                        hx_arg
                        hdefaultArg
                    have hDx_mem : Dx.fst ∈ ⟦γ⟧ᶻ := by
                      have hDx_mem' : Dx.fst ∈ ⟦Dx.snd.fst⟧ᶻ := Dx.snd.snd
                      rw [hDx_ty] at hDx_mem'
                      exact hDx_mem'
                    simpa [hγ_eq_bool, Dx] using hDx_mem
                  have hLamFunc :
                      ZFSet.IsFunc ⟦pairTy⟧ᶻ ⟦SMTType.bool⟧ᶻ
                        (⟦pairTy⟧ᶻ.lambda ⟦SMTType.bool⟧ᶻ bodyFun) := by
                    exact ZFSet.lambda_isFunc (fun {z} hz => hbody_bool hz)
                  have ha_eq_bool :
                      tcprodVal = ⟦pairTy⟧ᶻ.lambda ⟦SMTType.bool⟧ᶻ bodyFun := by
                    simpa [hγ_eq_bool] using ha_eq.symm
                  have happ_a_eq_bodyFun :
                      ∀ {x_1 : ZFSet} (hx_1 : x_1 ∈ ⟦pairTy⟧ᶻ),
                        ZFSet.fapply tcprodVal (ZFSet.is_func_is_pfunc ha_func)
                            ⟨x_1, by
                              rw [ZFSet.is_func_dom_eq ha_func]
                              exact hx_1⟩ =
                          bodyFun x_1 := by
                    intro x_1 hx_1
                    have happ_lam :
                        ZFSet.fapply
                            (⟦pairTy⟧ᶻ.lambda ⟦SMTType.bool⟧ᶻ bodyFun)
                            (ZFSet.is_func_is_pfunc hLamFunc)
                            ⟨x_1, by
                              rw [ZFSet.is_func_dom_eq hLamFunc]
                              exact hx_1⟩ =
                          bodyFun x_1 := by
                      rw [ZFSet.fapply_lambda
                        (hf := by
                          intro z hz
                          exact hbody_bool hz)
                        (ha := hx_1)]
                    cases ha_eq_bool
                    exact happ_lam
                  have hbody_true_of_prod :
                      ∀ {x_1 : ZFSet}, x_1 ∈ ⟦pairTy⟧ᶻ →
                        retract (αx ×ᴮ βx) x_1 ∈ X.prod Y →
                          bodyFun x_1 = zftrue := by
                    intro x_1 hx_1 hx_prod
                    have hx_cast :
                        x_1.hasArity 1 ∧
                          ∃ a₀ ∈ ⟦αx.toSMTType⟧ᶻ, ∃ b₀ ∈ ⟦βx.toSMTType⟧ᶻ,
                            x_1 = a₀.pair b₀ := by
                        exact mem_toZFSet_pair_inv hx_1
                    rcases hx_cast.2 with ⟨a₀, ha₀, b₀, hb₀, rfl⟩
                    have hpair_mem : a₀.pair b₀ ∈ ⟦pairTy⟧ᶻ := by
                        simpa [pairTy, SMTType.toZFSet, ZFSet.pair_mem_prod] using
                          And.intro ha₀ hb₀
                    have hprod_pair :
                      (retract αx a₀).pair (retract βx b₀) ∈ X.prod Y := by
                      simpa [retract] using hx_prod
                    rw [ZFSet.pair_mem_prod] at hprod_pair
                    rcases hprod_pair with ⟨haX, hbY⟩
                    let Wp : SMT.Dom := ⟨a₀.pair b₀, pairTy, hpair_mem⟩
                    let Wa : SMT.Dom := ⟨a₀, αx.toSMTType, ha₀⟩
                    let Wb : SMT.Dom := ⟨b₀, βx.toSMTType, hb₀⟩
                    let Δw : SMT.RenamingContext.Context :=
                      Function.update (Function.update (Function.update Δ'' p (some Wp)) a (some Wa)) b (some Wb)
                    have hpair_arg :
                        ∀ i : Fin [p].length,
                          ((fun _ => Wp) i).snd.fst = [pairTy][i] ∧
                            ((fun _ => Wp) i).fst ∈ ⟦[pairTy][i]⟧ᶻ := by
                      rintro ⟨i, hi⟩
                      have hi0 : i = 0 := by
                        simp at hi
                        exact hi
                      subst i
                      exact ⟨rfl, hpair_mem⟩
                    have hgo_pair :=
                      funAbstractGoSingle
                        (Δctx := Δ'') (P := existsTerm) (v := p) (τ := pairTy)
                        hgo_cov_tcprod hcov_exists_upd (fun _ => Wp) hpair_arg
                    have hcov_S_Wp :
                        RenamingContext.CoversFV
                          (Function.update (Function.update Δ'' p (some Wp)) b (some Wb))
                          S_enc := by
                      exact SMT.RenamingContext.coversFV_update_of_notMem
                        (x := b) (d := Wb) hb_not_fv_S_enc
                        (SMT.RenamingContext.coversFV_update_of_notMem
                          (x := p) (d := Wp) hp_not_fv_S_enc hΔ_S_final)
                    have den_S_Wp :
                        ∀ Xarg : SMT.Dom,
                          ⟦S_enc.abstract
                              (Function.update
                                (Function.update
                                  (Function.update Δ'' p (some Wp))
                                  b (some Wb))
                                a (some Xarg))
                              (SMT.RenamingContext.coversFV_update_of_notMem
                                (x := a) (d := Xarg) ha_not_fv_S_enc hcov_S_Wp)⟧ˢ =
                            some ⟨Senc, ⟨αx.set.toSMTType, hSenc⟩⟩ := by
                      intro Xarg
                      have hden_a_raw :
                          ⟦S_enc.abstract
                              (Function.update
                                (Function.update
                                  (Function.update Δ'' p (some Wp))
                                  b (some Wb))
                                a (some Xarg))
                              (SMT.RenamingContext.coversFV_update_of_notMem
                                (x := a) (d := Xarg) ha_not_fv_S_enc hcov_S_Wp)⟧ˢ =
                            ⟦S_enc.abstract
                                (Function.update
                                (Function.update Δ'' p (some Wp))
                                  b (some Wb))
                                hcov_S_Wp⟧ˢ := by
                        simpa [SMT.RenamingContext.denote] using
                          (SMT.RenamingContext.denote_update_of_notMem
                            («Δ» := Function.update
                              (Function.update Δ'' p (some Wp))
                              b (some Wb))
                            (t := S_enc) (x := a) (d := Xarg)
                            (h := hcov_S_Wp) ha_not_fv_S_enc).symm
                      have hcov_S_p :
                          RenamingContext.CoversFV
                            (Function.update Δ'' p (some Wp))
                            S_enc := by
                        exact SMT.RenamingContext.coversFV_update_of_notMem
                          (x := p) (d := Wp) hp_not_fv_S_enc hΔ_S_final
                      have hden_b_raw :
                          ⟦S_enc.abstract
                              (Function.update
                                (Function.update Δ'' p (some Wp))
                                b (some Wb))
                              hcov_S_Wp⟧ˢ =
                            ⟦S_enc.abstract
                                (Function.update Δ'' p (some Wp))
                                hcov_S_p⟧ˢ := by
                        simpa [SMT.RenamingContext.denote] using
                          (SMT.RenamingContext.denote_update_of_notMem
                            («Δ» := Function.update Δ'' p (some Wp))
                            (t := S_enc) (x := b) (d := Wb)
                            (h := hcov_S_p) hb_not_fv_S_enc).symm
                      have hden_p_raw :
                          ⟦S_enc.abstract
                              (Function.update Δ'' p (some Wp))
                              hcov_S_p⟧ˢ =
                            ⟦S_enc.abstract Δ'' hΔ_S_final⟧ˢ := by
                        simpa [SMT.RenamingContext.denote] using
                          (SMT.RenamingContext.denote_update_of_notMem
                            («Δ» := Δ'') (t := S_enc) (x := p) (d := Wp)
                            (h := hΔ_S_final) hp_not_fv_S_enc).symm
                      rw [hden_a_raw, hden_b_raw, hden_p_raw]
                      exact den_S_enc_final
                    obtain ⟨hcov_Sa, DSa, hDSa_ty, hDSa_val, hden_Sa⟩ :=
                    funDenoteAppAt
                      (Δctx := Function.update
                        (Function.update Δ'' p (some Wp))
                        b (some Wb))
                      (t := S_enc) (x := a)
                      (α := αx.toSMTType) (β := SMTType.bool)
                      (Y := ⟨Senc, ⟨αx.set.toSMTType, hSenc⟩⟩)
                      (hcov_t_upd := by
                        intro Xarg
                        exact SMT.RenamingContext.coversFV_update_of_notMem
                          (x := a) (d := Xarg) ha_not_fv_S_enc hcov_S_Wp)
                      (den_t_upd := by
                        intro Xarg
                        exact den_S_Wp Xarg)
                      (hY_ty := rfl)
                      (hY_func := hSenc_func)
                      (Xarg := Wa)
                      (hXarg_ty := rfl)
                      (hXarg_mem := ha₀)
                    have ha₀_mem : retract αx a₀ ∈ ⟦αx⟧ᶻ := by
                      exact retract_mem_of_toSMTType ha₀
                    have hcanon_a₀ :
                        ZFSet.fapply (BType.canonicalIsoSMTType αx).1
                            (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType αx).2.1)
                            ⟨retract αx a₀, by
                              rwa [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType αx).2.1]⟩ =
                          a₀ := by
                      simpa using canonical_of_retract αx ha₀
                    have hDSa_true : DSa.fst = zftrue := by
                      have hSenc_true := (mem_retract_set_iff_app_canonical_eq_zftrue
                        (α := αx) hSenc_func retract_Senc_eq_X ha₀_mem).mp haX
                      simpa [proof_irrel_heq, hcanon_a₀, hDSa_val] using hSenc_true
                    have hcov_T_Wp :
                        RenamingContext.CoversFV
                          (Function.update (Function.update Δ'' p (some Wp)) a (some Wa))
                          T_enc := by
                      exact SMT.RenamingContext.coversFV_update_of_notMem
                        (x := a) (d := Wa) ha_not_fv_T_enc
                        (SMT.RenamingContext.coversFV_update_of_notMem
                          (x := p) (d := Wp) hp_not_fv_T_enc Δ''_covers_T)
                    have den_T_Wp :
                        ∀ Xarg : SMT.Dom,
                          ⟦T_enc.abstract
                              (Function.update
                                (Function.update
                                  (Function.update Δ'' p (some Wp))
                                  a (some Wa))
                                b (some Xarg))
                              (SMT.RenamingContext.coversFV_update_of_notMem
                                (x := b) (d := Xarg) hb_not_fv_T_enc hcov_T_Wp)⟧ˢ =
                            some ⟨Tenc, ⟨βx.set.toSMTType, hTenc⟩⟩ := by
                      intro Xarg
                      have hden_b_raw :
                          ⟦T_enc.abstract
                              (Function.update
                                (Function.update
                                  (Function.update Δ'' p (some Wp))
                                  a (some Wa))
                                b (some Xarg))
                              (SMT.RenamingContext.coversFV_update_of_notMem
                                (x := b) (d := Xarg) hb_not_fv_T_enc hcov_T_Wp)⟧ˢ =
                            ⟦T_enc.abstract
                                (Function.update
                                (Function.update Δ'' p (some Wp))
                                  a (some Wa))
                                hcov_T_Wp⟧ˢ := by
                        simpa [SMT.RenamingContext.denote] using
                          (SMT.RenamingContext.denote_update_of_notMem
                            («Δ» := Function.update
                              (Function.update Δ'' p (some Wp))
                              a (some Wa))
                            (t := T_enc) (x := b) (d := Xarg)
                            (h := hcov_T_Wp) hb_not_fv_T_enc).symm
                      have hcov_T_p :
                          RenamingContext.CoversFV
                            (Function.update Δ'' p (some Wp))
                            T_enc := by
                        exact SMT.RenamingContext.coversFV_update_of_notMem
                          (x := p) (d := Wp) hp_not_fv_T_enc Δ''_covers_T
                      have hden_a_raw :
                          ⟦T_enc.abstract
                              (Function.update
                                (Function.update Δ'' p (some Wp))
                                a (some Wa))
                              hcov_T_Wp⟧ˢ =
                            ⟦T_enc.abstract
                                (Function.update Δ'' p (some Wp))
                                hcov_T_p⟧ˢ := by
                        simpa [SMT.RenamingContext.denote] using
                          (SMT.RenamingContext.denote_update_of_notMem
                            («Δ» := Function.update Δ'' p (some Wp))
                            (t := T_enc) (x := a) (d := Wa)
                            (h := hcov_T_p) ha_not_fv_T_enc).symm
                      have hden_p_raw :
                          ⟦T_enc.abstract
                              (Function.update Δ'' p (some Wp))
                              hcov_T_p⟧ˢ =
                            ⟦T_enc.abstract Δ'' Δ''_covers_T⟧ˢ := by
                        simpa [SMT.RenamingContext.denote] using
                          (SMT.RenamingContext.denote_update_of_notMem
                            («Δ» := Δ'') (t := T_enc) (x := p) (d := Wp)
                            (h := Δ''_covers_T) hp_not_fv_T_enc).symm
                      rw [hden_b_raw, hden_a_raw, hden_p_raw]
                      exact den_T_enc
                    obtain ⟨hcov_Tb, DTb, hDTb_ty, hDTb_val, hden_Tb⟩ :=
                      funDenoteAppAt
                        (Δctx := Function.update
                          (Function.update Δ'' p (some Wp))
                          a (some Wa))
                        (t := T_enc) (x := b)
                        (α := βx.toSMTType) (β := SMTType.bool)
                        (Y := ⟨Tenc, ⟨βx.set.toSMTType, hTenc⟩⟩)
                        (hcov_t_upd := by
                          intro Xarg
                          exact SMT.RenamingContext.coversFV_update_of_notMem
                            (x := b) (d := Xarg) hb_not_fv_T_enc hcov_T_Wp)
                        (den_t_upd := by
                          intro Xarg
                          exact den_T_Wp Xarg)
                        (hY_ty := rfl)
                        (hY_func := hTenc_func)
                        (Xarg := Wb)
                        (hXarg_ty := rfl)
                        (hXarg_mem := hb₀)
                    have hb₀_mem : retract βx b₀ ∈ ⟦βx⟧ᶻ := by
                      exact retract_mem_of_toSMTType hb₀
                    have hcanon_b₀ :
                        ZFSet.fapply (BType.canonicalIsoSMTType βx).1
                            (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType βx).2.1)
                            ⟨retract βx b₀, by
                              rwa [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType βx).2.1]⟩ =
                          b₀ := by
                      simpa using canonical_of_retract βx hb₀
                    have hDTb_true : DTb.fst = zftrue := by
                      have hTenc_true := (mem_retract_set_iff_app_canonical_eq_zftrue
                        (α := βx) hTenc_func retract_Tenc_eq_Y hb₀_mem).mp hbY
                      simpa [proof_irrel_heq, hcanon_b₀, hDTb_val] using hTenc_true
                    have hcov_var_p :
                        RenamingContext.CoversFV Δw (SMT.Term.var p) := by
                      simpa [Δw] using
                        cprod_covers_var_p (Δctx := Δ'') (Wp := Wp) (Wa := Wa) (Wb := Wb)
                          (p := p) (a := a) (b := b) hp_ne_a hp_ne_b
                    have hden_var_p :
                        ⟦(SMT.Term.var p).abstract Δw hcov_var_p⟧ˢ = some Wp := by
                      simpa [Δw] using
                        cprod_denote_var_p (Δctx := Δ'') (Wp := Wp) (Wa := Wa) (Wb := Wb)
                          (p := p) (a := a) (b := b) hp_ne_a hp_ne_b
                    have hcov_var_a :
                        RenamingContext.CoversFV Δw (SMT.Term.var a) := by
                      simpa [Δw] using
                        cprod_covers_var_a (Δctx := Δ'') (Wp := Wp) (Wa := Wa) (Wb := Wb)
                          (p := p) (a := a) (b := b) ha_ne_b
                    have hden_var_a :
                        ⟦(SMT.Term.var a).abstract Δw hcov_var_a⟧ˢ = some Wa := by
                      simpa [Δw] using
                        cprod_denote_var_a (Δctx := Δ'') (Wp := Wp) (Wa := Wa) (Wb := Wb)
                          (p := p) (a := a) (b := b) ha_ne_b
                    have hcov_var_b :
                        RenamingContext.CoversFV Δw (SMT.Term.var b) := by
                      simpa [Δw] using
                        cprod_covers_var_b (Δctx := Δ'') (Wp := Wp) (Wa := Wa) (Wb := Wb)
                          (p := p) (a := a) (b := b)
                    have hden_var_b :
                        ⟦(SMT.Term.var b).abstract Δw hcov_var_b⟧ˢ = some Wb := by
                      simpa [Δw] using
                        cprod_denote_var_b (Δctx := Δ'') (Wp := Wp) (Wa := Wa) (Wb := Wb)
                          (p := p) (a := a) (b := b)
                    obtain ⟨Dpair, hden_pair_raw, hDpair_ty⟩ :=
                      denote_pair_some_of_some hden_var_a hden_var_b
                    have hpair_eq_raw := hden_pair_raw
                    rw [SMT.denote, hden_var_a, hden_var_b] at hpair_eq_raw
                    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some,
                      Option.some.injEq] at hpair_eq_raw
                    have hWp_eq_Dpair : Wp = Dpair := by
                      simpa [Wp, Wa, Wb, pairTy] using hpair_eq_raw
                    have hcov_eq :
                        RenamingContext.CoversFV Δw
                          (SMT.Term.var p =ˢ (SMT.Term.var a).pair (SMT.Term.var b)) := by
                      simpa [body, Δw] using
                        cprod_body_covers_eq
                          («Δ» := Δ'') (Wp := Wp) (Wa := Wa) (Wb := Wb)
                          (p := p) (a := a) (b := b) (S_enc := S_enc) (T_enc := T_enc)
                          (hcov_body_upd := hcov_body_upd Wp Wa Wb)
                    have hden_eq_true :
                        ⟦(SMT.Term.var p =ˢ (SMT.Term.var a).pair (SMT.Term.var b)).abstract
                            Δw hcov_eq⟧ˢ =
                          some ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
                      simpa [SMT.Term.abstract, proof_irrel_heq] using
                        (denote_eq_eq_zftrue_of_fst_eq
                          hden_var_p hden_pair_raw
                          (congrArg (fun D : SMT.Dom => D.snd.fst) hWp_eq_Dpair)
                          (congrArg (fun D : SMT.Dom => D.fst) hWp_eq_Dpair))
                    have hcov_right :
                        RenamingContext.CoversFV Δw
                          ((@ˢT_enc) (SMT.Term.var b) ∧ˢ
                            (SMT.Term.var p =ˢ (SMT.Term.var a).pair (SMT.Term.var b))) := by
                      simpa [body, Δw] using
                        cprod_body_covers_right
                          («Δ» := Δ'') (Wp := Wp) (Wa := Wa) (Wb := Wb)
                          (p := p) (a := a) (b := b) (S_enc := S_enc) (T_enc := T_enc)
                          (hcov_body_upd := hcov_body_upd Wp Wa Wb)
                    have hcov_Sa_Δw :
                        RenamingContext.CoversFV Δw ((@ˢS_enc) (SMT.Term.var a)) := by
                      simpa [body, Δw] using
                        cprod_body_covers_left
                          («Δ» := Δ'') (Wp := Wp) (Wa := Wa) (Wb := Wb)
                          (p := p) (a := a) (b := b) (S_enc := S_enc) (T_enc := T_enc)
                          (hcov_body_upd := hcov_body_upd Wp Wa Wb)
                    have hctx_Sa :
                        Function.update (Function.update (Function.update Δ'' p (some Wp))
                          b (some Wb)) a (some Wa) = Δw := by
                      simpa [Δw] using
                        cprod_update_eq (Δctx := Δ'') (Wp := Wp) (Wa := Wa) (Wb := Wb)
                          (p := p) (a := a) (b := b) hp_ne_a hp_ne_b ha_ne_b
                    have hden_Sa_Δw :
                        ⟦((@ˢS_enc) (SMT.Term.var a)).abstract Δw hcov_Sa_Δw⟧ˢ =
                          some DSa := by
                      have hden_Sa' := hden_Sa
                      simpa [hctx_Sa, proof_irrel_heq] using hden_Sa'
                    have hden_right_true :
                        ⟦((@ˢT_enc) (SMT.Term.var b) ∧ˢ
                            (SMT.Term.var p =ˢ (SMT.Term.var a).pair (SMT.Term.var b))).abstract
                            Δw hcov_right⟧ˢ =
                          some ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
                      simpa [Δw, SMT.Term.abstract, proof_irrel_heq] using
                        (denote_and_eq_zftrue_of_some_zftrue
                          hden_Tb hDTb_ty hDTb_true
                          hden_eq_true rfl rfl)
                    have hden_body_true :
                        ⟦body.abstract Δw (hcov_body_upd Wp Wa Wb)⟧ˢ =
                          some ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
                      simpa [Δw, body, SMT.Term.abstract, proof_irrel_heq] using
                        (denote_and_eq_zftrue_of_some_zftrue
                          hden_Sa_Δw hDSa_ty hDSa_true
                          hden_right_true rfl rfl)
                    have hden_exists_true := by
                      let bodyF : ZFSet → ZFSet := fun y =>
                        if hy : y.hasArity [a, b].length ∧
                            ∀ i : Fin [a, b].length,
                              y.get [a, b].length i ∈ ⟦[αx.toSMTType, βx.toSMTType][i]⟧ᶻ then
                        (⟦¬ˢ'
                            (SMT.Term.abstract.go body [a, b]
                              (Function.update Δ'' p (some Wp))
                              (hgo_cov_exists Wp rfl)).uncurry
                                (fun i =>
                                  ⟨y.get [a, b].length i,
                                    [αx.toSMTType, βx.toSMTType][i], hy.2 i⟩)⟧ˢ.get
                          (by
                            simpa [SMT.denote] using
                              (den_not_body_isSome Wp rfl
                                (w := fun i =>
                                  ⟨y.get [a, b].length i,
                                    [αx.toSMTType, βx.toSMTType][i], hy.2 i⟩)
                                (by intro i; exact ⟨rfl, hy.2 i⟩)))).fst
                      else
                        zffalse
                      let D : ZFSet := ⟦αx.toSMTType⟧ᶻ.prod ⟦βx.toSMTType⟧ᶻ
                      have hbodyF_witness :
                          bodyF (a₀.pair b₀) = zffalse := by
                        have hy :
                            (a₀.pair b₀).hasArity [a, b].length ∧
                              ∀ i : Fin [a, b].length,
                                (a₀.pair b₀).get [a, b].length i ∈
                                  ⟦[αx.toSMTType, βx.toSMTType][i]⟧ᶻ := by
                          simpa using pair_hasArity_get_mem ha₀ hb₀
                        change
                          (if hy' :
                              (a₀.pair b₀).hasArity [a, b].length ∧
                                ∀ i : Fin [a, b].length,
                                  (a₀.pair b₀).get [a, b].length i ∈
                                    ⟦[αx.toSMTType, βx.toSMTType][i]⟧ᶻ then
                              (⟦¬ˢ'
                                  (SMT.Term.abstract.go body [a, b]
                                    (Function.update Δ'' p (some Wp))
                                    (hgo_cov_exists Wp rfl)).uncurry
                                      (fun i =>
                                        ⟨(a₀.pair b₀).get [a, b].length i,
                                          [αx.toSMTType, βx.toSMTType][i], hy'.2 i⟩)⟧ˢ.get
                                (by
                                  simpa [SMT.denote] using
                                    (den_not_body_isSome Wp rfl
                                      (w := fun i =>
                                        ⟨(a₀.pair b₀).get [a, b].length i,
                                          [αx.toSMTType, βx.toSMTType][i], hy'.2 i⟩)
                                      (by intro i; exact ⟨rfl, hy'.2 i⟩)))).fst
                            else zffalse) = zffalse
                        rw [dif_pos hy]
                        have hw :
                            ∀ i : Fin [a, b].length,
                              ((fun i =>
                                  (⟨(a₀.pair b₀).get [a, b].length i,
                                    [αx.toSMTType, βx.toSMTType][i], hy.2 i⟩ : SMT.Dom)) i).snd.fst =
                                  [αx.toSMTType, βx.toSMTType][i] ∧
                                ((fun i =>
                                    (⟨(a₀.pair b₀).get [a, b].length i,
                                      [αx.toSMTType, βx.toSMTType][i], hy.2 i⟩ : SMT.Dom)) i).fst ∈
                                  ⟦[αx.toSMTType, βx.toSMTType][i]⟧ᶻ := by
                          intro i
                          exact ⟨rfl, hy.2 i⟩
                        have hgo :=
                          funAbstractGoPair
                            (Δctx := Function.update Δ'' p (some Wp))
                            (P := body) (v₁ := a) (v₂ := b)
                            (τ₁ := αx.toSMTType) (τ₂ := βx.toSMTType)
                            (hgo_cov_exists Wp rfl) (fun W₁ W₂ => hcov_body_upd Wp W₁ W₂)
                            (fun i =>
                              ⟨(a₀.pair b₀).get [a, b].length i,
                                [αx.toSMTType, βx.toSMTType][i], hy.2 i⟩) hw
                        have hw0 :
                            (fun i =>
                              ⟨(a₀.pair b₀).get [a, b].length i,
                                [αx.toSMTType, βx.toSMTType][i], hy.2 i⟩) ⟨0, by simp⟩ = Wa := by
                          apply funDomEqOfTyEqAndFstEq
                          · rfl
                          · simp [Wa, ZFSet.get]
                        have hw1 :
                            (fun i =>
                              ⟨(a₀.pair b₀).get [a, b].length i,
                                [αx.toSMTType, βx.toSMTType][i], hy.2 i⟩) ⟨1, by simp⟩ = Wb := by
                          apply funDomEqOfTyEqAndFstEq
                          · rfl
                          · simp [Wb, ZFSet.get]
                        have hden_not_false :
                            ⟦¬ˢ'
                                (SMT.Term.abstract.go body [a, b]
                                  (Function.update Δ'' p (some Wp))
                                  (hgo_cov_exists Wp rfl)).uncurry
                                    (fun i =>
                                      ⟨(a₀.pair b₀).get [a, b].length i,
                                        [αx.toSMTType, βx.toSMTType][i], hy.2 i⟩)⟧ˢ =
                              some ⟨zffalse, SMTType.bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
                          rw [hgo, hw0, hw1]
                          simpa [Δw] using
                            denote_not_eq_zffalse_of_some_zftrue hden_body_true rfl rfl
                        have hget_eq :
                            (⟦¬ˢ'
                                (SMT.Term.abstract.go body [a, b]
                                  (Function.update Δ'' p (some Wp))
                                  (hgo_cov_exists Wp rfl)).uncurry
                                    (fun i =>
                                      ⟨(a₀.pair b₀).get [a, b].length i,
                                        [αx.toSMTType, βx.toSMTType][i], hy.2 i⟩)⟧ˢ.get
                              (by
                                simpa [SMT.denote] using
                                  (den_not_body_isSome Wp rfl
                                    (w := fun i =>
                                      ⟨(a₀.pair b₀).get [a, b].length i,
                                        [αx.toSMTType, βx.toSMTType][i], hy.2 i⟩)
                                    (by intro i; exact ⟨rfl, hy.2 i⟩)))) =
                              ⟨zffalse, ⟨SMTType.bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩⟩ := by
                          apply Option.get_of_eq_some
                          exact hden_not_false
                        exact congrArg (fun D : SMT.Dom => D.fst) hget_eq
                      change
                        ⟦(SMT.Term.exists [a, b] [αx.toSMTType, βx.toSMTType] body).abstract
                            (Function.update Δ'' p (some Wp))
                            (hcov_exists_upd Wp)⟧ˢ =
                          some ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩
                      rw [SMT.Term.abstract, dite_cond_eq_true (eq_true (by rfl)),
                        SMT.PHOAS.Term.exists, SMT.denote]
                      have hsInter_mem :
                          (⋂₀ ZFSet.sep (fun y => ∃ x ∈ D, y = bodyF x) 𝔹) ∈ 𝔹 :=
                        ZFSet.sInter_sep_subset_of_𝔹_mem_𝔹 (fun _ => id)
                      have hden_forall :
                          ⟦PHOAS.Term.forall (fun x => [αx.toSMTType, βx.toSMTType][↑x]) fun x_1 =>
                              ¬ˢ' (SMT.Term.abstract.go body [a, b]
                                (Function.update Δ'' p (some Wp))
                                (hgo_cov_exists Wp rfl)).uncurry x_1⟧ˢ =
                            some ⟨⋂₀ ZFSet.sep (fun y => ∃ x ∈ D, y = bodyF x) 𝔹,
                              SMTType.bool, hsInter_mem⟩ := by
                        rw [SMT.denote]
                        rw [dif_pos (by simp)]
                        rw [dif_pos (by
                          intro x_1 hx_1
                          simpa [SMT.denote] using
                            (den_not_body_isSome Wp rfl (w := x_1) hx_1))]
                        apply congrArg some
                        apply funDomEqOfTyEqAndFstEq rfl
                        ext y
                        constructor <;> intro hy
                        · simpa [D, bodyF, Fin.foldl_succ_last, Fin.foldl_zero] using hy
                        · simpa [D, bodyF, Fin.foldl_succ_last, Fin.foldl_zero] using hy
                      have hExistsTrue :
                          overloadUnaryOp id id ZFBool.false ZFBool.not
                            (⋂₀ ZFSet.sep (fun y => ∃ x ∈ D, y = bodyF x) 𝔹) = zftrue := by
                        simpa [overloadUnaryOp, hsInter_mem, id_eq, proof_irrel_heq] using
                          (not_sInter_sep_eq_zftrue_of_exists_eq_zffalse
                            ⟨a₀.pair b₀, by
                              change a₀.pair b₀ ∈ ⟦αx.toSMTType⟧ᶻ.prod ⟦βx.toSMTType⟧ᶻ
                              rw [ZFSet.pair_mem_prod]
                              exact ⟨ha₀, hb₀⟩, hbodyF_witness⟩)
                      erw [hden_forall]
                      simp only [Option.pure_def, Option.failure_eq_none, Option.bind_eq_bind,
                        Option.bind_some, Option.some.injEq, PSigma.mk.injEq]
                      refine ⟨hExistsTrue, ?_⟩
                      congr
                      · funext τ
                        erw [hExistsTrue]
                      · apply proof_irrel_heq
                    have hbodyFun_pair :
                        bodyFun (a₀.pair b₀) =
                          (⟦(SMT.Term.abstract.go existsTerm [p] Δ'' hgo_cov_tcprod).uncurry
                              (fun _ => Wp)⟧ˢ.get
                            (den_t_isSome hpair_arg)).fst := by
                      have hx_cast_pair :
                          (a₀.pair b₀).hasArity 1 ∧
                            ∃ a' ∈ ⟦αx.toSMTType⟧ᶻ, ∃ b' ∈ ⟦βx.toSMTType⟧ᶻ,
                              a₀.pair b₀ = a'.pair b' := by
                        exact ⟨by simp [ZFSet.hasArity], a₀, ha₀, b₀, hb₀, rfl⟩
                      dsimp [bodyFun]
                      rw [dif_pos hx_cast_pair]
                    have hden_uncurry_true :
                        ⟦(SMT.Term.abstract.go existsTerm [p] Δ'' hgo_cov_tcprod).uncurry
                            (fun _ => Wp)⟧ˢ =
                          some ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
                      rw [hgo_pair]
                      exact hden_exists_true
                    have hget_eq :
                        (⟦(SMT.Term.abstract.go existsTerm [p] Δ'' hgo_cov_tcprod).uncurry
                            (fun _ => Wp)⟧ˢ.get
                          (den_t_isSome hpair_arg)) =
                          ⟨zftrue, ⟨SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩⟩ := by
                      apply Option.get_of_eq_some
                      exact hden_uncurry_true
                    rw [hbodyFun_pair]
                    exact congrArg (fun D : SMT.Dom => D.fst) hget_eq
                  have hprod_of_body_true :
                      ∀ {x_1 : ZFSet}, x_1 ∈ ⟦pairTy⟧ᶻ →
                        bodyFun x_1 = zftrue →
                          retract (αx ×ᴮ βx) x_1 ∈ X.prod Y := by
                    intro x_1 hx_1 hx_true
                    have hx_cast :
                        x_1.hasArity 1 ∧
                          ∃ a₀ ∈ ⟦αx.toSMTType⟧ᶻ, ∃ b₀ ∈ ⟦βx.toSMTType⟧ᶻ,
                            x_1 = a₀.pair b₀ := by
                        exact mem_toZFSet_pair_inv hx_1
                    rcases hx_cast.2 with ⟨a₀, ha₀, b₀, hb₀, rfl⟩
                    have hpair_mem : a₀.pair b₀ ∈ ⟦pairTy⟧ᶻ := by
                        simpa [pairTy, SMTType.toZFSet, ZFSet.pair_mem_prod] using
                          And.intro ha₀ hb₀
                    let Wp : SMT.Dom := ⟨a₀.pair b₀, pairTy, hpair_mem⟩
                    have hpair_arg :
                        ∀ i : Fin [p].length,
                          ((fun _ => Wp) i).snd.fst = [pairTy][i] ∧
                            ((fun _ => Wp) i).fst ∈ ⟦[pairTy][i]⟧ᶻ := by
                      rintro ⟨i, hi⟩
                      have hi0 : i = 0 := by
                        simp at hi
                        exact hi
                      subst i
                      exact ⟨rfl, hpair_mem⟩
                    have hgo_pair :=
                      funAbstractGoSingle
                        (Δctx := Δ'') (P := existsTerm) (v := p) (τ := pairTy)
                        hgo_cov_tcprod hcov_exists_upd (fun _ => Wp) hpair_arg
                    have hbodyFun_pair :
                        bodyFun (a₀.pair b₀) =
                          (⟦(SMT.Term.abstract.go existsTerm [p] Δ'' hgo_cov_tcprod).uncurry
                              (fun _ => Wp)⟧ˢ.get
                            (den_t_isSome hpair_arg)).fst := by
                      have hx_cast_pair :
                          (a₀.pair b₀).hasArity 1 ∧
                            ∃ a' ∈ ⟦αx.toSMTType⟧ᶻ, ∃ b' ∈ ⟦βx.toSMTType⟧ᶻ,
                              a₀.pair b₀ = a'.pair b' := by
                        exact ⟨by simp [ZFSet.hasArity], a₀, ha₀, b₀, hb₀, rfl⟩
                      dsimp [bodyFun]
                      rw [dif_pos hx_cast_pair]
                    have hget_exists_true :
                      (⟦(SMT.Term.abstract.go existsTerm [p] Δ'' hgo_cov_tcprod).uncurry
                          (fun _ => Wp)⟧ˢ.get
                        (den_t_isSome hpair_arg)).fst = zftrue := by
                      rw [← hbodyFun_pair]
                      exact hx_true
                    have hsome_exists :
                      ⟦(SMT.Term.abstract.go existsTerm [p] Δ'' hgo_cov_tcprod).uncurry
                          (fun _ => Wp)⟧ˢ.isSome = true :=
                      den_t_isSome hpair_arg
                    obtain ⟨Dexists, hden_uncurry⟩ :
                      ∃ Dexists,
                        ⟦(SMT.Term.abstract.go existsTerm [p] Δ'' hgo_cov_tcprod).uncurry
                            (fun _ => Wp)⟧ˢ = some Dexists := by
                      cases hunc : ⟦(SMT.Term.abstract.go existsTerm [p] Δ'' hgo_cov_tcprod).uncurry (fun _ => Wp)⟧ˢ with
                      | none =>
                          exfalso
                          rw [hunc] at hsome_exists
                          simp at hsome_exists
                      | some Dexists =>
                          exact ⟨Dexists, by simpa [hunc]⟩
                    have hget_exists_eq :
                      (⟦(SMT.Term.abstract.go existsTerm [p] Δ'' hgo_cov_tcprod).uncurry
                          (fun _ => Wp)⟧ˢ.get
                        (den_t_isSome hpair_arg)) = Dexists := by
                      exact Option.get_of_eq_some _ hden_uncurry
                    have hDexists_true : Dexists.fst = zftrue := by
                      rw [hget_exists_eq] at hget_exists_true
                      exact hget_exists_true
                    have hden_exists :
                      ⟦existsTerm.abstract
                          (Function.update Δ'' p (some Wp))
                          (hcov_exists_upd Wp)⟧ˢ =
                        some Dexists := by
                      rw [← hgo_pair]
                      exact hden_uncurry
                    let bodyF : ZFSet → ZFSet := fun y =>
                      if hy : y.hasArity [a, b].length ∧
                          ∀ i : Fin [a, b].length,
                            y.get [a, b].length i ∈ ⟦[αx.toSMTType, βx.toSMTType][i]⟧ᶻ then
                        (⟦¬ˢ'
                            (SMT.Term.abstract.go body [a, b]
                              (Function.update Δ'' p (some Wp))
                              (hgo_cov_exists Wp rfl)).uncurry
                                (fun i =>
                                  ⟨y.get [a, b].length i,
                                    [αx.toSMTType, βx.toSMTType][i], hy.2 i⟩)⟧ˢ.get
                          (by
                            simpa [SMT.denote] using
                              (den_not_body_isSome Wp rfl
                                (w := fun i =>
                                  ⟨y.get [a, b].length i,
                                    [αx.toSMTType, βx.toSMTType][i], hy.2 i⟩)
                                (by intro i; exact ⟨rfl, hy.2 i⟩)))).fst
                      else
                        zffalse
                    let D : ZFSet := ⟦αx.toSMTType⟧ᶻ.prod ⟦βx.toSMTType⟧ᶻ
                    have hsInter_mem :
                      (⋂₀ ZFSet.sep (fun y => ∃ x ∈ D, y = bodyF x) 𝔹) ∈ 𝔹 :=
                      ZFSet.sInter_sep_subset_of_𝔹_mem_𝔹 (fun _ => id)
                    have hden_forall :
                      ⟦PHOAS.Term.forall (fun x => [αx.toSMTType, βx.toSMTType][↑x]) fun x_1 =>
                          ¬ˢ' (SMT.Term.abstract.go body [a, b]
                            (Function.update Δ'' p (some Wp))
                            (hgo_cov_exists Wp rfl)).uncurry x_1⟧ˢ =
                        some ⟨⋂₀ ZFSet.sep (fun y => ∃ x ∈ D, y = bodyF x) 𝔹,
                          SMTType.bool, hsInter_mem⟩ := by
                      rw [SMT.denote]
                      rw [dif_pos (by simp)]
                      rw [dif_pos (by
                        intro x_1 hx_1
                        simpa [SMT.denote] using
                          (den_not_body_isSome Wp rfl (w := x_1) hx_1))]
                      apply congrArg some
                      apply funDomEqOfTyEqAndFstEq rfl
                      ext y
                      constructor <;> intro hy
                      · simpa [D, bodyF, Fin.foldl_succ_last, Fin.foldl_zero] using hy
                      · simpa [D, bodyF, Fin.foldl_succ_last, Fin.foldl_zero] using hy
                    have houter_true :
                      overloadUnaryOp id id ZFBool.false ZFBool.not
                        (⋂₀ ZFSet.sep (fun y => ∃ x ∈ D, y = bodyF x) 𝔹) = zftrue := by
                      have hden_exists' := hden_exists
                      dsimp [existsTerm] at hden_exists'
                      rw [SMT.Term.abstract, dite_cond_eq_true (eq_true (by rfl)),
                        SMT.PHOAS.Term.exists, SMT.denote] at hden_exists'
                      erw [hden_forall] at hden_exists'
                      simp only [Option.pure_def, Option.failure_eq_none, Option.bind_eq_bind,
                        Option.bind_some] at hden_exists'
                      rw [Option.some.injEq] at hden_exists'
                      simpa [hDexists_true] using
                        congrArg (fun D : SMT.Dom => D.fst) hden_exists'
                    have hsInter_false :
                      (⋂₀ ZFSet.sep (fun y => ∃ x ∈ D, y = bodyF x) 𝔹 : ZFSet) = zffalse := by
                      rw [ZFSet.ZFBool.mem_𝔹_iff] at hsInter_mem
                      rcases hsInter_mem with hsInter_false | hsInter_true
                      · exact hsInter_false
                      · exfalso
                        have : zffalse = zftrue := by
                          simpa [overloadUnaryOp, hsInter_true, id_eq, proof_irrel_heq] using
                            houter_true
                        exact ZFSet.zftrue_ne_zffalse this.symm
                    have hbodyF_bool :
                      ∀ y ∈ D, bodyF y ∈ 𝔹 := by
                      intro y hyD
                      rw [ZFSet.mem_prod] at hyD
                      rcases hyD with ⟨u, hu, v, hv, rfl⟩
                      have hy :
                          (u.pair v).hasArity [a, b].length ∧
                        ∀ i : Fin [a, b].length,
                              (u.pair v).get [a, b].length i ∈
                                ⟦[αx.toSMTType, βx.toSMTType][i]⟧ᶻ := by
                        simpa using pair_hasArity_get_mem hu hv
                      let Dnot : SMT.Dom :=
                        (⟦¬ˢ'
                            (SMT.Term.abstract.go body [a, b]
                              (Function.update Δ'' p (some Wp))
                              (hgo_cov_exists Wp rfl)).uncurry
                                (fun i =>
                                  ⟨(u.pair v).get [a, b].length i,
                                    [αx.toSMTType, βx.toSMTType][i], hy.2 i⟩)⟧ˢ.get
                          (by
                            simpa [SMT.denote] using
                              (den_not_body_isSome Wp rfl
                                (w := fun i =>
                                  ⟨(u.pair v).get [a, b].length i,
                                    [αx.toSMTType, βx.toSMTType][i], hy.2 i⟩)
                                (by intro i; exact ⟨rfl, hy.2 i⟩))))
                      have hDnot_mem_bool : Dnot.fst ∈ 𝔹 := by
                        obtain ⟨Dbody, hden_body_raw, hDbody_ty⟩ :=
                          den_body_some (Wp := Wp) (hWp_ty := rfl)
                            (w := fun i =>
                              ⟨(u.pair v).get [a, b].length i,
                                [αx.toSMTType, βx.toSMTType][i], hy.2 i⟩) (by
                            intro i
                            exact ⟨rfl, hy.2 i⟩)
                        have hDbody_mem_bool : Dbody.fst ∈ 𝔹 := by
                          simpa [hDbody_ty] using Dbody.snd.snd
                        rw [ZFSet.ZFBool.mem_𝔹_iff] at hDbody_mem_bool
                        rcases hDbody_mem_bool with hDbody_false | hDbody_true
                        · have hden_not_true :
                              ⟦¬ˢ'
                                  (SMT.Term.abstract.go body [a, b]
                                    (Function.update Δ'' p (some Wp))
                                    (hgo_cov_exists Wp rfl)).uncurry
                                      (fun i =>
                                        ⟨(u.pair v).get [a, b].length i,
                                          [αx.toSMTType, βx.toSMTType][i], hy.2 i⟩)⟧ˢ =
                                some ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
                            exact denote_not_eq_zftrue_of_some_zffalse hden_body_raw hDbody_ty hDbody_false
                          have hget :
                              Dnot = ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
                            unfold Dnot
                            apply Option.get_of_eq_some
                            exact hden_not_true
                          simpa [hget] using ZFSet.ZFBool.zftrue_mem_𝔹
                        · have hden_not_false :
                              ⟦¬ˢ'
                                  (SMT.Term.abstract.go body [a, b]
                                    (Function.update Δ'' p (some Wp))
                                    (hgo_cov_exists Wp rfl)).uncurry
                                      (fun i =>
                                        ⟨(u.pair v).get [a, b].length i,
                                          [αx.toSMTType, βx.toSMTType][i], hy.2 i⟩)⟧ˢ =
                                some ⟨zffalse, SMTType.bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
                            exact denote_not_eq_zffalse_of_some_zftrue hden_body_raw hDbody_ty hDbody_true
                          have hget :
                              Dnot = ⟨zffalse, SMTType.bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
                            unfold Dnot
                            apply Option.get_of_eq_some
                            exact hden_not_false
                          simpa [hget] using ZFSet.ZFBool.zffalse_mem_𝔹
                      unfold bodyF
                      split_ifs with hy'
                      · simpa [Dnot, ZFSet.get, proof_irrel_heq] using hDnot_mem_bool
                    have hne : ∃ y, y ∈ D := by
                      refine ⟨a₀.pair b₀, ?_⟩
                      change a₀.pair b₀ ∈ ⟦αx.toSMTType⟧ᶻ.prod ⟦βx.toSMTType⟧ᶻ
                      rw [ZFSet.pair_mem_prod]
                      exact ⟨ha₀, hb₀⟩
                    obtain ⟨y, hyD, hyFalse⟩ :=
                      sInterSepEqZffalseImpliesExistsEqZffalse
                        (D := D) (F := bodyF) hbodyF_bool hne hsInter_false
                    rw [ZFSet.mem_prod] at hyD
                    rcases hyD with ⟨u, hu, v, hv, rfl⟩
                    let Wa : SMT.Dom := ⟨u, αx.toSMTType, hu⟩
                    let Wb : SMT.Dom := ⟨v, βx.toSMTType, hv⟩
                    let Δw : SMT.RenamingContext.Context :=
                      Function.update (Function.update (Function.update Δ'' p (some Wp)) a (some Wa)) b (some Wb)
                    have hy :
                      (u.pair v).hasArity [a, b].length ∧
                        ∀ i : Fin [a, b].length,
                          (u.pair v).get [a, b].length i ∈
                            ⟦[αx.toSMTType, βx.toSMTType][i]⟧ᶻ := by
                      simpa using pair_hasArity_get_mem hu hv
                    let w : Fin [a, b].length → SMT.Dom := fun i =>
                      ⟨(u.pair v).get [a, b].length i,
                        [αx.toSMTType, βx.toSMTType][i], hy.2 i⟩
                    have hw :
                      ∀ i : Fin [a, b].length,
                        (w i).snd.fst = [αx.toSMTType, βx.toSMTType][i] ∧
                          (w i).fst ∈ ⟦[αx.toSMTType, βx.toSMTType][i]⟧ᶻ := by
                      intro i
                      exact ⟨rfl, hy.2 i⟩
                    have hnot_isSome :
                      ⟦¬ˢ'
                          (SMT.Term.abstract.go body [a, b]
                            (Function.update Δ'' p (some Wp))
                            (hgo_cov_exists Wp rfl)).uncurry w⟧ˢ.isSome = true := by
                      simpa [w] using den_not_body_isSome Wp rfl hw
                    have hnot_get_false :
                      (⟦¬ˢ'
                          (SMT.Term.abstract.go body [a, b]
                            (Function.update Δ'' p (some Wp))
                            (hgo_cov_exists Wp rfl)).uncurry w⟧ˢ.get
                        hnot_isSome).fst = zffalse := by
                      have hbodyF_pair :
                          bodyF (u.pair v) =
                            (⟦¬ˢ'
                                (SMT.Term.abstract.go body [a, b]
                                  (Function.update Δ'' p (some Wp))
                                  (hgo_cov_exists Wp rfl)).uncurry w⟧ˢ.get
                              hnot_isSome).fst := by
                        unfold bodyF
                        split_ifs
                        · simp [w, ZFSet.get, proof_irrel_heq]
                      rw [hbodyF_pair] at hyFalse
                      exact hyFalse
                    obtain ⟨Dbody, hden_body_raw, hDbody_ty⟩ :=
                      den_body_some Wp rfl hw
                    have hDbody_true : Dbody.fst = zftrue := by
                      have hDbody_bool : Dbody.fst ∈ 𝔹 := by
                        simpa [hDbody_ty] using Dbody.snd.snd
                      rw [ZFSet.ZFBool.mem_𝔹_iff] at hDbody_bool
                      rcases hDbody_bool with hDbody_false | hDbody_true
                      · have hden_not_true :
                            ⟦¬ˢ'
                                (SMT.Term.abstract.go body [a, b]
                                  (Function.update Δ'' p (some Wp))
                                  (hgo_cov_exists Wp rfl)).uncurry w⟧ˢ =
                              some ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
                          exact denote_not_eq_zftrue_of_some_zffalse
                            hden_body_raw hDbody_ty hDbody_false
                        have hget_not_true :
                            (⟦¬ˢ'
                                (SMT.Term.abstract.go body [a, b]
                                  (Function.update Δ'' p (some Wp))
                                  (hgo_cov_exists Wp rfl)).uncurry w⟧ˢ.get
                              hnot_isSome) =
                              ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
                          apply Option.get_of_eq_some
                          exact hden_not_true
                        have : zftrue = zffalse := by
                          exact
                            (congrArg (fun D : SMT.Dom => D.fst) hget_not_true).symm.trans
                              hnot_get_false
                        exact False.elim (ZFSet.zftrue_ne_zffalse this)
                      · exact hDbody_true
                    have hgo :=
                      funAbstractGoPair
                        (Δctx := Function.update Δ'' p (some Wp))
                        (P := body) (v₁ := a) (v₂ := b)
                        (τ₁ := αx.toSMTType) (τ₂ := βx.toSMTType)
                        (hgo_cov_exists Wp rfl) (fun W₁ W₂ => hcov_body_upd Wp W₁ W₂)
                        w hw
                    have hw0 : w ⟨0, by simp⟩ = Wa := by
                      apply funDomEqOfTyEqAndFstEq
                      · rfl
                      · simp [w, Wa, ZFSet.get]
                    have hw1 : w ⟨1, by simp⟩ = Wb := by
                      apply funDomEqOfTyEqAndFstEq
                      · rfl
                      · simp [w, Wb, ZFSet.get]
                    have hden_body_true :
                      ⟦body.abstract Δw (hcov_body_upd Wp Wa Wb)⟧ˢ = some Dbody := by
                      have hden_body' := hden_body_raw
                      rw [hgo, hw0, hw1] at hden_body'
                      simpa [Δw, proof_irrel_heq] using hden_body'
                    have hcov_S_Wp :
                      RenamingContext.CoversFV
                        (Function.update (Function.update Δ'' p (some Wp)) b (some Wb))
                        S_enc := by
                      exact SMT.RenamingContext.coversFV_update_of_notMem
                        (x := b) (d := Wb) hb_not_fv_S_enc
                        (SMT.RenamingContext.coversFV_update_of_notMem
                          (x := p) (d := Wp) hp_not_fv_S_enc hΔ_S_final)
                    have den_S_Wp :
                      ∀ Xarg : SMT.Dom,
                        ⟦S_enc.abstract
                            (Function.update
                              (Function.update
                                (Function.update Δ'' p (some Wp))
                                b (some Wb))
                              a (some Xarg))
                            (SMT.RenamingContext.coversFV_update_of_notMem
                              (x := a) (d := Xarg) ha_not_fv_S_enc hcov_S_Wp)⟧ˢ =
                          some ⟨Senc, ⟨αx.set.toSMTType, hSenc⟩⟩ := by
                      intro Xarg
                      have hden_a_raw :
                          ⟦S_enc.abstract
                              (Function.update
                                (Function.update
                                  (Function.update Δ'' p (some Wp))
                                  b (some Wb))
                                a (some Xarg))
                              (SMT.RenamingContext.coversFV_update_of_notMem
                                (x := a) (d := Xarg) ha_not_fv_S_enc hcov_S_Wp)⟧ˢ =
                            ⟦S_enc.abstract
                                (Function.update
                                  (Function.update Δ'' p (some Wp))
                                  b (some Wb))
                                hcov_S_Wp⟧ˢ := by
                        simpa [SMT.RenamingContext.denote] using
                          (SMT.RenamingContext.denote_update_of_notMem
                            («Δ» := Function.update
                              (Function.update Δ'' p (some Wp))
                              b (some Wb))
                            (t := S_enc) (x := a) (d := Xarg)
                            (h := hcov_S_Wp) ha_not_fv_S_enc).symm
                      have hcov_S_p :
                          RenamingContext.CoversFV
                            (Function.update Δ'' p (some Wp))
                            S_enc := by
                        exact SMT.RenamingContext.coversFV_update_of_notMem
                          (x := p) (d := Wp) hp_not_fv_S_enc hΔ_S_final
                      have hden_b_raw :
                          ⟦S_enc.abstract
                              (Function.update
                                (Function.update Δ'' p (some Wp))
                                b (some Wb))
                              hcov_S_Wp⟧ˢ =
                            ⟦S_enc.abstract
                                (Function.update Δ'' p (some Wp))
                                hcov_S_p⟧ˢ := by
                        simpa [SMT.RenamingContext.denote] using
                          (SMT.RenamingContext.denote_update_of_notMem
                            («Δ» := Function.update Δ'' p (some Wp))
                            (t := S_enc) (x := b) (d := Wb)
                            (h := hcov_S_p) hb_not_fv_S_enc).symm
                      have hden_p_raw :
                          ⟦S_enc.abstract
                              (Function.update Δ'' p (some Wp))
                              hcov_S_p⟧ˢ =
                            ⟦S_enc.abstract Δ'' hΔ_S_final⟧ˢ := by
                        simpa [SMT.RenamingContext.denote] using
                          (SMT.RenamingContext.denote_update_of_notMem
                            («Δ» := Δ'') (t := S_enc) (x := p) (d := Wp)
                            (h := hΔ_S_final) hp_not_fv_S_enc).symm
                      rw [hden_a_raw, hden_b_raw, hden_p_raw]
                      exact den_S_enc_final
                    obtain ⟨hcov_Sa, DSa, hDSa_ty, hDSa_val, hden_Sa_calc⟩ :=
                      funDenoteAppAt
                        (Δctx := Function.update
                          (Function.update Δ'' p (some Wp))
                          b (some Wb))
                        (t := S_enc) (x := a)
                        (α := αx.toSMTType) (β := SMTType.bool)
                        (Y := ⟨Senc, ⟨αx.set.toSMTType, hSenc⟩⟩)
                        (hcov_t_upd := by
                          intro Xarg
                          exact SMT.RenamingContext.coversFV_update_of_notMem
                            (x := a) (d := Xarg) ha_not_fv_S_enc hcov_S_Wp)
                        (den_t_upd := by
                          intro Xarg
                          exact den_S_Wp Xarg)
                        (hY_ty := rfl)
                        (hY_func := hSenc_func)
                        (Xarg := Wa)
                        (hXarg_ty := rfl)
                        (hXarg_mem := hu)
                    have hu_mem : retract αx u ∈ ⟦αx⟧ᶻ := by
                      exact retract_mem_of_toSMTType hu
                    have hcanon_u :
                      ZFSet.fapply (BType.canonicalIsoSMTType αx).1
                          (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType αx).2.1)
                          ⟨retract αx u, by
                            rwa [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType αx).2.1]⟩ =
                        u := by
                      simpa using canonical_of_retract αx hu
                    have hcov_T_Wp :
                      RenamingContext.CoversFV
                        (Function.update (Function.update Δ'' p (some Wp)) a (some Wa))
                        T_enc := by
                      exact SMT.RenamingContext.coversFV_update_of_notMem
                        (x := a) (d := Wa) ha_not_fv_T_enc
                        (SMT.RenamingContext.coversFV_update_of_notMem
                          (x := p) (d := Wp) hp_not_fv_T_enc Δ''_covers_T)
                    have den_T_Wp :
                      ∀ Xarg : SMT.Dom,
                        ⟦T_enc.abstract
                            (Function.update
                              (Function.update
                                (Function.update Δ'' p (some Wp))
                                a (some Wa))
                              b (some Xarg))
                            (SMT.RenamingContext.coversFV_update_of_notMem
                              (x := b) (d := Xarg) hb_not_fv_T_enc hcov_T_Wp)⟧ˢ =
                          some ⟨Tenc, ⟨βx.set.toSMTType, hTenc⟩⟩ := by
                      intro Xarg
                      have hden_b_raw :
                          ⟦T_enc.abstract
                              (Function.update
                                (Function.update
                                  (Function.update Δ'' p (some Wp))
                                  a (some Wa))
                                b (some Xarg))
                              (SMT.RenamingContext.coversFV_update_of_notMem
                                (x := b) (d := Xarg) hb_not_fv_T_enc hcov_T_Wp)⟧ˢ =
                            ⟦T_enc.abstract
                                (Function.update
                                  (Function.update Δ'' p (some Wp))
                                  a (some Wa))
                                hcov_T_Wp⟧ˢ := by
                        simpa [SMT.RenamingContext.denote] using
                          (SMT.RenamingContext.denote_update_of_notMem
                            («Δ» := Function.update
                              (Function.update Δ'' p (some Wp))
                              a (some Wa))
                            (t := T_enc) (x := b) (d := Xarg)
                            (h := hcov_T_Wp) hb_not_fv_T_enc).symm
                      have hcov_T_p :
                          RenamingContext.CoversFV
                            (Function.update Δ'' p (some Wp))
                            T_enc := by
                        exact SMT.RenamingContext.coversFV_update_of_notMem
                          (x := p) (d := Wp) hp_not_fv_T_enc Δ''_covers_T
                      have hden_a_raw :
                          ⟦T_enc.abstract
                              (Function.update
                                (Function.update Δ'' p (some Wp))
                                a (some Wa))
                              hcov_T_Wp⟧ˢ =
                            ⟦T_enc.abstract
                                (Function.update Δ'' p (some Wp))
                                hcov_T_p⟧ˢ := by
                        simpa [SMT.RenamingContext.denote] using
                          (SMT.RenamingContext.denote_update_of_notMem
                            («Δ» := Function.update Δ'' p (some Wp))
                            (t := T_enc) (x := a) (d := Wa)
                            (h := hcov_T_p) ha_not_fv_T_enc).symm
                      have hden_p_raw :
                          ⟦T_enc.abstract
                              (Function.update Δ'' p (some Wp))
                              hcov_T_p⟧ˢ =
                            ⟦T_enc.abstract Δ'' Δ''_covers_T⟧ˢ := by
                        simpa [SMT.RenamingContext.denote] using
                          (SMT.RenamingContext.denote_update_of_notMem
                            («Δ» := Δ'') (t := T_enc) (x := p) (d := Wp)
                            (h := Δ''_covers_T) hp_not_fv_T_enc).symm
                      rw [hden_b_raw, hden_a_raw, hden_p_raw]
                      exact den_T_enc
                    obtain ⟨hcov_Tb, DTb, hDTb_ty, hDTb_val, hden_Tb_calc⟩ :=
                      funDenoteAppAt
                        (Δctx := Function.update
                          (Function.update Δ'' p (some Wp))
                          a (some Wa))
                        (t := T_enc) (x := b)
                        (α := βx.toSMTType) (β := SMTType.bool)
                        (Y := ⟨Tenc, ⟨βx.set.toSMTType, hTenc⟩⟩)
                        (hcov_t_upd := by
                          intro Xarg
                          exact SMT.RenamingContext.coversFV_update_of_notMem
                            (x := b) (d := Xarg) hb_not_fv_T_enc hcov_T_Wp)
                        (den_t_upd := by
                          intro Xarg
                          exact den_T_Wp Xarg)
                        (hY_ty := rfl)
                        (hY_func := hTenc_func)
                        (Xarg := Wb)
                        (hXarg_ty := rfl)
                        (hXarg_mem := hv)
                    have hv_mem : retract βx v ∈ ⟦βx⟧ᶻ := by
                      exact retract_mem_of_toSMTType hv
                    have hcanon_v :
                      ZFSet.fapply (BType.canonicalIsoSMTType βx).1
                          (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType βx).2.1)
                          ⟨retract βx v, by
                            rwa [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType βx).2.1]⟩ =
                        v := by
                      simpa using canonical_of_retract βx hv
                    have hcov_var_p :
                      RenamingContext.CoversFV Δw (SMT.Term.var p) := by
                      simpa [Δw] using
                        cprod_covers_var_p (Δctx := Δ'') (Wp := Wp) (Wa := Wa) (Wb := Wb)
                          (p := p) (a := a) (b := b) hp_ne_a hp_ne_b
                    have hden_var_p :
                      ⟦(SMT.Term.var p).abstract Δw hcov_var_p⟧ˢ = some Wp := by
                      simpa [Δw] using
                        cprod_denote_var_p (Δctx := Δ'') (Wp := Wp) (Wa := Wa) (Wb := Wb)
                          (p := p) (a := a) (b := b) hp_ne_a hp_ne_b
                    have hcov_var_a :
                      RenamingContext.CoversFV Δw (SMT.Term.var a) := by
                      simpa [Δw] using
                        cprod_covers_var_a (Δctx := Δ'') (Wp := Wp) (Wa := Wa) (Wb := Wb)
                          (p := p) (a := a) (b := b) ha_ne_b
                    have hden_var_a :
                      ⟦(SMT.Term.var a).abstract Δw hcov_var_a⟧ˢ = some Wa := by
                      simpa [Δw] using
                        cprod_denote_var_a (Δctx := Δ'') (Wp := Wp) (Wa := Wa) (Wb := Wb)
                          (p := p) (a := a) (b := b) ha_ne_b
                    have hcov_var_b :
                      RenamingContext.CoversFV Δw (SMT.Term.var b) := by
                      simpa [Δw] using
                        cprod_covers_var_b (Δctx := Δ'') (Wp := Wp) (Wa := Wa) (Wb := Wb)
                          (p := p) (a := a) (b := b)
                    have hden_var_b :
                      ⟦(SMT.Term.var b).abstract Δw hcov_var_b⟧ˢ = some Wb := by
                      simpa [Δw] using
                        cprod_denote_var_b (Δctx := Δ'') (Wp := Wp) (Wa := Wa) (Wb := Wb)
                          (p := p) (a := a) (b := b)
                    obtain ⟨Dpair, hden_pair_raw, hDpair_ty⟩ :=
                      denote_pair_some_of_some hden_var_a hden_var_b
                    have hpair_eq_raw := hden_pair_raw
                    rw [SMT.denote, hden_var_a, hden_var_b] at hpair_eq_raw
                    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some,
                      Option.some.injEq] at hpair_eq_raw
                    have hDpair_eq_uv : Dpair.fst = u.pair v := by
                      simpa [Wa, Wb] using
                        (congrArg (fun D : SMT.Dom => D.fst) hpair_eq_raw).symm
                    have hcov_Sa_Δw :
                      RenamingContext.CoversFV Δw ((@ˢS_enc) (SMT.Term.var a)) := by
                      simpa [body, Δw] using
                        cprod_body_covers_left
                          («Δ» := Δ'') (Wp := Wp) (Wa := Wa) (Wb := Wb)
                          (p := p) (a := a) (b := b) (S_enc := S_enc) (T_enc := T_enc)
                          (hcov_body_upd := hcov_body_upd Wp Wa Wb)
                    have hctx_Sa :
                      Function.update (Function.update (Function.update Δ'' p (some Wp))
                        b (some Wb)) a (some Wa) = Δw := by
                      simpa [Δw] using
                        cprod_update_eq (Δctx := Δ'') (Wp := Wp) (Wa := Wa) (Wb := Wb)
                          (p := p) (a := a) (b := b) hp_ne_a hp_ne_b ha_ne_b
                    have hden_Sa_true :
                      ⟦((@ˢS_enc) (SMT.Term.var a)).abstract Δw hcov_Sa_Δw⟧ˢ =
                        some DSa := by
                      simpa [hctx_Sa, proof_irrel_heq] using hden_Sa_calc
                    have hcov_eq :
                      RenamingContext.CoversFV Δw
                        (SMT.Term.var p =ˢ (SMT.Term.var a).pair (SMT.Term.var b)) := by
                      simpa [body, Δw] using
                        cprod_body_covers_eq
                          («Δ» := Δ'') (Wp := Wp) (Wa := Wa) (Wb := Wb)
                          (p := p) (a := a) (b := b) (S_enc := S_enc) (T_enc := T_enc)
                          (hcov_body_upd := hcov_body_upd Wp Wa Wb)
                    have hcov_right :
                      RenamingContext.CoversFV Δw
                        ((@ˢT_enc) (SMT.Term.var b) ∧ˢ
                          (SMT.Term.var p =ˢ (SMT.Term.var a).pair (SMT.Term.var b))) := by
                      simpa [body, Δw] using
                        cprod_body_covers_right
                          («Δ» := Δ'') (Wp := Wp) (Wa := Wa) (Wb := Wb)
                          (p := p) (a := a) (b := b) (S_enc := S_enc) (T_enc := T_enc)
                          (hcov_body_upd := hcov_body_upd Wp Wa Wb)
                    obtain ⟨_, typ_Sa_term, typ_right_term⟩ := SMT.Typing.andE typ_body
                    obtain ⟨_, typ_Tb_term, typ_eq_term⟩ := SMT.Typing.andE typ_right_term
                    have hcov_Tb_Δw :
                      RenamingContext.CoversFV Δw ((@ˢT_enc) (SMT.Term.var b)) := by
                      simpa [Δw] using hcov_Tb
                    have hden_body_split :
                        ⟦(((@ˢS_enc) (SMT.Term.var a)).abstract Δw hcov_Sa_Δw) ∧ˢ'
                            ((((@ˢT_enc) (SMT.Term.var b)) ∧ˢ
                              (SMT.Term.var p =ˢ (SMT.Term.var a).pair (SMT.Term.var b))).abstract
                              Δw hcov_right)⟧ˢ =
                          some Dbody := by
                      simpa [body, SMT.Term.abstract, proof_irrel_heq] using hden_body_true
                    obtain ⟨DSa', Dright, hden_Sa_from_body, hDSa'_true, hden_right, hDright_true⟩ :=
                      denoteAndTrueComponents
                        (p := ((@ˢS_enc) (SMT.Term.var a)).abstract Δw hcov_Sa_Δw)
                        (q := ((((@ˢT_enc) (SMT.Term.var b)) ∧ˢ
                          (SMT.Term.var p =ˢ (SMT.Term.var a).pair (SMT.Term.var b))).abstract
                            Δw hcov_right))
                        (typ_p_bool := by
                          intro Dp hDp
                          exact denote_type_eq_of_typing (typ_t := typ_Sa_term) (hden := hDp))
                        (typ_q_bool := by
                          intro Dq hDq
                          exact denote_type_eq_of_typing (typ_t := typ_right_term) (hden := hDq))
                        hden_body_split hDbody_true
                    have hden_right_split :
                        ⟦(((@ˢT_enc) (SMT.Term.var b)).abstract Δw hcov_Tb_Δw) ∧ˢ'
                            (((SMT.Term.var p) =ˢ (SMT.Term.var a).pair (SMT.Term.var b)).abstract
                              Δw hcov_eq)⟧ˢ =
                          some Dright := by
                      simpa [SMT.Term.abstract, proof_irrel_heq] using hden_right
                    obtain ⟨DTb', Deq, hden_Tb_from_body, hDTb'_true, hden_eq, hDeq_true⟩ :=
                      denoteAndTrueComponents
                        (p := ((@ˢT_enc) (SMT.Term.var b)).abstract Δw hcov_Tb_Δw)
                        (q := (((SMT.Term.var p) =ˢ (SMT.Term.var a).pair (SMT.Term.var b)).abstract
                          Δw hcov_eq))
                        (typ_p_bool := by
                          intro Dp hDp
                          exact denote_type_eq_of_typing (typ_t := typ_Tb_term) (hden := hDp))
                        (typ_q_bool := by
                          intro Dq hDq
                          exact denote_type_eq_of_typing (typ_t := typ_eq_term) (hden := hDq))
                        hden_right_split hDright_true
                    have hDSa_eq : DSa = DSa' := by
                      exact Option.some.inj (hden_Sa_true.symm.trans hden_Sa_from_body)
                    have hDTb_eq : DTb = DTb' := by
                      exact Option.some.inj (hden_Tb_calc.symm.trans hden_Tb_from_body)
                    have hDSa_true : DSa.fst = zftrue := by
                      simpa [hDSa_eq] using hDSa'_true
                    have hDTb_true : DTb.fst = zftrue := by
                      simpa [hDTb_eq] using hDTb'_true
                    have huX : retract αx u ∈ X := by
                      apply
                        (mem_retract_set_iff_app_canonical_eq_zftrue
                          (α := αx) hSenc_func retract_Senc_eq_X hu_mem).mpr
                      simpa [proof_irrel_heq, hcanon_u, hDSa_val] using hDSa_true
                    have hvY : retract βx v ∈ Y := by
                      apply
                        (mem_retract_set_iff_app_canonical_eq_zftrue
                          (α := βx) hTenc_func retract_Tenc_eq_Y hv_mem).mpr
                      simpa [proof_irrel_heq, hcanon_v, hDTb_val] using hDTb_true
                    have hWp_Dpair_ty : Wp.snd.fst = Dpair.snd.fst := by
                      simpa [Wp, pairTy, Wa, Wb] using hDpair_ty.symm
                    have hden_eq_split :
                        ⟦(SMT.Term.var p).abstract Δw hcov_var_p =ˢ'
                            ((SMT.Term.var a).abstract Δw hcov_var_a).pair
                              ((SMT.Term.var b).abstract Δw hcov_var_b)⟧ˢ =
                          some Deq := by
                      simpa [SMT.Term.abstract, proof_irrel_heq] using hden_eq
                    have hWp_eq_Dpair_fst : Wp.fst = Dpair.fst := by
                      exact
                        denote_eq_true_implies_fst_eq hden_var_p hden_pair_raw
                          hWp_Dpair_ty hden_eq_split hDeq_true
                    have hpair_eq : a₀.pair b₀ = u.pair v := by
                      calc
                        a₀.pair b₀ = Wp.fst := rfl
                        _ = Dpair.fst := hWp_eq_Dpair_fst
                        _ = u.pair v := hDpair_eq_uv
                    simpa [retract, ZFSet.pair_mem_prod, hpair_eq] using And.intro huX hvY
                  ext z
                  constructor
                  · intro hz
                    have hz_dom : z ∈ ⟦αx ×ᴮ βx⟧ᶻ := by
                      unfold retract at hz
                      exact (ZFSet.mem_sep.mp hz).1
                    have happ_true :
                        ZFSet.fapply tcprodVal (ZFSet.is_func_is_pfunc ha_func)
                            ⟨ZFSet.fapply (BType.canonicalIsoSMTType (αx ×ᴮ βx)).1
                                (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType (αx ×ᴮ βx)).2.1)
                                ⟨z, by
                                  rwa [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType (αx ×ᴮ βx)).2.1]⟩,
                              by
                                rw [ZFSet.is_func_dom_eq ha_func]
                                exact fapply_mem_range _ _⟩ = zftrue := by
                      exact
                        (mem_retract_set_iff_app_canonical_eq_zftrue
                          (α := αx ×ᴮ βx) (F := tcprodVal)
                          (X := retract (BType.set (αx ×ᴮ βx)) tcprodVal)
                          ha_func rfl hz_dom).mp hz
                    let zCan : ZFSet :=
                      ZFSet.fapply (BType.canonicalIsoSMTType (αx ×ᴮ βx)).1
                        (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType (αx ×ᴮ βx)).2.1)
                        ⟨z, by
                          rwa [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType (αx ×ᴮ βx)).2.1]⟩
                    have hzCan_mem : zCan ∈ ⟦pairTy⟧ᶻ := by
                      simpa [zCan, pairTy] using fapply_mem_range
                        (BType.canonicalIsoSMTType (αx ×ᴮ βx)).1
                        (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType (αx ×ᴮ βx)).2.1)
                    have hzCan_true : bodyFun zCan = zftrue := by
                      have hzCan_app :
                          ZFSet.fapply tcprodVal (ZFSet.is_func_is_pfunc ha_func)
                              ⟨zCan, by
                                rw [ZFSet.is_func_dom_eq ha_func]
                                exact hzCan_mem⟩ = zftrue := by
                        simpa [zCan] using happ_true
                      rw [← happ_a_eq_bodyFun hzCan_mem]
                      exact hzCan_app
                    have hz_eq : retract (αx ×ᴮ βx) zCan = z := by
                      simpa [zCan] using
                        (retract_of_canonical (τ := αx ×ᴮ βx) hz_dom rfl)
                    rw [← hz_eq]
                    exact hprod_of_body_true hzCan_mem hzCan_true
                  · intro hz
                    have hz_dom : z ∈ ⟦αx ×ᴮ βx⟧ᶻ := by
                      rw [BType.toZFSet, ZFSet.mem_powerset] at hT
                      exact hT hz
                    let zCan : ZFSet :=
                      ZFSet.fapply (BType.canonicalIsoSMTType (αx ×ᴮ βx)).1
                        (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType (αx ×ᴮ βx)).2.1)
                        ⟨z, by
                          rwa [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType (αx ×ᴮ βx)).2.1]⟩
                    have hzCan_mem : zCan ∈ ⟦pairTy⟧ᶻ := by
                      simpa [zCan, pairTy] using fapply_mem_range
                        (BType.canonicalIsoSMTType (αx ×ᴮ βx)).1
                        (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType (αx ×ᴮ βx)).2.1)
                    have hzCan_prod : retract (αx ×ᴮ βx) zCan ∈ X.prod Y := by
                      have hz_eq : retract (αx ×ᴮ βx) zCan = z := by
                        simpa [zCan] using
                          (retract_of_canonical (τ := αx ×ᴮ βx) hz_dom rfl)
                      rw [hz_eq]
                      exact hz
                    have hzCan_true : bodyFun zCan = zftrue :=
                      hbody_true_of_prod hzCan_mem hzCan_prod
                    apply
                      (mem_retract_set_iff_app_canonical_eq_zftrue
                        (α := αx ×ᴮ βx) (F := tcprodVal)
                        (X := retract (BType.set (αx ×ᴮ βx)) tcprodVal)
                        ha_func rfl hz_dom).mpr
                    simpa [zCan] using (happ_a_eq_bodyFun hzCan_mem).trans hzCan_true
  rcases hmain with ⟨denT', hdenT', hEq⟩
  refine ⟨denT', ?_, hEq⟩
  simpa [body, tcprod] using hdenT'

set_option maxHeartbeats 4000000 in
theorem encodeTerm_spec.cprod_case.{u} (fv_sub_typings : B.FvSubTypings) (S T_1 : B.Term)
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
  (T_ih :
    ∀ (E : B.Env) {Λ : SMT.TypeContext} {α : BType},
      E.context ⊢ᴮ T_1 : α →
        ∀ {«Δ» : B.RenamingContext.Context} (Δ_fv : ∀ v ∈ B.fv T_1, («Δ» v).isSome = true)
          {Δ₀ : SMT.RenamingContext.Context},
          RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» T_1 →
            ∀ {used : List SMT.𝒱},
              (∀ v ∉ used, Δ₀ v = none) →
                ∀ {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ},
                  ⟦T_1.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩ →
                    (∀ v ∈ T_1.vars, v ∈ used) →
                      (∀ v ∈ T_1.vars, v ∈ Λ → v ∈ E.context) →
                        ∀ {n : ℕ},
                          ⦃fun x =>
                            match x with
                            | { env := E0, types := Λ' } =>
                              ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
                            encodeTerm T_1 E ⦃PostCond.mayThrow fun x x_1 =>
                              match x with
                              | (t', σ) =>
                                match x_1 with
                                | { env := E', types := Γ' } =>
                                  ⌜used ⊆ E'.usedVars ∧
                                      Λ ⊆ Γ' ∧
                                        AList.keys Γ' ⊆ E'.usedVars ∧
                                          CoversUsedVars E'.usedVars T_1 ∧
                                            σ = α.toSMTType ∧
                                              Γ' ⊢ˢ t' : σ ∧
                                                (∀ v ∈ used, v ∉ Λ → v ∉ B.fv T_1 → v ∉ Γ') ∧
                                                  ∃ Δ',
                                                    ∃ (Δ'_covers : RenamingContext.CoversFV Δ' t'),
                                                      RenamingContext.Extends Δ' Δ₀ ∧
                                                        RenamingContext.ExtendsOnSourceFV Δ' «Δ» T_1 ∧
                                                          (∀ v ∉ E'.usedVars, Δ' v = none) ∧
                                                            ∃ denT',
                                                              ⟦t'.abstract Δ' Δ'_covers⟧ˢ = some denT' ∧
                                                                ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT' ∧
                                                                  ∀ (Δ_alt : B.RenamingContext.Context)
                                                                    (Δ_fv_alt : ∀ v ∈ B.fv T_1, (Δ_alt v).isSome = true)
                                                                    (Δ₀_alt : SMT.RenamingContext.Context),
                                                                    RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt T_1 →
                                                                      (∀ v ∉ E'.usedVars, Δ₀_alt v = none) →
                                                                      (∀ v (d : SMT.Dom), Δ₀_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) →
                                                                        ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦α⟧ᶻ),
                                                                          ⟦T_1.abstract Δ_alt Δ_fv_alt⟧ᴮ =
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
  (E : B.Env) {Λ : SMT.TypeContext} {α : BType} (typ_t : E.context ⊢ᴮ S ⨯ᴮ T_1 : α) {«Δ» : B.RenamingContext.Context}
  (Δ_fv : ∀ v ∈ B.fv (S ⨯ᴮ T_1), («Δ» v).isSome = true) {Δ₀ : SMT.RenamingContext.Context}
  (Δ₀_ext : RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» (S ⨯ᴮ T_1)) {used : List SMT.𝒱}
  (Δ₀_none_out : ∀ v ∉ used, Δ₀ v = none) {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ}
  (den_t : ⟦(S ⨯ᴮ T_1).abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩) (vars_used : ∀ v ∈ (S ⨯ᴮ T_1).vars, v ∈ used)
  (Λ_inv : ∀ v ∈ (S ⨯ᴮ T_1).vars, v ∈ Λ → v ∈ E.context) {n : ℕ} :
  ⦃fun x =>
    match x with
    | { env := E0, types := Λ' } => ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
    encodeTerm (S ⨯ᴮ T_1) E ⦃PostCond.mayThrow fun x x_1 =>
      match x with
      | (t', σ) =>
        match x_1 with
        | { env := E', types := Γ' } =>
          ⌜used ⊆ E'.usedVars ∧
              Λ ⊆ Γ' ∧
                AList.keys Γ' ⊆ E'.usedVars ∧
                  CoversUsedVars E'.usedVars (S ⨯ᴮ T_1) ∧
                    σ = α.toSMTType ∧
                      Γ' ⊢ˢ t' : σ ∧
                        (∀ v ∈ used, v ∉ Λ → v ∉ B.fv (S ⨯ᴮ T_1) → v ∉ Γ') ∧
                          ∃ Δ',
                            ∃ (Δ'_covers : RenamingContext.CoversFV Δ' t'),
                              RenamingContext.Extends Δ' Δ₀ ∧
                                RenamingContext.ExtendsOnSourceFV Δ' «Δ» (S ⨯ᴮ T_1) ∧
                                  (∀ v ∉ E'.usedVars, Δ' v = none) ∧
                                    ∃ denT',
                                      ⟦t'.abstract Δ' Δ'_covers⟧ˢ = some denT' ∧
                                        ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT' ∧
                                          ∀ (Δ_alt : B.RenamingContext.Context)
                                            (Δ_fv_alt : ∀ v ∈ B.fv (S ⨯ᴮ T_1), (Δ_alt v).isSome = true)
                                            (Δ₀_alt : SMT.RenamingContext.Context),
                                            RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt (S ⨯ᴮ T_1) →
                                              (∀ v ∉ E'.usedVars, Δ₀_alt v = none) →
                                              (∀ v (d : SMT.Dom), Δ₀_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) →
                                                ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦α⟧ᶻ),
                                                  ⟦(S ⨯ᴮ T_1).abstract Δ_alt Δ_fv_alt⟧ᴮ = some ⟨T_alt, ⟨α, hT_alt⟩⟩ →
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

  obtain ⟨αx, βx, rfl, typ_S, typ_T⟩ := B.Typing.cprodE typ_t

  have Δ_fv_S : ∀ v ∈ B.fv S, («Δ» v).isSome = true := by
    intro v hv
    exact Δ_fv v (by rw [B.fv, List.mem_append]; exact Or.inl hv)
  have Δ_fv_T : ∀ v ∈ B.fv T_1, («Δ» v).isSome = true := by
    intro v hv
    exact Δ_fv v (by rw [B.fv, List.mem_append]; exact Or.inr hv)

  rw [B.Term.abstract, B.denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at den_t
  obtain ⟨⟨X, τX, hX⟩, den_S, eq⟩ := den_t
  have hτX := denote_welltyped_eq
    (t := S.abstract («Δ» := «Δ») Δ_fv_S)
    ?_ den_S
  on_goal 2 =>
    use E.context.abstract («Δ» := «Δ»), WFTC.of_abstract, .set αx
    exact @Typing.of_abstract (B.Dom) («Δ» := «Δ») ?_ S E.context (.set αx) Δ_fv_S typ_S
  dsimp at hτX
  subst τX

  dsimp at eq
  rw [Option.bind_eq_some_iff] at eq
  obtain ⟨⟨Y, τY, hY⟩, den_T, eq⟩ := eq
  have hτY := denote_welltyped_eq
    (t := T_1.abstract («Δ» := «Δ») Δ_fv_T)
    ?_ den_T
  on_goal 2 =>
    use E.context.abstract («Δ» := «Δ»), WFTC.of_abstract, .set βx
    exact @Typing.of_abstract (B.Dom) («Δ» := «Δ») ?_ T_1 E.context (.set βx) Δ_fv_T typ_T
  dsimp at hτY
  subst τY

  rw [Option.some_inj] at eq
  injection eq with T_eq
  subst T

  have Δ₀_ext_S : RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» S := by
    exact RenamingContext.extendsOnSourceFV_of_fv_subset
      (hsub := by
        intro v hv
        simpa [B.fv] using (Or.inl hv : v ∈ B.fv S ∨ v ∈ B.fv T_1)) Δ₀_ext
  have Δ₀_ext_T : RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» T_1 := by
    exact RenamingContext.extendsOnSourceFV_of_fv_subset
      (hsub := by
        intro v hv
        simpa [B.fv] using (Or.inr hv : v ∈ B.fv S ∨ v ∈ B.fv T_1)) Δ₀_ext

  mspec S_ih (E := E) (Λ := St.types) (α := .set αx) typ_S
    («Δ» := «Δ») Δ_fv_S
    (Δ₀ := Δ₀) Δ₀_ext_S (used := used) Δ₀_none_out (T := X) (hT := hX)
    den_S (fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h))
    (fun v hv => Λ_inv v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h))
    (n := St.env.freshvarsc)
  clear S_ih
  rename_i out_S
  obtain ⟨S_enc, StS⟩ := out_S
  mrename_i pre
  mintro ∀StS
  mpure pre
  dsimp at pre
  obtain ⟨St_used_sub_StS, St_eq_StS, StS_sub, S_cov_StS, rfl, typ_S_enc, S_preserves,
    Δ', Δ'_covers_S, Δ'_extends_Δ₀, Δ'_ext_S, Δ'_none_out,
    ⟨Senc, _, hSenc⟩, den_S_enc, ⟨rfl, retract_Senc_eq_X⟩, S_ih_total⟩ := pre

  have Δ'_ext_T : RenamingContext.ExtendsOnSourceFV Δ' «Δ» T_1 := by
    exact RenamingContext.extendsOnSourceFV_of_extends Δ'_extends_Δ₀ Δ₀_ext_T

  rw [BType.toSMTType]
  mspec T_ih (E := E) (Λ := StS.types) (α := .set βx) typ_T
    («Δ» := «Δ») Δ_fv_T
    (Δ₀ := Δ') Δ'_ext_T (used := StS.env.usedVars) Δ'_none_out (T := Y) (hT := hY)
    den_T (fun v hv => St_used_sub_StS (vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inr h)))
    (fun v hv hΛ => by
      have hv_cprod : v ∈ (S ⨯ᴮ T_1).vars := by
        simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
        rcases hv with h | h <;> [left; right] <;> exact .inr h
      by_cases hv_St : v ∈ St.types
      · exact Λ_inv v hv_cprod hv_St
      · have hv_fv_S : v ∈ B.fv S := by
          by_contra h_neg
          exact absurd hΛ (S_preserves v (vars_used v hv_cprod) hv_St h_neg)
        exact _root_.B.Typing.typed_by_fv typ_S hv_fv_S)
    (n := StS.env.freshvarsc)
  clear T_ih
  rename_i out_T
  obtain ⟨T_enc, StT⟩ := out_T
  mrename_i pre
  mintro ∀StT
  mpure pre
  dsimp at pre
  obtain ⟨StS_used_sub_StT, StS_eq_StT, StT_sub, T_cov_StT, rfl, typ_T_enc, T_preserves,
    Δ'', Δ''_covers_T, Δ''_extends_Δ', Δ''_ext_T, Δ''_none_out,
    ⟨Tenc, _, hTenc⟩, den_T_enc, ⟨rfl, retract_Tenc_eq_Y⟩, T_ih_total⟩ := pre

  have typ_S_enc_T : StT.types ⊢ˢ S_enc : αx.set.toSMTType :=
    Typing.weakening StS_eq_StT typ_S_enc
  have hΔ_S_final : RenamingContext.CoversFV Δ'' S_enc := by
    exact RenamingContext.coversFV_of_extends_of_coversFV Δ''_extends_Δ' Δ'_covers_S
  have den_S_enc_final : ⟦S_enc.abstract Δ'' hΔ_S_final⟧ˢ = some ⟨Senc, ⟨αx.set.toSMTType, hSenc⟩⟩ := by
    have hag_S : RenamingContext.AgreesOnFV Δ'' Δ' S_enc := by
      exact RenamingContext.agreesOnFV_of_extends_of_coversFV Δ''_extends_Δ' Δ'_covers_S
    have hden_S_congr := RenamingContext.denote_congr_of_agreesOnFV
      (t := S_enc) (h1 := hΔ_S_final) (h2 := Δ'_covers_S) hag_S
    simpa [RenamingContext.denote] using hden_S_congr.trans den_S_enc

  rw [BType.toSMTType]
  set ctx := StT.types
  mspec freshVar_spec
    (Γ := ctx)
    (τ := αx.toSMTType.pair βx.toSMTType)
    (n := StT.env.freshvarsc)
    (used := StT.env.usedVars)
  case post.success p =>
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨St₁_types_eq, p_fresh, St₁_fvc_eq, St₁_used_eq, p_not_used⟩ := pre

    mspec freshVar_spec
      (Γ := ctx.insert p (αx.toSMTType.pair βx.toSMTType))
      (τ := αx.toSMTType)
      (n := St₁.env.freshvarsc)
      (used := St₁.env.usedVars)
    case post.success a =>
      mrename_i pre
      mintro ∀St₂
      mpure pre
      obtain ⟨St₂_types_eq, a_fresh, St₂_fvc_eq, St₂_used_eq, a_not_used⟩ := pre

      mspec freshVar_spec
        (Γ := (ctx.insert p (αx.toSMTType.pair βx.toSMTType)).insert a αx.toSMTType)
        (τ := βx.toSMTType)
        (n := St₂.env.freshvarsc)
        (used := St₂.env.usedVars)
      case post.success b =>
        mrename_i pre
        mintro ∀St₃
        mpure pre
        obtain ⟨St₃_types_eq, b_fresh, St₃_fvc_eq, St₃_used_eq, b_not_used⟩ := pre

        let body : SMT.Term :=
          ((@ˢS_enc) (SMT.Term.var a)) ∧ˢ
            (((@ˢT_enc) (SMT.Term.var b)) ∧ˢ
              ((SMT.Term.var p) =ˢ (SMT.Term.pair (SMT.Term.var a) (SMT.Term.var b))))
        let tcprod : SMT.Term :=
          (λˢ [p]) [αx.toSMTType.pair βx.toSMTType]
            (.exists [a, b] [αx.toSMTType, βx.toSMTType] body)

        mspec Std.Do.Spec.pure
        mpure_intro
        and_intros
        · intro v hv
          rw [St₃_used_eq, St₂_used_eq, St₁_used_eq]
          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (StS_used_sub_StT (St_used_sub_StS hv))))
        · intro v hv
          have hctx_sub_p :
              ctx ⊆ ctx.insert p (αx.toSMTType.pair βx.toSMTType) :=
            SMT.TypeContext.entries_subset_insert_of_notMem p_fresh
          have hctxp_sub_pa :
              ctx.insert p (αx.toSMTType.pair βx.toSMTType) ⊆
                (ctx.insert p (αx.toSMTType.pair βx.toSMTType)).insert a αx.toSMTType :=
            SMT.TypeContext.entries_subset_insert_of_notMem a_fresh
          have hctxpa_sub_pab :
              (ctx.insert p (αx.toSMTType.pair βx.toSMTType)).insert a αx.toSMTType ⊆
                ((ctx.insert p (αx.toSMTType.pair βx.toSMTType)).insert a αx.toSMTType).insert b βx.toSMTType :=
            SMT.TypeContext.entries_subset_insert_of_notMem b_fresh
          rw [St₃_types_eq]
          apply SMT.TypeContext.entries_subset_insert_of_notMem b_fresh
          apply SMT.TypeContext.entries_subset_insert_of_notMem a_fresh
          apply SMT.TypeContext.entries_subset_insert_of_notMem p_fresh
          exact StS_eq_StT (St_eq_StS hv)
        · intro v hv
          rw [St₃_used_eq, St₂_used_eq, St₁_used_eq]
          have hv' : v ∈ St₃.types := (AList.mem_keys).mpr hv
          rw [St₃_types_eq] at hv'
          iterate 3 rw [AList.mem_insert] at hv'
          rcases hv' with rfl | rfl | rfl | hv'
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (List.mem_cons_self)
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (StT_sub ((AList.mem_keys).mp hv'))))
        · intro v hv
          rw [B.fv, List.mem_append] at hv
          rw [St₃_used_eq, St₂_used_eq, St₁_used_eq]
          rcases hv with hv | hv
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (StS_used_sub_StT (S_cov_StS v hv))))
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (T_cov_StT v hv)))
        · rfl
        · have hp_ne_a : p ≠ a := by
            intro h
            subst h
            exact a_fresh (by rw [AList.mem_insert]; exact Or.inl rfl)
          have ha_ne_p : a ≠ p := hp_ne_a.symm
          have hb_ne_p : b ≠ p := by
            intro h
            subst h
            exact b_fresh (by
              rw [AList.mem_insert, AList.mem_insert]
              exact Or.inr (Or.inl rfl))
          have hp_ne_b : p ≠ b := hb_ne_p.symm
          have hb_ne_a : b ≠ a := by
            intro h
            subst h
            exact b_fresh (by
              rw [AList.mem_insert]
              exact Or.inl rfl)
          have ha_ne_b : a ≠ b := hb_ne_a.symm
          have hp_not_ctxa :
              p ∉ (ctx.insert a αx.toSMTType) := by
            intro hp_in
            rw [AList.mem_insert] at hp_in
            rcases hp_in with hp_eq | hp_ctx
            · exact hp_ne_a hp_eq
            · exact p_fresh hp_ctx
          have hp_not_ctxab :
              p ∉ ((ctx.insert a αx.toSMTType).insert b βx.toSMTType) := by
            intro hp_in
            rw [AList.mem_insert] at hp_in
            rcases hp_in with hp_eq | hp_ctxa
            · exact hp_ne_b hp_eq
            · exact hp_not_ctxa hp_ctxa
          have ha_not_ctx :
              a ∉ ctx := by
            intro ha_in
            exact a_fresh (by rw [AList.mem_insert]; exact Or.inr ha_in)
          have ha_not_ctxp :
              a ∉ ctx.insert p (αx.toSMTType.pair βx.toSMTType) := by
            exact a_fresh
          have hb_not_ctx :
              b ∉ ctx := by
            intro hb_in
            exact b_fresh (by
              rw [AList.mem_insert, AList.mem_insert]
              exact Or.inr (Or.inr hb_in))
          have hb_not_ctxp :
              b ∉ ctx.insert p (αx.toSMTType.pair βx.toSMTType) := by
            intro hb_in
            exact b_fresh (by rw [AList.mem_insert]; exact Or.inr hb_in)
          have hb_not_ctxpa :
              b ∉ (ctx.insert p (αx.toSMTType.pair βx.toSMTType)).insert a αx.toSMTType := by
            exact b_fresh
          have typ_S_enc_p :
              ctx.insert p (αx.toSMTType.pair βx.toSMTType) ⊢ˢ S_enc : αx.set.toSMTType :=
            Typing.weakening
              (h := SMT.TypeContext.entries_subset_insert_of_notMem p_fresh)
              typ_S_enc_T
          have typ_T_enc_p :
              ctx.insert p (αx.toSMTType.pair βx.toSMTType) ⊢ˢ T_enc : βx.set.toSMTType :=
            Typing.weakening
              (h := SMT.TypeContext.entries_subset_insert_of_notMem p_fresh)
              typ_T_enc
          have typ_S_enc_pab :
              ((ctx.insert p (αx.toSMTType.pair βx.toSMTType)).insert a αx.toSMTType).insert b βx.toSMTType ⊢ˢ
                S_enc : αx.set.toSMTType :=
            Typing.weakening
              (h := SMT.TypeContext.entries_subset_insert_of_notMem b_fresh)
              (Typing.weakening
                (h := SMT.TypeContext.entries_subset_insert_of_notMem a_fresh)
                typ_S_enc_p)
          have typ_T_enc_pab :
              ((ctx.insert p (αx.toSMTType.pair βx.toSMTType)).insert a αx.toSMTType).insert b βx.toSMTType ⊢ˢ
                T_enc : βx.set.toSMTType :=
            Typing.weakening
              (h := SMT.TypeContext.entries_subset_insert_of_notMem b_fresh)
              (Typing.weakening
                (h := SMT.TypeContext.entries_subset_insert_of_notMem a_fresh)
                typ_T_enc_p)
          have typ_body :
              ((ctx.insert p (αx.toSMTType.pair βx.toSMTType)).insert a αx.toSMTType).insert b βx.toSMTType ⊢ˢ
                body : .bool := by
            dsimp [body]
            apply SMT.Typing.and
            · apply SMT.Typing.app
              · exact typ_S_enc_pab
              · apply SMT.Typing.var
                rw [AList.lookup_insert_ne ha_ne_b, AList.lookup_insert]
            · apply SMT.Typing.and
              · apply SMT.Typing.app
                · exact typ_T_enc_pab
                · apply SMT.Typing.var
                  rw [AList.lookup_insert]
              · apply SMT.Typing.eq
                · apply SMT.Typing.var
                  rw [AList.lookup_insert_ne hp_ne_b]
                  rw [AList.lookup_insert_ne hp_ne_a]
                  rw [AList.lookup_insert]
                · apply SMT.Typing.pair
                  · apply SMT.Typing.var
                    rw [AList.lookup_insert_ne ha_ne_b]
                    rw [AList.lookup_insert]
                  · apply SMT.Typing.var
                    rw [AList.lookup_insert]
          have typ_exists :
              ctx.insert p (αx.toSMTType.pair βx.toSMTType) ⊢ˢ
                .exists [a, b] [αx.toSMTType, βx.toSMTType] body : .bool := by
            have ha_in_body_ctx :
                a ∈ ((ctx.insert p (αx.toSMTType.pair βx.toSMTType)).insert a αx.toSMTType).insert b βx.toSMTType := by
              rw [AList.mem_insert, AList.mem_insert]
              exact Or.inr (Or.inl rfl)
            have hb_in_body_ctx :
                b ∈ ((ctx.insert p (αx.toSMTType.pair βx.toSMTType)).insert a αx.toSMTType).insert b βx.toSMTType := by
              rw [AList.mem_insert]
              exact Or.inl rfl
            have fresh_body :
                ∀ v ∈ [a, b], v ∉ SMT.bv body := by
              intro v hv
              rw [List.mem_cons] at hv
              rcases hv with rfl | hv
              · intro hbv
                exact (SMT.Typing.bv_notMem_context typ_body _ hbv) ha_in_body_ctx
              · rw [List.mem_singleton] at hv
                subst hv
                intro hbv
                exact (SMT.Typing.bv_notMem_context typ_body _ hbv) hb_in_body_ctx
            have len_eq_ab : [a, b].length = [αx.toSMTType, βx.toSMTType].length := by
              simp
            apply SMT.Typing.exists
              (Γ := ctx.insert p (αx.toSMTType.pair βx.toSMTType))
              (vs := [a, b]) (τs := [αx.toSMTType, βx.toSMTType]) (len_eq := len_eq_ab)
            · intro v hv
              rw [List.mem_cons, List.mem_singleton] at hv
              rcases hv with rfl | rfl
              · exact ha_not_ctxp
              · exact hb_not_ctxp
            · exact fresh_body
            · simp
            · have hupdate_ab :
                  SMT.TypeContext.update
                    (ctx.insert p (αx.toSMTType.pair βx.toSMTType))
                    [a, b] [αx.toSMTType, βx.toSMTType] len_eq_ab =
                    ((ctx.insert p (αx.toSMTType.pair βx.toSMTType)).insert a αx.toSMTType).insert b βx.toSMTType := by
                unfold SMT.TypeContext.update
                simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
                  Fin.cast_eq_self, Fin.getElem_fin]
                rw [Fin.foldl_succ_last, Fin.foldl_succ_last]
                simp only [Fin.reduceLast, Fin.coe_ofNat_eq_mod, Nat.mod_succ,
                  List.getElem_cons_succ, List.getElem_cons_zero, Fin.last_zero, Fin.isValue,
                  Fin.castSucc_zero, Nat.zero_mod, Fin.coe_castSucc, Fin.val_eq_zero,
                  Fin.foldl_zero]
              rw [hupdate_ab]
              exact typ_body
          have typ_tcprod_ctx :
              ctx ⊢ˢ tcprod : (BType.set (αx ×ᴮ βx)).toSMTType := by
            dsimp [tcprod]
            have hp_in_exists_ctx :
                p ∈ ctx.insert p (αx.toSMTType.pair βx.toSMTType) := by
              rw [AList.mem_insert]
              exact Or.inl rfl
            have fresh_exists :
                ∀ v ∈ [p], v ∉ SMT.bv (.exists [a, b] [αx.toSMTType, βx.toSMTType] body) := by
              intro v hv
              rw [List.mem_singleton] at hv
              subst hv
              intro hbv
              exact (SMT.Typing.bv_notMem_context typ_exists _ hbv) hp_in_exists_ctx
            have len_eq_p : [p].length = [αx.toSMTType.pair βx.toSMTType].length := by
              simp
            apply SMT.Typing.lambda
              (Γ := ctx)
              (vs := [p]) (τs := [αx.toSMTType.pair βx.toSMTType]) (len_eq := len_eq_p)
            · intro v hv
              rw [List.mem_singleton] at hv
              subst hv
              exact p_fresh
            · exact fresh_exists
            · exact Nat.zero_lt_succ 0
            · have hupdate_p :
                  SMT.TypeContext.update ctx [p] [αx.toSMTType.pair βx.toSMTType] len_eq_p =
                    ctx.insert p (αx.toSMTType.pair βx.toSMTType) := by
                unfold SMT.TypeContext.update
                simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
                  Fin.cast_eq_self, Fin.getElem_fin, Fin.val_eq_zero,
                  List.getElem_cons_zero, Fin.foldl_succ, Fin.foldl_zero]
              rw [hupdate_p]
              exact typ_exists
          rw [St₃_types_eq]
          exact Typing.weakening
            (h := fun v hv =>
              SMT.TypeContext.entries_subset_insert_of_notMem b_fresh
                (SMT.TypeContext.entries_subset_insert_of_notMem a_fresh
                  (SMT.TypeContext.entries_subset_insert_of_notMem p_fresh hv)))
            typ_tcprod_ctx
        · -- preserves_types
          intro v hv h1 h2
          rw [B.fv, List.mem_append] at h2; push_neg at h2
          have hv_StS : v ∈ StS.env.usedVars := St_used_sub_StS (by simpa [St_used_eq] using hv)
          have hv_not_StS : v ∉ StS.types :=
            S_preserves v (by simpa [St_used_eq] using hv) h1 h2.1
          have hv_not_StT : v ∉ StT.types :=
            T_preserves v hv_StS hv_not_StS h2.2
          rw [St₃_types_eq]
          intro hv_in
          iterate 3 rw [AList.mem_insert] at hv_in
          rcases hv_in with rfl | rfl | rfl | hv_in
          · -- v = b: b ∉ St'.usedVars since b_not_used
            apply b_not_used
            rw [St₂_used_eq, St₁_used_eq]
            exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (StS_used_sub_StT hv_StS))
          · -- v = a: a ∉ St'.usedVars since a_not_used
            apply a_not_used
            rw [St₁_used_eq]
            exact List.mem_cons_of_mem _ (StS_used_sub_StT hv_StS)
          · -- v = p: p ∉ St'.usedVars since p_not_used
            exact p_not_used (StS_used_sub_StT hv_StS)
          · -- v ∈ StT.types = ctx
            exact hv_not_StT hv_in
        · have hcov_tcprod : RenamingContext.CoversFV Δ'' tcprod := by
            intro v hv
            dsimp [tcprod] at hv
            rw [SMT.fv, List.mem_removeAll_iff] at hv
            rcases hv with ⟨hv, hv_ne_p⟩
            dsimp [body] at hv
            rw [SMT.fv, List.mem_removeAll_iff] at hv
            rcases hv with ⟨hv, hv_ne_ab⟩
            rw [SMT.fv, List.mem_append] at hv
            rcases hv with hvSa | hv
            · rw [SMT.fv, List.mem_append] at hvSa
              rcases hvSa with hvS | hva
              · exact hΔ_S_final v hvS
              · exfalso
                have hva' : v = a := by
                  simpa [SMT.fv] using hva
                exact hv_ne_ab (by simp [hva'])
            · rw [SMT.fv, List.mem_append] at hv
              rcases hv with hvTb | hvEq
              · rw [SMT.fv, List.mem_append] at hvTb
                rcases hvTb with hvT | hvb
                · exact Δ''_covers_T v hvT
                · exfalso
                  have hvb' : v = b := by
                    simpa [SMT.fv] using hvb
                  apply hv_ne_ab
                  simp only [hvb', List.mem_cons, List.not_mem_nil, or_false, or_true]
              · rw [SMT.fv, List.mem_append] at hvEq
                rcases hvEq with hvp | hvPair
                · exfalso
                  have hvp' : v = p := by
                    simpa [SMT.fv] using hvp
                  apply hv_ne_p
                  simp only [hvp', List.mem_cons, List.not_mem_nil, or_false]
                · rw [SMT.fv, List.mem_append] at hvPair
                  rcases hvPair with hva | hvb
                  · exfalso
                    have hva' : v = a := by
                      simpa [SMT.fv] using hva
                    exact hv_ne_ab (by simp [hva'])
                  · exfalso
                    have hvb' : v = b := by
                      simp only [SMT.fv, List.mem_cons, List.not_mem_nil, or_false] at hvb
                      exact hvb
                    apply hv_ne_ab
                    simp only [hvb', List.mem_cons, List.not_mem_nil, or_false, or_true]
          refine ⟨Δ'', hcov_tcprod, ?_⟩
          and_intros
          · exact RenamingContext.extends_trans Δ''_extends_Δ' Δ'_extends_Δ₀
          · exact RenamingContext.extendsOnSourceFV_of_extends
              (RenamingContext.extends_trans Δ''_extends_Δ' Δ'_extends_Δ₀) Δ₀_ext
          · intro v hv
            exact Δ''_none_out v (by
              simp only [St₃_used_eq, St₂_used_eq, St₁_used_eq, List.mem_cons, not_or] at hv
              exact hv.2.2.2)
          · obtain ⟨denT_main, hden_main, hRDom_main⟩ :=
              cprod_case_denotation_aux
                (αx := αx) (βx := βx) (X := X) (Y := Y) (hT := hT)
                (ctx := ctx) (S_enc := S_enc) (T_enc := T_enc) (Δ'' := Δ'')
                (Senc := Senc) (Tenc := Tenc)
                (typ_T_enc := typ_T_enc) (typ_S_enc_T := typ_S_enc_T)
                (p := p) (a := a) (b := b)
                (p_fresh := p_fresh) (a_fresh := a_fresh) (b_fresh := b_fresh)
                (hSenc := hSenc) (hTenc := hTenc)
                (retract_Senc_eq_X := retract_Senc_eq_X)
                (retract_Tenc_eq_Y := retract_Tenc_eq_Y)
                (hΔ_S_final := hΔ_S_final) (Δ''_covers_T := Δ''_covers_T)
                (den_S_enc_final := den_S_enc_final) (den_T_enc := den_T_enc)
                (hcov_tcprod_in := hcov_tcprod)
            refine ⟨denT_main, hden_main, hRDom_main, ?_⟩
            -- alt universality for cprod
            intro Δ_alt Δ_fv_alt Δ₀_alt Δ₀_alt_ext Δ₀_alt_none_out Δ₀_alt_wt T_alt hT_alt den_t_alt
            -- Decompose B-denotation of (S ⨯ᴮ T_1) under alt valuation
            rw [B.Term.abstract, B.denote, Option.pure_def, Option.bind_eq_bind,
              Option.bind_eq_some_iff] at den_t_alt
            obtain ⟨⟨X_alt, τX_alt, hX_alt⟩, den_S_alt, eq_alt⟩ := den_t_alt
            have hτX_alt := denote_welltyped_eq
              (t := S.abstract («Δ» := Δ_alt)
                (fun v hv => Δ_fv_alt v (by rw [B.fv, List.mem_append]; exact Or.inl hv)))
              ?_ den_S_alt
            on_goal 2 =>
              use E.context.abstract («Δ» := Δ_alt), WFTC.of_abstract, .set αx
              exact @Typing.of_abstract (B.Dom) («Δ» := Δ_alt) ?_ S E.context (.set αx)
                (fun v hv => Δ_fv_alt v (by rw [B.fv, List.mem_append]; exact Or.inl hv)) typ_S
            dsimp at hτX_alt; subst τX_alt
            dsimp at eq_alt
            rw [Option.bind_eq_some_iff] at eq_alt
            obtain ⟨⟨Y_alt, τY_alt, hY_alt⟩, den_T_alt, eq_alt⟩ := eq_alt
            have hτY_alt := denote_welltyped_eq
              (t := T_1.abstract («Δ» := Δ_alt)
                (fun v hv => Δ_fv_alt v (by rw [B.fv, List.mem_append]; exact Or.inr hv)))
              ?_ den_T_alt
            on_goal 2 =>
              use E.context.abstract («Δ» := Δ_alt), WFTC.of_abstract, .set βx
              exact @Typing.of_abstract (B.Dom) («Δ» := Δ_alt) ?_ T_1 E.context (.set βx)
                (fun v hv => Δ_fv_alt v (by rw [B.fv, List.mem_append]; exact Or.inr hv)) typ_T
            dsimp at hτY_alt; subst τY_alt
            rw [Option.some_inj] at eq_alt
            injection eq_alt with T_alt_eq
            subst T_alt
            -- Build restricted base for S IH: zero outside StS.usedVars
            set Δ₀_alt_S : SMT.RenamingContext.Context :=
              fun v => if v ∈ StS.env.usedVars then Δ₀_alt v else none with Δ₀_alt_S_def
            -- ExtendsOnSourceFV Δ₀_alt_S Δ_alt S
            have Δ₀_alt_S_ext : RenamingContext.ExtendsOnSourceFV Δ₀_alt_S Δ_alt S := by
              have hsrc := RenamingContext.extendsOnSourceFV_of_fv_subset
                (hsub := by intro v hv; simpa [B.fv] using (Or.inl hv : v ∈ B.fv S ∨ v ∈ B.fv T_1))
                Δ₀_alt_ext
              intro v d hv
              simp only [Δ₀_alt_S_def]
              have hv_fv_S : v ∈ B.fv S := by
                by_contra hv_not
                simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                  B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_not] at hv
              have hv_used : v ∈ StS.env.usedVars :=
                St_used_sub_StS (vars_used v (by
                  simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append]
                  left; left; exact hv_fv_S))
              rw [if_pos hv_used]
              exact hsrc hv
            -- none_out for Δ₀_alt_S at StS
            have Δ₀_alt_S_none : ∀ v ∉ StS.env.usedVars, Δ₀_alt_S v = none := by
              intro v hv; simp only [Δ₀_alt_S_def]; rw [if_neg hv]
            have Δ₀_alt_S_wt : ∀ v (d : SMT.Dom), Δ₀_alt_S v = some d → ∀ τ, StS.types.lookup v = some τ → d.snd.fst = τ := by
              intro v d hv τ hτ; simp only [Δ₀_alt_S_def] at hv; split_ifs at hv with h; exact Δ₀_alt_wt v d hv τ (by rw [St₃_types_eq]; exact AList.mem_lookup_iff.mpr (SMT.TypeContext.entries_subset_insert_of_notMem b_fresh (SMT.TypeContext.entries_subset_insert_of_notMem a_fresh (SMT.TypeContext.entries_subset_insert_of_notMem p_fresh (StS_eq_StT (AList.mem_lookup_iff.mp hτ))))))
            -- Call S_ih_total
            obtain ⟨Δ'_alt_S, hcov_alt_S, denT_S_alt, hext_alt_S,
              Δ'_alt_S_none_out, Δ'_alt_S_wt_out, den_S_alt_enc, hRDom_S_alt, _⟩ :=
              S_ih_total Δ_alt
                (fun v hv => Δ_fv_alt v (by rw [B.fv, List.mem_append]; exact Or.inl hv))
                Δ₀_alt_S Δ₀_alt_S_ext Δ₀_alt_S_none Δ₀_alt_S_wt X_alt hX_alt den_S_alt
            -- Build hybrid base for T IH: Δ₀_alt priority, else Δ'_alt_S, restricted to StT
            set Δ₀_alt_T : SMT.RenamingContext.Context :=
              fun v => if v ∈ StT.env.usedVars then
                match Δ₀_alt v with
                  | some d => some d
                  | none => if v ∈ StS.types then Δ'_alt_S v else none
              else none
              with Δ₀_alt_T_def
            -- ExtendsOnSourceFV Δ₀_alt_T Δ_alt T_1
            have Δ₀_alt_T_ext : RenamingContext.ExtendsOnSourceFV Δ₀_alt_T Δ_alt T_1 := by
              have hsrc := RenamingContext.extendsOnSourceFV_of_fv_subset
                (hsub := by intro v hv; simpa [B.fv] using (Or.inr hv : v ∈ B.fv S ∨ v ∈ B.fv T_1))
                Δ₀_alt_ext
              intro v d hv
              simp only [Δ₀_alt_T_def]
              have hΔ₀_val := hsrc hv
              have hv_fv_T : v ∈ B.fv T_1 := by
                by_contra hv_not
                simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                  B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_not] at hv
              have hv_StT : v ∈ StT.env.usedVars :=
                StS_used_sub_StT (St_used_sub_StS (vars_used v (by
                  simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append]
                  left; right; exact hv_fv_T)))
              rw [if_pos hv_StT]
              simp [hΔ₀_val]
            -- none_out for Δ₀_alt_T at StT
            have Δ₀_alt_T_none : ∀ v ∉ StT.env.usedVars, Δ₀_alt_T v = none := by
              intro v hv; simp only [Δ₀_alt_T_def]; rw [if_neg hv]
            have Δ₀_alt_T_wt : ∀ v (d : SMT.Dom), Δ₀_alt_T v = some d → ∀ τ, StT.types.lookup v = some τ → d.snd.fst = τ := by
              intro v d hv τ hτ
              simp only [Δ₀_alt_T_def] at hv
              have hv_used : v ∈ StT.env.usedVars := by
                by_contra h; rw [if_neg h] at hv; exact Option.noConfusion hv
              rw [if_pos hv_used] at hv
              cases hΔ : Δ₀_alt v with
              | some d' =>
                simp [hΔ] at hv; subst hv
                exact Δ₀_alt_wt v d' hΔ τ (by
                  rw [St₃_types_eq]
                  exact AList.mem_lookup_iff.mpr
                    (SMT.TypeContext.entries_subset_insert_of_notMem b_fresh
                      (SMT.TypeContext.entries_subset_insert_of_notMem a_fresh
                        (SMT.TypeContext.entries_subset_insert_of_notMem p_fresh
                          (AList.mem_lookup_iff.mp hτ)))))
              | none =>
                simp [hΔ] at hv
                obtain ⟨hv_types, hv⟩ := hv
                apply Δ'_alt_S_wt_out v d hv
                obtain ⟨τ', hτ'⟩ := Option.isSome_iff_exists.mp (AList.lookup_isSome.mpr hv_types)
                have h_lkp := AList.lookup_of_subset StS_eq_StT hτ'
                rw [hτ] at h_lkp; cases h_lkp; exact hτ'
            -- Call T_ih_total
            obtain ⟨Δ'_alt_T, hcov_alt_T, denT_T_alt, hext_alt_T,
              Δ'_alt_T_none_out, Δ'_alt_T_wt_out, den_T_alt_enc, hRDom_T_alt, Δ'_alt_T_dom_out⟩ :=
              T_ih_total Δ_alt
                (fun v hv => Δ_fv_alt v (by rw [B.fv, List.mem_append]; exact Or.inr hv))
                Δ₀_alt_T Δ₀_alt_T_ext Δ₀_alt_T_none Δ₀_alt_T_wt Y_alt hY_alt den_T_alt
            -- Define final Δ'_alt: Δ₀_alt priority, else Δ'_alt_T
            set Δ'_alt : SMT.RenamingContext.Context :=
              fun v => match Δ₀_alt v with | some d => some d | none => Δ'_alt_T v
              with Δ'_alt_def
            -- Coverage for Δ'_alt on fv(tcprod)
            have hcov_tcprod_alt : RenamingContext.CoversFV Δ'_alt tcprod := by
              intro v hv
              dsimp [tcprod] at hv
              rw [SMT.fv, List.mem_removeAll_iff] at hv
              rcases hv with ⟨hv, hv_ne_p⟩
              dsimp [body] at hv
              rw [SMT.fv, List.mem_removeAll_iff] at hv
              rcases hv with ⟨hv, hv_ne_ab⟩
              rw [SMT.fv, List.mem_append] at hv
              simp only [Δ'_alt_def]
              cases h : Δ₀_alt v with
              | some d => simp
              | none =>
                rcases hv with hvSa | hv
                · rw [SMT.fv, List.mem_append] at hvSa
                  rcases hvSa with hvS | hva
                  · -- v ∈ fv(S_enc): covered by Δ'_alt_S
                    have hS_some : (Δ'_alt_S v).isSome = true := hcov_alt_S v hvS
                    have hv_StS : v ∈ StS.env.usedVars := by
                      by_contra hv_not
                      exact absurd (Δ'_covers_S v hvS) (by simp [Δ'_none_out v hv_not])
                    have hv_StT : v ∈ StT.env.usedVars := StS_used_sub_StT hv_StS
                    have hv_types : v ∈ StS.types := SMT.Typing.mem_context_of_mem_fv typ_S_enc hvS
                    have hΔ₀_alt_T_v : Δ₀_alt_T v = Δ'_alt_S v := by
                      simp [Δ₀_alt_T_def, h, if_pos hv_StT, if_pos hv_types]
                    obtain ⟨ds, hds⟩ := Option.isSome_iff_exists.mp hS_some
                    have : Δ₀_alt_T v = some ds := by rw [hΔ₀_alt_T_v, hds]
                    have := hext_alt_T this
                    rw [this]; simp
                  · exfalso
                    have hva' : v = a := by simpa [SMT.fv] using hva
                    exact hv_ne_ab (by simp [hva'])
                · rw [SMT.fv, List.mem_append] at hv
                  rcases hv with hvTb | hvEq
                  · rw [SMT.fv, List.mem_append] at hvTb
                    rcases hvTb with hvT | hvb
                    · exact hcov_alt_T v hvT
                    · exfalso
                      have hvb' : v = b := by simpa [SMT.fv] using hvb
                      apply hv_ne_ab
                      simp only [hvb', List.mem_cons, List.not_mem_nil, or_false, or_true]
                  · rw [SMT.fv, List.mem_append] at hvEq
                    rcases hvEq with hvp | hvPair
                    · exfalso
                      have hvp' : v = p := by simpa [SMT.fv] using hvp
                      apply hv_ne_p
                      simp only [hvp', List.mem_cons, List.not_mem_nil, or_false]
                    · rw [SMT.fv, List.mem_append] at hvPair
                      rcases hvPair with hva | hvb
                      · exfalso
                        have hva' : v = a := by simpa [SMT.fv] using hva
                        exact hv_ne_ab (by simp [hva'])
                      · exfalso
                        have hvb' : v = b := by
                          simp only [SMT.fv, List.mem_cons, List.not_mem_nil, or_false] at hvb
                          exact hvb
                        apply hv_ne_ab
                        simp only [hvb', List.mem_cons, List.not_mem_nil, or_false, or_true]
            -- Δ'_alt agrees with Δ'_alt_S on fv(S_enc)
            have hagree_S : RenamingContext.AgreesOnFV Δ'_alt Δ'_alt_S S_enc := by
              intro v hv
              simp only [Δ'_alt_def]
              cases h : Δ₀_alt v with
              | some d =>
                have hv_σS : v ∈ StS.env.usedVars := by
                  by_contra hv_not
                  exact absurd (Δ'_covers_S v hv) (by simp [Δ'_none_out v hv_not])
                have : Δ₀_alt_S v = some d := by simp [Δ₀_alt_S_def, if_pos hv_σS, h]
                symm; exact hext_alt_S this
              | none =>
                have hS_some : (Δ'_alt_S v).isSome = true := hcov_alt_S v hv
                have hv_StS : v ∈ StS.env.usedVars := by
                  by_contra hv_not
                  exact absurd (Δ'_covers_S v hv) (by simp [Δ'_none_out v hv_not])
                have hv_StT : v ∈ StT.env.usedVars := StS_used_sub_StT hv_StS
                have hv_types : v ∈ StS.types := SMT.Typing.mem_context_of_mem_fv typ_S_enc hv
                have hΔ₀_alt_T_v : Δ₀_alt_T v = Δ'_alt_S v := by
                  simp [Δ₀_alt_T_def, h, if_pos hv_StT, if_pos hv_types]
                obtain ⟨ds, hds⟩ := Option.isSome_iff_exists.mp hS_some
                have h₁ : Δ₀_alt_T v = some ds := by rw [hΔ₀_alt_T_v, hds]
                rw [hext_alt_T h₁, hds]
            -- Δ'_alt agrees with Δ'_alt_T on fv(T_enc)
            have hagree_T : RenamingContext.AgreesOnFV Δ'_alt Δ'_alt_T T_enc := by
              intro v hv
              simp only [Δ'_alt_def]
              cases h : Δ₀_alt v with
              | some d =>
                have hv_StT : v ∈ StT.env.usedVars := by
                  by_contra hv_not
                  exact absurd (Δ''_covers_T v hv) (by simp [Δ''_none_out v hv_not])
                have : Δ₀_alt_T v = some d := by simp [Δ₀_alt_T_def, h, if_pos hv_StT]
                symm; exact hext_alt_T this
              | none => rfl
            -- S_enc denotes under Δ'_alt
            have hcov_S_in_alt : RenamingContext.CoversFV Δ'_alt S_enc := by
              intro v hv
              exact hcov_tcprod_alt v (by
                dsimp [tcprod]
                rw [SMT.fv, List.mem_removeAll_iff]
                constructor
                · dsimp [body]
                  rw [SMT.fv, List.mem_removeAll_iff]
                  refine ⟨?_, ?_⟩
                  · rw [SMT.fv, List.mem_append]; left
                    rw [SMT.fv, List.mem_append]; left; exact hv
                  · intro hab
                    have ha_not_ctx : a ∉ ctx :=
                      fun ha_in => a_fresh (by rw [AList.mem_insert]; exact Or.inr ha_in)
                    have hb_not_ctx : b ∉ ctx :=
                      fun hb_in => b_fresh (by rw [AList.mem_insert, AList.mem_insert]; exact Or.inr (Or.inr hb_in))
                    have := funNotMemFvOfNotMemContext typ_S_enc_T ha_not_ctx
                    rw [List.mem_cons, List.mem_singleton] at hab
                    rcases hab with rfl | rfl
                    · exact this hv
                    · exact funNotMemFvOfNotMemContext typ_S_enc_T hb_not_ctx hv
                · intro hp
                  rw [List.mem_singleton] at hp
                  subst hp
                  exact funNotMemFvOfNotMemContext typ_S_enc_T p_fresh hv)
            have den_S_alt_final :
                ⟦S_enc.abstract Δ'_alt hcov_S_in_alt⟧ˢ = some denT_S_alt := by
              have := RenamingContext.denote_congr_of_agreesOnFV
                (t := S_enc) (h1 := hcov_S_in_alt) (h2 := hcov_alt_S) hagree_S
              simpa [RenamingContext.denote] using this.trans den_S_alt_enc
            -- T_enc denotes under Δ'_alt
            have hcov_T_in_alt : RenamingContext.CoversFV Δ'_alt T_enc := by
              intro v hv
              exact hcov_tcprod_alt v (by
                dsimp [tcprod]
                rw [SMT.fv, List.mem_removeAll_iff]
                constructor
                · dsimp [body]
                  rw [SMT.fv, List.mem_removeAll_iff]
                  refine ⟨?_, ?_⟩
                  · rw [SMT.fv, List.mem_append]; right
                    rw [SMT.fv, List.mem_append]; left
                    rw [SMT.fv, List.mem_append]; left; exact hv
                  · intro hab
                    have ha_not_ctx : a ∉ ctx :=
                      fun ha_in => a_fresh (by rw [AList.mem_insert]; exact Or.inr ha_in)
                    have hb_not_ctx : b ∉ ctx :=
                      fun hb_in => b_fresh (by rw [AList.mem_insert, AList.mem_insert]; exact Or.inr (Or.inr hb_in))
                    have := funNotMemFvOfNotMemContext typ_T_enc ha_not_ctx
                    rw [List.mem_cons, List.mem_singleton] at hab
                    rcases hab with rfl | rfl
                    · exact this hv
                    · exact funNotMemFvOfNotMemContext typ_T_enc hb_not_ctx hv
                · intro hp
                  rw [List.mem_singleton] at hp
                  subst hp
                  exact funNotMemFvOfNotMemContext typ_T_enc p_fresh hv)
            have den_T_alt_final :
                ⟦T_enc.abstract Δ'_alt hcov_T_in_alt⟧ˢ = some denT_T_alt := by
              have := RenamingContext.denote_congr_of_agreesOnFV
                (t := T_enc) (h1 := hcov_T_in_alt) (h2 := hcov_alt_T) hagree_T
              simpa [RenamingContext.denote] using this.trans den_T_alt_enc
            -- Extract Senc_alt and Tenc_alt from denT_S_alt and denT_T_alt
            obtain ⟨Senc_alt, σS_alt, hSenc_alt⟩ := denT_S_alt
            obtain ⟨Tenc_alt, σT_alt, hTenc_alt⟩ := denT_T_alt
            obtain ⟨rfl, retract_S_alt⟩ := hRDom_S_alt
            obtain ⟨rfl, retract_T_alt⟩ := hRDom_T_alt
            -- Use cprod_case_denotation_aux for the alt denotation
            have hΔ_S_alt_final : RenamingContext.CoversFV Δ'_alt S_enc := hcov_S_in_alt
            obtain ⟨denT_cprod_alt, hden_cprod_alt, hRDom_cprod_alt⟩ :=
              cprod_case_denotation_aux
                (αx := αx) (βx := βx) (X := X_alt) (Y := Y_alt) (hT := hT_alt)
                (ctx := ctx) (S_enc := S_enc) (T_enc := T_enc) (Δ'' := Δ'_alt)
                (Senc := Senc_alt) (Tenc := Tenc_alt)
                (typ_T_enc := typ_T_enc) (typ_S_enc_T := typ_S_enc_T)
                (p := p) (a := a) (b := b)
                (p_fresh := p_fresh) (a_fresh := a_fresh) (b_fresh := b_fresh)
                (hSenc := hSenc_alt) (hTenc := hTenc_alt)
                (retract_Senc_eq_X := retract_S_alt)
                (retract_Tenc_eq_Y := retract_T_alt)
                (hΔ_S_final := hΔ_S_alt_final) (Δ''_covers_T := hcov_T_in_alt)
                (den_S_enc_final := den_S_alt_final) (den_T_enc := den_T_alt_final)
                (hcov_tcprod_in := hcov_tcprod_alt)
            refine ⟨Δ'_alt, hcov_tcprod_alt, denT_cprod_alt, ?_, ?_, ?_, hden_cprod_alt, hRDom_cprod_alt, ?_⟩
            -- Extends Δ'_alt Δ₀_alt
            · intro v d hv; simp only [Δ'_alt_def, hv]
            -- Vanishing: ∀ v ∉ E'.usedVars, Δ'_alt v = none
            · intro v hv; simp only [Δ'_alt_def]
              rw [Δ₀_alt_none_out v hv]
              apply Δ'_alt_T_none_out
              intro hmem; exact hv (by rw [St₃_used_eq, St₂_used_eq, St₁_used_eq]; exact .tail _ (.tail _ (.tail _ hmem)))
            -- Well-typedness: output wt
            · intro v d hv τ hτ
              simp only [Δ'_alt_def] at hv
              cases hΔ : Δ₀_alt v with
              | some d' => simp [hΔ] at hv; subst hv; exact Δ₀_alt_wt v d' hΔ τ hτ
              | none =>
                simp [hΔ] at hv
                apply Δ'_alt_T_wt_out v d hv τ
                have hv_StT : v ∈ StT.env.usedVars := by
                  by_contra hv_not
                  exact absurd (Δ'_alt_T_none_out v hv_not) (by rw [hv]; exact Option.some_ne_none _)
                have hv_ne_p : v ≠ p := fun h => p_not_used (h ▸ hv_StT)
                have hv_ne_a : v ≠ a := fun h => a_not_used (St₁_used_eq ▸ List.mem_cons_of_mem _ (h ▸ hv_StT))
                have hv_ne_b : v ≠ b := fun h => b_not_used (St₂_used_eq ▸ List.mem_cons_of_mem _ (St₁_used_eq ▸ List.mem_cons_of_mem _ (h ▸ hv_StT)))
                rw [St₃_types_eq] at hτ
                rwa [AList.lookup_insert_ne hv_ne_b, AList.lookup_insert_ne hv_ne_a,
                  AList.lookup_insert_ne hv_ne_p] at hτ
            -- dom_out
            · intro v hv
              simp only [Δ'_alt_def] at hv
              cases hΔ : Δ₀_alt v with
              | some d =>
                exact fv_sub_typings (_root_.B.Typing.cprod typ_S typ_T)
                  (SMT.Typing.bool St₃.types true) v
                  (SMT.RenamingContext.ExtendsOnSourceFV.dom_sub_B_fv Δ₀_alt_ext v
                    (by rw [hΔ]; simp))
              | none =>
                simp [hΔ] at hv
                have h_StT := Δ'_alt_T_dom_out v hv
                rw [St₃_types_eq, AList.mem_insert, AList.mem_insert, AList.mem_insert]
                exact Or.inr (Or.inr (Or.inr h_StT))
