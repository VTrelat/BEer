import SMT.Reasoning.Defs
import SMT.Reasoning.LooseningDefs
import SMT.Reasoning.Basic.StateSpecs
import Encoder.Loosening.Rules

open Std.Do SMT ZFSet Classical

set_option maxHeartbeats 2000000

private theorem funUnaryTarget
    {α : SMTType} {y : ZFSet}
    (hy : y ∈ ⟦α⟧ᶻ) :
    y.hasArity 1 ∧ ∀ i : Fin 1, y ∈ ⟦[α][i]⟧ᶻ := by
  constructor
  · simp [ZFSet.hasArity]
  · rintro ⟨i, hi⟩
    simp at hi
    subst hi
    simpa using hy

private theorem defaultZFSetFunIsFunc
    {α β : SMTType} :
    ZFSet.IsFunc ⟦α⟧ᶻ ⟦β⟧ᶻ (SMTType.defaultZFSet (α.fun β)) := by
  rw [←ZFSet.mem_funs]
  exact SMTType.mem_toZFSet_of_defaultZFSet (α := α.fun β)

private theorem defaultZFSetFunApp
    {α β : SMTType} {x : ZFSet}
    (hx : x ∈ ⟦α⟧ᶻ) :
    ZFSet.fapply (SMTType.defaultZFSet (α.fun β))
      (ZFSet.is_func_is_pfunc (defaultZFSetFunIsFunc (α := α) (β := β)))
      ⟨x, by
        simpa [ZFSet.is_func_dom_eq (defaultZFSetFunIsFunc (α := α) (β := β))] using hx⟩ =
      β.defaultZFSet := by
  have hfun : ZFSet.IsFunc ⟦α⟧ᶻ ⟦β⟧ᶻ (SMTType.defaultZFSet (α.fun β)) :=
    defaultZFSetFunIsFunc (α := α) (β := β)
  have hpair :
      x.pair β.defaultZFSet ∈ SMTType.defaultZFSet (α.fun β) := by
    rw [SMTType.defaultZFSet, ZFSet.mem_sep]
    constructor
    · rw [ZFSet.pair_mem_prod]
      exact ⟨hx, SMTType.mem_toZFSet_of_defaultZFSet⟩
    · rw [ZFSet.π₂_pair]
  exact congrArg Subtype.val
    (ZFSet.fapply.of_pair (hf := ZFSet.is_func_is_pfunc hfun) hpair)

private theorem defaultSpecMFunDenoteAppAt
    {Δctx : RenamingContext.Context} {t : Term} {x : 𝒱}
    {α β : SMTType} {Y : SMT.Dom}
    (hcov_t_upd :
      ∀ Xarg : SMT.Dom,
        RenamingContext.CoversFV (Function.update Δctx x (some Xarg)) t)
    (den_t_upd :
      ∀ Xarg : SMT.Dom,
        ⟦t.abstract (Function.update Δctx x (some Xarg)) (hcov_t_upd Xarg)⟧ˢ = some Y)
    (hY_ty : Y.snd.fst = α.fun β)
    (hY_func : ZFSet.IsFunc ⟦α⟧ᶻ ⟦β⟧ᶻ Y.fst)
    (Xarg : SMT.Dom)
    (hXarg_ty : Xarg.snd.fst = α)
    (hXarg_mem : Xarg.fst ∈ ⟦α⟧ᶻ) :
    ∃ hcov_app : RenamingContext.CoversFV (Function.update Δctx x (some Xarg)) (.app t (.var x)),
      ∃ Dapp : SMT.Dom,
        Dapp.snd.fst = β ∧
          Dapp.fst =
            @ᶻY.fst
              ⟨Xarg.fst, by
                simpa [ZFSet.is_func_dom_eq hY_func] using hXarg_mem⟩ ∧
          ⟦(Term.app t (.var x)).abstract (Function.update Δctx x (some Xarg)) hcov_app⟧ˢ = some Dapp := by
  let hcov_app :
      RenamingContext.CoversFV (Function.update Δctx x (some Xarg)) (Term.app t (.var x)) := by
    intro v hv
    simp only [SMT.fv, List.mem_append, List.mem_singleton] at hv
    rcases hv with hv | hv
    · exact hcov_t_upd Xarg v hv
    · subst hv
      simp
  let Dapp : SMT.Dom :=
    ⟨@ᶻY.fst
        ⟨Xarg.fst, by
          simpa [ZFSet.is_func_dom_eq hY_func] using hXarg_mem⟩,
      β,
      by
        have hY_mem : Y.fst ∈ ⟦α⟧ᶻ.funs ⟦β⟧ᶻ := ZFSet.mem_funs.mpr hY_func
        rw [ZFSet.mem_funs] at hY_mem
        obtain ⟨y, hy_pair, hy_unique⟩ := hY_mem.2 Xarg.fst hXarg_mem
        have hEq :
            ZFSet.fapply Y.fst (ZFSet.is_func_is_pfunc hY_func)
              ⟨Xarg.fst, by
                simpa [ZFSet.is_func_dom_eq hY_func] using hXarg_mem⟩ = y := by
          exact congrArg Subtype.val
            (ZFSet.fapply.of_pair (hf := ZFSet.is_func_is_pfunc hY_func) hy_pair)
        have hy_mem : y ∈ ⟦β⟧ᶻ := by
          have hy_prod : Xarg.fst.pair y ∈ ⟦α⟧ᶻ.prod ⟦β⟧ᶻ := hY_mem.1 hy_pair
          rw [ZFSet.pair_mem_prod] at hy_prod
          exact hy_prod.2
        rw [hEq]
        exact hy_mem⟩
  refine ⟨hcov_app, Dapp, rfl, rfl, ?_⟩
  cases Y with
  | mk y hy =>
      cases hy with
      | mk τ hy =>
          cases hY_ty
          have hcov_var :
              RenamingContext.CoversFV (Function.update Δctx x (some Xarg)) (Term.var x) := by
            intro v hv
            rw [fv, List.mem_singleton] at hv
            subst hv
            simp [Function.update]
          have hden_var :
              ⟦(Term.var x).abstract (Function.update Δctx x (some Xarg)) hcov_var⟧ˢ = some Xarg := by
            rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some.injEq]
            apply Option.get_of_eq_some
            exact Function.update_self _ _ _
          rw [SMT.Term.abstract, SMT.denote, den_t_upd Xarg, hden_var]
          simp only [Option.bind_some]
          dsimp [Dapp]
          have hy_pfunc : y.IsPFunc ⟦α⟧ᶻ ⟦β⟧ᶻ := ZFSet.is_func_is_pfunc hY_func
          rw [if_pos hXarg_ty.symm, dif_pos hy_pfunc]
          have hx_dom : Xarg.fst ∈ y.Dom := by
            simpa [ZFSet.is_func_dom_eq hY_func] using hXarg_mem
          rw [dif_pos hx_dom]

private theorem denoteAndTrueComponents
    {p q : SMT.PHOAS.Term SMT.Dom} {Φ : SMT.Dom}
    (typ_p_bool : ∀ {Dp : SMT.Dom}, ⟦p⟧ˢ = some Dp → Dp.snd.fst = .bool)
    (typ_q_bool : ∀ {Dq : SMT.Dom}, ⟦q⟧ˢ = some Dq → Dq.snd.fst = .bool)
    (hden : ⟦p ∧ˢ' q⟧ˢ = some Φ)
    (htrue : Φ.fst = zftrue) :
    ∃ Dp Dq, ⟦p⟧ˢ = some Dp ∧ Dp.fst = zftrue ∧ ⟦q⟧ˢ = some Dq ∧ Dq.fst = zftrue := by
  cases hp : ⟦p⟧ˢ with
  | none =>
      simp [SMT.denote, hp] at hden
  | some Dp =>
      cases hq : ⟦q⟧ˢ with
      | none =>
          have hpTy : Dp.snd.fst = .bool := typ_p_bool hp
          obtain ⟨dp, τ, hdp⟩ := Dp
          cases hpTy
          simp [SMT.denote, hp, hq] at hden
      | some Dq =>
          have hpTy : Dp.snd.fst = .bool := typ_p_bool hp
          have hqTy : Dq.snd.fst = .bool := typ_q_bool hq
          have hpTrue : Dp.fst = zftrue := by
            have hDp_mem_bool : Dp.fst ∈ 𝔹 := by
              simpa [hpTy] using Dp.snd.snd
            rw [ZFSet.ZFBool.mem_𝔹_iff] at hDp_mem_bool
            rcases hDp_mem_bool with hDpFalse | hDpTrue
            · have hden_false := denote_and_eq_zffalse_of_some_zffalse_left hp hpTy hDpFalse hq hqTy
              have hΦ_false : Φ.fst = zffalse := by
                have hEq :
                    some Φ = some ⟨zffalse, .bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
                  exact hden.symm.trans hden_false
                obtain ⟨φ, τ, hφ⟩ := Φ
                cases hEq
                rfl
              exact False.elim (ZFSet.zftrue_ne_zffalse (htrue.symm.trans hΦ_false))
            · exact hDpTrue
          have hqTrue : Dq.fst = zftrue := by
            have hDq_mem_bool : Dq.fst ∈ 𝔹 := by
              simpa [hqTy] using Dq.snd.snd
            rw [ZFSet.ZFBool.mem_𝔹_iff] at hDq_mem_bool
            rcases hDq_mem_bool with hDqFalse | hDqTrue
            · have hden_false := denote_and_eq_zffalse_of_some_zffalse_right hp hpTy hq hqTy hDqFalse
              have hΦ_false : Φ.fst = zffalse := by
                have hEq :
                    some Φ = some ⟨zffalse, .bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
                  exact hden.symm.trans hden_false
                obtain ⟨φ, τ, hφ⟩ := Φ
                cases hEq
                rfl
              exact False.elim (ZFSet.zftrue_ne_zffalse (htrue.symm.trans hΦ_false))
            · exact hDqTrue
          refine ⟨Dp, Dq, ?_⟩
          constructor
          · rfl
          constructor
          · exact hpTrue
          constructor
          · rfl
          · exact hqTrue

private theorem sInterSepEqZftrueImpliesForallEqZftrue
    {D : ZFSet} {F : ZFSet → ZFSet}
    (hbool : ∀ x ∈ D, F x ∈ 𝔹)
    (hsInter :
      (⋂₀ (ZFSet.sep (fun y => ∃ x ∈ D, y = F x) 𝔹) : ZFSet) = zftrue) :
    ∀ x ∈ D, F x = zftrue := by
  intro x hx
  have hnot_false : F x ≠ zffalse := by
    intro hFx_false
    have hnot :
        ZFSet.ZFBool.not
            ⟨⋂₀ (ZFSet.sep (fun y => ∃ x ∈ D, y = F x) 𝔹),
              ZFSet.sInter_sep_subset_of_𝔹_mem_𝔹 (fun _ => id)⟩ = ⊤ := by
      exact not_sInter_sep_eq_zftrue_of_exists_eq_zffalse ⟨x, hx, hFx_false⟩
    have hsBool :
        (⟨⋂₀ (ZFSet.sep (fun y => ∃ x ∈ D, y = F x) 𝔹),
          ZFSet.sInter_sep_subset_of_𝔹_mem_𝔹 (fun _ => id)⟩ : ZFSet.ZFBool) = ⊤ := by
      rw [Subtype.mk.injEq]
      exact hsInter
    rw [hsBool, ZFSet.ZFBool.not_true_eq_false] at hnot
    have hnot' : zffalse = zftrue := congrArg Subtype.val hnot
    exact ZFSet.zftrue_ne_zffalse hnot'.symm
  have hFx_bool : F x ∈ 𝔹 := hbool x hx
  rw [ZFSet.ZFBool.mem_𝔹_iff] at hFx_bool
  rcases hFx_bool with hFx_false | hFx_true
  · exact False.elim (hnot_false hFx_false)
  · exact hFx_true

theorem defaultSpecMSpec.{u} :
    ∀ («Δ» : RenamingContext.Context.{u})
      {τ : SMTType} {Γ : TypeContext} {n : ℕ} {used : List 𝒱} {name : String} {t : Term}
      (typ_t : Γ ⊢ˢ t : τ)
      (ht : RenamingContext.CoversFV «Δ» t),
      ⦃fun st =>
        match st with
        | { env := E, types := Γ' } =>
          ⌜Γ' = Γ ∧ E.freshvarsc = n ∧ AList.keys Γ' ⊆ E.usedVars ∧ E.usedVars = used⌝⦄
        defaultSpecM name τ t ⦃PostCond.mayThrow fun spec st' =>
          match st' with
          | { env := E', types := Γ'' } =>
            ⌜n ≤ E'.freshvarsc ∧
                Γ ⊆ Γ'' ∧
                used ⊆ E'.usedVars ∧
                AList.keys Γ'' ⊆ E'.usedVars ∧
                (∀ v ∈ used, v ∉ Γ → v ∉ Γ'') ∧
                Γ'' ⊢ˢ spec : SMTType.bool ∧
                fv spec ⊆ fv t ∧
                ∀ («Δ₀» : RenamingContext.Context.{u})
                  (ht₀ : RenamingContext.CoversFV «Δ₀» t)
                  (Y : SMT.Dom.{u}),
                  ⟦t.abstract «Δ₀» ht₀⟧ˢ = some Y →
                    ∃ (hφ : RenamingContext.CoversFV «Δ₀» spec) (Φ : SMT.Dom.{u}),
                      ⟦spec.abstract «Δ₀» hφ⟧ˢ = some Φ ∧
                        Φ.snd.fst = SMTType.bool ∧
                        (Y.fst = τ.defaultZFSet → Φ.fst = zftrue)⌝⦄ := by
  intro «Δ» τ Γ n used name t typ_t ht
  induction τ generalizing «Δ» Γ n used name t with
  | int =>
      mintro pre ∀St₁
      mpure pre
      obtain ⟨rfl, rfl, sub, rfl⟩ := pre
      unfold defaultSpecM
      mspec Std.Do.Spec.pure
      mpure_intro
      and_intros
      · exact Nat.le_refl _
      · intro v hv
        exact hv
      · intro v hv
        exact hv
      · exact sub
      · intro v hv hv_not; exact hv_not
      · exact SMT.Typing.eq _ _ _ _ typ_t (SMT.Typing.int _ _)
      · intro v hv
        simpa [fv] using hv
      · intro «Δ₀» ht₀ Y den_t
        have hφ : RenamingContext.CoversFV «Δ₀» (t =ˢ .int 0) := by
          intro v hv
          simp [SMT.fv] at hv
          exact ht₀ v hv
        have hden_zero :
            ⟦(.int 0 : Term).abstract «Δ₀» (by
                intro v hv
                simp [fv] at hv)⟧ˢ =
              some ⟨ZFSet.ofInt 0, .int, ZFSet.mem_ofInt_Int 0⟩ := by
          rw [SMT.Term.abstract, SMT.denote, Option.pure_def]
        by_cases hdef : Y.fst = SMTType.int.defaultZFSet
        · refine ⟨hφ, ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩, ?_, rfl, ?_⟩
          · simpa [SMT.Term.abstract, SMTType.defaultZFSet] using
              (denote_eq_eq_zftrue_of_fst_eq den_t hden_zero
                (denote_type_eq_of_typing (typ_t := typ_t) (hden := den_t)) hdef)
          · intro
            rfl
        · obtain ⟨Φ, hdenΦ, hΦ_ty⟩ := denote_eq_some_of_some den_t hden_zero
            (denote_type_eq_of_typing (typ_t := typ_t) (hden := den_t))
          exact ⟨hφ, Φ, by simpa [SMT.Term.abstract] using hdenΦ, hΦ_ty, fun h => (hdef h).elim⟩
  | bool =>
      mintro pre ∀St₁
      mpure pre
      obtain ⟨rfl, rfl, sub, rfl⟩ := pre
      unfold defaultSpecM
      mspec Std.Do.Spec.pure
      mpure_intro
      and_intros
      · exact Nat.le_refl _
      · intro v hv
        exact hv
      · intro v hv
        exact hv
      · exact sub
      · intro v hv hv_not; exact hv_not
      · exact SMT.Typing.eq _ _ _ _ typ_t (SMT.Typing.bool _ false)
      · intro v hv
        simpa [fv] using hv
      · intro «Δ₀» ht₀ Y den_t
        have hφ : RenamingContext.CoversFV «Δ₀» (t =ˢ .bool false) := by
          intro v hv
          simp [SMT.fv] at hv
          exact ht₀ v hv
        have hden_false :
            ⟦(.bool false : Term).abstract «Δ₀» (by
                intro v hv
                simp [fv] at hv)⟧ˢ =
              some ⟨zffalse, .bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
          rw [SMT.Term.abstract, SMT.denote, Option.pure_def]
          rfl
        by_cases hdef : Y.fst = SMTType.bool.defaultZFSet
        · refine ⟨hφ, ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩, ?_, rfl, ?_⟩
          · simpa [SMT.Term.abstract, SMTType.defaultZFSet] using
              (denote_eq_eq_zftrue_of_fst_eq den_t hden_false
                (denote_type_eq_of_typing (typ_t := typ_t) (hden := den_t)) hdef)
          · intro
            rfl
        · obtain ⟨Φ, hdenΦ, hΦ_ty⟩ := denote_eq_some_of_some den_t hden_false
            (denote_type_eq_of_typing (typ_t := typ_t) (hden := den_t))
          exact ⟨hφ, Φ, by simpa [SMT.Term.abstract] using hdenΦ, hΦ_ty, fun h => (hdef h).elim⟩
  | unit =>
      mintro pre ∀St₁
      mpure pre
      obtain ⟨rfl, rfl, sub, rfl⟩ := pre
      unfold defaultSpecM
      mspec Std.Do.Spec.pure
      mpure_intro
      and_intros
      · exact Nat.le_refl _
      · intro v hv
        exact hv
      · intro v hv
        exact hv
      · exact sub
      · intro v hv hv_not; exact hv_not
      · exact SMT.Typing.bool _ true
      · intro v hv
        simpa [fv] using hv
      · intro «Δ₀» ht₀ Y den_t
        refine ⟨?_, ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩, ?_, rfl, ?_⟩
        · intro v hv
          simp [fv] at hv
        · rw [SMT.Term.abstract, SMT.denote, Option.pure_def]
          rfl
        · intro _
          rfl
  | option τ ih =>
      mintro pre ∀St₁
      mpure pre
      obtain ⟨rfl, rfl, sub, rfl⟩ := pre
      unfold defaultSpecM
      mspec Std.Do.Spec.pure
      mpure_intro
      and_intros
      · exact Nat.le_refl _
      · intro v hv
        exact hv
      · intro v hv
        exact hv
      · exact sub
      · intro v hv hv_not; exact hv_not
      · exact SMT.Typing.eq _ _ _ _ typ_t (SMT.Typing.none _ _)
      · intro v hv
        simpa [noneCast, SMT.fv] using hv
      · intro «Δ₀» ht₀ Y den_t
        have hφ : RenamingContext.CoversFV «Δ₀» (t =ˢ none$τ) := by
          intro v hv
          exact ht₀ v (by simpa [noneCast, SMT.fv] using hv)
        have hden_none :
            ⟦(none$τ).abstract «Δ₀» (by
                intro v hv
                simpa [noneCast, SMT.fv] using hv)⟧ˢ =
              some ⟨(SMTType.option τ).defaultZFSet, SMTType.option τ, SMTType.mem_toZFSet_of_defaultZFSet⟩ := by
          simpa [noneCast, SMTType.defaultZFSet, SMT.Term.abstract, SMT.denote]
        by_cases hdef : Y.fst = (SMTType.option τ).defaultZFSet
        · refine ⟨hφ, ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩, ?_, rfl, ?_⟩
          · simpa [SMT.Term.abstract] using
              (denote_eq_eq_zftrue_of_fst_eq den_t hden_none
                (denote_type_eq_of_typing (typ_t := typ_t) (hden := den_t)) hdef)
          · intro
            rfl
        · obtain ⟨Φ, hdenΦ, hΦ_ty⟩ := denote_eq_some_of_some den_t hden_none
            (denote_type_eq_of_typing (typ_t := typ_t) (hden := den_t))
          exact ⟨hφ, Φ, by simpa [SMT.Term.abstract] using hdenΦ, hΦ_ty, fun h => (hdef h).elim⟩
  | pair α β ihα ihβ =>
      unfold defaultSpecM
      have typ_fst : Γ ⊢ˢ .fst t : α := by
        exact SMT.Typing.fst _ _ _ _ typ_t
      have ht_fst : RenamingContext.CoversFV «Δ» (.fst t) := by
        intro v hv
        exact ht v (by simpa [SMT.fv] using hv)
      let Qfst :
          Term →
            Std.Do.Assertion
              (Std.Do.PostShape.arg EncoderState (Std.Do.PostShape.except String Std.Do.PostShape.pure)) :=
        fun hfst (st : EncoderState) =>
        match st with
        | { env := E', types := Γ'' } =>
          Std.Do.SPred.pure
            (n ≤ E'.freshvarsc ∧
              Γ ⊆ Γ'' ∧
              used ⊆ E'.usedVars ∧
              AList.keys Γ'' ⊆ E'.usedVars ∧
              (∀ v ∈ used, v ∉ Γ → v ∉ Γ'') ∧
              Γ'' ⊢ˢ hfst : SMTType.bool ∧
              fv hfst ⊆ fv (Term.fst t) ∧
              ∀ («Δ₀» : RenamingContext.Context)
                (ht₀ : RenamingContext.CoversFV «Δ₀» (Term.fst t))
                (Y : SMT.Dom),
                ⟦(Term.fst t).abstract «Δ₀» ht₀⟧ˢ = some Y →
                  ∃ (hφ : RenamingContext.CoversFV «Δ₀» hfst) (Φ : SMT.Dom),
                    ⟦hfst.abstract «Δ₀» hφ⟧ˢ = some Φ ∧
                      Φ.snd.fst = SMTType.bool ∧
                      (Y.fst = α.defaultZFSet → Φ.fst = zftrue))
      refine Std.Do.Triple.bind
        (Q := Qfst)
        (x := defaultSpecM s!"{name}_fst" α (.fst t))
        (f := fun hfst => do
          let hsnd ← defaultSpecM s!"{name}_snd" β (.snd t)
          pure (hfst ∧ˢ hsnd))
        ?_ ?_
      · exact ihα
          «Δ»
          (Γ := Γ) (n := n) (used := used)
          (name := s!"{name}_fst") (t := .fst t) typ_fst ht_fst
      · intro hfst
        mintro pre ∀St₂
        mpure pre
        obtain ⟨hn₂, sub₂, used₂, keys₂, preserves₂, typ_hfst, fv_hfst, den_hfst⟩ := pre
        have typ_t_St₂ : St₂.types ⊢ˢ t : α.pair β := by
          exact SMT.Typing.weakening (h := sub₂) typ_t
        have typ_snd : St₂.types ⊢ˢ .snd t : β := by
          exact SMT.Typing.snd _ _ _ _ typ_t_St₂
        have ht_snd : RenamingContext.CoversFV «Δ» (.snd t) := by
          intro v hv
          exact ht v (by simpa [SMT.fv] using hv)
        have ihβ_snd := ihβ
          «Δ»
          (Γ := St₂.types) (n := St₂.env.freshvarsc) (used := St₂.env.usedVars)
          (name := s!"{name}_snd") (t := .snd t) typ_snd ht_snd
        let Qraw : Std.Do.PostCond Term
            (Std.Do.PostShape.arg EncoderState (Std.Do.PostShape.except String Std.Do.PostShape.pure)) :=
          Std.Do.PostCond.mayThrow fun hsnd st =>
            match st with
            | { env := E', types := Γ'' } =>
              Std.Do.SPred.pure
                (St₂.env.freshvarsc ≤ E'.freshvarsc ∧
                  St₂.types ⊆ Γ'' ∧
                  St₂.env.usedVars ⊆ E'.usedVars ∧
                  AList.keys Γ'' ⊆ E'.usedVars ∧
                  (∀ v ∈ St₂.env.usedVars, v ∉ St₂.types → v ∉ Γ'') ∧
                  Γ'' ⊢ˢ hsnd : SMTType.bool ∧
                  fv hsnd ⊆ fv (Term.snd t) ∧
                  ∀ («Δ₀» : RenamingContext.Context)
                    (ht₀ : RenamingContext.CoversFV «Δ₀» (Term.snd t))
                    (Y : SMT.Dom),
                    ⟦(Term.snd t).abstract «Δ₀» ht₀⟧ˢ = some Y →
                      ∃ (hφ : RenamingContext.CoversFV «Δ₀» hsnd) (Φ : SMT.Dom),
                        ⟦hsnd.abstract «Δ₀» hφ⟧ˢ = some Φ ∧
                          Φ.snd.fst = SMTType.bool ∧
                          (Y.fst = β.defaultZFSet → Φ.fst = zftrue))
        let Qneed : Std.Do.PostCond Term
            (Std.Do.PostShape.arg EncoderState (Std.Do.PostShape.except String Std.Do.PostShape.pure)) :=
          Std.Do.PostCond.mayThrow fun hsnd st =>
            match st with
            | { env := E', types := Γ'' } =>
              Std.Do.SPred.pure
                (n ≤ E'.freshvarsc ∧
                  Γ ⊆ Γ'' ∧
                  used ⊆ E'.usedVars ∧
                  AList.keys Γ'' ⊆ E'.usedVars ∧
                  (∀ v ∈ used, v ∉ Γ → v ∉ Γ'') ∧
                  Γ'' ⊢ˢ (hfst ∧ˢ hsnd) : SMTType.bool ∧
                  fv (hfst ∧ˢ hsnd) ⊆ fv t ∧
                  ∀ («Δ₀» : RenamingContext.Context)
                    (ht₀ : RenamingContext.CoversFV «Δ₀» t)
                    (Y : SMT.Dom),
                    ⟦t.abstract «Δ₀» ht₀⟧ˢ = some Y →
                      ∃ (hφ : RenamingContext.CoversFV «Δ₀» (hfst ∧ˢ hsnd)) (Φ : SMT.Dom),
                        ⟦(hfst ∧ˢ hsnd).abstract «Δ₀» hφ⟧ˢ = some Φ ∧
                          Φ.snd.fst = SMTType.bool ∧
                          (Y.fst = (α.pair β).defaultZFSet → Φ.fst = zftrue))
        rw [Std.Do.WP.bind]
        simp only [Std.Do.WP.pure]
        have hraw_at :
            (wp⟦defaultSpecM s!"{name}_snd" β (.snd t)⟧ Qraw St₂).down :=
          ihβ_snd St₂ (by refine ⟨rfl, rfl, keys₂, rfl⟩)
        have hpost : Qraw ⊢ₚ Qneed := by
          rw [Std.Do.PostCond.entails_mayThrow]
          intro hsnd
          mintro pre ∀St₃
          mpure pre
          obtain ⟨hn₃, sub₃, used₃, keys₃, preserves₃, typ_hsnd, fv_hsnd, den_hsnd⟩ := pre
          mpure_intro
          and_intros
          · exact hn₂.trans hn₃
          · intro v hv
            exact sub₃ (sub₂ hv)
          · intro v hv
            exact used₃ (used₂ hv)
          · exact keys₃
          · intro v hv hv_not
            exact preserves₃ v (used₂ hv) (preserves₂ v hv hv_not)
          · have typ_hfst_St₃ : St₃.types ⊢ˢ hfst : SMTType.bool := by
              exact SMT.Typing.weakening (h := sub₃) typ_hfst
            exact SMT.Typing.and _ _ _ typ_hfst_St₃ typ_hsnd
          · intro v hv
            rcases (by simpa [SMT.fv, List.mem_append] using hv) with hv | hv
            · simpa [SMT.fv] using fv_hfst hv
            · simpa [SMT.fv] using fv_hsnd hv
          · intro «Δ₀» ht₀ Y den_t
            have ht_fst₀ : RenamingContext.CoversFV «Δ₀» (Term.fst t) := by
              intro v hv
              exact ht₀ v (by simpa [SMT.fv] using hv)
            have ht_snd₀ : RenamingContext.CoversFV «Δ₀» (Term.snd t) := by
              intro v hv
              exact ht₀ v (by simpa [SMT.fv] using hv)
            have hY_ty : Y.snd.fst = α.pair β :=
              denote_type_eq_of_typing (typ_t := typ_t) (hden := den_t)
            have hY_mem : Y.fst ∈ ⟦α.pair β⟧ᶻ := by
              simpa [hY_ty] using Y.snd.snd
            have hY_prod : Y.fst ∈ ⟦α⟧ᶻ.prod ⟦β⟧ᶻ := by
              simpa [SMTType.toZFSet] using hY_mem
            rw [ZFSet.pair_eta hY_prod, ZFSet.pair_mem_prod] at hY_prod
            let Yfst : SMT.Dom := ⟨Y.fst.π₁, α, hY_prod.1⟩
            let Ysnd : SMT.Dom := ⟨Y.fst.π₂, β, hY_prod.2⟩
            have hden_fst_t : ⟦(Term.fst t).abstract «Δ₀» ht_fst₀⟧ˢ = some Yfst := by
              cases Y with
              | mk y hy =>
                cases hy with
                | mk τ hy =>
                  cases hY_ty
                  rw [SMT.Term.abstract.eq_def, SMT.denote, den_t]
                  dsimp [Yfst]
            have hden_snd_t : ⟦(Term.snd t).abstract «Δ₀» ht_snd₀⟧ˢ = some Ysnd := by
              cases Y with
              | mk y hy =>
                cases hy with
                | mk τ hy =>
                  cases hY_ty
                  rw [SMT.Term.abstract.eq_def, SMT.denote, den_t]
                  dsimp [Ysnd]
            obtain ⟨hφfst, Φfst, hdenΦfst, hΦfst_ty, hΦfst_def⟩ := den_hfst «Δ₀» ht_fst₀ Yfst hden_fst_t
            obtain ⟨hφsnd, Φsnd, hdenΦsnd, hΦsnd_ty, hΦsnd_def⟩ := den_hsnd «Δ₀» ht_snd₀ Ysnd hden_snd_t
            have hφ : RenamingContext.CoversFV «Δ₀» (hfst ∧ˢ hsnd) := by
              intro v hv
              rcases (by simpa [SMT.fv, List.mem_append] using hv) with hv | hv
              · exact hφfst v hv
              · exact hφsnd v hv
            by_cases hdef : Y.fst = (α.pair β).defaultZFSet
            · have hdef_fst : Yfst.fst = α.defaultZFSet := by
                simpa [Yfst, SMTType.defaultZFSet] using congrArg ZFSet.π₁ hdef
              have hdef_snd : Ysnd.fst = β.defaultZFSet := by
                simpa [Ysnd, SMTType.defaultZFSet] using congrArg ZFSet.π₂ hdef
              have hΦfst_true : Φfst.fst = zftrue := hΦfst_def hdef_fst
              have hΦsnd_true : Φsnd.fst = zftrue := hΦsnd_def hdef_snd
              refine ⟨hφ, ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩, ?_, rfl, ?_⟩
              · simpa [SMT.Term.abstract] using
                  (denote_and_eq_zftrue_of_some_zftrue
                    hdenΦfst hΦfst_ty hΦfst_true
                    hdenΦsnd hΦsnd_ty hΦsnd_true)
              · intro _
                rfl
            · obtain ⟨Φ, hdenΦ, hΦ_ty⟩ := denote_and_some_bool_of_some_bool
                hdenΦfst hΦfst_ty hdenΦsnd hΦsnd_ty
              exact ⟨hφ, Φ, by simpa [SMT.Term.abstract] using hdenΦ, hΦ_ty, fun h => (hdef h).elim⟩
        simpa [Std.Do.PostCond.mayThrow] using
          (((Std.Do.wp (defaultSpecM s!"{name}_snd" β (.snd t))).mono
            Qraw
            (Std.Do.PostCond.mayThrow fun hsnd st =>
              match st with
              | { env := E', types := Γ'' } =>
                Std.Do.SPred.pure
                  (n ≤ E'.freshvarsc ∧
                    Γ ⊆ Γ'' ∧
                    used ⊆ E'.usedVars ∧
                    AList.keys Γ'' ⊆ E'.usedVars ∧
                    (∀ v ∈ used, v ∉ Γ → v ∉ Γ'') ∧
                    Γ'' ⊢ˢ (hfst ∧ˢ hsnd) : SMTType.bool ∧
                    fv (hfst ∧ˢ hsnd) ⊆ fv t ∧
                    ∀ («Δ₀» : RenamingContext.Context)
                      (ht₀ : RenamingContext.CoversFV «Δ₀» t)
                      (Y : SMT.Dom),
                      ⟦t.abstract «Δ₀» ht₀⟧ˢ = some Y →
                        ∃ (hφ : RenamingContext.CoversFV «Δ₀» (hfst ∧ˢ hsnd)) (Φ : SMT.Dom),
                          ⟦(hfst ∧ˢ hsnd).abstract «Δ₀» hφ⟧ˢ = some Φ ∧
                            Φ.snd.fst = SMTType.bool ∧
                            (Y.fst = (α.pair β).defaultZFSet → Φ.fst = zftrue))
            )
            (by simpa [Qneed] using hpost)) St₂ hraw_at)

  | «fun» α β ihα ihβ =>
      mintro pre ∀St₁
      mpure pre
      obtain ⟨rfl, rfl, sub, rfl⟩ := pre
      unfold defaultSpecM
      mspec SMT.freshVar_spec (Γ := St₁.types) (n := St₁.env.freshvarsc) (used := St₁.env.usedVars)
      next x =>
        mrename_i pre
        mintro ∀St₂
        mcases pre with ⟨St₂_types_eq, x_fresh, St₂_fvc, St₂_used_eq, x_not_used⟩
        have typ_t_St₂ : St₂.types ⊢ˢ t : α.fun β := by
          rw [St₂_types_eq]
          exact SMT.Typing.weakening
            (h := SMT.TypeContext.entries_subset_insert_of_notMem x_fresh)
            typ_t
        have typ_var_x_St₂ : St₂.types ⊢ˢ .var x : α := by
          apply SMT.Typing.var
          rw [St₂_types_eq]
          exact AList.lookup_insert St₁.types
        have typ_app_St₂ : St₂.types ⊢ˢ .app t (.var x) : β := by
          exact SMT.Typing.app
            (Γ := St₂.types) (f := t) (x := .var x) (τ := α) (σ := β)
            typ_t_St₂ typ_var_x_St₂
        have keys₂ : AList.keys St₂.types ⊆ St₂.env.usedVars := by
          rw [St₂_types_eq, St₂_used_eq, AList.keys_insert]
          intro v hv
          rw [List.mem_cons] at hv ⊢
          rcases hv with rfl | hv
          · exact Or.inl rfl
          · exact Or.inr (sub (List.mem_of_mem_erase hv))
        let Xdef : SMT.Dom := ⟨α.defaultZFSet, α, SMTType.mem_toZFSet_of_defaultZFSet⟩
        let Δd : RenamingContext.Context := Function.update «Δ» x (some Xdef)
        have ht_app_d : RenamingContext.CoversFV Δd (.app t (.var x)) := by
          intro v hv
          simp [SMT.fv] at hv
          rcases hv with hv | hv
          · by_cases hvx : v = x
            · subst hvx
              simp [Δd]
            · simpa [Δd, Function.update, hvx] using ht v hv
          · subst hv
            simp [Δd]
        have ihβ_body := ihβ
          Δd
          (Γ := St₂.types) (n := St₂.env.freshvarsc) (used := St₂.env.usedVars)
          (name := s!"{name}_body") (t := .app t (.var x)) typ_app_St₂ ht_app_d
        let Qraw : Std.Do.PostCond Term
            (Std.Do.PostShape.arg EncoderState (Std.Do.PostShape.except String Std.Do.PostShape.pure)) :=
          Std.Do.PostCond.mayThrow fun a st =>
            match st with
            | { env := E', types := Γ'' } =>
              Std.Do.SPred.pure
                (St₂.env.freshvarsc ≤ E'.freshvarsc ∧
                  St₂.types ⊆ Γ'' ∧
                  St₂.env.usedVars ⊆ E'.usedVars ∧
                  AList.keys Γ'' ⊆ E'.usedVars ∧
                  (∀ v ∈ St₂.env.usedVars, v ∉ St₂.types → v ∉ Γ'') ∧
                  Γ'' ⊢ˢ a : SMTType.bool ∧
                  fv a ⊆ fv (Term.app t (.var x)) ∧
                  ∀ (Δ₀ : RenamingContext.Context)
                    (ht₀ : RenamingContext.CoversFV Δ₀ (Term.app t (.var x)))
                    (Y : SMT.Dom),
                    ⟦(Term.app t (.var x)).abstract Δ₀ ht₀⟧ˢ = some Y →
                      ∃ (hφ : RenamingContext.CoversFV Δ₀ a) (Φ : SMT.Dom),
                        ⟦a.abstract Δ₀ hφ⟧ˢ = some Φ ∧
                          Φ.snd.fst = SMTType.bool ∧
                          (Y.fst = β.defaultZFSet → Φ.fst = zftrue))
        let Qneed : Std.Do.PostCond Term
            (Std.Do.PostShape.arg EncoderState (Std.Do.PostShape.except String Std.Do.PostShape.pure)) :=
          Std.Do.PostCond.mayThrow fun a st =>
            match st with
            | { env := E', types := Γ'' } =>
              Std.Do.SPred.pure
                (St₁.env.freshvarsc ≤ E'.freshvarsc ∧
                  St₁.types ⊆ Γ'' ∧
                  St₁.env.usedVars ⊆ E'.usedVars ∧
                  AList.keys Γ'' ⊆ E'.usedVars ∧
                  (∀ v ∈ St₁.env.usedVars, v ∉ St₁.types → v ∉ Γ'') ∧
                  Γ'' ⊢ˢ Term.forall [x] [α] a : .bool ∧
                  fv (Term.forall [x] [α] a) ⊆ fv t ∧
                  ∀ (Δ₀ : RenamingContext.Context)
                    (ht₀ : RenamingContext.CoversFV Δ₀ t)
                    (Y : SMT.Dom),
                    ⟦t.abstract Δ₀ ht₀⟧ˢ = some Y →
                      ∃ (hφ : RenamingContext.CoversFV Δ₀ (Term.forall [x] [α] a)) (Φ : SMT.Dom),
                        ⟦(Term.forall [x] [α] a).abstract Δ₀ hφ⟧ˢ = some Φ ∧
                          Φ.snd.fst = SMTType.bool ∧
                          (Y.fst = (α.fun β).defaultZFSet → Φ.fst = zftrue))
        rw [Std.Do.WP.bind]
        simp only [Std.Do.WP.pure]
        have hraw_at := ihβ_body St₂ (by
          refine ⟨rfl, rfl, keys₂, rfl⟩)
        have hpost : Qraw ⊢ₚ Qneed := by
          rw [Std.Do.PostCond.entails_mayThrow]
          intro a
          mintro pre ∀St₃
          mpure pre
          obtain ⟨hn₃, sub₃, used₃, keys₃, preserves₃, typ_a, fv_a, den_a⟩ := pre
          have typ_a_St₂ : St₂.types ⊢ˢ a : SMTType.bool := by
            apply SMT.Typing.strengthening_of_fv_subset sub₃ typ_a
            intro v hv
            have hv' := fv_a hv
            simp only [fv, List.mem_append, List.mem_singleton] at hv'
            rcases hv' with hv_t | hv_x
            · exact SMT.Typing.mem_context_of_mem_fv typ_t_St₂ hv_t
            · subst hv_x
              rw [St₂_types_eq, AList.mem_insert]
              exact Or.inl rfl
          mpure_intro
          and_intros
          · calc
              St₁.env.freshvarsc ≤ St₂.env.freshvarsc := by
                rw [St₂_fvc]
                exact Nat.le_succ _
              _ ≤ St₃.env.freshvarsc := hn₃
          · intro v hv
            exact sub₃ (by rw [St₂_types_eq]; exact SMT.TypeContext.entries_subset_insert_of_notMem x_fresh hv)
          · intro v hv
            exact used₃ (by rw [St₂_used_eq]; exact List.mem_cons_of_mem _ hv)
          · exact keys₃
          · intro v hv hv_not
            have hv_ne_x : v ≠ x := fun h => absurd hv (h ▸ x_not_used)
            have hv_not_St₂ : v ∉ St₂.types := by
              rw [St₂_types_eq, AList.mem_insert]; push_neg; exact ⟨hv_ne_x, hv_not⟩
            exact preserves₃ v (by rw [St₂_used_eq]; exact List.mem_cons_of_mem _ hv) hv_not_St₂
          · have typ_forall_base :
                St₁.types ⊢ˢ Term.forall [x] [α] a : SMTType.bool := by
              refine SMT.Typing.forall St₁.types [x] [α] a ?_ ?_ ?_ ?_ ?_
              · intro v hvv hvΓ
                rw [List.mem_singleton] at hvv
                subst hvv
                exact x_fresh hvΓ
              · intro v hvv hvb
                have hxv : v = x := by
                  simpa [List.mem_singleton] using hvv
                have hv_mem_St₂ : v ∈ St₂.types := by
                  rw [hxv, St₂_types_eq, AList.mem_insert]
                  exact Or.inl rfl
                exact SMT.Typing.bv_notMem_context typ_a_St₂ _ hvb hv_mem_St₂
              · simp
              · simp
              · have hupd : St₁.types.update [x] [α] rfl = AList.insert x α St₁.types := by
                  simp only [SMT.TypeContext.update, List.length_cons, List.length_nil, zero_add,
                    Fin.foldl_succ, Nat.reduceAdd, Fin.cast_eq_self, Fin.getElem_fin,
                    Fin.val_eq_zero, List.getElem_cons_zero, Fin.isValue, Fin.foldl_zero]
                rw [hupd]
                simpa [St₂_types_eq] using typ_a_St₂
            exact SMT.Typing.weakening
              (h := by
                intro v hv
                exact sub₃ (by
                  rw [St₂_types_eq]
                  exact SMT.TypeContext.entries_subset_insert_of_notMem x_fresh hv))
              typ_forall_base
          · intro v hv
            simp only [fv, List.mem_removeAll_iff, List.mem_cons, List.not_mem_nil, or_false] at hv
            obtain ⟨hv_a, hxv⟩ := hv
            have hv' := fv_a hv_a
            simp only [fv, List.mem_append, List.mem_singleton] at hv'
            rcases hv' with hv_t | hv_x
            · exact hv_t
            · exact (hxv hv_x).elim
          · intro Δ₀ ht₀ Y den_t
            have x_not_mem_fv_t : x ∉ fv t := by
              intro hx_mem
              exact x_fresh (SMT.Typing.mem_context_of_mem_fv typ_t hx_mem)
            have hY_ty : Y.snd.fst = α.fun β :=
              denote_type_eq_of_typing (typ_t := typ_t) (hden := den_t)
            have hY_func : ZFSet.IsFunc ⟦α⟧ᶻ ⟦β⟧ᶻ Y.fst := by
              rw [←ZFSet.mem_funs]
              simpa [hY_ty] using Y.snd.snd
            have hcov_t_upd (Xarg : SMT.Dom) :
                RenamingContext.CoversFV (Function.update Δ₀ x (some Xarg)) t :=
              SMT.RenamingContext.coversFV_update_of_notMem
                (x := x) (d := Xarg) x_not_mem_fv_t ht₀
            have den_t_upd (Xarg : SMT.Dom) :
                ⟦t.abstract (Function.update Δ₀ x (some Xarg)) (hcov_t_upd Xarg)⟧ˢ = some Y := by
              calc
                ⟦t.abstract (Function.update Δ₀ x (some Xarg)) (hcov_t_upd Xarg)⟧ˢ =
                    SMT.RenamingContext.denote (Function.update Δ₀ x (some Xarg)) t
                      (hcov_t_upd Xarg) := by
                      rfl
                _ = SMT.RenamingContext.denote Δ₀ t ht₀ := by
                      simpa [SMT.RenamingContext.denote] using
                        (SMT.RenamingContext.denote_update_of_notMem
                          («Δ» := Δ₀) (t := t) (x := x) (d := Xarg)
                          (h := ht₀) x_not_mem_fv_t).symm
                _ = some Y := den_t
            have hcov_a_upd (Xarg : SMT.Dom) :
                RenamingContext.CoversFV (Function.update Δ₀ x (some Xarg)) a := by
              intro v hv
              have hv' := fv_a hv
              simp only [fv, List.mem_append, List.mem_singleton] at hv'
              rcases hv' with hv_t | hv_x
              · by_cases hvx : v = x
                · subst hvx
                  simp
                · rw [Function.update_of_ne hvx]
                  exact ht₀ v hv_t
              · subst hv_x
                simp
            have hgo_cov :
                ∀ v ∈ fv a, v ∉ [x] → (Δ₀ v).isSome = true := by
              intro v hv hv_not_x
              have hv' := fv_a hv
              simp only [fv, List.mem_append, List.mem_singleton] at hv'
              rcases hv' with hv_t | hv_x
              · exact ht₀ v hv_t
              · have hv_mem_x : v ∈ [x] := by
                  simpa [List.mem_singleton] using hv_x
                exact (hv_not_x hv_mem_x).elim
            have hφ : RenamingContext.CoversFV Δ₀ (Term.forall [x] [α] a) := by
              intro v hv
              simp only [fv, List.mem_removeAll_iff, List.mem_cons, List.not_mem_nil, or_false] at hv
              obtain ⟨hv_a, hxv⟩ := hv
              have hv' := fv_a hv_a
              simp only [fv, List.mem_append, List.mem_singleton] at hv'
              rcases hv' with hv_t | hv_x
              · exact ht₀ v hv_t
              · exact (hxv hv_x).elim
            have hgo_forall
                (w : Fin [x].length → SMT.Dom)
                (hw : ∀ i, (w i).snd.fst = [α][i] ∧ (w i).fst ∈ ⟦[α][i]⟧ᶻ) :
                (Term.abstract.go a [x] Δ₀ hgo_cov).uncurry w =
                  a.abstract (Function.update Δ₀ x (some (w ⟨0, by simp⟩)))
                    (hcov_a_upd (w ⟨0, by simp⟩)) := by
              have hgo := SMT.Term.abstract.go.alt_def₂
                (vs := [x]) (P := a) (Δctx := Δ₀)
                (αs := List.ofFn w) (vs_αs_len := by simp)
                (Δ_isSome := hgo_cov)
                (tmp₁ := by
                  intro v hv
                  by_cases hvx : v ∈ [x]
                  · exact Function.updates_isSome_of_mem_map_some Δ₀ [x] (List.ofFn w) v hvx (by simp)
                  · rw [Function.updates_of_not_mem
                      (f := Δ₀)
                      (xs := [x]) (ys := (List.ofFn w).map Option.some) (k := v) hvx]
                    exact hgo_cov v hv (by simpa using hvx))
              have h_ofFn_list : List.ofFn w = [w ⟨0, by simp⟩] := by
                simpa using (List.ofFn_succ' (n := 0) w)
              have h_ofFn :
                  (fun i =>
                    match i with
                    | ⟨j, _⟩ => (List.ofFn w)[j]) = w := by
                funext i
                cases i with
                | mk j hj =>
                    simp at hj
                    have hj0 : j = 0 := hj
                    subst hj0
                    simp [h_ofFn_list]
              simpa [h_ofFn, Function.updates] using hgo
            have hbody_total :
                ∀ {x_1 : Fin [x].length → SMT.Dom},
                  (∀ i, (x_1 i).snd.fst = [α][i] ∧ (x_1 i).fst ∈ ⟦[α][i]⟧ᶻ) →
                    ⟦(Term.abstract.go a [x] Δ₀ hgo_cov).uncurry x_1⟧ˢ.isSome = true := by
              intro x_1 hx_1
              let Xarg : SMT.Dom := x_1 ⟨0, by simp⟩
              have hXarg_ty : Xarg.snd.fst = α := by
                simpa [Xarg] using (hx_1 ⟨0, by simp⟩).1
              have hXarg_mem : Xarg.fst ∈ ⟦α⟧ᶻ := by
                simpa [Xarg] using (hx_1 ⟨0, by simp⟩).2
              obtain ⟨hcov_app, Dapp, hDapp_ty, hDapp_val, hden_app⟩ :=
                defaultSpecMFunDenoteAppAt
                  (hcov_t_upd := hcov_t_upd) (den_t_upd := den_t_upd)
                  (hY_ty := hY_ty) (hY_func := hY_func)
                  Xarg hXarg_ty hXarg_mem
              obtain ⟨hφa, Dspec, hden_spec, hDspec_ty, hDspec_def⟩ :=
                den_a (Function.update Δ₀ x (some Xarg)) hcov_app Dapp hden_app
              rw [hgo_forall x_1 hx_1]
              exact Option.isSome_of_eq_some hden_spec
            have hbody_total' :
                ∀ {x_1 : Fin [x].length → SMT.Dom},
                  (∀ i,
                    ((x_1 i).snd.fst =
                        match i with
                        | ⟨i, hi⟩ => [α][i]) ∧
                      (x_1 i).fst ∈
                        ⟦match i with
                          | ⟨i, hi⟩ => [α][i]⟧ᶻ) →
                    ⟦(Term.abstract.go a [x] Δ₀ hgo_cov).uncurry x_1⟧ˢ.isSome = true := by
              intro x_1 hx_1
              exact hbody_total (by
                intro i
                have hi0 : i = ⟨0, by simp⟩ := by
                  apply Fin.ext
                  simp
                cases hi0
                simpa using hx_1 ⟨0, by simp⟩)
            have hlen_forall : [x].length > 0 := by
              simp
            let Φ : SMT.Dom :=
              ⟨⋂₀
                (ZFSet.sep
                  (fun y =>
                    ∃ x_1 ∈ ⟦α⟧ᶻ,
                      y =
                        if h : x_1.hasArity 1 ∧ x_1 ∈ ⟦α⟧ᶻ then
                          (⟦(Term.abstract.go a [x] Δ₀ hgo_cov).uncurry
                              (fun _ => ⟨x_1, α, h.2⟩)⟧ˢ.get
                            (hbody_total (by
                              intro i
                              have hi0 : i = ⟨0, by simp⟩ := by
                                apply Fin.ext
                                simp
                              cases hi0
                              exact ⟨rfl, h.2⟩))).fst
                        else zffalse)
                  𝔹 : ZFSet),
                SMTType.bool,
                ZFSet.sInter_sep_subset_of_𝔹_mem_𝔹 (fun _ => id)⟩
            refine ⟨hφ, Φ, ?_, rfl, ?_⟩
            · rw [SMT.Term.abstract, dif_pos (by rfl), SMT.denote]
              rw [dif_pos hlen_forall]
              split_ifs with hsome
              · simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_one_sub_one,
                  List.getElem_cons_succ, Fin.zero_eta, Fin.isValue, Fin.coe_ofNat_eq_mod,
                  Nat.zero_mod, List.getElem_cons_zero, Fin.val_eq_zero, get.eq_1, forall_const,
                  Option.pure_def, Option.failure_eq_none, Option.bind_some, Fin.foldl_zero, Φ]
                let sInterGoal : ZFSet :=
                  ⋂₀
                    ZFSet.sep
                      (fun y =>
                        ∃ x_1 ∈ ⟦α⟧ᶻ,
                          y =
                            if hx : x_1.hasArity 1 ∧ ∀ i : Fin 1, x_1 ∈ ⟦[α][↑i]⟧ᶻ then
                              (⟦(Term.abstract.go a [x] Δ₀ hgo_cov).uncurry
                                  (fun i => ⟨x_1, [α][↑i], hx.2 i⟩)⟧ˢ.get
                                (hsome (by
                                  intro i
                                  exact ⟨rfl, hx.2 i⟩))).fst
                            else zffalse)
                      𝔹
                have hsInter_eq :
                    (⋂₀
                      ZFSet.sep
                        (fun y =>
                          ∃ x_1 ∈ ⟦α⟧ᶻ,
                            y =
                              if hx : x_1.hasArity 1 ∧ ∀ i : Fin 1, x_1 ∈ ⟦[α][↑i]⟧ᶻ then
                                (⟦(Term.abstract.go a [x] Δ₀ hgo_cov).uncurry
                                    (fun i => ⟨x_1, [α][↑i], hx.2 i⟩)⟧ˢ.get
                                  (hsome (by
                                    intro i
                                    exact ⟨rfl, hx.2 i⟩))).fst
                              else zffalse)
                        𝔹 : ZFSet) =
                    (⋂₀
                      ZFSet.sep
                        (fun y =>
                          ∃ x_1 ∈ ⟦α⟧ᶻ,
                            y =
                              if h : x_1.hasArity 1 ∧ x_1 ∈ ⟦α⟧ᶻ then
                                (⟦(Term.abstract.go a [x] Δ₀ hgo_cov).uncurry
                                    (fun _ => ⟨x_1, α, h.2⟩)⟧ˢ.get
                                  (hbody_total (by
                                    intro i
                                    have hi0 : i = ⟨0, by simp⟩ := by
                                      apply Fin.ext
                                      simp
                                    cases hi0
                                    exact ⟨rfl, h.2⟩))).fst
                              else zffalse)
                        𝔹 : ZFSet) := by
                  congr
                  ext y
                  have hbody_eq {x_1 : ZFSet} (hx_1 : x_1 ∈ ⟦α⟧ᶻ) :
                      (if hx : x_1.hasArity 1 ∧ ∀ i : Fin 1, x_1 ∈ ⟦[α][↑i]⟧ᶻ then
                        (⟦(Term.abstract.go a [x] Δ₀ hgo_cov).uncurry
                            (fun i => ⟨x_1, [α][↑i], hx.2 i⟩)⟧ˢ.get
                          (hsome (by
                            intro i
                            exact ⟨rfl, hx.2 i⟩))).fst
                      else zffalse) =
                      (if h : x_1.hasArity 1 ∧ x_1 ∈ ⟦α⟧ᶻ then
                        (⟦(Term.abstract.go a [x] Δ₀ hgo_cov).uncurry
                            (fun _ => ⟨x_1, α, h.2⟩)⟧ˢ.get
                          (hbody_total (by
                            intro i
                            have hi0 : i = ⟨0, by simp⟩ := by
                              apply Fin.ext
                              simp
                            cases hi0
                            exact ⟨rfl, h.2⟩))).fst
                      else zffalse) := by
                    by_cases h : x_1.hasArity 1 ∧ x_1 ∈ ⟦α⟧ᶻ
                    · have hx : x_1.hasArity 1 ∧ ∀ i : Fin 1, x_1 ∈ ⟦[α][↑i]⟧ᶻ := by
                        constructor
                        · exact h.1
                        · intro i
                          have hi0 : i = ⟨0, by simp⟩ := by
                            apply Fin.ext
                            simp
                          cases hi0
                          simpa using h.2
                      simpa [hx, h]
                    · have hx : ¬ (x_1.hasArity 1 ∧ ∀ i : Fin 1, x_1 ∈ ⟦[α][↑i]⟧ᶻ) := by
                        intro hx
                        apply h
                        constructor
                        · exact hx.1
                        · simpa using hx.2 ⟨0, by simp⟩
                      simpa [hx, h]
                  constructor
                  · rintro ⟨x_1, hx_1, hy⟩
                    refine ⟨x_1, ?_, hy.trans (hbody_eq (by simpa [Fin.foldl_zero] using hx_1))⟩
                    simpa [Fin.foldl_zero] using hx_1
                  · rintro ⟨x_1, hx_1, hy⟩
                    refine ⟨x_1, ?_, hy.trans (hbody_eq hx_1).symm⟩
                    simpa [Fin.foldl_zero] using hx_1
                congr
                · conv_lhs =>
                    simp [sInterGoal, Fin.foldl_zero]
                · funext τ
                  conv_lhs =>
                    simp [sInterGoal, Fin.foldl_zero]
                · apply proof_irrel_heq
              · exact (hsome hbody_total').elim
            · intro hdef
              have hsInter_true :
                  (⋂₀
                    ZFSet.sep
                      (fun y =>
                        ∃ x_1 ∈ ⟦α⟧ᶻ,
                          y =
                            if h : x_1.hasArity 1 ∧ x_1 ∈ ⟦α⟧ᶻ then
                              (⟦(Term.abstract.go a [x] Δ₀ hgo_cov).uncurry
                                  (fun _ => ⟨x_1, α, h.2⟩)⟧ˢ.get
                                (hbody_total (by
                                  intro i
                                  have hi0 : i = ⟨0, by simp⟩ := by
                                    apply Fin.ext
                                    simp
                                  cases hi0
                                  exact ⟨rfl, h.2⟩))).fst
                            else zffalse)
                      𝔹 : ZFSet) = zftrue := by
                apply sInter_sep_eq_zftrue_of_forall_eq_zftrue
                · exact ⟨α.defaultZFSet, SMTType.mem_toZFSet_of_defaultZFSet⟩
                · intro x_1 hx_1
                  have hx1 := funUnaryTarget (α := α) hx_1
                  have hx_cast : x_1.hasArity 1 ∧ x_1 ∈ ⟦α⟧ᶻ := by
                    constructor
                    · exact hx1.1
                    · exact hx_1
                  rw [dif_pos hx_cast]
                  let Xarg : SMT.Dom := ⟨x_1, α, hx_1⟩
                  obtain ⟨hcov_app, Dapp, hDapp_ty, hDapp_val, hden_app⟩ :=
                    defaultSpecMFunDenoteAppAt
                      (hcov_t_upd := hcov_t_upd) (den_t_upd := den_t_upd)
                      (hY_ty := hY_ty) (hY_func := hY_func)
                      Xarg rfl hx_1
                  obtain ⟨hφa, Dspec, hden_spec, hDspec_ty, hDspec_def⟩ :=
                    den_a (Function.update Δ₀ x (some Xarg)) hcov_app Dapp hden_app
                  have hDapp_def : Dapp.fst = β.defaultZFSet := by
                    have hYeq_default :
                        Y = ⟨(α.fun β).defaultZFSet, α.fun β,
                          SMTType.mem_toZFSet_of_defaultZFSet⟩ := by
                      cases Y with
                      | mk y hy =>
                      cases hy with
                      | mk τ hy =>
                          cases hY_ty
                          subst hdef
                          congr
                    cases hYeq_default
                    rw [hDapp_val]
                    simpa [Xarg] using defaultZFSetFunApp (α := α) (β := β) hx_1
                  have hDspec_true : Dspec.fst = zftrue := hDspec_def hDapp_def
                  have hgo_Xarg := hgo_forall (fun _ => Xarg) (by
                    intro i
                    have hi0 : i = ⟨0, by simp⟩ := by
                      apply Fin.ext
                      simp
                    cases hi0
                    exact ⟨rfl, hx_1⟩)
                  have hbody_eq :
                      ⟦(Term.abstract.go a [x] Δ₀ hgo_cov).uncurry (fun _ => Xarg)⟧ˢ =
                        some Dspec := by
                    rw [hgo_Xarg]
                    simpa [Xarg] using hden_spec
                  generalize_proofs hbody_some
                  have hbody_get :
                      (⟦(Term.abstract.go a [x] Δ₀ hgo_cov).uncurry (fun _ => Xarg)⟧ˢ.get
                        hbody_some) = Dspec := by
                    rw [Option.get_of_eq_some hbody_some hbody_eq]
                  have hbody_fst :
                      (⟦(Term.abstract.go a [x] Δ₀ hgo_cov).uncurry (fun _ => Xarg)⟧ˢ.get
                        hbody_some).fst = Dspec.fst := by
                    exact congrArg (fun d : SMT.Dom => d.fst) hbody_get
                  rw [hbody_fst, hDspec_true]
              simpa [Φ] using hsInter_true
        simpa [Std.Do.PostCond.mayThrow] using
          (((Std.Do.wp (defaultSpecM s!"{name}_body" β (.app t (.var x)))).mono
            Qraw
            (Std.Do.PostCond.mayThrow fun a st =>
              match st with
              | { env := E', types := Γ'' } =>
                Std.Do.SPred.pure
                  (St₁.env.freshvarsc ≤ E'.freshvarsc ∧
                    St₁.types ⊆ Γ'' ∧
                    St₁.env.usedVars ⊆ E'.usedVars ∧
                    AList.keys Γ'' ⊆ E'.usedVars ∧
                    (∀ v ∈ St₁.env.usedVars, v ∉ St₁.types → v ∉ Γ'') ∧
                    Γ'' ⊢ˢ Term.forall [x] [α] a : SMTType.bool ∧
                    fv (Term.forall [x] [α] a) ⊆ fv t ∧
                    ∀ (Δ₀ : RenamingContext.Context)
                      (ht₀ : RenamingContext.CoversFV Δ₀ t)
                      (Y : SMT.Dom),
                      ⟦t.abstract Δ₀ ht₀⟧ˢ = some Y →
                        ∃ (hφ : RenamingContext.CoversFV Δ₀ (Term.forall [x] [α] a)) (Φ : SMT.Dom),
                          ⟦(Term.forall [x] [α] a).abstract Δ₀ hφ⟧ˢ = some Φ ∧
                            Φ.snd.fst = SMTType.bool ∧
                            (Y.fst = (α.fun β).defaultZFSet → Φ.fst = zftrue)))
            (by simpa [Qneed] using hpost)) St₂ hraw_at)

theorem defaultSpecMTrueImpliesDefault.{u} :
    ∀ («Δ» : RenamingContext.Context.{u})
      {τ : SMTType} {Γ : TypeContext} {n : ℕ} {used : List 𝒱} {name : String} {t : Term}
      (typ_t : Γ ⊢ˢ t : τ)
      (ht : RenamingContext.CoversFV «Δ» t),
      ⦃fun st =>
        match st with
        | { env := E, types := Γ' } =>
          ⌜Γ' = Γ ∧ E.freshvarsc = n ∧ AList.keys Γ' ⊆ E.usedVars ∧ E.usedVars = used⌝⦄
        defaultSpecM name τ t ⦃PostCond.mayThrow fun spec st' =>
          match st' with
          | { env := E', types := Γ'' } =>
            ⌜n ≤ E'.freshvarsc ∧
                Γ ⊆ Γ'' ∧
                used ⊆ E'.usedVars ∧
                AList.keys Γ'' ⊆ E'.usedVars ∧
                Γ'' ⊢ˢ spec : SMTType.bool ∧
                fv spec ⊆ fv t ∧
                ∀ («Δ₀» : RenamingContext.Context.{u})
                  (ht₀ : RenamingContext.CoversFV «Δ₀» t)
                  (Y : SMT.Dom.{u}),
                  ⟦t.abstract «Δ₀» ht₀⟧ˢ = some Y →
                    ∀ (hφ : RenamingContext.CoversFV «Δ₀» spec)
                      {Φ : SMT.Dom.{u}},
                      ⟦spec.abstract «Δ₀» hφ⟧ˢ = some Φ →
                        Φ.fst = zftrue →
                          Y.fst = τ.defaultZFSet⌝⦄ := by
  intro «Δ» τ Γ n used name t typ_t ht
  induction τ generalizing «Δ» Γ n used name t with
  | int =>
      mintro pre ∀St₁
      mpure pre
      obtain ⟨rfl, rfl, sub, rfl⟩ := pre
      unfold defaultSpecM
      mspec Std.Do.Spec.pure
      mpure_intro
      and_intros
      · exact Nat.le_refl _
      · intro v hv
        exact hv
      · intro v hv
        exact hv
      · exact sub
      · exact SMT.Typing.eq _ _ _ _ typ_t (SMT.Typing.int _ _)
      · intro v hv
        simpa [SMT.fv] using hv
      · intro Δ₀ ht₀ Y den_t hφ Φ hdenΦ htrue
        have hden_zero :
            ⟦(.int 0 : Term).abstract Δ₀ (by
                intro v hv
                simpa [SMT.fv] using hv)⟧ˢ =
              some ⟨ZFSet.ofInt 0, .int, ZFSet.mem_ofInt_Int 0⟩ := by
          rw [SMT.Term.abstract, SMT.denote, Option.pure_def]
        exact denote_eq_true_implies_fst_eq den_t hden_zero
          (denote_type_eq_of_typing (typ_t := typ_t) (hden := den_t))
          (by simpa [SMT.Term.abstract] using hdenΦ) htrue
  | bool =>
      mintro pre ∀St₁
      mpure pre
      obtain ⟨rfl, rfl, sub, rfl⟩ := pre
      unfold defaultSpecM
      mspec Std.Do.Spec.pure
      mpure_intro
      and_intros
      · exact Nat.le_refl _
      · intro v hv
        exact hv
      · intro v hv
        exact hv
      · exact sub
      · exact SMT.Typing.eq _ _ _ _ typ_t (SMT.Typing.bool _ false)
      · intro v hv
        simpa [SMT.fv] using hv
      · intro Δ₀ ht₀ Y den_t hφ Φ hdenΦ htrue
        have hden_false :
            ⟦(.bool false : Term).abstract Δ₀ (by
                intro v hv
                simpa [SMT.fv] using hv)⟧ˢ =
              some ⟨zffalse, .bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
          rw [SMT.Term.abstract, SMT.denote, Option.pure_def]
          rfl
        exact denote_eq_true_implies_fst_eq den_t hden_false
          (denote_type_eq_of_typing (typ_t := typ_t) (hden := den_t))
          (by simpa [SMT.Term.abstract] using hdenΦ) htrue
  | unit =>
      mintro pre ∀St₁
      mpure pre
      obtain ⟨rfl, rfl, sub, rfl⟩ := pre
      unfold defaultSpecM
      mspec Std.Do.Spec.pure
      mpure_intro
      and_intros
      · exact Nat.le_refl _
      · intro v hv
        exact hv
      · intro v hv
        exact hv
      · exact sub
      · exact SMT.Typing.bool _ true
      · intro v hv
        simpa [SMT.fv] using hv
      · intro Δ₀ ht₀ Y den_t hφ Φ hdenΦ htrue
        obtain ⟨y, τ, hy⟩ := Y
        have hY_ty : τ = SMTType.unit :=
          denote_type_eq_of_typing (typ_t := typ_t) (hden := den_t)
        cases hY_ty
        rw [SMTType.defaultZFSet]
        rw [SMTType.toZFSet] at hy
        exact ZFSet.mem_singleton.mp hy
  | option τ ih =>
      mintro pre ∀St₁
      mpure pre
      obtain ⟨rfl, rfl, sub, rfl⟩ := pre
      unfold defaultSpecM
      mspec Std.Do.Spec.pure
      mpure_intro
      and_intros
      · exact Nat.le_refl _
      · intro v hv
        exact hv
      · intro v hv
        exact hv
      · exact sub
      · exact SMT.Typing.eq _ _ _ _ typ_t (SMT.Typing.none _ _)
      · intro v hv
        simpa [noneCast, SMT.fv] using hv
      · intro Δ₀ ht₀ Y den_t hφ Φ hdenΦ htrue
        have hden_none :
            ⟦(none$τ).abstract Δ₀ (by
                intro v hv
                simpa [noneCast, SMT.fv] using hv)⟧ˢ =
              some ⟨(SMTType.option τ).defaultZFSet, SMTType.option τ,
                SMTType.mem_toZFSet_of_defaultZFSet⟩ := by
          simpa [noneCast, SMTType.defaultZFSet, SMT.Term.abstract, SMT.denote]
        exact denote_eq_true_implies_fst_eq den_t hden_none
          (denote_type_eq_of_typing (typ_t := typ_t) (hden := den_t))
          (by simpa [SMT.Term.abstract] using hdenΦ) htrue
  | pair α β ihα ihβ =>
      mintro pre ∀St₁
      mpure pre
      obtain ⟨rfl, rfl, sub, rfl⟩ := pre
      have hpair :
          ⦃fun st =>
            match st with
            | { env := E, types := Γ' } =>
              ⌜Γ' = St₁.types ∧
                  E.freshvarsc = St₁.env.freshvarsc ∧
                  AList.keys Γ' ⊆ E.usedVars ∧
                  E.usedVars = St₁.env.usedVars⌝⦄
          defaultSpecM name (α.pair β) t ⦃PostCond.mayThrow fun spec st' =>
            match st' with
            | { env := E', types := Γ'' } =>
              ⌜St₁.env.freshvarsc ≤ E'.freshvarsc ∧
                  St₁.types ⊆ Γ'' ∧
                  St₁.env.usedVars ⊆ E'.usedVars ∧
                  AList.keys Γ'' ⊆ E'.usedVars ∧
                  Γ'' ⊢ˢ spec : SMTType.bool ∧
                  fv spec ⊆ fv t ∧
                  ∀ («Δ₀» : RenamingContext.Context)
                    (ht₀ : RenamingContext.CoversFV «Δ₀» t)
                    (Y : SMT.Dom),
                    ⟦t.abstract «Δ₀» ht₀⟧ˢ = some Y →
                      ∀ (hφ : RenamingContext.CoversFV «Δ₀» spec)
                        {Φ : SMT.Dom},
                        ⟦spec.abstract «Δ₀» hφ⟧ˢ = some Φ →
                          Φ.fst = zftrue →
                            Y.fst = (α.pair β).defaultZFSet⌝⦄ := by
        unfold defaultSpecM
        let typ_fst : St₁.types ⊢ˢ .fst t : α := by
          exact SMT.Typing.fst _ _ _ _ typ_t
        let ht_fst : RenamingContext.CoversFV «Δ» (.fst t) := by
          intro v hv
          exact ht v (by simpa [SMT.fv] using hv)
        let Qfst :
            Term →
              Std.Do.Assertion
                (Std.Do.PostShape.arg EncoderState (Std.Do.PostShape.except String Std.Do.PostShape.pure)) :=
          fun hfst st =>
            match st with
            | { env := E', types := Γ'' } =>
              Std.Do.SPred.pure
                (St₁.env.freshvarsc ≤ E'.freshvarsc ∧
                  St₁.types ⊆ Γ'' ∧
                  St₁.env.usedVars ⊆ E'.usedVars ∧
                  AList.keys Γ'' ⊆ E'.usedVars ∧
                  Γ'' ⊢ˢ hfst : SMTType.bool ∧
                  fv hfst ⊆ fv (Term.fst t) ∧
                  ∀ («Δ₀» : RenamingContext.Context)
                    (ht₀ : RenamingContext.CoversFV «Δ₀» (Term.fst t))
                    (Y : SMT.Dom),
                    ⟦(Term.fst t).abstract «Δ₀» ht₀⟧ˢ = some Y →
                      ∀ (hφ : RenamingContext.CoversFV «Δ₀» hfst)
                        {Φ : SMT.Dom},
                        ⟦hfst.abstract «Δ₀» hφ⟧ˢ = some Φ →
                          Φ.fst = zftrue →
                            Y.fst = α.defaultZFSet)
        refine Std.Do.Triple.bind
          (Q := Qfst)
          (x := defaultSpecM s!"{name}_fst" α (.fst t))
          (f := fun hfst => do
            let hsnd ← defaultSpecM s!"{name}_snd" β (.snd t)
            pure (hfst ∧ˢ hsnd))
          ?_ ?_
        · exact ihα
            «Δ»
            (Γ := St₁.types) (n := St₁.env.freshvarsc) (used := St₁.env.usedVars)
            (name := s!"{name}_fst") (t := .fst t) typ_fst ht_fst
        · intro hfst
          mintro pre ∀St₂
          mpure pre
          obtain ⟨hn₂, sub₂, used₂, keys₂, typ_hfst, fv_hfst, den_hfst⟩ := pre
          have typ_t_St₂ : St₂.types ⊢ˢ t : α.pair β := by
            exact SMT.Typing.weakening (h := sub₂) typ_t
          have typ_snd : St₂.types ⊢ˢ .snd t : β := by
            exact SMT.Typing.snd _ _ _ _ typ_t_St₂
          have ht_snd : RenamingContext.CoversFV «Δ» (.snd t) := by
            intro v hv
            exact ht v (by simpa [SMT.fv] using hv)
          have ihβ_snd := ihβ
            «Δ»
            (Γ := St₂.types) (n := St₂.env.freshvarsc) (used := St₂.env.usedVars)
            (name := s!"{name}_snd") (t := .snd t) typ_snd ht_snd
          let Qraw : Std.Do.PostCond Term
              (Std.Do.PostShape.arg EncoderState (Std.Do.PostShape.except String Std.Do.PostShape.pure)) :=
            Std.Do.PostCond.mayThrow fun hsnd st =>
              match st with
              | { env := E', types := Γ'' } =>
                Std.Do.SPred.pure
                  (St₂.env.freshvarsc ≤ E'.freshvarsc ∧
                    St₂.types ⊆ Γ'' ∧
                    St₂.env.usedVars ⊆ E'.usedVars ∧
                    AList.keys Γ'' ⊆ E'.usedVars ∧
                    Γ'' ⊢ˢ hsnd : SMTType.bool ∧
                    fv hsnd ⊆ fv (Term.snd t) ∧
                    ∀ («Δ₀» : RenamingContext.Context)
                      (ht₀ : RenamingContext.CoversFV «Δ₀» (Term.snd t))
                      (Y : SMT.Dom),
                      ⟦(Term.snd t).abstract «Δ₀» ht₀⟧ˢ = some Y →
                        ∀ (hφ : RenamingContext.CoversFV «Δ₀» hsnd)
                          {Φ : SMT.Dom},
                          ⟦hsnd.abstract «Δ₀» hφ⟧ˢ = some Φ →
                            Φ.fst = zftrue →
                              Y.fst = β.defaultZFSet)
          let Qneed : Std.Do.PostCond Term
              (Std.Do.PostShape.arg EncoderState (Std.Do.PostShape.except String Std.Do.PostShape.pure)) :=
            Std.Do.PostCond.mayThrow fun hsnd st =>
              match st with
              | { env := E', types := Γ'' } =>
                Std.Do.SPred.pure
                  (St₁.env.freshvarsc ≤ E'.freshvarsc ∧
                    St₁.types ⊆ Γ'' ∧
                    St₁.env.usedVars ⊆ E'.usedVars ∧
                    AList.keys Γ'' ⊆ E'.usedVars ∧
                    Γ'' ⊢ˢ (hfst ∧ˢ hsnd) : SMTType.bool ∧
                    fv (hfst ∧ˢ hsnd) ⊆ fv t ∧
                    ∀ («Δ₀» : RenamingContext.Context)
                      (ht₀ : RenamingContext.CoversFV «Δ₀» t)
                      (Y : SMT.Dom),
                      ⟦t.abstract «Δ₀» ht₀⟧ˢ = some Y →
                        ∀ (hφ : RenamingContext.CoversFV «Δ₀» (hfst ∧ˢ hsnd))
                          {Φ : SMT.Dom},
                          ⟦(hfst ∧ˢ hsnd).abstract «Δ₀» hφ⟧ˢ = some Φ →
                            Φ.fst = zftrue →
                              Y.fst = (α.pair β).defaultZFSet)
          rw [Std.Do.WP.bind]
          simp only [Std.Do.WP.pure]
          have hraw_at :
              (wp⟦defaultSpecM s!"{name}_snd" β (.snd t)⟧ Qraw St₂).down := by
            change
              (wp⟦defaultSpecM s!"{name}_snd" β (.snd t)⟧
                (Std.Do.PostCond.mayThrow fun hsnd st =>
                  match st with
                  | { env := E', types := Γ'' } =>
                    Std.Do.SPred.pure
                      (St₂.env.freshvarsc ≤ E'.freshvarsc ∧
                        St₂.types ⊆ Γ'' ∧
                        St₂.env.usedVars ⊆ E'.usedVars ∧
                        AList.keys Γ'' ⊆ E'.usedVars ∧
                        Γ'' ⊢ˢ hsnd : SMTType.bool ∧
                        fv hsnd ⊆ fv (Term.snd t) ∧
                        ∀ («Δ₀» : RenamingContext.Context)
                          (ht₀ : RenamingContext.CoversFV «Δ₀» (Term.snd t))
                          (Y : SMT.Dom),
                          ⟦(Term.snd t).abstract «Δ₀» ht₀⟧ˢ = some Y →
                            ∀ (hφ : RenamingContext.CoversFV «Δ₀» hsnd)
                              {Φ : SMT.Dom},
                              ⟦hsnd.abstract «Δ₀» hφ⟧ˢ = some Φ →
                                Φ.fst = zftrue →
                                  Y.fst = β.defaultZFSet))
                St₂).down
            exact ihβ_snd St₂ (by
              refine ⟨rfl, rfl, keys₂, rfl⟩)
          have hpost : Qraw ⊢ₚ Qneed := by
            rw [Std.Do.PostCond.entails_mayThrow]
            intro hsnd
            mintro pre ∀St₃
            mpure pre
            obtain ⟨hn₃, sub₃, used₃, keys₃, typ_hsnd, fv_hsnd, den_hsnd⟩ := pre
            mpure_intro
            and_intros
            · exact hn₂.trans hn₃
            · intro v hv
              exact sub₃ (sub₂ hv)
            · intro v hv
              exact used₃ (used₂ hv)
            · exact keys₃
            · have typ_hfst_St₃ : St₃.types ⊢ˢ hfst : SMTType.bool := by
                exact SMT.Typing.weakening (h := sub₃) typ_hfst
              exact SMT.Typing.and _ _ _ typ_hfst_St₃ typ_hsnd
            · intro v hv
              rcases (by simpa [SMT.fv, List.mem_append] using hv) with hv | hv
              · simpa [SMT.fv] using fv_hfst hv
              · simpa [SMT.fv] using fv_hsnd hv
            · intro «Δ₀» ht₀ Y den_t hφ Φ hdenΦ htrue
              have ht_fst₀ : RenamingContext.CoversFV «Δ₀» (Term.fst t) := by
                intro v hv
                exact ht₀ v (by simpa [SMT.fv] using hv)
              have ht_snd₀ : RenamingContext.CoversFV «Δ₀» (Term.snd t) := by
                intro v hv
                exact ht₀ v (by simpa [SMT.fv] using hv)
              have hY_ty : Y.snd.fst = α.pair β :=
                denote_type_eq_of_typing (typ_t := typ_t) (hden := den_t)
              have hY_mem : Y.fst ∈ ⟦α.pair β⟧ᶻ := by
                simpa [hY_ty] using Y.snd.snd
              have hY_prod : Y.fst ∈ ⟦α⟧ᶻ.prod ⟦β⟧ᶻ := by
                simpa [SMTType.toZFSet] using hY_mem
              have hY_eta : Y.fst = Y.fst.π₁.pair Y.fst.π₂ := by
                exact ZFSet.pair_eta hY_prod
              rw [ZFSet.pair_eta hY_prod, ZFSet.pair_mem_prod] at hY_prod
              let Yfst : SMT.Dom := ⟨Y.fst.π₁, α, hY_prod.1⟩
              let Ysnd : SMT.Dom := ⟨Y.fst.π₂, β, hY_prod.2⟩
              have hden_fst_t : ⟦(Term.fst t).abstract «Δ₀» ht_fst₀⟧ˢ = some Yfst := by
                cases Y with
                | mk y hy =>
                    cases hy with
                    | mk τ hy =>
                        cases hY_ty
                        rw [SMT.Term.abstract.eq_def, SMT.denote, den_t]
                        dsimp [Yfst]
              have hden_snd_t : ⟦(Term.snd t).abstract «Δ₀» ht_snd₀⟧ˢ = some Ysnd := by
                cases Y with
                | mk y hy =>
                    cases hy with
                    | mk τ hy =>
                        cases hY_ty
                        rw [SMT.Term.abstract.eq_def, SMT.denote, den_t]
                        dsimp [Ysnd]
              have hφfst : RenamingContext.CoversFV «Δ₀» hfst := by
                intro v hv
                exact hφ v (by simpa [SMT.fv, List.mem_append] using Or.inl hv)
              have hφsnd : RenamingContext.CoversFV «Δ₀» hsnd := by
                intro v hv
                exact hφ v (by simpa [SMT.fv, List.mem_append] using Or.inr hv)
              obtain ⟨Dfst, Dsnd, hdenDfst, hDfst_true, hdenDsnd, hDsnd_true⟩ :=
                denoteAndTrueComponents
                  (fun hdenDfst =>
                    denote_type_eq_of_typing
                      (typ_t := SMT.Typing.weakening (h := sub₃) typ_hfst) (hden := hdenDfst))
                  (fun hdenDsnd =>
                    denote_type_eq_of_typing (typ_t := typ_hsnd) (hden := hdenDsnd))
                  (p := hfst.abstract «Δ₀» hφfst)
                  (q := hsnd.abstract «Δ₀» hφsnd)
                  (hden := by simpa [SMT.Term.abstract] using hdenΦ)
                  htrue
              have hfst_def : Yfst.fst = α.defaultZFSet := by
                exact den_hfst «Δ₀» ht_fst₀ Yfst hden_fst_t hφfst hdenDfst hDfst_true
              have hsnd_def : Ysnd.fst = β.defaultZFSet := by
                exact den_hsnd «Δ₀» ht_snd₀ Ysnd hden_snd_t hφsnd hdenDsnd hDsnd_true
              dsimp [Yfst, Ysnd] at hfst_def hsnd_def
              rw [hY_eta, SMTType.defaultZFSet, hfst_def, hsnd_def]
          simpa [Std.Do.PostCond.mayThrow] using
            (((Std.Do.wp (defaultSpecM s!"{name}_snd" β (.snd t))).mono
              Qraw
              (Std.Do.PostCond.mayThrow fun hsnd st =>
                match st with
                | { env := E', types := Γ'' } =>
                  Std.Do.SPred.pure
                    (St₁.env.freshvarsc ≤ E'.freshvarsc ∧
                      St₁.types ⊆ Γ'' ∧
                      St₁.env.usedVars ⊆ E'.usedVars ∧
                      AList.keys Γ'' ⊆ E'.usedVars ∧
                      Γ'' ⊢ˢ (hfst ∧ˢ hsnd) : SMTType.bool ∧
                      fv (hfst ∧ˢ hsnd) ⊆ fv t ∧
                      ∀ («Δ₀» : RenamingContext.Context)
                        (ht₀ : RenamingContext.CoversFV «Δ₀» t)
                        (Y : SMT.Dom),
                        ⟦t.abstract «Δ₀» ht₀⟧ˢ = some Y →
                          ∀ (hφ : RenamingContext.CoversFV «Δ₀» (hfst ∧ˢ hsnd))
                            {Φ : SMT.Dom},
                            ⟦(hfst ∧ˢ hsnd).abstract «Δ₀» hφ⟧ˢ = some Φ →
                              Φ.fst = zftrue →
                                Y.fst = (α.pair β).defaultZFSet))
              (by simpa [Qneed] using hpost)) St₂ hraw_at)
      simpa using hpair St₁ (by
        refine ⟨rfl, rfl, sub, rfl⟩)
  | «fun» α β ihα ihβ =>
      mintro pre ∀St₁
      mpure pre
      obtain ⟨rfl, rfl, sub, rfl⟩ := pre
      unfold defaultSpecM
      mspec SMT.freshVar_spec (Γ := St₁.types) (n := St₁.env.freshvarsc) (used := St₁.env.usedVars)
      next x =>
        mrename_i pre
        mintro ∀St₂
        mpure pre
        obtain ⟨St₂_types_eq, x_fresh, St₂_fvc, St₂_used_eq, x_not_used⟩ := pre
        have typ_t_St₂ : St₂.types ⊢ˢ t : α.fun β := by
          rw [St₂_types_eq]
          exact SMT.Typing.weakening
            (h := SMT.TypeContext.entries_subset_insert_of_notMem x_fresh)
            typ_t
        have typ_var_x_St₂ : St₂.types ⊢ˢ .var x : α := by
          apply SMT.Typing.var
          rw [St₂_types_eq]
          exact AList.lookup_insert St₁.types
        have typ_app_St₂ : St₂.types ⊢ˢ .app t (.var x) : β := by
          exact SMT.Typing.app
            (Γ := St₂.types) (f := t) (x := .var x) (τ := α) (σ := β)
            typ_t_St₂ typ_var_x_St₂
        have keys₂ : AList.keys St₂.types ⊆ St₂.env.usedVars := by
          rw [St₂_types_eq, St₂_used_eq, AList.keys_insert]
          intro v hv
          rw [List.mem_cons] at hv ⊢
          rcases hv with rfl | hv
          · exact Or.inl rfl
          · exact Or.inr (sub (List.mem_of_mem_erase hv))
        let Xdef : SMT.Dom := ⟨α.defaultZFSet, α, SMTType.mem_toZFSet_of_defaultZFSet⟩
        let Δd : RenamingContext.Context := Function.update «Δ» x (some Xdef)
        have ht_app_d : RenamingContext.CoversFV Δd (.app t (.var x)) := by
          intro v hv
          simp [SMT.fv] at hv
          rcases hv with hv | hv
          · by_cases hvx : v = x
            · subst hvx
              simp [Δd]
            · simpa [Δd, Function.update, hvx] using ht v hv
          · subst hv
            simp [Δd]
        have hspecβ_body := defaultSpecMSpec
          Δd
          (Γ := St₂.types) (n := St₂.env.freshvarsc) (used := St₂.env.usedVars)
          (name := s!"{name}_body") (t := .app t (.var x)) typ_app_St₂ ht_app_d
        have ihβ_body := ihβ
          Δd
          (Γ := St₂.types) (n := St₂.env.freshvarsc) (used := St₂.env.usedVars)
          (name := s!"{name}_body") (t := .app t (.var x)) typ_app_St₂ ht_app_d
        mspec (Std.Do.Triple.and _ hspecβ_body ihβ_body)
        · rename_i a
          mrename_i pre
          mintro ∀St₃
          mpure pre
          obtain ⟨pre_spec, pre_conv⟩ := pre
          obtain ⟨hn₃, sub₃, used₃, keys₃, _, typ_a, fv_a, spec_a⟩ := pre_spec
          obtain ⟨_, _, _, _, _, _, conv_a⟩ := pre_conv
          have typ_a_St₂ : St₂.types ⊢ˢ a : SMTType.bool := by
            apply SMT.Typing.strengthening_of_fv_subset sub₃ typ_a
            intro v hv
            have hv' := fv_a hv
            simp only [fv, List.mem_append, List.mem_singleton] at hv'
            rcases hv' with hv_t | hv_x
            · exact SMT.Typing.mem_context_of_mem_fv typ_t_St₂ hv_t
            · subst hv_x
              rw [St₂_types_eq, AList.mem_insert]
              exact Or.inl rfl
          mspec Std.Do.Spec.pure
          mpure_intro
          and_intros
          · calc
              St₁.env.freshvarsc ≤ St₂.env.freshvarsc := by
                rw [St₂_fvc]
                exact Nat.le_succ _
              _ ≤ St₃.env.freshvarsc := hn₃
          · intro v hv
            exact sub₃ (by
              rw [St₂_types_eq]
              exact SMT.TypeContext.entries_subset_insert_of_notMem x_fresh hv)
          · intro v hv
            exact used₃ (by
              rw [St₂_used_eq]
              exact List.mem_cons_of_mem _ hv)
          · exact keys₃
          · have typ_forall_base :
                St₁.types ⊢ˢ Term.forall [x] [α] a : SMTType.bool := by
              refine SMT.Typing.forall St₁.types [x] [α] a ?_ ?_ ?_ ?_ ?_
              · intro v hvv hvΓ
                rw [List.mem_singleton] at hvv
                subst hvv
                exact x_fresh hvΓ
              · intro v hvv hvb
                have hxv : v = x := by
                  simpa [List.mem_singleton] using hvv
                have hv_mem_St₂ : v ∈ St₂.types := by
                  rw [hxv, St₂_types_eq, AList.mem_insert]
                  exact Or.inl rfl
                exact SMT.Typing.bv_notMem_context typ_a_St₂ _ hvb hv_mem_St₂
              · simp
              · simp
              · have hupd : St₁.types.update [x] [α] rfl = AList.insert x α St₁.types := by
                  simp only [SMT.TypeContext.update, List.length_cons, List.length_nil, zero_add,
                    Fin.foldl_succ, Nat.reduceAdd, Fin.cast_eq_self, Fin.getElem_fin,
                    Fin.val_eq_zero, List.getElem_cons_zero, Fin.isValue, Fin.foldl_zero]
                rw [hupd]
                simpa [St₂_types_eq] using typ_a_St₂
            exact SMT.Typing.weakening
              (h := by
                intro v hv
                exact sub₃ (by
                  rw [St₂_types_eq]
                  exact SMT.TypeContext.entries_subset_insert_of_notMem x_fresh hv))
              typ_forall_base
          · intro v hv
            simp only [fv, List.mem_removeAll_iff, List.mem_cons, List.not_mem_nil, or_false] at hv
            obtain ⟨hv_a, hxv⟩ := hv
            have hv' := fv_a hv_a
            simp only [fv, List.mem_append, List.mem_singleton] at hv'
            rcases hv' with hv_t | hv_x
            · exact hv_t
            · exact (hxv hv_x).elim
          · intro Δ₀ ht₀ Y den_t hφ Φ hdenΦ htrue
            have x_not_mem_fv_t : x ∉ fv t := by
              intro hx_mem
              exact x_fresh (SMT.Typing.mem_context_of_mem_fv typ_t hx_mem)
            have hY_ty : Y.snd.fst = α.fun β :=
              denote_type_eq_of_typing (typ_t := typ_t) (hden := den_t)
            have hY_func : ZFSet.IsFunc ⟦α⟧ᶻ ⟦β⟧ᶻ Y.fst := by
              rw [←ZFSet.mem_funs]
              simpa [hY_ty] using Y.snd.snd
            have hcov_t_upd (Xarg : SMT.Dom) :
                RenamingContext.CoversFV (Function.update Δ₀ x (some Xarg)) t :=
              SMT.RenamingContext.coversFV_update_of_notMem
                (x := x) (d := Xarg) x_not_mem_fv_t ht₀
            have den_t_upd (Xarg : SMT.Dom) :
                ⟦t.abstract (Function.update Δ₀ x (some Xarg)) (hcov_t_upd Xarg)⟧ˢ = some Y := by
              calc
                ⟦t.abstract (Function.update Δ₀ x (some Xarg)) (hcov_t_upd Xarg)⟧ˢ =
                    SMT.RenamingContext.denote (Function.update Δ₀ x (some Xarg)) t
                      (hcov_t_upd Xarg) := by
                      rfl
                _ = SMT.RenamingContext.denote Δ₀ t ht₀ := by
                      simpa [SMT.RenamingContext.denote] using
                        (SMT.RenamingContext.denote_update_of_notMem
                          («Δ» := Δ₀) (t := t) (x := x) (d := Xarg)
                          (h := ht₀) x_not_mem_fv_t).symm
                _ = some Y := den_t
            have hcov_a_upd (Xarg : SMT.Dom) :
                RenamingContext.CoversFV (Function.update Δ₀ x (some Xarg)) a := by
              intro v hv
              have hv' := fv_a hv
              simp only [fv, List.mem_append, List.mem_singleton] at hv'
              rcases hv' with hv_t | hv_x
              · by_cases hvx : v = x
                · subst hvx
                  simp
                · rw [Function.update_of_ne hvx]
                  exact ht₀ v hv_t
              · subst hv_x
                simp
            have hgo_cov :
                ∀ v ∈ fv a, v ∉ [x] → (Δ₀ v).isSome = true := by
              intro v hv hv_not_x
              have hv' := fv_a hv
              simp only [fv, List.mem_append, List.mem_singleton] at hv'
              rcases hv' with hv_t | hv_x
              · exact ht₀ v hv_t
              · have hv_mem_x : v ∈ [x] := by
                  simpa [List.mem_singleton] using hv_x
                exact (hv_not_x hv_mem_x).elim
            have hφ_forall : RenamingContext.CoversFV Δ₀ (Term.forall [x] [α] a) := by
              intro v hv
              simp only [fv, List.mem_removeAll_iff, List.mem_cons, List.not_mem_nil, or_false] at hv
              obtain ⟨hv_a, hxv⟩ := hv
              have hv' := fv_a hv_a
              simp only [fv, List.mem_append, List.mem_singleton] at hv'
              rcases hv' with hv_t | hv_x
              · exact ht₀ v hv_t
              · exact (hxv hv_x).elim
            have hgo_forall
                (w : Fin [x].length → SMT.Dom)
                (hw : ∀ i, (w i).snd.fst = [α][i] ∧ (w i).fst ∈ ⟦[α][i]⟧ᶻ) :
                (Term.abstract.go a [x] Δ₀ hgo_cov).uncurry w =
                  a.abstract (Function.update Δ₀ x (some (w ⟨0, by simp⟩)))
                    (hcov_a_upd (w ⟨0, by simp⟩)) := by
              have hgo := SMT.Term.abstract.go.alt_def₂
                (vs := [x]) (P := a) (Δctx := Δ₀)
                (αs := List.ofFn w) (vs_αs_len := by simp)
                (Δ_isSome := hgo_cov)
                (tmp₁ := by
                  intro v hv
                  by_cases hvx : v ∈ [x]
                  · exact Function.updates_isSome_of_mem_map_some Δ₀ [x] (List.ofFn w) v hvx (by simp)
                  · rw [Function.updates_of_not_mem
                      (f := Δ₀)
                      (xs := [x]) (ys := (List.ofFn w).map Option.some) (k := v) hvx]
                    exact hgo_cov v hv (by simpa using hvx))
              have h_ofFn_list : List.ofFn w = [w ⟨0, by simp⟩] := by
                simpa using (List.ofFn_succ' (n := 0) w)
              have h_ofFn :
                  (fun i =>
                    match i with
                    | ⟨j, _⟩ => (List.ofFn w)[j]) = w := by
                funext i
                cases i with
                | mk j hj =>
                    simp at hj
                    have hj0 : j = 0 := hj
                    subst hj0
                    simp [h_ofFn_list]
              simpa [h_ofFn, Function.updates] using hgo
            have hbody_total :
                ∀ {x_1 : Fin [x].length → SMT.Dom},
                  (∀ i, (x_1 i).snd.fst = [α][i] ∧ (x_1 i).fst ∈ ⟦[α][i]⟧ᶻ) →
                    ⟦(Term.abstract.go a [x] Δ₀ hgo_cov).uncurry x_1⟧ˢ.isSome = true := by
              intro x_1 hx_1
              let Xarg : SMT.Dom := x_1 ⟨0, by simp⟩
              have hXarg_ty : Xarg.snd.fst = α := by
                simpa [Xarg] using (hx_1 ⟨0, by simp⟩).1
              have hXarg_mem : Xarg.fst ∈ ⟦α⟧ᶻ := by
                simpa [Xarg] using (hx_1 ⟨0, by simp⟩).2
              obtain ⟨hcov_app, Dapp, hDapp_ty, hDapp_val, hden_app⟩ :=
                defaultSpecMFunDenoteAppAt
                  (hcov_t_upd := hcov_t_upd) (den_t_upd := den_t_upd)
                  (hY_ty := hY_ty) (hY_func := hY_func)
                  Xarg hXarg_ty hXarg_mem
              obtain ⟨hφa, Dspec, hden_spec, hDspec_ty, hDspec_def⟩ :=
                spec_a (Function.update Δ₀ x (some Xarg)) hcov_app Dapp hden_app
              rw [hgo_forall x_1 hx_1]
              exact Option.isSome_of_eq_some hden_spec
            have hbody_total' :
                ∀ {x_1 : Fin [x].length → SMT.Dom},
                  (∀ i,
                    ((x_1 i).snd.fst =
                        match i with
                        | ⟨i, hi⟩ => [α][i]) ∧
                      (x_1 i).fst ∈
                        ⟦match i with
                          | ⟨i, hi⟩ => [α][i]⟧ᶻ) →
                    ⟦(Term.abstract.go a [x] Δ₀ hgo_cov).uncurry x_1⟧ˢ.isSome = true := by
              intro x_1 hx_1
              exact hbody_total (by
                intro i
                have hi0 : i = ⟨0, by simp⟩ := by
                  apply Fin.ext
                  simp
                cases hi0
                simpa using hx_1 ⟨0, by simp⟩)
            let bodyVal : ZFSet → ZFSet := fun x_1 =>
              if h : x_1.hasArity 1 ∧ x_1 ∈ ⟦α⟧ᶻ then
                (⟦(Term.abstract.go a [x] Δ₀ hgo_cov).uncurry
                    (fun _ => ⟨x_1, α, h.2⟩)⟧ˢ.get
                  (hbody_total (by
                    intro i
                    have hi0 : i = ⟨0, by simp⟩ := by
                      apply Fin.ext
                      simp
                    cases hi0
                    exact ⟨rfl, h.2⟩))).fst
              else zffalse
            let Sbody : ZFSet :=
              ⋂₀ (ZFSet.sep (fun y => ∃ x_1 ∈ ⟦α⟧ᶻ, y = bodyVal x_1) 𝔹)
            have hlen_forall : [x].length > 0 := by
              simp
            rw [SMT.Term.abstract, dif_pos (by rfl), SMT.denote] at hdenΦ
            rw [dif_pos hlen_forall] at hdenΦ
            split_ifs at hdenΦ with hsome
            · simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_one_sub_one,
                List.getElem_cons_succ, Fin.zero_eta, Fin.isValue, Fin.coe_ofNat_eq_mod,
                Nat.zero_mod, List.getElem_cons_zero, Fin.val_eq_zero, get.eq_1, forall_const,
                Option.pure_def, Option.failure_eq_none, Option.bind_some, Fin.foldl_zero] at hdenΦ
              let sInterGoal : ZFSet :=
                ⋂₀
                  ZFSet.sep
                    (fun y =>
                      ∃ x_1 ∈ ⟦α⟧ᶻ,
                        y =
                          if hx : x_1.hasArity 1 ∧ ∀ i : Fin 1, x_1 ∈ ⟦[α][↑i]⟧ᶻ then
                            (⟦(Term.abstract.go a [x] Δ₀ hgo_cov).uncurry
                                (fun i => ⟨x_1, [α][↑i], hx.2 i⟩)⟧ˢ.get
                              (hsome (by
                                intro i
                                exact ⟨rfl, hx.2 i⟩))).fst
                          else zffalse)
                    𝔹
              have hsInter_eq : sInterGoal = Sbody := by
                dsimp [sInterGoal, Sbody, bodyVal]
                congr
                ext y
                have hbody_eq {x_1 : ZFSet} (hx_1 : x_1 ∈ ⟦α⟧ᶻ) :
                    (if hx : x_1.hasArity 1 ∧ ∀ i : Fin 1, x_1 ∈ ⟦[α][↑i]⟧ᶻ then
                      (⟦(Term.abstract.go a [x] Δ₀ hgo_cov).uncurry
                          (fun i => ⟨x_1, [α][↑i], hx.2 i⟩)⟧ˢ.get
                        (hsome (by
                          intro i
                          exact ⟨rfl, hx.2 i⟩))).fst
                    else zffalse) =
                    bodyVal x_1 := by
                  by_cases h : x_1.hasArity 1 ∧ x_1 ∈ ⟦α⟧ᶻ
                  · have hx : x_1.hasArity 1 ∧ ∀ i : Fin 1, x_1 ∈ ⟦[α][↑i]⟧ᶻ := by
                      constructor
                      · exact h.1
                      · intro i
                        have hi0 : i = ⟨0, by simp⟩ := by
                          apply Fin.ext
                          simp
                        cases hi0
                        simpa using h.2
                    simpa [bodyVal, hx, h]
                  · have hx : ¬ (x_1.hasArity 1 ∧ ∀ i : Fin 1, x_1 ∈ ⟦[α][↑i]⟧ᶻ) := by
                      intro hx
                      apply h
                      constructor
                      · exact hx.1
                      · simpa using hx.2 ⟨0, by simp⟩
                    simpa [bodyVal, hx, h]
                constructor
                · rintro ⟨x_1, hx_1, hy⟩
                  refine ⟨x_1, ?_, hy.trans (hbody_eq (by simpa [Fin.foldl_zero] using hx_1))⟩
                  simpa [Fin.foldl_zero] using hx_1
                · rintro ⟨x_1, hx_1, hy⟩
                  refine ⟨x_1, ?_, hy.trans (hbody_eq hx_1).symm⟩
                  simpa [Fin.foldl_zero] using hx_1
              have hsInterGoal_true : sInterGoal = zftrue := by
                have hΦ_eq := Option.some.inj hdenΦ.symm
                cases hΦ_eq
                simpa [sInterGoal, Fin.foldl_zero] using htrue
              have hsInter_true : Sbody = zftrue := by
                calc
                  Sbody = sInterGoal := hsInter_eq.symm
                  _ = zftrue := hsInterGoal_true
              have hbody_bool : ∀ x_1 ∈ ⟦α⟧ᶻ, bodyVal x_1 ∈ 𝔹 := by
                intro x_1 hx_1
                have hx_cast : x_1.hasArity 1 ∧ x_1 ∈ ⟦α⟧ᶻ := by
                  constructor
                  · exact (funUnaryTarget (α := α) hx_1).1
                  · exact hx_1
                dsimp [bodyVal]
                rw [dif_pos hx_cast]
                let Xarg : SMT.Dom := ⟨x_1, α, hx_1⟩
                obtain ⟨hcov_app, Dapp, hDapp_ty, hDapp_val, hden_app⟩ :=
                  defaultSpecMFunDenoteAppAt
                    (hcov_t_upd := hcov_t_upd) (den_t_upd := den_t_upd)
                    (hY_ty := hY_ty) (hY_func := hY_func)
                    Xarg rfl hx_1
                obtain ⟨hφa, Dspec, hden_spec, hDspec_ty, hDspec_def⟩ :=
                  spec_a (Function.update Δ₀ x (some Xarg)) hcov_app Dapp hden_app
                have hgo_Xarg := hgo_forall (fun _ => Xarg) (by
                  intro i
                  have hi0 : i = ⟨0, by simp⟩ := by
                    apply Fin.ext
                    simp
                  cases hi0
                  exact ⟨rfl, hx_1⟩)
                have hbody_eq :
                    ⟦(Term.abstract.go a [x] Δ₀ hgo_cov).uncurry (fun _ => Xarg)⟧ˢ =
                      some Dspec := by
                  rw [hgo_Xarg]
                  simpa [Xarg] using hden_spec
                have hbody_some_bool :
                    ⟦(Term.abstract.go a [x] Δ₀ hgo_cov).uncurry (fun _ => Xarg)⟧ˢ.isSome = true := by
                  exact Option.isSome_of_eq_some hbody_eq
                have hbody_fst :
                    (⟦(Term.abstract.go a [x] Δ₀ hgo_cov).uncurry (fun _ => Xarg)⟧ˢ.get
                      (hbody_total (by
                        intro i
                        have hi0 : i = ⟨0, by simp⟩ := by
                          apply Fin.ext
                          simp
                        cases hi0
                        exact ⟨rfl, hx_1⟩))).fst = Dspec.fst := by
                  calc
                    (⟦(Term.abstract.go a [x] Δ₀ hgo_cov).uncurry (fun _ => Xarg)⟧ˢ.get
                      (hbody_total (by
                        intro i
                        have hi0 : i = ⟨0, by simp⟩ := by
                          apply Fin.ext
                          simp
                        cases hi0
                        exact ⟨rfl, hx_1⟩))).fst =
                    (⟦(Term.abstract.go a [x] Δ₀ hgo_cov).uncurry (fun _ => Xarg)⟧ˢ.get
                      hbody_some_bool).fst := by
                          exact Option.get_fst_eq_of_isSome
                    _ = Dspec.fst := by
                      exact congrArg (fun d : SMT.Dom => d.fst)
                        (Option.get_of_eq_some hbody_some_bool hbody_eq)
                have hbody_fst' :
                    (⟦(Term.abstract.go a [x] Δ₀ hgo_cov).uncurry
                      (fun _ => ⟨x_1, α, hx_1⟩)⟧ˢ.get (by simpa [Xarg] using hbody_some_bool)).fst = Dspec.fst := by
                  simpa [Xarg] using hbody_fst
                have hDspec_bool : Dspec.fst ∈ 𝔹 := by
                  simpa [hDspec_ty] using Dspec.snd.snd
                exact hbody_fst'.symm ▸ hDspec_bool
              have hall_true : ∀ x_1 ∈ ⟦α⟧ᶻ, bodyVal x_1 = zftrue := by
                exact sInterSepEqZftrueImpliesForallEqZftrue hbody_bool hsInter_true
              apply (ZFSet.is_func_ext_iff hY_func (defaultZFSetFunIsFunc (α := α) (β := β))).2
              intro x_1 hx_1
              have hx_cast : x_1.hasArity 1 ∧ x_1 ∈ ⟦α⟧ᶻ := by
                constructor
                · exact (funUnaryTarget (α := α) hx_1).1
                · exact hx_1
              let Xarg : SMT.Dom := ⟨x_1, α, hx_1⟩
              obtain ⟨hcov_app, Dapp, hDapp_ty, hDapp_val, hden_app⟩ :=
                defaultSpecMFunDenoteAppAt
                  (hcov_t_upd := hcov_t_upd) (den_t_upd := den_t_upd)
                  (hY_ty := hY_ty) (hY_func := hY_func)
                  Xarg rfl hx_1
              obtain ⟨hφa, Dspec, hden_spec, hDspec_ty, hDspec_def⟩ :=
                spec_a (Function.update Δ₀ x (some Xarg)) hcov_app Dapp hden_app
              have hgo_Xarg := hgo_forall (fun _ => Xarg) (by
                intro i
                have hi0 : i = ⟨0, by simp⟩ := by
                  apply Fin.ext
                  simp
                cases hi0
                exact ⟨rfl, hx_1⟩)
              have hbody_eq :
                  ⟦(Term.abstract.go a [x] Δ₀ hgo_cov).uncurry (fun _ => Xarg)⟧ˢ =
                    some Dspec := by
                rw [hgo_Xarg]
                simpa [Xarg] using hden_spec
              have hbody_some_true :
                  ⟦(Term.abstract.go a [x] Δ₀ hgo_cov).uncurry (fun _ => Xarg)⟧ˢ.isSome = true := by
                exact Option.isSome_of_eq_some hbody_eq
              have hbody_true : Dspec.fst = zftrue := by
                have hbody_true' : bodyVal x_1 = zftrue := hall_true x_1 hx_1
                dsimp [bodyVal] at hbody_true'
                rw [dif_pos hx_cast] at hbody_true'
                calc
                  Dspec.fst =
                    (⟦(Term.abstract.go a [x] Δ₀ hgo_cov).uncurry (fun _ => Xarg)⟧ˢ.get
                      hbody_some_true).fst := by
                        exact congrArg (fun d : SMT.Dom => d.fst)
                          (Option.get_of_eq_some hbody_some_true hbody_eq).symm
                  _ =
                    (⟦(Term.abstract.go a [x] Δ₀ hgo_cov).uncurry (fun _ => Xarg)⟧ˢ.get
                      (hbody_total (by
                        intro i
                        have hi0 : i = ⟨0, by simp⟩ := by
                          apply Fin.ext
                          simp
                        cases hi0
                        exact ⟨rfl, hx_1⟩))).fst := by
                          exact (Option.get_fst_eq_of_isSome).symm
                  _ = zftrue := hbody_true'
              have hDapp_default : Dapp.fst = β.defaultZFSet := by
                exact conv_a (Function.update Δ₀ x (some Xarg)) hcov_app Dapp hden_app hφa hden_spec hbody_true
              apply Subtype.ext
              calc
                (ZFSet.fapply Y.fst (ZFSet.is_func_is_pfunc hY_func)
                  ⟨x_1, by
                    simpa [ZFSet.is_func_dom_eq hY_func] using hx_1⟩).val = Dapp.fst := by
                      exact hDapp_val.symm
                _ = β.defaultZFSet := hDapp_default
                _ =
                  (ZFSet.fapply (SMTType.defaultZFSet (α.fun β))
                    (ZFSet.is_func_is_pfunc (defaultZFSetFunIsFunc (α := α) (β := β)))
                    ⟨x_1, by
                      simpa [ZFSet.is_func_dom_eq (defaultZFSetFunIsFunc (α := α) (β := β))] using hx_1⟩).val := by
                        exact (defaultZFSetFunApp (α := α) (β := β) hx_1).symm
            · exact (hsome hbody_total').elim
