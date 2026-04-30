import SMT.Reasoning.Defs
import SMT.Reasoning.LooseningDefs
import SMT.Reasoning.Basic.StateSpecs
import SMT.Reasoning.Basic.LoosenAuxExact.FunDefault

open Std.Do SMT ZFSet Classical

abbrev FunPf.{u} («Δ» : RenamingContext.Context.{u}) : Prop :=
  ∀ (x! : 𝒱) (X! : SMT.Dom.{u}), ∀ v ∈ fv (Term.var x!),
    (Function.update «Δ» x! (some X!) v).isSome = true

abbrev FunExactIH.{u}
    {τ τ' : SMTType} (p : τ ⇝ τ') : Prop :=
  ∀ {Λ : TypeContext} {n : ℕ} {used : List 𝒱} {name : String} {x : Term},
    Λ ⊢ˢ x : τ →
      ∀ («Δ₀» : RenamingContext.Context.{u}) (hx : RenamingContext.CoversFV «Δ₀» x)
        (pf₀ : FunPf «Δ₀»),
        ⦃fun x =>
          match x with
          | { env := E, types := Λ' } =>
            ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ AList.keys Λ' ⊆ E.usedVars ∧ E.usedVars = used⌝⦄
        loosenAux_prf name p x
          ⦃PostCond.mayThrow fun x_1 x_2 =>
            match x_1 with
            | (x!, x!_spec) =>
              match x_2 with
              | { env := E', types := Γ' } =>
                ⌜n ≤ E'.freshvarsc ∧
                    AList.insert x! τ' Λ ⊆ Γ' ∧
                      x! ∉ Λ ∧
                        x! ∉ used ∧
                          used ⊆ E'.usedVars ∧
                            AList.keys Γ' ⊆ E'.usedVars ∧
                              (∀ v ∈ used, v ∉ Λ → v ∉ Γ') ∧
                              AList.insert x! τ' Λ ⊢ˢ Term.var x! : τ' ∧
                                AList.insert x! τ' Λ ⊢ˢ x!_spec : SMTType.bool ∧
                                  Γ' ⊢ˢ Term.var x! : τ' ∧
                                    Γ' ⊢ˢ x!_spec : SMTType.bool ∧
                                      fv x!_spec ⊆ fv x ∪ {x!} ∧
                                        ∀ (X : SMT.Dom.{u}),
                                          ⟦x.abstract «Δ₀» hx⟧ˢ = some X →
                                            ∃ Φ X!,
                                              ∃ (_ :
                                                ⟦(Term.var x!).abstract
                                                    (Function.update «Δ₀» x! (some X!))
                                                    (pf₀ x! X!)⟧ˢ =
                                                  some X!)
                                                (hφ : RenamingContext.CoversFV
                                                  (Function.update «Δ₀» x! (some X!))
                                                  x!_spec)
                                                (_ :
                                                  ⟦x!_spec.abstract
                                                      (Function.update «Δ₀» x! (some X!))
                                                      hφ⟧ˢ =
                                                    some Φ),
                                                Φ.snd.fst = SMTType.bool ∧
                                                  (Φ.fst = zftrue ∧
                                                    X.fst.pair X!.fst ∈ (castZF_of_path p).1) ∧
                                                    ∀ (Y : SMT.Dom.{u}),
                                                      Y.snd.fst = τ' →
                                                        ∀ (hφY : RenamingContext.CoversFV
                                                          (Function.update «Δ₀» x! (some Y))
                                                          x!_spec),
                                                          ⟦x!_spec.abstract
                                                              (Function.update «Δ₀» x! (some Y))
                                                              hφY⟧ˢ.isSome =
                                                            true ∧
                                                            ∀ {ΦY : SMT.Dom.{u}},
                                                              ⟦x!_spec.abstract
                                                                  (Function.update «Δ₀» x! (some Y))
                                                                  hφY⟧ˢ =
                                                                some ΦY →
                                                                ΦY.fst = zftrue →
                                                                  X.fst.pair Y.fst ∈
                                                                    (castZF_of_path p).1⌝⦄

theorem typeContext_insert_swap_entries
    {Γ : TypeContext} {x y : 𝒱} {τx τy : SMTType}
    (hxy : x ≠ y) :
    (AList.insert x τx (AList.insert y τy Γ)).entries ⊆
      (AList.insert y τy (AList.insert x τx Γ)).entries := by
  intro e he
  rcases e with ⟨v, τ⟩
  rw [← AList.mem_lookup_iff] at he ⊢
  by_cases hvx : v = x
  · subst hvx
    rw [AList.lookup_insert] at he
    rw [AList.lookup_insert_ne hxy, AList.lookup_insert]
    exact he
  · by_cases hvy : v = y
    · subst hvy
      rw [AList.lookup_insert_ne hxy.symm, AList.lookup_insert] at he
      rw [AList.lookup_insert]
      exact he
    · rw [AList.lookup_insert_ne hvx, AList.lookup_insert_ne hvy] at he
      rw [AList.lookup_insert_ne hvy, AList.lookup_insert_ne hvx]
      exact he

theorem typeContext_mem_of_subset
    {Γ₁ : TypeContext} {Γ₂ : TypeContext} {v : 𝒱}
    (hsub : Γ₁ ⊆ Γ₂) (hv : v ∈ Γ₁) :
    v ∈ Γ₂ := by
  obtain ⟨τ, hlookup⟩ := Option.isSome_iff_exists.mp ((AList.lookup_isSome).2 hv)
  exact (AList.lookup_isSome).1 <| Option.isSome_of_eq_some <|
    (AList.mem_lookup_iff).2 <| hsub ((AList.mem_lookup_iff).1 hlookup)

theorem funNotMemFvOfNotMemContext
    {Γ : TypeContext} {t : Term} {τ : SMTType} {v : 𝒱}
    (ht : Γ ⊢ˢ t : τ)
    (hv : v ∉ Γ) :
    v ∉ fv t := by
  intro hfv
  exact hv (SMT.Typing.mem_context_of_mem_fv ht hfv)

theorem funDenoteEqFalseOfFstNe
    {t₁ t₂ : SMT.PHOAS.Term SMT.Dom}
    {D₁ D₂ : SMT.Dom}
    (h₁ : ⟦t₁⟧ˢ = some D₁)
    (h₂ : ⟦t₂⟧ˢ = some D₂)
    (hτ : D₁.snd.fst = D₂.snd.fst)
    (hNe : D₁.fst ≠ D₂.fst) :
    ⟦t₁ =ˢ' t₂⟧ˢ = some ⟨zffalse, .bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
  obtain ⟨Deq, hden_eq, hDeq_ty⟩ := denote_eq_some_of_some h₁ h₂ hτ
  have hDeq_false : Deq.fst = zffalse := by
    have hDeq_mem_bool : Deq.fst ∈ 𝔹 := by
      simpa [hDeq_ty] using Deq.snd.snd
    rw [ZFSet.ZFBool.mem_𝔹_iff] at hDeq_mem_bool
    rcases hDeq_mem_bool with hDeq_false | hDeq_true
    · exact hDeq_false
    · exfalso
      exact hNe <| denote_eq_true_implies_fst_eq h₁ h₂ hτ hden_eq hDeq_true
  obtain ⟨d, τ, hd⟩ := Deq
  cases hDeq_ty
  cases hDeq_false
  simpa [proof_irrel_heq] using hden_eq

theorem funAbstractGoSingle.{u}
    {Δctx : RenamingContext.Context.{u}} {P : Term} {v : 𝒱} {τ : SMTType}
    (hgo_cov : ∀ x ∈ fv P, x ∉ [v] → (Δctx x).isSome = true)
    (hcovP :
      ∀ W : SMT.Dom.{u},
        RenamingContext.CoversFV (Function.update Δctx v (some W)) P) :
    ∀ (w : Fin [v].length → SMT.Dom.{u})
      (hw : ∀ i, (w i).snd.fst = [τ][i] ∧ (w i).fst ∈ ⟦[τ][i]⟧ᶻ),
      (Term.abstract.go P [v] Δctx hgo_cov).uncurry w =
        P.abstract (Function.update Δctx v (some (w ⟨0, by simp⟩)))
          (hcovP (w ⟨0, by simp⟩)) := by
  intro w hw
  have hgo := SMT.Term.abstract.go.alt_def₂
    (vs := [v]) (P := P) (Δctx := Δctx)
    (αs := List.ofFn w) (vs_αs_len := by simp)
    (Δ_isSome := hgo_cov)
    (tmp₁ := by
      intro x hx
      by_cases hxv : x ∈ [v]
      · exact Function.updates_isSome_of_mem_map_some Δctx [v] (List.ofFn w) x hxv (by simp)
      · rw [Function.updates_of_not_mem
          (f := Δctx)
          (xs := [v]) (ys := (List.ofFn w).map Option.some) (k := x) hxv]
        exact hgo_cov x hx (by simpa using hxv))
  have h_ofFn_list : List.ofFn w = [w ⟨0, Nat.zero_lt_succ 0⟩] := rfl
  have h_ofFn : (fun ⟨j, _⟩ ↦ (List.ofFn w)[j]) = w := by
    funext ⟨j, hj⟩
    simp only [List.length_cons, List.length_nil, zero_add, Nat.lt_one_iff] at hj
    subst hj
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, List.ofFn_succ, Fin.isValue,
      List.ofFn_zero, List.getElem_cons_zero, Fin.zero_eta]
  simpa [h_ofFn, Function.updates] using hgo

theorem funNotAbstractIsSomeOfSomeBool.{u}
    {Δctx : RenamingContext.Context.{u}} {t : Term} {D : SMT.Dom.{u}}
    (hcov_t : RenamingContext.CoversFV Δctx t)
    (hden_t : ⟦t.abstract Δctx hcov_t⟧ˢ = some D)
    (hD_ty : D.snd.fst = SMTType.bool) :
    ∀ (hcov_not : RenamingContext.CoversFV Δctx (¬ˢ t)),
      ⟦(¬ˢ t).abstract Δctx hcov_not⟧ˢ.isSome = true := by
  intro hcov_not
  have hnot_some := denote_not_isSome_of_some_bool (hden := hden_t) (hTy := hD_ty)
  simpa only [SMT.Term.abstract, SMT.denote, proof_irrel_heq] using hnot_some

theorem funNotAbstractEqZftrueOfSomeZffalse.{u}
    {Δctx : RenamingContext.Context.{u}} {t : Term} {D : SMT.Dom.{u}}
    (hcov_t : RenamingContext.CoversFV Δctx t)
    (hden_t : ⟦t.abstract Δctx hcov_t⟧ˢ = some D)
    (hD_ty : D.snd.fst = SMTType.bool)
    (hD_false : D.fst = zffalse) :
    ∀ (hcov_not : RenamingContext.CoversFV Δctx (¬ˢ t)),
      ⟦(¬ˢ t).abstract Δctx hcov_not⟧ˢ =
        some ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
  intro hcov_not
  have hnot_true :=
    denote_not_eq_zftrue_of_some_zffalse hden_t hD_ty hD_false
  simpa only [SMT.Term.abstract, SMT.denote, proof_irrel_heq] using hnot_true

theorem funAbstractGoPair.{u}
    {Δctx : RenamingContext.Context.{u}} {P : Term} {v₁ v₂ : 𝒱}
    {τ₁ τ₂ : SMTType}
    (hgo_cov : ∀ x ∈ fv P, x ∉ [v₁, v₂] → (Δctx x).isSome = true)
    (hcovP :
      ∀ W₁ W₂ : SMT.Dom.{u},
        RenamingContext.CoversFV
          (Function.update (Function.update Δctx v₁ (some W₁)) v₂ (some W₂))
          P) :
    ∀ (w : Fin [v₁, v₂].length → SMT.Dom.{u})
      (hw : ∀ i, (w i).snd.fst = [τ₁, τ₂][i] ∧ (w i).fst ∈ ⟦[τ₁, τ₂][i]⟧ᶻ),
      (Term.abstract.go P [v₁, v₂] Δctx hgo_cov).uncurry w =
        P.abstract
          (Function.update
            (Function.update Δctx v₁ (some (w ⟨0, by simp⟩)))
            v₂ (some (w ⟨1, by simp⟩)))
          (hcovP (w ⟨0, by simp⟩) (w ⟨1, by simp⟩)) := by
  intro w hw
  have hgo := SMT.Term.abstract.go.alt_def₂
    (vs := [v₁, v₂]) (P := P) (Δctx := Δctx)
    (αs := List.ofFn w) (vs_αs_len := by simp)
    (Δ_isSome := hgo_cov)
    (tmp₁ := by
      intro x hx
      by_cases hxv : x ∈ [v₁, v₂]
      · exact Function.updates_isSome_of_mem_map_some Δctx [v₁, v₂] (List.ofFn w) x hxv (by simp)
      · rw [Function.updates_of_not_mem
          (f := Δctx)
          (xs := [v₁, v₂]) (ys := (List.ofFn w).map Option.some) (k := x) hxv]
        exact hgo_cov x hx (by simpa using hxv))
  have h_ofFn_list : List.ofFn w = [w ⟨0, by simp⟩, w ⟨1, by simp⟩] := rfl
  have h_ofFn :
      (fun i =>
        match i with
        | ⟨j, _⟩ => (List.ofFn w)[j]) = w := by
    funext i
    rcases i with ⟨j, hj⟩
    exact List.getElem_ofFn (f := w) (h := by simpa [h_ofFn_list] using hj)
  simpa [h_ofFn, Function.updates] using hgo

/-- Generalization of `funAbstractGoSingle`/`funAbstractGoPair` to arbitrary-length
bound-variable lists. -/
theorem funAbstractGoList.{u}
    {Δctx : RenamingContext.Context.{u}} {P : Term} {vs : List 𝒱} {τs : List SMTType}
    (vs_len : vs.length = τs.length)
    (hgo_cov : ∀ x ∈ fv P, x ∉ vs → (Δctx x).isSome = true)
    (hcovP :
      ∀ (w : Fin vs.length → SMT.Dom.{u}),
        RenamingContext.CoversFV
          (Function.updates Δctx vs (List.ofFn (fun i => some (w i))))
          P) :
    ∀ (w : Fin vs.length → SMT.Dom.{u})
      (_hw : ∀ i, (w i).snd.fst = τs[i]'(vs_len ▸ i.isLt) ∧
                  (w i).fst ∈ ⟦τs[i]'(vs_len ▸ i.isLt)⟧ᶻ),
      (Term.abstract.go P vs Δctx hgo_cov).uncurry w =
        P.abstract
          (Function.updates Δctx vs (List.ofFn (fun i => some (w i))))
          (hcovP w) := by
  intro w hw
  have hgo := SMT.Term.abstract.go.alt_def₂
    (vs := vs) (P := P) (Δctx := Δctx)
    (αs := List.ofFn w) (vs_αs_len := by simp)
    (Δ_isSome := hgo_cov)
    (tmp₁ := by
      intro x hx
      by_cases hxv : x ∈ vs
      · exact Function.updates_isSome_of_mem_map_some Δctx vs (List.ofFn w) x hxv (by simp)
      · rw [Function.updates_of_not_mem
          (f := Δctx)
          (xs := vs) (ys := (List.ofFn w).map Option.some) (k := x) hxv]
        exact hgo_cov x hx hxv)
  have h_ofFn :
      (fun (i : Fin vs.length) => (List.ofFn w)[i.val]'(by simp)) = w := by
    funext i
    rcases i with ⟨j, hj⟩
    simp only [List.getElem_ofFn]
  have h_map_ofFn :
      List.map (fun x : SMT.Dom => some x) (List.ofFn w) =
      List.ofFn (fun i => some (w i)) := by
    apply List.ext_getElem
    · simp
    · intro n h1 h2
      simp only [List.getElem_map, List.getElem_ofFn]
  simpa [h_ofFn, h_map_ofFn, Function.updates] using hgo

noncomputable def funCastTargetZF
    {α β α' β' : SMTType}
    (castα castβ : ZFSet) (X : SMT.Dom)
    (hcastα : ZFSet.IsFunc ⟦α⟧ᶻ ⟦α'⟧ᶻ castα)
    (hcastβ : ZFSet.IsFunc ⟦β⟧ᶻ ⟦β'⟧ᶻ castβ)
    (hX_func : ZFSet.IsFunc ⟦α⟧ᶻ ⟦β⟧ᶻ X.fst) : ZFSet :=
  λᶻ: ⟦α'⟧ᶻ → ⟦β'⟧ᶻ
    | x' ↦ if hx_ran : x' ∈ castα.Range then
              let x₀ := Classical.choose (ZFSet.mem_sep.mp hx_ran).2
              have hx₀_mem : x₀ ∈ ⟦α⟧ᶻ := by
                have ⟨dom, _⟩ := Classical.choose_spec (ZFSet.mem_sep.mp hx_ran).2
                exact (ZFSet.mem_sep.mp dom).1
              let y₀ := @ᶻX.fst
                ⟨x₀, by
                  simpa [ZFSet.is_func_dom_eq hX_func] using hx₀_mem⟩
              @ᶻcastβ
                ⟨y₀, by
                  rw [ZFSet.is_func_dom_eq hcastβ]
                  exact Subtype.property y₀⟩
            else
              β'.defaultZFSet

theorem funCastTargetZF_mem
    {α β α' β' : SMTType}
    (castα castβ : ZFSet) (X : SMT.Dom)
    (hcastα : ZFSet.IsFunc ⟦α⟧ᶻ ⟦α'⟧ᶻ castα)
    (hcastβ : ZFSet.IsFunc ⟦β⟧ᶻ ⟦β'⟧ᶻ castβ)
    (hX_func : ZFSet.IsFunc ⟦α⟧ᶻ ⟦β⟧ᶻ X.fst) :
    funCastTargetZF castα castβ X hcastα hcastβ hX_func ∈ ⟦α'.fun β'⟧ᶻ := by
  unfold funCastTargetZF
  rw [ZFSet.mem_funs]
  apply ZFSet.lambda_isFunc
  intro x' hx'
  dsimp
  split_ifs with hx_ran
  · exact ZFSet.fapply_mem_range (ZFSet.is_func_is_pfunc hcastβ) (by
      rw [ZFSet.is_func_dom_eq hcastβ]
      exact Subtype.property _)
  · exact SMTType.mem_toZFSet_of_defaultZFSet

theorem funCastTargetZF_isFunc
    {α β α' β' : SMTType}
    (castα castβ : ZFSet) (X : SMT.Dom)
    (hcastα : ZFSet.IsFunc ⟦α⟧ᶻ ⟦α'⟧ᶻ castα)
    (hcastβ : ZFSet.IsFunc ⟦β⟧ᶻ ⟦β'⟧ᶻ castβ)
    (hX_func : ZFSet.IsFunc ⟦α⟧ᶻ ⟦β⟧ᶻ X.fst) :
    ZFSet.IsFunc ⟦α'⟧ᶻ ⟦β'⟧ᶻ (funCastTargetZF castα castβ X hcastα hcastβ hX_func) := by
  rw [← ZFSet.mem_funs]
  exact funCastTargetZF_mem castα castβ X hcastα hcastβ hX_func

theorem funCastTargetZF_app_default
    {α β α' β' : SMTType}
    (castα castβ : ZFSet) (X : SMT.Dom)
    (hcastα : ZFSet.IsFunc ⟦α⟧ᶻ ⟦α'⟧ᶻ castα)
    (hcastβ : ZFSet.IsFunc ⟦β⟧ᶻ ⟦β'⟧ᶻ castβ)
    (hcastα_inj : castα.IsInjective hcastα)
    (hX_func : ZFSet.IsFunc ⟦α⟧ᶻ ⟦β⟧ᶻ X.fst)
    (wy0 : SMT.Dom)
    (hwy0_ty : wy0.snd.fst = α')
    (hy_not_ran : wy0.fst ∉ castα.Range) :
    ZFSet.fapply (funCastTargetZF castα castβ X hcastα hcastβ hX_func)
      (ZFSet.is_func_is_pfunc (funCastTargetZF_isFunc castα castβ X hcastα hcastβ hX_func))
      ⟨wy0.fst, by
        simpa [ZFSet.is_func_dom_eq
          (funCastTargetZF_isFunc castα castβ X hcastα hcastβ hX_func), hwy0_ty] using
          wy0.snd.snd⟩ =
      β'.defaultZFSet := by
  have hwy0_mem : wy0.fst ∈ ⟦α'⟧ᶻ := by
    rw [← hwy0_ty]
    exact wy0.snd.snd
  unfold funCastTargetZF
  rw [ZFSet.fapply_lambda
    (A := ⟦α'⟧ᶻ)
    (B := ⟦β'⟧ᶻ)
    (f := fun x' =>
      if hx_ran : x' ∈ castα.Range then
        let x₀ := Classical.choose (ZFSet.mem_sep.mp hx_ran).2
        have hx₀_mem : x₀ ∈ ⟦α⟧ᶻ := by
          have ⟨dom, _⟩ := Classical.choose_spec (ZFSet.mem_sep.mp hx_ran).2
          exact (ZFSet.mem_sep.mp dom).1
        let y₀ := @ᶻX.fst
          ⟨x₀, by
            simpa [ZFSet.is_func_dom_eq hX_func] using hx₀_mem⟩
        @ᶻcastβ
          ⟨y₀, by
            rw [ZFSet.is_func_dom_eq hcastβ]
            exact Subtype.property y₀⟩
      else
        β'.defaultZFSet)
    (hf := by
      intro x' hx'
      dsimp
      split_ifs with hx_ran
      · exact ZFSet.fapply_mem_range (ZFSet.is_func_is_pfunc hcastβ) (by
          rw [ZFSet.is_func_dom_eq hcastβ]
          exact Subtype.property _)
      · exact SMTType.mem_toZFSet_of_defaultZFSet)
    (ha := hwy0_mem)]
  rw [dif_neg hy_not_ran]

theorem funCastTargetZF_app_range
    {α β α' β' : SMTType}
    (castα castβ : ZFSet) (X : SMT.Dom)
    (hcastα : ZFSet.IsFunc ⟦α⟧ᶻ ⟦α'⟧ᶻ castα)
    (hcastβ : ZFSet.IsFunc ⟦β⟧ᶻ ⟦β'⟧ᶻ castβ)
    (hX_func : ZFSet.IsFunc ⟦α⟧ᶻ ⟦β⟧ᶻ X.fst)
    (wy0 : SMT.Dom)
    (hwy0_ty : wy0.snd.fst = α')
    (hy_ran : wy0.fst ∈ castα.Range) :
    ∃ (x₀ : ZFSet) (hx₀_mem : x₀ ∈ ⟦α⟧ᶻ),
      @ᶻcastα
        ⟨x₀, by
          rw [ZFSet.is_func_dom_eq hcastα]
          exact hx₀_mem⟩ = wy0.fst ∧
      ZFSet.fapply (funCastTargetZF castα castβ X hcastα hcastβ hX_func)
        (ZFSet.is_func_is_pfunc (funCastTargetZF_isFunc castα castβ X hcastα hcastβ hX_func))
        ⟨wy0.fst, by
          simpa [ZFSet.is_func_dom_eq
            (funCastTargetZF_isFunc castα castβ X hcastα hcastβ hX_func), hwy0_ty] using
            wy0.snd.snd⟩ =
        @ᶻcastβ
          ⟨@ᶻX.fst
              ⟨x₀, by
                simpa [ZFSet.is_func_dom_eq hX_func] using hx₀_mem⟩, by
                rw [ZFSet.is_func_dom_eq hcastβ]
                exact Subtype.property _⟩ := by
  have hwy0_mem : wy0.fst ∈ ⟦α'⟧ᶻ := by
    rw [← hwy0_ty]
    exact wy0.snd.snd
  let x₀ : ZFSet := Classical.choose (ZFSet.mem_sep.mp hy_ran).2
  have hx₀_mem : x₀ ∈ ⟦α⟧ᶻ := by
    have ⟨hdom, _⟩ := Classical.choose_spec (ZFSet.mem_sep.mp hy_ran).2
    exact (ZFSet.mem_sep.mp hdom).1
  have hcast_x₀ :
      @ᶻcastα
        ⟨x₀, by
          rw [ZFSet.is_func_dom_eq hcastα]
          exact hx₀_mem⟩ = wy0.fst := by
    have ⟨_, hpair⟩ := Classical.choose_spec (ZFSet.mem_sep.mp hy_ran).2
    exact congrArg Subtype.val
      (ZFSet.fapply.of_pair (hf := ZFSet.is_func_is_pfunc hcastα) hpair)
  refine ⟨x₀, hx₀_mem, hcast_x₀, ?_⟩
  apply Subtype.ext
  unfold funCastTargetZF
  rw [ZFSet.fapply_lambda
    (A := ⟦α'⟧ᶻ)
    (B := ⟦β'⟧ᶻ)
    (f := fun x' =>
      if hx_ran : x' ∈ castα.Range then
        let x₀ := Classical.choose (ZFSet.mem_sep.mp hx_ran).2
        have hx₀_mem : x₀ ∈ ⟦α⟧ᶻ := by
          have ⟨dom, _⟩ := Classical.choose_spec (ZFSet.mem_sep.mp hx_ran).2
          exact (ZFSet.mem_sep.mp dom).1
        let y₀ := @ᶻX.fst
          ⟨x₀, by
            simpa [ZFSet.is_func_dom_eq hX_func] using hx₀_mem⟩
        @ᶻcastβ
          ⟨y₀, by
            rw [ZFSet.is_func_dom_eq hcastβ]
            exact Subtype.property y₀⟩
      else
        β'.defaultZFSet)
    (hf := by
      intro x' hx'
      dsimp
      split_ifs with hx_ran
      · exact ZFSet.fapply_mem_range (ZFSet.is_func_is_pfunc hcastβ) (by
          rw [ZFSet.is_func_dom_eq hcastβ]
          exact Subtype.property _)
      · exact SMTType.mem_toZFSet_of_defaultZFSet)
    (ha := hwy0_mem)]
  rw [dif_pos hy_ran]

def funExistsABTerm
    (x a!_spec b!_spec : Term) (a b : 𝒱) (α β : SMTType) : Term :=
  .exists [a, b] [α, β]
    (((.app x (.var a)) =ˢ (.var b)) ∧ˢ (a!_spec ∧ˢ b!_spec))

def funBBodyTerm
    (x! a! b! : 𝒱) (exists_ab : Term) : Term :=
  (((.app (.var x!) (.var a!)) =ˢ (.var b!)) =ˢ exists_ab)

def funSpecTerm
    (x : Term) (x! a a! b b! : 𝒱)
    (α β α' β' : SMTType)
    (a!_spec b!_spec hdefault : Term) : Term :=
  let exists_a : Term := .exists [a] [α] a!_spec
  let exists_ab : Term := funExistsABTerm x a!_spec b!_spec a b α β
  let bBody : Term := funBBodyTerm x! a! b! exists_ab
  .forall [a!] [α'] (.ite exists_a (.forall [b!] [β'] bBody) hdefault)

theorem funSpecTermFvSubset
    {x a!_spec b!_spec hdefault : Term}
    {x! a a! b b! : 𝒱} {α β α' β' : SMTType}
    (fv_a!_spec : fv a!_spec ⊆ fv (.var a) ∪ {a!})
    (fv_b!_spec : fv b!_spec ⊆ fv (.var b) ∪ {b!})
    (fv_hdefault : fv hdefault ⊆ fv (.app (.var x!) (.var a!))) :
    fv (funSpecTerm x x! a a! b b! α β α' β' a!_spec b!_spec hdefault) ⊆
      fv x ∪ {x!} := by
  intro v hv
  dsimp [funSpecTerm, funExistsABTerm, funBBodyTerm] at hv
  rw [fv] at hv
  obtain ⟨hv_body, hv_not_a!⟩ := List.mem_removeAll_iff.mp hv
  rw [List.mem_singleton] at hv_not_a!
  rw [fv, List.mem_append] at hv_body
  rcases hv_body with hv_body | hv_default
  · rw [List.mem_append] at hv_body
    rcases hv_body with hv_exists | hv_then
    · rw [fv] at hv_exists
      obtain ⟨hv_a_spec, hv_not_a⟩ := List.mem_removeAll_iff.mp hv_exists
      rw [List.mem_singleton] at hv_not_a
      have hv' := fv_a!_spec hv_a_spec
      rw [List.mem_union_iff] at hv'
      rcases hv' with hv_a | hv_a!
      · rw [fv, List.mem_singleton] at hv_a
        exact False.elim (hv_not_a hv_a)
      · exact False.elim (hv_not_a! (List.mem_singleton.mp hv_a!))
    · rw [fv] at hv_then
      obtain ⟨hv_inner, hv_not_b!⟩ := List.mem_removeAll_iff.mp hv_then
      rw [List.mem_singleton] at hv_not_b!
      rw [fv, List.mem_append] at hv_inner
      rcases hv_inner with hv_eq | hv_exists
      · rw [fv, List.mem_append] at hv_eq
        rcases hv_eq with hv_app | hv_b!
        · rw [fv, List.mem_append] at hv_app
          rcases hv_app with hv_x! | hv_a!
          · rw [fv, List.mem_singleton] at hv_x!
            rw [List.mem_union_iff]
            exact Or.inr (List.mem_singleton.mpr hv_x!)
          · rw [fv, List.mem_singleton] at hv_a!
            exact False.elim (hv_not_a! hv_a!)
        · rw [fv, List.mem_singleton] at hv_b!
          exact False.elim (hv_not_b! hv_b!)
      · rw [fv] at hv_exists
        obtain ⟨hv_exists, hv_not_ab⟩ := List.mem_removeAll_iff.mp hv_exists
        rw [List.mem_cons, List.mem_singleton, not_or] at hv_not_ab
        obtain ⟨hv_not_a, hv_not_b⟩ := hv_not_ab
        rw [fv, List.mem_append] at hv_exists
        rcases hv_exists with hv_eq | hv_specs
        · rw [fv, List.mem_append] at hv_eq
          rcases hv_eq with hv_app | hv_b
          · rw [fv, List.mem_append] at hv_app
            rcases hv_app with hv_x | hv_a
            · rw [List.mem_union_iff]
              exact Or.inl hv_x
            · rw [fv, List.mem_singleton] at hv_a
              exact False.elim (hv_not_a hv_a)
          · rw [fv, List.mem_singleton] at hv_b
            exact False.elim (hv_not_b hv_b)
        · rw [fv, List.mem_append] at hv_specs
          rcases hv_specs with hv_a_spec | hv_b_spec
          · have hv' := fv_a!_spec hv_a_spec
            rw [List.mem_union_iff] at hv'
            rcases hv' with hv_a | hv_a!
            · rw [fv, List.mem_singleton] at hv_a
              exact False.elim (hv_not_a hv_a)
            · exact False.elim (hv_not_a! (List.mem_singleton.mp hv_a!))
          · have hv' := fv_b!_spec hv_b_spec
            rw [List.mem_union_iff] at hv'
            rcases hv' with hv_b | hv_b!
            · rw [fv, List.mem_singleton] at hv_b
              exact False.elim (hv_not_b hv_b)
            · exact False.elim (hv_not_b! (List.mem_singleton.mp hv_b!))
  · have hv' := fv_hdefault hv_default
    rw [fv, List.mem_append] at hv'
    rcases hv' with hv_x! | hv_a!
    · rw [fv, List.mem_singleton] at hv_x!
      rw [List.mem_union_iff]
      exact Or.inr (List.mem_singleton.mpr hv_x!)
    · rw [fv, List.mem_singleton] at hv_a!
      exact False.elim (hv_not_a! hv_a!)

theorem funSpecTermCoversUpdate.{u}
    {«Δ» : RenamingContext.Context.{u}}
    {x a!_spec b!_spec hdefault : Term}
    {x! a a! b b! : 𝒱} {α β α' β' : SMTType}
    (hx : RenamingContext.CoversFV «Δ» x)
    (hfv_fun_spec :
      fv (funSpecTerm x x! a a! b b! α β α' β' a!_spec b!_spec hdefault) ⊆
        fv x ∪ {x!})
    (Yfun : SMT.Dom.{u}) :
    RenamingContext.CoversFV
      (Function.update «Δ» x! (some Yfun))
      (funSpecTerm x x! a a! b b! α β α' β' a!_spec b!_spec hdefault) := by
  intro v hv
  have hv' := hfv_fun_spec hv
  rw [List.mem_union_iff] at hv'
  rcases hv' with hv_x | hv_x!
  · by_cases hvx : v = x!
    · subst hvx
      rw [Function.update_self]
      rfl
    · rw [Function.update_of_ne hvx]
      exact hx v hv_x
  · have hvx : v = x! := List.mem_singleton.mp hv_x!
    subst hvx
    rw [Function.update_self]
    rfl

theorem funSpecTermTyping
    {Γ : TypeContext} {x a!_spec b!_spec hdefault : Term}
    {x! a a! b b! : 𝒱} {α β α' β' : SMTType}
    (typ_x : Γ ⊢ˢ x : α.fun β)
    (typ_var_x! : Γ ⊢ˢ .var x! : α'.fun β')
    (a_not : a ∉ Γ)
    (a!_not : a! ∉ AList.insert a α Γ)
    (b_not : b ∉ AList.insert a! α' (AList.insert a α Γ))
    (b!_not : b! ∉ AList.insert b β (AList.insert a! α' (AList.insert a α Γ)))
    (a_ne_a! : a ≠ a!)
    (typ_a!_spec_ctx :
      AList.insert a! α' (AList.insert a α Γ) ⊢ˢ a!_spec : SMTType.bool)
    (typ_b!_spec_ctx :
      AList.insert b! β' (AList.insert b β (AList.insert a! α' (AList.insert a α Γ))) ⊢ˢ
        b!_spec : SMTType.bool)
    (typ_hdefault :
      AList.insert a! α' Γ ⊢ˢ hdefault : SMTType.bool) :
    Γ ⊢ˢ funSpecTerm x x! a a! b b! α β α' β' a!_spec b!_spec hdefault : SMTType.bool := by
  have a!_not_Γ : a! ∉ Γ := by
    intro ha!
    exact a!_not (by
      rw [AList.mem_insert]
      exact Or.inr ha!)
  have b!_not_St₄ : b! ∉ AList.insert a! α' (AList.insert a α Γ) := by
    intro hb!
    exact b!_not (by
      rw [AList.mem_insert]
      exact Or.inr hb!)
  have b!_not_Γa! : b! ∉ AList.insert a! α' Γ := by
    intro hb!
    rw [AList.mem_insert] at hb!
    rcases hb! with hb! | hb!
    · exact b!_not_St₄ (by
        rw [AList.mem_insert]
        exact Or.inl hb!)
    · exact b!_not_St₄ (by
        rw [AList.mem_insert]
        exact Or.inr (by
          rw [AList.mem_insert]
          exact Or.inr hb!))
  have a_ne_b! : a ≠ b! := by
    intro hab!
    subst hab!
    have ha_mem : a ∈ AList.insert b β (AList.insert a! α' (AList.insert a α Γ)) := by
      rw [AList.mem_insert]
      exact Or.inr (by
        rw [AList.mem_insert]
        exact Or.inr (by
          rw [AList.mem_insert]
          exact Or.inl rfl))
    exact b!_not ha_mem
  have b_ne_a : b ≠ a := by
    intro hba
    subst hba
    exact b_not (by
      rw [AList.mem_insert]
      exact Or.inr (by
        rw [AList.mem_insert]
        exact Or.inl rfl))
  have b_ne_b! : b ≠ b! := by
    intro hbb!
    subst hbb!
    have hb_mem : b ∈ AList.insert b β (AList.insert a! α' (AList.insert a α Γ)) := by
      rw [AList.mem_insert]
      exact Or.inl rfl
    exact b!_not hb_mem
  have b_not_Γa! : b ∉ AList.insert a! α' Γ := by
    intro hb
    rw [AList.mem_insert] at hb
    rcases hb with hb | hb
    · exact b_not (by
        rw [AList.mem_insert]
        exact Or.inl hb)
    · exact b_not (by
        rw [AList.mem_insert]
        exact Or.inr (by
          rw [AList.mem_insert]
          exact Or.inr hb))
  have a_not_Γa!b! : a ∉ AList.insert b! β' (AList.insert a! α' Γ) := by
    intro ha
    rw [AList.mem_insert] at ha
    rcases ha with ha | ha
    · exact a_ne_b! ha
    · rw [AList.mem_insert] at ha
      rcases ha with ha | ha
      · exact a_ne_a! ha
      · exact a_not ha
  have b_not_Γa!b! : b ∉ AList.insert b! β' (AList.insert a! α' Γ) := by
    intro hb
    rw [AList.mem_insert] at hb
    rcases hb with hb | hb
    · exact b_ne_b! hb
    · exact b_not_Γa! hb
  have b_not_mid :
      b ∉ AList.insert a α (AList.insert b! β' (AList.insert a! α' Γ)) := by
    intro hb
    rw [AList.mem_insert] at hb
    rcases hb with hb | hb
    · exact b_ne_a hb
    · exact b_not_Γa!b! hb
  have hsub_Γ_a! :
      Γ.entries ⊆ (AList.insert a! α' Γ).entries :=
    SMT.TypeContext.entries_subset_insert_of_notMem a!_not_Γ
  have typ_var_a! :
      AList.insert a! α' Γ ⊢ˢ .var a! : α' := by
    apply SMT.Typing.var
    exact AList.lookup_insert Γ
  have hsub_exists_a :
      (AList.insert a! α' (AList.insert a α Γ)).entries ⊆
        (AList.insert a α (AList.insert a! α' Γ)).entries :=
    typeContext_insert_swap_entries a_ne_a!.symm
  have typ_exists_a_body :
      AList.insert a α (AList.insert a! α' Γ) ⊢ˢ a!_spec : SMTType.bool := by
    exact SMT.Typing.weakening (h := hsub_exists_a) typ_a!_spec_ctx
  have a_in_exists_a :
      a ∈ AList.insert a α (AList.insert a! α' Γ) := by
    rw [AList.mem_insert]
    exact Or.inl rfl
  have fresh_exists_a :
      ∀ v ∈ [a], v ∉ bv a!_spec := by
    intro v hv
    rw [List.mem_singleton] at hv
    subst hv
    intro hbv
    exact (SMT.Typing.bv_notMem_context typ_exists_a_body _ hbv) a_in_exists_a
  have typ_exists_a :
      AList.insert a! α' Γ ⊢ˢ .exists [a] [α] a!_spec : SMTType.bool := by
    apply SMT.Typing.exists
      (Γ := AList.insert a! α' Γ) (vs := [a]) (τs := [α]) (len_eq := rfl)
    · intro v hv
      rw [List.mem_singleton] at hv
      subst hv
      intro ha
      rw [AList.mem_insert] at ha
      rcases ha with ha | ha
      · exact a_ne_a! ha
      · exact a_not ha
    · exact fresh_exists_a
    · simp
    · have hupdate_exists_a :
          SMT.TypeContext.update (AList.insert a! α' Γ) [a] [α] rfl =
            AList.insert a α (AList.insert a! α' Γ) := by
        simp only [SMT.TypeContext.update, List.length_cons, List.length_nil, zero_add,
          Fin.cast_eq_self, Fin.getElem_fin, Fin.foldl_succ_last, Fin.coe_ofNat_eq_mod, Nat.mod_succ,
          List.getElem_cons_zero, Fin.last_zero, Fin.isValue, Fin.foldl_zero]
      rwa [hupdate_exists_a]
  have hsub_Γ_then :
      Γ.entries ⊆ (AList.insert b! β' (AList.insert a! α' Γ)).entries := by
    intro v hv
    exact SMT.TypeContext.entries_subset_insert_of_notMem b!_not_Γa! (hsub_Γ_a! hv)
  have typ_var_x!_then :
      AList.insert b! β' (AList.insert a! α' Γ) ⊢ˢ .var x! : α'.fun β' := by
    exact SMT.Typing.weakening (h := hsub_Γ_then) typ_var_x!
  have typ_var_a!_then :
      AList.insert b! β' (AList.insert a! α' Γ) ⊢ˢ .var a! : α' := by
    exact SMT.Typing.weakening
      (h := SMT.TypeContext.entries_subset_insert_of_notMem b!_not_Γa!)
      typ_var_a!
  have typ_var_b!_then :
      AList.insert b! β' (AList.insert a! α' Γ) ⊢ˢ .var b! : β' := by
    apply SMT.Typing.var
    exact AList.lookup_insert _
  have typ_app_x!_then :
      AList.insert b! β' (AList.insert a! α' Γ) ⊢ˢ .app (.var x!) (.var a!) : β' := by
    exact SMT.Typing.app _ _ _ _ _ typ_var_x!_then typ_var_a!_then
  have typ_eq_lhs_then :
      AList.insert b! β' (AList.insert a! α' Γ) ⊢ˢ
        ((.app (.var x!) (.var a!)) =ˢ (.var b!)) : SMTType.bool := by
    exact SMT.Typing.eq _ _ _ _ typ_app_x!_then typ_var_b!_then
  have hsub_x_body :
      Γ.entries ⊆
        (AList.insert b β (AList.insert a α (AList.insert b! β' (AList.insert a! α' Γ)))).entries := by
    intro v hv
    exact
      (SMT.TypeContext.entries_subset_insert_of_notMem b_not_mid <|
        SMT.TypeContext.entries_subset_insert_of_notMem a_not_Γa!b! <|
          SMT.TypeContext.entries_subset_insert_of_notMem b!_not_Γa! <|
            SMT.TypeContext.entries_subset_insert_of_notMem a!_not_Γ hv)
  have typ_x_body :
      AList.insert b β (AList.insert a α (AList.insert b! β' (AList.insert a! α' Γ))) ⊢ˢ
        x : α.fun β := by
    exact SMT.Typing.weakening (h := hsub_x_body) typ_x
  have typ_var_a_body :
      AList.insert b β (AList.insert a α (AList.insert b! β' (AList.insert a! α' Γ))) ⊢ˢ
        .var a : α := by
    apply SMT.Typing.var
    rw [AList.lookup_insert_ne b_ne_a.symm, AList.lookup_insert]
  have typ_app_x_body :
      AList.insert b β (AList.insert a α (AList.insert b! β' (AList.insert a! α' Γ))) ⊢ˢ
        .app x (.var a) : β := by
    exact SMT.Typing.app _ _ _ _ _ typ_x_body typ_var_a_body
  have typ_var_b_body :
      AList.insert b β (AList.insert a α (AList.insert b! β' (AList.insert a! α' Γ))) ⊢ˢ
        .var b : β := by
    apply SMT.Typing.var
    rw [AList.lookup_insert]
  have typ_eq_body :
      AList.insert b β (AList.insert a α (AList.insert b! β' (AList.insert a! α' Γ))) ⊢ˢ
        ((.app x (.var a)) =ˢ (.var b)) : SMTType.bool := by
    exact SMT.Typing.eq _ _ _ _ typ_app_x_body typ_var_b_body
  have hsub_a!_body :
      (AList.insert a α (AList.insert a! α' Γ)).entries ⊆
        (AList.insert b β (AList.insert a α (AList.insert b! β' (AList.insert a! α' Γ)))).entries := by
    intro v hv
    exact
      (SMT.TypeContext.entries_subset_insert_of_notMem b_not_mid <|
        SMT.TypeContext.insert_mono
          (SMT.TypeContext.entries_subset_insert_of_notMem b!_not_Γa!) hv)
  have typ_a!_spec_body :
      AList.insert b β (AList.insert a α (AList.insert b! β' (AList.insert a! α' Γ))) ⊢ˢ
        a!_spec : SMTType.bool := by
    exact SMT.Typing.weakening (h := hsub_a!_body) typ_exists_a_body
  have hsub_b!_1 :
      (AList.insert b! β' (AList.insert b β (AList.insert a! α' (AList.insert a α Γ)))).entries ⊆
        (AList.insert b! β' (AList.insert b β (AList.insert a α (AList.insert a! α' Γ)))).entries := by
    exact SMT.TypeContext.insert_mono (SMT.TypeContext.insert_mono hsub_exists_a)
  have hsub_b!_2 :
      (AList.insert b! β' (AList.insert b β (AList.insert a α (AList.insert a! α' Γ)))).entries ⊆
        (AList.insert b β (AList.insert b! β' (AList.insert a α (AList.insert a! α' Γ)))).entries :=
    typeContext_insert_swap_entries b_ne_b!.symm
  have hsub_b!_3_inner :
      (AList.insert b! β' (AList.insert a α (AList.insert a! α' Γ))).entries ⊆
        (AList.insert a α (AList.insert b! β' (AList.insert a! α' Γ))).entries :=
    typeContext_insert_swap_entries a_ne_b!.symm
  have hsub_b!_3 :
      (AList.insert b β (AList.insert b! β' (AList.insert a α (AList.insert a! α' Γ)))).entries ⊆
        (AList.insert b β (AList.insert a α (AList.insert b! β' (AList.insert a! α' Γ)))).entries := by
    exact SMT.TypeContext.insert_mono hsub_b!_3_inner
  have typ_b!_spec_body :
      AList.insert b β (AList.insert a α (AList.insert b! β' (AList.insert a! α' Γ))) ⊢ˢ
        b!_spec : SMTType.bool := by
    exact SMT.Typing.weakening
      (h := fun e he => hsub_b!_3 (hsub_b!_2 (hsub_b!_1 he)))
      typ_b!_spec_ctx
  have typ_and_specs_body :
      AList.insert b β (AList.insert a α (AList.insert b! β' (AList.insert a! α' Γ))) ⊢ˢ
        (a!_spec ∧ˢ b!_spec) : SMTType.bool := by
    exact SMT.Typing.and _ _ _ typ_a!_spec_body typ_b!_spec_body
  have typ_exists_ab_body :
      AList.insert b β (AList.insert a α (AList.insert b! β' (AList.insert a! α' Γ))) ⊢ˢ
        (((.app x (.var a)) =ˢ (.var b)) ∧ˢ (a!_spec ∧ˢ b!_spec)) : SMTType.bool := by
    exact SMT.Typing.and _ _ _ typ_eq_body typ_and_specs_body
  have a_in_exists_ab :
      a ∈ AList.insert b β (AList.insert a α (AList.insert b! β' (AList.insert a! α' Γ))) := by
    rw [AList.mem_insert]
    exact Or.inr (by
      rw [AList.mem_insert]
      exact Or.inl rfl)
  have b_in_exists_ab :
      b ∈ AList.insert b β (AList.insert a α (AList.insert b! β' (AList.insert a! α' Γ))) := by
    rw [AList.mem_insert]
    exact Or.inl rfl
  have fresh_exists_ab :
      ∀ v ∈ [a, b], v ∉ bv (((.app x (.var a)) =ˢ (.var b)) ∧ˢ (a!_spec ∧ˢ b!_spec)) := by
    intro v hv
    rw [List.mem_cons, List.mem_singleton] at hv
    rcases hv with rfl | rfl
    · intro hbv
      exact (SMT.Typing.bv_notMem_context typ_exists_ab_body _ hbv) a_in_exists_ab
    · intro hbv
      exact (SMT.Typing.bv_notMem_context typ_exists_ab_body _ hbv) b_in_exists_ab
  have typ_exists_ab :
      AList.insert b! β' (AList.insert a! α' Γ) ⊢ˢ
        .exists [a, b] [α, β]
          (((.app x (.var a)) =ˢ (.var b)) ∧ˢ (a!_spec ∧ˢ b!_spec)) : SMTType.bool := by
    apply SMT.Typing.exists
      (Γ := AList.insert b! β' (AList.insert a! α' Γ))
      (vs := [a, b]) (τs := [α, β]) (len_eq := rfl)
    · intro v hv
      rw [List.mem_cons, List.mem_singleton] at hv
      rcases hv with rfl | rfl
      · intro ha
        rw [AList.mem_insert] at ha
        rcases ha with ha | ha
        · exact a_ne_b! ha
        · rw [AList.mem_insert] at ha
          rcases ha with ha | ha
          · exact a_ne_a! ha
          · exact a_not ha
      · intro hb
        rw [AList.mem_insert] at hb
        rcases hb with hb | hb
        · exact b_ne_b! hb
        · exact b_not_Γa! hb
    · exact fresh_exists_ab
    · simp
    · have hupdate_exists_ab :
          SMT.TypeContext.update (AList.insert b! β' (AList.insert a! α' Γ)) [a, b] [α, β] rfl =
            AList.insert b β (AList.insert a α (AList.insert b! β' (AList.insert a! α' Γ))) := by
        unfold SMT.TypeContext.update
        simp only [List.length_cons, List.length_nil, zero_add, Fin.foldl_succ_last,
          Fin.getElem_fin, Fin.coe_cast, Fin.val_last, List.getElem_append_right,
          Nat.sub_self, List.getElem_cons_zero, Fin.coe_castSucc, Fin.foldl_zero]
        rfl
      rwa [hupdate_exists_ab]
  let bBody : Term :=
    (((.app (.var x!) (.var a!)) =ˢ (.var b!)) =ˢ
      (.exists [a, b] [α, β]
        (((.app x (.var a)) =ˢ (.var b)) ∧ˢ (a!_spec ∧ˢ b!_spec))))
  have typ_eq_rhs_then :
      AList.insert b! β' (AList.insert a! α' Γ) ⊢ˢ
        (.exists [a, b] [α, β]
          (((.app x (.var a)) =ˢ (.var b)) ∧ˢ (a!_spec ∧ˢ b!_spec))) : SMTType.bool :=
    typ_exists_ab
  have typ_eq_then :
      AList.insert b! β' (AList.insert a! α' Γ) ⊢ˢ bBody : SMTType.bool := by
    exact SMT.Typing.eq _ _ _ _ typ_eq_lhs_then typ_eq_rhs_then
  have b!_in_forall :
      b! ∈ AList.insert b! β' (AList.insert a! α' Γ) := by
    rw [AList.mem_insert]
    exact Or.inl rfl
  have fresh_forall_b :
      ∀ v ∈ [b!], v ∉ bv bBody := by
    intro v hv
    rw [List.mem_singleton] at hv
    subst hv
    intro hbv
    exact (SMT.Typing.bv_notMem_context typ_eq_then _ hbv) b!_in_forall
  have typ_forall_b :
      AList.insert a! α' Γ ⊢ˢ .forall [b!] [β'] bBody : SMTType.bool := by
    refine SMT.Typing.forall
      (Γ := AList.insert a! α' Γ) (vs := [b!]) (τs := [β']) (P := bBody)
      ?_ ?_ ?_ ?_ ?_
    · intro v hv
      rw [List.mem_singleton] at hv
      subst hv
      exact b!_not_Γa!
    · exact fresh_forall_b
    · exact Nat.succ_pos 0
    · exact rfl
    · have hupdate_forall_b :
          SMT.TypeContext.update (AList.insert a! α' Γ) [b!] [β'] rfl =
            AList.insert b! β' (AList.insert a! α' Γ) := by
        simp only [SMT.TypeContext.update, List.length_cons, List.length_nil, zero_add,
          Fin.cast_eq_self, Fin.getElem_fin, Fin.foldl_succ_last, Fin.coe_ofNat_eq_mod, Nat.mod_succ,
          List.getElem_cons_zero, Fin.last_zero, Fin.isValue, Fin.foldl_zero]
      rwa [hupdate_forall_b]
  let aBody : Term :=
    (.ite (.exists [a] [α] a!_spec) (.forall [b!] [β'] bBody) hdefault)
  have typ_ite :
      AList.insert a! α' Γ ⊢ˢ aBody : SMTType.bool := by
    exact SMT.Typing.ite _ _ _ _ _ typ_exists_a typ_forall_b typ_hdefault
  have a!_in_forall :
      a! ∈ AList.insert a! α' Γ := by
    rw [AList.mem_insert]
    exact Or.inl rfl
  have fresh_forall_a :
      ∀ v ∈ [a!], v ∉ bv aBody := by
    intro v hv
    rw [List.mem_singleton] at hv
    subst hv
    intro hbv
    exact (SMT.Typing.bv_notMem_context typ_ite _ hbv) a!_in_forall
  refine SMT.Typing.forall
    (Γ := Γ) (vs := [a!]) (τs := [α']) (P := aBody)
    ?_ ?_ ?_ ?_ ?_
  · intro v hv
    rw [List.mem_singleton] at hv
    subst hv
    exact a!_not_Γ
  · exact fresh_forall_a
  · exact Nat.succ_pos 0
  · exact rfl
  · have hupdate_forall_a :
        SMT.TypeContext.update Γ [a!] [α'] rfl =
          AList.insert a! α' Γ := by
      simp only [SMT.TypeContext.update, List.length_cons, List.length_nil, zero_add,
        Fin.cast_eq_self, Fin.getElem_fin, Fin.foldl_succ_last, Fin.coe_ofNat_eq_mod, Nat.mod_succ,
        List.getElem_cons_zero, Fin.last_zero, Fin.isValue, Fin.foldl_zero]
    rwa [hupdate_forall_a]

theorem funASpecCoversAt.{u}
    {«Δ» : RenamingContext.Context.{u}}
    {a!_spec : Term} {x! a a! : 𝒱}
    (fv_a!_spec : fv a!_spec ⊆ fv (.var a) ∪ {a!})
    (a_ne_a! : a ≠ a!) :
    ∀ (Yfun x₀ wy0 : SMT.Dom.{u}),
      RenamingContext.CoversFV
        (Function.update
          (Function.update (Function.update «Δ» x! (some Yfun)) a (some x₀))
          a! (some wy0))
        a!_spec := by
  intro Yfun x₀ wy0 v hv
  have hv' := fv_a!_spec hv
  rw [List.mem_union_iff] at hv'
  rcases hv' with hv_a | hv_a!
  · have hva : v = a := by
      rw [fv, List.mem_singleton] at hv_a
      exact hv_a
    subst v
    rw [Function.update_of_ne a_ne_a!, Function.update_self]
    rfl
  · have hva! : v = a! := List.mem_singleton.mp hv_a!
    subst v
    rw [Function.update_self]
    rfl

theorem funRemoveAllASpecUpdateIsSome.{u}
    {Δctx : RenamingContext.Context.{u}}
    {a a! : 𝒱} {a!_spec : Term}
    (fv_a!_spec : fv a!_spec ⊆ fv (.var a) ∪ {a!})
    (ha! : (Δctx a!).isSome = true) :
    ∀ v, v ∈ List.removeAll (fv a!_spec) [a] → (Δctx v).isSome = true := by
  intro v hv_remove
  have hv_spec : v ∈ fv a!_spec := (List.mem_removeAll_iff.mp hv_remove).1
  have hv_not_a : v ∉ [a] := (List.mem_removeAll_iff.mp hv_remove).2
  have hv' : v ∈ fv (.var a) ∪ {a!} := fv_a!_spec hv_spec
  rw [List.mem_union_iff] at hv'
  rcases hv' with hv_a | hv_a!
  · have hva : v = a := by
      rw [fv, List.mem_singleton] at hv_a
      exact hv_a
    exact False.elim (hv_not_a (List.mem_singleton.mpr hva))
  · have hva! : v = a! := List.mem_singleton.mp hv_a!
    subst hva!
    exact ha!

theorem funUpdateSwap.{u}
    {Δctx : RenamingContext.Context.{u}}
    {a a! : 𝒱}
    (a_ne_a! : a ≠ a!) :
    ∀ (x₀ wy0 : SMT.Dom.{u}),
      Function.update (Function.update Δctx a! (some wy0)) a (some x₀) =
        Function.update (Function.update Δctx a (some x₀)) a! (some wy0) := by
  intro x₀ wy0
  funext v
  by_cases hva : v = a
  · subst hva
    rw [Function.update_self, Function.update_of_ne a_ne_a!, Function.update_self]
  · by_cases hva! : v = a!
    · subst hva!
      rw [Function.update_of_ne hva, Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hva, Function.update_of_ne hva!,
        Function.update_of_ne hva!, Function.update_of_ne hva]

theorem funBSpecCoversAt.{u}
    {«Δ» : RenamingContext.Context.{u}}
    {b!_spec : Term} {x! a! b b! : 𝒱}
    (fv_b!_spec : fv b!_spec ⊆ fv (.var b) ∪ {b!})
    (b_ne_b! : b ≠ b!) :
    ∀ (Yfun wy0 y₀ wy1 : SMT.Dom.{u}),
      RenamingContext.CoversFV
        (Function.update
          (Function.update
            (Function.update (Function.update «Δ» x! (some Yfun)) a! (some wy0))
            b (some y₀))
          b! (some wy1))
        b!_spec := by
  intro Yfun wy0 y₀ wy1 v hv
  have hv' := fv_b!_spec hv
  rw [List.mem_union_iff] at hv'
  rcases hv' with hv_b | hv_b!
  · have hvb : v = b := by
      rw [fv, List.mem_singleton] at hv_b
      exact hv_b
    subst v
    rw [Function.update_of_ne b_ne_b!, Function.update_self]
    rfl
  · have hvb! : v = b! := List.mem_singleton.mp hv_b!
    subst v
    rw [Function.update_self]
    rfl

theorem funEqBAfterUpdateCovers.{u}
    {Δctx : RenamingContext.Context.{u}}
    {x! a! b! : 𝒱}
    (x!_ne_a! : x! ≠ a!)
    (x!_ne_b! : x! ≠ b!)
    (a!_ne_b! : a! ≠ b!) :
    ∀ (Yfun wy0 wy1 : SMT.Dom.{u}),
      RenamingContext.CoversFV
        (Function.update
          (Function.update (Function.update Δctx x! (some Yfun)) a! (some wy0))
          b! (some wy1))
        (((@ˢTerm.var x!) (Term.var a!)) =ˢ Term.var b!) := by
  intro Yfun wy0 wy1 v hv
  simp only [fv, List.mem_append, List.mem_singleton] at hv
  rcases hv with hv | hvb!
  · rcases hv with hvx! | hva!
    · subst hvx!
      rw [Function.update_of_ne x!_ne_b!]
      rw [Function.update_of_ne x!_ne_a!]
      rw [Function.update_self]
      rfl
    · subst hva!
      rw [Function.update_of_ne a!_ne_b!]
      rw [Function.update_self]
      rfl
  · subst hvb!
    rw [Function.update_self]
    rfl

theorem funDenVarExactAt.{u}
    {«Δ» : RenamingContext.Context.{u}}
    {τ τ' : SMTType} {p : τ ⇝ τ'}
    (p_ih : FunExactIH.{u} p)
    {St₁ St₂ : EncoderState} {name : String} {z z! : 𝒱} {z!_spec : Term}
    (sub : AList.keys St₁.types ⊆ St₁.env.usedVars)
    (typ_var_z : St₁.types ⊢ˢ .var z : τ)
    (hrun : Id.run ((loosenAux_prf name p (.var z)) St₁) = Except.ok ((z!, z!_spec), St₂)) :
    ∀ (x₀ : SMT.Dom) (hx₀_ty : x₀.snd.fst = τ),
      ∃ Φ X₀!,
        ∃ (_ :
          ⟦(Term.var z!).abstract
              (Function.update (Function.update «Δ» z (some x₀)) z! (some X₀!))
              (by
                intro v hv
                rw [fv, List.mem_singleton] at hv
                subst hv
                simp [Function.update])⟧ˢ =
            some X₀!)
          (hφ :
            RenamingContext.CoversFV
              (Function.update (Function.update «Δ» z (some x₀)) z! (some X₀!))
              z!_spec)
          (_ :
            ⟦z!_spec.abstract
                (Function.update (Function.update «Δ» z (some x₀)) z! (some X₀!))
                hφ⟧ˢ =
              some Φ),
          Φ.snd.fst = SMTType.bool ∧
            (Φ.fst = zftrue ∧ x₀.fst.pair X₀!.fst ∈ (castZF_of_path p).1) ∧
              ∀ (Y : SMT.Dom),
                Y.snd.fst = τ' →
                  ∀ (hφY :
                    RenamingContext.CoversFV
                      (Function.update (Function.update «Δ» z (some x₀)) z! (some Y))
                      z!_spec),
                    ⟦z!_spec.abstract
                        (Function.update (Function.update «Δ» z (some x₀)) z! (some Y))
                        hφY⟧ˢ.isSome =
                      true ∧
                      ∀ {ΦY : SMT.Dom},
                        ⟦z!_spec.abstract
                            (Function.update (Function.update «Δ» z (some x₀)) z! (some Y))
                            hφY⟧ˢ =
                          some ΦY →
                          ΦY.fst = zftrue →
                            x₀.fst.pair Y.fst ∈ (castZF_of_path p).1 := by
  intro x₀ hx₀_ty
  let Δx₀ : RenamingContext.Context := Function.update «Δ» z (some x₀)
  have hcov_var_z_x₀ : RenamingContext.CoversFV Δx₀ (.var z) := by
    intro v hv
    rw [fv, List.mem_singleton] at hv
    subst hv
    simp only [Function.update_self, Option.isSome_some, Δx₀]
  have pf_var_z_x₀ : FunPf Δx₀ := by
    intro xz! Xz! v hv
    rw [fv, List.mem_singleton] at hv
    subst hv
    rw [Function.update_self]
    rfl
  have ih_var_z_x₀ := p_ih
    (Λ := St₁.types) (n := St₁.env.freshvarsc) (used := St₁.env.usedVars)
    (name := name) (x := .var z) typ_var_z Δx₀ hcov_var_z_x₀ pf_var_z_x₀
  have post_x₀ := ih_var_z_x₀ St₁ (by exact ⟨rfl, rfl, sub, rfl⟩)
  simp only [wp, PredTrans.pushArg_apply, PredTrans.pushExcept_apply, PredTrans.pure_apply] at post_x₀
  rw [hrun] at post_x₀
  have hden_var_z_x₀ :
      ⟦(Term.var z).abstract Δx₀ hcov_var_z_x₀⟧ˢ = some x₀ := by
    rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some_inj]
    apply Option.get_of_eq_some
    simp only [Function.update_self, Δx₀]
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hden_z_x₀⟩ := post_x₀
  exact hden_z_x₀ x₀ hden_var_z_x₀

theorem funDefaultSpecAt.{u}
    {«Δ» : RenamingContext.Context.{u}}
    {τ : SMTType}
    {St₁ St₂ : EncoderState} {name : String} {t spec : Term}
    (sub : AList.keys St₁.types ⊆ St₁.env.usedVars)
    (typ_t : St₁.types ⊢ˢ t : τ)
    (ht : RenamingContext.CoversFV «Δ» t)
    (hrun : Id.run ((defaultSpecM name τ t) St₁) = Except.ok (spec, St₂)) :
    ∀ (Y : SMT.Dom.{u}) (den_t : ⟦t.abstract «Δ» ht⟧ˢ = some Y),
      ∃ (hφ : RenamingContext.CoversFV «Δ» spec) (Φ : SMT.Dom.{u}),
        ⟦spec.abstract «Δ» hφ⟧ˢ = some Φ ∧
          Φ.snd.fst = SMTType.bool ∧
          (Y.fst = τ.defaultZFSet → Φ.fst = zftrue) := by
  intro Y den_t
  have hspec := defaultSpecMSpec.{u}
    («Δ» := «Δ») (Γ := St₁.types) (n := St₁.env.freshvarsc) (used := St₁.env.usedVars)
    (name := name) (t := t) typ_t ht
  have post := hspec St₁ (by exact ⟨rfl, rfl, sub, rfl⟩)
  simp only [wp, PredTrans.pushArg_apply, PredTrans.pushExcept_apply, PredTrans.pure_apply] at post
  rw [hrun] at post
  obtain ⟨_, _, _, _, _, _, _, hden_spec⟩ := post
  exact hden_spec «Δ» ht Y den_t

theorem funVarDenTrueAtCast.{u}
    {«Δ» : RenamingContext.Context.{u}}
    {τ τ' : SMTType} {p : τ ⇝ τ'}
    {x₀ Y X₀! Φ : SMT.Dom.{u}} {z! : 𝒱} {z!_spec : Term}
    (hx₀_ty : x₀.snd.fst = τ)
    (hX₀_ty : X₀!.snd.fst = τ')
    (hY_ty : Y.snd.fst = τ')
    (hcast_X₀! : x₀.fst.pair X₀!.fst ∈ (castZF_of_path p).1)
    (hcast_Y : x₀.fst.pair Y.fst ∈ (castZF_of_path p).1)
    (hφ : RenamingContext.CoversFV (Function.update «Δ» z! (some X₀!)) z!_spec)
    (hden :
      ⟦z!_spec.abstract
          (Function.update «Δ» z! (some X₀!))
          hφ⟧ˢ =
        some Φ)
    (htrue : Φ.fst = zftrue) :
    ∃ (hφY : RenamingContext.CoversFV (Function.update «Δ» z! (some Y)) z!_spec) (ΦY : SMT.Dom.{u}),
      ⟦z!_spec.abstract (Function.update «Δ» z! (some Y)) hφY⟧ˢ = some ΦY ∧
        ΦY.fst = zftrue := by
  have hx₀_mem : x₀.fst ∈ ⟦τ⟧ᶻ := by
    rw [← hx₀_ty]
    exact x₀.snd.snd
  have hcast : ZFSet.IsFunc ⟦τ⟧ᶻ ⟦τ'⟧ᶻ (castZF_of_path p).1 :=
    (castZF_of_path p).2
  have hx₀_dom_cast : x₀.fst ∈ (castZF_of_path p).1.Dom := by
    simpa [ZFSet.is_func_dom_eq hcast] using hx₀_mem
  have hcast_x₀_X₀! :
      @ᶻ(castZF_of_path p).1 ⟨x₀.fst, hx₀_dom_cast⟩ = X₀!.fst := by
    have hpair := ZFSet.fapply.of_pair (ZFSet.is_func_is_pfunc hcast) hcast_X₀!
    simpa only [Subtype.ext_iff] using hpair
  have hcast_x₀_Y :
      @ᶻ(castZF_of_path p).1 ⟨x₀.fst, hx₀_dom_cast⟩ = Y.fst := by
    have hpair := ZFSet.fapply.of_pair (ZFSet.is_func_is_pfunc hcast) hcast_Y
    simpa only [Subtype.ext_iff] using hpair
  have hfst_eq : X₀!.fst = Y.fst := by
    rw [← hcast_x₀_X₀!, ← hcast_x₀_Y]
  have hX₀_eq_Y : X₀! = Y := by
    cases X₀! with
    | mk xX hX =>
        cases hX with
        | mk τX hxX =>
            cases Y with
            | mk yY hY =>
                cases hY with
                | mk τY hyY =>
                    cases hX₀_ty
                    cases hY_ty
                    change xX = yY at hfst_eq
                    subst hfst_eq
                    have hproof : HEq hxX hyY := by
                      apply proof_irrel_heq
                    cases hproof
                    rfl
  subst hX₀_eq_Y
  refine ⟨?_, Φ, hden, htrue⟩
  simpa [proof_irrel_heq] using hφ

theorem funVarSpecTotalAt.{u}
    {«Δ» : RenamingContext.Context.{u}}
    {τ τ' : SMTType} {p : τ ⇝ τ'}
    (p_ih : FunExactIH.{u} p)
    {St₁ St₂ : EncoderState} {name : String} {z z! : 𝒱} {z!_spec : Term}
    (sub : AList.keys St₁.types ⊆ St₁.env.usedVars)
    (typ_var_z : St₁.types ⊢ˢ .var z : τ)
    (hrun : Id.run ((loosenAux_prf name p (.var z)) St₁) = Except.ok ((z!, z!_spec), St₂))
    (x₀ wy0 : SMT.Dom.{u})
    (hx₀_ty : x₀.snd.fst = τ)
    (hwy0_ty : wy0.snd.fst = τ')
    (hφY :
      RenamingContext.CoversFV
        (Function.update (Function.update «Δ» z (some x₀)) z! (some wy0))
        z!_spec) :
    ⟦z!_spec.abstract
        (Function.update (Function.update «Δ» z (some x₀)) z! (some wy0))
        hφY⟧ˢ.isSome =
      true := by
  obtain ⟨_, _, _, _, _, _, _, htot⟩ :=
    funDenVarExactAt
      («Δ» := «Δ») (p := p) p_ih
      (sub := sub) (typ_var_z := typ_var_z) (hrun := hrun)
      x₀ hx₀_ty
  exact (htot wy0 hwy0_ty hφY).1

theorem funVarSpecTrueImpliesCast.{u}
    {«Δ» : RenamingContext.Context.{u}}
    {τ τ' : SMTType} {p : τ ⇝ τ'}
    (p_ih : FunExactIH.{u} p)
    {St₁ St₂ : EncoderState} {name : String} {z z! : 𝒱} {z!_spec : Term}
    (sub : AList.keys St₁.types ⊆ St₁.env.usedVars)
    (typ_var_z : St₁.types ⊢ˢ .var z : τ)
    (hrun : Id.run ((loosenAux_prf name p (.var z)) St₁) = Except.ok ((z!, z!_spec), St₂))
    (x₀ wy0 : SMT.Dom.{u})
    (hx₀_ty : x₀.snd.fst = τ)
    (hwy0_ty : wy0.snd.fst = τ')
    (hφY :
      RenamingContext.CoversFV
        (Function.update (Function.update «Δ» z (some x₀)) z! (some wy0))
        z!_spec)
    {ΦY : SMT.Dom.{u}}
    (hdenY :
      ⟦z!_spec.abstract
          (Function.update (Function.update «Δ» z (some x₀)) z! (some wy0))
          hφY⟧ˢ =
        some ΦY)
    (htrue : ΦY.fst = zftrue) :
    x₀.fst.pair wy0.fst ∈ (castZF_of_path p).1 := by
  obtain ⟨_, _, _, _, _, _, _, htot⟩ :=
    funDenVarExactAt
      («Δ» := «Δ») (p := p) p_ih
      (sub := sub) (typ_var_z := typ_var_z) (hrun := hrun)
      x₀ hx₀_ty
  exact (htot wy0 hwy0_ty hφY).2 hdenY htrue

theorem funVarSpecTrueAtCast.{u}
    {«Δ» : RenamingContext.Context.{u}}
    {τ τ' : SMTType} {p : τ ⇝ τ'}
    (p_ih : FunExactIH.{u} p)
    {St₁ St₂ : EncoderState} {name : String} {z z! : 𝒱} {z!_spec : Term}
    (sub : AList.keys St₁.types ⊆ St₁.env.usedVars)
    (typ_var_z : St₁.types ⊢ˢ .var z : τ)
    (typ_var_z! : St₂.types ⊢ˢ .var z! : τ')
    (hrun : Id.run ((loosenAux_prf name p (.var z)) St₁) = Except.ok ((z!, z!_spec), St₂))
    (x₀ wy0 : SMT.Dom.{u})
    (hx₀_ty : x₀.snd.fst = τ)
    (hwy0_ty : wy0.snd.fst = τ')
    (hcast : x₀.fst.pair wy0.fst ∈ (castZF_of_path p).1) :
    ∃ (hφY :
      RenamingContext.CoversFV
        (Function.update (Function.update «Δ» z (some x₀)) z! (some wy0))
        z!_spec) (ΦY : SMT.Dom.{u}),
      ⟦z!_spec.abstract
          (Function.update (Function.update «Δ» z (some x₀)) z! (some wy0))
          hφY⟧ˢ =
        some ΦY ∧
      ΦY.fst = zftrue := by
  obtain ⟨Φ, X₀!, hden_var, hφ, hden, _, htrue_cast, _⟩ :=
    funDenVarExactAt
      («Δ» := «Δ») (p := p) p_ih
      (sub := sub) (typ_var_z := typ_var_z) (hrun := hrun)
      x₀ hx₀_ty
  obtain ⟨htrue, hcast_X₀!⟩ := htrue_cast
  have hX₀_ty : X₀!.snd.fst = τ' := by
    exact denote_type_eq_of_typing (typ_t := typ_var_z!) (hden := hden_var)
  exact funVarDenTrueAtCast
    («Δ» := Function.update «Δ» z (some x₀))
    (p := p)
    (hx₀_ty := hx₀_ty)
    (hX₀_ty := hX₀_ty)
    (hY_ty := hwy0_ty)
    (hcast_X₀! := hcast_X₀!)
    (hcast_Y := hcast)
    (hφ := hφ)
    (hden := hden)
    (htrue := htrue)

theorem funDefaultTrueImpliesDefaultAt.{u}
    {«Δ» : RenamingContext.Context.{u}}
    {τ : SMTType}
    {St₁ St₂ : EncoderState} {name : String} {t spec : Term}
    (sub : AList.keys St₁.types ⊆ St₁.env.usedVars)
    (typ_t : St₁.types ⊢ˢ t : τ)
    (ht : RenamingContext.CoversFV «Δ» t)
    (hrun : Id.run ((defaultSpecM name τ t) St₁) = Except.ok (spec, St₂)) :
    ∀ (Y : SMT.Dom.{u}) (den_t : ⟦t.abstract «Δ» ht⟧ˢ = some Y)
      (hφ : RenamingContext.CoversFV «Δ» spec) {Φ : SMT.Dom.{u}},
      ⟦spec.abstract «Δ» hφ⟧ˢ = some Φ →
        Φ.fst = zftrue →
        Y.fst = τ.defaultZFSet := by
  intro Y den_t hφ Φ hdenΦ htrue
  have hspec := defaultSpecMTrueImpliesDefault.{u}
    («Δ» := «Δ») (Γ := St₁.types) (n := St₁.env.freshvarsc) (used := St₁.env.usedVars)
    (name := name) (t := t) typ_t ht
  have post := hspec St₁ (by exact ⟨rfl, rfl, sub, rfl⟩)
  simp only [wp, PredTrans.pushArg_apply, PredTrans.pushExcept_apply, PredTrans.pure_apply] at post
  rw [hrun] at post
  obtain ⟨_, _, _, _, _, _, hconv⟩ := post
  exact hconv «Δ» ht Y den_t hφ hdenΦ htrue

theorem funRunVarSpec
    {τ τ' : SMTType} {p : τ ⇝ τ'}
    {name : String} {z : 𝒱} {St : EncoderState} :
    ⦃fun st => ⌜st = St⌝⦄
      loosenAux_prf name p (.var z)
    ⦃PostCond.mayThrow fun out st =>
      ⌜StateT.run (loosenAux_prf name p (.var z)) St =
        Except.ok (out, st)⌝⦄ := by
  unfold Std.Do.Triple
  intro st hst
  subst st
  simp only [wp, PredTrans.pushArg_apply, PredTrans.pushExcept_apply, PredTrans.pure_apply]
  cases hrun : Id.run ((loosenAux_prf name p (.var z)) St) with
  | error e =>
      trivial
  | ok a =>
      simpa using hrun

theorem funRunDefaultSpec
    {τ : SMTType}
    {name : String} {t : Term} {St : EncoderState} :
    ⦃fun st => ⌜st = St⌝⦄
      defaultSpecM name τ t
    ⦃PostCond.mayThrow fun spec st =>
      ⌜StateT.run (defaultSpecM name τ t) St =
        Except.ok (spec, st)⌝⦄ := by
  unfold Std.Do.Triple
  intro st hst
  subst st
  simp only [wp, PredTrans.pushArg_apply, PredTrans.pushExcept_apply, PredTrans.pure_apply]
  cases hrun : Id.run ((defaultSpecM name τ t) St) with
  | error e =>
      trivial
  | ok a =>
      simpa using hrun

theorem funUnaryTarget
    {α : SMTType} {y : ZFSet}
    (hy : y ∈ ⟦α⟧ᶻ) :
    y.hasArity 1 ∧ ∀ i : Fin 1, y ∈ ⟦[α][i]⟧ᶻ := by
  constructor
  · simp [ZFSet.hasArity]
  · intro i
    have hi0 : i = ⟨0, by simp⟩ := by
      apply Fin.ext
      simp
    cases hi0
    exact hy

theorem funSingletonArg
    {τ : SMTType} {x : ZFSet}
    (hx : x ∈ ⟦τ⟧ᶻ) :
    ∀ i : Fin [τ].length,
      (⟨x, τ, hx⟩ : SMT.Dom).snd.fst = [τ][i] ∧
        (⟨x, τ, hx⟩ : SMT.Dom).fst ∈ ⟦[τ][i]⟧ᶻ := by
  intro i
  have hi0 : i = ⟨0, by simp⟩ := by
    apply Fin.ext
    simp
  cases hi0
  exact ⟨rfl, hx⟩

theorem defaultZFSetFunIsFunc
    {α β : SMTType} :
    ZFSet.IsFunc ⟦α⟧ᶻ ⟦β⟧ᶻ (SMTType.defaultZFSet (α.fun β)) := by
  rw [←ZFSet.mem_funs]
  exact SMTType.mem_toZFSet_of_defaultZFSet (α := α.fun β)

theorem defaultZFSetFunApp
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

theorem denoteAndTrueComponents
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

theorem sInterSepEqZftrueImpliesForallEqZftrue
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

theorem sInterSepEqZffalseImpliesExistsEqZffalse
    {D : ZFSet} {F : ZFSet → ZFSet}
    (hbool : ∀ x ∈ D, F x ∈ 𝔹)
    (hne : ∃ x, x ∈ D)
    (hsInter :
      (⋂₀ (ZFSet.sep (fun y => ∃ x ∈ D, y = F x) 𝔹) : ZFSet) = zffalse) :
    ∃ x ∈ D, F x = zffalse := by
  by_contra hno
  have hall_true : ∀ x ∈ D, F x = zftrue := by
    intro x hx
    have hFx_bool : F x ∈ 𝔹 := hbool x hx
    rw [ZFSet.ZFBool.mem_𝔹_iff] at hFx_bool
    rcases hFx_bool with hFx_false | hFx_true
    · exact False.elim (hno ⟨x, hx, hFx_false⟩)
    · exact hFx_true
  have hsInter_true :
      (⋂₀ (ZFSet.sep (fun y => ∃ x ∈ D, y = F x) 𝔹) : ZFSet) = zftrue := by
    exact sInter_sep_eq_zftrue_of_forall_eq_zftrue hne hall_true
  exact ZFSet.zftrue_ne_zffalse (hsInter_true.symm.trans hsInter)

theorem funDomEqOfTyEqAndFstEq
    {x y : ZFSet} {τ₁ τ₂ : SMTType}
    {hx : x ∈ ⟦τ₁⟧ᶻ} {hy : y ∈ ⟦τ₂⟧ᶻ}
    (hτ : τ₁ = τ₂) (hxy : x = y) :
    (⟨x, τ₁, hx⟩ : SMT.Dom) = ⟨y, τ₂, hy⟩ := by
  cases hτ
  cases hxy
  have hmem : hx = hy := Subsingleton.elim _ _
  cases hmem
  rfl

theorem funDenoteAppAt
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
      RenamingContext.CoversFV (Function.update Δctx x (some Xarg)) (.app t (.var x)) := by
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
  obtain ⟨y, τ, hy⟩ := Y
  cases hY_ty
  have hcov_var :
      RenamingContext.CoversFV (Function.update Δctx x (some Xarg)) (Term.var x) := by
    intro v hv
    rw [fv, List.mem_singleton] at hv
    subst hv
    simp [Function.update]
  have hden_var :
      ⟦(Term.var x).abstract (Function.update Δctx x (some Xarg)) hcov_var⟧ˢ = some Xarg := by
    rw [SMT.Term.abstract.eq_def, SMT.denote, Option.pure_def, Option.some.injEq]
    apply Option.get_of_eq_some
    exact Function.update_self _ _ _
  rw [SMT.Term.abstract, SMT.denote, den_t_upd Xarg, hden_var]
  simp only
  dsimp [Dapp]
  have hy_pfunc : y.IsPFunc ⟦α⟧ᶻ ⟦β⟧ᶻ := ZFSet.is_func_is_pfunc hY_func
  rw [if_pos hXarg_ty.symm, dif_pos hy_pfunc]
  have hx_dom : Xarg.fst ∈ y.Dom := by
    simpa [ZFSet.is_func_dom_eq hY_func] using hXarg_mem
  rw [dif_pos hx_dom]

theorem funDenoteAppAtFst
    {Δctx : RenamingContext.Context} {t : Term} {x : 𝒱}
    {α β γ : SMTType} {Y : SMT.Dom}
    (hcov_t_upd :
      ∀ Xarg : SMT.Dom,
        RenamingContext.CoversFV (Function.update Δctx x (some Xarg)) t)
    (den_t_upd :
      ∀ Xarg : SMT.Dom,
        ⟦t.abstract (Function.update Δctx x (some Xarg)) (hcov_t_upd Xarg)⟧ˢ = some Y)
    (hY_ty : Y.snd.fst = α.fun β)
    (hY_func : ZFSet.IsFunc ⟦α⟧ᶻ ⟦β⟧ᶻ Y.fst)
    (Xarg : SMT.Dom)
    (hXarg_ty : Xarg.snd.fst = α.pair γ)
    (hXarg_mem : Xarg.fst ∈ ⟦α.pair γ⟧ᶻ) :
    ∃ hcov_app :
        RenamingContext.CoversFV (Function.update Δctx x (some Xarg))
          (.app t (.fst (.var x))),
      ∃ Dapp : SMT.Dom,
        Dapp.snd.fst = β ∧
          Dapp.fst =
            @ᶻY.fst
              ⟨Xarg.fst.π₁, by
                have hπ₁_mem : Xarg.fst.π₁ ∈ ⟦α⟧ᶻ := by
                  rw [SMTType.toZFSet, ZFSet.mem_prod] at hXarg_mem
                  obtain ⟨a, ha, b, _, hab⟩ := hXarg_mem
                  rw [hab, ZFSet.π₁_pair]
                  exact ha
                simpa [ZFSet.is_func_dom_eq hY_func] using hπ₁_mem⟩ ∧
          ⟦(Term.app t (.fst (.var x))).abstract
              (Function.update Δctx x (some Xarg)) hcov_app⟧ˢ = some Dapp := by
  have hπ₁_mem : Xarg.fst.π₁ ∈ ⟦α⟧ᶻ := by
    rw [SMTType.toZFSet, ZFSet.mem_prod] at hXarg_mem
    obtain ⟨a, ha, b, _, hab⟩ := hXarg_mem
    rw [hab, ZFSet.π₁_pair]
    exact ha
  let hcov_app :
      RenamingContext.CoversFV (Function.update Δctx x (some Xarg))
        (.app t (.fst (.var x))) := by
    intro v hv
    simp only [SMT.fv, List.mem_append, List.mem_singleton] at hv
    rcases hv with hv | hv
    · exact hcov_t_upd Xarg v hv
    · subst hv
      simp
  let Dapp : SMT.Dom :=
    ⟨@ᶻY.fst
        ⟨Xarg.fst.π₁, by
          simpa [ZFSet.is_func_dom_eq hY_func] using hπ₁_mem⟩,
      β,
      by
        have hY_mem : Y.fst ∈ ⟦α⟧ᶻ.funs ⟦β⟧ᶻ := ZFSet.mem_funs.mpr hY_func
        rw [ZFSet.mem_funs] at hY_mem
        obtain ⟨y, hy_pair, hy_unique⟩ := hY_mem.2 Xarg.fst.π₁ hπ₁_mem
        have hEq :
            ZFSet.fapply Y.fst (ZFSet.is_func_is_pfunc hY_func)
              ⟨Xarg.fst.π₁, by
                simpa [ZFSet.is_func_dom_eq hY_func] using hπ₁_mem⟩ = y := by
          exact congrArg Subtype.val
            (ZFSet.fapply.of_pair (hf := ZFSet.is_func_is_pfunc hY_func) hy_pair)
        have hy_mem : y ∈ ⟦β⟧ᶻ := by
          have hy_prod : Xarg.fst.π₁.pair y ∈ ⟦α⟧ᶻ.prod ⟦β⟧ᶻ := hY_mem.1 hy_pair
          rw [ZFSet.pair_mem_prod] at hy_prod
          exact hy_prod.2
        rw [hEq]
        exact hy_mem⟩
  refine ⟨hcov_app, Dapp, rfl, rfl, ?_⟩
  obtain ⟨y, τ, hy⟩ := Y
  cases hY_ty
  -- Decompose Xarg: its type is α.pair γ
  obtain ⟨Xv, Xτ, Xh⟩ := Xarg
  simp only at hXarg_ty hXarg_mem hπ₁_mem
  subst hXarg_ty
  have hcov_var :
      RenamingContext.CoversFV (Function.update Δctx x (some ⟨Xv, α.pair γ, Xh⟩))
        (Term.var x) := by
    intro v hv
    rw [fv, List.mem_singleton] at hv
    subst hv
    simp [Function.update]
  have hden_var :
      ⟦(Term.var x).abstract (Function.update Δctx x (some ⟨Xv, α.pair γ, Xh⟩))
          hcov_var⟧ˢ = some ⟨Xv, α.pair γ, Xh⟩ := by
    rw [SMT.Term.abstract.eq_def, SMT.denote, Option.pure_def, Option.some.injEq]
    apply Option.get_of_eq_some
    exact Function.update_self _ _ _
  have hcov_fst_var :
      RenamingContext.CoversFV (Function.update Δctx x (some ⟨Xv, α.pair γ, Xh⟩))
        (Term.fst (Term.var x)) := by
    intro v hv
    rw [fv] at hv
    exact hcov_var v hv
  have hden_fst_var :
      ⟦(Term.fst (Term.var x)).abstract
          (Function.update Δctx x (some ⟨Xv, α.pair γ, Xh⟩)) hcov_fst_var⟧ˢ =
        some ⟨Xv.π₁, α, hπ₁_mem⟩ := by
    unfold SMT.Term.abstract
    simp only [SMT.denote, hden_var]
    rfl
  rw [SMT.Term.abstract, SMT.denote, den_t_upd ⟨Xv, α.pair γ, Xh⟩, hden_fst_var]
  simp only
  dsimp [Dapp]
  have hy_pfunc : y.IsPFunc ⟦α⟧ᶻ ⟦β⟧ᶻ := ZFSet.is_func_is_pfunc hY_func
  rw [if_pos rfl, dif_pos hy_pfunc]
  have hx_dom : Xv.π₁ ∈ y.Dom := by
    simpa [ZFSet.is_func_dom_eq hY_func] using hπ₁_mem
  rw [dif_pos hx_dom]

theorem funUnaryForallTotal.{u}
    {Δctx : RenamingContext.Context.{u}} {a : Term} {v : 𝒱} {τ : SMTType}
    (hφ_forall : RenamingContext.CoversFV Δctx (Term.forall [v] [τ] a))
    (hgo_cov : ∀ x ∈ fv a, x ∉ [v] → (Δctx x).isSome = true)
    (hcov_a_upd :
      ∀ W : SMT.Dom.{u},
        RenamingContext.CoversFV (Function.update Δctx v (some W)) a)
    (hbody_total :
      ∀ W : SMT.Dom.{u}, W.snd.fst = τ →
        ⟦a.abstract (Function.update Δctx v (some W)) (hcov_a_upd W)⟧ˢ.isSome = true) :
    ⟦(Term.forall [v] [τ] a).abstract Δctx hφ_forall⟧ˢ.isSome = true := by
  rw [SMT.Term.abstract, dif_pos (by rfl), SMT.denote]
  have hlen : [v].length > 0 := by
    simp
  rw [dif_pos hlen]
  split_ifs with hsome
  · simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_one_sub_one,
    List.getElem_cons_succ, Fin.zero_eta, Fin.isValue, Nat.zero_mod, List.getElem_cons_zero,
    get.eq_1, Option.pure_def, Option.isSome_some]
  · exfalso
    apply hsome
    intro x_1 hx_1
    have hgo :=
      funAbstractGoSingle
        (Δctx := Δctx) (P := a) (v := v) (τ := τ)
        hgo_cov hcov_a_upd x_1 (by
          intro i
          have hi0 : i = ⟨0, by simp⟩ := by
            apply Fin.ext
            simp
          cases hi0
          simpa using hx_1 ⟨0, by simp⟩)
    rw [hgo]
    let W : SMT.Dom := x_1 ⟨0, by simp⟩
    have hW_ty : W.snd.fst = τ := by
      simpa [W] using (hx_1 ⟨0, by simp⟩).1
    simpa [W] using hbody_total W hW_ty

theorem funUnaryForallEqZftrue.{u}
    {Δctx : RenamingContext.Context.{u}} {a : Term} {v : 𝒱} {τ : SMTType}
    (hφ_forall : RenamingContext.CoversFV Δctx (Term.forall [v] [τ] a))
    (hgo_cov : ∀ x ∈ fv a, x ∉ [v] → (Δctx x).isSome = true)
    (hcov_a_upd :
      ∀ W : SMT.Dom.{u},
        RenamingContext.CoversFV (Function.update Δctx v (some W)) a)
    (hbody_total :
      ∀ W : SMT.Dom.{u}, W.snd.fst = τ →
        ⟦a.abstract (Function.update Δctx v (some W)) (hcov_a_upd W)⟧ˢ.isSome = true)
    (hbody_ty :
      ∀ W : SMT.Dom.{u}, W.snd.fst = τ →
        ∀ {D : SMT.Dom.{u}},
          ⟦a.abstract (Function.update Δctx v (some W)) (hcov_a_upd W)⟧ˢ = some D →
            D.snd.fst = SMTType.bool)
    (hbody_true :
      ∀ W : SMT.Dom.{u}, W.snd.fst = τ →
        ∃ D : SMT.Dom.{u},
          ⟦a.abstract (Function.update Δctx v (some W)) (hcov_a_upd W)⟧ˢ = some D ∧
            D.fst = zftrue) :
    ⟦(Term.forall [v] [τ] a).abstract Δctx hφ_forall⟧ˢ =
      some ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
  rw [SMT.Term.abstract, dif_pos (by rfl), SMT.denote]
  have hlen : [v].length > 0 := by
    simp
  rw [dif_pos hlen]
  have hbody_total' :
      ∀ {x_1 : Fin [v].length → SMT.Dom.{u}},
        (∀ i,
          ((x_1 i).snd.fst =
              match i with
              | ⟨i, hi⟩ => [τ][i]) ∧
            (x_1 i).fst ∈
              ⟦match i with
                | ⟨i, hi⟩ => [τ][i]⟧ᶻ) →
          ⟦(Term.abstract.go a [v] Δctx hgo_cov).uncurry x_1⟧ˢ.isSome = true := by
    intro x_1 hx_1
    have hgo :=
      funAbstractGoSingle
        (Δctx := Δctx) (P := a) (v := v) (τ := τ)
        hgo_cov hcov_a_upd x_1 (by
          intro i
          have hi0 : i = ⟨0, by simp⟩ := by
            apply Fin.ext
            simp
          cases hi0
          simpa using hx_1 ⟨0, by simp⟩)
    rw [hgo]
    let W : SMT.Dom := x_1 ⟨0, by simp⟩
    have hW_ty : W.snd.fst = τ := by
      simpa [W] using (hx_1 ⟨0, by simp⟩).1
    simpa [W] using hbody_total W hW_ty
  split_ifs with hsome
  · simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_one_sub_one,
      List.getElem_cons_succ, Fin.zero_eta, Fin.isValue, Fin.coe_ofNat_eq_mod,
      Nat.zero_mod, List.getElem_cons_zero, Fin.val_eq_zero, get.eq_1, forall_const,
      Option.pure_def, Option.failure_eq_none, Option.bind_some, Fin.foldl_zero]
    let sInterGoal : ZFSet :=
      ⋂₀
        ZFSet.sep
          (fun y =>
            ∃ x_1 ∈ ⟦τ⟧ᶻ,
              y =
                if hx : x_1.hasArity 1 ∧ ∀ i : Fin 1, x_1 ∈ ⟦[τ][↑i]⟧ᶻ then
                  (⟦(Term.abstract.go a [v] Δctx hgo_cov).uncurry
                      (fun i => ⟨x_1, [τ][↑i], hx.2 i⟩)⟧ˢ.get
                    (hsome (by
                      intro i
                      exact ⟨rfl, hx.2 i⟩))).fst
                else zffalse)
          𝔹
    let Φ : SMT.Dom :=
      ⟨sInterGoal, SMTType.bool, ZFSet.sInter_sep_subset_of_𝔹_mem_𝔹 (fun _ => id)⟩
    have hsInter_eq :
        sInterGoal =
          (⋂₀
            ZFSet.sep
              (fun y =>
                ∃ x_1 ∈ ⟦τ⟧ᶻ,
                  y =
                    if h : x_1.hasArity 1 ∧ x_1 ∈ ⟦τ⟧ᶻ then
                      (⟦(Term.abstract.go a [v] Δctx hgo_cov).uncurry
                          (fun _ => ⟨x_1, τ, h.2⟩)⟧ˢ.get
                        (hbody_total' (by
                          intro i
                          have hi0 : i = ⟨0, by simp⟩ := by
                            apply Fin.ext
                            simp
                          cases hi0
                          exact ⟨rfl, h.2⟩))).fst
                    else zffalse)
              𝔹 : ZFSet) := by
      dsimp [sInterGoal]
      congr
      ext y
      have hbody_eq {x_1 : ZFSet} (hx_1 : x_1 ∈ ⟦τ⟧ᶻ) :
          (if hx : x_1.hasArity 1 ∧ ∀ i : Fin 1, x_1 ∈ ⟦[τ][↑i]⟧ᶻ then
            (⟦(Term.abstract.go a [v] Δctx hgo_cov).uncurry
                (fun i => ⟨x_1, [τ][↑i], hx.2 i⟩)⟧ˢ.get
              (hsome (by
                intro i
                exact ⟨rfl, hx.2 i⟩))).fst
          else zffalse) =
          (if h : x_1.hasArity 1 ∧ x_1 ∈ ⟦τ⟧ᶻ then
            (⟦(Term.abstract.go a [v] Δctx hgo_cov).uncurry
                (fun _ => ⟨x_1, τ, h.2⟩)⟧ˢ.get
              (hbody_total' (by
                intro i
                have hi0 : i = ⟨0, by simp⟩ := by
                  apply Fin.ext
                  simp
                cases hi0
                exact ⟨rfl, h.2⟩))).fst
          else zffalse) := by
        by_cases h : x_1.hasArity 1 ∧ x_1 ∈ ⟦τ⟧ᶻ
        · have hx : x_1.hasArity 1 ∧ ∀ i : Fin 1, x_1 ∈ ⟦[τ][↑i]⟧ᶻ := by
            constructor
            · exact h.1
            · rintro ⟨i, hi⟩
              rw [Nat.lt_one_iff] at hi
              subst hi
              simp only [Fin.zero_eta, Fin.isValue, Fin.getElem_fin, Nat.reduceAdd, Fin.val_eq_zero,
                List.getElem_cons_zero]
              exact h.2
          simp only [hx, Fin.getElem_fin, Fin.val_eq_zero, List.getElem_cons_zero, h, implies_true,
            and_self, ↓reduceDIte, List.length_cons, List.length_nil, Nat.reduceAdd]
        · have hx : ¬ (x_1.hasArity 1 ∧ ∀ i : Fin 1, x_1 ∈ ⟦[τ][↑i]⟧ᶻ) := by
            intro hx
            apply h
            constructor
            · exact hx.1
            · simpa using hx.2 ⟨0, hlen⟩
          simp only [Fin.getElem_fin, Fin.val_eq_zero, List.getElem_cons_zero, forall_const, h,
            ↓reduceDIte]
      constructor
      · rintro ⟨x_1, hx_1, hy⟩
        refine ⟨x_1, ?_, hy.trans (hbody_eq (by simpa [Fin.foldl_zero] using hx_1))⟩
        simpa [Fin.foldl_zero] using hx_1
      · rintro ⟨x_1, hx_1, hy⟩
        refine ⟨x_1, ?_, hy.trans (hbody_eq hx_1).symm⟩
        simpa [Fin.foldl_zero] using hx_1
    have hsInter_true :
        (⋂₀
          ZFSet.sep
            (fun y =>
              ∃ x_1 ∈ ⟦τ⟧ᶻ,
                y =
                  if h : x_1.hasArity 1 ∧ x_1 ∈ ⟦τ⟧ᶻ then
                    (⟦(Term.abstract.go a [v] Δctx hgo_cov).uncurry
                        (fun _ => ⟨x_1, τ, h.2⟩)⟧ˢ.get
                      (hbody_total' (by
                        intro i
                        have hi0 : i = ⟨0, by simp⟩ := by
                          apply Fin.ext
                          simp
                        cases hi0
                        exact ⟨rfl, h.2⟩))).fst
                  else zffalse)
            𝔹 : ZFSet) = zftrue := by
      apply sInter_sep_eq_zftrue_of_forall_eq_zftrue
      · exact ⟨τ.defaultZFSet, SMTType.mem_toZFSet_of_defaultZFSet⟩
      · intro x_1 hx_1
        have hx1 := funUnaryTarget (α := τ) hx_1
        have hx_cast : x_1.hasArity 1 ∧ x_1 ∈ ⟦τ⟧ᶻ := by
          constructor
          · exact hx1.1
          · exact hx_1
        rw [dif_pos hx_cast]
        let W : SMT.Dom := ⟨x_1, τ, hx_1⟩
        obtain ⟨D, hden_body, hD_true⟩ := hbody_true W rfl
        have hgo_W :=
          funAbstractGoSingle
            (Δctx := Δctx) (P := a) (v := v) (τ := τ)
            hgo_cov hcov_a_upd (fun _ => W) (by
              intro i
              have hi0 : i = ⟨0, by simp⟩ := by
                apply Fin.ext
                simp
              cases hi0
              exact ⟨rfl, hx_1⟩)
        have hbody_eq :
            ⟦(Term.abstract.go a [v] Δctx hgo_cov).uncurry (fun _ => W)⟧ˢ =
              some D := by
          rw [hgo_W]
          simpa [W] using hden_body
        generalize_proofs hbody_some
        have hbody_get :
            (⟦(Term.abstract.go a [v] Δctx hgo_cov).uncurry (fun _ => W)⟧ˢ.get
              hbody_some) = D := by
          rw [Option.get_of_eq_some hbody_some hbody_eq]
        have hbody_fst :
            (⟦(Term.abstract.go a [v] Δctx hgo_cov).uncurry (fun _ => W)⟧ˢ.get
              hbody_some).fst = D.fst := by
          exact congrArg (fun d : SMT.Dom => d.fst) hbody_get
        rw [hbody_fst, hD_true]
    apply congrArg some
    apply funDomEqOfTyEqAndFstEq rfl
    simpa [Φ] using hsInter_true
  · exfalso
    apply hsome
    intro x_1 hx_1
    have hgo :=
      funAbstractGoSingle
        (Δctx := Δctx) (P := a) (v := v) (τ := τ)
        hgo_cov hcov_a_upd x_1 (by
          intro i
          have hi0 : i = ⟨0, by simp⟩ := by
            apply Fin.ext
            simp
          cases hi0
          simpa using hx_1 ⟨0, by simp⟩)
    rw [hgo]
    let W : SMT.Dom := x_1 ⟨0, by simp⟩
    have hW_ty : W.snd.fst = τ := by
      simpa [W] using (hx_1 ⟨0, by simp⟩).1
    simpa [W] using hbody_total W hW_ty

theorem funUnaryForallTrueImpliesAt.{u}
    {Δctx : RenamingContext.Context.{u}} {a : Term} {v : 𝒱} {τ : SMTType}
    (hφ_forall : RenamingContext.CoversFV Δctx (Term.forall [v] [τ] a))
    (hgo_cov : ∀ x ∈ fv a, x ∉ [v] → (Δctx x).isSome = true)
    (hcov_a_upd :
      ∀ W : SMT.Dom.{u},
        RenamingContext.CoversFV (Function.update Δctx v (some W)) a)
    (hbody_total :
      ∀ W : SMT.Dom.{u}, W.snd.fst = τ →
        ⟦a.abstract (Function.update Δctx v (some W)) (hcov_a_upd W)⟧ˢ.isSome = true)
    (hbody_ty :
      ∀ W : SMT.Dom.{u}, W.snd.fst = τ →
        ∀ {D : SMT.Dom.{u}},
          ⟦a.abstract (Function.update Δctx v (some W)) (hcov_a_upd W)⟧ˢ = some D →
            D.snd.fst = SMTType.bool)
    {Φ : SMT.Dom.{u}}
    (hden_forall :
      ⟦(Term.forall [v] [τ] a).abstract Δctx hφ_forall⟧ˢ = some Φ)
    (htrue : Φ.fst = zftrue)
    (W : SMT.Dom.{u})
    (hW_ty : W.snd.fst = τ) :
    ∃ D : SMT.Dom.{u},
      ⟦a.abstract (Function.update Δctx v (some W)) (hcov_a_upd W)⟧ˢ = some D ∧
        D.fst = zftrue := by
  have hW_mem : W.fst ∈ ⟦τ⟧ᶻ := by
    rw [← hW_ty]
    exact W.snd.snd
  have hbody_total' :
      ∀ {x_1 : Fin [v].length → SMT.Dom.{u}},
        (∀ i,
          ((x_1 i).snd.fst =
              match i with
              | ⟨i, hi⟩ => [τ][i]) ∧
            (x_1 i).fst ∈
              ⟦match i with
                | ⟨i, hi⟩ => [τ][i]⟧ᶻ) →
          ⟦(Term.abstract.go a [v] Δctx hgo_cov).uncurry x_1⟧ˢ.isSome = true := by
    intro x_1 hx_1
    have hgo :=
      funAbstractGoSingle
        (Δctx := Δctx) (P := a) (v := v) (τ := τ)
        hgo_cov hcov_a_upd x_1 (by
          intro i
          have hi0 : i = ⟨0, by simp⟩ := by
            apply Fin.ext
            simp
          cases hi0
          simpa using hx_1 ⟨0, by simp⟩)
    rw [hgo]
    let W0 : SMT.Dom := x_1 ⟨0, by simp⟩
    have hW0_ty : W0.snd.fst = τ := by
      simpa [W0] using (hx_1 ⟨0, by simp⟩).1
    simpa [W0] using hbody_total W0 hW0_ty
  let bodyVal : ZFSet → ZFSet := fun x_1 =>
    if h : x_1.hasArity 1 ∧ x_1 ∈ ⟦τ⟧ᶻ then
      (⟦(Term.abstract.go a [v] Δctx hgo_cov).uncurry
          (fun _ => ⟨x_1, τ, h.2⟩)⟧ˢ.get
        (hbody_total' (by
          intro i
          have hi0 : i = ⟨0, by simp⟩ := by
            apply Fin.ext
            simp
          cases hi0
          exact ⟨rfl, h.2⟩))).fst
    else zffalse
  let Sbody : ZFSet :=
    ⋂₀ (ZFSet.sep (fun y => ∃ x_1 ∈ ⟦τ⟧ᶻ, y = bodyVal x_1) 𝔹)
  have hlen_forall : [v].length > 0 := by
    simp
  rw [SMT.Term.abstract, dif_pos (by rfl), SMT.denote] at hden_forall
  rw [dif_pos hlen_forall] at hden_forall
  split_ifs at hden_forall with hsome
  · simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_one_sub_one,
    List.getElem_cons_succ, Fin.zero_eta, Fin.isValue, Nat.zero_mod, List.getElem_cons_zero,
    zero_add, Fin.val_eq_zero, get.eq_1, forall_const, Option.pure_def,
    Option.some.injEq] at hden_forall
    let sInterGoal : ZFSet :=
      ⋂₀
        ZFSet.sep
          (fun y =>
            ∃ x_1 ∈ ⟦τ⟧ᶻ,
              y =
                if hx : x_1.hasArity 1 ∧ ∀ i : Fin 1, x_1 ∈ ⟦[τ][↑i]⟧ᶻ then
                  (⟦(Term.abstract.go a [v] Δctx hgo_cov).uncurry
                      (fun i => ⟨x_1, [τ][↑i], hx.2 i⟩)⟧ˢ.get
                    (hsome (by
                      intro i
                      exact ⟨rfl, hx.2 i⟩))).fst
                else zffalse)
          𝔹
    have hsInter_eq : sInterGoal = Sbody := by
      dsimp [sInterGoal, Sbody, bodyVal]
      congr
      ext y
      have hbody_eq {x_1 : ZFSet} (hx_1 : x_1 ∈ ⟦τ⟧ᶻ) :
          (if hx : x_1.hasArity 1 ∧ ∀ i : Fin 1, x_1 ∈ ⟦[τ][↑i]⟧ᶻ then
            (⟦(Term.abstract.go a [v] Δctx hgo_cov).uncurry
                (fun i => ⟨x_1, [τ][↑i], hx.2 i⟩)⟧ˢ.get
              (hsome (by
                intro i
                exact ⟨rfl, hx.2 i⟩))).fst
          else zffalse) =
          bodyVal x_1 := by
        by_cases h : x_1.hasArity 1 ∧ x_1 ∈ ⟦τ⟧ᶻ
        · have hx : x_1.hasArity 1 ∧ ∀ i : Fin 1, x_1 ∈ ⟦[τ][↑i]⟧ᶻ := by
            constructor
            · exact h.1
            · intro i
              have hi0 : i = ⟨0, by simp⟩ := by
                apply Fin.ext
                simp
              cases hi0
              simpa using h.2
          simp only [hx, Fin.getElem_fin, Fin.val_eq_zero, List.getElem_cons_zero, h, implies_true,
            and_self, ↓reduceDIte, List.length_cons, List.length_nil, Nat.reduceAdd, subset_refl,
            subset_of_empty, bodyVal]
        · have hx : ¬ (x_1.hasArity 1 ∧ ∀ i : Fin 1, x_1 ∈ ⟦[τ][↑i]⟧ᶻ) := by
            intro hx
            apply h
            constructor
            · exact hx.1
            · simpa using hx.2 ⟨0, by simp⟩
          simp only [Fin.getElem_fin, Fin.val_eq_zero, List.getElem_cons_zero, forall_const, h,
            ↓reduceDIte, subset_refl, subset_of_empty, List.length_cons, List.length_nil,
            Nat.reduceAdd, bodyVal]
      constructor
      · rintro ⟨x_1, hx_1, hy⟩
        refine ⟨x_1, ?_, hy.trans (hbody_eq (by simpa [Fin.foldl_zero] using hx_1))⟩
        simpa [Fin.foldl_zero] using hx_1
      · rintro ⟨x_1, hx_1, hy⟩
        refine ⟨x_1, ?_, hy.trans (hbody_eq hx_1).symm⟩
        simpa [Fin.foldl_zero] using hx_1
    have hsInterGoal_true : sInterGoal = zftrue := by
      cases hden_forall
      rw [←htrue]
      simp only [hsInter_eq, subset_refl, subset_of_empty, Fin.foldl_zero, Fin.val_eq_zero,
        List.getElem_cons_zero, forall_const, Sbody, bodyVal]
      rfl
    have hsInter_true : Sbody = zftrue := by rwa [←hsInter_eq]
    have hbody_bool : ∀ x_1 ∈ ⟦τ⟧ᶻ, bodyVal x_1 ∈ 𝔹 := by
      intro x_1 hx_1
      have hx_cast : x_1.hasArity 1 ∧ x_1 ∈ ⟦τ⟧ᶻ := by
        constructor
        · exact (funUnaryTarget (α := τ) hx_1).1
        · exact hx_1
      dsimp [bodyVal]
      rw [dif_pos hx_cast]
      let W0 : SMT.Dom := ⟨x_1, τ, hx_1⟩
      obtain ⟨D, hden_body⟩ := Option.isSome_iff_exists.mp (hbody_total W0 rfl)
      have hgo_W0 :=
        funAbstractGoSingle
          (Δctx := Δctx) (P := a) (v := v) (τ := τ)
          hgo_cov hcov_a_upd (fun _ => W0) (by
            intro i
            have hi0 : i = ⟨0, by simp⟩ := by
              apply Fin.ext
              simp
            cases hi0
            exact ⟨rfl, hx_1⟩)
      have hbody_eq :
          ⟦(Term.abstract.go a [v] Δctx hgo_cov).uncurry (fun _ => W0)⟧ˢ =
            some D := by
        rw [hgo_W0]
        simpa [W0] using hden_body
      have hbody_some_bool :
          ⟦(Term.abstract.go a [v] Δctx hgo_cov).uncurry (fun _ => W0)⟧ˢ.isSome =
            true := by
        exact Option.isSome_of_eq_some hbody_eq
      have hbody_fst :
          (⟦(Term.abstract.go a [v] Δctx hgo_cov).uncurry (fun _ => W0)⟧ˢ.get
            (hbody_total' (by
              intro i
              have hi0 : i = ⟨0, by simp⟩ := by
                apply Fin.ext
                simp
              cases hi0
              exact ⟨rfl, hx_1⟩))).fst = D.fst := by
        calc
          (⟦(Term.abstract.go a [v] Δctx hgo_cov).uncurry (fun _ => W0)⟧ˢ.get
            (hbody_total' (by
              intro i
              have hi0 : i = ⟨0, by simp⟩ := by
                apply Fin.ext
                simp
              cases hi0
              exact ⟨rfl, hx_1⟩))).fst =
          (⟦(Term.abstract.go a [v] Δctx hgo_cov).uncurry (fun _ => W0)⟧ˢ.get
            hbody_some_bool).fst := by
              exact Option.get_fst_eq_of_isSome
          _ = D.fst := by
            exact congrArg (fun d : SMT.Dom => d.fst)
              (Option.get_of_eq_some hbody_some_bool hbody_eq)
      have hD_ty : D.snd.fst = SMTType.bool := by
        exact hbody_ty W0 rfl hden_body
      have hD_bool : D.fst ∈ 𝔹 := by
        simpa [hD_ty] using D.snd.snd
      exact hbody_fst.symm ▸ hD_bool
    have hall_true : ∀ x_1 ∈ ⟦τ⟧ᶻ, bodyVal x_1 = zftrue := by
      exact sInterSepEqZftrueImpliesForallEqZftrue hbody_bool hsInter_true
    let W0 : SMT.Dom := ⟨W.fst, τ, hW_mem⟩
    have hW_eq : W0 = W := by
      exact funDomEqOfTyEqAndFstEq hW_ty.symm rfl
    obtain ⟨D, hden_body⟩ := Option.isSome_iff_exists.mp (hbody_total W0 rfl)
    have hgo_W0 :=
      funAbstractGoSingle
        (Δctx := Δctx) (P := a) (v := v) (τ := τ)
        hgo_cov hcov_a_upd (fun _ => W0) (by
          intro i
          have hi0 : i = ⟨0, by simp⟩ := by
            apply Fin.ext
            simp
          cases hi0
          exact ⟨rfl, hW_mem⟩)
    have hbody_eq :
        ⟦(Term.abstract.go a [v] Δctx hgo_cov).uncurry (fun _ => W0)⟧ˢ =
          some D := by
      rw [hgo_W0]
      simpa [W0] using hden_body
    have hbody_some_true :
        ⟦(Term.abstract.go a [v] Δctx hgo_cov).uncurry (fun _ => W0)⟧ˢ.isSome =
          true := by
      exact Option.isSome_of_eq_some hbody_eq
    have hx_cast : W.fst.hasArity 1 ∧ W.fst ∈ ⟦τ⟧ᶻ := by
      constructor
      · exact (funUnaryTarget (α := τ) hW_mem).1
      · exact hW_mem
    have hD_true : D.fst = zftrue := by
      have hbody_true' : bodyVal W.fst = zftrue := by
        exact hall_true W.fst hW_mem
      dsimp [bodyVal] at hbody_true'
      rw [dif_pos hx_cast] at hbody_true'
      calc
        D.fst =
          (⟦(Term.abstract.go a [v] Δctx hgo_cov).uncurry (fun _ => W0)⟧ˢ.get
            hbody_some_true).fst := by
              exact congrArg (fun d : SMT.Dom => d.fst)
                (Option.get_of_eq_some hbody_some_true hbody_eq).symm
        _ =
          (⟦(Term.abstract.go a [v] Δctx hgo_cov).uncurry (fun _ => W0)⟧ˢ.get
            (hbody_total' (by
              intro i
              have hi0 : i = ⟨0, by simp⟩ := by
                apply Fin.ext
                simp
              cases hi0
              exact ⟨rfl, hW_mem⟩))).fst := by
              exact (Option.get_fst_eq_of_isSome).symm
        _ = zftrue := hbody_true'
    refine ⟨D, ?_, hD_true⟩
    simpa [W0, hW_eq] using hden_body
  · exfalso
    apply hsome
    intro x_1 hx_1
    let W0 : SMT.Dom := x_1 ⟨0, by simp⟩
    have hW0_ty : W0.snd.fst = τ := by
      simpa [W0] using (hx_1 ⟨0, by simp⟩).1
    have hgo :=
      funAbstractGoSingle
        (Δctx := Δctx) (P := a) (v := v) (τ := τ)
        hgo_cov hcov_a_upd x_1 (by
          intro i
          have hi0 : i = ⟨0, by simp⟩ := by
            apply Fin.ext
            simp
          cases hi0
          simpa using hx_1 ⟨0, by simp⟩)
    rw [hgo]
    simpa [W0] using hbody_total W0 hW0_ty

theorem funUnaryForallEqZffalse.{u}
    {Γ : TypeContext} {Δctx : RenamingContext.Context.{u}} {a : Term} {v : 𝒱} {τ : SMTType}
    (typ_forall : Γ ⊢ˢ (Term.forall [v] [τ] a) : SMTType.bool)
    (hφ_forall : RenamingContext.CoversFV Δctx (Term.forall [v] [τ] a))
    (hgo_cov : ∀ x ∈ fv a, x ∉ [v] → (Δctx x).isSome = true)
    (hcov_a_upd :
      ∀ W : SMT.Dom.{u},
        RenamingContext.CoversFV (Function.update Δctx v (some W)) a)
    (hbody_total :
      ∀ W : SMT.Dom.{u}, W.snd.fst = τ →
        ⟦a.abstract (Function.update Δctx v (some W)) (hcov_a_upd W)⟧ˢ.isSome = true)
    (hbody_ty :
      ∀ W : SMT.Dom.{u}, W.snd.fst = τ →
        ∀ {D : SMT.Dom.{u}},
          ⟦a.abstract (Function.update Δctx v (some W)) (hcov_a_upd W)⟧ˢ = some D →
            D.snd.fst = SMTType.bool)
    (W : SMT.Dom.{u})
    (hW_ty : W.snd.fst = τ)
    (hbody_false :
      ∃ D : SMT.Dom.{u},
        ⟦a.abstract (Function.update Δctx v (some W)) (hcov_a_upd W)⟧ˢ = some D ∧
          D.fst = zffalse) :
    ⟦(Term.forall [v] [τ] a).abstract Δctx hφ_forall⟧ˢ =
      some ⟨zffalse, SMTType.bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
  have hsome_forall :=
    funUnaryForallTotal
      (Δctx := Δctx) (a := a) (v := v) (τ := τ)
      hφ_forall hgo_cov hcov_a_upd hbody_total
  obtain ⟨Φ, hden_forall⟩ := Option.isSome_iff_exists.mp hsome_forall
  have hΦ_ty :
      Φ.snd.fst = SMTType.bool := by
    exact denote_type_eq_of_typing (typ_t := typ_forall) (hden := hden_forall)
  have hΦ_false :
      Φ.fst = zffalse := by
    have hΦ_bool : Φ.fst ∈ 𝔹 := by
      simpa [hΦ_ty] using Φ.snd.snd
    rw [ZFSet.ZFBool.mem_𝔹_iff] at hΦ_bool
    rcases hΦ_bool with hΦ_false | hΦ_true
    · exact hΦ_false
    · obtain ⟨D, hden_body, hD_false⟩ := hbody_false
      obtain ⟨Dtrue, hden_true, hD_true⟩ :=
        funUnaryForallTrueImpliesAt
          (Δctx := Δctx) (a := a) (v := v) (τ := τ)
          hφ_forall hgo_cov hcov_a_upd hbody_total hbody_ty
          hden_forall hΦ_true W hW_ty
      have hD_eq : Dtrue = D := by
        exact Option.some.inj (hden_true.symm.trans hden_body)
      have hcontra : zftrue = zffalse := by
        calc
          zftrue = Dtrue.fst := hD_true.symm
          _ = D.fst := by rw [hD_eq]
          _ = zffalse := hD_false
      exact False.elim (ZFSet.zftrue_ne_zffalse hcontra)
  obtain ⟨d, τ', hd⟩ := Φ
  cases hΦ_ty
  cases hΦ_false
  simpa [proof_irrel_heq] using hden_forall

theorem funUnaryExistsEqZftrue.{u}
    {Γ : TypeContext} {Δctx : RenamingContext.Context.{u}} {a : Term} {v : 𝒱} {τ : SMTType}
    (typ_exists : Γ ⊢ˢ (Term.exists [v] [τ] a) : SMTType.bool)
    (hφ_exists : RenamingContext.CoversFV Δctx (Term.exists [v] [τ] a))
    (hgo_cov : ∀ x ∈ fv a, x ∉ [v] → (Δctx x).isSome = true)
    (hcov_a_upd :
      ∀ W : SMT.Dom.{u},
        RenamingContext.CoversFV (Function.update Δctx v (some W)) a)
    (hbody_total :
      ∀ W : SMT.Dom.{u}, W.snd.fst = τ →
        ⟦a.abstract (Function.update Δctx v (some W)) (hcov_a_upd W)⟧ˢ.isSome = true)
    (hbody_ty :
      ∀ W : SMT.Dom.{u}, W.snd.fst = τ →
        ∀ {D : SMT.Dom.{u}},
          ⟦a.abstract (Function.update Δctx v (some W)) (hcov_a_upd W)⟧ˢ = some D →
            D.snd.fst = SMTType.bool)
    (W : SMT.Dom.{u})
    (hW_ty : W.snd.fst = τ)
    (hbody_true :
      ∃ D : SMT.Dom.{u},
        ⟦a.abstract (Function.update Δctx v (some W)) (hcov_a_upd W)⟧ˢ = some D ∧
          D.fst = zftrue) :
    ⟦(Term.exists [v] [τ] a).abstract Δctx hφ_exists⟧ˢ =
      some ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
  have hφ_forall_not :
      RenamingContext.CoversFV Δctx (Term.forall [v] [τ] (¬ˢ a)) := by
    intro x hx
    have hx' : x ∈ fv (Term.exists [v] [τ] a) := by
      simpa [fv] using hx
    exact hφ_exists x hx'
  have hgo_cov_not :
      ∀ x ∈ fv (¬ˢ a), x ∉ [v] → (Δctx x).isSome = true := by
    intro x hx hx_not
    exact hgo_cov x (by simpa [fv] using hx) hx_not
  have hcov_not_upd :
      ∀ W : SMT.Dom.{u},
        RenamingContext.CoversFV (Function.update Δctx v (some W)) (¬ˢ a) := by
    intro W x hx
    exact hcov_a_upd W x (by simpa [fv] using hx)
  have hbody_total_not :
      ∀ W : SMT.Dom.{u}, W.snd.fst = τ →
        ⟦(¬ˢ a).abstract (Function.update Δctx v (some W)) (hcov_not_upd W)⟧ˢ.isSome = true := by
    intro W hW_ty
    obtain ⟨D, hden_body⟩ := Option.isSome_iff_exists.mp (hbody_total W hW_ty)
    have hD_ty : D.snd.fst = SMTType.bool := hbody_ty W hW_ty hden_body
    exact funNotAbstractIsSomeOfSomeBool
      (Δctx := Function.update Δctx v (some W))
      (t := a) (D := D)
      (hcov_t := hcov_a_upd W)
      hden_body hD_ty
      (hcov_not_upd W)
  have hbody_ty_not :
      ∀ W : SMT.Dom.{u}, W.snd.fst = τ →
        ∀ {D : SMT.Dom.{u}},
          ⟦(¬ˢ a).abstract (Function.update Δctx v (some W)) (hcov_not_upd W)⟧ˢ = some D →
            D.snd.fst = SMTType.bool := by
    intro W hW_ty D hden_not
    obtain ⟨Db, hden_body⟩ := Option.isSome_iff_exists.mp (hbody_total W hW_ty)
    have hDb_ty : Db.snd.fst = SMTType.bool := hbody_ty W hW_ty hden_body
    obtain ⟨db, τb, hdb⟩ := Db
    cases hDb_ty
    rw [SMT.Term.abstract, SMT.denote, hden_body] at hden_not
    simp only [Option.pure_def, Option.failure_eq_none, Option.bind_eq_bind, Option.bind_some] at hden_not
    cases hden_not
    rfl
  have hbody_false_not :
      ∃ D : SMT.Dom.{u},
        ⟦(¬ˢ a).abstract (Function.update Δctx v (some W)) (hcov_not_upd W)⟧ˢ = some D ∧
          D.fst = zffalse := by
    obtain ⟨D, hden_body, hD_true⟩ := hbody_true
    have hD_ty : D.snd.fst = SMTType.bool := hbody_ty W hW_ty hden_body
    refine ⟨⟨zffalse, SMTType.bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩, ?_, rfl⟩
    rw [SMT.Term.abstract]
    exact denote_not_eq_zffalse_of_some_zftrue hden_body hD_ty hD_true
  obtain ⟨_, hnotin, hbv, hlen_pos, hlen_eq, typ_body⟩ := SMT.Typing.existsE typ_exists
  have typ_not_body :
      Γ.update [v] [τ] rfl ⊢ˢ (¬ˢ a) : SMTType.bool := by
    exact SMT.Typing.not (Γ := Γ.update [v] [τ] rfl) a typ_body
  have hbv_not :
      ∀ x ∈ [v], x ∉ bv (¬ˢ a) := by
    intro x hx
    simpa [bv] using hbv x hx
  have typ_forall_not :
      Γ ⊢ˢ (Term.forall [v] [τ] (¬ˢ a)) : SMTType.bool := by
    exact SMT.Typing.forall
      (Γ := Γ) (vs := [v]) (τs := [τ]) (P := ¬ˢ a)
      hnotin hbv_not hlen_pos hlen_eq typ_not_body
  have hden_forall_not_false :
      ⟦(Term.forall [v] [τ] (¬ˢ a)).abstract Δctx hφ_forall_not⟧ˢ =
        some ⟨zffalse, SMTType.bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
    exact funUnaryForallEqZffalse
      (Γ := Γ) (Δctx := Δctx) (a := ¬ˢ a) (v := v) (τ := τ)
      typ_forall_not
      hφ_forall_not hgo_cov_not hcov_not_upd
      hbody_total_not hbody_ty_not
      W hW_ty hbody_false_not
  have hgo_not :
      (Term.abstract.go (¬ˢ a) [v] Δctx hgo_cov_not).uncurry =
        fun x => ¬ˢ' (Term.abstract.go a [v] Δctx hgo_cov).uncurry x := by
    funext x
    let W0 := x ⟨0, by simp⟩
    have hx_eq :
        (fun x' : Fin [v].length =>
          match x' with
          | ⟨i, hi⟩ => [W0][i]) = x := by
      funext i
      have hi0 : i = ⟨0, by simp⟩ := by
        apply Fin.ext
        simp
      cases hi0
      rfl
    have hgo_not' :=
      SMT.Term.abstract.go.alt_def₂
        (vs := [v]) (P := ¬ˢ a) (Δctx := Δctx)
        (αs := [W0]) (vs_αs_len := by simp)
        (Δ_isSome := hgo_cov_not)
        (tmp₁ := by
          intro y hy
          simpa [W0, Function.updates] using hcov_not_upd W0 y hy)
    have hgo_a' :=
      SMT.Term.abstract.go.alt_def₂
        (vs := [v]) (P := a) (Δctx := Δctx)
        (αs := [W0]) (vs_αs_len := by simp)
        (Δ_isSome := hgo_cov)
        (tmp₁ := by
          intro y hy
          simpa [W0, Function.updates] using hcov_a_upd W0 y hy)
    rw [← hx_eq, hgo_not', hgo_a', Term.abstract]
  rw [SMT.Term.abstract, dite_cond_eq_true (eq_true (by rfl)), SMT.PHOAS.Term.exists, SMT.denote]
  have hden_forall_not_false' :
      ⟦SMT.PHOAS.Term.forall
          (fun x =>
            match x with
            | ⟨i, hi⟩ => [τ][i])
          (fun x => ¬ˢ' (Term.abstract.go a [v] Δctx hgo_cov).uncurry x)⟧ˢ =
        some ⟨zffalse, SMTType.bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
    simpa [SMT.Term.abstract, hgo_not, proof_irrel_heq] using hden_forall_not_false
  exact denote_not_eq_zftrue_of_some_zffalse hden_forall_not_false' rfl rfl

theorem funUnaryExistsEqZftrueAtWitness.{u}
    {Γ : TypeContext} {Δctx : RenamingContext.Context.{u}} {a : Term} {v : 𝒱} {τ : SMTType}
    (typ_exists : Γ ⊢ˢ (Term.exists [v] [τ] a) : SMTType.bool)
    (hφ_exists : RenamingContext.CoversFV Δctx (Term.exists [v] [τ] a))
    (hgo_cov : ∀ x ∈ fv a, x ∉ [v] → (Δctx x).isSome = true)
    (hcov_a_upd :
      ∀ W : SMT.Dom.{u},
        RenamingContext.CoversFV (Function.update Δctx v (some W)) a)
    (hbody_total :
      ∀ W : SMT.Dom.{u}, W.snd.fst = τ →
        ⟦a.abstract (Function.update Δctx v (some W)) (hcov_a_upd W)⟧ˢ.isSome = true)
    (hbody_ty :
      ∀ W : SMT.Dom.{u}, W.snd.fst = τ →
        ∀ {D : SMT.Dom.{u}},
          ⟦a.abstract (Function.update Δctx v (some W)) (hcov_a_upd W)⟧ˢ = some D →
            D.snd.fst = SMTType.bool)
    (W : SMT.Dom.{u})
    (hW_ty : W.snd.fst = τ)
    {D : SMT.Dom.{u}}
    (hden_body :
      ⟦a.abstract (Function.update Δctx v (some W)) (hcov_a_upd W)⟧ˢ = some D)
    (hD_true : D.fst = zftrue) :
    ⟦(Term.exists [v] [τ] a).abstract Δctx hφ_exists⟧ˢ =
      some ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
  exact funUnaryExistsEqZftrue
    (Γ := Γ) (Δctx := Δctx) (a := a) (v := v) (τ := τ)
    typ_exists hφ_exists hgo_cov hcov_a_upd hbody_total hbody_ty
    W hW_ty ⟨D, hden_body, hD_true⟩

theorem funUnaryExistsEqZffalse.{u}
    {Δctx : RenamingContext.Context.{u}} {a : Term} {v : 𝒱} {τ : SMTType}
    (hφ_exists : RenamingContext.CoversFV Δctx (Term.exists [v] [τ] a))
    (hgo_cov : ∀ x ∈ fv a, x ∉ [v] → (Δctx x).isSome = true)
    (hcov_a_upd :
      ∀ W : SMT.Dom.{u},
        RenamingContext.CoversFV (Function.update Δctx v (some W)) a)
    (hbody_total :
      ∀ W : SMT.Dom.{u}, W.snd.fst = τ →
        ⟦a.abstract (Function.update Δctx v (some W)) (hcov_a_upd W)⟧ˢ.isSome = true)
    (hbody_ty :
      ∀ W : SMT.Dom.{u}, W.snd.fst = τ →
        ∀ {D : SMT.Dom.{u}},
          ⟦a.abstract (Function.update Δctx v (some W)) (hcov_a_upd W)⟧ˢ = some D →
            D.snd.fst = SMTType.bool)
    (hbody_false :
      ∀ W : SMT.Dom.{u}, W.snd.fst = τ →
        ∃ D : SMT.Dom.{u},
          ⟦a.abstract (Function.update Δctx v (some W)) (hcov_a_upd W)⟧ˢ = some D ∧
            D.fst = zffalse) :
    ⟦(Term.exists [v] [τ] a).abstract Δctx hφ_exists⟧ˢ =
      some ⟨zffalse, SMTType.bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
  have hφ_forall_not :
      RenamingContext.CoversFV Δctx (Term.forall [v] [τ] (¬ˢ a)) := by
    intro x hx
    have hx' : x ∈ fv (Term.exists [v] [τ] a) := by
      simpa [fv] using hx
    exact hφ_exists x hx'
  have hgo_cov_not :
      ∀ x ∈ fv (¬ˢ a), x ∉ [v] → (Δctx x).isSome = true := by
    intro x hx hx_not
    exact hgo_cov x (by simpa [fv] using hx) hx_not
  have hcov_not_upd :
      ∀ W : SMT.Dom.{u},
        RenamingContext.CoversFV (Function.update Δctx v (some W)) (¬ˢ a) := by
    intro W x hx
    exact hcov_a_upd W x (by simpa [fv] using hx)
  have hbody_total_not :
      ∀ W : SMT.Dom.{u}, W.snd.fst = τ →
        ⟦(¬ˢ a).abstract (Function.update Δctx v (some W)) (hcov_not_upd W)⟧ˢ.isSome = true := by
    intro W hW_ty
    obtain ⟨D, hden_body⟩ := Option.isSome_iff_exists.mp (hbody_total W hW_ty)
    have hD_ty : D.snd.fst = SMTType.bool := hbody_ty W hW_ty hden_body
    exact funNotAbstractIsSomeOfSomeBool
      (Δctx := Function.update Δctx v (some W))
      (t := a) (D := D)
      (hcov_t := hcov_a_upd W)
      hden_body hD_ty
      (hcov_not_upd W)
  have hbody_ty_not :
      ∀ W : SMT.Dom.{u}, W.snd.fst = τ →
        ∀ {D : SMT.Dom.{u}},
          ⟦(¬ˢ a).abstract (Function.update Δctx v (some W)) (hcov_not_upd W)⟧ˢ = some D →
            D.snd.fst = SMTType.bool := by
    intro W hW_ty D hden_not
    obtain ⟨Db, hden_body⟩ := Option.isSome_iff_exists.mp (hbody_total W hW_ty)
    have hDb_ty : Db.snd.fst = SMTType.bool := hbody_ty W hW_ty hden_body
    obtain ⟨db, τb, hdb⟩ := Db
    cases hDb_ty
    rw [SMT.Term.abstract, SMT.denote, hden_body] at hden_not
    simp only [Option.pure_def, Option.failure_eq_none, Option.bind_eq_bind, Option.bind_some] at hden_not
    cases hden_not
    rfl
  have hbody_true_not :
      ∀ W : SMT.Dom.{u}, W.snd.fst = τ →
        ∃ D : SMT.Dom.{u},
          ⟦(¬ˢ a).abstract (Function.update Δctx v (some W)) (hcov_not_upd W)⟧ˢ = some D ∧
            D.fst = zftrue := by
    intro W hW_ty
    obtain ⟨D, hden_body, hD_false⟩ := hbody_false W hW_ty
    have hD_ty : D.snd.fst = SMTType.bool := hbody_ty W hW_ty hden_body
    have hden_not_true :=
      funNotAbstractEqZftrueOfSomeZffalse
        (Δctx := Function.update Δctx v (some W))
        (t := a) (D := D)
        (hcov_t := hcov_a_upd W)
        hden_body hD_ty hD_false
        (hcov_not_upd W)
    exact ⟨⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩, hden_not_true, rfl⟩
  have hden_forall_not_true :
      ⟦(Term.forall [v] [τ] (¬ˢ a)).abstract Δctx hφ_forall_not⟧ˢ =
        some ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
    exact funUnaryForallEqZftrue
      (Δctx := Δctx) (a := ¬ˢ a) (v := v) (τ := τ)
      hφ_forall_not hgo_cov_not hcov_not_upd
      hbody_total_not hbody_ty_not hbody_true_not
  have hgo_not :
      (Term.abstract.go (¬ˢ a) [v] Δctx hgo_cov_not).uncurry =
        fun x => ¬ˢ' (Term.abstract.go a [v] Δctx hgo_cov).uncurry x := by
    funext x
    let W0 := x ⟨0, by simp⟩
    have hx_eq :
        (fun x' : Fin [v].length =>
          match x' with
          | ⟨i, hi⟩ => [W0][i]) = x := by
      funext i
      have hi0 : i = ⟨0, by simp⟩ := by
        apply Fin.ext
        simp
      cases hi0
      rfl
    have hgo_not' :=
      SMT.Term.abstract.go.alt_def₂
        (vs := [v]) (P := ¬ˢ a) (Δctx := Δctx)
        (αs := [W0]) (vs_αs_len := by simp)
        (Δ_isSome := hgo_cov_not)
        (tmp₁ := by
          intro y hy
          simpa [W0, Function.updates] using hcov_not_upd W0 y hy)
    have hgo_a' :=
      SMT.Term.abstract.go.alt_def₂
        (vs := [v]) (P := a) (Δctx := Δctx)
        (αs := [W0]) (vs_αs_len := by simp)
        (Δ_isSome := hgo_cov)
        (tmp₁ := by
          intro y hy
          simpa [W0, Function.updates] using hcov_a_upd W0 y hy)
    rw [← hx_eq, hgo_not', hgo_a', Term.abstract]
  rw [SMT.Term.abstract, dite_cond_eq_true (eq_true (by rfl)), SMT.PHOAS.Term.exists, SMT.denote]
  have hden_forall_not_true' :
      ⟦SMT.PHOAS.Term.forall
          (fun x =>
            match x with
            | ⟨i, hi⟩ => [τ][i])
          (fun x => ¬ˢ' (Term.abstract.go a [v] Δctx hgo_cov).uncurry x)⟧ˢ =
        some ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
    simpa [SMT.Term.abstract, hgo_not, proof_irrel_heq] using hden_forall_not_true
  exact denote_not_eq_zffalse_of_some_zftrue hden_forall_not_true' rfl rfl

theorem funUnaryExistsEqZffalseOfTrueImpliesRange.{u}
    {Δctx : RenamingContext.Context.{u}} {a : Term} {v : 𝒱}
    {τ τ' : SMTType} {cast : ZFSet} {target : SMT.Dom.{u}}
    (hcast : ZFSet.IsFunc ⟦τ⟧ᶻ ⟦τ'⟧ᶻ cast)
    (hφ_exists : RenamingContext.CoversFV Δctx (Term.exists [v] [τ] a))
    (hgo_cov : ∀ x ∈ fv a, x ∉ [v] → (Δctx x).isSome = true)
    (hcov_a_upd :
      ∀ W : SMT.Dom.{u},
        RenamingContext.CoversFV (Function.update Δctx v (some W)) a)
    (hbody_total :
      ∀ W : SMT.Dom.{u}, W.snd.fst = τ →
        ⟦a.abstract (Function.update Δctx v (some W)) (hcov_a_upd W)⟧ˢ.isSome = true)
    (hbody_ty :
      ∀ W : SMT.Dom.{u}, W.snd.fst = τ →
        ∀ {D : SMT.Dom.{u}},
          ⟦a.abstract (Function.update Δctx v (some W)) (hcov_a_upd W)⟧ˢ = some D →
            D.snd.fst = SMTType.bool)
    (hbody_true_implies_cast :
      ∀ W : SMT.Dom.{u}, W.snd.fst = τ →
        ∀ {D : SMT.Dom.{u}},
          ⟦a.abstract (Function.update Δctx v (some W)) (hcov_a_upd W)⟧ˢ = some D →
            D.fst = zftrue →
              W.fst.pair target.fst ∈ cast)
    (htarget_not_ran : target.fst ∉ cast.Range) :
    ⟦(Term.exists [v] [τ] a).abstract Δctx hφ_exists⟧ˢ =
      some ⟨zffalse, SMTType.bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
  apply funUnaryExistsEqZffalse
    (Δctx := Δctx) (a := a) (v := v) (τ := τ)
    hφ_exists hgo_cov hcov_a_upd hbody_total hbody_ty
  intro W hW_ty
  obtain ⟨D, hden_body⟩ := Option.isSome_iff_exists.mp (hbody_total W hW_ty)
  have hD_ty : D.snd.fst = SMTType.bool := hbody_ty W hW_ty hden_body
  have hD_false : D.fst = zffalse := by
    have hD_bool : D.fst ∈ 𝔹 := by
      simpa [hD_ty] using D.snd.snd
    rw [ZFSet.ZFBool.mem_𝔹_iff] at hD_bool
    rcases hD_bool with hD_false | hD_true
    · exact hD_false
    · exfalso
      have hpair : W.fst.pair target.fst ∈ cast :=
        hbody_true_implies_cast W hW_ty hden_body hD_true
      have hW_mem : W.fst ∈ ⟦τ⟧ᶻ := by
        rw [← hW_ty]
        exact W.snd.snd
      have hW_dom : W.fst ∈ cast.Dom := by
        simpa [ZFSet.is_func_dom_eq hcast] using hW_mem
      have hcast_W :
          @ᶻcast ⟨W.fst, hW_dom⟩ = target.fst := by
        have hpair' := ZFSet.fapply.of_pair (ZFSet.is_func_is_pfunc hcast) hpair
        simpa only [Subtype.ext_iff] using hpair'
      have htarget_ran : target.fst ∈ cast.Range := by
        simpa [hcast_W] using
          ZFSet.IsPFunc.mem_range_of_mem
            (ZFSet.is_func_is_pfunc hcast)
            (ZFSet.fapply.def (ZFSet.is_func_is_pfunc hcast) hW_dom)
      exact htarget_not_ran htarget_ran
  exact ⟨D, hden_body, hD_false⟩

set_option maxHeartbeats 800000 in
theorem funExistsABTotalAt.{u}
    {α β : SMTType}
    {x a!_spec b!_spec : Term}
    {a a! b b! : 𝒱}
    {ΔY : RenamingContext.Context.{u}}
    {wy0 DappX : SMT.Dom.{u}}
    {Γa Γb : TypeContext}
    (fv_a!_spec : fv a!_spec ⊆ fv (Term.var a) ∪ {a!})
    (fv_b!_spec : fv b!_spec ⊆ fv (Term.var b) ∪ {b!})
    (a_not_mem_fv_x : a ∉ fv x)
    (b_not_mem_fv_x : b ∉ fv x)
    (a!_not_mem_fv_x : a! ∉ fv x)
    (b!_not_mem_fv_x : b! ∉ fv x)
    (b_ne_a : b ≠ a)
    (a!_ne_b : a! ≠ b)
    (a_ne_b! : a ≠ b!)
    (b_ne_b! : b ≠ b!)
    (a_ne_a! : a ≠ a!)
    (a!_ne_b! : a! ≠ b!)
    (hφ_exists_ab :
      RenamingContext.CoversFV
        (Function.update (Function.update ΔY a! (some wy0)) b! (some DappX))
        (Term.exists [a, b] [α, β] (((@ˢx) (Term.var a) =ˢ Term.var b) ∧ˢ (a!_spec ∧ˢ b!_spec))))
    (hφa_at :
      ∀ x₀ : SMT.Dom.{u},
        RenamingContext.CoversFV
          (Function.update (Function.update ΔY a (some x₀)) a! (some wy0))
          a!_spec)
    (hφb_at :
      ∀ y₀ : SMT.Dom.{u},
        RenamingContext.CoversFV
          (Function.update (Function.update (Function.update ΔY a! (some wy0)) b (some y₀)) b! (some DappX))
          b!_spec)
    (a_spec_total_at :
      ∀ x₀ : SMT.Dom.{u},
        x₀.snd.fst = α →
          ⟦a!_spec.abstract
              (Function.update (Function.update ΔY a (some x₀)) a! (some wy0))
              (hφa_at x₀)⟧ˢ.isSome =
            true)
    (b_spec_total_at :
      ∀ y₀ : SMT.Dom.{u},
        y₀.snd.fst = β →
          ⟦b!_spec.abstract
              (Function.update (Function.update (Function.update ΔY a! (some wy0)) b (some y₀)) b! (some DappX))
              (hφb_at y₀)⟧ˢ.isSome =
            true)
    (den_xa_at :
      ∀ x₀ : SMT.Dom.{u},
        x₀.snd.fst = α →
          x₀.fst ∈ ⟦α⟧ᶻ →
            ∃ hcov_xa : RenamingContext.CoversFV (Function.update ΔY a (some x₀)) ((@ˢx) (Term.var a)),
              ∃ Dxa : SMT.Dom.{u},
                Dxa.snd.fst = β ∧
                  ⟦((@ˢx) (Term.var a)).abstract (Function.update ΔY a (some x₀)) hcov_xa⟧ˢ =
                    some Dxa)
    (typ_a_ctx : Γa ⊢ˢ a!_spec : SMTType.bool)
    (typ_b_ctx : Γb ⊢ˢ b!_spec : SMTType.bool) :
    ⟦(Term.exists [a, b] [α, β] (((@ˢx) (Term.var a) =ˢ Term.var b) ∧ˢ (a!_spec ∧ˢ b!_spec))).abstract
        (Function.update (Function.update ΔY a! (some wy0)) b! (some DappX))
        hφ_exists_ab⟧ˢ.isSome =
      true := by
  let Δb0 : RenamingContext.Context :=
    Function.update (Function.update ΔY a! (some wy0)) b! (some DappX)
  let body : Term :=
    (((@ˢx) (Term.var a)) =ˢ Term.var b) ∧ˢ (a!_spec ∧ˢ b!_spec)
  have hΔ_body :
      ∀ v ∈ fv body, v ∉ [a, b] → (Δb0 v).isSome = true := by
    intro v hv hv_not_ab
    exact hφ_exists_ab v (SMT.fv.mem_exists ⟨by simpa [body] using hv, hv_not_ab⟩)
  have hcov_body_upd :
      ∀ W₁ W₂ : SMT.Dom,
        RenamingContext.CoversFV
          (Function.update (Function.update Δb0 a (some W₁)) b (some W₂))
          body := by
    as_aux_lemma =>
    intro W₁ W₂ v hv
    have hv_main :
        v ∈ fv x ∨ v = a ∨ v = b ∨ v = a! ∨ v = b! := by
      have hv' :
          v ∈ SMT.fv (((@ˢx) (Term.var a)) =ˢ Term.var b) ∨
            v ∈ SMT.fv (a!_spec ∧ˢ b!_spec) := by
        simpa [body, fv, or_assoc] using hv
      rcases hv' with hvEq | hvSpecs
      · have hvEq' :
            v ∈ SMT.fv ((@ˢx) (Term.var a)) ∨
              v ∈ SMT.fv (Term.var b) := by
          simpa [fv, or_assoc] using hvEq
        rcases hvEq' with hvApp | hvb
        · have hvApp' :
              v ∈ SMT.fv x ∨ v ∈ SMT.fv (Term.var a) := by
            simpa [fv] using hvApp
          rcases hvApp' with hvx | hva
          · exact Or.inl hvx
          · exact Or.inr <| Or.inl <| by
              rwa [fv, List.mem_singleton] at hva
        · exact Or.inr <| Or.inr <| Or.inl <| by
            rwa [fv, List.mem_singleton] at hvb
      · have hvSpecs' :
            v ∈ SMT.fv a!_spec ∨ v ∈ SMT.fv b!_spec := by
          simpa [fv] using hvSpecs
        rcases hvSpecs' with hvaSpec | hvbSpec
        · have hvA' := fv_a!_spec hvaSpec
          rw [List.mem_union_iff] at hvA'
          rcases hvA' with hva | hva!
          · exact Or.inr <| Or.inl <| by
              rwa [fv, List.mem_singleton] at hva
          · exact Or.inr <| Or.inr <| Or.inr <| Or.inl <| by
              simpa [Singleton.singleton] using hva!
        · have hvB' := fv_b!_spec hvbSpec
          rw [List.mem_union_iff] at hvB'
          rcases hvB' with hvb | hvb!
          · exact Or.inr <| Or.inr <| Or.inl <| by
              rwa [fv, List.mem_singleton] at hvb
          · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| by
              simpa [Singleton.singleton] using hvb!
    rcases hv_main with hvx | rfl | rfl | rfl | rfl
    · rw [Function.update_of_ne (by
          intro h
          subst h
          exact b_not_mem_fv_x hvx)]
      rw [Function.update_of_ne (by
          intro h
          subst h
          exact a_not_mem_fv_x hvx)]
      exact hΔ_body v
        (by simpa [body, fv] using hv)
        (by
          rw [List.mem_cons, List.mem_singleton, not_or]
          exact ⟨by
            intro h
            subst h
            exact a_not_mem_fv_x hvx,
            by
            intro h
            subst h
            exact b_not_mem_fv_x hvx⟩)
    · rw [Function.update_of_ne b_ne_a.symm]
      rw [Function.update_self]
      rfl
    · rw [Function.update_self]
      rfl
    · rw [Function.update_of_ne a!_ne_b]
      rw [Function.update_of_ne a_ne_a!.symm]
      dsimp [Δb0]
      rw [Function.update_of_ne a!_ne_b!]
      rw [Function.update_self]
      rfl
    · rw [Function.update_of_ne b_ne_b!.symm]
      rw [Function.update_of_ne a_ne_b!.symm]
      dsimp [Δb0]
      rw [Function.update_self]
      rfl
  have den_body_some :
      ∀ {w : Fin [a, b].length → SMT.Dom},
        (∀ i, (w i).snd.fst = [α, β][i] ∧ (w i).fst ∈ ⟦[α, β][i]⟧ᶻ) →
          ∃ Dbody : SMT.Dom,
            ⟦(Term.abstract.go body [a, b] Δb0 hΔ_body).uncurry w⟧ˢ = some Dbody ∧
              Dbody.snd.fst = SMTType.bool := by
    intro w hw
    have hgo :=
      funAbstractGoPair
        (Δctx := Δb0) (P := body) (v₁ := a) (v₂ := b)
        (τ₁ := α) (τ₂ := β)
        hΔ_body hcov_body_upd w hw
    rw [hgo]
    let Δw : RenamingContext.Context :=
      Function.update
        (Function.update Δb0 a (some (w ⟨0, by simp⟩)))
        b (some (w ⟨1, by simp⟩))
    have hφa_w :
        RenamingContext.CoversFV Δw a!_spec := by
      intro v hv
      have hv' := fv_a!_spec hv
      rw [List.mem_union_iff] at hv'
      rcases hv' with hva | hva!
      · rw [fv, List.mem_singleton] at hva
        subst hva
        dsimp [Δw, Δb0]
        rw [Function.update_of_ne b_ne_a.symm, Function.update_self]
        rfl
      · have hv_eq : v = a! := by
          change v ∈ ([a!] : List 𝒱) at hva!
          rw [List.mem_singleton] at hva!
          exact hva!
        subst hv_eq
        dsimp [Δw, Δb0]
        rw [Function.update_of_ne a!_ne_b, Function.update_of_ne a_ne_a!.symm,
          Function.update_of_ne a!_ne_b!, Function.update_self]
        rfl
    have hφb_w :
        RenamingContext.CoversFV Δw b!_spec := by
      intro v hv
      have hv' := fv_b!_spec hv
      rw [List.mem_union_iff] at hv'
      rcases hv' with hvb | hvb!
      · rw [fv, List.mem_singleton] at hvb
        subst hvb
        dsimp [Δw]
        rw [Function.update_self]
        rfl
      · have hv_eq : v = b! := by
          change v ∈ ([b!] : List 𝒱) at hvb!
          rw [List.mem_singleton] at hvb!
          exact hvb!
        subst hv_eq
        dsimp [Δw, Δb0]
        rw [Function.update_of_ne b_ne_b!.symm, Function.update_of_ne a_ne_b!.symm,
          Function.update_self]
        rfl
    have hsome_a :
        ⟦a!_spec.abstract
            Δw
            hφa_w⟧ˢ.isSome = true := by
      let Δa : RenamingContext.Context :=
        Function.update (Function.update ΔY a (some (w ⟨0, by simp⟩))) a! (some wy0)
      have hden_eq :
          ⟦a!_spec.abstract Δw hφa_w⟧ˢ =
            ⟦a!_spec.abstract Δa (hφa_at (w ⟨0, by simp⟩))⟧ˢ := by
        apply SMT.RenamingContext.denote_congr_of_agreesOnFV (h1 := hφa_w) (h2 := hφa_at (w ⟨0, by simp⟩))
        intro v hv
        have hv' := fv_a!_spec hv
        rw [List.mem_union_iff] at hv'
        rcases hv' with hva | hva!
        · rw [fv, List.mem_singleton] at hva
          subst hva
          dsimp [Δw, Δa, Δb0]
          rw [Function.update_of_ne b_ne_a.symm, Function.update_self]
          rw [Function.update_of_ne a_ne_a!, Function.update_self]
        · have hv_eq : v = a! := by
            change v ∈ ([a!] : List 𝒱) at hva!
            rw [List.mem_singleton] at hva!
            exact hva!
          cases hv_eq
          dsimp [Δw, Δa, Δb0]
          rw [Function.update_of_ne a!_ne_b, Function.update_of_ne a_ne_a!.symm,
            Function.update_of_ne a!_ne_b!, Function.update_self]
          rw [Function.update_self]
      rw [hden_eq]
      exact a_spec_total_at (w ⟨0, Nat.zero_lt_succ 1⟩) (hw ⟨0, Nat.zero_lt_succ 1⟩).1
    have hsome_b :
        ⟦b!_spec.abstract
            Δw
            hφb_w⟧ˢ.isSome = true := by
      let Δb : RenamingContext.Context :=
        Function.update
          (Function.update (Function.update ΔY a! (some wy0)) b (some (w ⟨1, by simp⟩)))
          b! (some DappX)
      have hden_eq :
          ⟦b!_spec.abstract Δw hφb_w⟧ˢ =
            ⟦b!_spec.abstract Δb (hφb_at (w ⟨1, by simp⟩))⟧ˢ := by
        apply SMT.RenamingContext.denote_congr_of_agreesOnFV (h1 := hφb_w) (h2 := hφb_at (w ⟨1, by simp⟩))
        intro v hv
        have hv' := fv_b!_spec hv
        rw [List.mem_union_iff] at hv'
        rcases hv' with hvb | hvb!
        · rw [fv, List.mem_singleton] at hvb
          subst hvb
          dsimp [Δw, Δb]
          rw [Function.update_self]
          rw [Function.update_of_ne b_ne_b!, Function.update_self]
        · have hv_eq : v = b! := by
            change v ∈ ([b!] : List 𝒱) at hvb!
            rw [List.mem_singleton] at hvb!
            exact hvb!
          cases hv_eq
          dsimp [Δw, Δb, Δb0]
          rw [Function.update_of_ne b_ne_b!.symm, Function.update_of_ne a_ne_b!.symm,
            Function.update_self]
          rw [Function.update_self]
      rw [hden_eq]
      exact b_spec_total_at (w ⟨1, Nat.one_lt_succ_succ 0⟩) (hw ⟨1, Nat.one_lt_succ_succ 0⟩).1
    obtain ⟨Da, hden_a⟩ := Option.isSome_iff_exists.mp hsome_a
    obtain ⟨Db, hden_b⟩ := Option.isSome_iff_exists.mp hsome_b
    have hDa_ty : Da.snd.fst = SMTType.bool := by
      exact denote_type_eq_of_typing (typ_t := typ_a_ctx) (hden := hden_a)
    have hDb_ty : Db.snd.fst = SMTType.bool := by
      exact denote_type_eq_of_typing (typ_t := typ_b_ctx) (hden := hden_b)
    have hcov_app_w :
        RenamingContext.CoversFV Δw ((@ˢx) (Term.var a)) := by
      have hcov_body_w := hcov_body_upd (w ⟨0, by simp⟩) (w ⟨1, by simp⟩)
      intro v hv
      apply hcov_body_w v
      have hvEq :
          v ∈ SMT.fv (((@ˢx) (Term.var a)) =ˢ Term.var b) := by
        simpa [fv, or_assoc] using (Or.inl hv :
          v ∈ SMT.fv ((@ˢx) (Term.var a)) ∨ v ∈ SMT.fv (Term.var b))
      exact (by
        simpa [body, fv, or_assoc] using (Or.inl hvEq :
          v ∈ SMT.fv (((@ˢx) (Term.var a)) =ˢ Term.var b) ∨
            v ∈ SMT.fv (a!_spec ∧ˢ b!_spec)))
    obtain ⟨hcov_xa0, Dxa, hDxa_ty, hden_app_raw⟩ :=
      den_xa_at (w ⟨0, by simp⟩) (hw ⟨0, by simp⟩).1
        (by simpa using (hw ⟨0, by simp⟩).2)
    have hden_app :
        ⟦((@ˢx) (Term.var a)).abstract Δw hcov_app_w⟧ˢ = some Dxa := by
      have hden_eq :
          ⟦((@ˢx) (Term.var a)).abstract Δw hcov_app_w⟧ˢ =
            ⟦((@ˢx) (Term.var a)).abstract
                (Function.update ΔY a (some (w ⟨0, by simp⟩)))
                hcov_xa0⟧ˢ := by
        apply SMT.RenamingContext.denote_congr_of_agreesOnFV (h1 := hcov_app_w) (h2 := hcov_xa0)
        intro v hv
        have hv' :
            v ∈ SMT.fv x ∨ v ∈ SMT.fv (Term.var a) := by
          simpa [fv] using hv
        rcases hv' with hvx | hva
        · have hne_b : v ≠ b := by
            intro h
            subst h
            exact b_not_mem_fv_x hvx
          have hne_a : v ≠ a := by
            intro h
            subst h
            exact a_not_mem_fv_x hvx
          have hne_b! : v ≠ b! := by
            intro h
            subst h
            exact b!_not_mem_fv_x hvx
          have hne_a! : v ≠ a! := by
            intro h
            subst h
            exact a!_not_mem_fv_x hvx
          dsimp [Δw, Δb0]
          rw [Function.update_of_ne hne_b, Function.update_of_ne hne_a,
            Function.update_of_ne hne_b!, Function.update_of_ne hne_a!,
            Function.update_of_ne hne_a]
        · rw [fv, List.mem_singleton] at hva
          subst hva
          dsimp [Δw]
          rw [Function.update_of_ne b_ne_a.symm, Function.update_self, Function.update_self]
      rw [hden_eq]
      exact hden_app_raw
    have hden_var_b :
        ⟦(Term.var b).abstract Δw
            (by
              intro v hv
              rw [fv, List.mem_singleton] at hv
              subst hv
              dsimp [Δw]
              rw [Function.update_self]
              rfl)⟧ˢ =
          some (w ⟨1, by simp⟩) := by
      rw [SMT.Term.abstract.eq_def, SMT.denote, Option.pure_def, Option.some.injEq]
      apply Option.get_of_eq_some
      dsimp [Δw]
      rw [Function.update_self]
    have hcov_eq_w :
        RenamingContext.CoversFV Δw (((@ˢx) (Term.var a)) =ˢ Term.var b) := by
      have hcov_body_w := hcov_body_upd (w ⟨0, by simp⟩) (w ⟨1, by simp⟩)
      intro v hv
      apply hcov_body_w v
      exact (by
        simpa [body, fv, or_assoc] using (Or.inl hv :
          v ∈ SMT.fv (((@ˢx) (Term.var a)) =ˢ Term.var b) ∨
            v ∈ SMT.fv (a!_spec ∧ˢ b!_spec)))
    obtain ⟨Deq, hden_eq_raw, hDeq_ty⟩ :=
      denote_eq_some_of_some (by simpa [proof_irrel_heq] using hden_app) hden_var_b
        (hDxa_ty.trans (hw ⟨1, by simp⟩).1.symm)
    have hden_eq :
        ⟦(((@ˢx) (Term.var a)) =ˢ Term.var b).abstract Δw hcov_eq_w⟧ˢ = some Deq := by
      simpa [SMT.Term.abstract, proof_irrel_heq] using hden_eq_raw
    have hcov_specs_w :
        RenamingContext.CoversFV Δw (a!_spec ∧ˢ b!_spec) := by
      intro v hv
      have hv' :
          v ∈ SMT.fv a!_spec ∨ v ∈ SMT.fv b!_spec := by
        simpa [fv] using hv
      rcases hv' with hva | hvb
      · exact hφa_w v hva
      · exact hφb_w v hvb
    obtain ⟨Dspecs, hden_specs_raw, hDspecs_ty⟩ :=
      denote_and_some_bool_of_some_bool hden_a hDa_ty hden_b hDb_ty
    have hden_specs :
        ⟦(a!_spec ∧ˢ b!_spec).abstract Δw hcov_specs_w⟧ˢ = some Dspecs := by
      simpa [SMT.Term.abstract, proof_irrel_heq] using hden_specs_raw
    obtain ⟨Dbody, hden_body_raw, hDbody_ty⟩ :=
      denote_and_some_bool_of_some_bool hden_eq hDeq_ty hden_specs hDspecs_ty
    have hden_body :
        ⟦body.abstract Δw (hcov_body_upd (w ⟨0, by simp⟩) (w ⟨1, by simp⟩))⟧ˢ = some Dbody := by
      simpa [body, SMT.Term.abstract, proof_irrel_heq] using hden_body_raw
    exact ⟨Dbody, hden_body, hDbody_ty⟩
  have den_body_isSome :
      ∀ {w : Fin [a, b].length → SMT.Dom},
        (∀ i, (w i).snd.fst = [α, β][i] ∧ (w i).fst ∈ ⟦[α, β][i]⟧ᶻ) →
          ⟦(Term.abstract.go body [a, b] Δb0 hΔ_body).uncurry w⟧ˢ.isSome = true := by
    intro w hw
    obtain ⟨Dbody, hden_body, _⟩ := den_body_some hw
    exact Option.isSome_of_eq_some hden_body
  have den_not_body_isSome :
      ∀ {w : Fin [a, b].length → SMT.Dom},
        (∀ i, (w i).snd.fst = [α, β][i] ∧ (w i).fst ∈ ⟦[α, β][i]⟧ᶻ) →
          ⟦¬ˢ' (Term.abstract.go body [a, b] Δb0 hΔ_body).uncurry w⟧ˢ.isSome = true := by
    intro w hw
    obtain ⟨Dbody, hden_body, hDbody_ty⟩ := den_body_some hw
    exact denote_not_isSome_of_some_bool hden_body hDbody_ty
  rw [SMT.Term.abstract, dite_cond_eq_true (eq_true (by rfl)), SMT.PHOAS.Term.exists, SMT.denote]
  simp only [Option.bind_eq_bind, Option.pure_def]
  have hlen_exists : [a, b].length > 0 := by
    simp
  rw [SMT.denote, dite_cond_eq_true (eq_true hlen_exists)]
  split_ifs with den_exists_isSome
  · simp
  · exfalso
    apply den_exists_isSome
    intro w hw
    simpa [SMT.denote] using den_not_body_isSome (w := w) hw

set_option maxHeartbeats 800000 in
theorem funExistsABTrueAtRange.{u}
    {α β α' β' : SMTType}
    {x a!_spec b!_spec : Term}
    {a a! b b! : 𝒱}
    {ΔY : RenamingContext.Context.{u}}
    {wy0 DappX wx₀ y₀ Φa Φb : SMT.Dom.{u}}
    {Γa Γb : TypeContext}
    (fv_a!_spec : fv a!_spec ⊆ fv (Term.var a) ∪ {a!})
    (fv_b!_spec : fv b!_spec ⊆ fv (Term.var b) ∪ {b!})
    (a_not_mem_fv_x : a ∉ fv x)
    (b_not_mem_fv_x : b ∉ fv x)
    (a!_not_mem_fv_x : a! ∉ fv x)
    (b!_not_mem_fv_x : b! ∉ fv x)
    (b_ne_a : b ≠ a)
    (a!_ne_b : a! ≠ b)
    (a_ne_b! : a ≠ b!)
    (b_ne_b! : b ≠ b!)
    (a_ne_a! : a ≠ a!)
    (a!_ne_b! : a! ≠ b!)
    (hφ_exists_ab :
      RenamingContext.CoversFV
        (Function.update (Function.update ΔY a! (some wy0)) b! (some DappX))
        (Term.exists [a, b] [α, β] (((@ˢx) (Term.var a) =ˢ Term.var b) ∧ˢ (a!_spec ∧ˢ b!_spec))))
    (hφa_at :
      ∀ x₀ : SMT.Dom.{u},
        RenamingContext.CoversFV
          (Function.update (Function.update ΔY a (some x₀)) a! (some wy0))
          a!_spec)
    (hφb_at :
      ∀ y₀ : SMT.Dom.{u},
        RenamingContext.CoversFV
          (Function.update (Function.update (Function.update ΔY a! (some wy0)) b (some y₀)) b! (some DappX))
          b!_spec)
    (a_spec_total_at :
      ∀ x₀ : SMT.Dom.{u},
        x₀.snd.fst = α →
          ⟦a!_spec.abstract
              (Function.update (Function.update ΔY a (some x₀)) a! (some wy0))
              (hφa_at x₀)⟧ˢ.isSome =
            true)
    (b_spec_total_at :
      ∀ y₀ : SMT.Dom.{u},
        y₀.snd.fst = β →
          ⟦b!_spec.abstract
              (Function.update (Function.update (Function.update ΔY a! (some wy0)) b (some y₀)) b! (some DappX))
              (hφb_at y₀)⟧ˢ.isSome =
            true)
    (den_xa_at :
      ∀ x₀ : SMT.Dom.{u},
        x₀.snd.fst = α →
          x₀.fst ∈ ⟦α⟧ᶻ →
            ∃ hcov_xa : RenamingContext.CoversFV (Function.update ΔY a (some x₀)) ((@ˢx) (Term.var a)),
              ∃ Dxa : SMT.Dom.{u},
                Dxa.snd.fst = β ∧
                  ⟦((@ˢx) (Term.var a)).abstract (Function.update ΔY a (some x₀)) hcov_xa⟧ˢ =
                    some Dxa)
    (typ_a_ctx : Γa ⊢ˢ a!_spec : SMTType.bool)
    (typ_b_ctx : Γb ⊢ˢ b!_spec : SMTType.bool)
    (hx₀_ty : wx₀.snd.fst = α)
    (hx₀_mem : wx₀.fst ∈ ⟦α⟧ᶻ)
    (hy₀_ty : y₀.snd.fst = β)
    (hcov_xa :
      RenamingContext.CoversFV (Function.update ΔY a (some wx₀)) ((@ˢx) (Term.var a)))
    (hden_xa :
      ⟦((@ˢx) (Term.var a)).abstract (Function.update ΔY a (some wx₀)) hcov_xa⟧ˢ =
        some y₀)
    (hφa0 :
      RenamingContext.CoversFV
        (Function.update (Function.update ΔY a (some wx₀)) a! (some wy0))
        a!_spec)
    (hden_a0 :
      ⟦a!_spec.abstract
          (Function.update (Function.update ΔY a (some wx₀)) a! (some wy0))
          hφa0⟧ˢ =
        some Φa)
    (hΦa_true : Φa.fst = zftrue)
    (hφb0 :
      RenamingContext.CoversFV
        (Function.update (Function.update (Function.update ΔY a! (some wy0)) b (some y₀)) b! (some DappX))
        b!_spec)
    (hden_b0 :
      ⟦b!_spec.abstract
          (Function.update (Function.update (Function.update ΔY a! (some wy0)) b (some y₀)) b! (some DappX))
          hφb0⟧ˢ =
        some Φb)
    (hΦb_true : Φb.fst = zftrue) :
    ⟦(Term.exists [a, b] [α, β] (((@ˢx) (Term.var a) =ˢ Term.var b) ∧ˢ (a!_spec ∧ˢ b!_spec))).abstract
        (Function.update (Function.update ΔY a! (some wy0)) b! (some DappX))
        hφ_exists_ab⟧ˢ =
      some ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
  let Δb0 : RenamingContext.Context :=
    Function.update (Function.update ΔY a! (some wy0)) b! (some DappX)
  let body : Term :=
    (((@ˢx) (Term.var a)) =ˢ Term.var b) ∧ˢ (a!_spec ∧ˢ b!_spec)
  have hΔ_body :
      ∀ v ∈ fv body, v ∉ [a, b] → (Δb0 v).isSome = true := by
    intro v hv hv_not_ab
    exact hφ_exists_ab v (SMT.fv.mem_exists ⟨by simpa [body] using hv, hv_not_ab⟩)
  have hcov_body_upd :
      ∀ W₁ W₂ : SMT.Dom,
        RenamingContext.CoversFV
          (Function.update (Function.update Δb0 a (some W₁)) b (some W₂))
          body := by
    as_aux_lemma =>
    intro W₁ W₂ v hv
    have hv_main :
        v ∈ fv x ∨ v = a ∨ v = b ∨ v = a! ∨ v = b! := by
      have hv' :
          v ∈ SMT.fv (((@ˢx) (Term.var a)) =ˢ Term.var b) ∨
            v ∈ SMT.fv (a!_spec ∧ˢ b!_spec) := by
        simpa [body, fv, or_assoc] using hv
      rcases hv' with hvEq | hvSpecs
      · have hvEq' :
            v ∈ SMT.fv ((@ˢx) (Term.var a)) ∨
              v ∈ SMT.fv (Term.var b) := by
          simpa [fv, or_assoc] using hvEq
        rcases hvEq' with hvApp | hvb
        · have hvApp' :
              v ∈ SMT.fv x ∨ v ∈ SMT.fv (Term.var a) := by
            simpa [fv] using hvApp
          rcases hvApp' with hvx | hva
          · exact Or.inl hvx
          · exact Or.inr <| Or.inl <| by
              rwa [fv, List.mem_singleton] at hva
        · exact Or.inr <| Or.inr <| Or.inl <| by
            rwa [fv, List.mem_singleton] at hvb
      · have hvSpecs' :
            v ∈ SMT.fv a!_spec ∨ v ∈ SMT.fv b!_spec := by
          simpa [fv] using hvSpecs
        rcases hvSpecs' with hvaSpec | hvbSpec
        · have hvA' := fv_a!_spec hvaSpec
          rw [List.mem_union_iff] at hvA'
          rcases hvA' with hva | hva!
          · exact Or.inr <| Or.inl <| by
              rwa [fv, List.mem_singleton] at hva
          · exact Or.inr <| Or.inr <| Or.inr <| Or.inl <| by
              simpa [Singleton.singleton] using hva!
        · have hvB' := fv_b!_spec hvbSpec
          rw [List.mem_union_iff] at hvB'
          rcases hvB' with hvb | hvb!
          · exact Or.inr <| Or.inr <| Or.inl <| by
              rwa [fv, List.mem_singleton] at hvb
          · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| by
              simpa [Singleton.singleton] using hvb!
    rcases hv_main with hvx | rfl | rfl | rfl | rfl
    · rw [Function.update_of_ne (by
          rintro rfl
          exact b_not_mem_fv_x hvx)]
      rw [Function.update_of_ne (by
          rintro rfl
          exact a_not_mem_fv_x hvx)]
      exact hΔ_body v
        hv
        (by
          rw [List.mem_cons, List.mem_singleton, not_or]
          constructor
          · rintro rfl
            exact a_not_mem_fv_x hvx
          · rintro rfl
            exact b_not_mem_fv_x hvx)
    · rw [Function.update_of_ne b_ne_a.symm]
      rw [Function.update_self]
      rfl
    · rw [Function.update_self]
      rfl
    · rw [Function.update_of_ne a!_ne_b]
      rw [Function.update_of_ne a_ne_a!.symm]
      dsimp [Δb0]
      apply hΔ_body
      · exact hv
      · rw [List.mem_cons, List.mem_singleton, not_or]
        exact ⟨a_ne_a!.symm, a!_ne_b⟩
    · rw [Function.update_of_ne b_ne_b!.symm]
      rw [Function.update_of_ne a_ne_b!.symm]
      apply hΔ_body
      · exact hv
      · rw [List.mem_cons, List.mem_singleton, not_or]
        exact ⟨a_ne_b!.symm, b_ne_b!.symm⟩
  have den_body_some :
      ∀ {w : Fin [a, b].length → SMT.Dom},
        (∀ i, (w i).snd.fst = [α, β][i] ∧ (w i).fst ∈ ⟦[α, β][i]⟧ᶻ) →
          ∃ Dbody : SMT.Dom,
            ⟦(Term.abstract.go body [a, b] Δb0 hΔ_body).uncurry w⟧ˢ = some Dbody ∧
              Dbody.snd.fst = SMTType.bool := by
    intro w hw
    have hgo :=
      funAbstractGoPair
        (Δctx := Δb0) (P := body) (v₁ := a) (v₂ := b)
        (τ₁ := α) (τ₂ := β)
        hΔ_body hcov_body_upd w hw
    rw [hgo]
    let Δw : RenamingContext.Context :=
      Function.update
        (Function.update Δb0 a (some (w ⟨0, by simp⟩)))
        b (some (w ⟨1, by simp⟩))
    have hφa_w :
        RenamingContext.CoversFV Δw a!_spec := by
      intro v hv
      have hv' := fv_a!_spec hv
      rw [List.mem_union_iff] at hv'
      rcases hv' with hva | hva!
      · rw [fv, List.mem_singleton] at hva
        subst hva
        dsimp [Δw, Δb0]
        rw [Function.update_of_ne b_ne_a.symm, Function.update_self]
        rfl
      · have hv_eq : v = a! := by
          simpa [Singleton.singleton] using hva!
        subst hv_eq
        dsimp [Δw, Δb0]
        rw [Function.update_of_ne a!_ne_b, Function.update_of_ne a_ne_a!.symm,
          Function.update_of_ne a!_ne_b!, Function.update_self]
        rfl
    have hφb_w :
        RenamingContext.CoversFV Δw b!_spec := by
      intro v hv
      have hv' := fv_b!_spec hv
      rw [List.mem_union_iff] at hv'
      rcases hv' with hvb | hvb!
      · rw [fv, List.mem_singleton] at hvb
        subst hvb
        dsimp [Δw]
        rw [Function.update_self]
        rfl
      · have hv_eq : v = b! := by
          simpa [Singleton.singleton] using hvb!
        subst hv_eq
        dsimp [Δw, Δb0]
        rw [Function.update_of_ne b_ne_b!.symm, Function.update_of_ne a_ne_b!.symm,
          Function.update_self]
        rfl
    have hsome_a :
        ⟦a!_spec.abstract
            Δw
            hφa_w⟧ˢ.isSome = true := by
      let Δa : RenamingContext.Context :=
        Function.update (Function.update ΔY a (some (w ⟨0, by simp⟩))) a! (some wy0)
      have hden_eq :
          ⟦a!_spec.abstract Δw hφa_w⟧ˢ =
            ⟦a!_spec.abstract Δa (hφa_at (w ⟨0, by simp⟩))⟧ˢ := by
        apply SMT.RenamingContext.denote_congr_of_agreesOnFV (h1 := hφa_w) (h2 := hφa_at (w ⟨0, by simp⟩))
        intro v hv
        have hv' := fv_a!_spec hv
        rw [List.mem_union_iff] at hv'
        rcases hv' with hva | hva!
        · rw [fv, List.mem_singleton] at hva
          subst hva
          dsimp [Δw, Δa, Δb0]
          rw [Function.update_of_ne b_ne_a.symm, Function.update_self]
          rw [Function.update_of_ne a_ne_a!, Function.update_self]
        · have hv_eq : v = a! := by
            simpa [Singleton.singleton] using hva!
          subst hv_eq
          dsimp [Δw, Δa, Δb0]
          rw [Function.update_of_ne a!_ne_b, Function.update_of_ne a_ne_a!.symm,
            Function.update_of_ne a!_ne_b!, Function.update_self]
          rw [Function.update_self]
      rw [hden_eq]
      exact a_spec_total_at (w ⟨0, Nat.zero_lt_succ 1⟩) (hw ⟨0, Nat.zero_lt_succ 1⟩).1
    have hsome_b :
        ⟦b!_spec.abstract
            Δw
            hφb_w⟧ˢ.isSome = true := by
      let Δb : RenamingContext.Context :=
        Function.update
          (Function.update (Function.update ΔY a! (some wy0)) b (some (w ⟨1, by simp⟩)))
          b! (some DappX)
      have hden_eq :
          ⟦b!_spec.abstract Δw hφb_w⟧ˢ =
            ⟦b!_spec.abstract Δb (hφb_at (w ⟨1, by simp⟩))⟧ˢ := by
        apply SMT.RenamingContext.denote_congr_of_agreesOnFV (h1 := hφb_w) (h2 := hφb_at (w ⟨1, by simp⟩))
        intro v hv
        have hv' := fv_b!_spec hv
        rw [List.mem_union_iff] at hv'
        rcases hv' with hvb | hvb!
        · rw [fv, List.mem_singleton] at hvb
          subst hvb
          dsimp [Δw, Δb, Δb0]
          rw [Function.update_self]
          rw [Function.update_of_ne b_ne_b!, Function.update_self]
        · have hv_eq : v = b! := by
            simpa [Singleton.singleton] using hvb!
          subst hv_eq
          dsimp [Δw, Δb, Δb0]
          rw [Function.update_of_ne b_ne_b!.symm, Function.update_of_ne a_ne_b!.symm,
            Function.update_self]
          rw [Function.update_self]
      rw [hden_eq]
      exact b_spec_total_at (w ⟨1, Nat.one_lt_succ_succ 0⟩) (hw ⟨1, Nat.one_lt_succ_succ 0⟩).1
    obtain ⟨Da, hden_a⟩ := Option.isSome_iff_exists.mp hsome_a
    obtain ⟨Db, hden_b⟩ := Option.isSome_iff_exists.mp hsome_b
    have hDa_ty : Da.snd.fst = SMTType.bool := by
      exact denote_type_eq_of_typing (typ_t := typ_a_ctx) (hden := hden_a)
    have hDb_ty : Db.snd.fst = SMTType.bool := by
      exact denote_type_eq_of_typing (typ_t := typ_b_ctx) (hden := hden_b)
    have hcov_app_w :
        RenamingContext.CoversFV Δw ((@ˢx) (Term.var a)) := by
      have hcov_body_w := hcov_body_upd (w ⟨0, by simp⟩) (w ⟨1, by simp⟩)
      intro v hv
      apply hcov_body_w v
      have hvEq :
          v ∈ SMT.fv (((@ˢx) (Term.var a)) =ˢ Term.var b) := by
        simpa [fv, or_assoc] using (Or.inl hv :
          v ∈ SMT.fv ((@ˢx) (Term.var a)) ∨ v ∈ SMT.fv (Term.var b))
      exact (by
        simpa [body, fv, or_assoc] using (Or.inl hvEq :
          v ∈ SMT.fv (((@ˢx) (Term.var a)) =ˢ Term.var b) ∨
            v ∈ SMT.fv (a!_spec ∧ˢ b!_spec)))
    obtain ⟨hcov_xa0, Dxa, hDxa_ty, hden_app_raw⟩ :=
      den_xa_at (w ⟨0, by simp⟩) (hw ⟨0, by simp⟩).1
        (by simpa using (hw ⟨0, by simp⟩).2)
    have hden_app :
        ⟦((@ˢx) (Term.var a)).abstract Δw hcov_app_w⟧ˢ = some Dxa := by
      have hden_eq :
          ⟦((@ˢx) (Term.var a)).abstract Δw hcov_app_w⟧ˢ =
            ⟦((@ˢx) (Term.var a)).abstract
                (Function.update ΔY a (some (w ⟨0, by simp⟩)))
                hcov_xa0⟧ˢ := by
        apply SMT.RenamingContext.denote_congr_of_agreesOnFV (h1 := hcov_app_w) (h2 := hcov_xa0)
        intro v hv
        have hv' :
            v ∈ SMT.fv x ∨ v ∈ SMT.fv (Term.var a) := by
          simpa [fv] using hv
        rcases hv' with hvx | hva
        · have hne_b : v ≠ b := by
            intro h
            subst h
            exact b_not_mem_fv_x hvx
          have hne_a : v ≠ a := by
            intro h
            subst h
            exact a_not_mem_fv_x hvx
          have hne_b! : v ≠ b! := by
            intro h
            subst h
            exact b!_not_mem_fv_x hvx
          have hne_a! : v ≠ a! := by
            intro h
            subst h
            exact a!_not_mem_fv_x hvx
          dsimp [Δw, Δb0]
          rw [Function.update_of_ne hne_b, Function.update_of_ne hne_a,
            Function.update_of_ne hne_b!, Function.update_of_ne hne_a!,
            Function.update_of_ne hne_a]
        · rw [fv, List.mem_singleton] at hva
          subst hva
          dsimp [Δw]
          rw [Function.update_of_ne b_ne_a.symm, Function.update_self, Function.update_self]
      rw [hden_eq]
      exact hden_app_raw
    have hsome_app :
        ⟦((@ˢx) (Term.var a)).abstract Δw hcov_app_w⟧ˢ.isSome = true := by
      exact Option.isSome_of_eq_some hden_app
    have hden_var_b :
        ⟦(Term.var b).abstract Δw
            (by
              intro v hv
              rw [fv, List.mem_singleton] at hv
              subst hv
              dsimp [Δw]
              rw [Function.update_self]
              rfl)⟧ˢ =
          some (w ⟨1, by simp⟩) := by
      rw [SMT.Term.abstract.eq_def, SMT.denote, Option.pure_def, Option.some.injEq]
      apply Option.get_of_eq_some
      dsimp [Δw]
      rw [Function.update_self]
    have hcov_eq_w :
        RenamingContext.CoversFV Δw (((@ˢx) (Term.var a)) =ˢ Term.var b) := by
      have hcov_body_w := hcov_body_upd (w ⟨0, by simp⟩) (w ⟨1, by simp⟩)
      intro v hv
      apply hcov_body_w v
      exact (by
        simpa [body, fv, or_assoc] using (Or.inl hv :
          v ∈ SMT.fv (((@ˢx) (Term.var a)) =ˢ Term.var b) ∨
            v ∈ SMT.fv (a!_spec ∧ˢ b!_spec)))
    have hsome_eq :
        ⟦(((@ˢx) (Term.var a)) =ˢ Term.var b).abstract Δw hcov_eq_w⟧ˢ.isSome = true := by
      have hEq_ty : Dxa.snd.fst = (w ⟨1, by simp⟩).snd.fst := by
        exact hDxa_ty.trans (hw ⟨1, by simp⟩).1.symm
      obtain ⟨Deq, hden_eq_raw, _⟩ :=
        denote_eq_some_of_some (by simpa [proof_irrel_heq] using hden_app) hden_var_b hEq_ty
      have hden_eq :
          ⟦(((@ˢx) (Term.var a)) =ˢ Term.var b).abstract Δw hcov_eq_w⟧ˢ = some Deq := by
        simpa [SMT.Term.abstract, proof_irrel_heq] using hden_eq_raw
      exact Option.isSome_of_eq_some hden_eq
    have hcov_specs_w :
        RenamingContext.CoversFV Δw (a!_spec ∧ˢ b!_spec) := by
      intro v hv
      have hv' :
          v ∈ SMT.fv a!_spec ∨ v ∈ SMT.fv b!_spec := by
        simpa [fv] using hv
      rcases hv' with hva | hvb
      · exact hφa_w v hva
      · exact hφb_w v hvb
    have hsome_specs :
        ⟦(a!_spec ∧ˢ b!_spec).abstract
            Δw hcov_specs_w⟧ˢ.isSome = true := by
      obtain ⟨Dspecs, hden_specs_raw, _⟩ :=
        denote_and_some_bool_of_some_bool hden_a hDa_ty hden_b hDb_ty
      have hden_specs :
          ⟦(a!_spec ∧ˢ b!_spec).abstract Δw hcov_specs_w⟧ˢ = some Dspecs := by
        simpa [SMT.Term.abstract, proof_irrel_heq] using hden_specs_raw
      exact Option.isSome_of_eq_some hden_specs
    have hEq_ty : Dxa.snd.fst = (w ⟨1, by simp⟩).snd.fst := by
      exact hDxa_ty.trans (hw ⟨1, by simp⟩).1.symm
    obtain ⟨Deq, hden_eq_raw, hDeq_ty⟩ :=
      denote_eq_some_of_some (by simpa [proof_irrel_heq] using hden_app) hden_var_b hEq_ty
    have hden_eq :
        ⟦(((@ˢx) (Term.var a)) =ˢ Term.var b).abstract Δw hcov_eq_w⟧ˢ = some Deq := by
      simpa [SMT.Term.abstract, proof_irrel_heq] using hden_eq_raw
    obtain ⟨Dspecs, hden_specs_raw, hDspecs_ty⟩ :=
      denote_and_some_bool_of_some_bool hden_a hDa_ty hden_b hDb_ty
    have hden_specs :
        ⟦(a!_spec ∧ˢ b!_spec).abstract Δw hcov_specs_w⟧ˢ = some Dspecs := by
      simpa [SMT.Term.abstract, proof_irrel_heq] using hden_specs_raw
    obtain ⟨Dbody, hden_body_raw, hDbody_ty⟩ :=
      denote_and_some_bool_of_some_bool hden_eq hDeq_ty hden_specs hDspecs_ty
    have hden_body :
        ⟦body.abstract Δw (hcov_body_upd (w ⟨0, by simp⟩) (w ⟨1, by simp⟩))⟧ˢ = some Dbody := by
      simpa [body, SMT.Term.abstract, proof_irrel_heq] using hden_body_raw
    exact ⟨Dbody, hden_body, hDbody_ty⟩
  have den_not_body_isSome :
      ∀ {w : Fin [a, b].length → SMT.Dom},
        (∀ i, (w i).snd.fst = [α, β][i] ∧ (w i).fst ∈ ⟦[α, β][i]⟧ᶻ) →
          ⟦¬ˢ' (Term.abstract.go body [a, b] Δb0 hΔ_body).uncurry w⟧ˢ.isSome = true := by
    intro w hw
    obtain ⟨Dbody, hden_body, hDbody_ty⟩ := den_body_some hw
    exact denote_not_isSome_of_some_bool hden_body hDbody_ty
  have den_body_isSome :
      ∀ {w : Fin [a, b].length → SMT.Dom},
        (∀ i, (w i).snd.fst = [α, β][i] ∧ (w i).fst ∈ ⟦[α, β][i]⟧ᶻ) →
          ⟦(Term.abstract.go body [a, b] Δb0 hΔ_body).uncurry w⟧ˢ.isSome = true := by
    intro w hw
    obtain ⟨Dbody, hden_body, _hDbody_ty⟩ := den_body_some hw
    exact Option.isSome_of_eq_some hden_body
  have hΦa_ty : Φa.snd.fst = SMTType.bool := by
    exact denote_type_eq_of_typing (typ_t := typ_a_ctx) (hden := hden_a0)
  have hΦb_ty : Φb.snd.fst = SMTType.bool := by
    exact denote_type_eq_of_typing (typ_t := typ_b_ctx) (hden := hden_b0)
  let D : ZFSet := ⟦α⟧ᶻ.prod ⟦β⟧ᶻ
  let bodyF : ZFSet → ZFSet := fun y =>
    if hy : y.hasArity [a, b].length ∧
        ∀ i : Fin [a, b].length,
          y.get [a, b].length i ∈ ⟦[α, β][i]⟧ᶻ then
      (⟦¬ˢ'
          (Term.abstract.go body [a, b] Δb0 hΔ_body).uncurry
            (fun i => (⟨y.get [a, b].length i, [α, β][i], hy.2 i⟩ : SMT.Dom))⟧ˢ.get
        (by
          simpa [SMT.denote] using
            (den_not_body_isSome
              (w := fun i => (⟨y.get [a, b].length i, [α, β][i], hy.2 i⟩ : SMT.Dom))
              (by
                intro i
                exact ⟨rfl, hy.2 i⟩)))).fst
    else
      zffalse
  have hbodyF_witness :
      bodyF (wx₀.fst.pair y₀.fst) = zffalse := by
    let Δgoal : RenamingContext.Context :=
      Function.update (Function.update Δb0 a (some wx₀)) b (some y₀)
    have hφa_goal :
        RenamingContext.CoversFV Δgoal a!_spec := by
      intro v hv
      have hv' := fv_a!_spec hv
      rw [List.mem_union_iff] at hv'
      rcases hv' with hva | hva!
      · rw [fv, List.mem_singleton] at hva
        subst hva
        dsimp [Δgoal, Δb0]
        rw [Function.update_of_ne b_ne_a.symm]
        rw [Function.update_self]
        rfl
      · have hv_eq : v = a! := by
          simpa [Singleton.singleton] using hva!
        subst hv_eq
        dsimp [Δgoal, Δb0]
        rw [Function.update_of_ne a!_ne_b, Function.update_of_ne a_ne_a!.symm,
          Function.update_of_ne a!_ne_b!, Function.update_self]
        rfl
    have hφb_goal :
        RenamingContext.CoversFV Δgoal b!_spec := by
      intro v hv
      have hv' := fv_b!_spec hv
      rw [List.mem_union_iff] at hv'
      rcases hv' with hvb | hvb!
      · rw [fv, List.mem_singleton] at hvb
        subst hvb
        dsimp [Δgoal]
        rw [Function.update_self]
        rfl
      · have hv_eq : v = b! := by
          simpa [Singleton.singleton] using hvb!
        subst hv_eq
        dsimp [Δgoal, Δb0]
        rw [Function.update_of_ne b_ne_b!.symm, Function.update_of_ne a_ne_b!.symm,
          Function.update_self]
        rfl
    have hden_a_goal :
        ⟦a!_spec.abstract Δgoal hφa_goal⟧ˢ = some Φa := by
      as_aux_lemma =>
      have hden_eq :
          ⟦a!_spec.abstract Δgoal hφa_goal⟧ˢ =
            ⟦a!_spec.abstract
                (Function.update (Function.update ΔY a (some wx₀)) a! (some wy0))
                hφa0⟧ˢ := by
        apply SMT.RenamingContext.denote_congr_of_agreesOnFV
          (h1 := hφa_goal) (h2 := hφa0)
        intro v hv
        have hv' := fv_a!_spec hv
        rw [List.mem_union_iff] at hv'
        rcases hv' with hva | hva!
        · rw [fv, List.mem_singleton] at hva
          subst hva
          dsimp [Δgoal, Δb0]
          rw [Function.update_of_ne b_ne_a.symm, Function.update_self]
          rw [Function.update_of_ne a_ne_a!, Function.update_self]
        · have hv_eq : v = a! := by
            simpa [Singleton.singleton] using hva!
          subst hv_eq
          dsimp [Δgoal, Δb0]
          rw [Function.update_of_ne a!_ne_b, Function.update_of_ne a_ne_a!.symm,
            Function.update_of_ne a!_ne_b!, Function.update_self]
          rw [Function.update_self]
      rw [hden_eq]
      exact hden_a0
    have hden_b_goal :
        ⟦b!_spec.abstract Δgoal hφb_goal⟧ˢ = some Φb := by
      as_aux_lemma =>
      have hden_eq :
          ⟦b!_spec.abstract Δgoal hφb_goal⟧ˢ =
            ⟦b!_spec.abstract
                (Function.update (Function.update (Function.update ΔY a! (some wy0)) b (some y₀)) b! (some DappX))
                hφb0⟧ˢ := by
        apply SMT.RenamingContext.denote_congr_of_agreesOnFV
          (h1 := hφb_goal) (h2 := hφb0)
        intro v hv
        have hv' := fv_b!_spec hv
        rw [List.mem_union_iff] at hv'
        rcases hv' with hvb | hvb!
        · rw [fv, List.mem_singleton] at hvb
          subst hvb
          dsimp [Δgoal]
          rw [Function.update_self]
          rw [Function.update_of_ne b_ne_b!, Function.update_self]
        · have hv_eq : v = b! := by
            simpa [Singleton.singleton] using hvb!
          subst hv_eq
          dsimp [Δgoal, Δb0]
          rw [Function.update_of_ne b_ne_b!.symm, Function.update_of_ne a_ne_b!.symm,
            Function.update_self]
          rw [Function.update_self]
      rw [hden_eq]
      exact hden_b0
    have hden_specs_true :
        ⟦(a!_spec ∧ˢ b!_spec).abstract Δgoal
            (by
              intro v hv
              have hv' :
                  v ∈ SMT.fv a!_spec ∨ v ∈ SMT.fv b!_spec := by
                simpa [fv] using hv
              rcases hv' with hva | hvb
              · exact hφa_goal v hva
              · exact hφb_goal v hvb)⟧ˢ =
          some ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
      as_aux_lemma =>
      rw [Term.abstract]
      exact denote_and_eq_zftrue_of_some_zftrue
        hden_a_goal hΦa_ty hΦa_true
        hden_b_goal hΦb_ty hΦb_true
    have hden_var_b :
        ⟦(Term.var b).abstract Δgoal
            (by
              intro v hv
              rw [fv, List.mem_singleton] at hv
              subst hv
              dsimp [Δgoal]
              rw [Function.update_self]
              rfl)⟧ˢ = some y₀ := by
      rw [SMT.Term.abstract.eq_def, SMT.denote, Option.pure_def, Option.some.injEq]
      apply Option.get_of_eq_some
      dsimp [Δgoal]
      exact Function.update_self _ _ _
    have hcov_app_goal :
        RenamingContext.CoversFV Δgoal ((@ˢx) (Term.var a)) := by
      have hcov_body_goal := hcov_body_upd wx₀ y₀
      intro v hv
      apply hcov_body_goal v
      have hvEq :
          v ∈ SMT.fv (((@ˢx) (Term.var a)) =ˢ Term.var b) := by
        simpa [fv, or_assoc] using (Or.inl hv :
          v ∈ SMT.fv ((@ˢx) (Term.var a)) ∨ v ∈ SMT.fv (Term.var b))
      exact (by
        simpa [body, fv, or_assoc] using (Or.inl hvEq :
          v ∈ SMT.fv (((@ˢx) (Term.var a)) =ˢ Term.var b) ∨
            v ∈ SMT.fv (a!_spec ∧ˢ b!_spec)))
    have hcov_eq_goal :
        RenamingContext.CoversFV Δgoal ((@ˢx) (Term.var a) =ˢ Term.var b) := by
      have hcov_body_goal := hcov_body_upd wx₀ y₀
      intro v hv
      apply hcov_body_goal v
      exact (by
        simpa [body, fv, or_assoc] using (Or.inl hv :
          v ∈ SMT.fv (((@ˢx) (Term.var a)) =ˢ Term.var b) ∨
            v ∈ SMT.fv (a!_spec ∧ˢ b!_spec)))
    have hden_app_goal :
        ⟦((@ˢx) (Term.var a)).abstract Δgoal hcov_app_goal⟧ˢ = some y₀ := by
      have hden_eq :
          ⟦((@ˢx) (Term.var a)).abstract Δgoal hcov_app_goal⟧ˢ =
            ⟦((@ˢx) (Term.var a)).abstract (Function.update ΔY a (some wx₀)) hcov_xa⟧ˢ := by
        apply SMT.RenamingContext.denote_congr_of_agreesOnFV (h1 := hcov_app_goal) (h2 := hcov_xa)
        intro v hv
        have hv' :
            v ∈ SMT.fv x ∨ v ∈ SMT.fv (Term.var a) := by
          simpa [fv] using hv
        rcases hv' with hvx | hva
        · have hne_b : v ≠ b := by
            intro h
            subst h
            exact b_not_mem_fv_x hvx
          have hne_a : v ≠ a := by
            intro h
            subst h
            exact a_not_mem_fv_x hvx
          have hne_b! : v ≠ b! := by
            intro h
            subst h
            exact b!_not_mem_fv_x hvx
          have hne_a! : v ≠ a! := by
            intro h
            subst h
            exact a!_not_mem_fv_x hvx
          dsimp [Δgoal, Δb0]
          rw [Function.update_of_ne hne_b, Function.update_of_ne hne_a,
            Function.update_of_ne hne_b!, Function.update_of_ne hne_a!,
            Function.update_of_ne hne_a]
        · rw [fv, List.mem_singleton] at hva
          subst hva
          dsimp [Δgoal]
          rw [Function.update_of_ne b_ne_a.symm, Function.update_self, Function.update_self]
      rw [hden_eq]
      exact hden_xa
    have hden_eq_true :
        ⟦(((@ˢx) (Term.var a)) =ˢ Term.var b).abstract Δgoal hcov_eq_goal⟧ˢ =
          some ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
      as_aux_lemma =>
      simpa [SMT.Term.abstract, proof_irrel_heq] using
        (denote_eq_eq_zftrue_of_fst_eq hden_app_goal hden_var_b rfl rfl)
    have hden_body_true :
        ⟦body.abstract Δgoal (hcov_body_upd wx₀ y₀)⟧ˢ =
          some ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
      rw [Term.abstract]
      exact denote_and_eq_zftrue_of_some_zftrue
        hden_eq_true rfl rfl
        hden_specs_true rfl rfl
    have hden_not_false :
        ⟦¬ˢ' (Term.abstract.go body [a, b] Δb0 hΔ_body).uncurry
            (fun i => if i = ⟨1, by simp⟩ then y₀ else wx₀)⟧ˢ =
          some ⟨zffalse, SMTType.bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
      as_aux_lemma =>
      have hw :
          ∀ i : Fin [a, b].length,
            ((fun i => if i = ⟨1, by simp⟩ then y₀ else wx₀) i).snd.fst =
                [α, β][i] ∧
              ((fun i => if i = ⟨1, by simp⟩ then y₀ else wx₀) i).fst ∈
                ⟦[α, β][i]⟧ᶻ := by
        intro i
        have hi_lt : i.1 < 2 := by
          simpa using i.2
        have hi : i.1 = 0 ∨ i.1 = 1 := by
          omega
        rcases hi with hi | hi
        · have hi' : i = ⟨0, by simp⟩ := by
            apply Fin.ext
            exact hi
          rw [hi']
          simpa [hx₀_ty, hy₀_ty] using And.intro hx₀_ty hx₀_mem
        · have hi' : i = ⟨1, by simp⟩ := by
            apply Fin.ext
            exact hi
          rw [hi']
          have hy₀_mem : y₀.fst ∈ ⟦β⟧ᶻ := by
            rw [← hy₀_ty]
            exact y₀.snd.snd
          simpa [hx₀_ty, hy₀_ty] using And.intro hy₀_ty hy₀_mem
      have hgo :=
        funAbstractGoPair
          (Δctx := Δb0) (P := body) (v₁ := a) (v₂ := b)
          (τ₁ := α) (τ₂ := β)
          hΔ_body hcov_body_upd
          (fun i => if i = ⟨1, by simp⟩ then y₀ else wx₀) hw
      rw [hgo]
      exact denote_not_eq_zffalse_of_some_zftrue hden_body_true rfl rfl
    let x₀ := wx₀.fst
    have hy₀_mem : y₀.fst ∈ ⟦β⟧ᶻ := by
      rw [← hy₀_ty]
      exact y₀.snd.snd
    have hy :
        (x₀.pair y₀.fst).hasArity [a, b].length ∧
          ∀ i : Fin [a, b].length,
            (x₀.pair y₀.fst).get [a, b].length i ∈ ⟦[α, β][i]⟧ᶻ := by
      constructor
      · simp [ZFSet.hasArity]
      · intro i
        have hi_lt : i.1 < 2 := by
          simpa using i.2
        have hi : i.1 = 0 ∨ i.1 = 1 := by
          omega
        rcases hi with hi | hi
        · have hi' : i = ⟨0, by simp⟩ := by
            apply Fin.ext
            exact hi
          rw [hi']
          simpa [x₀] using hx₀_mem
        · have hi' : i = ⟨1, by simp⟩ := by
            apply Fin.ext
            exact hi
          rw [hi']
          simpa [x₀] using hy₀_mem
    change
      (if hy' :
          (x₀.pair y₀.fst).hasArity [a, b].length ∧
            ∀ i : Fin [a, b].length,
              (x₀.pair y₀.fst).get [a, b].length i ∈ ⟦[α, β][i]⟧ᶻ
        then
          (⟦¬ˢ' (Term.abstract.go body [a, b] Δb0 hΔ_body).uncurry
              (fun i =>
                (⟨(x₀.pair y₀.fst).get [a, b].length i, [α, β][i], hy'.2 i⟩ : SMT.Dom))⟧ˢ.get
            (by
              simpa [SMT.denote] using
                (den_not_body_isSome
                  (w := fun i =>
                    (⟨(x₀.pair y₀.fst).get [a, b].length i, [α, β][i], hy'.2 i⟩ : SMT.Dom))
                  (by
                    intro i
                    exact ⟨rfl, hy'.2 i⟩)))).fst
        else zffalse) = zffalse
    rw [dif_pos hy]
    have hw :
        ∀ i : Fin [a, b].length,
          ((fun i => (⟨(x₀.pair y₀.fst).get [a, b].length i, [α, β][i], hy.2 i⟩ : SMT.Dom)) i).snd.fst =
            [α, β][i] ∧
          ((fun i => (⟨(x₀.pair y₀.fst).get [a, b].length i, [α, β][i], hy.2 i⟩ : SMT.Dom)) i).fst ∈
            ⟦[α, β][i]⟧ᶻ := by
      intro i
      exact ⟨rfl, hy.2 i⟩
    have hget :
        (⟦¬ˢ' (Term.abstract.go body [a, b] Δb0 hΔ_body).uncurry
            (fun i => ⟨(x₀.pair y₀.fst).get [a, b].length i, [α, β][i], hy.2 i⟩)⟧ˢ.get
          (by
            simpa [SMT.denote] using
              (den_not_body_isSome
                (w := fun i => ⟨(x₀.pair y₀.fst).get [a, b].length i, [α, β][i], hy.2 i⟩)
                  (by
                    intro i
                    exact ⟨rfl, hy.2 i⟩)))).fst = zffalse := by
      have hgo :=
        funAbstractGoPair
          (Δctx := Δb0) (P := body) (v₁ := a) (v₂ := b)
          (τ₁ := α) (τ₂ := β)
          hΔ_body hcov_body_upd
          (fun i => ⟨(x₀.pair y₀.fst).get [a, b].length i, [α, β][i], hy.2 i⟩) hw
      have hw0 :
          (fun i => ⟨(x₀.pair y₀.fst).get [a, b].length i, [α, β][i], hy.2 i⟩) ⟨0, by simp⟩ = wx₀ := by
        obtain ⟨fsr, ty, hmem⟩ := wx₀
        cases hx₀_ty
        apply PSigma.ext
        · simp [x₀, ZFSet.get]
        · simp only [List.length_cons, List.length_nil, Nat.reduceAdd, ZFSet.get,
          Fin.reduceLast, Fin.isValue, dite_eq_ite, Fin.getElem_fin, Fin.zero_eta,
          Fin.zero_eq_one_iff, Nat.succ_ne_self, ↓dreduceIte, Fin.coe_ofNat_eq_mod,
          Nat.zero_mod, List.getElem_cons_zero, ↓dreduceDIte, Fin.castPred_zero]
          congr
          · funext τ
            simp only [π₁_pair, eq_iff_iff]
            rfl
          · apply proof_irrel_heq
      have hw1 :
          (fun i => ⟨(x₀.pair y₀.fst).get [a, b].length i, [α, β][i], hy.2 i⟩) ⟨1, by simp⟩ = y₀ := by
        rcases y₀ with ⟨fst, ty, hmem⟩
        cases hy₀_ty
        apply PSigma.ext
        · simp [x₀, ZFSet.get]
        · simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_one_sub_one,
            ZFSet.get, Fin.reduceLast, Fin.isValue, dite_eq_ite, Fin.getElem_fin,
            Fin.zero_eta, Fin.zero_eq_one_iff, Nat.succ_ne_self, ↓dreduceIte,
            Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.getElem_cons_zero,
            List.getElem_cons_succ, ↓dreduceDIte, Fin.castPred_zero]
          congr
          · funext τ
            simp only [π₂_pair, eq_iff_iff]
            rfl
          · apply proof_irrel_heq
      have hden_not_false' :
          ⟦¬ˢ' (Term.abstract.go body [a, b] Δb0 hΔ_body).uncurry
              (fun i => ⟨(x₀.pair y₀.fst).get [a, b].length i, [α, β][i], hy.2 i⟩)⟧ˢ =
            some ⟨zffalse, SMTType.bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
        rw [hgo]
        rw [hw0, hw1]
        exact denote_not_eq_zffalse_of_some_zftrue hden_body_true rfl rfl
      have hget_eq :
          (⟦¬ˢ' (Term.abstract.go body [a, b] Δb0 hΔ_body).uncurry
              (fun i => ⟨(x₀.pair y₀.fst).get [a, b].length i, [α, β][i], hy.2 i⟩)⟧ˢ.get
            (by
              simpa [SMT.denote] using
                (den_not_body_isSome
                  (w := fun i => ⟨(x₀.pair y₀.fst).get [a, b].length i, [α, β][i], hy.2 i⟩)
                  (by
                    intro i
                    exact ⟨rfl, hy.2 i⟩)))) =
            ⟨zffalse, ⟨SMTType.bool, ZFBool.zffalse_mem_𝔹⟩⟩ := by
        apply Option.get_of_eq_some
        exact hden_not_false'
      exact congrArg (fun D : SMT.Dom => D.fst) hget_eq
    exact hget
  rw [SMT.Term.abstract, dif_pos (by rfl), SMT.PHOAS.Term.exists, SMT.denote]
  have hsInter_mem :
      (⋂₀ ZFSet.sep (fun y => ∃ x ∈ D, y = bodyF x) 𝔹) ∈ 𝔹 :=
    ZFSet.sInter_sep_subset_of_𝔹_mem_𝔹 (fun _ => id)
  have hden_forall :
      ⟦PHOAS.Term.forall (fun x => [α, β][↑x]) fun x_1 =>
          ¬ˢ' (Term.abstract.go body [a, b] Δb0 hΔ_body).uncurry x_1⟧ˢ =
        some ⟨⋂₀ ZFSet.sep (fun y => ∃ x ∈ D, y = bodyF x) 𝔹, SMTType.bool, hsInter_mem⟩ := by
    rw [SMT.denote]
    rw [dif_pos (by simp)]
    rw [dif_pos (by
      intro x_1 hx_1
      simpa [SMT.denote] using den_not_body_isSome (w := x_1) hx_1)]
    apply congrArg some
    apply funDomEqOfTyEqAndFstEq rfl
    ext y
    constructor <;> intro hy
    · simpa [D, bodyF, Fin.foldl_succ_last, Fin.foldl_zero] using hy
    · simpa [D, bodyF, Fin.foldl_succ_last, Fin.foldl_zero] using hy
  have hden_forall' :
      ⟦PHOAS.Term.forall (fun x => [α, β][↑x]) fun x_1 =>
          ¬ˢ' (Term.abstract.go (((@ˢx) (Term.var a) =ˢ Term.var b) ∧ˢ (a!_spec ∧ˢ b!_spec))
            [a, b] Δb0 hΔ_body).uncurry x_1⟧ˢ =
        some ⟨⋂₀ ZFSet.sep (fun y => ∃ x ∈ D, y = bodyF x) 𝔹, SMTType.bool, hsInter_mem⟩ := by
    simpa [body] using hden_forall
  have hExistsTrue :
      overloadUnaryOp id id ZFBool.false ZFBool.not
        (⋂₀ ZFSet.sep (fun y => ∃ x ∈ D, y = bodyF x) 𝔹) = zftrue := by
    have hy₀_mem : y₀.fst ∈ ⟦β⟧ᶻ := by
      simpa [hy₀_ty] using y₀.snd.snd
    simpa [overloadUnaryOp, hsInter_mem, id_eq, proof_irrel_heq] using
      (not_sInter_sep_eq_zftrue_of_exists_eq_zffalse ⟨wx₀.fst.pair y₀.fst, by
        change wx₀.fst.pair y₀.fst ∈ ⟦α⟧ᶻ.prod ⟦β⟧ᶻ
        rw [ZFSet.pair_mem_prod]
        exact ⟨hx₀_mem, hy₀_mem⟩, hbodyF_witness⟩)
  erw [hden_forall']
  simp only [Option.pure_def, Option.failure_eq_none, Option.bind_eq_bind, Option.bind_some,
    Option.some.injEq, PSigma.mk.injEq]
  refine ⟨hExistsTrue, ?_⟩
  congr
  · funext τ
    erw [hExistsTrue]
  · apply proof_irrel_heq

set_option maxHeartbeats 4000000 in
theorem funBBodyTrueOfEqFalseAtRange.{u}
    {α β α' β' : SMTType}
    {x a!_spec b!_spec : Term}
    {a a! b b! x! : 𝒱}
    {Δx : RenamingContext.Context.{u}}
    {X X! wy0 wy1 Dapp : SMT.Dom.{u}}
    {castα castβ : ZFSet}
    {Γa Γb : TypeContext}
    {hφ_eq :
      RenamingContext.CoversFV
        (Function.update (Function.update Δx a! (some wy0)) b! (some wy1))
        (((@ˢTerm.var x!) (Term.var a!)) =ˢ Term.var b!)}
    {hφ_bBody :
      RenamingContext.CoversFV
        (Function.update (Function.update Δx a! (some wy0)) b! (some wy1))
        (funBBodyTerm x! a! b! (funExistsABTerm x a!_spec b!_spec a b α β))}
    (hcastα : ZFSet.IsFunc ⟦α⟧ᶻ ⟦α'⟧ᶻ castα)
    (hcastα_inj : castα.IsInjective)
    (hcastβ : ZFSet.IsFunc ⟦β⟧ᶻ ⟦β'⟧ᶻ castβ)
    (hX_func : ZFSet.IsFunc ⟦α⟧ᶻ ⟦β⟧ᶻ X.fst)
    (fv_a!_spec : fv a!_spec ⊆ fv (Term.var a) ∪ {a!})
    (fv_b!_spec : fv b!_spec ⊆ fv (Term.var b) ∪ {b!})
    (a_not_mem_fv_x : a ∉ fv x)
    (b_not_mem_fv_x : b ∉ fv x)
    (a!_not_mem_fv_x : a! ∉ fv x)
    (b!_not_mem_fv_x : b! ∉ fv x)
    (b_ne_a : b ≠ a)
    (a!_ne_b : a! ≠ b)
    (a_ne_b! : a ≠ b!)
    (b_ne_b! : b ≠ b!)
    (a_ne_a! : a ≠ a!)
    (a!_ne_b! : a! ≠ b!)
    (hφ_exists_ab :
      RenamingContext.CoversFV
        (Function.update (Function.update Δx a! (some wy0)) b! (some wy1))
        (funExistsABTerm x a!_spec b!_spec a b α β))
    (hφa_at :
      ∀ x₀ : SMT.Dom.{u},
        RenamingContext.CoversFV
          (Function.update (Function.update Δx a (some x₀)) a! (some wy0))
          a!_spec)
    (hφb_at :
      ∀ y₀ : SMT.Dom.{u},
        RenamingContext.CoversFV
          (Function.update (Function.update (Function.update Δx a! (some wy0)) b (some y₀)) b! (some wy1))
          b!_spec)
    (a_spec_total_at :
      ∀ x₀ : SMT.Dom.{u},
        x₀.snd.fst = α →
          ⟦a!_spec.abstract
              (Function.update (Function.update Δx a (some x₀)) a! (some wy0))
              (hφa_at x₀)⟧ˢ.isSome =
            true)
    (b_spec_total_at :
      ∀ y₀ : SMT.Dom.{u},
        y₀.snd.fst = β →
          ⟦b!_spec.abstract
              (Function.update (Function.update (Function.update Δx a! (some wy0)) b (some y₀)) b! (some wy1))
              (hφb_at y₀)⟧ˢ.isSome =
            true)
    (den_xa_at :
      ∀ x₀ : SMT.Dom.{u},
        (hx₀_ty : x₀.snd.fst = α) →
          (hx₀_mem : x₀.fst ∈ ⟦α⟧ᶻ) →
            ∃ hcov_xa : RenamingContext.CoversFV (Function.update Δx a (some x₀)) ((@ˢx) (Term.var a)),
              ∃ Dxa : SMT.Dom.{u},
                Dxa.snd.fst = β ∧
                  Dxa.fst =
                    @ᶻX.fst
                      ⟨x₀.fst, by
                        simpa [ZFSet.is_func_dom_eq hX_func] using hx₀_mem⟩ ∧
                    ⟦((@ˢx) (Term.var a)).abstract (Function.update Δx a (some x₀)) hcov_xa⟧ˢ =
                      some Dxa)
    (a_spec_true_implies_cast :
      ∀ x₀ : SMT.Dom.{u},
        x₀.snd.fst = α →
          ∀ (hφa :
            RenamingContext.CoversFV
              (Function.update (Function.update Δx a (some x₀)) a! (some wy0))
              a!_spec)
          {Φa : SMT.Dom.{u}},
          ⟦a!_spec.abstract
              (Function.update (Function.update Δx a (some x₀)) a! (some wy0))
              hφa⟧ˢ =
            some Φa →
            Φa.fst = zftrue →
              x₀.fst.pair wy0.fst ∈ castα)
    (b_spec_true_implies_cast :
      ∀ y₀ : SMT.Dom.{u},
        y₀.snd.fst = β →
          ∀ (hφb :
            RenamingContext.CoversFV
              (Function.update (Function.update (Function.update Δx a! (some wy0)) b (some y₀)) b! (some wy1))
              b!_spec)
          {Φb : SMT.Dom.{u}},
          ⟦b!_spec.abstract
              (Function.update (Function.update (Function.update Δx a! (some wy0)) b (some y₀)) b! (some wy1))
              hφb⟧ˢ =
            some Φb →
            Φb.fst = zftrue →
              y₀.fst.pair wy1.fst ∈ castβ)
    (typ_a_ctx : Γa ⊢ˢ a!_spec : SMTType.bool)
    (typ_b_ctx : Γb ⊢ˢ b!_spec : SMTType.bool)
    (hwy0_ty : wy0.snd.fst = α')
    (hwy1_ty : wy1.snd.fst = β')
    (x₀r : ZFSet)
    (hx₀r_mem : x₀r ∈ ⟦α⟧ᶻ)
    (hcast_x₀r_wy0 : @ᶻcastα ⟨x₀r, by simpa [ZFSet.is_func_dom_eq hcastα] using hx₀r_mem⟩ = wy0.fst)
    (hDapp_from_range :
      Dapp.fst =
        @ᶻcastβ
          ⟨↑(@ᶻX.fst
              ⟨x₀r, by
                simpa [ZFSet.is_func_dom_eq hX_func] using hx₀r_mem⟩),
            by
              simpa [ZFSet.is_func_dom_eq hcastβ] using
                (Subtype.property
                  (@ᶻX.fst
                    ⟨x₀r, by
                      simpa [ZFSet.is_func_dom_eq hX_func] using hx₀r_mem⟩))⟩)
    (hEq : wy1.fst ≠ Dapp.fst)
    (hden_eq_false :
      ⟦(((@ˢTerm.var x!) (Term.var a!)) =ˢ Term.var b!).abstract
          (Function.update (Function.update Δx a! (some wy0)) b! (some wy1))
          hφ_eq⟧ˢ =
        some ⟨zffalse, SMTType.bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩) :
    ⟦(funBBodyTerm x! a! b! (funExistsABTerm x a!_spec b!_spec a b α β)).abstract
        (Function.update (Function.update Δx a! (some wy0)) b! (some wy1))
        hφ_bBody⟧ˢ =
      some ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
  let exists_ab : Term := funExistsABTerm x a!_spec b!_spec a b α β
  let bBody : Term := funBBodyTerm x! a! b! exists_ab
  let Δb0 : RenamingContext.Context :=
    Function.update (Function.update Δx a! (some wy0)) b! (some wy1)
  have hden_exists_ab_false :
      ⟦exists_ab.abstract Δb0 hφ_exists_ab⟧ˢ =
        some ⟨zffalse, SMTType.bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
    let body : Term :=
      (((@ˢx) (Term.var a)) =ˢ Term.var b) ∧ˢ (a!_spec ∧ˢ b!_spec)
    have hΔ_body :
        ∀ v ∈ fv body, v ∉ [a, b] → (Δb0 v).isSome = true := by
      intro v hv hv_not_ab
      exact hφ_exists_ab v (SMT.fv.mem_exists ⟨by simpa [body, exists_ab, funExistsABTerm] using hv, hv_not_ab⟩)
    have hcov_body_upd :
        ∀ W₁ W₂ : SMT.Dom,
          RenamingContext.CoversFV
            (Function.update (Function.update Δb0 a (some W₁)) b (some W₂))
            body := by
      intro W₁ W₂ v hv
      have hv_main :
          v ∈ fv x ∨ v = a ∨ v = b ∨ v = a! ∨ v = b! := by
        have hv' :
            v ∈ SMT.fv (((@ˢx) (Term.var a)) =ˢ Term.var b) ∨
              v ∈ SMT.fv (a!_spec ∧ˢ b!_spec) := by
          simpa [body, fv, or_assoc] using hv
        rcases hv' with hvEq | hvSpecs
        · have hvEq' :
              v ∈ SMT.fv ((@ˢx) (Term.var a)) ∨
                v ∈ SMT.fv (Term.var b) := by
            simpa [fv, or_assoc] using hvEq
          rcases hvEq' with hvApp | hvb
          · have hvApp' :
                v ∈ SMT.fv x ∨ v ∈ SMT.fv (Term.var a) := by
              simpa [fv] using hvApp
            rcases hvApp' with hvx | hva
            · exact Or.inl hvx
            · exact Or.inr <| Or.inl <| by
                rwa [fv, List.mem_singleton] at hva
          · exact Or.inr <| Or.inr <| Or.inl <| by
              rwa [fv, List.mem_singleton] at hvb
        · have hvSpecs' :
              v ∈ SMT.fv a!_spec ∨ v ∈ SMT.fv b!_spec := by
            simpa [fv] using hvSpecs
          rcases hvSpecs' with hvaSpec | hvbSpec
          · have hvA' := fv_a!_spec hvaSpec
            rw [List.mem_union_iff] at hvA'
            rcases hvA' with hva | hva!
            · exact Or.inr <| Or.inl <| by
                rwa [fv, List.mem_singleton] at hva
            · exact Or.inr <| Or.inr <| Or.inr <| Or.inl <| by
                simpa [Singleton.singleton] using hva!
          · have hvB' := fv_b!_spec hvbSpec
            rw [List.mem_union_iff] at hvB'
            rcases hvB' with hvb | hvb!
            · exact Or.inr <| Or.inr <| Or.inl <| by
                rwa [fv, List.mem_singleton] at hvb
            · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| by
                simpa [Singleton.singleton] using hvb!
      rcases hv_main with hvx | rfl | rfl | rfl | rfl
      · rw [Function.update_of_ne (by
            intro h
            subst h
            exact b_not_mem_fv_x hvx)]
        rw [Function.update_of_ne (by
            intro h
            subst h
            exact a_not_mem_fv_x hvx)]
        exact hΔ_body v
          (by simpa [body, fv] using hv)
          (by
            rw [List.mem_cons, List.mem_singleton, not_or]
            exact ⟨by
              intro h
              subst h
              exact a_not_mem_fv_x hvx,
              by
              intro h
              subst h
              exact b_not_mem_fv_x hvx⟩)
      · rw [Function.update_of_ne b_ne_a.symm]
        rw [Function.update_self]
        rfl
      · rw [Function.update_self]
        rfl
      · rw [Function.update_of_ne a!_ne_b]
        rw [Function.update_of_ne a_ne_a!.symm]
        dsimp [Δb0]
        rw [Function.update_of_ne a!_ne_b!]
        rw [Function.update_self]
        rfl
      · rw [Function.update_of_ne b_ne_b!.symm]
        rw [Function.update_of_ne a_ne_b!.symm]
        dsimp [Δb0]
        rw [Function.update_self]
        rfl
    have den_body_some :
        ∀ {w : Fin [a, b].length → SMT.Dom},
          (∀ i, (w i).snd.fst = [α, β][i] ∧ (w i).fst ∈ ⟦[α, β][i]⟧ᶻ) →
            ∃ Dbody : SMT.Dom,
              ⟦(Term.abstract.go body [a, b] Δb0 hΔ_body).uncurry w⟧ˢ = some Dbody ∧
                Dbody.snd.fst = SMTType.bool := by
      intro w hw
      have hgo :=
        funAbstractGoPair
          (Δctx := Δb0) (P := body) (v₁ := a) (v₂ := b)
          (τ₁ := α) (τ₂ := β)
          hΔ_body hcov_body_upd w hw
      rw [hgo]
      let Δw : RenamingContext.Context :=
        Function.update
          (Function.update Δb0 a (some (w ⟨0, by simp⟩)))
          b (some (w ⟨1, by simp⟩))
      have hφa_w :
          RenamingContext.CoversFV Δw a!_spec := by
        intro v hv
        have hv' := fv_a!_spec hv
        rw [List.mem_union_iff] at hv'
        rcases hv' with hva | hva!
        · rw [fv, List.mem_singleton] at hva
          subst hva
          dsimp [Δw, Δb0]
          rw [Function.update_of_ne b_ne_a.symm, Function.update_self]
          rfl
        · have hv_eq : v = a! := by
            change v ∈ ([a!] : List 𝒱) at hva!
            rw [List.mem_singleton] at hva!
            exact hva!
          subst hv_eq
          dsimp [Δw, Δb0]
          rw [Function.update_of_ne a!_ne_b, Function.update_of_ne a_ne_a!.symm,
            Function.update_of_ne a!_ne_b!, Function.update_self]
          rfl
      have hφb_w :
          RenamingContext.CoversFV Δw b!_spec := by
        intro v hv
        have hv' := fv_b!_spec hv
        rw [List.mem_union_iff] at hv'
        rcases hv' with hvb | hvb!
        · rw [fv, List.mem_singleton] at hvb
          subst hvb
          dsimp [Δw]
          rw [Function.update_self]
          rfl
        · have hv_eq : v = b! := by
            change v ∈ ([b!] : List 𝒱) at hvb!
            rw [List.mem_singleton] at hvb!
            exact hvb!
          subst hv_eq
          dsimp [Δw, Δb0]
          rw [Function.update_of_ne b_ne_b!.symm, Function.update_of_ne a_ne_b!.symm,
            Function.update_self]
          rfl
      have hsome_a :
          ⟦a!_spec.abstract Δw hφa_w⟧ˢ.isSome = true := by
        let Δa : RenamingContext.Context :=
          Function.update (Function.update Δx a (some (w ⟨0, by simp⟩))) a! (some wy0)
        have hden_eq :
            ⟦a!_spec.abstract Δw hφa_w⟧ˢ =
              ⟦a!_spec.abstract Δa (hφa_at (w ⟨0, by simp⟩))⟧ˢ := by
          apply SMT.RenamingContext.denote_congr_of_agreesOnFV (h1 := hφa_w) (h2 := hφa_at (w ⟨0, by simp⟩))
          intro v hv
          have hv' := fv_a!_spec hv
          rw [List.mem_union_iff] at hv'
          rcases hv' with hva | hva!
          · rw [fv, List.mem_singleton] at hva
            subst hva
            dsimp [Δw, Δa, Δb0]
            rw [Function.update_of_ne b_ne_a.symm, Function.update_self]
            rw [Function.update_of_ne a_ne_a!, Function.update_self]
          · have hv_eq : v = a! := by
              change v ∈ ([a!] : List 𝒱) at hva!
              rw [List.mem_singleton] at hva!
              exact hva!
            cases hv_eq
            dsimp [Δw, Δa, Δb0]
            rw [Function.update_of_ne a!_ne_b, Function.update_of_ne a_ne_a!.symm,
              Function.update_of_ne a!_ne_b!, Function.update_self]
            rw [Function.update_self]
        rw [hden_eq]
        exact a_spec_total_at (w ⟨0, Nat.zero_lt_succ 1⟩) (hw ⟨0, Nat.zero_lt_succ 1⟩).1
      have hsome_b :
          ⟦b!_spec.abstract Δw hφb_w⟧ˢ.isSome = true := by
        let Δb : RenamingContext.Context :=
          Function.update
            (Function.update (Function.update Δx a! (some wy0)) b (some (w ⟨1, by simp⟩)))
            b! (some wy1)
        have hden_eq :
            ⟦b!_spec.abstract Δw hφb_w⟧ˢ =
              ⟦b!_spec.abstract Δb (hφb_at (w ⟨1, by simp⟩))⟧ˢ := by
          apply SMT.RenamingContext.denote_congr_of_agreesOnFV (h1 := hφb_w) (h2 := hφb_at (w ⟨1, by simp⟩))
          intro v hv
          have hv' := fv_b!_spec hv
          rw [List.mem_union_iff] at hv'
          rcases hv' with hvb | hvb!
          · rw [fv, List.mem_singleton] at hvb
            subst hvb
            dsimp [Δw, Δb]
            rw [Function.update_self]
            rw [Function.update_of_ne b_ne_b!, Function.update_self]
          · have hv_eq : v = b! := by
              change v ∈ ([b!] : List 𝒱) at hvb!
              rw [List.mem_singleton] at hvb!
              exact hvb!
            cases hv_eq
            dsimp [Δw, Δb, Δb0]
            rw [Function.update_of_ne b_ne_b!.symm, Function.update_of_ne a_ne_b!.symm,
              Function.update_self]
            rw [Function.update_self]
        rw [hden_eq]
        exact b_spec_total_at (w ⟨1, Nat.one_lt_succ_succ 0⟩) (hw ⟨1, Nat.one_lt_succ_succ 0⟩).1
      obtain ⟨Da, hden_a⟩ := Option.isSome_iff_exists.mp hsome_a
      obtain ⟨Db, hden_b⟩ := Option.isSome_iff_exists.mp hsome_b
      have hDa_ty : Da.snd.fst = SMTType.bool := by
        exact denote_type_eq_of_typing (typ_t := typ_a_ctx) (hden := hden_a)
      have hDb_ty : Db.snd.fst = SMTType.bool := by
        exact denote_type_eq_of_typing (typ_t := typ_b_ctx) (hden := hden_b)
      have hcov_app_w :
          RenamingContext.CoversFV Δw ((@ˢx) (Term.var a)) := by
        have hcov_body_w := hcov_body_upd (w ⟨0, by simp⟩) (w ⟨1, by simp⟩)
        intro v hv
        apply hcov_body_w v
        have hvEq :
            v ∈ SMT.fv (((@ˢx) (Term.var a)) =ˢ Term.var b) := by
          simpa [fv, or_assoc] using (Or.inl hv :
            v ∈ SMT.fv ((@ˢx) (Term.var a)) ∨ v ∈ SMT.fv (Term.var b))
        exact (by
          simpa [body, fv, or_assoc] using (Or.inl hvEq :
            v ∈ SMT.fv (((@ˢx) (Term.var a)) =ˢ Term.var b) ∨
              v ∈ SMT.fv (a!_spec ∧ˢ b!_spec)))
      obtain ⟨hcov_xa0, Dxa, hDxa_ty, _hDxa_val, hden_app_raw⟩ :=
        den_xa_at (w ⟨0, by simp⟩) (hw ⟨0, by simp⟩).1
          (by simpa using (hw ⟨0, by simp⟩).2)
      have hden_app :
          ⟦((@ˢx) (Term.var a)).abstract Δw hcov_app_w⟧ˢ = some Dxa := by
        have hden_eq :
            ⟦((@ˢx) (Term.var a)).abstract Δw hcov_app_w⟧ˢ =
              ⟦((@ˢx) (Term.var a)).abstract
                  (Function.update Δx a (some (w ⟨0, by simp⟩)))
                  hcov_xa0⟧ˢ := by
          apply SMT.RenamingContext.denote_congr_of_agreesOnFV (h1 := hcov_app_w) (h2 := hcov_xa0)
          intro v hv
          have hv' :
              v ∈ SMT.fv x ∨ v ∈ SMT.fv (Term.var a) := by
            simpa [fv] using hv
          rcases hv' with hvx | hva
          · have hne_b : v ≠ b := by
              intro h
              subst h
              exact b_not_mem_fv_x hvx
            have hne_a : v ≠ a := by
              intro h
              subst h
              exact a_not_mem_fv_x hvx
            have hne_b! : v ≠ b! := by
              intro h
              subst h
              exact b!_not_mem_fv_x hvx
            have hne_a! : v ≠ a! := by
              intro h
              subst h
              exact a!_not_mem_fv_x hvx
            dsimp [Δw, Δb0]
            rw [Function.update_of_ne hne_b, Function.update_of_ne hne_a,
              Function.update_of_ne hne_b!, Function.update_of_ne hne_a!,
              Function.update_of_ne hne_a]
          · rw [fv, List.mem_singleton] at hva
            subst hva
            dsimp [Δw]
            rw [Function.update_of_ne b_ne_a.symm, Function.update_self, Function.update_self]
        rw [hden_eq]
        exact hden_app_raw
      have hden_var_b :
          ⟦(Term.var b).abstract Δw
              (by
                intro v hv
                rw [fv, List.mem_singleton] at hv
                subst hv
                dsimp [Δw]
                rw [Function.update_self]
                rfl)⟧ˢ =
            some (w ⟨1, by simp⟩) := by
        rw [SMT.Term.abstract.eq_def, SMT.denote, Option.pure_def, Option.some.injEq]
        apply Option.get_of_eq_some
        dsimp [Δw]
        rw [Function.update_self]
      have hcov_eq_w :
          RenamingContext.CoversFV Δw (((@ˢx) (Term.var a)) =ˢ Term.var b) := by
        have hcov_body_w := hcov_body_upd (w ⟨0, by simp⟩) (w ⟨1, by simp⟩)
        intro v hv
        apply hcov_body_w v
        exact (by
          simpa [body, fv, or_assoc] using (Or.inl hv :
            v ∈ SMT.fv (((@ˢx) (Term.var a)) =ˢ Term.var b) ∨
              v ∈ SMT.fv (a!_spec ∧ˢ b!_spec)))
      obtain ⟨Deq, hden_eq_raw, hDeq_ty⟩ :=
        denote_eq_some_of_some (by simpa [proof_irrel_heq] using hden_app) hden_var_b
          (hDxa_ty.trans (hw ⟨1, by simp⟩).1.symm)
      have hden_eq :
          ⟦(((@ˢx) (Term.var a)) =ˢ Term.var b).abstract Δw hcov_eq_w⟧ˢ = some Deq := by
        simpa [SMT.Term.abstract, proof_irrel_heq] using hden_eq_raw
      have hcov_specs_w :
          RenamingContext.CoversFV Δw (a!_spec ∧ˢ b!_spec) := by
        intro v hv
        have hv' :
            v ∈ SMT.fv a!_spec ∨ v ∈ SMT.fv b!_spec := by
          simpa [fv] using hv
        rcases hv' with hva | hvb
        · exact hφa_w v hva
        · exact hφb_w v hvb
      obtain ⟨Dspecs, hden_specs_raw, hDspecs_ty⟩ :=
        denote_and_some_bool_of_some_bool hden_a hDa_ty hden_b hDb_ty
      have hden_specs :
          ⟦(a!_spec ∧ˢ b!_spec).abstract Δw hcov_specs_w⟧ˢ = some Dspecs := by
        simpa [SMT.Term.abstract, proof_irrel_heq] using hden_specs_raw
      obtain ⟨Dbody, hden_body_raw, hDbody_ty⟩ :=
        denote_and_some_bool_of_some_bool hden_eq hDeq_ty hden_specs hDspecs_ty
      have hden_body :
          ⟦body.abstract Δw (hcov_body_upd (w ⟨0, by simp⟩) (w ⟨1, by simp⟩))⟧ˢ = some Dbody := by
        simpa [body, SMT.Term.abstract, proof_irrel_heq] using hden_body_raw
      exact ⟨Dbody, hden_body, hDbody_ty⟩
    have den_not_body_isSome :
        ∀ {w : Fin [a, b].length → SMT.Dom},
          (∀ i, (w i).snd.fst = [α, β][i] ∧ (w i).fst ∈ ⟦[α, β][i]⟧ᶻ) →
            ⟦¬ˢ' (Term.abstract.go body [a, b] Δb0 hΔ_body).uncurry w⟧ˢ.isSome = true := by
      intro w hw
      obtain ⟨Dbody, hden_body, hDbody_ty⟩ := den_body_some hw
      exact denote_not_isSome_of_some_bool hden_body hDbody_ty
    have den_body_isSome :
        ∀ {w : Fin [a, b].length → SMT.Dom},
          (∀ i, (w i).snd.fst = [α, β][i] ∧ (w i).fst ∈ ⟦[α, β][i]⟧ᶻ) →
            ⟦(Term.abstract.go body [a, b] Δb0 hΔ_body).uncurry w⟧ˢ.isSome = true := by
      intro w hw
      obtain ⟨Dbody, hden_body, _⟩ := den_body_some hw
      exact Option.isSome_of_eq_some hden_body
    let bodyF : ZFSet → ZFSet := fun y =>
      if hy : y.hasArity [a, b].length ∧
          ∀ i : Fin [a, b].length,
            y.get [a, b].length i ∈ ⟦[α, β][i]⟧ᶻ then
        (⟦¬ˢ'
            (Term.abstract.go body [a, b] Δb0 hΔ_body).uncurry
              (fun i => ⟨y.get [a, b].length i, [α, β][i], hy.2 i⟩)⟧ˢ.get
          (den_not_body_isSome (by intro i; exact ⟨rfl, hy.2 i⟩))).fst
      else
        zffalse
    let D : ZFSet := ⟦α⟧ᶻ.prod ⟦β⟧ᶻ
    dsimp [exists_ab, funExistsABTerm]
    rw [SMT.Term.abstract, dite_cond_eq_true (eq_true (by rfl)),
      SMT.PHOAS.Term.exists, SMT.denote]
    have hsInter_mem :
        (⋂₀ ZFSet.sep (fun y => ∃ x ∈ D, y = bodyF x) 𝔹) ∈ 𝔹 :=
      ZFSet.sInter_sep_subset_of_𝔹_mem_𝔹 (fun _ => id)
    have hden_forall :
        ⟦PHOAS.Term.forall (fun x => [α, β][↑x]) fun x_1 =>
            ¬ˢ' (Term.abstract.go body [a, b] Δb0 hΔ_body).uncurry x_1⟧ˢ =
          some ⟨⋂₀ ZFSet.sep (fun y => ∃ x ∈ D, y = bodyF x) 𝔹, SMTType.bool, hsInter_mem⟩ := by
      rw [SMT.denote]
      rw [dif_pos (by simp)]
      rw [dif_pos (by
        intro x_1 hx_1
        simpa [SMT.denote] using den_not_body_isSome (w := x_1) hx_1)]
      apply congrArg some
      apply funDomEqOfTyEqAndFstEq rfl
      ext y
      constructor <;> intro hy
      · simpa [D, bodyF, Fin.foldl_succ_last, Fin.foldl_zero] using hy
      · simpa [D, bodyF, Fin.foldl_succ_last, Fin.foldl_zero] using hy
    have hExistsFalse :
        overloadUnaryOp id id ZFBool.false ZFBool.not
          (⋂₀ ZFSet.sep (fun y => ∃ x ∈ D, y = bodyF x) 𝔹) = zffalse := by
      as_aux_lemma =>
      have hne : ∃ z, z ∈ D := by
        refine ⟨α.defaultZFSet.pair β.defaultZFSet, ?_⟩
        change α.defaultZFSet.pair β.defaultZFSet ∈ ⟦α⟧ᶻ.prod ⟦β⟧ᶻ
        rw [ZFSet.pair_mem_prod]
        exact ⟨SMTType.mem_toZFSet_of_defaultZFSet (α := α),
          SMTType.mem_toZFSet_of_defaultZFSet (α := β)⟩
      have hall : ∀ z ∈ D, bodyF z = zftrue := by
        intro z hz
        obtain ⟨x₁, hx₁, y₁, hy₁, rfl⟩ := ZFSet.mem_prod.mp hz
        let wx₁ : SMT.Dom := ⟨x₁, α, hx₁⟩
        let yy₁ : SMT.Dom := ⟨y₁, β, hy₁⟩
        have hy_pair :
            (x₁.pair y₁).hasArity [a, b].length ∧
              ∀ i : Fin [a, b].length,
                (x₁.pair y₁).get [a, b].length i ∈ ⟦[α, β][i]⟧ᶻ := by
          constructor
          · simp [ZFSet.hasArity]
          · intro i
            have hi_lt : i.1 < 2 := by
              simpa using i.2
            have hi : i.1 = 0 ∨ i.1 = 1 := by
              omega
            rcases hi with hi | hi
            · have hi' : i = ⟨0, by simp⟩ := by
                apply Fin.ext
                exact hi
              rw [hi']
              simp [hx₁, hy₁]
            · have hi' : i = ⟨1, by simp⟩ := by
                apply Fin.ext
                exact hi
              rw [hi']
              simp [hx₁, hy₁]
        change
          (if hy' :
              (x₁.pair y₁).hasArity [a, b].length ∧
                ∀ i : Fin [a, b].length,
                  (x₁.pair y₁).get [a, b].length i ∈ ⟦[α, β][i]⟧ᶻ
            then
              (⟦¬ˢ' (Term.abstract.go body [a, b] Δb0 hΔ_body).uncurry
                  (fun i =>
                    (⟨(x₁.pair y₁).get [a, b].length i, [α, β][i], hy'.2 i⟩ : SMT.Dom))⟧ˢ.get
                (by
                  simpa [SMT.denote] using
                    (den_not_body_isSome
                      (w := fun i =>
                        (⟨(x₁.pair y₁).get [a, b].length i, [α, β][i], hy'.2 i⟩ : SMT.Dom))
                      (by
                        intro i
                        exact ⟨rfl, hy'.2 i⟩)))).fst
            else zffalse) = zftrue
        rw [dif_pos hy_pair]
        let Δgoal : RenamingContext.Context :=
          Function.update (Function.update Δb0 a (some wx₁)) b (some yy₁)
        have hφa_goal :
            RenamingContext.CoversFV Δgoal a!_spec := by
          intro v hv
          have hv' := fv_a!_spec hv
          rw [List.mem_union_iff] at hv'
          rcases hv' with hva | hva!
          · rw [fv, List.mem_singleton] at hva
            subst hva
            dsimp [Δgoal]
            rw [Function.update_of_ne b_ne_a.symm]
            rw [Function.update_self]
            rfl
          · have hv_eq : v = a! := by
              simpa [Singleton.singleton] using hva!
            subst hv_eq
            dsimp [Δgoal, Δb0]
            rw [Function.update_of_ne a!_ne_b, Function.update_of_ne a_ne_a!.symm,
              Function.update_of_ne a!_ne_b!, Function.update_self]
            rfl
        have hφb_goal :
            RenamingContext.CoversFV Δgoal b!_spec := by
          intro v hv
          have hv' := fv_b!_spec hv
          rw [List.mem_union_iff] at hv'
          rcases hv' with hvb | hvb!
          · rw [fv, List.mem_singleton] at hvb
            subst hvb
            dsimp [Δgoal]
            rw [Function.update_self]
            rfl
          · have hv_eq : v = b! := by
              simpa [Singleton.singleton] using hvb!
            subst hv_eq
            dsimp [Δgoal, Δb0]
            rw [Function.update_of_ne b_ne_b!.symm, Function.update_of_ne a_ne_b!.symm,
              Function.update_self]
            rfl
        let Δa : RenamingContext.Context :=
          Function.update (Function.update Δx a (some wx₁)) a! (some wy0)
        have hden_a_goal_eq :
            ⟦a!_spec.abstract Δgoal hφa_goal⟧ˢ =
              ⟦a!_spec.abstract Δa (hφa_at wx₁)⟧ˢ := by
          apply SMT.RenamingContext.denote_congr_of_agreesOnFV
            (h1 := hφa_goal) (h2 := hφa_at wx₁)
          intro v hv
          have hv' := fv_a!_spec hv
          rw [List.mem_union_iff] at hv'
          rcases hv' with hva | hva!
          · rw [fv, List.mem_singleton] at hva
            subst hva
            dsimp [Δgoal, Δa, Δb0]
            rw [Function.update_of_ne b_ne_a.symm, Function.update_self]
            rw [Function.update_of_ne a_ne_a!, Function.update_self]
          · have hv_eq : v = a! := by
              simpa [Singleton.singleton] using hva!
            cases hv_eq
            dsimp [Δgoal, Δa, Δb0]
            rw [Function.update_of_ne a!_ne_b, Function.update_of_ne a_ne_a!.symm,
              Function.update_of_ne a!_ne_b!, Function.update_self]
            rw [Function.update_self]
        let Δb : RenamingContext.Context :=
          Function.update
            (Function.update (Function.update Δx a! (some wy0)) b (some yy₁))
            b! (some wy1)
        have hden_b_goal_eq :
            ⟦b!_spec.abstract Δgoal hφb_goal⟧ˢ =
              ⟦b!_spec.abstract Δb (hφb_at yy₁)⟧ˢ := by
          apply SMT.RenamingContext.denote_congr_of_agreesOnFV
            (h1 := hφb_goal) (h2 := hφb_at yy₁)
          intro v hv
          have hv' := fv_b!_spec hv
          rw [List.mem_union_iff] at hv'
          rcases hv' with hvb | hvb!
          · rw [fv, List.mem_singleton] at hvb
            subst hvb
            dsimp [Δgoal, Δb]
            rw [Function.update_self]
            rw [Function.update_of_ne b_ne_b!, Function.update_self]
          · have hv_eq : v = b! := by
              simpa [Singleton.singleton] using hvb!
            cases hv_eq
            dsimp [Δgoal, Δb, Δb0]
            rw [Function.update_of_ne b_ne_b!.symm, Function.update_of_ne a_ne_b!.symm,
              Function.update_self]
            rw [Function.update_self]
        have hsome_a :
            ⟦a!_spec.abstract Δgoal hφa_goal⟧ˢ.isSome = true := by
          rw [hden_a_goal_eq]
          exact a_spec_total_at wx₁ rfl
        have hsome_b :
            ⟦b!_spec.abstract Δgoal hφb_goal⟧ˢ.isSome = true := by
          rw [hden_b_goal_eq]
          exact b_spec_total_at yy₁ rfl
        obtain ⟨Da, hden_a⟩ := Option.isSome_iff_exists.mp hsome_a
        obtain ⟨Db, hden_b⟩ := Option.isSome_iff_exists.mp hsome_b
        have hDa_ty : Da.snd.fst = SMTType.bool := by
          exact denote_type_eq_of_typing
            (typ_t := typ_a_ctx) (hden := hden_a)
        have hDb_ty : Db.snd.fst = SMTType.bool := by
          exact denote_type_eq_of_typing
            (typ_t := typ_b_ctx) (hden := hden_b)
        obtain ⟨Dspec, hden_specs, hDspec_ty⟩ :=
          denote_and_some_bool_of_some_bool hden_a hDa_ty hden_b hDb_ty
        obtain ⟨hcov_xa, Dxa, hDxa_ty, hDxa_val, hden_xa⟩ :=
          den_xa_at wx₁ rfl hx₁
        have hden_var_b :
            ⟦(Term.var b).abstract Δgoal
                (by
                  intro v hv
                  rw [fv, List.mem_singleton] at hv
                  subst hv
                  dsimp [Δgoal]
                  rw [Function.update_self]
                  rfl)⟧ˢ = some yy₁ := by
          rw [SMT.Term.abstract.eq_def, SMT.denote, Option.pure_def, Option.some.injEq]
          apply Option.get_of_eq_some
          exact Function.update_self _ _ _
        have hcov_eq_goal :
            RenamingContext.CoversFV Δgoal ((@ˢx) (Term.var a) =ˢ Term.var b) := by
          have hcov_body_goal := hcov_body_upd wx₁ yy₁
          intro v hv
          apply hcov_body_goal v
          exact (by
            simpa [body, fv, or_assoc] using (Or.inl hv :
              v ∈ SMT.fv (((@ˢx) (Term.var a)) =ˢ Term.var b) ∨
                v ∈ SMT.fv (a!_spec ∧ˢ b!_spec)))
        have hcov_app_goal :
            RenamingContext.CoversFV Δgoal ((@ˢx) (Term.var a)) := by
          have hcov_body_goal := hcov_body_upd wx₁ yy₁
          intro v hv
          apply hcov_body_goal v
          have hvEq :
              v ∈ SMT.fv (((@ˢx) (Term.var a)) =ˢ Term.var b) := by
            simpa [fv, or_assoc] using (Or.inl hv :
              v ∈ SMT.fv ((@ˢx) (Term.var a)) ∨ v ∈ SMT.fv (Term.var b))
          exact (by
            simpa [body, fv, or_assoc] using (Or.inl hvEq :
              v ∈ SMT.fv (((@ˢx) (Term.var a)) =ˢ Term.var b) ∨
                v ∈ SMT.fv (a!_spec ∧ˢ b!_spec)))
        have hden_app_goal :
            ⟦((@ˢx) (Term.var a)).abstract Δgoal hcov_app_goal⟧ˢ = some Dxa := by
          have hden_eq :
              ⟦((@ˢx) (Term.var a)).abstract Δgoal hcov_app_goal⟧ˢ =
                ⟦((@ˢx) (Term.var a)).abstract
                    (Function.update Δx a (some wx₁))
                    hcov_xa⟧ˢ := by
            apply SMT.RenamingContext.denote_congr_of_agreesOnFV
              (h1 := hcov_app_goal) (h2 := hcov_xa)
            intro v hv
            have hv' :
                v ∈ SMT.fv x ∨ v ∈ SMT.fv (Term.var a) := by
              simpa [fv] using hv
            rcases hv' with hvx | hva
            · have hne_b : v ≠ b := by
                intro h
                subst h
                exact b_not_mem_fv_x hvx
              have hne_a : v ≠ a := by
                intro h
                subst h
                exact a_not_mem_fv_x hvx
              have hne_b! : v ≠ b! := by
                intro h
                subst h
                exact b!_not_mem_fv_x hvx
              have hne_a! : v ≠ a! := by
                intro h
                subst h
                exact a!_not_mem_fv_x hvx
              dsimp [Δgoal, Δb0]
              erw [Function.update_of_ne hne_b, Function.update_of_ne hne_a,
                Function.update_of_ne hne_b!, Function.update_of_ne hne_a!,
                Function.update_of_ne hne_a]
            · rw [fv, List.mem_singleton] at hva
              subst hva
              dsimp [Δgoal]
              erw [Function.update_of_ne b_ne_a.symm, Function.update_self, Function.update_self]
          rw [hden_eq]
          exact hden_xa
        have hden_body_false :
            ⟦body.abstract Δgoal (hcov_body_upd wx₁ yy₁)⟧ˢ =
              some ⟨zffalse, SMTType.bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
          by_cases hEqxy : Dxa.fst = y₁
          · have hDspec_false : Dspec.fst = zffalse := by
              have hDspec_bool : Dspec.fst ∈ 𝔹 := by
                simpa [hDspec_ty] using Dspec.snd.snd
              rw [ZFSet.ZFBool.mem_𝔹_iff] at hDspec_bool
              rcases hDspec_bool with hDspec_false | hDspec_true
              · exact hDspec_false
              · exfalso
                obtain ⟨Da', Db', hden_a_true, hDa_true, hden_b_true, hDb_true⟩ :=
                  denoteAndTrueComponents
                    (p := a!_spec.abstract Δgoal hφa_goal)
                    (q := b!_spec.abstract Δgoal hφb_goal)
                    (typ_p_bool := by
                      intro D hden
                      exact denote_type_eq_of_typing
                        (typ_t := typ_a_ctx) (hden := hden))
                    (typ_q_bool := by
                      intro D hden
                      exact denote_type_eq_of_typing
                        (typ_t := typ_b_ctx) (hden := hden))
                    hden_specs hDspec_true
                have hden_a_true_at :
                    ⟦a!_spec.abstract
                        (Function.update (Function.update Δx a (some wx₁)) a! (some wy0))
                        (hφa_at wx₁)⟧ˢ = some Da' := by
                  rw [← hden_a_goal_eq]
                  exact hden_a_true
                have hden_b_true_at :
                    ⟦b!_spec.abstract
                        (Function.update
                          (Function.update (Function.update Δx a! (some wy0)) b (some yy₁))
                          b! (some wy1))
                        (hφb_at yy₁)⟧ˢ = some Db' := by
                  rw [← hden_b_goal_eq]
                  exact hden_b_true
                have hcast_x₁_wy0_pair :
                    x₁.pair wy0.fst ∈ castα := by
                  exact a_spec_true_implies_cast wx₁ rfl
                    (hφa_at wx₁) hden_a_true_at hDa_true
                have hcast_y₁_wy1_pair :
                    y₁.pair wy1.fst ∈ castβ := by
                  exact b_spec_true_implies_cast yy₁ rfl
                    (hφb_at yy₁) hden_b_true_at hDb_true
                have hx₁_dom_cast : x₁ ∈ castα.Dom := by
                  simpa [ZFSet.is_func_dom_eq hcastα] using hx₁
                have hy₁_dom_cast : y₁ ∈ castβ.Dom := by
                  simpa [ZFSet.is_func_dom_eq hcastβ] using hy₁
                have hcast_x₁_wy0 :
                    @ᶻcastα ⟨x₁, hx₁_dom_cast⟩ = wy0.fst := by
                  have hpair := ZFSet.fapply.of_pair
                    (ZFSet.is_func_is_pfunc hcastα) hcast_x₁_wy0_pair
                  simpa only [Subtype.ext_iff] using hpair
                have hcast_y₁_wy1 :
                    @ᶻcastβ ⟨y₁, hy₁_dom_cast⟩ = wy1.fst := by
                  have hpair := ZFSet.fapply.of_pair
                    (ZFSet.is_func_is_pfunc hcastβ) hcast_y₁_wy1_pair
                  simpa only [Subtype.ext_iff] using hpair
                have hXx₁_eq_y₁ :
                    @ᶻX.fst
                      ⟨x₁, by
                        simpa [ZFSet.is_func_dom_eq hX_func] using hx₁⟩ = y₁ := by
                  rw [← hDxa_val]
                  exact hEqxy
                have hx₁_eq_x₀r : x₁ = x₀r := by
                  have hcast_x₀r :
                      @ᶻcastα
                        ⟨x₀r, by
                          simpa [ZFSet.is_func_dom_eq hcastα] using hx₀r_mem⟩ = wy0.fst := by
                    simpa [Subtype.ext_iff] using hcast_x₀r_wy0
                  have hcast_eq :
                      @ᶻcastα ⟨x₁, hx₁_dom_cast⟩ =
                        @ᶻcastα
                          ⟨x₀r, by
                            simpa [ZFSet.is_func_dom_eq hcastα] using hx₀r_mem⟩ := by
                    apply Subtype.ext
                    exact hcast_x₁_wy0.trans hcast_x₀r.symm
                  have hinj := IsInjective.apply_inj hcastα hcastα_inj hcast_eq
                  rw [Subtype.ext_iff] at hinj
                  exact hinj
                have hcast_rhs :
                    @ᶻcastβ
                      ⟨↑(@ᶻX.fst
                          ⟨x₀r, by
                            simpa [ZFSet.is_func_dom_eq hX_func] using hx₀r_mem⟩),
                        by
                          subst hx₁_eq_x₀r
                          simpa [hXx₁_eq_y₁, ZFSet.is_func_dom_eq hcastβ] using hy₁⟩ = wy1.fst := by
                  subst hx₁_eq_x₀r
                  simpa [hXx₁_eq_y₁] using hcast_y₁_wy1
                have hDapp_eq_wy1 : Dapp.fst = wy1.fst := by
                  calc
                    Dapp.fst =
                        @ᶻcastβ
                          ⟨↑(@ᶻX.fst
                              ⟨x₀r, by
                                simpa [ZFSet.is_func_dom_eq hX_func] using hx₀r_mem⟩),
                            by
                              simpa [ZFSet.is_func_dom_eq hcastβ] using
                                (Subtype.property
                                  (@ᶻX.fst
                                    ⟨x₀r, by
                                      simpa [ZFSet.is_func_dom_eq hX_func] using hx₀r_mem⟩))⟩ := hDapp_from_range
                    _ = wy1.fst := hcast_rhs
                exact hEq hDapp_eq_wy1.symm
            have hden_eq_true :
                ⟦(((@ˢx) (Term.var a)) =ˢ Term.var b).abstract Δgoal hcov_eq_goal⟧ˢ =
                  some ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
              rw [SMT.Term.abstract.eq_def]
              exact denote_eq_eq_zftrue_of_fst_eq
                hden_app_goal hden_var_b (hDxa_ty.trans rfl) hEqxy
            simpa [body, SMT.Term.abstract, proof_irrel_heq] using
              (denote_and_eq_zffalse_of_some_zffalse_right
                hden_eq_true rfl hden_specs hDspec_ty hDspec_false)
          · have hden_eq_false :
                ⟦(((@ˢx) (Term.var a)) =ˢ Term.var b).abstract Δgoal hcov_eq_goal⟧ˢ =
                  some ⟨zffalse, SMTType.bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
              rw [SMT.Term.abstract.eq_def]
              exact funDenoteEqFalseOfFstNe
                hden_app_goal hden_var_b (hDxa_ty.trans rfl) (by simpa using hEqxy)
            simpa [body, SMT.Term.abstract, proof_irrel_heq] using
              (denote_and_eq_zffalse_of_some_zffalse_left
                hden_eq_false rfl rfl hden_specs hDspec_ty)
        have hw :
            ∀ i : Fin [a, b].length,
              ((fun i => (⟨(x₁.pair y₁).get [a, b].length i, [α, β][i], hy_pair.2 i⟩ : SMT.Dom)) i).snd.fst =
                [α, β][i] ∧
              ((fun i => (⟨(x₁.pair y₁).get [a, b].length i, [α, β][i], hy_pair.2 i⟩ : SMT.Dom)) i).fst ∈
                ⟦[α, β][i]⟧ᶻ := by
          intro i
          exact ⟨rfl, hy_pair.2 i⟩
        have hcov_not_goal :
            RenamingContext.CoversFV Δgoal (¬ˢ body) := by
          intro v hv
          exact hcov_body_upd wx₁ yy₁ v (by simpa [fv] using hv)
        have hden_not_true :
            ⟦¬ˢ' (Term.abstract.go body [a, b] Δb0 hΔ_body).uncurry
                (fun i => ⟨(x₁.pair y₁).get [a, b].length i, [α, β][i], hy_pair.2 i⟩)⟧ˢ =
              some ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
          as_aux_lemma =>
          have hgo :=
            funAbstractGoPair
              (Δctx := Δb0) (P := body) (v₁ := a) (v₂ := b)
              (τ₁ := α) (τ₂ := β)
              hΔ_body hcov_body_upd
              (fun i => ⟨(x₁.pair y₁).get [a, b].length i, [α, β][i], hy_pair.2 i⟩) hw
          have hw0 :
              (fun i => ⟨(x₁.pair y₁).get [a, b].length i, [α, β][i], hy_pair.2 i⟩) ⟨0, by simp⟩ = wx₁ := by
            change (⟨(x₁.pair y₁).get [a, b].length ⟨0, by simp⟩, α, hy_pair.2 ⟨0, by simp⟩⟩ : SMT.Dom) =
              (⟨x₁, α, hx₁⟩ : SMT.Dom)
            apply PSigma.ext
            · simp [ZFSet.get]
            · simp only [List.length_cons, List.length_nil, Nat.reduceAdd, ZFSet.get,
                Fin.reduceLast, Fin.isValue, dite_eq_ite, Fin.getElem_fin, Fin.zero_eta,
                Fin.zero_eq_one_iff, Nat.succ_ne_self, ↓dreduceIte, Fin.coe_ofNat_eq_mod,
                Nat.zero_mod, List.getElem_cons_zero, ↓dreduceDIte, Fin.castPred_zero]
              congr
              · funext τ
                simp only [π₁_pair, eq_iff_iff]
              · apply proof_irrel_heq
          have hw1 :
              (fun i => ⟨(x₁.pair y₁).get [a, b].length i, [α, β][i], hy_pair.2 i⟩) ⟨1, by simp⟩ = yy₁ := by
            change (⟨(x₁.pair y₁).get [a, b].length ⟨1, by simp⟩, β, hy_pair.2 ⟨1, by simp⟩⟩ : SMT.Dom) =
              (⟨y₁, β, hy₁⟩ : SMT.Dom)
            apply PSigma.ext
            · simp [ZFSet.get]
            · simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_one_sub_one,
                ZFSet.get, Fin.reduceLast, Fin.isValue, dite_eq_ite, Fin.getElem_fin,
                Fin.zero_eta, Fin.zero_eq_one_iff, Nat.succ_ne_self, ↓dreduceIte,
                Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.getElem_cons_zero,
                List.getElem_cons_succ, ↓dreduceDIte, Fin.castPred_zero]
              congr
              · funext τ
                simpa [if_pos rfl, π₂_pair]
              · apply proof_irrel_heq
          rw [hgo]
          rw [hw0, hw1]
          simpa [SMT.Term.abstract, proof_irrel_heq] using
            (funNotAbstractEqZftrueOfSomeZffalse
              (Δctx := Δgoal) (t := body)
              (D := ⟨zffalse, SMTType.bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩)
              (hcov_t := hcov_body_upd wx₁ yy₁)
              hden_body_false rfl rfl hcov_not_goal)
        have hget :
            (⟦¬ˢ' (Term.abstract.go body [a, b] Δb0 hΔ_body).uncurry
                (fun i => ⟨(x₁.pair y₁).get [a, b].length i, [α, β][i], hy_pair.2 i⟩)⟧ˢ.get
              (den_not_body_isSome hw)).fst = zftrue := by
          as_aux_lemma =>
          have hget_eq :
              (⟦¬ˢ' (Term.abstract.go body [a, b] Δb0 hΔ_body).uncurry
                  (fun i => ⟨(x₁.pair y₁).get [a, b].length i, [α, β][i], hy_pair.2 i⟩)⟧ˢ.get
                (den_not_body_isSome hw)) =
                ⟨zftrue, ⟨SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩⟩ := by
            apply Option.get_of_eq_some
            simpa [Function.OfArity.uncurry, Function.FromTypes.uncurry,
              proof_irrel_heq] using hden_not_true
          exact congrArg (fun D : SMT.Dom => D.fst) hget_eq
        exact hget
      simpa [overloadUnaryOp, hsInter_mem, id_eq, proof_irrel_heq] using
        (not_sInter_sep_eq_zffalse_of_forall_eq_zftrue (D := D) (F := bodyF) hne hall)
      /-
          change α.defaultZFSet.pair β.defaultZFSet ∈ ⟦α⟧ᶻ.prod ⟦β⟧ᶻ
          rw [ZFSet.pair_mem_prod]
          exact ⟨SMTType.mem_toZFSet_of_defaultZFSet (α := α),
            SMTType.mem_toZFSet_of_defaultZFSet (α := β)⟩⟩
        (by
          intro z hz
          obtain ⟨x₁, hx₁, y₁, hy₁, rfl⟩ := ZFSet.mem_prod.mp hz
          let wx₁ : SMT.Dom := ⟨x₁, α, hx₁⟩
          let yy₁ : SMT.Dom := ⟨y₁, β, hy₁⟩
          have hy_pair :
              (x₁.pair y₁).hasArity [a, b].length ∧
                ∀ i : Fin [a, b].length,
                  (x₁.pair y₁).get [a, b].length i ∈ ⟦[α, β][i]⟧ᶻ := by
            constructor
            · simp [ZFSet.hasArity]
            · intro i
              have hi_lt : i.1 < 2 := by
                simpa using i.2
              have hi : i.1 = 0 ∨ i.1 = 1 := by
                omega
              rcases hi with hi | hi
              · have hi' : i = ⟨0, by simp⟩ := by
                  apply Fin.ext
                  exact hi
                rw [hi']
                simp [hx₁, hy₁]
              · have hi' : i = ⟨1, by simp⟩ := by
                  apply Fin.ext
                  exact hi
                rw [hi']
                simp [hx₁, hy₁]
          change
            (if hy' :
                (x₁.pair y₁).hasArity [a, b].length ∧
                  ∀ i : Fin [a, b].length,
                    (x₁.pair y₁).get [a, b].length i ∈ ⟦[α, β][i]⟧ᶻ
              then
                (⟦¬ˢ' (Term.abstract.go body [a, b] Δb0 hΔ_body).uncurry
                    (fun i =>
                      (⟨(x₁.pair y₁).get [a, b].length i, [α, β][i], hy'.2 i⟩ : SMT.Dom))⟧ˢ.get
                  (by
                    simpa [SMT.denote] using
                      (den_not_body_isSome
                        (w := fun i =>
                          (⟨(x₁.pair y₁).get [a, b].length i, [α, β][i], hy'.2 i⟩ : SMT.Dom))
                        (by
                          intro i
                          exact ⟨rfl, hy'.2 i⟩)))).fst
              else zffalse) = zftrue
          rw [dif_pos hy_pair]
          let Δgoal : RenamingContext.Context :=
            Function.update (Function.update Δb0 a (some wx₁)) b (some yy₁)
          have hφa_goal :
              RenamingContext.CoversFV Δgoal a!_spec := by
            intro v hv
            have hv' := fv_a!_spec hv
            rw [List.mem_union_iff] at hv'
            rcases hv' with hva | hva!
            · rw [fv, List.mem_singleton] at hva
              subst hva
              dsimp [Δgoal]
              rw [Function.update_of_ne b_ne_a.symm]
              rw [Function.update_self]
              rfl
            · have hv_eq : v = a! := by
                simpa [Singleton.singleton] using hva!
              subst hv_eq
              dsimp [Δgoal, Δb0]
              rw [Function.update_of_ne a!_ne_b, Function.update_of_ne a_ne_a!.symm,
                Function.update_of_ne a!_ne_b!, Function.update_self]
              rfl
          have hφb_goal :
              RenamingContext.CoversFV Δgoal b!_spec := by
            intro v hv
            have hv' := fv_b!_spec hv
            rw [List.mem_union_iff] at hv'
            rcases hv' with hvb | hvb!
            · rw [fv, List.mem_singleton] at hvb
              subst hvb
              dsimp [Δgoal]
              rw [Function.update_self]
              rfl
            · have hv_eq : v = b! := by
                simpa [Singleton.singleton] using hvb!
              subst hv_eq
              dsimp [Δgoal, Δb0]
              rw [Function.update_of_ne b_ne_b!.symm, Function.update_of_ne a_ne_b!.symm,
                Function.update_self]
              rfl
          let Δa : RenamingContext.Context :=
            Function.update (Function.update Δx a (some wx₁)) a! (some wy0)
          have hden_a_goal_eq :
              ⟦a!_spec.abstract Δgoal hφa_goal⟧ˢ =
                ⟦a!_spec.abstract Δa (hφa_at wx₁)⟧ˢ := by
            apply SMT.RenamingContext.denote_congr_of_agreesOnFV
              (h1 := hφa_goal) (h2 := hφa_at wx₁)
            intro v hv
            have hv' := fv_a!_spec hv
            rw [List.mem_union_iff] at hv'
            rcases hv' with hva | hva!
            · rw [fv, List.mem_singleton] at hva
              subst hva
              dsimp [Δgoal, Δa, Δb0]
              rw [Function.update_of_ne b_ne_a.symm, Function.update_self]
              rw [Function.update_of_ne a_ne_a!, Function.update_self]
            · have hv_eq : v = a! := by
                simpa [Singleton.singleton] using hva!
              cases hv_eq
              dsimp [Δgoal, Δa, Δb0]
              rw [Function.update_of_ne a!_ne_b, Function.update_of_ne a_ne_a!.symm,
                Function.update_of_ne a!_ne_b!, Function.update_self]
              rw [Function.update_self]
          let Δb : RenamingContext.Context :=
            Function.update
              (Function.update (Function.update Δx a! (some wy0)) b (some yy₁))
              b! (some wy1)
          have hden_b_goal_eq :
              ⟦b!_spec.abstract Δgoal hφb_goal⟧ˢ =
                ⟦b!_spec.abstract Δb (hφb_at yy₁)⟧ˢ := by
            apply SMT.RenamingContext.denote_congr_of_agreesOnFV
              (h1 := hφb_goal) (h2 := hφb_at yy₁)
            intro v hv
            have hv' := fv_b!_spec hv
            rw [List.mem_union_iff] at hv'
            rcases hv' with hvb | hvb!
            · rw [fv, List.mem_singleton] at hvb
              subst hvb
              dsimp [Δgoal, Δb]
              rw [Function.update_self]
              rw [Function.update_of_ne b_ne_b!, Function.update_self]
            · have hv_eq : v = b! := by
                simpa [Singleton.singleton] using hvb!
              cases hv_eq
              dsimp [Δgoal, Δb, Δb0]
              rw [Function.update_of_ne b_ne_b!.symm, Function.update_of_ne a_ne_b!.symm,
                Function.update_self]
              rw [Function.update_self]
          have hsome_a :
              ⟦a!_spec.abstract Δgoal hφa_goal⟧ˢ.isSome = true := by
            rw [hden_a_goal_eq]
            exact a_spec_total_at wx₁ rfl
          have hsome_b :
              ⟦b!_spec.abstract Δgoal hφb_goal⟧ˢ.isSome = true := by
            rw [hden_b_goal_eq]
            exact b_spec_total_at yy₁ rfl
          obtain ⟨Da, hden_a⟩ := Option.isSome_iff_exists.mp hsome_a
          obtain ⟨Db, hden_b⟩ := Option.isSome_iff_exists.mp hsome_b
          have hDa_ty : Da.snd.fst = SMTType.bool := by
            exact denote_type_eq_of_typing
              (typ_t := typ_a_ctx) (hden := hden_a)
          have hDb_ty : Db.snd.fst = SMTType.bool := by
            exact denote_type_eq_of_typing
              (typ_t := typ_b_ctx) (hden := hden_b)
          obtain ⟨Dspec, hden_specs, hDspec_ty⟩ :=
            denote_and_some_bool_of_some_bool hden_a hDa_ty hden_b hDb_ty
          obtain ⟨hcov_xa, Dxa, hDxa_ty, hDxa_val, hden_xa⟩ :=
            den_xa_at wx₁ rfl hx₁
          have hden_var_b :
              ⟦(Term.var b).abstract Δgoal
                  (by
                    intro v hv
                    rw [fv, List.mem_singleton] at hv
                    subst hv
                    dsimp [Δgoal]
                    rw [Function.update_self]
                    rfl)⟧ˢ = some yy₁ := by
            rw [SMT.Term.abstract.eq_def, SMT.denote, Option.pure_def, Option.some.injEq]
            apply Option.get_of_eq_some
            exact Function.update_self _ _ _
          have hcov_eq_goal :
              RenamingContext.CoversFV Δgoal ((@ˢx) (Term.var a) =ˢ Term.var b) := by
            have hcov_body_goal := hcov_body_upd wx₁ yy₁
            intro v hv
            apply hcov_body_goal v
            exact (by
              simpa [body, fv, or_assoc] using (Or.inl hv :
                v ∈ SMT.fv (((@ˢx) (Term.var a)) =ˢ Term.var b) ∨
                  v ∈ SMT.fv (a!_spec ∧ˢ b!_spec)))
          have hcov_app_goal :
              RenamingContext.CoversFV Δgoal ((@ˢx) (Term.var a)) := by
            have hcov_body_goal := hcov_body_upd wx₁ yy₁
            intro v hv
            apply hcov_body_goal v
            have hvEq :
                v ∈ SMT.fv (((@ˢx) (Term.var a)) =ˢ Term.var b) := by
              simpa [fv, or_assoc] using (Or.inl hv :
                v ∈ SMT.fv ((@ˢx) (Term.var a)) ∨ v ∈ SMT.fv (Term.var b))
            exact (by
              simpa [body, fv, or_assoc] using (Or.inl hvEq :
                v ∈ SMT.fv (((@ˢx) (Term.var a)) =ˢ Term.var b) ∨
                  v ∈ SMT.fv (a!_spec ∧ˢ b!_spec)))
          have hden_app_goal :
              ⟦((@ˢx) (Term.var a)).abstract Δgoal hcov_app_goal⟧ˢ = some Dxa := by
            have hden_eq :
                ⟦((@ˢx) (Term.var a)).abstract Δgoal hcov_app_goal⟧ˢ =
                  ⟦((@ˢx) (Term.var a)).abstract
                      (Function.update Δx a (some wx₁))
                      hcov_xa⟧ˢ := by
              apply SMT.RenamingContext.denote_congr_of_agreesOnFV
                (h1 := hcov_app_goal) (h2 := hcov_xa)
              intro v hv
              have hv' :
                  v ∈ SMT.fv x ∨ v ∈ SMT.fv (Term.var a) := by
                simpa [fv] using hv
              rcases hv' with hvx | hva
              · have hne_b : v ≠ b := by
                  intro h
                  subst h
                  exact b_not_mem_fv_x hvx
                have hne_a : v ≠ a := by
                  intro h
                  subst h
                  exact a_not_mem_fv_x hvx
                have hne_b! : v ≠ b! := by
                  intro h
                  subst h
                  exact b!_not_mem_fv_x hvx
                have hne_a! : v ≠ a! := by
                  intro h
                  subst h
                  exact a!_not_mem_fv_x hvx
                dsimp [Δgoal, Δb0]
                erw [Function.update_of_ne hne_b, Function.update_of_ne hne_a,
                  Function.update_of_ne hne_b!, Function.update_of_ne hne_a!,
                  Function.update_of_ne hne_a]
              · rw [fv, List.mem_singleton] at hva
                subst hva
                dsimp [Δgoal]
                erw [Function.update_of_ne b_ne_a.symm, Function.update_self, Function.update_self]
            rw [hden_eq]
            exact hden_xa
          have hden_body_false :
              ⟦body.abstract Δgoal (hcov_body_upd wx₁ yy₁)⟧ˢ =
                some ⟨zffalse, SMTType.bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
            by_cases hEqxy : Dxa.fst = y₁
            · have hDspec_false : Dspec.fst = zffalse := by
                have hDspec_bool : Dspec.fst ∈ 𝔹 := by
                  simpa [hDspec_ty] using Dspec.snd.snd
                rw [ZFSet.ZFBool.mem_𝔹_iff] at hDspec_bool
                rcases hDspec_bool with hDspec_false | hDspec_true
                · exact hDspec_false
                · exfalso
                  obtain ⟨Da', Db', hden_a_true, hDa_true, hden_b_true, hDb_true⟩ :=
                    denoteAndTrueComponents
                      (p := a!_spec.abstract Δgoal hφa_goal)
                      (q := b!_spec.abstract Δgoal hφb_goal)
                      (typ_p_bool := by
                        intro D hden
                        exact denote_type_eq_of_typing
                          (typ_t := typ_a_ctx) (hden := hden))
                      (typ_q_bool := by
                        intro D hden
                        exact denote_type_eq_of_typing
                          (typ_t := typ_b_ctx) (hden := hden))
                      hden_specs hDspec_true
                  have hden_a_true_at :
                      ⟦a!_spec.abstract
                          (Function.update (Function.update Δx a (some wx₁)) a! (some wy0))
                          (hφa_at wx₁)⟧ˢ = some Da' := by
                    rw [← hden_a_goal_eq]
                    exact hden_a_true
                  have hden_b_true_at :
                      ⟦b!_spec.abstract
                          (Function.update
                            (Function.update (Function.update Δx a! (some wy0)) b (some yy₁))
                            b! (some wy1))
                          (hφb_at yy₁)⟧ˢ = some Db' := by
                    rw [← hden_b_goal_eq]
                    exact hden_b_true
                  have hcast_x₁_wy0_pair :
                      x₁.pair wy0.fst ∈ castα := by
                    exact a_spec_true_implies_cast wx₁ rfl
                      (hφa_at wx₁) hden_a_true_at hDa_true
                  have hcast_y₁_wy1_pair :
                      y₁.pair wy1.fst ∈ castβ := by
                    exact b_spec_true_implies_cast yy₁ rfl
                      (hφb_at yy₁) hden_b_true_at hDb_true
                  have hx₁_dom_cast : x₁ ∈ castα.Dom := by
                    simpa [ZFSet.is_func_dom_eq hcastα] using hx₁
                  have hy₁_dom_cast : y₁ ∈ castβ.Dom := by
                    simpa [ZFSet.is_func_dom_eq hcastβ] using hy₁
                  have hcast_x₁_wy0 :
                      @ᶻcastα ⟨x₁, hx₁_dom_cast⟩ = wy0.fst := by
                    have hpair := ZFSet.fapply.of_pair
                      (ZFSet.is_func_is_pfunc hcastα) hcast_x₁_wy0_pair
                    simpa only [Subtype.ext_iff] using hpair
                  have hcast_y₁_wy1 :
                      @ᶻcastβ ⟨y₁, hy₁_dom_cast⟩ = wy1.fst := by
                    have hpair := ZFSet.fapply.of_pair
                      (ZFSet.is_func_is_pfunc hcastβ) hcast_y₁_wy1_pair
                    simpa only [Subtype.ext_iff] using hpair
                  have hXx₁_eq_y₁ :
                      @ᶻX.fst
                        ⟨x₁, by
                          simpa [ZFSet.is_func_dom_eq hX_func] using hx₁⟩ = y₁ := by
                    rw [← hDxa_val]
                    exact hEqxy
                  have hx₁_eq_x₀r : x₁ = x₀r := by
                    have hcast_x₀r :
                        @ᶻcastα
                          ⟨x₀r, by
                            simpa [ZFSet.is_func_dom_eq hcastα] using hx₀r_mem⟩ = wy0.fst := by
                      simpa [Subtype.ext_iff] using hcast_x₀r_wy0
                    have hcast_eq :
                        @ᶻcastα ⟨x₁, hx₁_dom_cast⟩ =
                          @ᶻcastα
                            ⟨x₀r, by
                              simpa [ZFSet.is_func_dom_eq hcastα] using hx₀r_mem⟩ := by
                      apply Subtype.ext
                      exact hcast_x₁_wy0.trans hcast_x₀r.symm
                    have hinj := IsInjective.apply_inj hcastα hx₁_dom_cast hcast_eq
                    rw [Subtype.ext_iff] at hinj
                    exact hinj
                  have hcast_rhs :
                      @ᶻcastβ
                        ⟨↑(@ᶻX.fst
                            ⟨x₀r, by
                              simpa [ZFSet.is_func_dom_eq hX_func] using hx₀r_mem⟩),
                          by
                            subst hx₁_eq_x₀r
                            simpa [hXx₁_eq_y₁, ZFSet.is_func_dom_eq hcastβ] using hy₁⟩ = wy1.fst := by
                    subst hx₁_eq_x₀r
                    simpa [hXx₁_eq_y₁] using hcast_y₁_wy1
                  have hDapp_eq_wy1 : Dapp.fst = wy1.fst := by
                    calc
                      Dapp.fst =
                          @ᶻcastβ
                            ⟨↑(@ᶻX.fst
                                ⟨x₀r, by
                                  simpa [ZFSet.is_func_dom_eq hX_func] using hx₀r_mem⟩),
                              by
                                simpa [ZFSet.is_func_dom_eq hcastβ] using
                                  (Subtype.property
                                    (@ᶻX.fst
                                      ⟨x₀r, by
                                        simpa [ZFSet.is_func_dom_eq hX_func] using hx₀r_mem⟩))⟩ := hDapp_from_range
                      _ = wy1.fst := hcast_rhs
                  exact hEq hDapp_eq_wy1.symm
              have hden_eq_true :
                  ⟦(((@ˢx) (Term.var a)) =ˢ Term.var b).abstract Δgoal hcov_eq_goal⟧ˢ =
                    some ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
                simpa [SMT.Term.abstract, proof_irrel_heq] using
                  (denote_eq_eq_zftrue_of_fst_eq hden_app_goal hden_var_b (hDxa_ty.trans rfl) hEqxy)
              simpa [body, SMT.Term.abstract, proof_irrel_heq] using
                (denote_and_eq_zffalse_of_some_zffalse_right
                  hden_eq_true rfl hden_specs hDspec_ty hDspec_false)
            · have hden_eq_false :
                  ⟦(((@ˢx) (Term.var a)) =ˢ Term.var b).abstract Δgoal hcov_eq_goal⟧ˢ =
                    some ⟨zffalse, SMTType.bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
                simpa [SMT.Term.abstract, proof_irrel_heq] using
                  (funDenoteEqFalseOfFstNe hden_app_goal hden_var_b (hDxa_ty.trans rfl) (by simpa using hEqxy))
              simpa [body, SMT.Term.abstract, proof_irrel_heq] using
                (denote_and_eq_zffalse_of_some_zffalse_left
                  hden_eq_false rfl rfl hden_specs hDspec_ty)
          have hw :
              ∀ i : Fin [a, b].length,
                ((fun i => (⟨(x₁.pair y₁).get [a, b].length i, [α, β][i], hy_pair.2 i⟩ : SMT.Dom)) i).snd.fst =
                  [α, β][i] ∧
                ((fun i => (⟨(x₁.pair y₁).get [a, b].length i, [α, β][i], hy_pair.2 i⟩ : SMT.Dom)) i).fst ∈
                  ⟦[α, β][i]⟧ᶻ := by
            intro i
            exact ⟨rfl, hy_pair.2 i⟩
          have hcov_not_goal :
              RenamingContext.CoversFV Δgoal (¬ˢ body) := by
            intro v hv
            exact hcov_body_upd wx₁ yy₁ v (by simpa [fv] using hv)
          have hden_not_true :
              ⟦¬ˢ' (Term.abstract.go body [a, b] Δb0 hΔ_body).uncurry
                  (fun i => ⟨(x₁.pair y₁).get [a, b].length i, [α, β][i], hy_pair.2 i⟩)⟧ˢ =
                some ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
            have hgo :=
              funAbstractGoPair
                (Δctx := Δb0) (P := body) (v₁ := a) (v₂ := b)
                (τ₁ := α) (τ₂ := β)
                hΔ_body hcov_body_upd
                (fun i => ⟨(x₁.pair y₁).get [a, b].length i, [α, β][i], hy_pair.2 i⟩) hw
            have hw0 :
                (fun i => ⟨(x₁.pair y₁).get [a, b].length i, [α, β][i], hy_pair.2 i⟩) ⟨0, by simp⟩ = wx₁ := by
              change (⟨(x₁.pair y₁).get [a, b].length ⟨0, by simp⟩, α, hy_pair.2 ⟨0, by simp⟩⟩ : SMT.Dom) =
                (⟨x₁, α, hx₁⟩ : SMT.Dom)
              apply PSigma.ext
              · simp [ZFSet.get]
              · simp only [List.length_cons, List.length_nil, Nat.reduceAdd, ZFSet.get,
                  Fin.reduceLast, Fin.isValue, dite_eq_ite, Fin.getElem_fin, Fin.zero_eta,
                  Fin.zero_eq_one_iff, Nat.succ_ne_self, ↓dreduceIte, Fin.coe_ofNat_eq_mod,
                  Nat.zero_mod, List.getElem_cons_zero, ↓dreduceDIte, Fin.castPred_zero]
                congr
                · funext τ
                  simp only [π₁_pair, eq_iff_iff]
                · apply proof_irrel_heq
            have hw1 :
                (fun i => ⟨(x₁.pair y₁).get [a, b].length i, [α, β][i], hy_pair.2 i⟩) ⟨1, by simp⟩ = yy₁ := by
              change (⟨(x₁.pair y₁).get [a, b].length ⟨1, by simp⟩, β, hy_pair.2 ⟨1, by simp⟩⟩ : SMT.Dom) =
                (⟨y₁, β, hy₁⟩ : SMT.Dom)
              apply PSigma.ext
              · simp [ZFSet.get]
              · simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_one_sub_one,
                  ZFSet.get, Fin.reduceLast, Fin.isValue, dite_eq_ite, Fin.getElem_fin,
                  Fin.zero_eta, Fin.zero_eq_one_iff, Nat.succ_ne_self, ↓dreduceIte,
                  Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.getElem_cons_zero,
                  List.getElem_cons_succ, ↓dreduceDIte, Fin.castPred_zero]
                congr
                · funext τ
                  simpa [if_pos rfl, π₂_pair]
                · apply proof_irrel_heq
            rw [hgo]
            rw [hw0, hw1]
            simpa [SMT.Term.abstract, proof_irrel_heq] using
              (funNotAbstractEqZftrueOfSomeZffalse
                (Δctx := Δgoal) (t := body)
                (D := ⟨zffalse, SMTType.bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩)
                (hcov_t := hcov_body_upd wx₁ yy₁)
                hden_body_false rfl rfl hcov_not_goal)
          have hget :
              (⟦¬ˢ' (Term.abstract.go body [a, b] Δb0 hΔ_body).uncurry
                  (fun i => ⟨(x₁.pair y₁).get [a, b].length i, [α, β][i], hy_pair.2 i⟩)⟧ˢ.get
                (den_not_body_isSome hw)).fst = zftrue := by
            have hget_eq :
                (⟦¬ˢ' (Term.abstract.go body [a, b] Δb0 hΔ_body).uncurry
                    (fun i => ⟨(x₁.pair y₁).get [a, b].length i, [α, β][i], hy_pair.2 i⟩)⟧ˢ.get
                  (den_not_body_isSome hw)) =
                  ⟨zftrue, ⟨SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩⟩ := by
              apply Option.get_of_eq_some
              simpa [Function.OfArity.uncurry, Function.FromTypes.uncurry,
                proof_irrel_heq] using hden_not_true
            exact congrArg (fun D : SMT.Dom => D.fst) hget_eq
          exact hget)
    -/
    erw [hden_forall]
    simp only [Option.pure_def, Option.failure_eq_none, Option.bind_eq_bind, Option.bind_some,
      Option.some.injEq, PSigma.mk.injEq]
    refine ⟨hExistsFalse, ?_⟩
    congr
    · funext τ
      erw [hExistsFalse]
    · apply proof_irrel_heq
  simpa [bBody, funBBodyTerm, SMT.Term.abstract, proof_irrel_heq] using
    (denote_eq_eq_zftrue_of_fst_eq hden_eq_false hden_exists_ab_false rfl rfl)

set_option maxHeartbeats 1000000
theorem funDenSpecTrueAtCast.{u}
    {α β α' β' : SMTType}
    {pα : α ⇝ α'} {pβ : β ⇝ β'}
    {x a!_spec b!_spec hdefault : Term}
    {x! a a! b b! : 𝒱}
    {Γ : TypeContext}
    {Δctx : RenamingContext.Context.{u}}
    {X X! : SMT.Dom.{u}}
    (hX!_ty : X!.snd.fst = α'.fun β')
    (typ_fun_spec_base :
      AList.insert x! (α'.fun β') Γ ⊢ˢ
        funSpecTerm x x! a a! b b! α β α' β' a!_spec b!_spec hdefault : SMTType.bool)
    (typ_a!_spec_ctx_base :
      AList.insert a! α' (AList.insert a α (AList.insert x! (α'.fun β') Γ)) ⊢ˢ
        a!_spec : SMTType.bool)
    (typ_b!_spec_ctx_base :
      AList.insert b! β'
        (AList.insert b β
          (AList.insert a! α' (AList.insert a α (AList.insert x! (α'.fun β') Γ)))) ⊢ˢ
        b!_spec : SMTType.bool)
    (fv_a!_spec : fv a!_spec ⊆ fv (Term.var a) ∪ {a!})
    (fv_b!_spec : fv b!_spec ⊆ fv (Term.var b) ∪ {b!})
    (hφX! :
      RenamingContext.CoversFV
        (Function.update Δctx x! (some X!))
        (funSpecTerm x x! a a! b b! α β α' β' a!_spec b!_spec hdefault))
    (castα castβ : ZFSet)
    (hcastα : ZFSet.IsFunc ⟦α⟧ᶻ ⟦α'⟧ᶻ castα)
    (hcastβ : ZFSet.IsFunc ⟦β⟧ᶻ ⟦β'⟧ᶻ castβ)
    (hcastα_inj : castα.IsInjective hcastα)
    (hX_func : ZFSet.IsFunc ⟦α⟧ᶻ ⟦β⟧ᶻ X.fst)
    (hX!_func : ZFSet.IsFunc ⟦α'⟧ᶻ ⟦β'⟧ᶻ X!.fst)
    (hX!_app_default :
      ∀ (wy0 : SMT.Dom.{u}) (hwy0_ty : wy0.snd.fst = α')
        (hy_not_ran : wy0.fst ∉ castα.Range),
        ZFSet.fapply X!.fst (ZFSet.is_func_is_pfunc hX!_func)
          ⟨wy0.fst, by
            simpa [ZFSet.is_func_dom_eq hX!_func, hwy0_ty] using wy0.snd.snd⟩ =
          β'.defaultZFSet)
    (hX!_app_range :
      ∀ (wy0 : SMT.Dom.{u}) (hwy0_ty : wy0.snd.fst = α')
        (hy_ran : wy0.fst ∈ castα.Range),
        ∃ (x₀ : ZFSet) (hx₀_mem : x₀ ∈ ⟦α⟧ᶻ),
          @ᶻcastα
            ⟨x₀, by
              rw [ZFSet.is_func_dom_eq hcastα]
              exact hx₀_mem⟩ = wy0.fst ∧
          ZFSet.fapply X!.fst (ZFSet.is_func_is_pfunc hX!_func)
            ⟨wy0.fst, by
              simpa [ZFSet.is_func_dom_eq hX!_func, hwy0_ty] using wy0.snd.snd⟩ =
            @ᶻcastβ
              ⟨@ᶻX.fst
                  ⟨x₀, by
                    simpa [ZFSet.is_func_dom_eq hX_func] using hx₀_mem⟩, by
                    rw [ZFSet.is_func_dom_eq hcastβ]
                    exact Subtype.property _⟩)
    (x!_ne_a! : x! ≠ a!)
    (x!_ne_b! : x! ≠ b!)
    (a_ne_a! : a ≠ a!)
    (b_not_base :
      b ∉ AList.insert a! α' (AList.insert a α (AList.insert x! (α'.fun β') Γ)))
    (b!_not_base :
      b! ∉ AList.insert b β
        (AList.insert a! α' (AList.insert a α (AList.insert x! (α'.fun β') Γ))))
    (a_not_mem_fv_x : a ∉ fv x)
    (b_not_mem_fv_x : b ∉ fv x)
    (a!_not_mem_fv_x : a! ∉ fv x)
    (b!_not_mem_fv_x : b! ∉ fv x)
    (den_xa_at :
      ∀ (Yfun x₀ : SMT.Dom.{u}) (hx₀_ty : x₀.snd.fst = α)
        (hx₀_mem : x₀.fst ∈ ⟦α⟧ᶻ),
        ∃ hcov_app :
          RenamingContext.CoversFV
            (Function.update (Function.update Δctx x! (some Yfun)) a (some x₀))
            ((@ˢx) (Term.var a)),
          ∃ Dapp : SMT.Dom.{u},
            Dapp.snd.fst = β ∧
              Dapp.fst =
                @ᶻX.fst
                  ⟨x₀.fst, by
                    simpa [ZFSet.is_func_dom_eq hX_func] using hx₀_mem⟩ ∧
              ⟦((@ˢx) (Term.var a)).abstract
                  (Function.update (Function.update Δctx x! (some Yfun)) a (some x₀))
                  hcov_app⟧ˢ =
                some Dapp)
    (hφa_at :
      ∀ (Yfun x₀ wy0 : SMT.Dom.{u}),
        RenamingContext.CoversFV
          (Function.update
            (Function.update (Function.update Δctx x! (some Yfun)) a (some x₀))
            a! (some wy0))
          a!_spec)
    (hφb_at :
      ∀ (Yfun wy0 y₀ wy1 : SMT.Dom.{u}),
        RenamingContext.CoversFV
          (Function.update
            (Function.update
              (Function.update (Function.update Δctx x! (some Yfun)) a! (some wy0))
              b (some y₀))
            b! (some wy1))
          b!_spec)
    (a_spec_total_at :
      ∀ (Yfun x₀ wy0 : SMT.Dom.{u})
        (hx₀_ty : x₀.snd.fst = α)
        (hwy0_ty : wy0.snd.fst = α'),
        ⟦a!_spec.abstract
            (Function.update
              (Function.update (Function.update Δctx x! (some Yfun)) a (some x₀))
              a! (some wy0))
            (hφa_at Yfun x₀ wy0)⟧ˢ.isSome =
          true)
    (b_spec_total_at :
      ∀ (Yfun wy0 y₀ wy1 : SMT.Dom.{u})
        (hy₀_ty : y₀.snd.fst = β)
        (hwy1_ty : wy1.snd.fst = β'),
        ⟦b!_spec.abstract
            (Function.update
              (Function.update
                (Function.update (Function.update Δctx x! (some Yfun)) a! (some wy0))
                b (some y₀))
              b! (some wy1))
            (hφb_at Yfun wy0 y₀ wy1)⟧ˢ.isSome =
          true)
    (a_spec_true_at :
      ∀ (Yfun x₀ wy0 : SMT.Dom.{u})
        (hx₀_ty : x₀.snd.fst = α)
        (hwy0_ty : wy0.snd.fst = α')
        (hcast_x₀w : x₀.fst.pair wy0.fst ∈ castα),
        ∃ (hφa :
          RenamingContext.CoversFV
            (Function.update
              (Function.update (Function.update Δctx x! (some Yfun)) a (some x₀))
              a! (some wy0))
            a!_spec)
          (Φa : SMT.Dom.{u}),
          ⟦a!_spec.abstract
              (Function.update
                (Function.update (Function.update Δctx x! (some Yfun)) a (some x₀))
                a! (some wy0))
              hφa⟧ˢ =
            some Φa ∧
          Φa.fst = zftrue)
    (b_spec_true_at :
      ∀ (Yfun wy0 y₀ wy1 : SMT.Dom.{u})
        (hy₀_ty : y₀.snd.fst = β)
        (hwy1_ty : wy1.snd.fst = β')
        (hcast_y₀w : y₀.fst.pair wy1.fst ∈ castβ),
        ∃ (hφb :
          RenamingContext.CoversFV
            (Function.update
              (Function.update
                (Function.update (Function.update Δctx x! (some Yfun)) a! (some wy0))
                b (some y₀))
              b! (some wy1))
            b!_spec)
          (Φb : SMT.Dom.{u}),
          ⟦b!_spec.abstract
              (Function.update
                (Function.update
                  (Function.update (Function.update Δctx x! (some Yfun)) a! (some wy0))
                  b (some y₀))
                b! (some wy1))
              hφb⟧ˢ =
            some Φb ∧
          Φb.fst = zftrue)
    (a_spec_true_implies_cast :
      ∀ (Yfun x₀ wy0 : SMT.Dom.{u})
        (hx₀_ty : x₀.snd.fst = α)
        (hwy0_ty : wy0.snd.fst = α')
        (hφa :
          RenamingContext.CoversFV
            (Function.update
              (Function.update (Function.update Δctx x! (some Yfun)) a (some x₀))
              a! (some wy0))
            a!_spec)
        {Φa : SMT.Dom.{u}},
        ⟦a!_spec.abstract
            (Function.update
              (Function.update (Function.update Δctx x! (some Yfun)) a (some x₀))
              a! (some wy0))
            hφa⟧ˢ =
          some Φa →
        Φa.fst = zftrue →
        x₀.fst.pair wy0.fst ∈ castα)
    (b_spec_true_implies_cast :
      ∀ (Yfun wy0 y₀ wy1 : SMT.Dom.{u})
        (hy₀_ty : y₀.snd.fst = β)
        (hwy1_ty : wy1.snd.fst = β')
        (hφb :
          RenamingContext.CoversFV
            (Function.update
              (Function.update
                (Function.update (Function.update Δctx x! (some Yfun)) a! (some wy0))
                b (some y₀))
              b! (some wy1))
            b!_spec)
        {Φb : SMT.Dom.{u}},
        ⟦b!_spec.abstract
            (Function.update
              (Function.update
                (Function.update (Function.update Δctx x! (some Yfun)) a! (some wy0))
                b (some y₀))
              b! (some wy1))
            hφb⟧ˢ =
          some Φb →
        Φb.fst = zftrue →
        y₀.fst.pair wy1.fst ∈ castβ)
    (den_app_at :
      ∀ (Yfun wy0 : SMT.Dom.{u})
        (hYfun_ty : Yfun.snd.fst = α'.fun β')
        (hYfun_func : ZFSet.IsFunc ⟦α'⟧ᶻ ⟦β'⟧ᶻ Yfun.fst)
        (hwy0_ty : wy0.snd.fst = α'),
        ∃ Dapp : SMT.Dom.{u},
          Dapp.snd.fst = β' ∧
            Dapp.fst =
              @ᶻYfun.fst
                ⟨wy0.fst, by
                  simpa [ZFSet.is_func_dom_eq hYfun_func, hwy0_ty] using wy0.snd.snd⟩ ∧
            ⟦((@ˢTerm.var x!) (Term.var a!)).abstract
                (Function.update (Function.update Δctx x! (some Yfun)) a! (some wy0))
                (by
                  intro v hv
                  simp only [fv, List.mem_append, List.mem_singleton] at hv
                  rcases hv with hv | hv
                  · subst hv
                    rw [Function.update_of_ne x!_ne_a!]
                    rw [Function.update_self]
                    rfl
                  · subst hv
                    rw [Function.update_self]
                    rfl)⟧ˢ =
              some Dapp)
    (default_spec_at :
      ∀ (Yfun wy0 Dapp : SMT.Dom.{u})
        (hden_app :
          ⟦((@ˢTerm.var x!) (Term.var a!)).abstract
              (Function.update (Function.update Δctx x! (some Yfun)) a! (some wy0))
              (by
                intro v hv
                simp only [fv, List.mem_append, List.mem_singleton] at hv
                rcases hv with hv | hv
                · subst hv
                  rw [Function.update_of_ne x!_ne_a!]
                  rw [Function.update_self]
                  rfl
                · subst hv
                  rw [Function.update_self]
                  rfl)⟧ˢ =
            some Dapp),
        ∃ (hφd :
          RenamingContext.CoversFV
            (Function.update (Function.update Δctx x! (some Yfun)) a! (some wy0))
            hdefault)
          (Φd : SMT.Dom.{u}),
          ⟦hdefault.abstract
              (Function.update (Function.update Δctx x! (some Yfun)) a! (some wy0))
              hφd⟧ˢ =
            some Φd ∧
          Φd.snd.fst = SMTType.bool ∧
          (Dapp.fst = β'.defaultZFSet → Φd.fst = zftrue)) :
    ∃ Φ : SMT.Dom.{u},
      ⟦(funSpecTerm x x! a a! b b! α β α' β' a!_spec b!_spec hdefault).abstract
          (Function.update Δctx x! (some X!))
          hφX!⟧ˢ =
        some Φ ∧
      Φ.snd.fst = SMTType.bool ∧
      Φ.fst = zftrue := by
  let exists_a : Term := .exists [a] [α] a!_spec
  let exists_ab : Term := funExistsABTerm x a!_spec b!_spec a b α β
  let bBody : Term := funBBodyTerm x! a! b! exists_ab
  let aBody : Term := (.ite exists_a (.forall [b!] [β'] bBody) hdefault)
  let Δx : RenamingContext.Context := Function.update Δctx x! (some X!)
  have typ_fun_spec_base' := typ_fun_spec_base
  change
    (AList.insert x! (α'.fun β') Γ) ⊢ˢ
      (.forall [a!] [α'] aBody) : SMTType.bool at typ_fun_spec_base'
  obtain ⟨_, _, _, _, _, typ_aBody_base⟩ :=
    SMT.Typing.forallE typ_fun_spec_base'
  obtain ⟨typ_exists_a_base, typ_forall_b_base, _⟩ :=
    SMT.Typing.iteE typ_aBody_base
  have hgo_cov_a :
      ∀ v ∈ SMT.fv aBody, v ∉ [a!] → (Δx v).isSome = true := by
    intro v hv hnot
    have hv' :
        v ∈ fv (funSpecTerm x x! a a! b b! α β α' β' a!_spec b!_spec hdefault) := by
      change v ∈ fv (Term.forall [a!] [α'] aBody)
      rw [fv]
      exact List.mem_removeAll_iff.mpr ⟨hv, hnot⟩
    exact hφX! v hv'
  have hcov_aBody_upd :
      ∀ wy0 : SMT.Dom,
        RenamingContext.CoversFV (Function.update Δx a! (some wy0)) aBody := by
    intro wy0 v hv
    by_cases hva! : v = a!
    · subst hva!
      rw [Function.update_self]
      rfl
    · rw [Function.update_of_ne hva!]
      exact hgo_cov_a v hv (by simpa [List.mem_singleton] using hva!)
  have hupdate_forall_a_base :
      SMT.TypeContext.update
        (AList.insert x! (α'.fun β') Γ) [a!] [α'] rfl =
        AList.insert a! α' (AList.insert x! (α'.fun β') Γ) := by
    simp only [SMT.TypeContext.update, List.length_cons, List.length_nil, zero_add,
      Fin.cast_eq_self, Fin.getElem_fin, Fin.foldl_succ_last, Fin.coe_ofNat_eq_mod,
      Nat.mod_succ, List.getElem_cons_zero, Fin.last_zero, Fin.isValue,
      Fin.foldl_zero]
  have typ_forall_b_base' :
      (AList.insert a! α' (AList.insert x! (α'.fun β') Γ)) ⊢ˢ
        (.forall [b!] [β'] bBody) : SMTType.bool := by
    rw [hupdate_forall_a_base] at typ_forall_b_base
    exact typ_forall_b_base
  obtain ⟨_, _, _, _, _, typ_bBody_base⟩ :=
    SMT.Typing.forallE typ_forall_b_base'
  have hcov_app_at :
      ∀ (Yfun wy0 : SMT.Dom.{u}),
        RenamingContext.CoversFV
          (Function.update (Function.update Δctx x! (some Yfun)) a! (some wy0))
          ((@ˢTerm.var x!) (Term.var a!)) := by
    intro Yfun wy0 v hv
    simp only [fv, List.mem_append, List.mem_singleton] at hv
    rcases hv with hv | hv
    · subst hv
      rw [Function.update_of_ne x!_ne_a!]
      rw [Function.update_self]
      rfl
    · subst hv
      rw [Function.update_self]
      rfl
  have hbody_true_at :
      ∀ (wy0 : SMT.Dom),
        wy0.snd.fst = α' →
          ∃ D : SMT.Dom,
            ⟦aBody.abstract (Function.update Δx a! (some wy0)) (hcov_aBody_upd wy0)⟧ˢ =
              some D ∧
            D.fst = zftrue := by
    as_aux_lemma =>
    intro wy0 hwy0_ty
    by_cases hy_ran : wy0.fst ∈ castα.Range
    · have hφ_exists_a :
        RenamingContext.CoversFV
          (Function.update Δx a! (some wy0)) exists_a := by
        intro v hv
        have hv_remove :
            v ∈ List.removeAll (fv a!_spec) [a] := by
          simpa [exists_a, fv] using hv
        exact funRemoveAllASpecUpdateIsSome
          (fv_a!_spec := fv_a!_spec)
          (ha! := by
            rw [Function.update_self]
            rfl)
          v hv_remove
      have hgo_cov_a_spec :
          ∀ v ∈ fv a!_spec, v ∉ [a] →
            (Function.update Δx a! (some wy0) v).isSome = true := by
        intro v hv hv_not_a
        have hv_remove : v ∈ List.removeAll (fv a!_spec) [a] := by
          exact List.mem_removeAll_iff.mpr ⟨hv, hv_not_a⟩
        exact funRemoveAllASpecUpdateIsSome
          (fv_a!_spec := fv_a!_spec)
          (ha! := by
            rw [Function.update_self]
            rfl)
          v hv_remove
      have hctx_swap :
          ∀ x₀ : SMT.Dom,
            Function.update (Function.update Δx a! (some wy0)) a (some x₀) =
              Function.update
                (Function.update (Function.update Δctx x! (some X!)) a (some x₀))
                a! (some wy0) := by
        intro x₀
        simpa [Δx] using
          funUpdateSwap
            (Δctx := Function.update Δctx x! (some X!))
            (a_ne_a! := a_ne_a!)
            x₀ wy0
      have hcov_a_spec_upd :
          ∀ x₀ : SMT.Dom,
            RenamingContext.CoversFV
              (Function.update (Function.update Δx a! (some wy0)) a (some x₀))
              a!_spec := by
        intro x₀ v hv
        rw [hctx_swap x₀]
        exact hφa_at X! x₀ wy0 v hv
      have typ_a!_spec_swap :
          AList.insert a α (AList.insert a! α' (AList.insert x! (α'.fun β') Γ)) ⊢ˢ
            a!_spec : SMTType.bool := by
        exact SMT.Typing.weakening
          (h := typeContext_insert_swap_entries a_ne_a!.symm)
          typ_a!_spec_ctx_base
      obtain ⟨x₀, hx₀_mem, hcast_x₀_wy0, hX!_app_eq⟩ :=
        hX!_app_range wy0 hwy0_ty hy_ran
      let wx₀ : SMT.Dom := ⟨x₀, α, hx₀_mem⟩
      have hx₀_dom_cast : x₀ ∈ castα.Dom := by
        simpa [ZFSet.is_func_dom_eq hcastα] using hx₀_mem
      have hcast_x₀_wy0_pair :
          wx₀.fst.pair wy0.fst ∈ castα := by
        simpa [wx₀, hcast_x₀_wy0] using
          ZFSet.fapply.def (ZFSet.is_func_is_pfunc hcastα) hx₀_dom_cast
      have hden_exists_a_true :
          ⟦exists_a.abstract (Function.update Δx a! (some wy0)) hφ_exists_a⟧ˢ =
            some ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
        obtain ⟨hφa, Φa, hden_a, hΦa_true⟩ :=
          a_spec_true_at X! wx₀ wy0 rfl hwy0_ty hcast_x₀_wy0_pair
        have typ_exists_a_base' :
            AList.insert a! α' (AList.insert x! (α'.fun β') Γ) ⊢ˢ
              exists_a : SMTType.bool := by
          rw [← hupdate_forall_a_base]
          exact typ_exists_a_base
        refine funUnaryExistsEqZftrueAtWitness
          (Γ := AList.insert a! α' (AList.insert x! (α'.fun β') Γ))
          (Δctx := Function.update Δx a! (some wy0))
          (a := a!_spec) (v := a) (τ := α)
          typ_exists_a_base'
          hφ_exists_a hgo_cov_a_spec hcov_a_spec_upd
          (hbody_total := ?_) (hbody_ty := ?_)
          (W := wx₀) (hW_ty := rfl) (D := Φa) ?_ ?_
        · intro x₁ hx₁_ty
          simpa [hctx_swap x₁, proof_irrel_heq] using
            a_spec_total_at X! x₁ wy0 hx₁_ty hwy0_ty
        · intro x₁ hx₁_ty D hden_a'
          exact denote_type_eq_of_typing
            (typ_t := typ_a!_spec_swap) (hden := hden_a')
        · simpa [hctx_swap wx₀, proof_irrel_heq, wx₀] using hden_a
        · exact hΦa_true
      have hφ_forall_b :
          RenamingContext.CoversFV
            (Function.update Δx a! (some wy0))
            (Term.forall [b!] [β'] bBody) := by
        intro v hv
        by_cases hva! : v = a!
        · subst hva!
          rw [Function.update_self]
          rfl
        · rw [Function.update_of_ne hva!]
          exact hgo_cov_a v
            (by
              dsimp [aBody]
              exact SMT.fv.mem_ite <| Or.inr <| Or.inl hv)
            (by simpa [List.mem_singleton] using hva!)
      have hden_forall_b_true :
          ⟦(Term.forall [b!] [β'] bBody).abstract
              (Function.update Δx a! (some wy0))
              hφ_forall_b⟧ˢ =
            some ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
        have hupdate_forall_b_base :
            SMT.TypeContext.update
              (AList.insert a! α' (AList.insert x! (α'.fun β') Γ))
              [b!] [β'] rfl =
              AList.insert b! β'
                (AList.insert a! α' (AList.insert x! (α'.fun β') Γ)) := by
          unfold SMT.TypeContext.update
          simp only [List.length_cons, List.length_nil, zero_add,
            Fin.foldl_succ_last, Fin.getElem_fin, Fin.coe_cast,
            Fin.val_last, List.getElem_cons_zero, Fin.coe_castSucc,
            Fin.foldl_zero]
        have typ_bBody_base' :
            AList.insert b! β'
              (AList.insert a! α' (AList.insert x! (α'.fun β') Γ)) ⊢ˢ
              bBody : SMTType.bool := by
          rw [← hupdate_forall_b_base]
          exact typ_bBody_base
        have hgo_cov_b :
            ∀ v ∈ fv bBody, v ∉ [b!] →
              (Function.update Δx a! (some wy0) v).isSome = true := by
          intro v hv hv_not_b!
          have hv_forall_b :
              v ∈ fv (Term.forall [b!] [β'] bBody) := by
            rw [fv]
            exact List.mem_removeAll_iff.mpr ⟨hv, hv_not_b!⟩
          by_cases hva! : v = a!
          · subst hva!
            rw [Function.update_self]
            rfl
          · rw [Function.update_of_ne hva!]
            exact hgo_cov_a v
              (by
                dsimp [aBody]
                exact SMT.fv.mem_ite <| Or.inr <| Or.inl hv_forall_b)
              (by simpa [List.mem_singleton] using hva!)
        have hcov_bBody_upd :
            ∀ wy1 : SMT.Dom,
              RenamingContext.CoversFV
                (Function.update (Function.update Δx a! (some wy0)) b! (some wy1))
                bBody := by
          intro wy1 v hv
          by_cases hvb! : v = b!
          · subst hvb!
            rw [Function.update_self]
            rfl
          · rw [Function.update_of_ne hvb!]
            exact hgo_cov_b v hv (by simpa [List.mem_singleton] using hvb!)
        have b_ne_a : b ≠ a := by
          intro h
          subst h
          exact b_not_base (by
            rw [AList.mem_insert]
            exact Or.inr (by
              rw [AList.mem_insert]
              exact Or.inl rfl))
        have a!_ne_b : a! ≠ b := by
          intro h
          exact b_not_base (h ▸ by
            rw [AList.mem_insert]
            exact Or.inl rfl)
        have a_ne_b! : a ≠ b! := by
          intro hab!
          exact b!_not_base (hab! ▸ by
            rw [AList.mem_insert]
            exact Or.inr (by
              rw [AList.mem_insert]
              exact Or.inr (by
                rw [AList.mem_insert]
                exact Or.inl rfl)))
        have a!_ne_b! : a! ≠ b! := by
          intro ha!b!
          exact b!_not_base (ha!b! ▸ by
            rw [AList.mem_insert]
            exact Or.inr (by
              rw [AList.mem_insert]
              exact Or.inl rfl))
        have hbody_true_b_at :
            ∀ (wy1 : SMT.Dom), wy1.snd.fst = β' →
              ∃ D : SMT.Dom,
                ⟦bBody.abstract
                    (Function.update (Function.update Δx a! (some wy0)) b! (some wy1))
                    (hcov_bBody_upd wy1)⟧ˢ =
                  some D ∧
                D.fst = zftrue := by
          as_aux_lemma =>
          intro wy1 hwy1_ty
          let Δb0 : RenamingContext.Context :=
            Function.update (Function.update Δx a! (some wy0)) b! (some wy1)
          obtain ⟨Dapp, hDapp_ty, hDapp_val, hden_app_lhs⟩ :=
            den_app_at X! wy0 hX!_ty hX!_func hwy0_ty
          have hb!_not_mem_fv_app_lhs :
              b! ∉ fv ((@ˢTerm.var x!) (Term.var a!)) := by
            intro hv
            simp only [fv, List.mem_append, List.mem_singleton] at hv
            rcases hv with hv | hv
            · exact x!_ne_b! hv.symm
            · exact a!_ne_b! hv.symm
          have hcov_app_b! :
              RenamingContext.CoversFV
                (Function.update (Function.update Δx a! (some wy0)) b! (some wy1))
                ((@ˢTerm.var x!) (Term.var a!)) := by
            exact SMT.RenamingContext.coversFV_update_of_notMem
              (x := b!) (d := wy1) hb!_not_mem_fv_app_lhs
              (hcov_app_at X! wy0)
          have hden_app_b! :
              ⟦((@ˢTerm.var x!) (Term.var a!)).abstract
                  (Function.update (Function.update Δx a! (some wy0)) b! (some wy1))
                  hcov_app_b!⟧ˢ =
                some Dapp := by
            exact
              (SMT.RenamingContext.denote_update_of_notMem
                (x := b!) (d := wy1)
                (h := hcov_app_at X! wy0)
                hb!_not_mem_fv_app_lhs).symm.trans hden_app_lhs
          have hcov_eq_b! :
              RenamingContext.CoversFV
                (Function.update (Function.update Δx a! (some wy0)) b! (some wy1))
                (((@ˢTerm.var x!) (Term.var a!)) =ˢ Term.var b!) := by
            simpa [Δx] using
              funEqBAfterUpdateCovers
                (Δctx := Δctx)
                (x!_ne_a! := x!_ne_a!)
                (x!_ne_b! := x!_ne_b!)
                (a!_ne_b! := a!_ne_b!)
                X! wy0 wy1
          by_cases hEq : wy1.fst = Dapp.fst
          · refine ⟨⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩, ?_, rfl⟩
            have hφ_exists_ab :
                RenamingContext.CoversFV
                  (Function.update (Function.update Δx a! (some wy0)) b! (some wy1))
                  exists_ab := by
              intro v hv
              exact hcov_bBody_upd wy1 v (by
                rw [SMT.fv.eq_def]
                exact List.mem_append.mpr (Or.inr hv))
            have hden_exists_ab_true :
                ⟦exists_ab.abstract
                    (Function.update (Function.update Δx a! (some wy0)) b! (some wy1))
                    hφ_exists_ab⟧ˢ =
                  some ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
              obtain ⟨hcov_xa, y₀, hy₀_ty, hy₀_val, hden_xa⟩ :=
                den_xa_at X! wx₀ rfl hx₀_mem
              have hy₀_mem : y₀.fst ∈ ⟦β⟧ᶻ := by
                rw [← hy₀_ty]
                exact y₀.snd.snd
              let yraw : { y : ZFSet // y ∈ ⟦β⟧ᶻ } :=
                @ᶻX.fst
                  ⟨x₀, by
                    rw [ZFSet.is_func_dom_eq hX_func]
                    exact hx₀_mem⟩
              have hyraw_mem : (yraw : ZFSet) ∈ ⟦β⟧ᶻ := yraw.2
              have hyraw_dom_castβ :
                  (yraw : ZFSet) ∈ castβ.Dom := by
                simpa [ZFSet.is_func_dom_eq hcastβ] using hyraw_mem
              have hcast_yraw_wy1 :
                  ↑(@ᶻcastβ ⟨(yraw : ZFSet), hyraw_dom_castβ⟩) =
                    wy1.fst := by
                have hcast_yraw_wy1_sub :
                    @ᶻcastβ ⟨(yraw : ZFSet), hyraw_dom_castβ⟩ =
                      ⟨wy1.fst, by
                        simpa [hwy1_ty] using wy1.snd.snd⟩ := by
                  calc
                    @ᶻcastβ ⟨(yraw : ZFSet), hyraw_dom_castβ⟩ =
                        @ᶻX!.fst
                          ⟨wy0.fst, by
                            rw [ZFSet.is_func_dom_eq hX!_func]
                            rw [← hwy0_ty]
                            exact wy0.snd.snd⟩ := by
                          exact hX!_app_eq.symm
                    _ = ⟨Dapp.fst, by
                          simpa [hDapp_ty] using Dapp.snd.snd⟩ := by
                          apply Subtype.ext
                          exact hDapp_val.symm
                    _ = ⟨wy1.fst, by
                          simpa [hwy1_ty] using wy1.snd.snd⟩ := by
                          apply Subtype.ext
                          exact hEq.symm
                exact congrArg Subtype.val hcast_yraw_wy1_sub
              have hcast_yraw_wy1_pair :
                  (yraw : ZFSet).pair wy1.fst ∈ castβ := by
                rw [← hcast_yraw_wy1]
                exact ZFSet.fapply.def
                  (ZFSet.is_func_is_pfunc hcastβ)
                  hyraw_dom_castβ
              have hcast_y₀_wy1_pair :
                  y₀.fst.pair wy1.fst ∈ castβ := by
                simpa [yraw, hy₀_val] using hcast_yraw_wy1_pair
              obtain ⟨hφa0, Φa, hden_a0, hΦa_true⟩ :=
                a_spec_true_at X! wx₀ wy0 rfl hwy0_ty hcast_x₀_wy0_pair
              obtain ⟨hφb0, Φb, hden_b0, hΦb_true⟩ :=
                b_spec_true_at X! wy0 y₀ wy1 hy₀_ty hwy1_ty hcast_y₀_wy1_pair
              have hφaX_at :
                  ∀ x₀ : SMT.Dom,
                    RenamingContext.CoversFV
                      (Function.update (Function.update Δx a (some x₀)) a! (some wy0))
                      a!_spec := by
                intro x₀
                exact hφa_at X! x₀ wy0
              have hφbX_at :
                  ∀ y₀ : SMT.Dom,
                    RenamingContext.CoversFV
                      (Function.update
                        (Function.update (Function.update Δx a! (some wy0)) b (some y₀))
                        b! (some wy1))
                      b!_spec := by
                intro y₀
                exact hφb_at X! wy0 y₀ wy1
              exact funExistsABTrueAtRange
                (α' := α') (β' := β')
                (fv_a!_spec := fv_a!_spec)
                (fv_b!_spec := fv_b!_spec)
                (a_not_mem_fv_x := a_not_mem_fv_x)
                (b_not_mem_fv_x := b_not_mem_fv_x)
                (a!_not_mem_fv_x := a!_not_mem_fv_x)
                (b!_not_mem_fv_x := b!_not_mem_fv_x)
                (b_ne_a := b_ne_a)
                (a!_ne_b := a!_ne_b)
                (a_ne_b! := a_ne_b!)
                (b_ne_b! := by
                  intro h
                  exact b!_not_base (h ▸ by
                    rw [AList.mem_insert]
                    exact Or.inl rfl))
                (a_ne_a! := a_ne_a!)
                (a!_ne_b! := a!_ne_b!)
                (hφ_exists_ab := hφ_exists_ab)
                (hφa_at := hφaX_at)
                (hφb_at := hφbX_at)
                (a_spec_total_at := by
                  intro x₀ hx₀_ty
                  simpa [proof_irrel_heq] using
                    a_spec_total_at X! x₀ wy0 hx₀_ty hwy0_ty)
                (b_spec_total_at := by
                  intro y₀ hy₀_ty
                  simpa [proof_irrel_heq] using
                    b_spec_total_at X! wy0 y₀ wy1 hy₀_ty hwy1_ty)
                (den_xa_at := by
                  intro x₀ hx₀_ty hx₀_mem'
                  obtain ⟨hcov_xa', Dxa, hDxa_ty, _, hden_xa'⟩ :=
                    den_xa_at X! x₀ hx₀_ty hx₀_mem'
                  exact ⟨hcov_xa', Dxa, hDxa_ty, hden_xa'⟩)
                (typ_a_ctx := typ_a!_spec_ctx_base)
                (typ_b_ctx := typ_b!_spec_ctx_base)
                (hx₀_ty := rfl)
                (hx₀_mem := hx₀_mem)
                (hy₀_ty := hy₀_ty)
                (hcov_xa := hcov_xa)
                (hden_xa := hden_xa)
                (hφa0 := hφa0)
                (hden_a0 := hden_a0)
                (hΦa_true := hΦa_true)
                (hφb0 := hφb0)
                (hden_b0 := hden_b0)
                (hΦb_true := hΦb_true)
            have hden_eq_true :
                ⟦((@ˢTerm.var x!) (Term.var a!) =ˢ Term.var b!).abstract
                    (Function.update (Function.update Δx a! (some wy0)) b! (some wy1))
                    hcov_eq_b!⟧ˢ =
                  some ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
              as_aux_lemma =>
              rw [SMT.Term.abstract.eq_def]
              have hden_var_b! :
                  ⟦(Term.var b!).abstract
                      (Function.update (Function.update Δx a! (some wy0)) b! (some wy1))
                      (by
                        intro v hv
                        rw [fv, List.mem_singleton] at hv
                        subst hv
                        rw [Function.update_self]
                        rfl)⟧ˢ = some wy1 := by
                rw [SMT.Term.abstract.eq_def, SMT.denote, Option.pure_def, Option.some.injEq]
                apply Option.get_of_eq_some
                exact Function.update_self _ _ _
              exact denote_eq_eq_zftrue_of_fst_eq
                hden_app_b! hden_var_b!
                (by rw [hDapp_ty, hwy1_ty]) hEq.symm
            simpa [bBody, funBBodyTerm, SMT.Term.abstract, proof_irrel_heq] using
              (denote_eq_eq_zftrue_of_fst_eq hden_eq_true hden_exists_ab_true rfl rfl)
          · refine ⟨⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩, ?_, rfl⟩
            have hden_eq_false :
                ⟦((@ˢTerm.var x!) (Term.var a!) =ˢ Term.var b!).abstract
                    (Function.update (Function.update Δx a! (some wy0)) b! (some wy1))
                    hcov_eq_b!⟧ˢ =
                  some ⟨zffalse, SMTType.bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
              as_aux_lemma =>
              rw [SMT.Term.abstract.eq_def]
              have hden_var_b! :
                  ⟦(Term.var b!).abstract
                      (Function.update (Function.update Δx a! (some wy0)) b! (some wy1))
                      (by
                        intro v hv
                        rw [fv, List.mem_singleton] at hv
                        subst hv
                        rw [Function.update_self]
                        rfl)⟧ˢ = some wy1 := by
                rw [SMT.Term.abstract.eq_def, SMT.denote, Option.pure_def, Option.some.injEq]
                apply Option.get_of_eq_some
                exact Function.update_self _ _ _
              exact funDenoteEqFalseOfFstNe
                hden_app_b! hden_var_b!
                (by rw [hDapp_ty, hwy1_ty])
                (by
                  intro h
                  exact hEq h.symm)
            have hφ_exists_ab :
                RenamingContext.CoversFV
                  (Function.update (Function.update Δx a! (some wy0)) b! (some wy1))
                  exists_ab := by
              intro v hv
              exact hcov_bBody_upd wy1 v (by
                rw [SMT.fv.eq_def]
                exact List.mem_append.mpr (Or.inr hv))
            have hφaX_at :
                ∀ x₀ : SMT.Dom,
                  RenamingContext.CoversFV
                    (Function.update (Function.update Δx a (some x₀)) a! (some wy0))
                    a!_spec := by
              intro x₀
              exact hφa_at X! x₀ wy0
            have hφbX_at :
                ∀ y₀ : SMT.Dom,
                  RenamingContext.CoversFV
                    (Function.update
                      (Function.update (Function.update Δx a! (some wy0)) b (some y₀))
                      b! (some wy1))
                    b!_spec := by
              intro y₀
              exact hφb_at X! wy0 y₀ wy1
            have hDapp_from_range :
                Dapp.fst =
                  @ᶻcastβ
                    ⟨↑(@ᶻX.fst
                        ⟨x₀, by
                          simpa [ZFSet.is_func_dom_eq hX_func] using hx₀_mem⟩),
                      by
                        simpa [ZFSet.is_func_dom_eq hcastβ] using
                          (Subtype.property
                            (@ᶻX.fst
                              ⟨x₀, by
                                simpa [ZFSet.is_func_dom_eq hX_func] using hx₀_mem⟩))⟩ := by
              calc
                Dapp.fst =
                    @ᶻX!.fst
                      ⟨wy0.fst, by
                        simpa [ZFSet.is_func_dom_eq hX!_func, hwy0_ty] using wy0.snd.snd⟩ := hDapp_val
                _ =
                    @ᶻcastβ
                      ⟨↑(@ᶻX.fst
                          ⟨x₀, by
                            simpa [ZFSet.is_func_dom_eq hX_func] using hx₀_mem⟩),
                        by
                          simpa [ZFSet.is_func_dom_eq hcastβ] using
                            (Subtype.property
                              (@ᶻX.fst
                                ⟨x₀, by
                                  simpa [ZFSet.is_func_dom_eq hX_func] using hx₀_mem⟩))⟩ := by
                      simpa using hX!_app_eq
            simpa [bBody, exists_ab] using
              (funBBodyTrueOfEqFalseAtRange
                (X! := X!)
                (hφ_eq := hcov_eq_b!)
                (hφ_bBody := by simpa [bBody, exists_ab] using hcov_bBody_upd wy1)
                (hcastα := hcastα)
                (hcastα_inj := hcastα_inj)
                (hcastβ := hcastβ)
                (hX_func := hX_func)
                (fv_a!_spec := fv_a!_spec)
                (fv_b!_spec := fv_b!_spec)
                (a_not_mem_fv_x := a_not_mem_fv_x)
                (b_not_mem_fv_x := b_not_mem_fv_x)
                (a!_not_mem_fv_x := a!_not_mem_fv_x)
                (b!_not_mem_fv_x := b!_not_mem_fv_x)
                (b_ne_a := b_ne_a)
                (a!_ne_b := a!_ne_b)
                (a_ne_b! := a_ne_b!)
                (b_ne_b! := by
                  intro h
                  exact b!_not_base (h ▸ by
                    rw [AList.mem_insert]
                    exact Or.inl rfl))
                (a_ne_a! := a_ne_a!)
                (a!_ne_b! := a!_ne_b!)
                (hφ_exists_ab := hφ_exists_ab)
                (hφa_at := hφaX_at)
                (hφb_at := hφbX_at)
                (a_spec_total_at := by
                  intro x₀ hx₀_ty
                  simpa [proof_irrel_heq] using
                    a_spec_total_at X! x₀ wy0 hx₀_ty hwy0_ty)
                (b_spec_total_at := by
                  intro y₀ hy₀_ty
                  simpa [proof_irrel_heq] using
                    b_spec_total_at X! wy0 y₀ wy1 hy₀_ty hwy1_ty)
                (den_xa_at := by
                  intro x₀ hx₀_ty hx₀_mem'
                  obtain ⟨hcov_xa', Dxa, hDxa_ty, hDxa_val, hden_xa'⟩ :=
                    den_xa_at X! x₀ hx₀_ty hx₀_mem'
                  exact ⟨hcov_xa', Dxa, hDxa_ty, hDxa_val, hden_xa'⟩)
                (a_spec_true_implies_cast := by
                  intro x₀ hx₀_ty hφa Φa hdenΦa htrueΦa
                  exact a_spec_true_implies_cast X! x₀ wy0 hx₀_ty hwy0_ty
                    hφa hdenΦa htrueΦa)
                (b_spec_true_implies_cast := by
                  intro y₀ hy₀_ty hφb Φb hdenΦb htrueΦb
                  exact b_spec_true_implies_cast X! wy0 y₀ wy1 hy₀_ty hwy1_ty
                    hφb hdenΦb htrueΦb)
                (typ_a_ctx := typ_a!_spec_ctx_base)
                (typ_b_ctx := typ_b!_spec_ctx_base)
                (hwy0_ty := hwy0_ty)
                (hwy1_ty := hwy1_ty)
                (x₀r := x₀)
                (hx₀r_mem := hx₀_mem)
                (hcast_x₀r_wy0 := hcast_x₀_wy0)
                (hDapp_from_range := hDapp_from_range)
                (hEq := hEq)
                (hden_eq_false := hden_eq_false))
        refine funUnaryForallEqZftrue
          (Δctx := Function.update Δx a! (some wy0))
          (a := bBody) (v := b!) (τ := β')
          hφ_forall_b hgo_cov_b hcov_bBody_upd
          ?_ ?_ ?_
        · intro wy1 hwy1_ty
          obtain ⟨D, hden_body, _⟩ := hbody_true_b_at wy1 hwy1_ty
          exact Option.isSome_of_eq_some hden_body
        · intro wy1 hwy1_ty D hden_body
          exact denote_type_eq_of_typing
            (typ_t := typ_bBody_base') (hden := hden_body)
        · intro wy1 hwy1_ty
          exact hbody_true_b_at wy1 hwy1_ty
      refine ⟨⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩, ?_, rfl⟩
      dsimp [aBody]
      rw [SMT.Term.abstract, SMT.denote, hden_exists_a_true]
      change
        (if ZFSet.ZFBool.toBool
              ⟨zftrue, ZFSet.ZFBool.zftrue_mem_𝔹⟩ = true then
            ⟦(Term.forall [b!] [β'] bBody).abstract
                (Function.update Δx a! (some wy0))
                hφ_forall_b⟧ˢ
         else
            ⟦hdefault.abstract
                (Function.update Δx a! (some wy0))
                (by
                  intro v hv
                  by_cases hva! : v = a!
                  · subst hva!
                    rw [Function.update_self]
                    rfl
                  · rw [Function.update_of_ne hva!]
                    exact hgo_cov_a v
                      (by
                        dsimp [aBody]
                        exact SMT.fv.mem_ite <| Or.inr <| Or.inr hv)
                      (by simpa [List.mem_singleton] using hva!))⟧ˢ) =
          some ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩
      have htoBool_true :
          ZFSet.ZFBool.toBool
            ⟨zftrue, ZFSet.ZFBool.zftrue_mem_𝔹⟩ = true :=
        ZFSet.ZFBool.toBool_true
      rw [htoBool_true]
      rw [if_pos rfl]
      exact hden_forall_b_true
    · have hφ_exists_a :
        RenamingContext.CoversFV
          (Function.update Δx a! (some wy0)) exists_a := by
        intro v hv
        have hv_remove :
            v ∈ List.removeAll (fv a!_spec) [a] := by
          simpa [exists_a, fv] using hv
        exact funRemoveAllASpecUpdateIsSome
          (fv_a!_spec := fv_a!_spec)
          (ha! := by
            rw [Function.update_self]
            rfl)
          v hv_remove
      have hgo_cov_a_spec :
          ∀ v ∈ fv a!_spec, v ∉ [a] →
            (Function.update Δx a! (some wy0) v).isSome = true := by
        intro v hv hv_not_a
        have hv_remove : v ∈ List.removeAll (fv a!_spec) [a] := by
          exact List.mem_removeAll_iff.mpr ⟨hv, hv_not_a⟩
        exact funRemoveAllASpecUpdateIsSome
          (fv_a!_spec := fv_a!_spec)
          (ha! := by
            rw [Function.update_self]
            rfl)
          v hv_remove
      have hctx_swap :
          ∀ x₀ : SMT.Dom,
            Function.update (Function.update Δx a! (some wy0)) a (some x₀) =
              Function.update
                (Function.update (Function.update Δctx x! (some X!)) a (some x₀))
                a! (some wy0) := by
        intro x₀
        simpa [Δx] using
          funUpdateSwap
            (Δctx := Function.update Δctx x! (some X!))
            (a_ne_a! := a_ne_a!)
            x₀ wy0
      have hcov_a_spec_upd :
          ∀ x₀ : SMT.Dom,
            RenamingContext.CoversFV
              (Function.update (Function.update Δx a! (some wy0)) a (some x₀))
              a!_spec := by
        intro x₀ v hv
        rw [hctx_swap x₀]
        exact hφa_at X! x₀ wy0 v hv
      have typ_a!_spec_swap :
          AList.insert a α (AList.insert a! α' (AList.insert x! (α'.fun β') Γ)) ⊢ˢ
            a!_spec : SMTType.bool := by
        exact SMT.Typing.weakening
          (h := typeContext_insert_swap_entries a_ne_a!.symm)
          typ_a!_spec_ctx_base
      have hden_exists_a_false :
          ⟦exists_a.abstract (Function.update Δx a! (some wy0)) hφ_exists_a⟧ˢ =
            some ⟨zffalse, SMTType.bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
        apply funUnaryExistsEqZffalseOfTrueImpliesRange
          (Δctx := Function.update Δx a! (some wy0))
          (τ' := α') (cast := castα) (target := wy0)
          hcastα
          (a := a!_spec) (v := a) (τ := α)
          hφ_exists_a hgo_cov_a_spec hcov_a_spec_upd
        · intro x₀ hx₀_ty
          simpa [hctx_swap x₀, proof_irrel_heq] using
            a_spec_total_at X! x₀ wy0 hx₀_ty hwy0_ty
        · intro x₀ hx₀_ty D hden_a
          exact denote_type_eq_of_typing
            (typ_t := typ_a!_spec_swap) (hden := hden_a)
        · intro x₀ hx₀_ty D hden_a hDa_true
          have hφa :
              RenamingContext.CoversFV
                (Function.update
                  (Function.update (Function.update Δctx x! (some X!)) a (some x₀))
                  a! (some wy0))
                a!_spec := hφa_at X! x₀ wy0
          exact a_spec_true_implies_cast X! x₀ wy0 hx₀_ty hwy0_ty
            hφa
            (by simpa [hctx_swap x₀, proof_irrel_heq] using hden_a)
            hDa_true
        · exact hy_ran
      obtain ⟨Dapp, hDapp_ty, hDapp_val, hden_app⟩ :=
        den_app_at X! wy0 hX!_ty hX!_func hwy0_ty
      have hDapp_default : Dapp.fst = β'.defaultZFSet := by
        rw [hDapp_val]
        exact hX!_app_default wy0 hwy0_ty hy_ran
      obtain ⟨hφd, Φd, hdenΦd, _, hΦd_true_if⟩ :=
        default_spec_at X! wy0 Dapp hden_app
      have hΦd_true : Φd.fst = zftrue := by
        exact hΦd_true_if hDapp_default
      have hφ_forall_b :
          RenamingContext.CoversFV
            (Function.update Δx a! (some wy0))
            (Term.forall [b!] [β'] bBody) := by
        intro v hv
        have hv_forall_b :
            v ∈ fv (Term.forall [b!] [β'] bBody) := hv
        by_cases hva! : v = a!
        · subst hva!
          rw [Function.update_self]
          rfl
        · rw [Function.update_of_ne hva!]
          exact hgo_cov_a v
            (by
              dsimp [aBody]
              exact SMT.fv.mem_ite <| Or.inr <| Or.inl hv_forall_b)
            (by simpa [List.mem_singleton] using hva!)
      refine ⟨Φd, ?_, hΦd_true⟩
      dsimp [aBody]
      rw [SMT.Term.abstract, SMT.denote, hden_exists_a_false]
      change
        (if ZFSet.ZFBool.toBool
              ⟨zffalse, ZFSet.ZFBool.zffalse_mem_𝔹⟩ = true then
            ⟦(Term.forall [b!] [β'] bBody).abstract
                (Function.update Δx a! (some wy0))
                hφ_forall_b⟧ˢ
         else
            ⟦hdefault.abstract
                (Function.update Δx a! (some wy0))
                hφd⟧ˢ) =
          some Φd
      have htoBool_false :
          ZFSet.ZFBool.toBool
            ⟨zffalse, ZFSet.ZFBool.zffalse_mem_𝔹⟩ = false := by
        exact ZFSet.ZFBool.toBool_false
      rw [htoBool_false]
      rw [if_neg (by decide)]
      exact hdenΦd
  refine ⟨⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩, ?_, rfl, rfl⟩
  apply funUnaryForallEqZftrue
    (Δctx := Δx) (a := aBody) (v := a!) (τ := α')
    (hφ_forall := hφX!)
    (hgo_cov := hgo_cov_a)
    (hcov_a_upd := hcov_aBody_upd)
  · intro wy0 hwy0_ty
    obtain ⟨D, hden_body, _⟩ := hbody_true_at wy0 hwy0_ty
    exact Option.isSome_of_eq_some hden_body
  · intro wy0 hwy0_ty D hden_body
    exact denote_type_eq_of_typing (typ_t := typ_aBody_base) (hden := hden_body)
  · intro wy0 hwy0_ty
    exact hbody_true_at wy0 hwy0_ty

set_option maxHeartbeats 1000000 in
theorem funSpecTrueImpliesCastAt.{u}
    {α β α' β' : SMTType}
    (hβ : β ≠ SMTType.bool)
    {pα : α ⇝ α'} {pβ : β ⇝ β'}
    {x a!_spec b!_spec hdefault : Term}
    {x! a a! b b! : 𝒱}
    {Γ : TypeContext}
    {Δctx : RenamingContext.Context.{u}}
    {X X! Y ΦY : SMT.Dom.{u}}
    (hY_ty : Y.snd.fst = α'.fun β')
    (hX!_ty : X!.snd.fst = α'.fun β')
    (typ_fun_spec_base :
      AList.insert x! (α'.fun β') Γ ⊢ˢ
        funSpecTerm x x! a a! b b! α β α' β' a!_spec b!_spec hdefault : SMTType.bool)
    (typ_a!_spec_ctx_base :
      AList.insert a! α' (AList.insert a α (AList.insert x! (α'.fun β') Γ)) ⊢ˢ
        a!_spec : SMTType.bool)
    (typ_b!_spec_ctx_base :
      AList.insert b! β'
        (AList.insert b β
          (AList.insert a! α' (AList.insert a α (AList.insert x! (α'.fun β') Γ)))) ⊢ˢ
        b!_spec : SMTType.bool)
    (fv_a!_spec : fv a!_spec ⊆ fv (Term.var a) ∪ {a!})
    (fv_b!_spec : fv b!_spec ⊆ fv (Term.var b) ∪ {b!})
    (castα castβ : ZFSet)
    (hcastα : ZFSet.IsFunc ⟦α⟧ᶻ ⟦α'⟧ᶻ castα)
    (hcastβ : ZFSet.IsFunc ⟦β⟧ᶻ ⟦β'⟧ᶻ castβ)
    (hcastα_eq : castα = (castZF_of_path pα).1)
    (hcastβ_eq : castβ = (castZF_of_path pβ).1)
    (hX_func : ZFSet.IsFunc ⟦α⟧ᶻ ⟦β⟧ᶻ X.fst)
    (hcast_mem :
      X.fst.pair X!.fst ∈ (castZF_of_path (castPath.fun hβ pα pβ)).1)
    (hX!_func : ZFSet.IsFunc ⟦α'⟧ᶻ ⟦β'⟧ᶻ X!.fst)
    (hX!_app_default :
      ∀ (wy0 : SMT.Dom.{u}) (hwy0_ty : wy0.snd.fst = α')
        (hy_not_ran : wy0.fst ∉ castα.Range),
        ZFSet.fapply X!.fst (ZFSet.is_func_is_pfunc hX!_func)
          ⟨wy0.fst, by
            simpa [ZFSet.is_func_dom_eq hX!_func, hwy0_ty] using wy0.snd.snd⟩ =
          β'.defaultZFSet)
    (hX!_app_range :
      ∀ (wy0 : SMT.Dom.{u}) (hwy0_ty : wy0.snd.fst = α')
        (hy_ran : wy0.fst ∈ castα.Range),
        ∃ (x₀ : ZFSet) (hx₀_mem : x₀ ∈ ⟦α⟧ᶻ),
          @ᶻcastα
            ⟨x₀, by
              rw [ZFSet.is_func_dom_eq hcastα]
              exact hx₀_mem⟩ = wy0.fst ∧
          ZFSet.fapply X!.fst (ZFSet.is_func_is_pfunc hX!_func)
            ⟨wy0.fst, by
              simpa [ZFSet.is_func_dom_eq hX!_func, hwy0_ty] using wy0.snd.snd⟩ =
            @ᶻcastβ
              ⟨@ᶻX.fst
                  ⟨x₀, by
                    simpa [ZFSet.is_func_dom_eq hX_func] using hx₀_mem⟩, by
                    rw [ZFSet.is_func_dom_eq hcastβ]
                    exact Subtype.property _⟩)
    (x!_ne_a! : x! ≠ a!)
    (x!_ne_b! : x! ≠ b!)
    (a_ne_a! : a ≠ a!)
    (b_not_base :
      b ∉ AList.insert a! α' (AList.insert a α (AList.insert x! (α'.fun β') Γ)))
    (b!_not_base :
      b! ∉ AList.insert b β
        (AList.insert a! α' (AList.insert a α (AList.insert x! (α'.fun β') Γ))))
    (a_not_mem_fv_x : a ∉ fv x)
    (b_not_mem_fv_x : b ∉ fv x)
    (a!_not_mem_fv_x : a! ∉ fv x)
    (b!_not_mem_fv_x : b! ∉ fv x)
    (den_xa_at :
      ∀ (Yfun x₀ : SMT.Dom.{u}) (hx₀_ty : x₀.snd.fst = α)
        (hx₀_mem : x₀.fst ∈ ⟦α⟧ᶻ),
        ∃ hcov_app :
          RenamingContext.CoversFV
            (Function.update (Function.update Δctx x! (some Yfun)) a (some x₀))
            ((@ˢx) (Term.var a)),
          ∃ Dapp : SMT.Dom.{u},
            Dapp.snd.fst = β ∧
              Dapp.fst =
                @ᶻX.fst
                  ⟨x₀.fst, by
                    simpa [ZFSet.is_func_dom_eq hX_func] using hx₀_mem⟩ ∧
              ⟦((@ˢx) (Term.var a)).abstract
                  (Function.update (Function.update Δctx x! (some Yfun)) a (some x₀))
                  hcov_app⟧ˢ =
                some Dapp)
    (hφa_at :
      ∀ (Yfun x₀ wy0 : SMT.Dom.{u}),
        RenamingContext.CoversFV
          (Function.update
            (Function.update (Function.update Δctx x! (some Yfun)) a (some x₀))
            a! (some wy0))
          a!_spec)
    (hφb_at :
      ∀ (Yfun wy0 y₀ wy1 : SMT.Dom.{u}),
        RenamingContext.CoversFV
          (Function.update
            (Function.update
              (Function.update (Function.update Δctx x! (some Yfun)) a! (some wy0))
              b (some y₀))
            b! (some wy1))
          b!_spec)
    (a_spec_total_at :
      ∀ (Yfun x₀ wy0 : SMT.Dom.{u})
        (hx₀_ty : x₀.snd.fst = α)
        (hwy0_ty : wy0.snd.fst = α'),
        ⟦a!_spec.abstract
            (Function.update
              (Function.update (Function.update Δctx x! (some Yfun)) a (some x₀))
              a! (some wy0))
            (hφa_at Yfun x₀ wy0)⟧ˢ.isSome =
          true)
    (b_spec_total_at :
      ∀ (Yfun wy0 y₀ wy1 : SMT.Dom.{u})
        (hy₀_ty : y₀.snd.fst = β)
        (hwy1_ty : wy1.snd.fst = β'),
        ⟦b!_spec.abstract
            (Function.update
              (Function.update
                (Function.update (Function.update Δctx x! (some Yfun)) a! (some wy0))
                b (some y₀))
              b! (some wy1))
            (hφb_at Yfun wy0 y₀ wy1)⟧ˢ.isSome =
          true)
    (a_spec_true_at :
      ∀ (Yfun x₀ wy0 : SMT.Dom.{u})
        (hx₀_ty : x₀.snd.fst = α)
        (hwy0_ty : wy0.snd.fst = α')
        (hcast_x₀w : x₀.fst.pair wy0.fst ∈ ↑(castZF_of_path pα).1),
        ∃ (hφa :
          RenamingContext.CoversFV
            (Function.update
              (Function.update (Function.update Δctx x! (some Yfun)) a (some x₀))
              a! (some wy0))
            a!_spec)
          (Φa : SMT.Dom.{u}),
          ⟦a!_spec.abstract
              (Function.update
                (Function.update (Function.update Δctx x! (some Yfun)) a (some x₀))
                a! (some wy0))
              hφa⟧ˢ =
            some Φa ∧
          Φa.fst = zftrue)
    (b_spec_true_at :
      ∀ (Yfun wy0 y₀ wy1 : SMT.Dom.{u})
        (hy₀_ty : y₀.snd.fst = β)
        (hwy1_ty : wy1.snd.fst = β')
        (hcast_y₀w : y₀.fst.pair wy1.fst ∈ ↑(castZF_of_path pβ).1),
        ∃ (hφb :
          RenamingContext.CoversFV
            (Function.update
              (Function.update
                (Function.update (Function.update Δctx x! (some Yfun)) a! (some wy0))
                b (some y₀))
              b! (some wy1))
            b!_spec)
          (Φb : SMT.Dom.{u}),
          ⟦b!_spec.abstract
              (Function.update
                (Function.update
                  (Function.update (Function.update Δctx x! (some Yfun)) a! (some wy0))
                  b (some y₀))
                b! (some wy1))
              hφb⟧ˢ =
            some Φb ∧
          Φb.fst = zftrue)
    (a_spec_true_implies_cast :
      ∀ (Yfun x₀ wy0 : SMT.Dom.{u})
        (hx₀_ty : x₀.snd.fst = α)
        (hwy0_ty : wy0.snd.fst = α')
        (hφa :
          RenamingContext.CoversFV
            (Function.update
              (Function.update (Function.update Δctx x! (some Yfun)) a (some x₀))
              a! (some wy0))
            a!_spec)
        {Φa : SMT.Dom.{u}},
        ⟦a!_spec.abstract
            (Function.update
              (Function.update (Function.update Δctx x! (some Yfun)) a (some x₀))
              a! (some wy0))
            hφa⟧ˢ =
          some Φa →
        Φa.fst = zftrue →
        x₀.fst.pair wy0.fst ∈ ↑(castZF_of_path pα).1)
    (b_spec_true_implies_cast :
      ∀ (Yfun wy0 y₀ wy1 : SMT.Dom.{u})
        (hy₀_ty : y₀.snd.fst = β)
        (hwy1_ty : wy1.snd.fst = β')
        (hφb :
          RenamingContext.CoversFV
            (Function.update
              (Function.update
                (Function.update (Function.update Δctx x! (some Yfun)) a! (some wy0))
                b (some y₀))
              b! (some wy1))
            b!_spec)
        {Φb : SMT.Dom.{u}},
        ⟦b!_spec.abstract
            (Function.update
              (Function.update
                (Function.update (Function.update Δctx x! (some Yfun)) a! (some wy0))
                b (some y₀))
              b! (some wy1))
            hφb⟧ˢ =
          some Φb →
        Φb.fst = zftrue →
        y₀.fst.pair wy1.fst ∈ ↑(castZF_of_path pβ).1)
    (den_app_at :
      ∀ (Yfun wy0 : SMT.Dom.{u})
        (hYfun_ty : Yfun.snd.fst = α'.fun β')
        (hYfun_func : ZFSet.IsFunc ⟦α'⟧ᶻ ⟦β'⟧ᶻ Yfun.fst)
        (hwy0_ty : wy0.snd.fst = α'),
        ∃ Dapp : SMT.Dom.{u},
          Dapp.snd.fst = β' ∧
            Dapp.fst =
              @ᶻYfun.fst
                ⟨wy0.fst, by
                  simpa [ZFSet.is_func_dom_eq hYfun_func, hwy0_ty] using wy0.snd.snd⟩ ∧
            ⟦((@ˢTerm.var x!) (Term.var a!)).abstract
                (Function.update (Function.update Δctx x! (some Yfun)) a! (some wy0))
                (by
                  intro v hv
                  simp only [fv, List.mem_append, List.mem_singleton] at hv
                  rcases hv with hv | hv
                  · subst hv
                    rw [Function.update_of_ne x!_ne_a!]
                    rw [Function.update_self]
                    rfl
                  · subst hv
                    rw [Function.update_self]
                    rfl)⟧ˢ =
              some Dapp)
    (default_spec_at :
      ∀ (Yfun wy0 Dapp : SMT.Dom.{u})
        (hden_app :
          ⟦((@ˢTerm.var x!) (Term.var a!)).abstract
              (Function.update (Function.update Δctx x! (some Yfun)) a! (some wy0))
              (by
                intro v hv
                simp only [fv, List.mem_append, List.mem_singleton] at hv
                rcases hv with hv | hv
                · subst hv
                  rw [Function.update_of_ne x!_ne_a!]
                  rw [Function.update_self]
                  rfl
                · subst hv
                  rw [Function.update_self]
                  rfl)⟧ˢ =
            some Dapp),
        ∃ (hφd :
          RenamingContext.CoversFV
            (Function.update (Function.update Δctx x! (some Yfun)) a! (some wy0))
            hdefault)
          (Φd : SMT.Dom.{u}),
          ⟦hdefault.abstract
              (Function.update (Function.update Δctx x! (some Yfun)) a! (some wy0))
              hφd⟧ˢ =
            some Φd ∧
          Φd.snd.fst = SMTType.bool ∧
          (Dapp.fst = β'.defaultZFSet → Φd.fst = zftrue))
    (default_true_implies_default_at :
      ∀ (Yfun wy0 Dapp : SMT.Dom.{u})
        (hden_app :
          ⟦((@ˢTerm.var x!) (Term.var a!)).abstract
              (Function.update (Function.update Δctx x! (some Yfun)) a! (some wy0))
              (by
                intro v hv
                simp only [fv, List.mem_append, List.mem_singleton] at hv
                rcases hv with hv | hv
                · subst hv
                  rw [Function.update_of_ne x!_ne_a!]
                  rw [Function.update_self]
                  rfl
                · subst hv
                  rw [Function.update_self]
                  rfl)⟧ˢ =
            some Dapp)
        (hφd :
          RenamingContext.CoversFV
            (Function.update (Function.update Δctx x! (some Yfun)) a! (some wy0))
            hdefault)
        {Φd : SMT.Dom.{u}},
        ⟦hdefault.abstract
            (Function.update (Function.update Δctx x! (some Yfun)) a! (some wy0))
            hφd⟧ˢ =
          some Φd →
        Φd.fst = zftrue →
        Dapp.fst = β'.defaultZFSet)
    (hφY :
      RenamingContext.CoversFV
        (Function.update Δctx x! (some Y))
        (funSpecTerm x x! a a! b b! α β α' β' a!_spec b!_spec hdefault))
    (hdenΦY :
      ⟦(funSpecTerm x x! a a! b b! α β α' β' a!_spec b!_spec hdefault).abstract
          (Function.update Δctx x! (some Y))
          hφY⟧ˢ =
        some ΦY)
    (htrue : ΦY.fst = zftrue) :
    X.fst.pair Y.fst ∈ (castZF_of_path (castPath.fun hβ pα pβ)).1 := by
  let exists_a : Term := .exists [a] [α] a!_spec
  let exists_ab : Term := funExistsABTerm x a!_spec b!_spec a b α β
  let bBody : Term := funBBodyTerm x! a! b! exists_ab
  let aBody : Term := (.ite exists_a (.forall [b!] [β'] bBody) hdefault)
  let ΔY : RenamingContext.Context := Function.update Δctx x! (some Y)
  have hY_mem : Y.fst ∈ ⟦α'.fun β'⟧ᶻ := by
    rw [← hY_ty]
    exact Y.snd.snd
  have hY_func : ZFSet.IsFunc ⟦α'⟧ᶻ ⟦β'⟧ᶻ Y.fst := by
    rw [ZFSet.mem_funs] at hY_mem
    exact hY_mem
  have typ_fun_spec_base' := typ_fun_spec_base
  change
    (AList.insert x! (α'.fun β') Γ) ⊢ˢ
      (.forall [a!] [α'] aBody) : SMTType.bool at typ_fun_spec_base'
  obtain ⟨_, _, _, _, _, typ_aBody_base⟩ :=
    SMT.Typing.forallE typ_fun_spec_base'
  obtain ⟨typ_exists_a_base, typ_forall_b_base, _⟩ :=
    SMT.Typing.iteE typ_aBody_base
  have hgo_cov_aY :
      ∀ v ∈ fv aBody, v ∉ [a!] → (ΔY v).isSome = true := by
    intro v hv hnot
    have hv' :
        v ∈ fv (funSpecTerm x x! a a! b b! α β α' β' a!_spec b!_spec hdefault) := by
      change v ∈ fv (Term.forall [a!] [α'] aBody)
      rw [fv]
      exact List.mem_removeAll_iff.mpr ⟨hv, hnot⟩
    exact hφY v hv'
  have hcov_aBody_updY :
      ∀ wy0 : SMT.Dom,
        RenamingContext.CoversFV (Function.update ΔY a! (some wy0)) aBody := by
    intro wy0 v hv
    by_cases hva! : v = a!
    · subst hva!
      rw [Function.update_self]
      rfl
    · rw [Function.update_of_ne hva!]
      exact hgo_cov_aY v hv (by simpa [List.mem_singleton] using hva!)
  have hupdate_forall_a_base :
      SMT.TypeContext.update
        (AList.insert x! (α'.fun β') Γ) [a!] [α'] rfl =
        AList.insert a! α' (AList.insert x! (α'.fun β') Γ) := by
    simp only [SMT.TypeContext.update, List.length_cons, List.length_nil, zero_add,
      Fin.cast_eq_self, Fin.getElem_fin, Fin.foldl_succ_last, Fin.coe_ofNat_eq_mod,
      Nat.mod_succ, List.getElem_cons_zero, Fin.last_zero, Fin.isValue,
      Fin.foldl_zero]
  have typ_forall_b_base' :
      AList.insert a! α' (AList.insert x! (α'.fun β') Γ) ⊢ˢ
        (.forall [b!] [β'] bBody) : SMTType.bool := by
    rw [hupdate_forall_a_base] at typ_forall_b_base
    exact typ_forall_b_base
  obtain ⟨_, _, _, _, _, typ_bBody_base⟩ :=
    SMT.Typing.forallE typ_forall_b_base'
  have hφ_exists_a_at :
      ∀ wy0 : SMT.Dom,
        RenamingContext.CoversFV
          (Function.update ΔY a! (some wy0))
          exists_a := by
    intro wy0 v hv
    have hv_remove :
        v ∈ List.removeAll (fv a!_spec) [a] := by
      simpa [exists_a, fv] using hv
    exact funRemoveAllASpecUpdateIsSome
      (fv_a!_spec := fv_a!_spec)
      (ha! := by
        rw [Function.update_self]
        rfl)
      v hv_remove
  have hgo_cov_a_spec_at :
      ∀ wy0 : SMT.Dom,
        ∀ v ∈ fv a!_spec, v ∉ [a] →
          (Function.update ΔY a! (some wy0) v).isSome = true := by
    intro wy0 v hv hv_not_a
    have hv_remove : v ∈ List.removeAll (fv a!_spec) [a] := by
      exact List.mem_removeAll_iff.mpr ⟨hv, hv_not_a⟩
    exact funRemoveAllASpecUpdateIsSome
      (fv_a!_spec := fv_a!_spec)
      (ha! := by
        rw [Function.update_self]
        rfl)
      v hv_remove
  have hctx_swap_at :
      ∀ wy0 x₀ : SMT.Dom,
        Function.update (Function.update ΔY a! (some wy0)) a (some x₀) =
          Function.update
            (Function.update (Function.update Δctx x! (some Y)) a (some x₀))
            a! (some wy0) := by
    intro wy0 x₀
    simpa [ΔY] using
      funUpdateSwap
        (Δctx := Function.update Δctx x! (some Y))
        (a_ne_a! := a_ne_a!)
        x₀ wy0
  have hcov_a_spec_upd_at :
      ∀ wy0 x₀ : SMT.Dom,
        RenamingContext.CoversFV
          (Function.update (Function.update ΔY a! (some wy0)) a (some x₀))
          a!_spec := by
    intro wy0 x₀ v hv
    rw [hctx_swap_at wy0 x₀]
    exact hφa_at Y x₀ wy0 v hv
  have typ_a!_spec_swap :
      AList.insert a α (AList.insert a! α' (AList.insert x! (α'.fun β') Γ)) ⊢ˢ
        a!_spec : SMTType.bool := by
    exact SMT.Typing.weakening
      (h := typeContext_insert_swap_entries a_ne_a!.symm)
      typ_a!_spec_ctx_base
  have hφ_forall_b_at :
      ∀ wy0 : SMT.Dom,
        RenamingContext.CoversFV
          (Function.update ΔY a! (some wy0))
          (Term.forall [b!] [β'] bBody) := by
    intro wy0 v hv
    by_cases hva! : v = a!
    · subst hva!
      rw [Function.update_self]
      rfl
    · rw [Function.update_of_ne hva!]
      exact hgo_cov_aY v
        (by
          dsimp [aBody]
          exact SMT.fv.mem_ite <| Or.inr <| Or.inl hv)
        (by simpa [List.mem_singleton] using hva!)
  have hupdate_forall_b_base :
      SMT.TypeContext.update
        (AList.insert a! α' (AList.insert x! (α'.fun β') Γ))
        [b!] [β'] rfl =
        AList.insert b! β' (AList.insert a! α' (AList.insert x! (α'.fun β') Γ)) := by
    unfold SMT.TypeContext.update
    simp only [List.length_cons, List.length_nil, zero_add,
      Fin.foldl_succ_last, Fin.getElem_fin, Fin.coe_cast,
      Fin.val_last, List.getElem_cons_zero, Fin.coe_castSucc,
      Fin.foldl_zero]
  have typ_bBody_base' :
      AList.insert b! β' (AList.insert a! α' (AList.insert x! (α'.fun β') Γ)) ⊢ˢ
        bBody : SMTType.bool := by
    rw [← hupdate_forall_b_base]
    exact typ_bBody_base
  have hgo_cov_b_at :
      ∀ wy0 : SMT.Dom,
        ∀ v ∈ fv bBody, v ∉ [b!] →
          (Function.update ΔY a! (some wy0) v).isSome = true := by
    intro wy0 v hv hv_not_b!
    have hv_forall_b :
        v ∈ fv (Term.forall [b!] [β'] bBody) := by
      rw [fv]
      exact List.mem_removeAll_iff.mpr ⟨hv, hv_not_b!⟩
    by_cases hva! : v = a!
    · subst hva!
      rw [Function.update_self]
      rfl
    · rw [Function.update_of_ne hva!]
      exact hgo_cov_aY v
        (by
          dsimp [aBody]
          exact SMT.fv.mem_ite <| Or.inr <| Or.inl hv_forall_b)
        (by simpa [List.mem_singleton] using hva!)
  have hcov_bBody_upd_at :
      ∀ wy0 wy1 : SMT.Dom,
        RenamingContext.CoversFV
          (Function.update (Function.update ΔY a! (some wy0)) b! (some wy1))
          bBody := by
    intro wy0 wy1 v hv
    by_cases hvb! : v = b!
    · subst hvb!
      rw [Function.update_self]
      rfl
    · rw [Function.update_of_ne hvb!]
      exact hgo_cov_b_at wy0 v hv (by simpa [List.mem_singleton] using hvb!)
  have b_ne_a : b ≠ a := by
    intro h
    subst h
    exact b_not_base (by
      rw [AList.mem_insert]
      exact Or.inr (by
        rw [AList.mem_insert]
        exact Or.inl rfl))
  have a!_ne_b : a! ≠ b := by
    intro h
    exact b_not_base (h ▸ by
      rw [AList.mem_insert]
      exact Or.inl rfl)
  have a_ne_b! : a ≠ b! := by
    intro hab!
    exact b!_not_base (hab! ▸ by
      rw [AList.mem_insert]
      exact Or.inr (by
        rw [AList.mem_insert]
        exact Or.inr (by
          rw [AList.mem_insert]
          exact Or.inl rfl)))
  have a!_ne_b! : a! ≠ b! := by
    intro ha!b!
    exact b!_not_base (ha!b! ▸ by
      rw [AList.mem_insert]
      exact Or.inr (by
        rw [AList.mem_insert]
        exact Or.inl rfl))
  have hexists_ab_total_at :
      ∀ wy0 wy1 : SMT.Dom,
        wy0.snd.fst = α' →
          wy1.snd.fst = β' →
            ⟦exists_ab.abstract
                (Function.update (Function.update ΔY a! (some wy0)) b! (some wy1))
                (by
                  intro v hv
                  exact hcov_bBody_upd_at wy0 wy1 v (by
                    rw [SMT.fv.eq_def]
                    exact List.mem_append.mpr (Or.inr hv)))⟧ˢ.isSome =
              true := by
    intro wy0 wy1 hwy0_ty hwy1_ty
    exact funExistsABTotalAt
      (fv_a!_spec := fv_a!_spec)
      (fv_b!_spec := fv_b!_spec)
      (a_not_mem_fv_x := a_not_mem_fv_x)
      (b_not_mem_fv_x := b_not_mem_fv_x)
      (a!_not_mem_fv_x := a!_not_mem_fv_x)
      (b!_not_mem_fv_x := b!_not_mem_fv_x)
      (b_ne_a := b_ne_a)
      (a!_ne_b := a!_ne_b)
      (a_ne_b! := a_ne_b!)
      (b_ne_b! := by
        intro h
        exact b!_not_base (h ▸ by
          rw [AList.mem_insert]
          exact Or.inl rfl))
      (a_ne_a! := a_ne_a!)
      (a!_ne_b! := a!_ne_b!)
      (hφ_exists_ab := by
        intro v hv
        exact hcov_bBody_upd_at wy0 wy1 v (by
          rw [SMT.fv.eq_def]
          exact List.mem_append.mpr (Or.inr hv)))
      (hφa_at := by
        intro x₀
        exact hφa_at Y x₀ wy0)
      (hφb_at := by
        intro y₀
        exact hφb_at Y wy0 y₀ wy1)
      (a_spec_total_at := by
        intro x₀ hx₀_ty
        simpa [proof_irrel_heq] using
          a_spec_total_at Y x₀ wy0 hx₀_ty hwy0_ty)
      (b_spec_total_at := by
        intro y₀ hy₀_ty
        simpa [proof_irrel_heq] using
          b_spec_total_at Y wy0 y₀ wy1 hy₀_ty hwy1_ty)
      (den_xa_at := by
        intro x₀ hx₀_ty hx₀_mem
        obtain ⟨hcov_xa, Dxa, hDxa_ty, _, hden_xa⟩ :=
          den_xa_at Y x₀ hx₀_ty hx₀_mem
        exact ⟨hcov_xa, Dxa, hDxa_ty, hden_xa⟩)
      (typ_a_ctx := typ_a!_spec_ctx_base)
      (typ_b_ctx := typ_b!_spec_ctx_base)
  have hbody_ty_b_at :
      ∀ wy0 wy1 : SMT.Dom,
        wy0.snd.fst = α' →
          wy1.snd.fst = β' →
            ∀ {D : SMT.Dom},
              ⟦bBody.abstract
                  (Function.update (Function.update ΔY a! (some wy0)) b! (some wy1))
                  (hcov_bBody_upd_at wy0 wy1)⟧ˢ =
                some D →
                D.snd.fst = SMTType.bool := by
    intro wy0 wy1 hwy0_ty hwy1_ty D hden_body
    exact denote_type_eq_of_typing (typ_t := typ_bBody_base') (hden := hden_body)
  have hbody_total_b_at :
      ∀ wy0 wy1 : SMT.Dom,
        wy0.snd.fst = α' →
          wy1.snd.fst = β' →
            ⟦bBody.abstract
                (Function.update (Function.update ΔY a! (some wy0)) b! (some wy1))
                (hcov_bBody_upd_at wy0 wy1)⟧ˢ.isSome =
              true := by
    as_aux_lemma =>
    intro wy0 wy1 hwy0_ty hwy1_ty
    obtain ⟨Dapp, hDapp_ty, _, hden_app⟩ :=
      den_app_at Y wy0 hY_ty hY_func hwy0_ty
    have hden_var_b! :
        ⟦(Term.var b!).abstract
            (Function.update (Function.update ΔY a! (some wy0)) b! (some wy1))
            (by
              intro v hv
              rw [fv, List.mem_singleton] at hv
              subst hv
              rw [Function.update_self]
              rfl)⟧ˢ = some wy1 := by
      rw [SMT.Term.abstract.eq_def, SMT.denote, Option.pure_def, Option.some.injEq]
      apply Option.get_of_eq_some
      exact Function.update_self _ _ _
    have hcov_appY :
        RenamingContext.CoversFV
          (Function.update (Function.update Δctx x! (some Y)) a! (some wy0))
          ((@ˢTerm.var x!) (Term.var a!)) := by
      intro v hv
      rw [fv, List.mem_append] at hv
      rcases hv with hv | hv
      · rw [fv, List.mem_singleton] at hv
        subst hv
        rw [Function.update_of_ne x!_ne_a!]
        rw [Function.update_self]
        rfl
      · rw [fv, List.mem_singleton] at hv
        subst hv
        rw [Function.update_self]
        rfl
    have hb!_not_mem_fv_app :
        b! ∉ fv ((@ˢTerm.var x!) (Term.var a!)) := by
      intro hv
      rw [fv, List.mem_append] at hv
      rcases hv with hv | hv
      · rw [fv, List.mem_singleton] at hv
        exact x!_ne_b! hv.symm
      · rw [fv, List.mem_singleton] at hv
        exact a!_ne_b! hv.symm
    have hcov_app' :
        RenamingContext.CoversFV
          (Function.update (Function.update ΔY a! (some wy0)) b! (some wy1))
          ((@ˢTerm.var x!) (Term.var a!)) := by
      simpa [ΔY] using
        SMT.RenamingContext.coversFV_update_of_notMem
          (x := b!) (d := wy1) hb!_not_mem_fv_app hcov_appY
    have hden_app' :
        ⟦((@ˢTerm.var x!) (Term.var a!)).abstract
            (Function.update (Function.update ΔY a! (some wy0)) b! (some wy1))
            hcov_app'⟧ˢ =
          some Dapp := by
      simpa [ΔY] using
        (SMT.RenamingContext.denote_update_of_notMem
          (x := b!) (d := wy1)
          (h := hcov_appY)
          hb!_not_mem_fv_app).symm.trans hden_app
    obtain ⟨Deq, hden_eq, hDeq_ty⟩ :=
      denote_eq_some_of_some
        hden_app'
        hden_var_b!
        (by rw [hDapp_ty, hwy1_ty])
    obtain ⟨Dexists, hden_exists⟩ :=
      Option.isSome_iff_exists.mp (hexists_ab_total_at wy0 wy1 hwy0_ty hwy1_ty)
    have typ_bBody_eq := SMT.Typing.eqE typ_bBody_base'
    obtain ⟨_, σ, typ_eq_ctx, typ_exists_ab_ctx⟩ := typ_bBody_eq
    have hσ_bool : σ = SMTType.bool := by
      obtain ⟨hσ_bool, _, _, _⟩ := SMT.Typing.eqE typ_eq_ctx
      exact hσ_bool
    have hDexists_ty : Dexists.snd.fst = SMTType.bool := by
      cases hσ_bool
      exact denote_type_eq_of_typing (typ_t := typ_exists_ab_ctx) (hden := hden_exists)
    obtain ⟨Dout, hden_out, _⟩ :=
      denote_eq_some_of_some hden_eq hden_exists (by rw [hDeq_ty, hDexists_ty])
    exact Option.isSome_of_eq_some (by
      simpa [bBody, funBBodyTerm, SMT.Term.abstract, proof_irrel_heq] using hden_out)
  have hY_eq : Y.fst = X!.fst := by
    apply (ZFSet.is_func_ext_iff hY_func hX!_func).2
    intro y hy
    let wy0 : SMT.Dom := ⟨y, α', hy⟩
    have hwy0_ty : wy0.snd.fst = α' := rfl
    have hbody_total_Y :
        ∀ wy0 : SMT.Dom, wy0.snd.fst = α' →
          ⟦aBody.abstract (Function.update ΔY a! (some wy0)) (hcov_aBody_updY wy0)⟧ˢ.isSome =
            true := by
      intro wy0 hwy0_ty
      by_cases hwy0_ran : wy0.fst ∈ castα.Range
      · have typ_exists_a_base' :
            AList.insert a! α' (AList.insert x! (α'.fun β') Γ) ⊢ˢ
              exists_a : SMTType.bool := by
          rw [← hupdate_forall_a_base]
          exact typ_exists_a_base
        obtain ⟨x₀, hx₀_mem, hcast_x₀_wy0, _⟩ :=
          hX!_app_range wy0 hwy0_ty hwy0_ran
        let wx₀ : SMT.Dom := ⟨x₀, α, hx₀_mem⟩
        have hx₀_dom_cast : x₀ ∈ castα.Dom := by
          simpa [ZFSet.is_func_dom_eq hcastα] using hx₀_mem
        have hcast_x₀_wy0_pair :
            wx₀.fst.pair wy0.fst ∈ castα := by
          simpa [wx₀, hcast_x₀_wy0] using
            ZFSet.fapply.def (ZFSet.is_func_is_pfunc hcastα) hx₀_dom_cast
        have hden_exists_a_true :
            ⟦exists_a.abstract (Function.update ΔY a! (some wy0)) (hφ_exists_a_at wy0)⟧ˢ =
              some ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
          obtain ⟨hφa, Φa, hden_a, hΦa_true⟩ :=
            a_spec_true_at Y wx₀ wy0 rfl hwy0_ty (by
              simpa [hcastα_eq] using hcast_x₀_wy0_pair)
          refine funUnaryExistsEqZftrueAtWitness
            (Γ := AList.insert a! α' (AList.insert x! (α'.fun β') Γ))
            (Δctx := Function.update ΔY a! (some wy0))
            (a := a!_spec) (v := a) (τ := α)
            typ_exists_a_base'
            (hφ_exists_a_at wy0) (hgo_cov_a_spec_at wy0) (hcov_a_spec_upd_at wy0)
            ?_ ?_ wx₀ rfl (D := Φa) ?_ hΦa_true
          · intro x₁ hx₁_ty
            simpa [hctx_swap_at wy0 x₁, proof_irrel_heq] using
              a_spec_total_at Y x₁ wy0 hx₁_ty hwy0_ty
          · intro x₁ hx₁_ty D hden_a'
            exact denote_type_eq_of_typing
              (typ_t := typ_a!_spec_swap) (hden := hden_a')
          · simpa [hctx_swap_at wy0 wx₀, proof_irrel_heq, wx₀] using hden_a
        have hden_forall_b_some :
            ⟦(Term.forall [b!] [β'] bBody).abstract
                (Function.update ΔY a! (some wy0))
                (hφ_forall_b_at wy0)⟧ˢ.isSome =
              true := by
          exact funUnaryForallTotal
            (Δctx := Function.update ΔY a! (some wy0))
            (a := bBody) (v := b!) (τ := β')
            (hφ_forall_b_at wy0) (hgo_cov_b_at wy0) (hcov_bBody_upd_at wy0)
            (by
              intro wy1 hwy1_ty
              exact hbody_total_b_at wy0 wy1 hwy0_ty hwy1_ty)
        dsimp [aBody]
        rw [SMT.Term.abstract, SMT.denote, hden_exists_a_true]
        change
          (if ZFSet.ZFBool.toBool
                ⟨zftrue, ZFSet.ZFBool.zftrue_mem_𝔹⟩ = true then
              ⟦(Term.forall [b!] [β'] bBody).abstract
                  (Function.update ΔY a! (some wy0))
                  (hφ_forall_b_at wy0)⟧ˢ
           else
              ⟦hdefault.abstract
                  (Function.update ΔY a! (some wy0))
                  (by
                    intro v hv
                    exact hcov_aBody_updY wy0 v (by
                      dsimp [aBody]
                      exact SMT.fv.mem_ite <| Or.inr <| Or.inr hv))⟧ˢ).isSome =
            true
        have htoBool_true :
            ZFSet.ZFBool.toBool
              ⟨zftrue, ZFSet.ZFBool.zftrue_mem_𝔹⟩ = true := by
          exact ZFSet.ZFBool.toBool_true
        rw [htoBool_true]
        rw [if_pos rfl]
        exact hden_forall_b_some
      · have hden_exists_a_false :
            ⟦exists_a.abstract (Function.update ΔY a! (some wy0)) (hφ_exists_a_at wy0)⟧ˢ =
              some ⟨zffalse, SMTType.bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
          apply funUnaryExistsEqZffalseOfTrueImpliesRange
            (Δctx := Function.update ΔY a! (some wy0))
            (τ' := α') (cast := castα) (target := wy0)
            hcastα
            (a := a!_spec) (v := a) (τ := α)
            (hφ_exists_a_at wy0) (hgo_cov_a_spec_at wy0) (hcov_a_spec_upd_at wy0)
          · intro x₀ hx₀_ty
            simpa [hctx_swap_at wy0 x₀, proof_irrel_heq] using
              a_spec_total_at Y x₀ wy0 hx₀_ty hwy0_ty
          · intro x₀ hx₀_ty D hden_a
            exact denote_type_eq_of_typing
              (typ_t := typ_a!_spec_swap) (hden := hden_a)
          · intro x₀ hx₀_ty D hden_a hDa_true
            have hφa :
                RenamingContext.CoversFV
                  (Function.update
                    (Function.update (Function.update Δctx x! (some Y)) a (some x₀))
                    a! (some wy0))
                  a!_spec := hφa_at Y x₀ wy0
            simpa [hcastα_eq] using
              a_spec_true_implies_cast Y x₀ wy0 hx₀_ty hwy0_ty
                hφa
                (by simpa [hctx_swap_at wy0 x₀, proof_irrel_heq] using hden_a)
                hDa_true
          · exact hwy0_ran
        obtain ⟨Dapp, _, _, hden_app⟩ :=
          den_app_at Y wy0 hY_ty hY_func hwy0_ty
        obtain ⟨hφd, Φd, hdenΦd, _, _⟩ :=
          default_spec_at Y wy0 Dapp hden_app
        dsimp [aBody]
        rw [SMT.Term.abstract, SMT.denote, hden_exists_a_false]
        change
          (if ZFSet.ZFBool.toBool
                ⟨zffalse, ZFSet.ZFBool.zffalse_mem_𝔹⟩ = true then
              ⟦(Term.forall [b!] [β'] bBody).abstract
                  (Function.update ΔY a! (some wy0))
                  (hφ_forall_b_at wy0)⟧ˢ
           else
              ⟦hdefault.abstract
                  (Function.update ΔY a! (some wy0))
                  hφd⟧ˢ).isSome =
            true
        have htoBool_false :
            ZFSet.ZFBool.toBool
              ⟨zffalse, ZFSet.ZFBool.zffalse_mem_𝔹⟩ = false := by
          exact ZFSet.ZFBool.toBool_false
        rw [htoBool_false]
        rw [if_neg (by decide)]
        exact Option.isSome_of_eq_some hdenΦd
    have hbody_ty_Y :
        ∀ wy0 : SMT.Dom, wy0.snd.fst = α' →
          ∀ {D : SMT.Dom},
            ⟦aBody.abstract (Function.update ΔY a! (some wy0)) (hcov_aBody_updY wy0)⟧ˢ = some D →
              D.snd.fst = SMTType.bool := by
      intro wy0 hwy0_ty D hden_body
      exact denote_type_eq_of_typing (typ_t := typ_aBody_base) (hden := hden_body)
    change
      @ᶻY.fst
        ⟨wy0.fst, by
          rw [ZFSet.is_func_dom_eq hY_func]
          exact wy0.snd.snd⟩ =
      @ᶻX!.fst
        ⟨wy0.fst, by
          rw [ZFSet.is_func_dom_eq hX!_func]
          exact wy0.snd.snd⟩
    by_cases hy_ran : wy0.fst ∈ castα.Range
    · have typ_exists_a_base' :
          AList.insert a! α' (AList.insert x! (α'.fun β') Γ) ⊢ˢ
            exists_a : SMTType.bool := by
        rw [← hupdate_forall_a_base]
        exact typ_exists_a_base
      obtain ⟨x₀, hx₀_mem, hcast_x₀_wy0, hX!_range_val⟩ :=
        hX!_app_range wy0 hwy0_ty hy_ran
      let wx₀ : SMT.Dom := ⟨x₀, α, hx₀_mem⟩
      have hx₀_dom_cast : x₀ ∈ castα.Dom := by
        simpa [ZFSet.is_func_dom_eq hcastα] using hx₀_mem
      have hcast_x₀_wy0_pair :
          wx₀.fst.pair wy0.fst ∈ castα := by
        simpa [wx₀, hcast_x₀_wy0] using
          ZFSet.fapply.def (ZFSet.is_func_is_pfunc hcastα) hx₀_dom_cast
      have hden_exists_a_true :
          ⟦exists_a.abstract (Function.update ΔY a! (some wy0)) (hφ_exists_a_at wy0)⟧ˢ =
            some ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
        obtain ⟨hφa, Φa, hden_a, hΦa_true⟩ :=
          a_spec_true_at Y wx₀ wy0 rfl hwy0_ty (by simpa [hcastα_eq] using hcast_x₀_wy0_pair)
        refine funUnaryExistsEqZftrueAtWitness
          (Γ := AList.insert a! α' (AList.insert x! (α'.fun β') Γ))
          (Δctx := Function.update ΔY a! (some wy0))
          (a := a!_spec) (v := a) (τ := α)
          typ_exists_a_base'
          (hφ_exists_a_at wy0) (hgo_cov_a_spec_at wy0) (hcov_a_spec_upd_at wy0)
          ?_ ?_ wx₀ rfl (D := Φa) ?_ hΦa_true
        · intro x₁ hx₁_ty
          simpa [hctx_swap_at wy0 x₁, proof_irrel_heq] using
            a_spec_total_at Y x₁ wy0 hx₁_ty hwy0_ty
        · intro x₁ hx₁_ty D hden_a'
          exact denote_type_eq_of_typing
            (typ_t := typ_a!_spec_swap) (hden := hden_a')
        · simpa [hctx_swap_at wy0 wx₀, proof_irrel_heq, wx₀] using hden_a
      obtain ⟨Dbody, hden_body, hDbody_true⟩ :=
        funUnaryForallTrueImpliesAt
          (Δctx := ΔY) (a := aBody) (v := a!) (τ := α')
          hφY hgo_cov_aY hcov_aBody_updY hbody_total_Y hbody_ty_Y
          hdenΦY htrue wy0 hwy0_ty
      have hden_forall_b :
          ⟦(Term.forall [b!] [β'] bBody).abstract
              (Function.update ΔY a! (some wy0))
              (hφ_forall_b_at wy0)⟧ˢ =
            some Dbody := by
        dsimp [aBody] at hden_body
        rw [SMT.Term.abstract, SMT.denote, hden_exists_a_true] at hden_body
        change
          (if ZFSet.ZFBool.toBool
                ⟨zftrue, ZFSet.ZFBool.zftrue_mem_𝔹⟩ = true then
              ⟦(Term.forall [b!] [β'] bBody).abstract
                  (Function.update ΔY a! (some wy0))
                  (hφ_forall_b_at wy0)⟧ˢ
           else
              ⟦hdefault.abstract
                  (Function.update ΔY a! (some wy0))
                  (by
                    intro v hv
                    exact hcov_aBody_updY wy0 v (by
                      dsimp [aBody]
                      exact SMT.fv.mem_ite <| Or.inr <| Or.inr hv))⟧ˢ) =
            some Dbody at hden_body
        have htoBool_true :
            ZFSet.ZFBool.toBool
              ⟨zftrue, ZFSet.ZFBool.zftrue_mem_𝔹⟩ = true := by
          exact ZFSet.ZFBool.toBool_true
        rw [htoBool_true, if_pos rfl] at hden_body
        exact hden_body
      obtain ⟨DappY, hDappY_ty, hDappY_val, hden_appY⟩ :=
        den_app_at Y wy0 hY_ty hY_func hwy0_ty
      obtain ⟨DappX, hDappX_ty, hDappX_val, hden_appX⟩ :=
        den_app_at X! wy0 hX!_ty hX!_func hwy0_ty
      obtain ⟨Dbb, hden_bbody, hDbb_true⟩ :=
        funUnaryForallTrueImpliesAt
          (Δctx := Function.update ΔY a! (some wy0))
          (a := bBody) (v := b!) (τ := β')
          (hφ_forall := hφ_forall_b_at wy0)
          (hgo_cov := hgo_cov_b_at wy0)
          (hcov_a_upd := hcov_bBody_upd_at wy0)
          (hbody_total := by
            intro wy1 hwy1_ty
            exact hbody_total_b_at wy0 wy1 hwy0_ty hwy1_ty)
          (hbody_ty := by
            intro wy1 hwy1_ty D hden
            exact hbody_ty_b_at wy0 wy1 hwy0_ty hwy1_ty hden)
          hden_forall_b hDbody_true DappX hDappX_ty
      have hφ_exists_ab :
          RenamingContext.CoversFV
            (Function.update (Function.update ΔY a! (some wy0)) b! (some DappX))
            exists_ab := by
        intro v hv
        exact hcov_bBody_upd_at wy0 DappX v (by
          rw [SMT.fv.eq_def]
          exact List.mem_append.mpr (Or.inr hv))
      have hden_exists_ab_true :
          ⟦exists_ab.abstract
              (Function.update (Function.update ΔY a! (some wy0)) b! (some DappX))
              hφ_exists_ab⟧ˢ =
            some ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
        obtain ⟨hcov_xa, y₀, hy₀_ty, hy₀_val, hden_xa⟩ :=
          den_xa_at Y wx₀ rfl hx₀_mem
        have hy₀_mem : y₀.fst ∈ ⟦β⟧ᶻ := by
          rw [← hy₀_ty]
          exact y₀.snd.snd
        have hy₀_dom_castβ : y₀.fst ∈ castβ.Dom := by
          simpa [ZFSet.is_func_dom_eq hcastβ] using hy₀_mem
        let yraw : { y : ZFSet // y ∈ ⟦β⟧ᶻ } :=
          @ᶻX.fst
            ⟨x₀, by
              rw [ZFSet.is_func_dom_eq hX_func]
              exact hx₀_mem⟩
        have hyraw_mem : (yraw : ZFSet) ∈ ⟦β⟧ᶻ := yraw.2
        have hyraw_dom_castβ :
            (yraw : ZFSet) ∈ castβ.Dom := by
          simpa [ZFSet.is_func_dom_eq hcastβ] using hyraw_mem
        have hcast_yraw_wy1 :
            ↑(@ᶻcastβ
                ⟨(yraw : ZFSet), hyraw_dom_castβ⟩) =
              DappX.fst := by
          have hcast_yraw_wy1_sub :
              @ᶻcastβ
                  ⟨(yraw : ZFSet), hyraw_dom_castβ⟩ =
                ⟨DappX.fst, by
                  simpa [hDappX_ty] using DappX.snd.snd⟩ := by
            calc
              @ᶻcastβ
                  ⟨(yraw : ZFSet), hyraw_dom_castβ⟩ =
                  @ᶻX!.fst
                    ⟨wy0.fst, by
                      rw [ZFSet.is_func_dom_eq hX!_func]
                      rw [← hwy0_ty]
                      exact wy0.snd.snd⟩ := by
                    exact hX!_range_val.symm
              _ = ⟨DappX.fst, by
                    simpa [hDappX_ty] using DappX.snd.snd⟩ := by
                    apply Subtype.ext
                    exact hDappX_val.symm
          exact congrArg Subtype.val hcast_yraw_wy1_sub
        have hcast_yraw_wy1_pair :
            (yraw : ZFSet).pair DappX.fst ∈ castβ := by
          rw [← hcast_yraw_wy1]
          exact ZFSet.fapply.def
            (ZFSet.is_func_is_pfunc hcastβ)
            hyraw_dom_castβ
        have hcast_y₀_wy1_pair :
            y₀.fst.pair DappX.fst ∈ castβ := by
          simpa [yraw, hy₀_val] using hcast_yraw_wy1_pair
        obtain ⟨hφa0, Φa, hden_a0, hΦa_true⟩ :=
          a_spec_true_at Y wx₀ wy0 rfl hwy0_ty (by simpa [hcastα_eq] using hcast_x₀_wy0_pair)
        obtain ⟨hφb0, Φb, hden_b0, hΦb_true⟩ :=
          b_spec_true_at Y wy0 y₀ DappX hy₀_ty hDappX_ty (by simpa [hcastβ_eq] using hcast_y₀_wy1_pair)
        have hφaY_at :
            ∀ x₀ : SMT.Dom,
              RenamingContext.CoversFV
                (Function.update (Function.update ΔY a (some x₀)) a! (some wy0))
                a!_spec := by
          intro x₀
          exact hφa_at Y x₀ wy0
        have hφbY_at :
            ∀ y₀ : SMT.Dom,
              RenamingContext.CoversFV
                (Function.update
                  (Function.update (Function.update ΔY a! (some wy0)) b (some y₀))
                  b! (some DappX))
                b!_spec := by
          intro y₀
          exact hφb_at Y wy0 y₀ DappX
        have b_ne_b! : b ≠ b! := by
          intro h
          exact b!_not_base (h ▸ by
            rw [AList.mem_insert]
            exact Or.inl rfl)
        exact funExistsABTrueAtRange
          (α' := α') (β' := β')
          (fv_a!_spec := fv_a!_spec)
          (fv_b!_spec := fv_b!_spec)
          (a_not_mem_fv_x := a_not_mem_fv_x)
          (b_not_mem_fv_x := b_not_mem_fv_x)
          (a!_not_mem_fv_x := a!_not_mem_fv_x)
          (b!_not_mem_fv_x := b!_not_mem_fv_x)
          (b_ne_a := b_ne_a)
          (a!_ne_b := a!_ne_b)
          (a_ne_b! := a_ne_b!)
          (b_ne_b! := b_ne_b!)
          (a_ne_a! := a_ne_a!)
          (a!_ne_b! := a!_ne_b!)
          (hφ_exists_ab := hφ_exists_ab)
          (hφa_at := hφaY_at)
          (hφb_at := hφbY_at)
          (a_spec_total_at := by
            intro x₀ hx₀_ty
            simpa [proof_irrel_heq] using
              a_spec_total_at Y x₀ wy0 hx₀_ty hwy0_ty)
          (b_spec_total_at := by
            intro y₀ hy₀_ty
            simpa [proof_irrel_heq] using
              b_spec_total_at Y wy0 y₀ DappX hy₀_ty hDappX_ty)
          (den_xa_at := by
            intro x₀ hx₀_ty hx₀_mem
            obtain ⟨hcov_xa, Dxa, hDxa_ty, _, hden_xa⟩ :=
              den_xa_at Y x₀ hx₀_ty hx₀_mem
            exact ⟨hcov_xa, Dxa, hDxa_ty, hden_xa⟩)
          (typ_a_ctx := typ_a!_spec_ctx_base)
          (typ_b_ctx := typ_b!_spec_ctx_base)
          (hx₀_ty := rfl)
          (hx₀_mem := hx₀_mem)
          (hy₀_ty := hy₀_ty)
          (hcov_xa := hcov_xa)
          (hden_xa := hden_xa)
          (hφa0 := hφa0)
          (hden_a0 := hden_a0)
          (hΦa_true := hΦa_true)
          (hφb0 := hφb0)
          (hden_b0 := hden_b0)
          (hΦb_true := hΦb_true)
      have hden_var_b! :
          ⟦(Term.var b!).abstract
              (Function.update (Function.update ΔY a! (some wy0)) b! (some DappX))
              (by
                intro v hv
                rw [fv, List.mem_singleton] at hv
                subst hv
                rw [Function.update_self]
                rfl)⟧ˢ = some DappX := by
        rw [SMT.Term.abstract.eq_def, SMT.denote, Option.pure_def, Option.some.injEq]
        apply Option.get_of_eq_some
        exact Function.update_self _ _ _
      obtain ⟨Deq, hden_eq, hDeq_ty⟩ :=
        denote_eq_some_of_some hden_appY hden_var_b! (by rw [hDappY_ty, hDappX_ty])
      have hDeq_true : Deq.fst = zftrue := by
        exact denote_eq_true_implies_fst_eq
          hden_eq hden_exists_ab_true hDeq_ty
          (by
            simpa [bBody, funBBodyTerm, SMT.Term.abstract, proof_irrel_heq,
              Function.update_of_ne x!_ne_b!, Function.update_of_ne a!_ne_b!]
              using hden_bbody)
          hDbb_true
      have hEq_app : DappY.fst = DappX.fst := by
        exact denote_eq_true_implies_fst_eq
          hden_appY hden_var_b! (by rw [hDappY_ty, hDappX_ty]) hden_eq hDeq_true
      apply Subtype.ext
      calc
        (↑(@ᶻY.fst
            ⟨wy0.fst, by
              rw [ZFSet.is_func_dom_eq hY_func]
              exact wy0.snd.snd⟩) : ZFSet) = DappY.fst := by
                exact hDappY_val.symm
        _ = DappX.fst := hEq_app
        _ = (↑(@ᶻX!.fst
            ⟨wy0.fst, by
              rw [ZFSet.is_func_dom_eq hX!_func]
              exact wy0.snd.snd⟩) : ZFSet) := by
                exact hDappX_val
    · obtain ⟨Dbody, hden_body, hDbody_true⟩ :=
        funUnaryForallTrueImpliesAt
          (Δctx := ΔY) (a := aBody) (v := a!) (τ := α')
          hφY hgo_cov_aY hcov_aBody_updY hbody_total_Y hbody_ty_Y
          hdenΦY htrue wy0 hwy0_ty
      have hden_exists_a_false :
          ⟦exists_a.abstract (Function.update ΔY a! (some wy0)) (hφ_exists_a_at wy0)⟧ˢ =
            some ⟨zffalse, SMTType.bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
        apply funUnaryExistsEqZffalseOfTrueImpliesRange
          (Δctx := Function.update ΔY a! (some wy0))
          (τ' := α') (cast := castα) (target := wy0)
          hcastα
          (a := a!_spec) (v := a) (τ := α)
          (hφ_exists_a_at wy0) (hgo_cov_a_spec_at wy0) (hcov_a_spec_upd_at wy0)
        · intro x₀ hx₀_ty
          simpa [hctx_swap_at wy0 x₀, proof_irrel_heq] using
            a_spec_total_at Y x₀ wy0 hx₀_ty hwy0_ty
        · intro x₀ hx₀_ty D hden_a
          exact denote_type_eq_of_typing
            (typ_t := typ_a!_spec_swap) (hden := hden_a)
        · intro x₀ hx₀_ty D hden_a hDa_true
          have hφa :
              RenamingContext.CoversFV
                (Function.update
                  (Function.update (Function.update Δctx x! (some Y)) a (some x₀))
                  a! (some wy0))
                a!_spec := hφa_at Y x₀ wy0
          simpa [hcastα_eq] using
            a_spec_true_implies_cast Y x₀ wy0 hx₀_ty hwy0_ty
              hφa
              (by simpa [hctx_swap_at wy0 x₀, proof_irrel_heq] using hden_a)
              hDa_true
        · exact hy_ran
      obtain ⟨Dapp, _, hDapp_val, hden_app⟩ :=
        den_app_at Y wy0 hY_ty hY_func hwy0_ty
      obtain ⟨hφd, Φd, hdenΦd, _, _⟩ :=
        default_spec_at Y wy0 Dapp hden_app
      have hden_default_body :
          ⟦hdefault.abstract (Function.update ΔY a! (some wy0)) hφd⟧ˢ =
            some Dbody := by
        dsimp [aBody] at hden_body
        rw [SMT.Term.abstract, SMT.denote, hden_exists_a_false] at hden_body
        change
          (if ZFSet.ZFBool.toBool
                ⟨zffalse, ZFSet.ZFBool.zffalse_mem_𝔹⟩ = true then
              ⟦(Term.forall [b!] [β'] bBody).abstract
                  (Function.update ΔY a! (some wy0))
                  (hφ_forall_b_at wy0)⟧ˢ
           else
              ⟦hdefault.abstract
                  (Function.update ΔY a! (some wy0))
                  hφd⟧ˢ) =
            some Dbody at hden_body
        have htoBool_false :
            ZFSet.ZFBool.toBool
              ⟨zffalse, ZFSet.ZFBool.zffalse_mem_𝔹⟩ = false := by
          exact ZFSet.ZFBool.toBool_false
        rw [htoBool_false, if_neg (by decide)] at hden_body
        exact hden_body
      have hΦd_true : Φd.fst = zftrue := by
        have hEq : Φd = Dbody := by
          exact Option.some.inj (hdenΦd.symm.trans hden_default_body)
        exact hEq ▸ hDbody_true
      have hY_default : Dapp.fst = β'.defaultZFSet := by
        exact default_true_implies_default_at Y wy0 Dapp hden_app hφd hdenΦd hΦd_true
      apply Subtype.ext
      calc
        (↑(@ᶻY.fst
            ⟨wy0.fst, by
              rw [ZFSet.is_func_dom_eq hY_func]
              exact wy0.snd.snd⟩) : ZFSet) = Dapp.fst := by
                exact hDapp_val.symm
        _ = β'.defaultZFSet := hY_default
        _ = (↑(@ᶻX!.fst
            ⟨wy0.fst, by
              rw [ZFSet.is_func_dom_eq hX!_func]
              exact wy0.snd.snd⟩) : ZFSet) := by
                symm
                exact hX!_app_default wy0 hwy0_ty hy_ran
  rw [hY_eq]
  exact hcast_mem

set_option maxHeartbeats 1000000 in
theorem funSpecTotalAt.{u}
    {α β α' β' : SMTType}
    {x a!_spec b!_spec hdefault : Term}
    {x! a a! b b! : 𝒱}
    {Γ : TypeContext}
    {Δctx : RenamingContext.Context.{u}}
    {Y : SMT.Dom.{u}}
    (hY_ty : Y.snd.fst = α'.fun β')
    (hY_func : ZFSet.IsFunc ⟦α'⟧ᶻ ⟦β'⟧ᶻ Y.fst)
    (typ_fun_spec_base :
      AList.insert x! (α'.fun β') Γ ⊢ˢ
        funSpecTerm x x! a a! b b! α β α' β' a!_spec b!_spec hdefault : SMTType.bool)
    (typ_a!_spec_ctx_base :
      AList.insert a! α' (AList.insert a α (AList.insert x! (α'.fun β') Γ)) ⊢ˢ
        a!_spec : SMTType.bool)
    (typ_b!_spec_ctx_base :
      AList.insert b! β'
        (AList.insert b β
          (AList.insert a! α' (AList.insert a α (AList.insert x! (α'.fun β') Γ)))) ⊢ˢ
        b!_spec : SMTType.bool)
    (fv_a!_spec : fv a!_spec ⊆ fv (Term.var a) ∪ {a!})
    (fv_b!_spec : fv b!_spec ⊆ fv (Term.var b) ∪ {b!})
    (castα : ZFSet)
    (hcastα : ZFSet.IsFunc ⟦α⟧ᶻ ⟦α'⟧ᶻ castα)
    (castα_preimage :
      ∀ (wy0 : SMT.Dom.{u}) (hwy0_ty : wy0.snd.fst = α')
        (hy_ran : wy0.fst ∈ castα.Range),
        ∃ (x₀ : ZFSet) (hx₀_mem : x₀ ∈ ⟦α⟧ᶻ),
          @ᶻcastα
            ⟨x₀, by
              rw [ZFSet.is_func_dom_eq hcastα]
              exact hx₀_mem⟩ = wy0.fst)
    (x!_ne_a! : x! ≠ a!)
    (x!_ne_b! : x! ≠ b!)
    (a_ne_a! : a ≠ a!)
    (b_not_base :
      b ∉ AList.insert a! α' (AList.insert a α (AList.insert x! (α'.fun β') Γ)))
    (b!_not_base :
      b! ∉ AList.insert b β
        (AList.insert a! α' (AList.insert a α (AList.insert x! (α'.fun β') Γ))))
    (a_not_mem_fv_x : a ∉ fv x)
    (b_not_mem_fv_x : b ∉ fv x)
    (a!_not_mem_fv_x : a! ∉ fv x)
    (b!_not_mem_fv_x : b! ∉ fv x)
    (den_xa_at :
      ∀ (x₀ : SMT.Dom.{u}) (hx₀_ty : x₀.snd.fst = α)
        (hx₀_mem : x₀.fst ∈ ⟦α⟧ᶻ),
        ∃ hcov_app :
          RenamingContext.CoversFV
            (Function.update (Function.update Δctx x! (some Y)) a (some x₀))
            ((@ˢx) (Term.var a)),
          ∃ Dapp : SMT.Dom.{u},
            Dapp.snd.fst = β ∧
              ⟦((@ˢx) (Term.var a)).abstract
                  (Function.update (Function.update Δctx x! (some Y)) a (some x₀))
                  hcov_app⟧ˢ =
                some Dapp)
    (hφa_at :
      ∀ (x₀ wy0 : SMT.Dom.{u}),
        RenamingContext.CoversFV
          (Function.update
            (Function.update (Function.update Δctx x! (some Y)) a (some x₀))
            a! (some wy0))
          a!_spec)
    (hφb_at :
      ∀ (wy0 y₀ wy1 : SMT.Dom.{u}),
        RenamingContext.CoversFV
          (Function.update
            (Function.update
              (Function.update (Function.update Δctx x! (some Y)) a! (some wy0))
              b (some y₀))
            b! (some wy1))
          b!_spec)
    (a_spec_total_at :
      ∀ (x₀ wy0 : SMT.Dom.{u})
        (hx₀_ty : x₀.snd.fst = α)
        (hwy0_ty : wy0.snd.fst = α'),
        ⟦a!_spec.abstract
            (Function.update
              (Function.update (Function.update Δctx x! (some Y)) a (some x₀))
              a! (some wy0))
            (hφa_at x₀ wy0)⟧ˢ.isSome =
          true)
    (b_spec_total_at :
      ∀ (wy0 y₀ wy1 : SMT.Dom.{u})
        (hy₀_ty : y₀.snd.fst = β)
        (hwy1_ty : wy1.snd.fst = β'),
        ⟦b!_spec.abstract
            (Function.update
              (Function.update
                (Function.update (Function.update Δctx x! (some Y)) a! (some wy0))
                b (some y₀))
              b! (some wy1))
            (hφb_at wy0 y₀ wy1)⟧ˢ.isSome =
          true)
    (a_spec_true_at :
      ∀ (x₀ wy0 : SMT.Dom.{u})
        (hx₀_ty : x₀.snd.fst = α)
        (hwy0_ty : wy0.snd.fst = α')
        (hcast_x₀w : x₀.fst.pair wy0.fst ∈ castα),
        ∃ (hφa :
          RenamingContext.CoversFV
            (Function.update
              (Function.update (Function.update Δctx x! (some Y)) a (some x₀))
              a! (some wy0))
            a!_spec)
          (Φa : SMT.Dom.{u}),
          ⟦a!_spec.abstract
              (Function.update
                (Function.update (Function.update Δctx x! (some Y)) a (some x₀))
                a! (some wy0))
              hφa⟧ˢ =
            some Φa ∧
          Φa.fst = zftrue)
    (a_spec_true_implies_cast :
      ∀ (x₀ wy0 : SMT.Dom.{u})
        (hx₀_ty : x₀.snd.fst = α)
        (hwy0_ty : wy0.snd.fst = α')
        (hφa :
          RenamingContext.CoversFV
            (Function.update
              (Function.update (Function.update Δctx x! (some Y)) a (some x₀))
              a! (some wy0))
            a!_spec)
        {Φa : SMT.Dom.{u}},
        ⟦a!_spec.abstract
            (Function.update
              (Function.update (Function.update Δctx x! (some Y)) a (some x₀))
              a! (some wy0))
            hφa⟧ˢ =
          some Φa →
        Φa.fst = zftrue →
        x₀.fst.pair wy0.fst ∈ castα)
    (den_app_at :
      ∀ (wy0 : SMT.Dom.{u}) (hwy0_ty : wy0.snd.fst = α'),
        ∃ Dapp : SMT.Dom.{u},
          Dapp.snd.fst = β' ∧
            Dapp.fst =
              @ᶻY.fst
                ⟨wy0.fst, by
                  simpa [ZFSet.is_func_dom_eq hY_func, hwy0_ty] using wy0.snd.snd⟩ ∧
            ⟦((@ˢTerm.var x!) (Term.var a!)).abstract
                (Function.update (Function.update Δctx x! (some Y)) a! (some wy0))
                (by
                  intro v hv
                  simp only [fv, List.mem_append, List.mem_singleton] at hv
                  rcases hv with hv | hv
                  · subst hv
                    rw [Function.update_of_ne x!_ne_a!]
                    rw [Function.update_self]
                    rfl
                  · subst hv
                    rw [Function.update_self]
                    rfl)⟧ˢ =
              some Dapp)
    (default_spec_at :
      ∀ (wy0 Dapp : SMT.Dom.{u})
        (hden_app :
          ⟦((@ˢTerm.var x!) (Term.var a!)).abstract
              (Function.update (Function.update Δctx x! (some Y)) a! (some wy0))
              (by
                intro v hv
                simp only [fv, List.mem_append, List.mem_singleton] at hv
                rcases hv with hv | hv
                · subst hv
                  rw [Function.update_of_ne x!_ne_a!]
                  rw [Function.update_self]
                  rfl
                · subst hv
                  rw [Function.update_self]
                  rfl)⟧ˢ =
            some Dapp),
        ∃ (hφd :
          RenamingContext.CoversFV
            (Function.update (Function.update Δctx x! (some Y)) a! (some wy0))
            hdefault)
          (Φd : SMT.Dom.{u}),
          ⟦hdefault.abstract
              (Function.update (Function.update Δctx x! (some Y)) a! (some wy0))
              hφd⟧ˢ =
            some Φd ∧
          Φd.snd.fst = SMTType.bool ∧
          (Dapp.fst = β'.defaultZFSet → Φd.fst = zftrue))
    (hφY :
      RenamingContext.CoversFV
        (Function.update Δctx x! (some Y))
        (funSpecTerm x x! a a! b b! α β α' β' a!_spec b!_spec hdefault)) :
    ⟦(funSpecTerm x x! a a! b b! α β α' β' a!_spec b!_spec hdefault).abstract
        (Function.update Δctx x! (some Y))
        hφY⟧ˢ.isSome =
      true := by
  let exists_a : Term := .exists [a] [α] a!_spec
  let exists_ab : Term := funExistsABTerm x a!_spec b!_spec a b α β
  let bBody : Term := funBBodyTerm x! a! b! exists_ab
  let aBody : Term := .ite exists_a (.forall [b!] [β'] bBody) hdefault
  let ΔY : RenamingContext.Context := Function.update Δctx x! (some Y)
  have hφY' :
      RenamingContext.CoversFV
        ΔY
        (.forall [a!] [α'] aBody) := by
    simpa [ΔY, aBody, bBody, exists_a, exists_ab, funSpecTerm] using hφY
  have typ_fun_spec_base' := typ_fun_spec_base
  change
    (AList.insert x! (α'.fun β') Γ) ⊢ˢ
      (.forall [a!] [α'] aBody) : SMTType.bool at typ_fun_spec_base'
  obtain ⟨_, _, _, _, _, typ_aBody_base⟩ :=
    SMT.Typing.forallE typ_fun_spec_base'
  obtain ⟨typ_exists_a_base, typ_forall_b_base, _⟩ :=
    SMT.Typing.iteE typ_aBody_base
  have hgo_cov_aY :
      ∀ v ∈ fv aBody, v ∉ [a!] → (ΔY v).isSome = true := by
    intro v hv hnot
    have hv' :
        v ∈ fv (funSpecTerm x x! a a! b b! α β α' β' a!_spec b!_spec hdefault) := by
      change v ∈ fv (Term.forall [a!] [α'] aBody)
      rw [fv]
      exact List.mem_removeAll_iff.mpr ⟨hv, hnot⟩
    exact hφY v hv'
  have hcov_aBody_updY :
      ∀ wy0 : SMT.Dom.{u},
        RenamingContext.CoversFV (Function.update ΔY a! (some wy0)) aBody := by
    intro wy0 v hv
    by_cases hva! : v = a!
    · subst hva!
      rw [Function.update_self]
      rfl
    · rw [Function.update_of_ne hva!]
      exact hgo_cov_aY v hv (by simpa [List.mem_singleton] using hva!)
  have hupdate_forall_a_base :
      SMT.TypeContext.update
        (AList.insert x! (α'.fun β') Γ) [a!] [α'] rfl =
        AList.insert a! α' (AList.insert x! (α'.fun β') Γ) := by
    simp only [SMT.TypeContext.update, List.length_cons, List.length_nil, zero_add,
      Fin.cast_eq_self, Fin.getElem_fin, Fin.foldl_succ_last, Fin.coe_ofNat_eq_mod,
      Nat.mod_succ, List.getElem_cons_zero, Fin.last_zero, Fin.isValue,
      Fin.foldl_zero]
  have typ_forall_b_base' :
      AList.insert a! α' (AList.insert x! (α'.fun β') Γ) ⊢ˢ
        (.forall [b!] [β'] bBody) : SMTType.bool := by
    rw [hupdate_forall_a_base] at typ_forall_b_base
    exact typ_forall_b_base
  obtain ⟨_, _, _, _, _, typ_bBody_base⟩ :=
    SMT.Typing.forallE typ_forall_b_base'
  have hφ_exists_a_at :
      ∀ wy0 : SMT.Dom.{u},
        RenamingContext.CoversFV
          (Function.update ΔY a! (some wy0))
          exists_a := by
    intro wy0 v hv
    have hv_remove :
        v ∈ List.removeAll (fv a!_spec) [a] := by
      simpa [exists_a, fv] using hv
    exact funRemoveAllASpecUpdateIsSome
      (fv_a!_spec := fv_a!_spec)
      (ha! := by
        rw [Function.update_self]
        rfl)
      v hv_remove
  have hgo_cov_a_spec_at :
      ∀ wy0 : SMT.Dom.{u},
        ∀ v ∈ fv a!_spec, v ∉ [a] →
          (Function.update ΔY a! (some wy0) v).isSome = true := by
    intro wy0 v hv hv_not_a
    have hv_remove : v ∈ List.removeAll (fv a!_spec) [a] := by
      exact List.mem_removeAll_iff.mpr ⟨hv, hv_not_a⟩
    exact funRemoveAllASpecUpdateIsSome
      (fv_a!_spec := fv_a!_spec)
      (ha! := by
        rw [Function.update_self]
        rfl)
      v hv_remove
  have hctx_swap_at :
      ∀ wy0 x₀ : SMT.Dom.{u},
        Function.update (Function.update ΔY a! (some wy0)) a (some x₀) =
          Function.update
            (Function.update (Function.update Δctx x! (some Y)) a (some x₀))
            a! (some wy0) := by
    intro wy0 x₀
    simpa [ΔY] using
      funUpdateSwap
        (Δctx := Function.update Δctx x! (some Y))
        (a_ne_a! := a_ne_a!)
        x₀ wy0
  have hcov_a_spec_upd_at :
      ∀ wy0 x₀ : SMT.Dom.{u},
        RenamingContext.CoversFV
          (Function.update (Function.update ΔY a! (some wy0)) a (some x₀))
          a!_spec := by
    intro wy0 x₀ v hv
    rw [hctx_swap_at wy0 x₀]
    exact hφa_at x₀ wy0 v hv
  have typ_a!_spec_swap :
      AList.insert a α (AList.insert a! α' (AList.insert x! (α'.fun β') Γ)) ⊢ˢ
        a!_spec : SMTType.bool := by
    exact SMT.Typing.weakening
      (h := typeContext_insert_swap_entries a_ne_a!.symm)
      typ_a!_spec_ctx_base
  have hφ_forall_b_at :
      ∀ wy0 : SMT.Dom.{u},
        RenamingContext.CoversFV
          (Function.update ΔY a! (some wy0))
          (Term.forall [b!] [β'] bBody) := by
    intro wy0 v hv
    by_cases hva! : v = a!
    · subst hva!
      rw [Function.update_self]
      rfl
    · rw [Function.update_of_ne hva!]
      exact hgo_cov_aY v
        (by
          dsimp [aBody]
          exact SMT.fv.mem_ite <| Or.inr <| Or.inl hv)
        (by simpa [List.mem_singleton] using hva!)
  have hupdate_forall_b_base :
      SMT.TypeContext.update
        (AList.insert a! α' (AList.insert x! (α'.fun β') Γ))
        [b!] [β'] rfl =
        AList.insert b! β' (AList.insert a! α' (AList.insert x! (α'.fun β') Γ)) := by
    unfold SMT.TypeContext.update
    simp only [List.length_cons, List.length_nil, zero_add,
      Fin.foldl_succ_last, Fin.getElem_fin, Fin.coe_cast,
      Fin.val_last, List.getElem_cons_zero, Fin.coe_castSucc,
      Fin.foldl_zero]
  have typ_bBody_base' :
      AList.insert b! β' (AList.insert a! α' (AList.insert x! (α'.fun β') Γ)) ⊢ˢ
        bBody : SMTType.bool := by
    rw [← hupdate_forall_b_base]
    exact typ_bBody_base
  have hgo_cov_b_at :
      ∀ wy0 : SMT.Dom.{u},
        ∀ v ∈ fv bBody, v ∉ [b!] →
          (Function.update ΔY a! (some wy0) v).isSome = true := by
    intro wy0 v hv hv_not_b!
    have hv_forall_b :
        v ∈ fv (Term.forall [b!] [β'] bBody) := by
      rw [fv]
      exact List.mem_removeAll_iff.mpr ⟨hv, hv_not_b!⟩
    by_cases hva! : v = a!
    · subst hva!
      rw [Function.update_self]
      rfl
    · rw [Function.update_of_ne hva!]
      exact hgo_cov_aY v
        (by
          dsimp [aBody]
          exact SMT.fv.mem_ite <| Or.inr <| Or.inl hv_forall_b)
        (by simpa [List.mem_singleton] using hva!)
  have hcov_bBody_upd_at :
      ∀ wy0 wy1 : SMT.Dom.{u},
        RenamingContext.CoversFV
          (Function.update (Function.update ΔY a! (some wy0)) b! (some wy1))
          bBody := by
    intro wy0 wy1 v hv
    by_cases hvb! : v = b!
    · subst hvb!
      rw [Function.update_self]
      rfl
    · rw [Function.update_of_ne hvb!]
      exact hgo_cov_b_at wy0 v hv (by simpa [List.mem_singleton] using hvb!)
  have b_ne_a : b ≠ a := by
    intro h
    subst h
    exact b_not_base (by
      rw [AList.mem_insert]
      exact Or.inr (by
        rw [AList.mem_insert]
        exact Or.inl rfl))
  have a!_ne_b : a! ≠ b := by
    intro h
    exact b_not_base (h ▸ by
      rw [AList.mem_insert]
      exact Or.inl rfl)
  have a_ne_b! : a ≠ b! := by
    intro hab!
    exact b!_not_base (hab! ▸ by
      rw [AList.mem_insert]
      exact Or.inr (by
        rw [AList.mem_insert]
        exact Or.inr (by
          rw [AList.mem_insert]
          exact Or.inl rfl)))
  have a!_ne_b! : a! ≠ b! := by
    intro ha!b!
    exact b!_not_base (ha!b! ▸ by
      rw [AList.mem_insert]
      exact Or.inr (by
        rw [AList.mem_insert]
        exact Or.inl rfl))
  have hexists_ab_total_at :
      ∀ wy0 wy1 : SMT.Dom.{u},
        wy0.snd.fst = α' →
          wy1.snd.fst = β' →
            ⟦exists_ab.abstract
                (Function.update (Function.update ΔY a! (some wy0)) b! (some wy1))
                (by
                  intro v hv
                  exact hcov_bBody_upd_at wy0 wy1 v (by
                    rw [SMT.fv.eq_def]
                    exact List.mem_append.mpr (Or.inr hv)))⟧ˢ.isSome =
              true := by
    intro wy0 wy1 hwy0_ty hwy1_ty
    exact funExistsABTotalAt
      (fv_a!_spec := fv_a!_spec)
      (fv_b!_spec := fv_b!_spec)
      (a_not_mem_fv_x := a_not_mem_fv_x)
      (b_not_mem_fv_x := b_not_mem_fv_x)
      (a!_not_mem_fv_x := a!_not_mem_fv_x)
      (b!_not_mem_fv_x := b!_not_mem_fv_x)
      (b_ne_a := b_ne_a)
      (a!_ne_b := a!_ne_b)
      (a_ne_b! := a_ne_b!)
      (b_ne_b! := by
        intro h
        exact b!_not_base (h ▸ by
          rw [AList.mem_insert]
          exact Or.inl rfl))
      (a_ne_a! := a_ne_a!)
      (a!_ne_b! := a!_ne_b!)
      (hφ_exists_ab := by
        intro v hv
        exact hcov_bBody_upd_at wy0 wy1 v (by
          rw [SMT.fv.eq_def]
          exact List.mem_append.mpr (Or.inr hv)))
      (hφa_at := by
        intro x₀
        exact hφa_at x₀ wy0)
      (hφb_at := by
        intro y₀
        exact hφb_at wy0 y₀ wy1)
      (a_spec_total_at := by
        intro x₀ hx₀_ty
        simpa [hctx_swap_at wy0 x₀, proof_irrel_heq] using
          a_spec_total_at x₀ wy0 hx₀_ty hwy0_ty)
      (b_spec_total_at := by
        intro y₀ hy₀_ty
        simpa [proof_irrel_heq] using
          b_spec_total_at wy0 y₀ wy1 hy₀_ty hwy1_ty)
      (den_xa_at := by
        intro x₀ hx₀_ty hx₀_mem
        obtain ⟨hcov_xa, Dxa, hDxa_ty, hden_xa⟩ :=
          den_xa_at x₀ hx₀_ty hx₀_mem
        exact ⟨hcov_xa, Dxa, hDxa_ty, hden_xa⟩)
      (typ_a_ctx := typ_a!_spec_ctx_base)
      (typ_b_ctx := typ_b!_spec_ctx_base)
  have hbody_total_b_at :
      ∀ wy0 wy1 : SMT.Dom.{u},
        wy0.snd.fst = α' →
          wy1.snd.fst = β' →
            ⟦bBody.abstract
                (Function.update (Function.update ΔY a! (some wy0)) b! (some wy1))
                (hcov_bBody_upd_at wy0 wy1)⟧ˢ.isSome =
              true := by
    as_aux_lemma =>
    intro wy0 wy1 hwy0_ty hwy1_ty
    obtain ⟨Dapp, hDapp_ty, _, hden_app⟩ :=
      den_app_at wy0 hwy0_ty
    have hden_var_b! :
        ⟦(Term.var b!).abstract
            (Function.update (Function.update ΔY a! (some wy0)) b! (some wy1))
            (by
              intro v hv
              rw [fv, List.mem_singleton] at hv
              subst hv
              rw [Function.update_self]
              rfl)⟧ˢ = some wy1 := by
      rw [SMT.Term.abstract.eq_def, SMT.denote, Option.pure_def, Option.some.injEq]
      apply Option.get_of_eq_some
      exact Function.update_self _ _ _
    have hcov_appY :
        RenamingContext.CoversFV
          (Function.update (Function.update Δctx x! (some Y)) a! (some wy0))
          ((@ˢTerm.var x!) (Term.var a!)) := by
      intro v hv
      rw [fv, List.mem_append] at hv
      rcases hv with hv | hv
      · rw [fv, List.mem_singleton] at hv
        subst hv
        rw [Function.update_of_ne x!_ne_a!]
        rw [Function.update_self]
        rfl
      · rw [fv, List.mem_singleton] at hv
        subst hv
        rw [Function.update_self]
        rfl
    have hb!_not_mem_fv_app :
        b! ∉ fv ((@ˢTerm.var x!) (Term.var a!)) := by
      intro hv
      rw [fv, List.mem_append] at hv
      rcases hv with hv | hv
      · rw [fv, List.mem_singleton] at hv
        exact x!_ne_b! hv.symm
      · rw [fv, List.mem_singleton] at hv
        exact a!_ne_b! hv.symm
    have hcov_app' :
        RenamingContext.CoversFV
          (Function.update (Function.update ΔY a! (some wy0)) b! (some wy1))
          ((@ˢTerm.var x!) (Term.var a!)) := by
      simpa [ΔY] using
        SMT.RenamingContext.coversFV_update_of_notMem
          (x := b!) (d := wy1) hb!_not_mem_fv_app hcov_appY
    have hden_app' :
        ⟦((@ˢTerm.var x!) (Term.var a!)).abstract
            (Function.update (Function.update ΔY a! (some wy0)) b! (some wy1))
            hcov_app'⟧ˢ =
          some Dapp := by
      simpa [ΔY] using
        (SMT.RenamingContext.denote_update_of_notMem
          (x := b!) (d := wy1)
          (h := hcov_appY)
          hb!_not_mem_fv_app).symm.trans hden_app
    obtain ⟨Deq, hden_eq, hDeq_ty⟩ :=
      denote_eq_some_of_some
        hden_app'
        hden_var_b!
        (by rw [hDapp_ty, hwy1_ty])
    obtain ⟨Dexists, hden_exists⟩ :=
      Option.isSome_iff_exists.mp (hexists_ab_total_at wy0 wy1 hwy0_ty hwy1_ty)
    have typ_bBody_eq := SMT.Typing.eqE typ_bBody_base'
    obtain ⟨_, σ, typ_eq_ctx, typ_exists_ab_ctx⟩ := typ_bBody_eq
    have hσ_bool : σ = SMTType.bool := by
      obtain ⟨hσ_bool, _, _, _⟩ := SMT.Typing.eqE typ_eq_ctx
      exact hσ_bool
    have hDexists_ty : Dexists.snd.fst = SMTType.bool := by
      cases hσ_bool
      exact denote_type_eq_of_typing (typ_t := typ_exists_ab_ctx) (hden := hden_exists)
    obtain ⟨Dout, hden_out, _⟩ :=
      denote_eq_some_of_some hden_eq hden_exists (by rw [hDeq_ty, hDexists_ty])
    exact Option.isSome_of_eq_some (by
      simpa [bBody, funBBodyTerm, SMT.Term.abstract, proof_irrel_heq] using hden_out)
  have hbody_total_Y :
      ∀ wy0 : SMT.Dom.{u}, wy0.snd.fst = α' →
        ⟦aBody.abstract (Function.update ΔY a! (some wy0)) (hcov_aBody_updY wy0)⟧ˢ.isSome =
          true := by
    intro wy0 hwy0_ty
    by_cases hwy0_ran : wy0.fst ∈ castα.Range
    · have typ_exists_a_base' :
          AList.insert a! α' (AList.insert x! (α'.fun β') Γ) ⊢ˢ
            exists_a : SMTType.bool := by
        rw [← hupdate_forall_a_base]
        exact typ_exists_a_base
      obtain ⟨x₀, hx₀_mem, hcast_x₀_wy0⟩ :=
        castα_preimage wy0 hwy0_ty hwy0_ran
      let wx₀ : SMT.Dom := ⟨x₀, α, hx₀_mem⟩
      have hx₀_dom_cast : x₀ ∈ castα.Dom := by
        simpa [ZFSet.is_func_dom_eq hcastα] using hx₀_mem
      have hcast_x₀_wy0_pair :
          wx₀.fst.pair wy0.fst ∈ castα := by
        simpa [wx₀, hcast_x₀_wy0] using
          ZFSet.fapply.def (ZFSet.is_func_is_pfunc hcastα) hx₀_dom_cast
      have hden_exists_a_true :
          ⟦exists_a.abstract (Function.update ΔY a! (some wy0)) (hφ_exists_a_at wy0)⟧ˢ =
            some ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
        obtain ⟨hφa, Φa, hden_a, hΦa_true⟩ :=
          a_spec_true_at wx₀ wy0 rfl hwy0_ty hcast_x₀_wy0_pair
        refine funUnaryExistsEqZftrueAtWitness
          (Γ := AList.insert a! α' (AList.insert x! (α'.fun β') Γ))
          (Δctx := Function.update ΔY a! (some wy0))
          (a := a!_spec) (v := a) (τ := α)
          typ_exists_a_base'
          (hφ_exists_a_at wy0) (hgo_cov_a_spec_at wy0) (hcov_a_spec_upd_at wy0)
          ?_ ?_ wx₀ rfl (D := Φa) ?_ hΦa_true
        · intro x₁ hx₁_ty
          simpa [hctx_swap_at wy0 x₁, proof_irrel_heq] using
            a_spec_total_at x₁ wy0 hx₁_ty hwy0_ty
        · intro x₁ hx₁_ty D hden_a'
          exact denote_type_eq_of_typing
            (typ_t := typ_a!_spec_swap) (hden := hden_a')
        · simpa [hctx_swap_at wy0 wx₀, proof_irrel_heq, wx₀] using hden_a
      have hden_forall_b_some :
          ⟦(Term.forall [b!] [β'] bBody).abstract
              (Function.update ΔY a! (some wy0))
              (hφ_forall_b_at wy0)⟧ˢ.isSome =
            true := by
        exact funUnaryForallTotal
          (Δctx := Function.update ΔY a! (some wy0))
          (a := bBody) (v := b!) (τ := β')
          (hφ_forall_b_at wy0) (hgo_cov_b_at wy0) (hcov_bBody_upd_at wy0)
          (by
            intro wy1 hwy1_ty
            exact hbody_total_b_at wy0 wy1 hwy0_ty hwy1_ty)
      dsimp [aBody]
      rw [SMT.Term.abstract, SMT.denote, hden_exists_a_true]
      change
        (if ZFSet.ZFBool.toBool
              ⟨zftrue, ZFSet.ZFBool.zftrue_mem_𝔹⟩ = true then
            ⟦(Term.forall [b!] [β'] bBody).abstract
                (Function.update ΔY a! (some wy0))
                (hφ_forall_b_at wy0)⟧ˢ
         else
            ⟦hdefault.abstract
                (Function.update ΔY a! (some wy0))
                (by
                  intro v hv
                  exact hcov_aBody_updY wy0 v (by
                    dsimp [aBody]
                    exact SMT.fv.mem_ite <| Or.inr <| Or.inr hv))⟧ˢ).isSome =
          true
      have htoBool_true :
          ZFSet.ZFBool.toBool
            ⟨zftrue, ZFSet.ZFBool.zftrue_mem_𝔹⟩ = true := by
        exact ZFSet.ZFBool.toBool_true
      rw [htoBool_true]
      rw [if_pos rfl]
      exact hden_forall_b_some
    · have hden_exists_a_false :
          ⟦exists_a.abstract (Function.update ΔY a! (some wy0)) (hφ_exists_a_at wy0)⟧ˢ =
            some ⟨zffalse, SMTType.bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
        apply funUnaryExistsEqZffalseOfTrueImpliesRange
          (Δctx := Function.update ΔY a! (some wy0))
          (τ' := α') (cast := castα) (target := wy0)
          hcastα
          (a := a!_spec) (v := a) (τ := α)
          (hφ_exists_a_at wy0) (hgo_cov_a_spec_at wy0) (hcov_a_spec_upd_at wy0)
        · intro x₀ hx₀_ty
          simpa [hctx_swap_at wy0 x₀, proof_irrel_heq] using
            a_spec_total_at x₀ wy0 hx₀_ty hwy0_ty
        · intro x₀ hx₀_ty D hden_a
          exact denote_type_eq_of_typing
            (typ_t := typ_a!_spec_swap) (hden := hden_a)
        · intro x₀ hx₀_ty D hden_a hDa_true
          have hφa :
              RenamingContext.CoversFV
                (Function.update
                  (Function.update (Function.update Δctx x! (some Y)) a (some x₀))
                  a! (some wy0))
                a!_spec := hφa_at x₀ wy0
          exact a_spec_true_implies_cast x₀ wy0 hx₀_ty hwy0_ty
            hφa
            (by simpa [hctx_swap_at wy0 x₀, proof_irrel_heq] using hden_a)
            hDa_true
        · exact hwy0_ran
      obtain ⟨Dapp, _, _, hden_app⟩ :=
        den_app_at wy0 hwy0_ty
      obtain ⟨hφd, Φd, hdenΦd, _, _⟩ :=
        default_spec_at wy0 Dapp hden_app
      dsimp [aBody]
      rw [SMT.Term.abstract, SMT.denote, hden_exists_a_false]
      change
        (if ZFSet.ZFBool.toBool
              ⟨zffalse, ZFSet.ZFBool.zffalse_mem_𝔹⟩ = true then
            ⟦(Term.forall [b!] [β'] bBody).abstract
                (Function.update ΔY a! (some wy0))
                (hφ_forall_b_at wy0)⟧ˢ
         else
            ⟦hdefault.abstract
                (Function.update ΔY a! (some wy0))
                hφd⟧ˢ).isSome =
          true
      have htoBool_false :
          ZFSet.ZFBool.toBool
            ⟨zffalse, ZFSet.ZFBool.zffalse_mem_𝔹⟩ = false := by
        exact ZFSet.ZFBool.toBool_false
      rw [htoBool_false]
      rw [if_neg (by decide)]
      exact Option.isSome_of_eq_some hdenΦd
  simpa [ΔY, aBody, bBody, exists_a, exists_ab, funSpecTerm, proof_irrel_heq] using
    (funUnaryForallTotal
      (Δctx := ΔY) (a := aBody) (v := a!) (τ := α')
      hφY' hgo_cov_aY hcov_aBody_updY hbody_total_Y)
