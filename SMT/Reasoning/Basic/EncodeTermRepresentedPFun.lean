import SMT.Reasoning.Basic.EncodeTermRepresentedCprod
import SMT.Reasoning.Basic.EncodeTermCorrectPFun

open Std.Do B SMT ZFSet Classical

/-! # Representation-aware partial-function spaces -/

def pfunSet (X Y : ZFSet) : ZFSet :=
  (X.prod Y).powerset.sep (fun f => f.IsPFunc X Y)

private theorem pfunDenoteAppCongr.{u}
    {f₁ f₂ x₁ x₂ : SMT.PHOAS.Term SMT.Dom.{u}}
    (hf : ⟦f₁⟧ˢ = ⟦f₂⟧ˢ) (hx : ⟦x₁⟧ˢ = ⟦x₂⟧ˢ) :
    ⟦SMT.PHOAS.Term.app f₁ x₁⟧ˢ =
      ⟦SMT.PHOAS.Term.app f₂ x₂⟧ˢ := by
  simp only [SMT.denote, hf, hx]

private theorem pfunDenoteAndCongr.{u}
    {p₁ p₂ q₁ q₂ : SMT.PHOAS.Term SMT.Dom.{u}}
    (hp : ⟦p₁⟧ˢ = ⟦p₂⟧ˢ) (hq : ⟦q₁⟧ˢ = ⟦q₂⟧ˢ) :
    ⟦SMT.PHOAS.Term.and p₁ q₁⟧ˢ =
      ⟦SMT.PHOAS.Term.and p₂ q₂⟧ˢ := by
  simp only [SMT.denote, hp, hq]

private theorem pfunDenoteNotCongr.{u}
    {p q : SMT.PHOAS.Term SMT.Dom.{u}}
    (h : ⟦p⟧ˢ = ⟦q⟧ˢ) :
    ⟦SMT.PHOAS.Term.not p⟧ˢ = ⟦SMT.PHOAS.Term.not q⟧ˢ := by
  simp only [SMT.denote, h]

private theorem pfunDenoteImpCongr.{u}
    {p₁ p₂ q₁ q₂ : SMT.PHOAS.Term SMT.Dom.{u}}
    (hp : ⟦p₁⟧ˢ = ⟦p₂⟧ˢ) (hq : ⟦q₁⟧ˢ = ⟦q₂⟧ˢ) :
    ⟦SMT.PHOAS.Term.imp p₁ q₁⟧ˢ =
      ⟦SMT.PHOAS.Term.imp p₂ q₂⟧ˢ := by
  exact pfunDenoteNotCongr
    (pfunDenoteAndCongr hp (pfunDenoteNotCongr hq))

private theorem denote_app_exact_rep_pfun.{u}
    {sigma tau : SMTType}
    {tf tx : SMT.PHOAS.Term SMT.Dom}
    {WF WX : SMT.Dom.{u}}
    (hdenF : ⟦tf⟧ˢ = some WF) (hdenX : ⟦tx⟧ˢ = some WX)
    (hWF_ty : WF.snd.fst = SMTType.fun sigma tau)
    (hWX_ty : WX.snd.fst = sigma) :
    let hfunc : ZFSet.IsFunc ⟦sigma⟧ᶻ ⟦tau⟧ᶻ WF.fst := by
      have hmem := WF.snd.snd
      rw [hWF_ty, SMTType.toZFSet] at hmem
      exact ZFSet.mem_funs.mp hmem
    let hdom : WX.fst ∈ WF.fst.Dom := by
      rw [ZFSet.is_func_dom_eq hfunc, ← hWX_ty]
      exact WX.snd.snd
    ∃ D : SMT.Dom.{u},
      ⟦SMT.PHOAS.Term.app tf tx⟧ˢ = some D ∧
      D.snd.fst = tau ∧
      D.fst = (ZFSet.fapply WF.fst (ZFSet.is_func_is_pfunc hfunc)
        ⟨WX.fst, hdom⟩).val := by
  dsimp only
  let hfunc : ZFSet.IsFunc ⟦sigma⟧ᶻ ⟦tau⟧ᶻ WF.fst := by
    have hmem := WF.snd.snd
    rw [hWF_ty, SMTType.toZFSet] at hmem
    exact ZFSet.mem_funs.mp hmem
  let hdom : WX.fst ∈ WF.fst.Dom := by
    rw [ZFSet.is_func_dom_eq hfunc, ← hWX_ty]
    exact WX.snd.snd
  let Y := ZFSet.fapply WF.fst (ZFSet.is_func_is_pfunc hfunc)
    ⟨WX.fst, hdom⟩
  refine ⟨⟨Y.val, tau, Y.property⟩, ?_, rfl, rfl⟩
  rw [SMT.denote, hdenF, hdenX]
  obtain ⟨F, sigmaF, hF⟩ := WF
  obtain ⟨X, sigmaX, hX⟩ := WX
  dsimp at hWF_ty hWX_ty hfunc hdom Y ⊢
  subst sigmaF
  subst sigmaX
  simp only [dif_pos (ZFSet.is_func_is_pfunc hfunc), dif_pos hdom,
    ite_true]
  rfl

private def pfunClosurePHOAS (WR WA WB Wa Wb : SMT.Dom) :
    SMT.PHOAS.Term SMT.Dom :=
  .imp
    (.app (.var WR) (.pair (.var Wa) (.var Wb)))
    (.and (.app (.var WA) (.var Wa))
      (.app (.var WB) (.var Wb)))

private def pfunClosureTerm
    (A B : SMT.Term) (R x y : SMT.𝒱) : SMT.Term :=
  .imp
    (.app (.var R) (.pair (.var x) (.var y)))
    (.and (.app A (.var x)) (.app B (.var y)))

private theorem pfunClosureTerm_denote_of_leaves.{u}
    {A B : SMT.Term} {R x y : SMT.𝒱}
    {Delta : SMT.RenamingContext.Context.{u}}
    {WR WA WB Wx Wy : SMT.Dom.{u}}
    (hcovBody : SMT.RenamingContext.CoversFV Delta
      (pfunClosureTerm A B R x y))
    (hcovR : SMT.RenamingContext.CoversFV Delta (SMT.Term.var R))
    (hcovA : SMT.RenamingContext.CoversFV Delta A)
    (hcovB : SMT.RenamingContext.CoversFV Delta B)
    (hcovX : SMT.RenamingContext.CoversFV Delta (SMT.Term.var x))
    (hcovY : SMT.RenamingContext.CoversFV Delta (SMT.Term.var y))
    (hdenR : ⟦(SMT.Term.var R).abstract Delta hcovR⟧ˢ = some WR)
    (hdenA : ⟦A.abstract Delta hcovA⟧ˢ = some WA)
    (hdenB : ⟦B.abstract Delta hcovB⟧ˢ = some WB)
    (hdenX : ⟦(SMT.Term.var x).abstract Delta hcovX⟧ˢ = some Wx)
    (hdenY : ⟦(SMT.Term.var y).abstract Delta hcovY⟧ˢ = some Wy) :
    ⟦(pfunClosureTerm A B R x y).abstract Delta hcovBody⟧ˢ =
      ⟦pfunClosurePHOAS WR WA WB Wx Wy⟧ˢ := by
  dsimp only [pfunClosureTerm]
  have hDeltaR : Delta R = some WR := by
    simpa [SMT.Term.abstract, SMT.denote, Option.pure_def] using hdenR
  have hDeltaX : Delta x = some Wx := by
    simpa [SMT.Term.abstract, SMT.denote, Option.pure_def] using hdenX
  have hDeltaY : Delta y = some Wy := by
    simpa [SMT.Term.abstract, SMT.denote, Option.pure_def] using hdenY
  simp only [SMT.Term.abstract]
  simp only [hDeltaR, hDeltaX, hDeltaY, Option.get_some]
  simp only [pfunClosurePHOAS]
  apply pfunDenoteImpCongr
  · rfl
  · apply pfunDenoteAndCongr
    · apply pfunDenoteAppCongr
      · simpa only [proof_irrel_heq] using hdenA
      · rfl
    · apply pfunDenoteAppCongr
      · simpa only [proof_irrel_heq] using hdenB
      · rfl

private theorem pfunClosurePHOAS_denote.{u}
    {rho sigma : SMTType} {WR WA WB Wa Wb : SMT.Dom.{u}}
    (hWR_ty : WR.snd.fst = SMTType.fun
      (SMTType.pair rho sigma) SMTType.bool)
    (hWA_ty : WA.snd.fst = SMTType.fun rho SMTType.bool)
    (hWB_ty : WB.snd.fst = SMTType.fun sigma SMTType.bool)
    (hWa_ty : Wa.snd.fst = rho)
    (hWb_ty : Wb.snd.fst = sigma) :
    ∃ D : SMT.Dom.{u},
      ⟦pfunClosurePHOAS WR WA WB Wa Wb⟧ˢ = some D ∧
      D.snd.fst = SMTType.bool ∧
      (D.fst = ZFSet.zftrue ↔
        (Wa.fst.pair Wb.fst).pair ZFSet.zftrue ∈ WR.fst →
          Wa.fst.pair ZFSet.zftrue ∈ WA.fst ∧
          Wb.fst.pair ZFSet.zftrue ∈ WB.fst) := by
  have hWa_mem : Wa.fst ∈ ⟦rho⟧ᶻ := by
    simpa [hWa_ty] using Wa.snd.snd
  have hWb_mem : Wb.fst ∈ ⟦sigma⟧ᶻ := by
    simpa [hWb_ty] using Wb.snd.snd
  have hpair_mem : Wa.fst.pair Wb.fst ∈
      ⟦SMTType.pair rho sigma⟧ᶻ := by
    simpa [SMTType.toZFSet] using
      ZFSet.pair_mem_prod.mpr ⟨hWa_mem, hWb_mem⟩
  let Wab : SMT.Dom.{u} :=
    ⟨Wa.fst.pair Wb.fst, SMTType.pair rho sigma, hpair_mem⟩
  have hden_pair :
      ⟦SMT.PHOAS.Term.pair (.var Wa) (.var Wb)⟧ˢ = some Wab := by
    simp [SMT.denote, Wab, hWa_ty, hWb_ty]
  obtain ⟨DR, hden_R, hDR_ty, hDR_val⟩ :=
    denote_app_exact_rep_pfun
      (sigma := SMTType.pair rho sigma) (tau := SMTType.bool)
      (tf := .var WR) (tx := .pair (.var Wa) (.var Wb))
      (WF := WR) (WX := Wab) (hdenF := rfl) (hdenX := hden_pair)
      hWR_ty (by rfl)
  obtain ⟨DA, hden_A, hDA_ty, hDA_val⟩ :=
    denote_app_exact_rep_pfun
      (sigma := rho) (tau := SMTType.bool)
      (tf := .var WA) (tx := .var Wa) (WF := WA) (WX := Wa)
      (hdenF := rfl) (hdenX := rfl) hWA_ty hWa_ty
  obtain ⟨DB, hden_B, hDB_ty, hDB_val⟩ :=
    denote_app_exact_rep_pfun
      (sigma := sigma) (tau := SMTType.bool)
      (tf := .var WB) (tx := .var Wb) (WF := WB) (WX := Wb)
      (hdenF := rfl) (hdenX := rfl) hWB_ty hWb_ty
  obtain ⟨DAB, hden_AB, hDAB_ty⟩ :=
    denote_and_some_bool_of_some_bool
      hden_A hDA_ty hden_B hDB_ty
  obtain ⟨D, hden_D, hD_ty⟩ :=
    denote_imp_some_bool hden_R hDR_ty hden_AB hDAB_ty
  have hRfunc : ZFSet.IsFunc ⟦SMTType.pair rho sigma⟧ᶻ
      ZFSet.𝔹 WR.fst :=
    ZFSet.mem_funs.mp (by
      simpa [hWR_ty, SMTType.toZFSet] using WR.snd.snd)
  have hAfunc : ZFSet.IsFunc ⟦rho⟧ᶻ ZFSet.𝔹 WA.fst :=
    ZFSet.mem_funs.mp (by
      simpa [hWA_ty, SMTType.toZFSet] using WA.snd.snd)
  have hBfunc : ZFSet.IsFunc ⟦sigma⟧ᶻ ZFSet.𝔹 WB.fst :=
    ZFSet.mem_funs.mp (by
      simpa [hWB_ty, SMTType.toZFSet] using WB.snd.snd)
  have hR_true_iff : DR.fst = ZFSet.zftrue ↔
      (Wa.fst.pair Wb.fst).pair ZFSet.zftrue ∈ WR.fst := by
    simpa [hDR_val, Wab] using
      (ZFSet.fapply_eq_zftrue_iff_pair hRfunc hpair_mem)
  have hA_true_iff : DA.fst = ZFSet.zftrue ↔
      Wa.fst.pair ZFSet.zftrue ∈ WA.fst := by
    simpa [hDA_val] using
      (ZFSet.fapply_eq_zftrue_iff_pair hAfunc hWa_mem)
  have hB_true_iff : DB.fst = ZFSet.zftrue ↔
      Wb.fst.pair ZFSet.zftrue ∈ WB.fst := by
    simpa [hDB_val] using
      (ZFSet.fapply_eq_zftrue_iff_pair hBfunc hWb_mem)
  have hAB_true_iff : DAB.fst = ZFSet.zftrue ↔
      DA.fst = ZFSet.zftrue ∧ DB.fst = ZFSet.zftrue := by
    constructor
    · exact fun h => denote_and_both_zftrue_of_zftrue
        hden_A hDA_ty hden_B hDB_ty hden_AB h
    · exact fun ⟨hA, hB⟩ => congrArg (·.fst)
        (Option.some.inj (hden_AB.symm.trans
          (denote_and_eq_zftrue_of_some_zftrue
            hden_A hDA_ty hA hden_B hDB_ty hB)))
  have hDR_bool : DR.fst ∈ ZFSet.𝔹 := by
    simpa [hDR_ty] using DR.snd.snd
  rw [ZFSet.ZFBool.mem_𝔹_iff] at hDR_bool
  refine ⟨D, ?_, hD_ty, ?_⟩
  · simpa [pfunClosurePHOAS] using hden_D
  · rw [denote_imp_true_iff hden_R hDR_ty hden_AB hDAB_ty hden_D]
    rcases hDR_bool with hRfalse | hRtrue
    · constructor
      · exact fun _ hmem => False.elim
          (ZFSet.zftrue_ne_zffalse
            ((hR_true_iff.mpr hmem).symm.trans hRfalse))
      · exact fun _ => Or.inl hRfalse
    · have hRmem : (Wa.fst.pair Wb.fst).pair ZFSet.zftrue ∈
          WR.fst := hR_true_iff.mp hRtrue
      simp only [hRtrue, ZFSet.zftrue_ne_zffalse,
        hAB_true_iff, hA_true_iff, hB_true_iff, hRmem,
        true_implies, false_or]

private def pfunFunctionalityPHOAS
    (WR Wa Wb Wb' : SMT.Dom) : SMT.PHOAS.Term SMT.Dom :=
  .imp
    (.and
      (.app (.var WR) (.pair (.var Wa) (.var Wb)))
      (.app (.var WR) (.pair (.var Wa) (.var Wb'))))
    (.eq (.var Wb) (.var Wb'))

private def pfunFunctionalityTerm
    (R x y y' : SMT.𝒱) : SMT.Term :=
  .imp
    (.and
      (.app (.var R) (.pair (.var x) (.var y)))
      (.app (.var R) (.pair (.var x) (.var y'))))
    (.eq (.var y) (.var y'))

private theorem pfunFunctionalityTerm_denote_of_leaves.{u}
    {R x y y' : SMT.𝒱}
    {Delta : SMT.RenamingContext.Context.{u}}
    {WR Wx Wy Wy' : SMT.Dom.{u}}
    (hcovBody : SMT.RenamingContext.CoversFV Delta
      (pfunFunctionalityTerm R x y y'))
    (hcovR : SMT.RenamingContext.CoversFV Delta (SMT.Term.var R))
    (hcovX : SMT.RenamingContext.CoversFV Delta (SMT.Term.var x))
    (hcovY : SMT.RenamingContext.CoversFV Delta (SMT.Term.var y))
    (hcovY' : SMT.RenamingContext.CoversFV Delta (SMT.Term.var y'))
    (hdenR : ⟦(SMT.Term.var R).abstract Delta hcovR⟧ˢ = some WR)
    (hdenX : ⟦(SMT.Term.var x).abstract Delta hcovX⟧ˢ = some Wx)
    (hdenY : ⟦(SMT.Term.var y).abstract Delta hcovY⟧ˢ = some Wy)
    (hdenY' : ⟦(SMT.Term.var y').abstract Delta hcovY'⟧ˢ = some Wy') :
    ⟦(pfunFunctionalityTerm R x y y').abstract Delta hcovBody⟧ˢ =
      ⟦pfunFunctionalityPHOAS WR Wx Wy Wy'⟧ˢ := by
  dsimp only [pfunFunctionalityTerm]
  have hDeltaR : Delta R = some WR := by
    simpa [SMT.Term.abstract, SMT.denote, Option.pure_def] using hdenR
  have hDeltaX : Delta x = some Wx := by
    simpa [SMT.Term.abstract, SMT.denote, Option.pure_def] using hdenX
  have hDeltaY : Delta y = some Wy := by
    simpa [SMT.Term.abstract, SMT.denote, Option.pure_def] using hdenY
  have hDeltaY' : Delta y' = some Wy' := by
    simpa [SMT.Term.abstract, SMT.denote, Option.pure_def] using hdenY'
  simp only [SMT.Term.abstract]
  simp only [hDeltaR, hDeltaX, hDeltaY, hDeltaY', Option.get_some]
  simp only [pfunFunctionalityPHOAS]

private theorem pfunFunctionalityPHOAS_denote.{u}
    {rho sigma : SMTType} {WR Wa Wb Wb' : SMT.Dom.{u}}
    (hWR_ty : WR.snd.fst = SMTType.fun
      (SMTType.pair rho sigma) SMTType.bool)
    (hWa_ty : Wa.snd.fst = rho)
    (hWb_ty : Wb.snd.fst = sigma)
    (hWb'_ty : Wb'.snd.fst = sigma) :
    ∃ D : SMT.Dom.{u},
      ⟦pfunFunctionalityPHOAS WR Wa Wb Wb'⟧ˢ = some D ∧
      D.snd.fst = SMTType.bool ∧
      (D.fst = ZFSet.zftrue ↔
        (Wa.fst.pair Wb.fst).pair ZFSet.zftrue ∈ WR.fst →
        (Wa.fst.pair Wb'.fst).pair ZFSet.zftrue ∈ WR.fst →
          Wb.fst = Wb'.fst) := by
  have hWa_mem : Wa.fst ∈ ⟦rho⟧ᶻ := by
    simpa [hWa_ty] using Wa.snd.snd
  have hWb_mem : Wb.fst ∈ ⟦sigma⟧ᶻ := by
    simpa [hWb_ty] using Wb.snd.snd
  have hWb'_mem : Wb'.fst ∈ ⟦sigma⟧ᶻ := by
    simpa [hWb'_ty] using Wb'.snd.snd
  have hpair_mem : Wa.fst.pair Wb.fst ∈
      ⟦SMTType.pair rho sigma⟧ᶻ := by
    simpa [SMTType.toZFSet] using
      ZFSet.pair_mem_prod.mpr ⟨hWa_mem, hWb_mem⟩
  have hpair'_mem : Wa.fst.pair Wb'.fst ∈
      ⟦SMTType.pair rho sigma⟧ᶻ := by
    simpa [SMTType.toZFSet] using
      ZFSet.pair_mem_prod.mpr ⟨hWa_mem, hWb'_mem⟩
  let Wab : SMT.Dom.{u} :=
    ⟨Wa.fst.pair Wb.fst, SMTType.pair rho sigma, hpair_mem⟩
  let Wab' : SMT.Dom.{u} :=
    ⟨Wa.fst.pair Wb'.fst, SMTType.pair rho sigma, hpair'_mem⟩
  have hden_pair :
      ⟦SMT.PHOAS.Term.pair (.var Wa) (.var Wb)⟧ˢ = some Wab := by
    simp [SMT.denote, Wab, hWa_ty, hWb_ty]
  have hden_pair' :
      ⟦SMT.PHOAS.Term.pair (.var Wa) (.var Wb')⟧ˢ = some Wab' := by
    simp [SMT.denote, Wab', hWa_ty, hWb'_ty]
  obtain ⟨DR, hden_R, hDR_ty, hDR_val⟩ :=
    denote_app_exact_rep_pfun
      (sigma := SMTType.pair rho sigma) (tau := SMTType.bool)
      (tf := .var WR) (tx := .pair (.var Wa) (.var Wb))
      (WF := WR) (WX := Wab) (hdenF := rfl) (hdenX := hden_pair)
      hWR_ty (by rfl)
  obtain ⟨DR', hden_R', hDR'_ty, hDR'_val⟩ :=
    denote_app_exact_rep_pfun
      (sigma := SMTType.pair rho sigma) (tau := SMTType.bool)
      (tf := .var WR) (tx := .pair (.var Wa) (.var Wb'))
      (WF := WR) (WX := Wab') (hdenF := rfl) (hdenX := hden_pair')
      hWR_ty (by rfl)
  obtain ⟨DAnte, hden_ante, hDAnte_ty⟩ :=
    denote_and_some_bool_of_some_bool
      hden_R hDR_ty hden_R' hDR'_ty
  have hbb'_ty : Wb.snd.fst = Wb'.snd.fst :=
    hWb_ty.trans hWb'_ty.symm
  obtain ⟨DEq, hden_eq, hDEq_ty⟩ :=
    denote_eq_some_of_some
      (t₁ := SMT.PHOAS.Term.var Wb)
      (t₂ := SMT.PHOAS.Term.var Wb')
      (D₁ := Wb) (D₂ := Wb') rfl rfl hbb'_ty
  obtain ⟨D, hden_D, hD_ty⟩ :=
    denote_imp_some_bool hden_ante hDAnte_ty hden_eq hDEq_ty
  have hRfunc : ZFSet.IsFunc ⟦SMTType.pair rho sigma⟧ᶻ
      ZFSet.𝔹 WR.fst :=
    ZFSet.mem_funs.mp (by
      simpa [hWR_ty, SMTType.toZFSet] using WR.snd.snd)
  have hR_true_iff : DR.fst = ZFSet.zftrue ↔
      (Wa.fst.pair Wb.fst).pair ZFSet.zftrue ∈ WR.fst := by
    simpa [hDR_val, Wab] using
      (ZFSet.fapply_eq_zftrue_iff_pair hRfunc hpair_mem)
  have hR'_true_iff : DR'.fst = ZFSet.zftrue ↔
      (Wa.fst.pair Wb'.fst).pair ZFSet.zftrue ∈ WR.fst := by
    simpa [hDR'_val, Wab'] using
      (ZFSet.fapply_eq_zftrue_iff_pair hRfunc hpair'_mem)
  have hAnte_true_iff : DAnte.fst = ZFSet.zftrue ↔
      DR.fst = ZFSet.zftrue ∧ DR'.fst = ZFSet.zftrue := by
    constructor
    · exact fun h => denote_and_both_zftrue_of_zftrue
        hden_R hDR_ty hden_R' hDR'_ty hden_ante h
    · exact fun ⟨hR, hR'⟩ => congrArg (·.fst)
        (Option.some.inj (hden_ante.symm.trans
          (denote_and_eq_zftrue_of_some_zftrue
            hden_R hDR_ty hR hden_R' hDR'_ty hR')))
  have hEq_true_iff : DEq.fst = ZFSet.zftrue ↔
      Wb.fst = Wb'.fst := by
    constructor
    · exact fun h => denote_eq_true_implies_fst_eq
        (t₁ := SMT.PHOAS.Term.var Wb)
        (t₂ := SMT.PHOAS.Term.var Wb')
        (D₁ := Wb) (D₂ := Wb') (Deq := DEq)
        rfl rfl hbb'_ty hden_eq h
    · exact fun h => congrArg (·.fst)
        (Option.some.inj (hden_eq.symm.trans
          (denote_eq_eq_zftrue_of_fst_eq
            (t₁ := SMT.PHOAS.Term.var Wb)
            (t₂ := SMT.PHOAS.Term.var Wb')
            (D₁ := Wb) (D₂ := Wb')
            rfl rfl hbb'_ty h)))
  have hAnte_bool : DAnte.fst ∈ ZFSet.𝔹 := by
    simpa [hDAnte_ty] using DAnte.snd.snd
  rw [ZFSet.ZFBool.mem_𝔹_iff] at hAnte_bool
  refine ⟨D, ?_, hD_ty, ?_⟩
  · simpa [pfunFunctionalityPHOAS] using hden_D
  · rw [denote_imp_true_iff hden_ante hDAnte_ty hden_eq hDEq_ty hden_D]
    rcases hAnte_bool with hAnteFalse | hAnteTrue
    · constructor
      · exact fun _ hRmem hR'mem => False.elim
          (ZFSet.zftrue_ne_zffalse
            ((hAnte_true_iff.mpr
              ⟨hR_true_iff.mpr hRmem,
               hR'_true_iff.mpr hR'mem⟩).symm.trans hAnteFalse))
      · exact fun _ => Or.inl hAnteFalse
    · have hRtrue_pair := hAnte_true_iff.mp hAnteTrue
      have hRmem := hR_true_iff.mp hRtrue_pair.1
      have hR'mem := hR'_true_iff.mp hRtrue_pair.2
      simp only [hAnteTrue, ZFSet.zftrue_ne_zffalse,
        hEq_true_iff, hRmem, hR'mem, true_implies, false_or]

private def pfunBodyTerm
    (A B : SMT.Term) (R x y y' : SMT.𝒱)
    (rho sigma : SMTType) : SMT.Term :=
  .and
    (.forall [x, y] [rho, sigma]
      (pfunClosureTerm A B R x y))
    (.forall [x, y, y'] [rho, sigma, sigma]
      (pfunFunctionalityTerm R x y y'))

private theorem pfun_lambda_fv_subset
    (A B : SMT.Term) (R x y y' : SMT.𝒱)
    (rho sigma : SMTType) :
    SMT.fv (SMT.Term.lambda [R]
      [SMTType.fun (SMTType.pair rho sigma) SMTType.bool]
      (pfunBodyTerm A B R x y y' rho sigma)) ⊆
      SMT.fv A ++ SMT.fv B := by
  intro v hv
  simp only [pfunBodyTerm, pfunClosureTerm, pfunFunctionalityTerm,
    SMT.fv, List.mem_removeAll_iff, List.mem_append,
    List.mem_cons, List.mem_nil_iff,
    or_false] at hv ⊢
  aesop

theorem pfunSet_mem_btype.{u} {alpha beta : BType} {X Y : ZFSet.{u}}
    (hX : X ∈ ⟦BType.set alpha⟧ᶻ)
    (hY : Y ∈ ⟦BType.set beta⟧ᶻ) :
    pfunSet X Y ∈ ⟦BType.set (BType.set (alpha ×ᴮ beta))⟧ᶻ := by
  exact ZFSet.prod_sep_is_pfunc_mem
    (ZFSet.mem_powerset.mp hX) (ZFSet.mem_powerset.mp hY)

/-- Functionality of a represented pair predicate reflects back to the
source relation.  Two target representatives of the same source argument are
equal by representation faithfulness, so target functionality identifies
their result representatives; faithfulness then identifies the source
results. -/
theorem RDomCastSupported.setPred_isPFunc_to_source.{u}
    {gamma alpha : BType} {rho sigma : SMTType} {F R : ZFSet.{u}}
    {hF : F ∈ ⟦BType.set (gamma ×ᴮ alpha)⟧ᶻ}
    {hR : R ∈ ⟦SMTType.fun
      (SMTType.pair rho sigma) SMTType.bool⟧ᶻ}
    (Frel : RDomCastSupported
      (⟨F, BType.set (gamma ×ᴮ alpha), hF⟩ : B.Dom)
      (⟨R, SMTType.fun
        (SMTType.pair rho sigma) SMTType.bool, hR⟩ : SMT.Dom))
    (hfun : (predGraph rho sigma R).IsPFunc
      ⟦rho⟧ᶻ ⟦sigma⟧ᶻ) :
    F.IsPFunc ⟦gamma⟧ᶻ ⟦alpha⟧ᶻ := by
  have hFsub : F ⊆ ⟦gamma ×ᴮ alpha⟧ᶻ := by
    simpa [BType.toZFSet] using ZFSet.mem_powerset.mp hF
  constructor
  · exact hFsub
  · intro A B hAB B' hAB'
    obtain ⟨hA, hB⟩ := ZFSet.pair_mem_prod.mp (hFsub hAB)
    obtain ⟨_hA', hB'⟩ := ZFSet.pair_mem_prod.mp (hFsub hAB')
    obtain ⟨ab, hab, ABrel⟩ := Frel.setPred_member_preimage hAB
    obtain ⟨a, ha, b, hb, rfl⟩ := ZFSet.mem_prod.mp hab
    obtain ⟨ab', hab', ABrel'⟩ :=
      Frel.setPred_member_preimage hAB'
    obtain ⟨a', ha', b', hb', rfl⟩ := ZFSet.mem_prod.mp hab'
    obtain ⟨Arel, Brel⟩ := RDomCastSupported.of_pair
      (hX := hA) (hY := hB) (hX' := ha) (hY' := hb) ABrel
    obtain ⟨Arel', Brel'⟩ := RDomCastSupported.of_pair
      (hX := hA) (hY := hB') (hX' := ha') (hY' := hb') ABrel'
    have haa' : a = a' :=
      (castZF_apply_self (castPath.reflexive rho) ha).symm.trans
        ((RDomCastSupported.cast_eq_iff Arel Arel'
          (castPath.reflexive rho)).mpr rfl)
    have hRfunc : ⟦SMTType.pair rho sigma⟧ᶻ.IsFunc ZFSet.𝔹 R := by
      simpa [SMTType.toZFSet] using hR
    have habtrue :=
      (RDomCastSupported.setPred_fapply_eq_zftrue_iff
        ABrel.toRDomCast Frel).mpr hAB
    have habgraph : a.pair b ∈ predGraph rho sigma R := by
      rw [predGraph, ZFSet.mem_sep]
      exact ⟨by simpa [SMTType.toZFSet] using hab,
        (ZFSet.fapply_eq_zftrue_iff_pair hRfunc hab).mp habtrue⟩
    have hab'true :=
      (RDomCastSupported.setPred_fapply_eq_zftrue_iff
        ABrel'.toRDomCast Frel).mpr hAB'
    have hab'graph : a'.pair b' ∈ predGraph rho sigma R := by
      rw [predGraph, ZFSet.mem_sep]
      exact ⟨by simpa [SMTType.toZFSet] using hab',
        (ZFSet.fapply_eq_zftrue_iff_pair hRfunc hab').mp hab'true⟩
    subst a'
    have hbb' : b = b' := hfun.2 a b habgraph b' hab'graph
    exact (RDomCastSupported.cast_eq_iff Brel Brel'
      (castPath.reflexive sigma)).mp
        ((castZF_apply_self (castPath.reflexive sigma) hb).trans hbb')

noncomputable def predTruthSet.{u}
    (rho : SMTType) (F : ZFSet.{u}) : ZFSet.{u} :=
  ⟦rho⟧ᶻ.sep fun x => x.pair ZFSet.zftrue ∈ F

theorem mem_predTruthSet_iff_fapply_eq_zftrue.{u}
    {rho : SMTType} {F x : ZFSet.{u}}
    (hF : F ∈ ⟦SMTType.fun rho SMTType.bool⟧ᶻ)
    (hx : x ∈ ⟦rho⟧ᶻ) :
    x ∈ predTruthSet rho F ↔
      (ZFSet.fapply F (ZFSet.is_func_is_pfunc (by
          simpa [SMTType.toZFSet] using hF :
            ⟦rho⟧ᶻ.IsFunc ZFSet.𝔹 F))
        ⟨x, by
          rw [ZFSet.is_func_dom_eq (by
            simpa [SMTType.toZFSet] using hF :
              ⟦rho⟧ᶻ.IsFunc ZFSet.𝔹 F)]
          exact hx⟩).val = ZFSet.zftrue := by
  rw [predTruthSet, ZFSet.mem_sep, and_iff_right hx]
  exact (ZFSet.fapply_eq_zftrue_iff_pair (by
    simpa [SMTType.toZFSet] using hF) hx).symm

theorem predGraph_isPFunc_iff_pointwise.{u}
    {rho sigma : SMTType} {A B R : ZFSet.{u}} :
    (predGraph rho sigma R).IsPFunc
        (predTruthSet rho A) (predTruthSet sigma B) ↔
      (∀ a, a ∈ ⟦rho⟧ᶻ → ∀ b, b ∈ ⟦sigma⟧ᶻ →
          (a.pair b).pair ZFSet.zftrue ∈ R →
            a.pair ZFSet.zftrue ∈ A ∧
            b.pair ZFSet.zftrue ∈ B) ∧
      ∀ a, a ∈ ⟦rho⟧ᶻ → ∀ b, b ∈ ⟦sigma⟧ᶻ →
        ∀ b', b' ∈ ⟦sigma⟧ᶻ →
          (a.pair b).pair ZFSet.zftrue ∈ R →
          (a.pair b').pair ZFSet.zftrue ∈ R → b = b' := by
  constructor
  · intro h
    constructor
    · intro a ha b hb habR
      have habGraph : a.pair b ∈ predGraph rho sigma R := by
        rw [predGraph, ZFSet.mem_sep]
        exact ⟨ZFSet.pair_mem_prod.mpr ⟨ha, hb⟩, habR⟩
      have htruth := h.1 habGraph
      obtain ⟨haTruth, hbTruth⟩ := ZFSet.pair_mem_prod.mp htruth
      exact ⟨(ZFSet.mem_sep.mp haTruth).2,
        (ZFSet.mem_sep.mp hbTruth).2⟩
    · intro a ha b hb b' hb' habR habR'
      apply h.2 a b
      · rw [predGraph, ZFSet.mem_sep]
        exact ⟨ZFSet.pair_mem_prod.mpr ⟨ha, hb⟩, habR⟩
      · rw [predGraph, ZFSet.mem_sep]
        exact ⟨ZFSet.pair_mem_prod.mpr ⟨ha, hb'⟩, habR'⟩
  · intro h
    constructor
    · intro ab habGraph
      rw [predGraph, ZFSet.mem_sep] at habGraph
      obtain ⟨a, ha, b, hb, rfl⟩ := ZFSet.mem_prod.mp habGraph.1
      obtain ⟨haA, hbB⟩ := h.1 a ha b hb habGraph.2
      rw [ZFSet.pair_mem_prod]
      exact ⟨ZFSet.mem_sep.mpr ⟨ha, haA⟩,
        ZFSet.mem_sep.mpr ⟨hb, hbB⟩⟩
    · intro a b hab b' hab'
      rw [predGraph, ZFSet.mem_sep] at hab hab'
      obtain ⟨ha, hb⟩ := ZFSet.pair_mem_prod.mp hab.1
      obtain ⟨_ha', hb'⟩ := ZFSet.pair_mem_prod.mp hab'.1
      exact h.2 a ha b hb b' hb' hab.2 hab'.2

open Classical in
theorem represented_setPred_pfun_of_pointwise.{u}
    {alpha beta : BType} {rho sigma : SMTType}
    (hrho : BType.SupportedSMT alpha rho)
    (hsigma : BType.SupportedSMT beta sigma)
    {X Y A B U : ZFSet.{u}}
    (hX : X ∈ ⟦BType.set alpha⟧ᶻ)
    (hY : Y ∈ ⟦BType.set beta⟧ᶻ)
    (hA : A ∈ ⟦SMTType.fun rho SMTType.bool⟧ᶻ)
    (hB : B ∈ ⟦SMTType.fun sigma SMTType.bool⟧ᶻ)
    (hU : U ∈ ⟦SMTType.fun
      (SMTType.fun (SMTType.pair rho sigma) SMTType.bool)
      SMTType.bool⟧ᶻ)
    (Xrel : RDomCastSupported
      (⟨X, BType.set alpha, hX⟩ : _root_.B.Dom)
      (⟨A, SMTType.fun rho SMTType.bool, hA⟩ : SMT.Dom))
    (Yrel : RDomCastSupported
      (⟨Y, BType.set beta, hY⟩ : _root_.B.Dom)
      (⟨B, SMTType.fun sigma SMTType.bool, hB⟩ : SMT.Dom))
    (hpoint : ∀ (R : ZFSet.{u})
      (hR : R ∈ ⟦SMTType.fun
        (SMTType.pair rho sigma) SMTType.bool⟧ᶻ),
      (ZFSet.fapply U (ZFSet.is_func_is_pfunc (by
          simpa [SMTType.toZFSet] using hU :
            ZFSet.IsFunc
              ⟦SMTType.fun (SMTType.pair rho sigma) SMTType.bool⟧ᶻ
              ZFSet.𝔹 U))
        ⟨R, by
          rw [ZFSet.is_func_dom_eq (by
            simpa [SMTType.toZFSet] using hU :
              ZFSet.IsFunc
                ⟦SMTType.fun (SMTType.pair rho sigma) SMTType.bool⟧ᶻ
                ZFSet.𝔹 U)]
          exact hR⟩).val = ZFSet.zftrue ↔
        (predGraph rho sigma R).IsPFunc
          (predTruthSet rho A) (predTruthSet sigma B)) :
    RDomCastSupported
      (⟨pfunSet X Y, BType.set (BType.set (alpha ×ᴮ beta)),
        pfunSet_mem_btype hX hY⟩ : _root_.B.Dom)
      (⟨U, SMTType.fun
        (SMTType.fun (SMTType.pair rho sigma) SMTType.bool)
        SMTType.bool, hU⟩ : SMT.Dom) := by
  have hPFunSub : pfunSet X Y ⊆
      ⟦BType.set (alpha ×ᴮ beta)⟧ᶻ := by
    simpa [BType.toZFSet] using ZFSet.mem_powerset.mp
      (pfunSet_mem_btype hX hY)
  have hUfunc : ZFSet.IsFunc
      ⟦SMTType.fun (SMTType.pair rho sigma) SMTType.bool⟧ᶻ
      ZFSet.𝔹 U := by
    simpa [SMTType.toZFSet] using hU
  apply RDomCastSupported.setPred_of_pointwise
    (.setPred (.prod hrho hsigma)) hPFunSub hU hUfunc
  · intro R hR hUtrue
    obtain ⟨F, hF, Frel⟩ :=
      supported_target_preimage (.setPred (.prod hrho hsigma)) R hR
    have htarget := (hpoint R hR).mp hUtrue
    have htargetFull : (predGraph rho sigma R).IsPFunc
        ⟦rho⟧ᶻ ⟦sigma⟧ᶻ := by
      constructor
      · intro ab hab
        obtain ⟨a, ha, b, hb, rfl⟩ :=
          ZFSet.mem_prod.mp (htarget.1 hab)
        exact ZFSet.pair_mem_prod.mpr
          ⟨(ZFSet.mem_sep.mp ha).1, (ZFSet.mem_sep.mp hb).1⟩
      · exact htarget.2
    have hFfunType :=
      RDomCastSupported.setPred_isPFunc_to_source Frel htargetFull
    have hFsubXY : F ⊆ X.prod Y := by
      intro AB hAB
      obtain ⟨AA, hAA, BB, hBB, rfl⟩ :=
        ZFSet.mem_prod.mp (hFfunType.1 hAB)
      obtain ⟨ab, hab, ABrel⟩ :=
        Frel.setPred_member_preimage hAB
      obtain ⟨a, ha, b, hb, rfl⟩ := ZFSet.mem_prod.mp hab
      obtain ⟨AArel, BBrel⟩ := RDomCastSupported.of_pair
        (hX := hAA) (hY := hBB) (hX' := ha) (hY' := hb) ABrel
      have hRtrue :=
        (RDomCastSupported.setPred_fapply_eq_zftrue_iff
          ABrel.toRDomCast Frel).mpr hAB
      have hRfunc : ZFSet.IsFunc
          ⟦SMTType.pair rho sigma⟧ᶻ ZFSet.𝔹 R := by
        simpa [SMTType.toZFSet] using hR
      have habGraph : a.pair b ∈ predGraph rho sigma R := by
        rw [predGraph, ZFSet.mem_sep]
        exact ⟨by simpa [SMTType.toZFSet] using hab,
          (ZFSet.fapply_eq_zftrue_iff_pair hRfunc hab).mp hRtrue⟩
      obtain ⟨haTruth, hbTruth⟩ :=
        ZFSet.pair_mem_prod.mp (htarget.1 habGraph)
      have hAtrue :=
        (mem_predTruthSet_iff_fapply_eq_zftrue hA ha).mp haTruth
      have hBtrue :=
        (mem_predTruthSet_iff_fapply_eq_zftrue hB hb).mp hbTruth
      obtain ⟨AA', hAA'X, AA'rel⟩ :=
        Xrel.setPred_target_of_true ha hAtrue
      obtain ⟨BB', hBB'Y, BB'rel⟩ :=
        Yrel.setPred_target_of_true hb hBtrue
      have hAAeq : AA = AA' :=
        (RDomCast.target_value_eq_iff
          AArel.toRDomCast AA'rel.toRDomCast).mp rfl
      have hBBeq : BB = BB' :=
        (RDomCast.target_value_eq_iff
          BBrel.toRDomCast BB'rel.toRDomCast).mp rfl
      rw [hAAeq, hBBeq]
      exact ZFSet.pair_mem_prod.mpr ⟨hAA'X, hBB'Y⟩
    have hFpfun : F.IsPFunc X Y := ⟨hFsubXY, hFfunType.2⟩
    have hFmem : F ∈ pfunSet X Y := by
      rw [pfunSet, ZFSet.mem_sep]
      exact ⟨ZFSet.mem_powerset.mpr hFsubXY, hFpfun⟩
    exact ⟨F, hFmem, by simpa only [proof_irrel_heq] using Frel⟩
  · intro F hFmem
    have hFmem0 := hFmem
    rw [pfunSet, ZFSet.mem_sep] at hFmem
    obtain ⟨hFpow, hFfunXY⟩ := hFmem
    have hFsubXY : F ⊆ X.prod Y := ZFSet.mem_powerset.mp hFpow
    have hFtype : F ∈ ⟦BType.set (alpha ×ᴮ beta)⟧ᶻ :=
      hPFunSub hFmem0
    let hpair : BType.SupportedSMT (alpha ×ᴮ beta)
        (SMTType.pair rho sigma) := .prod hrho hsigma
    let c := hpair.canonicalCastPath
    let body : ZFSet.{u} → ZFSet.{u} := fun ab =>
      if retract (alpha ×ᴮ beta) (castZF_apply c ab) ∈ F
      then ZFSet.zftrue else ZFSet.zffalse
    let R : ZFSet.{u} := ZFSet.lambda
      ⟦SMTType.pair rho sigma⟧ᶻ ZFSet.𝔹 body
    have body_mem : ∀ {ab : ZFSet.{u}},
        ab ∈ ⟦SMTType.pair rho sigma⟧ᶻ → body ab ∈ ZFSet.𝔹 := by
      intro ab hab
      simp only [body]
      split <;> simp
    have R_func : ZFSet.IsFunc
        ⟦SMTType.pair rho sigma⟧ᶻ ZFSet.𝔹 R := by
      exact ZFSet.lambda_isFunc (fun {ab} hab => body_mem hab)
    have hR : R ∈ ⟦SMTType.fun
        (SMTType.pair rho sigma) SMTType.bool⟧ᶻ := by
      simpa [SMTType.toZFSet] using R_func
    have hFsubType : F ⊆ ⟦alpha ×ᴮ beta⟧ᶻ := by
      simpa [BType.toZFSet] using ZFSet.mem_powerset.mp hFtype
    have Frel : RDomCastSupported
        (⟨F, BType.set (alpha ×ᴮ beta), hFtype⟩ : _root_.B.Dom)
        (⟨R, SMTType.fun (SMTType.pair rho sigma) SMTType.bool,
          hR⟩ : SMT.Dom) := by
      apply RDomCastSupported.setPred_of_pointwise
        hpair hFsubType hR R_func
      · intro ab hab htrue
        let AB := retract (alpha ×ᴮ beta) (castZF_apply c ab)
        have hcast : castZF_apply c ab ∈
            ⟦(alpha ×ᴮ beta).toSMTType⟧ᶻ :=
          castZF_apply_mem c hab
        have hABtype : AB ∈ ⟦alpha ×ᴮ beta⟧ᶻ :=
          retract_mem_of_canonical (alpha ×ᴮ beta) hcast
        have happ := ZFSet.fapply_lambda
          (hf := fun {z} hz => body_mem hz) (ha := hab)
        have hABF : AB ∈ F := by
          have hbody : body ab = ZFSet.zftrue := by
            exact happ.symm.trans htrue
          by_contra hnot
          change ¬ retract (alpha ×ᴮ beta)
            (castZF_apply c ab) ∈ F at hnot
          have hfalse : body ab = ZFSet.zffalse := by
            simp [body, hnot]
          exact ZFSet.zftrue_ne_zffalse (hbody.symm.trans hfalse)
        have bare : RDomCast
            (⟨AB, alpha ×ᴮ beta, hABtype⟩ : _root_.B.Dom)
            (⟨ab, SMTType.pair rho sigma, hab⟩ : SMT.Dom) :=
          ⟨c, rfl⟩
        exact ⟨AB, hABF,
          ⟨bare.toRDomCastAdmissible_of_supported hpair, hpair⟩⟩
      · intro AB hAB
        obtain ⟨AA, hAAX, BB, hBBY, rfl⟩ :=
          ZFSet.mem_prod.mp (hFsubXY hAB)
        obtain ⟨a, ha, AArel⟩ :=
          Xrel.setPred_member_preimage hAAX
        obtain ⟨b, hb, BBrel⟩ :=
          Yrel.setPred_member_preimage hBBY
        have hab : a.pair b ∈ ⟦SMTType.pair rho sigma⟧ᶻ :=
          ZFSet.pair_mem_prod.mpr ⟨ha, hb⟩
        have ABrel := RDomCastSupported.pair AArel BBrel
        refine ⟨a.pair b, hab, ?_, ?_⟩
        · simpa only [proof_irrel_heq] using ABrel
        · have happ := ZFSet.fapply_lambda
            (hf := fun {z} hz => body_mem hz) (ha := hab)
          have hret : retract (alpha ×ᴮ beta)
              (castZF_apply c (a.pair b)) = AA.pair BB := by
            obtain ⟨c', hc'⟩ := ABrel.toRDomCast
            have hcc : c' = c := castPath.eq_of_endpoints c' c
            subst c'
            exact hc'
          have hbody : body (a.pair b) = ZFSet.zftrue := by
            simp [body, hret, hAB]
          exact happ.trans hbody
    have hXsub : X ⊆ ⟦alpha⟧ᶻ := by
      simpa [BType.toZFSet] using ZFSet.mem_powerset.mp hX
    have hYsub : Y ⊆ ⟦beta⟧ᶻ := by
      simpa [BType.toZFSet] using ZFSet.mem_powerset.mp hY
    have hFfunType : F.IsPFunc ⟦alpha⟧ᶻ ⟦beta⟧ᶻ := by
      constructor
      · simpa [BType.toZFSet] using hFsubType
      · exact hFfunXY.2
    have hTargetFunFull : (predGraph rho sigma R).IsPFunc
        ⟦rho⟧ᶻ ⟦sigma⟧ᶻ := by
      exact RDomCastSupported.setPred_isPFunc_of_source Frel hFfunType
    have hTargetSub : predGraph rho sigma R ⊆
        (predTruthSet rho A).prod (predTruthSet sigma B) := by
      intro ab habGraph
      rw [predGraph, ZFSet.mem_sep] at habGraph
      obtain ⟨a, ha, b, hb, rfl⟩ := ZFSet.mem_prod.mp habGraph.1
      have hab : a.pair b ∈ ⟦SMTType.pair rho sigma⟧ᶻ := by
        exact ZFSet.pair_mem_prod.mpr ⟨ha, hb⟩
      have hRtrue :=
        (ZFSet.fapply_eq_zftrue_iff_pair R_func hab).mpr habGraph.2
      obtain ⟨AB, hABF, ABrel⟩ :=
        Frel.setPred_target_of_true hab hRtrue
      obtain ⟨AA, hAAX, BB, hBBY, rfl⟩ :=
        ZFSet.mem_prod.mp (hFsubXY hABF)
      obtain ⟨AArel, BBrel⟩ := RDomCastSupported.of_pair
        (hX := hXsub hAAX) (hY := hYsub hBBY)
        (hX' := ha) (hY' := hb) ABrel
      have hAtrue :=
        (RDomCastSupported.setPred_fapply_eq_zftrue_iff
          AArel.toRDomCast Xrel).mpr hAAX
      have hBtrue :=
        (RDomCastSupported.setPred_fapply_eq_zftrue_iff
          BBrel.toRDomCast Yrel).mpr hBBY
      rw [ZFSet.pair_mem_prod]
      constructor
      · exact (mem_predTruthSet_iff_fapply_eq_zftrue hA ha).mpr hAtrue
      · exact (mem_predTruthSet_iff_fapply_eq_zftrue hB hb).mpr hBtrue
    have hTarget : (predGraph rho sigma R).IsPFunc
        (predTruthSet rho A) (predTruthSet sigma B) :=
      ⟨hTargetSub, hTargetFunFull.2⟩
    have hUtrue := (hpoint R hR).mpr hTarget
    refine ⟨R, hR, ?_, hUtrue⟩
    simpa only [proof_irrel_heq] using Frel

open Classical in
private theorem represented_pfun_direct_lambda.{u}
    {alpha beta : BType} {rho sigma : SMTType}
    (hrho : BType.SupportedSMT alpha rho)
    (hsigma : BType.SupportedSMT beta sigma)
    {A B : SMT.Term} {R x y y' : SMT.𝒱}
    {Theta : SMT.RenamingContext.Context.{u}}
    {X Y Aval Bval U : ZFSet.{u}}
    (hX : X ∈ ⟦BType.set alpha⟧ᶻ)
    (hY : Y ∈ ⟦BType.set beta⟧ᶻ)
    (hAval : Aval ∈ ⟦SMTType.fun rho SMTType.bool⟧ᶻ)
    (hBval : Bval ∈ ⟦SMTType.fun sigma SMTType.bool⟧ᶻ)
    (hU : U ∈ ⟦SMTType.fun
      (SMTType.fun (SMTType.pair rho sigma) SMTType.bool)
      SMTType.bool⟧ᶻ)
    (R_not_fv_A : R ∉ SMT.fv A) (R_not_fv_B : R ∉ SMT.fv B)
    (x_not_fv_A : x ∉ SMT.fv A) (x_not_fv_B : x ∉ SMT.fv B)
    (y_not_fv_A : y ∉ SMT.fv A) (y_not_fv_B : y ∉ SMT.fv B)
    (hR_ne_x : R ≠ x) (hR_ne_y : R ≠ y) (hR_ne_y' : R ≠ y')
    (hx_ne_y : x ≠ y) (hx_ne_y' : x ≠ y') (hy_ne_y' : y ≠ y')
    (hcovA : SMT.RenamingContext.CoversFV Theta A)
    (hcovB : SMT.RenamingContext.CoversFV Theta B)
    (hdenA : ⟦A.abstract Theta hcovA⟧ˢ =
      some (⟨Aval, SMTType.fun rho SMTType.bool, hAval⟩ : SMT.Dom))
    (hdenB : ⟦B.abstract Theta hcovB⟧ˢ =
      some (⟨Bval, SMTType.fun sigma SMTType.bool, hBval⟩ : SMT.Dom))
    (Xrel : RDomCastSupported
      (⟨X, BType.set alpha, hX⟩ : _root_.B.Dom)
      (⟨Aval, SMTType.fun rho SMTType.bool, hAval⟩ : SMT.Dom))
    (Yrel : RDomCastSupported
      (⟨Y, BType.set beta, hY⟩ : _root_.B.Dom)
      (⟨Bval, SMTType.fun sigma SMTType.bool, hBval⟩ : SMT.Dom))
    (hcovOut : SMT.RenamingContext.CoversFV Theta
      (SMT.Term.lambda [R]
        [SMTType.fun (SMTType.pair rho sigma) SMTType.bool]
        (pfunBodyTerm A B R x y y' rho sigma)))
    (hdenOut :
      ⟦(SMT.Term.lambda [R]
        [SMTType.fun (SMTType.pair rho sigma) SMTType.bool]
        (pfunBodyTerm A B R x y y' rho sigma)).abstract
          Theta hcovOut⟧ˢ =
        some (⟨U, SMTType.fun
          (SMTType.fun (SMTType.pair rho sigma) SMTType.bool)
          SMTType.bool, hU⟩ : SMT.Dom)) :
    RDomCastSupported
      (⟨pfunSet X Y, BType.set (BType.set (alpha ×ᴮ beta)),
        pfunSet_mem_btype hX hY⟩ : _root_.B.Dom)
      (⟨U, SMTType.fun
        (SMTType.fun (SMTType.pair rho sigma) SMTType.bool)
        SMTType.bool, hU⟩ : SMT.Dom) := by
  apply represented_setPred_pfun_of_pointwise
    hrho hsigma hX hY hAval hBval hU Xrel Yrel
  intro Rval hRval
  let tauR := SMTType.fun (SMTType.pair rho sigma) SMTType.bool
  let WR : SMT.Dom.{u} := ⟨Rval, tauR, hRval⟩
  let ThetaR := Function.update Theta R (some WR)
  have hUfunc : ZFSet.IsFunc ⟦tauR⟧ᶻ ZFSet.𝔹 U := by
    simpa [tauR, SMTType.toZFSet] using hU
  have hcovBodyR : SMT.RenamingContext.CoversFV ThetaR
      (pfunBodyTerm A B R x y y' rho sigma) := by
    intro v hv
    by_cases hvR : v = R
    · subst v
      simp [ThetaR, Function.update_self]
    · simp only [ThetaR, Function.update_of_ne hvR]
      exact hcovOut v (SMT.fv.mem_lambda ⟨hv, by simp [hvR]⟩)
  have hcovP1 : SMT.RenamingContext.CoversFV ThetaR
      (SMT.Term.forall [x, y] [rho, sigma]
        (pfunClosureTerm A B R x y)) := by
    intro v hv
    exact hcovBodyR v (by
      rw [pfunBodyTerm]
      exact SMT.fv.mem_and (Or.inl hv))
  have hcovP2 : SMT.RenamingContext.CoversFV ThetaR
      (SMT.Term.forall [x, y, y'] [rho, sigma, sigma]
        (pfunFunctionalityTerm R x y y')) := by
    intro v hv
    exact hcovBodyR v (by
      rw [pfunBodyTerm]
      exact SMT.fv.mem_and (Or.inr hv))
  have hgoP1 : ∀ v, v ∈ SMT.fv (pfunClosureTerm A B R x y) →
      v ∉ [x, y] → (ThetaR v).isSome = true := by
    intro v hv hnot
    exact hcovP1 v (SMT.fv.mem_forall ⟨hv, hnot⟩)
  have hgoP2 : ∀ v, v ∈ SMT.fv (pfunFunctionalityTerm R x y y') →
      v ∉ [x, y, y'] → (ThetaR v).isSome = true := by
    intro v hv hnot
    exact hcovP2 v (SMT.fv.mem_forall ⟨hv, hnot⟩)
  have hcovClosure : ∀ Wa Wb : SMT.Dom.{u},
      SMT.RenamingContext.CoversFV
        (Function.update (Function.update ThetaR x (some Wa)) y (some Wb))
        (pfunClosureTerm A B R x y) := by
    intro Wa Wb v hv
    by_cases hvy : v = y
    · subst v
      simp [Function.update_self]
    · by_cases hvx : v = x
      · subst v
        simp [Function.update_of_ne hx_ne_y, Function.update_self]
      · simp only [Function.update_of_ne hvy, Function.update_of_ne hvx]
        exact hgoP1 v hv (by simp [hvx, hvy])
  have hcovFunctionality : ∀ Wa Wb Wb' : SMT.Dom.{u},
      SMT.RenamingContext.CoversFV
        (Function.update
          (Function.update (Function.update ThetaR x (some Wa)) y (some Wb))
          y' (some Wb'))
        (pfunFunctionalityTerm R x y y') := by
    intro Wa Wb Wb' v hv
    by_cases hvy' : v = y'
    · subst v
      simp [Function.update_self]
    · by_cases hvy : v = y
      · subst v
        simp [Function.update_of_ne hy_ne_y', Function.update_self]
      · by_cases hvx : v = x
        · subst v
          simp [Function.update_of_ne hx_ne_y',
            Function.update_of_ne hx_ne_y, Function.update_self]
        · simp only [Function.update_of_ne hvy', Function.update_of_ne hvy,
            Function.update_of_ne hvx]
          exact hgoP2 v hv (by simp [hvx, hvy, hvy'])
  have hcovA_R : SMT.RenamingContext.CoversFV ThetaR A := by
    exact SMT.RenamingContext.coversFV_update_of_notMem R_not_fv_A hcovA
  have hdenA_R : ⟦A.abstract ThetaR hcovA_R⟧ˢ =
      some (⟨Aval, SMTType.fun rho SMTType.bool, hAval⟩ : SMT.Dom) := by
    have hEq := SMT.RenamingContext.denote_update_of_notMem
      («Δ» := Theta) (t := A) (x := R) (d := WR)
      (h := hcovA) R_not_fv_A
    simpa [ThetaR, SMT.RenamingContext.denote] using hEq.symm.trans hdenA
  have hcovB_R : SMT.RenamingContext.CoversFV ThetaR B := by
    exact SMT.RenamingContext.coversFV_update_of_notMem R_not_fv_B hcovB
  have hdenB_R : ⟦B.abstract ThetaR hcovB_R⟧ˢ =
      some (⟨Bval, SMTType.fun sigma SMTType.bool, hBval⟩ : SMT.Dom) := by
    have hEq := SMT.RenamingContext.denote_update_of_notMem
      («Δ» := Theta) (t := B) (x := R) (d := WR)
      (h := hcovB) R_not_fv_B
    simpa [ThetaR, SMT.RenamingContext.denote] using hEq.symm.trans hdenB
  have hdenAClosure : ∀ Wa Wb : SMT.Dom.{u},
      ∃ hcovAxy : SMT.RenamingContext.CoversFV
          (Function.update (Function.update ThetaR x (some Wa)) y (some Wb)) A,
        ⟦A.abstract
          (Function.update (Function.update ThetaR x (some Wa)) y (some Wb))
          hcovAxy⟧ˢ =
          some (⟨Aval, SMTType.fun rho SMTType.bool, hAval⟩ : SMT.Dom) := by
    intro Wa Wb
    let hcovAx := SMT.RenamingContext.coversFV_update_of_notMem
      (x := x) (d := Wa) x_not_fv_A hcovA_R
    let hcovAxy := SMT.RenamingContext.coversFV_update_of_notMem
      (x := y) (d := Wb) y_not_fv_A hcovAx
    refine ⟨hcovAxy, ?_⟩
    have hEqx := SMT.RenamingContext.denote_update_of_notMem
      («Δ» := ThetaR) (t := A) (x := x) (d := Wa)
      (h := hcovA_R) x_not_fv_A
    have hEqy := SMT.RenamingContext.denote_update_of_notMem
      («Δ» := Function.update ThetaR x (some Wa))
      (t := A) (x := y) (d := Wb) (h := hcovAx) y_not_fv_A
    simpa [SMT.RenamingContext.denote, proof_irrel_heq] using
      hEqy.symm.trans (hEqx.symm.trans hdenA_R)
  have hdenBClosure : ∀ Wa Wb : SMT.Dom.{u},
      ∃ hcovBxy : SMT.RenamingContext.CoversFV
          (Function.update (Function.update ThetaR x (some Wa)) y (some Wb)) B,
        ⟦B.abstract
          (Function.update (Function.update ThetaR x (some Wa)) y (some Wb))
          hcovBxy⟧ˢ =
          some (⟨Bval, SMTType.fun sigma SMTType.bool, hBval⟩ : SMT.Dom) := by
    intro Wa Wb
    let hcovBx := SMT.RenamingContext.coversFV_update_of_notMem
      (x := x) (d := Wa) x_not_fv_B hcovB_R
    let hcovBxy := SMT.RenamingContext.coversFV_update_of_notMem
      (x := y) (d := Wb) y_not_fv_B hcovBx
    refine ⟨hcovBxy, ?_⟩
    have hEqx := SMT.RenamingContext.denote_update_of_notMem
      («Δ» := ThetaR) (t := B) (x := x) (d := Wa)
      (h := hcovB_R) x_not_fv_B
    have hEqy := SMT.RenamingContext.denote_update_of_notMem
      («Δ» := Function.update ThetaR x (some Wa))
      (t := B) (x := y) (d := Wb) (h := hcovBx) y_not_fv_B
    simpa [SMT.RenamingContext.denote, proof_irrel_heq] using
      hEqy.symm.trans (hEqx.symm.trans hdenB_R)
  have closureData : ∀ Wa Wb : SMT.Dom.{u},
      Wa.snd.fst = rho → Wb.snd.fst = sigma →
      ∃ D : SMT.Dom.{u},
        ⟦(pfunClosureTerm A B R x y).abstract
          (Function.update (Function.update ThetaR x (some Wa)) y (some Wb))
          (hcovClosure Wa Wb)⟧ˢ = some D ∧
        D.snd.fst = SMTType.bool ∧
        (D.fst = ZFSet.zftrue ↔
          (Wa.fst.pair Wb.fst).pair ZFSet.zftrue ∈ Rval →
            Wa.fst.pair ZFSet.zftrue ∈ Aval ∧
            Wb.fst.pair ZFSet.zftrue ∈ Bval) := by
    intro Wa Wb hWa_ty hWb_ty
    let DeltaXY :=
      Function.update (Function.update ThetaR x (some Wa)) y (some Wb)
    let WA : SMT.Dom.{u} :=
      ⟨Aval, SMTType.fun rho SMTType.bool, hAval⟩
    let WB : SMT.Dom.{u} :=
      ⟨Bval, SMTType.fun sigma SMTType.bool, hBval⟩
    obtain ⟨hcovAxy, hdenAxy⟩ := hdenAClosure Wa Wb
    obtain ⟨hcovBxy, hdenBxy⟩ := hdenBClosure Wa Wb
    have hcovRxy : SMT.RenamingContext.CoversFV DeltaXY
        (SMT.Term.var R) := by
      intro v hv
      have hvR : v = R := by simpa [SMT.fv] using hv
      subst v
      simp [DeltaXY, ThetaR, Function.update_of_ne hR_ne_y,
        Function.update_of_ne hR_ne_x, Function.update_self]
    have hcovXxy : SMT.RenamingContext.CoversFV DeltaXY
        (SMT.Term.var x) := by
      intro v hv
      have hvx : v = x := by simpa [SMT.fv] using hv
      subst v
      simp [DeltaXY, Function.update_of_ne hx_ne_y,
        Function.update_self]
    have hcovYxy : SMT.RenamingContext.CoversFV DeltaXY
        (SMT.Term.var y) := by
      intro v hv
      have hvy : v = y := by simpa [SMT.fv] using hv
      subst v
      simp [DeltaXY, Function.update_self]
    have hdenRxy :
        ⟦(SMT.Term.var R).abstract DeltaXY hcovRxy⟧ˢ = some WR := by
      simp [SMT.Term.abstract, SMT.denote, DeltaXY, ThetaR,
        Function.update_of_ne hR_ne_y, Function.update_of_ne hR_ne_x,
        Function.update_self]
    have hdenXxy :
        ⟦(SMT.Term.var x).abstract DeltaXY hcovXxy⟧ˢ = some Wa := by
      simp [SMT.Term.abstract, SMT.denote, DeltaXY,
        Function.update_of_ne hx_ne_y, Function.update_self]
    have hdenYxy :
        ⟦(SMT.Term.var y).abstract DeltaXY hcovYxy⟧ˢ = some Wb := by
      simp [SMT.Term.abstract, SMT.denote, DeltaXY, Function.update_self]
    have hdenTerm := pfunClosureTerm_denote_of_leaves
      (hcovBody := hcovClosure Wa Wb)
      (hcovR := hcovRxy) (hcovA := hcovAxy) (hcovB := hcovBxy)
      (hcovX := hcovXxy) (hcovY := hcovYxy)
      (hdenR := hdenRxy) (hdenA := hdenAxy) (hdenB := hdenBxy)
      (hdenX := hdenXxy) (hdenY := hdenYxy)
    obtain ⟨D, hdenD, hD_ty, hD_iff⟩ :=
      pfunClosurePHOAS_denote
        (WR := WR) (WA := WA) (WB := WB) (Wa := Wa) (Wb := Wb)
        (rho := rho) (sigma := sigma) (by rfl) (by rfl) (by rfl)
        hWa_ty hWb_ty
    refine ⟨D, ?_, hD_ty, ?_⟩
    · simpa [DeltaXY, WA, WB] using hdenTerm.trans hdenD
    · simpa [WR, WA, WB] using hD_iff
  have functionalityData : ∀ Wa Wb Wb' : SMT.Dom.{u},
      Wa.snd.fst = rho → Wb.snd.fst = sigma →
      Wb'.snd.fst = sigma →
      ∃ D : SMT.Dom.{u},
        ⟦(pfunFunctionalityTerm R x y y').abstract
          (Function.update
            (Function.update (Function.update ThetaR x (some Wa)) y (some Wb))
            y' (some Wb'))
          (hcovFunctionality Wa Wb Wb')⟧ˢ = some D ∧
        D.snd.fst = SMTType.bool ∧
        (D.fst = ZFSet.zftrue ↔
          (Wa.fst.pair Wb.fst).pair ZFSet.zftrue ∈ Rval →
          (Wa.fst.pair Wb'.fst).pair ZFSet.zftrue ∈ Rval →
            Wb.fst = Wb'.fst) := by
    intro Wa Wb Wb' hWa_ty hWb_ty hWb'_ty
    let DeltaXYY := Function.update
      (Function.update (Function.update ThetaR x (some Wa)) y (some Wb))
      y' (some Wb')
    have hcovRxyy : SMT.RenamingContext.CoversFV DeltaXYY
        (SMT.Term.var R) := by
      intro v hv
      have hvR : v = R := by simpa [SMT.fv] using hv
      subst v
      simp [DeltaXYY, ThetaR, Function.update_of_ne hR_ne_y',
        Function.update_of_ne hR_ne_y, Function.update_of_ne hR_ne_x,
        Function.update_self]
    have hcovXxyy : SMT.RenamingContext.CoversFV DeltaXYY
        (SMT.Term.var x) := by
      intro v hv
      have hvx : v = x := by simpa [SMT.fv] using hv
      subst v
      simp [DeltaXYY, Function.update_of_ne hx_ne_y',
        Function.update_of_ne hx_ne_y, Function.update_self]
    have hcovYxyy : SMT.RenamingContext.CoversFV DeltaXYY
        (SMT.Term.var y) := by
      intro v hv
      have hvy : v = y := by simpa [SMT.fv] using hv
      subst v
      simp [DeltaXYY, Function.update_of_ne hy_ne_y',
        Function.update_self]
    have hcovY'xyy : SMT.RenamingContext.CoversFV DeltaXYY
        (SMT.Term.var y') := by
      intro v hv
      have hvy' : v = y' := by simpa [SMT.fv] using hv
      subst v
      simp [DeltaXYY, Function.update_self]
    have hdenRxyy :
        ⟦(SMT.Term.var R).abstract DeltaXYY hcovRxyy⟧ˢ = some WR := by
      simp [SMT.Term.abstract, SMT.denote, DeltaXYY, ThetaR,
        Function.update_of_ne hR_ne_y', Function.update_of_ne hR_ne_y,
        Function.update_of_ne hR_ne_x, Function.update_self]
    have hdenXxyy :
        ⟦(SMT.Term.var x).abstract DeltaXYY hcovXxyy⟧ˢ = some Wa := by
      simp [SMT.Term.abstract, SMT.denote, DeltaXYY,
        Function.update_of_ne hx_ne_y', Function.update_of_ne hx_ne_y,
        Function.update_self]
    have hdenYxyy :
        ⟦(SMT.Term.var y).abstract DeltaXYY hcovYxyy⟧ˢ = some Wb := by
      simp [SMT.Term.abstract, SMT.denote, DeltaXYY,
        Function.update_of_ne hy_ne_y', Function.update_self]
    have hdenY'xyy :
        ⟦(SMT.Term.var y').abstract DeltaXYY hcovY'xyy⟧ˢ = some Wb' := by
      simp [SMT.Term.abstract, SMT.denote, DeltaXYY, Function.update_self]
    have hdenTerm := pfunFunctionalityTerm_denote_of_leaves
      (hcovBody := hcovFunctionality Wa Wb Wb')
      (hcovR := hcovRxyy) (hcovX := hcovXxyy)
      (hcovY := hcovYxyy) (hcovY' := hcovY'xyy)
      (hdenR := hdenRxyy) (hdenX := hdenXxyy)
      (hdenY := hdenYxyy) (hdenY' := hdenY'xyy)
    obtain ⟨D, hdenD, hD_ty, hD_iff⟩ :=
      pfunFunctionalityPHOAS_denote
        (WR := WR) (Wa := Wa) (Wb := Wb) (Wb' := Wb')
        (rho := rho) (sigma := sigma) (by rfl) hWa_ty hWb_ty hWb'_ty
    refine ⟨D, ?_, hD_ty, ?_⟩
    · simpa [DeltaXYY] using hdenTerm.trans hdenD
    · simpa [WR] using hD_iff
  let closureQ : SMT.Dom.{u} → SMT.Dom.{u} → Prop := fun Wa Wb =>
    (Wa.fst.pair Wb.fst).pair ZFSet.zftrue ∈ Rval →
      Wa.fst.pair ZFSet.zftrue ∈ Aval ∧
      Wb.fst.pair ZFSet.zftrue ∈ Bval
  obtain ⟨DP1, hdenP1, hDP1_ty, hDP1_iff⟩ :=
    funBinaryForallIffZftrue closureQ hcovP1 hgoP1 hcovClosure
      (by
        intro Wa Wb hWa_ty hWb_ty
        obtain ⟨D, hD, _⟩ := closureData Wa Wb hWa_ty hWb_ty
        exact Option.isSome_iff_exists.mpr ⟨D, hD⟩)
      (by
        intro Wa Wb hWa_ty hWb_ty D hD
        obtain ⟨D', hD', hD'_ty, _⟩ := closureData Wa Wb hWa_ty hWb_ty
        have hEq : D' = D := Option.some.inj (hD'.symm.trans hD)
        subst D
        exact hD'_ty)
      (by
        intro Wa Wb hWa_ty hWb_ty D hD
        obtain ⟨D', hD', _, hD'_iff⟩ := closureData Wa Wb hWa_ty hWb_ty
        have hEq : D' = D := Option.some.inj (hD'.symm.trans hD)
        simpa [closureQ, hEq] using hD'_iff)
  let functionalityQ : SMT.Dom.{u} → SMT.Dom.{u} →
      SMT.Dom.{u} → Prop := fun Wa Wb Wb' =>
    (Wa.fst.pair Wb.fst).pair ZFSet.zftrue ∈ Rval →
    (Wa.fst.pair Wb'.fst).pair ZFSet.zftrue ∈ Rval →
      Wb.fst = Wb'.fst
  obtain ⟨DP2, hdenP2, hDP2_ty, hDP2_iff⟩ :=
    funTernaryForallIffZftrue functionalityQ hcovP2 hgoP2
      hcovFunctionality
      (by
        intro Wa Wb Wb' hWa_ty hWb_ty hWb'_ty
        obtain ⟨D, hD, _⟩ :=
          functionalityData Wa Wb Wb' hWa_ty hWb_ty hWb'_ty
        exact Option.isSome_iff_exists.mpr ⟨D, hD⟩)
      (by
        intro Wa Wb Wb' hWa_ty hWb_ty hWb'_ty D hD
        obtain ⟨D', hD', hD'_ty, _⟩ :=
          functionalityData Wa Wb Wb' hWa_ty hWb_ty hWb'_ty
        have hEq : D' = D := Option.some.inj (hD'.symm.trans hD)
        subst D
        exact hD'_ty)
      (by
        intro Wa Wb Wb' hWa_ty hWb_ty hWb'_ty D hD
        obtain ⟨D', hD', _, hD'_iff⟩ :=
          functionalityData Wa Wb Wb' hWa_ty hWb_ty hWb'_ty
        have hEq : D' = D := Option.some.inj (hD'.symm.trans hD)
        simpa [functionalityQ, hEq] using hD'_iff)
  have hDP1_pointwise : DP1.fst = ZFSet.zftrue ↔
      ∀ a, a ∈ ⟦rho⟧ᶻ → ∀ b, b ∈ ⟦sigma⟧ᶻ →
        (a.pair b).pair ZFSet.zftrue ∈ Rval →
          a.pair ZFSet.zftrue ∈ Aval ∧
          b.pair ZFSet.zftrue ∈ Bval := by
    rw [hDP1_iff]
    constructor
    · intro hall a ha b hb
      let Wa : SMT.Dom.{u} := ⟨a, rho, ha⟩
      let Wb : SMT.Dom.{u} := ⟨b, sigma, hb⟩
      simpa [closureQ, Wa, Wb] using hall Wa Wb rfl rfl
    · intro hpoint Wa Wb hWa_ty hWb_ty
      have hWa_mem : Wa.fst ∈ ⟦rho⟧ᶻ := by
        simpa [hWa_ty] using Wa.snd.snd
      have hWb_mem : Wb.fst ∈ ⟦sigma⟧ᶻ := by
        simpa [hWb_ty] using Wb.snd.snd
      simpa [closureQ] using
        hpoint Wa.fst hWa_mem Wb.fst hWb_mem
  have hDP2_pointwise : DP2.fst = ZFSet.zftrue ↔
      ∀ a, a ∈ ⟦rho⟧ᶻ → ∀ b, b ∈ ⟦sigma⟧ᶻ →
        ∀ b', b' ∈ ⟦sigma⟧ᶻ →
          (a.pair b).pair ZFSet.zftrue ∈ Rval →
          (a.pair b').pair ZFSet.zftrue ∈ Rval → b = b' := by
    rw [hDP2_iff]
    constructor
    · intro hall a ha b hb b' hb'
      let Wa : SMT.Dom.{u} := ⟨a, rho, ha⟩
      let Wb : SMT.Dom.{u} := ⟨b, sigma, hb⟩
      let Wb' : SMT.Dom.{u} := ⟨b', sigma, hb'⟩
      simpa [functionalityQ, Wa, Wb, Wb'] using
        hall Wa Wb Wb' rfl rfl rfl
    · intro hpoint Wa Wb Wb' hWa_ty hWb_ty hWb'_ty
      have hWa_mem : Wa.fst ∈ ⟦rho⟧ᶻ := by
        simpa [hWa_ty] using Wa.snd.snd
      have hWb_mem : Wb.fst ∈ ⟦sigma⟧ᶻ := by
        simpa [hWb_ty] using Wb.snd.snd
      have hWb'_mem : Wb'.fst ∈ ⟦sigma⟧ᶻ := by
        simpa [hWb'_ty] using Wb'.snd.snd
      simpa [functionalityQ] using
        hpoint Wa.fst hWa_mem Wb.fst hWb_mem Wb'.fst hWb'_mem
  obtain ⟨DBody, hdenBodyParts, hDBody_ty, hDBody_iff⟩ :=
    denote_and_iff_zftrue hdenP1 hDP1_ty hdenP2 hDP2_ty
  have hdenBody :
      ⟦(pfunBodyTerm A B R x y y' rho sigma).abstract
        ThetaR hcovBodyR⟧ˢ = some DBody := by
    simpa [pfunBodyTerm, SMT.Term.abstract, proof_irrel_heq] using
      hdenBodyParts
  have houter := single_lambda_fapply_eq_body
    (Delta := Theta) (z := R)
    (alpha := SMTType.fun (SMTType.pair rho sigma) SMTType.bool)
    (beta := SMTType.bool)
    (body := pfunBodyTerm A B R x y y' rho sigma)
    (lamVal :=
      (⟨U, SMTType.fun
        (SMTType.fun (SMTType.pair rho sigma) SMTType.bool)
        SMTType.bool, hU⟩ : SMT.Dom))
    hcovOut hdenOut (by simpa [tauR] using hUfunc)
    (W := WR) (bodyVal := DBody) (by rfl) hRval hcovBodyR hdenBody
  rw [houter, hDBody_iff, hDP1_pointwise, hDP2_pointwise]
  exact predGraph_isPFunc_iff_pointwise.symm

theorem B.denote_pfun_inv_rep.{u}
    {S T : B.Term} {alpha beta : BType}
    {Xi : B.RenamingContext.Context}
    (Xi_fv : ∀ v ∈ B.fv (B.Term.pfun S T),
      (Xi v).isSome = true)
    {U : ZFSet.{u}}
    {hU : U ∈ ⟦BType.set (BType.set (alpha ×ᴮ beta))⟧ᶻ}
    (hden : ⟦(B.Term.pfun S T).abstract Xi Xi_fv⟧ᴮ =
      some ⟨U, BType.set (BType.set (alpha ×ᴮ beta)), hU⟩) :
    ∃ (X Y : ZFSet.{u})
      (hX : X ∈ ⟦BType.set alpha⟧ᶻ)
      (hY : Y ∈ ⟦BType.set beta⟧ᶻ),
      ⟦S.abstract Xi (fun v hv => Xi_fv v (by
        simpa [B.fv] using (Or.inl hv :
          v ∈ B.fv S ∨ v ∈ B.fv T)))⟧ᴮ =
          some ⟨X, BType.set alpha, hX⟩ ∧
      ⟦T.abstract Xi (fun v hv => Xi_fv v (by
        simpa [B.fv] using (Or.inr hv :
          v ∈ B.fv S ∨ v ∈ B.fv T)))⟧ᴮ =
          some ⟨Y, BType.set beta, hY⟩ ∧
      U = pfunSet X Y := by
  rw [B.Term.abstract, B.denote, Option.pure_def,
    Option.bind_eq_bind, Option.bind_eq_some_iff] at hden
  obtain ⟨⟨X, tauX, hX⟩, hdenX, hrest⟩ := hden
  cases tauX <;> first
    | rw [Option.bind_eq_some_iff] at hrest
    | exact absurd hrest (by simp)
  rename_i gammaX
  obtain ⟨⟨Y, tauY, hY⟩, hdenY, hout⟩ := hrest
  cases tauY <;> first
    | rw [Option.some_inj] at hout
    | exact absurd hout (by simp)
  rename_i gammaY
  injection hout with hvalue htype
  subst U
  simp only [heq_eq_eq, PSigma.mk.injEq, BType.set.injEq,
    BType.prod.injEq] at htype
  obtain ⟨⟨hgammaX, hgammaY⟩, _⟩ := htype
  subst gammaX
  subst gammaY
  refine ⟨X, Y, hX, hY, ?_, ?_, rfl⟩
  · simpa only [proof_irrel_heq] using hdenX
  · simpa only [proof_irrel_heq] using hdenY

private theorem erase_insert_ne_rep_pfun
    {a b : SMT.𝒱} {tau : SMTType} {ctx : SMT.TypeContext}
    (hab : a ≠ b) :
    (ctx.insert b tau).erase a = (ctx.erase a).insert b tau := by
  apply AList.ext
  show List.kerase a (AList.insert b tau ctx).entries =
    (AList.insert b tau (ctx.erase a)).entries
  rw [AList.entries_insert, AList.entries_insert]
  change List.kerase a (⟨b, tau⟩ :: List.kerase b ctx.entries) =
    ⟨b, tau⟩ :: List.kerase b (List.kerase a ctx.entries)
  rw [List.kerase_cons_ne (by simpa using hab), List.kerase_kerase]

private theorem erase_insert_self_rep_pfun
    {a : SMT.𝒱} {tau : SMTType} {ctx : SMT.TypeContext}
    (ha : a ∉ ctx) : (ctx.insert a tau).erase a = ctx := by
  apply AList.ext
  show List.kerase a (AList.insert a tau ctx).entries = ctx.entries
  rw [AList.entries_insert_of_notMem ha]
  exact List.kerase_cons_eq rfl

private theorem erase_four_rep_pfun
    {R x y z : SMT.𝒱} {tauR taux tauy tauz : SMTType}
    {ctx : SMT.TypeContext}
    (hR : R ∉ ctx) (hx : x ∉ ctx.insert R tauR)
    (hy : y ∉ (ctx.insert R tauR).insert x taux)
    (hz : z ∉ ((ctx.insert R tauR).insert x taux).insert y tauy) :
    let ctx4 := (((ctx.insert R tauR).insert x taux).insert y tauy).insert z tauz
    AList.erase z (AList.erase y (AList.erase x (AList.erase R ctx4))) =
      ctx := by
  dsimp
  have hRx : R ≠ x := by
    intro h; subst x; exact hx (by simp)
  have hRy : R ≠ y := by
    intro h; subst y; exact hy (by simp)
  have hRz : R ≠ z := by
    intro h; subst z; exact hz (by simp)
  have hxy : x ≠ y := by
    intro h; subst y; exact hy (by simp)
  have hxz : x ≠ z := by
    intro h; subst z; exact hz (by simp)
  have hyz : y ≠ z := by
    intro h; subst z; exact hz (by simp)
  have hx0 : x ∉ ctx := by
    intro h; exact hx (by simp [h])
  have hy0 : y ∉ ctx := by
    intro h; exact hy (by simp [h])
  have hz0 : z ∉ ctx := by
    intro h; exact hz (by simp [h])
  rw [erase_insert_ne_rep_pfun hRz,
    erase_insert_ne_rep_pfun hRy,
    erase_insert_ne_rep_pfun hRx,
    erase_insert_self_rep_pfun hR,
    erase_insert_ne_rep_pfun hxz,
    erase_insert_ne_rep_pfun hxy,
    erase_insert_self_rep_pfun hx0,
    erase_insert_ne_rep_pfun hyz,
    erase_insert_self_rep_pfun hy0,
    erase_insert_self_rep_pfun hz0]

private def encodePFunTail (A B : SMT.Term)
    (alpha beta : SMTType) : Encoder (SMT.Term × SMTType) := do
  let R ← freshVar (.fun (.pair alpha beta) .bool)
  let x ← freshVar alpha
  let y ← freshVar beta
  let y' ← freshVar beta
  SMT.eraseFromContext R
  SMT.eraseFromContext x
  SMT.eraseFromContext y
  SMT.eraseFromContext y'
  return (.lambda [R] [.fun (.pair alpha beta) .bool] (.and
      (.forall [x, y] [alpha, beta]
        (.imp (.app (.var R) (.pair (.var x) (.var y)))
          (.and (.app A (.var x)) (.app B (.var y)))))
      (.forall [x, y, y'] [alpha, beta, beta] (.imp
        (.and (.app (.var R) (.pair (.var x) (.var y)))
              (.app (.var R) (.pair (.var x) (.var y'))))
        (.eq (.var y) (.var y'))))),
    .fun (.fun (.pair alpha beta) .bool) .bool)

private theorem encodePFunTail_shape_decls
    (A B : SMT.Term) (alpha beta : SMTType)
    {Lambda : SMT.TypeContext} {n : ℕ} {used : List SMT.𝒱}
    {decl : SMT.Chunk} :
    ⦃fun ⟨env, Lambda'⟩ =>
      ⌜Lambda' = Lambda ∧ env.freshvarsc = n ∧
        Lambda.keys ⊆ env.usedVars ∧ env.usedVars = used ∧
        env.declarations = decl⌝⦄
    encodePFunTail A B alpha beta
    ⦃⇓? ⟨out, sigmaOut⟩ ⟨env', Gamma'⟩ =>
      ⌜∃ R x y y' : SMT.𝒱,
        out = .lambda [R] [.fun (.pair alpha beta) .bool]
          (.and
            (.forall [x, y] [alpha, beta]
              (.imp (.app (.var R) (.pair (.var x) (.var y)))
                (.and (.app A (.var x)) (.app B (.var y)))))
            (.forall [x, y, y'] [alpha, beta, beta]
              (.imp
                (.and (.app (.var R) (.pair (.var x) (.var y)))
                  (.app (.var R) (.pair (.var x) (.var y'))))
                (.eq (.var y) (.var y'))))) ∧
        sigmaOut = .fun (.fun (.pair alpha beta) .bool) .bool ∧
        Gamma' = Lambda ∧ env'.declarations = decl ∧
        R ∉ Lambda ∧ x ∉ Lambda ∧ y ∉ Lambda ∧ y' ∉ Lambda ∧
        R ≠ x ∧ R ≠ y ∧ R ≠ y' ∧ x ≠ y ∧ x ≠ y' ∧ y ≠ y'⌝⦄ := by
  unfold encodePFunTail
  mstart
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_keys, rfl, rfl⟩ := pre
  mspec (Std.Do.Triple.and _
    (SMT.freshVar_spec (Γ := St.types)
      (τ := SMTType.fun (SMTType.pair alpha beta) SMTType.bool)
      (n := St.env.freshvarsc) (used := St.env.usedVars))
    (SMT.freshVar_decls
      (τ := SMTType.fun (SMTType.pair alpha beta) SMTType.bool)
      (decl := St.env.declarations)))
  next R =>
    mrename_i postR
    mintro ∀StR
    mpure postR
    dsimp at postR
    obtain ⟨⟨StR_types, R_fresh, StR_fresh, StR_used,
      R_not_used⟩, StR_decl⟩ := postR
    mspec (Std.Do.Triple.and _
      (SMT.freshVar_spec (Γ := StR.types) (τ := alpha)
        (n := StR.env.freshvarsc) (used := StR.env.usedVars))
      (SMT.freshVar_decls (τ := alpha)
        (decl := StR.env.declarations)))
    next x =>
      mrename_i postX
      mintro ∀StX
      mpure postX
      dsimp at postX
      obtain ⟨⟨StX_types, x_fresh, StX_fresh, StX_used,
        x_not_used⟩, StX_decl⟩ := postX
      mspec (Std.Do.Triple.and _
        (SMT.freshVar_spec (Γ := StX.types) (τ := beta)
          (n := StX.env.freshvarsc) (used := StX.env.usedVars))
        (SMT.freshVar_decls (τ := beta)
          (decl := StX.env.declarations)))
      next y =>
        mrename_i postY
        mintro ∀StY
        mpure postY
        dsimp at postY
        obtain ⟨⟨StY_types, y_fresh, StY_fresh, StY_used,
          y_not_used⟩, StY_decl⟩ := postY
        mspec (Std.Do.Triple.and _
          (SMT.freshVar_spec (Γ := StY.types) (τ := beta)
            (n := StY.env.freshvarsc) (used := StY.env.usedVars))
          (SMT.freshVar_decls (τ := beta)
            (decl := StY.env.declarations)))
        next y' =>
          mrename_i postY'
          mintro ∀StY'
          mpure postY'
          dsimp at postY'
          obtain ⟨⟨StY'_types, y'_fresh, StY'_fresh, StY'_used,
            y'_not_used⟩, StY'_decl⟩ := postY'
          mspec (Std.Do.Triple.and _ SMT.eraseFromContext_spec
            (SMT.eraseFromContext_decls
              (decl := StY'.env.declarations)))
          mrename_i postER
          mintro ∀StER
          mpure postER
          dsimp at postER
          obtain ⟨⟨StER_types, StER_fresh, StER_used⟩,
            StER_decl⟩ := postER
          mspec (Std.Do.Triple.and _ SMT.eraseFromContext_spec
            (SMT.eraseFromContext_decls
              (decl := StER.env.declarations)))
          mrename_i postEX
          mintro ∀StEX
          mpure postEX
          dsimp at postEX
          obtain ⟨⟨StEX_types, StEX_fresh, StEX_used⟩,
            StEX_decl⟩ := postEX
          mspec (Std.Do.Triple.and _ SMT.eraseFromContext_spec
            (SMT.eraseFromContext_decls
              (decl := StEX.env.declarations)))
          mrename_i postEY
          mintro ∀StEY
          mpure postEY
          dsimp at postEY
          obtain ⟨⟨StEY_types, StEY_fresh, StEY_used⟩,
            StEY_decl⟩ := postEY
          mspec (Std.Do.Triple.and _ SMT.eraseFromContext_spec
            (SMT.eraseFromContext_decls
              (decl := StEY.env.declarations)))
          mrename_i postEY'
          mintro ∀StEY'
          mpure postEY'
          dsimp at postEY'
          obtain ⟨⟨StEY'_types, StEY'_fresh, StEY'_used⟩,
            StEY'_decl⟩ := postEY'

          let tauR := SMTType.fun
            (SMTType.pair alpha beta) .bool
          have x_fresh₀ : x ∉ St.types.insert R tauR := by
            simpa [tauR, StR_types] using x_fresh
          have y_fresh₀ : y ∉
              (St.types.insert R tauR).insert x alpha := by
            simpa [tauR, StX_types, StR_types] using y_fresh
          have y'_fresh₀ : y' ∉
              ((St.types.insert R tauR).insert x alpha).insert y beta := by
            simpa [tauR, StY_types, StX_types, StR_types] using y'_fresh
          have StEY'_types_final : StEY'.types = St.types := by
            rw [StEY'_types, StEY_types, StEX_types, StER_types,
              StY'_types, StY_types, StX_types, StR_types]
            exact erase_four_rep_pfun R_fresh x_fresh₀ y_fresh₀ y'_fresh₀
          have StEY'_decl_final :
              StEY'.env.declarations = St.env.declarations := by
            rw [StEY'_decl, StEY_decl, StEX_decl, StER_decl,
              StY'_decl, StY_decl, StX_decl, StR_decl]
          have hR_ne_x : R ≠ x := by
            intro h; subst x; exact x_fresh₀ (by simp)
          have hR_ne_y : R ≠ y := by
            intro h; subst y; exact y_fresh₀ (by simp)
          have hR_ne_y' : R ≠ y' := by
            intro h; subst y'; exact y'_fresh₀ (by simp)
          have hx_ne_y : x ≠ y := by
            intro h; subst y; exact y_fresh₀ (by simp)
          have hx_ne_y' : x ≠ y' := by
            intro h; subst y'; exact y'_fresh₀ (by simp)
          have hy_ne_y' : y ≠ y' := by
            intro h; subst y'; exact y'_fresh₀ (by simp)
          have x_fresh_ctx : x ∉ St.types := by
            intro h; exact x_fresh₀ (by simp [h])
          have y_fresh_ctx : y ∉ St.types := by
            intro h; exact y_fresh₀ (by simp [h])
          have y'_fresh_ctx : y' ∉ St.types := by
            intro h; exact y'_fresh₀ (by simp [h])

          mspec Std.Do.Spec.pure
          mpure_intro
          exact ⟨R, x, y, y', rfl, trivial,
            StEY'_types_final, StEY'_decl_final,
            R_fresh, x_fresh_ctx, y_fresh_ctx, y'_fresh_ctx,
            hR_ne_x, hR_ne_y, hR_ne_y',
            hx_ne_y, hx_ne_y', hy_ne_y'⟩

private theorem encodeTerm_pfun_via_tail
    (S T : B.Term) (E : B.Env) :
    encodeTerm (B.Term.pfun S T) E = (do
      let ⟨Aenc, .fun alpha .bool⟩ ← encodeTerm S E |
        throw "encodeTerm:pfun: Expected a set for domain"
      let ⟨Benc, .fun beta .bool⟩ ← encodeTerm T E |
        throw "encodeTerm:pfun: Expected a set for codomain"
      encodePFunTail Aenc Benc alpha beta) := by
  rfl

private theorem pfun_lambda_typing
    {alpha beta : SMTType} {A B : SMT.Term}
    {R x y y' : SMT.𝒱} {Gamma : SMT.TypeContext}
    (typ_A : Gamma ⊢ˢ A : .fun alpha .bool)
    (typ_B : Gamma ⊢ˢ B : .fun beta .bool)
    (R_fresh : R ∉ Gamma) (x_fresh : x ∉ Gamma)
    (y_fresh : y ∉ Gamma) (y'_fresh : y' ∉ Gamma)
    (R_not_bv_A : R ∉ SMT.bv A) (R_not_bv_B : R ∉ SMT.bv B)
    (x_not_bv_A : x ∉ SMT.bv A) (x_not_bv_B : x ∉ SMT.bv B)
    (y_not_bv_A : y ∉ SMT.bv A) (y_not_bv_B : y ∉ SMT.bv B)
    (hR_ne_x : R ≠ x) (hR_ne_y : R ≠ y) (hR_ne_y' : R ≠ y')
    (hx_ne_y : x ≠ y) (hx_ne_y' : x ≠ y') (hy_ne_y' : y ≠ y') :
    Gamma ⊢ˢ
      .lambda [R] [.fun (.pair alpha beta) .bool] (.and
        (.forall [x, y] [alpha, beta]
          (.imp (.app (.var R) (.pair (.var x) (.var y)))
            (.and (.app A (.var x)) (.app B (.var y)))))
        (.forall [x, y, y'] [alpha, beta, beta] (.imp
          (.and (.app (.var R) (.pair (.var x) (.var y)))
                (.app (.var R) (.pair (.var x) (.var y'))))
          (.eq (.var y) (.var y'))))) :
      .fun (.fun (.pair alpha beta) .bool) .bool := by
  let tauR := SMTType.fun (SMTType.pair alpha beta) .bool
  let body := SMT.Term.and
    (.forall [x, y] [alpha, beta]
      (.imp (.app (.var R) (.pair (.var x) (.var y)))
        (.and (.app A (.var x)) (.app B (.var y)))))
    (.forall [x, y, y'] [alpha, beta, beta] (.imp
      (.and (.app (.var R) (.pair (.var x) (.var y)))
            (.app (.var R) (.pair (.var x) (.var y'))))
      (.eq (.var y) (.var y'))))
  have x_fresh_R : x ∉ Gamma.insert R tauR := by
    intro h
    rw [AList.mem_insert] at h
    exact h.elim (fun h => hR_ne_x h.symm) x_fresh
  have y_fresh_R : y ∉ Gamma.insert R tauR := by
    intro h
    rw [AList.mem_insert] at h
    exact h.elim (fun h => hR_ne_y h.symm) y_fresh
  have y'_fresh_R : y' ∉ Gamma.insert R tauR := by
    intro h
    rw [AList.mem_insert] at h
    exact h.elim (fun h => hR_ne_y' h.symm) y'_fresh
  have typ_A_R : Gamma.insert R tauR ⊢ˢ A : .fun alpha .bool :=
    SMT.Typing.weakening
      (SMT.TypeContext.entries_subset_insert_of_notMem R_fresh) typ_A
      (SMT.Typing.bv_notMem_insert_of_fresh typ_A R_not_bv_A)
  have typ_B_R : Gamma.insert R tauR ⊢ˢ B : .fun beta .bool :=
    SMT.Typing.weakening
      (SMT.TypeContext.entries_subset_insert_of_notMem R_fresh) typ_B
      (SMT.Typing.bv_notMem_insert_of_fresh typ_B R_not_bv_B)
  have typ_body : Gamma.insert R tauR ⊢ˢ body : .bool := by
    dsimp [body]
    apply SMT.Typing.and
    · refine SMT.Typing.forall (Gamma.insert R tauR) [x, y]
        [alpha, beta] _ ?_ ?_ (by simp) rfl ?_
      · intro v hv
        rw [List.mem_cons, List.mem_singleton] at hv
        exact hv.elim (fun h => h ▸ x_fresh_R)
          (fun h => h ▸ y_fresh_R)
      · intro v hv hbv
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
        simp only [SMT.bv, List.mem_append, List.mem_nil_iff,
          false_or, or_false] at hbv
        rcases hv with rfl | rfl
        · exact hbv.elim x_not_bv_A x_not_bv_B
        · exact hbv.elim y_not_bv_A y_not_bv_B
      · have hupdate : SMT.TypeContext.update (Gamma.insert R tauR)
            [x, y] [alpha, beta] rfl =
            ((Gamma.insert R tauR).insert x alpha).insert y beta := by
          simp only [SMT.TypeContext.update, List.length_cons,
            List.length_nil, zero_add, Fin.foldl_succ_last,
            Fin.getElem_fin, Fin.val_cast, Fin.val_last,
            List.getElem_cons_zero, Fin.val_castSucc, Fin.foldl_zero]
          rfl
        rw [hupdate]
        have y_fresh_Rx : y ∉ (Gamma.insert R tauR).insert x alpha := by
          intro h
          rw [AList.mem_insert] at h
          exact h.elim (fun h => hx_ne_y h.symm) y_fresh_R
        have hsub : (Gamma.insert R tauR).entries ⊆
            (((Gamma.insert R tauR).insert x alpha).insert y beta).entries :=
          (SMT.TypeContext.entries_subset_insert_of_notMem x_fresh_R).trans
            (SMT.TypeContext.entries_subset_insert_of_notMem y_fresh_Rx)
        have hbv_A : ∀ v ∈ SMT.bv A,
            v ∉ ((Gamma.insert R tauR).insert x alpha).insert y beta := by
          intro v hv hmem
          rw [AList.mem_insert] at hmem
          rcases hmem with rfl | hmem
          · exact y_not_bv_A hv
          rw [AList.mem_insert] at hmem
          rcases hmem with rfl | hmem
          · exact x_not_bv_A hv
          rw [AList.mem_insert] at hmem
          rcases hmem with rfl | hmem
          · exact R_not_bv_A hv
          · exact SMT.Typing.bv_notMem_context typ_A v hv hmem
        have hbv_B : ∀ v ∈ SMT.bv B,
            v ∉ ((Gamma.insert R tauR).insert x alpha).insert y beta := by
          intro v hv hmem
          rw [AList.mem_insert] at hmem
          rcases hmem with rfl | hmem
          · exact y_not_bv_B hv
          rw [AList.mem_insert] at hmem
          rcases hmem with rfl | hmem
          · exact x_not_bv_B hv
          rw [AList.mem_insert] at hmem
          rcases hmem with rfl | hmem
          · exact R_not_bv_B hv
          · exact SMT.Typing.bv_notMem_context typ_B v hv hmem
        apply SMT.Typing.imp
        · apply SMT.Typing.app
          · apply SMT.Typing.var
            rw [AList.lookup_insert_ne hR_ne_y,
              AList.lookup_insert_ne hR_ne_x, AList.lookup_insert]
          · apply SMT.Typing.pair
            · apply SMT.Typing.var
              rw [AList.lookup_insert_ne hx_ne_y, AList.lookup_insert]
            · apply SMT.Typing.var
              rw [AList.lookup_insert]
        · apply SMT.Typing.and
          · apply SMT.Typing.app
            · exact SMT.Typing.weakening hsub typ_A_R hbv_A
            · apply SMT.Typing.var
              rw [AList.lookup_insert_ne hx_ne_y, AList.lookup_insert]
          · apply SMT.Typing.app
            · exact SMT.Typing.weakening hsub typ_B_R hbv_B
            · apply SMT.Typing.var
              rw [AList.lookup_insert]
    · refine SMT.Typing.forall (Gamma.insert R tauR) [x, y, y']
        [alpha, beta, beta] _ ?_ ?_ (by simp) rfl ?_
      · intro v hv
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
        rcases hv with rfl | rfl | rfl
        · exact x_fresh_R
        · exact y_fresh_R
        · exact y'_fresh_R
      · intro v _ hbv
        simp only [SMT.bv, List.mem_append, List.mem_nil_iff,
          or_false] at hbv
      · have hupdate : SMT.TypeContext.update (Gamma.insert R tauR)
            [x, y, y'] [alpha, beta, beta] rfl =
            (((Gamma.insert R tauR).insert x alpha).insert y beta).insert y' beta := by
          simp only [SMT.TypeContext.update, List.length_cons,
            List.length_nil, zero_add, Fin.foldl_succ_last,
            Fin.getElem_fin, Fin.val_cast, Fin.val_last,
            List.getElem_cons_zero, Fin.val_castSucc, Fin.foldl_zero]
          rfl
        rw [hupdate]
        apply SMT.Typing.imp
        · apply SMT.Typing.and
          · apply SMT.Typing.app
            · apply SMT.Typing.var
              rw [AList.lookup_insert_ne hR_ne_y',
                AList.lookup_insert_ne hR_ne_y,
                AList.lookup_insert_ne hR_ne_x, AList.lookup_insert]
            · apply SMT.Typing.pair
              · apply SMT.Typing.var
                rw [AList.lookup_insert_ne hx_ne_y',
                  AList.lookup_insert_ne hx_ne_y, AList.lookup_insert]
              · apply SMT.Typing.var
                rw [AList.lookup_insert_ne hy_ne_y', AList.lookup_insert]
          · apply SMT.Typing.app
            · apply SMT.Typing.var
              rw [AList.lookup_insert_ne hR_ne_y',
                AList.lookup_insert_ne hR_ne_y,
                AList.lookup_insert_ne hR_ne_x, AList.lookup_insert]
            · apply SMT.Typing.pair
              · apply SMT.Typing.var
                rw [AList.lookup_insert_ne hx_ne_y',
                  AList.lookup_insert_ne hx_ne_y, AList.lookup_insert]
              · apply SMT.Typing.var
                rw [AList.lookup_insert]
        · apply SMT.Typing.eq
          · apply SMT.Typing.var
            rw [AList.lookup_insert_ne hy_ne_y', AList.lookup_insert]
          · apply SMT.Typing.var
            rw [AList.lookup_insert]
  have typ_lambda : Gamma ⊢ˢ .lambda [R] [tauR] body :
      .fun tauR .bool := by
    refine SMT.Typing.lambda Gamma [R] [tauR] _ .bool ?_ ?_ ?_ ?_ ?_
    · intro v hv
      rw [List.mem_singleton] at hv
      exact hv ▸ R_fresh
    · intro v hv hbv
      rw [List.mem_singleton] at hv
      subst v
      dsimp [body] at hbv
      simp only [SMT.bv, List.append_nil] at hbv
      rcases List.mem_append.mp hbv with hL | hR
      · rcases List.mem_append.mp hL with hLL | hLR
        · rcases List.mem_cons.mp hLL with h | hLL'
          · exact hR_ne_x h
          · rcases List.mem_cons.mp hLL' with h | h
            · exact hR_ne_y h
            · exact List.not_mem_nil h
        · rcases List.mem_append.mp hLR with h | hLR'
          · exact List.not_mem_nil h
          · rcases List.mem_append.mp hLR' with h | h
            · exact R_not_bv_A h
            · exact R_not_bv_B h
      · rcases List.mem_cons.mp hR with h | hR'
        · exact hR_ne_x h
        · rcases List.mem_cons.mp hR' with h | hR''
          · exact hR_ne_y h
          · rcases List.mem_cons.mp hR'' with h | h
            · exact hR_ne_y' h
            · exact List.not_mem_nil h
    · exact Nat.zero_lt_succ 0
    · rfl
    · have hupdate : SMT.TypeContext.update Gamma [R] [tauR] rfl =
          Gamma.insert R tauR := by
        simp only [SMT.TypeContext.update, List.length_cons,
          List.length_nil, zero_add, Nat.reduceAdd, Fin.cast_eq_self,
          Fin.getElem_fin, Fin.val_eq_zero, List.getElem_cons_zero,
          Fin.foldl_succ, Fin.foldl_zero]
      rw [hupdate]
      exact typ_body
  simpa [tauR, body] using typ_lambda

abbrev EncodePFunTailRepSpec.{u}
    (alpha beta : BType) (rho sigma : SMTType)
    (_hrho : BType.SupportedSMT alpha rho)
    (_hsigma : BType.SupportedSMT beta sigma)
    (A B : SMT.Term) : Prop :=
  ∀ {Lambda : SMT.TypeContext} {n : ℕ} {used : List SMT.𝒱},
    Lambda ⊢ˢ A : SMTType.fun rho SMTType.bool →
    Lambda ⊢ˢ B : SMTType.fun sigma SMTType.bool →
    (∀ v ∈ SMT.bv A, v ∈ used) →
    (∀ v ∈ SMT.bv B, v ∈ used) →
    ⦃fun ⟨env, Lambda'⟩ =>
      ⌜Lambda' = Lambda ∧ env.freshvarsc = n ∧
        Lambda.keys ⊆ env.usedVars ∧ env.usedVars = used⌝⦄
    encodePFunTail A B rho sigma
    ⦃⇓? ⟨t, sigma⟩ ⟨env', Gamma'⟩ =>
      ⌜used ⊆ env'.usedVars ∧
        Lambda ⊆ Gamma' ∧
        Gamma'.keys ⊆ env'.usedVars ∧
        Nonempty (sigma ~>
          (BType.set (BType.set (alpha ×ᴮ beta))).toSMTType) ∧
        Gamma' ⊢ˢ t : sigma ∧
        (∀ v ∈ used, v ∉ Lambda → v ∉ Gamma') ∧
        ∀ (Theta : SMT.RenamingContext.Context.{u})
          (hA : RenamingContext.CoversFV Theta A)
          (hB : RenamingContext.CoversFV Theta B),
          (∀ v ∉ used, Theta v = none) →
          SMT.RenamingContext.RespectsTypeContextOnFV Theta Lambda A →
          SMT.RenamingContext.RespectsTypeContextOnFV Theta Lambda B →
          (∀ v, Theta v ≠ none → v ∈ Lambda) →
          ∀ (X Y : ZFSet.{u})
            (hX : X ∈ ⟦BType.set alpha⟧ᶻ)
            (hY : Y ∈ ⟦BType.set beta⟧ᶻ)
            (denA denB : SMT.Dom.{u}),
            ⟦A.abstract Theta hA⟧ˢ = some denA →
            ⟦B.abstract Theta hB⟧ˢ = some denB →
            RDomCastSupported
              (⟨X, BType.set alpha, hX⟩ : _root_.B.Dom) denA →
            RDomCastSupported
              (⟨Y, BType.set beta, hY⟩ : _root_.B.Dom) denB →
            ∃ (Theta' : SMT.RenamingContext.Context.{u})
              (hcov : RenamingContext.CoversFV Theta' t)
              (denOut : SMT.Dom.{u}),
              RenamingContext.Extends Theta' Theta ∧
              (∀ v ∉ env'.usedVars, Theta' v = none) ∧
              SMT.RenamingContext.RespectsTypeContextOnFV
                Theta' Gamma' t ∧
              (∀ v, Theta' v ≠ none → v ∈ Gamma') ∧
              ⟦t.abstract Theta' hcov⟧ˢ = some denOut ∧
              denOut.snd.fst = sigma ∧
              RDomCastSupported
                (⟨pfunSet X Y,
                  BType.set (BType.set (alpha ×ᴮ beta)),
                  pfunSet_mem_btype hX hY⟩ : _root_.B.Dom) denOut⌝⦄

set_option maxHeartbeats 7000000 in
theorem encodePFunTail_rep_spec.{u}
    (alpha beta : BType) (rho sigma : SMTType)
    (hrho : BType.SupportedSMT alpha rho)
    (hsigma : BType.SupportedSMT beta sigma)
    (A B : SMT.Term) :
    EncodePFunTailRepSpec.{u}
      alpha beta rho sigma hrho hsigma A B := by
  unfold EncodePFunTailRepSpec
  intro Lambda n used typ_A typ_B bv_A_used bv_B_used
  unfold encodePFunTail
  mstart
  mintro pre ∀St₀
  mpure pre
  obtain ⟨rfl, rfl, St₀_keys, rfl⟩ := pre
  mspec SMT.freshVar_spec
  next R =>
    mrename_i post₁
    mintro ∀St₁
    mpure post₁
    obtain ⟨St₁_types_eq, R_fresh, _, St₁_used_eq,
      R_not_used⟩ := post₁
    mspec SMT.freshVar_spec
    next x =>
      mrename_i post₂
      mintro ∀St₂
      mpure post₂
      obtain ⟨St₂_types_eq, x_fresh, _, St₂_used_eq,
        x_not_used⟩ := post₂
      mspec SMT.freshVar_spec
      next y =>
        mrename_i post₃
        mintro ∀St₃
        mpure post₃
        obtain ⟨St₃_types_eq, y_fresh, _, St₃_used_eq,
          y_not_used⟩ := post₃
        mspec SMT.freshVar_spec
        next y' =>
          mrename_i post₄
          mintro ∀St₄
          mpure post₄
          obtain ⟨St₄_types_eq, y'_fresh, _, St₄_used_eq,
            y'_not_used⟩ := post₄
          mspec SMT.eraseFromContext_spec
          mrename_i postER
          mintro ∀StER
          mpure postER
          obtain ⟨StER_types_eq, _, StER_used_eq⟩ := postER
          mspec SMT.eraseFromContext_spec
          mrename_i postEx
          mintro ∀StEx
          mpure postEx
          obtain ⟨StEx_types_eq, _, StEx_used_eq⟩ := postEx
          mspec SMT.eraseFromContext_spec
          mrename_i postEy
          mintro ∀StEy
          mpure postEy
          obtain ⟨StEy_types_eq, _, StEy_used_eq⟩ := postEy
          mspec SMT.eraseFromContext_spec
          mrename_i postEy'
          mintro ∀StEy'
          mpure postEy'
          obtain ⟨StEy'_types_eq, _, StEy'_used_eq⟩ := postEy'

          let tauR := SMTType.fun
            (SMTType.pair rho sigma) .bool
          have x_fresh₀ : x ∉ St₀.types.insert R tauR := by
            simpa [tauR, St₁_types_eq] using x_fresh
          have y_fresh₀ : y ∉
              (St₀.types.insert R tauR).insert x rho := by
            simpa [tauR, St₂_types_eq, St₁_types_eq] using y_fresh
          have y'_fresh₀ : y' ∉
              ((St₀.types.insert R tauR).insert x rho).insert y sigma := by
            simpa [tauR, St₃_types_eq, St₂_types_eq,
              St₁_types_eq] using y'_fresh
          have StEy'_types_final : StEy'.types = St₀.types := by
            rw [StEy'_types_eq, StEy_types_eq, StEx_types_eq,
              StER_types_eq, St₄_types_eq, St₃_types_eq,
              St₂_types_eq, St₁_types_eq]
            exact erase_four_rep_pfun R_fresh x_fresh₀ y_fresh₀ y'_fresh₀
          have hR_ne_x : R ≠ x := by
            intro h; subst x; exact x_fresh₀ (by simp)
          have hR_ne_y : R ≠ y := by
            intro h; subst y; exact y_fresh₀ (by simp)
          have hR_ne_y' : R ≠ y' := by
            intro h; subst y'; exact y'_fresh₀ (by simp)
          have hx_ne_y : x ≠ y := by
            intro h; subst y; exact y_fresh₀ (by simp)
          have hx_ne_y' : x ≠ y' := by
            intro h; subst y'; exact y'_fresh₀ (by simp)
          have hy_ne_y' : y ≠ y' := by
            intro h; subst y'; exact y'_fresh₀ (by simp)
          have x_fresh_ctx : x ∉ St₀.types := by
            intro h; exact x_fresh₀ (by simp [h])
          have y_fresh_ctx : y ∉ St₀.types := by
            intro h; exact y_fresh₀ (by simp [h])
          have y'_fresh_ctx : y' ∉ St₀.types := by
            intro h; exact y'_fresh₀ (by simp [h])
          have R_not_bv_A : R ∉ SMT.bv A :=
            fun h => R_not_used (bv_A_used R h)
          have R_not_bv_B : R ∉ SMT.bv B :=
            fun h => R_not_used (bv_B_used R h)
          have x_not_bv_A : x ∉ SMT.bv A := fun h => by
            apply x_not_used
            rw [St₁_used_eq]
            exact List.mem_cons_of_mem _ (bv_A_used x h)
          have x_not_bv_B : x ∉ SMT.bv B := fun h => by
            apply x_not_used
            rw [St₁_used_eq]
            exact List.mem_cons_of_mem _ (bv_B_used x h)
          have y_not_bv_A : y ∉ SMT.bv A := fun h => by
            apply y_not_used
            rw [St₂_used_eq, St₁_used_eq]
            exact List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (bv_A_used y h))
          have y_not_bv_B : y ∉ SMT.bv B := fun h => by
            apply y_not_used
            rw [St₂_used_eq, St₁_used_eq]
            exact List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (bv_B_used y h))

          let pfunBody : SMT.Term :=
            .and
              (.forall [x, y] [rho, sigma]
                (.imp (.app (.var R) (.pair (.var x) (.var y)))
                  (.and (.app A (.var x)) (.app B (.var y)))))
              (.forall [x, y, y']
                [rho, sigma, sigma] (.imp
                  (.and (.app (.var R) (.pair (.var x) (.var y)))
                        (.app (.var R) (.pair (.var x) (.var y'))))
                  (.eq (.var y) (.var y'))))
          let tpfun : SMT.Term := .lambda [R] [tauR] pfunBody
          have typ_tpfun : St₀.types ⊢ˢ tpfun :
              SMTType.fun tauR SMTType.bool := by
            simpa [tpfun, pfunBody, tauR] using
              pfun_lambda_typing typ_A typ_B R_fresh x_fresh_ctx
                y_fresh_ctx y'_fresh_ctx R_not_bv_A R_not_bv_B
                x_not_bv_A x_not_bv_B y_not_bv_A y_not_bv_B
                hR_ne_x hR_ne_y hR_ne_y' hx_ne_y hx_ne_y' hy_ne_y'
          have fv_tpfun_sub : SMT.fv tpfun ⊆ SMT.fv A ++ SMT.fv B := by
            intro v hv
            dsimp [tpfun] at hv
            rw [SMT.fv, List.mem_removeAll_iff] at hv
            obtain ⟨hv_body, hv_ne_R⟩ := hv
            dsimp [pfunBody] at hv_body
            rw [SMT.fv, List.mem_append] at hv_body
            rcases hv_body with hv_left | hv_right
            · rw [SMT.fv, List.mem_removeAll_iff] at hv_left
              obtain ⟨hv_imp, hv_ne_xy⟩ := hv_left
              rw [SMT.fv, List.mem_append] at hv_imp
              rcases hv_imp with hv_app | hv_and
              · rw [SMT.fv, List.mem_append] at hv_app
                rcases hv_app with hvR | hvpair
                · exfalso
                  apply hv_ne_R
                  simpa [SMT.fv] using hvR
                · rw [SMT.fv, List.mem_append] at hvpair
                  rcases hvpair with hvx | hvy
                  · exfalso
                    apply hv_ne_xy
                    have : v = x := by simpa [SMT.fv] using hvx
                    simp [this]
                  · exfalso
                    apply hv_ne_xy
                    have : v = y := by simpa [SMT.fv] using hvy
                    simp [this]
              · rw [SMT.fv, List.mem_append] at hv_and
                rcases hv_and with hvAx | hvBy
                · rw [SMT.fv, List.mem_append] at hvAx
                  rcases hvAx with hvA | hvx
                  · exact List.mem_append_left _ hvA
                  · exfalso
                    apply hv_ne_xy
                    have : v = x := by simpa [SMT.fv] using hvx
                    simp [this]
                · rw [SMT.fv, List.mem_append] at hvBy
                  rcases hvBy with hvB | hvy
                  · exact List.mem_append_right _ hvB
                  · exfalso
                    apply hv_ne_xy
                    have : v = y := by simpa [SMT.fv] using hvy
                    simp [this]
            · rw [SMT.fv, List.mem_removeAll_iff] at hv_right
              obtain ⟨hv_imp, hv_ne_xyy'⟩ := hv_right
              rw [SMT.fv, List.mem_append] at hv_imp
              rcases hv_imp with hv_and | hv_eq
              · rw [SMT.fv, List.mem_append] at hv_and
                rcases hv_and with hv1 | hv2
                · rw [SMT.fv, List.mem_append] at hv1
                  rcases hv1 with hvR | hvpair
                  · exfalso
                    apply hv_ne_R
                    simpa [SMT.fv] using hvR
                  · rw [SMT.fv, List.mem_append] at hvpair
                    rcases hvpair with hvx | hvy
                    · exfalso
                      apply hv_ne_xyy'
                      have : v = x := by simpa [SMT.fv] using hvx
                      simp [this]
                    · exfalso
                      apply hv_ne_xyy'
                      have : v = y := by simpa [SMT.fv] using hvy
                      simp [this]
                · rw [SMT.fv, List.mem_append] at hv2
                  rcases hv2 with hvR | hvpair
                  · exfalso
                    apply hv_ne_R
                    simpa [SMT.fv] using hvR
                  · rw [SMT.fv, List.mem_append] at hvpair
                    rcases hvpair with hvx | hvy'
                    · exfalso
                      apply hv_ne_xyy'
                      have : v = x := by simpa [SMT.fv] using hvx
                      simp [this]
                    · exfalso
                      apply hv_ne_xyy'
                      have : v = y' := by simpa [SMT.fv] using hvy'
                      simp [this]
              · rw [SMT.fv, List.mem_append] at hv_eq
                rcases hv_eq with hvy | hvy'
                · exfalso
                  apply hv_ne_xyy'
                  have : v = y := by simpa [SMT.fv] using hvy
                  simp [this]
                · exfalso
                  apply hv_ne_xyy'
                  have : v = y' := by simpa [SMT.fv] using hvy'
                  simp [this]

          mspec Std.Do.Spec.pure
          mpure_intro
          and_intros
          · intro v hv
            rw [StEy'_used_eq, StEy_used_eq, StEx_used_eq,
              StER_used_eq, St₄_used_eq, St₃_used_eq,
              St₂_used_eq, St₁_used_eq]
            exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hv)))
          · simp [StEy'_types_final]
          · intro v hv
            rw [StEy'_types_final] at hv
            rw [StEy'_used_eq, StEy_used_eq, StEx_used_eq,
              StER_used_eq, St₄_used_eq, St₃_used_eq,
              St₂_used_eq, St₁_used_eq]
            exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (St₀_keys hv))))
          · exact (BType.SupportedSMT.setPred
              (BType.SupportedSMT.setPred
                (BType.SupportedSMT.prod hrho hsigma))).nonemptyCanonicalCastPath
          · simpa [StEy'_types_final, tpfun, pfunBody, tauR] using
              typ_tpfun
          · intro v hv hv_not
            simpa [StEy'_types_final] using hv_not
          · intro Theta hcov_A hcov_B Theta_none
              respects_A respects_B Theta_dom X Y hX hY
              denA denB hden_A hden_B A_rel B_rel
            have denA_type :=
              SMT.RenamingContext.denote_type_of_typing_fv
                typ_A respects_A hcov_A hden_A
            have denB_type :=
              SMT.RenamingContext.denote_type_of_typing_fv
                typ_B respects_B hcov_B hden_B
            rcases denA with ⟨Aval, sigmaA, hAval⟩
            rcases denB with ⟨Bval, sigmaB, hBval⟩
            dsimp at denA_type denB_type
            subst sigmaA
            subst sigmaB
            have hcov_tpfun : RenamingContext.CoversFV Theta tpfun := by
              intro v hv
              have hv' := fv_tpfun_sub hv
              rw [List.mem_append] at hv'
              exact hv'.elim (hcov_A v) (hcov_B v)
            have R_not_fv_A : R ∉ SMT.fv A := fun hv =>
              R_fresh (SMT.Typing.mem_context_of_mem_fv typ_A hv)
            have R_not_fv_B : R ∉ SMT.fv B := fun hv =>
              R_fresh (SMT.Typing.mem_context_of_mem_fv typ_B hv)
            have x_not_fv_A : x ∉ SMT.fv A := fun hv =>
              x_fresh_ctx (SMT.Typing.mem_context_of_mem_fv typ_A hv)
            have x_not_fv_B : x ∉ SMT.fv B := fun hv =>
              x_fresh_ctx (SMT.Typing.mem_context_of_mem_fv typ_B hv)
            have y_not_fv_A : y ∉ SMT.fv A := fun hv =>
              y_fresh_ctx (SMT.Typing.mem_context_of_mem_fv typ_A hv)
            have y_not_fv_B : y ∉ SMT.fv B := fun hv =>
              y_fresh_ctx (SMT.Typing.mem_context_of_mem_fv typ_B hv)
            have target_respects :
                SMT.RenamingContext.RespectsTypeContextOnFV
                  Theta St₀.types tpfun := by
              intro v sigma hv hlookup
              have hv' := fv_tpfun_sub hv
              rw [List.mem_append] at hv'
              exact hv'.elim
                (fun h => respects_A h hlookup)
                (fun h => respects_B h hlookup)
            obtain ⟨denOut, hdenOut, htyOut⟩ :=
              SMT.RenamingContext.denote_exists_of_typing_fv
                typ_tpfun target_respects hcov_tpfun
            rcases denOut with ⟨Uout, sigmaOut, hUout⟩
            dsimp at htyOut
            subst sigmaOut
            have hUout' : Uout ∈ ⟦SMTType.fun
                (SMTType.fun (SMTType.pair rho sigma) SMTType.bool)
                SMTType.bool⟧ᶻ := by
              simpa [tauR] using hUout
            let denOut' : SMT.Dom.{u} := ⟨Uout, SMTType.fun
              (SMTType.fun (SMTType.pair rho sigma) SMTType.bool)
              SMTType.bool, hUout'⟩
            have hdenOut' : ⟦tpfun.abstract Theta hcov_tpfun⟧ˢ =
                some denOut' := by
              simpa [denOut', tauR, proof_irrel_heq] using hdenOut
            have hcovOutDirect : RenamingContext.CoversFV Theta
                (SMT.Term.lambda [R]
                  [SMTType.fun (SMTType.pair rho sigma) SMTType.bool]
                  (pfunBodyTerm A B R x y y' rho sigma)) := by
              simpa [tpfun, pfunBody, pfunBodyTerm, tauR] using hcov_tpfun
            have hdenOutDirect :
                ⟦(SMT.Term.lambda [R]
                  [SMTType.fun (SMTType.pair rho sigma) SMTType.bool]
                  (pfunBodyTerm A B R x y y' rho sigma)).abstract
                    Theta hcovOutDirect⟧ˢ = some denOut' := by
              simpa [tpfun, pfunBody, pfunBodyTerm, tauR, denOut',
                proof_irrel_heq] using hdenOut'
            have Out_rel : RDomCastSupported
                (⟨pfunSet X Y,
                  BType.set (BType.set (alpha ×ᴮ beta)),
                  pfunSet_mem_btype hX hY⟩ : _root_.B.Dom)
                denOut' := by
              apply represented_pfun_direct_lambda
                hrho hsigma hX hY hAval hBval hUout'
                R_not_fv_A R_not_fv_B
                x_not_fv_A x_not_fv_B y_not_fv_A y_not_fv_B
                hR_ne_x hR_ne_y hR_ne_y'
                hx_ne_y hx_ne_y' hy_ne_y'
                hcov_A hcov_B hden_A hden_B A_rel B_rel
                hcovOutDirect hdenOutDirect
            refine ⟨Theta,
              (by simpa [tpfun, pfunBody, tauR] using hcov_tpfun),
              denOut', ?_⟩
            and_intros
            · exact RenamingContext.extends_refl Theta
            · intro v hv
              apply Theta_none
              intro hvused
              apply hv
              rw [StEy'_used_eq, StEy_used_eq, StEx_used_eq,
                StER_used_eq, St₄_used_eq, St₃_used_eq,
                St₂_used_eq, St₁_used_eq]
              exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hvused)))
            · simpa [StEy'_types_final, tpfun, pfunBody, tauR] using
                target_respects
            · intro v hv
              rw [StEy'_types_final]
              exact Theta_dom v hv
            · simpa [tpfun, pfunBody, tauR] using hdenOut'
            · rfl
            · exact Out_rel.1.1
            · exact Out_rel.1.2.1
            · exact Out_rel.1.2.2
            · exact Out_rel.2

/-- Satisfying-assignment construction for one completed partial-function
tail run. -/
private abbrev EncodePFunTailRepTotalSemantics.{u}
    (alpha beta : BType) (A B out : SMT.Term)
    (sigmaOut : SMTType)
    (Lambda Gamma : SMT.TypeContext)
    (used usedOut : List SMT.𝒱) : Prop :=
  ∀ (Theta : SMT.RenamingContext.Context.{u})
    (hA : RenamingContext.CoversFV Theta A)
    (hB : RenamingContext.CoversFV Theta B),
    (∀ v ∉ used, Theta v = none) →
    SMT.RenamingContext.RespectsTypeContextOnFV Theta Lambda A →
    SMT.RenamingContext.RespectsTypeContextOnFV Theta Lambda B →
    (∀ v, Theta v ≠ none → v ∈ Lambda) →
    ∀ (X Y : ZFSet.{u})
      (hX : X ∈ ⟦BType.set alpha⟧ᶻ)
      (hY : Y ∈ ⟦BType.set beta⟧ᶻ)
      (denA denB : SMT.Dom.{u}),
      ⟦A.abstract Theta hA⟧ˢ = some denA →
      ⟦B.abstract Theta hB⟧ˢ = some denB →
      RDomCastSupported
        (⟨X, BType.set alpha, hX⟩ : _root_.B.Dom) denA →
      RDomCastSupported
        (⟨Y, BType.set beta, hY⟩ : _root_.B.Dom) denB →
      ∃ (Theta' : SMT.RenamingContext.Context.{u})
        (hcov : RenamingContext.CoversFV Theta' out)
        (denOut : SMT.Dom.{u}),
        RenamingContext.Extends Theta' Theta ∧
        (∀ v ∉ usedOut, Theta' v = none) ∧
        SMT.RenamingContext.RespectsTypeContextOnFV Theta' Gamma out ∧
        (∀ v, Theta' v ≠ none → v ∈ Gamma) ∧
        ⟦out.abstract Theta' hcov⟧ˢ = some denOut ∧
        denOut.snd.fst = sigmaOut ∧
        RDomCastSupported
          (⟨pfunSet X Y,
            BType.set (BType.set (alpha ×ᴮ beta)),
            pfunSet_mem_btype hX hY⟩ : _root_.B.Dom) denOut

/-- Soundness of the direct partial-function lambda under any target
assignment that denotes both encoded operand sets. -/
private abbrev EncodePFunTailRepGuardedSemantics.{u}
    (alpha beta : BType) (A B out : SMT.Term)
    (rho sigma sigmaOut : SMTType) : Prop :=
  ∀ (Theta : SMT.RenamingContext.Context.{u})
    (hcovA : RenamingContext.CoversFV Theta A)
    (hcovB : RenamingContext.CoversFV Theta B)
    (X Y : ZFSet.{u})
    (hX : X ∈ ⟦BType.set alpha⟧ᶻ)
    (hY : Y ∈ ⟦BType.set beta⟧ᶻ)
    (denA denB : SMT.Dom.{u}),
    ⟦A.abstract Theta hcovA⟧ˢ = some denA →
    ⟦B.abstract Theta hcovB⟧ˢ = some denB →
    denA.snd.fst = SMTType.fun rho SMTType.bool →
    denB.snd.fst = SMTType.fun sigma SMTType.bool →
    RDomCastSupported
      (⟨X, BType.set alpha, hX⟩ : _root_.B.Dom) denA →
    RDomCastSupported
      (⟨Y, BType.set beta, hY⟩ : _root_.B.Dom) denB →
    ∀ (hcovOut : RenamingContext.CoversFV Theta out)
      (denOut : SMT.Dom.{u}),
      ⟦out.abstract Theta hcovOut⟧ˢ = some denOut →
      denOut.snd.fst = sigmaOut →
      RDomCastSupported
        (⟨pfunSet X Y,
          BType.set (BType.set (alpha ×ᴮ beta)),
          pfunSet_mem_btype hX hY⟩ : _root_.B.Dom) denOut

/-- Declaration-aware operational contract for the partial-function tail.
The four local binders are erased from the type context and create no helper
declarations. -/
private abbrev EncodePFunTailRepScopedSpec.{u}
    (alpha beta : BType) (rho sigma : SMTType)
    (_hrho : BType.SupportedSMT alpha rho)
    (_hsigma : BType.SupportedSMT beta sigma)
    (A B : SMT.Term) : Prop :=
  ∀ {Lambda : SMT.TypeContext} {n : ℕ} {used : List SMT.𝒱}
    {decl : SMT.Chunk},
    Lambda ⊢ˢ A : SMTType.fun rho SMTType.bool →
    Lambda ⊢ˢ B : SMTType.fun sigma SMTType.bool →
    (∀ v ∈ SMT.bv A, v ∈ used) →
    (∀ v ∈ SMT.bv B, v ∈ used) →
    ⦃fun ⟨env, Lambda'⟩ =>
      ⌜Lambda' = Lambda ∧ env.freshvarsc = n ∧
        Lambda.keys ⊆ env.usedVars ∧ env.usedVars = used ∧
        env.declarations = decl⌝⦄
    encodePFunTail A B rho sigma
    ⦃⇓? ⟨out, sigmaOut⟩ ⟨env', Gamma'⟩ =>
      ⌜used ⊆ env'.usedVars ∧
        Lambda ⊆ Gamma' ∧
        Gamma'.keys ⊆ env'.usedVars ∧
        Nonempty (sigmaOut ~>
          (BType.set (BType.set (alpha ×ᴮ beta))).toSMTType) ∧
        Gamma' ⊢ˢ out : sigmaOut ∧
        (∀ v ∈ used, v ∉ Lambda → v ∉ Gamma') ∧
        EncodePFunTailRepTotalSemantics.{u}
          alpha beta A B out sigmaOut
          Lambda Gamma' used env'.usedVars ∧
        Gamma' = Lambda ∧ env'.declarations = decl ∧
        (∀ v ∈ SMT.fv A, v ∈ SMT.fv out) ∧
        (∀ v ∈ SMT.fv B, v ∈ SMT.fv out) ∧
        SMT.fv out ⊆ SMT.fv A ++ SMT.fv B ∧
        EncodePFunTailRepGuardedSemantics.{u}
          alpha beta A B out rho sigma sigmaOut⌝⦄

set_option maxHeartbeats 7000000 in
private theorem encodePFunTail_rep_scoped_spec.{u}
    (alpha beta : BType) (rho sigma : SMTType)
    (hrho : BType.SupportedSMT alpha rho)
    (hsigma : BType.SupportedSMT beta sigma)
    (A B : SMT.Term) :
    EncodePFunTailRepScopedSpec.{u}
      alpha beta rho sigma hrho hsigma A B := by
  unfold EncodePFunTailRepScopedSpec
  intro Lambda n used decl typA typB bvA_used bvB_used
  mstart
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_keys, rfl, rfl⟩ := pre
  mspec (Std.Do.Triple.and _
    (encodePFunTail_rep_spec alpha beta rho sigma hrho hsigma A B
      typA typB bvA_used bvB_used)
    (encodePFunTail_shape_decls A B rho sigma
      (n := St.env.freshvarsc) (used := St.env.usedVars)
      (decl := St.env.declarations)))
  rename_i outPair
  obtain ⟨out, sigmaOut⟩ := outPair
  mrename_i post
  mintro ∀StOut
  mpure post
  obtain ⟨opPost, shape⟩ := post
  obtain ⟨usedSub, typesSub, keysSub, path, typOut,
    preserves, total⟩ := opPost
  obtain ⟨R, x, y, y', outEq, sigmaEq, typesEq, declEq,
    RFresh, xFresh, yFresh, y'Fresh,
    hR_ne_x, hR_ne_y, hR_ne_y', hx_ne_y, hx_ne_y',
    hy_ne_y'⟩ := shape
  dsimp at outEq sigmaEq
  subst out
  subst sigmaOut
  have R_not_fv_A : R ∉ SMT.fv A :=
    funNotMemFvOfNotMemContext typA RFresh
  have R_not_fv_B : R ∉ SMT.fv B :=
    funNotMemFvOfNotMemContext typB RFresh
  have x_not_fv_A : x ∉ SMT.fv A :=
    funNotMemFvOfNotMemContext typA xFresh
  have x_not_fv_B : x ∉ SMT.fv B :=
    funNotMemFvOfNotMemContext typB xFresh
  have y_not_fv_A : y ∉ SMT.fv A :=
    funNotMemFvOfNotMemContext typA yFresh
  have y_not_fv_B : y ∉ SMT.fv B :=
    funNotMemFvOfNotMemContext typB yFresh
  have observesA : ∀ v ∈ SMT.fv A,
      v ∈ SMT.fv (SMT.Term.lambda [R]
        [SMTType.fun (SMTType.pair rho sigma) SMTType.bool]
        (pfunBodyTerm A B R x y y' rho sigma)) := by
    intro v hv
    apply SMT.fv.mem_lambda
    constructor
    · apply SMT.fv.mem_and
      left
      apply SMT.fv.mem_forall
      constructor
      · apply SMT.fv.mem_imp
        right
        apply SMT.fv.mem_and
        left
        exact SMT.fv.mem_app (Or.inl hv)
      · intro h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl
        · exact x_not_fv_A hv
        · exact y_not_fv_A hv
    · intro h
      rw [List.mem_singleton] at h
      subst v
      exact R_not_fv_A hv
  have observesB : ∀ v ∈ SMT.fv B,
      v ∈ SMT.fv (SMT.Term.lambda [R]
        [SMTType.fun (SMTType.pair rho sigma) SMTType.bool]
        (pfunBodyTerm A B R x y y' rho sigma)) := by
    intro v hv
    apply SMT.fv.mem_lambda
    constructor
    · apply SMT.fv.mem_and
      left
      apply SMT.fv.mem_forall
      constructor
      · apply SMT.fv.mem_imp
        right
        apply SMT.fv.mem_and
        right
        exact SMT.fv.mem_app (Or.inl hv)
      · intro h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl
        · exact x_not_fv_B hv
        · exact y_not_fv_B hv
    · intro h
      rw [List.mem_singleton] at h
      subst v
      exact R_not_fv_B hv
  mpure_intro
  refine ⟨usedSub, typesSub, keysSub, path, typOut, preserves,
    total, typesEq, declEq, observesA, observesB,
    pfun_lambda_fv_subset A B R x y y' rho sigma, ?_⟩
  intro Theta hcovA hcovB X Y hX hY denA denB
    hdenA hdenB hdenAType hdenBType Xrel Yrel
    hcovOut denOut hdenOut hdenOutType
  rcases denA with ⟨Aval, tauA, hAval⟩
  dsimp at hdenAType
  subst tauA
  rcases denB with ⟨Bval, tauB, hBval⟩
  dsimp at hdenBType
  subst tauB
  rcases denOut with ⟨Uout, tauOut, hUout⟩
  dsimp at hdenOutType
  subst tauOut
  have hcovOutDirect : RenamingContext.CoversFV Theta
      (SMT.Term.lambda [R]
        [SMTType.fun (SMTType.pair rho sigma) SMTType.bool]
        (pfunBodyTerm A B R x y y' rho sigma)) := by
    simpa [pfunBodyTerm, pfunClosureTerm,
      pfunFunctionalityTerm] using hcovOut
  have hdenOutDirect :
      ⟦(SMT.Term.lambda [R]
        [SMTType.fun (SMTType.pair rho sigma) SMTType.bool]
        (pfunBodyTerm A B R x y y' rho sigma)).abstract
          Theta hcovOutDirect⟧ˢ =
        some (⟨Uout, SMTType.fun
          (SMTType.fun (SMTType.pair rho sigma) SMTType.bool)
          SMTType.bool, hUout⟩ : SMT.Dom) := by
    simpa [pfunBodyTerm, pfunClosureTerm,
      pfunFunctionalityTerm, proof_irrel_heq] using hdenOut
  exact represented_pfun_direct_lambda
    hrho hsigma hX hY hAval hBval hUout
    R_not_fv_A R_not_fv_B x_not_fv_A x_not_fv_B
    y_not_fv_A y_not_fv_B hR_ne_x hR_ne_y hR_ne_y'
    hx_ne_y hx_ne_y' hy_ne_y' hcovA hcovB
    (by simpa only [proof_irrel_heq] using hdenA)
    (by simpa only [proof_irrel_heq] using hdenB)
    (by simpa only [proof_irrel_heq] using Xrel)
    (by simpa only [proof_irrel_heq] using Yrel)
    hcovOutDirect hdenOutDirect

set_option maxHeartbeats 9000000 in
theorem encodeTerm_rep_spec.pfun_case.{u}
    (S T : B.Term)
    (S_ih : EncodeTermRepIH.{u} S)
    (T_ih : EncodeTermRepIH.{u} T)
    (E : B.Env) {Lambda : SMT.TypeContext} {tau : BType}
    (typ_t : E.context ⊢ᴮ B.Term.pfun S T : tau)
    {Delta : B.RenamingContext.Context}
    (Delta_fv : ∀ v ∈ B.fv (B.Term.pfun S T),
      (Delta v).isSome = true)
    {Delta0 : SMT.RenamingContext.Context.{u}}
    (related : RValuationCastSupportedOnFV Delta Delta0
      (B.Term.pfun S T))
    {used : List SMT.𝒱}
    (Delta0_none : ∀ v ∉ used, Delta0 v = none)
    (Delta0_dom : ∀ v, Delta0 v ≠ none → v ∈ Lambda)
    {U : ZFSet.{u}} {hU : U ∈ ⟦tau⟧ᶻ}
    (den_t : ⟦(B.Term.pfun S T).abstract Delta Delta_fv⟧ᴮ =
      some ⟨U, tau, hU⟩)
    (vars_used : ∀ v ∈ (B.Term.pfun S T).vars, v ∈ used)
    (Lambda_inv : ∀ v ∈ (B.Term.pfun S T).vars,
      v ∈ Lambda → v ∈ E.context)
    (bv_nodup : (B.bv (B.Term.pfun S T)).Nodup)
    (respects : B.RenamingContext.RespectsTypeContextOnFV
      Delta0 Lambda (B.Term.pfun S T))
    (fv_in_Lambda : ∀ v ∈ B.fv (B.Term.pfun S T), v ∈ Lambda)
    (wf : B.RenWF E.context Delta)
    {n : ℕ} :
    ⦃fun ⟨E0, Lambda'⟩ =>
      ⌜Lambda' = Lambda ∧ E0.freshvarsc = n ∧
        Lambda.keys ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
    encodeTerm (B.Term.pfun S T) E
    ⦃⇓? (⟨t', sigma⟩ : SMT.Term × SMTType) ⟨E', Gamma'⟩ =>
      ⌜EncodeTermRepPost (B.Term.pfun S T) tau Lambda Delta Delta0
        used U hU E t' sigma E' Gamma'⌝⦄ := by
  mstart
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_keys, St_used_eq⟩ := pre
  rw [encodeTerm_pfun_via_tail]
  obtain ⟨alpha, beta, rfl, typ_S, typ_T⟩ := B.Typing.pfunE typ_t
  obtain ⟨X, Y, hX, hY, den_S, den_T, rfl⟩ :=
    B.denote_pfun_inv_rep Delta_fv den_t
  have fv_S_sub : B.fv S ⊆ B.fv (B.Term.pfun S T) := by
    intro v hv
    simpa [B.fv] using (Or.inl hv : v ∈ B.fv S ∨ v ∈ B.fv T)
  have fv_T_sub : B.fv T ⊆ B.fv (B.Term.pfun S T) := by
    intro v hv
    simpa [B.fv] using (Or.inr hv : v ∈ B.fv S ∨ v ∈ B.fv T)
  have S_bv_nodup : (B.bv S).Nodup := by
    have h := bv_nodup
    simp only [B.bv, List.nodup_append] at h
    exact h.1
  have T_bv_nodup : (B.bv T).Nodup := by
    have h := bv_nodup
    simp only [B.bv, List.nodup_append] at h
    exact h.2.1
  have ST_bv_disj : ∀ a ∈ B.bv S, ∀ b ∈ B.bv T, a ≠ b := by
    have h := bv_nodup
    simp only [B.bv, List.nodup_append] at h
    exact h.2.2

  mspec (Std.Do.Triple.and _
    (Std.Do.Triple.and _
      (S_ih E typ_S
        (fun v hv => Delta_fv v (fv_S_sub hv))
        (related.mono_fv fv_S_sub)
        Delta0_none Delta0_dom den_S
        (fun v hv => vars_used v (by
          simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
            List.mem_append] at hv ⊢
          rcases hv with h | h <;> [left; right] <;> exact .inl h))
        (fun v hv => Lambda_inv v (by
          simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
            List.mem_append] at hv ⊢
          rcases hv with h | h <;> [left; right] <;> exact .inl h))
        S_bv_nodup (respects.mono_fv fv_S_sub)
        (fun v hv => fv_in_Lambda v (fv_S_sub hv)) wf
        (n := St.env.freshvarsc))
      (encodeTerm_bv_used E (t := S) (used := St.env.usedVars)
        (n := St.env.freshvarsc) (decl := St.env.declarations)))
    (encodeTerm_bv_notMem_used E (t := S) (used := St.env.usedVars)
      (n := St.env.freshvarsc) (decl := St.env.declarations)))
  clear S_ih
  rename_i out_S
  obtain ⟨Senc, sigmaS⟩ := out_S
  mrename_i post_S
  mintro ∀StS
  mpure post_S
  dsimp at post_S
  obtain ⟨⟨S_post, bv_Senc_used, _S_used_sub, _S_decl⟩,
      bv_Senc_not_used, _S_used_sub', _S_decl'⟩ := post_S
  obtain ⟨used_sub_S, types_sub_S, keys_sub_S, covers_S,
    _path_S, typ_Senc, _shape_S, preserves_S,
    DeltaS, hcov_Senc, DeltaS_ext, _related_S, DeltaS_none,
    _respects_S, target_respects_Senc, DeltaS_dom,
    denSenc, hden_Senc, hdenSenc_type, S_rel, S_total⟩ := S_post
  rcases denSenc with ⟨Sval, sigmaSden, hSval⟩
  dsimp at hdenSenc_type
  subst sigmaSden
  cases S_rel.supported with
  | optionFun gamma delta =>
      mspec Std.Do.Spec.throw_StateT
  | @setPred _ rho hrho =>
    have related_T : RValuationCastSupportedOnFV Delta DeltaS T :=
      (related.mono_fv fv_T_sub).of_extends DeltaS_ext
    have respects_T : B.RenamingContext.RespectsTypeContextOnFV
        DeltaS StS.types T :=
      respects.of_extends DeltaS_ext types_sub_S fv_T_sub fv_in_Lambda
    mspec (Std.Do.Triple.and _
      (T_ih E typ_T
        (fun v hv => Delta_fv v (fv_T_sub hv)) related_T
        DeltaS_none DeltaS_dom den_T
        (fun v hv => used_sub_S (vars_used v (by
          simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
            List.mem_append] at hv ⊢
          rcases hv with h | h <;> [left; right] <;> exact .inr h)))
        (fun v hv hGamma => by
          have hv_pfun : v ∈ (B.Term.pfun S T).vars := by
            simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
              List.mem_append] at hv ⊢
            rcases hv with h | h <;> [left; right] <;> exact .inr h
          by_cases hv_Lambda : v ∈ St.types
          · exact Lambda_inv v hv_pfun hv_Lambda
          · have hv_vars_S : v ∈ B.Term.vars S := by
              by_contra hnot
              exact absurd hGamma
                (preserves_S v (vars_used v hv_pfun) hv_Lambda hnot)
            rcases B.Term.mem_vars_iff.mp hv_vars_S with hSfv | hSbv
            · exact B.Typing.typed_by_fv typ_S hSfv
            · rcases B.Term.mem_vars_iff.mp hv with hTfv | hTbv
              · exact absurd (B.Typing.typed_by_fv typ_T hTfv)
                  (B.Typing.bv_notMem_context typ_S v hSbv)
              · exact absurd rfl (ST_bv_disj v hSbv v hTbv))
        T_bv_nodup respects_T
        (fun v hv => AList.mem_of_subset types_sub_S
          (fv_in_Lambda v (fv_T_sub hv))) wf
        (n := StS.env.freshvarsc))
      (encodeTerm_bv_used E (t := T) (used := StS.env.usedVars)
        (n := StS.env.freshvarsc) (decl := StS.env.declarations)))
    clear T_ih
    rename_i out_T
    obtain ⟨Tenc, sigmaT⟩ := out_T
    mrename_i post_T
    mintro ∀StT
    mpure post_T
    dsimp at post_T
    obtain ⟨T_post, bv_Tenc_used, _T_used_sub, _T_decl⟩ := post_T
    obtain ⟨used_sub_T, types_sub_T, keys_sub_T, covers_T,
      _path_T, typ_Tenc, _shape_T, preserves_T,
      DeltaT, hcov_Tenc, DeltaT_ext, _related_T, DeltaT_none,
      _respects_T, target_respects_Tenc, DeltaT_dom,
      denTenc, hden_Tenc, hdenTenc_type, T_rel, T_total⟩ := T_post
    rcases denTenc with ⟨Tval, sigmaTden, hTval⟩
    dsimp at hdenTenc_type
    subst sigmaTden
    cases T_rel.supported with
    | optionFun gamma delta =>
        mspec Std.Do.Spec.throw_StateT
    | @setPred _ sigma hsigma =>
      have bv_Senc_final : ∀ v ∈ SMT.bv Senc,
          v ∈ StT.env.usedVars :=
        fun v hv => used_sub_T (bv_Senc_used v hv)
      have bv_Senc_not_final : ∀ v ∈ SMT.bv Senc,
          v ∉ StT.types :=
        fun v hv => preserves_T v (bv_Senc_used v hv)
          (SMT.Typing.bv_notMem_context typ_Senc v hv)
          (by
            rw [B.Term.notMem_vars_iff]
            refine ⟨?_, ?_⟩
            · intro hfvT
              exact SMT.Typing.bv_notMem_context typ_Senc v hv
                (AList.mem_of_subset types_sub_S
                  (fv_in_Lambda v (fv_T_sub hfvT)))
            · intro hbT
              exact bv_Senc_not_used v hv
                (St_used_eq ▸ vars_used v (by
                  simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
                    List.mem_append]
                  right
                  right
                  exact hbT)))
      have typ_Senc_final : StT.types ⊢ˢ Senc :
          SMTType.fun rho SMTType.bool :=
        SMT.Typing.weakening types_sub_T typ_Senc bv_Senc_not_final
      have hcov_Senc_final : RenamingContext.CoversFV DeltaT Senc :=
        RenamingContext.coversFV_of_extends_of_coversFV
          DeltaT_ext hcov_Senc
      have hden_Senc_final :
          ⟦Senc.abstract DeltaT hcov_Senc_final⟧ˢ =
            some (⟨Sval, SMTType.fun rho SMTType.bool, hSval⟩ :
              SMT.Dom) := by
        have hagree := RenamingContext.agreesOnFV_of_extends_of_coversFV
          DeltaT_ext hcov_Senc
        have hcongr := RenamingContext.denote_congr_of_agreesOnFV
          (t := Senc) (h1 := hcov_Senc_final)
          (h2 := hcov_Senc) hagree
        simpa [RenamingContext.denote] using hcongr.trans hden_Senc
      have target_respects_Senc_final :
          SMT.RenamingContext.RespectsTypeContextOnFV
            DeltaT StT.types Senc :=
        target_respects_Senc.of_extends
          DeltaT_ext types_sub_T typ_Senc

      mspec encodePFunTail_rep_spec alpha beta rho sigma hrho hsigma
        Senc Tenc
        typ_Senc_final typ_Tenc bv_Senc_final bv_Tenc_used
      rename_i out_pfun
      obtain ⟨PFunEnc, sigmaPFun⟩ := out_pfun
      mrename_i post_pfun
      mintro ∀StPFun
      mpure post_pfun
      obtain ⟨used_sub_pfun, types_sub_pfun, keys_sub_pfun, path_pfun,
        typ_PFunEnc, preserves_pfun, semantic_pfun⟩ := post_pfun
      obtain ⟨DeltaPFun, hcov_PFunEnc, denPFun, DeltaPFun_ext,
          DeltaPFun_none, target_respects_PFunEnc, DeltaPFun_dom,
          hden_PFunEnc, hdenPFun_type, PFun_rel⟩ :=
        semantic_pfun DeltaT hcov_Senc_final hcov_Tenc DeltaT_none
          target_respects_Senc_final target_respects_Tenc DeltaT_dom
          X Y hX hY
          (⟨Sval, SMTType.fun rho SMTType.bool, hSval⟩ : SMT.Dom)
          (⟨Tval, SMTType.fun sigma SMTType.bool, hTval⟩ : SMT.Dom)
          hden_Senc_final hden_Tenc S_rel T_rel
      have DeltaT_ext0 := RenamingContext.extends_trans DeltaT_ext DeltaS_ext
      have DeltaPFun_ext0 :=
        RenamingContext.extends_trans DeltaPFun_ext DeltaT_ext0
      have types_sub0 : St.types ⊆ StPFun.types :=
        fun _ h => types_sub_pfun (types_sub_T (types_sub_S h))

      mpure_intro
      and_intros
      · intro v hv
        exact used_sub_pfun (used_sub_T
          (used_sub_S (by simpa [St_used_eq] using hv)))
      · exact types_sub0
      · exact keys_sub_pfun
      · intro v hv
        rw [B.fv, List.mem_append] at hv
        exact hv.elim
          (fun h => used_sub_pfun (used_sub_T (covers_S v h)))
          (fun h => used_sub_pfun (covers_T v h))
      · exact path_pfun
      · exact typ_PFunEnc
      · trivial
      · intro v hv hLambda hvars
        have hv_StS : v ∈ StS.env.usedVars :=
          used_sub_S (by simpa [St_used_eq] using hv)
        have hv_not_StS : v ∉ StS.types :=
          preserves_S v (by simpa [St_used_eq] using hv) hLambda
            ((B.Term.notMem_vars_pfun.mp hvars).1)
        have hv_not_StT : v ∉ StT.types :=
          preserves_T v hv_StS hv_not_StS
            ((B.Term.notMem_vars_pfun.mp hvars).2)
        exact preserves_pfun v (used_sub_T hv_StS) hv_not_StT
      · refine ⟨DeltaPFun, hcov_PFunEnc, DeltaPFun_ext0,
          related.of_extends DeltaPFun_ext0, DeltaPFun_none, ?_,
          target_respects_PFunEnc, DeltaPFun_dom, denPFun,
          hden_PFunEnc, hdenPFun_type, ?_, ?_⟩
        · exact respects.of_extends DeltaPFun_ext0 types_sub0
            (fun _ h => h) fv_in_Lambda
        · simpa only [proof_irrel_heq] using PFun_rel
        · intro Delta_alt Delta_fv_alt Delta0_alt related_alt wf_alt
            Delta0_alt_none respects_alt Delta0_alt_dom
            U_alt hU_alt den_t_alt
          obtain ⟨X_alt, Y_alt, hX_alt, hY_alt,
              den_S_alt, den_T_alt, rfl⟩ :=
            B.denote_pfun_inv_rep Delta_fv_alt den_t_alt
          have Delta0_alt_none_S : ∀ v ∉ StS.env.usedVars,
              Delta0_alt v = none := by
            intro v hv
            by_contra hne
            have hv_Lambda := Delta0_alt_dom v hne
            have hv_used : v ∈ used := by
              rw [← St_used_eq]
              exact St_keys hv_Lambda
            exact hv (used_sub_S hv_used)
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
          have DeltaS_alt_none_T : ∀ v ∉ StT.env.usedVars,
              DeltaS_alt v = none := by
            intro v hv
            apply DeltaS_alt_none v
            intro hvS
            exact hv (used_sub_T hvS)
          have related_alt_T : RValuationCastSupportedOnFV
              Delta_alt DeltaS_alt T :=
            (related_alt.mono_fv fv_T_sub).of_extends DeltaS_alt_ext
          have respects_alt_T : B.RenamingContext.RespectsTypeContextOnFV
              DeltaS_alt StS.types T :=
            respects_alt.of_extends DeltaS_alt_ext types_sub_S
              fv_T_sub fv_in_Lambda
          obtain ⟨DeltaT_alt, hcov_Tenc_alt, denTenc_alt,
              DeltaT_alt_ext, _related_T_alt, DeltaT_alt_none,
              _respects_T_alt, target_respects_Tenc_alt,
              DeltaT_alt_dom, hden_Tenc_alt, _hdenTenc_alt_type,
              T_alt_rel⟩ :=
            T_total Delta_alt
              (fun v hv => Delta_fv_alt v (fv_T_sub hv))
              DeltaS_alt related_alt_T wf_alt DeltaS_alt_none_T
              respects_alt_T DeltaS_alt_dom Y_alt hY_alt den_T_alt
          have hcov_Senc_alt_final : RenamingContext.CoversFV
              DeltaT_alt Senc :=
            RenamingContext.coversFV_of_extends_of_coversFV
              DeltaT_alt_ext hcov_Senc_alt
          have hden_Senc_alt_final :
              ⟦Senc.abstract DeltaT_alt hcov_Senc_alt_final⟧ˢ =
                some denSenc_alt := by
            have hagree := RenamingContext.agreesOnFV_of_extends_of_coversFV
              DeltaT_alt_ext hcov_Senc_alt
            have hcongr := RenamingContext.denote_congr_of_agreesOnFV
              (t := Senc) (h1 := hcov_Senc_alt_final)
              (h2 := hcov_Senc_alt) hagree
            simpa [RenamingContext.denote] using
              hcongr.trans hden_Senc_alt
          have target_respects_Senc_alt_final :
              SMT.RenamingContext.RespectsTypeContextOnFV
                DeltaT_alt StT.types Senc :=
            target_respects_Senc_alt.of_extends
              DeltaT_alt_ext types_sub_T typ_Senc
          obtain ⟨DeltaPFun_alt, hcov_PFunEnc_alt, denPFun_alt,
              DeltaPFun_alt_ext, DeltaPFun_alt_none,
              target_respects_PFunEnc_alt, DeltaPFun_alt_dom,
              hden_PFunEnc_alt, hdenPFun_alt_type, PFun_alt_rel⟩ :=
            semantic_pfun DeltaT_alt hcov_Senc_alt_final hcov_Tenc_alt
              DeltaT_alt_none target_respects_Senc_alt_final
              target_respects_Tenc_alt DeltaT_alt_dom
              X_alt Y_alt hX_alt hY_alt denSenc_alt denTenc_alt
              hden_Senc_alt_final hden_Tenc_alt S_alt_rel T_alt_rel
          have DeltaT_alt_ext0 :=
            RenamingContext.extends_trans DeltaT_alt_ext DeltaS_alt_ext
          have DeltaPFun_alt_ext0 :=
            RenamingContext.extends_trans DeltaPFun_alt_ext DeltaT_alt_ext0
          refine ⟨DeltaPFun_alt, hcov_PFunEnc_alt, denPFun_alt,
            DeltaPFun_alt_ext0,
            related_alt.of_extends DeltaPFun_alt_ext0,
            DeltaPFun_alt_none, ?_, target_respects_PFunEnc_alt,
            DeltaPFun_alt_dom, hden_PFunEnc_alt,
            hdenPFun_alt_type, ?_⟩
          · exact respects_alt.of_extends DeltaPFun_alt_ext0 types_sub0
              (fun _ h => h) fv_in_Lambda
          · simpa only [proof_irrel_heq] using PFun_alt_rel

set_option maxHeartbeats 12000000 in
theorem encodeTerm_rep_scoped.pfun_case_from.{u}
    (S T : B.Term)
    (S_ih : EncodeTermRepIH.{u} S)
    (T_ih : EncodeTermRepIH.{u} T)
    (S_scoped : EncodeTermRepScopedFromIH.{u} S)
    (T_scoped : EncodeTermRepScopedFromIH.{u} T)
    (E : B.Env) {Lambda : SMT.TypeContext} {tau : BType}
    (typ_t : E.context ⊢ᴮ B.Term.pfun S T : tau)
    {Delta : B.RenamingContext.Context}
    (Delta_fv : ∀ v ∈ B.fv (B.Term.pfun S T),
      (Delta v).isSome = true)
    {Delta0 : SMT.RenamingContext.Context.{u}}
    (related : RValuationCastSupportedOnFV Delta Delta0
      (B.Term.pfun S T))
    {used : List SMT.𝒱}
    (Delta0_none : ∀ v ∉ used, Delta0 v = none)
    (Delta0_dom : ∀ v, Delta0 v ≠ none → v ∈ Lambda)
    {U : ZFSet.{u}} {hU : U ∈ ⟦tau⟧ᶻ}
    (den_t : ⟦(B.Term.pfun S T).abstract Delta Delta_fv⟧ᴮ =
      some ⟨U, tau, hU⟩)
    (vars_used : ∀ v ∈ (B.Term.pfun S T).vars, v ∈ used)
    (Lambda_inv : ∀ v ∈ (B.Term.pfun S T).vars,
      v ∈ Lambda → v ∈ E.context)
    (bv_nodup : (B.bv (B.Term.pfun S T)).Nodup)
    (respects : B.RenamingContext.RespectsTypeContextOnFV
      Delta0 Lambda (B.Term.pfun S T))
    (fv_in_Lambda : ∀ v ∈ B.fv (B.Term.pfun S T), v ∈ Lambda)
    (wf : B.RenWF E.context Delta)
    {Base : SMT.TypeContext} {Dpre : SMT.Chunk}
    (input_envelope : DeclarationContextEnvelope Base Dpre Lambda)
    (fv_in_Base : ∀ v ∈ B.fv (B.Term.pfun S T), v ∈ Base)
    (Dpre_typing : ScopedSpecsTyping Base Dpre)
    {n : ℕ} {decl : SMT.Chunk} :
    ⦃fun ⟨E0, Lambda'⟩ =>
      ⌜Lambda' = Lambda ∧ E0.freshvarsc = n ∧
        Lambda.keys ⊆ E0.usedVars ∧ E0.usedVars = used ∧
        E0.declarations = decl⌝⦄
    encodeTerm (B.Term.pfun S T) E
    ⦃⇓? (⟨t', sigma⟩ : SMT.Term × SMTType) ⟨E', Gamma'⟩ =>
      ⌜EncodeTermRepScopedPostFrom.{u} (B.Term.pfun S T) E tau
        Base Dpre Lambda decl t' sigma E' Gamma'⌝⦄ := by
  mstart
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_keys, St_used_eq, St_decl_eq⟩ := pre
  rw [encodeTerm_pfun_via_tail]
  obtain ⟨alpha, beta, rfl, typ_S, typ_T⟩ := B.Typing.pfunE typ_t
  obtain ⟨X, Y, hX, hY, den_S, den_T, rfl⟩ :=
    B.denote_pfun_inv_rep Delta_fv den_t
  have fv_S_sub : B.fv S ⊆ B.fv (B.Term.pfun S T) := by
    intro v hv
    simpa [B.fv] using (Or.inl hv : v ∈ B.fv S ∨ v ∈ B.fv T)
  have fv_T_sub : B.fv T ⊆ B.fv (B.Term.pfun S T) := by
    intro v hv
    simpa [B.fv] using (Or.inr hv : v ∈ B.fv S ∨ v ∈ B.fv T)
  have S_bv_nodup : (B.bv S).Nodup := by
    have h := bv_nodup
    simp only [B.bv, List.nodup_append] at h
    exact h.1
  have T_bv_nodup : (B.bv T).Nodup := by
    have h := bv_nodup
    simp only [B.bv, List.nodup_append] at h
    exact h.2.1
  have ST_bv_disj : ∀ a ∈ B.bv S, ∀ b ∈ B.bv T, a ≠ b := by
    have h := bv_nodup
    simp only [B.bv, List.nodup_append] at h
    exact h.2.2

  mspec (Std.Do.Triple.and _
    (Std.Do.Triple.and _
      (Std.Do.Triple.and _
        (S_ih E typ_S
          (fun v hv => Delta_fv v (fv_S_sub hv))
          (related.mono_fv fv_S_sub)
          Delta0_none Delta0_dom den_S
          (fun v hv => vars_used v (by
            simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
              List.mem_append] at hv ⊢
            rcases hv with h | h <;> [left; right] <;> exact .inl h))
          (fun v hv => Lambda_inv v (by
            simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
              List.mem_append] at hv ⊢
            rcases hv with h | h <;> [left; right] <;> exact .inl h))
          S_bv_nodup (respects.mono_fv fv_S_sub)
          (fun v hv => fv_in_Lambda v (fv_S_sub hv)) wf
          (n := St.env.freshvarsc))
        (S_scoped E typ_S
          (fun v hv => Delta_fv v (fv_S_sub hv))
          (related.mono_fv fv_S_sub)
          Delta0_none Delta0_dom den_S
          (fun v hv => vars_used v (by
            simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
              List.mem_append] at hv ⊢
            rcases hv with h | h <;> [left; right] <;> exact .inl h))
          (fun v hv => Lambda_inv v (by
            simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
              List.mem_append] at hv ⊢
            rcases hv with h | h <;> [left; right] <;> exact .inl h))
          S_bv_nodup (respects.mono_fv fv_S_sub)
          (fun v hv => fv_in_Lambda v (fv_S_sub hv)) wf
          input_envelope (fun v hv => fv_in_Base v (fv_S_sub hv))
          Dpre_typing (n := St.env.freshvarsc)
          (decl := St.env.declarations)))
      (encodeTerm_bv_used E (t := S) (used := St.env.usedVars)
        (n := St.env.freshvarsc) (decl := St.env.declarations)))
    (encodeTerm_bv_notMem_used E (t := S) (used := St.env.usedVars)
      (n := St.env.freshvarsc) (decl := St.env.declarations)))
  clear S_ih S_scoped
  rename_i out_S
  obtain ⟨Senc, sigmaS⟩ := out_S
  mrename_i post_S
  mintro ∀StS
  mpure post_S
  dsimp at post_S
  obtain ⟨⟨⟨S_post, S_scoped_post⟩,
      bv_Senc_used, _S_used_sub_struct, DltS_struct,
      S_decl_struct, S_delta_ok⟩,
    bv_Senc_not_used, _S_used_sub_struct', _DltS_struct',
      _S_decl_struct', _S_delta_not_used⟩ := post_S
  obtain ⟨DltS, S_decl_eq, S_trace, S_envelope, S_sc_total,
    S_guard, S_specs_op, S_sc_typing⟩ := S_scoped_post
  have DltS_eq : DltS = DltS_struct := by
    rw [S_decl_eq, St_decl_eq] at S_decl_struct
    exact (List.append_right_inj decl).mp S_decl_struct
  subst DltS_struct
  obtain ⟨used_sub_S, types_sub_S, keys_sub_S, covers_S,
    _path_S, typ_Senc, _shape_S, preserves_S,
    DeltaS, hcov_Senc, DeltaS_ext, _related_S, DeltaS_none,
    _respects_S, target_respects_Senc, DeltaS_dom,
    denSenc, hden_Senc, hdenSenc_type, S_rel, S_total⟩ := S_post
  rcases denSenc with ⟨Sval, sigmaSden, hSval⟩
  dsimp at hdenSenc_type
  subst sigmaSden
  cases S_rel.supported with
  | optionFun gamma delta =>
      mspec Std.Do.Spec.throw_StateT
  | @setPred _ rho hrho =>
    have related_T : RValuationCastSupportedOnFV Delta DeltaS T :=
      (related.mono_fv fv_T_sub).of_extends DeltaS_ext
    have respects_T : B.RenamingContext.RespectsTypeContextOnFV
        DeltaS StS.types T :=
      respects.of_extends DeltaS_ext types_sub_S fv_T_sub fv_in_Lambda
    have vars_used_T : ∀ v ∈ T.vars, v ∈ StS.env.usedVars := by
      intro v hv
      apply used_sub_S
      apply vars_used v
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
        List.mem_append]
      rcases B.Term.mem_vars_iff.mp hv with h | h
      · exact .inl (.inr h)
      · exact .inr (.inr h)
    have Lambda_inv_T : ∀ v ∈ T.vars,
        v ∈ StS.types → v ∈ E.context := by
      intro v hv hGamma
      have hv_pfun : v ∈ (B.Term.pfun S T).vars := by
        simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
          List.mem_append]
        rcases B.Term.mem_vars_iff.mp hv with h | h
        · exact .inl (.inr h)
        · exact .inr (.inr h)
      by_cases hv_Lambda : v ∈ St.types
      · exact Lambda_inv v hv_pfun hv_Lambda
      · have hv_vars_S : v ∈ B.Term.vars S := by
          by_contra hnot
          exact absurd hGamma
            (preserves_S v (vars_used v hv_pfun) hv_Lambda hnot)
        rcases B.Term.mem_vars_iff.mp hv_vars_S with hSfv | hSbv
        · exact B.Typing.typed_by_fv typ_S hSfv
        · rcases B.Term.mem_vars_iff.mp hv with hTfv | hTbv
          · exact absurd (B.Typing.typed_by_fv typ_T hTfv)
              (B.Typing.bv_notMem_context typ_S v hSbv)
          · exact absurd rfl (ST_bv_disj v hSbv v hTbv)

    mspec (Std.Do.Triple.and _
      (Std.Do.Triple.and _
        (Std.Do.Triple.and _
          (T_ih E typ_T
            (fun v hv => Delta_fv v (fv_T_sub hv)) related_T
            DeltaS_none DeltaS_dom den_T vars_used_T Lambda_inv_T
            T_bv_nodup respects_T
            (fun v hv => AList.mem_of_subset types_sub_S
              (fv_in_Lambda v (fv_T_sub hv))) wf
            (n := StS.env.freshvarsc))
          (T_scoped E typ_T
            (fun v hv => Delta_fv v (fv_T_sub hv)) related_T
            DeltaS_none DeltaS_dom den_T vars_used_T Lambda_inv_T
            T_bv_nodup respects_T
            (fun v hv => AList.mem_of_subset types_sub_S
              (fv_in_Lambda v (fv_T_sub hv))) wf
            S_envelope (fun v hv => fv_in_Base v (fv_T_sub hv))
            S_sc_typing.2
            (n := StS.env.freshvarsc)
            (decl := StS.env.declarations)))
        (encodeTerm_bv_used E (t := T) (used := StS.env.usedVars)
          (n := StS.env.freshvarsc) (decl := StS.env.declarations)))
      (encodeTerm_bv_notMem_used E (t := T)
        (used := StS.env.usedVars) (n := StS.env.freshvarsc)
        (decl := StS.env.declarations)))
    clear T_ih T_scoped
    rename_i out_T
    obtain ⟨Tenc, sigmaT⟩ := out_T
    mrename_i post_T
    mintro ∀StT
    mpure post_T
    dsimp at post_T
    obtain ⟨⟨⟨T_post, T_scoped_post⟩,
        bv_Tenc_used, _T_used_sub_struct, DltT_struct,
        T_decl_struct, T_delta_ok⟩,
      bv_Tenc_not_used, _T_used_sub_struct', _DltT_struct',
        _T_decl_struct', T_delta_not_used⟩ := post_T
    obtain ⟨DltT, T_decl_eq, T_trace, T_envelope, T_sc_total,
      T_guard, T_specs_op, T_sc_typing⟩ := T_scoped_post
    have DltT_eq : DltT = DltT_struct := by
      rw [T_decl_eq] at T_decl_struct
      exact (List.append_right_inj StS.env.declarations).mp T_decl_struct
    subst DltT_struct
    have DltT_eq' : DltT = _DltT_struct' := by
      rw [T_decl_eq] at _T_decl_struct'
      exact (List.append_right_inj StS.env.declarations).mp
        _T_decl_struct'
    subst _DltT_struct'
    obtain ⟨used_sub_T, types_sub_T, keys_sub_T, covers_T,
      _path_T, typ_Tenc, _shape_T, preserves_T,
      DeltaT, hcov_Tenc, DeltaT_ext, _related_T, DeltaT_none,
      _respects_T, target_respects_Tenc, DeltaT_dom,
      denTenc, hden_Tenc, hdenTenc_type, T_rel, T_total⟩ := T_post
    rcases denTenc with ⟨Tval, sigmaTden, hTval⟩
    dsimp at hdenTenc_type
    subst sigmaTden
    cases T_rel.supported with
    | optionFun gamma delta =>
        mspec Std.Do.Spec.throw_StateT
    | @setPred _ sigma hsigma =>
      have bv_Senc_final : ∀ v ∈ SMT.bv Senc,
          v ∈ StT.env.usedVars :=
        fun v hv => used_sub_T (bv_Senc_used v hv)
      have bv_Senc_not_final : ∀ v ∈ SMT.bv Senc,
          v ∉ StT.types :=
        fun v hv => preserves_T v (bv_Senc_used v hv)
          (SMT.Typing.bv_notMem_context typ_Senc v hv)
          (by
            rw [B.Term.notMem_vars_iff]
            refine ⟨?_, ?_⟩
            · intro hfvT
              exact SMT.Typing.bv_notMem_context typ_Senc v hv
                (AList.mem_of_subset types_sub_S
                  (fv_in_Lambda v (fv_T_sub hfvT)))
            · intro hbT
              exact bv_Senc_not_used v hv
                (St_used_eq ▸ vars_used v (by
                  simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
                    List.mem_append]
                  right
                  right
                  exact hbT)))
      have typ_Senc_final : StT.types ⊢ˢ Senc :
          SMTType.fun rho SMTType.bool :=
        SMT.Typing.weakening types_sub_T typ_Senc bv_Senc_not_final
      have hcov_Senc_final : RenamingContext.CoversFV DeltaT Senc :=
        RenamingContext.coversFV_of_extends_of_coversFV
          DeltaT_ext hcov_Senc
      have hden_Senc_final :
          ⟦Senc.abstract DeltaT hcov_Senc_final⟧ˢ =
            some (⟨Sval, SMTType.fun rho SMTType.bool, hSval⟩ :
              SMT.Dom) := by
        have hagree := RenamingContext.agreesOnFV_of_extends_of_coversFV
          DeltaT_ext hcov_Senc
        have hcongr := RenamingContext.denote_congr_of_agreesOnFV
          (t := Senc) (h1 := hcov_Senc_final)
          (h2 := hcov_Senc) hagree
        simpa [RenamingContext.denote] using hcongr.trans hden_Senc
      have target_respects_Senc_final :
          SMT.RenamingContext.RespectsTypeContextOnFV
            DeltaT StT.types Senc :=
        target_respects_Senc.of_extends
          DeltaT_ext types_sub_T typ_Senc
      mspec encodePFunTail_rep_scoped_spec
        alpha beta rho sigma hrho hsigma Senc Tenc
        typ_Senc_final typ_Tenc bv_Senc_final bv_Tenc_used
      rename_i out_pfun
      obtain ⟨PFunEnc, sigmaPFun⟩ := out_pfun
      mrename_i post_pfun
      mintro ∀StPFun
      mpure post_pfun
      obtain ⟨used_sub_PFun, types_sub_PFun, keys_sub_PFun, path_PFun,
        typ_PFunEnc, preserves_PFun, tail_total,
        tail_types_eq, tail_decl_eq, tail_obs_S, tail_obs_T,
        tail_fv_dep, tail_guard⟩ := post_pfun
      dsimp at path_PFun typ_PFunEnc tail_total tail_obs_S tail_obs_T tail_fv_dep tail_guard
      mpure_intro
      refine ⟨DltS ++ DltT, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [tail_decl_eq, T_decl_eq, S_decl_eq, St_decl_eq,
          List.append_assoc]
      · simpa [tail_types_eq] using
          DeclarationContextTrace.append S_trace T_trace
      · simpa [tail_types_eq, List.append_assoc] using T_envelope
      · intro Delta_alt Delta_fv_alt Delta0_alt related_alt wf_alt
          Delta0_alt_none respects_alt Delta0_alt_dom
          U_alt hU_alt den_t_alt
        obtain ⟨X_alt, Y_alt, hX_alt, hY_alt,
            den_S_alt, den_T_alt, rfl⟩ :=
          B.denote_pfun_inv_rep Delta_fv_alt den_t_alt
        have Delta0_alt_none_S : ∀ v ∉ StS.env.usedVars,
            Delta0_alt v = none := by
          intro v hv
          by_contra hne
          have hv_St := Delta0_alt_dom v hne
          have hv_used : v ∈ used := by
            rw [← St_used_eq]
            exact St_keys hv_St
          exact hv (used_sub_S hv_used)
        obtain ⟨DeltaS_alt, hcov_Senc_alt, denSenc_alt,
            DeltaS_alt_ext, _related_S_alt, DeltaS_alt_none,
            _respects_S_alt, target_respects_Senc_alt,
            DeltaS_alt_dom, specsS_alt, hden_Senc_alt,
            hdenSenc_alt_type, S_alt_rel⟩ :=
          S_sc_total Delta_alt
            (fun v hv => Delta_fv_alt v (fv_S_sub hv))
            Delta0_alt (related_alt.mono_fv fv_S_sub) wf_alt
            Delta0_alt_none_S (respects_alt.mono_fv fv_S_sub)
            Delta0_alt_dom X_alt hX_alt den_S_alt
        have DeltaS_alt_none_T : ∀ v ∉ StT.env.usedVars,
            DeltaS_alt v = none := by
          intro v hv
          apply DeltaS_alt_none v
          intro hvS
          exact hv (used_sub_T hvS)
        have related_alt_T : RValuationCastSupportedOnFV
            Delta_alt DeltaS_alt T :=
          (related_alt.mono_fv fv_T_sub).of_extends DeltaS_alt_ext
        have respects_alt_T : B.RenamingContext.RespectsTypeContextOnFV
            DeltaS_alt StS.types T :=
          respects_alt.of_extends DeltaS_alt_ext types_sub_S
            fv_T_sub fv_in_Lambda
        obtain ⟨DeltaT_alt, hcov_Tenc_alt, denTenc_alt,
            DeltaT_alt_ext, _related_T_alt, DeltaT_alt_none,
            _respects_T_alt, target_respects_Tenc_alt,
            DeltaT_alt_dom, specsT_alt, hden_Tenc_alt,
            hdenTenc_alt_type, T_alt_rel⟩ :=
          T_sc_total Delta_alt
            (fun v hv => Delta_fv_alt v (fv_T_sub hv))
            DeltaS_alt related_alt_T wf_alt DeltaS_alt_none_T
            respects_alt_T DeltaS_alt_dom Y_alt hY_alt den_T_alt
        have hcov_Senc_alt_final : RenamingContext.CoversFV
            DeltaT_alt Senc :=
          RenamingContext.coversFV_of_extends_of_coversFV
            DeltaT_alt_ext hcov_Senc_alt
        have hden_Senc_alt_final :
            ⟦Senc.abstract DeltaT_alt hcov_Senc_alt_final⟧ˢ =
              some denSenc_alt := by
          have hagree :=
            RenamingContext.agreesOnFV_of_extends_of_coversFV
              DeltaT_alt_ext hcov_Senc_alt
          have hcongr := RenamingContext.denote_congr_of_agreesOnFV
            (t := Senc) (h1 := hcov_Senc_alt_final)
            (h2 := hcov_Senc_alt) hagree
          simpa [RenamingContext.denote] using
            hcongr.trans hden_Senc_alt
        have target_respects_Senc_alt_final :
            SMT.RenamingContext.RespectsTypeContextOnFV
              DeltaT_alt StT.types Senc :=
          target_respects_Senc_alt.of_extends
            DeltaT_alt_ext types_sub_T typ_Senc
        obtain ⟨DeltaPFun_alt, hcov_PFunEnc_alt, denPFun_alt,
            DeltaPFun_alt_ext, DeltaPFun_alt_none,
            target_respects_PFunEnc_alt, DeltaPFun_alt_dom,
            hden_PFunEnc_alt, hdenPFun_alt_type, PFun_alt_rel⟩ :=
          tail_total DeltaT_alt hcov_Senc_alt_final hcov_Tenc_alt
            DeltaT_alt_none target_respects_Senc_alt_final
            target_respects_Tenc_alt DeltaT_alt_dom
            X_alt Y_alt hX_alt hY_alt denSenc_alt denTenc_alt
            hden_Senc_alt_final hden_Tenc_alt S_alt_rel T_alt_rel
        have DeltaT_alt_ext0 :=
          RenamingContext.extends_trans DeltaT_alt_ext DeltaS_alt_ext
        have DeltaPFun_alt_ext0 :=
          RenamingContext.extends_trans DeltaPFun_alt_ext DeltaT_alt_ext0
        have types_sub0 : St.types ⊆ StPFun.types :=
          fun _ h => types_sub_PFun (types_sub_T (types_sub_S h))
        have DeltaPFun_alt_extS :=
          RenamingContext.extends_trans DeltaPFun_alt_ext DeltaT_alt_ext
        have specsS_final : SpecBodiesTrue
            DeltaPFun_alt StPFun.types DltS :=
          specsS_alt.of_extends DeltaPFun_alt_extS
            (fun _ h => types_sub_PFun (types_sub_T h)) DeltaS_alt_dom
        have specsT_final : SpecBodiesTrue
            DeltaPFun_alt StPFun.types DltT :=
          specsT_alt.of_extends DeltaPFun_alt_ext
            types_sub_PFun DeltaT_alt_dom
        refine ⟨DeltaPFun_alt, hcov_PFunEnc_alt, denPFun_alt,
          DeltaPFun_alt_ext0,
          related_alt.of_extends DeltaPFun_alt_ext0,
          DeltaPFun_alt_none, ?_, target_respects_PFunEnc_alt,
          DeltaPFun_alt_dom, specsS_final.append specsT_final,
          hden_PFunEnc_alt, hdenPFun_alt_type, ?_⟩
        · exact respects_alt.of_extends DeltaPFun_alt_ext0 types_sub0
            (fun _ h => h) fv_in_Lambda
        · simpa only [proof_irrel_heq] using PFun_alt_rel
      · intro GammaSup GammaScope Delta_alt Delta_fv_alt Theta
          related_alt wf_alt respectsB respectsSMT specsTrue
          U_alt hU_alt den_alt hcovOut denOut hdenOut hdenOut_type
        have full_scope : ScopedContextExtends Base
            ((Dpre ++ DltS) ++ DltT) GammaSup := by
          simpa [List.append_assoc] using GammaScope
        have full_specs : SpecBodiesTrue Theta GammaSup
            ((Dpre ++ DltS) ++ DltT) := by
          simpa [List.append_assoc] using specsTrue
        have S_scope : ScopedContextExtends Base
            (Dpre ++ DltS) GammaSup := full_scope.left_of_append
        have S_specs_true : SpecBodiesTrue Theta GammaSup
            (Dpre ++ DltS) := full_specs.left_of_append
        obtain ⟨X_target, Y_target, hX_target, hY_target,
            den_S_target, den_T_target, rfl⟩ :=
          B.denote_pfun_inv_rep Delta_fv_alt den_alt
        have hcov_S_target : RenamingContext.CoversFV Theta Senc :=
          fun v hv => hcovOut v (tail_obs_S v hv)
        have hcov_T_target : RenamingContext.CoversFV Theta Tenc :=
          fun v hv => hcovOut v (tail_obs_T v hv)
        have respects_S_target :
            SMT.RenamingContext.RespectsTypeContextOnFV
              Theta GammaSup Senc := by
          intro v xi hv hlookup
          exact respectsSMT (tail_obs_S v hv) hlookup
        have respects_T_target :
            SMT.RenamingContext.RespectsTypeContextOnFV
              Theta GammaSup Tenc := by
          intro v xi hv hlookup
          exact respectsSMT (tail_obs_T v hv) hlookup
        obtain ⟨Core, core_trace, Core_sub_StT⟩ := T_envelope
        have Core_sub_sup : Core ⊆ GammaSup := by
          intro e he
          exact full_scope (core_trace.context_generated he)
        have S_scope_Core : ScopedContextExtends Base
            (Dpre ++ DltS) Core :=
          core_trace.scoped_extends.left_of_append
        have S_bv_fresh_Core : ∀ v ∈ SMT.bv Senc, v ∉ Core := by
          intro v hv hvCore
          exact SMT.Typing.bv_notMem_context typ_Senc_final v hv
            (AList.mem_of_subset Core_sub_StT hvCore)
        have T_bv_fresh_Core : ∀ v ∈ SMT.bv Tenc, v ∉ Core := by
          intro v hv hvCore
          exact SMT.Typing.bv_notMem_context typ_Tenc v hv
            (AList.mem_of_subset Core_sub_StT hvCore)
        have typ_S_Core : Core ⊢ˢ Senc : rho.fun SMTType.bool :=
          S_sc_typing.1 Core S_scope_Core S_bv_fresh_Core
        have typ_T_Core : Core ⊢ˢ Tenc : sigma.fun SMTType.bool :=
          T_sc_typing.1 Core core_trace.scoped_extends T_bv_fresh_Core
        have respects_S_Core :
            SMT.RenamingContext.RespectsTypeContextOnFV
              Theta Core Senc :=
          respects_S_target.of_super Core_sub_sup
        have respects_T_Core :
            SMT.RenamingContext.RespectsTypeContextOnFV
              Theta Core Tenc :=
          respects_T_target.of_super Core_sub_sup
        obtain ⟨denS_target, hdenS_target, hdenS_target_type⟩ :=
          SMT.RenamingContext.denote_exists_of_typing_fv
            typ_S_Core respects_S_Core hcov_S_target
        obtain ⟨denT_target, hdenT_target, hdenT_target_type⟩ :=
          SMT.RenamingContext.denote_exists_of_typing_fv
            typ_T_Core respects_T_Core hcov_T_target
        have S_target_rel := S_guard GammaSup S_scope Delta_alt
          (fun v hv => Delta_fv_alt v (fv_S_sub hv)) Theta
          (related_alt.mono_fv fv_S_sub) wf_alt
          (respectsB.mono_fv fv_S_sub) respects_S_target
          S_specs_true X_target hX_target den_S_target
          hcov_S_target denS_target hdenS_target hdenS_target_type
        have T_target_rel := T_guard GammaSup full_scope Delta_alt
          (fun v hv => Delta_fv_alt v (fv_T_sub hv)) Theta
          (related_alt.mono_fv fv_T_sub) wf_alt
          (respectsB.mono_fv fv_T_sub) respects_T_target
          full_specs Y_target hY_target den_T_target
          hcov_T_target denT_target hdenT_target hdenT_target_type
        have result_rel := tail_guard Theta hcov_S_target hcov_T_target
          X_target Y_target hX_target hY_target denS_target denT_target
          hdenS_target hdenT_target hdenS_target_type hdenT_target_type
          S_target_rel T_target_rel hcovOut denOut hdenOut hdenOut_type
        simpa only [proof_irrel_heq] using result_rel
      · intro body hbody
        rw [specBodies_append, List.mem_append] at hbody
        rcases hbody with hSbody | hTbody
        · have typ_at_T : StT.types ⊢ˢ body : SMTType.bool :=
            typing_weakening_generated types_sub_T
              T_trace.context_generated T_delta_not_used.1
              (S_specs_op body hSbody)
              (fun v hv => S_delta_ok.2 body hSbody v hv)
          simpa [tail_types_eq] using typ_at_T
        · simpa [tail_types_eq] using T_specs_op body hTbody
      · constructor
        · intro GammaSup GammaScope result_bv_fresh
          have full_scope : ScopedContextExtends Base
              ((Dpre ++ DltS) ++ DltT) GammaSup := by
            simpa [List.append_assoc] using GammaScope
          obtain ⟨Core, core_trace, Core_sub_StT⟩ := T_envelope
          have Core_sub_sup : Core ⊆ GammaSup := by
            intro e he
            exact full_scope (core_trace.context_generated he)
          have S_scope_Core : ScopedContextExtends Base
              (Dpre ++ DltS) Core :=
            core_trace.scoped_extends.left_of_append
          have S_bv_fresh_Core : ∀ v ∈ SMT.bv Senc, v ∉ Core := by
            intro v hv hvCore
            exact SMT.Typing.bv_notMem_context typ_Senc_final v hv
              (AList.mem_of_subset Core_sub_StT hvCore)
          have T_bv_fresh_Core : ∀ v ∈ SMT.bv Tenc, v ∉ Core := by
            intro v hv hvCore
            exact SMT.Typing.bv_notMem_context typ_Tenc v hv
              (AList.mem_of_subset Core_sub_StT hvCore)
          have typ_S_Core : Core ⊢ˢ Senc : rho.fun SMTType.bool :=
            S_sc_typing.1 Core S_scope_Core S_bv_fresh_Core
          have typ_T_Core : Core ⊢ˢ Tenc : sigma.fun SMTType.bool :=
            T_sc_typing.1 Core core_trace.scoped_extends T_bv_fresh_Core
          have Core_sub_StPFun : Core ⊆ StPFun.types := by
            simpa [tail_types_eq] using Core_sub_StT
          have output_fv_Core : ∀ v ∈ SMT.fv PFunEnc, v ∈ Core := by
            intro v hv
            have hv_children := tail_fv_dep hv
            rw [List.mem_append] at hv_children
            rcases hv_children with hvS | hvT
            · exact SMT.Typing.mem_context_of_mem_fv typ_S_Core hvS
            · exact SMT.Typing.mem_context_of_mem_fv typ_T_Core hvT
          have typ_PFun_Core : Core ⊢ˢ PFunEnc : sigmaPFun :=
            SMT.Typing.strengthening_of_fv_subset
              Core_sub_StPFun typ_PFunEnc output_fv_Core
          exact SMT.Typing.weakening Core_sub_sup typ_PFun_Core
            result_bv_fresh
        · simpa [List.append_assoc] using T_sc_typing.2
