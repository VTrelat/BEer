import Mathlib.Data.List.OfFn
import SMT.Reasoning.Basic.EncodeTermRepresentedBinders
import SMT.Reasoning.Basic.CollectCaseHelpers
import SMT.Reasoning.Basic.EncodeTermRepresentedMem

open B SMT ZFSet

/-!
# Representation-aware collection

The collection encoder builds an SMT lambda whose body is an `ite`: the
encoded domain predicate selects the substituted predicate body.  The lemmas
here isolate this last semantic step from the operational proof that constructs
the represented contexts.
-/

/-- Restricting a relation with separation preserves its partial-function
property.  This is the source-side invariant needed by the option-function
collection arm: filtering a represented partial function cannot introduce a
second result for an existing input. -/
theorem ZFSet.IsPFunc.sep {f A B : ZFSet} (hfun : f.IsPFunc A B)
    (p : ZFSet → Prop) :
    (f.sep p).IsPFunc A B := by
  constructor
  · intro x hx
    exact hfun.1 (ZFSet.sep_subset_self hx)
  · intro x y hxy z hxz
    exact hfun.2 x y (ZFSet.mem_sep.mp hxy).1 z
      (ZFSet.mem_sep.mp hxz).1

/- An option-function representative can only represent a source partial
function.  Its graph retracts to the source relation, and equal `some`
outputs at a canonical input force equal source codomain values. -/
open Classical in
theorem RDomCastSupported.optionFunction_isPFunc_of_source.{u}
    {alpha beta : BType} {S F : ZFSet.{u}}
    {hS : S ∈ ⟦BType.set (alpha ×ᴮ beta)⟧ᶻ}
    {hF : F ∈ ⟦SMTType.fun alpha.toSMTType
      (SMTType.option beta.toSMTType)⟧ᶻ}
    (rel : RDomCastSupported
      (⟨S, BType.set (alpha ×ᴮ beta), hS⟩ : B.Dom)
      (⟨F, SMTType.fun alpha.toSMTType
        (SMTType.option beta.toSMTType), hF⟩ : SMT.Dom)) :
    S.IsPFunc ⟦alpha⟧ᶻ ⟦beta⟧ᶻ := by
  constructor
  · rw [BType.toZFSet, ZFSet.mem_powerset] at hS
    exact hS
  · intro x y hxy z hxz
    have hxy_prod : x.pair y ∈ ⟦alpha⟧ᶻ.prod ⟦beta⟧ᶻ := by
      rw [BType.toZFSet, ZFSet.mem_powerset] at hS
      exact hS hxy
    have hxz_prod : x.pair z ∈ ⟦alpha⟧ᶻ.prod ⟦beta⟧ᶻ := by
      rw [BType.toZFSet, ZFSet.mem_powerset] at hS
      exact hS hxz
    obtain ⟨hx, hy⟩ := ZFSet.pair_mem_prod.mp hxy_prod
    obtain ⟨_, hz⟩ := ZFSet.pair_mem_prod.mp hxz_prod
    let X : SMT.Dom.{u} :=
      B.Dom.canonicalSMT (⟨x, alpha, hx⟩ : B.Dom)
    let Y : SMT.Dom.{u} :=
      B.Dom.canonicalSMT (⟨y, beta, hy⟩ : B.Dom)
    let Z : SMT.Dom.{u} :=
      B.Dom.canonicalSMT (⟨z, beta, hz⟩ : B.Dom)
    have hX : X.fst ∈ ⟦alpha.toSMTType⟧ᶻ := by
      dsimp [X]
      exact (B.Dom.canonicalSMT (⟨x, alpha, hx⟩ : B.Dom)).snd.snd
    have hY : Y.fst ∈ ⟦beta.toSMTType⟧ᶻ := by
      dsimp [Y]
      exact (B.Dom.canonicalSMT (⟨y, beta, hy⟩ : B.Dom)).snd.snd
    have hZ : Z.fst ∈ ⟦beta.toSMTType⟧ᶻ := by
      dsimp [Z]
      exact (B.Dom.canonicalSMT (⟨z, beta, hz⟩ : B.Dom)).snd.snd
    have hXret : retract alpha X.fst = x := by
      have hcanonical := B.Dom.rdom_canonicalSMT
        (⟨x, alpha, hx⟩ : B.Dom)
      rw [RDom] at hcanonical
      simpa [X] using hcanonical.2
    have hYret : retract beta Y.fst = y := by
      have hcanonical := B.Dom.rdom_canonicalSMT
        (⟨y, beta, hy⟩ : B.Dom)
      rw [RDom] at hcanonical
      simpa [Y] using hcanonical.2
    have hZret : retract beta Z.fst = z := by
      have hcanonical := B.Dom.rdom_canonicalSMT
        (⟨z, beta, hz⟩ : B.Dom)
      rw [RDom] at hcanonical
      simpa [Z] using hcanonical.2
    have hgraph_ret : retract (BType.set (alpha ×ᴮ beta))
        (optionGraph alpha.toSMTType beta.toSMTType F) = S :=
      RDomCast.optionFunction_graph_retract rel.toRDomCast
    have hpair_ret_y : retract (alpha ×ᴮ beta) (X.fst.pair Y.fst) =
        x.pair y := by
      simp [retract, hXret, hYret]
    have hpair_ret_z : retract (alpha ×ᴮ beta) (X.fst.pair Z.fst) =
        x.pair z := by
      simp [retract, hXret, hZret]
    let Fapp := fapply F (is_func_is_pfunc (by
      simpa [SMTType.toZFSet] using hF :
        ⟦alpha.toSMTType⟧ᶻ.IsFunc
          ⟦SMTType.option beta.toSMTType⟧ᶻ F))
      ⟨X.fst, by
        rw [is_func_dom_eq (by
          simpa [SMTType.toZFSet] using hF :
            ⟦alpha.toSMTType⟧ᶻ.IsFunc
              ⟦SMTType.option beta.toSMTType⟧ᶻ F)]
        exact hX⟩
    let someY := ZFSet.Option.some
      (S := ⟦beta.toSMTType⟧ᶻ) ⟨Y.fst, hY⟩
    let someZ := ZFSet.Option.some
      (S := ⟦beta.toSMTType⟧ᶻ) ⟨Z.fst, hZ⟩
    have happY : zfEqIn ⟦SMTType.option beta.toSMTType⟧ᶻ
        Fapp.val someY.val = ZFSet.zftrue := by
      exact (RDomCast.optionFunction_eq_some_eq_zftrue_iff
        (hX := ZFSet.pair_mem_prod.mpr ⟨hx, hy⟩)
        (ha := hX) (hb := hY) (hF := hF)
        hpair_ret_y hgraph_ret).mpr hxy
    have happZ : zfEqIn ⟦SMTType.option beta.toSMTType⟧ᶻ
        Fapp.val someZ.val = ZFSet.zftrue := by
      exact (RDomCast.optionFunction_eq_some_eq_zftrue_iff
        (hX := ZFSet.pair_mem_prod.mpr ⟨hx, hz⟩)
        (ha := hX) (hb := hZ) (hF := hF)
        hpair_ret_z hgraph_ret).mpr hxz
    have hFappY : Fapp.val = someY.val :=
      (zfEqIn_eq_zftrue_iff (ZFSet.fapply_mem_range _ _) someY.property).mp
        happY
    have hFappZ : Fapp.val = someZ.val :=
      (zfEqIn_eq_zftrue_iff (ZFSet.fapply_mem_range _ _) someZ.property).mp
        happZ
    have hsome : someY = someZ :=
      Subtype.ext (hFappY.symm.trans hFappZ)
    rw [ZFSet.Option.some.injEq] at hsome
    have hYZ : Y.fst = Z.fst := Subtype.ext_iff.mp hsome
    calc
      y = retract beta Y.fst := hYret.symm
      _ = retract beta Z.fst := by rw [hYZ]
      _ = z := hZret

/- A pointwise characteristic-graph specification is sufficient to package an
option-valued function as a supported representative of a source relation.
This is the final semantic interface needed by the function-domain collection
arm: the operational proof only has to establish the truth condition at the
canonical image of each source pair. -/
open Classical in
theorem RDomCastSupported.optionFunction_of_graph_truth.{u}
    {alpha beta : BType} {S F : ZFSet.{u}}
    {hS : S ∈ ⟦BType.set (alpha ×ᴮ beta)⟧ᶻ}
    {hF : F ∈ ⟦SMTType.fun alpha.toSMTType
      (SMTType.option beta.toSMTType)⟧ᶻ}
    (htruth : ∀ (x : ZFSet.{u}) (hx : x ∈ ⟦alpha ×ᴮ beta⟧ᶻ),
      let X : SMT.Dom.{u} :=
        B.Dom.canonicalSMT (⟨x, alpha ×ᴮ beta, hx⟩ : B.Dom)
      let G := optionGraph alpha.toSMTType beta.toSMTType F
      let hGfunc :
          ⟦SMTType.pair alpha.toSMTType beta.toSMTType⟧ᶻ.IsFunc
            ZFSet.𝔹 G := by
        simpa [SMTType.toZFSet] using
          (optionGraph_mem alpha.toSMTType beta.toSMTType hF)
      (ZFSet.fapply G (ZFSet.is_func_is_pfunc hGfunc)
        ⟨X.fst, by
          rw [ZFSet.is_func_dom_eq hGfunc]
          dsimp [X]
          exact (B.Dom.canonicalSMT
            (⟨x, alpha ×ᴮ beta, hx⟩ : B.Dom)).snd.snd⟩).val =
          ZFSet.zftrue ↔ x ∈ S) :
    RDomCastSupported
      (⟨S, BType.set (alpha ×ᴮ beta), hS⟩ : B.Dom)
      (⟨F, SMTType.fun alpha.toSMTType
        (SMTType.option beta.toSMTType), hF⟩ : SMT.Dom) := by
  refine ⟨?_, BType.SupportedSMT.optionFun alpha beta⟩
  apply RDomCast.toRDomCastAdmissible_of_supported
  · refine ⟨castPath.graph (castPath.reflexive alpha.toSMTType)
      (castPath.reflexive beta.toSMTType), ?_⟩
    change retract (BType.set (alpha ×ᴮ beta))
      (optionGraph alpha.toSMTType beta.toSMTType F) = S
    let G := optionGraph alpha.toSMTType beta.toSMTType F
    have hG : G ∈ ⟦SMTType.fun
        (SMTType.pair alpha.toSMTType beta.toSMTType) SMTType.bool⟧ᶻ :=
      optionGraph_mem alpha.toSMTType beta.toSMTType hF
    have hGfunc : ⟦SMTType.pair alpha.toSMTType beta.toSMTType⟧ᶻ.IsFunc
        ZFSet.𝔹 G := by
      simpa [SMTType.toZFSet] using hG
    have hGfunc' : ⟦(alpha ×ᴮ beta).toSMTType⟧ᶻ.IsFunc
        ZFSet.𝔹 G := by
      simpa using hGfunc
    apply ZFSet.ext
    intro x
    rw [retract, ZFSet.mem_sep]
    constructor
    · rintro ⟨hx, hpred⟩
      rw [dif_pos hx, dif_pos hGfunc'] at hpred
      let X : SMT.Dom.{u} :=
        B.Dom.canonicalSMT (⟨x, alpha ×ᴮ beta, hx⟩ : B.Dom)
      have hXdom : X.fst ∈ G.Dom (ZFSet.is_rel_of_is_func hGfunc) := by
        rw [ZFSet.is_func_dom_eq hGfunc]
        dsimp [X]
        exact (B.Dom.canonicalSMT
          (⟨x, alpha ×ᴮ beta, hx⟩ : B.Dom)).snd.snd
      have htruth' := htruth x hx
      change (ZFSet.fapply G (ZFSet.is_func_is_pfunc hGfunc)
        ⟨X.fst, hXdom⟩).val = ZFSet.zftrue ↔ x ∈ S at htruth'
      apply htruth'.mp
      simpa [G, X] using hpred
    · intro hxS
      refine ⟨?_, ?_⟩
      · rw [BType.toZFSet, ZFSet.mem_powerset] at hS
        exact hS hxS
      · have hx : x ∈ ⟦alpha ×ᴮ beta⟧ᶻ := by
          rw [BType.toZFSet, ZFSet.mem_powerset] at hS
          exact hS hxS
        rw [dif_pos hx, dif_pos hGfunc']
        let X : SMT.Dom.{u} :=
          B.Dom.canonicalSMT (⟨x, alpha ×ᴮ beta, hx⟩ : B.Dom)
        have hXdom : X.fst ∈ G.Dom (ZFSet.is_rel_of_is_func hGfunc) := by
          rw [ZFSet.is_func_dom_eq hGfunc]
          dsimp [X]
          exact (B.Dom.canonicalSMT
            (⟨x, alpha ×ᴮ beta, hx⟩ : B.Dom)).snd.snd
        have htruth' := htruth x hx
        change (ZFSet.fapply G (ZFSet.is_func_is_pfunc hGfunc)
          ⟨X.fst, hXdom⟩).val = ZFSet.zftrue ↔ x ∈ S at htruth'
        simpa [G, X] using htruth'.mpr hxS
  · exact BType.SupportedSMT.optionFun alpha beta

/-- At a pair of canonical target values, the characteristic graph of an
option-valued function is true exactly when the function returns that `some`
value.  This is the target-only half of the option-collection bridge. -/
theorem optionGraph_apply_eq_zftrue_iff.{u}
    (alpha beta : SMTType) {F x y : ZFSet.{u}}
    (hF : F ∈ ⟦SMTType.fun alpha (SMTType.option beta)⟧ᶻ)
    (hx : x ∈ ⟦alpha⟧ᶻ) (hy : y ∈ ⟦beta⟧ᶻ) :
    let G := optionGraph alpha beta F
    let Gapp := ZFSet.fapply G (ZFSet.is_func_is_pfunc (by
      simpa [SMTType.toZFSet] using
        (optionGraph_mem alpha beta hF) :
          ⟦SMTType.pair alpha beta⟧ᶻ.IsFunc ZFSet.𝔹 G))
      ⟨x.pair y, by
        rw [ZFSet.is_func_dom_eq (by
          simpa [SMTType.toZFSet] using
            (optionGraph_mem alpha beta hF) :
              ⟦SMTType.pair alpha beta⟧ᶻ.IsFunc ZFSet.𝔹 G)]
        exact ZFSet.pair_mem_prod.mpr ⟨hx, hy⟩⟩
    let Fapp := ZFSet.fapply F (ZFSet.is_func_is_pfunc (by
      simpa [SMTType.toZFSet] using hF :
        ⟦alpha⟧ᶻ.IsFunc ⟦SMTType.option beta⟧ᶻ F))
      ⟨x, by
        rw [ZFSet.is_func_dom_eq (by
          simpa [SMTType.toZFSet] using hF :
            ⟦alpha⟧ᶻ.IsFunc ⟦SMTType.option beta⟧ᶻ F)]
        exact hx⟩
    let someY := ZFSet.Option.some (S := ⟦beta⟧ᶻ) ⟨y, hy⟩
    Gapp.val = ZFSet.zftrue ↔ Fapp.val = someY.val := by
  dsimp only
  let G := optionGraph alpha beta F
  have hG : G ∈ ⟦SMTType.fun (SMTType.pair alpha beta) SMTType.bool⟧ᶻ :=
    optionGraph_mem alpha beta hF
  have hGfunc : ⟦SMTType.pair alpha beta⟧ᶻ.IsFunc ZFSet.𝔹 G := by
    simpa [SMTType.toZFSet] using hG
  have hFfunc : ⟦alpha⟧ᶻ.IsFunc ⟦SMTType.option beta⟧ᶻ F := by
    simpa [SMTType.toZFSet] using hF
  have hxy_prod : x.pair y ∈ ⟦alpha⟧ᶻ.prod ⟦beta⟧ᶻ :=
    ZFSet.pair_mem_prod.mpr ⟨hx, hy⟩
  have hxy_dom : x.pair y ∈ G.Dom (ZFSet.is_rel_of_is_func hGfunc) := by
    rw [ZFSet.is_func_dom_eq hGfunc]
    exact hxy_prod
  have hpair_graph :
      (ZFSet.fapply G (ZFSet.is_func_is_pfunc hGfunc)
        ⟨x.pair y, hxy_dom⟩).val = ZFSet.zftrue ↔
        x.pair y ∈ predGraph alpha beta G := by
    unfold predGraph
    rw [ZFSet.mem_sep, ZFSet.pair_mem_prod]
    simp only [hx, hy, and_self, true_and]
    constructor
    · intro happ
      rw [← happ]
      exact ZFSet.fapply.def (ZFSet.is_func_is_pfunc hGfunc) _
    · intro hmem
      exact Subtype.ext_iff.mp
        (ZFSet.fapply.of_pair (ZFSet.is_func_is_pfunc hGfunc) hmem)
  have hgraph_mem : x.pair y ∈ predGraph alpha beta G ↔
      x.pair (ZFSet.Option.some (S := ⟦beta⟧ᶻ) ⟨y, hy⟩).val ∈ F := by
    exact mem_predGraph_optionGraph_iff alpha beta F hF x y hx hy
  have hpair_app :
      x.pair (ZFSet.Option.some (S := ⟦beta⟧ᶻ) ⟨y, hy⟩).val ∈ F ↔
        (ZFSet.fapply F (ZFSet.is_func_is_pfunc hFfunc)
          ⟨x, by
            rw [ZFSet.is_func_dom_eq hFfunc]
            exact hx⟩).val =
          (ZFSet.Option.some (S := ⟦beta⟧ᶻ) ⟨y, hy⟩).val := by
    constructor
    · intro hpair
      exact Subtype.ext_iff.mp
        (ZFSet.fapply.of_pair (ZFSet.is_func_is_pfunc hFfunc) hpair)
    · intro happ
      rw [← happ]
      exact ZFSet.fapply.def (ZFSet.is_func_is_pfunc hFfunc) _
  exact hpair_graph.trans (hgraph_mem.trans hpair_app)

/- Unfold a successful source collection denotation into the separation
equation used by the SMT-lambda retraction proof.  Keeping this source-only
fact independent of the target representation lets the main and alternative
valuation arguments share it. -/
open Classical in
theorem B.denote_collect_eq_sep.{u}
    {vs : List B.𝒱} {D P : B.Term} {tau : BType}
    {Xi : B.RenamingContext.Context.{u}}
    (Xi_fv : ∀ v ∈ B.fv (B.Term.collect vs D P), (Xi v).isSome = true)
    (tau_hasArity : tau.hasArity vs.length)
    {Dval : ZFSet.{u}} {hDval : Dval ∈ ⟦BType.set tau⟧ᶻ}
    (den_D : ⟦D.abstract Xi
      (fun v hv => Xi_fv v (B.fv.mem_collect (.inl hv)))⟧ᴮ =
      some (⟨Dval, BType.set tau, hDval⟩ : B.Dom))
    {T : ZFSet.{u}} {hT : T ∈ ⟦BType.set tau⟧ᶻ}
    (den_collect : ⟦(B.Term.collect vs D P).abstract Xi Xi_fv⟧ᴮ =
      some (⟨T, BType.set tau, hT⟩ : B.Dom)) :
    ZFSet.sep (fun x =>
      if hx : x.hasArity vs.length ∧ tau.hasArity vs.length ∧ x ∈ ⟦tau⟧ᶻ then
        match ⟦(B.Term.abstract.go P vs Xi (fun v hv hvs => Xi_fv v
          (B.fv.mem_collect (.inr ⟨hv, hvs⟩)))).uncurry
          (fun i => ⟨x.get vs.length i, ⟨tau.get vs.length i,
            get_mem_type_of_isTuple hx.1 hx.2.1 hx.2.2⟩⟩)⟧ᴮ with
        | some ⟨Pz, _⟩ => Pz = ZFSet.zftrue
        | none => False
      else False) Dval = T := by
  have h_inv := den_collect
  simp only [B.Term.abstract] at h_inv
  unfold B.denote at h_inv
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h_inv
  obtain ⟨D_dom, hden_d, rest⟩ := h_inv
  have hconv_d : ⟦D.abstract Xi
      (fun v hv => Xi_fv v (B.fv.mem_collect (.inl hv)))⟧ᴮ =
      some D_dom := by
    convert hden_d using 2
  have hD_dom_eq : D_dom =
      (⟨Dval, BType.set tau, hDval⟩ : B.Dom) := by
    rw [hconv_d] at den_D
    exact Option.some.inj den_D
  subst D_dom
  simp only at rest
  split at rest
  · simp only [Option.bind_eq_some_iff] at rest
    obtain ⟨_, denP_eq, rest2⟩ := rest
    split_ifs at rest2 with h_den_P_cond h_typP_det_cond
    · simp only [Option.pure_def, Option.some.injEq, PSigma.mk.injEq] at rest2
      rw [← rest2.1]
      congr 1
      funext x
      simp
      constructor
      · rintro ⟨hx, match_eq⟩
        exact ⟨hx, by
          split at match_eq
          · rename_i h
            erw [h]
            exact match_eq
          · nomatch match_eq⟩
      · rintro ⟨hx, match_eq⟩
        exact ⟨hx, by
          split at match_eq
          · rename_i h
            erw [h]
            exact match_eq
          · nomatch match_eq⟩
  · rename_i h_neg
    exact absurd
      ⟨BType.hasArity_of_foldl_defaultZFSet tau_hasArity, tau_hasArity⟩
      h_neg

open Classical in
/-- At a tuple with the collection's expected arity and type, source
collection membership is exactly domain membership together with truth of the
instantiated source predicate.  This is the source-side counterpart of the
guarded option body emitted for a function-valued collection. -/
theorem B.denote_collect_member_iff.{u}
    {vs : List B.𝒱} {D P : B.Term} {tau : BType}
    {Xi : B.RenamingContext.Context.{u}}
    (Xi_fv : ∀ v ∈ B.fv (B.Term.collect vs D P), (Xi v).isSome = true)
    (tau_hasArity : tau.hasArity vs.length)
    {Dval : ZFSet.{u}} {hDval : Dval ∈ ⟦BType.set tau⟧ᶻ}
    (den_D : ⟦D.abstract Xi
      (fun v hv => Xi_fv v (B.fv.mem_collect (.inl hv)))⟧ᴮ =
      some (⟨Dval, BType.set tau, hDval⟩ : B.Dom))
    {T : ZFSet.{u}} {hT : T ∈ ⟦BType.set tau⟧ᶻ}
    (den_collect : ⟦(B.Term.collect vs D P).abstract Xi Xi_fv⟧ᴮ =
      some (⟨T, BType.set tau, hT⟩ : B.Dom))
    {x : ZFSet.{u}}
    (hx_arity : x.hasArity vs.length)
    (hx_type : x ∈ ⟦tau⟧ᶻ)
    {Pval : ZFSet.{u}} {hPval : Pval ∈ ⟦BType.bool⟧ᶻ}
    (den_P : ⟦(B.Term.abstract.go P vs Xi (fun v hv hvs => Xi_fv v
      (B.fv.mem_collect (.inr ⟨hv, hvs⟩)))).uncurry
        (fun i => ⟨x.get vs.length i, ⟨tau.get vs.length i,
          get_mem_type_of_isTuple hx_arity tau_hasArity hx_type⟩⟩)⟧ᴮ =
      some (⟨Pval, BType.bool, hPval⟩ : B.Dom)) :
    x ∈ T ↔ x ∈ Dval ∧ Pval = ZFSet.zftrue := by
  rw [← B.denote_collect_eq_sep Xi_fv tau_hasArity den_D den_collect,
    ZFSet.mem_sep, dif_pos ⟨hx_arity, tau_hasArity, hx_type⟩]
  simp [den_P]

/- A source collection is a subrelation of its domain.  In particular, when
the domain is a partial function, the collection result remains a partial
function.  This supplies the functionality certificate required when the
encoder keeps that relation in its option-function representation. -/
open Classical in
theorem B.denote_collect_isPFunc_of_domain.{u}
    {vs : List B.𝒱} {D P : B.Term} {alpha beta : BType}
    {Xi : B.RenamingContext.Context.{u}}
    (Xi_fv : ∀ v ∈ B.fv (B.Term.collect vs D P), (Xi v).isSome = true)
    (tau_hasArity : (alpha ×ᴮ beta).hasArity vs.length)
    {Dval : ZFSet.{u}}
    {hDval : Dval ∈ ⟦BType.set (alpha ×ᴮ beta)⟧ᶻ}
    (den_D : ⟦D.abstract Xi
      (fun v hv => Xi_fv v (B.fv.mem_collect (.inl hv)))⟧ᴮ =
      some (⟨Dval, BType.set (alpha ×ᴮ beta), hDval⟩ : B.Dom))
    {T : ZFSet.{u}} {hT : T ∈ ⟦BType.set (alpha ×ᴮ beta)⟧ᶻ}
    (den_collect : ⟦(B.Term.collect vs D P).abstract Xi Xi_fv⟧ᴮ =
      some (⟨T, BType.set (alpha ×ᴮ beta), hT⟩ : B.Dom))
    (hfun : Dval.IsPFunc ⟦alpha⟧ᶻ ⟦beta⟧ᶻ) :
    T.IsPFunc ⟦alpha⟧ᶻ ⟦beta⟧ᶻ := by
  rw [← B.denote_collect_eq_sep Xi_fv tau_hasArity den_D den_collect]
  exact hfun.sep _

/- A successful source collection denotation also supplies the totality of
its predicate at every tuple selected from its source domain.  This is the
second source-side ingredient of the lambda retraction argument, alongside
`B.denote_collect_eq_sep`. -/
open Classical in
theorem B.denote_collect_predicate_total.{u}
    {vs : List B.𝒱} {D P : B.Term} {tau : BType}
    {Xi : B.RenamingContext.Context.{u}}
    (Xi_fv : ∀ v ∈ B.fv (B.Term.collect vs D P), (Xi v).isSome = true)
    (tau_hasArity : tau.hasArity vs.length)
    {Dval : ZFSet.{u}} {hDval : Dval ∈ ⟦BType.set tau⟧ᶻ}
    (den_D : ⟦D.abstract Xi
      (fun v hv => Xi_fv v (B.fv.mem_collect (.inl hv)))⟧ᴮ =
      some (⟨Dval, BType.set tau, hDval⟩ : B.Dom))
    {T : ZFSet.{u}} {hT : T ∈ ⟦BType.set tau⟧ᶻ}
    (den_collect : ⟦(B.Term.collect vs D P).abstract Xi Xi_fv⟧ᴮ =
      some (⟨T, BType.set tau, hT⟩ : B.Dom)) :
    ∀ {x_fin : Fin vs.length → B.Dom.{u}},
      (∀ i, (x_fin i).snd.fst = tau.get vs.length i ∧
        (x_fin i).fst ∈ ⟦tau.get vs.length i⟧ᶻ) →
      ZFSet.ofFinDom x_fin ∈ Dval →
      ⟦(B.Term.abstract.go P vs Xi (fun v hv hvs => Xi_fv v
        (B.fv.mem_collect (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ.isSome = true := by
  intro x_fin hx_typ hx_mem
  have h_inv := den_collect
  simp only [B.Term.abstract] at h_inv
  unfold B.denote at h_inv
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h_inv
  obtain ⟨D_dom, hden_d, rest⟩ := h_inv
  have hconv_d : ⟦D.abstract Xi
      (fun v hv => Xi_fv v (B.fv.mem_collect (.inl hv)))⟧ᴮ =
      some D_dom := by
    convert hden_d using 2
  have hD_dom_eq : D_dom =
      (⟨Dval, BType.set tau, hDval⟩ : B.Dom) := by
    rw [hconv_d] at den_D
    exact Option.some.inj den_D
  subst D_dom
  simp only at rest
  split at rest
  · simp only [Option.bind_eq_some_iff] at rest
    obtain ⟨_, _, rest2⟩ := rest
    split_ifs at rest2 with h_den_P_cond
    exact h_den_P_cond hx_typ hx_mem
  · rename_i h_neg
    exact absurd
      ⟨BType.hasArity_of_foldl_defaultZFSet tau_hasArity, tau_hasArity⟩
      h_neg

/- Repackage the source predicate-totality condition as the Boolean
denotation needed by the representation-aware body induction hypothesis. -/
open Classical in
theorem B.denote_collect_predicate_exists.{u}
    {vs : List B.𝒱} {D P : B.Term} {tau : BType}
    {Xi : B.RenamingContext.Context.{u}}
    (Xi_fv : ∀ v ∈ B.fv (B.Term.collect vs D P), (Xi v).isSome = true)
    (vs_nemp : vs ≠ []) (vs_nodup : vs.Nodup)
    (tau_hasArity : tau.hasArity vs.length)
    {Dval : ZFSet.{u}} {hDval : Dval ∈ ⟦BType.set tau⟧ᶻ}
    (den_D : ⟦D.abstract Xi
      (fun v hv => Xi_fv v (B.fv.mem_collect (.inl hv)))⟧ᴮ =
      some (⟨Dval, BType.set tau, hDval⟩ : B.Dom))
    {T : ZFSet.{u}} {hT : T ∈ ⟦BType.set tau⟧ᶻ}
    (den_collect : ⟦(B.Term.collect vs D P).abstract Xi Xi_fv⟧ᴮ =
      some (⟨T, BType.set tau, hT⟩ : B.Dom))
    {Ectx : B.TypeContext} (typ_P : Ectx ⊢ᴮ P : BType.bool) :
    ∀ {x_fin : Fin vs.length → B.Dom.{u}},
      (∀ i, (x_fin i).snd.fst = tau.get vs.length i ∧
        (x_fin i).fst ∈ ⟦tau.get vs.length i⟧ᶻ) →
      ZFSet.ofFinDom x_fin ∈ Dval →
      B.RenWF Ectx (Function.updates Xi vs
        (List.ofFn fun i => some (x_fin i))) →
      ∃ (XiP_fv : ∀ v ∈ B.fv P,
          (Function.updates Xi vs
            (List.ofFn fun i => some (x_fin i)) v).isSome = true)
        (Pval : ZFSet.{u}) (hPval : Pval ∈ ⟦BType.bool⟧ᶻ),
        ⟦P.abstract (Function.updates Xi vs
          (List.ofFn fun i => some (x_fin i))) XiP_fv⟧ᴮ =
          some (⟨Pval, BType.bool, hPval⟩ : B.Dom) := by
  intro x_fin hx_typ hx_mem wf_P
  have XiP_fv : ∀ v ∈ B.fv P,
      (Function.updates Xi vs (List.ofFn fun i => some (x_fin i)) v).isSome =
        true := by
    intro v hv
    rw [Function.updates_eq_if (by simp) vs_nodup]
    split_ifs with hvs
    · simp
    · exact Xi_fv v (B.fv.mem_collect (.inr ⟨hv, hvs⟩))
  have hgo_some := B.denote_collect_predicate_total Xi_fv tau_hasArity
    den_D den_collect hx_typ hx_mem
  obtain ⟨⟨Pval, P_ty, hPval⟩, hgo⟩ :=
    Option.isSome_iff_exists.mp hgo_some
  have hden : ⟦P.abstract (Function.updates Xi vs
      (List.ofFn fun i => some (x_fin i))) XiP_fv⟧ᴮ =
      some (⟨Pval, P_ty, hPval⟩ : B.Dom) := by
    rw [← denote_term_abstract_go_eq_term_abstract vs_nodup vs_nemp x_fin
      XiP_fv]
    exact hgo
  have hP_ty : P_ty = BType.bool :=
    (denote_welltyped_eq
      (t := P.abstract (Function.updates Xi vs
        (List.ofFn fun i => some (x_fin i))) XiP_fv)
      ⟨_, WFTC.of_abstract, BType.bool,
        by convert Typing.of_abstract XiP_fv typ_P⟩ hden).symm
  subst P_ty
  exact ⟨XiP_fv, Pval, hPval, hden⟩

/- The source collection semantics evaluates its predicate once at the
canonical default tuple before it can construct the resulting separation.
That evaluation is the seed needed to run the body induction hypothesis for
the outer encoded lambda, even when the source domain is empty. -/
open Classical in
theorem B.denote_collect_default_predicate_exists.{u}
    {vs : List B.𝒱} {D P : B.Term} {tau : BType}
    {Xi : B.RenamingContext.Context.{u}}
    (Xi_fv : ∀ v ∈ B.fv (B.Term.collect vs D P), (Xi v).isSome = true)
    (vs_nemp : vs ≠ []) (vs_nodup : vs.Nodup)
    (tau_hasArity : tau.hasArity vs.length)
    {Dval : ZFSet.{u}} {hDval : Dval ∈ ⟦BType.set tau⟧ᶻ}
    (den_D : ⟦D.abstract Xi
      (fun v hv => Xi_fv v (B.fv.mem_collect (.inl hv)))⟧ᴮ =
      some (⟨Dval, BType.set tau, hDval⟩ : B.Dom))
    {T : ZFSet.{u}} {hT : T ∈ ⟦BType.set tau⟧ᶻ}
    (den_collect : ⟦(B.Term.collect vs D P).abstract Xi Xi_fv⟧ᴮ =
      some (⟨T, BType.set tau, hT⟩ : B.Dom))
    {Ectx : B.TypeContext} (typ_P : Ectx ⊢ᴮ P : BType.bool)
    (wf_P : B.RenWF Ectx
      (Function.updates Xi vs (List.ofFn fun i => some
        (⟨tau.defaultZFSet.get vs.length i, tau.get vs.length i,
          get_mem_type_of_isTuple
            (BType.hasArity_of_foldl_defaultZFSet tau_hasArity)
            tau_hasArity BType.mem_toZFSet_of_defaultZFSet⟩ : B.Dom)))) :
    let x_fin : Fin vs.length → B.Dom.{u} := fun i =>
      ⟨tau.defaultZFSet.get vs.length i, tau.get vs.length i,
        get_mem_type_of_isTuple
          (BType.hasArity_of_foldl_defaultZFSet tau_hasArity)
          tau_hasArity BType.mem_toZFSet_of_defaultZFSet⟩
    ∃ (XiP_fv : ∀ v ∈ B.fv P,
        (Function.updates Xi vs
          (List.ofFn fun i => some (x_fin i)) v).isSome = true)
      (Pval : ZFSet.{u}) (hPval : Pval ∈ ⟦BType.bool⟧ᶻ),
      ⟦P.abstract (Function.updates Xi vs
        (List.ofFn fun i => some (x_fin i))) XiP_fv⟧ᴮ =
        some (⟨Pval, BType.bool, hPval⟩ : B.Dom) := by
  dsimp only
  let x_fin : Fin vs.length → B.Dom := fun i =>
    ⟨tau.defaultZFSet.get vs.length i, tau.get vs.length i,
      get_mem_type_of_isTuple
        (BType.hasArity_of_foldl_defaultZFSet tau_hasArity)
        tau_hasArity BType.mem_toZFSet_of_defaultZFSet⟩
  have XiP_fv : ∀ v ∈ B.fv P,
      (Function.updates Xi vs (List.ofFn fun i => some (x_fin i)) v).isSome =
        true := by
    intro v hv
    rw [Function.updates_eq_if (by simp) vs_nodup]
    split_ifs with hvs
    · simp
    · exact Xi_fv v (B.fv.mem_collect (.inr ⟨hv, hvs⟩))
  have h_inv := den_collect
  simp only [B.Term.abstract] at h_inv
  unfold B.denote at h_inv
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h_inv
  obtain ⟨D_dom, hden_d, rest⟩ := h_inv
  have hconv_d : ⟦D.abstract Xi
      (fun v hv => Xi_fv v (B.fv.mem_collect (.inl hv)))⟧ᴮ =
      some D_dom := by
    convert hden_d using 2
  have hD_dom_eq : D_dom =
      (⟨Dval, BType.set tau, hDval⟩ : B.Dom) := by
    rw [hconv_d] at den_D
    exact Option.some.inj den_D
  subst D_dom
  simp only at rest
  have hdefault_arity : tau.defaultZFSet.hasArity vs.length ∧
      tau.hasArity vs.length :=
    ⟨BType.hasArity_of_foldl_defaultZFSet tau_hasArity, tau_hasArity⟩
  rw [dif_pos hdefault_arity, Option.bind_eq_some_iff] at rest
  obtain ⟨⟨Pval, P_ty, hPval⟩, hgo, _⟩ := rest
  have hden : ⟦P.abstract (Function.updates Xi vs
      (List.ofFn fun i => some (x_fin i))) XiP_fv⟧ᴮ =
      some (⟨Pval, P_ty, hPval⟩ : B.Dom) := by
    rw [← denote_term_abstract_go_eq_term_abstract vs_nodup vs_nemp x_fin
      XiP_fv]
    exact hgo
  have hP_ty : P_ty = BType.bool :=
    (denote_welltyped_eq
      (t := P.abstract (Function.updates Xi vs
        (List.ofFn fun i => some (x_fin i))) XiP_fv)
      ⟨_, WFTC.of_abstract, BType.bool,
        by convert Typing.of_abstract XiP_fv typ_P⟩ hden).symm
  subst P_ty
  exact ⟨XiP_fv, Pval, hPval, hden⟩

open Classical in
/-- The default tuple used by source collection semantics can seed the body
encoder under any ambient represented valuation.  Each bound source component
is installed together with its canonical SMT representative, while every free
variable outside the binder remains related through `ambient`. -/
theorem RValuationCastSupportedOnFV.updates_of_collect_default.{u}
    {vs : List B.𝒱} (vs_nodup : vs.Nodup)
    {tau : BType} (tau_hasArity : tau.hasArity vs.length)
    {Xi : B.RenamingContext.Context.{u}}
    {Theta : SMT.RenamingContext.Context.{u}}
    {P : B.Term}
    (ambient : ∀ v ∈ B.fv P, v ∉ vs →
      match Xi v, Theta v with
      | some d, some d' => RDomCastSupported d d'
      | _, _ => False) :
    let bs : Fin vs.length → B.Dom.{u} := fun i =>
      ⟨tau.defaultZFSet.get vs.length i, tau.get vs.length i,
        get_mem_type_of_isTuple
          (BType.hasArity_of_foldl_defaultZFSet tau_hasArity)
          tau_hasArity BType.mem_toZFSet_of_defaultZFSet⟩
    RValuationCastSupportedOnFV
      (Function.updates Xi vs (List.ofFn fun i => some (bs i)))
      (Function.updates Theta vs
        (List.ofFn fun i => some (bs i).canonicalSMT)) P := by
  dsimp only
  apply RValuationCastSupportedOnFV.updates vs_nodup
  · exact ambient
  · intro i
    exact B.Dom.rdomCastSupported_canonicalSMT _

/-- The projections introduced by the set-valued collection encoder preserve
the representation relation componentwise.  This packages the dependent
tuple bookkeeping needed when the predicate totality theorem is run under a
particular collection element. -/
theorem toDestPair_denote_represented_components.{u}
    {vs : List B.𝒱} (vs_nemp : vs ≠ [])
    {tau : BType} (tau_hasArity : tau.hasArity vs.length)
    {x : ZFSet.{u}} (hx_mem : x ∈ ⟦tau⟧ᶻ)
    {z : SMT.𝒱} {Delta : SMT.RenamingContext.Context.{u}}
    {Wx : SMT.Dom.{u}}
    (hcov_z : SMT.RenamingContext.CoversFV Delta (.var z))
    (hden_z : ⟦(SMT.Term.var z).abstract Delta hcov_z⟧ˢ = some Wx)
    (hWx_type : Wx.snd.fst = tau.toSMTType)
    (hWx_mem : Wx.fst ∈ ⟦tau.toSMTType⟧ᶻ)
    (hWx_retract : retract tau Wx.fst = x) :
    ∀ (i : ℕ) (hi_vs : i < vs.length)
      (hi_pair : i < (toDestPair vs (.var z)).length),
      ∃ (hcov : SMT.RenamingContext.CoversFV Delta
          ((toDestPair vs (.var z))[i]'hi_pair))
        (Di : SMT.Dom.{u}),
        ⟦((toDestPair vs (.var z))[i]'hi_pair).abstract Delta hcov⟧ˢ =
          some Di ∧
        RDomCastSupported
          (⟨x.get vs.length ⟨i, hi_vs⟩,
            tau.get vs.length ⟨i, hi_vs⟩,
            get_mem_type_of_isTuple
              (hasArity_of_mem_toZFSet tau_hasArity hx_mem)
              tau_hasArity hx_mem⟩ : B.Dom)
          Di := by
  intro i hi_vs hi_pair
  obtain ⟨hcov_i, Di, hden_i, hfst_i, htype_i⟩ :=
    toDestPair_denote_gen tau vs (.var z) Wx Delta [] [] vs_nemp
      hcov_z hden_z hWx_type hWx_mem tau_hasArity rfl (by simp)
      i hi_vs hi_pair
  refine ⟨hcov_i, Di, hden_i, ?_⟩
  apply RDom.toRDomCastSupported
  rw [RDom]
  refine ⟨htype_i, ?_⟩
  calc
    retract (tau.get vs.length ⟨i, hi_vs⟩) Di.fst =
        retract (tau.get vs.length ⟨i, hi_vs⟩)
          (Wx.fst.get vs.length ⟨i, hi_vs⟩) := by rw [hfst_i]
    _ = (retract tau Wx.fst).get vs.length ⟨i, hi_vs⟩ := by
      rw [retract_get_comm
        (hasArity_of_mem_toSMTZFSet tau_hasArity hWx_mem)
        tau_hasArity hWx_mem]
    _ = x.get vs.length ⟨i, hi_vs⟩ := by rw [hWx_retract]

open Classical in
/-- Install the canonical projections of a collection element as a
representation-aware binder valuation.  Outside the binder names the
ambient valuation is unchanged; at the binder names each projection is
related to its source component by the preceding lemma. -/
theorem represented_toDestPair_bound_context.{u}
    {vs : List B.𝒱} (vs_nemp : vs ≠ []) (vs_nodup : vs.Nodup)
    {tau : BType} (tau_hasArity : tau.hasArity vs.length)
    {x : ZFSet.{u}} (hx_mem : x ∈ ⟦tau⟧ᶻ)
    {z : SMT.𝒱} {Delta : SMT.RenamingContext.Context.{u}}
    {Wx : SMT.Dom.{u}}
    (hcov_z : SMT.RenamingContext.CoversFV Delta (.var z))
    (hden_z : ⟦(SMT.Term.var z).abstract Delta hcov_z⟧ˢ = some Wx)
    (hWx_type : Wx.snd.fst = tau.toSMTType)
    (hWx_mem : Wx.fst ∈ ⟦tau.toSMTType⟧ᶻ)
    (hWx_retract : retract tau Wx.fst = x)
    {Xi : B.RenamingContext.Context.{u}}
    {Theta : SMT.RenamingContext.Context.{u}} {P : B.Term}
    (ambient : ∀ v ∈ B.fv P, v ∉ vs →
      match Xi v, Theta v with
      | some d, some d' => RDomCastSupported d d'
      | _, _ => False) :
    ∃ ss : Fin vs.length → SMT.Dom.{u},
      (∀ i,
        ∃ hcov : SMT.RenamingContext.CoversFV Delta
            ((toDestPair vs (.var z))[i.val]'(by
              rw [toDestPair_length_gen vs (.var z) (.var z) [] vs_nemp]
              exact i.isLt)),
          ⟦((toDestPair vs (.var z))[i.val]'(by
              rw [toDestPair_length_gen vs (.var z) (.var z) [] vs_nemp]
              exact i.isLt)).abstract Delta hcov⟧ˢ = some (ss i) ∧
          RDomCastSupported
            (⟨x.get vs.length i, tau.get vs.length i,
              get_mem_type_of_isTuple
                (hasArity_of_mem_toZFSet tau_hasArity hx_mem)
                tau_hasArity hx_mem⟩ : B.Dom)
            (ss i)) ∧
      RValuationCastSupportedOnFV
        (Function.updates Xi vs
          (List.ofFn fun i => some
            (⟨x.get vs.length i, tau.get vs.length i,
              get_mem_type_of_isTuple
                (hasArity_of_mem_toZFSet tau_hasArity hx_mem)
                tau_hasArity hx_mem⟩ : B.Dom)))
        (Function.updates Theta vs
          (List.ofFn fun i => some (ss i))) P := by
  let x_fin : Fin vs.length → B.Dom.{u} := fun i =>
    ⟨x.get vs.length i, tau.get vs.length i,
      get_mem_type_of_isTuple
        (hasArity_of_mem_toZFSet tau_hasArity hx_mem)
        tau_hasArity hx_mem⟩
  have hcomponent : ∀ i : Fin vs.length,
      ∃ (hcov : SMT.RenamingContext.CoversFV Delta
          ((toDestPair vs (.var z))[i.val]'(by
            rw [toDestPair_length_gen vs (.var z) (.var z) [] vs_nemp]
            exact i.isLt)))
        (Di : SMT.Dom.{u}),
        ⟦((toDestPair vs (.var z))[i.val]'(by
            rw [toDestPair_length_gen vs (.var z) (.var z) [] vs_nemp]
            exact i.isLt)).abstract Delta hcov⟧ˢ = some Di ∧
        RDomCastSupported (x_fin i) Di := by
    intro i
    simpa [x_fin] using
      (toDestPair_denote_represented_components vs_nemp tau_hasArity
        hx_mem hcov_z hden_z hWx_type hWx_mem hWx_retract
        i.val i.isLt (by
          rw [toDestPair_length_gen vs (.var z) (.var z) [] vs_nemp]
          exact i.isLt))
  let ss : Fin vs.length → SMT.Dom.{u} := fun i =>
    Classical.choose (Classical.choose_spec (hcomponent i))
  refine ⟨ss, ?_, ?_⟩
  · intro i
    let hcov := Classical.choose (hcomponent i)
    obtain ⟨hden, hrel⟩ :=
      Classical.choose_spec (Classical.choose_spec (hcomponent i))
    refine ⟨hcov, ?_, ?_⟩
    · simpa [ss] using hden
    · simpa [ss, x_fin] using hrel
  · simpa [x_fin] using
      (RValuationCastSupportedOnFV.updates vs_nodup x_fin ss ambient
        (fun i => by
          obtain ⟨hden, hrel⟩ :=
            Classical.choose_spec (Classical.choose_spec (hcomponent i))
          simpa [ss] using hrel))

/-- Applying a canonical characteristic-predicate representative at the
canonical image of a source element in its represented set evaluates to
`true`.  This is the domain side of the `collect` body bridge. -/
theorem represented_set_app_true_of_mem_canonical.{u}
    {tau : BType} {S : ZFSet.{u}} {hS : S ∈ ⟦BType.set tau⟧ᶻ}
    {Denc : SMT.Term} {z : SMT.𝒱}
    {Delta : SMT.RenamingContext.Context.{u}} {Dval : SMT.Dom.{u}}
    (hcov_D_upd : ∀ W : SMT.Dom,
      SMT.RenamingContext.CoversFV
        (Function.update Delta z (some W)) Denc)
    (den_D_upd : ∀ W : SMT.Dom,
      ⟦Denc.abstract (Function.update Delta z (some W))
        (hcov_D_upd W)⟧ˢ = some Dval)
    (hD_type : Dval.snd.fst = tau.toSMTType.fun SMTType.bool)
    (hD_func : ⟦tau.toSMTType⟧ᶻ.IsFunc 𝔹 Dval.fst)
    (D_rel : RDomCastSupported
      (⟨S, BType.set tau, hS⟩ : B.Dom) Dval)
    {x : ZFSet.{u}} (hx : x ∈ S) :
    let Wx : SMT.Dom :=
      ⟨(ZFSet.fapply (BType.canonicalIsoSMTType tau).1
        (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType tau).2.1)
        ⟨x, by
          have hS_sub : S ⊆ ⟦tau⟧ᶻ := by
            rwa [BType.toZFSet, ZFSet.mem_powerset] at hS
          exact (by
            rw [ZFSet.is_func_dom_eq
              (BType.canonicalIsoSMTType tau).2.1]
            exact hS_sub hx)⟩).1,
        tau.toSMTType, ZFSet.fapply_mem_range _ _⟩
    ∃ (hcov : SMT.RenamingContext.CoversFV
        (Function.update Delta z (some Wx)) ((@ˢDenc) (.var z)))
      (Dapp : SMT.Dom.{u}),
      ⟦((@ˢDenc) (.var z)).abstract
        (Function.update Delta z (some Wx)) hcov⟧ˢ = some Dapp ∧
      Dapp.snd.fst = SMTType.bool ∧ Dapp.fst = ZFSet.zftrue := by
  rcases Dval with ⟨F, sigma, hF⟩
  dsimp at hD_type
  subst sigma
  let Dval : SMT.Dom := ⟨F, tau.toSMTType.fun SMTType.bool, hF⟩
  have hD_type : Dval.snd.fst = tau.toSMTType.fun SMTType.bool := rfl
  have hD_func' : ⟦tau.toSMTType⟧ᶻ.IsFunc 𝔹 Dval.fst := by
    simpa [Dval] using hD_func
  have D_rel' : RDomCastSupported
      (⟨S, BType.set tau, hS⟩ : B.Dom) Dval := by
    simpa [Dval] using D_rel
  dsimp
  have hS_sub : S ⊆ ⟦tau⟧ᶻ := by
    rwa [BType.toZFSet, ZFSet.mem_powerset] at hS
  have hx_tau : x ∈ ⟦tau⟧ᶻ := hS_sub hx
  let Wx : SMT.Dom :=
    ⟨(ZFSet.fapply (BType.canonicalIsoSMTType tau).1
      (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType tau).2.1)
      ⟨x, by
        rwa [ZFSet.is_func_dom_eq
          (BType.canonicalIsoSMTType tau).2.1]⟩).1,
      tau.toSMTType, ZFSet.fapply_mem_range _ _⟩
  have hWx_type : Wx.snd.fst = tau.toSMTType := rfl
  have hWx_mem : Wx.fst ∈ ⟦tau.toSMTType⟧ᶻ := Wx.snd.snd
  obtain ⟨hcov_app, Dapp, hDapp_type, hDapp_value, hden_app⟩ :=
    funDenoteAppAt (Δctx := Delta) (t := Denc) (x := z)
      (α := tau.toSMTType) (β := SMTType.bool) (Y := Dval)
      hcov_D_upd den_D_upd hD_type hD_func' Wx hWx_type hWx_mem
  refine ⟨hcov_app, Dapp, hden_app, hDapp_type, ?_⟩
  rw [hDapp_value]
  have D_canonical : (⟨S, BType.set tau, hS⟩ : B.Dom) ≘ᶻ Dval :=
    (RDomCast.iff_RDom_of_type_eq (α := BType.set tau) rfl).mp
      D_rel'.toRDomCast
  rw [RDom] at D_canonical
  have hx_retract : x ∈ retract (BType.set tau) Dval.fst := by
    rw [D_canonical.2]
    exact hx
  rw [retract, ZFSet.mem_sep, dif_pos hx_tau, dif_pos hD_func'] at hx_retract
  simpa [Wx] using hx_retract.2

/-- Applying an option-function representative at the canonical image of a
source-domain input returns `some` of the canonical output whenever the
corresponding source pair belongs to the represented relation.  This is the
function-domain analogue of `represented_set_app_true_of_mem_canonical` and
is the bridge used by the guarded `collect` encoder arm. -/
theorem represented_option_app_some_of_mem_canonical.{u}
    {alpha beta : BType} {S : ZFSet.{u}}
    {hS : S ∈ ⟦BType.set (alpha ×ᴮ beta)⟧ᶻ}
    {Denc : SMT.Term} {z : SMT.𝒱}
    {Delta : SMT.RenamingContext.Context.{u}} {Dval : SMT.Dom.{u}}
    (hcov_D_upd : ∀ W : SMT.Dom,
      SMT.RenamingContext.CoversFV
        (Function.update Delta z (some W)) Denc)
    (den_D_upd : ∀ W : SMT.Dom,
      ⟦Denc.abstract (Function.update Delta z (some W))
        (hcov_D_upd W)⟧ˢ = some Dval)
    (hD_type : Dval.snd.fst = alpha.toSMTType.fun
      (SMTType.option beta.toSMTType))
    (hD_func : ⟦alpha.toSMTType⟧ᶻ.IsFunc
      ⟦SMTType.option beta.toSMTType⟧ᶻ Dval.fst)
    (D_rel : RDomCastSupported
      (⟨S, BType.set (alpha ×ᴮ beta), hS⟩ : B.Dom) Dval)
    {a b : ZFSet.{u}} (ha : a ∈ ⟦alpha⟧ᶻ)
    (hb : b ∈ ⟦beta⟧ᶻ) (hmem : a.pair b ∈ S) :
    let Wa : SMT.Dom.{u} := B.Dom.canonicalSMT
      (⟨a, alpha, ha⟩ : B.Dom)
    let Wb : SMT.Dom.{u} := B.Dom.canonicalSMT
      (⟨b, beta, hb⟩ : B.Dom)
    ∃ (hcov : SMT.RenamingContext.CoversFV
        (Function.update Delta z (some Wa)) ((@ˢDenc) (.var z)))
      (Dapp : SMT.Dom.{u}),
      ⟦((@ˢDenc) (.var z)).abstract
        (Function.update Delta z (some Wa)) hcov⟧ˢ = some Dapp ∧
      Dapp.snd.fst = SMTType.option beta.toSMTType ∧
      Dapp.fst = (ZFSet.Option.some
        (S := ⟦beta.toSMTType⟧ᶻ) ⟨Wb.fst, Wb.snd.snd⟩).val := by
  classical
  dsimp only
  rcases Dval with ⟨G, sigma, hG⟩
  dsimp at hD_type
  subst sigma
  let Dval : SMT.Dom := ⟨G,
    alpha.toSMTType.fun (SMTType.option beta.toSMTType), hG⟩
  have hD_type : Dval.snd.fst = alpha.toSMTType.fun
      (SMTType.option beta.toSMTType) := rfl
  have hD_func' : ⟦alpha.toSMTType⟧ᶻ.IsFunc
      ⟦SMTType.option beta.toSMTType⟧ᶻ Dval.fst := by
    simpa [Dval] using hD_func
  have D_rel' : RDomCastSupported
      (⟨S, BType.set (alpha ×ᴮ beta), hS⟩ : B.Dom) Dval := by
    simpa [Dval] using D_rel
  let Wa : SMT.Dom := B.Dom.canonicalSMT
    (⟨a, alpha, ha⟩ : B.Dom)
  let Wb : SMT.Dom := B.Dom.canonicalSMT
    (⟨b, beta, hb⟩ : B.Dom)
  have hWa_type : Wa.snd.fst = alpha.toSMTType :=
    B.Dom.canonicalSMT_type _
  have hWa_mem : Wa.fst ∈ ⟦alpha.toSMTType⟧ᶻ := by
    rw [← hWa_type]
    exact Wa.snd.snd
  have hWb_type : Wb.snd.fst = beta.toSMTType :=
    B.Dom.canonicalSMT_type _
  have hWb_mem : Wb.fst ∈ ⟦beta.toSMTType⟧ᶻ := by
    rw [← hWb_type]
    exact Wb.snd.snd
  obtain ⟨hcov_app, Dapp, hDapp_type, hDapp_value, hden_app⟩ :=
    funDenoteAppAt (Δctx := Delta) (t := Denc) (x := z)
      (α := alpha.toSMTType) (β := SMTType.option beta.toSMTType)
      (Y := Dval) hcov_D_upd den_D_upd hD_type hD_func'
      Wa hWa_type hWa_mem
  refine ⟨hcov_app, Dapp, hden_app, hDapp_type, ?_⟩
  rw [hDapp_value]
  have hWa_rel : RDomCast (⟨a, alpha, ha⟩ : B.Dom) Wa :=
    B.Dom.rdomCast_canonicalSMT _
  have hWb_retract : retract beta Wb.fst = b := by
    have hcanonical := B.Dom.rdom_canonicalSMT
      (⟨b, beta, hb⟩ : B.Dom)
    rw [RDom] at hcanonical
    simpa [Wb] using hcanonical.2
  have hpair_retract : retract (alpha ×ᴮ beta) (Wa.fst.pair Wb.fst) =
      a.pair b := by
    have hWa_retract : retract alpha Wa.fst = a := by
      have hcanonical := B.Dom.rdom_canonicalSMT
        (⟨a, alpha, ha⟩ : B.Dom)
      rw [RDom] at hcanonical
      simpa [Wa] using hcanonical.2
    simp [retract, hWa_retract, hWb_retract]
  have hgraph_retract : retract (BType.set (alpha ×ᴮ beta))
      (optionGraph alpha.toSMTType beta.toSMTType Dval.fst) = S :=
    RDomCast.optionFunction_graph_retract D_rel'.toRDomCast
  have hsem := RDomCast.optionFunction_eq_some_eq_zftrue_iff
    (hX := ZFSet.pair_mem_prod.mpr ⟨ha, hb⟩)
    (ha := hWa_mem) (hb := hWb_mem) (hF := Dval.snd.snd)
    hpair_retract hgraph_retract
  dsimp only at hsem
  rw [zfEqIn_eq_zftrue_iff (ZFSet.fapply_mem_range _ _)
    (ZFSet.Option.some (S := ⟦beta.toSMTType⟧ᶻ)
      ⟨Wb.fst, hWb_mem⟩ |>.property)] at hsem
  simpa [Dval, Wa, Wb, proof_irrel_heq] using hsem.mpr hmem

open Classical in
/-- At canonical source endpoints, an option-function representative returns
the canonical `some` payload exactly when the corresponding source pair lies
in the represented relation. -/
theorem represented_option_app_some_iff_canonical.{u}
    {alpha beta : BType} {S : ZFSet.{u}}
    {hS : S ∈ ⟦BType.set (alpha ×ᴮ beta)⟧ᶻ}
    {Denc : SMT.Term} {z : SMT.𝒱}
    {Delta : SMT.RenamingContext.Context.{u}} {Dval : SMT.Dom.{u}}
    (hcov_D_upd : ∀ W : SMT.Dom,
      SMT.RenamingContext.CoversFV
        (Function.update Delta z (some W)) Denc)
    (den_D_upd : ∀ W : SMT.Dom,
      ⟦Denc.abstract (Function.update Delta z (some W))
        (hcov_D_upd W)⟧ˢ = some Dval)
    (hD_type : Dval.snd.fst = alpha.toSMTType.fun
      (SMTType.option beta.toSMTType))
    (hD_func : ⟦alpha.toSMTType⟧ᶻ.IsFunc
      ⟦SMTType.option beta.toSMTType⟧ᶻ Dval.fst)
    (D_rel : RDomCastSupported
      (⟨S, BType.set (alpha ×ᴮ beta), hS⟩ : B.Dom) Dval)
    {a b : ZFSet.{u}} (ha : a ∈ ⟦alpha⟧ᶻ)
    (hb : b ∈ ⟦beta⟧ᶻ) :
    let Wa : SMT.Dom.{u} := B.Dom.canonicalSMT
      (⟨a, alpha, ha⟩ : B.Dom)
    let Wb : SMT.Dom.{u} := B.Dom.canonicalSMT
      (⟨b, beta, hb⟩ : B.Dom)
    ∃ (hcov : SMT.RenamingContext.CoversFV
        (Function.update Delta z (some Wa)) ((@ˢDenc) (.var z)))
      (Dapp : SMT.Dom.{u}),
      ⟦((@ˢDenc) (.var z)).abstract
        (Function.update Delta z (some Wa)) hcov⟧ˢ = some Dapp ∧
      Dapp.snd.fst = SMTType.option beta.toSMTType ∧
      (Dapp.fst = (ZFSet.Option.some
        (S := ⟦beta.toSMTType⟧ᶻ) ⟨Wb.fst, Wb.snd.snd⟩).val ↔
        a.pair b ∈ S) := by
  dsimp only
  rcases Dval with ⟨G, sigma, hG⟩
  dsimp at hD_type
  subst sigma
  let Dval : SMT.Dom := ⟨G,
    alpha.toSMTType.fun (SMTType.option beta.toSMTType), hG⟩
  have hD_type : Dval.snd.fst = alpha.toSMTType.fun
      (SMTType.option beta.toSMTType) := rfl
  have hD_func' : ⟦alpha.toSMTType⟧ᶻ.IsFunc
      ⟦SMTType.option beta.toSMTType⟧ᶻ Dval.fst := by
    simpa [Dval] using hD_func
  have D_rel' : RDomCastSupported
      (⟨S, BType.set (alpha ×ᴮ beta), hS⟩ : B.Dom) Dval := by
    simpa [Dval] using D_rel
  let Wa : SMT.Dom := B.Dom.canonicalSMT
    (⟨a, alpha, ha⟩ : B.Dom)
  let Wb : SMT.Dom := B.Dom.canonicalSMT
    (⟨b, beta, hb⟩ : B.Dom)
  have hWa_type : Wa.snd.fst = alpha.toSMTType :=
    B.Dom.canonicalSMT_type _
  have hWa_mem : Wa.fst ∈ ⟦alpha.toSMTType⟧ᶻ := by
    rw [← hWa_type]
    exact Wa.snd.snd
  have hWb_type : Wb.snd.fst = beta.toSMTType :=
    B.Dom.canonicalSMT_type _
  have hWb_mem : Wb.fst ∈ ⟦beta.toSMTType⟧ᶻ := by
    rw [← hWb_type]
    exact Wb.snd.snd
  obtain ⟨hcov_app, Dapp, hDapp_type, hDapp_value, hden_app⟩ :=
    funDenoteAppAt (Δctx := Delta) (t := Denc) (x := z)
      (α := alpha.toSMTType) (β := SMTType.option beta.toSMTType)
      (Y := Dval) hcov_D_upd den_D_upd hD_type hD_func'
      Wa hWa_type hWa_mem
  refine ⟨hcov_app, Dapp, hden_app, hDapp_type, ?_⟩
  rw [hDapp_value]
  have hWb_retract : retract beta Wb.fst = b := by
    have hcanonical := B.Dom.rdom_canonicalSMT
      (⟨b, beta, hb⟩ : B.Dom)
    rw [RDom] at hcanonical
    simpa [Wb] using hcanonical.2
  have hpair_retract : retract (alpha ×ᴮ beta) (Wa.fst.pair Wb.fst) =
      a.pair b := by
    have hWa_retract : retract alpha Wa.fst = a := by
      have hcanonical := B.Dom.rdom_canonicalSMT
        (⟨a, alpha, ha⟩ : B.Dom)
      rw [RDom] at hcanonical
      simpa [Wa] using hcanonical.2
    simp [retract, hWa_retract, hWb_retract]
  have hgraph_retract : retract (BType.set (alpha ×ᴮ beta))
      (optionGraph alpha.toSMTType beta.toSMTType Dval.fst) = S :=
    RDomCast.optionFunction_graph_retract D_rel'.toRDomCast
  have hsem := RDomCast.optionFunction_eq_some_eq_zftrue_iff
    (hX := ZFSet.pair_mem_prod.mpr ⟨ha, hb⟩)
    (ha := hWa_mem) (hb := hWb_mem) (hF := Dval.snd.snd)
    hpair_retract hgraph_retract
  dsimp only at hsem
  rw [zfEqIn_eq_zftrue_iff (ZFSet.fapply_mem_range _ _)
    (ZFSet.Option.some (S := ⟦beta.toSMTType⟧ᶻ)
      ⟨Wb.fst, hWb_mem⟩ |>.property)] at hsem
  simpa [Dval, Wa, Wb, proof_irrel_heq] using hsem

/-- Eliminating an option-valued target term whose value is a canonical
`some` produces the corresponding payload.  The conclusion deliberately
keeps only the value and type tag, so it is insensitive to proof fields in
the dependent domain representation. -/
theorem denote_the_of_some.{u}
    {t : SMT.Term} {Theta : SMT.RenamingContext.Context.{u}}
    (hcov_t : SMT.RenamingContext.CoversFV Theta t)
    {D W : SMT.Dom.{u}} {beta : SMTType}
    (hden_t : ⟦t.abstract Theta hcov_t⟧ˢ = some D)
    (hD_type : D.snd.fst = SMTType.option beta)
    (hW_type : W.snd.fst = beta)
    (hD_value : D.fst = (ZFSet.Option.some
      (S := ⟦beta⟧ᶻ) ⟨W.fst, by rw [← hW_type]; exact W.snd.snd⟩).val) :
    ∃ (hcov_the : SMT.RenamingContext.CoversFV Theta (SMT.Term.the t))
      (Dthe : SMT.Dom.{u}),
      ⟦(SMT.Term.the t).abstract Theta hcov_the⟧ˢ = some Dthe ∧
      Dthe.snd.fst = beta ∧ Dthe.fst = W.fst := by
  classical
  have hcov_the : SMT.RenamingContext.CoversFV Theta (SMT.Term.the t) := by
    intro v hv
    exact hcov_t v (by simpa [SMT.fv] using hv)
  refine ⟨hcov_the, ?_⟩
  rcases D with ⟨Dval, Dsigma, hDmem⟩
  dsimp at hD_type hD_value
  subst Dsigma
  let Wpayload : {x // x ∈ ⟦beta⟧ᶻ} :=
    ⟨W.fst, by simpa [hW_type] using W.snd.snd⟩
  let Wsome : ZFSet.Option ⟦beta⟧ᶻ := ZFSet.Option.some Wpayload
  have hD_value' : Dval = Wsome.val := by
    simpa [Wsome, Wpayload] using hD_value
  let Dopt : ZFSet.Option ⟦beta⟧ᶻ := ⟨Dval, hDmem⟩
  have hDopt_eq : Dopt = Wsome := by
    apply Subtype.ext
    exact hD_value'
  have hthe : ZFSet.Option.the SMTType.toZFSet_nonempty Wsome = Wpayload := by
    unfold Wsome
    unfold ZFSet.Option.the
    rw [dif_neg (ZFSet.Option.some_ne_none Wpayload)]
    have hspec := Classical.choose_spec
      (Or.resolve_left
        (ZFSet.Option.casesOn (ZFSet.Option.some Wpayload))
        (ZFSet.Option.some_ne_none Wpayload))
    rw [ZFSet.Option.some.injEq] at hspec
    exact hspec.symm
  let Dthe : SMT.Dom := ⟨(ZFSet.Option.the SMTType.toZFSet_nonempty Dopt).val,
    beta, SetLike.coe_mem _⟩
  refine ⟨Dthe, ?_, rfl, ?_⟩
  · rw [SMT.Term.abstract.eq_def, SMT.denote]
    conv =>
      lhs
      rw [SMT.RenamingContext.denote_abstract_proof_irrel t Theta _ hcov_t]
    rw [hden_t]
    rfl
  · dsimp [Dthe]
    rw [hDopt_eq, hthe]

open Classical in
/-- The guarded option payload used by the function-valued `collect` encoder
returns `some W` when its domain application is `some W` and its substituted
predicate is true.  The input is phrased at the PHOAS level so callers can
reuse the lemma after establishing coverage for their concrete syntax. -/
theorem denote_guarded_option_some_of.{u}
    {d p : SMT.PHOAS.Term SMT.Dom}
    {Dd Dp Dthe W : SMT.Dom.{u}} {beta : SMTType}
    (hden_d : ⟦d⟧ˢ = some Dd)
    (hD_type : Dd.snd.fst = SMTType.option beta)
    (hW_type : W.snd.fst = beta)
    (hD_value : Dd.fst = (ZFSet.Option.some
      (S := ⟦beta⟧ᶻ) ⟨W.fst, by rw [← hW_type]; exact W.snd.snd⟩).val)
    (hden_the : ⟦SMT.PHOAS.Term.the d⟧ˢ = some Dthe)
    (hDthe_type : Dthe.snd.fst = beta)
    (hDthe_value : Dthe.fst = W.fst)
    (hden_p : ⟦p⟧ˢ = some Dp)
    (hP_type : Dp.snd.fst = SMTType.bool)
    (hP_true : Dp.fst = ZFSet.zftrue) :
    ∃ Dsome : SMT.Dom.{u},
      ⟦SMT.PHOAS.Term.ite
        (SMT.PHOAS.Term.and
          (SMT.PHOAS.Term.eq d (SMT.PHOAS.Term.some (SMT.PHOAS.Term.the d))) p)
        (SMT.PHOAS.Term.some (SMT.PHOAS.Term.the d))
        (SMT.PHOAS.Term.none beta)⟧ˢ = some Dsome ∧
      Dsome.snd.fst = SMTType.option beta ∧
      Dsome.fst = (ZFSet.Option.some
        (S := ⟦beta⟧ᶻ) ⟨W.fst, by rw [← hW_type]; exact W.snd.snd⟩).val := by
  rcases Dthe with ⟨T, tau, hT⟩
  dsimp at hDthe_type hDthe_value hden_the
  subst tau
  let Dsome : SMT.Dom := ⟨(ZFSet.Option.some
    (S := ⟦beta⟧ᶻ) ⟨T, hT⟩).val,
    SMTType.option beta, SetLike.coe_mem _⟩
  have hDsome_type : Dsome.snd.fst = SMTType.option beta := rfl
  have hDsome_value : Dsome.fst = (ZFSet.Option.some
      (S := ⟦beta⟧ᶻ) ⟨W.fst, by rw [← hW_type]; exact W.snd.snd⟩).val := by
    dsimp [Dsome]
    apply congrArg (fun x : {x // x ∈ ⟦beta⟧ᶻ} =>
      (ZFSet.Option.some x).val)
    apply Subtype.ext
    exact hDthe_value
  have hden_some_the : ⟦SMT.PHOAS.Term.some
      (SMT.PHOAS.Term.the d)⟧ˢ = some Dsome := by
    rw [SMT.denote, hden_the]
    rfl
  have heq_value : Dd.fst = Dsome.fst := by
    rw [hD_value, hDsome_value]
  have hden_eq : ⟦SMT.PHOAS.Term.eq d
      (SMT.PHOAS.Term.some (SMT.PHOAS.Term.the d))⟧ˢ =
        some ⟨ZFSet.zftrue, SMTType.bool,
          ZFSet.ZFBool.zftrue_mem_𝔹⟩ :=
    denote_eq_eq_zftrue_of_fst_eq hden_d hden_some_the
      (hD_type.trans hDsome_type.symm) heq_value
  have hden_guard : ⟦SMT.PHOAS.Term.and
      (SMT.PHOAS.Term.eq d (SMT.PHOAS.Term.some (SMT.PHOAS.Term.the d))) p⟧ˢ =
        some ⟨ZFSet.zftrue, SMTType.bool,
          ZFSet.ZFBool.zftrue_mem_𝔹⟩ :=
    denote_and_eq_zftrue_of_some_zftrue hden_eq rfl rfl hden_p hP_type hP_true
  refine ⟨Dsome, ?_, hDsome_type, hDsome_value⟩
  rw [SMT.denote, hden_guard]
  change (if ZFSet.ZFBool.toBool
      ⟨ZFSet.zftrue, ZFSet.ZFBool.zftrue_mem_𝔹⟩ then
      ⟦SMT.PHOAS.Term.some (SMT.PHOAS.Term.the d)⟧ˢ else
      ⟦SMT.PHOAS.Term.none beta⟧ˢ) = some Dsome
  have htoBool : ZFSet.ZFBool.toBool
      ⟨ZFSet.zftrue, ZFSet.ZFBool.zftrue_mem_𝔹⟩ = true := by
    change (⊤ : ZFSet.ZFBool).toBool = true
    exact ZFSet.ZFBool.toBool_true
  rw [htoBool, if_pos rfl]
  exact hden_some_the

open Classical in
/-- A successful option-valued PHOAS term can always be eliminated to a
typed payload value.  This target-only form is used by the reverse direction
of the guarded option-body characterization. -/
theorem denote_the_of_option_value.{u}
    {d : SMT.PHOAS.Term SMT.Dom.{u}} {Dd : SMT.Dom.{u}} {beta : SMTType}
    (hden_d : ⟦d⟧ˢ = some Dd)
    (hD_type : Dd.snd.fst = SMTType.option beta) :
    ∃ Dthe : SMT.Dom.{u},
      ⟦SMT.PHOAS.Term.the d⟧ˢ = some Dthe ∧
      Dthe.snd.fst = beta := by
  rcases Dd with ⟨Dval, Dsigma, hDmem⟩
  dsimp at hD_type hden_d
  subst Dsigma
  let Dthe : SMT.Dom := ⟨(ZFSet.Option.the SMTType.toZFSet_nonempty
    ⟨Dval, hDmem⟩).val, beta, SetLike.coe_mem _⟩
  refine ⟨Dthe, ?_, rfl⟩
  rw [SMT.denote, hden_d]
  rfl

open Classical in
/-- When an option-valued PHOAS term is known to be a particular `some W`,
eliminating it returns that same payload. -/
theorem denote_the_of_option_some_value.{u}
    {d : SMT.PHOAS.Term SMT.Dom.{u}} {Dd W : SMT.Dom.{u}} {beta : SMTType}
    (hden_d : ⟦d⟧ˢ = some Dd)
    (hD_type : Dd.snd.fst = SMTType.option beta)
    (hW_type : W.snd.fst = beta)
    (hD_value : Dd.fst = (ZFSet.Option.some
      (S := ⟦beta⟧ᶻ) ⟨W.fst, by rw [← hW_type]; exact W.snd.snd⟩).val) :
    ∃ Dthe : SMT.Dom.{u},
      ⟦SMT.PHOAS.Term.the d⟧ˢ = some Dthe ∧
      Dthe.snd.fst = beta ∧ Dthe.fst = W.fst := by
  rcases Dd with ⟨Dval, Dsigma, hDmem⟩
  dsimp at hD_type hD_value hden_d
  subst Dsigma
  let Wpayload : {x // x ∈ ⟦beta⟧ᶻ} :=
    ⟨W.fst, by rw [← hW_type]; exact W.snd.snd⟩
  let Wsome : ZFSet.Option ⟦beta⟧ᶻ := ZFSet.Option.some Wpayload
  have hDval : Dval = Wsome.val := by
    simpa [Wsome, Wpayload] using hD_value
  let Dopt : ZFSet.Option ⟦beta⟧ᶻ := ⟨Dval, hDmem⟩
  have hDopt : Dopt = Wsome := by
    apply Subtype.ext
    exact hDval
  have hthe : ZFSet.Option.the SMTType.toZFSet_nonempty Wsome = Wpayload := by
    unfold Wsome
    unfold ZFSet.Option.the
    rw [dif_neg (ZFSet.Option.some_ne_none Wpayload)]
    have hspec := Classical.choose_spec
      (Or.resolve_left
        (ZFSet.Option.casesOn (ZFSet.Option.some Wpayload))
        (ZFSet.Option.some_ne_none Wpayload))
    rw [ZFSet.Option.some.injEq] at hspec
    exact hspec.symm
  let Dthe : SMT.Dom := ⟨(ZFSet.Option.the SMTType.toZFSet_nonempty Dopt).val,
    beta, SetLike.coe_mem _⟩
  refine ⟨Dthe, ?_, rfl, ?_⟩
  · rw [SMT.denote, hden_d]
    rfl
  · dsimp [Dthe]
    rw [hDopt, hthe]

private theorem collect_denote_and_both_zftrue
    {p q : SMT.PHOAS.Term SMT.Dom} {Dp Dq : SMT.Dom}
    (hp : ⟦p⟧ˢ = some Dp) (hpTy : Dp.2.1 = .bool)
    (hq : ⟦q⟧ˢ = some Dq) (hqTy : Dq.2.1 = .bool)
    {Dand : SMT.Dom}
    (hand : ⟦p ∧ˢ' q⟧ˢ = some Dand) (handTrue : Dand.1 = zftrue) :
    Dp.1 = zftrue ∧ Dq.1 = zftrue := by
  have hDp_mem_𝔹 : Dp.fst ∈ 𝔹 := by
    have h := Dp.snd.snd
    rwa [hpTy] at h
  have hDq_mem_𝔹 : Dq.fst ∈ 𝔹 := by
    have h := Dq.snd.snd
    rwa [hqTy] at h
  constructor
  · rcases ZFSet.ZFBool.mem_𝔹_iff _ |>.mp hDp_mem_𝔹 with hDp_false | hDp_true
    · exfalso
      have hfalse := denote_and_eq_zffalse_of_some_zffalse_left
        hp hpTy hDp_false hq hqTy
      rw [hfalse] at hand
      have heq := Option.some_injective _ hand
      rw [← congrArg (·.fst) heq] at handTrue
      exact ZFSet.zftrue_ne_zffalse handTrue.symm
    · exact hDp_true
  · rcases ZFSet.ZFBool.mem_𝔹_iff _ |>.mp hDq_mem_𝔹 with hDq_false | hDq_true
    · exfalso
      have hfalse := denote_and_eq_zffalse_of_some_zffalse_right
        hp hpTy hq hqTy hDq_false
      rw [hfalse] at hand
      have heq := Option.some_injective _ hand
      rw [← congrArg (·.fst) heq] at handTrue
      exact ZFSet.zftrue_ne_zffalse handTrue.symm
    · exact hDq_true

open Classical in
/-- If the guarded option payload has produced `some W`, then both parts of
its guard succeeded: the domain application was that same `some W`, and the
substituted Boolean predicate was true. -/
theorem denote_guarded_option_some_elim.{u}
    {d p : SMT.PHOAS.Term SMT.Dom.{u}}
    {Dd Dp Dbody W : SMT.Dom.{u}} {beta : SMTType}
    (hden_d : ⟦d⟧ˢ = some Dd)
    (hD_type : Dd.snd.fst = SMTType.option beta)
    (hden_p : ⟦p⟧ˢ = some Dp)
    (hP_type : Dp.snd.fst = SMTType.bool)
    (hW_type : W.snd.fst = beta)
    (hden_body : ⟦SMT.PHOAS.Term.ite
      (SMT.PHOAS.Term.and
        (SMT.PHOAS.Term.eq d (SMT.PHOAS.Term.some (SMT.PHOAS.Term.the d))) p)
      (SMT.PHOAS.Term.some (SMT.PHOAS.Term.the d))
      (SMT.PHOAS.Term.none beta)⟧ˢ = some Dbody)
    (hbody_value : Dbody.fst = (ZFSet.Option.some
      (S := ⟦beta⟧ᶻ) ⟨W.fst, by rw [← hW_type]; exact W.snd.snd⟩).val) :
    Dd.fst = (ZFSet.Option.some
      (S := ⟦beta⟧ᶻ) ⟨W.fst, by rw [← hW_type]; exact W.snd.snd⟩).val ∧
      Dp.fst = ZFSet.zftrue := by
  obtain ⟨Dthe, hden_the, hDthe_type⟩ :=
    denote_the_of_option_value hden_d hD_type
  let Dsome : SMT.Dom := ⟨(ZFSet.Option.some
    (S := ⟦beta⟧ᶻ) ⟨Dthe.fst, by rw [← hDthe_type]; exact Dthe.snd.snd⟩).val,
    SMTType.option beta, SetLike.coe_mem _⟩
  have hDsome_type : Dsome.snd.fst = SMTType.option beta := rfl
  have hden_some : ⟦SMT.PHOAS.Term.some
      (SMT.PHOAS.Term.the d)⟧ˢ = some Dsome := by
    rcases Dthe with ⟨T, tau, hT⟩
    dsimp at hDthe_type hden_the ⊢
    subst tau
    rw [SMT.denote, hden_the]
    rfl
  obtain ⟨Deq, hden_eq, hDeq_type⟩ :=
    denote_eq_some_of_some hden_d hden_some
      (hD_type.trans hDsome_type.symm)
  obtain ⟨Dguard, hden_guard, hguard_type⟩ :=
    denote_and_some_bool_of_some_bool hden_eq hDeq_type hden_p hP_type
  rcases Dguard with ⟨G, Gtype, hGmem⟩
  dsimp at hguard_type hden_guard
  subst Gtype
  rcases ZFSet.ZFBool.mem_𝔹_iff G |>.mp hGmem with hGfalse | hGtrue
  · let Dnone : SMT.Dom := ⟨(ZFSet.Option.none (S := ⟦beta⟧ᶻ)).val,
      SMTType.option beta, SetLike.coe_mem _⟩
    have hden_none : ⟦SMT.PHOAS.Term.ite
        (SMT.PHOAS.Term.and
          (SMT.PHOAS.Term.eq d (SMT.PHOAS.Term.some (SMT.PHOAS.Term.the d))) p)
        (SMT.PHOAS.Term.some (SMT.PHOAS.Term.the d))
        (SMT.PHOAS.Term.none beta)⟧ˢ = some Dnone := by
      rw [SMT.denote, hden_guard]
      change (if ZFSet.ZFBool.toBool ⟨G, hGmem⟩ then
        ⟦SMT.PHOAS.Term.some (SMT.PHOAS.Term.the d)⟧ˢ else
        ⟦SMT.PHOAS.Term.none beta⟧ˢ) = some Dnone
      have htoBool : ZFSet.ZFBool.toBool ⟨G, hGmem⟩ = false := by
        have hG : (⟨G, hGmem⟩ : ZFSet.ZFBool) = ⊥ := by
          apply Subtype.ext
          exact hGfalse
        rw [hG]
        exact ZFSet.ZFBool.toBool_false
      rw [htoBool, if_neg (by decide), SMT.denote]
      rfl
    have hbody_none : Dbody = Dnone :=
      Option.some.inj (hden_body.symm.trans hden_none)
    have hnone_some : ZFSet.Option.none (S := ⟦beta⟧ᶻ) =
        ZFSet.Option.some ⟨W.fst, by rw [← hW_type]; exact W.snd.snd⟩ := by
      apply Subtype.ext
      change Dnone.fst = (ZFSet.Option.some
        (S := ⟦beta⟧ᶻ) ⟨W.fst, by rw [← hW_type]; exact W.snd.snd⟩).val
      rw [← hbody_none, hbody_value]
    exact False.elim ((ZFSet.Option.some_ne_none _) hnone_some.symm)
  · have hden_body_some : ⟦SMT.PHOAS.Term.ite
        (SMT.PHOAS.Term.and
          (SMT.PHOAS.Term.eq d (SMT.PHOAS.Term.some (SMT.PHOAS.Term.the d))) p)
        (SMT.PHOAS.Term.some (SMT.PHOAS.Term.the d))
        (SMT.PHOAS.Term.none beta)⟧ˢ = some Dsome := by
      rw [SMT.denote, hden_guard]
      change (if ZFSet.ZFBool.toBool ⟨G, hGmem⟩ then
        ⟦SMT.PHOAS.Term.some (SMT.PHOAS.Term.the d)⟧ˢ else
        ⟦SMT.PHOAS.Term.none beta⟧ˢ) = some Dsome
      have htoBool : ZFSet.ZFBool.toBool ⟨G, hGmem⟩ = true := by
        have hG : (⟨G, hGmem⟩ : ZFSet.ZFBool) = ⊤ := by
          apply Subtype.ext
          exact hGtrue
        rw [hG]
        exact ZFSet.ZFBool.toBool_true
      rw [htoBool, if_pos rfl]
      exact hden_some
    have hbody_some : Dbody = Dsome :=
      Option.some.inj (hden_body.symm.trans hden_body_some)
    have hDthe_value : Dthe.fst = W.fst := by
      have hsome_eq : ZFSet.Option.some
          (S := ⟦beta⟧ᶻ) ⟨Dthe.fst, by rw [← hDthe_type]; exact Dthe.snd.snd⟩ =
          ZFSet.Option.some ⟨W.fst,
            by rw [← hW_type]; exact W.snd.snd⟩ := by
        apply Subtype.ext
        change Dsome.fst = (ZFSet.Option.some
          (S := ⟦beta⟧ᶻ) ⟨W.fst, by rw [← hW_type]; exact W.snd.snd⟩).val
        rw [← hbody_some, hbody_value]
      have hpayload_eq := ZFSet.Option.some.injEq.mp hsome_eq
      exact congrArg Subtype.val hpayload_eq
    obtain ⟨hEq_true, hP_true⟩ := collect_denote_and_both_zftrue
      hden_eq hDeq_type hden_p hP_type hden_guard hGtrue
    have hDd_eq_some : Dd.fst = Dsome.fst :=
      denote_eq_true_implies_fst_eq hden_d hden_some
        (hD_type.trans hDsome_type.symm) hden_eq hEq_true
    constructor
    · rw [hDd_eq_some]
      dsimp [Dsome]
      apply congrArg (fun x : {x // x ∈ ⟦beta⟧ᶻ} =>
        (ZFSet.Option.some x).val)
      apply Subtype.ext
      exact hDthe_value
    · exact hP_true

open Classical in
/-- Package the two directions of the guarded option-body semantics against
an arbitrary domain/predicate membership decomposition.  Collection-specific
proofs supply the decomposition from the source separation equation. -/
theorem denote_guarded_option_some_iff.{u}
    {d p : SMT.PHOAS.Term SMT.Dom.{u}}
    {Dd Dp Dbody W : SMT.Dom.{u}} {beta : SMTType}
    {domain_ok predicate_ok member : Prop}
    (hden_d : ⟦d⟧ˢ = some Dd)
    (hD_type : Dd.snd.fst = SMTType.option beta)
    (hden_p : ⟦p⟧ˢ = some Dp)
    (hP_type : Dp.snd.fst = SMTType.bool)
    (hW_type : W.snd.fst = beta)
    (hden_body : ⟦SMT.PHOAS.Term.ite
      (SMT.PHOAS.Term.and
        (SMT.PHOAS.Term.eq d (SMT.PHOAS.Term.some (SMT.PHOAS.Term.the d))) p)
      (SMT.PHOAS.Term.some (SMT.PHOAS.Term.the d))
      (SMT.PHOAS.Term.none beta)⟧ˢ = some Dbody)
    (hdomain : Dd.fst = (ZFSet.Option.some
      (S := ⟦beta⟧ᶻ) ⟨W.fst, by rw [← hW_type]; exact W.snd.snd⟩).val ↔
        domain_ok)
    (hpredicate : Dp.fst = ZFSet.zftrue ↔ predicate_ok)
    (hmembership : member ↔ domain_ok ∧ predicate_ok) :
    Dbody.fst = (ZFSet.Option.some
      (S := ⟦beta⟧ᶻ) ⟨W.fst, by rw [← hW_type]; exact W.snd.snd⟩).val ↔
      member := by
  constructor
  · intro hbody
    obtain ⟨hD, hP⟩ := denote_guarded_option_some_elim
      hden_d hD_type hden_p hP_type hW_type hden_body hbody
    exact hmembership.mpr ⟨hdomain.mp hD, hpredicate.mp hP⟩
  · intro hmember
    obtain ⟨hD, hP⟩ := hmembership.mp hmember
    obtain ⟨Dthe, hden_the, hDthe_type, hDthe_value⟩ :=
      denote_the_of_option_some_value hden_d hD_type hW_type
        (hdomain.mpr hD)
    obtain ⟨Dsome, hden_some, _hDsome_type, hDsome_value⟩ :=
      denote_guarded_option_some_of hden_d hD_type hW_type
        (hdomain.mpr hD) hden_the hDthe_type hDthe_value
        hden_p hP_type (hpredicate.mpr hP)
    have hbody_eq : Dbody = Dsome :=
      Option.some.inj (hden_body.symm.trans hden_some)
    rw [hbody_eq, hDsome_value]

open Classical in
/-- A one-binder SMT lambda evaluates at a typed argument to the denotation
of its body.  This is phrased with an arbitrary functional codomain so it can
be reused by both Boolean and option-valued binder encodings. -/
theorem single_lambda_fapply_eq_body.{u}
    {Delta : SMT.RenamingContext.Context.{u}} {z : SMT.𝒱}
    {alpha beta : SMTType} {body : SMT.Term} {lamVal : SMT.Dom.{u}}
    (hcov_lambda : SMT.RenamingContext.CoversFV Delta
      ((λˢ [z]) [alpha] body))
    (hlamVal : ⟦((λˢ [z]) [alpha] body).abstract Delta hcov_lambda⟧ˢ =
      some lamVal)
    (hlamVal_func : ⟦alpha⟧ᶻ.IsFunc ⟦beta⟧ᶻ lamVal.fst)
    {W bodyVal : SMT.Dom.{u}}
    (hW_type : W.snd.fst = alpha)
    (hW_mem : W.fst ∈ ⟦alpha⟧ᶻ)
    (hcov_body : SMT.RenamingContext.CoversFV
      (Function.update Delta z (some W)) body)
    (hden_body : ⟦body.abstract (Function.update Delta z (some W))
      hcov_body⟧ˢ = some bodyVal) :
    (ZFSet.fapply lamVal.fst (ZFSet.is_func_is_pfunc hlamVal_func)
      ⟨W.fst, by
        rw [ZFSet.is_func_dom_eq hlamVal_func]
        exact hW_mem⟩).val = bodyVal.fst := by
  have hW_normalized : W = ⟨W.fst, alpha,
      by simpa [hW_type] using W.snd.snd⟩ := by
    rcases W with ⟨Wval, Wtype, hWval⟩
    dsimp at hW_type ⊢
    subst Wtype
    rfl
  have hgo_cov : ∀ x ∈ SMT.fv body, x ∉ [z] → (Delta x).isSome = true := by
    intro x hx hxz
    exact hcov_lambda x (SMT.fv.mem_lambda ⟨hx, hxz⟩)
  have hcov_body_upd : ∀ W : SMT.Dom,
      SMT.RenamingContext.CoversFV (Function.update Delta z (some W)) body := by
    intro W x hx
    by_cases hxz : x = z
    · subst x
      simp [Function.update]
    · rw [Function.update_of_ne hxz]
      exact hgo_cov x hx (by simp [hxz])
  have hden_body_upd : ⟦body.abstract (Function.update Delta z (some W))
      (hcov_body_upd W)⟧ˢ = some bodyVal := by
    rw [SMT.RenamingContext.denote_abstract_proof_irrel body
      (Function.update Delta z (some W)) hcov_body (hcov_body_upd W)]
    exact hden_body
  have hlamVal' := hlamVal
  rw [SMT.Term.abstract, dif_pos (by rfl)] at hlamVal'
  simp only [SMT.denote] at hlamVal'
  rw [dif_pos (show [z].length > 0 by exact Nat.zero_lt_succ 0)] at hlamVal'
  split_ifs at hlamVal' with h_isSome h_typ_det
  · let xW : Fin 1 → SMT.Dom := fun _ => W
    have hxW_spec : ∀ i, (xW i).snd.fst = [alpha][↑i] ∧
        (xW i).fst ∈ ⟦[alpha][↑i]⟧ᶻ := by
      intro ⟨i, hi⟩
      simp only [Nat.lt_one_iff] at hi
      subst hi
      exact ⟨hW_type, hW_mem⟩
    have hgo_W := funAbstractGoSingle (Δctx := Delta) (P := body) (v := z)
      (τ := alpha) hgo_cov hcov_body_upd xW hxW_spec
    have hden_W : ⟦(SMT.Term.abstract.go body [z] Delta hgo_cov).uncurry
        xW⟧ˢ = some bodyVal := by
      rw [hgo_W]
      exact hden_body_upd
    simp only [Option.pure_def, Option.some.injEq] at hlamVal'
    have hlamVal_fst_eq : lamVal.fst = _ := congrArg (·.fst) hlamVal'.symm
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.sub_self,
      Fin.foldr_zero, List.getElem_cons_zero] at hlamVal_fst_eq
    have h_pair_mem : W.fst.pair bodyVal.fst ∈ lamVal.fst := by
      rw [hlamVal_fst_eq, ZFSet.mem_lambda]
      refine ⟨W.fst, bodyVal.fst, rfl, hW_mem, ?_, ?_⟩
      · let xd : Fin 1 → SMT.Dom := fun _ =>
          ⟨alpha.defaultZFSet, alpha,
            SMTType.mem_toZFSet_of_defaultZFSet⟩
        have hxd_spec : ∀ i, (xd i).snd.fst = [alpha][↑i] ∧
            (xd i).fst ∈ ⟦[alpha][↑i]⟧ᶻ := by
          intro ⟨i, hi⟩
          simp only [Nat.lt_one_iff] at hi
          subst hi
          exact ⟨rfl, SMTType.mem_toZFSet_of_defaultZFSet⟩
        have hgamma := h_typ_det xW xd hxW_spec hxd_spec
        rw [congrArg (·.snd.fst) (Option.get_of_eq_some _ hden_W)] at hgamma
        exact hgamma ▸ bodyVal.snd.snd
      · split_ifs with hW_cond
        · let xW' := fun i : Fin 1 =>
            (⟨W.fst.get 1 i, [alpha][↑i], hW_cond.2 i⟩ : SMT.Dom)
          have hgo' := funAbstractGoSingle (Δctx := Delta) (P := body) (v := z)
            (τ := alpha) hgo_cov hcov_body_upd xW'
              (fun i => ⟨rfl, hW_cond.2 i⟩)
          have hxW'_eq : xW' ⟨0, Nat.zero_lt_one⟩ = W := by
            rw [hW_normalized]
            rfl
          have hden' : ⟦(SMT.Term.abstract.go body [z] Delta hgo_cov).uncurry
              xW'⟧ˢ = some bodyVal := by
            rw [hgo', hxW'_eq]
            exact hden_body_upd
          exact (congrArg (·.fst) (Option.get_of_eq_some _ hden')).symm
        · exfalso
          apply hW_cond
          exact ⟨trivial, fun ⟨i, hi⟩ => by
            have hi' : i = 0 := Nat.lt_one_iff.mp hi
            subst hi'
            exact hW_mem⟩
    have h_fapply := ZFSet.fapply.of_pair
      (ZFSet.is_func_is_pfunc hlamVal_func) h_pair_mem
    rw [Subtype.ext_iff] at h_fapply
    exact h_fapply

/-- If the collection-domain application is true, the generated `ite` has the
same truth value as its substituted predicate branch. -/
theorem collect_ite_truth_of_true_domain.{u}
    {Dapp Psub body : SMT.Term} {Theta : SMT.RenamingContext.Context.{u}}
    (hbody_def : body = Dapp.ite Psub (.bool false))
    (hcov_body : SMT.RenamingContext.CoversFV Theta body)
    (hcov_Dapp : SMT.RenamingContext.CoversFV Theta Dapp)
    (hcov_Psub : SMT.RenamingContext.CoversFV Theta Psub)
    {dD dP dBody : SMT.Dom.{u}}
    (hden_Dapp : ⟦Dapp.abstract Theta hcov_Dapp⟧ˢ = some dD)
    (hden_Psub : ⟦Psub.abstract Theta hcov_Psub⟧ˢ = some dP)
    (hden_body : ⟦body.abstract Theta hcov_body⟧ˢ = some dBody)
    (hD_type : dD.snd.fst = SMTType.bool)
    (hD_true : dD.fst = ZFSet.zftrue) :
    dBody = dP := by
  rcases dD with ⟨Dval, sigmaD, hD_mem⟩
  dsimp at hD_type hD_true
  subst sigmaD
  subst body
  rw [SMT.Term.abstract, SMT.denote, Option.bind_eq_bind] at hden_body
  conv at hden_body =>
    lhs
    rw [SMT.RenamingContext.denote_abstract_proof_irrel Dapp Theta _ hcov_Dapp]
  rw [hden_Dapp] at hden_body
  simp only [Option.bind_some] at hden_body
  have hD_bool : ZFSet.ZFBool.toBool ⟨Dval, hD_mem⟩ = true := by
    rw [show (⟨Dval, hD_mem⟩ : ZFSet.ZFBool) =
      ⟨ZFSet.zftrue, ZFSet.ZFBool.zftrue_mem_𝔹⟩ from Subtype.ext hD_true]
    exact ZFSet.ZFBool.toBool_true
  rw [show ZFSet.ZFBool.toBool ⟨Dval, _⟩ = true from by
    convert hD_bool] at hden_body
  simp only [ite_true] at hden_body
  conv at hden_body =>
    lhs
    rw [SMT.RenamingContext.denote_abstract_proof_irrel Psub Theta _ hcov_Psub]
  rw [hden_Psub] at hden_body
  exact Option.some.inj hden_body.symm

/-- The full collection-body bridge: once the represented predicate body is
transported through its binder substitution, a true domain application makes
the generated `ite` true exactly when the B predicate is true. -/
theorem collect_ite_truth_of_represented_subst.{u}
    {Dapp Penc body : SMT.Term}
    (xs : List SMT.𝒱) (ts : List SMT.Term)
    {Delta ThetaBody : SMT.RenamingContext.Context.{u}}
    (Ds : List SMT.Dom.{u})
    (hbody_def : body = Dapp.ite (SMT.substList xs ts Penc) (.bool false))
    (hcov_body : SMT.RenamingContext.CoversFV Delta body)
    (hcov_Dapp : SMT.RenamingContext.CoversFV Delta Dapp)
    (hlen_xt : xs.length = ts.length) (hlen_xd : xs.length = Ds.length)
    (hnodup : xs.Nodup)
    (hxs_not_bv : ∀ x ∈ xs, x ∉ SMT.bv Penc)
    (hts_bv_nil : ∀ t ∈ ts, SMT.bv t = [])
    (hts_fv_not_bv : ∀ t ∈ ts, ∀ w ∈ SMT.fv t, w ∉ SMT.bv Penc)
    (hts_not_none : ∀ t ∈ ts, t ≠ SMT.Term.none)
    (hts_fv_disj_xs : ∀ t ∈ ts, ∀ w ∈ SMT.fv t, w ∉ xs)
    (hts_den : ∀ (i : ℕ) (_hi_x : i < xs.length) (hi_t : i < ts.length)
      (hi_d : i < Ds.length),
      ∃ (ht_cov : SMT.RenamingContext.CoversFV Delta ts[i]),
        ⟦ts[i].abstract Delta ht_cov⟧ˢ = some Ds[i])
    (hcov_sub : SMT.RenamingContext.CoversFV Delta
      (SMT.substList xs ts Penc))
    (hcov_upd : SMT.RenamingContext.CoversFV
      (Function.updates Delta xs (Ds.map Option.some)) Penc)
    (hcov_body_P : SMT.RenamingContext.CoversFV ThetaBody Penc)
    (hagrees : SMT.RenamingContext.AgreesOnFV
      (Function.updates Delta xs (Ds.map Option.some)) ThetaBody Penc)
    {P : ZFSet.{u}} {hP : P ∈ ⟦BType.bool⟧ᶻ}
    {dP : SMT.Dom.{u}}
    (hden_P : ⟦Penc.abstract ThetaBody hcov_body_P⟧ˢ = some dP)
    (hrel_P : RDomCastSupported
      (⟨P, BType.bool, hP⟩ : B.Dom) dP)
    {dD dBody : SMT.Dom.{u}}
    (hden_D : ⟦Dapp.abstract Delta hcov_Dapp⟧ˢ = some dD)
    (hden_body : ⟦body.abstract Delta hcov_body⟧ˢ = some dBody)
    (hD_type : dD.snd.fst = SMTType.bool)
    (hD_true : dD.fst = ZFSet.zftrue) :
    dBody.fst = ZFSet.zftrue ↔ P = ZFSet.zftrue := by
  obtain ⟨hden_sub, htruth_sub⟩ :=
    SMT.RenamingContext.denote_substList_bool_truth_of_agrees
      Penc xs ts Ds hlen_xt hlen_xd hnodup hxs_not_bv hts_bv_nil
      hts_fv_not_bv hts_not_none hts_fv_disj_xs hts_den hcov_sub
      hcov_upd hcov_body_P hagrees hden_P hrel_P
  have hbody_eq := collect_ite_truth_of_true_domain hbody_def hcov_body
    hcov_Dapp hcov_sub hden_D hden_sub hden_body hD_type hD_true
  rw [hbody_eq]
  exact htruth_sub

/-- Collection-body truth from source-level agreement.  This is the form
consumed by the operational `collect` proof after its body IH supplies the
bound-variable denotations and the stable-body free-variable bound. -/
theorem collect_ite_truth_of_represented_source_fv.{u}
    {Dapp Penc body : SMT.Term}
    (xs : List SMT.𝒱) (ts : List SMT.Term)
    {Delta ThetaBase ThetaBody : SMT.RenamingContext.Context.{u}}
    (Ds : List SMT.Dom.{u}) {source : B.Term}
    (hbody_def : body = Dapp.ite (SMT.substList xs ts Penc) (.bool false))
    (hcov_body : SMT.RenamingContext.CoversFV Delta body)
    (hcov_Dapp : SMT.RenamingContext.CoversFV Delta Dapp)
    (hlen_xt : xs.length = ts.length) (hlen_xd : xs.length = Ds.length)
    (hnodup : xs.Nodup)
    (hxs_not_bv : ∀ x ∈ xs, x ∉ SMT.bv Penc)
    (hts_bv_nil : ∀ t ∈ ts, SMT.bv t = [])
    (hts_fv_not_bv : ∀ t ∈ ts, ∀ w ∈ SMT.fv t, w ∉ SMT.bv Penc)
    (hts_not_none : ∀ t ∈ ts, t ≠ SMT.Term.none)
    (hts_fv_disj_xs : ∀ t ∈ ts, ∀ w ∈ SMT.fv t, w ∉ xs)
    (hts_den : ∀ (i : ℕ) (_hi_x : i < xs.length) (hi_t : i < ts.length)
      (hi_d : i < Ds.length),
      ∃ (ht_cov : SMT.RenamingContext.CoversFV Delta ts[i]),
        ⟦ts[i].abstract Delta ht_cov⟧ˢ = some Ds[i])
    (hcov_sub : SMT.RenamingContext.CoversFV Delta
      (SMT.substList xs ts Penc))
    (hcov_upd : SMT.RenamingContext.CoversFV
      (Function.updates Delta xs (Ds.map Option.some)) Penc)
    (hcov_body_P : SMT.RenamingContext.CoversFV ThetaBody Penc)
    (hvalues : ∀ (i : ℕ) (hi_x : i < xs.length) (hi_d : i < Ds.length),
      ThetaBody xs[i] = some Ds[i])
    (hPenc_fv : SMT.fv Penc ⊆ B.Term.vars source)
    (hctx_source : ∀ v ∈ B.Term.vars source, v ∉ xs →
      Delta v = ThetaBase v)
    (hbody_ext : SMT.RenamingContext.Extends ThetaBody ThetaBase)
    {P : ZFSet.{u}} {hP : P ∈ ⟦BType.bool⟧ᶻ}
    {dP : SMT.Dom.{u}}
    (hden_P : ⟦Penc.abstract ThetaBody hcov_body_P⟧ˢ = some dP)
    (hrel_P : RDomCastSupported
      (⟨P, BType.bool, hP⟩ : B.Dom) dP)
    {dD dBody : SMT.Dom.{u}}
    (hden_D : ⟦Dapp.abstract Delta hcov_Dapp⟧ˢ = some dD)
    (hden_body : ⟦body.abstract Delta hcov_body⟧ˢ = some dBody)
    (hD_type : dD.snd.fst = SMTType.bool)
    (hD_true : dD.fst = ZFSet.zftrue) :
    dBody.fst = ZFSet.zftrue ↔ P = ZFSet.zftrue := by
  exact collect_ite_truth_of_represented_subst
    xs ts Ds hbody_def hcov_body hcov_Dapp hlen_xt hlen_xd hnodup
    hxs_not_bv hts_bv_nil hts_fv_not_bv hts_not_none hts_fv_disj_xs
    hts_den hcov_sub hcov_upd hcov_body_P
    (SMT.RenamingContext.agreesOnFV_updates_of_source_fv
      hlen_xd hnodup hcov_upd hvalues hPenc_fv hctx_source hbody_ext)
    hden_P hrel_P hden_D hden_body hD_type hD_true

/-- The operational form of the represented collection-body bridge.  It runs
the predicate's representation-aware totality theorem at the supplied bound
values, then applies the stable-free-variable substitution bridge.  In
particular, no equality with `B.RenamingContext.toSMT` is required. -/
theorem collect_ite_truth_of_total_body_source_fv.{u}
    {Dapp Penc body : SMT.Term}
    (xs : List SMT.𝒱) (ts : List SMT.Term)
    {Delta ThetaBase : SMT.RenamingContext.Context.{u}}
    (Ds : List SMT.Dom.{u})
    (hbody_def : body = Dapp.ite (SMT.substList xs ts Penc) (.bool false))
    (hcov_body : SMT.RenamingContext.CoversFV Delta body)
    (hcov_Dapp : SMT.RenamingContext.CoversFV Delta Dapp)
    (hlen_xt : xs.length = ts.length) (hlen_xd : xs.length = Ds.length)
    (hnodup : xs.Nodup)
    (hxs_not_bv : ∀ x ∈ xs, x ∉ SMT.bv Penc)
    (hts_bv_nil : ∀ t ∈ ts, SMT.bv t = [])
    (hts_fv_not_bv : ∀ t ∈ ts, ∀ w ∈ SMT.fv t, w ∉ SMT.bv Penc)
    (hts_not_none : ∀ t ∈ ts, t ≠ SMT.Term.none)
    (hts_fv_disj_xs : ∀ t ∈ ts, ∀ w ∈ SMT.fv t, w ∉ xs)
    (hts_den : ∀ (i : ℕ) (_hi_x : i < xs.length) (hi_t : i < ts.length)
      (hi_d : i < Ds.length),
      ∃ (ht_cov : SMT.RenamingContext.CoversFV Delta ts[i]),
        ⟦ts[i].abstract Delta ht_cov⟧ˢ = some Ds[i])
    (hcov_sub : SMT.RenamingContext.CoversFV Delta
      (SMT.substList xs ts Penc))
    (hcov_upd : SMT.RenamingContext.CoversFV
      (Function.updates Delta xs (Ds.map Option.some)) Penc)
    {Pterm : B.Term} {E : B.Env} {Lambda Gamma : SMT.TypeContext}
    {sigma : SMTType} {used : List SMT.𝒱}
    (P_total : EncodeTermRepTotal.{u}
      Pterm E BType.bool Lambda Penc sigma Gamma used)
    {Xi : B.RenamingContext.Context.{u}}
    (Xi_fv : ∀ v ∈ B.fv Pterm, (Xi v).isSome = true)
    (related : RValuationCastSupportedOnFV Xi ThetaBase Pterm)
    (wf : B.RenWF E.context Xi)
    (ThetaBase_none : ∀ v ∉ used, ThetaBase v = none)
    (source_respects : B.RenamingContext.RespectsTypeContextOnFV
      ThetaBase Lambda Pterm)
    (ThetaBase_dom : ∀ v, ThetaBase v ≠ none → v ∈ Lambda)
    {Pval : ZFSet.{u}} {hPval : Pval ∈ ⟦BType.bool⟧ᶻ}
    (den_P : ⟦Pterm.abstract Xi Xi_fv⟧ᴮ =
      some (⟨Pval, BType.bool, hPval⟩ : B.Dom))
    (bound_values : ∀ (i : ℕ) (hi_x : i < xs.length) (hi_d : i < Ds.length),
      ThetaBase xs[i] = some Ds[i])
    (hPenc_fv : SMT.fv Penc ⊆ B.Term.vars Pterm)
    (hctx_source : ∀ v ∈ B.Term.vars Pterm, v ∉ xs →
      Delta v = ThetaBase v)
    {dD dBody : SMT.Dom.{u}}
    (hden_D : ⟦Dapp.abstract Delta hcov_Dapp⟧ˢ = some dD)
    (hden_body : ⟦body.abstract Delta hcov_body⟧ˢ = some dBody)
    (hD_type : dD.snd.fst = SMTType.bool)
    (hD_true : dD.fst = ZFSet.zftrue) :
    dBody.fst = ZFSet.zftrue ↔ Pval = ZFSet.zftrue := by
  obtain ⟨ThetaBody, hcov_P, dP, hbody_ext, hvalues, hbody_rel,
    _hbody_none, _source_respects, _target_respects, _hbody_dom,
    hden_P, _hdP_type, hrel_P⟩ :=
    EncodeTermRepTotal.bound_body P_total Xi_fv related wf ThetaBase_none
      source_respects ThetaBase_dom den_P bound_values
  exact collect_ite_truth_of_represented_source_fv
    xs ts Ds hbody_def hcov_body hcov_Dapp hlen_xt hlen_xd hnodup
    hxs_not_bv hts_bv_nil hts_fv_not_bv hts_not_none hts_fv_disj_xs
    hts_den hcov_sub hcov_upd hcov_P hvalues hPenc_fv hctx_source
    hbody_ext hden_P hrel_P hden_D hden_body hD_type hD_true

/-- The fresh-variable form of the collection-body bridge.  The collection
encoder creates `z` only after encoding the predicate, so predicate totality
must run in the pre-`z` valuation.  Its result is then safely lifted across
the fresh update before comparing the substituted body. -/
theorem collect_ite_truth_of_total_body_source_fv_fresh.{u}
    {Dapp Penc body : SMT.Term}
    (xs : List SMT.𝒱) (ts : List SMT.Term)
    {DeltaCtx ThetaBase : SMT.RenamingContext.Context.{u}}
    {z : SMT.𝒱} {W : SMT.Dom.{u}}
    (Ds : List SMT.Dom.{u})
    (hbody_def : body = Dapp.ite (SMT.substList xs ts Penc) (.bool false))
    (hcov_body : SMT.RenamingContext.CoversFV
      (Function.update DeltaCtx z (some W)) body)
    (hcov_Dapp : SMT.RenamingContext.CoversFV
      (Function.update DeltaCtx z (some W)) Dapp)
    (hlen_xt : xs.length = ts.length) (hlen_xd : xs.length = Ds.length)
    (hnodup : xs.Nodup)
    (hxs_not_bv : ∀ x ∈ xs, x ∉ SMT.bv Penc)
    (hts_bv_nil : ∀ t ∈ ts, SMT.bv t = [])
    (hts_fv_not_bv : ∀ t ∈ ts, ∀ w ∈ SMT.fv t, w ∉ SMT.bv Penc)
    (hts_not_none : ∀ t ∈ ts, t ≠ SMT.Term.none)
    (hts_fv_disj_xs : ∀ t ∈ ts, ∀ w ∈ SMT.fv t, w ∉ xs)
    (hts_den : ∀ (i : ℕ) (_hi_x : i < xs.length) (hi_t : i < ts.length)
      (hi_d : i < Ds.length),
      ∃ (ht_cov : SMT.RenamingContext.CoversFV
          (Function.update DeltaCtx z (some W)) ts[i]),
        ⟦ts[i].abstract (Function.update DeltaCtx z (some W)) ht_cov⟧ˢ =
          some Ds[i])
    (hcov_sub : SMT.RenamingContext.CoversFV
      (Function.update DeltaCtx z (some W))
        (SMT.substList xs ts Penc))
    (hcov_upd : SMT.RenamingContext.CoversFV
      (Function.updates (Function.update DeltaCtx z (some W)) xs
        (Ds.map Option.some)) Penc)
    {Pterm : B.Term} {E : B.Env} {Lambda Gamma : SMT.TypeContext}
    {sigma : SMTType} {used : List SMT.𝒱}
    (P_total : EncodeTermRepTotal.{u}
      Pterm E BType.bool Lambda Penc sigma Gamma used)
    {Xi : B.RenamingContext.Context.{u}}
    (Xi_fv : ∀ v ∈ B.fv Pterm, (Xi v).isSome = true)
    (related : RValuationCastSupportedOnFV Xi ThetaBase Pterm)
    (wf : B.RenWF E.context Xi)
    (ThetaBase_none : ∀ v ∉ used, ThetaBase v = none)
    (source_respects : B.RenamingContext.RespectsTypeContextOnFV
      ThetaBase Lambda Pterm)
    (ThetaBase_dom : ∀ v, ThetaBase v ≠ none → v ∈ Lambda)
    {Pval : ZFSet.{u}} {hPval : Pval ∈ ⟦BType.bool⟧ᶻ}
    (den_P : ⟦Pterm.abstract Xi Xi_fv⟧ᴮ =
      some (⟨Pval, BType.bool, hPval⟩ : B.Dom))
    (bound_values : ∀ (i : ℕ) (hi_x : i < xs.length) (hi_d : i < Ds.length),
      ThetaBase xs[i] = some Ds[i])
    (hPenc_fv : SMT.fv Penc ⊆ B.Term.vars Pterm)
    (z_not_xs : z ∉ xs)
    (z_not_fv_Penc : z ∉ SMT.fv Penc)
    (z_not_vars_source : z ∉ B.Term.vars Pterm)
    (hctx_source : ∀ v ∈ B.Term.vars Pterm, v ∉ xs →
      DeltaCtx v = ThetaBase v)
    {dD dBody : SMT.Dom.{u}}
    (hden_D : ⟦Dapp.abstract (Function.update DeltaCtx z (some W))
      hcov_Dapp⟧ˢ = some dD)
    (hden_body : ⟦body.abstract (Function.update DeltaCtx z (some W))
      hcov_body⟧ˢ = some dBody)
    (hD_type : dD.snd.fst = SMTType.bool)
    (hD_true : dD.fst = ZFSet.zftrue) :
    dBody.fst = ZFSet.zftrue ↔ Pval = ZFSet.zftrue := by
  obtain ⟨ThetaBody, hcov_P, dP, hbody_ext, hvalues, _hbody_rel,
    _hbody_none, _source_respects, _target_respects, _hbody_dom,
    hden_P, _hdP_type, hrel_P⟩ :=
    EncodeTermRepTotal.bound_body P_total Xi_fv related wf ThetaBase_none
      source_respects ThetaBase_dom den_P bound_values
  have hcov_P_upd : SMT.RenamingContext.CoversFV
      (Function.update ThetaBody z (some W)) Penc :=
    SMT.RenamingContext.coversFV_update_of_notMem z_not_fv_Penc hcov_P
  have hden_P_upd : ⟦Penc.abstract (Function.update ThetaBody z (some W))
      hcov_P_upd⟧ˢ = some dP := by
    calc
      ⟦Penc.abstract (Function.update ThetaBody z (some W)) hcov_P_upd⟧ˢ =
          ⟦Penc.abstract ThetaBody hcov_P⟧ˢ := by
        symm
        exact SMT.RenamingContext.denote_update_of_notMem (h := hcov_P)
          z_not_fv_Penc
      _ = some dP := hden_P
  have hvalues_upd : ∀ (i : ℕ) (hi_x : i < xs.length)
      (hi_d : i < Ds.length),
      (Function.update ThetaBody z (some W)) xs[i] = some Ds[i] := by
    intro i hi_x hi_d
    have hxz : xs[i] ≠ z := by
      intro h
      apply z_not_xs
      rw [← h]
      exact List.getElem_mem hi_x
    rw [Function.update_of_ne hxz]
    exact hvalues i hi_x hi_d
  have hbody_ext_upd : SMT.RenamingContext.Extends
      (Function.update ThetaBody z (some W))
      (Function.update ThetaBase z (some W)) := by
    intro v d hv
    by_cases hvz : v = z
    · subst v
      simpa using hv
    · rw [Function.update_of_ne hvz]
      apply hbody_ext
      rw [Function.update_of_ne hvz] at hv
      exact hv
  have hctx_source_upd : ∀ v ∈ B.Term.vars Pterm, v ∉ xs →
      (Function.update DeltaCtx z (some W)) v =
        (Function.update ThetaBase z (some W)) v := by
    intro v hv hvs
    have hvz : v ≠ z := by
      intro h
      subst v
      exact z_not_vars_source hv
    rw [Function.update_of_ne hvz, Function.update_of_ne hvz]
    exact hctx_source v hv hvs
  exact collect_ite_truth_of_represented_source_fv
    xs ts Ds hbody_def hcov_body hcov_Dapp hlen_xt hlen_xd hnodup
    hxs_not_bv hts_bv_nil hts_fv_not_bv hts_not_none hts_fv_disj_xs
    hts_den hcov_sub hcov_upd hcov_P_upd hvalues_upd hPenc_fv
    hctx_source_upd hbody_ext_upd hden_P_upd hrel_P hden_D hden_body
    hD_type hD_true

/-- Transport a represented Boolean predicate through an arbitrary binder
substitution after a fresh outer binder has been installed.  Unlike the
collection-set helper above, this lemma has no enclosing `ite`: it is the
form required by the option-function `collect` arm, whose domain test and
payload extraction are handled separately. -/
theorem collect_subst_truth_of_total_body_source_fv_fresh.{u}
    {Penc : SMT.Term}
    (xs : List SMT.𝒱) (ts : List SMT.Term)
    {DeltaCtx ThetaBase : SMT.RenamingContext.Context.{u}}
    {z : SMT.𝒱} {W : SMT.Dom.{u}}
    (Ds : List SMT.Dom.{u})
    (hlen_xt : xs.length = ts.length) (hlen_xd : xs.length = Ds.length)
    (hnodup : xs.Nodup)
    (hxs_not_bv : ∀ x ∈ xs, x ∉ SMT.bv Penc)
    (hts_bv_nil : ∀ t ∈ ts, SMT.bv t = [])
    (hts_fv_not_bv : ∀ t ∈ ts, ∀ w ∈ SMT.fv t, w ∉ SMT.bv Penc)
    (hts_not_none : ∀ t ∈ ts, t ≠ SMT.Term.none)
    (hts_fv_disj_xs : ∀ t ∈ ts, ∀ w ∈ SMT.fv t, w ∉ xs)
    (hts_den : ∀ (i : ℕ) (_hi_x : i < xs.length) (hi_t : i < ts.length)
      (hi_d : i < Ds.length),
      ∃ (ht_cov : SMT.RenamingContext.CoversFV
          (Function.update DeltaCtx z (some W)) ts[i]),
        ⟦ts[i].abstract (Function.update DeltaCtx z (some W)) ht_cov⟧ˢ =
          some Ds[i])
    (hcov_sub : SMT.RenamingContext.CoversFV
      (Function.update DeltaCtx z (some W))
        (SMT.substList xs ts Penc))
    (hcov_upd : SMT.RenamingContext.CoversFV
      (Function.updates (Function.update DeltaCtx z (some W)) xs
        (Ds.map Option.some)) Penc)
    {Pterm : B.Term} {E : B.Env} {Lambda Gamma : SMT.TypeContext}
    {sigma : SMTType} {used : List SMT.𝒱}
    (P_total : EncodeTermRepTotal.{u}
      Pterm E BType.bool Lambda Penc sigma Gamma used)
    {Xi : B.RenamingContext.Context.{u}}
    (Xi_fv : ∀ v ∈ B.fv Pterm, (Xi v).isSome = true)
    (related : RValuationCastSupportedOnFV Xi ThetaBase Pterm)
    (wf : B.RenWF E.context Xi)
    (ThetaBase_none : ∀ v ∉ used, ThetaBase v = none)
    (source_respects : B.RenamingContext.RespectsTypeContextOnFV
      ThetaBase Lambda Pterm)
    (ThetaBase_dom : ∀ v, ThetaBase v ≠ none → v ∈ Lambda)
    {Pval : ZFSet.{u}} {hPval : Pval ∈ ⟦BType.bool⟧ᶻ}
    (den_P : ⟦Pterm.abstract Xi Xi_fv⟧ᴮ =
      some (⟨Pval, BType.bool, hPval⟩ : B.Dom))
    (bound_values : ∀ (i : ℕ) (hi_x : i < xs.length) (hi_d : i < Ds.length),
      ThetaBase xs[i] = some Ds[i])
    (hPenc_fv : SMT.fv Penc ⊆ B.Term.vars Pterm)
    (z_not_xs : z ∉ xs)
    (z_not_fv_Penc : z ∉ SMT.fv Penc)
    (z_not_vars_source : z ∉ B.Term.vars Pterm)
    (hctx_source : ∀ v ∈ B.Term.vars Pterm, v ∉ xs →
      DeltaCtx v = ThetaBase v) :
    ∃ dP : SMT.Dom.{u},
      ⟦(SMT.substList xs ts Penc).abstract
        (Function.update DeltaCtx z (some W)) hcov_sub⟧ˢ = some dP ∧
      (dP.fst = ZFSet.zftrue ↔ Pval = ZFSet.zftrue) := by
  obtain ⟨ThetaBody, hcov_P, dP, hbody_ext, hvalues, _hbody_rel,
    _hbody_none, _source_respects, _target_respects, _hbody_dom,
    hden_P, _hdP_type, hrel_P⟩ :=
    EncodeTermRepTotal.bound_body P_total Xi_fv related wf ThetaBase_none
      source_respects ThetaBase_dom den_P bound_values
  have hcov_P_upd : SMT.RenamingContext.CoversFV
      (Function.update ThetaBody z (some W)) Penc :=
    SMT.RenamingContext.coversFV_update_of_notMem z_not_fv_Penc hcov_P
  have hden_P_upd : ⟦Penc.abstract (Function.update ThetaBody z (some W))
      hcov_P_upd⟧ˢ = some dP := by
    calc
      ⟦Penc.abstract (Function.update ThetaBody z (some W)) hcov_P_upd⟧ˢ =
          ⟦Penc.abstract ThetaBody hcov_P⟧ˢ := by
        symm
        exact SMT.RenamingContext.denote_update_of_notMem (h := hcov_P)
          z_not_fv_Penc
      _ = some dP := hden_P
  have hvalues_upd : ∀ (i : ℕ) (hi_x : i < xs.length)
      (hi_d : i < Ds.length),
      (Function.update ThetaBody z (some W)) xs[i] = some Ds[i] := by
    intro i hi_x hi_d
    have hxz : xs[i] ≠ z := by
      intro h
      apply z_not_xs
      rw [← h]
      exact List.getElem_mem hi_x
    rw [Function.update_of_ne hxz]
    exact hvalues i hi_x hi_d
  have hbody_ext_upd : SMT.RenamingContext.Extends
      (Function.update ThetaBody z (some W))
      (Function.update ThetaBase z (some W)) := by
    intro v d hv
    by_cases hvz : v = z
    · subst v
      simpa using hv
    · rw [Function.update_of_ne hvz]
      apply hbody_ext
      rw [Function.update_of_ne hvz] at hv
      exact hv
  have hctx_source_upd : ∀ v ∈ B.Term.vars Pterm, v ∉ xs →
      (Function.update DeltaCtx z (some W)) v =
        (Function.update ThetaBase z (some W)) v := by
    intro v hv hvs
    have hvz : v ≠ z := by
      intro h
      subst v
      exact z_not_vars_source hv
    rw [Function.update_of_ne hvz, Function.update_of_ne hvz]
    exact hctx_source v hv hvs
  have hagrees : SMT.RenamingContext.AgreesOnFV
      (Function.updates (Function.update DeltaCtx z (some W)) xs
        (Ds.map Option.some))
      (Function.update ThetaBody z (some W)) Penc :=
    SMT.RenamingContext.agreesOnFV_updates_of_source_fv
      hlen_xd hnodup hcov_upd hvalues_upd hPenc_fv hctx_source_upd
      hbody_ext_upd
  obtain ⟨hden_sub, htruth_sub⟩ :=
    SMT.RenamingContext.denote_substList_bool_truth_of_agrees
      Penc xs ts Ds hlen_xt hlen_xd hnodup hxs_not_bv hts_bv_nil
      hts_fv_not_bv hts_not_none hts_fv_disj_xs hts_den hcov_sub
      hcov_upd hcov_P_upd hagrees hden_P_upd hrel_P
  exact ⟨dP, hden_sub, htruth_sub⟩

/-- Specialize the represented collection-body bridge to the tuple projections
emitted by the encoder.  This packages the routine length, freshness, and
denotation facts for `toDestPair`, leaving callers with the semantic data for
the dynamically chosen binder values. -/
theorem collect_ite_truth_of_total_body_toDestPair.{u}
    {Dapp Penc body : SMT.Term}
    {vs : List SMT.𝒱} (vs_nemp : vs ≠ []) (vs_nodup : vs.Nodup)
    {z : SMT.𝒱}
    {DeltaCtx ThetaBase : SMT.RenamingContext.Context.{u}} {W : SMT.Dom.{u}}
    {ss : Fin vs.length → SMT.Dom.{u}}
    (hbody_def : body = Dapp.ite
      (SMT.substList vs (toDestPair vs (.var z)) Penc) (.bool false))
    (hcov_body : SMT.RenamingContext.CoversFV
      (Function.update DeltaCtx z (some W)) body)
    (hcov_Dapp : SMT.RenamingContext.CoversFV
      (Function.update DeltaCtx z (some W)) Dapp)
    (hcov_sub : SMT.RenamingContext.CoversFV
      (Function.update DeltaCtx z (some W))
      (SMT.substList vs (toDestPair vs (.var z)) Penc))
    (hcov_upd : SMT.RenamingContext.CoversFV
      (Function.updates (Function.update DeltaCtx z (some W)) vs
        ((List.ofFn ss).map Option.some)) Penc)
    (hvs_not_bv : ∀ v ∈ vs, v ∉ SMT.bv Penc)
    (hz_not_bv : z ∉ SMT.bv Penc)
    (hz_not_vs : z ∉ vs)
    (hcomponents : ∀ i : Fin vs.length,
      ∃ hcov : SMT.RenamingContext.CoversFV
          (Function.update DeltaCtx z (some W))
          ((toDestPair vs (.var z))[i.val]'(by
            rw [toDestPair_length_gen vs (.var z) (.var z) [] vs_nemp]
            exact i.isLt)),
        ⟦((toDestPair vs (.var z))[i.val]'(by
          rw [toDestPair_length_gen vs (.var z) (.var z) [] vs_nemp]
          exact i.isLt)).abstract (Function.update DeltaCtx z (some W))
            hcov⟧ˢ = some (ss i))
    {Pterm : B.Term} {E : B.Env} {Lambda Gamma : SMT.TypeContext}
    {sigma : SMTType} {used : List SMT.𝒱}
    (P_total : EncodeTermRepTotal.{u}
      Pterm E BType.bool Lambda Penc sigma Gamma used)
    {Xi : B.RenamingContext.Context.{u}}
    (Xi_fv : ∀ v ∈ B.fv Pterm, (Xi v).isSome = true)
    (related : RValuationCastSupportedOnFV Xi ThetaBase Pterm)
    (wf : B.RenWF E.context Xi)
    (ThetaBase_none : ∀ v ∉ used, ThetaBase v = none)
    (source_respects : B.RenamingContext.RespectsTypeContextOnFV
      ThetaBase Lambda Pterm)
    (ThetaBase_dom : ∀ v, ThetaBase v ≠ none → v ∈ Lambda)
    {Pval : ZFSet.{u}} {hPval : Pval ∈ ⟦BType.bool⟧ᶻ}
    (den_P : ⟦Pterm.abstract Xi Xi_fv⟧ᴮ =
      some (⟨Pval, BType.bool, hPval⟩ : B.Dom))
    (bound_values : ∀ (i : ℕ) (hi_x : i < vs.length)
      (_hi_d : i < (List.ofFn ss).length),
      ThetaBase vs[i] = some (ss ⟨i, hi_x⟩))
    (hPenc_fv : SMT.fv Penc ⊆ B.Term.vars Pterm)
    (z_not_vars_Pterm : z ∉ B.Term.vars Pterm)
    (hctx_source : ∀ v ∈ B.Term.vars Pterm, v ∉ vs →
      DeltaCtx v = ThetaBase v)
    {dD dBody : SMT.Dom.{u}}
    (hden_D : ⟦Dapp.abstract (Function.update DeltaCtx z (some W))
      hcov_Dapp⟧ˢ = some dD)
    (hden_body : ⟦body.abstract (Function.update DeltaCtx z (some W))
      hcov_body⟧ˢ = some dBody)
    (hD_type : dD.snd.fst = SMTType.bool)
    (hD_true : dD.fst = ZFSet.zftrue) :
    dBody.fst = ZFSet.zftrue ↔ Pval = ZFSet.zftrue := by
  have hlen_xt : vs.length = (toDestPair vs (.var z)).length := by
    rw [toDestPair_length_gen vs (.var z) (.var z) [] vs_nemp]
    simp
  have hlen_xd : vs.length = (List.ofFn ss).length := by simp
  have hbound_values : ∀ (i : ℕ) (hi_x : i < vs.length)
      (hi_d : i < (List.ofFn ss).length),
      ThetaBase vs[i] = some (List.ofFn ss)[i] := by
    intro i hi_x hi_d
    simpa only [List.getElem_ofFn, Fin.getElem_fin] using
      bound_values i hi_x hi_d
  have hts_fv_not_bv : ∀ t ∈ toDestPair vs (.var z),
      ∀ w ∈ SMT.fv t, w ∉ SMT.bv Penc := by
    intro t ht w hw
    rw [SMT_fv_toDestPair_subset ht hw]
    exact hz_not_bv
  have hts_fv_disj_xs : ∀ t ∈ toDestPair vs (.var z),
      ∀ w ∈ SMT.fv t, w ∉ vs := by
    intro t ht w hw
    rw [SMT_fv_toDestPair_subset ht hw]
    exact hz_not_vs
  have hts_den : ∀ (i : ℕ) (_hi_x : i < vs.length)
      (hi_t : i < (toDestPair vs (.var z)).length)
      (hi_d : i < (List.ofFn ss).length),
      ∃ (ht_cov : SMT.RenamingContext.CoversFV
          (Function.update DeltaCtx z (some W))
          (toDestPair vs (.var z))[i]),
        ⟦(toDestPair vs (.var z))[i].abstract
          (Function.update DeltaCtx z (some W)) ht_cov⟧ˢ =
            some (List.ofFn ss)[i] := by
    intro i hi_x _hi_t _hi_d
    let j : Fin vs.length := ⟨i, hi_x⟩
    obtain ⟨hcov, hden⟩ := hcomponents j
    refine ⟨hcov, ?_⟩
    simpa [j] using hden
  have hz_not_fv_Penc : z ∉ SMT.fv Penc := by
    intro hz
    exact z_not_vars_Pterm (hPenc_fv hz)
  exact collect_ite_truth_of_total_body_source_fv_fresh
    (xs := vs) (ts := toDestPair vs (.var z)) (Ds := List.ofFn ss)
    (DeltaCtx := DeltaCtx) (ThetaBase := ThetaBase) (z := z) (W := W)
    (Pterm := Pterm) (E := E) (Lambda := Lambda) (Gamma := Gamma)
    (sigma := sigma) (used := used) (P_total := P_total)
    (Xi := Xi) (Xi_fv := Xi_fv) (related := related) (wf := wf)
    (ThetaBase_none := ThetaBase_none)
    (source_respects := source_respects) (ThetaBase_dom := ThetaBase_dom)
    (Pval := Pval) (hPval := hPval) (den_P := den_P)
    (bound_values := hbound_values) (hPenc_fv := hPenc_fv)
    (z_not_xs := hz_not_vs) (z_not_fv_Penc := hz_not_fv_Penc)
    (z_not_vars_source := z_not_vars_Pterm) (hctx_source := hctx_source)
    (dD := dD) (dBody := dBody)
    (hden_D := hden_D) (hden_body := hden_body)
    (hD_type := hD_type) (hD_true := hD_true)
    (hbody_def := hbody_def) (hcov_body := hcov_body)
    (hcov_Dapp := hcov_Dapp) (hcov_sub := hcov_sub)
    (hcov_upd := hcov_upd) (hlen_xt := hlen_xt) (hlen_xd := hlen_xd)
    (hnodup := vs_nodup) (hxs_not_bv := hvs_not_bv)
    (hts_bv_nil := toDestPair_bv_nil) (hts_fv_not_bv := hts_fv_not_bv)
    (hts_not_none := toDestPair_ne_none) (hts_fv_disj_xs := hts_fv_disj_xs)
    (hts_den := hts_den)

/-- A fixed Boolean B denotation is equivalent to the extensional truth
form required by the collection retraction lemma.  The latter quantifies over
all dependent-pair presentations of the same `Option B.Dom`; injectivity of
`some` identifies their underlying values. -/
theorem B.denote_bool_true_iff_forall.{u}
    {e : Option B.Dom.{u}} {P : ZFSet.{u}}
    {hP : P ∈ ⟦BType.bool⟧ᶻ}
    (hden : e = some (⟨P, BType.bool, hP⟩ : B.Dom)) :
    P = ZFSet.zftrue ↔
      ∀ (Px : ZFSet.{u}) (P_ty : BType) (hPx : Px ∈ ⟦P_ty⟧ᶻ),
        e = some (⟨Px, P_ty, hPx⟩ : B.Dom) → Px = ZFSet.zftrue := by
  constructor
  · intro htrue Px P_ty hPx hden'
    have heq : (⟨P, BType.bool, hP⟩ : B.Dom) =
        ⟨Px, P_ty, hPx⟩ :=
      Option.some.inj (hden.symm.trans hden')
    have hvalue : P = Px := congrArg PSigma.fst heq
    rw [← hvalue]
    exact htrue
  · intro h
    exact h P BType.bool hP hden

/-- Convert a pointwise Boolean body bridge into the extensional bridge used
by `retract_lamVal_eq_collect`.  The pointwise form is what the
representation-aware predicate totality theorem produces; the target form
quantifies over all dependent presentations of the source Boolean result. -/
theorem collect_hbridge_of_pointwise_bool.{u}
    {vs : List B.𝒱} {D P : B.Term} {tau : BType}
    {Dval : ZFSet.{u}}
    {Xi : B.RenamingContext.Context.{u}}
    (Xi_fv : ∀ v ∈ B.fv (B.Term.collect vs D P), (Xi v).isSome = true)
    {Delta : SMT.RenamingContext.Context.{u}} {z : SMT.𝒱}
    {ite_body : SMT.Term}
    (tau_hasArity : tau.hasArity vs.length)
    (hcov_ite_upd : ∀ W : SMT.Dom,
      SMT.RenamingContext.CoversFV (Function.update Delta z (some W))
        ite_body)
    (pointwise : ∀ (x : ZFSet.{u}) (hx_mem : x ∈ ⟦tau⟧ᶻ)
      (_hx_D : x ∈ Dval),
      let Wx : SMT.Dom :=
        ⟨(ZFSet.fapply (BType.canonicalIsoSMTType tau).1
          (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType tau).2.1)
          ⟨x, by rwa [ZFSet.is_func_dom_eq
            (BType.canonicalIsoSMTType tau).2.1]⟩).1,
          tau.toSMTType, ZFSet.fapply_mem_range _ _⟩
      let x_fin : Fin vs.length → B.Dom := fun i =>
        ⟨x.get vs.length i, ⟨tau.get vs.length i,
          get_mem_type_of_isTuple
            (hasArity_of_mem_toZFSet tau_hasArity hx_mem)
            tau_hasArity hx_mem⟩⟩
      ∀ body_val : SMT.Dom,
        ⟦ite_body.abstract (Function.update Delta z (some Wx))
          (hcov_ite_upd Wx)⟧ˢ = some body_val →
        ∃ (Pval : ZFSet.{u}) (hPval : Pval ∈ ⟦BType.bool⟧ᶻ),
          ⟦(B.Term.abstract.go P vs Xi (fun v hv hvs => Xi_fv v
            (B.fv.mem_collect (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ =
            some (⟨Pval, BType.bool, hPval⟩ : B.Dom) ∧
          (body_val.fst = ZFSet.zftrue ↔ Pval = ZFSet.zftrue)) :
    ∀ (x : ZFSet.{u}) (hx_mem : x ∈ ⟦tau⟧ᶻ)
      (_hx_D : x ∈ Dval),
      let Wx : SMT.Dom :=
        ⟨(ZFSet.fapply (BType.canonicalIsoSMTType tau).1
          (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType tau).2.1)
          ⟨x, by rwa [ZFSet.is_func_dom_eq
            (BType.canonicalIsoSMTType tau).2.1]⟩).1,
          tau.toSMTType, ZFSet.fapply_mem_range _ _⟩
      let x_fin : Fin vs.length → B.Dom := fun i =>
        ⟨x.get vs.length i, ⟨tau.get vs.length i,
          get_mem_type_of_isTuple
            (hasArity_of_mem_toZFSet tau_hasArity hx_mem)
            tau_hasArity hx_mem⟩⟩
      ∀ body_val : SMT.Dom,
        ⟦ite_body.abstract (Function.update Delta z (some Wx))
          (hcov_ite_upd Wx)⟧ˢ = some body_val →
        (body_val.fst = ZFSet.zftrue ↔
          ∀ (Px : ZFSet.{u}) (P_ty : BType) (hP_val : Px ∈ ⟦P_ty⟧ᶻ),
            ⟦(B.Term.abstract.go P vs Xi (fun v hv hvs => Xi_fv v
              (B.fv.mem_collect (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ =
              some (⟨Px, P_ty, hP_val⟩ : B.Dom) → Px = ZFSet.zftrue) := by
  intro x hx_mem _hx_D Wx x_fin body_val hbody
  obtain ⟨Pval, hPval, hden, htruth⟩ :=
    pointwise x hx_mem _hx_D body_val hbody
  exact htruth.trans (B.denote_bool_true_iff_forall hden)

open Classical in
/-- The pointwise semantic bridge for the set-valued `collect` arm.

At a canonical image of a source-domain element, the encoded domain predicate
is true.  The tuple projections then install a represented valuation for the
source binder variables, so the predicate's representation-aware totality
theorem transfers the truth value of the substituted SMT body back to the
source predicate.  This is deliberately independent of the operational
encoder trace: the `collect` case and its alternative-valuation totality
clause can both reuse it. -/
theorem represented_collect_pointwise_body_bridge.{u}
    {vs : List B.𝒱} (vs_nemp : vs ≠ []) (vs_nodup : vs.Nodup)
    {D P : B.Term} {tau : BType}
    {Xi : B.RenamingContext.Context.{u}}
    (Xi_fv : ∀ v ∈ B.fv (B.Term.collect vs D P), (Xi v).isSome = true)
    (tau_hasArity : tau.hasArity vs.length)
    {Dval : ZFSet.{u}} {hDval : Dval ∈ ⟦BType.set tau⟧ᶻ}
    (den_D : ⟦D.abstract Xi
      (fun v hv => Xi_fv v (B.fv.mem_collect (.inl hv)))⟧ᴮ =
      some (⟨Dval, BType.set tau, hDval⟩ : B.Dom))
    {T : ZFSet.{u}} {hT : T ∈ ⟦BType.set tau⟧ᶻ}
    (den_collect : ⟦(B.Term.collect vs D P).abstract Xi Xi_fv⟧ᴮ =
      some (⟨T, BType.set tau, hT⟩ : B.Dom))
    {Denc Penc ite_body : SMT.Term} {z : SMT.𝒱}
    {ThetaD : SMT.RenamingContext.Context.{u}} {DencVal : SMT.Dom.{u}}
    (hcov_D_upd : ∀ W : SMT.Dom,
      SMT.RenamingContext.CoversFV
        (Function.update ThetaD z (some W)) Denc)
    (den_D_upd : ∀ W : SMT.Dom,
      ⟦Denc.abstract (Function.update ThetaD z (some W))
        (hcov_D_upd W)⟧ˢ = some DencVal)
    (hDenc_type : DencVal.snd.fst = tau.toSMTType.fun SMTType.bool)
    (hDenc_func : ⟦tau.toSMTType⟧ᶻ.IsFunc 𝔹 DencVal.fst)
    (D_rel : RDomCastSupported
      (⟨Dval, BType.set tau, hDval⟩ : B.Dom) DencVal)
    (ite_body_def : ite_body = ((@ˢDenc) (.var z)).ite
      (SMT.substList vs (toDestPair vs (.var z)) Penc) (.bool false))
    (hcov_ite_upd : ∀ W : SMT.Dom,
      SMT.RenamingContext.CoversFV
        (Function.update ThetaD z (some W)) ite_body)
    (hcov_sub_upd : ∀ W : SMT.Dom,
      SMT.RenamingContext.CoversFV
        (Function.update ThetaD z (some W))
          (SMT.substList vs (toDestPair vs (.var z)) Penc))
    (hcov_P_upd : ∀ (W : SMT.Dom) (ss : Fin vs.length → SMT.Dom),
      SMT.RenamingContext.CoversFV
        (Function.updates (Function.update ThetaD z (some W)) vs
          ((List.ofFn ss).map Option.some)) Penc)
    (hvs_not_bv : ∀ v ∈ vs, v ∉ SMT.bv Penc)
    (hz_not_bv : z ∉ SMT.bv Penc) (hz_not_vs : z ∉ vs)
    (Penc_fv : SMT.fv Penc ⊆ B.Term.vars P)
    (z_not_vars_P : z ∉ B.Term.vars P)
    {Ebody : B.Env} {LambdaP GammaP : SMT.TypeContext}
    {sigmaP : SMTType} {usedP : List SMT.𝒱}
    (typ_P : Ebody.context ⊢ᴮ P : BType.bool)
    (P_total : EncodeTermRepTotal.{u}
      P Ebody BType.bool LambdaP Penc sigmaP GammaP usedP)
    (ambient : ∀ v ∈ B.fv P, v ∉ vs →
      match Xi v, ThetaD v with
      | some d, some d' => RDomCastSupported d d'
      | _, _ => False)
    (wf_bound : ∀ (x : ZFSet.{u}) (hx : x ∈ ⟦tau⟧ᶻ)
      (_hx_D : x ∈ Dval),
      B.RenWF Ebody.context
        (Function.updates Xi vs (List.ofFn fun i => some
          (⟨x.get vs.length i, tau.get vs.length i,
            get_mem_type_of_isTuple
              (hasArity_of_mem_toZFSet tau_hasArity hx)
              tau_hasArity hx⟩ : B.Dom))))
    (bound_none : ∀ (ss : Fin vs.length → SMT.Dom),
      ∀ v ∉ usedP,
        Function.updates ThetaD vs
          ((List.ofFn ss).map Option.some) v = none)
    (bound_respects : ∀ (ss : Fin vs.length → SMT.Dom),
      B.RenamingContext.RespectsTypeContextOnFV
        (Function.updates ThetaD vs
          ((List.ofFn ss).map Option.some)) LambdaP P)
    (bound_dom : ∀ (ss : Fin vs.length → SMT.Dom),
      ∀ v,
        Function.updates ThetaD vs
          ((List.ofFn ss).map Option.some) v ≠ none → v ∈ LambdaP) :
    ∀ (x : ZFSet.{u}) (hx_mem : x ∈ ⟦tau⟧ᶻ) (_hx_D : x ∈ Dval),
      let Wx : SMT.Dom :=
        ⟨(ZFSet.fapply (BType.canonicalIsoSMTType tau).1
          (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType tau).2.1)
          ⟨x, by rwa [ZFSet.is_func_dom_eq
            (BType.canonicalIsoSMTType tau).2.1]⟩).1,
          tau.toSMTType, ZFSet.fapply_mem_range _ _⟩
      let x_fin : Fin vs.length → B.Dom := fun i =>
        ⟨x.get vs.length i, tau.get vs.length i,
          get_mem_type_of_isTuple
            (hasArity_of_mem_toZFSet tau_hasArity hx_mem)
            tau_hasArity hx_mem⟩
      ∀ body_val : SMT.Dom,
        ⟦ite_body.abstract (Function.update ThetaD z (some Wx))
          (hcov_ite_upd Wx)⟧ˢ = some body_val →
        ∃ (Pval : ZFSet.{u}) (hPval : Pval ∈ ⟦BType.bool⟧ᶻ),
          ⟦(B.Term.abstract.go P vs Xi (fun v hv hvs => Xi_fv v
            (B.fv.mem_collect (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ =
            some (⟨Pval, BType.bool, hPval⟩ : B.Dom) ∧
          (body_val.fst = ZFSet.zftrue ↔ Pval = ZFSet.zftrue) := by
  intro x hx_mem hx_D
  dsimp only
  let Wx : SMT.Dom :=
    ⟨(ZFSet.fapply (BType.canonicalIsoSMTType tau).1
      (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType tau).2.1)
      ⟨x, by rwa [ZFSet.is_func_dom_eq
        (BType.canonicalIsoSMTType tau).2.1]⟩).1,
      tau.toSMTType, ZFSet.fapply_mem_range _ _⟩
  let x_fin : Fin vs.length → B.Dom := fun i =>
    ⟨x.get vs.length i, tau.get vs.length i,
      get_mem_type_of_isTuple
        (hasArity_of_mem_toZFSet tau_hasArity hx_mem)
        tau_hasArity hx_mem⟩
  change ∀ body_val : SMT.Dom,
    ⟦ite_body.abstract (Function.update ThetaD z (some Wx))
      (hcov_ite_upd Wx)⟧ˢ = some body_val →
    ∃ (Pval : ZFSet.{u}) (hPval : Pval ∈ ⟦BType.bool⟧ᶻ),
      ⟦(B.Term.abstract.go P vs Xi (fun v hv hvs => Xi_fv v
        (B.fv.mem_collect (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ =
        some (⟨Pval, BType.bool, hPval⟩ : B.Dom) ∧
      (body_val.fst = ZFSet.zftrue ↔ Pval = ZFSet.zftrue)
  intro body_val hden_body
  have hWx_type : Wx.snd.fst = tau.toSMTType := rfl
  have hWx_mem : Wx.fst ∈ ⟦tau.toSMTType⟧ᶻ := Wx.snd.snd
  have hWx_retract : retract tau Wx.fst = x := by
    dsimp [Wx]
    exact retract_of_canonical tau hx_mem
  have hcov_z : SMT.RenamingContext.CoversFV
      (Function.update ThetaD z (some Wx)) (.var z) := by
    intro v hv
    simp only [SMT.fv, List.mem_singleton] at hv
    subst v
    simp
  have hden_z : ⟦(SMT.Term.var z).abstract
      (Function.update ThetaD z (some Wx)) hcov_z⟧ˢ = some Wx := by
    simp only [SMT.Term.abstract, Function.update_self, Option.get_some,
      SMT.denote, Option.pure_def]
  obtain ⟨hcov_Dapp, Dapp, hden_Dapp, hDapp_type, hDapp_true⟩ :=
    represented_set_app_true_of_mem_canonical hcov_D_upd den_D_upd
      hDenc_type hDenc_func D_rel hx_D
  obtain ⟨ss, hcomponents, related_P⟩ :=
    represented_toDestPair_bound_context vs_nemp vs_nodup tau_hasArity
      hx_mem hcov_z hden_z hWx_type hWx_mem hWx_retract ambient
  have hss_map : (List.ofFn ss).map Option.some =
      List.ofFn (fun i => some (ss i)) := by
    rw [List.map_ofFn]
    rfl
  have related_P' : RValuationCastSupportedOnFV
      (Function.updates Xi vs (List.ofFn fun i => some (x_fin i)))
      (Function.updates ThetaD vs
        ((List.ofFn ss).map Option.some)) P := by
    rw [hss_map]
    exact related_P
  have hx_fin_typ : ∀ i, (x_fin i).snd.fst = tau.get vs.length i ∧
      (x_fin i).fst ∈ ⟦tau.get vs.length i⟧ᶻ :=
    fun i => ⟨rfl, (x_fin i).snd.snd⟩
  have hx_fin_eq : ZFSet.ofFinDom x_fin = x := by
    simpa [x_fin] using
      (ZFSet.ofFinDom_get (List.length_pos_iff.mpr vs_nemp)
        (fun i => get_mem_type_of_isTuple
          (hasArity_of_mem_toZFSet tau_hasArity hx_mem)
          tau_hasArity hx_mem)
        (hasArity_of_mem_toZFSet tau_hasArity hx_mem) tau_hasArity)
  have hx_fin_D : ZFSet.ofFinDom x_fin ∈ Dval := by
    rw [hx_fin_eq]
    exact hx_D
  obtain ⟨XiP_fv', Pval, hPval, den_P⟩ :=
    B.denote_collect_predicate_exists Xi_fv vs_nemp vs_nodup tau_hasArity
      den_D den_collect typ_P hx_fin_typ hx_fin_D
      (wf_bound x hx_mem hx_D)
  have hbound_values : ∀ (i : ℕ) (hi_x : i < vs.length)
      (hi_d : i < (List.ofFn ss).length),
      Function.updates ThetaD vs
        ((List.ofFn ss).map Option.some) vs[i] = some (ss ⟨i, hi_x⟩) := by
    intro i hi_x _hi_d
    rw [hss_map]
    rw [Function.updates_eq_if (by simp) vs_nodup,
      dif_pos (List.getElem_mem hi_x)]
    simp [List.Nodup.idxOf_getElem vs_nodup]
  have hctx_source : ∀ v ∈ B.Term.vars P, v ∉ vs →
      ThetaD v = Function.updates ThetaD vs
          ((List.ofFn ss).map Option.some) v := by
    intro v hv hvs
    rw [hss_map]
    rw [Function.updates_of_not_mem _ vs _ v hvs]
  have htruth := collect_ite_truth_of_total_body_toDestPair
    (Pterm := P) (E := Ebody) (Lambda := LambdaP) (Gamma := GammaP)
    (sigma := sigmaP) (used := usedP)
    vs_nemp vs_nodup (z := z) (DeltaCtx := ThetaD) (W := Wx) (ss := ss)
    (hbody_def := ite_body_def)
    (hcov_body := hcov_ite_upd Wx)
    (hcov_Dapp := hcov_Dapp)
    (hcov_sub := hcov_sub_upd Wx)
    (hcov_upd := hcov_P_upd Wx ss)
    (hvs_not_bv := hvs_not_bv) (hz_not_bv := hz_not_bv)
    (hz_not_vs := hz_not_vs)
    (hcomponents := by
      intro i
      obtain ⟨hcov, hden, _⟩ := hcomponents i
      exact ⟨hcov, hden⟩)
    (P_total := P_total) (Xi_fv := XiP_fv')
    (related := related_P') (wf := wf_bound x hx_mem hx_D)
    (ThetaBase_none := bound_none ss)
    (source_respects := bound_respects ss)
    (ThetaBase_dom := bound_dom ss)
    (den_P := den_P) (bound_values := hbound_values)
    (hPenc_fv := Penc_fv) (z_not_vars_Pterm := z_not_vars_P)
    (hctx_source := hctx_source)
    (hden_D := hden_Dapp) (hden_body := hden_body)
    (hD_type := hDapp_type) (hD_true := hDapp_true)
  have den_P_go :
      ⟦(B.Term.abstract.go P vs Xi (fun v hv hvs => Xi_fv v
        (B.fv.mem_collect (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ =
        some (⟨Pval, BType.bool, hPval⟩ : B.Dom) := by
    rw [denote_term_abstract_go_eq_term_abstract vs_nodup vs_nemp x_fin
      XiP_fv']
    exact den_P
  exact ⟨Pval, hPval, den_P_go, htruth⟩

open Classical in
/-- Assemble the representation-aware collection body bridge into the
retraction equation for the set-valued lambda emitted by the encoder.

The operational `collect` proof has to establish coverage, typing, and
totality for a concrete encoder trace.  Once it has done so, this lemma is
the whole semantic core: source collection denotation supplies the separation
equation and predicate totality, while
`represented_collect_pointwise_body_bridge` supplies the only genuinely
representation-sensitive step.  Keeping the composition here lets both the
main run and the alternative-valuation totality proof share exactly the same
argument. -/
theorem represented_collect_set_retract.{u}
    {vs : List B.𝒱} (vs_nemp : vs ≠ []) (vs_nodup : vs.Nodup)
    {D P : B.Term} {tau : BType}
    {Xi : B.RenamingContext.Context.{u}}
    (Xi_fv : ∀ v ∈ B.fv (B.Term.collect vs D P), (Xi v).isSome = true)
    (tau_hasArity : tau.hasArity vs.length)
    {Dval : ZFSet.{u}} {hDval : Dval ∈ ⟦BType.set tau⟧ᶻ}
    (den_D : ⟦D.abstract Xi
      (fun v hv => Xi_fv v (B.fv.mem_collect (.inl hv)))⟧ᴮ =
      some (⟨Dval, BType.set tau, hDval⟩ : B.Dom))
    {T : ZFSet.{u}} {hT : T ∈ ⟦BType.set tau⟧ᶻ}
    (den_collect : ⟦(B.Term.collect vs D P).abstract Xi Xi_fv⟧ᴮ =
      some (⟨T, BType.set tau, hT⟩ : B.Dom))
    {Denc Penc ite_body : SMT.Term} {z : SMT.𝒱}
    {ThetaD : SMT.RenamingContext.Context.{u}} {DencVal : SMT.Dom.{u}}
    (ite_body_def : ite_body = ((@ˢDenc) (.var z)).ite
      (SMT.substList vs (toDestPair vs (.var z)) Penc) (.bool false))
    (z_not_fv_D : z ∉ SMT.fv Denc)
    (hcov_lambda : SMT.RenamingContext.CoversFV ThetaD
      ((λˢ [z]) [tau.toSMTType] ite_body))
    {lamVal : SMT.Dom.{u}}
    (hlamVal : ⟦((λˢ [z]) [tau.toSMTType] ite_body).abstract ThetaD
      hcov_lambda⟧ˢ = some lamVal)
    (hlamVal_func : ⟦tau.toSMTType⟧ᶻ.IsFunc 𝔹 lamVal.fst)
    (hcov_D_upd : ∀ W : SMT.Dom,
      SMT.RenamingContext.CoversFV
        (Function.update ThetaD z (some W)) Denc)
    (den_D_upd : ∀ W : SMT.Dom,
      ⟦Denc.abstract (Function.update ThetaD z (some W))
        (hcov_D_upd W)⟧ˢ = some DencVal)
    (hDenc_type : DencVal.snd.fst = tau.toSMTType.fun SMTType.bool)
    (hDenc_func : ⟦tau.toSMTType⟧ᶻ.IsFunc 𝔹 DencVal.fst)
    (D_rel : RDomCastSupported
      (⟨Dval, BType.set tau, hDval⟩ : B.Dom) DencVal)
    (hcov_ite_upd : ∀ W : SMT.Dom,
      SMT.RenamingContext.CoversFV
        (Function.update ThetaD z (some W)) ite_body)
    {GammaBody : SMT.TypeContext}
    (typ_ite : GammaBody.insert z tau.toSMTType ⊢ˢ ite_body : SMTType.bool)
    (Theta_wt : ∀ v ∈ SMT.fv ite_body, ∀ d : SMT.Dom,
      ThetaD v = some d → ∀ sigma, GammaBody.lookup v = some sigma →
        d.snd.fst = sigma)
    (hcov_sub_upd : ∀ W : SMT.Dom,
      SMT.RenamingContext.CoversFV
        (Function.update ThetaD z (some W))
          (SMT.substList vs (toDestPair vs (.var z)) Penc))
    (fv_substList_disj_vs : ∀ v ∈
      SMT.fv (SMT.substList vs (toDestPair vs (.var z)) Penc),
      v ≠ z → v ∉ vs)
    (hgo_cov : ∀ x ∈ SMT.fv ite_body, x ∉ [z] → (ThetaD x).isSome = true)
    (hcov_P_upd : ∀ (W : SMT.Dom) (ss : Fin vs.length → SMT.Dom),
      SMT.RenamingContext.CoversFV
        (Function.updates (Function.update ThetaD z (some W)) vs
          ((List.ofFn ss).map Option.some)) Penc)
    (hvs_not_bv : ∀ v ∈ vs, v ∉ SMT.bv Penc)
    (hz_not_bv : z ∉ SMT.bv Penc) (hz_not_vs : z ∉ vs)
    (Penc_fv : SMT.fv Penc ⊆ B.Term.vars P)
    (z_not_vars_P : z ∉ B.Term.vars P)
    {Ebody : B.Env} {LambdaP GammaP : SMT.TypeContext}
    {sigmaP : SMTType} {usedP : List SMT.𝒱}
    (typ_P : Ebody.context ⊢ᴮ P : BType.bool)
    (P_total : EncodeTermRepTotal.{u}
      P Ebody BType.bool LambdaP Penc sigmaP GammaP usedP)
    (ambient : ∀ v ∈ B.fv P, v ∉ vs →
      match Xi v, ThetaD v with
      | some d, some d' => RDomCastSupported d d'
      | _, _ => False)
    (wf_bound : ∀ (x : ZFSet.{u}) (hx : x ∈ ⟦tau⟧ᶻ)
      (_hx_D : x ∈ Dval),
      B.RenWF Ebody.context
        (Function.updates Xi vs (List.ofFn fun i => some
          (⟨x.get vs.length i, tau.get vs.length i,
            get_mem_type_of_isTuple
              (hasArity_of_mem_toZFSet tau_hasArity hx)
              tau_hasArity hx⟩ : B.Dom))))
    (bound_none : ∀ (ss : Fin vs.length → SMT.Dom),
      ∀ v ∉ usedP,
        Function.updates ThetaD vs
          ((List.ofFn ss).map Option.some) v = none)
    (bound_respects : ∀ (ss : Fin vs.length → SMT.Dom),
      B.RenamingContext.RespectsTypeContextOnFV
        (Function.updates ThetaD vs
          ((List.ofFn ss).map Option.some)) LambdaP P)
    (bound_dom : ∀ (ss : Fin vs.length → SMT.Dom),
      ∀ v,
        Function.updates ThetaD vs
          ((List.ofFn ss).map Option.some) v ≠ none → v ∈ LambdaP) :
    retract (BType.set tau) lamVal.fst = T := by
  have hDenc_retract : retract (BType.set tau) DencVal.fst = Dval := by
    have hcanonical :
        (⟨Dval, BType.set tau, hDval⟩ : B.Dom) ≘ᶻ DencVal :=
      (RDomCast.iff_RDom_of_type_eq (α := BType.set tau)
        (by simpa using hDenc_type)).mp D_rel.toRDomCast
    rw [RDom] at hcanonical
    exact hcanonical.2
  obtain ⟨hbody_total, hbody_ty⟩ :=
    SMT.RenamingContext.denote_update_total_and_type_of_typing
      typ_ite Theta_wt hcov_ite_upd
  refine retract_lamVal_eq_collect
    (D := D) (D_enc := Denc) (P_enc := Penc) (z := z)
    (ite_body := ite_body) (Δ_ctx := ThetaD) (lamVal := lamVal)
    (denD_val := DencVal) (𝒟_val := Dval) (P := P) (T_val := T)
    vs_nemp vs_nodup tau_hasArity ite_body_def z_not_fv_D
    hcov_lambda hlamVal hlamVal_func hcov_D_upd den_D_upd
    hDenc_type hDenc_func hDval hDenc_retract hcov_ite_upd
    hbody_total hbody_ty hcov_sub_upd fv_substList_disj_vs hgo_cov
    Xi_fv ?_ ?_ ?_
  · exact B.denote_collect_eq_sep Xi_fv tau_hasArity den_D den_collect
  · exact B.denote_collect_predicate_total Xi_fv tau_hasArity
      den_D den_collect
  · apply collect_hbridge_of_pointwise_bool
      (D := D) (P := P) (tau := tau) (Dval := Dval)
      Xi_fv tau_hasArity hcov_ite_upd
    exact represented_collect_pointwise_body_bridge
      (D := D) (P := P) (tau := tau) (Denc := Denc) (Penc := Penc)
      (ite_body := ite_body) (z := z) (ThetaD := ThetaD)
      (DencVal := DencVal) (Ebody := Ebody) (LambdaP := LambdaP)
      (GammaP := GammaP) (sigmaP := sigmaP) (usedP := usedP)
      vs_nemp vs_nodup Xi_fv tau_hasArity den_D den_collect
      hcov_D_upd den_D_upd hDenc_type hDenc_func D_rel ite_body_def
      hcov_ite_upd hcov_sub_upd hcov_P_upd hvs_not_bv hz_not_bv hz_not_vs
      Penc_fv z_not_vars_P typ_P P_total ambient wf_bound bound_none
      bound_respects bound_dom

open Classical in
/-- Turn the collection retraction equation into the representation-aware
denotation result required by an encoder run.

The only additional work beyond `represented_collect_set_retract` is ordinary
SMT totality for the emitted lambda.  Its typing gives both the denotation and
the functionhood needed by retraction, so a caller only has to provide the
trace-specific typing and free-variable compatibility facts once. -/
theorem represented_collect_set_denote.{u}
    {vs : List B.𝒱} (vs_nemp : vs ≠ []) (vs_nodup : vs.Nodup)
    {D P : B.Term} {tau : BType}
    {Xi : B.RenamingContext.Context.{u}}
    (Xi_fv : ∀ v ∈ B.fv (B.Term.collect vs D P), (Xi v).isSome = true)
    (tau_hasArity : tau.hasArity vs.length)
    {Dval : ZFSet.{u}} {hDval : Dval ∈ ⟦BType.set tau⟧ᶻ}
    (den_D : ⟦D.abstract Xi
      (fun v hv => Xi_fv v (B.fv.mem_collect (.inl hv)))⟧ᴮ =
      some (⟨Dval, BType.set tau, hDval⟩ : B.Dom))
    {T : ZFSet.{u}} {hT : T ∈ ⟦BType.set tau⟧ᶻ}
    (den_collect : ⟦(B.Term.collect vs D P).abstract Xi Xi_fv⟧ᴮ =
      some (⟨T, BType.set tau, hT⟩ : B.Dom))
    {Denc Penc ite_body : SMT.Term} {z : SMT.𝒱}
    {ThetaD : SMT.RenamingContext.Context.{u}} {DencVal : SMT.Dom.{u}}
    (ite_body_def : ite_body = ((@ˢDenc) (.var z)).ite
      (SMT.substList vs (toDestPair vs (.var z)) Penc) (.bool false))
    (z_not_fv_D : z ∉ SMT.fv Denc)
    (hcov_lambda : SMT.RenamingContext.CoversFV ThetaD
      ((λˢ [z]) [tau.toSMTType] ite_body))
    {GammaOut : SMT.TypeContext}
    (typ_lambda : GammaOut ⊢ˢ ((λˢ [z]) [tau.toSMTType] ite_body) :
      tau.toSMTType.fun SMTType.bool)
    (respects_lambda : SMT.RenamingContext.RespectsTypeContextOnFV
      ThetaD GammaOut ((λˢ [z]) [tau.toSMTType] ite_body))
    (hcov_D_upd : ∀ W : SMT.Dom,
      SMT.RenamingContext.CoversFV
        (Function.update ThetaD z (some W)) Denc)
    (den_D_upd : ∀ W : SMT.Dom,
      ⟦Denc.abstract (Function.update ThetaD z (some W))
        (hcov_D_upd W)⟧ˢ = some DencVal)
    (hDenc_type : DencVal.snd.fst = tau.toSMTType.fun SMTType.bool)
    (hDenc_func : ⟦tau.toSMTType⟧ᶻ.IsFunc 𝔹 DencVal.fst)
    (D_rel : RDomCastSupported
      (⟨Dval, BType.set tau, hDval⟩ : B.Dom) DencVal)
    (hcov_ite_upd : ∀ W : SMT.Dom,
      SMT.RenamingContext.CoversFV
        (Function.update ThetaD z (some W)) ite_body)
    {GammaBody : SMT.TypeContext}
    (typ_ite : GammaBody.insert z tau.toSMTType ⊢ˢ ite_body : SMTType.bool)
    (Theta_wt : ∀ v ∈ SMT.fv ite_body, ∀ d : SMT.Dom,
      ThetaD v = some d → ∀ sigma, GammaBody.lookup v = some sigma →
        d.snd.fst = sigma)
    (hcov_sub_upd : ∀ W : SMT.Dom,
      SMT.RenamingContext.CoversFV
        (Function.update ThetaD z (some W))
          (SMT.substList vs (toDestPair vs (.var z)) Penc))
    (fv_substList_disj_vs : ∀ v ∈
      SMT.fv (SMT.substList vs (toDestPair vs (.var z)) Penc),
      v ≠ z → v ∉ vs)
    (hgo_cov : ∀ x ∈ SMT.fv ite_body, x ∉ [z] → (ThetaD x).isSome = true)
    (hcov_P_upd : ∀ (W : SMT.Dom) (ss : Fin vs.length → SMT.Dom),
      SMT.RenamingContext.CoversFV
        (Function.updates (Function.update ThetaD z (some W)) vs
          ((List.ofFn ss).map Option.some)) Penc)
    (hvs_not_bv : ∀ v ∈ vs, v ∉ SMT.bv Penc)
    (hz_not_bv : z ∉ SMT.bv Penc) (hz_not_vs : z ∉ vs)
    (Penc_fv : SMT.fv Penc ⊆ B.Term.vars P)
    (z_not_vars_P : z ∉ B.Term.vars P)
    {Ebody : B.Env} {LambdaP GammaP : SMT.TypeContext}
    {sigmaP : SMTType} {usedP : List SMT.𝒱}
    (typ_P : Ebody.context ⊢ᴮ P : BType.bool)
    (P_total : EncodeTermRepTotal.{u}
      P Ebody BType.bool LambdaP Penc sigmaP GammaP usedP)
    (ambient : ∀ v ∈ B.fv P, v ∉ vs →
      match Xi v, ThetaD v with
      | some d, some d' => RDomCastSupported d d'
      | _, _ => False)
    (wf_bound : ∀ (x : ZFSet.{u}) (hx : x ∈ ⟦tau⟧ᶻ)
      (_hx_D : x ∈ Dval),
      B.RenWF Ebody.context
        (Function.updates Xi vs (List.ofFn fun i => some
          (⟨x.get vs.length i, tau.get vs.length i,
            get_mem_type_of_isTuple
              (hasArity_of_mem_toZFSet tau_hasArity hx)
              tau_hasArity hx⟩ : B.Dom))))
    (bound_none : ∀ (ss : Fin vs.length → SMT.Dom),
      ∀ v ∉ usedP,
        Function.updates ThetaD vs
          ((List.ofFn ss).map Option.some) v = none)
    (bound_respects : ∀ (ss : Fin vs.length → SMT.Dom),
      B.RenamingContext.RespectsTypeContextOnFV
        (Function.updates ThetaD vs
          ((List.ofFn ss).map Option.some)) LambdaP P)
    (bound_dom : ∀ (ss : Fin vs.length → SMT.Dom),
      ∀ v,
        Function.updates ThetaD vs
          ((List.ofFn ss).map Option.some) v ≠ none → v ∈ LambdaP) :
    ∃ lamVal : SMT.Dom.{u},
      ⟦((λˢ [z]) [tau.toSMTType] ite_body).abstract ThetaD
        hcov_lambda⟧ˢ = some lamVal ∧
      RDomCastSupported (⟨T, BType.set tau, hT⟩ : B.Dom) lamVal := by
  obtain ⟨lamVal, hlamVal, hlamVal_type⟩ :=
    SMT.RenamingContext.denote_exists_of_typing_fv typ_lambda
      respects_lambda hcov_lambda
  have hlamVal_func : ⟦tau.toSMTType⟧ᶻ.IsFunc 𝔹 lamVal.fst := by
    have hmem : lamVal.fst ∈ ⟦tau.toSMTType⟧ᶻ.funs 𝔹 := by
      simpa [hlamVal_type, SMTType.toZFSet] using lamVal.snd.snd
    exact ZFSet.mem_funs.mp hmem
  refine ⟨lamVal, hlamVal, ?_⟩
  apply RDomCastSupported.of_canonical_set_retract
  · simpa using hlamVal_type
  · exact represented_collect_set_retract
      (D := D) (P := P) (tau := tau) (Denc := Denc) (Penc := Penc)
      (ite_body := ite_body) (z := z) (ThetaD := ThetaD)
      (DencVal := DencVal) (lamVal := lamVal) (GammaBody := GammaBody)
      (Ebody := Ebody) (LambdaP := LambdaP) (GammaP := GammaP)
      (sigmaP := sigmaP) (usedP := usedP)
      vs_nemp vs_nodup Xi_fv tau_hasArity den_D den_collect ite_body_def
      z_not_fv_D hcov_lambda hlamVal hlamVal_func hcov_D_upd den_D_upd
      hDenc_type hDenc_func D_rel hcov_ite_upd typ_ite Theta_wt
      hcov_sub_upd fv_substList_disj_vs hgo_cov hcov_P_upd hvs_not_bv
      hz_not_bv hz_not_vs Penc_fv z_not_vars_P typ_P P_total ambient
      wf_bound bound_none bound_respects bound_dom
