import SMT.Reasoning.Basic.EncodeTermRepresentedScopedBool
import SMT.Reasoning.Basic.CastMembershipExact

open Std.Do B SMT ZFSet Classical

/-! # Representation-aware membership

This file isolates the semantic fact used both by the ordinary membership
constructor and by the membership guard generated inside `all`: applying a
canonical characteristic predicate to a represented element computes exactly
the source-level membership Boolean.
-/

namespace SMT.RenamingContext

/-- Restrict a target-context agreement along a type-context inclusion. -/
theorem RespectsTypeContextOnFV.of_super
    {Θ : Context} {Γ Γ' : SMT.TypeContext} {t : SMT.Term}
    (h : RespectsTypeContextOnFV Θ Γ' t)
    (hsub : Γ ⊆ Γ') :
    RespectsTypeContextOnFV Θ Γ t := by
  intro v τ hv hlookup
  exact h hv (AList.lookup_of_subset hsub hlookup)

/-- A loosening specification mentions only the input term and its fresh
helper; updating that helper with a value of the declared type preserves the
target-context agreement needed to evaluate the specification. -/
theorem respects_update_helper.{u}
    {Θ : Context.{u}} {Γ : SMT.TypeContext}
    {x spec : SMT.Term} {helper : SMT.𝒱} {τ : SMTType}
    {Y : SMT.Dom.{u}}
    (hfv : SMT.fv spec ⊆ SMT.fv x ∪ [helper])
    (hx : RespectsTypeContextOnFV Θ Γ x)
    (hlookup : Γ.lookup helper = some τ)
    (hY : Y.snd.fst = τ) :
    RespectsTypeContextOnFV
      (Function.update Θ helper (some Y)) Γ spec := by
  intro v σ hv hlookup_v
  by_cases hvh : v = helper
  · subst v
    rw [hlookup] at hlookup_v
    cases hlookup_v
    refine ⟨Y, by simp, hY⟩
  · rcases List.mem_union_iff.mp (hfv hv) with hvx | hvhelper
    · obtain ⟨d, hd, hdtype⟩ := hx hvx hlookup_v
      exact ⟨d, by simpa [Function.update_of_ne hvh] using hd, hdtype⟩
    · exact absurd (List.mem_singleton.mp hvhelper) hvh

end SMT.RenamingContext

/-- Applying a canonical characteristic-predicate representation to a target
value computes membership of its retraction in the represented source set. -/
theorem RDomCast.setPred_apply_eq_mem.{u}
    {τ : BType} {X S Y F : ZFSet.{u}}
    (hX : X ∈ ⟦τ⟧ᶻ)
    (hY : Y ∈ ⟦τ.toSMTType⟧ᶻ)
    (hF : F ∈ ⟦SMTType.fun τ.toSMTType SMTType.bool⟧ᶻ)
    (hYret : retract τ Y = X)
    (hFret : retract (BType.set τ) F = S) :
    (fapply F (is_func_is_pfunc (by
      simpa [SMTType.toZFSet] using hF :
        ⟦τ.toSMTType⟧ᶻ.IsFunc ZFSet.𝔹 F))
      ⟨Y, by
        rw [is_func_dom_eq (by
          simpa [SMTType.toZFSet] using hF :
            ⟦τ.toSMTType⟧ᶻ.IsFunc ZFSet.𝔹 F)]
        exact hY⟩).val = X ∈ᶻ S := by
  have hF_func : ⟦τ.toSMTType⟧ᶻ.IsFunc ZFSet.𝔹 F := by
    simpa [SMTType.toZFSet] using hF
  have hY_dom : Y ∈ F.Dom (is_rel_of_is_func hF_func) := by
    rw [is_func_dom_eq hF_func]
    exact hY
  change (fapply F (is_func_is_pfunc hF_func) ⟨Y, hY_dom⟩).val = X ∈ᶻ S
  by_cases hXS : X ∈ S
  · have hXS' := hXS
    rw [← hFret, ← hYret] at hXS'
    rw [retract, ZFSet.mem_sep] at hXS'
    obtain ⟨_, happ⟩ := hXS'
    have hret_mem : retract τ Y ∈ ⟦τ⟧ᶻ := by rwa [hYret]
    simp only [dif_pos hret_mem, dif_pos hF_func] at happ
    rw [fapply_eq_Image_singleton hF_func
      (ZFSet.fapply_mem_range _ _)] at happ
    simp only [canonical_of_retract τ hY] at happ
    rw [← fapply_eq_Image_singleton hF_func hY] at happ
    rw [happ]
    simp [overloadUnaryOp, hXS]
  · have hXS' := hXS
    rw [← hFret, ← hYret] at hXS'
    rw [retract, ZFSet.mem_sep, not_and] at hXS'
    have hret_mem : retract τ Y ∈ ⟦τ⟧ᶻ := by rwa [hYret]
    specialize hXS' hret_mem
    simp only [dif_pos hret_mem, dif_pos hF_func] at hXS'
    rw [fapply_eq_Image_singleton hF_func
      (ZFSet.fapply_mem_range _ _)] at hXS'
    simp only [canonical_of_retract τ hY] at hXS'
    rw [← fapply_eq_Image_singleton hF_func hY] at hXS'
    conv at hXS' =>
      enter [1, 2]
      change (⊤ : ZFBool)
    rw [← Subtype.ext_iff, ← ne_eq, ZFBool.not_top_iff_bot,
      Subtype.ext_iff] at hXS'
    rw [hXS']
    simp [overloadUnaryOp, hXS]

/-- Propositional form of `setPred_apply_eq_mem`. -/
theorem RDomCast.setPred_apply_eq_zftrue_iff.{u}
    {τ : BType} {X S Y F : ZFSet.{u}}
    (hX : X ∈ ⟦τ⟧ᶻ)
    (hY : Y ∈ ⟦τ.toSMTType⟧ᶻ)
    (hF : F ∈ ⟦SMTType.fun τ.toSMTType SMTType.bool⟧ᶻ)
    (hYret : retract τ Y = X)
    (hFret : retract (BType.set τ) F = S) :
    (fapply F (is_func_is_pfunc (by
      simpa [SMTType.toZFSet] using hF :
        ⟦τ.toSMTType⟧ᶻ.IsFunc ZFSet.𝔹 F))
      ⟨Y, by
        rw [is_func_dom_eq (by
          simpa [SMTType.toZFSet] using hF :
            ⟦τ.toSMTType⟧ᶻ.IsFunc ZFSet.𝔹 F)]
        exact hY⟩).val = ZFSet.zftrue ↔ X ∈ S := by
  rw [RDomCast.setPred_apply_eq_mem hX hY hF hYret hFret]
  by_cases hXS : X ∈ S
  · simp [overloadUnaryOp, hXS]
  · simpa [overloadUnaryOp, hXS] using
      (Ne.symm ZFSet.zftrue_ne_zffalse)

/-- The overloaded equality operation with its otherwise implicit domain made
explicit. -/
noncomputable def zfEqIn.{u} (A X Y : ZFSet.{u}) : ZFSet.{u} :=
  overloadBinOp (A := A) (B := ZFSet.𝔹) (·.val)
    (fun p => if p then ZFSet.ZFBool.true else ZFSet.ZFBool.false)
    (⊥ : Prop) (· = ·) X Y

/-- Equality at a common ZF domain evaluates to `zftrue` exactly when the
underlying values are equal. -/
theorem zfEqIn_eq_zftrue_iff.{u} {A X Y : ZFSet.{u}}
    (hX : X ∈ A) (hY : Y ∈ A) :
    zfEqIn A X Y = ZFSet.zftrue ↔ X = Y := by
  by_cases hXY : X = Y
  · subst Y
    simp [zfEqIn, overloadBinOp, Function.onFun, hX]
  · have hfalse : zfEqIn A X Y = ZFSet.zffalse := by
      simp [zfEqIn, overloadBinOp, Function.onFun, hX, hY, hXY]
    rw [hfalse]
    exact ⟨fun h => (ZFSet.zftrue_ne_zffalse h.symm).elim,
      fun h => (hXY h).elim⟩

/-- Membership through the option-function representation.  Equality with a
`some` result is true exactly for pairs belonging to the represented source
relation. -/
theorem RDomCast.optionFunction_eq_some_eq_zftrue_iff.{u}
    {α β : BType} {X S a b F : ZFSet.{u}}
    (hX : X ∈ ⟦α ×ᴮ β⟧ᶻ)
    (ha : a ∈ ⟦α.toSMTType⟧ᶻ)
    (hb : b ∈ ⟦β.toSMTType⟧ᶻ)
    (hF : F ∈ ⟦SMTType.fun α.toSMTType
      (SMTType.option β.toSMTType)⟧ᶻ)
    (hpair_ret : retract (α ×ᴮ β) (a.pair b) = X)
    (hgraph_ret : retract (BType.set (α ×ᴮ β))
      (optionGraph α.toSMTType β.toSMTType F) = S) :
    let Fapp := fapply F (is_func_is_pfunc (by
      simpa [SMTType.toZFSet] using hF :
        ⟦α.toSMTType⟧ᶻ.IsFunc
          ⟦SMTType.option β.toSMTType⟧ᶻ F))
      ⟨a, by
        rw [is_func_dom_eq (by
          simpa [SMTType.toZFSet] using hF :
            ⟦α.toSMTType⟧ᶻ.IsFunc
              ⟦SMTType.option β.toSMTType⟧ᶻ F)]
        exact ha⟩
    let someb := ZFSet.Option.some
      (S := ⟦β.toSMTType⟧ᶻ) ⟨b, hb⟩
    zfEqIn ⟦SMTType.option β.toSMTType⟧ᶻ
      Fapp.val someb.val = ZFSet.zftrue ↔ X ∈ S := by
  dsimp only
  let R := optionGraph α.toSMTType β.toSMTType F
  have hR : R ∈ ⟦SMTType.fun
      (SMTType.pair α.toSMTType β.toSMTType) SMTType.bool⟧ᶻ :=
    optionGraph_mem α.toSMTType β.toSMTType hF
  have hab : a.pair b ∈
      ⟦SMTType.pair α.toSMTType β.toSMTType⟧ᶻ :=
    ZFSet.pair_mem_prod.mpr ⟨ha, hb⟩
  have hR_func :
      ⟦SMTType.pair α.toSMTType β.toSMTType⟧ᶻ.IsFunc
        ZFSet.𝔹 R := by
    simpa [SMTType.toZFSet] using hR
  have hab_dom : a.pair b ∈ R.Dom (is_rel_of_is_func hR_func) := by
    rw [is_func_dom_eq hR_func]
    exact hab
  have happ_graph :
      (fapply R (is_func_is_pfunc hR_func)
          ⟨a.pair b, hab_dom⟩).val = ZFSet.zftrue ↔
        a.pair b ∈ predGraph α.toSMTType β.toSMTType R := by
    unfold predGraph
    rw [ZFSet.mem_sep, ZFSet.pair_mem_prod]
    simp only [ha, hb, and_self, true_and]
    constructor
    · intro heq
      rw [← heq]
      exact fapply.def (is_func_is_pfunc hR_func) _
    · intro hpair
      exact Subtype.ext_iff.mp
        (fapply.of_pair (is_func_is_pfunc hR_func) hpair)
  have hset :
      (fapply R (is_func_is_pfunc hR_func)
          ⟨a.pair b, hab_dom⟩).val = ZFSet.zftrue ↔ X ∈ S := by
    exact RDomCast.setPred_apply_eq_zftrue_iff hX hab hR
      hpair_ret hgraph_ret
  have hgraph_F :
      a.pair b ∈ predGraph α.toSMTType β.toSMTType R ↔
        a.pair (ZFSet.Option.some
          (S := ⟦β.toSMTType⟧ᶻ) ⟨b, hb⟩).val ∈ F := by
    exact mem_predGraph_optionGraph_iff
      α.toSMTType β.toSMTType F hF a b ha hb
  have hF_func : ⟦α.toSMTType⟧ᶻ.IsFunc
      ⟦SMTType.option β.toSMTType⟧ᶻ F := by
    simpa [SMTType.toZFSet] using hF
  let someb := ZFSet.Option.some
    (S := ⟦β.toSMTType⟧ᶻ) ⟨b, hb⟩
  have hsomeb : someb.val ∈ ⟦SMTType.option β.toSMTType⟧ᶻ :=
    someb.property
  have ha_dom : a ∈ F.Dom (is_rel_of_is_func hF_func) := by
    rw [is_func_dom_eq hF_func]
    exact ha
  have hpair_app : a.pair someb.val ∈ F ↔
      (fapply F (is_func_is_pfunc hF_func) ⟨a, ha_dom⟩).val =
        someb.val := by
    constructor
    · intro hpair
      exact Subtype.ext_iff.mp
        (fapply.of_pair (is_func_is_pfunc hF_func) hpair)
    · intro heq
      rw [← heq]
      exact fapply.def (is_func_is_pfunc hF_func) _
  rw [zfEqIn_eq_zftrue_iff
    (ZFSet.fapply_mem_range (is_func_is_pfunc hF_func) _)
    hsomeb]
  exact hpair_app.symm.trans (hgraph_F.symm.trans
    (happ_graph.symm.trans hset))

/-- Exact membership semantics after casting an arbitrary supported element to
the canonical argument of a characteristic predicate. -/
theorem RDomCast.setPred_cast_apply_eq_zftrue_iff.{u}
    {τ : BType} {σ : SMTType}
    {X S X₀ Y F : ZFSet.{u}}
    {hX : X ∈ ⟦τ⟧ᶻ} {hS : S ∈ ⟦BType.set τ⟧ᶻ}
    {hX₀ : X₀ ∈ ⟦σ⟧ᶻ}
    {hY : Y ∈ ⟦τ.toSMTType⟧ᶻ}
    {hF : F ∈ ⟦SMTType.fun τ.toSMTType SMTType.bool⟧ᶻ}
    (Xrel : RDomCast (⟨X, τ, hX⟩ : B.Dom)
      (⟨X₀, σ, hX₀⟩ : SMT.Dom))
    (Srel : RDomCast (⟨S, BType.set τ, hS⟩ : B.Dom)
      (⟨F, SMTType.fun τ.toSMTType SMTType.bool, hF⟩ : SMT.Dom))
    (c : σ ~> τ.toSMTType)
    (hcast : X₀.pair Y ∈ (castZF_of_path c).1) :
    (fapply F (is_func_is_pfunc (by
      simpa [SMTType.toZFSet] using hF :
        ⟦τ.toSMTType⟧ᶻ.IsFunc ZFSet.𝔹 F))
      ⟨Y, by
        rw [is_func_dom_eq (by
          simpa [SMTType.toZFSet] using hF :
            ⟦τ.toSMTType⟧ᶻ.IsFunc ZFSet.𝔹 F)]
        exact hY⟩).val = ZFSet.zftrue ↔ X ∈ S := by
  obtain ⟨c₀, hretX⟩ := Xrel
  have hc : c₀ = c := castPath.eq_of_endpoints c₀ c
  subst c₀
  have hYeq : castZF_apply c X₀ = Y :=
    castZF_apply_eq_of_pair c hX₀ hcast
  have hYret : retract τ Y = X := by
    rw [← hYeq]
    exact hretX
  have hFret : retract (BType.set τ) F = S :=
    ((RDomCast.iff_RDom_of_type_eq
      (α := BType.set τ) rfl).mp Srel).2
  exact RDomCast.setPred_apply_eq_zftrue_iff
    hX hY hF hYret hFret

/-- Exact membership semantics after casting a represented pair to the
canonical pair consumed by an option-valued function. -/
theorem RDomCast.optionFunction_cast_eq_some_eq_zftrue_iff.{u}
    {α β : BType} {σ : SMTType}
    {X S X₀ Y F : ZFSet.{u}}
    {hX : X ∈ ⟦α ×ᴮ β⟧ᶻ}
    {hS : S ∈ ⟦BType.set (α ×ᴮ β)⟧ᶻ}
    {hX₀ : X₀ ∈ ⟦σ⟧ᶻ}
    {hY : Y ∈ ⟦SMTType.pair α.toSMTType β.toSMTType⟧ᶻ}
    {hF : F ∈ ⟦SMTType.fun α.toSMTType
      (SMTType.option β.toSMTType)⟧ᶻ}
    (Xrel : RDomCast (⟨X, α ×ᴮ β, hX⟩ : B.Dom)
      (⟨X₀, σ, hX₀⟩ : SMT.Dom))
    (Srel : RDomCast
      (⟨S, BType.set (α ×ᴮ β), hS⟩ : B.Dom)
      (⟨F, SMTType.fun α.toSMTType
        (SMTType.option β.toSMTType), hF⟩ : SMT.Dom))
    (c : σ ~> SMTType.pair α.toSMTType β.toSMTType)
    (hcast : X₀.pair Y ∈ (castZF_of_path c).1) :
    let Fapp := fapply F (is_func_is_pfunc (by
      simpa [SMTType.toZFSet] using hF :
        ⟦α.toSMTType⟧ᶻ.IsFunc
          ⟦SMTType.option β.toSMTType⟧ᶻ F))
      ⟨Y.π₁, by
        have hp := ZFSet.pair_mem_prod.mp
          (ZFSet.pair_eta hY ▸ hY)
        rw [is_func_dom_eq (by
          simpa [SMTType.toZFSet] using hF :
            ⟦α.toSMTType⟧ᶻ.IsFunc
              ⟦SMTType.option β.toSMTType⟧ᶻ F)]
        exact hp.1⟩
    let someY := ZFSet.Option.some
      (S := ⟦β.toSMTType⟧ᶻ) ⟨Y.π₂, by
        exact (ZFSet.pair_mem_prod.mp
          (ZFSet.pair_eta hY ▸ hY)).2⟩
    zfEqIn ⟦SMTType.option β.toSMTType⟧ᶻ
      Fapp.val someY.val = ZFSet.zftrue ↔ X ∈ S := by
  dsimp only
  obtain ⟨c₀, hretX⟩ := Xrel
  have hc : c₀ = c := castPath.eq_of_endpoints c₀ c
  subst c₀
  have hYeq : castZF_apply c X₀ = Y :=
    castZF_apply_eq_of_pair c hX₀ hcast
  have hYret : retract (α ×ᴮ β) Y = X := by
    rw [← hYeq]
    exact hretX
  have hYeta : Y = Y.π₁.pair Y.π₂ := ZFSet.pair_eta hY
  have hYparts := ZFSet.pair_mem_prod.mp (hYeta ▸ hY)
  have hpair_ret :
      retract (α ×ᴮ β) (Y.π₁.pair Y.π₂) = X := by
    rw [← hYeta]
    exact hYret
  have hgraph_ret : retract (BType.set (α ×ᴮ β))
      (optionGraph α.toSMTType β.toSMTType F) = S :=
    RDomCast.optionFunction_graph_retract Srel
  exact RDomCast.optionFunction_eq_some_eq_zftrue_iff
    hX hYparts.1 hYparts.2 hF hpair_ret hgraph_ret

/-! ## Constructor-facing cast-membership contract -/

/-- Semantic contract of one completed `castMembership` run.  The first
clause constructs a satisfying helper assignment; the second proves exactness
for every assignment satisfying the generated helper guards. -/
abbrev CastMembershipRepSemantics.{u}
    (τ : BType) (x S t : SMT.Term) (σx σS : SMTType)
    (Γ : SMT.TypeContext) (used₀ used₁ : List SMT.𝒱)
    (Dlt : SMT.Chunk) : Prop :=
  ∀ (Γsup : SMT.TypeContext), Γ ⊆ Γsup →
    ∀ (Θ : SMT.RenamingContext.Context.{u})
      (hcov_x : SMT.RenamingContext.CoversFV Θ x)
      (hcov_S : SMT.RenamingContext.CoversFV Θ S),
      (∀ v ∉ used₀, Θ v = none) →
      SMT.RenamingContext.RespectsTypeContextOnFV Θ Γsup x →
      SMT.RenamingContext.RespectsTypeContextOnFV Θ Γsup S →
      (∀ v, Θ v ≠ none → v ∈ Γsup) →
      ∀ (X A : ZFSet.{u})
        (hX : X ∈ ⟦τ⟧ᶻ) (hA : A ∈ ⟦BType.set τ⟧ᶻ)
        (denX denA : SMT.Dom.{u}),
        ⟦x.abstract Θ hcov_x⟧ˢ = some denX →
        ⟦S.abstract Θ hcov_S⟧ˢ = some denA →
        denX.snd.fst = σx → denA.snd.fst = σS →
        RDomCast (⟨X, τ, hX⟩ : B.Dom) denX →
        RDomCast (⟨A, BType.set τ, hA⟩ : B.Dom) denA →
        (∃ (Θ' : SMT.RenamingContext.Context.{u})
          (hcov_t : SMT.RenamingContext.CoversFV Θ' t)
          (denM : SMT.Dom.{u}),
          SMT.RenamingContext.Extends Θ' Θ ∧
          (∀ v ∉ used₁, Θ' v = none) ∧
          SMT.RenamingContext.RespectsTypeContextOnFV Θ' Γsup t ∧
          (∀ v, Θ' v ≠ none → v ∈ Γsup) ∧
          SpecBodiesTrue Θ' Γsup Dlt ∧
          ⟦t.abstract Θ' hcov_t⟧ˢ = some denM ∧
          denM.snd.fst = SMTType.bool ∧
          (denM.fst = ZFSet.zftrue ↔ X ∈ A)) ∧
        (∀ (hcov_t : SMT.RenamingContext.CoversFV Θ t)
          (denM : SMT.Dom.{u}),
          SMT.RenamingContext.RespectsTypeContextOnFV Θ Γsup t →
          SpecBodiesTrue Θ Γsup Dlt →
          ⟦t.abstract Θ hcov_t⟧ˢ = some denM →
          denM.snd.fst = SMTType.bool →
          (denM.fst = ZFSet.zftrue ↔ X ∈ A))

/-- Operational and semantic contract selected from the supported target
representations of an element and its set. -/
abbrev CastMembershipRepSpec.{u} (τ : BType)
    (x S : SMT.Term) (σx σS : SMTType) : Prop :=
  ∀ {Λ : SMT.TypeContext} {n : ℕ} {used : List SMT.𝒱}
    {decl : SMT.Chunk},
    Λ ⊢ˢ x : σx →
    Λ ⊢ˢ S : σS →
    (∀ v ∈ SMT.bv x, v ∈ used) →
    (∀ v ∈ SMT.bv S, v ∈ used) →
    ⦃fun ⟨E, Λ'⟩ =>
      ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ Λ.keys ⊆ E.usedVars ∧
        E.usedVars = used ∧ E.declarations = decl⌝⦄
    castMembership ⟨x, σx⟩ ⟨S, σS⟩
    ⦃⇓? ⟨t, σ⟩ ⟨E', Γ'⟩ =>
      ⌜used ⊆ E'.usedVars ∧
        Λ ⊆ Γ' ∧
        Γ'.keys ⊆ E'.usedVars ∧
        σ = SMTType.bool ∧
        Γ' ⊢ˢ t : SMTType.bool ∧
        (∀ v ∈ used, v ∉ Λ → v ∉ Γ') ∧
        ∃ Dlt : SMT.Chunk,
          E'.declarations = decl ++ Dlt ∧
          CastMembershipRepSemantics.{u} τ x S t σx σS Γ'
            used E'.usedVars Dlt⌝⦄

theorem castMembership_direct_rep_contract.{u}
    (τ : BType) (x S : SMT.Term) :
    CastMembershipRepSpec.{u} τ x S τ.toSMTType
      (SMTType.fun τ.toSMTType SMTType.bool) := by
  unfold CastMembershipRepSpec
  intro Λ n used decl typ_x typ_S bv_x_used bv_S_used
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_sub, rfl, rfl⟩ := pre
  unfold castMembership
  simp only [bind_pure_comp]
  rw [dif_pos True.intro]
  mspec Std.Do.Spec.pure
  mpure_intro
  refine ⟨List.Subset.refl _, (fun _ h => h), St_sub, trivial,
    SMT.Typing.app _ _ _ _ _ typ_S typ_x, ?_, [], by simp, ?_⟩
  · exact fun _ _ h => h
  · intro Γsup Γsub Θ hcov_x hcov_S Θ_none respects_x respects_S
      Θ_dom X A hX hA denX denA hdenX hdenA hdenX_ty hdenA_ty
      Xrel Arel
    rcases denX with ⟨X₀, σX, hX₀⟩
    rcases denA with ⟨F, σA, hF⟩
    dsimp at hdenX_ty hdenA_ty
    subst σX
    subst σA
    have hcov_t : SMT.RenamingContext.CoversFV Θ (.app S x) := by
      intro v hv
      rw [SMT.fv, List.mem_append] at hv
      exact hv.elim (hcov_S v) (hcov_x v)
    have respects_t :
        SMT.RenamingContext.RespectsTypeContextOnFV Θ Γsup (.app S x) := by
      intro v σ hv hlookup
      rw [SMT.fv, List.mem_append] at hv
      exact hv.elim (fun h => respects_S h hlookup)
        (fun h => respects_x h hlookup)
    have hF_func : ⟦τ.toSMTType⟧ᶻ.IsFunc ZFSet.𝔹 F := by
      simpa [SMTType.toZFSet] using hF
    have hX₀_dom : X₀ ∈ F.Dom (is_rel_of_is_func hF_func) := by
      rw [is_func_dom_eq hF_func]
      exact hX₀
    let denM : SMT.Dom.{u} :=
      ⟨(fapply F (is_func_is_pfunc hF_func) ⟨X₀, hX₀_dom⟩).val,
        SMTType.bool, ZFSet.fapply_mem_range _ _⟩
    have hdenM : ⟦(SMT.Term.app S x).abstract Θ hcov_t⟧ˢ =
        some denM := by
      rw [SMT.Term.abstract, SMT.denote, Option.pure_def,
        Option.bind_eq_bind, Option.bind_eq_some_iff]
      refine ⟨⟨F, SMTType.fun τ.toSMTType SMTType.bool, hF⟩,
        ?_, ?_⟩
      · simpa only [proof_irrel_heq] using hdenA
      · rw [Option.bind_eq_some_iff]
        refine ⟨⟨X₀, τ.toSMTType, hX₀⟩, ?_, ?_⟩
        · simpa only [proof_irrel_heq] using hdenX
        · simp only [dif_pos True.intro,
            dif_pos (is_func_is_pfunc hF_func), dif_pos hX₀_dom, denM]
    have hcast := castZF_apply_pair
      (castPath.reflexive τ.toSMTType) hX₀
    rw [castZF_apply_reflexive τ.toSMTType hX₀] at hcast
    have hiff : denM.fst = ZFSet.zftrue ↔ X ∈ A := by
      dsimp [denM]
      exact RDomCast.setPred_cast_apply_eq_zftrue_iff
        (hY := hX₀) Xrel Arel
        (castPath.reflexive τ.toSMTType) hcast
    constructor
    · exact ⟨Θ, hcov_t, denM,
        SMT.RenamingContext.extends_refl Θ, Θ_none, respects_t,
        Θ_dom, by simp [SpecBodiesTrue, specBodies], hdenM, rfl, hiff⟩
    · intro hcov_t' denM' _ _ hdenM' hdenM'_ty
      have hagree : hcov_t' = hcov_t := Subsingleton.elim _ _
      subst hcov_t'
      rw [hdenM] at hdenM'
      cases hdenM'
      exact hiff

set_option maxHeartbeats 3000000 in
theorem castMembership_setPred_cast_rep_contract.{u}
    (τ : BType) (σx : SMTType) (x S : SMT.Term)
    (c : σx ~> τ.toSMTType) (hne : σx ≠ τ.toSMTType) :
    CastMembershipRepSpec.{u} τ x S σx
      (SMTType.fun τ.toSMTType SMTType.bool) := by
  unfold CastMembershipRepSpec
  intro Λ n used decl typ_x typ_S bv_x_used bv_S_used
  have hle : σx ⊑ τ.toSMTType := castable?_of_castPath c
  mstart
  mintro pre ∀St
  mpure pre
  mspec castMembership_branch2_exact_spec typ_x typ_S hne hle
    bv_x_used bv_S_used
  rename_i out
  obtain ⟨t, σ⟩ := out
  mrename_i post
  mintro ∀St'
  mpure post
  obtain ⟨_fvc, types_sub, keys_sub, used_sub, σ_eq, typ_t,
    _fv_t, preserves, _total,
    helper, spec, decl_eq, t_eq, helper_fresh, helper_not_used,
    helper_lookup, spec_fv, exactness⟩ := post
  change σ = SMTType.bool at σ_eq
  subst σ
  change t = spec ∧ˢ .app S (.var helper) at t_eq
  subst t
  mpure_intro
  refine ⟨used_sub, types_sub, keys_sub, rfl, typ_t, preserves,
    helperSpecChunk helper τ.toSMTType spec, decl_eq, ?_⟩
  intro Γsup Γsub Θ hcov_x hcov_S Θ_none respects_x respects_S
    Θ_dom X A hX hA denX denA hdenX hdenA hdenX_ty hdenA_ty
    Xrel Arel
  rcases denX with ⟨X₀, σX, hX₀⟩
  rcases denA with ⟨F, σA, hF⟩
  dsimp at hdenX_ty hdenA_ty
  subst σX
  subst σA
  have Λ_sub_sup : Λ ⊆ Γsup :=
    AList.subset_trans types_sub Γsub
  have respects_x_Λ :
      SMT.RenamingContext.RespectsTypeContextOnFV Θ Λ x :=
    respects_x.of_super Λ_sub_sup
  have hpf : ∀ (x_! : SMT.𝒱) (Y : SMT.Dom.{u}),
      ∀ v ∈ SMT.fv (SMT.Term.var x_!),
        (Function.update Θ x_! (some Y) v).isSome = true := by
    intro x_! Y v hv
    simp only [SMT.fv, List.mem_singleton] at hv
    subst v
    simp
  obtain ⟨Φ, Y, hden_var, hcov_spec, hden_spec, hY_ty,
      hΦ_ty, ⟨hΦ_true, hcast⟩, hguard⟩ :=
    exactness Θ hcov_x respects_x_Λ hpf
      (⟨X₀, σx, hX₀⟩ : SMT.Dom) hdenX
  let Θ' := Function.update Θ helper (some Y)
  have helper_none : Θ helper = none :=
    Θ_none helper helper_not_used
  have Θ'_ext : SMT.RenamingContext.Extends Θ' Θ :=
    SMT.RenamingContext.extends_update_of_none helper_none
  have helper_mem_final : helper ∈ St'.types :=
    AList.lookup_isSome.mp (by rw [helper_lookup]; rfl)
  have helper_used_final : helper ∈ St'.env.usedVars :=
    keys_sub helper_mem_final
  have Θ'_none : ∀ v ∉ St'.env.usedVars, Θ' v = none := by
    intro v hv
    by_cases hvh : v = helper
    · subst v
      exact absurd helper_used_final hv
    · simpa [Θ', Function.update_of_ne hvh] using
        Θ_none v (fun hv_used => hv (used_sub hv_used))
  have helper_lookup_sup : Γsup.lookup helper = some τ.toSMTType :=
    AList.lookup_of_subset Γsub helper_lookup
  have respects_spec :
      SMT.RenamingContext.RespectsTypeContextOnFV Θ' Γsup spec :=
    SMT.RenamingContext.respects_update_helper spec_fv respects_x
      helper_lookup_sup hY_ty
  have respects_S' :
      SMT.RenamingContext.RespectsTypeContextOnFV Θ' Γsup S :=
    by
      intro v ξ hv hlookup
      have hv_ne : v ≠ helper := by
        intro heq
        subst v
        exact helper_fresh
          (SMT.Typing.mem_context_of_mem_fv typ_S hv)
      obtain ⟨d, hd, hdty⟩ := respects_S hv hlookup
      exact ⟨d, by simpa [Θ', Function.update_of_ne hv_ne] using hd,
        hdty⟩
  have hcov_S' : SMT.RenamingContext.CoversFV Θ' S :=
    SMT.RenamingContext.coversFV_of_extends_of_coversFV Θ'_ext hcov_S
  have hdenA' : ⟦S.abstract Θ' hcov_S'⟧ˢ =
      some (⟨F, SMTType.fun τ.toSMTType SMTType.bool, hF⟩ : SMT.Dom) := by
    have hagree := SMT.RenamingContext.agreesOnFV_of_extends_of_coversFV
      Θ'_ext hcov_S
    exact (SMT.RenamingContext.denote_congr_of_agreesOnFV
      (t := S) (h1 := hcov_S') (h2 := hcov_S) hagree).trans hdenA
  have hcov_var : SMT.RenamingContext.CoversFV Θ' (.var helper) := by
    intro v hv
    simp only [SMT.fv, List.mem_singleton] at hv
    subst v
    simp [Θ']
  have respects_var :
      SMT.RenamingContext.RespectsTypeContextOnFV Θ' Γsup (.var helper) := by
    intro v ξ hv hlookup
    simp only [SMT.fv, List.mem_singleton] at hv
    subst v
    rw [helper_lookup_sup] at hlookup
    cases hlookup
    exact ⟨Y, by simp [Θ'], hY_ty⟩
  have hF_func : ⟦τ.toSMTType⟧ᶻ.IsFunc ZFSet.𝔹 F := by
    simpa [SMTType.toZFSet] using hF
  have hY_mem : Y.fst ∈ ⟦τ.toSMTType⟧ᶻ := by
    rw [← hY_ty]
    exact Y.snd.snd
  have hY_dom : Y.fst ∈ F.Dom (is_rel_of_is_func hF_func) := by
    rw [is_func_dom_eq hF_func]
    exact hY_mem
  let denApp : SMT.Dom.{u} :=
    ⟨(fapply F (is_func_is_pfunc hF_func) ⟨Y.fst, hY_dom⟩).val,
      SMTType.bool, ZFSet.fapply_mem_range _ _⟩
  have hcov_app : SMT.RenamingContext.CoversFV Θ'
      (.app S (.var helper)) := by
    intro v hv
    rw [SMT.fv, List.mem_append] at hv
    exact hv.elim (hcov_S' v) (hcov_var v)
  have hden_app : ⟦(SMT.Term.app S (.var helper)).abstract
      Θ' hcov_app⟧ˢ = some denApp := by
    rw [SMT.Term.abstract, SMT.denote, Option.pure_def,
      Option.bind_eq_bind, Option.bind_eq_some_iff]
    refine ⟨⟨F, SMTType.fun τ.toSMTType SMTType.bool, hF⟩,
      ?_, ?_⟩
    · simpa only [proof_irrel_heq] using hdenA'
    · rw [Option.bind_eq_some_iff]
      refine ⟨Y, ?_, ?_⟩
      · simpa only [proof_irrel_heq] using hden_var
      · simp only [dif_pos hY_ty.symm,
          dif_pos (is_func_is_pfunc hF_func), dif_pos hY_dom,
          denApp]
  have respects_app :
      SMT.RenamingContext.RespectsTypeContextOnFV Θ' Γsup
        (.app S (.var helper)) := by
    intro v ξ hv hlookup
    rw [SMT.fv, List.mem_append] at hv
    exact hv.elim (fun h => respects_S' h hlookup)
      (fun h => respects_var h hlookup)
  have hcov_t : SMT.RenamingContext.CoversFV Θ'
      (spec ∧ˢ .app S (.var helper)) := by
    intro v hv
    rw [SMT.fv, List.mem_append] at hv
    exact hv.elim (hcov_spec v) (hcov_app v)
  have respects_t :
      SMT.RenamingContext.RespectsTypeContextOnFV Θ' Γsup
        (spec ∧ˢ .app S (.var helper)) := by
    intro v ξ hv hlookup
    rw [SMT.fv, List.mem_append] at hv
    exact hv.elim (fun h => respects_spec h hlookup)
      (fun h => respects_app h hlookup)
  have hΦ_mem_bool : Φ.fst ∈ ⟦SMTType.bool⟧ᶻ := by
    rw [← hΦ_ty]
    exact Φ.snd.snd
  rcases Φ with ⟨Φv, ⟨Φσ, hΦv⟩⟩
  dsimp at hΦ_ty
  subst Φσ
  change Φv = ZFSet.zftrue at hΦ_true
  have hΦv_true : Φv = ZFSet.zftrue := by
    simpa only using hΦ_true
  let denM : SMT.Dom.{u} :=
    ⟨Φv ⋀ᶻ denApp.fst, SMTType.bool,
      EncodeTermRepresentedBool.CheckedOp.eval_mem .and
        hΦ_mem_bool denApp.snd.snd⟩
  have hdenM : ⟦(spec ∧ˢ .app S (.var helper)).abstract
      Θ' hcov_t⟧ˢ = some denM := by
    rw [SMT.Term.abstract, SMT.denote, Option.pure_def,
      Option.bind_eq_bind, Option.bind_eq_some_iff]
    refine ⟨(⟨Φv, SMTType.bool, hΦv⟩ : SMT.Dom), hden_spec, ?_⟩
    rw [Option.bind_eq_some_iff]
    refine ⟨denApp, hden_app, ?_⟩
    rfl
  have hiff_app : denApp.fst = ZFSet.zftrue ↔ X ∈ A := by
    dsimp [denApp]
    exact RDomCast.setPred_cast_apply_eq_zftrue_iff
      (hY := hY_mem) Xrel Arel hle.toCastPath hcast
  have hiff : denM.fst = ZFSet.zftrue ↔ X ∈ A := by
    have hdenM_app : denM.fst = denApp.fst := by
      dsimp [denM]
      rw [hΦv_true]
      rcases ZFSet.ZFBool.mem_𝔹_iff denApp.fst |>.mp denApp.snd.snd with
        hfalse | htrue
      · rw [hfalse]
        simp [overloadBinOp_𝔹, overloadBinOp]
      · rw [htrue]
        simp [overloadBinOp_𝔹, overloadBinOp]
    rw [hdenM_app]
    exact hiff_app
  have specs_true : SpecBodiesTrue Θ' Γsup
      (helperSpecChunk helper τ.toSMTType spec) := by
    intro b hb
    simp only [specBodies_helperSpecChunk, List.mem_singleton] at hb
    subst b
    exact ⟨hcov_spec, (⟨Φv, SMTType.bool, hΦv⟩ : SMT.Dom),
      respects_spec, hden_spec, rfl, hΦv_true⟩
  have Θ'_dom : ∀ v, Θ' v ≠ none → v ∈ Γsup := by
    intro v hv
    by_cases hvh : v = helper
    · subst v
      exact AList.lookup_isSome.mp (by rw [helper_lookup_sup]; rfl)
    · exact Θ_dom v (by simpa [Θ', Function.update_of_ne hvh] using hv)
  constructor
  · exact ⟨Θ', hcov_t, denM, Θ'_ext, Θ'_none, respects_t,
      Θ'_dom, specs_true, hdenM, rfl, hiff⟩
  · intro hcov_tg denMg respects_tg specs_tg hdenMg hdenMg_ty
    obtain ⟨specVal, hspecVal, hden_spec_g,
        appVal, happVal, hden_app_g, denMg_eq⟩ :=
      EncodeTermRepresentedBool.CheckedOp.smt_denote_inv
        .and hcov_tg hdenMg
    have hspec_true := specs_tg spec (by simp)
    obtain ⟨hcov_spec_g, db, _resp_db, hden_db,
      _db_ty, hdb_true⟩ := hspec_true
    have hspecDom_eq :
        (⟨specVal, SMTType.bool, hspecVal⟩ : SMT.Dom) = db := by
      have hcov_eq : hcov_spec_g =
          (fun v hv => hcov_tg v (by
            rw [SMT.fv, List.mem_append]
            exact Or.inl hv)) := Subsingleton.elim _ _
      subst hcov_spec_g
      rw [hden_spec_g] at hden_db
      exact Option.some.inj hden_db
    have hspecVal_true : specVal = ZFSet.zftrue := by
      rw [← hspecDom_eq] at hdb_true
      exact hdb_true
    have helper_some : (Θ helper).isSome = true := by
      apply hcov_tg helper
      rw [SMT.fv, List.mem_append]
      exact Or.inr (by
        rw [SMT.fv, List.mem_append]
        exact Or.inr (by simp [SMT.fv]))
    obtain ⟨Yg, hYg⟩ := Option.isSome_iff_exists.mp helper_some
    have hYg_ty : Yg.snd.fst = τ.toSMTType := by
      have helper_fv_t : helper ∈
          SMT.fv (spec ∧ˢ .app S (.var helper)) := by
        rw [SMT.fv, List.mem_append]
        exact Or.inr (by
          rw [SMT.fv, List.mem_append]
          exact Or.inr (by simp [SMT.fv]))
      obtain ⟨d, hd, hdty⟩ := respects_tg
        helper_fv_t
        (AList.lookup_of_subset Γsub helper_lookup)
      rw [hYg] at hd
      injection hd with hdeq
      subst d
      exact hdty
    have hupd : Function.update Θ helper (some Yg) = Θ := by
      rw [← hYg]
      exact Function.update_eq_self helper Θ
    have hcov_spec_upd : SMT.RenamingContext.CoversFV
        (Function.update Θ helper (some Yg)) spec := by
      rw [hupd]
      exact fun v hv => hcov_tg v (by
        rw [SMT.fv, List.mem_append]
        exact Or.inl hv)
    obtain ⟨_hsome, hcast_g⟩ := hguard Yg hYg_ty hcov_spec_upd
    have hden_spec_upd : ⟦spec.abstract
        (Function.update Θ helper (some Yg)) hcov_spec_upd⟧ˢ =
        some (⟨specVal, SMTType.bool, hspecVal⟩ : SMT.Dom) := by
      simpa only [hupd, proof_irrel_heq] using hden_spec_g
    have hcast_g' := hcast_g hden_spec_upd hspecVal_true
    have hYg_mem : Yg.fst ∈ ⟦τ.toSMTType⟧ᶻ := by
      rw [← hYg_ty]
      exact Yg.snd.snd
    have hYg_dom : Yg.fst ∈ F.Dom (is_rel_of_is_func hF_func) := by
      rw [is_func_dom_eq hF_func]
      exact hYg_mem
    have hiff_app_g :
        (fapply F (is_func_is_pfunc hF_func)
          ⟨Yg.fst, hYg_dom⟩).val =
            ZFSet.zftrue ↔ X ∈ A :=
      RDomCast.setPred_cast_apply_eq_zftrue_iff
        (hY := hYg_mem) Xrel Arel hle.toCastPath hcast_g'
    have hcov_app_g : SMT.RenamingContext.CoversFV Θ
        (.app S (.var helper)) := by
      intro v hv
      exact hcov_tg v (by
        rw [SMT.fv, List.mem_append]
        exact Or.inr hv)
    let denAppG : SMT.Dom.{u} :=
      ⟨(fapply F (is_func_is_pfunc hF_func)
        ⟨Yg.fst, hYg_dom⟩).val,
        SMTType.bool, ZFSet.fapply_mem_range _ _⟩
    have hden_app_expected :
        ⟦(SMT.Term.app S (.var helper)).abstract Θ hcov_app_g⟧ˢ =
          some denAppG := by
      rw [SMT.Term.abstract, SMT.denote, Option.pure_def,
        Option.bind_eq_bind, Option.bind_eq_some_iff]
      refine ⟨⟨F, SMTType.fun τ.toSMTType SMTType.bool, hF⟩,
        ?_, ?_⟩
      · simpa only [proof_irrel_heq] using hdenA
      · rw [Option.bind_eq_some_iff]
        refine ⟨Yg, ?_, ?_⟩
        · rw [SMT.Term.abstract]
          simp only [SMT.denote]
          congr 1
          exact Option.get_of_eq_some _ hYg
        · simp only [dif_pos hYg_ty.symm,
            dif_pos (is_func_is_pfunc hF_func),
            dif_pos hYg_dom, denAppG]
    have happVal_eq : appVal = denAppG.fst := by
      have hcov_eq : hcov_app_g =
          (fun v hv => hcov_tg v (by
            rw [SMT.fv, List.mem_append]
            exact Or.inr hv)) := Subsingleton.elim _ _
      subst hcov_app_g
      rw [hden_app_g] at hden_app_expected
      exact congrArg (fun d : SMT.Dom => d.fst)
        (Option.some.inj hden_app_expected)
    subst denMg
    subst specVal
    have happ_true : appVal = ZFSet.zftrue ↔ X ∈ A := by
      rw [happVal_eq]
      exact hiff_app_g
    rcases ZFSet.ZFBool.mem_𝔹_iff appVal |>.mp happVal with
      hfalse | htrue
    · simpa [EncodeTermRepresentedBool.CheckedOp.eval,
        overloadBinOp_𝔹, overloadBinOp, hfalse] using happ_true
    · simpa [EncodeTermRepresentedBool.CheckedOp.eval,
        overloadBinOp_𝔹, overloadBinOp, htrue] using happ_true
