import SMT.Reasoning.Basic.EncodeTermRepresentedScopedBool
import SMT.Reasoning.Basic.CastMembershipExact

open Std.Do B SMT ZFSet Classical
open SMT.SMTType

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

/-- An SMT equality denotes `zftrue` exactly when its same-typed operands
have equal underlying ZF values. -/
theorem denote_eq_fst_eq_zftrue_iff.{u}
    {t₁ t₂ : SMT.PHOAS.Term SMT.Dom.{u}}
    {D₁ D₂ Deq : SMT.Dom.{u}}
    (h₁ : ⟦t₁⟧ˢ = some D₁) (h₂ : ⟦t₂⟧ˢ = some D₂)
    (hty : D₁.snd.fst = D₂.snd.fst)
    (heq : ⟦t₁ =ˢ' t₂⟧ˢ = some Deq) :
    Deq.fst = ZFSet.zftrue ↔ D₁.fst = D₂.fst := by
  constructor
  · exact denote_eq_true_implies_fst_eq h₁ h₂ hty heq
  · intro hfst
    have htrue := denote_eq_eq_zftrue_of_fst_eq h₁ h₂ hty hfst
    rw [heq] at htrue
    exact congrArg (fun d : SMT.Dom => d.fst)
      (Option.some.inj htrue)

/-- Two Boolean denotations agree representation-wise as soon as they have
the same truth condition. -/
theorem RDomCastSupported.bool_of_true_iff.{u}
    {P Q : ZFSet.{u}} {hP : P ∈ ⟦BType.bool⟧ᶻ}
    {hQ : Q ∈ ⟦SMTType.bool⟧ᶻ}
    (hiff : P = ZFSet.zftrue ↔ Q = ZFSet.zftrue) :
    RDomCastSupported
      (⟨P, BType.bool, hP⟩ : B.Dom)
      (⟨Q, SMTType.bool, hQ⟩ : SMT.Dom) := by
  have hPQ : P = Q := by
    rcases ZFSet.ZFBool.mem_𝔹_iff P |>.mp hP with hPf | hPt
    · rcases ZFSet.ZFBool.mem_𝔹_iff Q |>.mp hQ with hQf | hQt
      · exact hPf.trans hQf.symm
      · exact False.elim (ZFSet.zftrue_ne_zffalse
          ((hiff.mpr hQt).symm.trans hPf))
    · rcases ZFSet.ZFBool.mem_𝔹_iff Q |>.mp hQ with hQf | hQt
      · exact False.elim (ZFSet.zftrue_ne_zffalse
          ((hiff.mp hPt).symm.trans hQf))
      · exact hPt.trans hQt.symm
  have hrel : RDomCast
      (⟨P, BType.bool, hP⟩ : B.Dom)
      (⟨Q, SMTType.bool, hQ⟩ : SMT.Dom) := by
    apply RDom.toRDomCast
    rw [RDom]
    refine ⟨rfl, ?_⟩
    dsimp [retract]
    exact hPQ.symm
  exact ⟨hrel.toRDomCastAdmissible_of_supported
    BType.SupportedSMT.bool, BType.SupportedSMT.bool⟩

/-- Inversion of source-level membership under its typing derivation. -/
theorem B.denote_mem_inv.{u}
    {E : B.Env} {x S : B.Term} {a : BType}
    (typ_x : E.context ⊢ᴮ x : a)
    (typ_S : E.context ⊢ᴮ S : BType.set a)
    {«Δ» : B.RenamingContext.Context}
    (Δ_fv : ∀ v ∈ B.fv (x ∈ᴮ S), («Δ» v).isSome = true)
    (wf : B.RenWF E.context «Δ»)
    {T : ZFSet.{u}} {hT : T ∈ ⟦BType.bool⟧ᶻ}
    (hden : ⟦(x ∈ᴮ S).abstract «Δ» Δ_fv⟧ᴮ =
      some ⟨T, BType.bool, hT⟩) :
    ∃ (X : ZFSet.{u}) (hX : X ∈ ⟦a⟧ᶻ)
      (A : ZFSet.{u}) (hA : A ∈ ⟦BType.set a⟧ᶻ),
      ⟦x.abstract «Δ» (fun v hv => Δ_fv v (by
        rw [B.fv, List.mem_append]; exact Or.inl hv))⟧ᴮ =
          some ⟨X, a, hX⟩ ∧
      ⟦S.abstract «Δ» (fun v hv => Δ_fv v (by
        rw [B.fv, List.mem_append]; exact Or.inr hv))⟧ᴮ =
          some ⟨A, BType.set a, hA⟩ ∧
      T = X ∈ᶻ A := by
  rw [B.Term.abstract, B.denote, Option.pure_def,
    Option.bind_eq_bind, Option.bind_eq_some_iff] at hden
  obtain ⟨⟨X, ax, hX⟩, hdenX, hrest⟩ := hden
  have hax : ax = a := by
    exact (denote_welltyped_eq
      (t := x.abstract «Δ» (fun v hv => Δ_fv v (by
        rw [B.fv, List.mem_append]; exact Or.inl hv)))
      ⟨E.context.abstract («Δ» := «Δ»), WFTC.of_abstract, a,
        Typing.of_abstract _ typ_x wf⟩ hdenX).symm
  subst ax
  rw [Option.bind_eq_some_iff] at hrest
  obtain ⟨⟨A, sA, hA⟩, hdenA, hout⟩ := hrest
  have hsA : sA = BType.set a := by
    exact (denote_welltyped_eq
      (t := S.abstract «Δ» (fun v hv => Δ_fv v (by
        rw [B.fv, List.mem_append]; exact Or.inr hv)))
      ⟨E.context.abstract («Δ» := «Δ»), WFTC.of_abstract,
        BType.set a, Typing.of_abstract _ typ_S wf⟩ hdenA).symm
  subst sA
  simp only [dif_pos True.intro] at hout
  refine ⟨X, hX, A, hA, ?_, ?_, ?_⟩
  · simpa only [proof_irrel_heq] using hdenX
  · simpa only [proof_irrel_heq] using hdenA
  · exact (congrArg (fun d : B.Dom => d.fst)
      (Option.some.inj hout)).symm

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

/-- Exactness of a completed membership cast under an arbitrary valuation of
the generated helpers.  Unlike existential helper construction, this clause
must not inherit the pre-cast support condition: re-scoping deliberately
assigns those fresh helpers before invoking it. -/
abbrev CastMembershipRepGuardedSemantics.{u}
    (τ : BType) (x S t : SMT.Term) (σx σS : SMTType)
    (Λ : SMT.TypeContext) (Dlt : SMT.Chunk) : Prop :=
  ∀ (Γsup : SMT.TypeContext), ScopedContextExtends Λ Dlt Γsup →
    ∀ (Θ : SMT.RenamingContext.Context.{u})
      (hcov_x : SMT.RenamingContext.CoversFV Θ x)
      (hcov_S : SMT.RenamingContext.CoversFV Θ S),
      SMT.RenamingContext.RespectsTypeContextOnFV Θ Γsup x →
      SMT.RenamingContext.RespectsTypeContextOnFV Θ Γsup S →
      ∀ (X A : ZFSet.{u})
        (hX : X ∈ ⟦τ⟧ᶻ) (hA : A ∈ ⟦BType.set τ⟧ᶻ)
        (denX denA : SMT.Dom.{u}),
        ⟦x.abstract Θ hcov_x⟧ˢ = some denX →
        ⟦S.abstract Θ hcov_S⟧ˢ = some denA →
        denX.snd.fst = σx → denA.snd.fst = σS →
        RDomCast (⟨X, τ, hX⟩ : B.Dom) denX →
        RDomCast (⟨A, BType.set τ, hA⟩ : B.Dom) denA →
        ∀ (hcov_t : SMT.RenamingContext.CoversFV Θ t)
          (denM : SMT.Dom.{u}),
          SMT.RenamingContext.RespectsTypeContextOnFV Θ Γsup t →
          SpecBodiesTrue Θ Γsup Dlt →
          ⟦t.abstract Θ hcov_t⟧ˢ = some denM →
          denM.snd.fst = SMTType.bool →
          (denM.fst = ZFSet.zftrue ↔ X ∈ A)

/-- Semantic contract of one completed `castMembership` run.  The first
clause constructs a satisfying helper assignment; the second proves exactness
for every assignment satisfying the generated helper guards. -/
abbrev CastMembershipRepSemantics.{u}
    (τ : BType) (x S t : SMT.Term) (σx σS : SMTType)
    (Λ Γ : SMT.TypeContext) (used₀ used₁ : List SMT.𝒱)
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
        CastMembershipRepGuardedSemantics.{u}
          τ x S t σx σS Λ Dlt

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
        SMT.fv x ⊆ SMT.fv t ∧
        SMT.fv S ⊆ SMT.fv t ∧
        (∀ v ∈ used, v ∉ Λ → v ∉ Γ') ∧
        ∃ Dlt : SMT.Chunk,
          E'.declarations = decl ++ Dlt ∧
          ContextGeneratedByDeclarations Λ Γ' Dlt ∧
          DeclarationContextTrace Λ Dlt Γ' ∧
          CastMembershipRepSemantics.{u} τ x S t σx σS Λ Γ'
            used E'.usedVars Dlt ∧
          ScopedGeneratedTyping Λ Dlt t SMTType.bool⌝⦄

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
    SMT.Typing.app _ _ _ _ _ typ_S typ_x, ?_, ?_, ?_, [], by simp,
    ContextGeneratedByDeclarations.refl _, DeclarationContextTrace.nil _,
    ?_, ?_⟩
  · intro v hv
    rw [SMT.fv, List.mem_append]
    exact Or.inr hv
  · intro v hv
    rw [SMT.fv, List.mem_append]
    exact Or.inl hv
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
    · intro Γsupg Γsubg Θg hcov_xg hcov_Sg
        _respects_xg _respects_Sg Xg Ag hXg hAg denXg denAg
        hdenXg hdenAg hdenXg_ty hdenAg_ty Xrelg Arelg
        hcov_tg denMg _respects_tg _specs_tg hdenMg _hdenMg_ty
      rcases denXg with ⟨Xg₀, σXg, hXg₀⟩
      rcases denAg with ⟨Fg, σAg, hFg⟩
      dsimp at hdenXg_ty hdenAg_ty
      subst σXg
      subst σAg
      have hcov_expected : SMT.RenamingContext.CoversFV Θg
          (.app S x) := by
        intro v hv
        rw [SMT.fv, List.mem_append] at hv
        exact hv.elim (hcov_Sg v) (hcov_xg v)
      have hFg_func : ⟦τ.toSMTType⟧ᶻ.IsFunc ZFSet.𝔹 Fg := by
        simpa [SMTType.toZFSet] using hFg
      have hXg₀_dom : Xg₀ ∈ Fg.Dom (is_rel_of_is_func hFg_func) := by
        rw [is_func_dom_eq hFg_func]
        exact hXg₀
      let denExpected : SMT.Dom.{u} :=
        ⟨(fapply Fg (is_func_is_pfunc hFg_func)
            ⟨Xg₀, hXg₀_dom⟩).val,
          SMTType.bool, ZFSet.fapply_mem_range _ _⟩
      have hdenExpected : ⟦(SMT.Term.app S x).abstract Θg
          hcov_expected⟧ˢ = some denExpected := by
        rw [SMT.Term.abstract, SMT.denote, Option.pure_def,
          Option.bind_eq_bind, Option.bind_eq_some_iff]
        refine ⟨⟨Fg, SMTType.fun τ.toSMTType SMTType.bool, hFg⟩,
          ?_, ?_⟩
        · simpa only [proof_irrel_heq] using hdenAg
        · rw [Option.bind_eq_some_iff]
          refine ⟨⟨Xg₀, τ.toSMTType, hXg₀⟩, ?_, ?_⟩
          · simpa only [proof_irrel_heq] using hdenXg
          · simp only [dif_pos True.intro,
              dif_pos (is_func_is_pfunc hFg_func),
              dif_pos hXg₀_dom, denExpected]
      have hcastg := castZF_apply_pair
        (castPath.reflexive τ.toSMTType) hXg₀
      rw [castZF_apply_reflexive τ.toSMTType hXg₀] at hcastg
      have hiffg : denExpected.fst = ZFSet.zftrue ↔ Xg ∈ Ag := by
        dsimp [denExpected]
        exact RDomCast.setPred_cast_apply_eq_zftrue_iff
          (hY := hXg₀) Xrelg Arelg
          (castPath.reflexive τ.toSMTType) hcastg
      have hcov_eq : hcov_tg = hcov_expected := Subsingleton.elim _ _
      subst hcov_tg
      have hden_eq : denExpected = denMg :=
        Option.some.inj (hdenExpected.symm.trans hdenMg)
      rw [← congrArg (fun d : SMT.Dom => d.fst) hden_eq]
      exact hiffg
  · exact ScopedGeneratedTyping.of_operational
      (ContextGeneratedByDeclarations.refl St.types)
      (SMT.Typing.app _ _ _ _ _ typ_S typ_x)
      (by simp [specBodies])

set_option maxHeartbeats 3000000 in
theorem castMembership_setPred_cast_rep_contract.{u}
    (τ : BType) (σx : SMTType) (x S : SMT.Term)
    (hle : σx ⊑ τ.toSMTType)
    (hfaith : castPath.FVFaithful hle.toCastPath)
    (hne : σx ≠ τ.toSMTType) :
    CastMembershipRepSpec.{u} τ x S σx
      (SMTType.fun τ.toSMTType SMTType.bool) := by
  unfold CastMembershipRepSpec
  intro Λ n used decl typ_x typ_S bv_x_used bv_S_used
  mstart
  mintro pre ∀St
  mpure pre
  mspec castMembership_branch2_exact_spec typ_x typ_S hne hle hfaith
    bv_x_used bv_S_used
  rename_i out
  obtain ⟨t, σ⟩ := out
  mrename_i post
  mintro ∀St'
  mpure post
  obtain ⟨_fvc, types_sub, keys_sub, used_sub, σ_eq, typ_t,
    _fv_t, preserves, _total,
    helper, spec, decl_eq, t_eq, helper_fresh, helper_not_used,
    helper_lookup, helper_ctx_eq, spec_fv, source_fv_spec, exactness⟩ := post
  change σ = SMTType.bool at σ_eq
  subst σ
  change t = spec ∧ˢ .app S (.var helper) at t_eq
  subst t
  have helper_ctx_gen : ContextGeneratedByDeclarations Λ St'.types
      (helperSpecChunk helper τ.toSMTType spec) := by
    rw [helper_ctx_eq]
    exact ContextGeneratedByDeclarations.insert_helper
      Λ helper τ.toSMTType spec helper_fresh
  have helper_ctx_trace : DeclarationContextTrace Λ
      (helperSpecChunk helper τ.toSMTType spec) St'.types := by
    rw [helper_ctx_eq]
    exact DeclarationContextTrace.helperSpecChunk
      Λ helper τ.toSMTType spec helper_fresh
  mpure_intro
  refine ⟨used_sub, types_sub, keys_sub, rfl, typ_t, ?_, ?_, preserves,
    helperSpecChunk helper τ.toSMTType spec, decl_eq, helper_ctx_gen,
    helper_ctx_trace, ?_, ?_⟩
  · intro v hv
    rw [SMT.fv, List.mem_append]
    exact Or.inl (source_fv_spec hv)
  · intro v hv
    simp only [SMT.fv, List.mem_append, List.mem_singleton]
    exact Or.inr (Or.inl hv)
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
  · intro Γsupg Γsubg Θg hcov_xg hcov_Sg respects_xg _respects_Sg
      Xg Ag hXg hAg denXg denAg hdenXg hdenAg
      hdenXg_ty hdenAg_ty Xrelg Arelg hcov_tg denMg
      respects_tg specs_tg hdenMg _hdenMg_ty
    rcases denXg with ⟨Xg₀, σXg, hXg₀⟩
    rcases denAg with ⟨Fg, σAg, hFg⟩
    dsimp at hdenXg_ty hdenAg_ty
    subst σXg
    subst σAg
    have Λ_sub_supg : Λ ⊆ Γsupg := Γsubg.base
    have respects_x_Λg :
        SMT.RenamingContext.RespectsTypeContextOnFV Θg Λ x :=
      respects_xg.of_super Λ_sub_supg
    have hpfg : ∀ (x_! : SMT.𝒱) (Y : SMT.Dom.{u}),
        ∀ v ∈ SMT.fv (SMT.Term.var x_!),
          (Function.update Θg x_! (some Y) v).isSome = true := by
      intro x_! Y v hv
      simp only [SMT.fv, List.mem_singleton] at hv
      subst v
      simp
    obtain ⟨_Φg, _Yw, _hvar_g, _hcov_spec_w, _hden_spec_w,
        _hYw_ty, _hΦg_ty, _hcast_w, hguardg⟩ :=
      exactness Θg hcov_xg respects_x_Λg hpfg
        (⟨Xg₀, σx, hXg₀⟩ : SMT.Dom) hdenXg
    have hFg_func : ⟦τ.toSMTType⟧ᶻ.IsFunc ZFSet.𝔹 Fg := by
      simpa [SMTType.toZFSet] using hFg
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
    have helper_some : (Θg helper).isSome = true := by
      apply hcov_tg helper
      rw [SMT.fv, List.mem_append]
      exact Or.inr (by
        rw [SMT.fv, List.mem_append]
        exact Or.inr (by simp [SMT.fv]))
    obtain ⟨Yg, hYg⟩ := Option.isSome_iff_exists.mp helper_some
    have helper_fv_t : helper ∈
        SMT.fv (spec ∧ˢ .app S (.var helper)) := by
      rw [SMT.fv, List.mem_append]
      exact Or.inr (by
        rw [SMT.fv, List.mem_append]
        exact Or.inr (by simp [SMT.fv]))
    have hYg_ty : Yg.snd.fst = τ.toSMTType := by
      have helper_lookup_supg :
          Γsupg.lookup helper = some τ.toSMTType :=
        Γsubg.lookup_of_declared (by
          simp [declEntries_helperSpecChunk])
      obtain ⟨d, hd, hdty⟩ := respects_tg helper_fv_t
        helper_lookup_supg
      rw [hYg] at hd
      injection hd with hdeq
      subst d
      exact hdty
    have hupd : Function.update Θg helper (some Yg) = Θg := by
      rw [← hYg]
      exact Function.update_eq_self helper Θg
    have hcov_spec_upd : SMT.RenamingContext.CoversFV
        (Function.update Θg helper (some Yg)) spec := by
      rw [hupd]
      exact fun v hv => hcov_tg v (by
        rw [SMT.fv, List.mem_append]
        exact Or.inl hv)
    obtain ⟨_hsome, hcast_g⟩ := hguardg Yg hYg_ty hcov_spec_upd
    have hden_spec_upd : ⟦spec.abstract
        (Function.update Θg helper (some Yg)) hcov_spec_upd⟧ˢ =
        some (⟨specVal, SMTType.bool, hspecVal⟩ : SMT.Dom) := by
      simpa only [hupd, proof_irrel_heq] using hden_spec_g
    have hcast_g' := hcast_g hden_spec_upd hspecVal_true
    have hYg_mem : Yg.fst ∈ ⟦τ.toSMTType⟧ᶻ := by
      rw [← hYg_ty]
      exact Yg.snd.snd
    have hYg_dom : Yg.fst ∈ Fg.Dom (is_rel_of_is_func hFg_func) := by
      rw [is_func_dom_eq hFg_func]
      exact hYg_mem
    have hiff_app_g :
        (fapply Fg (is_func_is_pfunc hFg_func)
          ⟨Yg.fst, hYg_dom⟩).val = ZFSet.zftrue ↔ Xg ∈ Ag :=
      RDomCast.setPred_cast_apply_eq_zftrue_iff
        (hY := hYg_mem) Xrelg Arelg hle.toCastPath hcast_g'
    have hcov_app_g : SMT.RenamingContext.CoversFV Θg
        (.app S (.var helper)) := by
      intro v hv
      exact hcov_tg v (by
        rw [SMT.fv, List.mem_append]
        exact Or.inr hv)
    let denAppG : SMT.Dom.{u} :=
      ⟨(fapply Fg (is_func_is_pfunc hFg_func)
        ⟨Yg.fst, hYg_dom⟩).val,
        SMTType.bool, ZFSet.fapply_mem_range _ _⟩
    have hden_app_expected :
        ⟦(SMT.Term.app S (.var helper)).abstract Θg hcov_app_g⟧ˢ =
          some denAppG := by
      rw [SMT.Term.abstract, SMT.denote, Option.pure_def,
        Option.bind_eq_bind, Option.bind_eq_some_iff]
      refine ⟨⟨Fg, SMTType.fun τ.toSMTType SMTType.bool, hFg⟩,
        ?_, ?_⟩
      · simpa only [proof_irrel_heq] using hdenAg
      · rw [Option.bind_eq_some_iff]
        refine ⟨Yg, ?_, ?_⟩
        · rw [SMT.Term.abstract]
          simp only [SMT.denote]
          congr 1
          exact Option.get_of_eq_some _ hYg
        · simp only [dif_pos hYg_ty.symm,
            dif_pos (is_func_is_pfunc hFg_func),
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
    have happ_true : appVal = ZFSet.zftrue ↔ Xg ∈ Ag := by
      rw [happVal_eq]
      exact hiff_app_g
    rcases ZFSet.ZFBool.mem_𝔹_iff appVal |>.mp happVal with
      hfalse | htrue
    · simpa [EncodeTermRepresentedBool.CheckedOp.eval,
        overloadBinOp_𝔹, overloadBinOp, hfalse] using happ_true
    · simpa [EncodeTermRepresentedBool.CheckedOp.eval,
        overloadBinOp_𝔹, overloadBinOp, htrue] using happ_true
  · apply ScopedGeneratedTyping.of_operational helper_ctx_gen typ_t
    intro b hb
    simp only [specBodies_helperSpecChunk, List.mem_singleton] at hb
    subst b
    exact (SMT.Typing.andE typ_t).2.1

set_option maxHeartbeats 4000000 in
theorem castMembership_option_rep_contract.{u}
    (a b : BType) (sa sb : SMTType) (x S : SMT.Term)
    (ha_le : sa ⊑ a.toSMTType) (hb_le : sb ⊑ b.toSMTType)
    (hfaith : castPath.FVFaithful
      (.pair ha_le.toCastPath hb_le.toCastPath)) :
    CastMembershipRepSpec.{u} (a ×ᴮ b) x S (.pair sa sb)
      (.fun a.toSMTType (.option b.toSMTType)) := by
  unfold CastMembershipRepSpec
  intro Λ n used decl typ_x typ_S bv_x_used bv_S_used
  mstart
  mintro pre ∀St
  mpure pre
  mspec castMembership_option_exact_spec typ_x typ_S ha_le hb_le hfaith
    bv_x_used bv_S_used
  rename_i out
  obtain ⟨t, σ⟩ := out
  mrename_i post
  mintro ∀St'
  mpure post
  obtain ⟨_fvc, types_sub, keys_sub, used_sub, σ_eq, typ_t,
    _fv_t, preserves, _total,
    helper, spec, decl_eq, t_eq, helper_fresh, helper_not_used,
    helper_lookup, helper_ctx_eq, spec_fv, source_fv_spec, exactness⟩ := post
  change σ = SMTType.bool at σ_eq
  subst σ
  change t = spec ∧ˢ
    ((.app S (.fst (.var helper))) =ˢ (.some (.snd (.var helper)))) at t_eq
  subst t
  have helper_ctx_gen : ContextGeneratedByDeclarations Λ St'.types
      (helperSpecChunk helper (.pair a.toSMTType b.toSMTType) spec) := by
    rw [helper_ctx_eq]
    exact ContextGeneratedByDeclarations.insert_helper Λ helper
      (.pair a.toSMTType b.toSMTType) spec helper_fresh
  have helper_ctx_trace : DeclarationContextTrace Λ
      (helperSpecChunk helper (.pair a.toSMTType b.toSMTType) spec)
      St'.types := by
    rw [helper_ctx_eq]
    exact DeclarationContextTrace.helperSpecChunk Λ helper
      (.pair a.toSMTType b.toSMTType) spec helper_fresh
  mpure_intro
  refine ⟨used_sub, types_sub, keys_sub, rfl, typ_t, ?_, ?_, preserves,
    helperSpecChunk helper (.pair a.toSMTType b.toSMTType) spec,
    decl_eq, helper_ctx_gen, helper_ctx_trace, ?_, ?_⟩
  · intro v hv
    rw [SMT.fv, List.mem_append]
    exact Or.inl (source_fv_spec hv)
  · intro v hv
    simp only [SMT.fv, List.mem_append, List.mem_singleton]
    exact Or.inr (Or.inl (Or.inl hv))
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
      (⟨X₀, .pair sa sb, hX₀⟩ : SMT.Dom) hdenX
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
  have helper_lookup_sup : Γsup.lookup helper =
      some (.pair a.toSMTType b.toSMTType) :=
    AList.lookup_of_subset Γsub helper_lookup
  have respects_spec :
      SMT.RenamingContext.RespectsTypeContextOnFV Θ' Γsup spec :=
    SMT.RenamingContext.respects_update_helper spec_fv respects_x
      helper_lookup_sup hY_ty
  have respects_S' :
      SMT.RenamingContext.RespectsTypeContextOnFV Θ' Γsup S := by
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
      some (⟨F, .fun a.toSMTType (.option b.toSMTType), hF⟩ : SMT.Dom) := by
    have hagree := SMT.RenamingContext.agreesOnFV_of_extends_of_coversFV
      Θ'_ext hcov_S
    exact (SMT.RenamingContext.denote_congr_of_agreesOnFV
      (t := S) (h1 := hcov_S') (h2 := hcov_S) hagree).trans hdenA
  have hcov_var : SMT.RenamingContext.CoversFV Θ' (.var helper) := by
    intro v hv
    simp only [SMT.fv, List.mem_singleton] at hv
    subst v
    simp [Θ']
  have hden_var' : ⟦(SMT.Term.var helper).abstract Θ' hcov_var⟧ˢ =
      some Y := by
    simpa only [Θ', proof_irrel_heq] using hden_var
  have respects_var :
      SMT.RenamingContext.RespectsTypeContextOnFV Θ' Γsup
        (.var helper) := by
    intro v ξ hv hlookup
    simp only [SMT.fv, List.mem_singleton] at hv
    subst v
    rw [helper_lookup_sup] at hlookup
    cases hlookup
    exact ⟨Y, by simp [Θ'], hY_ty⟩
  have hY_mem : Y.fst ∈
      ⟦SMTType.pair a.toSMTType b.toSMTType⟧ᶻ := by
    rw [← hY_ty]
    exact Y.snd.snd
  have hY_eta : Y.fst = Y.fst.π₁.pair Y.fst.π₂ :=
    ZFSet.pair_eta hY_mem
  have hY_parts : Y.fst.π₁ ∈ ⟦a.toSMTType⟧ᶻ ∧
      Y.fst.π₂ ∈ ⟦b.toSMTType⟧ᶻ :=
    ZFSet.pair_mem_prod.mp (hY_eta ▸ hY_mem)
  let denFst : SMT.Dom.{u} :=
    ⟨Y.fst.π₁, a.toSMTType, hY_parts.1⟩
  let denSnd : SMT.Dom.{u} :=
    ⟨Y.fst.π₂, b.toSMTType, hY_parts.2⟩
  have hcov_fst : SMT.RenamingContext.CoversFV Θ'
      (.fst (.var helper)) := by
    intro v hv
    exact hcov_var v (by simpa only [SMT.fv] using hv)
  have hcov_snd : SMT.RenamingContext.CoversFV Θ'
      (.snd (.var helper)) := by
    intro v hv
    exact hcov_var v (by simpa only [SMT.fv] using hv)
  have hden_fst : ⟦(SMT.Term.fst (.var helper)).abstract
      Θ' hcov_fst⟧ˢ = some denFst := by
    rw [SMT.Term.abstract, SMT.denote, Option.pure_def,
      Option.bind_eq_bind]
    rw [hden_var']
    cases Y with
    | mk Yv Yty =>
      rcases Yty with ⟨Yσ, hYv⟩
      dsimp at hY_ty
      subst Yσ
      rfl
  have hden_snd : ⟦(SMT.Term.snd (.var helper)).abstract
      Θ' hcov_snd⟧ˢ = some denSnd := by
    rw [SMT.Term.abstract, SMT.denote, Option.pure_def,
      Option.bind_eq_bind]
    rw [hden_var']
    cases Y with
    | mk Yv Yty =>
      rcases Yty with ⟨Yσ, hYv⟩
      dsimp at hY_ty
      subst Yσ
      rfl
  have hF_func : ⟦a.toSMTType⟧ᶻ.IsFunc
      ⟦SMTType.option b.toSMTType⟧ᶻ F := by
    simpa [SMTType.toZFSet] using hF
  have hYa_dom : Y.fst.π₁ ∈ F.Dom (is_rel_of_is_func hF_func) := by
    rw [is_func_dom_eq hF_func]
    exact hY_parts.1
  let denApp : SMT.Dom.{u} :=
    ⟨(fapply F (is_func_is_pfunc hF_func)
        ⟨Y.fst.π₁, hYa_dom⟩).val,
      .option b.toSMTType, ZFSet.fapply_mem_range _ _⟩
  let someY := ZFSet.Option.some
    (S := ⟦b.toSMTType⟧ᶻ) ⟨Y.fst.π₂, hY_parts.2⟩
  let denSome : SMT.Dom.{u} :=
    ⟨someY.val, .option b.toSMTType, someY.property⟩
  have hcov_app : SMT.RenamingContext.CoversFV Θ'
      (.app S (.fst (.var helper))) := by
    intro v hv
    rw [SMT.fv, List.mem_append] at hv
    exact hv.elim (hcov_S' v) (hcov_fst v)
  have hden_app : ⟦(SMT.Term.app S (.fst (.var helper))).abstract
      Θ' hcov_app⟧ˢ = some denApp := by
    rw [SMT.Term.abstract, SMT.denote, Option.pure_def,
      Option.bind_eq_bind, Option.bind_eq_some_iff]
    refine ⟨⟨F, .fun a.toSMTType (.option b.toSMTType), hF⟩,
      ?_, ?_⟩
    · simpa only [proof_irrel_heq] using hdenA'
    · rw [Option.bind_eq_some_iff]
      refine ⟨denFst, ?_, ?_⟩
      · simpa only [proof_irrel_heq] using hden_fst
      · simp only [dif_pos True.intro, dif_pos (is_func_is_pfunc hF_func),
          dif_pos hYa_dom, denFst, denApp]
  have hcov_some : SMT.RenamingContext.CoversFV Θ'
      (.some (.snd (.var helper))) := by
    intro v hv
    exact hcov_snd v (by simpa only [SMT.fv] using hv)
  have hden_some : ⟦(SMT.Term.some (.snd (.var helper))).abstract
      Θ' hcov_some⟧ˢ = some denSome := by
    rw [SMT.Term.abstract, SMT.denote, Option.pure_def,
      Option.bind_eq_bind]
    rw [hden_snd]
    rfl
  let eqTerm :=
    (SMT.Term.app S (.fst (.var helper))) =ˢ
      (SMT.Term.some (.snd (.var helper)))
  have hcov_eq : SMT.RenamingContext.CoversFV Θ' eqTerm := by
    intro v hv
    simp only [eqTerm, SMT.fv, List.mem_append] at hv
    rcases hv with (hS | hv) | hv
    · exact hcov_S' v hS
    · exact hcov_var v (by simpa only [SMT.fv] using hv)
    · exact hcov_var v (by simpa only [SMT.fv] using hv)
  have respects_eq :
      SMT.RenamingContext.RespectsTypeContextOnFV Θ' Γsup eqTerm := by
    intro v ξ hv hlookup
    simp only [eqTerm, SMT.fv, List.mem_append] at hv
    rcases hv with (hS | hv) | hv
    · exact respects_S' hS hlookup
    · exact respects_var (by simpa only [SMT.fv] using hv) hlookup
    · exact respects_var (by simpa only [SMT.fv] using hv) hlookup
  obtain ⟨denEq, hden_eq_raw, hdenEq_ty⟩ :=
    denote_eq_some_of_some hden_app hden_some rfl
  have hden_eq : ⟦eqTerm.abstract Θ' hcov_eq⟧ˢ = some denEq := by
    dsimp only [eqTerm]
    rw [SMT.Term.abstract]
    simpa only [proof_irrel_heq] using hden_eq_raw
  have hsem : zfEqIn ⟦SMTType.option b.toSMTType⟧ᶻ
      denApp.fst denSome.fst = ZFSet.zftrue ↔ X ∈ A := by
    simpa only [denApp, denSome, someY, proof_irrel_heq] using
      (RDomCast.optionFunction_cast_eq_some_eq_zftrue_iff
        (hY := hY_mem) Xrel Arel
          (.pair ha_le.toCastPath hb_le.toCastPath) hcast)
  have hiff_eq : denEq.fst = ZFSet.zftrue ↔ X ∈ A :=
    (denote_eq_fst_eq_zftrue_iff hden_app hden_some rfl
      hden_eq_raw).trans
      ((zfEqIn_eq_zftrue_iff denApp.snd.snd denSome.snd.snd).symm.trans
        hsem)
  have hcov_t : SMT.RenamingContext.CoversFV Θ'
      (spec ∧ˢ eqTerm) := by
    intro v hv
    rw [SMT.fv, List.mem_append] at hv
    exact hv.elim (hcov_spec v) (hcov_eq v)
  have respects_t :
      SMT.RenamingContext.RespectsTypeContextOnFV Θ' Γsup
        (spec ∧ˢ eqTerm) := by
    intro v ξ hv hlookup
    rw [SMT.fv, List.mem_append] at hv
    exact hv.elim (fun h => respects_spec h hlookup)
      (fun h => respects_eq h hlookup)
  have hΦ_mem_bool : Φ.fst ∈ ⟦SMTType.bool⟧ᶻ := by
    rw [← hΦ_ty]
    exact Φ.snd.snd
  have hEq_mem_bool : denEq.fst ∈ ⟦SMTType.bool⟧ᶻ := by
    rw [← hdenEq_ty]
    exact denEq.snd.snd
  rcases Φ with ⟨Φv, ⟨Φσ, hΦv⟩⟩
  dsimp at hΦ_ty
  subst Φσ
  change Φv = ZFSet.zftrue at hΦ_true
  rcases denEq with ⟨Eqv, ⟨Eqσ, hEqv⟩⟩
  dsimp at hdenEq_ty
  subst Eqσ
  let denM : SMT.Dom.{u} :=
    ⟨Φv ⋀ᶻ Eqv, SMTType.bool,
      EncodeTermRepresentedBool.CheckedOp.eval_mem .and
        hΦ_mem_bool hEq_mem_bool⟩
  have hdenM : ⟦(spec ∧ˢ eqTerm).abstract Θ' hcov_t⟧ˢ =
      some denM := by
    rw [SMT.Term.abstract, SMT.denote, Option.pure_def,
      Option.bind_eq_bind, Option.bind_eq_some_iff]
    refine ⟨(⟨Φv, SMTType.bool, hΦv⟩ : SMT.Dom), hden_spec, ?_⟩
    rw [Option.bind_eq_some_iff]
    refine ⟨(⟨Eqv, SMTType.bool, hEqv⟩ : SMT.Dom), hden_eq, ?_⟩
    rfl
  have hiff : denM.fst = ZFSet.zftrue ↔ X ∈ A := by
    have hdenM_eq : denM.fst = Eqv := by
      dsimp [denM]
      rw [hΦ_true]
      rcases ZFSet.ZFBool.mem_𝔹_iff Eqv |>.mp hEqv with
        hfalse | htrue
      · rw [hfalse]
        simp [overloadBinOp_𝔹, overloadBinOp]
      · rw [htrue]
        simp [overloadBinOp_𝔹, overloadBinOp]
    rw [hdenM_eq]
    exact hiff_eq
  have specs_true : SpecBodiesTrue Θ' Γsup
      (helperSpecChunk helper (.pair a.toSMTType b.toSMTType) spec) := by
    intro body hbody
    simp only [specBodies_helperSpecChunk, List.mem_singleton] at hbody
    subst body
    exact ⟨hcov_spec, (⟨Φv, SMTType.bool, hΦv⟩ : SMT.Dom),
      respects_spec, hden_spec, rfl, hΦ_true⟩
  have Θ'_dom : ∀ v, Θ' v ≠ none → v ∈ Γsup := by
    intro v hv
    by_cases hvh : v = helper
    · subst v
      exact AList.lookup_isSome.mp (by rw [helper_lookup_sup]; rfl)
    · exact Θ_dom v (by simpa [Θ', Function.update_of_ne hvh] using hv)
  constructor
  · exact ⟨Θ', hcov_t, denM, Θ'_ext, Θ'_none, respects_t,
      Θ'_dom, specs_true, hdenM, rfl, hiff⟩
  · intro Γsupg Γsubg Θg hcov_xg hcov_Sg respects_xg _respects_Sg
      Xg Ag hXg hAg denXg denAg hdenXg hdenAg
      hdenXg_ty hdenAg_ty Xrelg Arelg hcov_tg denMg
      respects_tg specs_tg hdenMg _hdenMg_ty
    rcases denXg with ⟨Xg₀, σXg, hXg₀⟩
    rcases denAg with ⟨Fg, σAg, hFg⟩
    dsimp at hdenXg_ty hdenAg_ty
    subst σXg
    subst σAg
    have Λ_sub_supg : Λ ⊆ Γsupg := Γsubg.base
    have respects_x_Λg :
        SMT.RenamingContext.RespectsTypeContextOnFV Θg Λ x :=
      respects_xg.of_super Λ_sub_supg
    have hpfg : ∀ (x_! : SMT.𝒱) (Y : SMT.Dom.{u}),
        ∀ v ∈ SMT.fv (SMT.Term.var x_!),
          (Function.update Θg x_! (some Y) v).isSome = true := by
      intro x_! Y v hv
      simp only [SMT.fv, List.mem_singleton] at hv
      subst v
      simp
    obtain ⟨_Φg, _Yw, _hvar_g, _hcov_spec_w, _hden_spec_w,
        _hYw_ty, _hΦg_ty, _hcast_w, hguardg⟩ :=
      exactness Θg hcov_xg respects_x_Λg hpfg
        (⟨Xg₀, .pair sa sb, hXg₀⟩ : SMT.Dom) hdenXg
    have hFg_func : ⟦a.toSMTType⟧ᶻ.IsFunc
        ⟦SMTType.option b.toSMTType⟧ᶻ Fg := by
      simpa [SMTType.toZFSet] using hFg
    obtain ⟨specVal, hspecVal, hden_spec_g,
        eqVal, heqVal, hden_eq_g, denMg_eq⟩ :=
      EncodeTermRepresentedBool.CheckedOp.smt_denote_inv
        .and hcov_tg hdenMg
    have hspec_true := specs_tg spec (by simp)
    obtain ⟨hcov_spec_g, db, _resp_db, hden_db,
      _db_ty, hdb_true⟩ := hspec_true
    have hspecDom_eq :
        (⟨specVal, SMTType.bool, hspecVal⟩ : SMT.Dom) = db := by
      have hcov_eq' : hcov_spec_g =
          (fun v hv => hcov_tg v (by
            rw [SMT.fv, List.mem_append]
            exact Or.inl hv)) := Subsingleton.elim _ _
      subst hcov_spec_g
      rw [hden_spec_g] at hden_db
      exact Option.some.inj hden_db
    have hspecVal_true : specVal = ZFSet.zftrue := by
      rw [← hspecDom_eq] at hdb_true
      exact hdb_true
    have helper_some : (Θg helper).isSome = true := by
      apply hcov_tg helper
      simp [SMT.fv]
    obtain ⟨Yg, hYg⟩ := Option.isSome_iff_exists.mp helper_some
    have helper_fv_t : helper ∈ SMT.fv (spec ∧ˢ eqTerm) := by
      simp [eqTerm, SMT.fv]
    have hYg_ty : Yg.snd.fst =
        SMTType.pair a.toSMTType b.toSMTType := by
      have helper_lookup_supg : Γsupg.lookup helper =
          some (SMTType.pair a.toSMTType b.toSMTType) :=
        Γsubg.lookup_of_declared (by
          simp [declEntries_helperSpecChunk])
      obtain ⟨d, hd, hdty⟩ := respects_tg helper_fv_t
        helper_lookup_supg
      rw [hYg] at hd
      injection hd with hdeq
      subst d
      exact hdty
    have hupd : Function.update Θg helper (some Yg) = Θg := by
      rw [← hYg]
      exact Function.update_eq_self helper Θg
    have hcov_spec_upd : SMT.RenamingContext.CoversFV
        (Function.update Θg helper (some Yg)) spec := by
      simpa only [hupd] using (fun v hv => hcov_tg v (by
        rw [SMT.fv, List.mem_append]
        exact Or.inl hv))
    obtain ⟨_hsome, hcast_g⟩ := hguardg Yg hYg_ty hcov_spec_upd
    have hden_spec_upd : ⟦spec.abstract
        (Function.update Θg helper (some Yg)) hcov_spec_upd⟧ˢ =
        some (⟨specVal, SMTType.bool, hspecVal⟩ : SMT.Dom) := by
      simpa only [hupd, proof_irrel_heq] using hden_spec_g
    have hcast_g' := hcast_g hden_spec_upd hspecVal_true
    have hYg_mem : Yg.fst ∈
        ⟦SMTType.pair a.toSMTType b.toSMTType⟧ᶻ := by
      rw [← hYg_ty]
      exact Yg.snd.snd
    have hYg_eta : Yg.fst = Yg.fst.π₁.pair Yg.fst.π₂ :=
      ZFSet.pair_eta hYg_mem
    have hYg_parts : Yg.fst.π₁ ∈ ⟦a.toSMTType⟧ᶻ ∧
        Yg.fst.π₂ ∈ ⟦b.toSMTType⟧ᶻ :=
      ZFSet.pair_mem_prod.mp (hYg_eta ▸ hYg_mem)
    have hYga_dom : Yg.fst.π₁ ∈
        Fg.Dom (is_rel_of_is_func hFg_func) := by
      rw [is_func_dom_eq hFg_func]
      exact hYg_parts.1
    let denFstG : SMT.Dom.{u} :=
      ⟨Yg.fst.π₁, a.toSMTType, hYg_parts.1⟩
    let denSndG : SMT.Dom.{u} :=
      ⟨Yg.fst.π₂, b.toSMTType, hYg_parts.2⟩
    let denAppG : SMT.Dom.{u} :=
      ⟨(fapply Fg (is_func_is_pfunc hFg_func)
          ⟨Yg.fst.π₁, hYga_dom⟩).val,
        .option b.toSMTType, ZFSet.fapply_mem_range _ _⟩
    let someYg := ZFSet.Option.some
      (S := ⟦b.toSMTType⟧ᶻ) ⟨Yg.fst.π₂, hYg_parts.2⟩
    let denSomeG : SMT.Dom.{u} :=
      ⟨someYg.val, .option b.toSMTType, someYg.property⟩
    have hcov_var_g : SMT.RenamingContext.CoversFV Θg (.var helper) := by
      intro v hv
      simp only [SMT.fv, List.mem_singleton] at hv
      subst v
      simp [hYg]
    have hden_var_g : ⟦(SMT.Term.var helper).abstract Θg hcov_var_g⟧ˢ =
        some Yg := by
      rw [SMT.Term.abstract]
      simp only [SMT.denote]
      congr 1
      exact Option.get_of_eq_some _ hYg
    have hcov_fst_g : SMT.RenamingContext.CoversFV Θg
        (.fst (.var helper)) := by
      intro v hv
      exact hcov_var_g v (by simpa only [SMT.fv] using hv)
    have hcov_snd_g : SMT.RenamingContext.CoversFV Θg
        (.snd (.var helper)) := by
      intro v hv
      exact hcov_var_g v (by simpa only [SMT.fv] using hv)
    have hden_fst_g : ⟦(SMT.Term.fst (.var helper)).abstract
        Θg hcov_fst_g⟧ˢ = some denFstG := by
      rw [SMT.Term.abstract, SMT.denote, Option.pure_def,
        Option.bind_eq_bind, hden_var_g]
      cases Yg with
      | mk Ygv Ygty =>
        rcases Ygty with ⟨Ygσ, hYgv⟩
        dsimp at hYg_ty
        subst Ygσ
        rfl
    have hden_snd_g : ⟦(SMT.Term.snd (.var helper)).abstract
        Θg hcov_snd_g⟧ˢ = some denSndG := by
      rw [SMT.Term.abstract, SMT.denote, Option.pure_def,
        Option.bind_eq_bind, hden_var_g]
      cases Yg with
      | mk Ygv Ygty =>
        rcases Ygty with ⟨Ygσ, hYgv⟩
        dsimp at hYg_ty
        subst Ygσ
        rfl
    have hcov_app_g : SMT.RenamingContext.CoversFV Θg
        (.app S (.fst (.var helper))) := by
      intro v hv
      exact hcov_tg v (by
        rw [SMT.fv, List.mem_append]
        exact Or.inr (by
          rw [SMT.fv, List.mem_append]
          exact Or.inl hv))
    have hden_app_g : ⟦(SMT.Term.app S (.fst (.var helper))).abstract
        Θg hcov_app_g⟧ˢ = some denAppG := by
      rw [SMT.Term.abstract, SMT.denote, Option.pure_def,
        Option.bind_eq_bind, Option.bind_eq_some_iff]
      refine ⟨⟨Fg, .fun a.toSMTType (.option b.toSMTType), hFg⟩,
        ?_, ?_⟩
      · simpa only [proof_irrel_heq] using hdenAg
      · rw [Option.bind_eq_some_iff]
        refine ⟨denFstG, ?_, ?_⟩
        · simpa only [proof_irrel_heq] using hden_fst_g
        · simp only [dif_pos True.intro,
            dif_pos (is_func_is_pfunc hFg_func),
            dif_pos hYga_dom, denFstG, denAppG]
    have hcov_some_g : SMT.RenamingContext.CoversFV Θg
        (.some (.snd (.var helper))) := by
      intro v hv
      exact hcov_snd_g v (by simpa only [SMT.fv] using hv)
    have hden_some_g : ⟦(SMT.Term.some (.snd (.var helper))).abstract
        Θg hcov_some_g⟧ˢ = some denSomeG := by
      rw [SMT.Term.abstract, SMT.denote, Option.pure_def,
        Option.bind_eq_bind, hden_snd_g]
      rfl
    have hcov_eq_g : SMT.RenamingContext.CoversFV Θg eqTerm := by
      intro v hv
      exact hcov_tg v (by
        rw [SMT.fv, List.mem_append]
        exact Or.inr hv)
    have hden_eq_raw_g :
        ⟦(SMT.Term.app S (.fst (.var helper))).abstract Θg hcov_app_g =ˢ'
          (SMT.Term.some (.snd (.var helper))).abstract Θg hcov_some_g⟧ˢ =
          some (⟨eqVal, SMTType.bool, heqVal⟩ : SMT.Dom) := by
      rw [SMT.Term.abstract] at hden_eq_g
      simpa only [proof_irrel_heq] using hden_eq_g
    have hsem_g : zfEqIn ⟦SMTType.option b.toSMTType⟧ᶻ
        denAppG.fst denSomeG.fst = ZFSet.zftrue ↔ Xg ∈ Ag := by
      simpa only [denAppG, denSomeG, someYg, proof_irrel_heq] using
        (RDomCast.optionFunction_cast_eq_some_eq_zftrue_iff
          (hY := hYg_mem) Xrelg Arelg
            (.pair ha_le.toCastPath hb_le.toCastPath) hcast_g')
    have hiff_eq_g : eqVal = ZFSet.zftrue ↔ Xg ∈ Ag :=
      (denote_eq_fst_eq_zftrue_iff hden_app_g hden_some_g rfl
        hden_eq_raw_g).trans
        ((zfEqIn_eq_zftrue_iff denAppG.snd.snd
          denSomeG.snd.snd).symm.trans hsem_g)
    subst denMg
    subst specVal
    rcases ZFSet.ZFBool.mem_𝔹_iff eqVal |>.mp heqVal with
      hfalse | htrue
    · simpa [EncodeTermRepresentedBool.CheckedOp.eval,
        overloadBinOp_𝔹, overloadBinOp, hfalse] using hiff_eq_g
    · simpa [EncodeTermRepresentedBool.CheckedOp.eval,
        overloadBinOp_𝔹, overloadBinOp, htrue] using hiff_eq_g
  · apply ScopedGeneratedTyping.of_operational helper_ctx_gen typ_t
    intro body hbody
    simp only [specBodies_helperSpecChunk, List.mem_singleton] at hbody
    subst body
    exact (SMT.Typing.andE typ_t).2.1

/-- Every supported target representation admits an FV-faithful path to its
canonical representation. -/
theorem BType.SupportedSMT.nonemptyCanonicalCastPathFaithful
    {t : BType} {s : SMTType} (h : BType.SupportedSMT t s) :
    Nonempty {c : s ~> t.toSMTType // castPath.FVFaithful c} := by
  induction h with
  | int =>
      refine ⟨⟨castPath.reflexive .int, ?_⟩⟩
      exact .refl (Or.inl rfl)
  | bool =>
      refine ⟨⟨castPath.reflexive .bool, ?_⟩⟩
      exact .refl (Or.inr (Or.inl rfl))
  | prod _ _ ih₁ ih₂ =>
      refine ⟨⟨.pair ih₁.some.val ih₂.some.val, ?_⟩⟩
      exact .pair ih₁.some.property ih₂.some.property
  | setPred t =>
      refine ⟨⟨castPath.reflexive (.fun t.toSMTType .bool), ?_⟩⟩
      exact B.BType.reflexiveCast_fvFaithful (.set t)
  | optionFun a b =>
      refine ⟨⟨.graph (castPath.reflexive a.toSMTType)
        (castPath.reflexive b.toSMTType), ?_⟩⟩
      exact .graph (B.BType.reflexiveCast_fvFaithful a)
        (B.BType.reflexiveCast_fvFaithful b)

/-- A chosen canonical cast path for a supported representation. -/
noncomputable def BType.SupportedSMT.toCanonicalCastPath
    {t : BType} {s : SMTType} (h : BType.SupportedSMT t s) :
    s ~> t.toSMTType := h.nonemptyCanonicalCastPathFaithful.some.val

/-- The chosen canonical path is FV-faithful. -/
theorem BType.SupportedSMT.toCanonicalCastPath_faithful
    {t : BType} {s : SMTType} (h : BType.SupportedSMT t s) :
    castPath.FVFaithful h.toCanonicalCastPath :=
  h.nonemptyCanonicalCastPathFaithful.some.property

/-- Path uniqueness transfers FV faithfulness to the operational path selected
from any proof of castability. -/
theorem BType.SupportedSMT.toCastPath_faithful
    {t : BType} {s : SMTType} (h : BType.SupportedSMT t s)
    (hle : s ⊑ t.toSMTType) :
    castPath.FVFaithful hle.toCastPath := by
  rw [castPath.eq_of_endpoints hle.toCastPath h.toCanonicalCastPath]
  exact h.toCanonicalCastPath_faithful

/-- Select the operational membership proof from the two supported set
representations. -/
theorem castMembership_supported_rep_contract.{u}
    (t : BType) (x S : SMT.Term) (sx sS : SMTType)
    (hx : BType.SupportedSMT t sx)
    (hS : BType.SupportedSMT (BType.set t) sS) :
    CastMembershipRepSpec.{u} t x S sx sS := by
  unfold CastMembershipRepSpec
  intro Λ n used decl typ_x typ_S bv_x_used bv_S_used
  cases hS with
  | setPred t =>
      by_cases heq : sx = t.toSMTType
      · subst sx
        exact castMembership_direct_rep_contract.{u} t x S
          typ_x typ_S bv_x_used bv_S_used
      · let hle : sx ⊑ t.toSMTType :=
          castable?_of_castPath hx.toCanonicalCastPath
        exact castMembership_setPred_cast_rep_contract.{u} t sx x S hle
          (hx.toCastPath_faithful hle) heq typ_x typ_S
          bv_x_used bv_S_used
  | optionFun a b =>
      obtain ⟨sa, sb, rfl, ha, hb⟩ := hx.prodE
      let ha_le : sa ⊑ a.toSMTType :=
        castable?_of_castPath ha.toCanonicalCastPath
      let hb_le : sb ⊑ b.toSMTType :=
        castable?_of_castPath hb.toCanonicalCastPath
      exact castMembership_option_rep_contract.{u} a b sa sb x S
        ha_le hb_le (.pair (ha.toCastPath_faithful ha_le)
          (hb.toCastPath_faithful hb_le)) typ_x typ_S
          bv_x_used bv_S_used

set_option maxHeartbeats 5000000 in
theorem encodeTerm_rep_spec.mem_case.{u}
    (x S : B.Term)
    (x_ih : EncodeTermRepIH.{u} x)
    (S_ih : EncodeTermRepIH.{u} S)
    (E : B.Env) {Λ : SMT.TypeContext} {α : BType}
    (typ_t : E.context ⊢ᴮ x ∈ᴮ S : α)
    {«Δ» : B.RenamingContext.Context}
    (Δ_fv : ∀ v ∈ B.fv (x ∈ᴮ S), («Δ» v).isSome = true)
    {Δ₀ : SMT.RenamingContext.Context.{u}}
    (related : RValuationCastSupportedOnFV «Δ» Δ₀ (x ∈ᴮ S))
    {used : List SMT.𝒱}
    (Δ₀_none_out : ∀ v ∉ used, Δ₀ v = none)
    (Δ₀_dom : ∀ v, Δ₀ v ≠ none → v ∈ Λ)
    {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ}
    (den_t : ⟦(x ∈ᴮ S).abstract «Δ» Δ_fv⟧ᴮ =
      some ⟨T, α, hT⟩)
    (vars_used : ∀ v ∈ (x ∈ᴮ S).vars, v ∈ used)
    (Λ_inv : ∀ v ∈ (x ∈ᴮ S).vars,
      v ∈ Λ → v ∈ E.context)
    (bv_nodup : (B.bv (x ∈ᴮ S)).Nodup)
    (respects : B.RenamingContext.RespectsTypeContextOnFV
      Δ₀ Λ (x ∈ᴮ S))
    (fv_in_Λ : ∀ v ∈ B.fv (x ∈ᴮ S), v ∈ Λ)
    (wf : B.RenWF E.context «Δ»)
    {n : ℕ} :
    ⦃fun ⟨E₀, Λ'⟩ ↦
      ⌜Λ' = Λ ∧ E₀.freshvarsc = n ∧
        Λ.keys ⊆ E₀.usedVars ∧ E₀.usedVars = used⌝⦄
    encodeTerm (x ∈ᴮ S) E
    ⦃⇓? (⟨t', σ⟩ : SMT.Term × SMTType) ⟨E', Γ'⟩ =>
      ⌜EncodeTermRepPost (x ∈ᴮ S) α Λ «Δ» Δ₀ used T hT
        E t' σ E' Γ'⌝⦄ := by
  mstart
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
  obtain ⟨rfl, a, typ_x, typ_S⟩ := B.Typing.memE typ_t
  obtain ⟨X, hX, A, hA, den_x, den_S, T_eq⟩ :=
    B.denote_mem_inv typ_x typ_S Δ_fv wf den_t
  subst T
  rw [encodeTerm]

  have fv_x_sub : B.fv x ⊆ B.fv (x ∈ᴮ S) := by
    intro v hv
    rw [B.fv, List.mem_append]
    exact Or.inl hv
  have fv_S_sub : B.fv S ⊆ B.fv (x ∈ᴮ S) := by
    intro v hv
    rw [B.fv, List.mem_append]
    exact Or.inr hv
  have hx_bv_nodup : (B.bv x).Nodup := by
    have h := bv_nodup
    rw [B.bv, List.nodup_append] at h
    exact h.1
  have hS_bv_nodup : (B.bv S).Nodup := by
    have h := bv_nodup
    rw [B.bv, List.nodup_append] at h
    exact h.2.1
  have hxS_bv_disj : ∀ p ∈ B.bv x, ∀ q ∈ B.bv S, p ≠ q := by
    have h := bv_nodup
    rw [B.bv, List.nodup_append] at h
    exact h.2.2

  mspec (Std.Do.Triple.and _
    (Std.Do.Triple.and _
      (x_ih E typ_x
        (fun v hv => Δ_fv v (fv_x_sub hv))
        (related.mono_fv fv_x_sub)
        Δ₀_none_out Δ₀_dom den_x
        (fun v hv => vars_used v (by
          simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
            List.mem_append] at hv ⊢
          rcases hv with h | h <;> [left; right] <;> exact Or.inl h))
        (fun v hv => Λ_inv v (by
          simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
            List.mem_append] at hv ⊢
          rcases hv with h | h <;> [left; right] <;> exact Or.inl h))
        hx_bv_nodup (respects.mono_fv fv_x_sub)
        (fun v hv => fv_in_Λ v (fv_x_sub hv)) wf
        (n := St.env.freshvarsc))
      (encodeTerm_bv_used E (t := x) (used := St.env.usedVars)
        (n := St.env.freshvarsc) (decl := St.env.declarations)))
    (encodeTerm_bv_notMem_used E (t := x) (used := St.env.usedVars)
      (n := St.env.freshvarsc) (decl := St.env.declarations)))
  clear x_ih
  rename_i out_x
  obtain ⟨x_enc, sx⟩ := out_x
  mrename_i pre
  mintro ∀Stx
  mpure pre
  dsimp at pre
  obtain ⟨⟨⟨used_sub_x, types_sub_x, keys_sub_x, x_used,
      _path_x, typ_x_enc, _shape_x, x_preserves,
      Δx, hcov_x, Δx_ext, _related_x, Δx_none, _respects_x,
      target_respects_x, Δx_dom,
      denX, hden_x, hdenX_type, X_rel, x_total⟩,
      bv_x_used, _⟩,
      bv_x_not_used, _⟩ := pre
  rcases denX with ⟨Xenc, sxD, hXenc⟩
  dsimp at hdenX_type
  subst sxD

  have related_S : RValuationCastSupportedOnFV «Δ» Δx S :=
    (related.mono_fv fv_S_sub).of_extends Δx_ext
  have respects_S : B.RenamingContext.RespectsTypeContextOnFV
      Δx Stx.types S :=
    respects.of_extends Δx_ext types_sub_x fv_S_sub fv_in_Λ

  mspec (Std.Do.Triple.and _
    (S_ih E typ_S
      (fun v hv => Δ_fv v (fv_S_sub hv)) related_S
      Δx_none Δx_dom den_S
      (fun v hv => used_sub_x (vars_used v (by
        simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
          List.mem_append] at hv ⊢
        rcases hv with h | h <;> [left; right] <;> exact Or.inr h)))
      (fun v hv hΓ => by
        have hv_parent : v ∈ (x ∈ᴮ S).vars := by
          simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
            List.mem_append] at hv ⊢
          rcases hv with h | h <;> [left; right] <;> exact Or.inr h
        by_cases hv_Λ : v ∈ St.types
        · exact Λ_inv v hv_parent hv_Λ
        · have hv_vars_x : v ∈ B.Term.vars x := by
            by_contra hnot
            exact absurd hΓ
              (x_preserves v (vars_used v hv_parent) hv_Λ hnot)
          rcases B.Term.mem_vars_iff.mp hv_vars_x with hx_fv | hx_bv
          · exact B.Typing.typed_by_fv typ_x hx_fv
          · rcases B.Term.mem_vars_iff.mp hv with hS_fv | hS_bv
            · exact absurd (B.Typing.typed_by_fv typ_S hS_fv)
                (B.Typing.bv_notMem_context typ_x v hx_bv)
            · exact absurd rfl (hxS_bv_disj v hx_bv v hS_bv))
      hS_bv_nodup respects_S
      (fun v hv => AList.mem_of_subset types_sub_x
        (fv_in_Λ v (fv_S_sub hv))) wf
      (n := Stx.env.freshvarsc))
    (encodeTerm_bv_used E (t := S) (used := Stx.env.usedVars)
      (n := Stx.env.freshvarsc) (decl := Stx.env.declarations)))
  clear S_ih
  rename_i out_S
  obtain ⟨S_enc, sS⟩ := out_S
  mrename_i pre
  mintro ∀StS
  mpure pre
  dsimp at pre
  obtain ⟨⟨used_sub_S, types_sub_S, keys_sub_S, S_used,
      _path_S, typ_S_enc, _shape_S, S_preserves,
      ΔS, hcov_S, ΔS_ext, _related_S, ΔS_none, _respects_S,
      target_respects_S, ΔS_dom,
      denA, hden_S, hdenA_type, A_rel, S_total⟩,
      bv_S_used, _⟩ := pre
  rcases denA with ⟨Aenc, sSD, hAenc⟩
  dsimp at hdenA_type
  subst sSD

  have bv_x_not_final : ∀ v ∈ SMT.bv x_enc, v ∉ StS.types :=
    fun v hv => S_preserves v (bv_x_used v hv)
      (SMT.Typing.bv_notMem_context typ_x_enc v hv)
      (by
        rw [B.Term.notMem_vars_iff]
        refine ⟨?_, ?_⟩
        · intro hfv
          exact SMT.Typing.bv_notMem_context typ_x_enc v hv
            (AList.mem_of_subset types_sub_x
              (fv_in_Λ v (fv_S_sub hfv)))
        · intro hbS
          exact bv_x_not_used v hv
            (St_used_eq ▸ vars_used v (by
              apply B.Term.mem_vars_iff.mpr
              right
              rw [B.bv, List.mem_append]
              exact Or.inr hbS)))
  have typ_x_final : StS.types ⊢ˢ x_enc : sx :=
    SMT.Typing.weakening types_sub_S typ_x_enc bv_x_not_final
  have hcov_x_final : SMT.RenamingContext.CoversFV ΔS x_enc :=
    SMT.RenamingContext.coversFV_of_extends_of_coversFV ΔS_ext hcov_x
  have hden_x_final : ⟦x_enc.abstract ΔS hcov_x_final⟧ˢ =
      some (⟨Xenc, sx, hXenc⟩ : SMT.Dom) := by
    have hagree :=
      SMT.RenamingContext.agreesOnFV_of_extends_of_coversFV ΔS_ext hcov_x
    exact (SMT.RenamingContext.denote_congr_of_agreesOnFV
      (t := x_enc) (h1 := hcov_x_final) (h2 := hcov_x) hagree).trans
      hden_x
  have target_respects_x_final :
      SMT.RenamingContext.RespectsTypeContextOnFV ΔS StS.types x_enc :=
    target_respects_x.of_extends ΔS_ext types_sub_S typ_x_enc

  mspec castMembership_supported_rep_contract a x_enc S_enc sx sS
    X_rel.supported A_rel.supported typ_x_final typ_S_enc
    (fun v hv => used_sub_S (bv_x_used v hv)) bv_S_used
  rename_i out_mem
  obtain ⟨mem_enc, smem⟩ := out_mem
  mrename_i pre
  mintro ∀StM
  mpure pre
  obtain ⟨used_sub_M, types_sub_M, keys_sub_M, smem_eq,
    typ_mem, _fv_x_mem, _fv_S_mem, mem_preserves,
    Dlt, decl_eq, _mem_ctx, _mem_trace, mem_sem, _mem_sc_typing⟩ := pre
  change smem = SMTType.bool at smem_eq
  subst smem
  mpure_intro
  have ΔS_ext₀ := SMT.RenamingContext.extends_trans ΔS_ext Δx_ext
  have types_sub₀ : St.types ⊆ StM.types := fun _ h =>
    types_sub_M (types_sub_S (types_sub_x h))
  have target_respects_x_M :
      SMT.RenamingContext.RespectsTypeContextOnFV ΔS StM.types x_enc :=
    target_respects_x_final.of_extends
      (SMT.RenamingContext.extends_refl ΔS) types_sub_M typ_x_final
  have target_respects_S_M :
      SMT.RenamingContext.RespectsTypeContextOnFV ΔS StM.types S_enc :=
    target_respects_S.of_extends
      (SMT.RenamingContext.extends_refl ΔS) types_sub_M typ_S_enc
  have ΔS_dom_M : ∀ v, ΔS v ≠ none → v ∈ StM.types :=
    fun v hv => AList.mem_of_subset types_sub_M (ΔS_dom v hv)
  obtain ⟨good, guarded⟩ := mem_sem StM.types (fun _ h => h) ΔS
    hcov_x_final hcov_S ΔS_none target_respects_x_M
    target_respects_S_M ΔS_dom_M X A hX hA
    (⟨Xenc, sx, hXenc⟩ : SMT.Dom)
    (⟨Aenc, sS, hAenc⟩ : SMT.Dom)
    hden_x_final hden_S rfl rfl X_rel.toRDomCast A_rel.toRDomCast
  obtain ⟨ΔM, hcov_mem, denM, ΔM_ext, ΔM_none,
    target_respects_mem, ΔM_dom, specs_M, hden_mem,
    hdenM_type, hmem_iff⟩ := good
  have hsource_true : (X ∈ᶻ A) = ZFSet.zftrue ↔ X ∈ A := by
    by_cases hXA : X ∈ A
    · simp [overloadUnaryOp, hXA]
    · simpa [overloadUnaryOp, hXA] using
        (Ne.symm ZFSet.zftrue_ne_zffalse)
  have result_rel : RDomCastSupported
      (⟨X ∈ᶻ A, BType.bool, overloadUnaryOp_mem⟩ : B.Dom)
      denM := by
    rcases denM with ⟨Mv, Ms, hMv⟩
    dsimp at hdenM_type
    subst Ms
    exact RDomCastSupported.bool_of_true_iff
      (hsource_true.trans hmem_iff.symm)
  refine ⟨?_, ?_, keys_sub_M, ?_, ⟨castPath.reflexive .bool⟩,
    typ_mem, trivial, ?_, ΔM, hcov_mem, ?_⟩
  · intro v hv
    exact used_sub_M (used_sub_S (used_sub_x (by
      simpa [St_used_eq] using hv)))
  · exact types_sub₀
  · intro v hv
    rw [B.fv, List.mem_append] at hv
    exact hv.elim
      (fun h => used_sub_M (used_sub_S (x_used v h)))
      (fun h => used_sub_M (S_used v h))
  · intro v hv hΛ hvars hΓ
    rw [B.Term.notMem_vars_iff] at hvars
    have hvars_x : v ∉ x.vars := by
      rw [B.Term.notMem_vars_iff]
      refine ⟨?_, ?_⟩
      · exact fun h => hvars.1 (fv_x_sub h)
      · intro h
        exact hvars.2 (by rw [B.bv, List.mem_append]; exact Or.inl h)
    have hvars_S : v ∉ S.vars := by
      rw [B.Term.notMem_vars_iff]
      refine ⟨?_, ?_⟩
      · exact fun h => hvars.1 (fv_S_sub h)
      · intro h
        exact hvars.2 (by rw [B.bv, List.mem_append]; exact Or.inr h)
    have hv_not_Stx : v ∉ Stx.types := by
      intro hΓx
      by_cases hv_St : v ∈ St.types
      · exact hΛ hv_St
      · exact x_preserves v (by simpa [St_used_eq] using hv)
          hv_St hvars_x hΓx
    have hv_not_StS : v ∉ StS.types :=
      S_preserves v (used_sub_x (by simpa [St_used_eq] using hv))
        hv_not_Stx hvars_S
    exact mem_preserves v
      (used_sub_S (used_sub_x (by simpa [St_used_eq] using hv)))
      hv_not_StS hΓ
  · refine ⟨SMT.RenamingContext.extends_trans ΔM_ext ΔS_ext₀,
      related.of_extends
        (SMT.RenamingContext.extends_trans ΔM_ext ΔS_ext₀),
      ΔM_none, ?_, target_respects_mem, ΔM_dom,
      denM, hden_mem, hdenM_type, result_rel, ?_⟩
    · exact respects.of_extends
        (SMT.RenamingContext.extends_trans ΔM_ext ΔS_ext₀)
        types_sub₀ (fun _ h => h) fv_in_Λ
    · intro Δ_alt Δ_fv_alt Δ₀_alt related_alt wf_alt
        Δ₀_alt_none respects_alt Δ₀_alt_dom
        T_alt hT_alt den_t_alt
      obtain ⟨X_alt, hX_alt, A_alt, hA_alt,
          den_x_alt, den_S_alt, T_alt_eq⟩ :=
        B.denote_mem_inv typ_x typ_S Δ_fv_alt wf_alt den_t_alt
      subst T_alt
      have Δ₀_alt_none_x : ∀ v ∉ Stx.env.usedVars,
          Δ₀_alt v = none := by
        intro v hv
        by_contra hne
        have hv_Λ := Δ₀_alt_dom v hne
        have hv_used : v ∈ used := by
          simpa [← St_used_eq] using St_sub hv_Λ
        exact hv (used_sub_x hv_used)
      obtain ⟨Δx_alt, hcov_x_alt, denX_alt, Δx_alt_ext,
          _related_x_alt, Δx_alt_none, _respects_x_alt,
          target_respects_x_alt, Δx_alt_dom,
          hden_x_alt, hdenX_alt_type, X_alt_rel⟩ :=
        x_total Δ_alt
          (fun v hv => Δ_fv_alt v (fv_x_sub hv)) Δ₀_alt
          (related_alt.mono_fv fv_x_sub) wf_alt Δ₀_alt_none_x
          (respects_alt.mono_fv fv_x_sub) Δ₀_alt_dom
          X_alt hX_alt den_x_alt
      rcases denX_alt with ⟨Xenc_alt, sx_alt, hXenc_alt⟩
      dsimp at hdenX_alt_type
      subst sx_alt
      have Δx_alt_none_S : ∀ v ∉ StS.env.usedVars,
          Δx_alt v = none := by
        intro v hv
        apply Δx_alt_none v
        intro hvx
        exact hv (used_sub_S hvx)
      have related_alt_S : RValuationCastSupportedOnFV Δ_alt Δx_alt S :=
        (related_alt.mono_fv fv_S_sub).of_extends Δx_alt_ext
      have respects_alt_S :
          B.RenamingContext.RespectsTypeContextOnFV
            Δx_alt Stx.types S :=
        respects_alt.of_extends Δx_alt_ext types_sub_x
          fv_S_sub fv_in_Λ
      obtain ⟨ΔS_alt, hcov_S_alt, denA_alt, ΔS_alt_ext,
          _related_S_alt, ΔS_alt_none, _respects_S_alt,
          target_respects_S_alt, ΔS_alt_dom,
          hden_S_alt, hdenA_alt_type, A_alt_rel⟩ :=
        S_total Δ_alt
          (fun v hv => Δ_fv_alt v (fv_S_sub hv)) Δx_alt
          related_alt_S wf_alt Δx_alt_none_S respects_alt_S
          Δx_alt_dom A_alt hA_alt den_S_alt
      rcases denA_alt with ⟨Aenc_alt, sS_alt, hAenc_alt⟩
      dsimp at hdenA_alt_type
      subst sS_alt
      have hcov_x_alt_final : SMT.RenamingContext.CoversFV ΔS_alt x_enc :=
        SMT.RenamingContext.coversFV_of_extends_of_coversFV
          ΔS_alt_ext hcov_x_alt
      have hden_x_alt_final : ⟦x_enc.abstract ΔS_alt
          hcov_x_alt_final⟧ˢ =
          some (⟨Xenc_alt, sx, hXenc_alt⟩ : SMT.Dom) := by
        have hagree :=
          SMT.RenamingContext.agreesOnFV_of_extends_of_coversFV
            ΔS_alt_ext hcov_x_alt
        exact (SMT.RenamingContext.denote_congr_of_agreesOnFV
          (t := x_enc) (h1 := hcov_x_alt_final)
          (h2 := hcov_x_alt) hagree).trans hden_x_alt
      have target_respects_x_alt_final :
          SMT.RenamingContext.RespectsTypeContextOnFV
            ΔS_alt StS.types x_enc :=
        target_respects_x_alt.of_extends
          ΔS_alt_ext types_sub_S typ_x_enc
      have target_respects_x_alt_M :
          SMT.RenamingContext.RespectsTypeContextOnFV
            ΔS_alt StM.types x_enc :=
        target_respects_x_alt_final.of_extends
          (SMT.RenamingContext.extends_refl ΔS_alt)
          types_sub_M typ_x_final
      have target_respects_S_alt_M :
          SMT.RenamingContext.RespectsTypeContextOnFV
            ΔS_alt StM.types S_enc :=
        target_respects_S_alt.of_extends
          (SMT.RenamingContext.extends_refl ΔS_alt)
          types_sub_M typ_S_enc
      have ΔS_alt_dom_M : ∀ v, ΔS_alt v ≠ none → v ∈ StM.types :=
        fun v hv => AList.mem_of_subset types_sub_M (ΔS_alt_dom v hv)
      obtain ⟨good_alt, _guarded_alt⟩ := mem_sem StM.types
        (fun _ h => h) ΔS_alt hcov_x_alt_final hcov_S_alt
        ΔS_alt_none target_respects_x_alt_M target_respects_S_alt_M
        ΔS_alt_dom_M X_alt A_alt hX_alt hA_alt
        (⟨Xenc_alt, sx, hXenc_alt⟩ : SMT.Dom)
        (⟨Aenc_alt, sS, hAenc_alt⟩ : SMT.Dom)
        hden_x_alt_final hden_S_alt rfl rfl
        X_alt_rel.toRDomCast A_alt_rel.toRDomCast
      obtain ⟨ΔM_alt, hcov_M_alt, denM_alt, ΔM_alt_ext,
          ΔM_alt_none, target_respects_M_alt, ΔM_alt_dom,
          _specs_alt, hden_M_alt, hdenM_alt_type, hmem_alt_iff⟩ := good_alt
      have hsource_alt_true :
          (X_alt ∈ᶻ A_alt) = ZFSet.zftrue ↔ X_alt ∈ A_alt := by
        by_cases hXA : X_alt ∈ A_alt
        · simp [overloadUnaryOp, hXA]
        · simpa [overloadUnaryOp, hXA] using
            (Ne.symm ZFSet.zftrue_ne_zffalse)
      have result_alt_rel : RDomCastSupported
          (⟨X_alt ∈ᶻ A_alt, BType.bool,
            overloadUnaryOp_mem⟩ : B.Dom) denM_alt := by
        rcases denM_alt with ⟨Mv, Ms, hMv⟩
        dsimp at hdenM_alt_type
        subst Ms
        exact RDomCastSupported.bool_of_true_iff
          (hsource_alt_true.trans hmem_alt_iff.symm)
      have ΔS_alt_ext₀ :=
        SMT.RenamingContext.extends_trans ΔS_alt_ext Δx_alt_ext
      have ΔM_alt_ext₀ :=
        SMT.RenamingContext.extends_trans ΔM_alt_ext ΔS_alt_ext₀
      refine ⟨ΔM_alt, hcov_M_alt, denM_alt, ΔM_alt_ext₀,
        related_alt.of_extends ΔM_alt_ext₀, ΔM_alt_none, ?_,
        target_respects_M_alt, ΔM_alt_dom, hden_M_alt,
        hdenM_alt_type, result_alt_rel⟩
      exact respects_alt.of_extends ΔM_alt_ext₀ types_sub₀
        (fun _ h => h) fv_in_Λ
