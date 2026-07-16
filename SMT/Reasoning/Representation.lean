import SMT.Reasoning.Basic.AllCaseHelpers

open B SMT ZFSet

/-!
# Representation-indexed semantic agreement

`RDom` compares a B denotation only with its canonical SMT representation.
`RDomCast` additionally permits an SMT value at a less general type, provided
an explicit loosening path casts that value to the canonical SMT type before
retraction.
-/

/-- A reflexive cast acts as the identity on every well-typed SMT value. -/
theorem castZF_apply_reflexive.{u} (σ : SMTType) {Y : ZFSet.{u}}
    (hY : Y ∈ ⟦σ⟧ᶻ) :
    castZF_apply (castPath.reflexive σ) Y = Y := by
  have hpair := castZF_apply_pair (castPath.reflexive σ) hY
  rw [castZF_of_path_id, pair_mem_Id_iff hY] at hpair
  exact hpair.symm

/-- Every cast path whose source and target coincide is the canonical
reflexive path. -/
theorem castPath.eq_reflexive {σ : SMTType} (c : σ ~> σ) :
    c = castPath.reflexive σ := by
  induction σ with
  | bool =>
      cases c with
      | refl _ => rfl
  | int =>
      cases c with
      | refl _ => rfl
  | unit =>
      cases c with
      | refl _ => rfl
  | option σ ih =>
      cases c with
      | refl h =>
          rcases h with h | h | h <;> cases h
      | opt c =>
          rw [castPath.reflexive, ih c]
  | pair σ τ ihσ ihτ =>
      cases c with
      | refl h =>
          rcases h with h | h | h <;> cases h
      | pair cσ cτ =>
          rw [castPath.reflexive, ihσ cσ, ihτ cτ]
  | «fun» σ τ ihσ ihτ =>
      cases τ with
      | bool =>
          cases c with
          | refl h =>
              rcases h with h | h | h <;> cases h
          | «fun» h _ _ =>
              exact (h rfl).elim
          | chpred cσ =>
              rw [castPath.reflexive, ihσ cσ]
      | int =>
          cases c with
          | refl h =>
              rcases h with h | h | h <;> cases h
          | «fun» _ cσ cτ =>
              rw [castPath.reflexive, ihσ cσ, ihτ cτ]
              rfl
      | unit =>
          cases c with
          | refl h =>
              rcases h with h | h | h <;> cases h
          | «fun» _ cσ cτ =>
              rw [castPath.reflexive, ihσ cσ, ihτ cτ]
              rfl
      | option τ =>
          cases c with
          | refl h =>
              rcases h with h | h | h <;> cases h
          | «fun» _ cσ cτ =>
              rw [castPath.reflexive, ihσ cσ, ihτ cτ]
      | pair τ υ =>
          cases c with
          | refl h =>
              rcases h with h | h | h <;> cases h
          | «fun» _ cσ cτ =>
              rw [castPath.reflexive, ihσ cσ, ihτ cτ]
      | «fun» τ υ =>
          cases c with
          | refl h =>
              rcases h with h | h | h <;> cases h
          | «fun» _ cσ cτ =>
              rw [castPath.reflexive, ihσ cσ, ihτ cτ]

/-- A reflexive-endpoint cast acts as the identity, independently of the
particular proof object used to construct the path. -/
theorem castZF_apply_self.{u} {σ : SMTType} (c : σ ~> σ) {Y : ZFSet.{u}}
    (hY : Y ∈ ⟦σ⟧ᶻ) :
    castZF_apply c Y = Y := by
  rw [castPath.eq_reflexive c]
  exact castZF_apply_reflexive σ hY

/-- Representation-aware agreement between a B denotation and an SMT
denotation. The SMT value is first cast to the canonical SMT representation
of the B type and only then retracted. -/
def RDomCast : B.Dom → SMT.Dom → Prop
  | ⟨X, α, _⟩, ⟨Y, σ, _⟩ =>
      ∃ c : σ ~> α.toSMTType,
        retract α (castZF_apply c Y) = X

/-- A representation witness supplies both type correctness of the cast value
and the defining retraction equation. -/
theorem RDomCast.exists_cast.{u}
    {X Y : ZFSet.{u}} {α : BType} {σ : SMTType}
    {hX : X ∈ ⟦α⟧ᶻ} {hY : Y ∈ ⟦σ⟧ᶻ}
    (h : RDomCast (⟨X, α, hX⟩ : B.Dom) (⟨Y, σ, hY⟩ : SMT.Dom)) :
    ∃ c : σ ~> α.toSMTType,
      castZF_apply c Y ∈ ⟦α.toSMTType⟧ᶻ ∧
      retract α (castZF_apply c Y) = X := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, castZF_apply_mem c hY, hc⟩

/-- Ordinary canonical agreement is a special case of representation-aware
agreement. -/
theorem RDom.toRDomCast.{u} {d : B.Dom.{u}} {d' : SMT.Dom.{u}}
    (h : RDom d d') : RDomCast d d' := by
  rcases d with ⟨X, α, hX⟩
  rcases d' with ⟨Y, σ, hY⟩
  rw [RDom] at h
  obtain ⟨rfl, hret⟩ := h
  refine ⟨castPath.reflexive α.toSMTType, ?_⟩
  rwa [castZF_apply_reflexive α.toSMTType hY]

/-- At the canonical target type, representation-aware agreement is exactly
the existing `RDom` relation. -/
theorem RDomCast.iff_RDom_of_type_eq.{u}
    {X Y : ZFSet.{u}} {α : BType} {σ : SMTType}
    {hX : X ∈ ⟦α⟧ᶻ} {hY : Y ∈ ⟦σ⟧ᶻ}
    (hσ : σ = α.toSMTType) :
    RDomCast (⟨X, α, hX⟩ : B.Dom) (⟨Y, σ, hY⟩ : SMT.Dom) ↔
      RDom (⟨X, α, hX⟩ : B.Dom) (⟨Y, σ, hY⟩ : SMT.Dom) := by
  subst σ
  constructor
  · rintro ⟨c, hc⟩
    rw [RDom]
    refine ⟨rfl, ?_⟩
    rwa [castZF_apply_self c hY] at hc
  · exact RDom.toRDomCast

/-- Representation-aware agreement is stable under equality of the B-side
denotation. -/
theorem RDomCast.congr_left.{u}
    {d₁ d₂ : B.Dom.{u}} {d' : SMT.Dom.{u}}
    (h : d₁ = d₂) : RDomCast d₁ d' ↔ RDomCast d₂ d' := by
  subst d₂
  rfl

/-- Representation-aware agreement is stable under equality of the SMT-side
denotation. -/
theorem RDomCast.congr_right.{u}
    {d : B.Dom.{u}} {d₁' d₂' : SMT.Dom.{u}}
    (h : d₁' = d₂') : RDomCast d d₁' ↔ RDomCast d d₂' := by
  subst d₂'
  rfl

/-! ## Option functions and functional graphs -/

/-- The graph cast used for option-valued functions. -/
noncomputable def optionGraph.{u} (α β : SMTType) (F : ZFSet.{u}) : ZFSet.{u} :=
  castZF_apply
    (castPath.graph (castPath.reflexive α) (castPath.reflexive β)) F

/-- Collapse a functional pair-bool predicate to an option-valued function. -/
noncomputable def graphCollapse.{u} (α β : SMTType) (R : ZFSet.{u}) : ZFSet.{u} :=
  option_func_of_pfun α β R

theorem optionGraph_mem.{u} (α β : SMTType) {F : ZFSet.{u}}
    (hF : F ∈ ⟦SMTType.fun α (SMTType.option β)⟧ᶻ) :
    optionGraph α β F ∈
      ⟦SMTType.fun (SMTType.pair α β) SMTType.bool⟧ᶻ :=
  castZF_apply_mem
    (castPath.graph (castPath.reflexive α) (castPath.reflexive β)) hF

theorem graphCollapse_mem.{u} (α β : SMTType) (R : ZFSet.{u}) :
    graphCollapse α β R ∈
      ⟦SMTType.fun α (SMTType.option β)⟧ᶻ :=
  option_func_of_pfun_mem α β R

private theorem zftrue_eq_ofBool_decide_iff {P : Prop} [Decidable P] :
    zftrue = (ZFSet.ZFBool.ofBool (decide P)).val ↔ P := by
  rw [(by rfl : zftrue = (↑(⊤ : ZFBool) : ZFSet)), ← Subtype.ext_iff,
    eq_comm, ZFBool.ofBool_decide_eq_true_iff]

/-- Membership in the graph cast is exactly membership of the corresponding
`some`-valued pair in the option function. -/
theorem mem_predGraph_optionGraph_iff.{u}
    (α β : SMTType) (F : ZFSet.{u})
    (hF : F ∈ ⟦SMTType.fun α (SMTType.option β)⟧ᶻ)
    (a b : ZFSet.{u}) (ha : a ∈ ⟦α⟧ᶻ) (hb : b ∈ ⟦β⟧ᶻ) :
    a.pair b ∈ predGraph α β (optionGraph α β F) ↔
      a.pair (ZFSet.Option.some (S := ⟦β⟧ᶻ) ⟨b, hb⟩).val ∈ F := by
  have hF_func : IsFunc ⟦α⟧ᶻ ⟦SMTType.option β⟧ᶻ F := by
    rw [show ⟦SMTType.fun α (SMTType.option β)⟧ᶻ =
      ⟦α⟧ᶻ.funs ⟦SMTType.option β⟧ᶻ from rfl, mem_funs] at hF
    exact hF
  unfold predGraph
  rw [mem_sep, pair_mem_prod]
  simp only [ha, hb, and_self, true_and]
  have hpair := castZF_apply_pair
    (castPath.graph (castPath.reflexive α) (castPath.reflexive β)) hF
  change F.pair (optionGraph α β F) ∈
    (castZF_of_path
      (castPath.graph (castPath.reflexive α) (castPath.reflexive β))).1 at hpair
  rw [castZF_of_path, castZF_of_path_id, castZF_of_path_id] at hpair
  unfold castZF_graph at hpair
  rw [lambda_spec] at hpair
  obtain ⟨_, _, hEq⟩ := hpair
  rw [hEq, dif_pos hF_func, lambda_spec]
  have hab : a.pair b ∈ ⟦SMTType.pair α β⟧ᶻ :=
    pair_mem_prod.mpr ⟨ha, hb⟩
  have hx_range : (a.pair b).π₁ ∈ (𝟙⟦α⟧ᶻ : ZFSet).Range := by
    rw [range_Id]
    simpa using ha
  have hy_range : (a.pair b).π₂ ∈ (𝟙⟦β⟧ᶻ : ZFSet).Range := by
    rw [range_Id]
    simpa using hb
  simp only [hab, ZFBool.zftrue_mem_𝔹, true_and]
  rw [dite_true, dif_pos hx_range, dif_pos hy_range]
  have hx'_eq :
      Classical.choose (mem_sep.mp hx_range).2 = (a.pair b).π₁ := by
    have h_pair := (Classical.choose_spec (mem_sep.mp hx_range).2).2
    have h_dom : Classical.choose (mem_sep.mp hx_range).2 ∈ ⟦α⟧ᶻ :=
      (mem_sep.mp (Classical.choose_spec (mem_sep.mp hx_range).2).1).1
    exact (pair_mem_Id_iff h_dom).mp h_pair
  have hy'_eq :
      Classical.choose (mem_sep.mp hy_range).2 = (a.pair b).π₂ := by
    have h_pair := (Classical.choose_spec (mem_sep.mp hy_range).2).2
    have h_dom : Classical.choose (mem_sep.mp hy_range).2 ∈ ⟦β⟧ᶻ :=
      (mem_sep.mp (Classical.choose_spec (mem_sep.mp hy_range).2).1).1
    exact (pair_mem_Id_iff h_dom).mp h_pair
  have hx'_mem : Classical.choose (mem_sep.mp hx_range).2 ∈ ⟦α⟧ᶻ :=
    (mem_sep.mp (Classical.choose_spec (mem_sep.mp hx_range).2).1).1
  have hy'_mem : Classical.choose (mem_sep.mp hy_range).2 ∈ ⟦β⟧ᶻ :=
    (mem_sep.mp (Classical.choose_spec (mem_sep.mp hy_range).2).1).1
  have harg :
      (⟨Classical.choose (mem_sep.mp hx_range).2,
        by rw [is_func_dom_eq hF_func]; exact hx'_mem⟩ : {x // x ∈ F.Dom}) =
      ⟨a, by rw [is_func_dom_eq hF_func]; exact ha⟩ := by
    apply Subtype.ext
    exact hx'_eq.trans (π₁_pair a b)
  have hout :
      (⟨Classical.choose (mem_sep.mp hy_range).2, hy'_mem⟩ :
        {x // x ∈ ⟦β⟧ᶻ}) = ⟨b, hb⟩ := by
    apply Subtype.ext
    exact hy'_eq.trans (π₂_pair a b)
  rw [harg, hout, zftrue_eq_ofBool_decide_iff]
  constructor
  · intro happly
    have hdef := fapply.def (is_func_is_pfunc hF_func)
      (x := a) (by rw [is_func_dom_eq hF_func]; exact ha)
    rw [happly] at hdef
    exact hdef
  · intro hpairF
    exact fapply.of_pair (is_func_is_pfunc hF_func) hpairF

/-- The graph of every option-valued function is a partial function. -/
theorem predGraph_optionGraph_isPFunc.{u}
    (α β : SMTType) (F : ZFSet.{u})
    (hF : F ∈ ⟦SMTType.fun α (SMTType.option β)⟧ᶻ) :
    (predGraph α β (optionGraph α β F)).IsPFunc ⟦α⟧ᶻ ⟦β⟧ᶻ := by
  have hF_func : IsFunc ⟦α⟧ᶻ ⟦SMTType.option β⟧ᶻ F := by
    rw [show ⟦SMTType.fun α (SMTType.option β)⟧ᶻ =
      ⟦α⟧ᶻ.funs ⟦SMTType.option β⟧ᶻ from rfl, mem_funs] at hF
    exact hF
  constructor
  · intro ab hab
    exact (mem_sep.mp hab).1
  · intro a b hab b' hab'
    have hab_prod : a.pair b ∈ ⟦α⟧ᶻ.prod ⟦β⟧ᶻ :=
      (mem_sep.mp hab).1
    have hab'_prod : a.pair b' ∈ ⟦α⟧ᶻ.prod ⟦β⟧ᶻ :=
      (mem_sep.mp hab').1
    obtain ⟨ha, hb⟩ := pair_mem_prod.mp hab_prod
    obtain ⟨_, hb'⟩ := pair_mem_prod.mp hab'_prod
    have hpair :=
      (mem_predGraph_optionGraph_iff α β F hF a b ha hb).mp hab
    have hpair' :=
      (mem_predGraph_optionGraph_iff α β F hF a b' ha hb').mp hab'
    have hsome := (is_func_is_pfunc hF_func).2 a
      (ZFSet.Option.some (S := ⟦β⟧ᶻ) ⟨b, hb⟩).val hpair
      (ZFSet.Option.some (S := ⟦β⟧ᶻ) ⟨b', hb'⟩).val hpair'
    have hsome' :
        ZFSet.Option.some (S := ⟦β⟧ᶻ) ⟨b, hb⟩ =
          ZFSet.Option.some (S := ⟦β⟧ᶻ) ⟨b', hb'⟩ :=
      Subtype.ext hsome
    rw [ZFSet.Option.some.injEq] at hsome'
    exact Subtype.ext_iff.mp hsome'

/-- Graphing the collapse of a functional graph recovers that graph. -/
theorem optionGraph_graphCollapse.{u}
    (α β : SMTType) (R : ZFSet.{u})
    (hR : R ∈ ⟦SMTType.fun (SMTType.pair α β) SMTType.bool⟧ᶻ)
    (hfun : (predGraph α β R).IsPFunc ⟦α⟧ᶻ ⟦β⟧ᶻ) :
    optionGraph α β (graphCollapse α β R) = R :=
  castZF_apply_option_func_of_pfun α β R hR hfun

/-- Collapsing the graph of an option-valued function recovers the function. -/
theorem graphCollapse_optionGraph.{u}
    (α β : SMTType) (F : ZFSet.{u})
    (hF : F ∈ ⟦SMTType.fun α (SMTType.option β)⟧ᶻ) :
    graphCollapse α β (optionGraph α β F) = F := by
  let c := castPath.graph (castPath.reflexive α) (castPath.reflexive β)
  have hcollapse := graphCollapse_mem α β (optionGraph α β F)
  have hgraph := optionGraph_mem α β hF
  have hfun := predGraph_optionGraph_isPFunc α β F hF
  have hcollapse_graph := optionGraph_graphCollapse α β
    (optionGraph α β F) hgraph hfun
  have hpair_collapse := castZF_apply_pair c hcollapse
  have hpair_F := castZF_apply_pair c hF
  change (graphCollapse α β (optionGraph α β F)).pair
    (optionGraph α β (graphCollapse α β (optionGraph α β F))) ∈
      (castZF_of_path c).1 at hpair_collapse
  change F.pair (optionGraph α β F) ∈ (castZF_of_path c).1 at hpair_F
  rw [hcollapse_graph] at hpair_collapse
  exact castZF_of_path_injective c
    (graphCollapse α β (optionGraph α β F)) F (optionGraph α β F)
    hcollapse hF hgraph hpair_collapse hpair_F

/-- Functional pair-bool predicates, packaged with the condition needed for
the inverse graph construction. -/
abbrev FunctionalGraph.{u} (α β : SMTType) :=
  {R : ZFSet.{u} //
    R ∈ ⟦SMTType.fun (SMTType.pair α β) SMTType.bool⟧ᶻ ∧
      (predGraph α β R).IsPFunc ⟦α⟧ᶻ ⟦β⟧ᶻ}

/-- Option-valued functions and functional pair-bool predicates are
equivalent representations. -/
noncomputable def optionFunctionEquivFunctionalGraph.{u} (α β : SMTType) :
    {F : ZFSet.{u} // F ∈ ⟦SMTType.fun α (SMTType.option β)⟧ᶻ} ≃
      FunctionalGraph.{u} α β where
  toFun F :=
    ⟨optionGraph α β F.1,
      optionGraph_mem α β F.2,
      predGraph_optionGraph_isPFunc α β F.1 F.2⟩
  invFun R := ⟨graphCollapse α β R.1, graphCollapse_mem α β R.1⟩
  left_inv F := Subtype.ext (graphCollapse_optionGraph α β F.1 F.2)
  right_inv R := Subtype.ext
    (optionGraph_graphCollapse α β R.1 R.2.1 R.2.2)

/-- Pointwise representation-aware agreement of source and target
valuations. -/
def RValuationCast (Ξ : B.𝒱 → Option B.Dom)
    (Θ : SMT.𝒱 → Option SMT.Dom) : Prop := ∀ v,
  match Ξ v, Θ v with
  | none, none => True
  | some d, some d' => RDomCast d d'
  | _, _ => False

/-- Representation-aware agreement restricted to the source free variables
of a term. -/
abbrev RValuationCastOnFV (Ξ : B.𝒱 → Option B.Dom)
    (Θ : SMT.𝒱 → Option SMT.Dom) (t : B.Term) : Prop :=
  ∀ v ∈ B.fv t,
    match Ξ v, Θ v with
    | some d, some d' => RDomCast d d'
    | _, _ => False

namespace SMT.RenamingContext

/-- An SMT valuation represents a source valuation on the free variables of
`t`, without requiring canonical SMT type tags. -/
abbrev ExtendsOnSourceFVCast (Θ : Context)
    (Ξ : B.RenamingContext.Context) (t : B.Term) : Prop :=
  RValuationCastOnFV Ξ Θ t

end SMT.RenamingContext

/-- The canonical SMT valuation represents the source valuation on every
variable. -/
theorem RValuationCast_toSMT.{u} (Ξ : B.𝒱 → Option B.Dom.{u}) :
    RValuationCast Ξ (B.RenamingContext.toSMT Ξ) := by
  intro v
  have hcanonical := RValuation_toSMT Ξ v
  cases hΞ : Ξ v with
  | none =>
      rw [B.RenamingContext.toSMT, Option.pure_def, Option.bind_eq_bind,
        hΞ, Option.bind_none]
      trivial
  | some d =>
      cases hΘ : B.RenamingContext.toSMT Ξ v with
      | none =>
          have : False := by simpa [hΞ, hΘ] using hcanonical
          exact this.elim
      | some d' =>
          rw [hΞ, hΘ] at hcanonical
          exact RDom.toRDomCast hcanonical
