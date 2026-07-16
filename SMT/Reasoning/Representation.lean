import SMT.Reasoning.Basic.AllCaseHelpers

open B SMT ZFSet

/-!
# Representation-indexed semantic agreement

`RDom` compares a B denotation only with its canonical SMT representation.
`RDomCast` additionally permits an SMT value at a less general type, provided
an explicit loosening path casts that value to the canonical SMT type before
retraction.
-/

namespace SMT.RenamingContext

theorem RespectsTypeContextOnFV.of_full
    {Dc : Context} {Γ : SMT.TypeContext} {t : SMT.Term}
    (h : RespectsTypeContext Dc Γ) : RespectsTypeContextOnFV Dc Γ t := by
  intro v τ _hv hlookup
  exact h hlookup

theorem RespectsTypeContextOnFV.mono_fv
    {Dc : Context} {Γ : SMT.TypeContext} {t s : SMT.Term}
    (h : RespectsTypeContextOnFV Dc Γ t)
    (hsub : SMT.fv s ⊆ SMT.fv t) :
    RespectsTypeContextOnFV Dc Γ s := by
  intro v τ hv hlookup
  exact h (hsub hv) hlookup

/-- Preserve target-FV compatibility when both the valuation and type context
are extended. Typing supplies membership of every relevant free variable in
the old context, so lookup uniqueness identifies the transported type. -/
theorem RespectsTypeContextOnFV.of_extends
    {Dc Dc' : Context} {Γ Γ' : SMT.TypeContext}
    {t : SMT.Term} {σ : SMTType}
    (h : RespectsTypeContextOnFV Dc Γ t)
    (hDc : Extends Dc' Dc) (hΓ : Γ ⊆ Γ')
    (ht : Γ ⊢ˢ t : σ) :
    RespectsTypeContextOnFV Dc' Γ' t := by
  intro v τ hv hlookup'
  have hvΓ : v ∈ Γ := SMT.Typing.mem_context_of_mem_fv ht hv
  obtain ⟨τ₀, hlookup⟩ := Option.isSome_iff_exists.mp
    (AList.lookup_isSome.mpr hvΓ)
  have hlookup₀' : Γ'.lookup v = some τ₀ :=
    AList.lookup_of_subset hΓ hlookup
  rw [hlookup₀'] at hlookup'
  cases hlookup'
  obtain ⟨d, hd, hdτ⟩ := h hv hlookup
  exact ⟨d, hDc hd, hdτ⟩

end SMT.RenamingContext

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

/-- A value paired with an input by the relational cast is its functional
`castZF_apply` image. -/
theorem castZF_apply_eq_of_pair.{u} {α β : SMTType} (c : α ~> β)
    {x y : ZFSet.{u}} (hx : x ∈ ⟦α⟧ᶻ)
    (hxy : x.pair y ∈ (castZF_of_path c).1) :
    castZF_apply c x = y := by
  have happ := fapply.of_pair (is_func_is_pfunc (castZF_of_path c).2) hxy
  unfold castZF_apply
  rw [dif_pos hx]
  exact congrArg Subtype.val happ

/-- The only cast from an option-valued function to the matching relational
characteristic predicate is the graph cast with reflexive component paths. -/
theorem castPath.eq_graph_reflexive {α β : SMTType}
    (c : SMTType.fun α (SMTType.option β) ~>
      SMTType.fun (SMTType.pair α β) SMTType.bool) :
    c = castPath.graph (castPath.reflexive α) (castPath.reflexive β) := by
  cases c with
  | graph cα cβ =>
      rw [castPath.eq_reflexive cα, castPath.eq_reflexive cβ]
  | «fun» _ _ cβ =>
      cases cβ

/-- A cast ending at the integer base type must start there as well. -/
theorem castPath.source_eq_int {σ : SMTType} (_c : σ ~> SMTType.int) :
    σ = SMTType.int := by
  cases _c
  rfl

/-- A cast ending at the Boolean base type must start there as well. -/
theorem castPath.source_eq_bool {σ : SMTType} (_c : σ ~> SMTType.bool) :
    σ = SMTType.bool := by
  cases _c
  rfl

/-- A cast from a pair into an integer pair has integer components. -/
theorem castPath.source_pair_eq_int {σ τ : SMTType}
    (c : SMTType.pair σ τ ~>
      SMTType.pair SMTType.int SMTType.int) :
    σ = SMTType.int ∧ τ = SMTType.int := by
  cases c with
  | refl h =>
      rcases h with h | h | h <;> cases h
  | pair cx cy =>
      exact ⟨castPath.source_eq_int cx, castPath.source_eq_int cy⟩

/-- Representation-aware agreement between a B denotation and an SMT
denotation. The SMT value is first cast to the canonical SMT representation
of the B type and only then retracted. -/
def RDomCast : B.Dom → SMT.Dom → Prop
  | ⟨X, α, _⟩, ⟨Y, σ, _⟩ =>
      ∃ c : σ ~> α.toSMTType,
        retract α (castZF_apply c Y) = X

/-- A binder representation is admissible for a source domain when every
source value quantified over has a preimage at the selected SMT binder type.
This is the exact surjectivity condition needed to transport a false
counterexample through a cast and retraction. -/
def BinderCastAdmissible.{u} (τ : BType) (σ : SMTType)
    (c : σ ~> τ.toSMTType) (𝒟 : ZFSet.{u}) : Prop :=
  ∀ x ∈ 𝒟, ∃ x' ∈ ⟦σ⟧ᶻ,
    retract τ (castZF_apply c x') = x

/-- The canonical SMT representative of one B domain value.  This is the
pointwise operation used by `B.RenamingContext.toSMT`, exposed directly for
binder-local representation choices. -/
noncomputable def B.Dom.canonicalSMT.{u} (d : B.Dom.{u}) : SMT.Dom.{u} :=
  let ⟨X, α, hX⟩ := d
  let ζ := (BType.canonicalIsoSMTType α).1
  let ζ_isfunc := (BType.canonicalIsoSMTType α).2.1
  let X' : ZFSet.{u} := @ᶻζ ⟨X, by
    rwa [ZFSet.is_func_dom_eq ζ_isfunc]⟩
  ⟨X', α.toSMTType, by
    exact ZFSet.fapply_mem_range (ZFSet.is_func_is_pfunc ζ_isfunc)
      (by rwa [ZFSet.is_func_dom_eq ζ_isfunc])⟩

@[simp]
theorem B.Dom.canonicalSMT_type.{u} (d : B.Dom.{u}) :
    d.canonicalSMT.snd.fst = d.snd.fst.toSMTType := by
  rcases d with ⟨X, α, hX⟩
  rfl

/-- Direct canonical representatives satisfy the legacy agreement relation. -/
theorem B.Dom.rdom_canonicalSMT.{u} (d : B.Dom.{u}) :
    RDom d d.canonicalSMT := by
  rcases d with ⟨X, α, hX⟩
  rw [RDom]
  refine ⟨rfl, ?_⟩
  exact retract_of_canonical α hX

/-- Canonical binder representations are always admissible. -/
theorem BinderCastAdmissible.reflexive.{u}
    (τ : BType) {𝒟 : ZFSet.{u}} (h𝒟 : 𝒟 ∈ ⟦BType.set τ⟧ᶻ) :
    BinderCastAdmissible τ τ.toSMTType
      (castPath.reflexive τ.toSMTType) 𝒟 := by
  rw [BType.toZFSet, ZFSet.mem_powerset] at h𝒟
  intro x hx
  let d : B.Dom.{u} := ⟨x, τ, h𝒟 hx⟩
  have hy : d.canonicalSMT.fst ∈ ⟦τ.toSMTType⟧ᶻ := by
    change d.canonicalSMT.fst ∈ ⟦d.snd.fst.toSMTType⟧ᶻ
    rw [← B.Dom.canonicalSMT_type d]
    exact d.canonicalSMT.snd.snd
  refine ⟨d.canonicalSMT.fst, hy, ?_⟩
  rw [castZF_apply_reflexive τ.toSMTType hy]
  have hd := B.Dom.rdom_canonicalSMT d
  rw [RDom] at hd
  exact hd.2

/-- A functional relation admits the option-function binder representation.
The hypothesis is deliberately semantic: it concerns the canonical graph of
each source relation value, rather than merely membership of a variable name
in `E.flags`. -/
theorem BinderCastAdmissible.optionFunction.{u}
    (α β : BType) {𝒟 : ZFSet.{u}}
    (h𝒟 : 𝒟 ∈
      ⟦BType.set (BType.set (α ×ᴮ β))⟧ᶻ)
    (functional : ∀ (x : ZFSet.{u}) (_hx : x ∈ 𝒟)
      (hx_ty : x ∈ ⟦BType.set (α ×ᴮ β)⟧ᶻ),
      (predGraph α.toSMTType β.toSMTType
        (B.Dom.canonicalSMT
          (⟨x, BType.set (α ×ᴮ β), hx_ty⟩ : B.Dom)).fst).IsPFunc
        ⟦α.toSMTType⟧ᶻ ⟦β.toSMTType⟧ᶻ) :
    BinderCastAdmissible (BType.set (α ×ᴮ β))
      (SMTType.fun α.toSMTType (SMTType.option β.toSMTType))
      (castPath.graph (castPath.reflexive α.toSMTType)
        (castPath.reflexive β.toSMTType)) 𝒟 := by
  rw [BType.toZFSet, ZFSet.mem_powerset] at h𝒟
  intro x hx
  have hx_ty : x ∈ ⟦BType.set (α ×ᴮ β)⟧ᶻ := h𝒟 hx
  let d : B.Dom.{u} := ⟨x, BType.set (α ×ᴮ β), hx_ty⟩
  let y : SMT.Dom.{u} := d.canonicalSMT
  obtain ⟨x', hx', hcast⟩ := castZF_apply_surj_on_isPFunc
    α.toSMTType β.toSMTType y.fst y.snd.snd
    (functional x hx hx_ty)
  refine ⟨x', hx', ?_⟩
  rw [hcast]
  have hd := B.Dom.rdom_canonicalSMT d
  rw [RDom] at hd
  exact hd.2

/-- Convert binder admissibility to the preimage shape consumed by the
existing cast-plus-retract universal-quantifier bridge. -/
theorem BinderCastAdmissible.case_b_preimage.{u}
    {τ : BType} {σ : SMTType} {c : σ ~> τ.toSMTType}
    {𝒟 : ZFSet.{u}} (h : BinderCastAdmissible τ σ c 𝒟) :
    ∀ x ∈ 𝒟, ∃ x' ∈ ⟦σ⟧ᶻ,
      retract τ (castZF_apply c x') = x :=
  h

/-- Element-level preimage condition induced by a representation of a B set.
A characteristic predicate binds one argument of its domain type; an
option-valued function binds a domain/codomain pair. -/
def SetCastAdmissible.{u} (τ : BType) (𝒟 : ZFSet.{u}) :
    SMTType → Prop
  | SMTType.fun σ SMTType.bool =>
      ∃ c : σ ~> τ.toSMTType,
        BinderCastAdmissible τ σ c 𝒟
  | SMTType.fun σ (SMTType.option ρ) =>
      ∃ c : SMTType.pair σ ρ ~> τ.toSMTType,
        BinderCastAdmissible τ (SMTType.pair σ ρ) c 𝒟
  | _ => False

/-- Representation agreement strengthened by the exact surjectivity invariant
needed when the represented value is later consumed as a quantifier domain.
For non-set values this is precisely `RDomCast`. -/
def RDomCastAdmissible : B.Dom → SMT.Dom → Prop
  | ⟨𝒟, BType.set τ, _⟩, ⟨Y, σ, _⟩ =>
      ∃ c : σ ~> (BType.set τ).toSMTType,
        retract (BType.set τ) (castZF_apply c Y) = 𝒟 ∧
        SetCastAdmissible τ 𝒟 σ
  | d, d' => RDomCast d d'

theorem RDomCastAdmissible.toRDomCast.{u}
    {d : B.Dom.{u}} {d' : SMT.Dom.{u}}
    (h : RDomCastAdmissible d d') : RDomCast d d' := by
  rcases d with ⟨X, α, hX⟩
  rcases d' with ⟨Y, σ, hY⟩
  cases α with
  | set τ =>
      obtain ⟨c, hret, _hadm⟩ := h
      exact ⟨c, hret⟩
  | int | bool | prod =>
      exact h

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

/-- An SMT representative of a B integer necessarily has SMT integer type. -/
theorem RDomCast.target_type_eq_int.{u}
    {X Y : ZFSet.{u}} {σ : SMTType}
    {hX : X ∈ ⟦BType.int⟧ᶻ} {hY : Y ∈ ⟦σ⟧ᶻ}
    (h : RDomCast (⟨X, BType.int, hX⟩ : B.Dom)
      (⟨Y, σ, hY⟩ : SMT.Dom)) :
    σ = SMTType.int := by
  obtain ⟨c, _⟩ := h
  exact castPath.source_eq_int c

/-- An SMT representative of a B Boolean necessarily has SMT Boolean type. -/
theorem RDomCast.target_type_eq_bool.{u}
    {X Y : ZFSet.{u}} {σ : SMTType}
    {hX : X ∈ ⟦BType.bool⟧ᶻ} {hY : Y ∈ ⟦σ⟧ᶻ}
    (h : RDomCast (⟨X, BType.bool, hX⟩ : B.Dom)
      (⟨Y, σ, hY⟩ : SMT.Dom)) :
    σ = SMTType.bool := by
  obtain ⟨c, _⟩ := h
  exact castPath.source_eq_bool c

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

/-- Canonical agreement also supplies the binder-preimage invariant for set
values. -/
theorem RDom.toRDomCastAdmissible.{u}
    {d : B.Dom.{u}} {d' : SMT.Dom.{u}}
    (h : RDom d d') : RDomCastAdmissible d d' := by
  rcases d with ⟨X, α, hX⟩
  rcases d' with ⟨Y, σ, hY⟩
  rw [RDom] at h
  obtain ⟨rfl, hret⟩ := h
  cases α with
  | int =>
      exact RDom.toRDomCast
        (d := (⟨X, BType.int, hX⟩ : B.Dom))
        (d' := (⟨Y, SMTType.int, hY⟩ : SMT.Dom)) ⟨rfl, hret⟩
  | bool =>
      exact RDom.toRDomCast
        (d := (⟨X, BType.bool, hX⟩ : B.Dom))
        (d' := (⟨Y, SMTType.bool, hY⟩ : SMT.Dom)) ⟨rfl, hret⟩
  | prod α β =>
      exact RDom.toRDomCast
        (d := (⟨X, α ×ᴮ β, hX⟩ : B.Dom))
        (d' := (⟨Y, (α ×ᴮ β).toSMTType, hY⟩ : SMT.Dom))
        ⟨rfl, hret⟩
  | set τ =>
      refine ⟨castPath.reflexive (BType.set τ).toSMTType, ?_, ?_⟩
      · rwa [castZF_apply_reflexive (BType.set τ).toSMTType hY]
      · exact ⟨castPath.reflexive τ.toSMTType,
          BinderCastAdmissible.reflexive τ hX⟩

/-- Direct canonical representatives also satisfy representation-aware
agreement via the reflexive cast. -/
theorem B.Dom.rdomCast_canonicalSMT.{u} (d : B.Dom.{u}) :
    RDomCast d d.canonicalSMT :=
  RDom.toRDomCast (B.Dom.rdom_canonicalSMT d)

/-- Canonical representatives carry binder admissibility automatically. -/
theorem B.Dom.rdomCastAdmissible_canonicalSMT.{u} (d : B.Dom.{u}) :
    RDomCastAdmissible d d.canonicalSMT := by
  rcases d with ⟨X, α, hX⟩
  cases α with
  | int | bool | prod =>
      exact B.Dom.rdomCast_canonicalSMT ⟨X, _, hX⟩
  | set τ =>
      refine ⟨castPath.reflexive (BType.set τ).toSMTType, ?_, ?_⟩
      · have h := B.Dom.rdom_canonicalSMT
          (⟨X, BType.set τ, hX⟩ : B.Dom)
        rw [RDom] at h
        simpa [castZF_apply_self] using h.2
      · exact ⟨castPath.reflexive τ.toSMTType,
          BinderCastAdmissible.reflexive τ hX⟩

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

/-- Pair casts act componentwise on well-typed pair values. -/
theorem castZF_apply_pair_path.{u}
    {σ τ σ' τ' : SMTType} (cx : σ ~> σ') (cy : τ ~> τ')
    {X Y : ZFSet.{u}} (hX : X ∈ ⟦σ⟧ᶻ) (hY : Y ∈ ⟦τ⟧ᶻ) :
    castZF_apply (castPath.pair cx cy) (X.pair Y) =
      (castZF_apply cx X).pair (castZF_apply cy Y) := by
  apply castZF_apply_eq_of_pair (castPath.pair cx cy)
    (ZFSet.pair_mem_prod.mpr ⟨hX, hY⟩)
  change (X.pair Y).pair
      ((castZF_apply cx X).pair (castZF_apply cy Y)) ∈
    (castZF_pair (castZF_of_path cx) (castZF_of_path cy)).1
  rw [ZFSet.pair_mem_fprod]
  refine ⟨X, Y, hX, hY, rfl, ?_⟩
  unfold castZF_apply
  rw [dif_pos hX, dif_pos hY]

/-- Representation agreement is closed under pairing, using the component
cast paths pointwise. -/
theorem RDomCast.pair.{u}
    {X Y X' Y' : ZFSet.{u}} {α β : BType} {σ τ : SMTType}
    {hX : X ∈ ⟦α⟧ᶻ} {hY : Y ∈ ⟦β⟧ᶻ}
    {hX' : X' ∈ ⟦σ⟧ᶻ} {hY' : Y' ∈ ⟦τ⟧ᶻ}
    (hx : RDomCast (⟨X, α, hX⟩ : B.Dom)
      (⟨X', σ, hX'⟩ : SMT.Dom))
    (hy : RDomCast (⟨Y, β, hY⟩ : B.Dom)
      (⟨Y', τ, hY'⟩ : SMT.Dom)) :
    RDomCast
      (⟨X.pair Y, α ×ᴮ β, ZFSet.pair_mem_prod.mpr ⟨hX, hY⟩⟩ : B.Dom)
      (⟨X'.pair Y', SMTType.pair σ τ,
        ZFSet.pair_mem_prod.mpr ⟨hX', hY'⟩⟩ : SMT.Dom) := by
  obtain ⟨cx, hcx⟩ := hx
  obtain ⟨cy, hcy⟩ := hy
  refine ⟨castPath.pair cx cy, ?_⟩
  rw [castZF_apply_pair_path cx cy hX' hY']
  simp only [retract, ZFSet.π₁_pair, ZFSet.π₂_pair]
  rw [hcx, hcy]

/-- A represented pair determines represented components. -/
theorem RDomCast.of_pair.{u}
    {X Y X' Y' : ZFSet.{u}} {α β : BType} {σ τ : SMTType}
    {hX : X ∈ ⟦α⟧ᶻ} {hY : Y ∈ ⟦β⟧ᶻ}
    {hX' : X' ∈ ⟦σ⟧ᶻ} {hY' : Y' ∈ ⟦τ⟧ᶻ}
    (h : RDomCast
      (⟨X.pair Y, α ×ᴮ β, ZFSet.pair_mem_prod.mpr ⟨hX, hY⟩⟩ : B.Dom)
      (⟨X'.pair Y', SMTType.pair σ τ,
        ZFSet.pair_mem_prod.mpr ⟨hX', hY'⟩⟩ : SMT.Dom)) :
    RDomCast (⟨X, α, hX⟩ : B.Dom) (⟨X', σ, hX'⟩ : SMT.Dom) ∧
      RDomCast (⟨Y, β, hY⟩ : B.Dom) (⟨Y', τ, hY'⟩ : SMT.Dom) := by
  obtain ⟨c, hc⟩ := h
  cases c with
  | refl h =>
      rcases h with h | h | h <;> cases h
  | pair cx cy =>
      rw [castZF_apply_pair_path cx cy hX' hY'] at hc
      simp only [retract, ZFSet.π₁_pair, ZFSet.π₂_pair,
        ZFSet.pair_inj] at hc
      exact ⟨⟨cx, hc.1⟩, ⟨cy, hc.2⟩⟩

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

/-- Unpack representation agreement for the running option-function encoding
of a B relation. -/
theorem RDomCast.optionFunction_graph_retract.{u}
    {α β : BType} {X F : ZFSet.{u}} {hX hF}
    (hrel : RDomCast
      (⟨X, BType.set (α ×ᴮ β), hX⟩ : B.Dom)
      (⟨F, SMTType.fun α.toSMTType (SMTType.option β.toSMTType), hF⟩ :
        SMT.Dom)) :
    retract (BType.set (α ×ᴮ β))
      (optionGraph α.toSMTType β.toSMTType F) = X := by
  obtain ⟨c, hc⟩ := hrel
  rw [castPath.eq_graph_reflexive c] at hc
  exact hc

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

/-- Pointwise cast agreement carrying the binder-preimage invariant for every
set-valued source assignment. -/
def RValuationCastAdmissible (Ξ : B.𝒱 → Option B.Dom)
    (Θ : SMT.𝒱 → Option SMT.Dom) : Prop := ∀ v,
  match Ξ v, Θ v with
  | none, none => True
  | some d, some d' => RDomCastAdmissible d d'
  | _, _ => False

/-- Representation-aware agreement restricted to the source free variables
of a term. -/
abbrev RValuationCastOnFV (Ξ : B.𝒱 → Option B.Dom)
    (Θ : SMT.𝒱 → Option SMT.Dom) (t : B.Term) : Prop :=
  ∀ v ∈ B.fv t,
    match Ξ v, Θ v with
    | some d, some d' => RDomCast d d'
    | _, _ => False

/-- Binder-admissible representation agreement restricted to source free
variables. -/
abbrev RValuationCastAdmissibleOnFV
    (Ξ : B.𝒱 → Option B.Dom)
    (Θ : SMT.𝒱 → Option SMT.Dom) (t : B.Term) : Prop :=
  ∀ v ∈ B.fv t,
    match Ξ v, Θ v with
    | some d, some d' => RDomCastAdmissible d d'
    | _, _ => False

theorem RValuationCastAdmissibleOnFV.toRValuationCastOnFV
    {Ξ : B.𝒱 → Option B.Dom} {Θ : SMT.𝒱 → Option SMT.Dom}
    {t : B.Term} (h : RValuationCastAdmissibleOnFV Ξ Θ t) :
    RValuationCastOnFV Ξ Θ t := by
  intro v hv
  have hrel := h v hv
  cases hΞ : Ξ v with
  | none =>
      cases hΘ : Θ v <;> simp [hΞ, hΘ] at hrel
  | some d =>
      cases hΘ : Θ v with
      | none => simp [hΞ, hΘ] at hrel
      | some d' =>
          rw [hΞ, hΘ] at hrel
          simpa using hrel.toRDomCast

theorem RValuationCastAdmissibleOnFV.mono_fv
    {Ξ : B.𝒱 → Option B.Dom} {Θ : SMT.𝒱 → Option SMT.Dom}
    {s t : B.Term} (h : RValuationCastAdmissibleOnFV Ξ Θ t)
    (hfv : B.fv s ⊆ B.fv t) :
    RValuationCastAdmissibleOnFV Ξ Θ s :=
  fun v hv => h v (hfv hv)

theorem RValuationCastAdmissibleOnFV.of_extends.{u}
    {Ξ : B.𝒱 → Option B.Dom.{u}}
    {Θ Θ' : SMT.𝒱 → Option SMT.Dom.{u}} {t : B.Term}
    (h : RValuationCastAdmissibleOnFV Ξ Θ t)
    (hext : SMT.RenamingContext.Extends Θ' Θ) :
    RValuationCastAdmissibleOnFV Ξ Θ' t := by
  intro v hv
  have hv_rel := h v hv
  cases hΞ : Ξ v with
  | none =>
      cases hΘ : Θ v <;> simp [hΞ, hΘ] at hv_rel
  | some d =>
      cases hΘ : Θ v with
      | none => simp [hΞ, hΘ] at hv_rel
      | some d' =>
          rw [hΞ, hΘ] at hv_rel
          have hΘ' : Θ' v = some d' := hext hΘ
          simpa [hΞ, hΘ']

/-- Restrict representation-aware valuation agreement to a smaller
free-variable set. -/
theorem RValuationCastOnFV.mono_fv
    {Ξ : B.𝒱 → Option B.Dom} {Θ : SMT.𝒱 → Option SMT.Dom}
    {s t : B.Term} (h : RValuationCastOnFV Ξ Θ t)
    (hfv : B.fv s ⊆ B.fv t) :
    RValuationCastOnFV Ξ Θ s :=
  fun v hv => h v (hfv hv)

/-- Extending the SMT valuation preserves representation agreement: every
source free variable is already assigned on the SMT side, so extension keeps
that exact representative. -/
theorem RValuationCastOnFV.of_extends.{u}
    {Ξ : B.𝒱 → Option B.Dom.{u}}
    {Θ Θ' : SMT.𝒱 → Option SMT.Dom.{u}} {t : B.Term}
    (h : RValuationCastOnFV Ξ Θ t)
    (hext : SMT.RenamingContext.Extends Θ' Θ) :
    RValuationCastOnFV Ξ Θ' t := by
  intro v hv
  have hv_rel := h v hv
  cases hΞ : Ξ v with
  | none =>
      cases hΘ : Θ v <;> simp [hΞ, hΘ] at hv_rel
  | some d =>
      cases hΘ : Θ v with
      | none => simp [hΞ, hΘ] at hv_rel
      | some d' =>
          rw [hΞ, hΘ] at hv_rel
          have hΘ' : Θ' v = some d' := hext hΘ
          simpa [hΞ, hΘ']

/-- Transport free-variable type compatibility across both an extending SMT
valuation and an extending type context. -/
theorem B.RenamingContext.RespectsTypeContextOnFV.of_extends.{u}
    {Θ Θ' : SMT.RenamingContext.Context.{u}}
    {Λ Γ : SMT.TypeContext} {s t : B.Term}
    (h : B.RenamingContext.RespectsTypeContextOnFV Θ Λ t)
    (hext : SMT.RenamingContext.Extends Θ' Θ)
    (hΛΓ : Λ ⊆ Γ)
    (hfv : B.fv s ⊆ B.fv t)
    (fv_in_Λ : ∀ v ∈ B.fv t, v ∈ Λ) :
    B.RenamingContext.RespectsTypeContextOnFV Θ' Γ s := by
  intro v τ hv_s hΓ
  have hv_t : v ∈ B.fv t := hfv hv_s
  have hv_Λ : v ∈ Λ := fv_in_Λ v hv_t
  obtain ⟨τ₀, hΛ⟩ := Option.isSome_iff_exists.mp
    (AList.lookup_isSome.mpr hv_Λ)
  have hΓ₀ : Γ.lookup v = some τ₀ := AList.lookup_of_subset hΛΓ hΛ
  rw [hΓ₀] at hΓ
  cases hΓ
  obtain ⟨d, hd, hd_type⟩ := h hv_t hΛ
  exact ⟨d, hext hd, hd_type⟩

/-- Updating a binder with pointwise related values preserves
representation-aware agreement for its body.  Variables outside the binder
continue to use the ambient agreement, while bound variables may change SMT
representation independently at each position. -/
theorem RValuationCastOnFV.updates.{u}
    {Ξ : B.𝒱 → Option B.Dom.{u}}
    {Θ : SMT.𝒱 → Option SMT.Dom.{u}}
    {vs : List B.𝒱} (vs_nodup : vs.Nodup)
    (bs : Fin vs.length → B.Dom.{u})
    (ss : Fin vs.length → SMT.Dom.{u})
    {t : B.Term}
    (ambient : ∀ v ∈ B.fv t, v ∉ vs →
      match Ξ v, Θ v with
      | some d, some d' => RDomCast d d'
      | _, _ => False)
    (bound : ∀ i, RDomCast (bs i) (ss i)) :
    RValuationCastOnFV
      (Function.updates Ξ vs (List.ofFn fun i => some (bs i)))
      (Function.updates Θ vs (List.ofFn fun i => some (ss i))) t := by
  intro v hv
  by_cases hvs : v ∈ vs
  · rw [Function.updates_eq_if (by simp) vs_nodup,
      Function.updates_eq_if (by simp) vs_nodup,
      dif_pos hvs, dif_pos hvs]
    simpa using bound ⟨vs.idxOf v, List.idxOf_lt_length_of_mem hvs⟩
  · rw [Function.updates_of_not_mem Ξ vs _ v hvs,
      Function.updates_of_not_mem Θ vs _ v hvs]
    exact ambient v hv hvs

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

/-- The canonical SMT valuation is binder-admissibly related to the source
valuation on every variable. -/
theorem RValuationCastAdmissible_toSMT.{u}
    (Ξ : B.𝒱 → Option B.Dom.{u}) :
    RValuationCastAdmissible Ξ (B.RenamingContext.toSMT Ξ) := by
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
          exact RDom.toRDomCastAdmissible hcanonical
