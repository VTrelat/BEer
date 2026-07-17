import SMT.Reasoning.Basic.EncodeTermRepresentedInter
import SMT.Reasoning.Basic.EncodeTermRepresentedMem

open Std.Do B SMT ZFSet Classical

theorem denote_and_both_zftrue_of_zftrue_rep_eq
    {p q : SMT.PHOAS.Term SMT.Dom} {Dp Dq : SMT.Dom}
    (hp : ⟦p⟧ˢ = some Dp) (hpTy : Dp.snd.fst = .bool)
    (hq : ⟦q⟧ˢ = some Dq) (hqTy : Dq.snd.fst = .bool)
    {Dand : SMT.Dom}
    (hand : ⟦p ∧ˢ' q⟧ˢ = some Dand)
    (handTrue : Dand.fst = zftrue) :
    Dp.fst = zftrue ∧ Dq.fst = zftrue := by
  have hpMem : Dp.fst ∈ ZFSet.𝔹 := by
    have := Dp.snd.snd
    rwa [hpTy] at this
  have hqMem : Dq.fst ∈ ZFSet.𝔹 := by
    have := Dq.snd.snd
    rwa [hqTy] at this
  constructor
  · rcases ZFSet.ZFBool.mem_𝔹_iff _ |>.mp hpMem with hpFalse | hpTrue
    · have hfalse := denote_and_eq_zffalse_of_some_zffalse_left
        hp hpTy hpFalse hq hqTy
      rw [hfalse] at hand
      have heq := Option.some.inj hand
      rw [← congrArg (fun d : SMT.Dom => d.fst) heq] at handTrue
      exact (ZFSet.zftrue_ne_zffalse handTrue.symm).elim
    · exact hpTrue
  · rcases ZFSet.ZFBool.mem_𝔹_iff _ |>.mp hqMem with hqFalse | hqTrue
    · have hfalse := denote_and_eq_zffalse_of_some_zffalse_right
        hp hpTy hq hqTy hqFalse
      rw [hfalse] at hand
      have heq := Option.some.inj hand
      rw [← congrArg (fun d : SMT.Dom => d.fst) heq] at handTrue
      exact (ZFSet.zftrue_ne_zffalse handTrue.symm).elim
    · exact hqTrue

theorem castEq_direct_rep_semantics.{u}
    {alpha : BType} {A B : SMT.Term} {sigma : SMTType}
    {Lambda : SMT.TypeContext}
    {Theta : SMT.RenamingContext.Context.{u}}
    (hcovA : RenamingContext.CoversFV Theta A)
    (hcovB : RenamingContext.CoversFV Theta B)
    (respectsA : SMT.RenamingContext.RespectsTypeContextOnFV Theta Lambda A)
    (respectsB : SMT.RenamingContext.RespectsTypeContextOnFV Theta Lambda B)
    {X Y P : ZFSet.{u}}
    {hX : X ∈ ⟦alpha⟧ᶻ} {hY : Y ∈ ⟦alpha⟧ᶻ}
    {hP : P ∈ ⟦BType.bool⟧ᶻ}
    {denA denB : SMT.Dom.{u}}
    (hdenA : ⟦A.abstract Theta hcovA⟧ˢ = some denA)
    (hdenB : ⟦B.abstract Theta hcovB⟧ˢ = some denB)
    (hdenAty : denA.snd.fst = sigma)
    (hdenBty : denB.snd.fst = sigma)
    (relA : RDomCastSupported (⟨X, alpha, hX⟩ : _root_.B.Dom) denA)
    (relB : RDomCastSupported (⟨Y, alpha, hY⟩ : _root_.B.Dom) denB)
    (hPiff : P = ZFSet.zftrue ↔ X = Y) :
    ∃ (hcov : RenamingContext.CoversFV Theta (A =ˢ B))
      (denEq : SMT.Dom.{u}),
      SMT.RenamingContext.RespectsTypeContextOnFV Theta Lambda (A =ˢ B) ∧
      ⟦(A =ˢ B).abstract Theta hcov⟧ˢ = some denEq ∧
      denEq.snd.fst = SMTType.bool ∧
      RDomCastSupported (⟨P, BType.bool, hP⟩ : _root_.B.Dom) denEq := by
  rcases denA with ⟨Aval, sigmaA, hAval⟩
  rcases denB with ⟨Bval, sigmaB, hBval⟩
  dsimp at hdenAty hdenBty
  subst sigmaA
  subst sigmaB
  have hcov : RenamingContext.CoversFV Theta (A =ˢ B) := by
    intro v hv
    rw [SMT.fv, List.mem_append] at hv
    exact hv.elim (hcovA v) (hcovB v)
  have respectsEq :
      SMT.RenamingContext.RespectsTypeContextOnFV Theta Lambda (A =ˢ B) := by
    intro v xi hv hlookup
    rw [SMT.fv, List.mem_append] at hv
    exact hv.elim (fun h => respectsA h hlookup)
      (fun h => respectsB h hlookup)
  obtain ⟨denEq, hdenEqRaw, hdenEqTy⟩ :=
    denote_eq_some_of_some hdenA hdenB rfl
  rcases denEq with ⟨Q, tauQ, hQ⟩
  dsimp at hdenEqTy
  subst tauQ
  have hdenEq : ⟦(A =ˢ B).abstract Theta hcov⟧ˢ =
      some (⟨Q, SMTType.bool, hQ⟩ : SMT.Dom) := by
    rw [SMT.Term.abstract]
    simpa only [proof_irrel_heq] using hdenEqRaw
  have hEqTrue : Q = ZFSet.zftrue ↔ X = Y :=
    (denote_eq_fst_eq_zftrue_iff hdenA hdenB rfl hdenEqRaw).trans
      (RDomCast.target_value_eq_iff relA.toRDomCast relB.toRDomCast)
  refine ⟨hcov, (⟨Q, SMTType.bool, hQ⟩ : SMT.Dom), respectsEq,
    hdenEq, rfl, ?_⟩
  exact RDomCastSupported.bool_of_true_iff (hPiff.trans hEqTrue.symm)

theorem castEq_left_rep_semantics.{u}
    {alpha : BType} {A B spec : SMT.Term} {sigmaA sigmaB : SMTType}
    {Lambda Gamma : SMT.TypeContext} {helper : SMT.𝒱}
    {used0 used1 : List SMT.𝒱}
    (typA : Lambda ⊢ˢ A : sigmaA)
    (typB : Lambda ⊢ˢ B : sigmaB)
    (Lambda_sub : Lambda ⊆ Gamma)
    (helper_fresh : helper ∉ Lambda)
    (helper_lookup : Gamma.lookup helper = some sigmaB)
    (helper_not_used0 : helper ∉ used0)
    (helper_used1 : helper ∈ used1)
    (used_sub : used0 ⊆ used1)
    (spec_fv : SMT.fv spec ⊆ SMT.fv A ∪ {helper})
    (c : sigmaA ~> sigmaB)
    (exactness :
      ∀ (Theta : SMT.RenamingContext.Context.{u})
        (hA : RenamingContext.CoversFV Theta A)
        (_respects : SMT.RenamingContext.RespectsTypeContextOnFV
          Theta Lambda A)
        (pf : ∀ (x_ : SMT.𝒱) (X_ : SMT.Dom),
          ∀ v ∈ SMT.fv (SMT.Term.var x_),
            (Function.update Theta x_ (some X_) v).isSome = true),
      ∀ (denA : SMT.Dom), ⟦A.abstract Theta hA⟧ˢ = some denA →
        ∃ (Phi H : SMT.Dom)
          (_ : ⟦(SMT.Term.var helper).abstract
            (Function.update Theta helper (some H)) (pf helper H)⟧ˢ = some H)
          (hphi : RenamingContext.CoversFV
            (Function.update Theta helper (some H)) spec)
          (_ : ⟦spec.abstract (Function.update Theta helper (some H))
            hphi⟧ˢ = some Phi),
          H.snd.fst = sigmaB ∧
          Phi.snd.fst = SMTType.bool ∧
          (Phi.fst = zftrue ∧
            denA.fst.pair H.fst ∈ (castZF_of_path c).1) ∧
          (∀ (Y : SMT.Dom) (_ : Y.snd.fst = sigmaB)
            (hphiY : RenamingContext.CoversFV
              (Function.update Theta helper (some Y)) spec),
            (⟦spec.abstract (Function.update Theta helper (some Y))
              hphiY⟧ˢ).isSome = true ∧
            ∀ {PhiY : SMT.Dom},
              ⟦spec.abstract (Function.update Theta helper (some Y))
                hphiY⟧ˢ = some PhiY →
              PhiY.fst = zftrue →
              denA.fst.pair Y.fst ∈ (castZF_of_path c).1))
    {Theta : SMT.RenamingContext.Context.{u}}
    (hcovA : RenamingContext.CoversFV Theta A)
    (hcovB : RenamingContext.CoversFV Theta B)
    (Theta_none : ∀ v ∉ used0, Theta v = none)
    (respectsA : SMT.RenamingContext.RespectsTypeContextOnFV Theta Lambda A)
    (respectsB : SMT.RenamingContext.RespectsTypeContextOnFV Theta Lambda B)
    (Theta_dom : ∀ v, Theta v ≠ none → v ∈ Gamma)
    {X Y P : ZFSet.{u}}
    {hX : X ∈ ⟦alpha⟧ᶻ} {hY : Y ∈ ⟦alpha⟧ᶻ}
    {hP : P ∈ ⟦BType.bool⟧ᶻ}
    {denA denB : SMT.Dom.{u}}
    (hdenA : ⟦A.abstract Theta hcovA⟧ˢ = some denA)
    (hdenB : ⟦B.abstract Theta hcovB⟧ˢ = some denB)
    (hdenAty : denA.snd.fst = sigmaA)
    (hdenBty : denB.snd.fst = sigmaB)
    (relA : RDomCastSupported (⟨X, alpha, hX⟩ : _root_.B.Dom) denA)
    (relB : RDomCastSupported (⟨Y, alpha, hY⟩ : _root_.B.Dom) denB)
    (hPiff : P = ZFSet.zftrue ↔ X = Y) :
    ∃ (Theta' : SMT.RenamingContext.Context.{u})
      (hcov : RenamingContext.CoversFV Theta'
        (((.var helper) =ˢ B) ∧ˢ spec))
      (denEq : SMT.Dom.{u}),
      RenamingContext.Extends Theta' Theta ∧
      (∀ v ∉ used1, Theta' v = none) ∧
      SMT.RenamingContext.RespectsTypeContextOnFV Theta' Gamma
        (((.var helper) =ˢ B) ∧ˢ spec) ∧
      (∀ v, Theta' v ≠ none → v ∈ Gamma) ∧
      SpecBodiesTrue Theta' Gamma
        (helperSpecChunk helper sigmaB spec) ∧
      ⟦((((.var helper) =ˢ B) ∧ˢ spec).abstract Theta' hcov)⟧ˢ =
        some denEq ∧
      denEq.snd.fst = SMTType.bool ∧
      RDomCastSupported (⟨P, BType.bool, hP⟩ : _root_.B.Dom) denEq := by
  have helper_none : Theta helper = none :=
    Theta_none helper helper_not_used0
  rcases denA with ⟨Aval, sigmaA0, hAval⟩
  dsimp at hdenAty
  subst sigmaA0
  rcases denB with ⟨Bval, sigmaB0, hBval⟩
  dsimp at hdenBty
  subst sigmaB0
  let pf : ∀ (x_ : SMT.𝒱) (H : SMT.Dom),
      ∀ v ∈ SMT.fv (SMT.Term.var x_),
        (Function.update Theta x_ (some H) v).isSome = true := by
    intro x_ H v hv
    simp only [SMT.fv, List.mem_singleton] at hv
    subst v
    simp
  obtain ⟨Phi, H, hdenVar, hcovSpec, hdenSpec, Hty, Phity,
      ⟨PhiTrue, castPair⟩, _⟩ :=
    exactness Theta hcovA respectsA pf
      (⟨Aval, sigmaA, hAval⟩ : SMT.Dom) hdenA
  let Theta' := Function.update Theta helper (some H)
  have Theta'_ext : RenamingContext.Extends Theta' Theta :=
    RenamingContext.extends_update_of_none helper_none
  have hcovB' : RenamingContext.CoversFV Theta' B :=
    RenamingContext.coversFV_of_extends_of_coversFV Theta'_ext hcovB
  have hdenB' : ⟦B.abstract Theta' hcovB'⟧ˢ =
      some (⟨Bval, sigmaB, hBval⟩ : SMT.Dom) := by
    have hagree := RenamingContext.agreesOnFV_of_extends_of_coversFV
      Theta'_ext hcovB
    exact (RenamingContext.denote_congr_of_agreesOnFV
      (t := B) (h1 := hcovB') (h2 := hcovB) hagree).trans hdenB
  have helper_not_fv_B : helper ∉ SMT.fv B :=
    fun hv => helper_fresh (SMT.Typing.mem_context_of_mem_fv typB hv)
  have respectsB' :
      SMT.RenamingContext.RespectsTypeContextOnFV Theta' Gamma B := by
    intro v xi hv hlookup
    have hv_ne : v ≠ helper := fun h => by
      subst v
      exact helper_not_fv_B hv
    obtain ⟨d, hd, hdty⟩ := respectsB hv (by
      have hvLambda := SMT.Typing.mem_context_of_mem_fv typB hv
      obtain ⟨xi0, hlookup0⟩ := Option.isSome_iff_exists.mp
        (AList.lookup_isSome.mpr hvLambda)
      have hlookup0' := AList.lookup_of_subset Lambda_sub hlookup0
      rw [hlookup] at hlookup0'
      cases hlookup0'
      exact hlookup0)
    refine ⟨d, ?_, hdty⟩
    simpa [Theta', Function.update_of_ne hv_ne] using hd
  have respectsSpec :
      SMT.RenamingContext.RespectsTypeContextOnFV Theta' Gamma spec := by
    intro v xi hv hlookup
    rcases List.mem_union_iff.mp (spec_fv hv) with hvA | hvHelper
    · have hv_ne : v ≠ helper := by
        intro h
        subst v
        exact helper_fresh (SMT.Typing.mem_context_of_mem_fv typA hvA)
      have hvLambda := SMT.Typing.mem_context_of_mem_fv typA hvA
      obtain ⟨xi0, hlookup0⟩ := Option.isSome_iff_exists.mp
        (AList.lookup_isSome.mpr hvLambda)
      have hlookup0' := AList.lookup_of_subset Lambda_sub hlookup0
      rw [hlookup] at hlookup0'
      cases hlookup0'
      obtain ⟨d, hd, hdty⟩ := respectsA hvA hlookup0
      exact ⟨d, by simpa [Theta', Function.update_of_ne hv_ne] using hd,
        hdty⟩
    · have hv_eq : v = helper := List.mem_singleton.mp hvHelper
      subst v
      rw [helper_lookup] at hlookup
      cases hlookup
      exact ⟨H, by simp [Theta'], Hty⟩
  have hcovVar : RenamingContext.CoversFV Theta' (.var helper) := by
    intro v hv
    simp only [SMT.fv, List.mem_singleton] at hv
    subst v
    simp [Theta']
  have hdenVar' : ⟦(SMT.Term.var helper).abstract Theta' hcovVar⟧ˢ =
      some H := by
    simpa only [Theta', proof_irrel_heq] using hdenVar
  have respectsVar :
      SMT.RenamingContext.RespectsTypeContextOnFV Theta' Gamma
        (.var helper) := by
    intro v xi hv hlookup
    simp only [SMT.fv, List.mem_singleton] at hv
    subst v
    rw [helper_lookup] at hlookup
    cases hlookup
    exact ⟨H, by simp [Theta'], Hty⟩
  have hcovEq : RenamingContext.CoversFV Theta'
      ((.var helper) =ˢ B) := by
    intro v hv
    rw [SMT.fv, List.mem_append] at hv
    exact hv.elim (hcovVar v) (hcovB' v)
  have respectsEq :
      SMT.RenamingContext.RespectsTypeContextOnFV Theta' Gamma
        ((.var helper) =ˢ B) := by
    intro v xi hv hlookup
    rw [SMT.fv, List.mem_append] at hv
    exact hv.elim (fun h => respectsVar h hlookup)
      (fun h => respectsB' h hlookup)
  obtain ⟨denEq0, hdenEqRaw, hdenEqTy⟩ :=
    denote_eq_some_of_some hdenVar' hdenB' Hty
  have hdenEq : ⟦(((.var helper) =ˢ B).abstract Theta' hcovEq)⟧ˢ =
      some denEq0 := by
    rw [SMT.Term.abstract]
    simpa only [proof_irrel_heq] using hdenEqRaw
  have hcast : castZF_apply c Aval = H.fst :=
    castZF_apply_eq_of_pair c hAval castPair
  have hcastEq : H.fst = Bval ↔ X = Y := by
    rw [← hcast]
    exact RDomCastSupported.cast_eq_iff relA relB c
  have hEqTrue : denEq0.fst = ZFSet.zftrue ↔ X = Y :=
    (denote_eq_fst_eq_zftrue_iff hdenVar' hdenB'
      Hty hdenEqRaw).trans hcastEq
  have hcovOut : RenamingContext.CoversFV Theta'
      (((.var helper) =ˢ B) ∧ˢ spec) := by
    intro v hv
    rw [SMT.fv, List.mem_append] at hv
    exact hv.elim (hcovEq v) (hcovSpec v)
  have respectsOut :
      SMT.RenamingContext.RespectsTypeContextOnFV Theta' Gamma
        (((.var helper) =ˢ B) ∧ˢ spec) := by
    intro v xi hv hlookup
    rw [SMT.fv, List.mem_append] at hv
    exact hv.elim (fun h => respectsEq h hlookup)
      (fun h => respectsSpec h hlookup)
  obtain ⟨denOut, hdenOutRaw, hdenOutTy⟩ :=
    denote_and_some_bool_of_some_bool hdenEq hdenEqTy hdenSpec Phity
  have hdenOut :
      ⟦((((.var helper) =ˢ B) ∧ˢ spec).abstract Theta' hcovOut)⟧ˢ =
        some denOut := by
    rw [SMT.Term.abstract]
    simpa only [proof_irrel_heq] using hdenOutRaw
  have hOutTrue : denOut.fst = ZFSet.zftrue ↔ X = Y := by
    constructor
    · intro hout
      exact hEqTrue.mp
        (denote_and_both_zftrue_of_zftrue_rep_eq hdenEq hdenEqTy
          hdenSpec Phity hdenOutRaw hout).1
    · intro hxy
      have hraw := denote_and_eq_zftrue_of_some_zftrue
        hdenEq hdenEqTy (hEqTrue.mpr hxy)
        hdenSpec Phity PhiTrue
      rw [hdenOutRaw] at hraw
      exact congrArg (fun d : SMT.Dom => d.fst) (Option.some.inj hraw)
  have Theta'_none : ∀ v ∉ used1, Theta' v = none := by
    intro v hv
    have hv_ne : v ≠ helper := fun h => by
      subst v
      exact hv helper_used1
    simpa [Theta', Function.update_of_ne hv_ne] using
      Theta_none v (fun hv0 => hv (used_sub hv0))
  have Theta'_dom : ∀ v, Theta' v ≠ none → v ∈ Gamma := by
    intro v hv
    by_cases hvh : v = helper
    · subst v
      exact AList.lookup_isSome.mp (by rw [helper_lookup]; rfl)
    · exact Theta_dom v (by
        simpa [Theta', Function.update_of_ne hvh] using hv)
  have specs_true : SpecBodiesTrue Theta' Gamma
      (helperSpecChunk helper sigmaB spec) := by
    intro body hbody
    simp only [specBodies_helperSpecChunk, List.mem_singleton] at hbody
    subst body
    exact ⟨hcovSpec, Phi, respectsSpec, hdenSpec, Phity, PhiTrue⟩
  rcases denOut with ⟨Q, tauQ, hQ⟩
  dsimp at hdenOutTy
  subst tauQ
  refine ⟨Theta', hcovOut, (⟨Q, SMTType.bool, hQ⟩ : SMT.Dom),
    Theta'_ext, Theta'_none, respectsOut, Theta'_dom, specs_true,
    hdenOut, rfl, ?_⟩
  exact RDomCastSupported.bool_of_true_iff (hPiff.trans hOutTrue.symm)

abbrev CastEqRepSpec.{u} (alpha : BType)
    (A B : SMT.Term) (sigmaA sigmaB : SMTType) : Prop :=
  ∀ {Lambda : SMT.TypeContext} {n : ℕ} {used : List SMT.𝒱},
    Lambda ⊢ˢ A : sigmaA →
    Lambda ⊢ˢ B : sigmaB →
    (∀ v ∈ SMT.bv A, v ∈ used) →
    (∀ v ∈ SMT.bv B, v ∈ used) →
    ⦃fun ⟨E, Lambda'⟩ =>
      ⌜Lambda' = Lambda ∧ E.freshvarsc = n ∧
        Lambda.keys ⊆ E.usedVars ∧ E.usedVars = used⌝⦄
    castEq ⟨A, sigmaA⟩ ⟨B, sigmaB⟩
    ⦃⇓? ⟨t, sigma⟩ ⟨E', Gamma'⟩ =>
      ⌜used ⊆ E'.usedVars ∧
        Lambda ⊆ Gamma' ∧
        Gamma'.keys ⊆ E'.usedVars ∧
        sigma = SMTType.bool ∧
        Gamma' ⊢ˢ t : SMTType.bool ∧
        (∀ v ∈ used, v ∉ Lambda → v ∉ Gamma') ∧
        ∀ (Theta : SMT.RenamingContext.Context.{u})
          (hA : RenamingContext.CoversFV Theta A)
          (hB : RenamingContext.CoversFV Theta B),
          (∀ v ∉ used, Theta v = none) →
          SMT.RenamingContext.RespectsTypeContextOnFV Theta Lambda A →
          SMT.RenamingContext.RespectsTypeContextOnFV Theta Lambda B →
          (∀ v, Theta v ≠ none → v ∈ Lambda) →
          ∀ (X Y P : ZFSet.{u})
            (hX : X ∈ ⟦alpha⟧ᶻ)
            (hY : Y ∈ ⟦alpha⟧ᶻ)
            (hP : P ∈ ⟦BType.bool⟧ᶻ)
            (denA denB : SMT.Dom.{u}),
            ⟦A.abstract Theta hA⟧ˢ = some denA →
            ⟦B.abstract Theta hB⟧ˢ = some denB →
            denA.snd.fst = sigmaA →
            denB.snd.fst = sigmaB →
            RDomCastSupported
              (⟨X, alpha, hX⟩ : _root_.B.Dom) denA →
            RDomCastSupported
              (⟨Y, alpha, hY⟩ : _root_.B.Dom) denB →
            (P = ZFSet.zftrue ↔ X = Y) →
            ∃ (Theta' : SMT.RenamingContext.Context.{u})
              (hcov : RenamingContext.CoversFV Theta' t)
              (denEq : SMT.Dom.{u}),
              RenamingContext.Extends Theta' Theta ∧
              (∀ v ∉ E'.usedVars, Theta' v = none) ∧
              SMT.RenamingContext.RespectsTypeContextOnFV Theta' Gamma' t ∧
              (∀ v, Theta' v ≠ none → v ∈ Gamma') ∧
              ⟦t.abstract Theta' hcov⟧ˢ = some denEq ∧
              denEq.snd.fst = SMTType.bool ∧
              RDomCastSupported
                (⟨P, BType.bool, hP⟩ : _root_.B.Dom) denEq⌝⦄

set_option maxHeartbeats 3000000 in
theorem castEq_supported_rep_contract.{u}
    (alpha : BType) (A B : SMT.Term) (sigmaA sigmaB : SMTType)
    (_supportedA : BType.SupportedSMT alpha sigmaA)
    (_supportedB : BType.SupportedSMT alpha sigmaB) :
    CastEqRepSpec.{u} alpha A B sigmaA sigmaB := by
  unfold CastEqRepSpec
  intro Lambda n used typA typB bvA_used bvB_used
  mstart
  mintro pre ∀St0
  mpure pre
  obtain ⟨rfl, rfl, St0_keys, rfl⟩ := pre
  simp only [castEq]
  by_cases heq : sigmaA = sigmaB
  · rw [dif_pos heq]
    subst sigmaB
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨List.Subset.refl _, (fun _ h => h), St0_keys, True.intro,
      SMT.Typing.eq _ _ _ sigmaA typA typB, (fun _ _ h => h), ?_⟩
    intro Theta hcovA hcovB Theta_none respectsA respectsB Theta_dom
      X Y P hX hY hP denA denB hdenA hdenB hdenAty hdenBty
      relA relB hPiff
    obtain ⟨hcovEq, denEq, respectsEq, hdenEq, hdenEqTy, eqRel⟩ :=
      castEq_direct_rep_semantics hcovA hcovB respectsA respectsB
        hdenA hdenB hdenAty hdenBty relA relB hPiff
    exact ⟨Theta, hcovEq, denEq, RenamingContext.extends_refl Theta,
      Theta_none, respectsEq, Theta_dom, hdenEq, hdenEqTy, eqRel⟩
  · rw [dif_neg heq]
    by_cases hab : sigmaA ⊑ sigmaB
    · rw [dif_pos hab]
      mspec loosenAux_prf_exact_univ (Λ := St0.types)
        (n := St0.env.freshvarsc) (used := St0.env.usedVars)
        typA bvA_used hab.toCastPath
      next out =>
        obtain ⟨helper, spec⟩ := out
        mrename_i pre
        mintro ∀St1
        mpure pre
        obtain ⟨_, St1_types_sub, helper_fresh, helper_not_used,
          used_sub1, St1_keys, preserves1, _, _, typ_helper,
          typ_spec, spec_fv, exactness⟩ := pre
        mspec SMT.declareConst_addSpec_spec (x! := helper)
          (x!_spec := spec) (τ := sigmaB)
          (decl := St1.env.declarations) (as := St1.env.asserts)
          (n := St1.env.freshvarsc) (Γ := St1.types)
          (used := St1.env.usedVars)
        mrename_i pre
        mintro ∀St2
        mpure pre
        obtain ⟨_, _, St2_fvc, St2_used, St2_types⟩ := pre
        mspec Std.Do.Spec.pure
        have Lambda_sub1 : St0.types ⊆ St1.types := fun v hv =>
          St1_types_sub
            (SMT.TypeContext.entries_subset_insert_of_notMem
              helper_fresh hv)
        have typB1 : St1.types ⊢ˢ B : sigmaB :=
          SMT.Typing.weakening Lambda_sub1 typB
            (fun v hv => preserves1 v (bvB_used v hv)
              (SMT.Typing.bv_notMem_context typB v hv))
        have typOut1 : St1.types ⊢ˢ
            (((.var helper) =ˢ B) ∧ˢ spec) : SMTType.bool :=
          SMT.Typing.and _ _ _
            (SMT.Typing.eq _ _ _ sigmaB typ_helper typB1) typ_spec
        have helper_used1 : helper ∈ St1.env.usedVars :=
          St1_keys (AList.lookup_isSome.mp
            (Option.isSome_of_eq_some (SMT.Typing.varE typ_helper)))
        mpure_intro
        rw [St2_used, St2_types]
        refine ⟨used_sub1, Lambda_sub1, St1_keys, True.intro, typOut1,
          preserves1, ?_⟩
        intro Theta hcovA hcovB Theta_none respectsA respectsB Theta_dom
          X Y P hX hY hP denA denB hdenA hdenB hdenAty hdenBty
          relA relB hPiff
        obtain ⟨Theta', hcov, denEq, Theta'_ext, Theta'_none,
            respectsOut, Theta'_dom, _specsTrue, hdenEq,
            hdenEqTy, eqRel⟩ :=
          castEq_left_rep_semantics typA typB Lambda_sub1
          helper_fresh (SMT.Typing.varE typ_helper)
          helper_not_used helper_used1 used_sub1 spec_fv hab.toCastPath
          exactness hcovA hcovB Theta_none respectsA respectsB
          (fun v hv => AList.mem_of_subset Lambda_sub1 (Theta_dom v hv))
          hdenA hdenB hdenAty hdenBty relA relB hPiff
        exact ⟨Theta', hcov, denEq, Theta'_ext, Theta'_none,
          respectsOut, Theta'_dom, hdenEq, hdenEqTy, eqRel⟩
    · rw [dif_neg hab]
      by_cases hba : sigmaB ⊑ sigmaA
      · rw [dif_pos hba]
        mspec loosenAux_prf_exact_univ (Λ := St0.types)
          (n := St0.env.freshvarsc) (used := St0.env.usedVars)
          typB bvB_used hba.toCastPath
        next out =>
          obtain ⟨helper, spec⟩ := out
          mrename_i pre
          mintro ∀St1
          mpure pre
          obtain ⟨_, St1_types_sub, helper_fresh, helper_not_used,
            used_sub1, St1_keys, preserves1, _, _, typ_helper,
            typ_spec, spec_fv, exactness⟩ := pre
          mspec SMT.declareConst_addSpec_spec (x! := helper)
            (x!_spec := spec) (τ := sigmaA)
            (decl := St1.env.declarations) (as := St1.env.asserts)
            (n := St1.env.freshvarsc) (Γ := St1.types)
            (used := St1.env.usedVars)
          mrename_i pre
          mintro ∀St2
          mpure pre
          obtain ⟨_, _, St2_fvc, St2_used, St2_types⟩ := pre
          mspec Std.Do.Spec.pure
          have Lambda_sub1 : St0.types ⊆ St1.types := fun v hv =>
            St1_types_sub
              (SMT.TypeContext.entries_subset_insert_of_notMem
                helper_fresh hv)
          have typA1 : St1.types ⊢ˢ A : sigmaA :=
            SMT.Typing.weakening Lambda_sub1 typA
              (fun v hv => preserves1 v (bvA_used v hv)
                (SMT.Typing.bv_notMem_context typA v hv))
          have typOut1 : St1.types ⊢ˢ
              (((.var helper) =ˢ A) ∧ˢ spec) : SMTType.bool :=
            SMT.Typing.and _ _ _
              (SMT.Typing.eq _ _ _ sigmaA typ_helper typA1) typ_spec
          have helper_used1 : helper ∈ St1.env.usedVars :=
            St1_keys (AList.lookup_isSome.mp
              (Option.isSome_of_eq_some (SMT.Typing.varE typ_helper)))
          mpure_intro
          rw [St2_used, St2_types]
          refine ⟨used_sub1, Lambda_sub1, St1_keys, True.intro, typOut1,
            preserves1, ?_⟩
          intro Theta hcovA hcovB Theta_none respectsA respectsB Theta_dom
            X Y P hX hY hP denA denB hdenA hdenB hdenAty hdenBty
            relA relB hPiff
          have hPiff' : P = ZFSet.zftrue ↔ Y = X := by
            rw [hPiff]
            exact eq_comm
          obtain ⟨Theta', hcov, denEq, Theta'_ext, Theta'_none,
              respectsOut, Theta'_dom, _specsTrue, hdenEq,
              hdenEqTy, eqRel⟩ :=
            castEq_left_rep_semantics typB typA Lambda_sub1
            helper_fresh (SMT.Typing.varE typ_helper)
            helper_not_used helper_used1 used_sub1 spec_fv hba.toCastPath
            exactness hcovB hcovA Theta_none respectsB respectsA
            (fun v hv => AList.mem_of_subset Lambda_sub1 (Theta_dom v hv))
            hdenB hdenA hdenBty hdenAty relB relA hPiff'
          exact ⟨Theta', hcov, denEq, Theta'_ext, Theta'_none,
            respectsOut, Theta'_dom, hdenEq, hdenEqTy, eqRel⟩
      · rw [dif_neg hba]
        mvcgen

/-! ## Declaration-aware equality contract -/

/-- Exactness of a completed equality cast under an arbitrary valuation of
the generated helpers.  A true helper specification must characterize the
actual cast value; mere totality of the specification is not enough once the
declaration is moved under a quantifier. -/
abbrev CastEqRepGuardedSemantics.{u}
    (alpha : BType) (A B t : SMT.Term) (sigmaA sigmaB : SMTType)
    (Lambda : SMT.TypeContext) (Dlt : SMT.Chunk) : Prop :=
  ∀ (GammaSup : SMT.TypeContext),
    ScopedContextExtends Lambda Dlt GammaSup →
    ∀ (Theta : SMT.RenamingContext.Context.{u})
      (hcovA : RenamingContext.CoversFV Theta A)
      (hcovB : RenamingContext.CoversFV Theta B),
      SMT.RenamingContext.RespectsTypeContextOnFV Theta GammaSup A →
      SMT.RenamingContext.RespectsTypeContextOnFV Theta GammaSup B →
      ∀ (X Y P : ZFSet.{u})
        (hX : X ∈ ⟦alpha⟧ᶻ) (hY : Y ∈ ⟦alpha⟧ᶻ)
        (hP : P ∈ ⟦BType.bool⟧ᶻ)
        (denA denB : SMT.Dom.{u}),
        ⟦A.abstract Theta hcovA⟧ˢ = some denA →
        ⟦B.abstract Theta hcovB⟧ˢ = some denB →
        denA.snd.fst = sigmaA → denB.snd.fst = sigmaB →
        RDomCastSupported (⟨X, alpha, hX⟩ : _root_.B.Dom) denA →
        RDomCastSupported (⟨Y, alpha, hY⟩ : _root_.B.Dom) denB →
        (P = ZFSet.zftrue ↔ X = Y) →
        ∀ (hcov_t : RenamingContext.CoversFV Theta t)
          (denEq : SMT.Dom.{u}),
          SMT.RenamingContext.RespectsTypeContextOnFV Theta GammaSup t →
          SpecBodiesTrue Theta GammaSup Dlt →
          ⟦t.abstract Theta hcov_t⟧ˢ = some denEq →
          denEq.snd.fst = SMTType.bool →
          RDomCastSupported (⟨P, BType.bool, hP⟩ : _root_.B.Dom) denEq

/-- Semantic contract of one completed `castEq` run.  The first clause builds
a satisfying helper assignment and the second validates every assignment that
satisfies the generated specifications. -/
abbrev CastEqRepSemantics.{u}
    (alpha : BType) (A B t : SMT.Term) (sigmaA sigmaB : SMTType)
    (Lambda Gamma : SMT.TypeContext) (used0 used1 : List SMT.𝒱)
    (Dlt : SMT.Chunk) : Prop :=
  ∀ (GammaSup : SMT.TypeContext), Gamma ⊆ GammaSup →
    ∀ (Theta : SMT.RenamingContext.Context.{u})
      (hcovA : RenamingContext.CoversFV Theta A)
      (hcovB : RenamingContext.CoversFV Theta B),
      (∀ v ∉ used0, Theta v = none) →
      SMT.RenamingContext.RespectsTypeContextOnFV Theta GammaSup A →
      SMT.RenamingContext.RespectsTypeContextOnFV Theta GammaSup B →
      (∀ v, Theta v ≠ none → v ∈ GammaSup) →
      ∀ (X Y P : ZFSet.{u})
        (hX : X ∈ ⟦alpha⟧ᶻ) (hY : Y ∈ ⟦alpha⟧ᶻ)
        (hP : P ∈ ⟦BType.bool⟧ᶻ)
        (denA denB : SMT.Dom.{u}),
        ⟦A.abstract Theta hcovA⟧ˢ = some denA →
        ⟦B.abstract Theta hcovB⟧ˢ = some denB →
        denA.snd.fst = sigmaA → denB.snd.fst = sigmaB →
        RDomCastSupported (⟨X, alpha, hX⟩ : _root_.B.Dom) denA →
        RDomCastSupported (⟨Y, alpha, hY⟩ : _root_.B.Dom) denB →
        (P = ZFSet.zftrue ↔ X = Y) →
        (∃ (Theta' : SMT.RenamingContext.Context.{u})
          (hcov_t : RenamingContext.CoversFV Theta' t)
          (denEq : SMT.Dom.{u}),
          RenamingContext.Extends Theta' Theta ∧
          (∀ v ∉ used1, Theta' v = none) ∧
          SMT.RenamingContext.RespectsTypeContextOnFV Theta' GammaSup t ∧
          (∀ v, Theta' v ≠ none → v ∈ GammaSup) ∧
          SpecBodiesTrue Theta' GammaSup Dlt ∧
          ⟦t.abstract Theta' hcov_t⟧ˢ = some denEq ∧
          denEq.snd.fst = SMTType.bool ∧
          RDomCastSupported (⟨P, BType.bool, hP⟩ : _root_.B.Dom) denEq) ∧
        CastEqRepGuardedSemantics.{u}
          alpha A B t sigmaA sigmaB Lambda Dlt

/-- Operational and declaration-aware semantic contract selected from the two
supported target representations compared by equality. -/
abbrev CastEqRepScopedSpec.{u} (alpha : BType)
    (A B : SMT.Term) (sigmaA sigmaB : SMTType) : Prop :=
  ∀ {Lambda : SMT.TypeContext} {n : ℕ} {used : List SMT.𝒱}
    {decl : SMT.Chunk},
    Lambda ⊢ˢ A : sigmaA →
    Lambda ⊢ˢ B : sigmaB →
    (∀ v ∈ SMT.bv A, v ∈ used) →
    (∀ v ∈ SMT.bv B, v ∈ used) →
    ⦃fun ⟨E, Lambda'⟩ =>
      ⌜Lambda' = Lambda ∧ E.freshvarsc = n ∧
        Lambda.keys ⊆ E.usedVars ∧ E.usedVars = used ∧
        E.declarations = decl⌝⦄
    castEq ⟨A, sigmaA⟩ ⟨B, sigmaB⟩
    ⦃⇓? ⟨t, sigma⟩ ⟨E', Gamma'⟩ =>
      ⌜used ⊆ E'.usedVars ∧
        Lambda ⊆ Gamma' ∧
        Gamma'.keys ⊆ E'.usedVars ∧
        sigma = SMTType.bool ∧
        Gamma' ⊢ˢ t : SMTType.bool ∧
        SMT.fv A ⊆ SMT.fv t ∧
        SMT.fv B ⊆ SMT.fv t ∧
        (∀ v ∈ used, v ∉ Lambda → v ∉ Gamma') ∧
        ∃ Dlt : SMT.Chunk,
          E'.declarations = decl ++ Dlt ∧
          ContextGeneratedByDeclarations Lambda Gamma' Dlt ∧
          DeclarationContextTrace Lambda Dlt Gamma' ∧
          (∀ v ∈ declVars Dlt, v ∉ used) ∧
          CastEqRepSemantics.{u} alpha A B t sigmaA sigmaB
            Lambda Gamma' used E'.usedVars Dlt ∧
          (∀ b ∈ specBodies Dlt, Gamma' ⊢ˢ b : SMTType.bool) ∧
          ScopedGeneratedTyping Lambda Dlt t SMTType.bool⌝⦄

set_option maxHeartbeats 3000000 in
theorem castEq_left_rep_guarded_semantics.{u}
    {alpha : BType} {A B spec : SMT.Term} {sigmaA sigmaB : SMTType}
    {Lambda GammaSup : SMT.TypeContext} {helper : SMT.𝒱}
    (scope : ScopedContextExtends Lambda
      (helperSpecChunk helper sigmaB spec) GammaSup)
    (c : sigmaA ~> sigmaB)
    (exactness :
      ∀ (Theta : SMT.RenamingContext.Context.{u})
        (hA : RenamingContext.CoversFV Theta A)
        (_respects : SMT.RenamingContext.RespectsTypeContextOnFV
          Theta Lambda A)
        (pf : ∀ (x_ : SMT.𝒱) (X_ : SMT.Dom),
          ∀ v ∈ SMT.fv (SMT.Term.var x_),
            (Function.update Theta x_ (some X_) v).isSome = true),
      ∀ (denA : SMT.Dom), ⟦A.abstract Theta hA⟧ˢ = some denA →
        ∃ (Phi H : SMT.Dom)
          (_ : ⟦(SMT.Term.var helper).abstract
            (Function.update Theta helper (some H)) (pf helper H)⟧ˢ = some H)
          (hphi : RenamingContext.CoversFV
            (Function.update Theta helper (some H)) spec)
          (_ : ⟦spec.abstract (Function.update Theta helper (some H))
            hphi⟧ˢ = some Phi),
          H.snd.fst = sigmaB ∧
          Phi.snd.fst = SMTType.bool ∧
          (Phi.fst = zftrue ∧
            denA.fst.pair H.fst ∈ (castZF_of_path c).1) ∧
          (∀ (Y : SMT.Dom) (_ : Y.snd.fst = sigmaB)
            (hphiY : RenamingContext.CoversFV
              (Function.update Theta helper (some Y)) spec),
            (⟦spec.abstract (Function.update Theta helper (some Y))
              hphiY⟧ˢ).isSome = true ∧
            ∀ {PhiY : SMT.Dom},
              ⟦spec.abstract (Function.update Theta helper (some Y))
                hphiY⟧ˢ = some PhiY →
              PhiY.fst = zftrue →
              denA.fst.pair Y.fst ∈ (castZF_of_path c).1))
    {Theta : SMT.RenamingContext.Context.{u}}
    (hcovA : RenamingContext.CoversFV Theta A)
    (hcovB : RenamingContext.CoversFV Theta B)
    (respectsA : SMT.RenamingContext.RespectsTypeContextOnFV
      Theta GammaSup A)
    (_respectsB : SMT.RenamingContext.RespectsTypeContextOnFV
      Theta GammaSup B)
    {X Y P : ZFSet.{u}}
    {hX : X ∈ ⟦alpha⟧ᶻ} {hY : Y ∈ ⟦alpha⟧ᶻ}
    {hP : P ∈ ⟦BType.bool⟧ᶻ}
    {denA denB : SMT.Dom.{u}}
    (hdenA : ⟦A.abstract Theta hcovA⟧ˢ = some denA)
    (hdenB : ⟦B.abstract Theta hcovB⟧ˢ = some denB)
    (hdenAty : denA.snd.fst = sigmaA)
    (hdenBty : denB.snd.fst = sigmaB)
    (relA : RDomCastSupported (⟨X, alpha, hX⟩ : _root_.B.Dom) denA)
    (relB : RDomCastSupported (⟨Y, alpha, hY⟩ : _root_.B.Dom) denB)
    (hPiff : P = ZFSet.zftrue ↔ X = Y)
    (hcovOut : RenamingContext.CoversFV Theta
      (((.var helper) =ˢ B) ∧ˢ spec))
    (denOut : SMT.Dom.{u})
    (respectsOut : SMT.RenamingContext.RespectsTypeContextOnFV
      Theta GammaSup (((.var helper) =ˢ B) ∧ˢ spec))
    (specsTrue : SpecBodiesTrue Theta GammaSup
      (helperSpecChunk helper sigmaB spec))
    (hdenOut : ⟦((((.var helper) =ˢ B) ∧ˢ spec).abstract
      Theta hcovOut)⟧ˢ = some denOut)
    (_hdenOutTy : denOut.snd.fst = SMTType.bool) :
    RDomCastSupported (⟨P, BType.bool, hP⟩ : _root_.B.Dom) denOut := by
  have respectsA_base :
      SMT.RenamingContext.RespectsTypeContextOnFV Theta Lambda A :=
    respectsA.of_super scope.base
  let pf : ∀ (x_ : SMT.𝒱) (H : SMT.Dom),
      ∀ v ∈ SMT.fv (SMT.Term.var x_),
        (Function.update Theta x_ (some H) v).isSome = true := by
    intro x_ H v hv
    simp only [SMT.fv, List.mem_singleton] at hv
    subst v
    simp
  obtain ⟨_PhiW, _HW, _hdenVarW, _hcovSpecW, _hdenSpecW,
      _HWty, _PhiWty, _castW, guard⟩ :=
    exactness Theta hcovA respectsA_base pf denA hdenA
  obtain ⟨eqVal, heqVal, hdenEq,
      specVal, hspecVal, hdenSpec, denOutEq⟩ :=
    EncodeTermRepresentedBool.CheckedOp.smt_denote_inv
      .and hcovOut hdenOut
  have hspecTrue := specsTrue spec (by simp)
  obtain ⟨hcovSpec, denSpec, _respectsSpec, hdenSpec',
      _hdenSpecTy, hdenSpecTrue⟩ := hspecTrue
  have denSpecEq :
      (⟨specVal, SMTType.bool, hspecVal⟩ : SMT.Dom) = denSpec := by
    have hcovEq : hcovSpec = (fun v hv => hcovOut v (by
        rw [SMT.fv, List.mem_append]
        exact Or.inr hv)) := Subsingleton.elim _ _
    subst hcovSpec
    rw [hdenSpec] at hdenSpec'
    exact Option.some.inj hdenSpec'
  have specValTrue : specVal = ZFSet.zftrue := by
    rw [← denSpecEq] at hdenSpecTrue
    exact hdenSpecTrue
  have helperSome : (Theta helper).isSome = true := by
    apply hcovOut helper
    rw [SMT.fv, List.mem_append]
    exact Or.inl (by
      rw [SMT.fv, List.mem_append]
      exact Or.inl (by simp [SMT.fv]))
  obtain ⟨helperVal, hhelperVal⟩ := Option.isSome_iff_exists.mp helperSome
  have helperFV : helper ∈
      SMT.fv (((.var helper) =ˢ B) ∧ˢ spec) := by
    rw [SMT.fv, List.mem_append]
    exact Or.inl (by
      rw [SMT.fv, List.mem_append]
      exact Or.inl (by simp [SMT.fv]))
  have helperTy : helperVal.snd.fst = sigmaB := by
    have helperLookup : GammaSup.lookup helper = some sigmaB :=
      scope.lookup_of_declared (by simp [declEntries_helperSpecChunk])
    obtain ⟨d, hd, hdty⟩ := respectsOut helperFV helperLookup
    rw [hhelperVal] at hd
    injection hd with hdeq
    subst d
    exact hdty
  have updateEq : Function.update Theta helper (some helperVal) = Theta := by
    rw [← hhelperVal]
    exact Function.update_eq_self helper Theta
  have hcovSpecUpdate : RenamingContext.CoversFV
      (Function.update Theta helper (some helperVal)) spec := by
    rw [updateEq]
    exact fun v hv => hcovOut v (by
      rw [SMT.fv, List.mem_append]
      exact Or.inr hv)
  obtain ⟨_specSome, guardTrue⟩ :=
    guard helperVal helperTy hcovSpecUpdate
  have hdenSpecUpdate :
      ⟦spec.abstract (Function.update Theta helper (some helperVal))
        hcovSpecUpdate⟧ˢ =
        some (⟨specVal, SMTType.bool, hspecVal⟩ : SMT.Dom) := by
    simpa only [updateEq, proof_irrel_heq] using hdenSpec
  have castPair := guardTrue hdenSpecUpdate specValTrue
  rcases denA with ⟨Aval, sigmaA0, hAval⟩
  dsimp at hdenAty
  subst sigmaA0
  rcases denB with ⟨Bval, sigmaB0, hBval⟩
  dsimp at hdenBty
  subst sigmaB0
  have hcast : castZF_apply c Aval = helperVal.fst :=
    castZF_apply_eq_of_pair c hAval castPair
  have hcastEq : helperVal.fst = Bval ↔ X = Y := by
    rw [← hcast]
    exact RDomCastSupported.cast_eq_iff relA relB c
  have hcovVar : RenamingContext.CoversFV Theta (.var helper) := by
    intro v hv
    simp only [SMT.fv, List.mem_singleton] at hv
    subst v
    exact helperSome
  have hdenVar : ⟦(SMT.Term.var helper).abstract Theta hcovVar⟧ˢ =
      some helperVal := by
    rw [SMT.Term.abstract]
    simp only [SMT.denote]
    congr 1
    exact Option.get_of_eq_some _ hhelperVal
  have hdenB' : ⟦B.abstract Theta (fun v hv => hcovOut v (by
      rw [SMT.fv, List.mem_append]
      exact Or.inl (by
        rw [SMT.fv, List.mem_append]
        exact Or.inr hv)))⟧ˢ =
      some (⟨Bval, sigmaB, hBval⟩ : SMT.Dom) := by
    simpa only [proof_irrel_heq] using hdenB
  have hdenVar' : ⟦(SMT.Term.var helper).abstract Theta
      (fun v hv => hcovOut v (by
        rw [SMT.fv, List.mem_append]
        exact Or.inl (by
          rw [SMT.fv, List.mem_append]
          exact Or.inl hv)))⟧ˢ = some helperVal := by
    simpa only [proof_irrel_heq] using hdenVar
  have eqValTrue : eqVal = ZFSet.zftrue ↔ X = Y := by
    have hdenEqRaw := hdenEq
    rw [SMT.Term.abstract] at hdenEqRaw
    exact (denote_eq_fst_eq_zftrue_iff hdenVar' hdenB' helperTy
      hdenEqRaw).trans hcastEq
  subst denOut
  subst specVal
  have outTrue :
      (EncodeTermRepresentedBool.CheckedOp.eval .and eqVal ZFSet.zftrue) =
        ZFSet.zftrue ↔ X = Y := by
    rcases ZFSet.ZFBool.mem_𝔹_iff eqVal |>.mp heqVal with hfalse | htrue
    · simpa [EncodeTermRepresentedBool.CheckedOp.eval,
        overloadBinOp_𝔹, overloadBinOp, hfalse] using eqValTrue
    · simpa [EncodeTermRepresentedBool.CheckedOp.eval,
        overloadBinOp_𝔹, overloadBinOp, htrue] using eqValTrue
  exact RDomCastSupported.bool_of_true_iff (hPiff.trans outTrue.symm)

theorem castEq_direct_rep_scoped_contract.{u}
    (alpha : BType) (A B : SMT.Term) (sigma : SMTType) :
    CastEqRepScopedSpec.{u} alpha A B sigma sigma := by
  unfold CastEqRepScopedSpec
  intro Lambda n used decl typA typB bvA_used bvB_used
  mstart
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_keys, rfl, rfl⟩ := pre
  simp only [castEq]
  rw [dif_pos True.intro]
  mspec Std.Do.Spec.pure
  mpure_intro
  refine ⟨List.Subset.refl _, (fun _ h => h), St_keys, True.intro,
    SMT.Typing.eq _ _ _ sigma typA typB, ?_, ?_, (fun _ _ h => h),
    [], by simp, ContextGeneratedByDeclarations.refl St.types,
    DeclarationContextTrace.nil St.types, (by simp [declVars]), ?_,
    (by simp [specBodies]), ?_⟩
  · intro v hv
    rw [SMT.fv, List.mem_append]
    exact Or.inl hv
  · intro v hv
    rw [SMT.fv, List.mem_append]
    exact Or.inr hv
  · intro GammaSup GammaSub Theta hcovA hcovB Theta_none
      respectsA respectsB Theta_dom X Y P hX hY hP denA denB
      hdenA hdenB hdenAty hdenBty relA relB hPiff
    constructor
    · obtain ⟨hcovEq, denEq, respectsEq, hdenEq, hdenEqTy, eqRel⟩ :=
        castEq_direct_rep_semantics hcovA hcovB respectsA respectsB
          hdenA hdenB hdenAty hdenBty relA relB hPiff
      exact ⟨Theta, hcovEq, denEq, RenamingContext.extends_refl Theta,
        Theta_none, respectsEq, Theta_dom,
        by simp [SpecBodiesTrue, specBodies], hdenEq, hdenEqTy, eqRel⟩
    · intro GammaSupG _scope ThetaG hcovAG hcovBG
        respectsAG respectsBG XG YG PG hXG hYG hPG denAG denBG
        hdenAG hdenBG hdenAGTy hdenBGTy relAG relBG hPGiff
        hcovEqG denEqG _respectsEqG _specsG hdenEqG _hdenEqGTy
      obtain ⟨hcovExpected, denExpected, _respectsExpected,
          hdenExpected, _hdenExpectedTy, expectedRel⟩ :=
        castEq_direct_rep_semantics hcovAG hcovBG respectsAG respectsBG
          hdenAG hdenBG hdenAGTy hdenBGTy relAG relBG hPGiff
      have hcovEq : hcovExpected = hcovEqG := Subsingleton.elim _ _
      subst hcovExpected
      have hdenEq : denExpected = denEqG :=
        Option.some.inj (hdenExpected.symm.trans hdenEqG)
      subst denEqG
      exact expectedRel
  · exact ScopedGeneratedTyping.of_operational
      (ContextGeneratedByDeclarations.refl St.types)
      (SMT.Typing.eq _ _ _ sigma typA typB)
      (by simp [specBodies])

set_option maxHeartbeats 4000000 in
theorem castEq_left_rep_scoped_contract.{u}
    (alpha : BType) (A B : SMT.Term) (sigmaA sigmaB : SMTType)
    (hne : sigmaA ≠ sigmaB) (hle : sigmaA ⊑ sigmaB)
    (hfaith : castPath.FVFaithful hle.toCastPath) :
    CastEqRepScopedSpec.{u} alpha A B sigmaA sigmaB := by
  unfold CastEqRepScopedSpec
  intro Lambda n used decl typA typB bvA_used bvB_used
  mstart
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_keys, St_used_eq, St_decl_eq⟩ := pre
  simp only [castEq]
  rw [dif_neg hne, dif_pos hle]
  mspec (Std.Do.Triple.and _
    (Std.Do.Triple.and _
      (Std.Do.Triple.and _
        (loosenAux_prf_exact_univ
          (Λ := St.types) (n := St.env.freshvarsc)
          (used := St.env.usedVars) typA
          (fun v hv => St_used_eq ▸ bvA_used v hv) hle.toCastPath)
        (loosenAux_prf_fv_of_faithful hfaith
          (used := St.env.usedVars) (n := St.env.freshvarsc)
          (x := A) (by
            intro v hv
            exact St_keys (SMT.Typing.mem_context_of_mem_fv typA hv))))
      (loosenAux_prf_decls hle.toCastPath (decl := decl)))
    (loosenAux_prf_types_eq hle.toCastPath))
  next out =>
  obtain ⟨helper, spec⟩ := out
  mrename_i pre
  mintro ∀St1
  mpure pre
  obtain ⟨⟨⟨⟨_hn1, St1_types_sub, helper_fresh, helper_not_used,
      used_sub1, keys_sub1, preserves1, _typ_helper_insert,
      _typ_spec_insert, typ_helper, typ_spec, spec_fv, exactness⟩,
      _helper_not_used_fv, source_fv_spec, _used_sub_fv⟩,
      St1_decl_eq⟩, ⟨St1_types_exact, _⟩⟩ := pre
  mspec SMT.declareConst_addSpec_spec (x! := helper)
    (x!_spec := spec) (τ := sigmaB)
    (decl := St1.env.declarations) (as := St1.env.asserts)
    (n := St1.env.freshvarsc) (Γ := St1.types)
    (used := St1.env.usedVars)
  mrename_i pre
  mintro ∀St2
  mpure pre
  obtain ⟨St2_decl_eq, _, _St2_fvc, St2_used, St2_types⟩ := pre
  mspec Std.Do.Spec.pure
  have Lambda_sub1 : St.types ⊆ St1.types := fun v hv =>
    St1_types_sub
      (SMT.TypeContext.entries_subset_insert_of_notMem helper_fresh hv)
  have typB1 : St1.types ⊢ˢ B : sigmaB :=
    SMT.Typing.weakening Lambda_sub1 typB
      (fun v hv => preserves1 v (St_used_eq ▸ bvB_used v hv)
        (SMT.Typing.bv_notMem_context typB v hv))
  have typOut : St1.types ⊢ˢ
      (((.var helper) =ˢ B) ∧ˢ spec) : SMTType.bool :=
    SMT.Typing.and _ _ _
      (SMT.Typing.eq _ _ _ sigmaB typ_helper typB1) typ_spec
  have helper_lookup : St1.types.lookup helper = some sigmaB :=
    SMT.Typing.varE typ_helper
  have helper_used1 : helper ∈ St1.env.usedVars :=
    keys_sub1 (AList.lookup_isSome.mp
      (Option.isSome_of_eq_some helper_lookup))
  have helper_ctx_gen : ContextGeneratedByDeclarations St.types St1.types
      (helperSpecChunk helper sigmaB spec) := by
    rw [St1_types_exact]
    exact ContextGeneratedByDeclarations.insert_helper
      St.types helper sigmaB spec helper_fresh
  have helper_ctx_trace : DeclarationContextTrace St.types
      (helperSpecChunk helper sigmaB spec) St1.types := by
    rw [St1_types_exact]
    exact DeclarationContextTrace.helperSpecChunk
      St.types helper sigmaB spec helper_fresh
  have used_sub_out : used ⊆ St1.env.usedVars := by
    simpa [St_used_eq] using used_sub1
  have preserves_out : ∀ v ∈ used, v ∉ St.types → v ∉ St1.types := by
    simpa [St_used_eq] using preserves1
  have helper_not_used_out : helper ∉ used := by
    simpa [St_used_eq] using helper_not_used
  mpure_intro
  rw [St2_used, St2_types]
  refine ⟨used_sub_out, Lambda_sub1, keys_sub1, True.intro, typOut,
    ?_, ?_, preserves_out, helperSpecChunk helper sigmaB spec, ?_,
    helper_ctx_gen, helper_ctx_trace, ?_, ?_, ?_, ?_⟩
  · intro v hv
    rw [SMT.fv, List.mem_append]
    exact Or.inr (source_fv_spec hv)
  · intro v hv
    rw [SMT.fv, List.mem_append]
    exact Or.inl (by
      rw [SMT.fv, List.mem_append]
      exact Or.inr hv)
  · rw [St2_decl_eq, St1_decl_eq]
    simp [helperSpecChunk, List.concat_eq_append, List.append_assoc]
  · intro v hv
    simp only [declVars_helperSpecChunk, List.mem_singleton] at hv
    subst v
    exact helper_not_used_out
  · intro GammaSup GammaSub Theta hcovA hcovB Theta_none
      respectsA respectsB Theta_dom X Y P hX hY hP denA denB
      hdenA hdenB hdenAty hdenBty relA relB hPiff
    have Lambda_sub_sup : St.types ⊆ GammaSup :=
      AList.subset_trans Lambda_sub1 GammaSub
    have respectsA_base :
        SMT.RenamingContext.RespectsTypeContextOnFV Theta St.types A :=
      respectsA.of_super Lambda_sub_sup
    have respectsB_base :
        SMT.RenamingContext.RespectsTypeContextOnFV Theta St.types B :=
      respectsB.of_super Lambda_sub_sup
    have helper_lookup_sup : GammaSup.lookup helper = some sigmaB :=
      AList.lookup_of_subset GammaSub helper_lookup
    constructor
    · exact castEq_left_rep_semantics typA typB Lambda_sub_sup
        helper_fresh helper_lookup_sup
        helper_not_used_out helper_used1
        used_sub_out spec_fv hle.toCastPath exactness
        hcovA hcovB Theta_none respectsA_base respectsB_base Theta_dom
        hdenA hdenB hdenAty hdenBty relA relB hPiff
    · intro GammaSupG scopeG ThetaG hcovAG hcovBG
        respectsAG respectsBG XG YG PG hXG hYG hPG denAG denBG
        hdenAG hdenBG hdenAGTy hdenBGTy relAG relBG hPGiff
        hcovOutG denOutG respectsOutG specsTrueG hdenOutG hdenOutGTy
      exact castEq_left_rep_guarded_semantics scopeG hle.toCastPath
        exactness hcovAG hcovBG respectsAG respectsBG
        hdenAG hdenBG hdenAGTy hdenBGTy relAG relBG hPGiff
        hcovOutG denOutG respectsOutG specsTrueG hdenOutG hdenOutGTy
  · intro body hbody
    simp only [specBodies_helperSpecChunk, List.mem_singleton] at hbody
    subst body
    exact typ_spec
  · exact ScopedGeneratedTyping.of_operational helper_ctx_gen typOut
      (by
        intro body hbody
        simp only [specBodies_helperSpecChunk, List.mem_singleton] at hbody
        subst body
        exact typ_spec)

set_option maxHeartbeats 3000000 in
theorem castEq_right_rep_scoped_contract.{u}
    (alpha : BType) (A B : SMT.Term) (sigmaA sigmaB : SMTType)
    (hne : sigmaA ≠ sigmaB) (hnotle : ¬ sigmaA ⊑ sigmaB)
    (hle : sigmaB ⊑ sigmaA)
    (hfaith : castPath.FVFaithful hle.toCastPath) :
    CastEqRepScopedSpec.{u} alpha A B sigmaA sigmaB := by
  unfold CastEqRepScopedSpec
  intro Lambda n used decl typA typB bvA_used bvB_used
  have castEq_swap :
      castEq (A, sigmaA) (B, sigmaB) =
        castEq (B, sigmaB) (A, sigmaA) := by
    simp [castEq, hne, Ne.symm hne, hnotle, hle]
  mstart
  mintro pre ∀St
  mpure pre
  rw [castEq_swap]
  mspec castEq_left_rep_scoped_contract alpha B A sigmaB sigmaA
    (Ne.symm hne) hle hfaith typB typA bvB_used bvA_used
  rename_i out
  obtain ⟨t, sigma⟩ := out
  mrename_i post
  mintro ∀St'
  mpure post
  obtain ⟨used_sub, types_sub, keys_sub, sigma_eq, typ_t,
      fv_B_t, fv_A_t, preserves, Dlt, decl_eq, ctx_gen, ctx_trace,
      decl_fresh, sem_swap, specs_typ, scoped_typ⟩ := post
  mpure_intro
  refine ⟨used_sub, types_sub, keys_sub, sigma_eq, typ_t,
    fv_A_t, fv_B_t, preserves, Dlt, decl_eq, ctx_gen, ctx_trace,
    decl_fresh, ?_, specs_typ, scoped_typ⟩
  intro GammaSup GammaSub Theta hcovA hcovB Theta_none
    respectsA respectsB Theta_dom X Y P hX hY hP denA denB
    hdenA hdenB hdenAty hdenBty relA relB hPiff
  have hPiffSwap : P = ZFSet.zftrue ↔ Y = X := by
    rw [hPiff]
    exact eq_comm
  obtain ⟨good, guardSwap⟩ := sem_swap GammaSup GammaSub Theta
    hcovB hcovA Theta_none respectsB respectsA Theta_dom
    Y X P hY hX hP denB denA hdenB hdenA hdenBty hdenAty
    relB relA hPiffSwap
  constructor
  · exact good
  · intro GammaSupG scopeG ThetaG hcovAG hcovBG
      respectsAG respectsBG XG YG PG hXG hYG hPG denAG denBG
      hdenAG hdenBG hdenAGTy hdenBGTy relAG relBG hPGiff
      hcovOutG denOutG respectsOutG specsTrueG hdenOutG hdenOutGTy
    have hPGiffSwap : PG = ZFSet.zftrue ↔ YG = XG := by
      rw [hPGiff]
      exact eq_comm
    exact guardSwap GammaSupG scopeG ThetaG hcovBG hcovAG
      respectsBG respectsAG YG XG PG hYG hXG hPG denBG denAG
      hdenBG hdenAG hdenBGTy hdenAGTy relBG relAG hPGiffSwap
      hcovOutG denOutG respectsOutG specsTrueG hdenOutG hdenOutGTy

set_option maxHeartbeats 3000000 in
theorem castEq_supported_rep_scoped_contract.{u}
    (alpha : BType) (A B : SMT.Term) (sigmaA sigmaB : SMTType)
    (_supportedA : BType.SupportedSMT alpha sigmaA)
    (_supportedB : BType.SupportedSMT alpha sigmaB) :
    CastEqRepScopedSpec.{u} alpha A B sigmaA sigmaB := by
  unfold CastEqRepScopedSpec
  intro Lambda n used decl typA typB bvA_used bvB_used
  by_cases heq : sigmaA = sigmaB
  · subst sigmaB
    exact castEq_direct_rep_scoped_contract alpha A B sigmaA
      typA typB bvA_used bvB_used
  · by_cases hab : sigmaA ⊑ sigmaB
    · exact castEq_left_rep_scoped_contract alpha A B sigmaA sigmaB
        heq hab (castPath.fvFaithful hab.toCastPath)
        typA typB bvA_used bvB_used
    · by_cases hba : sigmaB ⊑ sigmaA
      · exact castEq_right_rep_scoped_contract alpha A B sigmaA sigmaB
          heq hab hba (castPath.fvFaithful hba.toCastPath)
          typA typB bvA_used bvB_used
      · simp only [castEq]
        rw [dif_neg heq, dif_neg hab, dif_neg hba]
        mstart
        mintro pre ∀St
        mpure pre
        mspec Std.Do.Spec.throw_StateT

theorem denote_eq_inv_rep.{u}
    {A B : _root_.B.Term} {alpha : BType} {Gamma : _root_.B.TypeContext}
    (typA : Gamma ⊢ᴮ A : alpha) (typB : Gamma ⊢ᴮ B : alpha)
    {Xi : _root_.B.RenamingContext.Context}
    (Xi_fv : ∀ v ∈ _root_.B.fv (A =ᴮ B), (Xi v).isSome = true)
    (wf : _root_.B.RenWF Gamma Xi)
    {P : ZFSet.{u}} {hP : P ∈ ⟦BType.bool⟧ᶻ}
    (hden : ⟦(A =ᴮ B).abstract Xi Xi_fv⟧ᴮ =
      some ⟨P, ⟨BType.bool, hP⟩⟩) :
    ∃ (X Y : ZFSet.{u}) (hX : X ∈ ⟦alpha⟧ᶻ)
      (hY : Y ∈ ⟦alpha⟧ᶻ),
      ⟦A.abstract Xi (fun v hv => Xi_fv v (by
        rw [_root_.B.fv, List.mem_append]
        exact Or.inl hv))⟧ᴮ = some ⟨X, ⟨alpha, hX⟩⟩ ∧
      ⟦B.abstract Xi (fun v hv => Xi_fv v (by
        rw [_root_.B.fv, List.mem_append]
        exact Or.inr hv))⟧ᴮ = some ⟨Y, ⟨alpha, hY⟩⟩ ∧
      (P = ZFSet.zftrue ↔ X = Y) := by
  rw [_root_.B.Term.abstract, _root_.B.denote, Option.pure_def,
    Option.bind_eq_bind, Option.bind_eq_some_iff] at hden
  obtain ⟨⟨X, alphaX, hX⟩, denA, hrest⟩ := hden
  have alphaX_eq := denote_welltyped_eq
    (t := A.abstract Xi (fun v hv => Xi_fv v (by
      rw [_root_.B.fv, List.mem_append]
      exact Or.inl hv))) ?_ denA
  on_goal 2 =>
    use Gamma.abstract («Δ» := Xi), WFTC.of_abstract, alpha
    exact @Typing.of_abstract (t := A) («Δ» := Xi) (Γ := Gamma)
      (τ := alpha) (fun v hv => Xi_fv v (by
        rw [_root_.B.fv, List.mem_append]
        exact Or.inl hv)) typA wf
  dsimp at alphaX_eq
  subst alphaX
  dsimp at hrest
  rw [Option.bind_eq_some_iff] at hrest
  obtain ⟨⟨Y, alphaY, hY⟩, denB, hout⟩ := hrest
  have alphaY_eq := denote_welltyped_eq
    (t := B.abstract Xi (fun v hv => Xi_fv v (by
      rw [_root_.B.fv, List.mem_append]
      exact Or.inr hv))) ?_ denB
  on_goal 2 =>
    use Gamma.abstract («Δ» := Xi), WFTC.of_abstract, alpha
    exact @Typing.of_abstract (t := B) («Δ» := Xi) (Γ := Gamma)
      (τ := alpha) (fun v hv => Xi_fv v (by
        rw [_root_.B.fv, List.mem_append]
        exact Or.inr hv)) typB wf
  dsimp at alphaY_eq
  subst alphaY
  simp only [↓reduceDIte, Option.some.injEq, PSigma.mk.injEq] at hout
  obtain ⟨P_eq, _⟩ := hout
  refine ⟨X, Y, hX, hY, ?_, ?_, ?_⟩
  · simpa only [proof_irrel_heq] using denA
  · simpa only [proof_irrel_heq] using denB
  · subst P
    exact zfEqIn_eq_zftrue_iff hX hY

private theorem encodeTerm_eq_via_maplet
    (A B : _root_.B.Term) (E : _root_.B.Env) :
    encodeTerm (A =ᴮ B) E = (do
      let ⟨p, sigmaP⟩ ← encodeTerm (A ↦ᴮ B) E
      match p, sigmaP with
      | .pair A' B', .pair sigmaA sigmaB =>
          castEq ⟨A', sigmaA⟩ ⟨B', sigmaB⟩
      | _, _ => throw "encodeTerm:eq: impossible maplet result") := by
  simp [encodeTerm]

private theorem denote_pair_inv_eq.{u}
    {A B : SMT.Term} {Theta : SMT.RenamingContext.Context.{u}}
    (hcov : RenamingContext.CoversFV Theta (SMT.Term.pair A B))
    {d : SMT.Dom.{u}}
    (hden : ⟦(SMT.Term.pair A B).abstract Theta hcov⟧ˢ = some d) :
    ∃ (dA dB : SMT.Dom.{u}),
      ⟦A.abstract Theta (fun v hv => hcov v (by
        rw [SMT.fv, List.mem_append]
        exact Or.inl hv))⟧ˢ = some dA ∧
      ⟦B.abstract Theta (fun v hv => hcov v (by
        rw [SMT.fv, List.mem_append]
        exact Or.inr hv))⟧ˢ = some dB ∧
      d = ⟨dA.fst.pair dB.fst,
        SMTType.pair dA.snd.fst dB.snd.fst,
        ZFSet.pair_mem_prod.mpr ⟨dA.snd.snd, dB.snd.snd⟩⟩ := by
  rw [SMT.Term.abstract, SMT.denote, Option.pure_def,
    Option.bind_eq_bind, Option.bind_eq_some_iff] at hden
  obtain ⟨dA, hdenA, hrest⟩ := hden
  rw [Option.bind_eq_some_iff] at hrest
  obtain ⟨dB, hdenB, hout⟩ := hrest
  refine ⟨dA, dB, ?_, ?_, ?_⟩
  · simpa only [proof_irrel_heq] using hdenA
  · simpa only [proof_irrel_heq] using hdenB
  · simpa using hout.symm

set_option maxHeartbeats 5000000 in
theorem encodeTerm_rep_spec.eq_case.{u}
    (A B : _root_.B.Term)
    (A_ih : EncodeTermRepIH.{u} A)
    (B_ih : EncodeTermRepIH.{u} B)
    (E : _root_.B.Env) {Lambda : SMT.TypeContext} {resultType : BType}
    (typ_t : E.context ⊢ᴮ A =ᴮ B : resultType)
    {Xi : _root_.B.RenamingContext.Context}
    (Xi_fv : ∀ v ∈ _root_.B.fv (A =ᴮ B), (Xi v).isSome = true)
    {Theta0 : SMT.RenamingContext.Context.{u}}
    (related : RValuationCastSupportedOnFV Xi Theta0 (A =ᴮ B))
    {used : List SMT.𝒱}
    (Theta0_none : ∀ v ∉ used, Theta0 v = none)
    (Theta0_dom : ∀ v, Theta0 v ≠ none → v ∈ Lambda)
    {P : ZFSet.{u}} {hP : P ∈ ⟦resultType⟧ᶻ}
    (den_t : ⟦(A =ᴮ B).abstract Xi Xi_fv⟧ᴮ =
      some ⟨P, ⟨resultType, hP⟩⟩)
    (vars_used : ∀ v ∈ (A =ᴮ B).vars, v ∈ used)
    (Lambda_inv : ∀ v ∈ (A =ᴮ B).vars,
      v ∈ Lambda → v ∈ E.context)
    (bv_nodup : (_root_.B.bv (A =ᴮ B)).Nodup)
    (respects : _root_.B.RenamingContext.RespectsTypeContextOnFV
      Theta0 Lambda (A =ᴮ B))
    (fv_in_Lambda : ∀ v ∈ _root_.B.fv (A =ᴮ B), v ∈ Lambda)
    (wf : _root_.B.RenWF E.context Xi)
    {n : ℕ} :
    ⦃fun ⟨E0, Lambda'⟩ =>
      ⌜Lambda' = Lambda ∧ E0.freshvarsc = n ∧
        Lambda.keys ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
    encodeTerm (A =ᴮ B) E
    ⦃⇓? (⟨t', sigma⟩ : SMT.Term × SMTType) ⟨E', Gamma'⟩ =>
      ⌜EncodeTermRepPost (A =ᴮ B) resultType Lambda Xi Theta0 used P hP
        E t' sigma E' Gamma'⌝⦄ := by
  mstart
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_keys, St_used_eq⟩ := pre
  rw [encodeTerm_eq_via_maplet]

  obtain ⟨rfl, alpha, typA, typB⟩ := _root_.B.Typing.eqE typ_t
  obtain ⟨X, Y, hX, hY, denA, denB, hPiff⟩ :=
    denote_eq_inv_rep typA typB Xi_fv wf den_t

  let Xi_fv_pair : ∀ v ∈ _root_.B.fv (A ↦ᴮ B), (Xi v).isSome = true :=
    fun v hv => Xi_fv v (by simpa [_root_.B.fv] using hv)
  have den_pair :
      ⟦(A ↦ᴮ B).abstract Xi Xi_fv_pair⟧ᴮ =
        some ⟨X.pair Y,
          ⟨alpha ×ᴮ alpha,
            ZFSet.pair_mem_prod.mpr ⟨hX, hY⟩⟩⟩ := by
    rw [_root_.B.Term.abstract, _root_.B.denote, Option.pure_def,
      Option.bind_eq_bind]
    have denA' :
        ⟦A.abstract Xi (fun v hv => Xi_fv_pair v (by
          rw [_root_.B.fv, List.mem_append]
          exact Or.inl hv))⟧ᴮ =
          some ⟨X, ⟨alpha, hX⟩⟩ := by
      simpa only [proof_irrel_heq] using denA
    have denB' :
        ⟦B.abstract Xi (fun v hv => Xi_fv_pair v (by
          rw [_root_.B.fv, List.mem_append]
          exact Or.inr hv))⟧ᴮ =
          some ⟨Y, ⟨alpha, hY⟩⟩ := by
      simpa only [proof_irrel_heq] using denB
    rw [denA', Option.bind_some, denB']
    rfl

  mspec (Std.Do.Triple.and _
    (encodeTerm_rep_spec.maplet_case A B A_ih B_ih E
      (_root_.B.Typing.maplet typA typB) Xi_fv_pair
      (by simpa [_root_.B.fv] using related)
      Theta0_none Theta0_dom den_pair
      (fun v hv => vars_used v (by
        simpa [_root_.B.Term.vars, _root_.B.fv, _root_.B.bv] using hv))
      (fun v hv => Lambda_inv v (by
        simpa [_root_.B.Term.vars, _root_.B.fv, _root_.B.bv] using hv))
      (by simpa [_root_.B.bv] using bv_nodup)
      (by simpa [_root_.B.fv] using respects)
      (fun v hv => fv_in_Lambda v
        (by simpa [_root_.B.fv] using hv)) wf
      (n := St.env.freshvarsc))
    (encodeTerm_bv_used E (t := A ↦ᴮ B)
      (used := St.env.usedVars) (n := St.env.freshvarsc)
      (decl := St.env.declarations)))
  rename_i out_pair
  obtain ⟨pairTerm, pairType⟩ := out_pair
  mrename_i pre
  mintro ∀Stp
  mpure pre
  dsimp at pre
  obtain ⟨maplet_post, bv_pair_used, _bv_used_sub, _bv_delta⟩ := pre
  obtain ⟨used_sub, types_sub, keys_sub, covers_used,
    _path_pair, typ_pair, shape_pair, preserves,
    Thetap, hcov_pair, Thetap_ext, related_p, Thetap_none, respects_p,
    target_respects_p, Thetap_dom,
    denPair, hden_pair, hdenPair_type, pair_rel, pair_total⟩ :=
    maplet_post
  obtain ⟨Aenc, Benc, sigmaA_shape, sigmaB_shape,
    hpairTerm, hpairType⟩ := shape_pair
  subst pairTerm
  subst pairType
  focus
    rw [hpairType] at typ_pair pair_total
    rw [hpairType]
    obtain ⟨sigmaA0, sigmaB0, hpair_type, typ_Aenc, typ_Benc⟩ :=
      SMT.Typing.pairE typ_pair
    injection hpair_type with hsigmaA hsigmaB
    subst sigmaA0
    subst sigmaB0

    have hcov_Aenc : RenamingContext.CoversFV Thetap Aenc := by
      intro v hv
      exact hcov_pair v (by
        rw [SMT.fv, List.mem_append]
        exact Or.inl hv)
    have hcov_Benc : RenamingContext.CoversFV Thetap Benc := by
      intro v hv
      exact hcov_pair v (by
        rw [SMT.fv, List.mem_append]
        exact Or.inr hv)
    have target_respects_Aenc :
        SMT.RenamingContext.RespectsTypeContextOnFV
          Thetap Stp.types Aenc := by
      intro v xi hv hlookup
      exact target_respects_p (by
        rw [SMT.fv, List.mem_append]
        exact Or.inl hv) hlookup
    have target_respects_Benc :
        SMT.RenamingContext.RespectsTypeContextOnFV
          Thetap Stp.types Benc := by
      intro v xi hv hlookup
      exact target_respects_p (by
        rw [SMT.fv, List.mem_append]
        exact Or.inr hv) hlookup
    obtain ⟨denAenc, denBenc, hden_Aenc, hden_Benc, denPair_eq⟩ :=
      denote_pair_inv_eq hcov_pair hden_pair
    rw [denPair_eq] at hpairType pair_rel
    rcases denAenc with ⟨Aval, tauA, hAval⟩
    rcases denBenc with ⟨Bval, tauB, hBval⟩
    dsimp at hpairType
    injection hpairType with htauA htauB
    subst tauA
    subst tauB
    have pair_rel' : RDomCastSupported
        (⟨X.pair Y, alpha ×ᴮ alpha,
          ZFSet.pair_mem_prod.mpr ⟨hX, hY⟩⟩ : _root_.B.Dom)
        (⟨Aval.pair Bval, SMTType.pair sigmaA_shape sigmaB_shape,
          ZFSet.pair_mem_prod.mpr ⟨hAval, hBval⟩⟩ : SMT.Dom) := by
      simpa only [proof_irrel_heq] using pair_rel
    obtain ⟨componentA_rel, componentB_rel⟩ :=
      RDomCastSupported.of_pair pair_rel'
    have bv_Aenc_used : ∀ v ∈ SMT.bv Aenc, v ∈ Stp.env.usedVars := by
      intro v hv
      exact bv_pair_used v (by
        rw [SMT.bv, List.mem_append]
        exact Or.inl hv)
    have bv_Benc_used : ∀ v ∈ SMT.bv Benc, v ∈ Stp.env.usedVars := by
      intro v hv
      exact bv_pair_used v (by
        rw [SMT.bv, List.mem_append]
        exact Or.inr hv)

    mspec castEq_supported_rep_contract alpha Aenc Benc
      sigmaA_shape sigmaB_shape componentA_rel.supported
      componentB_rel.supported typ_Aenc typ_Benc bv_Aenc_used bv_Benc_used
    rename_i out_eq
    obtain ⟨EqEnc, sigmaEq⟩ := out_eq
    mrename_i post_eq
    mintro ∀Steq
    mpure post_eq
    obtain ⟨used_sub_eq, types_sub_eq, keys_sub_eq, sigmaEq_eq,
      typ_EqEnc, preserves_eq, semantic_eq⟩ := post_eq
    change sigmaEq = SMTType.bool at sigmaEq_eq
    subst sigmaEq
    obtain ⟨ThetaEq, hcov_EqEnc, denEq, ThetaEq_ext, ThetaEq_none,
        target_respects_EqEnc, ThetaEq_dom, hden_EqEnc, hdenEq_type,
        Eq_rel⟩ :=
      semantic_eq Thetap hcov_Aenc hcov_Benc Thetap_none
        target_respects_Aenc target_respects_Benc Thetap_dom
        X Y P hX hY hP
        (⟨Aval, sigmaA_shape, hAval⟩ : SMT.Dom)
        (⟨Bval, sigmaB_shape, hBval⟩ : SMT.Dom)
        hden_Aenc hden_Benc rfl rfl componentA_rel componentB_rel hPiff
    have ThetaEq_ext0 := RenamingContext.extends_trans ThetaEq_ext Thetap_ext
    have types_sub0 : St.types ⊆ Steq.types :=
      fun _ h => types_sub_eq (types_sub h)

    mpure_intro
    and_intros
    · intro v hv
      exact used_sub_eq (used_sub (by simpa [St_used_eq] using hv))
    · exact types_sub0
    · exact keys_sub_eq
    · simpa [_root_.B.fv] using
        (_root_.B.CoversUsedVars.mono used_sub_eq covers_used)
    · exact ⟨castPath.reflexive SMTType.bool⟩
    · exact typ_EqEnc
    · trivial
    · intro v hv hLambda hvars
      apply preserves_eq v (used_sub (by simpa [St_used_eq] using hv))
      exact preserves v (by simpa [St_used_eq] using hv) hLambda
        (by simpa [_root_.B.Term.vars, _root_.B.fv, _root_.B.bv]
          using hvars)
    · refine ⟨ThetaEq, hcov_EqEnc, ThetaEq_ext0,
        related.of_extends ThetaEq_ext0, ThetaEq_none, ?_,
        target_respects_EqEnc, ThetaEq_dom, denEq, hden_EqEnc,
        ?_, ?_, ?_⟩
      · exact respects.of_extends ThetaEq_ext0 types_sub0
          (fun _ h => h) fv_in_Lambda
      · exact hdenEq_type
      · simpa only [proof_irrel_heq] using Eq_rel
      · intro Xi_alt Xi_fv_alt Theta0_alt related_alt wf_alt
          Theta0_alt_none respects_alt Theta0_alt_dom
          P_alt hP_alt den_t_alt
        obtain ⟨X_alt, Y_alt, hX_alt, hY_alt,
            denA_alt, denB_alt, hPiff_alt⟩ :=
          denote_eq_inv_rep typA typB Xi_fv_alt wf_alt den_t_alt
        let Xi_fv_pair_alt :
            ∀ v ∈ _root_.B.fv (A ↦ᴮ B), (Xi_alt v).isSome = true :=
          fun v hv => Xi_fv_alt v
            (by simpa [_root_.B.fv] using hv)
        have den_pair_alt :
            ⟦(A ↦ᴮ B).abstract Xi_alt Xi_fv_pair_alt⟧ᴮ =
              some ⟨X_alt.pair Y_alt,
                ⟨alpha ×ᴮ alpha,
                  ZFSet.pair_mem_prod.mpr ⟨hX_alt, hY_alt⟩⟩⟩ := by
          rw [_root_.B.Term.abstract, _root_.B.denote, Option.pure_def,
            Option.bind_eq_bind]
          have denA_alt' :
              ⟦A.abstract Xi_alt (fun v hv => Xi_fv_pair_alt v (by
                rw [_root_.B.fv, List.mem_append]
                exact Or.inl hv))⟧ᴮ =
                some ⟨X_alt, ⟨alpha, hX_alt⟩⟩ := by
            simpa only [proof_irrel_heq] using denA_alt
          have denB_alt' :
              ⟦B.abstract Xi_alt (fun v hv => Xi_fv_pair_alt v (by
                rw [_root_.B.fv, List.mem_append]
                exact Or.inr hv))⟧ᴮ =
                some ⟨Y_alt, ⟨alpha, hY_alt⟩⟩ := by
            simpa only [proof_irrel_heq] using denB_alt
          rw [denA_alt', Option.bind_some, denB_alt']
          rfl
        have Theta0_alt_none_pair : ∀ v ∉ Stp.env.usedVars,
            Theta0_alt v = none := by
          intro v hv
          by_contra hne
          have hv_Lambda := Theta0_alt_dom v hne
          have hv_used : v ∈ used := by
            rw [← St_used_eq]
            exact St_keys hv_Lambda
          exact hv (used_sub hv_used)
        obtain ⟨Thetap_alt, hcov_pair_alt, denPairAlt, Thetap_alt_ext,
            related_p_alt, Thetap_alt_none, respects_p_alt,
            target_respects_p_alt, Thetap_alt_dom,
            hden_pair_alt, hdenPairAlt_type, pair_alt_rel⟩ :=
          pair_total Xi_alt Xi_fv_pair_alt Theta0_alt
            (by simpa [_root_.B.fv] using related_alt) wf_alt
            Theta0_alt_none_pair
            (by simpa [_root_.B.fv] using respects_alt)
            Theta0_alt_dom (X_alt.pair Y_alt)
            (ZFSet.pair_mem_prod.mpr ⟨hX_alt, hY_alt⟩)
            den_pair_alt
        have hcov_Aenc_alt : RenamingContext.CoversFV Thetap_alt Aenc := by
          intro v hv
          exact hcov_pair_alt v (by
            rw [SMT.fv, List.mem_append]
            exact Or.inl hv)
        have hcov_Benc_alt : RenamingContext.CoversFV Thetap_alt Benc := by
          intro v hv
          exact hcov_pair_alt v (by
            rw [SMT.fv, List.mem_append]
            exact Or.inr hv)
        have target_respects_Aenc_alt :
            SMT.RenamingContext.RespectsTypeContextOnFV
              Thetap_alt Stp.types Aenc := by
          intro v xi hv hlookup
          exact target_respects_p_alt (by
            rw [SMT.fv, List.mem_append]
            exact Or.inl hv) hlookup
        have target_respects_Benc_alt :
            SMT.RenamingContext.RespectsTypeContextOnFV
              Thetap_alt Stp.types Benc := by
          intro v xi hv hlookup
          exact target_respects_p_alt (by
            rw [SMT.fv, List.mem_append]
            exact Or.inr hv) hlookup
        obtain ⟨denAAlt, denBAlt, hden_Aenc_alt,
            hden_Benc_alt, denPairAlt_eq⟩ :=
          denote_pair_inv_eq hcov_pair_alt hden_pair_alt
        rw [denPairAlt_eq] at hdenPairAlt_type pair_alt_rel
        rcases denAAlt with ⟨Aval_alt, tauA_alt, hAval_alt⟩
        rcases denBAlt with ⟨Bval_alt, tauB_alt, hBval_alt⟩
        dsimp at hdenPairAlt_type
        injection hdenPairAlt_type with htauA_alt htauB_alt
        subst tauA_alt
        subst tauB_alt
        have pair_alt_rel' : RDomCastSupported
            (⟨X_alt.pair Y_alt, alpha ×ᴮ alpha,
              ZFSet.pair_mem_prod.mpr ⟨hX_alt, hY_alt⟩⟩ :
                _root_.B.Dom)
            (⟨Aval_alt.pair Bval_alt,
              SMTType.pair sigmaA_shape sigmaB_shape,
              ZFSet.pair_mem_prod.mpr
                ⟨hAval_alt, hBval_alt⟩⟩ : SMT.Dom) := by
          simpa only [proof_irrel_heq] using pair_alt_rel
        obtain ⟨componentA_alt_rel, componentB_alt_rel⟩ :=
          RDomCastSupported.of_pair pair_alt_rel'
        obtain ⟨ThetaEq_alt, hcov_EqEnc_alt, denEq_alt,
            ThetaEq_alt_ext, ThetaEq_alt_none,
            target_respects_EqEnc_alt, ThetaEq_alt_dom,
            hden_EqEnc_alt, hdenEq_alt_type, Eq_alt_rel⟩ :=
          semantic_eq Thetap_alt hcov_Aenc_alt hcov_Benc_alt
            Thetap_alt_none target_respects_Aenc_alt
            target_respects_Benc_alt Thetap_alt_dom
            X_alt Y_alt P_alt hX_alt hY_alt hP_alt
            (⟨Aval_alt, sigmaA_shape, hAval_alt⟩ : SMT.Dom)
            (⟨Bval_alt, sigmaB_shape, hBval_alt⟩ : SMT.Dom)
            hden_Aenc_alt hden_Benc_alt rfl rfl
            componentA_alt_rel componentB_alt_rel hPiff_alt
        have ThetaEq_alt_ext0 :=
          RenamingContext.extends_trans ThetaEq_alt_ext Thetap_alt_ext
        refine ⟨ThetaEq_alt, hcov_EqEnc_alt, denEq_alt,
          ThetaEq_alt_ext0,
          related_alt.of_extends ThetaEq_alt_ext0,
          ThetaEq_alt_none, ?_, target_respects_EqEnc_alt,
          ThetaEq_alt_dom, hden_EqEnc_alt, hdenEq_alt_type, ?_⟩
        · exact respects_alt.of_extends ThetaEq_alt_ext0 types_sub0
            (fun _ h => h) fv_in_Lambda
        · simpa only [proof_irrel_heq] using Eq_alt_rel
