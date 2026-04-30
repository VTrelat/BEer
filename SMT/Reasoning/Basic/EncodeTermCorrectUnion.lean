import SMT.Reasoning.Defs
import SMT.Reasoning.LooseningDefs
import SMT.Reasoning.Basic.StateSpecs
import SMT.Reasoning.Basic.LoosenAuxSpec
import SMT.Reasoning.Axioms

open Std.Do B SMT ZFSet

private theorem mem_retract_set_iff_app_canonical_eq_zftrue'
    {α : BType} {F X : ZFSet} (hF : ⟦α.toSMTType⟧ᶻ.IsFunc 𝔹 F)
    (hRetr : retract (BType.set α) F = X) {x : ZFSet} (hx : x ∈ ⟦α⟧ᶻ) :
    x ∈ X ↔
      ZFSet.fapply F (ZFSet.is_func_is_pfunc hF)
        ⟨ZFSet.fapply (BType.canonicalIsoSMTType α).1
            (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType α).2.1)
            ⟨x, by rwa [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType α).2.1]⟩,
          by
            rw [ZFSet.is_func_dom_eq hF]
            exact ZFSet.fapply_mem_range _ _⟩ = zftrue := by
  rw [←hRetr, retract, ZFSet.mem_sep]
  constructor
  · intro h
    obtain ⟨hx', hmem⟩ := h
    rw [dif_pos hx', dif_pos hF] at hmem
    simpa using hmem
  · intro h
    refine ⟨hx, ?_⟩
    rw [dif_pos hx, dif_pos hF]
    simpa using h

/-!
## `castUnion` specification

The `castUnion` function encodes set union for B terms encoded as characteristic predicates.
When both inputs have the same type `.fun γ .bool`, it builds `λ x. S!(x) ∨ T(x)` where
`S!` is the loosened version of `S` (through a reflexive cast, so semantically equivalent).

Since PHOAS `.or` is defined as `¬(¬a ∧ ¬b)`, the denotation goes through the `.not` and `.and`
cases of `SMT.denote`.
-/

/-!
### Auxiliary: denotation computation for the union lambda

Given S and T encoded as characteristic predicates (`.fun γ .bool`), and X! the
loosened version of S (with X!.1 = den_S.1 via the reflexive cast), the lambda
`λ z : γ. S!(z) ∨ T(z)` denotes successfully and its retract computes the union
of the retracts of den_S and den_T.

The proof requires:
1. Computing the abstract of `.lambda [z] [γ] (.or (.app (.var S!) (.var z)) (.app T (.var z)))` — this gives a PHOAS lambda
2. Showing the PHOAS or-body denotes for all valid inputs (via app denotation + not/and)
3. Computing the ZFSet.lambda value and showing membership in `.fun γ .bool` function space
4. Proving the retract-union: since retract(α.set, f) = {x ∈ ⟦α⟧ᶻ | f(canon(x)) = zftrue},
   and the body computes f(canon(x)) = S(canon(x)) ∨ T(canon(x)), this gives the set union.
-/
/-!
### Direct-path denotation auxiliary for the new `castUnion` (α = β case)

When both inputs have the same type `.fun γ .bool`, `castUnion` builds
`λ z : γ. S(z) ∨ T(z)` directly (no loosening, no S! variable).
The renaming context is `Δ` unchanged.
-/
set_option maxHeartbeats 4000000 in
private theorem castUnion_denotation_direct.{u_1}
    {γ : SMTType} {S T : SMT.Term}
    {z : SMT.𝒱} {«Δ» : SMT.RenamingContext.Context}
    {den_S den_T : SMT.Dom.{u_1}}
    (hS : RenamingContext.CoversFV «Δ» S)
    (hT : RenamingContext.CoversFV «Δ» T)
    (h_den_S : ⟦S.abstract «Δ» hS⟧ˢ = some den_S)
    (h_den_T : ⟦T.abstract «Δ» hT⟧ˢ = some den_T)
    (den_S_type : den_S.2.1 = .fun γ .bool)
    (den_T_type : den_T.2.1 = .fun γ .bool)
    (z_not_fv_S : z ∉ SMT.fv S)
    (z_not_fv_T : z ∉ SMT.fv T)
    (hcov : RenamingContext.CoversFV «Δ»
      (.lambda [z] [γ] (.or (.app S (.var z)) (.app T (.var z))))) :
    ∃ den_t : SMT.Dom.{u_1},
      ⟦(Term.lambda [z] [γ] (.or (.app S (.var z)) (.app T (.var z)))).abstract
        «Δ» hcov⟧ˢ = some den_t ∧
      den_t.2.1 = .fun γ .bool ∧
      (∀ (α : BType), γ = α.toSMTType →
        retract α.set den_t.1 = retract α.set den_S.1 ∪ retract α.set den_T.1) := by
  -- Abbreviations
  set orBody := Term.or (.app S (.var z)) (.app T (.var z)) with horBody_def

  -- 1. IsFunc proofs
  have hdenS_func : ZFSet.IsFunc ⟦γ⟧ᶻ 𝔹 den_S.1 := by
    have hdenS_mem : den_S.1 ∈ ⟦γ⟧ᶻ.funs 𝔹 := by
      simpa [den_S_type, SMTType.toZFSet] using den_S.2.2
    exact ZFSet.mem_funs.mp hdenS_mem
  have hdenT_func : ZFSet.IsFunc ⟦γ⟧ᶻ 𝔹 den_T.1 := by
    have hdenT_mem : den_T.1 ∈ ⟦γ⟧ᶻ.funs 𝔹 := by
      simpa [den_T_type, SMTType.toZFSet] using den_T.2.2
    exact ZFSet.mem_funs.mp hdenT_mem

  -- CoversFV for S and T under z-updates of Δ
  have hcov_S_upd : ∀ W : SMT.Dom,
      RenamingContext.CoversFV (Function.update «Δ» z (some W)) S :=
    fun W => SMT.RenamingContext.coversFV_update_of_notMem z_not_fv_S hS
  have hcov_T_upd : ∀ W : SMT.Dom,
      RenamingContext.CoversFV (Function.update «Δ» z (some W)) T :=
    fun W => SMT.RenamingContext.coversFV_update_of_notMem z_not_fv_T hT

  -- S and T denotation invariance under z update
  have den_S_upd : ∀ W : SMT.Dom,
      ⟦S.abstract (Function.update «Δ» z (some W)) (hcov_S_upd W)⟧ˢ = some den_S := by
    intro W
    have : ⟦S.abstract «Δ» hS⟧ˢ =
        ⟦S.abstract (Function.update «Δ» z (some W)) (hcov_S_upd W)⟧ˢ := by
      rw [←SMT.RenamingContext.denote, ←SMT.RenamingContext.denote]
      exact SMT.RenamingContext.denote_update_of_notMem z_not_fv_S
    rw [←this]; exact h_den_S

  have den_T_upd : ∀ W : SMT.Dom,
      ⟦T.abstract (Function.update «Δ» z (some W)) (hcov_T_upd W)⟧ˢ = some den_T := by
    intro W
    have : ⟦T.abstract «Δ» hT⟧ˢ =
        ⟦T.abstract (Function.update «Δ» z (some W)) (hcov_T_upd W)⟧ˢ := by
      rw [←SMT.RenamingContext.denote, ←SMT.RenamingContext.denote]
      exact SMT.RenamingContext.denote_update_of_notMem z_not_fv_T
    rw [←this]; exact h_den_T

  -- Body denotation: for each valid W, the or-body denotes
  have hbody_den : ∀ (W : SMT.Dom) (hW_ty : W.2.1 = γ) (hW_mem : W.1 ∈ ⟦γ⟧ᶻ),
      ∃ Dbody : SMT.Dom,
        ∃ hcov_or : RenamingContext.CoversFV (Function.update «Δ» z (some W)) orBody,
          ⟦orBody.abstract (Function.update «Δ» z (some W)) hcov_or⟧ˢ = some Dbody ∧
          Dbody.2.1 = .bool ∧
          (Dbody.1 = zftrue ↔
            (ZFSet.fapply den_S.1 (ZFSet.is_func_is_pfunc hdenS_func)
              ⟨W.1, by rwa [ZFSet.is_func_dom_eq hdenS_func]⟩ = zftrue ∨
            ZFSet.fapply den_T.1 (ZFSet.is_func_is_pfunc hdenT_func)
              ⟨W.1, by rwa [ZFSet.is_func_dom_eq hdenT_func]⟩ = zftrue)) := by
    intro W hW_ty hW_mem
    -- Get app denotation for S
    obtain ⟨hcov_S_app_w, DS!, hDS!_ty, hDS!_val, hden_S_app⟩ :=
      funDenoteAppAt
        (Δctx := «Δ») (t := S) (x := z) (α := γ) (β := .bool) (Y := den_S)
        (hcov_t_upd := hcov_S_upd)
        (den_t_upd := den_S_upd)
        (hY_ty := den_S_type)
        (hY_func := hdenS_func)
        W hW_ty hW_mem
    -- Get app denotation for T
    obtain ⟨hcov_T_app_w, DT!, hDT!_ty, hDT!_val, hden_T_app⟩ :=
      funDenoteAppAt
        (Δctx := «Δ») (t := T) (x := z) (α := γ) (β := .bool) (Y := den_T)
        (hcov_t_upd := hcov_T_upd)
        (den_t_upd := den_T_upd)
        (hY_ty := den_T_type)
        (hY_func := hdenT_func)
        W hW_ty hW_mem
    -- Build or denotation
    have hDS!_bool : DS!.2.1 = .bool := hDS!_ty
    have hDT!_bool : DT!.2.1 = .bool := hDT!_ty
    have DS!_mem_𝔹 : DS!.1 ∈ 𝔹 := by have h := DS!.2.2; rwa [hDS!_bool] at h
    have DT!_mem_𝔹 : DT!.1 ∈ 𝔹 := by have h := DT!.2.2; rwa [hDT!_bool] at h
    -- Build CoversFV for or body
    have hcov_or : RenamingContext.CoversFV (Function.update «Δ» z (some W)) orBody := by
      intro v hv
      change v ∈ SMT.fv orBody at hv
      rw [horBody_def] at hv
      simp only [SMT.fv, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
      by_cases hvz : v = z
      · subst hvz; simp [Function.update]
      · rw [Function.update_of_ne hvz]
        rcases hv with ((hv | rfl) | (hv | rfl))
        · exact hS v hv
        · exact absurd rfl hvz
        · exact hT v hv
        · exact absurd rfl hvz
    -- Case analysis on ZFBool values
    rw [ZFSet.ZFBool.mem_𝔹_iff] at DS!_mem_𝔹 DT!_mem_𝔹
    rcases DS!_mem_𝔹 with hDS!_false | hDS!_true <;>
    rcases DT!_mem_𝔹 with hDT!_false | hDT!_true
    · -- Both false
      have hDnot_S := denote_not_eq_zftrue_of_some_zffalse hden_S_app hDS!_bool hDS!_false
      have hDnot_T := denote_not_eq_zftrue_of_some_zffalse hden_T_app hDT!_bool hDT!_false
      have hDand := denote_and_eq_zftrue_of_some_zftrue hDnot_S rfl rfl hDnot_T rfl rfl
      have hDor := denote_not_eq_zffalse_of_some_zftrue hDand rfl rfl
      refine ⟨⟨zffalse, .bool, ZFBool.zffalse_mem_𝔹⟩, hcov_or, ?_, rfl, ?_⟩
      · convert hDor using 1; simp only [horBody_def, SMT.Term.abstract]; rfl
      · constructor
        · intro h; exact (ZFSet.zftrue_ne_zffalse h.symm).elim
        · intro h; rcases h with h | h
          · nomatch ZFSet.zftrue_ne_zffalse (h.symm.trans (hDS!_val.symm.trans hDS!_false))
          · nomatch ZFSet.zftrue_ne_zffalse (h.symm.trans (hDT!_val.symm.trans hDT!_false))
    · -- S false, T true
      have hDnot_S := denote_not_eq_zftrue_of_some_zffalse hden_S_app hDS!_bool hDS!_false
      have hDnot_T := denote_not_eq_zffalse_of_some_zftrue hden_T_app hDT!_bool hDT!_true
      have hDand := denote_and_eq_zffalse_of_some_zffalse_right hDnot_S rfl hDnot_T rfl rfl
      have hDor := denote_not_eq_zftrue_of_some_zffalse hDand rfl rfl
      refine ⟨⟨zftrue, .bool, ZFBool.zftrue_mem_𝔹⟩, hcov_or, ?_, rfl, ?_⟩
      · convert hDor using 1; simp only [horBody_def, SMT.Term.abstract]; rfl
      · exact ⟨fun _ => Or.inr (hDT!_val ▸ hDT!_true), fun _ => rfl⟩
    · -- S true, T false
      have hDnot_S := denote_not_eq_zffalse_of_some_zftrue hden_S_app hDS!_bool hDS!_true
      have hDnot_T := denote_not_eq_zftrue_of_some_zffalse hden_T_app hDT!_bool hDT!_false
      have hDand := denote_and_eq_zffalse_of_some_zffalse_left hDnot_S rfl rfl hDnot_T rfl
      have hDor := denote_not_eq_zftrue_of_some_zffalse hDand rfl rfl
      refine ⟨⟨zftrue, .bool, ZFBool.zftrue_mem_𝔹⟩, hcov_or, ?_, rfl, ?_⟩
      · convert hDor using 1; simp only [horBody_def, SMT.Term.abstract]; rfl
      · exact ⟨fun _ => Or.inl (hDS!_val ▸ hDS!_true), fun _ => rfl⟩
    · -- Both true
      have hDnot_S := denote_not_eq_zffalse_of_some_zftrue hden_S_app hDS!_bool hDS!_true
      have hDnot_T := denote_not_eq_zffalse_of_some_zftrue hden_T_app hDT!_bool hDT!_true
      have hDand := denote_and_eq_zffalse_of_some_zffalse_left hDnot_S rfl rfl hDnot_T rfl
      have hDor := denote_not_eq_zftrue_of_some_zffalse hDand rfl rfl
      refine ⟨⟨zftrue, .bool, ZFBool.zftrue_mem_𝔹⟩, hcov_or, ?_, rfl, ?_⟩
      · convert hDor using 1; simp only [horBody_def, SMT.Term.abstract]; rfl
      · exact ⟨fun _ => Or.inl (hDS!_val ▸ hDS!_true), fun _ => rfl⟩

  -- 6. Lambda assembly + retract equality
  have hcov_orBody_upd :
      ∀ W : SMT.Dom,
        RenamingContext.CoversFV (Function.update «Δ» z (some W)) orBody := by
    intro W v hv
    change v ∈ SMT.fv orBody at hv
    rw [horBody_def] at hv
    simp only [SMT.fv, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
    by_cases hvz : v = z
    · subst hvz; simp [Function.update]
    · rw [Function.update_of_ne hvz]
      rcases hv with ((hv | rfl) | (hv | rfl))
      · exact hS v hv
      · exact absurd rfl hvz
      · exact hT v hv
      · exact absurd rfl hvz
  have hgo_cov : ∀ v ∈ SMT.fv orBody, v ∉ [z] → («Δ» v).isSome = true := by
    intro v hv hvz
    have hvz' : v ≠ z := by simpa [List.mem_singleton] using hvz
    have := hcov_orBody_upd ⟨γ.defaultZFSet, γ, SMTType.mem_toZFSet_of_defaultZFSet⟩ v hv
    rwa [Function.update_of_ne hvz'] at this
  have hbody_total : ∀ W : SMT.Dom, W.snd.fst = γ →
      ⟦orBody.abstract (Function.update «Δ» z (some W)) (hcov_orBody_upd W)⟧ˢ.isSome = true := by
    intro W hW_ty
    have hW_mem : W.fst ∈ ⟦γ⟧ᶻ := by rw [← hW_ty]; exact W.snd.snd
    obtain ⟨Dbody, hcov_or, hden_body, _⟩ := hbody_den W hW_ty hW_mem
    rw [show hcov_orBody_upd W = hcov_or from Subsingleton.elim _ _]
    exact Option.isSome_of_eq_some hden_body
  have hbody_ty : ∀ (W : SMT.Dom), W.snd.fst = γ → ∀ D,
      ⟦orBody.abstract (Function.update «Δ» z (some W)) (hcov_orBody_upd W)⟧ˢ = some D →
      D.snd.fst = .bool := by
    intro W hW_ty D hden
    have hW_mem : W.fst ∈ ⟦γ⟧ᶻ := by rw [← hW_ty]; exact W.snd.snd
    obtain ⟨Dbody, hcov_or, hden_body, hDbody_ty, _⟩ := hbody_den W hW_ty hW_mem
    rw [show hcov_orBody_upd W = hcov_or from Subsingleton.elim _ _] at hden
    cases hden.symm.trans hden_body
    exact hDbody_ty

  -- Lambda isSome
  have hsome_lambda : ⟦((λˢ [z]) [γ] orBody).abstract «Δ» hcov⟧ˢ.isSome = true := by
    rw [SMT.Term.abstract, dif_pos (by rfl), SMT.denote]
    have hlen : [z].length > 0 := by simp
    rw [dif_pos hlen]
    split_ifs with den_t_isSome den_t_typ_det
    · simp
    · exfalso; apply den_t_typ_det
      intro x y hx hy
      let Wx : SMT.Dom := x ⟨0, by simp⟩
      let Wy : SMT.Dom := y ⟨0, by simp⟩
      have hWx_ty : Wx.snd.fst = γ := by simpa [Wx] using (hx ⟨0, by simp⟩).1
      have hWy_ty : Wy.snd.fst = γ := by simpa [Wy] using (hy ⟨0, by simp⟩).1
      have hgo_x := funAbstractGoSingle (Δctx := «Δ») (P := orBody) (v := z) (τ := γ)
        hgo_cov hcov_orBody_upd x hx
      have hgo_y := funAbstractGoSingle (Δctx := «Δ») (P := orBody) (v := z) (τ := γ)
        hgo_cov hcov_orBody_upd y hy
      obtain ⟨Dx, hDx⟩ := Option.isSome_iff_exists.mp (hbody_total Wx hWx_ty)
      obtain ⟨Dy, hDy⟩ := Option.isSome_iff_exists.mp (hbody_total Wy hWy_ty)
      have hden_x : ⟦(SMT.Term.abstract.go orBody [z] «Δ» hgo_cov).uncurry x⟧ˢ = some Dx := by
        rw [hgo_x]; exact hDx
      have hden_y : ⟦(SMT.Term.abstract.go orBody [z] «Δ» hgo_cov).uncurry y⟧ˢ = some Dy := by
        rw [hgo_y]; exact hDy
      calc (⟦(SMT.Term.abstract.go orBody [z] «Δ» hgo_cov).uncurry x⟧ˢ.get
              (den_t_isSome hx)).snd.fst
          = Dx.snd.fst := congrArg (·.snd.fst) (Option.get_of_eq_some (den_t_isSome hx) hden_x)
        _ = SMTType.bool := hbody_ty Wx hWx_ty Dx hDx
        _ = Dy.snd.fst := (hbody_ty Wy hWy_ty Dy hDy).symm
        _ = (⟦(SMT.Term.abstract.go orBody [z] «Δ» hgo_cov).uncurry y⟧ˢ.get
              (den_t_isSome hy)).snd.fst :=
            (congrArg (·.snd.fst) (Option.get_of_eq_some (den_t_isSome hy) hden_y)).symm
    · exfalso; apply den_t_isSome
      intro x hx
      let Wx : SMT.Dom := x ⟨0, by simp⟩
      have hWx_ty : Wx.snd.fst = γ := by simpa [Wx] using (hx ⟨0, by simp⟩).1
      rw [funAbstractGoSingle (Δctx := «Δ») (P := orBody) (v := z) (τ := γ)
        hgo_cov hcov_orBody_upd x hx]
      exact hbody_total Wx hWx_ty

  -- Build body function
  classical
  set bodyFun : ZFSet → ZFSet := fun x₁ =>
    if hx : x₁.hasArity 1 ∧ x₁ ∈ ⟦γ⟧ᶻ then
      let W : SMT.Dom := ⟨x₁, γ, hx.2⟩
      if hsome : ⟦orBody.abstract (Function.update «Δ» z (some W))
          (hcov_orBody_upd W)⟧ˢ.isSome then
        (⟦orBody.abstract (Function.update «Δ» z (some W))
            (hcov_orBody_upd W)⟧ˢ.get hsome).fst
      else SMTType.bool.defaultZFSet
    else SMTType.bool.defaultZFSet with hbodyFun_def
  have hbodyFun_range : ∀ {x₁ : ZFSet}, x₁ ∈ ⟦γ⟧ᶻ → bodyFun x₁ ∈ 𝔹 := by
    intro x₁ hx₁
    simp only [bodyFun]
    have hx_cast : x₁.hasArity 1 ∧ x₁ ∈ ⟦γ⟧ᶻ := ⟨(funUnaryTarget hx₁).1, hx₁⟩
    rw [dif_pos hx_cast]
    let W : SMT.Dom := ⟨x₁, γ, hx₁⟩
    have hsome := hbody_total W rfl
    rw [dif_pos hsome]
    have hW_mem : W.fst ∈ ⟦γ⟧ᶻ := hx₁
    obtain ⟨Dbody, hcov_or, hden_body, hDbody_ty, _⟩ := hbody_den W rfl hW_mem
    rw [show hcov_orBody_upd W = hcov_or from Subsingleton.elim _ _] at hsome ⊢
    have hget_eq := Option.get_of_eq_some hsome hden_body
    rw [congrArg (·.fst) hget_eq]
    have : Dbody.fst ∈ ⟦Dbody.snd.fst⟧ᶻ := Dbody.snd.snd
    rwa [hDbody_ty] at this
  have hbodyFun_eq : ∀ (w : ZFSet) (hw : w ∈ ⟦γ⟧ᶻ),
      ∃ Dbody : SMT.Dom,
        ⟦orBody.abstract (Function.update «Δ» z (some ⟨w, γ, hw⟩))
          (hcov_orBody_upd ⟨w, γ, hw⟩)⟧ˢ = some Dbody ∧
        bodyFun w = Dbody.fst := by
    intro w hw
    let W : SMT.Dom := ⟨w, γ, hw⟩
    obtain ⟨Dbody, hcov_or, hden_body, _⟩ := hbody_den W rfl hw
    refine ⟨Dbody, ?_, ?_⟩
    · rw [show hcov_orBody_upd W = hcov_or from Subsingleton.elim _ _]; exact hden_body
    · simp only [bodyFun]
      have hx_cast : w.hasArity 1 ∧ w ∈ ⟦γ⟧ᶻ := ⟨(funUnaryTarget hw).1, hw⟩
      rw [dif_pos hx_cast]
      have hsome := hbody_total W rfl
      rw [dif_pos hsome]
      rw [show hcov_orBody_upd W = hcov_or from Subsingleton.elim _ _] at hsome ⊢
      exact congrArg (·.fst) (Option.get_of_eq_some hsome hden_body)
  set lamFun := ZFSet.lambda ⟦γ⟧ᶻ 𝔹 bodyFun with hlamFun_def
  have hlamFun_func : ZFSet.IsFunc ⟦γ⟧ᶻ 𝔹 lamFun :=
    ZFSet.lambda_isFunc (fun {z} hz => hbodyFun_range hz)
  have hlamFun_mem : lamFun ∈ ⟦γ.fun SMTType.bool⟧ᶻ := by
    simp [SMTType.toZFSet]; exact hlamFun_func
  have hlamFun_fapply : ∀ (w : ZFSet) (hw : w ∈ ⟦γ⟧ᶻ),
      ZFSet.fapply lamFun (ZFSet.is_func_is_pfunc hlamFun_func)
        ⟨w, by rw [ZFSet.is_func_dom_eq hlamFun_func]; exact hw⟩ = bodyFun w := by
    intro w hw; exact ZFSet.fapply_lambda (hf := fun {z} hz => hbodyFun_range hz) (ha := hw)
  obtain ⟨lamVal, hlamVal⟩ := Option.isSome_iff_exists.mp hsome_lambda
  have hlamVal_saved := hlamVal

  have hlamVal_ty : lamVal.snd.fst = .fun γ .bool := by
    have hlamVal' := hlamVal
    rw [SMT.Term.abstract, dif_pos (by rfl)] at hlamVal'
    simp only [SMT.denote] at hlamVal'
    rw [dif_pos (show [z].length > 0 by exact Nat.zero_lt_succ 0)] at hlamVal'
    split_ifs at hlamVal' with h_isSome h_typ_det
    · let xd : Fin 1 → SMT.Dom := fun _ => ⟨γ.defaultZFSet, γ, SMTType.mem_toZFSet_of_defaultZFSet⟩
      have hxd_spec : ∀ i, (xd i).2.1 = [γ][↑i] ∧ (xd i).1 ∈ ⟦[γ][↑i]⟧ᶻ := by
        intro ⟨i, hi⟩; simp at hi; subst hi; exact ⟨rfl, SMTType.mem_toZFSet_of_defaultZFSet⟩
      have hgo_d := funAbstractGoSingle (Δctx := «Δ») (P := orBody) (v := z) (τ := γ)
        hgo_cov hcov_orBody_upd xd hxd_spec
      obtain ⟨Dd, hDd⟩ := Option.isSome_iff_exists.mp (hbody_total (xd ⟨0, by simp⟩) rfl)
      have hden_d : ⟦(SMT.Term.abstract.go orBody [z] «Δ» hgo_cov).uncurry xd⟧ˢ = some Dd := by
        rw [hgo_d]; exact hDd
      have hγ_out : (⟦(SMT.Term.abstract.go orBody [z] «Δ» hgo_cov).uncurry xd⟧ˢ.get
          (h_isSome hxd_spec)).snd.fst = .bool := by
        rw [congrArg (·.snd.fst) (Option.get_of_eq_some _ hden_d)]
        exact hbody_ty (xd ⟨0, Nat.one_pos⟩) rfl Dd hDd
      simp only [Option.pure_def, Option.some.injEq] at hlamVal'
      rw [show lamVal.snd.fst = _ from congrArg (·.snd.fst) hlamVal'.symm]
      simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.sub_self,
        Fin.foldr_zero, List.getElem_cons_zero]
      exact congrArg (γ.fun ·) hγ_out

  have hlamVal_func : ZFSet.IsFunc ⟦γ⟧ᶻ 𝔹 lamVal.fst := by
    have : lamVal.fst ∈ ⟦γ⟧ᶻ.funs 𝔹 := by
      simpa [hlamVal_ty, SMTType.toZFSet] using lamVal.snd.snd
    exact ZFSet.mem_funs.mp this

  have hlamVal_app : ∀ (w : ZFSet) (hw : w ∈ ⟦γ⟧ᶻ),
      ∃ Dbody : SMT.Dom,
        ⟦orBody.abstract (Function.update «Δ» z (some ⟨w, γ, hw⟩))
          (hcov_orBody_upd ⟨w, γ, hw⟩)⟧ˢ = some Dbody ∧
        ZFSet.fapply lamVal.fst (ZFSet.is_func_is_pfunc hlamVal_func)
          ⟨w, by rw [ZFSet.is_func_dom_eq hlamVal_func]; exact hw⟩ = Dbody.fst := by
    intro w hw
    obtain ⟨Dbody, hden_body, hbf_eq⟩ := hbodyFun_eq w hw
    refine ⟨Dbody, hden_body, ?_⟩
    have hlamVal' := hlamVal_saved
    rw [SMT.Term.abstract, dif_pos (by rfl)] at hlamVal'
    simp only [SMT.denote] at hlamVal'
    rw [dif_pos (show [z].length > 0 by exact Nat.zero_lt_succ 0)] at hlamVal'
    split_ifs at hlamVal' with h_isSome h_typ_det
    · let xd : Fin 1 → SMT.Dom := fun _ => ⟨γ.defaultZFSet, γ, SMTType.mem_toZFSet_of_defaultZFSet⟩
      have hxd_spec : ∀ i, (xd i).2.1 = [γ][↑i] ∧ (xd i).1 ∈ ⟦[γ][↑i]⟧ᶻ := by
        intro ⟨i, hi⟩; simp at hi; subst hi; exact ⟨rfl, SMTType.mem_toZFSet_of_defaultZFSet⟩
      have hgo_d := funAbstractGoSingle (Δctx := «Δ») (P := orBody) (v := z) (τ := γ)
        hgo_cov hcov_orBody_upd xd hxd_spec
      obtain ⟨Dd, hDd⟩ := Option.isSome_iff_exists.mp (hbody_total (xd ⟨0, by simp⟩) rfl)
      have hden_d : ⟦(SMT.Term.abstract.go orBody [z] «Δ» hgo_cov).uncurry xd⟧ˢ = some Dd := by
        rw [hgo_d]; exact hDd
      have hγ_out : (⟦(SMT.Term.abstract.go orBody [z] «Δ» hgo_cov).uncurry xd⟧ˢ.get
          (h_isSome hxd_spec)).snd.fst = .bool := by
        rw [congrArg (·.snd.fst) (Option.get_of_eq_some _ hden_d)]
        exact hbody_ty (xd ⟨0, Nat.one_pos⟩) rfl Dd hDd
      simp only [Option.pure_def, Option.some.injEq] at hlamVal'
      have hlamVal_fst : lamVal.fst = _ := congrArg (·.fst) hlamVal'.symm
      simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.sub_self,
        Fin.foldr_zero, List.getElem_cons_zero] at hlamVal_fst
      have hlamVal_eq_lamFun : lamVal.fst = lamFun :=
        (ZFSet.is_func_ext_iff hlamVal_func hlamFun_func).mpr fun w' hw' => by
          apply Subtype.ext
          rw [hlamFun_fapply w' hw']
          obtain ⟨Dbody', hden_body', hbf_eq'⟩ := hbodyFun_eq w' hw'
          rw [hbf_eq']
          have h_pair_mem_lamFun : w'.pair (bodyFun w') ∈ lamFun := by
            rw [hlamFun_def, ZFSet.mem_lambda]
            exact ⟨w', bodyFun w', rfl, hw', hbodyFun_range hw', rfl⟩
          have hval_eq : lamVal.fst = _ := congrArg (·.fst) hlamVal'.symm
          have h_pair_mem : w'.pair Dbody'.fst ∈ lamVal.fst := by
            rw [hval_eq]
            simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.sub_self,
              Fin.foldr_zero, List.getElem_cons_zero]
            rw [ZFSet.mem_lambda]
            refine ⟨w', Dbody'.fst, rfl, hw', ?_, ?_⟩
            · have hD_ty := hbody_ty ⟨w', γ, hw'⟩ rfl Dbody' hden_body'
              have : Dbody'.fst ∈ ⟦Dbody'.snd.fst⟧ᶻ := Dbody'.snd.snd
              rw [hD_ty] at this
              convert this using 2
            · split_ifs with hw'_cond
              · let xₙ := fun i : Fin 1 => (⟨w'.get 1 i, [γ][↑i], hw'_cond.2 i⟩ : SMT.Dom)
                have hgo' := funAbstractGoSingle (Δctx := «Δ») (P := orBody) (v := z) (τ := γ)
                  hgo_cov hcov_orBody_upd xₙ (fun i => ⟨rfl, hw'_cond.2 i⟩)
                have hxₙ_eq : xₙ ⟨0, Nat.zero_lt_one⟩ = ⟨w', γ, hw'⟩ := rfl
                have hden' : ⟦(SMT.Term.abstract.go orBody [z] «Δ» hgo_cov).uncurry xₙ⟧ˢ = some Dbody' := by
                  rw [hgo', hxₙ_eq]; exact hden_body'
                exact (congrArg (·.fst) (Option.get_of_eq_some _ hden')).symm
              · exfalso; apply hw'_cond
                exact ⟨trivial, fun ⟨i, hi⟩ => by
                  have : i = 0 := Nat.lt_one_iff.mp hi; subst this
                  exact hw'⟩
          have h_fapply := ZFSet.fapply.of_pair (ZFSet.is_func_is_pfunc hlamVal_func) h_pair_mem
          rw [Subtype.ext_iff] at h_fapply
          exact h_fapply
      have := (ZFSet.is_func_ext_iff hlamVal_func hlamFun_func).mp hlamVal_eq_lamFun w hw
      rw [this, hlamFun_fapply w hw]
      exact hbf_eq

  -- Main conclusion
  refine ⟨lamVal, ?_, hlamVal_ty, ?_⟩
  · convert hlamVal using 2
  · intro α hα
    subst hα
    ext x
    simp only [ZFSet.mem_union]
    have retract_mem_α : ∀ {F : ZFSet}, x ∈ retract α.set F → x ∈ ⟦α⟧ᶻ := by
      intro F hx
      rw [retract, ZFSet.mem_sep] at hx
      exact hx.1
    let mk_cx (hx_α : x ∈ ⟦α⟧ᶻ) : ZFSet := ZFSet.fapply (BType.canonicalIsoSMTType α).1
      (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType α).2.1)
      ⟨x, by rwa [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType α).2.1]⟩
    have mk_cx_mem (hx_α : x ∈ ⟦α⟧ᶻ) : mk_cx hx_α ∈ ⟦α.toSMTType⟧ᶻ :=
      ZFSet.fapply_mem_range _ _
    have fapply_iff (hx_α : x ∈ ⟦α⟧ᶻ)
        {F : ZFSet} (hF_func : ZFSet.IsFunc ⟦α.toSMTType⟧ᶻ 𝔹 F) :
        x ∈ retract α.set F ↔
        ZFSet.fapply F (ZFSet.is_func_is_pfunc hF_func)
          ⟨mk_cx hx_α, by rw [ZFSet.is_func_dom_eq hF_func]; exact mk_cx_mem hx_α⟩ = zftrue :=
      mem_retract_set_iff_app_canonical_eq_zftrue' hF_func rfl hx_α
    constructor
    · intro hx_mem
      have hx_α := retract_mem_α hx_mem
      rw [fapply_iff hx_α hlamVal_func] at hx_mem
      have hcx_mem := mk_cx_mem hx_α
      obtain ⟨Dbody, hden_body, hfapply_eq⟩ := hlamVal_app (mk_cx hx_α) hcx_mem
      obtain ⟨Dbody', hcov_or, hden_body', _, hDbody'_iff⟩ :=
        hbody_den ⟨mk_cx hx_α, α.toSMTType, hcx_mem⟩ rfl hcx_mem
      have hDbody_eq : Dbody = Dbody' := by
        rw [show hcov_orBody_upd ⟨mk_cx hx_α, α.toSMTType, hcx_mem⟩ = hcov_or from
          Subsingleton.elim _ _] at hden_body
        exact Option.some_injective _ (hden_body.symm.trans hden_body')
      rw [hfapply_eq, hDbody_eq] at hx_mem
      rcases hDbody'_iff.mp hx_mem with hS_true | hT_true
      · left; rw [fapply_iff hx_α hdenS_func]; exact hS_true
      · right; rw [fapply_iff hx_α hdenT_func]; exact hT_true
    · intro hx_mem
      rcases hx_mem with hx_S | hx_T
      · have hx_α := retract_mem_α hx_S
        rw [fapply_iff hx_α hdenS_func] at hx_S
        have hcx_mem := mk_cx_mem hx_α
        obtain ⟨Dbody, hden_body, hfapply_eq⟩ := hlamVal_app (mk_cx hx_α) hcx_mem
        obtain ⟨Dbody', hcov_or, hden_body', _, hDbody'_iff⟩ :=
          hbody_den ⟨mk_cx hx_α, α.toSMTType, hcx_mem⟩ rfl hcx_mem
        have hDbody_eq : Dbody = Dbody' := by
          rw [show hcov_orBody_upd ⟨mk_cx hx_α, α.toSMTType, hcx_mem⟩ = hcov_or from
            Subsingleton.elim _ _] at hden_body
          exact Option.some_injective _ (hden_body.symm.trans hden_body')
        rw [fapply_iff hx_α hlamVal_func, hfapply_eq, hDbody_eq]
        exact hDbody'_iff.mpr (Or.inl hx_S)
      · have hx_α := retract_mem_α hx_T
        rw [fapply_iff hx_α hdenT_func] at hx_T
        have hcx_mem := mk_cx_mem hx_α
        obtain ⟨Dbody, hden_body, hfapply_eq⟩ := hlamVal_app (mk_cx hx_α) hcx_mem
        obtain ⟨Dbody', hcov_or, hden_body', _, hDbody'_iff⟩ :=
          hbody_den ⟨mk_cx hx_α, α.toSMTType, hcx_mem⟩ rfl hcx_mem
        have hDbody_eq : Dbody = Dbody' := by
          rw [show hcov_orBody_upd ⟨mk_cx hx_α, α.toSMTType, hcx_mem⟩ = hcov_or from
            Subsingleton.elim _ _] at hden_body
          exact Option.some_injective _ (hden_body.symm.trans hden_body')
        rw [fapply_iff hx_α hlamVal_func, hfapply_eq, hDbody_eq]
        exact hDbody'_iff.mpr (Or.inr hx_T)

set_option maxHeartbeats 4000000 in
private theorem castUnion_denotation_aux.{u_1}
    {γ : SMTType} {S T : SMT.Term}
    {z S! : SMT.𝒱} {«Δ» : SMT.RenamingContext.Context}
    {den_S den_T X! : SMT.Dom.{u_1}}
    (hS : RenamingContext.CoversFV «Δ» S)
    (hT : RenamingContext.CoversFV «Δ» T)
    (h_den_S : ⟦S.abstract «Δ» hS⟧ˢ = some den_S)
    (h_den_T : ⟦T.abstract «Δ» hT⟧ˢ = some den_T)
    (den_S_type : den_S.2.1 = .fun γ .bool)
    (den_T_type : den_T.2.1 = .fun γ .bool)
    (X!_type : X!.2.1 = .fun γ .bool)
    (X!_val_eq : X!.1 = den_S.1)
    (z_ne_S! : z ≠ S!)
    (S!_not_fv_T : S! ∉ SMT.fv T)
    (z_not_fv_S : z ∉ SMT.fv S)
    (z_not_fv_T : z ∉ SMT.fv T)
    (hΔ_S!_none : «Δ» S! = none)
    (hcov : RenamingContext.CoversFV (Function.update «Δ» S! (some X!))
      (.lambda [z] [γ] (.or (.app (.var S!) (.var z)) (.app T (.var z))))) :
    ∃ den_t : SMT.Dom.{u_1},
      ⟦(Term.lambda [z] [γ] (.or (.app (.var S!) (.var z)) (.app T (.var z)))).abstract
        (Function.update «Δ» S! (some X!)) hcov⟧ˢ = some den_t ∧
      den_t.2.1 = .fun γ .bool ∧
      (∀ (α : BType), γ = α.toSMTType →
        retract α.set den_t.1 = retract α.set den_S.1 ∪ retract α.set den_T.1) := by
  -- Abbreviations
  set Δ' := Function.update «Δ» S! (some X!) with hΔ'_def
  set orBody := Term.or (.app (.var S!) (.var z)) (.app T (.var z)) with horBody_def

  -- 1. IsFunc proofs from membership in ⟦.fun γ .bool⟧ᶻ
  have hX!_func : ZFSet.IsFunc ⟦γ⟧ᶻ 𝔹 X!.1 := by
    have hX!_mem : X!.1 ∈ ⟦γ⟧ᶻ.funs 𝔹 := by
      simpa [X!_type, SMTType.toZFSet] using X!.2.2
    exact ZFSet.mem_funs.mp hX!_mem
  have hdenT_func : ZFSet.IsFunc ⟦γ⟧ᶻ 𝔹 den_T.1 := by
    have hdenT_mem : den_T.1 ∈ ⟦γ⟧ᶻ.funs 𝔹 := by
      simpa [den_T_type, SMTType.toZFSet] using den_T.2.2
    exact ZFSet.mem_funs.mp hdenT_mem
  have hdenS_func : ZFSet.IsFunc ⟦γ⟧ᶻ 𝔹 den_S.1 := by
    have hdenS_mem : den_S.1 ∈ ⟦γ⟧ᶻ.funs 𝔹 := by
      simpa [den_S_type, SMTType.toZFSet] using den_S.2.2
    exact ZFSet.mem_funs.mp hdenS_mem

  -- 2. S! ∉ fv S (since Δ S! = none)
  have S!_not_fv_S : S! ∉ SMT.fv S := by
    intro hmem
    have := hS S! hmem
    rw [hΔ_S!_none] at this
    exact Bool.false_ne_true this

  -- CoversFV for S and T under z-updates of Δ'
  have hcov_S_Δ' : RenamingContext.CoversFV Δ' S :=
    SMT.RenamingContext.coversFV_update_of_notMem S!_not_fv_S hS
  have hcov_T_Δ' : RenamingContext.CoversFV Δ' T :=
    SMT.RenamingContext.coversFV_update_of_notMem S!_not_fv_T hT

  have hcov_S_upd : ∀ W : SMT.Dom,
      RenamingContext.CoversFV (Function.update Δ' z (some W)) S :=
    fun W => SMT.RenamingContext.coversFV_update_of_notMem z_not_fv_S hcov_S_Δ'
  have hcov_T_upd : ∀ W : SMT.Dom,
      RenamingContext.CoversFV (Function.update Δ' z (some W)) T :=
    fun W => SMT.RenamingContext.coversFV_update_of_notMem z_not_fv_T hcov_T_Δ'

  -- 3. S denotation invariance under z and S! updates
  have den_S_Δ' : ⟦S.abstract Δ' hcov_S_Δ'⟧ˢ = some den_S := by
    have : ⟦S.abstract «Δ» hS⟧ˢ = ⟦S.abstract Δ' hcov_S_Δ'⟧ˢ := by
      rw [←SMT.RenamingContext.denote, ←SMT.RenamingContext.denote]
      exact SMT.RenamingContext.denote_update_of_notMem S!_not_fv_S
    rw [←this]; exact h_den_S

  have den_S_upd : ∀ W : SMT.Dom,
      ⟦S.abstract (Function.update Δ' z (some W)) (hcov_S_upd W)⟧ˢ = some den_S := by
    intro W
    have : ⟦S.abstract Δ' hcov_S_Δ'⟧ˢ =
        ⟦S.abstract (Function.update Δ' z (some W)) (hcov_S_upd W)⟧ˢ := by
      rw [←SMT.RenamingContext.denote, ←SMT.RenamingContext.denote]
      exact SMT.RenamingContext.denote_update_of_notMem z_not_fv_S
    rw [←this]; exact den_S_Δ'

  -- 4. T denotation invariance
  have den_T_Δ' : ⟦T.abstract Δ' hcov_T_Δ'⟧ˢ = some den_T := by
    have : ⟦T.abstract «Δ» hT⟧ˢ = ⟦T.abstract Δ' hcov_T_Δ'⟧ˢ := by
      rw [←SMT.RenamingContext.denote, ←SMT.RenamingContext.denote]
      exact SMT.RenamingContext.denote_update_of_notMem S!_not_fv_T
    rw [←this]; exact h_den_T

  have den_T_upd : ∀ W : SMT.Dom,
      ⟦T.abstract (Function.update Δ' z (some W)) (hcov_T_upd W)⟧ˢ = some den_T := by
    intro W
    have : ⟦T.abstract Δ' hcov_T_Δ'⟧ˢ =
        ⟦T.abstract (Function.update Δ' z (some W)) (hcov_T_upd W)⟧ˢ := by
      rw [←SMT.RenamingContext.denote, ←SMT.RenamingContext.denote]
      exact SMT.RenamingContext.denote_update_of_notMem z_not_fv_T
    rw [←this]; exact den_T_Δ'

  -- 5. For each valid W, compute denotation of .app (.var S!) (.var z) and .app T (.var z)
  --    via funDenoteAppAt
  have hden_S!_var : ∀ W : SMT.Dom,
      ⟦(SMT.Term.var S!).abstract (Function.update Δ' z (some W))
        (by intro v hv; simp only [SMT.fv, List.mem_cons, List.not_mem_nil, or_false] at hv; subst hv;
            simp only [Function.update, z_ne_S!.symm, ↓reduceDIte, Function.update_self,
              Option.isSome_some, Δ'])⟧ˢ = some X! := by
    intro W
    simp only [SMT.Term.abstract, Function.update, z_ne_S!.symm, ↓reduceDIte, Option.get_some,
      SMT.denote, Option.pure_def, Δ']

  -- Body denotation: for each valid W, the or-body denotes and its value is related to
  -- fapply(X!.1, W.1) and fapply(den_T.1, W.1)
  have hbody_den : ∀ (W : SMT.Dom) (hW_ty : W.2.1 = γ) (hW_mem : W.1 ∈ ⟦γ⟧ᶻ),
      ∃ Dbody : SMT.Dom,
        ∃ hcov_or : RenamingContext.CoversFV (Function.update Δ' z (some W)) orBody,
          ⟦orBody.abstract (Function.update Δ' z (some W)) hcov_or⟧ˢ = some Dbody ∧
          Dbody.2.1 = .bool ∧
          (Dbody.1 = zftrue ↔
            (ZFSet.fapply X!.1 (ZFSet.is_func_is_pfunc hX!_func)
              ⟨W.1, by rwa [ZFSet.is_func_dom_eq hX!_func]⟩ = zftrue ∨
            ZFSet.fapply den_T.1 (ZFSet.is_func_is_pfunc hdenT_func)
              ⟨W.1, by rwa [ZFSet.is_func_dom_eq hdenT_func]⟩ = zftrue)) := by
    intro W hW_ty hW_mem
    -- Get app denotation for S!
    obtain ⟨hcov_S!_app_w, DS!, hDS!_ty, hDS!_val, hden_S!_app⟩ :=
      funDenoteAppAt
        (Δctx := Δ') (t := SMT.Term.var S!) (x := z) (α := γ) (β := .bool) (Y := X!)
        (hcov_t_upd := fun Xarg => by
          intro v hv; rw [SMT.fv, List.mem_cons, List.mem_nil_iff, or_false] at hv; subst hv
          simp only [Function.update, z_ne_S!.symm, ↓reduceDIte, Function.update_self,
            Option.isSome_some, Δ'])
        (den_t_upd := hden_S!_var)
        (hY_ty := X!_type)
        (hY_func := hX!_func)
        W hW_ty hW_mem
    -- Get app denotation for T
    obtain ⟨hcov_T_app_w, DT!, hDT!_ty, hDT!_val, hden_T_app⟩ :=
      funDenoteAppAt
        (Δctx := Δ') (t := T) (x := z) (α := γ) (β := .bool) (Y := den_T)
        (hcov_t_upd := hcov_T_upd)
        (den_t_upd := den_T_upd)
        (hY_ty := den_T_type)
        (hY_func := hdenT_func)
        W hW_ty hW_mem
    -- Build or denotation: .or = ¬(¬a ∧ ¬b)
    have hDS!_bool : DS!.2.1 = .bool := hDS!_ty
    have hDT!_bool : DT!.2.1 = .bool := hDT!_ty
    -- DS!.1 and DT!.1 are in 𝔹
    have DS!_mem_𝔹 : DS!.1 ∈ 𝔹 := by have h := DS!.2.2; rwa [hDS!_bool] at h
    have DT!_mem_𝔹 : DT!.1 ∈ 𝔹 := by have h := DT!.2.2; rwa [hDT!_bool] at h
    -- Build CoversFV for or body
    have hcov_or : RenamingContext.CoversFV (Function.update Δ' z (some W)) orBody := by
      intro v hv
      change v ∈ SMT.fv orBody at hv
      rw [horBody_def] at hv
      simp only [SMT.fv, List.mem_append, List.mem_singleton] at hv
      by_cases hvz : v = z
      · subst hvz; simp [Function.update]
      · rw [Function.update_of_ne hvz]
        by_cases hvS! : v = S!
        · subst hvS!; simp [hΔ'_def, Function.update_self]
        · have hv_fv_T : v ∈ SMT.fv T := by
            -- hv : (v = S! ∨ v = z) ∨ v ∈ SMT.fv T ∨ v = z
            rcases hv with ((rfl | rfl) | (hv | rfl))
            · nomatch hvS!
            · nomatch hvz
            · exact hv
            · nomatch hvz
          exact hcov_T_Δ' v hv_fv_T
    -- Case analysis on ZFBool values
    rw [ZFSet.ZFBool.mem_𝔹_iff] at DS!_mem_𝔹 DT!_mem_𝔹
    rcases DS!_mem_𝔹 with hDS!_false | hDS!_true <;>
    rcases DT!_mem_𝔹 with hDT!_false | hDT!_true
    · -- Both false: or is false
      have hDnot_S := denote_not_eq_zftrue_of_some_zffalse hden_S!_app hDS!_bool hDS!_false
      have hDnot_T := denote_not_eq_zftrue_of_some_zffalse hden_T_app hDT!_bool hDT!_false
      have hDand := denote_and_eq_zftrue_of_some_zftrue hDnot_S rfl rfl hDnot_T rfl rfl
      have hDor := denote_not_eq_zffalse_of_some_zftrue hDand rfl rfl
      refine ⟨⟨zffalse, .bool, ZFBool.zffalse_mem_𝔹⟩, hcov_or, ?_, rfl, ?_⟩
      · convert hDor using 1; simp only [horBody_def, SMT.Term.abstract]; rfl
      · constructor
        · intro h; exact (ZFSet.zftrue_ne_zffalse h.symm).elim
        · intro h; rcases h with h | h
          · nomatch ZFSet.zftrue_ne_zffalse (h.symm.trans (hDS!_val.symm.trans hDS!_false))
          · nomatch ZFSet.zftrue_ne_zffalse (h.symm.trans (hDT!_val.symm.trans hDT!_false))
    · -- S false, T true: or is true
      have hDnot_S := denote_not_eq_zftrue_of_some_zffalse hden_S!_app hDS!_bool hDS!_false
      have hDnot_T := denote_not_eq_zffalse_of_some_zftrue hden_T_app hDT!_bool hDT!_true
      have hDand := denote_and_eq_zffalse_of_some_zffalse_right hDnot_S rfl hDnot_T rfl rfl
      have hDor := denote_not_eq_zftrue_of_some_zffalse hDand rfl rfl
      refine ⟨⟨zftrue, .bool, ZFBool.zftrue_mem_𝔹⟩, hcov_or, ?_, rfl, ?_⟩
      · convert hDor using 1; simp only [horBody_def, SMT.Term.abstract]; rfl
      · exact ⟨fun _ => Or.inr (hDT!_val ▸ hDT!_true), fun _ => rfl⟩
    · -- S true, T false: or is true
      have hDnot_S := denote_not_eq_zffalse_of_some_zftrue hden_S!_app hDS!_bool hDS!_true
      have hDnot_T := denote_not_eq_zftrue_of_some_zffalse hden_T_app hDT!_bool hDT!_false
      have hDand := denote_and_eq_zffalse_of_some_zffalse_left hDnot_S rfl rfl hDnot_T rfl
      have hDor := denote_not_eq_zftrue_of_some_zffalse hDand rfl rfl
      refine ⟨⟨zftrue, .bool, ZFBool.zftrue_mem_𝔹⟩, hcov_or, ?_, rfl, ?_⟩
      · convert hDor using 1; simp only [horBody_def, SMT.Term.abstract]; rfl
      · exact ⟨fun _ => Or.inl (hDS!_val ▸ hDS!_true), fun _ => rfl⟩
    · -- Both true: or is true
      have hDnot_S := denote_not_eq_zffalse_of_some_zftrue hden_S!_app hDS!_bool hDS!_true
      have hDnot_T := denote_not_eq_zffalse_of_some_zftrue hden_T_app hDT!_bool hDT!_true
      have hDand := denote_and_eq_zffalse_of_some_zffalse_left hDnot_S rfl rfl hDnot_T rfl
      have hDor := denote_not_eq_zftrue_of_some_zffalse hDand rfl rfl
      refine ⟨⟨zftrue, .bool, ZFBool.zftrue_mem_𝔹⟩, hcov_or, ?_, rfl, ?_⟩
      · convert hDor using 1; simp only [horBody_def, SMT.Term.abstract]; rfl
      · exact ⟨fun _ => Or.inl (hDS!_val ▸ hDS!_true), fun _ => rfl⟩

  -- 6. Lambda assembly + retract equality
  -- 6a. CoversFV for orBody under z-updates of Δ'
  have hcov_orBody_upd :
      ∀ W : SMT.Dom,
        RenamingContext.CoversFV (Function.update Δ' z (some W)) orBody := by
    intro W v hv
    change v ∈ SMT.fv orBody at hv
    rw [horBody_def] at hv
    simp only [SMT.fv, List.mem_append, List.mem_singleton] at hv
    by_cases hvz : v = z
    · subst hvz; simp [Function.update]
    · rw [Function.update_of_ne hvz]
      by_cases hvS! : v = S!
      · subst hvS!; simp [hΔ'_def, Function.update_self]
      · have hv_fv_T : v ∈ SMT.fv T := by
          rcases hv with ((rfl | rfl) | (hv | rfl))
          · exact absurd rfl hvS!
          · exact absurd rfl hvz
          · exact hv
          · exact absurd rfl hvz
        exact hcov_T_Δ' v hv_fv_T
  -- 6b. go_cov for the lambda binder
  have hgo_cov : ∀ v ∈ SMT.fv orBody, v ∉ [z] → (Δ' v).isSome = true := by
    intro v hv hvz
    have hvz' : v ≠ z := by simpa [List.mem_singleton] using hvz
    have := hcov_orBody_upd ⟨γ.defaultZFSet, γ, SMTType.mem_toZFSet_of_defaultZFSet⟩ v hv
    rwa [Function.update_of_ne hvz'] at this
  -- 6c. Body denotes for all valid W
  have hbody_total : ∀ W : SMT.Dom, W.snd.fst = γ →
      ⟦orBody.abstract (Function.update Δ' z (some W)) (hcov_orBody_upd W)⟧ˢ.isSome = true := by
    intro W hW_ty
    have hW_mem : W.fst ∈ ⟦γ⟧ᶻ := by rw [← hW_ty]; exact W.snd.snd
    obtain ⟨Dbody, hcov_or, hden_body, _⟩ := hbody_den W hW_ty hW_mem
    rw [show hcov_orBody_upd W = hcov_or from Subsingleton.elim _ _]
    exact Option.isSome_of_eq_some hden_body
  -- 6d. Body type is always .bool
  have hbody_ty : ∀ (W : SMT.Dom), W.snd.fst = γ → ∀ D,
      ⟦orBody.abstract (Function.update Δ' z (some W)) (hcov_orBody_upd W)⟧ˢ = some D →
      D.snd.fst = .bool := by
    intro W hW_ty D hden
    have hW_mem : W.fst ∈ ⟦γ⟧ᶻ := by rw [← hW_ty]; exact W.snd.snd
    obtain ⟨Dbody, hcov_or, hden_body, hDbody_ty, _⟩ := hbody_den W hW_ty hW_mem
    rw [show hcov_orBody_upd W = hcov_or from Subsingleton.elim _ _] at hden
    cases hden.symm.trans hden_body
    exact hDbody_ty
  -- 6e. Lambda isSome
  have hsome_lambda : ⟦((λˢ [z]) [γ] orBody).abstract Δ' hcov⟧ˢ.isSome = true := by
    rw [SMT.Term.abstract, dif_pos (by rfl), SMT.denote]
    have hlen : [z].length > 0 := by simp
    rw [dif_pos hlen]
    split_ifs with den_t_isSome den_t_typ_det
    · simp
    · exfalso; apply den_t_typ_det
      intro x y hx hy
      let Wx : SMT.Dom := x ⟨0, by simp⟩
      let Wy : SMT.Dom := y ⟨0, by simp⟩
      have hWx_ty : Wx.snd.fst = γ := by simpa [Wx] using (hx ⟨0, by simp⟩).1
      have hWy_ty : Wy.snd.fst = γ := by simpa [Wy] using (hy ⟨0, by simp⟩).1
      have hgo_x := funAbstractGoSingle (Δctx := Δ') (P := orBody) (v := z) (τ := γ)
        hgo_cov hcov_orBody_upd x hx
      have hgo_y := funAbstractGoSingle (Δctx := Δ') (P := orBody) (v := z) (τ := γ)
        hgo_cov hcov_orBody_upd y hy
      obtain ⟨Dx, hDx⟩ := Option.isSome_iff_exists.mp (hbody_total Wx hWx_ty)
      obtain ⟨Dy, hDy⟩ := Option.isSome_iff_exists.mp (hbody_total Wy hWy_ty)
      have hden_x : ⟦(SMT.Term.abstract.go orBody [z] Δ' hgo_cov).uncurry x⟧ˢ = some Dx := by
        rw [hgo_x]; exact hDx
      have hden_y : ⟦(SMT.Term.abstract.go orBody [z] Δ' hgo_cov).uncurry y⟧ˢ = some Dy := by
        rw [hgo_y]; exact hDy
      calc (⟦(SMT.Term.abstract.go orBody [z] Δ' hgo_cov).uncurry x⟧ˢ.get
              (den_t_isSome hx)).snd.fst
          = Dx.snd.fst := congrArg (·.snd.fst) (Option.get_of_eq_some (den_t_isSome hx) hden_x)
        _ = SMTType.bool := hbody_ty Wx hWx_ty Dx hDx
        _ = Dy.snd.fst := (hbody_ty Wy hWy_ty Dy hDy).symm
        _ = (⟦(SMT.Term.abstract.go orBody [z] Δ' hgo_cov).uncurry y⟧ˢ.get
              (den_t_isSome hy)).snd.fst :=
            (congrArg (·.snd.fst) (Option.get_of_eq_some (den_t_isSome hy) hden_y)).symm
    · exfalso; apply den_t_isSome
      intro x hx
      let Wx : SMT.Dom := x ⟨0, by simp⟩
      have hWx_ty : Wx.snd.fst = γ := by simpa [Wx] using (hx ⟨0, by simp⟩).1
      rw [funAbstractGoSingle (Δctx := Δ') (P := orBody) (v := z) (τ := γ)
        hgo_cov hcov_orBody_upd x hx]
      exact hbody_total Wx hWx_ty
  -- 6f. Build the body function and show the lambda denotes
  -- Define the body value function
  classical
  set bodyFun : ZFSet → ZFSet := fun x₁ =>
    if hx : x₁.hasArity 1 ∧ x₁ ∈ ⟦γ⟧ᶻ then
      let W : SMT.Dom := ⟨x₁, γ, hx.2⟩
      if hsome : ⟦orBody.abstract (Function.update Δ' z (some W))
          (hcov_orBody_upd W)⟧ˢ.isSome then
        (⟦orBody.abstract (Function.update Δ' z (some W))
            (hcov_orBody_upd W)⟧ˢ.get hsome).fst
      else SMTType.bool.defaultZFSet
    else SMTType.bool.defaultZFSet with hbodyFun_def
  -- bodyFun maps ⟦γ⟧ᶻ into 𝔹
  have hbodyFun_range : ∀ {x₁ : ZFSet}, x₁ ∈ ⟦γ⟧ᶻ → bodyFun x₁ ∈ 𝔹 := by
    intro x₁ hx₁
    simp only [bodyFun]
    have hx_cast : x₁.hasArity 1 ∧ x₁ ∈ ⟦γ⟧ᶻ := ⟨(funUnaryTarget hx₁).1, hx₁⟩
    rw [dif_pos hx_cast]
    let W : SMT.Dom := ⟨x₁, γ, hx₁⟩
    have hsome := hbody_total W rfl
    rw [dif_pos hsome]
    have hW_mem : W.fst ∈ ⟦γ⟧ᶻ := hx₁
    obtain ⟨Dbody, hcov_or, hden_body, hDbody_ty, _⟩ := hbody_den W rfl hW_mem
    rw [show hcov_orBody_upd W = hcov_or from Subsingleton.elim _ _] at hsome ⊢
    have hget_eq := Option.get_of_eq_some hsome hden_body
    rw [congrArg (·.fst) hget_eq]
    have : Dbody.fst ∈ ⟦Dbody.snd.fst⟧ᶻ := Dbody.snd.snd
    rwa [hDbody_ty] at this
  -- bodyFun at w ∈ ⟦γ⟧ᶻ equals Dbody.fst from hbody_den
  have hbodyFun_eq : ∀ (w : ZFSet) (hw : w ∈ ⟦γ⟧ᶻ),
      ∃ Dbody : SMT.Dom,
        ⟦orBody.abstract (Function.update Δ' z (some ⟨w, γ, hw⟩))
          (hcov_orBody_upd ⟨w, γ, hw⟩)⟧ˢ = some Dbody ∧
        bodyFun w = Dbody.fst := by
    intro w hw
    let W : SMT.Dom := ⟨w, γ, hw⟩
    obtain ⟨Dbody, hcov_or, hden_body, _⟩ := hbody_den W rfl hw
    refine ⟨Dbody, ?_, ?_⟩
    · rw [show hcov_orBody_upd W = hcov_or from Subsingleton.elim _ _]; exact hden_body
    · simp only [bodyFun]
      have hx_cast : w.hasArity 1 ∧ w ∈ ⟦γ⟧ᶻ := ⟨(funUnaryTarget hw).1, hw⟩
      rw [dif_pos hx_cast]
      have hsome := hbody_total W rfl
      rw [dif_pos hsome]
      rw [show hcov_orBody_upd W = hcov_or from Subsingleton.elim _ _] at hsome ⊢
      exact congrArg (·.fst) (Option.get_of_eq_some hsome hden_body)
  -- Build the lambda ZFSet
  set lamFun := ZFSet.lambda ⟦γ⟧ᶻ 𝔹 bodyFun with hlamFun_def
  have hlamFun_func : ZFSet.IsFunc ⟦γ⟧ᶻ 𝔹 lamFun :=
    ZFSet.lambda_isFunc (fun {z} hz => hbodyFun_range hz)
  have hlamFun_mem : lamFun ∈ ⟦γ.fun SMTType.bool⟧ᶻ := by
    simp [SMTType.toZFSet]; exact hlamFun_func
  -- fapply lamFun at w = bodyFun w
  have hlamFun_fapply : ∀ (w : ZFSet) (hw : w ∈ ⟦γ⟧ᶻ),
      ZFSet.fapply lamFun (ZFSet.is_func_is_pfunc hlamFun_func)
        ⟨w, by rw [ZFSet.is_func_dom_eq hlamFun_func]; exact hw⟩ = bodyFun w := by
    intro w hw; exact ZFSet.fapply_lambda (hf := fun {z} hz => hbodyFun_range hz) (ha := hw)
  obtain ⟨lamVal, hlamVal⟩ := Option.isSome_iff_exists.mp hsome_lambda
  have hlamVal_saved := hlamVal

  have hlamVal_ty : lamVal.snd.fst = .fun γ .bool := by
    have hlamVal' := hlamVal
    rw [SMT.Term.abstract, dif_pos (by rfl)] at hlamVal'
    simp only [SMT.denote] at hlamVal'
    rw [dif_pos (show [z].length > 0 by exact Nat.zero_lt_succ 0)] at hlamVal'
    split_ifs at hlamVal' with h_isSome h_typ_det
    · -- Compute γ_out via default argument
      let xd : Fin 1 → SMT.Dom := fun _ => ⟨γ.defaultZFSet, γ, SMTType.mem_toZFSet_of_defaultZFSet⟩
      have hxd_spec : ∀ i, (xd i).2.1 = [γ][↑i] ∧ (xd i).1 ∈ ⟦[γ][↑i]⟧ᶻ := by
        intro ⟨i, hi⟩; simp at hi; subst hi; exact ⟨rfl, SMTType.mem_toZFSet_of_defaultZFSet⟩
      have hgo_d := funAbstractGoSingle (Δctx := Δ') (P := orBody) (v := z) (τ := γ)
        hgo_cov hcov_orBody_upd xd hxd_spec
      obtain ⟨Dd, hDd⟩ := Option.isSome_iff_exists.mp (hbody_total (xd ⟨0, by simp⟩) rfl)
      have hden_d : ⟦(SMT.Term.abstract.go orBody [z] Δ' hgo_cov).uncurry xd⟧ˢ = some Dd := by
        rw [hgo_d]; exact hDd
      have hγ_out : (⟦(SMT.Term.abstract.go orBody [z] Δ' hgo_cov).uncurry xd⟧ˢ.get
          (h_isSome hxd_spec)).snd.fst = .bool := by
        rw [congrArg (·.snd.fst) (Option.get_of_eq_some _ hden_d)]
        exact hbody_ty (xd ⟨0, Nat.one_pos⟩) rfl Dd hDd
      simp only [Option.pure_def, Option.some.injEq] at hlamVal'
      rw [show lamVal.snd.fst = _ from congrArg (·.snd.fst) hlamVal'.symm]
      simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.sub_self,
        Fin.foldr_zero, List.getElem_cons_zero]
      exact congrArg (γ.fun ·) hγ_out

  -- Step 2: lamVal is a function from ⟦γ⟧ᶻ to 𝔹
  have hlamVal_func : ZFSet.IsFunc ⟦γ⟧ᶻ 𝔹 lamVal.fst := by
    have : lamVal.fst ∈ ⟦γ⟧ᶻ.funs 𝔹 := by
      simpa [hlamVal_ty, SMTType.toZFSet] using lamVal.snd.snd
    exact ZFSet.mem_funs.mp this

  -- Step 3: fapply lamVal.fst at w equals bodyFun w (and hence Dbody.fst)
  have hlamVal_app : ∀ (w : ZFSet) (hw : w ∈ ⟦γ⟧ᶻ),
      ∃ Dbody : SMT.Dom,
        ⟦orBody.abstract (Function.update Δ' z (some ⟨w, γ, hw⟩))
          (hcov_orBody_upd ⟨w, γ, hw⟩)⟧ˢ = some Dbody ∧
        ZFSet.fapply lamVal.fst (ZFSet.is_func_is_pfunc hlamVal_func)
          ⟨w, by rw [ZFSet.is_func_dom_eq hlamVal_func]; exact hw⟩ = Dbody.fst := by
    intro w hw
    obtain ⟨Dbody, hden_body, hbf_eq⟩ := hbodyFun_eq w hw
    refine ⟨Dbody, hden_body, ?_⟩

    have hlamVal' := hlamVal_saved
    rw [SMT.Term.abstract, dif_pos (by rfl)] at hlamVal'
    simp only [SMT.denote] at hlamVal'
    rw [dif_pos (show [z].length > 0 by exact Nat.zero_lt_succ 0)] at hlamVal'
    split_ifs at hlamVal' with h_isSome h_typ_det
    · -- Compute γ_out = .bool (same as in hlamVal_ty)
      let xd : Fin 1 → SMT.Dom := fun _ => ⟨γ.defaultZFSet, γ, SMTType.mem_toZFSet_of_defaultZFSet⟩
      have hxd_spec : ∀ i, (xd i).2.1 = [γ][↑i] ∧ (xd i).1 ∈ ⟦[γ][↑i]⟧ᶻ := by
        intro ⟨i, hi⟩; simp at hi; subst hi; exact ⟨rfl, SMTType.mem_toZFSet_of_defaultZFSet⟩
      have hgo_d := funAbstractGoSingle (Δctx := Δ') (P := orBody) (v := z) (τ := γ)
        hgo_cov hcov_orBody_upd xd hxd_spec
      obtain ⟨Dd, hDd⟩ := Option.isSome_iff_exists.mp (hbody_total (xd ⟨0, by simp⟩) rfl)
      have hden_d : ⟦(SMT.Term.abstract.go orBody [z] Δ' hgo_cov).uncurry xd⟧ˢ = some Dd := by
        rw [hgo_d]; exact hDd
      have hγ_out : (⟦(SMT.Term.abstract.go orBody [z] Δ' hgo_cov).uncurry xd⟧ˢ.get
          (h_isSome hxd_spec)).snd.fst = .bool := by
        rw [congrArg (·.snd.fst) (Option.get_of_eq_some _ hden_d)]
        exact hbody_ty (xd ⟨0, Nat.one_pos⟩) rfl Dd hDd
      simp only [Option.pure_def, Option.some.injEq] at hlamVal'
      have hlamVal_fst : lamVal.fst = _ := congrArg (·.fst) hlamVal'.symm
      simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.sub_self,
        Fin.foldr_zero, List.getElem_cons_zero] at hlamVal_fst
      have hlamVal_eq_lamFun : lamVal.fst = lamFun :=
        (ZFSet.is_func_ext_iff hlamVal_func hlamFun_func).mpr fun w' hw' => by
          apply Subtype.ext
          rw [hlamFun_fapply w' hw']
          obtain ⟨Dbody', hden_body', hbf_eq'⟩ := hbodyFun_eq w' hw'
          rw [hbf_eq']
          have h_pair_mem_lamFun : w'.pair (bodyFun w') ∈ lamFun := by
            rw [hlamFun_def, ZFSet.mem_lambda]
            exact ⟨w', bodyFun w', rfl, hw', hbodyFun_range hw', rfl⟩
          -- Step 2: Since lamVal.fst and lamFun are both IsFunc ⟦γ⟧ᶻ 𝔹 and contain w' in domain,
          -- and they map w' to the same value (since both produce ZFSet.lambda from the same body),
          have hval_eq : lamVal.fst = _ := congrArg (·.fst) hlamVal'.symm
          have h_pair_mem : w'.pair Dbody'.fst ∈ lamVal.fst := by
            rw [hval_eq]
            simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.sub_self,
              Fin.foldr_zero, List.getElem_cons_zero]
            rw [ZFSet.mem_lambda]
            refine ⟨w', Dbody'.fst, rfl, hw', ?_, ?_⟩
            · -- Dbody'.fst ∈ ⟦γ_out⟧ᶻ
              have hD_ty := hbody_ty ⟨w', γ, hw'⟩ rfl Dbody' hden_body'
              have : Dbody'.fst ∈ ⟦Dbody'.snd.fst⟧ᶻ := Dbody'.snd.snd
              rw [hD_ty] at this
              convert this using 2
            · -- Dbody'.fst = T_internal(w')
              split_ifs with hw'_cond
              · -- Connect go.uncurry to orBody.abstract via funAbstractGoSingle
                let xₙ := fun i : Fin 1 => (⟨w'.get 1 i, [γ][↑i], hw'_cond.2 i⟩ : SMT.Dom)
                have hgo' := funAbstractGoSingle (Δctx := Δ') (P := orBody) (v := z) (τ := γ)
                  hgo_cov hcov_orBody_upd xₙ (fun i => ⟨rfl, hw'_cond.2 i⟩)
                have hxₙ_eq : xₙ ⟨0, Nat.zero_lt_one⟩ = ⟨w', γ, hw'⟩ := rfl
                have hden' : ⟦(SMT.Term.abstract.go orBody [z] Δ' hgo_cov).uncurry xₙ⟧ˢ = some Dbody' := by
                  rw [hgo', hxₙ_eq]; exact hden_body'
                exact (congrArg (·.fst) (Option.get_of_eq_some _ hden')).symm
              · exfalso; apply hw'_cond
                exact ⟨trivial, fun ⟨i, hi⟩ => by
                  have : i = 0 := Nat.lt_one_iff.mp hi; subst this
                  exact hw'⟩
          -- Use fapply.of_pair on lamVal.fst to conclude
          have h_fapply := ZFSet.fapply.of_pair (ZFSet.is_func_is_pfunc hlamVal_func) h_pair_mem
          rw [Subtype.ext_iff] at h_fapply
          exact h_fapply
      have := (ZFSet.is_func_ext_iff hlamVal_func hlamFun_func).mp hlamVal_eq_lamFun w hw
      rw [this, hlamFun_fapply w hw]
      exact hbf_eq

  -- Main conclusion: provide lamVal as witness
  refine ⟨lamVal, ?_, hlamVal_ty, ?_⟩
  · -- Denotation: use proof irrelevance on CoversFV
    convert hlamVal using 2
  · -- Retract equality
    intro α hα
    subst hα
    ext x
    simp only [ZFSet.mem_union]
    have retract_mem_α : ∀ {F : ZFSet}, x ∈ retract α.set F → x ∈ ⟦α⟧ᶻ := by
      intro F hx
      rw [retract, ZFSet.mem_sep] at hx
      exact hx.1
    let mk_cx (hx_α : x ∈ ⟦α⟧ᶻ) : ZFSet := ZFSet.fapply (BType.canonicalIsoSMTType α).1
      (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType α).2.1)
      ⟨x, by rwa [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType α).2.1]⟩
    have mk_cx_mem (hx_α : x ∈ ⟦α⟧ᶻ) : mk_cx hx_α ∈ ⟦α.toSMTType⟧ᶻ :=
      ZFSet.fapply_mem_range _ _
    have fapply_iff (hx_α : x ∈ ⟦α⟧ᶻ)
        {F : ZFSet} (hF_func : ZFSet.IsFunc ⟦α.toSMTType⟧ᶻ 𝔹 F) :
        x ∈ retract α.set F ↔
        ZFSet.fapply F (ZFSet.is_func_is_pfunc hF_func)
          ⟨mk_cx hx_α, by rw [ZFSet.is_func_dom_eq hF_func]; exact mk_cx_mem hx_α⟩ = zftrue :=
      mem_retract_set_iff_app_canonical_eq_zftrue' hF_func rfl hx_α
    constructor
    · -- (→) x ∈ retract α.set lamVal.fst → x ∈ ... ∪ ...
      intro hx_mem
      have hx_α := retract_mem_α hx_mem
      rw [fapply_iff hx_α hlamVal_func] at hx_mem
      have hcx_mem := mk_cx_mem hx_α
      obtain ⟨Dbody, hden_body, hfapply_eq⟩ := hlamVal_app (mk_cx hx_α) hcx_mem
      obtain ⟨Dbody', hcov_or, hden_body', _, hDbody'_iff⟩ :=
        hbody_den ⟨mk_cx hx_α, α.toSMTType, hcx_mem⟩ rfl hcx_mem
      have hDbody_eq : Dbody = Dbody' := by
        rw [show hcov_orBody_upd ⟨mk_cx hx_α, α.toSMTType, hcx_mem⟩ = hcov_or from
          Subsingleton.elim _ _] at hden_body
        exact Option.some_injective _ (hden_body.symm.trans hden_body')
      rw [hfapply_eq, hDbody_eq] at hx_mem
      rcases hDbody'_iff.mp hx_mem with hS_true | hT_true
      · left; rw [fapply_iff hx_α hdenS_func]
        rw [(ZFSet.is_func_ext_iff hX!_func hdenS_func).mp X!_val_eq (mk_cx hx_α) hcx_mem] at hS_true
        exact hS_true
      · right; rw [fapply_iff hx_α hdenT_func]; exact hT_true
    · -- (←) x ∈ ... ∪ ... → x ∈ retract α.set lamVal.fst
      intro hx_mem
      rcases hx_mem with hx_S | hx_T
      · have hx_α := retract_mem_α hx_S
        rw [fapply_iff hx_α hdenS_func] at hx_S
        have hcx_mem := mk_cx_mem hx_α
        obtain ⟨Dbody, hden_body, hfapply_eq⟩ := hlamVal_app (mk_cx hx_α) hcx_mem
        obtain ⟨Dbody', hcov_or, hden_body', _, hDbody'_iff⟩ :=
          hbody_den ⟨mk_cx hx_α, α.toSMTType, hcx_mem⟩ rfl hcx_mem
        have hDbody_eq : Dbody = Dbody' := by
          rw [show hcov_orBody_upd ⟨mk_cx hx_α, α.toSMTType, hcx_mem⟩ = hcov_or from
            Subsingleton.elim _ _] at hden_body
          exact Option.some_injective _ (hden_body.symm.trans hden_body')
        rw [fapply_iff hx_α hlamVal_func, hfapply_eq, hDbody_eq]
        have hx_S' : ↑(ZFSet.fapply X!.fst (ZFSet.is_func_is_pfunc hX!_func)
            ⟨mk_cx hx_α, by rw [ZFSet.is_func_dom_eq hX!_func]; exact hcx_mem⟩) = zftrue := by
          rw [(ZFSet.is_func_ext_iff hX!_func hdenS_func).mp X!_val_eq (mk_cx hx_α) hcx_mem]
          exact hx_S
        exact hDbody'_iff.mpr (Or.inl hx_S')
      · have hx_α := retract_mem_α hx_T
        rw [fapply_iff hx_α hdenT_func] at hx_T
        have hcx_mem := mk_cx_mem hx_α
        obtain ⟨Dbody, hden_body, hfapply_eq⟩ := hlamVal_app (mk_cx hx_α) hcx_mem
        obtain ⟨Dbody', hcov_or, hden_body', _, hDbody'_iff⟩ :=
          hbody_den ⟨mk_cx hx_α, α.toSMTType, hcx_mem⟩ rfl hcx_mem
        have hDbody_eq : Dbody = Dbody' := by
          rw [show hcov_orBody_upd ⟨mk_cx hx_α, α.toSMTType, hcx_mem⟩ = hcov_or from
            Subsingleton.elim _ _] at hden_body
          exact Option.some_injective _ (hden_body.symm.trans hden_body')
        rw [fapply_iff hx_α hlamVal_func, hfapply_eq, hDbody_eq]
        exact hDbody'_iff.mpr (Or.inr hx_T)

set_option maxHeartbeats 800000 in
@[spec]
theorem castUnion_spec
  {Λ : SMT.TypeContext} {n : ℕ} {used : List SMT.𝒱}
  {S T : SMT.Term} {γ : SMTType}
  (typ_S : Λ ⊢ˢ S : .fun γ .bool) (typ_T : Λ ⊢ˢ T : .fun γ .bool)
  {«Δ» : SMT.RenamingContext.Context}
  (hS : RenamingContext.CoversFV «Δ» S)
  (hT : RenamingContext.CoversFV «Δ» T)
  (Δ_none_out : ∀ v ∉ used, «Δ» v = none) :
  ⦃ fun ⟨E, Λ'⟩ => ⌜ Λ' = Λ ∧ E.freshvarsc = n ∧ AList.keys Λ ⊆ E.usedVars ∧ E.usedVars = used ⌝ ⦄
  castUnion ⟨S, .fun γ .bool⟩ ⟨T, .fun γ .bool⟩
  ⦃ ⇓? ⟨t, τ⟩ ⟨E', Γ'⟩ =>
     ⌜ used ⊆ E'.usedVars ∧
       Λ ⊆ Γ' ∧
       AList.keys Γ' ⊆ E'.usedVars ∧
       τ = .fun γ .bool ∧
       Γ' ⊢ˢ t : .fun γ .bool ∧
       (∀ v ∈ used, v ∉ Λ → v ∉ Γ') ∧
       (∀ (den_S den_T : SMT.Dom),
         ⟦S.abstract «Δ» hS⟧ˢ = some den_S →
         ⟦T.abstract «Δ» hT⟧ˢ = some den_T →
         ∃ (Δ' : SMT.RenamingContext.Context) (Δ'_covers : RenamingContext.CoversFV Δ' t),
           RenamingContext.Extends Δ' «Δ» ∧
           (∀ v ∉ E'.usedVars, Δ' v = none) ∧
           ∃ den_t,
             ⟦t.abstract Δ' Δ'_covers⟧ˢ = some den_t ∧
             den_t.2.1 = .fun γ .bool ∧
             (∀ (α : BType), γ = α.toSMTType →
               retract α.set den_t.1 = retract α.set den_S.1 ∪ retract α.set den_T.1)) ⌝ ⦄ := by
  -- Step 1: Reduce castUnion via the direct α = β path
  have hcastUnion :
      castUnion (S, .fun γ .bool) (T, .fun γ .bool) = do
        let x ← freshVar γ "union!"
        return (.lambda [x] [γ] (.or (.app S (.var x)) (.app T (.var x))), .fun γ .bool) := by
    unfold castUnion
    simp
  rw [hcastUnion]
  mintro pre ∀St₀
  mpure pre
  obtain ⟨rfl, rfl, St₀_sub, rfl⟩ := pre

  -- Step 2: freshVar γ
  mspec freshVar_spec
  next z =>
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨St₁_types_eq, z_fresh, St₁_fvc, St₁_used_eq, z_not_used⟩ := pre

    -- Step 3: pure return
    mspec Std.Do.Spec.pure
    mpure_intro
    and_intros
    -- (1) used ⊆ E'.usedVars
    · rw [St₁_used_eq]; exact List.subset_cons_of_subset z fun _ => id
    -- (2) Λ ⊆ Γ'
    · rw [St₁_types_eq]
      exact TypeContext.entries_subset_insert_of_notMem z_fresh
    -- (3) keys Γ' ⊆ E'.usedVars
    · intro v hv
      rw [St₁_types_eq, AList.keys_insert, List.mem_cons] at hv
      rw [St₁_used_eq]
      rcases hv with rfl | hv
      · exact List.mem_cons_self
      · rw [List.erase_of_not_mem z_fresh] at hv
        exact List.mem_cons_of_mem z (St₀_sub hv)
    -- (4) τ = .fun γ .bool
    · trivial
    -- (5) typing
    · rw [St₁_types_eq]
      have z_not_bv_S : z ∉ SMT.bv S := by
        have typ_S_ins : St₀.types.insert z γ ⊢ˢ S : .fun γ .bool :=
          Typing.weakening (TypeContext.entries_subset_insert_of_notMem z_fresh) typ_S
        intro hbv
        exact Typing.bv_notMem_context typ_S_ins z hbv
          (by rw [AList.mem_insert]; exact Or.inl rfl)
      have z_not_bv_T : z ∉ SMT.bv T := by
        have typ_T_ins : St₀.types.insert z γ ⊢ˢ T : .fun γ .bool :=
          Typing.weakening (TypeContext.entries_subset_insert_of_notMem z_fresh) typ_T
        intro hbv
        exact Typing.bv_notMem_context typ_T_ins z hbv
          (by rw [AList.mem_insert]; exact Or.inl rfl)
      apply Typing.weakening (TypeContext.entries_subset_insert_of_notMem z_fresh)
      refine Typing.lambda St₀.types [z] [γ] _ .bool ?_ ?_ ?_ ?_ ?_
      · intro v hv; rw [List.mem_singleton] at hv; subst hv; exact z_fresh
      · intro v hv; rw [List.mem_singleton] at hv; subst hv
        simp only [SMT.bv, List.append_nil, List.mem_append]
        push_neg; exact ⟨z_not_bv_S, z_not_bv_T⟩
      · exact Nat.zero_lt_succ 0
      · rfl
      · have hupdate : TypeContext.update St₀.types [z] [γ] rfl = St₀.types.insert z γ := by
          simp only [TypeContext.update, List.length_cons, List.length_nil, zero_add,
            Nat.reduceAdd, Fin.cast_eq_self, Fin.getElem_fin, Fin.val_eq_zero,
            List.getElem_cons_zero, Fin.foldl_succ, Fin.foldl_zero]
        rw [hupdate]
        apply SMT.Typing.or
        · apply SMT.Typing.app
          · exact Typing.weakening (TypeContext.entries_subset_insert_of_notMem z_fresh) typ_S
          · exact SMT.Typing.var _ z γ (AList.lookup_insert St₀.types)
        · apply SMT.Typing.app
          · exact Typing.weakening (TypeContext.entries_subset_insert_of_notMem z_fresh) typ_T
          · exact SMT.Typing.var _ z γ (AList.lookup_insert St₀.types)
    -- (6) preserves_types: ∀ v ∈ used, v ∉ Λ → v ∉ Γ'
    · intro v hv hv_not_Λ
      rw [St₁_types_eq, AList.mem_insert]; push_neg
      exact ⟨fun h => absurd (h ▸ hv) z_not_used, hv_not_Λ⟩
    -- (7) renaming context + denotation
    · intro den_S den_T h_den_S h_den_T
      -- In the direct path, Δ' = Δ (no new free variables from castUnion)
      refine ⟨«Δ», ?_, ?_, ?_, ?_⟩
      · -- CoversFV Δ t
        intro v hv
        -- fv (.lambda [z] [γ] (.or (.app S (.var z)) (.app T (.var z))))
        --   = ((fv S ++ [z]) ++ (fv T ++ [z])).removeAll [z]
        -- So v ∈ fv S ∨ v ∈ fv T (since z occurrences are removed)
        simp only [SMT.fv, List.removeAll, List.mem_filter, List.mem_append,
          List.mem_cons, List.not_mem_nil, or_false] at hv
        obtain ⟨hv_body, hv_ne_z⟩ := hv
        simp only [List.elem_eq_contains, List.contains_eq_mem, List.mem_cons,
          List.not_mem_nil, or_false, Bool.not_eq_true', decide_eq_false_iff_not] at hv_ne_z
        rcases hv_body with ((hv_S | rfl) | (hv_T | rfl))
        · exact hS v hv_S
        · exact absurd rfl hv_ne_z
        · exact hT v hv_T
        · exact absurd rfl hv_ne_z
      · -- Extends Δ Δ
        exact RenamingContext.extends_refl _
      · -- ∀ v ∉ E'.usedVars, Δ v = none
        intro v hv
        apply Δ_none_out
        intro hv_used
        exact hv (by rw [St₁_used_eq]; exact List.mem_cons_of_mem z hv_used)
      · -- Wt + Denotation + RDom (direct path)
        have z_not_fv_S : z ∉ SMT.fv S := funNotMemFvOfNotMemContext typ_S z_fresh
        have z_not_fv_T : z ∉ SMT.fv T := funNotMemFvOfNotMemContext typ_T z_fresh
        have hcov_lambda : RenamingContext.CoversFV «Δ»
            (.lambda [z] [γ] (.or (.app S (.var z)) (.app T (.var z)))) := by
          intro v hv
          simp only [SMT.fv, List.removeAll, List.mem_filter, List.mem_append,
            List.mem_cons, List.not_mem_nil, or_false] at hv
          obtain ⟨hv_body, hv_ne_z⟩ := hv
          simp only [List.elem_eq_contains, List.contains_eq_mem, List.mem_cons,
            List.not_mem_nil, or_false, Bool.not_eq_true', decide_eq_false_iff_not] at hv_ne_z
          rcases hv_body with ((hv_S | rfl) | (hv_T | rfl))
          · exact hS v hv_S
          · exact absurd rfl hv_ne_z
          · exact hT v hv_T
          · exact absurd rfl hv_ne_z
        have den_S_type : den_S.2.1 = .fun γ .bool :=
          denote_type_eq_of_typing typ_S (hden := h_den_S)
        have den_T_type : den_T.2.1 = .fun γ .bool :=
          denote_type_eq_of_typing typ_T (hden := h_den_T)
        exact castUnion_denotation_direct hS hT h_den_S h_den_T
          den_S_type den_T_type z_not_fv_S z_not_fv_T hcov_lambda

set_option maxHeartbeats 500000 in
theorem encodeTerm_spec.union_case.{u} (fv_sub_typings : B.FvSubTypings) (A B : B.Term)
  (A_ih :
    ∀ (E : _root_.B.Env) {Λ : SMT.TypeContext} {α : BType},
      E.context ⊢ᴮ A : α →
        ∀ {«Δ» : _root_.B.RenamingContext.Context} (Δ_fv : ∀ v ∈ _root_.B.fv A, («Δ» v).isSome = true)
          {Δ₀ : SMT.RenamingContext.Context},
          RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» A →
            ∀ {used : List SMT.𝒱},
              (∀ v ∉ used, Δ₀ v = none) →
                ∀ {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ},
                  ⟦A.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩ →
                    (∀ v ∈ A.vars, v ∈ used) →
                      (∀ v ∈ A.vars, v ∈ Λ → v ∈ E.context) →
                        ∀ {n : ℕ},
                          ⦃fun x =>
                            match x with
                            | { env := E0, types := Λ' } =>
                              ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
                            encodeTerm A E ⦃PostCond.mayThrow fun x x_1 =>
                              match x with
                              | (t', σ) =>
                                match x_1 with
                                | { env := E', types := Γ' } =>
                                  ⌜used ⊆ E'.usedVars ∧
                                      Λ ⊆ Γ' ∧
                                        AList.keys Γ' ⊆ E'.usedVars ∧
                                          CoversUsedVars E'.usedVars A ∧
                                            σ = α.toSMTType ∧
                                              Γ' ⊢ˢ t' : σ ∧
                                                (∀ v ∈ used, v ∉ Λ → v ∉ _root_.B.fv A → v ∉ Γ') ∧
                                                  ∃ Δ',
                                                    ∃ (Δ'_covers : RenamingContext.CoversFV Δ' t'),
                                                      RenamingContext.Extends Δ' Δ₀ ∧
                                                        RenamingContext.ExtendsOnSourceFV Δ' «Δ» A ∧
                                                          (∀ v ∉ E'.usedVars, Δ' v = none) ∧
                                                            ∃ denT',
                                                              ⟦t'.abstract Δ' Δ'_covers⟧ˢ = some denT' ∧
                                                                ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT' ∧
                                                                  ∀ (Δ_alt : _root_.B.RenamingContext.Context)
                                                                    (Δ_fv_alt :
                                                                      ∀ v ∈ _root_.B.fv A, (Δ_alt v).isSome = true)
                                                                    (Δ₀_alt : SMT.RenamingContext.Context),
                                                                    RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt A →
                                                                      (∀ v ∉ E'.usedVars, Δ₀_alt v = none) →
                                                                      (∀ v (d : SMT.Dom), Δ₀_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) →
                                                                        ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦α⟧ᶻ),
                                                                          ⟦A.abstract Δ_alt Δ_fv_alt⟧ᴮ =
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
  (B_ih :
    ∀ (E : _root_.B.Env) {Λ : SMT.TypeContext} {α : BType},
      E.context ⊢ᴮ B : α →
        ∀ {«Δ» : _root_.B.RenamingContext.Context} (Δ_fv : ∀ v ∈ _root_.B.fv B, («Δ» v).isSome = true)
          {Δ₀ : SMT.RenamingContext.Context},
          RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» B →
            ∀ {used : List SMT.𝒱},
              (∀ v ∉ used, Δ₀ v = none) →
                ∀ {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ},
                  ⟦B.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩ →
                    (∀ v ∈ B.vars, v ∈ used) →
                      (∀ v ∈ B.vars, v ∈ Λ → v ∈ E.context) →
                        ∀ {n : ℕ},
                          ⦃fun x =>
                            match x with
                            | { env := E0, types := Λ' } =>
                              ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
                            encodeTerm B E ⦃PostCond.mayThrow fun x x_1 =>
                              match x with
                              | (t', σ) =>
                                match x_1 with
                                | { env := E', types := Γ' } =>
                                  ⌜used ⊆ E'.usedVars ∧
                                      Λ ⊆ Γ' ∧
                                        AList.keys Γ' ⊆ E'.usedVars ∧
                                          CoversUsedVars E'.usedVars B ∧
                                            σ = α.toSMTType ∧
                                              Γ' ⊢ˢ t' : σ ∧
                                                (∀ v ∈ used, v ∉ Λ → v ∉ _root_.B.fv B → v ∉ Γ') ∧
                                                  ∃ Δ',
                                                    ∃ (Δ'_covers : RenamingContext.CoversFV Δ' t'),
                                                      RenamingContext.Extends Δ' Δ₀ ∧
                                                        RenamingContext.ExtendsOnSourceFV Δ' «Δ» B ∧
                                                          (∀ v ∉ E'.usedVars, Δ' v = none) ∧
                                                            ∃ denT',
                                                              ⟦t'.abstract Δ' Δ'_covers⟧ˢ = some denT' ∧
                                                                ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT' ∧
                                                                  ∀ (Δ_alt : _root_.B.RenamingContext.Context)
                                                                    (Δ_fv_alt :
                                                                      ∀ v ∈ _root_.B.fv B, (Δ_alt v).isSome = true)
                                                                    (Δ₀_alt : SMT.RenamingContext.Context),
                                                                    RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt B →
                                                                      (∀ v ∉ E'.usedVars, Δ₀_alt v = none) →
                                                                      (∀ v (d : SMT.Dom), Δ₀_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) →
                                                                        ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦α⟧ᶻ),
                                                                          ⟦B.abstract Δ_alt Δ_fv_alt⟧ᴮ =
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
  (E : _root_.B.Env) {Λ : SMT.TypeContext} {α : BType} (typ_t : E.context ⊢ᴮ A ∪ᴮ B : α)
  {«Δ» : _root_.B.RenamingContext.Context} (Δ_fv : ∀ v ∈ _root_.B.fv (A ∪ᴮ B), («Δ» v).isSome = true)
  {Δ₀ : SMT.RenamingContext.Context} (Δ₀_ext : RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» (A ∪ᴮ B)) {used : List SMT.𝒱}
  (Δ₀_none_out : ∀ v ∉ used, Δ₀ v = none) {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ}
  (den_t : ⟦(A ∪ᴮ B).abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩) (vars_used : ∀ v ∈ (A ∪ᴮ B).vars, v ∈ used)
  (Λ_inv : ∀ v ∈ (A ∪ᴮ B).vars, v ∈ Λ → v ∈ E.context) {n : ℕ} :
  ⦃fun x =>
    match x with
    | { env := E0, types := Λ' } => ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
    encodeTerm (A ∪ᴮ B) E ⦃PostCond.mayThrow fun x x_1 =>
      match x with
      | (t', σ) =>
        match x_1 with
        | { env := E', types := Γ' } =>
          ⌜used ⊆ E'.usedVars ∧
              Λ ⊆ Γ' ∧
                AList.keys Γ' ⊆ E'.usedVars ∧
                  CoversUsedVars E'.usedVars (A ∪ᴮ B) ∧
                    σ = α.toSMTType ∧
                      Γ' ⊢ˢ t' : σ ∧
                        (∀ v ∈ used, v ∉ Λ → v ∉ _root_.B.fv (A ∪ᴮ B) → v ∉ Γ') ∧
                          ∃ Δ',
                            ∃ (Δ'_covers : RenamingContext.CoversFV Δ' t'),
                              RenamingContext.Extends Δ' Δ₀ ∧
                                RenamingContext.ExtendsOnSourceFV Δ' «Δ» (A ∪ᴮ B) ∧
                                  (∀ v ∉ E'.usedVars, Δ' v = none) ∧
                                    ∃ denT',
                                      ⟦t'.abstract Δ' Δ'_covers⟧ˢ = some denT' ∧
                                        ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT' ∧
                                          ∀ (Δ_alt : _root_.B.RenamingContext.Context)
                                            (Δ_fv_alt : ∀ v ∈ _root_.B.fv (A ∪ᴮ B), (Δ_alt v).isSome = true)
                                            (Δ₀_alt : SMT.RenamingContext.Context),
                                            RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt (A ∪ᴮ B) →
                                              (∀ v ∉ E'.usedVars, Δ₀_alt v = none) →
                                              (∀ v (d : SMT.Dom), Δ₀_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) →
                                                ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦α⟧ᶻ),
                                                  ⟦(A ∪ᴮ B).abstract Δ_alt Δ_fv_alt⟧ᴮ = some ⟨T_alt, ⟨α, hT_alt⟩⟩ →
                                                    ∃ Δ'_alt,
                                                      ∃ (hcov_alt : RenamingContext.CoversFV Δ'_alt t'),
                                                        ∃ denT_alt,
                                                          RenamingContext.Extends Δ'_alt Δ₀_alt ∧
                                                            (∀ v ∉ E'.usedVars, Δ'_alt v = none) ∧
                                                              (∀ v (d : SMT.Dom), Δ'_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) ∧
                                                              ⟦t'.abstract Δ'_alt hcov_alt⟧ˢ = some denT_alt ∧
                                                                ⟨T_alt, ⟨α, hT_alt⟩⟩ ≘ᶻ denT_alt ∧
                                                                                        (∀ v, Δ'_alt v ≠ none → v ∈ Γ')⌝⦄ := by
  mintro pre ∀St₀
  mpure pre
  obtain ⟨rfl, rfl, St₀_sub, rfl⟩ := pre

  obtain ⟨α, rfl, typ_A, typ_B⟩ := Typing.unionE typ_t
  clear typ_t

  have Δ_fv_A : ∀ v ∈ _root_.B.fv A, («Δ» v).isSome = true := by
    intro v hv
    exact Δ_fv v (by rw [B.fv, List.mem_append]; exact Or.inl hv)
  have Δ_fv_B : ∀ v ∈ _root_.B.fv B, («Δ» v).isSome = true := by
    intro v hv
    exact Δ_fv v (by rw [B.fv, List.mem_append]; exact Or.inr hv)

  rw [B.Term.abstract, B.denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at den_t
  obtain ⟨⟨A', α', hA'⟩, den_A, eq⟩ := den_t
  have αx_eq := denote_welltyped_eq
    (t := A.abstract («Δ» := «Δ») Δ_fv_A)
    ?_ den_A
  on_goal 2 =>
    use E.context.abstract («Δ» := «Δ»), WFTC.of_abstract, α.set
    exact @Typing.of_abstract (_root_.B.Dom) («Δ» := «Δ») ?_ A E.context _ Δ_fv_A typ_A
  dsimp at αx_eq
  subst α'

  dsimp at eq
  rw [Option.bind_eq_some_iff] at eq
  obtain ⟨⟨B', β', hB'⟩, den_B, eq⟩ := eq
  have := denote_welltyped_eq
    (t := B.abstract («Δ» := «Δ») Δ_fv_B)
    ?_ den_B
  on_goal 2 =>
    use E.context.abstract («Δ» := «Δ»), WFTC.of_abstract, α.set
    exact @Typing.of_abstract (_root_.B.Dom) («Δ» := «Δ») ?_ B E.context _ Δ_fv_B typ_B
  dsimp at this
  subst β'

  dsimp at eq
  rw [dif_pos rfl, Option.some_inj] at eq
  obtain ⟨⟩ := eq

  have Δ₀_ext_A : RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» A := by
    apply RenamingContext.extendsOnSourceFV_of_fv_subset _ Δ₀_ext
    · intro v hv
      rw [_root_.B.fv, List.mem_append]
      left
      exact hv
  have Δ₀_ext_B : RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» B := by
    apply RenamingContext.extendsOnSourceFV_of_fv_subset _ Δ₀_ext
    · intro v hv
      rw [_root_.B.fv, List.mem_append]
      right
      exact hv

  ---

  rw [encodeTerm]

  mspec A_ih (E := E) (Λ := St₀.types) (α := α.set) typ_A («Δ» := «Δ») Δ_fv_A
    (Δ₀ := Δ₀) Δ₀_ext_A (used := St₀.env.usedVars) Δ₀_none_out (T := A') (hT := hA')
    den_A
    (fun v hv => vars_used v (by simp only [_root_.B.Term.vars, List.mem_union_iff, _root_.B.fv, _root_.B.bv, List.mem_append] at hv ⊢; rcases hv with h | h <;> [left; right] <;> exact .inl h))
    (fun v hv => Λ_inv v (by simp only [_root_.B.Term.vars, List.mem_union_iff, _root_.B.fv, _root_.B.bv, List.mem_append] at hv ⊢; rcases hv with h | h <;> [left; right] <;> exact .inl h))
    (n := St₀.env.freshvarsc)
  clear A_ih

  next out =>
    obtain ⟨Aenc, _⟩ := out

    mrename_i pre
    mintro ∀St₁
    mpure pre

    dsimp at pre
    obtain ⟨St₀_used_sub_St₁, St₀_sub_St₁, St₁_sub, A_cov_St₁, rfl, typ_Aenc, A_preserves,
      Δ', Δ'_covers_x, Δ'_extends_Δ₀, Δ'_ext_x, Δ'_none_out,
      ⟨Aenc', _, hAenc'⟩, den_Aenc, ⟨rfl, retract_Aenc'_eq_A'⟩, A_ih_total⟩ := pre

    have Δ'_ext_B : RenamingContext.ExtendsOnSourceFV Δ' «Δ» B :=
      RenamingContext.extendsOnSourceFV_of_extends Δ'_extends_Δ₀ Δ₀_ext_B
    mspec B_ih (E := E) (Λ := St₁.types) (α := α.set) typ_B («Δ» := «Δ») Δ_fv_B
      (Δ₀ := Δ') Δ'_ext_B (used := St₁.env.usedVars) Δ'_none_out (T := B') (hT := hB')
      den_B
      (fun v hv => St₀_used_sub_St₁ (vars_used v (by simp only [_root_.B.Term.vars, List.mem_union_iff, _root_.B.fv, _root_.B.bv, List.mem_append] at hv ⊢; rcases hv with h | h <;> [left; right] <;> exact .inr h)))
      (fun v hv hΛ => by
        have hv_mem : v ∈ (A ∪ᴮ B).vars := by
          simp only [_root_.B.Term.vars, List.mem_union_iff, _root_.B.fv, _root_.B.bv, List.mem_append] at hv ⊢
          rcases hv with h | h <;> [left; right] <;> exact .inr h
        by_cases hv_St : v ∈ St₀.types
        · exact Λ_inv v hv_mem hv_St
        · have hv_fv_A : v ∈ _root_.B.fv A := by
            by_contra h_neg
            exact absurd hΛ (A_preserves v (vars_used v hv_mem) hv_St h_neg)
          exact _root_.B.Typing.typed_by_fv typ_A hv_fv_A)
      (n := St₁.env.freshvarsc)
    clear B_ih

    next out =>
      obtain ⟨Benc, _⟩ := out

      mrename_i pre
      mintro ∀St₂
      mpure pre
      obtain ⟨St₁_used_sub_St₂, St₁_sub_St₂, St₂_sub, B_cov_St₂, rfl, typ_Benc, B_preserves,
        Δ'', Δ''_covers_y, Δ''_extends_Δ', Δ''_ext_y, Δ''_none_out,
        ⟨Benc', _, hBenc'⟩, den_Benc, ⟨rfl, retract_Benc'_eq_B'⟩, B_ih_total⟩ := pre
      dsimp at den_Benc

      ---
      -- Apply the castUnion spec
      have Δ''_fv_A : SMT.RenamingContext.CoversFV Δ'' Aenc :=
        SMT.RenamingContext.coversFV_of_extends_of_coversFV (hext := Δ''_extends_Δ') (hcov := Δ'_covers_x)
      have Δ''_fv_B : SMT.RenamingContext.CoversFV Δ'' Benc := Δ''_covers_y

      have den_Aenc_Δ'' : ⟦Aenc.abstract Δ'' Δ''_fv_A⟧ˢ = some ⟨Aenc', α.set.toSMTType, hAenc'⟩ := by
        trans
        · apply RenamingContext.denote_congr_of_agreesOnFV (t := Aenc) (h1 := Δ''_fv_A) (h2 := Δ'_covers_x)
          exact RenamingContext.agreesOnFV_of_extends_of_coversFV (hext := Δ''_extends_Δ') (hcov := Δ'_covers_x)
        · exact den_Aenc

      -- Set γ = α.toSMTType (the element type of the characteristic predicate)
      set γ := α.toSMTType with γ_def
      -- Inline castUnion for the direct α = β path
      have hcastUnion' :
          castUnion (Aenc, .fun γ .bool) (Benc, .fun γ .bool) = do
            let z ← freshVar γ "union!"
            return (.lambda [z] [γ] (.or (.app Aenc (.var z)) (.app Benc (.var z))), .fun γ .bool) := by
        unfold castUnion; simp
      rw [show castUnion (Aenc, α.set.toSMTType) (Benc, α.set.toSMTType) =
              castUnion (Aenc, .fun γ .bool) (Benc, .fun γ .bool) from rfl,
          hcastUnion']
      mspec freshVar_spec
      next z =>
        mrename_i cu_pre
        mintro ∀St_z
        mpure cu_pre
        obtain ⟨St_z_types_eq, z_fresh, St_z_fvc, St_z_used_eq, z_not_used⟩ := cu_pre

        have z_not_fv_Aenc : z ∉ SMT.fv Aenc :=
          funNotMemFvOfNotMemContext (Typing.weakening St₁_sub_St₂ typ_Aenc) z_fresh
        have z_not_fv_Benc : z ∉ SMT.fv Benc :=
          funNotMemFvOfNotMemContext typ_Benc z_fresh

        -- Δ'' covers fv(Aenc) and fv(Benc)
        have Δ''_fv_A : SMT.RenamingContext.CoversFV Δ'' Aenc :=
          SMT.RenamingContext.coversFV_of_extends_of_coversFV (hext := Δ''_extends_Δ') (hcov := Δ'_covers_x)
        have Δ''_fv_B : SMT.RenamingContext.CoversFV Δ'' Benc := Δ''_covers_y

        have den_Aenc_Δ'' : ⟦Aenc.abstract Δ'' Δ''_fv_A⟧ˢ = some ⟨Aenc', α.set.toSMTType, hAenc'⟩ := by
          trans
          · apply RenamingContext.denote_congr_of_agreesOnFV (t := Aenc) (h1 := Δ''_fv_A) (h2 := Δ'_covers_x)
            exact RenamingContext.agreesOnFV_of_extends_of_coversFV (hext := Δ''_extends_Δ') (hcov := Δ'_covers_x)
          · exact den_Aenc

        -- Δ'' covers fv(lambda [z] [γ] (or (app Aenc (var z)) (app Benc (var z))))
        have Δ''_cov_lambda : SMT.RenamingContext.CoversFV Δ''
            (.lambda [z] [γ] (.or (.app Aenc (.var z)) (.app Benc (.var z)))) := by
          intro v hv
          simp only [SMT.fv, List.removeAll, List.mem_filter, List.mem_append,
            List.mem_cons, List.not_mem_nil, or_false] at hv
          obtain ⟨hv_body, hv_ne_z⟩ := hv
          simp only [List.elem_eq_contains, List.contains_eq_mem, List.mem_cons,
            List.not_mem_nil, or_false, Bool.not_eq_true', decide_eq_false_iff_not] at hv_ne_z
          rcases hv_body with ((hv_A | rfl) | (hv_B | rfl))
          · exact Δ''_fv_A v hv_A
          · exact absurd rfl hv_ne_z
          · exact Δ''_fv_B v hv_B
          · exact absurd rfl hv_ne_z

        mspec Std.Do.Spec.pure
        mpure_intro
        and_intros
        -- (1) used ⊆ E'.usedVars
        · intro v hv
          rw [St_z_used_eq]
          exact List.mem_cons_of_mem z (St₁_used_sub_St₂ (St₀_used_sub_St₁ hv))
        -- (2) Λ ⊆ Γ'
        · rw [St_z_types_eq]
          exact fun v hv => TypeContext.entries_subset_insert_of_notMem z_fresh (St₁_sub_St₂ (St₀_sub_St₁ hv))
        -- (3) keys Γ' ⊆ E'.usedVars
        · intro v hv
          rw [St_z_types_eq, AList.keys_insert, List.mem_cons] at hv
          rw [St_z_used_eq]
          rcases hv with rfl | hv
          · exact List.mem_cons_self
          · rw [List.erase_of_not_mem z_fresh] at hv
            exact List.mem_cons_of_mem z (St₂_sub hv)
        -- (4) CoversUsedVars
        · intro v hv
          rw [_root_.B.fv, List.mem_append] at hv
          rcases hv with hv | hv
          · rw [St_z_used_eq]; exact List.mem_cons_of_mem z (St₁_used_sub_St₂ (A_cov_St₁ v hv))
          · rw [St_z_used_eq]; exact List.mem_cons_of_mem z (B_cov_St₂ v hv)
        -- (5) τ = α.set.toSMTType
        · rfl
        -- (6) typing
        · rw [St_z_types_eq]
          have z_not_bv_Aenc : z ∉ SMT.bv Aenc := by
            have htyp := Typing.weakening (TypeContext.entries_subset_insert_of_notMem (τ := γ) z_fresh)
              (Typing.weakening St₁_sub_St₂ typ_Aenc)
            intro hbv
            exact Typing.bv_notMem_context htyp z hbv (by rw [AList.mem_insert]; exact Or.inl rfl)
          have z_not_bv_Benc : z ∉ SMT.bv Benc := by
            have htyp := Typing.weakening (TypeContext.entries_subset_insert_of_notMem (τ := γ) z_fresh) typ_Benc
            intro hbv
            exact Typing.bv_notMem_context htyp z hbv (by rw [AList.mem_insert]; exact Or.inl rfl)
          apply Typing.weakening (TypeContext.entries_subset_insert_of_notMem (τ := γ) z_fresh)
          refine Typing.lambda St₂.types [z] [γ] _ .bool ?_ ?_ ?_ ?_ ?_
          · intro v hv; rw [List.mem_singleton] at hv; subst hv; exact z_fresh
          · intro v hv; rw [List.mem_singleton] at hv; subst hv
            simp only [SMT.bv, List.append_nil, List.mem_append]
            push_neg; exact ⟨z_not_bv_Aenc, z_not_bv_Benc⟩
          · exact Nat.zero_lt_succ 0
          · rfl
          · have hupdate : TypeContext.update St₂.types [z] [γ] rfl = St₂.types.insert z γ := by
              simp only [TypeContext.update, List.length_cons, List.length_nil, zero_add,
                Nat.reduceAdd, Fin.cast_eq_self, Fin.getElem_fin, Fin.val_eq_zero,
                List.getElem_cons_zero, Fin.foldl_succ, Fin.foldl_zero]
            rw [hupdate]
            apply SMT.Typing.or
            · apply SMT.Typing.app
              · exact Typing.weakening (TypeContext.entries_subset_insert_of_notMem (τ := γ) z_fresh)
                  (Typing.weakening St₁_sub_St₂ typ_Aenc)
              · exact SMT.Typing.var _ z γ (AList.lookup_insert St₂.types)
            · apply SMT.Typing.app
              · exact Typing.weakening (TypeContext.entries_subset_insert_of_notMem (τ := γ) z_fresh) typ_Benc
              · exact SMT.Typing.var _ z γ (AList.lookup_insert St₂.types)
        -- (7) preserves_types: ∀ v ∈ used, v ∉ Λ → v ∉ fv(A ∪ᴮ B) → v ∉ Γ'
        · intro v hv h1 h2
          rw [_root_.B.fv, List.mem_append] at h2; push_neg at h2
          rw [St_z_types_eq, AList.mem_insert]; push_neg
          exact ⟨fun h => absurd (h ▸ St₁_used_sub_St₂ (St₀_used_sub_St₁ hv)) z_not_used,
            B_preserves v (St₀_used_sub_St₁ hv) (A_preserves v hv h1 h2.1) h2.2⟩
        -- (8) renaming context + denotation
        · -- Use Δ'' as the renaming context; apply castUnion_denotation_direct
          obtain ⟨den_lambda, hden_lambda, htype_lambda, hretract_lambda⟩ :=
            castUnion_denotation_direct Δ''_fv_A Δ''_fv_B
              den_Aenc_Δ'' den_Benc
              (rfl : α.set.toSMTType = .fun γ .bool) (rfl : α.set.toSMTType = .fun γ .bool)
              z_not_fv_Aenc z_not_fv_Benc Δ''_cov_lambda
          have Δ''_none_out_z : ∀ v ∉ St_z.env.usedVars, Δ'' v = none := by
            intro v hv; apply Δ''_none_out
            intro hmem; exact hv (St_z_used_eq ▸ List.mem_cons_of_mem z hmem)
          refine ⟨Δ'', Δ''_cov_lambda, ?_, ?_, Δ''_none_out_z, ?_⟩
          · -- Extends Δ'' Δ₀
            exact RenamingContext.extends_trans Δ''_extends_Δ' Δ'_extends_Δ₀
          · -- ExtendsOnSourceFV Δ'' «Δ» (A ∪ᴮ B)
            intro v D hv
            exact Δ''_extends_Δ' (Δ'_extends_Δ₀ (Δ₀_ext hv))
          · refine ⟨den_lambda, hden_lambda, ?_, ?_⟩
            · -- RDom
              constructor
              · exact htype_lambda
              · rw [hretract_lambda α rfl, retract_Aenc'_eq_A', retract_Benc'_eq_B']
                rfl
            · -- ih_total: alt universality
              intro Δ_alt Δ_fv_alt Δ₀_alt Δ₀_alt_ext Δ₀_alt_none_out Δ₀_alt_wt T_alt hT_alt den_t_alt
              -- Decompose B-denotation of (A ∪ᴮ B) under alt valuation
              rw [_root_.B.Term.abstract, _root_.B.denote, Option.pure_def, Option.bind_eq_bind,
                Option.bind_eq_some_iff] at den_t_alt
              obtain ⟨⟨A_alt, α_alt', hA_alt⟩, den_A_alt, eq_alt⟩ := den_t_alt
              have α_alt_eq := @denote_welltyped_eq
                (A.abstract Δ_alt (fun v hv => Δ_fv_alt v (by rw [_root_.B.fv, List.mem_append]; exact Or.inl hv)))
                A_alt α_alt' hA_alt ?_ den_A_alt
              on_goal 2 =>
                use E.context.abstract («Δ» := Δ_alt), WFTC.of_abstract, α.set
                exact @Typing.of_abstract (_root_.B.Dom) («Δ» := Δ_alt) ?_ A E.context α.set
                  (fun v hv => Δ_fv_alt v (by rw [_root_.B.fv, List.mem_append]; exact Or.inl hv)) typ_A
              dsimp at α_alt_eq; subst α_alt_eq
              dsimp at eq_alt
              rw [Option.bind_eq_some_iff] at eq_alt
              obtain ⟨⟨B_alt, _, hB_alt⟩, den_B_alt, eq_alt⟩ := eq_alt
              have β_alt_eq := @denote_welltyped_eq
                (_root_.B.Term.abstract B Δ_alt (fun v hv => Δ_fv_alt v (by rw [_root_.B.fv, List.mem_append]; exact Or.inr hv)))
                B_alt _ hB_alt ?_ den_B_alt
              on_goal 2 =>
                use E.context.abstract («Δ» := Δ_alt), WFTC.of_abstract, α.set
                exact @Typing.of_abstract (_root_.B.Dom) («Δ» := Δ_alt) ?_ B E.context α.set
                  (fun v hv => Δ_fv_alt v (by rw [_root_.B.fv, List.mem_append]; exact Or.inr hv)) typ_B
              dsimp at β_alt_eq; subst β_alt_eq
              dsimp at eq_alt
              rw [dif_pos rfl, Option.some_inj] at eq_alt
              obtain ⟨⟩ := eq_alt
              -- Build restricted base for A IH
              set Δ₀_alt_A : SMT.RenamingContext.Context :=
                fun v => if v ∈ St₁.env.usedVars then Δ₀_alt v else none with Δ₀_alt_A_def
              have Δ₀_alt_A_ext : RenamingContext.ExtendsOnSourceFV Δ₀_alt_A Δ_alt A := by
                have hsrc := RenamingContext.extendsOnSourceFV_of_fv_subset
                  (hsub := by intro v hv; simpa [_root_.B.fv] using
                    (Or.inl hv : v ∈ _root_.B.fv A ∨ v ∈ _root_.B.fv B))
                  Δ₀_alt_ext
                intro v d hv
                simp only [Δ₀_alt_A_def]
                have hv_fv : v ∈ _root_.B.fv A := by
                  by_contra hv_not
                  simp [_root_.B.RenamingContext.toSMTOnFV, _root_.B.RenamingContext.toSMT,
                    _root_.B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_not] at hv
                have hv_used : v ∈ St₁.env.usedVars :=
                  St₀_used_sub_St₁ (vars_used v (by
                    simp only [_root_.B.Term.vars, List.mem_union_iff, _root_.B.fv, _root_.B.bv,
                      List.mem_append]
                    left; left; exact hv_fv))
                rw [if_pos hv_used]
                exact hsrc hv
              have Δ₀_alt_A_none : ∀ v ∉ St₁.env.usedVars, Δ₀_alt_A v = none := by
                intro v hv; simp only [Δ₀_alt_A_def]; rw [if_neg hv]
              have Δ₀_alt_A_wt : ∀ v (d : SMT.Dom), Δ₀_alt_A v = some d → ∀ τ, St₁.types.lookup v = some τ → d.snd.fst = τ := by
                intro v d hv τ hτ; simp only [Δ₀_alt_A_def] at hv; split_ifs at hv with h; exact Δ₀_alt_wt v d hv τ (by rw [St_z_types_eq]; exact AList.mem_lookup_iff.mpr (SMT.TypeContext.entries_subset_insert_of_notMem z_fresh (St₁_sub_St₂ (AList.mem_lookup_iff.mp hτ))))
              -- Call A_ih_total
              obtain ⟨Δ'_alt_A, hcov_alt_A, denT_A_alt, hext_alt_A,
                Δ'_alt_A_none_out, Δ'_alt_A_wt_out, den_A_alt_enc, hRDom_A_alt, _⟩ :=
                A_ih_total Δ_alt
                  (fun v hv => Δ_fv_alt v (by rw [_root_.B.fv, List.mem_append]; exact Or.inl hv))
                  Δ₀_alt_A Δ₀_alt_A_ext Δ₀_alt_A_none Δ₀_alt_A_wt A_alt hA_alt den_A_alt
              -- Build hybrid base for B IH; zero out variables not in St₂.env.usedVars
              set Δ₀_alt_B : SMT.RenamingContext.Context :=
                fun v => if v ∈ St₂.env.usedVars
                         then (match Δ₀_alt v with
                           | some d => some d
                           | none => if v ∈ St₁.types then Δ'_alt_A v else none)
                         else none
                with Δ₀_alt_B_def
              have Δ₀_alt_B_ext : RenamingContext.ExtendsOnSourceFV Δ₀_alt_B Δ_alt B := by
                have hsrc := RenamingContext.extendsOnSourceFV_of_fv_subset
                  (hsub := by intro v hv; simpa [_root_.B.fv] using
                    (Or.inr hv : v ∈ _root_.B.fv A ∨ v ∈ _root_.B.fv B))
                  Δ₀_alt_ext
                intro v d hv
                simp only [Δ₀_alt_B_def]
                have hv_fv : v ∈ _root_.B.fv B := by
                  by_contra hv_not
                  simp [_root_.B.RenamingContext.toSMTOnFV, _root_.B.RenamingContext.toSMT,
                    _root_.B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_not] at hv
                have hv_used : v ∈ St₂.env.usedVars :=
                  St₁_used_sub_St₂ (St₀_used_sub_St₁ (vars_used v (by
                    simp only [_root_.B.Term.vars, List.mem_union_iff, _root_.B.fv, _root_.B.bv,
                      List.mem_append]
                    left; right; exact hv_fv)))
                rw [if_pos hv_used]
                have hΔ₀_val := hsrc hv
                simp [hΔ₀_val]
              have Δ₀_alt_B_none : ∀ v ∉ St₂.env.usedVars, Δ₀_alt_B v = none := by
                intro v hv; simp only [Δ₀_alt_B_def]; rw [if_neg hv]
              have Δ₀_alt_B_wt : ∀ v (d : SMT.Dom), Δ₀_alt_B v = some d → ∀ τ, St₂.types.lookup v = some τ → d.snd.fst = τ := by
                intro v d hv τ hτ
                simp only [Δ₀_alt_B_def] at hv
                by_cases h_used : v ∈ St₂.env.usedVars
                · rw [if_pos h_used] at hv
                  cases hΔ : Δ₀_alt v with
                  | some d' =>
                    simp [hΔ] at hv; subst hv
                    exact Δ₀_alt_wt v d' hΔ τ (by
                      rw [St_z_types_eq]
                      exact AList.mem_lookup_iff.mpr
                        (SMT.TypeContext.entries_subset_insert_of_notMem z_fresh
                          (AList.mem_lookup_iff.mp (Option.mem_def.mpr hτ))))
                  | none =>
                    simp [hΔ] at hv
                    obtain ⟨h_mem, hv⟩ := hv
                    exact Δ'_alt_A_wt_out v d hv τ (by
                      obtain ⟨τ', hτ'⟩ := Option.isSome_iff_exists.mp (AList.lookup_isSome.mpr h_mem)
                      have h_lkp := AList.lookup_of_subset St₁_sub_St₂ hτ'
                      rw [hτ] at h_lkp; cases h_lkp; exact hτ')
                · rw [if_neg h_used] at hv; exact absurd hv (by simp)
              -- Call B_ih_total
              obtain ⟨Δ'_alt_B, hcov_alt_B, denT_B_alt, hext_alt_B,
                Δ'_alt_B_none_out, Δ'_alt_B_wt_out, den_B_alt_enc, hRDom_B_alt, Δ'_alt_B_dom_out⟩ :=
                B_ih_total Δ_alt
                  (fun v hv => Δ_fv_alt v (by rw [_root_.B.fv, List.mem_append]; exact Or.inr hv))
                  Δ₀_alt_B Δ₀_alt_B_ext Δ₀_alt_B_none Δ₀_alt_B_wt B_alt hB_alt den_B_alt
              -- Define final Δ'_alt = priority merge(Δ₀_alt, Δ'_alt_B)
              set Δ'_alt : SMT.RenamingContext.Context :=
                fun v => match Δ₀_alt v with | some d => some d | none => Δ'_alt_B v
                with Δ'_alt_def
              -- Extract types from alt denotations
              obtain ⟨Aenc_alt, σ_A_alt, hAenc_alt⟩ := denT_A_alt
              obtain ⟨Benc_alt, σ_B_alt, hBenc_alt⟩ := denT_B_alt
              obtain ⟨rfl, retract_A_alt⟩ := hRDom_A_alt
              obtain ⟨rfl, retract_B_alt⟩ := hRDom_B_alt
              -- Coverage of Aenc and Benc under Δ'_alt
              have hcov_A_alt : RenamingContext.CoversFV Δ'_alt Aenc := by
                intro v hv; simp only [Δ'_alt_def]
                cases h : Δ₀_alt v with
                | some d => simp
                | none =>
                  have hv_St₂ : v ∈ St₂.env.usedVars :=
                    St₁_used_sub_St₂ (by
                      by_contra hv_not
                      exact absurd (Δ'_covers_x v hv) (by simp [Δ'_none_out v hv_not]))
                  have hv_types : v ∈ St₁.types :=
                    SMT.Typing.mem_context_of_mem_fv typ_Aenc hv
                  have hΔ₀_alt_B_v : Δ₀_alt_B v = Δ'_alt_A v := by
                    simp [Δ₀_alt_B_def, if_pos hv_St₂, h, if_pos hv_types]
                  have hA_some := hcov_alt_A v hv
                  obtain ⟨dA, hdA⟩ := Option.isSome_iff_exists.mp hA_some
                  have := hext_alt_B (by rw [hΔ₀_alt_B_v, hdA])
                  rw [this]; simp
              have hcov_B_alt : RenamingContext.CoversFV Δ'_alt Benc := by
                intro v hv; simp only [Δ'_alt_def]
                cases h : Δ₀_alt v with
                | some d => simp
                | none => exact hcov_alt_B v hv
              -- Δ'_alt agrees with Δ'_alt_A on fv(Aenc)
              have hagree_A : RenamingContext.AgreesOnFV Δ'_alt Δ'_alt_A Aenc := by
                intro v hv; simp only [Δ'_alt_def]
                cases h : Δ₀_alt v with
                | some d =>
                  have hv_σ₁ : v ∈ St₁.env.usedVars := by
                    by_contra hv_not
                    exact absurd (Δ'_covers_x v hv) (by simp [Δ'_none_out v hv_not])
                  have : Δ₀_alt_A v = some d := by simp [Δ₀_alt_A_def, if_pos hv_σ₁, h]
                  symm; exact hext_alt_A this
                | none =>
                  have hv_St₂ : v ∈ St₂.env.usedVars :=
                    St₁_used_sub_St₂ (by
                      by_contra hv_not
                      exact absurd (Δ'_covers_x v hv) (by simp [Δ'_none_out v hv_not]))
                  have hv_types : v ∈ St₁.types :=
                    SMT.Typing.mem_context_of_mem_fv typ_Aenc hv
                  have hΔ₀_alt_B_v : Δ₀_alt_B v = Δ'_alt_A v := by
                    simp [Δ₀_alt_B_def, if_pos hv_St₂, h, if_pos hv_types]
                  have hA_some : (Δ'_alt_A v).isSome = true := hcov_alt_A v hv
                  obtain ⟨dA, hdA⟩ := Option.isSome_iff_exists.mp hA_some
                  have h₁ : Δ₀_alt_B v = some dA := by rw [hΔ₀_alt_B_v, hdA]
                  rw [hext_alt_B h₁, hdA]
              -- Δ'_alt agrees with Δ'_alt_B on fv(Benc)
              have hagree_B : RenamingContext.AgreesOnFV Δ'_alt Δ'_alt_B Benc := by
                intro v hv; simp only [Δ'_alt_def]
                cases h : Δ₀_alt v with
                | some d =>
                  have hv_St₂ : v ∈ St₂.env.usedVars :=
                    St₂_sub (SMT.Typing.mem_context_of_mem_fv typ_Benc hv)
                  have : Δ₀_alt_B v = some d := by
                    simp [Δ₀_alt_B_def, if_pos hv_St₂, h]
                  symm; exact hext_alt_B this
                | none => rfl
              have den_A_alt_final :
                  ⟦Aenc.abstract Δ'_alt hcov_A_alt⟧ˢ = some ⟨Aenc_alt, α.set.toSMTType, hAenc_alt⟩ := by
                have := RenamingContext.denote_congr_of_agreesOnFV
                  (t := Aenc) (h1 := hcov_A_alt) (h2 := hcov_alt_A) hagree_A
                simpa [RenamingContext.denote] using this.trans den_A_alt_enc
              have den_B_alt_final :
                  ⟦Benc.abstract Δ'_alt hcov_B_alt⟧ˢ = some ⟨Benc_alt, α.set.toSMTType, hBenc_alt⟩ := by
                have := RenamingContext.denote_congr_of_agreesOnFV
                  (t := Benc) (h1 := hcov_B_alt) (h2 := hcov_alt_B) hagree_B
                simpa [RenamingContext.denote] using this.trans den_B_alt_enc
              -- Coverage for the lambda under Δ'_alt
              have hcov_lambda_alt : RenamingContext.CoversFV Δ'_alt
                  (.lambda [z] [γ] (.or (.app Aenc (.var z)) (.app Benc (.var z)))) := by
                intro v hv
                simp only [SMT.fv, List.removeAll, List.mem_filter, List.mem_append,
                  List.mem_cons, List.not_mem_nil, or_false] at hv
                obtain ⟨hv_body, hv_ne_z⟩ := hv
                simp only [List.elem_eq_contains, List.contains_eq_mem, List.mem_cons,
                  List.not_mem_nil, or_false, Bool.not_eq_true', decide_eq_false_iff_not] at hv_ne_z
                rcases hv_body with ((hv_A | rfl) | (hv_B | rfl))
                · exact hcov_A_alt v hv_A
                · exact absurd rfl hv_ne_z
                · exact hcov_B_alt v hv_B
                · exact absurd rfl hv_ne_z
              -- Apply castUnion_denotation_direct with Δ'_alt
              obtain ⟨den_lambda_alt, hden_lambda_alt, htype_lambda_alt, hretract_lambda_alt⟩ :=
                castUnion_denotation_direct hcov_A_alt hcov_B_alt
                  den_A_alt_final den_B_alt_final
                  (rfl : α.set.toSMTType = .fun γ .bool) (rfl : α.set.toSMTType = .fun γ .bool)
                  z_not_fv_Aenc z_not_fv_Benc hcov_lambda_alt
              refine ⟨Δ'_alt, hcov_lambda_alt,
                ⟨den_lambda_alt.1, den_lambda_alt.2.1, den_lambda_alt.2.2⟩,
                ?_, ?_, ?_, ?_, ?_, ?_⟩
              -- Extends Δ'_alt Δ₀_alt
              · intro v d hv; simp only [Δ'_alt_def, hv]
              -- Vanishing: ∀ v ∉ E'.usedVars, Δ'_alt v = none
              · intro v hv; simp only [Δ'_alt_def]
                rw [Δ₀_alt_none_out v hv]
                apply Δ'_alt_B_none_out
                intro hmem; exact hv (St_z_used_eq ▸ List.mem_cons_of_mem z hmem)
              -- Well-typedness: output wt
              · intro v d hv τ hτ
                simp only [Δ'_alt_def] at hv
                cases hΔ : Δ₀_alt v with
                | some d' => simp [hΔ] at hv; subst hv; exact Δ₀_alt_wt v d' hΔ τ hτ
                | none =>
                  simp [hΔ] at hv
                  -- hv : Δ'_alt_B v = some d; strip z insert to get St₂ lookup
                  have hv_St₂ : v ∈ St₂.env.usedVars := by
                    by_contra h; exact absurd hv (by simp [Δ'_alt_B_none_out v h])
                  have hv_ne_z : v ≠ z := fun h => z_not_used (h ▸ hv_St₂)
                  rw [St_z_types_eq, AList.lookup_insert_ne hv_ne_z] at hτ
                  exact Δ'_alt_B_wt_out v d hv τ hτ
              -- Denotation under Δ'_alt
              · exact hden_lambda_alt
              -- RDom for alt
              · constructor
                · exact htype_lambda_alt
                · rw [hretract_lambda_alt α rfl, retract_A_alt, retract_B_alt]
                  rfl
              -- dom_out
              · intro v hv
                simp only [Δ'_alt_def] at hv
                cases hΔ : Δ₀_alt v with
                | some d =>
                  exact fv_sub_typings (_root_.B.Typing.union typ_A typ_B)
                    (SMT.Typing.bool St_z.types true) v
                    (SMT.RenamingContext.ExtendsOnSourceFV.dom_sub_B_fv Δ₀_alt_ext v
                      (by rw [hΔ]; simp))
                | none =>
                  simp [hΔ] at hv
                  -- Δ'_alt_B v ≠ none → v ∈ St₂.types ⊆ St_z.types
                  have h_St₂ := Δ'_alt_B_dom_out v hv
                  rw [St_z_types_eq, AList.mem_insert]
                  exact Or.inr h_St₂
