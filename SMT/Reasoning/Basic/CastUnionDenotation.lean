import SMT.Reasoning.Defs
import SMT.Reasoning.Basic.LoosenAuxExact.FunAux
import SMT.Reasoning.Basic.StateSpecs

open Std.Do B SMT ZFSet

/-! # Direct union denotation semantics -/

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
set_option maxHeartbeats 4000000 in
theorem castUnion_denotation_direct.{u_1}
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
        retract α.set den_t.1 = retract α.set den_S.1 ∪ retract α.set den_T.1) ∧
      (∀ (w : ZFSet.{u_1}) (hw : w ∈ ⟦γ⟧ᶻ),
        w.pair zftrue ∈ den_t.1 ↔
          w.pair zftrue ∈ den_S.1 ∨ w.pair zftrue ∈ den_T.1) := by
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
  refine ⟨lamVal, ?_, hlamVal_ty, ?_, ?_⟩
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
  · intro w hw
    obtain ⟨Dbody, hden_body, hfapply_eq⟩ := hlamVal_app w hw
    obtain ⟨Dbody', hcov_or, hden_body', _, hDbody'_iff⟩ :=
      hbody_den ⟨w, γ, hw⟩ rfl hw
    have hDbody_eq : Dbody = Dbody' := by
      rw [show hcov_orBody_upd ⟨w, γ, hw⟩ = hcov_or from
        Subsingleton.elim _ _] at hden_body
      exact Option.some_injective _ (hden_body.symm.trans hden_body')
    constructor
    · intro hpair
      have htrue :
          (ZFSet.fapply lamVal.fst
            (ZFSet.is_func_is_pfunc hlamVal_func)
            ⟨w, by rw [ZFSet.is_func_dom_eq hlamVal_func]; exact hw⟩).val =
            zftrue :=
        congrArg Subtype.val
          (ZFSet.fapply.of_pair
            (ZFSet.is_func_is_pfunc hlamVal_func) hpair)
      have hbody_true : Dbody'.fst = zftrue := by
        rw [← hDbody_eq, ← hfapply_eq]
        exact htrue
      rcases hDbody'_iff.mp hbody_true with hStrue | hTtrue
      · left
        have hpairS := ZFSet.fapply.def
          (ZFSet.is_func_is_pfunc hdenS_func)
          (by rw [ZFSet.is_func_dom_eq hdenS_func]; exact hw)
        rwa [hStrue] at hpairS
      · right
        have hpairT := ZFSet.fapply.def
          (ZFSet.is_func_is_pfunc hdenT_func)
          (by rw [ZFSet.is_func_dom_eq hdenT_func]; exact hw)
        rwa [hTtrue] at hpairT
    · intro hpair
      have hbody_true : Dbody'.fst = zftrue := by
        apply hDbody'_iff.mpr
        rcases hpair with hpairS | hpairT
        · left
          exact congrArg Subtype.val
            (ZFSet.fapply.of_pair
              (ZFSet.is_func_is_pfunc hdenS_func) hpairS)
        · right
          exact congrArg Subtype.val
            (ZFSet.fapply.of_pair
              (ZFSet.is_func_is_pfunc hdenT_func) hpairT)
      have htrue :
          (ZFSet.fapply lamVal.fst
            (ZFSet.is_func_is_pfunc hlamVal_func)
            ⟨w, by rw [ZFSet.is_func_dom_eq hlamVal_func]; exact hw⟩).val =
            zftrue := by
        rw [hfapply_eq, hDbody_eq]
        exact hbody_true
      have hpairU := ZFSet.fapply.def
        (ZFSet.is_func_is_pfunc hlamVal_func)
        (by rw [ZFSet.is_func_dom_eq hlamVal_func]; exact hw)
      rwa [htrue] at hpairU
