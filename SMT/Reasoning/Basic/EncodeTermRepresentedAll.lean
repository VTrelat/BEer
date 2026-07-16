import SMT.Reasoning.Basic.EncodeTermRepresentedUnion
import SMT.Reasoning.Representation

open Std.Do B SMT ZFSet

/-! # Representation-aware universal quantification -/

open Classical B in
/-- Decompose a supported relation between source and SMT tuples into the
pointwise relation needed by the body induction hypothesis.  This is the
static binder-update form, where both sides are obtained by projecting one
whole tuple. -/
theorem RValuationCastSupportedOnFV.updates_of_reduce_toProdl.{u}
    {Ξ : B.RenamingContext.Context.{u}}
    {Θ : SMT.RenamingContext.Context.{u}}
    {vs : List B.𝒱} (vs_nodup : vs.Nodup)
    {αs : List BType} (αs_nemp : αs ≠ [])
    {σs : List SMTType}
    (vs_αs_len : vs.length = αs.length)
    (αs_σs_len : αs.length = σs.length)
    {X Y : ZFSet.{u}}
    (hX : X ∈ ⟦αs.reduce (· ×ᴮ ·) αs_nemp⟧ᶻ)
    (hY : Y ∈ ⟦σs.toProdl⟧ᶻ)
    (hrel : RDomCastSupported
      (⟨X, αs.reduce (· ×ᴮ ·) αs_nemp, hX⟩ : B.Dom)
      (⟨Y, σs.toProdl, hY⟩ : SMT.Dom))
    {t : B.Term}
    (ambient : ∀ v ∈ B.fv t, v ∉ vs →
      match Ξ v, Θ v with
      | some d, some d' => RDomCastSupported d d'
      | _, _ => False) :
    let bs : Fin vs.length → B.Dom.{u} := fun i =>
      let j : Fin αs.length := Fin.cast vs_αs_len i
      ⟨X.get αs.length j, αs[j],
        BType.mem_get_of_mem_reduce_toZFSet αs_nemp hX⟩
    let ss : Fin vs.length → SMT.Dom.{u} := fun i =>
      let j : Fin σs.length := Fin.cast (vs_αs_len.trans αs_σs_len) i
      ⟨Y.get σs.length j, σs[j],
        SMTType.mem_get_of_mem_toProdl
          (fun hs => αs_nemp (List.length_eq_zero_iff.mp
            (αs_σs_len.trans (by simp [hs])))) hY⟩
    RValuationCastSupportedOnFV
      (Function.updates Ξ vs (List.ofFn fun i => some (bs i)))
      (Function.updates Θ vs (List.ofFn fun i => some (ss i))) t := by
  dsimp only
  apply RValuationCastSupportedOnFV.updates vs_nodup
  · exact ambient
  · intro i
    simpa using RDomCastSupported.get_of_reduce_toProdl
      αs_nemp αs_σs_len hX hY hrel (Fin.cast vs_αs_len i)

open Classical B in
/-- Dynamic form of `updates_of_reduce_toProdl`: the target components are an
arbitrary well-typed quantified assignment whose pair fold is the represented
whole tuple.  Pair-fold injectivity identifies each assignment component with
the corresponding tuple projection. -/
theorem RValuationCastSupportedOnFV.updates_of_fold_reduce_toProdl.{u}
    {Ξ : B.RenamingContext.Context.{u}}
    {Θ : SMT.RenamingContext.Context.{u}}
    {vs : List B.𝒱} (vs_nemp : vs ≠ []) (vs_nodup : vs.Nodup)
    {αs : List BType} (αs_nemp : αs ≠ [])
    {σs : List SMTType}
    (vs_αs_len : vs.length = αs.length)
    (αs_σs_len : αs.length = σs.length)
    {X Y : ZFSet.{u}}
    (hX : X ∈ ⟦αs.reduce (· ×ᴮ ·) αs_nemp⟧ᶻ)
    (hY : Y ∈ ⟦σs.toProdl⟧ᶻ)
    (hrel : RDomCastSupported
      (⟨X, αs.reduce (· ×ᴮ ·) αs_nemp, hX⟩ : B.Dom)
      (⟨Y, σs.toProdl, hY⟩ : SMT.Dom))
    (w : Fin vs.length → SMT.Dom.{u})
    (hw : ∀ i, (w i).snd.fst =
        σs[Fin.cast (vs_αs_len.trans αs_σs_len) i] ∧
      (w i).fst ∈
        ⟦σs[Fin.cast (vs_αs_len.trans αs_σs_len) i]⟧ᶻ)
    (hfold : Fin.foldl (vs.length - 1)
      (fun acc i => acc.pair
        (w ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩).fst)
      (w ⟨0, List.length_pos_iff.mpr vs_nemp⟩).fst = Y)
    {t : B.Term}
    (ambient : ∀ v ∈ B.fv t, v ∉ vs →
      match Ξ v, Θ v with
      | some d, some d' => RDomCastSupported d d'
      | _, _ => False) :
    let bs : Fin vs.length → B.Dom.{u} := fun i =>
      let j : Fin αs.length := Fin.cast vs_αs_len i
      ⟨X.get αs.length j, αs[j],
        BType.mem_get_of_mem_reduce_toZFSet αs_nemp hX⟩
    RValuationCastSupportedOnFV
      (Function.updates Ξ vs (List.ofFn fun i => some (bs i)))
      (Function.updates Θ vs (List.ofFn fun i => some (w i))) t := by
  dsimp only
  apply RValuationCastSupportedOnFV.updates vs_nodup
  · exact ambient
  · intro i
    let jα : Fin αs.length := Fin.cast vs_αs_len i
    let jσ : Fin σs.length :=
      Fin.cast (vs_αs_len.trans αs_σs_len) i
    have hcomp := RDomCastSupported.get_of_reduce_toProdl
      αs_nemp αs_σs_len hX hY hrel jα
    have hY_arity : Y.hasArity vs.length := by
      have harity := ZFSet.hasArity_of_mem_toProdl
        (fun hs => αs_nemp (List.length_eq_zero_iff.mp
          (αs_σs_len.trans (by simp [hs])))) hY
      rwa [← αs_σs_len, ← vs_αs_len] at harity
    have hget : (w i).fst = Y.get vs.length i :=
      foldl_pair_inj_get (List.length_pos_iff.mpr vs_nemp)
        hY_arity (fun i => (w i).fst) hfold i
    have hget' := hget
    rw [ZFSet.get_cast (vs_αs_len.trans αs_σs_len) i] at hget'
    rcases wi : w i with ⟨Wi, σi, hWi⟩
    have htype := (hw i).1
    rw [wi] at htype
    change σi = σs[jσ] at htype
    have hvalue : Wi = Y.get σs.length jσ := by
      rw [wi] at hget'
      exact hget'
    subst σi
    subst Wi
    simpa [jα, jσ] using hcomp

open Classical B in
set_option maxHeartbeats 8000000 in
/-- Semantic Gate C, nonempty-domain branch.  The actual SMT binder may use a
less general type `τs.toProdl`; admissibility supplies a preimage for every
source counterexample, and the existing forall bridge transports that
counterexample through cast-plus-retract. -/
theorem RDomCast.forall_nonempty.{u}
    {vs : List B.𝒱} (vs_nemp : vs ≠ []) (vs_nodup : vs.Nodup)
    {τ : BType} (τ_hasArity : τ.hasArity vs.length)
    {zs : List SMT.𝒱} {τs : List SMTType}
    (zs_nemp : zs ≠ []) (zs_len : zs.length = τs.length)
    (hcast : τs.toProdl ⊑ τ.toSMTType)
    {imp_body : SMT.Term}
    {Δ_ctx : SMT.RenamingContext.Context.{u}}
    (hcov_forall : SMT.RenamingContext.CoversFV Δ_ctx
      (SMT.Term.forall zs τs imp_body))
    {forallVal : SMT.Dom.{u}}
    (hforallVal :
      ⟦(SMT.Term.forall zs τs imp_body).abstract Δ_ctx hcov_forall⟧ˢ =
        some forallVal)
    (hforallVal_type : forallVal.snd.fst = SMTType.bool)
    {𝒟_val : ZFSet.{u}} (h𝒟_val : 𝒟_val ∈ ⟦τ.set⟧ᶻ)
    (𝒟_val_nonempty : 𝒟_val.Nonempty)
    (admissible : BinderCastAdmissible τ τs.toProdl hcast.toCastPath 𝒟_val)
    (hgo_cov : ∀ x ∈ SMT.fv imp_body, x ∉ zs → (Δ_ctx x).isSome = true)
    (hcov_imp_upd : ∀ (w : Fin zs.length → SMT.Dom.{u}),
      SMT.RenamingContext.CoversFV
        (Function.updates Δ_ctx zs (List.ofFn fun i => some (w i))) imp_body)
    (himp_total : ∀ (w : Fin zs.length → SMT.Dom.{u}),
      (∀ i, (w i).snd.fst = τs[i]'(zs_len ▸ i.isLt) ∧
        (w i).fst ∈ ⟦τs[i]'(zs_len ▸ i.isLt)⟧ᶻ) →
      ⟦imp_body.abstract
        (Function.updates Δ_ctx zs (List.ofFn fun i => some (w i)))
        (hcov_imp_upd w)⟧ˢ.isSome = true)
    (himp_ty : ∀ (w : Fin zs.length → SMT.Dom.{u}),
      (∀ i, (w i).snd.fst = τs[i]'(zs_len ▸ i.isLt) ∧
        (w i).fst ∈ ⟦τs[i]'(zs_len ▸ i.isLt)⟧ᶻ) →
      ∀ Db : SMT.Dom.{u},
        ⟦imp_body.abstract
          (Function.updates Δ_ctx zs (List.ofFn fun i => some (w i)))
          (hcov_imp_upd w)⟧ˢ = some Db →
        Db.snd.fst = SMTType.bool)
    {D P : B.Term} {«Δ» : B.RenamingContext.Context}
    (Δ_fv_all : ∀ v ∈ B.fv (Term.all vs D P), («Δ» v).isSome = true)
    {T_val : ZFSet.{u}} (hT_val : T_val ∈ ⟦BType.bool⟧ᶻ)
    (hT_eq : ZFSet.sInter (ZFSet.𝔹.sep fun (y : ZFSet) =>
      ∃ x ∈ 𝒟_val, y =
        (if hx : x.hasArity vs.length ∧ x ∈ ⟦τ⟧ᶻ then
          match ⟦(B.Term.abstract.go P vs «Δ» (fun v hv hvs => Δ_fv_all v
            (B.fv.mem_all (.inr ⟨hv, hvs⟩)))).uncurry
            (fun i => ⟨x.get vs.length i, ⟨τ.get vs.length i,
              get_mem_type_of_isTuple hx.1 τ_hasArity hx.2⟩⟩)⟧ᴮ with
          | some ⟨Pz, _⟩ => Pz
          | none => ZFSet.zffalse
        else ZFSet.zffalse)) = T_val)
    (h_den_P : ∀ {x_fin : Fin vs.length → B.Dom.{u}},
      (∀ i, (x_fin i).snd.fst = τ.get vs.length i ∧
            (x_fin i).fst ∈ ⟦τ.get vs.length i⟧ᶻ) →
      ZFSet.ofFinDom x_fin ∈ 𝒟_val →
      ⟦(B.Term.abstract.go P vs «Δ» (fun v hv hvs => Δ_fv_all v
        (B.fv.mem_all (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ.isSome = true)
    (h_den_P_bool : ∀ {x_fin : Fin vs.length → B.Dom.{u}},
      (∀ i, (x_fin i).snd.fst = τ.get vs.length i ∧
            (x_fin i).fst ∈ ⟦τ.get vs.length i⟧ᶻ) →
      ZFSet.ofFinDom x_fin ∈ 𝒟_val →
      ∀ (Pz : ZFSet.{u}) (P_ty : BType) (hP_val : Pz ∈ ⟦P_ty⟧ᶻ),
      ⟦(B.Term.abstract.go P vs «Δ» (fun v hv hvs => Δ_fv_all v
        (B.fv.mem_all (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ =
          some ⟨Pz, ⟨P_ty, hP_val⟩⟩ →
      P_ty = .bool)
    (zs_len_pos : 0 < zs.length) (vs_zs_len : vs.length = zs.length)
    (hbridge : ∀ (x : ZFSet.{u}) (hx_mem : x ∈ ⟦τs.toProdl⟧ᶻ),
      let x_B := retract_castZF τ hcast x
      let hx_B_mem : x_B ∈ ⟦τ⟧ᶻ := retract_castZF_mem τ hcast hx_mem
      let x_fin : Fin vs.length → B.Dom.{u} := fun i =>
        ⟨x_B.get vs.length i, ⟨τ.get vs.length i,
          get_mem_type_of_isTuple
            (hasArity_of_mem_toZFSet τ_hasArity hx_B_mem)
            τ_hasArity hx_B_mem⟩⟩
      ∀ (w : Fin zs.length → SMT.Dom.{u})
        (_hw : ∀ i, (w i).snd.fst = τs[i]'(zs_len ▸ i.isLt) ∧
          (w i).fst ∈ ⟦τs[i]'(zs_len ▸ i.isLt)⟧ᶻ)
        (_hw_smt : Fin.foldl (zs.length - 1)
          (fun acc i => acc.pair
            (w ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩).fst)
          (w ⟨0, zs_len_pos⟩).fst = x)
        (body_val : SMT.Dom.{u}),
        ⟦imp_body.abstract
          (Function.updates Δ_ctx zs (List.ofFn fun i => some (w i)))
          (hcov_imp_upd w)⟧ˢ = some body_val →
        (body_val.fst = zftrue ↔
          (x_B ∉ 𝒟_val ∨
           ∀ (Px : ZFSet.{u}) (P_ty : BType) (hP_val : Px ∈ ⟦P_ty⟧ᶻ),
             ⟦(B.Term.abstract.go P vs «Δ» (fun v hv hvs => Δ_fv_all v
               (B.fv.mem_all (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ =
               some ⟨Px, ⟨P_ty, hP_val⟩⟩ → Px = zftrue))) :
    RDomCast
      (⟨T_val, BType.bool, hT_val⟩ : B.Dom)
      forallVal := by
  have hret := retract_forallVal_eq_sInter_sep_hasflag
    vs_nemp vs_nodup τ_hasArity zs_nemp zs_len hcast hcov_forall
    hforallVal h𝒟_val 𝒟_val_nonempty hgo_cov hcov_imp_upd himp_total
    himp_ty Δ_fv_all hT_eq h_den_P h_den_P_bool
    (retract_castZF τ hcast) (fun x hx => retract_castZF_mem τ hcast hx)
    admissible zs_len_pos vs_zs_len hbridge
  apply RDom.toRDomCast
  rw [RDom]
  exact ⟨by simpa using hforallVal_type, hret⟩

open Classical B in
set_option maxHeartbeats 8000000 in
/-- Semantic Gate C, empty-domain branch.  No preimage hypothesis is needed:
the source domain contains no counterexample, but the same looser binder type
and helper re-scoping are retained. -/
theorem RDomCast.forall_empty.{u}
    {vs : List B.𝒱} (vs_nemp : vs ≠ [])
    {τ : BType} (τ_hasArity : τ.hasArity vs.length)
    {zs : List SMT.𝒱} {τs : List SMTType}
    (zs_nemp : zs ≠ []) (zs_len : zs.length = τs.length)
    (hcast : τs.toProdl ⊑ τ.toSMTType)
    {imp_body : SMT.Term}
    {Δ_ctx : SMT.RenamingContext.Context.{u}}
    (hcov_forall : SMT.RenamingContext.CoversFV Δ_ctx
      (SMT.Term.forall zs τs imp_body))
    {forallVal : SMT.Dom.{u}}
    (hforallVal :
      ⟦(SMT.Term.forall zs τs imp_body).abstract Δ_ctx hcov_forall⟧ˢ =
        some forallVal)
    (hforallVal_type : forallVal.snd.fst = SMTType.bool)
    (hgo_cov : ∀ x ∈ SMT.fv imp_body, x ∉ zs → (Δ_ctx x).isSome = true)
    (hcov_imp_upd : ∀ (w : Fin zs.length → SMT.Dom.{u}),
      SMT.RenamingContext.CoversFV
        (Function.updates Δ_ctx zs (List.ofFn fun i => some (w i))) imp_body)
    (himp_total : ∀ (w : Fin zs.length → SMT.Dom.{u}),
      (∀ i, (w i).snd.fst = τs[i]'(zs_len ▸ i.isLt) ∧
        (w i).fst ∈ ⟦τs[i]'(zs_len ▸ i.isLt)⟧ᶻ) →
      ⟦imp_body.abstract
        (Function.updates Δ_ctx zs (List.ofFn fun i => some (w i)))
        (hcov_imp_upd w)⟧ˢ.isSome = true)
    {𝒟_val : ZFSet.{u}} (h𝒟_empty : 𝒟_val = ∅)
    {D P : B.Term} {«Δ» : B.RenamingContext.Context}
    (Δ_fv_all : ∀ v ∈ B.fv (Term.all vs D P), («Δ» v).isSome = true)
    {T_val : ZFSet.{u}} (hT_val : T_val ∈ ⟦BType.bool⟧ᶻ)
    (hT_true : T_val = zftrue)
    (zs_len_pos : 0 < zs.length) (vs_zs_len : vs.length = zs.length)
    (hbridge : ∀ (x : ZFSet.{u}) (hx_mem : x ∈ ⟦τs.toProdl⟧ᶻ),
      let x_B := retract_castZF τ hcast x
      let hx_B_mem : x_B ∈ ⟦τ⟧ᶻ := retract_castZF_mem τ hcast hx_mem
      let x_fin : Fin vs.length → B.Dom.{u} := fun i =>
        ⟨x_B.get vs.length i, ⟨τ.get vs.length i,
          get_mem_type_of_isTuple
            (hasArity_of_mem_toZFSet τ_hasArity hx_B_mem)
            τ_hasArity hx_B_mem⟩⟩
      ∀ (w : Fin zs.length → SMT.Dom.{u})
        (_hw : ∀ i, (w i).snd.fst = τs[i]'(zs_len ▸ i.isLt) ∧
          (w i).fst ∈ ⟦τs[i]'(zs_len ▸ i.isLt)⟧ᶻ)
        (_hw_smt : Fin.foldl (zs.length - 1)
          (fun acc i => acc.pair
            (w ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩).fst)
          (w ⟨0, zs_len_pos⟩).fst = x)
        (body_val : SMT.Dom.{u}),
        ⟦imp_body.abstract
          (Function.updates Δ_ctx zs (List.ofFn fun i => some (w i)))
          (hcov_imp_upd w)⟧ˢ = some body_val →
        (body_val.fst = zftrue ↔
          (x_B ∉ 𝒟_val ∨
           ∀ (Px : ZFSet.{u}) (P_ty : BType) (hP_val : Px ∈ ⟦P_ty⟧ᶻ),
             ⟦(B.Term.abstract.go P vs «Δ» (fun v hv hvs => Δ_fv_all v
               (B.fv.mem_all (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ =
               some ⟨Px, ⟨P_ty, hP_val⟩⟩ → Px = zftrue))) :
    RDomCast
      (⟨T_val, BType.bool, hT_val⟩ : B.Dom)
      forallVal := by
  have hret := retract_forallVal_eq_zftrue_of_empty_𝒟_hasflag
    vs_nemp τ_hasArity zs_nemp zs_len hcast hcov_forall hforallVal
    hgo_cov hcov_imp_upd himp_total h𝒟_empty Δ_fv_all zs_len_pos
    vs_zs_len (retract_castZF τ hcast)
    (fun x hx => retract_castZF_mem τ hcast hx) hbridge
  apply RDom.toRDomCast
  rw [RDom]
  refine ⟨by simpa using hforallVal_type, ?_⟩
  rwa [hT_true]
