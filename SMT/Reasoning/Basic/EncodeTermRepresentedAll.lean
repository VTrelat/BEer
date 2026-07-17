import SMT.Reasoning.Basic.EncodeTermRepresentedUnion
import SMT.Reasoning.Basic.CastMembershipExact
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

/-! ## Nested helper binders

The encoder re-scopes every constant generated while encoding a quantified
body as a unary universal binder.  The two predicates below describe all
typed assignments, respectively one typed assignment, to that right-nested
sequence of binders.  Keeping this recursion independent of declaration
chunks lets the semantic argument apply equally to helpers generated by the
body and by the membership cast. -/

namespace SMT.ScopedForall

def AllAssignments.{u}
    (ps : List (SMT.𝒱 × SMTType))
    (Theta : SMT.RenamingContext.Context.{u})
    (P : SMT.RenamingContext.Context.{u} → Prop) : Prop :=
  match ps with
  | [] => P Theta
  | (v, tau) :: ps =>
      ∀ W : SMT.Dom.{u}, W.snd.fst = tau →
        AllAssignments ps (Function.update Theta v (some W)) P

def SomeAssignment.{u}
    (ps : List (SMT.𝒱 × SMTType))
    (Theta : SMT.RenamingContext.Context.{u})
    (P : SMT.RenamingContext.Context.{u} → Prop) : Prop :=
  match ps with
  | [] => P Theta
  | (v, tau) :: ps =>
      ∃ W : SMT.Dom.{u}, W.snd.fst = tau ∧
        SomeAssignment ps (Function.update Theta v (some W)) P

abbrev TermTrue.{u}
    (Theta : SMT.RenamingContext.Context.{u}) (t : SMT.Term) : Prop :=
  ∀ (hcov : SMT.RenamingContext.CoversFV Theta t) (d : SMT.Dom.{u}),
    ⟦t.abstract Theta hcov⟧ˢ = some d → d.fst = ZFSet.zftrue

abbrev TermsTrue.{u}
    (Theta : SMT.RenamingContext.Context.{u})
    (ts : List SMT.Term) : Prop :=
  ∀ t ∈ ts, TermTrue Theta t

private theorem denote_imp_eq_zffalse_of_true_false.{u}
    {p q : SMT.PHOAS.Term SMT.Dom.{u}} {Dp Dq : SMT.Dom.{u}}
    (hp : ⟦p⟧ˢ = some Dp) (hpTy : Dp.snd.fst = SMTType.bool)
    (hpTrue : Dp.fst = ZFSet.zftrue)
    (hq : ⟦q⟧ˢ = some Dq) (hqTy : Dq.snd.fst = SMTType.bool)
    (hqFalse : Dq.fst = ZFSet.zffalse) :
    ⟦p ⇒ˢ' q⟧ˢ = some ⟨ZFSet.zffalse, SMTType.bool,
      ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
  have hnq := denote_not_eq_zftrue_of_some_zffalse hq hqTy hqFalse
  have hand := denote_and_eq_zftrue_of_some_zftrue
    hp hpTy hpTrue hnq rfl rfl
  exact denote_not_eq_zffalse_of_some_zftrue hand rfl rfl

private theorem denote_imp_true_iff.{u}
    {p q : SMT.PHOAS.Term SMT.Dom.{u}} {Dp Dq Di : SMT.Dom.{u}}
    (hp : ⟦p⟧ˢ = some Dp) (hpTy : Dp.snd.fst = SMTType.bool)
    (hq : ⟦q⟧ˢ = some Dq) (hqTy : Dq.snd.fst = SMTType.bool)
    (hi : ⟦p ⇒ˢ' q⟧ˢ = some Di) :
    Di.fst = ZFSet.zftrue ↔
      Dp.fst = ZFSet.zffalse ∨ Dq.fst = ZFSet.zftrue := by
  have hpBool : Dp.fst ∈ ZFSet.𝔹 := by
    simpa [hpTy] using Dp.snd.snd
  have hqBool : Dq.fst ∈ ZFSet.𝔹 := by
    simpa [hqTy] using Dq.snd.snd
  rw [ZFSet.ZFBool.mem_𝔹_iff] at hpBool hqBool
  rcases hpBool with hpFalse | hpTrue
  · have hexact := denote_imp_eq_zftrue_of_zffalse_left
      hp hpTy hpFalse hq hqTy
    have hDi : Di = ⟨ZFSet.zftrue, SMTType.bool,
        ZFSet.ZFBool.zftrue_mem_𝔹⟩ :=
      Option.some.inj (hi.symm.trans hexact)
    rw [hDi]
    simp [hpFalse]
  · rcases hqBool with hqFalse | hqTrue
    · have hexact := denote_imp_eq_zffalse_of_true_false
        hp hpTy hpTrue hq hqTy hqFalse
      have hDi : Di = ⟨ZFSet.zffalse, SMTType.bool,
          ZFSet.ZFBool.zffalse_mem_𝔹⟩ :=
        Option.some.inj (hi.symm.trans hexact)
      rw [hDi]
      simp [hpTrue, hqFalse, ZFSet.zftrue_ne_zffalse]
    · have hexact := denote_imp_eq_zftrue_of_both_zftrue
        hp hpTy hpTrue hq hqTy hqTrue
      have hDi : Di = ⟨ZFSet.zftrue, SMTType.bool,
          ZFSet.ZFBool.zftrue_mem_𝔹⟩ :=
        Option.some.inj (hi.symm.trans hexact)
      rw [hDi]
      simp [hqTrue]

set_option maxHeartbeats 4000000 in
/-- A right-associated chain of Boolean implications is true exactly when
truth of every guard forces truth of the base. -/
theorem foldr_imp_true_iff.{u}
    (guards : List SMT.Term) (base : SMT.Term)
    {Gamma : SMT.TypeContext}
    {Theta : SMT.RenamingContext.Context.{u}}
    (htyp : Gamma ⊢ˢ guards.foldr (.imp · ·) base : SMTType.bool)
    (hcov : SMT.RenamingContext.CoversFV Theta
      (guards.foldr (.imp · ·) base))
    (hresp : SMT.RenamingContext.RespectsTypeContextOnFV Theta Gamma
      (guards.foldr (.imp · ·) base)) :
    ∃ d : SMT.Dom.{u},
      ⟦(guards.foldr (.imp · ·) base).abstract Theta hcov⟧ˢ = some d ∧
      d.snd.fst = SMTType.bool ∧
      (d.fst = ZFSet.zftrue ↔ TermsTrue Theta guards → TermTrue Theta base) := by
  induction guards generalizing Gamma with
  | nil =>
      obtain ⟨d, hd, hdTy⟩ :=
        SMT.RenamingContext.denote_exists_of_typing_fv htyp hresp hcov
      refine ⟨d, hd, hdTy, ?_⟩
      constructor
      · intro hdTrue _ hcov' d' hd'
        have hEq : d = d' := Option.some.inj (hd.symm.trans hd')
        simpa [← hEq] using hdTrue
      · intro hbase
        have hempty : TermsTrue Theta [] := by
          intro t ht
          cases ht
        exact hbase hempty hcov d hd
  | cons guard guards ih =>
      simp only [List.foldr_cons] at htyp hcov hresp ⊢
      obtain ⟨_, typ_guard, typ_tail⟩ := SMT.Typing.impE htyp
      have hcov_guard : SMT.RenamingContext.CoversFV Theta guard := by
        intro v hv
        exact hcov v (by simp only [SMT.fv, List.mem_append]; exact Or.inl hv)
      have hcov_tail : SMT.RenamingContext.CoversFV Theta
          (guards.foldr (.imp · ·) base) := by
        intro v hv
        exact hcov v (by simp only [SMT.fv, List.mem_append]; exact Or.inr hv)
      have hresp_guard : SMT.RenamingContext.RespectsTypeContextOnFV
          Theta Gamma guard := by
        intro v tau hv hlookup
        exact hresp (by simp only [SMT.fv, List.mem_append]; exact Or.inl hv) hlookup
      have hresp_tail : SMT.RenamingContext.RespectsTypeContextOnFV
          Theta Gamma (guards.foldr (.imp · ·) base) := by
        intro v tau hv hlookup
        exact hresp (by simp only [SMT.fv, List.mem_append]; exact Or.inr hv) hlookup
      obtain ⟨dg, hdg, hdgTy⟩ :=
        SMT.RenamingContext.denote_exists_of_typing_fv
          typ_guard hresp_guard hcov_guard
      obtain ⟨dt, hdt, hdtTy, iht⟩ :=
        ih typ_tail hcov_tail hresp_tail
      obtain ⟨di, hdiCore, hdiTy⟩ := denote_imp_some_bool
        hdg hdgTy hdt hdtTy
      have hdi :
          ⟦(SMT.Term.imp guard (guards.foldr (.imp · ·) base)).abstract
            Theta hcov⟧ˢ = some di := by
        simpa [SMT.Term.abstract, proof_irrel_heq] using hdiCore
      have hiIff : di.fst = ZFSet.zftrue ↔
          dg.fst = ZFSet.zffalse ∨ dt.fst = ZFSet.zftrue := by
        apply denote_imp_true_iff hdg hdgTy hdt hdtTy
        simpa [SMT.Term.abstract, proof_irrel_heq] using hdi
      refine ⟨di, hdi, hdiTy, ?_⟩
      constructor
      · intro hdiTrue hall
        have hgTrue : dg.fst = ZFSet.zftrue :=
          hall guard (List.mem_cons_self) hcov_guard dg hdg
        have htailAll : TermsTrue Theta guards := by
          intro t ht
          exact hall t (List.mem_cons_of_mem guard ht)
        rcases hiIff.mp hdiTrue with hgFalse | htTrue
        · exact absurd (hgTrue.symm.trans hgFalse)
            ZFSet.zftrue_ne_zffalse
        · exact iht.mp htTrue htailAll
      · intro hforce
        by_cases hgTrue : dg.fst = ZFSet.zftrue
        · apply hiIff.mpr
          right
          apply iht.mpr
          intro htailAll
          apply hforce
          intro t ht
          rcases List.mem_cons.mp ht with rfl | ht
          · intro hcov' d' hd'
            have hEq : dg = d' := Option.some.inj (hdg.symm.trans hd')
            simpa [← hEq] using hgTrue
          · exact htailAll t ht
        · apply hiIff.mpr
          left
          have hdgBool : dg.fst ∈ ZFSet.𝔹 := by
            simpa [hdgTy] using dg.snd.snd
          rw [ZFSet.ZFBool.mem_𝔹_iff] at hdgBool
          exact hdgBool.resolve_right hgTrue

theorem foldr_imp_eq_zftrue.{u}
    (guards : List SMT.Term) (base : SMT.Term)
    {Gamma : SMT.TypeContext}
    {Theta : SMT.RenamingContext.Context.{u}}
    (htyp : Gamma ⊢ˢ guards.foldr (.imp · ·) base : SMTType.bool)
    (hcov : SMT.RenamingContext.CoversFV Theta
      (guards.foldr (.imp · ·) base))
    (hresp : SMT.RenamingContext.RespectsTypeContextOnFV Theta Gamma
      (guards.foldr (.imp · ·) base))
    (hforce : TermsTrue Theta guards → TermTrue Theta base) :
    ⟦(guards.foldr (.imp · ·) base).abstract Theta hcov⟧ˢ =
      some ⟨ZFSet.zftrue, SMTType.bool,
        ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
  obtain ⟨d, hd, hdTy, hdIff⟩ :=
    foldr_imp_true_iff guards base htyp hcov hresp
  have hdTrue : d.fst = ZFSet.zftrue := hdIff.mpr hforce
  rcases d with ⟨D, tau, hD⟩
  dsimp at hdTy hdTrue
  subst tau
  subst D
  simpa [proof_irrel_heq] using hd

theorem foldr_imp_eq_zffalse.{u}
    (guards : List SMT.Term) (base : SMT.Term)
    {Gamma : SMT.TypeContext}
    {Theta : SMT.RenamingContext.Context.{u}}
    (htyp : Gamma ⊢ˢ guards.foldr (.imp · ·) base : SMTType.bool)
    (hcov : SMT.RenamingContext.CoversFV Theta
      (guards.foldr (.imp · ·) base))
    (hresp : SMT.RenamingContext.RespectsTypeContextOnFV Theta Gamma
      (guards.foldr (.imp · ·) base))
    (hall : TermsTrue Theta guards)
    (hbaseFalse : ∃ (hcov_base : SMT.RenamingContext.CoversFV Theta base)
      (d : SMT.Dom.{u}),
      ⟦base.abstract Theta hcov_base⟧ˢ = some d ∧
      d.fst = ZFSet.zffalse) :
    ⟦(guards.foldr (.imp · ·) base).abstract Theta hcov⟧ˢ =
      some ⟨ZFSet.zffalse, SMTType.bool,
        ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
  obtain ⟨d, hd, hdTy, hdIff⟩ :=
    foldr_imp_true_iff guards base htyp hcov hresp
  have hdNotTrue : d.fst ≠ ZFSet.zftrue := by
    intro hdTrue
    have hbaseTrue := hdIff.mp hdTrue hall
    obtain ⟨hcov_base, db, hdb, hdbFalse⟩ := hbaseFalse
    have hdbTrue := hbaseTrue hcov_base db hdb
    exact ZFSet.zftrue_ne_zffalse (hdbTrue.symm.trans hdbFalse)
  have hdBool : d.fst ∈ ZFSet.𝔹 := by
    simpa [hdTy] using d.snd.snd
  rw [ZFSet.ZFBool.mem_𝔹_iff] at hdBool
  have hdFalse : d.fst = ZFSet.zffalse := hdBool.resolve_right hdNotTrue
  rcases d with ⟨D, tau, hD⟩
  dsimp at hdTy hdFalse
  subst tau
  subst D
  simpa [proof_irrel_heq] using hd

set_option maxHeartbeats 4000000 in
/-- Substituting a list of variables by another list of variables has the same
denotation as evaluating the original term after updating the source names
with the values already assigned to the replacement names. -/
theorem substList_vars_denote_eq.{u}
    (t : SMT.Term) (vs zs : List SMT.𝒱) (ws : List SMT.Dom.{u})
    {Theta : SMT.RenamingContext.Context.{u}}
    (vs_zs_len : vs.length = zs.length)
    (vs_ws_len : vs.length = ws.length)
    (vs_nodup : vs.Nodup)
    (vs_not_bv : ∀ v ∈ vs, v ∉ SMT.bv t)
    (zs_not_bv : ∀ z ∈ zs, z ∉ SMT.bv t)
    (zs_disj_vs : ∀ z ∈ zs, z ∉ vs)
    (hzs : ∀ (i : ℕ) (hi_z : i < zs.length) (hi_w : i < ws.length),
      Theta zs[i] = some ws[i])
    (hcov_sub : SMT.RenamingContext.CoversFV Theta
      (SMT.substList vs (zs.map SMT.Term.var) t))
    (hcov_upd : SMT.RenamingContext.CoversFV
      (Function.updates Theta vs (ws.map Option.some)) t) :
    ⟦(SMT.substList vs (zs.map SMT.Term.var) t).abstract Theta hcov_sub⟧ˢ =
      ⟦t.abstract (Function.updates Theta vs (ws.map Option.some))
        hcov_upd⟧ˢ := by
  have hlen_xt : vs.length = (zs.map SMT.Term.var).length := by
    simpa using vs_zs_len
  have hts_bv_nil : ∀ s ∈ zs.map SMT.Term.var, SMT.bv s = [] := by
    intro s hs
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hs
    simp [SMT.bv]
  have hts_fv_not_bv : ∀ s ∈ zs.map SMT.Term.var,
      ∀ w ∈ SMT.fv s, w ∉ SMT.bv t := by
    intro s hs w hw
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hs
    simp only [SMT.fv, List.mem_singleton] at hw
    subst w
    exact zs_not_bv z hz
  have hts_not_none : ∀ s ∈ zs.map SMT.Term.var,
      s ≠ SMT.Term.none := by
    intro s hs
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hs
    intro h
    cases h
  have hts_fv_disj : ∀ s ∈ zs.map SMT.Term.var,
      ∀ w ∈ SMT.fv s, w ∉ vs := by
    intro s hs w hw
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hs
    simp only [SMT.fv, List.mem_singleton] at hw
    subst w
    exact zs_disj_vs z hz
  have hts_den : ∀ (i : ℕ) (hi_v : i < vs.length)
      (hi_t : i < (zs.map SMT.Term.var).length) (hi_w : i < ws.length),
      ∃ hcov_var : SMT.RenamingContext.CoversFV Theta
          (zs.map SMT.Term.var)[i],
        ⟦(zs.map SMT.Term.var)[i].abstract Theta hcov_var⟧ˢ =
          some ws[i] := by
    intro i hi_v hi_t hi_w
    have hi_z : i < zs.length := by simpa using hi_t
    have hlookup : Theta zs[i] = some ws[i] := hzs i hi_z hi_w
    have hcov_var' : SMT.RenamingContext.CoversFV Theta
        (SMT.Term.var zs[i]) := by
      intro z hz
      simp only [SMT.fv, List.mem_singleton] at hz
      subst z
      rw [hlookup]
      rfl
    let hcov_var : SMT.RenamingContext.CoversFV Theta
        (zs.map SMT.Term.var)[i] := by
      simpa only [List.getElem_map] using hcov_var'
    refine ⟨hcov_var, ?_⟩
    have hden_var :
        ⟦(SMT.Term.var zs[i]).abstract Theta hcov_var'⟧ˢ = some ws[i] := by
      rw [SMT.Term.abstract, SMT.denote]
      exact congrArg some (Option.get_of_eq_some _ hlookup)
    simpa only [List.getElem_map, proof_irrel_heq] using hden_var
  exact SMT.RenamingContext.abstract_substList_denote
    t vs (zs.map SMT.Term.var) ws hlen_xt vs_ws_len vs_nodup
    vs_not_bv hts_bv_nil hts_fv_not_bv hts_not_none hts_fv_disj
    hts_den hcov_sub hcov_upd

/-- A satisfying assignment for original helper specifications remains a
satisfying assignment after the encoder's `vs ↦ zs` substitution. -/
theorem TermsTrue.of_specBodies_subst.{u}
    {Dlt : SMT.Chunk} {Gamma : SMT.TypeContext}
    (vs zs : List SMT.𝒱) (ws : List SMT.Dom.{u})
    {Theta : SMT.RenamingContext.Context.{u}}
    (vs_zs_len : vs.length = zs.length)
    (vs_ws_len : vs.length = ws.length)
    (vs_nodup : vs.Nodup)
    (zs_disj_vs : ∀ z ∈ zs, z ∉ vs)
    (hbv : ∀ b ∈ specBodies Dlt,
      (∀ v ∈ vs, v ∉ SMT.bv b) ∧
      (∀ z ∈ zs, z ∉ SMT.bv b))
    (hzs : ∀ (i : ℕ) (hi_z : i < zs.length) (hi_w : i < ws.length),
      Theta zs[i] = some ws[i])
    (hspec : SpecBodiesTrue
      (Function.updates Theta vs (ws.map Option.some)) Gamma Dlt) :
    TermsTrue Theta
      ((specBodies Dlt).map (SMT.substList vs (zs.map SMT.Term.var))) := by
  intro t ht
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ht
  intro hcov_sub d hden_sub
  obtain ⟨hcov_b, db, _, hden_b, _, hdb_true⟩ := hspec b hb
  have heq := substList_vars_denote_eq b vs zs ws
    vs_zs_len vs_ws_len vs_nodup (hbv b hb).1 (hbv b hb).2
    zs_disj_vs hzs hcov_sub hcov_b
  have hden_db := heq.trans hden_b
  have hEq : db = d := Option.some.inj (hden_db.symm.trans hden_sub)
  simpa [← hEq] using hdb_true

private theorem singleton_update_eq_insert
    (Gamma : SMT.TypeContext) (v : SMT.𝒱) (tau : SMTType) :
    Gamma.update [v] [tau] rfl = Gamma.insert v tau := by
  simp only [SMT.TypeContext.update, List.length_cons, List.length_nil,
    zero_add, Fin.foldl_succ, Nat.reduceAdd, Fin.cast_eq_self,
    Fin.getElem_fin, Fin.val_eq_zero, List.getElem_cons_zero,
    Fin.foldl_zero]

/-- Re-scope a declaration trace as the encoder's right-nested sequence of
unary universal helper binders.  Freshness is recovered from the exact trace;
bound-variable freshness follows from typing in the final operational
context, which contains every declared helper. -/
theorem foldr_decl_forall_typing
    (Dlt : SMT.Chunk) (inner : SMT.Term)
    {Gamma GammaOp : SMT.TypeContext}
    (htrace : DeclarationContextTrace Gamma Dlt GammaOp)
    (hinner : GammaOp ⊢ˢ inner : SMTType.bool) :
    Gamma ⊢ˢ (declBinders Dlt).foldr
      (fun p t => SMT.Term.forall [p.1] [p.2] t) inner :
        SMTType.bool := by
  induction Dlt generalizing Gamma with
  | nil =>
      change GammaOp = Gamma at htrace
      subst GammaOp
      exact hinner
  | cons i D ih =>
      cases i with
      | declare_const v tau =>
          obtain ⟨hv, htail⟩ := htrace
          have htyp_tail := ih htail
          simp only [declBinders, List.filterMap_cons, List.foldr_cons]
          refine SMT.Typing.forall Gamma [v] [tau] _ ?_ ?_ (by simp) rfl ?_
          · simpa using hv
          · intro w hw hbv
            simp only [List.mem_singleton] at hw
            subst w
            exact SMT.Typing.bv_notMem_context htyp_tail v hbv (by simp)
          · rwa [singleton_update_eq_insert]
      | define_fun v tau sigma body =>
          simpa [declBinders] using ih htrace
      | define_const v tau body =>
          simpa [declBinders] using ih htrace
      | assert body =>
          simpa [declBinders] using ih htrace
      | push n =>
          simpa [declBinders] using ih htrace
      | pop n =>
          simpa [declBinders] using ih htrace
      | check_sat =>
          simpa [declBinders] using ih htrace

/-- Type a right-associated chain of Boolean guard implications. -/
theorem foldr_imp_typing
    (guards : List SMT.Term) (base : SMT.Term)
    {Gamma : SMT.TypeContext}
    (hguards : ∀ g ∈ guards, Gamma ⊢ˢ g : SMTType.bool)
    (hbase : Gamma ⊢ˢ base : SMTType.bool) :
    Gamma ⊢ˢ guards.foldr SMT.Term.imp base : SMTType.bool := by
  induction guards with
  | nil => exact hbase
  | cons g guards ih =>
      simp only [List.foldr_cons]
      exact SMT.Typing.imp Gamma g _
        (hguards g (List.mem_cons_self ..))
        (ih (fun h hh => hguards h (List.mem_cons_of_mem _ hh)))

private theorem tail_coverage.{u}
    {Theta : SMT.RenamingContext.Context.{u}}
    {v : SMT.𝒱} {tau : SMTType} {tail : SMT.Term}
    (hcov : SMT.RenamingContext.CoversFV Theta
      (SMT.Term.forall [v] [tau] tail)) :
    ∀ W : SMT.Dom.{u},
      SMT.RenamingContext.CoversFV
        (Function.update Theta v (some W)) tail := by
  intro W x hx
  by_cases hxv : x = v
  · subst x
    simp
  · rw [Function.update_of_ne hxv]
    exact hcov x (SMT.fv.mem_forall ⟨hx, by simpa using hxv⟩)

private theorem tail_respects.{u}
    {Gamma : SMT.TypeContext}
    {Theta : SMT.RenamingContext.Context.{u}}
    {v : SMT.𝒱} {tau : SMTType} {tail : SMT.Term}
    (hresp : SMT.RenamingContext.RespectsTypeContextOnFV Theta Gamma
      (SMT.Term.forall [v] [tau] tail))
    (W : SMT.Dom.{u}) (hW : W.snd.fst = tau) :
    SMT.RenamingContext.RespectsTypeContextOnFV
      (Function.update Theta v (some W))
      (Gamma.update [v] [tau] rfl) tail := by
  rw [singleton_update_eq_insert]
  intro x sigma hx hlookup
  by_cases hxv : x = v
  · subst x
    rw [AList.lookup_insert] at hlookup
    cases hlookup
    exact ⟨W, by simp, hW⟩
  · rw [AList.lookup_insert_ne hxv] at hlookup
    obtain ⟨d, hd, hdty⟩ :=
      hresp (SMT.fv.mem_forall ⟨hx, by simpa using hxv⟩) hlookup
    exact ⟨d, by simpa [Function.update_of_ne hxv] using hd, hdty⟩

set_option maxHeartbeats 4000000 in
/-- If the innermost body is true for every typed assignment to a sequence of
unary helper binders, the right-nested universal closure denotes `true`. -/
theorem foldr_eq_zftrue.{u}
    (ps : List (SMT.𝒱 × SMTType))
    (inner : SMT.Term)
    {Gamma : SMT.TypeContext}
    {Theta : SMT.RenamingContext.Context.{u}}
    (htyp : Gamma ⊢ˢ ps.foldr
      (fun p t => SMT.Term.forall [p.1] [p.2] t) inner :
        SMTType.bool)
    (hcov : SMT.RenamingContext.CoversFV Theta
      (ps.foldr (fun p t => SMT.Term.forall [p.1] [p.2] t) inner))
    (hresp : SMT.RenamingContext.RespectsTypeContextOnFV Theta Gamma
      (ps.foldr (fun p t => SMT.Term.forall [p.1] [p.2] t) inner))
    (hleaf : AllAssignments ps Theta (fun Theta' =>
      ∀ hcov_inner : SMT.RenamingContext.CoversFV Theta' inner,
        ⟦inner.abstract Theta' hcov_inner⟧ˢ =
          some ⟨ZFSet.zftrue, SMTType.bool,
            ZFSet.ZFBool.zftrue_mem_𝔹⟩)) :
    ⟦(ps.foldr (fun p t => SMT.Term.forall [p.1] [p.2] t) inner).abstract
      Theta hcov⟧ˢ =
        some ⟨ZFSet.zftrue, SMTType.bool,
          ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
  induction ps generalizing Gamma Theta with
  | nil =>
      exact hleaf hcov
  | cons p ps ih =>
      obtain ⟨v, tau⟩ := p
      simp only [List.foldr_cons] at htyp hcov hresp ⊢
      obtain ⟨_, _, _, _, _, htyp_tail⟩ := SMT.Typing.forallE htyp
      have hcov_tail := tail_coverage hcov
      have hgo : ∀ x ∈ SMT.fv
          (ps.foldr (fun p t => SMT.Term.forall [p.1] [p.2] t) inner),
          x ∉ [v] → (Theta x).isSome = true := by
        intro x hx hxv
        exact hcov x (SMT.fv.mem_forall ⟨hx, hxv⟩)
      have hrec : ∀ (W : SMT.Dom.{u}), W.snd.fst = tau →
          ⟦(ps.foldr (fun p t => SMT.Term.forall [p.1] [p.2] t) inner).abstract
            (Function.update Theta v (some W)) (hcov_tail W)⟧ˢ =
              some ⟨ZFSet.zftrue, SMTType.bool,
                ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
        intro W hW
        exact ih htyp_tail (hcov_tail W) (tail_respects hresp W hW)
          (hleaf W hW)
      exact funUnaryForallEqZftrue hcov hgo hcov_tail
        (fun W hW => by rw [hrec W hW]; simp)
        (fun W hW D hD => by
          have hEq := Option.some.inj ((hrec W hW).symm.trans hD)
          rw [← hEq]
          )
        (fun W hW => ⟨_, hrec W hW, rfl⟩)

set_option maxHeartbeats 4000000 in
/-- If one typed assignment makes the innermost body false, the right-nested
universal closure denotes `false`.  Totality at all other assignments comes
from the typing theorem, independently of the semantic counterexample. -/
theorem foldr_eq_zffalse.{u}
    (ps : List (SMT.𝒱 × SMTType))
    (inner : SMT.Term)
    {Gamma : SMT.TypeContext}
    {Theta : SMT.RenamingContext.Context.{u}}
    (htyp : Gamma ⊢ˢ ps.foldr
      (fun p t => SMT.Term.forall [p.1] [p.2] t) inner :
        SMTType.bool)
    (hcov : SMT.RenamingContext.CoversFV Theta
      (ps.foldr (fun p t => SMT.Term.forall [p.1] [p.2] t) inner))
    (hresp : SMT.RenamingContext.RespectsTypeContextOnFV Theta Gamma
      (ps.foldr (fun p t => SMT.Term.forall [p.1] [p.2] t) inner))
    (hleaf : SomeAssignment ps Theta (fun Theta' =>
      ∀ hcov_inner : SMT.RenamingContext.CoversFV Theta' inner,
        ⟦inner.abstract Theta' hcov_inner⟧ˢ =
          some ⟨ZFSet.zffalse, SMTType.bool,
            ZFSet.ZFBool.zffalse_mem_𝔹⟩)) :
    ⟦(ps.foldr (fun p t => SMT.Term.forall [p.1] [p.2] t) inner).abstract
      Theta hcov⟧ˢ =
        some ⟨ZFSet.zffalse, SMTType.bool,
          ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
  induction ps generalizing Gamma Theta with
  | nil =>
      exact hleaf hcov
  | cons p ps ih =>
      obtain ⟨v, tau⟩ := p
      simp only [List.foldr_cons] at htyp hcov hresp ⊢
      obtain ⟨_, _, _, _, _, htyp_tail⟩ := SMT.Typing.forallE htyp
      have hcov_tail := tail_coverage hcov
      have hgo : ∀ x ∈ SMT.fv
          (ps.foldr (fun p t => SMT.Term.forall [p.1] [p.2] t) inner),
          x ∉ [v] → (Theta x).isSome = true := by
        intro x hx hxv
        exact hcov x (SMT.fv.mem_forall ⟨hx, hxv⟩)
      have htotal : ∀ (W : SMT.Dom.{u}), W.snd.fst = tau →
          ⟦(ps.foldr (fun p t => SMT.Term.forall [p.1] [p.2] t) inner).abstract
            (Function.update Theta v (some W)) (hcov_tail W)⟧ˢ.isSome = true := by
        intro W hW
        obtain ⟨d, hd, _⟩ :=
          SMT.RenamingContext.denote_exists_of_typing_fv htyp_tail
            (tail_respects hresp W hW) (hcov_tail W)
        rw [hd]
        rfl
      have htype : ∀ (W : SMT.Dom.{u}), W.snd.fst = tau →
          ∀ d : SMT.Dom.{u},
            ⟦(ps.foldr (fun p t => SMT.Term.forall [p.1] [p.2] t) inner).abstract
              (Function.update Theta v (some W)) (hcov_tail W)⟧ˢ = some d →
            d.snd.fst = SMTType.bool := by
        intro W hW d hd
        exact SMT.RenamingContext.denote_type_of_typing_fv htyp_tail
          (tail_respects hresp W hW) (hcov_tail W) hd
      obtain ⟨W, hW, hleaf_tail⟩ := hleaf
      have hfalse := ih htyp_tail (hcov_tail W)
        (tail_respects hresp W hW) hleaf_tail
      exact funUnaryForallEqZffalse htyp hcov hgo hcov_tail
        htotal htype W hW ⟨_, hfalse, rfl⟩

end SMT.ScopedForall
