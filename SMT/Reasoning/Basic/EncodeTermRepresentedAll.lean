import SMT.Reasoning.Basic.EncodeTermRepresentedUnion
import SMT.Reasoning.Basic.EncodeTermRepresentedMem
import SMT.Reasoning.Basic.CastMembershipExact
import SMT.Reasoning.Basic.AbstractSubstDenote
import SMT.Reasoning.Basic.EncodeTermRepresentedBinders
import SMT.Reasoning.Representation

open Std.Do B SMT ZFSet

/-! # Representation-aware universal quantification -/

/-- Extensionality for source semantic values, with proof irrelevance for
the membership witness. -/
lemma B.RenamingContext.Dom_ext' {z1 z2 : ZFSet} {tau1 tau2 : BType}
    {h1 : z1 ∈ ⟦tau1⟧ᶻ} {h2 : z2 ∈ ⟦tau2⟧ᶻ}
    (hz : z1 = z2) (htau : tau1 = tau2) :
    (⟨z1, tau1, h1⟩ : B.Dom) = ⟨z2, tau2, h2⟩ := by
  subst z2
  subst tau2
  rfl

/-- The two dependent-pair patterns used by the source semantics and the
forall bridge project the same value from an optional B denotation. -/
@[simp] theorem optionBDom_value_pattern.{u}
    (d : Option B.Dom.{u}) :
    (match d with
      | some ⟨x, _⟩ => x
      | none => ZFSet.zffalse) =
    (match d with
      | some ⟨x, ⟨_, _⟩⟩ => x
      | none => ZFSet.zffalse) := by
  cases d with
  | none => rfl
  | some d => rcases d with ⟨x, tau, hx⟩; rfl

/-- A binder using a type propositionally equal to the canonical SMT type is
admissible.  Keeping the source type as a variable lets dependent elimination
transport both the cast witness and the admissibility predicate together. -/
theorem BinderCastAdmissible.of_eq_canonical.{u}
    {tau : BType} {sigma : SMTType} {D : ZFSet.{u}}
    (hsigma : sigma = tau.toSMTType)
    (hD : D ∈ ⟦BType.set tau⟧ᶻ)
    (hcast : sigma ⊑ tau.toSMTType) :
    BinderCastAdmissible tau sigma hcast.toCastPath D := by
  subst sigma
  rw [castPath.eq_reflexive hcast.toCastPath]
  exact BinderCastAdmissible.reflexive tau hD

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
    (τ_hasArity : (αs.reduce (· ×ᴮ ·) αs_nemp).hasArity vs.length)
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
      ⟨X.get vs.length i, (αs.reduce (· ×ᴮ ·) αs_nemp).get vs.length i,
        get_mem_type_of_isTuple
          (hasArity_of_mem_toZFSet τ_hasArity hX) τ_hasArity hX⟩
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
    have hsource :
        (⟨X.get vs.length i,
          (αs.reduce (· ×ᴮ ·) αs_nemp).get vs.length i,
          get_mem_type_of_isTuple
            (hasArity_of_mem_toZFSet τ_hasArity hX)
            τ_hasArity hX⟩ : B.Dom) =
        (⟨X.get αs.length jα, αs[jα],
          BType.mem_get_of_mem_reduce_toZFSet αs_nemp hX⟩ : B.Dom) := by
      have hval : X.get vs.length i =
          X.get αs.length (Fin.cast vs_αs_len i) :=
        ZFSet.get_cast vs_αs_len i
      have htype := BType.get_reduce αs_nemp vs_αs_len i
      exact B.RenamingContext.Dom_ext' hval htype
    rw [hsource]
    simpa [jα, jσ] using hcomp

open Classical in
/-- Every supported tuple representation has a concrete typed assignment.
Choosing the default target tuple and retracting it supplies the source tuple;
the resulting pair is supported by construction.  This witness is used only
to run the body encoder once—the scoped contract handles all later quantified
assignments. -/
theorem RDomCastSupported.default_tuple_witness.{u}
    {alphas : List BType} {sigmas : List SMTType}
    (alphas_nemp : alphas ≠ [])
    (hs : List.Forall₂ BType.SupportedSMT alphas sigmas) :
    ∃ (X Y : ZFSet.{u})
      (hX : X ∈ ⟦alphas.reduce (· ×ᴮ ·) alphas_nemp⟧ᶻ)
      (hY : Y ∈ ⟦sigmas.toProdl⟧ᶻ),
      RDomCastSupported
        (⟨X, alphas.reduce (· ×ᴮ ·) alphas_nemp, hX⟩ : B.Dom)
        (⟨Y, sigmas.toProdl, hY⟩ : SMT.Dom) := by
  let supported := BType.SupportedSMT.reduce_toProdl hs alphas_nemp
  let hle : sigmas.toProdl ⊑
      (alphas.reduce (· ×ᴮ ·) alphas_nemp).toSMTType :=
    castable?_of_castPath supported.toCanonicalCastPath
  let Y : ZFSet.{u} := sigmas.toProdl.defaultZFSet
  have hY : Y ∈ ⟦sigmas.toProdl⟧ᶻ :=
    SMTType.mem_toZFSet_of_defaultZFSet
  let X := retract_castZF
    (alphas.reduce (· ×ᴮ ·) alphas_nemp) hle Y
  have hX : X ∈ ⟦alphas.reduce (· ×ᴮ ·) alphas_nemp⟧ᶻ :=
    retract_castZF_mem _ hle hY
  have hrel : RDomCast
      (⟨X, alphas.reduce (· ×ᴮ ·) alphas_nemp, hX⟩ : B.Dom)
      (⟨Y, sigmas.toProdl, hY⟩ : SMT.Dom) := by
    refine ⟨hle.toCastPath, ?_⟩
    rfl
  exact ⟨X, Y, hX, hY,
    ⟨RDomCast.toRDomCastAdmissible_of_supported hrel supported,
      supported⟩⟩

/-- Folding the component projections of a nonempty tuple reconstructs the
tuple.  This public form is shared by the representation-aware quantifier
proof's operational and alternative-valuation witnesses. -/
theorem ZFSet.foldl_get_of_hasArity_rep.{u} {m : ℕ} {x : ZFSet.{u}}
    (hx : x.hasArity (m + 1)) :
    Fin.foldl m
      (fun (acc : ZFSet.{u}) (i : Fin m) =>
        acc.pair (x.get (m + 1)
          ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩))
      (x.get (m + 1) ⟨0, Nat.zero_lt_succ m⟩) = x := by
  induction m generalizing x with
  | zero => simp [Fin.foldl_zero, ZFSet.get]
  | succ k ih =>
      simp only [ZFSet.hasArity, if_false_right] at hx
      obtain ⟨⟨a, b, rfl⟩, a_hasArity⟩ := hx
      rw [ZFSet.π₁_pair] at a_hasArity
      rw [Fin.foldl_succ_last]
      have h_last : (a.pair b).get (k + 2)
          ⟨(Fin.last k).val + 1, by omega⟩ = b := by
        simp only [ZFSet.get]
        rw [dif_pos]
        · exact ZFSet.π₂_pair _ _
        · simp [Fin.ext_iff, Fin.val_last]
      have h_init : (a.pair b).get (k + 2) ⟨0, by omega⟩ =
          a.get (k + 1) ⟨0, by omega⟩ := by
        simp only [ZFSet.get]
        rw [dif_neg]
        · rw [ZFSet.π₁_pair]
          rfl
        · simp [Fin.ext_iff, Fin.val_last]
      have h_step : ∀ i : Fin k,
          (a.pair b).get (k + 2)
            ⟨i.castSucc.val + 1, by omega⟩ =
          a.get (k + 1) ⟨i.val + 1, by omega⟩ := by
        intro ⟨i, hi⟩
        simp only [ZFSet.get, Fin.castSucc_mk]
        rw [dif_neg]
        · rw [ZFSet.π₁_pair]
          rfl
        · simp [Fin.ext_iff, Fin.val_last]
          omega
      have hih := ih a_hasArity
      have heq : Fin.foldl k
          (fun (acc : ZFSet.{u}) (i : Fin k) =>
            acc.pair ((a.pair b).get (k + 2)
              ⟨i.castSucc.val + 1, by omega⟩))
          ((a.pair b).get (k + 2) ⟨0, by omega⟩) = a := by
        rw [h_init]
        have hfn : (fun (acc : ZFSet.{u}) (i : Fin k) =>
            acc.pair ((a.pair b).get (k + 2)
              ⟨i.castSucc.val + 1, by omega⟩)) =
            (fun (acc : ZFSet.{u}) (i : Fin k) =>
              acc.pair (a.get (k + 1)
                ⟨i.val + 1, by omega⟩)) := by
          funext acc i
          rw [h_step]
        rw [hfn]
        exact hih
      rw [heq, h_last]

open Classical B in
/-- Obtain one well-typed body denotation from a successful source universal
denotation.  A nonempty domain supplies an actual quantified tuple; for the
empty domain the body is semantically irrelevant, so well-definedness and
typing supply a default tuple witness.  This is the witness used for the one
operational body-encoding run; quantified correctness later ranges over every
assignment through the scoped induction hypothesis. -/
theorem all_body_denotation_witness.{u}
    {vs : List B.𝒱} (vs_nemp : vs ≠ []) (vs_nodup : vs.Nodup)
    {αs : List BType} {τ : BType}
    (τ_hasArity : τ.hasArity vs.length)
    {Ectx : B.TypeContext} {D P : B.Term}
    (typ_D : Ectx ⊢ᴮ D : BType.set τ)
    (typ_P : (vs.zipToAList αs ∪ Ectx) ⊢ᴮ P : BType.bool)
    (wd_P : B.Term.WellDefined.{u} P)
    {Xi : B.RenamingContext.Context.{u}}
    (Δ_fv_all : ∀ v ∈ B.fv (B.Term.all vs D P), (Xi v).isSome = true)
    (wf : B.RenWF Ectx Xi)
    (P_renwf : ∀ (f : Fin vs.length → B.Dom.{u}),
      (∀ i, (f i).snd.fst = τ.get vs.length i) →
      B.RenWF (vs.zipToAList αs ∪ Ectx)
        (Function.updates Xi vs (List.ofFn fun i => some (f i))))
    {T : ZFSet.{u}} {hT : T ∈ ⟦BType.bool⟧ᶻ}
    (hden_all : ⟦(B.Term.all vs D P).abstract Xi Δ_fv_all⟧ᴮ =
      some ⟨T, ⟨BType.bool, hT⟩⟩) :
    ∃ (f : Fin vs.length → B.Dom.{u}),
      (∀ i, (f i).snd.fst = τ.get vs.length i ∧
        (f i).fst ∈ ⟦τ.get vs.length i⟧ᶻ) ∧
      ∃ (Pval : ZFSet.{u}) (hPval : Pval ∈ ⟦BType.bool⟧ᶻ),
        ⟦(B.Term.abstract.go P vs Xi
          (fun v hv hvs => Δ_fv_all v
            (B.fv.mem_all (.inr ⟨hv, hvs⟩)))).uncurry f⟧ᴮ =
          some ⟨Pval, ⟨BType.bool, hPval⟩⟩ := by
  have hinv := hden_all
  simp only [B.Term.abstract] at hinv
  unfold B.denote at hinv
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hinv
  obtain ⟨⟨Dval, Dty, hDval⟩, hden_D_raw, rest⟩ := hinv
  have Δ_fv_D : ∀ v ∈ B.fv D, (Xi v).isSome = true :=
    fun v hv => Δ_fv_all v (B.fv.mem_all (.inl hv))
  have hden_D : ⟦D.abstract Xi Δ_fv_D⟧ᴮ =
      some ⟨Dval, ⟨Dty, hDval⟩⟩ := by
    convert hden_D_raw using 2
  have hDty : Dty = BType.set τ := by
    exact (denote_welltyped_eq
      (t := D.abstract Xi Δ_fv_D)
      ⟨_, WFTC.of_abstract, BType.set τ,
        by convert Typing.of_abstract Δ_fv_D typ_D⟩
      hden_D).symm
  subst Dty
  simp only at rest
  rw [dif_pos τ_hasArity] at rest
  split_ifs at rest with hden_P htyp_P_det hD_empty
  · let f : Fin vs.length → B.Dom.{u} := fun i =>
      ⟨(τ.get vs.length i).defaultZFSet,
        ⟨τ.get vs.length i, BType.mem_toZFSet_of_defaultZFSet⟩⟩
    have hf : ∀ i, (f i).snd.fst = τ.get vs.length i ∧
        (f i).fst ∈ ⟦τ.get vs.length i⟧ᶻ :=
      fun i => ⟨rfl, (f i).snd.snd⟩
    let Δext := Function.updates Xi vs
      (List.ofFn fun i => some (f i))
    have Δ_fv_P : ∀ v ∈ B.fv P, (Δext v).isSome = true := by
      intro v hv
      show (Function.updates Xi vs _ v).isSome = true
      rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup]
      split_ifs with hvs
      · simp [List.getElem_ofFn]
      · exact Δ_fv_all v (B.fv.mem_all (.inr ⟨hv, hvs⟩))
    have hwf_P := P_renwf f (fun i => (hf i).1)
    obtain ⟨Pval, hPval, hPden⟩ := B.denote_exists_of_typing typ_P
      Δext Δ_fv_P (@WFTC.wf _ WFTC.of_abstract)
      (wd_P.toPHOAS Δext Δ_fv_P)
    refine ⟨f, hf, Pval, hPval, ?_⟩
    rw [denote_term_abstract_go_eq_term_abstract vs_nodup vs_nemp f Δ_fv_P]
    exact hPden
  · have hD_nonempty : Dval.Nonempty :=
      Dval.eq_empty_or_nonempty.resolve_left hD_empty
    obtain ⟨x, hx⟩ := hD_nonempty
    have hD_sub : Dval ⊆ ⟦τ⟧ᶻ := by
      rwa [BType.toZFSet, ZFSet.mem_powerset] at hDval
    have hx_ty : x ∈ ⟦τ⟧ᶻ := hD_sub hx
    have hx_arity : x.hasArity vs.length :=
      hasArity_of_mem_toZFSet τ_hasArity hx_ty
    let f : Fin vs.length → B.Dom.{u} := fun i =>
      ⟨x.get vs.length i, τ.get vs.length i,
        get_mem_type_of_isTuple hx_arity τ_hasArity hx_ty⟩
    have hf : ∀ i, (f i).snd.fst = τ.get vs.length i ∧
        (f i).fst ∈ ⟦τ.get vs.length i⟧ᶻ :=
      fun i => ⟨rfl, (f i).snd.snd⟩
    have htuple : ZFSet.ofFinDom f = x :=
      ZFSet.ofFinDom_get (List.length_pos_iff.mpr vs_nemp)
        (fun _ => get_mem_type_of_isTuple hx_arity τ_hasArity hx_ty)
        hx_arity τ_hasArity
    have hP_some := hden_P hf (htuple ▸ hx)
    obtain ⟨⟨Pval, Pty, hPval⟩, hPden⟩ :=
      Option.isSome_iff_exists.mp hP_some
    let Δext := Function.updates Xi vs
      (List.ofFn fun i => some (f i))
    have Δ_fv_P : ∀ v ∈ B.fv P, (Δext v).isSome = true := by
      intro v hv
      show (Function.updates Xi vs _ v).isSome = true
      rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup]
      split_ifs with hvs
      · simp [List.getElem_ofFn]
      · exact Δ_fv_all v (B.fv.mem_all (.inr ⟨hv, hvs⟩))
    have hPden_abs : ⟦P.abstract Δext Δ_fv_P⟧ᴮ =
        some ⟨Pval, ⟨Pty, hPval⟩⟩ := by
      rw [← denote_term_abstract_go_eq_term_abstract
        vs_nodup vs_nemp f Δ_fv_P]
      convert hPden using 2
    have hwf_P := P_renwf f (fun i => (hf i).1)
    have hPty : Pty = BType.bool := by
      exact (denote_welltyped_eq
        (t := P.abstract Δext Δ_fv_P)
        ⟨_, WFTC.of_abstract, BType.bool,
          by convert Typing.of_abstract Δ_fv_P typ_P⟩
        hPden_abs).symm
    subst Pty
    exact ⟨f, hf, Pval, hPval, hPden⟩

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

theorem AllAssignments.mono.{u}
    {ps : List (SMT.𝒱 × SMTType)}
    {Theta : SMT.RenamingContext.Context.{u}}
    {P Q : SMT.RenamingContext.Context.{u} → Prop}
    (h : AllAssignments ps Theta P)
    (hPQ : ∀ Theta', P Theta' → Q Theta') :
    AllAssignments ps Theta Q := by
  induction ps generalizing Theta P Q with
  | nil => exact hPQ Theta h
  | cons p ps ih =>
      obtain ⟨v, tau⟩ := p
      intro W hW
      exact ih (h W hW) hPQ

theorem SomeAssignment.mono.{u}
    {ps : List (SMT.𝒱 × SMTType)}
    {Theta : SMT.RenamingContext.Context.{u}}
    {P Q : SMT.RenamingContext.Context.{u} → Prop}
    (h : SomeAssignment ps Theta P)
    (hPQ : ∀ Theta', P Theta' → Q Theta') :
    SomeAssignment ps Theta Q := by
  induction ps generalizing Theta P Q with
  | nil => exact hPQ Theta h
  | cons p ps ih =>
      obtain ⟨v, tau⟩ := p
      obtain ⟨W, hW, htail⟩ := h
      exact ⟨W, hW, ih htail hPQ⟩

/-- Reify a semantic model as one concrete assignment to a list of distinct
helper binders.  Helpers used by the leaf take their model values; unused
helpers take the canonical default of their declared type. -/
theorem SomeAssignment.of_model.{u}
    (ps : List (SMT.𝒱 × SMTType))
    {Theta ThetaModel : SMT.RenamingContext.Context.{u}}
    (inner : SMT.Term) {Gamma : SMT.TypeContext}
    (hnodup : (ps.map Prod.fst).Nodup)
    (hlookup : ∀ p ∈ ps, Gamma.lookup p.1 = some p.2)
    (hresp : SMT.RenamingContext.RespectsTypeContextOnFV
      ThetaModel Gamma inner)
    (houtside : ∀ x ∈ SMT.fv inner, x ∉ ps.map Prod.fst →
      Theta x = ThetaModel x) :
    SomeAssignment ps Theta (fun Theta' =>
      SMT.RenamingContext.AgreesOnFV Theta' ThetaModel inner) := by
  induction ps generalizing Theta with
  | nil =>
      intro x hx
      exact houtside x hx (by simp)
  | cons p ps ih =>
      obtain ⟨v, tau⟩ := p
      simp only [List.map_cons, List.nodup_cons] at hnodup
      have hlookup_tail : ∀ q ∈ ps,
          Gamma.lookup q.1 = some q.2 := by
        intro q hq
        exact hlookup q (List.mem_cons_of_mem (v, tau) hq)
      by_cases hv : v ∈ SMT.fv inner
      · obtain ⟨W, hW, hWtype⟩ := hresp hv <|
          hlookup (v, tau) (List.mem_cons_self)
        refine ⟨W, hWtype, ih hnodup.2 hlookup_tail ?_⟩
        intro x hx hx_tail
        by_cases hxv : x = v
        · subst x
          simpa [Function.update] using hW.symm
        · rw [Function.update_of_ne hxv]
          apply houtside x hx
          simpa [hxv, hx_tail]
      · let W : SMT.Dom.{u} :=
          ⟨tau.defaultZFSet, tau,
            SMTType.mem_toZFSet_of_defaultZFSet⟩
        refine ⟨W, rfl, ih hnodup.2 hlookup_tail ?_⟩
        intro x hx hx_tail
        by_cases hxv : x = v
        · subst x
          exact (hv hx).elim
        · rw [Function.update_of_ne hxv]
          apply houtside x hx
          simpa [hxv, hx_tail]

theorem SomeAssignment.and_all.{u}
    {ps : List (SMT.𝒱 × SMTType)}
    {Theta : SMT.RenamingContext.Context.{u}}
    {P Q : SMT.RenamingContext.Context.{u} → Prop}
    (hsome : SomeAssignment ps Theta P)
    (hall : AllAssignments ps Theta Q) :
    SomeAssignment ps Theta (fun Theta' => P Theta' ∧ Q Theta') := by
  induction ps generalizing Theta with
  | nil => exact ⟨hsome, hall⟩
  | cons p ps ih =>
      obtain ⟨v, tau⟩ := p
      obtain ⟨W, hW, htail⟩ := hsome
      exact ⟨W, hW, ih htail (hall W hW)⟩

theorem AllAssignments.and.{u}
    {ps : List (SMT.𝒱 × SMTType)}
    {Theta : SMT.RenamingContext.Context.{u}}
    {P Q : SMT.RenamingContext.Context.{u} → Prop}
    (hP : AllAssignments ps Theta P)
    (hQ : AllAssignments ps Theta Q) :
    AllAssignments ps Theta (fun Theta' => P Theta' ∧ Q Theta') := by
  induction ps generalizing Theta P Q with
  | nil => exact ⟨hP, hQ⟩
  | cons p ps ih =>
      obtain ⟨v, tau⟩ := p
      intro W hW
      exact ih (hP W hW) (hQ W hW)

/-- Assignments to names disjoint from `xs` preserve every value on `xs`. -/
theorem AllAssignments.preserves.{u}
    (ps : List (SMT.𝒱 × SMTType))
    {Theta : SMT.RenamingContext.Context.{u}} (xs : List SMT.𝒱)
    (hdisj : ∀ p ∈ ps, p.1 ∉ xs) :
    AllAssignments ps Theta (fun Theta' =>
      ∀ x ∈ xs, Theta' x = Theta x) := by
  induction ps generalizing Theta with
  | nil => exact fun _ _ => rfl
  | cons p ps ih =>
      obtain ⟨v, tau⟩ := p
      intro W hW
      have hv : v ∉ xs := hdisj (v, tau) (List.mem_cons_self)
      have htail := ih (Theta := Function.update Theta v (some W))
        (fun q hq => hdisj q (List.mem_cons_of_mem (v, tau) hq))
      exact htail.mono fun Theta' hpres x hx => by
        have hxv : x ≠ v := by
          intro h
          subst x
          exact hv hx
        rw [hpres x hx, Function.update_of_ne hxv]

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

theorem denote_imp_true_iff.{u}
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

/-- Type-context compatibility transfers from an original term evaluated
under `vs := ws` to the variable-substituted term evaluated under `zs := ws`. -/
theorem respects_substList_vars.{u}
    (t : SMT.Term) (vs zs : List SMT.𝒱) (ws : List SMT.Dom.{u})
    {Gamma : SMT.TypeContext}
    {Theta : SMT.RenamingContext.Context.{u}}
    (vs_zs_len : vs.length = zs.length)
    (vs_ws_len : vs.length = ws.length)
    (zs_disj_vs : ∀ z ∈ zs, z ∉ vs)
    (hzs : ∀ (i : ℕ) (hi_z : i < zs.length) (hi_w : i < ws.length),
      Theta zs[i] = some ws[i])
    (hzs_type : ∀ (i : ℕ) (hi_z : i < zs.length)
      (hi_w : i < ws.length) (tau : SMTType),
      Gamma.lookup zs[i] = some tau → (ws[i]).snd.fst = tau)
    (hresp : SMT.RenamingContext.RespectsTypeContextOnFV
      (Function.updates Theta vs (ws.map Option.some)) Gamma t) :
    SMT.RenamingContext.RespectsTypeContextOnFV Theta Gamma
      (SMT.substList vs (zs.map SMT.Term.var) t) := by
  intro x tau hx hlookup
  have hx_not_vs : x ∉ vs := by
    intro hxvs
    apply SMT_not_mem_fv_substList_of_mem_vars
      (by simp [vs_zs_len]) hxvs _ hx
    intro q hq
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hq
    simp only [SMT.fv, List.mem_singleton]
    intro hxz
    subst x
    exact zs_disj_vs z hz hxvs
  rcases SMT_mem_fv_substList hx with hx_t | ⟨q, hq, hx_q⟩
  · obtain ⟨d, hd, hd_type⟩ := hresp hx_t hlookup
    rw [Function.updates_of_not_mem Theta vs _ x hx_not_vs] at hd
    exact ⟨d, hd, hd_type⟩
  · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hq
    simp only [SMT.fv, List.mem_singleton] at hx_q
    subst x
    obtain ⟨i, hi, hzi⟩ := List.mem_iff_getElem.mp hz
    subst z
    have hi_w : i < ws.length := by omega
    exact ⟨ws[i], hzs i hi hi_w, hzs_type i hi hi_w tau hlookup⟩

/-- The converse compatibility transfer: if the variable-substituted term is
compatible and the replacement values have the types of the original names,
then the original term is compatible under `vs := ws`. -/
theorem respects_of_substList_vars.{u}
    (t : SMT.Term) (vs zs : List SMT.𝒱) (ws : List SMT.Dom.{u})
    {Gamma : SMT.TypeContext}
    {Theta : SMT.RenamingContext.Context.{u}}
    (vs_ws_len : vs.length = ws.length)
    (vs_nodup : vs.Nodup)
    (zs_disj_vs : ∀ z ∈ zs, z ∉ vs)
    (hws_type : ∀ (i : ℕ) (hi_v : i < vs.length)
      (hi_w : i < ws.length) (tau : SMTType),
      Gamma.lookup vs[i] = some tau → (ws[i]).snd.fst = tau)
    (hresp : SMT.RenamingContext.RespectsTypeContextOnFV Theta Gamma
      (SMT.substList vs (zs.map SMT.Term.var) t)) :
    SMT.RenamingContext.RespectsTypeContextOnFV
      (Function.updates Theta vs (ws.map Option.some)) Gamma t := by
  intro x tau hx hlookup
  by_cases hxs : x ∈ vs
  · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hxs
    have hi_w : i < ws.length := vs_ws_len ▸ hi
    refine ⟨ws[i], ?_, hws_type i hi hi_w tau hlookup⟩
    rw [Function.updates_eq_if (by simpa using vs_ws_len) vs_nodup,
      dif_pos (List.getElem_mem hi)]
    simp [List.Nodup.idxOf_getElem vs_nodup]
  · have hx_sub : x ∈ SMT.fv
        (SMT.substList vs (zs.map SMT.Term.var) t) :=
      SMT.RenamingContext.fv_mem_fv_substList hx hxs
        (fun q hq z hz => by
          obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hq
          simp only [SMT.fv, List.mem_singleton] at hz
          subst z
          exact zs_disj_vs w hw)
        (fun q hq => by
          obtain ⟨w, _, rfl⟩ := List.mem_map.mp hq
          simp [SMT.bv])
    obtain ⟨d, hd, hdtype⟩ := hresp hx_sub hlookup
    refine ⟨d, ?_, hdtype⟩
    rw [Function.updates_of_not_mem Theta vs _ x hxs]
    exact hd

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

/-- Conversely, truth of all substituted guards yields the original helper
specifications at the valuation obtained by assigning the original binder
names the replacement values. -/
theorem SpecBodiesTrue.of_subst_termsTrue.{u}
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
    (htyp : ∀ b ∈ specBodies Dlt, Gamma ⊢ˢ b : SMTType.bool)
    (hresp : ∀ b ∈ specBodies Dlt,
      SMT.RenamingContext.RespectsTypeContextOnFV
        (Function.updates Theta vs (ws.map Option.some)) Gamma b)
    (hcov_sub : ∀ b ∈ specBodies Dlt,
      SMT.RenamingContext.CoversFV Theta
        (SMT.substList vs (zs.map SMT.Term.var) b))
    (htrue : TermsTrue Theta
      ((specBodies Dlt).map
        (SMT.substList vs (zs.map SMT.Term.var)))) :
    SpecBodiesTrue
      (Function.updates Theta vs (ws.map Option.some)) Gamma Dlt := by
  intro b hb
  have hcov_b : SMT.RenamingContext.CoversFV
      (Function.updates Theta vs (ws.map Option.some)) b := by
    intro v hv
    obtain ⟨tau, hlookup⟩ := Option.isSome_iff_exists.mp <|
      AList.lookup_isSome.mpr (SMT.Typing.mem_context_of_mem_fv
        (htyp b hb) hv)
    obtain ⟨d, hd, _⟩ := hresp b hb hv hlookup
    rw [hd]
    rfl
  obtain ⟨db, hden_b, hdb_type⟩ :=
    SMT.RenamingContext.denote_exists_of_typing_fv
      (htyp b hb) (hresp b hb) hcov_b
  have heq := substList_vars_denote_eq b vs zs ws
    vs_zs_len vs_ws_len vs_nodup (hbv b hb).1 (hbv b hb).2
    zs_disj_vs hzs (hcov_sub b hb) hcov_b
  have hden_sub := heq.trans hden_b
  have hdb_true := htrue
    (SMT.substList vs (zs.map SMT.Term.var) b)
    (List.mem_map.mpr ⟨b, hb, rfl⟩) (hcov_sub b hb) db hden_sub
  exact ⟨hcov_b, db, hresp b hb, hden_b, hdb_type, hdb_true⟩

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

/-- Every declaration name is bound in the right-nested helper closure. -/
theorem not_mem_fv_foldr_decl_forall
    (Dlt : SMT.Chunk) (inner : SMT.Term) :
    ∀ v ∈ declVars Dlt,
      v ∉ SMT.fv ((declBinders Dlt).foldr
        (fun p t => SMT.Term.forall [p.1] [p.2] t) inner) := by
  induction Dlt with
  | nil => simp [declVars]
  | cons i D ih =>
      cases i with
      | declare_const w tau =>
          intro v hv
          simp only [declVars, List.filterMap_cons, List.mem_cons] at hv
          simp only [declBinders, List.filterMap_cons, List.foldr_cons,
            SMT.fv, List.mem_removeAll_iff]
          rcases hv with rfl | hv
          · exact fun h => h.2 (List.mem_singleton_self v)
          · intro h
            exact ih v hv h.1
      | define_fun w tau sigma body =>
          simpa [declVars, declBinders] using ih
      | define_const w tau body =>
          simpa [declVars, declBinders] using ih
      | assert body => simpa [declVars, declBinders] using ih
      | push n => simpa [declVars, declBinders] using ih
      | pop n => simpa [declVars, declBinders] using ih
      | check_sat => simpa [declVars, declBinders] using ih

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

/-- Free-variable type compatibility composes through a right-associated
Boolean implication chain. -/
theorem foldr_imp_respects.{u}
    (guards : List SMT.Term) (base : SMT.Term)
    {Gamma : SMT.TypeContext}
    {Theta : SMT.RenamingContext.Context.{u}}
    (hguards : ∀ g ∈ guards,
      SMT.RenamingContext.RespectsTypeContextOnFV Theta Gamma g)
    (hbase : SMT.RenamingContext.RespectsTypeContextOnFV Theta Gamma base) :
    SMT.RenamingContext.RespectsTypeContextOnFV Theta Gamma
      (guards.foldr SMT.Term.imp base) := by
  induction guards with
  | nil => exact hbase
  | cons g guards ih =>
      intro v sigma hv hlookup
      simp only [List.foldr_cons, SMT.fv, List.mem_append] at hv
      exact hv.elim
        (fun h => hguards g (List.mem_cons_self) h hlookup)
        (fun h => ih
          (fun q hq => hguards q (List.mem_cons_of_mem g hq)) h hlookup)

theorem fv_subset_foldr_imp_base
    (guards : List SMT.Term) (base : SMT.Term) :
    SMT.fv base ⊆ SMT.fv (guards.foldr SMT.Term.imp base) := by
  induction guards with
  | nil => exact fun _ h => h
  | cons g guards ih =>
      intro v hv
      simp only [List.foldr_cons, SMT.fv, List.mem_append]
      exact .inr (ih hv)

theorem fv_subset_foldr_imp_guard
    (guards : List SMT.Term) (base : SMT.Term)
    {g : SMT.Term} (hg : g ∈ guards) :
    SMT.fv g ⊆ SMT.fv (guards.foldr SMT.Term.imp base) := by
  induction guards with
  | nil => cases hg
  | cons q guards ih =>
      intro v hv
      simp only [List.mem_cons] at hg
      simp only [List.foldr_cons, SMT.fv, List.mem_append]
      rcases hg with rfl | hg
      · exact .inl hv
      · exact .inr (ih hg hv)

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

/-- Every typed assignment to the declarations re-scoped as unary binders
inherits the final operational context compatibility at the innermost body. -/
theorem allAssignments_respects_foldr_decl.{u}
    (Dlt : SMT.Chunk) (inner : SMT.Term)
    {Gamma GammaOp : SMT.TypeContext}
    {Theta : SMT.RenamingContext.Context.{u}}
    (htrace : DeclarationContextTrace Gamma Dlt GammaOp)
    (hresp : SMT.RenamingContext.RespectsTypeContextOnFV Theta Gamma
      ((declBinders Dlt).foldr
        (fun p t => SMT.Term.forall [p.1] [p.2] t) inner)) :
    AllAssignments (declBinders Dlt) Theta (fun Theta' =>
      SMT.RenamingContext.RespectsTypeContextOnFV Theta' GammaOp inner) := by
  induction Dlt generalizing Gamma Theta with
  | nil =>
      change GammaOp = Gamma at htrace
      subst GammaOp
      exact hresp
  | cons i D ih =>
      cases i with
      | declare_const v tau =>
          obtain ⟨hv, htail⟩ := htrace
          simp only [declBinders, List.filterMap_cons, List.foldr_cons]
            at hresp ⊢
          intro W hW
          apply ih htail
          simpa [singleton_update_eq_insert] using tail_respects hresp W hW
      | define_fun v tau sigma body =>
          simpa [declBinders] using ih htrace hresp
      | define_const v tau body =>
          simpa [declBinders] using ih htrace hresp
      | assert body => simpa [declBinders] using ih htrace hresp
      | push n => simpa [declBinders] using ih htrace hresp
      | pop n => simpa [declBinders] using ih htrace hresp
      | check_sat => simpa [declBinders] using ih htrace hresp

/-- Compatibility of the innermost body can be projected back through the
right-nested local declaration binders. -/
theorem respects_foldr_decl_forall.{u}
    (Dlt : SMT.Chunk) (inner : SMT.Term)
    {Gamma GammaOp : SMT.TypeContext}
    {Theta : SMT.RenamingContext.Context.{u}}
    (htrace : DeclarationContextTrace Gamma Dlt GammaOp)
    (hresp : SMT.RenamingContext.RespectsTypeContextOnFV Theta GammaOp inner) :
    SMT.RenamingContext.RespectsTypeContextOnFV Theta Gamma
      ((declBinders Dlt).foldr
        (fun p t => SMT.Term.forall [p.1] [p.2] t) inner) := by
  induction Dlt generalizing Gamma with
  | nil =>
      change GammaOp = Gamma at htrace
      subst GammaOp
      exact hresp
  | cons i D ih =>
      cases i with
      | declare_const v tau =>
          obtain ⟨hv, htail⟩ := htrace
          have htail_resp := ih htail
          simp only [declBinders, List.filterMap_cons, List.foldr_cons]
          intro x sigma hx hlookup
          have hx' := hx
          simp only [SMT.fv, List.mem_removeAll_iff] at hx'
          apply htail_resp hx'.1
          rw [AList.lookup_insert_ne (by simpa using hx'.2)]
          exact hlookup
      | define_fun v tau sigma body =>
          simpa [declBinders] using ih htrace
      | define_const v tau body =>
          simpa [declBinders] using ih htrace
      | assert body => simpa [declBinders] using ih htrace
      | push n => simpa [declBinders] using ih htrace
      | pop n => simpa [declBinders] using ih htrace
      | check_sat => simpa [declBinders] using ih htrace

/-- Compatibility of a quantified body under the updated context implies
compatibility of the universally closed term under the original context. -/
theorem respects_forall_of_body.{u}
    {Gamma : SMT.TypeContext} {vs : List SMT.𝒱} {taus : List SMTType}
    {body : SMT.Term} {Theta : SMT.RenamingContext.Context.{u}}
    (hlen : vs.length = taus.length)
    (hresp : SMT.RenamingContext.RespectsTypeContextOnFV Theta
      (Gamma.update vs taus hlen) body) :
    SMT.RenamingContext.RespectsTypeContextOnFV Theta Gamma
      (SMT.Term.forall vs taus body) := by
  intro x sigma hx hlookup
  have hx' := hx
  simp only [SMT.fv, List.mem_removeAll_iff] at hx'
  apply hresp hx'.1
  rw [SMT.TypeContext.lookup_update Gamma x vs taus hlen hx'.2]
  exact hlookup

/-- A typed assignment to every variable of a universal binder transports the
outer compatibility proof to its body under the updated valuation/context. -/
theorem respects_body_of_forall_assignment.{u}
    {Gamma : SMT.TypeContext} {vs : List SMT.𝒱} {taus : List SMTType}
    {body : SMT.Term} {Theta : SMT.RenamingContext.Context.{u}}
    (vs_nodup : vs.Nodup) (hlen : vs.length = taus.length)
    (hresp : SMT.RenamingContext.RespectsTypeContextOnFV Theta Gamma
      (SMT.Term.forall vs taus body))
    (w : Fin vs.length → SMT.Dom.{u})
    (hw : ∀ i, (w i).snd.fst = taus[i]'(hlen ▸ i.isLt)) :
    SMT.RenamingContext.RespectsTypeContextOnFV
      (Function.updates Theta vs (List.ofFn fun i => some (w i)))
      (Gamma.update vs taus hlen) body := by
  intro x sigma hx hlookup
  by_cases hxs : x ∈ vs
  · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hxs
    have hlookup_i := SMT.TypeContext.lookup_update_of_mem_nodup
      Gamma vs_nodup hlen hi
    rw [hlookup_i] at hlookup
    cases hlookup
    refine ⟨w ⟨i, hi⟩, ?_, hw ⟨i, hi⟩⟩
    rw [Function.updates_eq_if (by simp) vs_nodup,
      dif_pos (List.getElem_mem hi)]
    simp [List.Nodup.idxOf_getElem vs_nodup]
  · have hlookup_base : Gamma.lookup x = some sigma := by
      rwa [SMT.TypeContext.lookup_update Gamma x vs taus hlen hxs] at hlookup
    obtain ⟨d, hd, hdtype⟩ := hresp
      (SMT.fv.mem_forall ⟨hx, hxs⟩) hlookup_base
    refine ⟨d, ?_, hdtype⟩
    rw [Function.updates_of_not_mem Theta vs _ x hxs]
    exact hd

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

/-- A nested helper closure has the truth value of a proposition when every
typed helper assignment makes the leaf true in the positive case and one
typed assignment makes it false in the negative case. -/
theorem foldr_true_iff.{u}
    (ps : List (SMT.𝒱 × SMTType)) (inner : SMT.Term)
    {Gamma : SMT.TypeContext}
    {Theta : SMT.RenamingContext.Context.{u}} (Q : Prop)
    (htyp : Gamma ⊢ˢ ps.foldr
      (fun p t => SMT.Term.forall [p.1] [p.2] t) inner :
        SMTType.bool)
    (hcov : SMT.RenamingContext.CoversFV Theta
      (ps.foldr (fun p t => SMT.Term.forall [p.1] [p.2] t) inner))
    (hresp : SMT.RenamingContext.RespectsTypeContextOnFV Theta Gamma
      (ps.foldr (fun p t => SMT.Term.forall [p.1] [p.2] t) inner))
    (htrue : Q → AllAssignments ps Theta (fun Theta' =>
      ∀ hcov_inner : SMT.RenamingContext.CoversFV Theta' inner,
        ⟦inner.abstract Theta' hcov_inner⟧ˢ =
          some ⟨ZFSet.zftrue, SMTType.bool,
            ZFSet.ZFBool.zftrue_mem_𝔹⟩))
    (hfalse : ¬ Q → SomeAssignment ps Theta (fun Theta' =>
      ∀ hcov_inner : SMT.RenamingContext.CoversFV Theta' inner,
        ⟦inner.abstract Theta' hcov_inner⟧ˢ =
          some ⟨ZFSet.zffalse, SMTType.bool,
            ZFSet.ZFBool.zffalse_mem_𝔹⟩)) :
    ∃ d : SMT.Dom.{u},
      ⟦(ps.foldr (fun p t => SMT.Term.forall [p.1] [p.2] t) inner).abstract
        Theta hcov⟧ˢ = some d ∧
      d.snd.fst = SMTType.bool ∧
      (d.fst = ZFSet.zftrue ↔ Q) := by
  obtain ⟨d, hd, hdTy⟩ :=
    SMT.RenamingContext.denote_exists_of_typing_fv htyp hresp hcov
  refine ⟨d, hd, hdTy, ?_⟩
  constructor
  · intro hdTrue
    by_contra hnQ
    have hfalseDen := foldr_eq_zffalse ps inner htyp hcov hresp
      (hfalse hnQ)
    have hdEq : d = ⟨ZFSet.zffalse, SMTType.bool,
        ZFSet.ZFBool.zffalse_mem_𝔹⟩ :=
      Option.some.inj (hd.symm.trans hfalseDen)
    rw [hdEq] at hdTrue
    exact ZFSet.zftrue_ne_zffalse hdTrue.symm
  · intro hQ
    have htrueDen := foldr_eq_zftrue ps inner htyp hcov hresp
      (htrue hQ)
    have hdEq : d = ⟨ZFSet.zftrue, SMTType.bool,
        ZFSet.ZFBool.zftrue_mem_𝔹⟩ :=
      Option.some.inj (hd.symm.trans htrueDen)
    rw [hdEq]

end SMT.ScopedForall

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 2048 in
theorem encodeTerm_rep_spec.all_case.{u}
    (vs : List B.𝒱) (D P : B.Term)
    (D_ih : EncodeTermRepIH.{u} D)
    (P_ih : EncodeTermRepIH.{u} P)
    (P_scoped : EncodeTermRepScopedBoolFromIH.{u} P)
    (binder_admissible : EncodeTermAllBinderAdmissible.{u})
    (wd_P : B.Term.WellDefined.{u} P)
    (E : B.Env) {Lambda : SMT.TypeContext} {alpha : BType}
    (typ_t : E.context ⊢ᴮ B.Term.all vs D P : alpha)
    {Xi : B.RenamingContext.Context.{u}}
    (Xi_fv : ∀ v ∈ B.fv (B.Term.all vs D P), (Xi v).isSome = true)
    {Theta0 : SMT.RenamingContext.Context.{u}}
    (related : RValuationCastSupportedOnFV Xi Theta0
      (B.Term.all vs D P))
    {used : List SMT.𝒱}
    (Theta0_none : ∀ v ∉ used, Theta0 v = none)
    (Theta0_dom : ∀ v, Theta0 v ≠ none → v ∈ Lambda)
    {T : ZFSet.{u}} {hT : T ∈ ⟦alpha⟧ᶻ}
    (den_t : ⟦(B.Term.all vs D P).abstract Xi Xi_fv⟧ᴮ =
      some ⟨T, ⟨alpha, hT⟩⟩)
    (vars_used : ∀ v ∈ (B.Term.all vs D P).vars, v ∈ used)
    (Lambda_inv : ∀ v ∈ (B.Term.all vs D P).vars,
      v ∈ Lambda → v ∈ E.context)
    (bv_nodup : (B.bv (B.Term.all vs D P)).Nodup)
    (respects : B.RenamingContext.RespectsTypeContextOnFV Theta0 Lambda
      (B.Term.all vs D P))
    (fv_in_Lambda : ∀ v ∈ B.fv (B.Term.all vs D P), v ∈ Lambda)
    (wf : B.RenWF E.context Xi)
    {n : ℕ} :
    ⦃fun ⟨E0, Lambda'⟩ ↦
      ⌜Lambda' = Lambda ∧ E0.freshvarsc = n ∧
        Lambda.keys ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
    encodeTerm (B.Term.all vs D P) E
    ⦃⇓? (⟨t', sigma⟩ : SMT.Term × SMTType) ⟨E', Gamma'⟩ =>
      ⌜EncodeTermRepPost (B.Term.all vs D P) alpha Lambda Xi Theta0
        used T hT E t' sigma E' Gamma'⌝⦄ := by
  mstart
  mintro pre ∀St0
  mpure pre
  obtain ⟨rfl, rfl, St0_sub, St0_used_eq⟩ := pre
  obtain ⟨alpha_eq, vs_nemp, alphas, Ds, vs_alphas_len, vs_Ds_len,
      D_eq, vs_nodup, typ_Ds, typ_P, vs_context_disj⟩ :=
    B.Typing.allE typ_t
  subst alpha_eq
  have alphas_nemp : alphas ≠ [] := by
    simpa [vs_alphas_len, ← List.length_pos_iff] using vs_nemp
  let tau := alphas.reduce (· ×ᴮ ·) alphas_nemp
  have typ_D : E.context ⊢ᴮ D : BType.set tau := by
    rw [D_eq]
    exact typing_reduce_cprod E.context _ _ typ_Ds
      (by simpa [vs_Ds_len, ← List.length_pos_iff] using vs_nemp)
      (by simpa [vs_alphas_len, ← List.length_pos_iff] using vs_nemp)
  have tau_hasArity : tau.hasArity vs.length := by
    dsimp [tau]
    rw [List.reduce]
    have hlen : alphas.tail.length + 1 = vs.length := by
      rw [List.length_tail, vs_alphas_len]
      have := List.length_pos_of_ne_nil alphas_nemp
      omega
    convert BType.hasArity_of_foldl
      (α := alphas.head alphas_nemp) (αs := alphas.tail) using 1
    exact hlen.symm
  have Xi_fv_D : ∀ v ∈ B.fv D, (Xi v).isSome = true :=
    fun v hv => Xi_fv v (B.fv.mem_all (.inl hv))
  have fv_D_sub : B.fv D ⊆ B.fv (B.Term.all vs D P) :=
    fun _ hv => B.fv.mem_all (.inl hv)
  have related_D : RValuationCastSupportedOnFV Xi Theta0 D :=
    related.mono_fv fv_D_sub
  have vars_used_D : ∀ v ∈ D.vars, v ∈ used := by
    intro v hv
    apply vars_used v
    simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
      List.append_assoc, List.mem_append, List.mem_removeAll_iff] at hv ⊢
    rcases hv with hv | hv
    · exact .inl (.inl hv)
    · exact .inr (.inr (.inl hv))
  have vars_used_vs : ∀ v ∈ vs, v ∈ used := by
    intro v hv
    apply vars_used v
    simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
      List.append_assoc, List.mem_append, List.mem_removeAll_iff]
    exact .inr (.inl hv)
  have vars_used_P : ∀ v ∈ P.vars, v ∈ used := by
    intro v hv
    apply vars_used v
    simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
      List.append_assoc, List.mem_append, List.mem_removeAll_iff] at hv ⊢
    by_cases hvs : v ∈ vs
    · exact .inr (.inl hvs)
    · rcases hv with hv | hv
      · exact .inl (.inr ⟨hv, hvs⟩)
      · exact .inr (.inr (.inr hv))
  have Lambda_inv_D : ∀ v ∈ D.vars, v ∈ St0.types → v ∈ E.context := by
    intro v hv hctx
    apply Lambda_inv v _ hctx
    simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
      List.append_assoc, List.mem_append, List.mem_removeAll_iff] at hv ⊢
    rcases hv with hv | hv
    · exact .inl (.inl hv)
    · exact .inr (.inr (.inl hv))
  have D_bv_nodup : (B.bv D).Nodup := by
    have h := bv_nodup
    simp only [B.bv] at h
    rw [List.nodup_append, List.nodup_append] at h
    exact h.1.2.1
  have P_bv_nodup : (B.bv P).Nodup := by
    have h := bv_nodup
    simp only [B.bv] at h
    rw [List.nodup_append] at h
    exact h.2.1

  have den_all_inv := den_t
  simp only [B.Term.abstract] at den_all_inv
  unfold B.denote at den_all_inv
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at den_all_inv
  obtain ⟨⟨Dval, Dty, hDval⟩, den_D_raw, den_all_rest⟩ := den_all_inv
  have den_D0 : ⟦D.abstract Xi Xi_fv_D⟧ᴮ =
      some ⟨Dval, ⟨Dty, hDval⟩⟩ := by
    convert den_D_raw using 2
  have Dty_eq : Dty = BType.set tau := by
    exact (denote_welltyped_eq
      (t := D.abstract Xi Xi_fv_D)
      ⟨_, WFTC.of_abstract, BType.set tau,
        by convert Typing.of_abstract Xi_fv_D typ_D⟩
      den_D0).symm
  subst Dty
  have den_D : ⟦D.abstract Xi Xi_fv_D⟧ᴮ =
      some ⟨Dval, ⟨BType.set tau, hDval⟩⟩ := den_D0

  rw [encodeTerm]
  mspec (Std.Do.Triple.and _ (Std.Do.Triple.and _
    (D_ih E typ_D Xi_fv_D related_D Theta0_none Theta0_dom den_D
      vars_used_D Lambda_inv_D D_bv_nodup
      (respects.mono_fv fv_D_sub)
      (fun v hv => fv_in_Lambda v (fv_D_sub hv)) wf
      (n := St0.env.freshvarsc))
    (encodeTerm_bv_used E (t := D) (used := St0.env.usedVars)
      (n := St0.env.freshvarsc) (decl := St0.env.declarations)))
    (encodeTerm_bv_notMem_used E (t := D) (used := St0.env.usedVars)
      (n := St0.env.freshvarsc) (decl := St0.env.declarations)))
  clear D_ih
  rename_i out_D
  obtain ⟨Denc, sigmaD⟩ := out_D
  mrename_i pre
  mintro ∀St1
  mpure pre
  dsimp at pre
  obtain ⟨⟨D_post, bv_Denc_used, _D_used_sub, _D_decl⟩,
      bv_Denc_not_used, _D_used_sub', _D_decl'⟩ := pre
  obtain ⟨used_sub_D, types_sub_D, keys_sub_D, covers_D,
      path_D, typ_Denc, _shape_D, D_preserves,
      ThetaD, hcov_D, ThetaD_ext, related_D_out, ThetaD_none,
      respects_D_out, target_respects_D, ThetaD_dom,
      denD, hden_Denc, hdenD_type, D_rel, D_total⟩ := D_post
  rcases denD with ⟨DencVal, sigmaDVal, hDencVal⟩
  dsimp at hdenD_type
  subst sigmaDVal
  let setRep := sigmaD
  have setRep_supported :
      BType.SupportedSMT (BType.set tau) setRep := by
    simpa [setRep] using D_rel.supported
  rcases D_rel.supported.setE with
    ⟨rho, hsetPred, rho_supported⟩ | ⟨a, b, htau, hoption⟩
  all_goals first
    | dsimp at hsetPred
      subst sigmaD
      simp only [BType.toSMTType] at *
      have hlen_eq : vs.length =
          (rho.fromProdl (vs.length - 1)).length :=
        (rho_supported.fromProdl_length_of_hasArity tau_hasArity).symm
      rw [dif_pos hlen_eq]
      mspec SMT.mapFinIdxM_all_body_spec vs E.flags
        (rho.fromProdl (vs.length - 1)) hlen_eq
      rename_i sigmas
      mrename_i pre
      mintro ∀St2
      mpure pre
      obtain ⟨St2_types, St2_fvc, St2_used, sigmas_len, flag_rel⟩ := pre
      have selected_contract := binder_admissible E vs D P tau typ_t typ_D
        Xi Xi_fv_D Dval hDval den_D rho rho_supported sigmas
        hlen_eq sigmas_len flag_rel
      have component_supported : ∀ i (hi_alpha : i < alphas.length)
          (hi_sigma : i < sigmas.length),
          BType.SupportedSMT alphas[i] sigmas[i] := by
        intro i hi_alpha hi_sigma
        have hi_vs : i < vs.length := vs_alphas_len ▸ hi_alpha
        have hcomponent := selected_contract.1 i hi_sigma
        have hreduce : tau.get vs.length ⟨i, hi_vs⟩ =
            alphas[i] := by
          dsimp [tau]
          simpa using _root_.BType.get_reduce alphas_nemp
            vs_alphas_len ⟨i, hi_vs⟩
        simpa only [hreduce, List.get_eq_getElem] using hcomponent
      have selected_admissible :
          ∀ (Xi_alt : B.RenamingContext.Context)
            (Xi_fv_D_alt : ∀ v ∈ B.fv D, (Xi_alt v).isSome = true)
            (Dval_alt : ZFSet.{u})
            (hDval_alt : Dval_alt ∈ ⟦BType.set tau⟧ᶻ)
            (den_D_alt : ⟦D.abstract Xi_alt Xi_fv_D_alt⟧ᴮ =
              some ⟨Dval_alt, ⟨BType.set tau, hDval_alt⟩⟩)
            (hcast : sigmas.toProdl ⊑ tau.toSMTType),
            BinderCastAdmissible tau sigmas.toProdl
              hcast.toCastPath Dval_alt := by
        intro Xi_alt Xi_fv_D_alt Dval_alt hDval_alt den_D_alt hcast
        exact (binder_admissible E vs D P tau typ_t typ_D Xi_alt
          Xi_fv_D_alt Dval_alt hDval_alt den_D_alt rho rho_supported
          sigmas hlen_eq sigmas_len flag_rel).2 hcast
    | dsimp at hoption
      subst sigmaD
      simp only [BType.toSMTType] at *
      have hlen_eq : vs.length =
          (tau.toSMTType.fromProdl (vs.length - 1)).length :=
        (fromProdl_length_of_hasArity tau_hasArity).symm
      let sigmas :=
        (a.toSMTType.pair b.toSMTType).fromProdl (vs.length - 1)
      have sigmas_eq : sigmas =
          tau.toSMTType.fromProdl (vs.length - 1) := by
        dsimp [sigmas]
        rw [htau]
        simp only [BType.toSMTType]
      have sigmas_len : sigmas.length =
          (tau.toSMTType.fromProdl (vs.length - 1)).length := by
        rw [sigmas_eq]
      have vs_sigmas_len_raw :
          ((a.toSMTType.pair b.toSMTType).fromProdl
            (vs.length - 1)).length = vs.length := by
        simpa [sigmas] using (hlen_eq.trans sigmas_len.symm).symm
      have harity :
          (((a.toSMTType.pair b.toSMTType).fromProdl
            (vs.length - 1)).length == vs.length) = true :=
        beq_iff_eq.mpr vs_sigmas_len_raw
      rw [if_pos harity]
      mspec Std.Do.Spec.pure
      let St2 := St1
      have St2_types : St2.types = St1.types := rfl
      have St2_fvc : St2.env.freshvarsc = St1.env.freshvarsc := rfl
      have St2_used : St2.env.usedVars = St1.env.usedVars := rfl
      have component_supported : ∀ i (hi_alpha : i < alphas.length)
          (hi_sigma : i < sigmas.length),
          BType.SupportedSMT alphas[i] sigmas[i] := by
        intro i hi_alpha hi_sigma
        have hi_vs : i < vs.length := vs_alphas_len ▸ hi_alpha
        have hfrom :
            (tau.get vs.length ⟨i, hi_vs⟩).toSMTType =
              (tau.toSMTType.fromProdl (vs.length - 1))[i] :=
          toSMTType_get_eq_fromProdl_getElem tau_hasArity hi_vs
        have hreduce : tau.get vs.length ⟨i, hi_vs⟩ =
            alphas[i] := by
          dsimp [tau]
          simpa using _root_.BType.get_reduce alphas_nemp
            vs_alphas_len ⟨i, hi_vs⟩
        have htarget : alphas[i].toSMTType = sigmas[i] := by
          have hsigmas_get : sigmas[i] =
              (tau.toSMTType.fromProdl (vs.length - 1))[i] :=
            List.getElem_of_eq sigmas_eq hi_sigma
          calc
            alphas[i].toSMTType =
                (tau.get vs.length ⟨i, hi_vs⟩).toSMTType :=
              congrArg BType.toSMTType hreduce.symm
            _ = (tau.toSMTType.fromProdl (vs.length - 1))[i] := hfrom
            _ = sigmas[i] := hsigmas_get.symm
        rw [← htarget]
        exact BType.SupportedSMT.canonical alphas[i]
      have sigmas_toProdl : sigmas.toProdl = tau.toSMTType := by
        rw [sigmas_eq]
        have h_arith :
            (tau.toSMTType.fromProdl (vs.length - 1)).length =
              vs.length - 1 + 1 := by
          rw [← hlen_eq]
          have := List.length_pos_of_ne_nil vs_nemp
          omega
        exact SMT.SMTType.fromProdl_toProdl_roundtrip _ _ h_arith
      have selected_admissible :
          ∀ (Xi_alt : B.RenamingContext.Context)
            (Xi_fv_D_alt : ∀ v ∈ B.fv D, (Xi_alt v).isSome = true)
            (Dval_alt : ZFSet.{u})
            (hDval_alt : Dval_alt ∈ ⟦BType.set tau⟧ᶻ)
            (den_D_alt : ⟦D.abstract Xi_alt Xi_fv_D_alt⟧ᴮ =
              some ⟨Dval_alt, ⟨BType.set tau, hDval_alt⟩⟩)
            (hcast : sigmas.toProdl ⊑ tau.toSMTType),
            BinderCastAdmissible tau sigmas.toProdl
              hcast.toCastPath Dval_alt := by
        intro _Xi_alt _Xi_fv_D_alt Dval_alt hDval_alt _den_D_alt hcast
        exact BinderCastAdmissible.of_eq_canonical
          sigmas_toProdl hDval_alt hcast
  all_goals
    have vs_sigmas_len : vs.length = sigmas.length := by
      rw [sigmas_len]
      exact hlen_eq
    obtain ⟨vs_not_D_fv, vs_disj_St1⟩ :=
      vs_disj_St₁_helper (P := P) typ_D vs_context_disj
        Lambda_inv vars_used_vs D_preserves bv_nodup
    mspec SMT.addToContext_forIn_spec (pairs := vs.zip sigmas)
      (Γ := St2.types) (n := St2.env.freshvarsc)
      (used := St2.env.usedVars)
    mrename_i pre
    mintro ∀St3
    mpure pre
    obtain ⟨St3_types, St3_fvc, St3_used⟩ := pre
    have St3_update : St3.types =
        St1.types.update vs sigmas vs_sigmas_len := by
      rw [St3_types, St2_types,
        SMT.TypeContext.update_eq_zip_foldl]
    have St1_sub_St3_types : St1.types ⊆ St3.types := by
      rw [St3_update]
      exact entries_subset_update_of_fresh vs_disj_St1 vs_sigmas_len
    have St1_sub_St3_used : St1.env.usedVars ⊆ St3.env.usedVars := by
      rw [St3_used, St2_used]
      intro v hv
      suffices ∀ (ps : List (SMT.𝒱 × SMTType)) (acc : List SMT.𝒱),
          v ∈ acc → v ∈ ps.foldl (fun used p => p.1 :: used) acc by
        exact this _ _ hv
      intro ps
      induction ps with
      | nil => exact fun _ h => h
      | cons p ps ih =>
          intro acc h
          exact ih _ (List.mem_cons_of_mem p.1 h)
    have St3_keys_sub : St3.types.keys ⊆ St3.env.usedVars := by
      rw [St3_types, St3_used, St2_types, St2_used]
      exact encodeTerm_state.keys_foldl_insert_subset_foldl_cons
        (vs.zip sigmas) keys_sub_D

    have alphas_sigmas_len : alphas.length = sigmas.length :=
      vs_alphas_len.symm.trans vs_sigmas_len
    have supported_components :
        List.Forall₂ BType.SupportedSMT alphas sigmas := by
      apply List.forall₂_of_length_eq_of_get alphas_sigmas_len
      exact component_supported
    obtain ⟨Xrun, Yrun, hXrun, hYrun, run_rel⟩ :=
      RDomCastSupported.default_tuple_witness alphas_nemp
        supported_components
    let bs : Fin vs.length → B.Dom.{u} := fun i =>
      let j : Fin alphas.length := Fin.cast vs_alphas_len i
      ⟨Xrun.get alphas.length j, alphas[j],
        BType.mem_get_of_mem_reduce_toZFSet alphas_nemp hXrun⟩
    let ss : Fin vs.length → SMT.Dom.{u} := fun i =>
      let j : Fin sigmas.length :=
        Fin.cast (vs_alphas_len.trans alphas_sigmas_len) i
      ⟨Yrun.get sigmas.length j, sigmas[j],
        SMTType.mem_get_of_mem_toProdl
          (fun hs => alphas_nemp (List.length_eq_zero_iff.mp
            (alphas_sigmas_len.trans (by simp [hs])))) hYrun⟩
    let XiP := Function.updates Xi vs
      (List.ofFn fun i => some (bs i))
    let ThetaP := Function.updates ThetaD vs
      (List.ofFn fun i => some (ss i))
    have related_ambient : ∀ v ∈ B.fv P, v ∉ vs →
        match Xi v, ThetaD v with
        | some d, some d' => RDomCastSupported d d'
        | _, _ => False := by
      intro v hv hvs
      exact related.of_extends ThetaD_ext v
        (B.fv.mem_all (.inr ⟨hv, hvs⟩))
    have related_P : RValuationCastSupportedOnFV XiP ThetaP P := by
      simpa [XiP, ThetaP, bs, ss] using
        (RValuationCastSupportedOnFV.updates_of_reduce_toProdl
          vs_nodup alphas_nemp vs_alphas_len alphas_sigmas_len
          hXrun hYrun run_rel related_ambient (t := P))
    have XiP_fv : ∀ v ∈ B.fv P, (XiP v).isSome = true := by
      intro v hv
      by_cases hvs : v ∈ vs
      · change (Function.updates Xi vs
          (List.ofFn fun i => some (bs i)) v).isSome = true
        rw [Function.updates_eq_if (by simp) vs_nodup,
          dif_pos hvs]
        simp
      · change (Function.updates Xi vs
          (List.ofFn fun i => some (bs i)) v).isSome = true
        rw [Function.updates_of_not_mem Xi vs _ v hvs]
        exact Xi_fv v (B.fv.mem_all (.inr ⟨hv, hvs⟩))
    have wf_P : B.RenWF (vs.zipToAList alphas ∪ E.context) XiP := by
      exact B.RenWF.updates_ofFn wf vs_nodup vs_context_disj
        vs_alphas_len (fun _ => rfl)
    obtain ⟨Pval, hPval, den_P⟩ :=
      B.denote_exists_of_typing typ_P XiP XiP_fv
        (@WFTC.wf _ WFTC.of_abstract) (wd_P.toPHOAS XiP XiP_fv)

    have ThetaP_none : ∀ v ∉ St3.env.usedVars, ThetaP v = none := by
      intro v hv
      have hv_vs : v ∉ vs := by
        intro hvs
        have hidx : vs.idxOf v < vs.length :=
          List.idxOf_lt_length_of_mem hvs
        have hpair : (v, sigmas[vs.idxOf v]'(vs_sigmas_len ▸ hidx)) ∈
            vs.zip sigmas := by
          have hzipidx : vs.idxOf v < (vs.zip sigmas).length := by
            simp only [List.length_zip]
            omega
          have hm := List.getElem_mem (l := vs.zip sigmas) hzipidx
          simpa only [List.getElem_zip, List.getElem_idxOf hidx] using hm
        have hpreserve : ∀ (ps : List (SMT.𝒱 × SMTType))
            (acc : List SMT.𝒱) (x : SMT.𝒱), x ∈ acc →
            x ∈ ps.foldl (fun used q => q.1 :: used) acc := by
          intro ps
          induction ps with
          | nil => exact fun _ _ h => h
          | cons q qs ih =>
              intro acc x hx
              exact ih _ _ (List.mem_cons_of_mem q.1 hx)
        have hfold : ∀ (ps : List (SMT.𝒱 × SMTType))
            (acc : List SMT.𝒱) (p : SMT.𝒱 × SMTType),
            p ∈ ps → p.1 ∈ ps.foldl (fun used q => q.1 :: used) acc := by
          intro ps
          induction ps with
          | nil => simp
          | cons q qs ih =>
              intro acc p hp
              simp only [List.mem_cons] at hp
              simp only [List.foldl_cons]
              rcases hp with rfl | hp
              · exact hpreserve _ _ _ (List.mem_cons_self ..)
              · exact ih _ _ hp
        apply hv
        rw [St3_used, St2_used]
        exact hfold _ _ _ hpair
      change Function.updates ThetaD vs
        (List.ofFn fun i => some (ss i)) v = none
      rw [Function.updates_of_not_mem ThetaD vs _ v hv_vs]
      apply ThetaD_none v
      exact fun hused => hv (St1_sub_St3_used hused)
    have ThetaP_dom : ∀ v, ThetaP v ≠ none → v ∈ St3.types := by
      intro v hv
      by_cases hvs : v ∈ vs
      · rw [St3_update]
        exact (SMT.TypeContext.mem_update_iff
          St1.types v vs sigmas vs_sigmas_len).mpr (Or.inl hvs)
      · change Function.updates ThetaD vs
          (List.ofFn fun i => some (ss i)) v ≠ none at hv
        rw [Function.updates_of_not_mem ThetaD vs _ v hvs] at hv
        exact AList.mem_of_subset St1_sub_St3_types (ThetaD_dom v hv)
    have respects_P : B.RenamingContext.RespectsTypeContextOnFV
        ThetaP St3.types P := by
      intro v sigma hv hlookup
      by_cases hvs : v ∈ vs
      · let i : Fin vs.length :=
          ⟨vs.idxOf v, List.idxOf_lt_length_of_mem hvs⟩
        have hvi : vs[i] = v :=
          List.getElem_idxOf (List.idxOf_lt_length_of_mem hvs)
        have hctx : St3.types.lookup vs[i] =
            some sigmas[Fin.cast vs_sigmas_len i] := by
          rw [St3_update]
          exact SMT.TypeContext.lookup_update_of_mem_nodup
            St1.types vs_nodup vs_sigmas_len i.isLt
        rw [hvi] at hctx
        rw [hctx] at hlookup
        cases hlookup
        refine ⟨ss i, ?_, rfl⟩
        change Function.updates ThetaD vs
          (List.ofFn fun i => some (ss i)) v = some (ss i)
        rw [Function.updates_eq_if (by simp) vs_nodup,
          dif_pos hvs]
        simpa [i, hvi]
      · have hv_all : v ∈ B.fv (B.Term.all vs D P) :=
          B.fv.mem_all (.inr ⟨hv, hvs⟩)
        have hv_St0 := fv_in_Lambda v hv_all
        obtain ⟨sigma0, hsigma0⟩ := Option.isSome_iff_exists.mp
          (AList.lookup_isSome.mpr hv_St0)
        have hsigma1 : St1.types.lookup v = some sigma0 :=
          AList.lookup_of_subset types_sub_D hsigma0
        have hsigma3 : St3.types.lookup v = some sigma0 := by
          rw [St3_update,
            SMT.TypeContext.lookup_update St1.types v vs sigmas
              vs_sigmas_len hvs]
          exact hsigma1
        rw [hsigma3] at hlookup
        cases hlookup
        obtain ⟨d, hd, hdty⟩ := respects hv_all hsigma0
        refine ⟨d, ?_, hdty⟩
        change Function.updates ThetaD vs
          (List.ofFn fun i => some (ss i)) v = some d
        rw [Function.updates_of_not_mem ThetaD vs _ v hvs]
        exact ThetaD_ext hd

    let Ebody : B.Env :=
      { E with context := vs.zipToAList alphas ∪ E.context }
    conv in encodeTerm P E => rw [encodeTerm_env_irrel P E Ebody rfl]
    have vars_used_P_St3 : ∀ v ∈ P.vars, v ∈ St3.env.usedVars :=
      fun v hv => St1_sub_St3_used (used_sub_D (vars_used_P v hv))
    have fv_P_in_St3 : ∀ v ∈ B.fv P, v ∈ St3.types := by
      intro v hv
      by_cases hvs : v ∈ vs
      · rw [St3_update]
        exact (SMT.TypeContext.mem_update_iff
          St1.types v vs sigmas vs_sigmas_len).mpr (.inl hvs)
      · exact AList.mem_of_subset St1_sub_St3_types <|
          AList.mem_of_subset types_sub_D <|
            fv_in_Lambda v (B.fv.mem_all (.inr ⟨hv, hvs⟩))
    have St3_types_sub_Ebody_on_P_vars :
        ∀ v ∈ P.vars, v ∈ St3.types → v ∈ Ebody.context := by
      intro v v_in_P_vars v_in_St3
      simp only [Ebody]
      by_cases v_in_vs : v ∈ vs
      · exact AList.mem_union.mpr <| .inl <|
          AList.mem_zipToAList_of_mem vs_nodup vs_alphas_len v_in_vs
      · apply AList.mem_union.mpr
        right
        have v_in_St1 : v ∈ St1.types := by
          rw [St3_update] at v_in_St3
          exact ((SMT.TypeContext.mem_update_iff
            St1.types v vs sigmas vs_sigmas_len).mp v_in_St3).resolve_left
              v_in_vs
        have v_used : v ∈ used := vars_used_P v v_in_P_vars
        by_cases v_St0 : v ∈ St0.types
        · have v_all : v ∈ (B.Term.all vs D P).vars := by
            unfold B.Term.vars at v_in_P_vars ⊢
            rw [List.mem_union_iff]
            rcases List.mem_union_iff.mp v_in_P_vars with h_fv | h_bv
            · left
              simp only [B.fv, List.mem_append]
              exact .inr (List.mem_removeAll_iff.mpr ⟨h_fv, v_in_vs⟩)
            · right
              simp only [B.bv, List.mem_append]
              exact .inr h_bv
          exact Lambda_inv v v_all v_St0
        · have v_vars_D : v ∈ B.Term.vars D := by
            by_contra h
            exact (D_preserves v v_used v_St0 h) v_in_St1
          rcases B.Term.mem_vars_iff.mp v_vars_D with hD_fv | hD_bv
          · exact AList.lookup_isSome.mp
              (B.Typing.mem_context_of_mem_fv typ_D hD_fv)
          · rcases B.Term.mem_vars_iff.mp v_in_P_vars with hP_fv | hP_bv
            · have h_in_Ebody :
                  ((vs.zipToAList alphas ∪ E.context).lookup v).isSome :=
                B.Typing.mem_context_of_mem_fv typ_P hP_fv
              rcases AList.mem_union.mp
                  (AList.lookup_isSome.mp h_in_Ebody) with h_vs | h_E
              · exact absurd (AList.mem_zipToAList h_vs) v_in_vs
              · exact h_E
            · exfalso
              have hbn := bv_nodup
              simp only [B.bv] at hbn
              rw [List.nodup_append, List.nodup_append] at hbn
              exact hbn.2.2 v (List.mem_append.mpr (.inr hD_bv))
                v hP_bv rfl

    all_goals first
      | have _set_branch := flag_rel
        let PBase := St3
        have St3_sub_PBase_types : St3.types ⊆ PBase.types := by
          exact fun _ h => h
        have St3_sub_PBase_used :
            St3.env.usedVars ⊆ PBase.env.usedVars := by
          exact fun _ h => h
        have PBase_keys_sub :
            PBase.types.keys ⊆ PBase.env.usedVars := St3_keys_sub
        have PBase_decl_eq :
            PBase.env.declarations = St3.env.declarations := rfl
      | have _option_branch := sigmas_eq
        mspec (Std.Do.Triple.and _
          (SMT.freshVarList_spec sigmas)
          (SMT.freshVarList_decls sigmas
            (decl := St3.env.declarations)))
        rename_i zs
        mrename_i pre
        mintro ∀PBase
        mpure pre
        obtain ⟨⟨zs_len, zs_nodup, zs_not_used, zs_not_types,
          PBase_fvc, PBase_used, PBase_types⟩, PBase_decl_eq⟩ := pre
        have St3_sub_PBase_types : St3.types ⊆ PBase.types := by
          rw [PBase_types]
          refine AList.subset_foldl_insert' ?_ ?_
          · intro p hp
            exact zs_not_types p.1 (List.mem_fst_of_mem_zip hp)
          · exact List.nodup_map_fst_of_nodup_zip zs_nodup
        have St3_sub_PBase_used :
            St3.env.usedVars ⊆ PBase.env.usedVars := by
          rw [PBase_used]
          exact fun _ h => List.mem_append_right _ h
        have PBase_keys_sub :
            PBase.types.keys ⊆ PBase.env.usedVars := by
          intro v hv
          rw [PBase_types] at hv
          rw [PBase_used]
          by_cases hzs : v ∈ zs
          · exact List.mem_append_left _ (List.mem_reverse.mpr hzs)
          · exact List.mem_append_right _ <| St3_keys_sub <|
              AList.mem_of_mem_foldl_insert' hv (by
                intro hmap
                rw [List.mem_map] at hmap
                obtain ⟨⟨z, sigma⟩, hzpair, rfl⟩ := hmap
                exact hzs (List.of_mem_zip hzpair).1)
    all_goals
      have ThetaP_none_base : ∀ v ∉ PBase.env.usedVars,
          ThetaP v = none := by
        intro v hv
        exact ThetaP_none v (fun h => hv (St3_sub_PBase_used h))
      have ThetaP_dom_base : ∀ v, ThetaP v ≠ none →
          v ∈ PBase.types := by
        intro v hv
        exact AList.mem_of_subset St3_sub_PBase_types (ThetaP_dom v hv)
      have respects_P_base :
          B.RenamingContext.RespectsTypeContextOnFV
            ThetaP PBase.types P := by
        exact respects_P.transport_fv (fun _ h => h)
          St3_sub_PBase_types fv_P_in_St3
      have vars_used_P_base : ∀ v ∈ P.vars,
          v ∈ PBase.env.usedVars := by
        intro v hv
        exact St3_sub_PBase_used (vars_used_P_St3 v hv)
      have fv_P_in_base : ∀ v ∈ B.fv P, v ∈ PBase.types := by
        intro v hv
        exact AList.mem_of_subset St3_sub_PBase_types (fv_P_in_St3 v hv)
      have PBase_types_sub_Ebody_on_P_vars :
          ∀ v ∈ P.vars, v ∈ PBase.types → v ∈ Ebody.context := by
        intro v hv hbase
        apply St3_types_sub_Ebody_on_P_vars v hv
        first
        | exact hbase
        | rw [PBase_types] at hbase
          apply AList.mem_of_mem_foldl_insert' hbase
          intro hmap
          rw [List.mem_map] at hmap
          obtain ⟨⟨z, sigma⟩, hzpair, rfl⟩ := hmap
          exact zs_not_used z (List.of_mem_zip hzpair).1
            (vars_used_P_St3 z hv)

      mspec Std.Do.Spec.get_StateT
      mspec Std.Do.Spec.get_StateT
      mspec Std.Do.Spec.get_StateT
    mspec (Std.Do.Triple.and _
      (Std.Do.Triple.and _
        (Std.Do.Triple.and _
          (P_ih Ebody typ_P XiP_fv related_P ThetaP_none_base
            ThetaP_dom_base den_P vars_used_P_base
            PBase_types_sub_Ebody_on_P_vars P_bv_nodup
            respects_P_base fv_P_in_base wf_P
            (n := PBase.env.freshvarsc))
          (P_scoped Ebody typ_P XiP_fv related_P ThetaP_none_base
            ThetaP_dom_base den_P vars_used_P_base
            PBase_types_sub_Ebody_on_P_vars P_bv_nodup
            respects_P_base fv_P_in_base wf_P
            (⟨St3.types, DeclarationContextTrace.nil _,
              St3_sub_PBase_types⟩ :
              DeclarationContextEnvelope St3.types [] PBase.types)
            fv_P_in_St3 (ScopedSpecsTyping.nil St3.types)
            (n := PBase.env.freshvarsc)
            (decl := PBase.env.declarations)))
        (encodeTerm_bv_used Ebody (t := P)
          (used := PBase.env.usedVars) (n := PBase.env.freshvarsc)
          (decl := PBase.env.declarations)))
      (encodeTerm_bv_notMem_used Ebody (t := P)
        (used := PBase.env.usedVars) (n := PBase.env.freshvarsc)
        (decl := PBase.env.declarations)))
    clear P_ih P_scoped
    rename_i out_P
    obtain ⟨Penc, sigmaP⟩ := out_P
    mrename_i pre
    mintro ∀St4
    mpure pre
    dsimp at pre
    obtain ⟨⟨⟨P_post, ⟨DltP, P_decl_eq, P_trace, P_envelope,
        P_sc_total, P_guard, P_specs_op, P_sc_typing⟩⟩,
      bv_Penc_used, _P_used_sub_bv, P_decl_bv⟩,
      bv_Penc_not_used, _P_used_sub_struct, DltP_struct,
        P_decl_struct, P_delta_not_used⟩ := pre
    have DltP_eq : DltP = DltP_struct := by
      rw [P_decl_eq] at P_decl_struct
      exact List.append_right_injective _ P_decl_struct
    subst DltP_struct
    obtain ⟨DltP_bv, P_decl_bv_eq, P_delta_bv⟩ := P_decl_bv
    have DltP_bv_eq : DltP = DltP_bv := by
      rw [P_decl_eq] at P_decl_bv_eq
      exact List.append_right_injective _ P_decl_bv_eq
    subst DltP_bv
    obtain ⟨used_sub_P, types_sub_P, keys_sub_P, covers_P,
      path_P, typ_Penc, _shape_P, P_preserves,
      ThetaBody, hcov_P, ThetaBody_ext, related_P_out, ThetaBody_none,
      respects_P_out, target_respects_P, ThetaBody_dom,
      denP, hden_Penc, hdenP_type, P_rel, P_total⟩ := P_post
    rcases denP with ⟨PencVal, sigmaPVal, hPencVal⟩
    dsimp at hdenP_type
    subst sigmaPVal
    obtain ⟨cP⟩ := path_P
    have hsigmaP : sigmaP = SMTType.bool :=
      castPath.source_eq_bool cP
    subst sigmaP
    simp only [BType.toSMTType] at *

    have St3_sub_St4_types : St3.types ⊆ St4.types :=
      fun _ h => types_sub_P (St3_sub_PBase_types h)
    have St3_sub_St4_used :
        St3.env.usedVars ⊆ St4.env.usedVars :=
      fun _ h => used_sub_P (St3_sub_PBase_used h)
    all_goals first
      | have _set_branch := flag_rel
        mspec (Std.Do.Triple.and _
          (SMT.freshVarList_spec sigmas)
          (SMT.freshVarList_decls sigmas
            (decl := St4.env.declarations)))
        rename_i zs
        mrename_i pre
        mintro ∀St5
        mpure pre
        obtain ⟨⟨zs_len, zs_nodup, zs_not_used, zs_not_types,
          St5_fvc, St5_used, St5_types⟩, St5_decl_eq⟩ := pre
        have zs_typing :=
          zs_typing_helper (St₅types := St5.types)
            zs_nodup zs_len St5_types
        have St4_sub_St5_types : St4.types ⊆ St5.types := by
          rw [St5_types]
          refine AList.subset_foldl_insert' ?_ ?_
          · intro p hp
            exact zs_not_types p.1 (List.mem_fst_of_mem_zip hp)
          · exact List.nodup_map_fst_of_nodup_zip zs_nodup
        have St4_sub_St5_used :
            St4.env.usedVars ⊆ St5.env.usedVars := by
          rw [St5_used]
          exact fun _ h => List.mem_append_right _ h
        have zs_not_St3_types : ∀ z ∈ zs, z ∉ St3.types := by
          intro z hz h3
          exact zs_not_types z hz (AList.mem_of_subset types_sub_P
            (AList.mem_of_subset St3_sub_PBase_types h3))
        have zs_not_St3_used : ∀ z ∈ zs,
            z ∉ St3.env.usedVars := by
          intro z hz h3
          exact zs_not_used z hz
            (used_sub_P (St3_sub_PBase_used h3))
        have zs_mem_St5_used : ∀ z ∈ zs,
            z ∈ St5.env.usedVars := by
          intro z hz
          rw [St5_used]
          exact List.mem_append_left _ (List.mem_reverse.mpr hz)
        have not_St5_of_not_St4 : ∀ v, v ∉ zs →
            v ∉ St4.types → v ∉ St5.types := by
          intro v hvzs hv4 hv5
          rw [St5_types] at hv5
          apply hv4
          exact AList.mem_of_mem_foldl_insert' hv5 (by
            intro hmap
            rw [List.mem_map] at hmap
            obtain ⟨⟨z, sigma⟩, hzpair, rfl⟩ := hmap
            exact hvzs (List.of_mem_zip hzpair).1)
        have St5_keys_sub : St5.types.keys ⊆ St5.env.usedVars := by
          rw [St5_used]
          intro v hv
          rw [St5_types] at hv
          by_cases hzs : v ∈ zs
          · exact List.mem_append_left _ (List.mem_reverse.mpr hzs)
          · exact List.mem_append_right _ <| keys_sub_P <|
              AList.mem_of_mem_foldl_insert' hv (by
                intro hmap
                rw [List.mem_map] at hmap
                obtain ⟨⟨z, sigma⟩, hzpair, rfl⟩ := hmap
                exact hzs (List.of_mem_zip hzpair).1)
        have old_bv_not_St5 : ∀ (t : SMT.Term) (sigma : SMTType),
            St4.types ⊢ˢ t : sigma →
            (∀ v ∈ SMT.bv t, v ∈ St4.env.usedVars) →
            ∀ v ∈ SMT.bv t, v ∉ St5.types := by
          intro t sigma htyp hbv v hv
          apply not_St5_of_not_St4 v _
            (SMT.Typing.bv_notMem_context htyp v hv)
          intro hz
          exact zs_not_used v hz (hbv v hv)
        have St5_mem_classify : ∀ v, v ∈ St5.types →
            v ∈ St3.types ∨ v ∈ zs ∨ v ∈ declVars DltP := by
          intro v hv5
          rw [St5_types] at hv5
          have hv5' : v ∈ St4.types.update zs sigmas zs_len := by
            simpa only [SMT.TypeContext.update_eq_zip_foldl] using hv5
          rcases (SMT.TypeContext.mem_update_iff
            St4.types v zs sigmas zs_len).mp hv5' with hvz | hv4
          · exact .inr (.inl hvz)
          · rcases P_trace.context_generated.mem_classify hv4 with hv3 | hvP
            · exact .inl hv3
            · exact .inr (.inr hvP)
      | have _option_branch := sigmas_eq
        let St5 := St4
        have St5_fvc : St5.env.freshvarsc = St4.env.freshvarsc := rfl
        have St5_used : St5.env.usedVars = St4.env.usedVars := rfl
        have St5_types : St5.types = St4.types := rfl
        have St5_decl_eq :
            St5.env.declarations = St4.env.declarations := rfl
        have zs_typing : ∀ (i : ℕ) (hi : i < zs.length),
            St5.types.lookup zs[i] =
              some (sigmas[i]'(zs_len ▸ hi)) := by
          intro i hi
          exact AList.lookup_of_subset types_sub_P <|
            zs_typing_helper (St₅types := PBase.types)
              zs_nodup zs_len PBase_types i hi
        have St4_sub_St5_types : St4.types ⊆ St5.types := by
          exact fun _ h => h
        have St4_sub_St5_used :
            St4.env.usedVars ⊆ St5.env.usedVars := by
          exact fun _ h => h
        have zs_not_St3_types : ∀ z ∈ zs, z ∉ St3.types :=
          zs_not_types
        have zs_not_St3_used : ∀ z ∈ zs,
            z ∉ St3.env.usedVars := zs_not_used
        have zs_mem_St5_used : ∀ z ∈ zs,
            z ∈ St5.env.usedVars := by
          intro z hz
          exact St4_sub_St5_used <| used_sub_P <|
            by
              rw [PBase_used]
              exact List.mem_append_left _ (List.mem_reverse.mpr hz)
        have not_St5_of_not_St4 : ∀ v, v ∉ zs →
            v ∉ St4.types → v ∉ St5.types := by
          exact fun _ _ h => h
        have St5_keys_sub : St5.types.keys ⊆ St5.env.usedVars :=
          keys_sub_P
        have old_bv_not_St5 : ∀ (t : SMT.Term) (sigma : SMTType),
            St4.types ⊢ˢ t : sigma →
            (∀ v ∈ SMT.bv t, v ∈ St4.env.usedVars) →
            ∀ v ∈ SMT.bv t, v ∉ St5.types := by
          intro t sigma htyp _hbv v hv
          exact SMT.Typing.bv_notMem_context htyp v hv
        have St5_mem_classify : ∀ v, v ∈ St5.types →
            v ∈ St3.types ∨ v ∈ zs ∨ v ∈ declVars DltP := by
          intro v hv5
          rcases P_trace.context_generated.mem_classify hv5 with
            hvbase | hvP
          · have PBase_update : PBase.types =
                St3.types.update zs sigmas zs_len := by
              rw [PBase_types, SMT.TypeContext.update_eq_zip_foldl]
            rw [PBase_update] at hvbase
            rcases (SMT.TypeContext.mem_update_iff
              St3.types v zs sigmas zs_len).mp hvbase with hvz | hv3
            · exact .inr (.inl hvz)
            · exact .inl hv3
          · exact .inr (.inr hvP)
    have zs_nemp : zs ≠ [] :=
      zs_nemp_helper zs_len vs_sigmas_len vs_nemp
    have typ_tuple : St5.types ⊢ˢ
        (zs.map SMT.Term.var).toPairl : sigmas.toProdl :=
      toPairl_typ_helper zs_len zs_nemp zs_typing
    have St1_sub_St2_types : St1.types ⊆ St2.types := by
      rw [St2_types]
    have St2_sub_St3_types : St2.types ⊆ St3.types := by
      intro e he
      apply St1_sub_St3_types
      rwa [St2_types] at he
    have St1_sub_St5_types : St1.types ⊆ St5.types :=
      fun _ h => St4_sub_St5_types
        (St3_sub_St4_types (St1_sub_St3_types h))
    all_goals first
      | have _set_branch := flag_rel
        have P_preserves_St3 : ∀ v ∈ St3.env.usedVars,
            v ∉ St3.types → v ∉ P.vars → v ∉ St4.types := by
          exact P_preserves
      | have _option_branch := sigmas_eq
        have P_preserves_St3 : ∀ v ∈ St3.env.usedVars,
            v ∉ St3.types → v ∉ P.vars → v ∉ St4.types := by
          intro v hvused hv3 hvP hv4
          apply P_preserves v (St3_sub_PBase_used hvused) _ hvP hv4
          intro hvbase
          rw [PBase_types] at hvbase
          apply hv3
          exact AList.mem_of_mem_foldl_insert' hvbase (by
            intro hmap
            rw [List.mem_map] at hmap
            obtain ⟨⟨z, sigma⟩, hzpair, rfl⟩ := hmap
            exact zs_not_used z (List.of_mem_zip hzpair).1 hvused)
    have bv_Denc_not_St5 : ∀ v ∈ SMT.bv Denc, v ∉ St5.types := by
      intro v hv hmem
      have hv_St3_used : v ∈ St3.env.usedVars :=
        St1_sub_St3_used (bv_Denc_used v hv)
      have hv_not_zs : v ∉ zs := fun hz =>
        zs_not_St3_used v hz hv_St3_used
      have hv_St3_used : v ∈ St3.env.usedVars :=
        St1_sub_St3_used (bv_Denc_used v hv)
      have hv_not_St1 : v ∉ St1.types :=
        SMT.Typing.bv_notMem_context typ_Denc v hv
      have hv_not_St0_used : v ∉ St0.env.usedVars :=
        bv_Denc_not_used v hv
      have hv_not_vs : v ∉ vs := by
        intro hvs
        apply hv_not_St0_used
        rw [St0_used_eq]
        exact vars_used_vs v hvs
      have hv_not_P_vars : v ∉ P.vars := by
        intro hpv
        apply hv_not_St0_used
        rw [St0_used_eq]
        exact vars_used_P v hpv
      have hv_not_St3 : v ∉ St3.types := by
        rw [St3_update]
        intro hmem3
        rcases (SMT.TypeContext.mem_update_iff
          St1.types v vs sigmas vs_sigmas_len).mp hmem3 with hvs | hSt1
        · exact hv_not_vs hvs
        · exact hv_not_St1 hSt1
      exact not_St5_of_not_St4 v hv_not_zs
        (P_preserves_St3 v hv_St3_used hv_not_St3 hv_not_P_vars) hmem
    have typ_Denc_St5 : St5.types ⊢ˢ Denc : setRep := by
      simpa [setRep] using
        SMT.Typing.weakening St1_sub_St5_types typ_Denc bv_Denc_not_St5
    have tuple_supported :
        BType.SupportedSMT tau sigmas.toProdl := by
      simpa [tau] using
        BType.SupportedSMT.reduce_toProdl supported_components alphas_nemp
    mspec (Std.Do.Triple.and _
      (castMembership_supported_rep_contract tau
        (zs.map SMT.Term.var).toPairl Denc sigmas.toProdl
        setRep tuple_supported setRep_supported
        (n := St5.env.freshvarsc) (used := St5.env.usedVars)
        (decl := St5.env.declarations)
        typ_tuple typ_Denc_St5
        (by
          intro v hv
          rw [bv_toPairl_nil (ts := zs.map SMT.Term.var)
            (fun t ht => by
              simp only [List.mem_map] at ht
              obtain ⟨z, _, rfl⟩ := ht
              simp [SMT.bv])] at hv
          exact absurd hv List.not_mem_nil)
        (fun v hv => by
          exact St4_sub_St5_used <| St3_sub_St4_used <|
            St1_sub_St3_used (bv_Denc_used v hv)))
      (castMembership_decl
        (zs.map SMT.Term.var).toPairl Denc sigmas.toProdl
        setRep
        (n := St5.env.freshvarsc) (used := St5.env.usedVars)
        (decl := St5.env.declarations)))
    rename_i out_mem
    obtain ⟨mem_enc, sigmaMem⟩ := out_mem
    mrename_i pre
    mintro ∀St6
    mpure pre
    obtain ⟨⟨used_sub_M, types_sub_M, keys_sub_M, sigmaMem_eq,
      typ_mem, fv_tuple_mem, fv_Denc_mem, mem_preserves,
      DltM, mem_decl_eq, mem_ctx, mem_trace, mem_decl_fresh,
      _mem_fv_dep, _mem_specs_fv_dep, mem_sem,
      mem_specs_op, mem_sc_typing⟩,
      ⟨DltM_struct, mem_decl_struct, mem_specs_fv, mem_fv⟩⟩ := pre
    have DltM_struct_eq : DltM = DltM_struct := by
      rw [mem_decl_eq] at mem_decl_struct
      exact List.append_right_injective _ mem_decl_struct
    subst DltM_struct
    change sigmaMem = SMTType.bool at sigmaMem_eq
    subst sigmaMem

    mspec Std.Do.Spec.get_StateT
    mspec Std.Do.Spec.modifyGet_StateT
    beta_reduce
    mspec SMT.eraseVars_forIn_spec (vars := zs)
    mrename_i pre
    mintro ∀St8
    mpure pre
    obtain ⟨St8_types, St8_fvc, St8_used⟩ := pre
    mpure_intro
    have zs_not_St3 : ∀ z ∈ zs, z ∉ St3.types :=
      zs_not_St3_types
    all_goals first
      | have _set_branch := flag_rel
        have St8_types_eq : St8.types = St3.types := by
          rw [St8_types,
            encodeTerm_state.foldl_erase_of_notMem zs zs_not_St3]
      | have _option_branch := sigmas_eq
        have St8_types_eq : St8.types = St3.types := by
          rw [St8_types, PBase_types]
          have hmap : (zs.zip sigmas).map Prod.fst = zs :=
            List.map_fst_zip (le_of_eq zs_len)
          have herase := encodeTerm_state.foldl_erase_foldl_insert
            (zs.zip sigmas) (s := St3.types)
            (by rw [hmap]; exact zs_nodup)
            (by
              intro p hp
              exact zs_not_St3 p.1 (List.mem_fst_of_mem_zip hp))
          rwa [hmap] at herase
    have St6_decl_full : St6.env.declarations =
        PBase.env.declarations ++ (DltP ++ DltM) := by
      rw [mem_decl_eq, St5_decl_eq, P_decl_eq]
      simp only [List.append_assoc]
    have new_decls_eq :
        St6.env.declarations.drop PBase.env.declarations.length =
          DltP ++ DltM := by
      rw [St6_decl_full]
      simp
    have St5_sub_St6_used : St5.env.usedVars ⊆ St6.env.usedVars :=
      used_sub_M
    have used_sub_final : used ⊆ St8.env.usedVars := by
      rw [St8_used]
      exact fun v hv => St5_sub_St6_used <| St4_sub_St5_used <|
        St3_sub_St4_used <| St1_sub_St3_used <| used_sub_D hv
    have types_sub_final : St0.types ⊆ St8.types := by
      rw [St8_types_eq]
      exact fun _ h => St1_sub_St3_types (types_sub_D h)
    have keys_sub_final : St8.types.keys ⊆ St8.env.usedVars := by
      rw [St8_types_eq, St8_used]
      exact fun v hv => St5_sub_St6_used <| St4_sub_St5_used <|
        St3_sub_St4_used (St3_keys_sub hv)
    have covers_final : B.CoversUsedVars St8.env.usedVars
        (B.Term.all vs D P) := by
      intro v hv
      simp only [B.fv, List.mem_append] at hv
      rw [St8_used]
      rcases hv with hD | hP
      · exact St5_sub_St6_used <| St4_sub_St5_used <|
          St3_sub_St4_used <| St1_sub_St3_used (covers_D v hD)
      · rw [List.mem_removeAll_iff] at hP
        exact St5_sub_St6_used <| St4_sub_St5_used (covers_P v hP.1)

    have old_bv_fresh : ∀ (t : SMT.Term) (sigma : SMTType),
        St4.types ⊢ˢ t : sigma →
        (∀ v ∈ SMT.bv t, v ∈ St4.env.usedVars) →
        ∀ v ∈ SMT.bv t, v ∉ St6.types := by
      intro t sigma htyp hbv v hv hmem6
      have hv_not_St5 : v ∉ St5.types :=
        old_bv_not_St5 t sigma htyp hbv v hv
      obtain ⟨tauv, hlookup⟩ := Option.isSome_iff_exists.mp
        (AList.lookup_isSome.mpr hmem6)
      have hentry : (⟨v, tauv⟩ : Sigma fun _ : SMT.𝒱 => SMTType) ∈
          St6.types.entries := AList.mem_lookup_iff.mp hlookup
      rcases List.mem_append.mp (mem_ctx hentry) with hbase | hdecl
      · exact hv_not_St5 <| AList.mem_keys.mpr <|
          List.mem_map.mpr ⟨⟨v, tauv⟩, hbase, rfl⟩
      · exact mem_decl_fresh v
          (mem_declVars_of_mem_declEntries hdecl)
          (St4_sub_St5_used (hbv v hv))
    have typ_Penc_St6 : St6.types ⊢ˢ Penc : SMTType.bool :=
      SMT.Typing.weakening
        (fun e he => types_sub_M (St4_sub_St5_types he)) typ_Penc
        (old_bv_fresh Penc SMTType.bool typ_Penc bv_Penc_used)
    have P_specs_St6 : ∀ b ∈ specBodies DltP,
        St6.types ⊢ˢ b : SMTType.bool := by
      intro b hb
      exact SMT.Typing.weakening
        (fun e he => types_sub_M (St4_sub_St5_types he))
        (P_specs_op b hb)
        (old_bv_fresh b SMTType.bool (P_specs_op b hb)
          (fun v hv => P_delta_bv.2 b hb v hv))
    have all_specs_St6 : ∀ b ∈ specBodies (DltP ++ DltM),
        St6.types ⊢ˢ b : SMTType.bool := by
      intro b hb
      rw [specBodies_append, List.mem_append] at hb
      exact hb.elim (P_specs_St6 b) (mem_specs_op b)
    have vs_zs_len : vs.length = zs.length :=
      vs_sigmas_len.trans zs_len.symm
    have subst_typing : ∀ (t : SMT.Term) (sigma : SMTType),
        St6.types ⊢ˢ t : sigma →
        St6.types ⊢ˢ SMT.substList vs (zs.map SMT.Term.var) t : sigma := by
      intro t sigma htyp
      apply SMT_Typing_substList
      · exact htyp
      · intro q hq
        simp only [List.mem_map] at hq
        obtain ⟨z, _, rfl⟩ := hq
        simp [SMT.bv]
      · intro i hi_vs hi_zs hsome
        have hzs : i < zs.length := by simpa using hi_zs
        have hsig : i < sigmas.length := zs_len ▸ hzs
        have hlookup_z_5 : St5.types.lookup zs[i] = some sigmas[i] :=
          zs_typing i hzs
        have hlookup_z_6 : St6.types.lookup zs[i] = some sigmas[i] :=
          AList.lookup_of_subset types_sub_M hlookup_z_5
        have hlookup_v_3 : St3.types.lookup vs[i] = some sigmas[i] := by
          rw [St3_update]
          exact SMT.TypeContext.lookup_update_of_mem_nodup
            St1.types vs_nodup vs_sigmas_len hi_vs
        have hlookup_v_6 : St6.types.lookup vs[i] = some sigmas[i] :=
          AList.lookup_of_subset
            (fun e he => types_sub_M
              (St4_sub_St5_types (St3_sub_St4_types he)))
            hlookup_v_3
        have hget : (St6.types.lookup vs[i]).get hsome = sigmas[i] := by
          simp [hlookup_v_6]
        rw [hget]
        simpa only [List.getElem_map] using
          SMT.Typing.var St6.types zs[i] sigmas[i] hlookup_z_6
    let raw := SMT.Term.imp mem_enc
      (SMT.substList vs (zs.map SMT.Term.var) Penc)
    let guards := (specBodies (DltP ++ DltM)).map
      (SMT.substList vs (zs.map SMT.Term.var))
    let inner := guards.foldr SMT.Term.imp raw
    let scopedBody := (declBinders (DltP ++ DltM)).foldr
      (fun p t => SMT.Term.forall [p.1] [p.2] t) inner
    have typ_raw : St6.types ⊢ˢ raw : SMTType.bool := by
      exact SMT.Typing.imp _ _ _ typ_mem
        (subst_typing Penc SMTType.bool typ_Penc_St6)
    have typ_guards : ∀ g ∈ guards,
        St6.types ⊢ˢ g : SMTType.bool := by
      intro g hg
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hg
      exact subst_typing b SMTType.bool (all_specs_St6 b hb)
    have typ_inner_St6 : St6.types ⊢ˢ inner : SMTType.bool :=
      SMT.ScopedForall.foldr_imp_typing guards raw typ_guards typ_raw

    all_goals first
      | have _set_branch := flag_rel
        have St5_update : St5.types =
            St4.types.update zs sigmas zs_len := by
          rw [St5_types, SMT.TypeContext.update_eq_zip_foldl]
        obtain ⟨GammaP, traceP_reordered, permP⟩ :=
          P_trace.update_fresh zs sigmas zs_len zs_not_types
        rw [← St5_update] at permP
      | have _option_branch := sigmas_eq
        have PBase_update : PBase.types =
            St3.types.update zs sigmas zs_len := by
          rw [PBase_types, SMT.TypeContext.update_eq_zip_foldl]
        let GammaP := St4.types
        have traceP_reordered : DeclarationContextTrace
            (St3.types.update zs sigmas zs_len) DltP GammaP := by
          simpa [GammaP, PBase_update] using P_trace
        have permP : GammaP.entries.Perm St5.types.entries := by
          exact List.Perm.refl _
    obtain ⟨GammaM, traceM_reordered, permM⟩ :=
      mem_trace.transport_perm permP.symm
    have trace_reordered : DeclarationContextTrace
        (St3.types.update zs sigmas zs_len) (DltP ++ DltM) GammaM :=
      DeclarationContextTrace.append traceP_reordered traceM_reordered
    have typ_inner_reordered : GammaM ⊢ˢ inner : SMTType.bool :=
      SMT.Typing.permute_context permM typ_inner_St6
    have typ_scoped : St3.types.update zs sigmas zs_len ⊢ˢ
        scopedBody : SMTType.bool :=
      SMT.ScopedForall.foldr_decl_forall_typing
        (DltP ++ DltM) inner trace_reordered typ_inner_reordered
    have typ_out_St3 : St3.types ⊢ˢ
        SMT.Term.forall zs sigmas scopedBody : SMTType.bool := by
      refine SMT.Typing.forall St3.types zs sigmas scopedBody
        zs_not_St3 ?_ (List.length_pos_iff.mpr zs_nemp)
        zs_len ?_
      · intro z hz hbv
        exact SMT.Typing.bv_notMem_context typ_scoped z hbv <|
          (SMT.TypeContext.mem_update_iff St3.types z zs sigmas zs_len).mpr
            (.inl hz)
      · exact typ_scoped
    have typ_out : St8.types ⊢ˢ
        SMT.Term.forall zs sigmas scopedBody : SMTType.bool := by
      rwa [St8_types_eq]
    have all_total : EncodeTermRepTotal.{u}
        (B.Term.all vs D P) E BType.bool St0.types
        (SMT.Term.forall zs sigmas scopedBody) SMTType.bool
        St8.types St8.env.usedVars := by
      intro Xi_alt Xi_fv_alt Theta0_alt related_alt wf_alt
        Theta0_alt_none respects_alt Theta0_alt_dom
        T_alt hT_alt den_alt
      have Xi_fv_D_alt : ∀ v ∈ B.fv D,
          (Xi_alt v).isSome = true :=
        fun v hv => Xi_fv_alt v (B.fv.mem_all (.inl hv))
      have related_D_alt : RValuationCastSupportedOnFV
          Xi_alt Theta0_alt D :=
        related_alt.mono_fv fv_D_sub
      have respects_D_alt : B.RenamingContext.RespectsTypeContextOnFV
          Theta0_alt St0.types D :=
        respects_alt.mono_fv fv_D_sub
      have den_alt_inv := den_alt
      simp only [B.Term.abstract] at den_alt_inv
      unfold B.denote at den_alt_inv
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at den_alt_inv
      obtain ⟨⟨Dval_alt, Dty_alt, hDval_alt⟩,
        den_D_alt_raw, den_all_alt_rest⟩ := den_alt_inv
      have den_D_alt0 : ⟦D.abstract Xi_alt Xi_fv_D_alt⟧ᴮ =
          some ⟨Dval_alt, ⟨Dty_alt, hDval_alt⟩⟩ := by
        convert den_D_alt_raw using 2
      have Dty_alt_eq : Dty_alt = BType.set tau := by
        exact (denote_welltyped_eq
          (t := D.abstract Xi_alt Xi_fv_D_alt)
          ⟨_, WFTC.of_abstract, BType.set tau,
            by convert Typing.of_abstract Xi_fv_D_alt typ_D⟩
          den_D_alt0).symm
      subst Dty_alt
      have den_D_alt : ⟦D.abstract Xi_alt Xi_fv_D_alt⟧ᴮ =
          some ⟨Dval_alt, ⟨BType.set tau, hDval_alt⟩⟩ := den_D_alt0
      have Theta0_alt_none_D : ∀ v ∉ St1.env.usedVars,
          Theta0_alt v = none := by
        intro v hv
        by_contra hne
        have hv_St0 : v ∈ St0.types := Theta0_alt_dom v hne
        have hv_used : v ∈ used := by
          rw [← St0_used_eq]
          exact St0_sub hv_St0
        exact hv (used_sub_D hv_used)
      obtain ⟨ThetaD_alt, hcov_D_alt, denDenc_alt,
          ThetaD_alt_ext, related_D_alt_out, ThetaD_alt_none,
          respects_D_alt_out, target_respects_D_alt, ThetaD_alt_dom,
          hden_Denc_alt, hdenDenc_alt_type, D_alt_rel⟩ :=
        D_total Xi_alt Xi_fv_D_alt Theta0_alt related_D_alt wf_alt
          Theta0_alt_none_D respects_D_alt Theta0_alt_dom
          Dval_alt hDval_alt den_D_alt
      let XiP_alt := Function.updates Xi_alt vs
        (List.ofFn fun i => some (bs i))
      let ThetaP_alt := Function.updates ThetaD_alt vs
        (List.ofFn fun i => some (ss i))
      have related_ambient_alt : ∀ v ∈ B.fv P, v ∉ vs →
          match Xi_alt v, ThetaD_alt v with
          | some d, some d' => RDomCastSupported d d'
          | _, _ => False := by
        intro v hv hvs
        exact related_alt.of_extends ThetaD_alt_ext v
          (B.fv.mem_all (.inr ⟨hv, hvs⟩))
      have related_P_alt : RValuationCastSupportedOnFV
          XiP_alt ThetaP_alt P := by
        simpa [XiP_alt, ThetaP_alt, bs, ss] using
          (RValuationCastSupportedOnFV.updates_of_reduce_toProdl
            vs_nodup alphas_nemp vs_alphas_len alphas_sigmas_len
            hXrun hYrun run_rel related_ambient_alt (t := P))
      have XiP_fv_alt : ∀ v ∈ B.fv P,
          (XiP_alt v).isSome = true := by
        intro v hv
        by_cases hvs : v ∈ vs
        · change (Function.updates Xi_alt vs
            (List.ofFn fun i => some (bs i)) v).isSome = true
          rw [Function.updates_eq_if (by simp) vs_nodup, dif_pos hvs]
          simp
        · change (Function.updates Xi_alt vs
            (List.ofFn fun i => some (bs i)) v).isSome = true
          rw [Function.updates_of_not_mem Xi_alt vs _ v hvs]
          exact Xi_fv_alt v (B.fv.mem_all (.inr ⟨hv, hvs⟩))
      have wf_P_alt : B.RenWF
          (vs.zipToAList alphas ∪ E.context) XiP_alt :=
        B.RenWF.updates_ofFn wf_alt vs_nodup vs_context_disj
          vs_alphas_len (fun _ => rfl)
      obtain ⟨Pval_alt, hPval_alt, den_P_alt⟩ :=
        B.denote_exists_of_typing typ_P XiP_alt XiP_fv_alt
          (@WFTC.wf _ WFTC.of_abstract)
          (wd_P.toPHOAS XiP_alt XiP_fv_alt)
      have ThetaP_alt_none : ∀ v ∉ St3.env.usedVars,
          ThetaP_alt v = none := by
        intro v hv
        have hv_vs : v ∉ vs := by
          intro hvs
          exact hv <| St1_sub_St3_used <| used_sub_D <|
            vars_used_vs v hvs
        change Function.updates ThetaD_alt vs
          (List.ofFn fun i => some (ss i)) v = none
        rw [Function.updates_of_not_mem ThetaD_alt vs _ v hv_vs]
        exact ThetaD_alt_none v (fun h => hv (St1_sub_St3_used h))
      have ThetaP_alt_dom : ∀ v, ThetaP_alt v ≠ none →
          v ∈ St3.types := by
        intro v hv
        by_cases hvs : v ∈ vs
        · rw [St3_update]
          exact (SMT.TypeContext.mem_update_iff
            St1.types v vs sigmas vs_sigmas_len).mpr (.inl hvs)
        · change Function.updates ThetaD_alt vs
            (List.ofFn fun i => some (ss i)) v ≠ none at hv
          rw [Function.updates_of_not_mem ThetaD_alt vs _ v hvs] at hv
          exact AList.mem_of_subset St1_sub_St3_types
            (ThetaD_alt_dom v hv)
      have respects_P_alt : B.RenamingContext.RespectsTypeContextOnFV
          ThetaP_alt St3.types P := by
        intro v sigma hv hlookup
        by_cases hvs : v ∈ vs
        · let i : Fin vs.length :=
            ⟨vs.idxOf v, List.idxOf_lt_length_of_mem hvs⟩
          have hvi : vs[i] = v :=
            List.getElem_idxOf (List.idxOf_lt_length_of_mem hvs)
          have hctx : St3.types.lookup vs[i] =
              some sigmas[Fin.cast vs_sigmas_len i] := by
            rw [St3_update]
            exact SMT.TypeContext.lookup_update_of_mem_nodup
              St1.types vs_nodup vs_sigmas_len i.isLt
          rw [hvi] at hctx
          rw [hctx] at hlookup
          cases hlookup
          refine ⟨ss i, ?_, rfl⟩
          change Function.updates ThetaD_alt vs
            (List.ofFn fun i => some (ss i)) v = some (ss i)
          rw [Function.updates_eq_if (by simp) vs_nodup, dif_pos hvs]
          simpa [i, hvi]
        · have hv_all : v ∈ B.fv (B.Term.all vs D P) :=
            B.fv.mem_all (.inr ⟨hv, hvs⟩)
          have hv_St0 := fv_in_Lambda v hv_all
          obtain ⟨sigma0, hsigma0⟩ := Option.isSome_iff_exists.mp
            (AList.lookup_isSome.mpr hv_St0)
          have hsigma1 : St1.types.lookup v = some sigma0 :=
            AList.lookup_of_subset types_sub_D hsigma0
          have hsigma3 : St3.types.lookup v = some sigma0 := by
            rw [St3_update,
              SMT.TypeContext.lookup_update St1.types v vs sigmas
                vs_sigmas_len hvs]
            exact hsigma1
          rw [hsigma3] at hlookup
          cases hlookup
          obtain ⟨d, hd, hdty⟩ := respects_alt hv_all hsigma0
          refine ⟨d, ?_, hdty⟩
          change Function.updates ThetaD_alt vs
            (List.ofFn fun i => some (ss i)) v = some d
          rw [Function.updates_of_not_mem ThetaD_alt vs _ v hvs]
          exact ThetaD_alt_ext hd
      let wZ : Fin zs.length → SMT.Dom.{u} := fun i =>
        ss (Fin.cast vs_zs_len.symm i)
      have respects_P_alt_base :
          B.RenamingContext.RespectsTypeContextOnFV
            ThetaP_alt PBase.types P :=
        respects_P_alt.transport_fv (fun _ h => h)
          St3_sub_PBase_types fv_P_in_St3
      have ThetaP_alt_dom_base : ∀ v, ThetaP_alt v ≠ none →
          v ∈ PBase.types := by
        intro v hv
        exact AList.mem_of_subset St3_sub_PBase_types
          (ThetaP_alt_dom v hv)
      have ThetaP_alt_ext_D : SMT.RenamingContext.Extends
          ThetaP_alt ThetaD_alt := by
        intro v d hd
        by_cases hvs : v ∈ vs
        · have hv_ctx := ThetaD_alt_dom v (by rw [hd]; simp)
          exact absurd hv_ctx (vs_disj_St1 v hvs)
        · change Function.updates ThetaD_alt vs
            (List.ofFn fun i => some (ss i)) v = some d
          rw [Function.updates_of_not_mem ThetaD_alt vs _ v hvs]
          exact hd
      all_goals first
        | have _set_branch := flag_rel
          obtain ⟨ThetaBody_alt, hcov_P_alt, denPenc_alt,
              ThetaBody_alt_ext, related_P_alt_out, ThetaBody_alt_none,
              respects_P_alt_out, target_respects_P_alt, ThetaBody_alt_dom,
              P_specs_alt, hden_Penc_alt, hdenPenc_alt_type, P_alt_rel⟩ :=
            P_sc_total XiP_alt XiP_fv_alt ThetaP_alt related_P_alt
              wf_P_alt
              (fun v hv => ThetaP_alt_none v
                (fun h => hv (St3_sub_St4_used h)))
              respects_P_alt_base ThetaP_alt_dom_base
              Pval_alt hPval_alt den_P_alt
          have ThetaBody_alt_ext_P : SMT.RenamingContext.Extends
              ThetaBody_alt ThetaP_alt := ThetaBody_alt_ext
          have ThetaBody_alt_ext_D : SMT.RenamingContext.Extends
              ThetaBody_alt ThetaD_alt :=
            SMT.RenamingContext.extends_trans ThetaBody_alt_ext
              ThetaP_alt_ext_D
          let ThetaZ_alt := Function.updates ThetaBody_alt zs
            (List.ofFn fun i => some (wZ i))
          have ThetaZ_alt_ext : SMT.RenamingContext.Extends
              ThetaZ_alt ThetaBody_alt := by
            intro v d hd
            by_cases hzs : v ∈ zs
            · have hv_ctx := ThetaBody_alt_dom v (by rw [hd]; simp)
              exact absurd hv_ctx (zs_not_types v hzs)
            · change Function.updates ThetaBody_alt zs
                (List.ofFn fun i => some (wZ i)) v = some d
              rw [Function.updates_of_not_mem ThetaBody_alt zs _ v hzs]
              exact hd
          have ThetaZ_alt_ext_D : SMT.RenamingContext.Extends
              ThetaZ_alt ThetaD_alt :=
            SMT.RenamingContext.extends_trans ThetaZ_alt_ext
              ThetaBody_alt_ext_D
          have ThetaZ_alt_none : ∀ v ∉ St5.env.usedVars,
              ThetaZ_alt v = none := by
            intro v hv
            have hv_zs : v ∉ zs := fun hzs =>
              hv (zs_mem_St5_used v hzs)
            change Function.updates ThetaBody_alt zs
              (List.ofFn fun i => some (wZ i)) v = none
            rw [Function.updates_of_not_mem ThetaBody_alt zs _ v hv_zs]
            exact ThetaBody_alt_none v
              (fun hv4 => hv (St4_sub_St5_used hv4))
          have ThetaZ_alt_dom : ∀ v, ThetaZ_alt v ≠ none →
              v ∈ St5.types := by
            intro v hv
            by_cases hzs : v ∈ zs
            · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hzs
              exact AList.lookup_isSome.mp <| by
                rw [zs_typing i hi]
                rfl
            · change Function.updates ThetaBody_alt zs
                (List.ofFn fun i => some (wZ i)) v ≠ none at hv
              rw [Function.updates_of_not_mem ThetaBody_alt zs _ v hzs] at hv
              exact AList.mem_of_subset St4_sub_St5_types
                (ThetaBody_alt_dom v hv)
          have ThetaZ_alt_at_z : ∀ (i : ℕ) (hi : i < zs.length),
              ThetaZ_alt zs[i] = some (wZ ⟨i, hi⟩) := by
            intro i hi
            change Function.updates ThetaBody_alt zs
              (List.ofFn fun i => some (wZ i)) zs[i] =
                some (wZ ⟨i, hi⟩)
            rw [Function.updates_eq_if (by simp) zs_nodup,
              dif_pos (List.getElem_mem hi)]
            simp [List.Nodup.idxOf_getElem zs_nodup]
        | have _option_branch := sigmas_eq
          let ThetaP_run := Function.updates ThetaP_alt zs
            (List.ofFn fun i => some (wZ i))
          have zs_not_fv_P : ∀ z ∈ zs, z ∉ B.fv P := by
            intro z hz hfv
            exact zs_not_St3_used z hz
              (vars_used_P_St3 z (B.Term.mem_vars_iff.mpr (.inl hfv)))
          have related_P_run : RValuationCastSupportedOnFV
              XiP_alt ThetaP_run P := by
            intro v hv
            have hvz : v ∉ zs := fun hz => zs_not_fv_P v hz hv
            simpa [ThetaP_run,
              Function.updates_of_not_mem ThetaP_alt zs _ v hvz] using
              related_P_alt v hv
          have ThetaP_run_none : ∀ v ∉ PBase.env.usedVars,
              ThetaP_run v = none := by
            intro v hv
            have hvz : v ∉ zs := fun hz => hv <| by
              rw [PBase_used]
              exact List.mem_append_left _ (List.mem_reverse.mpr hz)
            change Function.updates ThetaP_alt zs
              (List.ofFn fun i => some (wZ i)) v = none
            rw [Function.updates_of_not_mem ThetaP_alt zs _ v hvz]
            exact ThetaP_alt_none v
              (fun h3 => hv (St3_sub_PBase_used h3))
          have ThetaP_run_dom : ∀ v, ThetaP_run v ≠ none →
              v ∈ PBase.types := by
            intro v hv
            by_cases hvz : v ∈ zs
            · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hvz
              exact AList.lookup_isSome.mp <| by
                rw [zs_typing_helper (St₅types := PBase.types)
                  zs_nodup zs_len PBase_types i hi]
                rfl
            · change Function.updates ThetaP_alt zs
                (List.ofFn fun i => some (wZ i)) v ≠ none at hv
              rw [Function.updates_of_not_mem ThetaP_alt zs _ v hvz] at hv
              exact ThetaP_alt_dom_base v hv
          have respects_P_run :
              B.RenamingContext.RespectsTypeContextOnFV
                ThetaP_run PBase.types P := by
            intro v sigma hv hlookup
            obtain ⟨d, hd, hdtype⟩ := respects_P_alt_base hv hlookup
            refine ⟨d, ?_, hdtype⟩
            have hvz : v ∉ zs := fun hz => zs_not_fv_P v hz hv
            change Function.updates ThetaP_alt zs
              (List.ofFn fun i => some (wZ i)) v = some d
            rw [Function.updates_of_not_mem ThetaP_alt zs _ v hvz]
            exact hd
          have ThetaP_run_ext_D : SMT.RenamingContext.Extends
              ThetaP_run ThetaD_alt := by
            intro v d hd
            have hvz : v ∉ zs := by
              intro hz
              have hv1 := ThetaD_alt_dom v (by rw [hd]; simp)
              exact zs_not_St3_types v hz
                (AList.mem_of_subset St1_sub_St3_types hv1)
            change Function.updates ThetaP_alt zs
              (List.ofFn fun i => some (wZ i)) v = some d
            rw [Function.updates_of_not_mem ThetaP_alt zs _ v hvz]
            exact ThetaP_alt_ext_D hd
          have ThetaP_run_ext_alt : SMT.RenamingContext.Extends
              ThetaP_run ThetaP_alt := by
            intro v d hd
            have hvz : v ∉ zs := by
              intro hz
              exact zs_not_St3_types v hz
                (ThetaP_alt_dom v (by rw [hd]; simp))
            change Function.updates ThetaP_alt zs
              (List.ofFn fun i => some (wZ i)) v = some d
            rw [Function.updates_of_not_mem ThetaP_alt zs _ v hvz]
            exact hd
          obtain ⟨ThetaBody_alt, hcov_P_alt, denPenc_alt,
              ThetaBody_alt_ext, related_P_alt_out, ThetaBody_alt_none,
              respects_P_alt_out, target_respects_P_alt, ThetaBody_alt_dom,
              P_specs_alt, hden_Penc_alt, hdenPenc_alt_type, P_alt_rel⟩ :=
            P_sc_total XiP_alt XiP_fv_alt ThetaP_run related_P_run
              wf_P_alt
              (fun v hv => ThetaP_run_none v
                (fun h => hv (used_sub_P h)))
              respects_P_run ThetaP_run_dom
              Pval_alt hPval_alt den_P_alt
          have ThetaBody_alt_ext_P : SMT.RenamingContext.Extends
              ThetaBody_alt ThetaP_alt :=
            SMT.RenamingContext.extends_trans ThetaBody_alt_ext
              ThetaP_run_ext_alt
          have ThetaBody_alt_ext_D : SMT.RenamingContext.Extends
              ThetaBody_alt ThetaD_alt :=
            SMT.RenamingContext.extends_trans ThetaBody_alt_ext
              ThetaP_run_ext_D
          let ThetaZ_alt := Function.updates ThetaBody_alt zs
            (List.ofFn fun i => some (wZ i))
          have ThetaZ_alt_eq : ThetaZ_alt = ThetaBody_alt := by
            funext v
            by_cases hvz : v ∈ zs
            · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hvz
              have hbody : ThetaBody_alt zs[i] = some (wZ ⟨i, hi⟩) := by
                apply ThetaBody_alt_ext
                change Function.updates ThetaP_alt zs
                  (List.ofFn fun i => some (wZ i)) zs[i] =
                    some (wZ ⟨i, hi⟩)
                rw [Function.updates_eq_if (by simp) zs_nodup,
                  dif_pos (List.getElem_mem hi)]
                simp [List.Nodup.idxOf_getElem zs_nodup]
              change Function.updates ThetaBody_alt zs
                (List.ofFn fun i => some (wZ i)) zs[i] = ThetaBody_alt zs[i]
              rw [Function.updates_eq_if (by simp) zs_nodup,
                dif_pos (List.getElem_mem hi)]
              simpa [List.Nodup.idxOf_getElem zs_nodup] using hbody.symm
            · change Function.updates ThetaBody_alt zs
                (List.ofFn fun i => some (wZ i)) v = ThetaBody_alt v
              rw [Function.updates_of_not_mem ThetaBody_alt zs _ v hvz]
          have ThetaZ_alt_ext : SMT.RenamingContext.Extends
              ThetaZ_alt ThetaBody_alt := by
            rw [ThetaZ_alt_eq]
            exact SMT.RenamingContext.extends_refl _
          have ThetaZ_alt_ext_D : SMT.RenamingContext.Extends
              ThetaZ_alt ThetaD_alt :=
            SMT.RenamingContext.extends_trans ThetaZ_alt_ext
              ThetaBody_alt_ext_D
          have ThetaZ_alt_none : ∀ v ∉ St5.env.usedVars,
              ThetaZ_alt v = none := by
            rw [ThetaZ_alt_eq]
            exact ThetaBody_alt_none
          have ThetaZ_alt_dom : ∀ v, ThetaZ_alt v ≠ none →
              v ∈ St5.types := by
            rw [ThetaZ_alt_eq]
            exact ThetaBody_alt_dom
          have ThetaZ_alt_at_z : ∀ (i : ℕ) (hi : i < zs.length),
              ThetaZ_alt zs[i] = some (wZ ⟨i, hi⟩) := by
            intro i hi
            change Function.updates ThetaBody_alt zs
              (List.ofFn fun i => some (wZ i)) zs[i] =
                some (wZ ⟨i, hi⟩)
            rw [Function.updates_eq_if (by simp) zs_nodup,
              dif_pos (List.getElem_mem hi)]
            simp [List.Nodup.idxOf_getElem zs_nodup]
      have target_respects_tuple_alt :
          SMT.RenamingContext.RespectsTypeContextOnFV
            ThetaZ_alt St5.types (zs.map SMT.Term.var).toPairl := by
        intro v sigma hv hlookup
        have hv_zs := fv_pairl_sub_zs_helper zs v hv
        obtain ⟨i, hi, hvi⟩ := List.mem_iff_getElem.mp hv_zs
        subst v
        have hlookup_i := zs_typing i hi
        rw [hlookup_i] at hlookup
        cases hlookup
        refine ⟨wZ ⟨i, hi⟩, ?_, ?_⟩
        · exact ThetaZ_alt_at_z i hi
        · dsimp [wZ, ss]
      have hcov_tuple_alt : SMT.RenamingContext.CoversFV
          ThetaZ_alt (zs.map SMT.Term.var).toPairl := by
        intro v hv
        obtain ⟨sigma, hlookup⟩ := Option.isSome_iff_exists.mp <|
          AList.lookup_isSome.mpr
            (SMT.Typing.mem_context_of_mem_fv typ_tuple hv)
        obtain ⟨d, hd, _⟩ := target_respects_tuple_alt hv hlookup
        rw [hd]
        rfl
      obtain ⟨denTuple_alt, hden_tuple_alt, hdenTuple_alt_type⟩ :=
        SMT.RenamingContext.denote_exists_of_typing_fv typ_tuple
          target_respects_tuple_alt hcov_tuple_alt
      rcases denTuple_alt with ⟨Ytuple_alt, tupleTy_alt, hYtuple_alt⟩
      dsimp at hdenTuple_alt_type
      subst tupleTy_alt
      let tuple_le : sigmas.toProdl ⊑ tau.toSMTType :=
        castable?_of_castPath tuple_supported.toCanonicalCastPath
      let Xtuple_alt := retract_castZF tau tuple_le Ytuple_alt
      have hXtuple_alt : Xtuple_alt ∈ ⟦tau⟧ᶻ :=
        retract_castZF_mem tau tuple_le hYtuple_alt
      have tuple_alt_rel : RDomCast
          (⟨Xtuple_alt, tau, hXtuple_alt⟩ : B.Dom)
          (⟨Ytuple_alt, sigmas.toProdl, hYtuple_alt⟩ : SMT.Dom) := by
        exact ⟨tuple_le.toCastPath, rfl⟩
      have tuple_alt_supported : RDomCastSupported
          (⟨Xtuple_alt, tau, hXtuple_alt⟩ : B.Dom)
          (⟨Ytuple_alt, sigmas.toProdl, hYtuple_alt⟩ : SMT.Dom) :=
        ⟨RDomCast.toRDomCastAdmissible_of_supported tuple_alt_rel
            tuple_supported,
          tuple_supported⟩
      have target_respects_D_Z :
          SMT.RenamingContext.RespectsTypeContextOnFV
            ThetaZ_alt St5.types Denc :=
        target_respects_D_alt.of_extends ThetaZ_alt_ext_D
          St1_sub_St5_types typ_Denc
      have hcov_D_Z : SMT.RenamingContext.CoversFV ThetaZ_alt Denc := by
        intro v hv
        obtain ⟨sigma, hlookup⟩ := Option.isSome_iff_exists.mp <|
          AList.lookup_isSome.mpr
            (SMT.Typing.mem_context_of_mem_fv typ_Denc_St5 hv)
        obtain ⟨d, hd, _⟩ := target_respects_D_Z hv hlookup
        rw [hd]
        rfl
      have hden_Denc_Z : ⟦Denc.abstract ThetaZ_alt hcov_D_Z⟧ˢ =
          some denDenc_alt := by
        have hag := SMT.RenamingContext.agreesOnFV_of_extends_of_coversFV
          ThetaZ_alt_ext_D hcov_D_alt
        exact (SMT.RenamingContext.denote_congr_of_agreesOnFV
          (t := Denc) (h1 := hcov_D_Z) (h2 := hcov_D_alt)
          hag).trans hden_Denc_alt
      have target_respects_tuple_St6 :
          SMT.RenamingContext.RespectsTypeContextOnFV
            ThetaZ_alt St6.types (zs.map SMT.Term.var).toPairl :=
        target_respects_tuple_alt.of_extends
          (SMT.RenamingContext.extends_refl ThetaZ_alt)
          types_sub_M typ_tuple
      have target_respects_D_St6 :
          SMT.RenamingContext.RespectsTypeContextOnFV
            ThetaZ_alt St6.types Denc :=
        target_respects_D_Z.of_extends
          (SMT.RenamingContext.extends_refl ThetaZ_alt)
          types_sub_M typ_Denc_St5
      have ThetaZ_alt_dom_St6 : ∀ v, ThetaZ_alt v ≠ none →
          v ∈ St6.types :=
        fun v hv => AList.mem_of_subset types_sub_M (ThetaZ_alt_dom v hv)
      obtain ⟨mem_good_alt, mem_guard_alt⟩ :=
        mem_sem St6.types (fun _ h => h) ThetaZ_alt
          hcov_tuple_alt hcov_D_Z ThetaZ_alt_none
          target_respects_tuple_St6 target_respects_D_St6
          ThetaZ_alt_dom_St6
          Xtuple_alt Dval_alt hXtuple_alt hDval_alt
          (⟨Ytuple_alt, sigmas.toProdl, hYtuple_alt⟩ : SMT.Dom)
          denDenc_alt hden_tuple_alt hden_Denc_Z rfl
          hdenDenc_alt_type tuple_alt_supported D_alt_rel
      obtain ⟨ThetaM_alt, hcov_mem_alt, denMem_alt,
          ThetaM_alt_ext, ThetaM_alt_none, target_respects_mem_alt,
          ThetaM_alt_dom, M_specs_alt, hden_mem_alt,
          hdenMem_alt_type, mem_alt_iff⟩ := mem_good_alt
      have St4_sub_St6_types : St4.types ⊆ St6.types :=
        fun e he => types_sub_M (St4_sub_St5_types he)
      have St6_sub_GammaM : St6.types ⊆ GammaM := by
        intro e he
        exact permM.mem_iff.mp he
      have St4_sub_GammaM : St4.types ⊆ GammaM :=
        fun e he => St6_sub_GammaM (St4_sub_St6_types he)
      have ThetaM_alt_ext_Body : SMT.RenamingContext.Extends
          ThetaM_alt ThetaBody_alt :=
        SMT.RenamingContext.extends_trans ThetaM_alt_ext ThetaZ_alt_ext
      have ThetaM_alt_ext_P : SMT.RenamingContext.Extends
          ThetaM_alt ThetaP_alt :=
        SMT.RenamingContext.extends_trans ThetaM_alt_ext_Body
          ThetaBody_alt_ext_P
      have ThetaM_alt_ext_D : SMT.RenamingContext.Extends
          ThetaM_alt ThetaD_alt :=
        SMT.RenamingContext.extends_trans ThetaM_alt_ext ThetaZ_alt_ext_D
      have P_specs_M : SpecBodiesTrue ThetaM_alt GammaM DltP :=
        P_specs_alt.of_extends ThetaM_alt_ext_Body St4_sub_GammaM
          ThetaBody_alt_dom
      have M_specs_M : SpecBodiesTrue ThetaM_alt GammaM DltM :=
        M_specs_alt.of_extends
          (SMT.RenamingContext.extends_refl ThetaM_alt)
          St6_sub_GammaM ThetaM_alt_dom
      have all_specs_M : SpecBodiesTrue ThetaM_alt GammaM
          (DltP ++ DltM) :=
        SpecBodiesTrue.append P_specs_M M_specs_M
      have target_respects_P_M :
          SMT.RenamingContext.RespectsTypeContextOnFV
            ThetaM_alt GammaM Penc :=
        target_respects_P_alt.of_extends ThetaM_alt_ext_Body
          St4_sub_GammaM typ_Penc
      have target_respects_mem_M :
          SMT.RenamingContext.RespectsTypeContextOnFV
            ThetaM_alt GammaM mem_enc :=
        target_respects_mem_alt.of_extends
          (SMT.RenamingContext.extends_refl ThetaM_alt)
          St6_sub_GammaM typ_mem
      have zs_disj_vs : ∀ z ∈ zs, z ∉ vs := by
        intro z hz hvs
        exact zs_not_St3_used z hz <| St1_sub_St3_used <|
          used_sub_D <| vars_used_vs z hvs
      have vs_mem_St5_used : ∀ v ∈ vs, v ∈ St5.env.usedVars := by
        intro v hv
        exact St4_sub_St5_used <| St3_sub_St4_used <|
          St1_sub_St3_used <| used_sub_D <| vars_used_vs v hv
      have vs_not_fv_tuple : ∀ v ∈ vs,
          v ∉ SMT.fv (zs.map SMT.Term.var).toPairl := by
        intro v hv htuple
        have hz := fv_pairl_sub_zs_helper zs v htuple
        exact zs_disj_vs v hz hv
      have vs_not_fv_Denc : ∀ v ∈ vs, v ∉ SMT.fv Denc := by
        intro v hv hDenc
        exact vs_disj_St1 v hv <|
          SMT.Typing.mem_context_of_mem_fv typ_Denc hDenc
      have vs_not_declM : ∀ v ∈ vs, v ∉ declVars DltM := by
        intro v hv hdecl
        exact mem_decl_fresh v hdecl (vs_mem_St5_used v hv)
      have vs_not_fv_mem : ∀ v ∈ vs, v ∉ SMT.fv mem_enc := by
        intro v hv hmem
        have hscope := mem_fv hmem
        simp only [List.mem_union_iff] at hscope
        rcases hscope with (htuple | hDenc) | hdecl
        · exact vs_not_fv_tuple v hv htuple
        · exact vs_not_fv_Denc v hv hDenc
        · exact vs_not_declM v hv hdecl
      have vs_not_fv_M_specs : ∀ b ∈ specBodies DltM,
          ∀ v ∈ vs, v ∉ SMT.fv b := by
        intro b hb v hv hbody
        have hscope := mem_specs_fv b hb hbody
        simp only [List.mem_union_iff] at hscope
        rcases hscope with (htuple | hDenc) | hdecl
        · exact vs_not_fv_tuple v hv htuple
        · exact vs_not_fv_Denc v hv hDenc
        · exact vs_not_declM v hv hdecl
      have vs_not_fv_subst : ∀ (t : SMT.Term) (v : SMT.𝒱), v ∈ vs →
          v ∉ SMT.fv (SMT.substList vs (zs.map SMT.Term.var) t) := by
        intro t v hv
        apply SMT_not_mem_fv_substList_of_mem_vars
          (by simpa [vs_zs_len]) hv
        intro q hq
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hq
        simp only [SMT.fv, List.mem_singleton]
        intro hvz
        subst z
        exact zs_disj_vs v hz hv
      have vs_not_fv_guards : ∀ g ∈ guards,
          ∀ v ∈ vs, v ∉ SMT.fv g := by
        intro g hg
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hg
        exact vs_not_fv_subst b
      have vs_not_fv_raw : ∀ v ∈ vs, v ∉ SMT.fv raw := by
        intro v hv hraw
        simp only [raw, SMT.fv, List.mem_append] at hraw
        exact hraw.elim (vs_not_fv_mem v hv)
          (vs_not_fv_subst Penc v hv)
      have vs_not_fv_inner : ∀ v ∈ vs, v ∉ SMT.fv inner := by
        intro v hv
        have foldr_no : ∀ gs : List SMT.Term,
            (∀ g ∈ gs, v ∉ SMT.fv g) →
            v ∉ SMT.fv (gs.foldr SMT.Term.imp raw) := by
          intro gs
          induction gs with
          | nil =>
              intro _
              exact vs_not_fv_raw v hv
          | cons g gs ih =>
              intro hguards hmem
              simp only [List.foldr_cons, SMT.fv,
                List.mem_append] at hmem
              exact hmem.elim
                (hguards g (List.mem_cons_self))
                (ih (fun q hq =>
                  hguards q (List.mem_cons_of_mem g hq)))
        exact foldr_no guards (fun g hg => vs_not_fv_guards g hg v hv)
      have ThetaM_at_vs : ∀ (i : ℕ) (hi : i < vs.length),
          ThetaM_alt vs[i] = some (ss ⟨i, hi⟩) := by
        intro i hi
        apply ThetaM_alt_ext_P
        change Function.updates ThetaD_alt vs
          (List.ofFn fun i => some (ss i)) vs[i] = some (ss ⟨i, hi⟩)
        rw [Function.updates_eq_if (by simp) vs_nodup,
          dif_pos (List.getElem_mem hi)]
        simp [List.Nodup.idxOf_getElem vs_nodup]
      have ThetaM_at_zs : ∀ (i : ℕ) (hi : i < zs.length),
          ThetaM_alt zs[i] = some (wZ ⟨i, hi⟩) := by
        intro i hi
        apply ThetaM_alt_ext
        exact ThetaZ_alt_at_z i hi
      have updates_vs_ThetaM : Function.updates ThetaM_alt vs
          ((List.ofFn ss).map Option.some) = ThetaM_alt := by
        funext v
        by_cases hvs : v ∈ vs
        · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hvs
          rw [Function.updates_eq_if (by simp) vs_nodup,
            dif_pos (List.getElem_mem hi)]
          simp [List.Nodup.idxOf_getElem vs_nodup, ThetaM_at_vs i hi]
        · exact Function.updates_of_not_mem ThetaM_alt vs _ v hvs
      have hzs_for_subst : ∀ (i : ℕ) (hi_z : i < zs.length)
          (hi_w : i < (List.ofFn ss).length),
          ThetaM_alt zs[i] = some (List.ofFn ss)[i] := by
        intro i hi_z hi_w
        rw [ThetaM_at_zs i hi_z]
        have hfin : Fin.cast vs_zs_len.symm ⟨i, hi_z⟩ =
            ⟨i, by simpa using hi_w⟩ := by
          apply Fin.ext
          rfl
        simp [wZ, hfin]
      have hzs_type_GammaM : ∀ (i : ℕ) (hi_z : i < zs.length)
          (hi_w : i < (List.ofFn ss).length) (sigma : SMTType),
          GammaM.lookup zs[i] = some sigma →
            ((List.ofFn ss)[i]).snd.fst = sigma := by
        intro i hi_z hi_w sigma hlookup
        have hlookup_base :
            (St3.types.update zs sigmas zs_len).lookup zs[i] =
              some (sigmas[i]'(zs_len ▸ hi_z)) :=
          SMT.TypeContext.lookup_update_of_mem_nodup St3.types
            zs_nodup zs_len hi_z
        have hlookup_final : GammaM.lookup zs[i] =
            some (sigmas[i]'(zs_len ▸ hi_z)) :=
          AList.lookup_of_subset trace_reordered.entries_subset hlookup_base
        rw [hlookup_final] at hlookup
        cases hlookup
        have hget : (List.ofFn ss)[i] = ss ⟨i, by simpa using hi_w⟩ :=
          List.getElem_ofFn (f := ss) (h := hi_w)
        rw [hget]
        let j : Fin vs.length := ⟨i, by simpa using hi_w⟩
        let k : Fin sigmas.length := ⟨i, zs_len ▸ hi_z⟩
        change (ss j).snd.fst = sigmas[k]
        dsimp [ss]
      have target_respects_subst_P :
          SMT.RenamingContext.RespectsTypeContextOnFV ThetaM_alt GammaM
            (SMT.substList vs (zs.map SMT.Term.var) Penc) := by
        apply SMT.ScopedForall.respects_substList_vars Penc vs zs
          (List.ofFn ss) vs_zs_len (by simp) zs_disj_vs
          hzs_for_subst hzs_type_GammaM
        rwa [updates_vs_ThetaM]
      have target_respects_subst_specs : ∀ b ∈ specBodies (DltP ++ DltM),
          SMT.RenamingContext.RespectsTypeContextOnFV ThetaM_alt GammaM
            (SMT.substList vs (zs.map SMT.Term.var) b) := by
        intro b hb
        obtain ⟨_, _, hresp_b, _, _, _⟩ := all_specs_M b hb
        apply SMT.ScopedForall.respects_substList_vars b vs zs
          (List.ofFn ss) vs_zs_len (by simp) zs_disj_vs
          hzs_for_subst hzs_type_GammaM
        rw [updates_vs_ThetaM]
        exact hresp_b
      have target_respects_raw :
          SMT.RenamingContext.RespectsTypeContextOnFV
            ThetaM_alt GammaM raw := by
        intro v sigma hv hlookup
        simp only [raw, SMT.fv, List.mem_append] at hv
        exact hv.elim
          (fun h => target_respects_mem_M h hlookup)
          (fun h => target_respects_subst_P h hlookup)
      have target_respects_guards : ∀ g ∈ guards,
          SMT.RenamingContext.RespectsTypeContextOnFV
            ThetaM_alt GammaM g := by
        intro g hg
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hg
        exact target_respects_subst_specs b hb
      have target_respects_inner :
          SMT.RenamingContext.RespectsTypeContextOnFV
            ThetaM_alt GammaM inner := by
        exact SMT.ScopedForall.foldr_imp_respects guards raw
          target_respects_guards target_respects_raw
      have target_respects_scoped_M :
          SMT.RenamingContext.RespectsTypeContextOnFV ThetaM_alt
            (St3.types.update zs sigmas zs_len) scopedBody :=
        SMT.ScopedForall.respects_foldr_decl_forall
          (DltP ++ DltM) inner trace_reordered target_respects_inner
      have target_respects_out_M :
          SMT.RenamingContext.RespectsTypeContextOnFV ThetaM_alt St3.types
            (SMT.Term.forall zs sigmas scopedBody) :=
        SMT.ScopedForall.respects_forall_of_body zs_len
          target_respects_scoped_M
      let boundNames := zs ++ declVars (DltP ++ DltM)
      let ThetaOuter_alt : SMT.RenamingContext.Context.{u} := fun v =>
        if v ∈ boundNames then none else ThetaM_alt v
      have St6_mem_classify : ∀ v, v ∈ St6.types →
          v ∈ St3.types ∨ v ∈ zs ∨ v ∈ declVars (DltP ++ DltM) := by
        intro v hv
        rcases mem_ctx.mem_classify hv with hv5 | hvM
        · rcases St5_mem_classify v hv5 with hv3 | hvz | hvP
          · exact .inl hv3
          · exact .inr (.inl hvz)
          · exact .inr (.inr (by
              simp only [declVars_append, List.mem_append]
              exact .inl hvP))
        · exact .inr (.inr (by
            simp only [declVars_append, List.mem_append]
            exact .inr hvM))
      have ThetaM_alt_ext_0 : SMT.RenamingContext.Extends
          ThetaM_alt Theta0_alt :=
        SMT.RenamingContext.extends_trans ThetaM_alt_ext_D
          ThetaD_alt_ext
      have ThetaOuter_alt_ext : SMT.RenamingContext.Extends
          ThetaOuter_alt Theta0_alt := by
        intro v d hd
        have hnot_bound : v ∉ boundNames := by
          intro hb
          simp only [boundNames, List.mem_append] at hb
          rcases hb with hz | hdecl
          · have hv0 := Theta0_alt_dom v (by rw [hd]; simp)
            have hv3 : v ∈ St3.types :=
              AList.mem_of_subset St1_sub_St3_types <|
                AList.mem_of_subset types_sub_D hv0
            exact zs_not_St3_types v hz hv3
          · have hv0 := Theta0_alt_dom v (by rw [hd]; simp)
            have hv3 : v ∈ St3.types :=
              AList.mem_of_subset St1_sub_St3_types <|
                AList.mem_of_subset types_sub_D hv0
            have hvbase : v ∈ St3.types.update zs sigmas zs_len :=
              (SMT.TypeContext.mem_update_iff
                St3.types v zs sigmas zs_len).mpr (.inr hv3)
            exact trace_reordered.declVars_fresh_base v hdecl hvbase
        simp only [ThetaOuter_alt, if_neg hnot_bound]
        exact ThetaM_alt_ext_0 hd
      have ThetaOuter_alt_none : ∀ v ∉ St8.env.usedVars,
          ThetaOuter_alt v = none := by
        intro v hv
        simp only [ThetaOuter_alt]
        split_ifs
        · rfl
        · apply ThetaM_alt_none v
          rw [← St8_used]
          exact hv
      have ThetaOuter_alt_dom : ∀ v, ThetaOuter_alt v ≠ none →
          v ∈ St8.types := by
        intro v hv
        have hnot_bound : v ∉ boundNames := by
          intro hb
          simp [ThetaOuter_alt, hb] at hv
        have hvM : ThetaM_alt v ≠ none := by
          simpa [ThetaOuter_alt, hnot_bound] using hv
        rcases St6_mem_classify v (ThetaM_alt_dom v hvM) with
          hv3 | hz | hdecl
        · rwa [St8_types_eq]
        · exact absurd (by
            simp only [boundNames, List.mem_append]
            exact .inl hz) hnot_bound
        · exact absurd (by
            simp only [boundNames, List.mem_append]
            exact .inr hdecl) hnot_bound
      have ThetaOuter_agrees_out : SMT.RenamingContext.AgreesOnFV
          ThetaOuter_alt ThetaM_alt
          (SMT.Term.forall zs sigmas scopedBody) := by
        intro v hv
        have hv' := hv
        simp only [SMT.fv, List.mem_removeAll_iff] at hv'
        have hnot_bound : v ∉ boundNames := by
          intro hb
          simp only [boundNames, List.mem_append] at hb
          rcases hb with hz | hdecl
          · exact hv'.2 hz
          · exact (SMT.ScopedForall.not_mem_fv_foldr_decl_forall
              (DltP ++ DltM) inner v hdecl) hv'.1
        simp [ThetaOuter_alt, hnot_bound]
      have target_respects_out_alt :
          SMT.RenamingContext.RespectsTypeContextOnFV
            ThetaOuter_alt St8.types
            (SMT.Term.forall zs sigmas scopedBody) := by
        rw [St8_types_eq]
        intro v sigma hv hlookup
        obtain ⟨d, hd, hdtype⟩ := target_respects_out_M hv hlookup
        exact ⟨d, (ThetaOuter_agrees_out hv).trans hd, hdtype⟩
      have hcov_out_alt : SMT.RenamingContext.CoversFV ThetaOuter_alt
          (SMT.Term.forall zs sigmas scopedBody) := by
        intro v hv
        obtain ⟨sigma, hlookup⟩ := Option.isSome_iff_exists.mp <|
          AList.lookup_isSome.mpr
            (SMT.Typing.mem_context_of_mem_fv typ_out hv)
        obtain ⟨d, hd, _⟩ := target_respects_out_alt hv hlookup
        rw [hd]
        rfl
      have related_out_alt : RValuationCastSupportedOnFV
          Xi_alt ThetaOuter_alt (B.Term.all vs D P) :=
        related_alt.of_extends ThetaOuter_alt_ext
      have respects_out_alt :
          B.RenamingContext.RespectsTypeContextOnFV
            ThetaOuter_alt St8.types (B.Term.all vs D P) :=
        respects_alt.of_extends ThetaOuter_alt_ext types_sub_final
          (fun _ h => h) fv_in_Lambda
      have helper_disj_zs : ∀ p ∈ declBinders (DltP ++ DltM),
          p.1 ∉ zs := by
        intro p hp hz
        have hpdecl := mem_declVars_of_mem_declBinders hp
        apply trace_reordered.declVars_fresh_base p.1 hpdecl
        exact (SMT.TypeContext.mem_update_iff
          St3.types p.1 zs sigmas zs_len).mpr (.inl hz)
      have hcov_scoped_upd : ∀ w : Fin zs.length → SMT.Dom.{u},
          SMT.RenamingContext.CoversFV
            (Function.updates ThetaOuter_alt zs
              (List.ofFn fun i => some (w i))) scopedBody :=
        hcov_imp_upd_helper zs_nodup hcov_out_alt
      have hresp_scoped_upd : ∀ (w : Fin zs.length → SMT.Dom.{u}),
          (∀ i, (w i).snd.fst = sigmas[i]'(zs_len ▸ i.isLt)) →
          SMT.RenamingContext.RespectsTypeContextOnFV
            (Function.updates ThetaOuter_alt zs
              (List.ofFn fun i => some (w i)))
            (St3.types.update zs sigmas zs_len) scopedBody := by
        intro w hw
        have hresp0 := target_respects_out_alt
        rw [St8_types_eq] at hresp0
        exact SMT.ScopedForall.respects_body_of_forall_assignment
          zs_nodup zs_len hresp0 w hw
      obtain ⟨denOut_alt, hden_out_alt, hdenOut_alt_type⟩ :=
        SMT.RenamingContext.denote_exists_of_typing_fv typ_out
          target_respects_out_alt hcov_out_alt
      have scoped_total : ∀ (w : Fin zs.length → SMT.Dom.{u}),
          (∀ i, (w i).snd.fst = sigmas[i]'(zs_len ▸ i.isLt) ∧
            (w i).fst ∈ ⟦sigmas[i]'(zs_len ▸ i.isLt)⟧ᶻ) →
          ⟦scopedBody.abstract
            (Function.updates ThetaOuter_alt zs
              (List.ofFn fun i => some (w i)))
            (hcov_scoped_upd w)⟧ˢ.isSome = true := by
        intro w hw
        obtain ⟨d, hd, _⟩ :=
          SMT.RenamingContext.denote_exists_of_typing_fv typ_scoped
            (hresp_scoped_upd w (fun i => (hw i).1))
            (hcov_scoped_upd w)
        rw [hd]
        rfl
      have scoped_type : ∀ (w : Fin zs.length → SMT.Dom.{u}),
          (∀ i, (w i).snd.fst = sigmas[i]'(zs_len ▸ i.isLt) ∧
            (w i).fst ∈ ⟦sigmas[i]'(zs_len ▸ i.isLt)⟧ᶻ) →
          ∀ d : SMT.Dom.{u},
            ⟦scopedBody.abstract
              (Function.updates ThetaOuter_alt zs
                (List.ofFn fun i => some (w i)))
              (hcov_scoped_upd w)⟧ˢ = some d →
            d.snd.fst = SMTType.bool := by
        intro w hw d hd
        exact SMT.RenamingContext.denote_type_of_typing_fv typ_scoped
          (hresp_scoped_upd w (fun i => (hw i).1))
          (hcov_scoped_upd w) hd
      have semantic_bridge : ∀ (x : ZFSet.{u})
          (hx_mem : x ∈ ⟦sigmas.toProdl⟧ᶻ),
          let x_B := retract_castZF tau tuple_le x
          let hx_B_mem : x_B ∈ ⟦tau⟧ᶻ :=
            retract_castZF_mem tau tuple_le hx_mem
          let x_fin : Fin vs.length → B.Dom.{u} := fun i =>
            ⟨x_B.get vs.length i, ⟨tau.get vs.length i,
              get_mem_type_of_isTuple
                (hasArity_of_mem_toZFSet tau_hasArity hx_B_mem)
                tau_hasArity hx_B_mem⟩⟩
          ∀ (w : Fin zs.length → SMT.Dom.{u})
            (hw : ∀ i, (w i).snd.fst =
                sigmas[i]'(zs_len ▸ i.isLt) ∧
              (w i).fst ∈ ⟦sigmas[i]'(zs_len ▸ i.isLt)⟧ᶻ)
            (hw_smt : Fin.foldl (zs.length - 1)
              (fun acc i => acc.pair
                (w ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩).fst)
              (w ⟨0, List.length_pos_iff.mpr zs_nemp⟩).fst = x)
            (body_val : SMT.Dom.{u}),
            ⟦scopedBody.abstract
              (Function.updates ThetaOuter_alt zs
                (List.ofFn fun i => some (w i)))
              (hcov_scoped_upd w)⟧ˢ = some body_val →
            (body_val.fst = zftrue ↔
              (x_B ∉ Dval_alt ∨
                ∀ (Px : ZFSet.{u}) (P_ty : BType)
                  (hP_val : Px ∈ ⟦P_ty⟧ᶻ),
                  ⟦(B.Term.abstract.go P vs Xi_alt
                    (fun v hv hvs => Xi_fv_alt v
                      (B.fv.mem_all (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ =
                    some ⟨Px, ⟨P_ty, hP_val⟩⟩ → Px = zftrue)) := by
        intro x hx_mem
        simp only []
        intro w hw hw_smt body_val hbody_val
        let x_B := retract_castZF tau tuple_le x
        have hx_B_mem : x_B ∈ ⟦tau⟧ᶻ :=
          retract_castZF_mem tau tuple_le hx_mem
        let x_fin : Fin vs.length → B.Dom.{u} := fun i =>
          ⟨x_B.get vs.length i, ⟨tau.get vs.length i,
            get_mem_type_of_isTuple
              (hasArity_of_mem_toZFSet tau_hasArity hx_B_mem)
              tau_hasArity hx_B_mem⟩⟩
        let XiW := Function.updates Xi_alt vs
          (List.ofFn fun i => some (x_fin i))
        have XiW_fv : ∀ v ∈ B.fv P, (XiW v).isSome = true := by
          intro v hv
          by_cases hvs : v ∈ vs
          · change (Function.updates Xi_alt vs
              (List.ofFn fun i => some (x_fin i)) v).isSome = true
            rw [Function.updates_eq_if (by simp) vs_nodup, dif_pos hvs]
            simp
          · change (Function.updates Xi_alt vs
              (List.ofFn fun i => some (x_fin i)) v).isSome = true
            rw [Function.updates_of_not_mem Xi_alt vs _ v hvs]
            exact Xi_fv_alt v (B.fv.mem_all (.inr ⟨hv, hvs⟩))
        have wf_P_w : B.RenWF
            (vs.zipToAList alphas ∪ E.context) XiW := by
          apply B.RenWF.updates_ofFn wf_alt vs_nodup vs_context_disj
            vs_alphas_len
          intro i
          dsimp [x_fin]
          dsimp [tau]
          simpa using (_root_.BType.get_reduce alphas_nemp
            vs_alphas_len i)
        obtain ⟨Pval_w, hPval_w, den_P_w⟩ :=
          B.denote_exists_of_typing typ_P XiW XiW_fv
            (@WFTC.wf _ WFTC.of_abstract)
            (wd_P.toPHOAS XiW XiW_fv)
        let wV : Fin vs.length → SMT.Dom.{u} := fun i =>
          w (Fin.cast vs_zs_len i)
        have hwV : ∀ i, (wV i).snd.fst =
              sigmas[Fin.cast (vs_alphas_len.trans alphas_sigmas_len) i] ∧
            (wV i).fst ∈
              ⟦sigmas[Fin.cast (vs_alphas_len.trans alphas_sigmas_len) i]⟧ᶻ := by
          intro i
          have hi := hw (Fin.cast vs_zs_len i)
          simpa [wV] using hi
        have hfoldV : Fin.foldl (vs.length - 1)
            (fun acc i => acc.pair
              (wV ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩).fst)
            (wV ⟨0, List.length_pos_iff.mpr vs_nemp⟩).fst = x := by
          simpa [wV, vs_zs_len] using hw_smt
        have tuple_rdom_w : RDomCast
            (⟨x_B, tau, hx_B_mem⟩ : B.Dom)
            (⟨x, sigmas.toProdl, hx_mem⟩ : SMT.Dom) := by
          exact ⟨tuple_le.toCastPath, rfl⟩
        have tuple_rel_w : RDomCastSupported
            (⟨x_B, tau, hx_B_mem⟩ : B.Dom)
            (⟨x, sigmas.toProdl, hx_mem⟩ : SMT.Dom) :=
          ⟨RDomCast.toRDomCastAdmissible_of_supported tuple_rdom_w
              tuple_supported,
            tuple_supported⟩
        have den_P_go :
            ⟦(B.Term.abstract.go P vs Xi_alt
              (fun v hv hvs => Xi_fv_alt v
                (B.fv.mem_all (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ =
              some ⟨Pval_w, ⟨BType.bool, hPval_w⟩⟩ := by
          rw [denote_term_abstract_go_eq_term_abstract
            vs_nodup vs_nemp x_fin XiW_fv]
          simpa [XiW] using den_P_w
        let ThetaW := Function.updates ThetaOuter_alt zs
          (List.ofFn fun i => some (w i))
        have hresp_scoped_w :
            SMT.RenamingContext.RespectsTypeContextOnFV ThetaW
              (St3.types.update zs sigmas zs_len) scopedBody :=
          hresp_scoped_upd w (fun i => (hw i).1)
        have all_helper_resp :=
          SMT.ScopedForall.allAssignments_respects_foldr_decl
            (DltP ++ DltM) inner trace_reordered hresp_scoped_w
        have all_helper_zs : SMT.ScopedForall.AllAssignments
            (declBinders (DltP ++ DltM)) ThetaW (fun ThetaH =>
              ∀ z ∈ zs, ThetaH z = ThetaW z) :=
          SMT.ScopedForall.AllAssignments.preserves
            (declBinders (DltP ++ DltM)) zs helper_disj_zs
        have helper_disj_base : ∀ p ∈ declBinders (DltP ++ DltM),
            p.1 ∉ St3.types.keys := by
          intro p hp hbase
          have hpdecl := mem_declVars_of_mem_declBinders hp
          apply trace_reordered.declVars_fresh_base p.1 hpdecl
          exact (SMT.TypeContext.mem_update_iff
            St3.types p.1 zs sigmas zs_len).mpr (.inr hbase)
        have all_helper_base : SMT.ScopedForall.AllAssignments
            (declBinders (DltP ++ DltM)) ThetaW (fun ThetaH =>
              ∀ v ∈ St3.types, ThetaH v = ThetaW v) := by
          simpa only [AList.mem_keys] using
            (SMT.ScopedForall.AllAssignments.preserves
              (declBinders (DltP ++ DltM)) St3.types.keys
              helper_disj_base)
        have all_specs_GammaM : ∀ b ∈ specBodies (DltP ++ DltM),
            GammaM ⊢ˢ b : SMTType.bool := by
          intro b hb
          exact SMT.Typing.permute_context permM (all_specs_St6 b hb)
        have vs_mem_GammaM : ∀ v ∈ vs, v ∈ GammaM := by
          intro v hv
          have hv3 : v ∈ St3.types := by
            rw [St3_update]
            exact (SMT.TypeContext.mem_update_iff
              St1.types v vs sigmas vs_sigmas_len).mpr (.inl hv)
          have hvbase : v ∈ St3.types.update zs sigmas zs_len :=
            (SMT.TypeContext.mem_update_iff
              St3.types v zs sigmas zs_len).mpr (.inr hv3)
          exact AList.mem_of_subset trace_reordered.entries_subset hvbase
        have zs_mem_GammaM : ∀ z ∈ zs, z ∈ GammaM := by
          intro z hz
          have hzbase : z ∈ St3.types.update zs sigmas zs_len :=
            (SMT.TypeContext.mem_update_iff
              St3.types z zs sigmas zs_len).mpr (.inl hz)
          exact AList.mem_of_subset trace_reordered.entries_subset hzbase
        have specs_bv_fresh : ∀ b ∈ specBodies (DltP ++ DltM),
            (∀ v ∈ vs, v ∉ SMT.bv b) ∧
            (∀ z ∈ zs, z ∉ SMT.bv b) := by
          intro b hb
          have htyp := all_specs_GammaM b hb
          constructor
          · intro v hv hbv
            exact SMT.Typing.bv_notMem_context htyp v hbv
              (vs_mem_GammaM v hv)
          · intro z hz hbv
            exact SMT.Typing.bv_notMem_context htyp z hbv
              (zs_mem_GammaM z hz)
        let wsV : List SMT.Dom.{u} := List.ofFn wV
        have wsV_len : vs.length = wsV.length := by simp [wsV]
        have hws_type_GammaM : ∀ (i : ℕ) (hi_v : i < vs.length)
            (hi_w : i < wsV.length) (sigma : SMTType),
            GammaM.lookup vs[i] = some sigma →
              wsV[i].snd.fst = sigma := by
          intro i hi_v hi_w sigma hlookup
          have hlookup3 : St3.types.lookup vs[i] = some sigmas[i] := by
            rw [St3_update]
            exact SMT.TypeContext.lookup_update_of_mem_nodup
              St1.types vs_nodup vs_sigmas_len hi_v
          have hv_not_zs : vs[i] ∉ zs := by
            intro hz
            exact zs_disj_vs vs[i] hz (List.getElem_mem hi_v)
          have hlookup_base :
              (St3.types.update zs sigmas zs_len).lookup vs[i] =
                some sigmas[i] := by
            rw [SMT.TypeContext.lookup_update
              St3.types vs[i] zs sigmas zs_len hv_not_zs]
            exact hlookup3
          have hlookup_final : GammaM.lookup vs[i] = some sigmas[i] :=
            AList.lookup_of_subset trace_reordered.entries_subset hlookup_base
          rw [hlookup_final] at hlookup
          cases hlookup
          have hget : wsV[i] = wV ⟨i, hi_v⟩ := by
            exact List.getElem_ofFn (f := wV) (h := hi_w)
          rw [hget]
          exact (hwV ⟨i, hi_v⟩).1
        have specs_true_of_guards : ∀
            (ThetaH : SMT.RenamingContext.Context.{u}),
            SMT.RenamingContext.RespectsTypeContextOnFV
              ThetaH GammaM inner →
            (∀ z ∈ zs, ThetaH z = ThetaW z) →
            SMT.ScopedForall.TermsTrue ThetaH guards →
            SpecBodiesTrue
              (Function.updates ThetaH vs (wsV.map Option.some))
              GammaM (DltP ++ DltM) := by
          intro ThetaH hresp_inner hpres_zs hterms
          have hzs_vals : ∀ (i : ℕ) (hi_z : i < zs.length)
              (hi_w : i < wsV.length),
              ThetaH zs[i] = some wsV[i] := by
            intro i hi_z hi_w
            rw [hpres_zs zs[i] (List.getElem_mem hi_z)]
            change Function.updates ThetaOuter_alt zs
              (List.ofFn fun i => some (w i)) zs[i] = some wsV[i]
            rw [Function.updates_eq_if (by simp) zs_nodup,
              dif_pos (List.getElem_mem hi_z)]
            have hidx := List.Nodup.idxOf_getElem zs_nodup i hi_z
            simp only [List.getElem_ofFn]
            have hget : wsV[i] = wV ⟨i, by simpa [wsV] using hi_w⟩ :=
              List.getElem_ofFn (f := wV) (h := hi_w)
            apply congrArg some
            rw [hget]
            dsimp [wV]
            apply congrArg w
            apply Fin.ext
            exact hidx
          have hresp_orig : ∀ b ∈ specBodies (DltP ++ DltM),
              SMT.RenamingContext.RespectsTypeContextOnFV
                (Function.updates ThetaH vs (wsV.map Option.some))
                GammaM b := by
            intro b hb
            apply SMT.ScopedForall.respects_of_substList_vars b vs zs wsV
              wsV_len vs_nodup zs_disj_vs hws_type_GammaM
            apply hresp_inner.mono_fv
            exact SMT.ScopedForall.fv_subset_foldr_imp_guard guards raw
              (List.mem_map.mpr ⟨b, hb, rfl⟩)
          have hcov_sub : ∀ b ∈ specBodies (DltP ++ DltM),
              SMT.RenamingContext.CoversFV ThetaH
                (SMT.substList vs (zs.map SMT.Term.var) b) := by
            intro b hb v hv
            have hv_inner := SMT.ScopedForall.fv_subset_foldr_imp_guard
              guards raw (List.mem_map.mpr ⟨b, hb, rfl⟩) hv
            obtain ⟨sigma, hlookup⟩ := Option.isSome_iff_exists.mp <|
              AList.lookup_isSome.mpr <|
                SMT.Typing.mem_context_of_mem_fv typ_inner_reordered hv_inner
            obtain ⟨d, hd, _⟩ := hresp_inner hv_inner hlookup
            rw [hd]
            rfl
          exact SMT.ScopedForall.SpecBodiesTrue.of_subst_termsTrue
            vs zs wsV vs_zs_len wsV_len vs_nodup zs_disj_vs
            specs_bv_fresh hzs_vals all_specs_GammaM hresp_orig
            hcov_sub hterms
        have P_scope : ScopedContextExtends St3.types DltP GammaM := by
          intro e he
          apply St4_sub_GammaM
          exact P_envelope.scoped_extends (by simpa using he)
        have M_scope : ScopedContextExtends St5.types DltM GammaM :=
          fun e he => St6_sub_GammaM (mem_trace.scoped_extends he)
        have typ_P_GammaM : GammaM ⊢ˢ Penc : SMTType.bool :=
          SMT.Typing.permute_context permM typ_Penc_St6
        have typ_mem_GammaM : GammaM ⊢ˢ mem_enc : SMTType.bool :=
          SMT.Typing.permute_context permM typ_mem
        have typ_raw_GammaM : GammaM ⊢ˢ raw : SMTType.bool :=
          SMT.Typing.permute_context permM typ_raw
        have guarded_raw : ∀
            (ThetaH : SMT.RenamingContext.Context.{u}),
            SMT.RenamingContext.RespectsTypeContextOnFV
              ThetaH GammaM inner →
            (∀ z ∈ zs, ThetaH z = ThetaW z) →
            (∀ v ∈ St3.types, ThetaH v = ThetaW v) →
            SMT.ScopedForall.TermsTrue ThetaH guards →
            ∃ d : SMT.Dom.{u},
              ∃ hcov_raw : SMT.RenamingContext.CoversFV ThetaH raw,
                ⟦raw.abstract ThetaH hcov_raw⟧ˢ = some d ∧
                d.snd.fst = SMTType.bool ∧
                (d.fst = zftrue ↔
                  (x_B ∉ Dval_alt ∨
                    ∀ (Px : ZFSet.{u}) (P_ty : BType)
                      (hP_val : Px ∈ ⟦P_ty⟧ᶻ),
                      ⟦(B.Term.abstract.go P vs Xi_alt
                        (fun v hv hvs => Xi_fv_alt v
                          (B.fv.mem_all (.inr ⟨hv, hvs⟩)))).uncurry
                          x_fin⟧ᴮ =
                        some ⟨Px, ⟨P_ty, hP_val⟩⟩ → Px = zftrue)) := by
          intro ThetaH hresp_inner hpres_zs hpres_base hterms
          let ThetaOrig := Function.updates ThetaH vs
            (wsV.map Option.some)
          have specs_orig : SpecBodiesTrue ThetaOrig GammaM
              (DltP ++ DltM) :=
            specs_true_of_guards ThetaH hresp_inner hpres_zs hterms
          have specs_M_H : SpecBodiesTrue ThetaH GammaM DltM := by
            apply SpecBodiesTrue.of_agreesOnFV
              (SpecBodiesTrue.right_of_append specs_orig)
            intro b hb v hv
            have hv_not_vs : v ∉ vs := by
              intro hvs
              exact vs_not_fv_M_specs b hb v hvs hv
            dsimp only [ThetaOrig]
            exact (Function.updates_of_not_mem ThetaH vs _ v
              hv_not_vs).symm
          have hresp_sub_P :
              SMT.RenamingContext.RespectsTypeContextOnFV ThetaH GammaM
                (SMT.substList vs (zs.map SMT.Term.var) Penc) := by
            apply hresp_inner.mono_fv
            exact fun v hv =>
              SMT.ScopedForall.fv_subset_foldr_imp_base guards raw
                (by simp only [raw, SMT.fv, List.mem_append]; exact .inr hv)
          have hresp_P_orig :
              SMT.RenamingContext.RespectsTypeContextOnFV
                ThetaOrig GammaM Penc := by
            exact SMT.ScopedForall.respects_of_substList_vars
              Penc vs zs wsV wsV_len vs_nodup zs_disj_vs
              hws_type_GammaM hresp_sub_P
          have ambient_H : ∀ v ∈ B.fv P, v ∉ vs →
              match Xi_alt v, ThetaH v with
              | some d, some d' => RDomCastSupported d d'
              | _, _ => False := by
            intro v hv hvs
            have hv_all : v ∈ B.fv (B.Term.all vs D P) :=
              B.fv.mem_all (.inr ⟨hv, hvs⟩)
            have hv0 := fv_in_Lambda v hv_all
            have hv3 : v ∈ St3.types :=
              AList.mem_of_subset St1_sub_St3_types <|
                AList.mem_of_subset types_sub_D hv0
            have hv_not_zs : v ∉ zs := by
              intro hz
              exact zs_not_St3_used v hz <|
                St1_sub_St3_used <| used_sub_D <|
                  vars_used_P v (B.Term.mem_vars_iff.mpr (Or.inl hv))
            rw [hpres_base v hv3]
            change (match Xi_alt v,
              Function.updates ThetaOuter_alt zs
                (List.ofFn fun i => some (w i)) v with
              | some d, some d' => RDomCastSupported d d'
              | _, _ => False)
            rw [Function.updates_of_not_mem ThetaOuter_alt zs _ v hv_not_zs]
            exact related_out_alt v hv_all
          have related_P_H : RValuationCastSupportedOnFV
              XiW ThetaOrig P := by
            have hwsV_some : wsV.map Option.some =
                List.ofFn (fun i => some (wV i)) := by
              apply List.ext_getElem
              · simp [wsV]
              · intro i hi_left hi_right
                simp [wsV]
            change RValuationCastSupportedOnFV XiW
              (Function.updates ThetaH vs (wsV.map Option.some)) P
            rw [hwsV_some]
            simpa [XiW, x_fin, tau,
              BType.get_reduce, ZFSet.get_cast] using
              (RValuationCastSupportedOnFV.updates_of_fold_reduce_toProdl
                vs_nemp vs_nodup alphas_nemp vs_alphas_len
                alphas_sigmas_len tau_hasArity hx_B_mem hx_mem tuple_rel_w
                wV hwV hfoldV ambient_H (t := P))
          have respects_P_H_St3 :
              B.RenamingContext.RespectsTypeContextOnFV
                ThetaOrig St3.types P := by
            intro v sigma hv hlookup
            by_cases hvs : v ∈ vs
            · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hvs
              have hlookup_i : St3.types.lookup vs[i] = some sigmas[i] := by
                rw [St3_update]
                exact SMT.TypeContext.lookup_update_of_mem_nodup
                  St1.types vs_nodup vs_sigmas_len hi
              rw [hlookup_i] at hlookup
              cases hlookup
              have hi_w : i < wsV.length := wsV_len ▸ hi
              refine ⟨wsV[i], ?_, hws_type_GammaM i hi hi_w
                sigmas[i] (AList.lookup_of_subset
                  (fun e he => St4_sub_GammaM (St3_sub_St4_types he))
                  hlookup_i)⟩
              change Function.updates ThetaH vs
                (wsV.map Option.some) vs[i] = some wsV[i]
              rw [Function.updates_eq_if (by simpa [wsV]) vs_nodup,
                dif_pos (List.getElem_mem hi)]
              simp [List.Nodup.idxOf_getElem vs_nodup]
            · have hv_all : v ∈ B.fv (B.Term.all vs D P) :=
                B.fv.mem_all (.inr ⟨hv, hvs⟩)
              have hresp0 := respects_out_alt
              rw [St8_types_eq] at hresp0
              obtain ⟨d, hd, hdtype⟩ := hresp0 hv_all hlookup
              refine ⟨d, ?_, hdtype⟩
              change Function.updates ThetaH vs
                (wsV.map Option.some) v = some d
              rw [Function.updates_of_not_mem ThetaH vs _ v hvs]
              have hv3 : v ∈ St3.types := fv_P_in_St3 v hv
              rw [hpres_base v hv3]
              have hv_not_zs : v ∉ zs := by
                intro hz
                exact zs_not_St3_types v hz hv3
              change Function.updates ThetaOuter_alt zs
                (List.ofFn fun i => some (w i)) v = some d
              rw [Function.updates_of_not_mem ThetaOuter_alt zs _ v hv_not_zs]
              exact hd
          have respects_P_H :
              B.RenamingContext.RespectsTypeContextOnFV
                ThetaOrig GammaM P :=
            respects_P_H_St3.of_extends
              (SMT.RenamingContext.extends_refl ThetaOrig)
              (fun e he => St4_sub_GammaM (St3_sub_St4_types he))
              (fun _ h => h) fv_P_in_St3
          have hcov_P_H : SMT.RenamingContext.CoversFV ThetaOrig Penc := by
            intro v hv
            obtain ⟨sigma, hlookup⟩ := Option.isSome_iff_exists.mp <|
              AList.lookup_isSome.mpr <|
                SMT.Typing.mem_context_of_mem_fv typ_P_GammaM hv
            obtain ⟨d, hd, _⟩ := hresp_P_orig hv hlookup
            rw [hd]
            rfl
          obtain ⟨denP_H, hden_P_H, hdenP_H_type⟩ :=
            SMT.RenamingContext.denote_exists_of_typing_fv typ_P_GammaM
              hresp_P_orig hcov_P_H
          have P_rel_H := P_guard GammaM P_scope XiW XiW_fv ThetaOrig
            related_P_H wf_P_w respects_P_H hresp_P_orig
            (SpecBodiesTrue.left_of_append specs_orig)
            Pval_w hPval_w den_P_w hcov_P_H denP_H
            hden_P_H hdenP_H_type
          have hresp_mem_H :
              SMT.RenamingContext.RespectsTypeContextOnFV
                ThetaH GammaM mem_enc := by
            apply hresp_inner.mono_fv
            intro v hv
            apply SMT.ScopedForall.fv_subset_foldr_imp_base guards raw
            simp only [raw, SMT.fv, List.mem_append]
            exact Or.inl hv
          have hresp_tuple_H :
              SMT.RenamingContext.RespectsTypeContextOnFV ThetaH GammaM
                (zs.map SMT.Term.var).toPairl :=
            hresp_mem_H.mono_fv fv_tuple_mem
          have hresp_D_H :
              SMT.RenamingContext.RespectsTypeContextOnFV
                ThetaH GammaM Denc :=
            hresp_mem_H.mono_fv fv_Denc_mem
          have hcov_mem_H : SMT.RenamingContext.CoversFV
              ThetaH mem_enc := by
            intro v hv
            obtain ⟨sigma, hlookup⟩ := Option.isSome_iff_exists.mp <|
              AList.lookup_isSome.mpr <|
                SMT.Typing.mem_context_of_mem_fv typ_mem_GammaM hv
            obtain ⟨d, hd, _⟩ := hresp_mem_H hv hlookup
            rw [hd]
            rfl
          have hcov_tuple_H : SMT.RenamingContext.CoversFV
              ThetaH (zs.map SMT.Term.var).toPairl := by
            intro v hv
            have hvmem := fv_tuple_mem hv
            obtain ⟨sigma, hlookup⟩ := Option.isSome_iff_exists.mp <|
              AList.lookup_isSome.mpr <|
                SMT.Typing.mem_context_of_mem_fv typ_mem_GammaM hvmem
            obtain ⟨d, hd, _⟩ := hresp_tuple_H hv hlookup
            rw [hd]
            rfl
          have ThetaH_at_zs : ∀ (i : ℕ) (hi : i < zs.length),
              ThetaH zs[i] = some (w ⟨i, hi⟩) := by
            intro i hi
            rw [hpres_zs zs[i] (List.getElem_mem hi)]
            change Function.updates ThetaOuter_alt zs
              (List.ofFn fun i => some (w i)) zs[i] =
                some (w ⟨i, hi⟩)
            rw [Function.updates_eq_if (by simp) zs_nodup,
              dif_pos (List.getElem_mem hi)]
            simp [List.Nodup.idxOf_getElem zs_nodup]
          have updates_zs_ThetaH : Function.updates ThetaH zs
              (List.ofFn fun i => some (w i)) = ThetaH := by
            funext v
            by_cases hv : v ∈ zs
            · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hv
              rw [Function.updates_eq_if (by simp) zs_nodup,
                dif_pos (List.getElem_mem hi)]
              simp [List.Nodup.idxOf_getElem zs_nodup,
                ThetaH_at_zs i hi]
            · exact Function.updates_of_not_mem ThetaH zs _ v hv
          have hcov_tuple_upd : SMT.RenamingContext.CoversFV
              (Function.updates ThetaH zs
                (List.ofFn fun i => some (w i)))
              (zs.map SMT.Term.var).toPairl := by
            rw [updates_zs_ThetaH]
            exact hcov_tuple_H
          obtain ⟨_hfold_mem, hden_tuple_upd⟩ :=
            toPairl_vars_denote_updates zs sigmas zs_len zs_nodup
              (List.length_pos_iff.mpr zs_nemp) ThetaH w hw
              hcov_tuple_upd
          have hden_tuple_H :
              ⟦(zs.map SMT.Term.var).toPairl.abstract
                ThetaH hcov_tuple_H⟧ˢ =
                some (⟨x, sigmas.toProdl, hx_mem⟩ : SMT.Dom) := by
            have hagree : SMT.RenamingContext.AgreesOnFV ThetaH
                (Function.updates ThetaH zs
                  (List.ofFn fun i => some (w i)))
                (zs.map SMT.Term.var).toPairl := by
              intro v hv
              rw [updates_zs_ThetaH]
            have hden_eq := SMT.RenamingContext.denote_congr_of_agreesOnFV
              (t := (zs.map SMT.Term.var).toPairl)
              (h1 := hcov_tuple_H) (h2 := hcov_tuple_upd) hagree
            have hdom_eq :
                (⟨Fin.foldl (zs.length - 1)
                    (fun acc i => acc.pair
                      (w ⟨i.val + 1,
                        Nat.add_lt_of_lt_sub i.isLt⟩).fst)
                    (w ⟨0, List.length_pos_iff.mpr zs_nemp⟩).fst,
                  sigmas.toProdl, _hfold_mem⟩ : SMT.Dom) =
                  ⟨x, sigmas.toProdl, hx_mem⟩ :=
              SMT.RenamingContext.Dom_ext' hw_smt rfl
            exact hden_eq.trans <| hden_tuple_upd.trans <|
              congrArg some hdom_eq
          have agrees_D_H : SMT.RenamingContext.AgreesOnFV
              ThetaH ThetaD_alt Denc := by
            intro v hv
            have hv1 : v ∈ St1.types :=
              SMT.Typing.mem_context_of_mem_fv typ_Denc hv
            have hv3 : v ∈ St3.types :=
              AList.mem_of_subset St1_sub_St3_types hv1
            have hv_not_zs : v ∉ zs := by
              intro hz
              exact zs_not_St3_types v hz hv3
            have hv_not_decl : v ∉ declVars (DltP ++ DltM) := by
              intro hdecl
              apply trace_reordered.declVars_fresh_base v hdecl
              exact (SMT.TypeContext.mem_update_iff
                St3.types v zs sigmas zs_len).mpr (.inr hv3)
            obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp
              (hcov_D_alt v hv)
            rw [hpres_base v hv3]
            rw [hd]
            dsimp only [ThetaW]
            change Function.updates ThetaOuter_alt zs
              (List.ofFn fun i => some (w i)) v = some d
            rw [Function.updates_of_not_mem ThetaOuter_alt zs _ v
              hv_not_zs]
            simp only [ThetaOuter_alt, boundNames,
              List.mem_append, hv_not_zs, hv_not_decl, or_false,
              ↓reduceIte]
            exact ThetaM_alt_ext_D hd
          have hcov_D_H : SMT.RenamingContext.CoversFV
              ThetaH Denc :=
            SMT.RenamingContext.coversFV_of_agreesOnFV_symm
              agrees_D_H hcov_D_alt
          have hden_D_H : ⟦Denc.abstract ThetaH hcov_D_H⟧ˢ =
              some denDenc_alt := by
            exact (SMT.RenamingContext.denote_congr_of_agreesOnFV
              (t := Denc) (h1 := hcov_D_H) (h2 := hcov_D_alt)
              agrees_D_H).trans hden_Denc_alt
          obtain ⟨denMem_H, hden_mem_H, hdenMem_H_type⟩ :=
            SMT.RenamingContext.denote_exists_of_typing_fv
              typ_mem_GammaM hresp_mem_H hcov_mem_H
          have mem_iff_H := mem_guard_alt GammaM M_scope ThetaH
            hcov_tuple_H hcov_D_H hresp_tuple_H hresp_D_H
            x_B Dval_alt hx_B_mem hDval_alt
            (⟨x, sigmas.toProdl, hx_mem⟩ : SMT.Dom) denDenc_alt
            hden_tuple_H hden_D_H rfl hdenDenc_alt_type
            tuple_rel_w D_alt_rel
            hcov_mem_H denMem_H hresp_mem_H specs_M_H
            hden_mem_H hdenMem_H_type
          have typ_sub_P_GammaM : GammaM ⊢ˢ
              SMT.substList vs (zs.map SMT.Term.var) Penc :
                SMTType.bool :=
            (SMT.Typing.impE typ_raw_GammaM).2.2
          have hcov_sub_P : SMT.RenamingContext.CoversFV ThetaH
              (SMT.substList vs (zs.map SMT.Term.var) Penc) := by
            intro v hv
            obtain ⟨sigma, hlookup⟩ := Option.isSome_iff_exists.mp <|
              AList.lookup_isSome.mpr <|
                SMT.Typing.mem_context_of_mem_fv typ_sub_P_GammaM hv
            obtain ⟨d, hd, _⟩ := hresp_sub_P hv hlookup
            rw [hd]
            rfl
          have Penc_vs_bv_fresh : ∀ v ∈ vs, v ∉ SMT.bv Penc := by
            intro v hv hbv
            exact SMT.Typing.bv_notMem_context typ_P_GammaM v hbv
              (vs_mem_GammaM v hv)
          have Penc_zs_bv_fresh : ∀ z ∈ zs, z ∉ SMT.bv Penc := by
            intro z hz hbv
            exact SMT.Typing.bv_notMem_context typ_P_GammaM z hbv
              (zs_mem_GammaM z hz)
          have hzs_for_P : ∀ (i : ℕ) (hi_z : i < zs.length)
              (hi_w : i < wsV.length), ThetaH zs[i] = some wsV[i] := by
            intro i hi_z hi_w
            have hvi : i < vs.length := by simpa [wsV] using hi_w
            have hfin : Fin.cast vs_zs_len ⟨i, hvi⟩ = ⟨i, hi_z⟩ := by
              apply Fin.ext
              rfl
            rw [ThetaH_at_zs i hi_z]
            have hget : wsV[i] = wV ⟨i, hvi⟩ :=
              List.getElem_ofFn (f := wV) (h := hi_w)
            rw [hget]
            simp only [wV, hfin]
          have hden_sub_eq := SMT.ScopedForall.substList_vars_denote_eq
            Penc vs zs wsV vs_zs_len wsV_len vs_nodup
            Penc_vs_bv_fresh Penc_zs_bv_fresh zs_disj_vs hzs_for_P
            hcov_sub_P hcov_P_H
          have hden_sub_P :
              ⟦(SMT.substList vs (zs.map SMT.Term.var) Penc).abstract
                ThetaH hcov_sub_P⟧ˢ = some denP_H :=
            hden_sub_eq.trans hden_P_H
          have hcov_raw_H : SMT.RenamingContext.CoversFV ThetaH raw := by
            intro v hv
            simp only [raw, SMT.fv, List.mem_append] at hv
            exact hv.elim (hcov_mem_H v) (hcov_sub_P v)
          obtain ⟨denRaw_H, hden_raw_core, hdenRaw_H_type⟩ :=
            denote_imp_some_bool hden_mem_H hdenMem_H_type
              hden_sub_P hdenP_H_type
          have hden_raw_H : ⟦raw.abstract ThetaH hcov_raw_H⟧ˢ =
              some denRaw_H := by
            simpa [raw, SMT.Term.abstract, proof_irrel_heq] using
              hden_raw_core
          have hraw_iff := SMT.ScopedForall.denote_imp_true_iff
            hden_mem_H hdenMem_H_type hden_sub_P hdenP_H_type
            hden_raw_core
          have P_rdom := (RDomCast.iff_RDom_of_type_eq
            (α := BType.bool) hdenP_H_type).mp P_rel_H.toRDomCast
          rw [RDom] at P_rdom
          have hP_eq : denP_H.fst = Pval_w := by
            dsimp [retract] at P_rdom
            exact P_rdom.2
          have hmem_bool : denMem_H.fst ∈ ZFSet.𝔹 := by
            simpa [hdenMem_H_type] using denMem_H.snd.snd
          have hmem_false_iff : denMem_H.fst = ZFSet.zffalse ↔
              x_B ∉ Dval_alt := by
            constructor
            · intro hfalse hxD
              have htrue := mem_iff_H.mpr hxD
              exact ZFSet.zftrue_ne_zffalse
                (htrue.symm.trans hfalse)
            · intro hnot
              rw [ZFSet.ZFBool.mem_𝔹_iff] at hmem_bool
              exact hmem_bool.resolve_right (fun htrue =>
                hnot (mem_iff_H.mp htrue))
          have hP_true_iff : denP_H.fst = ZFSet.zftrue ↔
              ∀ (Px : ZFSet.{u}) (P_ty : BType)
                (hP_val : Px ∈ ⟦P_ty⟧ᶻ),
                ⟦(B.Term.abstract.go P vs Xi_alt
                  (fun v hv hvs => Xi_fv_alt v
                    (B.fv.mem_all (.inr ⟨hv, hvs⟩)))).uncurry
                    x_fin⟧ᴮ = some ⟨Px, ⟨P_ty, hP_val⟩⟩ →
                  Px = ZFSet.zftrue := by
            constructor
            · intro htrue Px P_ty hP_val hPx
              have hdom :
                  (⟨Pval_w, BType.bool, hPval_w⟩ : B.Dom) =
                    ⟨Px, P_ty, hP_val⟩ :=
                Option.some.inj (den_P_go.symm.trans hPx)
              have hvalue := congrArg (fun d : B.Dom => d.fst) hdom
              exact hvalue.symm.trans (hP_eq.symm.trans htrue)
            · intro hall
              exact hP_eq.trans <| hall Pval_w BType.bool hPval_w den_P_go
          refine ⟨denRaw_H, hcov_raw_H, hden_raw_H,
            hdenRaw_H_type, ?_⟩
          exact hraw_iff.trans (or_congr hmem_false_iff hP_true_iff)
        let Q : Prop := x_B ∉ Dval_alt ∨
          ∀ (Px : ZFSet.{u}) (P_ty : BType)
            (hP_val : Px ∈ ⟦P_ty⟧ᶻ),
            ⟦(B.Term.abstract.go P vs Xi_alt
              (fun v hv hvs => Xi_fv_alt v
                (B.fv.mem_all (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ =
                some ⟨Px, ⟨P_ty, hP_val⟩⟩ → Px = ZFSet.zftrue
        have all_helper_data := all_helper_resp.and <|
          all_helper_zs.and all_helper_base
        have helper_true : Q → SMT.ScopedForall.AllAssignments
            (declBinders (DltP ++ DltM)) ThetaW (fun ThetaH =>
              ∀ hcov_inner : SMT.RenamingContext.CoversFV ThetaH inner,
                ⟦inner.abstract ThetaH hcov_inner⟧ˢ =
                  some ⟨ZFSet.zftrue, SMTType.bool,
                    ZFSet.ZFBool.zftrue_mem_𝔹⟩) := by
          intro hQ
          apply all_helper_data.mono
          intro ThetaH hdata hcov_inner
          apply SMT.ScopedForall.foldr_imp_eq_zftrue guards raw
            typ_inner_reordered hcov_inner hdata.1
          intro hguards hcov_raw d hden_raw
          obtain ⟨d0, hcov0, hden0, _htype0, hiff0⟩ :=
            guarded_raw ThetaH hdata.1 hdata.2.1 hdata.2.2 hguards
          have hproof := SMT.RenamingContext.denote_abstract_proof_irrel
            raw ThetaH hcov0 hcov_raw
          have hden0' : ⟦raw.abstract ThetaH hcov_raw⟧ˢ = some d0 :=
            hproof.symm.trans hden0
          have heq : d0 = d := Option.some.inj
            (hden0'.symm.trans hden_raw)
          rw [← heq]
          exact hiff0.mpr hQ
        have helper_false : ¬ Q → SMT.ScopedForall.SomeAssignment
            (declBinders (DltP ++ DltM)) ThetaW (fun ThetaH =>
              ∀ hcov_inner : SMT.RenamingContext.CoversFV ThetaH inner,
                ⟦inner.abstract ThetaH hcov_inner⟧ˢ =
                  some ⟨ZFSet.zffalse, SMTType.bool,
                    ZFSet.ZFBool.zffalse_mem_𝔹⟩) := by
          intro hnotQ
          let ThetaBaseW := Function.updates ThetaOuter_alt vs
            (wsV.map Option.some)
          have ambient_base : ∀ v ∈ B.fv P, v ∉ vs →
              match Xi_alt v, ThetaOuter_alt v with
              | some d, some d' => RDomCastSupported d d'
              | _, _ => False := by
            intro v hv hvs
            exact related_out_alt v <|
              B.fv.mem_all (.inr ⟨hv, hvs⟩)
          have related_P_base : RValuationCastSupportedOnFV
              XiW ThetaBaseW P := by
            have hwsV_some : wsV.map Option.some =
                List.ofFn (fun i => some (wV i)) := by
              apply List.ext_getElem
              · simp [wsV]
              · intro i hi_left hi_right
                simp [wsV]
            change RValuationCastSupportedOnFV XiW
              (Function.updates ThetaOuter_alt vs
                (wsV.map Option.some)) P
            rw [hwsV_some]
            simpa [XiW, x_fin, tau, BType.get_reduce,
              ZFSet.get_cast] using
              (RValuationCastSupportedOnFV.updates_of_fold_reduce_toProdl
                vs_nemp vs_nodup alphas_nemp vs_alphas_len
                alphas_sigmas_len tau_hasArity hx_B_mem hx_mem
                tuple_rel_w wV hwV hfoldV ambient_base (t := P))
          have vs_mem_St4_used : ∀ v ∈ vs,
              v ∈ St4.env.usedVars := by
            intro v hv
            exact St3_sub_St4_used <| St1_sub_St3_used <| used_sub_D <|
              vars_used_vs v hv
          have ThetaBaseW_none : ∀ v ∉ St4.env.usedVars,
              ThetaBaseW v = none := by
            intro v hv
            have hv_not_vs : v ∉ vs := by
              intro hvs
              exact hv (vs_mem_St4_used v hvs)
            dsimp only [ThetaBaseW]
            rw [Function.updates_of_not_mem ThetaOuter_alt vs _ v
              hv_not_vs]
            by_contra hne
            have hv8 := ThetaOuter_alt_dom v hne
            rw [St8_types_eq] at hv8
            exact hv (St3_sub_St4_used (St3_keys_sub hv8))
          have ThetaBaseW_dom : ∀ v, ThetaBaseW v ≠ none →
              v ∈ St3.types := by
            intro v hv
            by_cases hvs : v ∈ vs
            · rw [St3_update]
              exact (SMT.TypeContext.mem_update_iff
                St1.types v vs sigmas vs_sigmas_len).mpr (.inl hvs)
            · dsimp only [ThetaBaseW] at hv
              rw [Function.updates_of_not_mem ThetaOuter_alt vs _ v
                hvs] at hv
              have hv8 := ThetaOuter_alt_dom v hv
              rwa [St8_types_eq] at hv8
          have respects_P_base :
              B.RenamingContext.RespectsTypeContextOnFV
                ThetaBaseW St3.types P := by
            intro v sigma hv hlookup
            by_cases hvs : v ∈ vs
            · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hvs
              have hlookup_i : St3.types.lookup vs[i] =
                  some sigmas[i] := by
                rw [St3_update]
                exact SMT.TypeContext.lookup_update_of_mem_nodup
                  St1.types vs_nodup vs_sigmas_len hi
              rw [hlookup_i] at hlookup
              cases hlookup
              have hi_w : i < wsV.length := wsV_len ▸ hi
              refine ⟨wsV[i], ?_, ?_⟩
              · dsimp only [ThetaBaseW]
                rw [Function.updates_eq_if (by simpa using wsV_len)
                  vs_nodup, dif_pos (List.getElem_mem hi)]
                simp [List.Nodup.idxOf_getElem vs_nodup]
              · have hget : wsV[i] = wV ⟨i, hi⟩ :=
                  List.getElem_ofFn (f := wV) (h := hi_w)
                rw [hget]
                exact (hwV ⟨i, hi⟩).1
            · have hv_all : v ∈ B.fv (B.Term.all vs D P) :=
                B.fv.mem_all (.inr ⟨hv, hvs⟩)
              have hresp0 := respects_out_alt
              rw [St8_types_eq] at hresp0
              obtain ⟨d, hd, hdtype⟩ := hresp0 hv_all hlookup
              refine ⟨d, ?_, hdtype⟩
              dsimp only [ThetaBaseW]
              rw [Function.updates_of_not_mem ThetaOuter_alt vs _ v hvs]
              exact hd
          have respects_P_base_PBase :
              B.RenamingContext.RespectsTypeContextOnFV
                ThetaBaseW PBase.types P :=
            respects_P_base.transport_fv (fun _ h => h)
              St3_sub_PBase_types fv_P_in_St3
          have ThetaBaseW_dom_PBase : ∀ v, ThetaBaseW v ≠ none →
              v ∈ PBase.types := by
            intro v hv
            exact AList.mem_of_subset St3_sub_PBase_types
              (ThetaBaseW_dom v hv)
          have ThetaBaseW_ext_D : SMT.RenamingContext.Extends
              ThetaBaseW ThetaD_alt := by
            intro v d hd
            have hv1 := ThetaD_alt_dom v (by rw [hd]; simp)
            have hv3 : v ∈ St3.types :=
              AList.mem_of_subset St1_sub_St3_types hv1
            have hv_not_vs : v ∉ vs := fun hvs =>
              vs_disj_St1 v hvs hv1
            have hv_not_zs : v ∉ zs := by
              intro hz
              exact zs_not_St3_types v hz hv3
            have hv_not_decl : v ∉ declVars (DltP ++ DltM) := by
              intro hdecl
              apply trace_reordered.declVars_fresh_base v hdecl
              exact (SMT.TypeContext.mem_update_iff
                St3.types v zs sigmas zs_len).mpr (.inr hv3)
            dsimp only [ThetaBaseW]
            rw [Function.updates_of_not_mem ThetaOuter_alt vs _ v
              hv_not_vs]
            simp only [ThetaOuter_alt, boundNames, List.mem_append,
              hv_not_zs, hv_not_decl, or_false, ↓reduceIte]
            exact ThetaM_alt_ext_D hd
          all_goals first
            | have _set_branch := flag_rel
              obtain ⟨ThetaBody_w, hcov_P_w, denPenc_w,
                  ThetaBody_w_ext, related_P_w_out, ThetaBody_w_none,
                  respects_P_w_out, target_respects_P_w, ThetaBody_w_dom,
                  P_specs_w, hden_Penc_w, hdenPenc_w_type, P_w_rel⟩ :=
                P_sc_total XiW XiW_fv ThetaBaseW related_P_base
                  wf_P_w ThetaBaseW_none respects_P_base_PBase
                  ThetaBaseW_dom_PBase Pval_w hPval_w den_P_w
              have ThetaBody_w_ext_Base : SMT.RenamingContext.Extends
                  ThetaBody_w ThetaBaseW := ThetaBody_w_ext
              have ThetaBody_w_ext_D : SMT.RenamingContext.Extends
                  ThetaBody_w ThetaD_alt :=
                SMT.RenamingContext.extends_trans ThetaBody_w_ext
                  ThetaBaseW_ext_D
              let ThetaZ_w := Function.updates ThetaBody_w zs
                (List.ofFn fun i => some (w i))
              have ThetaZ_w_ext : SMT.RenamingContext.Extends
                  ThetaZ_w ThetaBody_w := by
                intro v d hd
                by_cases hzs : v ∈ zs
                · have hv_ctx := ThetaBody_w_dom v (by rw [hd]; simp)
                  exact absurd hv_ctx (zs_not_types v hzs)
                · dsimp only [ThetaZ_w]
                  rw [Function.updates_of_not_mem ThetaBody_w zs _ v hzs]
                  exact hd
              have ThetaZ_w_none : ∀ v ∉ St5.env.usedVars,
                  ThetaZ_w v = none := by
                intro v hv
                have hv_zs : v ∉ zs := fun hzs =>
                  hv (zs_mem_St5_used v hzs)
                dsimp only [ThetaZ_w]
                rw [Function.updates_of_not_mem ThetaBody_w zs _ v hv_zs]
                exact ThetaBody_w_none v
                  (fun hv4 => hv (St4_sub_St5_used hv4))
              have ThetaZ_w_dom : ∀ v, ThetaZ_w v ≠ none →
                  v ∈ St5.types := by
                intro v hv
                by_cases hzs : v ∈ zs
                · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hzs
                  exact AList.lookup_isSome.mp <| by
                    rw [zs_typing i hi]
                    rfl
                · dsimp only [ThetaZ_w] at hv
                  rw [Function.updates_of_not_mem ThetaBody_w zs _ v hzs]
                    at hv
                  exact AList.mem_of_subset St4_sub_St5_types
                    (ThetaBody_w_dom v hv)
              have ThetaZ_w_at_z : ∀ (i : ℕ) (hi : i < zs.length),
                  ThetaZ_w zs[i] = some (w ⟨i, hi⟩) := by
                intro i hi
                dsimp only [ThetaZ_w]
                rw [Function.updates_eq_if (by simp) zs_nodup,
                  dif_pos (List.getElem_mem hi)]
                simp [List.Nodup.idxOf_getElem zs_nodup]
            | have _option_branch := sigmas_eq
              let ThetaP_w := Function.updates ThetaBaseW zs
                (List.ofFn fun i => some (w i))
              have zs_not_fv_P_w : ∀ z ∈ zs, z ∉ B.fv P := by
                intro z hz hfv
                exact zs_not_St3_used z hz
                  (vars_used_P_St3 z (B.Term.mem_vars_iff.mpr (.inl hfv)))
              have related_P_w : RValuationCastSupportedOnFV
                  XiW ThetaP_w P := by
                intro v hv
                have hvz : v ∉ zs := fun hz => zs_not_fv_P_w v hz hv
                simpa [ThetaP_w,
                  Function.updates_of_not_mem ThetaBaseW zs _ v hvz] using
                  related_P_base v hv
              have ThetaP_w_none : ∀ v ∉ St4.env.usedVars,
                  ThetaP_w v = none := by
                intro v hv
                have hvz : v ∉ zs := fun hz =>
                  hv (zs_mem_St5_used v hz)
                change Function.updates ThetaBaseW zs
                  (List.ofFn fun i => some (w i)) v = none
                rw [Function.updates_of_not_mem ThetaBaseW zs _ v hvz]
                exact ThetaBaseW_none v hv
              have ThetaP_w_dom : ∀ v, ThetaP_w v ≠ none →
                  v ∈ PBase.types := by
                intro v hv
                by_cases hvz : v ∈ zs
                · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hvz
                  exact AList.lookup_isSome.mp <| by
                    rw [zs_typing_helper (St₅types := PBase.types)
                      zs_nodup zs_len PBase_types i hi]
                    rfl
                · change Function.updates ThetaBaseW zs
                    (List.ofFn fun i => some (w i)) v ≠ none at hv
                  rw [Function.updates_of_not_mem ThetaBaseW zs _ v hvz] at hv
                  exact ThetaBaseW_dom_PBase v hv
              have respects_P_w :
                  B.RenamingContext.RespectsTypeContextOnFV
                    ThetaP_w PBase.types P := by
                intro v sigma hv hlookup
                obtain ⟨d, hd, hdtype⟩ :=
                  respects_P_base_PBase hv hlookup
                refine ⟨d, ?_, hdtype⟩
                have hvz : v ∉ zs := fun hz => zs_not_fv_P_w v hz hv
                change Function.updates ThetaBaseW zs
                  (List.ofFn fun i => some (w i)) v = some d
                rw [Function.updates_of_not_mem ThetaBaseW zs _ v hvz]
                exact hd
              have ThetaP_w_ext_D : SMT.RenamingContext.Extends
                  ThetaP_w ThetaD_alt := by
                intro v d hd
                have hvz : v ∉ zs := by
                  intro hz
                  have hv1 := ThetaD_alt_dom v (by rw [hd]; simp)
                  exact zs_not_St3_types v hz
                    (AList.mem_of_subset St1_sub_St3_types hv1)
                change Function.updates ThetaBaseW zs
                  (List.ofFn fun i => some (w i)) v = some d
                rw [Function.updates_of_not_mem ThetaBaseW zs _ v hvz]
                exact ThetaBaseW_ext_D hd
              have ThetaP_w_ext_Base : SMT.RenamingContext.Extends
                  ThetaP_w ThetaBaseW := by
                intro v d hd
                have hvz : v ∉ zs := by
                  intro hz
                  exact zs_not_St3_types v hz
                    (ThetaBaseW_dom v (by rw [hd]; simp))
                change Function.updates ThetaBaseW zs
                  (List.ofFn fun i => some (w i)) v = some d
                rw [Function.updates_of_not_mem ThetaBaseW zs _ v hvz]
                exact hd
              obtain ⟨ThetaBody_w, hcov_P_w, denPenc_w,
                  ThetaBody_w_ext, related_P_w_out, ThetaBody_w_none,
                  respects_P_w_out, target_respects_P_w, ThetaBody_w_dom,
                  P_specs_w, hden_Penc_w, hdenPenc_w_type, P_w_rel⟩ :=
                P_sc_total XiW XiW_fv ThetaP_w related_P_w wf_P_w
                  ThetaP_w_none respects_P_w ThetaP_w_dom
                  Pval_w hPval_w den_P_w
              have ThetaBody_w_ext_Base : SMT.RenamingContext.Extends
                  ThetaBody_w ThetaBaseW :=
                SMT.RenamingContext.extends_trans ThetaBody_w_ext
                  ThetaP_w_ext_Base
              have ThetaBody_w_ext_D : SMT.RenamingContext.Extends
                  ThetaBody_w ThetaD_alt :=
                SMT.RenamingContext.extends_trans ThetaBody_w_ext
                  ThetaP_w_ext_D
              let ThetaZ_w := Function.updates ThetaBody_w zs
                (List.ofFn fun i => some (w i))
              have ThetaZ_w_eq : ThetaZ_w = ThetaBody_w := by
                funext v
                by_cases hvz : v ∈ zs
                · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hvz
                  have hbody : ThetaBody_w zs[i] = some (w ⟨i, hi⟩) := by
                    apply ThetaBody_w_ext
                    change Function.updates ThetaBaseW zs
                      (List.ofFn fun i => some (w i)) zs[i] =
                        some (w ⟨i, hi⟩)
                    rw [Function.updates_eq_if (by simp) zs_nodup,
                      dif_pos (List.getElem_mem hi)]
                    simp [List.Nodup.idxOf_getElem zs_nodup]
                  change Function.updates ThetaBody_w zs
                    (List.ofFn fun i => some (w i)) zs[i] = ThetaBody_w zs[i]
                  rw [Function.updates_eq_if (by simp) zs_nodup,
                    dif_pos (List.getElem_mem hi)]
                  simpa [List.Nodup.idxOf_getElem zs_nodup] using hbody.symm
                · change Function.updates ThetaBody_w zs
                    (List.ofFn fun i => some (w i)) v = ThetaBody_w v
                  rw [Function.updates_of_not_mem ThetaBody_w zs _ v hvz]
              have ThetaZ_w_ext : SMT.RenamingContext.Extends
                  ThetaZ_w ThetaBody_w := by
                rw [ThetaZ_w_eq]
                exact SMT.RenamingContext.extends_refl _
              have ThetaZ_w_none : ∀ v ∉ St5.env.usedVars,
                  ThetaZ_w v = none := by
                rw [ThetaZ_w_eq]
                exact ThetaBody_w_none
              have ThetaZ_w_dom : ∀ v, ThetaZ_w v ≠ none →
                  v ∈ St5.types := by
                rw [ThetaZ_w_eq]
                exact ThetaBody_w_dom
              have ThetaZ_w_at_z : ∀ (i : ℕ) (hi : i < zs.length),
                  ThetaZ_w zs[i] = some (w ⟨i, hi⟩) := by
                intro i hi
                dsimp only [ThetaZ_w]
                rw [Function.updates_eq_if (by simp) zs_nodup,
                  dif_pos (List.getElem_mem hi)]
                simp [List.Nodup.idxOf_getElem zs_nodup]
          have hresp_tuple_w :
              SMT.RenamingContext.RespectsTypeContextOnFV
                ThetaZ_w St5.types (zs.map SMT.Term.var).toPairl := by
            intro v sigma hv hlookup
            have hv_zs := fv_pairl_sub_zs_helper zs v hv
            obtain ⟨i, hi, hvi⟩ := List.mem_iff_getElem.mp hv_zs
            subst v
            have hlookup_i := zs_typing i hi
            rw [hlookup_i] at hlookup
            cases hlookup
            refine ⟨w ⟨i, hi⟩, ?_, (hw ⟨i, hi⟩).1⟩
            exact ThetaZ_w_at_z i hi
          have hcov_tuple_w : SMT.RenamingContext.CoversFV
              ThetaZ_w (zs.map SMT.Term.var).toPairl := by
            intro v hv
            obtain ⟨sigma, hlookup⟩ := Option.isSome_iff_exists.mp <|
              AList.lookup_isSome.mpr <|
                SMT.Typing.mem_context_of_mem_fv typ_tuple hv
            obtain ⟨d, hd, _⟩ := hresp_tuple_w hv hlookup
            rw [hd]
            rfl
          obtain ⟨hfold_mem_w, hden_tuple_w_raw⟩ :=
            toPairl_vars_denote_updates zs sigmas zs_len zs_nodup
              (List.length_pos_iff.mpr zs_nemp) ThetaBody_w w hw
              hcov_tuple_w
          have hden_tuple_w :
              ⟦(zs.map SMT.Term.var).toPairl.abstract
                ThetaZ_w hcov_tuple_w⟧ˢ =
                some (⟨x, sigmas.toProdl, hx_mem⟩ : SMT.Dom) := by
            have hdom_eq :
                (⟨Fin.foldl (zs.length - 1)
                    (fun acc i => acc.pair
                      (w ⟨i.val + 1,
                        Nat.add_lt_of_lt_sub i.isLt⟩).fst)
                    (w ⟨0, List.length_pos_iff.mpr zs_nemp⟩).fst,
                  sigmas.toProdl, hfold_mem_w⟩ : SMT.Dom) =
                  ⟨x, sigmas.toProdl, hx_mem⟩ :=
              SMT.RenamingContext.Dom_ext' hw_smt rfl
            exact hden_tuple_w_raw.trans (congrArg some hdom_eq)
          have ThetaZ_w_ext_D : SMT.RenamingContext.Extends
              ThetaZ_w ThetaD_alt :=
            SMT.RenamingContext.extends_trans ThetaZ_w_ext
              ThetaBody_w_ext_D
          have hresp_D_w :
              SMT.RenamingContext.RespectsTypeContextOnFV
                ThetaZ_w St5.types Denc :=
            target_respects_D_alt.of_extends ThetaZ_w_ext_D
              St1_sub_St5_types typ_Denc
          have hcov_D_w : SMT.RenamingContext.CoversFV ThetaZ_w Denc :=
            SMT.RenamingContext.coversFV_of_extends_of_coversFV
              ThetaZ_w_ext_D hcov_D_alt
          have hden_D_w : ⟦Denc.abstract ThetaZ_w hcov_D_w⟧ˢ =
              some denDenc_alt := by
            have hag :=
              SMT.RenamingContext.agreesOnFV_of_extends_of_coversFV
                ThetaZ_w_ext_D hcov_D_alt
            exact (SMT.RenamingContext.denote_congr_of_agreesOnFV
              (t := Denc) (h1 := hcov_D_w) (h2 := hcov_D_alt)
              hag).trans hden_Denc_alt
          have hresp_tuple_w_St6 :
              SMT.RenamingContext.RespectsTypeContextOnFV
                ThetaZ_w St6.types (zs.map SMT.Term.var).toPairl :=
            hresp_tuple_w.of_extends
              (SMT.RenamingContext.extends_refl ThetaZ_w)
              types_sub_M typ_tuple
          have hresp_D_w_St6 :
              SMT.RenamingContext.RespectsTypeContextOnFV
                ThetaZ_w St6.types Denc :=
            hresp_D_w.of_extends
              (SMT.RenamingContext.extends_refl ThetaZ_w)
              types_sub_M typ_Denc_St5
          have ThetaZ_w_dom_St6 : ∀ v, ThetaZ_w v ≠ none →
              v ∈ St6.types :=
            fun v hv => AList.mem_of_subset types_sub_M (ThetaZ_w_dom v hv)
          obtain ⟨mem_good_w, _mem_guard_w⟩ :=
            mem_sem St6.types (fun _ h => h) ThetaZ_w
              hcov_tuple_w hcov_D_w ThetaZ_w_none
              hresp_tuple_w_St6 hresp_D_w_St6 ThetaZ_w_dom_St6
              x_B Dval_alt hx_B_mem hDval_alt
              (⟨x, sigmas.toProdl, hx_mem⟩ : SMT.Dom) denDenc_alt
              hden_tuple_w hden_D_w rfl hdenDenc_alt_type
              tuple_rel_w D_alt_rel
          obtain ⟨ThetaModel, hcov_mem_model, denMem_model,
              ThetaModel_ext, ThetaModel_none,
              target_respects_mem_model, ThetaModel_dom,
              M_specs_model, hden_mem_model, hdenMem_model_type,
              mem_model_iff⟩ := mem_good_w
          have ThetaModel_ext_Body : SMT.RenamingContext.Extends
              ThetaModel ThetaBody_w :=
            SMT.RenamingContext.extends_trans ThetaModel_ext ThetaZ_w_ext
          have ThetaModel_ext_Base : SMT.RenamingContext.Extends
              ThetaModel ThetaBaseW :=
            SMT.RenamingContext.extends_trans ThetaModel_ext_Body
              ThetaBody_w_ext_Base
          have P_specs_model : SpecBodiesTrue ThetaModel GammaM DltP :=
            P_specs_w.of_extends ThetaModel_ext_Body St4_sub_GammaM
              ThetaBody_w_dom
          have M_specs_model' : SpecBodiesTrue ThetaModel GammaM DltM :=
            M_specs_model.of_extends
              (SMT.RenamingContext.extends_refl ThetaModel)
              St6_sub_GammaM ThetaModel_dom
          have all_specs_model : SpecBodiesTrue ThetaModel GammaM
              (DltP ++ DltM) :=
            SpecBodiesTrue.append P_specs_model M_specs_model'
          have ThetaModel_at_vs : ∀ (i : ℕ) (hi : i < vs.length),
              ThetaModel vs[i] = some wsV[i] := by
            intro i hi
            apply ThetaModel_ext_Base
            dsimp only [ThetaBaseW]
            rw [Function.updates_eq_if (by simpa using wsV_len)
              vs_nodup, dif_pos (List.getElem_mem hi)]
            simp [List.Nodup.idxOf_getElem vs_nodup]
          have ThetaModel_at_zs : ∀ (i : ℕ) (hi : i < zs.length),
              ThetaModel zs[i] = some (w ⟨i, hi⟩) := by
            intro i hi
            apply ThetaModel_ext
            dsimp only [ThetaZ_w]
            rw [Function.updates_eq_if (by simp) zs_nodup,
              dif_pos (List.getElem_mem hi)]
            simp [List.Nodup.idxOf_getElem zs_nodup]
          have updates_vs_ThetaModel : Function.updates ThetaModel vs
              (wsV.map Option.some) = ThetaModel := by
            funext v
            by_cases hvs : v ∈ vs
            · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hvs
              rw [Function.updates_eq_if (by simpa using wsV_len)
                vs_nodup, dif_pos (List.getElem_mem hi)]
              simp [List.Nodup.idxOf_getElem vs_nodup,
                ThetaModel_at_vs i hi]
            · exact Function.updates_of_not_mem ThetaModel vs _ v hvs
          have hzs_model : ∀ (i : ℕ) (hi_z : i < zs.length)
              (hi_w : i < wsV.length),
              ThetaModel zs[i] = some wsV[i] := by
            intro i hi_z hi_w
            rw [ThetaModel_at_zs i hi_z]
            have hvi : i < vs.length := by simpa [wsV] using hi_w
            have hget : wsV[i] = wV ⟨i, hvi⟩ :=
              List.getElem_ofFn (f := wV) (h := hi_w)
            rw [hget]
            dsimp only [wV]
            apply congrArg some
            apply congrArg w
            apply Fin.ext
            rfl
          have hzs_type_model : ∀ (i : ℕ) (hi_z : i < zs.length)
              (hi_w : i < wsV.length) (sigma : SMTType),
              GammaM.lookup zs[i] = some sigma →
                wsV[i].snd.fst = sigma := by
            intro i hi_z hi_w sigma hlookup
            have hlookup_base :
                (St3.types.update zs sigmas zs_len).lookup zs[i] =
                  some sigmas[i] := by
              exact SMT.TypeContext.lookup_update_of_mem_nodup
                St3.types zs_nodup zs_len hi_z
            have hlookup_final : GammaM.lookup zs[i] =
                some sigmas[i] :=
              AList.lookup_of_subset trace_reordered.entries_subset
                hlookup_base
            rw [hlookup_final] at hlookup
            cases hlookup
            have hvi : i < vs.length := by simpa [wsV] using hi_w
            have hget : wsV[i] = wV ⟨i, hvi⟩ :=
              List.getElem_ofFn (f := wV) (h := hi_w)
            rw [hget]
            have hfin : Fin.cast vs_zs_len ⟨i, hvi⟩ = ⟨i, hi_z⟩ := by
              apply Fin.ext
              rfl
            simpa [wV, hfin] using (hw ⟨i, hi_z⟩).1
          have target_respects_P_model :
              SMT.RenamingContext.RespectsTypeContextOnFV
                ThetaModel GammaM Penc :=
            target_respects_P_w.of_extends ThetaModel_ext_Body
              St4_sub_GammaM typ_Penc
          have target_respects_subst_P_model :
              SMT.RenamingContext.RespectsTypeContextOnFV ThetaModel
                GammaM (SMT.substList vs
                  (zs.map SMT.Term.var) Penc) := by
            apply SMT.ScopedForall.respects_substList_vars
              Penc vs zs wsV vs_zs_len wsV_len zs_disj_vs
              hzs_model hzs_type_model
            rwa [updates_vs_ThetaModel]
          have target_respects_subst_specs_model :
              ∀ b ∈ specBodies (DltP ++ DltM),
                SMT.RenamingContext.RespectsTypeContextOnFV ThetaModel
                  GammaM (SMT.substList vs
                    (zs.map SMT.Term.var) b) := by
            intro b hb
            obtain ⟨_, _, hresp_b, _, _, _⟩ := all_specs_model b hb
            apply SMT.ScopedForall.respects_substList_vars
              b vs zs wsV vs_zs_len wsV_len zs_disj_vs
              hzs_model hzs_type_model
            rw [updates_vs_ThetaModel]
            exact hresp_b
          have target_respects_mem_model' :
              SMT.RenamingContext.RespectsTypeContextOnFV
                ThetaModel GammaM mem_enc :=
            target_respects_mem_model.of_extends
              (SMT.RenamingContext.extends_refl ThetaModel)
              St6_sub_GammaM typ_mem
          have target_respects_raw_model :
              SMT.RenamingContext.RespectsTypeContextOnFV
                ThetaModel GammaM raw := by
            intro v sigma hv hlookup
            simp only [raw, SMT.fv, List.mem_append] at hv
            exact hv.elim
              (fun h => target_respects_mem_model' h hlookup)
              (fun h => target_respects_subst_P_model h hlookup)
          have target_respects_guards_model : ∀ g ∈ guards,
              SMT.RenamingContext.RespectsTypeContextOnFV
                ThetaModel GammaM g := by
            intro g hg
            obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hg
            exact target_respects_subst_specs_model b hb
          have target_respects_inner_model :
              SMT.RenamingContext.RespectsTypeContextOnFV
                ThetaModel GammaM inner :=
            SMT.ScopedForall.foldr_imp_respects guards raw
              target_respects_guards_model target_respects_raw_model
          have all_specs_model_upd : SpecBodiesTrue
              (Function.updates ThetaModel vs
                (wsV.map Option.some)) GammaM (DltP ++ DltM) := by
            rwa [updates_vs_ThetaModel]
          have model_guards : SMT.ScopedForall.TermsTrue
              ThetaModel guards := by
            exact SMT.ScopedForall.TermsTrue.of_specBodies_subst
              vs zs wsV vs_zs_len wsV_len vs_nodup zs_disj_vs
              specs_bv_fresh hzs_model all_specs_model_upd
          have helper_names_nodup :
              ((declBinders (DltP ++ DltM)).map Prod.fst).Nodup := by
            rw [declBinders_map_fst]
            exact trace_reordered.declVars_nodup
          have helper_lookup : ∀ p ∈ declBinders (DltP ++ DltM),
              GammaM.lookup p.1 = some p.2 := by
            intro p hp
            obtain ⟨v, sigma⟩ := p
            apply AList.mem_lookup_iff.mpr
            exact trace_reordered.declEntries_subset <|
              mem_declEntries_of_mem_declBinders hp
          have outside_agrees : ∀ y ∈ SMT.fv inner,
              y ∉ (declBinders (DltP ++ DltM)).map Prod.fst →
                ThetaW y = ThetaModel y := by
            intro y hy hnot_helpers
            have hy_not_vs : y ∉ vs := by
              intro hvs
              exact vs_not_fv_inner y hvs hy
            by_cases hy_zs : y ∈ zs
            · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hy_zs
              have hW : ThetaW zs[i] = some (w ⟨i, hi⟩) := by
                dsimp only [ThetaW]
                rw [Function.updates_eq_if (by simp) zs_nodup,
                  dif_pos (List.getElem_mem hi)]
                simp [List.Nodup.idxOf_getElem zs_nodup]
              have hZ : ThetaZ_w zs[i] = some (w ⟨i, hi⟩) := by
                dsimp only [ThetaZ_w]
                rw [Function.updates_eq_if (by simp) zs_nodup,
                  dif_pos (List.getElem_mem hi)]
                simp [List.Nodup.idxOf_getElem zs_nodup]
              exact hW.trans (ThetaModel_ext hZ).symm
            · have hy_scoped : y ∈ SMT.fv scopedBody := by
                have foldr_mem : ∀ ps : List (SMT.𝒱 × SMTType),
                    y ∉ ps.map Prod.fst → y ∈ SMT.fv
                      (ps.foldr
                        (fun p t => SMT.Term.forall [p.1] [p.2] t)
                        inner) := by
                  intro ps
                  induction ps with
                  | nil => exact fun _ => hy
                  | cons p ps ih =>
                      obtain ⟨v, sigma⟩ := p
                      intro hnot
                      simp only [List.map_cons, List.mem_cons, not_or]
                        at hnot
                      simp only [List.foldr_cons, SMT.fv,
                        List.mem_removeAll_iff]
                      exact ⟨ih hnot.2, by
                        simpa only [List.mem_singleton] using hnot.1⟩
                exact foldr_mem (declBinders (DltP ++ DltM))
                  hnot_helpers
              obtain ⟨d, hWd⟩ := Option.isSome_iff_exists.mp <|
                hcov_scoped_upd w y hy_scoped
              have hOuter : ThetaOuter_alt y = some d := by
                have h := hWd
                rw [Function.updates_of_not_mem ThetaOuter_alt zs _ y
                  hy_zs] at h
                exact h
              have hBase : ThetaBaseW y = some d := by
                dsimp only [ThetaBaseW]
                rw [Function.updates_of_not_mem ThetaOuter_alt vs _ y
                  hy_not_vs]
                exact hOuter
              exact hWd.trans (ThetaModel_ext_Base hBase).symm
          have some_agrees := SMT.ScopedForall.SomeAssignment.of_model
            (declBinders (DltP ++ DltM)) inner helper_names_nodup
            helper_lookup target_respects_inner_model outside_agrees
          have some_data :=
            SMT.ScopedForall.SomeAssignment.and_all some_agrees
              all_helper_data
          apply some_data.mono
          intro ThetaA hdata hcov_inner
          have guards_A : SMT.ScopedForall.TermsTrue ThetaA guards := by
            intro g hg hcov_g d hden_g
            have hagree_g : SMT.RenamingContext.AgreesOnFV
                ThetaA ThetaModel g := by
              intro v hv
              exact hdata.1 <|
                SMT.ScopedForall.fv_subset_foldr_imp_guard guards raw
                  hg hv
            have hcov_g_model : SMT.RenamingContext.CoversFV
                ThetaModel g :=
              SMT.RenamingContext.coversFV_of_agreesOnFV
                hagree_g hcov_g
            have hden_eq :=
              SMT.RenamingContext.denote_congr_of_agreesOnFV
                (t := g) (h1 := hcov_g) (h2 := hcov_g_model)
                hagree_g
            exact model_guards g hg hcov_g_model d
              (hden_eq.symm.trans hden_g)
          obtain ⟨dRaw, hcovRaw, hdenRaw, htypeRaw, hiffRaw⟩ :=
            guarded_raw ThetaA hdata.2.1 hdata.2.2.1
              hdata.2.2.2 guards_A
          have hnot_true : dRaw.fst ≠ ZFSet.zftrue := by
            intro htrue
            exact hnotQ (hiffRaw.mp htrue)
          have hRawBool : dRaw.fst ∈ ZFSet.𝔹 := by
            simpa [htypeRaw] using dRaw.snd.snd
          rw [ZFSet.ZFBool.mem_𝔹_iff] at hRawBool
          have hfalseRaw : dRaw.fst = ZFSet.zffalse :=
            hRawBool.resolve_right hnot_true
          apply SMT.ScopedForall.foldr_imp_eq_zffalse guards raw
            typ_inner_reordered hcov_inner hdata.2.1 guards_A
          exact ⟨hcovRaw, dRaw, hdenRaw, hfalseRaw⟩
        obtain ⟨dScoped, hden_scoped, _hdScoped_type,
            hscoped_iff⟩ := SMT.ScopedForall.foldr_true_iff
          (declBinders (DltP ++ DltM)) inner Q typ_scoped
          (hcov_scoped_upd w) hresp_scoped_w helper_true helper_false
        have hden_scoped' : ⟦scopedBody.abstract ThetaW
              (hcov_scoped_upd w)⟧ˢ = some dScoped := by
          simpa only [scopedBody] using hden_scoped
        have hbody_eq : dScoped = body_val := Option.some.inj
          (hden_scoped'.symm.trans hbody_val)
        subst body_val
        exact hscoped_iff
      simp only at den_all_alt_rest
      rw [dif_pos tau_hasArity] at den_all_alt_rest
      split_ifs at den_all_alt_rest with hden_P_all htyp_P_det hD_empty
      · have hT_true : T_alt = ZFSet.zftrue := by
          simp only [pure, Option.pure_def] at den_all_alt_rest
          have hdom := Option.some.inj den_all_alt_rest
          exact (congrArg (fun d : B.Dom => d.fst) hdom).symm
        have hgo_cov : ∀ y ∈ SMT.fv scopedBody, y ∉ zs →
            (ThetaOuter_alt y).isSome = true := by
          intro y hy hyzs
          exact hcov_out_alt y (SMT.fv.mem_forall ⟨hy, hyzs⟩)
        have hrel : RDomCast
            (⟨T_alt, BType.bool, hT_alt⟩ : B.Dom) denOut_alt :=
          RDomCast.forall_empty vs_nemp tau_hasArity zs_nemp zs_len
            tuple_le hcov_out_alt hden_out_alt hdenOut_alt_type
            hgo_cov hcov_scoped_upd scoped_total hD_empty
            Xi_fv_alt hT_alt hT_true
            (List.length_pos_iff.mpr zs_nemp) vs_zs_len semantic_bridge
        have hrel_supported : RDomCastSupported
            (⟨T_alt, BType.bool, hT_alt⟩ : B.Dom) denOut_alt :=
          RDom.toRDomCastSupported <|
            (RDomCast.iff_RDom_of_type_eq
              (α := BType.bool) hdenOut_alt_type).mp hrel
        exact ⟨ThetaOuter_alt, hcov_out_alt, denOut_alt,
          ThetaOuter_alt_ext, related_out_alt, ThetaOuter_alt_none,
          respects_out_alt, target_respects_out_alt, ThetaOuter_alt_dom,
          hden_out_alt, hdenOut_alt_type, hrel_supported⟩
      · have hD_nonempty : Dval_alt.Nonempty :=
          Dval_alt.eq_empty_or_nonempty.resolve_left hD_empty
        simp only [pure, Option.pure_def] at den_all_alt_rest
        have hdom_all := Option.some.inj den_all_alt_rest
        have hT_eq := congrArg (fun d : B.Dom => d.fst) hdom_all
        have h_den_P_bool : ∀ {x_fin : Fin vs.length → B.Dom.{u}},
            (∀ i, (x_fin i).snd.fst = tau.get vs.length i ∧
              (x_fin i).fst ∈ ⟦tau.get vs.length i⟧ᶻ) →
            ZFSet.ofFinDom x_fin ∈ Dval_alt →
            ∀ (Pz : ZFSet.{u}) (P_ty : BType)
              (hP_val : Pz ∈ ⟦P_ty⟧ᶻ),
              ⟦(B.Term.abstract.go P vs Xi_alt
                (fun v hv hvs => Xi_fv_alt v
                  (B.fv.mem_all (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ =
                  some ⟨Pz, ⟨P_ty, hP_val⟩⟩ → P_ty = BType.bool := by
          intro x_fin hx_fin _hx_D Pz P_ty hP_val hPden
          let XiX := Function.updates Xi_alt vs
            (List.ofFn fun i => some (x_fin i))
          have XiX_fv : ∀ v ∈ B.fv P, (XiX v).isSome = true := by
            intro v hv
            show (Function.updates Xi_alt vs _ v).isSome = true
            rw [Function.updates_eq_if (by rw [List.length_ofFn])
              vs_nodup]
            split_ifs with hvs
            · simp [List.getElem_ofFn]
            · exact Xi_fv_alt v <|
                B.fv.mem_all (.inr ⟨hv, hvs⟩)
          have hPden_abs : ⟦P.abstract XiX XiX_fv⟧ᴮ =
              some ⟨Pz, ⟨P_ty, hP_val⟩⟩ := by
            rw [← denote_term_abstract_go_eq_term_abstract
              vs_nodup vs_nemp x_fin XiX_fv]
            convert hPden using 2
          have wf_XiX : B.RenWF
              (vs.zipToAList alphas ∪ E.context) XiX := by
            apply B.RenWF.updates_ofFn wf_alt vs_nodup
              vs_context_disj vs_alphas_len
            intro i
            exact (hx_fin i).1.trans <| by
              dsimp only [tau]
              exact BType.get_reduce alphas_nemp vs_alphas_len i
          exact (denote_welltyped_eq
            (t := P.abstract XiX XiX_fv)
            ⟨_, WFTC.of_abstract, BType.bool,
              by convert Typing.of_abstract XiX_fv typ_P⟩
            hPden_abs).symm
        have admissible : BinderCastAdmissible tau sigmas.toProdl
            tuple_le.toCastPath Dval_alt :=
          selected_admissible Xi_alt Xi_fv_D_alt Dval_alt
            hDval_alt den_D_alt tuple_le
        have hgo_cov : ∀ y ∈ SMT.fv scopedBody, y ∉ zs →
            (ThetaOuter_alt y).isSome = true := by
          intro y hy hyzs
          exact hcov_out_alt y (SMT.fv.mem_forall ⟨hy, hyzs⟩)
        have hrel : RDomCast
            (⟨T_alt, BType.bool, hT_alt⟩ : B.Dom) denOut_alt :=
          RDomCast.forall_nonempty vs_nemp vs_nodup tau_hasArity
            zs_nemp zs_len tuple_le hcov_out_alt hden_out_alt
            hdenOut_alt_type hDval_alt hD_nonempty admissible
            hgo_cov hcov_scoped_upd scoped_total scoped_type Xi_fv_alt
            hT_alt (by
              convert hT_eq using 1 <;>
                simp only [optionBDom_value_pattern] <;> rfl)
            hden_P_all h_den_P_bool
            (List.length_pos_iff.mpr zs_nemp) vs_zs_len semantic_bridge
        have hrel_supported : RDomCastSupported
            (⟨T_alt, BType.bool, hT_alt⟩ : B.Dom) denOut_alt :=
          RDom.toRDomCastSupported <|
            (RDomCast.iff_RDom_of_type_eq
              (α := BType.bool) hdenOut_alt_type).mp hrel
        exact ⟨ThetaOuter_alt, hcov_out_alt, denOut_alt,
          ThetaOuter_alt_ext, related_out_alt, ThetaOuter_alt_none,
          respects_out_alt, target_respects_out_alt, ThetaOuter_alt_dom,
          hden_out_alt, hdenOut_alt_type, hrel_supported⟩
    mspec Std.Do.Spec.pure
    mpure_intro
    rw [new_decls_eq]
    change EncodeTermRepPost (B.Term.all vs D P) BType.bool
      St0.types Xi Theta0 used T hT E
      (SMT.Term.forall zs sigmas scopedBody) SMTType.bool
      St8.env St8.types
    refine ⟨used_sub_final, types_sub_final, keys_sub_final,
      covers_final, ⟨castPath.reflexive SMTType.bool⟩,
      typ_out, trivial, ?_, ?_⟩
    · intro v hv_used hv_not_St0 hv_not_vars hv_St8
      rw [St8_types_eq, St3_update] at hv_St8
      rcases (SMT.TypeContext.mem_update_iff
        St1.types v vs sigmas vs_sigmas_len).mp hv_St8 with hvs | hSt1
      · apply hv_not_vars
        unfold B.Term.vars
        rw [List.mem_union_iff]
        right
        simp only [B.bv, List.mem_append]
        exact .inl (.inl hvs)
      · apply D_preserves v hv_used hv_not_St0 _ hSt1
        intro hDvars
        apply hv_not_vars
        unfold B.Term.vars at hDvars ⊢
        rw [List.mem_union_iff] at hDvars ⊢
        rcases hDvars with hDfv | hDbv
        · left
          simp only [B.fv, List.mem_append]
          exact .inl hDfv
        · right
          simp only [B.bv, List.mem_append]
          exact .inl (.inr hDbv)
    · obtain ⟨ThetaFinal, hcovFinal, denFinal,
          ThetaFinal_ext, relatedFinal, ThetaFinal_none,
          respectsFinal, target_respectsFinal, ThetaFinal_dom,
          hdenFinal, hdenFinal_type, relFinal⟩ :=
        all_total Xi Xi_fv Theta0 related wf
          (fun v hv => Theta0_none v (fun h => hv (used_sub_final h)))
          respects Theta0_dom T hT den_t
      exact ⟨ThetaFinal, hcovFinal, ThetaFinal_ext, relatedFinal,
        ThetaFinal_none, respectsFinal, target_respectsFinal,
        ThetaFinal_dom, denFinal, hdenFinal, hdenFinal_type,
        relFinal, all_total⟩
