import Mathlib.Data.List.OfFn
import SMT.Reasoning.Basic.EncodeTermRepresentedBinders
import SMT.Reasoning.Basic.CollectCaseHelpers

open B SMT ZFSet

/-!
# Representation-aware collection

The collection encoder builds an SMT lambda whose body is an `ite`: the
encoded domain predicate selects the substituted predicate body.  The lemmas
here isolate this last semantic step from the operational proof that constructs
the represented contexts.
-/

/- Unfold a successful source collection denotation into the separation
equation used by the SMT-lambda retraction proof.  Keeping this source-only
fact independent of the target representation lets the main and alternative
valuation arguments share it. -/
open Classical in
theorem B.denote_collect_eq_sep.{u}
    {vs : List B.𝒱} {D P : B.Term} {tau : BType}
    {Xi : B.RenamingContext.Context.{u}}
    (Xi_fv : ∀ v ∈ B.fv (B.Term.collect vs D P), (Xi v).isSome = true)
    (tau_hasArity : tau.hasArity vs.length)
    {Dval : ZFSet.{u}} {hDval : Dval ∈ ⟦BType.set tau⟧ᶻ}
    (den_D : ⟦D.abstract Xi
      (fun v hv => Xi_fv v (B.fv.mem_collect (.inl hv)))⟧ᴮ =
      some (⟨Dval, BType.set tau, hDval⟩ : B.Dom))
    {T : ZFSet.{u}} {hT : T ∈ ⟦BType.set tau⟧ᶻ}
    (den_collect : ⟦(B.Term.collect vs D P).abstract Xi Xi_fv⟧ᴮ =
      some (⟨T, BType.set tau, hT⟩ : B.Dom)) :
    ZFSet.sep (fun x =>
      if hx : x.hasArity vs.length ∧ tau.hasArity vs.length ∧ x ∈ ⟦tau⟧ᶻ then
        match ⟦(B.Term.abstract.go P vs Xi (fun v hv hvs => Xi_fv v
          (B.fv.mem_collect (.inr ⟨hv, hvs⟩)))).uncurry
          (fun i => ⟨x.get vs.length i, ⟨tau.get vs.length i,
            get_mem_type_of_isTuple hx.1 hx.2.1 hx.2.2⟩⟩)⟧ᴮ with
        | some ⟨Pz, _⟩ => Pz = ZFSet.zftrue
        | none => False
      else False) Dval = T := by
  have h_inv := den_collect
  simp only [B.Term.abstract] at h_inv
  unfold B.denote at h_inv
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h_inv
  obtain ⟨D_dom, hden_d, rest⟩ := h_inv
  have hconv_d : ⟦D.abstract Xi
      (fun v hv => Xi_fv v (B.fv.mem_collect (.inl hv)))⟧ᴮ =
      some D_dom := by
    convert hden_d using 2
  have hD_dom_eq : D_dom =
      (⟨Dval, BType.set tau, hDval⟩ : B.Dom) := by
    rw [hconv_d] at den_D
    exact Option.some.inj den_D
  subst D_dom
  simp only at rest
  split at rest
  · simp only [Option.bind_eq_some_iff] at rest
    obtain ⟨_, denP_eq, rest2⟩ := rest
    split_ifs at rest2 with h_den_P_cond h_typP_det_cond
    · simp only [Option.pure_def, Option.some.injEq, PSigma.mk.injEq] at rest2
      rw [← rest2.1]
      congr 1
      funext x
      simp
      constructor
      · rintro ⟨hx, match_eq⟩
        exact ⟨hx, by
          split at match_eq
          · rename_i h
            erw [h]
            exact match_eq
          · nomatch match_eq⟩
      · rintro ⟨hx, match_eq⟩
        exact ⟨hx, by
          split at match_eq
          · rename_i h
            erw [h]
            exact match_eq
          · nomatch match_eq⟩
  · rename_i h_neg
    exact absurd
      ⟨BType.hasArity_of_foldl_defaultZFSet tau_hasArity, tau_hasArity⟩
      h_neg

/- A successful source collection denotation also supplies the totality of
its predicate at every tuple selected from its source domain.  This is the
second source-side ingredient of the lambda retraction argument, alongside
`B.denote_collect_eq_sep`. -/
open Classical in
theorem B.denote_collect_predicate_total.{u}
    {vs : List B.𝒱} {D P : B.Term} {tau : BType}
    {Xi : B.RenamingContext.Context.{u}}
    (Xi_fv : ∀ v ∈ B.fv (B.Term.collect vs D P), (Xi v).isSome = true)
    (tau_hasArity : tau.hasArity vs.length)
    {Dval : ZFSet.{u}} {hDval : Dval ∈ ⟦BType.set tau⟧ᶻ}
    (den_D : ⟦D.abstract Xi
      (fun v hv => Xi_fv v (B.fv.mem_collect (.inl hv)))⟧ᴮ =
      some (⟨Dval, BType.set tau, hDval⟩ : B.Dom))
    {T : ZFSet.{u}} {hT : T ∈ ⟦BType.set tau⟧ᶻ}
    (den_collect : ⟦(B.Term.collect vs D P).abstract Xi Xi_fv⟧ᴮ =
      some (⟨T, BType.set tau, hT⟩ : B.Dom)) :
    ∀ {x_fin : Fin vs.length → B.Dom.{u}},
      (∀ i, (x_fin i).snd.fst = tau.get vs.length i ∧
        (x_fin i).fst ∈ ⟦tau.get vs.length i⟧ᶻ) →
      ZFSet.ofFinDom x_fin ∈ Dval →
      ⟦(B.Term.abstract.go P vs Xi (fun v hv hvs => Xi_fv v
        (B.fv.mem_collect (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ.isSome = true := by
  intro x_fin hx_typ hx_mem
  have h_inv := den_collect
  simp only [B.Term.abstract] at h_inv
  unfold B.denote at h_inv
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h_inv
  obtain ⟨D_dom, hden_d, rest⟩ := h_inv
  have hconv_d : ⟦D.abstract Xi
      (fun v hv => Xi_fv v (B.fv.mem_collect (.inl hv)))⟧ᴮ =
      some D_dom := by
    convert hden_d using 2
  have hD_dom_eq : D_dom =
      (⟨Dval, BType.set tau, hDval⟩ : B.Dom) := by
    rw [hconv_d] at den_D
    exact Option.some.inj den_D
  subst D_dom
  simp only at rest
  split at rest
  · simp only [Option.bind_eq_some_iff] at rest
    obtain ⟨_, _, rest2⟩ := rest
    split_ifs at rest2 with h_den_P_cond
    exact h_den_P_cond hx_typ hx_mem
  · rename_i h_neg
    exact absurd
      ⟨BType.hasArity_of_foldl_defaultZFSet tau_hasArity, tau_hasArity⟩
      h_neg

/- Repackage the source predicate-totality condition as the Boolean
denotation needed by the representation-aware body induction hypothesis. -/
open Classical in
theorem B.denote_collect_predicate_exists.{u}
    {vs : List B.𝒱} {D P : B.Term} {tau : BType}
    {Xi : B.RenamingContext.Context.{u}}
    (Xi_fv : ∀ v ∈ B.fv (B.Term.collect vs D P), (Xi v).isSome = true)
    (vs_nemp : vs ≠ []) (vs_nodup : vs.Nodup)
    (tau_hasArity : tau.hasArity vs.length)
    {Dval : ZFSet.{u}} {hDval : Dval ∈ ⟦BType.set tau⟧ᶻ}
    (den_D : ⟦D.abstract Xi
      (fun v hv => Xi_fv v (B.fv.mem_collect (.inl hv)))⟧ᴮ =
      some (⟨Dval, BType.set tau, hDval⟩ : B.Dom))
    {T : ZFSet.{u}} {hT : T ∈ ⟦BType.set tau⟧ᶻ}
    (den_collect : ⟦(B.Term.collect vs D P).abstract Xi Xi_fv⟧ᴮ =
      some (⟨T, BType.set tau, hT⟩ : B.Dom))
    {Ectx : B.TypeContext} (typ_P : Ectx ⊢ᴮ P : BType.bool) :
    ∀ {x_fin : Fin vs.length → B.Dom.{u}},
      (∀ i, (x_fin i).snd.fst = tau.get vs.length i ∧
        (x_fin i).fst ∈ ⟦tau.get vs.length i⟧ᶻ) →
      ZFSet.ofFinDom x_fin ∈ Dval →
      B.RenWF Ectx (Function.updates Xi vs
        (List.ofFn fun i => some (x_fin i))) →
      ∃ (XiP_fv : ∀ v ∈ B.fv P,
          (Function.updates Xi vs
            (List.ofFn fun i => some (x_fin i)) v).isSome = true)
        (Pval : ZFSet.{u}) (hPval : Pval ∈ ⟦BType.bool⟧ᶻ),
        ⟦P.abstract (Function.updates Xi vs
          (List.ofFn fun i => some (x_fin i))) XiP_fv⟧ᴮ =
          some (⟨Pval, BType.bool, hPval⟩ : B.Dom) := by
  intro x_fin hx_typ hx_mem wf_P
  have XiP_fv : ∀ v ∈ B.fv P,
      (Function.updates Xi vs (List.ofFn fun i => some (x_fin i)) v).isSome =
        true := by
    intro v hv
    rw [Function.updates_eq_if (by simp) vs_nodup]
    split_ifs with hvs
    · simp
    · exact Xi_fv v (B.fv.mem_collect (.inr ⟨hv, hvs⟩))
  have hgo_some := B.denote_collect_predicate_total Xi_fv tau_hasArity
    den_D den_collect hx_typ hx_mem
  obtain ⟨⟨Pval, P_ty, hPval⟩, hgo⟩ :=
    Option.isSome_iff_exists.mp hgo_some
  have hden : ⟦P.abstract (Function.updates Xi vs
      (List.ofFn fun i => some (x_fin i))) XiP_fv⟧ᴮ =
      some (⟨Pval, P_ty, hPval⟩ : B.Dom) := by
    rw [← denote_term_abstract_go_eq_term_abstract vs_nodup vs_nemp x_fin
      XiP_fv]
    exact hgo
  have hP_ty : P_ty = BType.bool :=
    (denote_welltyped_eq
      (t := P.abstract (Function.updates Xi vs
        (List.ofFn fun i => some (x_fin i))) XiP_fv)
      ⟨_, WFTC.of_abstract, BType.bool,
        by convert Typing.of_abstract XiP_fv typ_P⟩ hden).symm
  subst P_ty
  exact ⟨XiP_fv, Pval, hPval, hden⟩

/- The source collection semantics evaluates its predicate once at the
canonical default tuple before it can construct the resulting separation.
That evaluation is the seed needed to run the body induction hypothesis for
the outer encoded lambda, even when the source domain is empty. -/
open Classical in
theorem B.denote_collect_default_predicate_exists.{u}
    {vs : List B.𝒱} {D P : B.Term} {tau : BType}
    {Xi : B.RenamingContext.Context.{u}}
    (Xi_fv : ∀ v ∈ B.fv (B.Term.collect vs D P), (Xi v).isSome = true)
    (vs_nemp : vs ≠ []) (vs_nodup : vs.Nodup)
    (tau_hasArity : tau.hasArity vs.length)
    {Dval : ZFSet.{u}} {hDval : Dval ∈ ⟦BType.set tau⟧ᶻ}
    (den_D : ⟦D.abstract Xi
      (fun v hv => Xi_fv v (B.fv.mem_collect (.inl hv)))⟧ᴮ =
      some (⟨Dval, BType.set tau, hDval⟩ : B.Dom))
    {T : ZFSet.{u}} {hT : T ∈ ⟦BType.set tau⟧ᶻ}
    (den_collect : ⟦(B.Term.collect vs D P).abstract Xi Xi_fv⟧ᴮ =
      some (⟨T, BType.set tau, hT⟩ : B.Dom))
    {Ectx : B.TypeContext} (typ_P : Ectx ⊢ᴮ P : BType.bool)
    (wf_P : B.RenWF Ectx
      (Function.updates Xi vs (List.ofFn fun i => some
        (⟨tau.defaultZFSet.get vs.length i, tau.get vs.length i,
          get_mem_type_of_isTuple
            (BType.hasArity_of_foldl_defaultZFSet tau_hasArity)
            tau_hasArity BType.mem_toZFSet_of_defaultZFSet⟩ : B.Dom)))) :
    let x_fin : Fin vs.length → B.Dom.{u} := fun i =>
      ⟨tau.defaultZFSet.get vs.length i, tau.get vs.length i,
        get_mem_type_of_isTuple
          (BType.hasArity_of_foldl_defaultZFSet tau_hasArity)
          tau_hasArity BType.mem_toZFSet_of_defaultZFSet⟩
    ∃ (XiP_fv : ∀ v ∈ B.fv P,
        (Function.updates Xi vs
          (List.ofFn fun i => some (x_fin i)) v).isSome = true)
      (Pval : ZFSet.{u}) (hPval : Pval ∈ ⟦BType.bool⟧ᶻ),
      ⟦P.abstract (Function.updates Xi vs
        (List.ofFn fun i => some (x_fin i))) XiP_fv⟧ᴮ =
        some (⟨Pval, BType.bool, hPval⟩ : B.Dom) := by
  dsimp only
  let x_fin : Fin vs.length → B.Dom := fun i =>
    ⟨tau.defaultZFSet.get vs.length i, tau.get vs.length i,
      get_mem_type_of_isTuple
        (BType.hasArity_of_foldl_defaultZFSet tau_hasArity)
        tau_hasArity BType.mem_toZFSet_of_defaultZFSet⟩
  have XiP_fv : ∀ v ∈ B.fv P,
      (Function.updates Xi vs (List.ofFn fun i => some (x_fin i)) v).isSome =
        true := by
    intro v hv
    rw [Function.updates_eq_if (by simp) vs_nodup]
    split_ifs with hvs
    · simp
    · exact Xi_fv v (B.fv.mem_collect (.inr ⟨hv, hvs⟩))
  have h_inv := den_collect
  simp only [B.Term.abstract] at h_inv
  unfold B.denote at h_inv
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h_inv
  obtain ⟨D_dom, hden_d, rest⟩ := h_inv
  have hconv_d : ⟦D.abstract Xi
      (fun v hv => Xi_fv v (B.fv.mem_collect (.inl hv)))⟧ᴮ =
      some D_dom := by
    convert hden_d using 2
  have hD_dom_eq : D_dom =
      (⟨Dval, BType.set tau, hDval⟩ : B.Dom) := by
    rw [hconv_d] at den_D
    exact Option.some.inj den_D
  subst D_dom
  simp only at rest
  have hdefault_arity : tau.defaultZFSet.hasArity vs.length ∧
      tau.hasArity vs.length :=
    ⟨BType.hasArity_of_foldl_defaultZFSet tau_hasArity, tau_hasArity⟩
  rw [dif_pos hdefault_arity, Option.bind_eq_some_iff] at rest
  obtain ⟨⟨Pval, P_ty, hPval⟩, hgo, _⟩ := rest
  have hden : ⟦P.abstract (Function.updates Xi vs
      (List.ofFn fun i => some (x_fin i))) XiP_fv⟧ᴮ =
      some (⟨Pval, P_ty, hPval⟩ : B.Dom) := by
    rw [← denote_term_abstract_go_eq_term_abstract vs_nodup vs_nemp x_fin
      XiP_fv]
    exact hgo
  have hP_ty : P_ty = BType.bool :=
    (denote_welltyped_eq
      (t := P.abstract (Function.updates Xi vs
        (List.ofFn fun i => some (x_fin i))) XiP_fv)
      ⟨_, WFTC.of_abstract, BType.bool,
        by convert Typing.of_abstract XiP_fv typ_P⟩ hden).symm
  subst P_ty
  exact ⟨XiP_fv, Pval, hPval, hden⟩

/-- The projections introduced by the set-valued collection encoder preserve
the representation relation componentwise.  This packages the dependent
tuple bookkeeping needed when the predicate totality theorem is run under a
particular collection element. -/
theorem toDestPair_denote_represented_components.{u}
    {vs : List B.𝒱} (vs_nemp : vs ≠ [])
    {tau : BType} (tau_hasArity : tau.hasArity vs.length)
    {x : ZFSet.{u}} (hx_mem : x ∈ ⟦tau⟧ᶻ)
    {z : SMT.𝒱} {Delta : SMT.RenamingContext.Context.{u}}
    {Wx : SMT.Dom.{u}}
    (hcov_z : SMT.RenamingContext.CoversFV Delta (.var z))
    (hden_z : ⟦(SMT.Term.var z).abstract Delta hcov_z⟧ˢ = some Wx)
    (hWx_type : Wx.snd.fst = tau.toSMTType)
    (hWx_mem : Wx.fst ∈ ⟦tau.toSMTType⟧ᶻ)
    (hWx_retract : retract tau Wx.fst = x) :
    ∀ (i : ℕ) (hi_vs : i < vs.length)
      (hi_pair : i < (toDestPair vs (.var z)).length),
      ∃ (hcov : SMT.RenamingContext.CoversFV Delta
          ((toDestPair vs (.var z))[i]'hi_pair))
        (Di : SMT.Dom.{u}),
        ⟦((toDestPair vs (.var z))[i]'hi_pair).abstract Delta hcov⟧ˢ =
          some Di ∧
        RDomCastSupported
          (⟨x.get vs.length ⟨i, hi_vs⟩,
            tau.get vs.length ⟨i, hi_vs⟩,
            get_mem_type_of_isTuple
              (hasArity_of_mem_toZFSet tau_hasArity hx_mem)
              tau_hasArity hx_mem⟩ : B.Dom)
          Di := by
  intro i hi_vs hi_pair
  obtain ⟨hcov_i, Di, hden_i, hfst_i, htype_i⟩ :=
    toDestPair_denote_gen tau vs (.var z) Wx Delta [] [] vs_nemp
      hcov_z hden_z hWx_type hWx_mem tau_hasArity rfl (by simp)
      i hi_vs hi_pair
  refine ⟨hcov_i, Di, hden_i, ?_⟩
  apply RDom.toRDomCastSupported
  rw [RDom]
  refine ⟨htype_i, ?_⟩
  calc
    retract (tau.get vs.length ⟨i, hi_vs⟩) Di.fst =
        retract (tau.get vs.length ⟨i, hi_vs⟩)
          (Wx.fst.get vs.length ⟨i, hi_vs⟩) := by rw [hfst_i]
    _ = (retract tau Wx.fst).get vs.length ⟨i, hi_vs⟩ := by
      rw [retract_get_comm
        (hasArity_of_mem_toSMTZFSet tau_hasArity hWx_mem)
        tau_hasArity hWx_mem]
    _ = x.get vs.length ⟨i, hi_vs⟩ := by rw [hWx_retract]

open Classical in
/-- Install the canonical projections of a collection element as a
representation-aware binder valuation.  Outside the binder names the
ambient valuation is unchanged; at the binder names each projection is
related to its source component by the preceding lemma. -/
theorem represented_toDestPair_bound_context.{u}
    {vs : List B.𝒱} (vs_nemp : vs ≠ []) (vs_nodup : vs.Nodup)
    {tau : BType} (tau_hasArity : tau.hasArity vs.length)
    {x : ZFSet.{u}} (hx_mem : x ∈ ⟦tau⟧ᶻ)
    {z : SMT.𝒱} {Delta : SMT.RenamingContext.Context.{u}}
    {Wx : SMT.Dom.{u}}
    (hcov_z : SMT.RenamingContext.CoversFV Delta (.var z))
    (hden_z : ⟦(SMT.Term.var z).abstract Delta hcov_z⟧ˢ = some Wx)
    (hWx_type : Wx.snd.fst = tau.toSMTType)
    (hWx_mem : Wx.fst ∈ ⟦tau.toSMTType⟧ᶻ)
    (hWx_retract : retract tau Wx.fst = x)
    {Xi : B.RenamingContext.Context.{u}}
    {Theta : SMT.RenamingContext.Context.{u}} {P : B.Term}
    (ambient : ∀ v ∈ B.fv P, v ∉ vs →
      match Xi v, Theta v with
      | some d, some d' => RDomCastSupported d d'
      | _, _ => False) :
    ∃ ss : Fin vs.length → SMT.Dom.{u},
      (∀ i,
        ∃ hcov : SMT.RenamingContext.CoversFV Delta
            ((toDestPair vs (.var z))[i.val]'(by
              rw [toDestPair_length_gen vs (.var z) (.var z) [] vs_nemp]
              exact i.isLt)),
          ⟦((toDestPair vs (.var z))[i.val]'(by
              rw [toDestPair_length_gen vs (.var z) (.var z) [] vs_nemp]
              exact i.isLt)).abstract Delta hcov⟧ˢ = some (ss i) ∧
          RDomCastSupported
            (⟨x.get vs.length i, tau.get vs.length i,
              get_mem_type_of_isTuple
                (hasArity_of_mem_toZFSet tau_hasArity hx_mem)
                tau_hasArity hx_mem⟩ : B.Dom)
            (ss i)) ∧
      RValuationCastSupportedOnFV
        (Function.updates Xi vs
          (List.ofFn fun i => some
            (⟨x.get vs.length i, tau.get vs.length i,
              get_mem_type_of_isTuple
                (hasArity_of_mem_toZFSet tau_hasArity hx_mem)
                tau_hasArity hx_mem⟩ : B.Dom)))
        (Function.updates Theta vs
          (List.ofFn fun i => some (ss i))) P := by
  let x_fin : Fin vs.length → B.Dom.{u} := fun i =>
    ⟨x.get vs.length i, tau.get vs.length i,
      get_mem_type_of_isTuple
        (hasArity_of_mem_toZFSet tau_hasArity hx_mem)
        tau_hasArity hx_mem⟩
  have hcomponent : ∀ i : Fin vs.length,
      ∃ (hcov : SMT.RenamingContext.CoversFV Delta
          ((toDestPair vs (.var z))[i.val]'(by
            rw [toDestPair_length_gen vs (.var z) (.var z) [] vs_nemp]
            exact i.isLt)))
        (Di : SMT.Dom.{u}),
        ⟦((toDestPair vs (.var z))[i.val]'(by
            rw [toDestPair_length_gen vs (.var z) (.var z) [] vs_nemp]
            exact i.isLt)).abstract Delta hcov⟧ˢ = some Di ∧
        RDomCastSupported (x_fin i) Di := by
    intro i
    simpa [x_fin] using
      (toDestPair_denote_represented_components vs_nemp tau_hasArity
        hx_mem hcov_z hden_z hWx_type hWx_mem hWx_retract
        i.val i.isLt (by
          rw [toDestPair_length_gen vs (.var z) (.var z) [] vs_nemp]
          exact i.isLt))
  let ss : Fin vs.length → SMT.Dom.{u} := fun i =>
    Classical.choose (Classical.choose_spec (hcomponent i))
  refine ⟨ss, ?_, ?_⟩
  · intro i
    let hcov := Classical.choose (hcomponent i)
    obtain ⟨hden, hrel⟩ :=
      Classical.choose_spec (Classical.choose_spec (hcomponent i))
    refine ⟨hcov, ?_, ?_⟩
    · simpa [ss] using hden
    · simpa [ss, x_fin] using hrel
  · simpa [x_fin] using
      (RValuationCastSupportedOnFV.updates vs_nodup x_fin ss ambient
        (fun i => by
          obtain ⟨hden, hrel⟩ :=
            Classical.choose_spec (Classical.choose_spec (hcomponent i))
          simpa [ss] using hrel))

/-- Applying a canonical characteristic-predicate representative at the
canonical image of a source element in its represented set evaluates to
`true`.  This is the domain side of the `collect` body bridge. -/
theorem represented_set_app_true_of_mem_canonical.{u}
    {tau : BType} {S : ZFSet.{u}} {hS : S ∈ ⟦BType.set tau⟧ᶻ}
    {Denc : SMT.Term} {z : SMT.𝒱}
    {Delta : SMT.RenamingContext.Context.{u}} {Dval : SMT.Dom.{u}}
    (hcov_D_upd : ∀ W : SMT.Dom,
      SMT.RenamingContext.CoversFV
        (Function.update Delta z (some W)) Denc)
    (den_D_upd : ∀ W : SMT.Dom,
      ⟦Denc.abstract (Function.update Delta z (some W))
        (hcov_D_upd W)⟧ˢ = some Dval)
    (hD_type : Dval.snd.fst = tau.toSMTType.fun SMTType.bool)
    (hD_func : ⟦tau.toSMTType⟧ᶻ.IsFunc 𝔹 Dval.fst)
    (D_rel : RDomCastSupported
      (⟨S, BType.set tau, hS⟩ : B.Dom) Dval)
    {x : ZFSet.{u}} (hx : x ∈ S) :
    let Wx : SMT.Dom :=
      ⟨(ZFSet.fapply (BType.canonicalIsoSMTType tau).1
        (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType tau).2.1)
        ⟨x, by
          have hS_sub : S ⊆ ⟦tau⟧ᶻ := by
            rwa [BType.toZFSet, ZFSet.mem_powerset] at hS
          exact (by
            rw [ZFSet.is_func_dom_eq
              (BType.canonicalIsoSMTType tau).2.1]
            exact hS_sub hx)⟩).1,
        tau.toSMTType, ZFSet.fapply_mem_range _ _⟩
    ∃ (hcov : SMT.RenamingContext.CoversFV
        (Function.update Delta z (some Wx)) ((@ˢDenc) (.var z)))
      (Dapp : SMT.Dom.{u}),
      ⟦((@ˢDenc) (.var z)).abstract
        (Function.update Delta z (some Wx)) hcov⟧ˢ = some Dapp ∧
      Dapp.snd.fst = SMTType.bool ∧ Dapp.fst = ZFSet.zftrue := by
  rcases Dval with ⟨F, sigma, hF⟩
  dsimp at hD_type
  subst sigma
  let Dval : SMT.Dom := ⟨F, tau.toSMTType.fun SMTType.bool, hF⟩
  have hD_type : Dval.snd.fst = tau.toSMTType.fun SMTType.bool := rfl
  have hD_func' : ⟦tau.toSMTType⟧ᶻ.IsFunc 𝔹 Dval.fst := by
    simpa [Dval] using hD_func
  have D_rel' : RDomCastSupported
      (⟨S, BType.set tau, hS⟩ : B.Dom) Dval := by
    simpa [Dval] using D_rel
  dsimp
  have hS_sub : S ⊆ ⟦tau⟧ᶻ := by
    rwa [BType.toZFSet, ZFSet.mem_powerset] at hS
  have hx_tau : x ∈ ⟦tau⟧ᶻ := hS_sub hx
  let Wx : SMT.Dom :=
    ⟨(ZFSet.fapply (BType.canonicalIsoSMTType tau).1
      (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType tau).2.1)
      ⟨x, by
        rwa [ZFSet.is_func_dom_eq
          (BType.canonicalIsoSMTType tau).2.1]⟩).1,
      tau.toSMTType, ZFSet.fapply_mem_range _ _⟩
  have hWx_type : Wx.snd.fst = tau.toSMTType := rfl
  have hWx_mem : Wx.fst ∈ ⟦tau.toSMTType⟧ᶻ := Wx.snd.snd
  obtain ⟨hcov_app, Dapp, hDapp_type, hDapp_value, hden_app⟩ :=
    funDenoteAppAt (Δctx := Delta) (t := Denc) (x := z)
      (α := tau.toSMTType) (β := SMTType.bool) (Y := Dval)
      hcov_D_upd den_D_upd hD_type hD_func' Wx hWx_type hWx_mem
  refine ⟨hcov_app, Dapp, hden_app, hDapp_type, ?_⟩
  rw [hDapp_value]
  have D_canonical : (⟨S, BType.set tau, hS⟩ : B.Dom) ≘ᶻ Dval :=
    (RDomCast.iff_RDom_of_type_eq (α := BType.set tau) rfl).mp
      D_rel'.toRDomCast
  rw [RDom] at D_canonical
  have hx_retract : x ∈ retract (BType.set tau) Dval.fst := by
    rw [D_canonical.2]
    exact hx
  rw [retract, ZFSet.mem_sep, dif_pos hx_tau, dif_pos hD_func'] at hx_retract
  simpa [Wx] using hx_retract.2

/-- If the collection-domain application is true, the generated `ite` has the
same truth value as its substituted predicate branch. -/
theorem collect_ite_truth_of_true_domain.{u}
    {Dapp Psub body : SMT.Term} {Theta : SMT.RenamingContext.Context.{u}}
    (hbody_def : body = Dapp.ite Psub (.bool false))
    (hcov_body : SMT.RenamingContext.CoversFV Theta body)
    (hcov_Dapp : SMT.RenamingContext.CoversFV Theta Dapp)
    (hcov_Psub : SMT.RenamingContext.CoversFV Theta Psub)
    {dD dP dBody : SMT.Dom.{u}}
    (hden_Dapp : ⟦Dapp.abstract Theta hcov_Dapp⟧ˢ = some dD)
    (hden_Psub : ⟦Psub.abstract Theta hcov_Psub⟧ˢ = some dP)
    (hden_body : ⟦body.abstract Theta hcov_body⟧ˢ = some dBody)
    (hD_type : dD.snd.fst = SMTType.bool)
    (hD_true : dD.fst = ZFSet.zftrue) :
    dBody = dP := by
  rcases dD with ⟨Dval, sigmaD, hD_mem⟩
  dsimp at hD_type hD_true
  subst sigmaD
  subst body
  rw [SMT.Term.abstract, SMT.denote, Option.bind_eq_bind] at hden_body
  conv at hden_body =>
    lhs
    rw [SMT.RenamingContext.denote_abstract_proof_irrel Dapp Theta _ hcov_Dapp]
  rw [hden_Dapp] at hden_body
  simp only [Option.bind_some] at hden_body
  have hD_bool : ZFSet.ZFBool.toBool ⟨Dval, hD_mem⟩ = true := by
    rw [show (⟨Dval, hD_mem⟩ : ZFSet.ZFBool) =
      ⟨ZFSet.zftrue, ZFSet.ZFBool.zftrue_mem_𝔹⟩ from Subtype.ext hD_true]
    exact ZFSet.ZFBool.toBool_true
  rw [show ZFSet.ZFBool.toBool ⟨Dval, _⟩ = true from by
    convert hD_bool] at hden_body
  simp only [ite_true] at hden_body
  conv at hden_body =>
    lhs
    rw [SMT.RenamingContext.denote_abstract_proof_irrel Psub Theta _ hcov_Psub]
  rw [hden_Psub] at hden_body
  exact Option.some.inj hden_body.symm

/-- The full collection-body bridge: once the represented predicate body is
transported through its binder substitution, a true domain application makes
the generated `ite` true exactly when the B predicate is true. -/
theorem collect_ite_truth_of_represented_subst.{u}
    {Dapp Penc body : SMT.Term}
    (xs : List SMT.𝒱) (ts : List SMT.Term)
    {Delta ThetaBody : SMT.RenamingContext.Context.{u}}
    (Ds : List SMT.Dom.{u})
    (hbody_def : body = Dapp.ite (SMT.substList xs ts Penc) (.bool false))
    (hcov_body : SMT.RenamingContext.CoversFV Delta body)
    (hcov_Dapp : SMT.RenamingContext.CoversFV Delta Dapp)
    (hlen_xt : xs.length = ts.length) (hlen_xd : xs.length = Ds.length)
    (hnodup : xs.Nodup)
    (hxs_not_bv : ∀ x ∈ xs, x ∉ SMT.bv Penc)
    (hts_bv_nil : ∀ t ∈ ts, SMT.bv t = [])
    (hts_fv_not_bv : ∀ t ∈ ts, ∀ w ∈ SMT.fv t, w ∉ SMT.bv Penc)
    (hts_not_none : ∀ t ∈ ts, t ≠ SMT.Term.none)
    (hts_fv_disj_xs : ∀ t ∈ ts, ∀ w ∈ SMT.fv t, w ∉ xs)
    (hts_den : ∀ (i : ℕ) (_hi_x : i < xs.length) (hi_t : i < ts.length)
      (hi_d : i < Ds.length),
      ∃ (ht_cov : SMT.RenamingContext.CoversFV Delta ts[i]),
        ⟦ts[i].abstract Delta ht_cov⟧ˢ = some Ds[i])
    (hcov_sub : SMT.RenamingContext.CoversFV Delta
      (SMT.substList xs ts Penc))
    (hcov_upd : SMT.RenamingContext.CoversFV
      (Function.updates Delta xs (Ds.map Option.some)) Penc)
    (hcov_body_P : SMT.RenamingContext.CoversFV ThetaBody Penc)
    (hagrees : SMT.RenamingContext.AgreesOnFV
      (Function.updates Delta xs (Ds.map Option.some)) ThetaBody Penc)
    {P : ZFSet.{u}} {hP : P ∈ ⟦BType.bool⟧ᶻ}
    {dP : SMT.Dom.{u}}
    (hden_P : ⟦Penc.abstract ThetaBody hcov_body_P⟧ˢ = some dP)
    (hrel_P : RDomCastSupported
      (⟨P, BType.bool, hP⟩ : B.Dom) dP)
    {dD dBody : SMT.Dom.{u}}
    (hden_D : ⟦Dapp.abstract Delta hcov_Dapp⟧ˢ = some dD)
    (hden_body : ⟦body.abstract Delta hcov_body⟧ˢ = some dBody)
    (hD_type : dD.snd.fst = SMTType.bool)
    (hD_true : dD.fst = ZFSet.zftrue) :
    dBody.fst = ZFSet.zftrue ↔ P = ZFSet.zftrue := by
  obtain ⟨hden_sub, htruth_sub⟩ :=
    SMT.RenamingContext.denote_substList_bool_truth_of_agrees
      Penc xs ts Ds hlen_xt hlen_xd hnodup hxs_not_bv hts_bv_nil
      hts_fv_not_bv hts_not_none hts_fv_disj_xs hts_den hcov_sub
      hcov_upd hcov_body_P hagrees hden_P hrel_P
  have hbody_eq := collect_ite_truth_of_true_domain hbody_def hcov_body
    hcov_Dapp hcov_sub hden_D hden_sub hden_body hD_type hD_true
  rw [hbody_eq]
  exact htruth_sub

/-- Collection-body truth from source-level agreement.  This is the form
consumed by the operational `collect` proof after its body IH supplies the
bound-variable denotations and the stable-body free-variable bound. -/
theorem collect_ite_truth_of_represented_source_fv.{u}
    {Dapp Penc body : SMT.Term}
    (xs : List SMT.𝒱) (ts : List SMT.Term)
    {Delta ThetaBase ThetaBody : SMT.RenamingContext.Context.{u}}
    (Ds : List SMT.Dom.{u}) {source : B.Term}
    (hbody_def : body = Dapp.ite (SMT.substList xs ts Penc) (.bool false))
    (hcov_body : SMT.RenamingContext.CoversFV Delta body)
    (hcov_Dapp : SMT.RenamingContext.CoversFV Delta Dapp)
    (hlen_xt : xs.length = ts.length) (hlen_xd : xs.length = Ds.length)
    (hnodup : xs.Nodup)
    (hxs_not_bv : ∀ x ∈ xs, x ∉ SMT.bv Penc)
    (hts_bv_nil : ∀ t ∈ ts, SMT.bv t = [])
    (hts_fv_not_bv : ∀ t ∈ ts, ∀ w ∈ SMT.fv t, w ∉ SMT.bv Penc)
    (hts_not_none : ∀ t ∈ ts, t ≠ SMT.Term.none)
    (hts_fv_disj_xs : ∀ t ∈ ts, ∀ w ∈ SMT.fv t, w ∉ xs)
    (hts_den : ∀ (i : ℕ) (_hi_x : i < xs.length) (hi_t : i < ts.length)
      (hi_d : i < Ds.length),
      ∃ (ht_cov : SMT.RenamingContext.CoversFV Delta ts[i]),
        ⟦ts[i].abstract Delta ht_cov⟧ˢ = some Ds[i])
    (hcov_sub : SMT.RenamingContext.CoversFV Delta
      (SMT.substList xs ts Penc))
    (hcov_upd : SMT.RenamingContext.CoversFV
      (Function.updates Delta xs (Ds.map Option.some)) Penc)
    (hcov_body_P : SMT.RenamingContext.CoversFV ThetaBody Penc)
    (hvalues : ∀ (i : ℕ) (hi_x : i < xs.length) (hi_d : i < Ds.length),
      ThetaBody xs[i] = some Ds[i])
    (hPenc_fv : SMT.fv Penc ⊆ B.Term.vars source)
    (hctx_source : ∀ v ∈ B.Term.vars source, v ∉ xs →
      Delta v = ThetaBase v)
    (hbody_ext : SMT.RenamingContext.Extends ThetaBody ThetaBase)
    {P : ZFSet.{u}} {hP : P ∈ ⟦BType.bool⟧ᶻ}
    {dP : SMT.Dom.{u}}
    (hden_P : ⟦Penc.abstract ThetaBody hcov_body_P⟧ˢ = some dP)
    (hrel_P : RDomCastSupported
      (⟨P, BType.bool, hP⟩ : B.Dom) dP)
    {dD dBody : SMT.Dom.{u}}
    (hden_D : ⟦Dapp.abstract Delta hcov_Dapp⟧ˢ = some dD)
    (hden_body : ⟦body.abstract Delta hcov_body⟧ˢ = some dBody)
    (hD_type : dD.snd.fst = SMTType.bool)
    (hD_true : dD.fst = ZFSet.zftrue) :
    dBody.fst = ZFSet.zftrue ↔ P = ZFSet.zftrue := by
  exact collect_ite_truth_of_represented_subst
    xs ts Ds hbody_def hcov_body hcov_Dapp hlen_xt hlen_xd hnodup
    hxs_not_bv hts_bv_nil hts_fv_not_bv hts_not_none hts_fv_disj_xs
    hts_den hcov_sub hcov_upd hcov_body_P
    (SMT.RenamingContext.agreesOnFV_updates_of_source_fv
      hlen_xd hnodup hcov_upd hvalues hPenc_fv hctx_source hbody_ext)
    hden_P hrel_P hden_D hden_body hD_type hD_true

/-- The operational form of the represented collection-body bridge.  It runs
the predicate's representation-aware totality theorem at the supplied bound
values, then applies the stable-free-variable substitution bridge.  In
particular, no equality with `B.RenamingContext.toSMT` is required. -/
theorem collect_ite_truth_of_total_body_source_fv.{u}
    {Dapp Penc body : SMT.Term}
    (xs : List SMT.𝒱) (ts : List SMT.Term)
    {Delta ThetaBase : SMT.RenamingContext.Context.{u}}
    (Ds : List SMT.Dom.{u})
    (hbody_def : body = Dapp.ite (SMT.substList xs ts Penc) (.bool false))
    (hcov_body : SMT.RenamingContext.CoversFV Delta body)
    (hcov_Dapp : SMT.RenamingContext.CoversFV Delta Dapp)
    (hlen_xt : xs.length = ts.length) (hlen_xd : xs.length = Ds.length)
    (hnodup : xs.Nodup)
    (hxs_not_bv : ∀ x ∈ xs, x ∉ SMT.bv Penc)
    (hts_bv_nil : ∀ t ∈ ts, SMT.bv t = [])
    (hts_fv_not_bv : ∀ t ∈ ts, ∀ w ∈ SMT.fv t, w ∉ SMT.bv Penc)
    (hts_not_none : ∀ t ∈ ts, t ≠ SMT.Term.none)
    (hts_fv_disj_xs : ∀ t ∈ ts, ∀ w ∈ SMT.fv t, w ∉ xs)
    (hts_den : ∀ (i : ℕ) (_hi_x : i < xs.length) (hi_t : i < ts.length)
      (hi_d : i < Ds.length),
      ∃ (ht_cov : SMT.RenamingContext.CoversFV Delta ts[i]),
        ⟦ts[i].abstract Delta ht_cov⟧ˢ = some Ds[i])
    (hcov_sub : SMT.RenamingContext.CoversFV Delta
      (SMT.substList xs ts Penc))
    (hcov_upd : SMT.RenamingContext.CoversFV
      (Function.updates Delta xs (Ds.map Option.some)) Penc)
    {Pterm : B.Term} {E : B.Env} {Lambda Gamma : SMT.TypeContext}
    {sigma : SMTType} {used : List SMT.𝒱}
    (P_total : EncodeTermRepTotal.{u}
      Pterm E BType.bool Lambda Penc sigma Gamma used)
    {Xi : B.RenamingContext.Context.{u}}
    (Xi_fv : ∀ v ∈ B.fv Pterm, (Xi v).isSome = true)
    (related : RValuationCastSupportedOnFV Xi ThetaBase Pterm)
    (wf : B.RenWF E.context Xi)
    (ThetaBase_none : ∀ v ∉ used, ThetaBase v = none)
    (source_respects : B.RenamingContext.RespectsTypeContextOnFV
      ThetaBase Lambda Pterm)
    (ThetaBase_dom : ∀ v, ThetaBase v ≠ none → v ∈ Lambda)
    {Pval : ZFSet.{u}} {hPval : Pval ∈ ⟦BType.bool⟧ᶻ}
    (den_P : ⟦Pterm.abstract Xi Xi_fv⟧ᴮ =
      some (⟨Pval, BType.bool, hPval⟩ : B.Dom))
    (bound_values : ∀ (i : ℕ) (hi_x : i < xs.length) (hi_d : i < Ds.length),
      ThetaBase xs[i] = some Ds[i])
    (hPenc_fv : SMT.fv Penc ⊆ B.Term.vars Pterm)
    (hctx_source : ∀ v ∈ B.Term.vars Pterm, v ∉ xs →
      Delta v = ThetaBase v)
    {dD dBody : SMT.Dom.{u}}
    (hden_D : ⟦Dapp.abstract Delta hcov_Dapp⟧ˢ = some dD)
    (hden_body : ⟦body.abstract Delta hcov_body⟧ˢ = some dBody)
    (hD_type : dD.snd.fst = SMTType.bool)
    (hD_true : dD.fst = ZFSet.zftrue) :
    dBody.fst = ZFSet.zftrue ↔ Pval = ZFSet.zftrue := by
  obtain ⟨ThetaBody, hcov_P, dP, hbody_ext, hvalues, hbody_rel,
    _hbody_none, _source_respects, _target_respects, _hbody_dom,
    hden_P, _hdP_type, hrel_P⟩ :=
    EncodeTermRepTotal.bound_body P_total Xi_fv related wf ThetaBase_none
      source_respects ThetaBase_dom den_P bound_values
  exact collect_ite_truth_of_represented_source_fv
    xs ts Ds hbody_def hcov_body hcov_Dapp hlen_xt hlen_xd hnodup
    hxs_not_bv hts_bv_nil hts_fv_not_bv hts_not_none hts_fv_disj_xs
    hts_den hcov_sub hcov_upd hcov_P hvalues hPenc_fv hctx_source
    hbody_ext hden_P hrel_P hden_D hden_body hD_type hD_true

/-- Specialize the represented collection-body bridge to the tuple projections
emitted by the encoder.  This packages the routine length, freshness, and
denotation facts for `toDestPair`, leaving callers with the semantic data for
the dynamically chosen binder values. -/
theorem collect_ite_truth_of_total_body_toDestPair.{u}
    {Dapp Penc body : SMT.Term}
    {vs : List SMT.𝒱} (vs_nemp : vs ≠ []) (vs_nodup : vs.Nodup)
    {z : SMT.𝒱}
    {Delta ThetaBase : SMT.RenamingContext.Context.{u}}
    {ss : Fin vs.length → SMT.Dom.{u}}
    (hbody_def : body = Dapp.ite
      (SMT.substList vs (toDestPair vs (.var z)) Penc) (.bool false))
    (hcov_body : SMT.RenamingContext.CoversFV Delta body)
    (hcov_Dapp : SMT.RenamingContext.CoversFV Delta Dapp)
    (hcov_sub : SMT.RenamingContext.CoversFV Delta
      (SMT.substList vs (toDestPair vs (.var z)) Penc))
    (hcov_upd : SMT.RenamingContext.CoversFV
      (Function.updates Delta vs ((List.ofFn ss).map Option.some)) Penc)
    (hvs_not_bv : ∀ v ∈ vs, v ∉ SMT.bv Penc)
    (hz_not_bv : z ∉ SMT.bv Penc)
    (hz_not_vs : z ∉ vs)
    (hcomponents : ∀ i : Fin vs.length,
      ∃ hcov : SMT.RenamingContext.CoversFV Delta
          ((toDestPair vs (.var z))[i.val]'(by
            rw [toDestPair_length_gen vs (.var z) (.var z) [] vs_nemp]
            exact i.isLt)),
        ⟦((toDestPair vs (.var z))[i.val]'(by
          rw [toDestPair_length_gen vs (.var z) (.var z) [] vs_nemp]
          exact i.isLt)).abstract Delta hcov⟧ˢ = some (ss i))
    {Pterm : B.Term} {E : B.Env} {Lambda Gamma : SMT.TypeContext}
    {sigma : SMTType} {used : List SMT.𝒱}
    (P_total : EncodeTermRepTotal.{u}
      Pterm E BType.bool Lambda Penc sigma Gamma used)
    {Xi : B.RenamingContext.Context.{u}}
    (Xi_fv : ∀ v ∈ B.fv Pterm, (Xi v).isSome = true)
    (related : RValuationCastSupportedOnFV Xi ThetaBase Pterm)
    (wf : B.RenWF E.context Xi)
    (ThetaBase_none : ∀ v ∉ used, ThetaBase v = none)
    (source_respects : B.RenamingContext.RespectsTypeContextOnFV
      ThetaBase Lambda Pterm)
    (ThetaBase_dom : ∀ v, ThetaBase v ≠ none → v ∈ Lambda)
    {Pval : ZFSet.{u}} {hPval : Pval ∈ ⟦BType.bool⟧ᶻ}
    (den_P : ⟦Pterm.abstract Xi Xi_fv⟧ᴮ =
      some (⟨Pval, BType.bool, hPval⟩ : B.Dom))
    (bound_values : ∀ (i : ℕ) (hi_x : i < vs.length)
      (_hi_d : i < (List.ofFn ss).length),
      ThetaBase vs[i] = some (ss ⟨i, hi_x⟩))
    (hPenc_fv : SMT.fv Penc ⊆ B.Term.vars Pterm)
    (hctx_source : ∀ v ∈ B.Term.vars Pterm, v ∉ vs →
      Delta v = ThetaBase v)
    {dD dBody : SMT.Dom.{u}}
    (hden_D : ⟦Dapp.abstract Delta hcov_Dapp⟧ˢ = some dD)
    (hden_body : ⟦body.abstract Delta hcov_body⟧ˢ = some dBody)
    (hD_type : dD.snd.fst = SMTType.bool)
    (hD_true : dD.fst = ZFSet.zftrue) :
    dBody.fst = ZFSet.zftrue ↔ Pval = ZFSet.zftrue := by
  have hlen_xt : vs.length = (toDestPair vs (.var z)).length := by
    rw [toDestPair_length_gen vs (.var z) (.var z) [] vs_nemp]
    simp
  have hlen_xd : vs.length = (List.ofFn ss).length := by simp
  have hbound_values : ∀ (i : ℕ) (hi_x : i < vs.length)
      (hi_d : i < (List.ofFn ss).length),
      ThetaBase vs[i] = some (List.ofFn ss)[i] := by
    intro i hi_x hi_d
    simpa only [List.getElem_ofFn, Fin.getElem_fin] using
      bound_values i hi_x hi_d
  have hts_fv_not_bv : ∀ t ∈ toDestPair vs (.var z),
      ∀ w ∈ SMT.fv t, w ∉ SMT.bv Penc := by
    intro t ht w hw
    rw [SMT_fv_toDestPair_subset ht hw]
    exact hz_not_bv
  have hts_fv_disj_xs : ∀ t ∈ toDestPair vs (.var z),
      ∀ w ∈ SMT.fv t, w ∉ vs := by
    intro t ht w hw
    rw [SMT_fv_toDestPair_subset ht hw]
    exact hz_not_vs
  have hts_den : ∀ (i : ℕ) (_hi_x : i < vs.length)
      (hi_t : i < (toDestPair vs (.var z)).length)
      (hi_d : i < (List.ofFn ss).length),
      ∃ (ht_cov : SMT.RenamingContext.CoversFV Delta
          (toDestPair vs (.var z))[i]),
        ⟦(toDestPair vs (.var z))[i].abstract Delta ht_cov⟧ˢ =
          some (List.ofFn ss)[i] := by
    intro i hi_x _hi_t _hi_d
    let j : Fin vs.length := ⟨i, hi_x⟩
    obtain ⟨hcov, hden⟩ := hcomponents j
    refine ⟨hcov, ?_⟩
    simpa [j] using hden
  exact collect_ite_truth_of_total_body_source_fv
    (xs := vs) (ts := toDestPair vs (.var z)) (Ds := List.ofFn ss)
    (Delta := Delta) (ThetaBase := ThetaBase)
    (Pterm := Pterm) (E := E) (Lambda := Lambda) (Gamma := Gamma)
    (sigma := sigma) (used := used) (P_total := P_total)
    (Xi := Xi) (Xi_fv := Xi_fv) (related := related) (wf := wf)
    (ThetaBase_none := ThetaBase_none)
    (source_respects := source_respects) (ThetaBase_dom := ThetaBase_dom)
    (Pval := Pval) (hPval := hPval) (den_P := den_P)
    (bound_values := hbound_values) (hPenc_fv := hPenc_fv)
    (hctx_source := hctx_source) (dD := dD) (dBody := dBody)
    (hden_D := hden_D) (hden_body := hden_body)
    (hD_type := hD_type) (hD_true := hD_true)
    (hbody_def := hbody_def) (hcov_body := hcov_body)
    (hcov_Dapp := hcov_Dapp) (hcov_sub := hcov_sub)
    (hcov_upd := hcov_upd) (hlen_xt := hlen_xt) (hlen_xd := hlen_xd)
    (hnodup := vs_nodup) (hxs_not_bv := hvs_not_bv)
    (hts_bv_nil := toDestPair_bv_nil) (hts_fv_not_bv := hts_fv_not_bv)
    (hts_not_none := toDestPair_ne_none) (hts_fv_disj_xs := hts_fv_disj_xs)
    (hts_den := hts_den)

/-- A fixed Boolean B denotation is equivalent to the extensional truth
form required by the collection retraction lemma.  The latter quantifies over
all dependent-pair presentations of the same `Option B.Dom`; injectivity of
`some` identifies their underlying values. -/
theorem B.denote_bool_true_iff_forall.{u}
    {e : Option B.Dom.{u}} {P : ZFSet.{u}}
    {hP : P ∈ ⟦BType.bool⟧ᶻ}
    (hden : e = some (⟨P, BType.bool, hP⟩ : B.Dom)) :
    P = ZFSet.zftrue ↔
      ∀ (Px : ZFSet.{u}) (P_ty : BType) (hPx : Px ∈ ⟦P_ty⟧ᶻ),
        e = some (⟨Px, P_ty, hPx⟩ : B.Dom) → Px = ZFSet.zftrue := by
  constructor
  · intro htrue Px P_ty hPx hden'
    have heq : (⟨P, BType.bool, hP⟩ : B.Dom) =
        ⟨Px, P_ty, hPx⟩ :=
      Option.some.inj (hden.symm.trans hden')
    have hvalue : P = Px := congrArg PSigma.fst heq
    rw [← hvalue]
    exact htrue
  · intro h
    exact h P BType.bool hP hden

/-- Convert a pointwise Boolean body bridge into the extensional bridge used
by `retract_lamVal_eq_collect`.  The pointwise form is what the
representation-aware predicate totality theorem produces; the target form
quantifies over all dependent presentations of the source Boolean result. -/
theorem collect_hbridge_of_pointwise_bool.{u}
    {vs : List B.𝒱} {D P : B.Term} {tau : BType}
    {Dval : ZFSet.{u}}
    {Xi : B.RenamingContext.Context.{u}}
    (Xi_fv : ∀ v ∈ B.fv (B.Term.collect vs D P), (Xi v).isSome = true)
    {Delta : SMT.RenamingContext.Context.{u}} {z : SMT.𝒱}
    {ite_body : SMT.Term}
    (tau_hasArity : tau.hasArity vs.length)
    (hcov_ite_upd : ∀ W : SMT.Dom,
      SMT.RenamingContext.CoversFV (Function.update Delta z (some W))
        ite_body)
    (pointwise : ∀ (x : ZFSet.{u}) (hx_mem : x ∈ ⟦tau⟧ᶻ)
      (_hx_D : x ∈ Dval),
      let Wx : SMT.Dom :=
        ⟨(ZFSet.fapply (BType.canonicalIsoSMTType tau).1
          (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType tau).2.1)
          ⟨x, by rwa [ZFSet.is_func_dom_eq
            (BType.canonicalIsoSMTType tau).2.1]⟩).1,
          tau.toSMTType, ZFSet.fapply_mem_range _ _⟩
      let x_fin : Fin vs.length → B.Dom := fun i =>
        ⟨x.get vs.length i, ⟨tau.get vs.length i,
          get_mem_type_of_isTuple
            (hasArity_of_mem_toZFSet tau_hasArity hx_mem)
            tau_hasArity hx_mem⟩⟩
      ∀ body_val : SMT.Dom,
        ⟦ite_body.abstract (Function.update Delta z (some Wx))
          (hcov_ite_upd Wx)⟧ˢ = some body_val →
        ∃ (Pval : ZFSet.{u}) (hPval : Pval ∈ ⟦BType.bool⟧ᶻ),
          ⟦(B.Term.abstract.go P vs Xi (fun v hv hvs => Xi_fv v
            (B.fv.mem_collect (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ =
            some (⟨Pval, BType.bool, hPval⟩ : B.Dom) ∧
          (body_val.fst = ZFSet.zftrue ↔ Pval = ZFSet.zftrue)) :
    ∀ (x : ZFSet.{u}) (hx_mem : x ∈ ⟦tau⟧ᶻ)
      (_hx_D : x ∈ Dval),
      let Wx : SMT.Dom :=
        ⟨(ZFSet.fapply (BType.canonicalIsoSMTType tau).1
          (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType tau).2.1)
          ⟨x, by rwa [ZFSet.is_func_dom_eq
            (BType.canonicalIsoSMTType tau).2.1]⟩).1,
          tau.toSMTType, ZFSet.fapply_mem_range _ _⟩
      let x_fin : Fin vs.length → B.Dom := fun i =>
        ⟨x.get vs.length i, ⟨tau.get vs.length i,
          get_mem_type_of_isTuple
            (hasArity_of_mem_toZFSet tau_hasArity hx_mem)
            tau_hasArity hx_mem⟩⟩
      ∀ body_val : SMT.Dom,
        ⟦ite_body.abstract (Function.update Delta z (some Wx))
          (hcov_ite_upd Wx)⟧ˢ = some body_val →
        (body_val.fst = ZFSet.zftrue ↔
          ∀ (Px : ZFSet.{u}) (P_ty : BType) (hP_val : Px ∈ ⟦P_ty⟧ᶻ),
            ⟦(B.Term.abstract.go P vs Xi (fun v hv hvs => Xi_fv v
              (B.fv.mem_collect (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ =
              some (⟨Px, P_ty, hP_val⟩ : B.Dom) → Px = ZFSet.zftrue) := by
  intro x hx_mem _hx_D Wx x_fin body_val hbody
  obtain ⟨Pval, hPval, hden, htruth⟩ :=
    pointwise x hx_mem _hx_D body_val hbody
  exact htruth.trans (B.denote_bool_true_iff_forall hden)

open Classical in
/-- The pointwise semantic bridge for the set-valued `collect` arm.

At a canonical image of a source-domain element, the encoded domain predicate
is true.  The tuple projections then install a represented valuation for the
source binder variables, so the predicate's representation-aware totality
theorem transfers the truth value of the substituted SMT body back to the
source predicate.  This is deliberately independent of the operational
encoder trace: the `collect` case and its alternative-valuation totality
clause can both reuse it. -/
theorem represented_collect_pointwise_body_bridge.{u}
    {vs : List B.𝒱} (vs_nemp : vs ≠ []) (vs_nodup : vs.Nodup)
    {D P : B.Term} {tau : BType}
    {Xi : B.RenamingContext.Context.{u}}
    (Xi_fv : ∀ v ∈ B.fv (B.Term.collect vs D P), (Xi v).isSome = true)
    (tau_hasArity : tau.hasArity vs.length)
    {Dval : ZFSet.{u}} {hDval : Dval ∈ ⟦BType.set tau⟧ᶻ}
    (den_D : ⟦D.abstract Xi
      (fun v hv => Xi_fv v (B.fv.mem_collect (.inl hv)))⟧ᴮ =
      some (⟨Dval, BType.set tau, hDval⟩ : B.Dom))
    {T : ZFSet.{u}} {hT : T ∈ ⟦BType.set tau⟧ᶻ}
    (den_collect : ⟦(B.Term.collect vs D P).abstract Xi Xi_fv⟧ᴮ =
      some (⟨T, BType.set tau, hT⟩ : B.Dom))
    {Denc Penc ite_body : SMT.Term} {z : SMT.𝒱}
    {ThetaD : SMT.RenamingContext.Context.{u}} {DencVal : SMT.Dom.{u}}
    (hcov_D_upd : ∀ W : SMT.Dom,
      SMT.RenamingContext.CoversFV
        (Function.update ThetaD z (some W)) Denc)
    (den_D_upd : ∀ W : SMT.Dom,
      ⟦Denc.abstract (Function.update ThetaD z (some W))
        (hcov_D_upd W)⟧ˢ = some DencVal)
    (hDenc_type : DencVal.snd.fst = tau.toSMTType.fun SMTType.bool)
    (hDenc_func : ⟦tau.toSMTType⟧ᶻ.IsFunc 𝔹 DencVal.fst)
    (D_rel : RDomCastSupported
      (⟨Dval, BType.set tau, hDval⟩ : B.Dom) DencVal)
    (ite_body_def : ite_body = ((@ˢDenc) (.var z)).ite
      (SMT.substList vs (toDestPair vs (.var z)) Penc) (.bool false))
    (hcov_ite_upd : ∀ W : SMT.Dom,
      SMT.RenamingContext.CoversFV
        (Function.update ThetaD z (some W)) ite_body)
    (hcov_sub_upd : ∀ W : SMT.Dom,
      SMT.RenamingContext.CoversFV
        (Function.update ThetaD z (some W))
          (SMT.substList vs (toDestPair vs (.var z)) Penc))
    (hcov_P_upd : ∀ (W : SMT.Dom) (ss : Fin vs.length → SMT.Dom),
      SMT.RenamingContext.CoversFV
        (Function.updates (Function.update ThetaD z (some W)) vs
          ((List.ofFn ss).map Option.some)) Penc)
    (hvs_not_bv : ∀ v ∈ vs, v ∉ SMT.bv Penc)
    (hz_not_bv : z ∉ SMT.bv Penc) (hz_not_vs : z ∉ vs)
    (Penc_fv : SMT.fv Penc ⊆ B.Term.vars P)
    (z_not_vars_P : z ∉ B.Term.vars P)
    {Ebody : B.Env} {LambdaP GammaP : SMT.TypeContext}
    {sigmaP : SMTType} {usedP : List SMT.𝒱}
    (typ_P : Ebody.context ⊢ᴮ P : BType.bool)
    (P_total : EncodeTermRepTotal.{u}
      P Ebody BType.bool LambdaP Penc sigmaP GammaP usedP)
    (ambient : ∀ v ∈ B.fv P, v ∉ vs →
      match Xi v, ThetaD v with
      | some d, some d' => RDomCastSupported d d'
      | _, _ => False)
    (wf_bound : ∀ (x : ZFSet.{u}) (hx : x ∈ ⟦tau⟧ᶻ)
      (_hx_D : x ∈ Dval),
      B.RenWF Ebody.context
        (Function.updates Xi vs (List.ofFn fun i => some
          (⟨x.get vs.length i, tau.get vs.length i,
            get_mem_type_of_isTuple
              (hasArity_of_mem_toZFSet tau_hasArity hx)
              tau_hasArity hx⟩ : B.Dom))))
    (bound_none : ∀ (W : SMT.Dom) (ss : Fin vs.length → SMT.Dom),
      ∀ v ∉ usedP,
        Function.updates (Function.update ThetaD z (some W)) vs
          ((List.ofFn ss).map Option.some) v = none)
    (bound_respects : ∀ (W : SMT.Dom) (ss : Fin vs.length → SMT.Dom),
      B.RenamingContext.RespectsTypeContextOnFV
        (Function.updates (Function.update ThetaD z (some W)) vs
          ((List.ofFn ss).map Option.some)) LambdaP P)
    (bound_dom : ∀ (W : SMT.Dom) (ss : Fin vs.length → SMT.Dom),
      ∀ v,
        Function.updates (Function.update ThetaD z (some W)) vs
          ((List.ofFn ss).map Option.some) v ≠ none → v ∈ LambdaP) :
    ∀ (x : ZFSet.{u}) (hx_mem : x ∈ ⟦tau⟧ᶻ) (_hx_D : x ∈ Dval),
      let Wx : SMT.Dom :=
        ⟨(ZFSet.fapply (BType.canonicalIsoSMTType tau).1
          (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType tau).2.1)
          ⟨x, by rwa [ZFSet.is_func_dom_eq
            (BType.canonicalIsoSMTType tau).2.1]⟩).1,
          tau.toSMTType, ZFSet.fapply_mem_range _ _⟩
      let x_fin : Fin vs.length → B.Dom := fun i =>
        ⟨x.get vs.length i, tau.get vs.length i,
          get_mem_type_of_isTuple
            (hasArity_of_mem_toZFSet tau_hasArity hx_mem)
            tau_hasArity hx_mem⟩
      ∀ body_val : SMT.Dom,
        ⟦ite_body.abstract (Function.update ThetaD z (some Wx))
          (hcov_ite_upd Wx)⟧ˢ = some body_val →
        ∃ (Pval : ZFSet.{u}) (hPval : Pval ∈ ⟦BType.bool⟧ᶻ),
          ⟦(B.Term.abstract.go P vs Xi (fun v hv hvs => Xi_fv v
            (B.fv.mem_collect (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ =
            some (⟨Pval, BType.bool, hPval⟩ : B.Dom) ∧
          (body_val.fst = ZFSet.zftrue ↔ Pval = ZFSet.zftrue) := by
  intro x hx_mem hx_D
  dsimp only
  let Wx : SMT.Dom :=
    ⟨(ZFSet.fapply (BType.canonicalIsoSMTType tau).1
      (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType tau).2.1)
      ⟨x, by rwa [ZFSet.is_func_dom_eq
        (BType.canonicalIsoSMTType tau).2.1]⟩).1,
      tau.toSMTType, ZFSet.fapply_mem_range _ _⟩
  let x_fin : Fin vs.length → B.Dom := fun i =>
    ⟨x.get vs.length i, tau.get vs.length i,
      get_mem_type_of_isTuple
        (hasArity_of_mem_toZFSet tau_hasArity hx_mem)
        tau_hasArity hx_mem⟩
  change ∀ body_val : SMT.Dom,
    ⟦ite_body.abstract (Function.update ThetaD z (some Wx))
      (hcov_ite_upd Wx)⟧ˢ = some body_val →
    ∃ (Pval : ZFSet.{u}) (hPval : Pval ∈ ⟦BType.bool⟧ᶻ),
      ⟦(B.Term.abstract.go P vs Xi (fun v hv hvs => Xi_fv v
        (B.fv.mem_collect (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ =
        some (⟨Pval, BType.bool, hPval⟩ : B.Dom) ∧
      (body_val.fst = ZFSet.zftrue ↔ Pval = ZFSet.zftrue)
  intro body_val hden_body
  have hWx_type : Wx.snd.fst = tau.toSMTType := rfl
  have hWx_mem : Wx.fst ∈ ⟦tau.toSMTType⟧ᶻ := Wx.snd.snd
  have hWx_retract : retract tau Wx.fst = x := by
    dsimp [Wx]
    exact retract_of_canonical tau hx_mem
  have hcov_z : SMT.RenamingContext.CoversFV
      (Function.update ThetaD z (some Wx)) (.var z) := by
    intro v hv
    simp only [SMT.fv, List.mem_singleton] at hv
    subst v
    simp
  have hden_z : ⟦(SMT.Term.var z).abstract
      (Function.update ThetaD z (some Wx)) hcov_z⟧ˢ = some Wx := by
    simp only [SMT.Term.abstract, Function.update_self, Option.get_some,
      SMT.denote, Option.pure_def]
  obtain ⟨hcov_Dapp, Dapp, hden_Dapp, hDapp_type, hDapp_true⟩ :=
    represented_set_app_true_of_mem_canonical hcov_D_upd den_D_upd
      hDenc_type hDenc_func D_rel hx_D
  have ambient_W : ∀ v ∈ B.fv P, v ∉ vs →
      match Xi v, (Function.update ThetaD z (some Wx)) v with
      | some d, some d' => RDomCastSupported d d'
      | _, _ => False := by
    intro v hv hvs
    have hvz : v ≠ z := by
      intro h
      subst v
      exact z_not_vars_P (B.Term.mem_vars_iff.mpr (.inl hv))
    rw [Function.update_of_ne hvz]
    exact ambient v hv hvs
  obtain ⟨ss, hcomponents, related_P⟩ :=
    represented_toDestPair_bound_context vs_nemp vs_nodup tau_hasArity
      hx_mem hcov_z hden_z hWx_type hWx_mem hWx_retract ambient_W
  have hss_map : (List.ofFn ss).map Option.some =
      List.ofFn (fun i => some (ss i)) := by
    rw [List.map_ofFn]
    rfl
  have related_P' : RValuationCastSupportedOnFV
      (Function.updates Xi vs (List.ofFn fun i => some (x_fin i)))
      (Function.updates (Function.update ThetaD z (some Wx)) vs
        ((List.ofFn ss).map Option.some)) P := by
    rw [hss_map]
    exact related_P
  have hx_fin_typ : ∀ i, (x_fin i).snd.fst = tau.get vs.length i ∧
      (x_fin i).fst ∈ ⟦tau.get vs.length i⟧ᶻ :=
    fun i => ⟨rfl, (x_fin i).snd.snd⟩
  have hx_fin_eq : ZFSet.ofFinDom x_fin = x := by
    simpa [x_fin] using
      (ZFSet.ofFinDom_get (List.length_pos_iff.mpr vs_nemp)
        (fun i => get_mem_type_of_isTuple
          (hasArity_of_mem_toZFSet tau_hasArity hx_mem)
          tau_hasArity hx_mem)
        (hasArity_of_mem_toZFSet tau_hasArity hx_mem) tau_hasArity)
  have hx_fin_D : ZFSet.ofFinDom x_fin ∈ Dval := by
    rw [hx_fin_eq]
    exact hx_D
  obtain ⟨XiP_fv', Pval, hPval, den_P⟩ :=
    B.denote_collect_predicate_exists Xi_fv vs_nemp vs_nodup tau_hasArity
      den_D den_collect typ_P hx_fin_typ hx_fin_D
      (wf_bound x hx_mem hx_D)
  have hbound_values : ∀ (i : ℕ) (hi_x : i < vs.length)
      (hi_d : i < (List.ofFn ss).length),
      Function.updates (Function.update ThetaD z (some Wx)) vs
        ((List.ofFn ss).map Option.some) vs[i] = some (ss ⟨i, hi_x⟩) := by
    intro i hi_x _hi_d
    rw [hss_map]
    rw [Function.updates_eq_if (by simp) vs_nodup,
      dif_pos (List.getElem_mem hi_x)]
    simp [List.Nodup.idxOf_getElem vs_nodup]
  have hctx_source : ∀ v ∈ B.Term.vars P, v ∉ vs →
      (Function.update ThetaD z (some Wx)) v =
        Function.updates (Function.update ThetaD z (some Wx)) vs
          ((List.ofFn ss).map Option.some) v := by
    intro v hv hvs
    have hvz : v ≠ z := by
      intro h
      subst v
      exact z_not_vars_P hv
    rw [hss_map]
    rw [Function.updates_of_not_mem _ vs _ v hvs]
  have htruth := collect_ite_truth_of_total_body_toDestPair
    (Pterm := P) (E := Ebody) (Lambda := LambdaP) (Gamma := GammaP)
    (sigma := sigmaP) (used := usedP)
    vs_nemp vs_nodup (z := z) (ss := ss)
    (hbody_def := ite_body_def)
    (hcov_body := hcov_ite_upd Wx)
    (hcov_Dapp := hcov_Dapp)
    (hcov_sub := hcov_sub_upd Wx)
    (hcov_upd := hcov_P_upd Wx ss)
    (hvs_not_bv := hvs_not_bv) (hz_not_bv := hz_not_bv)
    (hz_not_vs := hz_not_vs)
    (hcomponents := by
      intro i
      obtain ⟨hcov, hden, _⟩ := hcomponents i
      exact ⟨hcov, hden⟩)
    (P_total := P_total) (Xi_fv := XiP_fv')
    (related := related_P') (wf := wf_bound x hx_mem hx_D)
    (ThetaBase_none := bound_none Wx ss)
    (source_respects := bound_respects Wx ss)
    (ThetaBase_dom := bound_dom Wx ss)
    (den_P := den_P) (bound_values := hbound_values)
    (hPenc_fv := Penc_fv) (hctx_source := hctx_source)
    (hden_D := hden_Dapp) (hden_body := hden_body)
    (hD_type := hDapp_type) (hD_true := hDapp_true)
  have den_P_go :
      ⟦(B.Term.abstract.go P vs Xi (fun v hv hvs => Xi_fv v
        (B.fv.mem_collect (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ =
        some (⟨Pval, BType.bool, hPval⟩ : B.Dom) := by
    rw [denote_term_abstract_go_eq_term_abstract vs_nodup vs_nemp x_fin
      XiP_fv']
    exact den_P
  exact ⟨Pval, hPval, den_P_go, htruth⟩

open Classical in
/-- Assemble the representation-aware collection body bridge into the
retraction equation for the set-valued lambda emitted by the encoder.

The operational `collect` proof has to establish coverage, typing, and
totality for a concrete encoder trace.  Once it has done so, this lemma is
the whole semantic core: source collection denotation supplies the separation
equation and predicate totality, while
`represented_collect_pointwise_body_bridge` supplies the only genuinely
representation-sensitive step.  Keeping the composition here lets both the
main run and the alternative-valuation totality proof share exactly the same
argument. -/
theorem represented_collect_set_retract.{u}
    {vs : List B.𝒱} (vs_nemp : vs ≠ []) (vs_nodup : vs.Nodup)
    {D P : B.Term} {tau : BType}
    {Xi : B.RenamingContext.Context.{u}}
    (Xi_fv : ∀ v ∈ B.fv (B.Term.collect vs D P), (Xi v).isSome = true)
    (tau_hasArity : tau.hasArity vs.length)
    {Dval : ZFSet.{u}} {hDval : Dval ∈ ⟦BType.set tau⟧ᶻ}
    (den_D : ⟦D.abstract Xi
      (fun v hv => Xi_fv v (B.fv.mem_collect (.inl hv)))⟧ᴮ =
      some (⟨Dval, BType.set tau, hDval⟩ : B.Dom))
    {T : ZFSet.{u}} {hT : T ∈ ⟦BType.set tau⟧ᶻ}
    (den_collect : ⟦(B.Term.collect vs D P).abstract Xi Xi_fv⟧ᴮ =
      some (⟨T, BType.set tau, hT⟩ : B.Dom))
    {Denc Penc ite_body : SMT.Term} {z : SMT.𝒱}
    {ThetaD : SMT.RenamingContext.Context.{u}} {DencVal : SMT.Dom.{u}}
    (ite_body_def : ite_body = ((@ˢDenc) (.var z)).ite
      (SMT.substList vs (toDestPair vs (.var z)) Penc) (.bool false))
    (z_not_fv_D : z ∉ SMT.fv Denc)
    (hcov_lambda : SMT.RenamingContext.CoversFV ThetaD
      ((λˢ [z]) [tau.toSMTType] ite_body))
    {lamVal : SMT.Dom.{u}}
    (hlamVal : ⟦((λˢ [z]) [tau.toSMTType] ite_body).abstract ThetaD
      hcov_lambda⟧ˢ = some lamVal)
    (hlamVal_func : ⟦tau.toSMTType⟧ᶻ.IsFunc 𝔹 lamVal.fst)
    (hcov_D_upd : ∀ W : SMT.Dom,
      SMT.RenamingContext.CoversFV
        (Function.update ThetaD z (some W)) Denc)
    (den_D_upd : ∀ W : SMT.Dom,
      ⟦Denc.abstract (Function.update ThetaD z (some W))
        (hcov_D_upd W)⟧ˢ = some DencVal)
    (hDenc_type : DencVal.snd.fst = tau.toSMTType.fun SMTType.bool)
    (hDenc_func : ⟦tau.toSMTType⟧ᶻ.IsFunc 𝔹 DencVal.fst)
    (D_rel : RDomCastSupported
      (⟨Dval, BType.set tau, hDval⟩ : B.Dom) DencVal)
    (hcov_ite_upd : ∀ W : SMT.Dom,
      SMT.RenamingContext.CoversFV
        (Function.update ThetaD z (some W)) ite_body)
    {GammaBody : SMT.TypeContext}
    (typ_ite : GammaBody.insert z tau.toSMTType ⊢ˢ ite_body : SMTType.bool)
    (Theta_wt : ∀ v ∈ SMT.fv ite_body, ∀ d : SMT.Dom,
      ThetaD v = some d → ∀ sigma, GammaBody.lookup v = some sigma →
        d.snd.fst = sigma)
    (hcov_sub_upd : ∀ W : SMT.Dom,
      SMT.RenamingContext.CoversFV
        (Function.update ThetaD z (some W))
          (SMT.substList vs (toDestPair vs (.var z)) Penc))
    (fv_substList_disj_vs : ∀ v ∈
      SMT.fv (SMT.substList vs (toDestPair vs (.var z)) Penc),
      v ≠ z → v ∉ vs)
    (hgo_cov : ∀ x ∈ SMT.fv ite_body, x ∉ [z] → (ThetaD x).isSome = true)
    (hcov_P_upd : ∀ (W : SMT.Dom) (ss : Fin vs.length → SMT.Dom),
      SMT.RenamingContext.CoversFV
        (Function.updates (Function.update ThetaD z (some W)) vs
          ((List.ofFn ss).map Option.some)) Penc)
    (hvs_not_bv : ∀ v ∈ vs, v ∉ SMT.bv Penc)
    (hz_not_bv : z ∉ SMT.bv Penc) (hz_not_vs : z ∉ vs)
    (Penc_fv : SMT.fv Penc ⊆ B.Term.vars P)
    (z_not_vars_P : z ∉ B.Term.vars P)
    {Ebody : B.Env} {LambdaP GammaP : SMT.TypeContext}
    {sigmaP : SMTType} {usedP : List SMT.𝒱}
    (typ_P : Ebody.context ⊢ᴮ P : BType.bool)
    (P_total : EncodeTermRepTotal.{u}
      P Ebody BType.bool LambdaP Penc sigmaP GammaP usedP)
    (ambient : ∀ v ∈ B.fv P, v ∉ vs →
      match Xi v, ThetaD v with
      | some d, some d' => RDomCastSupported d d'
      | _, _ => False)
    (wf_bound : ∀ (x : ZFSet.{u}) (hx : x ∈ ⟦tau⟧ᶻ)
      (_hx_D : x ∈ Dval),
      B.RenWF Ebody.context
        (Function.updates Xi vs (List.ofFn fun i => some
          (⟨x.get vs.length i, tau.get vs.length i,
            get_mem_type_of_isTuple
              (hasArity_of_mem_toZFSet tau_hasArity hx)
              tau_hasArity hx⟩ : B.Dom))))
    (bound_none : ∀ (W : SMT.Dom) (ss : Fin vs.length → SMT.Dom),
      ∀ v ∉ usedP,
        Function.updates (Function.update ThetaD z (some W)) vs
          ((List.ofFn ss).map Option.some) v = none)
    (bound_respects : ∀ (W : SMT.Dom) (ss : Fin vs.length → SMT.Dom),
      B.RenamingContext.RespectsTypeContextOnFV
        (Function.updates (Function.update ThetaD z (some W)) vs
          ((List.ofFn ss).map Option.some)) LambdaP P)
    (bound_dom : ∀ (W : SMT.Dom) (ss : Fin vs.length → SMT.Dom),
      ∀ v,
        Function.updates (Function.update ThetaD z (some W)) vs
          ((List.ofFn ss).map Option.some) v ≠ none → v ∈ LambdaP) :
    retract (BType.set tau) lamVal.fst = T := by
  have hDenc_retract : retract (BType.set tau) DencVal.fst = Dval := by
    have hcanonical :
        (⟨Dval, BType.set tau, hDval⟩ : B.Dom) ≘ᶻ DencVal :=
      (RDomCast.iff_RDom_of_type_eq (α := BType.set tau)
        (by simpa using hDenc_type)).mp D_rel.toRDomCast
    rw [RDom] at hcanonical
    exact hcanonical.2
  obtain ⟨hbody_total, hbody_ty⟩ :=
    SMT.RenamingContext.denote_update_total_and_type_of_typing
      typ_ite Theta_wt hcov_ite_upd
  refine retract_lamVal_eq_collect
    (D := D) (D_enc := Denc) (P_enc := Penc) (z := z)
    (ite_body := ite_body) (Δ_ctx := ThetaD) (lamVal := lamVal)
    (denD_val := DencVal) (𝒟_val := Dval) (P := P) (T_val := T)
    vs_nemp vs_nodup tau_hasArity ite_body_def z_not_fv_D
    hcov_lambda hlamVal hlamVal_func hcov_D_upd den_D_upd
    hDenc_type hDenc_func hDval hDenc_retract hcov_ite_upd
    hbody_total hbody_ty hcov_sub_upd fv_substList_disj_vs hgo_cov
    Xi_fv ?_ ?_ ?_
  · exact B.denote_collect_eq_sep Xi_fv tau_hasArity den_D den_collect
  · exact B.denote_collect_predicate_total Xi_fv tau_hasArity
      den_D den_collect
  · apply collect_hbridge_of_pointwise_bool
      (D := D) (P := P) (tau := tau) (Dval := Dval)
      Xi_fv tau_hasArity hcov_ite_upd
    exact represented_collect_pointwise_body_bridge
      (D := D) (P := P) (tau := tau) (Denc := Denc) (Penc := Penc)
      (ite_body := ite_body) (z := z) (ThetaD := ThetaD)
      (DencVal := DencVal) (Ebody := Ebody) (LambdaP := LambdaP)
      (GammaP := GammaP) (sigmaP := sigmaP) (usedP := usedP)
      vs_nemp vs_nodup Xi_fv tau_hasArity den_D den_collect
      hcov_D_upd den_D_upd hDenc_type hDenc_func D_rel ite_body_def
      hcov_ite_upd hcov_sub_upd hcov_P_upd hvs_not_bv hz_not_bv hz_not_vs
      Penc_fv z_not_vars_P typ_P P_total ambient wf_bound bound_none
      bound_respects bound_dom

open Classical in
/-- Turn the collection retraction equation into the representation-aware
denotation result required by an encoder run.

The only additional work beyond `represented_collect_set_retract` is ordinary
SMT totality for the emitted lambda.  Its typing gives both the denotation and
the functionhood needed by retraction, so a caller only has to provide the
trace-specific typing and free-variable compatibility facts once. -/
theorem represented_collect_set_denote.{u}
    {vs : List B.𝒱} (vs_nemp : vs ≠ []) (vs_nodup : vs.Nodup)
    {D P : B.Term} {tau : BType}
    {Xi : B.RenamingContext.Context.{u}}
    (Xi_fv : ∀ v ∈ B.fv (B.Term.collect vs D P), (Xi v).isSome = true)
    (tau_hasArity : tau.hasArity vs.length)
    {Dval : ZFSet.{u}} {hDval : Dval ∈ ⟦BType.set tau⟧ᶻ}
    (den_D : ⟦D.abstract Xi
      (fun v hv => Xi_fv v (B.fv.mem_collect (.inl hv)))⟧ᴮ =
      some (⟨Dval, BType.set tau, hDval⟩ : B.Dom))
    {T : ZFSet.{u}} {hT : T ∈ ⟦BType.set tau⟧ᶻ}
    (den_collect : ⟦(B.Term.collect vs D P).abstract Xi Xi_fv⟧ᴮ =
      some (⟨T, BType.set tau, hT⟩ : B.Dom))
    {Denc Penc ite_body : SMT.Term} {z : SMT.𝒱}
    {ThetaD : SMT.RenamingContext.Context.{u}} {DencVal : SMT.Dom.{u}}
    (ite_body_def : ite_body = ((@ˢDenc) (.var z)).ite
      (SMT.substList vs (toDestPair vs (.var z)) Penc) (.bool false))
    (z_not_fv_D : z ∉ SMT.fv Denc)
    (hcov_lambda : SMT.RenamingContext.CoversFV ThetaD
      ((λˢ [z]) [tau.toSMTType] ite_body))
    {GammaOut : SMT.TypeContext}
    (typ_lambda : GammaOut ⊢ˢ ((λˢ [z]) [tau.toSMTType] ite_body) :
      tau.toSMTType.fun SMTType.bool)
    (respects_lambda : SMT.RenamingContext.RespectsTypeContextOnFV
      ThetaD GammaOut ((λˢ [z]) [tau.toSMTType] ite_body))
    (hcov_D_upd : ∀ W : SMT.Dom,
      SMT.RenamingContext.CoversFV
        (Function.update ThetaD z (some W)) Denc)
    (den_D_upd : ∀ W : SMT.Dom,
      ⟦Denc.abstract (Function.update ThetaD z (some W))
        (hcov_D_upd W)⟧ˢ = some DencVal)
    (hDenc_type : DencVal.snd.fst = tau.toSMTType.fun SMTType.bool)
    (hDenc_func : ⟦tau.toSMTType⟧ᶻ.IsFunc 𝔹 DencVal.fst)
    (D_rel : RDomCastSupported
      (⟨Dval, BType.set tau, hDval⟩ : B.Dom) DencVal)
    (hcov_ite_upd : ∀ W : SMT.Dom,
      SMT.RenamingContext.CoversFV
        (Function.update ThetaD z (some W)) ite_body)
    {GammaBody : SMT.TypeContext}
    (typ_ite : GammaBody.insert z tau.toSMTType ⊢ˢ ite_body : SMTType.bool)
    (Theta_wt : ∀ v ∈ SMT.fv ite_body, ∀ d : SMT.Dom,
      ThetaD v = some d → ∀ sigma, GammaBody.lookup v = some sigma →
        d.snd.fst = sigma)
    (hcov_sub_upd : ∀ W : SMT.Dom,
      SMT.RenamingContext.CoversFV
        (Function.update ThetaD z (some W))
          (SMT.substList vs (toDestPair vs (.var z)) Penc))
    (fv_substList_disj_vs : ∀ v ∈
      SMT.fv (SMT.substList vs (toDestPair vs (.var z)) Penc),
      v ≠ z → v ∉ vs)
    (hgo_cov : ∀ x ∈ SMT.fv ite_body, x ∉ [z] → (ThetaD x).isSome = true)
    (hcov_P_upd : ∀ (W : SMT.Dom) (ss : Fin vs.length → SMT.Dom),
      SMT.RenamingContext.CoversFV
        (Function.updates (Function.update ThetaD z (some W)) vs
          ((List.ofFn ss).map Option.some)) Penc)
    (hvs_not_bv : ∀ v ∈ vs, v ∉ SMT.bv Penc)
    (hz_not_bv : z ∉ SMT.bv Penc) (hz_not_vs : z ∉ vs)
    (Penc_fv : SMT.fv Penc ⊆ B.Term.vars P)
    (z_not_vars_P : z ∉ B.Term.vars P)
    {Ebody : B.Env} {LambdaP GammaP : SMT.TypeContext}
    {sigmaP : SMTType} {usedP : List SMT.𝒱}
    (typ_P : Ebody.context ⊢ᴮ P : BType.bool)
    (P_total : EncodeTermRepTotal.{u}
      P Ebody BType.bool LambdaP Penc sigmaP GammaP usedP)
    (ambient : ∀ v ∈ B.fv P, v ∉ vs →
      match Xi v, ThetaD v with
      | some d, some d' => RDomCastSupported d d'
      | _, _ => False)
    (wf_bound : ∀ (x : ZFSet.{u}) (hx : x ∈ ⟦tau⟧ᶻ)
      (_hx_D : x ∈ Dval),
      B.RenWF Ebody.context
        (Function.updates Xi vs (List.ofFn fun i => some
          (⟨x.get vs.length i, tau.get vs.length i,
            get_mem_type_of_isTuple
              (hasArity_of_mem_toZFSet tau_hasArity hx)
              tau_hasArity hx⟩ : B.Dom))))
    (bound_none : ∀ (W : SMT.Dom) (ss : Fin vs.length → SMT.Dom),
      ∀ v ∉ usedP,
        Function.updates (Function.update ThetaD z (some W)) vs
          ((List.ofFn ss).map Option.some) v = none)
    (bound_respects : ∀ (W : SMT.Dom) (ss : Fin vs.length → SMT.Dom),
      B.RenamingContext.RespectsTypeContextOnFV
        (Function.updates (Function.update ThetaD z (some W)) vs
          ((List.ofFn ss).map Option.some)) LambdaP P)
    (bound_dom : ∀ (W : SMT.Dom) (ss : Fin vs.length → SMT.Dom),
      ∀ v,
        Function.updates (Function.update ThetaD z (some W)) vs
          ((List.ofFn ss).map Option.some) v ≠ none → v ∈ LambdaP) :
    ∃ lamVal : SMT.Dom.{u},
      ⟦((λˢ [z]) [tau.toSMTType] ite_body).abstract ThetaD
        hcov_lambda⟧ˢ = some lamVal ∧
      RDomCastSupported (⟨T, BType.set tau, hT⟩ : B.Dom) lamVal := by
  obtain ⟨lamVal, hlamVal, hlamVal_type⟩ :=
    SMT.RenamingContext.denote_exists_of_typing_fv typ_lambda
      respects_lambda hcov_lambda
  have hlamVal_func : ⟦tau.toSMTType⟧ᶻ.IsFunc 𝔹 lamVal.fst := by
    have hmem : lamVal.fst ∈ ⟦tau.toSMTType⟧ᶻ.funs 𝔹 := by
      simpa [hlamVal_type, SMTType.toZFSet] using lamVal.snd.snd
    exact ZFSet.mem_funs.mp hmem
  refine ⟨lamVal, hlamVal, ?_⟩
  apply RDomCastSupported.of_canonical_set_retract
  · simpa using hlamVal_type
  · exact represented_collect_set_retract
      (D := D) (P := P) (tau := tau) (Denc := Denc) (Penc := Penc)
      (ite_body := ite_body) (z := z) (ThetaD := ThetaD)
      (DencVal := DencVal) (lamVal := lamVal) (GammaBody := GammaBody)
      (Ebody := Ebody) (LambdaP := LambdaP) (GammaP := GammaP)
      (sigmaP := sigmaP) (usedP := usedP)
      vs_nemp vs_nodup Xi_fv tau_hasArity den_D den_collect ite_body_def
      z_not_fv_D hcov_lambda hlamVal hlamVal_func hcov_D_upd den_D_upd
      hDenc_type hDenc_func D_rel hcov_ite_upd typ_ite Theta_wt
      hcov_sub_upd fv_substList_disj_vs hgo_cov hcov_P_upd hvs_not_bv
      hz_not_bv hz_not_vs Penc_fv z_not_vars_P typ_P P_total ambient
      wf_bound bound_none bound_respects bound_dom
