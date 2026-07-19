import SMT.Reasoning.Basic.EncodeTermRepresentedCollect
import SMT.Reasoning.Basic.EncodeTermRepresentedEq

open Std.Do B SMT ZFSet

/-!
# Representation-aware lambda encoding

The source lambda denotes the graph of its body over the source domain.  The
encoder emits that graph as one Boolean characteristic predicate whose bound
argument pairs a representation of the source tuple with a representation of
the body result.  Neither component is required to use its canonical SMT
type.
-/

open Classical in
/-- Every supported target shape represents the source type's canonical
default value by its own canonical default.  The relation case is the only
non-homomorphic branch: the default option-valued function is constantly
`none`, so its graph is the empty source relation. -/
theorem RDomCastSupported.default_of_supported.{u}
    {alpha : BType} {sigma : SMTType}
    (hsigma : BType.SupportedSMT alpha sigma) :
    RDomCastSupported
      (⟨alpha.defaultZFSet, alpha,
        BType.mem_toZFSet_of_defaultZFSet⟩ : B.Dom.{u})
      (⟨sigma.defaultZFSet, sigma,
        SMTType.mem_toZFSet_of_defaultZFSet⟩ : SMT.Dom.{u}) := by
  induction hsigma with
  | int =>
      exact RDom.toRDomCastSupported (by
        rw [RDom]
        simp [retract, BType.toSMTType, BType.defaultZFSet,
          SMTType.defaultZFSet])
  | bool =>
      exact RDom.toRDomCastSupported (by
        rw [RDom]
        simp [retract, BType.toSMTType, BType.defaultZFSet,
          SMTType.defaultZFSet])
  | prod hleft hright ihleft ihrigh =>
      simpa [BType.defaultZFSet, SMTType.defaultZFSet] using
        RDomCastSupported.pair ihleft ihrigh
  | @setPred alpha sigma hsigma ih =>
      let F : ZFSet.{u} :=
        SMTType.defaultZFSet (SMTType.fun sigma SMTType.bool)
      have hF : F ∈ ⟦SMTType.fun sigma SMTType.bool⟧ᶻ :=
        SMTType.mem_toZFSet_of_defaultZFSet
      have hFfunc : ⟦sigma⟧ᶻ.IsFunc ZFSet.𝔹 F := by
        simpa [SMTType.toZFSet] using hF
      refine RDomCastSupported.setPred_of_pointwise hsigma
        (S := (BType.set alpha).defaultZFSet) (F := F)
        ?_ hF hFfunc ?_ ?_
      · exact ZFSet.sep_subset_self
      · intro y hy htrue
        have hfalse :
            (ZFSet.fapply F (ZFSet.is_func_is_pfunc hFfunc)
              ⟨y, by rw [ZFSet.is_func_dom_eq hFfunc]; exact hy⟩).val =
              ZFSet.zffalse := by
          simpa only [F, SMTType.defaultZFSet, proof_irrel_heq] using
            (defaultZFSetFunApp
              (α := sigma) (β := SMTType.bool) hy)
        exact (ZFSet.zftrue_ne_zffalse
          (htrue.symm.trans hfalse)).elim
      · intro x hx
        simp [BType.defaultZFSet] at hx
  | optionFun alpha beta =>
      let F : ZFSet.{u} := SMTType.defaultZFSet
        (SMTType.fun alpha.toSMTType
          (SMTType.option beta.toSMTType))
      have hF : F ∈ ⟦SMTType.fun alpha.toSMTType
          (SMTType.option beta.toSMTType)⟧ᶻ :=
        SMTType.mem_toZFSet_of_defaultZFSet
      let G := optionGraph alpha.toSMTType beta.toSMTType F
      have hG : G ∈ ⟦SMTType.fun
          (SMTType.pair alpha.toSMTType beta.toSMTType)
          SMTType.bool⟧ᶻ :=
        optionGraph_mem alpha.toSMTType beta.toSMTType hF
      have hGfunc :
          ⟦SMTType.pair alpha.toSMTType beta.toSMTType⟧ᶻ.IsFunc
            ZFSet.𝔹 G := by
        simpa [SMTType.toZFSet] using hG
      have hgraphRel : RDomCastSupported
          (⟨(BType.set (alpha ×ᴮ beta)).defaultZFSet,
            BType.set (alpha ×ᴮ beta),
            BType.mem_toZFSet_of_defaultZFSet⟩ : B.Dom.{u})
          (⟨G, SMTType.fun
            (SMTType.pair alpha.toSMTType beta.toSMTType)
            SMTType.bool, hG⟩ : SMT.Dom.{u}) := by
        refine RDomCastSupported.setPred_of_pointwise
          (BType.SupportedSMT.canonical (alpha ×ᴮ beta))
          (S := (BType.set (alpha ×ᴮ beta)).defaultZFSet)
          (F := G) ?_ hG hGfunc ?_ ?_
        · exact ZFSet.sep_subset_self
        · intro xy hxy htrue
          obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.mp hxy
          have hsome :=
            (optionGraph_apply_eq_zftrue_iff
              alpha.toSMTType beta.toSMTType hF hx hy).mp
              (by simpa only [G, proof_irrel_heq] using htrue)
          have hFfunc : ⟦alpha.toSMTType⟧ᶻ.IsFunc
              ⟦SMTType.option beta.toSMTType⟧ᶻ F := by
            simpa [SMTType.toZFSet] using hF
          have hnone :
              (ZFSet.fapply F (ZFSet.is_func_is_pfunc hFfunc)
                ⟨x, by rw [ZFSet.is_func_dom_eq hFfunc]; exact hx⟩).val =
                (ZFSet.Option.none
                  (S := ⟦beta.toSMTType⟧ᶻ)).val := by
            simpa only [F, SMTType.defaultZFSet, proof_irrel_heq] using
              (defaultZFSetFunApp
                (α := alpha.toSMTType)
                (β := SMTType.option beta.toSMTType) hx)
          have hnone_some :
              ZFSet.Option.none (S := ⟦beta.toSMTType⟧ᶻ) =
                ZFSet.Option.some (S := ⟦beta.toSMTType⟧ᶻ) ⟨y, hy⟩ :=
            Subtype.ext (hnone.symm.trans hsome)
          exact False.elim
            (ZFSet.Option.some_ne_none _ hnone_some.symm)
        · intro xy hxy
          simp [BType.defaultZFSet] at hxy
      have hbare : RDomCast
          (⟨(BType.set (alpha ×ᴮ beta)).defaultZFSet,
            BType.set (alpha ×ᴮ beta),
            BType.mem_toZFSet_of_defaultZFSet⟩ : B.Dom.{u})
          (⟨F, SMTType.fun alpha.toSMTType
            (SMTType.option beta.toSMTType), hF⟩ : SMT.Dom.{u}) := by
        refine ⟨castPath.graph
          (castPath.reflexive alpha.toSMTType)
          (castPath.reflexive beta.toSMTType), ?_⟩
        change retract (BType.set (alpha ×ᴮ beta)) G =
          (BType.set (alpha ×ᴮ beta)).defaultZFSet
        obtain ⟨c, hret⟩ := hgraphRel.toRDomCast
        rw [castPath.eq_reflexive c,
          castZF_apply_reflexive _ hG] at hret
        exact hret
      exact ⟨RDomCast.toRDomCastAdmissible_of_supported hbare
          (.optionFun alpha beta),
        .optionFun alpha beta⟩

open Classical in
/-- Package one emitted Boolean lambda as a represented source set once its
body has an exact pointwise source correspondence. -/
theorem represented_setPred_lambda_of_pointwise.{u}
    {alpha : BType} {sigma : SMTType}
    (hsigma : BType.SupportedSMT alpha sigma)
    {S : ZFSet.{u}} (hSsub : S ⊆ ⟦alpha⟧ᶻ)
    {Theta : SMT.RenamingContext.Context.{u}} {z : SMT.𝒱}
    {body : SMT.Term} {lamVal : SMT.Dom.{u}}
    (hcov_lambda : SMT.RenamingContext.CoversFV Theta
      ((λˢ [z]) [sigma] body))
    (hden_lambda : ⟦((λˢ [z]) [sigma] body).abstract
      Theta hcov_lambda⟧ˢ = some lamVal)
    (hlam_type : lamVal.snd.fst =
      SMTType.fun sigma SMTType.bool)
    (hbody_total : ∀ (y : ZFSet.{u}) (hy : y ∈ ⟦sigma⟧ᶻ),
      ∃ (hcov_body : SMT.RenamingContext.CoversFV
          (Function.update Theta z
            (some (⟨y, sigma, hy⟩ : SMT.Dom))) body)
        (bodyVal : SMT.Dom.{u}),
        ⟦body.abstract (Function.update Theta z
          (some (⟨y, sigma, hy⟩ : SMT.Dom))) hcov_body⟧ˢ =
            some bodyVal)
    (hforward : ∀ (y : ZFSet.{u}) (hy : y ∈ ⟦sigma⟧ᶻ)
      (hcov_body : SMT.RenamingContext.CoversFV
        (Function.update Theta z
          (some (⟨y, sigma, hy⟩ : SMT.Dom))) body)
      (bodyVal : SMT.Dom.{u}),
      ⟦body.abstract (Function.update Theta z
        (some (⟨y, sigma, hy⟩ : SMT.Dom))) hcov_body⟧ˢ =
          some bodyVal →
      bodyVal.fst = ZFSet.zftrue →
      ∃ (x : ZFSet.{u}) (hx : x ∈ S),
        RDomCastSupported
          (⟨x, alpha, hSsub hx⟩ : B.Dom)
          (⟨y, sigma, hy⟩ : SMT.Dom))
    (hbackward : ∀ (x : ZFSet.{u}) (hx : x ∈ S),
      ∃ (y : ZFSet.{u}) (hy : y ∈ ⟦sigma⟧ᶻ)
        (_hrel : RDomCastSupported
          (⟨x, alpha, hSsub hx⟩ : B.Dom)
          (⟨y, sigma, hy⟩ : SMT.Dom))
        (hcov_body : SMT.RenamingContext.CoversFV
          (Function.update Theta z
            (some (⟨y, sigma, hy⟩ : SMT.Dom))) body)
        (bodyVal : SMT.Dom.{u}),
        ⟦body.abstract (Function.update Theta z
          (some (⟨y, sigma, hy⟩ : SMT.Dom))) hcov_body⟧ˢ =
            some bodyVal ∧
        bodyVal.fst = ZFSet.zftrue) :
    RDomCastSupported
      (⟨S, BType.set alpha, ZFSet.mem_powerset.mpr hSsub⟩ : B.Dom)
      lamVal := by
  rcases lamVal with ⟨F, rho, hF⟩
  dsimp at hlam_type hden_lambda ⊢
  subst rho
  have hFfunc : ⟦sigma⟧ᶻ.IsFunc ZFSet.𝔹 F := by
    simpa [SMTType.toZFSet] using hF
  apply RDomCastSupported.setPred_of_pointwise
    hsigma hSsub hF hFfunc
  · intro y hy htrue
    obtain ⟨hcov_body, bodyVal, hden_body⟩ :=
      hbody_total y hy
    have happly := single_lambda_fapply_eq_body
      (beta := SMTType.bool) hcov_lambda hden_lambda hFfunc rfl hy
      hcov_body hden_body
    exact hforward y hy hcov_body bodyVal hden_body
      (happly.symm.trans htrue)
  · intro x hx
    obtain ⟨y, hy, hrel, hcov_body, bodyVal, hden_body,
      hbody_true⟩ := hbackward x hx
    refine ⟨y, hy, hrel, ?_⟩
    have happly := single_lambda_fapply_eq_body
      (beta := SMTType.bool) hcov_lambda hden_lambda hFfunc rfl hy
      hcov_body hden_body
    exact happly.trans hbody_true

private lemma lambda_BDom_ext {z1 z2 : ZFSet} {tau1 tau2 : BType}
    {h1 : z1 ∈ ⟦tau1⟧ᶻ} {h2 : z2 ∈ ⟦tau2⟧ᶻ}
    (hz : z1 = z2) (htau : tau1 = tau2) :
    (⟨z1, tau1, h1⟩ : B.Dom) = ⟨z2, tau2, h2⟩ := by
  subst z2
  subst tau2
  rfl

open Classical in
set_option maxHeartbeats 1000000 in
theorem toDestPair_denote_supported_components.{u} :
    ∀ (tau : BType) (sigma : SMTType)
      (hsigma : BType.SupportedSMT tau sigma)
      (vs : List SMT.𝒱) (x : ZFSet.{u})
      (hx : x ∈ ⟦tau⟧ᶻ)
      (d : SMT.Term) (W : SMT.Dom.{u})
      (Theta : SMT.RenamingContext.Context)
      (acc : List SMT.Term) (Ds_acc : List SMT.Dom.{u}),
    (vs_nemp : vs ≠ []) →
    (harity : tau.hasArity vs.length) →
    (hcov_d : SMT.RenamingContext.CoversFV Theta d) →
    ⟦d.abstract Theta hcov_d⟧ˢ = some W →
    W.snd.fst = sigma →
    W.fst ∈ ⟦sigma⟧ᶻ →
    RDomCastSupported (⟨x, tau, hx⟩ : B.Dom) W →
    acc.length = Ds_acc.length →
    (∀ (j : ℕ) (hj : j < acc.length),
      ∃ (hcov : SMT.RenamingContext.CoversFV Theta (acc[j]'(by omega))),
        ⟦(acc[j]'(by omega)).abstract Theta hcov⟧ˢ.isSome = true) →
    ∀ (j : ℕ) (hj_v : j < vs.length)
      (hj_t : j < (toDestPair vs d acc d).length),
      ∃ (hcov_j : SMT.RenamingContext.CoversFV Theta
          ((toDestPair vs d acc d)[j]'hj_t))
        (D_j : SMT.Dom.{u}),
        ⟦((toDestPair vs d acc d)[j]'hj_t).abstract Theta hcov_j⟧ˢ =
            some D_j ∧
        RDomCastSupported
          (⟨x.get vs.length ⟨j, hj_v⟩,
            tau.get vs.length ⟨j, hj_v⟩,
            get_mem_type_of_isTuple
              (hasArity_of_mem_toZFSet harity hx)
              harity hx⟩ : B.Dom)
          D_j ∧
        D_j.snd.fst =
          (sigma.fromProdl (vs.length - 1))[j]'(by
            have hlen := hsigma.fromProdl_length_of_hasArity
              harity
            omega) := by
  intro tau sigma hsigma vs
  induction vs generalizing tau sigma with
  | nil =>
      intro x hx d W Theta acc Ds_acc vs_nemp
      exact (vs_nemp rfl).elim
  | cons v vs ih =>
      intro x hx d W Theta acc Ds_acc _ harity hcov_d hden_d
        hW_type hW_mem hrel hacc_len hacc j hj_v hj_t
      cases vs with
      | nil =>
          have hj0 : j = 0 := Nat.lt_one_iff.mp hj_v
          subst j
          unfold toDestPair
          simp only [List.getElem_cons_zero]
          refine ⟨hcov_d, W, hden_d, ?_, ?_⟩
          · simpa [BType.get, ZFSet.get] using hrel
          · cases sigma <;>
              simpa [SMT.SMTType.fromProdl] using hW_type
      | cons w ws =>
          cases hsigma with
          | int => exact absurd harity (by unfold BType.hasArity; exact id)
          | bool => exact absurd harity (by unfold BType.hasArity; exact id)
          | setPred hsigma =>
              exact absurd harity (by unfold BType.hasArity; exact id)
          | optionFun alpha beta =>
              exact absurd harity (by unfold BType.hasArity; exact id)
          | @prod alpha beta sigma rho hsigma hrho =>
              have harity_left : alpha.hasArity (w :: ws).length := by
                simpa [BType.hasArity] using harity
              obtain ⟨a, ha, b, hb, rfl⟩ := ZFSet.mem_prod.mp hx
              rcases W with ⟨Y, Wtype, hY⟩
              dsimp at hW_type hW_mem hden_d hrel ⊢
              subst Wtype
              obtain ⟨A, hA, B, hB, rfl⟩ := ZFSet.mem_prod.mp hY
              obtain ⟨hleft, hright⟩ := RDomCastSupported.of_pair hrel
              have hcov_fst : SMT.RenamingContext.CoversFV Theta
                  (SMT.Term.fst d) := by
                intro q hq
                exact hcov_d q (by unfold SMT.fv at hq; exact hq)
              have hcov_snd : SMT.RenamingContext.CoversFV Theta
                  (SMT.Term.snd d) := by
                intro q hq
                exact hcov_d q (by unfold SMT.fv at hq; exact hq)
              have hden_fst :
                  ⟦(SMT.Term.fst d).abstract Theta hcov_fst⟧ˢ =
                    some (⟨A, sigma, hA⟩ : SMT.Dom) := by
                unfold SMT.Term.abstract
                simp only [SMT.denote, hden_d, ZFSet.π₁_pair]
                apply congrArg some
                exact SMT.RenamingContext.Dom_ext' (by simp) rfl
              have hden_snd :
                  ⟦(SMT.Term.snd d).abstract Theta hcov_snd⟧ˢ =
                    some (⟨B, rho, hB⟩ : SMT.Dom) := by
                unfold SMT.Term.abstract
                simp only [SMT.denote, hden_d, ZFSet.π₂_pair]
                apply congrArg some
                exact SMT.RenamingContext.Dom_ext' (by simp) rfl
              unfold toDestPair
              have hacc' : ∀ (k : ℕ)
                  (hk : k < (SMT.Term.snd d :: acc).length),
                  ∃ (hcov : SMT.RenamingContext.CoversFV Theta
                      ((SMT.Term.snd d :: acc)[k]'(by omega))),
                    ⟦((SMT.Term.snd d :: acc)[k]'(by omega)).abstract
                      Theta hcov⟧ˢ.isSome = true := by
                intro k hk
                simp only [List.length_cons] at hk
                cases k with
                | zero =>
                    simp only [List.getElem_cons_zero]
                    exact ⟨hcov_snd,
                      Option.isSome_iff_exists.mpr ⟨_, hden_snd⟩⟩
                | succ k =>
                    simp only [List.getElem_cons_succ]
                    exact hacc k (by omega)
              by_cases hj_small : j < (w :: ws).length
              · have hrec := ih alpha sigma hsigma a ha
                  (SMT.Term.fst d) (⟨A, sigma, hA⟩ : SMT.Dom)
                  Theta (SMT.Term.snd d :: acc)
                  ((⟨B, rho, hB⟩ : SMT.Dom) :: Ds_acc)
                  (List.cons_ne_nil w ws) harity_left hcov_fst hden_fst
                  rfl hA hleft (by simp [hacc_len]) hacc'
                  j hj_small hj_t
                obtain ⟨hcov_j, D_j, hden_j, hrel_j, htype_j⟩ := hrec
                refine ⟨hcov_j, D_j, hden_j, ?_, ?_⟩
                · have hj_small' : j < ws.length + 1 := by
                    simpa only [List.length_cons] using hj_small
                  have hvalue :
                      (a.pair b).get (v :: w :: ws).length ⟨j, hj_v⟩ =
                        a.get (w :: ws).length ⟨j, hj_small⟩ := by
                    simpa only [List.length_cons, proof_irrel_heq] using
                      (ZFSet_get_pair_before_last
                        (a := a) (b := b) (n := (w :: ws).length)
                        (i := j) (by simp) hj_small)
                  have hsource_type :
                      (alpha ×ᴮ beta).get (v :: w :: ws).length
                          ⟨j, hj_v⟩ =
                        alpha.get (w :: ws).length ⟨j, hj_small⟩ := by
                    simpa only [List.length_cons, proof_irrel_heq] using
                      (BType_get_pair_before_last
                        (alpha := alpha) (beta := beta)
                        (n := (w :: ws).length) (i := j)
                        (by simp) hj_small)
                  have houter_mem :
                      (a.pair b).get (v :: w :: ws).length ⟨j, hj_v⟩ ∈
                        ⟦(alpha ×ᴮ beta).get (v :: w :: ws).length
                          ⟨j, hj_v⟩⟧ᶻ :=
                    get_mem_type_of_isTuple
                      (hasArity_of_mem_toZFSet harity hx) harity hx
                  have hinner_mem :
                      a.get (w :: ws).length ⟨j, hj_small⟩ ∈
                        ⟦alpha.get (w :: ws).length ⟨j, hj_small⟩⟧ᶻ :=
                    get_mem_type_of_isTuple
                      (hasArity_of_mem_toZFSet harity_left ha)
                      harity_left ha
                  let douter : _root_.B.Dom :=
                    ⟨(a.pair b).get (v :: w :: ws).length ⟨j, hj_v⟩,
                      (alpha ×ᴮ beta).get (v :: w :: ws).length
                        ⟨j, hj_v⟩, houter_mem⟩
                  let dinner : _root_.B.Dom :=
                    ⟨a.get (w :: ws).length ⟨j, hj_small⟩,
                      alpha.get (w :: ws).length ⟨j, hj_small⟩,
                      hinner_mem⟩
                  have hdom : douter = dinner :=
                    lambda_BDom_ext hvalue hsource_type
                  change RDomCastSupported douter D_j
                  rw [hdom]
                  simpa only [dinner, proof_irrel_heq] using hrel_j
                · have hleft_len :
                      (sigma.fromProdl ws.length).length =
                        (w :: ws).length := by
                    simpa [List.length_cons] using
                      hsigma.fromProdl_length_of_hasArity harity_left
                  have houter :
                      ((SMTType.pair sigma rho).fromProdl
                        ((v :: w :: ws).length - 1))[j]'(by
                          have hsprod :=
                            BType.SupportedSMT.prod hsigma hrho
                          have hlen :=
                            hsprod.fromProdl_length_of_hasArity harity
                          omega) =
                        (sigma.fromProdl ((w :: ws).length - 1))[j]'(by
                          have hlen :=
                            hsigma.fromProdl_length_of_hasArity harity_left
                          omega) := by
                    simp only [List.length_cons, Nat.add_sub_cancel,
                      SMT.SMTType.fromProdl, List.concat_eq_append]
                    rw [List.getElem_append_left (by
                      rw [hleft_len]
                      exact hj_small)]
                  exact htype_j.trans houter.symm
              · push_neg at hj_small
                have hj_eq : j = ws.length + 1 := by
                  simp only [List.length_cons] at hj_v hj_small
                  exact Nat.eq_of_le_of_lt_succ hj_small hj_v
                subst j
                have helem :
                    (toDestPair (w :: ws) (SMT.Term.fst d)
                      (SMT.Term.snd d :: acc) (SMT.Term.fst d))[ws.length + 1]'hj_t =
                        SMT.Term.snd d := by
                  induction ws with
                  | nil =>
                      simp only [toDestPair, List.length_nil, zero_add,
                        List.getElem_cons_succ, List.getElem_cons_zero]
                  | cons u us ih_ws =>
                      simp only [toDestPair, List.length_cons]
                      have hlen : (u :: us).length + 1 <
                          (toDestPair (u :: us)
                            (SMT.Term.fst (SMT.Term.fst d))
                            (SMT.Term.snd (SMT.Term.fst d) ::
                              SMT.Term.snd d :: acc)
                            (SMT.Term.fst (SMT.Term.fst d))).length := by
                        rw [toDestPair_length_gen _ _ _ _
                          (List.cons_ne_nil u us)]
                        simp [List.length_cons]
                      have hget := toDestPair_getElem_acc (u :: us)
                        (SMT.Term.fst (SMT.Term.fst d))
                        (SMT.Term.fst (SMT.Term.fst d))
                        (SMT.Term.snd (SMT.Term.fst d) ::
                          SMT.Term.snd d :: acc) 1
                        (by simp) (List.cons_ne_nil u us) hlen
                      erw [hget]
                      rfl
                simp only [helem]
                refine ⟨hcov_snd, (⟨B, rho, hB⟩ : SMT.Dom),
                  hden_snd, ?_, ?_⟩
                · have hvalue :
                      (a.pair b).get (v :: w :: ws).length
                          ⟨ws.length + 1, hj_v⟩ = b := by
                    simpa only [List.length_cons, proof_irrel_heq] using
                      (ZFSet_get_pair_last (a := a) (b := b)
                        (n := ws.length + 1) (by omega))
                  have hsource_type :
                      (alpha ×ᴮ beta).get (v :: w :: ws).length
                          ⟨ws.length + 1, hj_v⟩ = beta := by
                    simpa only [List.length_cons, proof_irrel_heq] using
                      (BType_get_pair_last (alpha := alpha) (beta := beta)
                        (n := ws.length + 1) (by omega))
                  have houter_mem :
                      (a.pair b).get (v :: w :: ws).length
                          ⟨ws.length + 1, hj_v⟩ ∈
                        ⟦(alpha ×ᴮ beta).get (v :: w :: ws).length
                          ⟨ws.length + 1, hj_v⟩⟧ᶻ :=
                    get_mem_type_of_isTuple
                      (hasArity_of_mem_toZFSet harity hx) harity hx
                  let douter : _root_.B.Dom :=
                    ⟨(a.pair b).get (v :: w :: ws).length
                        ⟨ws.length + 1, hj_v⟩,
                      (alpha ×ᴮ beta).get (v :: w :: ws).length
                        ⟨ws.length + 1, hj_v⟩, houter_mem⟩
                  let dright : _root_.B.Dom := ⟨b, beta, hb⟩
                  have hdom : douter = dright :=
                    lambda_BDom_ext hvalue hsource_type
                  change RDomCastSupported douter
                    (⟨B, rho, hB⟩ : SMT.Dom)
                  rw [hdom]
                  simpa only [dright, proof_irrel_heq] using hright
                · have hleft_len :
                      (sigma.fromProdl ws.length).length =
                        ws.length + 1 := by
                    simpa only [List.length_cons, Nat.add_sub_cancel] using
                      hsigma.fromProdl_length_of_hasArity harity_left
                  simp only [List.length_cons, Nat.add_sub_cancel,
                    SMT.SMTType.fromProdl, List.concat_eq_append]
                  rw [List.getElem_append_right (by
                    rw [hleft_len])]
                  simp [hleft_len]

open Classical in
/-- Install the projections of an arbitrary supported tuple representative as
a representation-aware binder valuation.  The projection denotations use the
evaluation context containing the fresh lambda argument, while unrelated body
variables retain the ambient source/target relation. -/
theorem represented_lambda_toDestPair_bound_context.{u}
    {vs : List B.𝒱} (vs_nemp : vs ≠ []) (vs_nodup : vs.Nodup)
    {tau : BType} (tau_hasArity : tau.hasArity vs.length)
    {sigma : SMTType} (hsigma : BType.SupportedSMT tau sigma)
    {x : ZFSet.{u}} (hx_mem : x ∈ ⟦tau⟧ᶻ)
    {d : SMT.Term} {Delta : SMT.RenamingContext.Context.{u}}
    {Wx : SMT.Dom.{u}}
    (hcov_d : SMT.RenamingContext.CoversFV Delta d)
    (hden_d : ⟦d.abstract Delta hcov_d⟧ˢ = some Wx)
    (hWx_type : Wx.snd.fst = sigma)
    (hWx_mem : Wx.fst ∈ ⟦sigma⟧ᶻ)
    (hrel : RDomCastSupported (⟨x, tau, hx_mem⟩ : B.Dom) Wx)
    {Xi : B.RenamingContext.Context.{u}}
    {Theta : SMT.RenamingContext.Context.{u}} {P : B.Term}
    (ambient : ∀ v ∈ B.fv P, v ∉ vs →
      match Xi v, Theta v with
      | some source, some target => RDomCastSupported source target
      | _, _ => False) :
    ∃ ss : Fin vs.length → SMT.Dom.{u},
      (∀ i,
        ∃ hcov : SMT.RenamingContext.CoversFV Delta
            ((toDestPair vs d)[i.val]'(by
              rw [toDestPair_length_gen vs d d [] vs_nemp]
              exact i.isLt)),
          ⟦((toDestPair vs d)[i.val]'(by
              rw [toDestPair_length_gen vs d d [] vs_nemp]
              exact i.isLt)).abstract Delta hcov⟧ˢ = some (ss i) ∧
          RDomCastSupported
            (⟨x.get vs.length i, tau.get vs.length i,
              get_mem_type_of_isTuple
                (hasArity_of_mem_toZFSet tau_hasArity hx_mem)
                tau_hasArity hx_mem⟩ : B.Dom)
            (ss i) ∧
          (ss i).snd.fst =
            (sigma.fromProdl (vs.length - 1))[i.val]'(by
              have hlen := hsigma.fromProdl_length_of_hasArity
                tau_hasArity
              exact i.isLt.trans_eq hlen.symm)) ∧
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
          ((toDestPair vs d)[i.val]'(by
            rw [toDestPair_length_gen vs d d [] vs_nemp]
            exact i.isLt)))
        (Di : SMT.Dom.{u}),
        ⟦((toDestPair vs d)[i.val]'(by
            rw [toDestPair_length_gen vs d d [] vs_nemp]
            exact i.isLt)).abstract Delta hcov⟧ˢ = some Di ∧
        RDomCastSupported (x_fin i) Di ∧
        Di.snd.fst =
          (sigma.fromProdl (vs.length - 1))[i.val]'(by
            have hlen := hsigma.fromProdl_length_of_hasArity
              tau_hasArity
            exact i.isLt.trans_eq hlen.symm) := by
    intro i
    simpa [x_fin] using
      (toDestPair_denote_supported_components tau sigma hsigma vs x hx_mem
        d Wx Delta [] [] vs_nemp tau_hasArity hcov_d hden_d hWx_type
        hWx_mem hrel rfl (by simp) i.val i.isLt (by
          rw [toDestPair_length_gen vs d d [] vs_nemp]
          exact i.isLt))
  let ss : Fin vs.length → SMT.Dom.{u} := fun i =>
    Classical.choose (Classical.choose_spec (hcomponent i))
  refine ⟨ss, ?_, ?_⟩
  · intro i
    let hcov := Classical.choose (hcomponent i)
    obtain ⟨hden, hrel_i, htype⟩ :=
      Classical.choose_spec (Classical.choose_spec (hcomponent i))
    refine ⟨hcov, ?_, ?_, ?_⟩
    · simpa [ss] using hden
    · simpa [ss, x_fin] using hrel_i
    · simpa [ss] using htype
  · simpa [x_fin] using
      (RValuationCastSupportedOnFV.updates vs_nodup x_fin ss ambient
        (fun i => by
          obtain ⟨_hden, hrel_i, _htype⟩ :=
            Classical.choose_spec (Classical.choose_spec (hcomponent i))
          simpa [ss] using hrel_i))

/- A successful source lambda first evaluates its source domain.  This
extractor keeps the later chosen/default split out of the operational encoder
proof. -/
open Classical in
theorem B.denote_lambda_domain_exists.{u}
    {vs : List B.𝒱} {D P : B.Term} {tau beta : BType}
    {Xi : B.RenamingContext.Context.{u}}
    (Xi_fv : ∀ v ∈ B.fv (B.Term.lambda vs D P),
      (Xi v).isSome = true)
    {Ectx : B.TypeContext} (typ_D : Ectx ⊢ᴮ D : BType.set tau)
    (wf : B.RenWF Ectx Xi)
    {T : ZFSet.{u}} {hT : T ∈ ⟦BType.set (tau ×ᴮ beta)⟧ᶻ}
    (den_lambda : ⟦(B.Term.lambda vs D P).abstract Xi Xi_fv⟧ᴮ =
      some (⟨T, BType.set (tau ×ᴮ beta), hT⟩ : B.Dom)) :
    ∃ (Dval : ZFSet.{u}) (hDval : Dval ∈ ⟦BType.set tau⟧ᶻ),
      ⟦D.abstract Xi
        (fun v hv => Xi_fv v (B.fv.mem_lambda (.inl hv)))⟧ᴮ =
        some (⟨Dval, BType.set tau, hDval⟩ : B.Dom) := by
  have den_inv := den_lambda
  simp only [B.Term.abstract] at den_inv
  unfold B.denote at den_inv
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at den_inv
  obtain ⟨⟨Dval, Dty, hDval⟩, den_D_raw, _⟩ := den_inv
  have den_D0 : ⟦D.abstract Xi
      (fun v hv => Xi_fv v (B.fv.mem_lambda (.inl hv)))⟧ᴮ =
      some (⟨Dval, Dty, hDval⟩ : B.Dom) := by
    convert den_D_raw using 2
  have Dty_eq : Dty = BType.set tau := by
    exact (denote_welltyped_eq
      (t := D.abstract Xi
        (fun v hv => Xi_fv v (B.fv.mem_lambda (.inl hv))))
      ⟨_, WFTC.of_abstract, BType.set tau,
        by convert Typing.of_abstract _ typ_D⟩
      den_D0).symm
  subst Dty
  exact ⟨Dval, hDval, den_D0⟩

/- A successful source lambda supplies body totality at every tuple in its
domain, independently of whether the interpreter selected a witness from a
nonempty domain or evaluated the body at the default tuple. -/
open Classical in
theorem B.denote_lambda_body_total.{u}
    {vs : List B.𝒱} {D P : B.Term} {tau beta : BType}
    {Xi : B.RenamingContext.Context.{u}}
    (Xi_fv : ∀ v ∈ B.fv (B.Term.lambda vs D P),
      (Xi v).isSome = true)
    (tau_hasArity : tau.hasArity vs.length)
    {Dval : ZFSet.{u}} {hDval : Dval ∈ ⟦BType.set tau⟧ᶻ}
    (den_D : ⟦D.abstract Xi
      (fun v hv => Xi_fv v (B.fv.mem_lambda (.inl hv)))⟧ᴮ =
      some (⟨Dval, BType.set tau, hDval⟩ : B.Dom))
    {T : ZFSet.{u}} {hT : T ∈ ⟦BType.set (tau ×ᴮ beta)⟧ᶻ}
    (den_lambda : ⟦(B.Term.lambda vs D P).abstract Xi Xi_fv⟧ᴮ =
      some (⟨T, BType.set (tau ×ᴮ beta), hT⟩ : B.Dom)) :
    ∀ {x_fin : Fin vs.length → B.Dom.{u}},
      (∀ i, (x_fin i).snd.fst = tau.get vs.length i ∧
        (x_fin i).fst ∈ ⟦tau.get vs.length i⟧ᶻ) →
      ZFSet.ofFinDom x_fin ∈ Dval →
      ⟦(B.Term.abstract.go P vs Xi (fun v hv hvs => Xi_fv v
        (B.fv.mem_lambda (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ.isSome =
        true := by
  intro x_fin hx_typ hx_mem
  have h_inv := den_lambda
  simp only [B.Term.abstract] at h_inv
  unfold B.denote at h_inv
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h_inv
  obtain ⟨D_dom, hden_d, rest⟩ := h_inv
  have hconv_d : ⟦D.abstract Xi
      (fun v hv => Xi_fv v (B.fv.mem_lambda (.inl hv)))⟧ᴮ =
      some D_dom := by
    convert hden_d using 2
  have hD_dom_eq : D_dom =
      (⟨Dval, BType.set tau, hDval⟩ : B.Dom) := by
    rw [hconv_d] at den_D
    exact Option.some.inj den_D
  subst D_dom
  simp only at rest
  rw [dif_pos tau_hasArity] at rest
  split_ifs at rest with h_den_P h_typP_det h_nemp h_chosen_arity
    h_default_arity
  · exact h_den_P hx_typ hx_mem
  · exact h_den_P hx_typ hx_mem

/- A source tuple in the lambda domain therefore supplies one well-typed
body denotation at the valuation obtained by installing its components. -/
open Classical in
theorem B.denote_lambda_body_exists.{u}
    {vs : List B.𝒱} {D P : B.Term} {tau beta : BType}
    {Xi : B.RenamingContext.Context.{u}}
    (Xi_fv : ∀ v ∈ B.fv (B.Term.lambda vs D P),
      (Xi v).isSome = true)
    (vs_nemp : vs ≠ []) (vs_nodup : vs.Nodup)
    (tau_hasArity : tau.hasArity vs.length)
    {Dval : ZFSet.{u}} {hDval : Dval ∈ ⟦BType.set tau⟧ᶻ}
    (den_D : ⟦D.abstract Xi
      (fun v hv => Xi_fv v (B.fv.mem_lambda (.inl hv)))⟧ᴮ =
      some (⟨Dval, BType.set tau, hDval⟩ : B.Dom))
    {T : ZFSet.{u}} {hT : T ∈ ⟦BType.set (tau ×ᴮ beta)⟧ᶻ}
    (den_lambda : ⟦(B.Term.lambda vs D P).abstract Xi Xi_fv⟧ᴮ =
      some (⟨T, BType.set (tau ×ᴮ beta), hT⟩ : B.Dom))
    {Ectx : B.TypeContext} (typ_P : Ectx ⊢ᴮ P : beta)
    {x_fin : Fin vs.length → B.Dom.{u}}
    (hx_typ : ∀ i, (x_fin i).snd.fst = tau.get vs.length i ∧
      (x_fin i).fst ∈ ⟦tau.get vs.length i⟧ᶻ)
    (hx_mem : ZFSet.ofFinDom x_fin ∈ Dval)
    (wf_P : B.RenWF Ectx (Function.updates Xi vs
      (List.ofFn fun i => some (x_fin i)))) :
    ∃ (XiP_fv : ∀ v ∈ B.fv P,
        (Function.updates Xi vs
          (List.ofFn fun i => some (x_fin i)) v).isSome = true)
      (Pval : ZFSet.{u}) (hPval : Pval ∈ ⟦beta⟧ᶻ),
      ⟦P.abstract (Function.updates Xi vs
        (List.ofFn fun i => some (x_fin i))) XiP_fv⟧ᴮ =
        some (⟨Pval, beta, hPval⟩ : B.Dom) := by
  have XiP_fv : ∀ v ∈ B.fv P,
      (Function.updates Xi vs
        (List.ofFn fun i => some (x_fin i)) v).isSome = true := by
    intro v hv
    rw [Function.updates_eq_if (by simp) vs_nodup]
    split_ifs with hvs
    · simp
    · exact Xi_fv v (B.fv.mem_lambda (.inr ⟨hv, hvs⟩))
  have hgo_some := B.denote_lambda_body_total Xi_fv tau_hasArity den_D
    den_lambda hx_typ hx_mem
  obtain ⟨⟨Pval, P_ty, hPval⟩, hgo⟩ :=
    Option.isSome_iff_exists.mp hgo_some
  have hden : ⟦P.abstract (Function.updates Xi vs
      (List.ofFn fun i => some (x_fin i))) XiP_fv⟧ᴮ =
      some (⟨Pval, P_ty, hPval⟩ : B.Dom) := by
    rw [← denote_term_abstract_go_eq_term_abstract vs_nodup vs_nemp x_fin
      XiP_fv]
    exact hgo
  have hP_ty : P_ty = beta :=
    (denote_welltyped_eq
      (t := P.abstract (Function.updates Xi vs
        (List.ofFn fun i => some (x_fin i))) XiP_fv)
      ⟨_, WFTC.of_abstract, beta,
        by convert Typing.of_abstract XiP_fv typ_P wf_P⟩ hden).symm
  subst P_ty
  exact ⟨XiP_fv, Pval, hPval, hden⟩

/-- The Boolean body emitted for a source lambda is true exactly when its
domain test is true and its result component equals the substituted encoded
body.  This statement is representation-neutral: only the two equality
operands must use the same target type. -/
theorem lambda_and_eq_truth_iff.{u}
    {domainTerm resultTerm bodyTerm : SMT.PHOAS.Term SMT.Dom.{u}}
    {domainVal resultVal bodyVal : SMT.Dom.{u}}
    (hden_domain : ⟦domainTerm⟧ˢ = some domainVal)
    (hdomain_type : domainVal.snd.fst = SMTType.bool)
    (hden_result : ⟦resultTerm⟧ˢ = some resultVal)
    {candidateTerm : SMT.PHOAS.Term SMT.Dom.{u}}
    {candidateVal : SMT.Dom.{u}}
    (hden_candidate : ⟦candidateTerm⟧ˢ = some candidateVal)
    (hresult_type : resultVal.snd.fst = candidateVal.snd.fst)
    (hbody_def : bodyTerm =
      (domainTerm ∧ˢ' (resultTerm =ˢ' candidateTerm)))
    (hden_body : ⟦bodyTerm⟧ˢ = some bodyVal) :
    bodyVal.fst = ZFSet.zftrue ↔
      domainVal.fst = ZFSet.zftrue ∧
        resultVal.fst = candidateVal.fst := by
  subst bodyTerm
  obtain ⟨eqVal, hden_eq, heq_type⟩ :=
    denote_eq_some_of_some hden_result hden_candidate hresult_type
  have heq_truth : eqVal.fst = ZFSet.zftrue ↔
      resultVal.fst = candidateVal.fst :=
    denote_eq_fst_eq_zftrue_iff hden_result hden_candidate
      hresult_type hden_eq
  constructor
  · intro htrue
    obtain ⟨hdomain_true, heq_true⟩ :=
      denote_and_both_zftrue_of_zftrue_rep_eq
        hden_domain hdomain_type hden_eq heq_type hden_body htrue
    exact ⟨hdomain_true, heq_truth.mp heq_true⟩
  · rintro ⟨hdomain_true, hresult_eq⟩
    have hden_true := denote_and_eq_zftrue_of_some_zftrue
      hden_domain hdomain_type hdomain_true hden_eq heq_type
      (heq_truth.mpr hresult_eq)
    rw [hden_body] at hden_true
    exact congrArg (fun d : SMT.Dom => d.fst)
      (Option.some.inj hden_true)

/-- A true conjunction has a true left operand.  This small inversion lemma
is deliberately independent of the right operand: in the forward graph
direction the domain test must be recovered before a source body denotation
is available. -/
theorem lambda_and_truth_implies_left_true.{u}
    {left right body : SMT.PHOAS.Term SMT.Dom.{u}}
    {leftVal bodyVal : SMT.Dom.{u}}
    (hden_left : ⟦left⟧ˢ = some leftVal)
    (hleft_type : leftVal.snd.fst = SMTType.bool)
    (hbody_def : body = (left ∧ˢ' right))
    (hden_body : ⟦body⟧ˢ = some bodyVal)
    (hbody_true : bodyVal.fst = ZFSet.zftrue) :
    leftVal.fst = ZFSet.zftrue := by
  subst body
  obtain ⟨rightVal, hden_right, hright_type⟩ :
      ∃ rightVal : SMT.Dom.{u},
        ⟦right⟧ˢ = some rightVal ∧
          rightVal.snd.fst = SMTType.bool := by
    rcases leftVal with ⟨leftZF, leftType, hleftMem⟩
    dsimp at hleft_type hden_left
    subst leftType
    simp only [SMT.denote, Option.bind_eq_bind, hden_left] at hden_body
    match hright : ⟦right⟧ˢ with
    | none => simp [hright] at hden_body
    | some ⟨R, .bool, hR⟩ => exact ⟨⟨R, .bool, hR⟩, rfl, rfl⟩
    | some ⟨R, .int, hR⟩ => simp [hright] at hden_body
    | some ⟨R, .unit, hR⟩ => simp [hright] at hden_body
    | some ⟨R, .fun _ _, hR⟩ => simp [hright] at hden_body
    | some ⟨R, .option _, hR⟩ => simp [hright] at hden_body
    | some ⟨R, .pair _ _, hR⟩ => simp [hright] at hden_body
  exact (denote_and_both_zftrue_of_zftrue_rep_eq hden_left hleft_type
    hden_right hright_type hden_body hbody_true).1

/-- Transport an arbitrarily represented body result through a binder
substitution after a fresh outer binder has been installed.  This is the
result-valued analogue of the Boolean collection bridge: the body induction
hypothesis may choose any supported SMT representation of its source type. -/
theorem lambda_subst_of_total_body_source_fv_fresh.{u}
    {Penc : SMT.Term}
    (xs : List SMT.𝒱) (ts : List SMT.Term)
    {DeltaCtx ThetaBase : SMT.RenamingContext.Context.{u}}
    {z : SMT.𝒱} {W : SMT.Dom.{u}}
    (Ds : List SMT.Dom.{u})
    (hlen_xt : xs.length = ts.length) (hlen_xd : xs.length = Ds.length)
    (hnodup : xs.Nodup)
    (hxs_not_bv : ∀ x ∈ xs, x ∉ SMT.bv Penc)
    (hts_bv_nil : ∀ t ∈ ts, SMT.bv t = [])
    (hts_fv_not_bv : ∀ t ∈ ts, ∀ w ∈ SMT.fv t, w ∉ SMT.bv Penc)
    (hts_not_none : ∀ t ∈ ts, t ≠ SMT.Term.none)
    (hts_fv_disj_xs : ∀ t ∈ ts, ∀ w ∈ SMT.fv t, w ∉ xs)
    (hts_den : ∀ (i : ℕ) (_hi_x : i < xs.length) (hi_t : i < ts.length)
      (hi_d : i < Ds.length),
      ∃ (ht_cov : SMT.RenamingContext.CoversFV
          (Function.update DeltaCtx z (some W)) ts[i]),
        ⟦ts[i].abstract (Function.update DeltaCtx z (some W)) ht_cov⟧ˢ =
          some Ds[i])
    (hcov_sub : SMT.RenamingContext.CoversFV
      (Function.update DeltaCtx z (some W))
        (SMT.substList xs ts Penc))
    (hcov_upd : SMT.RenamingContext.CoversFV
      (Function.updates (Function.update DeltaCtx z (some W)) xs
        (Ds.map Option.some)) Penc)
    {Pterm : B.Term} {E : B.Env} {alpha : BType}
    {Lambda Gamma : SMT.TypeContext}
    {sigma : SMTType} {used : List SMT.𝒱}
    (P_total : EncodeTermRepTotal.{u}
      Pterm E alpha Lambda Penc sigma Gamma used)
    {Xi : B.RenamingContext.Context.{u}}
    (Xi_fv : ∀ v ∈ B.fv Pterm, (Xi v).isSome = true)
    (related : RValuationCastSupportedOnFV Xi ThetaBase Pterm)
    (wf : B.RenWF E.context Xi)
    (Lambda_keys_used : Lambda.keys ⊆ used)
    (source_respects : B.RenamingContext.RespectsTypeContextOnFV
      ThetaBase Lambda Pterm)
    (source_fv_in_Lambda : ∀ v ∈ B.fv Pterm, v ∈ Lambda)
    (bound_in_Lambda : ∀ v ∈ xs, v ∈ Lambda)
    (Penc_fv_in_Lambda : ∀ v ∈ SMT.fv Penc, v ∈ Lambda)
    {Pval : ZFSet.{u}} {hPval : Pval ∈ ⟦alpha⟧ᶻ}
    (den_P : ⟦Pterm.abstract Xi Xi_fv⟧ᴮ =
      some (⟨Pval, alpha, hPval⟩ : B.Dom))
    (bound_values : ∀ (i : ℕ) (hi_x : i < xs.length) (hi_d : i < Ds.length),
      ThetaBase xs[i] = some Ds[i])
    (hPenc_fv : SMT.fv Penc ⊆ B.Term.vars Pterm)
    (z_not_xs : z ∉ xs)
    (z_not_fv_Penc : z ∉ SMT.fv Penc)
    (z_not_vars_source : z ∉ B.Term.vars Pterm)
    (hctx_source : ∀ v ∈ B.Term.vars Pterm, v ∉ xs →
      DeltaCtx v = ThetaBase v) :
    ∃ dP : SMT.Dom.{u},
      ⟦(SMT.substList xs ts Penc).abstract
        (Function.update DeltaCtx z (some W)) hcov_sub⟧ˢ = some dP ∧
      dP.snd.fst = sigma ∧
      RDomCastSupported (⟨Pval, alpha, hPval⟩ : B.Dom) dP := by
  let ThetaCore : SMT.RenamingContext.Context.{u} :=
    fun v => if v ∈ Lambda then ThetaBase v else none
  have related_core : RValuationCastSupportedOnFV Xi ThetaCore Pterm := by
    intro v hv
    simpa [ThetaCore, source_fv_in_Lambda v hv] using related v hv
  have ThetaCore_none : ∀ v ∉ used, ThetaCore v = none := by
    intro v hv
    by_cases hvLambda : v ∈ Lambda
    · exact (hv (Lambda_keys_used hvLambda)).elim
    · simp [ThetaCore, hvLambda]
  have source_respects_core :
      B.RenamingContext.RespectsTypeContextOnFV
        ThetaCore Lambda Pterm := by
    intro v tau hv hlookup
    obtain ⟨d, hd, hdtype⟩ := source_respects hv hlookup
    refine ⟨d, ?_, hdtype⟩
    simpa [ThetaCore, source_fv_in_Lambda v hv] using hd
  have ThetaCore_dom : ∀ v, ThetaCore v ≠ none → v ∈ Lambda := by
    intro v hv
    by_contra hvLambda
    simp [ThetaCore, hvLambda] at hv
  obtain ⟨ThetaBody, hcov_P, dP, hbody_ext, _hbody_rel,
    _hbody_none, _source_respects, _target_respects, _hbody_dom,
    hden_P, hdP_type, hrel_P⟩ :=
    P_total Xi Xi_fv ThetaCore related_core wf ThetaCore_none
      source_respects_core ThetaCore_dom Pval hPval den_P
  have hvalues : ∀ (i : ℕ) (hi_x : i < xs.length)
      (hi_d : i < Ds.length), ThetaBody xs[i] = some Ds[i] := by
    intro i hi_x hi_d
    apply hbody_ext
    simpa [ThetaCore, bound_in_Lambda xs[i]
      (List.getElem_mem hi_x)] using bound_values i hi_x hi_d
  have hcov_P_upd : SMT.RenamingContext.CoversFV
      (Function.update ThetaBody z (some W)) Penc :=
    SMT.RenamingContext.coversFV_update_of_notMem z_not_fv_Penc hcov_P
  have hden_P_upd : ⟦Penc.abstract (Function.update ThetaBody z (some W))
      hcov_P_upd⟧ˢ = some dP := by
    calc
      ⟦Penc.abstract (Function.update ThetaBody z (some W)) hcov_P_upd⟧ˢ =
          ⟦Penc.abstract ThetaBody hcov_P⟧ˢ := by
        symm
        exact SMT.RenamingContext.denote_update_of_notMem (h := hcov_P)
          z_not_fv_Penc
      _ = some dP := hden_P
  have hvalues_upd : ∀ (i : ℕ) (hi_x : i < xs.length)
      (hi_d : i < Ds.length),
      (Function.update ThetaBody z (some W)) xs[i] = some Ds[i] := by
    intro i hi_x hi_d
    have hxz : xs[i] ≠ z := by
      intro h
      apply z_not_xs
      rw [← h]
      exact List.getElem_mem hi_x
    rw [Function.update_of_ne hxz]
    exact hvalues i hi_x hi_d
  have hbody_ext_upd : SMT.RenamingContext.Extends
      (Function.update ThetaBody z (some W))
      (Function.update ThetaCore z (some W)) := by
    intro v d hv
    by_cases hvz : v = z
    · subst v
      simpa using hv
    · rw [Function.update_of_ne hvz]
      apply hbody_ext
      rw [Function.update_of_ne hvz] at hv
      exact hv
  have hctx_Penc_upd : ∀ v ∈ SMT.fv Penc, v ∉ xs →
      (Function.update DeltaCtx z (some W)) v =
        (Function.update ThetaCore z (some W)) v := by
    intro v hv hvs
    have hvz : v ≠ z := by
      intro h
      subst v
      exact z_not_fv_Penc hv
    rw [Function.update_of_ne hvz, Function.update_of_ne hvz]
    have hraw := hctx_source v (hPenc_fv hv) hvs
    simpa [ThetaCore, Penc_fv_in_Lambda v hv] using hraw
  have hagrees : SMT.RenamingContext.AgreesOnFV
      (Function.updates (Function.update DeltaCtx z (some W)) xs
        (Ds.map Option.some))
      (Function.update ThetaBody z (some W)) Penc :=
    by
      intro v hv
      by_cases hvxs : v ∈ xs
      · exact SMT.RenamingContext.updates_eq_of_bound_denotations
          hlen_xd hnodup hvalues_upd v hvxs
      · rw [Function.updates_of_not_mem _ xs _ v hvxs]
        have hbase := hctx_Penc_upd v hv hvxs
        cases hDelta : Function.update DeltaCtx z (some W) v with
        | none =>
            have hcontr := hcov_upd v hv
            rw [Function.updates_of_not_mem _ xs _ v hvxs,
              hDelta] at hcontr
            simp at hcontr
        | some d =>
            have hThetaCore :
                Function.update ThetaCore z (some W) v = some d :=
              hbase.symm.trans hDelta
            exact (hbody_ext_upd hThetaCore).symm
  have hden_sub :=
    SMT.RenamingContext.denote_substList_eq_of_denote_and_agrees
      Penc xs ts Ds hlen_xt hlen_xd hnodup hxs_not_bv hts_bv_nil
      hts_fv_not_bv hts_not_none hts_fv_disj_xs hts_den hcov_sub
      hcov_upd hcov_P_upd hagrees hden_P_upd
  exact ⟨dP, hden_sub, hdP_type, hrel_P⟩

private lemma lambda_toDestPair_ne_none {vs : List SMT.𝒱}
    {t₀ : SMT.Term} (ht₀ : t₀ ≠ SMT.Term.none) :
    ∀ t ∈ toDestPair vs t₀, t ≠ SMT.Term.none := by
  suffices h : ∀ (ws : List SMT.𝒱) (zp : SMT.Term)
      (acc : List SMT.Term) (d : SMT.Term),
      zp ≠ SMT.Term.none →
      (∀ a ∈ acc, a ≠ SMT.Term.none) →
      d ≠ SMT.Term.none →
      ∀ t ∈ toDestPair ws zp acc d, t ≠ SMT.Term.none by
    exact h vs t₀ [] t₀ ht₀
      (fun _ hmem => absurd hmem List.not_mem_nil) ht₀
  intro ws
  induction ws with
  | nil =>
      intro _ acc _ _ hacc _ t ht
      exact hacc t ht
  | cons _ ws ih =>
      intro zp acc d hzp hacc hd
      cases ws with
      | nil =>
          unfold toDestPair
          intro t ht
          rcases List.mem_cons.mp ht with rfl | ht
          · exact hzp
          · exact hacc t ht
      | cons _ ws =>
          unfold toDestPair
          exact ih (.fst d) (.snd d :: acc) (.fst d) (by simp)
            (fun a ha => by
              rcases List.mem_cons.mp ha with rfl | ha
              · simp
              · exact hacc a ha)
            (by simp)

open Classical in
/-- Specialize the arbitrary-result substitution bridge to the tuple
projections emitted by `lambda`.  The supplied components are precisely the
denotations obtained by destructuring the represented first projection of the
fresh pair binder. -/
theorem lambda_subst_of_total_body_toDestPair.{u}
    {Penc : SMT.Term}
    {vs : List SMT.𝒱} (vs_nemp : vs ≠ []) (vs_nodup : vs.Nodup)
    {z : SMT.𝒱}
    {DeltaCtx ThetaBase : SMT.RenamingContext.Context.{u}}
    {W : SMT.Dom.{u}} {ss : Fin vs.length → SMT.Dom.{u}}
    (hcomponents : ∀ i : Fin vs.length,
      ∃ hcov : SMT.RenamingContext.CoversFV
          (Function.update DeltaCtx z (some W))
          ((toDestPair vs (.fst (.var z)))[i.val]'(by
            rw [toDestPair_length_gen vs (.fst (.var z))
              (.fst (.var z)) [] vs_nemp]
            exact i.isLt)),
        ⟦((toDestPair vs (.fst (.var z)))[i.val]'(by
          rw [toDestPair_length_gen vs (.fst (.var z))
            (.fst (.var z)) [] vs_nemp]
          exact i.isLt)).abstract (Function.update DeltaCtx z (some W))
            hcov⟧ˢ = some (ss i))
    (hcov_sub : SMT.RenamingContext.CoversFV
      (Function.update DeltaCtx z (some W))
      (SMT.substList vs (toDestPair vs (.fst (.var z))) Penc))
    (hcov_upd : SMT.RenamingContext.CoversFV
      (Function.updates (Function.update DeltaCtx z (some W)) vs
        ((List.ofFn ss).map Option.some)) Penc)
    (hvs_not_bv : ∀ v ∈ vs, v ∉ SMT.bv Penc)
    (hz_not_bv : z ∉ SMT.bv Penc)
    (hz_not_vs : z ∉ vs)
    {Pterm : B.Term} {E : B.Env} {alpha : BType}
    {Lambda Gamma : SMT.TypeContext}
    {sigma : SMTType} {used : List SMT.𝒱}
    (P_total : EncodeTermRepTotal.{u}
      Pterm E alpha Lambda Penc sigma Gamma used)
    {Xi : B.RenamingContext.Context.{u}}
    (Xi_fv : ∀ v ∈ B.fv Pterm, (Xi v).isSome = true)
    (related : RValuationCastSupportedOnFV Xi ThetaBase Pterm)
    (wf : B.RenWF E.context Xi)
    (Lambda_keys_used : Lambda.keys ⊆ used)
    (source_respects : B.RenamingContext.RespectsTypeContextOnFV
      ThetaBase Lambda Pterm)
    (source_fv_in_Lambda : ∀ v ∈ B.fv Pterm, v ∈ Lambda)
    (bound_in_Lambda : ∀ v ∈ vs, v ∈ Lambda)
    (Penc_fv_in_Lambda : ∀ v ∈ SMT.fv Penc, v ∈ Lambda)
    {Pval : ZFSet.{u}} {hPval : Pval ∈ ⟦alpha⟧ᶻ}
    (den_P : ⟦Pterm.abstract Xi Xi_fv⟧ᴮ =
      some (⟨Pval, alpha, hPval⟩ : B.Dom))
    (bound_values : ∀ (i : ℕ) (hi_x : i < vs.length)
      (_hi_d : i < (List.ofFn ss).length),
      ThetaBase vs[i] = some (ss ⟨i, hi_x⟩))
    (hPenc_fv : SMT.fv Penc ⊆ B.Term.vars Pterm)
    (z_not_vars_Pterm : z ∉ B.Term.vars Pterm)
    (hctx_source : ∀ v ∈ B.Term.vars Pterm, v ∉ vs →
      DeltaCtx v = ThetaBase v) :
    ∃ dP : SMT.Dom.{u},
      ⟦(SMT.substList vs (toDestPair vs (.fst (.var z))) Penc).abstract
        (Function.update DeltaCtx z (some W)) hcov_sub⟧ˢ = some dP ∧
      dP.snd.fst = sigma ∧
      RDomCastSupported (⟨Pval, alpha, hPval⟩ : B.Dom) dP := by
  have hlen_xt :
      vs.length = (toDestPair vs (.fst (.var z))).length := by
    rw [toDestPair_length_gen vs (.fst (.var z))
      (.fst (.var z)) [] vs_nemp]
    simp
  have hlen_xd : vs.length = (List.ofFn ss).length := by simp
  have hbound_values : ∀ (i : ℕ) (hi_x : i < vs.length)
      (hi_d : i < (List.ofFn ss).length),
      ThetaBase vs[i] = some (List.ofFn ss)[i] := by
    intro i hi_x hi_d
    simpa only [List.getElem_ofFn, Fin.getElem_fin] using
      bound_values i hi_x hi_d
  have hbase_fv : ∀ w ∈ SMT.fv (.fst (.var z)), w = z := by
    intro w hw
    simpa [SMT.fv] using hw
  have hts_fv_not_bv : ∀ t ∈ toDestPair vs (.fst (.var z)),
      ∀ w ∈ SMT.fv t, w ∉ SMT.bv Penc := by
    intro t ht w hw
    rw [SMT_fv_toDestPair_subset_base hbase_fv ht hw]
    exact hz_not_bv
  have hts_fv_disj_xs : ∀ t ∈ toDestPair vs (.fst (.var z)),
      ∀ w ∈ SMT.fv t, w ∉ vs := by
    intro t ht w hw
    rw [SMT_fv_toDestPair_subset_base hbase_fv ht hw]
    exact hz_not_vs
  have hts_den : ∀ (i : ℕ) (_hi_x : i < vs.length)
      (hi_t : i < (toDestPair vs (.fst (.var z))).length)
      (hi_d : i < (List.ofFn ss).length),
      ∃ (ht_cov : SMT.RenamingContext.CoversFV
          (Function.update DeltaCtx z (some W))
          (toDestPair vs (.fst (.var z)))[i]),
        ⟦(toDestPair vs (.fst (.var z)))[i].abstract
          (Function.update DeltaCtx z (some W)) ht_cov⟧ˢ =
            some (List.ofFn ss)[i] := by
    intro i hi_x _hi_t _hi_d
    let j : Fin vs.length := ⟨i, hi_x⟩
    obtain ⟨hcov, hden⟩ := hcomponents j
    refine ⟨hcov, ?_⟩
    simpa [j] using hden
  have hz_not_fv_Penc : z ∉ SMT.fv Penc := by
    intro hz
    exact z_not_vars_Pterm (hPenc_fv hz)
  exact lambda_subst_of_total_body_source_fv_fresh
    (xs := vs) (ts := toDestPair vs (.fst (.var z)))
    (Ds := List.ofFn ss) (DeltaCtx := DeltaCtx) (ThetaBase := ThetaBase)
    (z := z) (W := W) (Pterm := Pterm) (E := E) (alpha := alpha)
    (Lambda := Lambda) (Gamma := Gamma) (sigma := sigma) (used := used)
    (P_total := P_total) (Xi := Xi) (Xi_fv := Xi_fv)
    (related := related) (wf := wf)
    (Lambda_keys_used := Lambda_keys_used)
    (source_respects := source_respects)
    (source_fv_in_Lambda := source_fv_in_Lambda)
    (bound_in_Lambda := bound_in_Lambda)
    (Penc_fv_in_Lambda := Penc_fv_in_Lambda)
    (Pval := Pval) (hPval := hPval) (den_P := den_P)
    (bound_values := hbound_values) (hPenc_fv := hPenc_fv)
    (z_not_xs := hz_not_vs) (z_not_fv_Penc := hz_not_fv_Penc)
    (z_not_vars_source := z_not_vars_Pterm) (hctx_source := hctx_source)
    (hcov_sub := hcov_sub) (hcov_upd := hcov_upd)
    (hlen_xt := hlen_xt) (hlen_xd := hlen_xd) (hnodup := vs_nodup)
    (hxs_not_bv := hvs_not_bv)
    (hts_bv_nil := toDestPair_bv_nil_base (by simp [SMT.bv]))
    (hts_fv_not_bv := hts_fv_not_bv)
    (hts_not_none := lambda_toDestPair_ne_none (by simp))
    (hts_fv_disj_xs := hts_fv_disj_xs) (hts_den := hts_den)

open Classical in
/-- Transport a represented body result through the tuple projections used by
`lambda`, under an arbitrary valuation satisfying the body's scoped helper
contract.  Unlike the existential-totality bridge above, this statement keeps
the supplied valuation fixed. -/
theorem lambda_subst_of_guarded_body_toDestPair.{u}
    {Penc : SMT.Term}
    {vs : List SMT.𝒱} (vs_nemp : vs ≠ []) (vs_nodup : vs.Nodup)
    {z : SMT.𝒱}
    {DeltaCtx : SMT.RenamingContext.Context.{u}} {W : SMT.Dom.{u}}
    {ss : Fin vs.length → SMT.Dom.{u}}
    (hcomponents : ∀ i : Fin vs.length,
      ∃ hcov : SMT.RenamingContext.CoversFV
          (Function.update DeltaCtx z (some W))
          ((toDestPair vs (.fst (.var z)))[i.val]'(by
            rw [toDestPair_length_gen vs (.fst (.var z))
              (.fst (.var z)) [] vs_nemp]
            exact i.isLt)),
        ⟦((toDestPair vs (.fst (.var z)))[i.val]'(by
          rw [toDestPair_length_gen vs (.fst (.var z))
            (.fst (.var z)) [] vs_nemp]
          exact i.isLt)).abstract (Function.update DeltaCtx z (some W))
            hcov⟧ˢ = some (ss i))
    (hcov_sub : SMT.RenamingContext.CoversFV
      (Function.update DeltaCtx z (some W))
      (SMT.substList vs (toDestPair vs (.fst (.var z))) Penc))
    (hcov_upd : SMT.RenamingContext.CoversFV
      (Function.updates (Function.update DeltaCtx z (some W)) vs
        ((List.ofFn ss).map Option.some)) Penc)
    (hvs_not_bv : ∀ v ∈ vs, v ∉ SMT.bv Penc)
    (hz_not_bv : z ∉ SMT.bv Penc)
    (hz_not_vs : z ∉ vs)
    (hz_not_fv : z ∉ SMT.fv Penc)
    {Pterm : B.Term} {E : B.Env} {alpha : BType}
    {Base Gamma : SMT.TypeContext} {Dlt : SMT.Chunk}
    {sigma : SMTType}
    (P_guard : EncodeTermRepGuardedSound.{u}
      Pterm E alpha Penc sigma Base Dlt)
    (P_scope : ScopedContextExtends Base Dlt Gamma)
    (typ_Penc : Gamma ⊢ˢ Penc : sigma)
    {Xi : B.RenamingContext.Context.{u}}
    (Xi_fv : ∀ v ∈ B.fv Pterm, (Xi v).isSome = true)
    (related : RValuationCastSupportedOnFV Xi
      (Function.updates DeltaCtx vs
        ((List.ofFn ss).map Option.some)) Pterm)
    (wf : B.RenWF E.context Xi)
    (source_respects : B.RenamingContext.RespectsTypeContextOnFV
      (Function.updates DeltaCtx vs
        ((List.ofFn ss).map Option.some)) Gamma Pterm)
    (target_respects : SMT.RenamingContext.RespectsTypeContextOnFV
      (Function.updates DeltaCtx vs
        ((List.ofFn ss).map Option.some)) Gamma Penc)
    (specs_true : SpecBodiesTrue
      (Function.updates DeltaCtx vs
        ((List.ofFn ss).map Option.some)) Gamma Dlt)
    {Pval : ZFSet.{u}} {hPval : Pval ∈ ⟦alpha⟧ᶻ}
    (den_P : ⟦Pterm.abstract Xi Xi_fv⟧ᴮ =
      some (⟨Pval, alpha, hPval⟩ : B.Dom)) :
    ∃ dP : SMT.Dom.{u},
      ⟦(SMT.substList vs (toDestPair vs (.fst (.var z))) Penc).abstract
        (Function.update DeltaCtx z (some W)) hcov_sub⟧ˢ = some dP ∧
      dP.snd.fst = sigma ∧
      RDomCastSupported (⟨Pval, alpha, hPval⟩ : B.Dom) dP := by
  let ThetaBody : SMT.RenamingContext.Context.{u} :=
    Function.updates DeltaCtx vs ((List.ofFn ss).map Option.some)
  have hcov_P : SMT.RenamingContext.CoversFV ThetaBody Penc := by
    intro v hv
    obtain ⟨tau, hlookup⟩ := Option.isSome_iff_exists.mp <|
      AList.lookup_isSome.mpr <| SMT.Typing.mem_context_of_mem_fv
        typ_Penc hv
    obtain ⟨d, hd, _⟩ := target_respects hv hlookup
    exact Option.isSome_of_eq_some hd
  obtain ⟨dP, hden_Penc, hdP_type⟩ :=
    SMT.RenamingContext.denote_exists_of_typing_fv typ_Penc
      target_respects hcov_P
  have hrel_P : RDomCastSupported
      (⟨Pval, alpha, hPval⟩ : B.Dom) dP :=
    P_guard Gamma P_scope Xi Xi_fv ThetaBody related wf source_respects
      target_respects specs_true Pval hPval den_P hcov_P dP hden_Penc
      hdP_type
  have hcov_P_upd : SMT.RenamingContext.CoversFV
      (Function.update ThetaBody z (some W)) Penc :=
    SMT.RenamingContext.coversFV_update_of_notMem hz_not_fv hcov_P
  have hden_P_upd :
      ⟦Penc.abstract (Function.update ThetaBody z (some W))
        hcov_P_upd⟧ˢ = some dP := by
    calc
      ⟦Penc.abstract (Function.update ThetaBody z (some W))
          hcov_P_upd⟧ˢ = ⟦Penc.abstract ThetaBody hcov_P⟧ˢ := by
        exact (SMT.RenamingContext.denote_update_of_notMem
          (h := hcov_P) hz_not_fv).symm
      _ = some dP := hden_Penc
  have hlen_xt :
      vs.length = (toDestPair vs (.fst (.var z))).length := by
    rw [toDestPair_length_gen vs (.fst (.var z))
      (.fst (.var z)) [] vs_nemp]
    simp
  have hlen_xd : vs.length = (List.ofFn ss).length := by simp
  have hbase_fv : ∀ w ∈ SMT.fv (.fst (.var z)), w = z := by
    intro w hw
    simpa [SMT.fv] using hw
  have hts_fv_not_bv : ∀ t ∈ toDestPair vs (.fst (.var z)),
      ∀ w ∈ SMT.fv t, w ∉ SMT.bv Penc := by
    intro t ht w hw
    rw [SMT_fv_toDestPair_subset_base hbase_fv ht hw]
    exact hz_not_bv
  have hts_fv_disj_vs : ∀ t ∈ toDestPair vs (.fst (.var z)),
      ∀ w ∈ SMT.fv t, w ∉ vs := by
    intro t ht w hw
    rw [SMT_fv_toDestPair_subset_base hbase_fv ht hw]
    exact hz_not_vs
  have hts_den : ∀ (i : ℕ) (_hi_x : i < vs.length)
      (hi_t : i < (toDestPair vs (.fst (.var z))).length)
      (hi_d : i < (List.ofFn ss).length),
      ∃ (ht_cov : SMT.RenamingContext.CoversFV
          (Function.update DeltaCtx z (some W))
          (toDestPair vs (.fst (.var z)))[i]),
        ⟦(toDestPair vs (.fst (.var z)))[i].abstract
          (Function.update DeltaCtx z (some W)) ht_cov⟧ˢ =
            some (List.ofFn ss)[i] := by
    intro i hi_x _hi_t _hi_d
    let j : Fin vs.length := ⟨i, hi_x⟩
    obtain ⟨hcov, hden⟩ := hcomponents j
    exact ⟨hcov, by simpa [j] using hden⟩
  have hagrees : SMT.RenamingContext.AgreesOnFV
      (Function.updates (Function.update DeltaCtx z (some W)) vs
        ((List.ofFn ss).map Option.some))
      (Function.update ThetaBody z (some W)) Penc := by
    intro v hv
    dsimp [ThetaBody]
    by_cases hvs : v ∈ vs
    · have hvz : v ≠ z := fun hvz => hz_not_vs (hvz ▸ hvs)
      rw [Function.update_of_ne hvz,
        Function.updates_eq_if (by simp) vs_nodup,
        Function.updates_eq_if (by simp) vs_nodup,
        dif_pos hvs, dif_pos hvs]
    · have hvz : v ≠ z := fun hvz => hz_not_fv (hvz ▸ hv)
      rw [Function.updates_of_not_mem _ vs _ v hvs,
        Function.update_of_ne hvz, Function.update_of_ne hvz,
        Function.updates_of_not_mem _ vs _ v hvs]
  have hden_sub :=
    SMT.RenamingContext.denote_substList_eq_of_denote_and_agrees
      Penc vs (toDestPair vs (.fst (.var z))) (List.ofFn ss)
      hlen_xt hlen_xd vs_nodup hvs_not_bv
      (toDestPair_bv_nil_base (by simp [SMT.bv])) hts_fv_not_bv
      (lambda_toDestPair_ne_none (by simp)) hts_fv_disj_vs hts_den
      hcov_sub hcov_upd hcov_P_upd hagrees hden_P_upd
  exact ⟨dP, hden_sub, hdP_type, hrel_P⟩

open Classical in
/-- A successful denotation of a unary SMT lambda already witnesses totality
of its body at every well-typed bound argument.  This inversion is independent
of any ambient typing context, which is essential for guarded soundness under
an arbitrary declaration super-context. -/
theorem lambda_body_total_of_denote.{u}
    {Theta : SMT.RenamingContext.Context.{u}}
    {z : SMT.𝒱} {sigma : SMTType} {body : SMT.Term}
    {lamVal : SMT.Dom.{u}}
    (hcov_lambda : SMT.RenamingContext.CoversFV Theta
      ((λˢ [z]) [sigma] body))
    (hden_lambda :
      ⟦((λˢ [z]) [sigma] body).abstract Theta hcov_lambda⟧ˢ =
        some lamVal)
    (hcov_body_upd : ∀ W : SMT.Dom.{u},
      SMT.RenamingContext.CoversFV
        (Function.update Theta z (some W)) body) :
    ∀ W : SMT.Dom.{u}, W.snd.fst = sigma →
      ∃ bodyVal : SMT.Dom.{u},
        ⟦body.abstract (Function.update Theta z (some W))
          (hcov_body_upd W)⟧ˢ = some bodyVal := by
  intro W hW
  have hWmem : W.fst ∈ ⟦sigma⟧ᶻ := by
    rw [← hW]
    exact W.snd.snd
  have hden := hden_lambda
  simp only [SMT.Term.abstract] at hden
  rw [dif_pos (by simp)] at hden
  unfold SMT.denote at hden
  rw [dif_pos (by simp)] at hden
  split_ifs at hden with hbody_some hbody_type
  · let xs : Fin [z].length → SMT.Dom.{u} := fun _ => W
    have hxs : ∀ i,
        (xs i).snd.fst = (fun j => [sigma][j]) i ∧
        (xs i).fst ∈ ⟦(fun j => [sigma][j]) i⟧ᶻ := by
      intro i
      rcases i with ⟨i, hi⟩
      have hi' : i < 1 := by simpa using hi
      have hi0 : i = 0 := by omega
      subst i
      simpa [xs] using And.intro hW hWmem
    have hsome := hbody_some hxs
    obtain ⟨bodyVal, hbodyVal⟩ := Option.isSome_iff_exists.mp hsome
    refine ⟨bodyVal, ?_⟩
    have hbase : ∀ v ∈ SMT.fv body, v ∉ [z] →
        (Theta v).isSome = true := by
      intro v hv hvz
      apply hcov_lambda v
      simp only [SMT.fv, List.mem_removeAll_iff]
      exact ⟨hv, hvz⟩
    have htmp : ∀ v ∈ SMT.fv body,
        (Function.updates Theta [z] [some W] v).isSome = true := by
      intro v hv
      simpa [Function.updates] using hcov_body_upd W v hv
    have hbridge := SMT.Term.abstract.go.alt_def₂ [z] body [W]
      (by simp) hbase htmp
    have hxs_eq : xs = fun i => [W][i] := by
      funext i
      rcases i with ⟨i, hi⟩
      have hi' : i < 1 := by simpa using hi
      have hi0 : i = 0 := by omega
      subst i
      simp [xs]
    rw [hxs_eq] at hbodyVal
    have hbodyVal' :
        ⟦(SMT.Term.abstract.go body [z] Theta hbase).uncurry
          (fun i => [W][i])⟧ˢ = some bodyVal := by
      simpa only [proof_irrel_heq] using hbodyVal
    have hbridge' :
        (SMT.Term.abstract.go body [z] Theta hbase).uncurry
            (fun i => [W][i]) =
          body.abstract
            (Function.updates Theta [z] (List.map Option.some [W]))
            htmp := by
      simpa only [proof_irrel_heq] using hbridge
    rw [hbridge'] at hbodyVal'
    simpa [Function.updates, proof_irrel_heq] using hbodyVal'

set_option maxHeartbeats 2000000 in
open Classical in
/-- A successfully denoting encoded lambda exposes a denoting domain
predicate of the expected function type.  The proof evaluates the body at a
default pair, then removes the fresh lambda variable from the recovered
domain denotation.  Unlike a typing argument, this remains valid when the
ambient context contains arbitrary additional declarations. -/
theorem lambda_domain_denote_of_lambda_denote.{u}
    {Theta : SMT.RenamingContext.Context.{u}}
    {z : SMT.𝒱} {sigma gamma : SMTType}
    {Denc Psub : SMT.Term} {lamVal : SMT.Dom.{u}}
    (hcov_lambda : SMT.RenamingContext.CoversFV Theta
      ((λˢ [z]) [sigma.pair gamma]
        (SMT.Term.and
          (SMT.Term.app Denc (SMT.Term.fst (.var z)))
          (SMT.Term.eq (SMT.Term.snd (.var z)) Psub))))
    (hden_lambda :
      ⟦((λˢ [z]) [sigma.pair gamma]
        (SMT.Term.and
          (SMT.Term.app Denc (SMT.Term.fst (.var z)))
          (SMT.Term.eq (SMT.Term.snd (.var z)) Psub))).abstract
          Theta hcov_lambda⟧ˢ = some lamVal)
    (hcov_body_upd : ∀ W : SMT.Dom.{u},
      SMT.RenamingContext.CoversFV (Function.update Theta z (some W))
        (SMT.Term.and
          (SMT.Term.app Denc (SMT.Term.fst (.var z)))
          (SMT.Term.eq (SMT.Term.snd (.var z)) Psub)))
    (hcov_D : SMT.RenamingContext.CoversFV Theta Denc)
    (z_not_fv_D : z ∉ SMT.fv Denc) :
    ∃ d : SMT.Dom.{u}, ⟦Denc.abstract Theta hcov_D⟧ˢ = some d ∧
      d.snd.fst = SMTType.fun sigma SMTType.bool := by
  let W : SMT.Dom.{u} :=
    ⟨(sigma.pair gamma).defaultZFSet, sigma.pair gamma,
      SMTType.mem_toZFSet_of_defaultZFSet⟩
  obtain ⟨bodyVal, hbody⟩ := lambda_body_total_of_denote
    hcov_lambda hden_lambda hcov_body_upd W rfl
  have hcov_D_upd : SMT.RenamingContext.CoversFV
      (Function.update Theta z (some W)) Denc :=
    SMT.RenamingContext.coversFV_update_of_notMem z_not_fv_D hcov_D
  simp only [SMT.Term.abstract, SMT.denote, Option.bind_eq_bind] at hbody
  match hD : ⟦Denc.abstract (Function.update Theta z (some W))
      hcov_D_upd⟧ˢ with
  | none => simp [hD] at hbody
  | some ⟨F, .bool, hF⟩ => simp [hD] at hbody
  | some ⟨F, .int, hF⟩ => simp [hD] at hbody
  | some ⟨F, .unit, hF⟩ => simp [hD] at hbody
  | some ⟨F, .option a, hF⟩ => simp [hD] at hbody
  | some ⟨F, .pair a b, hF⟩ => simp [hD] at hbody
  | some ⟨F, .fun a b, hF⟩ =>
      simp [W, hD] at hbody
      split_ifs at hbody with ha hp hdom
      · subst a
        cases b with
        | bool =>
            refine ⟨⟨F, .fun sigma .bool, hF⟩, ?_, rfl⟩
            calc
              ⟦Denc.abstract Theta hcov_D⟧ˢ =
                  ⟦Denc.abstract (Function.update Theta z (some W))
                    hcov_D_upd⟧ˢ := by
                exact SMT.RenamingContext.denote_update_of_notMem
                  (h := hcov_D) z_not_fv_D
              _ = some ⟨F, .fun sigma .bool, hF⟩ := hD
        | int => simp at hbody
        | unit => simp at hbody
        | «fun» c d => simp at hbody
        | option c => simp at hbody
        | pair c d => simp at hbody
      · simp at hbody
      · simp at hbody
      · simp at hbody

open Classical in
/-- Evaluate the encoded lambda body at a represented source-domain point.
The body result is related at its arbitrary encoder-chosen target type, and
the emitted Boolean conjunction is true exactly when the lambda's second
target component is that represented result. -/
theorem represented_lambda_body_at_domain.{u}
    {vs : List B.𝒱} (vs_nemp : vs ≠ []) (vs_nodup : vs.Nodup)
    {D P : B.Term} {tau beta : BType}
    {Xi : B.RenamingContext.Context.{u}}
    (Xi_fv : ∀ v ∈ B.fv (B.Term.lambda vs D P),
      (Xi v).isSome = true)
    (tau_hasArity : tau.hasArity vs.length)
    {Dval : ZFSet.{u}} {hDval : Dval ∈ ⟦BType.set tau⟧ᶻ}
    (den_D : ⟦D.abstract Xi
      (fun v hv => Xi_fv v (B.fv.mem_lambda (.inl hv)))⟧ᴮ =
      some (⟨Dval, BType.set tau, hDval⟩ : B.Dom))
    {T : ZFSet.{u}} {hT : T ∈ ⟦BType.set (tau ×ᴮ beta)⟧ᶻ}
    (den_lambda : ⟦(B.Term.lambda vs D P).abstract Xi Xi_fv⟧ᴮ =
      some (⟨T, BType.set (tau ×ᴮ beta), hT⟩ : B.Dom))
    {sigma gamma : SMTType}
    (hsigma : BType.SupportedSMT tau sigma)
    {Denc Penc body : SMT.Term} {z : SMT.𝒱}
    {ThetaD : SMT.RenamingContext.Context.{u}}
    {DencVal : SMT.Dom.{u}}
    (body_def : body = SMT.Term.and
      (SMT.Term.app Denc (SMT.Term.fst (SMT.Term.var z)))
      (SMT.Term.eq (SMT.Term.snd (SMT.Term.var z))
        (SMT.substList vs
          (toDestPair vs (SMT.Term.fst (SMT.Term.var z))) Penc)))
    (hcov_D_upd : ∀ W : SMT.Dom.{u},
      SMT.RenamingContext.CoversFV
        (Function.update ThetaD z (some W)) Denc)
    (den_D_upd : ∀ W : SMT.Dom.{u},
      ⟦Denc.abstract (Function.update ThetaD z (some W))
        (hcov_D_upd W)⟧ˢ = some DencVal)
    (hDenc_type : DencVal.snd.fst = sigma.fun SMTType.bool)
    (hDenc_func : ⟦sigma⟧ᶻ.IsFunc ZFSet.𝔹 DencVal.fst)
    (D_rel : RDomCastSupported
      (⟨Dval, BType.set tau, hDval⟩ : B.Dom) DencVal)
    (hcov_body_upd : ∀ W : SMT.Dom.{u},
      SMT.RenamingContext.CoversFV
        (Function.update ThetaD z (some W)) body)
    (hcov_sub_upd : ∀ W : SMT.Dom.{u},
      SMT.RenamingContext.CoversFV
        (Function.update ThetaD z (some W))
        (SMT.substList vs
          (toDestPair vs (SMT.Term.fst (SMT.Term.var z))) Penc))
    (hcov_P_upd : ∀ (W : SMT.Dom.{u})
      (ss : Fin vs.length → SMT.Dom.{u}),
      SMT.RenamingContext.CoversFV
        (Function.updates (Function.update ThetaD z (some W)) vs
          ((List.ofFn ss).map Option.some)) Penc)
    (hvs_not_bv : ∀ v ∈ vs, v ∉ SMT.bv Penc)
    (hz_not_bv : z ∉ SMT.bv Penc) (hz_not_vs : z ∉ vs)
    {Ebody : B.Env} {LambdaP GammaP : SMT.TypeContext}
    {usedP : List SMT.𝒱}
    (typ_P : Ebody.context ⊢ᴮ P : beta)
    (P_total : EncodeTermRepTotal.{u}
      P Ebody beta LambdaP Penc gamma GammaP usedP)
    (ambient : ∀ v ∈ B.fv P, v ∉ vs →
      match Xi v, ThetaD v with
      | some source, some target => RDomCastSupported source target
      | _, _ => False)
    (wf_bound : ∀ (x : ZFSet.{u}) (hx : x ∈ ⟦tau⟧ᶻ)
      (_hx_D : x ∈ Dval),
      B.RenWF Ebody.context
        (Function.updates Xi vs (List.ofFn fun i => some
          (⟨x.get vs.length i, tau.get vs.length i,
            get_mem_type_of_isTuple
              (hasArity_of_mem_toZFSet tau_hasArity hx)
              tau_hasArity hx⟩ : B.Dom))))
    (bound_expected : ∀ i : Fin vs.length,
      LambdaP.lookup vs[i] =
        some ((sigma.fromProdl (vs.length - 1))[i.val]'(by
          have hlen := hsigma.fromProdl_length_of_hasArity tau_hasArity
          exact i.isLt.trans_eq hlen.symm)))
    (source_respects : ∀ ss : Fin vs.length → SMT.Dom.{u},
      (∀ i, LambdaP.lookup vs[i] = some (ss i).snd.fst) →
      B.RenamingContext.RespectsTypeContextOnFV
        (Function.updates ThetaD vs
          ((List.ofFn ss).map Option.some)) LambdaP P)
    (source_fv_in_LambdaP : ∀ v ∈ B.fv P, v ∈ LambdaP)
    (Penc_fv_in_LambdaP : ∀ v ∈ SMT.fv Penc, v ∈ LambdaP)
    (LambdaP_keys_used : LambdaP.keys ⊆ usedP)
    (hPenc_fv : SMT.fv Penc ⊆ B.Term.vars P)
    (z_not_vars_P : z ∉ B.Term.vars P)
    {x : ZFSet.{u}} (hx : x ∈ ⟦tau⟧ᶻ) (hxD : x ∈ Dval)
    {Wy Wp : SMT.Dom.{u}}
    (hWy_type : Wy.snd.fst = sigma)
    (hWy_mem : Wy.fst ∈ ⟦sigma⟧ᶻ)
    (hrel_x : RDomCastSupported (⟨x, tau, hx⟩ : B.Dom) Wy)
    (hWp_type : Wp.snd.fst = gamma)
    (hWp_mem : Wp.fst ∈ ⟦gamma⟧ᶻ) :
    let Wxy : SMT.Dom.{u} :=
      ⟨Wy.fst.pair Wp.fst, sigma.pair gamma,
        ZFSet.pair_mem_prod.mpr ⟨hWy_mem, hWp_mem⟩⟩
    ∃ (XiP_fv : ∀ v ∈ B.fv P,
        (Function.updates Xi vs (List.ofFn fun i => some
          (⟨x.get vs.length i, tau.get vs.length i,
            get_mem_type_of_isTuple
              (hasArity_of_mem_toZFSet tau_hasArity hx)
              tau_hasArity hx⟩ : B.Dom)) v).isSome = true)
      (Pval : ZFSet.{u}) (hPval : Pval ∈ ⟦beta⟧ᶻ)
      (dP : SMT.Dom.{u}),
      ⟦P.abstract
        (Function.updates Xi vs (List.ofFn fun i => some
          (⟨x.get vs.length i, tau.get vs.length i,
            get_mem_type_of_isTuple
              (hasArity_of_mem_toZFSet tau_hasArity hx)
              tau_hasArity hx⟩ : B.Dom))) XiP_fv⟧ᴮ =
        some (⟨Pval, beta, hPval⟩ : B.Dom) ∧
      ⟦(SMT.substList vs
        (toDestPair vs (SMT.Term.fst (SMT.Term.var z))) Penc).abstract
        (Function.update ThetaD z (some Wxy))
        (hcov_sub_upd Wxy)⟧ˢ = some dP ∧
      dP.snd.fst = gamma ∧
      RDomCastSupported (⟨Pval, beta, hPval⟩ : B.Dom) dP ∧
      ∀ bodyVal : SMT.Dom.{u},
        ⟦body.abstract (Function.update ThetaD z (some Wxy))
          (hcov_body_upd Wxy)⟧ˢ = some bodyVal →
        (bodyVal.fst = ZFSet.zftrue ↔ Wp.fst = dP.fst) := by
  dsimp only
  let Wxy : SMT.Dom.{u} :=
    ⟨Wy.fst.pair Wp.fst, sigma.pair gamma,
      ZFSet.pair_mem_prod.mpr ⟨hWy_mem, hWp_mem⟩⟩
  let x_fin : Fin vs.length → B.Dom.{u} := fun i =>
    ⟨x.get vs.length i, tau.get vs.length i,
      get_mem_type_of_isTuple
        (hasArity_of_mem_toZFSet tau_hasArity hx)
        tau_hasArity hx⟩
  have hx_fin_typ : ∀ i, (x_fin i).snd.fst = tau.get vs.length i ∧
      (x_fin i).fst ∈ ⟦tau.get vs.length i⟧ᶻ :=
    fun i => ⟨rfl, (x_fin i).snd.snd⟩
  have hx_fin_eq : ZFSet.ofFinDom x_fin = x := by
    simpa [x_fin] using
      (ZFSet.ofFinDom_get (List.length_pos_iff.mpr vs_nemp)
        (fun i => get_mem_type_of_isTuple
          (hasArity_of_mem_toZFSet tau_hasArity hx)
          tau_hasArity hx)
        (hasArity_of_mem_toZFSet tau_hasArity hx) tau_hasArity)
  have hx_fin_D : ZFSet.ofFinDom x_fin ∈ Dval := by
    rw [hx_fin_eq]
    exact hxD
  obtain ⟨XiP_fv, Pval, hPval, den_P⟩ :=
    B.denote_lambda_body_exists Xi_fv vs_nemp vs_nodup tau_hasArity
      den_D den_lambda typ_P hx_fin_typ hx_fin_D (wf_bound x hx hxD)
  have hcov_fst : SMT.RenamingContext.CoversFV
      (Function.update ThetaD z (some Wxy)) (.fst (.var z)) := by
    intro v hv
    simp only [SMT.fv, List.mem_singleton] at hv
    subst v
    simp
  have hden_fst : ⟦(SMT.Term.fst (.var z)).abstract
      (Function.update ThetaD z (some Wxy)) hcov_fst⟧ˢ = some Wy := by
    simp only [SMT.Term.abstract, SMT.denote, Function.update_self]
    apply congrArg some
    exact SMT.RenamingContext.Dom_ext' (by simp [Wxy]) hWy_type.symm
  obtain ⟨ss, hcomponents, related_P⟩ :=
    represented_lambda_toDestPair_bound_context vs_nemp vs_nodup
      tau_hasArity hsigma hx hcov_fst hden_fst hWy_type hWy_mem hrel_x
      ambient
  have hss_map : (List.ofFn ss).map Option.some =
      List.ofFn (fun i => some (ss i)) := by
    rw [List.map_ofFn]
    rfl
  have related_P' : RValuationCastSupportedOnFV
      (Function.updates Xi vs (List.ofFn fun i => some (x_fin i)))
      (Function.updates ThetaD vs
        ((List.ofFn ss).map Option.some)) P := by
    rw [hss_map]
    simpa [x_fin] using related_P
  have hss_type : ∀ i : Fin vs.length,
      LambdaP.lookup vs[i] = some (ss i).snd.fst := by
    intro i
    obtain ⟨_, _, _, htype⟩ := hcomponents i
    exact (bound_expected i).trans (congrArg some htype).symm
  have vs_in_LambdaP : ∀ v ∈ vs, v ∈ LambdaP := by
    intro v hv
    let i : Fin vs.length :=
      ⟨vs.idxOf v, List.idxOf_lt_length_of_mem hv⟩
    have hvi : vs[i] = v := List.getElem_idxOf i.isLt
    rw [← hvi]
    exact AList.lookup_isSome.mp
      (Option.isSome_of_eq_some (bound_expected i))
  let ThetaBase : SMT.RenamingContext.Context.{u} :=
    Function.updates ThetaD vs ((List.ofFn ss).map Option.some)
  have bound_values : ∀ (i : ℕ) (hi_x : i < vs.length)
      (_hi_d : i < (List.ofFn ss).length),
      ThetaBase vs[i] = some (ss ⟨i, hi_x⟩) := by
    intro i hi_x _hi_d
    dsimp [ThetaBase]
    rw [Function.updates_eq_if (by simp) vs_nodup,
      dif_pos (List.getElem_mem hi_x)]
    simp [List.Nodup.idxOf_getElem vs_nodup]
  have hctx_source : ∀ v ∈ B.Term.vars P, v ∉ vs →
      ThetaD v = ThetaBase v := by
    intro v _hv hvs
    dsimp [ThetaBase]
    rw [Function.updates_of_not_mem ThetaD vs _ v hvs]
  obtain ⟨dP, hden_Psub, hdP_type, hrel_P⟩ :=
    lambda_subst_of_total_body_toDestPair
      (Penc := Penc) vs_nemp vs_nodup (z := z) (DeltaCtx := ThetaD)
      (ThetaBase := ThetaBase) (W := Wxy) (ss := ss)
      (hcomponents := by
        intro i
        obtain ⟨hcov, hden, _, _⟩ := hcomponents i
        exact ⟨hcov, hden⟩)
      (hcov_sub := hcov_sub_upd Wxy)
      (hcov_upd := hcov_P_upd Wxy ss)
      hvs_not_bv hz_not_bv hz_not_vs P_total XiP_fv
      (by simpa [ThetaBase, x_fin] using related_P')
      (wf_bound x hx hxD) LambdaP_keys_used (source_respects ss hss_type)
      source_fv_in_LambdaP vs_in_LambdaP Penc_fv_in_LambdaP den_P
      bound_values hPenc_fv z_not_vars_P hctx_source
  obtain ⟨hcov_Dapp, Dapp, hDapp_type, hDapp_value, hden_Dapp⟩ :=
    funDenoteAppAtFst (Δctx := ThetaD) (t := Denc) (x := z)
      (α := sigma) (β := SMTType.bool) (γ := gamma) (Y := DencVal)
      hcov_D_upd den_D_upd hDenc_type hDenc_func Wxy rfl Wxy.snd.snd
  let Wy' : SMT.Dom.{u} :=
    ⟨Wy.fst, sigma, by rw [← hWy_type]; exact Wy.snd.snd⟩
  have hWy_eq : Wy = Wy' := by
    exact SMT.RenamingContext.Dom_ext' rfl hWy_type
  have hrel_x' : RDomCastSupported
      (⟨x, tau, hx⟩ : B.Dom) Wy' := by
    simpa only [hWy_eq] using hrel_x
  let DencVal' : SMT.Dom.{u} :=
    ⟨DencVal.fst, sigma.fun SMTType.bool, by
      rw [← hDenc_type]
      exact DencVal.snd.snd⟩
  have hDencVal_eq : DencVal = DencVal' := by
    exact SMT.RenamingContext.Dom_ext' rfl hDenc_type
  have D_rel' : RDomCastSupported
      (⟨Dval, BType.set tau, hDval⟩ : B.Dom) DencVal' := by
    simpa only [hDencVal_eq] using D_rel
  have hDapp_true : Dapp.fst = ZFSet.zftrue := by
    rw [hDapp_value]
    simpa [Wxy] using
      (RDomCastSupported.setPred_fapply_eq_zftrue_iff
        hrel_x'.toRDomCast D_rel').mpr hxD
  have hcov_snd : SMT.RenamingContext.CoversFV
      (Function.update ThetaD z (some Wxy)) (.snd (.var z)) := by
    intro v hv
    simp only [SMT.fv, List.mem_singleton] at hv
    subst v
    simp
  have hden_snd : ⟦(SMT.Term.snd (.var z)).abstract
      (Function.update ThetaD z (some Wxy)) hcov_snd⟧ˢ = some Wp := by
    simp only [SMT.Term.abstract, SMT.denote, Function.update_self]
    apply congrArg some
    exact SMT.RenamingContext.Dom_ext' (by simp [Wxy]) hWp_type.symm
  refine ⟨XiP_fv, Pval, hPval, dP, ?_, hden_Psub, hdP_type,
    hrel_P, ?_⟩
  · simpa [x_fin] using den_P
  · intro bodyVal hden_body
    have hbody_abs : body.abstract
        (Function.update ThetaD z (some Wxy)) (hcov_body_upd Wxy) =
        ((SMT.Term.app Denc (.fst (.var z))).abstract
          (Function.update ThetaD z (some Wxy)) hcov_Dapp ∧ˢ'
        ((SMT.Term.snd (.var z)).abstract
          (Function.update ThetaD z (some Wxy)) hcov_snd =ˢ'
        (SMT.substList vs (toDestPair vs (.fst (.var z))) Penc).abstract
          (Function.update ThetaD z (some Wxy))
          (hcov_sub_upd Wxy))) := by
      subst body
      simp only [SMT.Term.abstract]
    have htruth := lambda_and_eq_truth_iff hden_Dapp hDapp_type
      hden_snd hden_Psub (hWp_type.trans hdP_type.symm) hbody_abs hden_body
    simpa only [hDapp_true, true_and] using htruth

/- Both interpreter branches compute the same extensional graph: the
nonempty branch chooses a domain element only to determine the result type,
while the empty branch is the empty instance of this separation. -/
open Classical in
theorem B.denote_lambda_eq_sep.{u}
    {vs : List B.𝒱} {D P : B.Term} {tau beta : BType}
    {Xi : B.RenamingContext.Context.{u}}
    (Xi_fv : ∀ v ∈ B.fv (B.Term.lambda vs D P),
      (Xi v).isSome = true)
    (tau_hasArity : tau.hasArity vs.length)
    {Dval : ZFSet.{u}} {hDval : Dval ∈ ⟦BType.set tau⟧ᶻ}
    (den_D : ⟦D.abstract Xi
      (fun v hv => Xi_fv v (B.fv.mem_lambda (.inl hv)))⟧ᴮ =
      some (⟨Dval, BType.set tau, hDval⟩ : B.Dom))
    {T : ZFSet.{u}} {hT : T ∈ ⟦BType.set (tau ×ᴮ beta)⟧ᶻ}
    (den_lambda : ⟦(B.Term.lambda vs D P).abstract Xi Xi_fv⟧ᴮ =
      some (⟨T, BType.set (tau ×ᴮ beta), hT⟩ : B.Dom)) :
    ZFSet.sep (fun xy =>
      if hxy : xy.hasArity 2 then
        if hx : xy.π₁.hasArity vs.length ∧ xy.π₁ ∈ Dval then
          match (motive := Option B.Dom → Prop)
            ⟦(B.Term.abstract.go P vs Xi (fun v hv hvs => Xi_fv v
              (B.fv.mem_lambda (.inr ⟨hv, hvs⟩)))).uncurry
              (fun i => ⟨xy.π₁.get vs.length i,
                tau.get vs.length i, by
                  rw [BType.toZFSet, ZFSet.mem_powerset] at hDval
                  exact get_mem_type_of_isTuple hx.1 tau_hasArity
                    (hDval hx.2)⟩)⟧ᴮ with
          | some ⟨ex, xi, _⟩ => if xi = beta then ex = xy.π₂ else False
          | none => False
        else False
      else False) (Dval.prod ⟦beta⟧ᶻ) = T := by
  have h_inv := den_lambda
  simp only [B.Term.abstract] at h_inv
  unfold B.denote at h_inv
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h_inv
  obtain ⟨D_dom, hden_d, rest⟩ := h_inv
  have hconv_d : ⟦D.abstract Xi
      (fun v hv => Xi_fv v (B.fv.mem_lambda (.inl hv)))⟧ᴮ =
      some D_dom := by
    convert hden_d using 2
  have hD_dom_eq : D_dom =
      (⟨Dval, BType.set tau, hDval⟩ : B.Dom) := by
    rw [hconv_d] at den_D
    exact Option.some.inj den_D
  subst D_dom
  simp only at rest
  rw [dif_pos tau_hasArity] at rest
  split_ifs at rest with h_den_P h_typP_det h_nemp h_chosen_arity
    h_default_arity
  · simp only [Option.bind_eq_some_iff] at rest
    obtain ⟨bodyD, hbodyD, hout⟩ := rest
    simp only [Option.pure_def, Option.some.injEq, PSigma.mk.injEq] at hout
    obtain ⟨hT_eq, hty_eq⟩ := hout
    subst T
    simp only [heq_eq_eq, PSigma.mk.injEq, BType.set.injEq,
      BType.prod.injEq] at hty_eq
    obtain ⟨⟨_, hbeta⟩, _⟩ := hty_eq
    subst beta
    rfl
  · simp only [Option.bind_eq_some_iff] at rest
    obtain ⟨bodyD, hbodyD, hout⟩ := rest
    simp only [Option.pure_def, Option.some.injEq, PSigma.mk.injEq] at hout
    obtain ⟨hT_eq, hty_eq⟩ := hout
    subst T
    simp only [heq_eq_eq, PSigma.mk.injEq, BType.set.injEq,
      BType.prod.injEq] at hty_eq
    obtain ⟨⟨_, hbeta⟩, _⟩ := hty_eq
    subst beta
    have hDempty : Dval = ∅ := not_ne_iff.mp h_nemp
    apply ZFSet.ext
    intro xy
    constructor
    · intro hxy
      have hprod := (ZFSet.mem_sep.mp hxy).1
      rw [ZFSet.mem_prod] at hprod
      obtain ⟨x, hx, y, hy, hxy_eq⟩ := hprod
      have hxempty : x ∈ (∅ : ZFSet) := hDempty ▸ hx
      exact (by simpa using hxempty : False).elim
    · intro hxy
      exact (by simpa using hxy : False).elim

/- Membership in the denoted lambda graph is domain membership together with
equality to the instantiated body result. -/
open Classical in
theorem B.denote_lambda_member_iff.{u}
    {vs : List B.𝒱} {D P : B.Term} {tau beta : BType}
    {Xi : B.RenamingContext.Context.{u}}
    (Xi_fv : ∀ v ∈ B.fv (B.Term.lambda vs D P),
      (Xi v).isSome = true)
    (tau_hasArity : tau.hasArity vs.length)
    {Dval : ZFSet.{u}} {hDval : Dval ∈ ⟦BType.set tau⟧ᶻ}
    (den_D : ⟦D.abstract Xi
      (fun v hv => Xi_fv v (B.fv.mem_lambda (.inl hv)))⟧ᴮ =
      some (⟨Dval, BType.set tau, hDval⟩ : B.Dom))
    {T : ZFSet.{u}} {hT : T ∈ ⟦BType.set (tau ×ᴮ beta)⟧ᶻ}
    (den_lambda : ⟦(B.Term.lambda vs D P).abstract Xi Xi_fv⟧ᴮ =
      some (⟨T, BType.set (tau ×ᴮ beta), hT⟩ : B.Dom))
    {x p Pval : ZFSet.{u}}
    (hx_arity : x.hasArity vs.length)
    (hx_type : x ∈ ⟦tau⟧ᶻ) (hp_type : p ∈ ⟦beta⟧ᶻ)
    (hPval : Pval ∈ ⟦beta⟧ᶻ)
    (den_P : ⟦(B.Term.abstract.go P vs Xi (fun v hv hvs => Xi_fv v
      (B.fv.mem_lambda (.inr ⟨hv, hvs⟩)))).uncurry
        (fun i => ⟨x.get vs.length i, tau.get vs.length i,
          get_mem_type_of_isTuple hx_arity tau_hasArity hx_type⟩)⟧ᴮ =
      some (⟨Pval, beta, hPval⟩ : B.Dom)) :
    x.pair p ∈ T ↔ x ∈ Dval ∧ Pval = p := by
  rw [← B.denote_lambda_eq_sep Xi_fv tau_hasArity den_D
    den_lambda, ZFSet.mem_sep]
  constructor
  · rintro ⟨hprod, hgraph⟩
    rw [ZFSet.mem_prod] at hprod
    obtain ⟨x', hx', p', hp', hpair⟩ := hprod
    rw [ZFSet.pair_inj] at hpair
    rcases hpair with ⟨hxx, hpp⟩
    subst x'
    subst p'
    refine ⟨hx', ?_⟩
    rw [dif_pos ZFSet.isTuple_pair, ZFSet.π₁_pair, ZFSet.π₂_pair,
      dif_pos ⟨hx_arity, hx'⟩] at hgraph
    simpa [den_P] using hgraph
  · rintro ⟨hxD, hP⟩
    subst p
    refine ⟨?_, ?_⟩
    · exact ZFSet.pair_mem_prod.mpr ⟨hxD, hPval⟩
    · rw [dif_pos ZFSet.isTuple_pair, ZFSet.π₁_pair, ZFSet.π₂_pair,
        dif_pos ⟨hx_arity, hxD⟩]
      simpa [den_P]

/- Every member of the denoted lambda graph has its first projection in the
source domain.  This direction does not require evaluating the body and is
therefore usable to bootstrap body totality in the backward representation
argument. -/
open Classical in
theorem B.denote_lambda_member_domain.{u}
    {vs : List B.𝒱} {D P : B.Term} {tau beta : BType}
    {Xi : B.RenamingContext.Context.{u}}
    (Xi_fv : ∀ v ∈ B.fv (B.Term.lambda vs D P),
      (Xi v).isSome = true)
    (tau_hasArity : tau.hasArity vs.length)
    {Dval : ZFSet.{u}} {hDval : Dval ∈ ⟦BType.set tau⟧ᶻ}
    (den_D : ⟦D.abstract Xi
      (fun v hv => Xi_fv v (B.fv.mem_lambda (.inl hv)))⟧ᴮ =
      some (⟨Dval, BType.set tau, hDval⟩ : B.Dom))
    {T : ZFSet.{u}} {hT : T ∈ ⟦BType.set (tau ×ᴮ beta)⟧ᶻ}
    (den_lambda : ⟦(B.Term.lambda vs D P).abstract Xi Xi_fv⟧ᴮ =
      some (⟨T, BType.set (tau ×ᴮ beta), hT⟩ : B.Dom))
    {x p : ZFSet.{u}} (hx : x ∈ ⟦tau⟧ᶻ) (hp : p ∈ ⟦beta⟧ᶻ)
    (hmem : x.pair p ∈ T) : x ∈ Dval := by
  rw [← B.denote_lambda_eq_sep Xi_fv tau_hasArity den_D den_lambda,
    ZFSet.mem_sep] at hmem
  have hgraph := hmem.2
  have hx_arity := hasArity_of_mem_toZFSet tau_hasArity hx
  rw [dif_pos ZFSet.isTuple_pair, ZFSet.π₁_pair, ZFSet.π₂_pair] at hgraph
  by_contra hxD
  rw [dif_neg (fun h => hxD h.2)] at hgraph
  exact hgraph

/- Lift the pointwise represented lambda-body correspondence to the whole
graph set.  The backward direction deliberately evaluates the pointwise
bridge twice: the first evaluation discovers the represented result, and the
second installs that result as the target pair's second component.  Both
results represent the same deterministic source value, so representation
injectivity identifies them. -/
open Classical in
theorem represented_lambda_set_of_pointwise.{u}
    {tau beta : BType} {sigma gamma : SMTType}
    (hsigma : BType.SupportedSMT tau sigma)
    (hgamma : BType.SupportedSMT beta gamma)
    {Dval T : ZFSet.{u}}
    (hDsub : Dval ⊆ ⟦tau⟧ᶻ)
    (hTsub : T ⊆ ⟦tau ×ᴮ beta⟧ᶻ)
    {Theta : SMT.RenamingContext.Context.{u}} {z : SMT.𝒱}
    {body : SMT.Term} {lamVal : SMT.Dom.{u}}
    (hcov_lambda : SMT.RenamingContext.CoversFV Theta
      ((λˢ [z]) [sigma.pair gamma] body))
    (hden_lambda : ⟦((λˢ [z]) [sigma.pair gamma] body).abstract
      Theta hcov_lambda⟧ˢ = some lamVal)
    (hlam_type : lamVal.snd.fst =
      SMTType.fun (sigma.pair gamma) SMTType.bool)
    (hcov_body_upd : ∀ W : SMT.Dom.{u},
      SMT.RenamingContext.CoversFV
        (Function.update Theta z (some W)) body)
    (hbody_total : ∀ W : SMT.Dom.{u},
      W.snd.fst = sigma.pair gamma →
      ∃ bodyVal : SMT.Dom.{u},
        ⟦body.abstract (Function.update Theta z (some W))
          (hcov_body_upd W)⟧ˢ = some bodyVal)
    (htarget_domain : ∀ {Wy Wp : SMT.Dom.{u}},
      (hWy_type : Wy.snd.fst = sigma) →
      (hWp_type : Wp.snd.fst = gamma) →
      let Wxy : SMT.Dom.{u} :=
        ⟨Wy.fst.pair Wp.fst, sigma.pair gamma,
          ZFSet.pair_mem_prod.mpr ⟨by
            rw [← hWy_type]
            exact Wy.snd.snd, by
            rw [← hWp_type]
            exact Wp.snd.snd⟩⟩
      ∀ bodyVal : SMT.Dom.{u},
        ⟦body.abstract (Function.update Theta z (some Wxy))
          (hcov_body_upd Wxy)⟧ˢ = some bodyVal →
        bodyVal.fst = ZFSet.zftrue →
        ∃ (x : ZFSet.{u}) (hx : x ∈ ⟦tau⟧ᶻ), x ∈ Dval ∧
          RDomCastSupported (⟨x, tau, hx⟩ : B.Dom) Wy)
    (hsource_preimage : ∀ (x : ZFSet.{u}) (hx : x ∈ ⟦tau⟧ᶻ),
      x ∈ Dval →
      ∃ (y : ZFSet.{u}) (hy : y ∈ ⟦sigma⟧ᶻ),
        RDomCastSupported (⟨x, tau, hx⟩ : B.Dom)
          (⟨y, sigma, hy⟩ : SMT.Dom))
    (hsource_domain : ∀ (x p : ZFSet.{u})
      (hx : x ∈ ⟦tau⟧ᶻ) (hp : p ∈ ⟦beta⟧ᶻ),
      x.pair p ∈ T → x ∈ Dval)
    (hpoint : ∀ {x : ZFSet.{u}} (hx : x ∈ ⟦tau⟧ᶻ),
      x ∈ Dval → ∀ {Wy Wp : SMT.Dom.{u}},
      (hWy_type : Wy.snd.fst = sigma) →
      RDomCastSupported (⟨x, tau, hx⟩ : B.Dom) Wy →
      (hWp_type : Wp.snd.fst = gamma) →
      let Wxy : SMT.Dom.{u} :=
        ⟨Wy.fst.pair Wp.fst, sigma.pair gamma,
          ZFSet.pair_mem_prod.mpr ⟨by
            rw [← hWy_type]
            exact Wy.snd.snd, by
            rw [← hWp_type]
            exact Wp.snd.snd⟩⟩
      ∃ (Pval : ZFSet.{u}) (hPval : Pval ∈ ⟦beta⟧ᶻ)
        (dP : SMT.Dom.{u}),
        (∀ (p : ZFSet.{u}) (hp : p ∈ ⟦beta⟧ᶻ),
          x.pair p ∈ T ↔ Pval = p) ∧
        dP.snd.fst = gamma ∧
        RDomCastSupported (⟨Pval, beta, hPval⟩ : B.Dom) dP ∧
        ∀ bodyVal : SMT.Dom.{u},
          ⟦body.abstract (Function.update Theta z (some Wxy))
            (hcov_body_upd Wxy)⟧ˢ = some bodyVal →
          (bodyVal.fst = ZFSet.zftrue ↔ Wp.fst = dP.fst)) :
    RDomCastSupported
      (⟨T, BType.set (tau ×ᴮ beta),
        ZFSet.mem_powerset.mpr hTsub⟩ : B.Dom) lamVal := by
  apply represented_setPred_lambda_of_pointwise
    (.prod hsigma hgamma) hTsub hcov_lambda hden_lambda hlam_type
  · intro y hy
    let W : SMT.Dom.{u} := ⟨y, sigma.pair gamma, hy⟩
    obtain ⟨bodyVal, hden_body⟩ := hbody_total W rfl
    exact ⟨hcov_body_upd W, bodyVal, hden_body⟩
  · intro y hy hcov_body bodyVal hden_body hbody_true
    obtain ⟨wy, hwy, wp, hwp, rfl⟩ := ZFSet.mem_prod.mp hy
    let Wy : SMT.Dom.{u} := ⟨wy, sigma, hwy⟩
    let Wp : SMT.Dom.{u} := ⟨wp, gamma, hwp⟩
    let Wxy : SMT.Dom.{u} :=
      ⟨wy.pair wp, sigma.pair gamma,
        ZFSet.pair_mem_prod.mpr ⟨hwy, hwp⟩⟩
    have hden_body' :
        ⟦body.abstract (Function.update Theta z (some Wxy))
          (hcov_body_upd Wxy)⟧ˢ = some bodyVal := by
      simpa only [Wxy, proof_irrel_heq] using hden_body
    obtain ⟨x, hx, hxD, hrel_x⟩ :=
      htarget_domain (Wy := Wy) (Wp := Wp) rfl rfl
        bodyVal hden_body' hbody_true
    obtain ⟨Pval, hPval, dP, hgraph, hdP_type, hrel_P, htruth⟩ :=
      hpoint hx hxD (Wy := Wy) (Wp := Wp) rfl hrel_x rfl
    have hWp_eq : wp = dP.fst :=
      (htruth bodyVal hden_body').mp hbody_true
    subst wp
    have hmem : x.pair Pval ∈ T := (hgraph Pval hPval).mpr rfl
    refine ⟨x.pair Pval, hmem, ?_⟩
    have hpair := RDomCastSupported.pair hrel_x hrel_P
    simpa only [Wy, Wp, hdP_type, proof_irrel_heq] using hpair
  · intro xy hxy
    obtain ⟨x, hx, p, hp, rfl⟩ := ZFSet.mem_prod.mp (hTsub hxy)
    have hxD : x ∈ Dval := hsource_domain x p hx hp hxy
    obtain ⟨wy, hwy, hrel_x⟩ := hsource_preimage x hx hxD
    let Wy : SMT.Dom.{u} := ⟨wy, sigma, hwy⟩
    let Wp0 : SMT.Dom.{u} :=
      ⟨gamma.defaultZFSet, gamma,
        SMTType.mem_toZFSet_of_defaultZFSet⟩
    obtain ⟨Pval, hPval, dP, hgraph, hdP_type, hrel_P, _⟩ :=
      hpoint hx hxD (Wy := Wy) (Wp := Wp0) rfl hrel_x rfl
    have hPval_eq : Pval = p := (hgraph p hp).mp hxy
    subst Pval
    rcases dP with ⟨dp, dPType, hdp⟩
    dsimp at hdP_type
    subst dPType
    let Wp : SMT.Dom.{u} := ⟨dp, gamma, hdp⟩
    obtain ⟨Pval2, hPval2, dP2, hgraph2, hdP2_type, hrel_P2,
      htruth2⟩ :=
      hpoint hx hxD (Wy := Wy) (Wp := Wp) rfl hrel_x rfl
    have hPval2_eq : Pval2 = p := (hgraph2 p hp).mp hxy
    rcases dP2 with ⟨dp2, dP2Type, hdp2⟩
    dsimp at hdP2_type
    subst dP2Type
    have hdp_eq : dp = dp2 :=
      (RDomCast.target_value_eq_iff hrel_P.toRDomCast
        hrel_P2.toRDomCast).mpr hPval2_eq.symm
    let Wxy : SMT.Dom.{u} :=
      ⟨wy.pair dp, sigma.pair gamma,
        ZFSet.pair_mem_prod.mpr ⟨hwy, hdp⟩⟩
    obtain ⟨bodyVal, hden_body⟩ := hbody_total Wxy rfl
    have hbody_true : bodyVal.fst = ZFSet.zftrue :=
      (htruth2 bodyVal (by
        simpa only [Wxy, Wy, Wp, proof_irrel_heq] using hden_body)).mpr
        hdp_eq
    refine ⟨wy.pair dp, ZFSet.pair_mem_prod.mpr ⟨hwy, hdp⟩,
      ?_, hcov_body_upd Wxy, bodyVal, ?_, hbody_true⟩
    · have hrel_P' : RDomCastSupported
          (⟨p, beta, hp⟩ : B.Dom) (⟨dp, gamma, hdp⟩ : SMT.Dom) := by
        simpa only [proof_irrel_heq] using hrel_P
      have hpair := RDomCastSupported.pair hrel_x hrel_P'
      simpa only [Wy, Wxy, proof_irrel_heq] using hpair
    · simpa only [Wxy, proof_irrel_heq] using hden_body

/- Semantic representation theorem for the lambda emitted by `encodeTerm`.
The operational case theorem only has to supply typing, coverage, freshness,
and the body induction hypothesis; all graph reasoning is discharged here. -/
open Classical in
theorem represented_lambda_of_total_body.{u}
    {vs : List B.𝒱} (vs_nemp : vs ≠ []) (vs_nodup : vs.Nodup)
    {D P : B.Term} {tau beta : BType}
    {Xi : B.RenamingContext.Context.{u}}
    (Xi_fv : ∀ v ∈ B.fv (B.Term.lambda vs D P),
      (Xi v).isSome = true)
    (tau_hasArity : tau.hasArity vs.length)
    {Dval : ZFSet.{u}} {hDval : Dval ∈ ⟦BType.set tau⟧ᶻ}
    (den_D : ⟦D.abstract Xi
      (fun v hv => Xi_fv v (B.fv.mem_lambda (.inl hv)))⟧ᴮ =
      some (⟨Dval, BType.set tau, hDval⟩ : B.Dom))
    {T : ZFSet.{u}} {hT : T ∈ ⟦BType.set (tau ×ᴮ beta)⟧ᶻ}
    (den_lambda : ⟦(B.Term.lambda vs D P).abstract Xi Xi_fv⟧ᴮ =
      some (⟨T, BType.set (tau ×ᴮ beta), hT⟩ : B.Dom))
    {sigma gamma : SMTType}
    (hsigma : BType.SupportedSMT tau sigma)
    (hgamma : BType.SupportedSMT beta gamma)
    {Denc Penc body : SMT.Term} {z : SMT.𝒱}
    {ThetaD : SMT.RenamingContext.Context.{u}}
    {DencVal lamVal : SMT.Dom.{u}}
    (body_def : body = SMT.Term.and
      (SMT.Term.app Denc (SMT.Term.fst (SMT.Term.var z)))
      (SMT.Term.eq (SMT.Term.snd (SMT.Term.var z))
        (SMT.substList vs
          (toDestPair vs (SMT.Term.fst (SMT.Term.var z))) Penc)))
    (hcov_lambda : SMT.RenamingContext.CoversFV ThetaD
      ((λˢ [z]) [sigma.pair gamma] body))
    (hden_target_lambda :
      ⟦((λˢ [z]) [sigma.pair gamma] body).abstract
        ThetaD hcov_lambda⟧ˢ = some lamVal)
    (hlam_type : lamVal.snd.fst =
      SMTType.fun (sigma.pair gamma) SMTType.bool)
    (hcov_D_upd : ∀ W : SMT.Dom.{u},
      SMT.RenamingContext.CoversFV
        (Function.update ThetaD z (some W)) Denc)
    (den_D_upd : ∀ W : SMT.Dom.{u},
      ⟦Denc.abstract (Function.update ThetaD z (some W))
        (hcov_D_upd W)⟧ˢ = some DencVal)
    (hDenc_type : DencVal.snd.fst = sigma.fun SMTType.bool)
    (hDenc_func : ⟦sigma⟧ᶻ.IsFunc ZFSet.𝔹 DencVal.fst)
    (D_rel : RDomCastSupported
      (⟨Dval, BType.set tau, hDval⟩ : B.Dom) DencVal)
    (hcov_body_upd : ∀ W : SMT.Dom.{u},
      SMT.RenamingContext.CoversFV
        (Function.update ThetaD z (some W)) body)
    (hbody_total : ∀ W : SMT.Dom.{u},
      W.snd.fst = sigma.pair gamma →
      ∃ bodyVal : SMT.Dom.{u},
        ⟦body.abstract (Function.update ThetaD z (some W))
          (hcov_body_upd W)⟧ˢ = some bodyVal)
    (hcov_sub_upd : ∀ W : SMT.Dom.{u},
      SMT.RenamingContext.CoversFV
        (Function.update ThetaD z (some W))
        (SMT.substList vs
          (toDestPair vs (SMT.Term.fst (SMT.Term.var z))) Penc))
    (hcov_P_upd : ∀ (W : SMT.Dom.{u})
      (ss : Fin vs.length → SMT.Dom.{u}),
      SMT.RenamingContext.CoversFV
        (Function.updates (Function.update ThetaD z (some W)) vs
          ((List.ofFn ss).map Option.some)) Penc)
    (hvs_not_bv : ∀ v ∈ vs, v ∉ SMT.bv Penc)
    (hz_not_bv : z ∉ SMT.bv Penc) (hz_not_vs : z ∉ vs)
    {Ebody : B.Env} {LambdaP GammaP : SMT.TypeContext}
    {usedP : List SMT.𝒱}
    (typ_P : Ebody.context ⊢ᴮ P : beta)
    (P_total : EncodeTermRepTotal.{u}
      P Ebody beta LambdaP Penc gamma GammaP usedP)
    (ambient : ∀ v ∈ B.fv P, v ∉ vs →
      match Xi v, ThetaD v with
      | some source, some target => RDomCastSupported source target
      | _, _ => False)
    (wf_bound : ∀ (x : ZFSet.{u}) (hx : x ∈ ⟦tau⟧ᶻ)
      (_hx_D : x ∈ Dval),
      B.RenWF Ebody.context
        (Function.updates Xi vs (List.ofFn fun i => some
          (⟨x.get vs.length i, tau.get vs.length i,
            get_mem_type_of_isTuple
              (hasArity_of_mem_toZFSet tau_hasArity hx)
              tau_hasArity hx⟩ : B.Dom))))
    (bound_expected : ∀ i : Fin vs.length,
      LambdaP.lookup vs[i] =
        some ((sigma.fromProdl (vs.length - 1))[i.val]'(by
          have hlen := hsigma.fromProdl_length_of_hasArity tau_hasArity
          exact i.isLt.trans_eq hlen.symm)))
    (source_respects : ∀ ss : Fin vs.length → SMT.Dom.{u},
      (∀ i, LambdaP.lookup vs[i] = some (ss i).snd.fst) →
      B.RenamingContext.RespectsTypeContextOnFV
        (Function.updates ThetaD vs
          ((List.ofFn ss).map Option.some)) LambdaP P)
    (source_fv_in_LambdaP : ∀ v ∈ B.fv P, v ∈ LambdaP)
    (Penc_fv_in_LambdaP : ∀ v ∈ SMT.fv Penc, v ∈ LambdaP)
    (LambdaP_keys_used : LambdaP.keys ⊆ usedP)
    (hPenc_fv : SMT.fv Penc ⊆ B.Term.vars P)
    (z_not_vars_P : z ∉ B.Term.vars P) :
    RDomCastSupported
      (⟨T, BType.set (tau ×ᴮ beta), hT⟩ : B.Dom) lamVal := by
  have hDsub : Dval ⊆ ⟦tau⟧ᶻ := by
    simpa [BType.toZFSet] using ZFSet.mem_powerset.mp hDval
  have hTsub : T ⊆ ⟦tau ×ᴮ beta⟧ᶻ := by
    simpa [BType.toZFSet] using ZFSet.mem_powerset.mp hT
  let DencVal' : SMT.Dom.{u} :=
    ⟨DencVal.fst, sigma.fun SMTType.bool, by
      rw [← hDenc_type]
      exact DencVal.snd.snd⟩
  have hDencVal_eq : DencVal = DencVal' := by
    exact SMT.RenamingContext.Dom_ext' rfl hDenc_type
  have D_rel' : RDomCastSupported
      (⟨Dval, BType.set tau, hDval⟩ : B.Dom) DencVal' := by
    simpa only [hDencVal_eq] using D_rel
  apply represented_lambda_set_of_pointwise hsigma hgamma hDsub hTsub
    hcov_lambda hden_target_lambda hlam_type hcov_body_upd hbody_total
  · intro Wy Wp hWy_type hWp_type
    dsimp only
    have hWy_mem : Wy.fst ∈ ⟦sigma⟧ᶻ := by
      rw [← hWy_type]
      exact Wy.snd.snd
    have hWp_mem : Wp.fst ∈ ⟦gamma⟧ᶻ := by
      rw [← hWp_type]
      exact Wp.snd.snd
    let Wxy : SMT.Dom.{u} :=
      ⟨Wy.fst.pair Wp.fst, sigma.pair gamma,
        ZFSet.pair_mem_prod.mpr ⟨hWy_mem, hWp_mem⟩⟩
    intro bodyVal hden_body hbody_true
    obtain ⟨hcov_Dapp, Dapp, hDapp_type, hDapp_value, hden_Dapp⟩ :=
      funDenoteAppAtFst (Δctx := ThetaD) (t := Denc) (x := z)
        (α := sigma) (β := SMTType.bool) (γ := gamma)
        (Y := DencVal) hcov_D_upd den_D_upd hDenc_type hDenc_func
        Wxy rfl Wxy.snd.snd
    have hcov_snd : SMT.RenamingContext.CoversFV
        (Function.update ThetaD z (some Wxy)) (.snd (.var z)) := by
      intro v hv
      simp only [SMT.fv, List.mem_singleton] at hv
      subst v
      simp
    have hbody_abs : body.abstract
        (Function.update ThetaD z (some Wxy)) (hcov_body_upd Wxy) =
        ((SMT.Term.app Denc (.fst (.var z))).abstract
          (Function.update ThetaD z (some Wxy)) hcov_Dapp ∧ˢ'
        ((SMT.Term.snd (.var z)).abstract
          (Function.update ThetaD z (some Wxy)) hcov_snd =ˢ'
        (SMT.substList vs (toDestPair vs (.fst (.var z))) Penc).abstract
          (Function.update ThetaD z (some Wxy))
          (hcov_sub_upd Wxy))) := by
      subst body
      simp only [SMT.Term.abstract]
    have hDapp_true := lambda_and_truth_implies_left_true
      hden_Dapp hDapp_type hbody_abs hden_body hbody_true
    have happ_true := hDapp_value.symm.trans hDapp_true
    obtain ⟨x, hxD, hrel_x⟩ :=
      RDomCastSupported.setPred_target_of_true D_rel' hWy_mem (by
        simpa only [DencVal', Wxy, ZFSet.π₁_pair, proof_irrel_heq]
          using happ_true)
    refine ⟨x, hDsub hxD, hxD, ?_⟩
    have hWy_eq : Wy = (⟨Wy.fst, sigma, hWy_mem⟩ : SMT.Dom) :=
      SMT.RenamingContext.Dom_ext' rfl hWy_type
    rw [hWy_eq]
    simpa only [proof_irrel_heq] using hrel_x
  · intro x hx hxD
    obtain ⟨y, hy, hrel⟩ :=
      RDomCastSupported.setPred_member_preimage D_rel' hxD
    refine ⟨y, hy, ?_⟩
    simpa only [proof_irrel_heq] using hrel
  · intro x p hx hp hmem
    exact B.denote_lambda_member_domain Xi_fv tau_hasArity den_D
      den_lambda hx hp hmem
  · intro x hx hxD Wy Wp hWy_type hrel_x hWp_type
    dsimp only
    have hWy_mem : Wy.fst ∈ ⟦sigma⟧ᶻ := by
      rw [← hWy_type]
      exact Wy.snd.snd
    have hWp_mem : Wp.fst ∈ ⟦gamma⟧ᶻ := by
      rw [← hWp_type]
      exact Wp.snd.snd
    obtain ⟨XiP_fv, Pval, hPval, dP, den_P, hden_Psub,
      hdP_type, hrel_P, htruth⟩ :=
      represented_lambda_body_at_domain
        (D := D) (P := P) (tau := tau) (beta := beta) (Xi := Xi)
        (Dval := Dval) (T := T) (sigma := sigma) (gamma := gamma)
        (Denc := Denc) (Penc := Penc) (body := body) (z := z)
        (ThetaD := ThetaD) (DencVal := DencVal)
        (Ebody := Ebody) (LambdaP := LambdaP) (GammaP := GammaP)
        (usedP := usedP) vs_nemp vs_nodup Xi_fv tau_hasArity den_D
        den_lambda hsigma body_def hcov_D_upd den_D_upd hDenc_type
        hDenc_func D_rel hcov_body_upd hcov_sub_upd hcov_P_upd
        hvs_not_bv hz_not_bv hz_not_vs typ_P P_total ambient wf_bound
        bound_expected source_respects source_fv_in_LambdaP
        Penc_fv_in_LambdaP LambdaP_keys_used hPenc_fv z_not_vars_P
        hx hxD hWy_type hWy_mem hrel_x
        hWp_type hWp_mem
    let x_fin : Fin vs.length → B.Dom.{u} := fun i =>
      ⟨x.get vs.length i, tau.get vs.length i,
        get_mem_type_of_isTuple
          (hasArity_of_mem_toZFSet tau_hasArity hx)
          tau_hasArity hx⟩
    have den_P_go :
        ⟦(B.Term.abstract.go P vs Xi (fun v hv hvs => Xi_fv v
          (B.fv.mem_lambda (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ =
          some (⟨Pval, beta, hPval⟩ : B.Dom) := by
      rw [denote_term_abstract_go_eq_term_abstract
        vs_nodup vs_nemp x_fin XiP_fv]
      simpa only [x_fin, proof_irrel_heq] using den_P
    have hx_arity := hasArity_of_mem_toZFSet tau_hasArity hx
    refine ⟨Pval, hPval, dP, ?_, hdP_type, hrel_P, htruth⟩
    intro p hp
    have hiff := B.denote_lambda_member_iff Xi_fv tau_hasArity den_D
      den_lambda hx_arity hx hp hPval den_P_go
    simpa only [hxD, true_and] using hiff

/- The body induction hypothesis needs one successful source evaluation before
its alternative-valuation clause becomes available.  Source lambda semantics
provides such a seed from a chosen member in the nonempty branch and from the
canonical default tuple in the empty branch. -/
open Classical in
theorem B.denote_lambda_seed_body_exists.{u}
    {vs : List B.𝒱} {D P : B.Term} {tau beta : BType}
    {Xi : B.RenamingContext.Context.{u}}
    (Xi_fv : ∀ v ∈ B.fv (B.Term.lambda vs D P),
      (Xi v).isSome = true)
    (vs_nemp : vs ≠ []) (vs_nodup : vs.Nodup)
    (tau_hasArity : tau.hasArity vs.length)
    {Dval : ZFSet.{u}} {hDval : Dval ∈ ⟦BType.set tau⟧ᶻ}
    (den_D : ⟦D.abstract Xi
      (fun v hv => Xi_fv v (B.fv.mem_lambda (.inl hv)))⟧ᴮ =
      some (⟨Dval, BType.set tau, hDval⟩ : B.Dom))
    {T : ZFSet.{u}} {hT : T ∈ ⟦BType.set (tau ×ᴮ beta)⟧ᶻ}
    (den_lambda : ⟦(B.Term.lambda vs D P).abstract Xi Xi_fv⟧ᴮ =
      some (⟨T, BType.set (tau ×ᴮ beta), hT⟩ : B.Dom))
    {Ectx : B.TypeContext} (typ_P : Ectx ⊢ᴮ P : beta)
    (wf_P : ∀ (x_fin : Fin vs.length → B.Dom.{u}),
      (∀ i, (x_fin i).snd.fst = tau.get vs.length i) →
      B.RenWF Ectx (Function.updates Xi vs
        (List.ofFn fun i => some (x_fin i)))) :
    ∃ (x : ZFSet.{u}) (hx : x ∈ ⟦tau⟧ᶻ),
      (x ∈ Dval ∨ x = tau.defaultZFSet) ∧
      let x_fin : Fin vs.length → B.Dom.{u} := fun i =>
        ⟨x.get vs.length i, tau.get vs.length i,
          get_mem_type_of_isTuple
            (hasArity_of_mem_toZFSet tau_hasArity hx)
            tau_hasArity hx⟩
      ∃ (XiP_fv : ∀ v ∈ B.fv P,
          (Function.updates Xi vs
            (List.ofFn fun i => some (x_fin i)) v).isSome = true)
        (Pval : ZFSet.{u}) (hPval : Pval ∈ ⟦beta⟧ᶻ),
        ⟦P.abstract (Function.updates Xi vs
          (List.ofFn fun i => some (x_fin i))) XiP_fv⟧ᴮ =
          some (⟨Pval, beta, hPval⟩ : B.Dom) := by
  have h_inv := den_lambda
  simp only [B.Term.abstract] at h_inv
  unfold B.denote at h_inv
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h_inv
  obtain ⟨D_dom, hden_d, rest⟩ := h_inv
  have hconv_d : ⟦D.abstract Xi
      (fun v hv => Xi_fv v (B.fv.mem_lambda (.inl hv)))⟧ᴮ =
      some D_dom := by
    convert hden_d using 2
  have hD_dom_eq : D_dom =
      (⟨Dval, BType.set tau, hDval⟩ : B.Dom) := by
    rw [hconv_d] at den_D
    exact Option.some.inj den_D
  subst D_dom
  simp only at rest
  rw [dif_pos tau_hasArity] at rest
  split_ifs at rest with h_den_P h_typP_det h_nemp h_chosen_arity
    h_default_arity
  · let x_choose :=
      Classical.choose (ZFSet.nonempty_exists_iff.mp h_nemp)
    have hx_choose_mem : x_choose ∈ Dval :=
      Classical.choose_spec (ZFSet.nonempty_exists_iff.mp h_nemp)
    let x_fin : Fin vs.length → B.Dom := fun i =>
      ⟨x_choose.get vs.length i,
        tau.get vs.length i,
        get_mem_type_of_isTuple h_chosen_arity.1 tau_hasArity
          h_chosen_arity.2⟩
    have hx_typ : ∀ i, (x_fin i).snd.fst = tau.get vs.length i ∧
        (x_fin i).fst ∈ ⟦tau.get vs.length i⟧ᶻ :=
      fun i => ⟨rfl, (x_fin i).snd.snd⟩
    have XiP_fv : ∀ v ∈ B.fv P,
        (Function.updates Xi vs
          (List.ofFn fun i => some (x_fin i)) v).isSome = true := by
      intro v hv
      rw [Function.updates_eq_if (by simp) vs_nodup]
      split_ifs with hvs
      · simp
      · exact Xi_fv v (B.fv.mem_lambda (.inr ⟨hv, hvs⟩))
    rw [denote_term_abstract_go_eq_term_abstract vs_nodup vs_nemp x_fin
      XiP_fv, Option.bind_eq_some_iff] at rest
    obtain ⟨⟨Pval, P_ty, hPval⟩, hden, hout⟩ := rest
    have hP_ty : P_ty = beta :=
      (denote_welltyped_eq
        (t := P.abstract (Function.updates Xi vs
          (List.ofFn fun i => some (x_fin i))) XiP_fv)
        ⟨_, WFTC.of_abstract, beta,
          Typing.of_abstract XiP_fv typ_P
            (wf_P x_fin (fun i => (hx_typ i).1))⟩ hden).symm
    subst P_ty
    exact ⟨x_choose, h_chosen_arity.2, Or.inl hx_choose_mem,
      XiP_fv, Pval, hPval, hden⟩
  · let x_fin : Fin vs.length → B.Dom := fun i =>
      ⟨tau.defaultZFSet.get vs.length i, tau.get vs.length i,
        get_mem_type_of_isTuple h_default_arity.1 tau_hasArity
          BType.mem_toZFSet_of_defaultZFSet⟩
    have hx_typ : ∀ i, (x_fin i).snd.fst = tau.get vs.length i ∧
        (x_fin i).fst ∈ ⟦tau.get vs.length i⟧ᶻ :=
      fun i => ⟨rfl, (x_fin i).snd.snd⟩
    have XiP_fv : ∀ v ∈ B.fv P,
        (Function.updates Xi vs
          (List.ofFn fun i => some (x_fin i)) v).isSome = true := by
      intro v hv
      rw [Function.updates_eq_if (by simp) vs_nodup]
      split_ifs with hvs
      · simp
      · exact Xi_fv v (B.fv.mem_lambda (.inr ⟨hv, hvs⟩))
    rw [denote_term_abstract_go_eq_term_abstract vs_nodup vs_nemp x_fin
      XiP_fv, Option.bind_eq_some_iff] at rest
    obtain ⟨⟨Pval, P_ty, hPval⟩, hden, hout⟩ := rest
    have hP_ty : P_ty = beta :=
      (denote_welltyped_eq
        (t := P.abstract (Function.updates Xi vs
          (List.ofFn fun i => some (x_fin i))) XiP_fv)
        ⟨_, WFTC.of_abstract, beta,
          Typing.of_abstract XiP_fv typ_P
            (wf_P x_fin (fun i => (hx_typ i).1))⟩ hden).symm
    subst P_ty
    exact ⟨tau.defaultZFSet, BType.mem_toZFSet_of_defaultZFSet,
      Or.inr rfl, XiP_fv, Pval, hPval, hden⟩
