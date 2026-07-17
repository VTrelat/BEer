import SMT.Reasoning.Basic.EncodeTermRepresentedScopedEq
import SMT.Reasoning.Basic.EncodeTermCorrectPFun

open Std.Do B SMT ZFSet Classical

/-! # Representation-aware function application -/

namespace ZFSet.Option

/-- Eliminating a present ZF option returns its payload. -/
theorem the_some.{u} {S : ZFSet.{u}} (S_nemp : S ≠ ∅)
    (z : {x // x ∈ S}) :
    the S_nemp (some z) = z := by
  unfold the
  rw [dif_neg (some_ne_none z)]
  have hspec := Classical.choose_spec
    (Or.resolve_left (casesOn (some z)) (some_ne_none z))
  rw [some.injEq] at hspec
  exact hspec.symm

end ZFSet.Option

/-- A supported target reachable by casting from the canonical
representation is itself canonical.  The representation grammar only adds
option-functions in the opposite direction (option-function to graph). -/
theorem BType.SupportedSMT.eq_canonical_of_cast_from_canonical
    {tau : BType} {sigma : SMTType}
    (hs : BType.SupportedSMT tau sigma)
    (c : tau.toSMTType ~> sigma) : sigma = tau.toSMTType := by
  induction hs with
  | int => rfl
  | bool => rfl
  | prod hs1 hs2 ih1 ih2 =>
      cases c with
      | pair c1 c2 =>
          rw [ih1 c1, ih2 c2]
          rfl
      | refl h => rcases h with h | h | h <;> nomatch h
  | setPred => rfl
  | optionFun =>
      have hcod := castable?_of_fun_bool (castable?_of_castPath c)
      nomatch hcod

/-- Invert a successful source application into its graph, argument, partial
function witness, domain witness, and selected result. -/
theorem B.denote_app_inv_rep.{u}
    {E : B.Env} {f x : B.Term} {gamma alpha : BType}
    (typ_f : E.context ⊢ᴮ f : BType.set (gamma ×ᴮ alpha))
    (typ_x : E.context ⊢ᴮ x : gamma)
    {Xi : B.RenamingContext.Context}
    (Xi_fv : ∀ v ∈ B.fv (.app f x), (Xi v).isSome = true)
    (wf : B.RenWF E.context Xi)
    {T : ZFSet.{u}} {hT : T ∈ ⟦alpha⟧ᶻ}
    (hden : ⟦(B.Term.app f x).abstract Xi Xi_fv⟧ᴮ =
      some ⟨T, alpha, hT⟩) :
    ∃ (F X : ZFSet.{u})
      (hF : F ∈ ⟦BType.set (gamma ×ᴮ alpha)⟧ᶻ)
      (hX : X ∈ ⟦gamma⟧ᶻ),
      ⟦f.abstract Xi (fun v hv => Xi_fv v (by
        rw [B.fv, List.mem_append]
        exact Or.inl hv))⟧ᴮ =
          some ⟨F, BType.set (gamma ×ᴮ alpha), hF⟩ ∧
      ⟦x.abstract Xi (fun v hv => Xi_fv v (by
        rw [B.fv, List.mem_append]
        exact Or.inr hv))⟧ᴮ = some ⟨X, gamma, hX⟩ ∧
      ∃ (hfun : F.IsPFunc ⟦gamma⟧ᶻ ⟦alpha⟧ᶻ)
        (hdom : X ∈ F.Dom),
        (fapply F hfun ⟨X, hdom⟩).val = T := by
  rw [B.Term.abstract, B.denote, Option.pure_def,
    Option.bind_eq_bind, Option.bind_eq_some_iff] at hden
  obtain ⟨⟨F, tauF, hF⟩, hdenF, hrest⟩ := hden
  have htauF := denote_welltyped_eq
    (t := f.abstract Xi (fun v hv => Xi_fv v (by
      rw [B.fv, List.mem_append]
      exact Or.inl hv))) ?_ hdenF
  on_goal 2 =>
    use E.context.abstract («Δ» := Xi), WFTC.of_abstract,
      BType.set (gamma ×ᴮ alpha)
    exact Typing.of_abstract _ typ_f wf
  dsimp at htauF
  subst tauF
  rw [Option.bind_eq_some_iff] at hrest
  obtain ⟨⟨X, tauX, hX⟩, hdenX, hout⟩ := hrest
  have htauX := denote_welltyped_eq
    (t := x.abstract Xi (fun v hv => Xi_fv v (by
      rw [B.fv, List.mem_append]
      exact Or.inr hv))) ?_ hdenX
  on_goal 2 =>
    use E.context.abstract («Δ» := Xi), WFTC.of_abstract, gamma
    exact Typing.of_abstract _ typ_x wf
  dsimp at htauX
  subst tauX
  dsimp at hout
  rw [if_pos rfl] at hout
  split_ifs at hout with hfun hdom
  · rw [Option.some_inj] at hout
    obtain ⟨⟩ := hout
    exact ⟨F, X, hF, hX, hdenF, hdenX, hfun, hdom, rfl⟩

/-- Materializing the canonical cast of a supported representative produces a
canonical supported representative of the same source value. -/
theorem RDomCastSupported.of_cast_to_canonical.{u}
    {tau : BType} {sigma : SMTType} {X Y0 Y : ZFSet.{u}}
    {hX : X ∈ ⟦tau⟧ᶻ} {hY0 : Y0 ∈ ⟦sigma⟧ᶻ}
    {hY : Y ∈ ⟦tau.toSMTType⟧ᶻ}
    (rel : RDomCastSupported (⟨X, tau, hX⟩ : B.Dom)
      (⟨Y0, sigma, hY0⟩ : SMT.Dom))
    (c : sigma ~> tau.toSMTType)
    (hpair : Y0.pair Y ∈ (castZF_of_path c).1) :
    RDomCastSupported (⟨X, tau, hX⟩ : B.Dom)
      (⟨Y, tau.toSMTType, hY⟩ : SMT.Dom) := by
  obtain ⟨c0, hret⟩ := rel.toRDomCast
  rw [castPath.eq_of_endpoints c0 c] at hret
  have hcast : castZF_apply c Y0 = Y :=
    castZF_apply_eq_of_pair c hY0 hpair
  apply RDom.toRDomCastSupported
  rw [RDom]
  refine ⟨rfl, ?_⟩
  rw [← hcast]
  exact hret

/-- Applying an option-function representative at a canonical representative
of the source argument returns `some` of any canonical representative of the
source result, provided the corresponding pair belongs to the source graph.

The proof deliberately reuses represented membership: equality with
`some Z` is true exactly when `(X, T)` belongs to the represented source
relation. -/
theorem RDomCast.optionFunction_apply_some_of_mem.{u}
    {gamma alpha : BType} {F X T G Y Z : ZFSet.{u}}
    {hF : F ∈ ⟦BType.set (gamma ×ᴮ alpha)⟧ᶻ}
    {hX : X ∈ ⟦gamma⟧ᶻ} {hT : T ∈ ⟦alpha⟧ᶻ}
    {hG : G ∈ ⟦SMTType.fun gamma.toSMTType
      (SMTType.option alpha.toSMTType)⟧ᶻ}
    {hY : Y ∈ ⟦gamma.toSMTType⟧ᶻ}
    {hZ : Z ∈ ⟦alpha.toSMTType⟧ᶻ}
    (Frel : RDomCast
      (⟨F, BType.set (gamma ×ᴮ alpha), hF⟩ : B.Dom)
      (⟨G, SMTType.fun gamma.toSMTType
        (SMTType.option alpha.toSMTType), hG⟩ : SMT.Dom))
    (Xrel : RDomCast (⟨X, gamma, hX⟩ : B.Dom)
      (⟨Y, gamma.toSMTType, hY⟩ : SMT.Dom))
    (hZret : retract alpha Z = T)
    (hmem : X.pair T ∈ F) :
    let Gapp := fapply G (is_func_is_pfunc (by
      simpa [SMTType.toZFSet] using hG :
        ⟦gamma.toSMTType⟧ᶻ.IsFunc
          ⟦SMTType.option alpha.toSMTType⟧ᶻ G))
      ⟨Y, by
        rw [is_func_dom_eq (by
          simpa [SMTType.toZFSet] using hG :
            ⟦gamma.toSMTType⟧ᶻ.IsFunc
              ⟦SMTType.option alpha.toSMTType⟧ᶻ G)]
        exact hY⟩
    let someZ := ZFSet.Option.some
      (S := ⟦alpha.toSMTType⟧ᶻ) ⟨Z, hZ⟩
    Gapp.val = someZ.val := by
  dsimp only
  have hYret : retract gamma Y = X :=
    ((RDomCast.iff_RDom_of_type_eq
      (α := gamma) rfl).mp Xrel).2
  have hpairRet : retract (gamma ×ᴮ alpha) (Y.pair Z) =
      X.pair T := by
    simp only [retract, ZFSet.π₁_pair, ZFSet.π₂_pair,
      hYret, hZret]
  have hgraphRet : retract (BType.set (gamma ×ᴮ alpha))
      (optionGraph gamma.toSMTType alpha.toSMTType G) = F :=
    RDomCast.optionFunction_graph_retract Frel
  have hsem := RDomCast.optionFunction_eq_some_eq_zftrue_iff
    (hX := ZFSet.pair_mem_prod.mpr ⟨hX, hT⟩)
    (ha := hY) (hb := hZ) (hF := hG)
    hpairRet hgraphRet
  dsimp only at hsem
  rw [zfEqIn_eq_zftrue_iff
    (ZFSet.fapply_mem_range _ _) (SetLike.coe_mem _)] at hsem
  exact hsem.mpr hmem

/-- The value obtained by applying and eliminating an option-function
representative is the canonical representative of the source application
result. -/
theorem RDomCastSupported.optionFunction_the_apply.{u}
    {gamma alpha : BType} {F X T G Y : ZFSet.{u}}
    {hF : F ∈ ⟦BType.set (gamma ×ᴮ alpha)⟧ᶻ}
    {hX : X ∈ ⟦gamma⟧ᶻ} {hT : T ∈ ⟦alpha⟧ᶻ}
    {hG : G ∈ ⟦SMTType.fun gamma.toSMTType
      (SMTType.option alpha.toSMTType)⟧ᶻ}
    {hY : Y ∈ ⟦gamma.toSMTType⟧ᶻ}
    (Frel : RDomCastSupported
      (⟨F, BType.set (gamma ×ᴮ alpha), hF⟩ : B.Dom)
      (⟨G, SMTType.fun gamma.toSMTType
        (SMTType.option alpha.toSMTType), hG⟩ : SMT.Dom))
    (Xrel : RDomCastSupported (⟨X, gamma, hX⟩ : B.Dom)
      (⟨Y, gamma.toSMTType, hY⟩ : SMT.Dom))
    (hmem : X.pair T ∈ F) :
    let Gapp := fapply G (is_func_is_pfunc (by
      simpa [SMTType.toZFSet] using hG :
        ⟦gamma.toSMTType⟧ᶻ.IsFunc
          ⟦SMTType.option alpha.toSMTType⟧ᶻ G))
      ⟨Y, by
        rw [is_func_dom_eq (by
          simpa [SMTType.toZFSet] using hG :
            ⟦gamma.toSMTType⟧ᶻ.IsFunc
              ⟦SMTType.option alpha.toSMTType⟧ᶻ G)]
        exact hY⟩
    RDomCastSupported
      (⟨T, alpha, hT⟩ : B.Dom)
      (⟨(ZFSet.Option.the SMTType.toZFSet_nonempty Gapp).val,
        alpha.toSMTType, SetLike.coe_mem _⟩ : SMT.Dom) := by
  dsimp only
  let dT : B.Dom.{u} := ⟨T, alpha, hT⟩
  let Z := dT.canonicalSMT
  have hZty : Z.snd.fst = alpha.toSMTType := by
    simp [Z, dT]
  have hZmem : Z.fst ∈ ⟦alpha.toSMTType⟧ᶻ := by
    rw [← hZty]
    exact Z.snd.snd
  have hZret : retract alpha Z.fst = T := by
    have hcanonical := B.Dom.rdom_canonicalSMT dT
    rw [RDom] at hcanonical
    exact hcanonical.2
  have happ := RDomCast.optionFunction_apply_some_of_mem
    (hT := hT) (hZ := hZmem)
    Frel.toRDomCast Xrel.toRDomCast hZret hmem
  let someZ := ZFSet.Option.some
    (S := ⟦alpha.toSMTType⟧ᶻ) ⟨Z.fst, hZmem⟩
  let hGfunc : ⟦gamma.toSMTType⟧ᶻ.IsFunc
      ⟦SMTType.option alpha.toSMTType⟧ᶻ G := by
    simpa [SMTType.toZFSet] using hG
  let hGpfun := is_func_is_pfunc hGfunc
  have hYdom : Y ∈ G.Dom := by
    rw [is_func_dom_eq hGfunc]
    exact hY
  let Gapp : ZFSet.Option ⟦alpha.toSMTType⟧ᶻ :=
    fapply G hGpfun ⟨Y, hYdom⟩
  have happ' : Gapp.val = someZ.val := by
    simpa only [Gapp, hGpfun, hGfunc, someZ, Z, dT,
      proof_irrel_heq] using happ
  have hGappEq : Gapp = someZ := by
    apply Subtype.ext
    exact happ'
  have hthe :
      (ZFSet.Option.the SMTType.toZFSet_nonempty Gapp).val = Z.fst := by
    rw [hGappEq, ZFSet.Option.the_some]
  change RDomCastSupported (⟨T, alpha, hT⟩ : B.Dom)
    (⟨(ZFSet.Option.the SMTType.toZFSet_nonempty Gapp).val,
      alpha.toSMTType, SetLike.coe_mem _⟩ : SMT.Dom)
  apply RDom.toRDomCastSupported
  rw [RDom]
  refine ⟨rfl, ?_⟩
  dsimp only
  rw [hthe]
  exact hZret

/-- Denotation and representation contract for the final term emitted by an
option-function application once both operands use canonical domain types. -/
theorem castApp_option_term_semantics.{u}
    {gamma alpha : BType} {f x : SMT.Term}
    {Gamma : SMT.TypeContext}
    {Theta : SMT.RenamingContext.Context.{u}}
    (hcov_f : RenamingContext.CoversFV Theta f)
    (hcov_x : RenamingContext.CoversFV Theta x)
    (respects_f : SMT.RenamingContext.RespectsTypeContextOnFV
      Theta Gamma f)
    (respects_x : SMT.RenamingContext.RespectsTypeContextOnFV
      Theta Gamma x)
    {F X T G Y : ZFSet.{u}}
    {hF : F ∈ ⟦BType.set (gamma ×ᴮ alpha)⟧ᶻ}
    {hX : X ∈ ⟦gamma⟧ᶻ} {hT : T ∈ ⟦alpha⟧ᶻ}
    {hG : G ∈ ⟦SMTType.fun gamma.toSMTType
      (SMTType.option alpha.toSMTType)⟧ᶻ}
    {hY : Y ∈ ⟦gamma.toSMTType⟧ᶻ}
    (hden_f : ⟦f.abstract Theta hcov_f⟧ˢ =
      some (⟨G, SMTType.fun gamma.toSMTType
        (SMTType.option alpha.toSMTType), hG⟩ : SMT.Dom))
    (hden_x : ⟦x.abstract Theta hcov_x⟧ˢ =
      some (⟨Y, gamma.toSMTType, hY⟩ : SMT.Dom))
    (Frel : RDomCastSupported
      (⟨F, BType.set (gamma ×ᴮ alpha), hF⟩ : B.Dom)
      (⟨G, SMTType.fun gamma.toSMTType
        (SMTType.option alpha.toSMTType), hG⟩ : SMT.Dom))
    (Xrel : RDomCastSupported (⟨X, gamma, hX⟩ : B.Dom)
      (⟨Y, gamma.toSMTType, hY⟩ : SMT.Dom))
    (hmem : X.pair T ∈ F) :
    ∃ (hcov_out : RenamingContext.CoversFV Theta
        (SMT.Term.the (SMT.Term.app f x)))
      (denOut : SMT.Dom.{u}),
      SMT.RenamingContext.RespectsTypeContextOnFV
        Theta Gamma (SMT.Term.the (SMT.Term.app f x)) ∧
      ⟦(SMT.Term.the (SMT.Term.app f x)).abstract
        Theta hcov_out⟧ˢ = some denOut ∧
      denOut.snd.fst = alpha.toSMTType ∧
      RDomCastSupported (⟨T, alpha, hT⟩ : B.Dom) denOut := by
  have hGfunc : ⟦gamma.toSMTType⟧ᶻ.IsFunc
      ⟦SMTType.option alpha.toSMTType⟧ᶻ G := by
    simpa [SMTType.toZFSet] using hG
  have hYdom : Y ∈ G.Dom := by
    rw [is_func_dom_eq hGfunc]
    exact hY
  let Gapp : ZFSet.Option ⟦alpha.toSMTType⟧ᶻ :=
    fapply G (is_func_is_pfunc hGfunc) ⟨Y, hYdom⟩
  let denApp : SMT.Dom.{u} :=
    ⟨Gapp.val, SMTType.option alpha.toSMTType, Gapp.property⟩
  have hcov_app : RenamingContext.CoversFV Theta
      (SMT.Term.app f x) := by
    intro v hv
    rw [SMT.fv, List.mem_append] at hv
    exact hv.elim (hcov_f v) (hcov_x v)
  have hden_app : ⟦(SMT.Term.app f x).abstract Theta hcov_app⟧ˢ =
      some denApp := by
    rw [SMT.Term.abstract.eq_def, SMT.denote, Option.pure_def,
      Option.bind_eq_bind, Option.bind_eq_some_iff]
    refine ⟨(⟨G, SMTType.fun gamma.toSMTType
      (SMTType.option alpha.toSMTType), hG⟩ : SMT.Dom), hden_f, ?_⟩
    rw [Option.bind_eq_some_iff]
    refine ⟨(⟨Y, gamma.toSMTType, hY⟩ : SMT.Dom), hden_x, ?_⟩
    simp only [dif_pos True.intro, dif_pos (is_func_is_pfunc hGfunc),
      dif_pos hYdom, Gapp, denApp, proof_irrel_heq]
  have hcov_out : RenamingContext.CoversFV Theta
      (SMT.Term.the (SMT.Term.app f x)) := by
    intro v hv
    exact hcov_app v (by simpa only [SMT.fv] using hv)
  let denOut : SMT.Dom.{u} :=
    ⟨(ZFSet.Option.the SMTType.toZFSet_nonempty Gapp).val,
      alpha.toSMTType, SetLike.coe_mem _⟩
  have hden_out :
      ⟦(SMT.Term.the (SMT.Term.app f x)).abstract Theta hcov_out⟧ˢ =
      some denOut := by
    rw [SMT.Term.abstract.eq_def, SMT.denote]
    have hden_app' :
        ⟦(SMT.Term.app f x).abstract Theta (fun v hv =>
          hcov_out v (by simpa only [SMT.fv] using hv))⟧ˢ =
          some denApp := by
      simpa only [proof_irrel_heq] using hden_app
    rw [hden_app']
    rfl
  have respects_out : SMT.RenamingContext.RespectsTypeContextOnFV
      Theta Gamma (SMT.Term.the (SMT.Term.app f x)) := by
    intro v sigma hv hlookup
    simp only [SMT.fv, List.mem_append] at hv
    exact hv.elim (fun h => respects_f h hlookup)
      (fun h => respects_x h hlookup)
  have result_rel :=
    RDomCastSupported.optionFunction_the_apply (hT := hT)
      Frel Xrel hmem
  refine ⟨hcov_out, denOut, respects_out, hden_out, rfl, ?_⟩
  simpa only [Gapp, denOut, proof_irrel_heq] using result_rel

/-- Construct the helper assignment for the branch that casts the argument
to the canonical domain of an option-function representative. -/
theorem castApp_option_arg_semantics.{u}
    {gamma alpha : BType} {f x spec : SMT.Term} {sx : SMTType}
    {Lambda Gamma : SMT.TypeContext} {helper : SMT.𝒱}
    {used0 used1 : List SMT.𝒱}
    (typ_f : Lambda ⊢ˢ f :
      SMTType.fun gamma.toSMTType (SMTType.option alpha.toSMTType))
    (typ_x : Lambda ⊢ˢ x : sx)
    (Lambda_sub : Lambda ⊆ Gamma)
    (helper_fresh : helper ∉ Lambda)
    (helper_lookup : Gamma.lookup helper = some gamma.toSMTType)
    (helper_not_used0 : helper ∉ used0)
    (helper_used1 : helper ∈ used1)
    (used_sub : used0 ⊆ used1)
    (spec_fv : SMT.fv spec ⊆ SMT.fv x ∪ {helper})
    (c : sx ~> gamma.toSMTType)
    (exactness :
      ∀ (Theta : SMT.RenamingContext.Context.{u})
        (hx : RenamingContext.CoversFV Theta x)
        (_respects : SMT.RenamingContext.RespectsTypeContextOnFV
          Theta Lambda x)
        (pf : ∀ (x_ : SMT.𝒱) (X_ : SMT.Dom),
          ∀ v ∈ SMT.fv (SMT.Term.var x_),
            (Function.update Theta x_ (some X_) v).isSome = true),
      ∀ (denX : SMT.Dom), ⟦x.abstract Theta hx⟧ˢ = some denX →
        ∃ (Phi H : SMT.Dom)
          (_ : ⟦(SMT.Term.var helper).abstract
            (Function.update Theta helper (some H)) (pf helper H)⟧ˢ =
              some H)
          (hphi : RenamingContext.CoversFV
            (Function.update Theta helper (some H)) spec)
          (_ : ⟦spec.abstract (Function.update Theta helper (some H))
            hphi⟧ˢ = some Phi),
          H.snd.fst = gamma.toSMTType ∧
          Phi.snd.fst = SMTType.bool ∧
          (Phi.fst = zftrue ∧
            denX.fst.pair H.fst ∈ (castZF_of_path c).1) ∧
          (∀ (Y : SMT.Dom) (_ : Y.snd.fst = gamma.toSMTType)
            (hphiY : RenamingContext.CoversFV
              (Function.update Theta helper (some Y)) spec),
            (⟦spec.abstract (Function.update Theta helper (some Y))
              hphiY⟧ˢ).isSome = true ∧
            ∀ {PhiY : SMT.Dom},
              ⟦spec.abstract (Function.update Theta helper (some Y))
                hphiY⟧ˢ = some PhiY →
              PhiY.fst = zftrue →
              denX.fst.pair Y.fst ∈ (castZF_of_path c).1))
    {Theta : SMT.RenamingContext.Context.{u}}
    (hcov_f : RenamingContext.CoversFV Theta f)
    (hcov_x : RenamingContext.CoversFV Theta x)
    (Theta_none : ∀ v ∉ used0, Theta v = none)
    (respects_f : SMT.RenamingContext.RespectsTypeContextOnFV
      Theta Lambda f)
    (respects_x : SMT.RenamingContext.RespectsTypeContextOnFV
      Theta Lambda x)
    (Theta_dom : ∀ v, Theta v ≠ none → v ∈ Gamma)
    {F X T G X0 : ZFSet.{u}}
    {hF : F ∈ ⟦BType.set (gamma ×ᴮ alpha)⟧ᶻ}
    {hX : X ∈ ⟦gamma⟧ᶻ} {hT : T ∈ ⟦alpha⟧ᶻ}
    {hG : G ∈ ⟦SMTType.fun gamma.toSMTType
      (SMTType.option alpha.toSMTType)⟧ᶻ}
    {hX0 : X0 ∈ ⟦sx⟧ᶻ}
    (hden_f : ⟦f.abstract Theta hcov_f⟧ˢ =
      some (⟨G, SMTType.fun gamma.toSMTType
        (SMTType.option alpha.toSMTType), hG⟩ : SMT.Dom))
    (hden_x : ⟦x.abstract Theta hcov_x⟧ˢ =
      some (⟨X0, sx, hX0⟩ : SMT.Dom))
    (Frel : RDomCastSupported
      (⟨F, BType.set (gamma ×ᴮ alpha), hF⟩ : B.Dom)
      (⟨G, SMTType.fun gamma.toSMTType
        (SMTType.option alpha.toSMTType), hG⟩ : SMT.Dom))
    (Xrel : RDomCastSupported (⟨X, gamma, hX⟩ : B.Dom)
      (⟨X0, sx, hX0⟩ : SMT.Dom))
    (hmem : X.pair T ∈ F) :
    ∃ (Theta' : SMT.RenamingContext.Context.{u})
      (hcov_out : RenamingContext.CoversFV Theta'
        (SMT.Term.the (SMT.Term.app f (.var helper))))
      (denOut : SMT.Dom.{u}),
      RenamingContext.Extends Theta' Theta ∧
      (∀ v ∉ used1, Theta' v = none) ∧
      SMT.RenamingContext.RespectsTypeContextOnFV Theta' Gamma
        (SMT.Term.the (SMT.Term.app f (.var helper))) ∧
      (∀ v, Theta' v ≠ none → v ∈ Gamma) ∧
      SpecBodiesTrue Theta' Gamma
        (helperSpecChunk helper gamma.toSMTType spec) ∧
      ⟦(SMT.Term.the (SMT.Term.app f (.var helper))).abstract
        Theta' hcov_out⟧ˢ = some denOut ∧
      denOut.snd.fst = alpha.toSMTType ∧
      RDomCastSupported (⟨T, alpha, hT⟩ : B.Dom) denOut := by
  have helper_none : Theta helper = none :=
    Theta_none helper helper_not_used0
  let pf : ∀ (x_ : SMT.𝒱) (H : SMT.Dom),
      ∀ v ∈ SMT.fv (SMT.Term.var x_),
        (Function.update Theta x_ (some H) v).isSome = true := by
    intro x_ H v hv
    simp only [SMT.fv, List.mem_singleton] at hv
    subst v
    simp
  obtain ⟨Phi, H, hden_var, hcov_spec, hden_spec, Hty, Phity,
      ⟨PhiTrue, castPair⟩, _guard⟩ :=
    exactness Theta hcov_x respects_x pf
      (⟨X0, sx, hX0⟩ : SMT.Dom) hden_x
  let Theta' := Function.update Theta helper (some H)
  have Theta'_ext : RenamingContext.Extends Theta' Theta :=
    RenamingContext.extends_update_of_none helper_none
  have helper_not_fv_f : helper ∉ SMT.fv f :=
    fun hv => helper_fresh (SMT.Typing.mem_context_of_mem_fv typ_f hv)
  have hcov_f' : RenamingContext.CoversFV Theta' f :=
    RenamingContext.coversFV_of_extends_of_coversFV Theta'_ext hcov_f
  have hden_f' : ⟦f.abstract Theta' hcov_f'⟧ˢ =
      some (⟨G, SMTType.fun gamma.toSMTType
        (SMTType.option alpha.toSMTType), hG⟩ : SMT.Dom) := by
    have hagree := RenamingContext.agreesOnFV_of_extends_of_coversFV
      Theta'_ext hcov_f
    exact (RenamingContext.denote_congr_of_agreesOnFV
      (t := f) (h1 := hcov_f') (h2 := hcov_f) hagree).trans hden_f
  have respects_f_Gamma :
      SMT.RenamingContext.RespectsTypeContextOnFV Theta Gamma f :=
    respects_f.of_extends (RenamingContext.extends_refl Theta)
      Lambda_sub typ_f
  have respects_f' :
      SMT.RenamingContext.RespectsTypeContextOnFV Theta' Gamma f := by
    intro v sigma hv hlookup
    have hv_ne : v ≠ helper := fun h => by
      subst v
      exact helper_not_fv_f hv
    obtain ⟨d, hd, hdty⟩ := respects_f_Gamma hv hlookup
    exact ⟨d, by simpa [Theta', Function.update_of_ne hv_ne] using hd,
      hdty⟩
  have hcov_var : RenamingContext.CoversFV Theta' (.var helper) := by
    intro v hv
    simp only [SMT.fv, List.mem_singleton] at hv
    subst v
    simp [Theta']
  have hden_var' : ⟦(SMT.Term.var helper).abstract Theta' hcov_var⟧ˢ =
      some H := by
    simpa only [Theta', proof_irrel_heq] using hden_var
  have respects_var :
      SMT.RenamingContext.RespectsTypeContextOnFV Theta' Gamma
        (.var helper) := by
    intro v sigma hv hlookup
    simp only [SMT.fv, List.mem_singleton] at hv
    subst v
    rw [helper_lookup] at hlookup
    cases hlookup
    exact ⟨H, by simp [Theta'], Hty⟩
  have Hmem : H.fst ∈ ⟦gamma.toSMTType⟧ᶻ := by
    rw [← Hty]
    exact H.snd.snd
  have Heq : H =
      (⟨H.fst, gamma.toSMTType, Hmem⟩ : SMT.Dom) := by
    rcases H with ⟨Hv, Hsigma, hHv⟩
    dsimp at Hty
    subst Hsigma
    rfl
  have hden_var_canon :
      ⟦(SMT.Term.var helper).abstract Theta' hcov_var⟧ˢ =
        some (⟨H.fst, gamma.toSMTType, Hmem⟩ : SMT.Dom) := by
    rw [← Heq]
    exact hden_var'
  have XrelH : RDomCastSupported (⟨X, gamma, hX⟩ : B.Dom)
      (⟨H.fst, gamma.toSMTType, Hmem⟩ : SMT.Dom) :=
    RDomCastSupported.of_cast_to_canonical Xrel c castPair
  obtain ⟨hcov_out, denOut, respects_out, hden_out,
      denOutTy, resultRel⟩ :=
    castApp_option_term_semantics hcov_f' hcov_var respects_f'
      respects_var hden_f' hden_var_canon Frel XrelH hmem
  have respects_x_Gamma :
      SMT.RenamingContext.RespectsTypeContextOnFV Theta Gamma x :=
    respects_x.of_extends (RenamingContext.extends_refl Theta)
      Lambda_sub typ_x
  have respects_spec :
      SMT.RenamingContext.RespectsTypeContextOnFV Theta' Gamma spec :=
    SMT.RenamingContext.respects_update_helper spec_fv
      respects_x_Gamma helper_lookup Hty
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
      (helperSpecChunk helper gamma.toSMTType spec) := by
    intro body hbody
    simp only [specBodies_helperSpecChunk, List.mem_singleton] at hbody
    subst body
    exact ⟨hcov_spec, Phi, respects_spec, hden_spec, Phity, PhiTrue⟩
  exact ⟨Theta', hcov_out, denOut, Theta'_ext, Theta'_none,
    respects_out, Theta'_dom, specs_true, hden_out, denOutTy, resultRel⟩

/-- Under any assignment satisfying the generated argument-cast
specification, the option-function application denotes the source result. -/
theorem castApp_option_arg_guarded_semantics.{u}
    {gamma alpha : BType} {f x spec : SMT.Term} {sx : SMTType}
    {Lambda GammaSup : SMT.TypeContext} {helper : SMT.𝒱}
    (scope : ScopedContextExtends Lambda
      (helperSpecChunk helper gamma.toSMTType spec) GammaSup)
    (c : sx ~> gamma.toSMTType)
    (exactness :
      ∀ (Theta : SMT.RenamingContext.Context.{u})
        (hx : RenamingContext.CoversFV Theta x)
        (_respects : SMT.RenamingContext.RespectsTypeContextOnFV
          Theta Lambda x)
        (pf : ∀ (x_ : SMT.𝒱) (X_ : SMT.Dom),
          ∀ v ∈ SMT.fv (SMT.Term.var x_),
            (Function.update Theta x_ (some X_) v).isSome = true),
      ∀ (denX : SMT.Dom), ⟦x.abstract Theta hx⟧ˢ = some denX →
        ∃ (Phi H : SMT.Dom)
          (_ : ⟦(SMT.Term.var helper).abstract
            (Function.update Theta helper (some H)) (pf helper H)⟧ˢ =
              some H)
          (hphi : RenamingContext.CoversFV
            (Function.update Theta helper (some H)) spec)
          (_ : ⟦spec.abstract (Function.update Theta helper (some H))
            hphi⟧ˢ = some Phi),
          H.snd.fst = gamma.toSMTType ∧
          Phi.snd.fst = SMTType.bool ∧
          (Phi.fst = zftrue ∧
            denX.fst.pair H.fst ∈ (castZF_of_path c).1) ∧
          (∀ (Y : SMT.Dom) (_ : Y.snd.fst = gamma.toSMTType)
            (hphiY : RenamingContext.CoversFV
              (Function.update Theta helper (some Y)) spec),
            (⟦spec.abstract (Function.update Theta helper (some Y))
              hphiY⟧ˢ).isSome = true ∧
            ∀ {PhiY : SMT.Dom},
              ⟦spec.abstract (Function.update Theta helper (some Y))
                hphiY⟧ˢ = some PhiY →
              PhiY.fst = zftrue →
              denX.fst.pair Y.fst ∈ (castZF_of_path c).1))
    {Theta : SMT.RenamingContext.Context.{u}}
    (hcov_f : RenamingContext.CoversFV Theta f)
    (hcov_x : RenamingContext.CoversFV Theta x)
    (respects_f : SMT.RenamingContext.RespectsTypeContextOnFV
      Theta GammaSup f)
    (respects_x : SMT.RenamingContext.RespectsTypeContextOnFV
      Theta GammaSup x)
    {F X T G X0 : ZFSet.{u}}
    {hF : F ∈ ⟦BType.set (gamma ×ᴮ alpha)⟧ᶻ}
    {hX : X ∈ ⟦gamma⟧ᶻ} {hT : T ∈ ⟦alpha⟧ᶻ}
    {hG : G ∈ ⟦SMTType.fun gamma.toSMTType
      (SMTType.option alpha.toSMTType)⟧ᶻ}
    {hX0 : X0 ∈ ⟦sx⟧ᶻ}
    (hden_f : ⟦f.abstract Theta hcov_f⟧ˢ =
      some (⟨G, SMTType.fun gamma.toSMTType
        (SMTType.option alpha.toSMTType), hG⟩ : SMT.Dom))
    (hden_x : ⟦x.abstract Theta hcov_x⟧ˢ =
      some (⟨X0, sx, hX0⟩ : SMT.Dom))
    (Frel : RDomCastSupported
      (⟨F, BType.set (gamma ×ᴮ alpha), hF⟩ : B.Dom)
      (⟨G, SMTType.fun gamma.toSMTType
        (SMTType.option alpha.toSMTType), hG⟩ : SMT.Dom))
    (Xrel : RDomCastSupported (⟨X, gamma, hX⟩ : B.Dom)
      (⟨X0, sx, hX0⟩ : SMT.Dom))
    (hmem : X.pair T ∈ F)
    (hcov_out : RenamingContext.CoversFV Theta
      (SMT.Term.the (SMT.Term.app f (.var helper))))
    (denOut : SMT.Dom.{u})
    (respects_out : SMT.RenamingContext.RespectsTypeContextOnFV
      Theta GammaSup
      (SMT.Term.the (SMT.Term.app f (.var helper))))
    (specs_true : SpecBodiesTrue Theta GammaSup
      (helperSpecChunk helper gamma.toSMTType spec))
    (hden_out :
      ⟦(SMT.Term.the (SMT.Term.app f (.var helper))).abstract
        Theta hcov_out⟧ˢ = some denOut)
    (_denOutTy : denOut.snd.fst = alpha.toSMTType) :
    RDomCastSupported (⟨T, alpha, hT⟩ : B.Dom) denOut := by
  have respects_x_base :
      SMT.RenamingContext.RespectsTypeContextOnFV Theta Lambda x :=
    respects_x.of_super scope.base
  let pf : ∀ (x_ : SMT.𝒱) (H : SMT.Dom),
      ∀ v ∈ SMT.fv (SMT.Term.var x_),
        (Function.update Theta x_ (some H) v).isSome = true := by
    intro x_ H v hv
    simp only [SMT.fv, List.mem_singleton] at hv
    subst v
    simp
  obtain ⟨_PhiW, _HW, _hdenVarW, _hcovSpecW, _hdenSpecW,
      _HWty, _PhiWty, _castW, guard⟩ :=
    exactness Theta hcov_x respects_x_base pf
      (⟨X0, sx, hX0⟩ : SMT.Dom) hden_x
  have helper_some : (Theta helper).isSome = true := by
    apply hcov_out helper
    simp only [SMT.fv, List.mem_append, List.mem_singleton]
    exact Or.inr trivial
  obtain ⟨H, hH⟩ := Option.isSome_iff_exists.mp helper_some
  have helper_fv_out : helper ∈ SMT.fv
      (SMT.Term.the (SMT.Term.app f (.var helper))) := by
    simp only [SMT.fv, List.mem_append, List.mem_singleton]
    exact Or.inr trivial
  have helper_lookup : GammaSup.lookup helper =
      some gamma.toSMTType :=
    scope.lookup_of_declared (by
      simp [declEntries_helperSpecChunk])
  have Hty : H.snd.fst = gamma.toSMTType := by
    obtain ⟨d, hd, hdty⟩ :=
      respects_out helper_fv_out helper_lookup
    rw [hH] at hd
    injection hd with hdeq
    subst d
    exact hdty
  have hupdate : Function.update Theta helper (some H) = Theta := by
    rw [← hH]
    exact Function.update_eq_self helper Theta
  have hspec_true := specs_true spec (by simp)
  obtain ⟨hcov_spec, denSpec, _respects_spec, hden_spec,
      _denSpecTy, denSpecTrue⟩ := hspec_true
  have hcov_spec_update : RenamingContext.CoversFV
      (Function.update Theta helper (some H)) spec := by
    rw [hupdate]
    exact hcov_spec
  obtain ⟨_some, castPair⟩ := guard H Hty hcov_spec_update
  have hden_spec_update :
      ⟦spec.abstract (Function.update Theta helper (some H))
        hcov_spec_update⟧ˢ = some denSpec := by
    simpa only [hupdate, proof_irrel_heq] using hden_spec
  have castPair' := castPair hden_spec_update denSpecTrue
  have Hmem : H.fst ∈ ⟦gamma.toSMTType⟧ᶻ := by
    rw [← Hty]
    exact H.snd.snd
  have XrelH : RDomCastSupported (⟨X, gamma, hX⟩ : B.Dom)
      (⟨H.fst, gamma.toSMTType, Hmem⟩ : SMT.Dom) :=
    RDomCastSupported.of_cast_to_canonical Xrel c castPair'
  have hcov_var : RenamingContext.CoversFV Theta (.var helper) := by
    intro v hv
    simp only [SMT.fv, List.mem_singleton] at hv
    subst v
    simpa [Option.isSome_iff_ne_none] using
      (show Theta helper ≠ none by simp [hH])
  have hden_var : ⟦(SMT.Term.var helper).abstract Theta hcov_var⟧ˢ =
      some (⟨H.fst, gamma.toSMTType, Hmem⟩ : SMT.Dom) := by
    rw [SMT.Term.abstract.eq_def]
    simp only [SMT.denote]
    have hget := Option.get_of_eq_some helper_some hH
    rw [hget]
    rcases H with ⟨Hv, Hsigma, hHv⟩
    dsimp at Hty
    subst Hsigma
    rfl
  have respects_var :
      SMT.RenamingContext.RespectsTypeContextOnFV Theta GammaSup
        (.var helper) := by
    intro v sigma hv hlookup
    simp only [SMT.fv, List.mem_singleton] at hv
    subst v
    rw [helper_lookup] at hlookup
    cases hlookup
    exact ⟨H, hH, Hty⟩
  obtain ⟨hcov_expected, denExpected, _respects_expected,
      hden_expected, _denExpectedTy, expectedRel⟩ :=
    castApp_option_term_semantics hcov_f hcov_var respects_f
      respects_var hden_f hden_var Frel XrelH hmem
  have hcov_eq : hcov_expected = hcov_out := Subsingleton.elim _ _
  subst hcov_expected
  rw [hden_out] at hden_expected
  have hden_eq : denExpected = denOut :=
    (Option.some.inj hden_expected).symm
  rw [← hden_eq]
  exact expectedRel

/-! ## Declaration-aware application contract -/

abbrev CastAppRepGuardedSemantics.{u}
    (gamma alpha : BType) (f x t : SMT.Term)
    (sf sx : SMTType) (Lambda : SMT.TypeContext)
    (Dlt : SMT.Chunk) : Prop :=
  ∀ (GammaSup : SMT.TypeContext),
    ScopedContextExtends Lambda Dlt GammaSup →
    ∀ (Theta : SMT.RenamingContext.Context.{u})
      (hcov_f : RenamingContext.CoversFV Theta f)
      (hcov_x : RenamingContext.CoversFV Theta x),
      SMT.RenamingContext.RespectsTypeContextOnFV Theta GammaSup f →
      SMT.RenamingContext.RespectsTypeContextOnFV Theta GammaSup x →
      ∀ (F X T : ZFSet.{u})
        (hF : F ∈ ⟦BType.set (gamma ×ᴮ alpha)⟧ᶻ)
        (hX : X ∈ ⟦gamma⟧ᶻ) (hT : T ∈ ⟦alpha⟧ᶻ)
        (hfun : F.IsPFunc ⟦gamma⟧ᶻ ⟦alpha⟧ᶻ)
        (hdom : X ∈ F.Dom)
        (hresult : (fapply F hfun ⟨X, hdom⟩).val = T)
        (denF denX : SMT.Dom.{u}),
        ⟦f.abstract Theta hcov_f⟧ˢ = some denF →
        ⟦x.abstract Theta hcov_x⟧ˢ = some denX →
        denF.snd.fst = sf → denX.snd.fst = sx →
        RDomCastSupported
          (⟨F, BType.set (gamma ×ᴮ alpha), hF⟩ : B.Dom) denF →
        RDomCastSupported (⟨X, gamma, hX⟩ : B.Dom) denX →
        ∀ (hcov_t : RenamingContext.CoversFV Theta t)
          (denT : SMT.Dom.{u}),
          SMT.RenamingContext.RespectsTypeContextOnFV Theta GammaSup t →
          SpecBodiesTrue Theta GammaSup Dlt →
          ⟦t.abstract Theta hcov_t⟧ˢ = some denT →
          denT.snd.fst = alpha.toSMTType →
          RDomCastSupported (⟨T, alpha, hT⟩ : B.Dom) denT

abbrev CastAppRepSemantics.{u}
    (gamma alpha : BType) (f x t : SMT.Term)
    (sf sx : SMTType) (Lambda Gamma : SMT.TypeContext)
    (used0 used1 : List SMT.𝒱) (Dlt : SMT.Chunk) : Prop :=
  ∀ (GammaSup : SMT.TypeContext), Gamma ⊆ GammaSup →
    ∀ (Theta : SMT.RenamingContext.Context.{u})
      (hcov_f : RenamingContext.CoversFV Theta f)
      (hcov_x : RenamingContext.CoversFV Theta x),
      (∀ v ∉ used0, Theta v = none) →
      SMT.RenamingContext.RespectsTypeContextOnFV Theta GammaSup f →
      SMT.RenamingContext.RespectsTypeContextOnFV Theta GammaSup x →
      (∀ v, Theta v ≠ none → v ∈ GammaSup) →
      ∀ (F X T : ZFSet.{u})
        (hF : F ∈ ⟦BType.set (gamma ×ᴮ alpha)⟧ᶻ)
        (hX : X ∈ ⟦gamma⟧ᶻ) (hT : T ∈ ⟦alpha⟧ᶻ)
        (hfun : F.IsPFunc ⟦gamma⟧ᶻ ⟦alpha⟧ᶻ)
        (hdom : X ∈ F.Dom)
        (hresult : (fapply F hfun ⟨X, hdom⟩).val = T)
        (denF denX : SMT.Dom.{u}),
        ⟦f.abstract Theta hcov_f⟧ˢ = some denF →
        ⟦x.abstract Theta hcov_x⟧ˢ = some denX →
        denF.snd.fst = sf → denX.snd.fst = sx →
        RDomCastSupported
          (⟨F, BType.set (gamma ×ᴮ alpha), hF⟩ : B.Dom) denF →
        RDomCastSupported (⟨X, gamma, hX⟩ : B.Dom) denX →
        (∃ (Theta' : SMT.RenamingContext.Context.{u})
          (hcov_t : RenamingContext.CoversFV Theta' t)
          (denT : SMT.Dom.{u}),
          RenamingContext.Extends Theta' Theta ∧
          (∀ v ∉ used1, Theta' v = none) ∧
          SMT.RenamingContext.RespectsTypeContextOnFV Theta' GammaSup t ∧
          (∀ v, Theta' v ≠ none → v ∈ GammaSup) ∧
          SpecBodiesTrue Theta' GammaSup Dlt ∧
          ⟦t.abstract Theta' hcov_t⟧ˢ = some denT ∧
          denT.snd.fst = alpha.toSMTType ∧
          RDomCastSupported (⟨T, alpha, hT⟩ : B.Dom) denT) ∧
        CastAppRepGuardedSemantics.{u}
          gamma alpha f x t sf sx Lambda Dlt

abbrev CastAppRepScopedSpec.{u} (gamma alpha : BType)
    (f x : SMT.Term) (sf sx : SMTType) : Prop :=
  ∀ {Lambda : SMT.TypeContext} {n : ℕ} {used : List SMT.𝒱}
    {decl : SMT.Chunk},
    Lambda ⊢ˢ f : sf →
    Lambda ⊢ˢ x : sx →
    (∀ v ∈ SMT.bv f, v ∈ used) →
    (∀ v ∈ SMT.bv x, v ∈ used) →
    ⦃fun ⟨E, Lambda'⟩ =>
      ⌜Lambda' = Lambda ∧ E.freshvarsc = n ∧
        Lambda.keys ⊆ E.usedVars ∧ E.usedVars = used ∧
        E.declarations = decl⌝⦄
    castApp ⟨f, sf⟩ ⟨x, sx⟩
    ⦃⇓? ⟨t, sigma⟩ ⟨E', Gamma'⟩ =>
      ⌜used ⊆ E'.usedVars ∧
        Lambda ⊆ Gamma' ∧
        Gamma'.keys ⊆ E'.usedVars ∧
        sigma = alpha.toSMTType ∧
        Gamma' ⊢ˢ t : alpha.toSMTType ∧
        (∀ v ∈ used, v ∉ Lambda → v ∉ Gamma') ∧
        ∃ Dlt : SMT.Chunk,
          E'.declarations = decl ++ Dlt ∧
          ContextGeneratedByDeclarations Lambda Gamma' Dlt ∧
          DeclarationContextTrace Lambda Dlt Gamma' ∧
          (∀ v ∈ declVars Dlt, v ∉ used) ∧
          CastAppRepSemantics.{u} gamma alpha f x t sf sx
            Lambda Gamma' used E'.usedVars Dlt ∧
          (∀ b ∈ specBodies Dlt, Gamma' ⊢ˢ b : SMTType.bool) ∧
          ScopedGeneratedTyping Lambda Dlt t alpha.toSMTType⌝⦄

set_option maxHeartbeats 4000000 in
theorem castApp_option_arg_scoped_contract.{u}
    (gamma alpha : BType) (f x : SMT.Term) (sx : SMTType)
    (hnotle : ¬ gamma.toSMTType ⊑ sx)
    (hle : sx ⊑ gamma.toSMTType)
    (hfaith : castPath.FVFaithful hle.toCastPath) :
    CastAppRepScopedSpec.{u} gamma alpha f x
      (SMTType.fun gamma.toSMTType
        (SMTType.option alpha.toSMTType)) sx := by
  unfold CastAppRepScopedSpec
  intro Lambda n used decl typ_f typ_x bv_f_used bv_x_used
  mstart
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_keys, St_used_eq, St_decl_eq⟩ := pre
  simp only [castApp]
  rw [dif_neg hnotle, dif_pos hle]
  mspec (Std.Do.Triple.and _
    (Std.Do.Triple.and _
      (Std.Do.Triple.and _
        (loosenAux_prf_exact_univ
          (Λ := St.types) (n := St.env.freshvarsc)
          (used := St.env.usedVars) typ_x
          (fun v hv => St_used_eq ▸ bv_x_used v hv) hle.toCastPath)
        (loosenAux_prf_fv_of_faithful hfaith
          (used := St.env.usedVars) (n := St.env.freshvarsc)
          (x := x) (by
            intro v hv
            exact St_keys (SMT.Typing.mem_context_of_mem_fv typ_x hv))))
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
    (x!_spec := spec) (τ := gamma.toSMTType)
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
  have typ_f1 : St1.types ⊢ˢ f :
      SMTType.fun gamma.toSMTType
        (SMTType.option alpha.toSMTType) :=
    SMT.Typing.weakening Lambda_sub1 typ_f
      (fun v hv => preserves1 v (St_used_eq ▸ bv_f_used v hv)
        (SMT.Typing.bv_notMem_context typ_f v hv))
  have typOut : St1.types ⊢ˢ
      (SMT.Term.the (SMT.Term.app f (.var helper))) :
        alpha.toSMTType := by
    apply SMT.Typing.the
    apply SMT.Typing.app
    · exact typ_f1
    · exact typ_helper
  have helper_lookup : St1.types.lookup helper =
      some gamma.toSMTType := SMT.Typing.varE typ_helper
  have helper_used1 : helper ∈ St1.env.usedVars :=
    keys_sub1 (AList.lookup_isSome.mp
      (Option.isSome_of_eq_some helper_lookup))
  have helper_ctx_gen : ContextGeneratedByDeclarations St.types St1.types
      (helperSpecChunk helper gamma.toSMTType spec) := by
    rw [St1_types_exact]
    exact ContextGeneratedByDeclarations.insert_helper
      St.types helper gamma.toSMTType spec helper_fresh
  have helper_ctx_trace : DeclarationContextTrace St.types
      (helperSpecChunk helper gamma.toSMTType spec) St1.types := by
    rw [St1_types_exact]
    exact DeclarationContextTrace.helperSpecChunk
      St.types helper gamma.toSMTType spec helper_fresh
  have used_sub_out : used ⊆ St1.env.usedVars := by
    simpa [St_used_eq] using used_sub1
  have preserves_out : ∀ v ∈ used, v ∉ St.types → v ∉ St1.types := by
    simpa [St_used_eq] using preserves1
  have helper_not_used_out : helper ∉ used := by
    simpa [St_used_eq] using helper_not_used
  mpure_intro
  rw [St2_used, St2_types]
  refine ⟨used_sub_out, Lambda_sub1, keys_sub1, True.intro, typOut,
    preserves_out, helperSpecChunk helper gamma.toSMTType spec, ?_,
    helper_ctx_gen, helper_ctx_trace, ?_, ?_, ?_, ?_⟩
  · rw [St2_decl_eq, St1_decl_eq]
    simp [helperSpecChunk, List.concat_eq_append, List.append_assoc]
  · intro v hv
    simp only [declVars_helperSpecChunk, List.mem_singleton] at hv
    subst v
    exact helper_not_used_out
  · intro GammaSup GammaSub Theta hcov_f hcov_x Theta_none
      respects_f respects_x Theta_dom F X T hF hX hT hfun hdom
      hresult denF denX hden_f hden_x hdenFty hdenXty Frel Xrel
    have Lambda_sub_sup : St.types ⊆ GammaSup :=
      AList.subset_trans Lambda_sub1 GammaSub
    have respects_f_base :
        SMT.RenamingContext.RespectsTypeContextOnFV Theta St.types f :=
      respects_f.of_super Lambda_sub_sup
    have respects_x_base :
        SMT.RenamingContext.RespectsTypeContextOnFV Theta St.types x :=
      respects_x.of_super Lambda_sub_sup
    have helper_lookup_sup : GammaSup.lookup helper =
        some gamma.toSMTType :=
      AList.lookup_of_subset GammaSub helper_lookup
    rcases denF with ⟨G, sigmaF, hG⟩
    rcases denX with ⟨X0, sigmaX, hX0⟩
    dsimp at hdenFty hdenXty
    subst sigmaF
    subst sigmaX
    have hmem : X.pair T ∈ F := by
      rw [← hresult]
      exact ZFSet.fapply.def hfun hdom
    constructor
    · exact castApp_option_arg_semantics typ_f typ_x Lambda_sub_sup
        helper_fresh helper_lookup_sup helper_not_used_out
        helper_used1 used_sub_out spec_fv hle.toCastPath exactness
        hcov_f hcov_x Theta_none respects_f_base respects_x_base
        Theta_dom hden_f hden_x Frel Xrel hmem
    · intro GammaSupG scopeG ThetaG hcov_fG hcov_xG
        respects_fG respects_xG FG XG TG hFG hXG hTG hfunG hdomG
        hresultG denFG denXG hden_fG hden_xG hdenFGty hdenXGty
        FrelG XrelG hcov_outG denOutG respects_outG specs_trueG
        hden_outG denOutGTy
      rcases denFG with ⟨GG, sigmaFG, hGG⟩
      rcases denXG with ⟨X0G, sigmaXG, hX0G⟩
      dsimp at hdenFGty hdenXGty
      subst sigmaFG
      subst sigmaXG
      have hmemG : XG.pair TG ∈ FG := by
        rw [← hresultG]
        exact ZFSet.fapply.def hfunG hdomG
      exact castApp_option_arg_guarded_semantics scopeG
        hle.toCastPath exactness hcov_fG hcov_xG respects_fG respects_xG
        hden_fG hden_xG FrelG XrelG hmemG hcov_outG denOutG
        respects_outG specs_trueG hden_outG denOutGTy
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

/-- Construct the helper assignment for the branch that self-casts an
option-function when the argument is already canonical. -/
theorem castApp_option_fun_semantics.{u}
    {gamma alpha : BType} {f x spec : SMT.Term}
    {Lambda Gamma : SMT.TypeContext} {helper : SMT.𝒱}
    {used0 used1 : List SMT.𝒱}
    (typ_f : Lambda ⊢ˢ f :
      SMTType.fun gamma.toSMTType (SMTType.option alpha.toSMTType))
    (typ_x : Lambda ⊢ˢ x : gamma.toSMTType)
    (Lambda_sub : Lambda ⊆ Gamma)
    (helper_fresh : helper ∉ Lambda)
    (helper_lookup : Gamma.lookup helper = some
      (SMTType.fun gamma.toSMTType
        (SMTType.option alpha.toSMTType)))
    (helper_not_used0 : helper ∉ used0)
    (helper_used1 : helper ∈ used1)
    (used_sub : used0 ⊆ used1)
    (spec_fv : SMT.fv spec ⊆ SMT.fv f ∪ {helper})
    (c : SMTType.fun gamma.toSMTType
      (SMTType.option alpha.toSMTType) ~>
      SMTType.fun gamma.toSMTType
        (SMTType.option alpha.toSMTType))
    (exactness :
      ∀ (Theta : SMT.RenamingContext.Context.{u})
        (hf : RenamingContext.CoversFV Theta f)
        (_respects : SMT.RenamingContext.RespectsTypeContextOnFV
          Theta Lambda f)
        (pf : ∀ (x_ : SMT.𝒱) (X_ : SMT.Dom),
          ∀ v ∈ SMT.fv (SMT.Term.var x_),
            (Function.update Theta x_ (some X_) v).isSome = true),
      ∀ (denF : SMT.Dom), ⟦f.abstract Theta hf⟧ˢ = some denF →
        ∃ (Phi H : SMT.Dom)
          (_ : ⟦(SMT.Term.var helper).abstract
            (Function.update Theta helper (some H)) (pf helper H)⟧ˢ =
              some H)
          (hphi : RenamingContext.CoversFV
            (Function.update Theta helper (some H)) spec)
          (_ : ⟦spec.abstract (Function.update Theta helper (some H))
            hphi⟧ˢ = some Phi),
          H.snd.fst = SMTType.fun gamma.toSMTType
            (SMTType.option alpha.toSMTType) ∧
          Phi.snd.fst = SMTType.bool ∧
          (Phi.fst = zftrue ∧
            denF.fst.pair H.fst ∈ (castZF_of_path c).1) ∧
          (∀ (Y : SMT.Dom)
            (_ : Y.snd.fst = SMTType.fun gamma.toSMTType
              (SMTType.option alpha.toSMTType))
            (hphiY : RenamingContext.CoversFV
              (Function.update Theta helper (some Y)) spec),
            (⟦spec.abstract (Function.update Theta helper (some Y))
              hphiY⟧ˢ).isSome = true ∧
            ∀ {PhiY : SMT.Dom},
              ⟦spec.abstract (Function.update Theta helper (some Y))
                hphiY⟧ˢ = some PhiY →
              PhiY.fst = zftrue →
              denF.fst.pair Y.fst ∈ (castZF_of_path c).1))
    {Theta : SMT.RenamingContext.Context.{u}}
    (hcov_f : RenamingContext.CoversFV Theta f)
    (hcov_x : RenamingContext.CoversFV Theta x)
    (Theta_none : ∀ v ∉ used0, Theta v = none)
    (respects_f : SMT.RenamingContext.RespectsTypeContextOnFV
      Theta Lambda f)
    (respects_x : SMT.RenamingContext.RespectsTypeContextOnFV
      Theta Lambda x)
    (Theta_dom : ∀ v, Theta v ≠ none → v ∈ Gamma)
    {F X T G Y : ZFSet.{u}}
    {hF : F ∈ ⟦BType.set (gamma ×ᴮ alpha)⟧ᶻ}
    {hX : X ∈ ⟦gamma⟧ᶻ} {hT : T ∈ ⟦alpha⟧ᶻ}
    {hG : G ∈ ⟦SMTType.fun gamma.toSMTType
      (SMTType.option alpha.toSMTType)⟧ᶻ}
    {hY : Y ∈ ⟦gamma.toSMTType⟧ᶻ}
    (hden_f : ⟦f.abstract Theta hcov_f⟧ˢ =
      some (⟨G, SMTType.fun gamma.toSMTType
        (SMTType.option alpha.toSMTType), hG⟩ : SMT.Dom))
    (hden_x : ⟦x.abstract Theta hcov_x⟧ˢ =
      some (⟨Y, gamma.toSMTType, hY⟩ : SMT.Dom))
    (Frel : RDomCastSupported
      (⟨F, BType.set (gamma ×ᴮ alpha), hF⟩ : B.Dom)
      (⟨G, SMTType.fun gamma.toSMTType
        (SMTType.option alpha.toSMTType), hG⟩ : SMT.Dom))
    (Xrel : RDomCastSupported (⟨X, gamma, hX⟩ : B.Dom)
      (⟨Y, gamma.toSMTType, hY⟩ : SMT.Dom))
    (hmem : X.pair T ∈ F) :
    ∃ (Theta' : SMT.RenamingContext.Context.{u})
      (hcov_out : RenamingContext.CoversFV Theta'
        (SMT.Term.the (SMT.Term.app (.var helper) x)))
      (denOut : SMT.Dom.{u}),
      RenamingContext.Extends Theta' Theta ∧
      (∀ v ∉ used1, Theta' v = none) ∧
      SMT.RenamingContext.RespectsTypeContextOnFV Theta' Gamma
        (SMT.Term.the (SMT.Term.app (.var helper) x)) ∧
      (∀ v, Theta' v ≠ none → v ∈ Gamma) ∧
      SpecBodiesTrue Theta' Gamma
        (helperSpecChunk helper
          (SMTType.fun gamma.toSMTType
            (SMTType.option alpha.toSMTType)) spec) ∧
      ⟦(SMT.Term.the (SMT.Term.app (.var helper) x)).abstract
        Theta' hcov_out⟧ˢ = some denOut ∧
      denOut.snd.fst = alpha.toSMTType ∧
      RDomCastSupported (⟨T, alpha, hT⟩ : B.Dom) denOut := by
  have helper_none : Theta helper = none :=
    Theta_none helper helper_not_used0
  let pf : ∀ (x_ : SMT.𝒱) (H : SMT.Dom),
      ∀ v ∈ SMT.fv (SMT.Term.var x_),
        (Function.update Theta x_ (some H) v).isSome = true := by
    intro x_ H v hv
    simp only [SMT.fv, List.mem_singleton] at hv
    subst v
    simp
  obtain ⟨Phi, H, hden_var, hcov_spec, hden_spec, Hty, Phity,
      ⟨PhiTrue, castPair⟩, _guard⟩ :=
    exactness Theta hcov_f respects_f pf
      (⟨G, SMTType.fun gamma.toSMTType
        (SMTType.option alpha.toSMTType), hG⟩ : SMT.Dom) hden_f
  let Theta' := Function.update Theta helper (some H)
  have Theta'_ext : RenamingContext.Extends Theta' Theta :=
    RenamingContext.extends_update_of_none helper_none
  have helper_not_fv_x : helper ∉ SMT.fv x :=
    fun hv => helper_fresh (SMT.Typing.mem_context_of_mem_fv typ_x hv)
  have hcov_x' : RenamingContext.CoversFV Theta' x :=
    RenamingContext.coversFV_of_extends_of_coversFV Theta'_ext hcov_x
  have hden_x' : ⟦x.abstract Theta' hcov_x'⟧ˢ =
      some (⟨Y, gamma.toSMTType, hY⟩ : SMT.Dom) := by
    have hagree := RenamingContext.agreesOnFV_of_extends_of_coversFV
      Theta'_ext hcov_x
    exact (RenamingContext.denote_congr_of_agreesOnFV
      (t := x) (h1 := hcov_x') (h2 := hcov_x) hagree).trans hden_x
  have respects_x_Gamma :
      SMT.RenamingContext.RespectsTypeContextOnFV Theta Gamma x :=
    respects_x.of_extends (RenamingContext.extends_refl Theta)
      Lambda_sub typ_x
  have respects_x' :
      SMT.RenamingContext.RespectsTypeContextOnFV Theta' Gamma x := by
    intro v sigma hv hlookup
    have hv_ne : v ≠ helper := fun h => by
      subst v
      exact helper_not_fv_x hv
    obtain ⟨d, hd, hdty⟩ := respects_x_Gamma hv hlookup
    exact ⟨d, by simpa [Theta', Function.update_of_ne hv_ne] using hd,
      hdty⟩
  have hcov_var : RenamingContext.CoversFV Theta' (.var helper) := by
    intro v hv
    simp only [SMT.fv, List.mem_singleton] at hv
    subst v
    simp [Theta']
  have hden_var' : ⟦(SMT.Term.var helper).abstract Theta' hcov_var⟧ˢ =
      some H := by
    simpa only [Theta', proof_irrel_heq] using hden_var
  have respects_var :
      SMT.RenamingContext.RespectsTypeContextOnFV Theta' Gamma
        (.var helper) := by
    intro v sigma hv hlookup
    simp only [SMT.fv, List.mem_singleton] at hv
    subst v
    rw [helper_lookup] at hlookup
    cases hlookup
    exact ⟨H, by simp [Theta'], Hty⟩
  have Hmem : H.fst ∈ ⟦SMTType.fun gamma.toSMTType
      (SMTType.option alpha.toSMTType)⟧ᶻ := by
    rw [← Hty]
    exact H.snd.snd
  have hcast : castZF_apply c G = H.fst :=
    castZF_apply_eq_of_pair c hG castPair
  have H_eq_G : H.fst = G := by
    rw [castZF_apply_self c hG] at hcast
    exact hcast.symm
  have FrelH : RDomCastSupported
      (⟨F, BType.set (gamma ×ᴮ alpha), hF⟩ : B.Dom)
      (⟨H.fst, SMTType.fun gamma.toSMTType
        (SMTType.option alpha.toSMTType), Hmem⟩ : SMT.Dom) := by
    have hdomEq :
        (⟨H.fst, SMTType.fun gamma.toSMTType
          (SMTType.option alpha.toSMTType), Hmem⟩ : SMT.Dom) =
        (⟨G, SMTType.fun gamma.toSMTType
          (SMTType.option alpha.toSMTType), hG⟩ : SMT.Dom) := by
      cases H_eq_G
      rfl
    rw [hdomEq]
    exact Frel
  have Heq : H =
      (⟨H.fst, SMTType.fun gamma.toSMTType
        (SMTType.option alpha.toSMTType), Hmem⟩ : SMT.Dom) := by
    rcases H with ⟨Hv, Hsigma, hHv⟩
    dsimp at Hty
    subst Hsigma
    rfl
  have hden_var_fun :
      ⟦(SMT.Term.var helper).abstract Theta' hcov_var⟧ˢ =
        some (⟨H.fst, SMTType.fun gamma.toSMTType
          (SMTType.option alpha.toSMTType), Hmem⟩ : SMT.Dom) := by
    rw [← Heq]
    exact hden_var'
  obtain ⟨hcov_out, denOut, respects_out, hden_out,
      denOutTy, resultRel⟩ :=
    castApp_option_term_semantics hcov_var hcov_x' respects_var
      respects_x' hden_var_fun hden_x' FrelH Xrel hmem
  have respects_f_Gamma :
      SMT.RenamingContext.RespectsTypeContextOnFV Theta Gamma f :=
    respects_f.of_extends (RenamingContext.extends_refl Theta)
      Lambda_sub typ_f
  have respects_spec :
      SMT.RenamingContext.RespectsTypeContextOnFV Theta' Gamma spec :=
    SMT.RenamingContext.respects_update_helper spec_fv
      respects_f_Gamma helper_lookup Hty
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
      (helperSpecChunk helper
        (SMTType.fun gamma.toSMTType
          (SMTType.option alpha.toSMTType)) spec) := by
    intro body hbody
    simp only [specBodies_helperSpecChunk, List.mem_singleton] at hbody
    subst body
    exact ⟨hcov_spec, Phi, respects_spec, hden_spec, Phity, PhiTrue⟩
  exact ⟨Theta', hcov_out, denOut, Theta'_ext, Theta'_none,
    respects_out, Theta'_dom, specs_true, hden_out, denOutTy, resultRel⟩

theorem castApp_option_fun_guarded_semantics.{u}
    {gamma alpha : BType} {f x spec : SMT.Term}
    {Lambda GammaSup : SMT.TypeContext} {helper : SMT.𝒱}
    (scope : ScopedContextExtends Lambda
      (helperSpecChunk helper
        (SMTType.fun gamma.toSMTType
          (SMTType.option alpha.toSMTType)) spec) GammaSup)
    (c : SMTType.fun gamma.toSMTType
      (SMTType.option alpha.toSMTType) ~>
      SMTType.fun gamma.toSMTType
        (SMTType.option alpha.toSMTType))
    (exactness :
      ∀ (Theta : SMT.RenamingContext.Context.{u})
        (hf : RenamingContext.CoversFV Theta f)
        (_respects : SMT.RenamingContext.RespectsTypeContextOnFV
          Theta Lambda f)
        (pf : ∀ (x_ : SMT.𝒱) (X_ : SMT.Dom),
          ∀ v ∈ SMT.fv (SMT.Term.var x_),
            (Function.update Theta x_ (some X_) v).isSome = true),
      ∀ (denF : SMT.Dom), ⟦f.abstract Theta hf⟧ˢ = some denF →
        ∃ (Phi H : SMT.Dom)
          (_ : ⟦(SMT.Term.var helper).abstract
            (Function.update Theta helper (some H)) (pf helper H)⟧ˢ =
              some H)
          (hphi : RenamingContext.CoversFV
            (Function.update Theta helper (some H)) spec)
          (_ : ⟦spec.abstract (Function.update Theta helper (some H))
            hphi⟧ˢ = some Phi),
          H.snd.fst = SMTType.fun gamma.toSMTType
            (SMTType.option alpha.toSMTType) ∧
          Phi.snd.fst = SMTType.bool ∧
          (Phi.fst = zftrue ∧
            denF.fst.pair H.fst ∈ (castZF_of_path c).1) ∧
          (∀ (Y : SMT.Dom)
            (_ : Y.snd.fst = SMTType.fun gamma.toSMTType
              (SMTType.option alpha.toSMTType))
            (hphiY : RenamingContext.CoversFV
              (Function.update Theta helper (some Y)) spec),
            (⟦spec.abstract (Function.update Theta helper (some Y))
              hphiY⟧ˢ).isSome = true ∧
            ∀ {PhiY : SMT.Dom},
              ⟦spec.abstract (Function.update Theta helper (some Y))
                hphiY⟧ˢ = some PhiY →
              PhiY.fst = zftrue →
              denF.fst.pair Y.fst ∈ (castZF_of_path c).1))
    {Theta : SMT.RenamingContext.Context.{u}}
    (hcov_f : RenamingContext.CoversFV Theta f)
    (hcov_x : RenamingContext.CoversFV Theta x)
    (respects_f : SMT.RenamingContext.RespectsTypeContextOnFV
      Theta GammaSup f)
    (respects_x : SMT.RenamingContext.RespectsTypeContextOnFV
      Theta GammaSup x)
    {F X T G Y : ZFSet.{u}}
    {hF : F ∈ ⟦BType.set (gamma ×ᴮ alpha)⟧ᶻ}
    {hX : X ∈ ⟦gamma⟧ᶻ} {hT : T ∈ ⟦alpha⟧ᶻ}
    {hG : G ∈ ⟦SMTType.fun gamma.toSMTType
      (SMTType.option alpha.toSMTType)⟧ᶻ}
    {hY : Y ∈ ⟦gamma.toSMTType⟧ᶻ}
    (hden_f : ⟦f.abstract Theta hcov_f⟧ˢ =
      some (⟨G, SMTType.fun gamma.toSMTType
        (SMTType.option alpha.toSMTType), hG⟩ : SMT.Dom))
    (hden_x : ⟦x.abstract Theta hcov_x⟧ˢ =
      some (⟨Y, gamma.toSMTType, hY⟩ : SMT.Dom))
    (Frel : RDomCastSupported
      (⟨F, BType.set (gamma ×ᴮ alpha), hF⟩ : B.Dom)
      (⟨G, SMTType.fun gamma.toSMTType
        (SMTType.option alpha.toSMTType), hG⟩ : SMT.Dom))
    (Xrel : RDomCastSupported (⟨X, gamma, hX⟩ : B.Dom)
      (⟨Y, gamma.toSMTType, hY⟩ : SMT.Dom))
    (hmem : X.pair T ∈ F)
    (hcov_out : RenamingContext.CoversFV Theta
      (SMT.Term.the (SMT.Term.app (.var helper) x)))
    (denOut : SMT.Dom.{u})
    (respects_out : SMT.RenamingContext.RespectsTypeContextOnFV
      Theta GammaSup
      (SMT.Term.the (SMT.Term.app (.var helper) x)))
    (specs_true : SpecBodiesTrue Theta GammaSup
      (helperSpecChunk helper
        (SMTType.fun gamma.toSMTType
          (SMTType.option alpha.toSMTType)) spec))
    (hden_out :
      ⟦(SMT.Term.the (SMT.Term.app (.var helper) x)).abstract
        Theta hcov_out⟧ˢ = some denOut)
    (_denOutTy : denOut.snd.fst = alpha.toSMTType) :
    RDomCastSupported (⟨T, alpha, hT⟩ : B.Dom) denOut := by
  have respects_f_base :
      SMT.RenamingContext.RespectsTypeContextOnFV Theta Lambda f :=
    respects_f.of_super scope.base
  let pf : ∀ (x_ : SMT.𝒱) (H : SMT.Dom),
      ∀ v ∈ SMT.fv (SMT.Term.var x_),
        (Function.update Theta x_ (some H) v).isSome = true := by
    intro x_ H v hv
    simp only [SMT.fv, List.mem_singleton] at hv
    subst v
    simp
  obtain ⟨_PhiW, _HW, _hdenVarW, _hcovSpecW, _hdenSpecW,
      _HWty, _PhiWty, _castW, guard⟩ :=
    exactness Theta hcov_f respects_f_base pf
      (⟨G, SMTType.fun gamma.toSMTType
        (SMTType.option alpha.toSMTType), hG⟩ : SMT.Dom) hden_f
  have helper_some : (Theta helper).isSome = true := by
    apply hcov_out helper
    simp only [SMT.fv, List.mem_append, List.mem_singleton]
    exact Or.inl trivial
  obtain ⟨H, hH⟩ := Option.isSome_iff_exists.mp helper_some
  have helper_fv_out : helper ∈ SMT.fv
      (SMT.Term.the (SMT.Term.app (.var helper) x)) := by
    simp only [SMT.fv, List.mem_append, List.mem_singleton]
    exact Or.inl trivial
  have helper_lookup : GammaSup.lookup helper = some
      (SMTType.fun gamma.toSMTType
        (SMTType.option alpha.toSMTType)) :=
    scope.lookup_of_declared (by
      simp [declEntries_helperSpecChunk])
  have Hty : H.snd.fst = SMTType.fun gamma.toSMTType
      (SMTType.option alpha.toSMTType) := by
    obtain ⟨d, hd, hdty⟩ :=
      respects_out helper_fv_out helper_lookup
    rw [hH] at hd
    injection hd with hdeq
    subst d
    exact hdty
  have hupdate : Function.update Theta helper (some H) = Theta := by
    rw [← hH]
    exact Function.update_eq_self helper Theta
  have hspec_true := specs_true spec (by simp)
  obtain ⟨hcov_spec, denSpec, _respects_spec, hden_spec,
      _denSpecTy, denSpecTrue⟩ := hspec_true
  have hcov_spec_update : RenamingContext.CoversFV
      (Function.update Theta helper (some H)) spec := by
    rw [hupdate]
    exact hcov_spec
  obtain ⟨_some, castPair⟩ := guard H Hty hcov_spec_update
  have hden_spec_update :
      ⟦spec.abstract (Function.update Theta helper (some H))
        hcov_spec_update⟧ˢ = some denSpec := by
    simpa only [hupdate, proof_irrel_heq] using hden_spec
  have castPair' := castPair hden_spec_update denSpecTrue
  have Hmem : H.fst ∈ ⟦SMTType.fun gamma.toSMTType
      (SMTType.option alpha.toSMTType)⟧ᶻ := by
    rw [← Hty]
    exact H.snd.snd
  have hcast : castZF_apply c G = H.fst :=
    castZF_apply_eq_of_pair c hG castPair'
  have H_eq_G : H.fst = G := by
    rw [castZF_apply_self c hG] at hcast
    exact hcast.symm
  have FrelH : RDomCastSupported
      (⟨F, BType.set (gamma ×ᴮ alpha), hF⟩ : B.Dom)
      (⟨H.fst, SMTType.fun gamma.toSMTType
        (SMTType.option alpha.toSMTType), Hmem⟩ : SMT.Dom) := by
    have hdomEq :
        (⟨H.fst, SMTType.fun gamma.toSMTType
          (SMTType.option alpha.toSMTType), Hmem⟩ : SMT.Dom) =
        (⟨G, SMTType.fun gamma.toSMTType
          (SMTType.option alpha.toSMTType), hG⟩ : SMT.Dom) := by
      cases H_eq_G
      rfl
    rw [hdomEq]
    exact Frel
  have hcov_var : RenamingContext.CoversFV Theta (.var helper) := by
    intro v hv
    simp only [SMT.fv, List.mem_singleton] at hv
    subst v
    exact helper_some
  have hden_var : ⟦(SMT.Term.var helper).abstract Theta hcov_var⟧ˢ =
      some (⟨H.fst, SMTType.fun gamma.toSMTType
        (SMTType.option alpha.toSMTType), Hmem⟩ : SMT.Dom) := by
    rw [SMT.Term.abstract.eq_def]
    simp only [SMT.denote]
    have hget := Option.get_of_eq_some helper_some hH
    rw [hget]
    rcases H with ⟨Hv, Hsigma, hHv⟩
    dsimp at Hty
    subst Hsigma
    rfl
  have respects_var :
      SMT.RenamingContext.RespectsTypeContextOnFV Theta GammaSup
        (.var helper) := by
    intro v sigma hv hlookup
    simp only [SMT.fv, List.mem_singleton] at hv
    subst v
    rw [helper_lookup] at hlookup
    cases hlookup
    exact ⟨H, hH, Hty⟩
  obtain ⟨hcov_expected, denExpected, _respects_expected,
      hden_expected, _denExpectedTy, expectedRel⟩ :=
    castApp_option_term_semantics hcov_var hcov_x respects_var
      respects_x hden_var hden_x FrelH Xrel hmem
  have hcov_eq : hcov_expected = hcov_out := Subsingleton.elim _ _
  subst hcov_expected
  rw [hden_out] at hden_expected
  have hden_eq : denExpected = denOut :=
    (Option.some.inj hden_expected).symm
  rw [← hden_eq]
  exact expectedRel

set_option maxHeartbeats 4000000 in
theorem castApp_option_fun_scoped_contract.{u}
    (gamma alpha : BType) (f x : SMT.Term)
    (hle : gamma.toSMTType ⊑ gamma.toSMTType) :
    CastAppRepScopedSpec.{u} gamma alpha f x
      (SMTType.fun gamma.toSMTType
        (SMTType.option alpha.toSMTType)) gamma.toSMTType := by
  unfold CastAppRepScopedSpec
  intro Lambda n used decl typ_f typ_x bv_f_used bv_x_used
  let cfun : SMTType.fun gamma.toSMTType
      (SMTType.option alpha.toSMTType) ~>
      SMTType.fun gamma.toSMTType
        (SMTType.option alpha.toSMTType) :=
    castPath.fun (by nofun) hle.toCastPath
      (castPath.reflexive (SMTType.option alpha.toSMTType))
  mstart
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_keys, St_used_eq, St_decl_eq⟩ := pre
  simp only [castApp]
  rw [dif_pos hle]
  mspec (Std.Do.Triple.and _
    (Std.Do.Triple.and _
      (Std.Do.Triple.and _
        (loosenAux_prf_exact_univ
          (Λ := St.types) (n := St.env.freshvarsc)
          (used := St.env.usedVars) typ_f
          (fun v hv => St_used_eq ▸ bv_f_used v hv) cfun)
        (loosenAux_prf_fv_of_faithful (castPath.fvFaithful cfun)
          (used := St.env.usedVars) (n := St.env.freshvarsc)
          (x := f) (by
            intro v hv
            exact St_keys (SMT.Typing.mem_context_of_mem_fv typ_f hv))))
      (loosenAux_prf_decls cfun (decl := decl)))
    (loosenAux_prf_types_eq cfun))
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
    (x!_spec := spec)
    (τ := SMTType.fun gamma.toSMTType
      (SMTType.option alpha.toSMTType))
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
  have typ_x1 : St1.types ⊢ˢ x : gamma.toSMTType :=
    SMT.Typing.weakening Lambda_sub1 typ_x
      (fun v hv => preserves1 v (St_used_eq ▸ bv_x_used v hv)
        (SMT.Typing.bv_notMem_context typ_x v hv))
  have typOut : St1.types ⊢ˢ
      (SMT.Term.the (SMT.Term.app (.var helper) x)) :
        alpha.toSMTType := by
    apply SMT.Typing.the
    apply SMT.Typing.app
    · exact typ_helper
    · exact typ_x1
  have helper_lookup : St1.types.lookup helper = some
      (SMTType.fun gamma.toSMTType
        (SMTType.option alpha.toSMTType)) :=
    SMT.Typing.varE typ_helper
  have helper_used1 : helper ∈ St1.env.usedVars :=
    keys_sub1 (AList.lookup_isSome.mp
      (Option.isSome_of_eq_some helper_lookup))
  have helper_ctx_gen : ContextGeneratedByDeclarations St.types St1.types
      (helperSpecChunk helper
        (SMTType.fun gamma.toSMTType
          (SMTType.option alpha.toSMTType)) spec) := by
    rw [St1_types_exact]
    exact ContextGeneratedByDeclarations.insert_helper
      St.types helper _ spec helper_fresh
  have helper_ctx_trace : DeclarationContextTrace St.types
      (helperSpecChunk helper
        (SMTType.fun gamma.toSMTType
          (SMTType.option alpha.toSMTType)) spec) St1.types := by
    rw [St1_types_exact]
    exact DeclarationContextTrace.helperSpecChunk
      St.types helper _ spec helper_fresh
  have used_sub_out : used ⊆ St1.env.usedVars := by
    simpa [St_used_eq] using used_sub1
  have preserves_out : ∀ v ∈ used, v ∉ St.types → v ∉ St1.types := by
    simpa [St_used_eq] using preserves1
  have helper_not_used_out : helper ∉ used := by
    simpa [St_used_eq] using helper_not_used
  mpure_intro
  rw [St2_used, St2_types]
  refine ⟨used_sub_out, Lambda_sub1, keys_sub1, True.intro, typOut,
    preserves_out, helperSpecChunk helper
      (SMTType.fun gamma.toSMTType
        (SMTType.option alpha.toSMTType)) spec, ?_,
    helper_ctx_gen, helper_ctx_trace, ?_, ?_, ?_, ?_⟩
  · rw [St2_decl_eq, St1_decl_eq]
    simp [helperSpecChunk, List.concat_eq_append, List.append_assoc]
  · intro v hv
    simp only [declVars_helperSpecChunk, List.mem_singleton] at hv
    subst v
    exact helper_not_used_out
  · intro GammaSup GammaSub Theta hcov_f hcov_x Theta_none
      respects_f respects_x Theta_dom F X T hF hX hT hfun hdom
      hresult denF denX hden_f hden_x hdenFty hdenXty Frel Xrel
    have Lambda_sub_sup : St.types ⊆ GammaSup :=
      AList.subset_trans Lambda_sub1 GammaSub
    have respects_f_base :
        SMT.RenamingContext.RespectsTypeContextOnFV Theta St.types f :=
      respects_f.of_super Lambda_sub_sup
    have respects_x_base :
        SMT.RenamingContext.RespectsTypeContextOnFV Theta St.types x :=
      respects_x.of_super Lambda_sub_sup
    have helper_lookup_sup : GammaSup.lookup helper = some
        (SMTType.fun gamma.toSMTType
          (SMTType.option alpha.toSMTType)) :=
      AList.lookup_of_subset GammaSub helper_lookup
    rcases denF with ⟨G, sigmaF, hG⟩
    rcases denX with ⟨Y, sigmaX, hY⟩
    dsimp at hdenFty hdenXty
    subst sigmaF
    subst sigmaX
    have hmem : X.pair T ∈ F := by
      rw [← hresult]
      exact ZFSet.fapply.def hfun hdom
    constructor
    · exact castApp_option_fun_semantics typ_f typ_x Lambda_sub_sup
        helper_fresh helper_lookup_sup helper_not_used_out
        helper_used1 used_sub_out spec_fv cfun exactness
        hcov_f hcov_x Theta_none respects_f_base respects_x_base
        Theta_dom hden_f hden_x Frel Xrel hmem
    · intro GammaSupG scopeG ThetaG hcov_fG hcov_xG
        respects_fG respects_xG FG XG TG hFG hXG hTG hfunG hdomG
        hresultG denFG denXG hden_fG hden_xG hdenFGty hdenXGty
        FrelG XrelG hcov_outG denOutG respects_outG specs_trueG
        hden_outG denOutGTy
      rcases denFG with ⟨GG, sigmaFG, hGG⟩
      rcases denXG with ⟨YG, sigmaXG, hYG⟩
      dsimp at hdenFGty hdenXGty
      subst sigmaFG
      subst sigmaXG
      have hmemG : XG.pair TG ∈ FG := by
        rw [← hresultG]
        exact ZFSet.fapply.def hfunG hdomG
      exact castApp_option_fun_guarded_semantics scopeG cfun exactness
        hcov_fG hcov_xG respects_fG respects_xG hden_fG hden_xG
        FrelG XrelG hmemG hcov_outG denOutG respects_outG specs_trueG
        hden_outG denOutGTy
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

theorem castApp_option_supported_rep_scoped_contract.{u}
    (gamma alpha : BType) (f x : SMT.Term) (sx : SMTType)
    (supported_x : BType.SupportedSMT gamma sx) :
    CastAppRepScopedSpec.{u} gamma alpha f x
      (SMTType.fun gamma.toSMTType
        (SMTType.option alpha.toSMTType)) sx := by
  by_cases hforward : gamma.toSMTType ⊑ sx
  · have hsx := supported_x.eq_canonical_of_cast_from_canonical
      hforward.toCastPath
    subst sx
    exact castApp_option_fun_scoped_contract gamma alpha f x hforward
  · let hback : sx ⊑ gamma.toSMTType :=
      castable?_of_castPath supported_x.toCanonicalCastPath
    exact castApp_option_arg_scoped_contract gamma alpha f x sx
      hforward hback (supported_x.toCastPath_faithful hback)

/-- Canonical characteristic-predicate representation preserves the partial
function property of a source graph. -/
theorem RDomCastSupported.setPred_isPFunc_of_source.{u}
    {gamma alpha : BType} {F R : ZFSet.{u}}
    {hF : F ∈ ⟦BType.set (gamma ×ᴮ alpha)⟧ᶻ}
    {hR : R ∈ ⟦SMTType.fun
      (SMTType.pair gamma.toSMTType alpha.toSMTType)
      SMTType.bool⟧ᶻ}
    (Frel : RDomCastSupported
      (⟨F, BType.set (gamma ×ᴮ alpha), hF⟩ : B.Dom)
      (⟨R, SMTType.fun
        (SMTType.pair gamma.toSMTType alpha.toSMTType)
        SMTType.bool, hR⟩ : SMT.Dom))
    (hfun : F.IsPFunc ⟦gamma⟧ᶻ ⟦alpha⟧ᶻ) :
    (predGraph gamma.toSMTType alpha.toSMTType R).IsPFunc
      ⟦gamma.toSMTType⟧ᶻ ⟦alpha.toSMTType⟧ᶻ := by
  have hRfunc : ⟦SMTType.pair gamma.toSMTType alpha.toSMTType⟧ᶻ.IsFunc
      ZFSet.𝔹 R := by
    simpa [SMTType.toZFSet] using hR
  have hRret : retract (BType.set (gamma ×ᴮ alpha)) R = F :=
    ((RDomCast.iff_RDom_of_type_eq
      (α := BType.set (gamma ×ᴮ alpha)) rfl).mp
      Frel.toRDomCast).2
  constructor
  · intro ab hab
    exact (ZFSet.mem_sep.mp hab).1
  · intro a b hab b' hab'
    have habProd := (ZFSet.mem_sep.mp hab).1
    have hab'Prod := (ZFSet.mem_sep.mp hab').1
    obtain ⟨ha, hb⟩ := ZFSet.pair_mem_prod.mp habProd
    obtain ⟨_ha', hb'⟩ := ZFSet.pair_mem_prod.mp hab'Prod
    have habRaw := (ZFSet.mem_sep.mp hab).2
    have hab'Raw := (ZFSet.mem_sep.mp hab').2
    have habDom : a.pair b ∈ R.Dom := by
      rw [ZFSet.is_func_dom_eq hRfunc]
      exact habProd
    have hab'Dom : a.pair b' ∈ R.Dom := by
      rw [ZFSet.is_func_dom_eq hRfunc]
      exact hab'Prod
    have happ :
        (fapply R (is_func_is_pfunc hRfunc)
          ⟨a.pair b, habDom⟩).val = ZFSet.zftrue := by
      exact Subtype.ext_iff.mp
        (ZFSet.fapply.of_pair (is_func_is_pfunc hRfunc) habRaw)
    have happ' :
        (fapply R (is_func_is_pfunc hRfunc)
          ⟨a.pair b', hab'Dom⟩).val = ZFSet.zftrue := by
      exact Subtype.ext_iff.mp
        (ZFSet.fapply.of_pair (is_func_is_pfunc hRfunc) hab'Raw)
    have hretPair : retract (gamma ×ᴮ alpha) (a.pair b) =
        (retract gamma a).pair (retract alpha b) := by
      simp [retract]
    have hretPair' : retract (gamma ×ᴮ alpha) (a.pair b') =
        (retract gamma a).pair (retract alpha b') := by
      simp [retract]
    have hmem : (retract gamma a).pair (retract alpha b) ∈ F := by
      have hiff := RDomCast.setPred_apply_eq_zftrue_iff
        (τ := gamma ×ᴮ alpha)
        (X := (retract gamma a).pair (retract alpha b))
        (S := F) (Y := a.pair b) (F := R)
        (ZFSet.pair_mem_prod.mpr
          ⟨retract_mem_of_canonical gamma ha,
            retract_mem_of_canonical alpha hb⟩)
        habProd hR hretPair hRret
      exact hiff.mp happ
    have hmem' : (retract gamma a).pair (retract alpha b') ∈ F := by
      have hiff := RDomCast.setPred_apply_eq_zftrue_iff
        (τ := gamma ×ᴮ alpha)
        (X := (retract gamma a).pair (retract alpha b'))
        (S := F) (Y := a.pair b') (F := R)
        (ZFSet.pair_mem_prod.mpr
          ⟨retract_mem_of_canonical gamma ha,
            retract_mem_of_canonical alpha hb'⟩)
        hab'Prod hR hretPair' hRret
      exact hiff.mp happ'
    have hretEq : retract alpha b = retract alpha b' :=
      hfun.2 (retract gamma a) (retract alpha b) hmem
        (retract alpha b') hmem'
    rw [← canonical_of_retract alpha hb,
      ← canonical_of_retract alpha hb']
    congr

private theorem denote_app_var_exact.{u}
    {sigma tau : SMTType} (WF WX : SMT.Dom.{u})
    (hWF_ty : WF.snd.fst = SMTType.fun sigma tau)
    (hWX_ty : WX.snd.fst = sigma) :
    let hfunc : ZFSet.IsFunc ⟦sigma⟧ᶻ ⟦tau⟧ᶻ WF.fst := by
      have hmem := WF.snd.snd
      rw [hWF_ty, SMTType.toZFSet] at hmem
      exact ZFSet.mem_funs.mp hmem
    let hdom : WX.fst ∈ WF.fst.Dom := by
      rw [ZFSet.is_func_dom_eq hfunc, ← hWX_ty]
      exact WX.snd.snd
    ∃ D : SMT.Dom.{u},
      ⟦SMT.PHOAS.Term.app (.var WF) (.var WX)⟧ˢ = some D ∧
      D.snd.fst = tau ∧
      D.fst = (ZFSet.fapply WF.fst (ZFSet.is_func_is_pfunc hfunc)
        ⟨WX.fst, hdom⟩).val := by
  dsimp only
  let hfunc : ZFSet.IsFunc ⟦sigma⟧ᶻ ⟦tau⟧ᶻ WF.fst := by
    have hmem := WF.snd.snd
    rw [hWF_ty, SMTType.toZFSet] at hmem
    exact ZFSet.mem_funs.mp hmem
  let hdom : WX.fst ∈ WF.fst.Dom := by
    rw [ZFSet.is_func_dom_eq hfunc, ← hWX_ty]
    exact WX.snd.snd
  let Y := ZFSet.fapply WF.fst (ZFSet.is_func_is_pfunc hfunc) ⟨WX.fst, hdom⟩
  refine ⟨⟨Y.val, tau, Y.property⟩, ?_, rfl, rfl⟩
  show SMT.denote (SMT.PHOAS.Term.app (.var WF) (.var WX)) = _
  simp only [SMT.denote, Option.pure_def]
  obtain ⟨F, sigmaF, hF⟩ := WF
  obtain ⟨X, sigmaX, hX⟩ := WX
  dsimp at hWF_ty hWX_ty hfunc hdom Y ⊢
  subst sigmaF
  subst sigmaX
  simp only [dif_pos (ZFSet.is_func_is_pfunc hfunc), dif_pos hdom, ite_true]
  rfl

private theorem denote_some_var_exact.{u}
    {tau : SMTType} (W : SMT.Dom.{u})
    (hW_ty : W.snd.fst = tau) :
    let hmem : W.fst ∈ ⟦tau⟧ᶻ := by
      rw [← hW_ty]
      exact W.snd.snd
    ∃ D : SMT.Dom.{u},
      ⟦SMT.PHOAS.Term.some (.var W)⟧ˢ = some D ∧
      D.snd.fst = SMTType.option tau ∧
      D.fst = (ZFSet.Option.some ⟨W.fst, hmem⟩).val := by
  dsimp only
  let hmem : W.fst ∈ ⟦tau⟧ᶻ := by
    rw [← hW_ty]
    exact W.snd.snd
  refine ⟨⟨(ZFSet.Option.some ⟨W.fst, hmem⟩).val,
    SMTType.option tau, SetLike.coe_mem _⟩, ?_, rfl, rfl⟩
  obtain ⟨w, sigmaW, hw⟩ := W
  dsimp at hW_ty hmem ⊢
  subst sigmaW
  simp only [SMT.denote, Option.pure_def]
  congr

theorem zfBool_eq_of_true_iff.{u} {P Q : ZFSet.{u}}
    (hP : P ∈ ZFSet.𝔹) (hQ : Q ∈ ZFSet.𝔹)
    (hiff : P = ZFSet.zftrue ↔ Q = ZFSet.zftrue) : P = Q := by
  rcases ZFSet.ZFBool.mem_𝔹_iff P |>.mp hP with hPf | hPt
  · rcases ZFSet.ZFBool.mem_𝔹_iff Q |>.mp hQ with hQf | hQt
    · exact hPf.trans hQf.symm
    · exact False.elim (ZFSet.zftrue_ne_zffalse
        ((hiff.mpr hQt).symm.trans hPf))
  · rcases ZFSet.ZFBool.mem_𝔹_iff Q |>.mp hQ with hQf | hQt
    · exact False.elim (ZFSet.zftrue_ne_zffalse
        ((hiff.mp hPt).symm.trans hQf))
    · exact hPt.trans hQt.symm

private theorem relation_option_body_denote.{u}
    (gamma alpha : SMTType) {R G a b : ZFSet.{u}}
    (hR : R ∈ ⟦SMTType.fun (SMTType.pair gamma alpha) SMTType.bool⟧ᶻ)
    (hG : G ∈ ⟦SMTType.fun gamma (SMTType.option alpha)⟧ᶻ)
    (ha : a ∈ ⟦gamma⟧ᶻ) (hb : b ∈ ⟦alpha⟧ᶻ) :
    let WR : SMT.Dom.{u} := ⟨R,
      SMTType.fun (SMTType.pair gamma alpha) SMTType.bool, hR⟩
    let WG : SMT.Dom.{u} := ⟨G,
      SMTType.fun gamma (SMTType.option alpha), hG⟩
    let Wa : SMT.Dom.{u} := ⟨a, gamma, ha⟩
    let Wb : SMT.Dom.{u} := ⟨b, alpha, hb⟩
    let hRfunc : ZFSet.IsFunc ⟦SMTType.pair gamma alpha⟧ᶻ ZFSet.𝔹 R := by
      simpa [SMTType.toZFSet] using hR
    let hab : a.pair b ∈ ⟦SMTType.pair gamma alpha⟧ᶻ :=
      ZFSet.pair_mem_prod.mpr ⟨ha, hb⟩
    let hRdom : a.pair b ∈ R.Dom := by
      rw [ZFSet.is_func_dom_eq hRfunc]
      exact hab
    let Rapp := ZFSet.fapply R (ZFSet.is_func_is_pfunc hRfunc)
      ⟨a.pair b, hRdom⟩
    let hGfunc : ZFSet.IsFunc ⟦gamma⟧ᶻ ⟦SMTType.option alpha⟧ᶻ G := by
      simpa [SMTType.toZFSet] using hG
    let hGdom : a ∈ G.Dom := by
      rw [ZFSet.is_func_dom_eq hGfunc]
      exact ha
    let Gapp := ZFSet.fapply G (ZFSet.is_func_is_pfunc hGfunc)
      ⟨a, hGdom⟩
    let someb := ZFSet.Option.some (S := ⟦alpha⟧ᶻ) ⟨b, hb⟩
    ∃ D : SMT.Dom.{u},
      ⟦SMT.PHOAS.Term.eq
        (.app (.var WR) (.pair (.var Wa) (.var Wb)))
        (.eq (.app (.var WG) (.var Wa)) (.some (.var Wb)))⟧ˢ = some D ∧
      D.snd.fst = SMTType.bool ∧
      (D.fst = ZFSet.zftrue ↔
        Rapp.val = zfEqIn ⟦SMTType.option alpha⟧ᶻ Gapp.val someb.val) := by
  dsimp only
  let WR : SMT.Dom.{u} := ⟨R,
    SMTType.fun (SMTType.pair gamma alpha) SMTType.bool, hR⟩
  let WG : SMT.Dom.{u} := ⟨G,
    SMTType.fun gamma (SMTType.option alpha), hG⟩
  let Wa : SMT.Dom.{u} := ⟨a, gamma, ha⟩
  let Wb : SMT.Dom.{u} := ⟨b, alpha, hb⟩
  let hRfunc : ZFSet.IsFunc ⟦SMTType.pair gamma alpha⟧ᶻ ZFSet.𝔹 R := by
    simpa [SMTType.toZFSet] using hR
  let hab : a.pair b ∈ ⟦SMTType.pair gamma alpha⟧ᶻ :=
    ZFSet.pair_mem_prod.mpr ⟨ha, hb⟩
  let hRdom : a.pair b ∈ R.Dom := by
    rw [ZFSet.is_func_dom_eq hRfunc]
    exact hab
  let Rapp := ZFSet.fapply R (ZFSet.is_func_is_pfunc hRfunc)
    ⟨a.pair b, hRdom⟩
  let hGfunc : ZFSet.IsFunc ⟦gamma⟧ᶻ ⟦SMTType.option alpha⟧ᶻ G := by
    simpa [SMTType.toZFSet] using hG
  let hGdom : a ∈ G.Dom := by
    rw [ZFSet.is_func_dom_eq hGfunc]
    exact ha
  let Gapp := ZFSet.fapply G (ZFSet.is_func_is_pfunc hGfunc)
    ⟨a, hGdom⟩
  let someb := ZFSet.Option.some (S := ⟦alpha⟧ᶻ) ⟨b, hb⟩
  change ∃ D : SMT.Dom.{u},
    ⟦SMT.PHOAS.Term.eq
      (.app (.var WR) (.pair (.var Wa) (.var Wb)))
      (.eq (.app (.var WG) (.var Wa)) (.some (.var Wb)))⟧ˢ = some D ∧
    D.snd.fst = SMTType.bool ∧
    (D.fst = ZFSet.zftrue ↔
      Rapp.val = zfEqIn ⟦SMTType.option alpha⟧ᶻ Gapp.val someb.val)
  obtain ⟨DR, hdenR, hDRty, hDRval⟩ :=
    denote_app_var_exact WR ⟨Wa.fst.pair Wb.fst,
      SMTType.pair gamma alpha, ZFSet.pair_mem_prod.mpr ⟨ha, hb⟩⟩ rfl rfl
  obtain ⟨DG, hdenG, hDGty, hDGval⟩ :=
    denote_app_var_exact WG Wa rfl rfl
  obtain ⟨DS, hdenS, hDSty, hDSval⟩ :=
    denote_some_var_exact Wb rfl
  obtain ⟨DI, hdenI, hDIty⟩ :=
    denote_eq_some_of_some hdenG hdenS (by rw [hDGty, hDSty])
  obtain ⟨DO, hdenO, hDOty⟩ :=
    denote_eq_some_of_some hdenR hdenI (by rw [hDRty, hDIty])
  have hDIsem : DI.fst = zfEqIn ⟦SMTType.option alpha⟧ᶻ
      Gapp.val someb.val := by
    apply zfBool_eq_of_true_iff
    · have hmem := DI.snd.snd
      rwa [hDIty] at hmem
    · exact overloadBinOp_mem Gapp.property someb.property
    · rw [denote_eq_fst_eq_zftrue_iff hdenG hdenS
          (by rw [hDGty, hDSty]) hdenI,
        zfEqIn_eq_zftrue_iff Gapp.property someb.property,
        hDGval, hDSval]
  refine ⟨DO, hdenO, hDOty, ?_⟩
  rw [denote_eq_fst_eq_zftrue_iff hdenR hdenI
      (by rw [hDRty, hDIty]) hdenO,
    hDRval, hDIsem]

/-- The option function obtained by collapsing a functional characteristic
predicate satisfies the pointwise graph equation emitted by `castApp`. -/
theorem graphCollapse_pointwise_spec.{u}
    (gamma alpha : SMTType) {R : ZFSet.{u}}
    (hR : R ∈ ⟦SMTType.fun (SMTType.pair gamma alpha)
      SMTType.bool⟧ᶻ)
    (hfun : (predGraph gamma alpha R).IsPFunc
      ⟦gamma⟧ᶻ ⟦alpha⟧ᶻ)
    {a b : ZFSet.{u}} (ha : a ∈ ⟦gamma⟧ᶻ)
    (hb : b ∈ ⟦alpha⟧ᶻ) :
    let Rapp := fapply R (is_func_is_pfunc (by
      simpa [SMTType.toZFSet] using hR :
        ⟦SMTType.pair gamma alpha⟧ᶻ.IsFunc ZFSet.𝔹 R))
      ⟨a.pair b, by
        rw [is_func_dom_eq (by
          simpa [SMTType.toZFSet] using hR :
            ⟦SMTType.pair gamma alpha⟧ᶻ.IsFunc ZFSet.𝔹 R)]
        exact ZFSet.pair_mem_prod.mpr ⟨ha, hb⟩⟩
    let G := option_func_of_pfun gamma alpha R
    let Gapp := fapply G (is_func_is_pfunc
      (option_func_of_pfun_isFunc gamma alpha R))
      ⟨a, by
        rw [is_func_dom_eq (option_func_of_pfun_isFunc gamma alpha R)]
        exact ha⟩
    let someb := ZFSet.Option.some (S := ⟦alpha⟧ᶻ) ⟨b, hb⟩
    Rapp.val = zfEqIn ⟦SMTType.option alpha⟧ᶻ
      Gapp.val someb.val := by
  dsimp only
  let G := option_func_of_pfun gamma alpha R
  have hG : G ∈ ⟦SMTType.fun gamma (SMTType.option alpha)⟧ᶻ :=
    graphCollapse_mem gamma alpha R
  have hGraph : optionGraph gamma alpha G = R :=
    optionGraph_graphCollapse gamma alpha R hR hfun
  have hRfunc : ⟦SMTType.pair gamma alpha⟧ᶻ.IsFunc ZFSet.𝔹 R := by
    simpa [SMTType.toZFSet] using hR
  have hab : a.pair b ∈ ⟦SMTType.pair gamma alpha⟧ᶻ :=
    ZFSet.pair_mem_prod.mpr ⟨ha, hb⟩
  have habDom : a.pair b ∈ R.Dom := by
    rw [ZFSet.is_func_dom_eq hRfunc]
    exact hab
  have hleft :
      (fapply R (is_func_is_pfunc hRfunc)
        ⟨a.pair b, habDom⟩).val = ZFSet.zftrue ↔
        a.pair b ∈ predGraph gamma alpha R := by
    unfold predGraph
    rw [ZFSet.mem_sep]
    constructor
    · intro htrue
      exact ⟨hab, by
        change (a.pair b).pair ZFSet.zftrue ∈ R
        rw [← htrue]
        exact ZFSet.fapply.def (is_func_is_pfunc hRfunc) habDom⟩
    · intro hpair
      exact Subtype.ext_iff.mp
        (ZFSet.fapply.of_pair (is_func_is_pfunc hRfunc) hpair.2)
  have hGfunc : ⟦gamma⟧ᶻ.IsFunc ⟦SMTType.option alpha⟧ᶻ G := by
    simpa [SMTType.toZFSet] using hG
  have haDom : a ∈ G.Dom := by
    rw [ZFSet.is_func_dom_eq hGfunc]
    exact ha
  let someb := ZFSet.Option.some (S := ⟦alpha⟧ᶻ) ⟨b, hb⟩
  have hsomeb : someb.val ∈ ⟦SMTType.option alpha⟧ᶻ := someb.property
  have hpairApp : a.pair someb.val ∈ G ↔
      (fapply G (is_func_is_pfunc hGfunc) ⟨a, haDom⟩).val =
        someb.val := by
    constructor
    · intro hpair
      exact Subtype.ext_iff.mp
        (ZFSet.fapply.of_pair (is_func_is_pfunc hGfunc) hpair)
    · intro heq
      rw [← heq]
      exact ZFSet.fapply.def (is_func_is_pfunc hGfunc) haDom
  have hgraphMem : a.pair b ∈ predGraph gamma alpha R ↔
      a.pair someb.val ∈ G := by
    rw [← hGraph]
    exact mem_predGraph_optionGraph_iff gamma alpha G hG a b ha hb
  have hright : zfEqIn ⟦SMTType.option alpha⟧ᶻ
      (fapply G (is_func_is_pfunc hGfunc) ⟨a, haDom⟩).val
      someb.val = ZFSet.zftrue ↔
      a.pair b ∈ predGraph gamma alpha R :=
    (zfEqIn_eq_zftrue_iff (ZFSet.fapply_mem_range _ _) hsomeb).trans
      (hpairApp.symm.trans hgraphMem.symm)
  apply zfBool_eq_of_true_iff
  · exact ZFSet.fapply_mem_range _ _
  · exact overloadBinOp_mem (ZFSet.fapply_mem_range _ _) hsomeb
  · exact hleft.trans hright.symm

private def relationOptionBody (R G u v : SMT.𝒱) : SMT.Term :=
  .eq
    (.app (.var R) (.pair (.var u) (.var v)))
    (.eq (.app (.var G) (.var u)) (.some (.var v)))

/-- Abstracting the relation-to-option body under a context that assigns its
four free names exposes exactly the pointwise graph equation used by the
encoder. -/
private theorem relation_option_body_abstract_denote.{u}
    (gamma alpha : SMTType)
    {Theta : SMT.RenamingContext.Context.{u}}
    {R G u v : SMT.𝒱} {WR WG Wa Wb : SMT.Dom.{u}}
    (hThetaR : Theta R = some WR) (hThetaG : Theta G = some WG)
    (hThetau : Theta u = some Wa) (hThetav : Theta v = some Wb)
    (hWR_ty : WR.snd.fst = SMTType.fun
      (SMTType.pair gamma alpha) SMTType.bool)
    (hWG_ty : WG.snd.fst = SMTType.fun gamma (SMTType.option alpha))
    (hWa_ty : Wa.snd.fst = gamma) (hWb_ty : Wb.snd.fst = alpha)
    (hcov : SMT.RenamingContext.CoversFV Theta
      (relationOptionBody R G u v)) :
    let hR : WR.fst ∈ ⟦SMTType.fun
        (SMTType.pair gamma alpha) SMTType.bool⟧ᶻ := by
      rw [← hWR_ty]
      exact WR.snd.snd
    let hG : WG.fst ∈ ⟦SMTType.fun gamma (SMTType.option alpha)⟧ᶻ := by
      rw [← hWG_ty]
      exact WG.snd.snd
    let ha : Wa.fst ∈ ⟦gamma⟧ᶻ := by
      rw [← hWa_ty]
      exact Wa.snd.snd
    let hb : Wb.fst ∈ ⟦alpha⟧ᶻ := by
      rw [← hWb_ty]
      exact Wb.snd.snd
    let hRfunc : ZFSet.IsFunc
        ⟦SMTType.pair gamma alpha⟧ᶻ ZFSet.𝔹 WR.fst := by
      simpa [SMTType.toZFSet] using hR
    let hab : Wa.fst.pair Wb.fst ∈ ⟦SMTType.pair gamma alpha⟧ᶻ :=
      ZFSet.pair_mem_prod.mpr ⟨ha, hb⟩
    let hRdom : Wa.fst.pair Wb.fst ∈ WR.fst.Dom := by
      rw [ZFSet.is_func_dom_eq hRfunc]
      exact hab
    let Rapp := ZFSet.fapply WR.fst
      (ZFSet.is_func_is_pfunc hRfunc) ⟨Wa.fst.pair Wb.fst, hRdom⟩
    let hGfunc : ZFSet.IsFunc ⟦gamma⟧ᶻ
        ⟦SMTType.option alpha⟧ᶻ WG.fst := by
      simpa [SMTType.toZFSet] using hG
    let hGdom : Wa.fst ∈ WG.fst.Dom := by
      rw [ZFSet.is_func_dom_eq hGfunc]
      exact ha
    let Gapp := ZFSet.fapply WG.fst
      (ZFSet.is_func_is_pfunc hGfunc) ⟨Wa.fst, hGdom⟩
    let someb := ZFSet.Option.some (S := ⟦alpha⟧ᶻ) ⟨Wb.fst, hb⟩
    ∃ D : SMT.Dom.{u},
      ⟦(relationOptionBody R G u v).abstract Theta hcov⟧ˢ = some D ∧
      D.snd.fst = SMTType.bool ∧
      (D.fst = ZFSet.zftrue ↔
        Rapp.val = zfEqIn ⟦SMTType.option alpha⟧ᶻ
          Gapp.val someb.val) := by
  dsimp only
  let hR : WR.fst ∈ ⟦SMTType.fun
      (SMTType.pair gamma alpha) SMTType.bool⟧ᶻ := by
    rw [← hWR_ty]
    exact WR.snd.snd
  let hG : WG.fst ∈ ⟦SMTType.fun gamma (SMTType.option alpha)⟧ᶻ := by
    rw [← hWG_ty]
    exact WG.snd.snd
  let ha : Wa.fst ∈ ⟦gamma⟧ᶻ := by
    rw [← hWa_ty]
    exact Wa.snd.snd
  let hb : Wb.fst ∈ ⟦alpha⟧ᶻ := by
    rw [← hWb_ty]
    exact Wb.snd.snd
  have hWR_eq : ⟨WR.fst,
      SMTType.fun (SMTType.pair gamma alpha) SMTType.bool, hR⟩ = WR :=
    (funDomEqOfTyEqAndFstEq hWR_ty rfl).symm
  have hWG_eq : ⟨WG.fst,
      SMTType.fun gamma (SMTType.option alpha), hG⟩ = WG :=
    (funDomEqOfTyEqAndFstEq hWG_ty rfl).symm
  have hWa_eq : ⟨Wa.fst, gamma, ha⟩ = Wa :=
    (funDomEqOfTyEqAndFstEq hWa_ty rfl).symm
  have hWb_eq : ⟨Wb.fst, alpha, hb⟩ = Wb :=
    (funDomEqOfTyEqAndFstEq hWb_ty rfl).symm
  simpa only [relationOptionBody, SMT.Term.abstract,
      hThetaR, hThetaG, hThetau, hThetav, Option.get_some,
      hWR_eq, hWG_eq, hWa_eq, hWb_eq, proof_irrel_heq]
    using relation_option_body_denote gamma alpha hR hG ha hb

/-- Assigning the graph-collapse function makes the complete quantified
relation-to-option specification true. -/
private theorem relation_option_forall_graphCollapse.{u}
    (gamma alpha : SMTType)
    {Theta : SMT.RenamingContext.Context.{u}}
    {Rname Gname u v : SMT.𝒱} {R : ZFSet.{u}}
    (hR : R ∈ ⟦SMTType.fun (SMTType.pair gamma alpha)
      SMTType.bool⟧ᶻ)
    (hfun : (predGraph gamma alpha R).IsPFunc
      ⟦gamma⟧ᶻ ⟦alpha⟧ᶻ)
    (hcov_forall : SMT.RenamingContext.CoversFV Theta
      (SMT.Term.forall [u, v] [gamma, alpha]
        (relationOptionBody Rname Gname u v)))
    (hgo_cov : ∀ w ∈ SMT.fv (relationOptionBody Rname Gname u v),
      w ∉ [u, v] → (Theta w).isSome = true)
    (hcov_body_upd : ∀ Wa Wb : SMT.Dom.{u},
      SMT.RenamingContext.CoversFV
        (Function.update (Function.update Theta u (some Wa)) v (some Wb))
        (relationOptionBody Rname Gname u v))
    (hlookupR : ∀ Wa Wb : SMT.Dom.{u},
      Function.update (Function.update Theta u (some Wa)) v (some Wb)
          Rname =
        some (⟨R, SMTType.fun (SMTType.pair gamma alpha)
          SMTType.bool, hR⟩ : SMT.Dom.{u}))
    (hlookupG : ∀ Wa Wb : SMT.Dom.{u},
      Function.update (Function.update Theta u (some Wa)) v (some Wb)
          Gname =
        some (⟨option_func_of_pfun gamma alpha R,
          SMTType.fun gamma (SMTType.option alpha),
          graphCollapse_mem gamma alpha R⟩ : SMT.Dom.{u}))
    (hlookupU : ∀ Wa Wb : SMT.Dom.{u},
      Function.update (Function.update Theta u (some Wa)) v (some Wb) u =
        some Wa)
    (hlookupV : ∀ Wa Wb : SMT.Dom.{u},
      Function.update (Function.update Theta u (some Wa)) v (some Wb) v =
        some Wb) :
    ⟦(SMT.Term.forall [u, v] [gamma, alpha]
        (relationOptionBody Rname Gname u v)).abstract Theta hcov_forall⟧ˢ =
      some ⟨ZFSet.zftrue, SMTType.bool,
        ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
  apply funBinaryForallEqZftrue hcov_forall hgo_cov hcov_body_upd
  · intro Wa Wb hWa_ty hWb_ty
    obtain ⟨D, hden, _hDty, _hiff⟩ :=
      relation_option_body_abstract_denote gamma alpha
        (hlookupR Wa Wb) (hlookupG Wa Wb)
        (hlookupU Wa Wb) (hlookupV Wa Wb)
        rfl rfl hWa_ty hWb_ty (hcov_body_upd Wa Wb)
    rw [hden]
    rfl
  · intro Wa Wb hWa_ty hWb_ty D hdenD
    obtain ⟨D0, hden0, hD0ty, _hiff⟩ :=
      relation_option_body_abstract_denote gamma alpha
        (hlookupR Wa Wb) (hlookupG Wa Wb)
        (hlookupU Wa Wb) (hlookupV Wa Wb)
        rfl rfl hWa_ty hWb_ty (hcov_body_upd Wa Wb)
    rw [hden0] at hdenD
    cases Option.some.inj hdenD
    exact hD0ty
  · intro Wa Wb hWa_ty hWb_ty
    obtain ⟨D, hden, hDty, hiff⟩ :=
      relation_option_body_abstract_denote gamma alpha
        (hlookupR Wa Wb) (hlookupG Wa Wb)
        (hlookupU Wa Wb) (hlookupV Wa Wb)
        rfl rfl hWa_ty hWb_ty (hcov_body_upd Wa Wb)
    refine ⟨D, hden, hiff.mpr ?_⟩
    simpa only [proof_irrel_heq] using
      graphCollapse_pointwise_spec gamma alpha hR hfun
        (by rw [← hWa_ty]; exact Wa.snd.snd)
        (by rw [← hWb_ty]; exact Wb.snd.snd)

/-- A true quantified relation-to-option specification can be inverted at any
typed pair.  This is the guarded direction needed for arbitrary satisfying
assignments of the freshly declared option function. -/
private theorem relation_option_forall_pointwise_of_true.{u}
    (gamma alpha : SMTType)
    {Theta : SMT.RenamingContext.Context.{u}}
    {Rname Gname u v : SMT.𝒱} {R G : ZFSet.{u}}
    (hR : R ∈ ⟦SMTType.fun (SMTType.pair gamma alpha)
      SMTType.bool⟧ᶻ)
    (hG : G ∈ ⟦SMTType.fun gamma (SMTType.option alpha)⟧ᶻ)
    (hcov_forall : SMT.RenamingContext.CoversFV Theta
      (SMT.Term.forall [u, v] [gamma, alpha]
        (relationOptionBody Rname Gname u v)))
    (hgo_cov : ∀ w ∈ SMT.fv (relationOptionBody Rname Gname u v),
      w ∉ [u, v] → (Theta w).isSome = true)
    (hcov_body_upd : ∀ Wa Wb : SMT.Dom.{u},
      SMT.RenamingContext.CoversFV
        (Function.update (Function.update Theta u (some Wa)) v (some Wb))
        (relationOptionBody Rname Gname u v))
    (hlookupR : ∀ Wa Wb : SMT.Dom.{u},
      Function.update (Function.update Theta u (some Wa)) v (some Wb)
          Rname =
        some (⟨R, SMTType.fun (SMTType.pair gamma alpha)
          SMTType.bool, hR⟩ : SMT.Dom.{u}))
    (hlookupG : ∀ Wa Wb : SMT.Dom.{u},
      Function.update (Function.update Theta u (some Wa)) v (some Wb)
          Gname =
        some (⟨G, SMTType.fun gamma (SMTType.option alpha), hG⟩ :
          SMT.Dom.{u}))
    (hlookupU : ∀ Wa Wb : SMT.Dom.{u},
      Function.update (Function.update Theta u (some Wa)) v (some Wb) u =
        some Wa)
    (hlookupV : ∀ Wa Wb : SMT.Dom.{u},
      Function.update (Function.update Theta u (some Wa)) v (some Wb) v =
        some Wb)
    {Phi : SMT.Dom.{u}}
    (hden_forall :
      ⟦(SMT.Term.forall [u, v] [gamma, alpha]
          (relationOptionBody Rname Gname u v)).abstract Theta hcov_forall⟧ˢ =
        some Phi)
    (htrue : Phi.fst = ZFSet.zftrue)
    (Wa Wb : SMT.Dom.{u})
    (hWa_ty : Wa.snd.fst = gamma) (hWb_ty : Wb.snd.fst = alpha) :
    let ha : Wa.fst ∈ ⟦gamma⟧ᶻ := by
      rw [← hWa_ty]
      exact Wa.snd.snd
    let hb : Wb.fst ∈ ⟦alpha⟧ᶻ := by
      rw [← hWb_ty]
      exact Wb.snd.snd
    let hRfunc : ZFSet.IsFunc ⟦SMTType.pair gamma alpha⟧ᶻ
        ZFSet.𝔹 R := by
      simpa [SMTType.toZFSet] using hR
    let hab : Wa.fst.pair Wb.fst ∈ ⟦SMTType.pair gamma alpha⟧ᶻ :=
      ZFSet.pair_mem_prod.mpr ⟨ha, hb⟩
    let hRdom : Wa.fst.pair Wb.fst ∈ R.Dom := by
      rw [ZFSet.is_func_dom_eq hRfunc]
      exact hab
    let Rapp := ZFSet.fapply R (ZFSet.is_func_is_pfunc hRfunc)
      ⟨Wa.fst.pair Wb.fst, hRdom⟩
    let hGfunc : ZFSet.IsFunc ⟦gamma⟧ᶻ ⟦SMTType.option alpha⟧ᶻ G := by
      simpa [SMTType.toZFSet] using hG
    let hGdom : Wa.fst ∈ G.Dom := by
      rw [ZFSet.is_func_dom_eq hGfunc]
      exact ha
    let Gapp := ZFSet.fapply G (ZFSet.is_func_is_pfunc hGfunc)
      ⟨Wa.fst, hGdom⟩
    let someb := ZFSet.Option.some (S := ⟦alpha⟧ᶻ) ⟨Wb.fst, hb⟩
    Rapp.val = zfEqIn ⟦SMTType.option alpha⟧ᶻ
      Gapp.val someb.val := by
  dsimp only
  have hbody_total :
      ∀ Wa Wb : SMT.Dom.{u}, Wa.snd.fst = gamma →
        Wb.snd.fst = alpha →
        ⟦(relationOptionBody Rname Gname u v).abstract
          (Function.update (Function.update Theta u (some Wa)) v (some Wb))
          (hcov_body_upd Wa Wb)⟧ˢ.isSome = true := by
    intro Wa' Wb' hWa'_ty hWb'_ty
    obtain ⟨D, hden, _hDty, _hiff⟩ :=
      relation_option_body_abstract_denote gamma alpha
        (hlookupR Wa' Wb') (hlookupG Wa' Wb')
        (hlookupU Wa' Wb') (hlookupV Wa' Wb')
        rfl rfl hWa'_ty hWb'_ty (hcov_body_upd Wa' Wb')
    rw [hden]
    rfl
  have hbody_ty :
      ∀ Wa Wb : SMT.Dom.{u}, Wa.snd.fst = gamma →
        Wb.snd.fst = alpha → ∀ {D : SMT.Dom.{u}},
        ⟦(relationOptionBody Rname Gname u v).abstract
          (Function.update (Function.update Theta u (some Wa)) v (some Wb))
          (hcov_body_upd Wa Wb)⟧ˢ = some D →
        D.snd.fst = SMTType.bool := by
    intro Wa' Wb' hWa'_ty hWb'_ty D hdenD
    obtain ⟨D0, hden0, hD0ty, _hiff⟩ :=
      relation_option_body_abstract_denote gamma alpha
        (hlookupR Wa' Wb') (hlookupG Wa' Wb')
        (hlookupU Wa' Wb') (hlookupV Wa' Wb')
        rfl rfl hWa'_ty hWb'_ty (hcov_body_upd Wa' Wb')
    rw [hden0] at hdenD
    cases Option.some.inj hdenD
    exact hD0ty
  obtain ⟨D, hdenD, hDtrue⟩ := funBinaryForallTrueAt
    hcov_forall hgo_cov hcov_body_upd hbody_total hbody_ty
    hden_forall htrue Wa Wb hWa_ty hWb_ty
  obtain ⟨D0, hden0, _hD0ty, hiff⟩ :=
    relation_option_body_abstract_denote gamma alpha
      (hlookupR Wa Wb) (hlookupG Wa Wb)
      (hlookupU Wa Wb) (hlookupV Wa Wb)
      rfl rfl hWa_ty hWb_ty (hcov_body_upd Wa Wb)
  rw [hden0] at hdenD
  cases Option.some.inj hdenD
  exact hiff.mp hDtrue

private theorem denote_app_exact_of_denote.{u}
    {sigma tau : SMTType}
    {tf tx : SMT.PHOAS.Term SMT.Dom}
    {WF WX : SMT.Dom.{u}}
    (hdenF : ⟦tf⟧ˢ = some WF) (hdenX : ⟦tx⟧ˢ = some WX)
    (hWF_ty : WF.snd.fst = SMTType.fun sigma tau)
    (hWX_ty : WX.snd.fst = sigma) :
    let hfunc : ZFSet.IsFunc ⟦sigma⟧ᶻ ⟦tau⟧ᶻ WF.fst := by
      have hmem := WF.snd.snd
      rw [hWF_ty, SMTType.toZFSet] at hmem
      exact ZFSet.mem_funs.mp hmem
    let hdom : WX.fst ∈ WF.fst.Dom := by
      rw [ZFSet.is_func_dom_eq hfunc, ← hWX_ty]
      exact WX.snd.snd
    ∃ D : SMT.Dom.{u},
      ⟦SMT.PHOAS.Term.app tf tx⟧ˢ = some D ∧
      D.snd.fst = tau ∧
      D.fst = (ZFSet.fapply WF.fst (ZFSet.is_func_is_pfunc hfunc)
        ⟨WX.fst, hdom⟩).val := by
  dsimp only
  let hfunc : ZFSet.IsFunc ⟦sigma⟧ᶻ ⟦tau⟧ᶻ WF.fst := by
    have hmem := WF.snd.snd
    rw [hWF_ty, SMTType.toZFSet] at hmem
    exact ZFSet.mem_funs.mp hmem
  let hdom : WX.fst ∈ WF.fst.Dom := by
    rw [ZFSet.is_func_dom_eq hfunc, ← hWX_ty]
    exact WX.snd.snd
  let Y := ZFSet.fapply WF.fst (ZFSet.is_func_is_pfunc hfunc)
    ⟨WX.fst, hdom⟩
  refine ⟨⟨Y.val, tau, Y.property⟩, ?_, rfl, rfl⟩
  rw [SMT.denote, hdenF, hdenX]
  obtain ⟨F, sigmaF, hF⟩ := WF
  obtain ⟨X, sigmaX, hX⟩ := WX
  dsimp at hWF_ty hWX_ty hfunc hdom Y ⊢
  subst sigmaF
  subst sigmaX
  simp only [dif_pos (ZFSet.is_func_is_pfunc hfunc), dif_pos hdom,
    ite_true]
  rfl

private def relationOptionTermBody
    (r : SMT.Term) (G u v : SMT.𝒱) : SMT.Term :=
  .eq
    (.app r (.pair (.var u) (.var v)))
    (.eq (.app (.var G) (.var u)) (.some (.var v)))

private theorem mem_fv_relationOptionTermBody_iff
    {r : SMT.Term} {G u v w : SMT.𝒱} :
    w ∈ SMT.fv (relationOptionTermBody r G u v) ↔
      w ∈ SMT.fv r ∨ w = G ∨ w = u ∨ w = v := by
  simp only [relationOptionTermBody, SMT.fv, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem mem_fv_relationOptionForall_iff
    {r : SMT.Term} {G u v w : SMT.𝒱}
    {gamma alpha : SMTType} :
    w ∈ SMT.fv (SMT.Term.forall [u, v] [gamma, alpha]
        (relationOptionTermBody r G u v)) ↔
      (w ∈ SMT.fv r ∨ w = G) ∧ w ≠ u ∧ w ≠ v := by
  rw [SMT.fv, List.mem_removeAll_iff,
    mem_fv_relationOptionTermBody_iff]
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  tauto

/-- Body semantics with an arbitrary relation term rather than a relation
variable.  This covers the application branch that casts only the argument. -/
private theorem relation_option_term_body_denote.{u}
    (gamma alpha : SMTType)
    {r : SMT.PHOAS.Term SMT.Dom} {WR WG Wa Wb : SMT.Dom.{u}}
    (hdenR : ⟦r⟧ˢ = some WR)
    (hWR_ty : WR.snd.fst = SMTType.fun
      (SMTType.pair gamma alpha) SMTType.bool)
    (hWG_ty : WG.snd.fst = SMTType.fun gamma (SMTType.option alpha))
    (hWa_ty : Wa.snd.fst = gamma) (hWb_ty : Wb.snd.fst = alpha) :
    let hR : WR.fst ∈ ⟦SMTType.fun
        (SMTType.pair gamma alpha) SMTType.bool⟧ᶻ := by
      rw [← hWR_ty]
      exact WR.snd.snd
    let hG : WG.fst ∈ ⟦SMTType.fun gamma (SMTType.option alpha)⟧ᶻ := by
      rw [← hWG_ty]
      exact WG.snd.snd
    let ha : Wa.fst ∈ ⟦gamma⟧ᶻ := by
      rw [← hWa_ty]
      exact Wa.snd.snd
    let hb : Wb.fst ∈ ⟦alpha⟧ᶻ := by
      rw [← hWb_ty]
      exact Wb.snd.snd
    let hRfunc : ZFSet.IsFunc ⟦SMTType.pair gamma alpha⟧ᶻ
        ZFSet.𝔹 WR.fst := by
      simpa [SMTType.toZFSet] using hR
    let hab : Wa.fst.pair Wb.fst ∈ ⟦SMTType.pair gamma alpha⟧ᶻ :=
      ZFSet.pair_mem_prod.mpr ⟨ha, hb⟩
    let hRdom : Wa.fst.pair Wb.fst ∈ WR.fst.Dom := by
      rw [ZFSet.is_func_dom_eq hRfunc]
      exact hab
    let Rapp := ZFSet.fapply WR.fst
      (ZFSet.is_func_is_pfunc hRfunc) ⟨Wa.fst.pair Wb.fst, hRdom⟩
    let hGfunc : ZFSet.IsFunc ⟦gamma⟧ᶻ
        ⟦SMTType.option alpha⟧ᶻ WG.fst := by
      simpa [SMTType.toZFSet] using hG
    let hGdom : Wa.fst ∈ WG.fst.Dom := by
      rw [ZFSet.is_func_dom_eq hGfunc]
      exact ha
    let Gapp := ZFSet.fapply WG.fst
      (ZFSet.is_func_is_pfunc hGfunc) ⟨Wa.fst, hGdom⟩
    let someb := ZFSet.Option.some (S := ⟦alpha⟧ᶻ) ⟨Wb.fst, hb⟩
    ∃ D : SMT.Dom.{u},
      ⟦SMT.PHOAS.Term.eq
        (.app r (.pair (.var Wa) (.var Wb)))
        (.eq (.app (.var WG) (.var Wa)) (.some (.var Wb)))⟧ˢ = some D ∧
      D.snd.fst = SMTType.bool ∧
      (D.fst = ZFSet.zftrue ↔
        Rapp.val = zfEqIn ⟦SMTType.option alpha⟧ᶻ
          Gapp.val someb.val) := by
  dsimp only
  let hR : WR.fst ∈ ⟦SMTType.fun
      (SMTType.pair gamma alpha) SMTType.bool⟧ᶻ := by
    rw [← hWR_ty]
    exact WR.snd.snd
  let hG : WG.fst ∈ ⟦SMTType.fun gamma (SMTType.option alpha)⟧ᶻ := by
    rw [← hWG_ty]
    exact WG.snd.snd
  let ha : Wa.fst ∈ ⟦gamma⟧ᶻ := by
    rw [← hWa_ty]
    exact Wa.snd.snd
  let hb : Wb.fst ∈ ⟦alpha⟧ᶻ := by
    rw [← hWb_ty]
    exact Wb.snd.snd
  let hRfunc : ZFSet.IsFunc ⟦SMTType.pair gamma alpha⟧ᶻ
      ZFSet.𝔹 WR.fst := by
    simpa [SMTType.toZFSet] using hR
  let hab : Wa.fst.pair Wb.fst ∈ ⟦SMTType.pair gamma alpha⟧ᶻ :=
    ZFSet.pair_mem_prod.mpr ⟨ha, hb⟩
  let hRdom : Wa.fst.pair Wb.fst ∈ WR.fst.Dom := by
    rw [ZFSet.is_func_dom_eq hRfunc]
    exact hab
  let Rapp := ZFSet.fapply WR.fst
    (ZFSet.is_func_is_pfunc hRfunc) ⟨Wa.fst.pair Wb.fst, hRdom⟩
  let hGfunc : ZFSet.IsFunc ⟦gamma⟧ᶻ
      ⟦SMTType.option alpha⟧ᶻ WG.fst := by
    simpa [SMTType.toZFSet] using hG
  let hGdom : Wa.fst ∈ WG.fst.Dom := by
    rw [ZFSet.is_func_dom_eq hGfunc]
    exact ha
  let Gapp := ZFSet.fapply WG.fst
    (ZFSet.is_func_is_pfunc hGfunc) ⟨Wa.fst, hGdom⟩
  let someb := ZFSet.Option.some (S := ⟦alpha⟧ᶻ) ⟨Wb.fst, hb⟩
  let Wab : SMT.Dom.{u} := ⟨Wa.fst.pair Wb.fst,
    SMTType.pair gamma alpha, ZFSet.pair_mem_prod.mpr ⟨ha, hb⟩⟩
  have hdenPair :
      ⟦SMT.PHOAS.Term.pair (.var Wa) (.var Wb)⟧ˢ = some Wab := by
    obtain ⟨a, sigmaA, ha'⟩ := Wa
    obtain ⟨b, sigmaB, hb'⟩ := Wb
    dsimp at hWa_ty hWb_ty ha hb Wab ⊢
    subst sigmaA
    subst sigmaB
    simp only [SMT.denote, Option.pure_def]
    congr
  obtain ⟨DR, hdenDR, hDRty, hDRval⟩ :=
    denote_app_exact_of_denote hdenR hdenPair hWR_ty rfl
  obtain ⟨DG, hdenDG, hDGty, hDGval⟩ :=
    denote_app_var_exact WG Wa hWG_ty hWa_ty
  obtain ⟨DS, hdenDS, hDSty, hDSval⟩ :=
    denote_some_var_exact Wb hWb_ty
  obtain ⟨DI, hdenI, hDIty⟩ :=
    denote_eq_some_of_some hdenDG hdenDS (by rw [hDGty, hDSty])
  obtain ⟨DO, hdenO, hDOty⟩ :=
    denote_eq_some_of_some hdenDR hdenI (by rw [hDRty, hDIty])
  have hDIsem : DI.fst = zfEqIn ⟦SMTType.option alpha⟧ᶻ
      Gapp.val someb.val := by
    apply zfBool_eq_of_true_iff
    · have hmem := DI.snd.snd
      rwa [hDIty] at hmem
    · exact overloadBinOp_mem Gapp.property someb.property
    · rw [denote_eq_fst_eq_zftrue_iff hdenDG hdenDS
          (by rw [hDGty, hDSty]) hdenI,
        zfEqIn_eq_zftrue_iff Gapp.property someb.property,
        hDGval, hDSval]
  refine ⟨DO, hdenO, hDOty, ?_⟩
  rw [denote_eq_fst_eq_zftrue_iff hdenDR hdenI
      (by rw [hDRty, hDIty]) hdenO,
    hDRval, hDIsem]

private theorem relation_option_term_body_abstract_denote.{u}
    (gamma alpha : SMTType)
    {Theta : SMT.RenamingContext.Context.{u}}
    {r : SMT.Term} {G u v : SMT.𝒱}
    {WR WG Wa Wb : SMT.Dom.{u}}
    (hcov_r : SMT.RenamingContext.CoversFV Theta r)
    (hden_r : ⟦r.abstract Theta hcov_r⟧ˢ = some WR)
    (hThetaG : Theta G = some WG)
    (hThetau : Theta u = some Wa) (hThetav : Theta v = some Wb)
    (hWR_ty : WR.snd.fst = SMTType.fun
      (SMTType.pair gamma alpha) SMTType.bool)
    (hWG_ty : WG.snd.fst = SMTType.fun gamma (SMTType.option alpha))
    (hWa_ty : Wa.snd.fst = gamma) (hWb_ty : Wb.snd.fst = alpha)
    (hcov : SMT.RenamingContext.CoversFV Theta
      (relationOptionTermBody r G u v)) :
    let hR : WR.fst ∈ ⟦SMTType.fun
        (SMTType.pair gamma alpha) SMTType.bool⟧ᶻ := by
      rw [← hWR_ty]
      exact WR.snd.snd
    let hG : WG.fst ∈ ⟦SMTType.fun gamma (SMTType.option alpha)⟧ᶻ := by
      rw [← hWG_ty]
      exact WG.snd.snd
    let ha : Wa.fst ∈ ⟦gamma⟧ᶻ := by
      rw [← hWa_ty]
      exact Wa.snd.snd
    let hb : Wb.fst ∈ ⟦alpha⟧ᶻ := by
      rw [← hWb_ty]
      exact Wb.snd.snd
    let hRfunc : ZFSet.IsFunc ⟦SMTType.pair gamma alpha⟧ᶻ
        ZFSet.𝔹 WR.fst := by
      simpa [SMTType.toZFSet] using hR
    let hab : Wa.fst.pair Wb.fst ∈ ⟦SMTType.pair gamma alpha⟧ᶻ :=
      ZFSet.pair_mem_prod.mpr ⟨ha, hb⟩
    let hRdom : Wa.fst.pair Wb.fst ∈ WR.fst.Dom := by
      rw [ZFSet.is_func_dom_eq hRfunc]
      exact hab
    let Rapp := ZFSet.fapply WR.fst
      (ZFSet.is_func_is_pfunc hRfunc) ⟨Wa.fst.pair Wb.fst, hRdom⟩
    let hGfunc : ZFSet.IsFunc ⟦gamma⟧ᶻ
        ⟦SMTType.option alpha⟧ᶻ WG.fst := by
      simpa [SMTType.toZFSet] using hG
    let hGdom : Wa.fst ∈ WG.fst.Dom := by
      rw [ZFSet.is_func_dom_eq hGfunc]
      exact ha
    let Gapp := ZFSet.fapply WG.fst
      (ZFSet.is_func_is_pfunc hGfunc) ⟨Wa.fst, hGdom⟩
    let someb := ZFSet.Option.some (S := ⟦alpha⟧ᶻ) ⟨Wb.fst, hb⟩
    ∃ D : SMT.Dom.{u},
      ⟦(relationOptionTermBody r G u v).abstract Theta hcov⟧ˢ = some D ∧
      D.snd.fst = SMTType.bool ∧
      (D.fst = ZFSet.zftrue ↔
        Rapp.val = zfEqIn ⟦SMTType.option alpha⟧ᶻ
          Gapp.val someb.val) := by
  dsimp only
  have hden_r' :
      ⟦r.abstract Theta (fun w hw => hcov w (by
        simp only [relationOptionTermBody, SMT.fv, List.mem_append,
          List.mem_cons, List.not_mem_nil, or_false]
        exact Or.inl (Or.inl hw)))⟧ˢ = some WR := by
    simpa only [proof_irrel_heq] using hden_r
  simpa only [relationOptionTermBody, SMT.Term.abstract,
      hThetaG, hThetau, hThetav, Option.get_some, proof_irrel_heq]
    using relation_option_term_body_denote gamma alpha hden_r'
      hWR_ty hWG_ty hWa_ty hWb_ty

private theorem relation_option_term_forall_graphCollapse.{u}
    (gamma alpha : SMTType)
    {Theta : SMT.RenamingContext.Context.{u}}
    {r : SMT.Term} {G u v : SMT.𝒱} {R : ZFSet.{u}}
    (hR : R ∈ ⟦SMTType.fun (SMTType.pair gamma alpha)
      SMTType.bool⟧ᶻ)
    (hfun : (predGraph gamma alpha R).IsPFunc
      ⟦gamma⟧ᶻ ⟦alpha⟧ᶻ)
    (hcov_forall : SMT.RenamingContext.CoversFV Theta
      (SMT.Term.forall [u, v] [gamma, alpha]
        (relationOptionTermBody r G u v)))
    (hgo_cov : ∀ w ∈ SMT.fv (relationOptionTermBody r G u v),
      w ∉ [u, v] → (Theta w).isSome = true)
    (hcov_body_upd : ∀ Wa Wb : SMT.Dom.{u},
      SMT.RenamingContext.CoversFV
        (Function.update (Function.update Theta u (some Wa)) v (some Wb))
        (relationOptionTermBody r G u v))
    (hcov_r_upd : ∀ Wa Wb : SMT.Dom.{u},
      SMT.RenamingContext.CoversFV
        (Function.update (Function.update Theta u (some Wa)) v (some Wb)) r)
    (hden_r_upd : ∀ Wa Wb : SMT.Dom.{u},
      ⟦r.abstract
        (Function.update (Function.update Theta u (some Wa)) v (some Wb))
        (hcov_r_upd Wa Wb)⟧ˢ =
      some (⟨R, SMTType.fun (SMTType.pair gamma alpha)
        SMTType.bool, hR⟩ : SMT.Dom.{u}))
    (hlookupG : ∀ Wa Wb : SMT.Dom.{u},
      Function.update (Function.update Theta u (some Wa)) v (some Wb) G =
        some (⟨option_func_of_pfun gamma alpha R,
          SMTType.fun gamma (SMTType.option alpha),
          graphCollapse_mem gamma alpha R⟩ : SMT.Dom.{u}))
    (hlookupU : ∀ Wa Wb : SMT.Dom.{u},
      Function.update (Function.update Theta u (some Wa)) v (some Wb) u =
        some Wa)
    (hlookupV : ∀ Wa Wb : SMT.Dom.{u},
      Function.update (Function.update Theta u (some Wa)) v (some Wb) v =
        some Wb) :
    ⟦(SMT.Term.forall [u, v] [gamma, alpha]
        (relationOptionTermBody r G u v)).abstract Theta hcov_forall⟧ˢ =
      some ⟨ZFSet.zftrue, SMTType.bool,
        ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
  apply funBinaryForallEqZftrue hcov_forall hgo_cov hcov_body_upd
  · intro Wa Wb hWa_ty hWb_ty
    obtain ⟨D, hden, _hDty, _hiff⟩ :=
      relation_option_term_body_abstract_denote gamma alpha
        (hcov_r_upd Wa Wb) (hden_r_upd Wa Wb)
        (hlookupG Wa Wb) (hlookupU Wa Wb) (hlookupV Wa Wb)
        rfl rfl hWa_ty hWb_ty (hcov_body_upd Wa Wb)
    rw [hden]
    rfl
  · intro Wa Wb hWa_ty hWb_ty D hdenD
    obtain ⟨D0, hden0, hD0ty, _hiff⟩ :=
      relation_option_term_body_abstract_denote gamma alpha
        (hcov_r_upd Wa Wb) (hden_r_upd Wa Wb)
        (hlookupG Wa Wb) (hlookupU Wa Wb) (hlookupV Wa Wb)
        rfl rfl hWa_ty hWb_ty (hcov_body_upd Wa Wb)
    rw [hden0] at hdenD
    cases Option.some.inj hdenD
    exact hD0ty
  · intro Wa Wb hWa_ty hWb_ty
    obtain ⟨D, hden, _hDty, hiff⟩ :=
      relation_option_term_body_abstract_denote gamma alpha
        (hcov_r_upd Wa Wb) (hden_r_upd Wa Wb)
        (hlookupG Wa Wb) (hlookupU Wa Wb) (hlookupV Wa Wb)
        rfl rfl hWa_ty hWb_ty (hcov_body_upd Wa Wb)
    refine ⟨D, hden, hiff.mpr ?_⟩
    simpa only [proof_irrel_heq] using
      graphCollapse_pointwise_spec gamma alpha hR hfun
        (by rw [← hWa_ty]; exact Wa.snd.snd)
        (by rw [← hWb_ty]; exact Wb.snd.snd)

private theorem relation_option_term_forall_pointwise_of_true.{u}
    (gamma alpha : SMTType)
    {Theta : SMT.RenamingContext.Context.{u}}
    {r : SMT.Term} {Gname u v : SMT.𝒱} {R G : ZFSet.{u}}
    (hR : R ∈ ⟦SMTType.fun (SMTType.pair gamma alpha)
      SMTType.bool⟧ᶻ)
    (hG : G ∈ ⟦SMTType.fun gamma (SMTType.option alpha)⟧ᶻ)
    (hcov_forall : SMT.RenamingContext.CoversFV Theta
      (SMT.Term.forall [u, v] [gamma, alpha]
        (relationOptionTermBody r Gname u v)))
    (hgo_cov : ∀ w ∈ SMT.fv (relationOptionTermBody r Gname u v),
      w ∉ [u, v] → (Theta w).isSome = true)
    (hcov_body_upd : ∀ Wa Wb : SMT.Dom.{u},
      SMT.RenamingContext.CoversFV
        (Function.update (Function.update Theta u (some Wa)) v (some Wb))
        (relationOptionTermBody r Gname u v))
    (hcov_r_upd : ∀ Wa Wb : SMT.Dom.{u},
      SMT.RenamingContext.CoversFV
        (Function.update (Function.update Theta u (some Wa)) v (some Wb)) r)
    (hden_r_upd : ∀ Wa Wb : SMT.Dom.{u},
      ⟦r.abstract
        (Function.update (Function.update Theta u (some Wa)) v (some Wb))
        (hcov_r_upd Wa Wb)⟧ˢ =
      some (⟨R, SMTType.fun (SMTType.pair gamma alpha)
        SMTType.bool, hR⟩ : SMT.Dom.{u}))
    (hlookupG : ∀ Wa Wb : SMT.Dom.{u},
      Function.update (Function.update Theta u (some Wa)) v (some Wb)
          Gname =
        some (⟨G, SMTType.fun gamma (SMTType.option alpha), hG⟩ :
          SMT.Dom.{u}))
    (hlookupU : ∀ Wa Wb : SMT.Dom.{u},
      Function.update (Function.update Theta u (some Wa)) v (some Wb) u =
        some Wa)
    (hlookupV : ∀ Wa Wb : SMT.Dom.{u},
      Function.update (Function.update Theta u (some Wa)) v (some Wb) v =
        some Wb)
    {Phi : SMT.Dom.{u}}
    (hden_forall :
      ⟦(SMT.Term.forall [u, v] [gamma, alpha]
          (relationOptionTermBody r Gname u v)).abstract Theta hcov_forall⟧ˢ =
        some Phi)
    (htrue : Phi.fst = ZFSet.zftrue)
    (Wa Wb : SMT.Dom.{u})
    (hWa_ty : Wa.snd.fst = gamma) (hWb_ty : Wb.snd.fst = alpha) :
    let ha : Wa.fst ∈ ⟦gamma⟧ᶻ := by
      rw [← hWa_ty]
      exact Wa.snd.snd
    let hb : Wb.fst ∈ ⟦alpha⟧ᶻ := by
      rw [← hWb_ty]
      exact Wb.snd.snd
    let hRfunc : ZFSet.IsFunc ⟦SMTType.pair gamma alpha⟧ᶻ
        ZFSet.𝔹 R := by
      simpa [SMTType.toZFSet] using hR
    let hab : Wa.fst.pair Wb.fst ∈ ⟦SMTType.pair gamma alpha⟧ᶻ :=
      ZFSet.pair_mem_prod.mpr ⟨ha, hb⟩
    let hRdom : Wa.fst.pair Wb.fst ∈ R.Dom := by
      rw [ZFSet.is_func_dom_eq hRfunc]
      exact hab
    let Rapp := ZFSet.fapply R (ZFSet.is_func_is_pfunc hRfunc)
      ⟨Wa.fst.pair Wb.fst, hRdom⟩
    let hGfunc : ZFSet.IsFunc ⟦gamma⟧ᶻ ⟦SMTType.option alpha⟧ᶻ G := by
      simpa [SMTType.toZFSet] using hG
    let hGdom : Wa.fst ∈ G.Dom := by
      rw [ZFSet.is_func_dom_eq hGfunc]
      exact ha
    let Gapp := ZFSet.fapply G (ZFSet.is_func_is_pfunc hGfunc)
      ⟨Wa.fst, hGdom⟩
    let someb := ZFSet.Option.some (S := ⟦alpha⟧ᶻ) ⟨Wb.fst, hb⟩
    Rapp.val = zfEqIn ⟦SMTType.option alpha⟧ᶻ
      Gapp.val someb.val := by
  dsimp only
  have hbody_total :
      ∀ Wa Wb : SMT.Dom.{u}, Wa.snd.fst = gamma →
        Wb.snd.fst = alpha →
        ⟦(relationOptionTermBody r Gname u v).abstract
          (Function.update (Function.update Theta u (some Wa)) v (some Wb))
          (hcov_body_upd Wa Wb)⟧ˢ.isSome = true := by
    intro Wa' Wb' hWa'_ty hWb'_ty
    obtain ⟨D, hden, _hDty, _hiff⟩ :=
      relation_option_term_body_abstract_denote gamma alpha
        (hcov_r_upd Wa' Wb') (hden_r_upd Wa' Wb')
        (hlookupG Wa' Wb') (hlookupU Wa' Wb') (hlookupV Wa' Wb')
        rfl rfl hWa'_ty hWb'_ty (hcov_body_upd Wa' Wb')
    rw [hden]
    rfl
  have hbody_ty :
      ∀ Wa Wb : SMT.Dom.{u}, Wa.snd.fst = gamma →
        Wb.snd.fst = alpha → ∀ {D : SMT.Dom.{u}},
        ⟦(relationOptionTermBody r Gname u v).abstract
          (Function.update (Function.update Theta u (some Wa)) v (some Wb))
          (hcov_body_upd Wa Wb)⟧ˢ = some D →
        D.snd.fst = SMTType.bool := by
    intro Wa' Wb' hWa'_ty hWb'_ty D hdenD
    obtain ⟨D0, hden0, hD0ty, _hiff⟩ :=
      relation_option_term_body_abstract_denote gamma alpha
        (hcov_r_upd Wa' Wb') (hden_r_upd Wa' Wb')
        (hlookupG Wa' Wb') (hlookupU Wa' Wb') (hlookupV Wa' Wb')
        rfl rfl hWa'_ty hWb'_ty (hcov_body_upd Wa' Wb')
    rw [hden0] at hdenD
    cases Option.some.inj hdenD
    exact hD0ty
  obtain ⟨D, hdenD, hDtrue⟩ := funBinaryForallTrueAt
    hcov_forall hgo_cov hcov_body_upd hbody_total hbody_ty
    hden_forall htrue Wa Wb hWa_ty hWb_ty
  obtain ⟨D0, hden0, _hD0ty, hiff⟩ :=
    relation_option_term_body_abstract_denote gamma alpha
      (hcov_r_upd Wa Wb) (hden_r_upd Wa Wb)
      (hlookupG Wa Wb) (hlookupU Wa Wb) (hlookupV Wa Wb)
      rfl rfl hWa_ty hWb_ty (hcov_body_upd Wa Wb)
  rw [hden0] at hdenD
  cases Option.some.inj hdenD
  exact hiff.mp hDtrue

/-- Pointwise form of option-function application soundness.  Unlike
`castApp_option_term_semantics`, this lemma needs only the selected application
equation, which is exactly what the guarded relation specification provides. -/
private theorem castApp_option_term_semantics_of_apply_some.{u}
    {gamma alpha : BType} {f x : SMT.Term}
    {Gamma : SMT.TypeContext}
    {Theta : SMT.RenamingContext.Context.{u}}
    (hcov_f : RenamingContext.CoversFV Theta f)
    (hcov_x : RenamingContext.CoversFV Theta x)
    (respects_f : SMT.RenamingContext.RespectsTypeContextOnFV
      Theta Gamma f)
    (respects_x : SMT.RenamingContext.RespectsTypeContextOnFV
      Theta Gamma x)
    {T G Y Z : ZFSet.{u}}
    {hT : T ∈ ⟦alpha⟧ᶻ}
    {hG : G ∈ ⟦SMTType.fun gamma.toSMTType
      (SMTType.option alpha.toSMTType)⟧ᶻ}
    {hY : Y ∈ ⟦gamma.toSMTType⟧ᶻ}
    {hZ : Z ∈ ⟦alpha.toSMTType⟧ᶻ}
    (hden_f : ⟦f.abstract Theta hcov_f⟧ˢ =
      some (⟨G, SMTType.fun gamma.toSMTType
        (SMTType.option alpha.toSMTType), hG⟩ : SMT.Dom))
    (hden_x : ⟦x.abstract Theta hcov_x⟧ˢ =
      some (⟨Y, gamma.toSMTType, hY⟩ : SMT.Dom))
    (hZret : retract alpha Z = T)
    (happ :
      let hGfunc : ⟦gamma.toSMTType⟧ᶻ.IsFunc
          ⟦SMTType.option alpha.toSMTType⟧ᶻ G := by
        simpa [SMTType.toZFSet] using hG
      let hYdom : Y ∈ G.Dom := by
        rw [ZFSet.is_func_dom_eq hGfunc]
        exact hY
      let Gapp := ZFSet.fapply G (ZFSet.is_func_is_pfunc hGfunc)
        ⟨Y, hYdom⟩
      let someZ := ZFSet.Option.some
        (S := ⟦alpha.toSMTType⟧ᶻ) ⟨Z, hZ⟩
      Gapp.val = someZ.val) :
    ∃ (hcov_out : RenamingContext.CoversFV Theta
        (SMT.Term.the (SMT.Term.app f x)))
      (denOut : SMT.Dom.{u}),
      SMT.RenamingContext.RespectsTypeContextOnFV
        Theta Gamma (SMT.Term.the (SMT.Term.app f x)) ∧
      ⟦(SMT.Term.the (SMT.Term.app f x)).abstract
        Theta hcov_out⟧ˢ = some denOut ∧
      denOut.snd.fst = alpha.toSMTType ∧
      RDomCastSupported (⟨T, alpha, hT⟩ : B.Dom) denOut := by
  let hGfunc : ⟦gamma.toSMTType⟧ᶻ.IsFunc
      ⟦SMTType.option alpha.toSMTType⟧ᶻ G := by
    simpa [SMTType.toZFSet] using hG
  let hYdom : Y ∈ G.Dom := by
    rw [ZFSet.is_func_dom_eq hGfunc]
    exact hY
  let Gapp : ZFSet.Option ⟦alpha.toSMTType⟧ᶻ :=
    ZFSet.fapply G (ZFSet.is_func_is_pfunc hGfunc) ⟨Y, hYdom⟩
  let someZ := ZFSet.Option.some
    (S := ⟦alpha.toSMTType⟧ᶻ) ⟨Z, hZ⟩
  have happ' : Gapp.val = someZ.val := by
    simpa only [Gapp, someZ, hGfunc, hYdom, proof_irrel_heq] using happ
  have hGappEq : Gapp = someZ := Subtype.ext happ'
  let denApp : SMT.Dom.{u} :=
    ⟨Gapp.val, SMTType.option alpha.toSMTType, Gapp.property⟩
  have hcov_app : RenamingContext.CoversFV Theta
      (SMT.Term.app f x) := by
    intro w hw
    rw [SMT.fv, List.mem_append] at hw
    exact hw.elim (hcov_f w) (hcov_x w)
  have hden_app : ⟦(SMT.Term.app f x).abstract Theta hcov_app⟧ˢ =
      some denApp := by
    rw [SMT.Term.abstract.eq_def, SMT.denote, Option.pure_def,
      Option.bind_eq_bind, Option.bind_eq_some_iff]
    refine ⟨(⟨G, SMTType.fun gamma.toSMTType
      (SMTType.option alpha.toSMTType), hG⟩ : SMT.Dom), hden_f, ?_⟩
    rw [Option.bind_eq_some_iff]
    refine ⟨(⟨Y, gamma.toSMTType, hY⟩ : SMT.Dom), hden_x, ?_⟩
    simp only [dif_pos True.intro,
      dif_pos (ZFSet.is_func_is_pfunc hGfunc), dif_pos hYdom,
      Gapp, denApp, proof_irrel_heq]
  have hcov_out : RenamingContext.CoversFV Theta
      (SMT.Term.the (SMT.Term.app f x)) := by
    intro w hw
    exact hcov_app w (by simpa only [SMT.fv] using hw)
  let denOut : SMT.Dom.{u} :=
    ⟨(ZFSet.Option.the SMTType.toZFSet_nonempty Gapp).val,
      alpha.toSMTType, SetLike.coe_mem _⟩
  have hden_out :
      ⟦(SMT.Term.the (SMT.Term.app f x)).abstract Theta hcov_out⟧ˢ =
        some denOut := by
    rw [SMT.Term.abstract.eq_def, SMT.denote]
    have hden_app' :
        ⟦(SMT.Term.app f x).abstract Theta (fun w hw =>
          hcov_out w (by simpa only [SMT.fv] using hw))⟧ˢ =
          some denApp := by
      simpa only [proof_irrel_heq] using hden_app
    rw [hden_app']
    rfl
  have respects_out : SMT.RenamingContext.RespectsTypeContextOnFV
      Theta Gamma (SMT.Term.the (SMT.Term.app f x)) := by
    intro w sigma hw hlookup
    simp only [SMT.fv, List.mem_append] at hw
    exact hw.elim (fun h => respects_f h hlookup)
      (fun h => respects_x h hlookup)
  have hthe :
      (ZFSet.Option.the SMTType.toZFSet_nonempty Gapp).val = Z := by
    rw [hGappEq, ZFSet.Option.the_some]
  have resultRel : RDomCastSupported (⟨T, alpha, hT⟩ : B.Dom)
      denOut := by
    change RDomCastSupported (⟨T, alpha, hT⟩ : B.Dom)
      (⟨(ZFSet.Option.the SMTType.toZFSet_nonempty Gapp).val,
        alpha.toSMTType, SetLike.coe_mem _⟩ : SMT.Dom)
    apply RDom.toRDomCastSupported
    rw [RDom]
    exact ⟨rfl, hthe.symm ▸ hZret⟩
  exact ⟨hcov_out, denOut, respects_out, hden_out, rfl, resultRel⟩

/-- Construct the graph-collapse helper assignment once the relation term and
argument already use canonical SMT representations. -/
private theorem castApp_relation_term_semantics.{u}
    {gamma alpha : BType} {r x spec : SMT.Term}
    {Lambda Gamma : SMT.TypeContext} {helper u v : SMT.𝒱}
    {used0 used1 : List SMT.𝒱}
    (typ_r : Lambda ⊢ˢ r : SMTType.fun
      (SMTType.pair gamma.toSMTType alpha.toSMTType) SMTType.bool)
    (typ_x : Lambda ⊢ˢ x : gamma.toSMTType)
    (Lambda_sub : Lambda ⊆ Gamma)
    (helper_fresh : helper ∉ Lambda)
    (helper_lookup : Gamma.lookup helper = some
      (SMTType.fun gamma.toSMTType (SMTType.option alpha.toSMTType)))
    (helper_not_used0 : helper ∉ used0)
    (helper_used1 : helper ∈ used1)
    (u_not_used0 : u ∉ used0) (v_not_used0 : v ∉ used0)
    (used_sub : used0 ⊆ used1)
    (helper_ne_u : helper ≠ u) (helper_ne_v : helper ≠ v)
    (u_ne_v : u ≠ v)
    (hspec : spec = SMT.Term.forall [u, v]
      [gamma.toSMTType, alpha.toSMTType]
      (relationOptionTermBody r helper u v))
    {Theta : SMT.RenamingContext.Context.{u}}
    (hcov_r : RenamingContext.CoversFV Theta r)
    (hcov_x : RenamingContext.CoversFV Theta x)
    (Theta_none : ∀ w ∉ used0, Theta w = none)
    (respects_r : SMT.RenamingContext.RespectsTypeContextOnFV
      Theta Lambda r)
    (respects_x : SMT.RenamingContext.RespectsTypeContextOnFV
      Theta Lambda x)
    (Theta_dom : ∀ w, Theta w ≠ none → w ∈ Gamma)
    {F X T R Y : ZFSet.{u}}
    {hF : F ∈ ⟦BType.set (gamma ×ᴮ alpha)⟧ᶻ}
    {hX : X ∈ ⟦gamma⟧ᶻ} {hT : T ∈ ⟦alpha⟧ᶻ}
    {hR : R ∈ ⟦SMTType.fun
      (SMTType.pair gamma.toSMTType alpha.toSMTType) SMTType.bool⟧ᶻ}
    {hY : Y ∈ ⟦gamma.toSMTType⟧ᶻ}
    (hden_r : ⟦r.abstract Theta hcov_r⟧ˢ =
      some (⟨R, SMTType.fun
        (SMTType.pair gamma.toSMTType alpha.toSMTType)
        SMTType.bool, hR⟩ : SMT.Dom))
    (hden_x : ⟦x.abstract Theta hcov_x⟧ˢ =
      some (⟨Y, gamma.toSMTType, hY⟩ : SMT.Dom))
    (Frel : RDomCastSupported
      (⟨F, BType.set (gamma ×ᴮ alpha), hF⟩ : B.Dom)
      (⟨R, SMTType.fun
        (SMTType.pair gamma.toSMTType alpha.toSMTType)
        SMTType.bool, hR⟩ : SMT.Dom))
    (Xrel : RDomCastSupported (⟨X, gamma, hX⟩ : B.Dom)
      (⟨Y, gamma.toSMTType, hY⟩ : SMT.Dom))
    (hfun : F.IsPFunc ⟦gamma⟧ᶻ ⟦alpha⟧ᶻ)
    (hmem : X.pair T ∈ F) :
    ∃ (Theta' : SMT.RenamingContext.Context.{u})
      (hcov_out : RenamingContext.CoversFV Theta'
        (SMT.Term.the (SMT.Term.app (.var helper) x)))
      (denOut : SMT.Dom.{u}),
      RenamingContext.Extends Theta' Theta ∧
      (∀ w ∉ used1, Theta' w = none) ∧
      SMT.RenamingContext.RespectsTypeContextOnFV Theta' Gamma
        (SMT.Term.the (SMT.Term.app (.var helper) x)) ∧
      (∀ w, Theta' w ≠ none → w ∈ Gamma) ∧
      SpecBodiesTrue Theta' Gamma
        (helperSpecChunk helper
          (SMTType.fun gamma.toSMTType (SMTType.option alpha.toSMTType))
          spec) ∧
      ⟦(SMT.Term.the (SMT.Term.app (.var helper) x)).abstract
        Theta' hcov_out⟧ˢ = some denOut ∧
      denOut.snd.fst = alpha.toSMTType ∧
      RDomCastSupported (⟨T, alpha, hT⟩ : B.Dom) denOut := by
  have helper_none : Theta helper = none :=
    Theta_none helper helper_not_used0
  have u_none : Theta u = none := Theta_none u u_not_used0
  have v_none : Theta v = none := Theta_none v v_not_used0
  have helper_not_fv_r : helper ∉ SMT.fv r :=
    fun hw => helper_fresh (SMT.Typing.mem_context_of_mem_fv typ_r hw)
  have helper_not_fv_x : helper ∉ SMT.fv x :=
    fun hw => helper_fresh (SMT.Typing.mem_context_of_mem_fv typ_x hw)
  have u_not_fv_r : u ∉ SMT.fv r := by
    intro hw
    have := hcov_r u hw
    rw [u_none] at this
    contradiction
  have v_not_fv_r : v ∉ SMT.fv r := by
    intro hw
    have := hcov_r v hw
    rw [v_none] at this
    contradiction
  have hfunR := RDomCastSupported.setPred_isPFunc_of_source Frel hfun
  let G := option_func_of_pfun gamma.toSMTType alpha.toSMTType R
  have hG : G ∈ ⟦SMTType.fun gamma.toSMTType
      (SMTType.option alpha.toSMTType)⟧ᶻ :=
    graphCollapse_mem gamma.toSMTType alpha.toSMTType R
  let WG : SMT.Dom.{u} := ⟨G,
    SMTType.fun gamma.toSMTType (SMTType.option alpha.toSMTType), hG⟩
  let Theta' := Function.update Theta helper (some WG)
  have Theta'_ext : RenamingContext.Extends Theta' Theta :=
    RenamingContext.extends_update_of_none helper_none
  have hcov_r' : RenamingContext.CoversFV Theta' r :=
    RenamingContext.coversFV_of_extends_of_coversFV Theta'_ext hcov_r
  have hcov_x' : RenamingContext.CoversFV Theta' x :=
    RenamingContext.coversFV_of_extends_of_coversFV Theta'_ext hcov_x
  have hden_r' : ⟦r.abstract Theta' hcov_r'⟧ˢ =
      some (⟨R, SMTType.fun
        (SMTType.pair gamma.toSMTType alpha.toSMTType)
        SMTType.bool, hR⟩ : SMT.Dom) := by
    have hagree := RenamingContext.agreesOnFV_of_extends_of_coversFV
      Theta'_ext hcov_r
    exact (RenamingContext.denote_congr_of_agreesOnFV
      (t := r) (h1 := hcov_r') (h2 := hcov_r) hagree).trans hden_r
  have hden_x' : ⟦x.abstract Theta' hcov_x'⟧ˢ =
      some (⟨Y, gamma.toSMTType, hY⟩ : SMT.Dom) := by
    have hagree := RenamingContext.agreesOnFV_of_extends_of_coversFV
      Theta'_ext hcov_x
    exact (RenamingContext.denote_congr_of_agreesOnFV
      (t := x) (h1 := hcov_x') (h2 := hcov_x) hagree).trans hden_x
  have respects_r_Gamma :
      SMT.RenamingContext.RespectsTypeContextOnFV Theta Gamma r :=
    respects_r.of_extends (RenamingContext.extends_refl Theta)
      Lambda_sub typ_r
  have respects_x_Gamma :
      SMT.RenamingContext.RespectsTypeContextOnFV Theta Gamma x :=
    respects_x.of_extends (RenamingContext.extends_refl Theta)
      Lambda_sub typ_x
  have respects_r' :
      SMT.RenamingContext.RespectsTypeContextOnFV Theta' Gamma r := by
    intro w sigma hw hlookup
    have hw_ne : w ≠ helper := fun h => by
      subst w
      exact helper_not_fv_r hw
    obtain ⟨d, hd, hdty⟩ := respects_r_Gamma hw hlookup
    exact ⟨d, by simpa [Theta', Function.update_of_ne hw_ne] using hd,
      hdty⟩
  have respects_x' :
      SMT.RenamingContext.RespectsTypeContextOnFV Theta' Gamma x := by
    intro w sigma hw hlookup
    have hw_ne : w ≠ helper := fun h => by
      subst w
      exact helper_not_fv_x hw
    obtain ⟨d, hd, hdty⟩ := respects_x_Gamma hw hlookup
    exact ⟨d, by simpa [Theta', Function.update_of_ne hw_ne] using hd,
      hdty⟩
  have hcov_var : RenamingContext.CoversFV Theta' (.var helper) := by
    intro w hw
    simp only [SMT.fv, List.mem_singleton] at hw
    subst w
    simp [Theta']
  have hden_var : ⟦(SMT.Term.var helper).abstract Theta' hcov_var⟧ˢ =
      some WG := by
    simp [SMT.Term.abstract, Theta']
    rfl
  have respects_var :
      SMT.RenamingContext.RespectsTypeContextOnFV Theta' Gamma
        (.var helper) := by
    intro w sigma hw hlookup
    simp only [SMT.fv, List.mem_singleton] at hw
    subst w
    rw [helper_lookup] at hlookup
    cases hlookup
    exact ⟨WG, by simp [Theta'], rfl⟩
  subst spec
  have hcov_spec : RenamingContext.CoversFV Theta'
      (SMT.Term.forall [u, v]
        [gamma.toSMTType, alpha.toSMTType]
        (relationOptionTermBody r helper u v)) := by
    intro w hw
    rw [mem_fv_relationOptionForall_iff] at hw
    rcases hw.1 with hwr | rfl
    · exact hcov_r' w hwr
    · simp [Theta']
  have respects_spec :
      SMT.RenamingContext.RespectsTypeContextOnFV Theta' Gamma
        (SMT.Term.forall [u, v]
          [gamma.toSMTType, alpha.toSMTType]
          (relationOptionTermBody r helper u v)) := by
    intro w sigma hw hlookup
    rw [mem_fv_relationOptionForall_iff] at hw
    rcases hw.1 with hwr | rfl
    · exact respects_r' hwr hlookup
    · rw [helper_lookup] at hlookup
      cases hlookup
      exact ⟨WG, by simp [Theta'], rfl⟩
  have hgo_cov : ∀ w ∈ SMT.fv
      (relationOptionTermBody r helper u v),
      w ∉ [u, v] → (Theta' w).isSome = true := by
    intro w hw hnot
    rw [mem_fv_relationOptionTermBody_iff] at hw
    rcases hw with hwr | rfl | rfl | rfl
    · exact hcov_r' w hwr
    · simp [Theta']
    · exact False.elim (hnot (by simp))
    · exact False.elim (hnot (by simp))
  have hcov_body_upd : ∀ Wa Wb : SMT.Dom.{u},
      RenamingContext.CoversFV
        (Function.update (Function.update Theta' u (some Wa)) v (some Wb))
        (relationOptionTermBody r helper u v) := by
    intro Wa Wb w hw
    rw [mem_fv_relationOptionTermBody_iff] at hw
    rcases hw with hwr | rfl | rfl | rfl
    · have hwu : w ≠ u := fun h => u_not_fv_r (h ▸ hwr)
      have hwv : w ≠ v := fun h => v_not_fv_r (h ▸ hwr)
      simpa [Function.update_of_ne hwv, Function.update_of_ne hwu]
        using hcov_r' w hwr
    · simp [Function.update_of_ne helper_ne_v,
        Function.update_of_ne helper_ne_u, Theta']
    · simp [Function.update_of_ne u_ne_v]
    · simp
  have hcov_r_upd : ∀ Wa Wb : SMT.Dom.{u},
      RenamingContext.CoversFV
        (Function.update (Function.update Theta' u (some Wa)) v (some Wb)) r := by
    intro Wa Wb w hw
    have hwu : w ≠ u := fun h => u_not_fv_r (h ▸ hw)
    have hwv : w ≠ v := fun h => v_not_fv_r (h ▸ hw)
    simpa [Function.update_of_ne hwv, Function.update_of_ne hwu]
      using hcov_r' w hw
  have hden_r_upd : ∀ Wa Wb : SMT.Dom.{u},
      ⟦r.abstract
        (Function.update (Function.update Theta' u (some Wa)) v (some Wb))
        (hcov_r_upd Wa Wb)⟧ˢ =
      some (⟨R, SMTType.fun
        (SMTType.pair gamma.toSMTType alpha.toSMTType)
        SMTType.bool, hR⟩ : SMT.Dom) := by
    intro Wa Wb
    have hagree : RenamingContext.AgreesOnFV
        (Function.update (Function.update Theta' u (some Wa)) v (some Wb))
        Theta' r := by
      intro w hw
      have hwu : w ≠ u := fun h => u_not_fv_r (h ▸ hw)
      have hwv : w ≠ v := fun h => v_not_fv_r (h ▸ hw)
      simp [Function.update_of_ne hwv, Function.update_of_ne hwu]
    exact (RenamingContext.denote_congr_of_agreesOnFV
      (h1 := hcov_r_upd Wa Wb) (h2 := hcov_r') hagree).trans hden_r'
  have hlookupG : ∀ Wa Wb : SMT.Dom.{u},
      Function.update (Function.update Theta' u (some Wa)) v (some Wb)
          helper = some WG := by
    intro Wa Wb
    simp [Function.update_of_ne helper_ne_v,
      Function.update_of_ne helper_ne_u, Theta']
  have hlookupU : ∀ Wa Wb : SMT.Dom.{u},
      Function.update (Function.update Theta' u (some Wa)) v (some Wb) u =
        some Wa := by
    intro Wa Wb
    simp [Function.update_of_ne u_ne_v]
  have hlookupV : ∀ Wa Wb : SMT.Dom.{u},
      Function.update (Function.update Theta' u (some Wa)) v (some Wb) v =
        some Wb := by simp
  have hden_spec := relation_option_term_forall_graphCollapse
    gamma.toSMTType alpha.toSMTType hR hfunR hcov_spec hgo_cov
    hcov_body_upd hcov_r_upd hden_r_upd hlookupG hlookupU hlookupV
  have hRret : retract (BType.set (gamma ×ᴮ alpha)) R = F :=
    ((RDomCast.iff_RDom_of_type_eq
      (α := BType.set (gamma ×ᴮ alpha)) rfl).mp
      Frel.toRDomCast).2
  have FrelG : RDomCastSupported
      (⟨F, BType.set (gamma ×ᴮ alpha), hF⟩ : B.Dom) WG := by
    simpa only [G, WG] using
      RDomCastSupported.functionalGraph_as_optionFunction
        gamma alpha hF hR hfunR hRret
  obtain ⟨hcov_out, denOut, respects_out, hden_out,
      denOutTy, resultRel⟩ :=
    castApp_option_term_semantics hcov_var hcov_x' respects_var
      respects_x' hden_var hden_x' FrelG Xrel hmem
  have Theta'_none : ∀ w ∉ used1, Theta' w = none := by
    intro w hw
    have hw_ne : w ≠ helper := fun h => by
      subst w
      exact hw helper_used1
    simpa [Theta', Function.update_of_ne hw_ne] using
      Theta_none w (fun hw0 => hw (used_sub hw0))
  have Theta'_dom : ∀ w, Theta' w ≠ none → w ∈ Gamma := by
    intro w hw
    by_cases hwh : w = helper
    · subst w
      exact AList.lookup_isSome.mp (by rw [helper_lookup]; rfl)
    · exact Theta_dom w (by
        simpa [Theta', Function.update_of_ne hwh] using hw)
  have specs_true : SpecBodiesTrue Theta' Gamma
      (helperSpecChunk helper
        (SMTType.fun gamma.toSMTType (SMTType.option alpha.toSMTType))
        (SMT.Term.forall [u, v]
          [gamma.toSMTType, alpha.toSMTType]
          (relationOptionTermBody r helper u v))) := by
    intro body hbody
    simp only [specBodies_helperSpecChunk, List.mem_singleton] at hbody
    subst body
    exact ⟨hcov_spec, ⟨ZFSet.zftrue, SMTType.bool,
      ZFSet.ZFBool.zftrue_mem_𝔹⟩, respects_spec, hden_spec, rfl, rfl⟩
  exact ⟨Theta', hcov_out, denOut, Theta'_ext, Theta'_none,
    respects_out, Theta'_dom, specs_true, hden_out, denOutTy, resultRel⟩

/- Guarded relation-to-option correctness: every typed assignment satisfying
the quantified helper specification yields the source application result. -/
set_option maxHeartbeats 4000000 in
private theorem castApp_relation_term_guarded_semantics.{u}
    {gamma alpha : BType} {r x spec : SMT.Term}
    {Lambda GammaSup : SMT.TypeContext} {helper u v : SMT.𝒱}
    (scope : ScopedContextExtends Lambda
      (helperSpecChunk helper
        (SMTType.fun gamma.toSMTType (SMTType.option alpha.toSMTType))
        spec) GammaSup)
    (typ_r : Lambda ⊢ˢ r : SMTType.fun
      (SMTType.pair gamma.toSMTType alpha.toSMTType) SMTType.bool)
    (typ_x : Lambda ⊢ˢ x : gamma.toSMTType)
    (helper_fresh : helper ∉ Lambda)
    (u_fresh : u ∉ Lambda) (v_fresh : v ∉ Lambda)
    (helper_ne_u : helper ≠ u) (helper_ne_v : helper ≠ v)
    (u_ne_v : u ≠ v)
    (hspec : spec = SMT.Term.forall [u, v]
      [gamma.toSMTType, alpha.toSMTType]
      (relationOptionTermBody r helper u v))
    {Theta : SMT.RenamingContext.Context.{u}}
    (hcov_r : RenamingContext.CoversFV Theta r)
    (hcov_x : RenamingContext.CoversFV Theta x)
    (respects_r : SMT.RenamingContext.RespectsTypeContextOnFV
      Theta GammaSup r)
    (respects_x : SMT.RenamingContext.RespectsTypeContextOnFV
      Theta GammaSup x)
    {F X T R Y : ZFSet.{u}}
    {hF : F ∈ ⟦BType.set (gamma ×ᴮ alpha)⟧ᶻ}
    {hX : X ∈ ⟦gamma⟧ᶻ} {hT : T ∈ ⟦alpha⟧ᶻ}
    {hR : R ∈ ⟦SMTType.fun
      (SMTType.pair gamma.toSMTType alpha.toSMTType) SMTType.bool⟧ᶻ}
    {hY : Y ∈ ⟦gamma.toSMTType⟧ᶻ}
    (hden_r : ⟦r.abstract Theta hcov_r⟧ˢ =
      some (⟨R, SMTType.fun
        (SMTType.pair gamma.toSMTType alpha.toSMTType)
        SMTType.bool, hR⟩ : SMT.Dom))
    (hden_x : ⟦x.abstract Theta hcov_x⟧ˢ =
      some (⟨Y, gamma.toSMTType, hY⟩ : SMT.Dom))
    (Frel : RDomCastSupported
      (⟨F, BType.set (gamma ×ᴮ alpha), hF⟩ : B.Dom)
      (⟨R, SMTType.fun
        (SMTType.pair gamma.toSMTType alpha.toSMTType)
        SMTType.bool, hR⟩ : SMT.Dom))
    (Xrel : RDomCastSupported (⟨X, gamma, hX⟩ : B.Dom)
      (⟨Y, gamma.toSMTType, hY⟩ : SMT.Dom))
    (hmem : X.pair T ∈ F)
    (hcov_out : RenamingContext.CoversFV Theta
      (SMT.Term.the (SMT.Term.app (.var helper) x)))
    (denOut : SMT.Dom.{u})
    (respects_out : SMT.RenamingContext.RespectsTypeContextOnFV
      Theta GammaSup (SMT.Term.the (SMT.Term.app (.var helper) x)))
    (specs_true : SpecBodiesTrue Theta GammaSup
      (helperSpecChunk helper
        (SMTType.fun gamma.toSMTType (SMTType.option alpha.toSMTType))
        spec))
    (hden_out :
      ⟦(SMT.Term.the (SMT.Term.app (.var helper) x)).abstract
        Theta hcov_out⟧ˢ = some denOut)
    (_denOutTy : denOut.snd.fst = alpha.toSMTType) :
    RDomCastSupported (⟨T, alpha, hT⟩ : B.Dom) denOut := by
  subst spec
  have helper_lookup : GammaSup.lookup helper = some
      (SMTType.fun gamma.toSMTType (SMTType.option alpha.toSMTType)) :=
    scope.lookup_of_declared (by simp [declEntries_helperSpecChunk])
  have helper_some : (Theta helper).isSome = true := by
    apply hcov_out helper
    simp only [SMT.fv, List.mem_append, List.mem_singleton]
    exact Or.inl trivial
  obtain ⟨WG, hWG⟩ := Option.isSome_iff_exists.mp helper_some
  have helper_fv_out : helper ∈ SMT.fv
      (SMT.Term.the (SMT.Term.app (.var helper) x)) := by
    simp only [SMT.fv, List.mem_append, List.mem_singleton]
    exact Or.inl trivial
  have WGty : WG.snd.fst =
      SMTType.fun gamma.toSMTType (SMTType.option alpha.toSMTType) := by
    obtain ⟨d, hd, hdty⟩ :=
      respects_out helper_fv_out helper_lookup
    rw [hWG] at hd
    injection hd with hdeq
    subst d
    exact hdty
  rcases WG with ⟨G, sigmaG, hG⟩
  dsimp at WGty
  subst sigmaG
  have helper_not_fv_r : helper ∉ SMT.fv r :=
    fun hw => helper_fresh (SMT.Typing.mem_context_of_mem_fv typ_r hw)
  have u_not_fv_r : u ∉ SMT.fv r :=
    fun hw => u_fresh (SMT.Typing.mem_context_of_mem_fv typ_r hw)
  have v_not_fv_r : v ∉ SMT.fv r :=
    fun hw => v_fresh (SMT.Typing.mem_context_of_mem_fv typ_r hw)
  have hspec_true := specs_true
    (SMT.Term.forall [u, v]
      [gamma.toSMTType, alpha.toSMTType]
      (relationOptionTermBody r helper u v)) (by simp)
  obtain ⟨hcov_spec, Phi, _respects_spec, hden_spec,
      _PhiTy, PhiTrue⟩ := hspec_true
  have hgo_cov : ∀ w ∈ SMT.fv
      (relationOptionTermBody r helper u v),
      w ∉ [u, v] → (Theta w).isSome = true := by
    intro w hw hnot
    rw [mem_fv_relationOptionTermBody_iff] at hw
    rcases hw with hwr | rfl | rfl | rfl
    · exact hcov_r w hwr
    · exact helper_some
    · exact False.elim (hnot (by simp))
    · exact False.elim (hnot (by simp))
  have hcov_body_upd : ∀ Wa Wb : SMT.Dom.{u},
      RenamingContext.CoversFV
        (Function.update (Function.update Theta u (some Wa)) v (some Wb))
        (relationOptionTermBody r helper u v) := by
    intro Wa Wb w hw
    rw [mem_fv_relationOptionTermBody_iff] at hw
    rcases hw with hwr | rfl | rfl | rfl
    · have hwu : w ≠ u := fun h => u_not_fv_r (h ▸ hwr)
      have hwv : w ≠ v := fun h => v_not_fv_r (h ▸ hwr)
      simpa [Function.update_of_ne hwv, Function.update_of_ne hwu]
        using hcov_r w hwr
    · simpa [Function.update_of_ne helper_ne_v,
        Function.update_of_ne helper_ne_u] using helper_some
    · simp [Function.update_of_ne u_ne_v]
    · simp
  have hcov_r_upd : ∀ Wa Wb : SMT.Dom.{u},
      RenamingContext.CoversFV
        (Function.update (Function.update Theta u (some Wa)) v (some Wb)) r := by
    intro Wa Wb w hw
    have hwu : w ≠ u := fun h => u_not_fv_r (h ▸ hw)
    have hwv : w ≠ v := fun h => v_not_fv_r (h ▸ hw)
    simpa [Function.update_of_ne hwv, Function.update_of_ne hwu]
      using hcov_r w hw
  have hden_r_upd : ∀ Wa Wb : SMT.Dom.{u},
      ⟦r.abstract
        (Function.update (Function.update Theta u (some Wa)) v (some Wb))
        (hcov_r_upd Wa Wb)⟧ˢ =
      some (⟨R, SMTType.fun
        (SMTType.pair gamma.toSMTType alpha.toSMTType)
        SMTType.bool, hR⟩ : SMT.Dom) := by
    intro Wa Wb
    have hagree : RenamingContext.AgreesOnFV
        (Function.update (Function.update Theta u (some Wa)) v (some Wb))
        Theta r := by
      intro w hw
      have hwu : w ≠ u := fun h => u_not_fv_r (h ▸ hw)
      have hwv : w ≠ v := fun h => v_not_fv_r (h ▸ hw)
      simp [Function.update_of_ne hwv, Function.update_of_ne hwu]
    exact (RenamingContext.denote_congr_of_agreesOnFV
      (h1 := hcov_r_upd Wa Wb) (h2 := hcov_r) hagree).trans hden_r
  have hlookupG : ∀ Wa Wb : SMT.Dom.{u},
      Function.update (Function.update Theta u (some Wa)) v (some Wb)
          helper =
        some (⟨G, SMTType.fun gamma.toSMTType
          (SMTType.option alpha.toSMTType), hG⟩ : SMT.Dom) := by
    intro Wa Wb
    simpa [Function.update_of_ne helper_ne_v,
      Function.update_of_ne helper_ne_u] using hWG
  have hlookupU : ∀ Wa Wb : SMT.Dom.{u},
      Function.update (Function.update Theta u (some Wa)) v (some Wb) u =
        some Wa := by
    intro Wa Wb
    simp [Function.update_of_ne u_ne_v]
  have hlookupV : ∀ Wa Wb : SMT.Dom.{u},
      Function.update (Function.update Theta u (some Wa)) v (some Wb) v =
        some Wb := by simp
  let dT : B.Dom.{u} := ⟨T, alpha, hT⟩
  let WZ : SMT.Dom.{u} := dT.canonicalSMT
  have WZty : WZ.snd.fst = alpha.toSMTType := by
    simp [WZ, dT]
  have hZ : WZ.fst ∈ ⟦alpha.toSMTType⟧ᶻ := by
    rw [← WZty]
    exact WZ.snd.snd
  have hZret : retract alpha WZ.fst = T := by
    have hcanonical := B.Dom.rdom_canonicalSMT dT
    rw [RDom] at hcanonical
    exact hcanonical.2
  let WY : SMT.Dom.{u} := ⟨Y, gamma.toSMTType, hY⟩
  have hpoint := relation_option_term_forall_pointwise_of_true
    gamma.toSMTType alpha.toSMTType hR hG hcov_spec hgo_cov
    hcov_body_upd hcov_r_upd hden_r_upd hlookupG hlookupU hlookupV
    hden_spec PhiTrue WY WZ rfl WZty
  have hYret : retract gamma Y = X :=
    ((RDomCast.iff_RDom_of_type_eq (α := gamma) rfl).mp
      Xrel.toRDomCast).2
  have hRret : retract (BType.set (gamma ×ᴮ alpha)) R = F :=
    ((RDomCast.iff_RDom_of_type_eq
      (α := BType.set (gamma ×ᴮ alpha)) rfl).mp
      Frel.toRDomCast).2
  have hpairRet : retract (gamma ×ᴮ alpha) (Y.pair WZ.fst) =
      X.pair T := by
    simp only [retract, ZFSet.π₁_pair, ZFSet.π₂_pair,
      hYret, hZret]
  have hRappTrue := (RDomCast.setPred_apply_eq_zftrue_iff
    (τ := gamma ×ᴮ alpha)
    (X := X.pair T) (S := F) (Y := Y.pair WZ.fst) (F := R)
    (ZFSet.pair_mem_prod.mpr ⟨hX, hT⟩)
    (ZFSet.pair_mem_prod.mpr ⟨hY, hZ⟩)
    hR hpairRet hRret).mpr hmem
  have hEqTrue :
      let hGfunc : ZFSet.IsFunc ⟦gamma.toSMTType⟧ᶻ
          ⟦SMTType.option alpha.toSMTType⟧ᶻ G := by
        simpa [SMTType.toZFSet] using hG
      let hGdom : Y ∈ G.Dom := by
        rw [ZFSet.is_func_dom_eq hGfunc]
        exact hY
      let Gapp := ZFSet.fapply G (ZFSet.is_func_is_pfunc hGfunc)
        ⟨Y, hGdom⟩
      let someZ := ZFSet.Option.some
        (S := ⟦alpha.toSMTType⟧ᶻ) ⟨WZ.fst, hZ⟩
      zfEqIn ⟦SMTType.option alpha.toSMTType⟧ᶻ
        Gapp.val someZ.val = ZFSet.zftrue := by
    dsimp only
    rw [← hpoint]
    simpa only [WY, proof_irrel_heq] using hRappTrue
  have happ :
      let hGfunc : ZFSet.IsFunc ⟦gamma.toSMTType⟧ᶻ
          ⟦SMTType.option alpha.toSMTType⟧ᶻ G := by
        simpa [SMTType.toZFSet] using hG
      let hGdom : Y ∈ G.Dom := by
        rw [ZFSet.is_func_dom_eq hGfunc]
        exact hY
      let Gapp := ZFSet.fapply G (ZFSet.is_func_is_pfunc hGfunc)
        ⟨Y, hGdom⟩
      let someZ := ZFSet.Option.some
        (S := ⟦alpha.toSMTType⟧ᶻ) ⟨WZ.fst, hZ⟩
      Gapp.val = someZ.val := by
    dsimp only
    exact (zfEqIn_eq_zftrue_iff
      (ZFSet.fapply_mem_range _ _) (SetLike.coe_mem _)).mp hEqTrue
  have hcov_var : RenamingContext.CoversFV Theta (.var helper) := by
    intro w hw
    simp only [SMT.fv, List.mem_singleton] at hw
    subst w
    exact helper_some
  have hden_var :
      ⟦(SMT.Term.var helper).abstract Theta hcov_var⟧ˢ =
        some (⟨G, SMTType.fun gamma.toSMTType
          (SMTType.option alpha.toSMTType), hG⟩ : SMT.Dom) := by
    rw [SMT.Term.abstract.eq_def]
    simp only [SMT.denote]
    have hget := Option.get_of_eq_some helper_some hWG
    rw [hget]
    rfl
  have respects_var :
      SMT.RenamingContext.RespectsTypeContextOnFV Theta GammaSup
        (.var helper) := by
    intro w sigma hw hlookup
    simp only [SMT.fv, List.mem_singleton] at hw
    subst w
    rw [helper_lookup] at hlookup
    cases hlookup
    exact ⟨⟨G, SMTType.fun gamma.toSMTType
      (SMTType.option alpha.toSMTType), hG⟩, hWG, rfl⟩
  obtain ⟨hcov_expected, denExpected, _respects_expected,
      hden_expected, _denExpectedTy, expectedRel⟩ :=
    castApp_option_term_semantics_of_apply_some hcov_var hcov_x
      respects_var respects_x hden_var hden_x hZret happ
  have hcov_eq : hcov_expected = hcov_out := Subsingleton.elim _ _
  subst hcov_expected
  rw [hden_out] at hden_expected
  have hden_eq : denExpected = denOut :=
    (Option.some.inj hden_expected).symm
  rw [← hden_eq]
  exact expectedRel

private theorem castApp_relation_arg_semantics.{u}
    {gamma alpha : BType} {f x xspec gspec : SMT.Term} {sx : SMTType}
    {Lambda Lambda1 Gamma : SMT.TypeContext}
    {xhelper ghelper u v : SMT.𝒱}
    {used0 usedMid used1 : List SMT.𝒱}
    (typ_f : Lambda ⊢ˢ f : SMTType.fun
      (SMTType.pair gamma.toSMTType alpha.toSMTType) SMTType.bool)
    (typ_x : Lambda ⊢ˢ x : sx)
    (typ_f1 : Lambda1 ⊢ˢ f : SMTType.fun
      (SMTType.pair gamma.toSMTType alpha.toSMTType) SMTType.bool)
    (typ_xhelper : Lambda1 ⊢ˢ (.var xhelper) : gamma.toSMTType)
    (Lambda_sub1 : Lambda ⊆ Lambda1) (Lambda1_sub : Lambda1 ⊆ Gamma)
    (xhelper_fresh : xhelper ∉ Lambda)
    (xhelper_lookup : Lambda1.lookup xhelper = some gamma.toSMTType)
    (xhelper_not_used0 : xhelper ∉ used0)
    (xhelper_usedMid : xhelper ∈ usedMid)
    (used_sub_mid : used0 ⊆ usedMid)
    (xspec_fv : SMT.fv xspec ⊆ SMT.fv x ∪ {xhelper})
    (c : sx ~> gamma.toSMTType)
    (exactness :
      ∀ (Theta : SMT.RenamingContext.Context.{u})
        (hx : RenamingContext.CoversFV Theta x)
        (_respects : SMT.RenamingContext.RespectsTypeContextOnFV
          Theta Lambda x)
        (pf : ∀ (x_ : SMT.𝒱) (X_ : SMT.Dom),
          ∀ w ∈ SMT.fv (SMT.Term.var x_),
            (Function.update Theta x_ (some X_) w).isSome = true),
      ∀ (denX : SMT.Dom), ⟦x.abstract Theta hx⟧ˢ = some denX →
        ∃ (Phi H : SMT.Dom)
          (_ : ⟦(SMT.Term.var xhelper).abstract
            (Function.update Theta xhelper (some H)) (pf xhelper H)⟧ˢ =
              some H)
          (hphi : RenamingContext.CoversFV
            (Function.update Theta xhelper (some H)) xspec)
          (_ : ⟦xspec.abstract (Function.update Theta xhelper (some H))
            hphi⟧ˢ = some Phi),
          H.snd.fst = gamma.toSMTType ∧
          Phi.snd.fst = SMTType.bool ∧
          (Phi.fst = zftrue ∧
            denX.fst.pair H.fst ∈ (castZF_of_path c).1) ∧
          (∀ (Y : SMT.Dom) (_ : Y.snd.fst = gamma.toSMTType)
            (hphiY : RenamingContext.CoversFV
              (Function.update Theta xhelper (some Y)) xspec),
            (⟦xspec.abstract (Function.update Theta xhelper (some Y))
              hphiY⟧ˢ).isSome = true ∧
            ∀ {PhiY : SMT.Dom},
              ⟦xspec.abstract (Function.update Theta xhelper (some Y))
                hphiY⟧ˢ = some PhiY →
              PhiY.fst = zftrue →
              denX.fst.pair Y.fst ∈ (castZF_of_path c).1))
    (ghelper_fresh : ghelper ∉ Lambda1)
    (ghelper_lookup : Gamma.lookup ghelper = some
      (SMTType.fun gamma.toSMTType (SMTType.option alpha.toSMTType)))
    (ghelper_not_usedMid : ghelper ∉ usedMid)
    (ghelper_used1 : ghelper ∈ used1)
    (u_not_usedMid : u ∉ usedMid) (v_not_usedMid : v ∉ usedMid)
    (used_mid_sub : usedMid ⊆ used1)
    (ghelper_ne_u : ghelper ≠ u) (ghelper_ne_v : ghelper ≠ v)
    (u_ne_v : u ≠ v)
    (hgspec : gspec = SMT.Term.forall [u, v]
      [gamma.toSMTType, alpha.toSMTType]
      (relationOptionTermBody f ghelper u v))
    {Theta : SMT.RenamingContext.Context.{u}}
    (hcov_f : RenamingContext.CoversFV Theta f)
    (hcov_x : RenamingContext.CoversFV Theta x)
    (Theta_none : ∀ w ∉ used0, Theta w = none)
    (respects_f : SMT.RenamingContext.RespectsTypeContextOnFV
      Theta Lambda f)
    (respects_x : SMT.RenamingContext.RespectsTypeContextOnFV
      Theta Lambda x)
    (Theta_dom : ∀ w, Theta w ≠ none → w ∈ Gamma)
    {F X T R X0 : ZFSet.{u}}
    {hF : F ∈ ⟦BType.set (gamma ×ᴮ alpha)⟧ᶻ}
    {hX : X ∈ ⟦gamma⟧ᶻ} {hT : T ∈ ⟦alpha⟧ᶻ}
    {hR : R ∈ ⟦SMTType.fun
      (SMTType.pair gamma.toSMTType alpha.toSMTType) SMTType.bool⟧ᶻ}
    {hX0 : X0 ∈ ⟦sx⟧ᶻ}
    (hden_f : ⟦f.abstract Theta hcov_f⟧ˢ =
      some (⟨R, SMTType.fun
        (SMTType.pair gamma.toSMTType alpha.toSMTType)
        SMTType.bool, hR⟩ : SMT.Dom))
    (hden_x : ⟦x.abstract Theta hcov_x⟧ˢ =
      some (⟨X0, sx, hX0⟩ : SMT.Dom))
    (Frel : RDomCastSupported
      (⟨F, BType.set (gamma ×ᴮ alpha), hF⟩ : B.Dom)
      (⟨R, SMTType.fun
        (SMTType.pair gamma.toSMTType alpha.toSMTType)
        SMTType.bool, hR⟩ : SMT.Dom))
    (Xrel : RDomCastSupported (⟨X, gamma, hX⟩ : B.Dom)
      (⟨X0, sx, hX0⟩ : SMT.Dom))
    (hfun : F.IsPFunc ⟦gamma⟧ᶻ ⟦alpha⟧ᶻ)
    (hmem : X.pair T ∈ F) :
    ∃ (Theta' : SMT.RenamingContext.Context.{u})
      (hcov_out : RenamingContext.CoversFV Theta'
        (SMT.Term.the (SMT.Term.app (.var ghelper) (.var xhelper))))
      (denOut : SMT.Dom.{u}),
      RenamingContext.Extends Theta' Theta ∧
      (∀ w ∉ used1, Theta' w = none) ∧
      SMT.RenamingContext.RespectsTypeContextOnFV Theta' Gamma
        (SMT.Term.the (SMT.Term.app (.var ghelper) (.var xhelper))) ∧
      (∀ w, Theta' w ≠ none → w ∈ Gamma) ∧
      SpecBodiesTrue Theta' Gamma
        (helperSpecChunk xhelper gamma.toSMTType xspec ++
          helperSpecChunk ghelper
            (SMTType.fun gamma.toSMTType (SMTType.option alpha.toSMTType))
            gspec) ∧
      ⟦(SMT.Term.the (SMT.Term.app (.var ghelper) (.var xhelper))).abstract
        Theta' hcov_out⟧ˢ = some denOut ∧
      denOut.snd.fst = alpha.toSMTType ∧
      RDomCastSupported (⟨T, alpha, hT⟩ : B.Dom) denOut := by
  have xhelper_none : Theta xhelper = none :=
    Theta_none xhelper xhelper_not_used0
  let pf : ∀ (w : SMT.𝒱) (H : SMT.Dom),
      ∀ z ∈ SMT.fv (SMT.Term.var w),
        (Function.update Theta w (some H) z).isSome = true := by
    intro w H z hz
    simp only [SMT.fv, List.mem_singleton] at hz
    subst z
    simp
  obtain ⟨Phi, H, hden_var, hcov_xspec, hden_xspec, Hty, Phity,
      ⟨PhiTrue, castPair⟩, _guard⟩ :=
    exactness Theta hcov_x respects_x pf
      (⟨X0, sx, hX0⟩ : SMT.Dom) hden_x
  let Theta1 := Function.update Theta xhelper (some H)
  have Theta1_ext : RenamingContext.Extends Theta1 Theta :=
    RenamingContext.extends_update_of_none xhelper_none
  have xhelper_not_fv_f : xhelper ∉ SMT.fv f :=
    fun hw => xhelper_fresh (SMT.Typing.mem_context_of_mem_fv typ_f hw)
  have hcov_f1 : RenamingContext.CoversFV Theta1 f :=
    RenamingContext.coversFV_of_extends_of_coversFV Theta1_ext hcov_f
  have hden_f1 : ⟦f.abstract Theta1 hcov_f1⟧ˢ =
      some (⟨R, SMTType.fun
        (SMTType.pair gamma.toSMTType alpha.toSMTType)
        SMTType.bool, hR⟩ : SMT.Dom) := by
    have hagree := RenamingContext.agreesOnFV_of_extends_of_coversFV
      Theta1_ext hcov_f
    exact (RenamingContext.denote_congr_of_agreesOnFV
      (t := f) (h1 := hcov_f1) (h2 := hcov_f) hagree).trans hden_f
  have hcov_xvar : RenamingContext.CoversFV Theta1 (.var xhelper) := by
    intro w hw
    simp only [SMT.fv, List.mem_singleton] at hw
    subst w
    simp [Theta1]
  have hden_xvar : ⟦(SMT.Term.var xhelper).abstract
      Theta1 hcov_xvar⟧ˢ = some H := by
    simpa only [Theta1, proof_irrel_heq] using hden_var
  have respects_f_Lambda1 :
      SMT.RenamingContext.RespectsTypeContextOnFV Theta Lambda1 f :=
    respects_f.of_extends (RenamingContext.extends_refl Theta)
      Lambda_sub1 typ_f
  have respects_f1 :
      SMT.RenamingContext.RespectsTypeContextOnFV Theta1 Lambda1 f := by
    intro w sigma hw hlookup
    have hw_ne : w ≠ xhelper := fun h => by
      subst w
      exact xhelper_not_fv_f hw
    obtain ⟨d, hd, hdty⟩ := respects_f_Lambda1 hw hlookup
    exact ⟨d, by simpa [Theta1, Function.update_of_ne hw_ne] using hd,
      hdty⟩
  have respects_xvar :
      SMT.RenamingContext.RespectsTypeContextOnFV Theta1 Lambda1
        (.var xhelper) := by
    intro w sigma hw hlookup
    simp only [SMT.fv, List.mem_singleton] at hw
    subst w
    rw [xhelper_lookup] at hlookup
    cases hlookup
    exact ⟨H, by simp [Theta1], Hty⟩
  have Hmem : H.fst ∈ ⟦gamma.toSMTType⟧ᶻ := by
    rw [← Hty]
    exact H.snd.snd
  have Heq : H = (⟨H.fst, gamma.toSMTType, Hmem⟩ : SMT.Dom) := by
    rcases H with ⟨Hv, Hsigma, hHv⟩
    dsimp at Hty
    subst Hsigma
    rfl
  have hden_xcanon : ⟦(SMT.Term.var xhelper).abstract
      Theta1 hcov_xvar⟧ˢ =
      some (⟨H.fst, gamma.toSMTType, Hmem⟩ : SMT.Dom) := by
    rw [← Heq]
    exact hden_xvar
  have XrelH : RDomCastSupported (⟨X, gamma, hX⟩ : B.Dom)
      (⟨H.fst, gamma.toSMTType, Hmem⟩ : SMT.Dom) :=
    RDomCastSupported.of_cast_to_canonical Xrel c castPair
  have Theta1_none : ∀ w ∉ usedMid, Theta1 w = none := by
    intro w hw
    have hw_ne : w ≠ xhelper := fun h => by
      subst w
      exact hw xhelper_usedMid
    simpa [Theta1, Function.update_of_ne hw_ne] using
      Theta_none w (fun hw0 => hw (used_sub_mid hw0))
  have Theta1_dom : ∀ w, Theta1 w ≠ none → w ∈ Gamma := by
    intro w hw
    by_cases hwx : w = xhelper
    · subst w
      exact AList.mem_of_subset Lambda1_sub
        (AList.lookup_isSome.mp (by rw [xhelper_lookup]; rfl))
    · exact Theta_dom w (by
        simpa [Theta1, Function.update_of_ne hwx] using hw)
  have ghelper_lookup' : Gamma.lookup ghelper = some
      (SMTType.fun gamma.toSMTType (SMTType.option alpha.toSMTType)) :=
    ghelper_lookup
  obtain ⟨Theta2, hcov_out, denOut, Theta2_ext, Theta2_none,
      respects_out, Theta2_dom, specs_g, hden_out, denOutTy, resultRel⟩ :=
    castApp_relation_term_semantics typ_f1 typ_xhelper Lambda1_sub
      ghelper_fresh ghelper_lookup' ghelper_not_usedMid ghelper_used1
      u_not_usedMid v_not_usedMid used_mid_sub ghelper_ne_u
      ghelper_ne_v u_ne_v hgspec hcov_f1 hcov_xvar Theta1_none
      respects_f1 respects_xvar Theta1_dom hden_f1 hden_xcanon Frel
      XrelH hfun hmem
  have respects_x_Gamma :
      SMT.RenamingContext.RespectsTypeContextOnFV Theta Gamma x :=
    respects_x.of_extends (RenamingContext.extends_refl Theta)
      (AList.subset_trans Lambda_sub1 Lambda1_sub) typ_x
  have xhelper_lookup_Gamma : Gamma.lookup xhelper = some gamma.toSMTType :=
    AList.lookup_of_subset Lambda1_sub xhelper_lookup
  have respects_xspec :
      SMT.RenamingContext.RespectsTypeContextOnFV Theta1 Gamma xspec :=
    SMT.RenamingContext.respects_update_helper xspec_fv
      respects_x_Gamma xhelper_lookup_Gamma Hty
  have specs_x : SpecBodiesTrue Theta1 Gamma
      (helperSpecChunk xhelper gamma.toSMTType xspec) := by
    intro body hbody
    simp only [specBodies_helperSpecChunk, List.mem_singleton] at hbody
    subst body
    exact ⟨hcov_xspec, Phi, respects_xspec, hden_xspec,
      Phity, PhiTrue⟩
  have specs_x2 : SpecBodiesTrue Theta2 Gamma
      (helperSpecChunk xhelper gamma.toSMTType xspec) :=
    SpecBodiesTrue.of_extends specs_x Theta2_ext
      (fun _ hw => hw) Theta1_dom
  have specs_all := SpecBodiesTrue.append specs_x2 specs_g
  exact ⟨Theta2, hcov_out, denOut,
    RenamingContext.extends_trans Theta2_ext Theta1_ext,
    Theta2_none, respects_out, Theta2_dom, specs_all,
    hden_out, denOutTy, resultRel⟩

private theorem castApp_relation_arg_guarded_semantics.{u}
    {gamma alpha : BType} {f x xspec gspec : SMT.Term} {sx : SMTType}
    {Lambda Lambda1 GammaSup : SMT.TypeContext}
    {xhelper ghelper u v : SMT.𝒱}
    (x_ctx_gen : ContextGeneratedByDeclarations Lambda Lambda1
      (helperSpecChunk xhelper gamma.toSMTType xspec))
    (scope : ScopedContextExtends Lambda
      (helperSpecChunk xhelper gamma.toSMTType xspec ++
        helperSpecChunk ghelper
          (SMTType.fun gamma.toSMTType (SMTType.option alpha.toSMTType))
          gspec) GammaSup)
    (typ_x : Lambda ⊢ˢ x : sx)
    (typ_f1 : Lambda1 ⊢ˢ f : SMTType.fun
      (SMTType.pair gamma.toSMTType alpha.toSMTType) SMTType.bool)
    (typ_xhelper : Lambda1 ⊢ˢ (.var xhelper) : gamma.toSMTType)
    (c : sx ~> gamma.toSMTType)
    (exactness :
      ∀ (Theta : SMT.RenamingContext.Context.{u})
        (hx : RenamingContext.CoversFV Theta x)
        (_respects : SMT.RenamingContext.RespectsTypeContextOnFV
          Theta Lambda x)
        (pf : ∀ (x_ : SMT.𝒱) (X_ : SMT.Dom),
          ∀ w ∈ SMT.fv (SMT.Term.var x_),
            (Function.update Theta x_ (some X_) w).isSome = true),
      ∀ (denX : SMT.Dom), ⟦x.abstract Theta hx⟧ˢ = some denX →
        ∃ (Phi H : SMT.Dom)
          (_ : ⟦(SMT.Term.var xhelper).abstract
            (Function.update Theta xhelper (some H)) (pf xhelper H)⟧ˢ =
              some H)
          (hphi : RenamingContext.CoversFV
            (Function.update Theta xhelper (some H)) xspec)
          (_ : ⟦xspec.abstract (Function.update Theta xhelper (some H))
            hphi⟧ˢ = some Phi),
          H.snd.fst = gamma.toSMTType ∧
          Phi.snd.fst = SMTType.bool ∧
          (Phi.fst = zftrue ∧
            denX.fst.pair H.fst ∈ (castZF_of_path c).1) ∧
          (∀ (Y : SMT.Dom) (_ : Y.snd.fst = gamma.toSMTType)
            (hphiY : RenamingContext.CoversFV
              (Function.update Theta xhelper (some Y)) xspec),
            (⟦xspec.abstract (Function.update Theta xhelper (some Y))
              hphiY⟧ˢ).isSome = true ∧
            ∀ {PhiY : SMT.Dom},
              ⟦xspec.abstract (Function.update Theta xhelper (some Y))
                hphiY⟧ˢ = some PhiY →
              PhiY.fst = zftrue →
              denX.fst.pair Y.fst ∈ (castZF_of_path c).1))
    (ghelper_fresh : ghelper ∉ Lambda1)
    (u_fresh : u ∉ Lambda1) (v_fresh : v ∉ Lambda1)
    (ghelper_ne_u : ghelper ≠ u) (ghelper_ne_v : ghelper ≠ v)
    (u_ne_v : u ≠ v)
    (hgspec : gspec = SMT.Term.forall [u, v]
      [gamma.toSMTType, alpha.toSMTType]
      (relationOptionTermBody f ghelper u v))
    {Theta : SMT.RenamingContext.Context.{u}}
    (hcov_f : RenamingContext.CoversFV Theta f)
    (hcov_x : RenamingContext.CoversFV Theta x)
    (respects_f : SMT.RenamingContext.RespectsTypeContextOnFV
      Theta GammaSup f)
    (respects_x : SMT.RenamingContext.RespectsTypeContextOnFV
      Theta GammaSup x)
    {F X T R X0 : ZFSet.{u}}
    {hF : F ∈ ⟦BType.set (gamma ×ᴮ alpha)⟧ᶻ}
    {hX : X ∈ ⟦gamma⟧ᶻ} {hT : T ∈ ⟦alpha⟧ᶻ}
    {hR : R ∈ ⟦SMTType.fun
      (SMTType.pair gamma.toSMTType alpha.toSMTType) SMTType.bool⟧ᶻ}
    {hX0 : X0 ∈ ⟦sx⟧ᶻ}
    (hden_f : ⟦f.abstract Theta hcov_f⟧ˢ =
      some (⟨R, SMTType.fun
        (SMTType.pair gamma.toSMTType alpha.toSMTType)
        SMTType.bool, hR⟩ : SMT.Dom))
    (hden_x : ⟦x.abstract Theta hcov_x⟧ˢ =
      some (⟨X0, sx, hX0⟩ : SMT.Dom))
    (Frel : RDomCastSupported
      (⟨F, BType.set (gamma ×ᴮ alpha), hF⟩ : B.Dom)
      (⟨R, SMTType.fun
        (SMTType.pair gamma.toSMTType alpha.toSMTType)
        SMTType.bool, hR⟩ : SMT.Dom))
    (Xrel : RDomCastSupported (⟨X, gamma, hX⟩ : B.Dom)
      (⟨X0, sx, hX0⟩ : SMT.Dom))
    (hmem : X.pair T ∈ F)
    (hcov_out : RenamingContext.CoversFV Theta
      (SMT.Term.the (SMT.Term.app (.var ghelper) (.var xhelper))))
    (denOut : SMT.Dom.{u})
    (respects_out : SMT.RenamingContext.RespectsTypeContextOnFV
      Theta GammaSup
      (SMT.Term.the (SMT.Term.app (.var ghelper) (.var xhelper))))
    (specs_true : SpecBodiesTrue Theta GammaSup
      (helperSpecChunk xhelper gamma.toSMTType xspec ++
        helperSpecChunk ghelper
          (SMTType.fun gamma.toSMTType (SMTType.option alpha.toSMTType))
          gspec))
    (hden_out :
      ⟦(SMT.Term.the (SMT.Term.app (.var ghelper) (.var xhelper))).abstract
        Theta hcov_out⟧ˢ = some denOut)
    (denOutTy : denOut.snd.fst = alpha.toSMTType) :
    RDomCastSupported (⟨T, alpha, hT⟩ : B.Dom) denOut := by
  have scope_x := ScopedContextExtends.left_of_append scope
  have scope_g := ScopedContextExtends.right_of_generated x_ctx_gen scope
  have respects_x_base :
      SMT.RenamingContext.RespectsTypeContextOnFV Theta Lambda x :=
    respects_x.of_super scope.base
  let pf : ∀ (w : SMT.𝒱) (H : SMT.Dom),
      ∀ z ∈ SMT.fv (SMT.Term.var w),
        (Function.update Theta w (some H) z).isSome = true := by
    intro w H z hz
    simp only [SMT.fv, List.mem_singleton] at hz
    subst z
    simp
  obtain ⟨_PhiW, _HW, _hdenVarW, _hcovSpecW, _hdenSpecW,
      _HWty, _PhiWty, _castW, guard⟩ :=
    exactness Theta hcov_x respects_x_base pf
      (⟨X0, sx, hX0⟩ : SMT.Dom) hden_x
  have xhelper_some : (Theta xhelper).isSome = true := by
    apply hcov_out xhelper
    simp only [SMT.fv, List.mem_append, List.mem_singleton]
    exact Or.inr trivial
  obtain ⟨H, hH⟩ := Option.isSome_iff_exists.mp xhelper_some
  have xhelper_lookup : GammaSup.lookup xhelper = some gamma.toSMTType :=
    scope_x.lookup_of_declared (by simp [declEntries_helperSpecChunk])
  have xhelper_fv_out : xhelper ∈ SMT.fv
      (SMT.Term.the (SMT.Term.app (.var ghelper) (.var xhelper))) := by
    simp only [SMT.fv, List.mem_append, List.mem_singleton]
    exact Or.inr trivial
  have Hty : H.snd.fst = gamma.toSMTType := by
    obtain ⟨d, hd, hdty⟩ :=
      respects_out xhelper_fv_out xhelper_lookup
    rw [hH] at hd
    injection hd with hdeq
    subst d
    exact hdty
  have hupdate : Function.update Theta xhelper (some H) = Theta := by
    rw [← hH]
    exact Function.update_eq_self xhelper Theta
  have specs_x := SpecBodiesTrue.left_of_append specs_true
  have hspec_true := specs_x xspec (by simp)
  obtain ⟨hcov_xspec, denSpec, _respects_xspec, hden_xspec,
      _denSpecTy, denSpecTrue⟩ := hspec_true
  have hcov_xspec_update : RenamingContext.CoversFV
      (Function.update Theta xhelper (some H)) xspec := by
    rw [hupdate]
    exact hcov_xspec
  obtain ⟨_some, castPair⟩ := guard H Hty hcov_xspec_update
  have hden_xspec_update :
      ⟦xspec.abstract (Function.update Theta xhelper (some H))
        hcov_xspec_update⟧ˢ = some denSpec := by
    simpa only [hupdate, proof_irrel_heq] using hden_xspec
  have castPair' := castPair hden_xspec_update denSpecTrue
  have Hmem : H.fst ∈ ⟦gamma.toSMTType⟧ᶻ := by
    rw [← Hty]
    exact H.snd.snd
  have XrelH : RDomCastSupported (⟨X, gamma, hX⟩ : B.Dom)
      (⟨H.fst, gamma.toSMTType, Hmem⟩ : SMT.Dom) :=
    RDomCastSupported.of_cast_to_canonical Xrel c castPair'
  have hcov_xvar : RenamingContext.CoversFV Theta (.var xhelper) := by
    intro w hw
    simp only [SMT.fv, List.mem_singleton] at hw
    subst w
    exact xhelper_some
  have hden_xvar :
      ⟦(SMT.Term.var xhelper).abstract Theta hcov_xvar⟧ˢ =
        some (⟨H.fst, gamma.toSMTType, Hmem⟩ : SMT.Dom) := by
    rw [SMT.Term.abstract.eq_def]
    simp only [SMT.denote]
    have hget := Option.get_of_eq_some xhelper_some hH
    rw [hget]
    rcases H with ⟨Hv, Hsigma, hHv⟩
    dsimp at Hty
    subst Hsigma
    rfl
  have respects_xvar :
      SMT.RenamingContext.RespectsTypeContextOnFV Theta GammaSup
        (.var xhelper) := by
    intro w sigma hw hlookup
    simp only [SMT.fv, List.mem_singleton] at hw
    subst w
    rw [xhelper_lookup] at hlookup
    cases hlookup
    exact ⟨H, hH, Hty⟩
  have specs_g := SpecBodiesTrue.right_of_append specs_true
  exact castApp_relation_term_guarded_semantics scope_g typ_f1 typ_xhelper
    ghelper_fresh u_fresh v_fresh ghelper_ne_u ghelper_ne_v u_ne_v
    hgspec hcov_f hcov_xvar respects_f respects_xvar hden_f hden_xvar
    Frel XrelH hmem hcov_out denOut respects_out specs_g hden_out denOutTy

set_option maxHeartbeats 8000000 in
theorem castApp_relation_arg_scoped_contract.{u}
    (gamma alpha : BType) (f x : SMT.Term) (sx : SMTType)
    (hnotle : ¬ gamma.toSMTType ⊑ sx)
    (hle : sx ⊑ gamma.toSMTType)
    (hfaith : castPath.FVFaithful hle.toCastPath) :
    CastAppRepScopedSpec.{u} gamma alpha f x
      (SMTType.fun
        (SMTType.pair gamma.toSMTType alpha.toSMTType) SMTType.bool) sx := by
  unfold CastAppRepScopedSpec
  intro Lambda n used decl typ_f typ_x bv_f_used bv_x_used
  mstart
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_keys, St_used_eq, St_decl_eq⟩ := pre
  simp only [castApp]
  rw [dif_neg hnotle, dif_pos hle]
  mspec (Std.Do.Triple.and _
    (Std.Do.Triple.and _
      (Std.Do.Triple.and _
        (Std.Do.Triple.and _
          (loosenAux_prf_exact_univ
            (Λ := St.types) (n := St.env.freshvarsc)
            (used := St.env.usedVars) typ_x
            (fun w hw => St_used_eq ▸ bv_x_used w hw) hle.toCastPath)
          (loosenAux_prf_fv_of_faithful hfaith
            (used := St.env.usedVars) (n := St.env.freshvarsc)
            (x := x) (by
              intro w hw
              exact St_keys (SMT.Typing.mem_context_of_mem_fv typ_x hw))))
        (loosenAux_prf_decls hle.toCastPath (decl := decl)))
      (loosenAux_prf_types_eq hle.toCastPath))
    (loosenAux_prf_bv hle.toCastPath
      (used := St.env.usedVars) (n := St.env.freshvarsc)
      (x := x) (fun w hw => St_used_eq ▸ bv_x_used w hw)))
  next out =>
  obtain ⟨xhelper, xspec⟩ := out
  mrename_i pre
  mintro ∀St1
  mpure pre
  obtain ⟨⟨⟨⟨⟨_hn1, St1_types_sub, xhelper_fresh,
      xhelper_not_used, used_sub1, keys_sub1, preserves1,
      _typ_helper_insert, _typ_spec_insert, typ_xhelper, typ_xspec,
      xspec_fv, exactness⟩, _helper_not_used_fv, _source_fv_spec,
      _used_sub_fv⟩, St1_decl_eq⟩, ⟨St1_types_exact, _⟩⟩,
      ⟨_xhelper_bv_used, xspec_bv_used, _used_sub_bv⟩⟩ := pre
  mspec SMT.declareConst_addSpec_spec (x! := xhelper)
    (x!_spec := xspec) (τ := gamma.toSMTType)
    (decl := St1.env.declarations) (as := St1.env.asserts)
    (n := St1.env.freshvarsc) (Γ := St1.types)
    (used := St1.env.usedVars)
  mrename_i pre
  mintro ∀St2
  mpure pre
  obtain ⟨St2_decl_eq, _, St2_fvc, St2_used, St2_types⟩ := pre
  mspec (Std.Do.Triple.and _ SMT.freshVar_spec
    (SMT.freshVar_decls (decl := St2.env.declarations)))
  next ghelper =>
  mrename_i pre
  mintro ∀St3
  mpure pre
  obtain ⟨⟨St3_types, ghelper_fresh, St3_fvc, St3_used,
      ghelper_not_used⟩, St3_decl⟩ := pre
  mspec SMT.declareConst_spec (v := ghelper)
    (τ := SMTType.fun gamma.toSMTType
      (SMTType.option alpha.toSMTType))
  mrename_i pre
  mintro ∀St4
  mpure pre
  obtain ⟨St4_decl, _, St4_fvc, St4_used, St4_types⟩ := pre
  mspec (Std.Do.Triple.and _ SMT.freshVar_spec
    (SMT.freshVar_decls (decl := St4.env.declarations)))
  next u =>
  mrename_i pre
  mintro ∀St5
  mpure pre
  obtain ⟨⟨St5_types, u_fresh, St5_fvc, St5_used, u_not_used⟩,
    St5_decl⟩ := pre
  mspec (Std.Do.Triple.and _ SMT.freshVar_spec
    (SMT.freshVar_decls (decl := St5.env.declarations)))
  next v =>
  mrename_i pre
  mintro ∀St6
  mpure pre
  obtain ⟨⟨St6_types, v_fresh, St6_fvc, St6_used, v_not_used⟩,
    St6_decl⟩ := pre
  let gspec : SMT.Term := SMT.Term.forall [u, v]
    [gamma.toSMTType, alpha.toSMTType]
    (relationOptionTermBody f ghelper u v)
  mspec (Std.Do.Triple.and _ SMT.eraseFromContext_spec
    (SMT.eraseFromContext_used_decls
      (used := St6.env.usedVars) (decl := St6.env.declarations)))
  mrename_i pre
  mintro ∀St7
  mpure pre
  obtain ⟨⟨St7_types, St7_fvc, St7_used⟩,
    St7_used', St7_decl⟩ := pre
  mspec (Std.Do.Triple.and _ SMT.eraseFromContext_spec
    (SMT.eraseFromContext_used_decls
      (used := St7.env.usedVars) (decl := St7.env.declarations)))
  mrename_i pre
  mintro ∀St8
  mpure pre
  obtain ⟨⟨St8_types, St8_fvc, St8_used⟩,
    St8_used', St8_decl⟩ := pre
  mspec SMT.addSpec_spec (x! := ghelper) (x!_spec := gspec)
  mrename_i pre
  mintro ∀St9
  mpure pre
  obtain ⟨St9_decl, _, St9_fvc, St9_used, St9_types⟩ := pre
  mspec Std.Do.Spec.pure
  have Lambda_sub1 : St.types ⊆ St1.types := fun w hw =>
    St1_types_sub
      (SMT.TypeContext.entries_subset_insert_of_notMem xhelper_fresh hw)
  have typ_f1 : St1.types ⊢ˢ f : SMTType.fun
      (SMTType.pair gamma.toSMTType alpha.toSMTType) SMTType.bool :=
    SMT.Typing.weakening Lambda_sub1 typ_f
      (fun w hw => preserves1 w (St_used_eq ▸ bv_f_used w hw)
        (SMT.Typing.bv_notMem_context typ_f w hw))
  have ghelper_fresh_St1 : ghelper ∉ St1.types := by
    rw [← St2_types]
    exact ghelper_fresh
  have St1_sub3 : St1.types ⊆ St3.types := by
    rw [St3_types, St2_types]
    exact SMT.TypeContext.entries_subset_insert_of_notMem ghelper_fresh_St1
  have typ_f3 : St3.types ⊢ˢ f : SMTType.fun
      (SMTType.pair gamma.toSMTType alpha.toSMTType) SMTType.bool :=
    SMT.Typing.weakening St1_sub3 typ_f1 (by
      intro w hw
      have hw_used1 : w ∈ St1.env.usedVars :=
        used_sub1 (St_used_eq ▸ bv_f_used w hw)
      have hw_ne_g : w ≠ ghelper := fun h => by
        subst w
        exact ghelper_not_used (St2_used ▸ hw_used1)
      intro hw3
      rw [St3_types, St2_types, AList.mem_insert] at hw3
      exact hw3.elim (fun h => hw_ne_g h)
        (SMT.Typing.bv_notMem_context typ_f1 w hw))
  have typ_xhelper3 : St3.types ⊢ˢ (.var xhelper) :
      gamma.toSMTType :=
    SMT.Typing.weakening St1_sub3 typ_xhelper (by simp [SMT.bv])
  have typ_xspec3 : St3.types ⊢ˢ xspec : SMTType.bool :=
    SMT.Typing.weakening St1_sub3 typ_xspec (by
      intro w hw hmem
      rw [St3_types, St2_types, AList.mem_insert] at hmem
      rcases hmem with h | hmem
      · subst w
        exact ghelper_not_used (St2_used ▸ xspec_bv_used ghelper hw)
      · exact SMT.Typing.bv_notMem_context typ_xspec w hw hmem)
  have u_ne_v : u ≠ v := by
    intro h
    apply v_fresh
    rw [St5_types, AList.mem_insert]
    exact Or.inl h.symm
  have v_fresh_St3 : v ∉ St3.types := by
    intro hv
    apply v_fresh
    rw [St5_types, St4_types]
    exact AList.mem_insert _ |>.mpr (Or.inr hv)
  have u_fresh_St3 : u ∉ St3.types := by
    rw [← St4_types]
    exact u_fresh
  have ghelper_ne_u : ghelper ≠ u := by
    intro h
    subst u
    exact u_fresh_St3 (by
      rw [St3_types]
      exact AList.mem_insert _ |>.mpr (Or.inl rfl))
  have ghelper_ne_v : ghelper ≠ v := by
    intro h
    subst v
    exact v_fresh_St3 (by
      rw [St3_types]
      exact AList.mem_insert _ |>.mpr (Or.inl rfl))
  have St8_types_base : St8.types = St3.types := by
    rw [St8_types, St7_types, St6_types, St5_types, St4_types,
      encodeTerm_state.erase_insert_ne u_ne_v,
      encodeTerm_state.erase_insert_self u_fresh_St3,
      encodeTerm_state.erase_insert_self v_fresh_St3]
  have ghelper_lookup3 : St3.types.lookup ghelper = some
      (SMTType.fun gamma.toSMTType
        (SMTType.option alpha.toSMTType)) := by
    rw [St3_types, St2_types, AList.lookup_insert]
  have typOut : St3.types ⊢ˢ
      (SMT.Term.the (SMT.Term.app (.var ghelper) (.var xhelper))) :
        alpha.toSMTType := by
    apply SMT.Typing.the
    apply SMT.Typing.app
    · apply SMT.Typing.var
      exact ghelper_lookup3
    · exact typ_xhelper3
  have gspec_eq : gspec = SMT.Term.forall [u, v]
      [gamma.toSMTType, alpha.toSMTType]
      (relationOptionTermBody f ghelper u v) := rfl
  have u_not_used_St1 : u ∉ St1.env.usedVars := by
    intro hu
    apply u_not_used
    rw [St4_used, St3_used, St2_used]
    exact List.mem_cons_of_mem _ hu
  have v_not_used_St1 : v ∉ St1.env.usedVars := by
    intro hv
    apply v_not_used
    rw [St5_used, St4_used, St3_used, St2_used]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hv)
  have uv_not_bv_f : ∀ w ∈ [u, v], w ∉ SMT.bv f := by
    intro w hw hbf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact u_not_used_St1 (used_sub1 (St_used_eq ▸ bv_f_used _ hbf))
    · exact v_not_used_St1 (used_sub1 (St_used_eq ▸ bv_f_used _ hbf))
  have typ_gspec : St3.types ⊢ˢ gspec : SMTType.bool := by
    rw [gspec_eq]
    refine SMT.Typing.forall St3.types [u, v]
      [gamma.toSMTType, alpha.toSMTType]
      (relationOptionTermBody f ghelper u v) ?_ ?_ (by simp) rfl ?_
    · intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      exact hw.elim (fun h => h ▸ u_fresh_St3)
        (fun h => h ▸ v_fresh_St3)
    · intro w hw hb
      exact uv_not_bv_f w hw (by
        simpa only [relationOptionTermBody, SMT.bv, List.mem_append,
          List.not_mem_nil, or_false, false_or] using hb)
    · have hupdate : SMT.TypeContext.update St3.types [u, v]
          [gamma.toSMTType, alpha.toSMTType] rfl =
          (St3.types.insert u gamma.toSMTType).insert v alpha.toSMTType := by
        simp only [SMT.TypeContext.update, List.length_cons, List.length_nil,
          Nat.reduceAdd, Fin.foldl_succ_last, Fin.getElem_fin, Fin.coe_cast,
          Fin.val_last, List.getElem_append_right, Nat.reduceSubDiff,
          List.getElem_cons_succ, List.getElem_cons_zero, Fin.coe_castSucc,
          Fin.foldl_zero]
      rw [hupdate]
      apply SMT.Typing.eq
      · apply SMT.Typing.app
        · exact SMT.Typing.weakening
            (List.Subset.trans
              (SMT.TypeContext.entries_subset_insert_of_notMem u_fresh_St3)
              (SMT.TypeContext.entries_subset_insert_of_notMem (by
                intro hv
                rw [AList.mem_insert] at hv
                exact hv.elim (fun h => u_ne_v h.symm)
                  (fun h => v_fresh_St3 h)))) typ_f3 (by
              intro w hw
              intro hmem
              rw [AList.mem_insert] at hmem
              rcases hmem with rfl | hmem
              · exact uv_not_bv_f _ (by simp) hw
              · rw [AList.mem_insert] at hmem
                exact hmem.elim (fun h => uv_not_bv_f u (by simp) (h ▸ hw))
                  (SMT.Typing.bv_notMem_context typ_f3 w hw))
        · apply SMT.Typing.pair
          · apply SMT.Typing.var
            rw [AList.lookup_insert_ne u_ne_v, AList.lookup_insert]
          · apply SMT.Typing.var
            rw [AList.lookup_insert]
      · apply SMT.Typing.eq
        · apply SMT.Typing.app
          · apply SMT.Typing.var
            rw [AList.lookup_insert_ne ghelper_ne_v,
              AList.lookup_insert_ne ghelper_ne_u, ghelper_lookup3]
          · apply SMT.Typing.var
            rw [AList.lookup_insert_ne u_ne_v, AList.lookup_insert]
        · apply SMT.Typing.some
          apply SMT.Typing.var
          rw [AList.lookup_insert]
  have x_ctx_gen : ContextGeneratedByDeclarations St.types St1.types
      (helperSpecChunk xhelper gamma.toSMTType xspec) := by
    rw [St1_types_exact]
    exact ContextGeneratedByDeclarations.insert_helper
      St.types xhelper gamma.toSMTType xspec xhelper_fresh
  have x_ctx_trace : DeclarationContextTrace St.types
      (helperSpecChunk xhelper gamma.toSMTType xspec) St1.types := by
    rw [St1_types_exact]
    exact DeclarationContextTrace.helperSpecChunk
      St.types xhelper gamma.toSMTType xspec xhelper_fresh
  have g_ctx_gen : ContextGeneratedByDeclarations St1.types St3.types
      (helperSpecChunk ghelper
        (SMTType.fun gamma.toSMTType (SMTType.option alpha.toSMTType))
        gspec) := by
    rw [St3_types, St2_types]
    exact ContextGeneratedByDeclarations.insert_helper St1.types ghelper _
      gspec ghelper_fresh_St1
  have g_ctx_trace : DeclarationContextTrace St1.types
      (helperSpecChunk ghelper
        (SMTType.fun gamma.toSMTType (SMTType.option alpha.toSMTType))
        gspec) St3.types := by
    rw [St3_types, St2_types]
    exact DeclarationContextTrace.helperSpecChunk St1.types ghelper _
      gspec ghelper_fresh_St1
  have all_ctx_gen := ContextGeneratedByDeclarations.append x_ctx_gen g_ctx_gen
  have all_ctx_trace := DeclarationContextTrace.append x_ctx_trace g_ctx_trace
  have used_sub_out : used ⊆ St9.env.usedVars := by
    intro w hw
    rw [St9_used, St8_used, St7_used, St6_used, St5_used,
      St4_used, St3_used, St2_used]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (used_sub1 (St_used_eq ▸ hw))))
  have keys_sub3 : St3.types.keys ⊆ St9.env.usedVars := by
    intro w hw
    rw [St9_used, St8_used, St7_used, St6_used, St5_used,
      St4_used, St3_used, St2_used]
    rw [St3_types, St2_types] at hw
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (keys_insert_subset_cons keys_sub1 hw))
  have preserves_out : ∀ w ∈ used, w ∉ St.types → w ∉ St3.types := by
    intro w hw hnot hmem
    rw [St3_types, St2_types, AList.mem_insert] at hmem
    rcases hmem with rfl | hmem
    · exact ghelper_not_used
        (St2_used ▸ used_sub1 (St_used_eq ▸ hw))
    · exact preserves1 w (St_used_eq ▸ hw) hnot hmem
  have xhelper_not_used_out : xhelper ∉ used := by
    simpa [St_used_eq] using xhelper_not_used
  have ghelper_not_used_out : ghelper ∉ used := by
    intro hw
    exact ghelper_not_used (St2_used ▸ used_sub1 (St_used_eq ▸ hw))
  have ghelper_not_used_St1 : ghelper ∉ St1.env.usedVars := by
    simpa [St2_used] using ghelper_not_used
  have u_fresh_St1 : u ∉ St1.types := fun hu =>
    u_fresh_St3 (AList.mem_of_subset St1_sub3 hu)
  have v_fresh_St1 : v ∉ St1.types := fun hv =>
    v_fresh_St3 (AList.mem_of_subset St1_sub3 hv)
  mpure_intro
  rw [St9_types, St8_types_base]
  let Dlt := helperSpecChunk xhelper gamma.toSMTType xspec ++
    helperSpecChunk ghelper
      (SMTType.fun gamma.toSMTType (SMTType.option alpha.toSMTType))
      gspec
  refine ⟨used_sub_out, AList.subset_trans Lambda_sub1 St1_sub3,
    keys_sub3, True.intro, typOut, preserves_out, Dlt, ?_,
    all_ctx_gen, all_ctx_trace, ?_, ?_, ?_, ?_⟩
  · rw [St9_decl, St8_decl, St7_decl, St6_decl, St5_decl,
      St4_decl, St3_decl, St2_decl_eq, St1_decl_eq]
    simp [Dlt, helperSpecChunk, List.concat_eq_append,
      List.append_assoc]
  · intro w hw
    simp only [Dlt, declVars_append, declVars_helperSpecChunk,
      List.mem_append, List.mem_singleton] at hw
    exact hw.elim (fun h => h ▸ xhelper_not_used_out)
      (fun h => h ▸ ghelper_not_used_out)
  · intro GammaSup GammaSub Theta hcov_f hcov_x Theta_none
      respects_f respects_x Theta_dom F X T hF hX hT hfun hdom
      hresult denF denX hden_f hden_x hdenFty hdenXty Frel Xrel
    have Lambda1_sub_sup : St1.types ⊆ GammaSup :=
      AList.subset_trans St1_sub3 GammaSub
    have Lambda_sub_sup : St.types ⊆ GammaSup :=
      AList.subset_trans Lambda_sub1 Lambda1_sub_sup
    have respects_f_base := respects_f.of_super Lambda_sub_sup
    have respects_x_base := respects_x.of_super Lambda_sub_sup
    have xhelper_lookup : St1.types.lookup xhelper = some gamma.toSMTType :=
      SMT.Typing.varE typ_xhelper
    have ghelper_lookup_sup : GammaSup.lookup ghelper = some
        (SMTType.fun gamma.toSMTType
          (SMTType.option alpha.toSMTType)) :=
      AList.lookup_of_subset GammaSub ghelper_lookup3
    have xhelper_usedMid : xhelper ∈ St1.env.usedVars :=
      keys_sub1 (AList.lookup_isSome.mp
        (Option.isSome_of_eq_some xhelper_lookup))
    have ghelper_used1 : ghelper ∈ St9.env.usedVars := by
      rw [St9_used, St8_used, St7_used, St6_used, St5_used,
        St4_used, St3_used]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    have u_not_usedMid : u ∉ St1.env.usedVars := u_not_used_St1
    have v_not_usedMid : v ∉ St1.env.usedVars := v_not_used_St1
    have used_mid_sub : St1.env.usedVars ⊆ St9.env.usedVars := by
      intro w hw
      rw [St9_used, St8_used, St7_used, St6_used, St5_used,
        St4_used, St3_used, St2_used]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ hw))
    rcases denF with ⟨R, sigmaF, hR⟩
    rcases denX with ⟨X0, sigmaX, hX0⟩
    dsimp at hdenFty hdenXty
    subst sigmaF
    subst sigmaX
    have hmem : X.pair T ∈ F := by
      rw [← hresult]
      exact ZFSet.fapply.def hfun hdom
    constructor
    · exact castApp_relation_arg_semantics typ_f typ_x typ_f1
        typ_xhelper Lambda_sub1 Lambda1_sub_sup xhelper_fresh
        xhelper_lookup xhelper_not_used_out xhelper_usedMid
        (by simpa [St_used_eq] using used_sub1) xspec_fv hle.toCastPath
        exactness ghelper_fresh_St1 ghelper_lookup_sup
        ghelper_not_used_St1 ghelper_used1 u_not_usedMid v_not_usedMid
        used_mid_sub
        ghelper_ne_u ghelper_ne_v u_ne_v gspec_eq hcov_f hcov_x
        Theta_none respects_f_base respects_x_base Theta_dom hden_f
        hden_x Frel Xrel hfun hmem
    · intro GammaSupG scopeG ThetaG hcov_fG hcov_xG
        respects_fG respects_xG FG XG TG hFG hXG hTG hfunG hdomG
        hresultG denFG denXG hden_fG hden_xG hdenFGty hdenXGty
        FrelG XrelG hcov_outG denOutG respects_outG specs_trueG
        hden_outG denOutGTy
      rcases denFG with ⟨RG, sigmaFG, hRG⟩
      rcases denXG with ⟨X0G, sigmaXG, hX0G⟩
      dsimp at hdenFGty hdenXGty
      subst sigmaFG
      subst sigmaXG
      have hmemG : XG.pair TG ∈ FG := by
        rw [← hresultG]
        exact ZFSet.fapply.def hfunG hdomG
      exact castApp_relation_arg_guarded_semantics x_ctx_gen scopeG typ_x
        typ_f1 typ_xhelper hle.toCastPath exactness ghelper_fresh_St1
        u_fresh_St1 v_fresh_St1 ghelper_ne_u ghelper_ne_v u_ne_v
        gspec_eq hcov_fG hcov_xG respects_fG respects_xG hden_fG
        hden_xG FrelG XrelG hmemG hcov_outG denOutG respects_outG
        specs_trueG hden_outG denOutGTy
  · intro body hbody
    simp only [Dlt, specBodies_append, specBodies_helperSpecChunk,
      List.mem_append, List.mem_singleton] at hbody
    exact hbody.elim (fun h => h ▸ typ_xspec3)
      (fun h => h ▸ typ_gspec)
  · exact ScopedGeneratedTyping.of_operational all_ctx_gen typOut (by
      intro body hbody
      simp only [Dlt, specBodies_append, specBodies_helperSpecChunk,
        List.mem_append, List.mem_singleton] at hbody
      exact hbody.elim (fun h => h ▸ typ_xspec3)
        (fun h => h ▸ typ_gspec))

private theorem castApp_relation_fun_semantics.{u}
    {gamma alpha : BType} {f x rspec gspec : SMT.Term}
    {Lambda Lambda1 Gamma : SMT.TypeContext}
    {rhelper ghelper u v : SMT.𝒱}
    {used0 usedMid used1 : List SMT.𝒱}
    (typ_f : Lambda ⊢ˢ f : SMTType.fun
      (SMTType.pair gamma.toSMTType alpha.toSMTType) SMTType.bool)
    (typ_x : Lambda ⊢ˢ x : gamma.toSMTType)
    (typ_rhelper : Lambda1 ⊢ˢ (.var rhelper) : SMTType.fun
      (SMTType.pair gamma.toSMTType alpha.toSMTType) SMTType.bool)
    (typ_x1 : Lambda1 ⊢ˢ x : gamma.toSMTType)
    (Lambda_sub1 : Lambda ⊆ Lambda1) (Lambda1_sub : Lambda1 ⊆ Gamma)
    (rhelper_fresh : rhelper ∉ Lambda)
    (rhelper_lookup : Lambda1.lookup rhelper = some
      (SMTType.fun
        (SMTType.pair gamma.toSMTType alpha.toSMTType) SMTType.bool))
    (rhelper_not_used0 : rhelper ∉ used0)
    (rhelper_usedMid : rhelper ∈ usedMid)
    (used_sub_mid : used0 ⊆ usedMid)
    (rspec_fv : SMT.fv rspec ⊆ SMT.fv f ∪ {rhelper})
    (c : SMTType.fun
      (SMTType.pair gamma.toSMTType alpha.toSMTType) SMTType.bool ~>
      SMTType.fun
        (SMTType.pair gamma.toSMTType alpha.toSMTType) SMTType.bool)
    (exactness :
      ∀ (Theta : SMT.RenamingContext.Context.{u})
        (hf : RenamingContext.CoversFV Theta f)
        (_respects : SMT.RenamingContext.RespectsTypeContextOnFV
          Theta Lambda f)
        (pf : ∀ (x_ : SMT.𝒱) (X_ : SMT.Dom),
          ∀ w ∈ SMT.fv (SMT.Term.var x_),
            (Function.update Theta x_ (some X_) w).isSome = true),
      ∀ (denF : SMT.Dom), ⟦f.abstract Theta hf⟧ˢ = some denF →
        ∃ (Phi H : SMT.Dom)
          (_ : ⟦(SMT.Term.var rhelper).abstract
            (Function.update Theta rhelper (some H)) (pf rhelper H)⟧ˢ =
              some H)
          (hphi : RenamingContext.CoversFV
            (Function.update Theta rhelper (some H)) rspec)
          (_ : ⟦rspec.abstract (Function.update Theta rhelper (some H))
            hphi⟧ˢ = some Phi),
          H.snd.fst = SMTType.fun
            (SMTType.pair gamma.toSMTType alpha.toSMTType) SMTType.bool ∧
          Phi.snd.fst = SMTType.bool ∧
          (Phi.fst = zftrue ∧
            denF.fst.pair H.fst ∈ (castZF_of_path c).1) ∧
          (∀ (Y : SMT.Dom)
            (_ : Y.snd.fst = SMTType.fun
              (SMTType.pair gamma.toSMTType alpha.toSMTType) SMTType.bool)
            (hphiY : RenamingContext.CoversFV
              (Function.update Theta rhelper (some Y)) rspec),
            (⟦rspec.abstract (Function.update Theta rhelper (some Y))
              hphiY⟧ˢ).isSome = true ∧
            ∀ {PhiY : SMT.Dom},
              ⟦rspec.abstract (Function.update Theta rhelper (some Y))
                hphiY⟧ˢ = some PhiY →
              PhiY.fst = zftrue →
              denF.fst.pair Y.fst ∈ (castZF_of_path c).1))
    (ghelper_fresh : ghelper ∉ Lambda1)
    (ghelper_lookup : Gamma.lookup ghelper = some
      (SMTType.fun gamma.toSMTType (SMTType.option alpha.toSMTType)))
    (ghelper_not_usedMid : ghelper ∉ usedMid)
    (ghelper_used1 : ghelper ∈ used1)
    (u_not_usedMid : u ∉ usedMid) (v_not_usedMid : v ∉ usedMid)
    (used_mid_sub : usedMid ⊆ used1)
    (ghelper_ne_u : ghelper ≠ u) (ghelper_ne_v : ghelper ≠ v)
    (u_ne_v : u ≠ v)
    (hgspec : gspec = SMT.Term.forall [u, v]
      [gamma.toSMTType, alpha.toSMTType]
      (relationOptionTermBody (.var rhelper) ghelper u v))
    {Theta : SMT.RenamingContext.Context.{u}}
    (hcov_f : RenamingContext.CoversFV Theta f)
    (hcov_x : RenamingContext.CoversFV Theta x)
    (Theta_none : ∀ w ∉ used0, Theta w = none)
    (respects_f : SMT.RenamingContext.RespectsTypeContextOnFV
      Theta Lambda f)
    (respects_x : SMT.RenamingContext.RespectsTypeContextOnFV
      Theta Lambda x)
    (Theta_dom : ∀ w, Theta w ≠ none → w ∈ Gamma)
    {F X T R Y : ZFSet.{u}}
    {hF : F ∈ ⟦BType.set (gamma ×ᴮ alpha)⟧ᶻ}
    {hX : X ∈ ⟦gamma⟧ᶻ} {hT : T ∈ ⟦alpha⟧ᶻ}
    {hR : R ∈ ⟦SMTType.fun
      (SMTType.pair gamma.toSMTType alpha.toSMTType) SMTType.bool⟧ᶻ}
    {hY : Y ∈ ⟦gamma.toSMTType⟧ᶻ}
    (hden_f : ⟦f.abstract Theta hcov_f⟧ˢ =
      some (⟨R, SMTType.fun
        (SMTType.pair gamma.toSMTType alpha.toSMTType)
        SMTType.bool, hR⟩ : SMT.Dom))
    (hden_x : ⟦x.abstract Theta hcov_x⟧ˢ =
      some (⟨Y, gamma.toSMTType, hY⟩ : SMT.Dom))
    (Frel : RDomCastSupported
      (⟨F, BType.set (gamma ×ᴮ alpha), hF⟩ : B.Dom)
      (⟨R, SMTType.fun
        (SMTType.pair gamma.toSMTType alpha.toSMTType)
        SMTType.bool, hR⟩ : SMT.Dom))
    (Xrel : RDomCastSupported (⟨X, gamma, hX⟩ : B.Dom)
      (⟨Y, gamma.toSMTType, hY⟩ : SMT.Dom))
    (hfun : F.IsPFunc ⟦gamma⟧ᶻ ⟦alpha⟧ᶻ)
    (hmem : X.pair T ∈ F) :
    ∃ (Theta' : SMT.RenamingContext.Context.{u})
      (hcov_out : RenamingContext.CoversFV Theta'
        (SMT.Term.the (SMT.Term.app (.var ghelper) x)))
      (denOut : SMT.Dom.{u}),
      RenamingContext.Extends Theta' Theta ∧
      (∀ w ∉ used1, Theta' w = none) ∧
      SMT.RenamingContext.RespectsTypeContextOnFV Theta' Gamma
        (SMT.Term.the (SMT.Term.app (.var ghelper) x)) ∧
      (∀ w, Theta' w ≠ none → w ∈ Gamma) ∧
      SpecBodiesTrue Theta' Gamma
        (helperSpecChunk rhelper
          (SMTType.fun
            (SMTType.pair gamma.toSMTType alpha.toSMTType) SMTType.bool)
          rspec ++
          helperSpecChunk ghelper
            (SMTType.fun gamma.toSMTType (SMTType.option alpha.toSMTType))
            gspec) ∧
      ⟦(SMT.Term.the (SMT.Term.app (.var ghelper) x)).abstract
        Theta' hcov_out⟧ˢ = some denOut ∧
      denOut.snd.fst = alpha.toSMTType ∧
      RDomCastSupported (⟨T, alpha, hT⟩ : B.Dom) denOut := by
  have rhelper_none : Theta rhelper = none :=
    Theta_none rhelper rhelper_not_used0
  let pf : ∀ (w : SMT.𝒱) (H : SMT.Dom),
      ∀ z ∈ SMT.fv (SMT.Term.var w),
        (Function.update Theta w (some H) z).isSome = true := by
    intro w H z hz
    simp only [SMT.fv, List.mem_singleton] at hz
    subst z
    simp
  obtain ⟨Phi, H, hden_var, hcov_rspec, hden_rspec, Hty, Phity,
      ⟨PhiTrue, castPair⟩, _guard⟩ :=
    exactness Theta hcov_f respects_f pf
      (⟨R, SMTType.fun
        (SMTType.pair gamma.toSMTType alpha.toSMTType)
        SMTType.bool, hR⟩ : SMT.Dom) hden_f
  let Theta1 := Function.update Theta rhelper (some H)
  have Theta1_ext : RenamingContext.Extends Theta1 Theta :=
    RenamingContext.extends_update_of_none rhelper_none
  have rhelper_not_fv_x : rhelper ∉ SMT.fv x :=
    fun hw => rhelper_fresh (SMT.Typing.mem_context_of_mem_fv typ_x hw)
  have hcov_x1 : RenamingContext.CoversFV Theta1 x :=
    RenamingContext.coversFV_of_extends_of_coversFV Theta1_ext hcov_x
  have hden_x1 : ⟦x.abstract Theta1 hcov_x1⟧ˢ =
      some (⟨Y, gamma.toSMTType, hY⟩ : SMT.Dom) := by
    have hagree := RenamingContext.agreesOnFV_of_extends_of_coversFV
      Theta1_ext hcov_x
    exact (RenamingContext.denote_congr_of_agreesOnFV
      (t := x) (h1 := hcov_x1) (h2 := hcov_x) hagree).trans hden_x
  have hcov_rvar : RenamingContext.CoversFV Theta1 (.var rhelper) := by
    intro w hw
    simp only [SMT.fv, List.mem_singleton] at hw
    subst w
    simp [Theta1]
  have hden_rvar : ⟦(SMT.Term.var rhelper).abstract
      Theta1 hcov_rvar⟧ˢ = some H := by
    simpa only [Theta1, proof_irrel_heq] using hden_var
  have respects_x_Lambda1 :
      SMT.RenamingContext.RespectsTypeContextOnFV Theta Lambda1 x :=
    respects_x.of_extends (RenamingContext.extends_refl Theta)
      Lambda_sub1 typ_x
  have respects_x1 :
      SMT.RenamingContext.RespectsTypeContextOnFV Theta1 Lambda1 x := by
    intro w sigma hw hlookup
    have hw_ne : w ≠ rhelper := fun h => by
      subst w
      exact rhelper_not_fv_x hw
    obtain ⟨d, hd, hdty⟩ := respects_x_Lambda1 hw hlookup
    exact ⟨d, by simpa [Theta1, Function.update_of_ne hw_ne] using hd,
      hdty⟩
  have respects_rvar :
      SMT.RenamingContext.RespectsTypeContextOnFV Theta1 Lambda1
        (.var rhelper) := by
    intro w sigma hw hlookup
    simp only [SMT.fv, List.mem_singleton] at hw
    subst w
    rw [rhelper_lookup] at hlookup
    cases hlookup
    exact ⟨H, by simp [Theta1], Hty⟩
  have Hmem : H.fst ∈ ⟦SMTType.fun
      (SMTType.pair gamma.toSMTType alpha.toSMTType) SMTType.bool⟧ᶻ := by
    rw [← Hty]
    exact H.snd.snd
  have hcast : castZF_apply c R = H.fst :=
    castZF_apply_eq_of_pair c hR castPair
  have H_eq_R : H.fst = R := by
    rw [castZF_apply_self c hR] at hcast
    exact hcast.symm
  have FrelH : RDomCastSupported
      (⟨F, BType.set (gamma ×ᴮ alpha), hF⟩ : B.Dom)
      (⟨H.fst, SMTType.fun
        (SMTType.pair gamma.toSMTType alpha.toSMTType)
        SMTType.bool, Hmem⟩ : SMT.Dom) := by
    have hdomEq :
        (⟨H.fst, SMTType.fun
          (SMTType.pair gamma.toSMTType alpha.toSMTType)
          SMTType.bool, Hmem⟩ : SMT.Dom) =
        (⟨R, SMTType.fun
          (SMTType.pair gamma.toSMTType alpha.toSMTType)
          SMTType.bool, hR⟩ : SMT.Dom) := by
      cases H_eq_R
      rfl
    rw [hdomEq]
    exact Frel
  have Heq : H = (⟨H.fst, SMTType.fun
      (SMTType.pair gamma.toSMTType alpha.toSMTType)
      SMTType.bool, Hmem⟩ : SMT.Dom) := by
    rcases H with ⟨Hv, Hsigma, hHv⟩
    dsimp at Hty
    subst Hsigma
    rfl
  have hden_rhelper : ⟦(SMT.Term.var rhelper).abstract
      Theta1 hcov_rvar⟧ˢ =
      some (⟨H.fst, SMTType.fun
        (SMTType.pair gamma.toSMTType alpha.toSMTType)
        SMTType.bool, Hmem⟩ : SMT.Dom) := by
    rw [← Heq]
    exact hden_rvar
  have Theta1_none : ∀ w ∉ usedMid, Theta1 w = none := by
    intro w hw
    have hw_ne : w ≠ rhelper := fun h => by
      subst w
      exact hw rhelper_usedMid
    simpa [Theta1, Function.update_of_ne hw_ne] using
      Theta_none w (fun hw0 => hw (used_sub_mid hw0))
  have Theta1_dom : ∀ w, Theta1 w ≠ none → w ∈ Gamma := by
    intro w hw
    by_cases hwr : w = rhelper
    · subst w
      exact AList.mem_of_subset Lambda1_sub
        (AList.lookup_isSome.mp (by rw [rhelper_lookup]; rfl))
    · exact Theta_dom w (by
        simpa [Theta1, Function.update_of_ne hwr] using hw)
  obtain ⟨Theta2, hcov_out, denOut, Theta2_ext, Theta2_none,
      respects_out, Theta2_dom, specs_g, hden_out, denOutTy, resultRel⟩ :=
    castApp_relation_term_semantics typ_rhelper typ_x1 Lambda1_sub
      ghelper_fresh ghelper_lookup ghelper_not_usedMid ghelper_used1
      u_not_usedMid v_not_usedMid used_mid_sub ghelper_ne_u
      ghelper_ne_v u_ne_v hgspec hcov_rvar hcov_x1 Theta1_none
      respects_rvar respects_x1 Theta1_dom hden_rhelper hden_x1 FrelH
      Xrel hfun hmem
  have respects_f_Gamma :
      SMT.RenamingContext.RespectsTypeContextOnFV Theta Gamma f :=
    respects_f.of_extends (RenamingContext.extends_refl Theta)
      (AList.subset_trans Lambda_sub1 Lambda1_sub) typ_f
  have rhelper_lookup_Gamma : Gamma.lookup rhelper = some
      (SMTType.fun
        (SMTType.pair gamma.toSMTType alpha.toSMTType) SMTType.bool) :=
    AList.lookup_of_subset Lambda1_sub rhelper_lookup
  have respects_rspec :
      SMT.RenamingContext.RespectsTypeContextOnFV Theta1 Gamma rspec :=
    SMT.RenamingContext.respects_update_helper rspec_fv
      respects_f_Gamma rhelper_lookup_Gamma Hty
  have specs_r : SpecBodiesTrue Theta1 Gamma
      (helperSpecChunk rhelper
        (SMTType.fun
          (SMTType.pair gamma.toSMTType alpha.toSMTType) SMTType.bool)
        rspec) := by
    intro body hbody
    simp only [specBodies_helperSpecChunk, List.mem_singleton] at hbody
    subst body
    exact ⟨hcov_rspec, Phi, respects_rspec, hden_rspec,
      Phity, PhiTrue⟩
  have specs_r2 : SpecBodiesTrue Theta2 Gamma
      (helperSpecChunk rhelper
        (SMTType.fun
          (SMTType.pair gamma.toSMTType alpha.toSMTType) SMTType.bool)
        rspec) :=
    SpecBodiesTrue.of_extends specs_r Theta2_ext
      (fun _ hw => hw) Theta1_dom
  exact ⟨Theta2, hcov_out, denOut,
    RenamingContext.extends_trans Theta2_ext Theta1_ext,
    Theta2_none, respects_out, Theta2_dom,
    SpecBodiesTrue.append specs_r2 specs_g,
    hden_out, denOutTy, resultRel⟩

private theorem castApp_relation_fun_guarded_semantics.{u}
    {gamma alpha : BType} {f x rspec gspec : SMT.Term}
    {Lambda Lambda1 GammaSup : SMT.TypeContext}
    {rhelper ghelper u v : SMT.𝒱}
    (r_ctx_gen : ContextGeneratedByDeclarations Lambda Lambda1
      (helperSpecChunk rhelper
        (SMTType.fun
          (SMTType.pair gamma.toSMTType alpha.toSMTType) SMTType.bool)
        rspec))
    (scope : ScopedContextExtends Lambda
      (helperSpecChunk rhelper
        (SMTType.fun
          (SMTType.pair gamma.toSMTType alpha.toSMTType) SMTType.bool)
        rspec ++
        helperSpecChunk ghelper
          (SMTType.fun gamma.toSMTType (SMTType.option alpha.toSMTType))
          gspec) GammaSup)
    (typ_f : Lambda ⊢ˢ f : SMTType.fun
      (SMTType.pair gamma.toSMTType alpha.toSMTType) SMTType.bool)
    (typ_rhelper : Lambda1 ⊢ˢ (.var rhelper) : SMTType.fun
      (SMTType.pair gamma.toSMTType alpha.toSMTType) SMTType.bool)
    (typ_x1 : Lambda1 ⊢ˢ x : gamma.toSMTType)
    (c : SMTType.fun
      (SMTType.pair gamma.toSMTType alpha.toSMTType) SMTType.bool ~>
      SMTType.fun
        (SMTType.pair gamma.toSMTType alpha.toSMTType) SMTType.bool)
    (exactness :
      ∀ (Theta : SMT.RenamingContext.Context.{u})
        (hf : RenamingContext.CoversFV Theta f)
        (_respects : SMT.RenamingContext.RespectsTypeContextOnFV
          Theta Lambda f)
        (pf : ∀ (x_ : SMT.𝒱) (X_ : SMT.Dom),
          ∀ w ∈ SMT.fv (SMT.Term.var x_),
            (Function.update Theta x_ (some X_) w).isSome = true),
      ∀ (denF : SMT.Dom), ⟦f.abstract Theta hf⟧ˢ = some denF →
        ∃ (Phi H : SMT.Dom)
          (_ : ⟦(SMT.Term.var rhelper).abstract
            (Function.update Theta rhelper (some H)) (pf rhelper H)⟧ˢ =
              some H)
          (hphi : RenamingContext.CoversFV
            (Function.update Theta rhelper (some H)) rspec)
          (_ : ⟦rspec.abstract (Function.update Theta rhelper (some H))
            hphi⟧ˢ = some Phi),
          H.snd.fst = SMTType.fun
            (SMTType.pair gamma.toSMTType alpha.toSMTType) SMTType.bool ∧
          Phi.snd.fst = SMTType.bool ∧
          (Phi.fst = zftrue ∧
            denF.fst.pair H.fst ∈ (castZF_of_path c).1) ∧
          (∀ (Y : SMT.Dom)
            (_ : Y.snd.fst = SMTType.fun
              (SMTType.pair gamma.toSMTType alpha.toSMTType) SMTType.bool)
            (hphiY : RenamingContext.CoversFV
              (Function.update Theta rhelper (some Y)) rspec),
            (⟦rspec.abstract (Function.update Theta rhelper (some Y))
              hphiY⟧ˢ).isSome = true ∧
            ∀ {PhiY : SMT.Dom},
              ⟦rspec.abstract (Function.update Theta rhelper (some Y))
                hphiY⟧ˢ = some PhiY →
              PhiY.fst = zftrue →
              denF.fst.pair Y.fst ∈ (castZF_of_path c).1))
    (ghelper_fresh : ghelper ∉ Lambda1)
    (u_fresh : u ∉ Lambda1) (v_fresh : v ∉ Lambda1)
    (ghelper_ne_u : ghelper ≠ u) (ghelper_ne_v : ghelper ≠ v)
    (u_ne_v : u ≠ v)
    (hgspec : gspec = SMT.Term.forall [u, v]
      [gamma.toSMTType, alpha.toSMTType]
      (relationOptionTermBody (.var rhelper) ghelper u v))
    {Theta : SMT.RenamingContext.Context.{u}}
    (hcov_f : RenamingContext.CoversFV Theta f)
    (hcov_x : RenamingContext.CoversFV Theta x)
    (respects_f : SMT.RenamingContext.RespectsTypeContextOnFV
      Theta GammaSup f)
    (respects_x : SMT.RenamingContext.RespectsTypeContextOnFV
      Theta GammaSup x)
    {F X T R Y : ZFSet.{u}}
    {hF : F ∈ ⟦BType.set (gamma ×ᴮ alpha)⟧ᶻ}
    {hX : X ∈ ⟦gamma⟧ᶻ} {hT : T ∈ ⟦alpha⟧ᶻ}
    {hR : R ∈ ⟦SMTType.fun
      (SMTType.pair gamma.toSMTType alpha.toSMTType) SMTType.bool⟧ᶻ}
    {hY : Y ∈ ⟦gamma.toSMTType⟧ᶻ}
    (hden_f : ⟦f.abstract Theta hcov_f⟧ˢ =
      some (⟨R, SMTType.fun
        (SMTType.pair gamma.toSMTType alpha.toSMTType)
        SMTType.bool, hR⟩ : SMT.Dom))
    (hden_x : ⟦x.abstract Theta hcov_x⟧ˢ =
      some (⟨Y, gamma.toSMTType, hY⟩ : SMT.Dom))
    (Frel : RDomCastSupported
      (⟨F, BType.set (gamma ×ᴮ alpha), hF⟩ : B.Dom)
      (⟨R, SMTType.fun
        (SMTType.pair gamma.toSMTType alpha.toSMTType)
        SMTType.bool, hR⟩ : SMT.Dom))
    (Xrel : RDomCastSupported (⟨X, gamma, hX⟩ : B.Dom)
      (⟨Y, gamma.toSMTType, hY⟩ : SMT.Dom))
    (hmem : X.pair T ∈ F)
    (hcov_out : RenamingContext.CoversFV Theta
      (SMT.Term.the (SMT.Term.app (.var ghelper) x)))
    (denOut : SMT.Dom.{u})
    (respects_out : SMT.RenamingContext.RespectsTypeContextOnFV
      Theta GammaSup (SMT.Term.the (SMT.Term.app (.var ghelper) x)))
    (specs_true : SpecBodiesTrue Theta GammaSup
      (helperSpecChunk rhelper
        (SMTType.fun
          (SMTType.pair gamma.toSMTType alpha.toSMTType) SMTType.bool)
        rspec ++
        helperSpecChunk ghelper
          (SMTType.fun gamma.toSMTType (SMTType.option alpha.toSMTType))
          gspec))
    (hden_out : ⟦(SMT.Term.the (SMT.Term.app (.var ghelper) x)).abstract
      Theta hcov_out⟧ˢ = some denOut)
    (denOutTy : denOut.snd.fst = alpha.toSMTType) :
    RDomCastSupported (⟨T, alpha, hT⟩ : B.Dom) denOut := by
  have scope_r := ScopedContextExtends.left_of_append scope
  have scope_g := ScopedContextExtends.right_of_generated r_ctx_gen scope
  have respects_f_base :
      SMT.RenamingContext.RespectsTypeContextOnFV Theta Lambda f :=
    respects_f.of_super scope.base
  let pf : ∀ (w : SMT.𝒱) (H : SMT.Dom),
      ∀ z ∈ SMT.fv (SMT.Term.var w),
        (Function.update Theta w (some H) z).isSome = true := by
    intro w H z hz
    simp only [SMT.fv, List.mem_singleton] at hz
    subst z
    simp
  obtain ⟨_PhiW, _HW, _hdenVarW, _hcovSpecW, _hdenSpecW,
      _HWty, _PhiWty, _castW, guard⟩ :=
    exactness Theta hcov_f respects_f_base pf
      (⟨R, SMTType.fun
        (SMTType.pair gamma.toSMTType alpha.toSMTType)
        SMTType.bool, hR⟩ : SMT.Dom) hden_f
  have specs_r := SpecBodiesTrue.left_of_append specs_true
  have specs_g := SpecBodiesTrue.right_of_append specs_true
  have hgspec_true := specs_g gspec (by simp)
  obtain ⟨hcov_gspec, _denGSpec, respects_gspec, _hden_gspec,
      _denGSpecTy, _denGSpecTrue⟩ := hgspec_true
  have rhelper_lookup : GammaSup.lookup rhelper = some
      (SMTType.fun
        (SMTType.pair gamma.toSMTType alpha.toSMTType) SMTType.bool) :=
    scope_r.lookup_of_declared (by simp [declEntries_helperSpecChunk])
  have rhelper_mem_Lambda1 : rhelper ∈ Lambda1 :=
    SMT.Typing.mem_context_of_mem_fv typ_rhelper (by simp [SMT.fv])
  have rhelper_ne_u : rhelper ≠ u := fun h => by
    subst u
    exact u_fresh rhelper_mem_Lambda1
  have rhelper_ne_v : rhelper ≠ v := fun h => by
    subst v
    exact v_fresh rhelper_mem_Lambda1
  have rhelper_fv_gspec : rhelper ∈ SMT.fv gspec := by
    rw [hgspec, mem_fv_relationOptionForall_iff]
    exact ⟨Or.inl (by simp [SMT.fv]), rhelper_ne_u, rhelper_ne_v⟩
  have rhelper_some := hcov_gspec rhelper rhelper_fv_gspec
  obtain ⟨H, hH⟩ := Option.isSome_iff_exists.mp rhelper_some
  have Hty : H.snd.fst = SMTType.fun
      (SMTType.pair gamma.toSMTType alpha.toSMTType) SMTType.bool := by
    obtain ⟨d, hd, hdty⟩ :=
      respects_gspec rhelper_fv_gspec rhelper_lookup
    rw [hH] at hd
    injection hd with hdeq
    subst d
    exact hdty
  have hupdate : Function.update Theta rhelper (some H) = Theta := by
    rw [← hH]
    exact Function.update_eq_self rhelper Theta
  have hrspec_true := specs_r rspec (by simp)
  obtain ⟨hcov_rspec, denRSpec, _respects_rspec, hden_rspec,
      _denRSpecTy, denRSpecTrue⟩ := hrspec_true
  have hcov_rspec_update : RenamingContext.CoversFV
      (Function.update Theta rhelper (some H)) rspec := by
    rw [hupdate]
    exact hcov_rspec
  obtain ⟨_some, castPair⟩ := guard H Hty hcov_rspec_update
  have hden_rspec_update :
      ⟦rspec.abstract (Function.update Theta rhelper (some H))
        hcov_rspec_update⟧ˢ = some denRSpec := by
    simpa only [hupdate, proof_irrel_heq] using hden_rspec
  have castPair' := castPair hden_rspec_update denRSpecTrue
  have Hmem : H.fst ∈ ⟦SMTType.fun
      (SMTType.pair gamma.toSMTType alpha.toSMTType) SMTType.bool⟧ᶻ := by
    rw [← Hty]
    exact H.snd.snd
  have hcast : castZF_apply c R = H.fst :=
    castZF_apply_eq_of_pair c hR castPair'
  have H_eq_R : H.fst = R := by
    rw [castZF_apply_self c hR] at hcast
    exact hcast.symm
  have FrelH : RDomCastSupported
      (⟨F, BType.set (gamma ×ᴮ alpha), hF⟩ : B.Dom)
      (⟨H.fst, SMTType.fun
        (SMTType.pair gamma.toSMTType alpha.toSMTType)
        SMTType.bool, Hmem⟩ : SMT.Dom) := by
    have hdomEq :
        (⟨H.fst, SMTType.fun
          (SMTType.pair gamma.toSMTType alpha.toSMTType)
          SMTType.bool, Hmem⟩ : SMT.Dom) =
        (⟨R, SMTType.fun
          (SMTType.pair gamma.toSMTType alpha.toSMTType)
          SMTType.bool, hR⟩ : SMT.Dom) := by
      cases H_eq_R
      rfl
    rw [hdomEq]
    exact Frel
  have hcov_rvar : RenamingContext.CoversFV Theta (.var rhelper) := by
    intro w hw
    simp only [SMT.fv, List.mem_singleton] at hw
    subst w
    exact rhelper_some
  have hden_rvar : ⟦(SMT.Term.var rhelper).abstract Theta hcov_rvar⟧ˢ =
      some (⟨H.fst, SMTType.fun
        (SMTType.pair gamma.toSMTType alpha.toSMTType)
        SMTType.bool, Hmem⟩ : SMT.Dom) := by
    rw [SMT.Term.abstract.eq_def]
    simp only [SMT.denote]
    have hget := Option.get_of_eq_some rhelper_some hH
    rw [hget]
    rcases H with ⟨Hv, Hsigma, hHv⟩
    dsimp at Hty
    subst Hsigma
    rfl
  have respects_rvar :
      SMT.RenamingContext.RespectsTypeContextOnFV Theta GammaSup
        (.var rhelper) := by
    intro w sigma hw hlookup
    simp only [SMT.fv, List.mem_singleton] at hw
    subst w
    rw [rhelper_lookup] at hlookup
    cases hlookup
    exact ⟨H, hH, Hty⟩
  exact castApp_relation_term_guarded_semantics scope_g typ_rhelper typ_x1
    ghelper_fresh u_fresh v_fresh ghelper_ne_u ghelper_ne_v u_ne_v
    hgspec hcov_rvar hcov_x respects_rvar respects_x hden_rvar hden_x
    FrelH Xrel hmem hcov_out denOut respects_out specs_g hden_out denOutTy

set_option maxHeartbeats 8000000 in
theorem castApp_relation_fun_scoped_contract.{u}
    (gamma alpha : BType) (f x : SMT.Term)
    (hle : gamma.toSMTType ⊑ gamma.toSMTType) :
    CastAppRepScopedSpec.{u} gamma alpha f x
      (SMTType.fun
        (SMTType.pair gamma.toSMTType alpha.toSMTType) SMTType.bool)
      gamma.toSMTType := by
  unfold CastAppRepScopedSpec
  intro Lambda n used decl typ_f typ_x bv_f_used bv_x_used
  let crel : SMTType.fun
      (SMTType.pair gamma.toSMTType alpha.toSMTType) SMTType.bool ~>
      SMTType.fun
        (SMTType.pair gamma.toSMTType alpha.toSMTType) SMTType.bool :=
    castPath.chpred (castPath.pair hle.toCastPath
      (castPath.reflexive alpha.toSMTType))
  mstart
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_keys, St_used_eq, St_decl_eq⟩ := pre
  simp only [castApp]
  rw [dif_pos hle]
  mspec (Std.Do.Triple.and _
    (Std.Do.Triple.and _
      (Std.Do.Triple.and _
        (Std.Do.Triple.and _
          (loosenAux_prf_exact_univ
            (Λ := St.types) (n := St.env.freshvarsc)
            (used := St.env.usedVars) typ_f
            (fun w hw => St_used_eq ▸ bv_f_used w hw) crel)
          (loosenAux_prf_fv_of_faithful (castPath.fvFaithful crel)
            (used := St.env.usedVars) (n := St.env.freshvarsc)
            (x := f) (by
              intro w hw
              exact St_keys (SMT.Typing.mem_context_of_mem_fv typ_f hw))))
        (loosenAux_prf_decls crel (decl := decl)))
      (loosenAux_prf_types_eq crel))
    (loosenAux_prf_bv crel
      (used := St.env.usedVars) (n := St.env.freshvarsc)
      (x := f) (fun w hw => St_used_eq ▸ bv_f_used w hw)))
  next out =>
  obtain ⟨rhelper, rspec⟩ := out
  mrename_i pre
  mintro ∀St1
  mpure pre
  obtain ⟨⟨⟨⟨⟨_hn1, St1_types_sub, rhelper_fresh,
      rhelper_not_used, used_sub1, keys_sub1, preserves1,
      _typ_helper_insert, _typ_spec_insert, typ_rhelper, typ_rspec,
      rspec_fv, exactness⟩, _helper_not_used_fv, _source_fv_spec,
      _used_sub_fv⟩, St1_decl_eq⟩, ⟨St1_types_exact, _⟩⟩,
      ⟨_rhelper_bv_used, rspec_bv_used, _used_sub_bv⟩⟩ := pre
  mspec SMT.declareConst_addSpec_spec (x! := rhelper)
    (x!_spec := rspec)
    (τ := SMTType.fun
      (SMTType.pair gamma.toSMTType alpha.toSMTType) SMTType.bool)
    (decl := St1.env.declarations) (as := St1.env.asserts)
    (n := St1.env.freshvarsc) (Γ := St1.types)
    (used := St1.env.usedVars)
  mrename_i pre
  mintro ∀St2
  mpure pre
  obtain ⟨St2_decl_eq, _, St2_fvc, St2_used, St2_types⟩ := pre
  mspec (Std.Do.Triple.and _ SMT.freshVar_spec
    (SMT.freshVar_decls (decl := St2.env.declarations)))
  next ghelper =>
  mrename_i pre
  mintro ∀St3
  mpure pre
  obtain ⟨⟨St3_types, ghelper_fresh, St3_fvc, St3_used,
      ghelper_not_used⟩, St3_decl⟩ := pre
  mspec SMT.declareConst_spec (v := ghelper)
    (τ := SMTType.fun gamma.toSMTType
      (SMTType.option alpha.toSMTType))
  mrename_i pre
  mintro ∀St4
  mpure pre
  obtain ⟨St4_decl, _, St4_fvc, St4_used, St4_types⟩ := pre
  mspec (Std.Do.Triple.and _ SMT.freshVar_spec
    (SMT.freshVar_decls (decl := St4.env.declarations)))
  next u =>
  mrename_i pre
  mintro ∀St5
  mpure pre
  obtain ⟨⟨St5_types, u_fresh, St5_fvc, St5_used, u_not_used⟩,
    St5_decl⟩ := pre
  mspec (Std.Do.Triple.and _ SMT.freshVar_spec
    (SMT.freshVar_decls (decl := St5.env.declarations)))
  next v =>
  mrename_i pre
  mintro ∀St6
  mpure pre
  obtain ⟨⟨St6_types, v_fresh, St6_fvc, St6_used, v_not_used⟩,
    St6_decl⟩ := pre
  let gspec : SMT.Term := SMT.Term.forall [u, v]
    [gamma.toSMTType, alpha.toSMTType]
    (relationOptionTermBody (.var rhelper) ghelper u v)
  mspec (Std.Do.Triple.and _ SMT.eraseFromContext_spec
    (SMT.eraseFromContext_used_decls
      (used := St6.env.usedVars) (decl := St6.env.declarations)))
  mrename_i pre
  mintro ∀St7
  mpure pre
  obtain ⟨⟨St7_types, St7_fvc, St7_used⟩,
    St7_used', St7_decl⟩ := pre
  mspec (Std.Do.Triple.and _ SMT.eraseFromContext_spec
    (SMT.eraseFromContext_used_decls
      (used := St7.env.usedVars) (decl := St7.env.declarations)))
  mrename_i pre
  mintro ∀St8
  mpure pre
  obtain ⟨⟨St8_types, St8_fvc, St8_used⟩,
    St8_used', St8_decl⟩ := pre
  mspec SMT.addSpec_spec (x! := ghelper) (x!_spec := gspec)
  mrename_i pre
  mintro ∀St9
  mpure pre
  obtain ⟨St9_decl, _, St9_fvc, St9_used, St9_types⟩ := pre
  mspec Std.Do.Spec.pure
  have Lambda_sub1 : St.types ⊆ St1.types := fun w hw =>
    St1_types_sub
      (SMT.TypeContext.entries_subset_insert_of_notMem rhelper_fresh hw)
  have typ_x1 : St1.types ⊢ˢ x : gamma.toSMTType :=
    SMT.Typing.weakening Lambda_sub1 typ_x
      (fun w hw => preserves1 w (St_used_eq ▸ bv_x_used w hw)
        (SMT.Typing.bv_notMem_context typ_x w hw))
  have ghelper_fresh_St1 : ghelper ∉ St1.types := by
    rw [← St2_types]
    exact ghelper_fresh
  have St1_sub3 : St1.types ⊆ St3.types := by
    rw [St3_types, St2_types]
    exact SMT.TypeContext.entries_subset_insert_of_notMem ghelper_fresh_St1
  have typ_rhelper3 : St3.types ⊢ˢ (.var rhelper) : SMTType.fun
      (SMTType.pair gamma.toSMTType alpha.toSMTType) SMTType.bool :=
    SMT.Typing.weakening St1_sub3 typ_rhelper (by simp [SMT.bv])
  have typ_x3 : St3.types ⊢ˢ x : gamma.toSMTType :=
    SMT.Typing.weakening St1_sub3 typ_x1 (by
      intro w hw hmem
      rw [St3_types, St2_types, AList.mem_insert] at hmem
      rcases hmem with h | hmem
      · subst w
        exact ghelper_not_used
          (St2_used ▸ used_sub1 (St_used_eq ▸ bv_x_used ghelper hw))
      · exact SMT.Typing.bv_notMem_context typ_x1 w hw hmem)
  have typ_rspec3 : St3.types ⊢ˢ rspec : SMTType.bool :=
    SMT.Typing.weakening St1_sub3 typ_rspec (by
      intro w hw hmem
      rw [St3_types, St2_types, AList.mem_insert] at hmem
      rcases hmem with h | hmem
      · subst w
        exact ghelper_not_used (St2_used ▸ rspec_bv_used ghelper hw)
      · exact SMT.Typing.bv_notMem_context typ_rspec w hw hmem)
  have u_ne_v : u ≠ v := by
    intro h
    apply v_fresh
    rw [St5_types, AList.mem_insert]
    exact Or.inl h.symm
  have v_fresh_St3 : v ∉ St3.types := by
    intro hv
    apply v_fresh
    rw [St5_types, St4_types]
    exact AList.mem_insert _ |>.mpr (Or.inr hv)
  have u_fresh_St3 : u ∉ St3.types := by
    rw [← St4_types]
    exact u_fresh
  have ghelper_ne_u : ghelper ≠ u := by
    intro h
    subst u
    exact u_fresh_St3 (by
      rw [St3_types]
      exact AList.mem_insert _ |>.mpr (Or.inl rfl))
  have ghelper_ne_v : ghelper ≠ v := by
    intro h
    subst v
    exact v_fresh_St3 (by
      rw [St3_types]
      exact AList.mem_insert _ |>.mpr (Or.inl rfl))
  have St8_types_base : St8.types = St3.types := by
    rw [St8_types, St7_types, St6_types, St5_types, St4_types,
      encodeTerm_state.erase_insert_ne u_ne_v,
      encodeTerm_state.erase_insert_self u_fresh_St3,
      encodeTerm_state.erase_insert_self v_fresh_St3]
  have ghelper_lookup3 : St3.types.lookup ghelper = some
      (SMTType.fun gamma.toSMTType
        (SMTType.option alpha.toSMTType)) := by
    rw [St3_types, St2_types, AList.lookup_insert]
  have typOut : St3.types ⊢ˢ
      (SMT.Term.the (SMT.Term.app (.var ghelper) x)) :
        alpha.toSMTType := by
    apply SMT.Typing.the
    apply SMT.Typing.app
    · apply SMT.Typing.var
      exact ghelper_lookup3
    · exact typ_x3
  have gspec_eq : gspec = SMT.Term.forall [u, v]
      [gamma.toSMTType, alpha.toSMTType]
      (relationOptionTermBody (.var rhelper) ghelper u v) := rfl
  have typ_gspec : St3.types ⊢ˢ gspec : SMTType.bool := by
    rw [gspec_eq]
    refine SMT.Typing.forall St3.types [u, v]
      [gamma.toSMTType, alpha.toSMTType]
      (relationOptionTermBody (.var rhelper) ghelper u v)
      ?_ (by simp [relationOptionTermBody, SMT.bv]) (by simp) rfl ?_
    · intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      exact hw.elim (fun h => h ▸ u_fresh_St3)
        (fun h => h ▸ v_fresh_St3)
    · have hupdate : SMT.TypeContext.update St3.types [u, v]
          [gamma.toSMTType, alpha.toSMTType] rfl =
          (St3.types.insert u gamma.toSMTType).insert v alpha.toSMTType := by
        simp only [SMT.TypeContext.update, List.length_cons, List.length_nil,
          Nat.reduceAdd, Fin.foldl_succ_last, Fin.getElem_fin, Fin.coe_cast,
          Fin.val_last, List.getElem_append_right, Nat.reduceSubDiff,
          List.getElem_cons_succ, List.getElem_cons_zero, Fin.coe_castSucc,
          Fin.foldl_zero]
      rw [hupdate]
      apply SMT.Typing.eq
      · apply SMT.Typing.app
        · apply SMT.Typing.var
          have rhelper_in3 : rhelper ∈ St3.types :=
            SMT.Typing.mem_context_of_mem_fv typ_rhelper3
              (by simp [SMT.fv])
          have rhelper_ne_u : rhelper ≠ u := fun h =>
            u_fresh_St3 (h ▸ rhelper_in3)
          have rhelper_ne_v : rhelper ≠ v := fun h =>
            v_fresh_St3 (h ▸ rhelper_in3)
          rw [AList.lookup_insert_ne rhelper_ne_v,
            AList.lookup_insert_ne rhelper_ne_u]
          exact SMT.Typing.varE typ_rhelper3
        · apply SMT.Typing.pair
          · apply SMT.Typing.var
            rw [AList.lookup_insert_ne u_ne_v, AList.lookup_insert]
          · apply SMT.Typing.var
            rw [AList.lookup_insert]
      · apply SMT.Typing.eq
        · apply SMT.Typing.app
          · apply SMT.Typing.var
            rw [AList.lookup_insert_ne ghelper_ne_v,
              AList.lookup_insert_ne ghelper_ne_u, ghelper_lookup3]
          · apply SMT.Typing.var
            rw [AList.lookup_insert_ne u_ne_v, AList.lookup_insert]
        · apply SMT.Typing.some
          apply SMT.Typing.var
          rw [AList.lookup_insert]
  have r_ctx_gen : ContextGeneratedByDeclarations St.types St1.types
      (helperSpecChunk rhelper
        (SMTType.fun
          (SMTType.pair gamma.toSMTType alpha.toSMTType) SMTType.bool)
        rspec) := by
    rw [St1_types_exact]
    exact ContextGeneratedByDeclarations.insert_helper
      St.types rhelper _ rspec rhelper_fresh
  have r_ctx_trace : DeclarationContextTrace St.types
      (helperSpecChunk rhelper
        (SMTType.fun
          (SMTType.pair gamma.toSMTType alpha.toSMTType) SMTType.bool)
        rspec) St1.types := by
    rw [St1_types_exact]
    exact DeclarationContextTrace.helperSpecChunk
      St.types rhelper _ rspec rhelper_fresh
  have g_ctx_gen : ContextGeneratedByDeclarations St1.types St3.types
      (helperSpecChunk ghelper
        (SMTType.fun gamma.toSMTType (SMTType.option alpha.toSMTType))
        gspec) := by
    rw [St3_types, St2_types]
    exact ContextGeneratedByDeclarations.insert_helper St1.types ghelper _
      gspec ghelper_fresh_St1
  have g_ctx_trace : DeclarationContextTrace St1.types
      (helperSpecChunk ghelper
        (SMTType.fun gamma.toSMTType (SMTType.option alpha.toSMTType))
        gspec) St3.types := by
    rw [St3_types, St2_types]
    exact DeclarationContextTrace.helperSpecChunk St1.types ghelper _
      gspec ghelper_fresh_St1
  have all_ctx_gen := ContextGeneratedByDeclarations.append r_ctx_gen g_ctx_gen
  have all_ctx_trace := DeclarationContextTrace.append r_ctx_trace g_ctx_trace
  have rhelper_lookup : St1.types.lookup rhelper = some
      (SMTType.fun
        (SMTType.pair gamma.toSMTType alpha.toSMTType) SMTType.bool) :=
    SMT.Typing.varE typ_rhelper
  have rhelper_usedMid : rhelper ∈ St1.env.usedVars :=
    keys_sub1 (AList.lookup_isSome.mp
      (Option.isSome_of_eq_some rhelper_lookup))
  have u_not_usedMid : u ∉ St1.env.usedVars := by
    intro hu
    apply u_not_used
    rw [St4_used, St3_used, St2_used]
    exact List.mem_cons_of_mem _ hu
  have v_not_usedMid : v ∉ St1.env.usedVars := by
    intro hv
    apply v_not_used
    rw [St5_used, St4_used, St3_used, St2_used]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hv)
  have used_sub_out : used ⊆ St9.env.usedVars := by
    intro w hw
    rw [St9_used, St8_used, St7_used, St6_used, St5_used,
      St4_used, St3_used, St2_used]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (used_sub1 (St_used_eq ▸ hw))))
  have used_mid_sub : St1.env.usedVars ⊆ St9.env.usedVars := by
    intro w hw
    rw [St9_used, St8_used, St7_used, St6_used, St5_used,
      St4_used, St3_used, St2_used]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ hw))
  have ghelper_used1 : ghelper ∈ St9.env.usedVars := by
    rw [St9_used, St8_used, St7_used, St6_used, St5_used,
      St4_used, St3_used]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have keys_sub3 : St3.types.keys ⊆ St9.env.usedVars := by
    intro w hw
    rw [St9_used, St8_used, St7_used, St6_used, St5_used,
      St4_used, St3_used, St2_used]
    rw [St3_types, St2_types] at hw
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (keys_insert_subset_cons keys_sub1 hw))
  have preserves_out : ∀ w ∈ used, w ∉ St.types → w ∉ St3.types := by
    intro w hw hnot hmem
    rw [St3_types, St2_types, AList.mem_insert] at hmem
    rcases hmem with rfl | hmem
    · exact ghelper_not_used
        (St2_used ▸ used_sub1 (St_used_eq ▸ hw))
    · exact preserves1 w (St_used_eq ▸ hw) hnot hmem
  have rhelper_not_used_out : rhelper ∉ used := by
    simpa [St_used_eq] using rhelper_not_used
  have ghelper_not_used_out : ghelper ∉ used := by
    intro hw
    exact ghelper_not_used (St2_used ▸ used_sub1 (St_used_eq ▸ hw))
  have ghelper_not_usedMid : ghelper ∉ St1.env.usedVars := by
    simpa [St2_used] using ghelper_not_used
  have u_fresh_St1 : u ∉ St1.types := fun hu =>
    u_fresh_St3 (AList.mem_of_subset St1_sub3 hu)
  have v_fresh_St1 : v ∉ St1.types := fun hv =>
    v_fresh_St3 (AList.mem_of_subset St1_sub3 hv)
  mpure_intro
  rw [St9_types, St8_types_base]
  let Dlt := helperSpecChunk rhelper
      (SMTType.fun
        (SMTType.pair gamma.toSMTType alpha.toSMTType) SMTType.bool)
      rspec ++
    helperSpecChunk ghelper
      (SMTType.fun gamma.toSMTType (SMTType.option alpha.toSMTType))
      gspec
  refine ⟨used_sub_out, AList.subset_trans Lambda_sub1 St1_sub3,
    keys_sub3, True.intro, typOut, preserves_out, Dlt, ?_,
    all_ctx_gen, all_ctx_trace, ?_, ?_, ?_, ?_⟩
  · rw [St9_decl, St8_decl, St7_decl, St6_decl, St5_decl,
      St4_decl, St3_decl, St2_decl_eq, St1_decl_eq]
    simp [Dlt, helperSpecChunk, List.concat_eq_append,
      List.append_assoc]
  · intro w hw
    simp only [Dlt, declVars_append, declVars_helperSpecChunk,
      List.mem_append, List.mem_singleton] at hw
    exact hw.elim (fun h => h ▸ rhelper_not_used_out)
      (fun h => h ▸ ghelper_not_used_out)
  · intro GammaSup GammaSub Theta hcov_f hcov_x Theta_none
      respects_f respects_x Theta_dom F X T hF hX hT hfun hdom
      hresult denF denX hden_f hden_x hdenFty hdenXty Frel Xrel
    have Lambda1_sub_sup : St1.types ⊆ GammaSup :=
      AList.subset_trans St1_sub3 GammaSub
    have Lambda_sub_sup : St.types ⊆ GammaSup :=
      AList.subset_trans Lambda_sub1 Lambda1_sub_sup
    have respects_f_base := respects_f.of_super Lambda_sub_sup
    have respects_x_base := respects_x.of_super Lambda_sub_sup
    have ghelper_lookup_sup : GammaSup.lookup ghelper = some
        (SMTType.fun gamma.toSMTType
          (SMTType.option alpha.toSMTType)) :=
      AList.lookup_of_subset GammaSub ghelper_lookup3
    rcases denF with ⟨R, sigmaF, hR⟩
    rcases denX with ⟨Y, sigmaX, hY⟩
    dsimp at hdenFty hdenXty
    subst sigmaF
    subst sigmaX
    have hmem : X.pair T ∈ F := by
      rw [← hresult]
      exact ZFSet.fapply.def hfun hdom
    constructor
    · exact castApp_relation_fun_semantics typ_f typ_x typ_rhelper
        typ_x1 Lambda_sub1 Lambda1_sub_sup rhelper_fresh rhelper_lookup
        rhelper_not_used_out rhelper_usedMid
        (by simpa [St_used_eq] using used_sub1) rspec_fv crel exactness
        ghelper_fresh_St1 ghelper_lookup_sup ghelper_not_usedMid
        ghelper_used1 u_not_usedMid v_not_usedMid used_mid_sub
        ghelper_ne_u ghelper_ne_v u_ne_v gspec_eq hcov_f hcov_x
        Theta_none respects_f_base respects_x_base Theta_dom hden_f
        hden_x Frel Xrel hfun hmem
    · intro GammaSupG scopeG ThetaG hcov_fG hcov_xG
        respects_fG respects_xG FG XG TG hFG hXG hTG hfunG hdomG
        hresultG denFG denXG hden_fG hden_xG hdenFGty hdenXGty
        FrelG XrelG hcov_outG denOutG respects_outG specs_trueG
        hden_outG denOutGTy
      rcases denFG with ⟨RG, sigmaFG, hRG⟩
      rcases denXG with ⟨YG, sigmaXG, hYG⟩
      dsimp at hdenFGty hdenXGty
      subst sigmaFG
      subst sigmaXG
      have hmemG : XG.pair TG ∈ FG := by
        rw [← hresultG]
        exact ZFSet.fapply.def hfunG hdomG
      exact castApp_relation_fun_guarded_semantics r_ctx_gen scopeG typ_f
        typ_rhelper typ_x1 crel exactness ghelper_fresh_St1
        u_fresh_St1 v_fresh_St1 ghelper_ne_u ghelper_ne_v u_ne_v
        gspec_eq hcov_fG hcov_xG respects_fG respects_xG hden_fG
        hden_xG FrelG XrelG hmemG hcov_outG denOutG respects_outG
        specs_trueG hden_outG denOutGTy
  · intro body hbody
    simp only [Dlt, specBodies_append, specBodies_helperSpecChunk,
      List.mem_append, List.mem_singleton] at hbody
    exact hbody.elim (fun h => h ▸ typ_rspec3)
      (fun h => h ▸ typ_gspec)
  · exact ScopedGeneratedTyping.of_operational all_ctx_gen typOut (by
      intro body hbody
      simp only [Dlt, specBodies_append, specBodies_helperSpecChunk,
        List.mem_append, List.mem_singleton] at hbody
      exact hbody.elim (fun h => h ▸ typ_rspec3)
        (fun h => h ▸ typ_gspec))

theorem castApp_relation_supported_rep_scoped_contract.{u}
    (gamma alpha : BType) (f x : SMT.Term) (sx : SMTType)
    (supported_x : BType.SupportedSMT gamma sx) :
    CastAppRepScopedSpec.{u} gamma alpha f x
      (SMTType.fun
        (SMTType.pair gamma.toSMTType alpha.toSMTType) SMTType.bool) sx := by
  by_cases hforward : gamma.toSMTType ⊑ sx
  · have hsx := supported_x.eq_canonical_of_cast_from_canonical
      hforward.toCastPath
    subst sx
    exact castApp_relation_fun_scoped_contract gamma alpha f x hforward
  · let hback : sx ⊑ gamma.toSMTType :=
      castable?_of_castPath supported_x.toCanonicalCastPath
    exact castApp_relation_arg_scoped_contract gamma alpha f x sx
      hforward hback (supported_x.toCastPath_faithful hback)

/-! ## Application constructor composition -/

private theorem encodeTerm_app_via_maplet (f x : B.Term) (E : B.Env) :
    encodeTerm (.app f x) E = (do
      let ⟨p, sigmaP⟩ ← encodeTerm (f ↦ᴮ x) E
      match p, sigmaP with
      | .pair f' x', .pair sigmaF sigmaX =>
          castApp ⟨f', sigmaF⟩ ⟨x', sigmaX⟩
      | _, _ => throw "encodeTerm:app: impossible maplet result") := by
  simp [encodeTerm]

private theorem denote_pair_inv_app.{u}
    {f x : SMT.Term} {Theta : SMT.RenamingContext.Context.{u}}
    (hcov : RenamingContext.CoversFV Theta (SMT.Term.pair f x))
    {d : SMT.Dom.{u}}
    (hden : ⟦(SMT.Term.pair f x).abstract Theta hcov⟧ˢ = some d) :
    ∃ (df dx : SMT.Dom.{u}),
      ⟦f.abstract Theta (fun v hv => hcov v (by
        rw [SMT.fv, List.mem_append]
        exact Or.inl hv))⟧ˢ = some df ∧
      ⟦x.abstract Theta (fun v hv => hcov v (by
        rw [SMT.fv, List.mem_append]
        exact Or.inr hv))⟧ˢ = some dx ∧
      d = ⟨df.fst.pair dx.fst,
        SMTType.pair df.snd.fst dx.snd.fst,
        ZFSet.pair_mem_prod.mpr ⟨df.snd.snd, dx.snd.snd⟩⟩ := by
  rw [SMT.Term.abstract, SMT.denote, Option.pure_def,
    Option.bind_eq_bind, Option.bind_eq_some_iff] at hden
  obtain ⟨df, hdenf, hrest⟩ := hden
  rw [Option.bind_eq_some_iff] at hrest
  obtain ⟨dx, hdenx, hout⟩ := hrest
  refine ⟨df, dx, ?_, ?_, ?_⟩
  · simpa only [proof_irrel_heq] using hdenf
  · simpa only [proof_irrel_heq] using hdenx
  · simpa using hout.symm

set_option maxHeartbeats 6000000 in
theorem encodeTerm_rep_spec.app_case.{u}
    (f x : B.Term)
    (f_ih : EncodeTermRepIH.{u} f)
    (x_ih : EncodeTermRepIH.{u} x)
    (E : B.Env) {Lambda : SMT.TypeContext} {alpha : BType}
    (typ_t : E.context ⊢ᴮ .app f x : alpha)
    {Xi : B.RenamingContext.Context}
    (Xi_fv : ∀ v ∈ B.fv (.app f x), (Xi v).isSome = true)
    {Theta0 : SMT.RenamingContext.Context.{u}}
    (related : RValuationCastSupportedOnFV Xi Theta0 (.app f x))
    {used : List SMT.𝒱}
    (Theta0_none : ∀ v ∉ used, Theta0 v = none)
    (Theta0_dom : ∀ v, Theta0 v ≠ none → v ∈ Lambda)
    {T : ZFSet.{u}} {hT : T ∈ ⟦alpha⟧ᶻ}
    (den_t : ⟦(B.Term.app f x).abstract Xi Xi_fv⟧ᴮ =
      some ⟨T, ⟨alpha, hT⟩⟩)
    (vars_used : ∀ v ∈ (B.Term.app f x).vars, v ∈ used)
    (Lambda_inv : ∀ v ∈ (B.Term.app f x).vars,
      v ∈ Lambda → v ∈ E.context)
    (bv_nodup : (B.bv (B.Term.app f x)).Nodup)
    (respects : B.RenamingContext.RespectsTypeContextOnFV
      Theta0 Lambda (B.Term.app f x))
    (fv_in_Lambda : ∀ v ∈ B.fv (B.Term.app f x), v ∈ Lambda)
    (wf : B.RenWF E.context Xi)
    {n : ℕ} :
    ⦃fun ⟨E0, Lambda'⟩ =>
      ⌜Lambda' = Lambda ∧ E0.freshvarsc = n ∧
        Lambda.keys ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
    encodeTerm (B.Term.app f x) E
    ⦃⇓? (⟨t', sigma⟩ : SMT.Term × SMTType) ⟨E', Gamma'⟩ =>
      ⌜EncodeTermRepPost (B.Term.app f x) alpha Lambda Xi Theta0
        used T hT E t' sigma E' Gamma'⌝⦄ := by
  mstart
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_keys, St_used_eq⟩ := pre
  rw [encodeTerm_app_via_maplet]

  obtain ⟨gamma, typ_f, typ_x⟩ := B.Typing.appE typ_t
  obtain ⟨F, X, hF, hX, den_f, den_x, hfun, hdom, hresult⟩ :=
    B.denote_app_inv_rep typ_f typ_x Xi_fv wf den_t

  let Xi_fv_pair : ∀ v ∈ B.fv (f ↦ᴮ x), (Xi v).isSome = true :=
    fun v hv => Xi_fv v (by simpa [B.fv] using hv)
  have den_pair :
      ⟦(f ↦ᴮ x).abstract Xi Xi_fv_pair⟧ᴮ =
        some ⟨F.pair X,
          ⟨BType.set (gamma ×ᴮ alpha) ×ᴮ gamma,
            ZFSet.pair_mem_prod.mpr ⟨hF, hX⟩⟩⟩ := by
    rw [B.Term.abstract, B.denote, Option.pure_def,
      Option.bind_eq_bind]
    have den_f' :
        ⟦f.abstract Xi (fun v hv => Xi_fv_pair v (by
          rw [B.fv, List.mem_append]
          exact Or.inl hv))⟧ᴮ =
          some ⟨F, ⟨BType.set (gamma ×ᴮ alpha), hF⟩⟩ := by
      simpa only [proof_irrel_heq] using den_f
    have den_x' :
        ⟦x.abstract Xi (fun v hv => Xi_fv_pair v (by
          rw [B.fv, List.mem_append]
          exact Or.inr hv))⟧ᴮ = some ⟨X, ⟨gamma, hX⟩⟩ := by
      simpa only [proof_irrel_heq] using den_x
    rw [den_f', Option.bind_some, den_x']
    rfl

  mspec (Std.Do.Triple.and _
    (encodeTerm_rep_spec.maplet_case f x f_ih x_ih E
      (B.Typing.maplet typ_f typ_x) Xi_fv_pair
      (by simpa [B.fv] using related)
      Theta0_none Theta0_dom den_pair
      (fun v hv => vars_used v (by
        simpa [B.Term.vars, B.fv, B.bv] using hv))
      (fun v hv => Lambda_inv v (by
        simpa [B.Term.vars, B.fv, B.bv] using hv))
      (by simpa [B.bv] using bv_nodup)
      (by simpa [B.fv] using respects)
      (fun v hv => fv_in_Lambda v (by simpa [B.fv] using hv)) wf
      (n := St.env.freshvarsc))
    (encodeTerm_bv_used E (t := f ↦ᴮ x)
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
  obtain ⟨fEnc, xEnc, sigmaF, sigmaX,
    hpairTerm, hpairType⟩ := shape_pair
  subst pairTerm
  subst pairType
  focus
    rw [hpairType] at typ_pair pair_total
    rw [hpairType]
    obtain ⟨sigmaF0, sigmaX0, hpair_type, typ_fEnc, typ_xEnc⟩ :=
      SMT.Typing.pairE typ_pair
    injection hpair_type with hsigmaF hsigmaX
    subst sigmaF0
    subst sigmaX0

    have hcov_fEnc : RenamingContext.CoversFV Thetap fEnc := by
      intro v hv
      exact hcov_pair v (by
        rw [SMT.fv, List.mem_append]
        exact Or.inl hv)
    have hcov_xEnc : RenamingContext.CoversFV Thetap xEnc := by
      intro v hv
      exact hcov_pair v (by
        rw [SMT.fv, List.mem_append]
        exact Or.inr hv)
    have target_respects_fEnc :
        SMT.RenamingContext.RespectsTypeContextOnFV
          Thetap Stp.types fEnc := by
      intro v tau hv hlookup
      exact target_respects_p (by
        rw [SMT.fv, List.mem_append]
        exact Or.inl hv) hlookup
    have target_respects_xEnc :
        SMT.RenamingContext.RespectsTypeContextOnFV
          Thetap Stp.types xEnc := by
      intro v tau hv hlookup
      exact target_respects_p (by
        rw [SMT.fv, List.mem_append]
        exact Or.inr hv) hlookup
    obtain ⟨denF, denX, hden_fEnc, hden_xEnc, denPair_eq⟩ :=
      denote_pair_inv_app hcov_pair hden_pair
    rw [denPair_eq] at hpairType pair_rel
    rcases denF with ⟨Fenc, tauF, hFenc⟩
    rcases denX with ⟨Xenc, tauX, hXenc⟩
    dsimp at hpairType
    injection hpairType with htauF htauX
    subst tauF
    subst tauX
    have pair_rel' : RDomCastSupported
        (⟨F.pair X,
          BType.set (gamma ×ᴮ alpha) ×ᴮ gamma,
          ZFSet.pair_mem_prod.mpr ⟨hF, hX⟩⟩ : B.Dom)
        (⟨Fenc.pair Xenc, SMTType.pair sigmaF sigmaX,
          ZFSet.pair_mem_prod.mpr ⟨hFenc, hXenc⟩⟩ : SMT.Dom) := by
      simpa only [proof_irrel_heq] using pair_rel
    obtain ⟨F_rel, X_rel⟩ := RDomCastSupported.of_pair pair_rel'
    have bv_fEnc_used : ∀ v ∈ SMT.bv fEnc, v ∈ Stp.env.usedVars := by
      intro v hv
      exact bv_pair_used v (by
        rw [SMT.bv, List.mem_append]
        exact Or.inl hv)
    have bv_xEnc_used : ∀ v ∈ SMT.bv xEnc, v ∈ Stp.env.usedVars := by
      intro v hv
      exact bv_pair_used v (by
        rw [SMT.bv, List.mem_append]
        exact Or.inr hv)

    have cast_contract : CastAppRepScopedSpec.{u}
        gamma alpha fEnc xEnc sigmaF sigmaX := by
      cases F_rel.supported with
      | setPred tau =>
          exact castApp_relation_supported_rep_scoped_contract
            gamma alpha fEnc xEnc sigmaX X_rel.supported
      | optionFun gamma' alpha' =>
          exact castApp_option_supported_rep_scoped_contract
            gamma alpha fEnc xEnc sigmaX X_rel.supported

    mspec cast_contract typ_fEnc typ_xEnc bv_fEnc_used bv_xEnc_used
    rename_i out_app
    obtain ⟨appEnc, sigmaApp⟩ := out_app
    mrename_i post_app
    mintro ∀StA
    mpure post_app
    obtain ⟨used_sub_app, types_sub_app, keys_sub_app, sigmaApp_eq,
      typ_appEnc, app_preserves, Dlt, _decl_eq, _ctx_gen, _ctx_trace,
      _decl_fresh, app_sem, _specs_typing, _scoped_typing⟩ := post_app
    change sigmaApp = alpha.toSMTType at sigmaApp_eq
    subst sigmaApp
    have types_sub0 : St.types ⊆ StA.types :=
      fun _ h => types_sub_app (types_sub h)
    have target_respects_fEnc_A :
        SMT.RenamingContext.RespectsTypeContextOnFV
          Thetap StA.types fEnc :=
      target_respects_fEnc.of_extends
        (SMT.RenamingContext.extends_refl Thetap)
        types_sub_app typ_fEnc
    have target_respects_xEnc_A :
        SMT.RenamingContext.RespectsTypeContextOnFV
          Thetap StA.types xEnc :=
      target_respects_xEnc.of_extends
        (SMT.RenamingContext.extends_refl Thetap)
        types_sub_app typ_xEnc
    have Thetap_dom_A : ∀ v, Thetap v ≠ none → v ∈ StA.types :=
      fun v hv => AList.mem_of_subset types_sub_app (Thetap_dom v hv)
    obtain ⟨good, _guarded⟩ := app_sem StA.types (fun _ h => h)
      Thetap hcov_fEnc hcov_xEnc Thetap_none
      target_respects_fEnc_A target_respects_xEnc_A Thetap_dom_A
      F X T hF hX hT hfun hdom hresult
      (⟨Fenc, sigmaF, hFenc⟩ : SMT.Dom)
      (⟨Xenc, sigmaX, hXenc⟩ : SMT.Dom)
      hden_fEnc hden_xEnc rfl rfl F_rel X_rel
    obtain ⟨ThetaA, hcov_app, denA, ThetaA_ext, ThetaA_none,
      target_respects_app, ThetaA_dom, _specs_A, hden_app,
      hdenA_type, result_rel⟩ := good
    have ThetaA_ext0 :=
      SMT.RenamingContext.extends_trans ThetaA_ext Thetap_ext

    mpure_intro
    refine ⟨?_, types_sub0, keys_sub_app, ?_,
      ⟨castPath.reflexive alpha.toSMTType⟩, typ_appEnc, trivial,
      ?_, ThetaA, hcov_app, ThetaA_ext0,
      related.of_extends ThetaA_ext0, ThetaA_none, ?_,
      target_respects_app, ThetaA_dom, denA, hden_app,
      hdenA_type, result_rel, ?_⟩
    · intro v hv
      exact used_sub_app (used_sub (by simpa [St_used_eq] using hv))
    · simpa [B.fv] using
        (B.CoversUsedVars.mono used_sub_app covers_used)
    · intro v hv hLambda hvars
      apply app_preserves v (used_sub (by simpa [St_used_eq] using hv))
      exact preserves v (by simpa [St_used_eq] using hv) hLambda
        (by simpa [B.Term.vars, B.fv, B.bv] using hvars)
    · exact respects.of_extends ThetaA_ext0 types_sub0
        (fun _ h => h) fv_in_Lambda
    · intro Xi_alt Xi_fv_alt Theta0_alt related_alt wf_alt
        Theta0_alt_none respects_alt Theta0_alt_dom
        T_alt hT_alt den_t_alt
      obtain ⟨F_alt, X_alt, hF_alt, hX_alt, den_f_alt, den_x_alt,
          hfun_alt, hdom_alt, hresult_alt⟩ :=
        B.denote_app_inv_rep typ_f typ_x Xi_fv_alt wf_alt den_t_alt
      let Xi_fv_pair_alt :
          ∀ v ∈ B.fv (f ↦ᴮ x), (Xi_alt v).isSome = true :=
        fun v hv => Xi_fv_alt v (by simpa [B.fv] using hv)
      have den_pair_alt :
          ⟦(f ↦ᴮ x).abstract Xi_alt Xi_fv_pair_alt⟧ᴮ =
            some ⟨F_alt.pair X_alt,
              ⟨BType.set (gamma ×ᴮ alpha) ×ᴮ gamma,
                ZFSet.pair_mem_prod.mpr ⟨hF_alt, hX_alt⟩⟩⟩ := by
        rw [B.Term.abstract, B.denote, Option.pure_def,
          Option.bind_eq_bind]
        have den_f_alt' :
            ⟦f.abstract Xi_alt (fun v hv => Xi_fv_pair_alt v (by
              rw [B.fv, List.mem_append]
              exact Or.inl hv))⟧ᴮ =
              some ⟨F_alt,
                ⟨BType.set (gamma ×ᴮ alpha), hF_alt⟩⟩ := by
          simpa only [proof_irrel_heq] using den_f_alt
        have den_x_alt' :
            ⟦x.abstract Xi_alt (fun v hv => Xi_fv_pair_alt v (by
              rw [B.fv, List.mem_append]
              exact Or.inr hv))⟧ᴮ =
              some ⟨X_alt, ⟨gamma, hX_alt⟩⟩ := by
          simpa only [proof_irrel_heq] using den_x_alt
        rw [den_f_alt', Option.bind_some, den_x_alt']
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
      obtain ⟨Thetap_alt, hcov_pair_alt, denPairAlt,
          Thetap_alt_ext, _related_p_alt, Thetap_alt_none,
          _respects_p_alt, target_respects_p_alt, Thetap_alt_dom,
          hden_pair_alt, hdenPairAlt_type, pair_alt_rel⟩ :=
        pair_total Xi_alt Xi_fv_pair_alt Theta0_alt
          (by simpa [B.fv] using related_alt) wf_alt
          Theta0_alt_none_pair
          (by simpa [B.fv] using respects_alt)
          Theta0_alt_dom (F_alt.pair X_alt)
          (ZFSet.pair_mem_prod.mpr ⟨hF_alt, hX_alt⟩)
          den_pair_alt
      have hcov_fEnc_alt : RenamingContext.CoversFV Thetap_alt fEnc := by
        intro v hv
        exact hcov_pair_alt v (by
          rw [SMT.fv, List.mem_append]
          exact Or.inl hv)
      have hcov_xEnc_alt : RenamingContext.CoversFV Thetap_alt xEnc := by
        intro v hv
        exact hcov_pair_alt v (by
          rw [SMT.fv, List.mem_append]
          exact Or.inr hv)
      have target_respects_fEnc_alt :
          SMT.RenamingContext.RespectsTypeContextOnFV
            Thetap_alt Stp.types fEnc := by
        intro v tau hv hlookup
        exact target_respects_p_alt (by
          rw [SMT.fv, List.mem_append]
          exact Or.inl hv) hlookup
      have target_respects_xEnc_alt :
          SMT.RenamingContext.RespectsTypeContextOnFV
            Thetap_alt Stp.types xEnc := by
        intro v tau hv hlookup
        exact target_respects_p_alt (by
          rw [SMT.fv, List.mem_append]
          exact Or.inr hv) hlookup
      obtain ⟨denFAlt, denXAlt, hden_fEnc_alt,
          hden_xEnc_alt, denPairAlt_eq⟩ :=
        denote_pair_inv_app hcov_pair_alt hden_pair_alt
      rw [denPairAlt_eq] at hdenPairAlt_type pair_alt_rel
      rcases denFAlt with ⟨Fenc_alt, tauF_alt, hFenc_alt⟩
      rcases denXAlt with ⟨Xenc_alt, tauX_alt, hXenc_alt⟩
      dsimp at hdenPairAlt_type
      injection hdenPairAlt_type with htauF_alt htauX_alt
      subst tauF_alt
      subst tauX_alt
      have pair_alt_rel' : RDomCastSupported
          (⟨F_alt.pair X_alt,
            BType.set (gamma ×ᴮ alpha) ×ᴮ gamma,
            ZFSet.pair_mem_prod.mpr ⟨hF_alt, hX_alt⟩⟩ : B.Dom)
          (⟨Fenc_alt.pair Xenc_alt,
            SMTType.pair sigmaF sigmaX,
            ZFSet.pair_mem_prod.mpr
              ⟨hFenc_alt, hXenc_alt⟩⟩ : SMT.Dom) := by
        simpa only [proof_irrel_heq] using pair_alt_rel
      obtain ⟨F_alt_rel, X_alt_rel⟩ :=
        RDomCastSupported.of_pair pair_alt_rel'
      have target_respects_fEnc_alt_A :
          SMT.RenamingContext.RespectsTypeContextOnFV
            Thetap_alt StA.types fEnc :=
        target_respects_fEnc_alt.of_extends
          (SMT.RenamingContext.extends_refl Thetap_alt)
          types_sub_app typ_fEnc
      have target_respects_xEnc_alt_A :
          SMT.RenamingContext.RespectsTypeContextOnFV
            Thetap_alt StA.types xEnc :=
        target_respects_xEnc_alt.of_extends
          (SMT.RenamingContext.extends_refl Thetap_alt)
          types_sub_app typ_xEnc
      have Thetap_alt_dom_A :
          ∀ v, Thetap_alt v ≠ none → v ∈ StA.types :=
        fun v hv => AList.mem_of_subset types_sub_app
          (Thetap_alt_dom v hv)
      obtain ⟨good_alt, _guarded_alt⟩ :=
        app_sem StA.types (fun _ h => h) Thetap_alt
          hcov_fEnc_alt hcov_xEnc_alt Thetap_alt_none
          target_respects_fEnc_alt_A target_respects_xEnc_alt_A
          Thetap_alt_dom_A
          F_alt X_alt T_alt hF_alt hX_alt hT_alt
          hfun_alt hdom_alt hresult_alt
          (⟨Fenc_alt, sigmaF, hFenc_alt⟩ : SMT.Dom)
          (⟨Xenc_alt, sigmaX, hXenc_alt⟩ : SMT.Dom)
          hden_fEnc_alt hden_xEnc_alt rfl rfl F_alt_rel X_alt_rel
      obtain ⟨ThetaA_alt, hcov_app_alt, denA_alt,
          ThetaA_alt_ext, ThetaA_alt_none,
          target_respects_app_alt, ThetaA_alt_dom,
          _specs_A_alt, hden_app_alt, hdenA_alt_type,
          result_alt_rel⟩ := good_alt
      have ThetaA_alt_ext0 := SMT.RenamingContext.extends_trans
        ThetaA_alt_ext Thetap_alt_ext
      refine ⟨ThetaA_alt, hcov_app_alt, denA_alt,
        ThetaA_alt_ext0, related_alt.of_extends ThetaA_alt_ext0,
        ThetaA_alt_none, ?_, target_respects_app_alt,
        ThetaA_alt_dom, hden_app_alt, hdenA_alt_type,
        result_alt_rel⟩
      exact respects_alt.of_extends ThetaA_alt_ext0 types_sub0
        (fun _ h => h) fv_in_Lambda
