import SMT.Reasoning.Basic.EncodeTermRepresentedArith
import SMT.Reasoning.Basic.EncodeTermRepresentedBinders
import SMT.Reasoning.Basic.EncodeTermCorrectInter

open Std.Do B SMT ZFSet

/-! # Representation-aware heterogeneous intersection -/

theorem relation_inter_mem.{u} {α β : BType} {F G : ZFSet.{u}}
    (hF : F ∈ ⟦BType.set (α ×ᴮ β)⟧ᶻ)
    (hG : G ∈ ⟦BType.set (α ×ᴮ β)⟧ᶻ) :
    F ∩ G ∈ ⟦BType.set (α ×ᴮ β)⟧ᶻ := by
  rw [BType.toZFSet, ZFSet.mem_powerset] at hF hG ⊢
  intro x hx
  rw [ZFSet.mem_inter] at hx
  exact hF hx.1

theorem set_inter_mem.{u} {τ : BType} {F G : ZFSet.{u}}
    (hF : F ∈ ⟦BType.set τ⟧ᶻ)
    (hG : G ∈ ⟦BType.set τ⟧ᶻ) :
    F ∩ G ∈ ⟦BType.set τ⟧ᶻ := by
  rw [BType.toZFSet, ZFSet.mem_powerset] at hF hG ⊢
  intro x hx
  rw [ZFSet.mem_inter] at hx
  exact hF hx.1

open Classical in
/-- Pointwise Boolean intersection preserves a shared supported element
representation, including when that representation itself contains encoded
sets. -/
theorem represented_setPred_inter_of_pointwise.{u}
    {τ : BType} {ρ : SMTType}
    (hρ : BType.SupportedSMT τ ρ)
    {F G Fenc Genc U : ZFSet.{u}}
    (hF : F ∈ ⟦BType.set τ⟧ᶻ)
    (hG : G ∈ ⟦BType.set τ⟧ᶻ)
    (hFenc : Fenc ∈ ⟦SMTType.fun ρ SMTType.bool⟧ᶻ)
    (hGenc : Genc ∈ ⟦SMTType.fun ρ SMTType.bool⟧ᶻ)
    (hU : U ∈ ⟦SMTType.fun ρ SMTType.bool⟧ᶻ)
    (F_rel : RDomCastSupported
      (⟨F, BType.set τ, hF⟩ : B.Dom)
      (⟨Fenc, SMTType.fun ρ SMTType.bool, hFenc⟩ : SMT.Dom))
    (G_rel : RDomCastSupported
      (⟨G, BType.set τ, hG⟩ : B.Dom)
      (⟨Genc, SMTType.fun ρ SMTType.bool, hGenc⟩ : SMT.Dom))
    (hpoint : ∀ (y : ZFSet.{u}) (hy : y ∈ ⟦ρ⟧ᶻ),
      y.pair ZFSet.zftrue ∈ U ↔
        y.pair ZFSet.zftrue ∈ Fenc ∧
          y.pair ZFSet.zftrue ∈ Genc) :
    RDomCastSupported
      (⟨F ∩ G, BType.set τ, set_inter_mem hF hG⟩ : B.Dom)
      (⟨U, SMTType.fun ρ SMTType.bool, hU⟩ : SMT.Dom) := by
  have hInterSub : F ∩ G ⊆ ⟦τ⟧ᶻ := by
    simpa [BType.toZFSet] using
      ZFSet.mem_powerset.mp (set_inter_mem hF hG)
  have hFfunc : ⟦ρ⟧ᶻ.IsFunc ZFSet.𝔹 Fenc := by
    simpa [SMTType.toZFSet] using hFenc
  have hGfunc : ⟦ρ⟧ᶻ.IsFunc ZFSet.𝔹 Genc := by
    simpa [SMTType.toZFSet] using hGenc
  have hUfunc : ⟦ρ⟧ᶻ.IsFunc ZFSet.𝔹 U := by
    simpa [SMTType.toZFSet] using hU
  apply RDomCastSupported.setPred_of_pointwise
    hρ hInterSub hU hUfunc
  · intro y hy hUtrue
    have hpairU := ZFSet.fapply.def
      (ZFSet.is_func_is_pfunc hUfunc)
      (by rw [ZFSet.is_func_dom_eq hUfunc]; exact hy)
    rw [hUtrue] at hpairU
    obtain ⟨hpairF, hpairG⟩ := (hpoint y hy).mp hpairU
    have hFtrue := congrArg Subtype.val
      (ZFSet.fapply.of_pair
        (ZFSet.is_func_is_pfunc hFfunc) hpairF)
    have hGtrue := congrArg Subtype.val
      (ZFSet.fapply.of_pair
        (ZFSet.is_func_is_pfunc hGfunc) hpairG)
    obtain ⟨xF, hxF, xFrel⟩ :=
      F_rel.setPred_target_of_true hy hFtrue
    obtain ⟨xG, hxG, xGrel⟩ :=
      G_rel.setPred_target_of_true hy hGtrue
    have hxFG : xF = xG :=
      (RDomCastSupported.cast_eq_iff xFrel xGrel
        (castPath.reflexive ρ)).mp
        (castZF_apply_reflexive ρ hy)
    subst xG
    refine ⟨xF, ?_, ?_⟩
    · rw [ZFSet.mem_inter]
      exact ⟨hxF, hxG⟩
    · simpa only [proof_irrel_heq] using xFrel
  · intro x hxInter
    rw [ZFSet.mem_inter] at hxInter
    obtain ⟨yF, hyF, xFrel⟩ :=
      F_rel.setPred_member_preimage hxInter.1
    obtain ⟨yG, hyG, xGrel⟩ :=
      G_rel.setPred_member_preimage hxInter.2
    have hyFG : yF = yG := by
      have hcast :=
        (RDomCastSupported.cast_eq_iff xFrel xGrel
          (castPath.reflexive ρ)).mpr rfl
      simpa only [castZF_apply_reflexive ρ hyF] using hcast
    subst yG
    have hFtrue :=
      (RDomCastSupported.setPred_fapply_eq_zftrue_iff
        xFrel.toRDomCast F_rel).mpr hxInter.1
    have hGtrue :=
      (RDomCastSupported.setPred_fapply_eq_zftrue_iff
        xGrel.toRDomCast G_rel).mpr hxInter.2
    have hpairF := ZFSet.fapply.def
      (ZFSet.is_func_is_pfunc hFfunc)
      (by rw [ZFSet.is_func_dom_eq hFfunc]; exact hyF)
    have hpairG := ZFSet.fapply.def
      (ZFSet.is_func_is_pfunc hGfunc)
      (by rw [ZFSet.is_func_dom_eq hGfunc]; exact hyF)
    rw [hFtrue] at hpairF
    rw [hGtrue] at hpairG
    have hpairU := (hpoint yF hyF).mpr ⟨hpairF, hpairG⟩
    have hUtrue := congrArg Subtype.val
      (ZFSet.fapply.of_pair
        (ZFSet.is_func_is_pfunc hUfunc) hpairU)
    refine ⟨yF, hyF, ?_, hUtrue⟩
    simpa only [proof_irrel_heq] using xFrel

private theorem erase_insert_self_rep_inter {a : SMT.𝒱} {τ : SMTType}
    {s : SMT.TypeContext} (ha : a ∉ s) : (s.insert a τ).erase a = s := by
  apply AList.ext
  show List.kerase a (AList.insert a τ s).entries = s.entries
  rw [AList.entries_insert_of_notMem ha]
  exact List.kerase_cons_eq rfl

/- The direct characteristic-predicate branch is Δ-universal.  This is the
contract used by the full intersection constructor both for its current denotation
and for the alternative-valuation totality clause. -/
set_option maxHeartbeats 1600000 in
@[spec]
theorem castInter_direct_rep_spec.{u}
    (τ : BType) (ρ : SMTType) (hρ : BType.SupportedSMT τ ρ)
    {S T : SMT.Term}
    {Λ : SMT.TypeContext} {n : ℕ} {used : List SMT.𝒱}
    (typ_S : Λ ⊢ˢ S : SMTType.fun ρ SMTType.bool)
    (typ_T : Λ ⊢ˢ T : SMTType.fun ρ SMTType.bool)
    (bv_S_used : ∀ v ∈ SMT.bv S, v ∈ used)
    (bv_T_used : ∀ v ∈ SMT.bv T, v ∈ used) :
    ⦃ fun ⟨E, Λ'⟩ =>
      ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ Λ.keys ⊆ E.usedVars ∧
        E.usedVars = used⌝ ⦄
    castInter
      ⟨S, SMTType.fun ρ SMTType.bool⟩
      ⟨T, SMTType.fun ρ SMTType.bool⟩
    ⦃ ⇓? ⟨t, σ⟩ ⟨E', Γ'⟩ =>
      ⌜used ⊆ E'.usedVars ∧
        Λ ⊆ Γ' ∧
        Γ'.keys ⊆ E'.usedVars ∧
        σ = SMTType.fun ρ SMTType.bool ∧
        Γ' ⊢ˢ t : SMTType.fun ρ SMTType.bool ∧
        (∀ v ∈ used, v ∉ Λ → v ∉ Γ') ∧
        ∀ (Θ : SMT.RenamingContext.Context.{u})
          (hS : RenamingContext.CoversFV Θ S)
          (hT : RenamingContext.CoversFV Θ T),
          (∀ v ∉ used, Θ v = none) →
          SMT.RenamingContext.RespectsTypeContextOnFV Θ Λ S →
          SMT.RenamingContext.RespectsTypeContextOnFV Θ Λ T →
          (∀ v, Θ v ≠ none → v ∈ Λ) →
          ∀ (F G : ZFSet.{u})
            (hF : F ∈ ⟦BType.set τ⟧ᶻ)
            (hG : G ∈ ⟦BType.set τ⟧ᶻ)
            (denS denT : SMT.Dom.{u}),
            ⟦S.abstract Θ hS⟧ˢ = some denS →
            ⟦T.abstract Θ hT⟧ˢ = some denT →
            RDomCast
              (⟨F, BType.set τ, hF⟩ : B.Dom) denS →
            RDomCast
              (⟨G, BType.set τ, hG⟩ : B.Dom) denT →
            ∃ (Θ' : SMT.RenamingContext.Context.{u})
              (hcov : RenamingContext.CoversFV Θ' t)
              (denU : SMT.Dom.{u}),
              RenamingContext.Extends Θ' Θ ∧
              (∀ v ∉ E'.usedVars, Θ' v = none) ∧
              SMT.RenamingContext.RespectsTypeContextOnFV Θ' Γ' t ∧
              (∀ v, Θ' v ≠ none → v ∈ Γ') ∧
              ⟦t.abstract Θ' hcov⟧ˢ = some denU ∧
              denU.snd.fst = σ ∧
              RDomCastSupported
                (⟨F ∩ G, BType.set τ, set_inter_mem hF hG⟩ : B.Dom)
                denU⌝ ⦄ := by
  have hcastInter :
      castInter
        (S, SMTType.fun ρ SMTType.bool)
        (T, SMTType.fun ρ SMTType.bool) = do
        let z ← SMT.freshVar ρ "inter!"
        SMT.eraseFromContext z
        return (.lambda [z] [ρ]
          (.and (.app S (.var z)) (.app T (.var z))),
          SMTType.fun ρ SMTType.bool) := by
    unfold castInter
    simp
  rw [hcastInter]
  mintro pre ∀St₀
  mpure pre
  obtain ⟨rfl, rfl, St₀_sub, rfl⟩ := pre
  mspec SMT.freshVar_spec
  next z =>
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨St₁_types_eq, z_fresh, St₁_fvc, St₁_used_eq,
      z_not_used⟩ := pre
    mspec SMT.eraseFromContext_spec
    mrename_i preE
    mintro ∀StE
    mpure preE
    obtain ⟨StE_types_eq, StE_fvc, StE_used_eq⟩ := preE
    have StE_types_eq' : StE.types = St₀.types := by
      rw [StE_types_eq, St₁_types_eq,
        erase_insert_self_rep_inter z_fresh]
    mspec Std.Do.Spec.pure
    mpure_intro
    and_intros
    · rw [StE_used_eq, St₁_used_eq]
      exact List.subset_cons_of_subset z fun _ => id
    · rw [StE_types_eq']
    · intro v hv
      rw [StE_types_eq'] at hv
      rw [StE_used_eq, St₁_used_eq]
      exact List.mem_cons_of_mem z (St₀_sub hv)
    · trivial
    · rw [StE_types_eq']
      have z_not_bv_S : z ∉ SMT.bv S :=
        fun hz => z_not_used (bv_S_used z hz)
      have z_not_bv_T : z ∉ SMT.bv T :=
        fun hz => z_not_used (bv_T_used z hz)
      refine SMT.Typing.lambda St₀.types [z] [ρ]
        _ SMTType.bool ?_ ?_ (by simp) rfl ?_
      · intro v hv
        rw [List.mem_singleton] at hv
        simpa [hv] using z_fresh
      · intro v hv
        rw [List.mem_singleton] at hv
        subst v
        simp only [SMT.bv, List.append_nil, List.mem_append]
        push_neg
        exact ⟨z_not_bv_S, z_not_bv_T⟩
      · have hupdate :
            TypeContext.update St₀.types [z] [ρ] rfl =
              St₀.types.insert z ρ := by
          simp only [TypeContext.update, List.length_cons, List.length_nil,
            zero_add, Nat.reduceAdd, Fin.cast_eq_self, Fin.getElem_fin,
            Fin.val_eq_zero, List.getElem_cons_zero, Fin.foldl_succ,
            Fin.foldl_zero]
        rw [hupdate]
        apply SMT.Typing.and
        · apply SMT.Typing.app
          · exact SMT.Typing.weakening
              (TypeContext.entries_subset_insert_of_notMem z_fresh)
              typ_S
              (SMT.Typing.bv_notMem_insert_of_fresh typ_S z_not_bv_S)
          · exact SMT.Typing.var _ z _ (AList.lookup_insert St₀.types)
        · apply SMT.Typing.app
          · exact SMT.Typing.weakening
              (TypeContext.entries_subset_insert_of_notMem z_fresh)
              typ_T
              (SMT.Typing.bv_notMem_insert_of_fresh typ_T z_not_bv_T)
          · exact SMT.Typing.var _ z _ (AList.lookup_insert St₀.types)
    · intro v hv hv_not
      rw [StE_types_eq']
      exact hv_not
    · intro Θ hS hT Θ_none respects_S respects_T Θ_dom
        F G hF hG denS denT hdenS hdenT F_rel G_rel
      have z_not_fv_S : z ∉ SMT.fv S :=
        funNotMemFvOfNotMemContext typ_S z_fresh
      have z_not_fv_T : z ∉ SMT.fv T :=
        funNotMemFvOfNotMemContext typ_T z_fresh
      have hcov_out : RenamingContext.CoversFV Θ
          (.lambda [z] [ρ]
            (.and (.app S (.var z)) (.app T (.var z)))) := by
        intro v hv
        simp only [SMT.fv, List.removeAll, List.mem_filter,
          List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
        obtain ⟨hv_body, hv_ne_z⟩ := hv
        simp only [List.elem_eq_contains, List.contains_eq_mem,
          List.mem_cons, List.not_mem_nil, or_false, Bool.not_eq_true',
          decide_eq_false_iff_not] at hv_ne_z
        rcases hv_body with ((hv_S | rfl) | (hv_T | rfl))
        · exact hS v hv_S
        · exact absurd rfl hv_ne_z
        · exact hT v hv_T
        · exact absurd rfl hv_ne_z
      have target_respects_out :
          SMT.RenamingContext.RespectsTypeContextOnFV Θ StE.types
            (.lambda [z] [ρ]
              (.and (.app S (.var z)) (.app T (.var z)))) := by
        rw [StE_types_eq']
        intro v σ hv hlookup
        simp only [SMT.fv, List.removeAll, List.mem_filter,
          List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
        obtain ⟨hv_body, hv_ne_z⟩ := hv
        simp only [List.elem_eq_contains, List.contains_eq_mem,
          List.mem_cons, List.not_mem_nil, or_false, Bool.not_eq_true',
          decide_eq_false_iff_not] at hv_ne_z
        rcases hv_body with ((hv_S | rfl) | (hv_T | rfl))
        · exact respects_S hv_S hlookup
        · exact absurd rfl hv_ne_z
        · exact respects_T hv_T hlookup
        · exact absurd rfl hv_ne_z
      have denS_type := SMT.RenamingContext.denote_type_of_typing_fv
        typ_S respects_S hS hdenS
      have denT_type := SMT.RenamingContext.denote_type_of_typing_fv
        typ_T respects_T hT hdenT
      obtain ⟨denU, hdenU, denU_type, _hretU, hpointU⟩ :=
        castInter_denotation_direct hS hT hdenS hdenT
          denS_type denT_type z_not_fv_S z_not_fv_T hcov_out
      refine ⟨Θ, hcov_out, denU, RenamingContext.extends_refl Θ,
        ?_, target_respects_out, ?_, hdenU, ?_, ?_⟩
      · intro v hv
        apply Θ_none
        intro hv_used
        apply hv
        rw [StE_used_eq, St₁_used_eq]
        exact List.mem_cons_of_mem z hv_used
      · intro v hv
        rw [StE_types_eq']
        exact Θ_dom v hv
      · simpa using denU_type
      · rcases denS with ⟨Fenc, σS, hFenc⟩
        rcases denT with ⟨Genc, σT, hGenc⟩
        rcases denU with ⟨U, σU, hU⟩
        dsimp at denS_type denT_type denU_type
        subst σS
        subst σT
        subst σU
        let setSupported : BType.SupportedSMT (BType.set τ)
            (SMTType.fun ρ SMTType.bool) := .setPred hρ
        have F_supported : RDomCastSupported
            (⟨F, BType.set τ, hF⟩ : B.Dom)
            (⟨Fenc, SMTType.fun ρ SMTType.bool, hFenc⟩ : SMT.Dom) :=
          ⟨RDomCast.toRDomCastAdmissible_of_supported F_rel setSupported,
            setSupported⟩
        have G_supported : RDomCastSupported
            (⟨G, BType.set τ, hG⟩ : B.Dom)
            (⟨Genc, SMTType.fun ρ SMTType.bool, hGenc⟩ : SMT.Dom) :=
          ⟨RDomCast.toRDomCastAdmissible_of_supported G_rel setSupported,
            setSupported⟩
        exact represented_setPred_inter_of_pointwise hρ hF hG
          hFenc hGenc hU F_supported G_supported hpointU

private theorem castInter_chpred_via_direct
    {rho sigma : SMTType} (S T : SMT.Term) (p : rho ~> sigma) :
    castInter.chpred S T p = (do
      let ⟨S!, S!_spec⟩ ←
        loosenAux_prf "inter!" (castPath.chpred p) S
      declareConst S! (SMTType.fun sigma SMTType.bool)
      addSpec S! S!_spec
      castInter
        ⟨SMT.Term.var S!, SMTType.fun sigma SMTType.bool⟩
        ⟨T, SMTType.fun sigma SMTType.bool⟩) := by
  unfold castInter.chpred castInter
  simp

/-- Semantic core of Gate B.  The helper produced by `loosenAux_prf` denotes
the graph cast of the option-valued function, and the lambda returned by
the graph branch of `castInter` therefore retracts to the intersection of the two source
relations. -/
theorem castInter_graph_denotation.{u}
    (α β : BType) {σA τA σB τB : SMTType}
    (hsAα : BType.SupportedSMT α σA)
    (hsAβ : BType.SupportedSMT β τA)
    (hsBα : BType.SupportedSMT α σB)
    (hsBβ : BType.SupportedSMT β τB)
    {F G : ZFSet.{u}}
    (hF : F ∈ ⟦BType.set (α ×ᴮ β)⟧ᶻ)
    (hG : G ∈ ⟦BType.set (α ×ᴮ β)⟧ᶻ)
    {S! z : SMT.𝒱} {T : SMT.Term}
    {«Δ» : SMT.RenamingContext.Context.{u}}
    {denS denS! denT : SMT.Dom.{u}}
    (denS_type : denS.snd.fst =
      SMTType.fun σA (SMTType.option τA))
    (denS!_type : denS!.snd.fst =
      SMTType.fun (SMTType.pair σB τB) SMTType.bool)
    (denT_type : denT.snd.fst =
      SMTType.fun (SMTType.pair σB τB) SMTType.bool)
    (F_rel : RDomCastSupported
      (⟨F, BType.set (α ×ᴮ β), hF⟩ : B.Dom) denS)
    (G_rel : RDomCastSupported
      (⟨G, BType.set (α ×ᴮ β), hG⟩ : B.Dom) denT)
    (cα : σA ~> σB) (cβ : τA ~> τB)
    (cast_pair : denS.fst.pair denS!.fst ∈
      (castZF_of_path (castPath.graph
        cα cβ)).1)
    (hS! : RenamingContext.CoversFV «Δ» (SMT.Term.var S!))
    (hT : RenamingContext.CoversFV «Δ» T)
    (h_den_S! : ⟦(SMT.Term.var S!).abstract «Δ» hS!⟧ˢ = some denS!)
    (h_den_T : ⟦T.abstract «Δ» hT⟧ˢ = some denT)
    (z_not_fv_S! : z ∉ SMT.fv (SMT.Term.var S!))
    (z_not_fv_T : z ∉ SMT.fv T)
    (hcov : RenamingContext.CoversFV «Δ»
      (.lambda [z] [SMTType.pair σB τB]
        (.and (.app (.var S!) (.var z)) (.app T (.var z))))) :
    ∃ denU : SMT.Dom.{u},
      ⟦(SMT.Term.lambda [z] [SMTType.pair σB τB]
        (.and (.app (.var S!) (.var z)) (.app T (.var z)))).abstract
          «Δ» hcov⟧ˢ = some denU ∧
      RDomCastSupported
        (⟨F ∩ G, BType.set (α ×ᴮ β), relation_inter_mem hF hG⟩ : B.Dom)
        denU := by
  rcases denS with ⟨Sval, σS, hSval⟩
  rcases denS! with ⟨S!val, σS!, hS!val⟩
  rcases denT with ⟨Tval, σT, hTval⟩
  dsimp at denS_type denS!_type denT_type
  subst σS
  subst σS!
  subst σT
  have hgraph :
      castZF_apply (castPath.graph cα cβ) Sval = S!val :=
    castZF_apply_eq_of_pair
      (castPath.graph cα cβ) hSval cast_pair
  have Fgraph_rel :=
    RDomCastSupported.optionFun_graph_cast_supported
      hsAα hsAβ hsBα hsBβ F_rel cα cβ
      (fun relx rely => RDomCastSupported.cast_eq_iff relx rely
        (castPath.pair cα cβ))
  have hgraph_dom :
      (⟨castZF_apply (castPath.graph cα cβ) Sval,
        SMTType.fun (SMTType.pair σB τB) SMTType.bool,
        castZF_apply_mem (castPath.graph cα cβ) hSval⟩ : SMT.Dom) =
      (⟨S!val, SMTType.fun (SMTType.pair σB τB) SMTType.bool,
        hS!val⟩ : SMT.Dom) :=
    SMTDom_eq_of_type_value rfl hgraph
  rw [hgraph_dom] at Fgraph_rel
  obtain ⟨denU, hdenU, denU_type, _hU_retract, hpointU⟩ :=
    castInter_denotation_direct hS! hT h_den_S! h_den_T rfl rfl
      z_not_fv_S! z_not_fv_T hcov
  rcases denU with ⟨Uval, σU, hUval⟩
  dsimp at denU_type
  subst σU
  refine ⟨⟨Uval,
      SMTType.fun (SMTType.pair σB τB) SMTType.bool,
      hUval⟩, hdenU, ?_⟩
  simpa only [proof_irrel_heq] using
    (represented_setPred_inter_of_pointwise (.prod hsBα hsBβ)
      hF hG hS!val hTval hUval Fgraph_rel G_rel hpointU)

/-- If two option-valued function terms denote supported representations of
relations at the same endpoint types, the pairwise equality lambda emitted by
`castInter.fun` represents their source intersection. -/
theorem castInter_option_denotation.{u}
    (α β : BType) {sigma tau : SMTType}
    (hsα : BType.SupportedSMT α sigma)
    (hsβ : BType.SupportedSMT β tau)
    {F G : ZFSet.{u}}
    (hF : F ∈ ⟦BType.set (α ×ᴮ β)⟧ᶻ)
    (hG : G ∈ ⟦BType.set (α ×ᴮ β)⟧ᶻ)
    {f g : SMT.Term} {p : SMT.𝒱}
    {Gamma : SMT.TypeContext}
    {Delta : SMT.RenamingContext.Context.{u}}
    {denF denG : SMT.Dom.{u}}
    (denF_type : denF.snd.fst =
      SMTType.fun sigma (SMTType.option tau))
    (denG_type : denG.snd.fst =
      SMTType.fun sigma (SMTType.option tau))
    (F_rel : RDomCastSupported
      (⟨F, BType.set (α ×ᴮ β), hF⟩ : B.Dom) denF)
    (G_rel : RDomCastSupported
      (⟨G, BType.set (α ×ᴮ β), hG⟩ : B.Dom) denG)
    (hcov_f : RenamingContext.CoversFV Delta f)
    (hcov_g : RenamingContext.CoversFV Delta g)
    (hden_f : ⟦f.abstract Delta hcov_f⟧ˢ = some denF)
    (hden_g : ⟦g.abstract Delta hcov_g⟧ˢ = some denG)
    (p_not_fv_f : p ∉ SMT.fv f)
    (p_not_fv_g : p ∉ SMT.fv g)
    (typ_out : Gamma ⊢ˢ
      SMT.Term.lambda [p] [SMTType.pair sigma tau]
        (.and
          (.eq (.app f (.fst (.var p)))
            (.some (.snd (.var p))))
          (.eq (.app g (.fst (.var p)))
            (.some (.snd (.var p))))) :
      SMTType.fun (SMTType.pair sigma tau) SMTType.bool)
    (respects_out :
      SMT.RenamingContext.RespectsTypeContextOnFV Delta Gamma
        (.lambda [p] [SMTType.pair sigma tau]
          (.and
            (.eq (.app f (.fst (.var p)))
              (.some (.snd (.var p))))
            (.eq (.app g (.fst (.var p)))
              (.some (.snd (.var p)))))))
    (hcov_out : RenamingContext.CoversFV Delta
      (SMT.Term.lambda [p] [SMTType.pair sigma tau]
        (.and
          (.eq (.app f (.fst (.var p)))
            (.some (.snd (.var p))))
          (.eq (.app g (.fst (.var p)))
            (.some (.snd (.var p))))))) :
    ∃ denU : SMT.Dom.{u},
      ⟦(SMT.Term.lambda [p] [SMTType.pair sigma tau]
        (.and
          (.eq (.app f (.fst (.var p)))
            (.some (.snd (.var p))))
          (.eq (.app g (.fst (.var p)))
            (.some (.snd (.var p)))))).abstract Delta hcov_out⟧ˢ =
          some denU ∧
      RDomCastSupported
        (⟨F ∩ G, BType.set (α ×ᴮ β),
          relation_inter_mem hF hG⟩ : B.Dom) denU := by
  rcases denF with ⟨Fenc, sigmaF, hFenc⟩
  rcases denG with ⟨Genc, sigmaG, hGenc⟩
  dsimp at denF_type denG_type hden_f hden_g ⊢
  subst sigmaF
  subst sigmaG
  obtain ⟨denU, hdenU, denU_type⟩ :=
    SMT.RenamingContext.denote_exists_of_typing_fv
      typ_out respects_out hcov_out
  rcases denU with ⟨U, sigmaU, hU⟩
  dsimp at denU_type hdenU ⊢
  subst sigmaU
  let rSigma := castPath.reflexive sigma
  let rTau := castPath.reflexive tau
  have Fgraph_rel₀ :=
    RDomCastSupported.optionFun_graph_cast_supported
      hsα hsβ hsα hsβ F_rel rSigma rTau
        (fun relx rely => RDomCastSupported.cast_eq_iff relx rely
          (castPath.pair rSigma rTau))
  have Ggraph_rel₀ :=
    RDomCastSupported.optionFun_graph_cast_supported
      hsα hsβ hsα hsβ G_rel rSigma rTau
        (fun relx rely => RDomCastSupported.cast_eq_iff relx rely
          (castPath.pair rSigma rTau))
  have Fgraph_rel : RDomCastSupported
      (⟨F, BType.set (α ×ᴮ β), hF⟩ : B.Dom)
      (⟨optionGraph sigma tau Fenc,
        SMTType.fun (SMTType.pair sigma tau) SMTType.bool,
        optionGraph_mem sigma tau hFenc⟩ : SMT.Dom) := by
    simpa only [optionGraph, rSigma, rTau, proof_irrel_heq] using
      Fgraph_rel₀
  have Ggraph_rel : RDomCastSupported
      (⟨G, BType.set (α ×ᴮ β), hG⟩ : B.Dom)
      (⟨optionGraph sigma tau Genc,
        SMTType.fun (SMTType.pair sigma tau) SMTType.bool,
        optionGraph_mem sigma tau hGenc⟩ : SMT.Dom) := by
    simpa only [optionGraph, rSigma, rTau, proof_irrel_heq] using
      Ggraph_rel₀
  have hUfunc : ⟦SMTType.pair sigma tau⟧ᶻ.IsFunc ZFSet.𝔹 U := by
    simpa [SMTType.toZFSet] using hU
  have hpoint : ∀ (w : ZFSet.{u})
      (hw : w ∈ ⟦SMTType.pair sigma tau⟧ᶻ),
      w.pair ZFSet.zftrue ∈ U ↔
        w.pair ZFSet.zftrue ∈ optionGraph sigma tau Fenc ∧
        w.pair ZFSet.zftrue ∈ optionGraph sigma tau Genc := by
    intro w hw
    obtain ⟨a, ha, b, hb, rfl⟩ := ZFSet.mem_prod.mp hw
    obtain ⟨hcov_guardF, denGuardF, hden_guardF,
        denGuardF_type, hguardF⟩ :=
      option_pair_guard_denotation hcov_f hden_f rfl
        p_not_fv_f a b ha hb
    obtain ⟨hcov_guardG, denGuardG, hden_guardG,
        denGuardG_type, hguardG⟩ :=
      option_pair_guard_denotation hcov_g hden_g rfl
        p_not_fv_g a b ha hb
    let W : SMT.Dom.{u} :=
      ⟨a.pair b, SMTType.pair sigma tau,
        ZFSet.pair_mem_prod.mpr ⟨ha, hb⟩⟩
    let DeltaP := Function.update Delta p (some W)
    let guardF := SMT.Term.eq
      (.app f (.fst (.var p))) (.some (.snd (.var p)))
    let guardG := SMT.Term.eq
      (.app g (.fst (.var p))) (.some (.snd (.var p)))
    let body := SMT.Term.and guardF guardG
    have hcov_body : RenamingContext.CoversFV DeltaP body := by
      intro v hv
      simp only [body, SMT.fv, List.mem_append] at hv
      exact hv.elim (hcov_guardF v) (hcov_guardG v)
    obtain ⟨denBody, hden_body_raw, denBody_type, hbody⟩ :=
      denote_and_true_iff hden_guardF denGuardF_type
        hden_guardG denGuardG_type
    have hden_body : ⟦body.abstract DeltaP hcov_body⟧ˢ =
        some denBody := by
      dsimp only [body, guardF, guardG]
      rw [SMT.Term.abstract]
      simpa only [proof_irrel_heq] using hden_body_raw
    have happly := single_lambda_fapply_eq_body
      (alpha := SMTType.pair sigma tau) (beta := SMTType.bool)
      hcov_out hdenU hUfunc rfl
      (ZFSet.pair_mem_prod.mpr ⟨ha, hb⟩)
      hcov_body hden_body
    have hUpair := ZFSet.fapply_eq_zftrue_iff_pair hUfunc
      (ZFSet.pair_mem_prod.mpr ⟨ha, hb⟩)
    calc
      (a.pair b).pair ZFSet.zftrue ∈ U ↔
          (ZFSet.fapply U (ZFSet.is_func_is_pfunc hUfunc)
            ⟨a.pair b, by
              rw [ZFSet.is_func_dom_eq hUfunc]
              exact ZFSet.pair_mem_prod.mpr ⟨ha, hb⟩⟩).val =
              ZFSet.zftrue := hUpair.symm
      _ ↔ denBody.fst = ZFSet.zftrue := by rw [happly]
      _ ↔ denGuardF.fst = ZFSet.zftrue ∧
          denGuardG.fst = ZFSet.zftrue := hbody
      _ ↔ (a.pair b).pair ZFSet.zftrue ∈
            optionGraph sigma tau Fenc ∧
          (a.pair b).pair ZFSet.zftrue ∈
            optionGraph sigma tau Genc := and_congr hguardF hguardG
  refine ⟨⟨U, SMTType.fun (SMTType.pair sigma tau) SMTType.bool,
      hU⟩, hdenU, ?_⟩
  simpa only [proof_irrel_heq] using
    (represented_setPred_inter_of_pointwise (.prod hsα hsβ)
      hF hG (optionGraph_mem sigma tau hFenc)
      (optionGraph_mem sigma tau hGenc) hU
      Fgraph_rel Ggraph_rel hpoint)

/- Gate B: the real heterogeneous `castInter` branch, including
`loosenAux_prf`, declaration and assertion of the helper graph, and the
lambda returned by the encoder.  The final denotation represents the source
intersection even though the left operand starts as an option-valued function. -/
set_option maxHeartbeats 1200000 in
@[spec]
theorem castInter_graph_rep_spec.{u}
    (α β : BType) {σA τA σB τB : SMTType}
    (hsAα : BType.SupportedSMT α σA)
    (hsAβ : BType.SupportedSMT β τA)
    (hsBα : BType.SupportedSMT α σB)
    (hsBβ : BType.SupportedSMT β τB)
    (hα : σA ⊑ σB) (hβ : τA ⊑ τB)
    {S T : SMT.Term}
    {Λ : SMT.TypeContext} {n : ℕ} {used : List SMT.𝒱}
    (typ_S : Λ ⊢ˢ S :
      SMTType.fun σA (SMTType.option τA))
    (typ_T : Λ ⊢ˢ T :
      SMTType.fun (SMTType.pair σB τB) SMTType.bool)
    (bv_S_used : ∀ v ∈ SMT.bv S, v ∈ used)
    (bv_T_used : ∀ v ∈ SMT.bv T, v ∈ used) :
    ⦃ fun ⟨E, Λ'⟩ =>
      ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ Λ.keys ⊆ E.usedVars ∧
        E.usedVars = used⌝ ⦄
    castInter
      ⟨S, SMTType.fun σA (SMTType.option τA)⟩
      ⟨T, SMTType.fun (SMTType.pair σB τB) SMTType.bool⟩
    ⦃ ⇓? ⟨t, σ⟩ ⟨E', Γ'⟩ =>
      ⌜used ⊆ E'.usedVars ∧
        Λ ⊆ Γ' ∧
        Γ'.keys ⊆ E'.usedVars ∧
        σ = SMTType.fun (SMTType.pair σB τB)
          SMTType.bool ∧
        Γ' ⊢ˢ t : SMTType.fun
          (SMTType.pair σB τB) SMTType.bool ∧
        (∀ v ∈ used, v ∉ Λ → v ∉ Γ') ∧
        ∀ (Θ : SMT.RenamingContext.Context.{u})
          (hS : RenamingContext.CoversFV Θ S)
          (hT : RenamingContext.CoversFV Θ T),
          (∀ v ∉ used, Θ v = none) →
          SMT.RenamingContext.RespectsTypeContextOnFV Θ Λ S →
          SMT.RenamingContext.RespectsTypeContextOnFV Θ Λ T →
          (∀ v, Θ v ≠ none → v ∈ Λ) →
          ∀ (F G : ZFSet.{u})
            (hF : F ∈ ⟦BType.set (α ×ᴮ β)⟧ᶻ)
            (hG : G ∈ ⟦BType.set (α ×ᴮ β)⟧ᶻ)
            (denS denT : SMT.Dom.{u}),
            ⟦S.abstract Θ hS⟧ˢ = some denS →
            ⟦T.abstract Θ hT⟧ˢ = some denT →
            RDomCast
              (⟨F, BType.set (α ×ᴮ β), hF⟩ : B.Dom) denS →
            RDomCast
              (⟨G, BType.set (α ×ᴮ β), hG⟩ : B.Dom) denT →
            ∃ (Θ' : SMT.RenamingContext.Context.{u})
              (hcov : RenamingContext.CoversFV Θ' t)
              (denU : SMT.Dom.{u}),
              RenamingContext.Extends Θ' Θ ∧
              (∀ v ∉ E'.usedVars, Θ' v = none) ∧
              SMT.RenamingContext.RespectsTypeContextOnFV Θ' Γ' t ∧
              (∀ v, Θ' v ≠ none → v ∈ Γ') ∧
              ⟦t.abstract Θ' hcov⟧ˢ = some denU ∧
              denU.snd.fst = σ ∧
              RDomCastSupported
                (⟨F ∩ G, BType.set (α ×ᴮ β),
                  relation_inter_mem hF hG⟩ : B.Dom) denU⌝ ⦄ := by
  have hcastInter :
      castInter
        (S, SMTType.fun σA (SMTType.option τA))
        (T, SMTType.fun (SMTType.pair σB τB) SMTType.bool) =
      castInter.graph S T hα.toCastPath hβ.toCastPath := by
    simp only [castInter]
    rw [dif_neg (by simp)]
    let hgraph :
        SMTType.fun σA (SMTType.option τA) ⊑
          SMTType.fun (SMTType.pair σB τB) SMTType.bool :=
      castable?.graph hα hβ
    rw [dif_pos hgraph]
    unfold castInterAux
    have hpath :
        hgraph.toCastPath = castPath.graph hα.toCastPath hβ.toCastPath := by
      calc
        hgraph.toCastPath = (castable?.graph hα hβ).toCastPath :=
          congrArg castable?.toCastPath (Subsingleton.elim _ _)
        _ = castPath.graph hα.toCastPath hβ.toCastPath :=
          SMTType.castable?_to_castPath_graph hα hβ
    rw [hpath]
  rw [hcastInter]
  unfold castInter.graph
  mintro pre ∀St₀
  mpure pre
  obtain ⟨rfl, rfl, St₀_sub, rfl⟩ := pre
  mspec loosenAux_prf_spec_univ (Λ := St₀.types)
    (n := St₀.env.freshvarsc)
    (used := St₀.env.usedVars) typ_S bv_S_used
    (castPath.graph hα.toCastPath hβ.toCastPath)
  next out =>
    obtain ⟨S!, S!_spec⟩ := out
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨_, St₁_types_sub, S!_fresh, S!_not_used, used_sub₁,
      St₁_keys_sub, preserves₁, _, _, typ_S!_St₁, _, _, adequacy⟩ := pre
    mspec SMT.declareConst_spec (v := S!)
      (τ := SMTType.fun (SMTType.pair σB τB) SMTType.bool)
      (decl := St₁.env.declarations) (as := St₁.env.asserts)
      (n := St₁.env.freshvarsc) (Γ := St₁.types)
      (used := St₁.env.usedVars)
    mrename_i pre
    mintro ∀St₂
    mpure pre
    obtain ⟨_, _, St₂_fvc_eq, St₂_used_eq, St₂_types_eq⟩ := pre
    mspec SMT.addSpec_spec (x! := S!) (x!_spec := S!_spec)
      (decl := St₂.env.declarations) (as := St₂.env.asserts)
      (n := St₂.env.freshvarsc) (Γ := St₂.types)
      (used := St₂.env.usedVars)
    mrename_i pre
    mintro ∀St₃
    mpure pre
    obtain ⟨_, _, St₃_fvc_eq, St₃_used_eq, St₃_types_eq⟩ := pre
    mspec SMT.freshVar_spec (Γ := St₃.types)
      (τ := SMTType.pair σB τB)
      (n := St₃.env.freshvarsc) (used := St₃.env.usedVars)
    next z =>
      mrename_i pre
      mintro ∀St₄
      mpure pre
      obtain ⟨St₄_types_eq, z_fresh, St₄_fvc_eq, St₄_used_eq,
        z_not_used⟩ := pre
      mspec SMT.eraseFromContext_spec (v := z) (Γ := St₄.types)
        (n := St₄.env.freshvarsc) (used := St₄.env.usedVars)
      mrename_i pre
      mintro ∀St₅
      mpure pre
      obtain ⟨St₅_types_eq, St₅_fvc_eq, St₅_used_eq⟩ := pre
      have St₅_types_eq' : St₅.types = St₃.types := by
        rw [St₅_types_eq, St₄_types_eq,
          erase_insert_self_rep_inter z_fresh]
      have typ_T_St₁ : St₁.types ⊢ˢ T :
          SMTType.fun (SMTType.pair σB τB) SMTType.bool :=
        SMT.Typing.weakening
          (h := fun v hv => St₁_types_sub
            (SMT.TypeContext.entries_subset_insert_of_notMem S!_fresh hv))
          typ_T
          (fun v hv => preserves₁ v (bv_T_used v hv)
            (SMT.Typing.bv_notMem_context typ_T v hv))
      have typ_T_St₃ : St₃.types ⊢ˢ T :
          SMTType.fun (SMTType.pair σB τB) SMTType.bool := by
        rwa [St₃_types_eq, St₂_types_eq]
      have typ_S!_St₃ : St₃.types ⊢ˢ SMT.Term.var S! :
          SMTType.fun (SMTType.pair σB τB) SMTType.bool := by
        rwa [St₃_types_eq, St₂_types_eq]
      have z_not_bv_T : z ∉ SMT.bv T := by
        intro hz
        apply z_not_used
        rw [St₃_used_eq, St₂_used_eq]
        exact used_sub₁ (bv_T_used z hz)
      have typ_out : St₅.types ⊢ˢ
          SMT.Term.lambda [z]
            [SMTType.pair σB τB]
            (.and (.app (.var S!) (.var z)) (.app T (.var z))) :
          SMTType.fun (SMTType.pair σB τB) SMTType.bool := by
        rw [St₅_types_eq']
        refine SMT.Typing.lambda St₃.types [z]
          [SMTType.pair σB τB] _ SMTType.bool
          ?_ ?_ (by simp) rfl ?_
        · intro v hv
          rw [List.mem_singleton] at hv
          simpa [hv] using z_fresh
        · intro v hv
          rw [List.mem_singleton] at hv
          subst v
          simp only [SMT.bv, List.append_nil, List.mem_append]
          push_neg
          exact ⟨by simp [SMT.bv], z_not_bv_T⟩
        · have hupdate :
              TypeContext.update St₃.types [z]
                [SMTType.pair σB τB] rfl =
              St₃.types.insert z (SMTType.pair σB τB) := by
            simp only [TypeContext.update, List.length_cons, List.length_nil,
              zero_add, Nat.reduceAdd, Fin.cast_eq_self, Fin.getElem_fin,
              Fin.val_eq_zero, List.getElem_cons_zero, Fin.foldl_succ,
              Fin.foldl_zero]
          rw [hupdate]
          apply SMT.Typing.and
          · apply SMT.Typing.app
            · exact SMT.Typing.weakening
                (TypeContext.entries_subset_insert_of_notMem z_fresh)
                typ_S!_St₃
                (SMT.Typing.bv_notMem_insert_of_fresh typ_S!_St₃
                  (by simp [SMT.bv]))
            · exact SMT.Typing.var _ z _ (AList.lookup_insert St₃.types)
          · apply SMT.Typing.app
            · exact SMT.Typing.weakening
                (TypeContext.entries_subset_insert_of_notMem z_fresh)
                typ_T_St₃
                (SMT.Typing.bv_notMem_insert_of_fresh typ_T_St₃ z_not_bv_T)
            · exact SMT.Typing.var _ z _ (AList.lookup_insert St₃.types)
      mspec Std.Do.Spec.pure
      mpure_intro
      and_intros
      · intro v hv
        rw [St₅_used_eq, St₄_used_eq, St₃_used_eq, St₂_used_eq]
        exact List.mem_cons_of_mem z (used_sub₁ hv)
      · intro e he
        rw [St₅_types_eq', St₃_types_eq, St₂_types_eq]
        exact St₁_types_sub
          (SMT.TypeContext.entries_subset_insert_of_notMem S!_fresh he)
      · intro v hv
        rw [St₅_types_eq', St₃_types_eq, St₂_types_eq] at hv
        rw [St₅_used_eq, St₄_used_eq, St₃_used_eq, St₂_used_eq]
        exact List.mem_cons_of_mem z (St₁_keys_sub hv)
      · trivial
      · exact typ_out
      · intro v hv hv_not
        rw [St₅_types_eq', St₃_types_eq, St₂_types_eq]
        exact preserves₁ v hv hv_not
      · intro Θ hS hT Θ_none respects_S respects_T Θ_dom
          F G hF hG denS denT h_den_S h_den_T F_rel G_rel
        have pf : ∀ (x! : SMT.𝒱) (X! : SMT.Dom.{u}),
            ∀ v ∈ SMT.fv (SMT.Term.var x!),
              (Function.update Θ x! (some X!) v).isSome = true := by
          intro x! X! v hv
          rw [SMT.fv, List.mem_singleton] at hv
          subst v
          simp [Function.update_self]
        obtain ⟨Φ, denS!, h_den_var, _hφ, _h_den_φ, denS!_type,
          _Φ_type, ⟨_Φ_true, cast_pair⟩, _helper_total⟩ :=
          adequacy Θ hS respects_S pf denS h_den_S
        let Δhelper := Function.update Θ S! (some denS!)
        have Δ_S!_none : Θ S! = none := Θ_none S! S!_not_used
        have Δhelper_ext : RenamingContext.Extends Δhelper Θ :=
          RenamingContext.extends_update_of_none Δ_S!_none
        have Λ_sub_final : St₀.types ⊆ St₅.types := by
          intro e he
          rw [St₅_types_eq', St₃_types_eq, St₂_types_eq]
          exact St₁_types_sub
            (SMT.TypeContext.entries_subset_insert_of_notMem S!_fresh he)
        have hS!_not_fv_T : S! ∉ SMT.fv T :=
          funNotMemFvOfNotMemContext typ_T S!_fresh
        have hT_helper : RenamingContext.CoversFV Δhelper T :=
          SMT.RenamingContext.coversFV_update_of_notMem hS!_not_fv_T hT
        have h_den_T_helper :
            ⟦T.abstract Δhelper hT_helper⟧ˢ = some denT := by
          have heq : ⟦T.abstract Θ hT⟧ˢ =
              ⟦T.abstract Δhelper hT_helper⟧ˢ := by
            rw [← SMT.RenamingContext.denote,
              ← SMT.RenamingContext.denote]
            exact SMT.RenamingContext.denote_update_of_notMem hS!_not_fv_T
          rw [← heq]
          exact h_den_T
        have hS!_helper :
            RenamingContext.CoversFV Δhelper (SMT.Term.var S!) := by
          intro v hv
          rw [SMT.fv, List.mem_singleton] at hv
          subst v
          simp [Δhelper, Function.update_self]
        have h_den_S!_helper :
            ⟦(SMT.Term.var S!).abstract Δhelper hS!_helper⟧ˢ =
              some denS! := by
          convert h_den_var using 1
        have hcov_out : RenamingContext.CoversFV Δhelper
            (.lambda [z] [SMTType.pair σB τB]
              (.and (.app (.var S!) (.var z)) (.app T (.var z)))) := by
          intro v hv
          simp only [SMT.fv, List.removeAll, List.mem_filter,
            List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
          obtain ⟨hv_body, hv_ne_z⟩ := hv
          simp only [List.elem_eq_contains, List.contains_eq_mem,
            List.mem_cons, List.not_mem_nil, or_false, Bool.not_eq_true',
            decide_eq_false_iff_not] at hv_ne_z
          rcases hv_body with ((rfl | rfl) | (hv_T | rfl))
          · exact hS!_helper v (by simp [SMT.fv])
          · exact absurd rfl hv_ne_z
          · exact hT_helper v hv_T
          · exact absurd rfl hv_ne_z
        have z_not_fv_S! : z ∉ SMT.fv (SMT.Term.var S!) :=
          funNotMemFvOfNotMemContext typ_S!_St₃ z_fresh
        have z_not_fv_T : z ∉ SMT.fv T :=
          funNotMemFvOfNotMemContext typ_T_St₃ z_fresh
        have denS_type := SMT.RenamingContext.denote_type_of_typing_fv
          typ_S respects_S hS h_den_S
        have denT_type := SMT.RenamingContext.denote_type_of_typing_fv
          typ_T respects_T hT h_den_T
        let hsS : BType.SupportedSMT (BType.set (α ×ᴮ β))
            (SMTType.fun σA (SMTType.option τA)) := .optionFun hsAα hsAβ
        let hsT : BType.SupportedSMT (BType.set (α ×ᴮ β))
            (SMTType.fun (SMTType.pair σB τB) SMTType.bool) :=
          .setPred (.prod hsBα hsBβ)
        have hsS_den : BType.SupportedSMT (BType.set (α ×ᴮ β))
            denS.snd.fst := by
          rw [denS_type]
          exact hsS
        have hsT_den : BType.SupportedSMT (BType.set (α ×ᴮ β))
            denT.snd.fst := by
          rw [denT_type]
          exact hsT
        have F_supported : RDomCastSupported
            (⟨F, BType.set (α ×ᴮ β), hF⟩ : B.Dom) denS :=
          ⟨RDomCast.toRDomCastAdmissible_of_supported F_rel hsS_den, hsS_den⟩
        have G_supported : RDomCastSupported
            (⟨G, BType.set (α ×ᴮ β), hG⟩ : B.Dom) denT :=
          ⟨RDomCast.toRDomCastAdmissible_of_supported G_rel hsT_den, hsT_den⟩
        obtain ⟨denU, h_den_U, U_rel⟩ :=
          castInter_graph_denotation α β hsAα hsAβ hsBα hsBβ hF hG
            denS_type denS!_type denT_type F_supported G_supported
            hα.toCastPath hβ.toCastPath cast_pair
            hS!_helper hT_helper h_den_S!_helper h_den_T_helper
            z_not_fv_S! z_not_fv_T hcov_out
        have typ_S!_St₅ : St₅.types ⊢ˢ SMT.Term.var S! :
            SMTType.fun (SMTType.pair σB τB) SMTType.bool := by
          rw [St₅_types_eq', St₃_types_eq, St₂_types_eq]
          exact typ_S!_St₁
        have respects_T_final :
            SMT.RenamingContext.RespectsTypeContextOnFV
              Δhelper St₅.types T :=
          respects_T.of_extends Δhelper_ext Λ_sub_final typ_T
        have target_respects_out :
            SMT.RenamingContext.RespectsTypeContextOnFV Δhelper St₅.types
              (.lambda [z] [SMTType.pair σB τB]
                (.and (.app (.var S!) (.var z)) (.app T (.var z)))) := by
          intro v σ hv hlookup
          simp only [SMT.fv, List.removeAll, List.mem_filter,
            List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
          obtain ⟨hv_body, hv_ne_z⟩ := hv
          simp only [List.elem_eq_contains, List.contains_eq_mem,
            List.mem_cons, List.not_mem_nil, or_false, Bool.not_eq_true',
            decide_eq_false_iff_not] at hv_ne_z
          rcases hv_body with ((rfl | rfl) | (hv_T | rfl))
          · have hlookup_S! := SMT.Typing.varE typ_S!_St₅
            rw [hlookup] at hlookup_S!
            cases hlookup_S!
            exact ⟨denS!, Function.update_self _ _ _, denS!_type⟩
          · exact absurd rfl hv_ne_z
          · exact respects_T_final hv_T hlookup
          · exact absurd rfl hv_ne_z
        have denU_type := SMT.RenamingContext.denote_type_of_typing_fv
          typ_out target_respects_out hcov_out h_den_U
        refine ⟨Δhelper, hcov_out, denU, Δhelper_ext, ?_,
          target_respects_out, ?_, h_den_U, denU_type, U_rel⟩
        · intro v hv_final
          have hv_not_St₁ : v ∉ St₁.env.usedVars := by
            intro hv₁
            apply hv_final
            rw [St₅_used_eq, St₄_used_eq, St₃_used_eq, St₂_used_eq]
            exact List.mem_cons_of_mem z hv₁
          by_cases hvS! : v = S!
          · subst v
            exfalso
            apply hv_not_St₁
            apply St₁_keys_sub
            exact (AList.lookup_isSome).1
              (Option.isSome_of_eq_some (SMT.Typing.varE typ_S!_St₁))
          · simp only [Δhelper, Function.update_of_ne hvS!]
            apply Θ_none
            intro hv_used
            exact hv_not_St₁ (used_sub₁ hv_used)
        · intro v hv
          by_cases hvS! : v = S!
          · subst v
            exact (AList.lookup_isSome).1
              (Option.isSome_of_eq_some (SMT.Typing.varE typ_S!_St₅))
          · have hv₀ : v ∈ St₀.types := Θ_dom v (by
              simpa [Δhelper, Function.update_of_ne hvS!] using hv)
            obtain ⟨τv, hlookup⟩ := Option.isSome_iff_exists.mp
              (AList.lookup_isSome.mpr hv₀)
            exact AList.lookup_isSome.mp (Option.isSome_of_eq_some
              (AList.lookup_of_subset Λ_sub_final hlookup))

/- The option/function loosening branch first materializes the left relation
at the right endpoint representation and then emits the Boolean
characteristic predicate of the pointwise graph intersection. -/
set_option maxHeartbeats 1800000 in
@[spec]
theorem castInter_fun_rep_spec.{u}
    (α β : BType) {σA τA σB τB : SMTType}
    (hsAα : BType.SupportedSMT α σA)
    (hsAβ : BType.SupportedSMT β τA)
    (hsBα : BType.SupportedSMT α σB)
    (hsBβ : BType.SupportedSMT β τB)
    (hα : σA ⊑ σB) (hβ : τA ⊑ τB)
    {S T : SMT.Term}
    {Λ : SMT.TypeContext} {n : ℕ} {used : List SMT.𝒱}
    (typ_S : Λ ⊢ˢ S :
      SMTType.fun σA (SMTType.option τA))
    (typ_T : Λ ⊢ˢ T :
      SMTType.fun σB (SMTType.option τB))
    (bv_S_used : ∀ v ∈ SMT.bv S, v ∈ used)
    (bv_T_used : ∀ v ∈ SMT.bv T, v ∈ used) :
    ⦃ fun ⟨E, Λ'⟩ =>
      ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ Λ.keys ⊆ E.usedVars ∧
        E.usedVars = used⌝ ⦄
    castInter
      ⟨S, SMTType.fun σA (SMTType.option τA)⟩
      ⟨T, SMTType.fun σB (SMTType.option τB)⟩
    ⦃ ⇓? ⟨t, σ⟩ ⟨E', Γ'⟩ =>
      ⌜used ⊆ E'.usedVars ∧
        Λ ⊆ Γ' ∧
        Γ'.keys ⊆ E'.usedVars ∧
        σ = SMTType.fun (SMTType.pair σB τB) SMTType.bool ∧
        Γ' ⊢ˢ t : SMTType.fun (SMTType.pair σB τB) SMTType.bool ∧
        (∀ v ∈ used, v ∉ Λ → v ∉ Γ') ∧
        ∀ (Theta : SMT.RenamingContext.Context.{u})
          (hS : RenamingContext.CoversFV Theta S)
          (hT : RenamingContext.CoversFV Theta T),
          (∀ v ∉ used, Theta v = none) →
          SMT.RenamingContext.RespectsTypeContextOnFV Theta Λ S →
          SMT.RenamingContext.RespectsTypeContextOnFV Theta Λ T →
          (∀ v, Theta v ≠ none → v ∈ Λ) →
          ∀ (F G : ZFSet.{u})
            (hF : F ∈ ⟦BType.set (α ×ᴮ β)⟧ᶻ)
            (hG : G ∈ ⟦BType.set (α ×ᴮ β)⟧ᶻ)
            (denS denT : SMT.Dom.{u}),
            ⟦S.abstract Theta hS⟧ˢ = some denS →
            ⟦T.abstract Theta hT⟧ˢ = some denT →
            RDomCast
              (⟨F, BType.set (α ×ᴮ β), hF⟩ : B.Dom) denS →
            RDomCast
              (⟨G, BType.set (α ×ᴮ β), hG⟩ : B.Dom) denT →
            ∃ (Theta' : SMT.RenamingContext.Context.{u})
              (hcov : RenamingContext.CoversFV Theta' t)
              (denU : SMT.Dom.{u}),
              RenamingContext.Extends Theta' Theta ∧
              (∀ v ∉ E'.usedVars, Theta' v = none) ∧
              SMT.RenamingContext.RespectsTypeContextOnFV Theta' Γ' t ∧
              (∀ v, Theta' v ≠ none → v ∈ Γ') ∧
              ⟦t.abstract Theta' hcov⟧ˢ = some denU ∧
              denU.snd.fst = σ ∧
              RDomCastSupported
                (⟨F ∩ G, BType.set (α ×ᴮ β),
                  relation_inter_mem hF hG⟩ : B.Dom) denU⌝ ⦄ := by
  let cfun : SMTType.fun σA (SMTType.option τA) ~>
      SMTType.fun σB (SMTType.option τB) :=
    castPath.fun (by simp) hα.toCastPath
      (castPath.opt hβ.toCastPath)
  have hcastInter :
      castInter
        (S, SMTType.fun σA (SMTType.option τA))
        (T, SMTType.fun σB (SMTType.option τB)) =
      castInter.fun S T (by simp) hα.toCastPath
        (castPath.opt hβ.toCastPath) := by
    simp only [castInter]
    by_cases heq : SMTType.fun σA (SMTType.option τA) =
        SMTType.fun σB (SMTType.option τB)
    · injection heq with hσ hopt
      injection hopt with hτ
      subst σB
      subst τB
      rw [dif_pos rfl]
      simp only
      have hdom : castPath.reflexive σA = hα.toCastPath :=
        castPath.eq_of_endpoints _ _
      have hcod : castPath.reflexive (SMTType.option τA) =
          castPath.opt hβ.toCastPath := castPath.eq_of_endpoints _ _
      rw [hdom, hcod]
    · rw [dif_neg heq]
      let hfun : SMTType.fun σA (SMTType.option τA) ⊑
          SMTType.fun σB (SMTType.option τB) :=
        castable?.fun (by simp) hα (castable?.opt hβ)
      rw [dif_pos hfun]
      unfold castInterAux
      have hpath : hfun.toCastPath = cfun :=
        castPath.eq_of_endpoints _ _
      rw [hpath]
  rw [hcastInter]
  unfold castInter.fun
  mintro pre ∀St₀
  mpure pre
  obtain ⟨rfl, rfl, St₀_sub, rfl⟩ := pre
  mspec loosenAux_prf_spec_univ (Λ := St₀.types)
    (n := St₀.env.freshvarsc)
    (used := St₀.env.usedVars) typ_S bv_S_used cfun
  next out =>
    obtain ⟨S!, S!_spec⟩ := out
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨_, St₁_types_sub, S!_fresh, S!_not_used, used_sub₁,
      St₁_keys_sub, preserves₁, _, _, typ_S!_St₁, _, _, adequacy⟩ := pre
    mspec SMT.declareConst_spec (v := S!)
      (τ := SMTType.fun σB (SMTType.option τB))
      (decl := St₁.env.declarations) (as := St₁.env.asserts)
      (n := St₁.env.freshvarsc) (Γ := St₁.types)
      (used := St₁.env.usedVars)
    mrename_i pre
    mintro ∀St₂
    mpure pre
    obtain ⟨_, _, St₂_fvc_eq, St₂_used_eq, St₂_types_eq⟩ := pre
    mspec SMT.addSpec_spec (x! := S!) (x!_spec := S!_spec)
      (decl := St₂.env.declarations) (as := St₂.env.asserts)
      (n := St₂.env.freshvarsc) (Γ := St₂.types)
      (used := St₂.env.usedVars)
    mrename_i pre
    mintro ∀St₃
    mpure pre
    obtain ⟨_, _, St₃_fvc_eq, St₃_used_eq, St₃_types_eq⟩ := pre
    mspec SMT.freshVar_spec (Γ := St₃.types)
      (τ := SMTType.pair σB τB)
      (n := St₃.env.freshvarsc) (used := St₃.env.usedVars)
    next p =>
      mrename_i pre
      mintro ∀St₄
      mpure pre
      obtain ⟨St₄_types_eq, p_fresh, St₄_fvc_eq, St₄_used_eq,
        p_not_used⟩ := pre
      mspec SMT.eraseFromContext_spec (v := p) (Γ := St₄.types)
        (n := St₄.env.freshvarsc) (used := St₄.env.usedVars)
      mrename_i pre
      mintro ∀St₅
      mpure pre
      obtain ⟨St₅_types_eq, St₅_fvc_eq, St₅_used_eq⟩ := pre
      have St₅_types_eq' : St₅.types = St₃.types := by
        rw [St₅_types_eq, St₄_types_eq,
          erase_insert_self_rep_inter p_fresh]
      have typ_T_St₁ : St₁.types ⊢ˢ T :
          SMTType.fun σB (SMTType.option τB) :=
        SMT.Typing.weakening
          (h := fun v hv => St₁_types_sub
            (SMT.TypeContext.entries_subset_insert_of_notMem S!_fresh hv))
          typ_T
          (fun v hv => preserves₁ v (bv_T_used v hv)
            (SMT.Typing.bv_notMem_context typ_T v hv))
      have typ_T_St₃ : St₃.types ⊢ˢ T :
          SMTType.fun σB (SMTType.option τB) := by
        rwa [St₃_types_eq, St₂_types_eq]
      have typ_S!_St₃ : St₃.types ⊢ˢ SMT.Term.var S! :
          SMTType.fun σB (SMTType.option τB) := by
        rwa [St₃_types_eq, St₂_types_eq]
      have p_not_bv_T : p ∉ SMT.bv T := by
        intro hp
        apply p_not_used
        rw [St₃_used_eq, St₂_used_eq]
        exact used_sub₁ (bv_T_used p hp)
      have typ_out : St₅.types ⊢ˢ
          SMT.Term.lambda [p] [SMTType.pair σB τB]
            (.and
              (.eq (.app (.var S!) (.fst (.var p)))
                (.some (.snd (.var p))))
              (.eq (.app T (.fst (.var p)))
                (.some (.snd (.var p))))) :
          SMTType.fun (SMTType.pair σB τB) SMTType.bool := by
        rw [St₅_types_eq']
        refine SMT.Typing.lambda St₃.types [p]
          [SMTType.pair σB τB] _ SMTType.bool
          ?_ ?_ (by simp) rfl ?_
        · intro v hv
          rw [List.mem_singleton] at hv
          simpa [hv] using p_fresh
        · intro v hv
          rw [List.mem_singleton] at hv
          subst v
          simp only [SMT.bv, List.append_nil, List.mem_append]
          push_neg
          exact ⟨by simp, p_not_bv_T⟩
        · have hupdate :
              TypeContext.update St₃.types [p]
                [SMTType.pair σB τB] rfl =
              St₃.types.insert p (SMTType.pair σB τB) := by
            simp only [TypeContext.update, List.length_cons, List.length_nil,
              zero_add, Nat.reduceAdd, Fin.cast_eq_self, Fin.getElem_fin,
              Fin.val_eq_zero, List.getElem_cons_zero, Fin.foldl_succ,
              Fin.foldl_zero]
          rw [hupdate]
          have typ_var : St₃.types.insert p (SMTType.pair σB τB) ⊢ˢ
              SMT.Term.var p : SMTType.pair σB τB :=
            SMT.Typing.var _ p _ (AList.lookup_insert St₃.types)
          have typ_fst : St₃.types.insert p (SMTType.pair σB τB) ⊢ˢ
              .fst (.var p) : σB := SMT.Typing.fst _ _ _ _ typ_var
          have typ_snd : St₃.types.insert p (SMTType.pair σB τB) ⊢ˢ
              .snd (.var p) : τB := SMT.Typing.snd _ _ _ _ typ_var
          have typ_some : St₃.types.insert p (SMTType.pair σB τB) ⊢ˢ
              .some (.snd (.var p)) : SMTType.option τB :=
            SMT.Typing.some _ _ _ typ_snd
          have typ_S!_body : St₃.types.insert p (SMTType.pair σB τB) ⊢ˢ
              SMT.Term.var S! : SMTType.fun σB (SMTType.option τB) :=
            SMT.Typing.weakening
              (TypeContext.entries_subset_insert_of_notMem p_fresh)
              typ_S!_St₃
              (SMT.Typing.bv_notMem_insert_of_fresh typ_S!_St₃
                (by simp [SMT.bv]))
          have typ_T_body : St₃.types.insert p (SMTType.pair σB τB) ⊢ˢ
              T : SMTType.fun σB (SMTType.option τB) :=
            SMT.Typing.weakening
              (TypeContext.entries_subset_insert_of_notMem p_fresh)
              typ_T_St₃
              (SMT.Typing.bv_notMem_insert_of_fresh typ_T_St₃ p_not_bv_T)
          apply SMT.Typing.and
          · apply SMT.Typing.eq
            · exact SMT.Typing.app _ _ _ _ _ typ_S!_body typ_fst
            · exact typ_some
          · apply SMT.Typing.eq
            · exact SMT.Typing.app _ _ _ _ _ typ_T_body typ_fst
            · exact typ_some
      mspec Std.Do.Spec.pure
      mpure_intro
      and_intros
      · intro v hv
        rw [St₅_used_eq, St₄_used_eq, St₃_used_eq, St₂_used_eq]
        exact List.mem_cons_of_mem p (used_sub₁ hv)
      · intro e he
        rw [St₅_types_eq', St₃_types_eq, St₂_types_eq]
        exact St₁_types_sub
          (SMT.TypeContext.entries_subset_insert_of_notMem S!_fresh he)
      · intro v hv
        rw [St₅_types_eq', St₃_types_eq, St₂_types_eq] at hv
        rw [St₅_used_eq, St₄_used_eq, St₃_used_eq, St₂_used_eq]
        exact List.mem_cons_of_mem p (St₁_keys_sub hv)
      · trivial
      · exact typ_out
      · intro v hv hv_not
        rw [St₅_types_eq', St₃_types_eq, St₂_types_eq]
        exact preserves₁ v hv hv_not
      · intro Theta hS hT Theta_none respects_S respects_T Theta_dom
          F G hF hG denS denT h_den_S h_den_T F_rel G_rel
        have pf : ∀ (x! : SMT.𝒱) (X! : SMT.Dom.{u}),
            ∀ v ∈ SMT.fv (SMT.Term.var x!),
              (Function.update Theta x! (some X!) v).isSome = true := by
          intro x! X! v hv
          rw [SMT.fv, List.mem_singleton] at hv
          subst v
          simp [Function.update_self]
        obtain ⟨Phi, denS!, h_den_var, _hPhi, _h_den_Phi, denS!_type,
          _Phi_type, ⟨_Phi_true, cast_pair⟩, _helper_total⟩ :=
          adequacy Theta hS respects_S pf denS h_den_S
        let DeltaHelper := Function.update Theta S! (some denS!)
        have Delta_S!_none : Theta S! = none :=
          Theta_none S! S!_not_used
        have DeltaHelper_ext : RenamingContext.Extends DeltaHelper Theta :=
          RenamingContext.extends_update_of_none Delta_S!_none
        have Lambda_sub_final : St₀.types ⊆ St₅.types := by
          intro e he
          rw [St₅_types_eq', St₃_types_eq, St₂_types_eq]
          exact St₁_types_sub
            (SMT.TypeContext.entries_subset_insert_of_notMem S!_fresh he)
        have hS!_not_fv_T : S! ∉ SMT.fv T :=
          funNotMemFvOfNotMemContext typ_T S!_fresh
        have hT_helper : RenamingContext.CoversFV DeltaHelper T :=
          SMT.RenamingContext.coversFV_update_of_notMem hS!_not_fv_T hT
        have h_den_T_helper :
            ⟦T.abstract DeltaHelper hT_helper⟧ˢ = some denT := by
          have heq : ⟦T.abstract Theta hT⟧ˢ =
              ⟦T.abstract DeltaHelper hT_helper⟧ˢ := by
            rw [← SMT.RenamingContext.denote,
              ← SMT.RenamingContext.denote]
            exact SMT.RenamingContext.denote_update_of_notMem hS!_not_fv_T
          rw [← heq]
          exact h_den_T
        have hS!_helper :
            RenamingContext.CoversFV DeltaHelper (SMT.Term.var S!) := by
          intro v hv
          rw [SMT.fv, List.mem_singleton] at hv
          subst v
          simp [DeltaHelper, Function.update_self]
        have h_den_S!_helper :
            ⟦(SMT.Term.var S!).abstract DeltaHelper hS!_helper⟧ˢ =
              some denS! := by
          convert h_den_var using 1
        have hcov_out : RenamingContext.CoversFV DeltaHelper
            (SMT.Term.lambda [p] [SMTType.pair σB τB]
              (.and
                (.eq (.app (.var S!) (.fst (.var p)))
                  (.some (.snd (.var p))))
                (.eq (.app T (.fst (.var p)))
                  (.some (.snd (.var p)))))) := by
          intro v hv
          simp only [SMT.fv, List.removeAll, List.mem_filter,
            List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
          obtain ⟨hv_body, hv_ne_p⟩ := hv
          simp only [List.elem_eq_contains, List.contains_eq_mem,
            List.mem_cons, List.not_mem_nil, or_false, Bool.not_eq_true',
            decide_eq_false_iff_not] at hv_ne_p
          rcases hv_body with
            (((rfl | rfl) | rfl) | ((hv_T | rfl) | rfl))
          · exact hS!_helper v (by simp [SMT.fv])
          · exact absurd rfl hv_ne_p
          · exact absurd rfl hv_ne_p
          · exact hT_helper v hv_T
          · exact absurd rfl hv_ne_p
          · exact absurd rfl hv_ne_p
        have p_not_fv_S! : p ∉ SMT.fv (SMT.Term.var S!) :=
          funNotMemFvOfNotMemContext typ_S!_St₃ p_fresh
        have p_not_fv_T : p ∉ SMT.fv T :=
          funNotMemFvOfNotMemContext typ_T_St₃ p_fresh
        have denS_type := SMT.RenamingContext.denote_type_of_typing_fv
          typ_S respects_S hS h_den_S
        have denT_type := SMT.RenamingContext.denote_type_of_typing_fv
          typ_T respects_T hT h_den_T
        rcases denS with ⟨Fenc, sigmaS, hFenc⟩
        dsimp at denS_type
        subst sigmaS
        rcases denT with ⟨Genc, sigmaT, hGenc⟩
        dsimp at denT_type
        subst sigmaT
        rcases denS! with ⟨Fhelper, sigmaHelper, hFhelper⟩
        dsimp at denS!_type
        subst sigmaHelper
        let hsS : BType.SupportedSMT (BType.set (α ×ᴮ β))
            (SMTType.fun σA (SMTType.option τA)) :=
          .optionFun hsAα hsAβ
        let hsT : BType.SupportedSMT (BType.set (α ×ᴮ β))
            (SMTType.fun σB (SMTType.option τB)) :=
          .optionFun hsBα hsBβ
        have F_supported : RDomCastSupported
            (⟨F, BType.set (α ×ᴮ β), hF⟩ : B.Dom)
            (⟨Fenc, SMTType.fun σA (SMTType.option τA), hFenc⟩ :
              SMT.Dom) :=
          ⟨RDomCast.toRDomCastAdmissible_of_supported F_rel hsS, hsS⟩
        have G_supported : RDomCastSupported
            (⟨G, BType.set (α ×ᴮ β), hG⟩ : B.Dom)
            (⟨Genc, SMTType.fun σB (SMTType.option τB), hGenc⟩ :
              SMT.Dom) :=
          ⟨RDomCast.toRDomCastAdmissible_of_supported G_rel hsT, hsT⟩
        have F_helper_supported : RDomCastSupported
            (⟨F, BType.set (α ×ᴮ β), hF⟩ : B.Dom)
            (⟨Fhelper, SMTType.fun σB (SMTType.option τB), hFhelper⟩ :
              SMT.Dom) :=
          RDomCastSupported.of_cast_to_supported F_supported hsT
            cfun cast_pair
        have typ_S!_St₅ : St₅.types ⊢ˢ SMT.Term.var S! :
            SMTType.fun σB (SMTType.option τB) := by
          rw [St₅_types_eq', St₃_types_eq, St₂_types_eq]
          exact typ_S!_St₁
        have respects_T_final :
            SMT.RenamingContext.RespectsTypeContextOnFV
              DeltaHelper St₅.types T :=
          respects_T.of_extends DeltaHelper_ext Lambda_sub_final typ_T
        have target_respects_out :
            SMT.RenamingContext.RespectsTypeContextOnFV
              DeltaHelper St₅.types
              (SMT.Term.lambda [p] [SMTType.pair σB τB]
                (.and
                  (.eq (.app (.var S!) (.fst (.var p)))
                    (.some (.snd (.var p))))
                  (.eq (.app T (.fst (.var p)))
                    (.some (.snd (.var p)))))) := by
          intro v σ hv hlookup
          simp only [SMT.fv, List.removeAll, List.mem_filter,
            List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
          obtain ⟨hv_body, hv_ne_p⟩ := hv
          simp only [List.elem_eq_contains, List.contains_eq_mem,
            List.mem_cons, List.not_mem_nil, or_false, Bool.not_eq_true',
            decide_eq_false_iff_not] at hv_ne_p
          rcases hv_body with
            (((rfl | rfl) | rfl) | ((hv_T | rfl) | rfl))
          · have hlookup_S! := SMT.Typing.varE typ_S!_St₅
            rw [hlookup] at hlookup_S!
            cases hlookup_S!
            exact ⟨_, Function.update_self _ _ _, rfl⟩
          · exact absurd rfl hv_ne_p
          · exact absurd rfl hv_ne_p
          · exact respects_T_final hv_T hlookup
          · exact absurd rfl hv_ne_p
          · exact absurd rfl hv_ne_p
        obtain ⟨denU, h_den_U, U_rel⟩ :=
          castInter_option_denotation α β hsBα hsBβ hF hG
            rfl rfl F_helper_supported G_supported
            hS!_helper hT_helper h_den_S!_helper h_den_T_helper
            p_not_fv_S! p_not_fv_T typ_out target_respects_out hcov_out
        have denU_type := SMT.RenamingContext.denote_type_of_typing_fv
          typ_out target_respects_out hcov_out h_den_U
        refine ⟨DeltaHelper, hcov_out, denU, DeltaHelper_ext, ?_,
          target_respects_out, ?_, h_den_U, denU_type, U_rel⟩
        · intro v hv_final
          have hv_not_St₁ : v ∉ St₁.env.usedVars := by
            intro hv₁
            apply hv_final
            rw [St₅_used_eq, St₄_used_eq, St₃_used_eq, St₂_used_eq]
            exact List.mem_cons_of_mem p hv₁
          by_cases hvS! : v = S!
          · subst v
            exfalso
            apply hv_not_St₁
            apply St₁_keys_sub
            exact (AList.lookup_isSome).1
              (Option.isSome_of_eq_some (SMT.Typing.varE typ_S!_St₁))
          · simp only [DeltaHelper, Function.update_of_ne hvS!]
            apply Theta_none
            intro hv_used
            exact hv_not_St₁ (used_sub₁ hv_used)
        · intro v hv
          by_cases hvS! : v = S!
          · subst v
            exact (AList.lookup_isSome).1
              (Option.isSome_of_eq_some (SMT.Typing.varE typ_S!_St₅))
          · have hv₀ : v ∈ St₀.types := Theta_dom v (by
              simpa [DeltaHelper, Function.update_of_ne hvS!] using hv)
            obtain ⟨τv, hlookup⟩ := Option.isSome_iff_exists.mp
              (AList.lookup_isSome.mpr hv₀)
            exact AList.lookup_isSome.mp (Option.isSome_of_eq_some
              (AList.lookup_of_subset Lambda_sub_final hlookup))

/-! ## Constructor-facing intersection-helper contract -/

/-- Representation-aware contract required from `castInter` after both source
operands have been encoded.  It is intentionally quantified over valuations
and denotations so one operational run serves the current and totality proofs. -/
abbrev CastInterRepSpec.{u} (τ : BType)
    (S T : SMT.Term) (σS σT : SMTType) : Prop :=
  ∀ {Λ : SMT.TypeContext} {n : ℕ} {used : List SMT.𝒱},
    Λ ⊢ˢ S : σS →
    Λ ⊢ˢ T : σT →
    (∀ v ∈ SMT.bv S, v ∈ used) →
    (∀ v ∈ SMT.bv T, v ∈ used) →
    ⦃ fun ⟨E, Λ'⟩ =>
      ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ Λ.keys ⊆ E.usedVars ∧
        E.usedVars = used⌝ ⦄
    castInter ⟨S, σS⟩ ⟨T, σT⟩
    ⦃ ⇓? ⟨t, σ⟩ ⟨E', Γ'⟩ =>
      ⌜used ⊆ E'.usedVars ∧
        Λ ⊆ Γ' ∧
        Γ'.keys ⊆ E'.usedVars ∧
        Nonempty (σ ~> (BType.set τ).toSMTType) ∧
        Γ' ⊢ˢ t : σ ∧
        (∀ v ∈ used, v ∉ Λ → v ∉ Γ') ∧
        ∀ (Θ : SMT.RenamingContext.Context.{u})
          (hS : RenamingContext.CoversFV Θ S)
          (hT : RenamingContext.CoversFV Θ T),
          (∀ v ∉ used, Θ v = none) →
          SMT.RenamingContext.RespectsTypeContextOnFV Θ Λ S →
          SMT.RenamingContext.RespectsTypeContextOnFV Θ Λ T →
          (∀ v, Θ v ≠ none → v ∈ Λ) →
          ∀ (F G : ZFSet.{u})
            (hF : F ∈ ⟦BType.set τ⟧ᶻ)
            (hG : G ∈ ⟦BType.set τ⟧ᶻ)
            (denS denT : SMT.Dom.{u}),
            ⟦S.abstract Θ hS⟧ˢ = some denS →
            ⟦T.abstract Θ hT⟧ˢ = some denT →
            RDomCast (⟨F, BType.set τ, hF⟩ : B.Dom) denS →
            RDomCast (⟨G, BType.set τ, hG⟩ : B.Dom) denT →
            ∃ (Θ' : SMT.RenamingContext.Context.{u})
              (hcov : RenamingContext.CoversFV Θ' t)
              (denU : SMT.Dom.{u}),
              RenamingContext.Extends Θ' Θ ∧
              (∀ v ∉ E'.usedVars, Θ' v = none) ∧
              SMT.RenamingContext.RespectsTypeContextOnFV Θ' Γ' t ∧
              (∀ v, Θ' v ≠ none → v ∈ Γ') ∧
              ⟦t.abstract Θ' hcov⟧ˢ = some denU ∧
              denU.snd.fst = σ ∧
              RDomCastSupported
                (⟨F ∩ G, BType.set τ, set_inter_mem hF hG⟩ : B.Dom)
                denU⌝ ⦄

theorem castInter_direct_rep_contract.{u} (τ : BType)
    (ρ : SMTType) (hρ : BType.SupportedSMT τ ρ) (S T : SMT.Term) :
    CastInterRepSpec.{u} τ S T
      (SMTType.fun ρ SMTType.bool)
      (SMTType.fun ρ SMTType.bool) := by
  unfold CastInterRepSpec
  intro Λ n used typ_S typ_T bv_S_used bv_T_used
  mstart
  mintro pre ∀St
  mpure pre
  mspec castInter_direct_rep_spec τ ρ hρ typ_S typ_T
    bv_S_used bv_T_used
  rename_i out
  obtain ⟨t, σ⟩ := out
  mrename_i post
  mintro ∀St'
  mpure post
  obtain ⟨used_sub, types_sub, keys_sub, σ_eq, typ_out,
    preserves, semantic⟩ := post
  change σ = SMTType.fun ρ SMTType.bool at σ_eq
  subst σ
  mpure_intro
  exact ⟨used_sub, types_sub, keys_sub,
    (BType.SupportedSMT.setPred hρ).nonemptyCanonicalCastPath,
    typ_out, preserves, semantic⟩

theorem castInter_fun_rep_contract.{u}
    (α β : BType) {σA τA σB τB : SMTType}
    (hsAα : BType.SupportedSMT α σA)
    (hsAβ : BType.SupportedSMT β τA)
    (hsBα : BType.SupportedSMT α σB)
    (hsBβ : BType.SupportedSMT β τB)
    (hα : σA ⊑ σB) (hβ : τA ⊑ τB)
    (S T : SMT.Term) :
    CastInterRepSpec.{u} (α ×ᴮ β) S T
      (SMTType.fun σA (SMTType.option τA))
      (SMTType.fun σB (SMTType.option τB)) := by
  unfold CastInterRepSpec
  intro Λ n used typ_S typ_T bv_S_used bv_T_used
  mstart
  mintro pre ∀St
  mpure pre
  mspec castInter_fun_rep_spec α β hsAα hsAβ hsBα hsBβ
    hα hβ typ_S typ_T bv_S_used bv_T_used
  rename_i out
  obtain ⟨t, σ⟩ := out
  mrename_i post
  mintro ∀St'
  mpure post
  obtain ⟨used_sub, types_sub, keys_sub, σ_eq, typ_out,
    preserves, semantic⟩ := post
  change σ = SMTType.fun (SMTType.pair σB τB) SMTType.bool at σ_eq
  subst σ
  mpure_intro
  exact ⟨used_sub, types_sub, keys_sub,
    (BType.SupportedSMT.setPred
      (BType.SupportedSMT.prod hsBα hsBβ)).nonemptyCanonicalCastPath,
    typ_out, preserves, semantic⟩

private theorem castInter_fun_swap
    {σA τA σB τB : SMTType}
    (hne : SMTType.fun σA (SMTType.option τA) ≠
      SMTType.fun σB (SMTType.option τB))
    (hα : σB ⊑ σA) (hβ : τB ⊑ τA) (S T : SMT.Term) :
    castInter
        ⟨S, SMTType.fun σA (SMTType.option τA)⟩
        ⟨T, SMTType.fun σB (SMTType.option τB)⟩ =
      castInter
        ⟨T, SMTType.fun σB (SMTType.option τB)⟩
        ⟨S, SMTType.fun σA (SMTType.option τA)⟩ := by
  simp only [castInter]
  let hrev : SMTType.fun σB (SMTType.option τB) ⊑
      SMTType.fun σA (SMTType.option τA) :=
    castable?.fun (by simp) hα (castable?.opt hβ)
  have hnot : ¬SMTType.fun σA (SMTType.option τA) ⊑
      SMTType.fun σB (SMTType.option τB) := by
    intro hfwd
    exact hne (castable?.antisymm hfwd hrev)
  rw [dif_neg hne, dif_neg hnot, dif_pos hrev,
    dif_neg hne.symm, dif_pos hrev]

theorem castInter_fun_rev_rep_contract.{u}
    (α β : BType) {σA τA σB τB : SMTType}
    (hsAα : BType.SupportedSMT α σA)
    (hsAβ : BType.SupportedSMT β τA)
    (hsBα : BType.SupportedSMT α σB)
    (hsBβ : BType.SupportedSMT β τB)
    (hne : SMTType.fun σA (SMTType.option τA) ≠
      SMTType.fun σB (SMTType.option τB))
    (hα : σB ⊑ σA) (hβ : τB ⊑ τA)
    (S T : SMT.Term) :
    CastInterRepSpec.{u} (α ×ᴮ β) S T
      (SMTType.fun σA (SMTType.option τA))
      (SMTType.fun σB (SMTType.option τB)) := by
  unfold CastInterRepSpec
  intro Λ n used typ_S typ_T bv_S_used bv_T_used
  rw [castInter_fun_swap hne hα hβ S T]
  mstart
  mintro pre ∀St
  mpure pre
  mspec castInter_fun_rep_contract α β hsBα hsBβ hsAα hsAβ
    hα hβ T S typ_T typ_S bv_T_used bv_S_used
  rename_i out
  obtain ⟨t, σout⟩ := out
  mrename_i post
  mintro ∀St'
  mpure post
  obtain ⟨used_sub, types_sub, keys_sub, path, typ_out,
    preserves, semantic⟩ := post
  mpure_intro
  refine ⟨used_sub, types_sub, keys_sub, path, typ_out,
    preserves, ?_⟩
  intro Θ hS hT Θ_none respects_S respects_T Θ_dom
    F G hF hG denS denT hdenS hdenT F_rel G_rel
  obtain ⟨Θ', hcov, denU, Θ'_ext, Θ'_none, target_respects,
      Θ'_dom, hdenU, hdenU_type, U_rel⟩ :=
    semantic Θ hT hS Θ_none respects_T respects_S Θ_dom
      G F hG hF denT denS hdenT hdenS G_rel F_rel
  refine ⟨Θ', hcov, denU, Θ'_ext, Θ'_none, target_respects,
    Θ'_dom, hdenU, hdenU_type, ?_⟩
  rcases denU with ⟨Uval, σU, hUval⟩
  obtain ⟨⟨⟨c, hret⟩, hadmissible⟩, hsupported⟩ := U_rel
  refine ⟨⟨⟨c, ?_⟩, ?_⟩, hsupported⟩
  · calc
      retract (BType.set (α ×ᴮ β)) (castZF_apply c Uval) =
          G ∩ F := hret
      _ = F ∩ G := ZFSet.inter_comm
  · have hinter : G ∩ F = F ∩ G := ZFSet.inter_comm
    simpa only [hinter, proof_irrel_heq] using hadmissible

set_option maxHeartbeats 1800000 in
/-- If two represented characteristic predicates have comparable element
representations, `castInter` loosens the left predicate and then reuses the
direct pointwise-inter proof at the common target representation. -/
theorem castInter_chpred_rep_contract.{u}
    (τ : BType) (ρ σ : SMTType)
    (hρ : BType.SupportedSMT τ ρ)
    (hσ : BType.SupportedSMT τ σ)
    (hne : ρ ≠ σ) (hcast : ρ ⊑ σ)
    (S T : SMT.Term) :
    CastInterRepSpec.{u} τ S T
      (SMTType.fun ρ SMTType.bool)
      (SMTType.fun σ SMTType.bool) := by
  unfold CastInterRepSpec
  intro Λ n used typ_S typ_T bv_S_used bv_T_used
  have hfun : SMTType.fun ρ SMTType.bool ⊑
      SMTType.fun σ SMTType.bool := castable?.chpred hcast
  have hcastInter :
      castInter (S, SMTType.fun ρ SMTType.bool)
          (T, SMTType.fun σ SMTType.bool) =
        castInter.chpred S T hcast.toCastPath := by
    simp only [castInter]
    rw [dif_neg (by simpa using hne), dif_pos hfun]
    unfold castInterAux
    have hpath : hfun.toCastPath =
        castPath.chpred hcast.toCastPath := by
      calc
        hfun.toCastPath = (castable?.chpred hcast).toCastPath :=
          congrArg castable?.toCastPath (Subsingleton.elim _ _)
        _ = castPath.chpred hcast.toCastPath :=
          SMTType.castable?_to_castPath_chpred hcast
    rw [hpath]
  rw [hcastInter, castInter_chpred_via_direct S T hcast.toCastPath]
  mintro pre ∀St₀
  mpure pre
  obtain ⟨rfl, rfl, St₀_sub, rfl⟩ := pre
  mspec loosenAux_prf_spec_univ (Λ := St₀.types)
    (n := St₀.env.freshvarsc) (used := St₀.env.usedVars)
    typ_S bv_S_used (castPath.chpred hcast.toCastPath)
  next out =>
    obtain ⟨S!, S!_spec⟩ := out
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨_, St₁_types_sub, S!_fresh, S!_not_used, used_sub₁,
      St₁_keys_sub, preserves₁, _, _, typ_S!_St₁, _, _, adequacy⟩ := pre
    mspec SMT.declareConst_spec (v := S!)
      (τ := SMTType.fun σ SMTType.bool)
      (decl := St₁.env.declarations) (as := St₁.env.asserts)
      (n := St₁.env.freshvarsc) (Γ := St₁.types)
      (used := St₁.env.usedVars)
    mrename_i pre
    mintro ∀St₂
    mpure pre
    obtain ⟨_, _, St₂_fvc_eq, St₂_used_eq, St₂_types_eq⟩ := pre
    mspec SMT.addSpec_spec (x! := S!) (x!_spec := S!_spec)
      (decl := St₂.env.declarations) (as := St₂.env.asserts)
      (n := St₂.env.freshvarsc) (Γ := St₂.types)
      (used := St₂.env.usedVars)
    mrename_i pre
    mintro ∀St₃
    mpure pre
    obtain ⟨_, _, St₃_fvc_eq, St₃_used_eq, St₃_types_eq⟩ := pre
    have typ_T_St₁ : St₁.types ⊢ˢ T :
        SMTType.fun σ SMTType.bool :=
      SMT.Typing.weakening
        (h := fun v hv => St₁_types_sub
          (SMT.TypeContext.entries_subset_insert_of_notMem S!_fresh hv))
        typ_T
        (fun v hv => preserves₁ v (bv_T_used v hv)
          (SMT.Typing.bv_notMem_context typ_T v hv))
    have typ_T_St₃ : St₃.types ⊢ˢ T :
        SMTType.fun σ SMTType.bool := by
      rwa [St₃_types_eq, St₂_types_eq]
    have typ_S!_St₃ : St₃.types ⊢ˢ SMT.Term.var S! :
        SMTType.fun σ SMTType.bool := by
      rw [St₃_types_eq, St₂_types_eq]
      exact typ_S!_St₁
    have bv_T_St₃ : ∀ v ∈ SMT.bv T, v ∈ St₃.env.usedVars := by
      intro v hv
      rw [St₃_used_eq, St₂_used_eq]
      exact used_sub₁ (bv_T_used v hv)
    have keys_St₃ : St₃.types.keys ⊆ St₃.env.usedVars := by
      rw [St₃_types_eq, St₂_types_eq, St₃_used_eq, St₂_used_eq]
      exact St₁_keys_sub
    mspec castInter_direct_rep_spec τ σ hσ typ_S!_St₃ typ_T_St₃
      (by simp [SMT.bv]) bv_T_St₃
    next out =>
      obtain ⟨t, σout⟩ := out
      mrename_i post
      mintro ∀St₄
      mpure post
      obtain ⟨used_sub₄, types_sub₄, keys_sub₄, σout_eq,
        typ_out, preserves₄, semantic₄⟩ := post
      change σout = SMTType.fun σ SMTType.bool at σout_eq
      subst σout
      mpure_intro
      and_intros
      · intro v hv
        apply used_sub₄
        rw [St₃_used_eq, St₂_used_eq]
        exact used_sub₁ hv
      · intro e he
        apply types_sub₄
        rw [St₃_types_eq, St₂_types_eq]
        exact St₁_types_sub
          (SMT.TypeContext.entries_subset_insert_of_notMem S!_fresh he)
      · exact keys_sub₄
      · exact hσ.setPred.nonemptyCanonicalCastPath
      · exact typ_out
      · intro v hv hv_not
        apply preserves₄ v
        · rw [St₃_used_eq, St₂_used_eq]
          exact used_sub₁ hv
        · rw [St₃_types_eq, St₂_types_eq]
          exact preserves₁ v hv hv_not
      · intro Θ hS hT Θ_none respects_S respects_T Θ_dom
          F G hF hG denS denT h_den_S h_den_T F_rel G_rel
        have pf : ∀ (x! : SMT.𝒱) (X! : SMT.Dom.{u}),
            ∀ v ∈ SMT.fv (SMT.Term.var x!),
              (Function.update Θ x! (some X!) v).isSome = true := by
          intro x! X! v hv
          rw [SMT.fv, List.mem_singleton] at hv
          subst v
          simp [Function.update_self]
        obtain ⟨Φ, denS!, h_den_var, _hφ, _h_den_φ, denS!_type,
          _Φ_type, ⟨_Φ_true, cast_pair⟩, _helper_total⟩ :=
          adequacy Θ hS respects_S pf denS h_den_S
        let Δhelper := Function.update Θ S! (some denS!)
        have Δ_S!_none : Θ S! = none := Θ_none S! S!_not_used
        have Δhelper_ext : RenamingContext.Extends Δhelper Θ :=
          RenamingContext.extends_update_of_none Δ_S!_none
        have Λ_sub_St₃ : St₀.types ⊆ St₃.types := by
          intro e he
          rw [St₃_types_eq, St₂_types_eq]
          exact St₁_types_sub
            (SMT.TypeContext.entries_subset_insert_of_notMem S!_fresh he)
        have hS!_not_fv_T : S! ∉ SMT.fv T :=
          funNotMemFvOfNotMemContext typ_T S!_fresh
        have hT_helper : RenamingContext.CoversFV Δhelper T :=
          SMT.RenamingContext.coversFV_update_of_notMem hS!_not_fv_T hT
        have h_den_T_helper :
            ⟦T.abstract Δhelper hT_helper⟧ˢ = some denT := by
          have heq : ⟦T.abstract Θ hT⟧ˢ =
              ⟦T.abstract Δhelper hT_helper⟧ˢ := by
            rw [← SMT.RenamingContext.denote,
              ← SMT.RenamingContext.denote]
            exact SMT.RenamingContext.denote_update_of_notMem hS!_not_fv_T
          rw [← heq]
          exact h_den_T
        have hS!_helper :
            RenamingContext.CoversFV Δhelper (SMT.Term.var S!) := by
          intro v hv
          rw [SMT.fv, List.mem_singleton] at hv
          subst v
          simp [Δhelper, Function.update_self]
        have h_den_S!_helper :
            ⟦(SMT.Term.var S!).abstract Δhelper hS!_helper⟧ˢ =
              some denS! := by
          convert h_den_var using 1
        have respects_S!_helper :
            SMT.RenamingContext.RespectsTypeContextOnFV
              Δhelper St₃.types (SMT.Term.var S!) := by
          intro v τv hv hlookup
          rw [SMT.fv, List.mem_singleton] at hv
          subst v
          have hlookup_S! := SMT.Typing.varE typ_S!_St₃
          rw [hlookup] at hlookup_S!
          cases hlookup_S!
          exact ⟨denS!, Function.update_self _ _ _, denS!_type⟩
        have respects_T_helper :
            SMT.RenamingContext.RespectsTypeContextOnFV
              Δhelper St₃.types T :=
          respects_T.of_extends Δhelper_ext Λ_sub_St₃ typ_T
        have Δhelper_none : ∀ v ∉ St₃.env.usedVars,
            Δhelper v = none := by
          intro v hv
          by_cases hvS! : v = S!
          · subst v
            exfalso
            apply hv
            rw [St₃_used_eq, St₂_used_eq]
            apply St₁_keys_sub
            exact (AList.lookup_isSome).1
              (Option.isSome_of_eq_some (SMT.Typing.varE typ_S!_St₁))
          · simp only [Δhelper, Function.update_of_ne hvS!]
            apply Θ_none
            intro hv_used
            apply hv
            rw [St₃_used_eq, St₂_used_eq]
            exact used_sub₁ hv_used
        have Δhelper_dom : ∀ v, Δhelper v ≠ none →
            v ∈ St₃.types := by
          intro v hv
          by_cases hvS! : v = S!
          · subst v
            exact (AList.lookup_isSome).1
              (Option.isSome_of_eq_some (SMT.Typing.varE typ_S!_St₃))
          · have hv₀ : v ∈ St₀.types := Θ_dom v (by
              simpa [Δhelper, Function.update_of_ne hvS!] using hv)
            obtain ⟨τv, hlookup⟩ := Option.isSome_iff_exists.mp
              (AList.lookup_isSome.mpr hv₀)
            exact AList.lookup_isSome.mp (Option.isSome_of_eq_some
              (AList.lookup_of_subset Λ_sub_St₃ hlookup))
        have denS_type := SMT.RenamingContext.denote_type_of_typing_fv
          typ_S respects_S hS h_den_S
        rcases denS with ⟨Fenc, σS, hFenc⟩
        dsimp at denS_type
        subst σS
        rcases denS! with ⟨Fhelper, σhelper, hFhelper⟩
        dsimp at denS!_type
        subst σhelper
        let sourceSupported : BType.SupportedSMT (BType.set τ)
            (SMTType.fun ρ SMTType.bool) := .setPred hρ
        have F_supported : RDomCastSupported
            (⟨F, BType.set τ, hF⟩ : B.Dom)
            (⟨Fenc, SMTType.fun ρ SMTType.bool, hFenc⟩ : SMT.Dom) :=
          ⟨RDomCast.toRDomCastAdmissible_of_supported F_rel sourceSupported,
            sourceSupported⟩
        have F_helper_supported : RDomCastSupported
            (⟨F, BType.set τ, hF⟩ : B.Dom)
            (⟨Fhelper, SMTType.fun σ SMTType.bool,
              hFhelper⟩ : SMT.Dom) :=
          RDomCastSupported.of_cast_to_supported F_supported
            (.setPred hσ) (castPath.chpred hcast.toCastPath) cast_pair
        obtain ⟨Θ', hcov, denU, Θ'_ext, Θ'_none,
            target_respects, Θ'_dom, hdenU, hdenU_type, U_rel⟩ :=
          semantic₄ Δhelper hS!_helper hT_helper Δhelper_none
            respects_S!_helper respects_T_helper Δhelper_dom
            F G hF hG
            (⟨Fhelper, SMTType.fun σ SMTType.bool,
              hFhelper⟩ : SMT.Dom)
            denT h_den_S!_helper h_den_T_helper
            F_helper_supported.toRDomCast G_rel
        exact ⟨Θ', hcov, denU,
          RenamingContext.extends_trans Θ'_ext Δhelper_ext,
          Θ'_none, target_respects, Θ'_dom, hdenU,
          hdenU_type, U_rel⟩

private theorem castInter_chpred_swap
    (ρ σ : SMTType) (hne : ρ ≠ σ) (hcast : σ ⊑ ρ)
    (S T : SMT.Term) :
    castInter
        ⟨S, SMTType.fun ρ SMTType.bool⟩
        ⟨T, SMTType.fun σ SMTType.bool⟩ =
      castInter
        ⟨T, SMTType.fun σ SMTType.bool⟩
        ⟨S, SMTType.fun ρ SMTType.bool⟩ := by
  simp only [castInter]
  have hnefun : SMTType.fun ρ SMTType.bool ≠
      SMTType.fun σ SMTType.bool := by
    simpa using hne
  have hrev : SMTType.fun σ SMTType.bool ⊑
      SMTType.fun ρ SMTType.bool := castable?.chpred hcast
  have hnot : ¬SMTType.fun ρ SMTType.bool ⊑
      SMTType.fun σ SMTType.bool := by
    intro hfwd
    exact hnefun (castable?.antisymm hfwd hrev)
  rw [dif_neg hnefun, dif_neg hnot, dif_pos hrev,
    dif_neg hnefun.symm, dif_pos hrev]

theorem castInter_chpred_rev_rep_contract.{u}
    (τ : BType) (ρ σ : SMTType)
    (hρ : BType.SupportedSMT τ ρ)
    (hσ : BType.SupportedSMT τ σ)
    (hne : ρ ≠ σ) (hcast : σ ⊑ ρ)
    (S T : SMT.Term) :
    CastInterRepSpec.{u} τ S T
      (SMTType.fun ρ SMTType.bool)
      (SMTType.fun σ SMTType.bool) := by
  unfold CastInterRepSpec
  intro Λ n used typ_S typ_T bv_S_used bv_T_used
  rw [castInter_chpred_swap ρ σ hne hcast S T]
  mstart
  mintro pre ∀St
  mpure pre
  mspec castInter_chpred_rep_contract τ σ ρ hσ hρ
    hne.symm hcast T S typ_T typ_S bv_T_used bv_S_used
  rename_i out
  obtain ⟨t, σout⟩ := out
  mrename_i post
  mintro ∀St'
  mpure post
  obtain ⟨used_sub, types_sub, keys_sub, path, typ_out,
    preserves, semantic⟩ := post
  mpure_intro
  refine ⟨used_sub, types_sub, keys_sub, path, typ_out,
    preserves, ?_⟩
  intro Θ hS hT Θ_none respects_S respects_T Θ_dom
    F G hF hG denS denT hdenS hdenT F_rel G_rel
  obtain ⟨Θ', hcov, denU, Θ'_ext, Θ'_none, target_respects,
      Θ'_dom, hdenU, hdenU_type, U_rel⟩ :=
    semantic Θ hT hS Θ_none respects_T respects_S Θ_dom
      G F hG hF denT denS hdenT hdenS G_rel F_rel
  refine ⟨Θ', hcov, denU, Θ'_ext, Θ'_none, target_respects,
    Θ'_dom, hdenU, hdenU_type, ?_⟩
  rcases denU with ⟨Uval, σU, hUval⟩
  obtain ⟨⟨⟨c, hret⟩, hadmissible⟩, hsupported⟩ := U_rel
  refine ⟨⟨⟨c, ?_⟩, ?_⟩, hsupported⟩
  · calc
      retract (BType.set τ) (castZF_apply c Uval) = G ∩ F := hret
      _ = F ∩ G := ZFSet.inter_comm
  · have hinter : G ∩ F = F ∩ G := ZFSet.inter_comm
    simpa only [hinter, proof_irrel_heq] using hadmissible

theorem castInter_graph_rep_contract.{u}
    (α β : BType) {σA τA σB τB : SMTType}
    (hsAα : BType.SupportedSMT α σA)
    (hsAβ : BType.SupportedSMT β τA)
    (hsBα : BType.SupportedSMT α σB)
    (hsBβ : BType.SupportedSMT β τB)
    (hα : σA ⊑ σB) (hβ : τA ⊑ τB)
    (S T : SMT.Term) :
    CastInterRepSpec.{u} (α ×ᴮ β) S T
      (SMTType.fun σA (SMTType.option τA))
      (SMTType.fun (SMTType.pair σB τB) SMTType.bool) := by
  unfold CastInterRepSpec
  intro Λ n used typ_S typ_T bv_S_used bv_T_used
  mstart
  mintro pre ∀St
  mpure pre
  mspec castInter_graph_rep_spec α β hsAα hsAβ hsBα hsBβ hα hβ typ_S typ_T
    bv_S_used bv_T_used
  rename_i out
  obtain ⟨t, σ⟩ := out
  mrename_i post
  mintro ∀St'
  mpure post
  obtain ⟨used_sub, types_sub, keys_sub, σ_eq, typ_out,
    preserves, semantic⟩ := post
  change σ = SMTType.fun (SMTType.pair σB τB) SMTType.bool at σ_eq
  subst σ
  mpure_intro
  exact ⟨used_sub, types_sub, keys_sub,
    (BType.SupportedSMT.setPred
      (BType.SupportedSMT.prod hsBα hsBβ)).nonemptyCanonicalCastPath,
    typ_out, preserves, semantic⟩

private theorem castInter_graph_swap
    {σA τA σB τB : SMTType}
    (hα : σA ⊑ σB) (hβ : τA ⊑ τB) (S T : SMT.Term) :
    castInter
        ⟨S, SMTType.fun (SMTType.pair σB τB) SMTType.bool⟩
        ⟨T, SMTType.fun σA (SMTType.option τA)⟩ =
      castInter
        ⟨T, SMTType.fun σA (SMTType.option τA)⟩
        ⟨S, SMTType.fun (SMTType.pair σB τB) SMTType.bool⟩ := by
  simp only [castInter]
  have hne :
      SMTType.fun (SMTType.pair σB τB) SMTType.bool ≠
        SMTType.fun σA (SMTType.option τA) := by
    simp
  have hne' :
      SMTType.fun σA (SMTType.option τA) ≠
        SMTType.fun (SMTType.pair σB τB) SMTType.bool := hne.symm
  have hnot : ¬
      SMTType.fun (SMTType.pair σB τB) SMTType.bool ⊑
        SMTType.fun σA (SMTType.option τA) := by
    intro h
    have := castable?_of_fun_bool h
    contradiction
  let hgraph :
      SMTType.fun σA (SMTType.option τA) ⊑
        SMTType.fun (SMTType.pair σB τB) SMTType.bool :=
    castable?.graph hα hβ
  rw [dif_neg hne, dif_neg hnot, dif_pos hgraph,
    dif_neg hne', dif_pos hgraph]

theorem castInter_graph_rev_rep_contract.{u}
    (α β : BType) {σA τA σB τB : SMTType}
    (hsAα : BType.SupportedSMT α σA)
    (hsAβ : BType.SupportedSMT β τA)
    (hsBα : BType.SupportedSMT α σB)
    (hsBβ : BType.SupportedSMT β τB)
    (hα : σA ⊑ σB) (hβ : τA ⊑ τB)
    (S T : SMT.Term) :
    CastInterRepSpec.{u} (α ×ᴮ β) S T
      (SMTType.fun (SMTType.pair σB τB) SMTType.bool)
      (SMTType.fun σA (SMTType.option τA)) := by
  unfold CastInterRepSpec
  intro Λ n used typ_S typ_T bv_S_used bv_T_used
  rw [castInter_graph_swap hα hβ S T]
  mstart
  mintro pre ∀St
  mpure pre
  mspec castInter_graph_rep_contract α β hsAα hsAβ hsBα hsBβ hα hβ T S
    typ_T typ_S bv_T_used bv_S_used
  rename_i out
  obtain ⟨t, σ⟩ := out
  mrename_i post
  mintro ∀St'
  mpure post
  obtain ⟨used_sub, types_sub, keys_sub, path, typ_out,
    preserves, semantic⟩ := post
  mpure_intro
  refine ⟨used_sub, types_sub, keys_sub, path, typ_out,
    preserves, ?_⟩
  intro Θ hS hT Θ_none respects_S respects_T Θ_dom
    F G hF hG denS denT hdenS hdenT F_rel G_rel
  obtain ⟨Θ', hcov, denU, Θ'_ext, Θ'_none, target_respects,
      Θ'_dom, hdenU, hdenU_type, U_rel⟩ :=
    semantic Θ hT hS Θ_none respects_T respects_S Θ_dom
      G F hG hF denT denS hdenT hdenS G_rel F_rel
  refine ⟨Θ', hcov, denU, Θ'_ext, Θ'_none, target_respects,
    Θ'_dom, hdenU, hdenU_type, ?_⟩
  rcases denU with ⟨Uval, σU, hUval⟩
  obtain ⟨⟨⟨c, hret⟩, hadmissible⟩, hsupported⟩ := U_rel
  refine ⟨⟨⟨c, ?_⟩, ?_⟩, hsupported⟩
  · calc
      retract (BType.set (α ×ᴮ β)) (castZF_apply c Uval) =
          G ∩ F := hret
      _ = F ∩ G := ZFSet.inter_comm
  · have hinter : G ∩ F = F ∩ G := ZFSet.inter_comm
    simpa only [hinter, proof_irrel_heq] using hadmissible

theorem castInter_option_rep_contract.{u}
    (α β : BType) {σ τ : SMTType}
    (hsα : BType.SupportedSMT α σ)
    (hsβ : BType.SupportedSMT β τ)
    (S T : SMT.Term) :
    CastInterRepSpec.{u} (α ×ᴮ β) S T
      (SMTType.fun σ (SMTType.option τ))
      (SMTType.fun σ (SMTType.option τ)) := by
  exact castInter_fun_rep_contract α β hsα hsβ hsα hsβ
    castable?.reflexive castable?.reflexive S T

private theorem castable_chpredE_rep {ρ σ : SMTType}
    (h : SMTType.fun ρ SMTType.bool ⊑
      SMTType.fun σ SMTType.bool) : ρ ⊑ σ := by
  cases h with
  | refl hbase => nomatch hbase
  | chpred hρ => exact hρ
  | «fun» hbool _ _ => exact (hbool rfl).elim

private theorem castable_optionFunE_rep
    {σA τA σB τB : SMTType}
    (h : SMTType.fun σA (SMTType.option τA) ⊑
      SMTType.fun σB (SMTType.option τB)) :
    σA ⊑ σB ∧ τA ⊑ τB := by
  cases h with
  | refl hbase => rcases hbase with h | h | h <;> cases h
  | «fun» _ hα hβ => exact ⟨hα, castable?.optE hβ⟩

private theorem not_castable_chpred_option
    (ρ α β : SMTType) :
    ¬SMTType.fun ρ SMTType.bool ⊑
      SMTType.fun α (SMTType.option β) := by
  intro h
  have hcod := castable?_of_fun_bool h
  contradiction

private theorem supported_prod_eq_canonical_of_graph_cast
    {α β : BType} {ρ : SMTType}
    (hρ : BType.SupportedSMT (α ×ᴮ β) ρ)
    (hcast : SMTType.fun α.toSMTType
        (SMTType.option β.toSMTType) ⊑
      SMTType.fun ρ SMTType.bool) :
    ρ = SMTType.pair α.toSMTType β.toSMTType := by
  rcases hρ.prodE with ⟨ρα, ρβ, rfl, hρα, hρβ⟩
  obtain ⟨cα, cβ⟩ := castPath.graph_components hcast.toCastPath
  have eα : α.toSMTType = ρα := castable?.antisymm
    (castable?_of_castPath cα.some)
    (castable?_of_castPath hρα.canonicalCastPath)
  have eβ : β.toSMTType = ρβ := castable?.antisymm
    (castable?_of_castPath cβ.some)
    (castable?_of_castPath hρβ.canonicalCastPath)
  simp [eα, eβ]

private theorem castInter_incomparable_rep_contract.{u}
    (τ : BType) (S T : SMT.Term) (σS σT : SMTType)
    (hne : σS ≠ σT) (hST : ¬σS ⊑ σT) (hTS : ¬σT ⊑ σS) :
    CastInterRepSpec.{u} τ S T σS σT := by
  unfold CastInterRepSpec
  intro Λ n used typ_S typ_T bv_S_used bv_T_used
  mintro pre ∀St
  mpure pre
  simp only [castInter]
  rw [dif_neg hne, dif_neg hST, dif_neg hTS]
  mvcgen

theorem castInter_supported_rep_contract.{u}
    (τ : BType) (S T : SMT.Term) (σS σT : SMTType)
    (supported_S : BType.SupportedSMT (BType.set τ) σS)
    (supported_T : BType.SupportedSMT (BType.set τ) σT) :
    CastInterRepSpec.{u} τ S T σS σT := by
  cases supported_S with
  | @setPred τ ρ hρ =>
      cases supported_T with
      | @setPred _ σ hσ =>
          by_cases heq : ρ = σ
          · subst σ
            exact castInter_direct_rep_contract τ ρ hρ S T
          · by_cases hcast : ρ ⊑ σ
            · exact castInter_chpred_rep_contract τ ρ σ hρ hσ
                heq hcast S T
            · by_cases hrev : σ ⊑ ρ
              · exact castInter_chpred_rev_rep_contract τ ρ σ hρ hσ
                  heq hrev S T
              · exact castInter_incomparable_rep_contract τ S T
                  (SMTType.fun ρ SMTType.bool)
                  (SMTType.fun σ SMTType.bool)
                  (by simpa using heq)
                  (fun h => hcast (castable_chpredE_rep h))
                  (fun h => hrev (castable_chpredE_rep h))
      | @optionFun α β σA τA hsAα hsAβ =>
          obtain ⟨σB, τB, rfl, hsBα, hsBβ⟩ := hρ.prodE
          have hne : SMTType.fun (SMTType.pair σB τB) SMTType.bool ≠
              SMTType.fun σA (SMTType.option τA) := by simp
          have hforward := not_castable_chpred_option
            (SMTType.pair σB τB) σA τA
          unfold CastInterRepSpec
          intro Λ n used typ_S typ_T bv_S_used bv_T_used
          by_cases hgraph : SMTType.fun σA (SMTType.option τA) ⊑
              SMTType.fun (SMTType.pair σB τB) SMTType.bool
          · obtain ⟨⟨cα⟩, ⟨cβ⟩⟩ :=
              castPath.graph_components hgraph.toCastPath
            exact castInter_graph_rev_rep_contract α β hsAα hsAβ hsBα hsBβ
              (castable?_of_castPath cα) (castable?_of_castPath cβ) S T
              typ_S typ_T bv_S_used bv_T_used
          · exact castInter_incomparable_rep_contract (α ×ᴮ β) S T
              (SMTType.fun (SMTType.pair σB τB) SMTType.bool)
              (SMTType.fun σA (SMTType.option τA))
              hne hforward hgraph typ_S typ_T bv_S_used bv_T_used
  | @optionFun α β σA τA hsAα hsAβ =>
      cases supported_T with
      | @setPred _ ρ hρ =>
          obtain ⟨σB, τB, rfl, hsBα, hsBβ⟩ := hρ.prodE
          have hne : SMTType.fun σA (SMTType.option τA) ≠
              SMTType.fun (SMTType.pair σB τB) SMTType.bool := by simp
          have hreverse := not_castable_chpred_option
            (SMTType.pair σB τB) σA τA
          unfold CastInterRepSpec
          intro Λ n used typ_S typ_T bv_S_used bv_T_used
          by_cases hgraph : SMTType.fun σA (SMTType.option τA) ⊑
              SMTType.fun (SMTType.pair σB τB) SMTType.bool
          · obtain ⟨⟨cα⟩, ⟨cβ⟩⟩ :=
              castPath.graph_components hgraph.toCastPath
            exact castInter_graph_rep_contract α β hsAα hsAβ hsBα hsBβ
              (castable?_of_castPath cα) (castable?_of_castPath cβ) S T
              typ_S typ_T bv_S_used bv_T_used
          · exact castInter_incomparable_rep_contract (α ×ᴮ β) S T
              (SMTType.fun σA (SMTType.option τA))
              (SMTType.fun (SMTType.pair σB τB) SMTType.bool)
              hne hgraph hreverse typ_S typ_T bv_S_used bv_T_used
      | @optionFun _ _ σB τB hsBα hsBβ =>
          by_cases heq : SMTType.fun σA (SMTType.option τA) =
              SMTType.fun σB (SMTType.option τB)
          · injection heq with hσ hopt
            injection hopt with hτ
            subst σB
            subst τB
            exact castInter_option_rep_contract α β hsAα hsAβ S T
          · by_cases hfwd : SMTType.fun σA (SMTType.option τA) ⊑
                SMTType.fun σB (SMTType.option τB)
            · obtain ⟨hα, hβ⟩ := castable_optionFunE_rep hfwd
              exact castInter_fun_rep_contract α β hsAα hsAβ hsBα hsBβ
                hα hβ S T
            · by_cases hrev : SMTType.fun σB (SMTType.option τB) ⊑
                  SMTType.fun σA (SMTType.option τA)
              · obtain ⟨hα, hβ⟩ := castable_optionFunE_rep hrev
                exact castInter_fun_rev_rep_contract α β hsAα hsAβ hsBα hsBβ
                  heq hα hβ S T
              · exact castInter_incomparable_rep_contract (α ×ᴮ β) S T
                  (SMTType.fun σA (SMTType.option τA))
                  (SMTType.fun σB (SMTType.option τB))
                  heq hfwd hrev

/-! ## Inter constructor composition -/

private theorem encodeTerm_inter_via_maplet (A B : B.Term)
    (E : _root_.B.Env) :
    encodeTerm (A ∩ᴮ B) E = (do
      let ⟨p, σp⟩ ← encodeTerm (A ↦ᴮ B) E
      match p, σp with
      | .pair A' B', .pair σA σB => castInter ⟨A', σA⟩ ⟨B', σB⟩
      | _, _ => throw "encodeTerm:inter: impossible maplet result") := by
  simp [encodeTerm]

private theorem denote_pair_inv_inter.{u}
    {x y : SMT.Term} {Θ : SMT.RenamingContext.Context.{u}}
    (hcov : RenamingContext.CoversFV Θ (SMT.Term.pair x y))
    {d : SMT.Dom.{u}}
    (hden : ⟦(SMT.Term.pair x y).abstract Θ hcov⟧ˢ = some d) :
    ∃ (dx dy : SMT.Dom.{u}),
      ⟦x.abstract Θ (fun v hv => hcov v (by
        rw [SMT.fv, List.mem_append]
        exact Or.inl hv))⟧ˢ = some dx ∧
      ⟦y.abstract Θ (fun v hv => hcov v (by
        rw [SMT.fv, List.mem_append]
        exact Or.inr hv))⟧ˢ = some dy ∧
      d = ⟨dx.fst.pair dy.fst, SMTType.pair dx.snd.fst dy.snd.fst,
        ZFSet.pair_mem_prod.mpr ⟨dx.snd.snd, dy.snd.snd⟩⟩ := by
  rw [SMT.Term.abstract, SMT.denote, Option.pure_def,
    Option.bind_eq_bind, Option.bind_eq_some_iff] at hden
  obtain ⟨dx, hdx, hrest⟩ := hden
  rw [Option.bind_eq_some_iff] at hrest
  obtain ⟨dy, hdy, hout⟩ := hrest
  refine ⟨dx, dy, ?_, ?_, ?_⟩
  · simpa only [proof_irrel_heq] using hdx
  · simpa only [proof_irrel_heq] using hdy
  · simpa using hout.symm

private theorem denote_inter_inv_rep.{u}
    {S T : B.Term} {τ : BType}
    {«Δ» : B.RenamingContext.Context}
    (Δ_fv : ∀ v ∈ B.fv (S ∩ᴮ T), («Δ» v).isSome = true)
    {U : ZFSet.{u}} {hU : U ∈ ⟦BType.set τ⟧ᶻ}
    (hden : ⟦(S ∩ᴮ T).abstract «Δ» Δ_fv⟧ᴮ =
      some ⟨U, ⟨BType.set τ, hU⟩⟩) :
    ∃ (F G : ZFSet.{u})
      (hF : F ∈ ⟦BType.set τ⟧ᶻ)
      (hG : G ∈ ⟦BType.set τ⟧ᶻ),
      ⟦S.abstract «Δ» (fun v hv => Δ_fv v (by
        rw [B.fv, List.mem_append]
        exact Or.inl hv))⟧ᴮ = some ⟨F, ⟨BType.set τ, hF⟩⟩ ∧
      ⟦T.abstract «Δ» (fun v hv => Δ_fv v (by
        rw [B.fv, List.mem_append]
        exact Or.inr hv))⟧ᴮ = some ⟨G, ⟨BType.set τ, hG⟩⟩ ∧
      U = F ∩ G := by
  rw [B.Term.abstract, B.denote, Option.pure_def,
    Option.bind_eq_bind, Option.bind_eq_some_iff] at hden
  obtain ⟨⟨F, α', hF⟩, denS, hrest⟩ := hden
  cases α' <;>
    first | rw [Option.bind_eq_some_iff] at hrest |
      exact absurd hrest (by simp)
  rename_i αi
  obtain ⟨⟨G, β', hG⟩, denT, hout⟩ := hrest
  cases β' <;>
    [exact absurd hout (by simp); exact absurd hout (by simp); skip;
      exact absurd hout (by simp)]
  rename_i βi
  dsimp only at hout
  split at hout
  on_goal 2 => exact absurd hout (by simp)
  rename_i hαβ
  rw [Option.some_inj] at hout
  injection hout with U_eq hτeq
  subst U
  simp only [heq_eq_eq, PSigma.mk.injEq, BType.set.injEq] at hτeq
  obtain ⟨hτeq, _⟩ := hτeq
  subst αi
  subst βi
  refine ⟨F, G, hF, hG, ?_, ?_, ?_⟩
  · simpa only [proof_irrel_heq] using denS
  · simpa only [proof_irrel_heq] using denT
  · rfl

set_option maxHeartbeats 5000000 in
theorem encodeTerm_rep_spec.inter_case.{u}
    (S T : B.Term)
    (S_ih : EncodeTermRepIH.{u} S)
    (T_ih : EncodeTermRepIH.{u} T)
    (E : B.Env) {Λ : SMT.TypeContext} {α : BType}
    (typ_t : E.context ⊢ᴮ S ∩ᴮ T : α)
    {«Δ» : B.RenamingContext.Context}
    (Δ_fv : ∀ v ∈ B.fv (S ∩ᴮ T), («Δ» v).isSome = true)
    {Δ₀ : SMT.RenamingContext.Context.{u}}
    (related : RValuationCastSupportedOnFV «Δ» Δ₀ (S ∩ᴮ T))
    {used : List SMT.𝒱}
    (Δ₀_none_out : ∀ v ∉ used, Δ₀ v = none)
    (Δ₀_dom : ∀ v, Δ₀ v ≠ none → v ∈ Λ)
    {U : ZFSet.{u}} {hU : U ∈ ⟦α⟧ᶻ}
    (den_t : ⟦(S ∩ᴮ T).abstract «Δ» Δ_fv⟧ᴮ =
      some ⟨U, ⟨α, hU⟩⟩)
    (vars_used : ∀ v ∈ (S ∩ᴮ T).vars, v ∈ used)
    (Λ_inv : ∀ v ∈ (S ∩ᴮ T).vars, v ∈ Λ → v ∈ E.context)
    (bv_nodup : (B.bv (S ∩ᴮ T)).Nodup)
    (respects : B.RenamingContext.RespectsTypeContextOnFV
      Δ₀ Λ (S ∩ᴮ T))
    (fv_in_Λ : ∀ v ∈ B.fv (S ∩ᴮ T), v ∈ Λ)
    (wf : B.RenWF E.context «Δ»)
    {n : ℕ} :
    ⦃fun ⟨E0, Λ'⟩ ↦
      ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧
        Λ.keys ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
    encodeTerm (S ∩ᴮ T) E
    ⦃⇓? (⟨t', σ⟩ : SMT.Term × SMTType) ⟨E', Γ'⟩ =>
      ⌜EncodeTermRepPost (S ∩ᴮ T) α Λ «Δ» Δ₀ used U hU
        E t' σ E' Γ'⌝⦄ := by
  mstart
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
  rw [encodeTerm_inter_via_maplet]

  obtain ⟨τ, rfl, typ_S, typ_T⟩ := B.Typing.interE typ_t
  obtain ⟨F, G, hF, hG, den_S, den_T, rfl⟩ :=
    denote_inter_inv_rep Δ_fv den_t

  let Δ_fv_pair : ∀ v ∈ B.fv (S ↦ᴮ T), («Δ» v).isSome = true :=
    fun v hv => Δ_fv v (by simpa [B.fv] using hv)
  have den_pair :
      ⟦(S ↦ᴮ T).abstract «Δ» Δ_fv_pair⟧ᴮ =
        some ⟨F.pair G,
          ⟨BType.set τ ×ᴮ BType.set τ,
            ZFSet.pair_mem_prod.mpr ⟨hF, hG⟩⟩⟩ := by
    rw [B.Term.abstract, B.denote, Option.pure_def,
      Option.bind_eq_bind]
    have den_S' :
        ⟦S.abstract «Δ» (fun v hv => Δ_fv_pair v (by
          rw [B.fv, List.mem_append]
          exact Or.inl hv))⟧ᴮ =
          some ⟨F, ⟨BType.set τ, hF⟩⟩ := by
      simpa only [proof_irrel_heq] using den_S
    have den_T' :
        ⟦T.abstract «Δ» (fun v hv => Δ_fv_pair v (by
          rw [B.fv, List.mem_append]
          exact Or.inr hv))⟧ᴮ =
          some ⟨G, ⟨BType.set τ, hG⟩⟩ := by
      simpa only [proof_irrel_heq] using den_T
    rw [den_S', Option.bind_some, den_T']
    rfl

  mspec (Std.Do.Triple.and _
    (encodeTerm_rep_spec.maplet_case S T S_ih T_ih E
      (B.Typing.maplet typ_S typ_T) Δ_fv_pair
      (by simpa [B.fv] using related)
      Δ₀_none_out Δ₀_dom den_pair
      (fun v hv => vars_used v (by
        simpa [B.Term.vars, B.fv, B.bv] using hv))
      (fun v hv => Λ_inv v (by
        simpa [B.Term.vars, B.fv, B.bv] using hv))
      (by simpa [B.bv] using bv_nodup)
      (by simpa [B.fv] using respects)
      (fun v hv => fv_in_Λ v (by simpa [B.fv] using hv)) wf
      (n := St.env.freshvarsc))
    (encodeTerm_bv_used E (t := S ↦ᴮ T)
      (used := St.env.usedVars) (n := St.env.freshvarsc)
      (decl := St.env.declarations)))
  rename_i out_pair
  obtain ⟨p, σp⟩ := out_pair
  mrename_i pre
  mintro ∀Stp
  mpure pre
  dsimp at pre
  obtain ⟨maplet_post, bv_pair_used, _bv_used_sub, _bv_delta⟩ := pre
  obtain ⟨used_sub, types_sub, keys_sub, covers_used,
    _path_pair, typ_pair, shape_pair, preserves,
    Δp, hcov_pair, Δp_ext, related_p, Δp_none, respects_p,
    target_respects_p, Δp_dom,
    denPair, hden_pair, hdenPair_type, pair_rel, pair_total⟩ :=
    maplet_post
  obtain ⟨Senc, Tenc, σS_shape, σT_shape, hp, hσp⟩ := shape_pair
  subst p
  subst σp
  focus
    rw [hσp] at typ_pair pair_total
    rw [hσp]
    obtain ⟨σS, σT, hpair_type, typ_Senc, typ_Tenc⟩ :=
      SMT.Typing.pairE typ_pair
    injection hpair_type with hσS_type hσT_type
    subst σS
    subst σT

    have hcov_Senc : RenamingContext.CoversFV Δp Senc := by
      intro v hv
      exact hcov_pair v (by
        rw [SMT.fv, List.mem_append]
        exact Or.inl hv)
    have hcov_Tenc : RenamingContext.CoversFV Δp Tenc := by
      intro v hv
      exact hcov_pair v (by
        rw [SMT.fv, List.mem_append]
        exact Or.inr hv)
    have target_respects_Senc :
        SMT.RenamingContext.RespectsTypeContextOnFV
          Δp Stp.types Senc := by
      intro v ξ hv hlookup
      exact target_respects_p (by
        rw [SMT.fv, List.mem_append]
        exact Or.inl hv) hlookup
    have target_respects_Tenc :
        SMT.RenamingContext.RespectsTypeContextOnFV
          Δp Stp.types Tenc := by
      intro v ξ hv hlookup
      exact target_respects_p (by
        rw [SMT.fv, List.mem_append]
        exact Or.inr hv) hlookup
    obtain ⟨denS, denT, hden_Senc, hden_Tenc, denPair_eq⟩ :=
      denote_pair_inv_inter hcov_pair hden_pair
    rw [denPair_eq] at hσp pair_rel
    rcases denS with ⟨Fenc, τS, hFenc⟩
    rcases denT with ⟨Genc, τT, hGenc⟩
    dsimp at hσp
    injection hσp with hτS hτT
    subst τS
    subst τT
    have component_rel := RDomCast.of_pair
      (hX := hF) (hY := hG) (hX' := hFenc) (hY' := hGenc)
      (by simpa using pair_rel.toRDomCast)
    obtain ⟨σS_supported, σT_supported, hsupported_pair,
        supported_S, supported_T⟩ := pair_rel.supported.prodE
    injection hsupported_pair with hsupported_S hsupported_T
    subst σS_supported
    subst σT_supported
    have bv_Senc_used : ∀ v ∈ SMT.bv Senc, v ∈ Stp.env.usedVars := by
      intro v hv
      exact bv_pair_used v (by
        rw [SMT.bv, List.mem_append]
        exact Or.inl hv)
    have bv_Tenc_used : ∀ v ∈ SMT.bv Tenc, v ∈ Stp.env.usedVars := by
      intro v hv
      exact bv_pair_used v (by
        rw [SMT.bv, List.mem_append]
        exact Or.inr hv)

    mspec castInter_supported_rep_contract τ Senc Tenc
      σS_shape σT_shape
      supported_S supported_T
      typ_Senc typ_Tenc bv_Senc_used bv_Tenc_used
    rename_i out_inter
    obtain ⟨Uenc, σU⟩ := out_inter
    mrename_i post_inter
    mintro ∀Stu
    mpure post_inter
    obtain ⟨used_sub_u, types_sub_u, keys_sub_u, path_u, typ_Uenc,
      preserves_u, semantic_u⟩ := post_inter
    obtain ⟨Δu, hcov_Uenc, denU, Δu_ext, Δu_none,
        target_respects_Uenc, Δu_dom, hden_Uenc, hdenU_type,
        U_rel⟩ :=
      semantic_u Δp hcov_Senc hcov_Tenc Δp_none
        target_respects_Senc target_respects_Tenc Δp_dom
        F G hF hG
        (⟨Fenc, σS_shape, hFenc⟩ : SMT.Dom)
        (⟨Genc, σT_shape, hGenc⟩ : SMT.Dom)
        hden_Senc hden_Tenc component_rel.1 component_rel.2
    have Δu_ext₀ := RenamingContext.extends_trans Δu_ext Δp_ext
    have types_sub₀ : St.types ⊆ Stu.types :=
      fun _ h => types_sub_u (types_sub h)

    mpure_intro
    and_intros
    · intro v hv
      exact used_sub_u (used_sub (by simpa [St_used_eq] using hv))
    · exact types_sub₀
    · exact keys_sub_u
    · simpa [B.fv] using
        (B.CoversUsedVars.mono used_sub_u covers_used)
    · exact path_u
    · exact typ_Uenc
    · trivial
    · intro v hv hΛ hvars
      apply preserves_u v (used_sub (by simpa [St_used_eq] using hv))
      exact preserves v (by simpa [St_used_eq] using hv) hΛ
        (by simpa [B.Term.vars, B.fv, B.bv] using hvars)
    · refine ⟨Δu, hcov_Uenc, Δu_ext₀,
        related.of_extends Δu_ext₀, Δu_none, ?_,
        target_respects_Uenc, Δu_dom, denU, hden_Uenc,
        hdenU_type, ?_, ?_⟩
      · exact respects.of_extends Δu_ext₀ types_sub₀
          (fun _ h => h) fv_in_Λ
      · simpa only [proof_irrel_heq] using U_rel
      · intro Δ_alt Δ_fv_alt Δ₀_alt related_alt wf_alt
          Δ₀_alt_none respects_alt Δ₀_alt_dom U_alt hU_alt den_t_alt
        obtain ⟨F_alt, G_alt, hF_alt, hG_alt,
            den_S_alt, den_T_alt, rfl⟩ :=
          denote_inter_inv_rep Δ_fv_alt den_t_alt
        let Δ_fv_pair_alt :
            ∀ v ∈ B.fv (S ↦ᴮ T), (Δ_alt v).isSome = true :=
          fun v hv => Δ_fv_alt v (by simpa [B.fv] using hv)
        have den_pair_alt :
            ⟦(S ↦ᴮ T).abstract Δ_alt Δ_fv_pair_alt⟧ᴮ =
              some ⟨F_alt.pair G_alt,
                ⟨BType.set τ ×ᴮ BType.set τ,
                  ZFSet.pair_mem_prod.mpr ⟨hF_alt, hG_alt⟩⟩⟩ := by
          rw [B.Term.abstract, B.denote, Option.pure_def,
            Option.bind_eq_bind]
          have den_S_alt' :
              ⟦S.abstract Δ_alt (fun v hv => Δ_fv_pair_alt v (by
                rw [B.fv, List.mem_append]
                exact Or.inl hv))⟧ᴮ =
                some ⟨F_alt, ⟨BType.set τ, hF_alt⟩⟩ := by
            simpa only [proof_irrel_heq] using den_S_alt
          have den_T_alt' :
              ⟦T.abstract Δ_alt (fun v hv => Δ_fv_pair_alt v (by
                rw [B.fv, List.mem_append]
                exact Or.inr hv))⟧ᴮ =
                some ⟨G_alt, ⟨BType.set τ, hG_alt⟩⟩ := by
            simpa only [proof_irrel_heq] using den_T_alt
          rw [den_S_alt', Option.bind_some, den_T_alt']
          rfl
        have Δ₀_alt_none_pair : ∀ v ∉ Stp.env.usedVars,
            Δ₀_alt v = none := by
          intro v hv
          by_contra hne
          have hv_Λ := Δ₀_alt_dom v hne
          have hv_used : v ∈ used := by
            rw [← St_used_eq]
            exact St_sub hv_Λ
          exact hv (used_sub hv_used)
        obtain ⟨Δp_alt, hcov_pair_alt, denPairAlt, Δp_alt_ext,
            related_p_alt, Δp_alt_none, respects_p_alt,
            target_respects_p_alt, Δp_alt_dom,
            hden_pair_alt, hdenPairAlt_type, pair_alt_rel⟩ :=
          pair_total Δ_alt Δ_fv_pair_alt Δ₀_alt
            (by simpa [B.fv] using related_alt) wf_alt
            Δ₀_alt_none_pair (by simpa [B.fv] using respects_alt)
            Δ₀_alt_dom (F_alt.pair G_alt)
            (ZFSet.pair_mem_prod.mpr ⟨hF_alt, hG_alt⟩)
            den_pair_alt
        have hcov_Senc_alt : RenamingContext.CoversFV Δp_alt Senc := by
          intro v hv
          exact hcov_pair_alt v (by
            rw [SMT.fv, List.mem_append]
            exact Or.inl hv)
        have hcov_Tenc_alt : RenamingContext.CoversFV Δp_alt Tenc := by
          intro v hv
          exact hcov_pair_alt v (by
            rw [SMT.fv, List.mem_append]
            exact Or.inr hv)
        have target_respects_Senc_alt :
            SMT.RenamingContext.RespectsTypeContextOnFV
              Δp_alt Stp.types Senc := by
          intro v ξ hv hlookup
          exact target_respects_p_alt (by
            rw [SMT.fv, List.mem_append]
            exact Or.inl hv) hlookup
        have target_respects_Tenc_alt :
            SMT.RenamingContext.RespectsTypeContextOnFV
              Δp_alt Stp.types Tenc := by
          intro v ξ hv hlookup
          exact target_respects_p_alt (by
            rw [SMT.fv, List.mem_append]
            exact Or.inr hv) hlookup
        obtain ⟨denSAlt, denTAlt, hden_Senc_alt,
            hden_Tenc_alt, denPairAlt_eq⟩ :=
          denote_pair_inv_inter hcov_pair_alt hden_pair_alt
        rw [denPairAlt_eq] at hdenPairAlt_type pair_alt_rel
        rcases denSAlt with ⟨Fenc_alt, τS_alt, hFenc_alt⟩
        rcases denTAlt with ⟨Genc_alt, τT_alt, hGenc_alt⟩
        dsimp at hdenPairAlt_type
        injection hdenPairAlt_type with hτS_alt hτT_alt
        subst τS_alt
        subst τT_alt
        have component_alt_rel := RDomCast.of_pair
          (hX := hF_alt) (hY := hG_alt)
          (hX' := hFenc_alt) (hY' := hGenc_alt)
          (by simpa using pair_alt_rel.toRDomCast)
        obtain ⟨Δu_alt, hcov_Uenc_alt, denU_alt, Δu_alt_ext,
            Δu_alt_none, target_respects_Uenc_alt, Δu_alt_dom,
            hden_Uenc_alt, hdenU_alt_type, U_alt_rel⟩ :=
          semantic_u Δp_alt hcov_Senc_alt hcov_Tenc_alt
            Δp_alt_none target_respects_Senc_alt
            target_respects_Tenc_alt Δp_alt_dom
            F_alt G_alt hF_alt hG_alt
            (⟨Fenc_alt, σS_shape, hFenc_alt⟩ : SMT.Dom)
            (⟨Genc_alt, σT_shape, hGenc_alt⟩ : SMT.Dom)
            hden_Senc_alt hden_Tenc_alt
            component_alt_rel.1 component_alt_rel.2
        have Δu_alt_ext₀ :=
          RenamingContext.extends_trans Δu_alt_ext Δp_alt_ext
        refine ⟨Δu_alt, hcov_Uenc_alt, denU_alt, Δu_alt_ext₀,
          related_alt.of_extends Δu_alt_ext₀, Δu_alt_none, ?_,
          target_respects_Uenc_alt, Δu_alt_dom,
          hden_Uenc_alt, hdenU_alt_type, ?_⟩
        · exact respects_alt.of_extends Δu_alt_ext₀ types_sub₀
            (fun _ h => h) fv_in_Λ
        · simpa only [proof_irrel_heq] using U_alt_rel
