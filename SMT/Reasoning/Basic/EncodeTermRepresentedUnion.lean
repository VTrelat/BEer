import SMT.Reasoning.Basic.EncodeTermRepresentedBase
import SMT.Reasoning.Basic.EncodeTermCorrectUnion

open Std.Do B SMT ZFSet

/-! # Representation-aware heterogeneous union -/

theorem relation_union_mem.{u} {α β : BType} {F G : ZFSet.{u}}
    (hF : F ∈ ⟦BType.set (α ×ᴮ β)⟧ᶻ)
    (hG : G ∈ ⟦BType.set (α ×ᴮ β)⟧ᶻ) :
    F ∪ G ∈ ⟦BType.set (α ×ᴮ β)⟧ᶻ := by
  rw [BType.toZFSet, ZFSet.mem_powerset] at hF hG ⊢
  intro x hx
  rw [ZFSet.mem_union] at hx
  exact hx.elim (fun hxF => hF hxF) (fun hxG => hG hxG)

private theorem erase_insert_self_rep_union {a : SMT.𝒱} {τ : SMTType}
    {s : SMT.TypeContext} (ha : a ∉ s) : (s.insert a τ).erase a = s := by
  apply AList.ext
  show List.kerase a (AList.insert a τ s).entries = s.entries
  rw [AList.entries_insert_of_notMem ha]
  exact List.kerase_cons_eq rfl

/-- Semantic core of Gate B.  The helper produced by `loosenAux_prf` denotes
the graph cast of the option-valued function, and the lambda returned by
`castUnion.graph` therefore retracts to the union of the two source
relations. -/
theorem castUnion_graph_denotation.{u}
    (α β : BType) {F G : ZFSet.{u}}
    (hF : F ∈ ⟦BType.set (α ×ᴮ β)⟧ᶻ)
    (hG : G ∈ ⟦BType.set (α ×ᴮ β)⟧ᶻ)
    {S! z : SMT.𝒱} {T : SMT.Term}
    {«Δ» : SMT.RenamingContext.Context.{u}}
    {denS denS! denT : SMT.Dom.{u}}
    (denS_type : denS.snd.fst =
      SMTType.fun α.toSMTType (SMTType.option β.toSMTType))
    (denS!_type : denS!.snd.fst =
      SMTType.fun (SMTType.pair α.toSMTType β.toSMTType) SMTType.bool)
    (denT_type : denT.snd.fst =
      SMTType.fun (SMTType.pair α.toSMTType β.toSMTType) SMTType.bool)
    (F_rel : RDomCast (⟨F, BType.set (α ×ᴮ β), hF⟩ : B.Dom) denS)
    (G_rel : RDomCast (⟨G, BType.set (α ×ᴮ β), hG⟩ : B.Dom) denT)
    (cast_pair : denS.fst.pair denS!.fst ∈
      (castZF_of_path (castPath.graph
        (castPath.reflexive α.toSMTType)
        (castPath.reflexive β.toSMTType))).1)
    (hS! : RenamingContext.CoversFV «Δ» (SMT.Term.var S!))
    (hT : RenamingContext.CoversFV «Δ» T)
    (h_den_S! : ⟦(SMT.Term.var S!).abstract «Δ» hS!⟧ˢ = some denS!)
    (h_den_T : ⟦T.abstract «Δ» hT⟧ˢ = some denT)
    (z_not_fv_S! : z ∉ SMT.fv (SMT.Term.var S!))
    (z_not_fv_T : z ∉ SMT.fv T)
    (hcov : RenamingContext.CoversFV «Δ»
      (.lambda [z] [SMTType.pair α.toSMTType β.toSMTType]
        (.or (.app (.var S!) (.var z)) (.app T (.var z))))) :
    ∃ denU : SMT.Dom.{u},
      ⟦(SMT.Term.lambda [z] [SMTType.pair α.toSMTType β.toSMTType]
        (.or (.app (.var S!) (.var z)) (.app T (.var z)))).abstract
          «Δ» hcov⟧ˢ = some denU ∧
      RDomCast
        (⟨F ∪ G, BType.set (α ×ᴮ β), relation_union_mem hF hG⟩ : B.Dom)
        denU := by
  rcases denS with ⟨Sval, σS, hSval⟩
  rcases denS! with ⟨S!val, σS!, hS!val⟩
  rcases denT with ⟨Tval, σT, hTval⟩
  dsimp at denS_type denS!_type denT_type
  subst σS
  subst σS!
  subst σT
  have hgraph :
      optionGraph α.toSMTType β.toSMTType Sval = S!val :=
    castZF_apply_eq_of_pair
      (castPath.graph (castPath.reflexive α.toSMTType)
        (castPath.reflexive β.toSMTType)) hSval cast_pair
  have hF_retract :
      retract (BType.set (α ×ᴮ β))
        (optionGraph α.toSMTType β.toSMTType Sval) = F :=
    RDomCast.optionFunction_graph_retract F_rel
  have hS!_retract : retract (BType.set (α ×ᴮ β)) S!val = F := by
    rw [← hgraph]
    exact hF_retract
  have hG_retract : retract (BType.set (α ×ᴮ β)) Tval = G :=
    ((RDomCast.iff_RDom_of_type_eq (σ :=
      SMTType.fun (SMTType.pair α.toSMTType β.toSMTType) SMTType.bool)
      rfl).mp G_rel).2
  obtain ⟨denU, hdenU, denU_type, hU_retract⟩ :=
    castUnion_denotation_direct hS! hT h_den_S! h_den_T rfl rfl
      z_not_fv_S! z_not_fv_T hcov
  have hU_retract' := hU_retract (α ×ᴮ β) rfl
  rcases denU with ⟨Uval, σU, hUval⟩
  dsimp at denU_type
  subst σU
  refine ⟨⟨Uval,
      SMTType.fun (SMTType.pair α.toSMTType β.toSMTType) SMTType.bool,
      hUval⟩, hdenU, ?_⟩
  refine ⟨castPath.reflexive
    (SMTType.fun (SMTType.pair α.toSMTType β.toSMTType) SMTType.bool), ?_⟩
  rw [castZF_apply_reflexive _ hUval, hU_retract', hS!_retract,
    hG_retract]

/- Gate B: the real heterogeneous `castUnion` branch, including
`loosenAux_prf`, declaration and assertion of the helper graph, and the
lambda returned by the encoder.  The final denotation represents the source
union even though the left operand starts as an option-valued function. -/
set_option maxHeartbeats 1200000 in
@[spec]
theorem castUnion_graph_rep_spec.{u}
    (α β : BType) {S T : SMT.Term}
    {Λ : SMT.TypeContext} {n : ℕ} {used : List SMT.𝒱}
    (typ_S : Λ ⊢ˢ S :
      SMTType.fun α.toSMTType (SMTType.option β.toSMTType))
    (typ_T : Λ ⊢ˢ T :
      SMTType.fun (SMTType.pair α.toSMTType β.toSMTType) SMTType.bool)
    (bv_S_used : ∀ v ∈ SMT.bv S, v ∈ used)
    (bv_T_used : ∀ v ∈ SMT.bv T, v ∈ used)
    {«Δ» : SMT.RenamingContext.Context.{u}}
    (hS : RenamingContext.CoversFV «Δ» S)
    (hT : RenamingContext.CoversFV «Δ» T)
    (Δ_none_out : ∀ v ∉ used, «Δ» v = none)
    (respects_S :
      SMT.RenamingContext.RespectsTypeContextOnFV «Δ» Λ S)
    (respects_T :
      SMT.RenamingContext.RespectsTypeContextOnFV «Δ» Λ T)
    {F G : ZFSet.{u}}
    (hF : F ∈ ⟦BType.set (α ×ᴮ β)⟧ᶻ)
    (hG : G ∈ ⟦BType.set (α ×ᴮ β)⟧ᶻ)
    {denS denT : SMT.Dom.{u}}
    (h_den_S : ⟦S.abstract «Δ» hS⟧ˢ = some denS)
    (h_den_T : ⟦T.abstract «Δ» hT⟧ˢ = some denT)
    (F_rel : RDomCast (⟨F, BType.set (α ×ᴮ β), hF⟩ : B.Dom) denS)
    (G_rel : RDomCast (⟨G, BType.set (α ×ᴮ β), hG⟩ : B.Dom) denT) :
    ⦃ fun ⟨E, Λ'⟩ =>
      ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ Λ.keys ⊆ E.usedVars ∧
        E.usedVars = used⌝ ⦄
    castUnion
      ⟨S, SMTType.fun α.toSMTType (SMTType.option β.toSMTType)⟩
      ⟨T, SMTType.fun (SMTType.pair α.toSMTType β.toSMTType) SMTType.bool⟩
    ⦃ ⇓? ⟨t, σ⟩ ⟨E', Γ'⟩ =>
      ⌜σ = SMTType.fun (SMTType.pair α.toSMTType β.toSMTType)
          SMTType.bool ∧
        Γ' ⊢ˢ t : SMTType.fun
          (SMTType.pair α.toSMTType β.toSMTType) SMTType.bool ∧
        ∃ (Δ' : SMT.RenamingContext.Context.{u})
          (hcov : RenamingContext.CoversFV Δ' t),
          RenamingContext.Extends Δ' «Δ» ∧
          (∀ v ∉ E'.usedVars, Δ' v = none) ∧
          ∃ denU : SMT.Dom.{u},
            ⟦t.abstract Δ' hcov⟧ˢ = some denU ∧
            RDomCast
              (⟨F ∪ G, BType.set (α ×ᴮ β), relation_union_mem hF hG⟩ :
                B.Dom)
              denU⌝ ⦄ := by
  have hcastUnion :
      castUnion
        (S, SMTType.fun α.toSMTType (SMTType.option β.toSMTType))
        (T, SMTType.fun (SMTType.pair α.toSMTType β.toSMTType) SMTType.bool) =
      castUnion.graph S T (castPath.reflexive α.toSMTType)
        (castPath.reflexive β.toSMTType) := by
    simp only [castUnion]
    rw [dif_neg (by simp)]
    let hα : α.toSMTType ⊑ α.toSMTType := castable?.reflexive
    let hβ : β.toSMTType ⊑ β.toSMTType := castable?.reflexive
    let hgraph :
        SMTType.fun α.toSMTType (SMTType.option β.toSMTType) ⊑
          SMTType.fun (SMTType.pair α.toSMTType β.toSMTType) SMTType.bool :=
      castable?.graph hα hβ
    rw [dif_pos hgraph]
    unfold castUnionAux
    have hpα : hα.toCastPath = castPath.reflexive α.toSMTType :=
      SMTType.castable?_to_castPath_reflexive
    have hpβ : hβ.toCastPath = castPath.reflexive β.toSMTType :=
      SMTType.castable?_to_castPath_reflexive
    have hpath :
        hgraph.toCastPath = castPath.graph (castPath.reflexive α.toSMTType)
          (castPath.reflexive β.toSMTType) := by
      calc
        hgraph.toCastPath = (castable?.graph hα hβ).toCastPath :=
          congrArg castable?.toCastPath (Subsingleton.elim _ _)
        _ = castPath.graph hα.toCastPath hβ.toCastPath :=
          SMTType.castable?_to_castPath_graph hα hβ
        _ = castPath.graph (castPath.reflexive α.toSMTType)
            (castPath.reflexive β.toSMTType) := by rw [hpα, hpβ]
    rw [hpath]
  rw [hcastUnion]
  unfold castUnion.graph
  mintro pre ∀St₀
  mpure pre
  obtain ⟨rfl, rfl, St₀_sub, rfl⟩ := pre
  mspec loosenAux_prf_spec (Λ := St₀.types) (n := St₀.env.freshvarsc)
    (used := St₀.env.usedVars) typ_S bv_S_used
    (castPath.graph (castPath.reflexive α.toSMTType)
      (castPath.reflexive β.toSMTType)) «Δ» hS
    respects_S
  next out =>
    obtain ⟨S!, S!_spec⟩ := out
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨_, St₁_types_sub, S!_fresh, S!_not_used, used_sub₁,
      St₁_keys_sub, preserves₁, _, _, typ_S!_St₁, _, _, adequacy⟩ := pre
    mspec SMT.declareConst_spec (v := S!)
      (τ := SMTType.fun (SMTType.pair α.toSMTType β.toSMTType) SMTType.bool)
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
      (τ := SMTType.pair α.toSMTType β.toSMTType)
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
          erase_insert_self_rep_union z_fresh]
      have typ_T_St₁ : St₁.types ⊢ˢ T :
          SMTType.fun (SMTType.pair α.toSMTType β.toSMTType)
            SMTType.bool :=
        SMT.Typing.weakening
          (h := fun v hv => St₁_types_sub
            (SMT.TypeContext.entries_subset_insert_of_notMem S!_fresh hv))
          typ_T
          (fun v hv => preserves₁ v (bv_T_used v hv)
            (SMT.Typing.bv_notMem_context typ_T v hv))
      have typ_T_St₃ : St₃.types ⊢ˢ T :
          SMTType.fun (SMTType.pair α.toSMTType β.toSMTType)
            SMTType.bool := by
        rwa [St₃_types_eq, St₂_types_eq]
      have typ_S!_St₃ : St₃.types ⊢ˢ SMT.Term.var S! :
          SMTType.fun (SMTType.pair α.toSMTType β.toSMTType)
            SMTType.bool := by
        rwa [St₃_types_eq, St₂_types_eq]
      have z_not_bv_T : z ∉ SMT.bv T := by
        intro hz
        apply z_not_used
        rw [St₃_used_eq, St₂_used_eq]
        exact used_sub₁ (bv_T_used z hz)
      have typ_out : St₅.types ⊢ˢ
          SMT.Term.lambda [z]
            [SMTType.pair α.toSMTType β.toSMTType]
            (.or (.app (.var S!) (.var z)) (.app T (.var z))) :
          SMTType.fun (SMTType.pair α.toSMTType β.toSMTType)
            SMTType.bool := by
        rw [St₅_types_eq']
        refine SMT.Typing.lambda St₃.types [z]
          [SMTType.pair α.toSMTType β.toSMTType] _ SMTType.bool
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
                [SMTType.pair α.toSMTType β.toSMTType] rfl =
              St₃.types.insert z
                (SMTType.pair α.toSMTType β.toSMTType) := by
            simp only [TypeContext.update, List.length_cons, List.length_nil,
              zero_add, Nat.reduceAdd, Fin.cast_eq_self, Fin.getElem_fin,
              Fin.val_eq_zero, List.getElem_cons_zero, Fin.foldl_succ,
              Fin.foldl_zero]
          rw [hupdate]
          apply SMT.Typing.or
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
      obtain ⟨Φ, denS!, h_den_var, _hφ, _h_den_φ, denS!_type,
        _Φ_type, ⟨_Φ_true, cast_pair⟩, _helper_total⟩ :=
        adequacy denS h_den_S
      let Δhelper := Function.update «Δ» S! (some denS!)
      have Δ_S!_none : «Δ» S! = none := Δ_none_out S! S!_not_used
      have hS!_not_fv_T : S! ∉ SMT.fv T :=
        funNotMemFvOfNotMemContext typ_T S!_fresh
      have hT_helper : RenamingContext.CoversFV Δhelper T :=
        SMT.RenamingContext.coversFV_update_of_notMem hS!_not_fv_T hT
      have h_den_T_helper : ⟦T.abstract Δhelper hT_helper⟧ˢ = some denT := by
        have heq : ⟦T.abstract «Δ» hT⟧ˢ =
            ⟦T.abstract Δhelper hT_helper⟧ˢ := by
          rw [← SMT.RenamingContext.denote, ← SMT.RenamingContext.denote]
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
          (.lambda [z] [SMTType.pair α.toSMTType β.toSMTType]
            (.or (.app (.var S!) (.var z)) (.app T (.var z)))) := by
        intro v hv
        simp only [SMT.fv, List.removeAll, List.mem_filter, List.mem_append,
          List.mem_cons, List.not_mem_nil, or_false] at hv
        obtain ⟨hv_body, hv_ne_z⟩ := hv
        simp only [List.elem_eq_contains, List.contains_eq_mem, List.mem_cons,
          List.not_mem_nil, or_false, Bool.not_eq_true',
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
      obtain ⟨denU, h_den_U, U_rel⟩ :=
        castUnion_graph_denotation α β hF hG denS_type denS!_type
          denT_type F_rel G_rel cast_pair hS!_helper hT_helper
          h_den_S!_helper h_den_T_helper z_not_fv_S! z_not_fv_T hcov_out
      mspec Std.Do.Spec.pure
      mpure_intro
      refine ⟨by trivial, typ_out, Δhelper, hcov_out, ?_, ?_, denU,
        h_den_U, U_rel⟩
      · exact RenamingContext.extends_update_of_none Δ_S!_none
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
          apply Δ_none_out
          intro hv_used
          exact hv_not_St₁ (used_sub₁ hv_used)
