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

theorem set_union_mem.{u} {τ : BType} {F G : ZFSet.{u}}
    (hF : F ∈ ⟦BType.set τ⟧ᶻ)
    (hG : G ∈ ⟦BType.set τ⟧ᶻ) :
    F ∪ G ∈ ⟦BType.set τ⟧ᶻ := by
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

/- The direct characteristic-predicate branch is Δ-universal.  This is the
contract used by the full union constructor both for its current denotation
and for the alternative-valuation totality clause. -/
set_option maxHeartbeats 1600000 in
@[spec]
theorem castUnion_direct_rep_spec.{u}
    (τ : BType) {S T : SMT.Term}
    {Λ : SMT.TypeContext} {n : ℕ} {used : List SMT.𝒱}
    (typ_S : Λ ⊢ˢ S : SMTType.fun τ.toSMTType SMTType.bool)
    (typ_T : Λ ⊢ˢ T : SMTType.fun τ.toSMTType SMTType.bool)
    (bv_S_used : ∀ v ∈ SMT.bv S, v ∈ used)
    (bv_T_used : ∀ v ∈ SMT.bv T, v ∈ used) :
    ⦃ fun ⟨E, Λ'⟩ =>
      ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ Λ.keys ⊆ E.usedVars ∧
        E.usedVars = used⌝ ⦄
    castUnion
      ⟨S, SMTType.fun τ.toSMTType SMTType.bool⟩
      ⟨T, SMTType.fun τ.toSMTType SMTType.bool⟩
    ⦃ ⇓? ⟨t, σ⟩ ⟨E', Γ'⟩ =>
      ⌜used ⊆ E'.usedVars ∧
        Λ ⊆ Γ' ∧
        Γ'.keys ⊆ E'.usedVars ∧
        σ = SMTType.fun τ.toSMTType SMTType.bool ∧
        Γ' ⊢ˢ t : SMTType.fun τ.toSMTType SMTType.bool ∧
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
              RDomCastAdmissible
                (⟨F ∪ G, BType.set τ, set_union_mem hF hG⟩ : B.Dom)
                denU⌝ ⦄ := by
  have hcastUnion :
      castUnion
        (S, SMTType.fun τ.toSMTType SMTType.bool)
        (T, SMTType.fun τ.toSMTType SMTType.bool) = do
        let z ← SMT.freshVar τ.toSMTType "union!"
        SMT.eraseFromContext z
        return (.lambda [z] [τ.toSMTType]
          (.or (.app S (.var z)) (.app T (.var z))),
          SMTType.fun τ.toSMTType SMTType.bool) := by
    unfold castUnion
    simp
  rw [hcastUnion]
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
        erase_insert_self_rep_union z_fresh]
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
      refine SMT.Typing.lambda St₀.types [z] [τ.toSMTType]
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
            TypeContext.update St₀.types [z] [τ.toSMTType] rfl =
              St₀.types.insert z τ.toSMTType := by
          simp only [TypeContext.update, List.length_cons, List.length_nil,
            zero_add, Nat.reduceAdd, Fin.cast_eq_self, Fin.getElem_fin,
            Fin.val_eq_zero, List.getElem_cons_zero, Fin.foldl_succ,
            Fin.foldl_zero]
        rw [hupdate]
        apply SMT.Typing.or
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
          (.lambda [z] [τ.toSMTType]
            (.or (.app S (.var z)) (.app T (.var z)))) := by
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
            (.lambda [z] [τ.toSMTType]
              (.or (.app S (.var z)) (.app T (.var z)))) := by
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
      obtain ⟨denU, hdenU, denU_type, hretU⟩ :=
        castUnion_denotation_direct hS hT hdenS hdenT
          denS_type denT_type z_not_fv_S z_not_fv_T hcov_out
      have hFret := ((RDomCast.iff_RDom_of_type_eq
        (α := BType.set τ) (σ := denS.snd.fst) denS_type).mp
        F_rel).2
      have hGret := ((RDomCast.iff_RDom_of_type_eq
        (α := BType.set τ) (σ := denT.snd.fst) denT_type).mp
        G_rel).2
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
      · rcases denU with ⟨U, σU, hU⟩
        dsimp at denU_type
        subst σU
        refine ⟨castPath.reflexive
          (SMTType.fun τ.toSMTType SMTType.bool), ?_, ?_⟩
        · rw [castZF_apply_reflexive _ hU, hretU τ rfl,
            hFret, hGret]
        · exact ⟨castPath.reflexive τ.toSMTType,
            BinderCastAdmissible.reflexive τ (set_union_mem hF hG)⟩

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
      RDomCastAdmissible
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
    (SMTType.fun (SMTType.pair α.toSMTType β.toSMTType) SMTType.bool),
    ?_, ?_⟩
  · rw [castZF_apply_reflexive _ hUval, hU_retract', hS!_retract,
      hG_retract]
  · exact ⟨castPath.reflexive (α ×ᴮ β).toSMTType,
      BinderCastAdmissible.reflexive (α ×ᴮ β)
        (relation_union_mem hF hG)⟩

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
    (bv_T_used : ∀ v ∈ SMT.bv T, v ∈ used) :
    ⦃ fun ⟨E, Λ'⟩ =>
      ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ Λ.keys ⊆ E.usedVars ∧
        E.usedVars = used⌝ ⦄
    castUnion
      ⟨S, SMTType.fun α.toSMTType (SMTType.option β.toSMTType)⟩
      ⟨T, SMTType.fun (SMTType.pair α.toSMTType β.toSMTType) SMTType.bool⟩
    ⦃ ⇓? ⟨t, σ⟩ ⟨E', Γ'⟩ =>
      ⌜used ⊆ E'.usedVars ∧
        Λ ⊆ Γ' ∧
        Γ'.keys ⊆ E'.usedVars ∧
        σ = SMTType.fun (SMTType.pair α.toSMTType β.toSMTType)
          SMTType.bool ∧
        Γ' ⊢ˢ t : SMTType.fun
          (SMTType.pair α.toSMTType β.toSMTType) SMTType.bool ∧
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
              RDomCastAdmissible
                (⟨F ∪ G, BType.set (α ×ᴮ β),
                  relation_union_mem hF hG⟩ : B.Dom) denU⌝ ⦄ := by
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
  mspec loosenAux_prf_spec_univ (Λ := St₀.types)
    (n := St₀.env.freshvarsc)
    (used := St₀.env.usedVars) typ_S bv_S_used
    (castPath.graph (castPath.reflexive α.toSMTType)
      (castPath.reflexive β.toSMTType))
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
            (.lambda [z] [SMTType.pair α.toSMTType β.toSMTType]
              (.or (.app (.var S!) (.var z)) (.app T (.var z)))) := by
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
        obtain ⟨denU, h_den_U, U_rel⟩ :=
          castUnion_graph_denotation α β hF hG denS_type denS!_type
            denT_type F_rel G_rel cast_pair
            hS!_helper hT_helper h_den_S!_helper h_den_T_helper
            z_not_fv_S! z_not_fv_T hcov_out
        have typ_S!_St₅ : St₅.types ⊢ˢ SMT.Term.var S! :
            SMTType.fun (SMTType.pair α.toSMTType β.toSMTType)
              SMTType.bool := by
          rw [St₅_types_eq', St₃_types_eq, St₂_types_eq]
          exact typ_S!_St₁
        have respects_T_final :
            SMT.RenamingContext.RespectsTypeContextOnFV
              Δhelper St₅.types T :=
          respects_T.of_extends Δhelper_ext Λ_sub_final typ_T
        have target_respects_out :
            SMT.RenamingContext.RespectsTypeContextOnFV Δhelper St₅.types
              (.lambda [z] [SMTType.pair α.toSMTType β.toSMTType]
                (.or (.app (.var S!) (.var z)) (.app T (.var z)))) := by
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

/-! ## Constructor-facing union-helper contract -/

/-- Representation-aware contract required from `castUnion` after both source
operands have been encoded.  It is intentionally quantified over valuations
and denotations so one operational run serves the current and totality proofs. -/
abbrev CastUnionRepSpec.{u} (τ : BType)
    (S T : SMT.Term) (σS σT : SMTType) : Prop :=
  ∀ {Λ : SMT.TypeContext} {n : ℕ} {used : List SMT.𝒱},
    Λ ⊢ˢ S : σS →
    Λ ⊢ˢ T : σT →
    (∀ v ∈ SMT.bv S, v ∈ used) →
    (∀ v ∈ SMT.bv T, v ∈ used) →
    ⦃ fun ⟨E, Λ'⟩ =>
      ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ Λ.keys ⊆ E.usedVars ∧
        E.usedVars = used⌝ ⦄
    castUnion ⟨S, σS⟩ ⟨T, σT⟩
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
              RDomCastAdmissible
                (⟨F ∪ G, BType.set τ, set_union_mem hF hG⟩ : B.Dom)
                denU⌝ ⦄

theorem castUnion_direct_rep_contract.{u} (τ : BType)
    (S T : SMT.Term) :
    CastUnionRepSpec.{u} τ S T
      (SMTType.fun τ.toSMTType SMTType.bool)
      (SMTType.fun τ.toSMTType SMTType.bool) := by
  unfold CastUnionRepSpec
  intro Λ n used typ_S typ_T bv_S_used bv_T_used
  mstart
  mintro pre ∀St
  mpure pre
  mspec castUnion_direct_rep_spec τ typ_S typ_T bv_S_used bv_T_used
  rename_i out
  obtain ⟨t, σ⟩ := out
  mrename_i post
  mintro ∀St'
  mpure post
  obtain ⟨used_sub, types_sub, keys_sub, σ_eq, typ_out,
    preserves, semantic⟩ := post
  change σ = SMTType.fun τ.toSMTType SMTType.bool at σ_eq
  subst σ
  mpure_intro
  exact ⟨used_sub, types_sub, keys_sub,
    ⟨castPath.reflexive (BType.set τ).toSMTType⟩,
    typ_out, preserves, semantic⟩

theorem castUnion_graph_rep_contract.{u}
    (α β : BType) (S T : SMT.Term) :
    CastUnionRepSpec.{u} (α ×ᴮ β) S T
      (SMTType.fun α.toSMTType (SMTType.option β.toSMTType))
      (SMTType.fun (SMTType.pair α.toSMTType β.toSMTType)
        SMTType.bool) := by
  unfold CastUnionRepSpec
  intro Λ n used typ_S typ_T bv_S_used bv_T_used
  mstart
  mintro pre ∀St
  mpure pre
  mspec castUnion_graph_rep_spec α β typ_S typ_T
    bv_S_used bv_T_used
  rename_i out
  obtain ⟨t, σ⟩ := out
  mrename_i post
  mintro ∀St'
  mpure post
  obtain ⟨used_sub, types_sub, keys_sub, σ_eq, typ_out,
    preserves, semantic⟩ := post
  change σ = SMTType.fun (SMTType.pair α.toSMTType β.toSMTType)
    SMTType.bool at σ_eq
  subst σ
  mpure_intro
  exact ⟨used_sub, types_sub, keys_sub,
    ⟨castPath.reflexive (BType.set (α ×ᴮ β)).toSMTType⟩,
    typ_out, preserves, semantic⟩
