import SMT.Reasoning.Basic.EncodeTermRepresentedScopedMaplet
import SMT.Reasoning.Basic.EncodeTermRepresentedUnion
import SMT.Reasoning.Basic.EncodeTermRepresentedMem
import SMT.Reasoning.Basic.LoosenAuxExactUniv

open Std.Do B SMT ZFSet Classical

/-! # Generated-helper contract for represented union -/

/-- Soundness of a completed union cast under an arbitrary valuation of its
generated helpers. -/
abbrev CastUnionRepGuardedSemantics.{u}
    (τ : BType) (S T out : SMT.Term) (σS σT σout : SMTType)
    (Λ : SMT.TypeContext) (Dlt : SMT.Chunk) : Prop :=
  ∀ (Γsup : SMT.TypeContext), ScopedContextExtends Λ Dlt Γsup →
    ∀ (Θ : SMT.RenamingContext.Context.{u})
      (hcovS : RenamingContext.CoversFV Θ S)
      (hcovT : RenamingContext.CoversFV Θ T),
      SMT.RenamingContext.RespectsTypeContextOnFV Θ Γsup S →
      SMT.RenamingContext.RespectsTypeContextOnFV Θ Γsup T →
      ∀ (F G : ZFSet.{u})
        (hF : F ∈ ⟦BType.set τ⟧ᶻ)
        (hG : G ∈ ⟦BType.set τ⟧ᶻ)
        (denS denT : SMT.Dom.{u}),
        ⟦S.abstract Θ hcovS⟧ˢ = some denS →
        ⟦T.abstract Θ hcovT⟧ˢ = some denT →
        denS.snd.fst = σS → denT.snd.fst = σT →
        RDomCastSupported (⟨F, BType.set τ, hF⟩ : B.Dom) denS →
        RDomCastSupported (⟨G, BType.set τ, hG⟩ : B.Dom) denT →
        ∀ (hcovOut : RenamingContext.CoversFV Θ out)
          (denOut : SMT.Dom.{u}),
          SMT.RenamingContext.RespectsTypeContextOnFV Θ Γsup out →
          SpecBodiesTrue Θ Γsup Dlt →
          ⟦out.abstract Θ hcovOut⟧ˢ = some denOut →
          denOut.snd.fst = σout →
          RDomCastSupported
            (⟨F ∪ G, BType.set τ, set_union_mem hF hG⟩ : B.Dom)
            denOut

/-- Satisfying-assignment construction paired with guarded soundness. -/
abbrev CastUnionRepSemantics.{u}
    (τ : BType) (S T out : SMT.Term) (σS σT σout : SMTType)
    (Λ Γ : SMT.TypeContext) (used₀ used₁ : List SMT.𝒱)
    (Dlt : SMT.Chunk) : Prop :=
  (∀ (Θ : SMT.RenamingContext.Context.{u})
      (hcovS : RenamingContext.CoversFV Θ S)
      (hcovT : RenamingContext.CoversFV Θ T),
      (∀ v ∉ used₀, Θ v = none) →
      SMT.RenamingContext.RespectsTypeContextOnFV Θ Λ S →
      SMT.RenamingContext.RespectsTypeContextOnFV Θ Λ T →
      (∀ v, Θ v ≠ none → v ∈ Λ) →
      ∀ (F G : ZFSet.{u})
        (hF : F ∈ ⟦BType.set τ⟧ᶻ)
        (hG : G ∈ ⟦BType.set τ⟧ᶻ)
        (denS denT : SMT.Dom.{u}),
        ⟦S.abstract Θ hcovS⟧ˢ = some denS →
        ⟦T.abstract Θ hcovT⟧ˢ = some denT →
        RDomCast (⟨F, BType.set τ, hF⟩ : B.Dom) denS →
        RDomCast (⟨G, BType.set τ, hG⟩ : B.Dom) denT →
        ∃ (Θ' : SMT.RenamingContext.Context.{u})
          (hcovOut : RenamingContext.CoversFV Θ' out)
          (denOut : SMT.Dom.{u}),
          RenamingContext.Extends Θ' Θ ∧
          (∀ v ∉ used₁, Θ' v = none) ∧
          SMT.RenamingContext.RespectsTypeContextOnFV Θ' Γ out ∧
          (∀ v, Θ' v ≠ none → v ∈ Γ) ∧
          SpecBodiesTrue Θ' Γ Dlt ∧
          ⟦out.abstract Θ' hcovOut⟧ˢ = some denOut ∧
          denOut.snd.fst = σout ∧
          RDomCastSupported
            (⟨F ∪ G, BType.set τ, set_union_mem hF hG⟩ : B.Dom)
            denOut) ∧
  CastUnionRepGuardedSemantics.{u}
    τ S T out σS σT σout Λ Dlt

/-- Operational union contract carrying its exact declaration delta. -/
abbrev CastUnionRepScopedSpec.{u} (τ : BType)
    (S T : SMT.Term) (σS σT : SMTType) : Prop :=
  ∀ {Λ : SMT.TypeContext} {n : ℕ} {used : List SMT.𝒱}
    {decl : SMT.Chunk},
    Λ ⊢ˢ S : σS →
    Λ ⊢ˢ T : σT →
    (∀ v ∈ SMT.bv S, v ∈ used) →
    (∀ v ∈ SMT.bv T, v ∈ used) →
    ⦃fun ⟨E, Λ'⟩ =>
      ⌜Λ' = Λ ∧ E.freshvarsc = n ∧
        Λ.keys ⊆ E.usedVars ∧ E.usedVars = used ∧
        E.declarations = decl⌝⦄
    castUnion ⟨S, σS⟩ ⟨T, σT⟩
    ⦃⇓? ⟨out, σout⟩ ⟨E', Γ'⟩ =>
      ⌜used ⊆ E'.usedVars ∧
        Λ ⊆ Γ' ∧
        Γ'.keys ⊆ E'.usedVars ∧
        Nonempty (σout ~> (BType.set τ).toSMTType) ∧
        Γ' ⊢ˢ out : σout ∧
        (∀ v ∈ used, v ∉ Λ → v ∉ Γ') ∧
        ∃ Dlt : SMT.Chunk,
          E'.declarations = decl ++ Dlt ∧
          ContextGeneratedByDeclarations Λ Γ' Dlt ∧
          DeclarationContextTrace Λ Dlt Γ' ∧
          (∀ v ∈ declVars Dlt, v ∉ used) ∧
          (∀ v ∈ SMT.fv S, v ∈ SMT.fv out ∨
            ∃ b ∈ specBodies Dlt, v ∈ SMT.fv b) ∧
          (∀ v ∈ SMT.fv T, v ∈ SMT.fv out ∨
            ∃ b ∈ specBodies Dlt, v ∈ SMT.fv b) ∧
          (SMT.fv out ⊆ (SMT.fv S ∪ SMT.fv T) ∪ declVars Dlt) ∧
          (∀ b ∈ specBodies Dlt,
            SMT.fv b ⊆ (SMT.fv S ∪ SMT.fv T) ∪ declVars Dlt) ∧
          CastUnionRepSemantics.{u} τ S T out σS σT σout
            Λ Γ' used E'.usedVars Dlt ∧
          (∀ b ∈ specBodies Dlt, Γ' ⊢ˢ b : SMTType.bool) ∧
          ScopedGeneratedTyping Λ Dlt out σout⌝⦄

namespace EncodeTermRepresentedScopedUnion

theorem direct_shape_decls
    (S T : SMT.Term) (ρ : SMTType)
    {Λ : SMT.TypeContext} {n : ℕ} {used : List SMT.𝒱}
    {decl : SMT.Chunk}
    (typS : Λ ⊢ˢ S : SMTType.fun ρ SMTType.bool)
    (typT : Λ ⊢ˢ T : SMTType.fun ρ SMTType.bool) :
    ⦃fun ⟨E, Λ'⟩ =>
      ⌜Λ' = Λ ∧ E.freshvarsc = n ∧
        Λ.keys ⊆ E.usedVars ∧ E.usedVars = used ∧
        E.declarations = decl⌝⦄
    castUnion ⟨S, SMTType.fun ρ SMTType.bool⟩
      ⟨T, SMTType.fun ρ SMTType.bool⟩
    ⦃⇓? ⟨out, σout⟩ ⟨E', Γ'⟩ =>
      ⌜∃ z : SMT.𝒱,
        out = SMT.Term.lambda [z] [ρ]
          (.or (.app S (.var z)) (.app T (.var z))) ∧
        σout = SMTType.fun ρ SMTType.bool ∧
        Γ' = Λ ∧ E'.declarations = decl ∧
        z ∉ SMT.fv S ∧ z ∉ SMT.fv T⌝⦄ := by
  have hcast :
      castUnion ⟨S, SMTType.fun ρ SMTType.bool⟩
          ⟨T, SMTType.fun ρ SMTType.bool⟩ = do
        let z ← SMT.freshVar ρ "union!"
        SMT.eraseFromContext z
        return (SMT.Term.lambda [z] [ρ]
          (.or (.app S (.var z)) (.app T (.var z))),
          SMTType.fun ρ SMTType.bool) := by
    unfold castUnion
    simp
  rw [hcast]
  mstart
  mintro pre ∀St₀
  mpure pre
  obtain ⟨rfl, rfl, St₀_keys, rfl, rfl⟩ := pre
  mspec (Std.Do.Triple.and _
    (SMT.freshVar_spec (Γ := St₀.types) (τ := ρ)
      (n := St₀.env.freshvarsc) (used := St₀.env.usedVars))
    (SMT.freshVar_decls (τ := ρ)
      (decl := St₀.env.declarations)))
  next z =>
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨⟨St₁_types_eq, z_fresh, _St₁_fvc,
      _St₁_used, _z_not_used⟩, St₁_decl⟩ := pre
    mspec (Std.Do.Triple.and _
      (SMT.eraseFromContext_spec (v := z) (Γ := St₁.types)
        (n := St₁.env.freshvarsc) (used := St₁.env.usedVars))
      (SMT.eraseFromContext_decls (v := z)
        (decl := St₁.env.declarations)))
    mrename_i pre
    mintro ∀StE
    mpure pre
    obtain ⟨⟨StE_types_eq, _StE_fvc, _StE_used⟩, StE_decl⟩ := pre
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨z, rfl, trivial, ?_, ?_, ?_, ?_⟩
    · rw [StE_types_eq, St₁_types_eq]
      apply AList.ext
      show List.kerase z (AList.insert z ρ St₀.types).entries =
        St₀.types.entries
      rw [AList.entries_insert_of_notMem z_fresh]
      exact List.kerase_cons_eq rfl
    · rw [StE_decl, St₁_decl]
    · exact funNotMemFvOfNotMemContext typS z_fresh
    · exact funNotMemFvOfNotMemContext typT z_fresh

/-- The direct pointwise union lambda is sound under every valuation of its
free operands. -/
theorem direct_guarded.{u}
    {τ : BType} {ρ : SMTType} (hρ : BType.SupportedSMT τ ρ)
    {S T : SMT.Term} {z : SMT.𝒱}
    {Θ : SMT.RenamingContext.Context.{u}}
    (hcovS : RenamingContext.CoversFV Θ S)
    (hcovT : RenamingContext.CoversFV Θ T)
    {F G : ZFSet.{u}}
    {hF : F ∈ ⟦BType.set τ⟧ᶻ}
    {hG : G ∈ ⟦BType.set τ⟧ᶻ}
    {denS denT : SMT.Dom.{u}}
    (hdenS : ⟦S.abstract Θ hcovS⟧ˢ = some denS)
    (hdenT : ⟦T.abstract Θ hcovT⟧ˢ = some denT)
    (hdenS_type : denS.snd.fst = SMTType.fun ρ SMTType.bool)
    (hdenT_type : denT.snd.fst = SMTType.fun ρ SMTType.bool)
    (F_rel : RDomCastSupported
      (⟨F, BType.set τ, hF⟩ : B.Dom) denS)
    (G_rel : RDomCastSupported
      (⟨G, BType.set τ, hG⟩ : B.Dom) denT)
    (z_not_fv_S : z ∉ SMT.fv S)
    (z_not_fv_T : z ∉ SMT.fv T)
    (hcovOut : RenamingContext.CoversFV Θ
      (SMT.Term.lambda [z] [ρ]
        (.or (.app S (.var z)) (.app T (.var z)))))
    (denOut : SMT.Dom.{u})
    (hdenOut :
      ⟦(SMT.Term.lambda [z] [ρ]
        (.or (.app S (.var z)) (.app T (.var z)))).abstract
          Θ hcovOut⟧ˢ = some denOut) :
    RDomCastSupported
      (⟨F ∪ G, BType.set τ, set_union_mem hF hG⟩ : B.Dom)
      denOut := by
  obtain ⟨denU, hdenU, denU_type, _hretU, hpointU⟩ :=
    castUnion_denotation_direct hcovS hcovT hdenS hdenT
      hdenS_type hdenT_type z_not_fv_S z_not_fv_T hcovOut
  have den_eq : denOut = denU := by
    rw [hdenU] at hdenOut
    exact Option.some.inj hdenOut.symm
  subst denU
  rcases denS with ⟨Fenc, σS, hFenc⟩
  rcases denT with ⟨Genc, σT, hGenc⟩
  rcases denOut with ⟨U, σU, hU⟩
  dsimp at hdenS_type hdenT_type denU_type
  subst σS σT σU
  exact represented_setPred_union_of_pointwise hρ hF hG
    hFenc hGenc hU F_rel G_rel hpointU

set_option maxHeartbeats 2500000 in
theorem direct_scoped_contract.{u}
    (τ : BType) (ρ : SMTType) (hρ : BType.SupportedSMT τ ρ)
    (S T : SMT.Term) :
    CastUnionRepScopedSpec.{u} τ S T
      (SMTType.fun ρ SMTType.bool)
      (SMTType.fun ρ SMTType.bool) := by
  unfold CastUnionRepScopedSpec
  intro Λ n used decl typS typT bvS_used bvT_used
  mstart
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_keys, rfl, rfl⟩ := pre
  mspec (Std.Do.Triple.and _
    (castUnion_direct_rep_contract τ ρ hρ S T
      typS typT bvS_used bvT_used)
    (direct_shape_decls S T ρ typS typT
      (n := St.env.freshvarsc) (used := St.env.usedVars)
      (decl := St.env.declarations)))
  rename_i out
  obtain ⟨out, σout⟩ := out
  mrename_i post
  mintro ∀St'
  mpure post
  obtain ⟨op_post, shape⟩ := post
  obtain ⟨used_sub, types_sub, keys_sub, path, typ_out,
    preserves, semantic⟩ := op_post
  obtain ⟨z, out_eq, σout_eq, types_eq, decl_eq,
    z_not_fv_S, z_not_fv_T⟩ := shape
  mpure_intro
  dsimp at out_eq σout_eq path typ_out semantic ⊢
  subst out
  subst σout
  rw [types_eq] at types_sub keys_sub typ_out preserves semantic ⊢
  refine ⟨used_sub, types_sub, keys_sub, path, typ_out, preserves,
    [], ?_, ContextGeneratedByDeclarations.refl _,
    DeclarationContextTrace.nil _, (by simp [declVars]), ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · simpa using decl_eq
  · intro v hv
    refine Or.inl ?_
    simp only [SMT.fv, List.removeAll, List.mem_filter,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    refine ⟨Or.inl (Or.inl hv), ?_⟩
    have hv_ne : v ≠ z := by
      intro hvz
      subst v
      exact z_not_fv_S hv
    simp [hv_ne]
  · intro v hv
    refine Or.inl ?_
    simp only [SMT.fv, List.removeAll, List.mem_filter,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    refine ⟨Or.inr (Or.inl hv), ?_⟩
    have hv_ne : v ≠ z := by
      intro hvz
      subst v
      exact z_not_fv_T hv
    simp [hv_ne]
  · intro v hv
    simp only [SMT.fv, List.removeAll, List.mem_filter,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
    obtain ⟨hv_body, hv_ne_z⟩ := hv
    simp only [List.elem_eq_contains, List.contains_eq_mem,
      List.mem_cons, List.not_mem_nil, or_false, Bool.not_eq_true',
      decide_eq_false_iff_not] at hv_ne_z
    rcases hv_body with ((hvS | rfl) | (hvT | rfl))
    · rw [List.mem_union_iff]
      exact Or.inl (List.mem_union_iff.mpr (.inl hvS))
    · exact absurd rfl hv_ne_z
    · rw [List.mem_union_iff]
      exact Or.inl (List.mem_union_iff.mpr (.inr hvT))
    · exact absurd rfl hv_ne_z
  · simp [specBodies]
  · constructor
    · intro Θ hcovS hcovT Θ_none respectsS respectsT
        Θ_dom F G hF hG denS denT hdenS hdenT F_rel G_rel
      obtain ⟨Θ', hcovOut, denOut, Θ'_ext, Θ'_none,
          respectsOut, Θ'_dom, hdenOut, hdenOut_type, result_rel⟩ :=
        semantic Θ hcovS hcovT Θ_none respectsS respectsT
          Θ_dom F G hF hG denS denT hdenS hdenT F_rel G_rel
      exact ⟨Θ', hcovOut, denOut, Θ'_ext, Θ'_none,
        respectsOut, Θ'_dom, (by simp [SpecBodiesTrue, specBodies]),
        hdenOut, hdenOut_type, result_rel⟩
    · intro Γsup Γscope Θ hcovS hcovT respectsS respectsT
        F G hF hG denS denT hdenS hdenT hdenS_type hdenT_type
        F_rel G_rel hcovOut denOut _respectsOut _specsTrue
        hdenOut _hdenOut_type
      exact direct_guarded hρ hcovS hcovT hdenS hdenT
        hdenS_type hdenT_type F_rel G_rel z_not_fv_S z_not_fv_T
        hcovOut denOut hdenOut
  · simp [specBodies]
  · constructor
    · intro Γsup Γscope result_bv_fresh
      exact SMT.Typing.weakening Γscope.base typ_out result_bv_fresh
    · simp [ScopedSpecsTyping, specBodies]

set_option maxHeartbeats 3500000 in
/-- A helper specification that is true under the ambient valuation forces
the helper to denote the cast of the source set.  The final pointwise union
lambda is therefore sound for every satisfying helper assignment, not only
for the witness selected while running the encoder. -/
theorem helper_guarded.{u}
    {τ : BType} {ρ σS : SMTType}
    (hρ : BType.SupportedSMT τ ρ)
    {S T spec : SMT.Term} {helper z : SMT.𝒱}
    {Λ Γsup : SMT.TypeContext}
    (scope : ScopedContextExtends Λ
      (helperSpecChunk helper (SMTType.fun ρ SMTType.bool) spec) Γsup)
    (c : σS ~> SMTType.fun ρ SMTType.bool)
    (exactness :
      ∀ (Θ : SMT.RenamingContext.Context.{u})
        (hS : RenamingContext.CoversFV Θ S)
        (_respects : SMT.RenamingContext.RespectsTypeContextOnFV Θ Λ S)
        (pf : ∀ (x_ : SMT.𝒱) (X_ : SMT.Dom),
          ∀ v ∈ SMT.fv (SMT.Term.var x_),
            (Function.update Θ x_ (some X_) v).isSome = true),
      ∀ (denS : SMT.Dom), ⟦S.abstract Θ hS⟧ˢ = some denS →
        ∃ (Φ H : SMT.Dom)
          (_ : ⟦(SMT.Term.var helper).abstract
            (Function.update Θ helper (some H)) (pf helper H)⟧ˢ = some H)
          (hφ : RenamingContext.CoversFV
            (Function.update Θ helper (some H)) spec)
          (_ : ⟦spec.abstract (Function.update Θ helper (some H))
            hφ⟧ˢ = some Φ),
          H.snd.fst = SMTType.fun ρ SMTType.bool ∧
          Φ.snd.fst = SMTType.bool ∧
          (Φ.fst = zftrue ∧
            denS.fst.pair H.fst ∈ (castZF_of_path c).1) ∧
          (∀ (Y : SMT.Dom)
            (_ : Y.snd.fst = SMTType.fun ρ SMTType.bool)
            (hφY : RenamingContext.CoversFV
              (Function.update Θ helper (some Y)) spec),
            (⟦spec.abstract (Function.update Θ helper (some Y))
              hφY⟧ˢ).isSome = true ∧
            ∀ {ΦY : SMT.Dom},
              ⟦spec.abstract (Function.update Θ helper (some Y))
                hφY⟧ˢ = some ΦY →
              ΦY.fst = zftrue →
              denS.fst.pair Y.fst ∈ (castZF_of_path c).1))
    {Θ : SMT.RenamingContext.Context.{u}}
    (hcovS : RenamingContext.CoversFV Θ S)
    (hcovT : RenamingContext.CoversFV Θ T)
    (respectsS : SMT.RenamingContext.RespectsTypeContextOnFV Θ Γsup S)
    (_respectsT : SMT.RenamingContext.RespectsTypeContextOnFV Θ Γsup T)
    {F G : ZFSet.{u}}
    {hF : F ∈ ⟦BType.set τ⟧ᶻ}
    {hG : G ∈ ⟦BType.set τ⟧ᶻ}
    {denS denT : SMT.Dom.{u}}
    (hdenS : ⟦S.abstract Θ hcovS⟧ˢ = some denS)
    (hdenT : ⟦T.abstract Θ hcovT⟧ˢ = some denT)
    (hdenS_type : denS.snd.fst = σS)
    (hdenT_type : denT.snd.fst = SMTType.fun ρ SMTType.bool)
    (F_rel : RDomCastSupported
      (⟨F, BType.set τ, hF⟩ : B.Dom) denS)
    (G_rel : RDomCastSupported
      (⟨G, BType.set τ, hG⟩ : B.Dom) denT)
    (z_not_fv_helper : z ∉ SMT.fv (SMT.Term.var helper))
    (z_not_fv_T : z ∉ SMT.fv T)
    (hcovOut : RenamingContext.CoversFV Θ
      (SMT.Term.lambda [z] [ρ]
        (.or (.app (.var helper) (.var z)) (.app T (.var z)))))
    (denOut : SMT.Dom.{u})
    (respectsOut : SMT.RenamingContext.RespectsTypeContextOnFV Θ Γsup
      (SMT.Term.lambda [z] [ρ]
        (.or (.app (.var helper) (.var z)) (.app T (.var z)))))
    (specsTrue : SpecBodiesTrue Θ Γsup
      (helperSpecChunk helper (SMTType.fun ρ SMTType.bool) spec))
    (hdenOut :
      ⟦(SMT.Term.lambda [z] [ρ]
        (.or (.app (.var helper) (.var z)) (.app T (.var z)))).abstract
          Θ hcovOut⟧ˢ = some denOut) :
    RDomCastSupported
      (⟨F ∪ G, BType.set τ, set_union_mem hF hG⟩ : B.Dom)
      denOut := by
  have respectsS_base :
      SMT.RenamingContext.RespectsTypeContextOnFV Θ Λ S :=
    fun _ _ hv hlookup =>
      respectsS hv (AList.lookup_of_subset scope.base hlookup)
  let pf : ∀ (x_ : SMT.𝒱) (H : SMT.Dom),
      ∀ v ∈ SMT.fv (SMT.Term.var x_),
        (Function.update Θ x_ (some H) v).isSome = true := by
    intro x_ H v hv
    simp only [SMT.fv, List.mem_singleton] at hv
    subst v
    simp
  obtain ⟨_ΦW, _HW, _hdenVarW, _hcovSpecW, _hdenSpecW,
      _HWty, _ΦWty, _castW, guard⟩ :=
    exactness Θ hcovS respectsS_base pf denS hdenS
  have hz_ne_helper : z ≠ helper := by
    intro h
    subst z
    exact z_not_fv_helper (by simp [SMT.fv])
  have helperFV : helper ∈ SMT.fv
      (SMT.Term.lambda [z] [ρ]
        (.or (.app (.var helper) (.var z)) (.app T (.var z)))) := by
    simp only [SMT.fv, List.removeAll, List.mem_filter,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    refine ⟨Or.inl (Or.inl (by simp)), ?_⟩
    simp [Ne.symm hz_ne_helper]
  have helperSome : (Θ helper).isSome = true := hcovOut helper helperFV
  obtain ⟨helperVal, hhelperVal⟩ := Option.isSome_iff_exists.mp helperSome
  have helperTy : helperVal.snd.fst =
      SMTType.fun ρ SMTType.bool := by
    have helperLookup : Γsup.lookup helper =
        some (SMTType.fun ρ SMTType.bool) :=
      scope.lookup_of_declared (by simp [declEntries_helperSpecChunk])
    obtain ⟨d, hd, hdty⟩ := respectsOut helperFV helperLookup
    rw [hhelperVal] at hd
    injection hd with hdeq
    subst d
    exact hdty
  have updateEq : Function.update Θ helper (some helperVal) = Θ := by
    rw [← hhelperVal]
    exact Function.update_eq_self helper Θ
  have specTrue := specsTrue spec (by
    simp [specBodies_helperSpecChunk])
  obtain ⟨hcovSpec, denSpec, _respectsSpec, hdenSpec,
      _hdenSpecTy, hdenSpecTrue⟩ := specTrue
  have hcovSpecUpdate : RenamingContext.CoversFV
      (Function.update Θ helper (some helperVal)) spec := by
    rw [updateEq]
    exact hcovSpec
  obtain ⟨_specSome, guardTrue⟩ :=
    guard helperVal helperTy hcovSpecUpdate
  have hdenSpecUpdate :
      ⟦spec.abstract (Function.update Θ helper (some helperVal))
        hcovSpecUpdate⟧ˢ = some denSpec := by
    simpa only [updateEq, proof_irrel_heq] using hdenSpec
  have castPair := guardTrue hdenSpecUpdate hdenSpecTrue
  have hcovHelper : RenamingContext.CoversFV Θ (.var helper) := by
    intro v hv
    simp only [SMT.fv, List.mem_singleton] at hv
    subst v
    exact helperSome
  have hdenHelper :
      ⟦(SMT.Term.var helper).abstract Θ hcovHelper⟧ˢ =
        some helperVal := by
    rw [SMT.Term.abstract]
    simp only [SMT.denote]
    congr 1
    exact Option.get_of_eq_some _ hhelperVal
  rcases denS with ⟨Fenc, σS0, hFenc⟩
  dsimp at hdenS_type
  subst σS0
  rcases helperVal with ⟨Fhelper, σhelper, hFhelper⟩
  dsimp at helperTy
  subst σhelper
  have F_helper_supported : RDomCastSupported
      (⟨F, BType.set τ, hF⟩ : B.Dom)
      (⟨Fhelper, SMTType.fun ρ SMTType.bool, hFhelper⟩ : SMT.Dom) :=
    RDomCastSupported.of_cast_to_supported F_rel (.setPred hρ) c castPair
  exact direct_guarded hρ hcovHelper hcovT hdenHelper hdenT
    rfl hdenT_type F_helper_supported G_rel z_not_fv_helper z_not_fv_T
    hcovOut denOut hdenOut

set_option maxHeartbeats 7000000 in
/-- Generic left-loosening branch used by both characteristic-predicate and
option-function/graph representations of sets. -/
theorem left_helper_scoped_contract.{u}
    (τ : BType) (ρ σS : SMTType)
    (hρ : BType.SupportedSMT τ ρ)
    (hSrep : BType.SupportedSMT (BType.set τ) σS)
    (S T : SMT.Term) (c : σS ~> SMTType.fun ρ SMTType.bool)
    (hfaith : castPath.FVFaithful c)
    (hbranch :
      castUnion (S, σS) (T, SMTType.fun ρ SMTType.bool) = do
        let ⟨helper, spec⟩ ← loosenAux_prf "union!" c S
        declareConstWithSpec helper (SMTType.fun ρ SMTType.bool) spec
        castUnion
          (SMT.Term.var helper, SMTType.fun ρ SMTType.bool)
          (T, SMTType.fun ρ SMTType.bool)) :
    CastUnionRepScopedSpec.{u} τ S T σS
      (SMTType.fun ρ SMTType.bool) := by
  unfold CastUnionRepScopedSpec
  intro Λ n used decl typS typT bvS_used bvT_used
  rw [hbranch]
  mstart
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_keys, rfl, rfl⟩ := pre
  mspec (Std.Do.Triple.and _
    (Std.Do.Triple.and _
      (Std.Do.Triple.and _
        (loosenAux_prf_exact_univ
          (Λ := St.types) (n := St.env.freshvarsc)
          (used := St.env.usedVars) typS bvS_used c)
        (loosenAux_prf_fv_of_faithful hfaith
          (used := St.env.usedVars) (n := St.env.freshvarsc)
          (x := S) (by
            intro v hv
            exact St_keys (SMT.Typing.mem_context_of_mem_fv typS hv))))
      (loosenAux_prf_decls c (decl := St.env.declarations)))
    (loosenAux_prf_types_eq c))
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
    (x!_spec := spec) (τ := SMTType.fun ρ SMTType.bool)
    (decl := St1.env.declarations) (as := St1.env.asserts)
    (n := St1.env.freshvarsc) (Γ := St1.types)
    (used := St1.env.usedVars)
  mrename_i pre
  mintro ∀St2
  mpure pre
  obtain ⟨St2_decl_eq, St2_asserts, _St2_fvc, St2_used, St2_types⟩ := pre
  clear St2_asserts
  have Λ_sub1 : St.types ⊆ St1.types := fun v hv =>
    St1_types_sub
      (SMT.TypeContext.entries_subset_insert_of_notMem helper_fresh hv)
  have typT1 : St1.types ⊢ˢ T : SMTType.fun ρ SMTType.bool :=
    SMT.Typing.weakening Λ_sub1 typT
      (fun v hv => preserves1 v (bvT_used v hv)
        (SMT.Typing.bv_notMem_context typT v hv))
  have bvT2 : ∀ v ∈ SMT.bv T, v ∈ St2.env.usedVars := by
    intro v hv
    rw [St2_used]
    exact used_sub1 (bvT_used v hv)
  have typHelper2 : St2.types ⊢ˢ SMT.Term.var helper :
      SMTType.fun ρ SMTType.bool := by
    rw [St2_types]
    exact typ_helper
  have typT2 : St2.types ⊢ˢ T : SMTType.fun ρ SMTType.bool := by
    rw [St2_types]
    exact typT1
  have keys2 : St2.types.keys ⊆ St2.env.usedVars := by
    rw [St2_types, St2_used]
    exact keys_sub1
  mspec (Std.Do.Triple.and _
    (castUnion_direct_rep_contract τ ρ hρ (.var helper) T
      typHelper2 typT2 (by simp [SMT.bv]) bvT2)
    (direct_shape_decls (.var helper) T ρ typHelper2 typT2
      (n := St2.env.freshvarsc) (used := St2.env.usedVars)
      (decl := St2.env.declarations)))
  mvcgen
  rename_i _helper_fresh_again _unit outPair St3
  let out := outPair.1
  let σout := outPair.2
  intro used_sub3 types_sub3 keys_sub3 path typOut preserves3 directSem
    shape
  obtain ⟨z, out_eq, σout_eq, types_eq, direct_decl_eq,
      z_not_fv_helper, z_not_fv_T⟩ := shape
  dsimp at out_eq σout_eq path typOut directSem
  rw [σout_eq] at path
  rw [out_eq, σout_eq] at typOut directSem ⊢
  rw [St2_types, St2_used] at directSem
  have helper_ctx_gen : ContextGeneratedByDeclarations St.types St1.types
      (helperSpecChunk helper (SMTType.fun ρ SMTType.bool) spec) := by
    rw [St1_types_exact]
    exact ContextGeneratedByDeclarations.insert_helper
      St.types helper (SMTType.fun ρ SMTType.bool) spec helper_fresh
  have helper_ctx_trace : DeclarationContextTrace St.types
      (helperSpecChunk helper (SMTType.fun ρ SMTType.bool) spec)
      St1.types := by
    rw [St1_types_exact]
    exact DeclarationContextTrace.helperSpecChunk
      St.types helper (SMTType.fun ρ SMTType.bool) spec helper_fresh
  have helper_lookup : St1.types.lookup helper =
      some (SMTType.fun ρ SMTType.bool) := SMT.Typing.varE typ_helper
  have helper_used1 : helper ∈ St1.env.usedVars :=
    keys_sub1 (AList.lookup_isSome.mp
      (Option.isSome_of_eq_some helper_lookup))
  have helper_not_used0 : helper ∉ St.env.usedVars := helper_not_used
  have initial_sub3 : St.types ⊆ St3.types := by
    intro e he
    apply types_sub3
    rw [St2_types]
    exact Λ_sub1 he
  have used_sub_out : St.env.usedVars ⊆ St3.env.usedVars := by
    intro v hv
    apply used_sub3
    rw [St2_used]
    exact used_sub1 hv
  have preserves_out : ∀ v ∈ St.env.usedVars,
      v ∉ St.types → v ∉ St3.types := by
    intro v hv hnot
    rw [types_eq, St2_types]
    apply preserves1 v hv hnot
  have typ_spec3 : St3.types ⊢ˢ spec : SMTType.bool := by
    rw [types_eq, St2_types]
    exact typ_spec
  have helper_ctx_gen3 : ContextGeneratedByDeclarations St.types St3.types
      (helperSpecChunk helper (SMTType.fun ρ SMTType.bool) spec) := by
    rw [types_eq, St2_types]
    exact helper_ctx_gen
  have helper_ctx_trace3 : DeclarationContextTrace St.types
      (helperSpecChunk helper (SMTType.fun ρ SMTType.bool) spec)
      St3.types := by
    rw [types_eq, St2_types]
    exact helper_ctx_trace
  refine ⟨used_sub_out, initial_sub3, keys_sub3, path, typOut,
    preserves_out,
    helperSpecChunk helper (SMTType.fun ρ SMTType.bool) spec,
    ?_, helper_ctx_gen3, helper_ctx_trace3, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · rw [direct_decl_eq, St2_decl_eq, St1_decl_eq]
    simp [helperSpecChunk, List.concat_eq_append, List.append_assoc]
  · intro v hv
    simp only [declVars_helperSpecChunk, List.mem_singleton] at hv
    subst v
    exact helper_not_used0
  · intro v hv
    exact Or.inr ⟨spec, by simp [specBodies_helperSpecChunk],
      source_fv_spec hv⟩
  · intro v hv
    refine Or.inl ?_
    simp only [SMT.fv, List.removeAll, List.mem_filter,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    refine ⟨Or.inr (Or.inl hv), ?_⟩
    have hv_ne : v ≠ z := by
      intro hvz
      subst v
      exact z_not_fv_T hv
    simp [hv_ne]
  · intro v hv
    simp only [SMT.fv, List.removeAll, List.mem_filter,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
    obtain ⟨hv_body, hv_ne_z⟩ := hv
    simp only [List.elem_eq_contains, List.contains_eq_mem,
      List.mem_cons, List.not_mem_nil, or_false, Bool.not_eq_true',
      decide_eq_false_iff_not] at hv_ne_z
    simp only [List.mem_union_iff, declVars_helperSpecChunk,
      List.mem_singleton]
    rcases hv_body with ((rfl | rfl) | (hvT | rfl))
    · exact Or.inr rfl
    · exact absurd rfl hv_ne_z
    · exact Or.inl (Or.inr hvT)
    · exact absurd rfl hv_ne_z
  · intro body hbody v hv
    simp only [specBodies_helperSpecChunk, List.mem_singleton] at hbody
    subst body
    simp only [List.mem_union_iff, declVars_helperSpecChunk,
      List.mem_singleton]
    rcases List.mem_union_iff.mp (spec_fv hv) with hS | hhelper
    · exact Or.inl (Or.inl hS)
    · exact Or.inr (List.mem_singleton.mp hhelper)
  · constructor
    · intro Θ hcovS hcovT Θ_none respectsS respectsT Θ_dom
        F G hF hG denS denT hdenS hdenT F_rel G_rel
      let pf : ∀ (x_ : SMT.𝒱) (H : SMT.Dom),
          ∀ v ∈ SMT.fv (SMT.Term.var x_),
            (Function.update Θ x_ (some H) v).isSome = true := by
        intro x_ H v hv
        simp only [SMT.fv, List.mem_singleton] at hv
        subst v
        simp
      obtain ⟨Φ, denHelper, hdenVar, hcovSpec, hdenSpec,
          denHelper_type, Φ_type, ⟨Φ_true, castPair⟩, _guard⟩ :=
        exactness Θ hcovS respectsS pf denS hdenS
      let Δhelper := Function.update Θ helper (some denHelper)
      have helper_none : Θ helper = none :=
        Θ_none helper helper_not_used0
      have Δhelper_ext : RenamingContext.Extends Δhelper Θ :=
        RenamingContext.extends_update_of_none helper_none
      have hhelper : RenamingContext.CoversFV Δhelper (.var helper) := by
        intro v hv
        simp only [SMT.fv, List.mem_singleton] at hv
        subst v
        simp [Δhelper]
      have hdenHelper :
          ⟦(SMT.Term.var helper).abstract Δhelper hhelper⟧ˢ =
            some denHelper := by
        simpa only [Δhelper] using hdenVar
      have helper_not_fv_T : helper ∉ SMT.fv T :=
        funNotMemFvOfNotMemContext typT helper_fresh
      have hcovT_helper : RenamingContext.CoversFV Δhelper T :=
        SMT.RenamingContext.coversFV_update_of_notMem helper_not_fv_T hcovT
      have hdenT_helper :
          ⟦T.abstract Δhelper hcovT_helper⟧ˢ = some denT := by
        have heq : ⟦T.abstract Θ hcovT⟧ˢ =
            ⟦T.abstract Δhelper hcovT_helper⟧ˢ := by
          rw [← SMT.RenamingContext.denote,
            ← SMT.RenamingContext.denote]
          exact SMT.RenamingContext.denote_update_of_notMem helper_not_fv_T
        exact heq.symm.trans hdenT
      have respectsS1 :
          SMT.RenamingContext.RespectsTypeContextOnFV Θ St1.types S :=
        respectsS.of_extends (RenamingContext.extends_refl Θ)
          Λ_sub1 typS
      have respectsHelper :
          SMT.RenamingContext.RespectsTypeContextOnFV
            Δhelper St1.types (.var helper) := by
        intro v τv hv hlookup
        simp only [SMT.fv, List.mem_singleton] at hv
        subst v
        rw [helper_lookup] at hlookup
        injection hlookup with heq
        subst τv
        exact ⟨denHelper, by simp [Δhelper], denHelper_type⟩
      have respectsT_helper :
          SMT.RenamingContext.RespectsTypeContextOnFV
            Δhelper St1.types T :=
        respectsT.of_extends Δhelper_ext Λ_sub1 typT
      have respectsSpec_helper :
          SMT.RenamingContext.RespectsTypeContextOnFV
            Δhelper St1.types spec :=
        SMT.RenamingContext.respects_update_helper spec_fv respectsS1
          helper_lookup denHelper_type
      have Δhelper_none : ∀ v ∉ St1.env.usedVars,
          Δhelper v = none := by
        intro v hv
        by_cases hvh : v = helper
        · subst v
          exact absurd helper_used1 hv
        · simp only [Δhelper, Function.update_of_ne hvh]
          apply Θ_none
          intro hv0
          exact hv (used_sub1 hv0)
      have Δhelper_dom : ∀ v, Δhelper v ≠ none → v ∈ St1.types := by
        intro v hv
        by_cases hvh : v = helper
        · subst v
          exact AList.lookup_isSome.mp
            (Option.isSome_of_eq_some helper_lookup)
        · have hv0 : v ∈ St.types := Θ_dom v (by
            simpa [Δhelper, Function.update_of_ne hvh] using hv)
          exact AList.mem_of_subset Λ_sub1 hv0
      rcases denS with ⟨Fenc, σS0, hFenc⟩
      have denS_type := SMT.RenamingContext.denote_type_of_typing_fv
        typS respectsS hcovS hdenS
      dsimp at denS_type
      subst σS0
      rcases denHelper with ⟨Fhelper, σhelper, hFhelper⟩
      dsimp at denHelper_type
      subst σhelper
      have F_supported : RDomCastSupported
          (⟨F, BType.set τ, hF⟩ : B.Dom)
          (⟨Fenc, σS, hFenc⟩ : SMT.Dom) :=
        ⟨RDomCast.toRDomCastAdmissible_of_supported F_rel hSrep, hSrep⟩
      have F_helper_supported : RDomCastSupported
          (⟨F, BType.set τ, hF⟩ : B.Dom)
          (⟨Fhelper, SMTType.fun ρ SMTType.bool,
            hFhelper⟩ : SMT.Dom) :=
        RDomCastSupported.of_cast_to_supported F_supported
          (.setPred hρ) c castPair
      rcases denT with ⟨Genc, σT0, hGenc⟩
      have denT_type := SMT.RenamingContext.denote_type_of_typing_fv
        typT respectsT hcovT hdenT
      dsimp at denT_type
      subst σT0
      have G_supported : RDomCastSupported
          (⟨G, BType.set τ, hG⟩ : B.Dom)
          (⟨Genc, SMTType.fun ρ SMTType.bool, hGenc⟩ : SMT.Dom) :=
        ⟨RDomCast.toRDomCastAdmissible_of_supported G_rel (.setPred hρ),
          .setPred hρ⟩
      obtain ⟨Θ', hcovOut, denOut, Θ'_ext, Θ'_none,
          respectsOut, Θ'_dom, hdenOut,
          hdenOut_type, result_rel⟩ :=
        directSem Δhelper hhelper hcovT_helper Δhelper_none
          respectsHelper respectsT_helper Δhelper_dom F G hF hG
          (⟨Fhelper, SMTType.fun ρ SMTType.bool, hFhelper⟩ : SMT.Dom)
          (⟨Genc, SMTType.fun ρ SMTType.bool, hGenc⟩ : SMT.Dom)
          hdenHelper hdenT_helper F_helper_supported.toRDomCast
          G_supported.toRDomCast
      have specs_helper : SpecBodiesTrue Δhelper St1.types
          (helperSpecChunk helper (SMTType.fun ρ SMTType.bool) spec) := by
        intro body hbody
        simp only [specBodies_helperSpecChunk, List.mem_singleton] at hbody
        subst body
        exact ⟨hcovSpec, Φ, respectsSpec_helper, hdenSpec,
          Φ_type, Φ_true⟩
      have specs_out : SpecBodiesTrue Θ' St1.types
          (helperSpecChunk helper (SMTType.fun ρ SMTType.bool) spec) :=
        specs_helper.of_extends Θ'_ext (fun _ h => h) Δhelper_dom
      have specs_out3 : SpecBodiesTrue Θ' St3.types
          (helperSpecChunk helper (SMTType.fun ρ SMTType.bool) spec) := by
        simpa [types_eq, St2_types] using specs_out
      exact ⟨Θ', hcovOut, denOut,
        RenamingContext.extends_trans Θ'_ext Δhelper_ext,
        Θ'_none, respectsOut, Θ'_dom, specs_out3,
        hdenOut, hdenOut_type, result_rel⟩
    · intro Γsup scopeG Θ hcovS hcovT respectsS respectsT
        F G hF hG denS denT hdenS hdenT hdenS_type hdenT_type
        F_rel G_rel hcovOut denOut respectsOut specsTrue
        hdenOut _hdenOut_type
      have exactness' :
          ∀ (Θ0 : SMT.RenamingContext.Context.{u})
            (hS0 : RenamingContext.CoversFV Θ0 S)
            (hresp0 : SMT.RenamingContext.RespectsTypeContextOnFV
              Θ0 St.types S)
            (pf0 : ∀ (x_ : SMT.𝒱) (X_ : SMT.Dom),
              ∀ v ∈ SMT.fv (SMT.Term.var x_),
                (Function.update Θ0 x_ (some X_) v).isSome = true),
            ∀ (denS0 : SMT.Dom),
              ⟦S.abstract Θ0 hS0⟧ˢ = some denS0 →
              ∃ (Φ H : SMT.Dom)
                (_ : ⟦(SMT.Term.var helper).abstract
                  (Function.update Θ0 helper (some H))
                    (pf0 helper H)⟧ˢ = some H)
                (hφ : RenamingContext.CoversFV
                  (Function.update Θ0 helper (some H)) spec)
                (_ : ⟦spec.abstract
                  (Function.update Θ0 helper (some H)) hφ⟧ˢ = some Φ),
                H.snd.fst = SMTType.fun ρ SMTType.bool ∧
                Φ.snd.fst = SMTType.bool ∧
                (Φ.fst = zftrue ∧
                  denS0.fst.pair H.fst ∈ (castZF_of_path c).1) ∧
                (∀ (Y : SMT.Dom)
                  (_ : Y.snd.fst = SMTType.fun ρ SMTType.bool)
                  (hφY : RenamingContext.CoversFV
                    (Function.update Θ0 helper (some Y)) spec),
                  (⟦spec.abstract (Function.update Θ0 helper (some Y))
                    hφY⟧ˢ).isSome = true ∧
                  ∀ {ΦY : SMT.Dom},
                    ⟦spec.abstract (Function.update Θ0 helper (some Y))
                      hφY⟧ˢ = some ΦY →
                    ΦY.fst = zftrue →
                    denS0.fst.pair Y.fst ∈ (castZF_of_path c).1) := by
        intro Θ0 hS0 hresp0 pf0 denS0 hdenS0
        obtain ⟨Φ, H, hvar, hφ, hspec, hHty, hΦty, hcast, hguard⟩ :=
          exactness Θ0 hS0 hresp0 pf0 denS0 hdenS0
        exact ⟨Φ, H, hvar, hφ, hspec, hHty, hΦty, hcast, hguard⟩
      exact helper_guarded hρ scopeG c exactness' hcovS hcovT
        respectsS respectsT hdenS hdenT hdenS_type hdenT_type
        F_rel G_rel z_not_fv_helper z_not_fv_T hcovOut denOut
        respectsOut specsTrue hdenOut
  · intro body hbody
    simp only [specBodies_helperSpecChunk, List.mem_singleton] at hbody
    subst body
    exact typ_spec3
  · exact ScopedGeneratedTyping.of_operational helper_ctx_gen3 typOut
      (by
        intro body hbody
        simp only [specBodies_helperSpecChunk, List.mem_singleton] at hbody
        subst body
        exact typ_spec3)

theorem chpred_scoped_contract.{u}
    (τ : BType) (ρ σ : SMTType)
    (hρ : BType.SupportedSMT τ ρ)
    (hσ : BType.SupportedSMT τ σ)
    (hne : ρ ≠ σ) (hcast : ρ ⊑ σ)
    (S T : SMT.Term) :
    CastUnionRepScopedSpec.{u} τ S T
      (SMTType.fun ρ SMTType.bool)
      (SMTType.fun σ SMTType.bool) := by
  have hfun : SMTType.fun ρ SMTType.bool ⊑
      SMTType.fun σ SMTType.bool := castable?.chpred hcast
  have hcastUnion :
      castUnion (S, SMTType.fun ρ SMTType.bool)
          (T, SMTType.fun σ SMTType.bool) =
        castUnion.chpred S T hcast.toCastPath := by
    simp only [castUnion]
    rw [dif_neg (by simpa using hne), dif_pos hfun]
    unfold castUnionAux
    have hpath : hfun.toCastPath =
        castPath.chpred hcast.toCastPath := by
      calc
        hfun.toCastPath = (castable?.chpred hcast).toCastPath :=
          congrArg castable?.toCastPath (Subsingleton.elim _ _)
        _ = castPath.chpred hcast.toCastPath :=
          SMTType.castable?_to_castPath_chpred hcast
    rw [hpath]
  have hvia : castUnion.chpred S T hcast.toCastPath = (do
      let ⟨helper, spec⟩ ← loosenAux_prf "union!"
        (castPath.chpred hcast.toCastPath) S
      declareConstWithSpec helper (SMTType.fun σ SMTType.bool) spec
      castUnion
        (SMT.Term.var helper, SMTType.fun σ SMTType.bool)
        (T, SMTType.fun σ SMTType.bool)) := by
    unfold castUnion.chpred SMT.declareConstWithSpec castUnion
    simp
  unfold CastUnionRepScopedSpec
  intro Λ n used decl typS typT bvS_used bvT_used
  exact left_helper_scoped_contract τ σ
    (SMTType.fun ρ SMTType.bool) hσ (.setPred hρ) S T
    (castPath.chpred hcast.toCastPath)
    (castPath.fvFaithful _) (hcastUnion.trans hvia)
    typS typT bvS_used bvT_used

theorem graph_scoped_contract.{u}
    (α β : BType) (S T : SMT.Term) :
    CastUnionRepScopedSpec.{u} (α ×ᴮ β) S T
      (SMTType.fun α.toSMTType (SMTType.option β.toSMTType))
      (SMTType.fun (SMTType.pair α.toSMTType β.toSMTType)
        SMTType.bool) := by
  let cα : α.toSMTType ~> α.toSMTType :=
    castPath.reflexive α.toSMTType
  let cβ : β.toSMTType ~> β.toSMTType :=
    castPath.reflexive β.toSMTType
  let c : SMTType.fun α.toSMTType (SMTType.option β.toSMTType) ~>
      SMTType.fun (SMTType.pair α.toSMTType β.toSMTType)
        SMTType.bool := castPath.graph cα cβ
  have hcastUnion :
      castUnion
        (S, SMTType.fun α.toSMTType (SMTType.option β.toSMTType))
        (T, SMTType.fun (SMTType.pair α.toSMTType β.toSMTType)
          SMTType.bool) = castUnion.graph S T cα cβ := by
    simp only [castUnion]
    rw [dif_neg (by simp)]
    let hα : α.toSMTType ⊑ α.toSMTType := castable?.reflexive
    let hβ : β.toSMTType ⊑ β.toSMTType := castable?.reflexive
    let hgraph :
        SMTType.fun α.toSMTType (SMTType.option β.toSMTType) ⊑
          SMTType.fun (SMTType.pair α.toSMTType β.toSMTType)
            SMTType.bool := castable?.graph hα hβ
    rw [dif_pos hgraph]
    unfold castUnionAux
    have hpα : hα.toCastPath = cα :=
      SMTType.castable?_to_castPath_reflexive
    have hpβ : hβ.toCastPath = cβ :=
      SMTType.castable?_to_castPath_reflexive
    have hpath : hgraph.toCastPath = c := by
      calc
        hgraph.toCastPath = (castable?.graph hα hβ).toCastPath :=
          congrArg castable?.toCastPath (Subsingleton.elim _ _)
        _ = castPath.graph hα.toCastPath hβ.toCastPath :=
          SMTType.castable?_to_castPath_graph hα hβ
        _ = c := by rw [hpα, hpβ]
    rw [hpath]
  have hvia : castUnion.graph S T cα cβ = (do
      let ⟨helper, spec⟩ ← loosenAux_prf "union!" c S
      declareConstWithSpec helper
        (SMTType.fun (SMTType.pair α.toSMTType β.toSMTType)
          SMTType.bool) spec
      castUnion
        (SMT.Term.var helper,
          SMTType.fun (SMTType.pair α.toSMTType β.toSMTType)
            SMTType.bool)
        (T, SMTType.fun (SMTType.pair α.toSMTType β.toSMTType)
          SMTType.bool)) := by
    unfold castUnion.graph SMT.declareConstWithSpec castUnion c cα cβ
    simp
  unfold CastUnionRepScopedSpec
  intro Λ n used decl typS typT bvS_used bvT_used
  exact left_helper_scoped_contract (α ×ᴮ β)
    (SMTType.pair α.toSMTType β.toSMTType)
    (SMTType.fun α.toSMTType (SMTType.option β.toSMTType))
    (BType.SupportedSMT.canonical (α ×ᴮ β)) (.optionFun α β)
    S T c (castPath.fvFaithful c) (hcastUnion.trans hvia)
    typS typT bvS_used bvT_used

theorem result_comm.{u}
    {τ : BType} {F G : ZFSet.{u}}
    {hF : F ∈ ⟦BType.set τ⟧ᶻ}
    {hG : G ∈ ⟦BType.set τ⟧ᶻ}
    {den : SMT.Dom.{u}}
    (rel : RDomCastSupported
      (⟨G ∪ F, BType.set τ, set_union_mem hG hF⟩ : B.Dom) den) :
    RDomCastSupported
      (⟨F ∪ G, BType.set τ, set_union_mem hF hG⟩ : B.Dom) den := by
  rcases den with ⟨Uval, σU, hUval⟩
  obtain ⟨⟨⟨c, hret⟩, hadmissible⟩, hsupported⟩ := rel
  refine ⟨⟨⟨c, ?_⟩, ?_⟩, hsupported⟩
  · calc
      retract (BType.set τ) (castZF_apply c Uval) = G ∪ F := hret
      _ = F ∪ G := ZFSet.union_comm
  · have hunion : G ∪ F = F ∪ G := ZFSet.union_comm
    simpa only [hunion, proof_irrel_heq] using hadmissible

theorem of_swap.{u}
    (τ : BType) (S T : SMT.Term) (σS σT : SMTType)
    (hswap : castUnion (S, σS) (T, σT) =
      castUnion (T, σT) (S, σS))
    (swapped : CastUnionRepScopedSpec.{u} τ T S σT σS) :
    CastUnionRepScopedSpec.{u} τ S T σS σT := by
  unfold CastUnionRepScopedSpec
  intro Λ n used decl typS typT bvS_used bvT_used
  rw [hswap]
  mstart
  mintro pre ∀St
  mpure pre
  mspec swapped typT typS bvT_used bvS_used
  rename_i out
  obtain ⟨out, σout⟩ := out
  mrename_i post
  mintro ∀St'
  mpure post
  obtain ⟨used_sub, types_sub, keys_sub, path, typOut, preserves,
      Dlt, decl_eq, ctx_gen, ctx_trace, decl_fresh,
      obsT, obsS, out_dep_swap, specs_dep_swap, semSwap,
      specs_typ, scoped_typ⟩ := post
  mpure_intro
  refine ⟨used_sub, types_sub, keys_sub, path, typOut, preserves,
    Dlt, decl_eq, ctx_gen, ctx_trace, decl_fresh,
    obsS, obsT, ?_, ?_, ?_, specs_typ, scoped_typ⟩
  · intro v hv
    have h := out_dep_swap hv
    simp only [List.mem_union_iff] at h ⊢
    rcases h with (hT | hS) | hdecl
    · exact Or.inl (Or.inr hT)
    · exact Or.inl (Or.inl hS)
    · exact Or.inr hdecl
  · intro body hbody v hv
    have h := specs_dep_swap body hbody hv
    simp only [List.mem_union_iff] at h ⊢
    rcases h with (hT | hS) | hdecl
    · exact Or.inl (Or.inr hT)
    · exact Or.inl (Or.inl hS)
    · exact Or.inr hdecl
  constructor
  · intro Θ hcovS hcovT Θ_none respectsS respectsT Θ_dom
      F G hF hG denS denT hdenS hdenT F_rel G_rel
    obtain ⟨goodSemSwap, _guardSwap⟩ := semSwap
    obtain ⟨Θ', hcovOut, denOut, Θ'_ext, Θ'_none,
        respectsOut, Θ'_dom, specsTrue, hdenOut,
        hdenOut_type, resultSwap⟩ := goodSemSwap Θ hcovT hcovS
      Θ_none respectsT respectsS Θ_dom G F hG hF denT denS
      hdenT hdenS G_rel F_rel
    exact ⟨Θ', hcovOut, denOut, Θ'_ext, Θ'_none,
      respectsOut, Θ'_dom, specsTrue, hdenOut, hdenOut_type,
      result_comm (hF := hF) (hG := hG) resultSwap⟩
  · intro Γsup scope Θ hcovS hcovT respectsS respectsT
      F G hF hG denS denT hdenS hdenT hdenS_type hdenT_type
      F_rel G_rel hcovOut denOut respectsOut specsTrue
      hdenOut hdenOut_type
    obtain ⟨_goodSemSwap, guardSwap⟩ := semSwap
    exact result_comm (hF := hF) (hG := hG)
      (guardSwap Γsup scope Θ hcovT hcovS
      respectsT respectsS G F hG hF denT denS hdenT hdenS
      hdenT_type hdenS_type G_rel F_rel hcovOut denOut
      respectsOut specsTrue hdenOut hdenOut_type)

theorem chpred_rev_scoped_contract.{u}
    (τ : BType) (ρ σ : SMTType)
    (hρ : BType.SupportedSMT τ ρ)
    (hσ : BType.SupportedSMT τ σ)
    (hne : ρ ≠ σ) (hcast : σ ⊑ ρ)
    (S T : SMT.Term) :
    CastUnionRepScopedSpec.{u} τ S T
      (SMTType.fun ρ SMTType.bool)
      (SMTType.fun σ SMTType.bool) := by
  have hswap :
      castUnion
          (S, SMTType.fun ρ SMTType.bool)
          (T, SMTType.fun σ SMTType.bool) =
        castUnion
          (T, SMTType.fun σ SMTType.bool)
          (S, SMTType.fun ρ SMTType.bool) := by
    simp only [castUnion]
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
  unfold CastUnionRepScopedSpec
  intro Λ n used decl typS typT bvS_used bvT_used
  exact of_swap τ S T
    (SMTType.fun ρ SMTType.bool)
    (SMTType.fun σ SMTType.bool) hswap
    (chpred_scoped_contract τ σ ρ hσ hρ hne.symm hcast T S)
    typS typT bvS_used bvT_used

theorem graph_rev_scoped_contract.{u}
    (α β : BType) (S T : SMT.Term) :
    CastUnionRepScopedSpec.{u} (α ×ᴮ β) S T
      (SMTType.fun (SMTType.pair α.toSMTType β.toSMTType)
        SMTType.bool)
      (SMTType.fun α.toSMTType (SMTType.option β.toSMTType)) := by
  have hswap :
      castUnion
          (S, SMTType.fun
            (SMTType.pair α.toSMTType β.toSMTType) SMTType.bool)
          (T, SMTType.fun α.toSMTType
            (SMTType.option β.toSMTType)) =
        castUnion
          (T, SMTType.fun α.toSMTType
            (SMTType.option β.toSMTType))
          (S, SMTType.fun
            (SMTType.pair α.toSMTType β.toSMTType) SMTType.bool) := by
    simp only [castUnion]
    have hne :
        SMTType.fun (SMTType.pair α.toSMTType β.toSMTType)
            SMTType.bool ≠
          SMTType.fun α.toSMTType (SMTType.option β.toSMTType) := by
      simp
    have hne' :
        SMTType.fun α.toSMTType (SMTType.option β.toSMTType) ≠
          SMTType.fun (SMTType.pair α.toSMTType β.toSMTType)
            SMTType.bool := hne.symm
    have hnot : ¬
        SMTType.fun (SMTType.pair α.toSMTType β.toSMTType)
            SMTType.bool ⊑
          SMTType.fun α.toSMTType (SMTType.option β.toSMTType) := by
      intro h
      have := castable?_of_fun_bool h
      contradiction
    let hα : α.toSMTType ⊑ α.toSMTType := castable?.reflexive
    let hβ : β.toSMTType ⊑ β.toSMTType := castable?.reflexive
    let hgraph :
        SMTType.fun α.toSMTType (SMTType.option β.toSMTType) ⊑
          SMTType.fun (SMTType.pair α.toSMTType β.toSMTType)
            SMTType.bool := castable?.graph hα hβ
    rw [dif_neg hne, dif_neg hnot, dif_pos hgraph,
      dif_neg hne', dif_pos hgraph]
  unfold CastUnionRepScopedSpec
  intro Λ n used decl typS typT bvS_used bvT_used
  exact of_swap (α ×ᴮ β) S T
    (SMTType.fun (SMTType.pair α.toSMTType β.toSMTType)
      SMTType.bool)
    (SMTType.fun α.toSMTType (SMTType.option β.toSMTType))
    hswap (graph_scoped_contract α β T S)
    typS typT bvS_used bvT_used

private theorem castable_chpredE {ρ σ : SMTType}
    (h : SMTType.fun ρ SMTType.bool ⊑
      SMTType.fun σ SMTType.bool) : ρ ⊑ σ := by
  cases h with
  | refl hbase => nomatch hbase
  | chpred hρ => exact hρ
  | «fun» hbool _ _ => exact (hbool rfl).elim

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

private theorem incomparable_scoped_contract.{u}
    (τ : BType) (S T : SMT.Term) (σS σT : SMTType)
    (hne : σS ≠ σT) (hST : ¬σS ⊑ σT) (hTS : ¬σT ⊑ σS) :
    CastUnionRepScopedSpec.{u} τ S T σS σT := by
  unfold CastUnionRepScopedSpec
  intro Λ n used decl typS typT bvS_used bvT_used
  mstart
  mintro pre ∀St
  mpure pre
  simp only [castUnion]
  rw [dif_neg hne, dif_neg hST, dif_neg hTS]
  mvcgen

private theorem option_scoped_contract.{u}
    (α β : BType) (S T : SMT.Term) :
    CastUnionRepScopedSpec.{u} (α ×ᴮ β) S T
      (SMTType.fun α.toSMTType (SMTType.option β.toSMTType))
      (SMTType.fun α.toSMTType (SMTType.option β.toSMTType)) := by
  unfold CastUnionRepScopedSpec
  intro Λ n used decl typS typT bvS_used bvT_used
  mstart
  mintro pre ∀St
  mpure pre
  unfold castUnion
  simp
  mvcgen

theorem supported_scoped_contract.{u}
    (τ : BType) (S T : SMT.Term) (σS σT : SMTType)
    (supportedS : BType.SupportedSMT (BType.set τ) σS)
    (supportedT : BType.SupportedSMT (BType.set τ) σT) :
    CastUnionRepScopedSpec.{u} τ S T σS σT := by
  unfold CastUnionRepScopedSpec
  intro Λ n used decl typS typT bvS_used bvT_used
  cases supportedS with
  | @setPred τ ρ hρ =>
      cases supportedT with
      | @setPred _ σ hσ =>
          by_cases heq : ρ = σ
          · subst σ
            exact direct_scoped_contract τ ρ hρ S T
              typS typT bvS_used bvT_used
          · by_cases hcast : ρ ⊑ σ
            · exact chpred_scoped_contract τ ρ σ hρ hσ
                heq hcast S T typS typT bvS_used bvT_used
            · by_cases hrev : σ ⊑ ρ
              · exact chpred_rev_scoped_contract τ ρ σ hρ hσ
                  heq hrev S T typS typT bvS_used bvT_used
              · exact incomparable_scoped_contract τ S T
                  (SMTType.fun ρ SMTType.bool)
                  (SMTType.fun σ SMTType.bool)
                  (by simpa using heq)
                  (fun h => hcast (castable_chpredE h))
                  (fun h => hrev (castable_chpredE h))
                  typS typT bvS_used bvT_used
      | optionFun α β =>
          have hne : SMTType.fun ρ SMTType.bool ≠
              SMTType.fun α.toSMTType
                (SMTType.option β.toSMTType) := by simp
          have hforward := not_castable_chpred_option
            ρ α.toSMTType β.toSMTType
          by_cases hgraph : SMTType.fun α.toSMTType
              (SMTType.option β.toSMTType) ⊑
            SMTType.fun ρ SMTType.bool
          · have hρeq :=
              supported_prod_eq_canonical_of_graph_cast hρ hgraph
            subst ρ
            exact graph_rev_scoped_contract α β S T
              typS typT bvS_used bvT_used
          · exact incomparable_scoped_contract (α ×ᴮ β) S T
              (SMTType.fun ρ SMTType.bool)
              (SMTType.fun α.toSMTType
                (SMTType.option β.toSMTType))
              hne hforward hgraph typS typT bvS_used bvT_used
  | optionFun α β =>
      cases supportedT with
      | @setPred _ ρ hρ =>
          have hne : SMTType.fun α.toSMTType
                (SMTType.option β.toSMTType) ≠
              SMTType.fun ρ SMTType.bool := by simp
          have hreverse := not_castable_chpred_option
            ρ α.toSMTType β.toSMTType
          by_cases hgraph : SMTType.fun α.toSMTType
              (SMTType.option β.toSMTType) ⊑
            SMTType.fun ρ SMTType.bool
          · have hρeq :=
              supported_prod_eq_canonical_of_graph_cast hρ hgraph
            subst ρ
            exact graph_scoped_contract α β S T
              typS typT bvS_used bvT_used
          · exact incomparable_scoped_contract (α ×ᴮ β) S T
              (SMTType.fun α.toSMTType
                (SMTType.option β.toSMTType))
              (SMTType.fun ρ SMTType.bool)
              hne hgraph hreverse typS typT bvS_used bvT_used
      | optionFun =>
          exact option_scoped_contract α β S T
            typS typT bvS_used bvT_used

end EncodeTermRepresentedScopedUnion
