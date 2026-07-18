import SMT.Reasoning.Basic.EncodeTermRepresentedScopedMaplet
import SMT.Reasoning.Basic.EncodeTermRepresentedInter
import SMT.Reasoning.Basic.EncodeTermRepresentedMem
import SMT.Reasoning.Basic.LoosenAuxExactUniv

open Std.Do B SMT ZFSet Classical

/-! # Generated-helper contract for represented intersection -/

/-- Soundness of a completed intersection cast under an arbitrary valuation of its
generated helpers. -/
abbrev CastInterRepGuardedSemantics.{u}
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
            (⟨F ∩ G, BType.set τ, set_inter_mem hF hG⟩ : B.Dom)
            denOut

/-- Satisfying-assignment construction paired with guarded soundness. -/
abbrev CastInterRepSemantics.{u}
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
            (⟨F ∩ G, BType.set τ, set_inter_mem hF hG⟩ : B.Dom)
            denOut) ∧
  CastInterRepGuardedSemantics.{u}
    τ S T out σS σT σout Λ Dlt

/-- Operational intersection contract carrying its exact declaration delta. -/
abbrev CastInterRepScopedSpec.{u} (τ : BType)
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
    castInter ⟨S, σS⟩ ⟨T, σT⟩
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
          CastInterRepSemantics.{u} τ S T out σS σT σout
            Λ Γ' used E'.usedVars Dlt ∧
          (∀ b ∈ specBodies Dlt, Γ' ⊢ˢ b : SMTType.bool) ∧
          ScopedGeneratedTyping Λ Dlt out σout⌝⦄

namespace EncodeTermRepresentedScopedInter

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
    castInter ⟨S, SMTType.fun ρ SMTType.bool⟩
      ⟨T, SMTType.fun ρ SMTType.bool⟩
    ⦃⇓? ⟨out, σout⟩ ⟨E', Γ'⟩ =>
      ⌜∃ z : SMT.𝒱,
        out = SMT.Term.lambda [z] [ρ]
          (.and (.app S (.var z)) (.app T (.var z))) ∧
        σout = SMTType.fun ρ SMTType.bool ∧
        Γ' = Λ ∧ E'.declarations = decl ∧
        z ∉ SMT.fv S ∧ z ∉ SMT.fv T⌝⦄ := by
  have hcast :
      castInter ⟨S, SMTType.fun ρ SMTType.bool⟩
          ⟨T, SMTType.fun ρ SMTType.bool⟩ = do
        let z ← SMT.freshVar ρ "inter!"
        SMT.eraseFromContext z
        return (SMT.Term.lambda [z] [ρ]
          (.and (.app S (.var z)) (.app T (.var z))),
          SMTType.fun ρ SMTType.bool) := by
    unfold castInter
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

/-- The direct pointwise intersection lambda is sound under every valuation of its
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
        (.and (.app S (.var z)) (.app T (.var z)))))
    (denOut : SMT.Dom.{u})
    (hdenOut :
      ⟦(SMT.Term.lambda [z] [ρ]
        (.and (.app S (.var z)) (.app T (.var z)))).abstract
          Θ hcovOut⟧ˢ = some denOut) :
    RDomCastSupported
      (⟨F ∩ G, BType.set τ, set_inter_mem hF hG⟩ : B.Dom)
      denOut := by
  obtain ⟨denU, hdenU, denU_type, _hretU, hpointU⟩ :=
    castInter_denotation_direct hcovS hcovT hdenS hdenT
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
  exact represented_setPred_inter_of_pointwise hρ hF hG
    hFenc hGenc hU F_rel G_rel hpointU

set_option maxHeartbeats 2500000 in
theorem direct_scoped_contract.{u}
    (τ : BType) (ρ : SMTType) (hρ : BType.SupportedSMT τ ρ)
    (S T : SMT.Term) :
    CastInterRepScopedSpec.{u} τ S T
      (SMTType.fun ρ SMTType.bool)
      (SMTType.fun ρ SMTType.bool) := by
  unfold CastInterRepScopedSpec
  intro Λ n used decl typS typT bvS_used bvT_used
  mstart
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_keys, rfl, rfl⟩ := pre
  mspec (Std.Do.Triple.and _
    (castInter_direct_rep_contract τ ρ hρ S T
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
the helper to denote the cast of the source set.  The final pointwise intersection
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
        (.and (.app (.var helper) (.var z)) (.app T (.var z)))))
    (denOut : SMT.Dom.{u})
    (respectsOut : SMT.RenamingContext.RespectsTypeContextOnFV Θ Γsup
      (SMT.Term.lambda [z] [ρ]
        (.and (.app (.var helper) (.var z)) (.app T (.var z)))))
    (specsTrue : SpecBodiesTrue Θ Γsup
      (helperSpecChunk helper (SMTType.fun ρ SMTType.bool) spec))
    (hdenOut :
      ⟦(SMT.Term.lambda [z] [ρ]
        (.and (.app (.var helper) (.var z)) (.app T (.var z)))).abstract
          Θ hcovOut⟧ˢ = some denOut) :
    RDomCastSupported
      (⟨F ∩ G, BType.set τ, set_inter_mem hF hG⟩ : B.Dom)
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
        (.and (.app (.var helper) (.var z)) (.app T (.var z)))) := by
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
      castInter (S, σS) (T, SMTType.fun ρ SMTType.bool) = do
        let ⟨helper, spec⟩ ← loosenAux_prf "inter!" c S
        declareConstWithSpec helper (SMTType.fun ρ SMTType.bool) spec
        castInter
          (SMT.Term.var helper, SMTType.fun ρ SMTType.bool)
          (T, SMTType.fun ρ SMTType.bool)) :
    CastInterRepScopedSpec.{u} τ S T σS
      (SMTType.fun ρ SMTType.bool) := by
  unfold CastInterRepScopedSpec
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
    (castInter_direct_rep_contract τ ρ hρ (.var helper) T
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
    CastInterRepScopedSpec.{u} τ S T
      (SMTType.fun ρ SMTType.bool)
      (SMTType.fun σ SMTType.bool) := by
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
  have hvia : castInter.chpred S T hcast.toCastPath = (do
      let ⟨helper, spec⟩ ← loosenAux_prf "inter!"
        (castPath.chpred hcast.toCastPath) S
      declareConstWithSpec helper (SMTType.fun σ SMTType.bool) spec
      castInter
        (SMT.Term.var helper, SMTType.fun σ SMTType.bool)
        (T, SMTType.fun σ SMTType.bool)) := by
    unfold castInter.chpred SMT.declareConstWithSpec castInter
    simp
  unfold CastInterRepScopedSpec
  intro Λ n used decl typS typT bvS_used bvT_used
  exact left_helper_scoped_contract τ σ
    (SMTType.fun ρ SMTType.bool) hσ (.setPred hρ) S T
    (castPath.chpred hcast.toCastPath)
    (castPath.fvFaithful _) (hcastInter.trans hvia)
    typS typT bvS_used bvT_used

theorem graph_scoped_contract.{u}
    (α β : BType) (S T : SMT.Term) :
    CastInterRepScopedSpec.{u} (α ×ᴮ β) S T
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
  have hcastInter :
      castInter
        (S, SMTType.fun α.toSMTType (SMTType.option β.toSMTType))
        (T, SMTType.fun (SMTType.pair α.toSMTType β.toSMTType)
          SMTType.bool) = castInter.graph S T cα cβ := by
    simp only [castInter]
    rw [dif_neg (by simp)]
    let hα : α.toSMTType ⊑ α.toSMTType := castable?.reflexive
    let hβ : β.toSMTType ⊑ β.toSMTType := castable?.reflexive
    let hgraph :
        SMTType.fun α.toSMTType (SMTType.option β.toSMTType) ⊑
          SMTType.fun (SMTType.pair α.toSMTType β.toSMTType)
            SMTType.bool := castable?.graph hα hβ
    rw [dif_pos hgraph]
    unfold castInterAux
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
  have hvia : castInter.graph S T cα cβ = (do
      let ⟨helper, spec⟩ ← loosenAux_prf "inter!" c S
      declareConstWithSpec helper
        (SMTType.fun (SMTType.pair α.toSMTType β.toSMTType)
          SMTType.bool) spec
      castInter
        (SMT.Term.var helper,
          SMTType.fun (SMTType.pair α.toSMTType β.toSMTType)
            SMTType.bool)
        (T, SMTType.fun (SMTType.pair α.toSMTType β.toSMTType)
          SMTType.bool)) := by
    unfold castInter.graph SMT.declareConstWithSpec castInter c cα cβ
    simp
  unfold CastInterRepScopedSpec
  intro Λ n used decl typS typT bvS_used bvT_used
  exact left_helper_scoped_contract (α ×ᴮ β)
    (SMTType.pair α.toSMTType β.toSMTType)
    (SMTType.fun α.toSMTType (SMTType.option β.toSMTType))
    (BType.SupportedSMT.canonical (α ×ᴮ β)) (.optionFun α β)
    S T c (castPath.fvFaithful c) (hcastInter.trans hvia)
    typS typT bvS_used bvT_used

theorem result_comm.{u}
    {τ : BType} {F G : ZFSet.{u}}
    {hF : F ∈ ⟦BType.set τ⟧ᶻ}
    {hG : G ∈ ⟦BType.set τ⟧ᶻ}
    {den : SMT.Dom.{u}}
    (rel : RDomCastSupported
      (⟨G ∩ F, BType.set τ, set_inter_mem hG hF⟩ : B.Dom) den) :
    RDomCastSupported
      (⟨F ∩ G, BType.set τ, set_inter_mem hF hG⟩ : B.Dom) den := by
  rcases den with ⟨Uval, σU, hUval⟩
  obtain ⟨⟨⟨c, hret⟩, hadmissible⟩, hsupported⟩ := rel
  refine ⟨⟨⟨c, ?_⟩, ?_⟩, hsupported⟩
  · calc
      retract (BType.set τ) (castZF_apply c Uval) = G ∩ F := hret
      _ = F ∩ G := ZFSet.inter_comm
  · have hinter : G ∩ F = F ∩ G := ZFSet.inter_comm
    simpa only [hinter, proof_irrel_heq] using hadmissible

theorem of_swap.{u}
    (τ : BType) (S T : SMT.Term) (σS σT : SMTType)
    (hswap : castInter (S, σS) (T, σT) =
      castInter (T, σT) (S, σS))
    (swapped : CastInterRepScopedSpec.{u} τ T S σT σS) :
    CastInterRepScopedSpec.{u} τ S T σS σT := by
  unfold CastInterRepScopedSpec
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
    CastInterRepScopedSpec.{u} τ S T
      (SMTType.fun ρ SMTType.bool)
      (SMTType.fun σ SMTType.bool) := by
  have hswap :
      castInter
          (S, SMTType.fun ρ SMTType.bool)
          (T, SMTType.fun σ SMTType.bool) =
        castInter
          (T, SMTType.fun σ SMTType.bool)
          (S, SMTType.fun ρ SMTType.bool) := by
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
  unfold CastInterRepScopedSpec
  intro Λ n used decl typS typT bvS_used bvT_used
  exact of_swap τ S T
    (SMTType.fun ρ SMTType.bool)
    (SMTType.fun σ SMTType.bool) hswap
    (chpred_scoped_contract τ σ ρ hσ hρ hne.symm hcast T S)
    typS typT bvS_used bvT_used

theorem graph_rev_scoped_contract.{u}
    (α β : BType) (S T : SMT.Term) :
    CastInterRepScopedSpec.{u} (α ×ᴮ β) S T
      (SMTType.fun (SMTType.pair α.toSMTType β.toSMTType)
        SMTType.bool)
      (SMTType.fun α.toSMTType (SMTType.option β.toSMTType)) := by
  have hswap :
      castInter
          (S, SMTType.fun
            (SMTType.pair α.toSMTType β.toSMTType) SMTType.bool)
          (T, SMTType.fun α.toSMTType
            (SMTType.option β.toSMTType)) =
        castInter
          (T, SMTType.fun α.toSMTType
            (SMTType.option β.toSMTType))
          (S, SMTType.fun
            (SMTType.pair α.toSMTType β.toSMTType) SMTType.bool) := by
    simp only [castInter]
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
  unfold CastInterRepScopedSpec
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
    CastInterRepScopedSpec.{u} τ S T σS σT := by
  unfold CastInterRepScopedSpec
  intro Λ n used decl typS typT bvS_used bvT_used
  mstart
  mintro pre ∀St
  mpure pre
  simp only [castInter]
  rw [dif_neg hne, dif_neg hST, dif_neg hTS]
  mvcgen

private theorem option_scoped_contract.{u}
    (α β : BType) (S T : SMT.Term) :
    CastInterRepScopedSpec.{u} (α ×ᴮ β) S T
      (SMTType.fun α.toSMTType (SMTType.option β.toSMTType))
      (SMTType.fun α.toSMTType (SMTType.option β.toSMTType)) := by
  unfold CastInterRepScopedSpec
  intro Λ n used decl typS typT bvS_used bvT_used
  mstart
  mintro pre ∀St
  mpure pre
  unfold castInter
  simp
  mvcgen

theorem supported_scoped_contract.{u}
    (τ : BType) (S T : SMT.Term) (σS σT : SMTType)
    (supportedS : BType.SupportedSMT (BType.set τ) σS)
    (supportedT : BType.SupportedSMT (BType.set τ) σT) :
    CastInterRepScopedSpec.{u} τ S T σS σT := by
  unfold CastInterRepScopedSpec
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

theorem pair_helper_typing
    {Base Λop Γop : SMT.TypeContext}
    {Dpre Dlt : SMT.Chunk}
    {P out : SMT.Term} {σP σout : SMTType}
    (envelope : DeclarationContextEnvelope Base Dpre Λop)
    (step : DeclarationContextTrace Λop Dlt Γop)
    (typP_op : Λop ⊢ˢ P : σP)
    (typOut_op : Γop ⊢ˢ out : σout)
    (specs_op : ∀ b ∈ specBodies Dlt,
      Γop ⊢ˢ b : SMTType.bool)
    (P_typing : ScopedGeneratedTyping Base Dpre P σP)
    (out_fv : SMT.fv out ⊆ SMT.fv P ∪ declVars Dlt)
    (specs_fv : ∀ b ∈ specBodies Dlt,
      SMT.fv b ⊆ SMT.fv P ∪ declVars Dlt) :
    DeclarationContextEnvelope Base (Dpre ++ Dlt) Γop ∧
      ScopedGeneratedTyping Base (Dpre ++ Dlt) out σout := by
  obtain ⟨Core, pre_trace, Core_sub_op⟩ := envelope
  obtain ⟨Core', step', Core'_sub_op⟩ :=
    step.rebase_subset Core_sub_op
  have P_bv_fresh : ∀ v ∈ SMT.bv P, v ∉ Core := by
    intro v hv hvCore
    exact SMT.Typing.bv_notMem_context typP_op v hv
      (AList.mem_of_subset Core_sub_op hvCore)
  have typP_Core : Core ⊢ˢ P : σP :=
    P_typing.1 Core pre_trace.scoped_extends P_bv_fresh
  have dependency_mem_Core' :
      ∀ {v}, v ∈ SMT.fv P ∪ declVars Dlt → v ∈ Core' := by
    intro v hv
    rw [List.mem_union_iff] at hv
    rcases hv with hvP | hvdecl
    · exact AList.mem_of_subset step'.entries_subset
        (SMT.Typing.mem_context_of_mem_fv typP_Core hvP)
    · exact step'.declVar_mem hvdecl
  have typOut_Core' : Core' ⊢ˢ out : σout :=
    SMT.Typing.strengthening_of_fv_subset Core'_sub_op typOut_op
      (fun v hv => dependency_mem_Core' (out_fv hv))
  have specs_Core' : ∀ b ∈ specBodies Dlt,
      Core' ⊢ˢ b : SMTType.bool := by
    intro b hb
    exact SMT.Typing.strengthening_of_fv_subset Core'_sub_op
      (specs_op b hb)
      (fun v hv => dependency_mem_Core' (specs_fv b hb hv))
  have local_typing : ScopedGeneratedTyping Core Dlt out σout :=
    ScopedGeneratedTyping.of_operational step'.context_generated
      typOut_Core' specs_Core'
  exact ⟨
    ⟨Core', DeclarationContextTrace.append pre_trace step',
      Core'_sub_op⟩,
    local_typing.append_prefix pre_trace P_typing.2⟩

private theorem encodeTerm_inter_via_maplet_scoped
    (S T : B.Term) (E : B.Env) :
    encodeTerm (S ∩ᴮ T) E = (do
      let ⟨p, σp⟩ ← encodeTerm (S ↦ᴮ T) E
      match p, σp with
      | .pair S' T', .pair σS σT =>
          castInter ⟨S', σS⟩ ⟨T', σT⟩
      | _, _ => throw "encodeTerm:intersection: impossible maplet result") := by
  simp [encodeTerm]

private theorem denote_pair_inv_scoped.{u}
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
      d = ⟨dx.fst.pair dy.fst,
        SMTType.pair dx.snd.fst dy.snd.fst,
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

private theorem denote_inter_inv_scoped.{u}
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
  refine ⟨F, G, hF, hG, ?_, ?_, rfl⟩
  · simpa only [proof_irrel_heq] using denS
  · simpa only [proof_irrel_heq] using denT

set_option maxHeartbeats 10000000 in
theorem encodeTerm_rep_scoped.inter_case_from.{u}
    (S T : B.Term)
    (S_ih : EncodeTermRepIH.{u} S)
    (T_ih : EncodeTermRepIH.{u} T)
    (S_scoped : EncodeTermRepScopedFromIH.{u} S)
    (T_scoped : EncodeTermRepScopedFromIH.{u} T)
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
    (Λ_inv : ∀ v ∈ (S ∩ᴮ T).vars,
      v ∈ Λ → v ∈ E.context)
    (bv_nodup : (B.bv (S ∩ᴮ T)).Nodup)
    (respects : B.RenamingContext.RespectsTypeContextOnFV
      Δ₀ Λ (S ∩ᴮ T))
    (fv_in_Λ : ∀ v ∈ B.fv (S ∩ᴮ T), v ∈ Λ)
    (wf : B.RenWF E.context «Δ»)
    {Base : SMT.TypeContext} {Dpre : SMT.Chunk}
    (input_envelope : DeclarationContextEnvelope Base Dpre Λ)
    (fv_in_Base : ∀ v ∈ B.fv (S ∩ᴮ T), v ∈ Base)
    (Dpre_typing : ScopedSpecsTyping Base Dpre)
    {n : ℕ} {decl : SMT.Chunk} :
    ⦃fun ⟨E0, Λ'⟩ ↦
      ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧
        Λ.keys ⊆ E0.usedVars ∧ E0.usedVars = used ∧
        E0.declarations = decl⌝ ⦄
    encodeTerm (S ∩ᴮ T) E
    ⦃⇓? (⟨t', σ⟩ : SMT.Term × SMTType) ⟨E', Γ'⟩ =>
      ⌜EncodeTermRepScopedPostFrom.{u} (S ∩ᴮ T) E α
        Base Dpre Λ decl t' σ E' Γ'⌝ ⦄ := by
  mstart
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_keys, St_used_eq, St_decl_eq⟩ := pre
  rw [encodeTerm_inter_via_maplet_scoped]
  obtain ⟨τ, rfl, typS, typT⟩ := B.Typing.interE typ_t
  obtain ⟨F, G, hF, hG, denS, denT, rfl⟩ :=
    denote_inter_inv_scoped Δ_fv den_t
  let Δ_fv_pair : ∀ v ∈ B.fv (S ↦ᴮ T),
      («Δ» v).isSome = true :=
    fun v hv => Δ_fv v (by simpa [B.fv] using hv)
  have den_pair :
      ⟦(S ↦ᴮ T).abstract «Δ» Δ_fv_pair⟧ᴮ =
        some ⟨F.pair G,
          ⟨BType.set τ ×ᴮ BType.set τ,
            ZFSet.pair_mem_prod.mpr ⟨hF, hG⟩⟩⟩ := by
    rw [B.Term.abstract, B.denote, Option.pure_def,
      Option.bind_eq_bind]
    have denS' :
        ⟦S.abstract «Δ» (fun v hv => Δ_fv_pair v (by
          rw [B.fv, List.mem_append]
          exact Or.inl hv))⟧ᴮ =
          some ⟨F, ⟨BType.set τ, hF⟩⟩ := by
      simpa only [proof_irrel_heq] using denS
    have denT' :
        ⟦T.abstract «Δ» (fun v hv => Δ_fv_pair v (by
          rw [B.fv, List.mem_append]
          exact Or.inr hv))⟧ᴮ =
          some ⟨G, ⟨BType.set τ, hG⟩⟩ := by
      simpa only [proof_irrel_heq] using denT
    rw [denS', Option.bind_some, denT']
    rfl
  mspec (Std.Do.Triple.and _
    (Std.Do.Triple.and _
      (encodeTerm_rep_spec.maplet_case S T S_ih T_ih E
        (B.Typing.maplet typS typT) Δ_fv_pair
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
      (encodeTerm_rep_scoped.maplet_case_from S T S_ih T_ih
        S_scoped T_scoped E (B.Typing.maplet typS typT)
        Δ_fv_pair (by simpa [B.fv] using related)
        Δ₀_none_out Δ₀_dom den_pair
        (fun v hv => vars_used v (by
          simpa [B.Term.vars, B.fv, B.bv] using hv))
        (fun v hv => Λ_inv v (by
          simpa [B.Term.vars, B.fv, B.bv] using hv))
        (by simpa [B.bv] using bv_nodup)
        (by simpa [B.fv] using respects)
        (fun v hv => fv_in_Λ v (by simpa [B.fv] using hv)) wf
        input_envelope
        (fun v hv => fv_in_Base v (by simpa [B.fv] using hv))
        Dpre_typing (n := St.env.freshvarsc)
        (decl := St.env.declarations)))
    (encodeTerm_bv_used E (t := S ↦ᴮ T)
      (used := St.env.usedVars) (n := St.env.freshvarsc)
      (decl := St.env.declarations)))
  rename_i outPair
  obtain ⟨Penc, σP⟩ := outPair
  mrename_i post
  mintro ∀Stp
  mpure post
  dsimp at post
  obtain ⟨⟨Ppost, Pscoped⟩, bvP_used, _used_struct,
      DltP_struct, P_decl_struct, P_delta_ok⟩ := post
  obtain ⟨DltP, P_decl_eq, P_trace, P_envelope, P_total, P_guard,
      P_specs_op, P_sc_typing⟩ := Pscoped
  have DltP_eq : DltP = DltP_struct := by
    rw [P_decl_eq, St_decl_eq] at P_decl_struct
    exact List.append_right_injective decl P_decl_struct
  subst DltP_struct
  obtain ⟨used_sub_P, types_sub_P, keys_sub_P, _covers_P,
      _path_P, typP, shapeP, _preserves_P,
      ΔP, hcovP, ΔP_ext, _related_P, ΔP_none, _respects_P,
      target_respects_P, ΔP_dom, denP, hdenP, hdenP_type,
      P_rel, _P_total_old⟩ := Ppost
  obtain ⟨Senc, Tenc, σS, σT, P_eq, σP_eq⟩ := shapeP
  subst Penc
  subst σP
  rw [σP_eq] at typP
  rw [σP_eq]
  obtain ⟨σS', σT', P_type_eq, typSenc, typTenc⟩ :=
    SMT.Typing.pairE typP
  injection P_type_eq with hσS hσT
  subst σS'
  subst σT'
  have hcovSenc : RenamingContext.CoversFV ΔP Senc := by
    intro v hv
    exact hcovP v (by
      rw [SMT.fv, List.mem_append]
      exact Or.inl hv)
  have hcovTenc : RenamingContext.CoversFV ΔP Tenc := by
    intro v hv
    exact hcovP v (by
      rw [SMT.fv, List.mem_append]
      exact Or.inr hv)
  have target_respects_Senc :
      SMT.RenamingContext.RespectsTypeContextOnFV ΔP Stp.types Senc := by
    intro v ξ hv hlookup
    exact target_respects_P (by
      rw [SMT.fv, List.mem_append]
      exact Or.inl hv) hlookup
  have target_respects_Tenc :
      SMT.RenamingContext.RespectsTypeContextOnFV ΔP Stp.types Tenc := by
    intro v ξ hv hlookup
    exact target_respects_P (by
      rw [SMT.fv, List.mem_append]
      exact Or.inr hv) hlookup
  obtain ⟨denSenc, denTenc, hdenSenc, hdenTenc, denP_eq⟩ :=
    denote_pair_inv_scoped hcovP hdenP
  rw [denP_eq] at σP_eq P_rel
  rcases denSenc with ⟨Fenc, σSden, hFenc⟩
  rcases denTenc with ⟨Genc, σTden, hGenc⟩
  dsimp at σP_eq
  injection σP_eq with hσSden hσTden
  subst σSden
  subst σTden
  have denP_type_eq : denP.snd.fst = SMTType.pair σS σT := by
    rw [denP_eq]
  rw [denP_type_eq] at P_total P_guard P_sc_typing
  have P_rel' : RDomCastSupported
      (⟨F.pair G, BType.set τ ×ᴮ BType.set τ,
        ZFSet.pair_mem_prod.mpr ⟨hF, hG⟩⟩ : B.Dom)
      (⟨Fenc.pair Genc, SMTType.pair σS σT,
        ZFSet.pair_mem_prod.mpr ⟨hFenc, hGenc⟩⟩ : SMT.Dom) := by
    simpa only [proof_irrel_heq] using P_rel
  obtain ⟨F_rel, G_rel⟩ := RDomCastSupported.of_pair
    (hX := hF) (hY := hG) (hX' := hFenc) (hY' := hGenc) P_rel'
  have bvSenc_used : ∀ v ∈ SMT.bv Senc, v ∈ Stp.env.usedVars := by
    intro v hv
    exact bvP_used v (by
      rw [SMT.bv, List.mem_append]
      exact Or.inl hv)
  have bvTenc_used : ∀ v ∈ SMT.bv Tenc, v ∈ Stp.env.usedVars := by
    intro v hv
    exact bvP_used v (by
      rw [SMT.bv, List.mem_append]
      exact Or.inr hv)
  mspec supported_scoped_contract τ Senc Tenc σS σT
    F_rel.supported G_rel.supported typSenc typTenc
    bvSenc_used bvTenc_used
  rename_i outU
  obtain ⟨Uenc, σU⟩ := outU
  mrename_i postU
  mintro ∀Stu
  mpure postU
  obtain ⟨used_sub_U, types_sub_U, keys_sub_U, pathU, typU,
      U_preserves, DltU, U_decl_eq, U_ctx, U_trace, U_decl_fresh,
      U_obsS, U_obsT, U_fv_dep, U_specs_fv_dep, U_sem,
      U_specs_op, _U_sc_typing⟩ := postU
  have P_fv_dep : SMT.fv Uenc ⊆
      SMT.fv (SMT.Term.pair Senc Tenc) ∪ declVars DltU := by
    intro v hv
    have h := U_fv_dep hv
    simp only [SMT.fv, List.mem_append, List.mem_union_iff] at h ⊢
    rcases h with (hS | hT) | hdecl
    · exact Or.inl (Or.inl hS)
    · exact Or.inl (Or.inr hT)
    · exact Or.inr hdecl
  have P_specs_fv_dep : ∀ b ∈ specBodies DltU,
      SMT.fv b ⊆ SMT.fv (SMT.Term.pair Senc Tenc) ∪
        declVars DltU := by
    intro b hb v hv
    have h := U_specs_fv_dep b hb hv
    simp only [SMT.fv, List.mem_append, List.mem_union_iff] at h ⊢
    rcases h with (hS | hT) | hdecl
    · exact Or.inl (Or.inl hS)
    · exact Or.inl (Or.inr hT)
    · exact Or.inr hdecl
  obtain ⟨U_envelope, U_sc_typing_clean⟩ :=
    pair_helper_typing P_envelope U_trace typP typU U_specs_op
      P_sc_typing P_fv_dep P_specs_fv_dep
  mpure_intro
  refine ⟨DltP ++ DltU, ?_, DeclarationContextTrace.append P_trace U_trace,
    (by simpa [List.append_assoc] using U_envelope), ?_, ?_, ?_, ?_⟩
  · simpa [P_decl_eq, St_decl_eq, List.append_assoc] using U_decl_eq
  · intro Δ_alt Δ_fv_alt Δ₀_alt related_alt wf_alt
      Δ₀_alt_none respects_alt Δ₀_alt_dom U_alt hU_alt den_alt
    obtain ⟨F_alt, G_alt, hF_alt, hG_alt,
        denS_alt, denT_alt, rfl⟩ :=
      denote_inter_inv_scoped Δ_fv_alt den_alt
    let Δ_fv_pair_alt : ∀ v ∈ B.fv (S ↦ᴮ T),
        (Δ_alt v).isSome = true :=
      fun v hv => Δ_fv_alt v (by simpa [B.fv] using hv)
    have den_pair_alt :
        ⟦(S ↦ᴮ T).abstract Δ_alt Δ_fv_pair_alt⟧ᴮ =
          some ⟨F_alt.pair G_alt,
            ⟨BType.set τ ×ᴮ BType.set τ,
              ZFSet.pair_mem_prod.mpr ⟨hF_alt, hG_alt⟩⟩⟩ := by
      rw [B.Term.abstract, B.denote, Option.pure_def,
        Option.bind_eq_bind]
      have denS_alt' :
          ⟦S.abstract Δ_alt (fun v hv => Δ_fv_pair_alt v (by
            rw [B.fv, List.mem_append]
            exact Or.inl hv))⟧ᴮ =
            some ⟨F_alt, ⟨BType.set τ, hF_alt⟩⟩ := by
        simpa only [proof_irrel_heq] using denS_alt
      have denT_alt' :
          ⟦T.abstract Δ_alt (fun v hv => Δ_fv_pair_alt v (by
            rw [B.fv, List.mem_append]
            exact Or.inr hv))⟧ᴮ =
            some ⟨G_alt, ⟨BType.set τ, hG_alt⟩⟩ := by
        simpa only [proof_irrel_heq] using denT_alt
      rw [denS_alt', Option.bind_some, denT_alt']
      rfl
    have Δ₀_alt_none_P : ∀ v ∉ Stp.env.usedVars,
        Δ₀_alt v = none := by
      intro v hv
      by_contra hne
      have hvΛ := Δ₀_alt_dom v hne
      have hvused : v ∈ used := by
        rw [← St_used_eq]
        exact St_keys hvΛ
      exact hv (used_sub_P hvused)
    obtain ⟨ΔP_alt, hcovP_alt, denP_alt, ΔP_alt_ext,
        _relatedP_alt, ΔP_alt_none, _respectsP_alt,
        target_respectsP_alt, ΔP_alt_dom, specsP_alt,
        hdenP_alt, hdenP_alt_type, P_alt_rel⟩ :=
      P_total Δ_alt Δ_fv_pair_alt Δ₀_alt
        (by simpa [B.fv] using related_alt) wf_alt
        Δ₀_alt_none_P (by simpa [B.fv] using respects_alt)
        Δ₀_alt_dom (F_alt.pair G_alt)
        (ZFSet.pair_mem_prod.mpr ⟨hF_alt, hG_alt⟩) den_pair_alt
    have hcovS_alt : RenamingContext.CoversFV ΔP_alt Senc := by
      intro v hv
      exact hcovP_alt v (by
        rw [SMT.fv, List.mem_append]
        exact Or.inl hv)
    have hcovT_alt : RenamingContext.CoversFV ΔP_alt Tenc := by
      intro v hv
      exact hcovP_alt v (by
        rw [SMT.fv, List.mem_append]
        exact Or.inr hv)
    have respectsS_alt : SMT.RenamingContext.RespectsTypeContextOnFV
        ΔP_alt Stp.types Senc := by
      intro v ξ hv hlookup
      exact target_respectsP_alt (by
        rw [SMT.fv, List.mem_append]
        exact Or.inl hv) hlookup
    have respectsT_alt : SMT.RenamingContext.RespectsTypeContextOnFV
        ΔP_alt Stp.types Tenc := by
      intro v ξ hv hlookup
      exact target_respectsP_alt (by
        rw [SMT.fv, List.mem_append]
        exact Or.inr hv) hlookup
    obtain ⟨denS_alt_t, denT_alt_t, hdenS_alt_t, hdenT_alt_t,
        denP_alt_eq⟩ := denote_pair_inv_scoped hcovP_alt hdenP_alt
    rw [denP_alt_eq] at hdenP_alt_type P_alt_rel
    rcases denS_alt_t with ⟨Fenc_alt, σS_alt, hFenc_alt⟩
    rcases denT_alt_t with ⟨Genc_alt, σT_alt, hGenc_alt⟩
    dsimp at hdenP_alt_type
    injection hdenP_alt_type with hσS_alt hσT_alt
    subst σS_alt
    subst σT_alt
    have P_alt_rel' : RDomCastSupported
        (⟨F_alt.pair G_alt, BType.set τ ×ᴮ BType.set τ,
          ZFSet.pair_mem_prod.mpr ⟨hF_alt, hG_alt⟩⟩ : B.Dom)
        (⟨Fenc_alt.pair Genc_alt, SMTType.pair σS σT,
          ZFSet.pair_mem_prod.mpr ⟨hFenc_alt, hGenc_alt⟩⟩ : SMT.Dom) := by
      simpa only [proof_irrel_heq] using P_alt_rel
    obtain ⟨F_alt_rel, G_alt_rel⟩ :=
      RDomCastSupported.of_pair P_alt_rel'
    obtain ⟨goodU, _guardU⟩ := U_sem
    obtain ⟨ΔU_alt, hcovU_alt, denU_alt, ΔU_alt_ext,
        ΔU_alt_none, target_respectsU_alt, ΔU_alt_dom,
        specsU_alt, hdenU_alt, hdenU_alt_type, U_alt_rel⟩ :=
      goodU ΔP_alt hcovS_alt hcovT_alt ΔP_alt_none
        respectsS_alt respectsT_alt ΔP_alt_dom F_alt G_alt
        hF_alt hG_alt
        (⟨Fenc_alt, σS, hFenc_alt⟩ : SMT.Dom)
        (⟨Genc_alt, σT, hGenc_alt⟩ : SMT.Dom)
        hdenS_alt_t hdenT_alt_t
        F_alt_rel.toRDomCast G_alt_rel.toRDomCast
    have ΔU_alt_ext0 :=
      RenamingContext.extends_trans ΔU_alt_ext ΔP_alt_ext
    have specsP_final : SpecBodiesTrue ΔU_alt Stu.types DltP :=
      specsP_alt.of_extends ΔU_alt_ext types_sub_U ΔP_alt_dom
    refine ⟨ΔU_alt, hcovU_alt, denU_alt, ΔU_alt_ext0,
      related_alt.of_extends ΔU_alt_ext0, ΔU_alt_none, ?_,
      target_respectsU_alt, ΔU_alt_dom,
      specsP_final.append specsU_alt, hdenU_alt,
      hdenU_alt_type, ?_⟩
    · exact respects_alt.of_extends ΔU_alt_ext0
        (fun _ h => types_sub_U (types_sub_P h))
        (fun _ h => h) fv_in_Λ
    · simpa only [proof_irrel_heq] using U_alt_rel
  · intro Γsup Γscope Δ_alt Δ_fv_alt Θ related_alt wf_alt
      respectsB respectsSMT specsTrue U_alt hU_alt den_alt
      hcovU denU hdenU hdenU_type
    have full_scope : ScopedContextExtends Base
        ((Dpre ++ DltP) ++ DltU) Γsup := by
      simpa [List.append_assoc] using Γscope
    have full_specs : SpecBodiesTrue Θ Γsup
        ((Dpre ++ DltP) ++ DltU) := by
      simpa [List.append_assoc] using specsTrue
    have P_scope : ScopedContextExtends Base
        (Dpre ++ DltP) Γsup := full_scope.left_of_append
    have P_specs_true : SpecBodiesTrue Θ Γsup (Dpre ++ DltP) :=
      full_specs.left_of_append
    have U_specs_true : SpecBodiesTrue Θ Γsup DltU :=
      full_specs.right_of_append
    obtain ⟨F_alt, G_alt, hF_alt, hG_alt,
        denS_alt, denT_alt, rfl⟩ :=
      denote_inter_inv_scoped Δ_fv_alt den_alt
    have hcovS_target : RenamingContext.CoversFV Θ Senc := by
      intro v hv
      rcases U_obsS v hv with hout | ⟨body, hbody, hvbody⟩
      · exact hcovU v hout
      · obtain ⟨hcovBody, _d, _resp, _hden, _hty, _htrue⟩ :=
          U_specs_true body hbody
        exact hcovBody v hvbody
    have hcovT_target : RenamingContext.CoversFV Θ Tenc := by
      intro v hv
      rcases U_obsT v hv with hout | ⟨body, hbody, hvbody⟩
      · exact hcovU v hout
      · obtain ⟨hcovBody, _d, _resp, _hden, _hty, _htrue⟩ :=
          U_specs_true body hbody
        exact hcovBody v hvbody
    have respectsS_sup : SMT.RenamingContext.RespectsTypeContextOnFV
        Θ Γsup Senc := by
      intro v ξ hv hlookup
      rcases U_obsS v hv with hout | ⟨body, hbody, hvbody⟩
      · exact respectsSMT hout hlookup
      · obtain ⟨_hcov, _d, respBody, _hden, _hty, _htrue⟩ :=
          U_specs_true body hbody
        exact respBody hvbody hlookup
    have respectsT_sup : SMT.RenamingContext.RespectsTypeContextOnFV
        Θ Γsup Tenc := by
      intro v ξ hv hlookup
      rcases U_obsT v hv with hout | ⟨body, hbody, hvbody⟩
      · exact respectsSMT hout hlookup
      · obtain ⟨_hcov, _d, respBody, _hden, _hty, _htrue⟩ :=
          U_specs_true body hbody
        exact respBody hvbody hlookup
    obtain ⟨UCore, U_clean_trace, UCore_sub_Stu⟩ := U_envelope
    have UCore_sub_sup : UCore ⊆ Γsup := by
      intro e he
      exact full_scope (U_clean_trace.context_generated he)
    have P_scope_Core : ScopedContextExtends Base
        (Dpre ++ DltP) UCore :=
      U_clean_trace.scoped_extends.left_of_append
    have P_bv_fresh_Core : ∀ v ∈ SMT.bv (SMT.Term.pair Senc Tenc),
        v ∉ UCore := by
      intro v hv hvCore
      exact U_preserves v (bvP_used v hv)
        (SMT.Typing.bv_notMem_context typP v hv)
        (AList.mem_of_subset UCore_sub_Stu hvCore)
    have typP_Core : UCore ⊢ˢ SMT.Term.pair Senc Tenc :
        SMTType.pair σS σT :=
      P_sc_typing.1 UCore P_scope_Core P_bv_fresh_Core
    obtain ⟨σSCore, σTCore, hPairCore, typS_Core, typT_Core⟩ :=
      SMT.Typing.pairE typP_Core
    injection hPairCore with hσSCore hσTCore
    subst σSCore
    subst σTCore
    have respectsS_Core : SMT.RenamingContext.RespectsTypeContextOnFV
        Θ UCore Senc := respectsS_sup.of_super UCore_sub_sup
    have respectsT_Core : SMT.RenamingContext.RespectsTypeContextOnFV
        Θ UCore Tenc := respectsT_sup.of_super UCore_sub_sup
    obtain ⟨denS_target, hdenS_target, hdenS_target_type⟩ :=
      SMT.RenamingContext.denote_exists_of_typing_fv
        typS_Core respectsS_Core hcovS_target
    obtain ⟨denT_target, hdenT_target, hdenT_target_type⟩ :=
      SMT.RenamingContext.denote_exists_of_typing_fv
        typT_Core respectsT_Core hcovT_target
    have hF_target_mem : denS_target.fst ∈ ⟦σS⟧ᶻ := by
      simpa [hdenS_target_type] using denS_target.snd.snd
    have hG_target_mem : denT_target.fst ∈ ⟦σT⟧ᶻ := by
      simpa [hdenT_target_type] using denT_target.snd.snd
    have hcovP_target : RenamingContext.CoversFV Θ
        (SMT.Term.pair Senc Tenc) := by
      intro v hv
      rw [SMT.fv, List.mem_append] at hv
      exact hv.elim (hcovS_target v) (hcovT_target v)
    have respectsP_sup : SMT.RenamingContext.RespectsTypeContextOnFV
        Θ Γsup (SMT.Term.pair Senc Tenc) := by
      intro v ξ hv hlookup
      rw [SMT.fv, List.mem_append] at hv
      exact hv.elim (fun h => respectsS_sup h hlookup)
        (fun h => respectsT_sup h hlookup)
    let denP_target : SMT.Dom.{u} :=
      ⟨denS_target.fst.pair denT_target.fst,
        SMTType.pair σS σT,
        ZFSet.pair_mem_prod.mpr ⟨hF_target_mem, hG_target_mem⟩⟩
    have hdenP_target :
        ⟦(SMT.Term.pair Senc Tenc).abstract Θ hcovP_target⟧ˢ =
          some denP_target := by
      rw [SMT.Term.abstract, SMT.denote, Option.pure_def,
        Option.bind_eq_bind]
      rw [hdenS_target, Option.bind_some, hdenT_target]
      simp [denP_target, hdenS_target_type, hdenT_target_type]
    let Δ_fv_pair_alt : ∀ v ∈ B.fv (S ↦ᴮ T),
        (Δ_alt v).isSome = true :=
      fun v hv => Δ_fv_alt v (by simpa [B.fv] using hv)
    have den_pair_alt :
        ⟦(S ↦ᴮ T).abstract Δ_alt Δ_fv_pair_alt⟧ᴮ =
          some ⟨F_alt.pair G_alt,
            ⟨BType.set τ ×ᴮ BType.set τ,
              ZFSet.pair_mem_prod.mpr ⟨hF_alt, hG_alt⟩⟩⟩ := by
      rw [B.Term.abstract, B.denote, Option.pure_def,
        Option.bind_eq_bind]
      have denS_alt' :
          ⟦S.abstract Δ_alt (fun v hv => Δ_fv_pair_alt v (by
            rw [B.fv, List.mem_append]
            exact Or.inl hv))⟧ᴮ =
            some ⟨F_alt, ⟨BType.set τ, hF_alt⟩⟩ := by
        simpa only [proof_irrel_heq] using denS_alt
      have denT_alt' :
          ⟦T.abstract Δ_alt (fun v hv => Δ_fv_pair_alt v (by
            rw [B.fv, List.mem_append]
            exact Or.inr hv))⟧ᴮ =
            some ⟨G_alt, ⟨BType.set τ, hG_alt⟩⟩ := by
        simpa only [proof_irrel_heq] using denT_alt
      rw [denS_alt', Option.bind_some, denT_alt']
      rfl
    have respectsB_pair : B.RenamingContext.RespectsTypeContextOnFV
        Θ Γsup (S ↦ᴮ T) := by
      simpa [B.fv] using respectsB
    have P_target_rel := P_guard Γsup P_scope Δ_alt Δ_fv_pair_alt Θ
      (by simpa [B.fv] using related_alt) wf_alt respectsB_pair
      respectsP_sup P_specs_true (F_alt.pair G_alt)
      (ZFSet.pair_mem_prod.mpr ⟨hF_alt, hG_alt⟩) den_pair_alt
      hcovP_target denP_target hdenP_target rfl
    have P_target_rel' : RDomCastSupported
        (⟨F_alt.pair G_alt, BType.set τ ×ᴮ BType.set τ,
          ZFSet.pair_mem_prod.mpr ⟨hF_alt, hG_alt⟩⟩ : B.Dom)
        denP_target := by
      simpa only [proof_irrel_heq] using P_target_rel
    obtain ⟨F_target_rel, G_target_rel⟩ :=
      RDomCastSupported.of_pair
        (hX := hF_alt) (hY := hG_alt)
        (hX' := hF_target_mem) (hY' := hG_target_mem)
        P_target_rel'
    have respectsS_Stu : SMT.RenamingContext.RespectsTypeContextOnFV
        Θ Stu.types Senc :=
      respectsS_Core.of_extends (RenamingContext.extends_refl Θ)
        UCore_sub_Stu typS_Core
    have respectsT_Stu : SMT.RenamingContext.RespectsTypeContextOnFV
        Θ Stu.types Tenc :=
      respectsT_Core.of_extends (RenamingContext.extends_refl Θ)
        UCore_sub_Stu typT_Core
    have dependency_mem_Core :
        ∀ {v}, v ∈ (SMT.fv Senc ∪ SMT.fv Tenc) ∪
          declVars DltU → v ∈ UCore := by
      intro v hv
      rw [List.mem_union_iff, List.mem_union_iff] at hv
      rcases hv with (hvS | hvT) | hvdecl
      · exact SMT.Typing.mem_context_of_mem_fv typS_Core hvS
      · exact SMT.Typing.mem_context_of_mem_fv typT_Core hvT
      · apply U_clean_trace.declVar_mem
        rw [declVars_append, List.mem_append]
        exact Or.inr hvdecl
    have typU_Core : UCore ⊢ˢ Uenc : σU :=
      SMT.Typing.strengthening_of_fv_subset UCore_sub_Stu typU
        (fun v hv => dependency_mem_Core (U_fv_dep hv))
    have respectsU_Core : SMT.RenamingContext.RespectsTypeContextOnFV
        Θ UCore Uenc := respectsSMT.of_super UCore_sub_sup
    have respectsU_Stu : SMT.RenamingContext.RespectsTypeContextOnFV
        Θ Stu.types Uenc :=
      respectsU_Core.of_extends (RenamingContext.extends_refl Θ)
        UCore_sub_Stu typU_Core
    have U_specs_Stu : SpecBodiesTrue Θ Stu.types DltU := by
      intro body hbody
      obtain ⟨hcovBody, denBody, respectsBodySup, hdenBody,
          hdenBodyType, hdenBodyTrue⟩ := U_specs_true body hbody
      have typBodyCore : UCore ⊢ˢ body : SMTType.bool :=
        SMT.Typing.strengthening_of_fv_subset UCore_sub_Stu
          (U_specs_op body hbody)
          (fun v hv => dependency_mem_Core
            (U_specs_fv_dep body hbody hv))
      have respectsBodyCore :
          SMT.RenamingContext.RespectsTypeContextOnFV Θ UCore body :=
        respectsBodySup.of_super UCore_sub_sup
      have respectsBodyStu :
          SMT.RenamingContext.RespectsTypeContextOnFV Θ Stu.types body :=
        respectsBodyCore.of_extends (RenamingContext.extends_refl Θ)
          UCore_sub_Stu typBodyCore
      exact ⟨hcovBody, denBody, respectsBodyStu, hdenBody,
        hdenBodyType, hdenBodyTrue⟩
    have denS_target_eta :
        (⟨denS_target.fst, σS, hF_target_mem⟩ :
            SMT.Dom) = denS_target := by
      rcases denS_target with ⟨Ftarget, σtarget, hFtarget⟩
      dsimp at hdenS_target_type ⊢
      subst σtarget
      rfl
    have denT_target_eta :
        (⟨denT_target.fst, σT, hG_target_mem⟩ :
            SMT.Dom) = denT_target := by
      rcases denT_target with ⟨Gtarget, σtarget, hGtarget⟩
      dsimp at hdenT_target_type ⊢
      subst σtarget
      rfl
    have F_target_rel_exact : RDomCastSupported
        (⟨F_alt, BType.set τ, hF_alt⟩ : B.Dom) denS_target := by
      rw [← denS_target_eta]
      simpa only [proof_irrel_heq] using F_target_rel
    have G_target_rel_exact : RDomCastSupported
        (⟨G_alt, BType.set τ, hG_alt⟩ : B.Dom) denT_target := by
      rw [← denT_target_eta]
      simpa only [proof_irrel_heq] using G_target_rel
    obtain ⟨_goodU, guardU⟩ := U_sem
    have result_rel := guardU Stu.types U_trace.scoped_extends Θ
      hcovS_target hcovT_target respectsS_Stu respectsT_Stu
      F_alt G_alt hF_alt hG_alt denS_target denT_target
      hdenS_target hdenT_target hdenS_target_type hdenT_target_type
      F_target_rel_exact G_target_rel_exact hcovU denU respectsU_Stu U_specs_Stu
      hdenU hdenU_type
    simpa only [proof_irrel_heq] using result_rel
  · intro body hbody
    rw [specBodies_append, List.mem_append] at hbody
    rcases hbody with hPbody | hUbody
    · exact typing_weakening_generated types_sub_U U_ctx
        U_decl_fresh (P_specs_op body hPbody)
        (fun v hv => P_delta_ok.2 body hPbody v hv)
    · exact U_specs_op body hUbody
  · simpa [List.append_assoc] using U_sc_typing_clean

end EncodeTermRepresentedScopedInter
