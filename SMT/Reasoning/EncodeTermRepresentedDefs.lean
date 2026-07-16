import SMT.Reasoning.Representation

open Std.Do B SMT ZFSet

/-!
# Common specification for representation-aware `encodeTerm` proofs

The specification retains the operational invariants of `encodeTerm_spec`,
but relates source and target valuations directly through `RDomCast`.  The
initial SMT valuation is therefore allowed to use a noncanonical type such as
`α → Option β` for a B relation of type `ℙ (α × β)`.
-/

/-- Constructor-specific successful-result shape information used when one
encoder branch is factored through another branch with the same recursive
prefix.  Only shapes needed by such transfers are recorded. -/
def EncodeTermResultShape : B.Term → SMT.Term → SMTType → Prop
  | .maplet _ _, t', σ => ∃ x' y' σx σy,
      t' = SMT.Term.pair x' y' ∧ σ = SMTType.pair σx σy
  | .ℤ, t', _ => SMT.fv t' = []
  | .𝔹, t', _ => SMT.fv t' = []
  | _, _, _ => True

/-- Totality under an alternative source valuation and a representation-aware
SMT valuation. Domain containment is explicit; it replaces the unsound legacy
rule that attempted to derive containment from one-sided extension. -/
abbrev EncodeTermRepTotal.{u}
    (t : B.Term) (E : B.Env) (α : BType) (Λ : SMT.TypeContext)
    (t' : SMT.Term) (σ : SMTType)
    (Γ' : SMT.TypeContext) (used' : List SMT.𝒱) : Prop :=
  ∀ (Δ_alt : B.RenamingContext.Context)
    (Δ_fv_alt : ∀ v ∈ B.fv t, (Δ_alt v).isSome = true)
    (Δ₀_alt : SMT.RenamingContext.Context.{u}),
    RValuationCastSupportedOnFV Δ_alt Δ₀_alt t →
    B.RenWF E.context Δ_alt →
    (∀ v ∉ used', Δ₀_alt v = none) →
    B.RenamingContext.RespectsTypeContextOnFV Δ₀_alt Λ t →
    (∀ v, Δ₀_alt v ≠ none → v ∈ Λ) →
    ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦α⟧ᶻ),
      ⟦t.abstract Δ_alt Δ_fv_alt⟧ᴮ =
        some ⟨T_alt, ⟨α, hT_alt⟩⟩ →
      ∃ (Δ'_alt : SMT.RenamingContext.Context.{u})
        (hcov_alt : RenamingContext.CoversFV Δ'_alt t')
        (denT_alt : SMT.Dom.{u}),
        RenamingContext.Extends Δ'_alt Δ₀_alt ∧
        RValuationCastSupportedOnFV Δ_alt Δ'_alt t ∧
        (∀ v ∉ used', Δ'_alt v = none) ∧
        B.RenamingContext.RespectsTypeContextOnFV Δ'_alt Γ' t ∧
        SMT.RenamingContext.RespectsTypeContextOnFV Δ'_alt Γ' t' ∧
        (∀ v, Δ'_alt v ≠ none → v ∈ Γ') ∧
        ⟦t'.abstract Δ'_alt hcov_alt⟧ˢ = some denT_alt ∧
        denT_alt.snd.fst = σ ∧
        RDomCastSupported (⟨T_alt, α, hT_alt⟩ : B.Dom) denT_alt

/-! ## Generated-helper contracts

The `all` encoder moves declarations produced while encoding its body under
the quantifier.  Its universally quantified helpers are guarded by the
corresponding `define_fun unit bool` specification bodies.  Ordinary
existential totality is not enough at that boundary: soundness also needs
correctness for every typed helper assignment satisfying those guards, and a
proof that one such assignment exists. -/

/-- Every generated Boolean helper specification is covered, well typed under
the supplied valuation, and evaluates to true. -/
abbrev SpecBodiesTrue.{u}
    (Θ : SMT.RenamingContext.Context.{u}) (Γ : SMT.TypeContext)
    (Dlt : SMT.Chunk) : Prop :=
  ∀ b ∈ specBodies Dlt,
    ∃ (hcov : SMT.RenamingContext.CoversFV Θ b)
      (db : SMT.Dom.{u}),
      SMT.RenamingContext.RespectsTypeContextOnFV Θ Γ b ∧
      ⟦b.abstract Θ hcov⟧ˢ = some db ∧
      db.snd.fst = SMTType.bool ∧
      db.fst = ZFSet.zftrue

theorem SpecBodiesTrue.append.{u}
    {Θ : SMT.RenamingContext.Context.{u}} {Γ : SMT.TypeContext}
    {D₁ D₂ : SMT.Chunk}
    (h₁ : SpecBodiesTrue Θ Γ D₁)
    (h₂ : SpecBodiesTrue Θ Γ D₂) :
    SpecBodiesTrue Θ Γ (D₁ ++ D₂) := by
  intro b hb
  rw [specBodies_append, List.mem_append] at hb
  exact hb.elim (h₁ b) (h₂ b)

theorem SpecBodiesTrue.left_of_append.{u}
    {Θ : SMT.RenamingContext.Context.{u}} {Γ : SMT.TypeContext}
    {D₁ D₂ : SMT.Chunk}
    (h : SpecBodiesTrue Θ Γ (D₁ ++ D₂)) :
    SpecBodiesTrue Θ Γ D₁ := by
  intro b hb
  exact h b (by rw [specBodies_append, List.mem_append]; exact Or.inl hb)

theorem SpecBodiesTrue.right_of_append.{u}
    {Θ : SMT.RenamingContext.Context.{u}} {Γ : SMT.TypeContext}
    {D₁ D₂ : SMT.Chunk}
    (h : SpecBodiesTrue Θ Γ (D₁ ++ D₂)) :
    SpecBodiesTrue Θ Γ D₂ := by
  intro b hb
  exact h b (by rw [specBodies_append, List.mem_append]; exact Or.inr hb)

theorem SpecBodiesTrue.of_extends.{u}
    {Θ Θ' : SMT.RenamingContext.Context.{u}}
    {Γ Γ' : SMT.TypeContext} {Dlt : SMT.Chunk}
    (h : SpecBodiesTrue Θ Γ Dlt)
    (hΘ : SMT.RenamingContext.Extends Θ' Θ)
    (hΓ : Γ ⊆ Γ')
    (hdom : ∀ v, Θ v ≠ none → v ∈ Γ) :
    SpecBodiesTrue Θ' Γ' Dlt := by
  intro b hb
  obtain ⟨hcov, db, hresp, hden, htype, htrue⟩ := h b hb
  have hcov' : SMT.RenamingContext.CoversFV Θ' b :=
    SMT.RenamingContext.coversFV_of_extends_of_coversFV hΘ hcov
  have hagree : SMT.RenamingContext.AgreesOnFV Θ' Θ b :=
    SMT.RenamingContext.agreesOnFV_of_extends_of_coversFV hΘ hcov
  have hden' := SMT.RenamingContext.denote_congr_of_agreesOnFV
    (t := b) (h1 := hcov') (h2 := hcov) hagree
  refine ⟨hcov', db, ?_, hden'.trans hden, htype, htrue⟩
  intro v τ hv hlookup'
  have hvΓ : v ∈ Γ := hdom v (by
    have := hcov v hv
    simpa [Option.isSome_iff_ne_none] using this)
  obtain ⟨τ₀, hlookup⟩ := Option.isSome_iff_exists.mp
    (AList.lookup_isSome.mpr hvΓ)
  have hlookup₀' : Γ'.lookup v = some τ₀ :=
    AList.lookup_of_subset hΓ hlookup
  rw [hlookup₀'] at hlookup'
  cases hlookup'
  obtain ⟨d, hd, hdtype⟩ := hresp hv hlookup
  exact ⟨d, hΘ hd, hdtype⟩

/-- Alternative-valuation totality strengthened with a satisfying assignment
for every helper specification generated by this encoder run. -/
abbrev EncodeTermRepScopedTotal.{u}
    (t : B.Term) (E : B.Env) (α : BType)
    (Λ : SMT.TypeContext) (t' : SMT.Term) (σ : SMTType)
    (Γ' : SMT.TypeContext) (used' : List SMT.𝒱)
    (Dlt : SMT.Chunk) : Prop :=
  ∀ (Δ_alt : B.RenamingContext.Context)
    (Δ_fv_alt : ∀ v ∈ B.fv t, (Δ_alt v).isSome = true)
    (Δ₀_alt : SMT.RenamingContext.Context.{u}),
    RValuationCastSupportedOnFV Δ_alt Δ₀_alt t →
    B.RenWF E.context Δ_alt →
    (∀ v ∉ used', Δ₀_alt v = none) →
    B.RenamingContext.RespectsTypeContextOnFV Δ₀_alt Λ t →
    (∀ v, Δ₀_alt v ≠ none → v ∈ Λ) →
    ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦α⟧ᶻ),
      ⟦t.abstract Δ_alt Δ_fv_alt⟧ᴮ =
        some ⟨T_alt, ⟨α, hT_alt⟩⟩ →
      ∃ (Δ'_alt : SMT.RenamingContext.Context.{u})
        (hcov_alt : RenamingContext.CoversFV Δ'_alt t')
        (denT_alt : SMT.Dom.{u}),
        RenamingContext.Extends Δ'_alt Δ₀_alt ∧
        RValuationCastSupportedOnFV Δ_alt Δ'_alt t ∧
        (∀ v ∉ used', Δ'_alt v = none) ∧
        B.RenamingContext.RespectsTypeContextOnFV Δ'_alt Γ' t ∧
        SMT.RenamingContext.RespectsTypeContextOnFV Δ'_alt Γ' t' ∧
        (∀ v, Δ'_alt v ≠ none → v ∈ Γ') ∧
        SpecBodiesTrue Δ'_alt Γ' Dlt ∧
        ⟦t'.abstract Δ'_alt hcov_alt⟧ˢ = some denT_alt ∧
        denT_alt.snd.fst = σ ∧
        RDomCastSupported (⟨T_alt, α, hT_alt⟩ : B.Dom) denT_alt

/-- Guarded partial correctness under an arbitrary assignment to generated
helpers.  When all generated specifications hold, any target denotation is the
supported representation of the corresponding source denotation. -/
abbrev EncodeTermRepGuardedSound.{u}
    (t : B.Term) (E : B.Env) (α : BType)
    (t' : SMT.Term) (σ : SMTType) (Γ' : SMT.TypeContext)
    (Dlt : SMT.Chunk) : Prop :=
  ∀ (Γ_sup : SMT.TypeContext), Γ' ⊆ Γ_sup →
    ∀ (Δ_alt : B.RenamingContext.Context)
    (Δ_fv_alt : ∀ v ∈ B.fv t, (Δ_alt v).isSome = true)
    (Θ : SMT.RenamingContext.Context.{u}),
    RValuationCastSupportedOnFV Δ_alt Θ t →
    B.RenWF E.context Δ_alt →
    B.RenamingContext.RespectsTypeContextOnFV Θ Γ_sup t →
    SMT.RenamingContext.RespectsTypeContextOnFV Θ Γ_sup t' →
    SpecBodiesTrue Θ Γ_sup Dlt →
    ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦α⟧ᶻ),
      ⟦t.abstract Δ_alt Δ_fv_alt⟧ᴮ =
        some ⟨T_alt, ⟨α, hT_alt⟩⟩ →
      ∀ (hcov : SMT.RenamingContext.CoversFV Θ t')
        (denT : SMT.Dom.{u}),
        ⟦t'.abstract Θ hcov⟧ˢ = some denT →
        denT.snd.fst = σ →
        RDomCastSupported (⟨T_alt, α, hT_alt⟩ : B.Dom) denT

/-- Declaration-aware postcondition used only where generated helpers are
re-scoped by a binder.  It is kept separate from `EncodeTermRepPost` so the
ordinary constructor proof remains lightweight. -/
abbrev EncodeTermRepScopedPost.{u}
    (t : B.Term) (E : B.Env) (α : BType) (Λ : SMT.TypeContext)
    (decl : SMT.Chunk) (t' : SMT.Term) (σ : SMTType)
    (E' : SMT.Env) (Γ' : SMT.TypeContext) : Prop :=
  ∃ Dlt : SMT.Chunk,
    E'.declarations = decl ++ Dlt ∧
    EncodeTermRepScopedTotal.{u} t E α Λ t' σ Γ' E'.usedVars Dlt ∧
    EncodeTermRepGuardedSound.{u} t E α t' σ Γ' Dlt

/-- Representation-aware postcondition for one successful `encodeTerm` run. -/
abbrev EncodeTermRepPost.{u}
    (t : B.Term) (α : BType) (Λ : SMT.TypeContext)
    («Δ» : B.RenamingContext.Context)
    (Δ₀ : SMT.RenamingContext.Context.{u})
    (used : List SMT.𝒱) (T : ZFSet.{u}) (hT : T ∈ ⟦α⟧ᶻ)
    (E : B.Env) (t' : SMT.Term) (σ : SMTType)
    (E' : SMT.Env) (Γ' : SMT.TypeContext) : Prop :=
  used ⊆ E'.usedVars ∧
  Λ ⊆ Γ' ∧
  Γ'.keys ⊆ E'.usedVars ∧
  B.CoversUsedVars E'.usedVars t ∧
  Nonempty (σ ~> α.toSMTType) ∧
  (Γ' ⊢ˢ t' : σ) ∧
  EncodeTermResultShape t t' σ ∧
  (∀ v ∈ used, v ∉ Λ → v ∉ B.Term.vars t → v ∉ Γ') ∧
  ∃ (Δ' : SMT.RenamingContext.Context.{u})
    (Δ'_covers : RenamingContext.CoversFV Δ' t'),
    RenamingContext.Extends Δ' Δ₀ ∧
    RValuationCastSupportedOnFV «Δ» Δ' t ∧
    (∀ v ∉ E'.usedVars, Δ' v = none) ∧
    B.RenamingContext.RespectsTypeContextOnFV Δ' Γ' t ∧
    SMT.RenamingContext.RespectsTypeContextOnFV Δ' Γ' t' ∧
    (∀ v, Δ' v ≠ none → v ∈ Γ') ∧
    ∃ denT' : SMT.Dom.{u},
      ⟦t'.abstract Δ' Δ'_covers⟧ˢ = some denT' ∧
      denT'.snd.fst = σ ∧
      RDomCastSupported (⟨T, α, hT⟩ : B.Dom) denT' ∧
      EncodeTermRepTotal.{u} t E α Λ t' σ Γ' E'.usedVars

/-- Induction-hypothesis shape shared by the representation-aware constructor
proofs. -/
abbrev EncodeTermRepIH.{u} (t : B.Term) : Prop :=
  ∀ (E : B.Env) {Λ : SMT.TypeContext} {α : BType},
    E.context ⊢ᴮ t : α →
    ∀ {«Δ» : B.RenamingContext.Context},
      (Δ_fv : ∀ v ∈ B.fv t, («Δ» v).isSome = true) →
    ∀ {Δ₀ : SMT.RenamingContext.Context.{u}},
      RValuationCastSupportedOnFV «Δ» Δ₀ t →
    ∀ {used : List SMT.𝒱},
      (∀ v ∉ used, Δ₀ v = none) →
      (∀ v, Δ₀ v ≠ none → v ∈ Λ) →
    ∀ {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ},
      ⟦t.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩ →
      (∀ v ∈ t.vars, v ∈ used) →
      (∀ v ∈ t.vars, v ∈ Λ → v ∈ E.context) →
      (B.bv t).Nodup →
      B.RenamingContext.RespectsTypeContextOnFV Δ₀ Λ t →
      (∀ v ∈ B.fv t, v ∈ Λ) →
      B.RenWF E.context «Δ» →
    ∀ {n : ℕ},
      (⦃fun ⟨E0, Λ'⟩ ↦
        ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧
          Λ.keys ⊆ E0.usedVars ∧ E0.usedVars = used⌝ ⦄
      encodeTerm t E
      ⦃ ⇓? (⟨t', σ⟩ : SMT.Term × SMTType) ⟨E', Γ'⟩ =>
        ⌜EncodeTermRepPost t α Λ «Δ» Δ₀ used T hT
          E t' σ E' Γ'⌝ ⦄)

/-- Declaration-aware companion induction hypothesis.  Constructor proofs use
this contract only when a parent binder re-scopes the declarations generated
by the recursive call. -/
abbrev EncodeTermRepScopedIH.{u} (t : B.Term) : Prop :=
  ∀ (E : B.Env) {Λ : SMT.TypeContext} {α : BType},
    E.context ⊢ᴮ t : α →
    ∀ {«Δ» : B.RenamingContext.Context},
      (Δ_fv : ∀ v ∈ B.fv t, («Δ» v).isSome = true) →
    ∀ {Δ₀ : SMT.RenamingContext.Context.{u}},
      RValuationCastSupportedOnFV «Δ» Δ₀ t →
    ∀ {used : List SMT.𝒱},
      (∀ v ∉ used, Δ₀ v = none) →
      (∀ v, Δ₀ v ≠ none → v ∈ Λ) →
    ∀ {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ},
      ⟦t.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩ →
      (∀ v ∈ t.vars, v ∈ used) →
      (∀ v ∈ t.vars, v ∈ Λ → v ∈ E.context) →
      (B.bv t).Nodup →
      B.RenamingContext.RespectsTypeContextOnFV Δ₀ Λ t →
      (∀ v ∈ B.fv t, v ∈ Λ) →
      B.RenWF E.context «Δ» →
    ∀ {n : ℕ} {decl : SMT.Chunk},
      (⦃fun ⟨E0, Λ'⟩ ↦
        ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧
          Λ.keys ⊆ E0.usedVars ∧ E0.usedVars = used ∧
          E0.declarations = decl⌝ ⦄
      encodeTerm t E
      ⦃ ⇓? (⟨t', σ⟩ : SMT.Term × SMTType) ⟨E', Γ'⟩ =>
        ⌜EncodeTermRepScopedPost.{u} t E α Λ decl
          t' σ E' Γ'⌝ ⦄)

/-- Declaration-aware induction hypothesis needed by `all`.  Its re-scoped
body is always Boolean, so constructors that cannot synthesize a Boolean need
no companion theorem. -/
abbrev EncodeTermRepScopedBoolIH.{u} (t : B.Term) : Prop :=
  ∀ (E : B.Env) {Λ : SMT.TypeContext},
    E.context ⊢ᴮ t : BType.bool →
    ∀ {«Δ» : B.RenamingContext.Context},
      (Δ_fv : ∀ v ∈ B.fv t, («Δ» v).isSome = true) →
    ∀ {Δ₀ : SMT.RenamingContext.Context.{u}},
      RValuationCastSupportedOnFV «Δ» Δ₀ t →
    ∀ {used : List SMT.𝒱},
      (∀ v ∉ used, Δ₀ v = none) →
      (∀ v, Δ₀ v ≠ none → v ∈ Λ) →
    ∀ {T : ZFSet.{u}} {hT : T ∈ ⟦BType.bool⟧ᶻ},
      ⟦t.abstract «Δ» Δ_fv⟧ᴮ =
        some ⟨T, ⟨BType.bool, hT⟩⟩ →
      (∀ v ∈ t.vars, v ∈ used) →
      (∀ v ∈ t.vars, v ∈ Λ → v ∈ E.context) →
      (B.bv t).Nodup →
      B.RenamingContext.RespectsTypeContextOnFV Δ₀ Λ t →
      (∀ v ∈ B.fv t, v ∈ Λ) →
      B.RenWF E.context «Δ» →
    ∀ {n : ℕ} {decl : SMT.Chunk},
      (⦃fun ⟨E0, Λ'⟩ ↦
        ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧
          Λ.keys ⊆ E0.usedVars ∧ E0.usedVars = used ∧
          E0.declarations = decl⌝ ⦄
      encodeTerm t E
      ⦃ ⇓? (⟨t', σ⟩ : SMT.Term × SMTType) ⟨E', Γ'⟩ =>
        ⌜EncodeTermRepScopedPost.{u} t E BType.bool Λ decl
          t' σ E' Γ'⌝ ⦄)

/-- Semantic side condition for the representation change performed on
flagged variables bound by `all`. B typing records a flagged function as a
set of pairs, so it does not by itself exclude nonfunctional relations from
the quantified domain. The oracle states exactly the missing fact: for every
successful flag-type selection made by the encoder, each source-domain value
has an SMT preimage at the selected binder type.

The proof-obligation layer discharges this condition from the functional
hypotheses that justify entries in `E.flags`; the raw term theorem keeps it
explicit. -/
abbrev EncodeTermAllBinderAdmissible.{u} : Prop :=
  ∀ (E : B.Env) (vs : List B.𝒱) (D P : B.Term) (τ : BType),
    E.context ⊢ᴮ B.Term.all vs D P : BType.bool →
    E.context ⊢ᴮ D : BType.set τ →
    ∀ («Δ» : B.RenamingContext.Context.{u})
      (Δ_fv_D : ∀ v ∈ B.fv D, («Δ» v).isSome = true)
      (𝒟 : ZFSet.{u}) (h𝒟 : 𝒟 ∈ ⟦BType.set τ⟧ᶻ),
      ⟦D.abstract «Δ» Δ_fv_D⟧ᴮ = some ⟨𝒟, ⟨BType.set τ, h𝒟⟩⟩ →
      ∀ (τs : List SMTType)
        (hvs_len : vs.length =
          (τ.toSMTType.fromProdl (vs.length - 1)).length)
        (hτs_len : τs.length =
          (τ.toSMTType.fromProdl (vs.length - 1)).length),
        (∀ i (hi : i < τs.length),
          SMTFlagTypeRel (vs[i]'(by omega) ∈ E.flags)
            ((τ.toSMTType.fromProdl (vs.length - 1))[i]'(hτs_len ▸ hi))
            (τs[i]'hi)) →
        ∀ (hcast : τs.toProdl ⊑ τ.toSMTType),
          BinderCastAdmissible τ τs.toProdl hcast.toCastPath 𝒟

/-- Recover a cast path indexed by an externally known target type tag. -/
theorem RDomCast.nonempty_path_of_type_eq.{u}
    {X Y : ZFSet.{u}} {α : BType} {σ τ : SMTType}
    {hX : X ∈ ⟦α⟧ᶻ} {hY : Y ∈ ⟦σ⟧ᶻ}
    (hrel : RDomCast (⟨X, α, hX⟩ : B.Dom)
      (⟨Y, σ, hY⟩ : SMT.Dom))
    (hσ : σ = τ) : Nonempty (τ ~> α.toSMTType) := by
  subst τ
  obtain ⟨c, _⟩ := hrel
  exact ⟨c⟩

theorem RDomCastAdmissible.nonempty_path_of_type_eq.{u}
    {X Y : ZFSet.{u}} {α : BType} {σ τ : SMTType}
    {hX : X ∈ ⟦α⟧ᶻ} {hY : Y ∈ ⟦σ⟧ᶻ}
    (hrel : RDomCastAdmissible (⟨X, α, hX⟩ : B.Dom)
      (⟨Y, σ, hY⟩ : SMT.Dom))
    (hσ : σ = τ) : Nonempty (τ ~> α.toSMTType) :=
  RDomCast.nonempty_path_of_type_eq hrel.toRDomCast hσ
