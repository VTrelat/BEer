import SMT.Reasoning.Representation

open Std.Do B SMT ZFSet

/-!
# Common specification for representation-aware `encodeTerm` proofs

The specification retains the operational invariants of `encodeTerm_spec`,
but relates source and target valuations directly through `RDomCast`.  The
initial SMT valuation is therefore allowed to use a noncanonical type such as
`α → Option β` for a B relation of type `ℙ (α × β)`.
-/

/-- An append-only declaration delta with unchanged length is empty.  Binder
encoders use this after `ensureDeclarationsUnchanged` to rule out a body
introducing global helper names. -/
theorem declaration_delta_eq_nil_of_length
    {decl delta out : SMT.Chunk}
    (happend : out = decl ++ delta)
    (hlen : out.length = decl.length) :
    delta = [] := by
  rw [happend, List.length_append] at hlen
  have hlen' : decl.length + delta.length = decl.length + 0 := by
    simpa using hlen
  exact List.length_eq_zero_iff.mp (Nat.add_left_cancel hlen')

/-- If an encoding run has appended no declarations, its structural
free-variable bound contains no generated helper names. -/
theorem encoded_fv_subset_source_of_declaration_stability
    {decl delta out : SMT.Chunk} {t : B.Term} {t' : SMT.Term}
    (happend : out = decl ++ delta)
    (hlen : out.length = decl.length)
    (hfv : SMT.fv t' ⊆ B.Term.vars t ∪ declVars delta) :
    SMT.fv t' ⊆ B.Term.vars t := by
  have hdelta : delta = [] :=
    declaration_delta_eq_nil_of_length happend hlen
  subst delta
  intro v hv
  simpa [declVars] using hfv hv

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

/-- The typed entries introduced by `declare_const` instructions in a
declaration delta.  Unlike `declVars`, this retains the declared SMT type; that
extra information is essential when the declarations are turned into local
quantifier binders. -/
def declEntries (Dlt : SMT.Chunk) :
    List (Sigma fun _ : SMT.𝒱 => SMTType) :=
  Dlt.filterMap fun
    | .declare_const v τ => some ⟨v, τ⟩
    | _ => none

/-- Pair-valued view of the declarations that become unary local binders in
the `all` encoder.  This is definitionally the encoder's `ex_binders`
filter-map. -/
def declBinders (Dlt : SMT.Chunk) : List (SMT.𝒱 × SMTType) :=
  Dlt.filterMap fun
    | .declare_const v τ => some (v, τ)
    | _ => none

theorem mem_declVars_of_mem_declBinders
    {Dlt : SMT.Chunk} {v : SMT.𝒱} {tau : SMTType}
    (h : (v, tau) ∈ declBinders Dlt) : v ∈ declVars Dlt := by
  induction Dlt with
  | nil => simp [declBinders] at h
  | cons i D ih =>
      cases i with
      | declare_const w sigma =>
          simp only [declBinders, List.filterMap_cons, List.mem_cons] at h
          simp only [declVars, List.filterMap_cons, List.mem_cons]
          rcases h with h | h
          · cases h
            exact .inl rfl
          · exact .inr (ih h)
      | define_fun w sigma rho t =>
          simpa [declVars] using ih (by simpa [declBinders] using h)
      | define_const w sigma t =>
          simpa [declVars] using ih (by simpa [declBinders] using h)
      | assert t => simpa [declVars] using ih (by simpa [declBinders] using h)
      | push n => simpa [declVars] using ih (by simpa [declBinders] using h)
      | pop n => simpa [declVars] using ih (by simpa [declBinders] using h)
      | check_sat => simpa [declVars] using ih (by simpa [declBinders] using h)

theorem mem_declEntries_of_mem_declBinders
    {Dlt : SMT.Chunk} {v : SMT.𝒱} {tau : SMTType}
    (h : (v, tau) ∈ declBinders Dlt) :
    (⟨v, tau⟩ : Sigma fun _ : SMT.𝒱 => SMTType) ∈ declEntries Dlt := by
  induction Dlt with
  | nil => simp [declBinders] at h
  | cons i D ih =>
      cases i with
      | declare_const w sigma =>
          simp only [declBinders, declEntries, List.filterMap_cons,
            List.mem_cons] at h ⊢
          exact h.elim (fun heq => Or.inl (by cases heq; rfl))
            (Or.inr ∘ ih)
      | define_fun w sigma rho t =>
          simpa [declEntries] using ih (by simpa [declBinders] using h)
      | define_const w sigma t =>
          simpa [declEntries] using ih (by simpa [declBinders] using h)
      | assert t =>
          simpa [declEntries] using ih (by simpa [declBinders] using h)
      | push n =>
          simpa [declEntries] using ih (by simpa [declBinders] using h)
      | pop n =>
          simpa [declEntries] using ih (by simpa [declBinders] using h)
      | check_sat =>
          simpa [declEntries] using ih (by simpa [declBinders] using h)

@[simp] theorem declBinders_map_fst (Dlt : SMT.Chunk) :
    (declBinders Dlt).map Prod.fst = declVars Dlt := by
  induction Dlt with
  | nil => rfl
  | cons i D ih =>
      cases i <;>
        simp only [declBinders, declVars, List.filterMap_cons,
          List.map_cons] <;>
        simpa [declBinders, declVars] using ih

@[simp] theorem declBinders_nil : declBinders [] = [] := rfl

@[simp] theorem declBinders_append (D₁ D₂ : SMT.Chunk) :
    declBinders (D₁ ++ D₂) = declBinders D₁ ++ declBinders D₂ := by
  simp [declBinders, List.filterMap_append]

@[simp] theorem declBinders_helperSpecChunk
    (v : SMT.𝒱) (τ : SMTType) (spec : SMT.Term) :
    declBinders (helperSpecChunk v τ spec) = [(v, τ)] := rfl

@[simp] theorem declEntries_nil : declEntries [] = [] := rfl

@[simp] theorem declEntries_append (D₁ D₂ : SMT.Chunk) :
    declEntries (D₁ ++ D₂) = declEntries D₁ ++ declEntries D₂ := by
  simp [declEntries, List.filterMap_append]

@[simp] theorem declEntries_helperSpecChunk
    (v : SMT.𝒱) (τ : SMTType) (spec : SMT.Term) :
    declEntries (helperSpecChunk v τ spec) = [⟨v, τ⟩] := rfl

theorem mem_declVars_of_mem_declEntries
    {Dlt : SMT.Chunk} {v : SMT.𝒱} {τ : SMTType}
    (h : (⟨v, τ⟩ : Sigma fun _ : SMT.𝒱 => SMTType) ∈ declEntries Dlt) :
    v ∈ declVars Dlt := by
  induction Dlt with
  | nil => simp [declEntries] at h
  | cons i D ih =>
      cases i with
      | declare_const w σ =>
          simp only [declEntries, List.filterMap_cons, List.mem_cons] at h
          simp only [declVars, List.filterMap_cons, List.mem_cons]
          rcases h with h | h
          · cases h
            exact Or.inl rfl
          · exact Or.inr (ih h)
      | define_fun w σ ρ t =>
          simpa [declVars] using ih (by simpa [declEntries] using h)
      | define_const w σ t =>
          simpa [declVars] using ih (by simpa [declEntries] using h)
      | assert t =>
          simpa [declVars] using ih (by simpa [declEntries] using h)
      | push n =>
          simpa [declVars] using ih (by simpa [declEntries] using h)
      | pop n =>
          simpa [declVars] using ih (by simpa [declEntries] using h)
      | check_sat =>
          simpa [declVars] using ih (by simpa [declEntries] using h)

theorem exists_mem_declEntries_of_mem_declVars
    {Dlt : SMT.Chunk} {v : SMT.𝒱} (h : v ∈ declVars Dlt) :
    ∃ τ : SMTType,
      (⟨v, τ⟩ : Sigma fun _ : SMT.𝒱 => SMTType) ∈ declEntries Dlt := by
  induction Dlt with
  | nil => simp [declVars] at h
  | cons i D ih =>
      cases i with
      | declare_const w σ =>
          simp only [declVars, List.filterMap_cons, List.mem_cons] at h
          rcases h with rfl | htail
          · exact ⟨σ, by simp [declEntries]⟩
          · obtain ⟨τ, hτ⟩ := ih htail
            refine ⟨τ, ?_⟩
            simp only [declEntries, List.filterMap_cons, List.mem_cons]
            exact Or.inr hτ
      | define_fun w σ ρ t =>
          obtain ⟨τ, hτ⟩ := ih (by simpa [declVars] using h)
          exact ⟨τ, by simpa [declEntries] using hτ⟩
      | define_const w σ t =>
          obtain ⟨τ, hτ⟩ := ih (by simpa [declVars] using h)
          exact ⟨τ, by simpa [declEntries] using hτ⟩
      | assert t =>
          obtain ⟨τ, hτ⟩ := ih (by simpa [declVars] using h)
          exact ⟨τ, by simpa [declEntries] using hτ⟩
      | push n =>
          obtain ⟨τ, hτ⟩ := ih (by simpa [declVars] using h)
          exact ⟨τ, by simpa [declEntries] using hτ⟩
      | pop n =>
          obtain ⟨τ, hτ⟩ := ih (by simpa [declVars] using h)
          exact ⟨τ, by simpa [declEntries] using hτ⟩
      | check_sat =>
          obtain ⟨τ, hτ⟩ := ih (by simpa [declVars] using h)
          exact ⟨τ, by simpa [declEntries] using hτ⟩

/-- Every entry in the operational result context is either an entry of the
input context or the typed declaration of a generated helper. -/
abbrev ContextGeneratedByDeclarations
    (Λ Γ : SMT.TypeContext) (Dlt : SMT.Chunk) : Prop :=
  Γ.entries ⊆ Λ.entries ++ declEntries Dlt

theorem ContextGeneratedByDeclarations.mem_classify
    {Lambda Gamma : SMT.TypeContext} {Dlt : SMT.Chunk}
    (h : ContextGeneratedByDeclarations Lambda Gamma Dlt)
    {v : SMT.𝒱} (hv : v ∈ Gamma) :
    v ∈ Lambda ∨ v ∈ declVars Dlt := by
  obtain ⟨tau, hlookup⟩ := Option.isSome_iff_exists.mp
    (AList.lookup_isSome.mpr hv)
  have hentry : (⟨v, tau⟩ : Sigma fun _ : SMT.𝒱 => SMTType) ∈
      Gamma.entries := AList.mem_lookup_iff.mp hlookup
  rcases List.mem_append.mp (h hentry) with hbase | hdecl
  · exact .inl <| AList.mem_keys.mpr <|
      List.mem_map.mpr ⟨⟨v, tau⟩, hbase, rfl⟩
  · exact .inr (mem_declVars_of_mem_declEntries hdecl)

/-- Exact context evolution induced by the declaration delta.  A
`declare_const` inserts one genuinely fresh typed name; every other
instruction leaves the type context unchanged.  Unlike the footprint-only
`ContextGeneratedByDeclarations`, this trace retains the freshness and order
needed when declarations are converted into nested local binders. -/
def DeclarationContextTrace :
    SMT.TypeContext → SMT.Chunk → SMT.TypeContext → Prop
  | Λ, [], Γ => Γ = Λ
  | Λ, .declare_const v τ :: Dlt, Γ =>
      v ∉ Λ ∧ DeclarationContextTrace (Λ.insert v τ) Dlt Γ
  | Λ, .define_fun _ _ _ _ :: Dlt, Γ =>
      DeclarationContextTrace Λ Dlt Γ
  | Λ, .define_const _ _ _ :: Dlt, Γ =>
      DeclarationContextTrace Λ Dlt Γ
  | Λ, .assert _ :: Dlt, Γ => DeclarationContextTrace Λ Dlt Γ
  | Λ, .push _ :: Dlt, Γ => DeclarationContextTrace Λ Dlt Γ
  | Λ, .pop _ :: Dlt, Γ => DeclarationContextTrace Λ Dlt Γ
  | Λ, .check_sat :: Dlt, Γ => DeclarationContextTrace Λ Dlt Γ

@[simp] theorem DeclarationContextTrace.nil (Λ : SMT.TypeContext) :
    DeclarationContextTrace Λ [] Λ := rfl

theorem DeclarationContextTrace.helperSpecChunk
    (Λ : SMT.TypeContext) (v : SMT.𝒱) (τ : SMTType)
    (spec : SMT.Term) (hv : v ∉ Λ) :
    DeclarationContextTrace Λ (helperSpecChunk v τ spec)
      (Λ.insert v τ) := by
  exact ⟨hv, rfl⟩

theorem DeclarationContextTrace.append
    {Λ Γ₁ Γ₂ : SMT.TypeContext} {D₁ D₂ : SMT.Chunk}
    (h₁ : DeclarationContextTrace Λ D₁ Γ₁)
    (h₂ : DeclarationContextTrace Γ₁ D₂ Γ₂) :
    DeclarationContextTrace Λ (D₁ ++ D₂) Γ₂ := by
  induction D₁ generalizing Λ with
  | nil =>
      change Γ₁ = Λ at h₁
      subst Γ₁
      exact h₂
  | cons i D ih =>
      cases i with
      | declare_const v τ =>
          obtain ⟨hv, htail⟩ := h₁
          exact ⟨hv, ih htail⟩
      | define_fun v τ σ t => exact ih h₁
      | define_const v τ t => exact ih h₁
      | assert t => exact ih h₁
      | push n => exact ih h₁
      | pop n => exact ih h₁
      | check_sat => exact ih h₁

/-- Replay a declaration trace from a smaller base context.  Freshness in the
larger base implies freshness in the smaller one, and the replayed core stays
entry-wise contained in the original result.  This is the key operation for
composing declaration traces when an encoder branch leaves irrelevant local
bindings in its operational context. -/
theorem DeclarationContextTrace.rebase_subset
    {LambdaSmall LambdaBig GammaBig : SMT.TypeContext}
    {Dlt : SMT.Chunk}
    (hsub : LambdaSmall.entries ⊆ LambdaBig.entries)
    (htrace : DeclarationContextTrace LambdaBig Dlt GammaBig) :
    ∃ GammaSmall,
      DeclarationContextTrace LambdaSmall Dlt GammaSmall ∧
      GammaSmall.entries ⊆ GammaBig.entries := by
  induction Dlt generalizing LambdaSmall LambdaBig with
  | nil =>
      change GammaBig = LambdaBig at htrace
      subst GammaBig
      exact ⟨LambdaSmall, rfl, hsub⟩
  | cons i D ih =>
      cases i with
      | declare_const v tau =>
          obtain ⟨hvBig, htail⟩ := htrace
          have hvSmall : v ∉ LambdaSmall := by
            intro hv
            exact hvBig (AList.mem_of_subset hsub hv)
          have hins : (LambdaSmall.insert v tau).entries ⊆
              (LambdaBig.insert v tau).entries := by
            rw [AList.entries_insert_of_notMem hvSmall,
              AList.entries_insert_of_notMem hvBig]
            intro e he
            rcases List.mem_cons.mp he with rfl | he
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (hsub he)
          obtain ⟨GammaSmall, htraceSmall, hfinal⟩ :=
            ih hins htail
          exact ⟨GammaSmall, ⟨hvSmall, htraceSmall⟩, hfinal⟩
      | define_fun v tau sigma body => exact ih hsub htrace
      | define_const v tau body => exact ih hsub htrace
      | assert body => exact ih hsub htrace
      | push n => exact ih hsub htrace
      | pop n => exact ih hsub htrace
      | check_sat => exact ih hsub htrace

/-- A declaration trace only adds fresh bindings; every binding present at
the beginning is therefore still present at the end. -/
theorem DeclarationContextTrace.entries_subset
    {Lambda Gamma : SMT.TypeContext} {Dlt : SMT.Chunk}
    (h : DeclarationContextTrace Lambda Dlt Gamma) :
    Lambda.entries ⊆ Gamma.entries := by
  induction Dlt generalizing Lambda with
  | nil =>
      change Gamma = Lambda at h
      subst Gamma
      exact fun _ he => he
  | cons i D ih =>
      cases i with
      | declare_const v tau =>
          obtain ⟨hv, htail⟩ := h
          exact List.Subset.trans
            (SMT.TypeContext.entries_subset_insert_of_notMem hv)
            (ih htail)
      | define_fun v tau sigma body => exact ih h
      | define_const v tau body => exact ih h
      | assert body => exact ih h
      | push n => exact ih h
      | pop n => exact ih h
      | check_sat => exact ih h

/-- The clean result of an exact declaration trace contains no entries other
than the input context and the declarations recorded by the trace. -/
theorem DeclarationContextTrace.context_generated
    {Lambda Gamma : SMT.TypeContext} {Dlt : SMT.Chunk}
    (h : DeclarationContextTrace Lambda Dlt Gamma) :
    ContextGeneratedByDeclarations Lambda Gamma Dlt := by
  induction Dlt generalizing Lambda with
  | nil =>
      change Gamma = Lambda at h
      subst Gamma
      simpa [declEntries]
  | cons i D ih =>
      cases i with
      | declare_const v tau =>
          obtain ⟨hv, htail⟩ := h
          intro e he
          have he' := ih htail he
          rw [AList.entries_insert_of_notMem hv] at he'
          simp only [declEntries, List.filterMap_cons]
          rcases List.mem_append.mp he' with hins | hdecl
          · rcases List.mem_cons.mp hins with rfl | hbase
            · exact List.mem_append.mpr (.inr (List.mem_cons_self))
            · exact List.mem_append.mpr (.inl hbase)
          · exact List.mem_append.mpr (.inr (List.mem_cons_of_mem _ hdecl))
      | define_fun v tau sigma body => simpa [declEntries] using ih h
      | define_const v tau body => simpa [declEntries] using ih h
      | assert body => simpa [declEntries] using ih h
      | push n => simpa [declEntries] using ih h
      | pop n => simpa [declEntries] using ih h
      | check_sat => simpa [declEntries] using ih h

/-- Every declaration name in an exact trace is fresh from the trace's input
context. -/
theorem DeclarationContextTrace.declVars_fresh_base
    {Lambda Gamma : SMT.TypeContext} {Dlt : SMT.Chunk}
    (h : DeclarationContextTrace Lambda Dlt Gamma) :
    ∀ v ∈ declVars Dlt, v ∉ Lambda := by
  induction Dlt generalizing Lambda with
  | nil => simp [declVars]
  | cons i D ih =>
      cases i with
      | declare_const w tau =>
          obtain ⟨hw, htail⟩ := h
          intro v hv
          simp only [declVars, List.filterMap_cons, List.mem_cons] at hv
          rcases hv with rfl | hv
          · exact hw
          · have hnot_insert := ih htail v hv
            exact fun hv_base => hnot_insert (by
              exact (AList.mem_insert _).mpr (.inr hv_base))
      | define_fun w tau sigma body =>
          simpa [declVars] using ih h
      | define_const w tau body =>
          simpa [declVars] using ih h
      | assert body => simpa [declVars] using ih h
      | push n => simpa [declVars] using ih h
      | pop n => simpa [declVars] using ih h
      | check_sat => simpa [declVars] using ih h

/-- Exact declaration traces introduce pairwise distinct helper names. -/
theorem DeclarationContextTrace.declVars_nodup
    {Lambda Gamma : SMT.TypeContext} {Dlt : SMT.Chunk}
    (h : DeclarationContextTrace Lambda Dlt Gamma) :
    (declVars Dlt).Nodup := by
  induction Dlt generalizing Lambda with
  | nil => simp [declVars]
  | cons i D ih =>
      cases i with
      | declare_const v tau =>
          obtain ⟨hv, htail⟩ := h
          simp only [declVars, List.filterMap_cons, List.nodup_cons]
          refine ⟨?_, ih htail⟩
          intro htail_mem
          exact (htail.declVars_fresh_base v htail_mem) <|
            (AList.mem_insert _).mpr (.inl rfl)
      | define_fun v tau sigma body => simpa [declVars] using ih h
      | define_const v tau body => simpa [declVars] using ih h
      | assert body => simpa [declVars] using ih h
      | push n => simpa [declVars] using ih h
      | pop n => simpa [declVars] using ih h
      | check_sat => simpa [declVars] using ih h

/-- Every typed declaration recorded by an exact trace is present in the
trace's final context. -/
theorem DeclarationContextTrace.declEntries_subset
    {Lambda Gamma : SMT.TypeContext} {Dlt : SMT.Chunk}
    (h : DeclarationContextTrace Lambda Dlt Gamma) :
    declEntries Dlt ⊆ Gamma.entries := by
  induction Dlt generalizing Lambda with
  | nil => simp [declEntries]
  | cons i D ih =>
      cases i with
      | declare_const v tau =>
          obtain ⟨hv, htail⟩ := h
          intro e he
          simp only [declEntries, List.filterMap_cons,
            List.mem_cons] at he
          rcases he with rfl | he
          · exact htail.entries_subset <| by
              rw [AList.entries_insert_of_notMem hv]
              exact List.mem_cons_self
          · exact ih htail he
      | define_fun v tau sigma body =>
          simpa [declEntries] using ih h
      | define_const v tau body =>
          simpa [declEntries] using ih h
      | assert body => simpa [declEntries] using ih h
      | push n => simpa [declEntries] using ih h
      | pop n => simpa [declEntries] using ih h
      | check_sat => simpa [declEntries] using ih h

theorem DeclarationContextTrace.declVar_mem
    {Lambda Gamma : SMT.TypeContext} {Dlt : SMT.Chunk}
    (h : DeclarationContextTrace Lambda Dlt Gamma)
    {v : SMT.𝒱} (hv : v ∈ declVars Dlt) : v ∈ Gamma := by
  obtain ⟨τ, hτ⟩ := exists_mem_declEntries_of_mem_declVars hv
  rw [AList.mem_keys]
  exact List.mem_keys_of_mem (h.declEntries_subset hτ)

/-- The final context of an exact declaration trace contains both its input
context and every typed declaration in the trace. -/
theorem DeclarationContextTrace.scoped_entries
    {Lambda Gamma : SMT.TypeContext} {Dlt : SMT.Chunk}
    (h : DeclarationContextTrace Lambda Dlt Gamma) :
    Lambda.entries ++ declEntries Dlt ⊆ Gamma.entries := by
  intro e he
  rcases List.mem_append.mp he with hbase | hdecl
  · exact h.entries_subset hbase
  · exact h.declEntries_subset hdecl

/-- Declaration traces are insensitive to the order of unrelated bindings in
their input context.  The resulting context has the same bindings, possibly
in a correspondingly different association-list order. -/
theorem DeclarationContextTrace.transport_perm
    {Lambda Lambda' Gamma : SMT.TypeContext} {Dlt : SMT.Chunk}
    (h : DeclarationContextTrace Lambda Dlt Gamma)
    (hperm : Lambda.entries.Perm Lambda'.entries) :
    ∃ Gamma', DeclarationContextTrace Lambda' Dlt Gamma' ∧
      Gamma.entries.Perm Gamma'.entries := by
  induction Dlt generalizing Lambda Lambda' with
  | nil =>
      change Gamma = Lambda at h
      subst Gamma
      exact ⟨Lambda', rfl, hperm⟩
  | cons i D ih =>
      cases i with
      | declare_const v tau =>
          obtain ⟨hv, htail⟩ := h
          have hv' : v ∉ Lambda' := by
            intro hv'
            exact hv ((AList.mem_of_perm hperm).mpr hv')
          have hperm_insert :
              (Lambda.insert v tau).entries.Perm
                (Lambda'.insert v tau).entries := by
            rw [AList.entries_insert_of_notMem hv,
              AList.entries_insert_of_notMem hv']
            exact hperm.cons (Sigma.mk v tau)
          obtain ⟨Gamma', htrace', hfinal⟩ :=
            ih htail hperm_insert
          exact ⟨Gamma', ⟨hv', htrace'⟩, hfinal⟩
      | define_fun v tau sigma body => exact ih h hperm
      | define_const v tau body => exact ih h hperm
      | assert body => exact ih h hperm
      | push n => exact ih h hperm
      | pop n => exact ih h hperm
      | check_sat => exact ih h hperm

/-- Inserting a binding whose key is absent from an update list commutes with
that update up to association-list order. -/
theorem SMT.TypeContext.update_insert_perm
    (Gamma : SMT.TypeContext) (v : SMT.𝒱) (tau : SMTType)
    (vs : List SMT.𝒱) (taus : List SMTType)
    (hlen : vs.length = taus.length) (hv : v ∉ vs) :
    ((Gamma.update vs taus hlen).insert v tau).entries.Perm
      (SMT.TypeContext.update (Gamma.insert v tau) vs taus hlen).entries := by
  induction vs, taus, hlen using List.reverse_induction₂ with
  | nil_nil =>
      simpa [SMT.TypeContext.update]
  | cons_cons w vs sigma taus hlen ih =>
      rw [List.concat_eq_append, List.mem_append,
        List.mem_singleton, not_or] at hv
      simp only [List.concat_eq_append]
      rw [SMT.TypeContext.update_concat Gamma vs taus w sigma hlen,
        SMT.TypeContext.update_concat (Gamma.insert v tau)
          vs taus w sigma hlen]
      exact (AList.insert_insert_of_ne
        (Gamma.update vs taus hlen) (Ne.symm hv.2)).trans
          (AList.perm_insert (ih hv.1))

/-- SMT typing depends on the bindings of a type context, not on their storage
order in the underlying association list. -/
theorem SMT.Typing.permute_context
    {Gamma Gamma' : SMT.TypeContext} {t : SMT.Term} {tau : SMTType}
    (hperm : Gamma.entries.Perm Gamma'.entries)
    (htyp : Gamma ⊢ˢ t : tau) :
    Gamma' ⊢ˢ t : tau := by
  refine SMT.Typing.weakening hperm.subset htyp ?_
  intro v hv hvGamma'
  exact (SMT.Typing.bv_notMem_context htyp v hv)
    ((AList.mem_of_perm hperm).mpr hvGamma')

/-- Fresh variables introduced after a declaration-producing computation may
be moved before that computation.  The exact declaration trace is preserved,
and the final context differs only by association-list order. -/
theorem DeclarationContextTrace.update_fresh
    {Lambda Gamma : SMT.TypeContext} {Dlt : SMT.Chunk}
    (h : DeclarationContextTrace Lambda Dlt Gamma)
    (vs : List SMT.𝒱) (taus : List SMTType)
    (hlen : vs.length = taus.length)
    (hfresh : ∀ v ∈ vs, v ∉ Gamma) :
    ∃ Gamma',
      DeclarationContextTrace (Lambda.update vs taus hlen) Dlt Gamma' ∧
      Gamma'.entries.Perm (Gamma.update vs taus hlen).entries := by
  induction Dlt generalizing Lambda with
  | nil =>
      change Gamma = Lambda at h
      subst Gamma
      exact ⟨Lambda.update vs taus hlen, rfl, .refl _⟩
  | cons i D ih =>
      cases i with
      | declare_const v tau =>
          obtain ⟨hv, htail⟩ := h
          have hvGamma : v ∈ Gamma := by
            rw [AList.mem_keys]
            exact List.mem_keys_of_mem <| htail.entries_subset <| by
              rw [AList.entries_insert_of_notMem hv]
              exact List.mem_cons_self
          have hv_vs : v ∉ vs := by
            intro hvs
            exact (hfresh v hvs) hvGamma
          have hv_update : v ∉ Lambda.update vs taus hlen := by
            intro hmem
            rw [SMT.TypeContext.mem_update_iff Lambda v vs taus hlen] at hmem
            exact (not_or.mpr ⟨hv_vs, hv⟩) hmem
          obtain ⟨GammaMid, htraceMid, hpermMid⟩ :=
            ih htail
          have hbasePerm :
              ((Lambda.update vs taus hlen).insert v tau).entries.Perm
                (SMT.TypeContext.update (Lambda.insert v tau)
                  vs taus hlen).entries :=
            SMT.TypeContext.update_insert_perm Lambda v tau vs taus hlen hv_vs
          obtain ⟨Gamma', htrace', hperm'⟩ :=
            htraceMid.transport_perm hbasePerm.symm
          exact ⟨Gamma', ⟨hv_update, htrace'⟩,
            hperm'.symm.trans hpermMid⟩
      | define_fun v tau sigma body => exact ih h
      | define_const v tau body => exact ih h
      | assert body => exact ih h
      | push n => exact ih h
      | pop n => exact ih h
      | check_sat => exact ih h

/-- A context in which a generated term is evaluated contains both the input
context and all typed helper declarations that the encoder later re-scopes. -/
abbrev ScopedContextExtends
    (Λ : SMT.TypeContext) (Dlt : SMT.Chunk) (Γ : SMT.TypeContext) : Prop :=
  Λ.entries ++ declEntries Dlt ⊆ Γ.entries

theorem DeclarationContextTrace.scoped_extends
    {Lambda Gamma : SMT.TypeContext} {Dlt : SMT.Chunk}
    (h : DeclarationContextTrace Lambda Dlt Gamma) :
    ScopedContextExtends Lambda Dlt Gamma :=
  h.scoped_entries

/-- The declaration-generated core of an encoder run, embedded in its actual
operational context.  The operational context may additionally retain local
source-binder entries; those entries are observable in the current encoder
state but are neither emitted declarations nor dependencies of the generated
term. -/
abbrev DeclarationContextEnvelope
    (Lambda : SMT.TypeContext) (Dlt : SMT.Chunk)
    (GammaOp : SMT.TypeContext) : Prop :=
  ∃ GammaCore,
    DeclarationContextTrace Lambda Dlt GammaCore ∧
    GammaCore.entries ⊆ GammaOp.entries

theorem DeclarationContextEnvelope.refl (Lambda : SMT.TypeContext) :
    DeclarationContextEnvelope Lambda [] Lambda :=
  ⟨Lambda, rfl, fun _ h => h⟩

theorem DeclarationContextEnvelope.of_trace
    {Lambda Gamma : SMT.TypeContext} {Dlt : SMT.Chunk}
    (h : DeclarationContextTrace Lambda Dlt Gamma) :
    DeclarationContextEnvelope Lambda Dlt Gamma :=
  ⟨Gamma, h, fun _ he => he⟩

/-- Envelopes compose even when the first operational result contains local
residue: replay the second declaration trace from the first clean core, then
append the two exact traces. -/
theorem DeclarationContextEnvelope.append
    {Lambda Gamma₁ Gamma₂ : SMT.TypeContext}
    {D₁ D₂ : SMT.Chunk}
    (h₁ : DeclarationContextEnvelope Lambda D₁ Gamma₁)
    (h₂ : DeclarationContextEnvelope Gamma₁ D₂ Gamma₂) :
    DeclarationContextEnvelope Lambda (D₁ ++ D₂) Gamma₂ := by
  obtain ⟨Core₁, htrace₁, hcore₁⟩ := h₁
  obtain ⟨Core₂, htrace₂, hcore₂⟩ := h₂
  obtain ⟨Core₂', htrace₂', hcore₂'⟩ :=
    htrace₂.rebase_subset hcore₁
  exact ⟨Core₂', DeclarationContextTrace.append htrace₁ htrace₂',
    fun e he => hcore₂ (hcore₂' he)⟩

theorem DeclarationContextEnvelope.scoped_extends
    {Lambda GammaOp : SMT.TypeContext} {Dlt : SMT.Chunk}
    (h : DeclarationContextEnvelope Lambda Dlt GammaOp) :
    ScopedContextExtends Lambda Dlt GammaOp := by
  obtain ⟨GammaCore, htrace, hsub⟩ := h
  exact fun e he => hsub (htrace.scoped_extends he)

theorem DeclarationContextEnvelope.declVars_fresh_base
    {Lambda GammaOp : SMT.TypeContext} {Dlt : SMT.Chunk}
    (h : DeclarationContextEnvelope Lambda Dlt GammaOp) :
    ∀ v ∈ declVars Dlt, v ∉ Lambda := by
  obtain ⟨_, htrace, _⟩ := h
  exact htrace.declVars_fresh_base

theorem DeclarationContextEnvelope.declVars_nodup
    {Lambda GammaOp : SMT.TypeContext} {Dlt : SMT.Chunk}
    (h : DeclarationContextEnvelope Lambda Dlt GammaOp) :
    (declVars Dlt).Nodup := by
  obtain ⟨_, htrace, _⟩ := h
  exact htrace.declVars_nodup

theorem ContextGeneratedByDeclarations.refl
    (Λ : SMT.TypeContext) :
    ContextGeneratedByDeclarations Λ Λ [] := by
  simpa using (List.Subset.refl Λ.entries)

theorem ContextGeneratedByDeclarations.insert_helper
    (Λ : SMT.TypeContext) (v : SMT.𝒱) (τ : SMTType)
    (spec : SMT.Term) (hv : v ∉ Λ) :
    ContextGeneratedByDeclarations Λ (Λ.insert v τ)
      (helperSpecChunk v τ spec) := by
  intro e he
  rw [AList.entries_insert_of_notMem hv] at he
  simpa [declEntries_helperSpecChunk, or_comm] using he

theorem ContextGeneratedByDeclarations.append
    {Λ Γ₁ Γ₂ : SMT.TypeContext} {D₁ D₂ : SMT.Chunk}
    (h₁ : ContextGeneratedByDeclarations Λ Γ₁ D₁)
    (h₂ : ContextGeneratedByDeclarations Γ₁ Γ₂ D₂) :
    ContextGeneratedByDeclarations Λ Γ₂ (D₁ ++ D₂) := by
  intro e he
  rw [declEntries_append]
  rcases List.mem_append.mp (h₂ he) with he₁ | heD₂
  · rcases List.mem_append.mp (h₁ he₁) with heΛ | heD₁
    · exact List.mem_append.mpr (.inl heΛ)
    · exact List.mem_append.mpr (.inr (List.mem_append.mpr (.inl heD₁)))
  · exact List.mem_append.mpr (.inr (List.mem_append.mpr (.inr heD₂)))

theorem ScopedContextExtends.left_of_append
    {Λ Γ : SMT.TypeContext} {D₁ D₂ : SMT.Chunk}
    (h : ScopedContextExtends Λ (D₁ ++ D₂) Γ) :
    ScopedContextExtends Λ D₁ Γ := by
  intro e he
  apply h
  rw [declEntries_append]
  rcases List.mem_append.mp he with heΛ | heD₁
  · exact List.mem_append.mpr (.inl heΛ)
  · exact List.mem_append.mpr (.inr (List.mem_append.mpr (.inl heD₁)))

theorem ScopedContextExtends.base
    {Λ Γ : SMT.TypeContext} {Dlt : SMT.Chunk}
    (h : ScopedContextExtends Λ Dlt Γ) : Λ ⊆ Γ := by
  intro e he
  exact h (List.mem_append.mpr (.inl he))

theorem ScopedContextExtends.lookup_of_declared
    {Λ Γ : SMT.TypeContext} {Dlt : SMT.Chunk}
    (h : ScopedContextExtends Λ Dlt Γ)
    {v : SMT.𝒱} {τ : SMTType}
    (he : ⟨v, τ⟩ ∈ declEntries Dlt) :
    Γ.lookup v = some τ := by
  apply Option.mem_def.mp
  apply AList.mem_lookup_iff.mpr
  exact h (List.mem_append.mpr (.inr he))

theorem ScopedContextExtends.right_of_generated
    {Λ Γ₁ Γ : SMT.TypeContext} {D₁ D₂ : SMT.Chunk}
    (hgen : ContextGeneratedByDeclarations Λ Γ₁ D₁)
    (h : ScopedContextExtends Λ (D₁ ++ D₂) Γ) :
    ScopedContextExtends Γ₁ D₂ Γ := by
  intro e he
  apply h
  rw [declEntries_append]
  rcases List.mem_append.mp he with heΓ₁ | heD₂
  · rcases List.mem_append.mp (hgen heΓ₁) with heΛ | heD₁
    · exact List.mem_append.mpr (.inl heΛ)
    · exact List.mem_append.mpr (.inr (List.mem_append.mpr (.inl heD₁)))
  · exact List.mem_append.mpr (.inr (List.mem_append.mpr (.inr heD₂)))

/-- Portable typing for the specification bodies already accumulated before
the current recursive encoder call. -/
abbrev ScopedSpecsTyping
    (Λ : SMT.TypeContext) (Dlt : SMT.Chunk) : Prop :=
  ∀ (Γsup : SMT.TypeContext), ScopedContextExtends Λ Dlt Γsup →
    (∀ b ∈ specBodies Dlt, ∀ v ∈ SMT.bv b, v ∉ Γsup) →
    ∀ b ∈ specBodies Dlt, Γsup ⊢ˢ b : SMTType.bool

theorem ScopedSpecsTyping.nil (Λ : SMT.TypeContext) :
    ScopedSpecsTyping Λ [] := by
  simp [ScopedSpecsTyping, specBodies]

/-- Syntactic information needed when an encoder result and its generated
helper specifications are moved from the operational context into a local
binder scope.  The explicit bound-variable freshness premises are essential:
SMT typing weakening is false when a newly added context entry captures a
bound name. -/
abbrev ScopedGeneratedTyping
    (Λ : SMT.TypeContext) (Dlt : SMT.Chunk)
    (t : SMT.Term) (σ : SMTType) : Prop :=
  (∀ (Γsup : SMT.TypeContext), ScopedContextExtends Λ Dlt Γsup →
    (∀ v ∈ SMT.bv t, v ∉ Γsup) →
    Γsup ⊢ˢ t : σ) ∧
  ScopedSpecsTyping Λ Dlt

/-- Prefix a portable generated-term typing contract with an earlier clean
declaration trace. -/
theorem ScopedGeneratedTyping.append_prefix
    {Base Core : SMT.TypeContext} {Dpre Dlt : SMT.Chunk}
    {t : SMT.Term} {σ : SMTType}
    (hpre : DeclarationContextTrace Base Dpre Core)
    (hpre_specs : ScopedSpecsTyping Base Dpre)
    (h : ScopedGeneratedTyping Core Dlt t σ) :
    ScopedGeneratedTyping Base (Dpre ++ Dlt) t σ := by
  constructor
  · intro Γsup hscope hbv
    exact h.1 Γsup
      (ScopedContextExtends.right_of_generated
        hpre.context_generated hscope) hbv
  · intro Γsup hscope hall_bv body hbody
    rw [specBodies_append, List.mem_append] at hbody
    rcases hbody with hprefix | hlocal
    · apply hpre_specs Γsup hscope.left_of_append
        (fun b hb => hall_bv b (by
          rw [specBodies_append, List.mem_append]
          exact Or.inl hb)) body hprefix
    · apply h.2 Γsup
        (ScopedContextExtends.right_of_generated
          hpre.context_generated hscope)
        (fun b hb => hall_bv b (by
          rw [specBodies_append, List.mem_append]
          exact Or.inr hb)) body hlocal

/-- Lift operational typing into any declaration-generated scope. -/
theorem ScopedGeneratedTyping.of_operational
    {Λ Γop : SMT.TypeContext} {Dlt : SMT.Chunk}
    {t : SMT.Term} {σ : SMTType}
    (hgen : ContextGeneratedByDeclarations Λ Γop Dlt)
    (ht : Γop ⊢ˢ t : σ)
    (hspec : ∀ b ∈ specBodies Dlt,
      Γop ⊢ˢ b : SMTType.bool) :
    ScopedGeneratedTyping Λ Dlt t σ := by
  constructor
  · intro Γsup hscope ht_bv
    have hop_sub : Γop ⊆ Γsup := fun e he => hscope (hgen he)
    exact SMT.Typing.weakening hop_sub ht ht_bv
  · intro Γsup hscope hspec_bv b hb
    have hop_sub : Γop ⊆ Γsup := fun e he => hscope (hgen he)
    exact SMT.Typing.weakening hop_sub (hspec b hb)
      (hspec_bv b hb)

/-- Re-scope one operational binary helper step through the clean declaration
core carried by its two inputs.  The free-variable dependency hypotheses are
the precise condition needed to strengthen operational typing to that core. -/
theorem ScopedGeneratedTyping.of_binary_helper
    {Base LambdaOp GammaOp : SMT.TypeContext}
    {Dpre Dlt : SMT.Chunk}
    {A B t : SMT.Term} {σA σB σ : SMTType}
    (henvelope : DeclarationContextEnvelope Base Dpre LambdaOp)
    (hstep : DeclarationContextTrace LambdaOp Dlt GammaOp)
    (htA_op : LambdaOp ⊢ˢ A : σA)
    (htB_op : LambdaOp ⊢ˢ B : σB)
    (ht_op : GammaOp ⊢ˢ t : σ)
    (hspec_op : ∀ b ∈ specBodies Dlt,
      GammaOp ⊢ˢ b : SMTType.bool)
    (hA : ScopedGeneratedTyping Base Dpre A σA)
    (hB : ScopedGeneratedTyping Base Dpre B σB)
    (ht_fv : SMT.fv t ⊆
      (SMT.fv A ∪ SMT.fv B) ∪ declVars Dlt)
    (hspec_fv : ∀ b ∈ specBodies Dlt,
      SMT.fv b ⊆ (SMT.fv A ∪ SMT.fv B) ∪ declVars Dlt) :
    DeclarationContextEnvelope Base (Dpre ++ Dlt) GammaOp ∧
      ScopedGeneratedTyping Base (Dpre ++ Dlt) t σ := by
  obtain ⟨Core, hpre, hCore_op⟩ := henvelope
  obtain ⟨Core', hstep', hCore'_op⟩ := hstep.rebase_subset hCore_op
  have hA_bv : ∀ v ∈ SMT.bv A, v ∉ Core := by
    intro v hv hvCore
    exact SMT.Typing.bv_notMem_context htA_op v hv
      (AList.mem_of_subset hCore_op hvCore)
  have hB_bv : ∀ v ∈ SMT.bv B, v ∉ Core := by
    intro v hv hvCore
    exact SMT.Typing.bv_notMem_context htB_op v hv
      (AList.mem_of_subset hCore_op hvCore)
  have htA_Core : Core ⊢ˢ A : σA :=
    hA.1 Core hpre.scoped_extends hA_bv
  have htB_Core : Core ⊢ˢ B : σB :=
    hB.1 Core hpre.scoped_extends hB_bv
  have dependency_mem_Core' :
      ∀ {v}, v ∈ (SMT.fv A ∪ SMT.fv B) ∪ declVars Dlt →
        v ∈ Core' := by
    intro v hv
    rw [List.mem_union_iff, List.mem_union_iff] at hv
    rcases hv with (hvA | hvB) | hvdecl
    · exact AList.mem_of_subset hstep'.entries_subset
        (SMT.Typing.mem_context_of_mem_fv htA_Core hvA)
    · exact AList.mem_of_subset hstep'.entries_subset
        (SMT.Typing.mem_context_of_mem_fv htB_Core hvB)
    · exact hstep'.declVar_mem hvdecl
  have ht_Core' : Core' ⊢ˢ t : σ :=
    SMT.Typing.strengthening_of_fv_subset hCore'_op ht_op
      (fun v hv => dependency_mem_Core' (ht_fv hv))
  have hspec_Core' : ∀ b ∈ specBodies Dlt,
      Core' ⊢ˢ b : SMTType.bool := by
    intro b hb
    exact SMT.Typing.strengthening_of_fv_subset hCore'_op
      (hspec_op b hb)
      (fun v hv => dependency_mem_Core' (hspec_fv b hb hv))
  have hlocal : ScopedGeneratedTyping Core Dlt t σ :=
    ScopedGeneratedTyping.of_operational hstep'.context_generated
      ht_Core' hspec_Core'
  exact ⟨
    ⟨Core', DeclarationContextTrace.append hpre hstep', hCore'_op⟩,
    hlocal.append_prefix hpre hA.2⟩

/-- Weaken a typed term across one declaration-generated encoder step.  Bound
variables already belong to the old used-name set, while every newly declared
name is fresh from that set, so no binder can be captured. -/
theorem typing_weakening_generated
    {Γ Γ' : SMT.TypeContext} {Dlt : SMT.Chunk}
    {used : List SMT.𝒱} {t : SMT.Term} {σ : SMTType}
    (hsub : Γ ⊆ Γ')
    (hgen : ContextGeneratedByDeclarations Γ Γ' Dlt)
    (hdecl : ∀ v ∈ declVars Dlt, v ∉ used)
    (ht : Γ ⊢ˢ t : σ)
    (hbv : ∀ v ∈ SMT.bv t, v ∈ used) :
    Γ' ⊢ˢ t : σ := by
  apply SMT.Typing.weakening hsub ht
  intro v hv hvΓ'
  have hvused := hbv v hv
  obtain ⟨τv, hlookup⟩ := Option.isSome_iff_exists.mp
    (AList.lookup_isSome.mpr hvΓ')
  have hentry : (⟨v, τv⟩ : Sigma fun _ : SMT.𝒱 => SMTType) ∈
      Γ'.entries := AList.mem_lookup_iff.mp hlookup
  rcases List.mem_append.mp (hgen hentry) with hbase | hnew
  · have hvΓ : v ∈ Γ :=
      AList.mem_keys.mpr (List.mem_map.mpr ⟨⟨v, τv⟩, hbase, rfl⟩)
    exact SMT.Typing.bv_notMem_context ht v hv hvΓ
  · exact hdecl v (mem_declVars_of_mem_declEntries hnew) hvused

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

/-- Helper specifications remain true when the new valuation agrees with the
old valuation on every free variable of every specification body. -/
theorem SpecBodiesTrue.of_agreesOnFV.{u}
    {Θ Θ' : SMT.RenamingContext.Context.{u}}
    {Γ : SMT.TypeContext} {Dlt : SMT.Chunk}
    (h : SpecBodiesTrue Θ Γ Dlt)
    (hagrees : ∀ b ∈ specBodies Dlt,
      SMT.RenamingContext.AgreesOnFV Θ' Θ b) :
    SpecBodiesTrue Θ' Γ Dlt := by
  intro b hb
  obtain ⟨hcov, db, hresp, hden, htype, htrue⟩ := h b hb
  have hagree := hagrees b hb
  have hcov' : SMT.RenamingContext.CoversFV Θ' b :=
    SMT.RenamingContext.coversFV_of_agreesOnFV_symm hagree hcov
  have hden' := SMT.RenamingContext.denote_congr_of_agreesOnFV
    (t := b) (h1 := hcov') (h2 := hcov) hagree
  refine ⟨hcov', db, ?_, hden'.trans hden, htype, htrue⟩
  intro v τ hv hlookup
  obtain ⟨d, hd, hdtype⟩ := hresp hv hlookup
  exact ⟨d, (hagree hv).trans hd, hdtype⟩

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
    (t' : SMT.Term) (σ : SMTType) (Λ : SMT.TypeContext)
    (Dlt : SMT.Chunk) : Prop :=
  ∀ (Γ_sup : SMT.TypeContext), ScopedContextExtends Λ Dlt Γ_sup →
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

/-- Declaration-aware postcondition rooted at a clean context and a prefix of
already generated declarations.  `Λop` is the actual operational input
context; it may contain irrelevant local binder residue.  Every portable
claim is instead made over `Base` and the complete `Dpre ++ Dlt` trace. -/
abbrev EncodeTermRepScopedPostFrom.{u}
    (t : B.Term) (E : B.Env) (α : BType)
    (Base : SMT.TypeContext) (Dpre : SMT.Chunk)
    (Λop : SMT.TypeContext) (decl : SMT.Chunk)
    (t' : SMT.Term) (σ : SMTType)
    (E' : SMT.Env) (Γ' : SMT.TypeContext) : Prop :=
  ∃ Dlt : SMT.Chunk,
    E'.declarations = decl ++ Dlt ∧
    DeclarationContextEnvelope Base (Dpre ++ Dlt) Γ' ∧
    EncodeTermRepScopedTotal.{u} t E α Λop t' σ Γ' E'.usedVars Dlt ∧
    EncodeTermRepGuardedSound.{u} t E α t' σ Base (Dpre ++ Dlt) ∧
    ScopedGeneratedTyping Base (Dpre ++ Dlt) t' σ

/-- Root instance of `EncodeTermRepScopedPostFrom`, used by binder clients. -/
abbrev EncodeTermRepScopedPost.{u}
    (t : B.Term) (E : B.Env) (α : BType) (Λ : SMT.TypeContext)
    (decl : SMT.Chunk) (t' : SMT.Term) (σ : SMTType)
    (E' : SMT.Env) (Γ' : SMT.TypeContext) : Prop :=
  EncodeTermRepScopedPostFrom.{u} t E α Λ [] Λ decl t' σ E' Γ'

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

/-- The semantic portion of `EncodeTermRepPost`.  Binder cases prove this
directly while the structural `encodeTerm_state` specification supplies the
state monotonicity and freshness conjuncts independently. -/
abbrev EncodeTermRepSemanticPost.{u}
    (t : B.Term) (α : BType) (Λ : SMT.TypeContext)
    («Δ» : B.RenamingContext.Context)
    (Δ₀ : SMT.RenamingContext.Context.{u})
    (T : ZFSet.{u}) (hT : T ∈ ⟦α⟧ᶻ)
    (E : B.Env) (t' : SMT.Term) (σ : SMTType)
    (E' : SMT.Env) (Γ' : SMT.TypeContext) : Prop :=
  Nonempty (σ ~> α.toSMTType) ∧
  (Γ' ⊢ˢ t' : σ) ∧
  EncodeTermResultShape t t' σ ∧
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

/-- Reassemble the full representation-aware postcondition from its semantic
part and the encoder's representation-independent state invariant. -/
theorem encodeTermRepPost_of_state_and_semantic.{u}
    {t : B.Term} {α : BType} {Λ : SMT.TypeContext}
    {«Δ» : B.RenamingContext.Context}
    {Δ₀ : SMT.RenamingContext.Context.{u}}
    {used : List SMT.𝒱} {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ}
    {E : B.Env} {t' : SMT.Term} {σ : SMTType}
    {E' : SMT.Env} {Γ' : SMT.TypeContext}
    (hstate :
      used ⊆ E'.usedVars ∧
      Λ ⊆ Γ' ∧
      Γ'.keys ⊆ E'.usedVars ∧
      B.CoversUsedVars E'.usedVars t ∧
      (∀ v ∈ used, v ∉ Λ → v ∉ B.Term.vars t → v ∉ Γ'))
    (hsemantic : EncodeTermRepSemanticPost t α Λ «Δ» Δ₀ T hT
      E t' σ E' Γ') :
    EncodeTermRepPost t α Λ «Δ» Δ₀ used T hT E t' σ E' Γ' := by
  obtain ⟨hused, hcontext, hkeys, hcovers, hpreserves⟩ := hstate
  obtain ⟨hpath, htyping, hshape, hden⟩ := hsemantic
  exact ⟨hused, hcontext, hkeys, hcovers, hpath, htyping, hshape,
    hpreserves, hden⟩

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
abbrev EncodeTermRepScopedFromIH.{u} (t : B.Term) : Prop :=
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
    ∀ {Base : SMT.TypeContext} {Dpre : SMT.Chunk},
      DeclarationContextEnvelope Base Dpre Λ →
      (∀ v ∈ B.fv t, v ∈ Base) →
      ScopedSpecsTyping Base Dpre →
    ∀ {n : ℕ} {decl : SMT.Chunk},
      (⦃fun ⟨E0, Λ'⟩ ↦
        ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧
          Λ.keys ⊆ E0.usedVars ∧ E0.usedVars = used ∧
          E0.declarations = decl⌝ ⦄
      encodeTerm t E
      ⦃ ⇓? (⟨t', σ⟩ : SMT.Term × SMTType) ⟨E', Γ'⟩ =>
        ⌜EncodeTermRepScopedPostFrom.{u} t E α Base Dpre Λ decl
          t' σ E' Γ'⌝ ⦄)

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
abbrev EncodeTermRepScopedBoolFromIH.{u} (t : B.Term) : Prop :=
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
    ∀ {Base : SMT.TypeContext} {Dpre : SMT.Chunk},
      DeclarationContextEnvelope Base Dpre Λ →
      (∀ v ∈ B.fv t, v ∈ Base) →
      ScopedSpecsTyping Base Dpre →
    ∀ {n : ℕ} {decl : SMT.Chunk},
      (⦃fun ⟨E0, Λ'⟩ ↦
        ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧
          Λ.keys ⊆ E0.usedVars ∧ E0.usedVars = used ∧
          E0.declarations = decl⌝ ⦄
      encodeTerm t E
      ⦃ ⇓? (⟨t', σ⟩ : SMT.Term × SMTType) ⟨E', Γ'⟩ =>
        ⌜EncodeTermRepScopedPostFrom.{u} t E BType.bool
          Base Dpre Λ decl t' σ E' Γ'⌝ ⦄)

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

The contract is indexed by the representation actually emitted for the
quantifier domain.  Besides semantic preimages, it records that every
successful flag transformation remains in the representation grammar used by
the induction hypothesis.  The proof-obligation layer discharges both facts
from the functional hypotheses and environment invariants that justify entries
in `E.flags`; the raw term theorem keeps them explicit. -/
abbrev EncodeTermAllBinderAdmissible.{u} : Prop :=
  ∀ (E : B.Env) (vs : List B.𝒱) (D P : B.Term) (τ : BType),
    E.context ⊢ᴮ B.Term.all vs D P : BType.bool →
    E.context ⊢ᴮ D : BType.set τ →
    ∀ («Δ» : B.RenamingContext.Context.{u})
      (Δ_fv_D : ∀ v ∈ B.fv D, («Δ» v).isSome = true)
      (𝒟 : ZFSet.{u}) (h𝒟 : 𝒟 ∈ ⟦BType.set τ⟧ᶻ),
      ⟦D.abstract «Δ» Δ_fv_D⟧ᴮ = some ⟨𝒟, ⟨BType.set τ, h𝒟⟩⟩ →
      ∀ (ρ : SMTType) (_hρ : BType.SupportedSMT τ ρ)
        (τs : List SMTType)
        (hvs_len : vs.length =
          (ρ.fromProdl (vs.length - 1)).length)
        (hτs_len : τs.length =
          (ρ.fromProdl (vs.length - 1)).length),
        (∀ i (hi : i < τs.length),
          SMTFlagTypeRel (vs[i]'(by omega) ∈ E.flags)
            ((ρ.fromProdl (vs.length - 1))[i]'(hτs_len ▸ hi))
            (τs[i]'hi)) →
        (∀ i (hi : i < τs.length),
          BType.SupportedSMT
            (τ.get vs.length ⟨i, by omega⟩) (τs[i]'hi)) ∧
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
