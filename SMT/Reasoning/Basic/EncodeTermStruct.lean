import SMT.Reasoning.Basic.StateSpecs
import SMT.Reasoning.SubstLemmas
import SMT.Reasoning.Axioms

/-!
# `encodeTerm` structural specification

`encodeTerm_struct` captures the *structural* postcondition of `encodeTerm`:
state monotonicity, free-variable coverage of the encoded term, source-variable
coverage/preservation, and the existence of a covering renaming context.

Unlike `encodeTerm_spec`, it requires neither the `respects` hypothesis nor any
`B`-typing, and asserts neither `σ = α.toSMTType` nor any denotational fact —
precisely the parts unavailable (indeed false) for a flagged binder. It is
consumed by the HAS-FLAG branch of `encodeTerm_spec.all_case`, which needs
structural facts about the encoding of the binder body `P` without a (false)
`respects`.

The renaming witness is discharged generically (`renaming_witness`): the
encoded term's free variables all live in the final context `Γ' ⊆ usedVars`,
so `Δ₀` padded over `Γ'` covers it.
-/

open Std.Do B SMT ZFSet
set_option mvcgen.warning false

namespace SMT.TypeContext

/-- Erasing any key keeps a non-member a non-member: if `v ∉ Γ` then `v ∉ Γ.erase z`. -/
theorem notMem_erase {Γ : SMT.TypeContext} {v z : SMT.𝒱}
    (h : v ∉ Γ) : v ∉ Γ.erase z := fun hin => h (AList.mem_erase.mp hin).2

/-- Erasing a key only shrinks the key set: `(Γ.erase z).keys ⊆ Γ.keys`. -/
theorem keys_erase_subset {Γ : SMT.TypeContext} {z : SMT.𝒱} :
    (Γ.erase z).keys ⊆ Γ.keys := by
  rw [AList.keys_erase]; exact List.erase_subset

/-- If `Γ.entries ⊆ Δ.entries` and the erased key `z` is not in `Γ`, then
`Γ.entries ⊆ (Δ.erase z).entries`: erasing `z` cannot drop any entry of `Γ`
because no entry of `Γ` has key `z`. -/
theorem entries_subset_erase_of_notMem {Γ Γ₂ : SMT.TypeContext} {z : SMT.𝒱}
    (h : Γ.entries ⊆ Γ₂.entries) (hz : z ∉ Γ) : Γ.entries ⊆ (Γ₂.erase z).entries := by
  intro e he
  apply List.mem_kerase_of_ne_key _ (h he)
  intro hcontra
  exact hz (AList.mem_keys.mpr (hcontra ▸ (List.mem_map.mpr ⟨e, he, rfl⟩)))

/-- Key membership transports along an `entries ⊆ entries` inclusion. -/
theorem mem_of_entries_subset {a : SMT.𝒱} {Γ Γ' : SMT.TypeContext}
    (ha : a ∈ Γ) (hsub : Γ.entries ⊆ Γ'.entries) : a ∈ Γ' := by
  have ha' := AList.mem_keys.mpr ha
  obtain ⟨τ, hτ⟩ := List.mem_keys.mp ha'
  exact AList.mem_keys.mp (List.mem_keys.mpr ⟨τ, hsub hτ⟩)

end SMT.TypeContext

/-- Any computation `m` followed by an unconditional `throw` satisfies every
`mayThrow` postcondition: the overall computation always throws, and `mayThrow`
imposes no obligation on thrown outcomes. Used to discharge the (statically
non-eliminable) throw branches of `encodeTerm_state`'s compound cases, whose
throw messages re-invoke `encodeTerm` on a subterm. -/
theorem wp_bind_throw {α : Type}
    (m : Encoder α) (msg : α → String)
    (Q : (SMT.Term × SMTType) →
      Assertion (PostShape.arg EncoderState (PostShape.except String PostShape.pure)))
    (s : EncoderState) :
    ⊢ₛ wp⟦do let r ← m; throw (msg r) : Encoder (SMT.Term × SMTType)⟧
      (PostCond.mayThrow Q) s := by
  simp only [wp, bind, StateT.bind, Except.bind, throw, throwThe,
    MonadExceptOf.throw, PredTrans.pushArg, PredTrans.pushExcept,
    PredTrans.pure, Id.run, PostCond.mayThrow, ExceptConds.true,
    ExceptConds.const]
  cases m s <;> trivial

namespace SMT.RenamingContext

/-- Generic structural renaming witness: `Δ₀`, left-biased over the canonical
context induced by the final type context `Γ'`, and over a dummy domain value
for any source variable in `extra` (the encoded `∀`-binder's free variables that
land in `B.Term.vars t` rather than in `Γ'`). -/
noncomputable def padWith (Δ₀ : Context) (Γ' : SMT.TypeContext)
    (extra : List SMT.𝒱) : Context :=
  fun v => match Δ₀ v with
    | some d => some d
    | none =>
      match ofTypeContext Γ' v with
      | some d => some d
      | none =>
        if v ∈ extra then
          some ⟨SMTType.int.defaultZFSet, SMTType.int,
            SMTType.mem_toZFSet_of_defaultZFSet⟩
        else none

end SMT.RenamingContext

/-- The structural `∃ Δ'` clause of `encodeTerm_struct`, discharged generically
from free-variable coverage of the encoded term by the final context together
with the `extra` source variables. -/
theorem encodeTerm_struct.renaming_witness
    {Δ₀ : SMT.RenamingContext.Context} {«Δ» : B.RenamingContext.Context}
    {t : B.Term} {Γ' : SMT.TypeContext} {t' : SMT.Term}
    {usedVars' used extra : List SMT.𝒱}
    (Δ₀_ext : SMT.RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» t)
    (Δ₀_none : ∀ v ∉ used, Δ₀ v = none)
    (used_sub : used ⊆ usedVars')
    (keys_sub : AList.keys Γ' ⊆ usedVars')
    (extra_sub : extra ⊆ usedVars')
    (fv_sub : SMT.fv t' ⊆ AList.keys Γ' ∪ extra) :
    ∃ (Δ' : SMT.RenamingContext.Context)
      (_ : SMT.RenamingContext.CoversFV Δ' t'),
      SMT.RenamingContext.Extends Δ' Δ₀ ∧
        SMT.RenamingContext.ExtendsOnSourceFV Δ' «Δ» t ∧
        (∀ v ∉ usedVars', Δ' v = none) := by
  refine ⟨SMT.RenamingContext.padWith Δ₀ Γ' extra, ?_, ?_, ?_, ?_⟩
  · -- CoversFV
    intro v hv
    simp only [SMT.RenamingContext.padWith]
    cases h : Δ₀ v with
    | some d => simp
    | none =>
      rcases List.mem_union_iff.mp (fv_sub hv) with hvΓ | hvextra
      · obtain ⟨τv, hτv⟩ := Option.isSome_iff_exists.mp
          ((AList.lookup_isSome).2 (AList.mem_keys.mp hvΓ))
        simp [SMT.RenamingContext.ofTypeContext, hτv]
      · cases hofc : SMT.RenamingContext.ofTypeContext Γ' v with
        | some d => simp
        | none => simp [hvextra]
  · -- Extends Δ' Δ₀
    intro v d h
    simp only [SMT.RenamingContext.padWith, h]
  · -- ExtendsOnSourceFV Δ' «Δ» t
    intro v d h
    have h0 : Δ₀ v = some d := Δ₀_ext h
    simp only [SMT.RenamingContext.padWith, h0]
  · -- none outside usedVars'
    intro v hv
    have hvu : v ∉ used := fun hu => hv (used_sub hu)
    have h0 : Δ₀ v = none := Δ₀_none v hvu
    have hvΓ : v ∉ Γ' := fun hg => hv (keys_sub (AList.mem_keys.mpr hg))
    have hvextra : v ∉ extra := fun he => hv (extra_sub he)
    have hlk : AList.lookup v Γ' = none := by
      rcases hl : AList.lookup v Γ' with _ | τ
      · rfl
      · exact absurd (AList.lookup_isSome.mp (by rw [hl]; rfl)) hvΓ
    simp only [SMT.RenamingContext.padWith, h0, SMT.RenamingContext.ofTypeContext, hlk,
      hvextra, if_false]

/-- If a type context's keys are covered by a used-variable list, inserting a
fresh key keeps the keys covered by the extended list. -/
theorem keys_insert_subset_cons {Γ : SMT.TypeContext} {v : SMT.𝒱} {τ : SMTType}
    {used : List SMT.𝒱} (hsub : AList.keys Γ ⊆ used) :
    AList.keys (Γ.insert v τ) ⊆ v :: used := by
  rw [AList.keys_insert]
  intro w hw
  rw [List.mem_cons] at hw ⊢
  rcases hw with rfl | hw
  · exact Or.inl rfl
  · exact Or.inr (hsub (List.mem_of_mem_erase hw))

/-! ### `declVars` — names declared by `declare_const` instructions

The `all` encoder scopes cast helpers as universal binders `ex_binders`, which
are obtained by `filterMap`-ping the `declare_const` instructions out of the
declarations delta produced while encoding the body + membership.  `declVars`
names exactly that set, so the `declarations`↔`fv` invariant of `encodeTerm`
(`encodeTerm_decl` below) and the cast-helper delta specs can be stated and
composed additively. -/

/-- Names introduced by `declare_const` instructions in a `Chunk`. -/
def declVars (decls : SMT.Chunk) : List SMT.𝒱 :=
  decls.filterMap fun
    | .declare_const v _ => some v
    | _ => none

@[simp] theorem declVars_nil : declVars [] = [] := rfl

@[simp] theorem declVars_append (a b : SMT.Chunk) :
    declVars (a ++ b) = declVars a ++ declVars b := by
  simp [declVars, List.filterMap_append]

@[simp] theorem declVars_concat (a : SMT.Chunk) (i : SMT.Instr) :
    declVars (a.concat i) = declVars a ++ declVars [i] := by
  rw [List.concat_eq_append, declVars_append]

@[simp] theorem declVars_declare_const (v : SMT.𝒱) (τ : SMTType) :
    declVars [.declare_const v τ] = [v] := rfl

@[simp] theorem declVars_define_fun (v : SMT.𝒱) (τ σ : SMTType) (t : SMT.Term) :
    declVars [.define_fun v τ σ t] = [] := rfl

theorem declVars_subset_of_isPrefix {a b : SMT.Chunk} (h : a <+: b) :
    declVars a ⊆ declVars b := by
  obtain ⟨c, rfl⟩ := h
  rw [declVars_append]
  exact fun v hv => List.mem_append_left _ hv

/-- The `define_fun … unit bool` bodies of a `Chunk`, as produced by `addSpec`. -/
def specBodies (decls : SMT.Chunk) : List SMT.Term :=
  decls.filterMap fun
    | .define_fun _ .unit .bool b => some b
    | _ => none

@[simp] theorem specBodies_nil : specBodies [] = [] := rfl

@[simp] theorem specBodies_append (a b : SMT.Chunk) :
    specBodies (a ++ b) = specBodies a ++ specBodies b := by
  simp [specBodies, List.filterMap_append]

@[simp] theorem specBodies_concat (a : SMT.Chunk) (i : SMT.Instr) :
    specBodies (a.concat i) = specBodies a ++ specBodies [i] := by
  rw [List.concat_eq_append, specBodies_append]

@[simp] theorem specBodies_declare_const (v : SMT.𝒱) (τ : SMTType) :
    specBodies [.declare_const v τ] = [] := rfl

@[simp] theorem mem_specBodies_define_fun {a : SMT.Chunk} {b : SMT.Term} :
    b ∈ specBodies a ↔ ∃ name, .define_fun name .unit .bool b ∈ a := by
  unfold specBodies
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨i, hi, heq⟩
    match i, heq with
    | .define_fun name .unit .bool b', h =>
      simp only [Option.some.injEq] at h
      exact ⟨name, h ▸ hi⟩
  · rintro ⟨name, hi⟩
    exact ⟨.define_fun name .unit .bool b, hi, rfl⟩

set_option maxHeartbeats 4000000 in
/-- Purely structural specification of `defaultSpecM`: it advances `freshvarsc`,
only grows `usedVars`, keeps `keys ⊆ usedVars`, preserves source variables, and
introduces no new free variables beyond those of the input term (all auxiliary
binders are quantified away). Proved by induction on the result type. -/
theorem defaultSpecM_state
    (τ : SMTType) {Λ : SMT.TypeContext} {n : ℕ}
    {used : List SMT.𝒱} {name : String} {t : SMT.Term} :
    ⦃ fun (⟨E, Λ'⟩ : EncoderState) ↦
        ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ AList.keys Λ ⊆ E.usedVars ∧ E.usedVars = used⌝ ⦄
    defaultSpecM name τ t
    ⦃ ⇓? (d : SMT.Term) (⟨E', Γ'⟩ : EncoderState) => ⌜
      n ≤ E'.freshvarsc ∧
      Λ ⊆ Γ' ∧
      used ⊆ E'.usedVars ∧
      AList.keys Γ' ⊆ E'.usedVars ∧
      (∀ v ∈ used, v ∉ Λ → v ∉ Γ') ∧
      SMT.fv d ⊆ SMT.fv t ⌝⦄ := by
  induction τ generalizing Λ n used name t with
  | int | bool =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl⟩ := pre
    unfold defaultSpecM
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨le_refl _, fun e he => he, fun v hv => hv, sub, fun v hv hΛ => hΛ, ?_⟩
    intro v hv
    simp only [SMT.fv, List.mem_append, List.not_mem_nil, or_false] at hv
    exact hv
  | unit =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl⟩ := pre
    unfold defaultSpecM
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨le_refl _, fun e he => he, fun v hv => hv, sub, fun v hv hΛ => hΛ, ?_⟩
    intro v hv
    simp only [SMT.fv, List.not_mem_nil] at hv
  | option σ _ih =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl⟩ := pre
    unfold defaultSpecM
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨le_refl _, fun e he => he, fun v hv => hv, sub, fun v hv hΛ => hΛ, ?_⟩
    intro v hv
    simp only [noneCast, SMT.fv, List.mem_append, List.not_mem_nil, or_false] at hv
    exact hv
  | pair σ ρ σ_ih ρ_ih =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl⟩ := pre
    unfold defaultSpecM
    mspec σ_ih
    mrename_i pre
    mintro ∀St₂
    mpure pre
    obtain ⟨fst_le, fst_Λ_sub, fst_used_sub, fst_keys_sub, fst_preserves, fst_fv_sub⟩ := pre
    mspec ρ_ih
    mrename_i pre
    mintro ∀St₃
    mpure pre
    obtain ⟨snd_le, snd_Λ_sub, snd_used_sub, snd_keys_sub, snd_preserves, snd_fv_sub⟩ := pre
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨le_trans fst_le snd_le, AList.subset_trans fst_Λ_sub snd_Λ_sub,
      fun v hv => snd_used_sub (fst_used_sub hv), snd_keys_sub, ?_, ?_⟩
    · intro v hv hΛ
      exact snd_preserves v (fst_used_sub hv) (fst_preserves v hv hΛ)
    · intro v hv
      simp only [SMT.fv, List.mem_append] at hv
      rcases hv with hv | hv
      · have := fst_fv_sub hv
        simp only [SMT.fv] at this
        exact this
      · have := snd_fv_sub hv
        simp only [SMT.fv] at this
        exact this
  | «fun» σ ρ _σ_ih ρ_ih =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl⟩ := pre
    unfold defaultSpecM
    mspec SMT.freshVar_spec
    mrename_i pre
    mintro ∀St₂
    mpure pre
    obtain ⟨St₂_types_eq, z_fresh, St₂_fvc, St₂_used_eq, z_not_used⟩ := pre
    have St₂_keys_sub : AList.keys St₂.types ⊆ St₂.env.usedVars := by
      rw [St₂_types_eq, St₂_used_eq]; exact keys_insert_subset_cons sub
    mspec (ρ_ih (Λ := St₂.types) (n := St₂.env.freshvarsc) (used := St₂.env.usedVars))
    mrename_i pre
    mintro ∀St₃
    mpure pre
    obtain ⟨body_le, body_Λ_sub, body_used_sub, body_keys_sub, body_preserves, body_fv_sub⟩ := pre
    rename_i z _
    have z_fresh' : z ∉ St.types := z_fresh
    mspec SMT.eraseFromContext_spec
    mrename_i preE
    mintro ∀StE
    mpure preE
    obtain ⟨StE_types_eq, StE_fvc, StE_used_eq⟩ := preE
    mspec Std.Do.Spec.pure
    mpure_intro
    rw [StE_types_eq, StE_fvc, StE_used_eq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · have h : St.env.freshvarsc ≤ St₂.env.freshvarsc := by omega
      exact le_trans h body_le
    · apply SMT.TypeContext.entries_subset_erase_of_notMem _ z_fresh'
      have hz : St₂.types ⊆ St₃.types := body_Λ_sub
      rw [St₂_types_eq] at hz
      exact AList.subset_trans
        (SMT.TypeContext.entries_subset_insert_of_notMem z_fresh) hz
    · intro v hv
      apply body_used_sub
      rw [St₂_used_eq]
      exact List.mem_cons_of_mem _ hv
    · exact fun v hv => body_keys_sub (SMT.TypeContext.keys_erase_subset hv)
    · intro v hv hΛ
      apply SMT.TypeContext.notMem_erase
      have hv_St₂ : v ∈ St₂.env.usedVars := by
        rw [St₂_used_eq]; exact List.mem_cons_of_mem _ hv
      have hv_ne_z : v ≠ z := fun h => z_not_used (h ▸ hv)
      apply body_preserves v hv_St₂
      rw [St₂_types_eq, AList.mem_insert]
      push_neg
      exact ⟨hv_ne_z, hΛ⟩
    · intro v hv
      simp only [SMT.fv, List.mem_removeAll_iff, List.mem_cons,
        List.not_mem_nil, or_false] at hv
      obtain ⟨hv_body, hv_ne_z⟩ := hv
      have hmem := body_fv_sub hv_body
      simp only [SMT.fv, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with hvt | hvz
      · exact hvt
      · exact absurd hvz hv_ne_z

/-- The structural postcondition shape of `loosenAux_prf`, abstracted so it can
be stated both as a goal and as an induction/recursion hypothesis. -/
abbrev LoosenAuxStatePost (β : SMTType) (Λ : SMT.TypeContext) (n : ℕ)
    (used : List SMT.𝒱) (x : SMT.Term) :
    PostCond (SMT.𝒱 × SMT.Term) (.arg EncoderState (.except String .pure)) :=
  ⇓? (⟨x!, x!_spec⟩ : SMT.𝒱 × SMT.Term) (⟨E', Γ'⟩ : EncoderState) => ⌜
    n ≤ E'.freshvarsc ∧
    Λ.insert x! β ⊆ Γ' ∧
    x! ∉ Λ ∧
    x! ∉ used ∧
    used ⊆ E'.usedVars ∧
    AList.keys Γ' ⊆ E'.usedVars ∧
    (∀ v ∈ used, v ∉ Λ → v ∉ Γ') ∧
    SMT.fv x!_spec ⊆ SMT.fv x ∪ {x!} ⌝

/-- The structural precondition shape of `loosenAux_prf`. -/
abbrev LoosenAuxStatePre (Λ : SMT.TypeContext) (n : ℕ) (used : List SMT.𝒱) :
    Assertion (.arg EncoderState (.except String .pure)) :=
  fun (⟨E, Λ'⟩ : EncoderState) ↦
    ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ AList.keys Λ ⊆ E.usedVars ∧ E.usedVars = used⌝

set_option maxHeartbeats 4000000 in
/-- The `pair` case of `loosenAux_prf_state`, factored out so it can be reused
both by the `pair` constructor and the `graph` constructor (whose inner
recursion is on a `castPath.pair`). Takes the structural specs of the component
cast paths as hypotheses. -/
theorem loosenAux_prf_state_pair
    {α β α' β' : SMTType} (pα : α ~> α') (pβ : β ~> β')
    (pα_ih : ∀ {Λ : SMT.TypeContext} {n : ℕ} {used : List SMT.𝒱} {name : String}
      {x : SMT.Term},
      Std.Do.Triple (loosenAux_prf name pα x)
        (LoosenAuxStatePre Λ n used) (LoosenAuxStatePost α' Λ n used x))
    (pβ_ih : ∀ {Λ : SMT.TypeContext} {n : ℕ} {used : List SMT.𝒱} {name : String}
      {x : SMT.Term},
      Std.Do.Triple (loosenAux_prf name pβ x)
        (LoosenAuxStatePre Λ n used) (LoosenAuxStatePost β' Λ n used x))
    {Λ : SMT.TypeContext} {n : ℕ} {used : List SMT.𝒱} {name : String}
    {x : SMT.Term} :
    Std.Do.Triple (loosenAux_prf name (castPath.pair pα pβ) x)
      (LoosenAuxStatePre Λ n used)
      (LoosenAuxStatePost (α'.pair β') Λ n used x) := by
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, sub, rfl⟩ := pre
  unfold loosenAux_prf
  mspec SMT.freshVar_spec
  mrename_i pre
  mintro ∀St₂
  mpure pre
  obtain ⟨St₂_types_eq, x!_fresh, St₂_fvc, St₂_used_eq, x!_not_used⟩ := pre
  have St₂_keys_sub : AList.keys St₂.types ⊆ St₂.env.usedVars := by
    rw [St₂_types_eq, St₂_used_eq]; exact keys_insert_subset_cons sub
  mspec (pα_ih (Λ := St₂.types) (n := St₂.env.freshvarsc) (used := St₂.env.usedVars))
  mrename_i pre
  mintro ∀St₃
  mpure pre
  obtain ⟨fst!_le, fst!_Λ_sub, fst!_fresh, fst!_not_used, fst!_used_sub,
    fst!_keys_sub, fst!_preserves, fst!_fv_sub⟩ := pre
  mspec (pβ_ih (Λ := St₃.types) (n := St₃.env.freshvarsc) (used := St₃.env.usedVars))
  mrename_i pre
  mintro ∀St₄
  mpure pre
  obtain ⟨snd!_le, snd!_Λ_sub, snd!_fresh, snd!_not_used, snd!_used_sub,
    snd!_keys_sub, snd!_preserves, snd!_fv_sub⟩ := pre
  rename_i x! fst_out snd_out
  obtain ⟨fst!, fst!_spec⟩ := fst_out
  obtain ⟨snd!, snd!_spec⟩ := snd_out
  -- freshness facts about the erased binders `fst!`, `snd!`
  have x!_in_St₂ : x! ∈ St₂.types := by rw [St₂_types_eq]; exact (AList.mem_insert _).mpr (Or.inl rfl)
  have St₂_sub_St₃ : St₂.types ⊆ St₃.types :=
    AList.subset_trans (SMT.TypeContext.entries_subset_insert_of_notMem fst!_fresh) fst!_Λ_sub
  have x!_in_St₃ : x! ∈ St₃.types := SMT.TypeContext.mem_of_entries_subset x!_in_St₂ St₂_sub_St₃
  have fst!_ne_x! : fst! ≠ x! := fun h => fst!_fresh (h ▸ x!_in_St₂)
  have fst!_notSt : fst! ∉ St.types := fun h => fst!_fresh (St₂_types_eq ▸ (AList.mem_insert _).mpr (Or.inr h))
  have snd!_ne_x! : snd! ≠ x! := fun h => snd!_fresh (h ▸ x!_in_St₃)
  have snd!_notSt : snd! ∉ St.types := fun h =>
    snd!_fresh (SMT.TypeContext.mem_of_entries_subset
      (St₂_types_eq ▸ (AList.mem_insert _).mpr (Or.inr h) : snd! ∈ St₂.types) St₂_sub_St₃)
  have fst!_notIns : fst! ∉ AList.insert x! (α'.pair β') St.types := by
    rw [AList.mem_insert]; push_neg; exact ⟨fst!_ne_x!, fst!_notSt⟩
  have snd!_notIns : snd! ∉ AList.insert x! (α'.pair β') St.types := by
    rw [AList.mem_insert]; push_neg; exact ⟨snd!_ne_x!, snd!_notSt⟩
  mspec SMT.eraseFromContext_spec
  mrename_i preE
  mintro ∀StE
  mpure preE
  obtain ⟨StE_types_eq, StE_fvc, StE_used_eq⟩ := preE
  mspec SMT.eraseFromContext_spec
  mrename_i preE2
  mintro ∀StE2
  mpure preE2
  obtain ⟨StE2_types_eq, StE2_fvc, StE2_used_eq⟩ := preE2
  mspec Std.Do.Spec.pure
  mpure_intro
  rw [StE2_types_eq, StE_types_eq, StE2_fvc, StE_fvc, StE2_used_eq, StE_used_eq]
  and_intros
  · have h₁ : St.env.freshvarsc ≤ St₂.env.freshvarsc := by omega
    exact le_trans h₁ (le_trans fst!_le snd!_le)
  · apply SMT.TypeContext.entries_subset_erase_of_notMem _ snd!_notIns
    apply SMT.TypeContext.entries_subset_erase_of_notMem _ fst!_notIns
    have hf : St₂.types ⊆ AList.insert fst! α' St₂.types :=
      SMT.TypeContext.entries_subset_insert_of_notMem fst!_fresh
    have hs : St₃.types ⊆ AList.insert snd! β' St₃.types :=
      SMT.TypeContext.entries_subset_insert_of_notMem snd!_fresh
    have h₃ : AList.insert x! (α'.pair β') St.types ⊆ St₄.types := by
      rw [← St₂_types_eq]
      exact AList.subset_trans hf (AList.subset_trans fst!_Λ_sub
        (AList.subset_trans hs snd!_Λ_sub))
    exact h₃
  · exact x!_fresh
  · exact x!_not_used
  · intro v hv
    apply snd!_used_sub
    apply fst!_used_sub
    rw [St₂_used_eq]
    exact List.mem_cons_of_mem _ hv
  · exact fun v hv => snd!_keys_sub (SMT.TypeContext.keys_erase_subset
      (SMT.TypeContext.keys_erase_subset hv))
  · intro v hv hv_not_St
    apply SMT.TypeContext.notMem_erase
    apply SMT.TypeContext.notMem_erase
    have hv_St₂ : v ∈ St₂.env.usedVars := by
      rw [St₂_used_eq]; exact List.mem_cons_of_mem _ hv
    have hv_St₃ : v ∈ St₃.env.usedVars := fst!_used_sub hv_St₂
    have hv_ne_x! : v ≠ x! := fun h => x!_not_used (h ▸ hv)
    have hv_not_St₂ : v ∉ St₂.types := by
      rw [St₂_types_eq, AList.mem_insert]
      push_neg
      exact ⟨hv_ne_x!, hv_not_St⟩
    have hv_not_St₃ : v ∉ St₃.types := fst!_preserves v hv_St₂ hv_not_St₂
    exact snd!_preserves v hv_St₃ hv_not_St₃
  · intro v hv
    simp only [SMT.fv, List.mem_append, List.mem_removeAll_iff,
      List.mem_cons, List.not_mem_nil, or_false] at hv
    rw [List.mem_union_iff]
    obtain ⟨hv_body, hv_ne_fstsnd⟩ := hv
    have hv_ne_fst! : v ≠ fst! := fun h => hv_ne_fstsnd (Or.inl h)
    have hv_ne_snd! : v ≠ snd! := fun h => hv_ne_fstsnd (Or.inr h)
    rcases hv_body with (hvx! | hvfst! | hvsnd!) | (hvfspec | hvsspec)
    · exact Or.inr (List.mem_singleton.mpr hvx!)
    · exact absurd hvfst! hv_ne_fst!
    · exact absurd hvsnd! hv_ne_snd!
    · have hmem := fst!_fv_sub hvfspec
      rw [List.mem_union_iff] at hmem
      rcases hmem with hx | hgv
      · simp only [SMT.fv] at hx; exact Or.inl hx
      · exact absurd (List.mem_singleton.mp hgv) hv_ne_fst!
    · have hmem := snd!_fv_sub hvsspec
      rw [List.mem_union_iff] at hmem
      rcases hmem with hx | hs!
      · simp only [SMT.fv] at hx; exact Or.inl hx
      · exact absurd (List.mem_singleton.mp hs!) hv_ne_snd!

set_option maxHeartbeats 4000000 in
/-- Purely structural specification of `loosenAux_prf` (no `B`-typing, no
`respects`, no denotation): the loosening introduces a fresh head variable `x!`
of type `β`, advances `freshvarsc`, only grows `usedVars`, keeps `keys ⊆
usedVars`, preserves source variables, and the spec term's free variables stay
within `fv x ∪ {x!}`. Proved by induction on the cast path. -/
theorem loosenAux_prf_state
    {α β : SMTType} (c : α ~> β) {Λ : SMT.TypeContext} {n : ℕ}
    {used : List SMT.𝒱} {name : String} {x : SMT.Term} :
    Std.Do.Triple (loosenAux_prf name c x)
      (LoosenAuxStatePre Λ n used)
      (LoosenAuxStatePost β Λ n used x) := by
  induction c generalizing Λ n used name x with
  | @refl α hα =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl⟩ := pre
    unfold loosenAux_prf
    mspec SMT.freshVar_spec
    mrename_i pre
    mintro ∀St₂
    mpure pre
    obtain ⟨St₂_types_eq, x!_fresh, St₂_fvc, St₂_used_eq, x!_not_used⟩ := pre
    mspec Std.Do.Spec.pure
    mpure_intro
    and_intros
    · rw [St₂_fvc]; exact Nat.le_succ _
    · rw [St₂_types_eq]
    · exact x!_fresh
    · exact x!_not_used
    · rw [St₂_used_eq]; intro v hv; exact List.mem_cons_of_mem _ hv
    · rw [St₂_types_eq, St₂_used_eq, AList.keys_insert]
      intro v hv
      rw [List.mem_cons] at hv ⊢
      rcases hv with rfl | hv
      · exact Or.inl rfl
      · exact Or.inr (sub (List.mem_of_mem_erase hv))
    · intro v hv hv_not_Λ
      rw [St₂_types_eq, AList.mem_insert]
      push_neg
      exact ⟨fun h => absurd (h ▸ hv) x!_not_used, hv_not_Λ⟩
    · rw [SMT.fv, SMT.fv]
      intro v hv
      rw [List.cons_append, List.nil_append, List.mem_cons] at hv
      rw [List.mem_union_iff]
      rcases hv with rfl | hv
      · exact Or.inr (List.mem_singleton.mpr rfl)
      · exact Or.inl hv
  | @graph α β α' β' pα pβ pα_ih pβ_ih =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl⟩ := pre
    unfold loosenAux_prf
    mspec SMT.freshVar_spec
    mrename_i pre
    mintro ∀St₂
    mpure pre
    obtain ⟨St₂_types_eq, x!_fresh, St₂_fvc, St₂_used_eq, x!_not_used⟩ := pre
    mspec SMT.freshVar_spec
    mrename_i pre
    mintro ∀St₃
    mpure pre
    obtain ⟨St₃_types_eq, z_fresh, St₃_fvc, St₃_used_eq, z_not_used⟩ := pre
    have St₂_keys_sub : AList.keys St₂.types ⊆ St₂.env.usedVars := by
      rw [St₂_types_eq, St₂_used_eq]; exact keys_insert_subset_cons sub
    have St₃_keys_sub : AList.keys St₃.types ⊆ St₃.env.usedVars := by
      rw [St₃_types_eq, St₃_used_eq]; exact keys_insert_subset_cons St₂_keys_sub
    mspec (loosenAux_prf_state_pair pα pβ pα_ih pβ_ih
      (Λ := St₃.types) (n := St₃.env.freshvarsc) (used := St₃.env.usedVars))
    mrename_i pre
    mintro ∀St₄
    mpure pre
    obtain ⟨z!_le, z!_Λ_sub, z!_fresh, z!_not_used, z!_used_sub,
      z!_keys_sub, z!_preserves, z!_fv_sub⟩ := pre
    rename_i x! z out
    obtain ⟨z!, z!_spec⟩ := out
    -- freshness facts about the erased binders `z`, `z!`
    have St₂_sub_St₃ : St₂.types ⊆ St₃.types := by
      rw [St₃_types_eq]; exact SMT.TypeContext.entries_subset_insert_of_notMem z_fresh
    have x!_in_St₂ : x! ∈ St₂.types := by rw [St₂_types_eq]; exact (AList.mem_insert _).mpr (Or.inl rfl)
    have x!_in_St₃ : x! ∈ St₃.types := SMT.TypeContext.mem_of_entries_subset x!_in_St₂ St₂_sub_St₃
    have z_ne_x! : z ≠ x! := fun h => z_fresh (h ▸ x!_in_St₂)
    have z_notSt : z ∉ St.types := fun h =>
      z_fresh (St₂_types_eq ▸ (AList.mem_insert _).mpr (Or.inr h))
    have z!_ne_x! : z! ≠ x! := fun h => z!_fresh (h ▸ x!_in_St₃)
    have z!_notSt : z! ∉ St.types := fun h =>
      z!_fresh (SMT.TypeContext.mem_of_entries_subset
        (St₂_types_eq ▸ (AList.mem_insert _).mpr (Or.inr h) : z! ∈ St₂.types) St₂_sub_St₃)
    have z_notIns : z ∉ AList.insert x! ((α'.pair β').fun SMTType.bool) St.types := by
      rw [AList.mem_insert]; push_neg; exact ⟨z_ne_x!, z_notSt⟩
    have z!_notIns : z! ∉ AList.insert x! ((α'.pair β').fun SMTType.bool) St.types := by
      rw [AList.mem_insert]; push_neg; exact ⟨z!_ne_x!, z!_notSt⟩
    mspec SMT.eraseFromContext_spec
    mrename_i preE
    mintro ∀StE
    mpure preE
    obtain ⟨StE_types_eq, StE_fvc, StE_used_eq⟩ := preE
    mspec SMT.eraseFromContext_spec
    mrename_i preE2
    mintro ∀StE2
    mpure preE2
    obtain ⟨StE2_types_eq, StE2_fvc, StE2_used_eq⟩ := preE2
    mspec Std.Do.Spec.pure
    mpure_intro
    rw [StE2_types_eq, StE_types_eq, StE2_fvc, StE_fvc, StE2_used_eq, StE_used_eq]
    and_intros
    · have h : St.env.freshvarsc ≤ St₃.env.freshvarsc := by omega
      exact le_trans h z!_le
    · apply SMT.TypeContext.entries_subset_erase_of_notMem _ z!_notIns
      apply SMT.TypeContext.entries_subset_erase_of_notMem _ z_notIns
      have h₁ : St₂.types ⊆ St₃.types := St₂_sub_St₃
      have h₂ : St₃.types ⊆ AList.insert z! (α'.pair β') St₃.types :=
        SMT.TypeContext.entries_subset_insert_of_notMem z!_fresh
      rw [St₂_types_eq] at h₁
      exact AList.subset_trans h₁ (AList.subset_trans h₂ z!_Λ_sub)
    · exact x!_fresh
    · exact x!_not_used
    · intro v hv
      apply z!_used_sub
      rw [St₃_used_eq, St₂_used_eq]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hv)
    · exact fun v hv => z!_keys_sub (SMT.TypeContext.keys_erase_subset
        (SMT.TypeContext.keys_erase_subset hv))
    · intro v hv hv_not_St
      apply SMT.TypeContext.notMem_erase
      apply SMT.TypeContext.notMem_erase
      have hv_St₃ : v ∈ St₃.env.usedVars := by
        rw [St₃_used_eq, St₂_used_eq]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hv)
      have hv_ne_x! : v ≠ x! := fun h => x!_not_used (h ▸ hv)
      have hv_ne_z : v ≠ z := fun h => z_not_used (h ▸ (St₂_used_eq ▸ List.mem_cons_of_mem _ hv))
      apply z!_preserves v hv_St₃
      rw [St₃_types_eq, St₂_types_eq, AList.mem_insert, AList.mem_insert]
      push_neg
      exact ⟨hv_ne_z, hv_ne_x!, hv_not_St⟩
    · intro v hv
      simp only [SMT.fv, List.mem_append, List.mem_removeAll_iff,
        List.mem_cons, List.not_mem_nil, or_false] at hv
      rw [List.mem_union_iff]
      rcases hv with hv | ⟨⟨hv_body, hv_ne_z⟩, hv_ne_z!⟩
      · exact Or.inr (List.mem_singleton.mpr hv)
      · rcases hv_body with ((hvx | hvz) | hvz') | hvspec
        · exact Or.inl hvx
        · exact absurd hvz hv_ne_z
        · exact absurd hvz' hv_ne_z
        · have hmem := z!_fv_sub hvspec
          rw [List.mem_union_iff] at hmem
          rcases hmem with hz | hz!
          · simp only [SMT.fv, List.mem_singleton] at hz
            exact absurd hz hv_ne_z
          · exact absurd (List.mem_singleton.mp hz!) hv_ne_z!
  | @chpred α α' p ih =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl⟩ := pre
    unfold loosenAux_prf
    mspec SMT.freshVar_spec
    mrename_i pre
    mintro ∀St₂
    mpure pre
    obtain ⟨St₂_types_eq, x!_fresh, St₂_fvc, St₂_used_eq, x!_not_used⟩ := pre
    mspec SMT.freshVar_spec
    mrename_i pre
    mintro ∀St₃
    mpure pre
    obtain ⟨St₃_types_eq, z_fresh, St₃_fvc, St₃_used_eq, z_not_used⟩ := pre
    have St₂_keys_sub : AList.keys St₂.types ⊆ St₂.env.usedVars := by
      rw [St₂_types_eq, St₂_used_eq]; exact keys_insert_subset_cons sub
    have St₃_keys_sub : AList.keys St₃.types ⊆ St₃.env.usedVars := by
      rw [St₃_types_eq, St₃_used_eq]; exact keys_insert_subset_cons St₂_keys_sub
    mspec (ih (Λ := St₃.types) (n := St₃.env.freshvarsc) (used := St₃.env.usedVars))
    mrename_i pre
    mintro ∀St₄
    mpure pre
    obtain ⟨z!_le, z!_Λ_sub, z!_fresh, z!_not_used, z!_used_sub,
      z!_keys_sub, z!_preserves, z!_fv_sub⟩ := pre
    rename_i x! z out
    obtain ⟨z!, z!_spec⟩ := out
    -- freshness facts about the erased binders `z`, `z!`
    have St₂_sub_St₃ : St₂.types ⊆ St₃.types := by
      rw [St₃_types_eq]; exact SMT.TypeContext.entries_subset_insert_of_notMem z_fresh
    have x!_in_St₂ : x! ∈ St₂.types := by rw [St₂_types_eq]; exact (AList.mem_insert _).mpr (Or.inl rfl)
    have x!_in_St₃ : x! ∈ St₃.types := SMT.TypeContext.mem_of_entries_subset x!_in_St₂ St₂_sub_St₃
    have z_ne_x! : z ≠ x! := fun h => z_fresh (h ▸ x!_in_St₂)
    have z_notSt : z ∉ St.types := fun h =>
      z_fresh (St₂_types_eq ▸ (AList.mem_insert _).mpr (Or.inr h))
    have z!_ne_x! : z! ≠ x! := fun h => z!_fresh (h ▸ x!_in_St₃)
    have z!_notSt : z! ∉ St.types := fun h =>
      z!_fresh (SMT.TypeContext.mem_of_entries_subset
        (St₂_types_eq ▸ (AList.mem_insert _).mpr (Or.inr h) : z! ∈ St₂.types) St₂_sub_St₃)
    have z_notIns : z ∉ AList.insert x! (α'.fun SMTType.bool) St.types := by
      rw [AList.mem_insert]; push_neg; exact ⟨z_ne_x!, z_notSt⟩
    have z!_notIns : z! ∉ AList.insert x! (α'.fun SMTType.bool) St.types := by
      rw [AList.mem_insert]; push_neg; exact ⟨z!_ne_x!, z!_notSt⟩
    mspec SMT.eraseFromContext_spec
    mrename_i preE
    mintro ∀StE
    mpure preE
    obtain ⟨StE_types_eq, StE_fvc, StE_used_eq⟩ := preE
    mspec SMT.eraseFromContext_spec
    mrename_i preE2
    mintro ∀StE2
    mpure preE2
    obtain ⟨StE2_types_eq, StE2_fvc, StE2_used_eq⟩ := preE2
    mspec Std.Do.Spec.pure
    mpure_intro
    rw [StE2_types_eq, StE_types_eq, StE2_fvc, StE_fvc, StE2_used_eq, StE_used_eq]
    and_intros
    · have : St.env.freshvarsc ≤ St₃.env.freshvarsc := by omega
      exact le_trans this z!_le
    · apply SMT.TypeContext.entries_subset_erase_of_notMem _ z!_notIns
      apply SMT.TypeContext.entries_subset_erase_of_notMem _ z_notIns
      have h₁ : St₂.types ⊆ St₃.types := St₂_sub_St₃
      have h₂ : St₃.types ⊆ AList.insert z! α' St₃.types :=
        SMT.TypeContext.entries_subset_insert_of_notMem z!_fresh
      rw [St₂_types_eq] at h₁
      exact AList.subset_trans h₁ (AList.subset_trans h₂ z!_Λ_sub)
    · exact x!_fresh
    · exact x!_not_used
    · intro v hv
      apply z!_used_sub
      rw [St₃_used_eq, St₂_used_eq]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hv)
    · exact fun v hv => z!_keys_sub (SMT.TypeContext.keys_erase_subset
        (SMT.TypeContext.keys_erase_subset hv))
    · intro v hv hv_not_St
      apply SMT.TypeContext.notMem_erase
      apply SMT.TypeContext.notMem_erase
      have hv_St₃ : v ∈ St₃.env.usedVars := by
        rw [St₃_used_eq, St₂_used_eq]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hv)
      have hv_ne_x! : v ≠ x! := fun h => x!_not_used (h ▸ hv)
      have hv_ne_z : v ≠ z := fun h => z_not_used (h ▸ (St₂_used_eq ▸ List.mem_cons_of_mem _ hv))
      apply z!_preserves v hv_St₃
      rw [St₃_types_eq, St₂_types_eq, AList.mem_insert, AList.mem_insert]
      push_neg
      exact ⟨hv_ne_z, hv_ne_x!, hv_not_St⟩
    · intro v hv
      simp only [SMT.fv, List.mem_append, List.mem_removeAll_iff,
        List.mem_cons, List.not_mem_nil, or_false] at hv
      rw [List.mem_union_iff]
      rcases hv with hv | ⟨⟨⟨hv_body, hv_ne_z⟩, hv_ne_z!⟩⟩
      · exact Or.inr (List.mem_singleton.mpr hv)
      · rcases hv_body with (hvx | hvz) | hvspec
        · exact Or.inl hvx
        · exact absurd hvz hv_ne_z
        · have hmem := z!_fv_sub hvspec
          rw [List.mem_union_iff] at hmem
          rcases hmem with hz | hz!
          · simp only [SMT.fv, List.mem_singleton] at hz
            exact absurd hz hv_ne_z
          · exact absurd (List.mem_singleton.mp hz!) hv_ne_z!
  | @«fun» α β α' β' hβ pα pβ pα_ih pβ_ih =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl⟩ := pre
    unfold loosenAux_prf
    mspec SMT.freshVar_spec
    mrename_i pre
    mintro ∀St₂
    mpure pre
    obtain ⟨St₂_types_eq, x!_fresh, St₂_fvc, St₂_used_eq, x!_not_used⟩ := pre
    have St₂_keys_sub : AList.keys St₂.types ⊆ St₂.env.usedVars := by
      rw [St₂_types_eq, St₂_used_eq]; exact keys_insert_subset_cons sub
    mspec SMT.freshVar_spec
    mrename_i pre
    mintro ∀St₃
    mpure pre
    obtain ⟨St₃_types_eq, a_fresh, St₃_fvc, St₃_used_eq, a_not_used⟩ := pre
    have St₃_keys_sub : AList.keys St₃.types ⊆ St₃.env.usedVars := by
      rw [St₃_types_eq, St₃_used_eq]; exact keys_insert_subset_cons St₂_keys_sub
    mspec (pα_ih (Λ := St₃.types) (n := St₃.env.freshvarsc) (used := St₃.env.usedVars))
    mrename_i pre
    mintro ∀St₄
    mpure pre
    obtain ⟨a!_le, a!_Λ_sub, a!_fresh, a!_not_used, a!_used_sub,
      a!_keys_sub, a!_preserves, a!_fv_sub⟩ := pre
    mspec SMT.freshVar_spec
    mrename_i pre
    mintro ∀St₅
    mpure pre
    obtain ⟨St₅_types_eq, b_fresh, St₅_fvc, St₅_used_eq, b_not_used⟩ := pre
    have St₅_keys_sub : AList.keys St₅.types ⊆ St₅.env.usedVars := by
      rw [St₅_types_eq, St₅_used_eq]; exact keys_insert_subset_cons a!_keys_sub
    mspec (pβ_ih (Λ := St₅.types) (n := St₅.env.freshvarsc) (used := St₅.env.usedVars))
    mrename_i pre
    mintro ∀St₆
    mpure pre
    obtain ⟨b!_le, b!_Λ_sub, b!_fresh, b!_not_used, b!_used_sub,
      b!_keys_sub, b!_preserves, b!_fv_sub⟩ := pre
    mspec (defaultSpecM_state β' (Λ := St₆.types) (n := St₆.env.freshvarsc)
      (used := St₆.env.usedVars))
    mrename_i pre
    mintro ∀St₇
    mpure pre
    obtain ⟨hd_le, hd_Λ_sub, hd_used_sub, hd_keys_sub, hd_preserves, hd_fv_sub⟩ := pre
    rename_i x! a a_out b b_out _hdefault
    obtain ⟨a!, a!_spec⟩ := a_out
    obtain ⟨b!, b!_spec⟩ := b_out
    -- the subset chain `St.types ⊆ ... ⊆ St₆.types`, reused below
    have h23 : St₂.types ⊆ St₃.types := by
      rw [St₃_types_eq]; exact SMT.TypeContext.entries_subset_insert_of_notMem a_fresh
    have h34 : St₃.types ⊆ St₄.types :=
      AList.subset_trans (SMT.TypeContext.entries_subset_insert_of_notMem a!_fresh) a!_Λ_sub
    have h45 : St₄.types ⊆ St₅.types := by
      rw [St₅_types_eq]; exact SMT.TypeContext.entries_subset_insert_of_notMem b_fresh
    have h56 : St₅.types ⊆ St₆.types :=
      AList.subset_trans (SMT.TypeContext.entries_subset_insert_of_notMem b!_fresh) b!_Λ_sub
    have x!_in_St₂ : x! ∈ St₂.types := by rw [St₂_types_eq]; exact (AList.mem_insert _).mpr (Or.inl rfl)
    have St_sub_St₂ : St.types ⊆ St₂.types := by
      rw [St₂_types_eq]; exact SMT.TypeContext.entries_subset_insert_of_notMem x!_fresh
    have x!_in_St₃ : x! ∈ St₃.types := SMT.TypeContext.mem_of_entries_subset x!_in_St₂ h23
    have x!_in_St₄ : x! ∈ St₄.types := SMT.TypeContext.mem_of_entries_subset x!_in_St₃ h34
    have x!_in_St₅ : x! ∈ St₅.types := SMT.TypeContext.mem_of_entries_subset x!_in_St₄ h45
    -- freshness facts about the four erased binders `a`, `a!`, `b`, `b!`
    have a_ne_x! : a ≠ x! := fun h => a_fresh (h ▸ x!_in_St₂)
    have a_notSt : a ∉ St.types := fun h =>
      a_fresh (SMT.TypeContext.mem_of_entries_subset h St_sub_St₂)
    have a!_ne_x! : a! ≠ x! := fun h => a!_fresh (h ▸ x!_in_St₃)
    have a!_notSt : a! ∉ St.types := fun h =>
      a!_fresh (SMT.TypeContext.mem_of_entries_subset
        (SMT.TypeContext.mem_of_entries_subset h St_sub_St₂) h23)
    have b_ne_x! : b ≠ x! := fun h => b_fresh (h ▸ x!_in_St₄)
    have b_notSt : b ∉ St.types := fun h =>
      b_fresh (SMT.TypeContext.mem_of_entries_subset
        (SMT.TypeContext.mem_of_entries_subset
          (SMT.TypeContext.mem_of_entries_subset h St_sub_St₂) h23) h34)
    have b!_ne_x! : b! ≠ x! := fun h => b!_fresh (h ▸ x!_in_St₅)
    have b!_notSt : b! ∉ St.types := fun h =>
      b!_fresh (SMT.TypeContext.mem_of_entries_subset
        (SMT.TypeContext.mem_of_entries_subset
          (SMT.TypeContext.mem_of_entries_subset
            (SMT.TypeContext.mem_of_entries_subset h St_sub_St₂) h23) h34) h45)
    have a_notIns : a ∉ AList.insert x! (α'.fun β') St.types := by
      rw [AList.mem_insert]; push_neg; exact ⟨a_ne_x!, a_notSt⟩
    have a!_notIns : a! ∉ AList.insert x! (α'.fun β') St.types := by
      rw [AList.mem_insert]; push_neg; exact ⟨a!_ne_x!, a!_notSt⟩
    have b_notIns : b ∉ AList.insert x! (α'.fun β') St.types := by
      rw [AList.mem_insert]; push_neg; exact ⟨b_ne_x!, b_notSt⟩
    have b!_notIns : b! ∉ AList.insert x! (α'.fun β') St.types := by
      rw [AList.mem_insert]; push_neg; exact ⟨b!_ne_x!, b!_notSt⟩
    mspec SMT.eraseFromContext_spec
    mrename_i preE
    mintro ∀StE
    mpure preE
    obtain ⟨StE_types_eq, StE_fvc, StE_used_eq⟩ := preE
    mspec SMT.eraseFromContext_spec
    mrename_i preE2
    mintro ∀StE2
    mpure preE2
    obtain ⟨StE2_types_eq, StE2_fvc, StE2_used_eq⟩ := preE2
    mspec SMT.eraseFromContext_spec
    mrename_i preE3
    mintro ∀StE3
    mpure preE3
    obtain ⟨StE3_types_eq, StE3_fvc, StE3_used_eq⟩ := preE3
    mspec SMT.eraseFromContext_spec
    mrename_i preE4
    mintro ∀StE4
    mpure preE4
    obtain ⟨StE4_types_eq, StE4_fvc, StE4_used_eq⟩ := preE4
    mspec Std.Do.Spec.pure
    mpure_intro
    rw [StE4_types_eq, StE3_types_eq, StE2_types_eq, StE_types_eq,
      StE4_fvc, StE3_fvc, StE2_fvc, StE_fvc,
      StE4_used_eq, StE3_used_eq, StE2_used_eq, StE_used_eq]
    and_intros
    · have h : St.env.freshvarsc ≤ St₃.env.freshvarsc := by omega
      exact le_trans h (le_trans a!_le (le_trans (by omega : St₄.env.freshvarsc ≤
        St₅.env.freshvarsc) (le_trans b!_le hd_le)))
    · apply SMT.TypeContext.entries_subset_erase_of_notMem _ b!_notIns
      apply SMT.TypeContext.entries_subset_erase_of_notMem _ b_notIns
      apply SMT.TypeContext.entries_subset_erase_of_notMem _ a!_notIns
      apply SMT.TypeContext.entries_subset_erase_of_notMem _ a_notIns
      have h₃ : AList.insert x! (α'.fun β') St.types ⊆ St₇.types := by
        rw [← St₂_types_eq]
        exact AList.subset_trans h23 (AList.subset_trans h34 (AList.subset_trans h45
          (AList.subset_trans h56 hd_Λ_sub)))
      exact h₃
    · exact x!_fresh
    · exact x!_not_used
    · intro v hv
      apply hd_used_sub
      apply b!_used_sub
      rw [St₅_used_eq]
      apply List.mem_cons_of_mem
      apply a!_used_sub
      rw [St₃_used_eq]
      apply List.mem_cons_of_mem
      rw [St₂_used_eq]
      exact List.mem_cons_of_mem _ hv
    · exact fun v hv => hd_keys_sub (SMT.TypeContext.keys_erase_subset
        (SMT.TypeContext.keys_erase_subset (SMT.TypeContext.keys_erase_subset
          (SMT.TypeContext.keys_erase_subset hv))))
    · intro v hv hv_not_St
      apply SMT.TypeContext.notMem_erase
      apply SMT.TypeContext.notMem_erase
      apply SMT.TypeContext.notMem_erase
      apply SMT.TypeContext.notMem_erase
      have hv_St₂ : v ∈ St₂.env.usedVars := by
        rw [St₂_used_eq]; exact List.mem_cons_of_mem _ hv
      have hv_St₃ : v ∈ St₃.env.usedVars := by
        rw [St₃_used_eq]; exact List.mem_cons_of_mem _ hv_St₂
      have hv_ne_x! : v ≠ x! := fun h => x!_not_used (h ▸ hv)
      have hv_ne_a : v ≠ a := fun h => a_not_used (h ▸ hv_St₂)
      have hv_not_St₂ : v ∉ St₂.types := by
        rw [St₂_types_eq, AList.mem_insert]
        push_neg
        exact ⟨hv_ne_x!, hv_not_St⟩
      have hv_not_St₃ : v ∉ St₃.types := by
        rw [St₃_types_eq, AList.mem_insert]
        push_neg
        exact ⟨hv_ne_a, hv_not_St₂⟩
      have hv_St₄ : v ∈ St₄.env.usedVars := a!_used_sub hv_St₃
      have hv_not_St₄ : v ∉ St₄.types := a!_preserves v hv_St₃ hv_not_St₃
      have hv_St₅ : v ∈ St₅.env.usedVars := by
        rw [St₅_used_eq]; exact List.mem_cons_of_mem _ hv_St₄
      have hv_ne_b : v ≠ b := fun h => b_not_used (h ▸ hv_St₄)
      have hv_not_St₅ : v ∉ St₅.types := by
        rw [St₅_types_eq, AList.mem_insert]
        push_neg
        exact ⟨hv_ne_b, hv_not_St₄⟩
      have hv_St₆ : v ∈ St₆.env.usedVars := b!_used_sub hv_St₅
      have hv_not_St₆ : v ∉ St₆.types := b!_preserves v hv_St₅ hv_not_St₅
      exact hd_preserves v hv_St₆ hv_not_St₆
    · intro v hv
      simp only [SMT.fv, List.mem_removeAll_iff, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false] at hv
      rw [List.mem_union_iff]
      obtain ⟨hv_body, hv_ne_a!⟩ := hv
      rcases hv_body with (hv_c | hv_t') | hv_e
      · -- v ∈ fv (∃[a][α] a!_spec)
        obtain ⟨hv_aspec, hv_ne_a⟩ := hv_c
        have hmem := a!_fv_sub hv_aspec
        rw [List.mem_union_iff] at hmem
        rcases hmem with ha | ha!
        · simp only [SMT.fv, List.mem_singleton] at ha
          exact absurd ha hv_ne_a
        · exact absurd (List.mem_singleton.mp ha!) hv_ne_a!
      · -- v ∈ fv (forall [b!][β'] body)
        obtain ⟨hv_bodyt, hv_ne_b!⟩ := hv_t'
        rcases hv_bodyt with ((hvx! | hva!) | hvb!) | hv_inner
        · exact Or.inr (List.mem_singleton.mpr hvx!)
        · exact absurd hva! hv_ne_a!
        · exact absurd hvb! hv_ne_b!
        · obtain ⟨hv_inner_body, hv_ne_ab⟩ := hv_inner
          have hv_ne_a : v ≠ a := fun h => hv_ne_ab (Or.inl h)
          have hv_ne_b : v ≠ b := fun h => hv_ne_ab (Or.inr h)
          rcases hv_inner_body with ((hvx | hva) | hvb) | (hvaspec | hvbspec)
          · exact Or.inl hvx
          · exact absurd hva hv_ne_a
          · exact absurd hvb hv_ne_b
          · have hmem := a!_fv_sub hvaspec
            rw [List.mem_union_iff] at hmem
            rcases hmem with ha | ha!
            · simp only [SMT.fv, List.mem_singleton] at ha
              exact absurd ha hv_ne_a
            · exact absurd (List.mem_singleton.mp ha!) hv_ne_a!
          · have hmem := b!_fv_sub hvbspec
            rw [List.mem_union_iff] at hmem
            rcases hmem with hb | hb!
            · simp only [SMT.fv, List.mem_singleton] at hb
              exact absurd hb hv_ne_b
            · exact absurd (List.mem_singleton.mp hb!) hv_ne_b!
      · -- v ∈ fv hdefault
        have hmem := hd_fv_sub hv_e
        simp only [SMT.fv, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with hvx! | hva!
        · exact Or.inr (List.mem_singleton.mpr hvx!)
        · exact absurd hva! hv_ne_a!
  | @pair α β α' β' pα pβ pα_ih pβ_ih =>
    exact loosenAux_prf_state_pair pα pβ pα_ih pβ_ih
  | @opt α α' p ih =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl⟩ := pre
    unfold loosenAux_prf
    mspec SMT.freshVar_spec
    mrename_i pre
    mintro ∀St₂
    mpure pre
    obtain ⟨St₂_types_eq, x!_fresh, St₂_fvc, St₂_used_eq, x!_not_used⟩ := pre
    have St₂_keys_sub : AList.keys St₂.types ⊆ St₂.env.usedVars := by
      rw [St₂_types_eq, St₂_used_eq]; exact keys_insert_subset_cons sub
    split
    · -- x = none
      rename_i x!
      mspec Std.Do.Spec.pure
      mpure_intro
      and_intros
      · rw [St₂_fvc]; exact Nat.le_succ _
      · rw [St₂_types_eq]
      · exact x!_fresh
      · exact x!_not_used
      · rw [St₂_used_eq]; intro v hv; exact List.mem_cons_of_mem _ hv
      · exact St₂_keys_sub
      · intro v hv hv_not_St
        rw [St₂_types_eq, AList.mem_insert]
        push_neg
        exact ⟨fun h => absurd (h ▸ hv) x!_not_used, hv_not_St⟩
      · intro v hv
        rw [List.mem_union_iff]
        refine Or.inr (List.mem_singleton.mpr ?_)
        simpa only [noneCast, SMT.fv, List.mem_append, List.not_mem_nil, or_false,
          List.mem_singleton] using hv
    · -- x = some x₀
      rename_i x! x₀
      mspec (ih (Λ := St₂.types) (n := St₂.env.freshvarsc) (used := St₂.env.usedVars))
      mrename_i pre
      mintro ∀St₃
      mpure pre
      obtain ⟨w!_le, w!_Λ_sub, w!_fresh, w!_not_used, w!_used_sub,
        w!_keys_sub, w!_preserves, w!_fv_sub⟩ := pre
      rename_i out
      obtain ⟨w!, w!_spec⟩ := out
      -- freshness facts about the erased binder `w!`
      have x!_in_St₂ : x! ∈ St₂.types := by rw [St₂_types_eq]; exact (AList.mem_insert _).mpr (Or.inl rfl)
      have w!_ne_x! : w! ≠ x! := fun h => w!_fresh (h ▸ x!_in_St₂)
      have w!_notSt : w! ∉ St.types := fun h =>
        w!_fresh (St₂_types_eq ▸ (AList.mem_insert _).mpr (Or.inr h))
      have w!_notIns : w! ∉ AList.insert x! α'.option St.types := by
        rw [AList.mem_insert]; push_neg; exact ⟨w!_ne_x!, w!_notSt⟩
      mspec SMT.eraseFromContext_spec
      mrename_i preE
      mintro ∀StE
      mpure preE
      obtain ⟨StE_types_eq, StE_fvc, StE_used_eq⟩ := preE
      mspec Std.Do.Spec.pure
      mpure_intro
      rw [StE_types_eq, StE_fvc, StE_used_eq]
      and_intros
      · have h : St.env.freshvarsc ≤ St₂.env.freshvarsc := by omega
        exact le_trans h w!_le
      · apply SMT.TypeContext.entries_subset_erase_of_notMem _ w!_notIns
        have h₂ : St₂.types ⊆ AList.insert w! α' St₂.types :=
          SMT.TypeContext.entries_subset_insert_of_notMem w!_fresh
        have h₃ : AList.insert x! α'.option St.types ⊆ St₃.types := by
          rw [← St₂_types_eq]; exact AList.subset_trans h₂ w!_Λ_sub
        exact h₃
      · exact x!_fresh
      · exact x!_not_used
      · intro v hv
        apply w!_used_sub
        rw [St₂_used_eq]
        exact List.mem_cons_of_mem _ hv
      · exact fun v hv => w!_keys_sub (SMT.TypeContext.keys_erase_subset hv)
      · intro v hv hv_not_St
        apply SMT.TypeContext.notMem_erase
        have hv_St₂ : v ∈ St₂.env.usedVars := by
          rw [St₂_used_eq]; exact List.mem_cons_of_mem _ hv
        have hv_ne_x! : v ≠ x! := fun h => x!_not_used (h ▸ hv)
        apply w!_preserves v hv_St₂
        rw [St₂_types_eq, AList.mem_insert]
        push_neg
        exact ⟨hv_ne_x!, hv_not_St⟩
      · intro v hv
        simp only [SMT.fv, List.mem_append, List.mem_removeAll_iff,
          List.mem_cons, List.not_mem_nil, or_false] at hv
        rw [List.mem_union_iff]
        obtain ⟨hv_body, hv_ne_w!⟩ := hv
        rcases hv_body with (hvx! | hvw!) | hvspec
        · exact Or.inr (List.mem_singleton.mpr hvx!)
        · exact absurd hvw! hv_ne_w!
        · have hmem := w!_fv_sub hvspec
          rw [List.mem_union_iff] at hmem
          rcases hmem with hx₀ | hw!
          · left; rw [SMT.fv]; exact hx₀
          · exact absurd (List.mem_singleton.mp hw!) hv_ne_w!
    · -- x = catch-all (the)
      rename_i x! x_ne_none x_ne_some
      mspec (ih (Λ := St₂.types) (n := St₂.env.freshvarsc) (used := St₂.env.usedVars))
      mrename_i pre
      mintro ∀St₃
      mpure pre
      obtain ⟨w!_le, w!_Λ_sub, w!_fresh, w!_not_used, w!_used_sub,
        w!_keys_sub, w!_preserves, w!_fv_sub⟩ := pre
      rename_i out
      obtain ⟨w!, w!_spec⟩ := out
      -- freshness facts about the erased binder `w!`
      have x!_in_St₂ : x! ∈ St₂.types := by rw [St₂_types_eq]; exact (AList.mem_insert _).mpr (Or.inl rfl)
      have w!_ne_x! : w! ≠ x! := fun h => w!_fresh (h ▸ x!_in_St₂)
      have w!_notSt : w! ∉ St.types := fun h =>
        w!_fresh (St₂_types_eq ▸ (AList.mem_insert _).mpr (Or.inr h))
      have w!_notIns : w! ∉ AList.insert x! α'.option St.types := by
        rw [AList.mem_insert]; push_neg; exact ⟨w!_ne_x!, w!_notSt⟩
      mspec SMT.eraseFromContext_spec
      mrename_i preE
      mintro ∀StE
      mpure preE
      obtain ⟨StE_types_eq, StE_fvc, StE_used_eq⟩ := preE
      mspec Std.Do.Spec.pure
      mpure_intro
      rw [StE_types_eq, StE_fvc, StE_used_eq]
      and_intros
      · have h : St.env.freshvarsc ≤ St₂.env.freshvarsc := by omega
        exact le_trans h w!_le
      · apply SMT.TypeContext.entries_subset_erase_of_notMem _ w!_notIns
        have h₂ : St₂.types ⊆ AList.insert w! α' St₂.types :=
          SMT.TypeContext.entries_subset_insert_of_notMem w!_fresh
        have h₃ : AList.insert x! α'.option St.types ⊆ St₃.types := by
          rw [← St₂_types_eq]; exact AList.subset_trans h₂ w!_Λ_sub
        exact h₃
      · exact x!_fresh
      · exact x!_not_used
      · intro v hv
        apply w!_used_sub
        rw [St₂_used_eq]
        exact List.mem_cons_of_mem _ hv
      · exact fun v hv => w!_keys_sub (SMT.TypeContext.keys_erase_subset hv)
      · intro v hv hv_not_St
        apply SMT.TypeContext.notMem_erase
        have hv_St₂ : v ∈ St₂.env.usedVars := by
          rw [St₂_used_eq]; exact List.mem_cons_of_mem _ hv
        have hv_ne_x! : v ≠ x! := fun h => x!_not_used (h ▸ hv)
        apply w!_preserves v hv_St₂
        rw [St₂_types_eq, AList.mem_insert]
        push_neg
        exact ⟨hv_ne_x!, hv_not_St⟩
      · intro v hv
        simp only [noneCast, SMT.fv, List.mem_append, List.mem_removeAll_iff,
          List.mem_cons, List.not_mem_nil, or_false] at hv
        rw [List.mem_union_iff]
        rcases hv with (hvc | hvt) | ⟨hv_body, hv_ne_w!⟩
        · exact Or.inl hvc
        · exact Or.inr (List.mem_singleton.mpr hvt)
        · rcases hv_body with (hvx! | hvw!) | hvspec
          · exact Or.inr (List.mem_singleton.mpr hvx!)
          · exact absurd hvw! hv_ne_w!
          · have hmem := w!_fv_sub hvspec
            rw [List.mem_union_iff] at hmem
            rcases hmem with hx | hw!
            · simp only [SMT.fv] at hx
              exact Or.inl hx
            · exact absurd (List.mem_singleton.mp hw!) hv_ne_w!

/-! ### `declarations`-preservation specs for `freshVar`, `defaultSpecM`, `loosenAux_prf`

`freshVar` only touches `freshvarsc`/`usedVars`/`types`; `defaultSpecM` and
`loosenAux_prf` only call `freshVar` (and recurse), so all three leave
`env.declarations` untouched.  These small specs let the cast-helper delta
specs (`castMembership_decl` etc.) account for the declarations delta as
exactly the explicit `declareConst`/`addSpec` calls. -/

/-- `incrementFreshVarC` leaves `declarations` unchanged. -/
theorem SMT.incrementFreshVarC_decls {decl : SMT.Chunk} :
    ⦃ λ ⟨E, _⟩ ↦ ⌜E.declarations = decl⌝ ⦄
    SMT.incrementFreshVarC
    ⦃ ⇓ _ ⟨E, _⟩ => ⌜E.declarations = decl⌝ ⦄ := by
  unfold SMT.incrementFreshVarC
  mintro pre ∀S; mpure pre
  mspec Std.Do.Spec.modifyGet_StateT

/-- `freshVar` leaves `declarations` unchanged. -/
theorem SMT.freshVar_decls {τ : SMTType} {name : String} {decl : SMT.Chunk} :
    ⦃ λ ⟨E, _⟩ ↦ ⌜E.declarations = decl⌝ ⦄
    SMT.freshVar τ name
    ⦃ ⇓ _ ⟨E, _⟩ => ⌜E.declarations = decl⌝ ⦄ := by
  unfold SMT.freshVar
  mintro pre ∀S; mpure pre
  mspec SMT.incrementFreshVarC_decls

/-- `defaultSpecM` leaves `declarations` unchanged (it only calls `freshVar`). -/
theorem defaultSpecM_decls (τ : SMTType) {name : String} {t : SMT.Term}
    {decl : SMT.Chunk} :
    ⦃ λ ⟨E, _⟩ ↦ ⌜E.declarations = decl⌝ ⦄
    defaultSpecM name τ t
    ⦃ ⇓? _ ⟨E, _⟩ => ⌜E.declarations = decl⌝ ⦄ := by
  induction τ generalizing name t with
  | int | bool | unit | option σ _ =>
    mintro pre ∀S; mpure pre
    unfold defaultSpecM
    mspec Std.Do.Spec.pure
  | pair σ ρ σ_ih ρ_ih =>
    mintro pre ∀S; mpure pre
    unfold defaultSpecM
    mspec σ_ih
    mintro ∀S'; mrename_i pre; mpure pre
    mspec ρ_ih
  | «fun» σ ρ _ ρ_ih =>
    mintro pre ∀S; mpure pre
    unfold defaultSpecM
    mspec SMT.freshVar_decls
    case post.success =>
      mintro ∀S'; mrename_i pre; mpure pre
      mspec ρ_ih
      mpure_intro; simp_all

/-- The `pair` recursion of `loosenAux_prf_decls`, shared with the `graph`
case (whose inner recursion is a `castPath.pair`). -/
theorem loosenAux_prf_decls_pair {α β α' β' : SMTType} (pα : α ~> α') (pβ : β ~> β')
    (pα_ih : ∀ {name : String} {x : SMT.Term} {decl : SMT.Chunk},
      ⦃ λ ⟨E, _⟩ ↦ ⌜E.declarations = decl⌝ ⦄ loosenAux_prf name pα x
      ⦃ ⇓? _ ⟨E, _⟩ => ⌜E.declarations = decl⌝ ⦄)
    (pβ_ih : ∀ {name : String} {x : SMT.Term} {decl : SMT.Chunk},
      ⦃ λ ⟨E, _⟩ ↦ ⌜E.declarations = decl⌝ ⦄ loosenAux_prf name pβ x
      ⦃ ⇓? _ ⟨E, _⟩ => ⌜E.declarations = decl⌝ ⦄)
    {name : String} {x : SMT.Term} {decl : SMT.Chunk} :
    ⦃ λ ⟨E, _⟩ ↦ ⌜E.declarations = decl⌝ ⦄
    loosenAux_prf name (castPath.pair pα pβ) x
    ⦃ ⇓? _ ⟨E, _⟩ => ⌜E.declarations = decl⌝ ⦄ := by
  mintro pre ∀S; mpure pre
  unfold loosenAux_prf
  mspec SMT.freshVar_decls
  case post.success =>
    mintro ∀S'; mrename_i pre; mpure pre
    mspec pα_ih
    mintro ∀S''; mrename_i pre; mpure pre
    mspec pβ_ih
    mpure_intro; simp_all

/-- `loosenAux_prf` leaves `declarations` unchanged (it only calls `freshVar`
and `defaultSpecM`, and recurses). -/
theorem loosenAux_prf_decls {α β : SMTType} (c : α ~> β) {name : String}
    {x : SMT.Term} {decl : SMT.Chunk} :
    ⦃ λ ⟨E, _⟩ ↦ ⌜E.declarations = decl⌝ ⦄
    loosenAux_prf name c x
    ⦃ ⇓? _ ⟨E, _⟩ => ⌜E.declarations = decl⌝ ⦄ := by
  induction c generalizing name x decl with
  | @refl α hα =>
    mintro pre ∀S; mpure pre
    unfold loosenAux_prf
    mspec SMT.freshVar_decls
  | @opt α α' p ih =>
    mintro pre ∀S; mpure pre
    unfold loosenAux_prf
    mspec SMT.freshVar_decls
    case post.success =>
      mintro ∀S'; mrename_i pre; mpure pre
      split
      · mspec Std.Do.Spec.pure
        mpure_intro; simp_all
      · mspec ih
        mpure_intro; simp_all
      · mspec ih
        mpure_intro; simp_all
  | @chpred α α' p ih =>
    mintro pre ∀S; mpure pre
    unfold loosenAux_prf
    mspec SMT.freshVar_decls
    case post.success =>
      mintro ∀S'; mrename_i pre; mpure pre
      mspec SMT.freshVar_decls
      case post.success =>
        mintro ∀S''; mrename_i pre; mpure pre
        mspec ih
        mpure_intro; simp_all
  | @pair α β α' β' pα pβ pα_ih pβ_ih =>
    mintro pre ∀S; mpure pre
    unfold loosenAux_prf
    mspec SMT.freshVar_decls
    case post.success =>
      mintro ∀S'; mrename_i pre; mpure pre
      mspec pα_ih
      mspec pβ_ih
      mpure_intro; simp_all
  | @«fun» α β α' β' hβ pα pβ pα_ih pβ_ih =>
    mintro pre ∀S; mpure pre
    unfold loosenAux_prf
    mspec SMT.freshVar_decls
    case post.success =>
      mintro ∀S'; mrename_i pre; mpure pre
      mspec SMT.freshVar_decls
      case post.success =>
        mintro ∀S''; mrename_i pre; mpure pre
        mspec pα_ih
        mspec SMT.freshVar_decls
        case post.success =>
          mintro ∀S5; mrename_i pre; mpure pre
          mspec pβ_ih
          mspec defaultSpecM_decls
          mpure_intro; simp_all
  | @graph α β α' β' pα pβ pα_ih pβ_ih =>
    mintro pre ∀S; mpure pre
    unfold loosenAux_prf
    mspec SMT.freshVar_decls
    case post.success =>
      mintro ∀S'; mrename_i pre; mpure pre
      mspec SMT.freshVar_decls
      case post.success =>
        mintro ∀S''; mrename_i pre; mpure pre
        mspec (loosenAux_prf_decls_pair pα pβ pα_ih pβ_ih)
        mpure_intro; simp_all

set_option maxHeartbeats 4000000 in
/-- Purely structural specification of `castUnionAux` (no `B`-typing, no
`respects`, no denotation): given that the free variables of both inputs `S`
and `T` already live in the type context `Λ`, the union encoding advances
`freshvarsc`, only grows `usedVars`, keeps `keys ⊆ usedVars`, preserves source
variables, and the encoded term's free variables stay within the final context.
Proved by cases on the cast path. -/
theorem castUnionAux_state
    {α β : SMTType} (c : α ~> β) (S T : SMT.Term) {Λ : SMT.TypeContext} {n : ℕ}
    {used : List SMT.𝒱} {X : List SMT.𝒱} :
    ⦃ fun (⟨E, Λ'⟩ : EncoderState) ↦
        ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ AList.keys Λ ⊆ E.usedVars ∧ E.usedVars = used ∧
          SMT.fv S ⊆ AList.keys Λ ∪ X ∧ SMT.fv T ⊆ AList.keys Λ ∪ X⌝ ⦄
    castUnionAux S T c
    ⦃ ⇓? (⟨t', _σ⟩ : SMT.Term × SMTType) (⟨E', Γ'⟩ : EncoderState) => ⌜
      n ≤ E'.freshvarsc ∧
      Λ ⊆ Γ' ∧
      used ⊆ E'.usedVars ∧
      AList.keys Γ' ⊆ E'.usedVars ∧
      SMT.fv t' ⊆ AList.keys Γ' ∪ X ∧
      (∀ v ∈ used, v ∉ Λ → v ∉ Γ') ⌝⦄ := by
  cases c with
  | @graph α β α' β' c_α c_β =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl, hS_fv, hT_fv⟩ := pre
    unfold castUnionAux castUnion.graph
    mspec loosenAux_prf_state
    mrename_i pre
    mintro ∀St₁
    rename_i S!_pair
    obtain ⟨S!, S!_spec⟩ := S!_pair
    mpure pre
    obtain ⟨S!_le, S!_Λ_sub, S!_fresh, S!_not_used, S!_used_sub,
      S!_keys_sub, S!_preserves, S!_fv_sub⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, hd1_fvc, hd1_used, hd1_types⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨_, _, hs1_fvc, hs1_used, hs1_types⟩ := pres
    mspec SMT.freshVar_spec
    mrename_i pre
    mintro ∀St₂
    mpure pre
    obtain ⟨St₂_types_eq, x_fresh, St₂_fvc, St₂_used_eq, x_not_used⟩ := pre
    mspec Std.Do.Spec.pure
    mpure_intro
    rename_i x
    rw [hs1_types, hd1_types] at St₂_types_eq x_fresh
    rw [hs1_used, hd1_used] at St₂_used_eq x_not_used
    rw [hs1_fvc, hd1_fvc] at St₂_fvc
    have S!_in : S! ∈ AList.keys St₁.types :=
      AList.mem_keys.mp (AList.mem_of_subset S!_Λ_sub (AList.mem_insert _ |>.mpr (Or.inl rfl)))
    and_intros
    · omega
    · refine AList.subset_trans (AList.subset_trans ?_ S!_Λ_sub) ?_
      · exact SMT.TypeContext.entries_subset_insert_of_notMem S!_fresh
      · rw [St₂_types_eq]
        exact SMT.TypeContext.entries_subset_insert_of_notMem x_fresh
    · intro v hv
      rw [St₂_used_eq]
      exact List.mem_cons_of_mem _ (S!_used_sub hv)
    · rw [St₂_types_eq, St₂_used_eq]
      exact keys_insert_subset_cons S!_keys_sub
    · intro v hv
      simp only [SMT.fv, List.mem_removeAll_iff, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hv
      obtain ⟨hv_body, hv_ne_x⟩ := hv
      have mem_St₂ : ∀ w, w ∈ AList.keys St₁.types → w ∈ AList.keys St₂.types := by
        intro w hw
        rw [St₂_types_eq, ← AList.mem_keys, AList.mem_insert]
        exact Or.inr (AList.mem_keys.mp hw)
      rcases hv_body with (hvS! | hvx) | (hvT | hvx)
      · exact List.mem_union_iff.mpr (Or.inl (mem_St₂ v (hvS! ▸ AList.mem_keys.mpr S!_in)))
      · exact absurd hvx hv_ne_x
      · rcases List.mem_union_iff.mp (hT_fv hvT) with hΛ | hX
        · exact List.mem_union_iff.mpr (Or.inl (mem_St₂ v (AList.mem_keys.mpr
            (AList.mem_of_subset S!_Λ_sub
              (AList.mem_insert _ |>.mpr (Or.inr (AList.mem_keys.mpr hΛ)))))))
        · exact List.mem_union_iff.mpr (Or.inr hX)
      · exact absurd hvx hv_ne_x
    · intro v hv hΛ
      rw [St₂_types_eq]
      intro hv_in
      rw [AList.mem_insert] at hv_in
      rcases hv_in with rfl | hv_in
      · exact x_not_used (S!_used_sub hv)
      · exact S!_preserves v hv hΛ hv_in
  | @«fun» α β α' β' hβ c_α c_β =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl, hS_fv, hT_fv⟩ := pre
    unfold castUnionAux castUnion.fun
    mspec loosenAux_prf_state
    mrename_i pre
    mintro ∀St₁
    rename_i S!_pair
    obtain ⟨S!, S!_spec⟩ := S!_pair
    mpure pre
    obtain ⟨S!_le, S!_Λ_sub, S!_fresh, S!_not_used, S!_used_sub,
      S!_keys_sub, S!_preserves, S!_fv_sub⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, hd1_fvc, hd1_used, hd1_types⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨_, _, hs1_fvc, hs1_used, hs1_types⟩ := pres
    split
    · mspec SMT.freshVar_spec
      mrename_i pre
      mintro ∀St₂
      mpure pre
      obtain ⟨St₂_types_eq, x_fresh, St₂_fvc, St₂_used_eq, x_not_used⟩ := pre
      mspec Std.Do.Spec.pure
      mpure_intro
      rename_i σ x
      rw [hs1_types, hd1_types] at St₂_types_eq x_fresh
      rw [hs1_used, hd1_used] at St₂_used_eq x_not_used
      rw [hs1_fvc, hd1_fvc] at St₂_fvc
      have S!_in : S! ∈ AList.keys St₁.types :=
        AList.mem_keys.mp (AList.mem_of_subset S!_Λ_sub (AList.mem_insert _ |>.mpr (Or.inl rfl)))
      and_intros
      · omega
      · refine AList.subset_trans (AList.subset_trans ?_ S!_Λ_sub) ?_
        · exact SMT.TypeContext.entries_subset_insert_of_notMem S!_fresh
        · rw [St₂_types_eq]
          exact SMT.TypeContext.entries_subset_insert_of_notMem x_fresh
      · intro v hv
        rw [St₂_used_eq]
        exact List.mem_cons_of_mem _ (S!_used_sub hv)
      · rw [St₂_types_eq, St₂_used_eq]
        exact keys_insert_subset_cons S!_keys_sub
      · intro v hv
        simp only [SMT.fv, List.mem_removeAll_iff, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false] at hv
        obtain ⟨hv_body, hv_ne_x⟩ := hv
        have mem_St₂ : ∀ w, w ∈ AList.keys St₁.types → w ∈ AList.keys St₂.types := by
          intro w hw
          rw [St₂_types_eq, ← AList.mem_keys, AList.mem_insert]
          exact Or.inr (AList.mem_keys.mp hw)
        rcases hv_body with ((hvS! | hvxa) | hvxa') | ((hvT | hvxb) | hvxb')
        · exact List.mem_union_iff.mpr (Or.inl (mem_St₂ v (hvS! ▸ AList.mem_keys.mpr S!_in)))
        · exact absurd hvxa hv_ne_x
        · exact absurd hvxa' hv_ne_x
        · rcases List.mem_union_iff.mp (hT_fv hvT) with hΛ | hX
          · exact List.mem_union_iff.mpr (Or.inl (mem_St₂ v (AList.mem_keys.mpr
              (AList.mem_of_subset S!_Λ_sub
                (AList.mem_insert _ |>.mpr (Or.inr (AList.mem_keys.mpr hΛ)))))))
          · exact List.mem_union_iff.mpr (Or.inr hX)
        · exact absurd hvxb hv_ne_x
        · exact absurd hvxb' hv_ne_x
      · intro v hv hΛ
        rw [St₂_types_eq]
        intro hv_in
        rw [AList.mem_insert] at hv_in
        rcases hv_in with rfl | hv_in
        · exact x_not_used (S!_used_sub hv)
        · exact S!_preserves v hv hΛ hv_in
    · mvcgen
  | @chpred α α' c_α =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl, hS_fv, hT_fv⟩ := pre
    unfold castUnionAux castUnion.chpred
    mspec loosenAux_prf_state
    mrename_i pre
    mintro ∀St₁
    rename_i S!_pair
    obtain ⟨S!, S!_spec⟩ := S!_pair
    mpure pre
    obtain ⟨S!_le, S!_Λ_sub, S!_fresh, S!_not_used, S!_used_sub,
      S!_keys_sub, S!_preserves, S!_fv_sub⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, hd1_fvc, hd1_used, hd1_types⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨_, _, hs1_fvc, hs1_used, hs1_types⟩ := pres
    mspec SMT.freshVar_spec
    mrename_i pre
    mintro ∀St₂
    mpure pre
    obtain ⟨St₂_types_eq, x_fresh, St₂_fvc, St₂_used_eq, x_not_used⟩ := pre
    mspec Std.Do.Spec.pure
    mpure_intro
    rename_i x
    rw [hs1_types, hd1_types] at St₂_types_eq x_fresh
    rw [hs1_used, hd1_used] at St₂_used_eq x_not_used
    rw [hs1_fvc, hd1_fvc] at St₂_fvc
    have S!_in : S! ∈ AList.keys St₁.types :=
      AList.mem_keys.mp (AList.mem_of_subset S!_Λ_sub (AList.mem_insert _ |>.mpr (Or.inl rfl)))
    and_intros
    · omega
    · refine AList.subset_trans (AList.subset_trans ?_ S!_Λ_sub) ?_
      · exact SMT.TypeContext.entries_subset_insert_of_notMem S!_fresh
      · rw [St₂_types_eq]
        exact SMT.TypeContext.entries_subset_insert_of_notMem x_fresh
    · intro v hv
      rw [St₂_used_eq]
      exact List.mem_cons_of_mem _ (S!_used_sub hv)
    · rw [St₂_types_eq, St₂_used_eq]
      exact keys_insert_subset_cons S!_keys_sub
    · intro v hv
      simp only [SMT.fv, List.mem_removeAll_iff, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hv
      obtain ⟨hv_body, hv_ne_x⟩ := hv
      have mem_St₂ : ∀ w, w ∈ AList.keys St₁.types → w ∈ AList.keys St₂.types := by
        intro w hw
        rw [St₂_types_eq, ← AList.mem_keys, AList.mem_insert]
        exact Or.inr (AList.mem_keys.mp hw)
      rcases hv_body with (hvS! | hvx) | (hvT | hvx)
      · exact List.mem_union_iff.mpr (Or.inl (mem_St₂ v (hvS! ▸ AList.mem_keys.mpr S!_in)))
      · exact absurd hvx hv_ne_x
      · rcases List.mem_union_iff.mp (hT_fv hvT) with hΛ | hX
        · exact List.mem_union_iff.mpr (Or.inl (mem_St₂ v (AList.mem_keys.mpr
            (AList.mem_of_subset S!_Λ_sub
              (AList.mem_insert _ |>.mpr (Or.inr (AList.mem_keys.mpr hΛ)))))))
        · exact List.mem_union_iff.mpr (Or.inr hX)
      · exact absurd hvx hv_ne_x
    · intro v hv hΛ
      rw [St₂_types_eq]
      intro hv_in
      rw [AList.mem_insert] at hv_in
      rcases hv_in with rfl | hv_in
      · exact x_not_used (S!_used_sub hv)
      · exact S!_preserves v hv hΛ hv_in
  | @opt α α' c_α =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl, hS_fv, hT_fv⟩ := pre
    unfold castUnionAux
    mvcgen
  | @pair α β α' β' c_α c_β =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl, hS_fv, hT_fv⟩ := pre
    unfold castUnionAux
    mvcgen
  | @refl α hα =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl, hS_fv, hT_fv⟩ := pre
    unfold castUnionAux
    mvcgen

set_option maxHeartbeats 4000000 in
/-- Purely structural specification of `castInterAux` (no `B`-typing, no
`respects`, no denotation): given that the free variables of both inputs `S`
and `T` already live in the type context `Λ`, the intersection encoding advances
`freshvarsc`, only grows `usedVars`, keeps `keys ⊆ usedVars`, preserves source
variables, and the encoded term's free variables stay within the final context.
Proved by cases on the cast path. -/
theorem castInterAux_state
    {α β : SMTType} (c : α ~> β) (S T : SMT.Term) {Λ : SMT.TypeContext} {n : ℕ}
    {used : List SMT.𝒱} {X : List SMT.𝒱} :
    ⦃ fun (⟨E, Λ'⟩ : EncoderState) ↦
        ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ AList.keys Λ ⊆ E.usedVars ∧ E.usedVars = used ∧
          SMT.fv S ⊆ AList.keys Λ ∪ X ∧ SMT.fv T ⊆ AList.keys Λ ∪ X⌝ ⦄
    castInterAux S T c
    ⦃ ⇓? (⟨t', _σ⟩ : SMT.Term × SMTType) (⟨E', Γ'⟩ : EncoderState) => ⌜
      n ≤ E'.freshvarsc ∧
      Λ ⊆ Γ' ∧
      used ⊆ E'.usedVars ∧
      AList.keys Γ' ⊆ E'.usedVars ∧
      SMT.fv t' ⊆ AList.keys Γ' ∪ X ∧
      (∀ v ∈ used, v ∉ Λ → v ∉ Γ') ⌝⦄ := by
  cases c with
  | @graph α β α' β' c_α c_β =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl, hS_fv, hT_fv⟩ := pre
    unfold castInterAux
    mspec loosenAux_prf_state
    mrename_i pre
    mintro ∀St₁
    rename_i S!_pair
    obtain ⟨S!, S!_spec⟩ := S!_pair
    mpure pre
    obtain ⟨S!_le, S!_Λ_sub, S!_fresh, S!_not_used, S!_used_sub,
      S!_keys_sub, S!_preserves, S!_fv_sub⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, hd1_fvc, hd1_used, hd1_types⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨_, _, hs1_fvc, hs1_used, hs1_types⟩ := pres
    mspec SMT.freshVar_spec
    mrename_i pre
    mintro ∀St₂
    mpure pre
    obtain ⟨St₂_types_eq, x_fresh, St₂_fvc, St₂_used_eq, x_not_used⟩ := pre
    mspec Std.Do.Spec.pure
    mpure_intro
    rename_i x
    rw [hs1_types, hd1_types] at St₂_types_eq x_fresh
    rw [hs1_used, hd1_used] at St₂_used_eq x_not_used
    rw [hs1_fvc, hd1_fvc] at St₂_fvc
    have S!_in : S! ∈ AList.keys St₁.types :=
      AList.mem_keys.mp (AList.mem_of_subset S!_Λ_sub (AList.mem_insert _ |>.mpr (Or.inl rfl)))
    and_intros
    · omega
    · refine AList.subset_trans (AList.subset_trans ?_ S!_Λ_sub) ?_
      · exact SMT.TypeContext.entries_subset_insert_of_notMem S!_fresh
      · rw [St₂_types_eq]
        exact SMT.TypeContext.entries_subset_insert_of_notMem x_fresh
    · intro v hv
      rw [St₂_used_eq]
      exact List.mem_cons_of_mem _ (S!_used_sub hv)
    · rw [St₂_types_eq, St₂_used_eq]
      exact keys_insert_subset_cons S!_keys_sub
    · intro v hv
      simp only [SMT.fv, List.mem_removeAll_iff, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hv
      obtain ⟨hv_body, hv_ne_x⟩ := hv
      have mem_St₂ : ∀ w, w ∈ AList.keys St₁.types → w ∈ AList.keys St₂.types := by
        intro w hw
        rw [St₂_types_eq, ← AList.mem_keys, AList.mem_insert]
        exact Or.inr (AList.mem_keys.mp hw)
      rcases hv_body with (hvS! | hvx) | (hvT | hvx)
      · exact List.mem_union_iff.mpr (Or.inl (mem_St₂ v (hvS! ▸ AList.mem_keys.mpr S!_in)))
      · exact absurd hvx hv_ne_x
      · rcases List.mem_union_iff.mp (hT_fv hvT) with hΛ | hX
        · exact List.mem_union_iff.mpr (Or.inl (mem_St₂ v (AList.mem_keys.mpr
            (AList.mem_of_subset S!_Λ_sub
              (AList.mem_insert _ |>.mpr (Or.inr (AList.mem_keys.mpr hΛ)))))))
        · exact List.mem_union_iff.mpr (Or.inr hX)
      · exact absurd hvx hv_ne_x
    · intro v hv hΛ
      rw [St₂_types_eq]
      intro hv_in
      rw [AList.mem_insert] at hv_in
      rcases hv_in with rfl | hv_in
      · exact x_not_used (S!_used_sub hv)
      · exact S!_preserves v hv hΛ hv_in
  | @«fun» α β α' β' hβ c_α c_β =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl, hS_fv, hT_fv⟩ := pre
    unfold castInterAux
    mspec loosenAux_prf_state
    mrename_i pre
    mintro ∀St₁
    rename_i S!_pair
    obtain ⟨S!, S!_spec⟩ := S!_pair
    mpure pre
    obtain ⟨S!_le, S!_Λ_sub, S!_fresh, S!_not_used, S!_used_sub,
      S!_keys_sub, S!_preserves, S!_fv_sub⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, hd1_fvc, hd1_used, hd1_types⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨_, _, hs1_fvc, hs1_used, hs1_types⟩ := pres
    split
    · mspec SMT.freshVar_spec
      mrename_i pre
      mintro ∀St₂
      mpure pre
      obtain ⟨St₂_types_eq, x_fresh, St₂_fvc, St₂_used_eq, x_not_used⟩ := pre
      mspec Std.Do.Spec.pure
      mpure_intro
      rename_i σ x
      rw [hs1_types, hd1_types] at St₂_types_eq x_fresh
      rw [hs1_used, hd1_used] at St₂_used_eq x_not_used
      rw [hs1_fvc, hd1_fvc] at St₂_fvc
      have S!_in : S! ∈ AList.keys St₁.types :=
        AList.mem_keys.mp (AList.mem_of_subset S!_Λ_sub (AList.mem_insert _ |>.mpr (Or.inl rfl)))
      and_intros
      · omega
      · refine AList.subset_trans (AList.subset_trans ?_ S!_Λ_sub) ?_
        · exact SMT.TypeContext.entries_subset_insert_of_notMem S!_fresh
        · rw [St₂_types_eq]
          exact SMT.TypeContext.entries_subset_insert_of_notMem x_fresh
      · intro v hv
        rw [St₂_used_eq]
        exact List.mem_cons_of_mem _ (S!_used_sub hv)
      · rw [St₂_types_eq, St₂_used_eq]
        exact keys_insert_subset_cons S!_keys_sub
      · intro v hv
        simp only [SMT.fv, List.mem_removeAll_iff, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false] at hv
        obtain ⟨hv_body, hv_ne_x⟩ := hv
        have mem_St₂ : ∀ w, w ∈ AList.keys St₁.types → w ∈ AList.keys St₂.types := by
          intro w hw
          rw [St₂_types_eq, ← AList.mem_keys, AList.mem_insert]
          exact Or.inr (AList.mem_keys.mp hw)
        rcases hv_body with ((hvS! | hvxa) | hvxa') | ((hvT | hvxb) | hvxb')
        · exact List.mem_union_iff.mpr (Or.inl (mem_St₂ v (hvS! ▸ AList.mem_keys.mpr S!_in)))
        · exact absurd hvxa hv_ne_x
        · exact absurd hvxa' hv_ne_x
        · rcases List.mem_union_iff.mp (hT_fv hvT) with hΛ | hX
          · exact List.mem_union_iff.mpr (Or.inl (mem_St₂ v (AList.mem_keys.mpr
              (AList.mem_of_subset S!_Λ_sub
                (AList.mem_insert _ |>.mpr (Or.inr (AList.mem_keys.mpr hΛ)))))))
          · exact List.mem_union_iff.mpr (Or.inr hX)
        · exact absurd hvxb hv_ne_x
        · exact absurd hvxb' hv_ne_x
      · intro v hv hΛ
        rw [St₂_types_eq]
        intro hv_in
        rw [AList.mem_insert] at hv_in
        rcases hv_in with rfl | hv_in
        · exact x_not_used (S!_used_sub hv)
        · exact S!_preserves v hv hΛ hv_in
    · mvcgen
  | @chpred α α' c_α =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl, hS_fv, hT_fv⟩ := pre
    unfold castInterAux
    mspec loosenAux_prf_state
    mrename_i pre
    mintro ∀St₁
    rename_i S!_pair
    obtain ⟨S!, S!_spec⟩ := S!_pair
    mpure pre
    obtain ⟨S!_le, S!_Λ_sub, S!_fresh, S!_not_used, S!_used_sub,
      S!_keys_sub, S!_preserves, S!_fv_sub⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, hd1_fvc, hd1_used, hd1_types⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨_, _, hs1_fvc, hs1_used, hs1_types⟩ := pres
    mspec SMT.freshVar_spec
    mrename_i pre
    mintro ∀St₂
    mpure pre
    obtain ⟨St₂_types_eq, x_fresh, St₂_fvc, St₂_used_eq, x_not_used⟩ := pre
    mspec Std.Do.Spec.pure
    mpure_intro
    rename_i x
    rw [hs1_types, hd1_types] at St₂_types_eq x_fresh
    rw [hs1_used, hd1_used] at St₂_used_eq x_not_used
    rw [hs1_fvc, hd1_fvc] at St₂_fvc
    have S!_in : S! ∈ AList.keys St₁.types :=
      AList.mem_keys.mp (AList.mem_of_subset S!_Λ_sub (AList.mem_insert _ |>.mpr (Or.inl rfl)))
    and_intros
    · omega
    · refine AList.subset_trans (AList.subset_trans ?_ S!_Λ_sub) ?_
      · exact SMT.TypeContext.entries_subset_insert_of_notMem S!_fresh
      · rw [St₂_types_eq]
        exact SMT.TypeContext.entries_subset_insert_of_notMem x_fresh
    · intro v hv
      rw [St₂_used_eq]
      exact List.mem_cons_of_mem _ (S!_used_sub hv)
    · rw [St₂_types_eq, St₂_used_eq]
      exact keys_insert_subset_cons S!_keys_sub
    · intro v hv
      simp only [SMT.fv, List.mem_removeAll_iff, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hv
      obtain ⟨hv_body, hv_ne_x⟩ := hv
      have mem_St₂ : ∀ w, w ∈ AList.keys St₁.types → w ∈ AList.keys St₂.types := by
        intro w hw
        rw [St₂_types_eq, ← AList.mem_keys, AList.mem_insert]
        exact Or.inr (AList.mem_keys.mp hw)
      rcases hv_body with (hvS! | hvx) | (hvT | hvx)
      · exact List.mem_union_iff.mpr (Or.inl (mem_St₂ v (hvS! ▸ AList.mem_keys.mpr S!_in)))
      · exact absurd hvx hv_ne_x
      · rcases List.mem_union_iff.mp (hT_fv hvT) with hΛ | hX
        · exact List.mem_union_iff.mpr (Or.inl (mem_St₂ v (AList.mem_keys.mpr
            (AList.mem_of_subset S!_Λ_sub
              (AList.mem_insert _ |>.mpr (Or.inr (AList.mem_keys.mpr hΛ)))))))
        · exact List.mem_union_iff.mpr (Or.inr hX)
      · exact absurd hvx hv_ne_x
    · intro v hv hΛ
      rw [St₂_types_eq]
      intro hv_in
      rw [AList.mem_insert] at hv_in
      rcases hv_in with rfl | hv_in
      · exact x_not_used (S!_used_sub hv)
      · exact S!_preserves v hv hΛ hv_in
  | @opt α α' c_α =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl, hS_fv, hT_fv⟩ := pre
    unfold castInterAux
    mvcgen
  | @pair α β α' β' c_α c_β =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl, hS_fv, hT_fv⟩ := pre
    unfold castInterAux
    mvcgen
  | @refl α hα =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl, hS_fv, hT_fv⟩ := pre
    unfold castInterAux
    mvcgen

set_option maxHeartbeats 4000000 in
/-- Purely structural specification of `castApp` (no `B`-typing, no `respects`,
no denotation): given that the free variables of both inputs `f` and `x`
already live in the type context `Λ`, the application encoding advances
`freshvarsc`, only grows `usedVars`, keeps `keys ⊆ usedVars`, preserves source
variables, and the encoded term's free variables stay within the final context.
Proved by cases on the function/argument types. -/
theorem castApp_state
    (f x : SMT.Term) (σf σx : SMTType) {Λ : SMT.TypeContext} {n : ℕ}
    {used : List SMT.𝒱} {X : List SMT.𝒱} :
    ⦃ fun (⟨E, Λ'⟩ : EncoderState) ↦
        ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ AList.keys Λ ⊆ E.usedVars ∧ E.usedVars = used ∧
          SMT.fv f ⊆ AList.keys Λ ∪ X ∧ SMT.fv x ⊆ AList.keys Λ ∪ X⌝ ⦄
    castApp (f, σf) (x, σx)
    ⦃ ⇓? (⟨t', _σ⟩ : SMT.Term × SMTType) (⟨E', Γ'⟩ : EncoderState) => ⌜
      n ≤ E'.freshvarsc ∧
      Λ ⊆ Γ' ∧
      used ⊆ E'.usedVars ∧
      AList.keys Γ' ⊆ E'.usedVars ∧
      SMT.fv t' ⊆ AList.keys Γ' ∪ X ∧
      (∀ v ∈ used, v ∉ Λ → v ∉ Γ') ⌝⦄ := by
  unfold castApp
  mvcgen
  case vc3.h_2.isTrue =>
    rename_i hxeq hfeq _ St hpre
    obtain ⟨rfl, rfl, sub, rfl, hf_fv, hx_fv⟩ := hpre
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hxeq
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hfeq
    mspec loosenAux_prf_state
    mrename_i pre
    mintro ∀St₁
    rename_i fpair
    obtain ⟨fv1, fv1_spec⟩ := fpair
    mpure pre
    obtain ⟨fv1_le, fv1_Λ_sub, fv1_fresh, fv1_not_used, fv1_used_sub,
      fv1_keys_sub, fv1_preserves, fv1_fv_sub⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, hd_fvc, hd_used, hd_types⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨_, _, hs_fvc, hs_used, hs_types⟩ := pres
    mspec Std.Do.Spec.pure
    mpure_intro
    rw [hs_types, hd_types, hs_used, hd_used, hs_fvc, hd_fvc]
    have fv1_in : fv1 ∈ AList.keys St₁.types :=
      AList.mem_keys.mp (AList.mem_of_subset fv1_Λ_sub (AList.mem_insert _ |>.mpr (Or.inl rfl)))
    and_intros
    · exact fv1_le
    · exact AList.subset_trans
        (SMT.TypeContext.entries_subset_insert_of_notMem fv1_fresh) fv1_Λ_sub
    · exact fv1_used_sub
    · exact fv1_keys_sub
    · intro v hv
      simp only [SMT.fv, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with hvfv1 | hvx
      · exact List.mem_union_iff.mpr (Or.inl (hvfv1 ▸ fv1_in))
      · rcases List.mem_union_iff.mp (hx_fv hvx) with hΛ | hX
        · exact List.mem_union_iff.mpr (Or.inl (AList.mem_keys.mp (AList.mem_of_subset fv1_Λ_sub
            (AList.mem_insert _ |>.mpr (Or.inr (AList.mem_keys.mpr hΛ))))))
        · exact List.mem_union_iff.mpr (Or.inr hX)
    · exact fv1_preserves
  case vc4.h_2.isFalse.isTrue =>
    rename_i hxeq hfeq _ _ St hpre
    obtain ⟨rfl, rfl, sub, rfl, hf_fv, hx_fv⟩ := hpre
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hxeq
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hfeq
    mspec loosenAux_prf_state
    mrename_i pre
    mintro ∀St₁
    rename_i xpair
    obtain ⟨xv1, xv1_spec⟩ := xpair
    mpure pre
    obtain ⟨xv1_le, xv1_Λ_sub, xv1_fresh, xv1_not_used, xv1_used_sub,
      xv1_keys_sub, xv1_preserves, xv1_fv_sub⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, hd_fvc, hd_used, hd_types⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨_, _, hs_fvc, hs_used, hs_types⟩ := pres
    mspec Std.Do.Spec.pure
    mpure_intro
    rw [hs_types, hd_types, hs_used, hd_used, hs_fvc, hd_fvc]
    have xv1_in : xv1 ∈ AList.keys St₁.types :=
      AList.mem_keys.mp (AList.mem_of_subset xv1_Λ_sub (AList.mem_insert _ |>.mpr (Or.inl rfl)))
    and_intros
    · exact xv1_le
    · exact AList.subset_trans
        (SMT.TypeContext.entries_subset_insert_of_notMem xv1_fresh) xv1_Λ_sub
    · exact xv1_used_sub
    · exact xv1_keys_sub
    · intro v hv
      simp only [SMT.fv, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with hvf | hvxv1
      · rcases List.mem_union_iff.mp (hf_fv hvf) with hΛ | hX
        · exact List.mem_union_iff.mpr (Or.inl (AList.mem_keys.mp (AList.mem_of_subset xv1_Λ_sub
            (AList.mem_insert _ |>.mpr (Or.inr (AList.mem_keys.mpr hΛ))))))
        · exact List.mem_union_iff.mpr (Or.inr hX)
      · exact List.mem_union_iff.mpr (Or.inl (hvxv1 ▸ xv1_in))
    · exact xv1_preserves
  case vc5.h_3.isTrue =>
    rename_i hxeq hfeq _ St hpre
    obtain ⟨rfl, rfl, sub, rfl, hf_fv, hx_fv⟩ := hpre
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hxeq
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hfeq
    mspec loosenAux_prf_state
    mrename_i pre
    mintro ∀St₁
    rename_i fpair
    obtain ⟨fv1, fv1_spec⟩ := fpair
    mpure pre
    obtain ⟨fv1_le, fv1_Λ_sub, fv1_fresh, fv1_not_used, fv1_used_sub,
      fv1_keys_sub, fv1_preserves, fv1_fv_sub⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, hd_fvc, hd_used, hd_types⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨_, _, hs_fvc, hs_used, hs_types⟩ := pres
    mspec Std.Do.Spec.pure
    mpure_intro
    rw [hs_types, hd_types, hs_used, hd_used, hs_fvc, hd_fvc]
    have fv1_in : fv1 ∈ AList.keys St₁.types :=
      AList.mem_keys.mp (AList.mem_of_subset fv1_Λ_sub (AList.mem_insert _ |>.mpr (Or.inl rfl)))
    and_intros
    · exact fv1_le
    · exact AList.subset_trans
        (SMT.TypeContext.entries_subset_insert_of_notMem fv1_fresh) fv1_Λ_sub
    · exact fv1_used_sub
    · exact fv1_keys_sub
    · intro v hv
      simp only [SMT.fv, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with hvfv1 | hvx
      · exact List.mem_union_iff.mpr (Or.inl (hvfv1 ▸ fv1_in))
      · rcases List.mem_union_iff.mp (hx_fv hvx) with hΛ | hX
        · exact List.mem_union_iff.mpr (Or.inl (AList.mem_keys.mp (AList.mem_of_subset fv1_Λ_sub
            (AList.mem_insert _ |>.mpr (Or.inr (AList.mem_keys.mpr hΛ))))))
        · exact List.mem_union_iff.mpr (Or.inr hX)
    · exact fv1_preserves
  case vc6.h_3.isFalse.isTrue =>
    rename_i hxeq hfeq _ _ St hpre
    obtain ⟨rfl, rfl, sub, rfl, hf_fv, hx_fv⟩ := hpre
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hxeq
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hfeq
    mspec loosenAux_prf_state
    mrename_i pre
    mintro ∀St₁
    rename_i xpair
    obtain ⟨xv1, xv1_spec⟩ := xpair
    mpure pre
    obtain ⟨xv1_le, xv1_Λ_sub, xv1_fresh, xv1_not_used, xv1_used_sub,
      xv1_keys_sub, xv1_preserves, xv1_fv_sub⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, hd_fvc, hd_used, hd_types⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨_, _, hs_fvc, hs_used, hs_types⟩ := pres
    mspec Std.Do.Spec.pure
    mpure_intro
    rw [hs_types, hd_types, hs_used, hd_used, hs_fvc, hd_fvc]
    have xv1_in : xv1 ∈ AList.keys St₁.types :=
      AList.mem_keys.mp (AList.mem_of_subset xv1_Λ_sub (AList.mem_insert _ |>.mpr (Or.inl rfl)))
    and_intros
    · exact xv1_le
    · exact AList.subset_trans
        (SMT.TypeContext.entries_subset_insert_of_notMem xv1_fresh) xv1_Λ_sub
    · exact xv1_used_sub
    · exact xv1_keys_sub
    · intro v hv
      simp only [SMT.fv, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with hvf | hvxv1
      · rcases List.mem_union_iff.mp (hf_fv hvf) with hΛ | hX
        · exact List.mem_union_iff.mpr (Or.inl (AList.mem_keys.mp (AList.mem_of_subset xv1_Λ_sub
            (AList.mem_insert _ |>.mpr (Or.inr (AList.mem_keys.mpr hΛ))))))
        · exact List.mem_union_iff.mpr (Or.inr hX)
      · exact List.mem_union_iff.mpr (Or.inl (hvxv1 ▸ xv1_in))
    · exact xv1_preserves
  case vc1.h_1.isTrue =>
    rename_i hxeq hfeq _ St hpre
    obtain ⟨rfl, rfl, sub, rfl, hf_fv, hx_fv⟩ := hpre
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hxeq
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hfeq
    mspec loosenAux_prf_state
    mrename_i pre
    mintro ∀St₁
    rename_i fpair
    obtain ⟨fv1, fv1_spec⟩ := fpair
    mpure pre
    obtain ⟨fv1_le, fv1_Λ_sub, fv1_fresh, fv1_not_used, fv1_used_sub,
      fv1_keys_sub, fv1_preserves, fv1_fv_sub⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, hd_fvc, hd_used, hd_types⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨_, _, hs_fvc, hs_used, hs_types⟩ := pres
    mspec SMT.freshVar_spec
    mrename_i pre2
    mintro ∀St₂
    rename_i ff
    mpure pre2
    obtain ⟨St₂_types_eq, ff_fresh, St₂_fvc, St₂_used_eq, ff_not_used⟩ := pre2
    rw [hs_types, hd_types] at St₂_types_eq ff_fresh
    rw [hs_used, hd_used] at St₂_used_eq ff_not_used
    rw [hs_fvc, hd_fvc] at St₂_fvc
    mspec SMT.declareConst_spec
    mrename_i pred2
    mintro ∀St₂d
    mpure pred2
    obtain ⟨_, _, hd2_fvc, hd2_used, hd2_types⟩ := pred2
    mspec SMT.freshVar_spec
    mrename_i pre3
    mintro ∀St₃
    rename_i u_var
    mpure pre3
    obtain ⟨St₃_types_eq, u_fresh, St₃_fvc, St₃_used_eq, u_not_used⟩ := pre3
    rw [hd2_types] at St₃_types_eq u_fresh
    rw [hd2_used] at St₃_used_eq u_not_used
    rw [hd2_fvc] at St₃_fvc
    mspec SMT.freshVar_spec
    mrename_i pre4
    mintro ∀St₄
    rename_i v_var
    mpure pre4
    obtain ⟨St₄_types_eq, v_fresh, St₄_fvc, St₄_used_eq, v_not_used⟩ := pre4
    mspec SMT.addSpec_spec
    mrename_i pres2
    mintro ∀St₄s
    mpure pres2
    obtain ⟨_, _, hs2_fvc, hs2_used, hs2_types⟩ := pres2
    mspec Std.Do.Spec.pure
    mpure_intro
    -- Membership of the freshly-declared `ff` in each state's types.
    have ff_in_St₂ : ff ∈ AList.keys St₂.types := by
      rw [St₂_types_eq]
      exact AList.mem_keys.mp (AList.mem_insert _ |>.mpr (Or.inl rfl))
    have St₂_into_St₃ : AList.keys St₂.types ⊆ AList.keys St₃.types := by
      intro w hw
      rw [← AList.mem_keys, St₃_types_eq, AList.mem_insert]
      exact Or.inr (AList.mem_keys.mp hw)
    have St₃_into_St₄ : AList.keys St₃.types ⊆ AList.keys St₄.types := by
      intro w hw
      rw [← AList.mem_keys, St₄_types_eq, AList.mem_insert]
      exact Or.inr (AList.mem_keys.mp hw)
    have ff_in_St₄ : ff ∈ AList.keys St₄.types :=
      St₃_into_St₄ (St₂_into_St₃ ff_in_St₂)
    and_intros
    · rw [hs2_fvc, St₄_fvc, St₃_fvc, St₂_fvc]
      exact le_trans fv1_le (Nat.le_succ_of_le (Nat.le_succ_of_le (Nat.le_succ _)))
    · rw [hs2_types]
      have h12 : St₁.types ⊆ St₂.types :=
        St₂_types_eq ▸ SMT.TypeContext.entries_subset_insert_of_notMem ff_fresh
      have h23 : St₂.types ⊆ St₃.types :=
        St₃_types_eq ▸ SMT.TypeContext.entries_subset_insert_of_notMem u_fresh
      have h34 : St₃.types ⊆ St₄.types :=
        St₄_types_eq ▸ SMT.TypeContext.entries_subset_insert_of_notMem v_fresh
      exact AList.subset_trans
        (SMT.TypeContext.entries_subset_insert_of_notMem fv1_fresh)
        (AList.subset_trans fv1_Λ_sub
          (AList.subset_trans h12 (AList.subset_trans h23 h34)))
    · rw [hs2_used, St₄_used_eq, St₃_used_eq, St₂_used_eq]
      intro w hw
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (fv1_used_sub hw)))
    · rw [hs2_types, hs2_used, St₄_types_eq, St₄_used_eq, St₃_types_eq, St₃_used_eq,
        St₂_types_eq, St₂_used_eq]
      exact keys_insert_subset_cons (keys_insert_subset_cons
        (keys_insert_subset_cons fv1_keys_sub))
    · rw [hs2_types]
      intro w hw
      simp only [SMT.fv, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with hwff | hwx
      · exact List.mem_union_iff.mpr (Or.inl (hwff ▸ ff_in_St₄))
      · rcases List.mem_union_iff.mp (hx_fv hwx) with hΛ | hX
        · have hx_in_St₁ : w ∈ AList.keys St₁.types :=
            AList.mem_keys.mp (AList.mem_of_subset fv1_Λ_sub
              (AList.mem_insert _ |>.mpr (Or.inr (AList.mem_keys.mpr hΛ))))
          have hx_in_St₂ : w ∈ AList.keys St₂.types := by
            rw [← AList.mem_keys, St₂_types_eq, AList.mem_insert]
            exact Or.inr (AList.mem_keys.mp hx_in_St₁)
          exact List.mem_union_iff.mpr (Or.inl (St₃_into_St₄ (St₂_into_St₃ hx_in_St₂)))
        · exact List.mem_union_iff.mpr (Or.inr hX)
    · rw [hs2_types]
      intro w hw hΛ
      have hw_St₁ : w ∉ St₁.types := fv1_preserves w hw hΛ
      have hw_St₂used : w ∈ St₂.env.usedVars :=
        St₂_used_eq ▸ List.mem_cons_of_mem ff (fv1_used_sub hw)
      have hw_St₃used : w ∈ St₃.env.usedVars :=
        St₃_used_eq ▸ List.mem_cons_of_mem u_var hw_St₂used
      have hw_ne_ff : w ≠ ff := fun h => ff_not_used (h ▸ fv1_used_sub hw)
      have hw_ne_u : w ≠ u_var := fun h => u_not_used (h ▸ hw_St₂used)
      have hw_ne_v : w ≠ v_var := fun h => v_not_used (h ▸ hw_St₃used)
      intro hw_in
      rw [St₄_types_eq, AList.mem_insert] at hw_in
      rcases hw_in with rfl | hw_in
      · exact hw_ne_v rfl
      · rw [St₃_types_eq, AList.mem_insert] at hw_in
        rcases hw_in with rfl | hw_in
        · exact hw_ne_u rfl
        · rw [St₂_types_eq, AList.mem_insert] at hw_in
          rcases hw_in with rfl | hw_in
          · exact hw_ne_ff rfl
          · exact hw_St₁ hw_in
  case vc2.h_1.isFalse.isTrue =>
    rename_i hxeq hfeq _ _ St hpre
    obtain ⟨rfl, rfl, sub, rfl, hf_fv, hx_fv⟩ := hpre
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hxeq
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hfeq
    mspec loosenAux_prf_state
    mrename_i pre
    mintro ∀St₁
    rename_i xpair
    obtain ⟨fv1, fv1_spec⟩ := xpair
    mpure pre
    obtain ⟨fv1_le, fv1_Λ_sub, fv1_fresh, fv1_not_used, fv1_used_sub,
      fv1_keys_sub, fv1_preserves, fv1_fv_sub⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, hd_fvc, hd_used, hd_types⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨_, _, hs_fvc, hs_used, hs_types⟩ := pres
    mspec SMT.freshVar_spec
    mrename_i pre2
    mintro ∀St₂
    rename_i ff
    mpure pre2
    obtain ⟨St₂_types_eq, ff_fresh, St₂_fvc, St₂_used_eq, ff_not_used⟩ := pre2
    rw [hs_types, hd_types] at St₂_types_eq ff_fresh
    rw [hs_used, hd_used] at St₂_used_eq ff_not_used
    rw [hs_fvc, hd_fvc] at St₂_fvc
    mspec SMT.declareConst_spec
    mrename_i pred2
    mintro ∀St₂d
    mpure pred2
    obtain ⟨_, _, hd2_fvc, hd2_used, hd2_types⟩ := pred2
    mspec SMT.freshVar_spec
    mrename_i pre3
    mintro ∀St₃
    rename_i u_var
    mpure pre3
    obtain ⟨St₃_types_eq, u_fresh, St₃_fvc, St₃_used_eq, u_not_used⟩ := pre3
    rw [hd2_types] at St₃_types_eq u_fresh
    rw [hd2_used] at St₃_used_eq u_not_used
    rw [hd2_fvc] at St₃_fvc
    mspec SMT.freshVar_spec
    mrename_i pre4
    mintro ∀St₄
    rename_i v_var
    mpure pre4
    obtain ⟨St₄_types_eq, v_fresh, St₄_fvc, St₄_used_eq, v_not_used⟩ := pre4
    mspec SMT.addSpec_spec
    mrename_i pres2
    mintro ∀St₄s
    mpure pres2
    obtain ⟨_, _, hs2_fvc, hs2_used, hs2_types⟩ := pres2
    mspec Std.Do.Spec.pure
    mpure_intro
    have fv1_in_St₁ : fv1 ∈ AList.keys St₁.types :=
      AList.mem_keys.mp (AList.mem_of_subset fv1_Λ_sub (AList.mem_insert _ |>.mpr (Or.inl rfl)))
    have ff_in_St₂ : ff ∈ AList.keys St₂.types := by
      rw [St₂_types_eq]
      exact AList.mem_keys.mp (AList.mem_insert _ |>.mpr (Or.inl rfl))
    have St₁_into_St₂ : AList.keys St₁.types ⊆ AList.keys St₂.types := by
      intro w hw
      rw [← AList.mem_keys, St₂_types_eq, AList.mem_insert]
      exact Or.inr (AList.mem_keys.mp hw)
    have St₂_into_St₃ : AList.keys St₂.types ⊆ AList.keys St₃.types := by
      intro w hw
      rw [← AList.mem_keys, St₃_types_eq, AList.mem_insert]
      exact Or.inr (AList.mem_keys.mp hw)
    have St₃_into_St₄ : AList.keys St₃.types ⊆ AList.keys St₄.types := by
      intro w hw
      rw [← AList.mem_keys, St₄_types_eq, AList.mem_insert]
      exact Or.inr (AList.mem_keys.mp hw)
    have fv1_in_St₄ : fv1 ∈ AList.keys St₄.types :=
      St₃_into_St₄ (St₂_into_St₃ (St₁_into_St₂ fv1_in_St₁))
    have ff_in_St₄ : ff ∈ AList.keys St₄.types :=
      St₃_into_St₄ (St₂_into_St₃ ff_in_St₂)
    and_intros
    · rw [hs2_fvc, St₄_fvc, St₃_fvc, St₂_fvc]
      exact le_trans fv1_le (Nat.le_succ_of_le (Nat.le_succ_of_le (Nat.le_succ _)))
    · rw [hs2_types]
      have h12 : St₁.types ⊆ St₂.types :=
        St₂_types_eq ▸ SMT.TypeContext.entries_subset_insert_of_notMem ff_fresh
      have h23 : St₂.types ⊆ St₃.types :=
        St₃_types_eq ▸ SMT.TypeContext.entries_subset_insert_of_notMem u_fresh
      have h34 : St₃.types ⊆ St₄.types :=
        St₄_types_eq ▸ SMT.TypeContext.entries_subset_insert_of_notMem v_fresh
      exact AList.subset_trans
        (SMT.TypeContext.entries_subset_insert_of_notMem fv1_fresh)
        (AList.subset_trans fv1_Λ_sub
          (AList.subset_trans h12 (AList.subset_trans h23 h34)))
    · rw [hs2_used, St₄_used_eq, St₃_used_eq, St₂_used_eq]
      intro w hw
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (fv1_used_sub hw)))
    · rw [hs2_types, hs2_used, St₄_types_eq, St₄_used_eq, St₃_types_eq, St₃_used_eq,
        St₂_types_eq, St₂_used_eq]
      exact keys_insert_subset_cons (keys_insert_subset_cons
        (keys_insert_subset_cons fv1_keys_sub))
    · rw [hs2_types]
      intro w hw
      simp only [SMT.fv, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with hwff | hwfv1
      · exact List.mem_union_iff.mpr (Or.inl (hwff ▸ ff_in_St₄))
      · exact List.mem_union_iff.mpr (Or.inl (hwfv1 ▸ fv1_in_St₄))
    · rw [hs2_types]
      intro w hw hΛ
      have hw_St₁ : w ∉ St₁.types := fv1_preserves w hw hΛ
      have hw_St₂used : w ∈ St₂.env.usedVars :=
        St₂_used_eq ▸ List.mem_cons_of_mem ff (fv1_used_sub hw)
      have hw_St₃used : w ∈ St₃.env.usedVars :=
        St₃_used_eq ▸ List.mem_cons_of_mem u_var hw_St₂used
      have hw_ne_ff : w ≠ ff := fun h => ff_not_used (h ▸ fv1_used_sub hw)
      have hw_ne_u : w ≠ u_var := fun h => u_not_used (h ▸ hw_St₂used)
      have hw_ne_v : w ≠ v_var := fun h => v_not_used (h ▸ hw_St₃used)
      intro hw_in
      rw [St₄_types_eq, AList.mem_insert] at hw_in
      rcases hw_in with rfl | hw_in
      · exact hw_ne_v rfl
      · rw [St₃_types_eq, AList.mem_insert] at hw_in
        rcases hw_in with rfl | hw_in
        · exact hw_ne_u rfl
        · rw [St₂_types_eq, AList.mem_insert] at hw_in
          rcases hw_in with rfl | hw_in
          · exact hw_ne_ff rfl
          · exact hw_St₁ hw_in

set_option maxHeartbeats 4000000 in
/-- Purely structural specification of `castMembership` (no `B`-typing, no
`respects`, no denotation): mirrors `castApp_state`. Given that the free
variables of both inputs `x` and `S` already live in the type context `Λ`, the
membership encoding advances `freshvarsc`, only grows `usedVars`, keeps
`keys ⊆ usedVars`, preserves source variables, and the encoded term's free
variables stay within the final context. Proved by cases on the input types. -/
theorem castMembership_state
    (x S : SMT.Term) (σx σS : SMTType) {Λ : SMT.TypeContext} {n : ℕ}
    {used : List SMT.𝒱} {X : List SMT.𝒱} :
    ⦃ fun (⟨E, Λ'⟩ : EncoderState) ↦
        ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ AList.keys Λ ⊆ E.usedVars ∧ E.usedVars = used ∧
          SMT.fv x ⊆ AList.keys Λ ∪ X ∧ SMT.fv S ⊆ AList.keys Λ ∪ X⌝ ⦄
    castMembership (x, σx) (S, σS)
    ⦃ ⇓? (⟨t', _σ⟩ : SMT.Term × SMTType) (⟨E', Γ'⟩ : EncoderState) => ⌜
      n ≤ E'.freshvarsc ∧
      Λ ⊆ Γ' ∧
      used ⊆ E'.usedVars ∧
      AList.keys Γ' ⊆ E'.usedVars ∧
      SMT.fv t' ⊆ AList.keys Γ' ∪ X ∧
      (∀ v ∈ used, v ∉ Λ → v ∉ Γ') ⌝⦄ := by
  unfold castMembership
  mvcgen
  case vc1.h_1.isTrue =>
    rename_i α' hσS hσx St hpre
    obtain ⟨rfl, rfl, sub, rfl, hx_fv, hS_fv⟩ := hpre
    and_intros
    · exact le_refl _
    · exact fun _ h => h
    · exact fun _ h => h
    · exact sub
    · intro v hv
      simp only [SMT.fv, List.mem_append] at hv
      rcases hv with hvS | hvx
      · exact hS_fv hvS
      · exact hx_fv hvx
    · intro v hv hΛ hin; exact hΛ hin
  case vc2.h_1.isFalse.isTrue =>
    rename_i α' hσS hσx_ne hσx_le St hpre
    obtain ⟨rfl, rfl, sub, rfl, hx_fv, hS_fv⟩ := hpre
    mspec loosenAux_prf_state
    mrename_i pre
    mintro ∀St₁
    rename_i xout
    obtain ⟨x!, x!_spec⟩ := xout
    mpure pre
    obtain ⟨x!_le, x!_Λ_sub, x!_fresh, x!_not_used, x!_used_sub,
      x!_keys_sub, x!_preserves, x!_fv_sub⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, hd_fvc, hd_used, hd_types⟩ := pred
    mspec Std.Do.Spec.pure
    mpure_intro
    rw [hd_types, hd_used, hd_fvc]
    have x!_in : x! ∈ AList.keys St₁.types :=
      AList.mem_keys.mp (AList.mem_of_subset x!_Λ_sub (AList.mem_insert _ |>.mpr (Or.inl rfl)))
    and_intros
    · exact x!_le
    · exact AList.subset_trans
        (SMT.TypeContext.entries_subset_insert_of_notMem x!_fresh) x!_Λ_sub
    · exact x!_used_sub
    · exact x!_keys_sub
    · intro v hv
      simp only [SMT.fv, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with hvspec | hvS | hvx!
      · have hmem := x!_fv_sub hvspec
        rw [List.mem_union_iff] at hmem
        rcases hmem with hvx | hvx!'
        · rcases List.mem_union_iff.mp (hx_fv hvx) with hΛ | hX
          · exact List.mem_union_iff.mpr (Or.inl (AList.mem_keys.mp (AList.mem_of_subset
              x!_Λ_sub (AList.mem_insert _ |>.mpr (Or.inr (AList.mem_keys.mpr hΛ))))))
          · exact List.mem_union_iff.mpr (Or.inr hX)
        · exact List.mem_union_iff.mpr (Or.inl (List.mem_singleton.mp hvx!' ▸ x!_in))
      · rcases List.mem_union_iff.mp (hS_fv hvS) with hΛ | hX
        · exact List.mem_union_iff.mpr (Or.inl (AList.mem_keys.mp (AList.mem_of_subset
            x!_Λ_sub (AList.mem_insert _ |>.mpr (Or.inr (AList.mem_keys.mpr hΛ))))))
        · exact List.mem_union_iff.mpr (Or.inr hX)
      · exact List.mem_union_iff.mpr (Or.inl (hvx! ▸ x!_in))
    · exact x!_preserves
  case vc3.h_1.isFalse.isFalse.isTrue =>
    rename_i α' hσS hσx_ne hσx_nle hα'_le St hpre
    obtain ⟨rfl, rfl, sub, rfl, hx_fv, hS_fv⟩ := hpre
    mspec loosenAux_prf_state
    mrename_i pre
    mintro ∀St₁
    rename_i Sout
    obtain ⟨S!, S!_spec⟩ := Sout
    mpure pre
    obtain ⟨S!_le, S!_Λ_sub, S!_fresh, S!_not_used, S!_used_sub,
      S!_keys_sub, S!_preserves, S!_fv_sub⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, hd_fvc, hd_used, hd_types⟩ := pred
    mspec Std.Do.Spec.pure
    mpure_intro
    rw [hd_types, hd_used, hd_fvc]
    have S!_in : S! ∈ AList.keys St₁.types :=
      AList.mem_keys.mp (AList.mem_of_subset S!_Λ_sub (AList.mem_insert _ |>.mpr (Or.inl rfl)))
    and_intros
    · exact S!_le
    · exact AList.subset_trans
        (SMT.TypeContext.entries_subset_insert_of_notMem S!_fresh) S!_Λ_sub
    · exact S!_used_sub
    · exact S!_keys_sub
    · intro v hv
      simp only [SMT.fv, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with hvspec | hvS! | hvx
      · have hmem := S!_fv_sub hvspec
        rw [List.mem_union_iff] at hmem
        rcases hmem with hvS | hvS!'
        · rcases List.mem_union_iff.mp (hS_fv hvS) with hΛ | hX
          · exact List.mem_union_iff.mpr (Or.inl (AList.mem_keys.mp (AList.mem_of_subset
              S!_Λ_sub (AList.mem_insert _ |>.mpr (Or.inr (AList.mem_keys.mpr hΛ))))))
          · exact List.mem_union_iff.mpr (Or.inr hX)
        · exact List.mem_union_iff.mpr (Or.inl (List.mem_singleton.mp hvS!' ▸ S!_in))
      · exact List.mem_union_iff.mpr (Or.inl (hvS! ▸ S!_in))
      · rcases List.mem_union_iff.mp (hx_fv hvx) with hΛ | hX
        · exact List.mem_union_iff.mpr (Or.inl (AList.mem_keys.mp (AList.mem_of_subset
            S!_Λ_sub (AList.mem_insert _ |>.mpr (Or.inr (AList.mem_keys.mpr hΛ))))))
        · exact List.mem_union_iff.mpr (Or.inr hX)
    · exact S!_preserves
  case vc4.h_2.h_1.isTrue.isTrue =>
    rename_i α' β' hσS α β hσx hα_le hβ_le St hpre
    obtain ⟨rfl, rfl, sub, rfl, hx_fv, hS_fv⟩ := hpre
    mspec loosenAux_prf_state
    mrename_i pre
    mintro ∀St₁
    rename_i xout
    obtain ⟨x!, x!_spec⟩ := xout
    mpure pre
    obtain ⟨x!_le, x!_Λ_sub, x!_fresh, x!_not_used, x!_used_sub,
      x!_keys_sub, x!_preserves, x!_fv_sub⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, hd_fvc, hd_used, hd_types⟩ := pred
    mspec Std.Do.Spec.pure
    mpure_intro
    rw [hd_types, hd_used, hd_fvc]
    have x!_in : x! ∈ AList.keys St₁.types :=
      AList.mem_keys.mp (AList.mem_of_subset x!_Λ_sub (AList.mem_insert _ |>.mpr (Or.inl rfl)))
    and_intros
    · exact x!_le
    · exact AList.subset_trans
        (SMT.TypeContext.entries_subset_insert_of_notMem x!_fresh) x!_Λ_sub
    · exact x!_used_sub
    · exact x!_keys_sub
    · intro v hv
      simp only [SMT.fv, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with hvspec | (hvS | hvx!a) | hvx!b
      · have hmem := x!_fv_sub hvspec
        rw [List.mem_union_iff] at hmem
        rcases hmem with hvx | hvx!'
        · rcases List.mem_union_iff.mp (hx_fv hvx) with hΛ | hX
          · exact List.mem_union_iff.mpr (Or.inl (AList.mem_keys.mp (AList.mem_of_subset
              x!_Λ_sub (AList.mem_insert _ |>.mpr (Or.inr (AList.mem_keys.mpr hΛ))))))
          · exact List.mem_union_iff.mpr (Or.inr hX)
        · exact List.mem_union_iff.mpr (Or.inl (List.mem_singleton.mp hvx!' ▸ x!_in))
      · rcases List.mem_union_iff.mp (hS_fv hvS) with hΛ | hX
        · exact List.mem_union_iff.mpr (Or.inl (AList.mem_keys.mp (AList.mem_of_subset
            x!_Λ_sub (AList.mem_insert _ |>.mpr (Or.inr (AList.mem_keys.mpr hΛ))))))
        · exact List.mem_union_iff.mpr (Or.inr hX)
      · exact List.mem_union_iff.mpr (Or.inl (hvx!a ▸ x!_in))
      · exact List.mem_union_iff.mpr (Or.inl (hvx!b ▸ x!_in))
    · exact x!_preserves
  case vc5.h_2.h_1.isTrue.isFalse.isTrue =>
    rename_i α' β' hσS α β hσx hα_le hβ_nle hβ'_le St hpre
    obtain ⟨rfl, rfl, sub, rfl, hx_fv, hS_fv⟩ := hpre
    mspec loosenAux_prf_state
    mrename_i prex
    mintro ∀St₁
    rename_i xout
    obtain ⟨x!, x!_spec⟩ := xout
    mpure prex
    obtain ⟨x!_le, x!_Λ_sub, x!_fresh, x!_not_used, x!_used_sub,
      x!_keys_sub, x!_preserves, x!_fv_sub⟩ := prex
    mspec SMT.declareConst_spec
    mrename_i predx
    mintro ∀St₁d
    mpure predx
    obtain ⟨_, _, hdx_fvc, hdx_used, hdx_types⟩ := predx
    have St₁d_keys_sub : AList.keys St₁d.types ⊆ St₁d.env.usedVars := by
      rw [hdx_types, hdx_used]; exact x!_keys_sub
    mspec loosenAux_prf_state
    mrename_i preS
    mintro ∀St₂
    rename_i Sout
    obtain ⟨S!, S!_spec⟩ := Sout
    mpure preS
    obtain ⟨S!_le, S!_Λ_sub, S!_fresh, S!_not_used, S!_used_sub,
      S!_keys_sub, S!_preserves, S!_fv_sub⟩ := preS
    mspec SMT.declareConst_spec
    mrename_i predS
    mintro ∀St₂d
    mpure predS
    obtain ⟨_, _, hdS_fvc, hdS_used, hdS_types⟩ := predS
    mspec Std.Do.Spec.pure
    mpure_intro
    rw [hdS_types, hdS_used, hdS_fvc]
    have S!_in_St₂ : S! ∈ St₂.types :=
      AList.mem_of_subset S!_Λ_sub (AList.mem_insert _ |>.mpr (Or.inl rfl))
    have St₁_to_St₂ : St₁.types ⊆ St₂.types := by
      have h₁ : St₁d.types ⊆ St₂.types :=
        AList.subset_trans
          (SMT.TypeContext.entries_subset_insert_of_notMem S!_fresh) S!_Λ_sub
      rwa [hdx_types] at h₁
    have Λ_to_St₂ : St.types ⊆ St₂.types :=
      AList.subset_trans
        (SMT.TypeContext.entries_subset_insert_of_notMem x!_fresh)
        (AList.subset_trans x!_Λ_sub St₁_to_St₂)
    have x!_in_St₂ : x! ∈ St₂.types :=
      AList.mem_of_subset St₁_to_St₂
        (AList.mem_of_subset x!_Λ_sub (AList.mem_insert _ |>.mpr (Or.inl rfl)))
    and_intros
    · exact le_trans x!_le (hdx_fvc ▸ S!_le)
    · exact Λ_to_St₂
    · exact fun v hv => S!_used_sub (hdx_used ▸ x!_used_sub hv)
    · exact S!_keys_sub
    · intro v hv
      simp only [SMT.fv, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with (hvxspec | hvSspec) | ((hvS! | hvx!) | hvxsnd)
      · have hmem := x!_fv_sub hvxspec
        rw [List.mem_union_iff] at hmem
        rcases hmem with hvx | hvx!'
        · simp only [SMT.fv] at hvx
          rcases List.mem_union_iff.mp (hx_fv hvx) with hΛ | hX
          · exact List.mem_union_iff.mpr (Or.inl (AList.mem_keys.mp (AList.mem_of_subset
              Λ_to_St₂ (AList.mem_keys.mpr hΛ))))
          · exact List.mem_union_iff.mpr (Or.inr hX)
        · exact List.mem_union_iff.mpr (Or.inl
            (List.mem_singleton.mp hvx!' ▸ AList.mem_keys.mp x!_in_St₂))
      · have hmem := S!_fv_sub hvSspec
        rw [List.mem_union_iff] at hmem
        rcases hmem with hvS | hvS!'
        · rcases List.mem_union_iff.mp (hS_fv hvS) with hΛ | hX
          · exact List.mem_union_iff.mpr (Or.inl (AList.mem_keys.mp (AList.mem_of_subset
              Λ_to_St₂ (AList.mem_keys.mpr hΛ))))
          · exact List.mem_union_iff.mpr (Or.inr hX)
        · exact List.mem_union_iff.mpr (Or.inl
            (List.mem_singleton.mp hvS!' ▸ AList.mem_keys.mp S!_in_St₂))
      · exact List.mem_union_iff.mpr (Or.inl (hvS! ▸ AList.mem_keys.mp S!_in_St₂))
      · exact List.mem_union_iff.mpr (Or.inl (hvx! ▸ AList.mem_keys.mp x!_in_St₂))
      · rcases List.mem_union_iff.mp (hx_fv hvxsnd) with hΛ | hX
        · exact List.mem_union_iff.mpr (Or.inl (AList.mem_keys.mp (AList.mem_of_subset
            Λ_to_St₂ (AList.mem_keys.mpr hΛ))))
        · exact List.mem_union_iff.mpr (Or.inr hX)
    · intro v hv hΛ
      have hv_St₁d : v ∉ St₁d.types := by
        rw [hdx_types]; exact x!_preserves v hv hΛ
      have hv_St₁d_used : v ∈ St₁d.env.usedVars := by
        rw [hdx_used]; exact x!_used_sub hv
      exact S!_preserves v hv_St₁d_used hv_St₁d
  case vc6.h_2.h_1.isFalse.isTrue.isTrue =>
    rename_i α' β' hσS α β hσx hα_nle hα'_le hβ_le St hpre
    obtain ⟨rfl, rfl, sub, rfl, hx_fv, hS_fv⟩ := hpre
    mspec loosenAux_prf_state
    mrename_i prey
    mintro ∀St₁
    rename_i yout
    obtain ⟨y!, y!_spec⟩ := yout
    mpure prey
    obtain ⟨y!_le, y!_Λ_sub, y!_fresh, y!_not_used, y!_used_sub,
      y!_keys_sub, y!_preserves, y!_fv_sub⟩ := prey
    mspec SMT.declareConst_spec
    mrename_i predy
    mintro ∀St₁d
    mpure predy
    obtain ⟨_, _, hdy_fvc, hdy_used, hdy_types⟩ := predy
    have St₁d_keys_sub : AList.keys St₁d.types ⊆ St₁d.env.usedVars := by
      rw [hdy_types, hdy_used]; exact y!_keys_sub
    mspec loosenAux_prf_state
    mrename_i preS
    mintro ∀St₂
    rename_i Sout
    obtain ⟨S!, S!_spec⟩ := Sout
    mpure preS
    obtain ⟨S!_le, S!_Λ_sub, S!_fresh, S!_not_used, S!_used_sub,
      S!_keys_sub, S!_preserves, S!_fv_sub⟩ := preS
    mspec SMT.declareConst_spec
    mrename_i predS
    mintro ∀St₂d
    mpure predS
    obtain ⟨_, _, hdS_fvc, hdS_used, hdS_types⟩ := predS
    mspec Std.Do.Spec.pure
    mpure_intro
    rw [hdS_types, hdS_used, hdS_fvc]
    have S!_in_St₂ : S! ∈ St₂.types :=
      AList.mem_of_subset S!_Λ_sub (AList.mem_insert _ |>.mpr (Or.inl rfl))
    have St₁_to_St₂ : St₁.types ⊆ St₂.types := by
      have h₁ : St₁d.types ⊆ St₂.types :=
        AList.subset_trans
          (SMT.TypeContext.entries_subset_insert_of_notMem S!_fresh) S!_Λ_sub
      rwa [hdy_types] at h₁
    have Λ_to_St₂ : St.types ⊆ St₂.types :=
      AList.subset_trans
        (SMT.TypeContext.entries_subset_insert_of_notMem y!_fresh)
        (AList.subset_trans y!_Λ_sub St₁_to_St₂)
    have y!_in_St₂ : y! ∈ St₂.types :=
      AList.mem_of_subset St₁_to_St₂
        (AList.mem_of_subset y!_Λ_sub (AList.mem_insert _ |>.mpr (Or.inl rfl)))
    and_intros
    · exact le_trans y!_le (hdy_fvc ▸ S!_le)
    · exact Λ_to_St₂
    · exact fun v hv => S!_used_sub (hdy_used ▸ y!_used_sub hv)
    · exact S!_keys_sub
    · intro v hv
      simp only [SMT.fv, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with (hvyspec | hvSspec) | ((hvS! | hvxfst) | hvy!)
      · have hmem := y!_fv_sub hvyspec
        rw [List.mem_union_iff] at hmem
        rcases hmem with hvx | hvy!'
        · simp only [SMT.fv] at hvx
          rcases List.mem_union_iff.mp (hx_fv hvx) with hΛ | hX
          · exact List.mem_union_iff.mpr (Or.inl (AList.mem_keys.mp (AList.mem_of_subset
              Λ_to_St₂ (AList.mem_keys.mpr hΛ))))
          · exact List.mem_union_iff.mpr (Or.inr hX)
        · exact List.mem_union_iff.mpr (Or.inl
            (List.mem_singleton.mp hvy!' ▸ AList.mem_keys.mp y!_in_St₂))
      · have hmem := S!_fv_sub hvSspec
        rw [List.mem_union_iff] at hmem
        rcases hmem with hvS | hvS!'
        · rcases List.mem_union_iff.mp (hS_fv hvS) with hΛ | hX
          · exact List.mem_union_iff.mpr (Or.inl (AList.mem_keys.mp (AList.mem_of_subset
              Λ_to_St₂ (AList.mem_keys.mpr hΛ))))
          · exact List.mem_union_iff.mpr (Or.inr hX)
        · exact List.mem_union_iff.mpr (Or.inl
            (List.mem_singleton.mp hvS!' ▸ AList.mem_keys.mp S!_in_St₂))
      · exact List.mem_union_iff.mpr (Or.inl (hvS! ▸ AList.mem_keys.mp S!_in_St₂))
      · rcases List.mem_union_iff.mp (hx_fv hvxfst) with hΛ | hX
        · exact List.mem_union_iff.mpr (Or.inl (AList.mem_keys.mp (AList.mem_of_subset
            Λ_to_St₂ (AList.mem_keys.mpr hΛ))))
        · exact List.mem_union_iff.mpr (Or.inr hX)
      · exact List.mem_union_iff.mpr (Or.inl (hvy! ▸ AList.mem_keys.mp y!_in_St₂))
    · intro v hv hΛ
      have hv_St₁d : v ∉ St₁d.types := by
        rw [hdy_types]; exact y!_preserves v hv hΛ
      have hv_St₁d_used : v ∈ St₁d.env.usedVars := by
        rw [hdy_used]; exact y!_used_sub hv
      exact S!_preserves v hv_St₁d_used hv_St₁d
  case vc7.h_2.h_1.isFalse.isTrue.isFalse.isTrue =>
    rename_i α' β' hσS α β hσx hα_nle hα'_le hβ_nle hβ'_le St hpre
    obtain ⟨rfl, rfl, sub, rfl, hx_fv, hS_fv⟩ := hpre
    mspec loosenAux_prf_state
    mrename_i pre
    mintro ∀St₁
    rename_i Sout
    obtain ⟨S!, S!_spec⟩ := Sout
    mpure pre
    obtain ⟨S!_le, S!_Λ_sub, S!_fresh, S!_not_used, S!_used_sub,
      S!_keys_sub, S!_preserves, S!_fv_sub⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, hd_fvc, hd_used, hd_types⟩ := pred
    mspec Std.Do.Spec.pure
    mpure_intro
    rw [hd_types, hd_used, hd_fvc]
    have S!_in : S! ∈ AList.keys St₁.types :=
      AList.mem_keys.mp (AList.mem_of_subset S!_Λ_sub (AList.mem_insert _ |>.mpr (Or.inl rfl)))
    and_intros
    · exact S!_le
    · exact AList.subset_trans
        (SMT.TypeContext.entries_subset_insert_of_notMem S!_fresh) S!_Λ_sub
    · exact S!_used_sub
    · exact S!_keys_sub
    · intro v hv
      simp only [SMT.fv, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with hvspec | (hvS! | hvxfst) | hvxsnd
      · have hmem := S!_fv_sub hvspec
        rw [List.mem_union_iff] at hmem
        rcases hmem with hvS | hvS!'
        · rcases List.mem_union_iff.mp (hS_fv hvS) with hΛ | hX
          · exact List.mem_union_iff.mpr (Or.inl (AList.mem_keys.mp (AList.mem_of_subset
              S!_Λ_sub (AList.mem_insert _ |>.mpr (Or.inr (AList.mem_keys.mpr hΛ))))))
          · exact List.mem_union_iff.mpr (Or.inr hX)
        · exact List.mem_union_iff.mpr (Or.inl (List.mem_singleton.mp hvS!' ▸ S!_in))
      · exact List.mem_union_iff.mpr (Or.inl (hvS! ▸ S!_in))
      · rcases List.mem_union_iff.mp (hx_fv hvxfst) with hΛ | hX
        · exact List.mem_union_iff.mpr (Or.inl (AList.mem_keys.mp (AList.mem_of_subset
            S!_Λ_sub (AList.mem_insert _ |>.mpr (Or.inr (AList.mem_keys.mpr hΛ))))))
        · exact List.mem_union_iff.mpr (Or.inr hX)
      · rcases List.mem_union_iff.mp (hx_fv hvxsnd) with hΛ | hX
        · exact List.mem_union_iff.mpr (Or.inl (AList.mem_keys.mp (AList.mem_of_subset
            S!_Λ_sub (AList.mem_insert _ |>.mpr (Or.inr (AList.mem_keys.mpr hΛ))))))
        · exact List.mem_union_iff.mpr (Or.inr hX)
    · exact S!_preserves

/-! ### Cast-helper `declarations`-delta spec for `castMembership`

`castMembership` is the only cast helper invoked by the `all` encoder.  It calls
`loosenAux_prf` (which leaves `declarations` untouched, `loosenAux_prf_decls`)
and `declareConst` (which `concat`s a single `declare_const`).  Hence its
`declarations` delta `Δ` is a list of `declare_const` instructions only —
`specBodies Δ = []` — and the encoded term's free variables stay within
`fv x ∪ fv S ∪ declVars Δ` (the loosening helper's intermediate `freshVar`
constants do *not* leak into the result term, by `loosenAux_prf_state`'s
`fv x!_spec ⊆ fv x ∪ {x!}` conjunct, and `x!` is exactly the `declareConst`ed
name).  This is the sharp invariant the `all` case needs: combined with the
`ex_binders` foldr-removal of `declVars`, it places the encoded body's free
variables inside the reverted final context. -/

set_option maxHeartbeats 4000000 in
/-- Combined `loosenAux_prf` spec: the structural `LoosenAuxStatePost` together
with `declarations`-preservation, so the cast-helper delta specs can `mspec` a
single triple. -/
theorem loosenAux_prf_state_decls
    {α β : SMTType} (c : α ~> β) {Λ : SMT.TypeContext} {n : ℕ}
    {used : List SMT.𝒱} {name : String} {x : SMT.Term} {decl : SMT.Chunk} :
    ⦃ fun (⟨E, Λ'⟩ : EncoderState) ↦
        ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ AList.keys Λ ⊆ E.usedVars ∧ E.usedVars = used ∧
          E.declarations = decl⌝ ⦄
    loosenAux_prf name c x
    ⦃ ⇓? (⟨x!, x!_spec⟩ : SMT.𝒱 × SMT.Term) (⟨E', Γ'⟩ : EncoderState) => ⌜
      n ≤ E'.freshvarsc ∧
      Λ.insert x! β ⊆ Γ' ∧
      x! ∉ Λ ∧
      x! ∉ used ∧
      used ⊆ E'.usedVars ∧
      AList.keys Γ' ⊆ E'.usedVars ∧
      (∀ v ∈ used, v ∉ Λ → v ∉ Γ') ∧
      SMT.fv x!_spec ⊆ SMT.fv x ∪ {x!} ∧
      E'.declarations = decl ⌝⦄ := by
  have hst : Std.Do.Triple (loosenAux_prf name c x)
      (LoosenAuxStatePre Λ n used) (LoosenAuxStatePost β Λ n used x) :=
    loosenAux_prf_state c
  have hde : Std.Do.Triple (loosenAux_prf name c x)
      (fun (⟨E, _⟩ : EncoderState) ↦ ⌜E.declarations = decl⌝)
      (⇓? _ (⟨E, _⟩ : EncoderState) => ⌜E.declarations = decl⌝) :=
    loosenAux_prf_decls c
  have hand := Std.Do.Triple.and (loosenAux_prf name c x) hst hde
  mintro pre ∀S
  mpure pre
  obtain ⟨h1, h2, h3, h4, h5⟩ := pre
  mspec hand
  mrename_i hpost
  mintro ∀S'
  mpure hpost
  mpure_intro
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8⟩, hdecl⟩ := hpost
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, hdecl⟩

set_option maxHeartbeats 4000000 in
/-- `castMembership`'s `declarations` delta is a `declare_const`-only chunk
(`specBodies Δ = []`), and the encoded membership term's free variables live in
`fv x ∪ fv S ∪ declVars Δ`. -/
theorem castMembership_decl
    (x S : SMT.Term) (σx σS : SMTType) {Λ : SMT.TypeContext} {n : ℕ}
    {used : List SMT.𝒱} {decl : SMT.Chunk} :
    ⦃ fun (⟨E, Λ'⟩ : EncoderState) ↦
        ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ AList.keys Λ ⊆ E.usedVars ∧ E.usedVars = used ∧
          E.declarations = decl⌝ ⦄
    castMembership (x, σx) (S, σS)
    ⦃ ⇓? (⟨t', _σ⟩ : SMT.Term × SMTType) (⟨E', Γ'⟩ : EncoderState) => ⌜
      ∃ Dlt : SMT.Chunk,
        E'.declarations = decl ++ Dlt ∧
        specBodies Dlt = [] ∧
        SMT.fv t' ⊆ SMT.fv x ∪ SMT.fv S ∪ declVars Dlt ⌝⦄ := by
  unfold castMembership
  mvcgen
  case vc1.h_1.isTrue =>
    rename_i α' hσS hσx St hpre
    obtain ⟨rfl, rfl, sub, rfl, rfl⟩ := hpre
    refine ⟨[], by simp, by simp, ?_⟩
    intro v hv
    simp only [SMT.fv, List.mem_append, declVars_nil, List.mem_union_iff,
      List.not_mem_nil, or_false] at hv ⊢
    tauto
  case vc2.h_1.isFalse.isTrue =>
    rename_i α' hσS hσx_ne hσx_le St hpre
    obtain ⟨rfl, rfl, sub, rfl, rfl⟩ := hpre
    mspec loosenAux_prf_state_decls
    mrename_i pre
    mintro ∀St₁
    rename_i xout
    obtain ⟨x!, x!_spec⟩ := xout
    mpure pre
    obtain ⟨x!_le, x!_Λ_sub, x!_fresh, x!_not_used, x!_used_sub,
      x!_keys_sub, x!_preserves, x!_fv_sub, x!_decl⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, _, _⟩ := pred
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨[.declare_const x! α'], ?_, by simp, ?_⟩
    · rw [hd_decl, x!_decl, List.concat_eq_append]
    · intro v hv
      simp only [SMT.fv, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        declVars_declare_const, List.mem_union_iff, List.mem_singleton] at hv ⊢
      have hsp : v ∈ SMT.fv x!_spec → v ∈ SMT.fv x ∨ v = x! := by
        intro h
        rcases List.mem_union_iff.mp (x!_fv_sub h) with hm | hm
        · exact Or.inl hm
        · exact Or.inr (List.mem_singleton.mp hm)
      tauto
  case vc3.h_1.isFalse.isFalse.isTrue =>
    rename_i α' hσS hσx_ne hσx_nle hα'_le St hpre
    obtain ⟨rfl, rfl, sub, rfl, rfl⟩ := hpre
    mspec loosenAux_prf_state_decls
    mrename_i pre
    mintro ∀St₁
    rename_i Sout
    obtain ⟨S!, S!_spec⟩ := Sout
    mpure pre
    obtain ⟨S!_le, S!_Λ_sub, S!_fresh, S!_not_used, S!_used_sub,
      S!_keys_sub, S!_preserves, S!_fv_sub, S!_decl⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, _, _⟩ := pred
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨[.declare_const S! (.fun σx .bool)], ?_, by simp, ?_⟩
    · rw [hd_decl, S!_decl, List.concat_eq_append]
    · intro v hv
      simp only [SMT.fv, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        declVars_declare_const, List.mem_union_iff, List.mem_singleton] at hv ⊢
      have hsp : v ∈ SMT.fv S!_spec → v ∈ SMT.fv S ∨ v = S! := by
        intro h
        rcases List.mem_union_iff.mp (S!_fv_sub h) with hm | hm
        · exact Or.inl hm
        · exact Or.inr (List.mem_singleton.mp hm)
      tauto
  case vc4.h_2.h_1.isTrue.isTrue =>
    rename_i α' β' hσS α β hσx hα_le hβ_le St hpre
    obtain ⟨rfl, rfl, sub, rfl, rfl⟩ := hpre
    mspec loosenAux_prf_state_decls
    mrename_i pre
    mintro ∀St₁
    rename_i xout
    obtain ⟨x!, x!_spec⟩ := xout
    mpure pre
    obtain ⟨x!_le, x!_Λ_sub, x!_fresh, x!_not_used, x!_used_sub,
      x!_keys_sub, x!_preserves, x!_fv_sub, x!_decl⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, _, _⟩ := pred
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨[.declare_const x! (.pair α' β')], ?_, by simp, ?_⟩
    · rw [hd_decl, x!_decl, List.concat_eq_append]
    · intro v hv
      simp only [SMT.fv, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        declVars_declare_const, List.mem_union_iff, List.mem_singleton] at hv ⊢
      have hsp : v ∈ SMT.fv x!_spec → v ∈ SMT.fv x ∨ v = x! := by
        intro h
        rcases List.mem_union_iff.mp (x!_fv_sub h) with hm | hm
        · exact Or.inl hm
        · exact Or.inr (List.mem_singleton.mp hm)
      tauto
  case vc5.h_2.h_1.isTrue.isFalse.isTrue =>
    rename_i α' β' hσS α β hσx hα_le hβ_nle hβ'_le St hpre
    obtain ⟨rfl, rfl, sub, rfl, rfl⟩ := hpre
    mspec loosenAux_prf_state_decls
    mrename_i prex
    mintro ∀St₁
    rename_i xout
    obtain ⟨x!, x!_spec⟩ := xout
    mpure prex
    obtain ⟨x!_le, x!_Λ_sub, x!_fresh, x!_not_used, x!_used_sub,
      x!_keys_sub, x!_preserves, x!_fv_sub, x!_decl⟩ := prex
    mspec SMT.declareConst_spec
    mrename_i predx
    mintro ∀St₁d
    mpure predx
    obtain ⟨hdx_decl, _, _, hdx_used, hdx_types⟩ := predx
    mspec (loosenAux_prf_state_decls (c := _) (used := St₁d.env.usedVars)
      (decl := St₁d.env.declarations))
    case pre =>
      mpure_intro
      refine ⟨trivial, trivial, ?_, trivial, trivial⟩
      rw [hdx_types, hdx_used]; exact x!_keys_sub
    mrename_i preS
    mintro ∀St₂
    rename_i Sout
    obtain ⟨S!, S!_spec⟩ := Sout
    mpure preS
    obtain ⟨S!_le, S!_Λ_sub, S!_fresh, S!_not_used, S!_used_sub,
      S!_keys_sub, S!_preserves, S!_fv_sub, S!_decl⟩ := preS
    mspec SMT.declareConst_spec
    mrename_i predS
    mintro ∀St₂d
    mpure predS
    obtain ⟨hdS_decl, _, _, _, _⟩ := predS
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨[.declare_const x! α'] ++ [.declare_const S! (.fun α' (.option β))],
      ?_, by simp [specBodies], ?_⟩
    · rw [hdS_decl, S!_decl, hdx_decl, x!_decl, List.concat_eq_append, List.concat_eq_append,
        List.append_assoc]
    · intro v hv
      simp only [SMT.fv, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        declVars_append, declVars_declare_const, List.mem_union_iff, List.mem_singleton] at hv ⊢
      have hspx : v ∈ SMT.fv x!_spec → v ∈ SMT.fv x ∨ v = x! := by
        intro h
        rcases List.mem_union_iff.mp (x!_fv_sub h) with hm | hm
        · exact Or.inl (by simpa only [SMT.fv] using hm)
        · exact Or.inr (List.mem_singleton.mp hm)
      have hspS : v ∈ SMT.fv S!_spec → v ∈ SMT.fv S ∨ v = S! := by
        intro h
        rcases List.mem_union_iff.mp (S!_fv_sub h) with hm | hm
        · exact Or.inl hm
        · exact Or.inr (List.mem_singleton.mp hm)
      tauto
  case vc6.h_2.h_1.isFalse.isTrue.isTrue =>
    rename_i α' β' hσS α β hσx hα_nle hα'_le hβ_le St hpre
    obtain ⟨rfl, rfl, sub, rfl, rfl⟩ := hpre
    mspec loosenAux_prf_state_decls
    mrename_i prey
    mintro ∀St₁
    rename_i yout
    obtain ⟨y!, y!_spec⟩ := yout
    mpure prey
    obtain ⟨y!_le, y!_Λ_sub, y!_fresh, y!_not_used, y!_used_sub,
      y!_keys_sub, y!_preserves, y!_fv_sub, y!_decl⟩ := prey
    mspec SMT.declareConst_spec
    mrename_i predy
    mintro ∀St₁d
    mpure predy
    obtain ⟨hdy_decl, _, _, hdy_used, hdy_types⟩ := predy
    mspec (loosenAux_prf_state_decls (c := _) (used := St₁d.env.usedVars)
      (decl := St₁d.env.declarations))
    case pre =>
      mpure_intro
      refine ⟨trivial, trivial, ?_, trivial, trivial⟩
      rw [hdy_types, hdy_used]; exact y!_keys_sub
    mrename_i preS
    mintro ∀St₂
    rename_i Sout
    obtain ⟨S!, S!_spec⟩ := Sout
    mpure preS
    obtain ⟨S!_le, S!_Λ_sub, S!_fresh, S!_not_used, S!_used_sub,
      S!_keys_sub, S!_preserves, S!_fv_sub, S!_decl⟩ := preS
    mspec SMT.declareConst_spec
    mrename_i predS
    mintro ∀St₂d
    mpure predS
    obtain ⟨hdS_decl, _, _, _, _⟩ := predS
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨[.declare_const y! β'] ++ [.declare_const S! (.fun α (.option β'))],
      ?_, by simp [specBodies], ?_⟩
    · rw [hdS_decl, S!_decl, hdy_decl, y!_decl, List.concat_eq_append, List.concat_eq_append,
        List.append_assoc]
    · intro v hv
      simp only [SMT.fv, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        declVars_append, declVars_declare_const, List.mem_union_iff, List.mem_singleton] at hv ⊢
      have hspy : v ∈ SMT.fv y!_spec → v ∈ SMT.fv x ∨ v = y! := by
        intro h
        rcases List.mem_union_iff.mp (y!_fv_sub h) with hm | hm
        · exact Or.inl (by simpa only [SMT.fv] using hm)
        · exact Or.inr (List.mem_singleton.mp hm)
      have hspS : v ∈ SMT.fv S!_spec → v ∈ SMT.fv S ∨ v = S! := by
        intro h
        rcases List.mem_union_iff.mp (S!_fv_sub h) with hm | hm
        · exact Or.inl hm
        · exact Or.inr (List.mem_singleton.mp hm)
      rcases hv with (hy | hSs) | (hSeq | hxf) | hyeq
      · rcases hspy hy with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr (Or.inl h')
      · rcases hspS hSs with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr (Or.inr h')
      · exact Or.inr (Or.inr hSeq)
      · exact Or.inl (Or.inl hxf)
      · exact Or.inr (Or.inl hyeq)
  case vc7.h_2.h_1.isFalse.isTrue.isFalse.isTrue =>
    rename_i α' β' hσS α β hσx hα_nle hα'_le hβ_nle hβ'_le St hpre
    obtain ⟨rfl, rfl, sub, rfl, rfl⟩ := hpre
    mspec loosenAux_prf_state_decls
    mrename_i pre
    mintro ∀St₁
    rename_i Sout
    obtain ⟨S!, S!_spec⟩ := Sout
    mpure pre
    obtain ⟨S!_le, S!_Λ_sub, S!_fresh, S!_not_used, S!_used_sub,
      S!_keys_sub, S!_preserves, S!_fv_sub, S!_decl⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, _, _⟩ := pred
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨[.declare_const S! (.fun α (.option β))], ?_, by simp, ?_⟩
    · rw [hd_decl, S!_decl, List.concat_eq_append]
    · intro v hv
      simp only [SMT.fv, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        declVars_declare_const, List.mem_union_iff, List.mem_singleton] at hv ⊢
      have hsp : v ∈ SMT.fv S!_spec → v ∈ SMT.fv S ∨ v = S! := by
        intro h
        rcases List.mem_union_iff.mp (S!_fv_sub h) with hm | hm
        · exact Or.inl hm
        · exact Or.inr (List.mem_singleton.mp hm)
      tauto

set_option maxHeartbeats 4000000 in
/-- State-context spec for `castEq`, parametrized by an extra var-list `X`
(mirrors `castMembership_state`): the encoded equality term's free variables stay
within `AList.keys Γ' ∪ X` when the inputs' free variables do. -/
theorem castEq_state
    (A B : SMT.Term) (σA σB : SMTType) {Λ : SMT.TypeContext} {n : ℕ}
    {used : List SMT.𝒱} {X : List SMT.𝒱} :
    ⦃ fun (⟨E, Λ'⟩ : EncoderState) ↦
        ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ AList.keys Λ ⊆ E.usedVars ∧ E.usedVars = used ∧
          SMT.fv A ⊆ AList.keys Λ ∪ X ∧ SMT.fv B ⊆ AList.keys Λ ∪ X⌝ ⦄
    castEq (A, σA) (B, σB)
    ⦃ ⇓? (⟨t', _σ⟩ : SMT.Term × SMTType) (⟨E', Γ'⟩ : EncoderState) => ⌜
      n ≤ E'.freshvarsc ∧
      Λ ⊆ Γ' ∧
      used ⊆ E'.usedVars ∧
      AList.keys Γ' ⊆ E'.usedVars ∧
      SMT.fv t' ⊆ AList.keys Γ' ∪ X ∧
      (∀ v ∈ used, v ∉ Λ → v ∉ Γ') ⌝⦄ := by
  unfold castEq
  mvcgen
  · -- σA = σB : direct equality `A =ˢ B`
    rename_i hpre
    obtain ⟨rfl, rfl, sub, rfl, hA_fv, hB_fv⟩ := hpre
    refine ⟨le_refl _, fun _ h => h, fun _ h => h, sub, ?_, fun v hv hΛ hin => hΛ hin⟩
    intro v hv
    simp only [SMT.fv, List.mem_append] at hv
    rcases hv with hv | hv
    · exact hA_fv hv
    · exact hB_fv hv
  · -- σA ⊑ σB : loosen A
    rename_i hpre
    obtain ⟨rfl, rfl, sub, rfl, hA_fv, hB_fv⟩ := hpre
    mspec loosenAux_prf_state
    mrename_i pre
    mintro ∀St₁
    rename_i Aout
    obtain ⟨A!, A!_spec⟩ := Aout
    mpure pre
    obtain ⟨A!_le, A!_Λ_sub, A!_fresh, A!_not_used, A!_used_sub,
      A!_keys_sub, A!_preserves, A!_fv_sub⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, hd_fvc, hd_used, hd_types⟩ := pred
    mspec Std.Do.Spec.pure
    mpure_intro
    rw [hd_types, hd_used, hd_fvc]
    have A!_in : A! ∈ AList.keys St₁.types :=
      AList.mem_keys.mp (AList.mem_of_subset A!_Λ_sub (AList.mem_insert _ |>.mpr (Or.inl rfl)))
    refine ⟨A!_le, AList.subset_trans
      (SMT.TypeContext.entries_subset_insert_of_notMem A!_fresh) A!_Λ_sub,
      A!_used_sub, A!_keys_sub, ?_, A!_preserves⟩
    intro v hv
    simp only [SMT.fv, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with (hvA! | hvB) | hvspec
    · exact List.mem_union_iff.mpr (Or.inl (hvA! ▸ A!_in))
    · rcases List.mem_union_iff.mp (hB_fv hvB) with hΛ | hX
      · exact List.mem_union_iff.mpr (Or.inl (AList.mem_keys.mp (AList.mem_of_subset A!_Λ_sub
          (AList.mem_insert _ |>.mpr (Or.inr (AList.mem_keys.mpr hΛ))))))
      · exact List.mem_union_iff.mpr (Or.inr hX)
    · have hmem := A!_fv_sub hvspec
      rw [List.mem_union_iff] at hmem
      rcases hmem with hA | hA!
      · rcases List.mem_union_iff.mp (hA_fv hA) with hΛ | hX
        · exact List.mem_union_iff.mpr (Or.inl (AList.mem_keys.mp (AList.mem_of_subset A!_Λ_sub
            (AList.mem_insert _ |>.mpr (Or.inr (AList.mem_keys.mpr hΛ))))))
        · exact List.mem_union_iff.mpr (Or.inr hX)
      · exact List.mem_union_iff.mpr (Or.inl (List.mem_singleton.mp hA! ▸ A!_in))
  · -- σB ⊑ σA : loosen B
    rename_i hpre
    obtain ⟨rfl, rfl, sub, rfl, hA_fv, hB_fv⟩ := hpre
    mspec loosenAux_prf_state
    mrename_i pre
    mintro ∀St₁
    rename_i Bout
    obtain ⟨B!, B!_spec⟩ := Bout
    mpure pre
    obtain ⟨B!_le, B!_Λ_sub, B!_fresh, B!_not_used, B!_used_sub,
      B!_keys_sub, B!_preserves, B!_fv_sub⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨_, _, hd_fvc, hd_used, hd_types⟩ := pred
    mspec Std.Do.Spec.pure
    mpure_intro
    rw [hd_types, hd_used, hd_fvc]
    have B!_in : B! ∈ AList.keys St₁.types :=
      AList.mem_keys.mp (AList.mem_of_subset B!_Λ_sub (AList.mem_insert _ |>.mpr (Or.inl rfl)))
    refine ⟨B!_le, AList.subset_trans
      (SMT.TypeContext.entries_subset_insert_of_notMem B!_fresh) B!_Λ_sub,
      B!_used_sub, B!_keys_sub, ?_, B!_preserves⟩
    intro v hv
    simp only [SMT.fv, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with (hvB! | hvA) | hvspec
    · exact List.mem_union_iff.mpr (Or.inl (hvB! ▸ B!_in))
    · rcases List.mem_union_iff.mp (hA_fv hvA) with hΛ | hX
      · exact List.mem_union_iff.mpr (Or.inl (AList.mem_keys.mp (AList.mem_of_subset B!_Λ_sub
          (AList.mem_insert _ |>.mpr (Or.inr (AList.mem_keys.mpr hΛ))))))
      · exact List.mem_union_iff.mpr (Or.inr hX)
    · have hmem := B!_fv_sub hvspec
      rw [List.mem_union_iff] at hmem
      rcases hmem with hB | hB!
      · rcases List.mem_union_iff.mp (hB_fv hB) with hΛ | hX
        · exact List.mem_union_iff.mpr (Or.inl (AList.mem_keys.mp (AList.mem_of_subset B!_Λ_sub
            (AList.mem_insert _ |>.mpr (Or.inr (AList.mem_keys.mpr hΛ))))))
        · exact List.mem_union_iff.mpr (Or.inr hX)
      · exact List.mem_union_iff.mpr (Or.inl (List.mem_singleton.mp hB! ▸ B!_in))

set_option maxHeartbeats 4000000 in
/-- `castEq`'s `declarations` delta is a `declare_const`-only chunk
(`specBodies Δ = []` — `castEq` never calls `addSpec`), and the encoded equality
term's free variables live in `fv A ∪ fv B ∪ declVars Δ`. -/
theorem castEq_decl
    (A B : SMT.Term) (σA σB : SMTType) {Λ : SMT.TypeContext} {n : ℕ}
    {used : List SMT.𝒱} {decl : SMT.Chunk} :
    ⦃ fun (⟨E, Λ'⟩ : EncoderState) ↦
        ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ AList.keys Λ ⊆ E.usedVars ∧ E.usedVars = used ∧
          E.declarations = decl⌝ ⦄
    castEq (A, σA) (B, σB)
    ⦃ ⇓? (⟨t', _σ⟩ : SMT.Term × SMTType) (⟨E', Γ'⟩ : EncoderState) => ⌜
      ∃ Dlt : SMT.Chunk,
        E'.declarations = decl ++ Dlt ∧
        specBodies Dlt = [] ∧
        SMT.fv t' ⊆ SMT.fv A ∪ SMT.fv B ∪ declVars Dlt ⌝⦄ := by
  unfold castEq
  mvcgen
  · -- σA = σB : direct equality `A =ˢ B`
    rename_i hpre
    obtain ⟨rfl, rfl, sub, rfl, rfl⟩ := hpre
    refine ⟨[], by simp, by simp, ?_⟩
    intro v hv
    simp only [SMT.fv, List.mem_append, declVars_nil, List.mem_union_iff,
      List.not_mem_nil, or_false] at hv ⊢
    tauto
  · -- σA ⊑ σB : loosen A
    rename_i hpre
    obtain ⟨rfl, rfl, sub, rfl, rfl⟩ := hpre
    mspec loosenAux_prf_state_decls
    mrename_i pre
    mintro ∀St₁
    rename_i Aout
    obtain ⟨A!, A!_spec⟩ := Aout
    mpure pre
    obtain ⟨A!_le, A!_Λ_sub, A!_fresh, A!_not_used, A!_used_sub,
      A!_keys_sub, A!_preserves, A!_fv_sub, A!_decl⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, _, _⟩ := pred
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨[.declare_const A! σB], ?_, by simp, ?_⟩
    · rw [hd_decl, A!_decl, List.concat_eq_append]
    · intro v hv
      simp only [SMT.fv, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        declVars_declare_const, List.mem_union_iff, List.mem_singleton] at hv ⊢
      have hsp : v ∈ SMT.fv A!_spec → v ∈ SMT.fv A ∨ v = A! := by
        intro h
        rcases List.mem_union_iff.mp (A!_fv_sub h) with hm | hm
        · exact Or.inl hm
        · exact Or.inr (List.mem_singleton.mp hm)
      tauto
  · -- σB ⊑ σA : loosen B
    rename_i hpre
    obtain ⟨rfl, rfl, sub, rfl, rfl⟩ := hpre
    mspec loosenAux_prf_state_decls
    mrename_i pre
    mintro ∀St₁
    rename_i Bout
    obtain ⟨B!, B!_spec⟩ := Bout
    mpure pre
    obtain ⟨B!_le, B!_Λ_sub, B!_fresh, B!_not_used, B!_used_sub,
      B!_keys_sub, B!_preserves, B!_fv_sub, B!_decl⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, _, _⟩ := pred
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨[.declare_const B! σA], ?_, by simp, ?_⟩
    · rw [hd_decl, B!_decl, List.concat_eq_append]
    · intro v hv
      simp only [SMT.fv, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        declVars_declare_const, List.mem_union_iff, List.mem_singleton] at hv ⊢
      have hsp : v ∈ SMT.fv B!_spec → v ∈ SMT.fv B ∨ v = B! := by
        intro h
        rcases List.mem_union_iff.mp (B!_fv_sub h) with hm | hm
        · exact Or.inl hm
        · exact Or.inr (List.mem_singleton.mp hm)
      tauto

set_option maxHeartbeats 4000000 in
/-- `castUnionAux`'s `declarations` delta `Dlt`: the encoded union term's free
variables live in `fv S ∪ fv T ∪ declVars Dlt`, and every `addSpec`-introduced
spec body's free variables stay within the same bound (the loosening helper's
spec `S!_spec` has `fv ⊆ fv S ∪ {S!}` and `S!` is `declareConst`ed). -/
theorem castUnionAux_decl
    {α β : SMTType} (c : α ~> β) (S T : SMT.Term) {Λ : SMT.TypeContext} {n : ℕ}
    {used : List SMT.𝒱} {decl : SMT.Chunk} :
    ⦃ fun (⟨E, Λ'⟩ : EncoderState) ↦
        ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ AList.keys Λ ⊆ E.usedVars ∧ E.usedVars = used ∧
          E.declarations = decl⌝ ⦄
    castUnionAux S T c
    ⦃ ⇓? (⟨t', _σ⟩ : SMT.Term × SMTType) (⟨E', Γ'⟩ : EncoderState) => ⌜
      ∃ Dlt : SMT.Chunk,
        E'.declarations = decl ++ Dlt ∧
        (∀ b ∈ specBodies Dlt, SMT.fv b ⊆ SMT.fv S ∪ SMT.fv T ∪ declVars Dlt) ∧
        SMT.fv t' ⊆ SMT.fv S ∪ SMT.fv T ∪ declVars Dlt ⌝⦄ := by
  cases c with
  | @graph α β α' β' c_α c_β =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl, rfl⟩ := pre
    unfold castUnionAux castUnion.graph
    mspec loosenAux_prf_state_decls
    mrename_i pre
    mintro ∀St₁
    rename_i S!_pair
    obtain ⟨S!, S!_spec⟩ := S!_pair
    mpure pre
    obtain ⟨S!_le, S!_Λ_sub, S!_fresh, S!_not_used, S!_used_sub,
      S!_keys_sub, S!_preserves, S!_fv_sub, S!_decl⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, _, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨hs_decl, _, _, _, _⟩ := pres
    mspec SMT.freshVar_decls
    case post.success =>
      mintro ∀St₂
      mrename_i pref
      mpure pref
      mspec Std.Do.Spec.pure
      mpure_intro
      rename_i x
      refine ⟨[.declare_const S! (.fun (.pair α' β') .bool),
        .define_fun s!"{S!}_spec" .unit .bool S!_spec], ?_, ?_, ?_⟩
      · rw [pref, hs_decl, hd_decl, S!_decl, List.concat_eq_append, List.concat_eq_append,
          List.append_assoc, List.cons_append, List.nil_append]
      · intro b hb
        simp only [specBodies, List.filterMap_cons, List.filterMap_nil] at hb
        rw [List.mem_singleton] at hb
        subst hb
        intro v hv
        simp only [declVars, List.filterMap_cons, List.filterMap_nil, List.mem_union_iff,
          List.mem_singleton] at hv ⊢
        rcases List.mem_union_iff.mp (S!_fv_sub hv) with hm | hm
        · exact Or.inl (Or.inl hm)
        · exact Or.inr (List.mem_singleton.mp hm)
      · intro v hv
        simp only [SMT.fv, List.mem_removeAll_iff, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false, declVars, List.filterMap_cons, List.filterMap_nil,
          List.mem_union_iff] at hv ⊢
        obtain ⟨hv_body, hv_ne_x⟩ := hv
        rcases hv_body with (hvS! | hvx) | (hvT | hvx)
        · exact Or.inr hvS!
        · exact absurd hvx hv_ne_x
        · exact Or.inl (Or.inr hvT)
        · exact absurd hvx hv_ne_x
  | @«fun» α β α' β' hβ c_α c_β =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl, rfl⟩ := pre
    unfold castUnionAux castUnion.fun
    mspec loosenAux_prf_state_decls
    mrename_i pre
    mintro ∀St₁
    rename_i S!_pair
    obtain ⟨S!, S!_spec⟩ := S!_pair
    mpure pre
    obtain ⟨S!_le, S!_Λ_sub, S!_fresh, S!_not_used, S!_used_sub,
      S!_keys_sub, S!_preserves, S!_fv_sub, S!_decl⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, _, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨hs_decl, _, _, _, _⟩ := pres
    split
    · rename_i σ _
      mspec SMT.freshVar_decls
      case post.success =>
        mintro ∀St₂
        mrename_i pref
        mpure pref
        mspec Std.Do.Spec.pure
        mpure_intro
        refine ⟨[.declare_const S! (.fun α' (.option σ)),
          .define_fun s!"{S!}_spec" .unit .bool S!_spec], ?_, ?_, ?_⟩
        · rw [pref, hs_decl, hd_decl, S!_decl, List.concat_eq_append, List.concat_eq_append,
            List.append_assoc, List.cons_append, List.nil_append]
        · intro b hb
          simp only [specBodies, List.filterMap_cons, List.filterMap_nil] at hb
          rw [List.mem_singleton] at hb
          subst hb
          intro v hv
          simp only [declVars, List.filterMap_cons, List.filterMap_nil, List.mem_union_iff,
            List.mem_singleton] at hv ⊢
          rcases List.mem_union_iff.mp (S!_fv_sub hv) with hm | hm
          · exact Or.inl (Or.inl hm)
          · exact Or.inr (List.mem_singleton.mp hm)
        · intro v hv
          simp only [SMT.fv, List.mem_removeAll_iff, List.mem_append, List.mem_cons,
            List.not_mem_nil, or_false, declVars, List.filterMap_cons, List.filterMap_nil,
            List.mem_union_iff] at hv ⊢
          obtain ⟨hv_body, hv_ne_p⟩ := hv
          rcases hv_body with ((hvS! | hvpa) | hvpa') | ((hvT | hvpb) | hvpb')
          · exact Or.inr hvS!
          · exact absurd hvpa hv_ne_p
          · exact absurd hvpa' hv_ne_p
          · exact Or.inl (Or.inr hvT)
          · exact absurd hvpb hv_ne_p
          · exact absurd hvpb' hv_ne_p
    · mvcgen
  | @chpred α α' c_α =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl, rfl⟩ := pre
    unfold castUnionAux castUnion.chpred
    mspec loosenAux_prf_state_decls
    mrename_i pre
    mintro ∀St₁
    rename_i S!_pair
    obtain ⟨S!, S!_spec⟩ := S!_pair
    mpure pre
    obtain ⟨S!_le, S!_Λ_sub, S!_fresh, S!_not_used, S!_used_sub,
      S!_keys_sub, S!_preserves, S!_fv_sub, S!_decl⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, _, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨hs_decl, _, _, _, _⟩ := pres
    mspec SMT.freshVar_decls
    case post.success =>
      mintro ∀St₂
      mrename_i pref
      mpure pref
      mspec Std.Do.Spec.pure
      mpure_intro
      rename_i x
      refine ⟨[.declare_const S! (.fun α' .bool),
        .define_fun s!"{S!}_spec" .unit .bool S!_spec], ?_, ?_, ?_⟩
      · rw [pref, hs_decl, hd_decl, S!_decl, List.concat_eq_append, List.concat_eq_append,
          List.append_assoc, List.cons_append, List.nil_append]
      · intro b hb
        simp only [specBodies, List.filterMap_cons, List.filterMap_nil] at hb
        rw [List.mem_singleton] at hb
        subst hb
        intro v hv
        simp only [declVars, List.filterMap_cons, List.filterMap_nil, List.mem_union_iff,
          List.mem_singleton] at hv ⊢
        rcases List.mem_union_iff.mp (S!_fv_sub hv) with hm | hm
        · exact Or.inl (Or.inl hm)
        · exact Or.inr (List.mem_singleton.mp hm)
      · intro v hv
        simp only [SMT.fv, List.mem_removeAll_iff, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false, declVars, List.filterMap_cons, List.filterMap_nil,
          List.mem_union_iff] at hv ⊢
        obtain ⟨hv_body, hv_ne_x⟩ := hv
        rcases hv_body with (hvS! | hvx) | (hvT | hvx)
        · exact Or.inr hvS!
        · exact absurd hvx hv_ne_x
        · exact Or.inl (Or.inr hvT)
        · exact absurd hvx hv_ne_x
  | @opt α α' c_α =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl, rfl⟩ := pre
    unfold castUnionAux
    mvcgen
  | @pair α β α' β' c_α c_β =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl, rfl⟩ := pre
    unfold castUnionAux
    mvcgen
  | @refl α hα =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl, rfl⟩ := pre
    unfold castUnionAux
    mvcgen

set_option maxHeartbeats 4000000 in
/-- `castInterAux`'s `declarations` delta `Dlt`: the encoded intersection term's
free variables live in `fv S ∪ fv T ∪ declVars Dlt`, and every `addSpec`-
introduced spec body's free variables stay within the same bound. Mirrors
`castUnionAux_decl`. -/
theorem castInterAux_decl
    {α β : SMTType} (c : α ~> β) (S T : SMT.Term) {Λ : SMT.TypeContext} {n : ℕ}
    {used : List SMT.𝒱} {decl : SMT.Chunk} :
    ⦃ fun (⟨E, Λ'⟩ : EncoderState) ↦
        ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ AList.keys Λ ⊆ E.usedVars ∧ E.usedVars = used ∧
          E.declarations = decl⌝ ⦄
    castInterAux S T c
    ⦃ ⇓? (⟨t', _σ⟩ : SMT.Term × SMTType) (⟨E', Γ'⟩ : EncoderState) => ⌜
      ∃ Dlt : SMT.Chunk,
        E'.declarations = decl ++ Dlt ∧
        (∀ b ∈ specBodies Dlt, SMT.fv b ⊆ SMT.fv S ∪ SMT.fv T ∪ declVars Dlt) ∧
        SMT.fv t' ⊆ SMT.fv S ∪ SMT.fv T ∪ declVars Dlt ⌝⦄ := by
  cases c with
  | @graph α β α' β' c_α c_β =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl, rfl⟩ := pre
    unfold castInterAux
    mspec loosenAux_prf_state_decls
    mrename_i pre
    mintro ∀St₁
    rename_i S!_pair
    obtain ⟨S!, S!_spec⟩ := S!_pair
    mpure pre
    obtain ⟨S!_le, S!_Λ_sub, S!_fresh, S!_not_used, S!_used_sub,
      S!_keys_sub, S!_preserves, S!_fv_sub, S!_decl⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, _, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨hs_decl, _, _, _, _⟩ := pres
    mspec SMT.freshVar_decls
    case post.success =>
      mintro ∀St₂
      mrename_i pref
      mpure pref
      mspec Std.Do.Spec.pure
      mpure_intro
      rename_i x
      refine ⟨[.declare_const S! (.fun (.pair α' β') .bool),
        .define_fun s!"{S!}_spec" .unit .bool S!_spec], ?_, ?_, ?_⟩
      · rw [pref, hs_decl, hd_decl, S!_decl, List.concat_eq_append, List.concat_eq_append,
          List.append_assoc, List.cons_append, List.nil_append]
      · intro b hb
        simp only [specBodies, List.filterMap_cons, List.filterMap_nil] at hb
        rw [List.mem_singleton] at hb
        subst hb
        intro v hv
        simp only [declVars, List.filterMap_cons, List.filterMap_nil, List.mem_union_iff,
          List.mem_singleton] at hv ⊢
        rcases List.mem_union_iff.mp (S!_fv_sub hv) with hm | hm
        · exact Or.inl (Or.inl hm)
        · exact Or.inr (List.mem_singleton.mp hm)
      · intro v hv
        simp only [SMT.fv, List.mem_removeAll_iff, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false, declVars, List.filterMap_cons, List.filterMap_nil,
          List.mem_union_iff] at hv ⊢
        obtain ⟨hv_body, hv_ne_x⟩ := hv
        rcases hv_body with (hvS! | hvx) | (hvT | hvx)
        · exact Or.inr hvS!
        · exact absurd hvx hv_ne_x
        · exact Or.inl (Or.inr hvT)
        · exact absurd hvx hv_ne_x
  | @«fun» α β α' β' hβ c_α c_β =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl, rfl⟩ := pre
    unfold castInterAux
    mspec loosenAux_prf_state_decls
    mrename_i pre
    mintro ∀St₁
    rename_i S!_pair
    obtain ⟨S!, S!_spec⟩ := S!_pair
    mpure pre
    obtain ⟨S!_le, S!_Λ_sub, S!_fresh, S!_not_used, S!_used_sub,
      S!_keys_sub, S!_preserves, S!_fv_sub, S!_decl⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, _, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨hs_decl, _, _, _, _⟩ := pres
    split
    · rename_i σ _
      mspec SMT.freshVar_decls
      case post.success =>
        mintro ∀St₂
        mrename_i pref
        mpure pref
        mspec Std.Do.Spec.pure
        mpure_intro
        refine ⟨[.declare_const S! (.fun α' (.option σ)),
          .define_fun s!"{S!}_spec" .unit .bool S!_spec], ?_, ?_, ?_⟩
        · rw [pref, hs_decl, hd_decl, S!_decl, List.concat_eq_append, List.concat_eq_append,
            List.append_assoc, List.cons_append, List.nil_append]
        · intro b hb
          simp only [specBodies, List.filterMap_cons, List.filterMap_nil] at hb
          rw [List.mem_singleton] at hb
          subst hb
          intro v hv
          simp only [declVars, List.filterMap_cons, List.filterMap_nil, List.mem_union_iff,
            List.mem_singleton] at hv ⊢
          rcases List.mem_union_iff.mp (S!_fv_sub hv) with hm | hm
          · exact Or.inl (Or.inl hm)
          · exact Or.inr (List.mem_singleton.mp hm)
        · intro v hv
          simp only [SMT.fv, List.mem_removeAll_iff, List.mem_append, List.mem_cons,
            List.not_mem_nil, or_false, declVars, List.filterMap_cons, List.filterMap_nil,
            List.mem_union_iff] at hv ⊢
          obtain ⟨hv_body, hv_ne_p⟩ := hv
          rcases hv_body with ((hvS! | hvpa) | hvpa') | ((hvT | hvpb) | hvpb')
          · exact Or.inr hvS!
          · exact absurd hvpa hv_ne_p
          · exact absurd hvpa' hv_ne_p
          · exact Or.inl (Or.inr hvT)
          · exact absurd hvpb hv_ne_p
          · exact absurd hvpb' hv_ne_p
    · mvcgen
  | @chpred α α' c_α =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl, rfl⟩ := pre
    unfold castInterAux
    mspec loosenAux_prf_state_decls
    mrename_i pre
    mintro ∀St₁
    rename_i S!_pair
    obtain ⟨S!, S!_spec⟩ := S!_pair
    mpure pre
    obtain ⟨S!_le, S!_Λ_sub, S!_fresh, S!_not_used, S!_used_sub,
      S!_keys_sub, S!_preserves, S!_fv_sub, S!_decl⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, _, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨hs_decl, _, _, _, _⟩ := pres
    mspec SMT.freshVar_decls
    case post.success =>
      mintro ∀St₂
      mrename_i pref
      mpure pref
      mspec Std.Do.Spec.pure
      mpure_intro
      rename_i x
      refine ⟨[.declare_const S! (.fun α' .bool),
        .define_fun s!"{S!}_spec" .unit .bool S!_spec], ?_, ?_, ?_⟩
      · rw [pref, hs_decl, hd_decl, S!_decl, List.concat_eq_append, List.concat_eq_append,
          List.append_assoc, List.cons_append, List.nil_append]
      · intro b hb
        simp only [specBodies, List.filterMap_cons, List.filterMap_nil] at hb
        rw [List.mem_singleton] at hb
        subst hb
        intro v hv
        simp only [declVars, List.filterMap_cons, List.filterMap_nil, List.mem_union_iff,
          List.mem_singleton] at hv ⊢
        rcases List.mem_union_iff.mp (S!_fv_sub hv) with hm | hm
        · exact Or.inl (Or.inl hm)
        · exact Or.inr (List.mem_singleton.mp hm)
      · intro v hv
        simp only [SMT.fv, List.mem_removeAll_iff, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false, declVars, List.filterMap_cons, List.filterMap_nil,
          List.mem_union_iff] at hv ⊢
        obtain ⟨hv_body, hv_ne_x⟩ := hv
        rcases hv_body with (hvS! | hvx) | (hvT | hvx)
        · exact Or.inr hvS!
        · exact absurd hvx hv_ne_x
        · exact Or.inl (Or.inr hvT)
        · exact absurd hvx hv_ne_x
  | @opt α α' c_α =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl, rfl⟩ := pre
    unfold castInterAux
    mvcgen
  | @pair α β α' β' c_α c_β =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl, rfl⟩ := pre
    unfold castInterAux
    mvcgen
  | @refl α hα =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, sub, rfl, rfl⟩ := pre
    unfold castInterAux
    mvcgen

set_option maxHeartbeats 4000000 in
/-- `castApp`'s `declarations` delta `Dlt`: the encoded application term's free
variables live in `fv f ∪ fv x ∪ declVars Dlt`, and every `addSpec`-introduced
spec body's free variables stay within the same bound.  The relation-to-function
casts (`.fun (.pair τ σ) .bool` arm) declare two consts (the loosened input and
the functionalised helper) and emit two spec bodies (the loosening spec and the
functionalisation `forall`), all of whose extra free variables are exactly the
declared constants. -/
theorem castApp_decl
    (f x : SMT.Term) (σf σx : SMTType) {Λ : SMT.TypeContext} {n : ℕ}
    {used : List SMT.𝒱} {decl : SMT.Chunk} :
    ⦃ fun (⟨E, Λ'⟩ : EncoderState) ↦
        ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ AList.keys Λ ⊆ E.usedVars ∧ E.usedVars = used ∧
          E.declarations = decl⌝ ⦄
    castApp (f, σf) (x, σx)
    ⦃ ⇓? (⟨t', _σ⟩ : SMT.Term × SMTType) (⟨E', Γ'⟩ : EncoderState) => ⌜
      ∃ Dlt : SMT.Chunk,
        E'.declarations = decl ++ Dlt ∧
        (∀ b ∈ specBodies Dlt, SMT.fv b ⊆ SMT.fv f ∪ SMT.fv x ∪ declVars Dlt) ∧
        SMT.fv t' ⊆ SMT.fv f ∪ SMT.fv x ∪ declVars Dlt ⌝⦄ := by
  unfold castApp
  mvcgen
  case vc3.h_2.isTrue =>
    rename_i hxeq hfeq _ St hpre
    obtain ⟨rfl, rfl, sub, rfl, rfl⟩ := hpre
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hxeq
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hfeq
    mspec loosenAux_prf_state_decls
    mrename_i pre
    mintro ∀St₁
    rename_i fpair
    obtain ⟨fL, fL_spec⟩ := fpair
    mpure pre
    obtain ⟨fL_le, fL_Λ_sub, fL_fresh, fL_not_used, fL_used_sub,
      fL_keys_sub, fL_preserves, fL_fv_sub, fL_decl⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, _, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨hs_decl, _, _, _, _⟩ := pres
    mspec Std.Do.Spec.pure
    mpure_intro
    exact ⟨_, by rw [hs_decl, hd_decl, fL_decl, List.concat_eq_append, List.concat_eq_append,
        List.append_assoc, List.cons_append, List.nil_append],
      by
        intro b hb
        simp only [specBodies, List.filterMap_cons, List.filterMap_nil] at hb
        rw [List.mem_singleton] at hb
        subst hb
        intro v hv
        simp only [declVars, List.filterMap_cons, List.filterMap_nil, List.mem_union_iff,
          List.mem_singleton] at hv ⊢
        rcases List.mem_union_iff.mp (fL_fv_sub hv) with hm | hm
        · exact Or.inl (Or.inl hm)
        · exact Or.inr (List.mem_singleton.mp hm),
      by
        intro v hv
        simp only [SMT.fv, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
          declVars, List.filterMap_cons, List.filterMap_nil, List.mem_union_iff] at hv ⊢
        rcases hv with hvfL | hvx
        · exact Or.inr hvfL
        · exact Or.inl (Or.inr hvx)⟩
  case vc4.h_2.isFalse.isTrue =>
    rename_i hxeq hfeq _ _ St hpre
    obtain ⟨rfl, rfl, sub, rfl, rfl⟩ := hpre
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hxeq
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hfeq
    mspec loosenAux_prf_state_decls
    mrename_i pre
    mintro ∀St₁
    rename_i xpair
    obtain ⟨x!, x!_spec⟩ := xpair
    mpure pre
    obtain ⟨x!_le, x!_Λ_sub, x!_fresh, x!_not_used, x!_used_sub,
      x!_keys_sub, x!_preserves, x!_fv_sub, x!_decl⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, _, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨hs_decl, _, _, _, _⟩ := pres
    mspec Std.Do.Spec.pure
    mpure_intro
    exact ⟨_, by rw [hs_decl, hd_decl, x!_decl, List.concat_eq_append, List.concat_eq_append,
        List.append_assoc, List.cons_append, List.nil_append],
      by
        intro b hb
        simp only [specBodies, List.filterMap_cons, List.filterMap_nil] at hb
        rw [List.mem_singleton] at hb
        subst hb
        intro v hv
        simp only [declVars, List.filterMap_cons, List.filterMap_nil, List.mem_union_iff,
          List.mem_singleton] at hv ⊢
        rcases List.mem_union_iff.mp (x!_fv_sub hv) with hm | hm
        · exact Or.inl (Or.inr hm)
        · exact Or.inr (List.mem_singleton.mp hm),
      by
        intro v hv
        simp only [SMT.fv, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
          declVars, List.filterMap_cons, List.filterMap_nil, List.mem_union_iff] at hv ⊢
        rcases hv with hvf | hvx!
        · exact Or.inl (Or.inl hvf)
        · exact Or.inr hvx!⟩
  case vc5.h_3.isTrue =>
    rename_i hxeq hfeq _ St hpre
    obtain ⟨rfl, rfl, sub, rfl, rfl⟩ := hpre
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hxeq
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hfeq
    mspec loosenAux_prf_state_decls
    mrename_i pre
    mintro ∀St₁
    rename_i fpair
    obtain ⟨fL, fL_spec⟩ := fpair
    mpure pre
    obtain ⟨fL_le, fL_Λ_sub, fL_fresh, fL_not_used, fL_used_sub,
      fL_keys_sub, fL_preserves, fL_fv_sub, fL_decl⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, _, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨hs_decl, _, _, _, _⟩ := pres
    mspec Std.Do.Spec.pure
    mpure_intro
    exact ⟨_, by rw [hs_decl, hd_decl, fL_decl, List.concat_eq_append, List.concat_eq_append,
        List.append_assoc, List.cons_append, List.nil_append],
      by
        intro b hb
        simp only [specBodies, List.filterMap_cons, List.filterMap_nil] at hb
        rw [List.mem_singleton] at hb
        subst hb
        intro v hv
        simp only [declVars, List.filterMap_cons, List.filterMap_nil, List.mem_union_iff,
          List.mem_singleton] at hv ⊢
        rcases List.mem_union_iff.mp (fL_fv_sub hv) with hm | hm
        · exact Or.inl (Or.inl hm)
        · exact Or.inr (List.mem_singleton.mp hm),
      by
        intro v hv
        simp only [SMT.fv, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
          declVars, List.filterMap_cons, List.filterMap_nil, List.mem_union_iff] at hv ⊢
        rcases hv with hvfL | hvx
        · exact Or.inr hvfL
        · exact Or.inl (Or.inr hvx)⟩
  case vc6.h_3.isFalse.isTrue =>
    rename_i hxeq hfeq _ _ St hpre
    obtain ⟨rfl, rfl, sub, rfl, rfl⟩ := hpre
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hxeq
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hfeq
    mspec loosenAux_prf_state_decls
    mrename_i pre
    mintro ∀St₁
    rename_i xpair
    obtain ⟨x!, x!_spec⟩ := xpair
    mpure pre
    obtain ⟨x!_le, x!_Λ_sub, x!_fresh, x!_not_used, x!_used_sub,
      x!_keys_sub, x!_preserves, x!_fv_sub, x!_decl⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, _, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨hs_decl, _, _, _, _⟩ := pres
    mspec Std.Do.Spec.pure
    mpure_intro
    exact ⟨_, by rw [hs_decl, hd_decl, x!_decl, List.concat_eq_append, List.concat_eq_append,
        List.append_assoc, List.cons_append, List.nil_append],
      by
        intro b hb
        simp only [specBodies, List.filterMap_cons, List.filterMap_nil] at hb
        rw [List.mem_singleton] at hb
        subst hb
        intro v hv
        simp only [declVars, List.filterMap_cons, List.filterMap_nil, List.mem_union_iff,
          List.mem_singleton] at hv ⊢
        rcases List.mem_union_iff.mp (x!_fv_sub hv) with hm | hm
        · exact Or.inl (Or.inr hm)
        · exact Or.inr (List.mem_singleton.mp hm),
      by
        intro v hv
        simp only [SMT.fv, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
          declVars, List.filterMap_cons, List.filterMap_nil, List.mem_union_iff] at hv ⊢
        rcases hv with hvf | hvx!
        · exact Or.inl (Or.inl hvf)
        · exact Or.inr hvx!⟩
  case vc1.h_1.isTrue =>
    rename_i hxeq hfeq _ St hpre
    obtain ⟨rfl, rfl, sub, rfl, rfl⟩ := hpre
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hxeq
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hfeq
    mspec loosenAux_prf_state_decls
    mrename_i pre
    mintro ∀St₁
    rename_i fpair
    obtain ⟨fL, fL_spec⟩ := fpair
    mpure pre
    obtain ⟨fL_le, fL_Λ_sub, fL_fresh, fL_not_used, fL_used_sub,
      fL_keys_sub, fL_preserves, fL_fv_sub, fL_decl⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, _, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨hs_decl, _, _, _, _⟩ := pres
    mspec SMT.freshVar_decls
    case post.success =>
      mintro ∀St₂
      mrename_i pref
      mpure pref
      rename_i ff
      mspec SMT.declareConst_spec
      mrename_i pred2
      mintro ∀St₂d
      mpure pred2
      obtain ⟨hd2_decl, _, _, _, _⟩ := pred2
      mspec SMT.freshVar_decls
      case post.success =>
        mintro ∀St₃
        mrename_i pref2
        mpure pref2
        rename_i u_var
        mspec SMT.freshVar_decls
        case post.success =>
          mintro ∀St₄
          mrename_i pref3
          mpure pref3
          rename_i v_var
          mspec SMT.addSpec_spec
          mrename_i pres2
          mintro ∀St₄s
          mpure pres2
          obtain ⟨hs2_decl, _, _, _, _⟩ := pres2
          mspec Std.Do.Spec.pure
          mpure_intro
          exact ⟨_,
            by rw [hs2_decl, pref3, pref2, hd2_decl, pref, hs_decl, hd_decl, fL_decl]
               simp only [List.concat_eq_append, List.append_assoc, List.cons_append,
                 List.nil_append]
               rfl,
            by
              intro b hb v hv
              simp only [specBodies, List.filterMap_cons, List.filterMap_nil,
                List.mem_cons, List.not_mem_nil, or_false] at hb
              simp only [List.mem_union_iff, declVars, List.filterMap_cons, List.filterMap_nil,
                List.mem_cons, List.not_mem_nil, or_false]
              rcases hb with rfl | rfl
              · rcases List.mem_union_iff.mp (fL_fv_sub hv) with hm | hm
                · exact Or.inl (Or.inl hm)
                · exact Or.inr (Or.inl (List.mem_singleton.mp hm))
              · simp only [SMT.fv, List.mem_removeAll_iff, List.mem_append, List.mem_cons,
                  List.not_mem_nil, or_false] at hv
                obtain ⟨hv_body, hv_ne⟩ := hv
                rcases hv_body with (hvfL | hvu | hvv) | (hvff | hvu') | hvv'
                · exact Or.inr (Or.inl hvfL)
                · exact absurd (Or.inl hvu) hv_ne
                · exact absurd (Or.inr hvv) hv_ne
                · exact Or.inr (Or.inr hvff)
                · exact absurd (Or.inl hvu') hv_ne
                · exact absurd (Or.inr hvv') hv_ne,
            by
              intro v hv
              simp only [SMT.fv, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
                List.mem_union_iff, declVars, List.filterMap_cons, List.filterMap_nil] at hv ⊢
              rcases hv with hvff | hvx
              · exact Or.inr (Or.inr hvff)
              · exact Or.inl (Or.inr hvx)⟩
  case vc2.h_1.isFalse.isTrue =>
    rename_i hxeq hfeq _ _ St hpre
    obtain ⟨rfl, rfl, sub, rfl, rfl⟩ := hpre
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hxeq
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hfeq
    mspec loosenAux_prf_state_decls
    mrename_i pre
    mintro ∀St₁
    rename_i xpair
    obtain ⟨x!, x!_spec⟩ := xpair
    mpure pre
    obtain ⟨x!_le, x!_Λ_sub, x!_fresh, x!_not_used, x!_used_sub,
      x!_keys_sub, x!_preserves, x!_fv_sub, x!_decl⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, _, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨hs_decl, _, _, _, _⟩ := pres
    mspec SMT.freshVar_decls
    case post.success =>
      mintro ∀St₂
      mrename_i pref
      mpure pref
      rename_i ff
      mspec SMT.declareConst_spec
      mrename_i pred2
      mintro ∀St₂d
      mpure pred2
      obtain ⟨hd2_decl, _, _, _, _⟩ := pred2
      mspec SMT.freshVar_decls
      case post.success =>
        mintro ∀St₃
        mrename_i pref2
        mpure pref2
        rename_i u_var
        mspec SMT.freshVar_decls
        case post.success =>
          mintro ∀St₄
          mrename_i pref3
          mpure pref3
          rename_i v_var
          mspec SMT.addSpec_spec
          mrename_i pres2
          mintro ∀St₄s
          mpure pres2
          obtain ⟨hs2_decl, _, _, _, _⟩ := pres2
          mspec Std.Do.Spec.pure
          mpure_intro
          exact ⟨_,
            by rw [hs2_decl, pref3, pref2, hd2_decl, pref, hs_decl, hd_decl, x!_decl]
               simp only [List.concat_eq_append, List.append_assoc, List.cons_append,
                 List.nil_append]
               rfl,
            by
              intro b hb v hv
              simp only [specBodies, List.filterMap_cons, List.filterMap_nil,
                List.mem_cons, List.not_mem_nil, or_false] at hb
              simp only [List.mem_union_iff, declVars, List.filterMap_cons, List.filterMap_nil,
                List.mem_cons, List.not_mem_nil, or_false]
              rcases hb with rfl | rfl
              · rcases List.mem_union_iff.mp (x!_fv_sub hv) with hm | hm
                · exact Or.inl (Or.inr hm)
                · exact Or.inr (Or.inl (List.mem_singleton.mp hm))
              · simp only [SMT.fv, List.mem_removeAll_iff, List.mem_append, List.mem_cons,
                  List.not_mem_nil, or_false] at hv
                obtain ⟨hv_body, hv_ne⟩ := hv
                rcases hv_body with (hvf | hvu | hvv) | (hvff | hvu') | hvv'
                · exact Or.inl (Or.inl hvf)
                · exact absurd (Or.inl hvu) hv_ne
                · exact absurd (Or.inr hvv) hv_ne
                · exact Or.inr (Or.inr hvff)
                · exact absurd (Or.inl hvu') hv_ne
                · exact absurd (Or.inr hvv') hv_ne,
            by
              intro v hv
              simp only [SMT.fv, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
                List.mem_union_iff, declVars, List.filterMap_cons, List.filterMap_nil] at hv ⊢
              rcases hv with hvff | hvx!
              · exact Or.inr (Or.inr hvff)
              · exact Or.inr (Or.inl hvx!)⟩

/-- `List.toProdl` on a concatenation `xs ++ [x]` (with `xs` non-empty) reassociates
into a `.pair`. Local copy of `AllCaseHelpers.List.toProdl_concat_of_nonempty`. -/
theorem encodeTerm_state.toProdl_concat_of_nonempty
    (xs : List SMTType) (x : SMTType) (hne : xs ≠ []) :
    List.toProdl (xs.concat x) = .pair (List.toProdl xs) x := by
  unfold List.toProdl
  rw [List.concat_eq_append, List.reverse_append]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
  have hne_rev : xs.reverse ≠ [] := by
    intro h; exact hne (List.reverse_eq_nil_iff.mp h)
  cases hrev : xs.reverse with
  | nil => exact absurd hrev hne_rev
  | cons h t =>
    show List.toProdl.aux (x :: h :: t) = .pair (List.toProdl.aux (h :: t)) x
    rfl

/-- The round-trip `fromProdl` then `toProdl` is the identity on `.pair`-nested
types of matching arity. Local copy of `AllCaseHelpers.fromProdl_toProdl_roundtrip`. -/
theorem encodeTerm_state.fromProdl_toProdl_roundtrip :
    ∀ (τ : SMTType) (n : ℕ), (τ.fromProdl n).length = n + 1 →
      (τ.fromProdl n).toProdl = τ := by
  intro τ n h
  induction n generalizing τ with
  | zero =>
    cases τ with
    | pair α β => simp only [SMTType.fromProdl]; unfold List.toProdl; rfl
    | _ => simp only [SMTType.fromProdl]; unfold List.toProdl; rfl
  | succ n ih =>
    cases τ with
    | pair α β =>
      simp only [SMTType.fromProdl]
      have hα_ne : α.fromProdl n ≠ [] := by
        intro h_nil
        have : (α.fromProdl n).length = 0 := by rw [h_nil]; rfl
        simp only [SMTType.fromProdl, List.length_concat] at h
        omega
      have hlen_α : (α.fromProdl n).length = n + 1 := by
        simp only [SMTType.fromProdl, List.length_concat] at h
        omega
      rw [encodeTerm_state.toProdl_concat_of_nonempty (α.fromProdl n) β hα_ne]
      rw [ih α hlen_α]
    | _ =>
      simp only [SMTType.fromProdl] at h
      simp at h

set_option maxHeartbeats 4000000 in
/-- Specialised `castApp` declarations spec for the case where the function's
domain type *equals* the argument's type: `castApp` then necessarily takes the
function-loosening branch, so every generated spec body's free variables live in
`fv f ∪ declVars Dlt` — **independent of `fv x`**. This is the form the `collect`
case needs, where `castApp`'s second argument is a tuple of *fresh binder*
variables whose free vars cannot be bounded by source vars. -/
theorem castApp_decl_domEq
    (f x : SMT.Term) (τ σ : SMTType) {Λ : SMT.TypeContext} {n : ℕ}
    {used : List SMT.𝒱} {decl : SMT.Chunk} :
    ⦃ fun (⟨E, Λ'⟩ : EncoderState) ↦
        ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ AList.keys Λ ⊆ E.usedVars ∧ E.usedVars = used ∧
          E.declarations = decl⌝ ⦄
    castApp (f, .fun τ (.option σ)) (x, τ)
    ⦃ ⇓? (⟨t', _σ⟩ : SMT.Term × SMTType) (⟨E', Γ'⟩ : EncoderState) => ⌜
      ∃ Dlt : SMT.Chunk,
        E'.declarations = decl ++ Dlt ∧
        (∀ b ∈ specBodies Dlt, SMT.fv b ⊆ SMT.fv f ∪ declVars Dlt) ∧
        SMT.fv t' ⊆ SMT.fv f ∪ SMT.fv x ∪ declVars Dlt ⌝⦄ := by
  unfold castApp
  mvcgen
  case vc1.h_1.isTrue => rename_i h; simp_all
  case vc2.h_1.isFalse.isTrue => rename_i h; simp_all
  case vc3.h_2.isTrue => rename_i h; simp_all
  case vc4.h_2.isFalse.isTrue => rename_i h; simp_all
  case vc5.h_3.isTrue =>
    rename_i hxeq hfeq hle St hpre
    obtain ⟨rfl, hft⟩ := Prod.mk.injEq .. |>.mp hfeq
    injection hft with ht hso
    injection hso with hs
    subst ht
    subst hs
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hxeq
    obtain ⟨rfl, rfl, sub, rfl, rfl⟩ := hpre
    mspec loosenAux_prf_state_decls
    mrename_i pre
    mintro ∀St₁
    rename_i fpair
    obtain ⟨fL, fL_spec⟩ := fpair
    mpure pre
    obtain ⟨fL_le, fL_Λ_sub, fL_fresh, fL_not_used, fL_used_sub,
      fL_keys_sub, fL_preserves, fL_fv_sub, fL_decl⟩ := pre
    mspec SMT.declareConst_spec
    mrename_i pred
    mintro ∀St₁d
    mpure pred
    obtain ⟨hd_decl, _, _, _, _⟩ := pred
    mspec SMT.addSpec_spec
    mrename_i pres
    mintro ∀St₁s
    mpure pres
    obtain ⟨hs_decl, _, _, _, _⟩ := pres
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨_, by rw [hs_decl, hd_decl, fL_decl, List.concat_eq_append,
        List.concat_eq_append, List.append_assoc, List.cons_append, List.nil_append], ?_, ?_⟩
    · intro b hb
      simp only [specBodies, List.filterMap_cons, List.filterMap_nil] at hb
      rw [List.mem_singleton] at hb
      subst hb
      intro v hv
      simp only [declVars, List.filterMap_cons, List.filterMap_nil, List.mem_union_iff,
        List.mem_singleton] at hv ⊢
      rcases List.mem_union_iff.mp (fL_fv_sub hv) with hm | hm
      · exact Or.inl hm
      · exact Or.inr (List.mem_singleton.mp hm)
    · intro v hv
      simp only [SMT.fv, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        declVars, List.filterMap_cons, List.filterMap_nil, List.mem_union_iff] at hv ⊢
      rcases hv with hvfL | hvx
      · exact Or.inr hvfL
      · exact Or.inl (Or.inr hvx)
  case vc6.h_3.isFalse.isTrue =>
    rename_i hxeq hfeq hne h2 St hpre
    obtain ⟨rfl, hft⟩ := Prod.mk.injEq .. |>.mp hfeq
    injection hft with ht hso
    injection hso with hs
    subst ht
    subst hs
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp hxeq
    exact absurd castable?.reflexive hne

/-- `encodeTerm` depends on its `B.Env` argument only through `flags`: the
result is unchanged across environments with equal `flags`. Local copy of
`CollectCaseHelpers.encodeTerm_env_irrel` (importing that module would pull in
`@[spec]`-tagged loosening lemmas that disturb `mvcgen` in the already-proven
non-binder cases). Used in the binder cases to rewrite `encodeTerm P E` so the
extended-context induction hypothesis `P_ih` applies. -/
theorem encodeTerm_state.encodeTerm_env_irrel (t : B.Term) (E₁ E₂ : B.Env)
    (hflags : E₁.flags = E₂.flags) :
    encodeTerm t E₁ = encodeTerm t E₂ := by
  induction t with
  | var v => simp [encodeTerm]
  | int n => simp [encodeTerm]
  | bool b => simp [encodeTerm]
  | «ℤ» => simp [encodeTerm]
  | «𝔹» => simp [encodeTerm]
  | maplet x y ihx ihy => simp only [encodeTerm]; rw [ihx, ihy]
  | add x y ihx ihy => simp only [encodeTerm]; rw [ihx, ihy]
  | sub x y ihx ihy => simp only [encodeTerm]; rw [ihx, ihy]
  | mul x y ihx ihy => simp only [encodeTerm]; rw [ihx, ihy]
  | le x y ihx ihy => simp only [encodeTerm]; rw [ihx, ihy]
  | and x y ihx ihy => simp only [encodeTerm]; rw [ihx, ihy]
  | not x ihx => simp only [encodeTerm]; rw [ihx]
  | eq x y ihx ihy => simp only [encodeTerm]; rw [ihx, ihy]
  | mem x S ihx ihS => simp only [encodeTerm]; rw [ihx, ihS]
  | pow S ihS => simp only [encodeTerm]; rw [ihS]
  | cprod A B ihA ihB => simp only [encodeTerm]; rw [ihA, ihB]
  | union S T ihS ihT => simp only [encodeTerm]; rw [ihS, ihT]
  | inter S T ihS ihT => simp only [encodeTerm]; rw [ihS, ihT]
  | card S ihS => simp only [encodeTerm]
  | app f x ihf ihx => simp only [encodeTerm]; rw [ihf, ihx]
  | collect vs D P ihD ihP => simp only [encodeTerm]; rw [ihD, ihP]
  | lambda vs D P ihD ihP => simp only [encodeTerm]; rw [ihD, ihP]
  | pfun A B ihA ihB => simp only [encodeTerm]; rw [ihA, ihB]
  | min S ihS => simp only [encodeTerm]
  | max S ihS => simp only [encodeTerm]
  | all vs D P ihD ihP => simp only [encodeTerm]; rw [ihD, ihP, hflags]

/-- A nonempty list of set-typed terms folded with `⨯ᴮ` is typed as the
corresponding folded cartesian-product set type. Local copy of
`CollectCaseHelpers.typing_reduce_cprod` (see `encodeTerm_env_irrel` above for
why that module is not imported). -/
theorem encodeTerm_state.typing_reduce_cprod (Γ : B.TypeContext) :
    ∀ (Ds : List B.Term) (αs : List BType)
    (_hForall : List.Forall₂ (fun Dᵢ αᵢ => Γ ⊢ᴮ Dᵢ : .set αᵢ) Ds αs)
    (hDs : Ds ≠ []) (hαs : αs ≠ []),
    Γ ⊢ᴮ Ds.reduce (· ⨯ᴮ ·) hDs : .set (αs.reduce (· ×ᴮ ·) hαs)
  | [_], [_], .cons h .nil, _, _ => by simpa [List.reduce] using h
  | D :: D' :: Ds, α :: α' :: αs, .cons hD (.cons hD' htail), _, _ => by
    rw [List.reduce_cons_cons, List.reduce_cons_cons]
    exact typing_reduce_cprod Γ _ _ (.cons (Typing.cprod hD hD') htail)
      (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)
  termination_by Ds => Ds.length

/-- Folding `p.1 :: ·` over a pair list only grows the accumulator: every
element of the accumulator survives. The `addToContext`/`freshVarList` loops in
the binder cases extend `usedVars` exactly this way. -/
theorem encodeTerm_state.mem_foldl_cons_of_mem {γ : Type*}
    (l : List (SMT.𝒱 × γ)) (acc : List SMT.𝒱) {v : SMT.𝒱} (hv : v ∈ acc) :
    v ∈ l.foldl (fun used (p : SMT.𝒱 × γ) => p.1 :: used) acc := by
  induction l generalizing acc with
  | nil => exact hv
  | cons p ps ih => exact ih _ (List.mem_cons_of_mem _ hv)

/-- Folding the `addToContext` insert over a pair list keeps `keys ⊆ used`
covered, provided `used` is extended by the same `p.1 :: ·` fold. -/
theorem encodeTerm_state.keys_foldl_insert_subset_foldl_cons
    (l : List (SMT.𝒱 × SMTType)) {Γ : SMT.TypeContext} {used : List SMT.𝒱}
    (h : AList.keys Γ ⊆ used) :
    AList.keys (l.foldl (fun Γ (p : SMT.𝒱 × SMTType) => Γ.insert p.1 p.2) Γ) ⊆
      l.foldl (fun used (p : SMT.𝒱 × SMTType) => p.1 :: used) used := by
  induction l generalizing Γ used with
  | nil => exact h
  | cons p ps ih =>
    simp only [List.foldl_cons]
    apply ih
    intro v hv
    simp only [AList.keys_insert] at hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (h (List.mem_of_mem_erase hv))

/-- Erasing a freshly-inserted key is the identity: the binder cases insert a
single fresh `xy`/`zs` and immediately `eraseFromContext` it, so the final type
context equals the one before the insertion. -/
theorem encodeTerm_state.erase_insert_self {a : SMT.𝒱} {τ : SMTType}
    {s : SMT.TypeContext} (ha : a ∉ s) : (s.insert a τ).erase a = s := by
  apply AList.ext
  show List.kerase a (AList.insert a τ s).entries = s.entries
  rw [AList.entries_insert_of_notMem ha]
  exact List.kerase_cons_eq rfl

/-- Erasing a key that is absent from the context is the identity. -/
theorem encodeTerm_state.erase_of_notMem {a : SMT.𝒱} {s : SMT.TypeContext}
    (ha : a ∉ s) : s.erase a = s := by
  apply AList.ext
  show List.kerase a s.entries = s.entries
  exact List.kerase_of_notMem_keys (by simpa [AList.mem_keys] using ha)

/-- Folding `erase` over a list of keys all absent from the context is the
identity. -/
theorem encodeTerm_state.foldl_erase_of_notMem (zs : List SMT.𝒱)
    {s : SMT.TypeContext} (hzs : ∀ z ∈ zs, z ∉ s) :
    zs.foldl (fun Γ v => Γ.erase v) s = s := by
  induction zs generalizing s with
  | nil => rfl
  | cons z zs ih =>
    rw [List.foldl_cons, encodeTerm_state.erase_of_notMem (hzs z (List.mem_cons_self ..))]
    exact ih (fun w hw => hzs w (List.mem_cons_of_mem _ hw))

/-- `erase` and `insert` commute when the two keys differ. -/
theorem encodeTerm_state.erase_insert_ne {a b : SMT.𝒱} {τ : SMTType}
    {s : SMT.TypeContext} (hab : a ≠ b) :
    (s.insert b τ).erase a = (s.erase a).insert b τ := by
  apply AList.ext
  show List.kerase a (AList.insert b τ s).entries
      = (AList.insert b τ (s.erase a)).entries
  rw [AList.entries_insert, AList.entries_insert]
  show List.kerase a (⟨b, τ⟩ :: List.kerase b s.entries)
      = ⟨b, τ⟩ :: List.kerase b (s.erase a).entries
  rw [List.kerase_cons_ne (by simpa using hab)]
  show ⟨b, τ⟩ :: List.kerase a (List.kerase b s.entries)
      = ⟨b, τ⟩ :: List.kerase b (List.kerase a s.entries)
  rw [List.kerase_kerase]

/-- `erase` commutes through a `foldl`-insert over a pair list whose keys all
differ from the erased key. -/
theorem encodeTerm_state.erase_foldl_insert_of_notMem (a : SMT.𝒱)
    (l : List (SMT.𝒱 × SMTType)) {s : SMT.TypeContext}
    (ha : a ∉ l.map Prod.fst) :
    (l.foldl (fun Γ p => Γ.insert p.1 p.2) s).erase a
      = l.foldl (fun Γ p => Γ.insert p.1 p.2) (s.erase a) := by
  induction l generalizing s with
  | nil => rfl
  | cons p l ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at ha
    rw [List.foldl_cons, List.foldl_cons, ih ha.2,
      encodeTerm_state.erase_insert_ne ha.1]

/-- Folding `erase` over the keys of a pair list, applied to the result of
`foldl`-inserting that same pair list into a context disjoint from the keys,
recovers the original context. -/
theorem encodeTerm_state.foldl_erase_foldl_insert (l : List (SMT.𝒱 × SMTType))
    {s : SMT.TypeContext} (hnodup : (l.map Prod.fst).Nodup)
    (hdisj : ∀ p ∈ l, p.1 ∉ s) :
    (l.map Prod.fst).foldl (fun Γ v => Γ.erase v)
      (l.foldl (fun Γ p => Γ.insert p.1 p.2) s) = s := by
  induction l generalizing s with
  | nil => rfl
  | cons p l ih =>
    simp only [List.map_cons, List.foldl_cons, List.nodup_cons] at hnodup ⊢
    rw [encodeTerm_state.erase_foldl_insert_of_notMem p.1 l hnodup.1,
      encodeTerm_state.erase_insert_self (hdisj p (List.mem_cons_self ..))]
    refine ih hnodup.2 (fun q hq => ?_)
    exact hdisj q (List.mem_cons_of_mem _ hq)

/-- Spec for the `forIn` loop in the function-`D` arm of `encodeTerm`'s
`collect`/`all` cases: it folds a bare `modify (types := types.insert …)` over a
pair list. Unlike `addToContext`, this updates only `types` — `usedVars` and
`freshvarsc` are untouched. -/
theorem encodeTerm_state.modifyTypes_forIn_spec (pairs : List (SMT.𝒱 × SMTType))
    {Γ : SMT.TypeContext} {n : ℕ} {used : List SMT.𝒱} :
    ⦃ λ ⟨E, Λ⟩ ↦ ⌜Λ = Γ ∧ E.freshvarsc = n ∧ E.usedVars = used⌝ ⦄
    forIn pairs PUnit.unit (fun (p : SMT.𝒱 × SMTType) _ => (do
      modify (fun (e : EncoderState) => { e with types := AList.insert p.1 p.2 e.types })
      pure (ForInStep.yield PUnit.unit) : Encoder (ForInStep PUnit)))
    ⦃ ⇓ () ⟨E, Λ⟩ =>
        ⌜Λ = pairs.foldl (fun Γ (p : SMT.𝒱 × SMTType) => Γ.insert p.1 p.2) Γ ∧
          E.freshvarsc = n ∧ E.usedVars = used⌝ ⦄ := by
  induction pairs generalizing Γ used with
  | nil =>
    mintro pre ∀S; mpure pre; obtain ⟨rfl, rfl, rfl⟩ := pre
    simp only [List.forIn_nil]
    mpure_intro; exact ⟨rfl, rfl, rfl⟩
  | cons p pairs ih =>
    mintro pre ∀S; mpure pre; obtain ⟨rfl, rfl, rfl⟩ := pre
    simp only [List.forIn_cons, bind_assoc]
    mspec Std.Do.Spec.modifyGet_StateT
    mspec Std.Do.Spec.pure
    simp only [List.foldl_cons]
    mspec ih

/-- Folding the `modify`-style type insert over a pair list whose first
components are already covered by `used` keeps `keys ⊆ used`. Used in the
function-`D` arm of `collect`/`all`, where the inserts do not extend `usedVars`
but the inserted keys (the binders `vs`) are already used. -/
theorem encodeTerm_state.keys_foldl_insert_subset_of_fst_mem
    (l : List (SMT.𝒱 × SMTType)) {Γ : SMT.TypeContext} {used : List SMT.𝒱}
    (h : AList.keys Γ ⊆ used) (hl : ∀ p ∈ l, p.1 ∈ used) :
    AList.keys (l.foldl (fun Γ (p : SMT.𝒱 × SMTType) => Γ.insert p.1 p.2) Γ) ⊆ used := by
  induction l generalizing Γ with
  | nil => exact h
  | cons p ps ih =>
    simp only [List.foldl_cons]
    apply ih
    · intro v hv
      simp only [AList.keys_insert] at hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hl p (List.mem_cons_self ..)
      · exact h (List.mem_of_mem_erase hv)
    · exact fun p hp => hl p (List.mem_cons_of_mem _ hp)

/-- The `foldl`-insert over a pair list only grows the key set. -/
theorem encodeTerm_state.keys_subset_foldl_insert
    (l : List (SMT.𝒱 × SMTType)) {Γ : SMT.TypeContext} :
    AList.keys Γ ⊆
      AList.keys (l.foldl (fun Γ (p : SMT.𝒱 × SMTType) => Γ.insert p.1 p.2) Γ) := by
  induction l generalizing Γ with
  | nil => exact fun _ h => h
  | cons p ps ih =>
    simp only [List.foldl_cons]
    intro v hv
    refine ih ?_
    exact AList.mem_keys.mp ((AList.mem_insert _).mpr (.inr (AList.mem_keys.mpr hv)))

/-- A key inserted by the `foldl`-insert over a pair list is present in the
result. Used in the function-`D` arm to recover the freshly inserted `xs`. -/
theorem encodeTerm_state.mem_keys_foldl_insert_of_fst
    (l : List (SMT.𝒱 × SMTType)) {Γ : SMT.TypeContext} {v : SMT.𝒱}
    (hv : v ∈ l.map Prod.fst) :
    v ∈ AList.keys (l.foldl (fun Γ (p : SMT.𝒱 × SMTType) => Γ.insert p.1 p.2) Γ) := by
  induction l generalizing Γ with
  | nil => simp at hv
  | cons p ps ih =>
    simp only [List.foldl_cons]
    simp only [List.map_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact encodeTerm_state.keys_subset_foldl_insert ps
        (by rw [AList.keys_insert]; exact List.mem_cons_self ..)
    · exact ih hv

/-- Free variables of `toPairl.aux` of a list of variable terms are among those
variables. Local copy of `AllCaseHelpers.fv_toPairl_aux_of_vars`. -/
theorem encodeTerm_state.fv_toPairl_aux_of_vars (ts : List SMT.Term) (vs : List SMT.𝒱)
    (hts : ts = vs.map SMT.Term.var) :
    ∀ v ∈ SMT.fv (List.toPairl.aux ts), v ∈ vs := by
  induction ts generalizing vs with
  | nil => intro v hv; simp [List.toPairl.aux, SMT.fv] at hv
  | cons t ts ih =>
    cases vs with
    | nil => simp at hts
    | cons v' vs' =>
      simp only [List.map_cons] at hts
      obtain ⟨ht_eq, hts_eq⟩ := List.cons_eq_cons.mp hts
      cases ts with
      | nil =>
        intro v hv
        simp only [List.toPairl.aux] at hv
        rw [ht_eq] at hv; simp [SMT.fv] at hv; subst hv; simp
      | cons t' ts' =>
        intro v hv
        simp only [List.toPairl.aux] at hv
        simp only [SMT.fv, List.mem_append] at hv
        rcases hv with hv_left | hv_right
        · have := ih vs' hts_eq v hv_left; simp; right; exact this
        · rw [ht_eq] at hv_right
          simp [SMT.fv] at hv_right; subst hv_right; simp

/-- Free variables of `(zs.map var).toPairl` are among `zs`. Local copy of
`AllCaseHelpers.fv_toPairl_map_var_subset`. -/
theorem encodeTerm_state.fv_toPairl_map_var_subset (zs : List SMT.𝒱) :
    ∀ v ∈ SMT.fv (zs.map SMT.Term.var).toPairl, v ∈ zs := by
  unfold List.toPairl
  have h := encodeTerm_state.fv_toPairl_aux_of_vars (zs.map SMT.Term.var).reverse zs.reverse
      (by rw [List.map_reverse])
  intro v hv; have := h v hv; exact (List.mem_reverse.mp this)

/-- State-only spec for the `mapFinIdxM.go` recursion driving the `all`
encoder's flag-loosening pass: the body only `pure`s or `throw`s, so the state
is untouched and the produced list has the same length as the input. A
structural-only weakening of `AllCaseHelpers.mapFinIdxM_all_body_spec` (which
also tracks `SMTFlagTypeRel`); copied here because importing that module would
pollute `mvcgen`'s `@[spec]` set. -/
theorem encodeTerm_state.mapFinIdxM_go_all_state
    (vs : List SMT.𝒱) (flags : List SMT.𝒱) (tmp_τs : List SMTType)
    (hvs_eq : vs.length = tmp_τs.length)
    (bs : List SMTType) (acc : Array SMTType) (hsize : bs.length + acc.size = tmp_τs.length)
    {Γ : SMT.TypeContext} {n : ℕ} {used : List SMT.𝒱} :
    ⦃ λ ⟨E, Γ'⟩ ↦ ⌜Γ' = Γ ∧ E.freshvarsc = n ∧ E.usedVars = used⌝⦄
    List.mapFinIdxM.go (as := tmp_τs)
      (fun i τ hi =>
        (if vs[i]'(by omega) ∈ flags then
          (match τ with
          | .fun (.pair α β) .bool => pure (.fun α (.option β))
          | .fun α (.option β) => pure (.fun α (.option β))
          | ξ => throw s!"encodeTerm:all: Unsupported flag type {vs[i]'(by omega)} : {ξ}"
            : Encoder SMTType)
        else pure τ))
      bs acc hsize
    ⦃ ⇓? τs ⟨E', Γ'⟩ =>
      ⌜ Γ' = Γ ∧ E'.freshvarsc = n ∧ E'.usedVars = used ∧ τs.length = tmp_τs.length ⌝⦄ := by
  induction bs generalizing acc Γ n used with
  | nil =>
    mintro pre ∀S; mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    simp only [List.mapFinIdxM.go]
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨trivial, trivial, trivial, ?_⟩
    have h_acc : acc.size = tmp_τs.length := by
      have := hsize; simp only [List.length_nil, Nat.zero_add] at this; exact this
    simp [Array.length_toList, h_acc]
  | cons b bs' ih =>
    mintro pre ∀S; mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    simp only [List.mapFinIdxM.go]
    have h_acc_lt : acc.size < tmp_τs.length := by
      simp only [List.length_cons] at hsize; omega
    have hsize_cons : bs'.length + 1 + acc.size = tmp_τs.length := by
      simp only [List.length_cons] at hsize; omega
    by_cases hf : vs[acc.size]'(by omega) ∈ flags
    · simp only [hf, if_true]
      split
      · rename_i τ_o α₀ β₀
        have hsize_push : bs'.length + (acc.push (.fun α₀ (.option β₀))).size = tmp_τs.length := by
          simp only [Array.size_push]; omega
        mspec Std.Do.Spec.pure
        mspec (ih (acc.push (.fun α₀ (.option β₀))) hsize_push)
      · rename_i τ_o α₀ β₀
        have hsize_push : bs'.length + (acc.push (.fun α₀ (.option β₀))).size = tmp_τs.length := by
          simp only [Array.size_push]; omega
        mspec Std.Do.Spec.pure
        mspec (ih (acc.push (.fun α₀ (.option β₀))) hsize_push)
      · mspec
    · simp only [hf, if_false]
      have hsize_push : bs'.length + (acc.push b).size = tmp_τs.length := by
        simp only [Array.size_push]; omega
      mspec Std.Do.Spec.pure
      mspec (ih (acc.push b) hsize_push)

/-- Top-level state-only spec for the `all` encoder's `mapFinIdxM` flag pass.
See `mapFinIdxM_go_all_state`. -/
theorem encodeTerm_state.mapFinIdxM_all_state
    (vs : List SMT.𝒱) (flags : List SMT.𝒱) (tmp_τs : List SMTType)
    (hvs_eq : vs.length = tmp_τs.length)
    {Γ : SMT.TypeContext} {n : ℕ} {used : List SMT.𝒱} :
    ⦃ λ ⟨E, Γ'⟩ ↦ ⌜Γ' = Γ ∧ E.freshvarsc = n ∧ E.usedVars = used⌝⦄
    tmp_τs.mapFinIdxM
      (fun i τ hi =>
        (if vs[i]'(by omega) ∈ flags then
          (match τ with
          | .fun (.pair α β) .bool => pure (.fun α (.option β))
          | .fun α (.option β) => pure (.fun α (.option β))
          | ξ => throw s!"encodeTerm:all: Unsupported flag type {vs[i]'(by omega)} : {ξ}"
            : Encoder SMTType)
        else pure τ))
    ⦃ ⇓? τs ⟨E', Γ'⟩ =>
      ⌜ Γ' = Γ ∧ E'.freshvarsc = n ∧ E'.usedVars = used ∧ τs.length = tmp_τs.length ⌝⦄ := by
  unfold List.mapFinIdxM
  exact encodeTerm_state.mapFinIdxM_go_all_state vs flags tmp_τs hvs_eq tmp_τs #[] (by simp)

/-- `declarations`-only spec for the `mapFinIdxM.go` flag pass of the `all`
encoder: the pass only does `pure`/`throw`, so `declarations` is unchanged. -/
theorem encodeTerm_state.mapFinIdxM_go_all_decls
    (vs : List SMT.𝒱) (flags : List SMT.𝒱) (tmp_τs : List SMTType)
    (hvs_eq : vs.length = tmp_τs.length)
    (bs : List SMTType) (acc : Array SMTType) (hsize : bs.length + acc.size = tmp_τs.length)
    {decl : SMT.Chunk} :
    ⦃ λ ⟨E, _⟩ ↦ ⌜E.declarations = decl⌝⦄
    List.mapFinIdxM.go (as := tmp_τs)
      (fun i τ hi =>
        (if vs[i]'(by omega) ∈ flags then
          (match τ with
          | .fun (.pair α β) .bool => pure (.fun α (.option β))
          | .fun α (.option β) => pure (.fun α (.option β))
          | ξ => throw s!"encodeTerm:all: Unsupported flag type {vs[i]'(by omega)} : {ξ}"
            : Encoder SMTType)
        else pure τ))
      bs acc hsize
    ⦃ ⇓? _ ⟨E', _⟩ => ⌜E'.declarations = decl⌝ ⦄ := by
  induction bs generalizing acc decl with
  | nil =>
    mintro pre ∀S; mpure pre
    simp only [List.mapFinIdxM.go]
    mspec Std.Do.Spec.pure
  | cons b bs' ih =>
    mintro pre ∀S; mpure pre
    simp only [List.mapFinIdxM.go]
    have h_acc_lt : acc.size < tmp_τs.length := by
      simp only [List.length_cons] at hsize; omega
    have hsize_cons : bs'.length + 1 + acc.size = tmp_τs.length := by
      simp only [List.length_cons] at hsize; omega
    by_cases hf : vs[acc.size]'(by omega) ∈ flags
    · simp only [hf, if_true]
      split
      · rename_i τ_o α₀ β₀
        have hsize_push : bs'.length + (acc.push (.fun α₀ (.option β₀))).size = tmp_τs.length := by
          simp only [Array.size_push]; omega
        mspec Std.Do.Spec.pure
        mspec (ih (acc.push (.fun α₀ (.option β₀))) hsize_push)
      · rename_i τ_o α₀ β₀
        have hsize_push : bs'.length + (acc.push (.fun α₀ (.option β₀))).size = tmp_τs.length := by
          simp only [Array.size_push]; omega
        mspec Std.Do.Spec.pure
        mspec (ih (acc.push (.fun α₀ (.option β₀))) hsize_push)
      · mspec
    · simp only [hf, if_false]
      have hsize_push : bs'.length + (acc.push b).size = tmp_τs.length := by
        simp only [Array.size_push]; omega
      mspec Std.Do.Spec.pure
      mspec (ih (acc.push b) hsize_push)

/-- Top-level `declarations`-only spec for the `all` encoder's `mapFinIdxM`
flag pass. See `mapFinIdxM_go_all_decls`. -/
theorem encodeTerm_state.mapFinIdxM_all_decls
    (vs : List SMT.𝒱) (flags : List SMT.𝒱) (tmp_τs : List SMTType)
    (hvs_eq : vs.length = tmp_τs.length)
    {decl : SMT.Chunk} :
    ⦃ λ ⟨E, _⟩ ↦ ⌜E.declarations = decl⌝⦄
    tmp_τs.mapFinIdxM
      (fun i τ hi =>
        (if vs[i]'(by omega) ∈ flags then
          (match τ with
          | .fun (.pair α β) .bool => pure (.fun α (.option β))
          | .fun α (.option β) => pure (.fun α (.option β))
          | ξ => throw s!"encodeTerm:all: Unsupported flag type {vs[i]'(by omega)} : {ξ}"
            : Encoder SMTType)
        else pure τ))
    ⦃ ⇓? _ ⟨E', _⟩ => ⌜E'.declarations = decl⌝ ⦄ := by
  unfold List.mapFinIdxM
  exact encodeTerm_state.mapFinIdxM_go_all_decls vs flags tmp_τs hvs_eq tmp_τs #[] (by simp)


/-- The `modify`-style type-insert `forIn` loop leaves `declarations` unchanged. -/
theorem encodeTerm_state.modifyTypes_forIn_decls (pairs : List (SMT.𝒱 × SMTType))
    {decl : SMT.Chunk} :
    ⦃ λ ⟨E, _⟩ ↦ ⌜E.declarations = decl⌝ ⦄
    forIn pairs PUnit.unit (fun (p : SMT.𝒱 × SMTType) _ => (do
      modify (fun (e : EncoderState) => { e with types := AList.insert p.1 p.2 e.types })
      pure (ForInStep.yield PUnit.unit) : Encoder (ForInStep PUnit)))
    ⦃ ⇓ () ⟨E, _⟩ => ⌜E.declarations = decl⌝ ⦄ := by
  induction pairs with
  | nil =>
    mintro pre ∀S; mpure pre
    simp only [List.forIn_nil]
    mspec Std.Do.Spec.pure
  | cons p pairs ih =>
    mintro pre ∀S; mpure pre
    simp only [List.forIn_cons, bind_assoc]
    mspec Std.Do.Spec.modifyGet_StateT
    mspec Std.Do.Spec.pure
    mspec ih

/-- The `addToContext` `forIn` loop leaves `declarations` unchanged. -/
theorem SMT.addToContext_forIn_decls (pairs : List (SMT.𝒱 × SMTType))
    {decl : SMT.Chunk} :
    ⦃ λ ⟨E, _⟩ ↦ ⌜E.declarations = decl⌝ ⦄
    forIn pairs PUnit.unit (fun (p : SMT.𝒱 × SMTType) _ => do
      SMT.addToContext p.1 p.2; pure (ForInStep.yield PUnit.unit))
    ⦃ ⇓ () ⟨E, _⟩ => ⌜E.declarations = decl⌝ ⦄ := by
  induction pairs with
  | nil =>
    mintro pre ∀S; mpure pre
    simp only [List.forIn_nil]
    mspec Std.Do.Spec.pure
  | cons p pairs ih =>
    mintro pre ∀S; mpure pre
    simp only [List.forIn_cons, bind_assoc]
    unfold SMT.addToContext
    mspec Std.Do.Spec.modifyGet_StateT
    mspec Std.Do.Spec.pure
    mspec ih

/-- `eraseFromContext` leaves `declarations` unchanged. -/
theorem SMT.eraseFromContext_decls {v : SMT.𝒱} {decl : SMT.Chunk} :
    ⦃ λ ⟨E, _⟩ ↦ ⌜E.declarations = decl⌝ ⦄
    SMT.eraseFromContext v
    ⦃ ⇓ () ⟨E, _⟩ => ⌜E.declarations = decl⌝ ⦄ := by
  unfold SMT.eraseFromContext
  mintro pre ∀S; mpure pre
  mspec Std.Do.Spec.modifyGet_StateT

/-- The `eraseFromContext` `forIn` loop leaves `declarations` unchanged. -/
theorem SMT.eraseFromContext_forIn_decls (zs : List SMT.𝒱) {decl : SMT.Chunk} :
    ⦃ λ ⟨E, _⟩ ↦ ⌜E.declarations = decl⌝ ⦄
    forIn zs PUnit.unit (fun (v : SMT.𝒱) _ => do
      SMT.eraseFromContext v; pure (ForInStep.yield PUnit.unit))
    ⦃ ⇓ () ⟨E, _⟩ => ⌜E.declarations = decl⌝ ⦄ := by
  induction zs with
  | nil =>
    mintro pre ∀S; mpure pre
    simp only [List.forIn_nil]
    mspec Std.Do.Spec.pure
  | cons z zs ih =>
    mintro pre ∀S; mpure pre
    simp only [List.forIn_cons, bind_assoc]
    unfold SMT.eraseFromContext
    mspec Std.Do.Spec.modifyGet_StateT
    mspec Std.Do.Spec.pure
    mspec ih

/-- State spec for the final `eraseFromContext` `forIn` loop of the `all`
encoder: after erasing each `v ∈ zs`, the context is `zs.foldl (·.erase ·) Γ`,
and `freshvarsc`/`usedVars` are unchanged. -/
theorem SMT.eraseFromContext_forIn_spec (zs : List SMT.𝒱) {Γ : SMT.TypeContext}
    {n : ℕ} {used : List SMT.𝒱} :
    ⦃ λ ⟨E, Λ⟩ ↦ ⌜Λ = Γ ∧ E.freshvarsc = n ∧ E.usedVars = used⌝ ⦄
    forIn zs PUnit.unit (fun (v : SMT.𝒱) _ => do
      SMT.eraseFromContext v; pure (ForInStep.yield PUnit.unit))
    ⦃ ⇓ () ⟨E, Λ⟩ => ⌜Λ = zs.foldl (fun Γ v => Γ.erase v) Γ ∧
      E.freshvarsc = n ∧ E.usedVars = used⌝ ⦄ := by
  induction zs generalizing Γ with
  | nil =>
    mintro pre ∀S; mpure pre; obtain ⟨rfl, rfl, rfl⟩ := pre
    simp only [List.forIn_nil]
    mpure_intro; exact ⟨rfl, rfl, rfl⟩
  | cons z zs ih =>
    mintro pre ∀S; mpure pre; obtain ⟨rfl, rfl, rfl⟩ := pre
    simp only [List.forIn_cons, bind_assoc]
    mspec SMT.eraseFromContext_spec
    mspec Std.Do.Spec.pure
    simp only [List.foldl_cons]
    exact ih

/-- `freshVarList` leaves `declarations` unchanged (only calls `freshVar`). -/
theorem SMT.freshVarList_decls (τs : List SMTType) {decl : SMT.Chunk} :
    ⦃ λ ⟨E, _⟩ ↦ ⌜E.declarations = decl⌝ ⦄
    SMT.freshVarList τs
    ⦃ ⇓ _ ⟨E, _⟩ => ⌜E.declarations = decl⌝ ⦄ := by
  induction τs with
  | nil =>
    mintro pre ∀S; mpure pre
    show _ ⊢ₛ wp⟦(pure [] : Encoder (List SMT.𝒱))⟧ _ _
    mspec Std.Do.Spec.pure
  | cons τ τs ih =>
    mintro pre ∀S; mpure pre
    show _ ⊢ₛ wp⟦(List.cons <$> SMT.freshVar τ <*> SMT.freshVarList τs : Encoder (List SMT.𝒱))⟧ _ _
    rw [show (List.cons <$> SMT.freshVar τ <*> SMT.freshVarList τs : Encoder (List SMT.𝒱)) =
         (do let v ← SMT.freshVar τ; let vs ← SMT.freshVarList τs; pure (v :: vs)) from rfl]
    mspec SMT.freshVar_decls
    case post.success =>
    mintro ∀S₁; mrename_i pre; mpure pre
    mspec ih
    mpure_intro
    simp_all

/-- `toDestPair` produces at least `vs.length` entries. -/
private theorem toDestPair_len_ge (vs : List SMT.𝒱) (t₀ : SMT.Term) :
    vs.length ≤ (toDestPair vs t₀).length := by
  suffices h : ∀ (ws : List SMT.𝒱) (zp : SMT.Term) (acc : List SMT.Term) (d : SMT.Term),
      ws.length + acc.length ≤ (toDestPair ws zp acc d).length by
    simpa using h vs t₀ [] t₀
  intro ws
  induction ws with
  | nil => intro _ acc _; simp [toDestPair]
  | cons w ws' ih =>
    intro zp acc d
    cases ws' with
    | nil => simp [toDestPair]; omega
    | cons w' ws'' =>
      simp only [toDestPair]
      have := ih (.fst d) (.snd d :: acc) (.fst d)
      simp [List.length] at this ⊢; omega


/-- Free vars of a generated spec body embed into a larger context when each of
the two components (source vars, declared helpers) embeds.
The workhorse for propagating the `decl_post` spec-body clause through compound
cases of `encodeTerm_combined`. -/
theorem specBody_mono {b : SMT.Term} {vx vt dx dt : List SMT.𝒱}
    (hv : vx ⊆ vt) (hd : dx ⊆ dt)
    (h : SMT.fv b ⊆ vx ∪ dx) : SMT.fv b ⊆ vt ∪ dt := by
  intro w hw
  rcases List.mem_union_iff.mp (h hw) with hvv | hdd
  · exact List.mem_union_iff.mpr (.inl (hv hvv))
  · exact List.mem_union_iff.mpr (.inr (hd hdd))

/-- The `ex_binders` produced by the `all` encoder (`filterMap`-ing
`declare_const` instructions to `(v, τ)` pairs) project onto exactly the
`declVars` of the chunk. -/
theorem map_fst_exBinders_eq_declVars (decls : SMT.Chunk) :
    (decls.filterMap (fun | .declare_const v τ => some (v, τ) | _ => none)).map Prod.fst
      = declVars decls := by
  unfold declVars
  induction decls with
  | nil => rfl
  | cons i is ih =>
    cases i <;> simp_all

/-- The `spec_bodies` produced by the `all` encoder (`filterMap`-ing
`define_fun _ unit bool` instructions to their bodies) is exactly `specBodies`. -/
theorem filterMap_specBodies_eq (decls : SMT.Chunk) :
    decls.filterMap (fun | .define_fun _ .unit .bool b => some b | _ => none)
      = specBodies decls := rfl

/-- Free vars of an `.imp`-right-fold: a variable is free iff it is free in one
of the folded clauses or in the base term.  Used in the `all` case to analyse
`inner = spec_bodies.foldr (.imp · ·) base`. -/
theorem mem_fv_foldr_imp {bs : List SMT.Term} {base : SMT.Term} {v : SMT.𝒱}
    (hv : v ∈ SMT.fv (bs.foldr (.imp · ·) base)) :
    (∃ b ∈ bs, v ∈ SMT.fv b) ∨ v ∈ SMT.fv base := by
  induction bs with
  | nil => exact Or.inr hv
  | cons b bs ih =>
    simp only [List.foldr_cons, SMT.fv, List.mem_append] at hv
    rcases hv with hb | hrest
    · exact Or.inl ⟨b, List.mem_cons_self .., hb⟩
    · rcases ih hrest with ⟨b', hb', hvb'⟩ | hbase
      · exact Or.inl ⟨b', List.mem_cons_of_mem _ hb', hvb'⟩
      · exact Or.inr hbase

/-- Free vars of a `.forall`-binder right-fold: a variable free in the result is
free in the body `inner` and is not one of the bound binder names.  Used in the
`all` case to analyse `scoped_body = ex_binders.foldr (fun (v,τ) t => .forall …)`. -/
theorem mem_fv_foldr_forall {ps : List (SMT.𝒱 × SMTType)} {inner : SMT.Term}
    {v : SMT.𝒱}
    (hv : v ∈ SMT.fv (ps.foldr (fun (p : SMT.𝒱 × SMTType) t => SMT.Term.forall [p.1] [p.2] t)
      inner)) :
    v ∈ SMT.fv inner ∧ v ∉ ps.map Prod.fst := by
  induction ps with
  | nil => exact ⟨hv, by simp⟩
  | cons p ps ih =>
    simp only [List.foldr_cons, SMT.fv, List.mem_removeAll_iff, List.mem_singleton] at hv
    obtain ⟨hv_inner, hv_ne⟩ := hv
    obtain ⟨hv_in, hv_notMem⟩ := ih hv_inner
    refine ⟨hv_in, ?_⟩
    simp only [List.map_cons, List.mem_cons, not_or]
    exact ⟨hv_ne, hv_notMem⟩

set_option maxHeartbeats 16000000 in
/-- Combined structural specification of `encodeTerm`: the `encodeTerm_state`
postcondition (with conjunct 5 weakened by `B.Term.vars t` slack) **and** the
`encodeTerm_decl` postcondition (declarations grow by a `Dlt`, the encoded term's
free vars and every generated spec body are bounded by source vars plus declared
helpers), proven by **one** induction over `B.Term`.

The `all` case genuinely needs both halves at once: its conjunct-5 bound on the
encoded `∀`-body relies on the decl-side spec-body facts for the sub-term `P`,
while the decl-side cast cases need the state-side facts. Neither `encodeTerm_state`
nor `encodeTerm_decl` can be a standalone lemma usable by the other, hence the
single combined induction. `encodeTerm_state` / `encodeTerm_decl` are re-derived
as the `.1` / `.2` projections (see corollaries below). -/
theorem encodeTerm_combined
    (E : B.Env) {Λ : SMT.TypeContext} {t : B.Term} {α : B.BType}
    (typ_t : E.context ⊢ᴮ t : α)
    {used : List SMT.𝒱}
    (vars_used : ∀ v ∈ t.vars, v ∈ used)
    (Λ_inv : ∀ v ∈ t.vars, v ∈ Λ → v ∈ E.context)
    (bv_nodup : (B.bv t).Nodup)
    {n : ℕ} {decl : SMT.Chunk} :
    ⦃ fun (⟨E0, Λ'⟩ : EncoderState) ↦
        ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used ∧
          E0.declarations = decl⌝ ⦄
    encodeTerm t E
    ⦃ ⇓? (⟨t', _σ⟩ : SMT.Term × SMTType) (⟨E', Γ'⟩ : EncoderState) => ⌜
      (used ⊆ E'.usedVars ∧
       Λ ⊆ Γ' ∧
       AList.keys Γ' ⊆ E'.usedVars ∧
       B.CoversUsedVars E'.usedVars t ∧
       SMT.fv t' ⊆ AList.keys Γ' ∪ B.Term.vars t ∧
       (∀ v ∈ used, v ∉ Λ → v ∉ B.Term.vars t → v ∉ Γ')) ∧
      (∃ Dlt : SMT.Chunk,
        E'.declarations = decl ++ Dlt ∧
        (∀ b ∈ specBodies Dlt, SMT.fv b ⊆ B.Term.vars t ∪ declVars Dlt) ∧
        SMT.fv t' ⊆ B.Term.vars t ∪ declVars Dlt) ⌝⦄ := by
  induction t generalizing E n used Λ α decl with
  | int i =>
    mstart
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq, rfl⟩ := pre
    rw [encodeTerm]
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, [], by simp, by simp, ?_⟩
    · intro v hv; simpa [St_used_eq] using hv
    · intro v hv; simpa using hv
    · intro v hv; simpa [St_used_eq] using St_sub hv
    · intro v hv; simp [B.fv] at hv
    · intro v hv; simp [SMT.fv] at hv
    · exact fun _ _ h _ => h
    · intro v hv; simp [SMT.fv] at hv
  | bool b =>
    mstart
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq, rfl⟩ := pre
    rw [encodeTerm]
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, [], by simp, by simp, ?_⟩
    · intro v hv; simpa [St_used_eq] using hv
    · intro v hv; simpa using hv
    · intro v hv; simpa [St_used_eq] using St_sub hv
    · intro v hv; simp [B.fv] at hv
    · intro v hv; simp [SMT.fv] at hv
    · exact fun _ _ h _ => h
    · intro v hv; simp [SMT.fv] at hv
  | var v =>
    mstart
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq, rfl⟩ := pre
    rw [encodeTerm]
    mvcgen
    case vc1 τ τ_lookup =>
      have hv_in_types : v ∈ St.types :=
        AList.lookup_isSome.1 (Option.isSome_of_eq_some τ_lookup)
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, [], by simp, by simp, ?_⟩
      · intro x hx; simpa [St_used_eq] using hx
      · intro x hx; simpa using hx
      · intro x hx; simpa [St_used_eq] using St_sub hx
      · intro x hx
        rw [B.fv, List.mem_singleton] at hx
        subst x
        simpa [St_used_eq] using (St_sub (AList.mem_keys.mpr hv_in_types))
      · intro x hx
        rw [SMT.fv, List.mem_singleton] at hx
        subst x
        exact List.mem_union_iff.mpr (.inl (AList.mem_keys.mpr hv_in_types))
      · exact fun _ _ h _ => h
      · intro x hx
        rw [SMT.fv, List.mem_singleton] at hx
        subst x
        exact List.mem_union_iff.mpr (.inl (B.Term.mem_vars_iff.mpr (.inl B.fv.mem_var)))
  | «ℤ» =>
    mstart
    mintro pre ∀S
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq, rfl⟩ := pre
    rw [encodeTerm]
    mspec Std.Do.Spec.get_StateT
    mspec (Std.Do.Triple.and (SMT.freshVar .int)
      (SMT.freshVar_spec (Γ := S.types) (τ := .int) (n := S.env.freshvarsc)
        (used := S.env.usedVars))
      (SMT.freshVar_decls (τ := .int) (decl := S.env.declarations)))
    case post.success 𝓋 =>
      mrename_i pre
      mintro ∀S'
      mpure pre
      obtain ⟨⟨types_eq, 𝓋_notMem, freshvarsc_eq, used_eq, 𝓋_neq_used⟩, decl_eq⟩ := pre
      mspec Std.Do.Spec.modifyGet_StateT
      mspec Std.Do.Spec.pure
      mpure_intro
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, [], by simpa using decl_eq, by simp, ?_⟩
      · intro x hx; rw [used_eq, St_used_eq]; exact List.mem_cons_of_mem _ hx
      · exact fun _ => id
      · rw [used_eq]; intro x hx; exact List.mem_cons_of_mem _ (St_sub hx)
      · intro x hx; rw [B.fv] at hx; contradiction
      · intro x hx; simp only [SMT.fv, List.mem_removeAll_iff] at hx; nomatch hx.1
      · exact fun _ _ h _ => h
      · intro x hx; simp only [SMT.fv, List.mem_removeAll_iff] at hx; nomatch hx.1
  | 𝔹 =>
    mstart
    mintro pre ∀S
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq, rfl⟩ := pre
    rw [encodeTerm]
    mspec Std.Do.Spec.get_StateT
    mspec (Std.Do.Triple.and (SMT.freshVar .bool)
      (SMT.freshVar_spec (Γ := S.types) (τ := .bool) (n := S.env.freshvarsc)
        (used := S.env.usedVars))
      (SMT.freshVar_decls (τ := .bool) (decl := S.env.declarations)))
    case post.success 𝓋 =>
      mrename_i pre
      mintro ∀S'
      mpure pre
      obtain ⟨⟨types_eq, 𝓋_notMem, freshvarsc_eq, used_eq, 𝓋_neq_used⟩, decl_eq⟩ := pre
      mspec Std.Do.Spec.modifyGet_StateT
      mspec Std.Do.Spec.pure
      mpure_intro
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, [], by simpa using decl_eq, by simp, ?_⟩
      · intro x hx; rw [used_eq, St_used_eq]; exact List.mem_cons_of_mem _ hx
      · exact fun _ => id
      · rw [used_eq]; intro x hx; exact List.mem_cons_of_mem _ (St_sub hx)
      · intro x hx; rw [B.fv] at hx; contradiction
      · intro x hx; simp only [SMT.fv, List.mem_removeAll_iff] at hx; nomatch hx.1
      · exact fun _ _ h _ => h
      · intro x hx; simp only [SMT.fv, List.mem_removeAll_iff] at hx; nomatch hx.1
  | maplet x y x_ih y_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq, rfl⟩ := pre
    rw [encodeTerm]
    obtain ⟨αx, βx, rfl, typ_x, typ_y⟩ := B.Typing.mapletE typ_t
    have hx_bv_nodup : (B.bv x).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.1
    have hy_bv_nodup : (B.bv y).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.2.1
    have hxy_bv_disj : ∀ a ∈ B.bv x, ∀ b ∈ B.bv y, a ≠ b := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.2.2
    have vars_used_x : ∀ v ∈ x.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h)
    have vars_used_y : ∀ v ∈ y.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inr h)
    have Λ_inv_x : ∀ v ∈ x.vars, v ∈ σ.types → v ∈ E.context := fun v hv => Λ_inv v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h)
    mspec x_ih (E := E) (Λ := σ.types) (decl := σ.env.declarations)
      typ_x vars_used_x Λ_inv_x hx_bv_nodup
    clear x_ih
    rename_i out_x
    obtain ⟨x_enc, σx⟩ := out_x
    mrename_i pre
    mintro ∀σ_x
    mpure pre
    obtain ⟨⟨x_used_sub, x_Λ_sub, x_keys_sub, x_cov, x_fv_sub, x_preserves⟩,
      Δx, x_decl_eq, x_specb, x_enc_fv_sub⟩ := pre
    have Λ_inv_y : ∀ v ∈ y.vars, v ∈ σ_x.types → v ∈ E.context := fun v hv hΛ => by
      have hv_par : v ∈ (x ↦ᴮ y).vars := by
        simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
        rcases hv with h | h <;> [left; right] <;> exact .inr h
      by_cases hv_St : v ∈ σ.types
      · exact Λ_inv v hv_par hv_St
      · have hv_vars_x : v ∈ B.Term.vars x := by
          by_contra h_neg
          exact absurd hΛ (x_preserves v (vars_used v hv_par) hv_St h_neg)
        rcases B.Term.mem_vars_iff.mp hv_vars_x with h | h
        · exact _root_.B.Typing.typed_by_fv typ_x h
        · rcases B.Term.mem_vars_iff.mp hv with hy_fv | hy_bv
          · exact absurd (_root_.B.Typing.typed_by_fv typ_y hy_fv)
              (_root_.B.Typing.bv_notMem_context typ_x v h)
          · exact absurd rfl (hxy_bv_disj v h v hy_bv)
    mspec y_ih (E := E) (Λ := σ_x.types) (used := σ_x.env.usedVars)
      (decl := σ.env.declarations ++ Δx)
      typ_y (fun v hv => x_used_sub (vars_used_y v hv)) Λ_inv_y hy_bv_nodup
    clear y_ih
    rename_i out_y
    obtain ⟨y_enc, σy⟩ := out_y
    mrename_i pre
    mintro ∀σ_y
    mpure pre
    obtain ⟨⟨y_used_sub, y_Λ_sub, y_keys_sub, y_cov, y_fv_sub, y_preserves⟩,
      Δy, y_decl_eq, y_specb, y_enc_fv_sub⟩ := pre
    mpure_intro
    have hbv_par : B.bv (x ↦ᴮ y) = B.bv x ++ B.bv y := by rw [B.bv]
    have hvars_x_sub : B.Term.vars x ⊆ B.Term.vars (x ↦ᴮ y) := fun v hv => by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h
    have hvars_y_sub : B.Term.vars y ⊆ B.Term.vars (x ↦ᴮ y) := fun v hv => by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inr h
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, Δx ++ Δy, ?_, ?_, ?_⟩
    · exact fun v hv => y_used_sub (x_used_sub hv)
    · exact AList.subset_trans x_Λ_sub y_Λ_sub
    · exact y_keys_sub
    · intro v hv
      rw [B.fv, List.mem_append] at hv
      rcases hv with hv | hv
      · exact y_used_sub (x_cov v hv)
      · exact y_cov v hv
    · intro v hv
      rw [SMT.fv, List.mem_append] at hv
      rcases hv with hv | hv
      · rcases List.mem_union_iff.mp (x_fv_sub hv) with hk | hb
        · exact List.mem_union_iff.mpr (.inl (AList.mem_keys.mpr
            (AList.mem_of_subset y_Λ_sub (AList.mem_keys.mp hk))))
        · exact List.mem_union_iff.mpr (.inr (hvars_x_sub hb))
      · rcases List.mem_union_iff.mp (y_fv_sub hv) with hk | hb
        · exact List.mem_union_iff.mpr (.inl hk)
        · exact List.mem_union_iff.mpr (.inr (hvars_y_sub hb))
    · intro v hv hΛ hvars
      have hvx : v ∉ B.Term.vars x := fun h => hvars (hvars_x_sub h)
      have hvy : v ∉ B.Term.vars y := fun h => hvars (hvars_y_sub h)
      exact y_preserves v (x_used_sub hv) (x_preserves v hv hΛ hvx) hvy
    · rw [y_decl_eq, List.append_assoc]
    · intro b hb
      rw [specBodies_append, List.mem_append] at hb
      rcases hb with hb | hb
      · exact specBody_mono hvars_x_sub (declVars_append .. ▸ List.subset_append_left ..)
          (x_specb b hb)
      · exact specBody_mono hvars_y_sub (declVars_append .. ▸ List.subset_append_right ..)
          (y_specb b hb)
    · intro v hv
      rw [SMT.fv, List.mem_append] at hv
      rw [declVars_append]
      rcases hv with hv | hv
      · rcases List.mem_union_iff.mp (x_enc_fv_sub hv) with h | h
        · exact List.mem_union_iff.mpr (.inl (hvars_x_sub h))
        · exact List.mem_union_iff.mpr (.inr (List.mem_append_left _ h))
      · rcases List.mem_union_iff.mp (y_enc_fv_sub hv) with h | h
        · exact List.mem_union_iff.mpr (.inl (hvars_y_sub h))
        · exact List.mem_union_iff.mpr (.inr (List.mem_append_right _ h))
  | add x y x_ih y_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq, rfl⟩ := pre
    rw [encodeTerm]
    obtain ⟨rfl, typ_x, typ_y⟩ := B.Typing.addE typ_t
    have hx_bv_nodup : (B.bv x).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.1
    have hy_bv_nodup : (B.bv y).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.2.1
    have hxy_bv_disj : ∀ a ∈ B.bv x, ∀ b ∈ B.bv y, a ≠ b := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.2.2
    have vars_used_x : ∀ v ∈ x.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h)
    have vars_used_y : ∀ v ∈ y.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inr h)
    have Λ_inv_x : ∀ v ∈ x.vars, v ∈ σ.types → v ∈ E.context := fun v hv => Λ_inv v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h)
    mspec x_ih (E := E) (Λ := σ.types) (decl := σ.env.declarations)
      typ_x vars_used_x Λ_inv_x hx_bv_nodup
    rename_i out_x
    obtain ⟨x_enc, σx⟩ := out_x
    mrename_i prex
    mintro ∀σ_x
    mpure prex
    obtain ⟨⟨x_used_sub, x_Λ_sub, x_keys_sub, x_cov, x_fv_sub, x_preserves⟩,
      Δx, x_decl_eq, x_specb, x_enc_fv_sub⟩ := prex
    have Λ_inv_y : ∀ v ∈ y.vars, v ∈ σ_x.types → v ∈ E.context := fun v hv hΛ => by
      have hv_par : v ∈ (x +ᴮ y).vars := by
        simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
        rcases hv with h | h <;> [left; right] <;> exact .inr h
      by_cases hv_St : v ∈ σ.types
      · exact Λ_inv v hv_par hv_St
      · have hv_vars_x : v ∈ B.Term.vars x := by
          by_contra h_neg
          exact absurd hΛ (x_preserves v (vars_used v hv_par) hv_St h_neg)
        rcases B.Term.mem_vars_iff.mp hv_vars_x with h | h
        · exact _root_.B.Typing.typed_by_fv typ_x h
        · rcases B.Term.mem_vars_iff.mp hv with hy_fv | hy_bv
          · exact absurd (_root_.B.Typing.typed_by_fv typ_y hy_fv)
              (_root_.B.Typing.bv_notMem_context typ_x v h)
          · exact absurd rfl (hxy_bv_disj v h v hy_bv)
    have hbv_par : B.bv (x +ᴮ y) = B.bv x ++ B.bv y := by rw [B.bv]
    have hvars_x_sub : B.Term.vars x ⊆ B.Term.vars (x +ᴮ y) := fun v hv => by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h
    have hvars_y_sub : B.Term.vars y ⊆ B.Term.vars (x +ᴮ y) := fun v hv => by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inr h
    split
    · rename_i heq
      injection heq with hxe hσe
      subst hσe
      subst hxe
      mspec y_ih (E := E) (Λ := σ_x.types) (used := σ_x.env.usedVars)
        (decl := σ.env.declarations ++ Δx)
        typ_y (fun v hv => x_used_sub (vars_used_y v hv)) Λ_inv_y hy_bv_nodup
      rename_i out_y
      obtain ⟨y_enc, σy⟩ := out_y
      mrename_i prey
      mintro ∀σ_y
      mpure prey
      obtain ⟨⟨y_used_sub, y_Λ_sub, y_keys_sub, y_cov, y_fv_sub, y_preserves⟩,
        Δy, y_decl_eq, y_specb, y_enc_fv_sub⟩ := prey
      split
      · rename_i heq2
        injection heq2 with hye hσe2
        subst hσe2
        subst hye
        mspec Std.Do.Spec.pure
        mpure_intro
        refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, Δx ++ Δy, ?_, ?_, ?_⟩
        · exact fun v hv => y_used_sub (x_used_sub hv)
        · exact AList.subset_trans x_Λ_sub y_Λ_sub
        · exact y_keys_sub
        · intro v hv
          rw [B.fv, List.mem_append] at hv
          rcases hv with hv | hv
          · exact y_used_sub (x_cov v hv)
          · exact y_cov v hv
        · intro v hv
          rw [SMT.fv, List.mem_append] at hv
          rcases hv with hv | hv
          · rcases List.mem_union_iff.mp (x_fv_sub hv) with hk | hb
            · exact List.mem_union_iff.mpr (.inl (AList.mem_keys.mpr
                (AList.mem_of_subset y_Λ_sub (AList.mem_keys.mp hk))))
            · exact List.mem_union_iff.mpr (.inr (hvars_x_sub hb))
          · rcases List.mem_union_iff.mp (y_fv_sub hv) with hk | hb
            · exact List.mem_union_iff.mpr (.inl hk)
            · exact List.mem_union_iff.mpr (.inr (hvars_y_sub hb))
        · intro v hv hΛ hvars
          have hvx : v ∉ B.Term.vars x := fun h => hvars (hvars_x_sub h)
          have hvy : v ∉ B.Term.vars y := fun h => hvars (hvars_y_sub h)
          exact y_preserves v (x_used_sub hv) (x_preserves v hv hΛ hvx) hvy
        · rw [y_decl_eq, List.append_assoc]
        · intro b hb
          rw [specBodies_append, List.mem_append] at hb
          rcases hb with hb | hb
          · exact specBody_mono hvars_x_sub (declVars_append .. ▸ List.subset_append_left ..)
              (x_specb b hb)
          · exact specBody_mono hvars_y_sub (declVars_append .. ▸ List.subset_append_right ..)
              (y_specb b hb)
        · intro v hv
          rw [SMT.fv, List.mem_append] at hv
          rw [declVars_append]
          rcases hv with hv | hv
          · rcases List.mem_union_iff.mp (x_enc_fv_sub hv) with h | h
            · exact List.mem_union_iff.mpr (.inl (hvars_x_sub h))
            · exact List.mem_union_iff.mpr (.inr (List.mem_append_left _ h))
          · rcases List.mem_union_iff.mp (y_enc_fv_sub hv) with h | h
            · exact List.mem_union_iff.mpr (.inl (hvars_y_sub h))
            · exact List.mem_union_iff.mpr (.inr (List.mem_append_right _ h))
      · exact wp_bind_throw _ _ _ _
    · exact wp_bind_throw _ _ _ _
  | sub x y x_ih y_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq, rfl⟩ := pre
    rw [encodeTerm]
    obtain ⟨rfl, typ_x, typ_y⟩ := B.Typing.subE typ_t
    have hx_bv_nodup : (B.bv x).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.1
    have hy_bv_nodup : (B.bv y).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.2.1
    have hxy_bv_disj : ∀ a ∈ B.bv x, ∀ b ∈ B.bv y, a ≠ b := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.2.2
    have vars_used_x : ∀ v ∈ x.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h)
    have vars_used_y : ∀ v ∈ y.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inr h)
    have Λ_inv_x : ∀ v ∈ x.vars, v ∈ σ.types → v ∈ E.context := fun v hv => Λ_inv v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h)
    mspec x_ih (E := E) (Λ := σ.types) (decl := σ.env.declarations)
      typ_x vars_used_x Λ_inv_x hx_bv_nodup
    rename_i out_x
    obtain ⟨x_enc, σx⟩ := out_x
    mrename_i prex
    mintro ∀σ_x
    mpure prex
    obtain ⟨⟨x_used_sub, x_Λ_sub, x_keys_sub, x_cov, x_fv_sub, x_preserves⟩,
      Δx, x_decl_eq, x_specb, x_enc_fv_sub⟩ := prex
    have Λ_inv_y : ∀ v ∈ y.vars, v ∈ σ_x.types → v ∈ E.context := fun v hv hΛ => by
      have hv_par : v ∈ (x -ᴮ y).vars := by
        simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
        rcases hv with h | h <;> [left; right] <;> exact .inr h
      by_cases hv_St : v ∈ σ.types
      · exact Λ_inv v hv_par hv_St
      · have hv_vars_x : v ∈ B.Term.vars x := by
          by_contra h_neg
          exact absurd hΛ (x_preserves v (vars_used v hv_par) hv_St h_neg)
        rcases B.Term.mem_vars_iff.mp hv_vars_x with h | h
        · exact _root_.B.Typing.typed_by_fv typ_x h
        · rcases B.Term.mem_vars_iff.mp hv with hy_fv | hy_bv
          · exact absurd (_root_.B.Typing.typed_by_fv typ_y hy_fv)
              (_root_.B.Typing.bv_notMem_context typ_x v h)
          · exact absurd rfl (hxy_bv_disj v h v hy_bv)
    have hbv_par : B.bv (x -ᴮ y) = B.bv x ++ B.bv y := by rw [B.bv]
    have hvars_x_sub : B.Term.vars x ⊆ B.Term.vars (x -ᴮ y) := fun v hv => by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h
    have hvars_y_sub : B.Term.vars y ⊆ B.Term.vars (x -ᴮ y) := fun v hv => by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inr h
    split
    · rename_i heq
      injection heq with hxe hσe
      subst hσe
      subst hxe
      mspec y_ih (E := E) (Λ := σ_x.types) (used := σ_x.env.usedVars)
        (decl := σ.env.declarations ++ Δx)
        typ_y (fun v hv => x_used_sub (vars_used_y v hv)) Λ_inv_y hy_bv_nodup
      rename_i out_y
      obtain ⟨y_enc, σy⟩ := out_y
      mrename_i prey
      mintro ∀σ_y
      mpure prey
      obtain ⟨⟨y_used_sub, y_Λ_sub, y_keys_sub, y_cov, y_fv_sub, y_preserves⟩,
        Δy, y_decl_eq, y_specb, y_enc_fv_sub⟩ := prey
      split
      · rename_i heq2
        injection heq2 with hye hσe2
        subst hσe2
        subst hye
        mspec Std.Do.Spec.pure
        mpure_intro
        refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, Δx ++ Δy, ?_, ?_, ?_⟩
        · exact fun v hv => y_used_sub (x_used_sub hv)
        · exact AList.subset_trans x_Λ_sub y_Λ_sub
        · exact y_keys_sub
        · intro v hv
          rw [B.fv, List.mem_append] at hv
          rcases hv with hv | hv
          · exact y_used_sub (x_cov v hv)
          · exact y_cov v hv
        · intro v hv
          rw [SMT.fv, List.mem_append] at hv
          rcases hv with hv | hv
          · rcases List.mem_union_iff.mp (x_fv_sub hv) with hk | hb
            · exact List.mem_union_iff.mpr (.inl (AList.mem_keys.mpr
                (AList.mem_of_subset y_Λ_sub (AList.mem_keys.mp hk))))
            · exact List.mem_union_iff.mpr (.inr (hvars_x_sub hb))
          · rcases List.mem_union_iff.mp (y_fv_sub hv) with hk | hb
            · exact List.mem_union_iff.mpr (.inl hk)
            · exact List.mem_union_iff.mpr (.inr (hvars_y_sub hb))
        · intro v hv hΛ hvars
          have hvx : v ∉ B.Term.vars x := fun h => hvars (hvars_x_sub h)
          have hvy : v ∉ B.Term.vars y := fun h => hvars (hvars_y_sub h)
          exact y_preserves v (x_used_sub hv) (x_preserves v hv hΛ hvx) hvy
        · rw [y_decl_eq, List.append_assoc]
        · intro b hb
          rw [specBodies_append, List.mem_append] at hb
          rcases hb with hb | hb
          · exact specBody_mono hvars_x_sub (declVars_append .. ▸ List.subset_append_left ..)
              (x_specb b hb)
          · exact specBody_mono hvars_y_sub (declVars_append .. ▸ List.subset_append_right ..)
              (y_specb b hb)
        · intro v hv
          rw [SMT.fv, List.mem_append] at hv
          rw [declVars_append]
          rcases hv with hv | hv
          · rcases List.mem_union_iff.mp (x_enc_fv_sub hv) with h | h
            · exact List.mem_union_iff.mpr (.inl (hvars_x_sub h))
            · exact List.mem_union_iff.mpr (.inr (List.mem_append_left _ h))
          · rcases List.mem_union_iff.mp (y_enc_fv_sub hv) with h | h
            · exact List.mem_union_iff.mpr (.inl (hvars_y_sub h))
            · exact List.mem_union_iff.mpr (.inr (List.mem_append_right _ h))
      · exact wp_bind_throw _ _ _ _
    · exact wp_bind_throw _ _ _ _
  | mul x y x_ih y_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq, rfl⟩ := pre
    rw [encodeTerm]
    obtain ⟨rfl, typ_x, typ_y⟩ := B.Typing.mulE typ_t
    have hx_bv_nodup : (B.bv x).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.1
    have hy_bv_nodup : (B.bv y).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.2.1
    have hxy_bv_disj : ∀ a ∈ B.bv x, ∀ b ∈ B.bv y, a ≠ b := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.2.2
    have vars_used_x : ∀ v ∈ x.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h)
    have vars_used_y : ∀ v ∈ y.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inr h)
    have Λ_inv_x : ∀ v ∈ x.vars, v ∈ σ.types → v ∈ E.context := fun v hv => Λ_inv v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h)
    mspec x_ih (E := E) (Λ := σ.types) (decl := σ.env.declarations)
      typ_x vars_used_x Λ_inv_x hx_bv_nodup
    rename_i out_x
    obtain ⟨x_enc, σx⟩ := out_x
    mrename_i prex
    mintro ∀σ_x
    mpure prex
    obtain ⟨⟨x_used_sub, x_Λ_sub, x_keys_sub, x_cov, x_fv_sub, x_preserves⟩,
      Δx, x_decl_eq, x_specb, x_enc_fv_sub⟩ := prex
    have Λ_inv_y : ∀ v ∈ y.vars, v ∈ σ_x.types → v ∈ E.context := fun v hv hΛ => by
      have hv_par : v ∈ (x *ᴮ y).vars := by
        simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
        rcases hv with h | h <;> [left; right] <;> exact .inr h
      by_cases hv_St : v ∈ σ.types
      · exact Λ_inv v hv_par hv_St
      · have hv_vars_x : v ∈ B.Term.vars x := by
          by_contra h_neg
          exact absurd hΛ (x_preserves v (vars_used v hv_par) hv_St h_neg)
        rcases B.Term.mem_vars_iff.mp hv_vars_x with h | h
        · exact _root_.B.Typing.typed_by_fv typ_x h
        · rcases B.Term.mem_vars_iff.mp hv with hy_fv | hy_bv
          · exact absurd (_root_.B.Typing.typed_by_fv typ_y hy_fv)
              (_root_.B.Typing.bv_notMem_context typ_x v h)
          · exact absurd rfl (hxy_bv_disj v h v hy_bv)
    have hbv_par : B.bv (x *ᴮ y) = B.bv x ++ B.bv y := by rw [B.bv]
    have hvars_x_sub : B.Term.vars x ⊆ B.Term.vars (x *ᴮ y) := fun v hv => by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h
    have hvars_y_sub : B.Term.vars y ⊆ B.Term.vars (x *ᴮ y) := fun v hv => by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inr h
    split
    · rename_i heq
      injection heq with hxe hσe
      subst hσe
      subst hxe
      mspec y_ih (E := E) (Λ := σ_x.types) (used := σ_x.env.usedVars)
        (decl := σ.env.declarations ++ Δx)
        typ_y (fun v hv => x_used_sub (vars_used_y v hv)) Λ_inv_y hy_bv_nodup
      rename_i out_y
      obtain ⟨y_enc, σy⟩ := out_y
      mrename_i prey
      mintro ∀σ_y
      mpure prey
      obtain ⟨⟨y_used_sub, y_Λ_sub, y_keys_sub, y_cov, y_fv_sub, y_preserves⟩,
        Δy, y_decl_eq, y_specb, y_enc_fv_sub⟩ := prey
      split
      · rename_i heq2
        injection heq2 with hye hσe2
        subst hσe2
        subst hye
        mspec Std.Do.Spec.pure
        mpure_intro
        refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, Δx ++ Δy, ?_, ?_, ?_⟩
        · exact fun v hv => y_used_sub (x_used_sub hv)
        · exact AList.subset_trans x_Λ_sub y_Λ_sub
        · exact y_keys_sub
        · intro v hv
          rw [B.fv, List.mem_append] at hv
          rcases hv with hv | hv
          · exact y_used_sub (x_cov v hv)
          · exact y_cov v hv
        · intro v hv
          rw [SMT.fv, List.mem_append] at hv
          rcases hv with hv | hv
          · rcases List.mem_union_iff.mp (x_fv_sub hv) with hk | hb
            · exact List.mem_union_iff.mpr (.inl (AList.mem_keys.mpr
                (AList.mem_of_subset y_Λ_sub (AList.mem_keys.mp hk))))
            · exact List.mem_union_iff.mpr (.inr (hvars_x_sub hb))
          · rcases List.mem_union_iff.mp (y_fv_sub hv) with hk | hb
            · exact List.mem_union_iff.mpr (.inl hk)
            · exact List.mem_union_iff.mpr (.inr (hvars_y_sub hb))
        · intro v hv hΛ hvars
          have hvx : v ∉ B.Term.vars x := fun h => hvars (hvars_x_sub h)
          have hvy : v ∉ B.Term.vars y := fun h => hvars (hvars_y_sub h)
          exact y_preserves v (x_used_sub hv) (x_preserves v hv hΛ hvx) hvy
        · rw [y_decl_eq, List.append_assoc]
        · intro b hb
          rw [specBodies_append, List.mem_append] at hb
          rcases hb with hb | hb
          · exact specBody_mono hvars_x_sub (declVars_append .. ▸ List.subset_append_left ..)
              (x_specb b hb)
          · exact specBody_mono hvars_y_sub (declVars_append .. ▸ List.subset_append_right ..)
              (y_specb b hb)
        · intro v hv
          rw [SMT.fv, List.mem_append] at hv
          rw [declVars_append]
          rcases hv with hv | hv
          · rcases List.mem_union_iff.mp (x_enc_fv_sub hv) with h | h
            · exact List.mem_union_iff.mpr (.inl (hvars_x_sub h))
            · exact List.mem_union_iff.mpr (.inr (List.mem_append_left _ h))
          · rcases List.mem_union_iff.mp (y_enc_fv_sub hv) with h | h
            · exact List.mem_union_iff.mpr (.inl (hvars_y_sub h))
            · exact List.mem_union_iff.mpr (.inr (List.mem_append_right _ h))
      · exact wp_bind_throw _ _ _ _
    · exact wp_bind_throw _ _ _ _
  | le x y x_ih y_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq, rfl⟩ := pre
    rw [encodeTerm]
    obtain ⟨rfl, typ_x, typ_y⟩ := B.Typing.leE typ_t
    have hx_bv_nodup : (B.bv x).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.1
    have hy_bv_nodup : (B.bv y).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.2.1
    have hxy_bv_disj : ∀ a ∈ B.bv x, ∀ b ∈ B.bv y, a ≠ b := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.2.2
    have vars_used_x : ∀ v ∈ x.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h)
    have vars_used_y : ∀ v ∈ y.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inr h)
    have Λ_inv_x : ∀ v ∈ x.vars, v ∈ σ.types → v ∈ E.context := fun v hv => Λ_inv v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h)
    mspec x_ih (E := E) (Λ := σ.types) (decl := σ.env.declarations)
      typ_x vars_used_x Λ_inv_x hx_bv_nodup
    clear x_ih
    rename_i out_x
    obtain ⟨x_enc, σx⟩ := out_x
    mrename_i pre
    mintro ∀σ_x
    mpure pre
    obtain ⟨⟨x_used_sub, x_Λ_sub, x_keys_sub, x_cov, x_fv_sub, x_preserves⟩,
      Δx, x_decl_eq, x_specb, x_enc_fv_sub⟩ := pre
    have Λ_inv_y : ∀ v ∈ y.vars, v ∈ σ_x.types → v ∈ E.context := fun v hv hΛ => by
      have hv_par : v ∈ (x ≤ᴮ y).vars := by
        simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
        rcases hv with h | h <;> [left; right] <;> exact .inr h
      by_cases hv_St : v ∈ σ.types
      · exact Λ_inv v hv_par hv_St
      · have hv_vars_x : v ∈ B.Term.vars x := by
          by_contra h_neg
          exact absurd hΛ (x_preserves v (vars_used v hv_par) hv_St h_neg)
        rcases B.Term.mem_vars_iff.mp hv_vars_x with h | h
        · exact _root_.B.Typing.typed_by_fv typ_x h
        · rcases B.Term.mem_vars_iff.mp hv with hy_fv | hy_bv
          · exact absurd (_root_.B.Typing.typed_by_fv typ_y hy_fv)
              (_root_.B.Typing.bv_notMem_context typ_x v h)
          · exact absurd rfl (hxy_bv_disj v h v hy_bv)
    mspec y_ih (E := E) (Λ := σ_x.types) (used := σ_x.env.usedVars)
      (decl := σ.env.declarations ++ Δx)
      typ_y (fun v hv => x_used_sub (vars_used_y v hv)) Λ_inv_y hy_bv_nodup
    clear y_ih
    rename_i out_y
    obtain ⟨y_enc, σy⟩ := out_y
    mrename_i pre
    mintro ∀σ_y
    mpure pre
    obtain ⟨⟨y_used_sub, y_Λ_sub, y_keys_sub, y_cov, y_fv_sub, y_preserves⟩,
      Δy, y_decl_eq, y_specb, y_enc_fv_sub⟩ := pre
    mpure_intro
    have hbv_par : B.bv (x ≤ᴮ y) = B.bv x ++ B.bv y := by rw [B.bv]
    have hvars_x_sub : B.Term.vars x ⊆ B.Term.vars (x ≤ᴮ y) := fun v hv => by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h
    have hvars_y_sub : B.Term.vars y ⊆ B.Term.vars (x ≤ᴮ y) := fun v hv => by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inr h
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, Δx ++ Δy, ?_, ?_, ?_⟩
    · exact fun v hv => y_used_sub (x_used_sub hv)
    · exact AList.subset_trans x_Λ_sub y_Λ_sub
    · exact y_keys_sub
    · intro v hv
      rw [B.fv, List.mem_append] at hv
      rcases hv with hv | hv
      · exact y_used_sub (x_cov v hv)
      · exact y_cov v hv
    · intro v hv
      rw [SMT.fv, List.mem_append] at hv
      rcases hv with hv | hv
      · rcases List.mem_union_iff.mp (x_fv_sub hv) with hk | hb
        · exact List.mem_union_iff.mpr (.inl (AList.mem_keys.mpr
            (AList.mem_of_subset y_Λ_sub (AList.mem_keys.mp hk))))
        · exact List.mem_union_iff.mpr (.inr (hvars_x_sub hb))
      · rcases List.mem_union_iff.mp (y_fv_sub hv) with hk | hb
        · exact List.mem_union_iff.mpr (.inl hk)
        · exact List.mem_union_iff.mpr (.inr (hvars_y_sub hb))
    · intro v hv hΛ hvars
      have hvx : v ∉ B.Term.vars x := fun h => hvars (hvars_x_sub h)
      have hvy : v ∉ B.Term.vars y := fun h => hvars (hvars_y_sub h)
      exact y_preserves v (x_used_sub hv) (x_preserves v hv hΛ hvx) hvy
    · rw [y_decl_eq, List.append_assoc]
    · intro b hb
      rw [specBodies_append, List.mem_append] at hb
      rcases hb with hb | hb
      · exact specBody_mono hvars_x_sub (declVars_append .. ▸ List.subset_append_left ..)
          (x_specb b hb)
      · exact specBody_mono hvars_y_sub (declVars_append .. ▸ List.subset_append_right ..)
          (y_specb b hb)
    · intro v hv
      rw [SMT.fv, List.mem_append] at hv
      rw [declVars_append]
      rcases hv with hv | hv
      · rcases List.mem_union_iff.mp (x_enc_fv_sub hv) with h | h
        · exact List.mem_union_iff.mpr (.inl (hvars_x_sub h))
        · exact List.mem_union_iff.mpr (.inr (List.mem_append_left _ h))
      · rcases List.mem_union_iff.mp (y_enc_fv_sub hv) with h | h
        · exact List.mem_union_iff.mpr (.inl (hvars_y_sub h))
        · exact List.mem_union_iff.mpr (.inr (List.mem_append_right _ h))
  | min S _ih =>
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq, rfl⟩ := pre
    simp only [encodeTerm] <;> mvcgen
  | max S _ih =>
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq, rfl⟩ := pre
    simp only [encodeTerm] <;> mvcgen
  | card S _ih =>
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq, rfl⟩ := pre
    simp only [encodeTerm] <;> mvcgen
  | and x y x_ih y_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq, rfl⟩ := pre
    rw [encodeTerm]
    obtain ⟨rfl, typ_x, typ_y⟩ := B.Typing.andE typ_t
    have hx_bv_nodup : (B.bv x).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.1
    have hy_bv_nodup : (B.bv y).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.2.1
    have hxy_bv_disj : ∀ a ∈ B.bv x, ∀ b ∈ B.bv y, a ≠ b := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.2.2
    have vars_used_x : ∀ v ∈ x.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h)
    have vars_used_y : ∀ v ∈ y.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inr h)
    have Λ_inv_x : ∀ v ∈ x.vars, v ∈ σ.types → v ∈ E.context := fun v hv => Λ_inv v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h)
    mspec x_ih (E := E) (Λ := σ.types) (decl := σ.env.declarations)
      typ_x vars_used_x Λ_inv_x hx_bv_nodup
    rename_i out_x
    obtain ⟨x_enc, σx⟩ := out_x
    mrename_i prex
    mintro ∀σ_x
    mpure prex
    obtain ⟨⟨x_used_sub, x_Λ_sub, x_keys_sub, x_cov, x_fv_sub, x_preserves⟩,
      Δx, x_decl_eq, x_specb, x_enc_fv_sub⟩ := prex
    have Λ_inv_y : ∀ v ∈ y.vars, v ∈ σ_x.types → v ∈ E.context := fun v hv hΛ => by
      have hv_par : v ∈ (x ∧ᴮ y).vars := by
        simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
        rcases hv with h | h <;> [left; right] <;> exact .inr h
      by_cases hv_St : v ∈ σ.types
      · exact Λ_inv v hv_par hv_St
      · have hv_vars_x : v ∈ B.Term.vars x := by
          by_contra h_neg
          exact absurd hΛ (x_preserves v (vars_used v hv_par) hv_St h_neg)
        rcases B.Term.mem_vars_iff.mp hv_vars_x with h | h
        · exact _root_.B.Typing.typed_by_fv typ_x h
        · rcases B.Term.mem_vars_iff.mp hv with hy_fv | hy_bv
          · exact absurd (_root_.B.Typing.typed_by_fv typ_y hy_fv)
              (_root_.B.Typing.bv_notMem_context typ_x v h)
          · exact absurd rfl (hxy_bv_disj v h v hy_bv)
    have hbv_par : B.bv (x ∧ᴮ y) = B.bv x ++ B.bv y := by rw [B.bv]
    have hvars_x_sub : B.Term.vars x ⊆ B.Term.vars (x ∧ᴮ y) := fun v hv => by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h
    have hvars_y_sub : B.Term.vars y ⊆ B.Term.vars (x ∧ᴮ y) := fun v hv => by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inr h
    split
    · rename_i heq
      injection heq with hxe hσe
      subst hσe
      subst hxe
      mspec y_ih (E := E) (Λ := σ_x.types) (used := σ_x.env.usedVars)
        (decl := σ.env.declarations ++ Δx)
        typ_y (fun v hv => x_used_sub (vars_used_y v hv)) Λ_inv_y hy_bv_nodup
      rename_i out_y
      obtain ⟨y_enc, σy⟩ := out_y
      mrename_i prey
      mintro ∀σ_y
      mpure prey
      obtain ⟨⟨y_used_sub, y_Λ_sub, y_keys_sub, y_cov, y_fv_sub, y_preserves⟩,
        Δy, y_decl_eq, y_specb, y_enc_fv_sub⟩ := prey
      split
      · rename_i heq2
        injection heq2 with hye hσe2
        subst hσe2
        subst hye
        mspec Std.Do.Spec.pure
        mpure_intro
        refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, Δx ++ Δy, ?_, ?_, ?_⟩
        · exact fun v hv => y_used_sub (x_used_sub hv)
        · exact AList.subset_trans x_Λ_sub y_Λ_sub
        · exact y_keys_sub
        · intro v hv
          rw [B.fv, List.mem_append] at hv
          rcases hv with hv | hv
          · exact y_used_sub (x_cov v hv)
          · exact y_cov v hv
        · intro v hv
          rw [SMT.fv, List.mem_append] at hv
          rcases hv with hv | hv
          · rcases List.mem_union_iff.mp (x_fv_sub hv) with hk | hb
            · exact List.mem_union_iff.mpr (.inl (AList.mem_keys.mpr
                (AList.mem_of_subset y_Λ_sub (AList.mem_keys.mp hk))))
            · exact List.mem_union_iff.mpr (.inr (hvars_x_sub hb))
          · rcases List.mem_union_iff.mp (y_fv_sub hv) with hk | hb
            · exact List.mem_union_iff.mpr (.inl hk)
            · exact List.mem_union_iff.mpr (.inr (hvars_y_sub hb))
        · intro v hv hΛ hvars
          have hvx : v ∉ B.Term.vars x := fun h => hvars (hvars_x_sub h)
          have hvy : v ∉ B.Term.vars y := fun h => hvars (hvars_y_sub h)
          exact y_preserves v (x_used_sub hv) (x_preserves v hv hΛ hvx) hvy
        · rw [y_decl_eq, List.append_assoc]
        · intro b hb
          rw [specBodies_append, List.mem_append] at hb
          rcases hb with hb | hb
          · exact specBody_mono hvars_x_sub (declVars_append .. ▸ List.subset_append_left ..)
              (x_specb b hb)
          · exact specBody_mono hvars_y_sub (declVars_append .. ▸ List.subset_append_right ..)
              (y_specb b hb)
        · intro v hv
          rw [SMT.fv, List.mem_append] at hv
          rw [declVars_append]
          rcases hv with hv | hv
          · rcases List.mem_union_iff.mp (x_enc_fv_sub hv) with h | h
            · exact List.mem_union_iff.mpr (.inl (hvars_x_sub h))
            · exact List.mem_union_iff.mpr (.inr (List.mem_append_left _ h))
          · rcases List.mem_union_iff.mp (y_enc_fv_sub hv) with h | h
            · exact List.mem_union_iff.mpr (.inl (hvars_y_sub h))
            · exact List.mem_union_iff.mpr (.inr (List.mem_append_right _ h))
      · exact wp_bind_throw _ _ _ _
    · exact wp_bind_throw _ _ _ _
  | not x ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq, rfl⟩ := pre
    rw [encodeTerm]
    obtain ⟨rfl, typ_x⟩ := B.Typing.notE typ_t
    have hx_bv_nodup : (B.bv x).Nodup := by simpa [B.bv] using bv_nodup
    have vars_used_x : ∀ v ∈ x.vars, v ∈ used := fun v hv => vars_used v (by
      simpa [B.Term.vars, B.fv, B.bv] using hv)
    have Λ_inv_x : ∀ v ∈ x.vars, v ∈ σ.types → v ∈ E.context := fun v hv => Λ_inv v (by
      simpa [B.Term.vars, B.fv, B.bv] using hv)
    mspec ih (E := E) (Λ := σ.types) (decl := σ.env.declarations)
      typ_x vars_used_x Λ_inv_x hx_bv_nodup
    rename_i out_x
    obtain ⟨x_enc, σx⟩ := out_x
    mrename_i prex
    mintro ∀σ_x
    mpure prex
    obtain ⟨⟨x_used_sub, x_Λ_sub, x_keys_sub, x_cov, x_fv_sub, x_preserves⟩,
      Δx, x_decl_eq, x_specb, x_enc_fv_sub⟩ := prex
    have hvars_x_sub : B.Term.vars x ⊆ B.Term.vars (¬ᴮ x) := fun v hv => by
      simpa [B.Term.vars, B.fv, B.bv] using hv
    split
    · rename_i heq
      injection heq with hxe hσe
      subst hσe
      subst hxe
      mspec Std.Do.Spec.pure
      mpure_intro
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, Δx, x_decl_eq, ?_, ?_⟩
      · exact x_used_sub
      · exact x_Λ_sub
      · exact x_keys_sub
      · intro v hv; simp only [B.fv] at hv; exact x_cov v hv
      · intro v hv; simp only [SMT.fv] at hv; exact x_fv_sub hv
      · intro v hv hΛ hvars
        exact x_preserves v hv hΛ (fun h => hvars (hvars_x_sub h))
      · intro b hb
        exact specBody_mono hvars_x_sub (fun w hw => hw) (x_specb b hb)
      · intro v hv
        simp only [SMT.fv] at hv
        rcases List.mem_union_iff.mp (x_enc_fv_sub hv) with h | h
        · exact List.mem_union_iff.mpr (.inl (hvars_x_sub h))
        · exact List.mem_union_iff.mpr (.inr h)
    · exact wp_bind_throw _ _ _ _
  | pow S ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq, rfl⟩ := pre
    rw [encodeTerm]
    obtain ⟨β, rfl, typ_S⟩ := B.Typing.powE typ_t
    have hS_bv_nodup : (B.bv S).Nodup := by simpa [B.bv] using bv_nodup
    have vars_used_S : ∀ v ∈ S.vars, v ∈ used := fun v hv => vars_used v (by
      simpa [B.Term.vars, B.fv, B.bv] using hv)
    have Λ_inv_S : ∀ v ∈ S.vars, v ∈ σ.types → v ∈ E.context := fun v hv => Λ_inv v (by
      simpa [B.Term.vars, B.fv, B.bv] using hv)
    have hvars_S_sub : B.Term.vars S ⊆ B.Term.vars (𝒫ᴮ S) := fun v hv => by
      simpa [B.Term.vars, B.fv, B.bv] using hv
    mspec ih (E := E) (Λ := σ.types) (decl := σ.env.declarations)
      typ_S vars_used_S Λ_inv_S hS_bv_nodup
    rename_i out_S
    obtain ⟨S_enc, σS⟩ := out_S
    mrename_i preS
    mintro ∀σ_S
    mpure preS
    obtain ⟨⟨S_used_sub, S_Λ_sub, S_keys_sub, S_cov, S_fv_sub, S_preserves⟩,
      ΔS, S_decl_eq, S_specb, S_enc_fv_sub⟩ := preS
    split
    · rename_i α heq
      subst heq
      set ctx := σ_S.types with hctx
      mspec Std.Do.Spec.get_StateT
      mspec (Std.Do.Triple.and (SMT.freshVar α)
        (SMT.freshVar_spec (Γ := ctx) (τ := α)
          (n := σ_S.env.freshvarsc) (used := σ_S.env.usedVars))
        (SMT.freshVar_decls (τ := α) (decl := σ_S.env.declarations)))
      case post.success x =>
        mrename_i pre
        mintro ∀St₁
        mpure pre
        obtain ⟨⟨St₁_types_eq, x_fresh, St₁_fvc_eq, St₁_used_eq, x_not_used⟩, St₁_decl⟩ := pre
        mspec (Std.Do.Triple.and (SMT.freshVar (.fun α .bool))
          (SMT.freshVar_spec (Γ := ctx.insert x _) (τ := .fun α .bool)
            (n := St₁.env.freshvarsc) (used := St₁.env.usedVars))
          (SMT.freshVar_decls (τ := .fun α .bool) (decl := St₁.env.declarations)))
        case post.success ℰ =>
          mrename_i pre
          mintro ∀St₂
          mpure pre
          obtain ⟨⟨St₂_types_eq, ℰ_fresh, St₂_fvc_eq, St₂_used_eq, ℰ_not_used⟩,
            St₂_decl⟩ := pre
          simp [modify]
          mspec Std.Do.Spec.modifyGet_StateT
          mpure_intro
          refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ΔS, ?_, ?_, ?_⟩
          · intro v hv
            rw [St₂_used_eq, St₁_used_eq]
            exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (S_used_sub hv))
          · exact S_Λ_sub
          · intro v hv
            rw [St₂_used_eq, St₁_used_eq]
            exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (S_keys_sub hv))
          · intro v hv
            rw [B.fv] at hv
            rw [St₂_used_eq, St₁_used_eq]
            exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (S_cov v hv))
          · intro v hv
            simp only [SMT.fv, List.mem_removeAll_iff, List.mem_append,
              List.mem_cons, List.not_mem_nil, or_false] at hv
            obtain ⟨⟨hv1, hv_ne_x⟩, hv_ne_ℰ⟩ := hv
            rcases hv1 with (hvℰ | hvx) | hvS | hvx
            · exact absurd hvℰ hv_ne_ℰ
            · exact absurd hvx hv_ne_x
            · exact S_fv_sub hvS
            · exact absurd hvx hv_ne_x
          · intro v hv hΛ hvars
            exact S_preserves v hv hΛ (fun h => hvars (by
              simpa [B.Term.vars, B.fv, B.bv] using h))
          · rw [St₂_decl, St₁_decl, S_decl_eq]
          · intro b name hb
            exact specBody_mono hvars_S_sub (fun w hw => hw)
              (S_specb b (mem_specBodies_define_fun.mpr ⟨name, hb⟩))
          · intro v hv
            simp only [SMT.fv, List.mem_removeAll_iff, List.mem_append,
              List.mem_cons, List.not_mem_nil, or_false] at hv
            obtain ⟨⟨hv1, hv_ne_x⟩, hv_ne_ℰ⟩ := hv
            rcases hv1 with (hvℰ | hvx) | hvS | hvx
            · exact absurd hvℰ hv_ne_ℰ
            · exact absurd hvx hv_ne_x
            · rcases List.mem_union_iff.mp (S_enc_fv_sub hvS) with h | h
              · exact List.mem_union_iff.mpr (.inl (hvars_S_sub h))
              · exact List.mem_union_iff.mpr (.inr h)
            · exact absurd hvx hv_ne_x
    · rename_i α γ heq
      subst heq
      set ctx := σ_S.types with hctx
      mspec Std.Do.Spec.get_StateT
      mspec (Std.Do.Triple.and (SMT.freshVar α)
        (SMT.freshVar_spec (Γ := ctx) (τ := α)
          (n := σ_S.env.freshvarsc) (used := σ_S.env.usedVars))
        (SMT.freshVar_decls (τ := α) (decl := σ_S.env.declarations)))
      case post.success x =>
        mrename_i pre
        mintro ∀St₁
        mpure pre
        obtain ⟨⟨St₁_types_eq, x_fresh, St₁_fvc_eq, St₁_used_eq, x_not_used⟩, St₁_decl⟩ := pre
        mspec (Std.Do.Triple.and (SMT.freshVar γ)
          (SMT.freshVar_spec (Γ := ctx.insert x _) (τ := γ)
            (n := St₁.env.freshvarsc) (used := St₁.env.usedVars))
          (SMT.freshVar_decls (τ := γ) (decl := St₁.env.declarations)))
        case post.success y =>
          mrename_i pre
          mintro ∀St₂
          mpure pre
          obtain ⟨⟨St₂_types_eq, y_fresh, St₂_fvc_eq, St₂_used_eq, y_not_used⟩,
            St₂_decl⟩ := pre
          mspec (Std.Do.Triple.and (SMT.freshVar (α.fun γ.option))
            (SMT.freshVar_spec (Γ := (ctx.insert x _).insert y _) (τ := α.fun γ.option)
              (n := St₂.env.freshvarsc) (used := St₂.env.usedVars))
            (SMT.freshVar_decls (τ := α.fun γ.option) (decl := St₂.env.declarations)))
          case post.success f =>
            mrename_i pre
            mintro ∀St₃
            mpure pre
            obtain ⟨⟨St₃_types_eq, f_fresh, St₃_fvc_eq, St₃_used_eq, f_not_used⟩,
              St₃_decl⟩ := pre
            simp [modify]
            mspec Std.Do.Spec.modifyGet_StateT
            mpure_intro
            refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ΔS, ?_, ?_, ?_⟩
            · intro v hv
              rw [St₃_used_eq, St₂_used_eq, St₁_used_eq]
              exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ (S_used_sub hv)))
            · exact S_Λ_sub
            · intro v hv
              rw [St₃_used_eq, St₂_used_eq, St₁_used_eq]
              exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ (S_keys_sub hv)))
            · intro v hv
              rw [B.fv] at hv
              rw [St₃_used_eq, St₂_used_eq, St₁_used_eq]
              exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ (S_cov v hv)))
            · intro v hv
              simp only [SMT.fv, List.mem_removeAll_iff, List.mem_append,
                List.mem_cons, List.not_mem_nil, or_false] at hv
              obtain ⟨⟨hv1, hv_ne_xy⟩, hv_ne_f⟩ := hv
              rcases hv1 with ((hvf | hvx) | hvy) | (hvS | hvx) | hvy
              · exact absurd hvf hv_ne_f
              · exact absurd (Or.inl hvx) hv_ne_xy
              · exact absurd (Or.inr hvy) hv_ne_xy
              · exact S_fv_sub hvS
              · exact absurd (Or.inl hvx) hv_ne_xy
              · exact absurd (Or.inr hvy) hv_ne_xy
            · intro v hv hΛ hvars
              exact S_preserves v hv hΛ (fun h => hvars (by
                simpa [B.Term.vars, B.fv, B.bv] using h))
            · rw [St₃_decl, St₂_decl, St₁_decl, S_decl_eq]
            · intro b name hb
              exact specBody_mono hvars_S_sub (fun w hw => hw)
                (S_specb b (mem_specBodies_define_fun.mpr ⟨name, hb⟩))
            · intro v hv
              simp only [SMT.fv, List.mem_removeAll_iff, List.mem_append,
                List.mem_cons, List.not_mem_nil, or_false] at hv
              obtain ⟨⟨hv1, hv_ne_xy⟩, hv_ne_f⟩ := hv
              rcases hv1 with ((hvf | hvx) | hvy) | (hvS | hvx) | hvy
              · exact absurd hvf hv_ne_f
              · exact absurd (Or.inl hvx) hv_ne_xy
              · exact absurd (Or.inr hvy) hv_ne_xy
              · rcases List.mem_union_iff.mp (S_enc_fv_sub hvS) with h | h
                · exact List.mem_union_iff.mpr (.inl (hvars_S_sub h))
                · exact List.mem_union_iff.mpr (.inr h)
              · exact absurd (Or.inl hvx) hv_ne_xy
              · exact absurd (Or.inr hvy) hv_ne_xy
    · mvcgen
  | cprod A C A_ih C_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq, rfl⟩ := pre
    rw [encodeTerm]
    obtain ⟨αA, βC, rfl, typ_A, typ_C⟩ := B.Typing.cprodE typ_t
    have hA_bv_nodup : (B.bv A).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.1
    have hC_bv_nodup : (B.bv C).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.2.1
    have hAC_bv_disj : ∀ a ∈ B.bv A, ∀ b ∈ B.bv C, a ≠ b := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.2.2
    have vars_used_A : ∀ v ∈ A.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h)
    have vars_used_C : ∀ v ∈ C.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inr h)
    have Λ_inv_A : ∀ v ∈ A.vars, v ∈ σ.types → v ∈ E.context := fun v hv => Λ_inv v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h)
    have hvars_A_sub : B.Term.vars A ⊆ B.Term.vars (A ⨯ᴮ C) := fun v hv => by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h
    have hvars_C_sub : B.Term.vars C ⊆ B.Term.vars (A ⨯ᴮ C) := fun v hv => by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inr h
    mspec A_ih (E := E) (Λ := σ.types) (decl := σ.env.declarations)
      typ_A vars_used_A Λ_inv_A hA_bv_nodup
    rename_i out_A
    obtain ⟨A_enc, σA⟩ := out_A
    mrename_i preA
    mintro ∀σ_A
    mpure preA
    obtain ⟨⟨A_used_sub, A_Λ_sub, A_keys_sub, A_cov, A_fv_sub, A_preserves⟩,
      ΔA, A_decl_eq, A_specb, A_enc_fv_sub⟩ := preA
    have Λ_inv_C : ∀ v ∈ C.vars, v ∈ σ_A.types → v ∈ E.context := fun v hv hΛ => by
      have hv_par : v ∈ (A ⨯ᴮ C).vars := hvars_C_sub hv
      by_cases hv_St : v ∈ σ.types
      · exact Λ_inv v hv_par hv_St
      · have hv_vars_A : v ∈ B.Term.vars A := by
          by_contra h_neg
          exact absurd hΛ (A_preserves v (vars_used v hv_par) hv_St h_neg)
        rcases B.Term.mem_vars_iff.mp hv_vars_A with h | h
        · exact _root_.B.Typing.typed_by_fv typ_A h
        · rcases B.Term.mem_vars_iff.mp hv with hC_fv | hC_bv
          · exact absurd (_root_.B.Typing.typed_by_fv typ_C hC_fv)
              (_root_.B.Typing.bv_notMem_context typ_A v h)
          · exact absurd rfl (hAC_bv_disj v h v hC_bv)
    split
    · rename_i heq
      injection heq with hAe hσe
      subst hσe
      subst hAe
      mspec C_ih (E := E) (Λ := σ_A.types) (used := σ_A.env.usedVars)
        (decl := σ.env.declarations ++ ΔA)
        typ_C (fun v hv => A_used_sub (vars_used_C v hv)) Λ_inv_C hC_bv_nodup
      rename_i out_C
      obtain ⟨C_enc, σC⟩ := out_C
      mrename_i preC
      mintro ∀σ_C
      mpure preC
      obtain ⟨⟨C_used_sub, C_Λ_sub, C_keys_sub, C_cov, C_fv_sub, C_preserves⟩,
        ΔC, C_decl_eq, C_specb, C_enc_fv_sub⟩ := preC
      split
      · rename_i heq2
        injection heq2 with hCe hσe2
        subst hσe2
        subst hCe
        set ctx := σ_C.types with hctx
        mspec (Std.Do.Triple.and (SMT.freshVar _)
          (SMT.freshVar_spec (Γ := ctx) (n := σ_C.env.freshvarsc)
            (used := σ_C.env.usedVars))
          (SMT.freshVar_decls (decl := σ_C.env.declarations)))
        case post.success p =>
          mrename_i pre
          mintro ∀St₁
          mpure pre
          obtain ⟨⟨St₁_types_eq, p_fresh, St₁_fvc_eq, St₁_used_eq, p_not_used⟩,
            St₁_decl⟩ := pre
          mspec (Std.Do.Triple.and (SMT.freshVar _)
            (SMT.freshVar_spec (Γ := ctx.insert p _) (n := St₁.env.freshvarsc)
              (used := St₁.env.usedVars))
            (SMT.freshVar_decls (decl := St₁.env.declarations)))
          case post.success a =>
            mrename_i pre
            mintro ∀St₂
            mpure pre
            obtain ⟨⟨St₂_types_eq, a_fresh, St₂_fvc_eq, St₂_used_eq, a_not_used⟩,
              St₂_decl⟩ := pre
            mspec (Std.Do.Triple.and (SMT.freshVar _)
              (SMT.freshVar_spec (Γ := (ctx.insert p _).insert a _)
                (n := St₂.env.freshvarsc) (used := St₂.env.usedVars))
              (SMT.freshVar_decls (decl := St₂.env.declarations)))
            case post.success b =>
              mrename_i pre
              mintro ∀St₃
              mpure pre
              obtain ⟨⟨St₃_types_eq, b_fresh, St₃_fvc_eq, St₃_used_eq, b_not_used⟩,
                St₃_decl⟩ := pre
              mspec (Std.Do.Triple.and (SMT.eraseFromContext p)
                (SMT.eraseFromContext_spec (v := p) (Γ := St₃.types)
                  (n := St₃.env.freshvarsc) (used := St₃.env.usedVars))
                (SMT.eraseFromContext_decls (v := p) (decl := St₃.env.declarations)))
              mrename_i preEp
              mintro ∀StEp
              mpure preEp
              obtain ⟨⟨StEp_types_eq, StEp_fvc, StEp_used_eq⟩, StEp_decl⟩ := preEp
              mspec (Std.Do.Triple.and (SMT.eraseFromContext a)
                (SMT.eraseFromContext_spec (v := a) (Γ := StEp.types)
                  (n := StEp.env.freshvarsc) (used := StEp.env.usedVars))
                (SMT.eraseFromContext_decls (v := a) (decl := StEp.env.declarations)))
              mrename_i preEa
              mintro ∀StEa
              mpure preEa
              obtain ⟨⟨StEa_types_eq, StEa_fvc, StEa_used_eq⟩, StEa_decl⟩ := preEa
              mspec (Std.Do.Triple.and (SMT.eraseFromContext b)
                (SMT.eraseFromContext_spec (v := b) (Γ := StEa.types)
                  (n := StEa.env.freshvarsc) (used := StEa.env.usedVars))
                (SMT.eraseFromContext_decls (v := b) (decl := StEa.env.declarations)))
              mrename_i preEb
              mintro ∀StEb
              mpure preEb
              obtain ⟨⟨StEb_types_eq, StEb_fvc, StEb_used_eq⟩, StEb_decl⟩ := preEb
              have hσ_sub_ctx : σ.types ⊆ ctx := AList.subset_trans A_Λ_sub C_Λ_sub
              have p_notσ : p ∉ σ.types := fun h => p_fresh (AList.mem_of_subset hσ_sub_ctx h)
              have a_notσ : a ∉ σ.types := fun h =>
                a_fresh ((AList.mem_insert _).mpr (Or.inr (AList.mem_of_subset hσ_sub_ctx h)))
              have b_notσ : b ∉ σ.types := fun h =>
                b_fresh ((AList.mem_insert _).mpr (Or.inr
                  ((AList.mem_insert _).mpr (Or.inr (AList.mem_of_subset hσ_sub_ctx h)))))
              have hv_ne : ∀ {v : SMT.𝒱}, v ≠ p → v ≠ a → v ≠ b → v ∈ ctx →
                  v ∈ AList.keys StEb.types := by
                intro v hvp hva hvb hvctx
                rw [← AList.mem_keys, StEb_types_eq]
                refine AList.mem_erase.mpr ⟨hvb, ?_⟩
                rw [StEa_types_eq]
                refine AList.mem_erase.mpr ⟨hva, ?_⟩
                rw [StEp_types_eq]
                refine AList.mem_erase.mpr ⟨hvp, ?_⟩
                rw [St₃_types_eq]
                exact (AList.mem_insert _).mpr (Or.inr ((AList.mem_insert _).mpr
                  (Or.inr ((AList.mem_insert _).mpr (Or.inr hvctx)))))
              mspec Std.Do.Spec.pure
              mpure_intro
              refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ΔA ++ ΔC, ?_, ?_, ?_⟩
              · intro v hv
                rw [StEb_used_eq, StEa_used_eq, StEp_used_eq,
                  St₃_used_eq, St₂_used_eq, St₁_used_eq]
                exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                  (List.mem_cons_of_mem _ (C_used_sub (A_used_sub hv))))
              · rw [StEb_types_eq, StEa_types_eq, StEp_types_eq]
                have base : σ.types ⊆ St₃.types := by
                  rw [St₃_types_eq]
                  exact AList.subset_trans (AList.subset_trans A_Λ_sub C_Λ_sub)
                    (AList.subset_trans (SMT.TypeContext.entries_subset_insert_of_notMem p_fresh)
                      (AList.subset_trans
                        (SMT.TypeContext.entries_subset_insert_of_notMem a_fresh)
                        (SMT.TypeContext.entries_subset_insert_of_notMem b_fresh)))
                exact SMT.TypeContext.entries_subset_erase_of_notMem
                  (SMT.TypeContext.entries_subset_erase_of_notMem
                    (SMT.TypeContext.entries_subset_erase_of_notMem base p_notσ) a_notσ) b_notσ
              · intro v hv
                rw [StEb_used_eq, StEa_used_eq, StEp_used_eq,
                  St₃_used_eq, St₂_used_eq, St₁_used_eq]
                have hv0 : v ∈ AList.keys St₃.types :=
                  SMT.TypeContext.keys_erase_subset (StEp_types_eq ▸
                    SMT.TypeContext.keys_erase_subset (StEa_types_eq ▸
                      SMT.TypeContext.keys_erase_subset (StEb_types_eq ▸ hv)))
                have hv' : v ∈ St₃.types := AList.mem_keys.mpr hv0
                rw [St₃_types_eq] at hv'
                iterate 3 rw [AList.mem_insert] at hv'
                rcases hv' with rfl | rfl | rfl | hv'
                · exact List.mem_cons_self
                · exact List.mem_cons_of_mem _ List.mem_cons_self
                · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
                · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                    (List.mem_cons_of_mem _ (C_keys_sub (AList.mem_keys.mp hv'))))
              · intro v hv
                rw [B.fv, List.mem_append] at hv
                rw [StEb_used_eq, StEa_used_eq, StEp_used_eq,
                  St₃_used_eq, St₂_used_eq, St₁_used_eq]
                rcases hv with hv | hv
                · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                    (List.mem_cons_of_mem _ (C_used_sub (A_cov v hv))))
                · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                    (List.mem_cons_of_mem _ (C_cov v hv)))
              · intro v hv
                simp only [SMT.fv, List.mem_removeAll_iff, List.mem_append,
                  List.mem_cons, List.not_mem_nil, or_false] at hv
                obtain ⟨⟨hv1, hv_ne_ab⟩, hv_ne_p⟩ := hv
                have hv_ne_a : v ≠ a := fun h => hv_ne_ab (Or.inl h)
                have hv_ne_b : v ≠ b := fun h => hv_ne_ab (Or.inr h)
                rcases hv1 with (hvA | hva) | (hvC | hvb) | (hvp | hva | hvb)
                · rcases List.mem_union_iff.mp (A_fv_sub hvA) with hk | hbv
                  · exact List.mem_union_iff.mpr (.inl (hv_ne hv_ne_p hv_ne_a hv_ne_b
                      (AList.mem_of_subset C_Λ_sub (AList.mem_keys.mp hk))))
                  · exact List.mem_union_iff.mpr (.inr (hvars_A_sub hbv))
                · exact absurd (Or.inl hva) hv_ne_ab
                · rcases List.mem_union_iff.mp (C_fv_sub hvC) with hk | hbv
                  · exact List.mem_union_iff.mpr (.inl (hv_ne hv_ne_p hv_ne_a hv_ne_b
                      (AList.mem_keys.mp hk)))
                  · exact List.mem_union_iff.mpr (.inr (hvars_C_sub hbv))
                · exact absurd (Or.inr hvb) hv_ne_ab
                · exact absurd hvp hv_ne_p
                · exact absurd (Or.inl hva) hv_ne_ab
                · exact absurd (Or.inr hvb) hv_ne_ab
              · intro v hv hΛ hvars
                have hvA : v ∉ B.Term.vars A := fun h => hvars (hvars_A_sub h)
                have hvC : v ∉ B.Term.vars C := fun h => hvars (hvars_C_sub h)
                have hv_not_ctx : v ∉ ctx :=
                  C_preserves v (A_used_sub hv) (A_preserves v hv hΛ hvA) hvC
                rw [StEb_types_eq]
                apply SMT.TypeContext.notMem_erase
                rw [StEa_types_eq]
                apply SMT.TypeContext.notMem_erase
                rw [StEp_types_eq]
                apply SMT.TypeContext.notMem_erase
                rw [St₃_types_eq]
                intro hv_in
                iterate 3 rw [AList.mem_insert] at hv_in
                rcases hv_in with rfl | rfl | rfl | hv_in
                · exact b_not_used (by
                    rw [St₂_used_eq, St₁_used_eq]
                    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                      (C_used_sub (A_used_sub hv))))
                · exact a_not_used (by
                    rw [St₁_used_eq]
                    exact List.mem_cons_of_mem _ (C_used_sub (A_used_sub hv)))
                · exact p_not_used (C_used_sub (A_used_sub hv))
                · exact hv_not_ctx hv_in
              · rw [StEb_decl, StEa_decl, StEp_decl,
                  St₃_decl, St₂_decl, St₁_decl, C_decl_eq, List.append_assoc]
              · intro b hb
                rw [specBodies_append, List.mem_append] at hb
                rcases hb with hb | hb
                · exact specBody_mono hvars_A_sub
                    (declVars_append .. ▸ List.subset_append_left ..) (A_specb b hb)
                · exact specBody_mono hvars_C_sub
                    (declVars_append .. ▸ List.subset_append_right ..) (C_specb b hb)
              · intro v hv
                simp only [SMT.fv, List.mem_removeAll_iff, List.mem_append,
                  List.mem_cons, List.not_mem_nil, or_false] at hv
                obtain ⟨⟨hv1, hv_ne_ab⟩, hv_ne_p⟩ := hv
                rw [declVars_append]
                rcases hv1 with (hvA | hva) | (hvC | hvb) | (hvp | hva | hvb)
                · rcases List.mem_union_iff.mp (A_enc_fv_sub hvA) with h | h
                  · exact List.mem_union_iff.mpr (.inl (hvars_A_sub h))
                  · exact List.mem_union_iff.mpr (.inr (List.mem_append_left _ h))
                · exact absurd (Or.inl hva) hv_ne_ab
                · rcases List.mem_union_iff.mp (C_enc_fv_sub hvC) with h | h
                  · exact List.mem_union_iff.mpr (.inl (hvars_C_sub h))
                  · exact List.mem_union_iff.mpr (.inr (List.mem_append_right _ h))
                · exact absurd (Or.inr hvb) hv_ne_ab
                · exact absurd hvp hv_ne_p
                · exact absurd (Or.inl hva) hv_ne_ab
                · exact absurd (Or.inr hvb) hv_ne_ab
      · exact wp_bind_throw _ _ _ _
    · exact wp_bind_throw _ _ _ _
  | mem x S x_ih S_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq, rfl⟩ := pre
    rw [encodeTerm]
    obtain ⟨rfl, αx, typ_x, typ_S⟩ := B.Typing.memE typ_t
    have hx_bv_nodup : (B.bv x).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.1
    have hS_bv_nodup : (B.bv S).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.2.1
    have hxS_bv_disj : ∀ a ∈ B.bv x, ∀ b ∈ B.bv S, a ≠ b := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.2.2
    have vars_used_x : ∀ v ∈ x.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h)
    have vars_used_S : ∀ v ∈ S.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inr h)
    have Λ_inv_x : ∀ v ∈ x.vars, v ∈ σ.types → v ∈ E.context := fun v hv => Λ_inv v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h)
    have hbv_par : B.bv (x ∈ᴮ S) = B.bv x ++ B.bv S := by rw [B.bv]
    have hvars_x_sub : B.Term.vars x ⊆ B.Term.vars (x ∈ᴮ S) := fun v hv => by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h
    have hvars_S_sub : B.Term.vars S ⊆ B.Term.vars (x ∈ᴮ S) := fun v hv => by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inr h
    mspec x_ih (E := E) (Λ := σ.types) (decl := σ.env.declarations)
      typ_x vars_used_x Λ_inv_x hx_bv_nodup
    clear x_ih
    rename_i out_x
    obtain ⟨x_enc, σx⟩ := out_x
    mrename_i pre
    mintro ∀σ_x
    mpure pre
    obtain ⟨⟨x_used_sub, x_Λ_sub, x_keys_sub, x_cov, x_fv_sub, x_preserves⟩,
      Δx, x_decl_eq, x_specb, x_enc_fv_sub⟩ := pre
    have Λ_inv_S : ∀ v ∈ S.vars, v ∈ σ_x.types → v ∈ E.context := fun v hv hΛ => by
      have hv_par : v ∈ (x ∈ᴮ S).vars := hvars_S_sub hv
      by_cases hv_St : v ∈ σ.types
      · exact Λ_inv v hv_par hv_St
      · have hv_vars_x : v ∈ B.Term.vars x := by
          by_contra h_neg
          exact absurd hΛ (x_preserves v (vars_used v hv_par) hv_St h_neg)
        rcases B.Term.mem_vars_iff.mp hv_vars_x with h | h
        · exact _root_.B.Typing.typed_by_fv typ_x h
        · rcases B.Term.mem_vars_iff.mp hv with hS_fv | hS_bv
          · exact absurd (_root_.B.Typing.typed_by_fv typ_S hS_fv)
              (_root_.B.Typing.bv_notMem_context typ_x v h)
          · exact absurd rfl (hxS_bv_disj v h v hS_bv)
    mspec S_ih (E := E) (Λ := σ_x.types) (used := σ_x.env.usedVars)
      (decl := σ.env.declarations ++ Δx)
      typ_S (fun v hv => x_used_sub (vars_used_S v hv)) Λ_inv_S hS_bv_nodup
    clear S_ih
    rename_i out_S
    obtain ⟨S_enc, σS⟩ := out_S
    mrename_i pre
    mintro ∀σ_S
    mpure pre
    obtain ⟨⟨S_used_sub, S_Λ_sub, S_keys_sub, S_cov, S_fv_sub, S_preserves⟩,
      ΔS, S_decl_eq, S_specb, S_enc_fv_sub⟩ := pre
    mspec (Std.Do.Triple.and
      (castMembership (x_enc, σx) (S_enc, σS))
      (castMembership_state x_enc S_enc σx σS (Λ := σ_S.types) (n := σ_S.env.freshvarsc)
        (used := σ_S.env.usedVars) (X := B.Term.vars (x ∈ᴮ S)))
      (castMembership_decl x_enc S_enc σx σS (Λ := σ_S.types) (n := σ_S.env.freshvarsc)
        (used := σ_S.env.usedVars) (decl := σ.env.declarations ++ Δx ++ ΔS)))
    case pre =>
      mpure_intro
      refine ⟨⟨rfl, rfl, S_keys_sub, rfl, ?_, ?_⟩, rfl, rfl, S_keys_sub, rfl, S_decl_eq⟩
      · intro v hv
        rcases List.mem_union_iff.mp (x_fv_sub hv) with hk | hb
        · exact List.mem_union_iff.mpr (.inl (AList.mem_keys.mpr
            (AList.mem_of_subset S_Λ_sub (AList.mem_keys.mp hk))))
        · exact List.mem_union_iff.mpr (.inr (hvars_x_sub hb))
      · intro v hv
        rcases List.mem_union_iff.mp (S_fv_sub hv) with hk | hb
        · exact List.mem_union_iff.mpr (.inl hk)
        · exact List.mem_union_iff.mpr (.inr (hvars_S_sub hb))
    case post.success =>
      rename_i out_cm
      obtain ⟨cm_enc, σcm⟩ := out_cm
      mrename_i pre
      mintro ∀σ'
      mpure pre
      obtain ⟨⟨h_le, h_Λ_sub, h_used_sub, h_keys_sub, h_fv_sub, h_preserves⟩,
        Dcm, cm_decl_eq, cm_spec_nil, cm_fv_decl_sub⟩ := pre
      mpure_intro
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, Δx ++ ΔS ++ Dcm, ?_, ?_, ?_⟩
      · exact fun v hv => h_used_sub (S_used_sub (x_used_sub hv))
      · exact AList.subset_trans (AList.subset_trans x_Λ_sub S_Λ_sub) h_Λ_sub
      · exact h_keys_sub
      · intro v hv
        rw [B.fv, List.mem_append] at hv
        rcases hv with hv | hv
        · exact h_used_sub (S_used_sub (x_cov v hv))
        · exact h_used_sub (S_cov v hv)
      · exact h_fv_sub
      · intro v hv hΛ hvars
        have hvx : v ∉ B.Term.vars x := fun h => hvars (hvars_x_sub h)
        have hvS : v ∉ B.Term.vars S := fun h => hvars (hvars_S_sub h)
        exact h_preserves v (S_used_sub (x_used_sub hv))
          (S_preserves v (x_used_sub hv) (x_preserves v hv hΛ hvx) hvS)
      · rw [cm_decl_eq]; simp only [List.append_assoc]
      · intro b hb
        rw [specBodies_append, List.mem_append] at hb
        rcases hb with hb | hb
        · rw [specBodies_append, List.mem_append] at hb
          rcases hb with hb | hb
          · exact specBody_mono hvars_x_sub
              (by rw [declVars_append, declVars_append]
                  exact List.Subset.trans (List.subset_append_left ..)
                    (List.subset_append_left ..))
              (x_specb b hb)
          · exact specBody_mono hvars_S_sub
              (by rw [declVars_append, declVars_append]
                  exact List.Subset.trans (List.subset_append_right ..)
                    (List.subset_append_left ..))
              (S_specb b hb)
        · rw [cm_spec_nil] at hb
          simp at hb
      · intro v hv
        have hv' := cm_fv_decl_sub hv
        rw [declVars_append, declVars_append]
        rcases List.mem_union_iff.mp hv' with h | h
        · rcases List.mem_union_iff.mp h with h | h
          · rcases List.mem_union_iff.mp (x_enc_fv_sub h) with h | h
            · exact List.mem_union_iff.mpr (.inl (hvars_x_sub h))
            · exact List.mem_union_iff.mpr (.inr (List.mem_append_left _
                (List.mem_append_left _ h)))
          · rcases List.mem_union_iff.mp (S_enc_fv_sub h) with h | h
            · exact List.mem_union_iff.mpr (.inl (hvars_S_sub h))
            · exact List.mem_union_iff.mpr (.inr (List.mem_append_left _
                (List.mem_append_right _ h)))
        · exact List.mem_union_iff.mpr (.inr (List.mem_append_right _ h))
  | eq x y x_ih y_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq, rfl⟩ := pre
    rw [encodeTerm]
    obtain ⟨rfl, αx, typ_x, typ_y⟩ := B.Typing.eqE typ_t
    have hx_bv_nodup : (B.bv x).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.1
    have hy_bv_nodup : (B.bv y).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.2.1
    have hxy_bv_disj : ∀ a ∈ B.bv x, ∀ b ∈ B.bv y, a ≠ b := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.2.2
    have vars_used_x : ∀ v ∈ x.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h)
    have vars_used_y : ∀ v ∈ y.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inr h)
    have Λ_inv_x : ∀ v ∈ x.vars, v ∈ σ.types → v ∈ E.context := fun v hv => Λ_inv v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h)
    have hbv_par : B.bv (x =ᴮ y) = B.bv x ++ B.bv y := by rw [B.bv]
    have hvars_x_sub : B.Term.vars x ⊆ B.Term.vars (x =ᴮ y) := fun v hv => by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h
    have hvars_y_sub : B.Term.vars y ⊆ B.Term.vars (x =ᴮ y) := fun v hv => by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inr h
    mspec x_ih (E := E) (Λ := σ.types) (decl := σ.env.declarations)
      typ_x vars_used_x Λ_inv_x hx_bv_nodup
    clear x_ih
    rename_i out_x
    obtain ⟨x_enc, σx⟩ := out_x
    mrename_i pre
    mintro ∀σ_x
    mpure pre
    obtain ⟨⟨x_used_sub, x_Λ_sub, x_keys_sub, x_cov, x_fv_sub, x_preserves⟩,
      Δx, x_decl_eq, x_specb, x_enc_fv_sub⟩ := pre
    have Λ_inv_y : ∀ v ∈ y.vars, v ∈ σ_x.types → v ∈ E.context := fun v hv hΛ => by
      have hv_par : v ∈ (x =ᴮ y).vars := hvars_y_sub hv
      by_cases hv_St : v ∈ σ.types
      · exact Λ_inv v hv_par hv_St
      · have hv_vars_x : v ∈ B.Term.vars x := by
          by_contra h_neg
          exact absurd hΛ (x_preserves v (vars_used v hv_par) hv_St h_neg)
        rcases B.Term.mem_vars_iff.mp hv_vars_x with h | h
        · exact _root_.B.Typing.typed_by_fv typ_x h
        · rcases B.Term.mem_vars_iff.mp hv with hy_fv | hy_bv
          · exact absurd (_root_.B.Typing.typed_by_fv typ_y hy_fv)
              (_root_.B.Typing.bv_notMem_context typ_x v h)
          · exact absurd rfl (hxy_bv_disj v h v hy_bv)
    mspec y_ih (E := E) (Λ := σ_x.types) (used := σ_x.env.usedVars)
      (decl := σ.env.declarations ++ Δx)
      typ_y (fun v hv => x_used_sub (vars_used_y v hv)) Λ_inv_y hy_bv_nodup
    clear y_ih
    rename_i out_y
    obtain ⟨y_enc, σy⟩ := out_y
    mrename_i pre
    mintro ∀σ_y
    mpure pre
    obtain ⟨⟨y_used_sub, y_Λ_sub, y_keys_sub, y_cov, y_fv_sub, y_preserves⟩,
      Δy, y_decl_eq, y_specb, y_enc_fv_sub⟩ := pre
    mspec (Std.Do.Triple.and
      (castEq (x_enc, σx) (y_enc, σy))
      (castEq_state x_enc y_enc σx σy (Λ := σ_y.types) (n := σ_y.env.freshvarsc)
        (used := σ_y.env.usedVars) (X := B.Term.vars (x =ᴮ y)))
      (castEq_decl x_enc y_enc σx σy (Λ := σ_y.types) (n := σ_y.env.freshvarsc)
        (used := σ_y.env.usedVars) (decl := σ.env.declarations ++ Δx ++ Δy)))
    case pre =>
      mpure_intro
      refine ⟨⟨rfl, rfl, y_keys_sub, rfl, ?_, ?_⟩, rfl, rfl, y_keys_sub, rfl, y_decl_eq⟩
      · intro v hv
        rcases List.mem_union_iff.mp (x_fv_sub hv) with hk | hb
        · exact List.mem_union_iff.mpr (.inl (AList.mem_keys.mpr
            (AList.mem_of_subset y_Λ_sub (AList.mem_keys.mp hk))))
        · exact List.mem_union_iff.mpr (.inr (hvars_x_sub hb))
      · intro v hv
        rcases List.mem_union_iff.mp (y_fv_sub hv) with hk | hb
        · exact List.mem_union_iff.mpr (.inl hk)
        · exact List.mem_union_iff.mpr (.inr (hvars_y_sub hb))
    case post.success =>
      rename_i out_ce
      obtain ⟨ce_enc, σce⟩ := out_ce
      mrename_i pre
      mintro ∀σ'
      mpure pre
      obtain ⟨⟨h_le, h_Λ_sub, h_used_sub, h_keys_sub, h_fv_sub, h_preserves⟩,
        Dce, ce_decl_eq, ce_spec_nil, ce_fv_decl_sub⟩ := pre
      mpure_intro
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, Δx ++ Δy ++ Dce, ?_, ?_, ?_⟩
      · exact fun v hv => h_used_sub (y_used_sub (x_used_sub hv))
      · exact AList.subset_trans (AList.subset_trans x_Λ_sub y_Λ_sub) h_Λ_sub
      · exact h_keys_sub
      · intro v hv
        rw [B.fv, List.mem_append] at hv
        rcases hv with hv | hv
        · exact h_used_sub (y_used_sub (x_cov v hv))
        · exact h_used_sub (y_cov v hv)
      · exact h_fv_sub
      · intro v hv hΛ hvars
        have hvx : v ∉ B.Term.vars x := fun h => hvars (hvars_x_sub h)
        have hvy : v ∉ B.Term.vars y := fun h => hvars (hvars_y_sub h)
        exact h_preserves v (y_used_sub (x_used_sub hv))
          (y_preserves v (x_used_sub hv) (x_preserves v hv hΛ hvx) hvy)
      · rw [ce_decl_eq]; simp only [List.append_assoc]
      · intro b hb
        rw [specBodies_append, List.mem_append] at hb
        rcases hb with hb | hb
        · rw [specBodies_append, List.mem_append] at hb
          rcases hb with hb | hb
          · exact specBody_mono hvars_x_sub
              (by rw [declVars_append, declVars_append]
                  exact List.Subset.trans (List.subset_append_left ..)
                    (List.subset_append_left ..))
              (x_specb b hb)
          · exact specBody_mono hvars_y_sub
              (by rw [declVars_append, declVars_append]
                  exact List.Subset.trans (List.subset_append_right ..)
                    (List.subset_append_left ..))
              (y_specb b hb)
        · rw [ce_spec_nil] at hb
          simp at hb
      · intro v hv
        have hv' := ce_fv_decl_sub hv
        rw [declVars_append, declVars_append]
        rcases List.mem_union_iff.mp hv' with h | h
        · rcases List.mem_union_iff.mp h with h | h
          · rcases List.mem_union_iff.mp (x_enc_fv_sub h) with h | h
            · exact List.mem_union_iff.mpr (.inl (hvars_x_sub h))
            · exact List.mem_union_iff.mpr (.inr (List.mem_append_left _
                (List.mem_append_left _ h)))
          · rcases List.mem_union_iff.mp (y_enc_fv_sub h) with h | h
            · exact List.mem_union_iff.mpr (.inl (hvars_y_sub h))
            · exact List.mem_union_iff.mpr (.inr (List.mem_append_left _
                (List.mem_append_right _ h)))
        · exact List.mem_union_iff.mpr (.inr (List.mem_append_right _ h))
  | union A C A_ih C_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq, rfl⟩ := pre
    rw [encodeTerm]
    obtain ⟨αA, rfl, typ_A, typ_C⟩ := B.Typing.unionE typ_t
    have hA_bv_nodup : (B.bv A).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.1
    have hC_bv_nodup : (B.bv C).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.2.1
    have hAC_bv_disj : ∀ a ∈ B.bv A, ∀ b ∈ B.bv C, a ≠ b := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.2.2
    have vars_used_A : ∀ v ∈ A.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h)
    have vars_used_C : ∀ v ∈ C.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inr h)
    have Λ_inv_A : ∀ v ∈ A.vars, v ∈ σ.types → v ∈ E.context := fun v hv => Λ_inv v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h)
    have hbv_par : B.bv (A ∪ᴮ C) = B.bv A ++ B.bv C := by rw [B.bv]
    have hvars_A_sub : B.Term.vars A ⊆ B.Term.vars (A ∪ᴮ C) := fun v hv => by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h
    have hvars_C_sub : B.Term.vars C ⊆ B.Term.vars (A ∪ᴮ C) := fun v hv => by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inr h
    mspec A_ih (E := E) (Λ := σ.types) (decl := σ.env.declarations)
      typ_A vars_used_A Λ_inv_A hA_bv_nodup
    clear A_ih
    rename_i out_A
    obtain ⟨A_enc, σA⟩ := out_A
    mrename_i pre
    mintro ∀σ_A
    mpure pre
    obtain ⟨⟨A_used_sub, A_Λ_sub, A_keys_sub, A_cov, A_fv_sub, A_preserves⟩,
      ΔA, A_decl_eq, A_specb, A_enc_fv_sub⟩ := pre
    have Λ_inv_C : ∀ v ∈ C.vars, v ∈ σ_A.types → v ∈ E.context := fun v hv hΛ => by
      have hv_par : v ∈ (A ∪ᴮ C).vars := hvars_C_sub hv
      by_cases hv_St : v ∈ σ.types
      · exact Λ_inv v hv_par hv_St
      · have hv_vars_A : v ∈ B.Term.vars A := by
          by_contra h_neg
          exact absurd hΛ (A_preserves v (vars_used v hv_par) hv_St h_neg)
        rcases B.Term.mem_vars_iff.mp hv_vars_A with h | h
        · exact _root_.B.Typing.typed_by_fv typ_A h
        · rcases B.Term.mem_vars_iff.mp hv with hC_fv | hC_bv
          · exact absurd (_root_.B.Typing.typed_by_fv typ_C hC_fv)
              (_root_.B.Typing.bv_notMem_context typ_A v h)
          · exact absurd rfl (hAC_bv_disj v h v hC_bv)
    mspec C_ih (E := E) (Λ := σ_A.types) (used := σ_A.env.usedVars)
      (decl := σ.env.declarations ++ ΔA)
      typ_C (fun v hv => A_used_sub (vars_used_C v hv)) Λ_inv_C hC_bv_nodup
    clear C_ih
    rename_i out_C
    obtain ⟨C_enc, σC⟩ := out_C
    mrename_i pre
    mintro ∀σ_C
    mpure pre
    obtain ⟨⟨C_used_sub, C_Λ_sub, C_keys_sub, C_cov, C_fv_sub, C_preserves⟩,
      ΔC, C_decl_eq, C_specb, C_enc_fv_sub⟩ := pre
    have hpres : ∀ v ∈ used, v ∉ σ.types → v ∉ B.Term.vars (A ∪ᴮ C) → v ∉ σ_C.types :=
      fun v hv hΛ hvars => by
        have hvA : v ∉ B.Term.vars A := fun h => hvars (hvars_A_sub h)
        have hvC : v ∉ B.Term.vars C := fun h => hvars (hvars_C_sub h)
        exact C_preserves v (A_used_sub hv) (A_preserves v hv hΛ hvA) hvC
    unfold castUnion
    split <;> split <;> split <;> split
    · rename_i _ Senc1 _ Senc2 _ _ _ gamma heqA heqC
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heqA
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heqC
      mspec (Std.Do.Triple.and (SMT.freshVar gamma "union!")
        (SMT.freshVar_spec (Γ := σ_C.types) (τ := gamma) (n := σ_C.env.freshvarsc)
          (used := σ_C.env.usedVars))
        (SMT.freshVar_decls (τ := gamma) (decl := σ_C.env.declarations)))
      case post.success x =>
        mrename_i pre
        mintro ∀St₁
        mpure pre
        obtain ⟨⟨St₁_types_eq, x_fresh, St₁_fvc, St₁_used_eq, x_not_used⟩, St₁_decl⟩ := pre
        mspec (Std.Do.Triple.and (SMT.eraseFromContext x)
          (SMT.eraseFromContext_spec (v := x) (Γ := St₁.types) (n := St₁.env.freshvarsc)
            (used := St₁.env.usedVars))
          (SMT.eraseFromContext_decls (v := x) (decl := St₁.env.declarations)))
        mrename_i preE
        mintro ∀StE
        mpure preE
        obtain ⟨⟨StE_types_eq, StE_fvc, StE_used_eq⟩, StE_decl⟩ := preE
        have x_notσ : x ∉ σ.types := fun h =>
          x_fresh (AList.mem_of_subset (AList.subset_trans A_Λ_sub C_Λ_sub) h)
        mspec Std.Do.Spec.pure
        mpure_intro
        refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ΔA ++ ΔC, ?_, ?_, ?_⟩
        · intro v hv
          rw [StE_used_eq, St₁_used_eq]
          exact List.mem_cons_of_mem _ (C_used_sub (A_used_sub hv))
        · rw [StE_types_eq]
          apply SMT.TypeContext.entries_subset_erase_of_notMem _ x_notσ
          rw [St₁_types_eq]
          exact AList.subset_trans (AList.subset_trans A_Λ_sub C_Λ_sub)
            (SMT.TypeContext.entries_subset_insert_of_notMem x_fresh)
        · rw [StE_used_eq, St₁_used_eq]
          intro v hv
          rw [StE_types_eq] at hv
          have hv' : v ∈ AList.keys St₁.types := SMT.TypeContext.keys_erase_subset hv
          rw [St₁_types_eq] at hv'
          exact keys_insert_subset_cons C_keys_sub hv'
        · intro v hv
          rw [B.fv, List.mem_append] at hv
          rw [StE_used_eq, St₁_used_eq]
          rcases hv with hv | hv
          · exact List.mem_cons_of_mem _ (C_used_sub (A_cov v hv))
          · exact List.mem_cons_of_mem _ (C_cov v hv)
        · intro v hv
          simp only [SMT.fv, List.mem_removeAll_iff, List.mem_append, List.mem_cons,
            List.not_mem_nil, or_false] at hv
          obtain ⟨hv_body, hv_ne_x⟩ := hv
          rw [StE_types_eq, St₁_types_eq]
          rcases hv_body with (hvA | hvx) | (hvC | hvx)
          · rcases List.mem_union_iff.mp (A_fv_sub hvA) with hk | hb
            · exact List.mem_union_iff.mpr (.inl (AList.mem_keys.mpr (AList.mem_erase.mpr
                ⟨hv_ne_x, AList.mem_insert _ |>.mpr
                  (Or.inr (AList.mem_of_subset C_Λ_sub (AList.mem_keys.mp hk)))⟩)))
            · exact List.mem_union_iff.mpr (.inr (hvars_A_sub hb))
          · exact absurd hvx hv_ne_x
          · rcases List.mem_union_iff.mp (C_fv_sub hvC) with hk | hb
            · exact List.mem_union_iff.mpr (.inl (AList.mem_keys.mpr (AList.mem_erase.mpr
                ⟨hv_ne_x, AList.mem_insert _ |>.mpr (Or.inr (AList.mem_keys.mp hk))⟩)))
            · exact List.mem_union_iff.mpr (.inr (hvars_C_sub hb))
          · exact absurd hvx hv_ne_x
        · intro v hv hΛ hvars
          have hv_not_σC := hpres v hv hΛ hvars
          rw [StE_types_eq]
          apply SMT.TypeContext.notMem_erase
          rw [St₁_types_eq]
          intro hv_in
          rw [AList.mem_insert] at hv_in
          rcases hv_in with rfl | hv_in
          · exact x_not_used (C_used_sub (A_used_sub hv))
          · exact hv_not_σC hv_in
        · rw [StE_decl, St₁_decl, C_decl_eq, List.append_assoc]
        · intro b hb
          rw [specBodies_append, List.mem_append] at hb
          rcases hb with hb | hb
          · exact specBody_mono hvars_A_sub (declVars_append .. ▸ List.subset_append_left ..)
              (A_specb b hb)
          · exact specBody_mono hvars_C_sub (declVars_append .. ▸ List.subset_append_right ..)
              (C_specb b hb)
        · intro v hv
          simp only [SMT.fv, List.mem_removeAll_iff, List.mem_append, List.mem_cons,
            List.not_mem_nil, or_false] at hv
          obtain ⟨hv_body, hv_ne_x⟩ := hv
          rw [declVars_append]
          rcases hv_body with (hvA | hvx) | (hvC | hvx)
          · rcases List.mem_union_iff.mp (A_enc_fv_sub hvA) with h | h
            · exact List.mem_union_iff.mpr (.inl (hvars_A_sub h))
            · exact List.mem_union_iff.mpr (.inr (List.mem_append_left _ h))
          · exact absurd hvx hv_ne_x
          · rcases List.mem_union_iff.mp (C_enc_fv_sub hvC) with h | h
            · exact List.mem_union_iff.mpr (.inl (hvars_C_sub h))
            · exact List.mem_union_iff.mpr (.inr (List.mem_append_right _ h))
          · exact absurd hvx hv_ne_x
    · mvcgen
    · rename_i _ Senc1 _ heqA _ Senc2 _ heqC _ _
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heqA
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heqC
      mspec (Std.Do.Triple.and
        (castUnionAux A_enc C_enc _)
        (castUnionAux_state _ A_enc C_enc (Λ := σ_C.types) (n := σ_C.env.freshvarsc)
          (used := σ_C.env.usedVars) (X := B.Term.vars (A ∪ᴮ C)))
        (castUnionAux_decl _ A_enc C_enc (Λ := σ_C.types) (n := σ_C.env.freshvarsc)
          (used := σ_C.env.usedVars) (decl := σ.env.declarations ++ ΔA ++ ΔC)))
      case pre =>
        mpure_intro
        refine ⟨⟨rfl, rfl, C_keys_sub, rfl, ?_, ?_⟩, rfl, rfl, C_keys_sub, rfl, C_decl_eq⟩
        · intro v hv
          rcases List.mem_union_iff.mp (A_fv_sub hv) with hk | hb
          · exact List.mem_union_iff.mpr (.inl (AList.mem_keys.mpr
              (AList.mem_of_subset C_Λ_sub (AList.mem_keys.mp hk))))
          · exact List.mem_union_iff.mpr (.inr (hvars_A_sub hb))
        · intro v hv
          rcases List.mem_union_iff.mp (C_fv_sub hv) with hk | hb
          · exact List.mem_union_iff.mpr (.inl hk)
          · exact List.mem_union_iff.mpr (.inr (hvars_C_sub hb))
      case post.success =>
        rename_i out_cu
        obtain ⟨cu_enc, σcu⟩ := out_cu
        mrename_i pre
        mintro ∀σ'
        mpure pre
        obtain ⟨⟨h_le, h_Λ_sub, h_used_sub, h_keys_sub, h_fv_sub, h_preserves⟩,
          Dcu, cu_decl_eq, cu_specb, cu_fv_decl_sub⟩ := pre
        mpure_intro
        refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ΔA ++ ΔC ++ Dcu, ?_, ?_, ?_⟩
        · exact fun v hv => h_used_sub (C_used_sub (A_used_sub hv))
        · exact AList.subset_trans (AList.subset_trans A_Λ_sub C_Λ_sub) h_Λ_sub
        · exact h_keys_sub
        · intro v hv
          rw [B.fv, List.mem_append] at hv
          rcases hv with hv | hv
          · exact h_used_sub (C_used_sub (A_cov v hv))
          · exact h_used_sub (C_cov v hv)
        · exact h_fv_sub
        · intro v hv hΛ hvars
          exact h_preserves v (C_used_sub (A_used_sub hv)) (hpres v hv hΛ hvars)
        · rw [cu_decl_eq]; simp only [List.append_assoc]
        · intro b hb
          rw [specBodies_append, List.mem_append] at hb
          rcases hb with hb | hb
          · rw [specBodies_append, List.mem_append] at hb
            rcases hb with hb | hb
            · exact specBody_mono hvars_A_sub
                (by rw [declVars_append, declVars_append]
                    exact List.Subset.trans (List.subset_append_left ..)
                      (List.subset_append_left ..))
                (A_specb b hb)
            · exact specBody_mono hvars_C_sub
                (by rw [declVars_append, declVars_append]
                    exact List.Subset.trans (List.subset_append_right ..)
                      (List.subset_append_left ..))
                (C_specb b hb)
          · intro w hw
            have hw' := cu_specb b hb hw
            rw [declVars_append, declVars_append]
            rcases List.mem_union_iff.mp hw' with h | h
            · rcases List.mem_union_iff.mp h with h | h
              · rcases List.mem_union_iff.mp (A_enc_fv_sub h) with h | h
                · exact List.mem_union_iff.mpr (.inl (hvars_A_sub h))
                · exact List.mem_union_iff.mpr (.inr (List.mem_append_left _
                    (List.mem_append_left _ h)))
              · rcases List.mem_union_iff.mp (C_enc_fv_sub h) with h | h
                · exact List.mem_union_iff.mpr (.inl (hvars_C_sub h))
                · exact List.mem_union_iff.mpr (.inr (List.mem_append_left _
                    (List.mem_append_right _ h)))
            · exact List.mem_union_iff.mpr (.inr (List.mem_append_right _ h))
        · intro v hv
          have hv' := cu_fv_decl_sub hv
          rw [declVars_append, declVars_append]
          rcases List.mem_union_iff.mp hv' with h | h
          · rcases List.mem_union_iff.mp h with h | h
            · rcases List.mem_union_iff.mp (A_enc_fv_sub h) with h | h
              · exact List.mem_union_iff.mpr (.inl (hvars_A_sub h))
              · exact List.mem_union_iff.mpr (.inr (List.mem_append_left _
                  (List.mem_append_left _ h)))
            · rcases List.mem_union_iff.mp (C_enc_fv_sub h) with h | h
              · exact List.mem_union_iff.mpr (.inl (hvars_C_sub h))
              · exact List.mem_union_iff.mpr (.inr (List.mem_append_left _
                  (List.mem_append_right _ h)))
          · exact List.mem_union_iff.mpr (.inr (List.mem_append_right _ h))
    · split
      · rename_i _ Senc1 _ heqA _ Senc2 _ heqC _ _ _
        obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heqA
        obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heqC
        mspec (Std.Do.Triple.and
          (castUnionAux C_enc A_enc _)
          (castUnionAux_state _ C_enc A_enc (Λ := σ_C.types) (n := σ_C.env.freshvarsc)
            (used := σ_C.env.usedVars) (X := B.Term.vars (A ∪ᴮ C)))
          (castUnionAux_decl _ C_enc A_enc (Λ := σ_C.types) (n := σ_C.env.freshvarsc)
            (used := σ_C.env.usedVars) (decl := σ.env.declarations ++ ΔA ++ ΔC)))
        case pre =>
          mpure_intro
          refine ⟨⟨rfl, rfl, C_keys_sub, rfl, ?_, ?_⟩, rfl, rfl, C_keys_sub, rfl, C_decl_eq⟩
          · intro v hv
            rcases List.mem_union_iff.mp (C_fv_sub hv) with hk | hb
            · exact List.mem_union_iff.mpr (.inl hk)
            · exact List.mem_union_iff.mpr (.inr (hvars_C_sub hb))
          · intro v hv
            rcases List.mem_union_iff.mp (A_fv_sub hv) with hk | hb
            · exact List.mem_union_iff.mpr (.inl (AList.mem_keys.mpr
                (AList.mem_of_subset C_Λ_sub (AList.mem_keys.mp hk))))
            · exact List.mem_union_iff.mpr (.inr (hvars_A_sub hb))
        case post.success =>
          rename_i out_cu
          obtain ⟨cu_enc, σcu⟩ := out_cu
          mrename_i pre
          mintro ∀σ'
          mpure pre
          obtain ⟨⟨h_le, h_Λ_sub, h_used_sub, h_keys_sub, h_fv_sub, h_preserves⟩,
            Dcu, cu_decl_eq, cu_specb, cu_fv_decl_sub⟩ := pre
          mpure_intro
          refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ΔA ++ ΔC ++ Dcu, ?_, ?_, ?_⟩
          · exact fun v hv => h_used_sub (C_used_sub (A_used_sub hv))
          · exact AList.subset_trans (AList.subset_trans A_Λ_sub C_Λ_sub) h_Λ_sub
          · exact h_keys_sub
          · intro v hv
            rw [B.fv, List.mem_append] at hv
            rcases hv with hv | hv
            · exact h_used_sub (C_used_sub (A_cov v hv))
            · exact h_used_sub (C_cov v hv)
          · exact h_fv_sub
          · intro v hv hΛ hvars
            exact h_preserves v (C_used_sub (A_used_sub hv)) (hpres v hv hΛ hvars)
          · rw [cu_decl_eq]; simp only [List.append_assoc]
          · intro b hb
            rw [specBodies_append, List.mem_append] at hb
            rcases hb with hb | hb
            · rw [specBodies_append, List.mem_append] at hb
              rcases hb with hb | hb
              · exact specBody_mono hvars_A_sub
                  (by rw [declVars_append, declVars_append]
                      exact List.Subset.trans (List.subset_append_left ..)
                        (List.subset_append_left ..))
                  (A_specb b hb)
              · exact specBody_mono hvars_C_sub
                  (by rw [declVars_append, declVars_append]
                      exact List.Subset.trans (List.subset_append_right ..)
                        (List.subset_append_left ..))
                  (C_specb b hb)
            · intro w hw
              have hw' := cu_specb b hb hw
              rw [declVars_append, declVars_append]
              rcases List.mem_union_iff.mp hw' with h | h
              · rcases List.mem_union_iff.mp h with h | h
                · rcases List.mem_union_iff.mp (C_enc_fv_sub h) with h | h
                  · exact List.mem_union_iff.mpr (.inl (hvars_C_sub h))
                  · exact List.mem_union_iff.mpr (.inr (List.mem_append_left _
                      (List.mem_append_right _ h)))
                · rcases List.mem_union_iff.mp (A_enc_fv_sub h) with h | h
                  · exact List.mem_union_iff.mpr (.inl (hvars_A_sub h))
                  · exact List.mem_union_iff.mpr (.inr (List.mem_append_left _
                      (List.mem_append_left _ h)))
              · exact List.mem_union_iff.mpr (.inr (List.mem_append_right _ h))
          · intro v hv
            have hv' := cu_fv_decl_sub hv
            rw [declVars_append, declVars_append]
            rcases List.mem_union_iff.mp hv' with h | h
            · rcases List.mem_union_iff.mp h with h | h
              · rcases List.mem_union_iff.mp (C_enc_fv_sub h) with h | h
                · exact List.mem_union_iff.mpr (.inl (hvars_C_sub h))
                · exact List.mem_union_iff.mpr (.inr (List.mem_append_left _
                    (List.mem_append_right _ h)))
              · rcases List.mem_union_iff.mp (A_enc_fv_sub h) with h | h
                · exact List.mem_union_iff.mpr (.inl (hvars_A_sub h))
                · exact List.mem_union_iff.mpr (.inr (List.mem_append_left _
                    (List.mem_append_left _ h)))
            · exact List.mem_union_iff.mpr (.inr (List.mem_append_right _ h))
      · mvcgen
  | inter A C A_ih C_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq, rfl⟩ := pre
    rw [encodeTerm]
    obtain ⟨αA, rfl, typ_A, typ_C⟩ := B.Typing.interE typ_t
    have hA_bv_nodup : (B.bv A).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.1
    have hC_bv_nodup : (B.bv C).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.2.1
    have hAC_bv_disj : ∀ a ∈ B.bv A, ∀ b ∈ B.bv C, a ≠ b := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.2.2
    have vars_used_A : ∀ v ∈ A.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h)
    have vars_used_C : ∀ v ∈ C.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inr h)
    have Λ_inv_A : ∀ v ∈ A.vars, v ∈ σ.types → v ∈ E.context := fun v hv => Λ_inv v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h)
    have hbv_par : B.bv (A ∩ᴮ C) = B.bv A ++ B.bv C := by rw [B.bv]
    have hvars_A_sub : B.Term.vars A ⊆ B.Term.vars (A ∩ᴮ C) := fun v hv => by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h
    have hvars_C_sub : B.Term.vars C ⊆ B.Term.vars (A ∩ᴮ C) := fun v hv => by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inr h
    mspec A_ih (E := E) (Λ := σ.types) (decl := σ.env.declarations)
      typ_A vars_used_A Λ_inv_A hA_bv_nodup
    clear A_ih
    rename_i out_A
    obtain ⟨A_enc, σA⟩ := out_A
    mrename_i pre
    mintro ∀σ_A
    mpure pre
    obtain ⟨⟨A_used_sub, A_Λ_sub, A_keys_sub, A_cov, A_fv_sub, A_preserves⟩,
      ΔA, A_decl_eq, A_specb, A_enc_fv_sub⟩ := pre
    have Λ_inv_C : ∀ v ∈ C.vars, v ∈ σ_A.types → v ∈ E.context := fun v hv hΛ => by
      have hv_par : v ∈ (A ∩ᴮ C).vars := hvars_C_sub hv
      by_cases hv_St : v ∈ σ.types
      · exact Λ_inv v hv_par hv_St
      · have hv_vars_A : v ∈ B.Term.vars A := by
          by_contra h_neg
          exact absurd hΛ (A_preserves v (vars_used v hv_par) hv_St h_neg)
        rcases B.Term.mem_vars_iff.mp hv_vars_A with h | h
        · exact _root_.B.Typing.typed_by_fv typ_A h
        · rcases B.Term.mem_vars_iff.mp hv with hC_fv | hC_bv
          · exact absurd (_root_.B.Typing.typed_by_fv typ_C hC_fv)
              (_root_.B.Typing.bv_notMem_context typ_A v h)
          · exact absurd rfl (hAC_bv_disj v h v hC_bv)
    mspec C_ih (E := E) (Λ := σ_A.types) (used := σ_A.env.usedVars)
      (decl := σ.env.declarations ++ ΔA)
      typ_C (fun v hv => A_used_sub (vars_used_C v hv)) Λ_inv_C hC_bv_nodup
    clear C_ih
    rename_i out_C
    obtain ⟨C_enc, σC⟩ := out_C
    mrename_i pre
    mintro ∀σ_C
    mpure pre
    obtain ⟨⟨C_used_sub, C_Λ_sub, C_keys_sub, C_cov, C_fv_sub, C_preserves⟩,
      ΔC, C_decl_eq, C_specb, C_enc_fv_sub⟩ := pre
    have hpres : ∀ v ∈ used, v ∉ σ.types → v ∉ B.Term.vars (A ∩ᴮ C) → v ∉ σ_C.types :=
      fun v hv hΛ hvars => by
        have hvA : v ∉ B.Term.vars A := fun h => hvars (hvars_A_sub h)
        have hvC : v ∉ B.Term.vars C := fun h => hvars (hvars_C_sub h)
        exact C_preserves v (A_used_sub hv) (A_preserves v hv hΛ hvA) hvC
    unfold castInter
    split <;> split <;> split <;> split
    · rename_i _ Senc1 _ Senc2 _ _ _ gamma heqA heqC
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heqA
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heqC
      mspec (Std.Do.Triple.and (SMT.freshVar gamma "inter!")
        (SMT.freshVar_spec (Γ := σ_C.types) (τ := gamma) (n := σ_C.env.freshvarsc)
          (used := σ_C.env.usedVars))
        (SMT.freshVar_decls (τ := gamma) (decl := σ_C.env.declarations)))
      case post.success x =>
        mrename_i pre
        mintro ∀St₁
        mpure pre
        obtain ⟨⟨St₁_types_eq, x_fresh, St₁_fvc, St₁_used_eq, x_not_used⟩, St₁_decl⟩ := pre
        mspec (Std.Do.Triple.and (SMT.eraseFromContext x)
          (SMT.eraseFromContext_spec (v := x) (Γ := St₁.types) (n := St₁.env.freshvarsc)
            (used := St₁.env.usedVars))
          (SMT.eraseFromContext_decls (v := x) (decl := St₁.env.declarations)))
        mrename_i preE
        mintro ∀StE
        mpure preE
        obtain ⟨⟨StE_types_eq, StE_fvc, StE_used_eq⟩, StE_decl⟩ := preE
        have x_notσ : x ∉ σ.types := fun h =>
          x_fresh (AList.mem_of_subset (AList.subset_trans A_Λ_sub C_Λ_sub) h)
        mspec Std.Do.Spec.pure
        mpure_intro
        refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ΔA ++ ΔC, ?_, ?_, ?_⟩
        · intro v hv
          rw [StE_used_eq, St₁_used_eq]
          exact List.mem_cons_of_mem _ (C_used_sub (A_used_sub hv))
        · rw [StE_types_eq]
          apply SMT.TypeContext.entries_subset_erase_of_notMem _ x_notσ
          rw [St₁_types_eq]
          exact AList.subset_trans (AList.subset_trans A_Λ_sub C_Λ_sub)
            (SMT.TypeContext.entries_subset_insert_of_notMem x_fresh)
        · rw [StE_used_eq, St₁_used_eq]
          intro v hv
          rw [StE_types_eq] at hv
          have hv' : v ∈ AList.keys St₁.types := SMT.TypeContext.keys_erase_subset hv
          rw [St₁_types_eq] at hv'
          exact keys_insert_subset_cons C_keys_sub hv'
        · intro v hv
          rw [B.fv, List.mem_append] at hv
          rw [StE_used_eq, St₁_used_eq]
          rcases hv with hv | hv
          · exact List.mem_cons_of_mem _ (C_used_sub (A_cov v hv))
          · exact List.mem_cons_of_mem _ (C_cov v hv)
        · intro v hv
          simp only [SMT.fv, List.mem_removeAll_iff, List.mem_append, List.mem_cons,
            List.not_mem_nil, or_false] at hv
          obtain ⟨hv_body, hv_ne_x⟩ := hv
          rw [StE_types_eq, St₁_types_eq]
          rcases hv_body with (hvA | hvx) | (hvC | hvx)
          · rcases List.mem_union_iff.mp (A_fv_sub hvA) with hk | hb
            · exact List.mem_union_iff.mpr (.inl (AList.mem_keys.mpr (AList.mem_erase.mpr
                ⟨hv_ne_x, AList.mem_insert _ |>.mpr
                  (Or.inr (AList.mem_of_subset C_Λ_sub (AList.mem_keys.mp hk)))⟩)))
            · exact List.mem_union_iff.mpr (.inr (hvars_A_sub hb))
          · exact absurd hvx hv_ne_x
          · rcases List.mem_union_iff.mp (C_fv_sub hvC) with hk | hb
            · exact List.mem_union_iff.mpr (.inl (AList.mem_keys.mpr (AList.mem_erase.mpr
                ⟨hv_ne_x, AList.mem_insert _ |>.mpr (Or.inr (AList.mem_keys.mp hk))⟩)))
            · exact List.mem_union_iff.mpr (.inr (hvars_C_sub hb))
          · exact absurd hvx hv_ne_x
        · intro v hv hΛ hvars
          have hv_not_σC := hpres v hv hΛ hvars
          rw [StE_types_eq]
          apply SMT.TypeContext.notMem_erase
          rw [St₁_types_eq]
          intro hv_in
          rw [AList.mem_insert] at hv_in
          rcases hv_in with rfl | hv_in
          · exact x_not_used (C_used_sub (A_used_sub hv))
          · exact hv_not_σC hv_in
        · rw [StE_decl, St₁_decl, C_decl_eq, List.append_assoc]
        · intro b hb
          rw [specBodies_append, List.mem_append] at hb
          rcases hb with hb | hb
          · exact specBody_mono hvars_A_sub (declVars_append .. ▸ List.subset_append_left ..)
              (A_specb b hb)
          · exact specBody_mono hvars_C_sub (declVars_append .. ▸ List.subset_append_right ..)
              (C_specb b hb)
        · intro v hv
          simp only [SMT.fv, List.mem_removeAll_iff, List.mem_append, List.mem_cons,
            List.not_mem_nil, or_false] at hv
          obtain ⟨hv_body, hv_ne_x⟩ := hv
          rw [declVars_append]
          rcases hv_body with (hvA | hvx) | (hvC | hvx)
          · rcases List.mem_union_iff.mp (A_enc_fv_sub hvA) with h | h
            · exact List.mem_union_iff.mpr (.inl (hvars_A_sub h))
            · exact List.mem_union_iff.mpr (.inr (List.mem_append_left _ h))
          · exact absurd hvx hv_ne_x
          · rcases List.mem_union_iff.mp (C_enc_fv_sub hvC) with h | h
            · exact List.mem_union_iff.mpr (.inl (hvars_C_sub h))
            · exact List.mem_union_iff.mpr (.inr (List.mem_append_right _ h))
          · exact absurd hvx hv_ne_x
    · mvcgen
    · rename_i _ Senc1 _ heqA _ Senc2 _ heqC _ _
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heqA
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heqC
      mspec (Std.Do.Triple.and
        (castInterAux A_enc C_enc _)
        (castInterAux_state _ A_enc C_enc (Λ := σ_C.types) (n := σ_C.env.freshvarsc)
          (used := σ_C.env.usedVars) (X := B.Term.vars (A ∩ᴮ C)))
        (castInterAux_decl _ A_enc C_enc (Λ := σ_C.types) (n := σ_C.env.freshvarsc)
          (used := σ_C.env.usedVars) (decl := σ.env.declarations ++ ΔA ++ ΔC)))
      case pre =>
        mpure_intro
        refine ⟨⟨rfl, rfl, C_keys_sub, rfl, ?_, ?_⟩, rfl, rfl, C_keys_sub, rfl, C_decl_eq⟩
        · intro v hv
          rcases List.mem_union_iff.mp (A_fv_sub hv) with hk | hb
          · exact List.mem_union_iff.mpr (.inl (AList.mem_keys.mpr
              (AList.mem_of_subset C_Λ_sub (AList.mem_keys.mp hk))))
          · exact List.mem_union_iff.mpr (.inr (hvars_A_sub hb))
        · intro v hv
          rcases List.mem_union_iff.mp (C_fv_sub hv) with hk | hb
          · exact List.mem_union_iff.mpr (.inl hk)
          · exact List.mem_union_iff.mpr (.inr (hvars_C_sub hb))
      case post.success =>
        rename_i out_cu
        obtain ⟨cu_enc, σcu⟩ := out_cu
        mrename_i pre
        mintro ∀σ'
        mpure pre
        obtain ⟨⟨h_le, h_Λ_sub, h_used_sub, h_keys_sub, h_fv_sub, h_preserves⟩,
          Dcu, cu_decl_eq, cu_specb, cu_fv_decl_sub⟩ := pre
        mpure_intro
        refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ΔA ++ ΔC ++ Dcu, ?_, ?_, ?_⟩
        · exact fun v hv => h_used_sub (C_used_sub (A_used_sub hv))
        · exact AList.subset_trans (AList.subset_trans A_Λ_sub C_Λ_sub) h_Λ_sub
        · exact h_keys_sub
        · intro v hv
          rw [B.fv, List.mem_append] at hv
          rcases hv with hv | hv
          · exact h_used_sub (C_used_sub (A_cov v hv))
          · exact h_used_sub (C_cov v hv)
        · exact h_fv_sub
        · intro v hv hΛ hvars
          exact h_preserves v (C_used_sub (A_used_sub hv)) (hpres v hv hΛ hvars)
        · rw [cu_decl_eq]; simp only [List.append_assoc]
        · intro b hb
          rw [specBodies_append, List.mem_append] at hb
          rcases hb with hb | hb
          · rw [specBodies_append, List.mem_append] at hb
            rcases hb with hb | hb
            · exact specBody_mono hvars_A_sub
                (by rw [declVars_append, declVars_append]
                    exact List.Subset.trans (List.subset_append_left ..)
                      (List.subset_append_left ..))
                (A_specb b hb)
            · exact specBody_mono hvars_C_sub
                (by rw [declVars_append, declVars_append]
                    exact List.Subset.trans (List.subset_append_right ..)
                      (List.subset_append_left ..))
                (C_specb b hb)
          · intro w hw
            have hw' := cu_specb b hb hw
            rw [declVars_append, declVars_append]
            rcases List.mem_union_iff.mp hw' with h | h
            · rcases List.mem_union_iff.mp h with h | h
              · rcases List.mem_union_iff.mp (A_enc_fv_sub h) with h | h
                · exact List.mem_union_iff.mpr (.inl (hvars_A_sub h))
                · exact List.mem_union_iff.mpr (.inr (List.mem_append_left _
                    (List.mem_append_left _ h)))
              · rcases List.mem_union_iff.mp (C_enc_fv_sub h) with h | h
                · exact List.mem_union_iff.mpr (.inl (hvars_C_sub h))
                · exact List.mem_union_iff.mpr (.inr (List.mem_append_left _
                    (List.mem_append_right _ h)))
            · exact List.mem_union_iff.mpr (.inr (List.mem_append_right _ h))
        · intro v hv
          have hv' := cu_fv_decl_sub hv
          rw [declVars_append, declVars_append]
          rcases List.mem_union_iff.mp hv' with h | h
          · rcases List.mem_union_iff.mp h with h | h
            · rcases List.mem_union_iff.mp (A_enc_fv_sub h) with h | h
              · exact List.mem_union_iff.mpr (.inl (hvars_A_sub h))
              · exact List.mem_union_iff.mpr (.inr (List.mem_append_left _
                  (List.mem_append_left _ h)))
            · rcases List.mem_union_iff.mp (C_enc_fv_sub h) with h | h
              · exact List.mem_union_iff.mpr (.inl (hvars_C_sub h))
              · exact List.mem_union_iff.mpr (.inr (List.mem_append_left _
                  (List.mem_append_right _ h)))
          · exact List.mem_union_iff.mpr (.inr (List.mem_append_right _ h))
    · split
      · rename_i _ Senc1 _ heqA _ Senc2 _ heqC _ _ _
        obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heqA
        obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heqC
        mspec (Std.Do.Triple.and
          (castInterAux C_enc A_enc _)
          (castInterAux_state _ C_enc A_enc (Λ := σ_C.types) (n := σ_C.env.freshvarsc)
            (used := σ_C.env.usedVars) (X := B.Term.vars (A ∩ᴮ C)))
          (castInterAux_decl _ C_enc A_enc (Λ := σ_C.types) (n := σ_C.env.freshvarsc)
            (used := σ_C.env.usedVars) (decl := σ.env.declarations ++ ΔA ++ ΔC)))
        case pre =>
          mpure_intro
          refine ⟨⟨rfl, rfl, C_keys_sub, rfl, ?_, ?_⟩, rfl, rfl, C_keys_sub, rfl, C_decl_eq⟩
          · intro v hv
            rcases List.mem_union_iff.mp (C_fv_sub hv) with hk | hb
            · exact List.mem_union_iff.mpr (.inl hk)
            · exact List.mem_union_iff.mpr (.inr (hvars_C_sub hb))
          · intro v hv
            rcases List.mem_union_iff.mp (A_fv_sub hv) with hk | hb
            · exact List.mem_union_iff.mpr (.inl (AList.mem_keys.mpr
                (AList.mem_of_subset C_Λ_sub (AList.mem_keys.mp hk))))
            · exact List.mem_union_iff.mpr (.inr (hvars_A_sub hb))
        case post.success =>
          rename_i out_cu
          obtain ⟨cu_enc, σcu⟩ := out_cu
          mrename_i pre
          mintro ∀σ'
          mpure pre
          obtain ⟨⟨h_le, h_Λ_sub, h_used_sub, h_keys_sub, h_fv_sub, h_preserves⟩,
            Dcu, cu_decl_eq, cu_specb, cu_fv_decl_sub⟩ := pre
          mpure_intro
          refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ΔA ++ ΔC ++ Dcu, ?_, ?_, ?_⟩
          · exact fun v hv => h_used_sub (C_used_sub (A_used_sub hv))
          · exact AList.subset_trans (AList.subset_trans A_Λ_sub C_Λ_sub) h_Λ_sub
          · exact h_keys_sub
          · intro v hv
            rw [B.fv, List.mem_append] at hv
            rcases hv with hv | hv
            · exact h_used_sub (C_used_sub (A_cov v hv))
            · exact h_used_sub (C_cov v hv)
          · exact h_fv_sub
          · intro v hv hΛ hvars
            exact h_preserves v (C_used_sub (A_used_sub hv)) (hpres v hv hΛ hvars)
          · rw [cu_decl_eq]; simp only [List.append_assoc]
          · intro b hb
            rw [specBodies_append, List.mem_append] at hb
            rcases hb with hb | hb
            · rw [specBodies_append, List.mem_append] at hb
              rcases hb with hb | hb
              · exact specBody_mono hvars_A_sub
                  (by rw [declVars_append, declVars_append]
                      exact List.Subset.trans (List.subset_append_left ..)
                        (List.subset_append_left ..))
                  (A_specb b hb)
              · exact specBody_mono hvars_C_sub
                  (by rw [declVars_append, declVars_append]
                      exact List.Subset.trans (List.subset_append_right ..)
                        (List.subset_append_left ..))
                  (C_specb b hb)
            · intro w hw
              have hw' := cu_specb b hb hw
              rw [declVars_append, declVars_append]
              rcases List.mem_union_iff.mp hw' with h | h
              · rcases List.mem_union_iff.mp h with h | h
                · rcases List.mem_union_iff.mp (C_enc_fv_sub h) with h | h
                  · exact List.mem_union_iff.mpr (.inl (hvars_C_sub h))
                  · exact List.mem_union_iff.mpr (.inr (List.mem_append_left _
                      (List.mem_append_right _ h)))
                · rcases List.mem_union_iff.mp (A_enc_fv_sub h) with h | h
                  · exact List.mem_union_iff.mpr (.inl (hvars_A_sub h))
                  · exact List.mem_union_iff.mpr (.inr (List.mem_append_left _
                      (List.mem_append_left _ h)))
              · exact List.mem_union_iff.mpr (.inr (List.mem_append_right _ h))
          · intro v hv
            have hv' := cu_fv_decl_sub hv
            rw [declVars_append, declVars_append]
            rcases List.mem_union_iff.mp hv' with h | h
            · rcases List.mem_union_iff.mp h with h | h
              · rcases List.mem_union_iff.mp (C_enc_fv_sub h) with h | h
                · exact List.mem_union_iff.mpr (.inl (hvars_C_sub h))
                · exact List.mem_union_iff.mpr (.inr (List.mem_append_left _
                    (List.mem_append_right _ h)))
              · rcases List.mem_union_iff.mp (A_enc_fv_sub h) with h | h
                · exact List.mem_union_iff.mpr (.inl (hvars_A_sub h))
                · exact List.mem_union_iff.mpr (.inr (List.mem_append_left _
                    (List.mem_append_left _ h)))
            · exact List.mem_union_iff.mpr (.inr (List.mem_append_right _ h))
      · mvcgen
  | pfun A C A_ih C_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq, rfl⟩ := pre
    rw [encodeTerm]
    obtain ⟨αA, βC, rfl, typ_A, typ_C⟩ := B.Typing.pfunE typ_t
    have hA_bv_nodup : (B.bv A).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.1
    have hC_bv_nodup : (B.bv C).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.2.1
    have hAC_bv_disj : ∀ a ∈ B.bv A, ∀ b ∈ B.bv C, a ≠ b := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.2.2
    have vars_used_A : ∀ v ∈ A.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h)
    have vars_used_C : ∀ v ∈ C.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inr h)
    have Λ_inv_A : ∀ v ∈ A.vars, v ∈ σ.types → v ∈ E.context := fun v hv => Λ_inv v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h)
    have hvars_A_sub : B.Term.vars A ⊆ B.Term.vars (A ⇸ᴮ C) := fun v hv => by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h
    have hvars_C_sub : B.Term.vars C ⊆ B.Term.vars (A ⇸ᴮ C) := fun v hv => by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inr h
    mspec A_ih (E := E) (Λ := σ.types) (decl := σ.env.declarations)
      typ_A vars_used_A Λ_inv_A hA_bv_nodup
    rename_i out_A
    obtain ⟨A_enc, σA⟩ := out_A
    mrename_i preA
    mintro ∀σ_A
    mpure preA
    obtain ⟨⟨A_used_sub, A_Λ_sub, A_keys_sub, A_cov, A_fv_sub, A_preserves⟩,
      ΔA, A_decl_eq, A_specb, A_enc_fv_sub⟩ := preA
    have Λ_inv_C : ∀ v ∈ C.vars, v ∈ σ_A.types → v ∈ E.context := fun v hv hΛ => by
      have hv_par : v ∈ (A ⇸ᴮ C).vars := hvars_C_sub hv
      by_cases hv_St : v ∈ σ.types
      · exact Λ_inv v hv_par hv_St
      · have hv_vars_A : v ∈ B.Term.vars A := by
          by_contra h_neg
          exact absurd hΛ (A_preserves v (vars_used v hv_par) hv_St h_neg)
        rcases B.Term.mem_vars_iff.mp hv_vars_A with h | h
        · exact _root_.B.Typing.typed_by_fv typ_A h
        · rcases B.Term.mem_vars_iff.mp hv with hC_fv | hC_bv
          · exact absurd (_root_.B.Typing.typed_by_fv typ_C hC_fv)
              (_root_.B.Typing.bv_notMem_context typ_A v h)
          · exact absurd rfl (hAC_bv_disj v h v hC_bv)
    split
    · rename_i heq
      injection heq with hAe hσe
      subst hσe
      subst hAe
      mspec C_ih (E := E) (Λ := σ_A.types) (used := σ_A.env.usedVars)
        (decl := σ.env.declarations ++ ΔA)
        typ_C (fun v hv => A_used_sub (vars_used_C v hv)) Λ_inv_C hC_bv_nodup
      rename_i out_C
      obtain ⟨C_enc, σC⟩ := out_C
      mrename_i preC
      mintro ∀σ_C
      mpure preC
      obtain ⟨⟨C_used_sub, C_Λ_sub, C_keys_sub, C_cov, C_fv_sub, C_preserves⟩,
        ΔC, C_decl_eq, C_specb, C_enc_fv_sub⟩ := preC
      split
      · rename_i heq2
        injection heq2 with hCe hσe2
        subst hσe2
        subst hCe
        set ctx := σ_C.types with hctx
        mspec (Std.Do.Triple.and (SMT.freshVar _)
          (SMT.freshVar_spec (Γ := ctx) (n := σ_C.env.freshvarsc)
            (used := σ_C.env.usedVars))
          (SMT.freshVar_decls (decl := σ_C.env.declarations)))
        case post.success R =>
          mrename_i pre
          mintro ∀St₁
          mpure pre
          obtain ⟨⟨St₁_types_eq, R_fresh, St₁_fvc_eq, St₁_used_eq, R_not_used⟩,
            St₁_decl⟩ := pre
          mspec (Std.Do.Triple.and (SMT.freshVar _)
            (SMT.freshVar_spec (Γ := ctx.insert R _) (n := St₁.env.freshvarsc)
              (used := St₁.env.usedVars))
            (SMT.freshVar_decls (decl := St₁.env.declarations)))
          case post.success x =>
            mrename_i pre
            mintro ∀St₂
            mpure pre
            obtain ⟨⟨St₂_types_eq, x_fresh, St₂_fvc_eq, St₂_used_eq, x_not_used⟩,
              St₂_decl⟩ := pre
            mspec (Std.Do.Triple.and (SMT.freshVar _)
              (SMT.freshVar_spec (Γ := (ctx.insert R _).insert x _) (n := St₂.env.freshvarsc)
                (used := St₂.env.usedVars))
              (SMT.freshVar_decls (decl := St₂.env.declarations)))
            case post.success y =>
              mrename_i pre
              mintro ∀St₃
              mpure pre
              obtain ⟨⟨St₃_types_eq, y_fresh, St₃_fvc_eq, St₃_used_eq, y_not_used⟩,
                St₃_decl⟩ := pre
              mspec (Std.Do.Triple.and (SMT.freshVar _)
                (SMT.freshVar_spec (Γ := ((ctx.insert R _).insert x _).insert y _)
                  (n := St₃.env.freshvarsc) (used := St₃.env.usedVars))
                (SMT.freshVar_decls (decl := St₃.env.declarations)))
              case post.success y' =>
                mrename_i pre
                mintro ∀St₄
                mpure pre
                obtain ⟨⟨St₄_types_eq, y'_fresh, St₄_fvc_eq, St₄_used_eq, y'_not_used⟩,
                  St₄_decl⟩ := pre
                mspec (Std.Do.Triple.and (SMT.eraseFromContext R)
                  (SMT.eraseFromContext_spec (v := R) (Γ := St₄.types)
                    (n := St₄.env.freshvarsc) (used := St₄.env.usedVars))
                  (SMT.eraseFromContext_decls (v := R) (decl := St₄.env.declarations)))
                mrename_i preER
                mintro ∀StER
                mpure preER
                obtain ⟨⟨StER_types_eq, StER_fvc, StER_used_eq⟩, StER_decl⟩ := preER
                mspec (Std.Do.Triple.and (SMT.eraseFromContext x)
                  (SMT.eraseFromContext_spec (v := x) (Γ := StER.types)
                    (n := StER.env.freshvarsc) (used := StER.env.usedVars))
                  (SMT.eraseFromContext_decls (v := x) (decl := StER.env.declarations)))
                mrename_i preEx
                mintro ∀StEx
                mpure preEx
                obtain ⟨⟨StEx_types_eq, StEx_fvc, StEx_used_eq⟩, StEx_decl⟩ := preEx
                mspec (Std.Do.Triple.and (SMT.eraseFromContext y)
                  (SMT.eraseFromContext_spec (v := y) (Γ := StEx.types)
                    (n := StEx.env.freshvarsc) (used := StEx.env.usedVars))
                  (SMT.eraseFromContext_decls (v := y) (decl := StEx.env.declarations)))
                mrename_i preEy
                mintro ∀StEy
                mpure preEy
                obtain ⟨⟨StEy_types_eq, StEy_fvc, StEy_used_eq⟩, StEy_decl⟩ := preEy
                mspec (Std.Do.Triple.and (SMT.eraseFromContext y')
                  (SMT.eraseFromContext_spec (v := y') (Γ := StEy.types)
                    (n := StEy.env.freshvarsc) (used := StEy.env.usedVars))
                  (SMT.eraseFromContext_decls (v := y') (decl := StEy.env.declarations)))
                mrename_i preEy'
                mintro ∀StEy'
                mpure preEy'
                obtain ⟨⟨StEy'_types_eq, StEy'_fvc, StEy'_used_eq⟩, StEy'_decl⟩ := preEy'
                have hσ_sub_ctx : σ.types ⊆ ctx := AList.subset_trans A_Λ_sub C_Λ_sub
                have R_notσ : R ∉ σ.types := fun h => R_fresh (AList.mem_of_subset hσ_sub_ctx h)
                have x_notσ : x ∉ σ.types := fun h =>
                  x_fresh ((AList.mem_insert _).mpr (Or.inr (AList.mem_of_subset hσ_sub_ctx h)))
                have y_notσ : y ∉ σ.types := fun h =>
                  y_fresh ((AList.mem_insert _).mpr (Or.inr
                    ((AList.mem_insert _).mpr (Or.inr (AList.mem_of_subset hσ_sub_ctx h)))))
                have y'_notσ : y' ∉ σ.types := fun h =>
                  y'_fresh ((AList.mem_insert _).mpr (Or.inr
                    ((AList.mem_insert _).mpr (Or.inr
                      ((AList.mem_insert _).mpr (Or.inr (AList.mem_of_subset hσ_sub_ctx h)))))))
                have hv_ne : ∀ {v : SMT.𝒱}, v ≠ R → v ≠ x → v ≠ y → v ≠ y' → v ∈ ctx →
                    v ∈ AList.keys StEy'.types := by
                  intro v hvR hvx hvy hvy' hvctx
                  rw [← AList.mem_keys, StEy'_types_eq]
                  refine AList.mem_erase.mpr ⟨hvy', ?_⟩
                  rw [StEy_types_eq]
                  refine AList.mem_erase.mpr ⟨hvy, ?_⟩
                  rw [StEx_types_eq]
                  refine AList.mem_erase.mpr ⟨hvx, ?_⟩
                  rw [StER_types_eq]
                  refine AList.mem_erase.mpr ⟨hvR, ?_⟩
                  rw [St₄_types_eq]
                  exact (AList.mem_insert _).mpr (Or.inr ((AList.mem_insert _).mpr
                    (Or.inr ((AList.mem_insert _).mpr (Or.inr ((AList.mem_insert _).mpr
                      (Or.inr hvctx)))))))
                mspec Std.Do.Spec.pure
                mpure_intro
                refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ΔA ++ ΔC, ?_, ?_, ?_⟩
                · intro v hv
                  rw [StEy'_used_eq, StEy_used_eq, StEx_used_eq, StER_used_eq,
                    St₄_used_eq, St₃_used_eq, St₂_used_eq, St₁_used_eq]
                  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                      (C_used_sub (A_used_sub hv)))))
                · rw [StEy'_types_eq, StEy_types_eq, StEx_types_eq, StER_types_eq]
                  have base : σ.types ⊆ St₄.types := by
                    rw [St₄_types_eq]
                    exact AList.subset_trans (AList.subset_trans A_Λ_sub C_Λ_sub)
                      (AList.subset_trans
                        (SMT.TypeContext.entries_subset_insert_of_notMem R_fresh)
                        (AList.subset_trans
                          (SMT.TypeContext.entries_subset_insert_of_notMem x_fresh)
                          (AList.subset_trans
                            (SMT.TypeContext.entries_subset_insert_of_notMem y_fresh)
                            (SMT.TypeContext.entries_subset_insert_of_notMem y'_fresh))))
                  exact SMT.TypeContext.entries_subset_erase_of_notMem
                    (SMT.TypeContext.entries_subset_erase_of_notMem
                      (SMT.TypeContext.entries_subset_erase_of_notMem
                        (SMT.TypeContext.entries_subset_erase_of_notMem base R_notσ)
                          x_notσ) y_notσ) y'_notσ
                · intro v hv
                  rw [StEy'_used_eq, StEy_used_eq, StEx_used_eq, StER_used_eq,
                    St₄_used_eq, St₃_used_eq, St₂_used_eq, St₁_used_eq]
                  have hv0 : v ∈ AList.keys St₄.types :=
                    SMT.TypeContext.keys_erase_subset (StER_types_eq ▸
                      SMT.TypeContext.keys_erase_subset (StEx_types_eq ▸
                        SMT.TypeContext.keys_erase_subset (StEy_types_eq ▸
                          SMT.TypeContext.keys_erase_subset (StEy'_types_eq ▸ hv))))
                  have hv' : v ∈ St₄.types := AList.mem_keys.mpr hv0
                  rw [St₄_types_eq] at hv'
                  iterate 4 rw [AList.mem_insert] at hv'
                  rcases hv' with rfl | rfl | rfl | rfl | hv'
                  · exact List.mem_cons_self
                  · exact List.mem_cons_of_mem _ List.mem_cons_self
                  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
                  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                      (List.mem_cons_of_mem _ List.mem_cons_self))
                  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                        (C_keys_sub (AList.mem_keys.mp hv')))))
                · intro v hv
                  rw [B.fv, List.mem_append] at hv
                  rw [StEy'_used_eq, StEy_used_eq, StEx_used_eq, StER_used_eq,
                    St₄_used_eq, St₃_used_eq, St₂_used_eq, St₁_used_eq]
                  rcases hv with hv | hv
                  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                        (C_used_sub (A_cov v hv)))))
                  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (C_cov v hv))))
                · intro v hv
                  simp only [SMT.fv, List.mem_removeAll_iff, List.mem_append,
                    List.mem_cons, List.not_mem_nil, or_false] at hv
                  obtain ⟨hv_body, hv_ne_R⟩ := hv
                  -- Any key of `ctx` differs from the fresh binders `x`, `y`, `y'`.
                  have ctx_ne_x : ∀ {w}, w ∈ ctx → w ≠ x := fun hw h =>
                    x_fresh (h ▸ (AList.mem_insert _).mpr (Or.inr hw))
                  have ctx_ne_y : ∀ {w}, w ∈ ctx → w ≠ y := fun hw h =>
                    y_fresh (h ▸ (AList.mem_insert _).mpr (Or.inr
                      ((AList.mem_insert _).mpr (Or.inr hw))))
                  have ctx_ne_y' : ∀ {w}, w ∈ ctx → w ≠ y' := fun hw h =>
                    y'_fresh (h ▸ (AList.mem_insert _).mpr (Or.inr
                      ((AList.mem_insert _).mpr (Or.inr
                        ((AList.mem_insert _).mpr (Or.inr hw))))))
                  have hv_ctx : v ∈ ctx → v ∈ AList.keys StEy'.types ∪ B.Term.vars (A ⇸ᴮ C) :=
                    fun hvc => List.mem_union_iff.mpr (Or.inl
                      (hv_ne hv_ne_R (ctx_ne_x hvc) (ctx_ne_y hvc) (ctx_ne_y' hvc) hvc))
                  rcases hv_body with ⟨hv1, hv_ne_xy⟩ | ⟨hv2, hv_ne_xyy'⟩
                  · rcases hv1 with (hR | hx | hy) | (hvA | hx) | hvC | hy
                    · exact absurd hR hv_ne_R
                    · exact absurd (Or.inl hx) hv_ne_xy
                    · exact absurd (Or.inr hy) hv_ne_xy
                    · rcases List.mem_union_iff.mp (A_fv_sub hvA) with hk | hbv
                      · exact hv_ctx (AList.mem_of_subset C_Λ_sub (AList.mem_keys.mp hk))
                      · exact List.mem_union_iff.mpr (Or.inr (hvars_A_sub hbv))
                    · exact absurd (Or.inl hx) hv_ne_xy
                    · rcases List.mem_union_iff.mp (C_fv_sub hvC) with hk | hbv
                      · exact hv_ctx (AList.mem_keys.mp hk)
                      · exact List.mem_union_iff.mpr (Or.inr (hvars_C_sub hbv))
                    · exact absurd (Or.inr hy) hv_ne_xy
                  · rcases hv2 with ((hR | hx | hy) | hR | hx | hy') | hy | hy'
                    · exact absurd hR hv_ne_R
                    · exact absurd (Or.inl hx) hv_ne_xyy'
                    · exact absurd (Or.inr (Or.inl hy)) hv_ne_xyy'
                    · exact absurd hR hv_ne_R
                    · exact absurd (Or.inl hx) hv_ne_xyy'
                    · exact absurd (Or.inr (Or.inr hy')) hv_ne_xyy'
                    · exact absurd (Or.inr (Or.inl hy)) hv_ne_xyy'
                    · exact absurd (Or.inr (Or.inr hy')) hv_ne_xyy'
                · intro v hv hΛ hvars
                  have hvA : v ∉ B.Term.vars A := fun h => hvars (hvars_A_sub h)
                  have hvC : v ∉ B.Term.vars C := fun h => hvars (hvars_C_sub h)
                  have hv_not_ctx : v ∉ ctx :=
                    C_preserves v (A_used_sub hv) (A_preserves v hv hΛ hvA) hvC
                  rw [StEy'_types_eq]
                  apply SMT.TypeContext.notMem_erase
                  rw [StEy_types_eq]
                  apply SMT.TypeContext.notMem_erase
                  rw [StEx_types_eq]
                  apply SMT.TypeContext.notMem_erase
                  rw [StER_types_eq]
                  apply SMT.TypeContext.notMem_erase
                  rw [St₄_types_eq]
                  intro hv_in
                  iterate 4 rw [AList.mem_insert] at hv_in
                  rcases hv_in with rfl | rfl | rfl | rfl | hv_in
                  · exact y'_not_used (by
                      rw [St₃_used_eq, St₂_used_eq, St₁_used_eq]
                      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                        (List.mem_cons_of_mem _ (C_used_sub (A_used_sub hv)))))
                  · exact y_not_used (by
                      rw [St₂_used_eq, St₁_used_eq]
                      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                        (C_used_sub (A_used_sub hv))))
                  · exact x_not_used (by
                      rw [St₁_used_eq]
                      exact List.mem_cons_of_mem _ (C_used_sub (A_used_sub hv)))
                  · exact R_not_used (C_used_sub (A_used_sub hv))
                  · exact hv_not_ctx hv_in
                · rw [StEy'_decl, StEy_decl, StEx_decl, StER_decl,
                    St₄_decl, St₃_decl, St₂_decl, St₁_decl, C_decl_eq, List.append_assoc]
                · intro b hb
                  rw [specBodies_append, List.mem_append] at hb
                  rcases hb with hb | hb
                  · exact specBody_mono hvars_A_sub
                      (declVars_append .. ▸ List.subset_append_left ..) (A_specb b hb)
                  · exact specBody_mono hvars_C_sub
                      (declVars_append .. ▸ List.subset_append_right ..) (C_specb b hb)
                · intro v hv
                  simp only [SMT.fv, List.mem_removeAll_iff, List.mem_append,
                    List.mem_cons, List.not_mem_nil, or_false] at hv
                  obtain ⟨hv_body, hv_ne_R⟩ := hv
                  rw [declVars_append]
                  rcases hv_body with ⟨hv1, hv_ne_xy⟩ | ⟨hv2, hv_ne_xyy'⟩
                  · rcases hv1 with (hR | hx | hy) | (hvA | hx) | hvC | hy
                    · exact absurd hR hv_ne_R
                    · exact absurd (Or.inl hx) hv_ne_xy
                    · exact absurd (Or.inr hy) hv_ne_xy
                    · rcases List.mem_union_iff.mp (A_enc_fv_sub hvA) with h | h
                      · exact List.mem_union_iff.mpr (.inl (hvars_A_sub h))
                      · exact List.mem_union_iff.mpr (.inr (List.mem_append_left _ h))
                    · exact absurd (Or.inl hx) hv_ne_xy
                    · rcases List.mem_union_iff.mp (C_enc_fv_sub hvC) with h | h
                      · exact List.mem_union_iff.mpr (.inl (hvars_C_sub h))
                      · exact List.mem_union_iff.mpr (.inr (List.mem_append_right _ h))
                    · exact absurd (Or.inr hy) hv_ne_xy
                  · rcases hv2 with ((hR | hx | hy) | hR | hx | hy') | hy | hy'
                    · exact absurd hR hv_ne_R
                    · exact absurd (Or.inl hx) hv_ne_xyy'
                    · exact absurd (Or.inr (Or.inl hy)) hv_ne_xyy'
                    · exact absurd hR hv_ne_R
                    · exact absurd (Or.inl hx) hv_ne_xyy'
                    · exact absurd (Or.inr (Or.inr hy')) hv_ne_xyy'
                    · exact absurd (Or.inr (Or.inl hy)) hv_ne_xyy'
                    · exact absurd (Or.inr (Or.inr hy')) hv_ne_xyy'
      · mvcgen
    · mvcgen
  | app f x f_ih x_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq, rfl⟩ := pre
    rw [encodeTerm]
    obtain ⟨αx, typ_f, typ_x⟩ := B.Typing.appE typ_t
    have hf_bv_nodup : (B.bv f).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.1
    have hx_bv_nodup : (B.bv x).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.2.1
    have hfx_bv_disj : ∀ a ∈ B.bv f, ∀ b ∈ B.bv x, a ≠ b := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.2.2
    have vars_used_f : ∀ v ∈ f.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h)
    have vars_used_x : ∀ v ∈ x.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inr h)
    have Λ_inv_f : ∀ v ∈ f.vars, v ∈ σ.types → v ∈ E.context := fun v hv => Λ_inv v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h)
    have hbv_par : B.bv (B.Term.app f x) = B.bv f ++ B.bv x := by rw [B.bv]
    have hvars_f_sub : B.Term.vars f ⊆ B.Term.vars (B.Term.app f x) := fun v hv => by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h
    have hvars_x_sub : B.Term.vars x ⊆ B.Term.vars (B.Term.app f x) := fun v hv => by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inr h
    mspec f_ih (E := E) (Λ := σ.types) (decl := σ.env.declarations)
      typ_f vars_used_f Λ_inv_f hf_bv_nodup
    clear f_ih
    rename_i out_f
    obtain ⟨f_enc, σf⟩ := out_f
    mrename_i pre
    mintro ∀σ_f
    mpure pre
    obtain ⟨⟨f_used_sub, f_Λ_sub, f_keys_sub, f_cov, f_fv_sub, f_preserves⟩,
      Δf, f_decl_eq, f_specb, f_enc_fv_sub⟩ := pre
    have Λ_inv_x : ∀ v ∈ x.vars, v ∈ σ_f.types → v ∈ E.context := fun v hv hΛ => by
      have hv_par : v ∈ (B.Term.app f x).vars := hvars_x_sub hv
      by_cases hv_St : v ∈ σ.types
      · exact Λ_inv v hv_par hv_St
      · have hv_vars_f : v ∈ B.Term.vars f := by
          by_contra h_neg
          exact absurd hΛ (f_preserves v (vars_used v hv_par) hv_St h_neg)
        rcases B.Term.mem_vars_iff.mp hv_vars_f with h | h
        · exact _root_.B.Typing.typed_by_fv typ_f h
        · rcases B.Term.mem_vars_iff.mp hv with hx_fv | hx_bv
          · exact absurd (_root_.B.Typing.typed_by_fv typ_x hx_fv)
              (_root_.B.Typing.bv_notMem_context typ_f v h)
          · exact absurd rfl (hfx_bv_disj v h v hx_bv)
    mspec x_ih (E := E) (Λ := σ_f.types) (used := σ_f.env.usedVars)
      (decl := σ.env.declarations ++ Δf)
      typ_x (fun v hv => f_used_sub (vars_used_x v hv)) Λ_inv_x hx_bv_nodup
    clear x_ih
    rename_i out_x
    obtain ⟨x_enc, σx⟩ := out_x
    mrename_i pre
    mintro ∀σ_x
    mpure pre
    obtain ⟨⟨x_used_sub, x_Λ_sub, x_keys_sub, x_cov, x_fv_sub, x_preserves⟩,
      Δx, x_decl_eq, x_specb, x_enc_fv_sub⟩ := pre
    mspec (Std.Do.Triple.and
      (castApp (f_enc, σf) (x_enc, σx))
      (castApp_state f_enc x_enc σf σx (Λ := σ_x.types) (n := σ_x.env.freshvarsc)
        (used := σ_x.env.usedVars) (X := B.Term.vars (B.Term.app f x)))
      (castApp_decl f_enc x_enc σf σx (Λ := σ_x.types) (n := σ_x.env.freshvarsc)
        (used := σ_x.env.usedVars) (decl := σ.env.declarations ++ Δf ++ Δx)))
    case pre =>
      mpure_intro
      refine ⟨⟨rfl, rfl, x_keys_sub, rfl, ?_, ?_⟩, rfl, rfl, x_keys_sub, rfl, x_decl_eq⟩
      · intro v hv
        rcases List.mem_union_iff.mp (f_fv_sub hv) with hk | hb
        · exact List.mem_union_iff.mpr (.inl (AList.mem_keys.mpr
            (AList.mem_of_subset x_Λ_sub (AList.mem_keys.mp hk))))
        · exact List.mem_union_iff.mpr (.inr (hvars_f_sub hb))
      · intro v hv
        rcases List.mem_union_iff.mp (x_fv_sub hv) with hk | hb
        · exact List.mem_union_iff.mpr (.inl hk)
        · exact List.mem_union_iff.mpr (.inr (hvars_x_sub hb))
    case post.success =>
      rename_i out_ca
      obtain ⟨ca_enc, σca⟩ := out_ca
      mrename_i pre
      mintro ∀σ'
      mpure pre
      obtain ⟨⟨h_le, h_Λ_sub, h_used_sub, h_keys_sub, h_fv_sub, h_preserves⟩,
        Dca, ca_decl_eq, ca_specb, ca_fv_decl_sub⟩ := pre
      mpure_intro
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, Δf ++ Δx ++ Dca, ?_, ?_, ?_⟩
      · exact fun v hv => h_used_sub (x_used_sub (f_used_sub hv))
      · exact AList.subset_trans (AList.subset_trans f_Λ_sub x_Λ_sub) h_Λ_sub
      · exact h_keys_sub
      · intro v hv
        rw [B.fv, List.mem_append] at hv
        rcases hv with hv | hv
        · exact h_used_sub (x_used_sub (f_cov v hv))
        · exact h_used_sub (x_cov v hv)
      · exact h_fv_sub
      · intro v hv hΛ hvars
        have hvf : v ∉ B.Term.vars f := fun h => hvars (hvars_f_sub h)
        have hvx : v ∉ B.Term.vars x := fun h => hvars (hvars_x_sub h)
        exact h_preserves v (x_used_sub (f_used_sub hv))
          (x_preserves v (f_used_sub hv) (f_preserves v hv hΛ hvf) hvx)
      · rw [ca_decl_eq]; simp only [List.append_assoc]
      · intro b hb
        rw [specBodies_append, List.mem_append] at hb
        rcases hb with hb | hb
        · rw [specBodies_append, List.mem_append] at hb
          rcases hb with hb | hb
          · exact specBody_mono hvars_f_sub
              (by rw [declVars_append, declVars_append]
                  exact List.Subset.trans (List.subset_append_left ..)
                    (List.subset_append_left ..))
              (f_specb b hb)
          · exact specBody_mono hvars_x_sub
              (by rw [declVars_append, declVars_append]
                  exact List.Subset.trans (List.subset_append_right ..)
                    (List.subset_append_left ..))
              (x_specb b hb)
        · intro w hw
          have hw' := ca_specb b hb hw
          rw [declVars_append, declVars_append]
          rcases List.mem_union_iff.mp hw' with h | h
          · rcases List.mem_union_iff.mp h with h | h
            · rcases List.mem_union_iff.mp (f_enc_fv_sub h) with h | h
              · exact List.mem_union_iff.mpr (.inl (hvars_f_sub h))
              · exact List.mem_union_iff.mpr
                  (.inr (List.mem_append_left _ (List.mem_append_left _ h)))
            · rcases List.mem_union_iff.mp (x_enc_fv_sub h) with h | h
              · exact List.mem_union_iff.mpr (.inl (hvars_x_sub h))
              · exact List.mem_union_iff.mpr
                  (.inr (List.mem_append_left _ (List.mem_append_right _ h)))
          · exact List.mem_union_iff.mpr (.inr (List.mem_append_right _ h))
      · intro v hv
        have hv' := ca_fv_decl_sub hv
        rw [declVars_append, declVars_append]
        rcases List.mem_union_iff.mp hv' with h | h
        · rcases List.mem_union_iff.mp h with h | h
          · rcases List.mem_union_iff.mp (f_enc_fv_sub h) with h | h
            · exact List.mem_union_iff.mpr (.inl (hvars_f_sub h))
            · exact List.mem_union_iff.mpr (.inr (List.mem_append_left _
                (List.mem_append_left _ h)))
          · rcases List.mem_union_iff.mp (x_enc_fv_sub h) with h | h
            · exact List.mem_union_iff.mpr (.inl (hvars_x_sub h))
            · exact List.mem_union_iff.mpr (.inr (List.mem_append_left _
                (List.mem_append_right _ h)))
        · exact List.mem_union_iff.mpr (.inr (List.mem_append_right _ h))
  | collect vs D P D_ih P_ih =>
    mintro pre ∀St₀
    mpure pre
    obtain ⟨rfl, rfl, St₀_sub, St₀_used_eq, St₀_decl_eq⟩ := pre
    rw [encodeTerm]
    obtain ⟨αs, Ds, vs_nemp, vs_αs_len, vs_Ds_len, α_eq, vs_nodup, D_eq, typDs, typP,
      vs_Γ_disj⟩ := B.Typing.collectE typ_t
    set τ := αs.reduce (· ×ᴮ ·) (by simpa [vs_αs_len, ← List.length_pos_iff] using vs_nemp)
      with τ_def
    have typ_D : E.context ⊢ᴮ D : .set τ := by
      rw [D_eq]
      exact encodeTerm_state.typing_reduce_cprod E.context _ _ typDs
        (by simpa [vs_Ds_len, ← List.length_pos_iff] using vs_nemp)
        (by simpa [vs_αs_len, ← List.length_pos_iff] using vs_nemp)
    have hD_bv_nodup : (B.bv D).Nodup := by
      have h := bv_nodup
      simp only [B.bv] at h
      rw [List.nodup_append, List.nodup_append] at h
      exact h.1.2.1
    have hP_bv_nodup : (B.bv P).Nodup := by
      have h := bv_nodup
      simp only [B.bv] at h
      rw [List.nodup_append] at h
      exact h.2.1
    have vars_used_D : ∀ v ∈ D.vars, v ∈ used := by
      intro v hv
      apply vars_used v
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.append_assoc,
        List.mem_append, List.mem_removeAll_iff] at hv ⊢
      rcases hv with hv | hv
      · exact .inl (.inl hv)
      · exact .inr (.inr (.inl hv))
    have vars_used_vs : ∀ v ∈ vs, v ∈ used := by
      intro v hv
      apply vars_used v
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.append_assoc,
        List.mem_append] at hv ⊢
      exact .inr (.inl hv)
    have vars_used_P : ∀ v ∈ P.vars, v ∈ used := by
      intro v hv
      by_cases hvs : v ∈ vs
      · exact vars_used_vs v hvs
      · apply vars_used v
        simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.append_assoc,
          List.mem_append, List.mem_removeAll_iff] at hv ⊢
        rcases hv with hv | hv
        · exact .inl (.inr ⟨hv, hvs⟩)
        · exact .inr (.inr (.inr hv))
    have Λ_inv_D : ∀ v ∈ D.vars, v ∈ St₀.types → v ∈ E.context := by
      intro v hv hSt₀
      apply Λ_inv v _ hSt₀
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.append_assoc,
        List.mem_append, List.mem_removeAll_iff] at hv ⊢
      rcases hv with hv | hv
      · exact .inl (.inl hv)
      · exact .inr (.inr (.inl hv))
    have hvars_D_sub : B.Term.vars D ⊆ B.Term.vars (B.Term.collect vs D P) := by
      intro v hv
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.append_assoc,
        List.mem_append, List.mem_removeAll_iff] at hv ⊢
      rcases hv with hv | hv
      · exact .inl (.inl hv)
      · exact .inr (.inr (.inl hv))
    have hvars_vs_sub : ∀ v ∈ vs, v ∈ B.Term.vars (B.Term.collect vs D P) := by
      intro v hv
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.append_assoc,
        List.mem_append] at hv ⊢
      exact .inr (.inl hv)
    have hvars_P_sub : B.Term.vars P ⊆ B.Term.vars (B.Term.collect vs D P) := by
      intro v hv
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.append_assoc,
        List.mem_append, List.mem_removeAll_iff] at hv ⊢
      rcases hv with hvP | hvP
      · by_cases hvs : v ∈ vs
        · exact .inr (.inl hvs)
        · exact .inl (.inr ⟨hvP, hvs⟩)
      · exact .inr (.inr (.inr hvP))
    mspec D_ih (E := E) (Λ := St₀.types) (n := St₀.env.freshvarsc) (used := used)
      (α := .set τ) (decl := decl) typ_D vars_used_D Λ_inv_D hD_bv_nodup
    rename_i out_D
    obtain ⟨D_enc, τD⟩ := out_D
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨⟨D_used_sub, D_Λ_sub, D_keys_sub, D_cov, D_state_fv_sub, D_preserves⟩,
      ΔD, D_decl_eq, D_specb, D_fv_sub⟩ := pre
    split
    · -- function-`D` arm
      rename_i α' β' heq
      split
      · -- arity matches
        rename_i harity
        set αs' := α'.fromProdl (vs.length - 2) with αs'_def
        have αs'_len_pos : 1 ≤ αs'.length := by
          rw [αs'_def]
          cases h2 : vs.length - 2 with
          | zero => cases α' <;> simp [SMT.SMTType.fromProdl]
          | succ k =>
            cases α' <;>
              simp [SMT.SMTType.fromProdl, List.concat_eq_append, List.length_append]
        have αs'_len_eq : αs'.length = vs.length - 1 := beq_iff_eq.mp harity
        have vs_len_ge_2 : 2 ≤ vs.length := by omega
        have αs'_toProdl_eq : αs'.toProdl = α' := by
          rw [αs'_def]
          exact encodeTerm_state.fromProdl_toProdl_roundtrip α' (vs.length - 2)
            (by rw [← αs'_def, αs'_len_eq]; omega)
        mspec Std.Do.Spec.pure
        mspec (Std.Do.Triple.and _
          (encodeTerm_state.modifyTypes_forIn_spec (vs.zip (αs'.concat β'))
            (Γ := St₁.types) (n := St₁.env.freshvarsc) (used := St₁.env.usedVars))
          (encodeTerm_state.modifyTypes_forIn_decls (vs.zip (αs'.concat β'))
            (decl := decl ++ ΔD)))
        mrename_i pre
        mintro ∀St₂
        mpure pre
        obtain ⟨⟨St₂_types, St₂_fvc, St₂_used⟩, St₂_decl⟩ := pre
        set E' : B.Env := { E with context := vs.zipToAList αs ∪ E.context } with E'_def
        conv in encodeTerm P E => rw [encodeTerm_state.encodeTerm_env_irrel P E E' rfl]
        have St₂_used_eq : St₂.env.usedVars = St₁.env.usedVars := St₂_used
        have vars_used_P_St₂ : ∀ v ∈ P.vars, v ∈ St₂.env.usedVars := by
          rw [St₂_used_eq]
          exact fun v hv => D_used_sub (vars_used_P v hv)
        have vs_disj_St₁ : ∀ v ∈ vs, v ∉ St₁.types := by
          intro v hv
          have vs_not_D_fv : v ∉ B.fv D := fun hv_fv =>
            vs_Γ_disj v hv (AList.lookup_isSome.mp (B.Typing.mem_context_of_mem_fv typ_D hv_fv))
          have hv_vars_D : v ∉ B.Term.vars D :=
            B.Term.notMem_vars_iff.mpr ⟨vs_not_D_fv, by
              have h := bv_nodup
              simp only [B.bv] at h
              rw [List.nodup_append, List.nodup_append] at h
              intro h_bv
              exact h.1.2.2 v hv v h_bv rfl⟩
          apply D_preserves v (vars_used_vs v hv) _ hv_vars_D
          intro hv_St₀
          have hv_coll : v ∈ (B.Term.collect vs D P).vars := by
            unfold B.Term.vars; rw [List.mem_union_iff]; right
            simp only [B.bv, List.mem_append]; exact .inl (.inl hv)
          exact vs_Γ_disj v hv (Λ_inv v hv_coll hv_St₀)
        have Λ_inv_P : ∀ v ∈ P.vars, v ∈ St₂.types → v ∈ E'.context := by
          intro v v_in_P_vars v_in_St₂_types
          rw [E'_def]
          show v ∈ vs.zipToAList αs ∪ E.context
          by_cases v_in_vs : v ∈ vs
          · exact AList.mem_union.mpr (.inl (AList.mem_zipToAList_of_mem vs_nodup vs_αs_len v_in_vs))
          · have v_in_St₁ : v ∈ St₁.types := by
              rw [St₂_types] at v_in_St₂_types
              refine AList.mem_of_mem_foldl_insert' v_in_St₂_types ?_
              intro h
              rw [List.mem_map] at h
              obtain ⟨⟨a, b⟩, hab, rfl⟩ := h
              exact v_in_vs (List.of_mem_zip hab).1
            have v_used : v ∈ used := vars_used_P v v_in_P_vars
            by_cases v_St₀ : v ∈ St₀.types
            · have v_coll : v ∈ (B.Term.collect vs D P).vars := by
                unfold B.Term.vars at v_in_P_vars ⊢
                rw [List.mem_union_iff]
                rcases List.mem_union_iff.mp v_in_P_vars with h_fv | h_bv
                · exact .inl (by
                    simp only [B.fv, List.mem_append]
                    exact .inr (List.mem_removeAll_iff.mpr ⟨h_fv, v_in_vs⟩))
                · exact .inr (by
                    simp only [B.bv, List.mem_append]
                    exact .inr h_bv)
              exact AList.mem_union.mpr (.inr (Λ_inv v v_coll v_St₀))
            · have v_vars_D : v ∈ B.Term.vars D := by
                by_contra h
                exact absurd v_in_St₁ (D_preserves v v_used v_St₀ h)
              rcases B.Term.mem_vars_iff.mp v_vars_D with h | h
              · exact AList.mem_union.mpr (.inr (AList.lookup_isSome.mp
                  (B.Typing.mem_context_of_mem_fv typ_D h)))
              · rcases B.Term.mem_vars_iff.mp v_in_P_vars with hv_fv_P | hv_bv_P
                · have h_in_E' : ((vs.zipToAList αs ∪ E.context).lookup v).isSome :=
                    B.Typing.mem_context_of_mem_fv typP hv_fv_P
                  exact AList.lookup_isSome.mp h_in_E'
                · exfalso
                  have hbn := bv_nodup
                  simp only [B.bv] at hbn
                  rw [List.nodup_append] at hbn
                  have hin : v ∈ vs ++ B.bv D := List.mem_append.mpr (.inr h)
                  exact hbn.2.2 v hin v hv_bv_P rfl
        have vs_sub_St₁_used : ∀ v ∈ vs, v ∈ St₁.env.usedVars :=
          fun v hv => D_used_sub (vars_used_vs v hv)
        have St₂_keys_sub : AList.keys St₂.types ⊆ St₂.env.usedVars := by
          rw [St₂_types, St₂_used_eq]
          exact encodeTerm_state.keys_foldl_insert_subset_of_fst_mem _ D_keys_sub
            (fun p hp => vs_sub_St₁_used p.1 (List.of_mem_zip hp).1)
        mspec P_ih (E := E') (Λ := St₂.types) (n := St₂.env.freshvarsc)
          (used := St₂.env.usedVars) (α := .bool) (decl := decl ++ ΔD) typP vars_used_P_St₂
          Λ_inv_P hP_bv_nodup
        rename_i out_P
        obtain ⟨P_enc, σP⟩ := out_P
        mrename_i pre
        mintro ∀St₃
        mpure pre
        obtain ⟨⟨P_used_sub, P_Λ_sub, P_keys_sub, P_cov, P_state_fv_sub, P_preserves⟩,
          ΔP, P_decl_eq, P_specb, P_fv_sub⟩ := pre
        split
        · -- `encodeTerm P` returned a boolean
          rename_i heqP
          obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ heqP
          mspec (Std.Do.Triple.and (SMT.freshVarList αs')
            (SMT.freshVarList_spec αs' (Γ := St₃.types) (n := St₃.env.freshvarsc)
              (used := St₃.env.usedVars))
            (SMT.freshVarList_decls αs' (decl := decl ++ ΔD ++ ΔP)))
          rename_i xs
          mrename_i pre
          mintro ∀St₄
          mpure pre
          obtain ⟨⟨xs_len, xs_nodup, xs_not_used, xs_not_Γ, St₄_fvc, St₄_used,
            St₄_types⟩, St₄_decl⟩ := pre
          have St₃_sub_St₄_types : St₃.types ⊆ St₄.types := by
            rw [St₄_types]
            refine AList.subset_foldl_insert' ?_ ?_
            · intro p hp
              exact xs_not_Γ p.1 (List.mem_fst_of_mem_zip hp)
            · exact List.nodup_map_fst_of_nodup_zip xs_nodup
          have St₃_sub_St₄_used : St₃.env.usedVars ⊆ St₄.env.usedVars := by
            rw [St₄_used]
            exact fun v hv => List.mem_append_right _ hv
          have xs_sub_St₄_types : ∀ x ∈ xs, x ∈ St₄.types := by
            intro x hx
            rw [St₄_types]
            apply encodeTerm_state.mem_keys_foldl_insert_of_fst
            have hmap : (xs.zip αs').map Prod.fst = xs :=
              List.map_fst_zip (le_of_eq xs_len)
            rw [hmap]; exact hx
          have St₁_sub_St₂ : St₁.types ⊆ St₂.types := by
            rw [St₂_types]
            refine AList.subset_foldl_insert' ?_ ?_
            · intro p hp
              exact vs_disj_St₁ p.1 (List.mem_fst_of_mem_zip hp)
            · exact List.nodup_map_fst_of_nodup_zip vs_nodup
          have St₁_sub_St₄ : St₁.types ⊆ St₄.types :=
            AList.subset_trans (AList.subset_trans St₁_sub_St₂ P_Λ_sub) St₃_sub_St₄_types
          have St₄_keys_sub : AList.keys St₄.types ⊆ St₄.env.usedVars := by
            rw [St₄_types, St₄_used]
            refine encodeTerm_state.keys_foldl_insert_subset_of_fst_mem _ ?_ ?_
            · exact fun v hv => List.mem_append_right _ (P_keys_sub hv)
            · intro p hp
              exact List.mem_append_left _ (List.mem_reverse.mpr
                (List.mem_fst_of_mem_zip hp))
          rw [αs'_toProdl_eq]
          mspec (Std.Do.Triple.and
            (castApp (D_enc, α'.fun β'.option) ((List.map SMT.Term.var xs).toPairl, α'))
            (castApp_state D_enc ((List.map SMT.Term.var xs).toPairl) (α'.fun β'.option)
              α' (Λ := St₄.types) (n := St₄.env.freshvarsc)
              (used := St₄.env.usedVars) (X := B.Term.vars (B.Term.collect vs D P)))
            (castApp_decl_domEq D_enc ((List.map SMT.Term.var xs).toPairl) α' β'
              (Λ := St₄.types) (n := St₄.env.freshvarsc)
              (used := St₄.env.usedVars) (decl := decl ++ ΔD ++ ΔP)))
          case pre =>
            mpure_intro
            refine ⟨⟨rfl, rfl, St₄_keys_sub, rfl, ?_, ?_⟩,
              rfl, rfl, St₄_keys_sub, rfl, St₄_decl⟩
            · intro v hv
              rcases List.mem_union_iff.mp (D_state_fv_sub hv) with hk | hb
              · exact List.mem_union_iff.mpr (Or.inl (AList.mem_keys.mp (AList.mem_of_subset
                  St₁_sub_St₄ (AList.mem_keys.mpr hk))))
              · exact List.mem_union_iff.mpr (Or.inr (hvars_D_sub hb))
            · intro v hv
              exact List.mem_union_iff.mpr (Or.inl (AList.mem_keys.mp (xs_sub_St₄_types v
                (encodeTerm_state.fv_toPairl_map_var_subset xs v hv))))
          case post.success =>
            rename_i out_ca
            obtain ⟨Dxs, σDxs⟩ := out_ca
            mrename_i pre
            mintro ∀St₅
            mpure pre
            obtain ⟨⟨ca_le, ca_Λ_sub, ca_used_sub, ca_keys_sub, ca_fv_sub₀,
              ca_preserves⟩, Δca, ca_decl_eq, ca_specb, ca_fv_decl_sub⟩ := pre
            mspec Std.Do.Spec.pure
            mpure_intro
            have St₀_sub_St₅ : St₀.types ⊆ St₅.types :=
              AList.subset_trans (AList.subset_trans D_Λ_sub St₁_sub_St₄) ca_Λ_sub
            have St₁_used_sub_St₃ : St₁.env.usedVars ⊆ St₃.env.usedVars := by
              rw [← St₂_used_eq]; exact P_used_sub
            have used_sub_St₃ : used ⊆ St₃.env.usedVars :=
              fun v hv => St₁_used_sub_St₃ (D_used_sub hv)
            have used_sub_St₅ : used ⊆ St₅.env.usedVars :=
              fun v hv => ca_used_sub (St₃_sub_St₄_used (used_sub_St₃ hv))
            have St₃_keys_sub_St₅ : AList.keys St₃.types ⊆ AList.keys St₅.types := by
              intro v hv
              exact AList.mem_keys.mp (AList.mem_of_subset
                (AList.subset_trans St₃_sub_St₄_types ca_Λ_sub) (AList.mem_keys.mpr hv))
            have xs_not_used_orig : ∀ x ∈ xs, x ∉ used := by
              intro x hx hx_used
              exact xs_not_used x hx (used_sub_St₃ hx_used)
            have hdv : declVars (ΔD ++ ΔP ++ Δca)
                = declVars ΔD ++ declVars ΔP ++ declVars Δca := by
              rw [declVars_append, declVars_append]
            have Dxs_fv : ∀ w ∈ SMT.fv Dxs, w ∉ xs →
                w ∈ B.Term.vars (B.Term.collect vs D P) ∪ declVars (ΔD ++ ΔP ++ Δca) := by
              intro w hw hw_xs
              rw [hdv]
              rcases List.mem_union_iff.mp (ca_fv_decl_sub hw) with h | h
              · rcases List.mem_union_iff.mp h with hD | hpairl
                · rcases List.mem_union_iff.mp (D_fv_sub hD) with hbd | hdd
                  · exact List.mem_union_iff.mpr (.inl (hvars_D_sub hbd))
                  · exact List.mem_union_iff.mpr (.inr (List.mem_append_left _
                      (List.mem_append_left _ hdd)))
                · exact absurd (encodeTerm_state.fv_toPairl_map_var_subset xs w hpairl) hw_xs
              · exact List.mem_union_iff.mpr (.inr (List.mem_append_right _ h))
            refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ΔD ++ ΔP ++ Δca,
              by rw [ca_decl_eq]; simp only [List.append_assoc], ?_, ?_⟩
            · exact used_sub_St₅
            · exact St₀_sub_St₅
            · exact ca_keys_sub
            · intro v hv
              rw [B.fv, List.mem_append] at hv
              rcases hv with hv | hv
              · exact ca_used_sub (St₃_sub_St₄_used (St₁_used_sub_St₃ (D_cov v hv)))
              · exact ca_used_sub (St₃_sub_St₄_used (P_cov v (List.mem_removeAll_iff.mp hv).1))
            · intro v hv
              simp only [SMT.fv, List.mem_removeAll_iff, List.mem_append, noneCast,
                List.not_mem_nil, or_false] at hv
              obtain ⟨hv_body, hv_not_xs⟩ := hv
              rcases hv_body with hv_subst | hv_dxs
              · rcases SMT_mem_fv_substList hv_subst with hvP | ⟨t, ht, hvt⟩
                · rcases List.mem_union_iff.mp (P_state_fv_sub hvP) with hk | hb
                  · exact List.mem_union_iff.mpr (.inl (St₃_keys_sub_St₅ hk))
                  · exact List.mem_union_iff.mpr (.inr (hvars_P_sub hb))
                · rw [List.concat_eq_append] at ht
                  rcases List.mem_append.mp ht with ht_xs | ht_eq
                  · rw [List.mem_map] at ht_xs
                    obtain ⟨x, hx, rfl⟩ := ht_xs
                    simp only [SMT.fv, List.mem_singleton] at hvt
                    exact absurd (hvt ▸ hx) hv_not_xs
                  · rw [List.mem_singleton] at ht_eq
                    subst ht_eq
                    exact ca_fv_sub₀ hvt
              · exact ca_fv_sub₀ hv_dxs
            · intro v v_used v_notMem_St₀ v_notMem_vars
              obtain ⟨v_notMem_vars_D, v_notMem_vars_P, hv_not_vs⟩ :=
                B.Term.notMem_vars_collect.mp v_notMem_vars
              have v_notMem_St₁ := D_preserves v v_used v_notMem_St₀ v_notMem_vars_D
              have v_notMem_St₂ : v ∉ St₂.types := by
                rw [St₂_types]
                intro h
                refine v_notMem_St₁ (AList.mem_of_mem_foldl_insert' h ?_)
                intro hmem
                rw [List.mem_map] at hmem
                obtain ⟨⟨a, b⟩, hab, rfl⟩ := hmem
                exact hv_not_vs (List.of_mem_zip hab).1
              have v_St₂_used : v ∈ St₂.env.usedVars := by
                rw [St₂_used_eq]; exact D_used_sub v_used
              have v_notMem_St₃ : v ∉ St₃.types :=
                P_preserves v v_St₂_used v_notMem_St₂ v_notMem_vars_P
              have v_notMem_St₄ : v ∉ St₄.types := by
                rw [St₄_types]
                intro h
                refine v_notMem_St₃ (AList.mem_of_mem_foldl_insert' h ?_)
                intro hmem
                rw [List.mem_map] at hmem
                obtain ⟨⟨a, b⟩, hab, rfl⟩ := hmem
                exact xs_not_used_orig a (List.of_mem_zip hab).1 v_used
              exact ca_preserves v (St₃_sub_St₄_used (used_sub_St₃ v_used)) v_notMem_St₄
            · intro b hb
              rw [specBodies_append, List.mem_append] at hb
              rcases hb with hb | hb
              · rw [specBodies_append, List.mem_append] at hb
                rcases hb with hb | hb
                · exact specBody_mono hvars_D_sub
                    (by rw [declVars_append, declVars_append]
                        exact List.Subset.trans (List.subset_append_left ..)
                          (List.subset_append_left ..))
                    (D_specb b hb)
                · exact specBody_mono hvars_P_sub
                    (by rw [declVars_append, declVars_append]
                        exact List.Subset.trans (List.subset_append_right ..)
                          (List.subset_append_left ..))
                    (P_specb b hb)
              · intro w hw
                have hw' := ca_specb b hb hw
                rw [declVars_append, declVars_append]
                rcases List.mem_union_iff.mp hw' with hD | hdca
                · rcases List.mem_union_iff.mp (D_fv_sub hD) with hbd | hdd
                  · exact List.mem_union_iff.mpr (.inl (hvars_D_sub hbd))
                  · exact List.mem_union_iff.mpr (.inr (List.mem_append_left _
                      (List.mem_append_left _ hdd)))
                · exact List.mem_union_iff.mpr (.inr (List.mem_append_right _ hdca))
            · intro v hv
              simp only [SMT.fv, List.mem_removeAll_iff, List.mem_append, noneCast,
                List.not_mem_nil, or_false] at hv
              obtain ⟨hv_body, hv_not_xs⟩ := hv
              rcases hv_body with hv_subst | hv_dxs
              · rcases SMT_mem_fv_substList hv_subst with hvP | ⟨t, ht, hvt⟩
                · by_cases hvs : v ∈ vs
                  · have hex : ∃ t ∈ (List.map SMT.Term.var xs).concat Dxs, v ∈ SMT.fv t := by
                      by_contra hcon
                      push_neg at hcon
                      refine SMT_not_mem_fv_substList_of_mem_vars ?_ hvs hcon hv_subst
                      have hvs_pos : 0 < vs.length := List.length_pos_iff.mpr vs_nemp
                      rw [List.concat_eq_append, List.length_append, List.length_map,
                        List.length_singleton, xs_len, αs'_len_eq]
                      omega
                    obtain ⟨t, ht, hvt⟩ := hex
                    rw [List.concat_eq_append] at ht
                    rcases List.mem_append.mp ht with ht_xs | ht_dxs
                    · rw [List.mem_map] at ht_xs
                      obtain ⟨x, hx, rfl⟩ := ht_xs
                      simp only [SMT.fv, List.mem_singleton] at hvt
                      exact absurd (hvt ▸ hx) hv_not_xs
                    · rw [List.mem_singleton] at ht_dxs
                      subst ht_dxs
                      exact Dxs_fv v hvt hv_not_xs
                  · rcases List.mem_union_iff.mp (P_fv_sub hvP) with hfv | hdvP
                    · exact List.mem_union_iff.mpr (.inl (hvars_P_sub hfv))
                    · rw [declVars_append, declVars_append]
                      exact List.mem_union_iff.mpr (.inr (List.mem_append_left _
                        (List.mem_append_right _ hdvP)))
                · rw [List.concat_eq_append] at ht
                  rcases List.mem_append.mp ht with ht_xs | ht_dxs
                  · rw [List.mem_map] at ht_xs
                    obtain ⟨x, hx, rfl⟩ := ht_xs
                    simp only [SMT.fv, List.mem_singleton] at hvt
                    exact absurd (hvt ▸ hx) hv_not_xs
                  · rw [List.mem_singleton] at ht_dxs
                    subst ht_dxs
                    exact Dxs_fv v hvt hv_not_xs
              · exact Dxs_fv v hv_dxs hv_not_xs
        · exact wp_bind_throw _ _ _ _
      · -- arity mismatch: throw
        mvcgen
    · -- set-`D` arm
      rename_i τ' heq
      mspec (Std.Do.Triple.and _
        (SMT.addToContext_forIn_spec (vs.zip (τ'.fromProdl (vs.length - 1)))
          (Γ := St₁.types) (n := St₁.env.freshvarsc) (used := St₁.env.usedVars))
        (SMT.addToContext_forIn_decls (vs.zip (τ'.fromProdl (vs.length - 1)))
          (decl := decl ++ ΔD)))
      mrename_i pre
      mintro ∀St₂
      mpure pre
      obtain ⟨⟨St₂_types, St₂_fvc, St₂_used⟩, St₂_decl⟩ := pre
      set E' : B.Env := { E with context := vs.zipToAList αs ∪ E.context } with E'_def
      conv in encodeTerm P E => rw [encodeTerm_state.encodeTerm_env_irrel P E E' rfl]
      have St₁_sub_St₂_used : St₁.env.usedVars ⊆ St₂.env.usedVars := by
        rw [St₂_used]
        exact fun v hv => encodeTerm_state.mem_foldl_cons_of_mem _ _ hv
      have vars_used_P_St₂ : ∀ v ∈ P.vars, v ∈ St₂.env.usedVars :=
        fun v hv => St₁_sub_St₂_used (D_used_sub (vars_used_P v hv))
      have vs_disj_St₁ : ∀ v ∈ vs, v ∉ St₁.types := by
        intro v hv
        have vs_not_D_fv : v ∉ B.fv D := fun hv_fv =>
          vs_Γ_disj v hv (AList.lookup_isSome.mp (B.Typing.mem_context_of_mem_fv typ_D hv_fv))
        have hv_vars_D : v ∉ B.Term.vars D :=
          B.Term.notMem_vars_iff.mpr ⟨vs_not_D_fv, by
            have h := bv_nodup
            simp only [B.bv] at h
            rw [List.nodup_append, List.nodup_append] at h
            intro h_bv
            exact h.1.2.2 v hv v h_bv rfl⟩
        apply D_preserves v (vars_used_vs v hv) _ hv_vars_D
        intro hv_St₀
        have hv_coll : v ∈ (B.Term.collect vs D P).vars := by
          unfold B.Term.vars; rw [List.mem_union_iff]; right
          simp only [B.bv, List.mem_append]; exact .inl (.inl hv)
        exact vs_Γ_disj v hv (Λ_inv v hv_coll hv_St₀)
      have Λ_inv_P : ∀ v ∈ P.vars, v ∈ St₂.types → v ∈ E'.context := by
        intro v v_in_P_vars v_in_St₂_types
        rw [E'_def]
        show v ∈ vs.zipToAList αs ∪ E.context
        by_cases v_in_vs : v ∈ vs
        · exact AList.mem_union.mpr (.inl (AList.mem_zipToAList_of_mem vs_nodup vs_αs_len v_in_vs))
        · have v_in_St₁ : v ∈ St₁.types := by
            rw [St₂_types] at v_in_St₂_types
            refine AList.mem_of_mem_foldl_insert' v_in_St₂_types ?_
            intro h
            rw [List.mem_map] at h
            obtain ⟨⟨a, b⟩, hab, rfl⟩ := h
            exact v_in_vs (List.of_mem_zip hab).1
          have v_used : v ∈ used := vars_used_P v v_in_P_vars
          by_cases v_St₀ : v ∈ St₀.types
          · have v_coll : v ∈ (B.Term.collect vs D P).vars := by
              unfold B.Term.vars at v_in_P_vars ⊢
              rw [List.mem_union_iff]
              rcases List.mem_union_iff.mp v_in_P_vars with h_fv | h_bv
              · exact .inl (by
                  simp only [B.fv, List.mem_append]
                  exact .inr (List.mem_removeAll_iff.mpr ⟨h_fv, v_in_vs⟩))
              · exact .inr (by
                  simp only [B.bv, List.mem_append]
                  exact .inr h_bv)
            exact AList.mem_union.mpr (.inr (Λ_inv v v_coll v_St₀))
          · have v_vars_D : v ∈ B.Term.vars D := by
              by_contra h
              exact absurd v_in_St₁ (D_preserves v v_used v_St₀ h)
            rcases B.Term.mem_vars_iff.mp v_vars_D with h | h
            · exact AList.mem_union.mpr (.inr (AList.lookup_isSome.mp
                (B.Typing.mem_context_of_mem_fv typ_D h)))
            · rcases B.Term.mem_vars_iff.mp v_in_P_vars with hv_fv_P | hv_bv_P
              · have h_in_E' : ((vs.zipToAList αs ∪ E.context).lookup v).isSome :=
                  B.Typing.mem_context_of_mem_fv typP hv_fv_P
                exact AList.lookup_isSome.mp h_in_E'
              · exfalso
                have hbn := bv_nodup
                simp only [B.bv] at hbn
                rw [List.nodup_append] at hbn
                have hin : v ∈ vs ++ B.bv D := List.mem_append.mpr (.inr h)
                exact hbn.2.2 v hin v hv_bv_P rfl
      have St₂_keys_sub : AList.keys St₂.types ⊆ St₂.env.usedVars := by
        rw [St₂_types, St₂_used]
        exact encodeTerm_state.keys_foldl_insert_subset_foldl_cons _ D_keys_sub
      mspec P_ih (E := E') (Λ := St₂.types) (n := St₂.env.freshvarsc)
        (used := St₂.env.usedVars) (α := .bool) (decl := decl ++ ΔD) typP vars_used_P_St₂
        Λ_inv_P hP_bv_nodup
      rename_i out_P
      obtain ⟨P_enc, σP⟩ := out_P
      mrename_i pre
      mintro ∀St₃
      mpure pre
      obtain ⟨⟨P_used_sub, P_Λ_sub, P_keys_sub, P_cov, P_state_fv_sub, P_preserves⟩,
        ΔP, P_decl_eq, P_specb, P_fv_sub⟩ := pre
      split
      · -- `encodeTerm P` returned a boolean
        rename_i heqP
        obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ heqP
        mspec (Std.Do.Triple.and (SMT.freshVar τ')
          (SMT.freshVar_spec (Γ := St₃.types) (τ := τ') (n := St₃.env.freshvarsc)
            (used := St₃.env.usedVars))
          (SMT.freshVar_decls (τ := τ') (decl := St₃.env.declarations)))
        case post.success z =>
        mrename_i pre4
        mintro ∀St₄
        mpure pre4
        obtain ⟨⟨St₄_types, z_fresh, St₄_fvc, St₄_used, z_not_used⟩, St₄_decl⟩ := pre4
        mspec (Std.Do.Triple.and (SMT.eraseFromContext z)
          (SMT.eraseFromContext_spec (v := z) (Γ := St₄.types) (n := St₄.env.freshvarsc)
            (used := St₄.env.usedVars))
          (SMT.eraseFromContext_decls (v := z) (decl := St₄.env.declarations)))
        mrename_i pre5
        mintro ∀St₅
        mpure pre5
        obtain ⟨⟨St₅_types, St₅_fvc, St₅_used⟩, St₅_decl⟩ := pre5
        mspec Std.Do.Spec.pure
        mpure_intro
        have St₁_sub_St₂ : St₁.types ⊆ St₂.types := by
          rw [St₂_types]
          refine AList.subset_foldl_insert' ?_ ?_
          · intro p hp
            exact vs_disj_St₁ p.1 (List.mem_fst_of_mem_zip hp)
          · exact List.nodup_map_fst_of_nodup_zip vs_nodup
        have St₀_sub_St₃ : St₀.types ⊆ St₃.types :=
          AList.subset_trans (AList.subset_trans D_Λ_sub St₁_sub_St₂) P_Λ_sub
        have St₁_sub_St₃ : St₁.types ⊆ St₃.types :=
          AList.subset_trans St₁_sub_St₂ P_Λ_sub
        have St₃_used_chain : St₃.env.usedVars ⊆ St₅.env.usedVars := by
          rw [St₅_used, St₄_used]; exact fun v hv => List.mem_cons_of_mem _ hv
        have used_sub_St₃ : used ⊆ St₃.env.usedVars :=
          fun v hv => P_used_sub (St₁_sub_St₂_used (D_used_sub hv))
        have z_not_St₃ : z ∉ St₃.types := z_fresh
        have toDestPair_fv : ∀ t ∈ toDestPair vs (SMT.Term.var z),
            ∀ w ∈ SMT.fv t, w = z := by
          intro t ht w hw
          exact SMT_fv_toDestPair_subset ht hw
        have St₅_types_eq : St₅.types = St₃.types := by
          rw [St₅_types, St₄_types]
          exact encodeTerm_state.erase_insert_self z_not_St₃
        refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ΔD ++ ΔP,
          by rw [St₅_decl, St₄_decl, P_decl_eq, List.append_assoc], ?_, ?_⟩
        · exact fun v hv => St₃_used_chain (used_sub_St₃ hv)
        · rw [St₅_types_eq]; exact St₀_sub_St₃
        · rw [St₅_types_eq]
          exact fun v hv => St₃_used_chain (P_keys_sub hv)
        · intro v hv
          apply St₃_used_chain
          rw [B.fv, List.mem_append] at hv
          rcases hv with hv | hv
          · exact P_used_sub (St₁_sub_St₂_used (D_cov v hv))
          · exact P_cov v (List.mem_removeAll_iff.mp hv).1
        · intro v hv
          simp only [SMT.fv, List.mem_removeAll_iff, List.mem_append, List.mem_singleton,
            List.not_mem_nil, or_false] at hv
          obtain ⟨hv_body, hv_ne_z⟩ := hv
          rw [St₅_types_eq]
          rcases hv_body with (hvD | hvz1) | hvsubst
          · rcases List.mem_union_iff.mp (D_state_fv_sub hvD) with hk | hb
            · exact List.mem_union_iff.mpr (.inl (AList.mem_keys.mp (AList.mem_of_subset
                St₁_sub_St₃ (AList.mem_keys.mpr hk))))
            · exact List.mem_union_iff.mpr (.inr (hvars_D_sub hb))
          · exact absurd hvz1 hv_ne_z
          · rcases SMT_mem_fv_substList hvsubst with hvP | ⟨t, ht, hvt⟩
            · rcases List.mem_union_iff.mp (P_state_fv_sub hvP) with hk | hb
              · exact List.mem_union_iff.mpr (.inl hk)
              · exact List.mem_union_iff.mpr (.inr (hvars_P_sub hb))
            · exact absurd (toDestPair_fv t ht v hvt) hv_ne_z
        · intro v v_used v_notMem_St₀ v_notMem_vars
          obtain ⟨v_notMem_vars_D, v_notMem_vars_P, hv_not_vs⟩ :=
            B.Term.notMem_vars_collect.mp v_notMem_vars
          rw [St₅_types_eq]
          intro v_in_St₃
          have v_notMem_St₁ := D_preserves v v_used v_notMem_St₀ v_notMem_vars_D
          have v_notMem_St₂ : v ∉ St₂.types := by
            rw [St₂_types]
            intro h
            refine v_notMem_St₁ (AList.mem_of_mem_foldl_insert' h ?_)
            intro hmem
            rw [List.mem_map] at hmem
            obtain ⟨⟨a, b⟩, hab, rfl⟩ := hmem
            exact hv_not_vs (List.of_mem_zip hab).1
          exact P_preserves v (St₁_sub_St₂_used (D_used_sub v_used))
            v_notMem_St₂ v_notMem_vars_P v_in_St₃
        · intro b hb
          rw [specBodies_append, List.mem_append] at hb
          rcases hb with hb | hb
          · exact specBody_mono hvars_D_sub
              (declVars_append .. ▸ List.subset_append_left ..) (D_specb b hb)
          · exact specBody_mono hvars_P_sub
              (declVars_append .. ▸ List.subset_append_right ..) (P_specb b hb)
        · intro v hv
          simp only [SMT.fv, List.mem_removeAll_iff, List.mem_append, List.mem_singleton,
            List.not_mem_nil, or_false] at hv
          obtain ⟨hv_body, hv_ne_z⟩ := hv
          rw [declVars_append]
          rcases hv_body with (hvD | hvz1) | hvsubst
          · rcases List.mem_union_iff.mp (D_fv_sub hvD) with h | h
            · exact List.mem_union_iff.mpr (.inl (hvars_D_sub h))
            · exact List.mem_union_iff.mpr (.inr (List.mem_append_left _ h))
          · exact absurd hvz1 hv_ne_z
          · rcases SMT_mem_fv_substList hvsubst with hvP | ⟨t, ht, hvt⟩
            · rcases List.mem_union_iff.mp (P_fv_sub hvP) with hfv | hdv
              · exact List.mem_union_iff.mpr (.inl (hvars_P_sub hfv))
              · exact List.mem_union_iff.mpr (.inr (List.mem_append_right _ hdv))
            · exact absurd (toDestPair_fv t ht v hvt) hv_ne_z
      · -- `encodeTerm P` did not return a boolean: throw
        exact wp_bind_throw _ _ _ _
    · -- throw arm
      mvcgen
  | all vs D P D_ih P_ih =>
    mintro pre ∀St₀
    mpure pre
    obtain ⟨rfl, rfl, St₀_sub, St₀_used_eq, St₀_decl_eq⟩ := pre
    rw [encodeTerm]
    obtain ⟨rfl, vs_nemp, αs, Ds, vs_αs_len, vs_Ds_len, D_eq, vs_nodup, typDs, typP,
      vs_Γ_disj⟩ := B.Typing.allE typ_t
    set τ := αs.reduce (· ×ᴮ ·) (by simpa [vs_αs_len, ← List.length_pos_iff] using vs_nemp)
      with τ_def
    have typ_D : E.context ⊢ᴮ D : .set τ := by
      rw [D_eq]
      exact encodeTerm_state.typing_reduce_cprod E.context _ _ typDs
        (by simpa [vs_Ds_len, ← List.length_pos_iff] using vs_nemp)
        (by simpa [vs_αs_len, ← List.length_pos_iff] using vs_nemp)
    have hD_bv_nodup : (B.bv D).Nodup := by
      have h := bv_nodup
      simp only [B.bv] at h
      rw [List.nodup_append, List.nodup_append] at h
      exact h.1.2.1
    have hP_bv_nodup : (B.bv P).Nodup := by
      have h := bv_nodup
      simp only [B.bv] at h
      rw [List.nodup_append] at h
      exact h.2.1
    have vars_used_D : ∀ v ∈ D.vars, v ∈ used := by
      intro v hv
      apply vars_used v
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.append_assoc,
        List.mem_append, List.mem_removeAll_iff] at hv ⊢
      rcases hv with hv | hv
      · exact .inl (.inl hv)
      · exact .inr (.inr (.inl hv))
    have vars_used_vs : ∀ v ∈ vs, v ∈ used := by
      intro v hv
      apply vars_used v
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.append_assoc,
        List.mem_append] at hv ⊢
      exact .inr (.inl hv)
    have vars_used_P : ∀ v ∈ P.vars, v ∈ used := by
      intro v hv
      by_cases hvs : v ∈ vs
      · exact vars_used_vs v hvs
      · apply vars_used v
        simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.append_assoc,
          List.mem_append, List.mem_removeAll_iff] at hv ⊢
        rcases hv with hv | hv
        · exact .inl (.inr ⟨hv, hvs⟩)
        · exact .inr (.inr (.inr hv))
    have Λ_inv_D : ∀ v ∈ D.vars, v ∈ St₀.types → v ∈ E.context := by
      intro v hv hSt₀
      apply Λ_inv v _ hSt₀
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.append_assoc,
        List.mem_append, List.mem_removeAll_iff] at hv ⊢
      rcases hv with hv | hv
      · exact .inl (.inl hv)
      · exact .inr (.inr (.inl hv))
    have hvars_D_sub : B.Term.vars D ⊆ B.Term.vars (B.Term.all vs D P) := by
      intro v hv
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.append_assoc,
        List.mem_append, List.mem_removeAll_iff] at hv ⊢
      rcases hv with hv | hv
      · exact .inl (.inl hv)
      · exact .inr (.inr (.inl hv))
    have hvars_P_sub : B.Term.vars P ⊆ B.Term.vars (B.Term.all vs D P) := by
      intro v hv
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.append_assoc,
        List.mem_append, List.mem_removeAll_iff] at hv ⊢
      rcases hv with hvP | hvP
      · by_cases hvs : v ∈ vs
        · exact .inr (.inl hvs)
        · exact .inl (.inr ⟨hvP, hvs⟩)
      · exact .inr (.inr (.inr hvP))
    have hvars_vs_sub : ∀ v ∈ vs, v ∈ B.Term.vars (B.Term.all vs D P) := by
      intro v hv
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.append_assoc,
        List.mem_append]
      exact .inr (.inl hv)
    mspec D_ih (E := E) (Λ := St₀.types) (n := St₀.env.freshvarsc) (used := used)
      (α := .set τ) (decl := decl) typ_D vars_used_D Λ_inv_D hD_bv_nodup
    rename_i out_D
    obtain ⟨D_enc, τD⟩ := out_D
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨⟨D_used_sub, D_Λ_sub, D_keys_sub, D_cov, D_state_fv_sub, D_preserves⟩,
      ΔD, D_decl_eq, D_specb, D_fv_sub⟩ := pre
    split
    · -- D-arm 1: `D` encodes to a set `.fun τ' .bool`
      rename_i τ' heq
      split
      · -- arities match
        rename_i hlen
        set tmp_τs := τ'.fromProdl (vs.length - 1) with tmp_τs_def
        mspec (Std.Do.Triple.and _
          (encodeTerm_state.mapFinIdxM_all_state vs E.flags tmp_τs hlen
            (Γ := St₁.types) (n := St₁.env.freshvarsc) (used := St₁.env.usedVars))
          (encodeTerm_state.mapFinIdxM_all_decls vs E.flags tmp_τs hlen
            (decl := decl ++ ΔD)))
        rename_i τs
        mrename_i preM
        mintro ∀StM
        mpure preM
        obtain ⟨⟨StM_types, StM_fvc, StM_used, τs_len⟩, StM_decl⟩ := preM
        mspec (Std.Do.Triple.and _
          (SMT.addToContext_forIn_spec (vs.zip τs)
            (Γ := StM.types) (n := StM.env.freshvarsc) (used := StM.env.usedVars))
          (SMT.addToContext_forIn_decls (vs.zip τs)
            (decl := decl ++ ΔD)))
        mrename_i pre
        mintro ∀St₂
        mpure pre
        obtain ⟨⟨St₂_types, St₂_fvc, St₂_used⟩, St₂_decl⟩ := pre
        rw [StM_types] at St₂_types
        rw [StM_used] at St₂_used
        rw [StM_fvc] at St₂_fvc
        set E' : B.Env := { E with context := vs.zipToAList αs ∪ E.context } with E'_def
        conv in encodeTerm P E => rw [encodeTerm_state.encodeTerm_env_irrel P E E' rfl]
        mspec Std.Do.Spec.get_StateT
        mspec Std.Do.Spec.get_StateT
        mspec Std.Do.Spec.get_StateT
        have St₁_sub_St₂_used : St₁.env.usedVars ⊆ St₂.env.usedVars := by
          rw [St₂_used]
          exact fun v hv => encodeTerm_state.mem_foldl_cons_of_mem _ _ hv
        have vars_used_P_St₂ : ∀ v ∈ P.vars, v ∈ St₂.env.usedVars :=
          fun v hv => St₁_sub_St₂_used (D_used_sub (vars_used_P v hv))
        have vs_disj_St₁ : ∀ v ∈ vs, v ∉ St₁.types := by
          intro v hv
          have vs_not_D_fv : v ∉ B.fv D := fun hv_fv =>
            vs_Γ_disj v hv (AList.lookup_isSome.mp (B.Typing.mem_context_of_mem_fv typ_D hv_fv))
          have hv_vars_D : v ∉ B.Term.vars D :=
            B.Term.notMem_vars_iff.mpr ⟨vs_not_D_fv, by
              have h := bv_nodup
              simp only [B.bv] at h
              rw [List.nodup_append, List.nodup_append] at h
              intro h_bv
              exact h.1.2.2 v hv v h_bv rfl⟩
          apply D_preserves v (vars_used_vs v hv) _ hv_vars_D
          intro hv_St₀
          exact vs_Γ_disj v hv (Λ_inv v (hvars_vs_sub v hv) hv_St₀)
        have Λ_inv_P : ∀ v ∈ P.vars, v ∈ St₂.types → v ∈ E'.context := by
          intro v v_in_P_vars v_in_St₂_types
          rw [E'_def]
          show v ∈ vs.zipToAList αs ∪ E.context
          by_cases v_in_vs : v ∈ vs
          · exact AList.mem_union.mpr (.inl (AList.mem_zipToAList_of_mem vs_nodup vs_αs_len v_in_vs))
          · have v_in_St₁ : v ∈ St₁.types := by
              rw [St₂_types] at v_in_St₂_types
              refine AList.mem_of_mem_foldl_insert' v_in_St₂_types ?_
              intro h
              rw [List.mem_map] at h
              obtain ⟨⟨a, b⟩, hab, rfl⟩ := h
              exact v_in_vs (List.of_mem_zip hab).1
            have v_used : v ∈ used := vars_used_P v v_in_P_vars
            by_cases v_St₀ : v ∈ St₀.types
            · have v_all : v ∈ (B.Term.all vs D P).vars := by
                unfold B.Term.vars at v_in_P_vars ⊢
                rw [List.mem_union_iff]
                rcases List.mem_union_iff.mp v_in_P_vars with h_fv | h_bv
                · exact .inl (by
                    simp only [B.fv, List.mem_append]
                    exact .inr (List.mem_removeAll_iff.mpr ⟨h_fv, v_in_vs⟩))
                · exact .inr (by
                    simp only [B.bv, List.mem_append]
                    exact .inr h_bv)
              exact AList.mem_union.mpr (.inr (Λ_inv v v_all v_St₀))
            · have v_vars_D : v ∈ B.Term.vars D := by
                by_contra h
                exact absurd v_in_St₁ (D_preserves v v_used v_St₀ h)
              rcases B.Term.mem_vars_iff.mp v_vars_D with h | h
              · exact AList.mem_union.mpr (.inr (AList.lookup_isSome.mp
                  (B.Typing.mem_context_of_mem_fv typ_D h)))
              · rcases B.Term.mem_vars_iff.mp v_in_P_vars with hv_fv_P | hv_bv_P
                · have h_in_E' : ((vs.zipToAList αs ∪ E.context).lookup v).isSome :=
                    B.Typing.mem_context_of_mem_fv typP hv_fv_P
                  exact AList.lookup_isSome.mp h_in_E'
                · exfalso
                  have hbn := bv_nodup
                  simp only [B.bv] at hbn
                  rw [List.nodup_append] at hbn
                  have hin : v ∈ vs ++ B.bv D := List.mem_append.mpr (.inr h)
                  exact hbn.2.2 v hin v hv_bv_P rfl
        have St₂_keys_sub : AList.keys St₂.types ⊆ St₂.env.usedVars := by
          rw [St₂_types, St₂_used]
          exact encodeTerm_state.keys_foldl_insert_subset_foldl_cons _ D_keys_sub
        mspec P_ih (E := E') (Λ := St₂.types) (n := St₂.env.freshvarsc)
          (used := St₂.env.usedVars) (α := .bool) (decl := decl ++ ΔD) typP vars_used_P_St₂
          Λ_inv_P hP_bv_nodup
        rename_i out_P
        obtain ⟨P_enc, σP⟩ := out_P
        mrename_i pre
        mintro ∀St₇
        mpure pre
        obtain ⟨⟨P_used_sub, P_Λ_sub, P_keys_sub, P_cov, P_state_fv_sub, P_preserves⟩,
          ΔP, P_decl_eq, P_specb, P_fv_sub⟩ := pre
        split
        · -- `encodeTerm P` returned a boolean
          rename_i heqP
          obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ heqP
          mspec (Std.Do.Triple.and (SMT.freshVarList τs)
            (SMT.freshVarList_spec τs (Γ := St₇.types) (n := St₇.env.freshvarsc)
              (used := St₇.env.usedVars))
            (SMT.freshVarList_decls τs (decl := decl ++ ΔD ++ ΔP)))
          rename_i zs
          mrename_i pre8
          mintro ∀St₈
          mpure pre8
          obtain ⟨⟨zs_len, zs_nodup, zs_not_used, zs_not_Γ, St₈_fvc, St₈_used,
            St₈_types⟩, St₈_decl⟩ := pre8
          have St₇_sub_St₈ : St₇.types ⊆ St₈.types := by
            rw [St₈_types]
            refine AList.subset_foldl_insert' ?_ ?_
            · intro p hp
              exact zs_not_Γ p.1 (List.mem_fst_of_mem_zip hp)
            · exact List.nodup_map_fst_of_nodup_zip zs_nodup
          have St₈_keys_sub : AList.keys St₈.types ⊆ St₈.env.usedVars := by
            rw [St₈_types, St₈_used]
            refine encodeTerm_state.keys_foldl_insert_subset_of_fst_mem _ ?_ ?_
            · exact fun v hv => List.mem_append_right _ (P_keys_sub hv)
            · intro p hp
              exact List.mem_append_left _ (List.mem_reverse.mpr
                (List.mem_fst_of_mem_zip hp))
          have zs_sub_St₈ : ∀ z ∈ zs, z ∈ AList.keys St₈.types := by
            intro z hz
            rw [St₈_types]
            apply encodeTerm_state.mem_keys_foldl_insert_of_fst
            have hmap : (zs.zip τs).map Prod.fst = zs :=
              List.map_fst_zip (le_of_eq zs_len)
            rw [hmap]; exact hz
          have St₁_sub_St₂ : St₁.types ⊆ St₂.types := by
            rw [St₂_types]
            refine AList.subset_foldl_insert' ?_ ?_
            · intro p hp
              exact vs_disj_St₁ p.1 (List.mem_fst_of_mem_zip hp)
            · exact List.nodup_map_fst_of_nodup_zip vs_nodup
          have St₁_keys_sub_St₈ : AList.keys St₁.types ⊆ AList.keys St₈.types := by
            intro v hv
            exact AList.mem_keys.mp (AList.mem_of_subset
              (AList.subset_trans (AList.subset_trans St₁_sub_St₂ P_Λ_sub) St₇_sub_St₈)
              (AList.mem_keys.mpr hv))
          mspec (Std.Do.Triple.and
            (castMembership ((zs.map SMT.Term.var).toPairl, τs.toProdl)
              (D_enc, .fun τ' .bool))
            (castMembership_state (zs.map SMT.Term.var).toPairl D_enc τs.toProdl
              (.fun τ' .bool) (Λ := St₈.types) (n := St₈.env.freshvarsc)
              (used := St₈.env.usedVars) (X := B.Term.vars (B.Term.all vs D P)))
            (castMembership_decl (zs.map SMT.Term.var).toPairl D_enc τs.toProdl
              (.fun τ' .bool) (Λ := St₈.types) (n := St₈.env.freshvarsc)
              (used := St₈.env.usedVars) (decl := decl ++ ΔD ++ ΔP)))
          case pre =>
            mpure_intro
            refine ⟨⟨rfl, rfl, St₈_keys_sub, rfl, ?_, ?_⟩,
              rfl, rfl, St₈_keys_sub, rfl, St₈_decl⟩
            · intro v hv
              exact List.mem_union_iff.mpr (Or.inl (AList.mem_keys.mp (zs_sub_St₈ v
                (encodeTerm_state.fv_toPairl_map_var_subset zs v hv))))
            · intro v hv
              rcases List.mem_union_iff.mp (D_state_fv_sub hv) with hk | hb
              · exact List.mem_union_iff.mpr (Or.inl (St₁_keys_sub_St₈ hk))
              · exact List.mem_union_iff.mpr (Or.inr (hvars_D_sub hb))
          case post.success =>
            rename_i out_cm
            obtain ⟨z_mem_D', σcm⟩ := out_cm
            mrename_i pre9
            mintro ∀St₉
            mpure pre9
            obtain ⟨⟨cm_le, cm_Λ_sub, cm_used_sub, cm_keys_sub, cm_fv_sub₀,
              cm_preserves⟩, Δcm, cm_decl_eq, cm_specb_nil, cm_fv_decl_sub⟩ := pre9
            split
            · -- `castMembership` returned a boolean-typed membership term
              rename_i heqcm
              obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ heqcm
              mspec Std.Do.Spec.get_StateT
              simp only [modify]
              mspec Std.Do.Spec.modifyGet_StateT
              mspec (Std.Do.Triple.and (forIn zs PUnit.unit (fun v _ => do
                  SMT.eraseFromContext v; pure (ForInStep.yield PUnit.unit)))
                (SMT.eraseFromContext_forIn_spec zs (Γ := St₂.types)
                  (n := St₉.env.freshvarsc) (used := St₉.env.usedVars))
                (SMT.eraseFromContext_forIn_decls zs (decl := decl ++ ΔD)))
              mrename_i preE
              mintro ∀StF
              mpure preE
              obtain ⟨⟨StF_types, StF_fvc, StF_used⟩, StF_decl⟩ := preE
              mspec Std.Do.Spec.pure
              mpure_intro
              have zs_not_St₂ : ∀ z ∈ zs, z ∉ St₂.types := by
                intro z hz hmem
                have z_used₂ : z ∈ St₂.env.usedVars := St₂_keys_sub (AList.mem_keys.mpr hmem)
                have z_used₇ : z ∈ St₇.env.usedVars := P_used_sub z_used₂
                exact zs_not_used z hz z_used₇
              have StF_types_eq : StF.types = St₂.types := by
                rw [StF_types, encodeTerm_state.foldl_erase_of_notMem zs zs_not_St₂]
              have St₇_used_sub_St₈ : St₇.env.usedVars ⊆ St₈.env.usedVars := by
                rw [St₈_used]; exact fun v hv => List.mem_append_right _ hv
              have St₂_used_sub_St₉ : St₂.env.usedVars ⊆ St₉.env.usedVars :=
                fun v hv => cm_used_sub (St₇_used_sub_St₈ (P_used_sub hv))
              have used_sub_St₉ : used ⊆ St₉.env.usedVars :=
                fun v hv => St₂_used_sub_St₉ (St₁_sub_St₂_used (D_used_sub hv))
              have St₀_types_sub_St₂ : St₀.types ⊆ St₂.types :=
                AList.subset_trans D_Λ_sub St₁_sub_St₂
              have St₁_keys_sub_St₂ : AList.keys St₁.types ⊆ AList.keys St₂.types := by
                rw [St₂_types]; exact encodeTerm_state.keys_subset_foldl_insert _
              have St₉_decls_eq : St₉.env.declarations = decl ++ ΔD ++ ΔP ++ Δcm := cm_decl_eq
              have new_decls_eq :
                  St₉.env.declarations.drop St₂.env.declarations.length = ΔP ++ Δcm := by
                rw [St₉_decls_eq, St₂_decl, List.append_assoc (decl ++ ΔD) ΔP Δcm,
                  List.drop_left]
              have spec_bodies_eq :
                  (St₉.env.declarations.drop St₂.env.declarations.length).filterMap
                    (fun | .define_fun _ .unit .bool b => some b | _ => none)
                    = specBodies ΔP := by
                rw [new_decls_eq, filterMap_specBodies_eq, specBodies_append,
                  cm_specb_nil, List.append_nil]
              have ex_binders_fst_eq :
                  ((St₉.env.declarations.drop St₂.env.declarations.length).filterMap
                    (fun | .declare_const v τ => some (v, τ) | _ => none)).map Prod.fst
                    = declVars ΔP ++ declVars Δcm := by
                rw [map_fst_exBinders_eq_declVars, new_decls_eq, declVars_append]
              set newD := St₉.env.declarations.drop St₂.env.declarations.length with newD_def
              set spB := newD.filterMap
                (fun | .define_fun _ .unit .bool b => some b | _ => none) with spB_def
              set exB := newD.filterMap
                (fun | .declare_const v τ => some (v, τ) | _ => none) with exB_def
              have fv_zsvar : ∀ t ∈ zs.map SMT.Term.var, ∀ w ∈ SMT.fv t, w ∈ zs := by
                intro t ht w hw
                rw [List.mem_map] at ht
                obtain ⟨z, hz, rfl⟩ := ht
                simp only [SMT.fv, List.mem_singleton] at hw
                exact hw ▸ hz
              have body_fv :
                  ∀ v ∈ SMT.fv (SMT.Term.forall zs τs
                    (exB.foldr (fun (p : SMT.𝒱 × SMTType) t => SMT.Term.forall [p.1] [p.2] t)
                      ((spB.map (SMT.substList vs (zs.map SMT.Term.var))).foldr (.imp · ·)
                        (.imp z_mem_D' (SMT.substList vs (zs.map SMT.Term.var) P_enc))))),
                    v ∉ zs ∧ v ∉ declVars ΔP ∧ v ∉ declVars Δcm ∧
                    ((∃ b ∈ specBodies ΔP, v ∈ SMT.fv b) ∨
                      v ∈ SMT.fv z_mem_D' ∨
                      v ∈ SMT.fv (SMT.substList vs (zs.map SMT.Term.var) P_enc)) := by
                intro v hv
                simp only [SMT.fv, List.mem_removeAll_iff] at hv
                obtain ⟨hv_body, hv_notMem_zs⟩ := hv
                obtain ⟨hv_inner, hv_notMem_exB⟩ := mem_fv_foldr_forall hv_body
                have hv_notMem_dv : v ∉ declVars ΔP ++ declVars Δcm := by
                  rw [← ex_binders_fst_eq]; exact hv_notMem_exB
                refine ⟨hv_notMem_zs,
                  fun h => hv_notMem_dv (List.mem_append_left _ h),
                  fun h => hv_notMem_dv (List.mem_append_right _ h), ?_⟩
                rcases mem_fv_foldr_imp hv_inner with ⟨b, hb, hvb⟩ | hbase
                · left
                  obtain ⟨b₀, hb₀, rfl⟩ := List.mem_map.mp hb
                  rcases SMT_mem_fv_substList hvb with hvb' | ⟨t, ht, hvt⟩
                  · rw [spec_bodies_eq] at hb₀
                    exact ⟨b₀, hb₀, hvb'⟩
                  · exact absurd (fv_zsvar t ht v hvt) hv_notMem_zs
                · simp only [SMT.fv, List.mem_append] at hbase
                  rcases hbase with hz_mem | hsubst
                  · exact Or.inr (Or.inl hz_mem)
                  · exact Or.inr (Or.inr hsubst)
              refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ΔD,
                by rw [StF_decl], ?_, ?_⟩
              · intro v hv
                rw [StF_used]
                exact used_sub_St₉ hv
              · rw [StF_types_eq]; exact St₀_types_sub_St₂
              · rw [StF_types_eq, StF_used]
                exact fun v hv => St₂_used_sub_St₉ (St₂_keys_sub hv)
              · intro v hv
                rw [StF_used]
                rw [B.fv, List.mem_append] at hv
                rcases hv with hv | hv
                · exact St₂_used_sub_St₉ (St₁_sub_St₂_used (D_cov v hv))
                · exact cm_used_sub (St₇_used_sub_St₈
                    (P_cov v (List.mem_removeAll_iff.mp hv).1))
              · intro v hv
                obtain ⟨hv_notMem_zs, hv_notMem_dvP, hv_notMem_dvcm, hcases⟩ := body_fv v hv
                rw [StF_types_eq]
                rcases hcases with ⟨b, hb, hvb⟩ | hz_mem | hsubst
                · rcases List.mem_union_iff.mp (P_specb b hb hvb) with hkP | hdP
                  · exact List.mem_union_iff.mpr (Or.inr (hvars_P_sub hkP))
                  · exact absurd hdP hv_notMem_dvP
                · have hcm := cm_fv_decl_sub hz_mem
                  rcases List.mem_union_iff.mp hcm with hxD | hdcm
                  · rcases List.mem_union_iff.mp hxD with hpairl | hD
                    · exact absurd (encodeTerm_state.fv_toPairl_map_var_subset zs v hpairl)
                        hv_notMem_zs
                    · rcases List.mem_union_iff.mp (D_state_fv_sub hD) with hk | hbv
                      · exact List.mem_union_iff.mpr (Or.inl (St₁_keys_sub_St₂ hk))
                      · exact List.mem_union_iff.mpr (Or.inr (hvars_D_sub hbv))
                  · exact absurd hdcm hv_notMem_dvcm
                · rcases SMT_mem_fv_substList hsubst with hvP | ⟨t, ht, hvt⟩
                  · rcases List.mem_union_iff.mp (P_fv_sub hvP) with hk | hd
                    · exact List.mem_union_iff.mpr (Or.inr (hvars_P_sub hk))
                    · exact absurd hd hv_notMem_dvP
                  · exact absurd (fv_zsvar t ht v hvt) hv_notMem_zs
              · intro v v_used v_notMem_St₀ v_notMem_vars
                obtain ⟨v_notMem_vars_D, v_notMem_vars_P, hv_not_vs⟩ :=
                  B.Term.notMem_vars_all.mp v_notMem_vars
                rw [StF_types_eq, St₂_types]
                intro v_in
                have v_notMem_St₁ : v ∉ St₁.types :=
                  D_preserves v v_used v_notMem_St₀ v_notMem_vars_D
                refine v_notMem_St₁ (AList.mem_of_mem_foldl_insert' v_in ?_)
                intro hmem
                rw [List.mem_map] at hmem
                obtain ⟨⟨a, b⟩, hab, rfl⟩ := hmem
                exact hv_not_vs (List.of_mem_zip hab).1
              · intro b hb
                exact specBody_mono hvars_D_sub (List.Subset.refl _) (D_specb b hb)
              · intro v hv
                obtain ⟨hv_notMem_zs, hv_notMem_dvP, hv_notMem_dvcm, hcases⟩ := body_fv v hv
                rcases hcases with ⟨b, hb, hvb⟩ | hz_mem | hsubst
                · rcases List.mem_union_iff.mp (P_specb b hb hvb) with hkP | hdP
                  · exact List.mem_union_iff.mpr (Or.inl (hvars_P_sub hkP))
                  · exact absurd hdP hv_notMem_dvP
                · have hcm := cm_fv_decl_sub hz_mem
                  rcases List.mem_union_iff.mp hcm with hxD | hdcm
                  · rcases List.mem_union_iff.mp hxD with hpairl | hD
                    · exact absurd (encodeTerm_state.fv_toPairl_map_var_subset zs v hpairl)
                        hv_notMem_zs
                    · rcases List.mem_union_iff.mp (D_fv_sub hD) with hbd | hdd
                      · exact List.mem_union_iff.mpr (Or.inl (hvars_D_sub hbd))
                      · exact List.mem_union_iff.mpr (Or.inr hdd)
                  · exact absurd hdcm hv_notMem_dvcm
                · rcases SMT_mem_fv_substList hsubst with hvP | ⟨t, ht, hvt⟩
                  · rcases List.mem_union_iff.mp (P_fv_sub hvP) with hk | hd
                    · exact List.mem_union_iff.mpr (Or.inl (hvars_P_sub hk))
                    · exact absurd hd hv_notMem_dvP
                  · exact absurd (fv_zsvar t ht v hvt) hv_notMem_zs
            · -- castMembership did not return a boolean: throw
              mvcgen
        · -- `encodeTerm P` did not return a boolean: throw
          exact wp_bind_throw _ _ _ _
      · -- arity mismatch: throw
        mvcgen
    · -- D-arm 2: `D` encodes to a relation `.fun α' (.option β')`
      rename_i α' β' heq
      set τs := (α'.pair β').fromProdl (vs.length - 1) with τs_def
      split
      · -- arities match
        rename_i harity
        have vs_τs_len : vs.length = τs.length := (beq_iff_eq.mp harity).symm
        mspec Std.Do.Spec.pure
        mspec (Std.Do.Triple.and _
          (SMT.addToContext_forIn_spec (vs.zip τs)
            (Γ := St₁.types) (n := St₁.env.freshvarsc) (used := St₁.env.usedVars))
          (SMT.addToContext_forIn_decls (vs.zip τs) (decl := decl ++ ΔD)))
        mrename_i pre
        mintro ∀St₂
        mpure pre
        obtain ⟨⟨St₂_types, St₂_fvc, St₂_used⟩, St₂_decl⟩ := pre
        set E' : B.Env := { E with context := vs.zipToAList αs ∪ E.context } with E'_def
        conv in encodeTerm P E => rw [encodeTerm_state.encodeTerm_env_irrel P E E' rfl]
        have St₁_sub_St₂_used : St₁.env.usedVars ⊆ St₂.env.usedVars := by
          rw [St₂_used]
          exact fun v hv => encodeTerm_state.mem_foldl_cons_of_mem _ _ hv
        have vs_disj_St₁ : ∀ v ∈ vs, v ∉ St₁.types := by
          intro v hv
          have vs_not_D_fv : v ∉ B.fv D := fun hv_fv =>
            vs_Γ_disj v hv (AList.lookup_isSome.mp (B.Typing.mem_context_of_mem_fv typ_D hv_fv))
          have hv_vars_D : v ∉ B.Term.vars D :=
            B.Term.notMem_vars_iff.mpr ⟨vs_not_D_fv, by
              have h := bv_nodup
              simp only [B.bv] at h
              rw [List.nodup_append, List.nodup_append] at h
              intro h_bv
              exact h.1.2.2 v hv v h_bv rfl⟩
          apply D_preserves v (vars_used_vs v hv) _ hv_vars_D
          intro hv_St₀
          exact vs_Γ_disj v hv (Λ_inv v (hvars_vs_sub v hv) hv_St₀)
        have St₁_sub_St₂ : St₁.types ⊆ St₂.types := by
          rw [St₂_types]
          refine AList.subset_foldl_insert' ?_ ?_
          · intro p hp
            exact vs_disj_St₁ p.1 (List.mem_fst_of_mem_zip hp)
          · exact List.nodup_map_fst_of_nodup_zip vs_nodup
        have St₂_keys_sub : AList.keys St₂.types ⊆ St₂.env.usedVars := by
          rw [St₂_types, St₂_used]
          exact encodeTerm_state.keys_foldl_insert_subset_foldl_cons _ D_keys_sub
        mspec (Std.Do.Triple.and (SMT.freshVarList τs)
          (SMT.freshVarList_spec τs (Γ := St₂.types) (n := St₂.env.freshvarsc)
            (used := St₂.env.usedVars))
          (SMT.freshVarList_decls τs (decl := decl ++ ΔD)))
        rename_i xs
        mrename_i pre3
        mintro ∀St₃
        mpure pre3
        obtain ⟨⟨xs_len, xs_nodup, xs_not_used, xs_not_Γ, St₃_fvc, St₃_used,
          St₃_types⟩, St₃_decl⟩ := pre3
        mspec Std.Do.Spec.get_StateT
        mspec Std.Do.Spec.get_StateT
        mspec Std.Do.Spec.get_StateT
        have St₂_sub_St₃_used : St₂.env.usedVars ⊆ St₃.env.usedVars := by
          rw [St₃_used]; exact fun v hv => List.mem_append_right _ hv
        have St₂_sub_St₃ : St₂.types ⊆ St₃.types := by
          rw [St₃_types]
          refine AList.subset_foldl_insert' ?_ ?_
          · intro p hp
            exact xs_not_Γ p.1 (List.mem_fst_of_mem_zip hp)
          · exact List.nodup_map_fst_of_nodup_zip xs_nodup
        have xs_map_fst : (xs.zip τs).map Prod.fst = xs :=
          List.map_fst_zip (le_of_eq xs_len)
        have vars_used_P_St₃ : ∀ v ∈ P.vars, v ∈ St₃.env.usedVars :=
          fun v hv => St₂_sub_St₃_used (St₁_sub_St₂_used (D_used_sub (vars_used_P v hv)))
        have xs_disj_P : ∀ v ∈ P.vars, v ∉ xs := by
          intro v hv hxs
          exact xs_not_used v hxs (St₁_sub_St₂_used (D_used_sub (vars_used_P v hv)))
        have St₃_keys_sub : AList.keys St₃.types ⊆ St₃.env.usedVars := by
          rw [St₃_types, St₃_used]
          refine encodeTerm_state.keys_foldl_insert_subset_of_fst_mem _ ?_ ?_
          · exact fun v hv => List.mem_append_right _ (St₂_keys_sub hv)
          · intro p hp
            exact List.mem_append_left _ (List.mem_reverse.mpr
              (List.mem_fst_of_mem_zip hp))
        have Λ_inv_P : ∀ v ∈ P.vars, v ∈ St₃.types → v ∈ E'.context := by
          intro v v_in_P_vars v_in_St₃_types
          have v_in_St₂ : v ∈ St₂.types := by
            rw [St₃_types] at v_in_St₃_types
            refine AList.mem_of_mem_foldl_insert' v_in_St₃_types ?_
            rw [xs_map_fst]
            exact xs_disj_P v v_in_P_vars
          rw [E'_def]
          show v ∈ vs.zipToAList αs ∪ E.context
          by_cases v_in_vs : v ∈ vs
          · exact AList.mem_union.mpr (.inl (AList.mem_zipToAList_of_mem vs_nodup vs_αs_len v_in_vs))
          · have v_in_St₁ : v ∈ St₁.types := by
              rw [St₂_types] at v_in_St₂
              refine AList.mem_of_mem_foldl_insert' v_in_St₂ ?_
              intro h
              rw [List.mem_map] at h
              obtain ⟨⟨a, b⟩, hab, rfl⟩ := h
              exact v_in_vs (List.of_mem_zip hab).1
            have v_used : v ∈ used := vars_used_P v v_in_P_vars
            by_cases v_St₀ : v ∈ St₀.types
            · have v_all : v ∈ (B.Term.all vs D P).vars := by
                unfold B.Term.vars at v_in_P_vars ⊢
                rw [List.mem_union_iff]
                rcases List.mem_union_iff.mp v_in_P_vars with h_fv | h_bv
                · exact .inl (by
                    simp only [B.fv, List.mem_append]
                    exact .inr (List.mem_removeAll_iff.mpr ⟨h_fv, v_in_vs⟩))
                · exact .inr (by
                    simp only [B.bv, List.mem_append]
                    exact .inr h_bv)
              exact AList.mem_union.mpr (.inr (Λ_inv v v_all v_St₀))
            · have v_vars_D : v ∈ B.Term.vars D := by
                by_contra h
                exact absurd v_in_St₁ (D_preserves v v_used v_St₀ h)
              rcases B.Term.mem_vars_iff.mp v_vars_D with h | h
              · exact AList.mem_union.mpr (.inr (AList.lookup_isSome.mp
                  (B.Typing.mem_context_of_mem_fv typ_D h)))
              · rcases B.Term.mem_vars_iff.mp v_in_P_vars with hv_fv_P | hv_bv_P
                · have h_in_E' : ((vs.zipToAList αs ∪ E.context).lookup v).isSome :=
                    B.Typing.mem_context_of_mem_fv typP hv_fv_P
                  exact AList.lookup_isSome.mp h_in_E'
                · exfalso
                  have hbn := bv_nodup
                  simp only [B.bv] at hbn
                  rw [List.nodup_append] at hbn
                  have hin : v ∈ vs ++ B.bv D := List.mem_append.mpr (.inr h)
                  exact hbn.2.2 v hin v hv_bv_P rfl
        mspec P_ih (E := E') (Λ := St₃.types) (n := St₃.env.freshvarsc)
          (used := St₃.env.usedVars) (α := .bool) (decl := decl ++ ΔD) typP vars_used_P_St₃
          Λ_inv_P hP_bv_nodup
        rename_i out_P
        obtain ⟨P_enc, σP⟩ := out_P
        mrename_i pre
        mintro ∀St₇
        mpure pre
        obtain ⟨⟨P_used_sub, P_Λ_sub, P_keys_sub, P_cov, P_state_fv_sub, P_preserves⟩,
          ΔP, P_decl_eq, P_specb, P_fv_sub⟩ := pre
        split
        · -- `encodeTerm P` returned a boolean
          rename_i heqP
          obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ heqP
          have St₂_keys_sub_St₇ : AList.keys St₂.types ⊆ AList.keys St₇.types := by
            intro v hv
            exact AList.mem_keys.mp (AList.mem_of_subset
              (AList.subset_trans St₂_sub_St₃ P_Λ_sub) (AList.mem_keys.mpr hv))
          have xs_sub_St₇ : ∀ x ∈ xs, x ∈ AList.keys St₇.types := by
            intro x hx
            have hx₃ : x ∈ St₃.types := by
              rw [St₃_types]
              apply encodeTerm_state.mem_keys_foldl_insert_of_fst
              rw [xs_map_fst]; exact hx
            exact AList.mem_keys.mp (AList.mem_of_subset P_Λ_sub hx₃)
          mspec (Std.Do.Triple.and
            (castMembership ((xs.map SMT.Term.var).toPairl, τs.toProdl)
              (D_enc, .fun α' (.option β')))
            (castMembership_state (xs.map SMT.Term.var).toPairl D_enc τs.toProdl
              (.fun α' (.option β')) (Λ := St₇.types) (n := St₇.env.freshvarsc)
              (used := St₇.env.usedVars) (X := B.Term.vars (B.Term.all vs D P)))
            (castMembership_decl (xs.map SMT.Term.var).toPairl D_enc τs.toProdl
              (.fun α' (.option β')) (Λ := St₇.types) (n := St₇.env.freshvarsc)
              (used := St₇.env.usedVars) (decl := decl ++ ΔD ++ ΔP)))
          case pre =>
            mpure_intro
            refine ⟨⟨rfl, rfl, P_keys_sub, rfl, ?_, ?_⟩,
              rfl, rfl, P_keys_sub, rfl, P_decl_eq⟩
            · intro v hv
              exact List.mem_union_iff.mpr (Or.inl (xs_sub_St₇ v
                (encodeTerm_state.fv_toPairl_map_var_subset xs v hv)))
            · intro v hv
              rcases List.mem_union_iff.mp (D_state_fv_sub hv) with hk | hb
              · refine List.mem_union_iff.mpr (Or.inl (St₂_keys_sub_St₇ ?_))
                exact AList.mem_keys.mp (AList.mem_of_subset St₁_sub_St₂
                  (AList.mem_keys.mpr hk))
              · exact List.mem_union_iff.mpr (Or.inr (hvars_D_sub hb))
          case post.success =>
            rename_i out_cm
            obtain ⟨xsy_mem_D, σcm⟩ := out_cm
            mrename_i pre9
            mintro ∀St₉
            mpure pre9
            obtain ⟨⟨cm_le, cm_Λ_sub, cm_used_sub, cm_keys_sub, cm_fv_sub₀,
              cm_preserves⟩, Δcm, cm_decl_eq, cm_specb_nil, cm_fv_decl_sub⟩ := pre9
            mspec Std.Do.Spec.get_StateT
            simp only [modify]
            mspec Std.Do.Spec.modifyGet_StateT
            mspec (Std.Do.Triple.and (forIn xs PUnit.unit (fun v _ => do
                SMT.eraseFromContext v; pure (ForInStep.yield PUnit.unit)))
              (SMT.eraseFromContext_forIn_spec xs (Γ := St₃.types)
                (n := St₉.env.freshvarsc) (used := St₉.env.usedVars))
              (SMT.eraseFromContext_forIn_decls xs (decl := decl ++ ΔD)))
            mrename_i preE
            mintro ∀StF
            mpure preE
            obtain ⟨⟨StF_types, StF_fvc, StF_used⟩, StF_decl⟩ := preE
            mspec Std.Do.Spec.pure
            mpure_intro
            have xs_disj_St₂ : ∀ p ∈ xs.zip τs, p.1 ∉ St₂.types := by
              intro p hp
              exact xs_not_Γ p.1 (List.mem_fst_of_mem_zip hp)
            have StF_types_eq : StF.types = St₂.types := by
              rw [StF_types, St₃_types]
              have hh := encodeTerm_state.foldl_erase_foldl_insert (xs.zip τs)
                (s := St₂.types)
                (by rw [xs_map_fst]; exact xs_nodup) xs_disj_St₂
              rw [xs_map_fst] at hh
              exact hh
            have St₇_used_sub_St₈ : St₇.env.usedVars ⊆ St₇.env.usedVars := fun _ h => h
            have St₂_used_sub_St₉ : St₂.env.usedVars ⊆ St₉.env.usedVars :=
              fun v hv => cm_used_sub (P_used_sub (St₂_sub_St₃_used hv))
            have used_sub_St₉ : used ⊆ St₉.env.usedVars :=
              fun v hv => St₂_used_sub_St₉ (St₁_sub_St₂_used (D_used_sub hv))
            have St₀_types_sub_St₂ : St₀.types ⊆ St₂.types :=
              AList.subset_trans D_Λ_sub St₁_sub_St₂
            have St₁_keys_sub_St₂ : AList.keys St₁.types ⊆ AList.keys St₂.types := fun v hv =>
              AList.mem_keys.mp (AList.mem_of_subset St₁_sub_St₂ (AList.mem_keys.mpr hv))
            have St₉_decls_eq : St₉.env.declarations = decl ++ ΔD ++ ΔP ++ Δcm := cm_decl_eq
            have new_decls_eq :
                St₉.env.declarations.drop St₃.env.declarations.length = ΔP ++ Δcm := by
              rw [St₉_decls_eq, St₃_decl, List.append_assoc (decl ++ ΔD) ΔP Δcm,
                List.drop_left]
            have spec_bodies_eq :
                (St₉.env.declarations.drop St₃.env.declarations.length).filterMap
                  (fun | .define_fun _ .unit .bool b => some b | _ => none)
                  = specBodies ΔP := by
              rw [new_decls_eq, filterMap_specBodies_eq, specBodies_append,
                cm_specb_nil, List.append_nil]
            have ex_binders_fst_eq :
                ((St₉.env.declarations.drop St₃.env.declarations.length).filterMap
                  (fun | .declare_const v τ => some (v, τ) | _ => none)).map Prod.fst
                  = declVars ΔP ++ declVars Δcm := by
              rw [map_fst_exBinders_eq_declVars, new_decls_eq, declVars_append]
            set newD := St₉.env.declarations.drop St₃.env.declarations.length with newD_def
            set spB := newD.filterMap
              (fun | .define_fun _ .unit .bool b => some b | _ => none) with spB_def
            set exB := newD.filterMap
              (fun | .declare_const v τ => some (v, τ) | _ => none) with exB_def
            have fv_xsvar : ∀ t ∈ xs.map SMT.Term.var, ∀ w ∈ SMT.fv t, w ∈ xs := by
              intro t ht w hw
              rw [List.mem_map] at ht
              obtain ⟨z, hz, rfl⟩ := ht
              simp only [SMT.fv, List.mem_singleton] at hw
              exact hw ▸ hz
            have body_fv :
                ∀ v ∈ SMT.fv (SMT.Term.forall xs τs
                  (exB.foldr (fun (p : SMT.𝒱 × SMTType) t => SMT.Term.forall [p.1] [p.2] t)
                    ((spB.map (SMT.substList vs (xs.map SMT.Term.var))).foldr (.imp · ·)
                      (.imp xsy_mem_D (SMT.substList vs (xs.map SMT.Term.var) P_enc))))),
                  v ∉ xs ∧ v ∉ declVars ΔP ∧ v ∉ declVars Δcm ∧
                  ((∃ b ∈ specBodies ΔP, v ∈ SMT.fv b) ∨
                    v ∈ SMT.fv xsy_mem_D ∨
                    v ∈ SMT.fv (SMT.substList vs (xs.map SMT.Term.var) P_enc)) := by
              intro v hv
              simp only [SMT.fv, List.mem_removeAll_iff] at hv
              obtain ⟨hv_body, hv_notMem_xs⟩ := hv
              obtain ⟨hv_inner, hv_notMem_exB⟩ := mem_fv_foldr_forall hv_body
              have hv_notMem_dv : v ∉ declVars ΔP ++ declVars Δcm := by
                rw [← ex_binders_fst_eq]; exact hv_notMem_exB
              refine ⟨hv_notMem_xs,
                fun h => hv_notMem_dv (List.mem_append_left _ h),
                fun h => hv_notMem_dv (List.mem_append_right _ h), ?_⟩
              rcases mem_fv_foldr_imp hv_inner with ⟨b, hb, hvb⟩ | hbase
              · left
                obtain ⟨b₀, hb₀, rfl⟩ := List.mem_map.mp hb
                rcases SMT_mem_fv_substList hvb with hvb' | ⟨t, ht, hvt⟩
                · rw [spec_bodies_eq] at hb₀
                  exact ⟨b₀, hb₀, hvb'⟩
                · exact absurd (fv_xsvar t ht v hvt) hv_notMem_xs
              · simp only [SMT.fv, List.mem_append] at hbase
                rcases hbase with hz_mem | hsubst
                · exact Or.inr (Or.inl hz_mem)
                · exact Or.inr (Or.inr hsubst)
            refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ΔD,
              by rw [StF_decl], ?_, ?_⟩
            · intro v hv
              rw [StF_used]
              exact used_sub_St₉ hv
            · rw [StF_types_eq]; exact St₀_types_sub_St₂
            · rw [StF_types_eq, StF_used]
              exact fun v hv => St₂_used_sub_St₉ (St₂_keys_sub hv)
            · intro v hv
              rw [StF_used]
              rw [B.fv, List.mem_append] at hv
              rcases hv with hv | hv
              · exact St₂_used_sub_St₉ (St₁_sub_St₂_used (D_cov v hv))
              · exact cm_used_sub (P_cov v (List.mem_removeAll_iff.mp hv).1)
            · intro v hv
              obtain ⟨hv_notMem_xs, hv_notMem_dvP, hv_notMem_dvcm, hcases⟩ := body_fv v hv
              rw [StF_types_eq]
              rcases hcases with ⟨b, hb, hvb⟩ | hz_mem | hsubst
              · rcases List.mem_union_iff.mp (P_specb b hb hvb) with hkP | hdP
                · exact List.mem_union_iff.mpr (Or.inr (hvars_P_sub hkP))
                · exact absurd hdP hv_notMem_dvP
              · have hcm := cm_fv_decl_sub hz_mem
                rcases List.mem_union_iff.mp hcm with hxD | hdcm
                · rcases List.mem_union_iff.mp hxD with hpairl | hD
                  · exact absurd (encodeTerm_state.fv_toPairl_map_var_subset xs v hpairl)
                      hv_notMem_xs
                  · rcases List.mem_union_iff.mp (D_state_fv_sub hD) with hk | hbv
                    · exact List.mem_union_iff.mpr (Or.inl (St₁_keys_sub_St₂ hk))
                    · exact List.mem_union_iff.mpr (Or.inr (hvars_D_sub hbv))
                · exact absurd hdcm hv_notMem_dvcm
              · rcases SMT_mem_fv_substList hsubst with hvP | ⟨t, ht, hvt⟩
                · rcases List.mem_union_iff.mp (P_fv_sub hvP) with hk | hd
                  · exact List.mem_union_iff.mpr (Or.inr (hvars_P_sub hk))
                  · exact absurd hd hv_notMem_dvP
                · exact absurd (fv_xsvar t ht v hvt) hv_notMem_xs
            · intro v v_used v_notMem_St₀ v_notMem_vars
              obtain ⟨v_notMem_vars_D, v_notMem_vars_P, hv_not_vs⟩ :=
                B.Term.notMem_vars_all.mp v_notMem_vars
              rw [StF_types_eq, St₂_types]
              intro v_in
              have v_notMem_St₁ : v ∉ St₁.types :=
                D_preserves v v_used v_notMem_St₀ v_notMem_vars_D
              refine v_notMem_St₁ (AList.mem_of_mem_foldl_insert' v_in ?_)
              intro hmem
              rw [List.mem_map] at hmem
              obtain ⟨⟨a, b⟩, hab, rfl⟩ := hmem
              exact hv_not_vs (List.of_mem_zip hab).1
            · intro b hb
              exact specBody_mono hvars_D_sub (List.Subset.refl _) (D_specb b hb)
            · intro v hv
              obtain ⟨hv_notMem_xs, hv_notMem_dvP, hv_notMem_dvcm, hcases⟩ := body_fv v hv
              rcases hcases with ⟨b, hb, hvb⟩ | hz_mem | hsubst
              · rcases List.mem_union_iff.mp (P_specb b hb hvb) with hkP | hdP
                · exact List.mem_union_iff.mpr (Or.inl (hvars_P_sub hkP))
                · exact absurd hdP hv_notMem_dvP
              · have hcm := cm_fv_decl_sub hz_mem
                rcases List.mem_union_iff.mp hcm with hxD | hdcm
                · rcases List.mem_union_iff.mp hxD with hpairl | hD
                  · exact absurd (encodeTerm_state.fv_toPairl_map_var_subset xs v hpairl)
                      hv_notMem_xs
                  · rcases List.mem_union_iff.mp (D_fv_sub hD) with hbd | hdd
                    · exact List.mem_union_iff.mpr (Or.inl (hvars_D_sub hbd))
                    · exact List.mem_union_iff.mpr (Or.inr hdd)
                · exact absurd hdcm hv_notMem_dvcm
              · rcases SMT_mem_fv_substList hsubst with hvP | ⟨t, ht, hvt⟩
                · rcases List.mem_union_iff.mp (P_fv_sub hvP) with hk | hd
                  · exact List.mem_union_iff.mpr (Or.inl (hvars_P_sub hk))
                  · exact absurd hd hv_notMem_dvP
                · exact absurd (fv_xsvar t ht v hvt) hv_notMem_xs
        · -- `encodeTerm P` did not return a boolean: throw
          exact wp_bind_throw _ _ _ _
      · -- arity mismatch: throw
        mvcgen
    · -- D encodes to neither a set nor a relation: throw
      exact wp_bind_throw _ _ _ _
  | lambda vs D P D_ih P_ih =>
    mintro pre ∀St₀
    mpure pre
    obtain ⟨rfl, rfl, St₀_sub, St₀_used_eq, St₀_decl_eq⟩ := pre
    rw [encodeTerm]
    obtain ⟨β, αs, Ds, vs_nemp, vs_αs_len, vs_Ds_len, rfl, vs_nodup, D_eq, typDs, typP,
      vs_Γ_disj⟩ := B.Typing.lambdaE typ_t
    set τ := αs.reduce (· ×ᴮ ·) (by simpa [vs_αs_len, ← List.length_pos_iff] using vs_nemp)
      with τ_def
    have typ_D : E.context ⊢ᴮ D : .set τ := by
      rw [D_eq]
      exact encodeTerm_state.typing_reduce_cprod E.context _ _ typDs
        (by simpa [vs_Ds_len, ← List.length_pos_iff] using vs_nemp)
        (by simpa [vs_αs_len, ← List.length_pos_iff] using vs_nemp)
    have hD_bv_nodup : (B.bv D).Nodup := by
      have h := bv_nodup
      simp only [B.bv] at h
      rw [List.nodup_append, List.nodup_append] at h
      exact h.1.2.1
    have hP_bv_nodup : (B.bv P).Nodup := by
      have h := bv_nodup
      simp only [B.bv] at h
      rw [List.nodup_append] at h
      exact h.2.1
    have vars_used_D : ∀ v ∈ D.vars, v ∈ used := by
      intro v hv
      apply vars_used v
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.append_assoc,
        List.mem_append, List.mem_removeAll_iff] at hv ⊢
      rcases hv with hv | hv
      · exact .inl (.inl hv)
      · exact .inr (.inr (.inl hv))
    have vars_used_vs : ∀ v ∈ vs, v ∈ used := by
      intro v hv
      apply vars_used v
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.append_assoc,
        List.mem_append] at hv ⊢
      exact .inr (.inl hv)
    have vars_used_P : ∀ v ∈ P.vars, v ∈ used := by
      intro v hv
      by_cases hvs : v ∈ vs
      · exact vars_used_vs v hvs
      · apply vars_used v
        simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.append_assoc,
          List.mem_append, List.mem_removeAll_iff] at hv ⊢
        rcases hv with hv | hv
        · exact .inl (.inr ⟨hv, hvs⟩)
        · exact .inr (.inr (.inr hv))
    have Λ_inv_D : ∀ v ∈ D.vars, v ∈ St₀.types → v ∈ E.context := by
      intro v hv hSt₀
      apply Λ_inv v _ hSt₀
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.append_assoc,
        List.mem_append, List.mem_removeAll_iff] at hv ⊢
      rcases hv with hv | hv
      · exact .inl (.inl hv)
      · exact .inr (.inr (.inl hv))
    have hvars_D_sub : B.Term.vars D ⊆ B.Term.vars (B.Term.lambda vs D P) := by
      intro v hv
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.append_assoc,
        List.mem_append, List.mem_removeAll_iff] at hv ⊢
      rcases hv with hv | hv
      · exact .inl (.inl hv)
      · exact .inr (.inr (.inl hv))
    have hvars_P_sub : B.Term.vars P ⊆ B.Term.vars (B.Term.lambda vs D P) := by
      intro v hv
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.append_assoc,
        List.mem_append, List.mem_removeAll_iff] at hv ⊢
      rcases hv with hvP | hvP
      · by_cases hvs : v ∈ vs
        · exact .inr (.inl hvs)
        · exact .inl (.inr ⟨hvP, hvs⟩)
      · exact .inr (.inr (.inr hvP))
    mspec D_ih (E := E) (Λ := St₀.types) (n := St₀.env.freshvarsc) (used := used)
      (α := .set τ) (decl := decl) typ_D vars_used_D Λ_inv_D hD_bv_nodup
    rename_i out_D
    obtain ⟨D_enc, τD⟩ := out_D
    mrename_i pre
    mintro ∀St₁
    mpure pre
    obtain ⟨⟨D_used_sub, D_Λ_sub, D_keys_sub, D_cov, D_state_fv_sub, D_preserves⟩,
      ΔD, D_decl_eq, D_specb, D_fv_sub⟩ := pre
    split
    · rename_i τ' heq
      mspec (Std.Do.Triple.and _
        (SMT.addToContext_forIn_spec (vs.zip (τ'.fromProdl (vs.length - 1)))
          (Γ := St₁.types) (n := St₁.env.freshvarsc) (used := St₁.env.usedVars))
        (SMT.addToContext_forIn_decls (vs.zip (τ'.fromProdl (vs.length - 1)))
          (decl := decl ++ ΔD)))
      mrename_i pre
      mintro ∀St₂
      mpure pre
      obtain ⟨⟨St₂_types, St₂_fvc, St₂_used⟩, St₂_decl⟩ := pre
      set E' : B.Env := { E with context := vs.zipToAList αs ∪ E.context } with E'_def
      conv in encodeTerm P E => rw [encodeTerm_state.encodeTerm_env_irrel P E E' rfl]
      have St₁_sub_St₂_used : St₁.env.usedVars ⊆ St₂.env.usedVars := by
        rw [St₂_used]
        exact fun v hv => encodeTerm_state.mem_foldl_cons_of_mem _ _ hv
      have vars_used_P_St₂ : ∀ v ∈ P.vars, v ∈ St₂.env.usedVars :=
        fun v hv => St₁_sub_St₂_used (D_used_sub (vars_used_P v hv))
      have vs_disj_St₁ : ∀ v ∈ vs, v ∉ St₁.types := by
        intro v hv
        have vs_not_D_fv : v ∉ B.fv D := fun hv_fv =>
          vs_Γ_disj v hv (AList.lookup_isSome.mp (B.Typing.mem_context_of_mem_fv typ_D hv_fv))
        have hv_vars_D : v ∉ B.Term.vars D :=
          B.Term.notMem_vars_iff.mpr ⟨vs_not_D_fv, by
            have h := bv_nodup
            simp only [B.bv] at h
            rw [List.nodup_append, List.nodup_append] at h
            intro h_bv
            exact h.1.2.2 v hv v h_bv rfl⟩
        apply D_preserves v (vars_used_vs v hv) _ hv_vars_D
        intro hv_St₀
        have hv_lambda : v ∈ (B.Term.lambda vs D P).vars := by
          unfold B.Term.vars; rw [List.mem_union_iff]; right
          simp only [B.bv, List.mem_append]; exact .inl (.inl hv)
        exact vs_Γ_disj v hv (Λ_inv v hv_lambda hv_St₀)
      have Λ_inv_P : ∀ v ∈ P.vars, v ∈ St₂.types → v ∈ E'.context := by
        intro v v_in_P_vars v_in_St₂_types
        rw [E'_def]
        show v ∈ vs.zipToAList αs ∪ E.context
        by_cases v_in_vs : v ∈ vs
        · exact AList.mem_union.mpr (.inl (AList.mem_zipToAList_of_mem vs_nodup vs_αs_len v_in_vs))
        · have v_in_St₁ : v ∈ St₁.types := by
            rw [St₂_types] at v_in_St₂_types
            refine AList.mem_of_mem_foldl_insert' v_in_St₂_types ?_
            intro h
            rw [List.mem_map] at h
            obtain ⟨⟨a, b⟩, hab, rfl⟩ := h
            exact v_in_vs (List.of_mem_zip hab).1
          have v_used : v ∈ used := vars_used_P v v_in_P_vars
          by_cases v_St₀ : v ∈ St₀.types
          · have v_lambda : v ∈ (B.Term.lambda vs D P).vars := by
              unfold B.Term.vars at v_in_P_vars ⊢
              rw [List.mem_union_iff]
              rcases List.mem_union_iff.mp v_in_P_vars with h_fv | h_bv
              · exact .inl (by
                  simp only [B.fv, List.mem_append]
                  exact .inr (List.mem_removeAll_iff.mpr ⟨h_fv, v_in_vs⟩))
              · exact .inr (by
                  simp only [B.bv, List.mem_append]
                  exact .inr h_bv)
            exact AList.mem_union.mpr (.inr (Λ_inv v v_lambda v_St₀))
          · have v_vars_D : v ∈ B.Term.vars D := by
              by_contra h
              exact absurd v_in_St₁ (D_preserves v v_used v_St₀ h)
            rcases B.Term.mem_vars_iff.mp v_vars_D with h | h
            · exact AList.mem_union.mpr (.inr (AList.lookup_isSome.mp
                (B.Typing.mem_context_of_mem_fv typ_D h)))
            · rcases B.Term.mem_vars_iff.mp v_in_P_vars with hv_fv_P | hv_bv_P
              · have h_in_E' : ((vs.zipToAList αs ∪ E.context).lookup v).isSome :=
                  B.Typing.mem_context_of_mem_fv typP hv_fv_P
                exact AList.lookup_isSome.mp h_in_E'
              · exfalso
                have hbn := bv_nodup
                simp only [B.bv] at hbn
                rw [List.nodup_append] at hbn
                have hin : v ∈ vs ++ B.bv D := List.mem_append.mpr (.inr h)
                exact hbn.2.2 v hin v hv_bv_P rfl
      have St₂_keys_sub : AList.keys St₂.types ⊆ St₂.env.usedVars := by
        rw [St₂_types, St₂_used]
        exact encodeTerm_state.keys_foldl_insert_subset_foldl_cons _ D_keys_sub
      mspec P_ih (E := E') (Λ := St₂.types) (n := St₂.env.freshvarsc)
        (used := St₂.env.usedVars) (α := β) (decl := decl ++ ΔD) typP vars_used_P_St₂
        Λ_inv_P hP_bv_nodup
      rename_i out_P
      obtain ⟨P_enc, σP⟩ := out_P
      mrename_i pre
      mintro ∀St₃
      mpure pre
      obtain ⟨⟨P_used_sub, P_Λ_sub, P_keys_sub, P_cov, P_state_fv_sub, P_preserves⟩,
        ΔP, P_decl_eq, P_specb, P_fv_sub⟩ := pre
      mspec (Std.Do.Triple.and (SMT.freshVar (.pair τ' σP))
        (SMT.freshVar_spec (Γ := St₃.types) (τ := .pair τ' σP) (n := St₃.env.freshvarsc)
          (used := St₃.env.usedVars))
        (SMT.freshVar_decls (τ := .pair τ' σP) (decl := St₃.env.declarations)))
      case post.success xy =>
      mrename_i pre4
      mintro ∀St₄
      mpure pre4
      obtain ⟨⟨St₄_types, xy_fresh, St₄_fvc, St₄_used, xy_not_used⟩, St₄_decl⟩ := pre4
      mspec (Std.Do.Triple.and (SMT.eraseFromContext xy)
        (SMT.eraseFromContext_spec (v := xy) (Γ := St₄.types) (n := St₄.env.freshvarsc)
          (used := St₄.env.usedVars))
        (SMT.eraseFromContext_decls (v := xy) (decl := St₄.env.declarations)))
      mrename_i pre5
      mintro ∀St₅
      mpure pre5
      obtain ⟨⟨St₅_types, St₅_fvc, St₅_used⟩, St₅_decl⟩ := pre5
      mspec Std.Do.Spec.pure
      mpure_intro
      have St₁_sub_St₂ : St₁.types ⊆ St₂.types := by
        rw [St₂_types]
        refine AList.subset_foldl_insert' ?_ ?_
        · intro p hp
          exact vs_disj_St₁ p.1 (List.mem_fst_of_mem_zip hp)
        · exact List.nodup_map_fst_of_nodup_zip vs_nodup
      have St₀_sub_St₃ : St₀.types ⊆ St₃.types :=
        AList.subset_trans (AList.subset_trans D_Λ_sub St₁_sub_St₂) P_Λ_sub
      have St₁_sub_St₃ : St₁.types ⊆ St₃.types :=
        AList.subset_trans St₁_sub_St₂ P_Λ_sub
      have St₃_used_chain : St₃.env.usedVars ⊆ St₅.env.usedVars := by
        rw [St₅_used, St₄_used]; exact fun v hv => List.mem_cons_of_mem _ hv
      have used_sub_St₃ : used ⊆ St₃.env.usedVars :=
        fun v hv => P_used_sub (St₁_sub_St₂_used (D_used_sub hv))
      have xy_not_St₃ : xy ∉ St₃.types := xy_fresh
      have toDestPair_fv : ∀ t ∈ toDestPair vs (SMT.Term.fst (.var xy)),
          ∀ w ∈ SMT.fv t, w = xy := by
        intro t ht w hw
        exact SMT_fv_toDestPair_subset_base (t₀ := SMT.Term.fst (.var xy))
          (by intro u hu; simp only [SMT.fv, List.mem_singleton] at hu; exact hu) ht hw
      have St₅_types_eq : St₅.types = St₃.types := by
        rw [St₅_types, St₄_types]
        exact encodeTerm_state.erase_insert_self xy_not_St₃
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ΔD ++ ΔP,
        by rw [St₅_decl, St₄_decl, P_decl_eq, List.append_assoc], ?_, ?_⟩
      · exact fun v hv => St₃_used_chain (used_sub_St₃ hv)
      · rw [St₅_types_eq]; exact St₀_sub_St₃
      · rw [St₅_types_eq]
        exact fun v hv => St₃_used_chain (P_keys_sub hv)
      · intro v hv
        apply St₃_used_chain
        rw [B.fv, List.mem_append] at hv
        rcases hv with hv | hv
        · exact P_used_sub (St₁_sub_St₂_used (D_cov v hv))
        · exact P_cov v (List.mem_removeAll_iff.mp hv).1
      · intro v hv
        simp only [SMT.fv, List.mem_removeAll_iff, List.mem_append, List.mem_singleton] at hv
        obtain ⟨hv_body, hv_ne_xy⟩ := hv
        rw [St₅_types_eq]
        rcases hv_body with (hvD | hvxy1) | (hvxy2 | hvsubst)
        · rcases List.mem_union_iff.mp (D_state_fv_sub hvD) with hk | hb
          · exact List.mem_union_iff.mpr (.inl (AList.mem_keys.mp (AList.mem_of_subset
              St₁_sub_St₃ (AList.mem_keys.mpr hk))))
          · exact List.mem_union_iff.mpr (.inr (hvars_D_sub hb))
        · exact absurd hvxy1 hv_ne_xy
        · exact absurd hvxy2 hv_ne_xy
        · rcases SMT_mem_fv_substList hvsubst with hvP | ⟨t, ht, hvt⟩
          · rcases List.mem_union_iff.mp (P_state_fv_sub hvP) with hk | hb
            · exact List.mem_union_iff.mpr (.inl hk)
            · exact List.mem_union_iff.mpr (.inr (hvars_P_sub hb))
          · exact absurd (toDestPair_fv t ht v hvt) hv_ne_xy
      · intro v v_used v_notMem_St₀ v_notMem_vars
        obtain ⟨v_notMem_vars_D, v_notMem_vars_P, hv_not_vs⟩ :=
          B.Term.notMem_vars_lambda.mp v_notMem_vars
        rw [St₅_types_eq]
        intro v_in_St₃
        have v_notMem_St₁ := D_preserves v v_used v_notMem_St₀ v_notMem_vars_D
        have v_notMem_St₂ : v ∉ St₂.types := by
          rw [St₂_types]
          intro h
          refine v_notMem_St₁ (AList.mem_of_mem_foldl_insert' h ?_)
          intro hmem
          rw [List.mem_map] at hmem
          obtain ⟨⟨a, b⟩, hab, rfl⟩ := hmem
          exact hv_not_vs (List.of_mem_zip hab).1
        exact P_preserves v (St₁_sub_St₂_used (D_used_sub v_used))
          v_notMem_St₂ v_notMem_vars_P v_in_St₃
      · intro b hb
        rw [specBodies_append, List.mem_append] at hb
        rcases hb with hb | hb
        · exact specBody_mono hvars_D_sub
            (declVars_append .. ▸ List.subset_append_left ..) (D_specb b hb)
        · exact specBody_mono hvars_P_sub
            (declVars_append .. ▸ List.subset_append_right ..) (P_specb b hb)
      · intro v hv
        simp only [SMT.fv, List.mem_removeAll_iff, List.mem_append, List.mem_singleton] at hv
        obtain ⟨hv_body, hv_ne_xy⟩ := hv
        rw [declVars_append]
        rcases hv_body with (hvD | hvxy1) | (hvxy2 | hvsubst)
        · rcases List.mem_union_iff.mp (D_fv_sub hvD) with h | h
          · exact List.mem_union_iff.mpr (.inl (hvars_D_sub h))
          · exact List.mem_union_iff.mpr (.inr (List.mem_append_left _ h))
        · exact absurd hvxy1 hv_ne_xy
        · exact absurd hvxy2 hv_ne_xy
        · rcases SMT_mem_fv_substList hvsubst with hvP | ⟨t, ht, hvt⟩
          · rcases List.mem_union_iff.mp (P_fv_sub hvP) with hfv | hdv
            · exact List.mem_union_iff.mpr (.inl (hvars_P_sub hfv))
            · exact List.mem_union_iff.mpr (.inr (List.mem_append_right _ hdv))
          · exact absurd (toDestPair_fv t ht v hvt) hv_ne_xy
    · mvcgen

set_option maxHeartbeats 4000000 in
/-- Purely structural postcondition of `encodeTerm` (no `«Δ»`, no `respects`, no
`B`-typing, no denotation): state monotonicity, key coverage, source-FV
coverage, encoded-term FV coverage, and variable preservation. Re-derived as the
`.1` projection of `encodeTerm_combined`. -/
theorem encodeTerm_state
    (E : B.Env) {Λ : SMT.TypeContext} {t : B.Term} {α : B.BType}
    (typ_t : E.context ⊢ᴮ t : α)
    {used : List SMT.𝒱}
    (vars_used : ∀ v ∈ t.vars, v ∈ used)
    (Λ_inv : ∀ v ∈ t.vars, v ∈ Λ → v ∈ E.context)
    (bv_nodup : (B.bv t).Nodup)
    {n : ℕ} :
    ⦃ fun (⟨E0, Λ'⟩ : EncoderState) ↦
        ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used⌝ ⦄
    encodeTerm t E
    ⦃ ⇓? (⟨t', _σ⟩ : SMT.Term × SMTType) (⟨E', Γ'⟩ : EncoderState) => ⌜
      used ⊆ E'.usedVars ∧
      Λ ⊆ Γ' ∧
      AList.keys Γ' ⊆ E'.usedVars ∧
      B.CoversUsedVars E'.usedVars t ∧
      SMT.fv t' ⊆ AList.keys Γ' ∪ B.Term.vars t ∧
      (∀ v ∈ used, v ∉ Λ → v ∉ B.Term.vars t → v ∉ Γ') ⌝⦄ := by
  mintro hpre ∀S
  mpure hpre
  obtain ⟨rfl, rfl, hsub, rfl⟩ := hpre
  mspec (encodeTerm_combined E typ_t vars_used Λ_inv bv_nodup
    (decl := S.env.declarations))
  mrename_i hpost
  mintro ∀S'
  mpure hpost
  mpure_intro
  exact hpost.1

set_option maxHeartbeats 4000000 in
/-- The `declarations`-delta postcondition of `encodeTerm`: encoding `t` appends
a chunk `Dlt` to `declarations`, every generated spec body and the encoded term
itself have free variables bounded by source vars plus declared helpers.
Re-derived as the `.2` projection of `encodeTerm_combined`. -/
theorem encodeTerm_decl
    (E : B.Env) {Λ : SMT.TypeContext} {t : B.Term} {α : B.BType}
    (typ_t : E.context ⊢ᴮ t : α)
    {used : List SMT.𝒱}
    (vars_used : ∀ v ∈ t.vars, v ∈ used)
    (Λ_inv : ∀ v ∈ t.vars, v ∈ Λ → v ∈ E.context)
    (bv_nodup : (B.bv t).Nodup)
    {n : ℕ} {decl : SMT.Chunk} :
    ⦃ fun (⟨E0, Λ'⟩ : EncoderState) ↦
        ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used ∧
          E0.declarations = decl⌝ ⦄
    encodeTerm t E
    ⦃ ⇓? (⟨t', _σ⟩ : SMT.Term × SMTType) (⟨E', Γ'⟩ : EncoderState) => ⌜
      ∃ Dlt : SMT.Chunk,
        E'.declarations = decl ++ Dlt ∧
        (∀ b ∈ specBodies Dlt, SMT.fv b ⊆ B.Term.vars t ∪ declVars Dlt) ∧
        SMT.fv t' ⊆ B.Term.vars t ∪ declVars Dlt ⌝⦄ := by
  mintro hpre ∀S
  mpure hpre
  obtain ⟨rfl, rfl, hsub, rfl, rfl⟩ := hpre
  mspec (encodeTerm_combined E typ_t vars_used Λ_inv bv_nodup
    (decl := S.env.declarations))
  mrename_i hpost
  mintro ∀S'
  mpure hpost
  mpure_intro
  exact hpost.2

set_option maxHeartbeats 4000000 in
/-- Structural specification of `encodeTerm`: `encodeTerm_state` together with a
covering renaming witness. Consumed by the HAS-FLAG branch of `all_case`. -/
theorem encodeTerm_struct
    (E : B.Env) {Λ : SMT.TypeContext} {t : B.Term} {α : B.BType}
    (typ_t : E.context ⊢ᴮ t : α)
    {«Δ» : B.RenamingContext.Context}
    {Δ₀ : SMT.RenamingContext.Context}
    (Δ₀_ext : SMT.RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» t)
    {used : List SMT.𝒱}
    (Δ₀_none_out : ∀ v ∉ used, Δ₀ v = none)
    (vars_used : ∀ v ∈ t.vars, v ∈ used)
    (Λ_inv : ∀ v ∈ t.vars, v ∈ Λ → v ∈ E.context)
    (bv_nodup : (B.bv t).Nodup)
    {n : ℕ} :
    ⦃ fun (⟨E0, Λ'⟩ : EncoderState) ↦
        ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used⌝ ⦄
    encodeTerm t E
    ⦃ ⇓? (⟨t', _σ⟩ : SMT.Term × SMTType) (⟨E', Γ'⟩ : EncoderState) => ⌜
      used ⊆ E'.usedVars ∧
      Λ ⊆ Γ' ∧
      AList.keys Γ' ⊆ E'.usedVars ∧
      B.CoversUsedVars E'.usedVars t ∧
      SMT.fv t' ⊆ AList.keys Γ' ∪ B.Term.vars t ∧
      (∀ v ∈ used, v ∉ Λ → v ∉ B.Term.vars t → v ∉ Γ') ∧
      ∃ (Δ' : SMT.RenamingContext.Context)
        (_ : SMT.RenamingContext.CoversFV Δ' t'),
        SMT.RenamingContext.Extends Δ' Δ₀ ∧
          SMT.RenamingContext.ExtendsOnSourceFV Δ' «Δ» t ∧
          (∀ v ∉ E'.usedVars, Δ' v = none) ⌝⦄ := by
  mintro hpre ∀S
  mpure hpre
  obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := hpre
  mspec (encodeTerm_state E typ_t vars_used Λ_inv bv_nodup)
  mrename_i hpost
  mintro ∀S'
  mpure hpost
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hpost
  mpure_intro
  refine ⟨h1, h2, h3, h4, h5, h6,
    encodeTerm_struct.renaming_witness Δ₀_ext Δ₀_none_out h1 h3 ?_ h5⟩
  exact fun v hv => h1 (vars_used v hv)
