import SMT.Reasoning.Basic.StateSpecs
import SMT.Reasoning.Axioms

/-!
# `encodeTerm` structural specification

`encodeTerm_struct` captures the *structural* postcondition of `encodeTerm`:
state monotonicity, SMT well-typedness of the encoded term, source-variable
coverage/preservation, and the existence of a covering renaming context.

Unlike `encodeTerm_spec`, it does **not** require the `respects` hypothesis and
does **not** assert `σ = α.toSMTType` or any denotational fact — precisely the
parts that are unavailable (indeed false) for a flagged binder. It is consumed
by the HAS-FLAG branch of `encodeTerm_spec.all_case`, which needs structural
facts about the encoding of the binder body `P` without a (false) `respects`.

The renaming witness is discharged generically (`renaming_witness`): a term
typed by the final context `Γ'` has all free variables in `Γ' ⊆ usedVars`, so
`Δ₀` padded over `Γ'` covers it.
-/

open Std.Do B SMT ZFSet
set_option mvcgen.warning false

namespace SMT.RenamingContext

/-- Generic structural renaming witness: `Δ₀`, left-biased over the canonical
context induced by the final type context `Γ'`. -/
noncomputable def padWith (Δ₀ : Context) (Γ' : SMT.TypeContext) : Context :=
  fun v => match Δ₀ v with
    | some d => some d
    | none => ofTypeContext Γ' v

end SMT.RenamingContext

/-- The structural `∃ Δ'` clause of `encodeTerm_struct`, discharged generically
from the SMT typing of the encoded term plus key-coverage of the final context. -/
theorem encodeTerm_struct.renaming_witness
    {Δ₀ : SMT.RenamingContext.Context} {«Δ» : B.RenamingContext.Context}
    {t : B.Term} {Γ' : SMT.TypeContext} {t' : SMT.Term} {σ : SMTType}
    {usedVars' used : List SMT.𝒱}
    (Δ₀_ext : SMT.RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» t)
    (Δ₀_none : ∀ v ∉ used, Δ₀ v = none)
    (used_sub : used ⊆ usedVars')
    (keys_sub : AList.keys Γ' ⊆ usedVars')
    (typ : Γ' ⊢ˢ t' : σ) :
    ∃ (Δ' : SMT.RenamingContext.Context)
      (_ : SMT.RenamingContext.CoversFV Δ' t'),
      SMT.RenamingContext.Extends Δ' Δ₀ ∧
        SMT.RenamingContext.ExtendsOnSourceFV Δ' «Δ» t ∧
        (∀ v ∉ usedVars', Δ' v = none) := by
  refine ⟨SMT.RenamingContext.padWith Δ₀ Γ', ?_, ?_, ?_, ?_⟩
  · -- CoversFV
    intro v hv
    have hvΓ : v ∈ Γ' := SMT.Typing.mem_context_of_mem_fv typ hv
    obtain ⟨τv, hτv⟩ := Option.isSome_iff_exists.mp ((AList.lookup_isSome).2 hvΓ)
    simp only [SMT.RenamingContext.padWith]
    cases h : Δ₀ v with
    | some d => simp
    | none => simp [SMT.RenamingContext.ofTypeContext, hτv]
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
    have hvΓ : v ∉ Γ' := fun hg => hv (keys_sub hg)
    have hlk : AList.lookup v Γ' = none := by
      rcases hl : AList.lookup v Γ' with _ | τ
      · rfl
      · exact absurd (AList.lookup_isSome.mp (by rw [hl]; rfl)) hvΓ
    simp only [SMT.RenamingContext.padWith, h0, SMT.RenamingContext.ofTypeContext, hlk]

set_option maxHeartbeats 4000000 in
/-- Structural postcondition of `encodeTerm` (no `«Δ»`, no `respects`, no
denotation): state monotonicity, key coverage, source-FV coverage, SMT typing
of the encoded term, and variable preservation. -/
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
    ⦃ ⇓? (⟨t', σ⟩ : SMT.Term × SMTType) (⟨E', Γ'⟩ : EncoderState) => ⌜
      used ⊆ E'.usedVars ∧
      Λ ⊆ Γ' ∧
      AList.keys Γ' ⊆ E'.usedVars ∧
      B.CoversUsedVars E'.usedVars t ∧
      (Γ' ⊢ˢ t' : σ) ∧
      (∀ v ∈ used, v ∉ Λ → v ∉ B.Term.vars t → v ∉ Γ') ⌝⦄ := by
  induction t generalizing E n α used Λ with
  | int i =>
    mstart
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
    rw [encodeTerm]
    mspec Std.Do.Spec.pure
    mpure_intro
    and_intros
    · intro v hv; simpa [St_used_eq] using hv
    · intro v hv; simpa using hv
    · intro v hv; simpa [St_used_eq] using St_sub hv
    · intro v hv; simp [B.fv] at hv
    · apply SMT.Typing.int
    · exact fun _ _ h _ => h
  | bool b =>
    mstart
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
    rw [encodeTerm]
    mspec Std.Do.Spec.pure
    mpure_intro
    and_intros
    · intro v hv; simpa [St_used_eq] using hv
    · intro v hv; simpa using hv
    · intro v hv; simpa [St_used_eq] using St_sub hv
    · intro v hv; simp [B.fv] at hv
    · apply SMT.Typing.bool
    · exact fun _ _ h _ => h
  | var v =>
    mstart
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
    rw [encodeTerm]
    mvcgen
    case vc1 τ τ_lookup =>
      and_intros
      · intro x hx; simpa [St_used_eq] using hx
      · intro x hx; simpa using hx
      · intro x hx; simpa [St_used_eq] using St_sub hx
      · intro x hx
        rw [B.fv, List.mem_singleton] at hx
        subst x
        have hv_in_types : v ∈ St.types :=
          AList.lookup_isSome.1 (Option.isSome_of_eq_some τ_lookup)
        simpa [St_used_eq] using (St_sub hv_in_types)
      · exact SMT.Typing.var St.types v τ τ_lookup
      · exact fun _ _ h _ => h
  | «ℤ» =>
    mstart
    mintro pre ∀S
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
    rw [encodeTerm]
    mspec Std.Do.Spec.get_StateT
    mspec freshVar_spec (used := S.env.usedVars)
    case post.success 𝓋 =>
      mrename_i pre
      mintro ∀S'
      mpure pre
      obtain ⟨types_eq, 𝓋_notMem, freshvarsc_eq, used_eq, 𝓋_neq_used⟩ := pre
      mspec Std.Do.Spec.modifyGet_StateT
      mspec Std.Do.Spec.pure
      mpure_intro
      and_intros
      · intro x hx; rw [used_eq, St_used_eq]; exact List.mem_cons_of_mem _ hx
      · exact fun _ => id
      · rw [used_eq]; intro x hx; exact List.mem_cons_of_mem _ (St_sub hx)
      · intro x hx; rw [B.fv] at hx; contradiction
      · apply SMT.Typing.lambda
        · intro _ h; rw [List.mem_singleton] at h; obtain ⟨⟩ := h; exact 𝓋_notMem
        · simp only [List.mem_cons, List.not_mem_nil, or_false, SMT.bv, not_false_eq_true,
            implies_true]
        · apply Nat.zero_lt_succ
        · apply SMT.Typing.bool
        · rfl
      · exact fun _ _ h _ => h
  | 𝔹 =>
    mstart
    mintro pre ∀S
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
    rw [encodeTerm]
    mspec Std.Do.Spec.get_StateT
    mspec freshVar_spec (used := S.env.usedVars)
    case post.success 𝓋 =>
      mrename_i pre
      mintro ∀S'
      mpure pre
      obtain ⟨types_eq, 𝓋_notMem, freshvarsc_eq, used_eq, 𝓋_neq_used⟩ := pre
      mspec Std.Do.Spec.modifyGet_StateT
      mspec Std.Do.Spec.pure
      mpure_intro
      and_intros
      · intro x hx; rw [used_eq, St_used_eq]; exact List.mem_cons_of_mem _ hx
      · exact fun _ => id
      · rw [used_eq]; intro x hx; exact List.mem_cons_of_mem _ (St_sub hx)
      · intro x hx; rw [B.fv] at hx; contradiction
      · apply SMT.Typing.lambda
        · intro _ h; rw [List.mem_singleton] at h; obtain ⟨⟩ := h; exact 𝓋_notMem
        · simp only [List.mem_cons, List.not_mem_nil, or_false, SMT.bv, not_false_eq_true,
            implies_true]
        · apply Nat.zero_lt_succ
        · apply SMT.Typing.bool
        · rfl
      · exact fun _ _ h _ => h
  | maplet x y x_ih y_ih => sorry
  | add x y x_ih y_ih => sorry
  | sub x y x_ih y_ih => sorry
  | mul x y x_ih y_ih => sorry
  | le x y x_ih y_ih => sorry
  | min S ih => sorry
  | max S ih => sorry
  | card S ih => sorry
  | and x y x_ih y_ih => sorry
  | not x ih => sorry
  | pow S ih => sorry
  | cprod A B A_ih B_ih => sorry
  | mem x S x_ih S_ih => sorry
  | eq x y x_ih y_ih => sorry
  | union A B A_ih B_ih => sorry
  | inter A B A_ih B_ih => sorry
  | pfun A B A_ih B_ih => sorry
  | app f x f_ih x_ih => sorry
  | collect vs D P D_ih P_ih => sorry
  | all vs D P D_ih P_ih => sorry
  | lambda vs D P D_ih P_ih => sorry

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
    ⦃ ⇓? (⟨t', σ⟩ : SMT.Term × SMTType) (⟨E', Γ'⟩ : EncoderState) => ⌜
      used ⊆ E'.usedVars ∧
      Λ ⊆ Γ' ∧
      AList.keys Γ' ⊆ E'.usedVars ∧
      B.CoversUsedVars E'.usedVars t ∧
      (Γ' ⊢ˢ t' : σ) ∧
      (∀ v ∈ used, v ∉ Λ → v ∉ B.Term.vars t → v ∉ Γ') ∧
      ∃ (Δ' : SMT.RenamingContext.Context)
        (_ : SMT.RenamingContext.CoversFV Δ' t'),
        SMT.RenamingContext.Extends Δ' Δ₀ ∧
          SMT.RenamingContext.ExtendsOnSourceFV Δ' «Δ» t ∧
          (∀ v ∉ E'.usedVars, Δ' v = none) ⌝⦄ := by
  mintro hpre ∀S
  mspec (encodeTerm_state E typ_t vars_used Λ_inv bv_nodup (n := n))
  mrename_i hpost
  mintro ∀S'
  mpure hpost
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hpost
  mpure_intro
  exact ⟨h1, h2, h3, h4, h5, h6,
    encodeTerm_struct.renaming_witness Δ₀_ext Δ₀_none_out h1 h3 h5⟩
