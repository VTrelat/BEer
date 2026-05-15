import SMT.Reasoning.Basic.StateSpecs
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

namespace SMT.RenamingContext

/-- Generic structural renaming witness: `Δ₀`, left-biased over the canonical
context induced by the final type context `Γ'`. -/
noncomputable def padWith (Δ₀ : Context) (Γ' : SMT.TypeContext) : Context :=
  fun v => match Δ₀ v with
    | some d => some d
    | none => ofTypeContext Γ' v

end SMT.RenamingContext

/-- The structural `∃ Δ'` clause of `encodeTerm_struct`, discharged generically
from free-variable coverage of the encoded term by the final context. -/
theorem encodeTerm_struct.renaming_witness
    {Δ₀ : SMT.RenamingContext.Context} {«Δ» : B.RenamingContext.Context}
    {t : B.Term} {Γ' : SMT.TypeContext} {t' : SMT.Term}
    {usedVars' used : List SMT.𝒱}
    (Δ₀_ext : SMT.RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» t)
    (Δ₀_none : ∀ v ∉ used, Δ₀ v = none)
    (used_sub : used ⊆ usedVars')
    (keys_sub : AList.keys Γ' ⊆ usedVars')
    (fv_sub : SMT.fv t' ⊆ AList.keys Γ') :
    ∃ (Δ' : SMT.RenamingContext.Context)
      (_ : SMT.RenamingContext.CoversFV Δ' t'),
      SMT.RenamingContext.Extends Δ' Δ₀ ∧
        SMT.RenamingContext.ExtendsOnSourceFV Δ' «Δ» t ∧
        (∀ v ∉ usedVars', Δ' v = none) := by
  refine ⟨SMT.RenamingContext.padWith Δ₀ Γ', ?_, ?_, ?_, ?_⟩
  · -- CoversFV
    intro v hv
    have hvΓ : v ∈ Γ' := AList.mem_keys.mp (fv_sub hv)
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
    have hvΓ : v ∉ Γ' := fun hg => hv (keys_sub (AList.mem_keys.mpr hg))
    have hlk : AList.lookup v Γ' = none := by
      rcases hl : AList.lookup v Γ' with _ | τ
      · rfl
      · exact absurd (AList.lookup_isSome.mp (by rw [hl]; rfl)) hvΓ
    simp only [SMT.RenamingContext.padWith, h0, SMT.RenamingContext.ofTypeContext, hlk]

set_option maxHeartbeats 4000000 in
/-- Structural postcondition of `encodeTerm` (no `«Δ»`, no `respects`, no
`B`-typing, no denotation): state monotonicity, key coverage, source-FV
coverage, encoded-term FV coverage, and variable preservation. -/
theorem encodeTerm_state
    (E : B.Env) {Λ : SMT.TypeContext} {t : B.Term}
    {used : List SMT.𝒱}
    (vars_used : ∀ v ∈ t.vars, v ∈ used)
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
      SMT.fv t' ⊆ AList.keys Γ' ∧
      (∀ v ∈ used, v ∉ Λ → v ∉ B.Term.vars t → v ∉ Γ') ⌝⦄ := by
  induction t generalizing E n used Λ with
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
    · intro v hv; simp [SMT.fv] at hv
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
    · intro v hv; simp [SMT.fv] at hv
    · exact fun _ _ h _ => h
  | var v =>
    mstart
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
    rw [encodeTerm]
    mvcgen
    case vc1 τ τ_lookup =>
      have hv_in_types : v ∈ St.types :=
        AList.lookup_isSome.1 (Option.isSome_of_eq_some τ_lookup)
      and_intros
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
        exact AList.mem_keys.mpr hv_in_types
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
      · intro x hx; simp only [SMT.fv, List.mem_removeAll_iff] at hx; nomatch hx.1
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
      · intro x hx; simp only [SMT.fv, List.mem_removeAll_iff] at hx; nomatch hx.1
      · exact fun _ _ h _ => h
  | maplet x y x_ih y_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
    rw [encodeTerm]
    have hx_bv_nodup : (B.bv x).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.1
    have hy_bv_nodup : (B.bv y).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.2.1
    have vars_used_x : ∀ v ∈ x.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h)
    have vars_used_y : ∀ v ∈ y.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inr h)
    mspec x_ih (E := E) (Λ := σ.types) vars_used_x hx_bv_nodup
    clear x_ih
    rename_i out_x
    obtain ⟨x_enc, σx⟩ := out_x
    mrename_i pre
    mintro ∀σ_x
    mpure pre
    obtain ⟨x_used_sub, x_Λ_sub, x_keys_sub, x_cov, x_fv_sub, x_preserves⟩ := pre
    mspec y_ih (E := E) (Λ := σ_x.types) (used := σ_x.env.usedVars)
      (fun v hv => x_used_sub (vars_used_y v hv)) hy_bv_nodup
    clear y_ih
    rename_i out_y
    obtain ⟨y_enc, σy⟩ := out_y
    mrename_i pre
    mintro ∀σ_y
    mpure pre
    obtain ⟨y_used_sub, y_Λ_sub, y_keys_sub, y_cov, y_fv_sub, y_preserves⟩ := pre
    mpure_intro
    and_intros
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
      · exact AList.mem_keys.mpr (AList.mem_of_subset y_Λ_sub (AList.mem_keys.mp (x_fv_sub hv)))
      · exact y_fv_sub hv
    · intro v hv hΛ hvars
      have hvx : v ∉ B.Term.vars x := fun h => hvars (by
        simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
        rcases h with h | h <;> [left; right] <;> exact .inl h)
      have hvy : v ∉ B.Term.vars y := fun h => hvars (by
        simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
        rcases h with h | h <;> [left; right] <;> exact .inr h)
      exact y_preserves v (x_used_sub hv) (x_preserves v hv hΛ hvx) hvy
  | add x y x_ih y_ih => sorry
  | sub x y x_ih y_ih => sorry
  | mul x y x_ih y_ih => sorry
  | le x y x_ih y_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
    rw [encodeTerm]
    have hx_bv_nodup : (B.bv x).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.1
    have hy_bv_nodup : (B.bv y).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.2.1
    have vars_used_x : ∀ v ∈ x.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h)
    have vars_used_y : ∀ v ∈ y.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inr h)
    mspec x_ih (E := E) (Λ := σ.types) vars_used_x hx_bv_nodup
    clear x_ih
    rename_i out_x
    obtain ⟨x_enc, σx⟩ := out_x
    mrename_i pre
    mintro ∀σ_x
    mpure pre
    obtain ⟨x_used_sub, x_Λ_sub, x_keys_sub, x_cov, x_fv_sub, x_preserves⟩ := pre
    mspec y_ih (E := E) (Λ := σ_x.types) (used := σ_x.env.usedVars)
      (fun v hv => x_used_sub (vars_used_y v hv)) hy_bv_nodup
    clear y_ih
    rename_i out_y
    obtain ⟨y_enc, σy⟩ := out_y
    mrename_i pre
    mintro ∀σ_y
    mpure pre
    obtain ⟨y_used_sub, y_Λ_sub, y_keys_sub, y_cov, y_fv_sub, y_preserves⟩ := pre
    mpure_intro
    and_intros
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
      · exact AList.mem_keys.mpr (AList.mem_of_subset y_Λ_sub (AList.mem_keys.mp (x_fv_sub hv)))
      · exact y_fv_sub hv
    · intro v hv hΛ hvars
      have hvx : v ∉ B.Term.vars x := fun h => hvars (by
        simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
        rcases h with h | h <;> [left; right] <;> exact .inl h)
      have hvy : v ∉ B.Term.vars y := fun h => hvars (by
        simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
        rcases h with h | h <;> [left; right] <;> exact .inr h)
      exact y_preserves v (x_used_sub hv) (x_preserves v hv hΛ hvx) hvy
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
    (E : B.Env) {Λ : SMT.TypeContext} {t : B.Term}
    {«Δ» : B.RenamingContext.Context}
    {Δ₀ : SMT.RenamingContext.Context}
    (Δ₀_ext : SMT.RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» t)
    {used : List SMT.𝒱}
    (Δ₀_none_out : ∀ v ∉ used, Δ₀ v = none)
    (vars_used : ∀ v ∈ t.vars, v ∈ used)
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
      SMT.fv t' ⊆ AList.keys Γ' ∧
      (∀ v ∈ used, v ∉ Λ → v ∉ B.Term.vars t → v ∉ Γ') ∧
      ∃ (Δ' : SMT.RenamingContext.Context)
        (_ : SMT.RenamingContext.CoversFV Δ' t'),
        SMT.RenamingContext.Extends Δ' Δ₀ ∧
          SMT.RenamingContext.ExtendsOnSourceFV Δ' «Δ» t ∧
          (∀ v ∉ E'.usedVars, Δ' v = none) ⌝⦄ := by
  mintro hpre ∀S
  mpure hpre
  obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := hpre
  mspec (encodeTerm_state E vars_used bv_nodup)
  mrename_i hpost
  mintro ∀S'
  mpure hpost
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hpost
  mpure_intro
  exact ⟨h1, h2, h3, h4, h5, h6,
    encodeTerm_struct.renaming_witness Δ₀_ext Δ₀_none_out h1 h3 h5⟩
