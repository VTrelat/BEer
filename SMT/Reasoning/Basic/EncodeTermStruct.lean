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
  | add x y x_ih y_ih =>
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
    rename_i out_x
    obtain ⟨x_enc, σx⟩ := out_x
    mrename_i prex
    mintro ∀σ_x
    mpure prex
    obtain ⟨x_used_sub, x_Λ_sub, x_keys_sub, x_cov, x_fv_sub, x_preserves⟩ := prex
    split
    · rename_i heq
      injection heq with hxe hσe
      subst hσe
      subst hxe
      mspec y_ih (E := E) (Λ := σ_x.types) (used := σ_x.env.usedVars)
        (fun v hv => x_used_sub (vars_used_y v hv)) hy_bv_nodup
      rename_i out_y
      obtain ⟨y_enc, σy⟩ := out_y
      mrename_i prey
      mintro ∀σ_y
      mpure prey
      obtain ⟨y_used_sub, y_Λ_sub, y_keys_sub, y_cov, y_fv_sub, y_preserves⟩ := prey
      split
      · rename_i heq2
        injection heq2 with hye hσe2
        subst hσe2
        subst hye
        mspec Std.Do.Spec.pure
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
          · exact AList.mem_keys.mpr
              (AList.mem_of_subset y_Λ_sub (AList.mem_keys.mp (x_fv_sub hv)))
          · exact y_fv_sub hv
        · intro v hv hΛ hvars
          have hvx : v ∉ B.Term.vars x := fun h => hvars (by
            simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
            rcases h with h | h <;> [left; right] <;> exact .inl h)
          have hvy : v ∉ B.Term.vars y := fun h => hvars (by
            simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
            rcases h with h | h <;> [left; right] <;> exact .inr h)
          exact y_preserves v (x_used_sub hv) (x_preserves v hv hΛ hvx) hvy
      · mspec y_ih (E := E) (Λ := σ_y.types) (used := σ_y.env.usedVars)
          (fun v hv => y_used_sub (x_used_sub (vars_used_y v hv))) hy_bv_nodup
        mvcgen
    · mspec x_ih (E := E) (Λ := σ_x.types) (used := σ_x.env.usedVars)
        (fun v hv => x_used_sub (vars_used_x v hv)) hx_bv_nodup
      mvcgen
  | sub x y x_ih y_ih =>
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
    rename_i out_x
    obtain ⟨x_enc, σx⟩ := out_x
    mrename_i prex
    mintro ∀σ_x
    mpure prex
    obtain ⟨x_used_sub, x_Λ_sub, x_keys_sub, x_cov, x_fv_sub, x_preserves⟩ := prex
    split
    · rename_i heq
      injection heq with hxe hσe
      subst hσe
      subst hxe
      mspec y_ih (E := E) (Λ := σ_x.types) (used := σ_x.env.usedVars)
        (fun v hv => x_used_sub (vars_used_y v hv)) hy_bv_nodup
      rename_i out_y
      obtain ⟨y_enc, σy⟩ := out_y
      mrename_i prey
      mintro ∀σ_y
      mpure prey
      obtain ⟨y_used_sub, y_Λ_sub, y_keys_sub, y_cov, y_fv_sub, y_preserves⟩ := prey
      split
      · rename_i heq2
        injection heq2 with hye hσe2
        subst hσe2
        subst hye
        mspec Std.Do.Spec.pure
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
          · exact AList.mem_keys.mpr
              (AList.mem_of_subset y_Λ_sub (AList.mem_keys.mp (x_fv_sub hv)))
          · exact y_fv_sub hv
        · intro v hv hΛ hvars
          have hvx : v ∉ B.Term.vars x := fun h => hvars (by
            simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
            rcases h with h | h <;> [left; right] <;> exact .inl h)
          have hvy : v ∉ B.Term.vars y := fun h => hvars (by
            simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
            rcases h with h | h <;> [left; right] <;> exact .inr h)
          exact y_preserves v (x_used_sub hv) (x_preserves v hv hΛ hvx) hvy
      · mspec y_ih (E := E) (Λ := σ_y.types) (used := σ_y.env.usedVars)
          (fun v hv => y_used_sub (x_used_sub (vars_used_y v hv))) hy_bv_nodup
        mvcgen
    · mspec x_ih (E := E) (Λ := σ_x.types) (used := σ_x.env.usedVars)
        (fun v hv => x_used_sub (vars_used_x v hv)) hx_bv_nodup
      mvcgen
  | mul x y x_ih y_ih =>
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
    rename_i out_x
    obtain ⟨x_enc, σx⟩ := out_x
    mrename_i prex
    mintro ∀σ_x
    mpure prex
    obtain ⟨x_used_sub, x_Λ_sub, x_keys_sub, x_cov, x_fv_sub, x_preserves⟩ := prex
    split
    · rename_i heq
      injection heq with hxe hσe
      subst hσe
      subst hxe
      mspec y_ih (E := E) (Λ := σ_x.types) (used := σ_x.env.usedVars)
        (fun v hv => x_used_sub (vars_used_y v hv)) hy_bv_nodup
      rename_i out_y
      obtain ⟨y_enc, σy⟩ := out_y
      mrename_i prey
      mintro ∀σ_y
      mpure prey
      obtain ⟨y_used_sub, y_Λ_sub, y_keys_sub, y_cov, y_fv_sub, y_preserves⟩ := prey
      split
      · rename_i heq2
        injection heq2 with hye hσe2
        subst hσe2
        subst hye
        mspec Std.Do.Spec.pure
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
          · exact AList.mem_keys.mpr
              (AList.mem_of_subset y_Λ_sub (AList.mem_keys.mp (x_fv_sub hv)))
          · exact y_fv_sub hv
        · intro v hv hΛ hvars
          have hvx : v ∉ B.Term.vars x := fun h => hvars (by
            simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
            rcases h with h | h <;> [left; right] <;> exact .inl h)
          have hvy : v ∉ B.Term.vars y := fun h => hvars (by
            simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
            rcases h with h | h <;> [left; right] <;> exact .inr h)
          exact y_preserves v (x_used_sub hv) (x_preserves v hv hΛ hvx) hvy
      · mspec y_ih (E := E) (Λ := σ_y.types) (used := σ_y.env.usedVars)
          (fun v hv => y_used_sub (x_used_sub (vars_used_y v hv))) hy_bv_nodup
        mvcgen
    · mspec x_ih (E := E) (Λ := σ_x.types) (used := σ_x.env.usedVars)
        (fun v hv => x_used_sub (vars_used_x v hv)) hx_bv_nodup
      mvcgen
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
  | min S _ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
    simp only [encodeTerm] <;> mvcgen
  | max S _ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
    simp only [encodeTerm] <;> mvcgen
  | card S _ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
    simp only [encodeTerm] <;> mvcgen
  | and x y x_ih y_ih =>
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
    rename_i out_x
    obtain ⟨x_enc, σx⟩ := out_x
    mrename_i prex
    mintro ∀σ_x
    mpure prex
    obtain ⟨x_used_sub, x_Λ_sub, x_keys_sub, x_cov, x_fv_sub, x_preserves⟩ := prex
    split
    · rename_i heq
      injection heq with hxe hσe
      subst hσe
      subst hxe
      mspec y_ih (E := E) (Λ := σ_x.types) (used := σ_x.env.usedVars)
        (fun v hv => x_used_sub (vars_used_y v hv)) hy_bv_nodup
      rename_i out_y
      obtain ⟨y_enc, σy⟩ := out_y
      mrename_i prey
      mintro ∀σ_y
      mpure prey
      obtain ⟨y_used_sub, y_Λ_sub, y_keys_sub, y_cov, y_fv_sub, y_preserves⟩ := prey
      split
      · rename_i heq2
        injection heq2 with hye hσe2
        subst hσe2
        subst hye
        mspec Std.Do.Spec.pure
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
          · exact AList.mem_keys.mpr
              (AList.mem_of_subset y_Λ_sub (AList.mem_keys.mp (x_fv_sub hv)))
          · exact y_fv_sub hv
        · intro v hv hΛ hvars
          have hvx : v ∉ B.Term.vars x := fun h => hvars (by
            simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
            rcases h with h | h <;> [left; right] <;> exact .inl h)
          have hvy : v ∉ B.Term.vars y := fun h => hvars (by
            simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at h ⊢
            rcases h with h | h <;> [left; right] <;> exact .inr h)
          exact y_preserves v (x_used_sub hv) (x_preserves v hv hΛ hvx) hvy
      · mspec y_ih (E := E) (Λ := σ_y.types) (used := σ_y.env.usedVars)
          (fun v hv => y_used_sub (x_used_sub (vars_used_y v hv))) hy_bv_nodup
        mvcgen
    · mspec x_ih (E := E) (Λ := σ_x.types) (used := σ_x.env.usedVars)
        (fun v hv => x_used_sub (vars_used_x v hv)) hx_bv_nodup
      mvcgen
  | not x ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
    rw [encodeTerm]
    have hx_bv_nodup : (B.bv x).Nodup := by simpa [B.bv] using bv_nodup
    have vars_used_x : ∀ v ∈ x.vars, v ∈ used := fun v hv => vars_used v (by
      simpa [B.Term.vars, B.fv, B.bv] using hv)
    mspec ih (E := E) (Λ := σ.types) vars_used_x hx_bv_nodup
    rename_i out_x
    obtain ⟨x_enc, σx⟩ := out_x
    mrename_i prex
    mintro ∀σ_x
    mpure prex
    obtain ⟨x_used_sub, x_Λ_sub, x_keys_sub, x_cov, x_fv_sub, x_preserves⟩ := prex
    split
    · rename_i heq
      injection heq with hxe hσe
      subst hσe
      subst hxe
      mspec Std.Do.Spec.pure
      mpure_intro
      and_intros
      · exact x_used_sub
      · exact x_Λ_sub
      · exact x_keys_sub
      · intro v hv; simp only [B.fv] at hv; exact x_cov v hv
      · intro v hv; simp only [SMT.fv] at hv; exact x_fv_sub hv
      · intro v hv hΛ hvars
        exact x_preserves v hv hΛ (fun h => hvars (by
          simpa [B.Term.vars, B.fv, B.bv] using h))
    · mspec ih (E := E) (Λ := σ_x.types) (used := σ_x.env.usedVars)
        (fun v hv => x_used_sub (vars_used_x v hv)) hx_bv_nodup
      mvcgen
  | pow S ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
    rw [encodeTerm]
    have hS_bv_nodup : (B.bv S).Nodup := by simpa [B.bv] using bv_nodup
    have vars_used_S : ∀ v ∈ S.vars, v ∈ used := fun v hv => vars_used v (by
      simpa [B.Term.vars, B.fv, B.bv] using hv)
    mspec ih (E := E) (Λ := σ.types) vars_used_S hS_bv_nodup
    rename_i out_S
    obtain ⟨S_enc, σS⟩ := out_S
    mrename_i preS
    mintro ∀σ_S
    mpure preS
    obtain ⟨S_used_sub, S_Λ_sub, S_keys_sub, S_cov, S_fv_sub, S_preserves⟩ := preS
    split
    · rename_i heq
      subst heq
      set ctx := σ_S.types with hctx
      mspec Std.Do.Spec.get_StateT
      mspec freshVar_spec (Γ := ctx) (used := σ_S.env.usedVars)
      case post.success x =>
        mrename_i pre
        mintro ∀St₁
        mpure pre
        obtain ⟨St₁_types_eq, x_fresh, St₁_fvc_eq, St₁_used_eq, x_not_used⟩ := pre
        mspec freshVar_spec (Γ := ctx.insert x _) (used := St₁.env.usedVars)
        case post.success ℰ =>
          mrename_i pre
          mintro ∀St₂
          mpure pre
          obtain ⟨St₂_types_eq, ℰ_fresh, St₂_fvc_eq, St₂_used_eq, ℰ_not_used⟩ := pre
          simp [modify]
          mspec Std.Do.Spec.modifyGet_StateT
          mpure_intro
          and_intros
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
    · rename_i heq
      subst heq
      set ctx := σ_S.types with hctx
      mspec Std.Do.Spec.get_StateT
      mspec freshVar_spec (Γ := ctx) (used := σ_S.env.usedVars)
      case post.success x =>
        mrename_i pre
        mintro ∀St₁
        mpure pre
        obtain ⟨St₁_types_eq, x_fresh, St₁_fvc_eq, St₁_used_eq, x_not_used⟩ := pre
        mspec freshVar_spec (Γ := ctx.insert x _) (used := St₁.env.usedVars)
        case post.success y =>
          mrename_i pre
          mintro ∀St₂
          mpure pre
          obtain ⟨St₂_types_eq, y_fresh, St₂_fvc_eq, St₂_used_eq, y_not_used⟩ := pre
          mspec freshVar_spec (Γ := (ctx.insert x _).insert y _) (used := St₂.env.usedVars)
          case post.success f =>
            mrename_i pre
            mintro ∀St₃
            mpure pre
            obtain ⟨St₃_types_eq, f_fresh, St₃_fvc_eq, St₃_used_eq, f_not_used⟩ := pre
            simp [modify]
            mspec Std.Do.Spec.modifyGet_StateT
            mpure_intro
            and_intros
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
    · mvcgen
  | cprod A C A_ih C_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
    rw [encodeTerm]
    have hA_bv_nodup : (B.bv A).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.1
    have hC_bv_nodup : (B.bv C).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.2.1
    have vars_used_A : ∀ v ∈ A.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h)
    have vars_used_C : ∀ v ∈ C.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inr h)
    mspec A_ih (E := E) (Λ := σ.types) vars_used_A hA_bv_nodup
    rename_i out_A
    obtain ⟨A_enc, σA⟩ := out_A
    mrename_i preA
    mintro ∀σ_A
    mpure preA
    obtain ⟨A_used_sub, A_Λ_sub, A_keys_sub, A_cov, A_fv_sub, A_preserves⟩ := preA
    split
    · rename_i heq
      injection heq with hAe hσe
      subst hσe
      subst hAe
      mspec C_ih (E := E) (Λ := σ_A.types) (used := σ_A.env.usedVars)
        (fun v hv => A_used_sub (vars_used_C v hv)) hC_bv_nodup
      rename_i out_C
      obtain ⟨C_enc, σC⟩ := out_C
      mrename_i preC
      mintro ∀σ_C
      mpure preC
      obtain ⟨C_used_sub, C_Λ_sub, C_keys_sub, C_cov, C_fv_sub, C_preserves⟩ := preC
      split
      · rename_i heq2
        injection heq2 with hCe hσe2
        subst hσe2
        subst hCe
        set ctx := σ_C.types with hctx
        mspec freshVar_spec (Γ := ctx) (used := σ_C.env.usedVars)
        case post.success p =>
          mrename_i pre
          mintro ∀St₁
          mpure pre
          obtain ⟨St₁_types_eq, p_fresh, St₁_fvc_eq, St₁_used_eq, p_not_used⟩ := pre
          mspec freshVar_spec (Γ := ctx.insert p _) (used := St₁.env.usedVars)
          case post.success a =>
            mrename_i pre
            mintro ∀St₂
            mpure pre
            obtain ⟨St₂_types_eq, a_fresh, St₂_fvc_eq, St₂_used_eq, a_not_used⟩ := pre
            mspec freshVar_spec (Γ := (ctx.insert p _).insert a _) (used := St₂.env.usedVars)
            case post.success b =>
              mrename_i pre
              mintro ∀St₃
              mpure pre
              obtain ⟨St₃_types_eq, b_fresh, St₃_fvc_eq, St₃_used_eq, b_not_used⟩ := pre
              mspec Std.Do.Spec.pure
              mpure_intro
              and_intros
              · intro v hv
                rw [St₃_used_eq, St₂_used_eq, St₁_used_eq]
                exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                  (List.mem_cons_of_mem _ (C_used_sub (A_used_sub hv))))
              · intro v hv
                rw [St₃_types_eq]
                apply SMT.TypeContext.entries_subset_insert_of_notMem b_fresh
                apply SMT.TypeContext.entries_subset_insert_of_notMem a_fresh
                apply SMT.TypeContext.entries_subset_insert_of_notMem p_fresh
                exact AList.subset_trans A_Λ_sub C_Λ_sub hv
              · intro v hv
                rw [St₃_used_eq, St₂_used_eq, St₁_used_eq]
                have hv' : v ∈ St₃.types := AList.mem_keys.mpr hv
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
                rw [St₃_used_eq, St₂_used_eq, St₁_used_eq]
                rcases hv with hv | hv
                · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                    (List.mem_cons_of_mem _ (C_used_sub (A_cov v hv))))
                · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                    (List.mem_cons_of_mem _ (C_cov v hv)))
              · intro v hv
                simp only [SMT.fv, List.mem_removeAll_iff, List.mem_append,
                  List.mem_cons, List.not_mem_nil, or_false] at hv
                obtain ⟨⟨hv1, hv_ne_ab⟩, hv_ne_p⟩ := hv
                rw [← AList.mem_keys, St₃_types_eq, AList.mem_insert,
                  AList.mem_insert, AList.mem_insert]
                rcases hv1 with (hvA | hva) | (hvC | hvb) | (hvp | hva | hvb)
                · have hvc : v ∈ ctx :=
                    AList.mem_of_subset C_Λ_sub (AList.mem_keys.mp (A_fv_sub hvA))
                  exact Or.inr (Or.inr (Or.inr hvc))
                · exact absurd (Or.inl hva) hv_ne_ab
                · have hvc : v ∈ ctx := AList.mem_keys.mp (C_fv_sub hvC)
                  exact Or.inr (Or.inr (Or.inr hvc))
                · exact absurd (Or.inr hvb) hv_ne_ab
                · exact absurd hvp hv_ne_p
                · exact absurd (Or.inl hva) hv_ne_ab
                · exact absurd (Or.inr hvb) hv_ne_ab
              · intro v hv hΛ hvars
                have hvA : v ∉ B.Term.vars A := fun h => hvars (by
                  simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
                    List.mem_append] at h ⊢
                  rcases h with h | h <;> [left; right] <;> exact .inl h)
                have hvC : v ∉ B.Term.vars C := fun h => hvars (by
                  simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
                    List.mem_append] at h ⊢
                  rcases h with h | h <;> [left; right] <;> exact .inr h)
                have hv_not_ctx : v ∉ ctx :=
                  C_preserves v (A_used_sub hv) (A_preserves v hv hΛ hvA) hvC
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
      · mspec C_ih (E := E) (Λ := σ_C.types) (used := σ_C.env.usedVars)
          (fun v hv => C_used_sub (A_used_sub (vars_used_C v hv))) hC_bv_nodup
        mvcgen
    · mspec A_ih (E := E) (Λ := σ_A.types) (used := σ_A.env.usedVars)
        (fun v hv => A_used_sub (vars_used_A v hv)) hA_bv_nodup
      mvcgen
  | mem x S x_ih S_ih => sorry
  | eq x y x_ih y_ih => sorry
  | union A C A_ih C_ih => sorry
  | inter A C A_ih C_ih => sorry
  | pfun A C A_ih C_ih =>
    mstart
    mintro pre ∀σ
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
    rw [encodeTerm]
    have hA_bv_nodup : (B.bv A).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.1
    have hC_bv_nodup : (B.bv C).Nodup := by
      have := bv_nodup; simp only [B.bv, List.nodup_append] at this; exact this.2.1
    have vars_used_A : ∀ v ∈ A.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h)
    have vars_used_C : ∀ v ∈ C.vars, v ∈ used := fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inr h)
    mspec A_ih (E := E) (Λ := σ.types) vars_used_A hA_bv_nodup
    rename_i out_A
    obtain ⟨A_enc, σA⟩ := out_A
    mrename_i preA
    mintro ∀σ_A
    mpure preA
    obtain ⟨A_used_sub, A_Λ_sub, A_keys_sub, A_cov, A_fv_sub, A_preserves⟩ := preA
    split
    · rename_i heq
      injection heq with hAe hσe
      subst hσe
      subst hAe
      mspec C_ih (E := E) (Λ := σ_A.types) (used := σ_A.env.usedVars)
        (fun v hv => A_used_sub (vars_used_C v hv)) hC_bv_nodup
      rename_i out_C
      obtain ⟨C_enc, σC⟩ := out_C
      mrename_i preC
      mintro ∀σ_C
      mpure preC
      obtain ⟨C_used_sub, C_Λ_sub, C_keys_sub, C_cov, C_fv_sub, C_preserves⟩ := preC
      split
      · rename_i heq2
        injection heq2 with hCe hσe2
        subst hσe2
        subst hCe
        set ctx := σ_C.types with hctx
        mspec freshVar_spec (Γ := ctx) (used := σ_C.env.usedVars)
        case post.success R =>
          mrename_i pre
          mintro ∀St₁
          mpure pre
          obtain ⟨St₁_types_eq, R_fresh, St₁_fvc_eq, St₁_used_eq, R_not_used⟩ := pre
          mspec freshVar_spec (Γ := ctx.insert R _) (used := St₁.env.usedVars)
          case post.success x =>
            mrename_i pre
            mintro ∀St₂
            mpure pre
            obtain ⟨St₂_types_eq, x_fresh, St₂_fvc_eq, St₂_used_eq, x_not_used⟩ := pre
            mspec freshVar_spec (Γ := (ctx.insert R _).insert x _) (used := St₂.env.usedVars)
            case post.success y =>
              mrename_i pre
              mintro ∀St₃
              mpure pre
              obtain ⟨St₃_types_eq, y_fresh, St₃_fvc_eq, St₃_used_eq, y_not_used⟩ := pre
              mspec freshVar_spec
                (Γ := ((ctx.insert R _).insert x _).insert y _) (used := St₃.env.usedVars)
              case post.success y' =>
                mrename_i pre
                mintro ∀St₄
                mpure pre
                obtain ⟨St₄_types_eq, y'_fresh, St₄_fvc_eq, St₄_used_eq, y'_not_used⟩ := pre
                mspec Std.Do.Spec.pure
                mpure_intro
                and_intros
                · intro v hv
                  rw [St₄_used_eq, St₃_used_eq, St₂_used_eq, St₁_used_eq]
                  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                      (C_used_sub (A_used_sub hv)))))
                · intro v hv
                  rw [St₄_types_eq]
                  apply SMT.TypeContext.entries_subset_insert_of_notMem y'_fresh
                  apply SMT.TypeContext.entries_subset_insert_of_notMem y_fresh
                  apply SMT.TypeContext.entries_subset_insert_of_notMem x_fresh
                  apply SMT.TypeContext.entries_subset_insert_of_notMem R_fresh
                  exact AList.subset_trans A_Λ_sub C_Λ_sub hv
                · intro v hv
                  rw [St₄_used_eq, St₃_used_eq, St₂_used_eq, St₁_used_eq]
                  have hv' : v ∈ St₄.types := AList.mem_keys.mpr hv
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
                  rw [St₄_used_eq, St₃_used_eq, St₂_used_eq, St₁_used_eq]
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
                  have hv_ctx : v ∈ ctx → v ∈ AList.keys St₄.types := fun hvc =>
                    AList.mem_keys.mp (by
                      rw [St₄_types_eq, AList.mem_insert, AList.mem_insert,
                        AList.mem_insert, AList.mem_insert]
                      exact Or.inr (Or.inr (Or.inr (Or.inr hvc))))
                  rcases hv_body with ⟨hv1, hv_ne_xy⟩ | ⟨hv2, hv_ne_xyy'⟩
                  · rcases hv1 with (hR | hx | hy) | (hvA | hx) | hvC | hy
                    · exact absurd hR hv_ne_R
                    · exact absurd (Or.inl hx) hv_ne_xy
                    · exact absurd (Or.inr hy) hv_ne_xy
                    · exact hv_ctx
                        (AList.mem_of_subset C_Λ_sub (AList.mem_keys.mp (A_fv_sub hvA)))
                    · exact absurd (Or.inl hx) hv_ne_xy
                    · exact hv_ctx (AList.mem_keys.mp (C_fv_sub hvC))
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
                  have hvA : v ∉ B.Term.vars A := fun h => hvars (by
                    simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
                      List.mem_append] at h ⊢
                    rcases h with h | h <;> [left; right] <;> exact .inl h)
                  have hvC : v ∉ B.Term.vars C := fun h => hvars (by
                    simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
                      List.mem_append] at h ⊢
                    rcases h with h | h <;> [left; right] <;> exact .inr h)
                  have hv_not_ctx : v ∉ ctx :=
                    C_preserves v (A_used_sub hv) (A_preserves v hv hΛ hvA) hvC
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
      · mvcgen
    · mvcgen
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
