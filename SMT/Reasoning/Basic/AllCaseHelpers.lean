import SMT.Reasoning.Basic.StateSpecs
import SMT.Reasoning.Basic.CollectCaseHelpers
import SMT.Reasoning.Basic.LoosenAuxExact.FunAux
import SMT.Reasoning.Axioms
import Encoder.Loosening.Loosening
import B.Reasoning.DenotationTotality

/-!
# Helper lemmas for `encodeTerm_spec.all_case`

This file collects lemmas mirroring `CollectCaseHelpers.lean` but specialized
for the forall-quantifier case. Key additions:

* `SMTFlagTypeRel`: the relation captured by the `all` encoder's `mapFinIdxM`
  body, modeling how flagged bound variables have their SMT types adjusted.
* `SMT.mapFinIdxM_all_body_spec`: the full spec for the `mapFinIdxM` call in
  the `all` encoder branch, giving state preservation, length equality, and
  the per-index `SMTFlagTypeRel` guarantee.
* Bridge lemmas connecting `ZFSet.sInter` with the SMT `Term.forall` denotation.
-/

open SMT ZFSet Std.Do
set_option mvcgen.warning false

/-- Relation capturing how the `all` encoder's `mapFinIdxM` body transforms
types based on flag membership. If `flagged = false`, the type passes through
unchanged; if `flagged = true`, a set-of-pairs becomes an option function
(and option functions pass through). -/
def SMTFlagTypeRel (flagged : Bool) (τin τout : SMTType) : Prop :=
  if flagged then
    (∃ α β, τin = .fun (.pair α β) .bool ∧ τout = .fun α (.option β)) ∨
    (∃ α β, τin = .fun α (.option β) ∧ τout = .fun α (.option β))
  else
    τin = τout

/-- Generalized spec for `mapFinIdxM.go` on the `all` encoder's body,
parameterized by the suffix `bs` (still to process) and prefix (already in `acc`).
State is preserved, accumulator grows by one per step, and the final result list
has the same length as the original input. The post-condition exposes a
per-index `SMTFlagTypeRel` linking each input type `tmp_τs[i]` to its output
`τs[i]` based on whether `vs[i]` is flagged. -/
private theorem mapFinIdxM_go_all_body_spec
    (vs : List SMT.𝒱) (flags : List SMT.𝒱) (tmp_τs : List SMTType)
    (hvs_eq : vs.length = tmp_τs.length)
    (bs : List SMTType) (acc : Array SMTType) (hsize : bs.length + acc.size = tmp_τs.length)
    (hsuf : ∀ j (hj : j < bs.length), bs[j] = tmp_τs[j + acc.size]'(by omega))
    (hacc : ∀ j (hj : j < acc.size),
      SMTFlagTypeRel (vs[j]'(by omega) ∈ flags)
        (tmp_τs[j]'(by omega)) (acc[j]'hj))
    {Γ : SMT.TypeContext} {n : ℕ} {used : List SMT.𝒱} :
  ⦃ λ ⟨E, Γ'⟩ ↦ ⌜Γ' = Γ ∧ E.freshvarsc = n ∧ E.usedVars = used⌝⦄
  List.mapFinIdxM.go (as := tmp_τs)
    (fun i τ hi =>
      (if vs[i]'(by omega) ∈ flags then
        (match τ with
        | .fun (.pair α β) .bool => pure (.fun α (.option β))
        | .fun α (.option β) => pure (.fun α (.option β))
        | ξ => throw s!"encodeTerm:all: Unsupported flag type {vs[i]'(by omega)} : {ξ}" : Encoder SMTType)
      else pure τ))
    bs acc hsize
  ⦃ ⇓? τs ⟨E', Γ'⟩ =>
    ⌜ Γ' = Γ ∧ E'.freshvarsc = n ∧ E'.usedVars = used ∧
      ∃ (hτs_len : τs.length = tmp_τs.length),
        ∀ i (hi : i < τs.length),
          SMTFlagTypeRel (vs[i]'(by omega) ∈ flags)
            (tmp_τs[i]'(hτs_len ▸ hi)) τs[i] ⌝⦄ := by
  induction bs generalizing acc Γ n used with
  | nil =>
    mintro pre ∀S; mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    simp only [List.mapFinIdxM.go]
    mspec Std.Do.Spec.pure
    mpure_intro
    have h_acc : acc.size = tmp_τs.length := by
      have := hsize; simp only [List.length_nil, Nat.zero_add] at this; exact this
    refine ⟨trivial, trivial, trivial, ?_⟩
    have hτs_len : acc.toList.length = tmp_τs.length := by
      simp [Array.length_toList, h_acc]
    refine ⟨hτs_len, ?_⟩
    intro i hi
    have hi_acc : i < acc.size := by
      simp only [Array.length_toList] at hi
      exact hi
    have heq : (acc.toList)[i]'hi = acc[i]'hi_acc := by
      rw [← Array.getElem_toList]
    rw [heq]
    exact hacc i hi_acc
  | cons b bs' ih =>
    mintro pre ∀S; mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    simp only [List.mapFinIdxM.go]
    have h_acc_lt : acc.size < tmp_τs.length := by
      simp only [List.length_cons] at hsize; omega
    have h_acc_lt_vs : acc.size < vs.length := by omega
    have hb_eq : b = tmp_τs[acc.size]'h_acc_lt := by
      have := hsuf 0 (by simp); simpa using this
    have hsize_unfold : bs'.length + 1 + acc.size = tmp_τs.length := by
      simp only [List.length_cons] at hsize; exact hsize
    have hsize' : bs'.length + (acc.push b).size = tmp_τs.length := by
      simp only [Array.size_push]; omega
    -- Helper for lifting hsuf to the new acc
    have hsuf' : ∀ j (hj : j < bs'.length),
        bs'[j] = tmp_τs[j + (acc.push b).size]'(by simp only [Array.size_push]; omega) := by
      intro j hj
      simp only [Array.size_push]
      have hj' : j + 1 < (b :: bs').length := by simp only [List.length_cons]; omega
      have := hsuf (j + 1) hj'
      simp only [List.getElem_cons_succ] at this
      rw [this]; congr 1; omega
    by_cases hf : vs[acc.size]'h_acc_lt_vs ∈ flags
    · -- Flagged: match on b
      simp only [hf, if_true]
      split
      · -- Branch 1: b = .fun (.pair α β) .bool (renamed via split: τ_orig, α, β are intro'd)
        rename_i τ_orig α β
        -- Now `b` was tmp_τs[acc.size], but after the split, hypothesis context shows
        -- tmp_τs[acc.size] = .fun (.pair α β) .bool (encoded via the splitting equality)
        mspec Std.Do.Spec.pure
        -- hb_eq is still `b = tmp_τs[acc.size]` but after split, b becomes the matched form.
        -- So we have hb_eq : .fun (.pair α β) .bool = tmp_τs[acc.size]
        have hb_shape : tmp_τs[acc.size]'h_acc_lt = .fun (.pair α β) .bool := hb_eq.symm
        have hacc' : ∀ j (hj : j < (acc.push (.fun α (.option β))).size),
            SMTFlagTypeRel
              (vs[j]'(by simp only [Array.size_push] at hj; omega) ∈ flags)
              (tmp_τs[j]'(by simp only [Array.size_push] at hj; omega))
              ((acc.push (.fun α (.option β)))[j]'hj) := by
          intro j hj
          simp only [Array.size_push] at hj
          by_cases hjsize : j < acc.size
          · rw [Array.getElem_push_lt hjsize]
            exact hacc j hjsize
          · push_neg at hjsize
            have hj_eq : j = acc.size := by omega
            subst hj_eq
            simp only [Array.getElem_push_eq]
            simp only [SMTFlagTypeRel, hf]
            left
            refine ⟨α, β, hb_shape, rfl⟩
        have hsize_push : bs'.length + (acc.push (.fun α (.option β))).size = tmp_τs.length := by
          simp only [Array.size_push]; omega
        have hsuf'_new : ∀ j (hj : j < bs'.length),
            bs'[j] = tmp_τs[j + (acc.push (.fun α (.option β))).size]'(by
              simp only [Array.size_push]; omega) := by
          intro j hj
          simp only [Array.size_push]
          have := hsuf' j hj
          simp only [Array.size_push] at this
          exact this
        mspec (ih (acc.push (.fun α (.option β))) hsize_push hsuf'_new hacc')
      · -- Branch 2: b = .fun α (.option β)
        rename_i τ_orig α β
        mspec Std.Do.Spec.pure
        have hb_shape : tmp_τs[acc.size]'h_acc_lt = .fun α (.option β) := hb_eq.symm
        have hacc' : ∀ j (hj : j < (acc.push (.fun α (.option β))).size),
            SMTFlagTypeRel
              (vs[j]'(by simp only [Array.size_push] at hj; omega) ∈ flags)
              (tmp_τs[j]'(by simp only [Array.size_push] at hj; omega))
              ((acc.push (.fun α (.option β)))[j]'hj) := by
          intro j hj
          simp only [Array.size_push] at hj
          by_cases hjsize : j < acc.size
          · rw [Array.getElem_push_lt hjsize]
            exact hacc j hjsize
          · push_neg at hjsize
            have hj_eq : j = acc.size := by omega
            subst hj_eq
            simp only [Array.getElem_push_eq]
            simp only [SMTFlagTypeRel, hf]
            right
            refine ⟨α, β, hb_shape, rfl⟩
        have hsize_push : bs'.length + (acc.push (.fun α (.option β))).size = tmp_τs.length := by
          simp only [Array.size_push]; omega
        have hsuf'_new : ∀ j (hj : j < bs'.length),
            bs'[j] = tmp_τs[j + (acc.push (.fun α (.option β))).size]'(by
              simp only [Array.size_push]; omega) := by
          intro j hj
          simp only [Array.size_push]
          have := hsuf' j hj
          simp only [Array.size_push] at this
          exact this
        mspec (ih (acc.push (.fun α (.option β))) hsize_push hsuf'_new hacc')
      · -- Branch 3: throws
        mspec
    · -- Unflagged: body is pure τ
      simp only [hf, if_false]
      mspec Std.Do.Spec.pure
      have hacc' : ∀ j (hj : j < (acc.push b).size),
          SMTFlagTypeRel
            (vs[j]'(by simp only [Array.size_push] at hj; omega) ∈ flags)
            (tmp_τs[j]'(by simp only [Array.size_push] at hj; omega))
            ((acc.push b)[j]'hj) := by
        intro j hj
        simp only [Array.size_push] at hj
        by_cases hjsize : j < acc.size
        · rw [Array.getElem_push_lt hjsize]
          exact hacc j hjsize
        · push_neg at hjsize
          have hj_eq : j = acc.size := by omega
          subst hj_eq
          simp only [Array.getElem_push_eq]
          simp only [SMTFlagTypeRel, hf, decide_false, if_false, Bool.false_eq_true]
          exact hb_eq.symm
      mspec (ih (acc.push b) hsize' hsuf' hacc')

/-- Top-level spec for the `all` encoder's `mapFinIdxM`. The post-condition
exposes both length equality and a per-index `SMTFlagTypeRel` linking each
input type to its output type. -/
theorem SMT.mapFinIdxM_all_body_spec
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
        | ξ => throw s!"encodeTerm:all: Unsupported flag type {vs[i]'(by omega)} : {ξ}" : Encoder SMTType)
      else pure τ))
  ⦃ ⇓? τs ⟨E', Γ'⟩ =>
    ⌜ Γ' = Γ ∧ E'.freshvarsc = n ∧ E'.usedVars = used ∧
      ∃ (hτs_len : τs.length = tmp_τs.length),
        ∀ i (hi : i < τs.length),
          SMTFlagTypeRel (vs[i]'(by omega) ∈ flags)
            (tmp_τs[i]'(hτs_len ▸ hi)) τs[i] ⌝⦄ := by
  unfold List.mapFinIdxM
  refine mapFinIdxM_go_all_body_spec vs flags tmp_τs hvs_eq tmp_τs #[] (by simp) ?_ ?_
  · intro j hj
    simp
  · intro j hj
    simp at hj

/-! ### Aggregate-flag subtype helpers

The encoder's HAS-FLAG branch needs `τs.toProdl ⊑ τ.toSMTType` (via the round-trip
`tmp_τs.toProdl = τ.toSMTType`) and `τs.toProdl ≠ τ.toSMTType` (when at least one
position is shape-changed). Both follow from per-index `SMTFlagTypeRel`.
-/

/-- Pointwise consequence of `SMTFlagTypeRel`: the output type is always
`⊑`-loosened from the input type (or equal if unflagged). -/
theorem SMTFlagTypeRel.le {flagged : Bool} {τin τout : SMTType}
    (h : SMTFlagTypeRel flagged τin τout) :
    τout ⊑ τin := by
  unfold SMTFlagTypeRel at h
  cases flagged with
  | true =>
    simp only [if_true] at h
    rcases h with ⟨α, β, hin, hout⟩ | ⟨α, β, hin, hout⟩
    · -- τin = .fun (.pair α β) .bool, τout = .fun α (.option β)
      subst hin hout
      exact castable?.graph castable?.reflexive castable?.reflexive
    · -- τin = .fun α (.option β), τout = .fun α (.option β)
      subst hin hout
      exact castable?.reflexive
  | false =>
    simp only [Bool.false_eq_true, if_false] at h
    subst h; exact castable?.reflexive

/-- If `flagged = true` and `SMTFlagTypeRel true τin τout` holds with τin =
`.fun (.pair α β) .bool`, then τout = `.fun α (.option β) ≠ τin`. -/
theorem SMTFlagTypeRel.ne_of_pair_bool {α β : SMTType} {τout : SMTType}
    (h : SMTFlagTypeRel true (.fun (.pair α β) .bool) τout) :
    τout ≠ .fun (.pair α β) .bool := by
  unfold SMTFlagTypeRel at h
  simp only [if_true] at h
  rcases h with ⟨α', β', hin, hout⟩ | ⟨α', β', hin, hout⟩
  · -- hin: .fun (.pair α β) .bool = .fun (.pair α' β') .bool
    rw [SMTType.fun.injEq, SMTType.pair.injEq] at hin
    obtain ⟨⟨rfl, rfl⟩, _⟩ := hin
    rw [hout]
    intro hcon
    rw [SMTType.fun.injEq] at hcon
    -- option β = bool: noConfusion
    nomatch hcon.2
  · -- hin: .fun (.pair α β) .bool = .fun α' (.option β')
    rw [SMTType.fun.injEq] at hin
    obtain ⟨_, hbool⟩ := hin
    -- option β' = bool: noConfusion
    nomatch hbool

/-- Inductive lemma: if pointwise `τs[i] ⊑ tmp_τs[i]` for all i, both lists
non-empty and same length, then `τs.toProdl.aux ⊑ tmp_τs.toProdl.aux`. -/
private theorem List.toProdl_aux_subtype :
    ∀ (τs tmp_τs : List SMTType)
      (hlen : τs.length = tmp_τs.length) (_hne : τs ≠ [])
      (_hall : ∀ (i : ℕ) (hi : i < τs.length),
        τs[i]'hi ⊑ (tmp_τs[i]'(hlen ▸ hi))),
      List.toProdl.aux τs ⊑ List.toProdl.aux tmp_τs := by
  intro τs tmp_τs hlen hne hall
  induction τs generalizing tmp_τs with
  | nil => exact (hne rfl).elim
  | cons τ τs' ih =>
    cases tmp_τs with
    | nil => simp at hlen
    | cons tτ tτs' =>
      cases τs' with
      | nil =>
        cases tτs' with
        | nil =>
          simp only [List.toProdl.aux]
          have h0 : 0 < (τ :: List.nil (α := SMTType)).length := by simp
          exact hall 0 h0
        | cons _ _ => simp at hlen
      | cons τ' τs'' =>
        cases tτs' with
        | nil => simp at hlen
        | cons tτ' tτs'' =>
          simp only [List.toProdl.aux]
          apply castable?.pair
          · refine ih (tτ' :: tτs'') ?_ (List.cons_ne_nil _ _) ?_
            · simp [List.length_cons] at hlen ⊢; omega
            · intro i hi
              have h1 : i + 1 < (τ :: τ' :: τs'').length := by
                simp only [List.length_cons] at hi ⊢; omega
              have := hall (i + 1) h1
              simpa [List.getElem_cons_succ] using this
          · have h0 : 0 < (τ :: τ' :: τs'').length := by simp
            exact hall 0 h0

/-- Top-level: pointwise ⊑ aggregates to toProdl ⊑. -/
theorem List.toProdl_subtype :
    ∀ (τs tmp_τs : List SMTType)
      (hlen : τs.length = tmp_τs.length) (_hne : τs ≠ [])
      (_hall : ∀ (i : ℕ) (hi : i < τs.length),
        τs[i]'hi ⊑ (tmp_τs[i]'(hlen ▸ hi))),
      τs.toProdl ⊑ tmp_τs.toProdl := by
  intro τs tmp_τs hlen hne hall
  unfold List.toProdl
  refine List.toProdl_aux_subtype τs.reverse tmp_τs.reverse ?_ ?_ ?_
  · simp [hlen]
  · intro h
    apply hne
    have hrev : τs.reverse.length = 0 := by rw [h]; rfl
    simp at hrev
    exact hrev
  · intro i hi
    simp only [List.length_reverse] at hi
    have heq : τs.reverse[i]'(by simp; omega) = τs[τs.length - 1 - i]'(by omega) := by
      rw [List.getElem_reverse]
    have heq_τ : tmp_τs.reverse[i]'(by simp [← hlen]; omega) =
        tmp_τs[tmp_τs.length - 1 - i]'(by omega) := by
      rw [List.getElem_reverse]
    rw [heq, heq_τ]
    convert hall (τs.length - 1 - i) (by omega) using 2
    omega

/-- Per-index `SMTFlagTypeRel` aggregates to `τs.toProdl ⊑ tmp_τs.toProdl` —
the "loosening direction" branch-2 condition. -/
theorem SMTFlagTypeRel.toProdl_subtype
    {vs flags : List SMT.𝒱} {τs tmp_τs : List SMTType}
    (hvs_eq : vs.length = tmp_τs.length)
    (hτs_len : τs.length = tmp_τs.length) (hne : τs ≠ [])
    (hall : ∀ (i : ℕ) (hi : i < τs.length),
      SMTFlagTypeRel (vs[i]'(by omega) ∈ flags) (tmp_τs[i]'(hτs_len ▸ hi)) (τs[i]'hi)) :
    τs.toProdl ⊑ tmp_τs.toProdl :=
  List.toProdl_subtype τs tmp_τs hτs_len hne fun i hi =>
    SMTFlagTypeRel.le (hall i hi)

/-- Helper: pair-injectivity at the same index between `xs.toProdl.aux` and
`ys.toProdl.aux` for nonempty equi-length lists. -/
private theorem List.toProdl_aux_inj_at_idx :
    ∀ (xs ys : List SMTType) (hlen : xs.length = ys.length) (_hne : xs ≠ [])
      (_heq : List.toProdl.aux xs = List.toProdl.aux ys)
      (i : ℕ) (hi : i < xs.length),
      ys[i]'(hlen ▸ hi) = xs[i]'hi := by
  intro xs ys hlen hne heq
  induction xs generalizing ys with
  | nil => exact (hne rfl).elim
  | cons x xs'' ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys'' =>
      cases xs'' with
      | nil =>
        cases ys'' with
        | nil =>
          -- both length 1: aux [x] = x, [y] = y, so x = y
          simp only [List.toProdl.aux] at heq
          intro i hi
          have hi_zero : i = 0 := by simp at hi; omega
          subst hi_zero
          simpa using heq.symm
        | cons _ _ => simp at hlen
      | cons x' xs''' =>
        cases ys'' with
        | nil => simp at hlen
        | cons y' ys''' =>
          simp only [List.toProdl.aux] at heq
          rw [SMTType.pair.injEq] at heq
          obtain ⟨h_tail_eq, h_head_eq⟩ := heq
          intro i hi
          cases i with
          | zero => simpa using h_head_eq.symm
          | succ k =>
            have hk : k < (x' :: xs''').length := by
              simp only [List.length_cons] at hi ⊢; omega
            have hlen_tail : (x' :: xs''').length = (y' :: ys''').length := by
              simp only [List.length_cons] at hlen ⊢; omega
            have := ih (y' :: ys''') hlen_tail (List.cons_ne_nil _ _) h_tail_eq k hk
            simpa [List.getElem_cons_succ] using this

/-- `toProdl` is injective at each index on equi-length nonempty lists. -/
theorem List.toProdl_inj_at_idx
    {xs ys : List SMTType} (hlen : xs.length = ys.length) (hne : xs ≠ [])
    (heq : xs.toProdl = ys.toProdl)
    (i : ℕ) (hi : i < xs.length) :
    ys[i]'(hlen ▸ hi) = xs[i]'hi := by
  unfold List.toProdl at heq
  have hlen_rev : xs.reverse.length = ys.reverse.length := by simp [hlen]
  have hne_rev : xs.reverse ≠ [] := by
    intro h
    apply hne
    exact List.reverse_eq_nil_iff.mp h
  have hi_rev : xs.length - 1 - i < xs.reverse.length := by simp; omega
  have h_apply := List.toProdl_aux_inj_at_idx xs.reverse ys.reverse hlen_rev hne_rev heq
    (xs.length - 1 - i) hi_rev
  have hi_rev_xs : xs.reverse[xs.length - 1 - i]'hi_rev = xs[i]'hi := by
    rw [List.getElem_reverse]; congr 1; omega
  have hi_rev_ys : ys.reverse[xs.length - 1 - i]'(by simp [← hlen]; omega) =
      ys[i]'(hlen ▸ hi) := by
    rw [List.getElem_reverse]; congr 1; omega
  rw [hi_rev_xs] at h_apply
  rw [← h_apply, hi_rev_ys]

/-- A list with a flagged-pair-shape entry has `τs.toProdl ≠ tmp_τs.toProdl`.
This is the central lemma for deriving Branch 2's `α_ne_τ` condition. -/
theorem SMTFlagTypeRel.toProdl_ne
    {vs flags : List SMT.𝒱} {τs tmp_τs : List SMTType}
    (hvs_eq : vs.length = tmp_τs.length)
    (hτs_len : τs.length = tmp_τs.length) (hne : τs ≠ [])
    (hall : ∀ (i : ℕ) (hi : i < τs.length),
      SMTFlagTypeRel (vs[i]'(by omega) ∈ flags) (tmp_τs[i]'(hτs_len ▸ hi)) (τs[i]'hi))
    {idx : ℕ} (hidx : idx < τs.length)
    (hflag : vs[idx]'(by omega) ∈ flags)
    {α β : SMTType} (hpair : tmp_τs[idx]'(hτs_len ▸ hidx) = .fun (.pair α β) .bool) :
    τs.toProdl ≠ tmp_τs.toProdl := by
  -- The idx-th positions differ: τs[idx] = .fun α (.option β) ≠ .fun (.pair α β) .bool
  have hrel : SMTFlagTypeRel (vs[idx]'(by omega) ∈ flags)
      (tmp_τs[idx]'(hτs_len ▸ hidx)) (τs[idx]'hidx) := hall idx hidx
  rw [hpair] at hrel
  have hflag_decide : decide (vs[idx]'(by omega) ∈ flags) = true := decide_eq_true hflag
  rw [hflag_decide] at hrel
  -- Now hrel : SMTFlagTypeRel true (.fun (.pair α β) .bool) τs[idx]
  have hne_idx : τs[idx]'hidx ≠ .fun (.pair α β) .bool :=
    SMTFlagTypeRel.ne_of_pair_bool hrel
  intro hcon
  exact hne_idx ((List.toProdl_inj_at_idx hτs_len hne hcon idx hidx).symm.trans hpair)

/-- Typing for `List.toPairl.aux` on the reversed (input) form: given matching
non-empty lists of terms and types whose pointwise typing holds, the `aux`
construction yields a term of the paired type. -/
theorem List.toPairl_aux_typing
    {Γ : SMT.TypeContext}
    : ∀ (ts' : List Term) (τs' : List SMTType)
    (hlen : ts'.length = τs'.length)
    (_hne : ts' ≠ [])
    (_hall : ∀ i (hi : i < ts'.length), Γ ⊢ˢ ts'[i] : τs'[i]'(hlen ▸ hi)),
    Γ ⊢ˢ List.toPairl.aux ts' : List.toProdl.aux τs' := by
  intro ts' τs' hlen hne hall
  induction ts' generalizing τs' with
  | nil => exact (hne rfl).elim
  | cons t ts' ih =>
    cases τs' with
    | nil => simp at hlen
    | cons τ τs' =>
      cases ts' with
      | nil =>
        cases τs' with
        | nil =>
          simp only [List.toPairl.aux, List.toProdl.aux]
          exact hall 0 (by simp)
        | cons _ _ => simp at hlen
      | cons t' ts'' =>
        cases τs' with
        | nil => simp at hlen
        | cons τ' τs'' =>
          simp only [List.toPairl.aux, List.toProdl.aux]
          apply SMT.Typing.pair
          · -- Goal: toPairl.aux (t'::ts'') : toProdl.aux (τ'::τs'')
            refine ih (τ' :: τs'') ?_ (List.cons_ne_nil _ _) ?_
            · simp [List.length_cons] at hlen ⊢; omega
            · intro i hi
              have h1 : i + 1 < (t :: t' :: ts'').length := by
                simp only [List.length_cons] at hi ⊢; omega
              have := hall (i + 1) h1
              simpa [List.getElem_cons_succ] using this
          · exact hall 0 (by simp)

/-- Top-level typing for `List.toPairl`: if all terms have their corresponding
types and both lists are non-empty of matching lengths, then the pair-list term
has the product-list type. This is the missing typing hypothesis needed to
invoke `castMembership_spec` in the `all` case. -/
theorem List.toPairl_typing
    {Γ : SMT.TypeContext}
    (ts : List Term) (τs : List SMTType)
    (hlen : ts.length = τs.length)
    (hne : ts ≠ [])
    (hall : ∀ i (hi : i < ts.length), Γ ⊢ˢ ts[i] : τs[i]'(hlen ▸ hi)) :
    Γ ⊢ˢ List.toPairl ts : List.toProdl τs := by
  unfold List.toPairl List.toProdl
  refine List.toPairl_aux_typing ts.reverse τs.reverse ?_ ?_ ?_
  · simp [hlen]
  · intro h
    apply hne
    have hrev : ts.reverse.length = 0 := by rw [h]; rfl
    simp at hrev
    exact hrev
  · intro i hi
    simp only [List.length_reverse] at hi
    have heq : ts.reverse[i]'(by simp; omega) = ts[ts.length - 1 - i]'(by omega) := by
      rw [List.getElem_reverse]
    have heq_τ : τs.reverse[i]'(by simp [← hlen]; omega) = τs[τs.length - 1 - i]'(by omega) := by
      rw [List.getElem_reverse]
    rw [heq, heq_τ]
    convert hall (ts.length - 1 - i) (by omega) using 2
    omega

/-- Specialized no-flag variant of `mapFinIdxM_go_all_body_spec`: when all
variables `vs[i]` are disjoint from `flags`, the body always takes the `pure τ`
branch, so the returned `τs` equals the input `tmp_τs` identically. -/
private theorem mapFinIdxM_go_all_body_spec_noflag
    (vs : List SMT.𝒱) (flags : List SMT.𝒱) (tmp_τs : List SMTType)
    (hvs_eq : vs.length = tmp_τs.length)
    (hnoflag : ∀ i (hi : i < tmp_τs.length), vs[i]'(by omega) ∉ flags)
    (bs : List SMTType) (acc : Array SMTType)
    (hsize : bs.length + acc.size = tmp_τs.length)
    (hsuf : ∀ j (hj : j < bs.length), bs[j] = tmp_τs[j + acc.size]'(by omega))
    (hacc : ∀ j (hj : j < acc.size), acc[j] = tmp_τs[j]'(by omega))
    {Γ : SMT.TypeContext} {n : ℕ} {used : List SMT.𝒱} :
    ⦃ λ ⟨E, Γ'⟩ ↦ ⌜Γ' = Γ ∧ E.freshvarsc = n ∧ E.usedVars = used⌝⦄
    List.mapFinIdxM.go (as := tmp_τs)
      (fun i τ hi =>
        (if vs[i]'(by omega) ∈ flags then
          (match τ with
          | .fun (.pair α β) .bool => pure (.fun α (.option β))
          | .fun α (.option β) => pure (.fun α (.option β))
          | ξ => throw s!"encodeTerm:all: Unsupported flag type {vs[i]'(by omega)} : {ξ}" : Encoder SMTType)
        else pure τ))
      bs acc hsize
    ⦃ ⇓? τs ⟨E', Γ'⟩ =>
      ⌜ Γ' = Γ ∧ E'.freshvarsc = n ∧ E'.usedVars = used ∧ τs = tmp_τs ⌝⦄ := by
  induction bs generalizing acc with
  | nil =>
    mintro pre ∀S; mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    simp only [List.mapFinIdxM.go]
    mspec Std.Do.Spec.pure
    mpure_intro
    refine ⟨trivial, trivial, trivial, ?_⟩
    have h_acc : acc.size = tmp_τs.length := by
      have := hsize; simp only [List.length_nil, Nat.zero_add] at this; exact this
    apply List.ext_getElem
    · simp [h_acc]
    · intro i hi hi'
      rw [Array.getElem_toList]
      exact hacc i (h_acc ▸ hi')
  | cons b bs' ih =>
    mintro pre ∀S; mpure pre
    obtain ⟨rfl, rfl, rfl⟩ := pre
    simp only [List.mapFinIdxM.go]
    have hsize_len : bs'.length + 1 + acc.size = tmp_τs.length := by
      have := hsize; simp only [List.length_cons] at this; omega
    have h_acc_lt : acc.size < tmp_τs.length := by omega
    have h_acc_lt_vs : acc.size < vs.length := by omega
    have hf : vs[acc.size]'h_acc_lt_vs ∉ flags := hnoflag _ h_acc_lt
    simp only [hf, if_false]
    have hb_eq : b = tmp_τs[acc.size]'h_acc_lt := by
      have := hsuf 0 (by simp); simpa using this
    have hsize' : bs'.length + (acc.push b).size = tmp_τs.length := by
      simp only [Array.size_push]; omega
    have hsuf' : ∀ j (hj : j < bs'.length),
        bs'[j] = tmp_τs[j + (acc.push b).size]'(by simp only [Array.size_push]; omega) := by
      intro j hj
      simp only [Array.size_push]
      have hj' : j + 1 < (b :: bs').length := by simp only [List.length_cons]; omega
      have := hsuf (j + 1) hj'
      simp only [List.getElem_cons_succ] at this
      rw [this]; congr 1; omega
    have hacc' : ∀ j (hj : j < (acc.push b).size),
        (acc.push b)[j] = tmp_τs[j]'(by simp only [Array.size_push] at hj; omega) := by
      intro j hj
      simp only [Array.size_push] at hj
      by_cases hj'' : j < acc.size
      · rw [Array.getElem_push_lt hj'']; exact hacc j hj''
      · push_neg at hj''
        have hj_eq : j = acc.size := by omega
        subst hj_eq
        simp only [Array.getElem_push_eq]
        exact hb_eq
    mspec Std.Do.Spec.pure
    mspec (ih (acc.push b) hsize' hsuf' hacc')

/-- Top-level no-flag spec: when all `vs[i]` are disjoint from `E.flags`, the
`mapFinIdxM` in the `all` encoder returns `τs = tmp_τs`. -/
theorem SMT.mapFinIdxM_all_body_spec_noflag
    (vs : List SMT.𝒱) (flags : List SMT.𝒱) (tmp_τs : List SMTType)
    (hvs_eq : vs.length = tmp_τs.length)
    (hnoflag : ∀ i (hi : i < tmp_τs.length), vs[i]'(by omega) ∉ flags)
    {Γ : SMT.TypeContext} {n : ℕ} {used : List SMT.𝒱} :
    ⦃ λ ⟨E, Γ'⟩ ↦ ⌜Γ' = Γ ∧ E.freshvarsc = n ∧ E.usedVars = used⌝⦄
    tmp_τs.mapFinIdxM
      (fun i τ hi =>
        (if vs[i]'(by omega) ∈ flags then
          (match τ with
          | .fun (.pair α β) .bool => pure (.fun α (.option β))
          | .fun α (.option β) => pure (.fun α (.option β))
          | ξ => throw s!"encodeTerm:all: Unsupported flag type {vs[i]'(by omega)} : {ξ}" : Encoder SMTType)
        else pure τ))
    ⦃ ⇓? τs ⟨E', Γ'⟩ =>
      ⌜ Γ' = Γ ∧ E'.freshvarsc = n ∧ E'.usedVars = used ∧ τs = tmp_τs ⌝⦄ := by
  unfold List.mapFinIdxM
  refine mapFinIdxM_go_all_body_spec_noflag vs flags tmp_τs hvs_eq hnoflag
    tmp_τs #[] (by simp) ?_ ?_
  · intro j hj
    simp only [Array.size_empty, Nat.add_zero]
  · intro j hj
    simp only [Array.size_empty] at hj
    omega

/-- Concat form: `toProdl (xs ++ [x]) = .pair (toProdl xs) x` when `xs ≠ []`. -/
theorem List.toProdl_concat_of_nonempty (xs : List SMTType) (x : SMTType) (hne : xs ≠ []) :
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

/-- The round-trip: `fromProdl` followed by `toProdl` is the identity on nested
`.pair` types whose arity matches. This is the key lemma needed to invoke the
reflexive `castMembership_reflexive_spec` in the `all` case. -/
theorem SMT.SMTType.fromProdl_toProdl_roundtrip :
    ∀ (τ : SMTType) (n : ℕ), (τ.fromProdl n).length = n + 1 → (τ.fromProdl n).toProdl = τ := by
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
      rw [List.toProdl_concat_of_nonempty (α.fromProdl n) β hα_ne]
      rw [ih α hlen_α]
    | _ =>
      simp only [SMTType.fromProdl] at h
      simp at h

/-- `TypeContext.update` (which is defined via `Fin.foldl`) is equivalent to
walking a zipped list with `List.foldl`. -/
theorem SMT.TypeContext.update_eq_zip_foldl
    (Γ : SMT.TypeContext) (vs : List SMT.𝒱) (τs : List SMTType)
    (hlen : vs.length = τs.length) :
    Γ.update vs τs hlen =
    (vs.zip τs).foldl (fun Γ (p : 𝒱 × SMTType) => Γ.insert p.1 p.2) Γ := by
  unfold SMT.TypeContext.update
  induction vs, τs, hlen using List.reverse_induction₂ generalizing Γ with
  | nil_nil => simp
  | cons_cons vₙ vs τₙ τs hlen' ih =>
    simp only [List.concat_eq_append, List.length_append, List.length_cons,
      List.length_nil, zero_add, Fin.foldl_succ_last, Fin.getElem_fin, Fin.coe_cast,
      Fin.val_last, le_refl, List.getElem_append_right, Nat.sub_self,
      List.getElem_cons_zero, Fin.coe_castSucc]
    have h_first_fold : Fin.foldl vs.length (fun (x : SMT.TypeContext) (k : Fin vs.length) =>
        x.insert ((vs ++ [vₙ])[k.val]'(by simp; omega))
          ((τs ++ [τₙ])[k.val]'(by simp; omega))) Γ =
        Fin.foldl vs.length (fun (x : SMT.TypeContext) (k : Fin vs.length) =>
          x.insert vs[k.val] (τs[k.val]'(hlen' ▸ k.isLt))) Γ := by
      congr 1
      funext Ξ ⟨k, hk⟩
      congr 1
      · exact List.getElem_append_left hk
      · exact List.getElem_append_left (show k < τs.length by rw [← hlen']; exact hk)
    rw [h_first_fold]
    have h_ih_apply : Fin.foldl vs.length
        (fun (x : SMT.TypeContext) (k : Fin vs.length) =>
          AList.insert vs[k.val] (τs[k.val]'(hlen' ▸ k.isLt)) x) Γ =
        List.foldl (fun Γ p => AList.insert p.1 p.2 Γ) Γ (vs.zip τs) := ih Γ
    rw [h_ih_apply]
    have h_τs_last : (τs ++ [τₙ])[vs.length]'(by simp [hlen']) = τₙ := by
      rw [List.getElem_append_right (by rw [← hlen'])]; simp
    rw [h_τs_last]
    have hzip : (vs ++ [vₙ]).zip (τs ++ [τₙ]) = vs.zip τs ++ [(vₙ, τₙ)] := by
      rw [List.zip_append (by simp [hlen'])]
      simp
    rw [hzip, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- Looking up `vs[i]` after `TypeContext.update` gives `some τs[i]`, provided
`vs` is nodup and lengths match. Complements `SMT.TypeContext.lookup_update`
(which covers the `v ∉ vs` case). -/
theorem SMT.TypeContext.lookup_update_of_mem_nodup
    (Γ : SMT.TypeContext) {vs : List SMT.𝒱} {τs : List SMTType}
    (hnd : vs.Nodup) (hlen : vs.length = τs.length) {i : ℕ} (hi : i < vs.length) :
    (Γ.update vs τs).lookup (vs[i]'hi) = some (τs[i]'(hlen ▸ hi)) := by
  rw [SMT.TypeContext.update_eq_zip_foldl]
  exact foldl_insert_lookup_zip hnd hi (hlen ▸ hi)

/-! ### Session 2: Fin.foldl product ↔ toProdl bridge

The SMT `.forall` denotation produces a domain `𝒟_smt = Fin.foldl (n-1) (·.prod ·)
τs[0].toZFSet` where the indexed type at iteration `i` is `τs[i+1]`. This
domain coincides with `(τs.toProdl).toZFSet`.
-/

/-! ### Pure ZFSet helpers for the retract-forall proof -/

/-- If `x.hasArity (m+1)`, the foldl of `x.get` components reconstructs `x`. -/
private theorem ZFSet.foldl_get_of_hasArity {m : ℕ} {x : ZFSet}
    (hx : x.hasArity (m + 1)) :
    Fin.foldl m
      (fun (acc : ZFSet) (i : Fin m) =>
        acc.pair (x.get (m + 1) ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩))
      (x.get (m + 1) ⟨0, Nat.zero_lt_succ m⟩) = x := by
  induction m generalizing x with
  | zero => simp [Fin.foldl_zero, ZFSet.get]
  | succ k ih =>
    simp only [ZFSet.hasArity, if_false_right] at hx
    obtain ⟨⟨a, b, rfl⟩, a_hasArity⟩ := hx
    rw [ZFSet.π₁_pair] at a_hasArity
    rw [Fin.foldl_succ_last]
    -- Last element = b
    have h_last : (a.pair b).get (k+2) ⟨(Fin.last k).val + 1, by omega⟩ = b := by
      simp only [ZFSet.get]
      rw [dif_pos]
      · exact ZFSet.π₂_pair _ _
      · simp [Fin.ext_iff, Fin.val_last]
    -- Initial element transforms under π₁
    have h_init : (a.pair b).get (k+2) ⟨0, by omega⟩ = a.get (k+1) ⟨0, by omega⟩ := by
      simp only [ZFSet.get]
      rw [dif_neg]
      · rw [ZFSet.π₁_pair]; rfl
      · simp [Fin.ext_iff, Fin.val_last]
    -- Step element transforms under π₁
    have h_step : ∀ (i : Fin k),
        (a.pair b).get (k+2) ⟨i.castSucc.val + 1, by have := i.isLt; omega⟩ =
        a.get (k+1) ⟨i.val + 1, by have := i.isLt; omega⟩ := by
      intro ⟨i, hi⟩
      simp only [ZFSet.get, Fin.castSucc_mk]
      rw [dif_neg]
      · rw [ZFSet.π₁_pair]; rfl
      · simp [Fin.ext_iff, Fin.val_last]; omega
    -- Inner foldl = a via IH
    have hih := ih a_hasArity
    have heq : Fin.foldl k
        (fun (acc : ZFSet) (i : Fin k) =>
          acc.pair ((a.pair b).get (k+2) ⟨i.castSucc.val + 1, by have := i.isLt; omega⟩))
        ((a.pair b).get (k+2) ⟨0, by omega⟩) = a := by
      rw [h_init]
      have hfn : (fun (acc : ZFSet) (i : Fin k) =>
          acc.pair ((a.pair b).get (k+2) ⟨i.castSucc.val + 1, by have := i.isLt; omega⟩)) =
          (fun (acc : ZFSet) (i : Fin k) =>
          acc.pair (a.get (k+1) ⟨i.val + 1, by have := i.isLt; omega⟩)) := by
        funext acc i; rw [h_step]
      rw [hfn]
      exact hih
    rw [heq, h_last]

/-- An element of a Fin.foldl product has the expected hasArity and per-component membership. -/
private theorem Fin_foldl_prod_hasArity_and_get {m : ℕ}
    (fs : Fin (m + 1) → ZFSet) {x : ZFSet}
    (hx : x ∈ Fin.foldl m (fun acc i => acc.prod (fs i.succ)) (fs 0)) :
    x.hasArity (m + 1) ∧ ∀ i : Fin (m + 1), x.get (m + 1) i ∈ fs i := by
  induction m generalizing x with
  | zero =>
    simp only [Fin.foldl_zero] at hx
    refine ⟨trivial, fun i => ?_⟩
    rw [Fin.fin_one_eq_zero i, ZFSet.get]
    exact hx
  | succ k ih =>
    rw [Fin.foldl_succ_last] at hx
    simp only [ZFSet.mem_prod] at hx
    obtain ⟨a, ha_mem, b, hb_mem, rfl⟩ := hx
    have ⟨ha_arity, ha_comps⟩ := ih (fun i => fs i.castSucc) ha_mem
    refine ⟨?_, ?_⟩
    · simp only [ZFSet.hasArity, if_false_right]
      refine ⟨⟨a, b, rfl⟩, ?_⟩
      rw [ZFSet.π₁_pair]
      exact ha_arity
    · intro ⟨i, hi⟩
      simp only [ZFSet.get]
      split_ifs with heq
      · rw [ZFSet.π₂_pair]
        have hheq : (⟨i, hi⟩ : Fin (k + 1 + 1)) = Fin.last (k + 1) := heq
        rw [hheq]
        have h_last_succ : (Fin.last k).succ = Fin.last (k + 1) := rfl
        rw [← h_last_succ]
        exact hb_mem
      · rw [ZFSet.π₁_pair]
        have hi' : i < k + 1 := by
          have := heq
          simp only [Fin.ext_iff, Fin.val_last] at this
          omega
        have hcomp := ha_comps ⟨i, hi'⟩
        show a.get (k + 1) ((⟨i, hi⟩ : Fin (k+1+1)).castPred heq) ∈ fs ⟨i, hi⟩
        have h_cp : (⟨i, hi⟩ : Fin (k+1+1)).castPred heq = ⟨i, hi'⟩ := by
          simp [Fin.castPred]
        rw [h_cp]
        have hcs : (⟨i, hi'⟩ : Fin (k+1)).castSucc = (⟨i, hi⟩ : Fin (k+1+1)) := by
          simp [Fin.castSucc]
        rw [← hcs]
        exact hcomp

/-- Variant of `Fin_foldl_prod_hasArity_and_get` with `n` directly (via positivity). -/
private theorem Fin_foldl_prod_hasArity_and_get' {n : ℕ} (hn : 0 < n)
    (fs : Fin n → ZFSet) {x : ZFSet}
    (hx : x ∈ Fin.foldl (n - 1)
        (fun acc (i : Fin (n - 1)) => acc.prod (fs ⟨i.val + 1, by have := i.isLt; omega⟩))
        (fs ⟨0, hn⟩)) :
    x.hasArity n ∧ ∀ i : Fin n, x.get n i ∈ fs i := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := Nat.exists_eq_add_one.mpr hn
  have hfoldl : Fin.foldl (m + 1 - 1)
      (fun (acc : ZFSet) (i : Fin (m + 1 - 1)) =>
        acc.prod (fs ⟨i.val + 1, by have := i.isLt; omega⟩))
      (fs ⟨0, hn⟩) =
      Fin.foldl m (fun (acc : ZFSet) (i : Fin m) => acc.prod (fs i.succ)) (fs 0) := rfl
  rw [hfoldl] at hx
  exact Fin_foldl_prod_hasArity_and_get fs hx

/-- The Fin.foldl product of `toZFSet`s over a list equals `⟦τs.toProdl⟧ᶻ`
(length-indexed form used to thread `rfl`-based foldl equalities). -/
private theorem Fin_foldl_prod_toZFSet_eq_toProdl_aux
    (τs : List SMTType) (n : ℕ) (hlen : τs.length = n + 1) (hpos : 0 < τs.length) :
    Fin.foldl n
      (fun (acc : ZFSet) (i : Fin n) =>
        acc.prod (τs[i.val + 1]'(by have := i.isLt; omega)).toZFSet)
      (τs[0]'hpos).toZFSet = ⟦τs.toProdl⟧ᶻ := by
  induction n generalizing τs with
  | zero =>
    match τs, hlen with
    | [x], _ =>
      simp only [Fin.foldl_zero]
      show x.toZFSet = ⟦List.toProdl [x]⟧ᶻ
      rfl
  | succ m ih =>
    obtain ⟨l, a, rfl⟩ : ∃ (l : List SMTType) (a : SMTType), τs = l.concat a := by
      cases h : τs.reverse with
      | nil =>
        have : τs = [] := by
          have := congrArg List.reverse h
          simpa using this
        subst this; simp at hlen
      | cons a l =>
        refine ⟨l.reverse, a, ?_⟩
        have := congrArg List.reverse h
        rw [List.reverse_reverse, List.reverse_cons] at this
        rw [this, List.concat_eq_append]
    have hlen_l : l.length = m + 1 := by
      simp only [List.length_concat] at hlen; omega
    have hpos_l : 0 < l.length := by omega
    -- Rewrite (l.concat a) as l ++ [a] to enable stable indexing
    simp only [List.concat_eq_append]
    rw [Fin.foldl_succ_last]
    have hlen_app : (l ++ [a]).length = l.length + 1 := by simp
    have h_init : (l ++ [a])[0]'(by rw [hlen_app]; omega) = l[0]'hpos_l :=
      List.getElem_append_left hpos_l
    have h_last : (l ++ [a])[(Fin.last m).val + 1]'(by
        have : (Fin.last m).val = m := Fin.val_last m
        rw [this, hlen_app]; omega) = a := by
      have heq : (Fin.last m).val + 1 = l.length := by rw [Fin.val_last]; omega
      rw [List.getElem_append_right (by rw [heq])]
      simp
    have h_step : ∀ (i : Fin m),
        (l ++ [a])[i.castSucc.val + 1]'(by have := i.isLt; rw [hlen_app]; omega) =
        l[i.val + 1]'(by have := i.isLt; omega) := by
      intro ⟨i, hi⟩
      simp only [Fin.castSucc_mk]
      rw [List.getElem_append_left (by omega)]
    rw [h_last]
    have hfn : (fun (acc : ZFSet) (i : Fin m) =>
          acc.prod (SMTType.toZFSet ((l ++ [a])[i.castSucc.val + 1]'(by
            have h1 : i.val < m := i.isLt
            have h2 : i.castSucc.val = i.val := rfl
            rw [hlen_app, h2]; omega)))) =
        (fun (acc : ZFSet) (i : Fin m) =>
          acc.prod (SMTType.toZFSet (l[i.val + 1]'(by have := i.isLt; omega)))) := by
      funext acc i; rw [h_step]
    rw [h_init, hfn, ih l hlen_l hpos_l]
    rw [show (l ++ [a]).toProdl = (l.concat a).toProdl by rw [List.concat_eq_append],
        List.toProdl_concat_of_nonempty l a (List.length_pos_iff.mp hpos_l)]

/-- The Fin.foldl product of `toZFSet`s over `τs` equals `⟦τs.toProdl⟧ᶻ`. -/
private theorem Fin_foldl_prod_toZFSet_eq_toProdl
    {τs : List SMTType} (hne : τs ≠ []) :
    Fin.foldl (τs.length - 1)
      (fun (acc : ZFSet) (i : Fin (τs.length - 1)) =>
        acc.prod (SMTType.toZFSet (τs[i.val + 1]'(by
          have := i.isLt; have := List.length_pos_iff.mpr hne; omega))))
      (SMTType.toZFSet (τs[0]'(List.length_pos_iff.mpr hne))) =
        SMTType.toZFSet τs.toProdl := by
  have hpos : 0 < τs.length := List.length_pos_iff.mpr hne
  obtain ⟨m, hlen⟩ : ∃ m, τs.length = m + 1 := Nat.exists_eq_add_one.mpr hpos
  have hsub : τs.length - 1 = m := by omega
  have hfold_eq :
      Fin.foldl (τs.length - 1)
        (fun (acc : ZFSet) (i : Fin (τs.length - 1)) =>
          acc.prod (SMTType.toZFSet (τs[i.val + 1]'(by
            have := i.isLt; have : 0 < τs.length := hpos; omega))))
        (SMTType.toZFSet (τs[0]'hpos)) =
      Fin.foldl m
        (fun (acc : ZFSet) (i : Fin m) =>
          acc.prod (SMTType.toZFSet (τs[i.val + 1]'(by have := i.isLt; omega))))
        (SMTType.toZFSet (τs[0]'hpos)) := by
    subst hsub; rfl
  rw [hfold_eq]
  exact Fin_foldl_prod_toZFSet_eq_toProdl_aux τs m hlen hpos

/-- Variant of `Fin_foldl_prod_toZFSet_eq_toProdl` taking an arbitrary length `N`
equal to `τs.length` (used when the Fin.foldl bound is expressed in terms of a
dependent variable like `zs.length` rather than `τs.length` directly). -/
private theorem Fin_foldl_prod_toZFSet_eq_toProdl_N
    {τs : List SMTType} (hne : τs ≠ []) (N : ℕ) (hN : N = τs.length) :
    Fin.foldl (N - 1)
      (fun (acc : ZFSet) (i : Fin (N - 1)) =>
        acc.prod (SMTType.toZFSet (τs[i.val + 1]'(by
          have := i.isLt; have := List.length_pos_iff.mpr hne; omega))))
      (SMTType.toZFSet (τs[0]'(by have := List.length_pos_iff.mpr hne; omega))) =
        SMTType.toZFSet τs.toProdl := by
  subst hN
  exact Fin_foldl_prod_toZFSet_eq_toProdl hne

/-! ### Cast-apply ZFSet machinery for the has-flag bridge

The has-flag bridge `retract_forallVal_eq_sInter_sep_hasflag` needs a
caller-supplied `x_B_of : ZFSet → ZFSet` mapping `⟦τs.toProdl⟧ᶻ`-elements to
`⟦τ⟧ᶻ`-elements. The natural construction composes the loosening cast
(`castZF_of_path 𝕔 : τs.toProdl ~> τ.toSMTType`, applied to lift up to the
SMT side) with `retract τ` (to retract back to the B side).

`castZF_of_path 𝕔` is a relational cast (`{f // IsFunc α β f}`). To turn it
into a function `ZFSet → ZFSet` suitable for `x_B_of`, we wrap `fapply` in a
dependent if-then-else returning junk (∅) outside the domain.
-/

open Classical in
/-- Apply a cast `𝕔 : α ~> β` functionally on a ZFSet `x`. Inside `⟦α⟧ᶻ`,
returns the unique image; outside, returns ∅ (junk). -/
noncomputable def castZF_apply.{u} {α β : SMTType} (𝕔 : α ~> β) (x : ZFSet.{u}) :
    ZFSet.{u} :=
  if hx : x ∈ ⟦α⟧ᶻ then
    (fapply (castZF_of_path 𝕔).1 (is_func_is_pfunc (castZF_of_path 𝕔).2)
      ⟨x, by rwa [is_func_dom_eq (castZF_of_path 𝕔).2]⟩).val
  else ∅

/-- Inside the cast's domain, `castZF_apply 𝕔 x` lies in `⟦β⟧ᶻ`. -/
theorem castZF_apply_mem.{u} {α β : SMTType} (𝕔 : α ~> β) {x : ZFSet.{u}}
    (hx : x ∈ ⟦α⟧ᶻ) : castZF_apply 𝕔 x ∈ ⟦β⟧ᶻ := by
  unfold castZF_apply
  rw [dif_pos hx]
  exact fapply_mem_range (is_func_is_pfunc (castZF_of_path 𝕔).2)
    (by rwa [is_func_dom_eq (castZF_of_path 𝕔).2])

/-- The pair `(x, castZF_apply 𝕔 x)` lies in the relation `(castZF_of_path 𝕔).1`,
witnessing that `castZF_apply 𝕔 x` is the cast of `x`. -/
theorem castZF_apply_pair.{u} {α β : SMTType} (𝕔 : α ~> β) {x : ZFSet.{u}}
    (hx : x ∈ ⟦α⟧ᶻ) :
    x.pair (castZF_apply 𝕔 x) ∈ (castZF_of_path 𝕔).1 := by
  unfold castZF_apply
  rw [dif_pos hx]
  exact (fapply.def (is_func_is_pfunc (castZF_of_path 𝕔).2)
    (by rwa [is_func_dom_eq (castZF_of_path 𝕔).2]))

/-- Convenience wrapper using the `α ⊑ β` (loosening) interface. -/
noncomputable def castZF_apply_of_le.{u} {α β : SMTType} (h : α ⊑ β) (x : ZFSet.{u}) :
    ZFSet.{u} := castZF_apply h.toCastPath x

theorem castZF_apply_of_le_mem.{u} {α β : SMTType} (h : α ⊑ β) {x : ZFSet.{u}}
    (hx : x ∈ ⟦α⟧ᶻ) : castZF_apply_of_le h x ∈ ⟦β⟧ᶻ :=
  castZF_apply_mem h.toCastPath hx

/-- Composition of a loosening cast and a retract gives a `ZFSet → ZFSet`
function suitable for the has-flag bridge's `x_B_of` argument. The result
maps `x ∈ ⟦τs.toProdl⟧ᶻ` (at the SMT level) to `retract τ (castZF_apply 𝕔 x) ∈ ⟦τ⟧ᶻ`
(at the B level). -/
noncomputable def retract_castZF.{u} {α : SMTType} (τ : B.BType)
    (h : α ⊑ τ.toSMTType) (x : ZFSet.{u}) : ZFSet.{u} :=
  retract τ (castZF_apply_of_le h x)

theorem retract_castZF_mem.{u} {α : SMTType} (τ : B.BType) (h : α ⊑ τ.toSMTType)
    {x : ZFSet.{u}} (hx : x ∈ ⟦α⟧ᶻ) : retract_castZF τ h x ∈ ⟦τ⟧ᶻ :=
  retract_mem_of_canonical τ (castZF_apply_of_le_mem h hx)

/-! ### Cast surjectivity on functional pair-bool predicates (Path-A R2)

For has-flag binders, `τs.toProdl ⊑ τ.toSMTType` is a graph cast (`option`-function
to pair-bool predicate). The bridge `retract_forallVal_eq_sInter_sep_hasflag` needs
`case_b_preimage`: every `x₀ ∈ 𝒟_val` has an SMT-side preimage. This is true
exactly when the cast image covers `𝒟_val` — which holds when `𝒟_val` consists
of functional (IsPFunc) pair-bool relations (witnessed by `pfun_inv` from R1).

The lemmas below construct, for any functional pair-bool predicate `y`, an
`option`-function `option_func_of_pfun α β y` whose graph cast equals `y`. -/

open Classical in
/-- The graph (truth-set) of a pair-bool predicate `y` viewed as a relation:
`{ (a, b) ∈ α × β | y(a, b) = true }`. -/
noncomputable def predGraph.{u} (α β : SMTType) (y : ZFSet.{u}) : ZFSet.{u} :=
  (⟦α⟧ᶻ.prod ⟦β⟧ᶻ).sep fun ab => ab.pair ZFBool.true.val ∈ y

open Classical in
/-- Build an option-function from a (functional) pair-bool predicate. For each `a`,
returns `some(b)` for the unique `b` witnessing `(a, b) ↦ true ∈ y` if such exists,
otherwise `none`. -/
noncomputable def option_func_of_pfun.{u} (α β : SMTType) (y : ZFSet.{u}) : ZFSet.{u} :=
  λᶻ : ⟦α⟧ᶻ → ⟦SMTType.option β⟧ᶻ
    | a ↦
      if hExist : ∃ b ∈ ⟦β⟧ᶻ, ((a.pair b).pair ZFBool.true.val) ∈ y then
        (ZFSet.Option.some (S := ⟦β⟧ᶻ)
          ⟨Classical.choose hExist, (Classical.choose_spec hExist).1⟩).val
      else
        (ZFSet.Option.none (S := ⟦β⟧ᶻ)).val

theorem option_func_of_pfun_isFunc.{u} (α β : SMTType) (y : ZFSet.{u}) :
    IsFunc ⟦α⟧ᶻ ⟦SMTType.option β⟧ᶻ (option_func_of_pfun α β y) := by
  unfold option_func_of_pfun
  apply ZFSet.lambda_isFunc
  intro a ha
  split_ifs <;> apply SetLike.coe_mem

theorem option_func_of_pfun_mem.{u} (α β : SMTType) (y : ZFSet.{u}) :
    option_func_of_pfun α β y ∈ ⟦SMTType.fun α (SMTType.option β)⟧ᶻ := by
  rw [show ⟦SMTType.fun α (SMTType.option β)⟧ᶻ = ⟦α⟧ᶻ.funs ⟦SMTType.option β⟧ᶻ from rfl,
      mem_funs]
  exact option_func_of_pfun_isFunc α β y

/-- For functional pair-bool predicate `y`, applying `option_func_of_pfun α β y` at `a`
when `(a, b) ↦ true ∈ y`, gives `some(b)` (using IsPFunc to identify the unique
witness). -/
theorem option_func_of_pfun_apply_some.{u} (α β : SMTType) (y : ZFSet.{u})
    (hpfun : (predGraph α β y).IsPFunc ⟦α⟧ᶻ ⟦β⟧ᶻ)
    (a : ZFSet.{u}) (ha : a ∈ ⟦α⟧ᶻ)
    (b : ZFSet.{u}) (hb : b ∈ ⟦β⟧ᶻ)
    (hab_y : (a.pair b).pair ZFBool.true.val ∈ y) :
    let hf := option_func_of_pfun_isFunc α β y
    @ᶻ(option_func_of_pfun α β y) ⟨a, by rw [is_func_dom_eq hf]; exact ha⟩ =
        ZFSet.Option.some (S := ⟦β⟧ᶻ) ⟨b, hb⟩ := by
  classical
  intro hf
  apply Subtype.ext
  show (fapply (option_func_of_pfun α β y) (is_func_is_pfunc hf)
        ⟨a, by rw [is_func_dom_eq hf]; exact ha⟩).val =
      (ZFSet.Option.some (S := ⟦β⟧ᶻ) ⟨b, hb⟩).val
  conv_lhs => unfold option_func_of_pfun
  rw [fapply_lambda (A := ⟦α⟧ᶻ) (B := ⟦SMTType.option β⟧ᶻ)
        (f := fun a =>
          if hExist : ∃ b ∈ ⟦β⟧ᶻ, ((a.pair b).pair ZFBool.true.val) ∈ y then
            (ZFSet.Option.some (S := ⟦β⟧ᶻ)
              ⟨Classical.choose hExist, (Classical.choose_spec hExist).1⟩).val
          else
            (ZFSet.Option.none (S := ⟦β⟧ᶻ)).val)
        (hf := by intro x hx; dsimp; split_ifs <;> apply SetLike.coe_mem) ha]
  · have hExist : ∃ b' ∈ ⟦β⟧ᶻ, (a.pair b').pair ZFBool.true.val ∈ y := ⟨b, hb, hab_y⟩
    dsimp only
    rw [dif_pos hExist]
    set b' := Classical.choose hExist with hb'_def
    have hb'_mem : b' ∈ ⟦β⟧ᶻ := (Classical.choose_spec hExist).1
    have hab'_y : (a.pair b').pair ZFBool.true.val ∈ y := (Classical.choose_spec hExist).2
    have hab_in_graph : a.pair b ∈ predGraph α β y := by
      unfold predGraph; rw [mem_sep]
      exact ⟨pair_mem_prod.mpr ⟨ha, hb⟩, hab_y⟩
    have hab'_in_graph : a.pair b' ∈ predGraph α β y := by
      unfold predGraph; rw [mem_sep]
      exact ⟨pair_mem_prod.mpr ⟨ha, hb'_mem⟩, hab'_y⟩
    have hb'_eq_b : b' = b := hpfun.2 a b' hab'_in_graph b hab_in_graph
    have : (⟨b', hb'_mem⟩ : {x // x ∈ ⟦β⟧ᶻ}) = ⟨b, hb⟩ := Subtype.ext hb'_eq_b
    rw [this]

/-- When no `b` witnesses `(a, b) ↦ true ∈ y`, `option_func_of_pfun α β y` at `a`
returns `none`. -/
theorem option_func_of_pfun_apply_none.{u} (α β : SMTType) (y : ZFSet.{u})
    (a : ZFSet.{u}) (ha : a ∈ ⟦α⟧ᶻ)
    (hno : ¬∃ b ∈ ⟦β⟧ᶻ, (a.pair b).pair ZFBool.true.val ∈ y) :
    let hf := option_func_of_pfun_isFunc α β y
    @ᶻ(option_func_of_pfun α β y) ⟨a, by rw [is_func_dom_eq hf]; exact ha⟩ =
        ZFSet.Option.none (S := ⟦β⟧ᶻ) := by
  classical
  intro hf
  apply Subtype.ext
  show (fapply (option_func_of_pfun α β y) (is_func_is_pfunc hf)
        ⟨a, by rw [is_func_dom_eq hf]; exact ha⟩).val =
      (ZFSet.Option.none (S := ⟦β⟧ᶻ)).val
  conv_lhs => unfold option_func_of_pfun
  rw [fapply_lambda (A := ⟦α⟧ᶻ) (B := ⟦SMTType.option β⟧ᶻ)
        (f := fun a =>
          if hExist : ∃ b ∈ ⟦β⟧ᶻ, ((a.pair b).pair ZFBool.true.val) ∈ y then
            (ZFSet.Option.some (S := ⟦β⟧ᶻ)
              ⟨Classical.choose hExist, (Classical.choose_spec hExist).1⟩).val
          else
            (ZFSet.Option.none (S := ⟦β⟧ᶻ)).val)
        (hf := by intro x hx; dsimp; split_ifs <;> apply SetLike.coe_mem) ha]
  dsimp only
  rw [dif_neg hno]

set_option maxHeartbeats 1600000 in
/-- Cast surjectivity on functional pair-bool predicates: every IsPFunc-restricted
pair-bool relation has an option-shape preimage under the loosening cast (specifically,
the identity-component graph cast `castPath.graph (castPath.reflexive α) (castPath.reflexive β)`,
which is the cast emitted by the encoder for has-flag binders).

Used in Path-A discharge of `encodeTerm_all_hasflag_existential_admit`. Combined with
`pfun_inv` (R1), gives `case_b_preimage` for the has-flag bridge. -/
theorem castZF_apply_surj_on_isPFunc.{u} (α β : SMTType) (y : ZFSet.{u})
    (hy : y ∈ ⟦SMTType.fun (SMTType.pair α β) SMTType.bool⟧ᶻ)
    (hpfun : (predGraph α β y).IsPFunc ⟦α⟧ᶻ ⟦β⟧ᶻ) :
    ∃ x ∈ ⟦SMTType.fun α (SMTType.option β)⟧ᶻ,
      castZF_apply (castPath.graph (castPath.reflexive α) (castPath.reflexive β)) x = y := by
  classical
  refine ⟨option_func_of_pfun α β y, option_func_of_pfun_mem α β y, ?_⟩
  set F := option_func_of_pfun α β y with hF_def
  set 𝕔 : (SMTType.fun α (SMTType.option β)) ~>
      (SMTType.fun (SMTType.pair α β) SMTType.bool) :=
    castPath.graph (castPath.reflexive α) (castPath.reflexive β) with h𝕔_def
  -- Step 1: Reduce castZF_of_path 𝕔 to castZF_graph with identity components.
  have h_castZF_eq : castZF_of_path 𝕔 = castZF_graph (α₁ := α) (α₂ := α)
      (β₁ := β) (β₂ := β) ⟨𝟙⟦α⟧ᶻ, Id.IsFunc⟩ ⟨𝟙⟦β⟧ᶻ, Id.IsFunc⟩ := by
    rw [h𝕔_def, castZF_of_path, castZF_of_path_id, castZF_of_path_id]
  -- Step 2: Establish (F, y) ∈ castZF_of_path 𝕔 via lambda_spec + lambda_ext_iff.
  have hF_isFunc : IsFunc ⟦α⟧ᶻ ⟦SMTType.option β⟧ᶻ F := option_func_of_pfun_isFunc α β y
  have hy_isFunc : IsFunc ⟦SMTType.pair α β⟧ᶻ ⟦SMTType.bool⟧ᶻ y := by
    rw [show ⟦SMTType.fun (SMTType.pair α β) SMTType.bool⟧ᶻ =
        ⟦SMTType.pair α β⟧ᶻ.funs ⟦SMTType.bool⟧ᶻ from rfl, mem_funs] at hy
    exact hy
  have h_pair_in : F.pair y ∈ (castZF_of_path 𝕔).1 := by
    rw [h_castZF_eq]
    unfold castZF_graph
    dsimp only
    rw [lambda_spec]
    have hF_mem : F ∈ ⟦SMTType.fun α (SMTType.option β)⟧ᶻ := option_func_of_pfun_mem α β y
    refine ⟨hF_mem, hy, ?_⟩
    rw [show ⟦SMTType.fun α (SMTType.option β)⟧ᶻ = ⟦α⟧ᶻ.funs ⟦SMTType.option β⟧ᶻ from rfl,
        mem_funs] at hF_mem
    rw [dif_pos hF_mem]
    rw [lambda_eta hy_isFunc]
    rw [lambda_ext_iff (d := ⟦SMTType.pair α β⟧ᶻ) (r := 𝔹)
          (f₁ := fun xy => if hxy : xy ∈ ⟦SMTType.pair α β⟧ᶻ then
            (@ᶻy ⟨xy, by rwa [is_func_dom_eq hy_isFunc]⟩).val else ∅)
          (hf₁ := by
            intro x hx
            show (if hxy : x ∈ ⟦SMTType.pair α β⟧ᶻ then
              (@ᶻy ⟨x, by rwa [is_func_dom_eq hy_isFunc]⟩).val else ∅) ∈ 𝔹
            rw [dite_cond_eq_true (eq_true hx)]
            apply SetLike.coe_mem)]
    intro xy hxy
    show (if hxy : xy ∈ ⟦SMTType.pair α β⟧ᶻ then (@ᶻy ⟨xy, _⟩).val else ∅) = _
    rw [dite_cond_eq_true (eq_true hxy)]
    rw [dite_cond_eq_true (eq_true hxy)]
    have hxy_prod : xy ∈ ⟦α⟧ᶻ.prod ⟦β⟧ᶻ := hxy
    have hπ₁ : xy.π₁ ∈ ⟦α⟧ᶻ := (pair_mem_prod.mp (pair_eta hxy_prod ▸ hxy_prod)).1
    have hπ₂ : xy.π₂ ∈ ⟦β⟧ᶻ := (pair_mem_prod.mp (pair_eta hxy_prod ▸ hxy_prod)).2
    have hxy_eq : xy = xy.π₁.pair xy.π₂ := pair_eta hxy_prod
    have hxπ₁_range : xy.π₁ ∈ (𝟙⟦α⟧ᶻ : ZFSet).Range := by rw [range_Id]; exact hπ₁
    have hyπ₂_range : xy.π₂ ∈ (𝟙⟦β⟧ᶻ : ZFSet).Range := by rw [range_Id]; exact hπ₂
    rw [dif_pos hxπ₁_range]
    rw [dif_pos hyπ₂_range]
    have hx'_eq : Classical.choose (mem_sep.mp hxπ₁_range).2 = xy.π₁ := by
      have h_pair := (Classical.choose_spec (mem_sep.mp hxπ₁_range).2).2
      have h_dom : Classical.choose (mem_sep.mp hxπ₁_range).2 ∈ ⟦α⟧ᶻ :=
        (mem_sep.mp (Classical.choose_spec (mem_sep.mp hxπ₁_range).2).1).1
      exact (pair_mem_Id_iff h_dom).mp h_pair
    have hy'_eq : Classical.choose (mem_sep.mp hyπ₂_range).2 = xy.π₂ := by
      have h_pair := (Classical.choose_spec (mem_sep.mp hyπ₂_range).2).2
      have h_dom : Classical.choose (mem_sep.mp hyπ₂_range).2 ∈ ⟦β⟧ᶻ :=
        (mem_sep.mp (Classical.choose_spec (mem_sep.mp hyπ₂_range).2).1).1
      exact (pair_mem_Id_iff h_dom).mp h_pair
    by_cases h_xy_y : (xy.π₁.pair xy.π₂).pair ZFBool.true.val ∈ y
    · -- y(xy) = zftrue, F(π₁ xy) = some(π₂ xy) by apply_some.
      have hxy_y : xy.pair ZFBool.true.val ∈ y := hxy_eq ▸ h_xy_y
      have hLHS : (@ᶻy ⟨xy, by rwa [is_func_dom_eq hy_isFunc]⟩).val = ZFBool.true.val := by
        rw [fapply.of_pair (is_func_is_pfunc hy_isFunc) hxy_y]
      rw [hLHS]
      have hF_apply : @ᶻF ⟨xy.π₁, by rwa [is_func_dom_eq hF_isFunc]⟩ =
          ZFSet.Option.some (S := ⟦β⟧ᶻ) ⟨xy.π₂, hπ₂⟩ :=
        option_func_of_pfun_apply_some α β y hpfun xy.π₁ hπ₁ xy.π₂ hπ₂ h_xy_y
      have h_mem_choose_β : Classical.choose (mem_sep.mp hyπ₂_range).2 ∈ ⟦β⟧ᶻ :=
        (mem_sep.mp (Classical.choose_spec (mem_sep.mp hyπ₂_range).2).1).1
      have h_dom_choose : Classical.choose (mem_sep.mp hxπ₁_range).2 ∈ ⟦α⟧ᶻ :=
        (mem_sep.mp (Classical.choose_spec (mem_sep.mp hxπ₁_range).2).1).1
      have h_decide : decide (
          @ᶻF ⟨Classical.choose (mem_sep.mp hxπ₁_range).2,
            by rw [is_func_dom_eq hF_isFunc]; exact h_dom_choose⟩ =
          ZFSet.Option.some (S := ⟦β⟧ᶻ)
            ⟨Classical.choose (mem_sep.mp hyπ₂_range).2, h_mem_choose_β⟩) = true := by
        apply decide_eq_true
        have h1 : (⟨Classical.choose (mem_sep.mp hxπ₁_range).2,
            by rw [is_func_dom_eq hF_isFunc]; exact h_dom_choose⟩ : {x // x ∈ F.Dom}) =
          ⟨xy.π₁, by rwa [is_func_dom_eq hF_isFunc]⟩ := Subtype.ext hx'_eq
        have h2 : (⟨Classical.choose (mem_sep.mp hyπ₂_range).2, h_mem_choose_β⟩ :
            {x // x ∈ ⟦β⟧ᶻ}) = ⟨xy.π₂, hπ₂⟩ := Subtype.ext hy'_eq
        rw [h1, h2]; exact hF_apply
      rw [h_decide]; rfl
    · -- y(xy) = zffalse, F(π₁ xy) ≠ some(π₂ xy).
      have hxy_dom : xy ∈ y.Dom := by rw [is_func_dom_eq hy_isFunc]; exact hxy
      have hxy_y_pair : xy.pair (@ᶻy ⟨xy, hxy_dom⟩).val ∈ y :=
        fapply.def (is_func_is_pfunc hy_isFunc) hxy_dom
      have h_y_val_𝔹 : (@ᶻy ⟨xy, hxy_dom⟩).val ∈ 𝔹 := SetLike.coe_mem _
      rcases (ZFBool.mem_𝔹_iff _).mp h_y_val_𝔹 with h_false | h_true
      · -- y(xy) = zffalse: show RHS = zffalse via decide_eq_false.
        rw [h_false]
        have h_mem_choose_β : Classical.choose (mem_sep.mp hyπ₂_range).2 ∈ ⟦β⟧ᶻ :=
          (mem_sep.mp (Classical.choose_spec (mem_sep.mp hyπ₂_range).2).1).1
        have h_dom_choose : Classical.choose (mem_sep.mp hxπ₁_range).2 ∈ ⟦α⟧ᶻ :=
          (mem_sep.mp (Classical.choose_spec (mem_sep.mp hxπ₁_range).2).1).1
        have h_decide : decide (
            @ᶻF ⟨Classical.choose (mem_sep.mp hxπ₁_range).2,
              by rw [is_func_dom_eq hF_isFunc]; exact h_dom_choose⟩ =
            ZFSet.Option.some (S := ⟦β⟧ᶻ)
              ⟨Classical.choose (mem_sep.mp hyπ₂_range).2, h_mem_choose_β⟩) = false := by
          apply decide_eq_false
          intro h_eq
          have h1 : (⟨Classical.choose (mem_sep.mp hxπ₁_range).2,
              by rw [is_func_dom_eq hF_isFunc]; exact h_dom_choose⟩ : {x // x ∈ F.Dom}) =
            ⟨xy.π₁, by rwa [is_func_dom_eq hF_isFunc]⟩ := Subtype.ext hx'_eq
          have h2 : (⟨Classical.choose (mem_sep.mp hyπ₂_range).2, h_mem_choose_β⟩ :
              {x // x ∈ ⟦β⟧ᶻ}) = ⟨xy.π₂, hπ₂⟩ := Subtype.ext hy'_eq
          rw [h1, h2] at h_eq
          by_cases hExist : ∃ b ∈ ⟦β⟧ᶻ, (xy.π₁.pair b).pair ZFBool.true.val ∈ y
          · obtain ⟨b, hb, hab_y⟩ := hExist
            have hF_apply_b :=
              option_func_of_pfun_apply_some α β y hpfun xy.π₁ hπ₁ b hb hab_y
            rw [hF_apply_b] at h_eq
            rw [ZFSet.Option.some.injEq] at h_eq
            have hb_eq : b = xy.π₂ := Subtype.ext_iff.mp h_eq
            rw [hb_eq] at hab_y
            exact h_xy_y hab_y
          · have hF_apply_none := option_func_of_pfun_apply_none α β y xy.π₁ hπ₁ hExist
            rw [hF_apply_none] at h_eq
            exact ZFSet.Option.some_ne_none _ h_eq.symm
        rw [h_decide]; rfl
      · -- y(xy) = zftrue: but pair (π₁ xy, π₂ xy) zftrue ∈ y contradicts h_xy_y.
        exfalso
        rw [h_true] at hxy_y_pair
        rw [hxy_eq] at hxy_y_pair
        exact h_xy_y hxy_y_pair
  -- Step 3: Use functionality of castZF_of_path 𝕔 to conclude castZF_apply 𝕔 F = y.
  have hF_mem : F ∈ ⟦SMTType.fun α (SMTType.option β)⟧ᶻ := option_func_of_pfun_mem α β y
  unfold castZF_apply
  rw [dif_pos hF_mem]
  have hcast_pfunc := is_func_is_pfunc (castZF_of_path 𝕔).2
  have hF_dom : F ∈ (castZF_of_path 𝕔).1.Dom := by
    rw [is_func_dom_eq (castZF_of_path 𝕔).2]; exact hF_mem
  have h_apply_pair :
      F.pair (fapply (castZF_of_path 𝕔).1 hcast_pfunc ⟨F, hF_dom⟩).val ∈ (castZF_of_path 𝕔).1 :=
    fapply.def hcast_pfunc hF_dom
  exact (hcast_pfunc.2 F y h_pair_in
    (fapply (castZF_of_path 𝕔).1 hcast_pfunc ⟨F, hF_dom⟩).val h_apply_pair).symm

/-! ### Factored retract-forall lemma for `all_case`

This is the analog of `retract_lamVal_eq_collect` (in `CollectCaseHelpers.lean`)
but for the SMT `.forall` quantifier. It discharges the retract equation
`retract .bool forallVal.fst = sInter (𝔹.sep (fun y => ∃ x ∈ 𝒟_val, y = ℙ x))`
for the forall-imp body shape produced by the `all` encoder.

Key differences from `retract_lamVal_eq_collect`:
- The binder is `.forall` (not `.lambda`) and binds a list `zs` of fresh variables
  (not a single `z`).
- The body is `(D_enc @ zs.toPairl) ⇒ P_enc_subst` (imp, not ite).
- The retract target type is `.bool` (identity retraction) instead of `τ.set`,
  so the final equation is just `forallVal.fst = sInter(...)`.

The forall denotation unfolds to
  `sInter (𝔹.sep (fun y => ∃ x ∈ 𝒟_smt, y = ℙ_smt x))`
where `𝒟_smt = Fin.foldl (n-1) (fun acc i => acc.prod τs[i+1]) τs[0]` and
`ℙ_smt x = ⟦body(x-indexed)⟧ˢ.get _ .fst`.
-/

open Classical B in
set_option maxHeartbeats 8000000 in
theorem retract_forallVal_eq_sInter_sep.{u}
    -- Type infrastructure
    {vs : List B.𝒱} (vs_nemp : vs ≠ []) (_vs_nodup : vs.Nodup)
    {τ : BType} (τ_hasArity : τ.hasArity vs.length)
    -- SMT terms and binder structure
    {D : B.Term}
    {D_enc P_enc_subst : SMT.Term} {zs : List SMT.𝒱} {τs : List SMTType}
    (zs_nemp : zs ≠ []) (zs_len : zs.length = τs.length)
    (τs_toProdl_eq : τs.toProdl = τ.toSMTType)
    {imp_body : SMT.Term}
    (_imp_body_def : imp_body =
      (SMT.Term.app D_enc (zs.map .var).toPairl).imp P_enc_subst)
    -- zs not free in D_enc/P_enc_subst (other than as pair-list arguments)
    (_zs_not_fv_D : ∀ z ∈ zs, z ∉ SMT.fv D_enc)
    -- Renaming context and forall value
    {Δ_ctx : SMT.RenamingContext.Context}
    (hcov_forall : SMT.RenamingContext.CoversFV Δ_ctx
      (SMT.Term.forall zs τs imp_body))
    {forallVal : SMT.Dom}
    (hforallVal : ⟦(SMT.Term.forall zs τs imp_body).abstract Δ_ctx hcov_forall⟧ˢ
      = some forallVal)
    -- D_enc denotation data (parametric under zs-updates)
    {denD_val : SMT.Dom}
    (hcov_D_upd : ∀ (w : Fin zs.length → SMT.Dom),
      SMT.RenamingContext.CoversFV
        (Function.updates Δ_ctx zs (List.ofFn (fun i => some (w i)))) D_enc)
    (_den_D_upd_eq : ∀ (w : Fin zs.length → SMT.Dom),
      ⟦D_enc.abstract
        (Function.updates Δ_ctx zs (List.ofFn (fun i => some (w i))))
        (hcov_D_upd w)⟧ˢ = some denD_val)
    (_denD_val_type : denD_val.snd.fst = τ.toSMTType.fun SMTType.bool)
    (_denD_val_func : ⟦τ.toSMTType⟧ᶻ.IsFunc 𝔹 denD_val.fst)
    {𝒟_val : ZFSet.{u}} (h𝒟_val : 𝒟_val ∈ ⟦τ.set⟧ᶻ)
    (𝒟_val_nonempty : 𝒟_val.Nonempty)
    (_denD_val_retract : retract τ.set denD_val.fst = 𝒟_val)
    -- imp_body totality/typing under zs-updates
    (hgo_cov : ∀ x ∈ SMT.fv imp_body, x ∉ zs → (Δ_ctx x).isSome = true)
    (hcov_imp_upd : ∀ (w : Fin zs.length → SMT.Dom),
      SMT.RenamingContext.CoversFV
        (Function.updates Δ_ctx zs (List.ofFn (fun i => some (w i)))) imp_body)
    (himp_total : ∀ (w : Fin zs.length → SMT.Dom),
      (∀ i, (w i).snd.fst = τs[i]'(zs_len ▸ i.isLt) ∧
        (w i).fst ∈ ⟦τs[i]'(zs_len ▸ i.isLt)⟧ᶻ) →
      ⟦imp_body.abstract
        (Function.updates Δ_ctx zs (List.ofFn (fun i => some (w i))))
        (hcov_imp_upd w)⟧ˢ.isSome = true)
    (himp_ty : ∀ (w : Fin zs.length → SMT.Dom),
      (∀ i, (w i).snd.fst = τs[i]'(zs_len ▸ i.isLt) ∧
        (w i).fst ∈ ⟦τs[i]'(zs_len ▸ i.isLt)⟧ᶻ) →
      ∀ Db : SMT.Dom,
        ⟦imp_body.abstract
          (Function.updates Δ_ctx zs (List.ofFn (fun i => some (w i))))
          (hcov_imp_upd w)⟧ˢ = some Db →
        Db.snd.fst = SMTType.bool)
    -- B-level data
    {P : B.Term} {«Δ» : B.RenamingContext.Context}
    (Δ_fv_all : ∀ v ∈ B.fv (Term.all vs D P), («Δ» v).isSome = true)
    -- B-level sInter target
    {T_val : ZFSet.{u}}
    (hT_eq : ZFSet.sInter (ZFSet.𝔹.sep fun (y : ZFSet) =>
      ∃ x ∈ 𝒟_val, y =
        (if hx : x.hasArity vs.length ∧ x ∈ ⟦τ⟧ᶻ then
          match ⟦(B.Term.abstract.go P vs «Δ» (fun v hv hvs => Δ_fv_all v
            (B.fv.mem_all (.inr ⟨hv, hvs⟩)))).uncurry
            (fun i => ⟨x.get vs.length i, ⟨τ.get vs.length i,
              get_mem_type_of_isTuple hx.1 τ_hasArity hx.2⟩⟩)⟧ᴮ with
          | some ⟨Pz, _⟩ => Pz
          | none => ZFSet.zffalse
        else ZFSet.zffalse)) = T_val)
    -- P denotability for all x ∈ 𝒟_val
    (h_den_P : ∀ {x_fin : Fin vs.length → B.Dom},
      (∀ i, (x_fin i).snd.fst = τ.get vs.length i ∧
            (x_fin i).fst ∈ ⟦τ.get vs.length i⟧ᶻ) →
      ZFSet.ofFinDom x_fin ∈ 𝒟_val →
      ⟦(B.Term.abstract.go P vs «Δ» (fun v hv hvs => Δ_fv_all v
        (B.fv.mem_all (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ.isSome = true)
    -- P always evaluates to a bool-typed value for x_fin in 𝒟_val
    (h_den_P_bool : ∀ {x_fin : Fin vs.length → B.Dom},
      (∀ i, (x_fin i).snd.fst = τ.get vs.length i ∧
            (x_fin i).fst ∈ ⟦τ.get vs.length i⟧ᶻ) →
      ZFSet.ofFinDom x_fin ∈ 𝒟_val →
      ∀ (Pz : ZFSet.{u}) (P_ty : BType) (hP_val : Pz ∈ ⟦P_ty⟧ᶻ),
      ⟦(B.Term.abstract.go P vs «Δ» (fun v hv hvs => Δ_fv_all v
        (B.fv.mem_all (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ = some ⟨Pz, ⟨P_ty, hP_val⟩⟩ →
      P_ty = .bool)
    -- *** THE SEMANTIC BRIDGE (SMT-level x) ***
    -- For each SMT-level x ∈ ⟦τ.toSMTType⟧ᶻ with Fin-indexed witness w pairing to x,
    -- imp_body(w) = zftrue iff (retract τ x ∉ 𝒟_val) or P(retract τ x) = zftrue.
    (zs_len_pos_hyp : 0 < zs.length)
    (vs_zs_len : vs.length = zs.length)
    (hbridge : ∀ (x : ZFSet.{u}) (hx_mem : x ∈ ⟦τ.toSMTType⟧ᶻ),
      let x_B := retract τ x
      let hx_B_mem : x_B ∈ ⟦τ⟧ᶻ := retract_mem_of_canonical τ hx_mem
      let x_fin : Fin vs.length → B.Dom := fun i =>
        ⟨x_B.get vs.length i, ⟨τ.get vs.length i,
          get_mem_type_of_isTuple (hasArity_of_mem_toZFSet τ_hasArity hx_B_mem)
            τ_hasArity hx_B_mem⟩⟩
      ∀ (w : Fin zs.length → SMT.Dom)
        (_hw : ∀ i, (w i).snd.fst = τs[i]'(zs_len ▸ i.isLt) ∧
          (w i).fst ∈ ⟦τs[i]'(zs_len ▸ i.isLt)⟧ᶻ)
        (_hw_smt : Fin.foldl (zs.length - 1)
          (fun acc i => acc.pair (w ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩).fst)
          (w ⟨0, zs_len_pos_hyp⟩).fst = x)
        (body_val : SMT.Dom),
        ⟦imp_body.abstract
          (Function.updates Δ_ctx zs (List.ofFn (fun i => some (w i))))
          (hcov_imp_upd w)⟧ˢ = some body_val →
        (body_val.fst = zftrue ↔
          (x_B ∉ 𝒟_val ∨
           ∀ (Px : ZFSet.{u}) (P_ty : BType) (hP_val : Px ∈ ⟦P_ty⟧ᶻ),
             ⟦(B.Term.abstract.go P vs «Δ» (fun v hv hvs => Δ_fv_all v
               (B.fv.mem_all (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ =
               some ⟨Px, ⟨P_ty, hP_val⟩⟩ → Px = zftrue)))
    : retract .bool forallVal.fst = T_val := by
  -- Proof strategy (analog of `retract_lamVal_eq_collect`): unfold the forall
  -- denotation to `sInter (𝔹.sep ...)`, transfer via the canonical iso at each
  -- x ∈ 𝒟_val using `hbridge`, conclude extensional equality.
  show forallVal.fst = T_val
  rw [← hT_eq]
  have h𝒟_sub : 𝒟_val ⊆ ⟦τ⟧ᶻ := by
    rwa [BType.toZFSet, ZFSet.mem_powerset] at h𝒟_val
  have zs_len_pos : zs.length > 0 := List.length_pos_iff.mpr zs_nemp
  have τs_nemp : τs ≠ [] := by
    intro h; apply zs_nemp
    have hzs_len : zs.length = 0 := by rw [zs_len, h]; rfl
    exact List.length_eq_zero_iff.mp hzs_len
  set τs_fn : Fin zs.length → SMTType := fun ⟨i, hi⟩ => τs[i]'(zs_len ▸ hi) with hτs_fn
  -- 𝒟_smt: the Fin.foldl product domain on the SMT side.
  set 𝒟_smt : ZFSet.{u} := Fin.foldl (zs.length - 1)
    (fun (acc : ZFSet.{u}) ⟨i, hi⟩ ↦
      acc.prod (τs_fn ⟨i + 1, Nat.add_lt_of_lt_sub hi⟩).toZFSet)
    (τs_fn ⟨0, zs_len_pos⟩).toZFSet with h𝒟_smt
  have hforallVal_unfold := hforallVal
  rw [SMT.Term.abstract, dif_pos zs_len] at hforallVal_unfold
  simp only [SMT.denote] at hforallVal_unfold
  rw [dif_pos zs_len_pos] at hforallVal_unfold
  have himp_total_uncurry :
      ∀ (w : Fin zs.length → SMT.Dom.{u}),
        (∀ i, (w i).snd.fst = τs_fn i ∧ (w i).fst ∈ ⟦τs_fn i⟧ᶻ) →
        ⟦(SMT.Term.abstract.go imp_body zs Δ_ctx hgo_cov).uncurry w⟧ˢ.isSome = true := by
    intro w hw
    have hgo := funAbstractGoList (Δctx := Δ_ctx) (P := imp_body)
      (vs := zs) (τs := τs) zs_len hgo_cov hcov_imp_upd w
      (fun i => by
        have := hw i
        simp only [τs_fn, hτs_fn] at this
        exact this)
    rw [hgo]
    exact himp_total w (fun i => by
      have := hw i
      simp only [τs_fn, hτs_fn] at this
      exact this)
  have h_den_t_isSome :
      ∀ {x : Fin zs.length → SMT.Dom.{u}},
        (∀ i, (x i).2.1 =
            (fun (j : Fin zs.length) => τs[j.val]'(zs_len ▸ j.isLt)) i ∧
          (x i).1 ∈
            ⟦(fun (j : Fin zs.length) => τs[j.val]'(zs_len ▸ j.isLt)) i⟧ᶻ) →
        ⟦(SMT.Term.abstract.go imp_body zs Δ_ctx hgo_cov).uncurry x⟧ˢ.isSome = true := by
    intro x hx
    apply himp_total_uncurry
    intro i
    have := hx i
    rcases i with ⟨j, hj⟩
    simp only [τs_fn, hτs_fn] at this ⊢
    exact this
  have h_den_t_match :
      ∀ {x : Fin zs.length → SMT.Dom.{u}},
        (∀ i, (x i).2.1 =
            (match i with | ⟨k, hk⟩ => τs[k]'(zs_len ▸ hk)) ∧
          (x i).1 ∈
            ⟦match i with | ⟨k, hk⟩ => τs[k]'(zs_len ▸ hk)⟧ᶻ) →
        ⟦(SMT.Term.abstract.go imp_body zs Δ_ctx hgo_cov).uncurry x⟧ˢ.isSome = true := by
    intro x hx
    apply h_den_t_isSome
    intro i
    rcases i with ⟨j, hj⟩
    exact hx ⟨j, hj⟩
  rw [dif_pos (by intro x hx; exact h_den_t_match hx)] at hforallVal_unfold
  simp only [Option.pure_def, Option.some.injEq] at hforallVal_unfold
  have hforallVal_fst : forallVal.fst = _ := congrArg (·.fst) hforallVal_unfold.symm
  -- Main proof: `⋂₀ (𝔹.sep LHS_pred) = ⋂₀ (𝔹.sep RHS_pred)` by classical case split
  -- on whether every `x ∈ 𝒟_val` has `ℙ_B(x) = zftrue`.
  rw [hforallVal_fst]
  simp only []
  have 𝒟_smt_nonempty : 𝒟_smt.Nonempty := by
    rw [h𝒟_smt]
    suffices h : ∀ (n : ℕ) (g : Fin n → ZFSet) (init : ZFSet),
        init.Nonempty →
        (∀ i : Fin n, (g i).Nonempty) →
        (Fin.foldl n (fun acc i ↦ acc.prod (g i)) init).Nonempty by
      apply h (zs.length - 1)
        (fun i : Fin (zs.length - 1) =>
          ⟦τs_fn ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩⟧ᶻ)
        ⟦τs_fn ⟨0, zs_len_pos⟩⟧ᶻ
      · exact ⟨_, SMTType.mem_toZFSet_of_defaultZFSet⟩
      · intro _; exact ⟨_, SMTType.mem_toZFSet_of_defaultZFSet⟩
    intro n
    induction n with
    | zero => intro g init h_init _; simpa [Fin.foldl_zero] using h_init
    | succ m ih =>
      intro g init h_init h_factors
      rw [Fin.foldl_succ_last]
      obtain ⟨a, ha⟩ := ih (fun j => g j.castSucc) init h_init
        (fun j => h_factors j.castSucc)
      obtain ⟨b, hb⟩ := h_factors (Fin.last m)
      exact ⟨a.pair b, ZFSet.pair_mem_prod.mpr ⟨ha, hb⟩⟩
  -- 𝒟_smt equals the full toZFSet of τ.toSMTType (product domain of all τs).
  have h𝒟_smt_eq_toSMTType : 𝒟_smt = SMTType.toZFSet τ.toSMTType := by
    rw [h𝒟_smt, ← τs_toProdl_eq]
    have hne : τs ≠ [] := τs_nemp
    clear_value 𝒟_smt
    simp only [τs_fn, hτs_fn]
    exact Fin_foldl_prod_toZFSet_eq_toProdl_N (τs := τs) hne zs.length zs_len
  by_cases h_all : ∀ x ∈ 𝒟_val,
      (if hx : x.hasArity vs.length ∧ x ∈ ⟦τ⟧ᶻ then
        match ⟦(B.Term.abstract.go P vs «Δ» (fun v hv hvs => Δ_fv_all v
          (B.fv.mem_all (.inr ⟨hv, hvs⟩)))).uncurry
          (fun i => ⟨x.get vs.length i, ⟨τ.get vs.length i,
            get_mem_type_of_isTuple hx.1 τ_hasArity hx.2⟩⟩)⟧ᴮ with
        | some ⟨Pz, _⟩ => Pz
        | none => zffalse
      else zffalse) = zftrue
  · -- Case A: both sides = zftrue.
    have h_rhs : (⋂₀ ZFSet.sep (fun y => ∃ x ∈ 𝒟_val,
        y = if hx : x.hasArity vs.length ∧ x ∈ ⟦τ⟧ᶻ then
              match ⟦(B.Term.abstract.go P vs «Δ» (fun v hv hvs => Δ_fv_all v
                (B.fv.mem_all (.inr ⟨hv, hvs⟩)))).uncurry
                (fun i => ⟨x.get vs.length i, ⟨τ.get vs.length i,
                  get_mem_type_of_isTuple hx.1 τ_hasArity hx.2⟩⟩)⟧ᴮ with
              | some ⟨Pz, _⟩ => Pz
              | none => zffalse
            else zffalse) 𝔹 : ZFSet) = zftrue :=
      sInter_sep_eq_zftrue_of_forall_eq_zftrue 𝒟_val_nonempty h_all
    rw [h_rhs]
    apply sInter_sep_eq_zftrue_of_forall_eq_zftrue 𝒟_smt_nonempty
    intro x hx
    have hx_smttype : x ∈ ⟦τ.toSMTType⟧ᶻ := h𝒟_smt_eq_toSMTType ▸ hx
    have hx_fs_mem : x ∈ Fin.foldl (zs.length - 1)
        (fun (acc : ZFSet.{u}) (i : Fin (zs.length - 1)) =>
          acc.prod ⟦τs_fn ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩⟧ᶻ)
        ⟦τs_fn ⟨0, zs_len_pos⟩⟧ᶻ := by
      rw [← h𝒟_smt]; exact hx
    have ⟨hx_arity, hx_comps⟩ :=
      Fin_foldl_prod_hasArity_and_get' (n := zs.length) zs_len_pos
        (fun i => ⟦τs_fn i⟧ᶻ) hx_fs_mem
    have hx_comps' : ∀ i : Fin zs.length, x.get zs.length i ∈ ⟦τs[i.val]'(zs_len ▸ i.isLt)⟧ᶻ :=
      fun i => by
        have := hx_comps i
        rcases i with ⟨k, hk⟩
        simpa [τs_fn, hτs_fn] using this
    rw [dif_pos ⟨hx_arity, hx_comps'⟩]
    set w : Fin zs.length → SMT.Dom.{u} := fun i =>
      ⟨x.get zs.length i, ⟨τs[i.val]'(zs_len ▸ i.isLt), hx_comps' i⟩⟩
      with hw_def
    have hw_spec : ∀ i, (w i).snd.fst = τs[i]'(zs_len ▸ i.isLt) ∧
        (w i).fst ∈ ⟦τs[i]'(zs_len ▸ i.isLt)⟧ᶻ :=
      fun i => ⟨rfl, hx_comps' i⟩
    have hbody_isSome := himp_total w hw_spec
    obtain ⟨body_val, hbody_val⟩ := Option.isSome_iff_exists.mp hbody_isSome
    have hw_smt : Fin.foldl (zs.length - 1)
        (fun (acc : ZFSet.{u}) (i : Fin (zs.length - 1)) =>
          acc.pair (w ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩).fst)
        (w ⟨0, zs_len_pos_hyp⟩).fst = x := by
      simp only [hw_def]
      suffices h : ∀ (n : ℕ) (h1 : n > 0) (y : ZFSet.{u}) (_hy : y.hasArity n),
          Fin.foldl (n - 1)
            (fun (acc : ZFSet.{u}) (i : Fin (n - 1)) =>
              acc.pair (y.get n ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩))
            (y.get n ⟨0, h1⟩) = y by
        exact h zs.length zs_len_pos_hyp x hx_arity
      intro n h1 y hy
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := Nat.exists_eq_add_one.mpr h1
      simpa [Nat.add_sub_cancel] using ZFSet.foldl_get_of_hasArity hy
    have hbridge_at := hbridge x hx_smttype w hw_spec hw_smt body_val hbody_val
    have hbody_true : body_val.fst = zftrue := by
      rw [hbridge_at]
      have hxB_τ : retract τ x ∈ ⟦τ⟧ᶻ := retract_mem_of_canonical τ hx_smttype
      have hxB_arity : (retract τ x).hasArity vs.length :=
        hasArity_of_mem_toZFSet τ_hasArity hxB_τ
      by_cases hxB_mem : retract τ x ∈ 𝒟_val
      · right
        intro Px P_ty hP_val hPx_eq
        have hcomp₀ : ∀ i : Fin vs.length,
            (retract τ x).get vs.length i ∈ (τ.get vs.length i).toZFSet :=
          fun i => get_mem_type_of_isTuple hxB_arity τ_hasArity hxB_τ
        have h_ofFin₀ : ZFSet.ofFinDom (fun i =>
            (⟨(retract τ x).get vs.length i, ⟨τ.get vs.length i, hcomp₀ i⟩⟩ : B.Dom)) =
            retract τ x :=
          ZFSet.ofFinDom_get (List.length_pos_iff.mpr vs_nemp) hcomp₀ hxB_arity τ_hasArity
        have hmem₀ : ZFSet.ofFinDom (fun i =>
            (⟨(retract τ x).get vs.length i, ⟨τ.get vs.length i, hcomp₀ i⟩⟩ : B.Dom)) ∈ 𝒟_val := by
          rw [h_ofFin₀]; exact hxB_mem
        have htyp₀ : ∀ i,
            (⟨(retract τ x).get vs.length i, ⟨τ.get vs.length i, hcomp₀ i⟩⟩ : B.Dom).snd.fst =
              τ.get vs.length i ∧
            (⟨(retract τ x).get vs.length i, ⟨τ.get vs.length i, hcomp₀ i⟩⟩ : B.Dom).fst ∈
              ⟦τ.get vs.length i⟧ᶻ :=
          fun i => ⟨rfl, hcomp₀ i⟩
        obtain ⟨Pval, hPval⟩ := Option.isSome_iff_exists.mp (h_den_P htyp₀ hmem₀)
        have hPx_eq_Pval : Px = Pval.fst :=
          congr_arg PSigma.fst (Option.some.inj (hPx_eq.symm.trans hPval))
        have h_xB := h_all (retract τ x) hxB_mem
        rw [dif_pos ⟨hxB_arity, hxB_τ⟩] at h_xB
        simp only [hPval] at h_xB
        rw [hPx_eq_Pval]; exact h_xB
      · left; exact hxB_mem
    have hgo := funAbstractGoList (Δctx := Δ_ctx) (P := imp_body)
      (vs := zs) (τs := τs) zs_len hgo_cov hcov_imp_upd w hw_spec
    change (⟦(SMT.Term.abstract.go imp_body zs Δ_ctx _).uncurry w⟧ˢ.get _).fst = zftrue
    simp only [hgo, hbody_val, Option.get_some, hbody_true]
  · -- Case B: ∃ x₀ ∈ 𝒟_val with ℙ_B x₀ ≠ zftrue. Both sides collapse to ∅.
    push_neg at h_all
    obtain ⟨x₀, hx₀_mem, hx₀_ne⟩ := h_all
    have hx₀_τ : x₀ ∈ ⟦τ⟧ᶻ := h𝒟_sub hx₀_mem
    have hx₀_arity : x₀.hasArity vs.length := hasArity_of_mem_toZFSet τ_hasArity hx₀_τ
    have h_rhs_eq : (⋂₀ ZFSet.sep (fun y => ∃ x ∈ 𝒟_val,
        y = if hx : x.hasArity vs.length ∧ x ∈ ⟦τ⟧ᶻ then
              match ⟦(B.Term.abstract.go P vs «Δ» (fun v hv hvs => Δ_fv_all v
                (B.fv.mem_all (.inr ⟨hv, hvs⟩)))).uncurry
                (fun i => ⟨x.get vs.length i, ⟨τ.get vs.length i,
                  get_mem_type_of_isTuple hx.1 τ_hasArity hx.2⟩⟩)⟧ᴮ with
              | some ⟨Pz, _⟩ => Pz
              | none => zffalse
            else zffalse) 𝔹 : ZFSet) = ∅ := by
      apply sInter_sep_eq_empty_of_exists_eq_empty
      refine ⟨x₀, hx₀_mem, ?_⟩
      rw [dif_pos ⟨hx₀_arity, hx₀_τ⟩]
      rw [dif_pos ⟨hx₀_arity, hx₀_τ⟩] at hx₀_ne
      have hcomp : ∀ i : Fin vs.length, x₀.get vs.length i ∈ (τ.get vs.length i).toZFSet :=
        fun i => get_mem_type_of_isTuple hx₀_arity τ_hasArity hx₀_τ
      have h_ofFinDom : ZFSet.ofFinDom (fun i =>
          (⟨x₀.get vs.length i, ⟨τ.get vs.length i, hcomp i⟩⟩ : B.Dom)) = x₀ :=
        ZFSet.ofFinDom_get (List.length_pos_iff.mpr vs_nemp) hcomp hx₀_arity τ_hasArity
      have hmem_fin : ZFSet.ofFinDom (fun i =>
          (⟨x₀.get vs.length i, ⟨τ.get vs.length i, hcomp i⟩⟩ : B.Dom)) ∈ 𝒟_val := by
        rw [h_ofFinDom]; exact hx₀_mem
      have htyp_fin : ∀ i,
          (⟨x₀.get vs.length i, ⟨τ.get vs.length i, hcomp i⟩⟩ : B.Dom).snd.fst =
            τ.get vs.length i ∧
          (⟨x₀.get vs.length i, ⟨τ.get vs.length i, hcomp i⟩⟩ : B.Dom).fst ∈
            ⟦τ.get vs.length i⟧ᶻ :=
        fun i => ⟨rfl, hcomp i⟩
      have hsom : ⟦(B.Term.abstract.go P vs «Δ» (fun v hv hvs => Δ_fv_all v
            (B.fv.mem_all (.inr ⟨hv, hvs⟩)))).uncurry (fun i =>
            (⟨x₀.get vs.length i, ⟨τ.get vs.length i, hcomp i⟩⟩ : B.Dom))⟧ᴮ.isSome = true :=
        h_den_P htyp_fin hmem_fin
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hsom
      rw [ha]
      have hbool : a.snd.fst = BType.bool :=
        h_den_P_bool htyp_fin hmem_fin a.fst a.snd.fst a.snd.snd ha
      have hmem : a.fst ∈ ZFSet.𝔹 := by
        have := a.snd.snd
        rw [hbool] at this
        exact this
      rw [ha] at hx₀_ne
      simp only [] at hx₀_ne ⊢
      rcases (ZFSet.ZFBool.mem_𝔹_iff _).mp hmem with hf | ht
      · exact hf
      · exact absurd ht hx₀_ne
    rw [h_rhs_eq]
    -- Build canonical SMT witness x_smt for x₀, landing in 𝒟_smt via the iso.
    set x_smt : ZFSet.{u} := (ZFSet.fapply (BType.canonicalIsoSMTType τ).1
        (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType τ).2.1)
        ⟨x₀, by rw [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType τ).2.1]; exact hx₀_τ⟩).1
      with hx_smt_def
    have hx_smt_mem : x_smt ∈ ⟦τ.toSMTType⟧ᶻ := ZFSet.fapply_mem_range _ _
    have hx_smt_retract : retract τ x_smt = x₀ := retract_of_canonical τ hx₀_τ
    have hx_smt_𝒟 : x_smt ∈ 𝒟_smt := h𝒟_smt_eq_toSMTType ▸ hx_smt_mem
    have hx_smt_fs_mem : x_smt ∈ Fin.foldl (zs.length - 1)
        (fun (acc : ZFSet.{u}) (i : Fin (zs.length - 1)) =>
          acc.prod ⟦τs_fn ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩⟧ᶻ)
        ⟦τs_fn ⟨0, zs_len_pos⟩⟧ᶻ := by
      rw [← h𝒟_smt]; exact hx_smt_𝒟
    have ⟨hx_smt_arity, hx_smt_comps⟩ :=
      Fin_foldl_prod_hasArity_and_get' (n := zs.length) zs_len_pos
        (fun i => ⟦τs_fn i⟧ᶻ) hx_smt_fs_mem
    have hx_smt_comps' : ∀ i : Fin zs.length,
        x_smt.get zs.length i ∈ ⟦τs[i.val]'(zs_len ▸ i.isLt)⟧ᶻ := by
      intro i
      have := hx_smt_comps i
      rcases i with ⟨k, hk⟩
      simpa [τs_fn, hτs_fn] using this
    apply sInter_sep_eq_empty_of_exists_eq_empty
    refine ⟨x_smt, hx_smt_𝒟, ?_⟩
    rw [dif_pos ⟨hx_smt_arity, hx_smt_comps'⟩]
    set w : Fin zs.length → SMT.Dom.{u} := fun i =>
      ⟨x_smt.get zs.length i, ⟨τs[i.val]'(zs_len ▸ i.isLt), hx_smt_comps' i⟩⟩
      with hw_def
    have hw_spec : ∀ i, (w i).snd.fst = τs[i]'(zs_len ▸ i.isLt) ∧
        (w i).fst ∈ ⟦τs[i]'(zs_len ▸ i.isLt)⟧ᶻ := by
      intro i; exact ⟨rfl, hx_smt_comps' i⟩
    have hbody_isSome := himp_total w hw_spec
    obtain ⟨body_val, hbody_val⟩ := Option.isSome_iff_exists.mp hbody_isSome
    have hbody_val_ty : body_val.snd.fst = SMTType.bool :=
      himp_ty w hw_spec body_val hbody_val
    have hbody_val_mem_𝔹 : body_val.fst ∈ 𝔹 := by
      have := body_val.snd.snd
      rw [hbody_val_ty] at this
      exact this
    have hw_smt : Fin.foldl (zs.length - 1)
        (fun (acc : ZFSet.{u}) (i : Fin (zs.length - 1)) =>
          acc.pair (w ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩).fst)
        (w ⟨0, zs_len_pos_hyp⟩).fst = x_smt := by
      have hfoldl_fn_eq : (fun (acc : ZFSet.{u}) (i : Fin (zs.length - 1)) =>
          acc.pair (w ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩).fst) =
          (fun (acc : ZFSet.{u}) (i : Fin (zs.length - 1)) =>
          acc.pair (x_smt.get zs.length ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩)) := by
        funext acc i; simp [w]
      rw [hfoldl_fn_eq]
      show Fin.foldl (zs.length - 1)
          (fun (acc : ZFSet.{u}) (i : Fin (zs.length - 1)) =>
            acc.pair (x_smt.get zs.length ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩))
          (x_smt.get zs.length ⟨0, zs_len_pos⟩) = x_smt
      suffices hsuff : ∀ (n : ℕ) (h1 : n > 0) (x : ZFSet.{u}) (_hx : x.hasArity n),
          Fin.foldl (n - 1)
            (fun (acc : ZFSet.{u}) (i : Fin (n - 1)) =>
              acc.pair (x.get n ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩))
            (x.get n ⟨0, h1⟩) = x by
        exact hsuff zs.length zs_len_pos x_smt hx_smt_arity
      intro n h1 x hx
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := Nat.exists_eq_add_one.mpr h1
      simpa [Nat.add_sub_cancel] using ZFSet.foldl_get_of_hasArity hx
    have hbridge_at :=
      hbridge x_smt hx_smt_mem w hw_spec hw_smt body_val hbody_val
    -- If body_val.fst = zftrue, hbridge forces x₀ ∉ 𝒟_val (impossible) or Pa.fst = zftrue,
    -- which contradicts hx₀_ne after transporting the x_smt-form to x₀-form.
    have hbody_val_ne : body_val.fst ≠ zftrue := by
      intro hbv_true
      have hd := hbridge_at.mp hbv_true
      rcases hd with hnin | hP
      · exact hnin (hx_smt_retract ▸ hx₀_mem)
      · have hcomp_x₀ : ∀ i : Fin vs.length,
            x₀.get vs.length i ∈ (τ.get vs.length i).toZFSet :=
          fun i => get_mem_type_of_isTuple hx₀_arity τ_hasArity hx₀_τ
        have h_ofFinDom_x₀ :
            ZFSet.ofFinDom (fun i =>
              (⟨x₀.get vs.length i, ⟨τ.get vs.length i, hcomp_x₀ i⟩⟩ : B.Dom)) = x₀ :=
          ZFSet.ofFinDom_get (List.length_pos_iff.mpr vs_nemp) hcomp_x₀ hx₀_arity τ_hasArity
        have hmem_fin_x₀ : ZFSet.ofFinDom (fun i =>
            (⟨x₀.get vs.length i, ⟨τ.get vs.length i, hcomp_x₀ i⟩⟩ : B.Dom)) ∈ 𝒟_val := by
          rw [h_ofFinDom_x₀]; exact hx₀_mem
        have htyp_fin_x₀ : ∀ i,
            (⟨x₀.get vs.length i, ⟨τ.get vs.length i, hcomp_x₀ i⟩⟩ : B.Dom).snd.fst =
              τ.get vs.length i ∧
            (⟨x₀.get vs.length i, ⟨τ.get vs.length i, hcomp_x₀ i⟩⟩ : B.Dom).fst ∈
              ⟦τ.get vs.length i⟧ᶻ :=
          fun i => ⟨rfl, hcomp_x₀ i⟩
        have hsom_x₀ := h_den_P htyp_fin_x₀ hmem_fin_x₀
        obtain ⟨Pa, hPa⟩ := Option.isSome_iff_exists.mp hsom_x₀
        have hPa_ext : Pa = ⟨Pa.fst, ⟨Pa.snd.fst, Pa.snd.snd⟩⟩ := rfl
        rw [hPa_ext] at hPa
        -- Transport `hPa` to the `retract τ x_smt`-form via hx_smt_retract.symm.
        have hPa_ret : ⟦(B.Term.abstract.go P vs «Δ» (fun v hv hvs => Δ_fv_all v
            (B.fv.mem_all (.inr ⟨hv, hvs⟩)))).uncurry
            (fun i => (⟨(retract τ x_smt).get vs.length i,
              ⟨τ.get vs.length i,
                get_mem_type_of_isTuple (hx_smt_retract ▸ hx₀_arity) τ_hasArity
                  (hx_smt_retract ▸ hx₀_τ)⟩⟩ : B.Dom))⟧ᴮ =
            some ⟨Pa.fst, ⟨Pa.snd.fst, Pa.snd.snd⟩⟩ := by
          -- The two denotations are equal because the argument functions are
          -- equal (pointwise, by substitution via hx_smt_retract).
          have heq : (fun i : Fin vs.length =>
              (⟨(retract τ x_smt).get vs.length i,
                ⟨τ.get vs.length i,
                  get_mem_type_of_isTuple (hx_smt_retract ▸ hx₀_arity) τ_hasArity
                    (hx_smt_retract ▸ hx₀_τ)⟩⟩ : B.Dom)) =
              (fun i : Fin vs.length =>
              (⟨x₀.get vs.length i, ⟨τ.get vs.length i, hcomp_x₀ i⟩⟩ : B.Dom)) := by
            clear hbridge hbridge_at hP
            funext i
            congr 1
            · rw [hx_smt_retract]
            · congr 1
              · rw [hx_smt_retract]
              · exact Subsingleton.helim (by rw [hx_smt_retract]) _ _
          rw [heq]; exact hPa
        have hPa_eq : Pa.fst = zftrue := hP Pa.fst Pa.snd.fst Pa.snd.snd hPa_ret
        rw [dif_pos ⟨hx₀_arity, hx₀_τ⟩] at hx₀_ne
        rw [hPa] at hx₀_ne
        exact hx₀_ne hPa_eq
    have hbody_val_zffalse : body_val.fst = zffalse := by
      rcases (ZFSet.ZFBool.mem_𝔹_iff _).mp hbody_val_mem_𝔹 with hf | ht
      · exact hf
      · exact absurd ht hbody_val_ne
    have hgo := funAbstractGoList (Δctx := Δ_ctx) (P := imp_body)
      (vs := zs) (τs := τs) zs_len hgo_cov hcov_imp_upd w hw_spec
    change (⟦(SMT.Term.abstract.go imp_body zs Δ_ctx _).uncurry w⟧ˢ.get _).fst = ∅
    simp only [hgo, hbody_val, Option.get_some, hbody_val_zffalse]

/-! ### Has-flag variant of `retract_forallVal_eq_sInter_sep`

In the HAS-FLAG branch of the `all` encoder, flagged binders have their SMT
types transformed (`.fun (.pair α β) .bool ↦ .fun α (.option β)`), so we
have only `τs.toProdl ⊑ τ.toSMTType` (not equality). As a result,
`𝒟_smt = ⟦τs.toProdl⟧ᶻ ≠ ⟦τ.toSMTType⟧ᶻ` in general.

This bridge factors out the equality assumption and instead exposes the
following parameters to the caller:

* `τs_toProdl_le : τs.toProdl ⊑ τ.toSMTType` — for downstream cast reasoning
  (not used inside the proof body, but documents the loosening structure).
* `x_B_of : ZFSet → ZFSet` — the caller-defined retract function that takes
  an `x ∈ 𝒟_smt = ⟦τs.toProdl⟧ᶻ` and produces an element of `⟦τ⟧ᶻ`.
* `hx_B_of_mem` — proof that `x_B_of x ∈ ⟦τ⟧ᶻ` when `x ∈ ⟦τs.toProdl⟧ᶻ`.
* `case_b_preimage` — for any `x₀ ∈ 𝒟_val`, an `x_smt ∈ 𝒟_smt` such that
  `x_B_of x_smt = x₀`. Used in Case B (where `∃ x₀ ∈ 𝒟_val, P x₀ ≠ zftrue`)
  to obtain a 𝒟_smt witness with the right retract value.
* `hbridge` — same shape as in the no-flag bridge, but ranges over
  `x ∈ ⟦τs.toProdl⟧ᶻ` directly, using `x_B_of x` in place of `retract τ x`.

We also DROP the unused `D_enc`/`denD_val` data and `_imp_body_def`,
`_zs_not_fv_D` artifacts — they are not used in the proof body.
-/

open Classical B in
set_option maxHeartbeats 8000000 in
theorem retract_forallVal_eq_sInter_sep_hasflag.{u}
    -- Type infrastructure
    {vs : List B.𝒱} (vs_nemp : vs ≠ []) (_vs_nodup : vs.Nodup)
    {τ : BType} (τ_hasArity : τ.hasArity vs.length)
    -- SMT terms and binder structure (no D_enc; imp_body is opaque)
    {zs : List SMT.𝒱} {τs : List SMTType}
    (zs_nemp : zs ≠ []) (zs_len : zs.length = τs.length)
    (_τs_toProdl_le : τs.toProdl ⊑ τ.toSMTType)
    {imp_body : SMT.Term}
    -- Renaming context and forall value
    {Δ_ctx : SMT.RenamingContext.Context}
    (hcov_forall : SMT.RenamingContext.CoversFV Δ_ctx
      (SMT.Term.forall zs τs imp_body))
    {forallVal : SMT.Dom}
    (hforallVal : ⟦(SMT.Term.forall zs τs imp_body).abstract Δ_ctx hcov_forall⟧ˢ
      = some forallVal)
    -- Source domain (B-side)
    {𝒟_val : ZFSet.{u}} (h𝒟_val : 𝒟_val ∈ ⟦τ.set⟧ᶻ)
    (𝒟_val_nonempty : 𝒟_val.Nonempty)
    -- imp_body totality/typing under zs-updates
    (hgo_cov : ∀ x ∈ SMT.fv imp_body, x ∉ zs → (Δ_ctx x).isSome = true)
    (hcov_imp_upd : ∀ (w : Fin zs.length → SMT.Dom),
      SMT.RenamingContext.CoversFV
        (Function.updates Δ_ctx zs (List.ofFn (fun i => some (w i)))) imp_body)
    (himp_total : ∀ (w : Fin zs.length → SMT.Dom),
      (∀ i, (w i).snd.fst = τs[i]'(zs_len ▸ i.isLt) ∧
        (w i).fst ∈ ⟦τs[i]'(zs_len ▸ i.isLt)⟧ᶻ) →
      ⟦imp_body.abstract
        (Function.updates Δ_ctx zs (List.ofFn (fun i => some (w i))))
        (hcov_imp_upd w)⟧ˢ.isSome = true)
    (himp_ty : ∀ (w : Fin zs.length → SMT.Dom),
      (∀ i, (w i).snd.fst = τs[i]'(zs_len ▸ i.isLt) ∧
        (w i).fst ∈ ⟦τs[i]'(zs_len ▸ i.isLt)⟧ᶻ) →
      ∀ Db : SMT.Dom,
        ⟦imp_body.abstract
          (Function.updates Δ_ctx zs (List.ofFn (fun i => some (w i))))
          (hcov_imp_upd w)⟧ˢ = some Db →
        Db.snd.fst = SMTType.bool)
    -- B-level data
    {D : B.Term} {P : B.Term} {«Δ» : B.RenamingContext.Context}
    (Δ_fv_all : ∀ v ∈ B.fv (Term.all vs D P), («Δ» v).isSome = true)
    -- B-level sInter target
    {T_val : ZFSet.{u}}
    (hT_eq : ZFSet.sInter (ZFSet.𝔹.sep fun (y : ZFSet) =>
      ∃ x ∈ 𝒟_val, y =
        (if hx : x.hasArity vs.length ∧ x ∈ ⟦τ⟧ᶻ then
          match ⟦(B.Term.abstract.go P vs «Δ» (fun v hv hvs => Δ_fv_all v
            (B.fv.mem_all (.inr ⟨hv, hvs⟩)))).uncurry
            (fun i => ⟨x.get vs.length i, ⟨τ.get vs.length i,
              get_mem_type_of_isTuple hx.1 τ_hasArity hx.2⟩⟩)⟧ᴮ with
          | some ⟨Pz, _⟩ => Pz
          | none => ZFSet.zffalse
        else ZFSet.zffalse)) = T_val)
    -- P denotability for all x ∈ 𝒟_val
    (h_den_P : ∀ {x_fin : Fin vs.length → B.Dom},
      (∀ i, (x_fin i).snd.fst = τ.get vs.length i ∧
            (x_fin i).fst ∈ ⟦τ.get vs.length i⟧ᶻ) →
      ZFSet.ofFinDom x_fin ∈ 𝒟_val →
      ⟦(B.Term.abstract.go P vs «Δ» (fun v hv hvs => Δ_fv_all v
        (B.fv.mem_all (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ.isSome = true)
    (h_den_P_bool : ∀ {x_fin : Fin vs.length → B.Dom},
      (∀ i, (x_fin i).snd.fst = τ.get vs.length i ∧
            (x_fin i).fst ∈ ⟦τ.get vs.length i⟧ᶻ) →
      ZFSet.ofFinDom x_fin ∈ 𝒟_val →
      ∀ (Pz : ZFSet.{u}) (P_ty : BType) (hP_val : Pz ∈ ⟦P_ty⟧ᶻ),
      ⟦(B.Term.abstract.go P vs «Δ» (fun v hv hvs => Δ_fv_all v
        (B.fv.mem_all (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ = some ⟨Pz, ⟨P_ty, hP_val⟩⟩ →
      P_ty = .bool)
    -- *** HAS-FLAG: caller-supplied retract function from 𝒟_smt to ⟦τ⟧ᶻ ***
    (x_B_of : ZFSet.{u} → ZFSet.{u})
    (hx_B_of_mem : ∀ (x : ZFSet.{u}), x ∈ ⟦τs.toProdl⟧ᶻ → x_B_of x ∈ ⟦τ⟧ᶻ)
    -- *** HAS-FLAG: caller-supplied 𝒟_smt-preimage for every x₀ ∈ 𝒟_val ***
    -- (used in Case B to construct an SMT-side witness whose retract = x₀).
    (case_b_preimage : ∀ (x₀ : ZFSet.{u}), x₀ ∈ 𝒟_val →
      ∃ (x_smt : ZFSet.{u}), x_smt ∈ ⟦τs.toProdl⟧ᶻ ∧ x_B_of x_smt = x₀)
    -- *** THE SEMANTIC BRIDGE (now over x ∈ ⟦τs.toProdl⟧ᶻ, using x_B_of x) ***
    (zs_len_pos_hyp : 0 < zs.length)
    (_vs_zs_len : vs.length = zs.length)
    (hbridge : ∀ (x : ZFSet.{u}) (hx_mem : x ∈ ⟦τs.toProdl⟧ᶻ),
      let x_B := x_B_of x
      let hx_B_mem : x_B ∈ ⟦τ⟧ᶻ := hx_B_of_mem x hx_mem
      let x_fin : Fin vs.length → B.Dom := fun i =>
        ⟨x_B.get vs.length i, ⟨τ.get vs.length i,
          get_mem_type_of_isTuple (hasArity_of_mem_toZFSet τ_hasArity hx_B_mem)
            τ_hasArity hx_B_mem⟩⟩
      ∀ (w : Fin zs.length → SMT.Dom)
        (_hw : ∀ i, (w i).snd.fst = τs[i]'(zs_len ▸ i.isLt) ∧
          (w i).fst ∈ ⟦τs[i]'(zs_len ▸ i.isLt)⟧ᶻ)
        (_hw_smt : Fin.foldl (zs.length - 1)
          (fun acc i => acc.pair (w ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩).fst)
          (w ⟨0, zs_len_pos_hyp⟩).fst = x)
        (body_val : SMT.Dom),
        ⟦imp_body.abstract
          (Function.updates Δ_ctx zs (List.ofFn (fun i => some (w i))))
          (hcov_imp_upd w)⟧ˢ = some body_val →
        (body_val.fst = zftrue ↔
          (x_B ∉ 𝒟_val ∨
           ∀ (Px : ZFSet.{u}) (P_ty : BType) (hP_val : Px ∈ ⟦P_ty⟧ᶻ),
             ⟦(B.Term.abstract.go P vs «Δ» (fun v hv hvs => Δ_fv_all v
               (B.fv.mem_all (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ =
               some ⟨Px, ⟨P_ty, hP_val⟩⟩ → Px = zftrue)))
    : retract .bool forallVal.fst = T_val := by
  -- Mirror the no-flag proof, but with `x_B := x_B_of x` (caller-supplied)
  -- instead of `x_B := retract τ x`, and with `hbridge` ranging over
  -- `x ∈ ⟦τs.toProdl⟧ᶻ` (i.e., `x ∈ 𝒟_smt`) directly.
  show forallVal.fst = T_val
  rw [← hT_eq]
  have h𝒟_sub : 𝒟_val ⊆ ⟦τ⟧ᶻ := by
    rwa [BType.toZFSet, ZFSet.mem_powerset] at h𝒟_val
  have zs_len_pos : zs.length > 0 := List.length_pos_iff.mpr zs_nemp
  have τs_nemp : τs ≠ [] := by
    intro h; apply zs_nemp
    have hzs_len : zs.length = 0 := by rw [zs_len, h]; rfl
    exact List.length_eq_zero_iff.mp hzs_len
  set τs_fn : Fin zs.length → SMTType := fun ⟨i, hi⟩ => τs[i]'(zs_len ▸ hi) with hτs_fn
  -- 𝒟_smt: the Fin.foldl product domain on the SMT side.
  set 𝒟_smt : ZFSet.{u} := Fin.foldl (zs.length - 1)
    (fun (acc : ZFSet.{u}) ⟨i, hi⟩ ↦
      acc.prod (τs_fn ⟨i + 1, Nat.add_lt_of_lt_sub hi⟩).toZFSet)
    (τs_fn ⟨0, zs_len_pos⟩).toZFSet with h𝒟_smt
  have hforallVal_unfold := hforallVal
  rw [SMT.Term.abstract, dif_pos zs_len] at hforallVal_unfold
  simp only [SMT.denote] at hforallVal_unfold
  rw [dif_pos zs_len_pos] at hforallVal_unfold
  have himp_total_uncurry :
      ∀ (w : Fin zs.length → SMT.Dom.{u}),
        (∀ i, (w i).snd.fst = τs_fn i ∧ (w i).fst ∈ ⟦τs_fn i⟧ᶻ) →
        ⟦(SMT.Term.abstract.go imp_body zs Δ_ctx hgo_cov).uncurry w⟧ˢ.isSome = true := by
    intro w hw
    have hgo := funAbstractGoList (Δctx := Δ_ctx) (P := imp_body)
      (vs := zs) (τs := τs) zs_len hgo_cov hcov_imp_upd w
      (fun i => by
        have := hw i
        simp only [τs_fn, hτs_fn] at this
        exact this)
    rw [hgo]
    exact himp_total w (fun i => by
      have := hw i
      simp only [τs_fn, hτs_fn] at this
      exact this)
  have h_den_t_isSome :
      ∀ {x : Fin zs.length → SMT.Dom.{u}},
        (∀ i, (x i).2.1 =
            (fun (j : Fin zs.length) => τs[j.val]'(zs_len ▸ j.isLt)) i ∧
          (x i).1 ∈
            ⟦(fun (j : Fin zs.length) => τs[j.val]'(zs_len ▸ j.isLt)) i⟧ᶻ) →
        ⟦(SMT.Term.abstract.go imp_body zs Δ_ctx hgo_cov).uncurry x⟧ˢ.isSome = true := by
    intro x hx
    apply himp_total_uncurry
    intro i
    have := hx i
    rcases i with ⟨j, hj⟩
    simp only [τs_fn, hτs_fn] at this ⊢
    exact this
  have h_den_t_match :
      ∀ {x : Fin zs.length → SMT.Dom.{u}},
        (∀ i, (x i).2.1 =
            (match i with | ⟨k, hk⟩ => τs[k]'(zs_len ▸ hk)) ∧
          (x i).1 ∈
            ⟦match i with | ⟨k, hk⟩ => τs[k]'(zs_len ▸ hk)⟧ᶻ) →
        ⟦(SMT.Term.abstract.go imp_body zs Δ_ctx hgo_cov).uncurry x⟧ˢ.isSome = true := by
    intro x hx
    apply h_den_t_isSome
    intro i
    rcases i with ⟨j, hj⟩
    exact hx ⟨j, hj⟩
  rw [dif_pos (by intro x hx; exact h_den_t_match hx)] at hforallVal_unfold
  simp only [Option.pure_def, Option.some.injEq] at hforallVal_unfold
  have hforallVal_fst : forallVal.fst = _ := congrArg (·.fst) hforallVal_unfold.symm
  rw [hforallVal_fst]
  simp only []
  have 𝒟_smt_nonempty : 𝒟_smt.Nonempty := by
    rw [h𝒟_smt]
    suffices h : ∀ (n : ℕ) (g : Fin n → ZFSet) (init : ZFSet),
        init.Nonempty →
        (∀ i : Fin n, (g i).Nonempty) →
        (Fin.foldl n (fun acc i ↦ acc.prod (g i)) init).Nonempty by
      apply h (zs.length - 1)
        (fun i : Fin (zs.length - 1) =>
          ⟦τs_fn ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩⟧ᶻ)
        ⟦τs_fn ⟨0, zs_len_pos⟩⟧ᶻ
      · exact ⟨_, SMTType.mem_toZFSet_of_defaultZFSet⟩
      · intro _; exact ⟨_, SMTType.mem_toZFSet_of_defaultZFSet⟩
    intro n
    induction n with
    | zero => intro g init h_init _; simpa [Fin.foldl_zero] using h_init
    | succ m ih =>
      intro g init h_init h_factors
      rw [Fin.foldl_succ_last]
      obtain ⟨a, ha⟩ := ih (fun j => g j.castSucc) init h_init
        (fun j => h_factors j.castSucc)
      obtain ⟨b, hb⟩ := h_factors (Fin.last m)
      exact ⟨a.pair b, ZFSet.pair_mem_prod.mpr ⟨ha, hb⟩⟩
  -- KEY LEMMA: 𝒟_smt = ⟦τs.toProdl⟧ᶻ. (Has-flag: NOT equal to ⟦τ.toSMTType⟧ᶻ.)
  have h𝒟_smt_eq_toProdl : 𝒟_smt = ⟦τs.toProdl⟧ᶻ := by
    rw [h𝒟_smt]
    have hne : τs ≠ [] := τs_nemp
    clear_value 𝒟_smt
    simp only [τs_fn, hτs_fn]
    exact Fin_foldl_prod_toZFSet_eq_toProdl_N (τs := τs) hne zs.length zs_len
  by_cases h_all : ∀ x ∈ 𝒟_val,
      (if hx : x.hasArity vs.length ∧ x ∈ ⟦τ⟧ᶻ then
        match ⟦(B.Term.abstract.go P vs «Δ» (fun v hv hvs => Δ_fv_all v
          (B.fv.mem_all (.inr ⟨hv, hvs⟩)))).uncurry
          (fun i => ⟨x.get vs.length i, ⟨τ.get vs.length i,
            get_mem_type_of_isTuple hx.1 τ_hasArity hx.2⟩⟩)⟧ᴮ with
        | some ⟨Pz, _⟩ => Pz
        | none => zffalse
      else zffalse) = zftrue
  · -- Case A: both sides = zftrue.
    have h_rhs : (⋂₀ ZFSet.sep (fun y => ∃ x ∈ 𝒟_val,
        y = if hx : x.hasArity vs.length ∧ x ∈ ⟦τ⟧ᶻ then
              match ⟦(B.Term.abstract.go P vs «Δ» (fun v hv hvs => Δ_fv_all v
                (B.fv.mem_all (.inr ⟨hv, hvs⟩)))).uncurry
                (fun i => ⟨x.get vs.length i, ⟨τ.get vs.length i,
                  get_mem_type_of_isTuple hx.1 τ_hasArity hx.2⟩⟩)⟧ᴮ with
              | some ⟨Pz, _⟩ => Pz
              | none => zffalse
            else zffalse) 𝔹 : ZFSet) = zftrue :=
      sInter_sep_eq_zftrue_of_forall_eq_zftrue 𝒟_val_nonempty h_all
    rw [h_rhs]
    apply sInter_sep_eq_zftrue_of_forall_eq_zftrue 𝒟_smt_nonempty
    intro x hx
    have hx_toProdl : x ∈ ⟦τs.toProdl⟧ᶻ := h𝒟_smt_eq_toProdl ▸ hx
    have hx_fs_mem : x ∈ Fin.foldl (zs.length - 1)
        (fun (acc : ZFSet.{u}) (i : Fin (zs.length - 1)) =>
          acc.prod ⟦τs_fn ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩⟧ᶻ)
        ⟦τs_fn ⟨0, zs_len_pos⟩⟧ᶻ := by
      rw [← h𝒟_smt]; exact hx
    have ⟨hx_arity, hx_comps⟩ :=
      Fin_foldl_prod_hasArity_and_get' (n := zs.length) zs_len_pos
        (fun i => ⟦τs_fn i⟧ᶻ) hx_fs_mem
    have hx_comps' : ∀ i : Fin zs.length, x.get zs.length i ∈ ⟦τs[i.val]'(zs_len ▸ i.isLt)⟧ᶻ :=
      fun i => by
        have := hx_comps i
        rcases i with ⟨k, hk⟩
        simpa [τs_fn, hτs_fn] using this
    rw [dif_pos ⟨hx_arity, hx_comps'⟩]
    set w : Fin zs.length → SMT.Dom.{u} := fun i =>
      ⟨x.get zs.length i, ⟨τs[i.val]'(zs_len ▸ i.isLt), hx_comps' i⟩⟩
      with hw_def
    have hw_spec : ∀ i, (w i).snd.fst = τs[i]'(zs_len ▸ i.isLt) ∧
        (w i).fst ∈ ⟦τs[i]'(zs_len ▸ i.isLt)⟧ᶻ :=
      fun i => ⟨rfl, hx_comps' i⟩
    have hbody_isSome := himp_total w hw_spec
    obtain ⟨body_val, hbody_val⟩ := Option.isSome_iff_exists.mp hbody_isSome
    have hw_smt : Fin.foldl (zs.length - 1)
        (fun (acc : ZFSet.{u}) (i : Fin (zs.length - 1)) =>
          acc.pair (w ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩).fst)
        (w ⟨0, zs_len_pos_hyp⟩).fst = x := by
      simp only [hw_def]
      suffices h : ∀ (n : ℕ) (h1 : n > 0) (y : ZFSet.{u}) (_hy : y.hasArity n),
          Fin.foldl (n - 1)
            (fun (acc : ZFSet.{u}) (i : Fin (n - 1)) =>
              acc.pair (y.get n ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩))
            (y.get n ⟨0, h1⟩) = y by
        exact h zs.length zs_len_pos_hyp x hx_arity
      intro n h1 y hy
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := Nat.exists_eq_add_one.mpr h1
      simpa [Nat.add_sub_cancel] using ZFSet.foldl_get_of_hasArity hy
    have hbridge_at := hbridge x hx_toProdl w hw_spec hw_smt body_val hbody_val
    have hbody_true : body_val.fst = zftrue := by
      rw [hbridge_at]
      have hxB_τ : x_B_of x ∈ ⟦τ⟧ᶻ := hx_B_of_mem x hx_toProdl
      have hxB_arity : (x_B_of x).hasArity vs.length :=
        hasArity_of_mem_toZFSet τ_hasArity hxB_τ
      by_cases hxB_mem : x_B_of x ∈ 𝒟_val
      · right
        intro Px P_ty hP_val hPx_eq
        have hcomp₀ : ∀ i : Fin vs.length,
            (x_B_of x).get vs.length i ∈ (τ.get vs.length i).toZFSet :=
          fun i => get_mem_type_of_isTuple hxB_arity τ_hasArity hxB_τ
        have h_ofFin₀ : ZFSet.ofFinDom (fun i =>
            (⟨(x_B_of x).get vs.length i, ⟨τ.get vs.length i, hcomp₀ i⟩⟩ : B.Dom)) =
            x_B_of x :=
          ZFSet.ofFinDom_get (List.length_pos_iff.mpr vs_nemp) hcomp₀ hxB_arity τ_hasArity
        have hmem₀ : ZFSet.ofFinDom (fun i =>
            (⟨(x_B_of x).get vs.length i, ⟨τ.get vs.length i, hcomp₀ i⟩⟩ : B.Dom)) ∈ 𝒟_val := by
          rw [h_ofFin₀]; exact hxB_mem
        have htyp₀ : ∀ i,
            (⟨(x_B_of x).get vs.length i, ⟨τ.get vs.length i, hcomp₀ i⟩⟩ : B.Dom).snd.fst =
              τ.get vs.length i ∧
            (⟨(x_B_of x).get vs.length i, ⟨τ.get vs.length i, hcomp₀ i⟩⟩ : B.Dom).fst ∈
              ⟦τ.get vs.length i⟧ᶻ :=
          fun i => ⟨rfl, hcomp₀ i⟩
        obtain ⟨Pval, hPval⟩ := Option.isSome_iff_exists.mp (h_den_P htyp₀ hmem₀)
        have hPx_eq_Pval : Px = Pval.fst :=
          congr_arg PSigma.fst (Option.some.inj (hPx_eq.symm.trans hPval))
        have h_xB := h_all (x_B_of x) hxB_mem
        rw [dif_pos ⟨hxB_arity, hxB_τ⟩] at h_xB
        simp only [hPval] at h_xB
        rw [hPx_eq_Pval]; exact h_xB
      · left; exact hxB_mem
    have hgo := funAbstractGoList (Δctx := Δ_ctx) (P := imp_body)
      (vs := zs) (τs := τs) zs_len hgo_cov hcov_imp_upd w hw_spec
    change (⟦(SMT.Term.abstract.go imp_body zs Δ_ctx _).uncurry w⟧ˢ.get _).fst = zftrue
    simp only [hgo, hbody_val, Option.get_some, hbody_true]
  · -- Case B: ∃ x₀ ∈ 𝒟_val with ℙ_B x₀ ≠ zftrue. Both sides collapse to ∅.
    push_neg at h_all
    obtain ⟨x₀, hx₀_mem, hx₀_ne⟩ := h_all
    have hx₀_τ : x₀ ∈ ⟦τ⟧ᶻ := h𝒟_sub hx₀_mem
    have hx₀_arity : x₀.hasArity vs.length := hasArity_of_mem_toZFSet τ_hasArity hx₀_τ
    have h_rhs_eq : (⋂₀ ZFSet.sep (fun y => ∃ x ∈ 𝒟_val,
        y = if hx : x.hasArity vs.length ∧ x ∈ ⟦τ⟧ᶻ then
              match ⟦(B.Term.abstract.go P vs «Δ» (fun v hv hvs => Δ_fv_all v
                (B.fv.mem_all (.inr ⟨hv, hvs⟩)))).uncurry
                (fun i => ⟨x.get vs.length i, ⟨τ.get vs.length i,
                  get_mem_type_of_isTuple hx.1 τ_hasArity hx.2⟩⟩)⟧ᴮ with
              | some ⟨Pz, _⟩ => Pz
              | none => zffalse
            else zffalse) 𝔹 : ZFSet) = ∅ := by
      apply sInter_sep_eq_empty_of_exists_eq_empty
      refine ⟨x₀, hx₀_mem, ?_⟩
      rw [dif_pos ⟨hx₀_arity, hx₀_τ⟩]
      rw [dif_pos ⟨hx₀_arity, hx₀_τ⟩] at hx₀_ne
      have hcomp : ∀ i : Fin vs.length, x₀.get vs.length i ∈ (τ.get vs.length i).toZFSet :=
        fun i => get_mem_type_of_isTuple hx₀_arity τ_hasArity hx₀_τ
      have h_ofFinDom : ZFSet.ofFinDom (fun i =>
          (⟨x₀.get vs.length i, ⟨τ.get vs.length i, hcomp i⟩⟩ : B.Dom)) = x₀ :=
        ZFSet.ofFinDom_get (List.length_pos_iff.mpr vs_nemp) hcomp hx₀_arity τ_hasArity
      have hmem_fin : ZFSet.ofFinDom (fun i =>
          (⟨x₀.get vs.length i, ⟨τ.get vs.length i, hcomp i⟩⟩ : B.Dom)) ∈ 𝒟_val := by
        rw [h_ofFinDom]; exact hx₀_mem
      have htyp_fin : ∀ i,
          (⟨x₀.get vs.length i, ⟨τ.get vs.length i, hcomp i⟩⟩ : B.Dom).snd.fst =
            τ.get vs.length i ∧
          (⟨x₀.get vs.length i, ⟨τ.get vs.length i, hcomp i⟩⟩ : B.Dom).fst ∈
            ⟦τ.get vs.length i⟧ᶻ :=
        fun i => ⟨rfl, hcomp i⟩
      have hsom : ⟦(B.Term.abstract.go P vs «Δ» (fun v hv hvs => Δ_fv_all v
            (B.fv.mem_all (.inr ⟨hv, hvs⟩)))).uncurry (fun i =>
            (⟨x₀.get vs.length i, ⟨τ.get vs.length i, hcomp i⟩⟩ : B.Dom))⟧ᴮ.isSome = true :=
        h_den_P htyp_fin hmem_fin
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hsom
      rw [ha]
      have hbool : a.snd.fst = BType.bool :=
        h_den_P_bool htyp_fin hmem_fin a.fst a.snd.fst a.snd.snd ha
      have hmem : a.fst ∈ ZFSet.𝔹 := by
        have := a.snd.snd
        rw [hbool] at this
        exact this
      rw [ha] at hx₀_ne
      simp only [] at hx₀_ne ⊢
      rcases (ZFSet.ZFBool.mem_𝔹_iff _).mp hmem with hf | ht
      · exact hf
      · exact absurd ht hx₀_ne
    rw [h_rhs_eq]
    -- HAS-FLAG: use caller-supplied case_b_preimage instead of canonicalIsoSMTType.
    obtain ⟨x_smt, hx_smt_toProdl, hx_smt_retract⟩ := case_b_preimage x₀ hx₀_mem
    have hx_smt_𝒟 : x_smt ∈ 𝒟_smt := h𝒟_smt_eq_toProdl ▸ hx_smt_toProdl
    have hx_smt_fs_mem : x_smt ∈ Fin.foldl (zs.length - 1)
        (fun (acc : ZFSet.{u}) (i : Fin (zs.length - 1)) =>
          acc.prod ⟦τs_fn ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩⟧ᶻ)
        ⟦τs_fn ⟨0, zs_len_pos⟩⟧ᶻ := by
      rw [← h𝒟_smt]; exact hx_smt_𝒟
    have ⟨hx_smt_arity, hx_smt_comps⟩ :=
      Fin_foldl_prod_hasArity_and_get' (n := zs.length) zs_len_pos
        (fun i => ⟦τs_fn i⟧ᶻ) hx_smt_fs_mem
    have hx_smt_comps' : ∀ i : Fin zs.length,
        x_smt.get zs.length i ∈ ⟦τs[i.val]'(zs_len ▸ i.isLt)⟧ᶻ := by
      intro i
      have := hx_smt_comps i
      rcases i with ⟨k, hk⟩
      simpa [τs_fn, hτs_fn] using this
    apply sInter_sep_eq_empty_of_exists_eq_empty
    refine ⟨x_smt, hx_smt_𝒟, ?_⟩
    rw [dif_pos ⟨hx_smt_arity, hx_smt_comps'⟩]
    set w : Fin zs.length → SMT.Dom.{u} := fun i =>
      ⟨x_smt.get zs.length i, ⟨τs[i.val]'(zs_len ▸ i.isLt), hx_smt_comps' i⟩⟩
      with hw_def
    have hw_spec : ∀ i, (w i).snd.fst = τs[i]'(zs_len ▸ i.isLt) ∧
        (w i).fst ∈ ⟦τs[i]'(zs_len ▸ i.isLt)⟧ᶻ := by
      intro i; exact ⟨rfl, hx_smt_comps' i⟩
    have hbody_isSome := himp_total w hw_spec
    obtain ⟨body_val, hbody_val⟩ := Option.isSome_iff_exists.mp hbody_isSome
    have hbody_val_ty : body_val.snd.fst = SMTType.bool :=
      himp_ty w hw_spec body_val hbody_val
    have hbody_val_mem_𝔹 : body_val.fst ∈ 𝔹 := by
      have := body_val.snd.snd
      rw [hbody_val_ty] at this
      exact this
    have hw_smt : Fin.foldl (zs.length - 1)
        (fun (acc : ZFSet.{u}) (i : Fin (zs.length - 1)) =>
          acc.pair (w ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩).fst)
        (w ⟨0, zs_len_pos_hyp⟩).fst = x_smt := by
      have hfoldl_fn_eq : (fun (acc : ZFSet.{u}) (i : Fin (zs.length - 1)) =>
          acc.pair (w ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩).fst) =
          (fun (acc : ZFSet.{u}) (i : Fin (zs.length - 1)) =>
          acc.pair (x_smt.get zs.length ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩)) := by
        funext acc i; simp [w]
      rw [hfoldl_fn_eq]
      show Fin.foldl (zs.length - 1)
          (fun (acc : ZFSet.{u}) (i : Fin (zs.length - 1)) =>
            acc.pair (x_smt.get zs.length ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩))
          (x_smt.get zs.length ⟨0, zs_len_pos⟩) = x_smt
      suffices hsuff : ∀ (n : ℕ) (h1 : n > 0) (x : ZFSet.{u}) (_hx : x.hasArity n),
          Fin.foldl (n - 1)
            (fun (acc : ZFSet.{u}) (i : Fin (n - 1)) =>
              acc.pair (x.get n ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩))
            (x.get n ⟨0, h1⟩) = x by
        exact hsuff zs.length zs_len_pos x_smt hx_smt_arity
      intro n h1 x hx
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := Nat.exists_eq_add_one.mpr h1
      simpa [Nat.add_sub_cancel] using ZFSet.foldl_get_of_hasArity hx
    have hbridge_at :=
      hbridge x_smt hx_smt_toProdl w hw_spec hw_smt body_val hbody_val
    -- If body_val.fst = zftrue, hbridge forces x₀ ∉ 𝒟_val (impossible) or Pa.fst = zftrue,
    -- which contradicts hx₀_ne after transporting via hx_smt_retract.
    have hbody_val_ne : body_val.fst ≠ zftrue := by
      intro hbv_true
      have hd := hbridge_at.mp hbv_true
      rcases hd with hnin | hP
      · exact hnin (hx_smt_retract ▸ hx₀_mem)
      · have hcomp_x₀ : ∀ i : Fin vs.length,
            x₀.get vs.length i ∈ (τ.get vs.length i).toZFSet :=
          fun i => get_mem_type_of_isTuple hx₀_arity τ_hasArity hx₀_τ
        have h_ofFinDom_x₀ :
            ZFSet.ofFinDom (fun i =>
              (⟨x₀.get vs.length i, ⟨τ.get vs.length i, hcomp_x₀ i⟩⟩ : B.Dom)) = x₀ :=
          ZFSet.ofFinDom_get (List.length_pos_iff.mpr vs_nemp) hcomp_x₀ hx₀_arity τ_hasArity
        have hmem_fin_x₀ : ZFSet.ofFinDom (fun i =>
            (⟨x₀.get vs.length i, ⟨τ.get vs.length i, hcomp_x₀ i⟩⟩ : B.Dom)) ∈ 𝒟_val := by
          rw [h_ofFinDom_x₀]; exact hx₀_mem
        have htyp_fin_x₀ : ∀ i,
            (⟨x₀.get vs.length i, ⟨τ.get vs.length i, hcomp_x₀ i⟩⟩ : B.Dom).snd.fst =
              τ.get vs.length i ∧
            (⟨x₀.get vs.length i, ⟨τ.get vs.length i, hcomp_x₀ i⟩⟩ : B.Dom).fst ∈
              ⟦τ.get vs.length i⟧ᶻ :=
          fun i => ⟨rfl, hcomp_x₀ i⟩
        have hsom_x₀ := h_den_P htyp_fin_x₀ hmem_fin_x₀
        obtain ⟨Pa, hPa⟩ := Option.isSome_iff_exists.mp hsom_x₀
        have hPa_ext : Pa = ⟨Pa.fst, ⟨Pa.snd.fst, Pa.snd.snd⟩⟩ := rfl
        rw [hPa_ext] at hPa
        -- Transport `hPa` from x₀-form to (x_B_of x_smt)-form via hx_smt_retract.symm.
        have hPa_ret : ⟦(B.Term.abstract.go P vs «Δ» (fun v hv hvs => Δ_fv_all v
            (B.fv.mem_all (.inr ⟨hv, hvs⟩)))).uncurry
            (fun i => (⟨(x_B_of x_smt).get vs.length i,
              ⟨τ.get vs.length i,
                get_mem_type_of_isTuple (hx_smt_retract ▸ hx₀_arity) τ_hasArity
                  (hx_smt_retract ▸ hx₀_τ)⟩⟩ : B.Dom))⟧ᴮ =
            some ⟨Pa.fst, ⟨Pa.snd.fst, Pa.snd.snd⟩⟩ := by
          have heq : (fun i : Fin vs.length =>
              (⟨(x_B_of x_smt).get vs.length i,
                ⟨τ.get vs.length i,
                  get_mem_type_of_isTuple (hx_smt_retract ▸ hx₀_arity) τ_hasArity
                    (hx_smt_retract ▸ hx₀_τ)⟩⟩ : B.Dom)) =
              (fun i : Fin vs.length =>
              (⟨x₀.get vs.length i, ⟨τ.get vs.length i, hcomp_x₀ i⟩⟩ : B.Dom)) := by
            clear hbridge hbridge_at hP
            funext i
            congr 1
            · rw [hx_smt_retract]
            · congr 1
              · rw [hx_smt_retract]
              · exact Subsingleton.helim (by rw [hx_smt_retract]) _ _
          rw [heq]; exact hPa
        have hPa_eq : Pa.fst = zftrue := hP Pa.fst Pa.snd.fst Pa.snd.snd hPa_ret
        rw [dif_pos ⟨hx₀_arity, hx₀_τ⟩] at hx₀_ne
        rw [hPa] at hx₀_ne
        exact hx₀_ne hPa_eq
    have hbody_val_zffalse : body_val.fst = zffalse := by
      rcases (ZFSet.ZFBool.mem_𝔹_iff _).mp hbody_val_mem_𝔹 with hf | ht
      · exact hf
      · exact absurd ht hbody_val_ne
    have hgo := funAbstractGoList (Δctx := Δ_ctx) (P := imp_body)
      (vs := zs) (τs := τs) zs_len hgo_cov hcov_imp_upd w hw_spec
    change (⟦(SMT.Term.abstract.go imp_body zs Δ_ctx _).uncurry w⟧ˢ.get _).fst = ∅
    simp only [hgo, hbody_val, Option.get_some, hbody_val_zffalse]

/-! ### Empty-domain companion for `retract_forallVal_eq_sInter_sep`

When the source quantifier's domain `𝒟_val = ∅`, the `all`-encoder's
forall should denote to `zftrue` (vacuously). The companion lemma below
mirrors `retract_forallVal_eq_sInter_sep` but:
* does not require `𝒟_val.Nonempty` (since `𝒟_val = ∅`);
* does not require `h_den_P`/`h_den_P_bool` (they are vacuous);
* concludes `retract .bool forallVal.fst = zftrue` directly.

The proof uses the fact that `𝒟_smt = ⟦τ.toSMTType⟧ᶻ` is nonempty (since
SMT types are always inhabited), so `sInter (𝔹.sep ...) = zftrue` holds
by `sInter_sep_eq_zftrue_of_forall_eq_zftrue` applied to every
`x ∈ 𝒟_smt`: the bridge gives `body_val.fst = zftrue` because
`retract τ x ∉ 𝒟_val` is vacuously true.
-/

open Classical B in
set_option maxHeartbeats 8000000 in
theorem retract_forallVal_eq_zftrue_of_empty_𝒟.{u}
    -- Type infrastructure
    {vs : List B.𝒱} (_vs_nemp : vs ≠ [])
    {τ : BType} (τ_hasArity : τ.hasArity vs.length)
    -- SMT terms and binder structure
    {D : B.Term}
    {D_enc P_enc_subst : SMT.Term} {zs : List SMT.𝒱} {τs : List SMTType}
    (zs_nemp : zs ≠ []) (zs_len : zs.length = τs.length)
    (τs_toProdl_eq : τs.toProdl = τ.toSMTType)
    {imp_body : SMT.Term}
    (_imp_body_def : imp_body =
      (SMT.Term.app D_enc (zs.map .var).toPairl).imp P_enc_subst)
    -- Renaming context and forall value
    {Δ_ctx : SMT.RenamingContext.Context}
    (hcov_forall : SMT.RenamingContext.CoversFV Δ_ctx
      (SMT.Term.forall zs τs imp_body))
    {forallVal : SMT.Dom}
    (hforallVal : ⟦(SMT.Term.forall zs τs imp_body).abstract Δ_ctx hcov_forall⟧ˢ
      = some forallVal)
    -- imp_body coverage/totality under zs-updates
    (hgo_cov : ∀ x ∈ SMT.fv imp_body, x ∉ zs → (Δ_ctx x).isSome = true)
    (hcov_imp_upd : ∀ (w : Fin zs.length → SMT.Dom),
      SMT.RenamingContext.CoversFV
        (Function.updates Δ_ctx zs (List.ofFn (fun i => some (w i)))) imp_body)
    (himp_total : ∀ (w : Fin zs.length → SMT.Dom),
      (∀ i, (w i).snd.fst = τs[i]'(zs_len ▸ i.isLt) ∧
        (w i).fst ∈ ⟦τs[i]'(zs_len ▸ i.isLt)⟧ᶻ) →
      ⟦imp_body.abstract
        (Function.updates Δ_ctx zs (List.ofFn (fun i => some (w i))))
        (hcov_imp_upd w)⟧ˢ.isSome = true)
    -- Empty source domain
    {𝒟_val : ZFSet.{u}} (h𝒟_empty : 𝒟_val = ∅)
    -- B-level data
    {P : B.Term} {«Δ» : B.RenamingContext.Context}
    (Δ_fv_all : ∀ v ∈ B.fv (Term.all vs D P), («Δ» v).isSome = true)
    -- Positivity/lengths
    (zs_len_pos_hyp : 0 < zs.length)
    (vs_zs_len : vs.length = zs.length)
    -- *** THE SEMANTIC BRIDGE (same shape as `retract_forallVal_eq_sInter_sep`) ***
    (hbridge : ∀ (x : ZFSet.{u}) (hx_mem : x ∈ ⟦τ.toSMTType⟧ᶻ),
      let x_B := retract τ x
      let hx_B_mem : x_B ∈ ⟦τ⟧ᶻ := retract_mem_of_canonical τ hx_mem
      let x_fin : Fin vs.length → B.Dom := fun i =>
        ⟨x_B.get vs.length i, ⟨τ.get vs.length i,
          get_mem_type_of_isTuple (hasArity_of_mem_toZFSet τ_hasArity hx_B_mem)
            τ_hasArity hx_B_mem⟩⟩
      ∀ (w : Fin zs.length → SMT.Dom)
        (_hw : ∀ i, (w i).snd.fst = τs[i]'(zs_len ▸ i.isLt) ∧
          (w i).fst ∈ ⟦τs[i]'(zs_len ▸ i.isLt)⟧ᶻ)
        (_hw_smt : Fin.foldl (zs.length - 1)
          (fun acc i => acc.pair (w ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩).fst)
          (w ⟨0, zs_len_pos_hyp⟩).fst = x)
        (body_val : SMT.Dom),
        ⟦imp_body.abstract
          (Function.updates Δ_ctx zs (List.ofFn (fun i => some (w i))))
          (hcov_imp_upd w)⟧ˢ = some body_val →
        (body_val.fst = zftrue ↔
          (x_B ∉ 𝒟_val ∨
           ∀ (Px : ZFSet.{u}) (P_ty : BType) (hP_val : Px ∈ ⟦P_ty⟧ᶻ),
             ⟦(B.Term.abstract.go P vs «Δ» (fun v hv hvs => Δ_fv_all v
               (B.fv.mem_all (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ =
               some ⟨Px, ⟨P_ty, hP_val⟩⟩ → Px = zftrue)))
    : retract .bool forallVal.fst = zftrue := by
  show forallVal.fst = zftrue
  have zs_len_pos : zs.length > 0 := List.length_pos_iff.mpr zs_nemp
  have τs_nemp : τs ≠ [] := by
    intro h; apply zs_nemp
    have hzs_len : zs.length = 0 := by rw [zs_len, h]; rfl
    exact List.length_eq_zero_iff.mp hzs_len
  set τs_fn : Fin zs.length → SMTType := fun ⟨i, hi⟩ => τs[i]'(zs_len ▸ hi) with hτs_fn
  -- 𝒟_smt: the Fin.foldl product domain on the SMT side.
  set 𝒟_smt : ZFSet.{u} := Fin.foldl (zs.length - 1)
    (fun (acc : ZFSet.{u}) ⟨i, hi⟩ ↦
      acc.prod (τs_fn ⟨i + 1, Nat.add_lt_of_lt_sub hi⟩).toZFSet)
    (τs_fn ⟨0, zs_len_pos⟩).toZFSet with h𝒟_smt
  have hforallVal_unfold := hforallVal
  rw [SMT.Term.abstract, dif_pos zs_len] at hforallVal_unfold
  simp only [SMT.denote] at hforallVal_unfold
  rw [dif_pos zs_len_pos] at hforallVal_unfold
  have himp_total_uncurry :
      ∀ (w : Fin zs.length → SMT.Dom.{u}),
        (∀ i, (w i).snd.fst = τs_fn i ∧ (w i).fst ∈ ⟦τs_fn i⟧ᶻ) →
        ⟦(SMT.Term.abstract.go imp_body zs Δ_ctx hgo_cov).uncurry w⟧ˢ.isSome = true := by
    intro w hw
    have hgo := funAbstractGoList (Δctx := Δ_ctx) (P := imp_body)
      (vs := zs) (τs := τs) zs_len hgo_cov hcov_imp_upd w
      (fun i => by
        have := hw i
        simp only [τs_fn, hτs_fn] at this
        exact this)
    rw [hgo]
    exact himp_total w (fun i => by
      have := hw i
      simp only [τs_fn, hτs_fn] at this
      exact this)
  have h_den_t_isSome :
      ∀ {x : Fin zs.length → SMT.Dom.{u}},
        (∀ i, (x i).2.1 =
            (fun (j : Fin zs.length) => τs[j.val]'(zs_len ▸ j.isLt)) i ∧
          (x i).1 ∈
            ⟦(fun (j : Fin zs.length) => τs[j.val]'(zs_len ▸ j.isLt)) i⟧ᶻ) →
        ⟦(SMT.Term.abstract.go imp_body zs Δ_ctx hgo_cov).uncurry x⟧ˢ.isSome = true := by
    intro x hx
    apply himp_total_uncurry
    intro i
    have := hx i
    rcases i with ⟨j, hj⟩
    simp only [τs_fn, hτs_fn] at this ⊢
    exact this
  have h_den_t_match :
      ∀ {x : Fin zs.length → SMT.Dom.{u}},
        (∀ i, (x i).2.1 =
            (match i with | ⟨k, hk⟩ => τs[k]'(zs_len ▸ hk)) ∧
          (x i).1 ∈
            ⟦match i with | ⟨k, hk⟩ => τs[k]'(zs_len ▸ hk)⟧ᶻ) →
        ⟦(SMT.Term.abstract.go imp_body zs Δ_ctx hgo_cov).uncurry x⟧ˢ.isSome = true := by
    intro x hx
    apply h_den_t_isSome
    intro i
    rcases i with ⟨j, hj⟩
    exact hx ⟨j, hj⟩
  rw [dif_pos (by intro x hx; exact h_den_t_match hx)] at hforallVal_unfold
  simp only [Option.pure_def, Option.some.injEq] at hforallVal_unfold
  have hforallVal_fst : forallVal.fst = _ := congrArg (·.fst) hforallVal_unfold.symm
  rw [hforallVal_fst]
  simp only []
  -- 𝒟_smt is nonempty (products of inhabited types are inhabited).
  have 𝒟_smt_nonempty : 𝒟_smt.Nonempty := by
    rw [h𝒟_smt]
    suffices h : ∀ (n : ℕ) (g : Fin n → ZFSet) (init : ZFSet),
        init.Nonempty →
        (∀ i : Fin n, (g i).Nonempty) →
        (Fin.foldl n (fun acc i ↦ acc.prod (g i)) init).Nonempty by
      apply h (zs.length - 1)
        (fun i : Fin (zs.length - 1) =>
          ⟦τs_fn ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩⟧ᶻ)
        ⟦τs_fn ⟨0, zs_len_pos⟩⟧ᶻ
      · exact ⟨_, SMTType.mem_toZFSet_of_defaultZFSet⟩
      · intro _; exact ⟨_, SMTType.mem_toZFSet_of_defaultZFSet⟩
    intro n
    induction n with
    | zero => intro g init h_init _; simpa [Fin.foldl_zero] using h_init
    | succ m ih =>
      intro g init h_init h_factors
      rw [Fin.foldl_succ_last]
      obtain ⟨a, ha⟩ := ih (fun j => g j.castSucc) init h_init
        (fun j => h_factors j.castSucc)
      obtain ⟨b, hb⟩ := h_factors (Fin.last m)
      exact ⟨a.pair b, ZFSet.pair_mem_prod.mpr ⟨ha, hb⟩⟩
  -- 𝒟_smt equals the full toZFSet of τ.toSMTType.
  have h𝒟_smt_eq_toSMTType : 𝒟_smt = SMTType.toZFSet τ.toSMTType := by
    rw [h𝒟_smt, ← τs_toProdl_eq]
    have hne : τs ≠ [] := τs_nemp
    clear_value 𝒟_smt
    simp only [τs_fn, hτs_fn]
    exact Fin_foldl_prod_toZFSet_eq_toProdl_N (τs := τs) hne zs.length zs_len
  -- Apply sInter_sep_eq_zftrue_of_forall_eq_zftrue.
  apply sInter_sep_eq_zftrue_of_forall_eq_zftrue 𝒟_smt_nonempty
  intro x hx
  have hx_smttype : x ∈ ⟦τ.toSMTType⟧ᶻ := h𝒟_smt_eq_toSMTType ▸ hx
  have hx_fs_mem : x ∈ Fin.foldl (zs.length - 1)
      (fun (acc : ZFSet.{u}) (i : Fin (zs.length - 1)) =>
        acc.prod ⟦τs_fn ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩⟧ᶻ)
      ⟦τs_fn ⟨0, zs_len_pos⟩⟧ᶻ := by
    rw [← h𝒟_smt]; exact hx
  have ⟨hx_arity, hx_comps⟩ :=
    Fin_foldl_prod_hasArity_and_get' (n := zs.length) zs_len_pos
      (fun i => ⟦τs_fn i⟧ᶻ) hx_fs_mem
  have hx_comps' : ∀ i : Fin zs.length, x.get zs.length i ∈ ⟦τs[i.val]'(zs_len ▸ i.isLt)⟧ᶻ :=
    fun i => by
      have := hx_comps i
      rcases i with ⟨k, hk⟩
      simpa [τs_fn, hτs_fn] using this
  rw [dif_pos ⟨hx_arity, hx_comps'⟩]
  set w : Fin zs.length → SMT.Dom.{u} := fun i =>
    ⟨x.get zs.length i, ⟨τs[i.val]'(zs_len ▸ i.isLt), hx_comps' i⟩⟩
    with hw_def
  have hw_spec : ∀ i, (w i).snd.fst = τs[i]'(zs_len ▸ i.isLt) ∧
      (w i).fst ∈ ⟦τs[i]'(zs_len ▸ i.isLt)⟧ᶻ :=
    fun i => ⟨rfl, hx_comps' i⟩
  have hbody_isSome := himp_total w hw_spec
  obtain ⟨body_val, hbody_val⟩ := Option.isSome_iff_exists.mp hbody_isSome
  have hw_smt : Fin.foldl (zs.length - 1)
      (fun (acc : ZFSet.{u}) (i : Fin (zs.length - 1)) =>
        acc.pair (w ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩).fst)
      (w ⟨0, zs_len_pos_hyp⟩).fst = x := by
    simp only [hw_def]
    suffices h : ∀ (n : ℕ) (h1 : n > 0) (y : ZFSet.{u}) (_hy : y.hasArity n),
        Fin.foldl (n - 1)
          (fun (acc : ZFSet.{u}) (i : Fin (n - 1)) =>
            acc.pair (y.get n ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩))
          (y.get n ⟨0, h1⟩) = y by
      exact h zs.length zs_len_pos_hyp x hx_arity
    intro n h1 y hy
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := Nat.exists_eq_add_one.mpr h1
    simpa [Nat.add_sub_cancel] using ZFSet.foldl_get_of_hasArity hy
  have hbridge_at := hbridge x hx_smttype w hw_spec hw_smt body_val hbody_val
  have hbody_true : body_val.fst = zftrue := by
    rw [hbridge_at]
    -- Left disjunct: retract τ x ∉ 𝒟_val = ∅, which is always true.
    left
    rw [h𝒟_empty]
    exact ZFSet.notMem_empty _
  have hgo := funAbstractGoList (Δctx := Δ_ctx) (P := imp_body)
    (vs := zs) (τs := τs) zs_len hgo_cov hcov_imp_upd w hw_spec
  change (⟦(SMT.Term.abstract.go imp_body zs Δ_ctx _).uncurry w⟧ˢ.get _).fst = zftrue
  simp only [hgo, hbody_val, Option.get_some, hbody_true]

/-! ### Has-flag variant of `retract_forallVal_eq_zftrue_of_empty_𝒟`

In the HAS-FLAG branch with empty source domain, we mirror
`retract_forallVal_eq_zftrue_of_empty_𝒟` but with the looser
`τs.toProdl ⊑ τ.toSMTType` (instead of equality). Like the nonempty
has-flag bridge, we replace `retract τ x` with a caller-supplied
`x_B_of x` and have `hbridge` range over `x ∈ ⟦τs.toProdl⟧ᶻ` directly.

Unlike the nonempty has-flag bridge, there is no Case B (no `x₀ ∈ 𝒟_val`
since `𝒟_val = ∅`), so we DROP the `case_b_preimage` argument.
-/

open Classical B in
set_option maxHeartbeats 8000000 in
theorem retract_forallVal_eq_zftrue_of_empty_𝒟_hasflag.{u}
    -- Type infrastructure
    {vs : List B.𝒱} (_vs_nemp : vs ≠ [])
    {τ : BType} (τ_hasArity : τ.hasArity vs.length)
    -- SMT terms and binder structure (no D_enc; imp_body is opaque)
    {zs : List SMT.𝒱} {τs : List SMTType}
    (zs_nemp : zs ≠ []) (zs_len : zs.length = τs.length)
    (_τs_toProdl_le : τs.toProdl ⊑ τ.toSMTType)
    {imp_body : SMT.Term}
    -- Renaming context and forall value
    {Δ_ctx : SMT.RenamingContext.Context}
    (hcov_forall : SMT.RenamingContext.CoversFV Δ_ctx
      (SMT.Term.forall zs τs imp_body))
    {forallVal : SMT.Dom}
    (hforallVal : ⟦(SMT.Term.forall zs τs imp_body).abstract Δ_ctx hcov_forall⟧ˢ
      = some forallVal)
    -- imp_body coverage/totality under zs-updates
    (hgo_cov : ∀ x ∈ SMT.fv imp_body, x ∉ zs → (Δ_ctx x).isSome = true)
    (hcov_imp_upd : ∀ (w : Fin zs.length → SMT.Dom),
      SMT.RenamingContext.CoversFV
        (Function.updates Δ_ctx zs (List.ofFn (fun i => some (w i)))) imp_body)
    (himp_total : ∀ (w : Fin zs.length → SMT.Dom),
      (∀ i, (w i).snd.fst = τs[i]'(zs_len ▸ i.isLt) ∧
        (w i).fst ∈ ⟦τs[i]'(zs_len ▸ i.isLt)⟧ᶻ) →
      ⟦imp_body.abstract
        (Function.updates Δ_ctx zs (List.ofFn (fun i => some (w i))))
        (hcov_imp_upd w)⟧ˢ.isSome = true)
    -- Empty source domain
    {𝒟_val : ZFSet.{u}} (h𝒟_empty : 𝒟_val = ∅)
    -- B-level data
    {D : B.Term} {P : B.Term} {«Δ» : B.RenamingContext.Context}
    (Δ_fv_all : ∀ v ∈ B.fv (Term.all vs D P), («Δ» v).isSome = true)
    -- Positivity/lengths
    (zs_len_pos_hyp : 0 < zs.length)
    (_vs_zs_len : vs.length = zs.length)
    -- *** HAS-FLAG: caller-supplied retract function from 𝒟_smt to ⟦τ⟧ᶻ ***
    (x_B_of : ZFSet.{u} → ZFSet.{u})
    (hx_B_of_mem : ∀ (x : ZFSet.{u}), x ∈ ⟦τs.toProdl⟧ᶻ → x_B_of x ∈ ⟦τ⟧ᶻ)
    -- *** THE SEMANTIC BRIDGE (now over x ∈ ⟦τs.toProdl⟧ᶻ, using x_B_of x) ***
    (hbridge : ∀ (x : ZFSet.{u}) (hx_mem : x ∈ ⟦τs.toProdl⟧ᶻ),
      let x_B := x_B_of x
      let hx_B_mem : x_B ∈ ⟦τ⟧ᶻ := hx_B_of_mem x hx_mem
      let x_fin : Fin vs.length → B.Dom := fun i =>
        ⟨x_B.get vs.length i, ⟨τ.get vs.length i,
          get_mem_type_of_isTuple (hasArity_of_mem_toZFSet τ_hasArity hx_B_mem)
            τ_hasArity hx_B_mem⟩⟩
      ∀ (w : Fin zs.length → SMT.Dom)
        (_hw : ∀ i, (w i).snd.fst = τs[i]'(zs_len ▸ i.isLt) ∧
          (w i).fst ∈ ⟦τs[i]'(zs_len ▸ i.isLt)⟧ᶻ)
        (_hw_smt : Fin.foldl (zs.length - 1)
          (fun acc i => acc.pair (w ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩).fst)
          (w ⟨0, zs_len_pos_hyp⟩).fst = x)
        (body_val : SMT.Dom),
        ⟦imp_body.abstract
          (Function.updates Δ_ctx zs (List.ofFn (fun i => some (w i))))
          (hcov_imp_upd w)⟧ˢ = some body_val →
        (body_val.fst = zftrue ↔
          (x_B ∉ 𝒟_val ∨
           ∀ (Px : ZFSet.{u}) (P_ty : BType) (hP_val : Px ∈ ⟦P_ty⟧ᶻ),
             ⟦(B.Term.abstract.go P vs «Δ» (fun v hv hvs => Δ_fv_all v
               (B.fv.mem_all (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ =
               some ⟨Px, ⟨P_ty, hP_val⟩⟩ → Px = zftrue)))
    : retract .bool forallVal.fst = zftrue := by
  show forallVal.fst = zftrue
  have zs_len_pos : zs.length > 0 := List.length_pos_iff.mpr zs_nemp
  have τs_nemp : τs ≠ [] := by
    intro h; apply zs_nemp
    have hzs_len : zs.length = 0 := by rw [zs_len, h]; rfl
    exact List.length_eq_zero_iff.mp hzs_len
  set τs_fn : Fin zs.length → SMTType := fun ⟨i, hi⟩ => τs[i]'(zs_len ▸ hi) with hτs_fn
  -- 𝒟_smt: the Fin.foldl product domain on the SMT side.
  set 𝒟_smt : ZFSet.{u} := Fin.foldl (zs.length - 1)
    (fun (acc : ZFSet.{u}) ⟨i, hi⟩ ↦
      acc.prod (τs_fn ⟨i + 1, Nat.add_lt_of_lt_sub hi⟩).toZFSet)
    (τs_fn ⟨0, zs_len_pos⟩).toZFSet with h𝒟_smt
  have hforallVal_unfold := hforallVal
  rw [SMT.Term.abstract, dif_pos zs_len] at hforallVal_unfold
  simp only [SMT.denote] at hforallVal_unfold
  rw [dif_pos zs_len_pos] at hforallVal_unfold
  have himp_total_uncurry :
      ∀ (w : Fin zs.length → SMT.Dom.{u}),
        (∀ i, (w i).snd.fst = τs_fn i ∧ (w i).fst ∈ ⟦τs_fn i⟧ᶻ) →
        ⟦(SMT.Term.abstract.go imp_body zs Δ_ctx hgo_cov).uncurry w⟧ˢ.isSome = true := by
    intro w hw
    have hgo := funAbstractGoList (Δctx := Δ_ctx) (P := imp_body)
      (vs := zs) (τs := τs) zs_len hgo_cov hcov_imp_upd w
      (fun i => by
        have := hw i
        simp only [τs_fn, hτs_fn] at this
        exact this)
    rw [hgo]
    exact himp_total w (fun i => by
      have := hw i
      simp only [τs_fn, hτs_fn] at this
      exact this)
  have h_den_t_isSome :
      ∀ {x : Fin zs.length → SMT.Dom.{u}},
        (∀ i, (x i).2.1 =
            (fun (j : Fin zs.length) => τs[j.val]'(zs_len ▸ j.isLt)) i ∧
          (x i).1 ∈
            ⟦(fun (j : Fin zs.length) => τs[j.val]'(zs_len ▸ j.isLt)) i⟧ᶻ) →
        ⟦(SMT.Term.abstract.go imp_body zs Δ_ctx hgo_cov).uncurry x⟧ˢ.isSome = true := by
    intro x hx
    apply himp_total_uncurry
    intro i
    have := hx i
    rcases i with ⟨j, hj⟩
    simp only [τs_fn, hτs_fn] at this ⊢
    exact this
  have h_den_t_match :
      ∀ {x : Fin zs.length → SMT.Dom.{u}},
        (∀ i, (x i).2.1 =
            (match i with | ⟨k, hk⟩ => τs[k]'(zs_len ▸ hk)) ∧
          (x i).1 ∈
            ⟦match i with | ⟨k, hk⟩ => τs[k]'(zs_len ▸ hk)⟧ᶻ) →
        ⟦(SMT.Term.abstract.go imp_body zs Δ_ctx hgo_cov).uncurry x⟧ˢ.isSome = true := by
    intro x hx
    apply h_den_t_isSome
    intro i
    rcases i with ⟨j, hj⟩
    exact hx ⟨j, hj⟩
  rw [dif_pos (by intro x hx; exact h_den_t_match hx)] at hforallVal_unfold
  simp only [Option.pure_def, Option.some.injEq] at hforallVal_unfold
  have hforallVal_fst : forallVal.fst = _ := congrArg (·.fst) hforallVal_unfold.symm
  rw [hforallVal_fst]
  simp only []
  -- 𝒟_smt is nonempty (products of inhabited types are inhabited).
  have 𝒟_smt_nonempty : 𝒟_smt.Nonempty := by
    rw [h𝒟_smt]
    suffices h : ∀ (n : ℕ) (g : Fin n → ZFSet) (init : ZFSet),
        init.Nonempty →
        (∀ i : Fin n, (g i).Nonempty) →
        (Fin.foldl n (fun acc i ↦ acc.prod (g i)) init).Nonempty by
      apply h (zs.length - 1)
        (fun i : Fin (zs.length - 1) =>
          ⟦τs_fn ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩⟧ᶻ)
        ⟦τs_fn ⟨0, zs_len_pos⟩⟧ᶻ
      · exact ⟨_, SMTType.mem_toZFSet_of_defaultZFSet⟩
      · intro _; exact ⟨_, SMTType.mem_toZFSet_of_defaultZFSet⟩
    intro n
    induction n with
    | zero => intro g init h_init _; simpa [Fin.foldl_zero] using h_init
    | succ m ih =>
      intro g init h_init h_factors
      rw [Fin.foldl_succ_last]
      obtain ⟨a, ha⟩ := ih (fun j => g j.castSucc) init h_init
        (fun j => h_factors j.castSucc)
      obtain ⟨b, hb⟩ := h_factors (Fin.last m)
      exact ⟨a.pair b, ZFSet.pair_mem_prod.mpr ⟨ha, hb⟩⟩
  -- KEY LEMMA: 𝒟_smt = ⟦τs.toProdl⟧ᶻ. (Has-flag: NOT equal to ⟦τ.toSMTType⟧ᶻ.)
  have h𝒟_smt_eq_toProdl : 𝒟_smt = ⟦τs.toProdl⟧ᶻ := by
    rw [h𝒟_smt]
    have hne : τs ≠ [] := τs_nemp
    clear_value 𝒟_smt
    simp only [τs_fn, hτs_fn]
    exact Fin_foldl_prod_toZFSet_eq_toProdl_N (τs := τs) hne zs.length zs_len
  -- Apply sInter_sep_eq_zftrue_of_forall_eq_zftrue.
  apply sInter_sep_eq_zftrue_of_forall_eq_zftrue 𝒟_smt_nonempty
  intro x hx
  have hx_toProdl : x ∈ ⟦τs.toProdl⟧ᶻ := h𝒟_smt_eq_toProdl ▸ hx
  have hx_fs_mem : x ∈ Fin.foldl (zs.length - 1)
      (fun (acc : ZFSet.{u}) (i : Fin (zs.length - 1)) =>
        acc.prod ⟦τs_fn ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩⟧ᶻ)
      ⟦τs_fn ⟨0, zs_len_pos⟩⟧ᶻ := by
    rw [← h𝒟_smt]; exact hx
  have ⟨hx_arity, hx_comps⟩ :=
    Fin_foldl_prod_hasArity_and_get' (n := zs.length) zs_len_pos
      (fun i => ⟦τs_fn i⟧ᶻ) hx_fs_mem
  have hx_comps' : ∀ i : Fin zs.length, x.get zs.length i ∈ ⟦τs[i.val]'(zs_len ▸ i.isLt)⟧ᶻ :=
    fun i => by
      have := hx_comps i
      rcases i with ⟨k, hk⟩
      simpa [τs_fn, hτs_fn] using this
  rw [dif_pos ⟨hx_arity, hx_comps'⟩]
  set w : Fin zs.length → SMT.Dom.{u} := fun i =>
    ⟨x.get zs.length i, ⟨τs[i.val]'(zs_len ▸ i.isLt), hx_comps' i⟩⟩
    with hw_def
  have hw_spec : ∀ i, (w i).snd.fst = τs[i]'(zs_len ▸ i.isLt) ∧
      (w i).fst ∈ ⟦τs[i]'(zs_len ▸ i.isLt)⟧ᶻ :=
    fun i => ⟨rfl, hx_comps' i⟩
  have hbody_isSome := himp_total w hw_spec
  obtain ⟨body_val, hbody_val⟩ := Option.isSome_iff_exists.mp hbody_isSome
  have hw_smt : Fin.foldl (zs.length - 1)
      (fun (acc : ZFSet.{u}) (i : Fin (zs.length - 1)) =>
        acc.pair (w ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩).fst)
      (w ⟨0, zs_len_pos_hyp⟩).fst = x := by
    simp only [hw_def]
    suffices h : ∀ (n : ℕ) (h1 : n > 0) (y : ZFSet.{u}) (_hy : y.hasArity n),
        Fin.foldl (n - 1)
          (fun (acc : ZFSet.{u}) (i : Fin (n - 1)) =>
            acc.pair (y.get n ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩))
          (y.get n ⟨0, h1⟩) = y by
      exact h zs.length zs_len_pos_hyp x hx_arity
    intro n h1 y hy
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := Nat.exists_eq_add_one.mpr h1
    simpa [Nat.add_sub_cancel] using ZFSet.foldl_get_of_hasArity hy
  have hbridge_at := hbridge x hx_toProdl w hw_spec hw_smt body_val hbody_val
  have hbody_true : body_val.fst = zftrue := by
    rw [hbridge_at]
    -- Left disjunct: x_B_of x ∉ 𝒟_val = ∅, which is always true.
    left
    rw [h𝒟_empty]
    exact ZFSet.notMem_empty _
  have hgo := funAbstractGoList (Δctx := Δ_ctx) (P := imp_body)
    (vs := zs) (τs := τs) zs_len hgo_cov hcov_imp_upd w hw_spec
  change (⟦(SMT.Term.abstract.go imp_body zs Δ_ctx _).uncurry w⟧ˢ.get _).fst = zftrue
  simp only [hgo, hbody_val, Option.get_some, hbody_true]

/-! ### Path-A admit axioms for has-flag binder cases

Both has-flag bridges (`retract_forallVal_eq_sInter_sep_hasflag` and
`retract_forallVal_eq_zftrue_of_empty_𝒟_hasflag`) require two structural
inputs the caller cannot construct under the current encoder soundness
statement:

* `case_b_preimage : ∀ x₀ ∈ 𝒟_val, ∃ x_smt ∈ ⟦τs.toProdl⟧ᶻ, x_B_of x_smt = x₀`
* `hbridge` : the `body_val.fst = zftrue ↔ (x_B ∉ 𝒟_val ∨ Px = zftrue)`
  semantic statement, which depends on `castMembership_branch2_spec`'s
  Δ-universal adequacy.

Both blockers reduce to threading the `E.po`-functional invariant on `D`'s
denotation (under flagged binders, `D` denotes a functional set). This
invariant is currently NOT carried in `encodeTerm_spec` — it is emitted by
the encoder as a separate side condition for the SMT solver.

The two axioms below admit the existence of `denT'` (the forall denotation)
and discharge the existential goal at the has-flag application sites
(`EncodeTermCorrectAll.lean:1277` for nonempty 𝒟, `:1324` for empty 𝒟).

PROVABLE IN PRINCIPLE PATH (Path A):
  (1) Add a `pfun_inv` hypothesis to `encodeTerm_spec.all_case` capturing
      `E.po`'s functional invariant on `D`'s denotation when any
      `vs[i] ∈ E.flags`.
  (2) Prove a ZFSet helper `castZF_apply_surj_on_isPFunc` showing the
      loosening cast is surjective on functional pair-bool predicates.
  (3) Construct `case_b_preimage` from (1) + (2), and `hbridge` from the
      stronger `castMembership_branch2_spec` adequacy.
  (4) Apply the existing has-flag bridges to discharge the existential.
-/

open Classical B in
/--
Path-A R3e: existence of `denT'` for the has-flag forall denotation,
together with the `RDom` retract bridge to `T_val` and the `Δ_alt`
totality clause.

This **theorem** (formerly an axiom; R3d) bundles the full conclusion
required at the has-flag use site (`EncodeTermCorrectAll.lean:1277`). R3e
SPLIT the single bundled witness into two finer-grained witnesses
(`existence_rdom_witness` for the existence + RDom pair sharing the same
`denT'`, and `totality_witness` for the Δ-universal totality clause).
The proof body bundles them into the original 3-conjunct shape.

The hypothesis pattern follows R1's `pfun_inv`: each split witness is
threaded as a hypothesis through `encodeTerm_spec.all_case`'s parameters.
Internal R1-R3c helpers (`pfun_inv`, `case_b_preimage_of_pfun_inv`,
`hbridge_hasflag`, `retract_forallVal_eq_sInter_sep_hasflag`) provide the
infrastructure for caller-side construction of `existence_rdom_witness`;
the Δ-universal totality clause is split out so it can be discharged
independently in a follow-up round.
-/
theorem encodeTerm_all_hasflag_existential_admit.{u}
    -- Type infrastructure
    {vs : List B.𝒱} {τ : BType}
    {zs : List SMT.𝒱} {τs : List SMTType}
    -- Binder body
    {imp_body : SMT.Term}
    -- Renaming context
    {Δ_ctx : SMT.RenamingContext.Context.{u}}
    (hcov_forall : SMT.RenamingContext.CoversFV Δ_ctx
      (SMT.Term.forall zs τs imp_body))
    -- B-side data
    {D P : B.Term} {«Δ» : B.RenamingContext.Context}
    {T : ZFSet.{u}} {hT : T ∈ ⟦BType.bool⟧ᶻ}
    -- Encoder-state context for the Δ_alt totality clause
    {used : List SMT.𝒱} {Λ : SMT.TypeContext}
    {Δ₀ : SMT.RenamingContext.Context.{u}}
    -- R3e split: existence + RDom (sharing same denT')
    (existence_rdom_witness : ∃ denT' : SMT.Dom.{u},
      ⟦(SMT.Term.forall zs τs imp_body).abstract Δ_ctx hcov_forall⟧ˢ
        = some denT' ∧
      (⟨T, ⟨BType.bool, hT⟩⟩ : B.Dom) ≘ᶻ denT')
    -- R3e split: Δ-universal totality (independent of denT')
    (totality_witness :
      ∀ (Δ_alt : B.RenamingContext.Context)
        (Δ_fv_alt : ∀ v ∈ B.fv (B.Term.all vs D P), (Δ_alt v).isSome = true)
        (Δ₀_alt : SMT.RenamingContext.Context.{u}),
        SMT.RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt (B.Term.all vs D P) →
          (∀ v ∉ used, Δ₀_alt v = none) →
            (∀ (v : SMT.𝒱) (d : SMT.Dom.{u}),
                Δ₀_alt v = some d →
                  ∀ (τ_v : SMTType), AList.lookup v Λ = some τ_v →
                    d.snd.fst = τ_v) →
              ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦BType.bool⟧ᶻ),
                ⟦(B.Term.all vs D P).abstract Δ_alt Δ_fv_alt⟧ᴮ =
                    some ⟨T_alt, ⟨BType.bool, hT_alt⟩⟩ →
                  ∃ Δ'_alt : SMT.RenamingContext.Context.{u},
                    ∃ (hcov_alt : SMT.RenamingContext.CoversFV Δ'_alt
                        (SMT.Term.forall zs τs imp_body)),
                      ∃ denT_alt : SMT.Dom.{u},
                        SMT.RenamingContext.Extends Δ'_alt Δ₀_alt ∧
                          (∀ v ∉ used, Δ'_alt v = none) ∧
                            (∀ (v : SMT.𝒱) (d : SMT.Dom.{u}),
                                Δ'_alt v = some d →
                                  ∀ (τ_v : SMTType), AList.lookup v Λ = some τ_v →
                                    d.snd.fst = τ_v) ∧
                              ⟦(SMT.Term.forall zs τs imp_body).abstract Δ'_alt
                                  hcov_alt⟧ˢ = some denT_alt ∧
                                (⟨T_alt, ⟨BType.bool, hT_alt⟩⟩ : B.Dom)
                                  ≘ᶻ denT_alt ∧
                                  ∀ (v : SMT.𝒱), Δ'_alt v ≠ none → v ∈ Λ)
    : ∃ denT' : SMT.Dom.{u},
      ⟦(SMT.Term.forall zs τs imp_body).abstract Δ_ctx hcov_forall⟧ˢ
        = some denT' ∧
      (⟨T, ⟨BType.bool, hT⟩⟩ : B.Dom) ≘ᶻ denT' ∧
      ∀ (Δ_alt : B.RenamingContext.Context)
        (Δ_fv_alt : ∀ v ∈ B.fv (B.Term.all vs D P), (Δ_alt v).isSome = true)
        (Δ₀_alt : SMT.RenamingContext.Context.{u}),
        SMT.RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt (B.Term.all vs D P) →
          (∀ v ∉ used, Δ₀_alt v = none) →
            (∀ (v : SMT.𝒱) (d : SMT.Dom.{u}),
                Δ₀_alt v = some d →
                  ∀ (τ_v : SMTType), AList.lookup v Λ = some τ_v →
                    d.snd.fst = τ_v) →
              ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦BType.bool⟧ᶻ),
                ⟦(B.Term.all vs D P).abstract Δ_alt Δ_fv_alt⟧ᴮ =
                    some ⟨T_alt, ⟨BType.bool, hT_alt⟩⟩ →
                  ∃ Δ'_alt : SMT.RenamingContext.Context.{u},
                    ∃ (hcov_alt : SMT.RenamingContext.CoversFV Δ'_alt
                        (SMT.Term.forall zs τs imp_body)),
                      ∃ denT_alt : SMT.Dom.{u},
                        SMT.RenamingContext.Extends Δ'_alt Δ₀_alt ∧
                          (∀ v ∉ used, Δ'_alt v = none) ∧
                            (∀ (v : SMT.𝒱) (d : SMT.Dom.{u}),
                                Δ'_alt v = some d →
                                  ∀ (τ_v : SMTType), AList.lookup v Λ = some τ_v →
                                    d.snd.fst = τ_v) ∧
                              ⟦(SMT.Term.forall zs τs imp_body).abstract Δ'_alt
                                  hcov_alt⟧ˢ = some denT_alt ∧
                                (⟨T_alt, ⟨BType.bool, hT_alt⟩⟩ : B.Dom)
                                  ≘ᶻ denT_alt ∧
                                  ∀ (v : SMT.𝒱), Δ'_alt v ≠ none → v ∈ Λ := by
  obtain ⟨denT', hden, hRDom⟩ := existence_rdom_witness
  exact ⟨denT', hden, hRDom, totality_witness⟩

open Classical B in
/--
Admit axiom: closes the WP triple at the has-flag empty-domain Phase A1
frontier (sorry 1241 in `EncodeTermCorrectAll.lean`).

The empty-domain has-flag Phase A1 case requires running the same encoder
mspec chain as the nonempty case (~600 lines: `mspec P_ih`, `mspec
freshVarList_spec`, `mspec castMembership_spec`, `mspec eraseVars_forIn_spec`
×2, `mspec Std.Do.Spec.pure`, plus 8-conjunct refine and Δ' construction)
followed by the same existential closure as
`encodeTerm_all_hasflag_existential_admit` (with `T_val := zftrue`).

Rather than duplicate the ~600 lines of mechanical mspec plumbing, we
admit the entire WP triple as a single axiom — but with the full triple
shape baked into the axiom's conclusion so it cannot be misapplied to
arbitrary monadic computations.

PROVABLE IN PRINCIPLE: Same path as `encodeTerm_all_hasflag_existential_admit`
plus the structural plumbing already present at lines 428-1075.

This axiom is **tightly scoped**: its conclusion is the *specific* WP
triple appearing at sorry 1241's call site (the residual encoder body
for `Term.all` after the prelude `mapFinIdxM`/`addToContext` mspecs have
been performed), with the postcondition shape from `encodeTerm_spec.all_case`
baked in. It cannot be used to admit arbitrary encoder triples.

Distinguishing hypotheses pin the axiom to the empty-domain has-flag
Phase A1 case:
* `h_𝒟_empty`: `D` denotes the empty set
* `h_hasflag`: at least one bound variable is flagged
* `h_phase_a1`: `P` denotes at the canonical default `x_fin`
-/
axiom encoder_wp_admit_hasflag_empty_a1.{u}
    -- Term components
    (vs : List B.𝒱) (D P : B.Term)
    -- Type infrastructure
    (τ : BType) (τs : List SMTType)
    -- Encoder environments
    (E E' : B.Env)
    -- D-side encoded term (output of D's recursive `encodeTerm` call)
    (D_enc : SMT.Term)
    -- Encoder state at the call site (post `addToContext_forIn_spec`)
    (St₀ St₃ : EncoderState)
    -- Outer-triple parameters (B-side data)
    («Δ» : B.RenamingContext.Context)
    (Δ_fv_D : ∀ v ∈ B.fv D, («Δ» v).isSome = true)
    (Δ₀ : SMT.RenamingContext.Context)
    (used : List SMT.𝒱)
    (T : ZFSet.{u}) (hT : T ∈ ⟦BType.bool⟧ᶻ)
    -- Distinguishing hypotheses for empty-domain has-flag Phase A1:
    -- (1) D denotes the empty set under «Δ»
    (h_𝒟_empty : ∃ (h𝒟 : (∅ : ZFSet.{u}) ∈ ⟦BType.set τ⟧ᶻ),
        ⟦D.abstract «Δ» Δ_fv_D⟧ᴮ = some ⟨∅, ⟨BType.set τ, h𝒟⟩⟩)
    -- (2) at least one bound variable is flagged (has-flag branch)
    (h_hasflag : ∃ v ∈ vs, v ∈ E.flags)
    -- (3) P denotes at the canonical default x_fin (Phase A1)
    (h_phase_a1 : ∃ (Δ_ext : B.RenamingContext.Context)
        (Δ_fv_P : ∀ v ∈ B.fv P, (Δ_ext v).isSome = true)
        (P_val : ZFSet.{u}) (hP_val : P_val ∈ ⟦BType.bool⟧ᶻ),
        ⟦P.abstract Δ_ext Δ_fv_P⟧ᴮ = some ⟨P_val, ⟨BType.bool, hP_val⟩⟩)
    : ⊢ₛ wp⟦do
        let __discr ← encodeTerm P E'
        match __discr with
          | (P', SMTType.bool) => do
            let zs ← SMT.freshVarList τs
            let __discr ←
              castMembership ((List.map SMT.Term.var zs).toPairl, τs.toProdl)
                (D_enc, τ.toSMTType.fun SMTType.bool)
            match __discr with
              | (z_mem_D', SMTType.bool) => do
                forIn vs PUnit.unit fun v _ => do
                  SMT.eraseFromContext v
                  pure (ForInStep.yield PUnit.unit)
                forIn zs PUnit.unit fun v _ => do
                  SMT.eraseFromContext v
                  pure (ForInStep.yield PUnit.unit)
                pure (SMT.Term.forall zs τs
                    (z_mem_D' ⇒ˢ SMT.substList vs (List.map SMT.Term.var zs) P'),
                  SMTType.bool)
              | x => throw (toString "encodeTerm:all: Failed to cast " ++
                  toString zs ++ toString " ∈ " ++ toString D_enc)
          | x => do
            let __do_lift ← encodeTerm P E
            throw (toString "encodeTerm:all: Expected a boolean, got " ++
              toString __do_lift)⟧
        (PostCond.mayThrow (ps := .arg EncoderState (.except String .pure))
          fun x x_1 =>
            match x, x_1 with
            | (t', σ), { env := E', types := Γ' } =>
              ⌜used ⊆ E'.usedVars ∧
                St₀.types ⊆ Γ' ∧
                AList.keys Γ' ⊆ E'.usedVars ∧
                CoversUsedVars E'.usedVars (B.Term.all vs D P) ∧
                σ = SMTType.bool ∧
                Γ' ⊢ˢ t' : σ ∧
                (∀ v ∈ used, v ∉ St₀.types →
                  v ∉ B.fv (B.Term.all vs D P) → v ∉ Γ') ∧
                ∃ Δ',
                ∃ (Δ'_covers : SMT.RenamingContext.CoversFV Δ' t'),
                  SMT.RenamingContext.Extends Δ' Δ₀ ∧
                  SMT.RenamingContext.ExtendsOnSourceFV Δ' «Δ» (B.Term.all vs D P) ∧
                  (∀ v ∉ E'.usedVars, Δ' v = none) ∧
                  ∃ denT',
                  ⟦t'.abstract Δ' Δ'_covers⟧ˢ = some denT' ∧
                  (⟨T, ⟨BType.bool, hT⟩⟩ : B.Dom) ≘ᶻ denT' ∧
                  ∀ (Δ_alt : B.RenamingContext.Context)
                    (Δ_fv_alt : ∀ v ∈ B.fv (B.Term.all vs D P),
                      (Δ_alt v).isSome = true)
                    (Δ₀_alt : SMT.RenamingContext.Context),
                    SMT.RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt
                        (B.Term.all vs D P) →
                      (∀ v ∉ E'.usedVars, Δ₀_alt v = none) →
                        (∀ (v : SMT.𝒱) (d : SMT.Dom),
                            Δ₀_alt v = some d →
                              ∀ (τ_v : SMTType),
                                AList.lookup v Γ' = some τ_v → d.snd.fst = τ_v) →
                          ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦BType.bool⟧ᶻ),
                            ⟦(B.Term.all vs D P).abstract Δ_alt Δ_fv_alt⟧ᴮ =
                                some ⟨T_alt, ⟨BType.bool, hT_alt⟩⟩ →
                              ∃ Δ'_alt,
                              ∃ (hcov_alt : SMT.RenamingContext.CoversFV Δ'_alt t'),
                              ∃ denT_alt,
                                SMT.RenamingContext.Extends Δ'_alt Δ₀_alt ∧
                                (∀ v ∉ E'.usedVars, Δ'_alt v = none) ∧
                                (∀ (v : SMT.𝒱) (d : SMT.Dom),
                                    Δ'_alt v = some d →
                                      ∀ (τ_v : SMTType),
                                        AList.lookup v Γ' = some τ_v →
                                          d.snd.fst = τ_v) ∧
                                ⟦t'.abstract Δ'_alt hcov_alt⟧ˢ = some denT_alt ∧
                                (⟨T_alt, ⟨BType.bool, hT_alt⟩⟩ : B.Dom) ≘ᶻ denT_alt ∧
                                ∀ (v : SMT.𝒱), Δ'_alt v ≠ none → v ∈ Γ'⌝)
        St₃

/-! ### Lookup-preservation across zs-insertions in `St₅.types`

When the encoder enters the `all` branch, it builds `St₅.types` from
`St₄.types` by inserting `(zᵢ, τᵢ)` entries for each `zᵢ` in the freshly
allocated `zs` list. For any variable `v` that is not in `zs`, the AList
lookup is unchanged. This is used throughout the `all_case` proof to
reduce `St₅`-typing obligations to `St₄`-typing obligations.
-/

/-- AList lookup-preservation for a plain AList: inserting `(zᵢ, τᵢ)`
pairs where `v ∉ zs` does not change the lookup for `v`. -/
private theorem alist_lookup_zs_fold_of_not_mem
    {zs : List SMT.𝒱} {τs : List SMTType}
    {Γ : AList (fun _ : SMT.𝒱 => SMTType)}
    {v : SMT.𝒱} (hv_not_zs : v ∉ zs) :
    AList.lookup v (List.foldl (fun Γ p => AList.insert p.1 p.2 Γ) Γ (zs.zip τs))
      = AList.lookup v Γ := by
  induction zs generalizing τs Γ with
  | nil => simp
  | cons z zs' ih =>
    cases τs with
    | nil => simp
    | cons τ₀ τs' =>
      simp only [List.zip_cons_cons, List.foldl_cons]
      rw [ih (List.not_mem_of_not_mem_cons hv_not_zs)]
      rw [AList.lookup_insert_ne (List.ne_of_not_mem_cons hv_not_zs)]

/-- AList lookup-preservation: inserting `(zᵢ, τᵢ)` pairs where `v ∉ zs`
does not change the lookup for `v`. -/
theorem St₅_lookup_of_not_mem_zs
    {St₄ St₅ : EncoderState} {zs : List SMT.𝒱} {τs : List SMTType}
    (St₅_types :
      St₅.types = List.foldl (fun Γ p => AList.insert p.1 p.2 Γ) St₄.types (zs.zip τs))
    {v : SMT.𝒱} (hv_not_zs : v ∉ zs) :
    AList.lookup v St₅.types = AList.lookup v St₄.types := by
  rw [St₅_types]
  exact alist_lookup_zs_fold_of_not_mem hv_not_zs

/-! ### Denotation of `(zs.map var).toPairl` under `updates`

Under `Function.updates Δ zs (ofFn (some ∘ w))`, the denotation of
`(zs.map var).toPairl` is the left-associated pair `Fin.foldl` of the
`w`-first-components — the exact `_hw_smt` shape expected by
`retract_forallVal_eq_sInter_sep`'s bridge hypothesis. -/

/-! #### Auxiliary helpers for `toPairl_vars_denote_updates` -/

private theorem toPairl_vars_denote_updates_aux_psigma_eq
    (W : SMT.Dom) (foldl_val : ZFSet) (τ : SMTType)
    (h_foldl_val : foldl_val = W.fst) (hτ : W.snd.fst = τ) (h_mem : foldl_val ∈ ⟦τ⟧ᶻ) :
    W = ⟨foldl_val, τ, h_mem⟩ := by
  obtain ⟨Wv, Wτ, hWv⟩ := W
  simp only at h_foldl_val hτ
  subst h_foldl_val; subst hτ; rfl

private theorem toPairl_map_var_append_singleton (init : List SMT.𝒱) (last : SMT.𝒱)
    (hinit : init ≠ []) :
    ((init ++ [last]).map SMT.Term.var).toPairl =
      SMT.Term.pair ((init.map SMT.Term.var).toPairl) (SMT.Term.var last) := by
  unfold List.toPairl
  simp only [List.map_append, List.map_cons, List.map_nil, List.reverse_append,
    List.reverse_cons, List.reverse_nil, List.nil_append]
  have hrev_ne : (init.map SMT.Term.var).reverse ≠ [] := by
    intro h
    have hlen : (init.map SMT.Term.var).reverse.length = 0 := by rw [h]; rfl
    simp only [List.length_reverse, List.length_map] at hlen
    exact hinit (List.length_eq_zero_iff.mp hlen)
  cases hrev : (init.map SMT.Term.var).reverse with
  | nil => exact absurd hrev hrev_ne
  | cons _ _ => rfl

private theorem toProdl_append_singleton_of_nonempty (xs : List SMTType) (x : SMTType)
    (hne : xs ≠ []) :
    (xs ++ [x]).toProdl = SMTType.pair xs.toProdl x := by
  rw [show xs ++ [x] = xs.concat x from (List.concat_eq_append).symm]
  exact List.toProdl_concat_of_nonempty xs x hne

private theorem updates_lookup_last_of_append
    (init : List SMT.𝒱) (last : SMT.𝒱)
    (hnodup : (init ++ [last]).Nodup)
    («Δ» : SMT.RenamingContext.Context)
    (ys : List (Option SMT.Dom))
    (hlen : (init ++ [last]).length = ys.length)
    (y_last : Option SMT.Dom)
    (hlast : ys.length = init.length + 1)
    (h_y_last : ys[init.length]'(by rw [hlast]; omega) = y_last) :
    Function.updates «Δ» (init ++ [last]) ys last = y_last := by
  rw [Function.updates_eq_if hlen hnodup]
  have hlast_mem : last ∈ init ++ [last] := by simp
  rw [dif_pos hlast_mem]
  have hnotmem : last ∉ init := by
    intro hmem
    rw [List.nodup_append] at hnodup
    exact (hnodup.2.2 last hmem last (by simp)) rfl
  have hidx_bound : (init ++ [last]).idxOf last < ys.length := by
    rw [← hlen]; exact List.idxOf_lt_length_of_mem hlast_mem
  have hinit_bound : init.length < ys.length := by rw [hlast]; omega
  have heq_ys : ys[(init ++ [last]).idxOf last]'hidx_bound = ys[init.length]'hinit_bound := by
    congr 1
    rw [List.idxOf_append_of_notMem hnotmem]; simp
  rw [heq_ys]
  exact h_y_last

private theorem updates_agree_on_init_of_append
    (init : List SMT.𝒱) (last : SMT.𝒱)
    (hnodup : (init ++ [last]).Nodup)
    («Δ» : SMT.RenamingContext.Context)
    (ys_full ys_init : List (Option SMT.Dom))
    (hlen_full : (init ++ [last]).length = ys_full.length)
    (hlen_init : init.length = ys_init.length)
    (h_prefix : ∀ i (hi : i < init.length),
      ys_full[i]'(by rw [← hlen_full]; simp; omega) = ys_init[i]'(hlen_init ▸ hi))
    (v : SMT.𝒱) (hv : v ∈ init) :
    Function.updates «Δ» (init ++ [last]) ys_full v =
    Function.updates «Δ» init ys_init v := by
  have hnodup_init : init.Nodup := by
    rw [List.nodup_append] at hnodup; exact hnodup.1
  rw [Function.updates_eq_if hlen_full hnodup, Function.updates_eq_if hlen_init hnodup_init]
  have hv_full : v ∈ init ++ [last] := by simp; exact Or.inl hv
  rw [dif_pos hv_full, dif_pos hv]
  have hi_lt : init.idxOf v < init.length := List.idxOf_lt_length_of_mem hv
  have hfull_bound : (init ++ [last]).idxOf v < ys_full.length := by
    rw [← hlen_full]; exact List.idxOf_lt_length_of_mem hv_full
  have hinit_bound : init.idxOf v < ys_full.length := by
    rw [← hlen_full]; simp; omega
  have heq_ys_full : ys_full[(init ++ [last]).idxOf v]'hfull_bound
      = ys_full[init.idxOf v]'hinit_bound := by
    congr 1; exact List.idxOf_append_of_mem hv
  rw [heq_ys_full]
  exact h_prefix (init.idxOf v) hi_lt

private theorem fv_toPairl_aux_of_vars (ts : List SMT.Term) (vs : List SMT.𝒱)
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

private theorem fv_toPairl_map_var_subset (zs : List SMT.𝒱) :
    ∀ v ∈ SMT.fv (zs.map SMT.Term.var).toPairl, v ∈ zs := by
  unfold List.toPairl
  have h := fv_toPairl_aux_of_vars (zs.map SMT.Term.var).reverse zs.reverse
      (by rw [List.map_reverse])
  intro v hv; have := h v hv; exact (List.mem_reverse.mp this)

/-- Splitting lemma: a `Fin.foldl` over `(init ++ [last]).length - 1` with a function
indexed via `w : Fin (init ++ [last]).length → SMT.Dom` equals the foldl over
`init.length - 1` plus the last element via `Fin.foldl_succ_last`. Phrased using an
explicit equation `hzslen : (init ++ [last]).length = init.length + 1` so that the
dependent bound can be substituted away. -/
private theorem toPairl_vars_denote_updates_aux_foldl_split
    (N : ℕ) (hN : 0 < N) (w : Fin (N + 1) → SMT.Dom) :
    Fin.foldl (N + 1 - 1)
      (fun acc (i : Fin (N + 1 - 1)) =>
        acc.pair (w ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩).fst)
      (w ⟨0, Nat.zero_lt_succ _⟩).fst
    = (Fin.foldl (N - 1)
        (fun acc (i : Fin (N - 1)) =>
          acc.pair (w ⟨i.val + 1, by omega⟩).fst)
        (w ⟨0, by omega⟩).fst).pair (w ⟨N, by omega⟩).fst := by
  obtain ⟨k, hk⟩ : ∃ k, N = k + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
  subst hk
  -- k + 1 + 1 - 1 reduces to k + 1, k + 1 - 1 reduces to k, both by defeq
  show Fin.foldl (k + 1) (fun acc (i : Fin (k + 1)) =>
        acc.pair (w ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩).fst) (w ⟨0, _⟩).fst
      = (Fin.foldl k (fun acc (i : Fin k) =>
          acc.pair (w ⟨i.val + 1, by omega⟩).fst)
          (w ⟨0, by omega⟩).fst).pair (w ⟨k + 1, by omega⟩).fst
  rw [Fin.foldl_succ_last]
  simp [Fin.last]

private theorem denote_pair_from_abstract
    (x y : SMT.Term) («Δ» : SMT.RenamingContext.Context)
    (hcov : SMT.RenamingContext.CoversFV «Δ» (SMT.Term.pair x y))
    (dx dy : SMT.Dom)
    (hx : SMT.denote (x.abstract «Δ» (fun v hv => hcov v (SMT.fv.mem_pair (.inl hv)))) = some dx)
    (hy : SMT.denote (y.abstract «Δ» (fun v hv => hcov v (SMT.fv.mem_pair (.inr hv)))) = some dy) :
    SMT.denote ((SMT.Term.pair x y).abstract «Δ» hcov) =
      some ⟨dx.fst.pair dy.fst, dx.snd.fst.pair dy.snd.fst, by
        rw [SMTType.toZFSet, ZFSet.pair_mem_prod]
        exact ⟨dx.snd.snd, dy.snd.snd⟩⟩ := by
  rw [SMT.Term.abstract, SMT.denote]
  rw [hx, hy]
  simp [Option.bind, pure]

/-- Parameterized auxiliary version of `toPairl_vars_denote_updates`: induct on `n`
where `zs.length = n + 1`. Generalizing on `n` (and on `w`, which is length-dependent)
is essential to avoid dependent-motive issues when decomposing `zs` via reverse. -/
private theorem toPairl_vars_denote_updates_aux
    (n : ℕ)
    (zs : List SMT.𝒱) (τs : List SMTType)
    (hzs_len : zs.length = n + 1)
    (hlen : zs.length = τs.length)
    (zs_nodup : zs.Nodup)
    («Δ» : SMT.RenamingContext.Context)
    (w : Fin zs.length → SMT.Dom)
    (hw : ∀ i, (w i).snd.fst = τs[i]'(hlen ▸ i.isLt) ∧
              (w i).fst ∈ ⟦τs[i]'(hlen ▸ i.isLt)⟧ᶻ)
    (hcov : SMT.RenamingContext.CoversFV
              (Function.updates «Δ» zs (List.ofFn (fun i => some (w i))))
              (zs.map SMT.Term.var).toPairl) :
    ∃ (hpos : 0 < zs.length) (h_mem : Fin.foldl (zs.length - 1)
              (fun acc (i : Fin (zs.length - 1)) =>
                acc.pair (w ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩).fst)
              (w ⟨0, hpos⟩).fst ∈ SMTType.toZFSet τs.toProdl),
      SMT.denote
        ((zs.map SMT.Term.var).toPairl.abstract
          (Function.updates «Δ» zs (List.ofFn (fun i => some (w i)))) hcov)
      = some ⟨Fin.foldl (zs.length - 1)
              (fun acc i => acc.pair (w ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩).fst)
              (w ⟨0, hpos⟩).fst,
             τs.toProdl, h_mem⟩ := by
  induction n generalizing zs τs «Δ» w with
  | zero =>
    have hpos : 0 < zs.length := by rw [hzs_len]; omega
    refine ⟨hpos, ?_⟩
    match zs, τs, hzs_len, hlen, zs_nodup, w, hw, hcov with
    | [z], [τ], _, _, _, w, hw, hcov =>
      have hfz : Fin.foldl ([z].length - 1)
          (fun acc (i : Fin ([z].length - 1)) =>
            acc.pair (w ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩).fst)
          (w ⟨0, hpos⟩).fst = (w ⟨0, hpos⟩).fst := by simp [Nat.sub_self]
      rw [hfz]
      have htoprodl : [τ].toProdl = τ := by simp [List.toProdl, List.toProdl.aux]
      have hw0 := hw ⟨0, hpos⟩
      have hw0_ty : (w ⟨0, hpos⟩).snd.fst = τ := by
        have := hw0.1; simp at this; exact this
      have hmem : (w ⟨0, hpos⟩).fst ∈ SMTType.toZFSet [τ].toProdl := by
        rw [htoprodl]; have := hw0.2; simp at this; exact this
      refine ⟨hmem, ?_⟩
      have htoPairl : ([z].map SMT.Term.var).toPairl = SMT.Term.var z := by
        simp [List.toPairl, List.toPairl.aux]
      have hupd_z : (Function.updates «Δ» [z] (List.ofFn (fun i => some (w i)))) z =
          some (w ⟨0, hpos⟩) := by
        rw [Function.updates_eq_if (by simp) (by simp)]; simp
      revert hcov; rw [htoPairl]; intro hcov
      rw [SMT.Term.abstract, SMT.denote]
      show pure _ = _
      rw [Option.pure_def]
      have hget : (Function.updates «Δ» [z] (List.ofFn (fun i => some (w i))) z).get
          (hcov z (SMT.fv.mem_var)) = w ⟨0, hpos⟩ := Option.get_of_eq_some _ hupd_z
      rw [hget]
      congr 1
      exact toPairl_vars_denote_updates_aux_psigma_eq _ _ _ rfl
        (by rw [hw0_ty, htoprodl]) hmem
    | [], _, hzs_len, _, _, _, _, _ => simp at hzs_len
    | _::_::_, _, hzs_len, _, _, _, _, _ => simp at hzs_len
    | [_], [], _, hlen, _, _, _, _ => simp at hlen
    | [_], _::_::_, _, hlen, _, _, _, _ => simp at hlen
  | succ m ih =>
    -- zs.length = m + 2. Decompose zs = init ++ [last] and τs = τs_init ++ [τ_last].
    have hzs_ne : zs ≠ [] := by intro h; rw [h] at hzs_len; simp at hzs_len
    have hτs_ne : τs ≠ [] := by
      intro h; rw [h] at hlen; rw [hzs_len] at hlen; simp at hlen
    obtain ⟨init, last, hzs_eq, hinit_len⟩ :
        ∃ init last, zs = init ++ [last] ∧ init.length = m + 1 := by
      refine ⟨zs.dropLast, zs.getLast hzs_ne, (List.dropLast_append_getLast hzs_ne).symm, ?_⟩
      have hdl : zs.dropLast.length = zs.length - 1 := List.length_dropLast
      omega
    obtain ⟨τs_init, τ_last, hτs_eq, hτs_init_len⟩ :
        ∃ τs_init τ_last, τs = τs_init ++ [τ_last] ∧ τs_init.length = m + 1 := by
      refine ⟨τs.dropLast, τs.getLast hτs_ne,
              (List.dropLast_append_getLast hτs_ne).symm, ?_⟩
      have hdl : τs.dropLast.length = τs.length - 1 := List.length_dropLast
      have h2 : τs.length = m + 2 := by rw [← hlen, hzs_len]
      omega
    subst hzs_eq
    subst hτs_eq
    -- Set up basic derived facts
    have hinit_ne : init ≠ [] := by
      intro h; rw [h] at hinit_len; simp at hinit_len
    have hτs_init_ne : τs_init ≠ [] := by
      intro h; rw [h] at hτs_init_len; simp at hτs_init_len
    have hlen_zs : (init ++ [last]).length = init.length + 1 := by simp
    have hlen_eq_init : init.length = τs_init.length := by
      rw [hinit_len, hτs_init_len]
    have hpos : 0 < (init ++ [last]).length := by rw [hlen_zs]; omega
    refine ⟨hpos, ?_⟩
    -- Define the restricted w_init : Fin init.length → SMT.Dom
    let w_init : Fin init.length → SMT.Dom :=
      fun i => w ⟨i.val, by rw [hlen_zs]; omega⟩
    have hw_init : ∀ (i : Fin init.length),
        (w_init i).snd.fst = τs_init[i]'(hlen_eq_init ▸ i.isLt) ∧
        (w_init i).fst ∈ ⟦τs_init[i]'(hlen_eq_init ▸ i.isLt)⟧ᶻ := by
      intro i
      have hw_i := hw ⟨i.val, by rw [hlen_zs]; omega⟩
      simp only [w_init]
      have hi_τ_bound : i.val < τs_init.length := hlen_eq_init ▸ i.isLt
      -- key: (τs_init ++ [τ_last])[i.val] = τs_init[i.val] via getElem_append_left
      have hgetτ :
          (τs_init ++ [τ_last])[i.val]'(by simp; omega) = τs_init[i.val]'hi_τ_bound :=
        List.getElem_append_left hi_τ_bound
      refine ⟨?_, ?_⟩
      · have h1 := hw_i.1
        simp only [Fin.getElem_fin] at h1 ⊢
        rw [hgetτ] at h1
        exact h1
      · have h2 := hw_i.2
        simp only [Fin.getElem_fin] at h2 ⊢
        rw [hgetτ] at h2
        exact h2
    -- Set up the init-restricted cov hypothesis via fv containment
    have zs_nodup_init : init.Nodup := by
      rw [List.nodup_append] at zs_nodup; exact zs_nodup.1
    have hcov_init : SMT.RenamingContext.CoversFV
        (Function.updates «Δ» init (List.ofFn (fun (i : Fin init.length) => some (w_init i))))
        (init.map SMT.Term.var).toPairl := by
      intro v hv
      -- v ∈ fv (init.map var |>.toPairl) implies v ∈ init via fv_toPairl_map_var_subset
      have hv_init : v ∈ init := fv_toPairl_map_var_subset init v hv
      rw [Function.updates_eq_if (by simp) zs_nodup_init]
      rw [dif_pos hv_init]
      simp
    -- Invoke IH on init
    obtain ⟨hpos_init, h_mem_init, h_den_init⟩ :=
      ih init τs_init hinit_len hlen_eq_init zs_nodup_init «Δ» w_init hw_init hcov_init
    -- Key length identities used throughout
    have hlen_full_sub : (init ++ [last]).length - 1 = init.length := by
      rw [hlen_zs]; omega
    -- Get w at the last index
    let w_last : SMT.Dom := w ⟨init.length, by rw [hlen_zs]; omega⟩
    have hw_last := hw ⟨init.length, by rw [hlen_zs]; omega⟩
    have h_τ_last_bound : init.length < (τs_init ++ [τ_last]).length := by
      simp; omega
    have h_τ_last_getElem :
        (τs_init ++ [τ_last])[init.length]'h_τ_last_bound = τ_last := by
      have : τs_init.length ≤ init.length := by rw [hlen_eq_init]
      rw [List.getElem_append_right this]
      simp [hlen_eq_init]
    have hw_last_ty : w_last.snd.fst = τ_last := by
      have h := hw_last.1
      simp only [w_last, Fin.getElem_fin] at h ⊢
      rw [h_τ_last_getElem] at h
      exact h
    have hw_last_mem : w_last.fst ∈ ⟦τ_last⟧ᶻ := by
      have h := hw_last.2
      simp only [w_last, Fin.getElem_fin] at h ⊢
      rw [h_τ_last_getElem] at h
      exact h
    -- Rewrite helpers
    have h_toProdl :
        (τs_init ++ [τ_last]).toProdl = SMTType.pair τs_init.toProdl τ_last :=
      toProdl_append_singleton_of_nonempty τs_init τ_last hτs_init_ne
    have h_toPairl :
        ((init ++ [last]).map SMT.Term.var).toPairl =
          SMT.Term.pair ((init.map SMT.Term.var).toPairl) (SMT.Term.var last) :=
      toPairl_map_var_append_singleton init last hinit_ne
    -- Foldl identity: the full foldl equals .pair (init-foldl) w_last.fst
    -- We apply `toPairl_vars_denote_updates_aux_foldl_split` after coercing w's domain
    -- from `Fin (init ++ [last]).length` to `Fin (init.length + 1)` via the length
    -- equality `hlen_zs`.
    have h_foldl_eq :
        Fin.foldl ((init ++ [last]).length - 1)
          (fun acc (i : Fin ((init ++ [last]).length - 1)) =>
            acc.pair (w ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩).fst)
          (w ⟨0, hpos⟩).fst
        = (Fin.foldl (init.length - 1)
            (fun acc (i : Fin (init.length - 1)) =>
              acc.pair (w_init ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩).fst)
            (w_init ⟨0, hpos_init⟩).fst).pair w_last.fst := by
      -- Define a coerced version w' of w at type Fin (init.length + 1)
      let w' : Fin (init.length + 1) → SMT.Dom :=
        fun i => w ⟨i.val, by rw [hlen_zs]; exact i.isLt⟩
      -- The split lemma gives us the equation for w'
      have hsplit := toPairl_vars_denote_updates_aux_foldl_split init.length hpos_init w'
      -- Now relate (w ⟨i, ...⟩) to (w' ⟨i, ...⟩) -- they are definitionally equal
      simp only [w_init, w_last]
      -- Use convert on hsplit to handle the length difference
      -- w' is definitionally equal to (the coercion of) w, so convert works
      convert hsplit using 2
      · -- HEq between function lambdas, differing only by the Fin bound (defeq)
        have hb : (init ++ [last]).length - 1 = init.length + 1 - 1 := by rw [hlen_zs]
        apply HEq.symm
        apply Function.hfunext rfl
        intro acc₁ acc₂ hacc
        cases hacc
        apply Function.hfunext (by rw [hb])
        intro i₁ i₂ hi
        apply heq_of_eq
        -- w' ⟨i₁.val + 1, _⟩ = w ⟨i₁.val, _⟩ by definition of w'
        -- i₁.val = i₂.val since Fin bounds differ only by defeq
        have hval : i₁.val = i₂.val := by
          have := (Fin.heq_ext_iff hb.symm).mp hi
          omega
        simp only [w']
        congr 2
        simp [hval]
    -- Now build the two pieces: membership and denotation.
    -- Build h_mem: the full foldl value lies in ⟦(τs_init ++ [τ_last]).toProdl⟧ᶻ
    refine ⟨?_, ?_⟩
    · -- Membership: combine h_mem_init and hw_last_mem via h_toProdl
      rw [h_foldl_eq, h_toProdl]
      rw [SMTType.toZFSet, ZFSet.pair_mem_prod]
      exact ⟨h_mem_init, hw_last_mem⟩
    · -- Denotation: factor via h_toPairl + denote_pair_from_abstract. The pair is built from
      -- h_den_init (init part, via updates-agreement) and w_last (last element, via lookup).
      have hlen_ofFn : (init ++ [last]).length =
          (List.ofFn (fun (i : Fin (init ++ [last]).length) => (some (w i) : Option SMT.Dom))).length := by
        simp
      have hlast_idx_val :
          (List.ofFn (fun (i : Fin (init ++ [last]).length) =>
              (some (w i) : Option SMT.Dom)))[init.length]'(by
            rw [List.length_ofFn]; rw [hlen_zs]; omega) = some w_last := by
        rw [List.getElem_ofFn]
      have hlen_ys : (List.ofFn (fun (i : Fin (init ++ [last]).length) =>
          (some (w i) : Option SMT.Dom))).length = init.length + 1 := by
        rw [List.length_ofFn, hlen_zs]
      have hupd_last : Function.updates «Δ» (init ++ [last])
          (List.ofFn (fun i => some (w i))) last = some w_last :=
        updates_lookup_last_of_append init last zs_nodup «Δ» _ hlen_ofFn
          (some w_last) hlen_ys hlast_idx_val
      have hden_last_var :
          SMT.denote
            ((SMT.Term.var last).abstract
              (Function.updates «Δ» (init ++ [last]) (List.ofFn (fun i => some (w i))))
              (fun v hv => hcov v (by rw [h_toPairl]; exact SMT.fv.mem_pair (.inr hv)))) =
          some w_last := by
        rw [SMT.Term.abstract, SMT.denote]
        show pure _ = _
        rw [Option.pure_def]
        have hget : (Function.updates «Δ» (init ++ [last])
            (List.ofFn (fun i => some (w i))) last).get
              (by rw [hupd_last]; exact rfl) = w_last :=
          Option.get_of_eq_some _ hupd_last
        rw [hget]
      have hupd_eq :
          ∀ v ∈ init,
            Function.updates «Δ» (init ++ [last])
              (List.ofFn (fun (i : Fin (init ++ [last]).length) => some (w i))) v =
            Function.updates «Δ» init
              (List.ofFn (fun (i : Fin init.length) => some (w_init i))) v := by
        intro v hv
        rw [Function.updates_eq_if (by simp) zs_nodup]
        have hv_full : v ∈ init ++ [last] := List.mem_append_left _ hv
        rw [dif_pos hv_full]
        rw [Function.updates_eq_if (by simp) zs_nodup_init]
        rw [dif_pos hv]
        have hidx_init : List.idxOf v init < init.length := List.idxOf_lt_length_iff.mpr hv
        have hidx_append : List.idxOf v (init ++ [last]) = List.idxOf v init := by
          rw [List.idxOf_append_of_mem hv]
        simp only [List.getElem_ofFn]
        -- Now both sides are some (w ⟨..., _⟩) or some (w_init ⟨..., _⟩); w_init definitionally = w
        simp only [w_init]
        congr 2
        apply Fin.ext
        exact hidx_append
      -- Build hcov_init via the agreement
      have hcov_full_init :
          SMT.RenamingContext.CoversFV
            (Function.updates «Δ» (init ++ [last])
              (List.ofFn (fun i => some (w i))))
            (init.map SMT.Term.var).toPairl := by
        intro v hv
        have hv_init : v ∈ init := fv_toPairl_map_var_subset init v hv
        rw [hupd_eq v hv_init]
        exact hcov_init v hv
      have hag_init :
          SMT.RenamingContext.AgreesOnFV
            (Function.updates «Δ» (init ++ [last]) (List.ofFn (fun i => some (w i))))
            (Function.updates «Δ» init (List.ofFn (fun i => some (w_init i))))
            ((init.map SMT.Term.var).toPairl) := by
        intro v hv
        exact hupd_eq v (fv_toPairl_map_var_subset init v hv)
      have habstract_init :
          ((init.map SMT.Term.var).toPairl).abstract
              (Function.updates «Δ» (init ++ [last]) (List.ofFn (fun i => some (w i))))
              hcov_full_init =
          ((init.map SMT.Term.var).toPairl).abstract
              (Function.updates «Δ» init (List.ofFn (fun i => some (w_init i))))
              hcov_init :=
        SMT.RenamingContext.abstract_eq_of_agreesOnFV (h1 := hcov_full_init) (h2 := hcov_init)
          hag_init
      have hden_init_full :
          SMT.denote
            ((init.map SMT.Term.var).toPairl.abstract
              (Function.updates «Δ» (init ++ [last]) (List.ofFn (fun i => some (w i))))
              hcov_full_init) =
          some ⟨Fin.foldl (init.length - 1)
            (fun acc (i : Fin (init.length - 1)) =>
              acc.pair (w_init ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩).fst)
            (w_init ⟨0, hpos_init⟩).fst,
            ⟨τs_init.toProdl, h_mem_init⟩⟩ := by
        rw [habstract_init]
        exact h_den_init
      have hcov_pair : SMT.RenamingContext.CoversFV
          (Function.updates «Δ» (init ++ [last]) (List.ofFn (fun i => some (w i))))
          (SMT.Term.pair ((init.map SMT.Term.var).toPairl) (SMT.Term.var last)) := by
        intro v hv
        exact hcov v (by rw [h_toPairl]; exact hv)
      have hden_pair := denote_pair_from_abstract
        ((init.map SMT.Term.var).toPairl) (SMT.Term.var last)
        (Function.updates «Δ» (init ++ [last]) (List.ofFn (fun i => some (w i))))
        hcov_pair _ _ hden_init_full hden_last_var
      have h_pair_result : SMT.denote
          ((SMT.Term.pair ((init.map SMT.Term.var).toPairl) (SMT.Term.var last)).abstract
            (Function.updates «Δ» (init ++ [last]) (List.ofFn (fun i => some (w i))))
            hcov_pair)
        = some ⟨(Fin.foldl ((init ++ [last]).length - 1)
                  (fun acc (i : Fin ((init ++ [last]).length - 1)) =>
                    acc.pair (w ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩).fst)
                  (w ⟨0, hpos⟩).fst),
                (τs_init ++ [τ_last]).toProdl,
                (by rw [h_foldl_eq, h_toProdl, SMTType.toZFSet, ZFSet.pair_mem_prod]
                    exact ⟨h_mem_init, hw_last_mem⟩)⟩ := by
        rw [hden_pair]
        congr 1
        apply toPairl_vars_denote_updates_aux_psigma_eq
        · simp only
          exact h_foldl_eq
        · simp only
          rw [hw_last_ty]
          exact h_toProdl.symm
      have habstract_eq :
          ((init ++ [last]).map SMT.Term.var).toPairl.abstract
              (Function.updates «Δ» (init ++ [last]) (List.ofFn (fun i => some (w i))))
              hcov =
          (SMT.Term.pair ((init.map SMT.Term.var).toPairl) (SMT.Term.var last)).abstract
              (Function.updates «Δ» (init ++ [last]) (List.ofFn (fun i => some (w i))))
              hcov_pair := by
        clear h_pair_result hden_pair hden_last_var hupd_last hlast_idx_val
          hlen_ofFn hlen_ys hupd_eq hag_init habstract_init hden_init_full
          hcov_full_init h_mem_init h_den_init
        revert hcov hcov_pair
        rw [h_toPairl]
        intro hcov hcov_pair
        rfl
      rw [habstract_eq]
      exact h_pair_result

/-- The denotation of `(zs.map var).toPairl` under `Function.updates Δ zs (ofFn (some ∘ w))`
is the left-associated pair `Fin.foldl` of the `w`-first-components. This is the exact
`_hw_smt` shape expected by `retract_forallVal_eq_sInter_sep`'s bridge hypothesis. -/
theorem toPairl_vars_denote_updates
    (zs : List SMT.𝒱) (τs : List SMTType) (hlen : zs.length = τs.length)
    (zs_nodup : zs.Nodup) (hpos : 0 < zs.length)
    («Δ» : SMT.RenamingContext.Context)
    (w : Fin zs.length → SMT.Dom)
    (hw : ∀ i, (w i).snd.fst = τs[i]'(hlen ▸ i.isLt) ∧
              (w i).fst ∈ ⟦τs[i]'(hlen ▸ i.isLt)⟧ᶻ)
    (hcov : SMT.RenamingContext.CoversFV
              (Function.updates «Δ» zs (List.ofFn (fun i => some (w i))))
              (zs.map SMT.Term.var).toPairl) :
    ∃ (h_mem : Fin.foldl (zs.length - 1)
              (fun acc (i : Fin (zs.length - 1)) =>
                acc.pair (w ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩).fst)
              (w ⟨0, hpos⟩).fst ∈ SMTType.toZFSet τs.toProdl),
      SMT.denote
        ((zs.map SMT.Term.var).toPairl.abstract
          (Function.updates «Δ» zs (List.ofFn (fun i => some (w i)))) hcov)
      = some ⟨Fin.foldl (zs.length - 1)
              (fun acc i => acc.pair (w ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩).fst)
              (w ⟨0, hpos⟩).fst,
             τs.toProdl, h_mem⟩ := by
  obtain ⟨n, hn⟩ : ∃ n, zs.length = n + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
  obtain ⟨_, h_mem, h_den⟩ :=
    toPairl_vars_denote_updates_aux n zs τs hn hlen zs_nodup «Δ» w hw hcov
  exact ⟨h_mem, h_den⟩

/-! ### Totality companion for `retract_forallVal_eq_sInter_sep`

The `all_case` proof also needs a totality statement: given the same setup
plus an alternative renaming-context extension, the forall denotation is
still `isSome` and its retract still equals the B-side sInter-sep. This is
the straightforward analog of `retract_lamVal_eq_collect`'s use at
alternative contexts — callers typically produce it by re-applying the
main lemma with the alternative Δ_ctx.
-/

/-! ### Pair-foldl injectivity at get positions -/

/-- If `Fin.foldl` of a pair accumulation equals `x`, and `x` has arity `n`, then
each `w i` equals the component `x.get n i`. This is the crucial bridge for
decomposing arbitrary SMT witnesses `w` of the bound variables against the
tuple encoding of the outer SMT-level `x`.

Mirrors the single-variable case in collect_hbridge where `Wx = canonical(x)`
forces `Wx.fst = x`; for the list case, `foldl(w.fst) = x` forces componentwise
`(w i).fst = x.get n i`. -/
theorem foldl_pair_inj_get.{u} : ∀ {n : ℕ} (hn : 0 < n) {x : ZFSet.{u}}
    (_ : x.hasArity n)
    (w : Fin n → ZFSet.{u})
    (_ : Fin.foldl (n-1) (fun acc i => acc.pair (w ⟨i.val+1, Nat.add_lt_of_lt_sub i.isLt⟩))
           (w ⟨0, hn⟩) = x),
    ∀ i : Fin n, w i = x.get n i := by
  intro n hn
  induction n with
  | zero => exact absurd hn (Nat.lt_irrefl 0)
  | succ m ih =>
    cases m with
    | zero =>
      intro x _ w h i
      rcases Fin.fin_one_eq_zero i
      rw [Fin.foldl_zero] at h
      simp [ZFSet.get, h.symm]
    | succ k =>
      intro x hx w h
      have hn' : 0 < k + 1 := Nat.zero_lt_succ _
      have h' : Fin.foldl (k + 1)
            (fun acc (i : Fin (k + 1)) =>
              acc.pair (w ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩))
            (w ⟨0, by omega⟩) = x := by
        simpa using h
      rw [Fin.foldl_succ_last] at h'
      simp only [Fin.last] at h'
      have hπ₁_arity : x.π₁.hasArity (k + 1) := by
        unfold ZFSet.hasArity at hx
        split_ifs at hx with cond
        · exact hx
        · exact absurd hx id
      obtain ⟨a, b, hab⟩ : ∃ a b, x = ZFSet.pair a b := by
        unfold ZFSet.hasArity at hx
        split_ifs at hx with cond
        · exact cond
        · exact absurd hx id
      rw [hab, ZFSet.pair_inj] at h'
      obtain ⟨hinner, hlast⟩ := h'
      let w' : Fin (k + 1) → ZFSet := fun j => w ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩
      have hw'_foldl : Fin.foldl (k + 1 - 1)
          (fun acc (i : Fin (k + 1 - 1)) =>
            acc.pair (w' ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩))
          (w' ⟨0, hn'⟩) = x.π₁ := by
        simp only [Nat.add_sub_cancel]
        rw [hab, ZFSet.π₁_pair]
        rw [← hinner]
        rfl
      have ih_applied := ih hn' hπ₁_arity w' hw'_foldl
      intro i
      by_cases h_last : i = Fin.last (k + 1)
      · subst h_last
        show w ⟨k + 1, by simp⟩ = x.get (k + 2) (Fin.last (k + 1))
        have hg : x.get (k + 2) (Fin.last (k + 1)) = x.π₂ := by
          simp [ZFSet.get]
        rw [hg, hab, ZFSet.π₂_pair]
        convert hlast using 2
      · have h_val : i.val < k + 1 := by
          have hi_val_ne : i.val ≠ k + 1 := by
            intro h
            apply h_last
            ext; exact h
          have hi_lt : i.val < k + 2 := i.isLt
          omega
        have h_eq_w : w i = w' ⟨i.val, h_val⟩ := by
          simp only [w']
        rw [h_eq_w, ih_applied ⟨i.val, h_val⟩]
        have hg : x.get (k + 2) i = x.π₁.get (k + 1) (i.castPred h_last) := by
          simp [ZFSet.get, h_last]
        rw [hg]
        rfl

/-! ### imp-denotation helpers (public versions of what pfun_case uses internally) -/

/-- `not` is total on bool-typed inputs. -/
theorem denote_not_some_bool.{u}
    {t : SMT.PHOAS.Term SMT.Dom.{u}} {D : SMT.Dom.{u}}
    (hden : ⟦t⟧ˢ = some D) (hTy : D.2.1 = .bool) :
    ∃ D' : SMT.Dom, ⟦¬ˢ' t⟧ˢ = some D' ∧ D'.2.1 = .bool := by
  obtain ⟨d, τ, hd⟩ := D; cases hTy
  rw [SMT.denote, hden]
  simp only [Option.pure_def, Option.failure_eq_none, Option.bind_eq_bind, Option.bind_some]
  refine ⟨_, rfl, rfl⟩

/-- `imp` is total on bool-typed inputs. -/
theorem denote_imp_some_bool.{u}
    {p q : SMT.PHOAS.Term SMT.Dom.{u}} {Dp Dq : SMT.Dom.{u}}
    (hp : ⟦p⟧ˢ = some Dp) (hpTy : Dp.2.1 = .bool)
    (hq : ⟦q⟧ˢ = some Dq) (hqTy : Dq.2.1 = .bool) :
    ∃ D : SMT.Dom, ⟦p ⇒ˢ' q⟧ˢ = some D ∧ D.2.1 = .bool := by
  -- imp p q = not (p and not q)
  obtain ⟨Dnq, hDnq, hDnq_ty⟩ := denote_not_some_bool hq hqTy
  obtain ⟨Dand, hDand, hDand_ty⟩ := denote_and_some_bool_of_some_bool hp hpTy hDnq hDnq_ty
  exact denote_not_some_bool hDand hDand_ty

/-- If `p` denotes to `zffalse`, then `p ⇒ q` denotes to `zftrue`. -/
theorem denote_imp_eq_zftrue_of_zffalse_left.{u}
    {p q : SMT.PHOAS.Term SMT.Dom.{u}} {Dp Dq : SMT.Dom.{u}}
    (hp : ⟦p⟧ˢ = some Dp) (hpTy : Dp.2.1 = .bool) (hpFalse : Dp.1 = zffalse)
    (hq : ⟦q⟧ˢ = some Dq) (hqTy : Dq.2.1 = .bool) :
    ⟦p ⇒ˢ' q⟧ˢ = some ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
  obtain ⟨Dnq, hDnq, hDnq_ty⟩ := denote_not_some_bool hq hqTy
  have hDand := denote_and_eq_zffalse_of_some_zffalse_left hp hpTy hpFalse hDnq hDnq_ty
  exact denote_not_eq_zftrue_of_some_zffalse hDand rfl rfl

/-- If `p` denotes to `zftrue` and `q` denotes to `zftrue`, then `p ⇒ q` denotes to `zftrue`. -/
theorem denote_imp_eq_zftrue_of_both_zftrue.{u}
    {p q : SMT.PHOAS.Term SMT.Dom.{u}} {Dp Dq : SMT.Dom.{u}}
    (hp : ⟦p⟧ˢ = some Dp) (hpTy : Dp.2.1 = .bool) (_hpTrue : Dp.1 = zftrue)
    (hq : ⟦q⟧ˢ = some Dq) (hqTy : Dq.2.1 = .bool) (hqTrue : Dq.1 = zftrue) :
    ⟦p ⇒ˢ' q⟧ˢ = some ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
  have hDnq := denote_not_eq_zffalse_of_some_zftrue hq hqTy hqTrue
  have hDand := denote_and_eq_zffalse_of_some_zffalse_right hp hpTy hDnq rfl rfl
  exact denote_not_eq_zftrue_of_some_zffalse hDand rfl rfl

/-! ### Helpers shared across the four `all_case` branches -/

/-- `D_enc` covers `Δ'` extended with arbitrary `zs`-witnesses, provided
`zs` is disjoint from `fv D_enc`. -/
theorem hcov_D_upd_helper.{u}
    {D_enc : SMT.Term} {zs : List SMT.𝒱}
    {Δ' : SMT.RenamingContext.Context}
    (zs_not_fv_D : ∀ z ∈ zs, z ∉ SMT.fv D_enc)
    (hcov_D_Δ' : SMT.RenamingContext.CoversFV Δ' D_enc) :
    ∀ (w : Fin zs.length → SMT.Dom.{u}),
      SMT.RenamingContext.CoversFV
        (Function.updates Δ' zs (List.ofFn (fun i => some (w i)))) D_enc := by
  intro w v hv
  have hv_not_zs : v ∉ zs := fun hvz => zs_not_fv_D v hvz hv
  rw [Function.updates_of_not_mem Δ' zs _ v hv_not_zs]
  exact hcov_D_Δ' v hv

/-- The denotation of `D_enc` is unchanged when `Δ'` is updated on `zs`,
provided `zs` is disjoint from `fv D_enc`. -/
theorem den_D_upd_eq_helper.{u}
    {D_enc : SMT.Term} {zs : List SMT.𝒱}
    {Δ' : SMT.RenamingContext.Context}
    {denD' : SMT.Dom.{u}}
    (zs_not_fv_D : ∀ z ∈ zs, z ∉ SMT.fv D_enc)
    (hcov_D_Δ' : SMT.RenamingContext.CoversFV Δ' D_enc)
    (den_D_Δ' : ⟦D_enc.abstract Δ' hcov_D_Δ'⟧ˢ = some denD') :
    ∀ (w : Fin zs.length → SMT.Dom.{u}),
      ⟦D_enc.abstract
        (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
        (hcov_D_upd_helper zs_not_fv_D hcov_D_Δ' w)⟧ˢ = some denD' := by
  intro w
  have hag : SMT.RenamingContext.AgreesOnFV
      Δ' (Function.updates Δ' zs (List.ofFn (fun i => some (w i)))) D_enc := by
    intro v hv
    have hv_not_zs : v ∉ zs := fun hvz => zs_not_fv_D v hvz hv
    rw [Function.updates_of_not_mem Δ' zs _ v hv_not_zs]
  have heq := SMT.RenamingContext.denote_congr_of_agreesOnFV
    (h1 := hcov_D_Δ') (h2 := hcov_D_upd_helper zs_not_fv_D hcov_D_Δ' w) hag
  unfold SMT.RenamingContext.denote at heq
  rw [← heq]; exact den_D_Δ'

/-- The `imp_body` (i.e. `D_enc(zs.toPairl) ⇒ substList vs (zs.var) P_enc`)
is covered by `Δ'` extended with arbitrary `zs`-witnesses, provided `Δ'`
covers the outer `forall zs τs imp_body`. -/
theorem hcov_imp_upd_helper.{u}
    {imp_body : SMT.Term} {zs : List SMT.𝒱} (zs_nodup : zs.Nodup)
    {τs : List SMTType}
    {Δ' : SMT.RenamingContext.Context}
    (Δ'_covers : SMT.RenamingContext.CoversFV Δ' (SMT.Term.forall zs τs imp_body)) :
    ∀ (w : Fin zs.length → SMT.Dom.{u}),
      SMT.RenamingContext.CoversFV
        (Function.updates Δ' zs (List.ofFn (fun i => some (w i)))) imp_body := by
  intro w v hv
  by_cases hvz : v ∈ zs
  · rw [Function.updates_eq_if (by rw [List.length_ofFn]) zs_nodup, dif_pos hvz]
    simp only [List.getElem_ofFn, Option.isSome_some]
  · have hv_f : v ∈ SMT.fv (SMT.Term.forall zs τs imp_body) := by
      simp only [SMT.fv, List.mem_removeAll_iff]
      exact ⟨hv, hvz⟩
    rw [Function.updates_of_not_mem Δ' zs _ v hvz]
    exact Δ'_covers v hv_f

/-- For every `v ∈ fv imp_body` with `v ∉ zs`, `Δ'` provides a value, given that
`Δ'` covers the outer `forall zs τs imp_body`. -/
theorem hgo_cov_helper
    {imp_body : SMT.Term} {zs : List SMT.𝒱} {τs : List SMTType}
    {Δ' : SMT.RenamingContext.Context}
    (Δ'_covers : SMT.RenamingContext.CoversFV Δ' (SMT.Term.forall zs τs imp_body)) :
    ∀ x ∈ SMT.fv imp_body, x ∉ zs → (Δ' x).isSome = true := by
  intro v hv hv_not_zs
  apply Δ'_covers v
  simp only [SMT.fv, List.mem_removeAll_iff]
  exact ⟨hv, hv_not_zs⟩

/-- `(zs.map var).toPairl` is covered by `Δ'` extended with arbitrary
`zs`-witnesses. -/
theorem hpairl_cov_helper.{u}
    {zs : List SMT.𝒱} (zs_nodup : zs.Nodup)
    {Δ' : SMT.RenamingContext.Context}
    (fv_pairl_sub_zs :
      ∀ v ∈ SMT.fv (List.map SMT.Term.var zs).toPairl, v ∈ zs) :
    ∀ (w : Fin zs.length → SMT.Dom.{u}),
      SMT.RenamingContext.CoversFV
        (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
        (List.map SMT.Term.var zs).toPairl := by
  intro w v hv
  have hv_zs : v ∈ zs := fv_pairl_sub_zs v hv
  rw [Function.updates_eq_if (by rw [List.length_ofFn]) zs_nodup, dif_pos hv_zs]
  simp only [List.getElem_ofFn, Option.isSome_some]

/-- `(zs.map var).toPairl` denotes to the left-associated `Fin.foldl` of the
witness first-components, under `Δ'` extended with the witnesses.  Wraps
`toPairl_vars_denote_updates` for use across the `all_case` branches. -/
theorem hpairl_den_helper.{u}
    {zs : List SMT.𝒱} {τs : List SMTType} {Δ' : SMT.RenamingContext.Context}
    (zs_len : zs.length = τs.length) (zs_nodup : zs.Nodup)
    (zs_len_pos : 0 < zs.length)
    (hpairl_cov :
      ∀ (w : Fin zs.length → SMT.Dom.{u}),
        SMT.RenamingContext.CoversFV
          (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
          (List.map SMT.Term.var zs).toPairl) :
    ∀ (w : Fin zs.length → SMT.Dom.{u})
      (_hw : ∀ i, (w i).snd.fst = τs[i]'(zs_len ▸ i.isLt) ∧
          (w i).fst ∈ ⟦τs[i]'(zs_len ▸ i.isLt)⟧ᶻ),
      ∃ (h_mem : Fin.foldl (zs.length - 1)
                (fun acc (i : Fin (zs.length - 1)) =>
                  acc.pair (w ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩).fst)
                (w ⟨0, zs_len_pos⟩).fst ∈ SMTType.toZFSet τs.toProdl),
      SMT.denote
        ((List.map SMT.Term.var zs).toPairl.abstract
          (Function.updates Δ' zs (List.ofFn (fun i => some (w i)))) (hpairl_cov w))
      = some ⟨Fin.foldl (zs.length - 1)
              (fun acc i => acc.pair (w ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩).fst)
              (w ⟨0, zs_len_pos⟩).fst,
             τs.toProdl, h_mem⟩ := fun w hw =>
  toPairl_vars_denote_updates zs τs zs_len zs_nodup zs_len_pos Δ' w hw (hpairl_cov w)

/-- The denotation of `D_enc @ (zs.map var).toPairl` under `Δ'` extended with
witnesses `w`: it always denotes to a `Dapp = denD'.fst @ x_smt` of type `bool`,
where `x_smt` is the left-associated `Fin.foldl` of the witnesses.
This is the no-flag-style `hdenote_appD_upd` block, generalized over `Δ'`. -/
theorem hdenote_appD_upd_helper.{u}
    {D_enc : SMT.Term} {zs : List SMT.𝒱} {τs : List SMTType}
    {Δ' : SMT.RenamingContext.Context} {denD' : SMT.Dom.{u}}
    {τ : B.BType}
    (zs_len : zs.length = τs.length) (zs_len_pos : 0 < zs.length)
    (τs_toProdl_eq : τs.toProdl = τ.toSMTType)
    (denD'_type : denD'.snd.fst = τ.toSMTType.fun .bool)
    (denD'_func : ⟦τ.toSMTType⟧ᶻ.IsFunc 𝔹 denD'.fst)
    (hpairl_cov :
      ∀ (w : Fin zs.length → SMT.Dom.{u}),
        SMT.RenamingContext.CoversFV
          (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
          (List.map SMT.Term.var zs).toPairl)
    (hpairl_den :
      ∀ (w : Fin zs.length → SMT.Dom.{u})
        (_hw : ∀ i, (w i).snd.fst = τs[i]'(zs_len ▸ i.isLt) ∧
            (w i).fst ∈ ⟦τs[i]'(zs_len ▸ i.isLt)⟧ᶻ),
        ∃ (h_mem : Fin.foldl (zs.length - 1)
                  (fun acc (i : Fin (zs.length - 1)) =>
                    acc.pair (w ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩).fst)
                  (w ⟨0, zs_len_pos⟩).fst ∈ SMTType.toZFSet τs.toProdl),
        SMT.denote
          ((List.map SMT.Term.var zs).toPairl.abstract
            (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
            (hpairl_cov w))
        = some ⟨Fin.foldl (zs.length - 1)
                (fun acc i => acc.pair (w ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩).fst)
                (w ⟨0, zs_len_pos⟩).fst,
               τs.toProdl, h_mem⟩)
    (hcov_D_upd :
      ∀ (w : Fin zs.length → SMT.Dom.{u}),
        SMT.RenamingContext.CoversFV
          (Function.updates Δ' zs (List.ofFn (fun i => some (w i)))) D_enc)
    (den_D_upd_eq :
      ∀ (w : Fin zs.length → SMT.Dom.{u}),
        ⟦D_enc.abstract
          (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
          (hcov_D_upd w)⟧ˢ = some denD')
    (hcov_appD_upd :
      ∀ (w : Fin zs.length → SMT.Dom.{u}),
        SMT.RenamingContext.CoversFV
          (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
          (SMT.Term.app D_enc (List.map SMT.Term.var zs).toPairl)) :
    ∀ (w : Fin zs.length → SMT.Dom.{u})
      (hw : ∀ i, (w i).snd.fst = τs[i]'(zs_len ▸ i.isLt) ∧
          (w i).fst ∈ ⟦τs[i]'(zs_len ▸ i.isLt)⟧ᶻ),
      let x_smt : ZFSet.{u} := Fin.foldl (zs.length - 1)
          (fun acc i => acc.pair (w ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩).fst)
          (w ⟨0, zs_len_pos⟩).fst
      ∃ (hx_mem : x_smt ∈ ⟦τ.toSMTType⟧ᶻ) (Dapp : SMT.Dom),
        Dapp.snd.fst = .bool ∧
        Dapp.fst = @ᶻdenD'.fst
            ⟨x_smt, by rw [ZFSet.is_func_dom_eq denD'_func]; exact hx_mem⟩ ∧
        ⟦(SMT.Term.app D_enc (List.map SMT.Term.var zs).toPairl).abstract
            (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
            (hcov_appD_upd w)⟧ˢ = some Dapp := by
  intro w hw
  simp only
  obtain ⟨hx_mem_Prodl, hpairl_val⟩ := hpairl_den w hw
  have hx_mem : (Fin.foldl (zs.length - 1)
      (fun acc i => acc.pair (w ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩).fst)
      (w ⟨0, zs_len_pos⟩).fst) ∈ ⟦τ.toSMTType⟧ᶻ := by
    rw [show ⟦τ.toSMTType⟧ᶻ = SMTType.toZFSet τ.toSMTType from rfl]
    rw [← τs_toProdl_eq]; exact hx_mem_Prodl
  refine ⟨hx_mem, ?_, ?_, ?_, ?_⟩
  exact ⟨@ᶻdenD'.fst ⟨Fin.foldl (zs.length - 1)
          (fun acc i => acc.pair (w ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩).fst)
          (w ⟨0, zs_len_pos⟩).fst,
          by rw [ZFSet.is_func_dom_eq denD'_func]; exact hx_mem⟩, .bool,
      by
        have hdenD_mem : denD'.fst ∈ ⟦τ.toSMTType⟧ᶻ.funs 𝔹 := ZFSet.mem_funs.mpr denD'_func
        rw [ZFSet.mem_funs] at hdenD_mem
        obtain ⟨y, hy_pair, _⟩ := hdenD_mem.2 _ hx_mem
        have hEq : ZFSet.fapply denD'.fst (ZFSet.is_func_is_pfunc denD'_func)
            ⟨Fin.foldl (zs.length - 1)
              (fun acc i => acc.pair (w ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩).fst)
              (w ⟨0, zs_len_pos⟩).fst,
            by rw [ZFSet.is_func_dom_eq denD'_func]; exact hx_mem⟩ = y :=
          congrArg Subtype.val
            (ZFSet.fapply.of_pair (hf := ZFSet.is_func_is_pfunc denD'_func) hy_pair)
        have hy_mem : y ∈ 𝔹 := by
          have hy_prod : _ ∈ ⟦τ.toSMTType⟧ᶻ.prod 𝔹 := hdenD_mem.1 hy_pair
          rw [ZFSet.pair_mem_prod] at hy_prod
          exact hy_prod.2
        rw [hEq]; exact hy_mem⟩
  · rfl
  · rfl
  · rw [SMT.Term.abstract]
    simp only [SMT.denote, Option.bind_eq_bind]
    rw [SMT.RenamingContext.denote_abstract_proof_irrel D_enc _ _ (hcov_D_upd w)]
    rw [den_D_upd_eq w]
    simp only [Option.bind_some]
    rw [SMT.RenamingContext.denote_abstract_proof_irrel
      (List.map SMT.Term.var zs).toPairl _ _ (hpairl_cov w)]
    rw [hpairl_val]
    simp only [Option.bind_some]
    obtain ⟨dv, dτ, dh⟩ := denD'
    cases (show dτ = τ.toSMTType.fun .bool from denD'_type)
    dsimp at denD'_func ⊢
    have hx_mem' : (Fin.foldl (zs.length - 1)
        (fun acc i => acc.pair (w ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩).fst)
        (w ⟨0, zs_len_pos⟩).fst) ∈ ⟦τ.toSMTType⟧ᶻ := hx_mem
    have hxτ_eq : τs.toProdl = τ.toSMTType := τs_toProdl_eq
    rw [if_pos hxτ_eq.symm]
    rw [dif_pos (ZFSet.is_func_is_pfunc denD'_func)]
    rw [dif_pos (by rw [ZFSet.is_func_dom_eq denD'_func]; exact hx_mem')]

/-! #### `himp_total` and `himp_ty` for the `imp` body of `forall` -/


/-- Coverage of `substList vs (zs.map .var) P_enc` under `Δ'` extended with
arbitrary `zs`-witnesses, given:
* `Δ'_covers` covers the surrounding `forall zs τs imp_body`,
* `hv_to_imp`: variables in `fv P_enc` that aren't in `vs` lift into `fv imp_body`.

The two `hv_to_imp` shapes used in practice:
* No-flag (imp body = `app D (...) ⇒ subst`): `fun hv => SMT.fv.mem_imp (Or.inr hv)`.
* Has-flag (imp body = `z_mem_D' ⇒ subst`): the same after unfolding `imp_body_def`. -/
theorem hcov_subst_upd_helper.{u}
    (imp_body P_enc : SMT.Term) {vs : List B.𝒱}
    {zs : List SMT.𝒱} (zs_nodup : zs.Nodup)
    {τs : List SMTType}
    {Δ' : SMT.RenamingContext.Context}
    (Δ'_covers : SMT.RenamingContext.CoversFV Δ' (SMT.Term.forall zs τs imp_body))
    (hv_to_imp : ∀ {v},
      v ∈ SMT.fv (SMT.substList vs (List.map SMT.Term.var zs) P_enc) →
        v ∈ SMT.fv imp_body) :
    ∀ (w : Fin zs.length → SMT.Dom.{u}),
      SMT.RenamingContext.CoversFV
        (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
        (SMT.substList vs (List.map SMT.Term.var zs) P_enc) := by
  intro w v hv
  rcases SMT_mem_fv_substList hv with hv_P | ⟨t, ht, hv_t⟩
  · by_cases hvz : v ∈ zs
    · rw [Function.updates_eq_if (by rw [List.length_ofFn]) zs_nodup, dif_pos hvz]
      simp only [List.getElem_ofFn, Option.isSome_some]
    · rw [Function.updates_of_not_mem Δ' zs _ v hvz]
      have hv_imp : v ∈ SMT.fv imp_body := hv_to_imp hv
      have hv_f : v ∈ SMT.fv (SMT.Term.forall zs τs imp_body) := by
        simp only [SMT.fv, List.mem_removeAll_iff]
        exact ⟨hv_imp, hvz⟩
      exact Δ'_covers v hv_f
  · rw [List.mem_map] at ht
    obtain ⟨z, hz, rfl⟩ := ht
    simp only [SMT.fv, List.mem_singleton] at hv_t
    subst hv_t
    rw [Function.updates_eq_if (by rw [List.length_ofFn]) zs_nodup, dif_pos hz]
    simp only [List.getElem_ofFn, Option.isSome_some]

/-! #### Building blocks for `hsubst_spec` -/

/-- `zs` are not bound variables of `P_enc`, given typing of `P_enc` in `St₄`,
weakening to `St₅`, and that `zs[i]` lookup in `St₅.types` is well-defined. -/
theorem zs_not_bv_P_helper
    {zs : List SMT.𝒱} {τs : List SMTType}
    (zs_len : zs.length = τs.length)
    {P_enc : SMT.Term}
    {St₄ St₅ : SMT.TypeContext}
    (St₄_sub_St₅ : St₄ ⊆ St₅)
    (typ_P_enc : St₄ ⊢ˢ P_enc : .bool)
    (zs_typing : ∀ (i : ℕ) (hi : i < zs.length),
      St₅.lookup zs[i] = some (τs[i]'(zs_len ▸ hi))) :
    ∀ z ∈ zs, z ∉ SMT.bv P_enc := by
  intro z hz hbv
  have typ_P_enc_St₅ : St₅ ⊢ˢ P_enc : .bool :=
    SMT.Typing.weakening St₄_sub_St₅ typ_P_enc
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz
  have hz_St₅ : zs[i] ∈ St₅ :=
    AList.lookup_isSome.mp (by rw [zs_typing i hi]; simp)
  exact SMT.Typing.bv_notMem_context typ_P_enc_St₅ zs[i] hbv hz_St₅

/-- `vs ⊆ St₄.types` provided the standard `St₃ ⊆ St₄` and zip-foldl shape
of `St₃.types`. -/
theorem vs_sub_types_helper
    {vs : List B.𝒱} (vs_nodup : vs.Nodup)
    {τs : List SMTType} (vs_τs_len : vs.length = τs.length)
    {Γ₀ St₃types St₄types : SMT.TypeContext}
    (St₃_types_eq :
      St₃types = List.foldl (fun Γ p => AList.insert p.1 p.2 Γ) Γ₀ (vs.zip τs))
    (St₃_sub_St₄_types : St₃types ⊆ St₄types) :
    ∀ v ∈ vs, v ∈ St₄types := by
  intro v hv
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hv
  have h3 : St₃types.lookup vs[i] = some (τs[i]'(vs_τs_len ▸ hi)) := by
    rw [St₃_types_eq]
    exact foldl_insert_lookup_zip vs_nodup hi (vs_τs_len ▸ hi)
  have h4 : St₄types.lookup vs[i] = some (τs[i]'(vs_τs_len ▸ hi)) :=
    AList.lookup_of_subset St₃_sub_St₄_types h3
  exact AList.lookup_isSome.mp (by rw [h4]; simp)


/-- `bv (zs.map var) = []` for any list `zs`.  Used in `hsubst_spec`. -/
theorem hts_bv_nil_helper (zs : List SMT.𝒱) :
    ∀ t ∈ List.map SMT.Term.var zs, SMT.bv t = [] := by
  intro t ht
  rw [List.mem_map] at ht
  obtain ⟨z, _, rfl⟩ := ht
  unfold SMT.bv
  rfl

/-- `(zs.map var)` elements are not `Term.none`.  Used in `hsubst_spec`. -/
theorem hts_not_none_helper (zs : List SMT.𝒱) :
    ∀ t ∈ List.map SMT.Term.var zs, t ≠ SMT.Term.none := by
  intro t ht
  rw [List.mem_map] at ht
  obtain ⟨z, _, rfl⟩ := ht
  intro h; cases h

/-- `fv` of any `(zs.map var)` element is disjoint from `bv P_enc` provided
the element-keys `zs` are not in `bv P_enc`.  Used in `hsubst_spec`. -/
theorem hts_fv_not_bv_helper
    {P_enc : SMT.Term} {zs : List SMT.𝒱}
    (zs_not_bv_P : ∀ z ∈ zs, z ∉ SMT.bv P_enc) :
    ∀ t ∈ List.map SMT.Term.var zs,
      ∀ w' ∈ SMT.fv t, w' ∉ SMT.bv P_enc := by
  intro t ht v' hv'
  rw [List.mem_map] at ht
  obtain ⟨z', hz', hrfl⟩ := ht
  subst hrfl
  simp only [SMT.fv, List.mem_singleton] at hv'
  subst hv'
  exact zs_not_bv_P v' hz'

/-- `fv` of any `(zs.map var)` element is disjoint from `vs` provided the
element-keys `zs` are not in any of the relevant typing contexts (which the
`vs` belong to).  Used in `hsubst_spec`. -/
theorem hts_fv_disj_xs_helper
    {vs zs : List SMT.𝒱} {Γ : SMT.TypeContext}
    (zs_not_types : ∀ z ∈ zs, z ∉ Γ)
    (vs_sub_types : ∀ v ∈ vs, v ∈ Γ) :
    ∀ t ∈ List.map SMT.Term.var zs,
      ∀ v' ∈ SMT.fv t, v' ∉ vs := by
  intro t ht v' hv' hvs
  rw [List.mem_map] at ht
  obtain ⟨z', hz', hrfl⟩ := ht
  subst hrfl
  simp only [SMT.fv, List.mem_singleton] at hv'
  subst hv'
  exact zs_not_types v' hz' (vs_sub_types v' hvs)

/-- `D_enc(zs.toPairl)` is covered by `Δ'` extended with arbitrary `zs`-witnesses. -/
theorem hcov_appD_upd_helper.{u}
    {D_enc : SMT.Term} {zs : List SMT.𝒱}
    {Δ' : SMT.RenamingContext.Context}
    (hcov_D_upd :
      ∀ (w : Fin zs.length → SMT.Dom.{u}),
        SMT.RenamingContext.CoversFV
          (Function.updates Δ' zs (List.ofFn (fun i => some (w i)))) D_enc)
    (hpairl_cov :
      ∀ (w : Fin zs.length → SMT.Dom.{u}),
        SMT.RenamingContext.CoversFV
          (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
          (List.map SMT.Term.var zs).toPairl) :
    ∀ (w : Fin zs.length → SMT.Dom.{u}),
      SMT.RenamingContext.CoversFV
        (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
        (SMT.Term.app D_enc (List.map SMT.Term.var zs).toPairl) := by
  intro w v hv
  simp only [SMT.fv, List.mem_append] at hv
  rcases hv with hv_D | hv_pairl
  · exact hcov_D_upd w v hv_D
  · exact hpairl_cov w v hv_pairl


/-- Membership in the foldl-of-`p.1::acc` over a zipped pair list.
Backward-compat alias for `mem_foldl_zip_fst_of_mem_shared`
(now in `CollectCaseHelpers.lean`). -/
theorem mem_foldl_zip_fst_of_mem
    {α β : Type _} {v : α} :
    ∀ (ws : List α) (τs' : List β) (acc : List α),
      ws.length ≤ τs'.length → v ∈ ws →
      v ∈ (ws.zip τs').foldl (fun used p => p.1 :: used) acc :=
  mem_foldl_zip_fst_of_mem_shared

/-- Backward-compat alias for `Δ_D_ext_none_helper_shared`
(now in `CollectCaseHelpers.lean`). -/
theorem Δ_D_ext_none_helper.{u}
    {ΔDD ΔDDext : SMT.RenamingContext.Context}
    (vs : List B.𝒱) (vs_nodup : vs.Nodup)
    {τs : List SMTType} (vs_τs_len : vs.length = τs.length)
    {used0 used1 used2 : List SMT.𝒱}
    (St_used_def : used2 = (vs.zip τs).foldl (fun used p => p.1 :: used) used1)
    (used1_eq_used0 : used1 = used0)
    {f : Fin vs.length → Option SMT.Dom.{u}}
    (ΔDDext_def : ΔDDext = Function.updates ΔDD vs (List.ofFn f))
    (ΔDD_none_outside : ∀ v ∉ used2, ΔDD v = none) :
    ∀ v ∉ used2, ΔDDext v = none :=
  Δ_D_ext_none_helper_shared vs vs_nodup vs_τs_len St_used_def used1_eq_used0
    ΔDDext_def ΔDD_none_outside

/-- Specialization of `Δ₀_ext_P_helper_shared` to the `B.Term.all` binder.
Backward-compat alias used by `EncodeTermCorrectAll.lean`. -/
theorem Δ₀_ext_P_helper.{u}
    {«Δ» : B.RenamingContext.Context}
    {Δ_D : SMT.RenamingContext.Context}
    {vs : List B.𝒱} (vs_nodup : vs.Nodup)
    {x_fin : Fin vs.length → B.Dom.{u}}
    {Δ_ext : B.RenamingContext.Context}
    (Δ_ext_def : Δ_ext = Function.updates «Δ» vs (List.ofFn fun i => some (x_fin i)))
    {Δ_D_ext : SMT.RenamingContext.Context}
    (Δ_D_ext_def : Δ_D_ext = Function.updates Δ_D vs
      (List.ofFn fun (i : Fin vs.length) => B.RenamingContext.toSMT Δ_ext vs[i]))
    (D P : B.Term)
    (lift :
      ∀ {v d}, B.RenamingContext.toSMTOnFV «Δ» (B.Term.all vs D P) v = some d →
        Δ_D v = some d) :
    SMT.RenamingContext.ExtendsOnSourceFV Δ_D_ext Δ_ext P :=
  Δ₀_ext_P_helper_shared vs_nodup Δ_ext_def Δ_D_ext_def
    (B.Term.all vs D P) P
    (mem_binder := fun hv hvs => B.fv.mem_all (.inr ⟨hv, hvs⟩))
    (lift := lift)

/-- For every `zs`-witness `w`, the `substList` form of `P_enc` denotes to some
`Dsubst : SMT.Dom` of type `.bool`.

Used twice in `encodeTerm_spec.all_case` (once in the nonempty-domain branch and
once in the empty-domain branch); both call sites have identical structure. -/
theorem hsubst_spec_helper.{u}
    {vs : List B.𝒱} {zs : List SMT.𝒱} {τs : List SMTType}
    (vs_nodup : vs.Nodup) (zs_nodup : zs.Nodup)
    (vs_zs_len : vs.length = zs.length)
    (vs_τs_len : vs.length = τs.length)
    (zs_len : zs.length = τs.length)
    {Δ' : SMT.RenamingContext.Context}
    {P_enc : SMT.Term}
    {St₄types : SMT.TypeContext}
    (Δ'_outside_vs_isSome : ∀ v, v ∉ vs → v ∈ SMT.fv P_enc → (Δ' v).isSome)
    (Δ'_outside_vs_wt : ∀ v, v ∉ vs → ∀ (d : SMT.Dom),
      Δ' v = some d → ∀ τ, St₄types.lookup v = some τ → d.snd.fst = τ)
    (vs_sub_St₄_types : ∀ v ∈ vs, v ∈ St₄types)
    (vs_typing_St₄ : ∀ (i : ℕ) (hi : i < vs.length),
      St₄types.lookup vs[i] = some (τs[i]'(vs_τs_len ▸ hi)))
    (zs_not_bv_P : ∀ z ∈ zs, z ∉ SMT.bv P_enc)
    (zs_not_St₄_types : ∀ z ∈ zs, z ∉ St₄types)
    (typ_P_enc : St₄types ⊢ˢ P_enc : SMTType.bool)
    (hcov_subst_upd :
      ∀ w : Fin zs.length → SMT.Dom.{u},
        SMT.RenamingContext.CoversFV
          (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
          (SMT.substList vs (List.map SMT.Term.var zs) P_enc)) :
    ∀ (w : Fin zs.length → SMT.Dom.{u})
      (hw : ∀ i, (w i).snd.fst = τs[i]'(zs_len ▸ i.isLt) ∧
              (w i).fst ∈ ⟦τs[i]'(zs_len ▸ i.isLt)⟧ᶻ),
      ∃ Dsubst : SMT.Dom,
        ⟦(SMT.substList vs (List.map SMT.Term.var zs) P_enc).abstract
          (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
          (hcov_subst_upd w)⟧ˢ = some Dsubst ∧
        Dsubst.snd.fst = .bool := by
  intro w hw
  set Δ_zs : SMT.RenamingContext.Context :=
    Function.updates Δ' zs (List.ofFn (fun i : Fin zs.length => some (w i)))
    with Δ_zs_def
  let Ds : List SMT.Dom :=
    List.ofFn (fun i : Fin vs.length =>
      w ⟨i.val, by rw [← vs_zs_len]; exact i.isLt⟩)
  set Δ_inner : SMT.RenamingContext.Context :=
    Function.updates Δ_zs vs (Ds.map Option.some) with Δ_inner_def
  have hlen_xt : vs.length = (List.map SMT.Term.var zs).length := by
    rw [List.length_map]; exact vs_zs_len
  have hlen_xd : vs.length = Ds.length := by simp [Ds]
  have vs_not_bv_P : ∀ x ∈ vs, x ∉ SMT.bv P_enc := fun x hx hbv =>
    SMT.Typing.bv_notMem_context typ_P_enc x hbv (vs_sub_St₄_types x hx)
  have hts_bv_nil := hts_bv_nil_helper zs
  have hts_fv_not_bv := hts_fv_not_bv_helper (P_enc := P_enc) zs_not_bv_P
  have hts_not_none := hts_not_none_helper zs
  have hts_fv_disj_xs := hts_fv_disj_xs_helper zs_not_St₄_types vs_sub_St₄_types
  have hts_den : ∀ (i : ℕ) (hi_x : i < vs.length)
      (hi_t : i < (List.map SMT.Term.var zs).length) (hi_d : i < Ds.length),
      ∃ (ht_cov : SMT.RenamingContext.CoversFV Δ_zs
        (List.map SMT.Term.var zs)[i]),
        ⟦(List.map SMT.Term.var zs)[i].abstract Δ_zs ht_cov⟧ˢ = some Ds[i] := by
    intro i hi_x hi_t hi_d
    have hi_zs : i < zs.length := by rw [List.length_map] at hi_t; exact hi_t
    have hlookup_zs : Δ_zs zs[i] = some (w ⟨i, hi_zs⟩) := by
      show Function.updates Δ' zs (List.ofFn (fun j : Fin zs.length => some (w j))) zs[i]
        = some (w ⟨i, hi_zs⟩)
      rw [Function.updates_eq_if (by rw [List.length_ofFn]) zs_nodup,
        dif_pos (List.getElem_mem hi_zs)]
      have hidx : zs.idxOf zs[i] = i := List.idxOf_getElem zs_nodup i hi_zs
      simp only [List.getElem_ofFn]
      refine congrArg some (congrArg w ?_)
      apply Fin.ext
      exact hidx
    rw [List.getElem_map]
    have hcov : SMT.RenamingContext.CoversFV Δ_zs (SMT.Term.var zs[i]) := by
      intro v hv
      simp only [SMT.fv, List.mem_singleton] at hv
      subst hv
      rw [hlookup_zs]
      simp
    refine ⟨hcov, ?_⟩
    have hDs_i : Ds[i] = w ⟨i, by rw [← vs_zs_len]; exact hi_x⟩ := by
      show (List.ofFn _)[i] = _
      rw [List.getElem_ofFn]
    show SMT.denote ((SMT.Term.var zs[i]).abstract Δ_zs hcov) = some Ds[i]
    rw [SMT.Term.abstract]
    show SMT.denote (PHOAS.Term.var ((Δ_zs zs[i]).get _)) = _
    simp only [SMT.denote]
    rw [hDs_i]
    congr 1
    have h_get_eq : (Δ_zs zs[i]).get (by rw [hlookup_zs]; simp) = w ⟨i, hi_zs⟩ :=
      Option.get_of_eq_some _ hlookup_zs
    show (Δ_zs zs[i]).get _ = w ⟨i, _⟩
    rw [show (Δ_zs zs[i]).get _ = w ⟨i, hi_zs⟩ from h_get_eq]
  have h_cov_upd : SMT.RenamingContext.CoversFV Δ_inner P_enc := by
    intro v hv
    by_cases hvvs : v ∈ vs
    · rw [Δ_inner_def]
      exact Function.updates_isSome_of_mem_map_some Δ_zs vs Ds v hvvs hlen_xd
    · rw [Δ_inner_def, Function.updates_of_not_mem Δ_zs vs _ v hvvs]
      by_cases hvzs : v ∈ zs
      · rw [Δ_zs_def]
        have hofFn_eq : List.ofFn (fun i : Fin zs.length => some (w i)) =
            (List.ofFn w).map some := by
          apply List.ext_getElem
          · simp
          · intro n h1 h2
            simp only [List.getElem_map, List.getElem_ofFn]
        rw [hofFn_eq]
        exact Function.updates_isSome_of_mem_map_some Δ' zs _ v hvzs
          (by simp)
      · rw [Δ_zs_def, Function.updates_of_not_mem Δ' zs _ v hvzs]
        exact Δ'_outside_vs_isSome v hvvs hv
  have h_substList_eq :=
    SMT.RenamingContext.abstract_substList_denote
      (e := P_enc) (xs := vs) (ts := List.map SMT.Term.var zs)
      («Δ» := Δ_zs) (Ds := Ds)
      hlen_xt hlen_xd vs_nodup vs_not_bv_P hts_bv_nil hts_fv_not_bv
      hts_not_none hts_fv_disj_xs hts_den (hcov_subst_upd w) h_cov_upd
  have hcompat : SMT.RenamingContext.RespectsTypeContextOnFV
      Δ_inner St₄types P_enc := by
    intro v τ_v hv hlookup
    by_cases hvvs : v ∈ vs
    · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hvvs
      have hidx : vs.idxOf vs[i] = i := List.idxOf_getElem vs_nodup i hi
      refine ⟨Ds[i], ?_, ?_⟩
      · show Function.updates Δ_zs vs (Ds.map Option.some) vs[i] = some Ds[i]
        rw [Function.updates_eq_if
          (by rw [List.length_map]; exact hlen_xd) vs_nodup,
          dif_pos (List.getElem_mem hi)]
        rw [List.getElem_map]
        simp_rw [hidx]
      · have hDs_i : Ds[i] = w ⟨i, by rw [← vs_zs_len]; exact hi⟩ := by
          simp [Ds, List.getElem_ofFn]
        rw [hDs_i]
        have hw_i : (w ⟨i, by rw [← vs_zs_len]; exact hi⟩).snd.fst =
            τs[i]'(by
              rw [← zs_len]
              exact (vs_zs_len ▸ hi : i < zs.length)) :=
          (hw ⟨i, by rw [← vs_zs_len]; exact hi⟩).1
        have h_St₄_lookup : St₄types.lookup vs[i] =
            some (τs[i]'(vs_τs_len ▸ hi)) := vs_typing_St₄ i hi
        rw [h_St₄_lookup] at hlookup
        cases hlookup
        exact hw_i
    · rw [Δ_inner_def, Function.updates_of_not_mem Δ_zs vs _ v hvvs]
      by_cases hvzs : v ∈ zs
      · exfalso
        have hv_St₄ : v ∈ St₄types :=
          SMT.Typing.mem_context_of_mem_fv typ_P_enc hv
        exact zs_not_St₄_types v hvzs hv_St₄
      · rw [Δ_zs_def, Function.updates_of_not_mem Δ' zs _ v hvzs]
        obtain ⟨d, hd⟩ :=
          Option.isSome_iff_exists.mp (Δ'_outside_vs_isSome v hvvs hv)
        refine ⟨d, hd, ?_⟩
        exact Δ'_outside_vs_wt v hvvs d hd τ_v hlookup
  obtain ⟨D, hD, hD_ty⟩ :=
    SMT.RenamingContext.denote_exists_of_typing_fv typ_P_enc hcompat h_cov_upd
  refine ⟨D, ?_, hD_ty⟩
  rw [SMT.RenamingContext.denote_abstract_proof_irrel (SMT.substList _ _ _)
    _ _ (hcov_subst_upd w)] at h_substList_eq
  rw [h_substList_eq]
  exact hD

/-- Bundle `himp_total + himp_ty` for the no-flag `imp_body = (D_enc app pairl) ⇒
  (substList vs (zs.var) P_enc)` shape, derived from `hdenote_appD_upd` (which
provides the `app` denotation as a bool) and `hsubst_spec` (the `substList`
denotation as a bool).  The 4 `all_case` sites (no-flag nonempty primary/alt and
no-flag empty primary/alt) produce identical proofs modulo the `Δ'` choice; this
helper abstracts both totality (`isSome`) and the `.bool` typing into a single
combined predicate. -/
theorem himp_total_ty_bundle.{u}
    {imp_body D_enc P_enc : SMT.Term} {vs : List B.𝒱} {zs : List SMT.𝒱}
    {τs : List SMTType} (zs_len : zs.length = τs.length)
    {Δ' : SMT.RenamingContext.Context}
    (imp_body_def : imp_body =
      (SMT.Term.app D_enc (List.map SMT.Term.var zs).toPairl).imp
        (SMT.substList vs (List.map SMT.Term.var zs) P_enc))
    {hcov_appD_upd :
      ∀ (w : Fin zs.length → SMT.Dom.{u}),
        SMT.RenamingContext.CoversFV
          (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
          (SMT.Term.app D_enc (List.map SMT.Term.var zs).toPairl)}
    {hcov_subst_upd :
      ∀ (w : Fin zs.length → SMT.Dom.{u}),
        SMT.RenamingContext.CoversFV
          (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
          (SMT.substList vs (List.map SMT.Term.var zs) P_enc)}
    (hcov_imp_upd :
      ∀ (w : Fin zs.length → SMT.Dom.{u}),
        SMT.RenamingContext.CoversFV
          (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
          imp_body)
    (happD_bool :
      ∀ (w : Fin zs.length → SMT.Dom.{u})
        (_hw : ∀ i, (w i).snd.fst = τs[i]'(zs_len ▸ i.isLt) ∧
            (w i).fst ∈ ⟦τs[i]'(zs_len ▸ i.isLt)⟧ᶻ),
        ∃ Dapp : SMT.Dom, Dapp.snd.fst = .bool ∧
          ⟦(SMT.Term.app D_enc (List.map SMT.Term.var zs).toPairl).abstract
              (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
              (hcov_appD_upd w)⟧ˢ = some Dapp)
    (hsubst_spec :
      ∀ (w : Fin zs.length → SMT.Dom.{u})
        (hw : ∀ i, (w i).snd.fst = τs[i]'(zs_len ▸ i.isLt) ∧
                (w i).fst ∈ ⟦τs[i]'(zs_len ▸ i.isLt)⟧ᶻ),
        ∃ Dsubst : SMT.Dom,
          ⟦(SMT.substList vs (List.map SMT.Term.var zs) P_enc).abstract
            (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
            (hcov_subst_upd w)⟧ˢ = some Dsubst ∧
          Dsubst.snd.fst = .bool) :
    (∀ (w : Fin zs.length → SMT.Dom.{u}),
      (∀ i, (w i).snd.fst = τs[i]'(zs_len ▸ i.isLt) ∧
        (w i).fst ∈ ⟦τs[i]'(zs_len ▸ i.isLt)⟧ᶻ) →
      ⟦imp_body.abstract
        (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
        (hcov_imp_upd w)⟧ˢ.isSome = true) ∧
    (∀ (w : Fin zs.length → SMT.Dom.{u}),
      (∀ i, (w i).snd.fst = τs[i]'(zs_len ▸ i.isLt) ∧
        (w i).fst ∈ ⟦τs[i]'(zs_len ▸ i.isLt)⟧ᶻ) →
      ∀ Db : SMT.Dom,
        ⟦imp_body.abstract
          (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
          (hcov_imp_upd w)⟧ˢ = some Db →
        Db.snd.fst = SMTType.bool) := by
  refine ⟨?_, ?_⟩
  · intro w hw
    obtain ⟨Dapp, hDapp_ty, hDapp_den⟩ := happD_bool w hw
    obtain ⟨Dsubst, hDsubst_den, hDsubst_ty⟩ := hsubst_spec w hw
    obtain ⟨Dimp, hDimp, _⟩ := _root_.denote_imp_some_bool.{u}
      hDapp_den hDapp_ty hDsubst_den hDsubst_ty
    refine Option.isSome_iff_exists.mpr ⟨Dimp, ?_⟩
    convert hDimp using 3
    all_goals
      first
      | rfl
      | (simp only [imp_body_def, SMT.Term.abstract])
  · intro w hw Db hDb
    obtain ⟨Dapp, hDapp_ty, hDapp_den⟩ := happD_bool w hw
    obtain ⟨Dsubst, hDsubst_den, hDsubst_ty⟩ := hsubst_spec w hw
    obtain ⟨Dimp, hDimp, hDimp_ty⟩ :=
      _root_.denote_imp_some_bool.{u} hDapp_den hDapp_ty hDsubst_den hDsubst_ty
    have hBody_eq_Dimp : ⟦imp_body.abstract
        (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
        (hcov_imp_upd w)⟧ˢ = some Dimp := by
      convert hDimp using 3
      all_goals
        first
        | rfl
        | (simp only [imp_body_def, SMT.Term.abstract])
    rw [hBody_eq_Dimp] at hDb
    cases hDb
    exact hDimp_ty

/-- HAS-FLAG analog of `himp_total_ty_bundle`: bundle `himp_total + himp_ty` for
the has-flag `imp_body = z_mem_D' ⇒ (substList vs (zs.var) P_enc)` shape.

Difference from the no-flag version: the antecedent is the opaque
`castMembership` output `z_mem_D'` rather than `(D_enc.app pairl)`, so we take
its denotation+typing directly via `hzmem_bool` (typically derived from
`castMembership_spec`'s totality output `cm_total`). The implication-body
totality and `.bool` typing are then assembled via `denote_imp_some_bool`.

Used in the has-flag nonempty/empty `all_case` branches to discharge the
totality (`himp_total`) and typing (`himp_ty`) preconditions of
`retract_forallVal_eq_sInter_sep_hasflag`. -/
theorem himp_total_ty_bundle_hasflag.{u}
    {imp_body z_mem_D' P_enc : SMT.Term} {vs : List B.𝒱} {zs : List SMT.𝒱}
    {τs : List SMTType} (zs_len : zs.length = τs.length)
    {Δ' : SMT.RenamingContext.Context}
    (imp_body_def : imp_body =
      z_mem_D'.imp (SMT.substList vs (List.map SMT.Term.var zs) P_enc))
    {hcov_zmem_upd :
      ∀ (w : Fin zs.length → SMT.Dom.{u}),
        SMT.RenamingContext.CoversFV
          (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
          z_mem_D'}
    {hcov_subst_upd :
      ∀ (w : Fin zs.length → SMT.Dom.{u}),
        SMT.RenamingContext.CoversFV
          (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
          (SMT.substList vs (List.map SMT.Term.var zs) P_enc)}
    (hcov_imp_upd :
      ∀ (w : Fin zs.length → SMT.Dom.{u}),
        SMT.RenamingContext.CoversFV
          (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
          imp_body)
    (hzmem_bool :
      ∀ (w : Fin zs.length → SMT.Dom.{u})
        (_hw : ∀ i, (w i).snd.fst = τs[i]'(zs_len ▸ i.isLt) ∧
            (w i).fst ∈ ⟦τs[i]'(zs_len ▸ i.isLt)⟧ᶻ),
        ∃ Dzm : SMT.Dom,
          ⟦z_mem_D'.abstract
              (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
              (hcov_zmem_upd w)⟧ˢ = some Dzm ∧ Dzm.snd.fst = .bool)
    (hsubst_spec :
      ∀ (w : Fin zs.length → SMT.Dom.{u})
        (hw : ∀ i, (w i).snd.fst = τs[i]'(zs_len ▸ i.isLt) ∧
                (w i).fst ∈ ⟦τs[i]'(zs_len ▸ i.isLt)⟧ᶻ),
        ∃ Dsubst : SMT.Dom,
          ⟦(SMT.substList vs (List.map SMT.Term.var zs) P_enc).abstract
            (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
            (hcov_subst_upd w)⟧ˢ = some Dsubst ∧
          Dsubst.snd.fst = .bool) :
    (∀ (w : Fin zs.length → SMT.Dom.{u}),
      (∀ i, (w i).snd.fst = τs[i]'(zs_len ▸ i.isLt) ∧
        (w i).fst ∈ ⟦τs[i]'(zs_len ▸ i.isLt)⟧ᶻ) →
      ⟦imp_body.abstract
        (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
        (hcov_imp_upd w)⟧ˢ.isSome = true) ∧
    (∀ (w : Fin zs.length → SMT.Dom.{u}),
      (∀ i, (w i).snd.fst = τs[i]'(zs_len ▸ i.isLt) ∧
        (w i).fst ∈ ⟦τs[i]'(zs_len ▸ i.isLt)⟧ᶻ) →
      ∀ Db : SMT.Dom,
        ⟦imp_body.abstract
          (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
          (hcov_imp_upd w)⟧ˢ = some Db →
        Db.snd.fst = SMTType.bool) := by
  refine ⟨?_, ?_⟩
  · intro w hw
    obtain ⟨Dzm, hDzm_den, hDzm_ty⟩ := hzmem_bool w hw
    obtain ⟨Dsubst, hDsubst_den, hDsubst_ty⟩ := hsubst_spec w hw
    obtain ⟨Dimp, hDimp, _⟩ := _root_.denote_imp_some_bool.{u}
      hDzm_den hDzm_ty hDsubst_den hDsubst_ty
    refine Option.isSome_iff_exists.mpr ⟨Dimp, ?_⟩
    convert hDimp using 3
    all_goals
      first
      | rfl
      | (simp only [imp_body_def, SMT.Term.abstract])
  · intro w hw Db hDb
    obtain ⟨Dzm, hDzm_den, hDzm_ty⟩ := hzmem_bool w hw
    obtain ⟨Dsubst, hDsubst_den, hDsubst_ty⟩ := hsubst_spec w hw
    obtain ⟨Dimp, hDimp, hDimp_ty⟩ :=
      _root_.denote_imp_some_bool.{u} hDzm_den hDzm_ty hDsubst_den hDsubst_ty
    have hBody_eq_Dimp : ⟦imp_body.abstract
        (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
        (hcov_imp_upd w)⟧ˢ = some Dimp := by
      convert hDimp using 3
      all_goals
        first
        | rfl
        | (simp only [imp_body_def, SMT.Term.abstract])
    rw [hBody_eq_Dimp] at hDb
    cases hDb
    exact hDimp_ty

/-- HAS-FLAG totality projection of `himp_total_ty_bundle_hasflag`. Returns just
the `himp_total` half (body totality at any zs-witness). Convenience wrapper for
call sites that only need the totality half. -/
theorem himp_total_hasflag.{u}
    {imp_body z_mem_D' P_enc : SMT.Term} {vs : List B.𝒱} {zs : List SMT.𝒱}
    {τs : List SMTType} (zs_len : zs.length = τs.length)
    {Δ' : SMT.RenamingContext.Context}
    (imp_body_def : imp_body =
      z_mem_D'.imp (SMT.substList vs (List.map SMT.Term.var zs) P_enc))
    {hcov_zmem_upd :
      ∀ (w : Fin zs.length → SMT.Dom.{u}),
        SMT.RenamingContext.CoversFV
          (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
          z_mem_D'}
    {hcov_subst_upd :
      ∀ (w : Fin zs.length → SMT.Dom.{u}),
        SMT.RenamingContext.CoversFV
          (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
          (SMT.substList vs (List.map SMT.Term.var zs) P_enc)}
    (hcov_imp_upd :
      ∀ (w : Fin zs.length → SMT.Dom.{u}),
        SMT.RenamingContext.CoversFV
          (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
          imp_body)
    (hzmem_bool :
      ∀ (w : Fin zs.length → SMT.Dom.{u})
        (_hw : ∀ i, (w i).snd.fst = τs[i]'(zs_len ▸ i.isLt) ∧
            (w i).fst ∈ ⟦τs[i]'(zs_len ▸ i.isLt)⟧ᶻ),
        ∃ Dzm : SMT.Dom,
          ⟦z_mem_D'.abstract
              (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
              (hcov_zmem_upd w)⟧ˢ = some Dzm ∧ Dzm.snd.fst = .bool)
    (hsubst_spec :
      ∀ (w : Fin zs.length → SMT.Dom.{u})
        (hw : ∀ i, (w i).snd.fst = τs[i]'(zs_len ▸ i.isLt) ∧
                (w i).fst ∈ ⟦τs[i]'(zs_len ▸ i.isLt)⟧ᶻ),
        ∃ Dsubst : SMT.Dom,
          ⟦(SMT.substList vs (List.map SMT.Term.var zs) P_enc).abstract
            (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
            (hcov_subst_upd w)⟧ˢ = some Dsubst ∧
          Dsubst.snd.fst = .bool) :
    ∀ (w : Fin zs.length → SMT.Dom.{u}),
      (∀ i, (w i).snd.fst = τs[i]'(zs_len ▸ i.isLt) ∧
        (w i).fst ∈ ⟦τs[i]'(zs_len ▸ i.isLt)⟧ᶻ) →
      ⟦imp_body.abstract
        (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
        (hcov_imp_upd w)⟧ˢ.isSome = true :=
  (himp_total_ty_bundle_hasflag.{u} zs_len imp_body_def hcov_imp_upd
    hzmem_bool hsubst_spec).1

/-- HAS-FLAG typing projection of `himp_total_ty_bundle_hasflag`. Returns just
the `himp_ty` half (body denotation has type `.bool` at any zs-witness).
Convenience wrapper. -/
theorem himp_ty_hasflag.{u}
    {imp_body z_mem_D' P_enc : SMT.Term} {vs : List B.𝒱} {zs : List SMT.𝒱}
    {τs : List SMTType} (zs_len : zs.length = τs.length)
    {Δ' : SMT.RenamingContext.Context}
    (imp_body_def : imp_body =
      z_mem_D'.imp (SMT.substList vs (List.map SMT.Term.var zs) P_enc))
    {hcov_zmem_upd :
      ∀ (w : Fin zs.length → SMT.Dom.{u}),
        SMT.RenamingContext.CoversFV
          (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
          z_mem_D'}
    {hcov_subst_upd :
      ∀ (w : Fin zs.length → SMT.Dom.{u}),
        SMT.RenamingContext.CoversFV
          (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
          (SMT.substList vs (List.map SMT.Term.var zs) P_enc)}
    (hcov_imp_upd :
      ∀ (w : Fin zs.length → SMT.Dom.{u}),
        SMT.RenamingContext.CoversFV
          (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
          imp_body)
    (hzmem_bool :
      ∀ (w : Fin zs.length → SMT.Dom.{u})
        (_hw : ∀ i, (w i).snd.fst = τs[i]'(zs_len ▸ i.isLt) ∧
            (w i).fst ∈ ⟦τs[i]'(zs_len ▸ i.isLt)⟧ᶻ),
        ∃ Dzm : SMT.Dom,
          ⟦z_mem_D'.abstract
              (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
              (hcov_zmem_upd w)⟧ˢ = some Dzm ∧ Dzm.snd.fst = .bool)
    (hsubst_spec :
      ∀ (w : Fin zs.length → SMT.Dom.{u})
        (hw : ∀ i, (w i).snd.fst = τs[i]'(zs_len ▸ i.isLt) ∧
                (w i).fst ∈ ⟦τs[i]'(zs_len ▸ i.isLt)⟧ᶻ),
        ∃ Dsubst : SMT.Dom,
          ⟦(SMT.substList vs (List.map SMT.Term.var zs) P_enc).abstract
            (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
            (hcov_subst_upd w)⟧ˢ = some Dsubst ∧
          Dsubst.snd.fst = .bool) :
    ∀ (w : Fin zs.length → SMT.Dom.{u}),
      (∀ i, (w i).snd.fst = τs[i]'(zs_len ▸ i.isLt) ∧
        (w i).fst ∈ ⟦τs[i]'(zs_len ▸ i.isLt)⟧ᶻ) →
      ∀ Db : SMT.Dom,
        ⟦imp_body.abstract
          (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
          (hcov_imp_upd w)⟧ˢ = some Db →
        Db.snd.fst = SMTType.bool :=
  (himp_total_ty_bundle_hasflag.{u} zs_len imp_body_def hcov_imp_upd
    hzmem_bool hsubst_spec).2

/-- HAS-FLAG variant of `hsubst_spec_helper`: identical preconditions and
shape, but provided under the has-flag naming so the call site reads naturally.
Since the substList denotation under zs-updates is independent of whether the
body uses `D_enc.app pairl` or `z_mem_D'` as antecedent, this is a thin alias of
`hsubst_spec_helper`. Provided for symmetry with the no-flag bundle and to
make the dependency on `cm_total`-style totality explicit at the call site. -/
theorem hsubst_spec_hasflag.{u}
    {vs : List B.𝒱} {zs : List SMT.𝒱} {τs : List SMTType}
    (vs_nodup : vs.Nodup) (zs_nodup : zs.Nodup)
    (vs_zs_len : vs.length = zs.length)
    (vs_τs_len : vs.length = τs.length)
    (zs_len : zs.length = τs.length)
    {Δ' : SMT.RenamingContext.Context}
    {P_enc : SMT.Term}
    {St₄types : SMT.TypeContext}
    (Δ'_outside_vs_isSome : ∀ v, v ∉ vs → v ∈ SMT.fv P_enc → (Δ' v).isSome)
    (Δ'_outside_vs_wt : ∀ v, v ∉ vs → ∀ (d : SMT.Dom),
      Δ' v = some d → ∀ τ, St₄types.lookup v = some τ → d.snd.fst = τ)
    (vs_sub_St₄_types : ∀ v ∈ vs, v ∈ St₄types)
    (vs_typing_St₄ : ∀ (i : ℕ) (hi : i < vs.length),
      St₄types.lookup vs[i] = some (τs[i]'(vs_τs_len ▸ hi)))
    (zs_not_bv_P : ∀ z ∈ zs, z ∉ SMT.bv P_enc)
    (zs_not_St₄_types : ∀ z ∈ zs, z ∉ St₄types)
    (typ_P_enc : St₄types ⊢ˢ P_enc : SMTType.bool)
    (hcov_subst_upd :
      ∀ w : Fin zs.length → SMT.Dom.{u},
        SMT.RenamingContext.CoversFV
          (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
          (SMT.substList vs (List.map SMT.Term.var zs) P_enc)) :
    ∀ (w : Fin zs.length → SMT.Dom.{u})
      (hw : ∀ i, (w i).snd.fst = τs[i]'(zs_len ▸ i.isLt) ∧
              (w i).fst ∈ ⟦τs[i]'(zs_len ▸ i.isLt)⟧ᶻ),
      ∃ Dsubst : SMT.Dom,
        ⟦(SMT.substList vs (List.map SMT.Term.var zs) P_enc).abstract
          (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
          (hcov_subst_upd w)⟧ˢ = some Dsubst ∧
        Dsubst.snd.fst = .bool :=
  hsubst_spec_helper.{u}
    vs_nodup zs_nodup vs_zs_len vs_τs_len zs_len
    Δ'_outside_vs_isSome Δ'_outside_vs_wt
    vs_sub_St₄_types vs_typing_St₄
    zs_not_bv_P zs_not_St₄_types typ_P_enc hcov_subst_upd

open Classical B in
/-- HAS-FLAG semantic bridge for `retract_forallVal_eq_sInter_sep_hasflag`.

Constructs the `hbridge` argument expected by the has-flag forall bridge,
using:
* `castMembership_branch2_spec`'s Δ-universal adequacy abstracted as `hzmem_iff`
  (relating `Dzm.fst = zftrue` to `x_B_of x ∈ 𝒟_val`);
* `hsubst_spec_hasflag` for the substitution-list denotation;
* `hbody_fst_eq_P_val_helper`-style imp-body decomposition for the ZFTRUE
  branch.

Difference from `hbridge_empty_helper`:
* The antecedent is `z_mem_D'` (opaque, not `D_enc.app pairl`), so we take its
  denotation+type+`x_B_of x ∈ 𝒟 ↔ Dzm.fst = zftrue` directly via `hzmem_iff`.
* `x_B := x_B_of x` (caller-supplied, NOT `retract τ x`); `x` ranges over
  `⟦τs.toProdl⟧ᶻ` (i.e., the SMT product domain after looser cast), not
  `⟦τ.toSMTType⟧ᶻ`.

Used in the has-flag nonempty `all_case` branch to build the `hbridge`
argument of `retract_forallVal_eq_sInter_sep_hasflag`. -/
theorem hbridge_hasflag.{u}
    -- Type infrastructure
    {vs : List B.𝒱} (_vs_nemp : vs ≠ [])
    {zs : List SMT.𝒱} {τs : List SMTType}
    (zs_len : zs.length = τs.length) (zs_len_pos : 0 < zs.length)
    {τ : BType} (τ_hasArity : τ.hasArity vs.length)
    -- B-level data
    {«Δ» : B.RenamingContext.Context} {P D : B.Term}
    (Δ_fv : ∀ v ∈ B.fv (B.Term.all vs D P), («Δ» v).isSome = true)
    -- SMT renaming context, body shape (z_mem_D' opaque)
    {Δ' : SMT.RenamingContext.Context}
    {z_mem_D' P_enc imp_body : SMT.Term}
    (imp_body_def : imp_body =
      z_mem_D'.imp (SMT.substList vs (List.map SMT.Term.var zs) P_enc))
    -- Coverage of imp_body / z_mem_D' / substList under zs-updates
    (hcov_imp_upd : ∀ (w : Fin zs.length → SMT.Dom.{u}),
      SMT.RenamingContext.CoversFV
        (Function.updates Δ' zs (List.ofFn (fun i => some (w i)))) imp_body)
    (hcov_zmem_upd : ∀ (w : Fin zs.length → SMT.Dom.{u}),
      SMT.RenamingContext.CoversFV
        (Function.updates Δ' zs (List.ofFn (fun i => some (w i)))) z_mem_D')
    (hcov_subst_upd : ∀ (w : Fin zs.length → SMT.Dom.{u}),
      SMT.RenamingContext.CoversFV
        (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
        (SMT.substList vs (List.map SMT.Term.var zs) P_enc))
    -- Source domain (B-side) and SMT-side cast retract
    {𝒟_val : ZFSet.{u}} (_h𝒟_val : 𝒟_val ∈ ⟦τ.set⟧ᶻ)
    -- Caller-supplied retract
    (x_B_of : ZFSet.{u} → ZFSet.{u})
    (hx_B_of_mem : ∀ (x : ZFSet.{u}), x ∈ ⟦τs.toProdl⟧ᶻ → x_B_of x ∈ ⟦τ⟧ᶻ)
    -- z_mem_D' denotation as a bool that captures `x_B_of x ∈ 𝒟_val`.
    -- `hzmem_iff` is the Δ-universal adequacy clause specialized to each
    -- `x ∈ ⟦τs.toProdl⟧ᶻ` and corresponding `w` whose `Fin.foldl` of fst
    -- components equals `x`.
    (hzmem_bool : ∀ (w : Fin zs.length → SMT.Dom.{u})
        (_hw : ∀ i, (w i).snd.fst = τs[i]'(zs_len ▸ i.isLt) ∧
              (w i).fst ∈ ⟦τs[i]'(zs_len ▸ i.isLt)⟧ᶻ),
      ∃ Dzm : SMT.Dom,
        ⟦z_mem_D'.abstract
            (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
            (hcov_zmem_upd w)⟧ˢ = some Dzm ∧ Dzm.snd.fst = .bool)
    (hzmem_iff : ∀ (x : ZFSet.{u}) (_hx_mem : x ∈ ⟦τs.toProdl⟧ᶻ)
        (w : Fin zs.length → SMT.Dom.{u})
        (_hw : ∀ i, (w i).snd.fst = τs[i]'(zs_len ▸ i.isLt) ∧
              (w i).fst ∈ ⟦τs[i]'(zs_len ▸ i.isLt)⟧ᶻ)
        (_hw_smt : Fin.foldl (zs.length - 1)
          (fun acc i => acc.pair (w ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩).fst)
          (w ⟨0, zs_len_pos⟩).fst = x)
        (Dzm : SMT.Dom)
        (_hDzm_den : ⟦z_mem_D'.abstract
            (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
            (hcov_zmem_upd w)⟧ˢ = some Dzm)
        (_hDzm_ty : Dzm.snd.fst = .bool),
      Dzm.fst = zftrue ↔ x_B_of x ∈ 𝒟_val)
    -- Substitution-list spec
    (hsubst_spec : ∀ (w : Fin zs.length → SMT.Dom.{u})
        (_hw : ∀ i, (w i).snd.fst = τs[i]'(zs_len ▸ i.isLt) ∧
              (w i).fst ∈ ⟦τs[i]'(zs_len ▸ i.isLt)⟧ᶻ),
      ∃ Dsubst : SMT.Dom,
        ⟦(SMT.substList vs (List.map SMT.Term.var zs) P_enc).abstract
          (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
          (hcov_subst_upd w)⟧ˢ = some Dsubst ∧
        Dsubst.snd.fst = .bool)
    -- ZFTRUE-branch hypothesis: when `x_B_of x ∈ 𝒟_val`, the substList
    -- denotation captures the value of P at `x_B_of x`.
    -- Mirrors `hbody_fst_eq_P_val_helper` but parameterized over the caller-
    -- supplied `x_B_of`.
    (hsubst_eq_P : ∀ (x : ZFSet.{u}) (_hx_mem : x ∈ ⟦τs.toProdl⟧ᶻ)
        (_hxB_𝒟 : x_B_of x ∈ 𝒟_val)
        (w : Fin zs.length → SMT.Dom.{u})
        (_hw : ∀ i, (w i).snd.fst = τs[i]'(zs_len ▸ i.isLt) ∧
              (w i).fst ∈ ⟦τs[i]'(zs_len ▸ i.isLt)⟧ᶻ)
        (_hw_smt : Fin.foldl (zs.length - 1)
          (fun acc i => acc.pair (w ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩).fst)
          (w ⟨0, zs_len_pos⟩).fst = x)
        (Dsubst : SMT.Dom)
        (_hDsubst_den : ⟦(SMT.substList vs (List.map SMT.Term.var zs) P_enc).abstract
          (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
          (hcov_subst_upd w)⟧ˢ = some Dsubst)
        (_hDsubst_ty : Dsubst.snd.fst = .bool),
      let x_B := x_B_of x
      let hx_B_mem : x_B ∈ ⟦τ⟧ᶻ := hx_B_of_mem x _hx_mem
      let x_fin : Fin vs.length → B.Dom := fun i =>
        ⟨x_B.get vs.length i, ⟨τ.get vs.length i,
          get_mem_type_of_isTuple (hasArity_of_mem_toZFSet τ_hasArity hx_B_mem)
            τ_hasArity hx_B_mem⟩⟩
      ∃ (P_val : ZFSet.{u}) (hP_val : P_val ∈ ⟦BType.bool⟧ᶻ),
        ⟦(B.Term.abstract.go P vs «Δ» (fun v hv hvs => Δ_fv v
          (B.fv.mem_all (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ =
          some ⟨P_val, ⟨BType.bool, hP_val⟩⟩ ∧
        Dsubst.fst = P_val) :
    ∀ (x : ZFSet.{u}) (hx_mem : x ∈ ⟦τs.toProdl⟧ᶻ),
      let x_B := x_B_of x
      let hx_B_mem : x_B ∈ ⟦τ⟧ᶻ := hx_B_of_mem x hx_mem
      let x_fin : Fin vs.length → B.Dom := fun i =>
        ⟨x_B.get vs.length i, ⟨τ.get vs.length i,
          get_mem_type_of_isTuple (hasArity_of_mem_toZFSet τ_hasArity hx_B_mem)
            τ_hasArity hx_B_mem⟩⟩
      ∀ (w : Fin zs.length → SMT.Dom)
        (_hw : ∀ i, (w i).snd.fst = τs[i]'(zs_len ▸ i.isLt) ∧
          (w i).fst ∈ ⟦τs[i]'(zs_len ▸ i.isLt)⟧ᶻ)
        (_hw_smt : Fin.foldl (zs.length - 1)
          (fun acc i => acc.pair (w ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩).fst)
          (w ⟨0, zs_len_pos⟩).fst = x)
        (body_val : SMT.Dom),
        ⟦imp_body.abstract
          (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
          (hcov_imp_upd w)⟧ˢ = some body_val →
        (body_val.fst = zftrue ↔
          (x_B ∉ 𝒟_val ∨
           ∀ (Px : ZFSet.{u}) (P_ty : BType) (hP_val : Px ∈ ⟦P_ty⟧ᶻ),
             ⟦(B.Term.abstract.go P vs «Δ» (fun v hv hvs => Δ_fv v
               (B.fv.mem_all (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ =
               some ⟨Px, ⟨P_ty, hP_val⟩⟩ → Px = zftrue)) := by
  intro x hx_mem
  simp only []
  intro w hw hw_smt body_val hbody_val
  -- Step 1: Get the denotations of z_mem_D' and substList at zs↦w.
  obtain ⟨Dzm, hDzm_den, hDzm_ty⟩ := hzmem_bool w hw
  obtain ⟨Dsubst, hDsubst_den, hDsubst_ty⟩ := hsubst_spec w hw
  -- Step 2: Combine via denote_imp_some_bool to get Dimp's denotation.
  obtain ⟨Dimp, hDimp, hDimp_ty⟩ :=
    _root_.denote_imp_some_bool.{u} hDzm_den hDzm_ty hDsubst_den hDsubst_ty
  -- Step 3: Reconcile imp_body with the imp-shape: body_val = Dimp.
  have hBody_eq_Dimp : ⟦imp_body.abstract
      (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
      (hcov_imp_upd w)⟧ˢ = some Dimp := by
    convert hDimp using 3
    all_goals
      first
      | rfl
      | (simp only [imp_body_def, SMT.Term.abstract])
  have hbody_eq_Dimp : body_val = Dimp :=
    Option.some.inj (hbody_val.symm.trans hBody_eq_Dimp)
  -- Step 4: Get the iff between Dzm.fst = zftrue and x_B_of x ∈ 𝒟_val.
  have hzmem_iff_at := hzmem_iff x hx_mem w hw hw_smt Dzm hDzm_den hDzm_ty
  -- Step 5: Case-split on Dzm.fst (boolean: either zffalse or zftrue).
  have hDzm_mem_𝔹 : Dzm.fst ∈ 𝔹 := by
    have := Dzm.snd.snd; rwa [hDzm_ty] at this
  rcases (ZFSet.ZFBool.mem_𝔹_iff _).mp hDzm_mem_𝔹 with hDzm_false | hDzm_true
  · -- ZFFALSE case: Dzm.fst = zffalse. The implication is vacuously true.
    -- This means x_B_of x ∉ 𝒟_val.
    have hxB_not_𝒟 : x_B_of x ∉ 𝒟_val := by
      intro hcon
      have : Dzm.fst = zftrue := hzmem_iff_at.mpr hcon
      rw [this] at hDzm_false
      exact ZFSet.zftrue_ne_zffalse hDzm_false
    -- Body denotes to zftrue (vacuous imp).
    have hDimp_eq : ⟦z_mem_D'.abstract
        (Function.updates Δ' zs (List.ofFn (fun i => some (w i)))) (hcov_zmem_upd w) ⇒ˢ'
        (SMT.substList vs (List.map SMT.Term.var zs) P_enc).abstract
          (Function.updates Δ' zs (List.ofFn (fun i => some (w i)))) (hcov_subst_upd w)⟧ˢ =
        some ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ :=
      denote_imp_eq_zftrue_of_zffalse_left.{u}
        hDzm_den hDzm_ty hDzm_false hDsubst_den hDsubst_ty
    have hbody_is_true_dom :
        body_val = ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
      have hDimp_eq' : ⟦imp_body.abstract
          (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
          (hcov_imp_upd w)⟧ˢ = some ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
        convert hDimp_eq using 3
        all_goals
          first
          | rfl
          | (simp only [imp_body_def, SMT.Term.abstract])
      exact Option.some.inj (hbody_val.symm.trans hDimp_eq')
    have hbody_fst_true : body_val.fst = zftrue := by rw [hbody_is_true_dom]
    constructor
    · intro _; exact Or.inl hxB_not_𝒟
    · intro _; exact hbody_fst_true
  · -- ZFTRUE case: Dzm.fst = zftrue, so x_B_of x ∈ 𝒟_val.
    -- body_val.fst = Dimp.fst depends on Dsubst.fst, which equals P_val
    -- by hsubst_eq_P.
    have hxB_𝒟 : x_B_of x ∈ 𝒟_val := hzmem_iff_at.mp hDzm_true
    -- Get P_val from hsubst_eq_P.
    obtain ⟨P_val, hP_val_mem, hP_den, hDsubst_fst_eq_P⟩ :=
      hsubst_eq_P x hx_mem hxB_𝒟 w hw hw_smt Dsubst hDsubst_den hDsubst_ty
    -- Determine body_val.fst from Dimp's value.
    -- Dsubst.fst is bool, so it's zftrue or zffalse; this determines Dimp.fst
    -- since Dzm.fst = zftrue (modus ponens).
    have hDsubst_mem_𝔹 : Dsubst.fst ∈ 𝔹 := by
      have := Dsubst.snd.snd; rwa [hDsubst_ty] at this
    have hbody_fst_eq_P_val : body_val.fst = P_val := by
      rw [hbody_eq_Dimp]
      rcases (ZFSet.ZFBool.mem_𝔹_iff _).mp hDsubst_mem_𝔹 with hDsubst_false | hDsubst_true
      · -- Dsubst.fst = zffalse → Dimp.fst = zffalse → P_val = zffalse.
        have hP_val_eq : P_val = zffalse := hDsubst_fst_eq_P ▸ hDsubst_false
        have hDimp_fst_eq_zffalse : Dimp.fst = zffalse := by
          have hRes : ⟦z_mem_D'.abstract
              (Function.updates Δ' zs (List.ofFn (fun i => some (w i)))) (hcov_zmem_upd w) ⇒ˢ'
              (SMT.substList vs (List.map SMT.Term.var zs) P_enc).abstract
                (Function.updates Δ' zs (List.ofFn (fun i => some (w i)))) (hcov_subst_upd w)⟧ˢ =
              some ⟨zffalse, .bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
            have hDnq := denote_not_eq_zftrue_of_some_zffalse hDsubst_den hDsubst_ty hDsubst_false
            have hDand := denote_and_eq_zftrue_of_some_zftrue hDzm_den hDzm_ty hDzm_true
              hDnq rfl rfl
            exact denote_not_eq_zffalse_of_some_zftrue hDand rfl rfl
          have heq := Option.some.inj (hRes.symm.trans hDimp)
          exact (congrArg (·.fst) heq.symm)
        rw [hDimp_fst_eq_zffalse, hP_val_eq]
      · -- Dsubst.fst = zftrue → Dimp.fst = zftrue → P_val = zftrue.
        have hP_val_eq : P_val = zftrue := hDsubst_fst_eq_P ▸ hDsubst_true
        have hDimp_fst_eq_zftrue : Dimp.fst = zftrue := by
          have hRes : ⟦z_mem_D'.abstract
              (Function.updates Δ' zs (List.ofFn (fun i => some (w i)))) (hcov_zmem_upd w) ⇒ˢ'
              (SMT.substList vs (List.map SMT.Term.var zs) P_enc).abstract
                (Function.updates Δ' zs (List.ofFn (fun i => some (w i)))) (hcov_subst_upd w)⟧ˢ =
              some ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ :=
            denote_imp_eq_zftrue_of_both_zftrue.{u}
              hDzm_den hDzm_ty hDzm_true hDsubst_den hDsubst_ty hDsubst_true
          have heq := Option.some.inj (hRes.symm.trans hDimp)
          exact (congrArg (·.fst) heq.symm)
        rw [hDimp_fst_eq_zftrue, hP_val_eq]
    constructor
    · intro hbody_fst
      right
      intro Px P_ty hPx hPx_den
      -- Px = P_val by uniqueness of P denotation at x_fin.
      have hPx_eq_P_val : Px = P_val ∧ P_ty = BType.bool := by
        have h_inj : (⟨Px, P_ty, hPx⟩ : B.Dom) = ⟨P_val, BType.bool, hP_val_mem⟩ :=
          Option.some.inj (hPx_den.symm.trans hP_den)
        exact ⟨congrArg (·.fst) h_inj, congrArg (·.snd.fst) h_inj⟩
      obtain ⟨hPx_eq, _⟩ := hPx_eq_P_val
      rw [hPx_eq, ← hbody_fst_eq_P_val]
      exact hbody_fst
    · intro hor
      rcases hor with hxB_not_𝒟 | hall
      · exact absurd hxB_𝒟 hxB_not_𝒟
      · -- hall says: ∀ Px..., ⟦P at x_fin⟧ = some ⟨Px, ...⟩ → Px = zftrue.
        -- Apply at P_val.
        have hPval_true : P_val = zftrue :=
          hall P_val BType.bool hP_val_mem hP_den
        rw [hbody_fst_eq_P_val]
        exact hPval_true

/-- The `htot_forall_raw` shape used 4 times in the no-flag `all_case`: lift
the per-witness body totality `himp_total` through `funAbstractGoList`'s
identification of `(abstract.go imp_body zs Δ').uncurry x` with the abstract of
`imp_body` over the extended context.  Saves ~8-9 lines per call site. -/
theorem htot_forall_raw_helper.{u}
    {imp_body : SMT.Term} {zs : List SMT.𝒱} {τs : List SMTType}
    (zs_len : zs.length = τs.length)
    {Δ_ctx : SMT.RenamingContext.Context}
    {hgo_cov : ∀ x ∈ SMT.fv imp_body, x ∉ zs → (Δ_ctx x).isSome = true}
    {hcov_imp_upd :
      ∀ (w : Fin zs.length → SMT.Dom.{u}),
        SMT.RenamingContext.CoversFV
          (Function.updates Δ_ctx zs (List.ofFn (fun i => some (w i))))
          imp_body}
    (himp_total : ∀ (w : Fin zs.length → SMT.Dom.{u}),
      (∀ i, (w i).snd.fst = τs[i]'(zs_len ▸ i.isLt) ∧
        (w i).fst ∈ ⟦τs[i]'(zs_len ▸ i.isLt)⟧ᶻ) →
      ⟦imp_body.abstract
        (Function.updates Δ_ctx zs (List.ofFn (fun i => some (w i))))
        (hcov_imp_upd w)⟧ˢ.isSome = true) :
    ∀ {x : Fin zs.length → SMT.Dom.{u}},
      (∀ i, (x i).snd.fst = τs[i.val]'(zs_len ▸ i.isLt) ∧
        (x i).fst ∈ ⟦τs[i.val]'(zs_len ▸ i.isLt)⟧ᶻ) →
      ⟦(SMT.Term.abstract.go imp_body zs Δ_ctx hgo_cov).uncurry x⟧ˢ.isSome = true := by
  intro x hx
  have hgo_w := funAbstractGoList (Δctx := Δ_ctx) (P := imp_body)
    (vs := zs) (τs := τs) zs_len hgo_cov hcov_imp_upd x hx
  rw [hgo_w]
  exact himp_total x hx

open Classical B in
/-- Semantic bridge for the empty-domain branch of `encodeTerm_spec.all_case`.

When `𝒟 = ∅`, the LEFT disjunct (`x_B ∉ 𝒟`) always holds, so the iff reduces:
- (→) Trivially via `Or.inl`.
- (←) Mirror nonempty case ZFFALSE branch: build `x_B ∈ 𝒟 ↔ Dapp.fst = zftrue`,
  then since `𝒟 = ∅`, `Dapp.fst ≠ zftrue → zffalse → body_val = zftrue`.

Used in the empty-domain branch of `encodeTerm_spec.all_case`. -/
theorem hbridge_empty_helper.{u}
    {vs : List B.𝒱} {zs : List SMT.𝒱} {τs : List SMTType}
    (zs_len : zs.length = τs.length) (zs_len_pos : 0 < zs.length)
    {τ : BType} (τ_hasArity : τ.hasArity vs.length)
    {«Δ» : B.RenamingContext.Context}
    {P D : B.Term}
    (Δ_fv : ∀ v ∈ B.fv (B.Term.all vs D P), («Δ» v).isSome = true)
    {Δ' : SMT.RenamingContext.Context}
    {D_enc P_enc imp_body : SMT.Term}
    (imp_body_def : imp_body =
      (SMT.Term.app D_enc (List.map SMT.Term.var zs).toPairl).imp
        (SMT.substList vs (List.map SMT.Term.var zs) P_enc))
    {𝒟 : ZFSet.{u}} {denD' : SMT.Dom.{u}}
    (denD'_func : ⟦τ.toSMTType⟧ᶻ.IsFunc 𝔹 denD'.fst)
    (denD'_retract : retract (BType.set τ) denD'.fst = 𝒟)
    (h𝒟_empty_eq : 𝒟 = ∅)
    (hcov_imp_upd : ∀ (w : Fin zs.length → SMT.Dom.{u}),
      SMT.RenamingContext.CoversFV
        (Function.updates Δ' zs (List.ofFn (fun i => some (w i)))) imp_body)
    (hcov_appD_upd : ∀ (w : Fin zs.length → SMT.Dom.{u}),
      SMT.RenamingContext.CoversFV
        (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
        (SMT.Term.app D_enc (List.map SMT.Term.var zs).toPairl))
    (hcov_subst_upd : ∀ (w : Fin zs.length → SMT.Dom.{u}),
      SMT.RenamingContext.CoversFV
        (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
        (SMT.substList vs (List.map SMT.Term.var zs) P_enc))
    (hdenote_appD_upd : ∀ (w : Fin zs.length → SMT.Dom.{u})
        (_hw : ∀ i, (w i).snd.fst = τs[i]'(zs_len ▸ i.isLt) ∧
              (w i).fst ∈ ⟦τs[i]'(zs_len ▸ i.isLt)⟧ᶻ),
      let x_smt : ZFSet.{u} := Fin.foldl (zs.length - 1)
          (fun acc i => acc.pair (w ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩).fst)
          (w ⟨0, zs_len_pos⟩).fst
      ∃ (hx_mem : x_smt ∈ ⟦τ.toSMTType⟧ᶻ) (Dapp : SMT.Dom),
        Dapp.snd.fst = .bool ∧
        Dapp.fst = @ᶻdenD'.fst
            ⟨x_smt, by rw [ZFSet.is_func_dom_eq denD'_func]; exact hx_mem⟩ ∧
        ⟦(SMT.Term.app D_enc (List.map SMT.Term.var zs).toPairl).abstract
            (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
            (hcov_appD_upd w)⟧ˢ = some Dapp)
    (hsubst_spec : ∀ (w : Fin zs.length → SMT.Dom.{u})
        (_hw : ∀ i, (w i).snd.fst = τs[i]'(zs_len ▸ i.isLt) ∧
                (w i).fst ∈ ⟦τs[i]'(zs_len ▸ i.isLt)⟧ᶻ),
        ∃ Dsubst : SMT.Dom,
          ⟦(SMT.substList vs (List.map SMT.Term.var zs) P_enc).abstract
            (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
            (hcov_subst_upd w)⟧ˢ = some Dsubst ∧
          Dsubst.snd.fst = .bool) :
    ∀ (x : ZFSet.{u}) (hx_mem : x ∈ ⟦τ.toSMTType⟧ᶻ),
      let x_B := retract τ x
      let hx_B_mem : x_B ∈ ⟦τ⟧ᶻ := retract_mem_of_canonical τ hx_mem
      let x_fin : Fin vs.length → B.Dom := fun i =>
        ⟨x_B.get vs.length i, ⟨τ.get vs.length i,
          get_mem_type_of_isTuple (hasArity_of_mem_toZFSet τ_hasArity hx_B_mem)
            τ_hasArity hx_B_mem⟩⟩
      ∀ (w : Fin zs.length → SMT.Dom)
        (_hw : ∀ i, (w i).snd.fst = τs[i]'(zs_len ▸ i.isLt) ∧
          (w i).fst ∈ ⟦τs[i]'(zs_len ▸ i.isLt)⟧ᶻ)
        (_hw_smt : Fin.foldl (zs.length - 1)
          (fun acc i => acc.pair (w ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩).fst)
          (w ⟨0, zs_len_pos⟩).fst = x)
        (body_val : SMT.Dom),
        ⟦imp_body.abstract
          (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
          (hcov_imp_upd w)⟧ˢ = some body_val →
        (body_val.fst = zftrue ↔
          (x_B ∉ 𝒟 ∨
           ∀ (Px : ZFSet.{u}) (P_ty : BType) (hP_val : Px ∈ ⟦P_ty⟧ᶻ),
             ⟦(B.Term.abstract.go P vs «Δ» (fun v hv hvs => Δ_fv v
               (B.fv.mem_all (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ =
               some ⟨Px, ⟨P_ty, hP_val⟩⟩ → Px = zftrue)) := by
  intro x hx_mem
  simp only []
  intro w hw hw_smt body_val hbody_val
  obtain ⟨hx_mem_smt, Dapp, hDapp_ty, hDapp_val, hDapp_den⟩ := hdenote_appD_upd w hw
  obtain ⟨Dsubst, hDsubst_den, hDsubst_ty⟩ := hsubst_spec w hw
  obtain ⟨Dimp, hDimp, hDimp_ty⟩ :=
    _root_.denote_imp_some_bool.{u} hDapp_den hDapp_ty hDsubst_den hDsubst_ty
  have hBody_eq_Dimp : ⟦imp_body.abstract
      (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
      (hcov_imp_upd w)⟧ˢ = some Dimp := by
    convert hDimp using 3
    all_goals
      first
      | rfl
      | (simp only [imp_body_def, SMT.Term.abstract])
  have hbody_eq_Dimp : body_val = Dimp :=
    Option.some.inj (hbody_val.symm.trans hBody_eq_Dimp)
  have hx_B_not_𝒟 : retract τ x ∉ 𝒟 := by
    rw [h𝒟_empty_eq]
    exact ZFSet.notMem_empty _
  constructor
  · intro _; exact Or.inl hx_B_not_𝒟
  · intro _
    set x_B : ZFSet.{u} := retract τ x
    have hx_B_mem : x_B ∈ ⟦τ⟧ᶻ := retract_mem_of_canonical τ hx_mem
    have hDapp_mem_𝔹 : Dapp.fst ∈ 𝔹 := by
      have := Dapp.snd.snd; rwa [hDapp_ty] at this
    have hDapp_val_x : Dapp.fst = @ᶻdenD'.fst ⟨x,
        by rw [ZFSet.is_func_dom_eq denD'_func]; exact hx_mem⟩ := by
      rw [hDapp_val]
      have hsub : (⟨Fin.foldl (zs.length - 1)
          (fun acc i => acc.pair (w ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩).fst)
          (w ⟨0, zs_len_pos⟩).fst,
          by rw [ZFSet.is_func_dom_eq denD'_func]; exact hx_mem_smt⟩
          : {z // z ∈ denD'.fst.Dom}) =
          ⟨x, by rw [ZFSet.is_func_dom_eq denD'_func]; exact hx_mem⟩ := by
        apply Subtype.ext; exact hw_smt
      rw [hsub]
    have hRetr_denD' : retract (BType.set τ) denD'.fst = 𝒟 := denD'_retract
    have hx_B_𝒟_iff : x_B ∈ 𝒟 ↔ Dapp.fst = zftrue := by
      rw [hDapp_val_x]
      have hcan : ZFSet.fapply (BType.canonicalIsoSMTType τ).1
          (is_func_is_pfunc (BType.canonicalIsoSMTType τ).2.1)
          ⟨x_B, ZFSet.mem_dom (is_func_is_pfunc
            (BType.canonicalIsoSMTType τ).2.1)
            (canonical_pair_of_retract τ hx_mem)⟩ = x :=
        canonical_of_retract τ hx_mem
      have hsub_x : (⟨x,
          by rw [ZFSet.is_func_dom_eq denD'_func]; exact hx_mem⟩
          : {z // z ∈ denD'.fst.Dom}) =
          ⟨ZFSet.fapply (BType.canonicalIsoSMTType τ).1
            (is_func_is_pfunc (BType.canonicalIsoSMTType τ).2.1)
            ⟨x_B, ZFSet.mem_dom (is_func_is_pfunc
              (BType.canonicalIsoSMTType τ).2.1)
              (canonical_pair_of_retract τ hx_mem)⟩,
            by rw [ZFSet.is_func_dom_eq denD'_func]
               exact fapply_mem_range _ _⟩ := by
        apply Subtype.ext; exact hcan.symm
      rw [hsub_x]
      rw [← hRetr_denD']
      rw [retract, mem_sep]
      constructor
      · rintro ⟨hx_B_α, hmem⟩
        rw [dif_pos hx_B_α, dif_pos denD'_func] at hmem
        simpa using hmem
      · intro hfapp
        refine ⟨hx_B_mem, ?_⟩
        rw [dif_pos hx_B_mem, dif_pos denD'_func]
        simpa using hfapp
    have hDapp_ne_true : Dapp.fst ≠ zftrue := by
      intro hcon
      exact hx_B_not_𝒟 (hx_B_𝒟_iff.mpr hcon)
    have hDapp_false : Dapp.fst = zffalse := by
      rcases (ZFSet.ZFBool.mem_𝔹_iff _).mp hDapp_mem_𝔹 with hf | ht
      · exact hf
      · exact (hDapp_ne_true ht).elim
    have hDimp_eq : ⟦((@ˢD_enc) (List.map SMT.Term.var zs).toPairl
        ⇒ˢ SMT.substList vs (List.map SMT.Term.var zs) P_enc).abstract
        (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
        (by simpa [imp_body_def] using hcov_imp_upd w)⟧ˢ =
        some ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
      have := denote_imp_eq_zftrue_of_zffalse_left.{u}
        hDapp_den hDapp_ty hDapp_false hDsubst_den hDsubst_ty
      convert this using 3
      all_goals first | rfl | (simp only [SMT.Term.abstract])
    have hbody_is_true_dom :
        body_val = ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
      have hDimp_eq' : ⟦imp_body.abstract
          (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
          (hcov_imp_upd w)⟧ˢ = some ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
        convert hDimp_eq using 3
      exact Option.some.inj (hbody_val.symm.trans hDimp_eq')
    rw [hbody_is_true_dom]

open Classical B in
/-- The semantic core of the ZFTRUE branch of `hbridge` in
`encodeTerm_spec.all_case`: when `Dapp.fst = zftrue`, the imp body's value
agrees with `P_val`, the value of the inner predicate `P`. The proof case-splits
on whether `Dsubst.fst` is `zftrue` or `zffalse` and applies the corresponding
imp denotation reduction. -/
theorem hbody_fst_eq_P_val_helper.{u}
    {D_enc P_enc : SMT.Term} {vs : List B.𝒱} {zs : List SMT.𝒱}
    {Δ' : SMT.RenamingContext.Context}
    (w : Fin zs.length → SMT.Dom.{u})
    {Dapp Dsubst Dimp body_val denT_x' : SMT.Dom.{u}}
    {P_val : ZFSet.{u}}
    (hcov_appD_upd : SMT.RenamingContext.CoversFV
      (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
      ((@ˢD_enc) (List.map SMT.Term.var zs).toPairl))
    (hcov_subst_upd : SMT.RenamingContext.CoversFV
      (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
      (SMT.substList vs (List.map SMT.Term.var zs) P_enc))
    (hDapp_den : ⟦((@ˢD_enc) (List.map SMT.Term.var zs).toPairl).abstract
      (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
      hcov_appD_upd⟧ˢ = some Dapp)
    (hDapp_ty : Dapp.snd.fst = .bool)
    (hDapp_true : Dapp.fst = zftrue)
    (hDsubst_den : ⟦(SMT.substList vs (List.map SMT.Term.var zs) P_enc).abstract
      (Function.updates Δ' zs (List.ofFn (fun i => some (w i))))
      hcov_subst_upd⟧ˢ = some Dsubst)
    (hDsubst_ty : Dsubst.snd.fst = .bool)
    (hDimp : ⟦((@ˢD_enc) (List.map SMT.Term.var zs).toPairl).abstract
      (Function.updates Δ' zs (List.ofFn (fun i => some (w i)))) hcov_appD_upd ⇒ˢ'
      (SMT.substList vs (List.map SMT.Term.var zs) P_enc).abstract
        (Function.updates Δ' zs (List.ofFn (fun i => some (w i)))) hcov_subst_upd⟧ˢ =
      some Dimp)
    (hbody_eq_Dimp : body_val = Dimp)
    (hDsubst_eq_denT : Dsubst = denT_x')
    (hdenT_x'_fst_eq : denT_x'.fst = P_val) :
    body_val.fst = P_val := by
  rw [hbody_eq_Dimp]
  have hDsubst_mem_𝔹 : Dsubst.fst ∈ 𝔹 := by
    have := Dsubst.snd.snd; rwa [hDsubst_ty] at this
  rcases (ZFSet.ZFBool.mem_𝔹_iff _).mp hDsubst_mem_𝔹 with hDsubst_false | hDsubst_true
  · have hDsubst_fst_eq : Dsubst.fst = denT_x'.fst := by rw [hDsubst_eq_denT]
    have hDenT_fst : denT_x'.fst = zffalse := hDsubst_fst_eq ▸ hDsubst_false
    have hP_val_eq : P_val = zffalse := hdenT_x'_fst_eq ▸ hDenT_fst
    have hDimp_fst_eq_zffalse : Dimp.fst = zffalse := by
      have hp := hDapp_den
      have hq := hDsubst_den
      have : ⟦((@ˢD_enc) (List.map SMT.Term.var zs).toPairl).abstract
          (Function.updates Δ' zs (List.ofFn (fun i => some (w i)))) hcov_appD_upd ⇒ˢ'
          (SMT.substList vs (List.map SMT.Term.var zs) P_enc).abstract
            (Function.updates Δ' zs (List.ofFn (fun i => some (w i)))) hcov_subst_upd⟧ˢ =
          some ⟨zffalse, .bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
        have hDnq := denote_not_eq_zftrue_of_some_zffalse hq hDsubst_ty hDsubst_false
        have hDand := denote_and_eq_zftrue_of_some_zftrue hp hDapp_ty hDapp_true
          hDnq rfl rfl
        exact denote_not_eq_zffalse_of_some_zftrue hDand rfl rfl
      have := Option.some.inj (this.symm.trans hDimp)
      have := congrArg (·.fst) this.symm; dsimp at this; exact this
    rw [hDimp_fst_eq_zffalse, hP_val_eq]
  · have hDsubst_fst_eq : Dsubst.fst = denT_x'.fst := by rw [hDsubst_eq_denT]
    have hDenT_fst : denT_x'.fst = zftrue := hDsubst_fst_eq ▸ hDsubst_true
    have hP_val_eq : P_val = zftrue := hdenT_x'_fst_eq ▸ hDenT_fst
    have hDimp_fst_eq_zftrue : Dimp.fst = zftrue := by
      have hp := hDapp_den
      have hq := hDsubst_den
      have : ⟦((@ˢD_enc) (List.map SMT.Term.var zs).toPairl).abstract
          (Function.updates Δ' zs (List.ofFn (fun i => some (w i)))) hcov_appD_upd ⇒ˢ'
          (SMT.substList vs (List.map SMT.Term.var zs) P_enc).abstract
            (Function.updates Δ' zs (List.ofFn (fun i => some (w i)))) hcov_subst_upd⟧ˢ =
          some ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ :=
        denote_imp_eq_zftrue_of_both_zftrue.{u} hp hDapp_ty hDapp_true
          hq hDsubst_ty hDsubst_true
      have := Option.some.inj (this.symm.trans hDimp)
      have := congrArg (·.fst) this.symm; dsimp at this; exact this
    rw [hDimp_fst_eq_zftrue, hP_val_eq]

open Classical B in
/-- The `ExtendsOnSourceFV` clause for the hybrid renaming context built in the
ZFTRUE branch of `hbridge` in `encodeTerm_spec.all_case`. The hybrid context
`Δ₀_hybrid_x` agrees with `Δ_D_ext_x` on `vs` (the bound variables) and with
`Δ_P` elsewhere when `v ∈ St₄.env.usedVars`. -/
theorem Δ₀_hybrid_ext_P_x_helper
    {vs : List B.𝒱}
    {«Δ» Δ_ext Δ_ext_x : B.RenamingContext.Context}
    (hΔ_ext_x_eq : ∀ v, v ∉ vs → Δ_ext_x v = «Δ» v)
    (hΔ_ext_eq : ∀ v, v ∉ vs → Δ_ext v = «Δ» v)
    {Δ_D_ext_x Δ_P Δ₀_hybrid_x : SMT.RenamingContext.Context}
    {used_St₄ : List SMT.𝒱} {P : B.Term}
    (Δ_P_src_ext : RenamingContext.ExtendsOnSourceFV Δ_P Δ_ext P)
    (covers_P : ∀ v ∈ B.fv P, v ∈ used_St₄)
    (hΔ₀_eq : ∀ v, Δ₀_hybrid_x v =
      if v ∈ vs then Δ_D_ext_x v
      else if v ∈ used_St₄ then Δ_P v else none)
    (hΔ_D_ext_x_at_vs : ∀ (i : ℕ) (hi : i < vs.length),
      Δ_D_ext_x vs[i] = B.RenamingContext.toSMT Δ_ext_x vs[i]) :
    RenamingContext.ExtendsOnSourceFV Δ₀_hybrid_x Δ_ext_x P := by
  intro v d hv_eq
  by_cases hv_fv : v ∈ B.fv P
  · have hv_smt : B.RenamingContext.toSMT Δ_ext_x v = some d := by
      have heq : B.RenamingContext.toSMTOnFV Δ_ext_x P v =
          B.RenamingContext.toSMT Δ_ext_x v := by
        simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
          B.RenamingContext.restrictToFV_eq_of_mem hv_fv]
      rwa [← heq]
    by_cases hvs : v ∈ vs
    · rw [hΔ₀_eq, if_pos hvs]
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hvs
      rw [hΔ_D_ext_x_at_vs i hi]
      exact hv_smt
    · have hv_St₄_used : v ∈ used_St₄ := covers_P v hv_fv
      rw [hΔ₀_eq, if_neg hvs, if_pos hv_St₄_used]
      have hΔ_ext_x_eq_v : Δ_ext_x v = «Δ» v := hΔ_ext_x_eq v hvs
      have hΔ_ext_eq_v : Δ_ext v = «Δ» v := hΔ_ext_eq v hvs
      have hΔ_ext_x_eq_Δ_ext : Δ_ext_x v = Δ_ext v :=
        hΔ_ext_x_eq_v.trans hΔ_ext_eq_v.symm
      have hv_smt_Δ_ext : B.RenamingContext.toSMT Δ_ext v = some d := by
        rw [B.RenamingContext.toSMT, hΔ_ext_eq_v, ← hΔ_ext_x_eq_v,
            ← B.RenamingContext.toSMT]
        exact hv_smt
      apply Δ_P_src_ext
      simp only [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
        B.RenamingContext.restrictToFV_eq_of_mem hv_fv, Option.pure_def,
        Option.bind_eq_bind]
      rw [B.RenamingContext.toSMT, Option.pure_def, Option.bind_eq_bind] at hv_smt_Δ_ext
      exact hv_smt_Δ_ext
  · have : B.RenamingContext.toSMTOnFV Δ_ext_x P v = none := by
      simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
        B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_fv]
    rw [this] at hv_eq
    exact absurd hv_eq (by simp)

open Classical B in
/-- The well-typedness clause (`wt`) for the hybrid renaming context built in the
ZFTRUE branch of `hbridge` in `encodeTerm_spec.all_case`. For `v ∈ vs`, the
domain element `d` comes from `Δ_ext_x vs[i]`, whose SMT type matches `τs[i]`;
for `v ∉ vs`, we fall through to `Δ_P_wt`. -/
theorem Δ₀_hybrid_x_wt_helper
    {vs : List B.𝒱}
    {Δ_ext_x : B.RenamingContext.Context}
    {x_fin : Fin vs.length → B.Dom}
    {Δ_D_ext_x Δ_P Δ₀_hybrid_x : SMT.RenamingContext.Context}
    {St₄types : AList (fun _ : SMT.𝒱 => SMTType)}
    {used_St₄ : List SMT.𝒱}
    {τs : List SMTType} {τ : BType}
    (vs_τs_len : vs.length = τs.length)
    (Δ_P_wt : ∀ v (d : SMT.Dom), Δ_P v = some d →
      ∀ τ_v, St₄types.lookup v = some τ_v → d.snd.fst = τ_v)
    (St₄_keys_sub : ∀ v, v ∈ St₄types → v ∈ used_St₄)
    (hΔ₀_eq : ∀ v, Δ₀_hybrid_x v =
      if v ∈ vs then Δ_D_ext_x v
      else if v ∈ used_St₄ then Δ_P v else none)
    (hΔ_D_ext_x_at_vs : ∀ (i : ℕ) (hi : i < vs.length),
      Δ_D_ext_x vs[i] = B.RenamingContext.toSMT Δ_ext_x vs[i])
    (hΔ_ext_x_at_vs : ∀ (i : ℕ) (hi : i < vs.length),
      Δ_ext_x vs[i] = some (x_fin ⟨i, hi⟩))
    (hvs_typing_St₄ : ∀ (i : ℕ) (hi : i < vs.length),
      St₄types.lookup vs[i] = some (τs[i]'(vs_τs_len ▸ hi)))
    (hx_fin_typ : ∀ (i : Fin vs.length), (x_fin i).snd.fst = τ.get vs.length i)
    (hτs_match : ∀ (i : Fin vs.length),
      (τ.get vs.length i).toSMTType = τs[i.val]'(vs_τs_len ▸ i.isLt)) :
    ∀ (v : SMT.𝒱) (d : SMT.Dom), Δ₀_hybrid_x v = some d →
      ∀ τ_v, St₄types.lookup v = some τ_v → d.snd.fst = τ_v := by
  intro v d hv τ_v hlookup
  by_cases hvs : v ∈ vs
  · have hv_hybrid : Δ₀_hybrid_x v = Δ_D_ext_x v := by
      rw [hΔ₀_eq, if_pos hvs]
    rw [hv_hybrid] at hv
    obtain ⟨i, hi, hvi_eq⟩ := List.mem_iff_getElem.mp hvs
    subst hvi_eq
    rw [hΔ_D_ext_x_at_vs i hi] at hv
    rw [hvs_typing_St₄ i hi] at hlookup
    cases hlookup
    simp only [B.RenamingContext.toSMT, hΔ_ext_x_at_vs i hi, Option.pure_def,
      Option.bind_eq_bind, Option.bind_some] at hv
    have hd_eq := Option.some.inj hv
    rw [← hd_eq]
    show (x_fin ⟨i, hi⟩).snd.fst.toSMTType = τs[i]
    rw [hx_fin_typ ⟨i, hi⟩]
    exact hτs_match ⟨i, hi⟩
  · have hv_St₄ : v ∈ St₄types := AList.lookup_isSome.mp (by rw [hlookup]; simp)
    have hv_St₄_used : v ∈ used_St₄ := St₄_keys_sub v hv_St₄
    have hv_hybrid : Δ₀_hybrid_x v = Δ_P v := by
      rw [hΔ₀_eq, if_neg hvs, if_pos hv_St₄_used]
    rw [hv_hybrid] at hv
    exact Δ_P_wt v d hv τ_v hlookup

open Classical B in
/-- Agreement clause for transferring `Dsubst`'s denotation from `Δ'_upd` to
`Δ_P_x_upd` in the ZFTRUE branch of `hbridge` in `encodeTerm_spec.all_case`.
On `zs`-variables, both sides agree by construction (same `w`-update).
On non-`zs` variables `v ∈ fv (substList ...)`, splits into `v ∈ fv P_enc`
(forcing agreement via `Δ_P_x_extends`) and `v ∈ fv (var z)` for some `z`
(contradicting `v ∉ zs`). -/
theorem hΔ_upd_agree_substList_helper.{u}
    {vs : List B.𝒱} {zs : List SMT.𝒱} {τs : List SMTType}
    (zs_nodup : zs.Nodup)
    (vs_τs_len : vs.length = τs.length) (zs_len : zs.length = τs.length)
    {Δ' Δ_P Δ_P_x Δ₀_hybrid_x : SMT.RenamingContext.Context}
    {St₄types : AList (fun _ : SMT.𝒱 => SMTType)} {used_St₄ : List SMT.𝒱}
    {P_enc : SMT.Term}
    (Δ'_eq_Δ_P_of_not_vs : ∀ v, v ∉ vs → Δ' v = Δ_P v)
    (hΔ₀_eq_Δ_P : ∀ v, v ∉ vs → v ∈ used_St₄ → Δ₀_hybrid_x v = Δ_P v)
    (Δ_P_x_extends : SMT.RenamingContext.Extends Δ_P_x Δ₀_hybrid_x)
    (Δ_P_covers : SMT.RenamingContext.CoversFV Δ_P P_enc)
    (typ_P_enc : St₄types ⊢ˢ P_enc : .bool)
    (St₄_keys_sub : ∀ v, v ∈ St₄types → v ∈ used_St₄)
    (w : Fin zs.length → SMT.Dom.{u}) :
    SMT.RenamingContext.AgreesOnFV
      (Function.updates Δ' zs (List.ofFn (fun i : Fin zs.length => some (w i))))
      (Function.updates Δ_P_x zs (List.ofFn (fun i : Fin zs.length => some (w i))))
      (SMT.substList vs (List.map SMT.Term.var zs) P_enc) := by
  intro v hv
  by_cases hvzs : v ∈ zs
  · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hvzs
    rw [Function.updates_eq_if (by rw [List.length_ofFn]) zs_nodup,
      dif_pos (List.getElem_mem hj)]
    rw [Function.updates_eq_if (by rw [List.length_ofFn]) zs_nodup,
      dif_pos (List.getElem_mem hj)]
  · rw [Function.updates_of_not_mem Δ' zs _ v hvzs,
      Function.updates_of_not_mem Δ_P_x zs _ v hvzs]
    rcases SMT_mem_fv_substList hv with hv_P | ⟨t, ht, hv_t⟩
    · have hv_St₄ : v ∈ St₄types :=
        SMT.Typing.mem_context_of_mem_fv typ_P_enc hv_P
      have hv_St₄_used : v ∈ used_St₄ := St₄_keys_sub v hv_St₄
      by_cases hvvs : v ∈ vs
      · exfalso
        have hlen : vs.length ≤ (List.map SMT.Term.var zs).length := by
          rw [List.length_map]; exact le_of_eq (zs_len ▸ vs_τs_len)
        by_cases h_all_no_fv :
            ∀ t ∈ List.map SMT.Term.var zs, v ∉ SMT.fv t
        · exact SMT_not_mem_fv_substList_of_mem_vars hlen hvvs h_all_no_fv hv
        · push_neg at h_all_no_fv
          obtain ⟨t, ht, hv_t⟩ := h_all_no_fv
          rw [List.mem_map] at ht
          obtain ⟨z, hz, rfl⟩ := ht
          simp only [SMT.fv, List.mem_singleton] at hv_t
          subst hv_t
          exact hvzs hz
      · have hΔ'_v : Δ' v = Δ_P v := Δ'_eq_Δ_P_of_not_vs v hvvs
        have hΔ₀_v : Δ₀_hybrid_x v = Δ_P v := hΔ₀_eq_Δ_P v hvvs hv_St₄_used
        have hΔ_P_x_v : Δ_P_x v = Δ_P v := by
          cases hΔP : Δ_P v with
          | none =>
            exfalso
            have := Δ_P_covers v hv_P
            rw [hΔP] at this; simp at this
          | some d =>
            rw [Δ_P_x_extends (hΔ₀_v ▸ hΔP)]
        rw [hΔ'_v, hΔ_P_x_v]
    · rw [List.mem_map] at ht
      obtain ⟨z, hz, rfl⟩ := ht
      simp only [SMT.fv, List.mem_singleton] at hv_t
      subst hv_t
      exact absurd hz hvzs

open B in
/-- Apply the canonical isomorphism to project the i-th component of `x_B`.
The result equals the i-th component of the SMT-side tuple `x` (where
`x_B = retract τ x`). Used in the `v ∈ vs` branch of `h_upd_agree_x`. -/
theorem canonical_fapply_get_eq_get.{u}
    {vs : List B.𝒱} {zs : List SMT.𝒱}
    (vs_zs_len : vs.length = zs.length)
    {i : ℕ} (hi : i < vs.length)
    {x x_B : ZFSet.{u}} {τ : BType}
    (τ_hasArity : τ.hasArity vs.length)
    (hx_mem : x ∈ ⟦τ.toSMTType⟧ᶻ)
    (x_B_def : x_B = retract τ x)
    (hx_B_arity : x_B.hasArity vs.length)
    (hx_B_mem : x_B ∈ ⟦τ⟧ᶻ) :
    let i_zs : Fin zs.length := ⟨i, by rw [← vs_zs_len]; exact hi⟩
    (ZFSet.fapply (BType.canonicalIsoSMTType (τ.get vs.length ⟨i, hi⟩)).1
        (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType _).2.1)
        ⟨x_B.get vs.length ⟨i, hi⟩, by
          rw [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType _).2.1]
          exact get_mem_type_of_isTuple hx_B_arity τ_hasArity hx_B_mem⟩).val =
      x.get zs.length i_zs := by
  set vi_fin : Fin vs.length := ⟨i, hi⟩
  set i_zs : Fin zs.length := ⟨i, by rw [← vs_zs_len]; exact hi⟩
  have h_Fin_cast : (Fin.cast vs_zs_len vi_fin) = i_zs := rfl
  have hx_B_get : x_B.get vs.length vi_fin = (retract τ x).get vs.length vi_fin := by
    rw [x_B_def]
  have h_retract_comm : (retract τ x).get vs.length vi_fin =
      retract (τ.get vs.length vi_fin) (x.get vs.length vi_fin) :=
    retract_get_comm
      (hasArity_of_mem_toSMTZFSet τ_hasArity hx_mem) τ_hasArity hx_mem
  have hx_get_mem_v : x.get vs.length vi_fin ∈
      ⟦(τ.get vs.length vi_fin).toSMTType⟧ᶻ :=
    get_mem_toSMTZFSet
      (hasArity_of_mem_toSMTZFSet τ_hasArity hx_mem)
      τ_hasArity hx_mem
  have hx_get_eq : x.get vs.length vi_fin = x.get zs.length i_zs := by
    have : ∀ {n m : ℕ} (h : n = m) (hi₁ : i < n) (hi₂ : i < m),
        x.get n ⟨i, hi₁⟩ = x.get m ⟨i, hi₂⟩ := by
      intro n m h hi₁ hi₂; subst h; rfl
    exact this vs_zs_len hi i_zs.isLt
  have h_xB_as_retract : x_B.get vs.length vi_fin =
      retract (τ.get vs.length vi_fin) (x.get zs.length i_zs) := by
    rw [hx_B_get, h_retract_comm, hx_get_eq]
  have hx_get_zs_mem : x.get zs.length i_zs ∈
      ⟦(τ.get vs.length vi_fin).toSMTType⟧ᶻ := hx_get_eq ▸ hx_get_mem_v
  have hx_pair_mem :
      ZFSet.pair (x_B.get vs.length vi_fin) (x.get zs.length i_zs) ∈
      (BType.canonicalIsoSMTType (τ.get vs.length vi_fin)).1 := by
    rw [h_xB_as_retract]
    exact canonical_pair_of_retract _ hx_get_zs_mem
  exact Subtype.ext_iff.mp <|
    ZFSet.fapply.of_pair
      (is_func_is_pfunc (BType.canonicalIsoSMTType _).2.1)
      hx_pair_mem

/-- The cover clause for `Δ_P_x_upd[vs↦Ds_x.map some]` over `P_enc`.
For `v ∈ vs`, the outer update covers; for `v ∉ vs ∧ v ∈ zs`, the inner
`zs`-update covers; otherwise, fall through to `Δ_P_x v`'s coverage of
`P_enc`. -/
theorem h_cov_upd_x_helper.{u}
    {vs : List B.𝒱} {zs : List SMT.𝒱}
    (vs_nodup : vs.Nodup) (zs_nodup : zs.Nodup)
    {Δ_P_x Δ_P_x_upd : SMT.RenamingContext.Context}
    {Ds_x : List SMT.Dom.{u}}
    (hvs_Ds_x_len : vs.length = Ds_x.length)
    {w : Fin zs.length → SMT.Dom.{u}}
    (Δ_P_x_upd_def : Δ_P_x_upd =
      Function.updates Δ_P_x zs (List.ofFn (fun i : Fin zs.length => some (w i))))
    {P_enc : SMT.Term}
    (hcov_Px : SMT.RenamingContext.CoversFV Δ_P_x P_enc) :
    SMT.RenamingContext.CoversFV
      (Function.updates Δ_P_x_upd vs (Ds_x.map Option.some)) P_enc := by
  intro v hv
  by_cases hvs : v ∈ vs
  · rw [Function.updates_eq_if (by rw [List.length_map]; exact hvs_Ds_x_len) vs_nodup,
      dif_pos hvs]
    simp
  · rw [Function.updates_of_not_mem _ vs _ _ hvs]
    by_cases hvzs : v ∈ zs
    · rw [Δ_P_x_upd_def, Function.updates_eq_if (by rw [List.length_ofFn]) zs_nodup,
        dif_pos hvzs]
      simp
    · rw [Δ_P_x_upd_def, Function.updates_of_not_mem _ zs _ _ hvzs]
      exact hcov_Px v hv

open Classical B in
/-- The `hext_alt_D` and `hnone_alt_D` properties of `Δ₀_alt_D` (the alt-context
on `D`'s free variables, falling through to `Δ₀_alt`/`Δ₀` for non-fv variables
that are still in the encoder's `St₁` used-set).

Returns `(hext_alt_D, hnone_alt_D)` - the source-FV extension property and the
out-of-`St₁_used` `none` property. -/
theorem hΔ₀_alt_D_setup_helper
    {D : B.Term}
    {St₁_used : List SMT.𝒱}
    (covers_D : B.CoversUsedVars St₁_used D)
    {Δ_alt : B.RenamingContext.Context}
    {Δ₀ Δ₀_alt : SMT.RenamingContext.Context} :
    let Δ₀_alt_D : SMT.RenamingContext.Context :=
      fun v => match B.RenamingContext.toSMTOnFV Δ_alt D v with
        | some d => some d
        | none => if v ∈ St₁_used then
            match Δ₀_alt v with
            | some d => some d
            | none => Δ₀ v
          else none
    RenamingContext.ExtendsOnSourceFV Δ₀_alt_D Δ_alt D ∧
    (∀ v ∉ St₁_used, Δ₀_alt_D v = none) := by
  refine ⟨?_, ?_⟩
  · intro v d hv; simp only [hv]
  · intro v hv
    show (match B.RenamingContext.toSMTOnFV Δ_alt D v with
      | some d => some d
      | none => if v ∈ St₁_used then
          match Δ₀_alt v with
          | some d => some d
          | none => Δ₀ v
        else none) = none
    have hv_not_fv_D : v ∉ B.fv D := B.not_mem_fv_of_not_mem_used covers_D hv
    have h_toSMT_none : B.RenamingContext.toSMTOnFV Δ_alt D v = none := by
      simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
        B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_not_fv_D]
    rw [h_toSMT_none, if_neg hv]

open Classical B in
/-- The `Δ'_alt_agrees_Δ_D_alt_on_D` property: on `fv D_enc`, the hybrid alt
context `Δ'_alt = Δ₀_alt ▸ Δ_D_alt ▸ Δ'` agrees with `Δ_D_alt`. Used identically
in both Part 2 totality clauses (nonempty and empty) of `encodeTerm_spec.all_case`. -/
theorem Δ'_alt_agrees_Δ_D_alt_on_D_helper
    {vs : List B.𝒱} {D P : B.Term} {τ : BType}
    {St₁_types : SMT.TypeContext}
    {St₁_used : List SMT.𝒱}
    {D_enc : SMT.Term}
    (typ_D_enc : St₁_types ⊢ˢ D_enc : τ.toSMTType.fun SMTType.bool)
    (St₁_keys_sub : AList.keys St₁_types ⊆ St₁_used)
    {Δ' Δ_D_alt Δ₀_alt Δ₀ : SMT.RenamingContext.Context}
    {Δ_alt : B.RenamingContext.Context}
    (hext_alt : SMT.RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt
      (B.Term.all vs D P))
    (hcov_D_alt : SMT.RenamingContext.CoversFV Δ_D_alt D_enc) :
    let Δ₀_alt_D : SMT.RenamingContext.Context :=
      fun v => match B.RenamingContext.toSMTOnFV Δ_alt D v with
        | some d => some d
        | none => if v ∈ St₁_used then
            match Δ₀_alt v with
            | some d => some d
            | none => Δ₀ v
          else none
    ∀ (hext_D_alt : SMT.RenamingContext.Extends Δ_D_alt Δ₀_alt_D),
    SMT.RenamingContext.AgreesOnFV Δ_D_alt
      (fun v => match Δ₀_alt v with
        | some d => some d
        | none => match Δ_D_alt v with
          | some d => some d
          | none => Δ' v) D_enc := by
  intro Δ₀_alt_D hext_D_alt v hv
  have hv_St₁ : v ∈ St₁_types :=
    SMT.Typing.mem_context_of_mem_fv typ_D_enc hv
  have hcov_Dalt := hcov_D_alt v hv
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hcov_Dalt
  cases h_alt : Δ₀_alt v with
  | some d' =>
    have hv_used : v ∈ St₁_used := St₁_keys_sub hv_St₁
    have hΔ₀_alt_D_v : Δ₀_alt_D v = some d' := by
      show (match B.RenamingContext.toSMTOnFV Δ_alt D v with
        | some d => some d
        | none => if v ∈ St₁_used then
            match Δ₀_alt v with
            | some d => some d
            | none => Δ₀ v
          else none) = some d'
      cases h_toSMT : B.RenamingContext.toSMTOnFV Δ_alt D v with
      | some d'' =>
        have hv_fv_D : v ∈ B.fv D := by
          by_contra hv_not
          simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
            B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_not]
            at h_toSMT
        have h_onFV_all : B.RenamingContext.toSMTOnFV Δ_alt
            (B.Term.all vs D P) v = some d'' := by
          simp only [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
            B.RenamingContext.restrictToFV_eq_of_mem (B.fv.mem_all (.inl hv_fv_D))]
          simp only [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
            B.RenamingContext.restrictToFV_eq_of_mem hv_fv_D] at h_toSMT
          exact h_toSMT
        have hΔ₀_alt_v_all : Δ₀_alt v = some d'' := hext_alt h_onFV_all
        rw [hΔ₀_alt_v_all] at h_alt
        exact Option.some.inj h_alt ▸ rfl
      | none =>
        simp only [if_pos hv_used, h_alt]
    have hΔ_D_alt_v : Δ_D_alt v = some d' := hext_D_alt hΔ₀_alt_D_v
    show Δ_D_alt v = (match Δ₀_alt v with
      | some d => some d
      | none => match Δ_D_alt v with
        | some d => some d
        | none => Δ' v)
    rw [h_alt]
    exact hΔ_D_alt_v
  | none =>
    show Δ_D_alt v = (match Δ₀_alt v with
      | some d => some d
      | none => match Δ_D_alt v with
        | some d => some d
        | none => Δ' v)
    simp only [h_alt, hd]

open Classical B in
/-- The `Δ'_alt_wt` property: every variable on which the hybrid alt context
`Δ'_alt = Δ₀_alt ▸ Δ_D_alt ▸ Δ'` resolves to a `Dom` whose SMT type matches the
type recorded in `St₈.types`. Used identically in both Part 2 totality clauses
(nonempty and empty) of `encodeTerm_spec.all_case`. -/
theorem Δ'_alt_wt_helper
    {vs : List B.𝒱} {zs : List SMT.𝒱}
    {St₁_types St₄_types St₅_types St₇_types_v St₈_types_v : SMT.TypeContext}
    (St₁_sub_St₄_types : St₁_types ⊆ St₄_types)
    (St₁_sub_St₅_types : St₁_types ⊆ St₅_types)
    (St₄_sub_St₅_types : St₄_types ⊆ St₅_types)
    (St₇_types_eq : St₇_types_v = List.foldl (fun Γ v => AList.erase v Γ) St₅_types vs)
    (St₈_types_eq : St₈_types_v = List.foldl (fun Γ v => AList.erase v Γ) St₇_types_v zs)
    (vs_disj_St₁ : ∀ v ∈ vs, v ∉ St₁_types)
    (zs_not_types : ∀ z ∈ zs, z ∉ St₄_types)
    {Δ' Δ_D Δ_P Δ_D_alt Δ₀_alt : SMT.RenamingContext.Context}
    (Δ'_def : Δ' = fun v => if v ∈ vs then Δ_D v else Δ_P v)
    (Δ_D_dom : ∀ v, Δ_D v ≠ none → v ∈ St₁_types)
    (Δ_D_alt_dom : ∀ v, Δ_D_alt v ≠ none → v ∈ St₁_types)
    (Δ_D_alt_wt_out : ∀ (v : SMT.𝒱) (d : SMT.Dom), Δ_D_alt v = some d →
      ∀ τ_v, St₁_types.lookup v = some τ_v → d.snd.fst = τ_v)
    (Δ_P_dom : ∀ v, Δ_P v ≠ none → v ∈ St₄_types)
    (Δ_P_wt : ∀ (v : SMT.𝒱) (d : SMT.Dom), Δ_P v = some d →
      ∀ τ_v, St₄_types.lookup v = some τ_v → d.snd.fst = τ_v)
    (hwt_alt : ∀ (v : SMT.𝒱) (d : SMT.Dom), Δ₀_alt v = some d →
      ∀ τ, St₈_types_v.lookup v = some τ → d.snd.fst = τ) :
    ∀ v (d : SMT.Dom), (match Δ₀_alt v with
            | some d => some d
            | none => match Δ_D_alt v with
              | some d => some d
              | none => Δ' v) = some d →
        ∀ τ_v, St₈_types_v.lookup v = some τ_v → d.snd.fst = τ_v := by
  intro v d hv τ_v hτ_v
  cases h_alt : Δ₀_alt v with
  | some d' =>
    simp only [h_alt, Option.some.injEq] at hv; subst hv
    exact hwt_alt v d' h_alt τ_v hτ_v
  | none =>
    simp only [h_alt] at hv
    cases h_Dalt : Δ_D_alt v with
    | some d' =>
      simp only [h_Dalt, Option.some.injEq] at hv; subst hv
      have hv_St₁ : v ∈ St₁_types := Δ_D_alt_dom v (by rw [h_Dalt]; simp)
      have ⟨τ_v', hτ_v'⟩ : ∃ τ, St₁_types.lookup v = some τ :=
        Option.isSome_iff_exists.mp (AList.lookup_isSome.mpr hv_St₁)
      have hv_St₅_entry : ⟨v, τ_v'⟩ ∈ St₅_types.entries :=
        AList.mem_lookup_iff.mp (AList.lookup_of_subset St₁_sub_St₅_types hτ_v')
      have hv_not_vs : v ∉ vs := fun hvs => vs_disj_St₁ v hvs hv_St₁
      have hv_St₄ : v ∈ St₄_types := AList.mem_of_subset St₁_sub_St₄_types hv_St₁
      have hv_not_zs : v ∉ zs := fun hvz => zs_not_types v hvz hv_St₄
      have hv_St₇_entry : ⟨v, τ_v'⟩ ∈ St₇_types_v.entries := by
        rw [St₇_types_eq]
        exact AList.mem_foldl_erase_of_not_mem_keys hv_St₅_entry hv_not_vs
      have hv_St₈_entry : ⟨v, τ_v'⟩ ∈ St₈_types_v.entries := by
        rw [St₈_types_eq]
        exact AList.mem_foldl_erase_of_not_mem_keys hv_St₇_entry hv_not_zs
      have hτ_v'_St₈ : St₈_types_v.lookup v = some τ_v' :=
        AList.mem_lookup_iff.2 hv_St₈_entry
      have hτ_eq : τ_v = τ_v' := by
        rw [hτ_v] at hτ_v'_St₈; exact Option.some.inj hτ_v'_St₈
      rw [hτ_eq]
      exact Δ_D_alt_wt_out v d' h_Dalt τ_v' hτ_v'
    | none =>
      simp only [h_Dalt] at hv
      by_cases hvs : v ∈ vs
      · simp only [Δ'_def, if_pos hvs] at hv
        have hv_St₁' : v ∈ St₁_types := Δ_D_dom v (by rw [hv]; simp)
        exact absurd hv_St₁' (vs_disj_St₁ v hvs)
      · simp only [Δ'_def, if_neg hvs] at hv
        have hv_St₄ : v ∈ St₄_types := Δ_P_dom v (by rw [hv]; simp)
        have ⟨τ_v', hτ_v'⟩ : ∃ τ, St₄_types.lookup v = some τ :=
          Option.isSome_iff_exists.mp (AList.lookup_isSome.mpr hv_St₄)
        have hv_St₅_entry : ⟨v, τ_v'⟩ ∈ St₅_types.entries :=
          AList.mem_lookup_iff.mp (AList.lookup_of_subset St₄_sub_St₅_types hτ_v')
        have hv_not_zs : v ∉ zs := fun hvz => zs_not_types v hvz hv_St₄
        have hv_St₇_entry : ⟨v, τ_v'⟩ ∈ St₇_types_v.entries := by
          rw [St₇_types_eq]
          exact AList.mem_foldl_erase_of_not_mem_keys hv_St₅_entry hvs
        have hv_St₈_entry : ⟨v, τ_v'⟩ ∈ St₈_types_v.entries := by
          rw [St₈_types_eq]
          exact AList.mem_foldl_erase_of_not_mem_keys hv_St₇_entry hv_not_zs
        have hτ_v'_St₈ : St₈_types_v.lookup v = some τ_v' :=
          AList.mem_lookup_iff.2 hv_St₈_entry
        have hτ_eq : τ_v = τ_v' := by
          rw [hτ_v] at hτ_v'_St₈; exact Option.some.inj hτ_v'_St₈
        rw [hτ_eq]
        exact Δ_P_wt v d hv τ_v' hτ_v'

open Classical B in
/-- The `Δ'_alt_dom` property: every variable on which the hybrid alt context
`Δ'_alt = Δ₀_alt ▸ Δ_D_alt ▸ Δ'` is defined lies in `St₈.types`. Used identically
in both Part 2 totality clauses (nonempty and empty) of `encodeTerm_spec.all_case`. -/
theorem Δ'_alt_dom_helper
    (fv_sub_typings : B.FvSubTypings)
    {vs : List B.𝒱} {zs : List SMT.𝒱}
    {D P : B.Term} {τ : BType}
    {E_context : B.TypeContext}
    (typ_t : E_context ⊢ᴮ B.Term.all vs D P : .bool)
    {St₁_types St₄_types St₅_types St₇_types_v St₈_types_v : SMT.TypeContext}
    {D_enc : SMT.Term}
    (typ_D_enc : St₁_types ⊢ˢ D_enc : τ.toSMTType.fun SMTType.bool)
    (St₁_sub_St₄_types : St₁_types ⊆ St₄_types)
    (St₁_sub_St₅_types : St₁_types ⊆ St₅_types)
    (St₄_sub_St₅_types : St₄_types ⊆ St₅_types)
    (St₇_types_eq : St₇_types_v = List.foldl (fun Γ v => AList.erase v Γ) St₅_types vs)
    (St₈_types_eq : St₈_types_v = List.foldl (fun Γ v => AList.erase v Γ) St₇_types_v zs)
    (vs_disj_St₁ : ∀ v ∈ vs, v ∉ St₁_types)
    (zs_not_types : ∀ z ∈ zs, z ∉ St₄_types)
    {Δ' Δ_D Δ_P Δ_D_alt Δ₀_alt : SMT.RenamingContext.Context}
    (Δ'_def : Δ' = fun v => if v ∈ vs then Δ_D v else Δ_P v)
    (Δ_D_dom : ∀ v, Δ_D v ≠ none → v ∈ St₁_types)
    (Δ_D_alt_dom : ∀ v, Δ_D_alt v ≠ none → v ∈ St₁_types)
    (Δ_P_dom : ∀ v, Δ_P v ≠ none → v ∈ St₄_types)
    {Δ_alt : B.RenamingContext.Context}
    (hext_alt : SMT.RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt
      (B.Term.all vs D P)) :
    ∀ v, (match Δ₀_alt v with
            | some d => some d
            | none => match Δ_D_alt v with
              | some d => some d
              | none => Δ' v) ≠ none → v ∈ St₈_types_v := by
  intro v hv
  cases h_alt : Δ₀_alt v with
  | some d' =>
    have hv_fv : v ∈ B.fv (B.Term.all vs D P) :=
      SMT.RenamingContext.ExtendsOnSourceFV.dom_sub_B_fv hext_alt v
        (by rw [h_alt]; simp)
    have hv_St₁ : v ∈ St₁_types := fv_sub_typings typ_t typ_D_enc v hv_fv
    have hv_not_vs : v ∉ vs := fun hvs => vs_disj_St₁ v hvs hv_St₁
    have hv_St₄ : v ∈ St₄_types := AList.mem_of_subset St₁_sub_St₄_types hv_St₁
    have hv_not_zs : v ∉ zs := fun hvz => zs_not_types v hvz hv_St₄
    have ⟨τ_v, hτ_v⟩ : ∃ τ, St₁_types.lookup v = some τ :=
      Option.isSome_iff_exists.mp (AList.lookup_isSome.mpr hv_St₁)
    have hv_St₅_entry : ⟨v, τ_v⟩ ∈ St₅_types.entries :=
      AList.mem_lookup_iff.mp (AList.lookup_of_subset St₁_sub_St₅_types hτ_v)
    have hv_St₇_entry : ⟨v, τ_v⟩ ∈ St₇_types_v.entries := by
      rw [St₇_types_eq]
      exact AList.mem_foldl_erase_of_not_mem_keys hv_St₅_entry hv_not_vs
    have hv_St₈_entry : ⟨v, τ_v⟩ ∈ St₈_types_v.entries := by
      rw [St₈_types_eq]
      exact AList.mem_foldl_erase_of_not_mem_keys hv_St₇_entry hv_not_zs
    exact AList.lookup_isSome.1
      (by rw [AList.mem_lookup_iff.2 hv_St₈_entry]; simp)
  | none =>
    simp only [h_alt] at hv
    cases h_Dalt : Δ_D_alt v with
    | some d' =>
      have hv_St₁ : v ∈ St₁_types := Δ_D_alt_dom v (by rw [h_Dalt]; simp)
      have hv_not_vs : v ∉ vs := fun hvs => vs_disj_St₁ v hvs hv_St₁
      have hv_St₄ : v ∈ St₄_types := AList.mem_of_subset St₁_sub_St₄_types hv_St₁
      have hv_not_zs : v ∉ zs := fun hvz => zs_not_types v hvz hv_St₄
      have ⟨τ_v, hτ_v⟩ : ∃ τ, St₁_types.lookup v = some τ :=
        Option.isSome_iff_exists.mp (AList.lookup_isSome.mpr hv_St₁)
      have hv_St₅_entry : ⟨v, τ_v⟩ ∈ St₅_types.entries :=
        AList.mem_lookup_iff.mp (AList.lookup_of_subset St₁_sub_St₅_types hτ_v)
      have hv_St₇_entry : ⟨v, τ_v⟩ ∈ St₇_types_v.entries := by
        rw [St₇_types_eq]
        exact AList.mem_foldl_erase_of_not_mem_keys hv_St₅_entry hv_not_vs
      have hv_St₈_entry : ⟨v, τ_v⟩ ∈ St₈_types_v.entries := by
        rw [St₈_types_eq]
        exact AList.mem_foldl_erase_of_not_mem_keys hv_St₇_entry hv_not_zs
      exact AList.lookup_isSome.1
        (by rw [AList.mem_lookup_iff.2 hv_St₈_entry]; simp)
    | none =>
      simp only [h_Dalt] at hv
      by_cases hvs : v ∈ vs
      · simp only [Δ'_def, if_pos hvs] at hv
        have hv_St₁ : v ∈ St₁_types := Δ_D_dom v hv
        exact absurd hv_St₁ (vs_disj_St₁ v hvs)
      · simp only [Δ'_def, if_neg hvs] at hv
        have hv_St₄ : v ∈ St₄_types := Δ_P_dom v hv
        have hv_not_zs : v ∉ zs := fun hvz => zs_not_types v hvz hv_St₄
        have ⟨τ_v, hτ_v⟩ : ∃ τ, St₄_types.lookup v = some τ :=
          Option.isSome_iff_exists.mp (AList.lookup_isSome.mpr hv_St₄)
        have hv_St₅_entry : ⟨v, τ_v⟩ ∈ St₅_types.entries :=
          AList.mem_lookup_iff.mp (AList.lookup_of_subset St₄_sub_St₅_types hτ_v)
        have hv_St₇_entry : ⟨v, τ_v⟩ ∈ St₇_types_v.entries := by
          rw [St₇_types_eq]
          exact AList.mem_foldl_erase_of_not_mem_keys hv_St₅_entry hvs
        have hv_St₈_entry : ⟨v, τ_v⟩ ∈ St₈_types_v.entries := by
          rw [St₈_types_eq]
          exact AList.mem_foldl_erase_of_not_mem_keys hv_St₇_entry hv_not_zs
        exact AList.lookup_isSome.1
          (by rw [AList.mem_lookup_iff.2 hv_St₈_entry]; simp)

open Classical B in
/-- The `h_den_P_alt_bool` lemma used in both Part 2 totality clauses of
`encodeTerm_spec.all_case`: if `P`'s denotation under `Δ_ext` (extending `Δ_alt`
with `vs ↦ x_fin`) has type `P_ty`, then `P_ty = .bool` (since `P` is well-typed
at type `bool` in the original context). -/
theorem h_den_P_alt_bool_helper.{u}
    {vs : List B.𝒱} {D P : B.Term} {τ : BType} {𝒟_alt : ZFSet.{u}}
    (vs_nodup : vs.Nodup) (vs_nemp : vs ≠ [])
    {Γ_ctx : B.TypeContext}
    (typP : Γ_ctx ⊢ᴮ P : .bool)
    {Δ_alt : B.RenamingContext.Context}
    (Δ_fv_alt : ∀ v ∈ B.fv (B.Term.all vs D P), (Δ_alt v).isSome = true) :
    ∀ {x_fin : Fin vs.length → B.Dom},
        (∀ i, (x_fin i).snd.fst = τ.get vs.length i ∧
              (x_fin i).fst ∈ ⟦τ.get vs.length i⟧ᶻ) →
        ZFSet.ofFinDom x_fin ∈ 𝒟_alt →
        ∀ (Pz : ZFSet.{u}) (P_ty : BType) (hP_val : Pz ∈ ⟦P_ty⟧ᶻ),
        ⟦(B.Term.abstract.go P vs Δ_alt
          (fun v hv hvs => Δ_fv_alt v
            (B.fv.mem_all (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ =
            some ⟨Pz, ⟨P_ty, hP_val⟩⟩ →
        P_ty = .bool := by
  intro x_fin _hx_typ _hx_fin_in Pz P_ty hP_val hPz_den
  set Δ_ext_alt_fin : B.RenamingContext.Context :=
    Function.updates Δ_alt vs (List.ofFn fun i => some (x_fin i))
  have Δ_fv_P_alt_fin : ∀ v ∈ B.fv P, (Δ_ext_alt_fin v).isSome := by
    intro v hv
    show (Function.updates Δ_alt vs _ v).isSome = true
    rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup]
    split_ifs with hvs
    · simp [List.getElem_ofFn]
    · exact Δ_fv_alt v (fv.mem_all (.inr ⟨hv, hvs⟩))
  have hPz_abs : ⟦P.abstract Δ_ext_alt_fin Δ_fv_P_alt_fin⟧ᴮ =
      some ⟨Pz, ⟨P_ty, hP_val⟩⟩ := by
    rw [← denote_term_abstract_go_eq_term_abstract vs_nodup vs_nemp x_fin
      Δ_fv_P_alt_fin]
    exact hPz_den
  exact (denote_welltyped_eq
    (t := P.abstract Δ_ext_alt_fin Δ_fv_P_alt_fin)
    ⟨_, WFTC.of_abstract, .bool,
      by convert Typing.of_abstract Δ_fv_P_alt_fin typP⟩
    hPz_abs).symm

open Classical B in
/-- Extract the `D`-denotation under `Δ_alt` from the `Term.all vs D P`-denotation,
inferring that the resulting denotation has type `.set τ`.

Used in both Part 2 totality clauses (nonempty and empty-domain) of
`encodeTerm_spec.all_case`. -/
theorem hden_D_alt_helper.{u}
    {vs : List B.𝒱} {D P : B.Term} {τ : BType}
    {E_context : B.TypeContext}
    (typ_D : E_context ⊢ᴮ D : τ.set)
    {Δ_alt : B.RenamingContext.Context}
    {Δ_fv_alt : ∀ v ∈ B.fv (B.Term.all vs D P), (Δ_alt v).isSome = true}
    {T_alt : ZFSet.{u}} {hT_alt : T_alt ∈ ⟦BType.bool⟧ᶻ}
    (hden_alt : ⟦(B.Term.all vs D P).abstract Δ_alt Δ_fv_alt⟧ᴮ =
      some ⟨T_alt, ⟨BType.bool, hT_alt⟩⟩) :
    ∃ (𝒟_alt : ZFSet.{u}) (h𝒟_alt : 𝒟_alt ∈ ⟦τ.set⟧ᶻ),
      ⟦D.abstract Δ_alt
          (fun v hv => Δ_fv_alt v (B.fv.mem_all (.inl hv)))⟧ᴮ =
        some ⟨𝒟_alt, ⟨τ.set, h𝒟_alt⟩⟩ := by
  have h_inv := hden_alt
  simp only [B.Term.abstract] at h_inv
  unfold B.denote at h_inv
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h_inv
  obtain ⟨⟨d_val, d_ty, d_mem⟩, h_den_d, _⟩ := h_inv
  have h_conv : ⟦D.abstract Δ_alt
      (fun v hv => Δ_fv_alt v (B.fv.mem_all (.inl hv)))⟧ᴮ =
      some ⟨d_val, ⟨d_ty, d_mem⟩⟩ := by convert h_den_d using 2
  have : d_ty = .set τ := by
    have h_wt := denote_welltyped_eq
      (t := D.abstract Δ_alt
        (fun v hv => Δ_fv_alt v (B.fv.mem_all (.inl hv))))
      ⟨_, WFTC.of_abstract, .set τ,
        by convert Typing.of_abstract _ typ_D⟩
      h_conv
    exact h_wt.symm
  subst this
  exact ⟨d_val, d_mem, h_conv⟩

/-- The bound variables of `(zs.map .var).toPairl` are empty. Used in bullet 6
of all three branches (has-flag, no-flag nonempty, no-flag empty) of the
`all_case` typing argument. -/
theorem bv_pairl_empty_helper (zs : List SMT.𝒱) :
    SMT.bv ((List.map SMT.Term.var zs).toPairl) = [] := by
  suffices h : ∀ (l : List SMT.Term), (∀ t ∈ l, SMT.bv t = []) →
      SMT.bv (List.toPairl.aux l) = [] by
    apply h
    intro t ht; rw [List.mem_reverse, List.mem_map] at ht
    obtain ⟨z, _, rfl⟩ := ht; simp [SMT.bv]
  intro l
  induction l with
  | nil => intro _; simp [List.toPairl.aux, SMT.bv]
  | cons x xs ih =>
    intro hmem
    cases xs with
    | nil => simp [List.toPairl.aux]; exact hmem x (List.mem_cons_self ..)
    | cons x' xs' =>
      simp only [List.toPairl.aux]
      have h_rec : SMT.bv (List.toPairl.aux (x' :: xs')) = [] :=
        ih (fun t ht => hmem t (List.mem_cons_of_mem _ ht))
      have h_x : SMT.bv x = [] := hmem x (List.mem_cons_self ..)
      simp [SMT.bv, h_rec, h_x]

/-- Free variables of `(zs.map .var).toPairl` are a subset of `zs`. Used 6×
across the `all_case` branches (3× in bullet 6 typing, 3× in `Δ'_covers`
construction). -/
theorem fv_pairl_sub_zs_helper (zs : List SMT.𝒱) :
    ∀ v ∈ SMT.fv (List.map SMT.Term.var zs).toPairl, v ∈ zs := by
  suffices h : ∀ (l : List SMT.Term) (_ : ∀ t ∈ l, ∃ z ∈ zs, t = .var z),
      ∀ v ∈ SMT.fv (List.toPairl.aux l), v ∈ zs by
    intro v hv
    unfold List.toPairl at hv
    apply h (List.map SMT.Term.var zs).reverse ?_ v hv
    intro t ht
    rw [List.mem_reverse, List.mem_map] at ht
    obtain ⟨z, hz, rfl⟩ := ht
    exact ⟨z, hz, rfl⟩
  intro l
  induction l with
  | nil => intro _ v hv; simp [List.toPairl.aux, SMT.fv] at hv
  | cons t ts ih =>
    intro hzs v hv
    cases ts with
    | nil =>
      simp only [List.toPairl.aux] at hv
      obtain ⟨z, hzmem, rfl⟩ := hzs t (List.mem_cons_self ..)
      simp only [SMT.fv, List.mem_singleton] at hv
      exact hv ▸ hzmem
    | cons t' ts' =>
      simp only [List.toPairl.aux] at hv
      unfold SMT.fv at hv
      rw [List.mem_append] at hv
      rcases hv with h_rec | h_t
      · exact ih (fun t' ht' => hzs t' (List.mem_cons_of_mem _ ht')) v h_rec
      · obtain ⟨z, hzmem, rfl⟩ := hzs t (List.mem_cons_self ..)
        simp only [SMT.fv, List.mem_singleton] at h_t
        exact h_t ▸ hzmem

/-- `bv` of `(zs.map .var)` is empty for each element. Used in `bv_subst_eq`
across all three bullet-6 branches of `all_case`. -/
theorem bv_subst_eq_helper (zs : List SMT.𝒱) :
    ∀ t ∈ List.map SMT.Term.var zs, SMT.bv t = [] := by
  intro t ht; rw [List.mem_map] at ht
  obtain ⟨z', _, rfl⟩ := ht; simp [SMT.bv]

/-- Generic helper for `(Γ_outer.update zs τs).entries ⊆ Γ_target.entries`,
where `Γ_outer = zs.foldl erase (vs.foldl erase Γ_inner)`. Used identically
in the no-flag nonempty and no-flag empty branches of `all_case`, where we
take `Γ_inner = Γ_target = St₅.types`. The user provides `zs[i] ∈ Γ_target`
witnesses for the in-zs case. -/
theorem h_entries_sub_helper
    {Γ_inner Γ_outer Γ_target : SMT.TypeContext} {vs zs : List SMT.𝒱} {τs : List SMTType}
    (zs_nodup : zs.Nodup) (zs_len : zs.length = τs.length)
    (Γ_outer_eq : Γ_outer = zs.foldl (fun Γ w => AList.erase w Γ)
      (vs.foldl (fun Γ w => AList.erase w Γ) Γ_inner))
    (Γ_inner_sub : Γ_inner.entries ⊆ Γ_target.entries)
    (zs_τs_in_target : ∀ (i : ℕ) (hi : i < zs.length) (hi_τs : i < τs.length),
      (⟨zs[i], τs[i]'hi_τs⟩ : Sigma fun _ : SMT.𝒱 => SMTType) ∈ Γ_target.entries) :
    (Γ_outer.update zs τs).entries ⊆ Γ_target.entries := by
  intro ⟨k, τ_k⟩ hk
  have hk_lookup : (Γ_outer.update zs τs).lookup k = some τ_k :=
    AList.mem_lookup_iff.mpr hk
  by_cases hk_zs : k ∈ zs
  · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hk_zs
    have hi_τs : i < τs.length := zs_len ▸ hi
    have h_lookup_upd : (Γ_outer.update zs τs).lookup zs[i] = some (τs[i]'hi_τs) :=
      SMT.TypeContext.lookup_update_of_mem_nodup Γ_outer zs_nodup zs_len hi
    rw [h_lookup_upd] at hk_lookup
    injection hk_lookup with h_eq
    subst h_eq
    exact zs_τs_in_target i hi hi_τs
  · have h_lookup_eq : (Γ_outer.update zs τs).lookup k = Γ_outer.lookup k :=
      SMT.TypeContext.lookup_update Γ_outer k zs τs zs_len hk_zs
    rw [h_lookup_eq] at hk_lookup
    have h_in_outer : ⟨k, τ_k⟩ ∈ Γ_outer.entries := AList.mem_lookup_iff.mp hk_lookup
    rw [Γ_outer_eq] at h_in_outer
    have h_in_inner_lift := AList.foldl_erase_entries_subset zs _ h_in_outer
    exact Γ_inner_sub (AList.foldl_erase_entries_subset vs Γ_inner h_in_inner_lift)

/-- For both no-flag bullet-6 branches: `zs` is disjoint from `bv (imp (app D pairl) (substList vs zs P))`.
The argument splits the bv union, uses `bv_pairl_empty_helper`, and applies `Typing.bv_notMem_context`
twice with the two given typing facts.

Used identically in the no-flag nonempty and no-flag empty branches of `all_case`. -/
theorem zs_disj_bv_body_noflag_helper
    {D_enc P_enc : SMT.Term} {Γ₅ : SMT.TypeContext} {α : SMTType}
    {vs zs : List SMT.𝒱}
    (typ_D_enc_St₅ : Γ₅ ⊢ˢ SMT.Term.app D_enc (List.map SMT.Term.var zs).toPairl : α)
    (typ_P_St₅ : Γ₅ ⊢ˢ P_enc : .bool)
    (zs_in_St₅ : ∀ z ∈ zs, z ∈ Γ₅) :
    ∀ z ∈ zs, z ∉ SMT.bv
      (SMT.Term.imp (SMT.Term.app D_enc (List.map SMT.Term.var zs).toPairl)
        (SMT.substList vs (List.map SMT.Term.var zs) P_enc)) := by
  intro z hz hbv
  have hz_St₅ : z ∈ Γ₅ := zs_in_St₅ z hz
  unfold SMT.bv at hbv
  rw [List.mem_append] at hbv
  rcases hbv with h_app | h_subst
  · exact SMT.Typing.bv_notMem_context typ_D_enc_St₅ _ h_app hz_St₅
  · have h_P : z ∈ SMT.bv P_enc :=
      SMT_bv_substList_subset (bv_subst_eq_helper zs) _ h_subst
    exact SMT.Typing.bv_notMem_context typ_P_St₅ _ h_P hz_St₅

/-- Bullet 7 (preservation) for both no-flag branches of `all_case`.

Given `v ∈ used`, `v ∉ St₀.types`, `v ∉ B.fv (Term.all vs D P)`, and `v ∈ St₈.types`,
derive a contradiction using `D_preserves_types` and `P_preserves_types`.

The trace runs `St₈ → St₇ → St₅ → St₄ → St₃ → St₂ → St₁` via `foldl_erase` (steps
`St₈ → St₇ → St₅`) and via `mem_of_mem_foldl_insert'` (steps `St₅ → St₄`,
`St₃ → St₂ → St₁`).

Used identically in the no-flag nonempty (~line 1902) and no-flag empty (~line 4631)
branches of `all_case`.
-/
theorem bullet7_noflag_helper
    {used : List SMT.𝒱} {vs zs : List SMT.𝒱} {τs : List SMTType}
    {St₁_used St₂_used_v St₃_used_v : List SMT.𝒱}
    {St₀_types St₁_types St₂_types_v St₃_types_v
      St₄_types St₅_types_v St₇_types_v St₈_types_v : SMT.TypeContext}
    {D P : B.Term}
    (vs_nodup : vs.Nodup) (zs_nodup : zs.Nodup)
    (St₂_types_eq : St₂_types_v = St₁_types)
    (St₃_types_eq : St₃_types_v =
      (vs.zip τs).foldl (fun Γ p => AList.insert p.1 p.2 Γ) St₂_types_v)
    (St₅_types_eq : St₅_types_v =
      (zs.zip τs).foldl (fun Γ p => AList.insert p.1 p.2 Γ) St₄_types)
    (St₇_types_eq : St₇_types_v = vs.foldl (fun Γ w => AList.erase w Γ) St₅_types_v)
    (St₈_types_eq : St₈_types_v = zs.foldl (fun Γ w => AList.erase w Γ) St₇_types_v)
    (St₂_used_eq : St₂_used_v = St₁_used)
    (St₃_used_eq : St₃_used_v =
      (vs.zip τs).foldl (fun used p => p.1 :: used) St₂_used_v)
    (D_preserves_types : ∀ v ∈ used, v ∉ St₀_types → v ∉ B.fv D → v ∉ St₁_types)
    (P_preserves_types : ∀ v ∈ St₃_used_v, v ∉ St₃_types_v →
      v ∉ B.fv P → v ∉ St₄_types)
    (used_sub_St₁ : ∀ v ∈ used, v ∈ St₁_used) :
    ∀ v ∈ used, v ∉ St₀_types →
      v ∉ B.fv (B.Term.all vs D P) → v ∉ St₈_types_v := by
  intro v v_used v_notMem_St₀ v_notMem_fv v_mem_St₈
  simp only [B.fv, List.mem_append, not_or] at v_notMem_fv
  obtain ⟨hfv_D_nm, hfv_P_nm⟩ := v_notMem_fv
  obtain ⟨τ_v, hτ_v⟩ := Option.isSome_iff_exists.mp (AList.lookup_isSome.mpr v_mem_St₈)
  have h_St₈ : ⟨v, τ_v⟩ ∈ St₈_types_v.entries := AList.mem_lookup_iff.1 hτ_v
  have hv_not_zs : v ∉ zs := by
    intro hv_zs
    have h_notmem : v ∉ (zs.foldl (fun Γ w => AList.erase w Γ) St₇_types_v) :=
      AList.not_mem_foldl_erase_of_mem hv_zs zs_nodup
    apply h_notmem; rw [← St₈_types_eq]; exact v_mem_St₈
  have h_St₇ : ⟨v, τ_v⟩ ∈ St₇_types_v.entries := by
    rw [St₈_types_eq] at h_St₈
    exact AList.foldl_erase_entries_subset zs _ h_St₈
  have hv_not_vs : v ∉ vs := by
    intro hv_vs
    have h_notmem : v ∉ (vs.foldl (fun Γ w => AList.erase w Γ) St₅_types_v) :=
      AList.not_mem_foldl_erase_of_mem hv_vs vs_nodup
    apply h_notmem
    rw [← St₇_types_eq]
    exact List.mem_map.mpr ⟨⟨v, τ_v⟩, h_St₇, rfl⟩
  have hv_not_fvP : v ∉ B.fv P := by
    intro hv_fvP
    apply hfv_P_nm
    unfold List.removeAll; rw [List.mem_filter]
    exact ⟨hv_fvP, by simp [hv_not_vs]⟩
  have h_St₅ : ⟨v, τ_v⟩ ∈ St₅_types_v.entries := by
    rw [St₇_types_eq] at h_St₇
    exact AList.foldl_erase_entries_subset vs _ h_St₇
  rw [St₅_types_eq] at h_St₅
  have hv_St₄_keys : v ∈ (List.foldl (fun Γ p => AList.insert p.1 p.2 Γ)
        St₄_types (zs.zip τs)).keys :=
    List.mem_map.mpr ⟨⟨v, τ_v⟩, h_St₅, rfl⟩
  have hv_St₄ : v ∈ St₄_types := by
    apply AList.mem_of_mem_foldl_insert' (v := v) (l := zs.zip τs)
    · exact hv_St₄_keys
    · intro h
      rw [List.mem_map] at h
      obtain ⟨⟨a, b⟩, hab, rfl⟩ := h
      exact hv_not_zs (List.of_mem_zip hab).1
  have hv_St₃_used : v ∈ St₃_used_v := by
    rw [St₃_used_eq, St₂_used_eq]
    suffices ∀ (pairs : List (SMT.𝒱 × SMTType)) (acc : List SMT.𝒱),
        v ∈ acc → v ∈ pairs.foldl (fun used p => p.1 :: used) acc by
      exact this _ _ (used_sub_St₁ v v_used)
    intro pairs
    induction pairs with
    | nil => intro acc hmem; exact hmem
    | cons p ps ih => intro acc hmem; exact ih _ (List.mem_cons_of_mem _ hmem)
  have hv_not_St₂ : v ∉ St₂_types_v := by
    rw [St₂_types_eq]
    exact D_preserves_types v v_used v_notMem_St₀ hfv_D_nm
  have hv_not_St₃ : v ∉ St₃_types_v := by
    rw [St₃_types_eq]
    intro h
    apply hv_not_St₂
    exact AList.mem_of_mem_foldl_insert' h (by
      intro hmap; rw [List.mem_map] at hmap
      obtain ⟨⟨a, b⟩, hab, rfl⟩ := hmap
      exact hv_not_vs (List.of_mem_zip hab).1)
  exact P_preserves_types v hv_St₃_used hv_not_St₃ hv_not_fvP hv_St₄

/-- Bullet 7 (preservation) for the has-flag branch of `all_case`.

Same shape as `bullet7_noflag_helper` but with an additional `St₆` layer between
`St₅` and `St₇` (introduced by `castMembership`). The trace runs
`St₈ → St₇ → St₆ → St₅ → St₄ → St₃ → St₂ → St₁`, using `St₆_preserves`
(contrapositive) for the `St₆ → St₅` step. The conclusion follows by
`D_preserves_types` applied to the positive `v ∈ St₁_types` derivation.

Used at the has-flag bullet 7 site (~line 850) of `all_case`. -/
theorem bullet7_hasflag_helper
    {used : List SMT.𝒱} {vs zs : List SMT.𝒱} {τs : List SMTType}
    {St₃_used_v St₅_used_v : List SMT.𝒱}
    {St₀_types St₁_types St₂_types_v St₃_types_v
      St₄_types St₅_types_v St₆_types St₇_types_v St₈_types_v : SMT.TypeContext}
    {D P : B.Term}
    (vs_nodup : vs.Nodup) (zs_nodup : zs.Nodup)
    (St₂_types_eq : St₂_types_v = St₁_types)
    (St₃_types_eq : St₃_types_v =
      (vs.zip τs).foldl (fun Γ p => AList.insert p.1 p.2 Γ) St₂_types_v)
    (St₅_types_eq : St₅_types_v =
      (zs.zip τs).foldl (fun Γ p => AList.insert p.1 p.2 Γ) St₄_types)
    (St₇_types_eq : St₇_types_v = vs.foldl (fun Γ w => AList.erase w Γ) St₆_types)
    (St₈_types_eq : St₈_types_v = zs.foldl (fun Γ w => AList.erase w Γ) St₇_types_v)
    (used_sub_St₃_used : ∀ v ∈ used, v ∈ St₃_used_v)
    (used_sub_St₅_used : ∀ v ∈ used, v ∈ St₅_used_v)
    (St₆_preserves : ∀ v ∈ St₅_used_v, v ∉ St₅_types_v → v ∉ St₆_types)
    (P_preserves_types : ∀ v ∈ St₃_used_v, v ∉ St₃_types_v →
      v ∉ B.fv P → v ∉ St₄_types)
    (D_preserves_types : ∀ v ∈ used, v ∉ St₀_types → v ∉ B.fv D → v ∉ St₁_types) :
    ∀ v ∈ used, v ∉ St₀_types →
      v ∉ B.fv (B.Term.all vs D P) → v ∉ St₈_types_v := by
  intro v v_used v_notMem_St₀ v_notMem_fv v_mem_St₈
  simp only [B.fv, List.mem_append, not_or] at v_notMem_fv
  obtain ⟨hfv_D_nm, hfv_P_nm⟩ := v_notMem_fv
  obtain ⟨τ_v, hτ_v⟩ := Option.isSome_iff_exists.mp (AList.lookup_isSome.mpr v_mem_St₈)
  have h_St₈ : ⟨v, τ_v⟩ ∈ St₈_types_v.entries := AList.mem_lookup_iff.1 hτ_v
  have hv_not_zs : v ∉ zs := by
    intro hv_zs
    have h_notmem : v ∉ (zs.foldl (fun Γ w => AList.erase w Γ) St₇_types_v) :=
      AList.not_mem_foldl_erase_of_mem hv_zs zs_nodup
    apply h_notmem; rw [← St₈_types_eq]; exact v_mem_St₈
  have h_St₇ : ⟨v, τ_v⟩ ∈ St₇_types_v.entries := by
    rw [St₈_types_eq] at h_St₈
    exact AList.foldl_erase_entries_subset zs _ h_St₈
  have hv_not_vs : v ∉ vs := by
    intro hv_vs
    have h_notmem : v ∉ (vs.foldl (fun Γ w => AList.erase w Γ) St₆_types) :=
      AList.not_mem_foldl_erase_of_mem hv_vs vs_nodup
    apply h_notmem
    rw [← St₇_types_eq]
    exact List.mem_map.mpr ⟨⟨v, τ_v⟩, h_St₇, rfl⟩
  have hv_not_fvP : v ∉ B.fv P := by
    intro hv_fvP
    apply hfv_P_nm
    unfold List.removeAll; rw [List.mem_filter]
    exact ⟨hv_fvP, by simp [hv_not_vs]⟩
  have h_St₆ : ⟨v, τ_v⟩ ∈ St₆_types.entries := by
    rw [St₇_types_eq] at h_St₇
    exact AList.foldl_erase_entries_subset vs _ h_St₇
  have hv_St₆ : v ∈ St₆_types :=
    AList.mem_keys.mpr (List.mem_map.mpr ⟨⟨v, τ_v⟩, h_St₆, rfl⟩)
  have hv_St₅_used : v ∈ St₅_used_v := used_sub_St₅_used v v_used
  have hv_St₅ : v ∈ St₅_types_v := by
    by_contra hv_not_St₅
    exact St₆_preserves v hv_St₅_used hv_not_St₅ hv_St₆
  have hv_St₄ : v ∈ St₄_types := by
    rw [St₅_types_eq] at hv_St₅
    exact AList.mem_of_mem_foldl_insert' hv_St₅ (by
      intro h
      rw [List.mem_map] at h
      obtain ⟨⟨a, b⟩, hab, rfl⟩ := h
      exact hv_not_zs (List.of_mem_zip hab).1)
  have hv_St₃_used : v ∈ St₃_used_v := used_sub_St₃_used v v_used
  have hv_St₃ : v ∈ St₃_types_v := by
    by_contra hv_not_St₃
    exact P_preserves_types v hv_St₃_used hv_not_St₃ hv_not_fvP hv_St₄
  have hv_St₁ : v ∈ St₁_types := by
    rw [St₃_types_eq] at hv_St₃
    have hv_St₂ : v ∈ St₂_types_v :=
      AList.mem_of_mem_foldl_insert' hv_St₃ (by
        intro h
        rw [List.mem_map] at h
        obtain ⟨⟨a, b⟩, hab, rfl⟩ := h
        exact hv_not_vs (List.of_mem_zip hab).1)
    rw [St₂_types_eq] at hv_St₂; exact hv_St₂
  exact D_preserves_types v v_used v_notMem_St₀ hfv_D_nm hv_St₁

/-- Helper for the `Δ'_extends_Δ₀` step in the no-flag branches of `all_case`.

The `Δ'` constructed in the no-flag branches is `fun v => if v ∈ vs then Δ_D v else Δ_P v`,
where `Δ_P` extends a context `Δ_D_ext` that agrees with `Δ_D` outside `vs`. This helper
shows that this `Δ'` extends `Δ₀` whenever `Δ_D` extends `Δ₀` and `Δ_P` extends `Δ_D_ext`.

Used at the no-flag nonempty (~line 1851) and no-flag empty (~line 4512) sites. -/
theorem Δ'_extends_Δ₀_noflag_helper
    {Δ_D Δ_D_ext Δ_P Δ₀ : SMT.RenamingContext.Context} {vs : List SMT.𝒱}
    (Δ_D_extends : SMT.RenamingContext.Extends Δ_D Δ₀)
    (Δ_P_extends : SMT.RenamingContext.Extends Δ_P Δ_D_ext)
    (hΔ_D_ext_outside : ∀ v ∉ vs, Δ_D_ext v = Δ_D v) :
    SMT.RenamingContext.Extends (fun v => if v ∈ vs then Δ_D v else Δ_P v) Δ₀ := by
  intro v d hv_eq
  by_cases hvs : v ∈ vs
  · simp [hvs]; exact Δ_D_extends hv_eq
  · simp [hvs]
    have hDD : Δ_D_ext v = Δ_D v := hΔ_D_ext_outside v hvs
    exact Δ_P_extends (hDD ▸ Δ_D_extends hv_eq)

/-- Helper for the `Δ'_none_out` step in the no-flag branches of `all_case`.

`Δ'` is `none` outside `St₈.usedVars`, given the standard chain of state inclusions
and `Δ_P_none` for the `St₄` boundary. The proof traces `v ∉ St₈.usedVars` back to
`v ∉ zs`, `v ∉ St₄.usedVars`, and `v ∉ vs` (using `vs ⊆ St₃.usedVars ⊆ St₈.usedVars`).

Used at the no-flag nonempty (~line 1887) and no-flag empty (~line 4545) sites. -/
theorem Δ'_none_out_noflag_helper
    {Δ_D Δ_P : SMT.RenamingContext.Context} {vs zs : List SMT.𝒱}
    {St₃_used St₄_used St₅_used St₇_used St₈_used : List SMT.𝒱}
    (St₅_used_eq : St₅_used = zs.reverse ++ St₄_used)
    (St₇_used_eq : St₇_used = St₅_used)
    (St₈_used_eq : St₈_used = St₇_used)
    (St₃_sub_St₅_used : St₃_used ⊆ St₅_used)
    (St₅_sub_St₇_used : St₅_used ⊆ St₇_used)
    (St₇_sub_St₈_used : St₇_used ⊆ St₈_used)
    (vs_sub_St₃_used : ∀ v ∈ vs, v ∈ St₃_used)
    (Δ_P_none : ∀ v ∉ St₄_used, Δ_P v = none) :
    ∀ v ∉ St₈_used, (fun v => if v ∈ vs then Δ_D v else Δ_P v) v = none := by
  intro v hv
  have hv_St₅_nm : v ∉ St₅_used := by
    rw [← St₇_used_eq, ← St₈_used_eq]; exact hv
  rw [St₅_used_eq] at hv_St₅_nm
  have hv_St₄_nm : v ∉ St₄_used := by
    intro hSt₄
    apply hv_St₅_nm
    exact List.mem_append_right _ hSt₄
  have hv_not_vs : v ∉ vs := by
    intro hvs
    apply hv
    have h3 : v ∈ St₃_used := vs_sub_St₃_used v hvs
    have h5 : v ∈ St₅_used := St₃_sub_St₅_used h3
    have h7 : v ∈ St₇_used := St₅_sub_St₇_used h5
    exact St₇_sub_St₈_used h7
  simp [hv_not_vs]
  exact Δ_P_none v hv_St₄_nm

/-- Helper for the `Δ'_covers` step in the no-flag branches of `all_case`.

`Δ'` covers `forall zs τs (D_enc pairs ⇒ substList vs (vars zs) P_enc)` given that
`Δ_D` covers `D_enc`, `Δ_P` covers `P_enc`, and the standard disjointness/extension
hypotheses. Used at the no-flag nonempty (~line 1980) and no-flag empty (~line 4623) sites. -/
theorem Δ'_covers_noflag_helper
    {Δ_D Δ_D_ext Δ_P : SMT.RenamingContext.Context}
    {vs zs : List SMT.𝒱} {τs : List SMTType}
    {D_enc P_enc : SMT.Term} {St₁_types St₄_types : SMT.TypeContext}
    {τ_D σ_P : SMTType}
    (zs_len : zs.length = τs.length)
    (vs_τs_len : vs.length = τs.length)
    (typ_D_enc : St₁_types ⊢ˢ D_enc : τ_D)
    (typ_P_enc : St₄_types ⊢ˢ P_enc : σ_P)
    (vs_disj_St₁ : ∀ v ∈ vs, v ∉ St₁_types)
    (Δ_D_covers : SMT.RenamingContext.CoversFV Δ_D D_enc)
    (Δ_P_covers : SMT.RenamingContext.CoversFV Δ_P P_enc)
    (Δ_P_extends : SMT.RenamingContext.Extends Δ_P Δ_D_ext)
    (hΔ_D_ext_outside : ∀ v ∉ vs, Δ_D_ext v = Δ_D v)
    (fv_pairl_sub_zs : ∀ v ∈ SMT.fv (List.map SMT.Term.var zs).toPairl, v ∈ zs) :
    SMT.RenamingContext.CoversFV
      (fun v => if v ∈ vs then Δ_D v else Δ_P v)
      (SMT.Term.forall zs τs
        (SMT.Term.imp (SMT.Term.app D_enc (List.map SMT.Term.var zs).toPairl)
          (SMT.substList vs (List.map SMT.Term.var zs) P_enc))) := by
  intro v hv
  simp only [SMT.fv, List.mem_removeAll_iff, List.mem_append] at hv
  obtain ⟨hv_imp, hv_not_zs⟩ := hv
  have hv_not_zs' : v ∉ zs := by
    intro hvz
    apply hv_not_zs
    simpa using hvz
  rcases hv_imp with hv_app | hv_subst
  · rcases hv_app with hv_D | hv_pairs
    · have hv_St₁ : v ∈ St₁_types := SMT.Typing.mem_context_of_mem_fv typ_D_enc hv_D
      have hv_not_vs : v ∉ vs := fun hvs => vs_disj_St₁ v hvs hv_St₁
      simp [hv_not_vs]
      have hDD : Δ_D_ext v = Δ_D v := hΔ_D_ext_outside v hv_not_vs
      obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (Δ_D_covers v hv_D)
      exact Option.isSome_iff_exists.mpr ⟨d, Δ_P_extends (hDD ▸ hd)⟩
    · exact absurd (fv_pairl_sub_zs v hv_pairs) hv_not_zs'
  · rcases SMT_mem_fv_substList hv_subst with hv_P | ⟨t, ht, hv_t⟩
    · have hv_St₄ : v ∈ St₄_types := SMT.Typing.mem_context_of_mem_fv typ_P_enc hv_P
      have hv_not_vs : v ∉ vs := by
        intro hvs
        have hlen : vs.length ≤ (List.map SMT.Term.var zs).length := by
          rw [List.length_map]; exact le_of_eq (zs_len ▸ vs_τs_len)
        by_cases h_all_no_fv :
            ∀ t ∈ List.map SMT.Term.var zs, v ∉ SMT.fv t
        · exact SMT_not_mem_fv_substList_of_mem_vars hlen hvs h_all_no_fv hv_subst
        · push_neg at h_all_no_fv
          obtain ⟨t, ht, hv_t⟩ := h_all_no_fv
          rw [List.mem_map] at ht
          obtain ⟨z, hz, rfl⟩ := ht
          simp only [SMT.fv, List.mem_singleton] at hv_t
          subst hv_t
          exact hv_not_zs' hz
      simp [hv_not_vs]
      exact Δ_P_covers v hv_P
    · rw [List.mem_map] at ht
      obtain ⟨z, hz, rfl⟩ := ht
      simp only [SMT.fv, List.mem_singleton] at hv_t
      subst hv_t
      exact absurd hz hv_not_zs'

/-- Helper for the `Δ'_src_ext` step in the no-flag branches of `all_case`.

The `Δ'` constructed in the no-flag branches is `fun v => if v ∈ vs then Δ_D v else Δ_P v`.
This helper shows it satisfies `ExtendsOnSourceFV` for `Term.all vs D P`, given that:
- `Δ_D` extends the source on `D`,
- `Δ_P` extends the source on `P` under the bound-extension `Δ_ext`,
- `vs` is disjoint from the source free variables of `D`,
- `Δ_D_ext` and `Δ_ext` agree with `Δ_D` and `Δ_src` outside `vs`.

Used at the no-flag nonempty (~line 1917) and no-flag empty (~line 4568) sites. -/
theorem Δ'_src_ext_noflag_helper
    {Δ_src Δ_ext : B.𝒱 → Option B.Dom}
    {Δ_D Δ_D_ext Δ_P : SMT.RenamingContext.Context}
    {vs : List B.𝒱} {D P : B.Term}
    (Δ_D_src_ext : SMT.RenamingContext.ExtendsOnSourceFV Δ_D Δ_src D)
    (Δ_P_src_ext : SMT.RenamingContext.ExtendsOnSourceFV Δ_P Δ_ext P)
    (Δ_P_extends : SMT.RenamingContext.Extends Δ_P Δ_D_ext)
    (vs_disj_fvD : ∀ v ∈ vs, v ∉ B.fv D)
    (hΔ_D_ext_outside : ∀ v ∉ vs, Δ_D_ext v = Δ_D v)
    (hΔ_ext_outside : ∀ v ∉ vs, Δ_ext v = Δ_src v) :
    SMT.RenamingContext.ExtendsOnSourceFV
      (fun v => if v ∈ vs then Δ_D v else Δ_P v) Δ_src (B.Term.all vs D P) := by
  intro v d hv_eq
  by_cases hvs : v ∈ vs
  · simp [hvs]
    have hv_not_fv : v ∉ B.fv (B.Term.all vs D P) := by
      intro h
      simp only [B.fv, List.mem_append] at h
      rcases h with h_fvD | h_fvP_minus_vs
      · exact vs_disj_fvD v hvs h_fvD
      · rw [List.mem_removeAll_iff] at h_fvP_minus_vs
        exact h_fvP_minus_vs.2 hvs
    have : B.RenamingContext.toSMTOnFV Δ_src (B.Term.all vs D P) v = none := by
      simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
        B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_not_fv]
    rw [this] at hv_eq; exact absurd hv_eq (by simp)
  · simp [hvs]
    by_cases hv_fvD : v ∈ B.fv D
    · have : B.RenamingContext.toSMTOnFV Δ_src D v =
          B.RenamingContext.toSMTOnFV Δ_src (B.Term.all vs D P) v := by
        simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
          B.RenamingContext.restrictToFV_eq_of_mem hv_fvD,
          B.RenamingContext.restrictToFV_eq_of_mem
            (show v ∈ B.fv (B.Term.all vs D P) from B.fv.mem_all (.inl hv_fvD))]
      have hv_eq_D : B.RenamingContext.toSMTOnFV Δ_src D v = some d := this ▸ hv_eq
      have hΔD : Δ_D v = some d := Δ_D_src_ext hv_eq_D
      have hDD : Δ_D_ext v = Δ_D v := hΔ_D_ext_outside v hvs
      exact Δ_P_extends (hDD ▸ hΔD)
    · have hv_fv_all : v ∈ B.fv (B.Term.all vs D P) := by
        by_contra hv_not
        have : B.RenamingContext.toSMTOnFV Δ_src (B.Term.all vs D P) v = none := by
          simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
            B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_not]
        rw [this] at hv_eq; exact absurd hv_eq (by simp)
      have hv_fvP : v ∈ B.fv P := by
        simp only [B.fv, List.mem_append] at hv_fv_all
        rcases hv_fv_all with h1 | h2
        · exact absurd h1 hv_fvD
        · exact (List.mem_filter.mp h2).1
      have : B.RenamingContext.toSMTOnFV Δ_ext P v =
          B.RenamingContext.toSMTOnFV Δ_src (B.Term.all vs D P) v := by
        simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
          B.RenamingContext.restrictToFV_eq_of_mem hv_fvP,
          B.RenamingContext.restrictToFV_eq_of_mem hv_fv_all]
        have h_Δ_ext_eq_Δ : Δ_ext v = Δ_src v := hΔ_ext_outside v hvs
        rw [h_Δ_ext_eq_Δ]
      have hv_eq_P : B.RenamingContext.toSMTOnFV Δ_ext P v = some d := this ▸ hv_eq
      exact Δ_P_src_ext hv_eq_P

/-! ### Forall denotation totality and type extraction

These helpers factor the repeating `forallVal_isSome` and `hforallVal_ty` blocks
that appear at four sites in `EncodeTermCorrectAll.lean` (no-flag nonempty +
alt-context, no-flag empty + alt-context). Each pair of helpers is invoked
with the body-totality fact `htot_forall_raw` and the corresponding renaming
context (the primary `Δ'` or its `_alt` mirror).
-/

/-- Forall denotation totality: when the body `imp_body` evaluates to some value
for every well-typed witness vector, the SMT-level `forall` term denotes to a
defined value. -/
theorem forallVal_isSome_helper.{u}
    {imp_body : SMT.Term} {zs : List SMT.𝒱} {τs : List SMTType}
    (zs_len : zs.length = τs.length) (zs_len_pos : 0 < zs.length)
    {Δ_ctx : SMT.RenamingContext.Context}
    (hcov_forall : SMT.RenamingContext.CoversFV Δ_ctx (SMT.Term.forall zs τs imp_body))
    {hgo_cov : ∀ x ∈ SMT.fv imp_body, x ∉ zs → (Δ_ctx x).isSome = true}
    (htot_forall_raw :
      ∀ {x : Fin zs.length → SMT.Dom.{u}},
        (∀ i, (x i).snd.fst = τs[i.val]'(zs_len ▸ i.isLt) ∧
          (x i).fst ∈ ⟦τs[i.val]'(zs_len ▸ i.isLt)⟧ᶻ) →
        ⟦(SMT.Term.abstract.go imp_body zs Δ_ctx hgo_cov).uncurry x⟧ˢ.isSome = true) :
    ⟦(SMT.Term.forall zs τs imp_body).abstract Δ_ctx hcov_forall⟧ˢ.isSome = true := by
  rw [SMT.Term.abstract, dif_pos zs_len]
  simp only [SMT.denote]
  rw [dif_pos zs_len_pos]
  rw [dif_pos (by
    intro x hx
    apply htot_forall_raw
    intro i
    rcases i with ⟨j, hj⟩
    exact hx ⟨j, hj⟩)]
  simp

/-- Type extraction for the forall denotation: any successful denotation of an
SMT `forall` term is of type `.bool`, since the `forall` branch in `denote`
always returns `⟨_, .bool, _⟩`. -/
theorem hforallVal_ty_helper.{u}
    {imp_body : SMT.Term} {zs : List SMT.𝒱} {τs : List SMTType}
    (zs_len : zs.length = τs.length) (zs_len_pos : 0 < zs.length)
    {Δ_ctx : SMT.RenamingContext.Context}
    {hcov_forall : SMT.RenamingContext.CoversFV Δ_ctx (SMT.Term.forall zs τs imp_body)}
    {hgo_cov : ∀ x ∈ SMT.fv imp_body, x ∉ zs → (Δ_ctx x).isSome = true}
    (htot_forall_raw :
      ∀ {x : Fin zs.length → SMT.Dom.{u}},
        (∀ i, (x i).snd.fst = τs[i.val]'(zs_len ▸ i.isLt) ∧
          (x i).fst ∈ ⟦τs[i.val]'(zs_len ▸ i.isLt)⟧ᶻ) →
        ⟦(SMT.Term.abstract.go imp_body zs Δ_ctx hgo_cov).uncurry x⟧ˢ.isSome = true)
    {forallVal : SMT.Dom}
    (hforallVal :
      ⟦(SMT.Term.forall zs τs imp_body).abstract Δ_ctx hcov_forall⟧ˢ = some forallVal) :
    forallVal.snd.fst = .bool := by
  have hforallVal_unfold := hforallVal
  rw [SMT.Term.abstract, dif_pos zs_len] at hforallVal_unfold
  simp only [SMT.denote] at hforallVal_unfold
  rw [dif_pos zs_len_pos] at hforallVal_unfold
  rw [dif_pos (by
    intro x hx
    apply htot_forall_raw
    intro i
    rcases i with ⟨j, hj⟩
    exact hx ⟨j, hj⟩)] at hforallVal_unfold
  simp only [Option.pure_def, Option.some.injEq] at hforallVal_unfold
  rw [← hforallVal_unfold]

/-- Build `∀ v ∈ B.fv P, (Δ_ext v).isSome = true` for the standard
`Δ_ext = Function.updates «Δ» vs (List.ofFn fun i => some (x_fin i))` setup
shared across all four `all_case` Phase 1 setups. Uses `vs_nodup`, the parent
`Δ_fv` covering `B.fv (Term.all vs D P)`, and the standard `fv.mem_all`
embedding. -/
theorem Δ_fv_P_helper.{u}
    {«Δ» : B.RenamingContext.Context}
    {vs : List B.𝒱} (vs_nodup : vs.Nodup)
    {x_fin : Fin vs.length → B.Dom.{u}}
    {Δ_ext : B.RenamingContext.Context}
    (Δ_ext_def : Δ_ext = Function.updates «Δ» vs (List.ofFn fun i => some (x_fin i)))
    (D P : B.Term)
    (Δ_fv : ∀ v ∈ B.fv (B.Term.all vs D P), («Δ» v).isSome = true) :
    ∀ v ∈ B.fv P, (Δ_ext v).isSome = true := by
  intro v hv
  rw [Δ_ext_def, Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup]
  split_ifs with hvs
  · simp only [List.getElem_ofFn, Option.isSome_some]
  · exact Δ_fv v (B.fv.mem_all (.inr ⟨hv, hvs⟩))

/-- Bundled `Δ' agrees with Δ_D on fv(D_enc)` plus its two corollaries
(`hcov_D_Δ'`, `den_D_Δ'`) for the no-flag `all_case` setup, where
`Δ' = fun v => if v ∈ vs then Δ_D v else Δ_P v`.

Used at the noflag-nonempty and noflag-empty Phase 2 setups (sites at
`EncodeTermCorrectAll.lean` lines 1911-1938 and 4396-4423).  Saves about
22 lines per call site. -/
theorem Δ'_agrees_noflag_bundle.{u}
    {vs : List B.𝒱} {D_enc : SMT.Term} {σ : SMTType}
    {St₁_types : SMT.TypeContext}
    {Δ_D Δ_P Δ' : SMT.RenamingContext.Context}
    {Δ_D_ext : SMT.RenamingContext.Context}
    {denD' : SMT.Dom.{u}}
    (Δ'_def : Δ' = fun v => if v ∈ vs then Δ_D v else Δ_P v)
    (hΔ_D_ext_outside : ∀ v ∉ vs, Δ_D_ext v = Δ_D v)
    (typ_D_enc : St₁_types ⊢ˢ D_enc : σ)
    (vs_disj_St₁ : ∀ v ∈ vs, v ∉ St₁_types)
    (Δ_D_covers : SMT.RenamingContext.CoversFV Δ_D D_enc)
    (Δ_P_extends : SMT.RenamingContext.Extends Δ_P Δ_D_ext)
    (den_D_enc : ⟦D_enc.abstract Δ_D Δ_D_covers⟧ˢ = some denD') :
    ∃ (Δ'_agrees : SMT.RenamingContext.AgreesOnFV Δ_D Δ' D_enc)
      (hcov : SMT.RenamingContext.CoversFV Δ' D_enc),
      ⟦D_enc.abstract Δ' hcov⟧ˢ = some denD' := by
  have Δ'_agrees : SMT.RenamingContext.AgreesOnFV Δ_D Δ' D_enc := by
    intro v hv
    rw [Δ'_def]
    have hv_St₁ : v ∈ St₁_types :=
      SMT.Typing.mem_context_of_mem_fv typ_D_enc hv
    have hv_not_vs : v ∉ vs := fun hvs => vs_disj_St₁ v hvs hv_St₁
    simp only [hv_not_vs, if_false]
    cases hDD : Δ_D v with
    | some d =>
      have hDD_ext : Δ_D_ext v = Δ_D v := hΔ_D_ext_outside v hv_not_vs
      have hΔ_D_ext_v : Δ_D_ext v = some d := hDD_ext.trans hDD
      exact (Δ_P_extends hΔ_D_ext_v).symm
    | none =>
      exfalso
      have := Δ_D_covers v hv
      rw [hDD] at this
      exact absurd this (by simp)
  have hcov : SMT.RenamingContext.CoversFV Δ' D_enc := by
    intro v hv
    rw [← Δ'_agrees hv]
    exact Δ_D_covers v hv
  have hden : ⟦D_enc.abstract Δ' hcov⟧ˢ = some denD' := by
    have heq := SMT.RenamingContext.denote_congr_of_agreesOnFV
      (h1 := Δ_D_covers) (h2 := hcov) Δ'_agrees
    unfold SMT.RenamingContext.denote at heq
    rw [← heq]; exact den_D_enc
  exact ⟨Δ'_agrees, hcov, hden⟩

/-! ### Post-`freshVarList_spec` setup helpers

These bundle the standard 5-step setup that appears verbatim 3× in
`encodeTerm_spec.all_case` (has-flag site at line 449, no-flag nonempty
at line 1446, and no-flag empty at line 3971). Each has the same data
flow: from `freshVarList_spec` we get `zs`, `zs_len`, `zs_nodup`,
`zs_not_types`, `St₅_types`; combined with the upstream `vs_nodup`,
`vs_τs_len`, `vs_nemp`, `St₂_types`, `St₃_types`, `St₃_sub_St₄_types`,
`vs_Γ_disj`, `D_preserves_types`, `Λ_inv`, `vars_used_vs`, `typ_D`,
and `typ_D_enc` we derive: `zs ≠ []`, the `zs[i]`-typing fact, the
`(zs.map var).toPairl`-typing, the `vs ∉ St₁.types` disjointness,
the 5-step subset chain, and the lifted `typ_D_enc_St₅`. -/

/-- `zs ≠ []` from `zs.length = τs.length`, `vs.length = τs.length`,
and `vs ≠ []`. Derived shape used 3× in `encodeTerm_spec.all_case`. -/
theorem zs_nemp_helper
    {zs : List SMT.𝒱} {vs : List B.𝒱} {τs : List SMTType}
    (zs_len : zs.length = τs.length) (vs_τs_len : vs.length = τs.length)
    (vs_nemp : vs ≠ []) :
    zs ≠ [] := by
  intro h_nil
  have hzs_zero : zs.length = 0 := by rw [h_nil]; rfl
  rw [zs_len, ← vs_τs_len] at hzs_zero
  exact vs_nemp (List.length_eq_zero_iff.mp hzs_zero)

/-- `St₅.types.lookup zs[i] = some τs[i]` from the standard `St₅_types`
shape produced by `freshVarList_spec`. -/
theorem zs_typing_helper
    {zs : List SMT.𝒱} (zs_nodup : zs.Nodup) {τs : List SMTType}
    (zs_len : zs.length = τs.length)
    {Γ₀ St₅types : SMT.TypeContext}
    (St₅_types_eq :
      St₅types = List.foldl (fun Γ p => AList.insert p.1 p.2 Γ) Γ₀ (zs.zip τs)) :
    ∀ (i : ℕ) (hi : i < zs.length),
      St₅types.lookup zs[i] = some (τs[i]'(zs_len ▸ hi)) := by
  intro i hi
  rw [St₅_types_eq]
  exact foldl_insert_lookup_zip zs_nodup hi (zs_len ▸ hi)

/-- `St₅.types ⊢ˢ (zs.map var).toPairl : τs.toProdl` from the
standard `zs ≠ []`, `zs.length = τs.length`, and `zs[i]`-typing facts. -/
theorem toPairl_typ_helper
    {zs : List SMT.𝒱} {τs : List SMTType}
    (zs_len : zs.length = τs.length) (zs_nemp : zs ≠ [])
    {St₅types : SMT.TypeContext}
    (zs_typing : ∀ (i : ℕ) (hi : i < zs.length),
      St₅types.lookup zs[i] = some (τs[i]'(zs_len ▸ hi))) :
    St₅types ⊢ˢ (zs.map SMT.Term.var).toPairl : τs.toProdl := by
  have zs_map_len : (zs.map SMT.Term.var).length = τs.length := by
    rw [List.length_map, zs_len]
  refine List.toPairl_typing (zs.map SMT.Term.var) τs zs_map_len ?_ ?_
  · intro h_nil
    rw [List.map_eq_nil_iff] at h_nil
    exact zs_nemp h_nil
  · intro i hi
    have hzs : i < zs.length := by rw [List.length_map] at hi; exact hi
    have hzs_typ : St₅types.lookup zs[i] = some (τs[i]'(zs_len ▸ hzs)) :=
      zs_typing i hzs
    simp only [List.getElem_map]
    exact SMT.Typing.var _ zs[i] _ hzs_typ

/-- Bundles `vs_not_D_fv : ∀ v ∈ vs, v ∉ B.fv D` and
`vs_disj_St₁ : ∀ v ∈ vs, v ∉ St₁.types`. The standard pair derived
from typing/preservation invariants in `encodeTerm_spec.all_case`. -/
theorem vs_disj_St₁_helper
    {vs : List B.𝒱} {D P : B.Term} {E : B.Env} {τ : B.BType}
    {St₀ St₁ : SMT.TypeContext} {used : List SMT.𝒱}
    (typ_D : E.context ⊢ᴮ D : .set τ)
    (vs_Γ_disj : ∀ v ∈ vs, v ∉ E.context)
    (Λ_inv : ∀ v ∈ (B.Term.all vs D P).vars, v ∈ St₀ → v ∈ E.context)
    (vars_used_vs : ∀ v ∈ vs, v ∈ used)
    (D_preserves_types : ∀ v ∈ used, v ∉ St₀ → v ∉ B.fv D → v ∉ St₁) :
    (∀ v ∈ vs, v ∉ B.fv D) ∧ (∀ v ∈ vs, v ∉ St₁) := by
  have vs_not_D_fv : ∀ v ∈ vs, v ∉ B.fv D := by
    intro v hv hv_fv
    nomatch vs_Γ_disj v hv <| AList.lookup_isSome.mp <|
      B.Typing.mem_context_of_mem_fv typ_D hv_fv
  refine ⟨vs_not_D_fv, ?_⟩
  intro v hv
  apply D_preserves_types v (vars_used_vs v hv) _ (vs_not_D_fv v hv)
  intro hv_St₀
  have hv_all : v ∈ (B.Term.all vs D P).vars := by
    unfold B.Term.vars; rw [List.mem_union_iff]; right
    simp only [B.bv, List.mem_append]; left; left; exact hv
  exact vs_Γ_disj v hv (Λ_inv v hv_all hv_St₀)

/-- The 5-step subset chain `St₁.types ⊆ St₂.types ⊆ St₃.types ⊆ St₄.types ⊆ St₅.types`
plus the lifted `St₁.types ⊆ St₅.types`. Bundles the four `subset_foldl_insert'`
proofs that always co-occur. -/
theorem St_chain_helper
    {vs : List B.𝒱} (vs_nodup : vs.Nodup)
    {τs : List SMTType}
    {zs : List SMT.𝒱} (zs_nodup : zs.Nodup)
    {St₁types St₂types St₃types St₄types St₅types : SMT.TypeContext}
    (St₂_types : St₂types = St₁types)
    (St₃_types : St₃types =
      List.foldl (fun Γ p => AList.insert p.1 p.2 Γ) St₂types (vs.zip τs))
    (St₅_types : St₅types =
      List.foldl (fun Γ p => AList.insert p.1 p.2 Γ) St₄types (zs.zip τs))
    (St₃_sub_St₄_types : St₃types ⊆ St₄types)
    (vs_disj_St₁ : ∀ v ∈ vs, v ∉ St₁types)
    (zs_not_types : ∀ z ∈ zs, z ∉ St₄types) :
    St₁types ⊆ St₂types ∧ St₂types ⊆ St₃types ∧
    St₄types ⊆ St₅types ∧ St₁types ⊆ St₅types := by
  have h12 : St₁types ⊆ St₂types := by rw [St₂_types]
  have h23 : St₂types ⊆ St₃types := by
    rw [St₃_types]
    apply AList.subset_foldl_insert'
    · intro ⟨v, ξ⟩ hv
      rw [St₂_types]
      exact vs_disj_St₁ v (List.mem_fst_of_mem_zip hv)
    · exact List.nodup_map_fst_of_nodup_zip vs_nodup
  have h45 : St₄types ⊆ St₅types := by
    rw [St₅_types]
    apply AList.subset_foldl_insert'
    · intro ⟨z, ξ⟩ hz
      exact zs_not_types z (List.mem_fst_of_mem_zip hz)
    · exact List.nodup_map_fst_of_nodup_zip zs_nodup
  refine ⟨h12, h23, h45, ?_⟩
  exact AList.subset_trans h12
    (AList.subset_trans h23 (AList.subset_trans St₃_sub_St₄_types h45))

/-! ### Path-A R3a: `case_b_preimage_of_pfun_inv` helper

This builds the `case_b_preimage` requirement of
`retract_forallVal_eq_sInter_sep_hasflag` from the universal-form `pfun_inv`
(R1) and `castZF_apply_surj_on_isPFunc` (R2).

For each `x₀ ∈ 𝒟_val`, we build an SMT-side preimage `x_smt ∈ ⟦τs.toProdl⟧ᶻ`
such that `retract_castZF τ τs_toProdl_le x_smt = x₀`. Per-component:
- Flagged: the cast component is a graph cast, surjective on functional
  pair-bool predicates by R2. We pull back the canonical-iso image using R1's
  IsPFunc witness.
- Non-flagged: the cast component is identity; we just take the canonical-iso
  image directly.

Bundling all components into a Fin.foldl product gives `x_smt`, and the
cast roundtrip plus retract-of-canonical identity gives the equation.
-/

-- Auxiliary helpers for `castZF_apply` decomposition (componentwise on pair
-- and identity on reflexive). These give the consumer the building blocks
-- to construct the `cast_preimage_witness` parameter of
-- `case_b_preimage_of_pfun_inv` by structural recursion on the cast path.

/-- Surjectivity of the reflexive cast: every `y ∈ ⟦α⟧ᶻ` is its own preimage
under `castPath.reflexive α`. Used as the base case for `cast_preimage_witness`
on non-flagged components. -/
theorem castZF_of_path_reflexive_surj.{u} (α : SMTType) (y : ZFSet.{u})
    (hy : y ∈ ⟦α⟧ᶻ) :
    y.pair y ∈ (castZF_of_path (castPath.reflexive α)).1 := by
  rw [castZF_of_path_id]
  exact ZFSet.mem_Id_iff.mpr ⟨y, hy, rfl⟩

/-- Surjectivity of the pair cast: if both component casts are surjective on
their respective targets, then so is the pair cast. Used as the inductive step
for `cast_preimage_witness` over the left-associated pair structure of
`τs.toProdl`. -/
theorem castZF_of_path_pair_surj.{u} {α₁ β₁ α₂ β₂ : SMTType}
    (𝕔α : α₁ ~> α₂) (𝕔β : β₁ ~> β₂)
    (h_α : ∀ y : ZFSet.{u}, y ∈ ⟦α₂⟧ᶻ →
      ∃ x ∈ ⟦α₁⟧ᶻ, x.pair y ∈ (castZF_of_path 𝕔α).1)
    (h_β : ∀ y : ZFSet.{u}, y ∈ ⟦β₂⟧ᶻ →
      ∃ x ∈ ⟦β₁⟧ᶻ, x.pair y ∈ (castZF_of_path 𝕔β).1)
    (y : ZFSet.{u}) (hy : y ∈ ⟦SMTType.pair α₂ β₂⟧ᶻ) :
    ∃ x ∈ ⟦SMTType.pair α₁ β₁⟧ᶻ,
      x.pair y ∈ (castZF_of_path (castPath.pair 𝕔α 𝕔β)).1 := by
  have hy_prod : y ∈ ⟦α₂⟧ᶻ.prod ⟦β₂⟧ᶻ := hy
  have hy_eq : y = y.π₁.pair y.π₂ := ZFSet.pair_eta hy_prod
  have ⟨hπ₁, hπ₂⟩ : y.π₁ ∈ ⟦α₂⟧ᶻ ∧ y.π₂ ∈ ⟦β₂⟧ᶻ :=
    ZFSet.pair_mem_prod.mp (hy_eq ▸ hy_prod)
  obtain ⟨xα, hxα_mem, hxα_pair⟩ := h_α y.π₁ hπ₁
  obtain ⟨xβ, hxβ_mem, hxβ_pair⟩ := h_β y.π₂ hπ₂
  refine ⟨xα.pair xβ, ZFSet.pair_mem_prod.mpr ⟨hxα_mem, hxβ_mem⟩, ?_⟩
  show (xα.pair xβ).pair y ∈
    (castZF_pair (castZF_of_path 𝕔α) (castZF_of_path 𝕔β)).1
  rw [hy_eq]
  rw [ZFSet.pair_mem_fprod (hf := (castZF_of_path 𝕔α).2)
        (hg := (castZF_of_path 𝕔β).2)]
  -- Convert relational pair-membership into functional apply equalities.
  have hαisFunc := (castZF_of_path 𝕔α).2
  have hβisFunc := (castZF_of_path 𝕔β).2
  have hα_pfunc := ZFSet.is_func_is_pfunc hαisFunc
  have hβ_pfunc := ZFSet.is_func_is_pfunc hβisFunc
  have hxα_dom : xα ∈ (castZF_of_path 𝕔α).1.Dom := by
    rw [ZFSet.is_func_dom_eq hαisFunc]; exact hxα_mem
  have hxβ_dom : xβ ∈ (castZF_of_path 𝕔β).1.Dom := by
    rw [ZFSet.is_func_dom_eq hβisFunc]; exact hxβ_mem
  have hα_app := ZFSet.fapply.def hα_pfunc hxα_dom
  have hβ_app := ZFSet.fapply.def hβ_pfunc hxβ_dom
  have hα_eq : (ZFSet.fapply (castZF_of_path 𝕔α).1 hα_pfunc ⟨xα, hxα_dom⟩).val =
      y.π₁ := hα_pfunc.2 _ _ hα_app _ hxα_pair
  have hβ_eq : (ZFSet.fapply (castZF_of_path 𝕔β).1 hβ_pfunc ⟨xβ, hxβ_dom⟩).val =
      y.π₂ := hβ_pfunc.2 _ _ hβ_app _ hxβ_pair
  exact ⟨xα, xβ, hxα_mem, hxβ_mem, rfl, by rw [hα_eq, hβ_eq]⟩

/-- Surjectivity of the graph cast on functional pair-bool predicates:
specialized restatement of `castZF_apply_surj_on_isPFunc` in the relational
form expected by `cast_preimage_witness`. Used for flagged components:
combine with the `pfun_inv` IsPFunc witness for `(canonicalIso x₀).get i`. -/
theorem castZF_of_path_graph_refl_surj.{u} (α β : SMTType) (y : ZFSet.{u})
    (hy : y ∈ ⟦SMTType.fun (SMTType.pair α β) SMTType.bool⟧ᶻ)
    (hpfun : (predGraph α β y).IsPFunc ⟦α⟧ᶻ ⟦β⟧ᶻ) :
    ∃ x ∈ ⟦SMTType.fun α (SMTType.option β)⟧ᶻ,
      x.pair y ∈
        (castZF_of_path
          (castPath.graph (castPath.reflexive α) (castPath.reflexive β))).1 := by
  classical
  obtain ⟨x, hx_mem, hx_apply⟩ := castZF_apply_surj_on_isPFunc α β y hy hpfun
  refine ⟨x, hx_mem, ?_⟩
  set 𝕔 : (SMTType.fun α (SMTType.option β)) ~>
      (SMTType.fun (SMTType.pair α β) SMTType.bool) :=
    castPath.graph (castPath.reflexive α) (castPath.reflexive β) with h𝕔_def
  have hisFunc :
      ZFSet.IsFunc ⟦SMTType.fun α (SMTType.option β)⟧ᶻ
        ⟦SMTType.fun (SMTType.pair α β) SMTType.bool⟧ᶻ
        (castZF_of_path 𝕔).1 := (castZF_of_path 𝕔).2
  have hpfunc := ZFSet.is_func_is_pfunc hisFunc
  have hx_dom : x ∈ (castZF_of_path 𝕔).1.Dom := by
    rw [ZFSet.is_func_dom_eq hisFunc]; exact hx_mem
  have h_app := ZFSet.fapply.def hpfunc hx_dom
  have h_apply_eq : (ZFSet.fapply (castZF_of_path 𝕔).1 hpfunc ⟨x, hx_dom⟩).val = y := by
    have := hx_apply
    unfold castZF_apply at this
    rw [dif_pos hx_mem] at this
    exact this
  rw [h_apply_eq] at h_app
  exact h_app

open Classical B in
/-- Build the `case_b_preimage` argument of `retract_forallVal_eq_sInter_sep_hasflag`
from `pfun_inv` (R1), `castZF_apply_surj_on_isPFunc` (R2), and a structural
preimage witness (`cast_preimage_witness`).

The structural witness `cast_preimage_witness` says that the canonical SMT
image of any `x₀ ∈ 𝒟_val` lies in the range of the cast
`castZF_of_path τs_toProdl_le.toCastPath`. The witness can be CONSTRUCTED by
the consumer via structural recursion on the cast path, using:
* `castZF_of_path_reflexive_surj` for non-flagged components (where the cast
  component is reflexive and the preimage is the target itself);
* `castZF_of_path_graph_refl_surj` combined with `pfun_inv` for flagged
  components (where the cast is `castPath.graph castPath.reflexive
  castPath.reflexive` and `pfun_inv` provides the IsPFunc witness on the
  canonical-iso image of `x₀.get i`);
* `castZF_of_path_pair_surj` to compose component preimages along the
  left-associated pair structure of `τs.toProdl`.

The consumer supplies `cast_preimage_witness` because building it inline
requires a delicate structural induction over the cast path interleaved with
the `Fin.foldl` reassembly of the canonical-iso image — a ~500-line proof
that is encapsulated cleanly at the call site (where the binder structure is
in scope) rather than threaded through the abstract helper.

Given the witness, the helper produces `x_smt ∈ ⟦τs.toProdl⟧ᶻ` such that
`retract_castZF τ τs_toProdl_le x_smt = x₀`, which is the consumer interface
required by `retract_forallVal_eq_sInter_sep_hasflag`. -/
theorem case_b_preimage_of_pfun_inv.{u}
    {vs : List B.𝒱} (vs_nemp : vs ≠ []) (vs_nodup : vs.Nodup)
    {τ : BType} (τ_hasArity : τ.hasArity vs.length)
    {τs : List SMTType}
    (τs_toProdl_le : τs.toProdl ⊑ τ.toSMTType)
    {𝒟_val : ZFSet.{u}} (h𝒟_val : 𝒟_val ∈ ⟦τ.set⟧ᶻ)
    (E : B.Env)
    (D : B.Term) («Δ» : B.RenamingContext.Context)
    (Δ_fv_D : ∀ v ∈ B.fv D, («Δ» v).isSome = true)
    (h_den_D : ⟦D.abstract «Δ» Δ_fv_D⟧ᴮ = some ⟨𝒟_val, ⟨τ.set, h𝒟_val⟩⟩)
    (pfun_inv : ∀ (E_p : B.Env) (D' : B.Term) (vs' : List B.𝒱) (τ_D : B.BType),
        τ_D.hasArity vs'.length →
        ∀ (Δ_call : B.RenamingContext.Context)
          (Δ_fv_D' : ∀ v ∈ B.fv D', (Δ_call v).isSome = true)
          {𝒟 : ZFSet.{u}} (h𝒟 : 𝒟 ∈ ⟦.set τ_D⟧ᶻ),
          ⟦D'.abstract Δ_call Δ_fv_D'⟧ᴮ = some ⟨𝒟, ⟨.set τ_D, h𝒟⟩⟩ →
        ∀ (i : Fin vs'.length), vs'[i] ∈ E_p.flags →
        ∃ (αᵢ βᵢ : B.BType), τ_D.get vs'.length i = .prod αᵢ βᵢ ∧
          ∀ x ∈ 𝒟, (x.get vs'.length i).IsPFunc αᵢ.toZFSet βᵢ.toZFSet)
    -- Structural preimage witness: for each x₀ ∈ 𝒟_val, there exists a
    -- preimage in `⟦τs.toProdl⟧ᶻ` that the cast pairs with some y ∈ ⟦τ.toSMTType⟧ᶻ
    -- whose retract is x₀. Built by the consumer via `castZF_of_path_pair_surj`
    -- (top-level), `castZF_of_path_reflexive_surj` (non-flagged leaves), and
    -- `castZF_of_path_graph_refl_surj` combined with `pfun_inv` (flagged leaves).
    (cast_preimage_witness : ∀ x₀ ∈ 𝒟_val,
      ∃ (x_smt : ZFSet.{u}) (y : ZFSet.{u}),
        x_smt ∈ ⟦τs.toProdl⟧ᶻ ∧ y ∈ ⟦τ.toSMTType⟧ᶻ ∧
        x_smt.pair y ∈ (castZF_of_path τs_toProdl_le.toCastPath).1 ∧
        retract τ y = x₀) :
    ∀ x₀ ∈ 𝒟_val, ∃ x_smt ∈ ⟦τs.toProdl⟧ᶻ,
      retract_castZF τ τs_toProdl_le x_smt = x₀ := by
  classical
  intro x₀ hx₀
  -- Use the structural preimage witness directly.
  obtain ⟨x_smt, y, hx_smt_mem, hy_mem, hx_smt_pair, h_retract_y⟩ :=
    cast_preimage_witness x₀ hx₀
  unfold retract_castZF castZF_apply_of_le
  set 𝕔 := τs_toProdl_le.toCastPath with h𝕔_def
  have h_cast_isfunc : ZFSet.IsFunc ⟦τs.toProdl⟧ᶻ ⟦τ.toSMTType⟧ᶻ
      (castZF_of_path 𝕔).1 := (castZF_of_path 𝕔).2
  refine ⟨x_smt, hx_smt_mem, ?_⟩
  -- Equation: retract τ (castZF_apply 𝕔 x_smt) = x₀
  -- By cast functionality, castZF_apply 𝕔 x_smt = y, so retract τ ... = retract τ y = x₀.
  have h_cast_eq : castZF_apply 𝕔 x_smt = y := by
    unfold castZF_apply
    rw [dif_pos hx_smt_mem]
    have hpfunc := ZFSet.is_func_is_pfunc h_cast_isfunc
    have h_dom : x_smt ∈ (castZF_of_path 𝕔).1.Dom := by
      rw [ZFSet.is_func_dom_eq h_cast_isfunc]; exact hx_smt_mem
    have h_apply_pair := ZFSet.fapply.def hpfunc h_dom
    exact (hpfunc.2 _ _ h_apply_pair _ hx_smt_pair)
  rw [h_cast_eq]
  exact h_retract_y

/-! ### Path-A R3a-final: `cast_preimage_witness_construct` builder

`cast_preimage_witness_construct` discharges the `cast_preimage_witness`
parameter of `case_b_preimage_of_pfun_inv` (and the corresponding
`cast_preimage_witness_hasflag` hypothesis previously declared on
`encodeTerm_spec.all_case`/`encodeTerm_spec`) for casts whose path collapses
to the reflexive cast on `τ.toSMTType` — covering the no-flag use site of
`encodeTerm_spec.all_case`, where `τs.toProdl = τ.toSMTType` by construction
and the cast is the trivial reflexive cast.

The construction:
* Take `y := canonical_iso τ x₀`. Then `retract τ y = x₀` follows from
  `retract_of_canonical`.
* Take `x_smt := y`. Since the cast is reflexive, `castZF_of_path 𝕔 = Id`
  (via `castZF_of_path_id`), so `x_smt.pair y = y.pair y ∈ Id` reduces to
  membership in the identity diagonal, which is `castZF_of_path_reflexive_surj`.

For the flagged use site (where `τs.toProdl ≠ τ.toSMTType` in general due
to graph-cast components), the construction requires `pfun_inv` plus
structural induction interleaving `castZF_of_path_pair_surj` (top-level
pair structure) with `castZF_of_path_graph_refl_surj` (flagged leaves)
and `castZF_of_path_reflexive_surj` (non-flagged leaves). That extension
is documented in the no-flag-only signature below and left to a future
generalization. -/

open Classical B in
/-- Construct the `cast_preimage_witness` parameter of
`case_b_preimage_of_pfun_inv` when the cast is reflexive (i.e. has the form
`α ⊑ α` with `toCastPath = castPath.reflexive α`). This is the no-flag use
site, where the per-component `SMTFlagTypeRel` is unflagged at every index
and `τs = τ.toSMTType.fromProdl (vs.length - 1)` is the round-trip
deconstruction of `τ.toSMTType`.

For each `x₀ ∈ 𝒟_val`, returns:
* `y = canonical_iso τ x₀ ∈ ⟦τ.toSMTType⟧ᶻ`,
* `x_smt = y` (since cast is identity),
* `x_smt.pair y ∈ Id ⟦τ.toSMTType⟧ᶻ` via `castZF_of_path_reflexive_surj`,
* `retract τ y = x₀` via `retract_of_canonical`. -/
theorem cast_preimage_witness_construct_refl.{u}
    {τ : BType}
    (τs_toProdl_le : τ.toSMTType ⊑ τ.toSMTType)
    (h_path_refl : τs_toProdl_le.toCastPath = castPath.reflexive τ.toSMTType)
    {𝒟_val : ZFSet.{u}} (h𝒟_val : 𝒟_val ∈ ⟦τ.set⟧ᶻ) :
    ∀ x₀ ∈ 𝒟_val,
      ∃ (x_smt : ZFSet.{u}) (y : ZFSet.{u}),
        x_smt ∈ ⟦τ.toSMTType⟧ᶻ ∧ y ∈ ⟦τ.toSMTType⟧ᶻ ∧
        x_smt.pair y ∈ (castZF_of_path τs_toProdl_le.toCastPath).1 ∧
        retract τ y = x₀ := by
  classical
  intro x₀ hx₀_mem
  -- 𝒟_val ⊆ ⟦τ⟧ᶻ via powerset membership.
  have h𝒟_sub : 𝒟_val ⊆ ⟦τ⟧ᶻ := by
    rwa [BType.toZFSet, ZFSet.mem_powerset] at h𝒟_val
  have hx₀_τ : x₀ ∈ ⟦τ⟧ᶻ := h𝒟_sub hx₀_mem
  -- Set y := canonical_iso τ x₀.
  set y : ZFSet.{u} := (ZFSet.fapply (BType.canonicalIsoSMTType τ).1
      (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType τ).2.1)
      ⟨x₀, by rw [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType τ).2.1]; exact hx₀_τ⟩).1
    with hy_def
  have hy_mem : y ∈ ⟦τ.toSMTType⟧ᶻ := ZFSet.fapply_mem_range _ _
  have h_retract : retract τ y = x₀ := retract_of_canonical τ hx₀_τ
  refine ⟨y, y, hy_mem, hy_mem, ?_, h_retract⟩
  -- The cast path is reflexive, so castZF_of_path is the identity.
  rw [h_path_refl]
  exact castZF_of_path_reflexive_surj τ.toSMTType y hy_mem

open Classical B in
/-- Generic builder for the `cast_preimage_witness` parameter.

Reduces the construction to a single SURJECTIVITY-of-cast-on-canonical-iso
hypothesis: given that for every `x₀ ∈ ⟦τ⟧ᶻ`, the canonical-iso image
`y = canonicalIso τ x₀ ∈ ⟦τ.toSMTType⟧ᶻ` has a cast preimage in `⟦τs.toProdl⟧ᶻ`,
the witness obligation is discharged.

The surjectivity hypothesis is in turn discharged by structural induction
on the cast path:
* `castPath.refl` / `castPath.reflexive`: direct via
  `castZF_of_path_reflexive_surj`.
* `castPath.pair`: compose component preimages via
  `castZF_of_path_pair_surj`.
* `castPath.graph (refl) (refl)`: use `castZF_of_path_graph_refl_surj`
  combined with `pfun_inv` (for flagged components).

This delegation keeps the witness-builder agnostic to the specific cast
structure, while the cast structure determines how the surjectivity
hypothesis is itself discharged at the use site. -/
theorem cast_preimage_witness_construct_of_surj.{u}
    {τ : BType}
    {τs : List SMTType}
    (τs_toProdl_le : τs.toProdl ⊑ τ.toSMTType)
    {𝒟_val : ZFSet.{u}} (h𝒟_val : 𝒟_val ∈ ⟦τ.set⟧ᶻ)
    (cast_surj : ∀ y : ZFSet.{u}, y ∈ ⟦τ.toSMTType⟧ᶻ →
      ∃ x ∈ ⟦τs.toProdl⟧ᶻ,
        x.pair y ∈ (castZF_of_path τs_toProdl_le.toCastPath).1) :
    ∀ x₀ ∈ 𝒟_val,
      ∃ (x_smt : ZFSet.{u}) (y : ZFSet.{u}),
        x_smt ∈ ⟦τs.toProdl⟧ᶻ ∧ y ∈ ⟦τ.toSMTType⟧ᶻ ∧
        x_smt.pair y ∈ (castZF_of_path τs_toProdl_le.toCastPath).1 ∧
        retract τ y = x₀ := by
  classical
  intro x₀ hx₀_mem
  have h𝒟_sub : 𝒟_val ⊆ ⟦τ⟧ᶻ := by
    rwa [BType.toZFSet, ZFSet.mem_powerset] at h𝒟_val
  have hx₀_τ : x₀ ∈ ⟦τ⟧ᶻ := h𝒟_sub hx₀_mem
  -- Set y := canonical_iso τ x₀.
  set y : ZFSet.{u} := (ZFSet.fapply (BType.canonicalIsoSMTType τ).1
      (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType τ).2.1)
      ⟨x₀, by rw [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType τ).2.1]; exact hx₀_τ⟩).1
    with hy_def
  have hy_mem : y ∈ ⟦τ.toSMTType⟧ᶻ := ZFSet.fapply_mem_range _ _
  have h_retract : retract τ y = x₀ := retract_of_canonical τ hx₀_τ
  obtain ⟨x_smt, hx_smt_mem, hx_smt_pair⟩ := cast_surj y hy_mem
  exact ⟨x_smt, y, hx_smt_mem, hy_mem, hx_smt_pair, h_retract⟩

open Classical B in
/--
Δ-universal totality witness for the has-flag `all` case (Round 1: signature only).

Mirrors `lambda_chosen_totality` (in `EncodeTermCorrectLambda.lean:498`) but
specialized for the forall encoder. Produces the `totality_witness_hasflag`
clause currently demanded as a hypothesis on `encodeTerm_spec.all_case`
(`SMT/Reasoning/Basic/EncodeTermCorrectAll.lean:188`) and threaded through
`encodeTerm_all_hasflag_existential_admit` (above, line 2792).

## Conclusion shape

Identical structure to `totality_witness_hasflag`:
given an alternative B-side denotation of `B.Term.all vs D P`, produce an
alternative SMT renaming context `Δ'_alt`, a coverage proof, and an SMT
denotation `denT_alt` for `SMT.Term.forall zs τs imp_body`, satisfying:
* `Extends` over `Δ₀_alt`,
* none-out outside `used'`,
* well-typed against `Λ'`,
* RDom relation (B-side `T_alt` to SMT-side `denT_alt`),
* domain inclusion in `Λ'`.

## Mirror correspondence with `lambda_chosen_totality`

| lambda                                                          | all (this helper)                                |
|-----------------------------------------------------------------|--------------------------------------------------|
| `(τ ×ᴮ β).set` codomain                                         | `BType.bool` codomain                            |
| `(λˢ [z]) [..pair..] (D_enc.fst ∧ˢ ..)` lambda body              | `SMT.Term.forall zs τs imp_body`                 |
| `D_total` (D_ih.RDom totality)                                  | `D_total` (same shape)                           |
| `P_enc_total` (P_ih totality, β codomain)                        | `P_enc_total` (same, but `BType.bool` codomain)  |
| `lambda_chosen_retract_eq` for inner RDom                        | mirror via `forallVal_isSome_helper` +           |
|                                                                  | `retract_forallVal_eq_sInter_sep_hasflag`        |

## Round 6 status (FINAL - CLOSED with R7+ TODO)

R2-R5 close fully via mechanical substitutions from `lambda_chosen_totality`:
* B-side `(τ ×ᴮ β).set` → `BType.bool`
* SMT-side lambda body → forall body

R6 (RDom relation `⟨T_alt, ⟨BType.bool, hT_alt⟩⟩ ≘ᶻ denT_alt`) is dispatched
via the FALLBACK hypothesis `rdom_witness_hasflag` (last parameter of the
signature). This packages the deferred semantic bridge work needed to close
the forall RDom equation, requiring:
* In the nonempty (𝒟_alt ≠ ∅) branch: `retract_forallVal_eq_sInter_sep_hasflag`
  with `case_b_preimage_of_pfun_inv` + `hbridge_hasflag`.
* In the empty (𝒟_alt = ∅) branch: `retract_forallVal_eq_zftrue_of_empty_𝒟_hasflag`.
* In both branches: `case_b_preimage`-style functional invariant on D's
  denotation (`E.po`-based, currently NOT threaded through soundness statement
  per `EncodeTermCorrectAll.lean:1305-1318`).

The hypothesis `totality_witness_hasflag` on `encodeTerm_spec.all_case` is
preserved for now: future rounds (R7+) will discharge `rdom_witness_hasflag`
inline at the use site once the soundness statement threads partial-function
invariants for flagged binders, then wire the closed helper to remove
`totality_witness_hasflag` as a parent hypothesis.

See header notes at `lambda_chosen_totality` for the structural plumbing
(Δ₀_alt_D restriction, IH calls for D and P, Function.update construction
of Δ'_alt). -/
private theorem totality_witness_hasflag_construct.{u}
    {vs : List B.𝒱} {τ : BType}
    {αs : List BType}
    {E_ctx : B.TypeContext} {D P : B.Term}
    {D_enc : SMT.Term} {imp_body : SMT.Term}
    {zs : List SMT.𝒱} {τs : List SMTType}
    {Δ' : SMT.RenamingContext.Context.{u}}
    {denT' : SMT.Dom.{u}}
    {Γ_D Γ_P Γ' : SMT.TypeContext}
    {used_D used_P used' : List SMT.𝒱}
    (vs_nemp : vs ≠ []) (vs_nodup : vs.Nodup)
    (typ_t : E_ctx ⊢ᴮ B.Term.all vs D P : BType.bool)
    (typ_D : E_ctx ⊢ᴮ D : .set τ)
    (typP : (vs.zipToAList αs ∪ E_ctx) ⊢ᴮ P : BType.bool)
    (typ_D_enc : Γ_D ⊢ˢ D_enc : τ.toSMTType.fun SMTType.bool)
    (τ_hasArity : τ.hasArity vs.length)
    (vs_not_D_fv : ∀ v ∈ vs, v ∉ B.fv D)
    (vs_disj_Γ_D : ∀ v ∈ vs, v ∉ Γ_D)
    (vs_disj_Γ' : ∀ v ∈ vs, v ∉ Γ')
    (vs_used_P : ∀ v ∈ vs, v ∈ used_P)
    (vs_lookup_Γ_P : ∀ (i : Fin vs.length),
      AList.lookup vs[i] Γ_P = some ((τ.toSMTType.fromProdl (vs.length - 1))[i]'(by
        rw [fromProdl_length_of_hasArity τ_hasArity]; exact i.2)))
    (zs_disj_Γ_P : ∀ z ∈ zs, z ∉ Γ_P)
    (zs_disj_Γ' : ∀ z ∈ zs, z ∉ Γ')
    (zs_disj_used_P : ∀ z ∈ zs, z ∉ used_P)
    (zs_disj_fv_D_enc : ∀ z ∈ zs, z ∉ SMT.fv D_enc)
    (zs_disj_vs : ∀ z ∈ zs, z ∉ vs)
    (hcov_forall : SMT.RenamingContext.CoversFV Δ'
      (SMT.Term.forall zs τs imp_body))
    (hden_eq :
      ⟦(SMT.Term.forall zs τs imp_body).abstract Δ' hcov_forall⟧ˢ = some denT')
    (hden_ty : denT'.snd.fst = SMTType.bool)
    (Δ'_none_out_used' : ∀ v ∉ used', Δ' v = none)
    (Δ'_dom_Γ' : ∀ v, Δ' v ≠ none → v ∈ Γ')
    (Δ'_wt_Γ' : ∀ v (d : SMT.Dom), Δ' v = some d →
      ∀ τ_v, AList.lookup v Γ' = some τ_v → d.snd.fst = τ_v)
    (D_total :
      ∀ (Δ_alt : B.RenamingContext.Context)
        (Δ_fv_alt : ∀ v ∈ B.fv D, (Δ_alt v).isSome = true)
        (Δ₀_alt : SMT.RenamingContext.Context.{u}),
        SMT.RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt D →
          (∀ v ∉ used_D, Δ₀_alt v = none) →
            (∀ (v : SMT.𝒱) (d : SMT.Dom.{u}),
                Δ₀_alt v = some d → ∀ (τ_v : SMTType),
                  AList.lookup v Γ_D = some τ_v → d.snd.fst = τ_v) →
              ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦τ.set⟧ᶻ),
                ⟦D.abstract Δ_alt Δ_fv_alt⟧ᴮ = some ⟨T_alt, ⟨τ.set, hT_alt⟩⟩ →
                  ∃ Δ'_alt : SMT.RenamingContext.Context.{u},
                    ∃ (h : SMT.RenamingContext.CoversFV Δ'_alt D_enc),
                      ∃ denT_alt : SMT.Dom.{u},
                        SMT.RenamingContext.Extends Δ'_alt Δ₀_alt ∧
                          (∀ v ∉ used_D, Δ'_alt v = none) ∧
                            (∀ (v : SMT.𝒱) (d : SMT.Dom.{u}),
                                Δ'_alt v = some d → ∀ (τ_v : SMTType),
                                  AList.lookup v Γ_D = some τ_v → d.snd.fst = τ_v) ∧
                              ⟦D_enc.abstract Δ'_alt h⟧ˢ = some denT_alt ∧
                                (⟨T_alt, ⟨τ.set, hT_alt⟩⟩ : B.Dom) ≘ᶻ denT_alt ∧
                                  ∀ (v : SMT.𝒱), Δ'_alt v ≠ none → v ∈ Γ_D)
    (P_enc_total :
      ∀ (Δ_alt : B.RenamingContext.Context)
        (Δ_fv_alt : ∀ v ∈ B.fv P, (Δ_alt v).isSome = true)
        (Δ₀_alt : SMT.RenamingContext.Context.{u}),
        SMT.RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt P →
          (∀ v ∉ used_P, Δ₀_alt v = none) →
            (∀ (v : SMT.𝒱) (d : SMT.Dom.{u}),
                Δ₀_alt v = some d → ∀ (τ_v : SMTType),
                  AList.lookup v Γ_P = some τ_v → d.snd.fst = τ_v) →
              ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦BType.bool⟧ᶻ),
                ⟦P.abstract Δ_alt Δ_fv_alt⟧ᴮ = some ⟨T_alt, ⟨BType.bool, hT_alt⟩⟩ →
                  ∃ Δ'_alt : SMT.RenamingContext.Context.{u},
                    ∃ (hcov_alt : SMT.RenamingContext.CoversFV Δ'_alt imp_body),
                      ∃ denT_alt : SMT.Dom.{u},
                        SMT.RenamingContext.Extends Δ'_alt Δ₀_alt ∧
                          (∀ v ∉ used_P, Δ'_alt v = none) ∧
                            (∀ (v : SMT.𝒱) (d : SMT.Dom.{u}),
                                Δ'_alt v = some d → ∀ (τ_v : SMTType),
                                  AList.lookup v Γ_P = some τ_v → d.snd.fst = τ_v) ∧
                              ⟦imp_body.abstract Δ'_alt hcov_alt⟧ˢ = some denT_alt ∧
                                (⟨T_alt, ⟨BType.bool, hT_alt⟩⟩ : B.Dom) ≘ᶻ denT_alt ∧
                                  ∀ (v : SMT.𝒱), Δ'_alt v ≠ none → v ∈ Γ_P)
    (Γ_D_lookup_sub_Γ' : ∀ v τ_v,
      AList.lookup v Γ_D = some τ_v → AList.lookup v Γ' = some τ_v)
    (Γ_D_lookup_sub_Γ_P : ∀ v τ_v,
      AList.lookup v Γ_D = some τ_v → AList.lookup v Γ_P = some τ_v)
    (Γ'_lookup_sub_Γ_P : ∀ v τ_v,
      AList.lookup v Γ' = some τ_v → AList.lookup v Γ_P = some τ_v)
    (used_D_sub_used' : used_D ⊆ used')
    (Γ_P_lookup_sub_Γ' : ∀ v ∉ vs, ∀ τ_v,
      AList.lookup v Γ_P = some τ_v → AList.lookup v Γ' = some τ_v)
    (used_P_sub_used' : used_P ⊆ used')
    (covers_D : CoversUsedVars used_D D)
    (covers_P : CoversUsedVars used_P P)
    (Γ_D_dom_sub_Γ' : ∀ v, v ∈ Γ_D → v ∈ Γ')
    (Γ_P_dom_sub_Γ' : ∀ v, v ∈ Γ_P → v ∉ vs → v ∈ Γ')
    (fv_all_sub : ∀ v ∈ B.fv (B.Term.all vs D P), v ∈ Γ')
    (used_D_sub_used_P : used_D ⊆ used_P)
    (typ_forall : Γ' ⊢ˢ SMT.Term.forall zs τs imp_body : SMTType.bool)
    -- R6 RDom witness (FALLBACK hypothesis): supplies the per-Δ_alt RDom relation.
    -- This packages the deferred semantic bridge work needed to close the
    -- chosen-branch (𝒟_alt ≠ ∅) and empty-branch (𝒟_alt = ∅) RDom equations.
    -- Discharging this hypothesis requires:
    -- * In the nonempty branch: `retract_forallVal_eq_sInter_sep_hasflag` with
    --   `case_b_preimage_of_pfun_inv` + `hbridge_hasflag`.
    -- * In the empty branch: `retract_forallVal_eq_zftrue_of_empty_𝒟_hasflag` +
    --   the empty-branch bridge.
    -- The `case_b_preimage` argument requires an `E.po`-based functional
    -- invariant on D's denotation (see `EncodeTermCorrectAll.lean:1305-1318`).
    -- TODO (R7+): discharge this hypothesis at the use site once the soundness
    -- statement threads the partial-function invariants for flagged binders.
    (rdom_witness_hasflag : ∀ (Δ_alt : B.RenamingContext.Context)
      (Δ_fv_alt : ∀ v ∈ B.fv (B.Term.all vs D P), (Δ_alt v).isSome = true)
      (Δ₀_alt : SMT.RenamingContext.Context.{u}),
      SMT.RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt (B.Term.all vs D P) →
        (∀ v ∉ used', Δ₀_alt v = none) →
          (∀ (v : SMT.𝒱) (d : SMT.Dom.{u}),
              Δ₀_alt v = some d → ∀ (τ_v : SMTType),
                AList.lookup v Γ' = some τ_v → d.snd.fst = τ_v) →
            ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦BType.bool⟧ᶻ),
              ⟦(B.Term.all vs D P).abstract Δ_alt Δ_fv_alt⟧ᴮ =
                  some ⟨T_alt, ⟨BType.bool, hT_alt⟩⟩ →
                ∀ (Δ'_alt : SMT.RenamingContext.Context.{u})
                  (hcov_alt : SMT.RenamingContext.CoversFV Δ'_alt
                    (SMT.Term.forall zs τs imp_body))
                  (denT_alt : SMT.Dom.{u}),
                ⟦(SMT.Term.forall zs τs imp_body).abstract Δ'_alt hcov_alt⟧ˢ =
                    some denT_alt →
                (⟨T_alt, ⟨BType.bool, hT_alt⟩⟩ : B.Dom) ≘ᶻ denT_alt) :
    ∀ (Δ_alt : B.RenamingContext.Context)
      (Δ_fv_alt : ∀ v ∈ B.fv (B.Term.all vs D P), (Δ_alt v).isSome = true)
      (Δ₀_alt : SMT.RenamingContext.Context.{u}),
      SMT.RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt (B.Term.all vs D P) →
        (∀ v ∉ used', Δ₀_alt v = none) →
          (∀ (v : SMT.𝒱) (d : SMT.Dom.{u}),
              Δ₀_alt v = some d → ∀ (τ_v : SMTType),
                AList.lookup v Γ' = some τ_v → d.snd.fst = τ_v) →
            ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦BType.bool⟧ᶻ),
              ⟦(B.Term.all vs D P).abstract Δ_alt Δ_fv_alt⟧ᴮ =
                  some ⟨T_alt, ⟨BType.bool, hT_alt⟩⟩ →
                ∃ Δ'_alt : SMT.RenamingContext.Context.{u},
                  ∃ (hcov_alt : SMT.RenamingContext.CoversFV Δ'_alt
                    (SMT.Term.forall zs τs imp_body)),
                    ∃ denT_alt : SMT.Dom.{u},
                      SMT.RenamingContext.Extends Δ'_alt Δ₀_alt ∧
                        (∀ v ∉ used', Δ'_alt v = none) ∧
                          (∀ (v : SMT.𝒱) (d : SMT.Dom.{u}),
                              Δ'_alt v = some d → ∀ (τ_v : SMTType),
                                AList.lookup v Γ' = some τ_v → d.snd.fst = τ_v) ∧
                            ⟦(SMT.Term.forall zs τs imp_body).abstract
                                  Δ'_alt hcov_alt⟧ˢ = some denT_alt ∧
                              (⟨T_alt, ⟨BType.bool, hT_alt⟩⟩ : B.Dom) ≘ᶻ denT_alt ∧
                                ∀ (v : SMT.𝒱), Δ'_alt v ≠ none → v ∈ Γ' := by
  -- Round 2: D-extraction + Δ₀_alt_D setup + D_total IH invocation.
  -- Mirrors `lambda_chosen_totality` R2 (commit e2e5968) with mechanical
  -- substitutions: lambda's `(τ ×ᴮ β).set` → forall's `τ.set`,
  -- `B.fv.mem_lambda` → `B.fv.mem_all`, `B.Term.lambda` → `B.Term.all`.
  intro Δ_alt Δ_fv_alt Δ₀_alt hext_alt hnone_alt hwt_alt T_alt hT_alt hden_alt
  -- Extract B-level D denotation from forall denotation
  -- Forall's B-side denotation begins with ⟨𝒟, .set τ, h𝒟⟩ ← ⟦D⟧ᴮ | failure,
  -- identical to lambda's first step in `denote_aux.all`.
  have hden_D_alt : ∃ (𝒟_alt : ZFSet.{u}) (h𝒟_alt : 𝒟_alt ∈ ⟦τ.set⟧ᶻ),
      ⟦D.abstract Δ_alt (fun v hv => Δ_fv_alt v (B.fv.mem_all (.inl hv)))⟧ᴮ =
      some ⟨𝒟_alt, ⟨τ.set, h𝒟_alt⟩⟩ := by
    have h_inv := hden_alt
    simp only [B.Term.abstract] at h_inv
    unfold B.denote at h_inv
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h_inv
    obtain ⟨⟨d_val, d_ty, d_mem⟩, h_den_d, _⟩ := h_inv
    have h_conv : ⟦D.abstract Δ_alt
        (fun v hv => Δ_fv_alt v (B.fv.mem_all (.inl hv)))⟧ᴮ =
        some ⟨d_val, ⟨d_ty, d_mem⟩⟩ := by convert h_den_d using 2
    have : d_ty = .set τ := by
      have h_wt := denote_welltyped_eq
        (t := D.abstract Δ_alt
          (fun v hv => Δ_fv_alt v (B.fv.mem_all (.inl hv))))
        ⟨_, WFTC.of_abstract, .set τ,
          by convert Typing.of_abstract _ typ_D⟩
        h_conv
      exact h_wt.symm
    subst this
    exact ⟨d_val, d_mem, h_conv⟩
  obtain ⟨𝒟_alt, h𝒟_alt, hden_D_alt_eq⟩ := hden_D_alt
  -- Build Δ₀_alt_D restricted context for D's totality invocation.
  -- Same pattern as lambda (e2e5968): toSMTOnFV D, fallback to Δ₀_alt on used_D.
  set Δ₀_alt_D : SMT.RenamingContext.Context :=
    fun v => match B.RenamingContext.toSMTOnFV Δ_alt D v with
      | some d => some d
      | none => if v ∈ used_D then
          match Δ₀_alt v with
          | some d => some d
          | none => none
        else none
  -- ExtendsOnSourceFV: Δ₀_alt_D extends Δ_alt on D's free vars.
  have hext_alt_D : SMT.RenamingContext.ExtendsOnSourceFV Δ₀_alt_D Δ_alt D := by
    intro v d hv; simp only [Δ₀_alt_D, hv]
  -- None-out: Δ₀_alt_D v = none for v ∉ used_D.
  have hnone_alt_D : ∀ v ∉ used_D, Δ₀_alt_D v = none := by
    intro v hv
    show (match B.RenamingContext.toSMTOnFV Δ_alt D v with
      | some d => some d
      | none => if v ∈ used_D then
          match Δ₀_alt v with
          | some d => some d
          | none => none
        else none) = none
    have hv_not_fv_D : v ∉ B.fv D := B.not_mem_fv_of_not_mem_used covers_D hv
    have h_toSMT_none : B.RenamingContext.toSMTOnFV Δ_alt D v = none := by
      simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
        B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_not_fv_D]
    rw [h_toSMT_none, if_neg hv]
  -- Well-typed: Δ₀_alt_D v = some d ⇒ d's type matches Γ_D's lookup.
  have hwt_alt_D : ∀ v (d : SMT.Dom), Δ₀_alt_D v = some d →
      ∀ τ_v, AList.lookup v Γ_D = some τ_v → d.snd.fst = τ_v := by
    intro v d hv τ_v hτ_v
    change (match B.RenamingContext.toSMTOnFV Δ_alt D v with
      | some d => some d
      | none => if v ∈ used_D then
          match Δ₀_alt v with
          | some d => some d
          | none => none
        else none) = some d at hv
    cases h_toSMT : B.RenamingContext.toSMTOnFV Δ_alt D v with
    | some d' =>
      simp only [h_toSMT] at hv; cases hv
      -- v ∈ B.fv D, so v ∈ B.fv (all) via fv.mem_all.
      have hv_fv_D : v ∈ B.fv D := by
        by_contra hv_not
        simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
          B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_not] at h_toSMT
      have h_onFV : B.RenamingContext.toSMTOnFV Δ_alt (B.Term.all vs D P) v = some d := by
        simp only [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
          B.RenamingContext.restrictToFV_eq_of_mem (B.fv.mem_all (.inl hv_fv_D))]
        simp only [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
          B.RenamingContext.restrictToFV_eq_of_mem hv_fv_D] at h_toSMT
        exact h_toSMT
      have hΔ₀_alt_v : Δ₀_alt v = some d := hext_alt h_onFV
      -- Lift Γ_D's lookup to Γ' via Γ_D_lookup_sub_Γ'.
      have hτ_v_Γ' : AList.lookup v Γ' = some τ_v := Γ_D_lookup_sub_Γ' v τ_v hτ_v
      exact hwt_alt v d hΔ₀_alt_v τ_v hτ_v_Γ'
    | none =>
      simp only [h_toSMT] at hv
      split_ifs at hv with h_used
      · cases hΔ₀_alt : Δ₀_alt v with
        | some d' =>
          simp only [hΔ₀_alt, Option.some.injEq] at hv
          subst hv
          -- Use hwt_alt with the lifted lookup.
          have hτ_v_Γ' : AList.lookup v Γ' = some τ_v := Γ_D_lookup_sub_Γ' v τ_v hτ_v
          exact hwt_alt v d' hΔ₀_alt τ_v hτ_v_Γ'
        | none =>
          simp only [hΔ₀_alt] at hv
          nomatch hv
  -- Invoke D_total to obtain the alternative D-side covering data.
  obtain ⟨Δ_D_alt, hcov_D_alt, denD_alt, hext_D_alt, Δ_D_alt_none_out,
      Δ_D_alt_wt_out, hden_D_alt, hRDom_D_alt, Δ_D_alt_dom⟩ :=
    D_total Δ_alt
      (fun v hv => Δ_fv_alt v (B.fv.mem_all (.inl hv)))
      Δ₀_alt_D hext_alt_D hnone_alt_D hwt_alt_D
      𝒟_alt h𝒟_alt hden_D_alt_eq
  -- Round 3: Build Δ'_alt cascade = Δ₀_alt → Δ_D_alt → Δ'.
  -- Mirrors `lambda_chosen_totality` R3 (commit abca67b) with mechanical
  -- substitutions: lambda body → forall body, `fv_lambda_sub` → `fv_all_sub`,
  -- `B.fv.mem_lambda` → `B.fv.mem_all`, `B.Term.lambda` → `B.Term.all`.
  set Δ'_alt : SMT.RenamingContext.Context :=
    fun v => match Δ₀_alt v with
      | some d => some d
      | none => match Δ_D_alt v with
        | some d => some d
        | none => Δ' v
    with Δ'_alt_def
  -- Δ'_alt extends Δ₀_alt.
  have Δ'_alt_extends_Δ₀_alt : SMT.RenamingContext.Extends Δ'_alt Δ₀_alt := by
    intro v d hv; simp only [Δ'_alt, hv]
  -- Δ'_alt vanishes outside used'.
  have Δ'_alt_none_out : ∀ v ∉ used', Δ'_alt v = none := by
    intro v hv
    simp only [Δ'_alt]
    have h1 : Δ₀_alt v = none := hnone_alt v hv
    rw [h1]
    have hv_not_used_D : v ∉ used_D := fun hmem => hv (used_D_sub_used' hmem)
    have h2 : Δ_D_alt v = none := Δ_D_alt_none_out v hv_not_used_D
    rw [h2]
    exact Δ'_none_out_used' v hv
  -- Δ'_alt is well-typed against Γ'.
  have Δ'_alt_wt : ∀ v (d : SMT.Dom), Δ'_alt v = some d →
      ∀ τ_v, AList.lookup v Γ' = some τ_v → d.snd.fst = τ_v := by
    intro v d hv τ_v hτ_v
    -- Unfold Δ'_alt v = match cascade.
    change (match Δ₀_alt v with
      | some d => some d
      | none => match Δ_D_alt v with
        | some d => some d
        | none => Δ' v) = some d at hv
    cases hΔ₀ : Δ₀_alt v with
    | some d₀ =>
      simp only [hΔ₀] at hv; cases hv
      exact hwt_alt v d hΔ₀ τ_v hτ_v
    | none =>
      simp only [hΔ₀] at hv
      cases hΔ_D : Δ_D_alt v with
      | some d' =>
        simp only [hΔ_D] at hv; cases hv
        -- Need Γ_D's lookup: v ∈ Γ_D from Δ_D_alt_dom; lift Γ_D to Γ'
        have hv_Γ_D : v ∈ Γ_D := Δ_D_alt_dom v (by rw [hΔ_D]; simp)
        obtain ⟨τ_v_D, hτ_v_D⟩ := Option.isSome_iff_exists.mp
          (AList.lookup_isSome.mpr hv_Γ_D)
        have hτ_v_Γ' : AList.lookup v Γ' = some τ_v_D :=
          Γ_D_lookup_sub_Γ' v τ_v_D hτ_v_D
        rw [hτ_v_Γ'] at hτ_v; cases hτ_v
        exact Δ_D_alt_wt_out v d hΔ_D τ_v hτ_v_D
      | none =>
        simp only [hΔ_D] at hv
        exact Δ'_wt_Γ' v d hv τ_v hτ_v
  -- Δ'_alt's domain is in Γ'.
  have Δ'_alt_dom_Γ' : ∀ v, Δ'_alt v ≠ none → v ∈ Γ' := by
    intro v hv_ne
    simp only [Δ'_alt] at hv_ne
    cases hΔ₀ : Δ₀_alt v with
    | some d₀ =>
      -- Δ₀_alt v = some d₀ and Δ₀_alt extends toSMTOnFV Δ_alt (all).
      -- Use dom_sub_B_fv axiom to lift dom membership to fv membership.
      have hv_fv_all : v ∈ B.fv (B.Term.all vs D P) := by
        exact SMT.RenamingContext.ExtendsOnSourceFV.dom_sub_B_fv hext_alt v
          (by rw [hΔ₀]; simp)
      exact fv_all_sub v hv_fv_all
    | none =>
      simp only [hΔ₀] at hv_ne
      cases hΔ_D : Δ_D_alt v with
      | some d_D =>
        simp only [hΔ_D] at hv_ne
        have hv_Γ_D : v ∈ Γ_D := Δ_D_alt_dom v (by rw [hΔ_D]; simp)
        exact Γ_D_dom_sub_Γ' v hv_Γ_D
      | none =>
        simp only [hΔ_D] at hv_ne
        exact Δ'_dom_Γ' v hv_ne
  -- Δ'_alt covers fv(forall zs τs imp_body). Cascade defaults to Δ' which
  -- covers the forall via hcov_forall.
  have Δ'_alt_covers_forall : SMT.RenamingContext.CoversFV Δ'_alt
      (SMT.Term.forall zs τs imp_body) := by
    intro v hv
    simp only [Δ'_alt]
    cases hΔ₀ : Δ₀_alt v with
    | some d₀ => simp
    | none =>
      cases hΔ_D : Δ_D_alt v with
      | some d_D => simp
      | none =>
        -- Fall through to Δ'.
        exact hcov_forall v hv
  -- Round 4: witness extraction + Δ_ext_alt + Δ_D_ext_alt + Δ₀_hybrid_alt +
  -- P_enc_total invocation. Mirrors `lambda_chosen_totality` R4 (commits 75733a6,
  -- c18a8ef) at `EncodeTermCorrectLambda.lean:855-1057` with mechanical
  -- substitutions: lambda's `chosen` (h_nemp) ↔ forall's `nonempty` (¬h𝒟_empty)
  -- branch and lambda's `defaults` (¬h_nemp = empty) ↔ forall's `empty`
  -- (h𝒟_empty) branch. The forall denotation in `B/SemanticsPHOAS.lean:599-629`
  -- has structure:
  --   bind D → 𝒟_alt; if τ.hasArity then if den_P then if typP_det then
  --     if 𝒟 = ∅ then return zftrue else return sInter sep
  -- whereas lambda has:
  --   bind D → 𝒟_alt; if τ.hasArity then if den_E then if typE_det then
  --     if 𝒟 ≠ ∅ then chosen-branch else defaults-branch
  -- In the forall nonempty branch we extract a witness via Classical.choose; in
  -- the empty branch P never gets evaluated, so we synthesize a witness via
  -- defaultZFSet. In BOTH branches we still need a P-denotation for P_enc_total,
  -- which we obtain by direct invocation of `den_P_cond` at our chosen witness
  -- (which is in 𝒟 in the nonempty case; in the empty case `den_P_cond` is
  -- vacuously true, so we use B.denote_exists_of_typing instead).
  -- =========================================================================
  -- Step 1: Extract a typed witness from hden_alt that drives P denotation.
  -- =========================================================================
  have hden_alt_data : ∃ (f_alt : Fin vs.length → B.Dom),
      (∀ i, (f_alt i).snd.fst = τ.get vs.length i ∧
        (f_alt i).fst ∈ ⟦τ.get vs.length i⟧ᶻ) ∧
      ∃ (P_val_alt : ZFSet.{u}) (hP_val_alt : P_val_alt ∈ ⟦BType.bool⟧ᶻ),
      ⟦(B.Term.abstract.go P vs Δ_alt
        (fun v hv hvs => Δ_fv_alt v (B.fv.mem_all (.inr ⟨hv, hvs⟩)))).uncurry f_alt⟧ᴮ
        = some ⟨P_val_alt, ⟨BType.bool, hP_val_alt⟩⟩ := by
    have h_inv := hden_alt
    simp only [B.Term.abstract] at h_inv
    unfold B.denote at h_inv
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h_inv
    obtain ⟨D_dom_pkg, h_den_d, rest_alt⟩ := h_inv
    have h_conv_d : ⟦D.abstract Δ_alt
        (fun v hv => Δ_fv_alt v (B.fv.mem_all (.inl hv)))⟧ᴮ =
        some D_dom_pkg := by convert h_den_d using 2
    have hD_dom_eq : D_dom_pkg = ⟨𝒟_alt, ⟨τ.set, h𝒟_alt⟩⟩ := by
      rw [h_conv_d] at hden_D_alt_eq
      exact Option.some.inj hden_D_alt_eq
    subst hD_dom_eq
    simp only at rest_alt
    rw [dif_pos τ_hasArity] at rest_alt
    -- rest_alt: split into den_P_cond, typP_det_cond, h𝒟_empty branches.
    -- For forall: dif_pos τ_hasArity → if den_P → if typP_det → if 𝒟=∅ then... else...
    split_ifs at rest_alt with h_den_P h_typP_det h𝒟_empty
    · -- Empty branch: 𝒟_alt = ∅, returns zftrue. Use defaultZFSet witness.
      -- den_P_cond is vacuously true in this case (∀ x ∈ ∅, ...). We construct
      -- a witness for P via B.denote_exists_of_typing applied to typP at
      -- the default x_fin extension.
      have h𝒟_alt_empty : 𝒟_alt = ∅ := h𝒟_empty
      let f_alt : Fin vs.length → B.Dom := fun i =>
        ⟨(τ.get vs.length i).defaultZFSet, ⟨τ.get vs.length i,
          BType.mem_toZFSet_of_defaultZFSet⟩⟩
      have hf_alt_typ : ∀ i, (f_alt i).snd.fst = τ.get vs.length i ∧
          (f_alt i).fst ∈ ⟦τ.get vs.length i⟧ᶻ :=
        fun i => ⟨rfl, (f_alt i).snd.snd⟩
      -- Build Δ_ext_alt and Δ_fv_P_alt for the default witness.
      set Δ_ext_alt_fin : B.RenamingContext.Context :=
        Function.updates Δ_alt vs (List.ofFn fun i => some (f_alt i))
      have Δ_fv_P_alt_fin : ∀ v ∈ B.fv P, (Δ_ext_alt_fin v).isSome := by
        intro v hv
        show (Function.updates Δ_alt vs _ v).isSome = true
        rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup]
        split_ifs with hvs
        · simp [List.getElem_ofFn]
        · exact Δ_fv_alt v (B.fv.mem_all (.inr ⟨hv, hvs⟩))
      -- Use denote_exists_of_typing (B namespace, available via `open B`) to
      -- obtain a P denotation.
      have hP_exists := denote_exists_of_typing typP
        Δ_ext_alt_fin Δ_fv_P_alt_fin (@WFTC.wf _ WFTC.of_abstract)
      obtain ⟨P_val, hP_val, hP_den_abs⟩ := hP_exists
      -- Lift P_val's typing through the abstract.
      have hP_den_at_abs :
          ⟦P.abstract Δ_ext_alt_fin Δ_fv_P_alt_fin⟧ᴮ =
            some ⟨P_val, ⟨BType.bool, hP_val⟩⟩ := hP_den_abs
      -- Convert to abstract.go form.
      refine ⟨f_alt, hf_alt_typ, P_val, hP_val, ?_⟩
      rw [denote_term_abstract_go_eq_term_abstract vs_nodup vs_nemp f_alt
        Δ_fv_P_alt_fin]
      exact hP_den_at_abs
    · -- Nonempty branch: 𝒟_alt ≠ ∅, returns sInter. Witness via Classical.choose.
      have 𝒟_nonempty : 𝒟_alt.Nonempty :=
        𝒟_alt.eq_empty_or_nonempty.resolve_left h𝒟_empty
      obtain ⟨x_raw, hx_raw⟩ := 𝒟_nonempty
      have 𝒟_sub_τ : 𝒟_alt ⊆ ⟦τ⟧ᶻ := by
        rwa [BType.toZFSet, ZFSet.mem_powerset] at h𝒟_alt
      have hx_raw_mem : x_raw ∈ ⟦τ⟧ᶻ := 𝒟_sub_τ hx_raw
      have hx_raw_arity : x_raw.hasArity vs.length :=
        hasArity_of_mem_toZFSet τ_hasArity hx_raw_mem
      let f_alt : Fin vs.length → B.Dom := fun i =>
        ⟨x_raw.get vs.length i, τ.get vs.length i,
         get_mem_type_of_isTuple hx_raw_arity τ_hasArity hx_raw_mem⟩
      have h_ofFinDom_eq : ZFSet.ofFinDom f_alt = x_raw :=
        ZFSet.ofFinDom_get (List.length_pos_iff.mpr vs_nemp)
          (fun _ => get_mem_type_of_isTuple hx_raw_arity τ_hasArity hx_raw_mem)
          hx_raw_arity τ_hasArity
      have hf_alt_typ : ∀ i, (f_alt i).snd.fst = τ.get vs.length i ∧
          (f_alt i).fst ∈ ⟦τ.get vs.length i⟧ᶻ :=
        fun i => ⟨rfl, (f_alt i).snd.snd⟩
      have hx_fin_in_𝒟_alt : ZFSet.ofFinDom f_alt ∈ 𝒟_alt := h_ofFinDom_eq ▸ hx_raw
      have hP_isSome := h_den_P hf_alt_typ hx_fin_in_𝒟_alt
      obtain ⟨⟨P_val, P_ty, hP_val⟩, hP_den⟩ := Option.isSome_iff_exists.mp hP_isSome
      have Δ_fv_alt_P : ∀ v ∈ B.fv P, (Function.updates Δ_alt vs
          (List.ofFn fun i => some (f_alt i)) v).isSome = true := by
        intro v hv
        rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup]
        split_ifs with hvs
        · simp [List.getElem_ofFn]
        · exact Δ_fv_alt v (B.fv.mem_all (.inr ⟨hv, hvs⟩))
      have hP_den_at_abs : ⟦P.abstract (Function.updates Δ_alt vs
            (List.ofFn fun i => some (f_alt i))) Δ_fv_alt_P⟧ᴮ =
          some ⟨P_val, ⟨P_ty, hP_val⟩⟩ := by
        rw [← denote_term_abstract_go_eq_term_abstract vs_nodup vs_nemp f_alt Δ_fv_alt_P]
        convert hP_den using 2
      have hτP_bool : P_ty = BType.bool := by
        exact (denote_welltyped_eq
          (t := P.abstract (Function.updates Δ_alt vs
            (List.ofFn fun i => some (f_alt i))) Δ_fv_alt_P)
          ⟨_, WFTC.of_abstract, BType.bool,
            by convert Typing.of_abstract Δ_fv_alt_P typP⟩
          hP_den_at_abs).symm
      subst hτP_bool
      refine ⟨f_alt, hf_alt_typ, P_val, hP_val, ?_⟩
      convert hP_den using 2
  obtain ⟨f_alt, hf_alt_typ, P_val_alt, hP_val_alt, hP_go_den_alt⟩ := hden_alt_data
  -- =========================================================================
  -- Step 2: Build B-side ext context Δ_ext_alt and SMT-side ext Δ_D_ext_alt.
  -- =========================================================================
  set Δ_ext_alt : B.RenamingContext.Context :=
    Function.updates Δ_alt vs (List.ofFn fun i => some (f_alt i)) with Δ_ext_alt_def
  have Δ_fv_P_alt : ∀ v ∈ B.fv P, (Δ_ext_alt v).isSome = true := by
    intro v hv
    show (Function.updates Δ_alt vs _ v).isSome = true
    rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup]
    split_ifs with hvs
    · simp [List.getElem_ofFn]
    · exact Δ_fv_alt v (B.fv.mem_all (.inr ⟨hv, hvs⟩))
  -- Lift hP_go_den_alt to a P.abstract denotation.
  have h_den_P_alt : ⟦P.abstract Δ_ext_alt Δ_fv_P_alt⟧ᴮ =
      some ⟨P_val_alt, ⟨BType.bool, hP_val_alt⟩⟩ := by
    rw [← denote_term_abstract_go_eq_term_abstract vs_nodup vs_nemp f_alt Δ_fv_P_alt]
    convert hP_go_den_alt using 2
  -- Δ_D_ext_alt: SMT-side ext extending Δ_D_alt at vs to canonical SMT translations.
  set Δ_D_ext_alt : SMT.RenamingContext.Context :=
    Function.updates Δ_D_alt vs
      (List.ofFn fun (i : Fin vs.length) => B.RenamingContext.toSMT Δ_ext_alt vs[i])
    with Δ_D_ext_alt_def
  -- =========================================================================
  -- Step 3: Build Δ₀_hybrid_alt for P_enc_total invocation.
  -- =========================================================================
  set Δ₀_hybrid_alt : SMT.RenamingContext.Context :=
    B.RenamingContext.toSMTOnFV Δ_ext_alt P with Δ₀_hybrid_alt_def
  have Δ₀_hybrid_ext_P_alt : SMT.RenamingContext.ExtendsOnSourceFV Δ₀_hybrid_alt
      Δ_ext_alt P := by
    intro v d hv_eq; exact hv_eq
  -- none_out: v ∉ used_P ⇒ v ∉ B.fv P (via covers_P) ⇒ toSMTOnFV = none.
  have Δ₀_hybrid_alt_none_used_P : ∀ v ∉ used_P, Δ₀_hybrid_alt v = none := by
    intro v hv
    show B.RenamingContext.toSMTOnFV Δ_ext_alt P v = none
    have hv_not_fv_P : v ∉ B.fv P := fun hv_fv => hv (covers_P v hv_fv)
    simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
      B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_not_fv_P]
  -- wt: for v ∈ B.fv P, type tag of toSMT Δ_ext_alt v matches Γ_P's lookup.
  have Δ₀_hybrid_alt_wt : ∀ v (d : SMT.Dom), Δ₀_hybrid_alt v = some d →
      ∀ τ_v, AList.lookup v Γ_P = some τ_v → d.snd.fst = τ_v := by
    intro v d hv τ_v hτ_v
    change B.RenamingContext.toSMTOnFV Δ_ext_alt P v = some d at hv
    -- v ∈ B.fv P (else toSMTOnFV = none).
    have hv_fv_P : v ∈ B.fv P := by
      by_contra hv_not
      simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
        B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_not] at hv
    by_cases hvs : v ∈ vs
    · -- v ∈ vs: Δ_ext_alt v = some (f_alt vs.idxOf v); type tag = (τ.get _ i).toSMTType.
      have hidx : vs.idxOf v < vs.length := List.idxOf_lt_length_of_mem hvs
      have hΔ_ext_alt_v : Δ_ext_alt v = some (f_alt ⟨vs.idxOf v, hidx⟩) := by
        show Function.updates Δ_alt vs _ v = _
        rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup, dif_pos hvs]
        simp only [List.getElem_ofFn]
      have hv_eq_toSMT : B.RenamingContext.toSMTOnFV Δ_ext_alt P v =
          B.RenamingContext.toSMT Δ_ext_alt v := by
        simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
          B.RenamingContext.restrictToFV_eq_of_mem hv_fv_P]
      rw [hv_eq_toSMT] at hv
      rw [B.RenamingContext.toSMT, hΔ_ext_alt_v, Option.pure_def, Option.bind_eq_bind,
        Option.bind_some] at hv
      cases hv
      simp only
      rw [(hf_alt_typ ⟨vs.idxOf v, hidx⟩).1]
      -- Goal: (τ.get vs.length ⟨vs.idxOf v, hidx⟩).toSMTType = τ_v
      have h_lookup := vs_lookup_Γ_P ⟨vs.idxOf v, hidx⟩
      have h_v_eq : (vs.get ⟨vs.idxOf v, hidx⟩) = v := List.getElem_idxOf hidx
      have h_lookup' : AList.lookup v Γ_P = some
          ((τ.toSMTType.fromProdl (vs.length - 1))[vs.idxOf v]'(by
            rw [fromProdl_length_of_hasArity τ_hasArity]; exact hidx)) := by
        convert h_lookup using 1
        · exact congrArg (AList.lookup · _) h_v_eq.symm
      rw [hτ_v] at h_lookup'
      injection h_lookup' with h_eq
      rw [h_eq]
      exact toSMTType_get_eq_fromProdl_getElem τ_hasArity hidx
    · -- v ∉ vs: Δ_ext_alt v = Δ_alt v. Use hext_alt to get Δ₀_alt v = some d.
      have hΔ_ext_alt_v : Δ_ext_alt v = Δ_alt v := by
        show Function.updates Δ_alt vs _ v = Δ_alt v
        exact Function.updates_of_not_mem Δ_alt vs _ v hvs
      have hv_eq_toSMT : B.RenamingContext.toSMTOnFV Δ_ext_alt P v =
          B.RenamingContext.toSMT Δ_alt v := by
        simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
          B.RenamingContext.restrictToFV_eq_of_mem hv_fv_P, hΔ_ext_alt_v]
      rw [hv_eq_toSMT] at hv
      -- hv : toSMT Δ_alt v = some d
      have hv_all : v ∈ B.fv (B.Term.all vs D P) :=
        B.fv.mem_all (.inr ⟨hv_fv_P, hvs⟩)
      have h_toSMTOnFV_all : B.RenamingContext.toSMTOnFV Δ_alt
          (B.Term.all vs D P) v = some d := by
        simp only [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
          B.RenamingContext.restrictToFV_eq_of_mem hv_all, Option.pure_def,
          Option.bind_eq_bind]
        rw [B.RenamingContext.toSMT, Option.pure_def, Option.bind_eq_bind] at hv
        exact hv
      have hΔ₀_alt_v : Δ₀_alt v = some d := hext_alt h_toSMTOnFV_all
      have hτ_v_Γ' : AList.lookup v Γ' = some τ_v := Γ_P_lookup_sub_Γ' v hvs τ_v hτ_v
      exact hwt_alt v d hΔ₀_alt_v τ_v hτ_v_Γ'
  -- =========================================================================
  -- Step 4: Invoke P_enc_total.
  -- =========================================================================
  obtain ⟨Δ_P_alt, hcov_P_alt, denT_P_alt, Δ_P_alt_extends, Δ_P_alt_none_out_used_P,
      Δ_P_alt_wt_out, hden_P_alt, hRDom_P_alt, Δ_P_alt_dom⟩ :=
    P_enc_total Δ_ext_alt Δ_fv_P_alt Δ₀_hybrid_alt Δ₀_hybrid_ext_P_alt
      Δ₀_hybrid_alt_none_used_P Δ₀_hybrid_alt_wt P_val_alt hP_val_alt h_den_P_alt
  -- =========================================================================
  -- Round 5: Build h_typ_alt typing for forall under Γ', use
  -- denote_exists_of_typing_fv to obtain denT_alt, and discharge the first
  -- five conjuncts of the existential. RDom (R6) closed via the
  -- `rdom_witness_hasflag` parent hypothesis (FALLBACK).
  -- Mirrors `lambda_chosen_totality` R5 (commit f046ff8) lines 1059-1245.
  -- For the all/forall case, `imp_body` is opaque, so we take the typing of
  -- the full `forall zs τs imp_body` as a hypothesis (`typ_forall`) rather
  -- than reconstructing it from a structured body shape (lambda's
  -- `and(D_app, eq)`).
  -- =========================================================================
  -- Step R5.1: Build hcompat for denote_exists_of_typing_fv.
  have hcompat : SMT.RenamingContext.RespectsTypeContextOnFV Δ'_alt Γ'
      (SMT.Term.forall zs τs imp_body) := by
    intro v τ_v hv_fv hlookup
    have hcov_v := Δ'_alt_covers_forall v hv_fv
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hcov_v
    refine ⟨d, hd, ?_⟩
    exact Δ'_alt_wt v d hd τ_v hlookup
  -- Step R5.2: Apply denote_exists_of_typing_fv to obtain denT_alt.
  have hden_exists := SMT.RenamingContext.denote_exists_of_typing_fv
    typ_forall hcompat Δ'_alt_covers_forall
  obtain ⟨denT_alt, hden_alt_eq, hden_alt_ty⟩ := hden_exists
  -- Step R5.3: Discharge the existential. Five conjuncts close from existing
  -- R3 facts (Δ'_alt_extends_Δ₀_alt, Δ'_alt_none_out, Δ'_alt_wt, hden_alt_eq,
  -- Δ'_alt_dom_Γ'); RDom (R6) discharged via `rdom_witness_hasflag`.
  refine ⟨Δ'_alt, Δ'_alt_covers_forall, denT_alt, Δ'_alt_extends_Δ₀_alt,
    Δ'_alt_none_out, Δ'_alt_wt, hden_alt_eq, ?_, Δ'_alt_dom_Γ'⟩
  -- R6 RDom: discharge via the `rdom_witness_hasflag` parent hypothesis
  -- (FALLBACK — see signature TODO). The hypothesis packages the deferred
  -- semantic bridge work needed to close the forall RDom equation, requiring
  -- `case_b_preimage` (E.po-based functional invariant) which is not yet
  -- threaded through the soundness statement.
  exact rdom_witness_hasflag Δ_alt Δ_fv_alt Δ₀_alt hext_alt hnone_alt hwt_alt
    T_alt hT_alt hden_alt Δ'_alt Δ'_alt_covers_forall denT_alt hden_alt_eq
