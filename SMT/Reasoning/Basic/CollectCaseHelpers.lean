import SMT.Reasoning.Basic.AbstractSubstDenote
import SMT.Reasoning.Basic.DenotationTotality
import SMT.Reasoning.SubstLemmas

open Std.Do B SMT ZFSet

theorem toDestPair_bv_nil {vs : List SMT.𝒱} {z : SMT.𝒱} :
    ∀ t ∈ toDestPair vs (.var z), SMT.bv t = [] := by
  suffices h : ∀ (vs : List SMT.𝒱) (zp : SMT.Term) (acc : List SMT.Term) (d : SMT.Term),
      SMT.bv zp = [] → (∀ a ∈ acc, SMT.bv a = []) → SMT.bv d = [] →
      ∀ t ∈ toDestPair vs zp acc d, SMT.bv t = [] by
    exact h vs (.var z) [] (.var z) (by rw [SMT.bv]) (fun _ h => absurd h (List.not_mem_nil)) (by rw [SMT.bv])
  intro vs'; induction vs' with
  | nil => intro _ acc _ _ hacc _; exact hacc
  | cons x xs ih =>
    intro zp acc d hzp hacc hd
    cases xs with
    | nil =>
      unfold toDestPair; intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact hzp
      · exact hacc t ht
    | cons y ys =>
      unfold toDestPair
      exact ih (.fst d) (.snd d :: acc) (.fst d)
        (by simp [SMT.bv, hd])
        (fun a ha => by
          rcases List.mem_cons.mp ha with rfl | ha
          · simp [SMT.bv, hd]
          · exact hacc a ha)
        (by simp [SMT.bv, hd])

/-- Generalized form of `toDestPair_bv_nil` with a user-supplied base term `t₀`
whose `bv` is empty. -/
theorem toDestPair_bv_nil_base {vs : List SMT.𝒱} {t₀ : SMT.Term} (h_bv : SMT.bv t₀ = []) :
    ∀ t ∈ toDestPair vs t₀, SMT.bv t = [] := by
  suffices h : ∀ (vs : List SMT.𝒱) (zp : SMT.Term) (acc : List SMT.Term) (d : SMT.Term),
      SMT.bv zp = [] → (∀ a ∈ acc, SMT.bv a = []) → SMT.bv d = [] →
      ∀ t ∈ toDestPair vs zp acc d, SMT.bv t = [] by
    exact h vs t₀ [] t₀ h_bv (fun _ h => absurd h (List.not_mem_nil)) h_bv
  intro vs'; induction vs' with
  | nil => intro _ acc _ _ hacc _; exact hacc
  | cons x xs ih =>
    intro zp acc d hzp hacc hd
    cases xs with
    | nil =>
      unfold toDestPair; intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact hzp
      · exact hacc t ht
    | cons y ys =>
      unfold toDestPair
      exact ih (.fst d) (.snd d :: acc) (.fst d)
        (by simp [SMT.bv, hd])
        (fun a ha => by
          rcases List.mem_cons.mp ha with rfl | ha
          · simp [SMT.bv, hd]
          · exact hacc a ha)
        (by simp [SMT.bv, hd])

theorem toDestPair_ne_none {vs : List SMT.𝒱} {z : SMT.𝒱} :
    ∀ t ∈ toDestPair vs (.var z), t ≠ SMT.Term.none := by
  suffices h : ∀ (vs : List SMT.𝒱) (zp : SMT.Term) (acc : List SMT.Term) (d : SMT.Term),
      zp ≠ .none → (∀ a ∈ acc, a ≠ .none) → d ≠ .none →
      ∀ t ∈ toDestPair vs zp acc d, t ≠ .none by
    exact h vs (.var z) [] (.var z) (by simp) (fun _ h => absurd h (List.not_mem_nil)) (by simp)
  intro vs'; induction vs' with
  | nil => intro _ acc _ _ hacc _; exact hacc
  | cons x xs ih =>
    intro zp acc d hzp hacc hd
    cases xs with
    | nil =>
      unfold toDestPair; intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact hzp
      · exact hacc t ht
    | cons y ys =>
      unfold toDestPair
      exact ih (.fst d) (.snd d :: acc) (.fst d)
        (by simp)
        (fun a ha => by
          rcases List.mem_cons.mp ha with rfl | ha
          · simp
          · exact hacc a ha)
        (by simp)

theorem foldl_insert_preserves_lookup {Γ : SMT.TypeContext} {k : SMT.𝒱} {v : SMTType}
    {pairs : List (SMT.𝒱 × SMTType)}
    (hlookup : Γ.lookup k = some v)
    (hk : ∀ p ∈ pairs, p.1 ≠ k) :
    (pairs.foldl (fun Γ (p : SMT.𝒱 × SMTType) => Γ.insert p.1 p.2) Γ).lookup k = some v := by
  induction pairs generalizing Γ with
  | nil => exact hlookup
  | cons p ps ih =>
    simp only [List.foldl_cons]
    exact ih (by rw [AList.lookup_insert_ne (hk p (List.mem_cons_self ..)).symm]; exact hlookup)
      (fun q hq => hk q (List.mem_cons_of_mem _ hq))

theorem foldl_insert_lookup_zip {Γ : SMT.TypeContext}
    {vs : List SMT.𝒱} {τs : List SMTType}
    (hnd : vs.Nodup) {i : ℕ} (hi_vs : i < vs.length) (hi_τs : i < τs.length) :
    ((vs.zip τs).foldl (fun Γ (p : SMT.𝒱 × SMTType) => Γ.insert p.1 p.2) Γ).lookup vs[i] =
      some τs[i] := by
  induction vs generalizing τs Γ i with
  | nil => exact absurd hi_vs (Nat.not_lt_zero _)
  | cons v vs' ih =>
    cases τs with
    | nil => exact absurd hi_τs (Nat.not_lt_zero _)
    | cons τ' τs' =>
      simp only [List.zip_cons_cons, List.foldl_cons]
      cases i with
      | zero =>
        simp only [List.getElem_cons_zero]
        exact foldl_insert_preserves_lookup (AList.lookup_insert Γ) (by
          intro ⟨k, _⟩ hk
          exact fun heq => (List.nodup_cons.mp hnd).1 (heq ▸ List.mem_fst_of_mem_zip hk))
      | succ i' =>
        simp only [List.getElem_cons_succ, List.length_cons, Nat.succ_lt_succ_iff] at hi_vs hi_τs ⊢
        exact ih (List.nodup_cons.mp hnd).2 hi_vs hi_τs

theorem toDestPair_length_gen :
    ∀ (vs : List SMT.𝒱) (zp d : SMT.Term) (acc : List SMT.Term),
    vs ≠ [] → (toDestPair vs zp acc d).length = vs.length + acc.length := by
  intro vs; induction vs with
  | nil => intro _ _ _ h; exact absurd rfl h
  | cons x xs ih =>
    intro zp d acc _
    cases xs with
    | nil => unfold toDestPair; simp [List.length_cons]; omega
    | cons y ys =>
      unfold toDestPair
      rw [ih (.fst d) (.fst d) (.snd d :: acc) (List.cons_ne_nil y ys)]
      simp [List.length_cons]; omega

theorem fromProdl_zero_eq (σ : SMTType) : σ.fromProdl 0 = [σ] := by
  cases σ <;> simp [SMT.SMTType.fromProdl]

theorem toDestPair_typing_gen (Γ : SMT.TypeContext) :
    ∀ (vs : List SMT.𝒱) (zp d : SMT.Term) (σ : SMTType)
      (acc : List SMT.Term) (σs_acc : List SMTType),
    vs ≠ [] → zp = d → Γ ⊢ˢ d : σ →
    (σ.fromProdl (vs.length - 1)).length = vs.length →
    (hacc_len : acc.length = σs_acc.length) →
    (∀ j (hj : j < acc.length), Γ ⊢ˢ acc[j] : σs_acc[j]'(hacc_len ▸ hj)) →
    ∀ j (τ_j : SMTType),
      ((σ.fromProdl (vs.length - 1)) ++ σs_acc)[j]? = some τ_j →
      ∃ hj : j < (toDestPair vs zp acc d).length,
        Γ ⊢ˢ (toDestPair vs zp acc d)[j] : τ_j := by
  intro vs'
  induction vs' with
  | nil => intro _ _ _ _ _ hvs; exact absurd rfl hvs
  | cons x xs ih =>
    intro zp dd σ acc σs_acc _ heq hd hfp hacc_len hacc j τ_j hget
    subst zp
    cases xs with
    | nil =>
      -- vs = [x], result = d :: acc, types = [σ] ++ σs_acc
      have hfp0 : σ.fromProdl 0 = [σ] := fromProdl_zero_eq σ
      have hvs_sub : ([x] : List SMT.𝒱).length - 1 = 0 := by simp
      rw [hvs_sub] at hfp hget
      rw [hfp0] at hget
      unfold toDestPair
      cases j with
      | zero =>
        simp only [List.singleton_append, List.getElem?_cons_zero] at hget
        exact ⟨by simp, by cases hget; exact hd⟩
      | succ j' =>
        simp only [List.singleton_append, List.getElem?_cons_succ] at hget
        have hj' : j' < acc.length := by
          by_contra h; push_neg at h
          rw [List.getElem?_eq_none (by omega)] at hget; exact Option.noConfusion hget
        have hj'_t : j' < σs_acc.length := by omega
        refine ⟨by simp; omega, ?_⟩
        rw [List.getElem?_eq_getElem hj'_t] at hget
        cases hget
        exact hacc j' hj'
    | cons y ys =>
      -- vs = x :: y :: ys
      -- σ must be .pair α β (from length constraint)
      obtain ⟨α, β, rfl⟩ : ∃ α β, σ = .pair α β := by
        have hvs_len : (x :: y :: ys).length - 1 = ys.length + 1 := by simp [List.length_cons]
        rw [hvs_len] at hfp
        cases σ with
        | pair α β => exact ⟨α, β, rfl⟩
        | bool => simp [SMT.SMTType.fromProdl, List.length_cons] at hfp
        | int => simp [SMT.SMTType.fromProdl, List.length_cons] at hfp
        | unit => simp [SMT.SMTType.fromProdl, List.length_cons] at hfp
        | «fun» _ _ => simp [SMT.SMTType.fromProdl, List.length_cons] at hfp
        | option _ => simp [SMT.SMTType.fromProdl, List.length_cons] at hfp
      -- Prepare for IH
      have hvs_sub : (x :: y :: ys).length - 1 = ys.length + 1 := by simp [List.length_cons]
      have hvs_sub' : (y :: ys).length - 1 = ys.length := by simp [List.length_cons]
      have h_fromProdl : SMT.SMTType.fromProdl (.pair α β) (ys.length + 1) =
          (α.fromProdl ys.length).concat β := by
        simp [SMT.SMTType.fromProdl]
      have hα_len : (α.fromProdl ys.length).length = 1 + ys.length := by
        rw [hvs_sub] at hfp; rw [h_fromProdl, List.length_concat] at hfp
        simp [List.length_cons] at hfp; omega
      have h_types_eq : SMT.SMTType.fromProdl (.pair α β) (ys.length + 1) ++ σs_acc =
          α.fromProdl ys.length ++ (β :: σs_acc) := by
        rw [h_fromProdl, List.concat_eq_append, List.append_assoc, List.singleton_append]
      rw [hvs_sub] at hget
      rw [h_types_eq] at hget
      have hfst : Γ ⊢ˢ Term.fst dd : α := SMT.Typing.fst _ _ _ _ hd
      have hsnd : Γ ⊢ˢ Term.snd dd : β := SMT.Typing.snd _ _ _ _ hd
      unfold toDestPair
      exact ih (Term.fst dd) (Term.fst dd) α (Term.snd dd :: acc) (β :: σs_acc)
        (List.cons_ne_nil y ys) rfl hfst
        (by rw [hvs_sub']; simp [List.length_cons]; omega)
        (by simp [hacc_len])
        (by intro j' hj'
            simp [List.length_cons] at hj'
            cases j' with
            | zero => simp only [List.getElem_cons_zero]; exact hsnd
            | succ j'' =>
              simp only [List.getElem_cons_succ]
              exact hacc j'' (by omega))
        j τ_j hget

theorem fromProdl_length_of_hasArity {τ : BType} {n : ℕ} (h : τ.hasArity n) :
    (τ.toSMTType.fromProdl (n - 1)).length = n := by
  induction n generalizing τ with
  | zero => exact absurd h (by unfold BType.hasArity; exact id)
  | succ n ih =>
    cases n with
    | zero =>
      -- n = 1: any type, fromProdl 0 always returns a singleton
      cases τ <;> simp [BType.toSMTType, SMT.SMTType.fromProdl]
    | succ k =>
      -- n = k+2: τ must be .prod α β with α.hasArity (k+1)
      cases τ with
      | prod α β =>
        unfold BType.hasArity at h
        simp only [BType.toSMTType]
        show (SMT.SMTType.fromProdl (.pair α.toSMTType β.toSMTType) (k + 1)).length = k + 2
        rw [SMT.SMTType.fromProdl, List.length_concat]
        have := ih h; simp only [Nat.add_sub_cancel] at this; omega
      | int => exact absurd h (by unfold BType.hasArity; exact id)
      | bool => exact absurd h (by unfold BType.hasArity; exact id)
      | set _ => exact absurd h (by unfold BType.hasArity; exact id)

theorem toSMTType_get_eq_fromProdl_getElem {τ : BType} {n : ℕ}
    (h : τ.hasArity n) {i : ℕ} (hi : i < n) :
    (τ.get n ⟨i, hi⟩).toSMTType =
      (τ.toSMTType.fromProdl (n - 1))[i]'(by
        have := fromProdl_length_of_hasArity h; omega) := by
  induction n generalizing τ i with
  | zero => exact absurd hi (Nat.not_lt_zero _)
  | succ n ih =>
    cases n with
    | zero =>
      have hi0 : i = 0 := Nat.lt_one_iff.mp hi
      subst hi0
      cases τ <;> simp [BType.get, BType.toSMTType, SMT.SMTType.fromProdl]
    | succ k =>
      match τ, h with
      | .prod α β, h_arity =>
        have h' : α.hasArity (k + 1) := h_arity
        have hα_len : (α.toSMTType.fromProdl k).length = k + 1 := by
          have := fromProdl_length_of_hasArity h'; simp only [Nat.add_sub_cancel] at this; exact this
        -- Use suffices to work with the concat form
        suffices hsuff : ((BType.prod α β).get (k + 1 + 1) ⟨i, hi⟩).toSMTType =
            ((α.toSMTType.fromProdl k).concat β.toSMTType)[i]'(by
              rw [List.length_concat, hα_len]; omega) by
          have hfp : (α ×ᴮ β).toSMTType.fromProdl (k + 1 + 1 - 1) =
              (α.toSMTType.fromProdl k).concat β.toSMTType := by
            show (α.toSMTType.pair β.toSMTType).fromProdl (k + 1) = _
            simp [SMT.SMTType.fromProdl]
          simp only [hfp]; exact hsuff
        by_cases hilast : i = k + 1
        · subst hilast
          have hlhs : (BType.prod α β).get (k + 2) ⟨k + 1, hi⟩ = β := by unfold BType.get; simp
          rw [hlhs]
          have : ((α.toSMTType.fromProdl k).concat β.toSMTType)[k + 1]'(by
              rw [List.length_concat, hα_len]; omega) =
              ((α.toSMTType.fromProdl k) ++ [β.toSMTType])[k + 1]'(by
              simp [hα_len]) := by
            simp [List.concat_eq_append]
          rw [this, List.getElem_append_right (by omega)]
          simp [hα_len]
        · have hi_small : i < k + 1 := by omega
          have hlhs : (BType.prod α β).get (k + 2) ⟨i, hi⟩ = α.get (k + 1) ⟨i, by omega⟩ := by
            show (if _ : i = k + 1 then β else α.get (k + 1) ⟨i, _⟩) = _
            rw [dif_neg hilast]
          rw [hlhs]
          have : ((α.toSMTType.fromProdl k).concat β.toSMTType)[i]'(by
              rw [List.length_concat, hα_len]; omega) =
              ((α.toSMTType.fromProdl k) ++ [β.toSMTType])[i]'(by simp [hα_len]; omega) := by
            simp [List.concat_eq_append]
          rw [this, List.getElem_append_left (by omega)]
          exact ih h' hi_small

theorem encodeTerm_env_irrel (t : B.Term) (E₁ E₂ : B.Env) (hflags : E₁.flags = E₂.flags) :
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
  | all vs D P ihD ihP =>
    simp only [encodeTerm]; rw [ihD, ihP, hflags]

theorem typing_reduce_cprod (Γ : B.TypeContext) :
    ∀ (Ds : List B.Term) (αs : List BType)
    (hForall : List.Forall₂ (fun Dᵢ αᵢ => Γ ⊢ᴮ Dᵢ : .set αᵢ) Ds αs)
    (hDs : Ds ≠ []) (hαs : αs ≠ []),
    Γ ⊢ᴮ Ds.reduce (· ⨯ᴮ ·) hDs : .set (αs.reduce (· ×ᴮ ·) hαs)
  | [_], [_], .cons h .nil, _, _ => by simpa [List.reduce] using h
  | D :: D' :: Ds, α :: α' :: αs, .cons hD (.cons hD' htail), _, _ => by
    rw [List.reduce_cons_cons, List.reduce_cons_cons]
    exact typing_reduce_cprod Γ _ _ (.cons (Typing.cprod hD hD') htail)
      (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)
  termination_by Ds => Ds.length

theorem hasArity_of_mem_toZFSet {τ : BType} {n : ℕ} {x : ZFSet}
    (hτ : τ.hasArity n) (hx : x ∈ τ.toZFSet) : x.hasArity n := by
  induction n generalizing τ x with
  | zero => exact absurd hτ (by cases τ <;> unfold BType.hasArity <;> exact id)
  | succ n ih =>
    cases n with
    | zero =>
      -- n = 1: any BType with hasArity 1
      simp only [ZFSet.hasArity]
    | succ k =>
      -- n = k + 2: τ must be .prod α β with α.hasArity (k + 1)
      cases τ with
      | prod α β =>
        rw [BType.hasArity] at hτ
        rw [BType.toZFSet] at hx
        obtain ⟨a, ha, b, hb, hab⟩ := ZFSet.mem_prod.mp hx
        simp only [ZFSet.hasArity, show (∃ a b, x = a.pair b) from ⟨a, b, hab⟩, ite_true]
        rw [hab, ZFSet.π₁_pair]
        exact ih hτ ha
      | int => exact absurd hτ (by simp [BType.hasArity])
      | bool => exact absurd hτ (by simp [BType.hasArity])
      | set _ => exact absurd hτ (by simp [BType.hasArity])

/-- Elements of `⟦τ.toSMTType⟧ᶻ` have the same hasArity as elements of `⟦τ⟧ᶻ`. -/
theorem hasArity_of_mem_toSMTZFSet {τ : BType} {n : ℕ} {x : ZFSet}
    (hτ : τ.hasArity n) (hx : x ∈ ⟦τ.toSMTType⟧ᶻ) : x.hasArity n := by
  induction n generalizing τ x with
  | zero => exact absurd hτ (by cases τ <;> unfold BType.hasArity <;> exact id)
  | succ n ih =>
    cases n with
    | zero => simp only [ZFSet.hasArity]
    | succ k =>
      cases τ with
      | prod α β =>
        rw [BType.hasArity] at hτ
        rw [BType.toSMTType, SMTType.toZFSet] at hx
        obtain ⟨a, ha, b, hb, hab⟩ := ZFSet.mem_prod.mp hx
        simp only [ZFSet.hasArity, show (∃ a b, x = a.pair b) from ⟨a, b, hab⟩, ite_true]
        rw [hab, ZFSet.π₁_pair]
        exact ih hτ ha
      | int => exact absurd hτ (by simp [BType.hasArity])
      | bool => exact absurd hτ (by simp [BType.hasArity])
      | set _ => exact absurd hτ (by simp [BType.hasArity])

/-- Projecting the i-th component of an element of `⟦τ.toSMTType⟧ᶻ` gives an element of
    `⟦(τ.get n i).toSMTType⟧ᶻ`. -/
theorem get_mem_toSMTZFSet {τ : BType} {n : ℕ} {i : Fin n} {z : ZFSet}
    (hz : z.hasArity n) (hτ : τ.hasArity n) (hz' : z ∈ ⟦τ.toSMTType⟧ᶻ) :
    z.get n i ∈ ⟦(τ.get n i).toSMTType⟧ᶻ := by
  fun_induction ZFSet.hasArity generalizing τ with
  | case1 => nomatch hz
  | case2 =>
    rcases Fin.fin_one_eq_zero i
    unfold ZFSet.get BType.get
    exact hz'
  | case3 x n npos hx ih =>
    cases n with
    | zero =>
      rcases Fin.fin_one_eq_zero i
      unfold ZFSet.get BType.get
      exact hz'
    | succ n =>
      unfold BType.hasArity at hτ
      unfold ZFSet.get BType.get
      split at hτ using α β
      · split_ifs with _ hi hi
        · rw [BType.toSMTType, SMTType.toZFSet, ZFSet.mem_prod] at hz'
          obtain ⟨_, hα, _, hβ, rfl⟩ := hz'
          rwa [ZFSet.π₂_pair]
        · rw [Fin.ext_iff] at hi; contradiction
        · rw [Fin.ext_iff] at hi; contradiction
        · letI i' : Fin (n+1) := ⟨i, Nat.lt_iff_le_and_ne.mpr
            ⟨Nat.le_of_lt_succ i.prop, by rwa [Fin.ext_iff] at hi⟩⟩
          have := ih (i := i.castPred hi) hz hτ
          rw [BType.toSMTType, SMTType.toZFSet, ZFSet.mem_prod] at hz'
          obtain ⟨_, hα, _, hβ, rfl⟩ := hz'
          apply ih hz hτ
          rwa [ZFSet.π₁_pair]
      · nomatch hτ
  | case4 x n npos hx =>
    cases n with
    | zero =>
      rcases Fin.fin_one_eq_zero i
      unfold ZFSet.get BType.get
      exact hz'
    | succ n =>
      unfold BType.hasArity at hτ
      unfold ZFSet.get BType.get
      split at hτ using α β
      · rw [BType.toSMTType, SMTType.toZFSet, ZFSet.mem_prod] at hz'
        nomatch hz
      · nomatch hτ

/-- `retract` distributes over `get`: the i-th component of `retract τ x` equals
    `retract (τ.get n i) (x.get n i)`. -/
theorem retract_get_comm {τ : BType} {n : ℕ} {i : Fin n} {x : ZFSet}
    (hx : x.hasArity n) (hτ : τ.hasArity n) (hx_mem : x ∈ ⟦τ.toSMTType⟧ᶻ) :
    (retract τ x).get n i = retract (τ.get n i) (x.get n i) := by
  fun_induction ZFSet.hasArity generalizing τ with
  | case1 => nomatch hx
  | case2 =>
    rcases Fin.fin_one_eq_zero i
    unfold ZFSet.get BType.get
    rfl
  | case3 x n npos hx_pair ih =>
    cases n with
    | zero =>
      rcases Fin.fin_one_eq_zero i
      unfold ZFSet.get BType.get
      rfl
    | succ n =>
      unfold BType.hasArity at hτ
      unfold ZFSet.get BType.get
      split at hτ using α β
      · split_ifs with i_eq hi hi
        · -- i = last: both sides reduce to retract β x.π₂
          rw [BType.toSMTType, SMTType.toZFSet, ZFSet.mem_prod] at hx_mem
          obtain ⟨_, hα, _, hβ, rfl⟩ := hx_mem
          simp only [ZFSet.π₂_pair, retract]
        · nomatch i_eq
        · obtain ⟨i, hi⟩ := i
          cases hi
          simp only [Nat.succ_eq_add_one, Nat.add_eq, add_zero] at i_eq
          nomatch i_eq
        · -- i < last: need IH on α and x.π₁
          rw [BType.toSMTType, SMTType.toZFSet, ZFSet.mem_prod] at hx_mem
          obtain ⟨a, hα, b, hβ, rfl⟩ := hx_mem
          simp only [ZFSet.π₁_pair, retract]
          simp only [π₁_pair] at ih hx
          exact ih hx hτ hα
      · nomatch hτ
  | case4 x n npos hx_not_pair =>
    cases n with
    | zero =>
      rcases Fin.fin_one_eq_zero i
      unfold ZFSet.get BType.get
      rfl
    | succ n =>
      unfold BType.hasArity at hτ
      unfold ZFSet.get BType.get
      split at hτ using α β
      · rw [BType.toSMTType, SMTType.toZFSet, ZFSet.mem_prod] at hx_mem
        nomatch hx
      · nomatch hτ

/-- The tail of `toDestPair vs zp acc d` starting at position `vs.length` is exactly `acc`. -/
theorem toDestPair_drop_eq_acc :
    ∀ (vs : List SMT.𝒱) (zp d : SMT.Term) (acc : List SMT.Term),
    vs ≠ [] → (toDestPair vs zp acc d).drop vs.length = acc := by
  intro vs
  induction vs with
  | nil => nofun
  | cons x xs ih =>
    intro zp d acc _
    cases xs with
    | nil =>
      unfold toDestPair
      simp [List.drop_succ_cons]
    | cons y ys =>
      simp only [List.length_cons, toDestPair]
      cases ys with
      | nil =>
        simp only [List.length_nil, zero_add, Nat.reduceAdd, toDestPair, List.drop_succ_cons,
          List.drop_zero]
      | cons y' ys =>
        -- toDestPair (x :: y :: y' :: ys) zp acc d
        --   = toDestPair (y :: y' :: ys) (.fst d) (.snd d :: acc) (.fst d)
        change (toDestPair (y :: y' :: ys) (.fst d) (.snd d :: acc) (.fst d)).drop
          (y :: y' :: ys).length.succ = acc
        have := ih (.fst d) (.fst d) (.snd d :: acc) (List.cons_ne_nil y (y' :: ys))
        simp only [List.length_cons] at this ⊢
        -- drop (n+1) l = (drop n l).tail
        conv_lhs => rw [show (ys.length + 1 + 1).succ = (ys.length + 1 + 1) + 1 from rfl]
        rw [← List.drop_drop (i := 1), this, List.drop_one, List.tail_cons]

/-- Element at position `vs.length + k` in `toDestPair vs zp acc d` is `acc[k]`. -/
theorem toDestPair_getElem_acc :
    ∀ (vs : List SMT.𝒱) (zp d : SMT.Term) (acc : List SMT.Term)
      (k : ℕ) (hk : k < acc.length),
    vs ≠ [] →
    ∀ (h : vs.length + k < (toDestPair vs zp acc d).length),
    (toDestPair vs zp acc d)[vs.length + k] = acc[k] := by
  intro vs; induction vs with
  | nil => intro _ _ _ _ _ h; exact absurd rfl h
  | cons x xs ih =>
    intro zp d acc k hk _
    cases xs with
    | nil =>
      unfold toDestPair; intro h
      simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.succ_add]
      rfl
    | cons y ys =>
      intro h
      unfold toDestPair
      simp only [List.length_cons]
      have hk1 : k + 1 < (SMT.Term.snd d :: acc).length := by simp; omega
      have h' : (y :: ys).length + (k + 1) <
          (toDestPair (y :: ys) (.fst d) (.snd d :: acc) (.fst d)).length := by
        simp only [List.length_cons] at h ⊢
        rw [toDestPair_length_gen (y :: ys) (.fst d) (.fst d) (.snd d :: acc)
          (List.cons_ne_nil y ys)]
        simpa only [List.length_cons, Nat.add_lt_add_iff_left, Nat.add_lt_add_iff_right]
      have := ih (.fst d) (.fst d) (.snd d :: acc) (k + 1) hk1 (List.cons_ne_nil y ys) h'
      show (toDestPair (y :: ys) (.fst d) (.snd d :: acc) (.fst d))[ys.length + 1 + 1 + k] =
        acc[k]
      convert this using 1
      simp only [List.length_cons]
      conv =>
        enter [2, 2]
        rw [add_comm k 1, ←add_assoc]

/-- `ZFSet.get` step-down: for j not the last index, get at n+2 peels π₁ and reduces to get at n+1. -/
theorem ZFSet_get_step_down {x : ZFSet} {n : ℕ} {j : ℕ}
    (hj : j < n + 2) (hj_small : j < n + 1) :
    x.get (n + 2) ⟨j, hj⟩ = x.π₁.get (n + 1) ⟨j, hj_small⟩ := by
  show (if h : (⟨j, hj⟩ : Fin (n + 2)) = Fin.last (n + 1)
    then x.π₂ else x.π₁.get (n + 1) ((⟨j, hj⟩ : Fin (n + 2)).castPred h)) =
    x.π₁.get (n + 1) ⟨j, hj_small⟩
  rw [dif_neg (by intro heq; simp [Fin.ext_iff, Fin.last] at heq; omega)]
  exact congr_arg (x.π₁.get (n + 1)) (Fin.ext rfl)

/-- `BType.get` step-down: for j not the last index, get at n+2 on a product peels the fst type. -/
theorem BType_get_step_down {α β : BType} {n : ℕ} {j : ℕ}
    (hj : j < n + 2) (hj_small : j < n + 1) :
    BType.get (α ×ᴮ β) (n + 2) ⟨j, hj⟩ = BType.get α (n + 1) ⟨j, hj_small⟩ := by
  show (if h : j = n + 1 then β else α.get (n + 1) ⟨j, by omega⟩) =
    BType.get α (n + 1) ⟨j, hj_small⟩
  rw [dif_neg (by omega)]

/-- Each element of `toDestPair vs d acc d` denotes under `Θ`. For indices `j < vs.length`,
    the denotation value's ZFSet component equals `D_val.fst.get vs.length j` and its type
    component equals `(τ.get vs.length j).toSMTType`. -/
theorem toDestPair_denote_gen.{v} :
    ∀ (τ_B : BType) (vs : List SMT.𝒱) (d : SMT.Term) (D_val : SMT.Dom.{v})
      (Θ : SMT.RenamingContext.Context)
      (acc : List SMT.Term) (Ds_acc : List SMT.Dom.{v}),
    vs ≠ [] →
    (hcov_d : SMT.RenamingContext.CoversFV Θ d) →
    ⟦d.abstract Θ hcov_d⟧ˢ = some D_val →
    D_val.snd.fst = τ_B.toSMTType →
    D_val.fst ∈ ⟦τ_B.toSMTType⟧ᶻ →
    τ_B.hasArity vs.length →
    acc.length = Ds_acc.length →
    (∀ (j : ℕ) (hj : j < acc.length),
      ∃ (hcov : SMT.RenamingContext.CoversFV Θ (acc[j]'(by omega))),
        ⟦(acc[j]'(by omega)).abstract Θ hcov⟧ˢ.isSome = true) →
    ∀ (j : ℕ) (hj_v : j < vs.length) (hj_t : j < (toDestPair vs d acc d).length),
    ∃ (hcov_j : SMT.RenamingContext.CoversFV Θ ((toDestPair vs d acc d)[j]'hj_t))
      (D_j : SMT.Dom.{v}),
      ⟦((toDestPair vs d acc d)[j]'hj_t).abstract Θ hcov_j⟧ˢ = some D_j ∧
      D_j.fst = D_val.fst.get vs.length ⟨j, hj_v⟩ ∧
      D_j.snd.fst = (τ_B.get vs.length ⟨j, hj_v⟩).toSMTType := by
  suffices h : ∀ (vs : List SMT.𝒱) (τ_B : BType) (d : SMT.Term) (D_val : SMT.Dom.{v})
      (Θ : SMT.RenamingContext.Context) (acc : List SMT.Term) (Ds_acc : List SMT.Dom.{v}),
      vs ≠ [] →
      (hcov_d : SMT.RenamingContext.CoversFV Θ d) →
      ⟦d.abstract Θ hcov_d⟧ˢ = some D_val →
      D_val.snd.fst = τ_B.toSMTType →
      D_val.fst ∈ ⟦τ_B.toSMTType⟧ᶻ →
      τ_B.hasArity vs.length →
      acc.length = Ds_acc.length →
      (∀ (j : ℕ) (hj : j < acc.length),
        ∃ (hcov : SMT.RenamingContext.CoversFV Θ (acc[j]'(by omega))),
          ⟦(acc[j]).abstract Θ hcov⟧ˢ.isSome = true) →
      ∀ (j : ℕ) (hj_v : j < vs.length) (hj_t : j < (toDestPair vs d acc d).length),
      ∃ (hcov_j : SMT.RenamingContext.CoversFV Θ ((toDestPair vs d acc d)[j]))
        (D_j : SMT.Dom.{v}),
        ⟦((toDestPair vs d acc d)[j]'hj_t).abstract Θ hcov_j⟧ˢ = some D_j ∧
        D_j.fst = D_val.fst.get vs.length ⟨j, hj_v⟩ ∧
        D_j.snd.fst = (τ_B.get vs.length ⟨j, hj_v⟩).toSMTType by
    intro τ_B vs; exact h vs τ_B
  intro vs
  induction vs with
  | nil => intro _ _ _ _ _ _ hvs; exact absurd rfl hvs
  | cons x xs ih =>
    intro τ_B d D_val Θ acc Ds_acc _ hcov_d hden_d htype_d hmem_d harity hlen_acc hacc j hj_v hj_t
    cases xs with
    | nil =>
      -- vs = [x], toDestPair [x] d acc d = d :: acc
      -- j < 1 means j = 0
      have hj0 : j = 0 := Nat.lt_one_iff.mp hj_v
      subst hj0
      unfold toDestPair
      simp only [List.getElem_cons_zero]
      exact ⟨hcov_d, D_val, hden_d, by unfold ZFSet.get; rfl, by unfold BType.get; exact htype_d⟩
    | cons y ys =>
      -- vs = x :: y :: ys, length = ys.length + 2
      have hvs_len : (x :: y :: ys).length = ys.length + 2 := by simp [List.length_cons]
      rw [hvs_len] at harity
      obtain ⟨α, β, rfl⟩ : ∃ α β, τ_B = .prod α β := by
        cases τ_B with
        | prod α β => exact ⟨α, β, rfl⟩
        | int => exact absurd harity (by unfold BType.hasArity; exact id)
        | bool => exact absurd harity (by unfold BType.hasArity; exact id)
        | set _ => exact absurd harity (by unfold BType.hasArity; exact id)
      rw [BType.hasArity] at harity
      have htype_pair : D_val.snd.fst = SMTType.pair α.toSMTType β.toSMTType := htype_d
      have hmem_pair := hmem_d
      -- Extract pair components from membership
      have hpair_decomp : ∃ a b, D_val.fst = a.pair b ∧ a ∈ ⟦α.toSMTType⟧ᶻ ∧ b ∈ ⟦β.toSMTType⟧ᶻ := by
        rw [BType.toSMTType, SMTType.toZFSet, ZFSet.mem_prod] at hmem_pair
        obtain ⟨a, ha, b, hb, hab⟩ := hmem_pair
        exact ⟨a, b, hab, ha, hb⟩
      obtain ⟨a_val, b_val, hab_eq, ha_mem, hb_mem⟩ := hpair_decomp
      -- CoversFV for SMT.Term.fst d and SMT.Term.snd d
      have hcov_fst : SMT.RenamingContext.CoversFV Θ (SMT.Term.fst d) := by
        intro v hv; exact hcov_d v (by unfold SMT.fv at hv; exact hv)
      have hcov_snd : SMT.RenamingContext.CoversFV Θ (SMT.Term.snd d) := by
        intro v hv; exact hcov_d v (by unfold SMT.fv at hv; exact hv)
      -- Denotation of SMT.Term.fst d
      have hfst_mem : D_val.fst.π₁ ∈ ⟦α.toSMTType⟧ᶻ := by rw [hab_eq, ZFSet.π₁_pair]; exact ha_mem
      -- Decompose D_val to work with its components
      obtain ⟨X_d, σ_d, hX_d⟩ := D_val
      simp only at htype_pair hmem_d hab_eq hfst_mem ⊢
      subst htype_pair
      have hden_fst : ⟦(SMT.Term.fst d).abstract Θ hcov_fst⟧ˢ =
          some ⟨X_d.π₁, α.toSMTType, hfst_mem⟩ := by
        unfold SMT.Term.abstract; simp only [SMT.denote, hden_d]; rfl
      -- Denotation of SMT.Term.snd d
      have hsnd_mem : X_d.π₂ ∈ ⟦β.toSMTType⟧ᶻ := by rw [hab_eq, ZFSet.π₂_pair]; exact hb_mem
      have hden_snd : ⟦(SMT.Term.snd d).abstract Θ hcov_snd⟧ˢ =
          some ⟨X_d.π₂, β.toSMTType, hsnd_mem⟩ := by
        unfold SMT.Term.abstract; simp only [SMT.denote, hden_d]; rfl
      unfold toDestPair
      -- Acc hypothesis for SMT.Term.snd d :: acc
      have hacc' : ∀ (j : ℕ) (hj : j < (SMT.Term.snd d :: acc).length),
          ∃ (hcov : SMT.RenamingContext.CoversFV Θ ((SMT.Term.snd d :: acc)[j]'(by omega))),
            ⟦((SMT.Term.snd d :: acc)[j]'(by omega)).abstract Θ hcov⟧ˢ.isSome = true := by
        intro j' hj'; simp only [List.length_cons] at hj'
        cases j' with
        | zero =>
          simp only [List.getElem_cons_zero]
          exact ⟨hcov_snd, Option.isSome_iff_exists.mpr ⟨_, hden_snd⟩⟩
        | succ k => simp only [List.getElem_cons_succ]; exact hacc k (by omega)
      by_cases hj_small : j < (y :: ys).length
      · -- j < (y :: ys).length: use IH with τ_B := α
        have hj_t' : j < (toDestPair (y :: ys) (SMT.Term.fst d)
            (SMT.Term.snd d :: acc) (SMT.Term.fst d)).length := hj_t
        have := ih α (SMT.Term.fst d)
          ⟨X_d.π₁, α.toSMTType, hfst_mem⟩ Θ (SMT.Term.snd d :: acc)
          ((⟨X_d.π₂, β.toSMTType, hsnd_mem⟩ : SMT.Dom.{v}) :: Ds_acc)
          (List.cons_ne_nil y ys) hcov_fst hden_fst rfl hfst_mem
          harity (by simp [hlen_acc]) hacc' j hj_small hj_t'
        obtain ⟨hcov_j, D_j, hden_j, hfst_j, htype_j⟩ := this
        refine ⟨hcov_j, D_j, hden_j, ?_, ?_⟩
        · conv_rhs =>
            simp only [List.length_cons, get.eq_2]
            rw [dif_neg (Fin.lt_last_iff_ne_last.mp hj_small)]
          rw [hfst_j]
          rfl
        · rw [htype_j]
          conv_rhs =>
            simp only [List.length_cons, BType.get]
            rw [dif_neg (by exact Nat.ne_of_lt hj_small)]
          rfl
      · -- j = (y :: ys).length: the element is SMT.Term.snd d (from the accumulator)
        push_neg at hj_small
        have hj_eq : j = ys.length + 1 := by
          simp only [List.length_cons] at hj_v hj_small
          exact Nat.eq_of_le_of_lt_succ hj_small hj_v
        subst hj_eq
        have helem : (toDestPair (y :: ys) (SMT.Term.fst d)
            (SMT.Term.snd d :: acc) (SMT.Term.fst d))[ys.length + 1]'hj_t =
            SMT.Term.snd d := by
          induction ys with
          | nil =>
            simp only [toDestPair, List.length_nil, zero_add, List.getElem_cons_succ,
              List.getElem_cons_zero]
          | cons y' ys ih_ys =>
            simp only [toDestPair, List.length_cons]
            have h_len : (y' :: ys).length + 1 <
                (toDestPair (y' :: ys) (SMT.Term.fst (SMT.Term.fst d))
                  (SMT.Term.snd (SMT.Term.fst d) :: SMT.Term.snd d :: acc)
                  (SMT.Term.fst (SMT.Term.fst d))).length := by
              rw [toDestPair_length_gen _ _ _ _ (List.cons_ne_nil y' ys)]
              simp [List.length_cons]
            have := toDestPair_getElem_acc (y' :: ys) (SMT.Term.fst (SMT.Term.fst d))
              (SMT.Term.fst (SMT.Term.fst d))
              (SMT.Term.snd (SMT.Term.fst d) :: SMT.Term.snd d :: acc) 1
              (by simp) (List.cons_ne_nil y' ys) h_len
            erw [this]
            rfl
        simp only [helem]
        refine ⟨hcov_snd, ⟨X_d.π₂, β.toSMTType, hsnd_mem⟩, hden_snd, ?_, ?_⟩
        · simp only [List.length_cons, ZFSet.get]
          rw [dif_pos (by rfl)]
        · simp only [List.length_cons]
          rw [BType.get, dif_pos rfl]

/-! ### Factored retract-lambda lemma for collect

This lemma abstracts the `retract τ.set lamVal.fst = T` proof.
It takes a generic renaming context `Δ_ctx` and a "semantic bridge" hypothesis
`hbridge` that connects the ite body evaluation to the B-level predicate,
and proves the retract equality via ZFSet.ext + the lambda↔body bridge.

This avoids duplicating the ~1000-line forward+backward proof for both
the original Δ' and the alternative Δ'_alt.
-/
open Classical in
set_option maxHeartbeats 4000000 in
theorem retract_lamVal_eq_collect.{u}
    -- Type infrastructure
    {vs : List B.𝒱} (vs_nemp : vs ≠ []) (vs_nodup : vs.Nodup)
    {τ : BType} (τ_hasArity : τ.hasArity vs.length)
    -- SMT terms
    {D : B.Term}
    {D_enc P_enc : SMT.Term} {z : SMT.𝒱}
    {ite_body : SMT.Term}
    (ite_body_def : ite_body = ((@ˢD_enc) (.var z)).ite
      (SMT.substList vs (toDestPair vs (.var z)) P_enc) (.bool false))
    -- z not free in D_enc/P_enc
    (z_not_fv_D : z ∉ SMT.fv D_enc)
    -- Renaming context and lambda value
    {Δ_ctx : SMT.RenamingContext.Context}
    (hcov_lambda : SMT.RenamingContext.CoversFV Δ_ctx ((λˢ [z]) [τ.toSMTType] ite_body))
    {lamVal : SMT.Dom}
    (hlamVal : ⟦((λˢ [z]) [τ.toSMTType] ite_body).abstract Δ_ctx hcov_lambda⟧ˢ = some lamVal)
    (hlamVal_func : ⟦τ.toSMTType⟧ᶻ.IsFunc 𝔹 lamVal.fst)
    -- D_enc denotation data
    {denD_val : SMT.Dom}
    (hcov_D_upd : ∀ Xarg : SMT.Dom,
      SMT.RenamingContext.CoversFV (Function.update Δ_ctx z (some Xarg)) D_enc)
    (den_D_upd_eq : ∀ Xarg : SMT.Dom,
      ⟦D_enc.abstract (Function.update Δ_ctx z (some Xarg)) (hcov_D_upd Xarg)⟧ˢ = some denD_val)
    (denD_val_type : denD_val.snd.fst = τ.toSMTType.fun SMTType.bool)
    (denD_val_func : ⟦τ.toSMTType⟧ᶻ.IsFunc 𝔹 denD_val.fst)
    {𝒟_val : ZFSet.{u}} (h𝒟_val : 𝒟_val ∈ ⟦τ.set⟧ᶻ)
    (denD_val_retract : retract τ.set denD_val.fst = 𝒟_val)
    -- Body totality/typing
    (hcov_ite_upd : ∀ W : SMT.Dom,
      SMT.RenamingContext.CoversFV (Function.update Δ_ctx z (some W)) ite_body)
    (hbody_total : ∀ W : SMT.Dom, W.snd.fst = τ.toSMTType →
      ⟦ite_body.abstract (Function.update Δ_ctx z (some W)) (hcov_ite_upd W)⟧ˢ.isSome = true)
    (hbody_ty : ∀ W : SMT.Dom, W.snd.fst = τ.toSMTType →
      ∀ Db : SMT.Dom,
        ⟦ite_body.abstract (Function.update Δ_ctx z (some W)) (hcov_ite_upd W)⟧ˢ = some Db →
        Db.snd.fst = SMTType.bool)
    -- substList coverage and FV
    (hcov_substList_upd : ∀ W : SMT.Dom,
      SMT.RenamingContext.CoversFV (Function.update Δ_ctx z (some W))
        (SMT.substList vs (toDestPair vs (.var z)) P_enc))
    (fv_substList_disj_vs : ∀ v ∈ SMT.fv (SMT.substList vs (toDestPair vs (.var z)) P_enc),
      v ≠ z → v ∉ vs)
    (hgo_cov : ∀ x ∈ SMT.fv ite_body, x ∉ [z] → (Δ_ctx x).isSome = true)
    -- B-level data
    {P : B.Term} {«Δ» : B.RenamingContext.Context}
    (Δ_fv_collect : ∀ v ∈ B.fv (Term.collect vs D P), («Δ» v).isSome = true)
    -- B-level sep = T_val
    {T_val : ZFSet.{u}}
    (hT_eq : ZFSet.sep (fun x =>
      if hx : x.hasArity vs.length ∧ τ.hasArity vs.length ∧ x ∈ ⟦τ⟧ᶻ then
        match ⟦(B.Term.abstract.go P vs «Δ» (fun v hv hvs => Δ_fv_collect v
          (B.fv.mem_collect (.inr ⟨hv, hvs⟩)))).uncurry
          (fun i => ⟨x.get vs.length i, ⟨τ.get vs.length i,
            get_mem_type_of_isTuple hx.1 hx.2.1 hx.2.2⟩⟩)⟧ᴮ with
        | some ⟨Pz, _⟩ => Pz = zftrue
        | none => False
      else False) 𝒟_val = T_val)
    -- P denotability for all x ∈ 𝒟_val
    (h_den_P : ∀ {x_fin : Fin vs.length → B.Dom},
      (∀ i, (x_fin i).snd.fst = τ.get vs.length i ∧
            (x_fin i).fst ∈ ⟦τ.get vs.length i⟧ᶻ) →
      ofFinDom x_fin ∈ 𝒟_val →
      ⟦(B.Term.abstract.go P vs «Δ» (fun v hv hvs => Δ_fv_collect v
        (B.fv.mem_collect (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ.isSome = true)
    -- *** THE SEMANTIC BRIDGE ***
    -- For each x ∈ 𝒟_val with canonical Wx, the ite body result
    -- corresponds to the B-level P predicate at x
    (hbridge : ∀ (x : ZFSet.{u}) (hx_mem : x ∈ ⟦τ⟧ᶻ) (hx_𝒟 : x ∈ 𝒟_val),
      let Wx : SMT.Dom := ⟨(ZFSet.fapply (BType.canonicalIsoSMTType τ).1
        (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType τ).2.1)
        ⟨x, by rwa [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType τ).2.1]⟩).1,
        τ.toSMTType, ZFSet.fapply_mem_range _ _⟩
      let x_fin : Fin vs.length → B.Dom := fun i =>
        ⟨x.get vs.length i, ⟨τ.get vs.length i,
          get_mem_type_of_isTuple (hasArity_of_mem_toZFSet τ_hasArity hx_mem) τ_hasArity hx_mem⟩⟩
      -- For any body_val from ite_body at Wx:
      ∀ body_val : SMT.Dom,
        ⟦ite_body.abstract (Function.update Δ_ctx z (some Wx)) (hcov_ite_upd Wx)⟧ˢ = some body_val →
        -- body_val.fst = zftrue iff P(x) evaluates to zftrue
        (body_val.fst = zftrue ↔
          (∀ (Px : ZFSet.{u}) (P_ty : BType) (hP_val : Px ∈ ⟦P_ty⟧ᶻ),
            ⟦(B.Term.abstract.go P vs «Δ» (fun v hv hvs => Δ_fv_collect v
              (B.fv.mem_collect (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ =
              some ⟨Px, ⟨P_ty, hP_val⟩⟩ → Px = zftrue)))
    : retract τ.set lamVal.fst = T_val := by
  rw [← hT_eq]
  -- Show extensional equality via ZFSet.ext
  apply ZFSet.ext; intro x
  rw [retract, ZFSet.mem_sep, ZFSet.mem_sep]
  -- Establish subset: 𝒟_val ⊆ ⟦τ⟧ᶻ
  have h𝒟_sub : 𝒟_val ⊆ ⟦τ⟧ᶻ := by
    rwa [BType.toZFSet, ZFSet.mem_powerset] at h𝒟_val
  -- Key bridge: for any W of type τ.toSMTType, the lambda
  -- fapply equals the body evaluation
  have lamVal_body_bridge : ∀ (W : SMT.Dom),
      W.snd.fst = τ.toSMTType → W.fst ∈ ⟦τ.toSMTType⟧ᶻ →
      ∃ (body_val : SMT.Dom),
        ⟦ite_body.abstract (Function.update Δ_ctx z (some W))
          (hcov_ite_upd W)⟧ˢ = some body_val ∧
        body_val.snd.fst = SMTType.bool ∧
        body_val.fst ∈ 𝔹 := by
    intro W hW_ty hW_mem
    obtain ⟨bv, hbv⟩ := Option.isSome_iff_exists.mp (hbody_total W hW_ty)
    have hbv_ty := hbody_ty W hW_ty bv hbv
    have hbv_mem : bv.fst ∈ 𝔹 := by
      have := bv.snd.snd; rw [hbv_ty, SMTType.toZFSet] at this; exact this
    exact ⟨bv, hbv, hbv_ty, hbv_mem⟩
  constructor
  · -- Forward: x ∈ retract → x ∈ T
    intro ⟨hx_mem, hx_pred⟩
    rw [dif_pos hx_mem, dif_pos hlamVal_func] at hx_pred
    -- Step 1: Build canonical witness Wx for x
    have hx_canon_mem : (ZFSet.fapply (BType.canonicalIsoSMTType τ).1
        (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType τ).2.1)
        ⟨x, by rwa [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType τ).2.1]⟩).1 ∈
        ⟦τ.toSMTType⟧ᶻ :=
      ZFSet.fapply_mem_range _ _
    let Wx : SMT.Dom := ⟨_, τ.toSMTType, hx_canon_mem⟩
    have hWx_ty : Wx.snd.fst = τ.toSMTType := rfl
    have hWx_mem : Wx.fst ∈ ⟦τ.toSMTType⟧ᶻ := hx_canon_mem
    -- Step 2: Get D_enc app and body evaluation at Wx
    obtain ⟨_, Dapp_x, hDapp_x_ty, hDapp_x_val, hDapp_x_den⟩ :=
      funDenoteAppAt (Δctx := Δ_ctx) (t := D_enc) (x := z)
        (α := τ.toSMTType) (β := .bool) (Y := denD_val)
        hcov_D_upd den_D_upd_eq denD_val_type
        denD_val_func Wx hWx_ty hWx_mem
    obtain ⟨body_val, hbody_val, hbody_val_ty, hbody_val_mem⟩ :=
      lamVal_body_bridge Wx hWx_ty hWx_mem
    have hDapp_x_mem_𝔹 : Dapp_x.fst ∈ 𝔹 := by
      have := Dapp_x.snd.snd; rw [hDapp_x_ty] at this; exact this
    -- Step 3: body_val.fst = zftrue (from hx_pred and lambda structure)
    have hbody_val_eq_zftrue : body_val.fst = zftrue := by
      have hlamVal' := hlamVal
      rw [SMT.Term.abstract, dif_pos (by rfl)] at hlamVal'
      simp only [SMT.denote] at hlamVal'
      rw [dif_pos (show [z].length > 0 by exact Nat.zero_lt_succ 0)] at hlamVal'
      split_ifs at hlamVal' with h_isSome h_typ_det
      · let xd : Fin 1 → SMT.Dom :=
          fun _ => ⟨τ.toSMTType.defaultZFSet, τ.toSMTType, SMTType.mem_toZFSet_of_defaultZFSet⟩
        have hxd_spec : ∀ i, (xd i).2.1 = [τ.toSMTType][↑i] ∧ (xd i).1 ∈ ⟦[τ.toSMTType][↑i]⟧ᶻ := by
          intro ⟨i, hi⟩; simp at hi; subst hi
          exact ⟨rfl, SMTType.mem_toZFSet_of_defaultZFSet⟩
        have hgo_d := funAbstractGoSingle (Δctx := Δ_ctx) (P := ite_body) (v := z) (τ := τ.toSMTType)
          hgo_cov hcov_ite_upd xd hxd_spec
        obtain ⟨Dd, hDd⟩ := Option.isSome_iff_exists.mp
          (hbody_total (xd ⟨0, Nat.one_pos⟩) rfl)
        have hden_d : ⟦(SMT.Term.abstract.go ite_body [z] Δ_ctx hgo_cov).uncurry xd⟧ˢ = some Dd := by
          rw [hgo_d]; exact hDd
        have hγ_out : (⟦(SMT.Term.abstract.go ite_body [z] Δ_ctx hgo_cov).uncurry xd⟧ˢ.get
            (h_isSome hxd_spec)).snd.fst = .bool := by
          rw [congrArg (·.snd.fst) (Option.get_of_eq_some _ hden_d)]
          exact hbody_ty (xd ⟨0, Nat.one_pos⟩) rfl Dd hDd
        simp only [Option.pure_def, Option.some.injEq] at hlamVal'
        have hlamVal_fst_eq : lamVal.fst = _ := congrArg (·.fst) hlamVal'.symm
        simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.sub_self,
          Fin.foldr_zero, List.getElem_cons_zero] at hlamVal_fst_eq
        have h_pair_mem : Wx.fst.pair body_val.fst ∈ lamVal.fst := by
          rw [hlamVal_fst_eq, ZFSet.mem_lambda]
          refine ⟨Wx.fst, body_val.fst, rfl, hWx_mem, ?_, ?_⟩
          · have := body_val.snd.snd; rw [hbody_val_ty] at this; convert this using 2
          · split_ifs with hw'_cond
            · let xₙ := fun i : Fin 1 => (⟨Wx.fst.get 1 i, [τ.toSMTType][↑i], hw'_cond.2 i⟩ : SMT.Dom)
              have hgo' := funAbstractGoSingle (Δctx := Δ_ctx) (P := ite_body) (v := z) (τ := τ.toSMTType)
                hgo_cov hcov_ite_upd xₙ (fun i => ⟨rfl, hw'_cond.2 i⟩)
              have hxₙ_eq : xₙ ⟨0, Nat.zero_lt_one⟩ = Wx := rfl
              have hden' : ⟦(SMT.Term.abstract.go ite_body [z] Δ_ctx hgo_cov).uncurry xₙ⟧ˢ = some body_val := by
                rw [hgo', hxₙ_eq]; exact hbody_val
              exact (congrArg (·.fst) (Option.get_of_eq_some _ hden')).symm
            · exfalso; apply hw'_cond
              exact ⟨trivial, fun ⟨i, hi⟩ => by
                have : i = 0 := Nat.lt_one_iff.mp hi; subst this; exact hWx_mem⟩
        have h_fapply := ZFSet.fapply.of_pair (ZFSet.is_func_is_pfunc hlamVal_func) h_pair_mem
        rw [Subtype.ext_iff] at h_fapply
        exact h_fapply.symm.trans hx_pred
    -- Step 4: D_enc condition must be true (false branch gives zffalse)
    have hcond_true :
        ZFSet.ZFBool.toBool ⟨Dapp_x.fst, hDapp_x_mem_𝔹⟩ = true := by
      by_contra hcond_false
      have hcond_eq_false :
          ZFSet.ZFBool.toBool ⟨Dapp_x.fst, hDapp_x_mem_𝔹⟩ = false :=
        eq_false_of_ne_true hcond_false
      have hfalse_body :
          ⟦ite_body.abstract (Function.update Δ_ctx z (some Wx))
            (hcov_ite_upd Wx)⟧ˢ =
          some ⟨ZFSet.zffalse, .bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
        conv_lhs => rw [show ite_body.abstract (Function.update Δ_ctx z (some Wx)) (hcov_ite_upd Wx) =
          (((@ˢD_enc) (SMT.Term.var z)).ite
            (SMT.substList vs (toDestPair vs (.var z)) P_enc) (.bool false)).abstract
            (Function.update Δ_ctx z (some Wx)) (ite_body_def ▸ hcov_ite_upd Wx) by
          subst ite_body_def; rfl]
        simp only [SMT.Term.abstract, SMT.denote, Option.bind_eq_bind]
        conv_lhs => rw [SMT.RenamingContext.denote_abstract_proof_irrel
          D_enc (Function.update Δ_ctx z (some Wx)) _ (hcov_D_upd Wx)]
        rw [den_D_upd_eq Wx]
        simp only [Option.bind_some, Function.update_self,
          Option.get_some, Option.pure_def, hWx_ty]
        have hDapp_x_den' := hDapp_x_den
        simp only [SMT.Term.abstract, SMT.denote,
          Option.bind_eq_bind] at hDapp_x_den'
        conv at hDapp_x_den' =>
          lhs; rw [SMT.RenamingContext.denote_abstract_proof_irrel
            D_enc _ _ (hcov_D_upd Wx)]
        rw [den_D_upd_eq Wx] at hDapp_x_den'
        simp only [Function.update_self, Option.get_some,
          Option.pure_def, Option.bind_some, hWx_ty] at hDapp_x_den'
        rw [hDapp_x_den']
        simp only [Option.bind_some]
        have : Dapp_x =
            ⟨Dapp_x.fst, ⟨.bool, hDapp_x_ty ▸ Dapp_x.snd.snd⟩⟩ := by
          obtain ⟨_, ⟨_, _⟩⟩ := Dapp_x; cases hDapp_x_ty; rfl
        rw [this]; dsimp
        rw [show ZFSet.ZFBool.toBool ⟨Dapp_x.fst, _⟩ = false
          from hcond_eq_false]
        simp [ZFSet.ZFBool.ofBool]
      rw [hfalse_body] at hbody_val
      have hfst_eq : body_val.fst = ZFSet.zffalse :=
        congrArg (·.fst) (Option.some.inj hbody_val).symm
      exact absurd (hfst_eq ▸ hbody_val_eq_zftrue)
        (Ne.symm ZFSet.zftrue_ne_zffalse)
    -- Step 5: Show x ∈ 𝒟_val
    have hDapp_fst_true : Dapp_x.fst = zftrue := by
      rcases ZFSet.ZFBool.mem_𝔹_iff _ |>.mp hDapp_x_mem_𝔹 with h | h
      · exfalso
        have : ZFSet.ZFBool.toBool ⟨Dapp_x.fst, hDapp_x_mem_𝔹⟩ = false := by
          rw [show (⟨Dapp_x.fst, hDapp_x_mem_𝔹⟩ : ZFSet.ZFBool) =
            ⟨ZFSet.zffalse, ZFSet.ZFBool.zffalse_mem_𝔹⟩ from Subtype.ext h]
          exact ZFSet.ZFBool.toBool_false
        rw [this] at hcond_true; nomatch hcond_true
      · exact h
    have hx_in_𝒟 : x ∈ 𝒟_val := by
      rw [← denD_val_retract, retract, ZFSet.mem_sep]
      constructor
      · exact hx_mem
      · rw [dif_pos hx_mem, dif_pos denD_val_func]
        convert hDapp_fst_true using 1
        exact hDapp_x_val.symm
    -- Step 6: Show B-level P evaluation = zftrue using hbridge
    constructor
    · exact hx_in_𝒟
    · rw [dif_pos ⟨hasArity_of_mem_toZFSet τ_hasArity hx_mem,
          τ_hasArity, hx_mem⟩]
      let x_fin : Fin vs.length → B.Dom := fun i =>
        ⟨x.get vs.length ↑i, ⟨τ.get vs.length ↑i,
         get_mem_type_of_isTuple
           (hasArity_of_mem_toZFSet τ_hasArity hx_mem)
           τ_hasArity hx_mem⟩⟩
      have h_ofFinDom_eq : ZFSet.ofFinDom x_fin = x :=
        ZFSet.ofFinDom_get (List.length_pos_iff.mpr vs_nemp)
          (fun i => get_mem_type_of_isTuple
            (hasArity_of_mem_toZFSet τ_hasArity hx_mem)
            τ_hasArity hx_mem)
          (hasArity_of_mem_toZFSet τ_hasArity hx_mem) τ_hasArity
      have hx_fin_in_𝒟 : ZFSet.ofFinDom x_fin ∈ 𝒟_val :=
        h_ofFinDom_eq ▸ hx_in_𝒟
      have hx_fin_typ : ∀ i, (x_fin i).snd.fst = τ.get vs.length i ∧
          (x_fin i).fst ∈ ⟦τ.get vs.length i⟧ᶻ :=
        fun i => ⟨rfl, (x_fin i).snd.snd⟩
      have hP_isSome := h_den_P hx_fin_typ hx_fin_in_𝒟
      obtain ⟨⟨P_val, P_ty, hP_val⟩, hP_den⟩ := Option.isSome_iff_exists.mp hP_isSome
      -- Use hbridge to transfer body_val.fst = zftrue to P predicate
      have hbridge_fwd := (hbridge x hx_mem hx_in_𝒟 body_val hbody_val).mp hbody_val_eq_zftrue
      split
      · rename_i Px τPx hPx den_P_eq_Px
        unfold x_fin at hP_den
        conv at den_P_eq_Px => erw [hP_den, Option.some_inj]
        injection den_P_eq_Px with den_P_eq_Px
        subst P_val
        exact hbridge_fwd τPx P_ty hP_val hP_den
      · -- contradiction
        rename_i den_P_eq_none
        unfold x_fin at hP_den
        conv at den_P_eq_none => erw [hP_den]
        nomatch den_P_eq_none
  · -- Backward: x ∈ T → x ∈ retract
    intro ⟨hx_𝒟, hx_pred⟩
    have hx_mem : x ∈ ⟦τ⟧ᶻ := h𝒟_sub hx_𝒟
    refine ⟨hx_mem, ?_⟩
    rw [dif_pos hx_mem, dif_pos hlamVal_func]
    -- Step 1: Build canonical witness Wx for x
    have hx_canon_mem : (ZFSet.fapply (BType.canonicalIsoSMTType τ).1
        (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType τ).2.1)
        ⟨x, by rwa [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType τ).2.1]⟩).1 ∈
        ⟦τ.toSMTType⟧ᶻ :=
      ZFSet.fapply_mem_range _ _
    let Wx : SMT.Dom := ⟨_, τ.toSMTType, hx_canon_mem⟩
    have hWx_ty : Wx.snd.fst = τ.toSMTType := rfl
    have hWx_mem : Wx.fst ∈ ⟦τ.toSMTType⟧ᶻ := hx_canon_mem
    -- Step 2: Get D_enc app and body evaluation at Wx
    obtain ⟨_, Dapp_x, hDapp_x_ty, hDapp_x_val, hDapp_x_den⟩ :=
      funDenoteAppAt (Δctx := Δ_ctx) (t := D_enc) (x := z)
        (α := τ.toSMTType) (β := .bool) (Y := denD_val)
        hcov_D_upd den_D_upd_eq denD_val_type
        denD_val_func Wx hWx_ty hWx_mem
    obtain ⟨body_val, hbody_val, hbody_val_ty, hbody_val_mem⟩ :=
      lamVal_body_bridge Wx hWx_ty hWx_mem
    have hDapp_x_mem_𝔹 : Dapp_x.fst ∈ 𝔹 := by
      have := Dapp_x.snd.snd; rw [hDapp_x_ty] at this; exact this
    -- Step 3: D_enc condition is true (from x ∈ 𝒟_val)
    have hDapp_fst_true : Dapp_x.fst = zftrue := by
      have hx_in_retract : x ∈ retract (BType.set τ) denD_val.fst := by
        rw [denD_val_retract]; exact hx_𝒟
      rw [retract, ZFSet.mem_sep] at hx_in_retract
      obtain ⟨_, hx_retract_pred⟩ := hx_in_retract
      rw [dif_pos hx_mem, dif_pos denD_val_func] at hx_retract_pred
      rw [hDapp_x_val]
      convert hx_retract_pred using 1
    have hcond_true :
        ZFSet.ZFBool.toBool ⟨Dapp_x.fst, hDapp_x_mem_𝔹⟩ = true := by
      rw [show (⟨Dapp_x.fst, hDapp_x_mem_𝔹⟩ : ZFSet.ZFBool) =
        ⟨ZFSet.zftrue, ZFSet.ZFBool.zftrue_mem_𝔹⟩ from Subtype.ext hDapp_fst_true]
      exact ZFSet.ZFBool.toBool_true
    -- Step 4: Decompose hx_pred to get Px = zftrue
    rw [dif_pos ⟨hasArity_of_mem_toZFSet τ_hasArity hx_mem,
        τ_hasArity, hx_mem⟩] at hx_pred
    let x_fin : Fin vs.length → B.Dom := fun i =>
      ⟨x.get vs.length ↑i, ⟨τ.get vs.length ↑i,
       get_mem_type_of_isTuple
         (hasArity_of_mem_toZFSet τ_hasArity hx_mem)
         τ_hasArity hx_mem⟩⟩
    have h_ofFinDom_eq : ZFSet.ofFinDom x_fin = x :=
      ZFSet.ofFinDom_get (List.length_pos_iff.mpr vs_nemp)
        (fun i => get_mem_type_of_isTuple
          (hasArity_of_mem_toZFSet τ_hasArity hx_mem)
          τ_hasArity hx_mem)
        (hasArity_of_mem_toZFSet τ_hasArity hx_mem) τ_hasArity
    have hx_fin_in_𝒟 : ZFSet.ofFinDom x_fin ∈ 𝒟_val :=
      h_ofFinDom_eq ▸ hx_𝒟
    have hx_fin_typ : ∀ i, (x_fin i).snd.fst = τ.get vs.length i ∧
        (x_fin i).fst ∈ ⟦τ.get vs.length i⟧ᶻ :=
      fun i => ⟨rfl, (x_fin i).snd.snd⟩
    have hP_isSome := h_den_P hx_fin_typ hx_fin_in_𝒟
    obtain ⟨⟨P_val, P_ty, hP_val⟩, hP_den⟩ := Option.isSome_iff_exists.mp hP_isSome
    -- Extract Px = zftrue from hx_pred via split/match
    split at hx_pred
    · rename_i Px τPx hPx den_P_eq_Px
      unfold x_fin at hP_den
      conv at den_P_eq_Px => erw [hP_den, Option.some_inj]
      injection den_P_eq_Px with den_P_eq_Px
      subst P_val
      -- Now hx_pred : Px = zftrue (where Px is the match-bound value)
      -- Use hbridge backward: Px = zftrue → body_val.fst = zftrue
      have hbody_val_eq_zftrue : body_val.fst = zftrue := by
        apply (hbridge x hx_mem hx_𝒟 body_val hbody_val).mpr
        intro Px' P_ty' hP_val' hP_den'
        -- hP_den and hP_den' both evaluate the same expression
        rw [show ⟦(B.Term.abstract.go P vs «Δ» (fun v hv hvs => Δ_fv_collect v
            (B.fv.mem_collect (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ =
            ⟦(B.Term.abstract.go P vs «Δ» (fun v hv hvs => Δ_fv_collect v
            (B.fv.mem_collect (.inr ⟨hv, hvs⟩)))).uncurry
            (fun i => ⟨x.get vs.length i, ⟨τ.get vs.length i,
              get_mem_type_of_isTuple (hasArity_of_mem_toZFSet τ_hasArity hx_mem) τ_hasArity hx_mem⟩⟩)⟧ᴮ
            from rfl] at hP_den
        rw [hP_den] at hP_den'
        have hinj := congrArg PSigma.fst (Option.some.inj hP_den')
        dsimp at hinj
        rw [← hinj]; exact hx_pred
      -- Lambda bridge: fapply lamVal.fst Wx = body_val.fst
      have hlamVal' := hlamVal
      rw [SMT.Term.abstract, dif_pos (by rfl)] at hlamVal'
      simp only [SMT.denote] at hlamVal'
      rw [dif_pos (show [z].length > 0 by exact Nat.zero_lt_succ 0)] at hlamVal'
      split_ifs at hlamVal' with h_isSome h_typ_det
      · let xd : Fin 1 → SMT.Dom :=
          fun _ => ⟨τ.toSMTType.defaultZFSet, τ.toSMTType, SMTType.mem_toZFSet_of_defaultZFSet⟩
        have hxd_spec : ∀ i, (xd i).2.1 = [τ.toSMTType][↑i] ∧ (xd i).1 ∈ ⟦[τ.toSMTType][↑i]⟧ᶻ := by
          intro ⟨i, hi⟩; simp at hi; subst hi
          exact ⟨rfl, SMTType.mem_toZFSet_of_defaultZFSet⟩
        have hgo_d := funAbstractGoSingle (Δctx := Δ_ctx) (P := ite_body) (v := z) (τ := τ.toSMTType)
          hgo_cov hcov_ite_upd xd hxd_spec
        obtain ⟨Dd, hDd⟩ := Option.isSome_iff_exists.mp
          (hbody_total (xd ⟨0, Nat.one_pos⟩) rfl)
        have hden_d : ⟦(SMT.Term.abstract.go ite_body [z] Δ_ctx hgo_cov).uncurry xd⟧ˢ = some Dd := by
          rw [hgo_d]; exact hDd
        have hγ_out : (⟦(SMT.Term.abstract.go ite_body [z] Δ_ctx hgo_cov).uncurry xd⟧ˢ.get
            (h_isSome hxd_spec)).snd.fst = .bool := by
          rw [congrArg (·.snd.fst) (Option.get_of_eq_some _ hden_d)]
          exact hbody_ty (xd ⟨0, Nat.one_pos⟩) rfl Dd hDd
        simp only [Option.pure_def, Option.some.injEq] at hlamVal'
        have hlamVal_fst_eq : lamVal.fst = _ := congrArg (·.fst) hlamVal'.symm
        simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.sub_self,
          Fin.foldr_zero, List.getElem_cons_zero] at hlamVal_fst_eq
        have h_pair_mem : Wx.fst.pair body_val.fst ∈ lamVal.fst := by
          rw [hlamVal_fst_eq, ZFSet.mem_lambda]
          refine ⟨Wx.fst, body_val.fst, rfl, hWx_mem, ?_, ?_⟩
          · have := body_val.snd.snd; rw [hbody_val_ty] at this; convert this using 2
          · split_ifs with hw'_cond
            · let xₙ := fun i : Fin 1 => (⟨Wx.fst.get 1 i, [τ.toSMTType][↑i], hw'_cond.2 i⟩ : SMT.Dom)
              have hgo' := funAbstractGoSingle (Δctx := Δ_ctx) (P := ite_body) (v := z) (τ := τ.toSMTType)
                hgo_cov hcov_ite_upd xₙ (fun i => ⟨rfl, hw'_cond.2 i⟩)
              have hxₙ_eq : xₙ ⟨0, Nat.zero_lt_one⟩ = Wx := rfl
              have hden' : ⟦(SMT.Term.abstract.go ite_body [z] Δ_ctx hgo_cov).uncurry xₙ⟧ˢ = some body_val := by
                rw [hgo', hxₙ_eq]; exact hbody_val
              exact (congrArg (·.fst) (Option.get_of_eq_some _ hden')).symm
            · exfalso; apply hw'_cond
              exact ⟨trivial, fun ⟨i, hi⟩ => by
                have : i = 0 := Nat.lt_one_iff.mp hi; subst this; exact hWx_mem⟩
        have h_fapply := ZFSet.fapply.of_pair (ZFSet.is_func_is_pfunc hlamVal_func) h_pair_mem
        rw [Subtype.ext_iff] at h_fapply
        exact h_fapply.trans hbody_val_eq_zftrue
    · -- contradiction
      rename_i den_P_eq_none
      unfold x_fin at hP_den
      conv at den_P_eq_none => erw [hP_den]
      nomatch den_P_eq_none

/-! ### Factored hbridge lemma for collect_case

This lemma proves the `hbridge` condition required by `retract_lamVal_eq_collect`.
It connects the SMT-level ite_body evaluation to the B-level predicate P via the
substList transfer chain and `P_enc_total`.

**Key design: hybrid base approach.** For each x in the domain:
- Build `Δ_D_ext_x := updates Δ_D_eval vs (toSMT Δ_ext_x vs[i])`
- Build hybrid base `Δ₀_hybrid_x` that:
  - At vs positions: uses Δ_D_ext_x (bound variable substitutions)
  - At other used_St₃ positions: uses Δ_ctx (the evaluation context)
  - Elsewhere: none (satisfying none_out)
- Invoke P_enc_total with Δ₀_hybrid_x to get Δ_P_x extending it
- DIRECT transfer from Δ_ctx to Δ_P_x: for v ∈ fv(substList)\{z}\vs,
  `Δ_ctx v = Δ₀_hybrid_x v` (since v ∈ used_St₃), and
  `Δ_P_x v = Δ₀_hybrid_x v` (from Extends), so `Δ_ctx v = Δ_P_x v`.
  No intermediate Δ_P needed!
-/
open Classical in
set_option maxHeartbeats 8000000 in
theorem collect_hbridge.{u}
    -- Type infrastructure
    {vs : List B.𝒱} (vs_nemp : vs ≠ []) (vs_nodup : vs.Nodup)
    {τ : BType} (τ_hasArity : τ.hasArity vs.length)
    -- SMT terms
    {D : B.Term}
    {D_enc P_enc : SMT.Term} {z : SMT.𝒱}
    {ite_body : SMT.Term}
    (ite_body_def : ite_body = ((@ˢD_enc) (.var z)).ite
      (SMT.substList vs (toDestPair vs (.var z)) P_enc) (.bool false))
    -- z not free in D_enc/P_enc, z ∉ vs
    (z_not_fv_D : z ∉ SMT.fv D_enc)
    (z_not_fv_P : z ∉ SMT.fv P_enc)
    (z_not_vs : z ∉ vs)
    -- vs disjoint from B.fv D
    (vs_not_D_fv : ∀ v ∈ vs, v ∉ B.fv D)
    -- BV constraints (from typing: bv of well-typed terms are disjoint from context)
    (hvs_not_bv_P : ∀ v ∈ vs, v ∉ SMT.bv P_enc)
    (z_not_bv_P : z ∉ SMT.bv P_enc)
    -- Renaming context for ite_body evaluation
    {Δ_ctx : SMT.RenamingContext.Context}
    (hcov_ite_upd : ∀ W : SMT.Dom,
      SMT.RenamingContext.CoversFV (Function.update Δ_ctx z (some W)) ite_body)
    -- D_enc denotation data (parametric in z-update)
    {denD_val : SMT.Dom}
    (hcov_D_upd : ∀ Xarg : SMT.Dom,
      SMT.RenamingContext.CoversFV (Function.update Δ_ctx z (some Xarg)) D_enc)
    (den_D_upd_eq : ∀ Xarg : SMT.Dom,
      ⟦D_enc.abstract (Function.update Δ_ctx z (some Xarg)) (hcov_D_upd Xarg)⟧ˢ = some denD_val)
    (denD_val_type : denD_val.snd.fst = τ.toSMTType.fun SMTType.bool)
    (denD_val_func : ⟦τ.toSMTType⟧ᶻ.IsFunc 𝔹 denD_val.fst)
    {𝒟_val : ZFSet.{u}} (h𝒟_val : 𝒟_val ∈ ⟦τ.set⟧ᶻ)
    (denD_val_retract : retract τ.set denD_val.fst = 𝒟_val)
    -- substList coverage and FV
    (hcov_substList_upd : ∀ W : SMT.Dom,
      SMT.RenamingContext.CoversFV (Function.update Δ_ctx z (some W))
        (SMT.substList vs (toDestPair vs (.var z)) P_enc))
    (fv_substList_disj_vs : ∀ v ∈ SMT.fv (SMT.substList vs (toDestPair vs (.var z)) P_enc),
      v ≠ z → v ∉ vs)
    -- B-level data
    {P : B.Term} {«Δ» : B.RenamingContext.Context}
    (Δ_fv_collect : ∀ v ∈ B.fv (Term.collect vs D P), («Δ» v).isSome = true)
    -- B typing
    {E_ctx : B.TypeContext}
    (typP : E_ctx ⊢ᴮ P : BType.bool)
    -- SMT renaming: Δ_D_eval extends toSMTOnFV «Δ» (collect vs D P)
    -- (In the original case Δ_D_eval = Δ_D, in the alt case Δ_D_eval = Δ_D_alt)
    {Δ_D_eval : SMT.RenamingContext.Context}
    (Δ_D_eval_extends : SMT.RenamingContext.Extends Δ_D_eval
      (B.RenamingContext.toSMTOnFV «Δ» (Term.collect vs D P)))
    -- Δ_ctx agrees with toSMT «Δ» on source-level P variables not in vs
    (Δ_ctx_source : ∀ v ∈ B.fv P, v ∉ vs → Δ_ctx v = B.RenamingContext.toSMT «Δ» v)
    -- Δ_D_eval vanishes outside used vars
    {used_St₂ : List SMT.𝒱}
    (Δ_D_eval_none_St₂ : ∀ v ∉ used_St₂, Δ_D_eval v = none)
    -- vs ⊆ used (for contradiction in none_out)
    (vars_used_vs : ∀ v ∈ vs, v ∈ used_St₂)
    -- used_St₂ ⊆ used_St₃ (subsumption)
    {used_St₃ : List SMT.𝒱}
    (St₂_sub_St₃ : ∀ v ∈ used_St₂, v ∈ used_St₃)
    -- fv(P_enc) ⊆ used_St₃ (P was encoded within St₃)
    (fv_P_enc_used : ∀ v ∈ SMT.fv P_enc, v ∈ used_St₃)
    -- P_enc_total: simplified (no agreement clause)
    (P_enc_total :
      ∀ (Δ_alt : B.RenamingContext.Context)
        (Δ_fv_alt : ∀ v ∈ B.fv P, (Δ_alt v).isSome = true)
        (Δ₀_alt : SMT.RenamingContext.Context),
        RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt P →
        (∀ v ∉ used_St₃, Δ₀_alt v = none) →
        ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦BType.bool⟧ᶻ),
          ⟦P.abstract Δ_alt Δ_fv_alt⟧ᴮ = some ⟨T_alt, ⟨BType.bool, hT_alt⟩⟩ →
          ∃ (Δ'_alt : SMT.RenamingContext.Context)
            (hcov_alt : SMT.RenamingContext.CoversFV Δ'_alt P_enc)
            (denT_alt : SMT.Dom),
            SMT.RenamingContext.Extends Δ'_alt Δ₀_alt ∧
            ⟦P_enc.abstract Δ'_alt hcov_alt⟧ˢ = some denT_alt ∧
            ⟨T_alt, ⟨BType.bool, hT_alt⟩⟩ ≘ᶻ denT_alt)
    -- P denotability for all x ∈ 𝒟_val
    (h_den_P : ∀ {x_fin : Fin vs.length → B.Dom},
      (∀ i, (x_fin i).snd.fst = τ.get vs.length i ∧
            (x_fin i).fst ∈ ⟦τ.get vs.length i⟧ᶻ) →
      ofFinDom x_fin ∈ 𝒟_val →
      ⟦(B.Term.abstract.go P vs «Δ» (fun v hv hvs => Δ_fv_collect v
        (B.fv.mem_collect (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ.isSome = true)
    : ∀ (x : ZFSet.{u}) (hx_mem : x ∈ ⟦τ⟧ᶻ) (hx_𝒟 : x ∈ 𝒟_val),
      let Wx : SMT.Dom := ⟨(ZFSet.fapply (BType.canonicalIsoSMTType τ).1
        (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType τ).2.1)
        ⟨x, by rwa [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType τ).2.1]⟩).1,
        τ.toSMTType, ZFSet.fapply_mem_range _ _⟩
      let x_fin : Fin vs.length → B.Dom := fun i =>
        ⟨x.get vs.length i, ⟨τ.get vs.length i,
          get_mem_type_of_isTuple (hasArity_of_mem_toZFSet τ_hasArity hx_mem) τ_hasArity hx_mem⟩⟩
      ∀ body_val : SMT.Dom,
        ⟦ite_body.abstract (Function.update Δ_ctx z (some Wx)) (hcov_ite_upd Wx)⟧ˢ = some body_val →
        (body_val.fst = zftrue ↔
          (∀ (Px : ZFSet.{u}) (P_ty : BType) (hP_val : Px ∈ ⟦P_ty⟧ᶻ),
            ⟦(B.Term.abstract.go P vs «Δ» (fun v hv hvs => Δ_fv_collect v
              (B.fv.mem_collect (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ =
              some ⟨Px, ⟨P_ty, hP_val⟩⟩ → Px = zftrue)) := by
  intro x hx_mem hx_𝒟 Wx x_fin body_val hbody_val
  subst ite_body_def
  have hWx_ty : Wx.snd.fst = τ.toSMTType := rfl
  have hWx_mem : Wx.fst ∈ ⟦τ.toSMTType⟧ᶻ := Wx.snd.snd
  have hretract_Wx : retract τ Wx.fst = x := retract_of_canonical τ hx_mem
  -- Step B: Build x_fin-derived B context
  set Δ_ext_x := Function.updates «Δ» vs (List.ofFn fun i => some (x_fin i))
  have Δ_fv_P_x : ∀ v ∈ B.fv P, (Δ_ext_x v).isSome = true := by
    intro v hv; show (Function.updates «Δ» vs _ v).isSome = true
    rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup]
    split_ifs with hvs
    · simp [List.getElem_ofFn]
    · exact Δ_fv_collect v (B.fv.mem_collect (.inr ⟨hv, hvs⟩))
  set Δ_D_ext_x := Function.updates Δ_D_eval vs
    (List.ofFn fun (i : Fin vs.length) => B.RenamingContext.toSMT Δ_ext_x vs[i])
  -- Step C: Get B-level P denotation at x_fin
  have h_ofFinDom_eq : ZFSet.ofFinDom x_fin = x :=
    ZFSet.ofFinDom_get (List.length_pos_iff.mpr vs_nemp)
      (fun i => get_mem_type_of_isTuple (hasArity_of_mem_toZFSet τ_hasArity hx_mem) τ_hasArity hx_mem)
      (hasArity_of_mem_toZFSet τ_hasArity hx_mem) τ_hasArity
  have hx_fin_in_𝒟 : ZFSet.ofFinDom x_fin ∈ 𝒟_val := h_ofFinDom_eq ▸ hx_𝒟
  have hx_fin_typ : ∀ i, (x_fin i).snd.fst = τ.get vs.length i ∧
      (x_fin i).fst ∈ ⟦τ.get vs.length i⟧ᶻ :=
    fun i => ⟨rfl, (x_fin i).snd.snd⟩
  have hP_isSome := h_den_P hx_fin_typ hx_fin_in_𝒟
  obtain ⟨⟨P_val, P_ty, hP_val⟩, hP_den⟩ := Option.isSome_iff_exists.mp hP_isSome
  -- Type-determine P_ty = .bool
  have hP_go_den : ⟦(B.Term.abstract.go P vs «Δ» (by
        intro v hv hvs; exact Δ_fv_collect v (B.fv.mem_collect (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ
      = some ⟨P_val, ⟨P_ty, hP_val⟩⟩ := by convert hP_den using 2
  have hτPx_bool : P_ty = BType.bool := by
    rw [denote_term_abstract_go_eq_term_abstract vs_nodup vs_nemp x_fin Δ_fv_P_x] at hP_go_den
    exact (denote_welltyped_eq (t := P.abstract Δ_ext_x Δ_fv_P_x)
      ⟨_, WFTC.of_abstract, .bool, by convert Typing.of_abstract Δ_fv_P_x typP⟩ hP_go_den).symm
  subst hτPx_bool
  have h_den_P_x : ⟦P.abstract Δ_ext_x Δ_fv_P_x⟧ᴮ = some ⟨P_val, ⟨BType.bool, hP_val⟩⟩ := by
    rw [← denote_term_abstract_go_eq_term_abstract vs_nodup vs_nemp x_fin Δ_fv_P_x]; exact hP_go_den
  -- Step E: Build HYBRID BASE Δ₀_hybrid_x
  -- At vs positions: Δ_D_ext_x (bound variable SMT translations)
  -- At other used_St₃ positions: Δ_ctx (the evaluation context)
  -- Elsewhere: none
  set Δ₀_hybrid_x : SMT.RenamingContext.Context :=
    fun v => if v ∈ vs then Δ_D_ext_x v
             else if v ∈ used_St₃ then Δ_ctx v
             else none
  -- Step E.1: ExtendsOnSourceFV for Δ₀_hybrid_x
  have Δ₀_hybrid_ext_P_x : RenamingContext.ExtendsOnSourceFV Δ₀_hybrid_x Δ_ext_x P := by
    intro v d hv_eq
    by_cases hv_fv : v ∈ B.fv P
    · have hv_smt : B.RenamingContext.toSMT Δ_ext_x v = some d := by
        have : B.RenamingContext.toSMTOnFV Δ_ext_x P v = B.RenamingContext.toSMT Δ_ext_x v := by
          simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
            B.RenamingContext.restrictToFV_eq_of_mem hv_fv]
        rwa [← this]
      by_cases hvs : v ∈ vs
      · -- v ∈ vs: Δ₀_hybrid_x v = Δ_D_ext_x v = updates Δ_D_eval vs (...) v
        show (if v ∈ vs then Δ_D_ext_x v else _) = some d
        rw [if_pos hvs]
        show Function.updates Δ_D_eval vs _ v = some d
        rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup, dif_pos hvs]
        simp only [List.getElem_ofFn, Fin.getElem_fin, List.getElem_idxOf]; exact hv_smt
      · -- v ∉ vs, v ∈ B.fv P: Δ₀_hybrid_x v = Δ_ctx v (since v ∈ used_St₃)
        have hv_collect : v ∈ B.fv (Term.collect vs D P) := fv.mem_collect (.inr ⟨hv_fv, hvs⟩)
        have hv_used : v ∈ used_St₃ := by
          have hΔ_ext_x_eq : Δ_ext_x v = «Δ» v := by
            show Function.updates «Δ» vs _ v = «Δ» v; exact Function.updates_of_not_mem «Δ» vs _ v hvs
          obtain ⟨bdom, hbdom⟩ := Option.isSome_iff_exists.mp (Δ_fv_collect v hv_collect)
          have h_toSMT_v : ∃ d', B.RenamingContext.toSMT «Δ» v = some d' := by
            simp only [B.RenamingContext.toSMT, hbdom, Option.pure_def]; exact ⟨_, rfl⟩
          obtain ⟨d', hd'⟩ := h_toSMT_v
          have h_toSMTOnFV_v : B.RenamingContext.toSMTOnFV «Δ» (Term.collect vs D P) v = some d' := by
            simp only [RenamingContext.toSMTOnFV, RenamingContext.toSMT,
              B.RenamingContext.restrictToFV_eq_of_mem hv_collect, Option.pure_def, Option.bind_eq_bind,
              hbdom, Option.bind_some]
            rw [B.RenamingContext.toSMT, Option.pure_def, Option.bind_eq_bind, hbdom, Option.bind_some] at hd'
            exact hd'
          have hΔ_D_eval_v : Δ_D_eval v = some d' := Δ_D_eval_extends h_toSMTOnFV_v
          by_contra hv_not_used
          exact absurd (Δ_D_eval_none_St₂ v (fun h => hv_not_used (St₂_sub_St₃ v h)))
            (by rw [hΔ_D_eval_v]; simp)
        show (if v ∈ vs then _ else if v ∈ used_St₃ then Δ_ctx v else none) = some d
        rw [if_neg hvs, if_pos hv_used]
        -- Δ_ctx v = toSMT «Δ» v = some d
        rw [Δ_ctx_source v hv_fv hvs]
        -- Need: toSMT «Δ» v = some d, i.e. hv_smt with Δ_ext_x = «Δ» at v
        have hΔ_ext_x_eq : Δ_ext_x v = «Δ» v := by
          show Function.updates «Δ» vs _ v = «Δ» v; exact Function.updates_of_not_mem «Δ» vs _ v hvs
        simpa only [B.RenamingContext.toSMT, hΔ_ext_x_eq, Option.pure_def, Option.bind_eq_bind] using hv_smt
    · have : B.RenamingContext.toSMTOnFV Δ_ext_x P v = none := by
        simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
          B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_fv]
      rw [this] at hv_eq; exact absurd hv_eq (not_eq_of_beq_eq_false rfl)
  -- Step E.2: none_out for Δ₀_hybrid_x
  have Δ₀_hybrid_x_none_St₃ : ∀ v ∉ used_St₃, Δ₀_hybrid_x v = none := by
    intro v hv
    show (if v ∈ vs then Δ_D_ext_x v else if v ∈ used_St₃ then Δ_ctx v else none) = none
    have hv_not_vs : v ∉ vs := fun hvs => hv (St₂_sub_St₃ v (vars_used_vs v hvs))
    rw [if_neg hv_not_vs, if_neg hv]
  -- Step F: Invoke P_enc_total with Δ₀_hybrid_x as base
  obtain ⟨Δ_P_x, hcov_Px, denT_x', Δ_P_x_extends, hden_Px, hRDom_x⟩ :=
    P_enc_total Δ_ext_x Δ_fv_P_x Δ₀_hybrid_x Δ₀_hybrid_ext_P_x Δ₀_hybrid_x_none_St₃
      P_val hP_val h_den_P_x
  -- Step G: Extract denT_x'.fst = P_val from RDom
  have hdenT_x'_fst_eq : denT_x'.fst = P_val := hRDom_x.2
  -- Step H: Show body_val = substList result when D_enc condition is true
  have hbody_is_substList :
      ⟦(SMT.substList vs (toDestPair vs (.var z)) P_enc).abstract
        (Function.update Δ_ctx z (some Wx)) (hcov_substList_upd Wx)⟧ˢ = some body_val := by
    have hbody_val' := hbody_val
    -- ite_body has been subst'd to its definition, so we can directly simp
    simp only [SMT.Term.abstract, SMT.denote, Option.bind_eq_bind] at hbody_val'
    conv at hbody_val' =>
      lhs; rw [SMT.RenamingContext.denote_abstract_proof_irrel D_enc
        (Function.update Δ_ctx z (some Wx)) _ (hcov_D_upd Wx)]
    rw [den_D_upd_eq Wx] at hbody_val'
    simp only [Option.bind_some, Function.update_self, Option.get_some, Option.pure_def, hWx_ty] at hbody_val'
    obtain ⟨_, Dapp_x, hDapp_x_ty, hDapp_x_val, hDapp_x_den⟩ :=
      funDenoteAppAt (Δctx := Δ_ctx) (t := D_enc) (x := z) (α := τ.toSMTType) (β := .bool) (Y := denD_val)
        hcov_D_upd den_D_upd_eq denD_val_type denD_val_func Wx hWx_ty hWx_mem
    have hDapp_x_den' := hDapp_x_den
    simp only [SMT.Term.abstract, SMT.denote, Option.bind_eq_bind] at hDapp_x_den'
    conv at hDapp_x_den' =>
      lhs; rw [SMT.RenamingContext.denote_abstract_proof_irrel D_enc _ _ (hcov_D_upd Wx)]
    rw [den_D_upd_eq Wx] at hDapp_x_den'
    simp only [Function.update_self, Option.get_some, Option.pure_def, Option.bind_some, hWx_ty] at hDapp_x_den'
    rw [hDapp_x_den'] at hbody_val'; simp only [Option.bind_some] at hbody_val'
    have hDapp_x_mem_𝔹 : Dapp_x.fst ∈ 𝔹 := by have := Dapp_x.snd.snd; rw [hDapp_x_ty] at this; exact this
    have hDapp_fst_true : Dapp_x.fst = zftrue := by
      have hx_in_retract : x ∈ retract (BType.set τ) denD_val.fst := by rw [denD_val_retract]; exact hx_𝒟
      rw [retract, ZFSet.mem_sep] at hx_in_retract
      obtain ⟨_, hx_retract_pred⟩ := hx_in_retract
      rw [dif_pos hx_mem, dif_pos denD_val_func] at hx_retract_pred
      rw [hDapp_x_val]; convert hx_retract_pred using 1
    have hcond_true : ZFSet.ZFBool.toBool ⟨Dapp_x.fst, hDapp_x_mem_𝔹⟩ = true := by
      rw [show (⟨Dapp_x.fst, hDapp_x_mem_𝔹⟩ : ZFSet.ZFBool) =
        ⟨ZFSet.zftrue, ZFSet.ZFBool.zftrue_mem_𝔹⟩ from Subtype.ext hDapp_fst_true]
      exact ZFSet.ZFBool.toBool_true
    have hDapp_x_struct : Dapp_x = ⟨Dapp_x.fst, ⟨.bool, hDapp_x_ty ▸ Dapp_x.snd.snd⟩⟩ := by
      obtain ⟨_, ⟨_, _⟩⟩ := Dapp_x; cases hDapp_x_ty; rfl
    rw [hDapp_x_struct] at hbody_val'; dsimp at hbody_val'
    rw [show ZFSet.ZFBool.toBool ⟨Dapp_x.fst, _⟩ = true from by convert hcond_true] at hbody_val'
    simp only [ite_true] at hbody_val'
    conv at hbody_val' =>
      lhs; rw [SMT.RenamingContext.denote_abstract_proof_irrel
        (SMT.substList vs (toDestPair vs (.var z)) P_enc)
        (Function.update Δ_ctx z (some Wx)) _ (hcov_substList_upd Wx)]
    exact hbody_val'
  -- Step I: DIRECT transfer substList from Δ_ctx[z↦Wx] to Δ_P_x[z↦Wx]
  -- Key: Δ_P_x extends Δ₀_hybrid_x, and for v ∈ fv(substList)\{z}\vs,
  -- Δ₀_hybrid_x v = Δ_ctx v (since v ∈ used_St₃), so Δ_P_x v = Δ_ctx v.
  have hΔ_agree_substList_direct : SMT.RenamingContext.AgreesOnFV
      (Function.update Δ_ctx z (some Wx)) (Function.update Δ_P_x z (some Wx))
      (SMT.substList vs (toDestPair vs (.var z)) P_enc) := by
    intro v hv; by_cases hvz : v = z
    · subst hvz; simp [Function.update_self]
    · rw [Function.update_of_ne hvz, Function.update_of_ne hvz]
      have hv_not_vs := fv_substList_disj_vs v hv hvz
      rcases SMT_mem_fv_substList hv with hv_P | ⟨t, ht, hv_t⟩
      · -- v ∈ fv(P_enc), v ∉ vs
        -- v ∈ used_St₃ (from fv_P_enc_used)
        have hv_used : v ∈ used_St₃ := fv_P_enc_used v hv_P
        -- Δ₀_hybrid_x v = Δ_ctx v (since v ∉ vs, v ∈ used_St₃)
        have hΔ₀_v : Δ₀_hybrid_x v = Δ_ctx v := by
          show (if v ∈ vs then _ else if v ∈ used_St₃ then Δ_ctx v else none) = Δ_ctx v
          rw [if_neg hv_not_vs, if_pos hv_used]
        -- Δ_P_x extends Δ₀_hybrid_x, so for v where Δ₀_hybrid_x v = some d,
        -- Δ_P_x v = some d
        cases hctx : Δ_ctx v with
        | some d =>
          have hΔ_P_x_v : Δ_P_x v = some d := Δ_P_x_extends (hΔ₀_v ▸ hctx)
          exact hΔ_P_x_v.symm
        | none =>
          -- Δ_ctx v = none but v ∈ fv(P_enc) ⊆ fv(substList) ⊆ fv(ite_body)
          -- This contradicts hcov_ite_upd (coverage of ite_body under Δ_ctx[z↦Wx])
          exfalso
          -- hv : v ∈ fv(substList ...), use directly as "then" branch of ite_body
          have hv_ite : v ∈ SMT.fv (((@ˢD_enc) (.var z)).ite
              (SMT.substList vs (toDestPair vs (.var z)) P_enc) (.bool false)) :=
            SMT.fv.mem_ite (Or.inr (Or.inl hv))
          have hcov := hcov_ite_upd Wx v hv_ite
          rw [Function.update_of_ne hvz, hctx] at hcov; exact absurd hcov (by simp)
      · exact absurd (SMT_fv_toDestPair_subset ht hv_t ▸ rfl) hvz
  have hcov_substList_Px : SMT.RenamingContext.CoversFV
      (Function.update Δ_P_x z (some Wx)) (SMT.substList vs (toDestPair vs (.var z)) P_enc) := by
    intro v hv; by_cases hvz : v = z
    · subst hvz; simp [Function.update_self]
    · rw [Function.update_of_ne hvz]
      have hagr := hΔ_agree_substList_direct hv
      rw [Function.update_of_ne hvz, Function.update_of_ne hvz] at hagr; rw [← hagr]
      have := hcov_substList_upd Wx v hv; rwa [Function.update_of_ne hvz] at this
  have hsubst_at_ΔPx : ⟦(SMT.substList vs (toDestPair vs (.var z)) P_enc).abstract
      (Function.update Δ_P_x z (some Wx)) hcov_substList_Px⟧ˢ = some body_val := by
    have h_transfer := SMT.RenamingContext.denote_congr_of_agreesOnFV
      (h1 := hcov_substList_upd Wx) (h2 := hcov_substList_Px) hΔ_agree_substList_direct
    unfold SMT.RenamingContext.denote at h_transfer; rw [← h_transfer]; exact hbody_is_substList
  -- Step K: abstract_substList_denote
  have hΔ_Px_vs_isSome : ∀ (i : Fin vs.length), (Δ_P_x vs[i]).isSome = true := by
    intro ⟨i, hi⟩; have hvi_mem : vs[i] ∈ vs := List.getElem_mem hi
    have hΔ_ext_x_vi : (Δ_ext_x vs[i]).isSome = true := by
      show (Function.updates «Δ» vs _ vs[i]).isSome = true
      rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup, dif_pos hvi_mem]
      simp only [List.getElem_ofFn, Option.isSome]
    obtain ⟨bval, hbval⟩ := Option.isSome_iff_exists.mp hΔ_ext_x_vi
    obtain ⟨V, τ_v, hV⟩ := bval
    have htoSMT_some : ∃ d, B.RenamingContext.toSMT Δ_ext_x vs[i] = some d := by
      simp only [B.RenamingContext.toSMT, hbval, Option.pure_def]; exact ⟨_, rfl⟩
    obtain ⟨d, hd⟩ := htoSMT_some
    have hΔ_D_ext_x_vi : Δ_D_ext_x vs[i] = some d := by
      show Function.updates Δ_D_eval vs _ vs[i] = some d
      rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup, dif_pos hvi_mem]
      simp only [List.getElem_ofFn, Fin.getElem_fin, List.getElem_idxOf]; exact hd
    have hΔ₀_hybrid_vi : Δ₀_hybrid_x vs[i] = some d := by
      show (if vs[i] ∈ vs then Δ_D_ext_x vs[i] else _) = some d
      rw [if_pos hvi_mem]; exact hΔ_D_ext_x_vi
    exact Option.isSome_iff_exists.mpr ⟨d, Δ_P_x_extends hΔ₀_hybrid_vi⟩
  let Ds_x : List SMT.Dom := List.ofFn fun i : Fin vs.length => (Δ_P_x vs[i]).get (hΔ_Px_vs_isSome i)
  have h_cov_upd_x : SMT.RenamingContext.CoversFV
      (Function.updates (Function.update Δ_P_x z (some Wx)) vs (Ds_x.map Option.some)) P_enc := by
    intro v hv; by_cases hvs : v ∈ vs
    · rw [Function.updates_eq_if (by rw [List.length_map, List.length_ofFn]) vs_nodup, dif_pos hvs]; simp
    · rw [Function.updates_of_not_mem _ vs _ _ hvs,
        Function.update_of_ne (by intro heq; exact z_not_fv_P (heq ▸ hv))]; exact hcov_Px v hv
  have hlen_xt' : vs.length = (toDestPair vs (.var z)).length := by
    rw [toDestPair_length_gen vs (.var z) (.var z) [] vs_nemp]; simp
  have hlen_xd' : vs.length = Ds_x.length := by simp [Ds_x, List.length_ofFn]
  have hvs_not_bv' : ∀ x_v ∈ vs, x_v ∉ SMT.bv P_enc := hvs_not_bv_P
  have z_not_bv_P' : z ∉ SMT.bv P_enc := z_not_bv_P
  have h_eq_x := SMT.RenamingContext.abstract_substList_denote P_enc vs (toDestPair vs (.var z))
    Ds_x hlen_xt' hlen_xd' vs_nodup hvs_not_bv' toDestPair_bv_nil
    (fun t ht w hw hbv => by rw [SMT_fv_toDestPair_subset ht hw] at hbv; exact z_not_bv_P' hbv)
    toDestPair_ne_none
    (fun t ht w hw => by rw [SMT_fv_toDestPair_subset ht hw]; exact z_not_vs)
    (by -- toDestPair[i] denotes to Ds_x[i] under Δ_P_x[z↦Wx]
      intro i hi_x hi_t hi_d
      have hcov_ti : SMT.RenamingContext.CoversFV
          (Function.update Δ_P_x z (some Wx)) (toDestPair vs (.var z))[i] := by
        intro v hv
        have hvz := SMT_fv_toDestPair_subset (List.getElem_mem hi_t) hv
        subst hvz; simp [Function.update_self]
      refine ⟨hcov_ti, ?_⟩
      have hcov_z_Px : SMT.RenamingContext.CoversFV
          (Function.update Δ_P_x z (some Wx)) (.var z) := by
        intro v hv; simp [SMT.fv] at hv; subst hv; simp [Function.update_self]
      have hden_z_Px : ⟦(SMT.Term.var z).abstract
          (Function.update Δ_P_x z (some Wx)) hcov_z_Px⟧ˢ = some Wx := by
        simp [SMT.Term.abstract, SMT.denote, Function.update_self]
      have hWx_hasArity := hasArity_of_mem_toSMTZFSet τ_hasArity hWx_mem
      obtain ⟨hcov_j, D_j, hden_j, hfst_j, hty_j⟩ :=
        toDestPair_denote_gen τ vs (.var z) Wx
          (Function.update Δ_P_x z (some Wx)) [] [] vs_nemp
          hcov_z_Px hden_z_Px hWx_ty hWx_mem τ_hasArity rfl (by simp) i hi_x hi_t
      rw [SMT.RenamingContext.denote_abstract_proof_irrel _ _ hcov_ti hcov_j, hden_j]
      have hvi_mem : vs[i] ∈ vs := List.getElem_mem hi_x
      have hΔ_ext_x_vi : Δ_ext_x vs[i] = some (x_fin ⟨i, hi_x⟩) := by
        show Function.updates «Δ» vs _ vs[i] = _
        rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup, dif_pos hvi_mem]
        simp only [List.getElem_ofFn]
        simp [List.idxOf_getElem vs_nodup]
      obtain ⟨d_smt, hd_smt⟩ : ∃ d, B.RenamingContext.toSMT Δ_ext_x vs[i] = some d := by
        simp only [B.RenamingContext.toSMT, hΔ_ext_x_vi, Option.pure_def]; exact ⟨_, rfl⟩
      have htoSMT_unf : B.RenamingContext.toSMT Δ_ext_x vs[i] = some d_smt := hd_smt
      rw [B.RenamingContext.toSMT, Option.pure_def, Option.bind_eq_bind, hΔ_ext_x_vi, Option.bind_some] at htoSMT_unf
      have hd_inj := Option.some_injective _ htoSMT_unf
      have hd_ty : d_smt.snd.fst = (τ.get vs.length ⟨i, hi_x⟩).toSMTType :=
        (congr_arg (·.snd.fst) hd_inj).symm
      have hd_retract : retract (τ.get vs.length ⟨i, hi_x⟩) d_smt.fst =
          (retract τ Wx.fst).get vs.length ⟨i, hi_x⟩ := by
        have hfst_inj := congr_arg (·.fst) hd_inj; dsimp at hfst_inj
        rw [← hfst_inj, hretract_Wx]
        exact retract_of_canonical (τ.get vs.length ⟨i, hi_x⟩)
          (get_mem_type_of_isTuple (hasArity_of_mem_toZFSet τ_hasArity hx_mem) τ_hasArity hx_mem)
      have hΔ_D_ext_x_vi : Δ_D_ext_x vs[i] = some d_smt := by
        show Function.updates Δ_D_eval vs _ vs[i] = some d_smt
        rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup, dif_pos hvi_mem]
        simp only [List.getElem_ofFn, Fin.getElem_fin, List.getElem_idxOf]; exact hd_smt
      have hΔ₀_hybrid_vi : Δ₀_hybrid_x vs[i] = some d_smt := by
        show (if vs[i] ∈ vs then Δ_D_ext_x vs[i] else _) = some d_smt
        rw [if_pos hvi_mem]; exact hΔ_D_ext_x_vi
      have hΔ_Px_vi : Δ_P_x vs[i] = some d_smt := Δ_P_x_extends hΔ₀_hybrid_vi
      have hWi_mem : Wx.fst.get vs.length ⟨i, hi_x⟩ ∈ ⟦(τ.get vs.length ⟨i, hi_x⟩).toSMTType⟧ᶻ :=
        get_mem_toSMTZFSet (hasArity_of_mem_toSMTZFSet τ_hasArity hWx_mem) τ_hasArity hWx_mem
      have hd_fst : d_smt.fst = Wx.fst.get vs.length ⟨i, hi_x⟩ := by
        have hd_mem : d_smt.fst ∈ ⟦(τ.get vs.length ⟨i, hi_x⟩).toSMTType⟧ᶻ := hd_ty ▸ d_smt.snd.snd
        have h_retract_eq : retract (τ.get vs.length ⟨i, hi_x⟩) d_smt.fst =
            retract (τ.get vs.length ⟨i, hi_x⟩) (Wx.fst.get vs.length ⟨i, hi_x⟩) := by
          rw [hd_retract, retract_get_comm (hasArity_of_mem_toSMTZFSet τ_hasArity hWx_mem) τ_hasArity hWx_mem]
        calc d_smt.fst
            = fapply (BType.canonicalIsoSMTType (τ.get vs.length ⟨i, hi_x⟩)).1
                (is_func_is_pfunc (BType.canonicalIsoSMTType _).2.1)
                ⟨retract (τ.get vs.length ⟨i, hi_x⟩) d_smt.fst, _⟩ := (canonical_of_retract _ hd_mem).symm
          _ = fapply (BType.canonicalIsoSMTType (τ.get vs.length ⟨i, hi_x⟩)).1
                (is_func_is_pfunc (BType.canonicalIsoSMTType _).2.1)
                ⟨retract (τ.get vs.length ⟨i, hi_x⟩) (Wx.fst.get vs.length ⟨i, hi_x⟩), _⟩ := by
              simp [h_retract_eq]
          _ = Wx.fst.get vs.length ⟨i, hi_x⟩ := canonical_of_retract _ hWi_mem
      have hD_j_eq : D_j = d_smt := by
        rcases D_j with ⟨z1, τ1, hz1⟩; rcases d_smt with ⟨z2, τ2, hz2⟩
        exact SMT.RenamingContext.Dom_ext'
          (show z1 = z2 by simpa using hfst_j.trans hd_fst.symm)
          (show τ1 = τ2 by simpa using hty_j.trans hd_ty.symm)
      have hDs_eq : Ds_x[i] = d_smt := by
        simp only [Ds_x, List.getElem_ofFn, Fin.getElem_fin, hΔ_Px_vi, Option.get_some]
      rw [show D_j = Ds_x[i] from hD_j_eq.trans hDs_eq.symm])
    hcov_substList_Px h_cov_upd_x
  -- Step L: updates agrees with Δ_P_x on fv(P_enc)
  have h_upd_agree_x : SMT.RenamingContext.AgreesOnFV
      (Function.updates (Function.update Δ_P_x z (some Wx)) vs (Ds_x.map Option.some)) Δ_P_x P_enc := by
    intro v hv; by_cases hvs : v ∈ vs
    · rw [Function.updates_eq_if (by rw [List.length_map, List.length_ofFn]) vs_nodup, dif_pos hvs]
      simp only [Ds_x, List.getElem_map, List.getElem_ofFn, Fin.getElem_fin, List.getElem_idxOf]
      exact Option.some_get _
    · rw [Function.updates_of_not_mem _ vs _ _ hvs,
        Function.update_of_ne (by intro heq; exact z_not_fv_P (heq ▸ hv))]
  have h_eq2_x := SMT.RenamingContext.denote_congr_of_agreesOnFV
    (h1 := h_cov_upd_x) (h2 := hcov_Px) h_upd_agree_x
  unfold SMT.RenamingContext.denote at h_eq2_x
  -- Step M: Chain body_val = denT_x'
  rw [h_eq_x, h_eq2_x, hden_Px] at hsubst_at_ΔPx
  have hbody_eq_denT : body_val = denT_x' := Option.some.inj hsubst_at_ΔPx.symm
  -- Both iff directions follow from body_val.fst = denT_x'.fst = P_val
  constructor
  · -- Forward: body_val.fst = zftrue → Px = zftrue
    intro hbody_fst Px τPx hPx hPx_den
    -- hP_den and hPx_den evaluate the same expression, so Px = P_val
    have hPx_den' := hPx_den; rw [hP_den] at hPx_den'
    have hinj := congrArg PSigma.fst (Option.some.inj hPx_den')
    dsimp at hinj
    rw [← hinj, ← hdenT_x'_fst_eq, ← hbody_eq_denT]; exact hbody_fst
  · -- Backward: (∀ Px ..., Px = zftrue) → body_val.fst = zftrue
    intro hall
    have hPval_true : P_val = zftrue := hall P_val BType.bool hP_val hP_den
    rw [hbody_eq_denT, hdenT_x'_fst_eq]; exact hPval_true

/-! ## Shared helpers for binder cases (`collect`, `lambda`, `all`)

These three helpers extract the shared `Δ_ext` / `Δ_D_ext` infrastructure
used identically across the three binder cases (`collect`, `lambda`, and
`all`).  Each binder builds a renaming-context extension by adding fresh
witnesses for the bound variables `vs`; the corresponding SMT renaming
extension `Δ_D_ext` agrees with `Δ_D` outside `vs` and with the
canonically-translated witnesses on `vs`.  -/

/-- Membership in the foldl-of-`p.1::acc` over a zipped pair list, given
membership in the underlying first-component list.  Used to discharge the
`Δ_D_ext_none_St₂/St₃` exfalso branch when proving that fresh `vs` are
disjoint from the pre-binder `usedVars`. -/
theorem mem_foldl_zip_fst_of_mem_shared
    {α β : Type _} {v : α} :
    ∀ (ws : List α) (τs' : List β) (acc : List α),
      ws.length ≤ τs'.length → v ∈ ws →
      v ∈ (ws.zip τs').foldl (fun used p => p.1 :: used) acc := by
  intro ws
  induction ws with
  | nil => intro _ _ _ hv; exact absurd hv List.not_mem_nil
  | cons w ws' ih =>
    intro τs' acc hlen hv
    cases τs' with
    | nil => simp at hlen
    | cons τ' τs'' =>
      simp only [List.zip_cons_cons, List.foldl_cons]
      rcases List.mem_cons.mp hv with rfl | hv'
      · suffices ∀ (l : List (α × β)) (acc' : List α),
            v ∈ acc' → v ∈ l.foldl (fun used p => p.1 :: used) acc' by
          exact this _ _ (List.mem_cons_self ..)
        intro l; induction l with
        | nil => exact fun _ h => h
        | cons _ _ ih' => intro acc' hmem; exact ih' _ (List.mem_cons_of_mem _ hmem)
      · exact ih τs'' _ (by simp at hlen; omega) hv'

/-- Generalized form of the `Δ_D_ext_none_St₂/St₃` block.  Given a `Δ_DD`
that is `none` outside the pre-binder `usedVars` and `vs` that are disjoint
from those `usedVars` via the (foldl of `zip`) `St_used` shape, the
`vs`-update of `Δ_DD` remains `none` outside `usedVars`. -/
theorem Δ_D_ext_none_helper_shared.{u}
    {ΔDD ΔDDext : SMT.RenamingContext.Context}
    (vs : List B.𝒱) (vs_nodup : vs.Nodup)
    {τs : List SMTType} (vs_τs_len : vs.length = τs.length)
    {used0 used1 used2 : List SMT.𝒱}
    (St_used_def : used2 = (vs.zip τs).foldl (fun used p => p.1 :: used) used1)
    (used1_eq_used0 : used1 = used0)
    {f : Fin vs.length → Option SMT.Dom.{u}}
    (ΔDDext_def : ΔDDext = Function.updates ΔDD vs (List.ofFn f))
    (ΔDD_none_outside : ∀ v ∉ used2, ΔDD v = none) :
    ∀ v ∉ used2, ΔDDext v = none := by
  intro v hv_out
  rw [ΔDDext_def, Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup]
  split_ifs with hvs
  · exfalso; apply hv_out; rw [St_used_def, used1_eq_used0]
    exact mem_foldl_zip_fst_of_mem_shared vs τs used0 (le_of_eq vs_τs_len) hvs
  · exact ΔDD_none_outside v hv_out

/-- Generalized form of the `Δ₀_ext_P` extension lemma applicable to any
binder term (collect, lambda, or all).  Given the standard `vs`-update setups
for both `«Δ»` and `Δ_D`, with `Δ_D` extending `«Δ»` on the source free
variables of the binder term `binder`, the `vs`-updates extend each other on
the source free variables of `P`.  The caller supplies `mem_binder` proving
that `v ∈ fv P ∧ v ∉ vs → v ∈ fv binder` (which holds for `Term.collect`,
`Term.lambda`, and `Term.all` via the corresponding `fv.mem_*` lemma). -/
theorem Δ₀_ext_P_helper_shared.{u}
    {«Δ» : B.RenamingContext.Context}
    {Δ_D : SMT.RenamingContext.Context}
    {vs : List B.𝒱} (vs_nodup : vs.Nodup)
    {x_fin : Fin vs.length → B.Dom.{u}}
    {Δ_ext : B.RenamingContext.Context}
    (Δ_ext_def : Δ_ext = Function.updates «Δ» vs (List.ofFn fun i => some (x_fin i)))
    {Δ_D_ext : SMT.RenamingContext.Context}
    (Δ_D_ext_def : Δ_D_ext = Function.updates Δ_D vs
      (List.ofFn fun (i : Fin vs.length) => B.RenamingContext.toSMT Δ_ext vs[i]))
    (binder P : B.Term)
    (mem_binder : ∀ {v}, v ∈ B.fv P → v ∉ vs → v ∈ B.fv binder)
    (lift :
      ∀ {v d}, B.RenamingContext.toSMTOnFV «Δ» binder v = some d →
        Δ_D v = some d) :
    SMT.RenamingContext.ExtendsOnSourceFV Δ_D_ext Δ_ext P := by
  intro v d hv_eq
  by_cases hv_fv : v ∈ B.fv P
  · have hv_smt : B.RenamingContext.toSMT Δ_ext v = some d := by
      have : B.RenamingContext.toSMTOnFV Δ_ext P v = B.RenamingContext.toSMT Δ_ext v := by
        simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
          B.RenamingContext.restrictToFV_eq_of_mem hv_fv]
      rwa [← this]
    by_cases hvs : v ∈ vs
    · rw [Δ_D_ext_def]
      rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup, dif_pos hvs]
      simp only [List.getElem_ofFn, Fin.getElem_fin, List.getElem_idxOf]
      exact hv_smt
    · have hDD_ext : Δ_D_ext v = Δ_D v := by
        rw [Δ_D_ext_def]; exact Function.updates_of_not_mem Δ_D vs _ v hvs
      rw [hDD_ext]
      have hΔ_ext_eq : Δ_ext v = «Δ» v := by
        rw [Δ_ext_def]; exact Function.updates_of_not_mem «Δ» vs _ v hvs
      have hv_binder : v ∈ B.fv binder := mem_binder hv_fv hvs
      have hv_smt_Δ : B.RenamingContext.toSMTOnFV «Δ» binder v = some d := by
        simp only [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
          B.RenamingContext.restrictToFV_eq_of_mem hv_binder, Option.pure_def,
          Option.bind_eq_bind]
        simpa only [B.RenamingContext.toSMT, hΔ_ext_eq, Option.pure_def,
          Option.bind_eq_bind] using hv_smt
      exact lift hv_smt_Δ
  · have : B.RenamingContext.toSMTOnFV Δ_ext P v = none := by
      simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
        B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_fv]
    rw [this] at hv_eq; exact absurd hv_eq (by simp)
