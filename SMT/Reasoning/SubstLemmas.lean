import SMT.Reasoning.Defs

open Std.Do B SMT ZFSet

theorem SMT_not_mem_fv_subst {x : SMT.𝒱} {t e : SMT.Term} (h : x ∉ SMT.fv t) :
    SMT.subst x e t = t := by
  induction t with
  | var v =>
    unfold SMT.subst
    simp only [SMT.fv, List.mem_singleton] at h
    rw [if_neg (Ne.symm h)]
  | int n => unfold SMT.subst; rfl
  | bool b => unfold SMT.subst; rfl
  | app f a ihf iha =>
    simp only [SMT.fv, List.mem_append, not_or] at h
    unfold SMT.subst; rw [ihf h.1, iha h.2]
  | lambda vs τs body ih =>
    unfold SMT.subst
    split_ifs with hvs
    · rfl
    · rw [ih (by intro hx; exact h (SMT.fv.mem_lambda ⟨hx, hvs⟩))]
  | «forall» vs τs body ih =>
    unfold SMT.subst
    split_ifs with hvs
    · rfl
    · rw [ih (by intro hx; exact h (SMT.fv.mem_forall ⟨hx, hvs⟩))]
  | «exists» vs τs body ih =>
    unfold SMT.subst
    split_ifs with hvs
    · rfl
    · rw [ih (by intro hx; exact h (SMT.fv.mem_exists ⟨hx, hvs⟩))]
  | as a τ ih => unfold SMT.subst; rw [ih (by simp only [SMT.fv] at h; exact h)]
  | eq t₁ t₂ ih₁ ih₂ =>
    simp only [SMT.fv, List.mem_append, not_or] at h
    unfold SMT.subst; rw [ih₁ h.1, ih₂ h.2]
  | and t₁ t₂ ih₁ ih₂ =>
    simp only [SMT.fv, List.mem_append, not_or] at h
    unfold SMT.subst; rw [ih₁ h.1, ih₂ h.2]
  | or t₁ t₂ ih₁ ih₂ =>
    simp only [SMT.fv, List.mem_append, not_or] at h
    unfold SMT.subst; rw [ih₁ h.1, ih₂ h.2]
  | not t ih => unfold SMT.subst; rw [ih (by simp only [SMT.fv] at h; exact h)]
  | imp t₁ t₂ ih₁ ih₂ =>
    simp only [SMT.fv, List.mem_append, not_or] at h
    unfold SMT.subst; rw [ih₁ h.1, ih₂ h.2]
  | ite c t₁ t₂ ihc ih₁ ih₂ =>
    simp only [SMT.fv, List.mem_append, not_or] at h
    obtain ⟨⟨hc, ht⟩, he⟩ := h
    unfold SMT.subst; rw [ihc hc, ih₁ ht, ih₂ he]
  | some t ih => unfold SMT.subst; rw [ih (by simp only [SMT.fv] at h; exact h)]
  | the t ih => unfold SMT.subst; rw [ih (by simp only [SMT.fv] at h; exact h)]
  | none => unfold SMT.subst; rfl
  | pair t₁ t₂ ih₁ ih₂ =>
    simp only [SMT.fv, List.mem_append, not_or] at h
    unfold SMT.subst; rw [ih₁ h.1, ih₂ h.2]
  | fst t ih => unfold SMT.subst; rw [ih (by simp only [SMT.fv] at h; exact h)]
  | snd t ih => unfold SMT.subst; rw [ih (by simp only [SMT.fv] at h; exact h)]
  | distinct ts ih =>
    unfold SMT.subst; congr 1
    have hmem : ∀ t_i ∈ ts, x ∉ SMT.fv t_i := fun t_i ht_i hx =>
      h (SMT.fv.mem_distinct ⟨t_i, ht_i⟩ hx)
    suffices h : ts.attach.map (fun ⟨u, hu⟩ => SMT.subst x e u) = ts.attach.map Subtype.val by
      rw [h]; exact ts.attach_map_subtype_val
    exact List.map_congr_left fun ⟨t_i, ht_i⟩ _ => ih t_i ht_i (hmem t_i ht_i)
  | le t₁ t₂ ih₁ ih₂ =>
    simp only [SMT.fv, List.mem_append, not_or] at h
    unfold SMT.subst; rw [ih₁ h.1, ih₂ h.2]
  | add t₁ t₂ ih₁ ih₂ =>
    simp only [SMT.fv, List.mem_append, not_or] at h
    unfold SMT.subst; rw [ih₁ h.1, ih₂ h.2]
  | sub t₁ t₂ ih₁ ih₂ =>
    simp only [SMT.fv, List.mem_append, not_or] at h
    unfold SMT.subst; rw [ih₁ h.1, ih₂ h.2]
  | mul t₁ t₂ ih₁ ih₂ =>
    simp only [SMT.fv, List.mem_append, not_or] at h
    unfold SMT.subst; rw [ih₁ h.1, ih₂ h.2]

theorem SMT_not_mem_fv_substList {xs : List SMT.𝒱} {ts : List SMT.Term} {e : SMT.Term}
    (h : ∀ x ∈ xs, x ∉ SMT.fv e) : SMT.substList xs ts e = e := by
  induction xs generalizing ts e with
  | nil => cases ts <;> unfold SMT.substList <;> rfl
  | cons x xs ih =>
    cases ts with
    | nil => unfold SMT.substList; rfl
    | cons t ts =>
      unfold SMT.substList
      have hx := h x (List.mem_cons_self ..)
      rw [SMT_not_mem_fv_subst hx]
      exact ih (fun y hy => h y (List.mem_cons_of_mem _ hy))

/-- After substituting x by t in e, x cannot be free if x ∉ fv t. -/
theorem SMT_not_mem_fv_subst_self {x : SMT.𝒱} {t e : SMT.Term}
    (hx : x ∉ SMT.fv t) : x ∉ SMT.fv (SMT.subst x t e) := by
  induction e with
  | var w =>
    unfold SMT.subst
    split_ifs with hw
    · exact hx
    · simp only [SMT.fv, List.mem_singleton]; exact Ne.symm hw
  | int _ | bool _ | none => simp [SMT.subst, SMT.fv]
  | app f a ihf iha =>
    unfold SMT.subst; simp only [SMT.fv, List.mem_append, not_or]; exact ⟨ihf, iha⟩
  | lambda vs τs body ih =>
    unfold SMT.subst
    split_ifs with hvs
    · intro hmem; simp only [SMT.fv, List.mem_removeAll_iff] at hmem; exact hmem.2 hvs
    · intro hmem; simp only [SMT.fv, List.mem_removeAll_iff] at hmem; exact ih hmem.1
  | «forall» vs τs body ih =>
    unfold SMT.subst
    split_ifs with hvs
    · intro hmem; simp only [SMT.fv, List.mem_removeAll_iff] at hmem; exact hmem.2 hvs
    · intro hmem; simp only [SMT.fv, List.mem_removeAll_iff] at hmem; exact ih hmem.1
  | «exists» vs τs body ih =>
    unfold SMT.subst
    split_ifs with hvs
    · intro hmem; simp only [SMT.fv, List.mem_removeAll_iff] at hmem; exact hmem.2 hvs
    · intro hmem; simp only [SMT.fv, List.mem_removeAll_iff] at hmem; exact ih hmem.1
  | as a τ ih => unfold SMT.subst; simp only [SMT.fv]; exact ih
  | eq t₁ t₂ ih₁ ih₂ =>
    unfold SMT.subst; simp only [SMT.fv, List.mem_append, not_or]; exact ⟨ih₁, ih₂⟩
  | and t₁ t₂ ih₁ ih₂ =>
    unfold SMT.subst; simp only [SMT.fv, List.mem_append, not_or]; exact ⟨ih₁, ih₂⟩
  | or t₁ t₂ ih₁ ih₂ =>
    unfold SMT.subst; simp only [SMT.fv, List.mem_append, not_or]; exact ⟨ih₁, ih₂⟩
  | not a ih => unfold SMT.subst; simp only [SMT.fv]; exact ih
  | imp t₁ t₂ ih₁ ih₂ =>
    unfold SMT.subst; simp only [SMT.fv, List.mem_append, not_or]; exact ⟨ih₁, ih₂⟩
  | ite c a b ihc iha ihb =>
    unfold SMT.subst; simp only [SMT.fv, List.mem_append, not_or]; exact ⟨⟨ihc, iha⟩, ihb⟩
  | some a ih => unfold SMT.subst; simp only [SMT.fv]; exact ih
  | the a ih => unfold SMT.subst; simp only [SMT.fv]; exact ih
  | pair t₁ t₂ ih₁ ih₂ =>
    unfold SMT.subst; simp only [SMT.fv, List.mem_append, not_or]; exact ⟨ih₁, ih₂⟩
  | fst a ih => unfold SMT.subst; simp only [SMT.fv]; exact ih
  | snd a ih => unfold SMT.subst; simp only [SMT.fv]; exact ih
  | distinct ts ih =>
    intro hmem
    unfold SMT.subst at hmem
    simp only [SMT.fv] at hmem
    rw [List.mem_flatten] at hmem
    obtain ⟨l, hl_mem, hv_l⟩ := hmem
    rw [List.mem_map] at hl_mem
    obtain ⟨⟨a, ha_attach⟩, _, rfl⟩ := hl_mem
    rw [List.mem_map] at ha_attach
    obtain ⟨⟨u, hu_ts⟩, _, rfl⟩ := ha_attach
    exact ih u hu_ts hv_l
  | le t₁ t₂ ih₁ ih₂ =>
    unfold SMT.subst; simp only [SMT.fv, List.mem_append, not_or]; exact ⟨ih₁, ih₂⟩
  | add t₁ t₂ ih₁ ih₂ =>
    unfold SMT.subst; simp only [SMT.fv, List.mem_append, not_or]; exact ⟨ih₁, ih₂⟩
  | sub t₁ t₂ ih₁ ih₂ =>
    unfold SMT.subst; simp only [SMT.fv, List.mem_append, not_or]; exact ⟨ih₁, ih₂⟩
  | mul t₁ t₂ ih₁ ih₂ =>
    unfold SMT.subst; simp only [SMT.fv, List.mem_append, not_or]; exact ⟨ih₁, ih₂⟩

/-- Free variables of `subst x t e` are contained in `(fv e \ {x}) ∪ fv t`. -/
theorem SMT_mem_fv_subst {v x : SMT.𝒱} {t e : SMT.Term}
    (h : v ∈ SMT.fv (SMT.subst x t e)) : v ∈ SMT.fv e ∨ v ∈ SMT.fv t := by
  induction e with
  | var w =>
    unfold SMT.subst at h
    split_ifs at h with hw
    · exact Or.inr h
    · exact Or.inl h
  | int n => unfold SMT.subst at h; exact Or.inl h
  | bool b => unfold SMT.subst at h; exact Or.inl h
  | none => unfold SMT.subst at h; exact Or.inl h
  | app f a ihf iha =>
    unfold SMT.subst at h; simp only [SMT.fv, List.mem_append] at h ⊢
    rcases h with hf | ha
    · rcases ihf hf with hfe | ht <;> [exact Or.inl (Or.inl hfe); exact Or.inr ht]
    · rcases iha ha with hae | ht <;> [exact Or.inl (Or.inr hae); exact Or.inr ht]
  | lambda vs τs body ih =>
    unfold SMT.subst at h
    split_ifs at h with hvs
    · exact Or.inl h
    · simp only [SMT.fv, List.mem_removeAll_iff] at h ⊢
      obtain ⟨hbody, hne⟩ := h
      rcases ih hbody with hb | ht
      · exact Or.inl ⟨hb, hne⟩
      · exact Or.inr ht
  | «forall» vs τs body ih =>
    unfold SMT.subst at h
    split_ifs at h with hvs
    · exact Or.inl h
    · simp only [SMT.fv, List.mem_removeAll_iff] at h ⊢
      obtain ⟨hbody, hne⟩ := h
      rcases ih hbody with hb | ht
      · exact Or.inl ⟨hb, hne⟩
      · exact Or.inr ht
  | «exists» vs τs body ih =>
    unfold SMT.subst at h
    split_ifs at h with hvs
    · exact Or.inl h
    · simp only [SMT.fv, List.mem_removeAll_iff] at h ⊢
      obtain ⟨hbody, hne⟩ := h
      rcases ih hbody with hb | ht
      · exact Or.inl ⟨hb, hne⟩
      · exact Or.inr ht
  | as a τ ih =>
    unfold SMT.subst at h; simp only [SMT.fv] at h ⊢; exact ih h
  | eq t₁ t₂ ih₁ ih₂ =>
    unfold SMT.subst at h; simp only [SMT.fv, List.mem_append] at h ⊢
    rcases h with h1 | h2
    · rcases ih₁ h1 with h1e | ht <;> [exact Or.inl (Or.inl h1e); exact Or.inr ht]
    · rcases ih₂ h2 with h2e | ht <;> [exact Or.inl (Or.inr h2e); exact Or.inr ht]
  | and t₁ t₂ ih₁ ih₂ =>
    unfold SMT.subst at h; simp only [SMT.fv, List.mem_append] at h ⊢
    rcases h with h1 | h2
    · rcases ih₁ h1 with h1e | ht <;> [exact Or.inl (Or.inl h1e); exact Or.inr ht]
    · rcases ih₂ h2 with h2e | ht <;> [exact Or.inl (Or.inr h2e); exact Or.inr ht]
  | or t₁ t₂ ih₁ ih₂ =>
    unfold SMT.subst at h; simp only [SMT.fv, List.mem_append] at h ⊢
    rcases h with h1 | h2
    · rcases ih₁ h1 with h1e | ht <;> [exact Or.inl (Or.inl h1e); exact Or.inr ht]
    · rcases ih₂ h2 with h2e | ht <;> [exact Or.inl (Or.inr h2e); exact Or.inr ht]
  | not a ih =>
    unfold SMT.subst at h; simp only [SMT.fv] at h ⊢; exact ih h
  | imp t₁ t₂ ih₁ ih₂ =>
    unfold SMT.subst at h; simp only [SMT.fv, List.mem_append] at h ⊢
    rcases h with h1 | h2
    · rcases ih₁ h1 with h1e | ht <;> [exact Or.inl (Or.inl h1e); exact Or.inr ht]
    · rcases ih₂ h2 with h2e | ht <;> [exact Or.inl (Or.inr h2e); exact Or.inr ht]
  | ite c a b ihc iha ihb =>
    unfold SMT.subst at h; simp only [SMT.fv, List.mem_append] at h ⊢
    rcases h with (hc | ha) | hb
    · rcases ihc hc with hce | ht <;> [exact Or.inl (Or.inl (Or.inl hce)); exact Or.inr ht]
    · rcases iha ha with hae | ht <;> [exact Or.inl (Or.inl (Or.inr hae)); exact Or.inr ht]
    · rcases ihb hb with hbe | ht <;> [exact Or.inl (Or.inr hbe); exact Or.inr ht]
  | some a ih =>
    unfold SMT.subst at h; simp only [SMT.fv] at h ⊢; exact ih h
  | the a ih =>
    unfold SMT.subst at h; simp only [SMT.fv] at h ⊢; exact ih h
  | pair t₁ t₂ ih₁ ih₂ =>
    unfold SMT.subst at h; simp only [SMT.fv, List.mem_append] at h ⊢
    rcases h with h1 | h2
    · rcases ih₁ h1 with h1e | ht <;> [exact Or.inl (Or.inl h1e); exact Or.inr ht]
    · rcases ih₂ h2 with h2e | ht <;> [exact Or.inl (Or.inr h2e); exact Or.inr ht]
  | fst a ih =>
    unfold SMT.subst at h; simp only [SMT.fv] at h ⊢; exact ih h
  | snd a ih =>
    unfold SMT.subst at h; simp only [SMT.fv] at h ⊢; exact ih h
  | distinct ts ih =>
    unfold SMT.subst at h; simp only [SMT.fv] at h
    rw [List.mem_flatten] at h
    obtain ⟨l, hl_mem, hv_l⟩ := h
    rw [List.mem_map] at hl_mem
    obtain ⟨⟨a, ha_in_substs⟩, _, rfl⟩ := hl_mem
    -- a ∈ ts.attach.map (fun ⟨u, _⟩ => subst x t u), so ∃ u ∈ ts, subst x t u = a
    rw [List.mem_map] at ha_in_substs
    obtain ⟨⟨u, hu_ts⟩, _, rfl⟩ := ha_in_substs
    -- hv_l : v ∈ fv (subst x t u)
    rcases ih u hu_ts hv_l with he | ht
    · exact Or.inl (SMT.fv.mem_distinct ⟨u, hu_ts⟩ he)
    · exact Or.inr ht
  | le t₁ t₂ ih₁ ih₂ =>
    unfold SMT.subst at h; simp only [SMT.fv, List.mem_append] at h ⊢
    rcases h with h1 | h2
    · rcases ih₁ h1 with h1e | ht <;> [exact Or.inl (Or.inl h1e); exact Or.inr ht]
    · rcases ih₂ h2 with h2e | ht <;> [exact Or.inl (Or.inr h2e); exact Or.inr ht]
  | add t₁ t₂ ih₁ ih₂ =>
    unfold SMT.subst at h; simp only [SMT.fv, List.mem_append] at h ⊢
    rcases h with h1 | h2
    · rcases ih₁ h1 with h1e | ht <;> [exact Or.inl (Or.inl h1e); exact Or.inr ht]
    · rcases ih₂ h2 with h2e | ht <;> [exact Or.inl (Or.inr h2e); exact Or.inr ht]
  | sub t₁ t₂ ih₁ ih₂ =>
    unfold SMT.subst at h; simp only [SMT.fv, List.mem_append] at h ⊢
    rcases h with h1 | h2
    · rcases ih₁ h1 with h1e | ht <;> [exact Or.inl (Or.inl h1e); exact Or.inr ht]
    · rcases ih₂ h2 with h2e | ht <;> [exact Or.inl (Or.inr h2e); exact Or.inr ht]
  | mul t₁ t₂ ih₁ ih₂ =>
    unfold SMT.subst at h; simp only [SMT.fv, List.mem_append] at h ⊢
    rcases h with h1 | h2
    · rcases ih₁ h1 with h1e | ht <;> [exact Or.inl (Or.inl h1e); exact Or.inr ht]
    · rcases ih₂ h2 with h2e | ht <;> [exact Or.inl (Or.inr h2e); exact Or.inr ht]

/-- Free variables of `substList xs ts e` are contained in `(fv e) ∪ ⋃ (fv <$> ts)`. -/
theorem SMT_mem_fv_substList {v : SMT.𝒱} {xs : List SMT.𝒱} {ts : List SMT.Term} {e : SMT.Term}
    (h : v ∈ SMT.fv (SMT.substList xs ts e)) : v ∈ SMT.fv e ∨ ∃ t ∈ ts, v ∈ SMT.fv t := by
  induction xs generalizing ts e with
  | nil => cases ts <;> (unfold SMT.substList at h; exact Or.inl h)
  | cons x xs ih =>
    cases ts with
    | nil => unfold SMT.substList at h; exact Or.inl h
    | cons t' ts' =>
      unfold SMT.substList at h
      rcases ih h with hsub | ⟨t'', ht'', hv⟩
      · rcases SMT_mem_fv_subst hsub with he | ht
        · exact Or.inl he
        · exact Or.inr ⟨t', List.mem_cons_self .., ht⟩
      · exact Or.inr ⟨t'', List.mem_cons_of_mem _ ht'', hv⟩

/-- If v is not free in e and not free in any substitution term, it's not free in the substList result. -/
theorem SMT_not_mem_fv_substList_of_not_mem {v : SMT.𝒱} {xs : List SMT.𝒱}
    {ts : List SMT.Term} {e : SMT.Term}
    (he : v ∉ SMT.fv e) (hts : ∀ t ∈ ts, v ∉ SMT.fv t) :
    v ∉ SMT.fv (SMT.substList xs ts e) := by
  intro habs
  rcases SMT_mem_fv_substList habs with h | ⟨t, ht, hv⟩
  · exact he h
  · exact hts t ht hv

/-- After substList xs ts e, any x ∈ xs with x ∉ fv(t) for all t ∈ ts is not free in the result,
    provided xs.length ≤ ts.length. -/
theorem SMT_not_mem_fv_substList_of_mem_vars {v : SMT.𝒱} {xs : List SMT.𝒱}
    {ts : List SMT.Term} {e : SMT.Term}
    (hlen : xs.length ≤ ts.length) (hvs : v ∈ xs) (hts : ∀ t ∈ ts, v ∉ SMT.fv t) :
    v ∉ SMT.fv (SMT.substList xs ts e) := by
  induction xs generalizing ts e with
  | nil => simp at hvs
  | cons x xs ih =>
    cases ts with
    | nil => simp at hlen
    | cons t' ts' =>
      unfold SMT.substList
      rcases List.mem_cons.mp hvs with rfl | hvs'
      · have v_not_inner : v ∉ SMT.fv (SMT.subst v t' e) :=
          SMT_not_mem_fv_subst_self (hts t' (by exact List.mem_cons_self ..))
        exact SMT_not_mem_fv_substList_of_not_mem v_not_inner
          (fun t ht => hts t (List.mem_cons_of_mem _ ht))
      · exact ih (by simp [List.length] at hlen; omega) hvs'
          (fun t ht => hts t (List.mem_cons_of_mem _ ht))


theorem SMT_fv_toDestPair_subset_base {v : SMT.𝒱} {z : SMT.𝒱}
    {vs : List SMT.𝒱} {t : SMT.Term} {t₀ : SMT.Term}
    (ht₀ : ∀ w ∈ SMT.fv t₀, w = z)
    (ht : t ∈ toDestPair vs t₀) (hv : v ∈ SMT.fv t) : v = z := by
  have key : ∀ (vs : List SMT.𝒱) (zp : SMT.Term) (acc : List SMT.Term) (d : SMT.Term),
      (∀ w ∈ SMT.fv zp, w = z) →
      (∀ a ∈ acc, ∀ w ∈ SMT.fv a, w = z) → (∀ w ∈ SMT.fv d, w = z) →
      ∀ u ∈ toDestPair vs zp acc d, ∀ w ∈ SMT.fv u, w = z := by
    intro vs'
    induction vs' with
    | nil => exact fun zp acc d a hacc _ u hu ↦ hacc u hu
    | cons x xs ih =>
      intro zp acc d hzp hacc hd u hu
      cases xs with
      | nil =>
        unfold toDestPair at hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact hzp
        · exact hacc u hu
      | cons y ys =>
        unfold toDestPair at hu
        exact ih (.fst d) (.snd d :: acc) (.fst d)
          (fun w hw => by simp only [SMT.fv] at hw; exact hd w hw)
          (fun a ha w hw => by
            rcases List.mem_cons.mp ha with rfl | ha
            · simp only [SMT.fv] at hw; exact hd w hw
            · exact hacc a ha w hw)
          (fun w hw => by simp only [SMT.fv] at hw; exact hd w hw)
          u hu
  exact key vs t₀ [] t₀ ht₀ (by simp) ht₀ t ht v hv

theorem SMT_fv_toDestPair_subset {v : SMT.𝒱} {z : SMT.𝒱}
    {vs : List SMT.𝒱} {t : SMT.Term}
    (ht : t ∈ toDestPair vs (.var z)) (hv : v ∈ SMT.fv t) : v = z :=
  SMT_fv_toDestPair_subset_base (t₀ := .var z)
    (by intro w hw; simp [SMT.fv] at hw; exact hw) ht hv

theorem SMT_bv_subst_subset {x : SMT.𝒱} {t e : SMT.Term}
    (hbv : SMT.bv e = []) : ∀ v ∈ SMT.bv (SMT.subst x e t), v ∈ SMT.bv t := by
  intro v; induction t with
  | var w =>
    unfold SMT.subst; split_ifs
    · intro hv; simp [hbv] at hv
    · exact id
  | int _ | bool _ | none => unfold SMT.subst; exact id
  | app f a ihf iha =>
    unfold SMT.subst; simp only [SMT.bv, List.mem_append]
    intro hv; rcases hv with hf | ha
    · exact Or.inl (ihf hf)
    · exact Or.inr (iha ha)
  | lambda vs τs body ih =>
    unfold SMT.subst; split_ifs
    · exact id
    · simp only [SMT.bv, List.mem_append]; intro hv; rcases hv with hvs | hbody
      · exact Or.inl hvs
      · exact Or.inr (ih hbody)
  | «forall» vs τs body ih =>
    unfold SMT.subst; split_ifs
    · exact id
    · simp only [SMT.bv, List.mem_append]; intro hv; rcases hv with hvs | hbody
      · exact Or.inl hvs
      · exact Or.inr (ih hbody)
  | «exists» vs τs body ih =>
    unfold SMT.subst; split_ifs
    · exact id
    · simp only [SMT.bv, List.mem_append]; intro hv; rcases hv with hvs | hbody
      · exact Or.inl hvs
      · exact Or.inr (ih hbody)
  | as a τ ih =>
    intro hv; unfold SMT.subst at hv; unfold SMT.bv at hv ⊢; exact ih hv
  | eq t₁ t₂ ih₁ ih₂ =>
    intro hv; unfold SMT.subst at hv; unfold SMT.bv at hv ⊢
    simp only [List.mem_append] at hv ⊢
    rcases hv with h1 | h2
    · exact Or.inl (ih₁ h1)
    · exact Or.inr (ih₂ h2)
  | and t₁ t₂ ih₁ ih₂ =>
    intro hv; unfold SMT.subst at hv; unfold SMT.bv at hv ⊢
    simp only [List.mem_append] at hv ⊢
    rcases hv with h1 | h2
    · exact Or.inl (ih₁ h1)
    · exact Or.inr (ih₂ h2)
  | or t₁ t₂ ih₁ ih₂ =>
    intro hv; unfold SMT.subst at hv; unfold SMT.bv at hv ⊢
    simp only [List.mem_append] at hv ⊢
    rcases hv with h1 | h2
    · exact Or.inl (ih₁ h1)
    · exact Or.inr (ih₂ h2)
  | not a ih =>
    intro hv; unfold SMT.subst at hv; unfold SMT.bv at hv ⊢; exact ih hv
  | imp t₁ t₂ ih₁ ih₂ =>
    intro hv; unfold SMT.subst at hv; unfold SMT.bv at hv ⊢
    simp only [List.mem_append] at hv ⊢
    rcases hv with h1 | h2
    · exact Or.inl (ih₁ h1)
    · exact Or.inr (ih₂ h2)
  | ite c a b ihc iha ihb =>
    intro hv; unfold SMT.subst at hv; unfold SMT.bv at hv ⊢
    simp only [List.mem_append] at hv ⊢
    rcases hv with (hc | ha) | hb
    · exact Or.inl (Or.inl (ihc hc))
    · exact Or.inl (Or.inr (iha ha))
    · exact Or.inr (ihb hb)
  | some a ih =>
    intro hv; unfold SMT.subst at hv; unfold SMT.bv at hv ⊢; exact ih hv
  | the a ih =>
    intro hv; unfold SMT.subst at hv; unfold SMT.bv at hv ⊢; exact ih hv
  | pair t₁ t₂ ih₁ ih₂ =>
    intro hv; unfold SMT.subst at hv; unfold SMT.bv at hv ⊢
    simp only [List.mem_append] at hv ⊢
    rcases hv with h1 | h2
    · exact Or.inl (ih₁ h1)
    · exact Or.inr (ih₂ h2)
  | fst a ih =>
    intro hv; unfold SMT.subst at hv; unfold SMT.bv at hv ⊢; exact ih hv
  | snd a ih =>
    intro hv; unfold SMT.subst at hv; unfold SMT.bv at hv ⊢; exact ih hv
  | distinct ts ih =>
    intro hv; unfold SMT.subst at hv; unfold SMT.bv at hv
    rw [List.mem_flatten] at hv
    obtain ⟨l, hl_mem, hv_l⟩ := hv
    rw [List.mem_map] at hl_mem
    obtain ⟨⟨a, ha_in_substs⟩, _, rfl⟩ := hl_mem
    rw [List.mem_map] at ha_in_substs
    obtain ⟨⟨u, hu_ts⟩, _, rfl⟩ := ha_in_substs
    -- hv_l : v ∈ bv (subst x e u), ih gives v ∈ bv u
    unfold SMT.bv; rw [List.mem_flatten]
    exact ⟨SMT.bv u, List.mem_map.mpr ⟨⟨u, hu_ts⟩, List.mem_attach _ _, rfl⟩, ih u hu_ts hv_l⟩
  | le t₁ t₂ ih₁ ih₂ =>
    intro hv; unfold SMT.subst at hv; unfold SMT.bv at hv ⊢
    simp only [List.mem_append] at hv ⊢
    rcases hv with h1 | h2
    · exact Or.inl (ih₁ h1)
    · exact Or.inr (ih₂ h2)
  | add t₁ t₂ ih₁ ih₂ =>
    intro hv; unfold SMT.subst at hv; unfold SMT.bv at hv ⊢
    simp only [List.mem_append] at hv ⊢
    rcases hv with h1 | h2
    · exact Or.inl (ih₁ h1)
    · exact Or.inr (ih₂ h2)
  | sub t₁ t₂ ih₁ ih₂ =>
    intro hv; unfold SMT.subst at hv; unfold SMT.bv at hv ⊢
    simp only [List.mem_append] at hv ⊢
    rcases hv with h1 | h2
    · exact Or.inl (ih₁ h1)
    · exact Or.inr (ih₂ h2)
  | mul t₁ t₂ ih₁ ih₂ =>
    intro hv; unfold SMT.subst at hv; unfold SMT.bv at hv ⊢
    simp only [List.mem_append] at hv ⊢
    rcases hv with h1 | h2
    · exact Or.inl (ih₁ h1)
    · exact Or.inr (ih₂ h2)

theorem SMT_bv_substList_subset {xs : List SMT.𝒱} {ts : List SMT.Term} {e : SMT.Term}
    (hbvs : ∀ t ∈ ts, SMT.bv t = []) : ∀ v ∈ SMT.bv (SMT.substList xs ts e), v ∈ SMT.bv e := by
  induction xs generalizing ts e with
  | nil => cases ts <;> (unfold SMT.substList; exact fun _ => id)
  | cons x xs ih =>
    cases ts with
    | nil => unfold SMT.substList; exact fun _ => id
    | cons t' ts' =>
      unfold SMT.substList
      intro v hv
      have h_sub := ih (fun t ht => hbvs t (List.mem_cons_of_mem _ ht)) v hv
      exact SMT_bv_subst_subset (hbvs t' (List.mem_cons_self ..)) v h_sub


-- Entries are monotone under update when bound variables are fresh w.r.t. the original context
theorem entries_subset_update_of_fresh {Γ : SMT.TypeContext} {vs : List SMT.𝒱} {τs : List SMTType}
    (hvs : ∀ v ∈ vs, v ∉ Γ) (hlen : vs.length = τs.length) :
    Γ ⊆ (Γ.update vs τs hlen) := by
  intro e he
  have he_not_vs : e.1 ∉ vs := by
    intro hv; exact hvs e.1 hv (AList.mem_keys.mpr (List.mem_map.mpr ⟨e, he, rfl⟩))
  have hlookup : Γ.lookup e.1 = some e.2 := AList.mem_lookup_iff.mpr he
  have hlookup_upd : (Γ.update vs τs).lookup e.1 = Γ.lookup e.1 :=
    SMT.TypeContext.lookup_update Γ e.1 vs τs hlen he_not_vs
  exact AList.mem_lookup_iff.mp (hlookup_upd ▸ hlookup)

theorem SMT_Typing_subst {Γ : SMT.TypeContext} {x : SMT.𝒱} (t e : SMT.Term) {τ : SMTType}
    (h : Γ ⊢ˢ t : τ) (hbv_e : SMT.bv e = [])
    (h' : (hx : (Γ.lookup x).isSome = true) → Γ ⊢ˢ e : (Γ.lookup x).get hx) :
    Γ ⊢ˢ SMT.subst x e t : τ := by
  by_cases h_fv : x ∈ SMT.fv t
  swap
  · rwa [SMT_not_mem_fv_subst h_fv]
  have hx_mem : x ∈ Γ := SMT.Typing.mem_context_of_mem_fv h h_fv
  obtain ⟨α, α_def⟩ := Option.isSome_iff_exists.mp (AList.lookup_isSome.mpr hx_mem)
  have h_e_typed : Γ ⊢ˢ e : α := by
    have hsome : (Γ.lookup x).isSome := by rw [α_def]; rfl
    have h_typ := h' hsome
    simp only [α_def, Option.get_some] at h_typ
    exact h_typ
  clear h' h_fv
  exact SMT_Typing_subst_core t e h hbv_e α_def h_e_typed
where
  SMT_Typing_subst_core (t e : SMT.Term) {Γ : SMT.TypeContext} {x : SMT.𝒱} {τ α : SMTType}
      (h : Γ ⊢ˢ t : τ) (hbv_e : SMT.bv e = [])
      (α_def : Γ.lookup x = some α) (h_e_typed : Γ ⊢ˢ e : α) :
      Γ ⊢ˢ SMT.subst x e t : τ := by
    induction h with
    | var Γ' v τ' hlookup =>
      unfold SMT.subst
      split_ifs with heq
      · subst heq; cases α_def ▸ hlookup; exact h_e_typed
      · exact .var Γ' v τ' hlookup
    | int Γ' n => unfold SMT.subst; exact .int Γ' n
    | bool Γ' b => unfold SMT.subst; exact .bool Γ' b
    | app Γ' f a τ' σ _ _ ihf iha =>
      unfold SMT.subst; exact .app Γ' _ _ τ' σ (ihf α_def h_e_typed) (iha α_def h_e_typed)
    | lambda Γ' vs' τs' body γ hvs hfresh hlen_pos hlen_eq _ ih =>
      unfold SMT.subst
      split_ifs with hxvs
      · exact .lambda Γ' vs' τs' body γ hvs hfresh hlen_pos hlen_eq (by assumption)
      · exact SMT.Typing.lambda Γ' vs' τs' _ γ hvs
            (fun v hv hbv => hfresh v hv (SMT_bv_subst_subset hbv_e v hbv))
            hlen_pos hlen_eq
            (ih (by rw [SMT.TypeContext.lookup_update Γ' x vs' τs' hlen_eq hxvs]; exact α_def)
                (SMT.Typing.weakening (entries_subset_update_of_fresh hvs hlen_eq) h_e_typed))
    | «forall» Γ' vs' τs' body hvs hfresh hlen_pos hlen_eq _ ih =>
      unfold SMT.subst
      split_ifs with hxvs
      · exact .forall Γ' vs' τs' body hvs hfresh hlen_pos hlen_eq (by assumption)
      · exact SMT.Typing.forall Γ' vs' τs' _ hvs
            (fun v hv hbv => hfresh v hv (SMT_bv_subst_subset hbv_e v hbv))
            hlen_pos hlen_eq
            (ih (by rw [SMT.TypeContext.lookup_update Γ' x vs' τs' hlen_eq hxvs]; exact α_def)
                (SMT.Typing.weakening (entries_subset_update_of_fresh hvs hlen_eq) h_e_typed))
    | «exists» Γ' vs' τs' body hvs hfresh hlen_pos hlen_eq _ ih =>
      unfold SMT.subst
      split_ifs with hxvs
      · exact .exists Γ' vs' τs' body hvs hfresh hlen_pos hlen_eq (by assumption)
      · exact SMT.Typing.exists Γ' vs' τs' _ hvs
            (fun v hv hbv => hfresh v hv (SMT_bv_subst_subset hbv_e v hbv))
            hlen_pos hlen_eq
            (ih (by rw [SMT.TypeContext.lookup_update Γ' x vs' τs' hlen_eq hxvs]; exact α_def)
                (SMT.Typing.weakening (entries_subset_update_of_fresh hvs hlen_eq) h_e_typed))
    | eq Γ' t₁ t₂ τ' _ _ ih₁ ih₂ =>
      unfold SMT.subst; exact .eq Γ' _ _ τ' (ih₁ α_def h_e_typed) (ih₂ α_def h_e_typed)
    | and Γ' t₁ t₂ _ _ ih₁ ih₂ =>
      unfold SMT.subst; exact .and Γ' _ _ (ih₁ α_def h_e_typed) (ih₂ α_def h_e_typed)
    | or Γ' t₁ t₂ _ _ ih₁ ih₂ =>
      unfold SMT.subst; exact .or Γ' _ _ (ih₁ α_def h_e_typed) (ih₂ α_def h_e_typed)
    | not Γ' t' _ ih =>
      unfold SMT.subst; exact .not Γ' _ (ih α_def h_e_typed)
    | imp Γ' t₁ t₂ _ _ ih₁ ih₂ =>
      unfold SMT.subst; exact .imp Γ' _ _ (ih₁ α_def h_e_typed) (ih₂ α_def h_e_typed)
    | ite Γ' c t₁ t₂ τ' _ _ _ ihc ih₁ ih₂ =>
      unfold SMT.subst
      exact .ite Γ' _ _ _ τ' (ihc α_def h_e_typed) (ih₁ α_def h_e_typed) (ih₂ α_def h_e_typed)
    | some Γ' t' τ' _ ih =>
      unfold SMT.subst; exact .some Γ' _ τ' (ih α_def h_e_typed)
    | none Γ' τ' => simp only [SMT.subst]; exact .none Γ' τ'
    | the Γ' t' τ' _ ih =>
      unfold SMT.subst; exact .the Γ' _ τ' (ih α_def h_e_typed)
    | pair Γ' t₁ τ₁ t₂ τ₂ _ _ ih₁ ih₂ =>
      unfold SMT.subst; exact .pair Γ' _ τ₁ _ τ₂ (ih₁ α_def h_e_typed) (ih₂ α_def h_e_typed)
    | fst Γ' t' τ' σ _ ih =>
      unfold SMT.subst; exact .fst Γ' _ τ' σ (ih α_def h_e_typed)
    | snd Γ' t' τ' σ _ ih =>
      unfold SMT.subst; exact .snd Γ' _ τ' σ (ih α_def h_e_typed)
    | distinct Γ' ts τ' hts ih =>
      unfold SMT.subst
      apply SMT.Typing.distinct
      intro u hu
      rw [List.mem_map] at hu
      obtain ⟨⟨t_i, ht_i⟩, _, rfl⟩ := hu
      exact ih t_i ht_i α_def h_e_typed
    | le Γ' t₁ t₂ _ _ ih₁ ih₂ =>
      unfold SMT.subst; exact .le Γ' _ _ (ih₁ α_def h_e_typed) (ih₂ α_def h_e_typed)
    | add Γ' t₁ t₂ _ _ ih₁ ih₂ =>
      unfold SMT.subst; exact .add Γ' _ _ (ih₁ α_def h_e_typed) (ih₂ α_def h_e_typed)
    | sub Γ' t₁ t₂ _ _ ih₁ ih₂ =>
      unfold SMT.subst; exact .sub Γ' _ _ (ih₁ α_def h_e_typed) (ih₂ α_def h_e_typed)
    | mul Γ' t₁ t₂ _ _ ih₁ ih₂ =>
      unfold SMT.subst; exact .mul Γ' _ _ (ih₁ α_def h_e_typed) (ih₂ α_def h_e_typed)

theorem SMT_Typing_substList {Γ : SMT.TypeContext} (xs : List SMT.𝒱) (ts : List SMT.Term)
    (e : SMT.Term) {τ : SMTType}
    (h : Γ ⊢ˢ e : τ)
    (hbvs : ∀ t ∈ ts, SMT.bv t = [])
    (hpairs : ∀ i, ∀ (hi_x : i < xs.length), ∀ (hi_t : i < ts.length),
      (hx : (Γ.lookup xs[i]).isSome = true) → Γ ⊢ˢ ts[i] : (Γ.lookup xs[i]).get hx) :
    Γ ⊢ˢ SMT.substList xs ts e : τ := by
  induction xs generalizing ts e with
  | nil => cases ts <;> (unfold SMT.substList; exact h)
  | cons x xs' ih =>
    cases ts with
    | nil => unfold SMT.substList; exact h
    | cons t' ts' =>
      unfold SMT.substList
      apply ih
      · apply SMT_Typing_subst _ _ h
        · exact hbvs t' (List.mem_cons_self ..)
        · intro hx
          exact hpairs 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _) hx
      · exact fun t ht => hbvs t (List.mem_cons_of_mem _ ht)
      · intro i hi_x hi_t hx
        exact hpairs (i + 1) (Nat.succ_lt_succ hi_x) (Nat.succ_lt_succ hi_t) hx

