import SMT.Reasoning.Defs
import SMT.Reasoning.LooseningDefs
import SMT.Reasoning.Basic.StateSpecs
import SMT.Reasoning.Basic.LoosenAuxSpec

open Std.Do B SMT ZFSet

namespace SMT.RenamingContext

/-- Proof irrelevance for `abstract`/`denote`: the coverage proof does not affect the denotation. -/
lemma denote_abstract_proof_irrel (e : SMT.Term) («Δ» : Context)
    (h₁ h₂ : CoversFV «Δ» e) :
    ⟦e.abstract «Δ» h₁⟧ˢ = ⟦e.abstract «Δ» h₂⟧ˢ :=
  congr_arg SMT.denote (abstract_eq_of_agreesOnFV (h1 := h₁) (h2 := h₂) (agreesOnFV_refl «Δ» e))

lemma Dom_ext' {z1 z2 : ZFSet} {τ1 τ2 : SMTType} {h1 : z1 ∈ ⟦τ1⟧ᶻ} {h2 : z2 ∈ ⟦τ2⟧ᶻ}
    (hz : z1 = z2) (hτ : τ1 = τ2) :
    (⟨z1, τ1, h1⟩ : SMT.Dom) = ⟨z2, τ2, h2⟩ := by
  subst hz; subst hτ; rfl

lemma psigma_eq_of_fst_eq {X Y : ZFSet} {τ : SMTType}
    {hX : X ∈ ⟦τ⟧ᶻ} {hY : Y ∈ ⟦τ⟧ᶻ} (h : X = Y) :
    (⟨X, ⟨τ, hX⟩⟩ : SMT.Dom) = ⟨Y, ⟨τ, hY⟩⟩ := by
  subst h; rfl

/-- Congruence for lambda denotation: if two body functions agree denotationally
on all arguments, their lambda denotations are equal. -/
lemma denote_lambda_congr {n : ℕ} {τs : Fin n → SMTType}
    {body1 body2 : (Fin n → SMT.Dom) → PHOAS.Term SMT.Dom}
    (h : ∀ αs : Fin n → SMT.Dom, SMT.denote (body1 αs) = SMT.denote (body2 αs)) :
    SMT.denote (PHOAS.Term.lambda τs body1) = SMT.denote (PHOAS.Term.lambda τs body2) := by
  simp only [SMT.denote]
  open Classical in
  refine dite_congr rfl (fun n_pos => ?_) (fun _ => rfl)
  have h_isSome_eq :
      (∀ {x : Fin n → Dom},
        (∀ (i : Fin n), (x i).snd.fst = τs i ∧ (x i).fst ∈ ⟦τs i⟧ᶻ) →
          ⟦body1 x⟧ˢ.isSome = true) =
      (∀ {x : Fin n → Dom},
        (∀ (i : Fin n), (x i).snd.fst = τs i ∧ (x i).fst ∈ ⟦τs i⟧ᶻ) →
          ⟦body2 x⟧ˢ.isSome = true) :=
    propext ⟨fun hh {x} hx => by rw [← h]; exact @hh x hx,
            fun hh {x} hx => by rw [h]; exact @hh x hx⟩
  refine dite_congr h_isSome_eq (fun den_t_isSome => ?_) (fun _ => rfl)
  have hxₙ : ∀ i : Fin n,
      (⟨(τs i).defaultZFSet, τs i, SMTType.mem_toZFSet_of_defaultZFSet⟩ : Dom).2.1 = τs i ∧
      (⟨(τs i).defaultZFSet, τs i, SMTType.mem_toZFSet_of_defaultZFSet⟩ : Dom).1 ∈ ⟦τs i⟧ᶻ :=
    fun i => ⟨rfl, SMTType.mem_toZFSet_of_defaultZFSet⟩
  have h_get : ∀ (x : Fin n → Dom) (hx : ∀ i, (x i).2.1 = τs i ∧ (x i).1 ∈ ⟦τs i⟧ᶻ),
      (⟦body1 x⟧ˢ.get (h_isSome_eq.mpr den_t_isSome hx)) =
      (⟦body2 x⟧ˢ.get (den_t_isSome hx)) := fun x hx => Option.get_congr (h x)
  have h_typ_det_eq :
      (∀ (x y : Fin n → Dom),
        (hx : ∀ i, (x i).2.1 = τs i ∧ (x i).1 ∈ ⟦τs i⟧ᶻ) →
        (hy : ∀ i, (y i).2.1 = τs i ∧ (y i).1 ∈ ⟦τs i⟧ᶻ) →
        (⟦body1 x⟧ˢ.get (h_isSome_eq.mpr den_t_isSome hx)).2.1 =
        (⟦body1 y⟧ˢ.get (h_isSome_eq.mpr den_t_isSome hy)).2.1) =
      (∀ (x y : Fin n → Dom),
        (hx : ∀ i, (x i).2.1 = τs i ∧ (x i).1 ∈ ⟦τs i⟧ᶻ) →
        (hy : ∀ i, (y i).2.1 = τs i ∧ (y i).1 ∈ ⟦τs i⟧ᶻ) →
        (⟦body2 x⟧ˢ.get (den_t_isSome hx)).2.1 =
        (⟦body2 y⟧ˢ.get (den_t_isSome hy)).2.1) := by
    apply propext; constructor <;> intro hh x y hx hy
    · rw [← congr_arg (·.2.1) (h_get x hx), ← congr_arg (·.2.1) (h_get y hy)]
      exact hh x y hx hy
    · rw [congr_arg (·.2.1) (h_get x hx), congr_arg (·.2.1) (h_get y hy)]
      exact hh x y hx hy
  refine dite_congr h_typ_det_eq (fun den_t_typ_det => ?_) (fun _ => rfl)
  have h_xₙ := h_get _ hxₙ
  have h_γ := congr_arg (·.2.1) h_xₙ
  apply congr_arg
  apply Dom_ext'
  · congr 1
    · exact congr_arg SMTType.toZFSet h_γ
    · funext x; split_ifs with hcond
      · have : ∀ i, (⟨x.get n i, τs i, hcond.2 i⟩ : Dom).2.1 = τs i ∧
                     (⟨x.get n i, τs i, hcond.2 i⟩ : Dom).1 ∈ ⟦τs i⟧ᶻ :=
          fun i => ⟨rfl, hcond.2 i⟩
        exact congr_arg (·.1) (h_get _ this)
      · exact congr_arg SMTType.defaultZFSet h_γ
  · exact congr_arg (SMTType.fun _) h_γ

/-- Congruence for forall denotation: if two body functions agree denotationally
on all arguments, their forall denotations are equal. -/
lemma denote_forall_congr {n : ℕ} {τs : Fin n → SMTType}
    {body1 body2 : (Fin n → SMT.Dom) → PHOAS.Term SMT.Dom}
    (h : ∀ αs : Fin n → SMT.Dom, SMT.denote (body1 αs) = SMT.denote (body2 αs)) :
    SMT.denote (PHOAS.Term.forall τs body1) = SMT.denote (PHOAS.Term.forall τs body2) := by
  simp only [SMT.denote]
  open Classical in
  refine dite_congr rfl (fun n_pos => ?_) (fun _ => rfl)
  have h_cond :
      (∀ {x : Fin n → Dom},
        (∀ (i : Fin n), (x i).snd.fst = τs i ∧ (x i).fst ∈ ⟦τs i⟧ᶻ) →
          ⟦body1 x⟧ˢ.isSome = true) =
      (∀ {x : Fin n → Dom},
        (∀ (i : Fin n), (x i).snd.fst = τs i ∧ (x i).fst ∈ ⟦τs i⟧ᶻ) →
          ⟦body2 x⟧ˢ.isSome = true) :=
    propext ⟨fun hh {x} hx => by rw [← h]; exact @hh x hx,
            fun hh {x} hx => by rw [h]; exact @hh x hx⟩
  refine dite_congr h_cond (fun h_isSome => ?_) (fun _ => rfl)
  apply congr_arg
  apply psigma_eq_of_fst_eq
  congr 1; congr 1; funext y; apply propext
  constructor <;> intro ⟨x, hx, hy⟩ <;> refine ⟨x, hx, ?_⟩ <;>
    simp only [hy] <;> split_ifs with hcond <;> try rfl
  · exact congr_arg PSigma.fst (Option.get_congr (h _))
  · exact congr_arg PSigma.fst (Option.get_congr (h _)).symm

lemma denote_not_congr {e1 e2 : SMT.PHOAS.Term SMT.Dom}
    (h : ⟦e1⟧ˢ = ⟦e2⟧ˢ) : ⟦PHOAS.Term.not e1⟧ˢ = ⟦PHOAS.Term.not e2⟧ˢ := by
  simp only [SMT.denote, h]

lemma denote_exists_congr {n : ℕ} {τs : Fin n → SMTType}
    {body1 body2 : (Fin n → SMT.Dom) → SMT.PHOAS.Term SMT.Dom}
    (h : ∀ αs : Fin n → SMT.Dom, SMT.denote (body1 αs) = SMT.denote (body2 αs)) :
    SMT.denote (SMT.PHOAS.Term.exists τs body1) = SMT.denote (SMT.PHOAS.Term.exists τs body2) := by
  simp only [SMT.PHOAS.Term.exists]
  apply denote_not_congr
  apply denote_forall_congr
  intro αs
  exact denote_not_congr (h αs)

private lemma abstractList_eq_denote {L1 L2 : List SMT.Term} (hL : L1 = L2)
    {ctx : Context}
    (h1 : ∀ e ∈ L1, ∀ v ∈ SMT.fv e, (ctx v).isSome)
    (h2 : ∀ e ∈ L2, ∀ v ∈ SMT.fv e, (ctx v).isSome)
    (i1 : Fin L1.length) (i2 : Fin L2.length) (hi : i1.val = i2.val) :
    ⟦SMT.Term.abstractList L1 ctx h1 i1⟧ˢ =
    ⟦SMT.Term.abstractList L2 ctx h2 i2⟧ˢ := by
  subst hL; exact congr_arg _ (congr_arg _ (Fin.ext hi))

private lemma attach_map_cons_eq (hd : SMT.Term) (tl : List SMT.Term) (f : SMT.Term → SMT.Term) :
    ((hd :: tl).attach.map (fun ⟨e, _⟩ => f e)) =
    f hd :: (tl.attach.map (fun ⟨e, _⟩ => f e)) := by
  simp [List.attach_cons, List.map_cons, List.map_map, Function.comp]

set_option maxHeartbeats 1600000 in
private theorem abstractList_subst_denote_inner
    (us : List SMT.Term) (x : SMT.𝒱) (t : SMT.Term)
    (ctx : Context) {D_t : Dom}
    (ih_us : ∀ t_1 ∈ us,
      x ∉ SMT.bv t_1 → (∀ w ∈ SMT.fv t, w ∉ SMT.bv t_1) →
        ∀ (h_sub : CoversFV ctx (SMT.subst x t t_1))
          (h_upd : CoversFV (Function.update ctx x (some D_t)) t_1),
          ⟦(SMT.subst x t t_1).abstract ctx h_sub⟧ˢ =
          ⟦t_1.abstract (Function.update ctx x (some D_t)) h_upd⟧ˢ)
    (hx_us : ∀ e ∈ us, x ∉ SMT.bv e)
    (hfv_us : ∀ e ∈ us, ∀ w ∈ SMT.fv t, w ∉ SMT.bv e)
    (m : ℕ)
    (h_sub : ∀ e ∈ (us.attach.map (fun ⟨e, _⟩ => SMT.subst x t e)),
      ∀ v ∈ SMT.fv e, (ctx v).isSome)
    (h_upd : ∀ e ∈ us,
      ∀ v ∈ SMT.fv e, (Function.update ctx x (some D_t) v).isSome)
    (hm1 : m < (us.attach.map (fun ⟨e, _⟩ => SMT.subst x t e)).length)
    (hm2 : m < us.length) :
    ⟦SMT.Term.abstractList (us.attach.map (fun ⟨e, _⟩ => SMT.subst x t e)) ctx h_sub ⟨m, hm1⟩⟧ˢ =
    ⟦SMT.Term.abstractList us (Function.update ctx x (some D_t)) h_upd ⟨m, hm2⟩⟧ˢ := by
  induction us generalizing m with
  | nil => simp at hm1
  | cons hd tl ih_tl =>
    have hcons := attach_map_cons_eq hd tl (SMT.subst x t)
    have h_sub' := hcons ▸ h_sub
    have hm1' : m < (SMT.subst x t hd :: tl.attach.map (fun ⟨e, _⟩ => SMT.subst x t e)).length :=
      hcons ▸ hm1
    rw [abstractList_eq_denote hcons h_sub h_sub' ⟨m, hm1⟩ ⟨m, hm1'⟩ rfl]
    cases m with
    | zero =>
      simp only [SMT.Term.abstractList, ↓reduceDIte]
      have h_sub_hd : CoversFV ctx (SMT.subst x t hd) := fun v hv =>
        h_sub' _ (List.mem_cons_self ..) v hv
      have h_upd_hd : CoversFV (Function.update ctx x (some D_t)) hd := fun v hv =>
        h_upd hd (List.mem_cons_self ..) v hv
      rw [denote_abstract_proof_irrel _ _ _ h_sub_hd, denote_abstract_proof_irrel _ _ _ h_upd_hd]
      exact ih_us hd (List.mem_cons_self ..)
        (hx_us hd (List.mem_cons_self ..))
        (hfv_us hd (List.mem_cons_self ..))
        h_sub_hd h_upd_hd
    | succ m =>
      have h0_lhs : (⟨m + 1, hm1'⟩ : Fin _) ≠ ⟨0, by omega⟩ := by simp [Fin.ext_iff]
      have h0_rhs : (⟨m + 1, hm2⟩ : Fin _) ≠ ⟨0, by omega⟩ := by simp [Fin.ext_iff]
      simp only [SMT.Term.abstractList, dif_neg h0_lhs, dif_neg h0_rhs]
      convert ih_tl
        (fun t1 ht1 => ih_us t1 (List.mem_cons_of_mem hd ht1))
        (fun e he => hx_us e (List.mem_cons_of_mem hd he))
        (fun e he => hfv_us e (List.mem_cons_of_mem hd he))
        m
        (fun e he v hv => h_sub' _ (List.mem_cons_of_mem _ he) v hv)
        (fun e he v hv => h_upd e (List.mem_cons_of_mem hd he) v hv)
        (Nat.lt_of_succ_lt_succ hm1') (Nat.lt_of_succ_lt_succ hm2) using 2

set_option maxHeartbeats 400000 in
theorem abstract_subst_denote (e : SMT.Term) (x : SMT.𝒱) (t : SMT.Term)
    {«Δ» : Context} {D_t : Dom}
    (hx_not_bv : x ∉ SMT.bv e)
    (hfv_t_bv_e : ∀ w ∈ SMT.fv t, w ∉ SMT.bv e)
    (ht_not_none : t ≠ .none)
    {ht_cov : CoversFV «Δ» t}
    (ht_den : ⟦t.abstract «Δ» ht_cov⟧ˢ = some D_t)
    (h_cov_subst : CoversFV «Δ» (SMT.subst x t e))
    (h_cov_upd : CoversFV (Function.update «Δ» x (some D_t)) e) :
    ⟦(SMT.subst x t e).abstract «Δ» h_cov_subst⟧ˢ =
    ⟦e.abstract (Function.update «Δ» x (some D_t)) h_cov_upd⟧ˢ := by
  induction e using SMT.Term.rec' generalizing «Δ» D_t with
  | int n => simp [SMT.subst, SMT.Term.abstract]
  | bool b => simp [SMT.subst, SMT.Term.abstract]
  | none => simp [SMT.subst, SMT.Term.abstract]
  | var v =>
    by_cases hv : v = x
    · subst hv
      -- LHS: ⟦(subst v t (.var v)).abstract Δ _⟧ˢ where subst v t (.var v) = t
      -- RHS: ⟦(.var v).abstract (update Δ v (some D_t)) _⟧ˢ = some D_t
      simp only [SMT.subst, ite_true, SMT.Term.abstract, Function.update_self,
        Option.get_some, SMT.denote] at *
      exact ht_den
    · -- v ≠ x: subst doesn't change .var v, and update doesn't change Δ v
      simp only [SMT.subst, hv, ite_false, SMT.Term.abstract, SMT.denote,
        Function.update_of_ne hv]
  | add a b ih_a ih_b =>
    simp only [SMT.bv, List.mem_append, not_or] at hx_not_bv
    have hbv_a := hx_not_bv.1
    have hbv_b := hx_not_bv.2
    have hfv_t_a : ∀ w ∈ SMT.fv t, w ∉ SMT.bv a := fun w hw => by
      have := hfv_t_bv_e w hw
      simp only [SMT.bv, List.mem_append, not_or] at this
      exact this.1
    have hfv_t_b : ∀ w ∈ SMT.fv t, w ∉ SMT.bv b := fun w hw => by
      have := hfv_t_bv_e w hw
      simp only [SMT.bv, List.mem_append, not_or] at this
      exact this.2
    have h_cov_subst_a : CoversFV «Δ» (SMT.subst x t a) := fun v hv =>
      h_cov_subst v (by simp only [SMT.subst, SMT.fv, List.mem_append]; exact Or.inl hv)
    have h_cov_subst_b : CoversFV «Δ» (SMT.subst x t b) := fun v hv =>
      h_cov_subst v (by simp only [SMT.subst, SMT.fv, List.mem_append]; exact Or.inr hv)
    have h_cov_upd_a : CoversFV (Function.update «Δ» x (some D_t)) a := fun v hv =>
      h_cov_upd v (by simp only [SMT.fv, List.mem_append]; exact Or.inl hv)
    have h_cov_upd_b : CoversFV (Function.update «Δ» x (some D_t)) b := fun v hv =>
      h_cov_upd v (by simp only [SMT.fv, List.mem_append]; exact Or.inr hv)
    have eq_a := ih_a hbv_a hfv_t_a ht_den h_cov_subst_a h_cov_upd_a
    have eq_b := ih_b hbv_b hfv_t_b ht_den h_cov_subst_b h_cov_upd_b
    simp only [SMT.subst, SMT.Term.abstract, SMT.denote, eq_a, eq_b]
  | sub a b ih_a ih_b =>
    simp only [SMT.bv, List.mem_append, not_or] at hx_not_bv
    have hbv_a := hx_not_bv.1
    have hbv_b := hx_not_bv.2
    have hfv_t_a : ∀ w ∈ SMT.fv t, w ∉ SMT.bv a := fun w hw => by
      have := hfv_t_bv_e w hw
      simp only [SMT.bv, List.mem_append, not_or] at this; exact this.1
    have hfv_t_b : ∀ w ∈ SMT.fv t, w ∉ SMT.bv b := fun w hw => by
      have := hfv_t_bv_e w hw
      simp only [SMT.bv, List.mem_append, not_or] at this; exact this.2
    have h_cov_subst_a : CoversFV «Δ» (SMT.subst x t a) := fun v hv =>
      h_cov_subst v (by simp only [SMT.subst, SMT.fv, List.mem_append]; exact Or.inl hv)
    have h_cov_subst_b : CoversFV «Δ» (SMT.subst x t b) := fun v hv =>
      h_cov_subst v (by simp only [SMT.subst, SMT.fv, List.mem_append]; exact Or.inr hv)
    have h_cov_upd_a : CoversFV (Function.update «Δ» x (some D_t)) a := fun v hv =>
      h_cov_upd v (by simp only [SMT.fv, List.mem_append]; exact Or.inl hv)
    have h_cov_upd_b : CoversFV (Function.update «Δ» x (some D_t)) b := fun v hv =>
      h_cov_upd v (by simp only [SMT.fv, List.mem_append]; exact Or.inr hv)
    have eq_a := ih_a hbv_a hfv_t_a ht_den h_cov_subst_a h_cov_upd_a
    have eq_b := ih_b hbv_b hfv_t_b ht_den h_cov_subst_b h_cov_upd_b
    simp only [SMT.subst, SMT.Term.abstract, SMT.denote, eq_a, eq_b]
  | mul a b ih_a ih_b =>
    simp only [SMT.bv, List.mem_append, not_or] at hx_not_bv
    have hbv_a := hx_not_bv.1
    have hbv_b := hx_not_bv.2
    have hfv_t_a : ∀ w ∈ SMT.fv t, w ∉ SMT.bv a := fun w hw => by
      have := hfv_t_bv_e w hw
      simp only [SMT.bv, List.mem_append, not_or] at this; exact this.1
    have hfv_t_b : ∀ w ∈ SMT.fv t, w ∉ SMT.bv b := fun w hw => by
      have := hfv_t_bv_e w hw
      simp only [SMT.bv, List.mem_append, not_or] at this; exact this.2
    have h_cov_subst_a : CoversFV «Δ» (SMT.subst x t a) := fun v hv =>
      h_cov_subst v (by simp only [SMT.subst, SMT.fv, List.mem_append]; exact Or.inl hv)
    have h_cov_subst_b : CoversFV «Δ» (SMT.subst x t b) := fun v hv =>
      h_cov_subst v (by simp only [SMT.subst, SMT.fv, List.mem_append]; exact Or.inr hv)
    have h_cov_upd_a : CoversFV (Function.update «Δ» x (some D_t)) a := fun v hv =>
      h_cov_upd v (by simp only [SMT.fv, List.mem_append]; exact Or.inl hv)
    have h_cov_upd_b : CoversFV (Function.update «Δ» x (some D_t)) b := fun v hv =>
      h_cov_upd v (by simp only [SMT.fv, List.mem_append]; exact Or.inr hv)
    have eq_a := ih_a hbv_a hfv_t_a ht_den h_cov_subst_a h_cov_upd_a
    have eq_b := ih_b hbv_b hfv_t_b ht_den h_cov_subst_b h_cov_upd_b
    simp only [SMT.subst, SMT.Term.abstract, SMT.denote, eq_a, eq_b]
  | le a b ih_a ih_b =>
    simp only [SMT.bv, List.mem_append, not_or] at hx_not_bv
    have hbv_a := hx_not_bv.1
    have hbv_b := hx_not_bv.2
    have hfv_t_a : ∀ w ∈ SMT.fv t, w ∉ SMT.bv a := fun w hw => by
      have := hfv_t_bv_e w hw
      simp only [SMT.bv, List.mem_append, not_or] at this; exact this.1
    have hfv_t_b : ∀ w ∈ SMT.fv t, w ∉ SMT.bv b := fun w hw => by
      have := hfv_t_bv_e w hw
      simp only [SMT.bv, List.mem_append, not_or] at this; exact this.2
    have h_cov_subst_a : CoversFV «Δ» (SMT.subst x t a) := fun v hv =>
      h_cov_subst v (by simp only [SMT.subst, SMT.fv, List.mem_append]; exact Or.inl hv)
    have h_cov_subst_b : CoversFV «Δ» (SMT.subst x t b) := fun v hv =>
      h_cov_subst v (by simp only [SMT.subst, SMT.fv, List.mem_append]; exact Or.inr hv)
    have h_cov_upd_a : CoversFV (Function.update «Δ» x (some D_t)) a := fun v hv =>
      h_cov_upd v (by simp only [SMT.fv, List.mem_append]; exact Or.inl hv)
    have h_cov_upd_b : CoversFV (Function.update «Δ» x (some D_t)) b := fun v hv =>
      h_cov_upd v (by simp only [SMT.fv, List.mem_append]; exact Or.inr hv)
    have eq_a := ih_a hbv_a hfv_t_a ht_den h_cov_subst_a h_cov_upd_a
    have eq_b := ih_b hbv_b hfv_t_b ht_den h_cov_subst_b h_cov_upd_b
    simp only [SMT.subst, SMT.Term.abstract, SMT.denote, eq_a, eq_b]
  | eq a b ih_a ih_b =>
    simp only [SMT.bv, List.mem_append, not_or] at hx_not_bv
    have hbv_a := hx_not_bv.1
    have hbv_b := hx_not_bv.2
    have hfv_t_a : ∀ w ∈ SMT.fv t, w ∉ SMT.bv a := fun w hw => by
      have := hfv_t_bv_e w hw
      simp only [SMT.bv, List.mem_append, not_or] at this; exact this.1
    have hfv_t_b : ∀ w ∈ SMT.fv t, w ∉ SMT.bv b := fun w hw => by
      have := hfv_t_bv_e w hw
      simp only [SMT.bv, List.mem_append, not_or] at this; exact this.2
    have h_cov_subst_a : CoversFV «Δ» (SMT.subst x t a) := fun v hv =>
      h_cov_subst v (by simp only [SMT.subst, SMT.fv, List.mem_append]; exact Or.inl hv)
    have h_cov_subst_b : CoversFV «Δ» (SMT.subst x t b) := fun v hv =>
      h_cov_subst v (by simp only [SMT.subst, SMT.fv, List.mem_append]; exact Or.inr hv)
    have h_cov_upd_a : CoversFV (Function.update «Δ» x (some D_t)) a := fun v hv =>
      h_cov_upd v (by simp only [SMT.fv, List.mem_append]; exact Or.inl hv)
    have h_cov_upd_b : CoversFV (Function.update «Δ» x (some D_t)) b := fun v hv =>
      h_cov_upd v (by simp only [SMT.fv, List.mem_append]; exact Or.inr hv)
    have eq_a := ih_a hbv_a hfv_t_a ht_den h_cov_subst_a h_cov_upd_a
    have eq_b := ih_b hbv_b hfv_t_b ht_den h_cov_subst_b h_cov_upd_b
    simp only [SMT.subst, SMT.Term.abstract, SMT.denote, eq_a, eq_b]
  | and a b ih_a ih_b =>
    simp only [SMT.bv, List.mem_append, not_or] at hx_not_bv
    have hbv_a := hx_not_bv.1
    have hbv_b := hx_not_bv.2
    have hfv_t_a : ∀ w ∈ SMT.fv t, w ∉ SMT.bv a := fun w hw => by
      have := hfv_t_bv_e w hw
      simp only [SMT.bv, List.mem_append, not_or] at this; exact this.1
    have hfv_t_b : ∀ w ∈ SMT.fv t, w ∉ SMT.bv b := fun w hw => by
      have := hfv_t_bv_e w hw
      simp only [SMT.bv, List.mem_append, not_or] at this; exact this.2
    have h_cov_subst_a : CoversFV «Δ» (SMT.subst x t a) := fun v hv =>
      h_cov_subst v (by simp only [SMT.subst, SMT.fv, List.mem_append]; exact Or.inl hv)
    have h_cov_subst_b : CoversFV «Δ» (SMT.subst x t b) := fun v hv =>
      h_cov_subst v (by simp only [SMT.subst, SMT.fv, List.mem_append]; exact Or.inr hv)
    have h_cov_upd_a : CoversFV (Function.update «Δ» x (some D_t)) a := fun v hv =>
      h_cov_upd v (by simp only [SMT.fv, List.mem_append]; exact Or.inl hv)
    have h_cov_upd_b : CoversFV (Function.update «Δ» x (some D_t)) b := fun v hv =>
      h_cov_upd v (by simp only [SMT.fv, List.mem_append]; exact Or.inr hv)
    have eq_a := ih_a hbv_a hfv_t_a ht_den h_cov_subst_a h_cov_upd_a
    have eq_b := ih_b hbv_b hfv_t_b ht_den h_cov_subst_b h_cov_upd_b
    simp only [SMT.subst, SMT.Term.abstract, SMT.denote, eq_a, eq_b]
  | or a b ih_a ih_b =>
    simp only [SMT.bv, List.mem_append, not_or] at hx_not_bv
    have hbv_a := hx_not_bv.1
    have hbv_b := hx_not_bv.2
    have hfv_t_a : ∀ w ∈ SMT.fv t, w ∉ SMT.bv a := fun w hw => by
      have := hfv_t_bv_e w hw
      simp only [SMT.bv, List.mem_append, not_or] at this; exact this.1
    have hfv_t_b : ∀ w ∈ SMT.fv t, w ∉ SMT.bv b := fun w hw => by
      have := hfv_t_bv_e w hw
      simp only [SMT.bv, List.mem_append, not_or] at this; exact this.2
    have h_cov_subst_a : CoversFV «Δ» (SMT.subst x t a) := fun v hv =>
      h_cov_subst v (by simp only [SMT.subst, SMT.fv, List.mem_append]; exact Or.inl hv)
    have h_cov_subst_b : CoversFV «Δ» (SMT.subst x t b) := fun v hv =>
      h_cov_subst v (by simp only [SMT.subst, SMT.fv, List.mem_append]; exact Or.inr hv)
    have h_cov_upd_a : CoversFV (Function.update «Δ» x (some D_t)) a := fun v hv =>
      h_cov_upd v (by simp only [SMT.fv, List.mem_append]; exact Or.inl hv)
    have h_cov_upd_b : CoversFV (Function.update «Δ» x (some D_t)) b := fun v hv =>
      h_cov_upd v (by simp only [SMT.fv, List.mem_append]; exact Or.inr hv)
    have eq_a := ih_a hbv_a hfv_t_a ht_den h_cov_subst_a h_cov_upd_a
    have eq_b := ih_b hbv_b hfv_t_b ht_den h_cov_subst_b h_cov_upd_b
    simp only [SMT.subst, SMT.Term.abstract, SMT.denote, eq_a, eq_b]
  | imp a b ih_a ih_b =>
    simp only [SMT.bv, List.mem_append, not_or] at hx_not_bv
    have hbv_a := hx_not_bv.1
    have hbv_b := hx_not_bv.2
    have hfv_t_a : ∀ w ∈ SMT.fv t, w ∉ SMT.bv a := fun w hw => by
      have := hfv_t_bv_e w hw
      simp only [SMT.bv, List.mem_append, not_or] at this; exact this.1
    have hfv_t_b : ∀ w ∈ SMT.fv t, w ∉ SMT.bv b := fun w hw => by
      have := hfv_t_bv_e w hw
      simp only [SMT.bv, List.mem_append, not_or] at this; exact this.2
    have h_cov_subst_a : CoversFV «Δ» (SMT.subst x t a) := fun v hv =>
      h_cov_subst v (by simp only [SMT.subst, SMT.fv, List.mem_append]; exact Or.inl hv)
    have h_cov_subst_b : CoversFV «Δ» (SMT.subst x t b) := fun v hv =>
      h_cov_subst v (by simp only [SMT.subst, SMT.fv, List.mem_append]; exact Or.inr hv)
    have h_cov_upd_a : CoversFV (Function.update «Δ» x (some D_t)) a := fun v hv =>
      h_cov_upd v (by simp only [SMT.fv, List.mem_append]; exact Or.inl hv)
    have h_cov_upd_b : CoversFV (Function.update «Δ» x (some D_t)) b := fun v hv =>
      h_cov_upd v (by simp only [SMT.fv, List.mem_append]; exact Or.inr hv)
    have eq_a := ih_a hbv_a hfv_t_a ht_den h_cov_subst_a h_cov_upd_a
    have eq_b := ih_b hbv_b hfv_t_b ht_den h_cov_subst_b h_cov_upd_b
    simp only [SMT.subst, SMT.Term.abstract, SMT.denote, eq_a, eq_b]
  | pair a b ih_a ih_b =>
    simp only [SMT.bv, List.mem_append, not_or] at hx_not_bv
    have hbv_a := hx_not_bv.1
    have hbv_b := hx_not_bv.2
    have hfv_t_a : ∀ w ∈ SMT.fv t, w ∉ SMT.bv a := fun w hw => by
      have := hfv_t_bv_e w hw
      simp only [SMT.bv, List.mem_append, not_or] at this; exact this.1
    have hfv_t_b : ∀ w ∈ SMT.fv t, w ∉ SMT.bv b := fun w hw => by
      have := hfv_t_bv_e w hw
      simp only [SMT.bv, List.mem_append, not_or] at this; exact this.2
    have h_cov_subst_a : CoversFV «Δ» (SMT.subst x t a) := fun v hv =>
      h_cov_subst v (by simp only [SMT.subst, SMT.fv, List.mem_append]; exact Or.inl hv)
    have h_cov_subst_b : CoversFV «Δ» (SMT.subst x t b) := fun v hv =>
      h_cov_subst v (by simp only [SMT.subst, SMT.fv, List.mem_append]; exact Or.inr hv)
    have h_cov_upd_a : CoversFV (Function.update «Δ» x (some D_t)) a := fun v hv =>
      h_cov_upd v (by simp only [SMT.fv, List.mem_append]; exact Or.inl hv)
    have h_cov_upd_b : CoversFV (Function.update «Δ» x (some D_t)) b := fun v hv =>
      h_cov_upd v (by simp only [SMT.fv, List.mem_append]; exact Or.inr hv)
    have eq_a := ih_a hbv_a hfv_t_a ht_den h_cov_subst_a h_cov_upd_a
    have eq_b := ih_b hbv_b hfv_t_b ht_den h_cov_subst_b h_cov_upd_b
    simp only [SMT.subst, SMT.Term.abstract, SMT.denote, eq_a, eq_b]
  | app a b ih_a ih_b =>
    simp only [SMT.bv, List.mem_append, not_or] at hx_not_bv
    have hbv_a := hx_not_bv.1
    have hbv_b := hx_not_bv.2
    have hfv_t_a : ∀ w ∈ SMT.fv t, w ∉ SMT.bv a := fun w hw => by
      have := hfv_t_bv_e w hw
      simp only [SMT.bv, List.mem_append, not_or] at this; exact this.1
    have hfv_t_b : ∀ w ∈ SMT.fv t, w ∉ SMT.bv b := fun w hw => by
      have := hfv_t_bv_e w hw
      simp only [SMT.bv, List.mem_append, not_or] at this; exact this.2
    have h_cov_subst_a : CoversFV «Δ» (SMT.subst x t a) := fun v hv =>
      h_cov_subst v (by simp only [SMT.subst, SMT.fv, List.mem_append]; exact Or.inl hv)
    have h_cov_subst_b : CoversFV «Δ» (SMT.subst x t b) := fun v hv =>
      h_cov_subst v (by simp only [SMT.subst, SMT.fv, List.mem_append]; exact Or.inr hv)
    have h_cov_upd_a : CoversFV (Function.update «Δ» x (some D_t)) a := fun v hv =>
      h_cov_upd v (by simp only [SMT.fv, List.mem_append]; exact Or.inl hv)
    have h_cov_upd_b : CoversFV (Function.update «Δ» x (some D_t)) b := fun v hv =>
      h_cov_upd v (by simp only [SMT.fv, List.mem_append]; exact Or.inr hv)
    have eq_a := ih_a hbv_a hfv_t_a ht_den h_cov_subst_a h_cov_upd_a
    have eq_b := ih_b hbv_b hfv_t_b ht_den h_cov_subst_b h_cov_upd_b
    simp only [SMT.subst, SMT.Term.abstract, SMT.denote, eq_a, eq_b]
  | not a ih_a =>
    simp only [SMT.bv] at hx_not_bv
    have hfv_t_a : ∀ w ∈ SMT.fv t, w ∉ SMT.bv a := fun w hw => by
      have := hfv_t_bv_e w hw; simp only [SMT.bv] at this; exact this
    have h_cov_subst_a : CoversFV «Δ» (SMT.subst x t a) := fun v hv =>
      h_cov_subst v (by simp only [SMT.subst, SMT.fv]; exact hv)
    have h_cov_upd_a : CoversFV (Function.update «Δ» x (some D_t)) a := fun v hv =>
      h_cov_upd v (by simp only [SMT.fv]; exact hv)
    have eq_a := ih_a hx_not_bv hfv_t_a ht_den h_cov_subst_a h_cov_upd_a
    simp only [SMT.subst, SMT.Term.abstract, SMT.denote, eq_a]
  | fst a ih_a =>
    simp only [SMT.bv] at hx_not_bv
    have hfv_t_a : ∀ w ∈ SMT.fv t, w ∉ SMT.bv a := fun w hw => by
      have := hfv_t_bv_e w hw; simp only [SMT.bv] at this; exact this
    have h_cov_subst_a : CoversFV «Δ» (SMT.subst x t a) := fun v hv =>
      h_cov_subst v (by simp only [SMT.subst, SMT.fv]; exact hv)
    have h_cov_upd_a : CoversFV (Function.update «Δ» x (some D_t)) a := fun v hv =>
      h_cov_upd v (by simp only [SMT.fv]; exact hv)
    have eq_a := ih_a hx_not_bv hfv_t_a ht_den h_cov_subst_a h_cov_upd_a
    simp only [SMT.subst, SMT.Term.abstract, SMT.denote, eq_a]
  | snd a ih_a =>
    simp only [SMT.bv] at hx_not_bv
    have hfv_t_a : ∀ w ∈ SMT.fv t, w ∉ SMT.bv a := fun w hw => by
      have := hfv_t_bv_e w hw; simp only [SMT.bv] at this; exact this
    have h_cov_subst_a : CoversFV «Δ» (SMT.subst x t a) := fun v hv =>
      h_cov_subst v (by simp only [SMT.subst, SMT.fv]; exact hv)
    have h_cov_upd_a : CoversFV (Function.update «Δ» x (some D_t)) a := fun v hv =>
      h_cov_upd v (by simp only [SMT.fv]; exact hv)
    have eq_a := ih_a hx_not_bv hfv_t_a ht_den h_cov_subst_a h_cov_upd_a
    simp only [SMT.subst, SMT.Term.abstract, SMT.denote, eq_a]
  | some a ih_a =>
    simp only [SMT.bv] at hx_not_bv
    have hfv_t_a : ∀ w ∈ SMT.fv t, w ∉ SMT.bv a := fun w hw => by
      have := hfv_t_bv_e w hw; simp only [SMT.bv] at this; exact this
    have h_cov_subst_a : CoversFV «Δ» (SMT.subst x t a) := fun v hv =>
      h_cov_subst v (by simp only [SMT.subst, SMT.fv]; exact hv)
    have h_cov_upd_a : CoversFV (Function.update «Δ» x (some D_t)) a := fun v hv =>
      h_cov_upd v (by simp only [SMT.fv]; exact hv)
    have eq_a := ih_a hx_not_bv hfv_t_a ht_den h_cov_subst_a h_cov_upd_a
    simp only [SMT.subst, SMT.Term.abstract, SMT.denote, eq_a]
  | the a ih_a =>
    simp only [SMT.bv] at hx_not_bv
    have hfv_t_a : ∀ w ∈ SMT.fv t, w ∉ SMT.bv a := fun w hw => by
      have := hfv_t_bv_e w hw; simp only [SMT.bv] at this; exact this
    have h_cov_subst_a : CoversFV «Δ» (SMT.subst x t a) := fun v hv =>
      h_cov_subst v (by simp only [SMT.subst, SMT.fv]; exact hv)
    have h_cov_upd_a : CoversFV (Function.update «Δ» x (some D_t)) a := fun v hv =>
      h_cov_upd v (by simp only [SMT.fv]; exact hv)
    have eq_a := ih_a hx_not_bv hfv_t_a ht_den h_cov_subst_a h_cov_upd_a
    simp only [SMT.subst, SMT.Term.abstract, SMT.denote, eq_a]
  | as a τ ih_a =>
    simp only [SMT.subst] at h_cov_subst ⊢
    have hx_bv_a : x ∉ SMT.bv a := by simpa [SMT.bv] using hx_not_bv
    have hfv_t_a : ∀ w ∈ SMT.fv t, w ∉ SMT.bv a := fun w hw => by
      have := hfv_t_bv_e w hw; simp only [SMT.bv] at this; exact this
    have h_cov_subst_a : CoversFV «Δ» (SMT.subst x t a) := fun v hv =>
      h_cov_subst v (by rwa [fv])
    have h_cov_upd_a : CoversFV (Function.update «Δ» x (some D_t)) a := fun v hv =>
      h_cov_upd v (by rwa [SMT.fv])
    have eq_a := ih_a hx_bv_a hfv_t_a ht_den h_cov_subst_a h_cov_upd_a
    cases a with
    | none =>
      simp only [SMT.subst]
      exact denote_congr_of_agreesOnFV (fun v hv => by simp [SMT.fv] at hv)
    | var v =>
      by_cases hv : v = x
      · -- subst x t (var x) = t; use eq_25 since t ≠ none
        have h_subst_not_none : SMT.subst x t (SMT.Term.var v) ≠ SMT.Term.none := by
          simp only [SMT.subst, hv, ite_true]; exact ht_not_none
        rw [SMT.Term.abstract.eq_25 «Δ» _ τ h_cov_subst
            (fun _ _ h_none _ _ => h_subst_not_none h_none)]
        rw [SMT.Term.abstract.eq_25 (Function.update «Δ» x (some D_t)) _ τ h_cov_upd
            (fun _ _ h_none _ _ => by cases h_none)]
        rw [denote_abstract_proof_irrel _ _ _ h_cov_subst_a,
            denote_abstract_proof_irrel _ _ _ h_cov_upd_a]
        exact eq_a
      · -- subst x t (var v) = var v since v ≠ x; contexts agree on [v]
        simp only [SMT.subst, hv, if_false] at *
        exact denote_congr_of_agreesOnFV (fun w hw => by
          simp only [SMT.fv, List.mem_cons, List.mem_nil_iff, or_false] at hw
          subst hw; simp [Function.update_of_ne hv])
    | _ =>
      -- a is a concrete constructor other than none and var;
      -- subst x t a has the same constructor shape, so ≠ none
      rw [SMT.Term.abstract.eq_25 «Δ» _ τ h_cov_subst
          (fun _ _ h_none _ _ => by
            simp only [SMT.subst] at h_none
            try split_ifs at h_none
            all_goals cases h_none)]
      rw [SMT.Term.abstract.eq_25 (Function.update «Δ» x (some D_t)) _ τ h_cov_upd
          (fun _ _ h_none _ _ => by cases h_none)]
      rw [denote_abstract_proof_irrel _ _ _ h_cov_subst_a,
          denote_abstract_proof_irrel _ _ _ h_cov_upd_a]
      exact eq_a

  | ite c th el ih_c ih_th ih_el =>
    simp only [SMT.bv, List.mem_append, not_or] at hx_not_bv
    obtain ⟨⟨hbv_c, hbv_th⟩, hbv_el⟩ := hx_not_bv
    have hfv_t_c : ∀ w ∈ SMT.fv t, w ∉ SMT.bv c := fun w hw => by
      have := hfv_t_bv_e w hw
      simp only [SMT.bv, List.mem_append, not_or] at this; exact this.1.1
    have hfv_t_th : ∀ w ∈ SMT.fv t, w ∉ SMT.bv th := fun w hw => by
      have := hfv_t_bv_e w hw
      simp only [SMT.bv, List.mem_append, not_or] at this; exact this.1.2
    have hfv_t_el : ∀ w ∈ SMT.fv t, w ∉ SMT.bv el := fun w hw => by
      have := hfv_t_bv_e w hw
      simp only [SMT.bv, List.mem_append, not_or] at this; exact this.2
    have h_cov_subst_c : CoversFV «Δ» (SMT.subst x t c) := fun v hv =>
      h_cov_subst v (by simp only [SMT.subst, SMT.fv, List.mem_append]; exact Or.inl (Or.inl hv))
    have h_cov_subst_th : CoversFV «Δ» (SMT.subst x t th) := fun v hv =>
      h_cov_subst v (by simp only [SMT.subst, SMT.fv, List.mem_append]; exact Or.inl (Or.inr hv))
    have h_cov_subst_el : CoversFV «Δ» (SMT.subst x t el) := fun v hv =>
      h_cov_subst v (by simp only [SMT.subst, SMT.fv, List.mem_append]; exact Or.inr hv)
    have h_cov_upd_c : CoversFV (Function.update «Δ» x (some D_t)) c := fun v hv =>
      h_cov_upd v (by simp only [SMT.fv, List.mem_append]; exact Or.inl (Or.inl hv))
    have h_cov_upd_th : CoversFV (Function.update «Δ» x (some D_t)) th := fun v hv =>
      h_cov_upd v (by simp only [SMT.fv, List.mem_append]; exact Or.inl (Or.inr hv))
    have h_cov_upd_el : CoversFV (Function.update «Δ» x (some D_t)) el := fun v hv =>
      h_cov_upd v (by simp only [SMT.fv, List.mem_append]; exact Or.inr hv)
    have eq_c := ih_c hbv_c hfv_t_c ht_den h_cov_subst_c h_cov_upd_c
    have eq_th := ih_th hbv_th hfv_t_th ht_den h_cov_subst_th h_cov_upd_th
    have eq_el := ih_el hbv_el hfv_t_el ht_den h_cov_subst_el h_cov_upd_el
    simp only [SMT.subst, SMT.Term.abstract, SMT.denote, eq_c, eq_th, eq_el]
  | distinct ts ih_ts =>
    simp only [SMT.subst, SMT.Term.abstract, SMT.denote]
    congr 1; apply congr_arg
    apply List.ext_getElem
    · simp [List.length_ofFn, List.length_map]
    · intro n hn1 hn2
      simp only [List.getElem_ofFn, List.length_ofFn] at hn1 hn2 ⊢
      exact abstractList_subst_denote_inner ts x t «Δ»
        (fun t1 ht1 hbv hfv => ih_ts t1 ht1 hbv hfv ht_den)
        (fun e he h => hx_not_bv (by simp only [SMT.bv]; exact List.mem_flatten_of_mem (List.mem_map.mpr ⟨⟨e, he⟩, List.mem_attach .., rfl⟩) h))
        (fun e he w hw h => hfv_t_bv_e w hw (by simp only [SMT.bv]; exact List.mem_flatten_of_mem (List.mem_map.mpr ⟨⟨e, he⟩, List.mem_attach .., rfl⟩) h))
        n _ _ hn1 hn2
  | lambda vs τs P ih_P =>
    simp only [SMT.bv, List.mem_append, not_or] at hx_not_bv
    have hx_not_vs : x ∉ vs := hx_not_bv.1
    have hx_not_bv_P : x ∉ SMT.bv P := hx_not_bv.2
    have hfv_t_bv_P : ∀ w ∈ SMT.fv t, w ∉ SMT.bv P := fun w hw => by
      have := hfv_t_bv_e w hw
      simp only [SMT.bv, List.mem_append, not_or] at this; exact this.2
    have hx_not_vs_mem : ¬(x ∈ vs) := hx_not_vs
    simp only [SMT.subst, hx_not_vs_mem, ite_false] at h_cov_subst ⊢
    by_cases h_len : vs.length = τs.length
    · simp only [SMT.Term.abstract, h_len, ↓reduceDIte]
      apply denote_lambda_congr
      intro f
      have hcov_subst_body : ∀ v ∈ SMT.fv (SMT.subst x t P),
          (Function.updates «Δ» vs (List.map Option.some (List.ofFn f)) v).isSome = true := by
        intro v hv
        by_cases hvs : v ∈ vs
        · exact Function.updates_isSome_of_mem_map_some «Δ» vs (List.ofFn f) v hvs (by simp)
        · rw [Function.updates_of_not_mem (f := «Δ») (xs := vs)
              (ys := (List.ofFn f).map Option.some) (k := v) hvs]
          exact h_cov_subst v (fv.mem_lambda ⟨hv, hvs⟩)
      have hcov_upd_body : ∀ v ∈ SMT.fv P,
          (Function.updates (Function.update «Δ» x (some D_t)) vs
            (List.map Option.some (List.ofFn f)) v).isSome = true := by
        intro v hv
        by_cases hvs : v ∈ vs
        · exact Function.updates_isSome_of_mem_map_some _ vs (List.ofFn f) v hvs (by simp)
        · rw [Function.updates_of_not_mem (f := Function.update «Δ» x (some D_t)) (xs := vs)
              (ys := (List.ofFn f).map Option.some) (k := v) hvs]
          exact h_cov_upd v (fv.mem_lambda ⟨hv, hvs⟩)
      have hgo_subst := SMT.Term.abstract.go.alt_def₂ (vs := vs) (P := SMT.subst x t P)
        (Δctx := «Δ») (αs := List.ofFn f) (vs_αs_len := by simp)
        (Δ_isSome := by
          intro v hv hv_not_vs
          exact h_cov_subst v (fv.mem_lambda ⟨hv, hv_not_vs⟩))
        (tmp₁ := hcov_subst_body)
      have hgo_upd := SMT.Term.abstract.go.alt_def₂ (vs := vs) (P := P)
        (Δctx := Function.update «Δ» x (some D_t)) (αs := List.ofFn f) (vs_αs_len := by simp)
        (Δ_isSome := by
          intro v hv hv_not_vs
          exact h_cov_upd v (fv.mem_lambda ⟨hv, hv_not_vs⟩))
        (tmp₁ := hcov_upd_body)
      have h_ofFn : (fun i => (List.ofFn f)[i]) = f := by funext i; simp
      rw [show (Term.abstract.go (SMT.subst x t P) vs «Δ»
            (fun v hv h => h_cov_subst v (fv.mem_lambda ⟨hv, h⟩))).uncurry f
            = (SMT.subst x t P).abstract (Function.updates «Δ» vs
                ((List.ofFn f).map Option.some)) hcov_subst_body by simpa [h_ofFn] using hgo_subst]
      rw [show (Term.abstract.go P vs (Function.update «Δ» x (some D_t))
            (fun v hv h => h_cov_upd v (fv.mem_lambda ⟨hv, h⟩))).uncurry f
            = P.abstract (Function.updates (Function.update «Δ» x (some D_t)) vs
                ((List.ofFn f).map Option.some)) hcov_upd_body by simpa [h_ofFn] using hgo_upd]
      have ht_cov' : CoversFV (Function.updates «Δ» vs ((List.ofFn f).map Option.some)) t := by
        intro w hw
        have hw_not_vs : w ∉ vs := fun hmem => hfv_t_bv_e w hw
          (by simp only [SMT.bv, List.mem_append]; exact Or.inl hmem)
        rw [Function.updates_of_not_mem (f := «Δ») (xs := vs)
            (ys := (List.ofFn f).map Option.some) (k := w) hw_not_vs]
        exact ht_cov w hw
      have ht_den' : ⟦t.abstract (Function.updates «Δ» vs ((List.ofFn f).map Option.some)) ht_cov'⟧ˢ =
          some D_t := by
        have hag : AgreesOnFV (Function.updates «Δ» vs ((List.ofFn f).map Option.some)) «Δ» t := by
          intro w hw
          have hw_not_vs : w ∉ vs := fun hmem => hfv_t_bv_e w hw
            (by simp only [SMT.bv, List.mem_append]; exact Or.inl hmem)
          rw [Function.updates_of_not_mem (f := «Δ») (xs := vs)
              (ys := (List.ofFn f).map Option.some) (k := w) hw_not_vs]
        rw [← ht_den]
        exact denote_congr_of_agreesOnFV (h1 := ht_cov') (h2 := ht_cov) hag
      have hctx_comm : Function.update (Function.updates «Δ» vs ((List.ofFn f).map Option.some)) x (some D_t) =
          Function.updates (Function.update «Δ» x (some D_t)) vs ((List.ofFn f).map Option.some) := by
        funext v
        by_cases hv_vs : v ∈ vs
        · simp only [Function.update_of_ne (show v ≠ x from fun heq => hx_not_vs (heq ▸ hv_vs))]
          exact (Function.updates_eq_of_mem_map_some (Function.update «Δ» x (some D_t)) «Δ» vs
            (List.ofFn f) v hv_vs (by simp)).symm
        · by_cases hvx : v = x
          · subst hvx
            simp only [Function.update_self,
              Function.updates_of_not_mem (f := Function.update «Δ» v (some D_t)) (xs := vs)
                (ys := (List.ofFn f).map Option.some) (k := v) hv_vs]
          · simp only [Function.update_of_ne hvx,
              Function.updates_of_not_mem (f := «Δ») (xs := vs) (ys := (List.ofFn f).map Option.some) (k := v) hv_vs,
              Function.updates_of_not_mem (f := Function.update «Δ» x (some D_t)) (xs := vs)
                (ys := (List.ofFn f).map Option.some) (k := v) hv_vs]
      have h_cov_subst_P : CoversFV (Function.updates «Δ» vs ((List.ofFn f).map Option.some)) (SMT.subst x t P) := by
        intro v hv
        by_cases hv_vs : v ∈ vs
        · exact Function.updates_isSome_of_mem_map_some «Δ» vs (List.ofFn f) v hv_vs (by simp)
        · rw [Function.updates_of_not_mem (f := «Δ») (xs := vs)
              (ys := (List.ofFn f).map Option.some) (k := v) hv_vs]
          exact h_cov_subst v (fv.mem_lambda ⟨hv, hv_vs⟩)
      have h_cov_upd_P : CoversFV (Function.update (Function.updates «Δ» vs ((List.ofFn f).map Option.some)) x (some D_t)) P := by
        rw [hctx_comm]; exact hcov_upd_body
      have eq_body := ih_P hx_not_bv_P hfv_t_bv_P ht_den' h_cov_subst_P h_cov_upd_P
      calc ⟦(SMT.subst x t P).abstract (Function.updates «Δ» vs ((List.ofFn f).map Option.some))
              hcov_subst_body⟧ˢ
          = ⟦(SMT.subst x t P).abstract (Function.updates «Δ» vs ((List.ofFn f).map Option.some))
              h_cov_subst_P⟧ˢ :=
            denote_abstract_proof_irrel _ _ hcov_subst_body h_cov_subst_P
        _ = ⟦P.abstract (Function.update (Function.updates «Δ» vs ((List.ofFn f).map Option.some))
              x (some D_t)) h_cov_upd_P⟧ˢ := eq_body
        _ = ⟦P.abstract (Function.updates (Function.update «Δ» x (some D_t)) vs
              ((List.ofFn f).map Option.some)) hcov_upd_body⟧ˢ :=
            denote_congr_of_agreesOnFV (h1 := h_cov_upd_P) (h2 := hcov_upd_body)
              (fun v _ => congr_fun hctx_comm v)
    · simp [SMT.Term.abstract, h_len]
  | «forall» vs τs P ih_P =>
    simp only [SMT.bv, List.mem_append, not_or] at hx_not_bv
    have hx_not_vs : x ∉ vs := hx_not_bv.1
    have hx_not_bv_P : x ∉ SMT.bv P := hx_not_bv.2
    have hfv_t_bv_P : ∀ w ∈ SMT.fv t, w ∉ SMT.bv P := fun w hw => by
      have := hfv_t_bv_e w hw
      simp only [SMT.bv, List.mem_append, not_or] at this; exact this.2
    have hx_not_vs_mem : ¬(x ∈ vs) := hx_not_vs
    simp only [SMT.subst, hx_not_vs_mem, ite_false] at h_cov_subst ⊢
    by_cases h_len : vs.length = τs.length
    · simp only [SMT.Term.abstract, h_len, ↓reduceDIte]
      apply denote_forall_congr
      intro f
      have hcov_subst_body : ∀ v ∈ SMT.fv (SMT.subst x t P),
          (Function.updates «Δ» vs (List.map Option.some (List.ofFn f)) v).isSome = true := by
        intro v hv
        by_cases hvs : v ∈ vs
        · exact Function.updates_isSome_of_mem_map_some «Δ» vs (List.ofFn f) v hvs (by simp)
        · rw [Function.updates_of_not_mem (f := «Δ») (xs := vs)
              (ys := (List.ofFn f).map Option.some) (k := v) hvs]
          exact h_cov_subst v (fv.mem_forall ⟨hv, hvs⟩)
      have hcov_upd_body : ∀ v ∈ SMT.fv P,
          (Function.updates (Function.update «Δ» x (some D_t)) vs
            (List.map Option.some (List.ofFn f)) v).isSome = true := by
        intro v hv
        by_cases hvs : v ∈ vs
        · exact Function.updates_isSome_of_mem_map_some _ vs (List.ofFn f) v hvs (by simp)
        · rw [Function.updates_of_not_mem (f := Function.update «Δ» x (some D_t)) (xs := vs)
              (ys := (List.ofFn f).map Option.some) (k := v) hvs]
          exact h_cov_upd v (fv.mem_forall ⟨hv, hvs⟩)
      have hgo_subst := SMT.Term.abstract.go.alt_def₂ (vs := vs) (P := SMT.subst x t P)
        (Δctx := «Δ») (αs := List.ofFn f) (vs_αs_len := by simp)
        (Δ_isSome := by
          intro v hv hv_not_vs
          exact h_cov_subst v (fv.mem_forall ⟨hv, hv_not_vs⟩))
        (tmp₁ := hcov_subst_body)
      have hgo_upd := SMT.Term.abstract.go.alt_def₂ (vs := vs) (P := P)
        (Δctx := Function.update «Δ» x (some D_t)) (αs := List.ofFn f) (vs_αs_len := by simp)
        (Δ_isSome := by
          intro v hv hv_not_vs
          exact h_cov_upd v (fv.mem_forall ⟨hv, hv_not_vs⟩))
        (tmp₁ := hcov_upd_body)
      have h_ofFn : (fun i => (List.ofFn f)[i]) = f := by funext i; simp
      rw [show (Term.abstract.go (SMT.subst x t P) vs «Δ»
            (fun v hv h => h_cov_subst v (fv.mem_forall ⟨hv, h⟩))).uncurry f
            = (SMT.subst x t P).abstract (Function.updates «Δ» vs
                ((List.ofFn f).map Option.some)) hcov_subst_body by
          simpa [h_ofFn] using hgo_subst]
      rw [show (Term.abstract.go P vs (Function.update «Δ» x (some D_t))
            (fun v hv h => h_cov_upd v (fv.mem_forall ⟨hv, h⟩))).uncurry f
            = P.abstract (Function.updates (Function.update «Δ» x (some D_t)) vs
                ((List.ofFn f).map Option.some)) hcov_upd_body by
          simpa [h_ofFn] using hgo_upd]
      have ht_cov' : CoversFV (Function.updates «Δ» vs ((List.ofFn f).map Option.some)) t := by
        intro w hw
        have hw_not_vs : w ∉ vs := fun hmem => hfv_t_bv_e w hw
          (by simp only [SMT.bv, List.mem_append]; exact Or.inl hmem)
        rw [Function.updates_of_not_mem (f := «Δ») (xs := vs)
            (ys := (List.ofFn f).map Option.some) (k := w) hw_not_vs]
        exact ht_cov w hw
      have ht_den' : ⟦t.abstract (Function.updates «Δ» vs ((List.ofFn f).map Option.some)) ht_cov'⟧ˢ =
          some D_t := by
        have hag : AgreesOnFV (Function.updates «Δ» vs ((List.ofFn f).map Option.some)) «Δ» t := by
          intro w hw
          have hw_not_vs : w ∉ vs := fun hmem => hfv_t_bv_e w hw
            (by simp only [SMT.bv, List.mem_append]; exact Or.inl hmem)
          rw [Function.updates_of_not_mem (f := «Δ») (xs := vs)
              (ys := (List.ofFn f).map Option.some) (k := w) hw_not_vs]
        rw [← ht_den]; exact denote_congr_of_agreesOnFV (h1 := ht_cov') (h2 := ht_cov) hag
      have hctx_comm : Function.update (Function.updates «Δ» vs ((List.ofFn f).map Option.some)) x (some D_t) =
          Function.updates (Function.update «Δ» x (some D_t)) vs ((List.ofFn f).map Option.some) := by
        funext v
        by_cases hv_vs : v ∈ vs
        · simp only [Function.update_of_ne (show v ≠ x from fun heq => hx_not_vs (heq ▸ hv_vs))]
          exact (Function.updates_eq_of_mem_map_some (Function.update «Δ» x (some D_t)) «Δ» vs
            (List.ofFn f) v hv_vs (by simp)).symm
        · by_cases hvx : v = x
          · subst hvx
            simp only [Function.update_self,
              Function.updates_of_not_mem (f := Function.update «Δ» v (some D_t)) (xs := vs)
                (ys := (List.ofFn f).map Option.some) (k := v) hv_vs]
          · simp only [Function.update_of_ne hvx,
              Function.updates_of_not_mem (f := «Δ») (xs := vs) (ys := (List.ofFn f).map Option.some) (k := v) hv_vs,
              Function.updates_of_not_mem (f := Function.update «Δ» x (some D_t)) (xs := vs)
                (ys := (List.ofFn f).map Option.some) (k := v) hv_vs]
      have h_cov_subst_P : CoversFV (Function.updates «Δ» vs ((List.ofFn f).map Option.some)) (SMT.subst x t P) := by
        intro v hv
        by_cases hv_vs : v ∈ vs
        · exact Function.updates_isSome_of_mem_map_some «Δ» vs (List.ofFn f) v hv_vs (by simp)
        · rw [Function.updates_of_not_mem (f := «Δ») (xs := vs)
              (ys := (List.ofFn f).map Option.some) (k := v) hv_vs]
          exact h_cov_subst v (fv.mem_forall ⟨hv, hv_vs⟩)
      have h_cov_upd_P : CoversFV (Function.update (Function.updates «Δ» vs ((List.ofFn f).map Option.some)) x (some D_t)) P := by
        rw [hctx_comm]; exact hcov_upd_body
      have eq_body := ih_P hx_not_bv_P hfv_t_bv_P ht_den' h_cov_subst_P h_cov_upd_P
      calc ⟦(SMT.subst x t P).abstract (Function.updates «Δ» vs ((List.ofFn f).map Option.some))
              hcov_subst_body⟧ˢ
          = ⟦(SMT.subst x t P).abstract (Function.updates «Δ» vs ((List.ofFn f).map Option.some))
              h_cov_subst_P⟧ˢ :=
            denote_abstract_proof_irrel _ _ hcov_subst_body h_cov_subst_P
        _ = ⟦P.abstract (Function.update (Function.updates «Δ» vs ((List.ofFn f).map Option.some))
              x (some D_t)) h_cov_upd_P⟧ˢ := eq_body
        _ = ⟦P.abstract (Function.updates (Function.update «Δ» x (some D_t)) vs
              ((List.ofFn f).map Option.some)) hcov_upd_body⟧ˢ :=
            denote_congr_of_agreesOnFV (h1 := h_cov_upd_P) (h2 := hcov_upd_body)
              (fun v _ => congr_fun hctx_comm v)
    · simp [SMT.Term.abstract, h_len]
  | «exists» vs τs P ih_P =>
    simp only [SMT.bv, List.mem_append, not_or] at hx_not_bv
    have hx_not_vs : x ∉ vs := hx_not_bv.1
    have hx_not_bv_P : x ∉ SMT.bv P := hx_not_bv.2
    have hfv_t_bv_P : ∀ w ∈ SMT.fv t, w ∉ SMT.bv P := fun w hw => by
      have := hfv_t_bv_e w hw
      simp only [SMT.bv, List.mem_append, not_or] at this; exact this.2
    have hx_not_vs_mem : ¬(x ∈ vs) := hx_not_vs
    simp only [SMT.subst, hx_not_vs_mem, ite_false] at h_cov_subst ⊢
    by_cases h_len : vs.length = τs.length
    · simp only [Term.abstract, h_len, ↓reduceDIte]
      -- exists = ¬(forall(¬ ...)), use denote_exists_congr
      apply denote_exists_congr
      intro f
      have hcov_subst_body : ∀ v ∈ SMT.fv (SMT.subst x t P),
          (Function.updates «Δ» vs (List.map Option.some (List.ofFn f)) v).isSome = true := by
        intro v hv
        by_cases hvs : v ∈ vs
        · exact Function.updates_isSome_of_mem_map_some «Δ» vs (List.ofFn f) v hvs (by simp)
        · rw [Function.updates_of_not_mem (f := «Δ») (xs := vs)
              (ys := (List.ofFn f).map Option.some) (k := v) hvs]
          exact h_cov_subst v (fv.mem_exists ⟨hv, hvs⟩)
      have hcov_upd_body : ∀ v ∈ SMT.fv P,
          (Function.updates (Function.update «Δ» x (some D_t)) vs
            (List.map Option.some (List.ofFn f)) v).isSome = true := by
        intro v hv
        by_cases hvs : v ∈ vs
        · exact Function.updates_isSome_of_mem_map_some _ vs (List.ofFn f) v hvs (by simp)
        · rw [Function.updates_of_not_mem (f := Function.update «Δ» x (some D_t)) (xs := vs)
              (ys := (List.ofFn f).map Option.some) (k := v) hvs]
          exact h_cov_upd v (fv.mem_exists ⟨hv, hvs⟩)
      have hgo_subst := SMT.Term.abstract.go.alt_def₂ (vs := vs) (P := SMT.subst x t P)
        (Δctx := «Δ») (αs := List.ofFn f) (vs_αs_len := by simp)
        (Δ_isSome := by
          intro v hv hv_not_vs
          exact h_cov_subst v (fv.mem_exists ⟨hv, hv_not_vs⟩))
        (tmp₁ := hcov_subst_body)
      have hgo_upd := SMT.Term.abstract.go.alt_def₂ (vs := vs) (P := P)
        (Δctx := Function.update «Δ» x (some D_t)) (αs := List.ofFn f) (vs_αs_len := by simp)
        (Δ_isSome := by
          intro v hv hv_not_vs
          exact h_cov_upd v (fv.mem_exists ⟨hv, hv_not_vs⟩))
        (tmp₁ := hcov_upd_body)
      have h_ofFn : (fun i => (List.ofFn f)[i]) = f := by funext i; simp
      rw [show (Term.abstract.go (SMT.subst x t P) vs «Δ»
            (fun v hv h => h_cov_subst v (fv.mem_exists ⟨hv, h⟩))).uncurry f
            = (SMT.subst x t P).abstract (Function.updates «Δ» vs
                ((List.ofFn f).map Option.some)) hcov_subst_body by
          simpa [h_ofFn] using hgo_subst]
      rw [show (Term.abstract.go P vs (Function.update «Δ» x (some D_t))
            (fun v hv h => h_cov_upd v (fv.mem_exists ⟨hv, h⟩))).uncurry f
            = P.abstract (Function.updates (Function.update «Δ» x (some D_t)) vs
                ((List.ofFn f).map Option.some)) hcov_upd_body by
          simpa [h_ofFn] using hgo_upd]
      have ht_cov' : CoversFV (Function.updates «Δ» vs ((List.ofFn f).map Option.some)) t := by
        intro w hw
        have hw_not_vs : w ∉ vs := fun hmem => hfv_t_bv_e w hw
          (by simp only [SMT.bv, List.mem_append]; exact Or.inl hmem)
        rw [Function.updates_of_not_mem (f := «Δ») (xs := vs)
            (ys := (List.ofFn f).map Option.some) (k := w) hw_not_vs]
        exact ht_cov w hw
      have ht_den' : ⟦t.abstract (Function.updates «Δ» vs ((List.ofFn f).map Option.some)) ht_cov'⟧ˢ =
          some D_t := by
        have hag : AgreesOnFV (Function.updates «Δ» vs ((List.ofFn f).map Option.some)) «Δ» t := by
          intro w hw
          have hw_not_vs : w ∉ vs := fun hmem => hfv_t_bv_e w hw
            (by simp only [SMT.bv, List.mem_append]; exact Or.inl hmem)
          rw [Function.updates_of_not_mem (f := «Δ») (xs := vs)
              (ys := (List.ofFn f).map Option.some) (k := w) hw_not_vs]
        rw [← ht_den]; exact denote_congr_of_agreesOnFV (h1 := ht_cov') (h2 := ht_cov) hag
      have hctx_comm : Function.update (Function.updates «Δ» vs ((List.ofFn f).map Option.some)) x (some D_t) =
          Function.updates (Function.update «Δ» x (some D_t)) vs ((List.ofFn f).map Option.some) := by
        funext v
        by_cases hv_vs : v ∈ vs
        · simp only [Function.update_of_ne (show v ≠ x from fun heq => hx_not_vs (heq ▸ hv_vs))]
          exact (Function.updates_eq_of_mem_map_some (Function.update «Δ» x (some D_t)) «Δ» vs
            (List.ofFn f) v hv_vs (by simp)).symm
        · by_cases hvx : v = x
          · subst hvx
            simp only [Function.update_self,
              Function.updates_of_not_mem (f := Function.update «Δ» v (some D_t)) (xs := vs)
                (ys := (List.ofFn f).map Option.some) (k := v) hv_vs]
          · simp only [Function.update_of_ne hvx,
              Function.updates_of_not_mem (f := «Δ») (xs := vs) (ys := (List.ofFn f).map Option.some) (k := v) hv_vs,
              Function.updates_of_not_mem (f := Function.update «Δ» x (some D_t)) (xs := vs)
                (ys := (List.ofFn f).map Option.some) (k := v) hv_vs]
      have h_cov_subst_P : CoversFV (Function.updates «Δ» vs ((List.ofFn f).map Option.some)) (SMT.subst x t P) := by
        intro v hv
        by_cases hv_vs : v ∈ vs
        · exact Function.updates_isSome_of_mem_map_some «Δ» vs (List.ofFn f) v hv_vs (by simp)
        · rw [Function.updates_of_not_mem (f := «Δ») (xs := vs)
              (ys := (List.ofFn f).map Option.some) (k := v) hv_vs]
          exact h_cov_subst v (fv.mem_exists ⟨hv, hv_vs⟩)
      have h_cov_upd_P : CoversFV (Function.update (Function.updates «Δ» vs ((List.ofFn f).map Option.some)) x (some D_t)) P := by
        rw [hctx_comm]; exact hcov_upd_body
      have eq_body := ih_P hx_not_bv_P hfv_t_bv_P ht_den' h_cov_subst_P h_cov_upd_P
      calc ⟦(SMT.subst x t P).abstract (Function.updates «Δ» vs ((List.ofFn f).map Option.some))
              hcov_subst_body⟧ˢ
          = ⟦(SMT.subst x t P).abstract (Function.updates «Δ» vs ((List.ofFn f).map Option.some))
              h_cov_subst_P⟧ˢ :=
            denote_abstract_proof_irrel _ _ hcov_subst_body h_cov_subst_P
        _ = ⟦P.abstract (Function.update (Function.updates «Δ» vs ((List.ofFn f).map Option.some))
              x (some D_t)) h_cov_upd_P⟧ˢ := eq_body
        _ = ⟦P.abstract (Function.updates (Function.update «Δ» x (some D_t)) vs
              ((List.ofFn f).map Option.some)) hcov_upd_body⟧ˢ :=
            denote_congr_of_agreesOnFV (h1 := h_cov_upd_P) (h2 := hcov_upd_body)
              (fun v _ => congr_fun hctx_comm v)
    · simp [SMT.Term.abstract, h_len]

private theorem bv_subst_subset {x : SMT.𝒱} {t e : SMT.Term}
    (hbv_t : SMT.bv t = []) : ∀ v ∈ SMT.bv (SMT.subst x t e), v ∈ SMT.bv e := by
  intro v hv
  induction e using SMT.Term.rec' with
  | var w => simp only [SMT.subst] at hv; split_ifs at hv <;> simp_all [SMT.bv]
  | int _ | bool _ | none => simp [SMT.subst, SMT.bv] at hv
  | app f a ihf iha =>
    simp only [SMT.subst, SMT.bv, List.mem_append] at hv ⊢
    exact hv.elim (Or.inl ∘ ihf) (Or.inr ∘ iha)
  | add a b iha ihb | sub a b iha ihb | mul a b iha ihb | le a b iha ihb
  | eq a b iha ihb | and a b iha ihb | or a b iha ihb | imp a b iha ihb =>
    simp only [SMT.subst, SMT.bv, List.mem_append] at hv ⊢
    exact hv.elim (Or.inl ∘ iha) (Or.inr ∘ ihb)
  | not a ih => simp only [SMT.subst, SMT.bv] at hv ⊢; exact ih hv
  | ite c a b ihc iha ihb =>
    simp only [SMT.subst, SMT.bv, List.mem_append] at hv ⊢
    rcases hv with (hv | hv) | hv
    · exact Or.inl (Or.inl (ihc hv))
    · exact Or.inl (Or.inr (iha hv))
    · exact Or.inr (ihb hv)
  | lambda vs τs body ih =>
    simp only [SMT.subst] at hv; split_ifs at hv
    · simp only [SMT.bv, List.mem_append] at hv ⊢; exact hv
    · simp only [SMT.bv, List.mem_append] at hv ⊢; exact hv.elim Or.inl (Or.inr ∘ ih)
  | «forall» vs τs body ih =>
    simp only [SMT.subst] at hv; split_ifs at hv
    · simp only [SMT.bv, List.mem_append] at hv ⊢; exact hv
    · simp only [SMT.bv, List.mem_append] at hv ⊢; exact hv.elim Or.inl (Or.inr ∘ ih)
  | «exists» vs τs body ih =>
    simp only [SMT.subst] at hv; split_ifs at hv
    · simp only [SMT.bv, List.mem_append] at hv ⊢; exact hv
    · simp only [SMT.bv, List.mem_append] at hv ⊢; exact hv.elim Or.inl (Or.inr ∘ ih)
  | some a ih => simp only [SMT.subst, SMT.bv] at hv ⊢; exact ih hv
  | the a ih => simp only [SMT.subst, SMT.bv] at hv ⊢; exact ih hv
  | pair a b iha ihb =>
    simp only [SMT.subst, SMT.bv, List.mem_append] at hv ⊢
    exact hv.elim (Or.inl ∘ iha) (Or.inr ∘ ihb)
  | fst a ih | snd a ih => simp only [SMT.subst, SMT.bv] at hv ⊢; exact ih hv
  | distinct vs ih =>
    simp only [SMT.subst, SMT.bv, List.mem_flatten] at hv ⊢
    obtain ⟨l, hl_mem, hv_l⟩ := hv
    simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists] at hl_mem
    obtain ⟨u, hu_mem, rfl⟩ := hl_mem
    obtain ⟨w, hw_mem, hw_eq⟩ := hu_mem
    refine ⟨SMT.bv w, ?_, ih w hw_mem (hw_eq ▸ hv_l)⟩
    simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists]
    exact ⟨w, hw_mem, rfl⟩
  | as a _ ih => simp only [SMT.subst, SMT.bv] at hv ⊢; exact ih hv

private theorem fv_subst_of_ne {v x : SMT.𝒱} {t e : SMT.Term}
    (hv : v ∈ SMT.fv e) (hvx : v ≠ x) : v ∈ SMT.fv (SMT.subst x t e) := by
  induction e using SMT.Term.rec' with
  | var w =>
    simp only [SMT.fv, List.mem_singleton] at hv; subst hv
    simp only [SMT.subst, hvx, ite_false, SMT.fv, List.mem_singleton]
  | int _ | bool _ | none => simp [SMT.fv] at hv
  | app f a ihf iha =>
    simp only [SMT.subst, SMT.fv, List.mem_append] at hv ⊢
    exact hv.elim (Or.inl ∘ ihf) (Or.inr ∘ iha)
  | add a b iha ihb | sub a b iha ihb | mul a b iha ihb | le a b iha ihb
  | eq a b iha ihb | and a b iha ihb | or a b iha ihb | imp a b iha ihb =>
    simp only [SMT.subst, SMT.fv, List.mem_append] at hv ⊢
    exact hv.elim (Or.inl ∘ iha) (Or.inr ∘ ihb)
  | not a ih => simp only [SMT.subst, SMT.fv] at hv ⊢; exact ih hv
  | ite c a b ihc iha ihb =>
    simp only [SMT.subst, SMT.fv, List.mem_append] at hv ⊢
    rcases hv with (hv | hv) | hv
    · exact Or.inl (Or.inl (ihc hv))
    · exact Or.inl (Or.inr (iha hv))
    · exact Or.inr (ihb hv)
  | lambda vs τs body ih =>
    simp only [SMT.fv, List.mem_removeAll_iff] at hv
    simp only [SMT.subst]; split_ifs with hxvs
    · simp only [SMT.fv, List.mem_removeAll_iff]; exact hv
    · simp only [SMT.fv, List.mem_removeAll_iff]; exact ⟨ih hv.1, hv.2⟩
  | «forall» vs τs body ih =>
    simp only [SMT.fv, List.mem_removeAll_iff] at hv
    simp only [SMT.subst]; split_ifs with hxvs
    · simp only [SMT.fv, List.mem_removeAll_iff]; exact hv
    · simp only [SMT.fv, List.mem_removeAll_iff]; exact ⟨ih hv.1, hv.2⟩
  | «exists» vs τs body ih =>
    simp only [SMT.fv, List.mem_removeAll_iff] at hv
    simp only [SMT.subst]; split_ifs with hxvs
    · simp only [SMT.fv, List.mem_removeAll_iff]; exact hv
    · simp only [SMT.fv, List.mem_removeAll_iff]; exact ⟨ih hv.1, hv.2⟩
  | some a ih => simp only [SMT.subst, SMT.fv] at hv ⊢; exact ih hv
  | the a ih => simp only [SMT.subst, SMT.fv] at hv ⊢; exact ih hv
  | pair a b iha ihb =>
    simp only [SMT.subst, SMT.fv, List.mem_append] at hv ⊢
    exact hv.elim (Or.inl ∘ iha) (Or.inr ∘ ihb)
  | fst a ih | snd a ih => simp only [SMT.subst, SMT.fv] at hv ⊢; exact ih hv
  | distinct vs ih =>
    simp only [SMT.subst, SMT.fv, List.mem_flatten] at hv ⊢
    obtain ⟨l, hl_mem, hv_l⟩ := hv
    simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists] at hl_mem
    obtain ⟨w, hw_mem, rfl⟩ := hl_mem
    refine ⟨SMT.fv (SMT.subst x t w), ?_, ih w hw_mem hv_l⟩
    simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists]
    exact ⟨SMT.subst x t w, ⟨w, hw_mem, rfl⟩, rfl⟩
  | as a _ ih => simp only [SMT.subst, SMT.fv] at hv ⊢; exact ih hv

private theorem fv_mem_fv_substList {v : SMT.𝒱} {xs : List SMT.𝒱} {ts : List SMT.Term} {e : SMT.Term}
    (hv : v ∈ SMT.fv e) (hvxs : v ∉ xs) (hts_fv_disj : ∀ t ∈ ts, ∀ w ∈ SMT.fv t, w ∉ xs)
    (hts_bv : ∀ t ∈ ts, SMT.bv t = []) :
    v ∈ SMT.fv (SMT.substList xs ts e) := by
  induction xs generalizing ts e with
  | nil => match ts with | [] | _::_ => simpa [SMT.substList]
  | cons x xs ih =>
    match ts with
    | [] => simpa [SMT.substList]
    | t :: ts =>
      unfold SMT.substList
      have hvx : v ≠ x := fun h => hvxs (h ▸ List.mem_cons_self ..)
      exact ih (fv_subst_of_ne hv hvx) (List.not_mem_of_not_mem_cons hvxs)
        (fun t' ht' w hw => List.not_mem_of_not_mem_cons
          (hts_fv_disj t' (List.mem_cons_of_mem _ ht') w hw))
        (fun t' ht' => hts_bv t' (List.mem_cons_of_mem _ ht'))

set_option maxHeartbeats 1600000 in
theorem abstract_substList_denote (e : SMT.Term) (xs : List SMT.𝒱) (ts : List SMT.Term)
    {«Δ» : Context} (Ds : List Dom)
    (hlen_xt : xs.length = ts.length) (hlen_xd : xs.length = Ds.length)
    (hnodup : xs.Nodup)
    (hxs_not_bv : ∀ x ∈ xs, x ∉ SMT.bv e)
    (hts_bv_nil : ∀ t ∈ ts, SMT.bv t = [])
    (hts_fv_not_bv : ∀ t ∈ ts, ∀ w ∈ SMT.fv t, w ∉ SMT.bv e)
    (hts_not_none : ∀ t ∈ ts, t ≠ SMT.Term.none)
    (hts_fv_disj_xs : ∀ t ∈ ts, ∀ w ∈ SMT.fv t, w ∉ xs)
    (hts_den : ∀ (i : ℕ) (hi_x : i < xs.length) (hi_t : i < ts.length) (hi_d : i < Ds.length),
      ∃ (ht_cov : CoversFV «Δ» ts[i]),
        ⟦ts[i].abstract «Δ» ht_cov⟧ˢ = some Ds[i])
    (h_cov_sub : CoversFV «Δ» (SMT.substList xs ts e))
    (h_cov_upd : CoversFV (Function.updates «Δ» xs (Ds.map Option.some)) e) :
    ⟦(SMT.substList xs ts e).abstract «Δ» h_cov_sub⟧ˢ =
    ⟦e.abstract (Function.updates «Δ» xs (Ds.map Option.some)) h_cov_upd⟧ˢ := by
  induction xs generalizing ts Ds e «Δ» with
  | nil =>
    match ts, Ds with
    | [], [] => simp only [SMT.substList, Function.updates]
    | [], _::_ => simp at hlen_xd
    | _::_, _ => simp at hlen_xt
  | cons x xs ih =>
    match ts, Ds with
    | [], _ => simp at hlen_xt
    | _::_, [] => simp at hlen_xd
    | t :: ts, D :: Ds =>
      simp only [List.length_cons] at hlen_xt hlen_xd
      have hlen_xt' : xs.length = ts.length := Nat.succ_inj.mp hlen_xt
      have hlen_xd' : xs.length = Ds.length := Nat.succ_inj.mp hlen_xd
      have hx_nodup : x ∉ xs := (List.nodup_cons.mp hnodup).1
      have xs_nodup : xs.Nodup := (List.nodup_cons.mp hnodup).2
      have hx_bv : x ∉ SMT.bv e := hxs_not_bv x (List.mem_cons_self ..)
      have ht_fv_bv : ∀ w ∈ SMT.fv t, w ∉ SMT.bv e := hts_fv_not_bv t (List.mem_cons_self ..)
      have ht_not_none : t ≠ SMT.Term.none := hts_not_none t (List.mem_cons_self ..)
      have ht_bv_nil : SMT.bv t = [] := hts_bv_nil t (List.mem_cons_self ..)
      obtain ⟨ht_cov, ht_den⟩ := hts_den 0
        (Nat.zero_lt_succ xs.length)
        (Nat.zero_lt_succ ts.length)
        (Nat.zero_lt_succ Ds.length)
      have hbv_subst : ∀ v ∈ SMT.bv (SMT.subst x t e), v ∈ SMT.bv e := bv_subst_subset ht_bv_nil
      show ⟦(SMT.substList xs ts (SMT.subst x t e)).abstract «Δ» h_cov_sub⟧ˢ = _
      have h_cov_upd_xs : CoversFV (Function.updates «Δ» xs (Ds.map Option.some)) (SMT.subst x t e) := by
        intro v hv
        by_cases hvxs : v ∈ xs
        · exact Function.updates_isSome_of_mem_map_some «Δ» xs Ds v hvxs (by simp [hlen_xd'])
        · rw [Function.updates_of_not_mem «Δ» xs _ v hvxs]
          exact h_cov_sub v (fv_mem_fv_substList (e := SMT.subst x t e) hv hvxs
            (fun t' ht' w hw => List.not_mem_of_not_mem_cons
              (hts_fv_disj_xs t' (List.mem_cons_of_mem _ ht') w hw))
            (fun t' ht' => hts_bv_nil t' (List.mem_cons_of_mem _ ht')))
      have h_eq_ih := ih (SMT.subst x t e) ts Ds hlen_xt' hlen_xd' xs_nodup
        (fun y hy hbv => hxs_not_bv y (List.mem_cons_of_mem _ hy) (hbv_subst _ hbv))
        (fun t' ht' => hts_bv_nil t' (List.mem_cons_of_mem _ ht'))
        (fun t' ht' w hw hbv => hts_fv_not_bv t' (List.mem_cons_of_mem _ ht') w hw (hbv_subst _ hbv))
        (fun t' ht' => hts_not_none t' (List.mem_cons_of_mem _ ht'))
        (fun t' ht' w hw => List.not_mem_of_not_mem_cons
          (hts_fv_disj_xs t' (List.mem_cons_of_mem _ ht') w hw))
        (fun i hi_x hi_t hi_d => hts_den (i + 1)
          (Nat.add_lt_of_lt_sub hi_x)
          (Nat.add_lt_of_lt_sub hi_t)
          (Nat.add_lt_of_lt_sub hi_d))
        h_cov_sub h_cov_upd_xs
      have ht_fv_disj : ∀ w ∈ SMT.fv t, w ∉ xs :=
        fun w hw => List.not_mem_of_not_mem_cons (hts_fv_disj_xs t (List.mem_cons_self ..) w hw)
      have ht_cov' : CoversFV «Δ» t := ht_cov
      have ht_cov_upd : CoversFV (Function.updates «Δ» xs (Ds.map Option.some)) t := by
        intro v hv; rw [Function.updates_of_not_mem «Δ» xs _ v (ht_fv_disj v hv)]; exact ht_cov' v hv
      have ht_den_upd : ⟦t.abstract (Function.updates «Δ» xs (Ds.map Option.some)) ht_cov_upd⟧ˢ
          = some D := by
        have h := denote_congr_of_agreesOnFV (h1 := ht_cov') (h2 := ht_cov_upd)
          (fun v hv => (Function.updates_of_not_mem «Δ» xs _ v (ht_fv_disj v hv)).symm)
        simp only [denote] at h; rw [← h]; exact ht_den
      have h_ctx_eq : ∀ v, Function.update (Function.updates «Δ» xs (Ds.map Option.some)) x (some D) v =
          Function.updates «Δ» (x :: xs) ((D :: Ds).map Option.some) v := by
        intro v
        show _ = Function.updates (Function.update «Δ» x (some D)) xs (Ds.map Option.some) v
        by_cases hvxs : v ∈ xs
        · have hvx : v ≠ x := fun h => hx_nodup (h ▸ hvxs)
          rw [Function.update_of_ne hvx,
            Function.updates_eq_of_mem_map_some (Function.update «Δ» x (some D)) «Δ» xs Ds v hvxs
              (by simp [hlen_xd']),
            Function.updates_eq_of_mem_map_some «Δ» «Δ» xs Ds v hvxs (by simp [hlen_xd'])]
        · rw [Function.updates_of_not_mem (Function.update «Δ» x (some D)) xs _ v hvxs]
          by_cases hvx : v = x
          · subst hvx; simp [Function.update_self]
          · rw [Function.update_of_ne hvx, Function.update_of_ne hvx,
              Function.updates_of_not_mem «Δ» xs _ v hvxs]
      have h_cov_upd_e : CoversFV (Function.update (Function.updates «Δ» xs (Ds.map Option.some))
          x (some D)) e := fun v hv => by rw [h_ctx_eq]; exact h_cov_upd v hv
      have h_eq_subst := abstract_subst_denote e x t hx_bv ht_fv_bv ht_not_none
        ht_den_upd h_cov_upd_xs h_cov_upd_e
      calc ⟦(SMT.substList xs ts (SMT.subst x t e)).abstract «Δ» h_cov_sub⟧ˢ
          = ⟦(SMT.subst x t e).abstract (Function.updates «Δ» xs (Ds.map Option.some))
              h_cov_upd_xs⟧ˢ := h_eq_ih
        _ = ⟦e.abstract (Function.update (Function.updates «Δ» xs (Ds.map Option.some)) x (some D))
              h_cov_upd_e⟧ˢ := h_eq_subst
        _ = ⟦e.abstract (Function.updates «Δ» (x :: xs) ((D :: Ds).map Option.some)) h_cov_upd⟧ˢ :=
              denote_congr_of_agreesOnFV (h1 := h_cov_upd_e) (h2 := h_cov_upd)
                (fun v _ => h_ctx_eq v)

end SMT.RenamingContext
