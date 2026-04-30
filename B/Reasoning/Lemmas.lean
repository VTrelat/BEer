import B.Simplifier
import B.SemanticsPHOAS

open Classical B PHOAS ZFSet

theorem BType.mem_get_of_mem_foldl_prod {𝒟 : ZFSet} {n : ℕ} {αs : Fin (n + 1) → BType}
  {x : ZFSet} (hx : x ∈ 𝒟)
  (𝒟α : 𝒟 ∈ (Fin.foldl n (fun d i => d ×ᴮ αs i.succ) (αs 0)).set.toZFSet)
  {i : Fin (n + 1)} :
  x.get (n + 1) i ∈ ((Fin.foldl n (fun d i => d ×ᴮ αs i.succ) (αs 0)).get (n + 1) i).toZFSet := by
  induction n generalizing x 𝒟 with
  | zero =>
    rcases Fin.fin_one_eq_zero i
    simp only [Fin.isValue, Fin.foldl_zero, Nat.reduceAdd, ZFSet.get] at 𝒟α ⊢
    rw [BType.get, dite_cond_eq_true (eq_true (by rfl))]
    rw [BType.toZFSet, ZFSet.mem_powerset] at 𝒟α
    exact 𝒟α hx
  | succ n ih =>
    rw [Fin.foldl_succ_last, BType.get]
    rw [BType.toZFSet, ZFSet.mem_powerset, Fin.foldl_succ_last, BType.toZFSet] at 𝒟α
    obtain ⟨a, ha, b, hb, eq⟩ := mem_prod.mp <| 𝒟α hx
    rw [eq]
    split_ifs with hi
    · rcases Fin.eq_mk_iff_val_eq (hk := Nat.lt_add_one (n + 1)).mpr hi
      clear hi
      rwa [ZFSet.get, dite_cond_eq_true (eq_true (by rfl)), ZFSet.π₂_pair]
    · rw [ZFSet.get, ZFSet.π₁_pair, π₂_pair]
      rw [dite_cond_eq_false (eq_false (by rwa [Fin.ext_iff, Fin.val_last]))]
      apply @ih _ (fun ⟨i, hi⟩ => αs ⟨i, Nat.lt_add_right 1 hi⟩) a ha
      simp only [Nat.zero_mod, Fin.zero_eta]
      rw [BType.toZFSet]
      exact ZFSet.mem_powerset_self

def Fin.foldlRecOn {n} {β} {motive : β → Sort _} : ∀ (i : Fin n) (op : β → Fin ↑i → β) {b : β} (_ : motive b)
    (_ : ∀ (b : β) (_ : motive b) (j : Fin i), motive (op b j)), motive (Fin.foldl i op b) := fun ⟨i, hi⟩ op b _ hl => by
  induction i generalizing b with
  | zero => rwa [Fin.foldl_zero]
  | succ i ih =>
    rw [foldl_succ]
    apply ih
    · apply hl
      assumption
    · exact fun b x j => hl b x j.succ
    · exact Nat.lt_of_succ_lt hi

class WFTC (Γ : TypeContext Dom) where
  wf v v' : Γ v = some v' → v.2.1 = v'

theorem TypeContext.update1 {Γ : TypeContext Dom} {v : Dom} {α : BType} :
  Γ.update (fun _ : Fin 1 => v) (fun _ => α) v = some α := by
  rw [TypeContext.update, Fin.foldl_succ, Fin.foldl_zero, Function.update, dite_cond_eq_true <| eq_true rfl]

theorem WFTC.update1 {Γ} [WFTC Γ] {v : Dom} {α : BType} (hv : v.2.1 = α) :
  WFTC (Γ.update (fun _ : Fin 1 => v) (fun _ => α)) where
  wf := by
    rintro x β eq_some
    by_cases hx : x = v
    · subst hx
      rw [TypeContext.update1, Option.some_inj] at eq_some
      rcases eq_some
      exact hv
    · rw [TypeContext.update, Fin.foldl_succ, Fin.foldl_zero, Function.update_apply] at eq_some
      split_ifs at eq_some
      exact WFTC.wf _ _ eq_some

theorem TypeContext.update_succ {Γ : TypeContext Dom} {n} {vs : Fin (n + 1) → Dom} {αs : Fin (n + 1) → BType} :
  Γ.update vs αs = (Γ.update (fun _ : Fin 1 => vs 0) (fun _ => αs 0)).update (fun i => vs i.succ) (fun i => αs i.succ) := by
  rw [TypeContext.update, Fin.foldl_succ, ←TypeContext.update]
  have : Function.update Γ (vs 0) (some (αs 0)) = Γ.update (fun _ : Fin 1 => vs 0) (fun _ => αs 0) := by
    rw [TypeContext.update, Fin.foldl_succ, Fin.foldl_zero]
  rw [this]

theorem WFTC.update {Γ} [WFTC Γ] {n} {vs : Fin n → Dom} {τs : Fin n → BType} (vs_τs_wf : ∀ i, (vs i).2.1 = τs i) :
  WFTC <| Γ.update vs τs where
    wf := by
      intro v τ eq_some
      induction n generalizing Γ with
      | zero =>
        rw [TypeContext.update, Fin.foldl_zero] at eq_some
        exact WFTC.wf _ _ eq_some
      | succ n ih =>
        rw [TypeContext.update_succ] at eq_some
        apply @ih (Γ.update (fun _ : Fin 1 => vs 0) (fun _ => τs 0)) (WFTC.update1 (vs_τs_wf 0)) (fun i => vs i.succ) (fun i => τs i.succ)
        · exact (vs_τs_wf ·.succ)
        · exact eq_some

abbrev WellTyped' (t : PHOAS.Term Dom) := Σ' (Γ : TypeContext Dom) (_ : WFTC Γ) (τ : BType), Γ ⊢ᴮ' t : τ

instance : Nonempty (Π n, Fin n → Dom) := ⟨fun _ _ => ⟨∅, .bool, ZFBool.zffalse_mem_𝔹⟩⟩

theorem denote_welltyped_eq {t : PHOAS.Term Dom} {T τ hTτ}
  (wt_t : WellTyped' t)
  (den_t : ⟦t⟧ᴮ = some ⟨T, τ, hTτ⟩) : wt_t.2.2.1 = τ := by
  induction t generalizing T τ with
  | var v =>
    obtain ⟨Γ, Γwf, τ, hτ⟩ := wt_t
    obtain ⟨V, σ, hσ⟩ := v
    rcases WFTC.wf _ _ <| PHOAS.Typing.varE hτ
    rcases den_t
    rfl
  | int n =>
    obtain ⟨Γ, _, τ, hτ⟩ := wt_t
    rcases PHOAS.Typing.intE hτ
    rcases den_t
    rfl
  | bool b =>
    obtain ⟨Γ, _, τ, hτ⟩ := wt_t
    rcases PHOAS.Typing.boolE hτ
    rcases den_t
    rfl
  | maplet x y x_ih y_ih =>
    obtain ⟨Γ, Γwf, _, typ⟩ := wt_t
    obtain ⟨α, β, rfl, hx, hy⟩ := Typing.mapletE typ
    simp_rw [denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at den_t
    obtain ⟨⟨X, α, Xα⟩, den_x, ⟨Y, β, Yβ⟩, den_y, ⟨⟩⟩ := den_t
    obtain ⟨⟩ := x_ih ⟨Γ, Γwf, _, hx⟩ den_x
    obtain ⟨⟩ := y_ih ⟨Γ, Γwf, _, hy⟩ den_y
    rfl
  | add x y x_ih y_ih
  | sub x y x_ih y_ih
  | mul x y x_ih y_ih
  | le x y x_ih y_ih
  | and x y x_ih y_ih =>
    obtain ⟨Γ, Γwf, _, typ⟩ := wt_t
    first
    | obtain ⟨rfl, hx, hy⟩ := Typing.addE typ
    | obtain ⟨rfl, hx, hy⟩ := Typing.subE typ
    | obtain ⟨rfl, hx, hy⟩ := Typing.mulE typ
    | obtain ⟨rfl, hx, hy⟩ := Typing.leE typ
    | obtain ⟨rfl, hx, hy⟩ := Typing.andE typ
    simp_rw [denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_t
    obtain ⟨X, τ, Xτ, den_x, other⟩ := den_t
    obtain ⟨⟩ := x_ih ⟨Γ, Γwf, _, hx⟩ den_x
    simp_rw [Option.bind_eq_some_iff] at other
    obtain ⟨⟨Y, τ, Yτ⟩, den_y, other⟩ := other
    obtain ⟨⟩ := y_ih ⟨Γ, Γwf, _, hy⟩ den_y
    simp only [Option.some.injEq, PSigma.mk.injEq] at other
    obtain ⟨⟨⟩, _⟩ := other
    injections
  | eq x y x_ih y_ih =>
    obtain ⟨Γ, Γwf, _, typ⟩ := wt_t
    obtain ⟨rfl, α, hx, hy⟩ := Typing.eqE typ
    simp_rw [denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_t
    obtain ⟨X, τ, Xτ, den_x, Y, σ, Yσ, den_y, other⟩ := den_t
    obtain ⟨⟩ := x_ih ⟨Γ, Γwf, _, hx⟩ den_x
    obtain ⟨⟩ := y_ih ⟨Γ, Γwf, _, hy⟩ den_y
    simp only [dite_cond_eq_true, Option.some.injEq, PSigma.mk.injEq] at other
    obtain ⟨⟨⟩, _⟩ := other
    injections
  | not x ih
  | pow x ih =>
    obtain ⟨Γ, Γwf, τ, hτ⟩ := wt_t
    first
    | obtain ⟨rfl, hx⟩ := PHOAS.Typing.notE hτ
    | obtain ⟨α, rfl, hx⟩ := PHOAS.Typing.powE hτ
    simp_rw [denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_t
    obtain ⟨X, τ, Xτ, den_x, other⟩ := den_t
    obtain ⟨⟩ := ih ⟨Γ, Γwf, _, hx⟩ den_x
    simp only [Option.some.injEq, PSigma.mk.injEq] at other
    obtain ⟨⟨⟩, _⟩ := other
    injections
  | min S ih
  | max S ih
  | card S ih =>
    obtain ⟨Γ, Γwf, τ, hτ⟩ := wt_t
    first
    | obtain ⟨rfl, hS⟩ := PHOAS.Typing.minE hτ
    | obtain ⟨rfl, hS⟩ := PHOAS.Typing.maxE hτ
    | obtain ⟨rfl, _, hS⟩ := PHOAS.Typing.cardE hτ
    simp_rw [denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_t
    obtain ⟨X, τ, Xτ, den_S, other⟩ := den_t
    obtain ⟨⟩ := ih ⟨Γ, Γwf, _, hS⟩ den_S
    simp only at other
    split_ifs at other with X_cond
    injections
    subst_eqs
    rfl
  | «ℤ»
  | 𝔹 =>
    obtain ⟨Γ, Γwf, τ, hτ⟩ := wt_t
    first
    | rcases PHOAS.Typing.ℤE hτ
    | rcases PHOAS.Typing.𝔹E hτ
    simp_rw [denote, Option.pure_def, Option.some.injEq, PSigma.mk.injEq] at den_t
    obtain ⟨⟨⟩, _⟩ := den_t
    injections
  | union S T S_ih T_ih
  | inter S T S_ih T_ih
  | cprod S T S_ih T_ih =>
    obtain ⟨Γ, Γwf, τ, hτ⟩ := wt_t
    first
    | obtain ⟨α, rfl, hS, hT⟩ := PHOAS.Typing.unionE hτ
    | obtain ⟨α, rfl, hS, hT⟩ := PHOAS.Typing.interE hτ
    | obtain ⟨α, β, rfl, hS, hT⟩ := PHOAS.Typing.cprodE hτ
    simp_rw [denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_t
    obtain ⟨X, τ, Xτ, den_S, other⟩ := den_t
    obtain ⟨⟩ := S_ih ⟨Γ, Γwf, _, hS⟩ den_S
    simp only [Option.bind_eq_some_iff, PSigma.exists] at other
    obtain ⟨Y, τ, Yτ, den_T, other⟩ := other
    obtain ⟨⟩ := T_ih ⟨Γ, Γwf, _, hT⟩ den_T
    simp only [dite_cond_eq_true, Option.some.injEq, PSigma.mk.injEq] at other
    obtain ⟨⟨⟩, _⟩ := other
    injections
  | mem x S x_ih S_ih =>
    obtain ⟨Γ, Γwf, τ, hτ⟩ := wt_t
    obtain ⟨rfl, α, hS, hT⟩ := PHOAS.Typing.memE hτ
    simp only [denote, Option.pure_def, dite_eq_ite, Option.bind_eq_bind, Option.bind_eq_some_iff] at den_t
    obtain ⟨⟨X, τ, Xτ⟩, den_x, ⟨S, σ, Sσ⟩, den_S, other⟩ := den_t
    obtain ⟨⟩ := x_ih ⟨Γ, Γwf, _, hS⟩ den_x
    obtain ⟨⟩ := S_ih ⟨Γ, Γwf, _, hT⟩ den_S
    simp only [if_true, Option.some.injEq, PSigma.mk.injEq] at other
    obtain ⟨⟨⟩, _⟩ := other
    injections
  | pfun A B A_ih B_ih =>
    obtain ⟨Γ, Γwf, τ, hτ⟩ := wt_t
    obtain ⟨α, β, rfl, hA, hB⟩ := PHOAS.Typing.pfunE hτ
    simp_rw [denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_t
    obtain ⟨X, τ, Xτ, den_A, other⟩ := den_t
    obtain ⟨⟩ := A_ih ⟨Γ, Γwf, _, hA⟩ den_A
    simp only [Option.bind_eq_some_iff] at other
    obtain ⟨⟨Y, σ, Yσ⟩, den_B, other⟩ := other
    obtain ⟨⟩ := B_ih ⟨Γ, Γwf, _, hB⟩ den_B
    simp only [Option.some.injEq, PSigma.mk.injEq] at other
    obtain ⟨⟨⟩, _⟩ := other
    injections
  | app f x f_ih x_ih =>
    obtain ⟨Γ, Γwf, τ, hτ⟩ := wt_t
    obtain ⟨α, hf, hx⟩ := PHOAS.Typing.appE hτ
    simp_rw [denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_t
    obtain ⟨F, τ, Fτ, den_F, other⟩ := den_t
    obtain ⟨⟩ := f_ih ⟨Γ, Γwf, _, hf⟩ den_F
    simp only [Option.bind_eq_some_iff] at other
    obtain ⟨⟨X, σ, Xσ⟩, den_X, other⟩ := other
    obtain ⟨⟩ := x_ih ⟨Γ, Γwf, _, hx⟩ den_X
    simp only [dite_cond_eq_true] at other
    split_ifs at other
    injections
    subst_eqs
    rfl
  | collect D P D_ih P_ih =>
    obtain ⟨Γ, Γwf, α, hτ⟩ := wt_t
    obtain ⟨n_pos, ⟨αs, Ds⟩, ⟨α_eq, hDs, D_eq, typP⟩, αs_Ds_unq⟩ := PHOAS.Typing.collectE hτ
    clear αs_Ds_unq
    simp_rw [denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_t
    obtain ⟨𝒟, _, 𝒟α, den_D, other⟩ := den_t
    dsimp at D_eq α_eq

    obtain ⟨n, rfl⟩ := Nat.exists_add_one_eq.mpr n_pos
    have wt_D : Γ ⊢ᴮ' D : α := by
      simp_rw [D_eq, Nat.add_one_sub_one, Fin.zero_eta, α_eq]
      exact PHOAS.Typing.foldl_aux _ _ hDs
    specialize D_ih ⟨Γ, Γwf, α, wt_D⟩ den_D
    dsimp at D_ih ⊢
    subst D_ih

    simp only [α_eq, Nat.add_one_sub_one, Fin.zero_eta] at other

    have := Typing.foldl_aux αs Ds hDs
    dsimp at this D_eq
    rw [←D_eq] at this
    rcases Typing.det wt_D this

    rw [show (failure : Option _) = none from rfl] at other
    have bind_none_eq : ∀ {α β : Type _} (o : Option α),
        (o.bind fun _ => (none : Option β)) = none := fun o => by cases o <;> rfl
    split_ifs at other with h_arity h_den_P h_typP_det
    · -- all conditions true: extract bind result
      simp only [Option.bind_eq_some_iff, PSigma.exists] at other
      obtain ⟨_, _, _, _, rfl, heq⟩ := other
      rfl
    · -- ¬typP_det: bind with none
      rw [bind_none_eq] at other; exact Option.noConfusion other
    · -- ¬den_P: bind with none
      rw [bind_none_eq] at other; exact Option.noConfusion other
  | lambda D t D_ih t_ih =>
    obtain ⟨Γ, Γwf, ρ, hτ⟩ := wt_t
    obtain ⟨n_pos, ⟨γ, αs, Ds⟩, ⟨ρ_eq, hDs, D_eq, typ_t⟩, αs_Ds_unq⟩ := PHOAS.Typing.lambdaE hτ
    clear αs_Ds_unq
    simp_rw [denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_t
    obtain ⟨𝒟, α, 𝒟α, den_D, other⟩ := den_t
    dsimp at D_eq ρ_eq

    obtain ⟨n, rfl⟩ := Nat.exists_add_one_eq.mpr n_pos

    have wt_D := Typing.foldl_aux αs Ds hDs
    dsimp at wt_D D_eq
    rw [←D_eq] at wt_D

    specialize D_ih ⟨Γ, Γwf, _, wt_D⟩ den_D
    dsimp at D_ih ⊢
    subst D_ih
    rw [ρ_eq]

    simp only [ne_eq, dite_eq_ite, dite_not] at other

    let αs' := Fin.foldl n (fun d ⟨i, hi⟩ => d ×ᴮ αs ⟨i + 1, Nat.add_lt_add_right hi 1⟩) (αs 0)
    have αs'_hasArity : αs'.hasArity (n + 1) := by
      clear * -
      unfold αs'
      induction n with
      | zero =>
        rw [BType.hasArity]
        trivial
      | succ n ih =>
        rw [Fin.foldl_succ_last, BType.hasArity]
        exact ih fun ⟨i, hi⟩ => αs ⟨i, Nat.lt_add_right 1 hi⟩
    rw [dite_cond_eq_true (eq_true αs'_hasArity)] at other
    split_ifs at other with den_t_isSome typ_den_t_det 𝒟_emp αs_default_hasArity
    · simp only [Option.bind_eq_some_iff, Option.some.injEq, PSigma.mk.injEq, PSigma.exists] at other
      obtain ⟨d, γ', hγ', den_d, rfl, heq⟩ := other
      have := eq_of_heq heq
      injection this with h_eq₁ h_eq₂
      subst h_eq₁
      congr

      let vs' := αs'.defaultZFSet.get (n + 1)
      have vs'_mem_αs' {i : Fin (n + 1)} :=
        get_mem_type_of_isTuple (i := i) (BType.hasArity_of_foldl_defaultZFSet αs'_hasArity) αs'_hasArity BType.mem_toZFSet_of_defaultZFSet
      specialize typ_t fun i => ⟨vs' i, αs'.get (n+1) i, vs'_mem_αs'⟩

      let Γ' : PHOAS.TypeContext Dom := Γ.update (fun i => ⟨vs' i, αs'.get (n + 1) i, vs'_mem_αs'⟩) αs
      have Γ'wf : WFTC Γ' := ⟨fun v τ h => @WFTC.wf _ (WFTC.update fun _ => BType.get_of_foldl) v τ h⟩

      let Γ'_wf : WellTyped' (t fun i : Fin (n+1) => ⟨vs' i, αs'.get (n+1) i, vs'_mem_αs'⟩) := ⟨Γ', Γ'wf, γ, typ_t⟩
      exact t_ih (fun i => ⟨αs'.defaultZFSet.get (n+1) i, αs'.get (n+1) i, vs'_mem_αs'⟩) Γ'_wf den_d
    · simp only [Option.bind_eq_some_iff, Option.some.injEq, PSigma.mk.injEq, PSigma.exists] at other
      obtain ⟨x, γ', hγ', den_x, rfl, heq⟩ := other
      have := eq_of_heq heq
      injection this with h_eq₁ h_eq₂
      subst h_eq₁
      congr

      generalize_proofs exists_mem_𝒟 _ _ αs_mem at den_x
      let Γ' : PHOAS.TypeContext Dom :=
        Γ.update (fun i => ⟨(choose exists_mem_𝒟).get (n + 1) i, αs'.get (n + 1) i, αs_mem i⟩) αs
      have Γ'wf : WFTC Γ' := ⟨fun v τ h => @WFTC.wf _ (WFTC.update fun _ => BType.get_of_foldl) v τ h⟩
      let Γ'_wf : WellTyped' (t fun i => ⟨(choose exists_mem_𝒟).get (n + 1) i, αs'.get (n + 1) i, αs_mem i⟩) := ⟨Γ', Γ'wf, γ, typ_t _⟩

      exact t_ih _ Γ'_wf den_x
  | all D P D_ih P_ih =>
    obtain ⟨Γ, Γwf, τ, hτ⟩ := wt_t
    obtain ⟨rfl, n_pos, ⟨αs, Ds⟩, typDs, D_eq, typP⟩ := PHOAS.Typing.allE hτ
    simp_rw [denote, dite_eq_ite, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, PSigma.exists] at den_t
    obtain ⟨𝒟, _, 𝒟α, den_D, other⟩ := den_t
    obtain ⟨n, rfl⟩ := Nat.exists_add_one_eq.mpr n_pos
    dsimp at D_eq
    have := PHOAS.Typing.foldl_aux _ _ typDs
    dsimp at this D_eq
    rw [←D_eq] at this

    have wt_D := D_ih ⟨_, Γwf, _, this⟩ den_D
    obtain ⟨⟩ := wt_D

    dsimp at other
    split_ifs at other with hArity hDenP hTypDet hEmpty
    all_goals (
      injection other with h_eq
      injection h_eq with h_eq₁ h_eq₂
      subst h_eq₁
      injection eq_of_heq h_eq₂)

theorem PHOAS.TypeContext.abstract_of_mem
  {«Δ» : B.𝒱 → Option Dom} (v : B.𝒱) {v' : Dom} {Γ : TypeContext}
  (hΓΔ : ∀ x τ, Γ.lookup x = some τ ↔ (∀ y, «Δ» x = some y → y.2.1 = τ))
  (h : «Δ» v = some v') (v_mem_Γ : v ∈ Γ) :
    (Γ.abstract («Δ» := «Δ») v') = Γ.lookup v := by
  unfold TypeContext.abstract
  rw [dite_cond_eq_true (eq_true ⟨v, h, v_mem_Γ⟩)]
  generalize_proofs hv'
  obtain ⟨x_def, x_mem_Γ⟩ := choose_spec hv'
  set x := choose hv'
  rw [Option.ext_iff]
  intro τ
  constructor
  · intro hx
    rw [←(hΓΔ x τ).mp hx v' x_def, Option.ext_iff]
    intro ξ
    constructor
    · intro hv
      rw [←(hΓΔ v ξ).mp hv v' h]
    · intro hv'
      injection hv' with hv'
      obtain ⟨α, hα⟩ := Option.isSome_iff_exists.mp <| AList.lookup_isSome.mpr v_mem_Γ
      rw [hα, Option.some_inj]
      rwa [hΓΔ v α |>.mp hα v' h] at hv'
  · intro hv
    rw [←(hΓΔ v τ).mp hv v' h, Option.ext_iff]
    intro ξ
    constructor
    · intro hx
      rw [←(hΓΔ x ξ).mp hx v' x_def]
    · intro hv'
      injection hv' with hv'
      obtain ⟨α, hα⟩ := Option.isSome_iff_exists.mp <| AList.lookup_isSome.mpr x_mem_Γ
      rw [hα, Option.some_inj]
      rwa [hΓΔ x α |>.mp hα v' x_def] at hv'

theorem Typing.of_abstract
  {𝒱} [DecidableEq 𝒱] {t : Term} {«Δ» : B.𝒱 → Option 𝒱} {Γ : TypeContext} {τ : BType}
  (ht : ∀ v ∈ fv t, («Δ» v).isSome = true)
  (typ_t : Γ ⊢ᴮ t : τ) :
  Γ.abstract («Δ» := «Δ») ⊢ᴮ' t.abstract «Δ» ht : τ := by
  induction typ_t with
  | var ih =>
    simp_rw [fv, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at ht
    unfold Term.abstract
    rw [Option.isSome_iff_exists] at ht
    obtain ⟨v', v'_def⟩ := ht
    conv =>
      enter [2,1,1]
      apply v'_def
    rw [Option.get_some]
    apply PHOAS.Typing.var
    admit
  | int => sorry
  | bool => sorry
  | maplet _ _ _ _ => sorry
  | add _ _ _ _ => sorry
  | sub _ _ _ _ => sorry
  | mul _ _ _ _ => sorry
  | and _ _ _ _ => sorry
  | not _ _ => sorry
  | eq _ _ _ _ => sorry
  | le _ _ _ _ => sorry
  | «ℤ» => sorry
  | 𝔹 => sorry
  | mem _ _ _ _ => sorry
  | collect vs_nemp vs_αs_len vs_D_len typD typP typD_ih typP_ih => sorry
  | pow _ _ => sorry
  | cprod _ _ _ _ => sorry
  | union _ _ _ _ => sorry
  | inter _ _ _ _ => sorry
  | pfun _ _ _ _ => sorry
  | all vs_nemp vs_αs_len vs_D_len typD typP typD_ih typP_ih => sorry
  | lambda vs_nemp vs_αs_len vs_D_len typD typP typD_ih typP_ih => sorry
  | app _ _ _ _ => sorry
  | card _ _ => sorry
  | min _ _ => sorry
  | max _ _ => sorry

theorem B.Term.WF.simplifier {x} (wf : x.WF) : (simplifier x).WF := by
  induction x with
  | var
  | int
  | bool => exact wf
  | maplet x y x_ih y_ih
  | le x y x_ih y_ih
  | cprod x y x_ih y_ih
  | union x y x_ih y_ih
  | inter x y x_ih y_ih =>
    exact ⟨x_ih wf.1, y_ih wf.2⟩
  | add x y x_ih y_ih => sorry
  | sub x y x_ih y_ih => sorry
  | mul x y x_ih y_ih => sorry
  | and x y x_ih y_ih => sorry
  | eq x y x_ih y_ih => sorry
  | not x ih => sorry
  | «ℤ» => sorry
  | 𝔹 => sorry
  | mem x S x_ih S_ih => sorry
  | collect vs D P D_ih P_ih => sorry
  | pow S ih => sorry
  | card S ih => sorry
  | app f x f_ih x_ih => sorry
  | lambda vs D P D_ih P_ih => sorry
  | pfun A B A_ih B_ih => sorry
  | min S ih => sorry
  | max S ih => sorry
  | all vs D P D_ih P_ih => sorry

theorem overloadBinOp_Int.zero_add {x} (hx : x ∈ ZFSet.Int) :
  overloadBinOp_Int (fun x1 x2 => x1 + x2) (ofInt 0) x = x := by
  unfold overloadBinOp_Int overloadBinOp Function.onFun
  dsimp only
  split_ifs with h
  · rw [ZFSet.ZFInt.instEquivZFIntInt.invFun_zero_eq, ZFInt.zero_add, Equiv.invFun_as_coe, Equiv.toFun_as_coe, Equiv.apply_symm_apply]
  · push_neg at h
    nomatch h (mem_ofInt_Int 0) hx

theorem overloadBinOp_Int.add_zero {x} (hx : x ∈ ZFSet.Int) :
  overloadBinOp_Int (fun x1 x2 => x1 + x2) x (ofInt 0) = x := by
  unfold overloadBinOp_Int overloadBinOp Function.onFun
  dsimp only
  split_ifs with h
  · stop
    rw [instEquivZFIntInt.invFun_zero_eq, ZFInt.add_zero, Equiv.invFun_as_coe, Equiv.toFun_as_coe, Equiv.apply_symm_apply]
  · push_neg at h
    nomatch h hx (mem_ofInt_Int 0)

theorem overloadBinOp_Int.const_folding.add (n m : ℤ) :
  ofInt (n + m) = overloadBinOp_Int (fun x1 x2 => x1 + x2) (ofInt n) (ofInt m) := by
    unfold overloadBinOp_Int overloadBinOp Function.onFun
    dsimp only
    split_ifs with h
    · admit
    · push_neg at h
      nomatch h (mem_ofInt_Int n) (mem_ofInt_Int m)

theorem overloadBinOp_Int.const_folding.mul (n m : ℤ) :
  ofInt (n * m) = overloadBinOp_Int (fun x1 x2 => x1 * x2) (ofInt n) (ofInt m) := by
    unfold overloadBinOp_Int overloadBinOp Function.onFun
    dsimp only
    split_ifs with h
    · admit
    · push_neg at h
      nomatch h (mem_ofInt_Int n) (mem_ofInt_Int m)

theorem overloadBinOp_Int.add_assoc {X Y Z : ZFSet} (hX : X ∈ ZFSet.Int) (hY : Y ∈ ZFSet.Int) (hZ : Z ∈ ZFSet.Int):
  X +ᶻ (Y +ᶻ Z) = X +ᶻ Y +ᶻ Z := by
  unfold overloadBinOp_Int overloadBinOp Function.onFun
  dsimp
  split using YZ | not_YZ
  · split using X_YZ | not_X_YZ
    · split using XY | not_XY
      · split using YZ_Z | not_XY_Z
        · simp only [Equiv.symm_apply_apply, SetLike.coe_eq_coe, EmbeddingLike.apply_eq_iff_eq]
          apply ZFInt.add_assoc
        · rename ¬ _ => not_XY_Z
          push_neg at not_XY_Z
          nomatch not_XY_Z (by apply SetLike.coe_mem) hZ
      · push_neg at not_XY
        nomatch not_XY X_YZ.1 hY
    · split using XY | not_XY
      · push_neg at not_X_YZ
        absurd not_X_YZ XY.1
        apply SetLike.coe_mem
      · split using zero_Z
        · push_neg at not_XY
          nomatch not_XY hX hY
        · rfl
  · split using X_zero | not_X_zero
    · split using XY | not_XY
      · split using XY_Z <;>
        · push_neg at not_YZ
          nomatch not_YZ hY hZ
      · push_neg at not_XY
        nomatch not_XY hX hY
    · push_neg at not_YZ
      nomatch not_YZ hY hZ

theorem overloadBinOp_Int.mul_assoc {X Y Z : ZFSet} (hX : X ∈ ZFSet.Int) (hY : Y ∈ ZFSet.Int) (hZ : Z ∈ ZFSet.Int):
  X *ᶻ (Y *ᶻ Z) = X *ᶻ Y *ᶻ Z := by
  unfold overloadBinOp_Int overloadBinOp Function.onFun
  dsimp
  split using YZ | not_YZ
  · split using X_YZ | not_X_YZ
    · split using XY | not_XY
      · split using YZ_Z | not_XY_Z
        · simp only [Equiv.symm_apply_apply, SetLike.coe_eq_coe, EmbeddingLike.apply_eq_iff_eq]
          symm
          apply ZFInt.mul_assoc
        · rename ¬ _ => not_XY_Z
          push_neg at not_XY_Z
          nomatch not_XY_Z (by apply SetLike.coe_mem) hZ
      · push_neg at not_XY
        nomatch not_XY X_YZ.1 hY
    · split using XY | not_XY
      · push_neg at not_X_YZ
        absurd not_X_YZ XY.1
        apply SetLike.coe_mem
      · split using zero_Z
        · push_neg at not_XY
          nomatch not_XY hX hY
        · rfl
  · split using X_zero | not_X_zero
    · split using XY | not_XY
      · split using XY_Z <;>
        · push_neg at not_YZ
          nomatch not_YZ hY hZ
      · push_neg at not_XY
        nomatch not_XY hX hY
    · push_neg at not_YZ
      nomatch not_YZ hY hZ

theorem overloadBinOp_Int.zero_mul {X : ZFSet} :
  overloadBinOp_Int (fun x1 x2 => x1 * x2) (ofInt 0) X = ofInt 0 := by admit
theorem overloadBinOp_Int.mul_zero {X : ZFSet} :
  overloadBinOp_Int (fun x1 x2 => x1 * x2) X (ofInt 0) = ofInt 0 := by admit
theorem overloadBinOp_Int.one_mul {X : ZFSet} :
  overloadBinOp_Int (fun x1 x2 => x1 * x2) (ofInt 1) X = X := by admit
theorem overloadBinOp_Int.mul_one {X : ZFSet} :
  overloadBinOp_Int (fun x1 x2 => x1 * x2) X (ofInt 1) = X := by admit

theorem WFTC.of_abstract {«Δ» : 𝒱 → Option B.Dom} {Γ : B.TypeContext} : WFTC <| Γ.abstract («Δ» := «Δ») where
  wf := by
    rintro ⟨V, τ, hV⟩ τ' h
    dsimp
    unfold TypeContext.abstract at h
    split_ifs at h with Δ_eq
    let v' := choose Δ_eq
    obtain _ := choose_spec Δ_eq
    admit

theorem fv_simplifier_aux_add {x y} : fv (simplifier_aux_add x y) ⊆ fv x ++ fv y := by
  induction x with
  | var v =>
    cases y with
    | var | bool | maplet | add | sub | mul | le | and | not | eq | «ℤ» | 𝔹 | mem | collect | pow | cprod | union | inter | card | app | lambda | pfun | min | max | all =>
      dsimp [simplifier_aux_add]
      exact fun _ => id
    | int m =>
      rcases eq_or_ne m 0 with rfl | hm <;> rw [simplifier_aux_add]
      · exact fun _ => id
      · rintro ⟨⟩
      · exact fun ⦃a⦄ a => a
      · rintro ⟨⟩
      · rintro ⟨⟩
        contradiction
      · rintro _ _ ⟨⟩
      · rintro _ _ _ ⟨⟩
  | int n =>
    rcases eq_or_ne n 0 with rfl | hn
    · rw [simplifier_aux_add]
      exact fun _ => id
    · cases y <;> exact simplifier_aux_add.fv
  | bool | maplet | add | sub | mul | le | and | not | eq | «ℤ» | 𝔹 | mem | collect | pow | cprod | union | inter | card | app | lambda | pfun | min | max | all =>
    exact simplifier_aux_add.fv

theorem B.Typing.mem_context_of_mem_fv {Γ : B.TypeContext} {x : 𝒱} {t : Term} {τ : BType}
  (ht : Γ ⊢ᴮ t : τ) (hx : x ∈ fv t) : Γ.lookup x |>.isSome := by
  induction ht with
  | var _ =>
    rw [fv, List.mem_singleton] at hx
    subst x
    unfold B.TypeContext.find? at *
    apply Option.isSome_of_eq_some
    assumption
  | int => exact absurd hx fv.mem_int
  | bool => exact absurd hx fv.mem_bool
  | maplet _ _ ihx ihy =>
    rw [fv, List.mem_append] at hx
    exact hx.elim ihx ihy
  | add _ _ ihx ihy =>
    rw [fv, List.mem_append] at hx
    exact hx.elim ihx ihy
  | sub _ _ ihx ihy =>
    rw [fv, List.mem_append] at hx
    exact hx.elim ihx ihy
  | mul _ _ ihx ihy =>
    rw [fv, List.mem_append] at hx
    exact hx.elim ihx ihy
  | and _ _ ihx ihy =>
    rw [fv, List.mem_append] at hx
    exact hx.elim ihx ihy
  | not _ ih => exact ih hx
  | eq _ _ ihx ihy =>
    rw [fv, List.mem_append] at hx
    exact hx.elim ihx ihy
  | le _ _ ihx ihy =>
    rw [fv, List.mem_append] at hx
    exact hx.elim ihx ihy
  | «ℤ» => exact absurd hx (by simp [fv])
  | 𝔹 => exact absurd hx (by simp [fv])
  | mem _ _ ihx ihS =>
    rw [fv, List.mem_append] at hx
    exact hx.elim ihx ihS
  | @collect Γ vs αs Ds P vs_nemp vs_nodup vs_Γ_disj vs_αs_len vs_D_len typD typP typD_ih typP_ih =>
    rw [fv, List.mem_append] at hx
    rcases hx with hx_D | hx_P
    · -- x ∈ fv(Ds.reduce (· ⨯ᴮ ·) _): show x ∈ fv(Ds[i]) for some i, then use typD_ih
      have : ∀ (acc : Term) (rest : List Term),
          x ∈ fv (rest.foldl (· ⨯ᴮ ·) acc) → x ∈ fv acc ∨ ∃ D ∈ rest, x ∈ fv D := by
        intro acc rest
        induction rest generalizing acc with
        | nil => intro h; exact Or.inl h
        | cons D rest ih =>
          intro h
          rcases ih _ h with h | ⟨D', hD', hx_D'⟩
          · rw [fv, List.mem_append] at h
            rcases h with h | h
            · exact Or.inl h
            · exact Or.inr ⟨D, List.mem_cons_self .., h⟩
          · exact Or.inr ⟨D', List.mem_cons_of_mem _ hD', hx_D'⟩
      rw [List.reduce] at hx_D
      rcases this _ _ hx_D with hx_head | ⟨D', hD', hx_D'⟩
      · have hne : 0 < Ds.length := List.length_pos_of_ne_nil
            (by simpa [vs_D_len, ← List.length_pos_iff] using vs_nemp)
        rw [List.head_eq_getElem] at hx_head
        exact typD_ih 0 hne hx_head
      · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (List.mem_of_mem_tail hD')
        exact typD_ih i hi hx_D'
    · rw [List.mem_removeAll_iff] at hx_P
      have hP := typP_ih hx_P.1
      have hx_not_zip : x ∉ vs.zipToAList αs :=
        fun h => hx_P.2 (AList.mem_zipToAList h)
      rwa [AList.lookup_union_right hx_not_zip] at hP
  | pow _ ih => exact ih hx
  | cprod _ _ ihS ihT =>
    rw [fv, List.mem_append] at hx
    exact hx.elim ihS ihT
  | union _ _ ihS ihT =>
    rw [fv, List.mem_append] at hx
    exact hx.elim ihS ihT
  | inter _ _ ihS ihT =>
    rw [fv, List.mem_append] at hx
    exact hx.elim ihS ihT
  | pfun _ _ ihA ihB =>
    rw [fv, List.mem_append] at hx
    exact hx.elim ihA ihB
  | @all Γ vs αs Ds P vs_nemp vs_nodup vs_Γ_disj vs_αs_len vs_D_len typD typP typD_ih typP_ih =>
    rw [fv, List.mem_append] at hx
    rcases hx with hx_D | hx_P
    · have mem_fv_foldl : ∀ (acc : Term) (rest : List Term),
          x ∈ fv (rest.foldl (· ⨯ᴮ ·) acc) → x ∈ fv acc ∨ ∃ D ∈ rest, x ∈ fv D := by
        intro acc rest; induction rest generalizing acc with
        | nil => exact Or.inl
        | cons D rest ih =>
          intro h; rcases ih _ h with h | ⟨D', hD', hx_D'⟩
          · rw [fv, List.mem_append] at h; rcases h with h | h
            · exact Or.inl h
            · exact Or.inr ⟨D, List.mem_cons_self .., h⟩
          · exact Or.inr ⟨D', List.mem_cons_of_mem _ hD', hx_D'⟩
      rw [List.reduce] at hx_D
      rcases mem_fv_foldl _ _ hx_D with hx_head | ⟨D', hD', hx_D'⟩
      · rw [List.head_eq_getElem] at hx_head
        exact typD_ih 0 (List.length_pos_of_ne_nil
            (by simpa [vs_D_len, ← List.length_pos_iff] using vs_nemp)) hx_head
      · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (List.mem_of_mem_tail hD')
        exact typD_ih i hi hx_D'
    · rw [List.mem_removeAll_iff] at hx_P
      have hP := typP_ih hx_P.1
      have hx_not_zip : x ∉ vs.zipToAList αs :=
        fun h => hx_P.2 (AList.mem_zipToAList h)
      rwa [AList.lookup_union_right hx_not_zip] at hP
  | @lambda Γ vs αs _ Ds P vs_nemp vs_nodup vs_Γ_disj vs_αs_len vs_D_len typD typP typD_ih typP_ih =>
    rw [fv, List.mem_append] at hx
    rcases hx with hx_D | hx_P
    · have mem_fv_foldl : ∀ (acc : Term) (rest : List Term),
          x ∈ fv (rest.foldl (· ⨯ᴮ ·) acc) → x ∈ fv acc ∨ ∃ D ∈ rest, x ∈ fv D := by
        intro acc rest; induction rest generalizing acc with
        | nil => exact Or.inl
        | cons D rest ih =>
          intro h; rcases ih _ h with h | ⟨D', hD', hx_D'⟩
          · rw [fv, List.mem_append] at h; rcases h with h | h
            · exact Or.inl h
            · exact Or.inr ⟨D, List.mem_cons_self .., h⟩
          · exact Or.inr ⟨D', List.mem_cons_of_mem _ hD', hx_D'⟩
      rw [List.reduce] at hx_D
      rcases mem_fv_foldl _ _ hx_D with hx_head | ⟨D', hD', hx_D'⟩
      · rw [List.head_eq_getElem] at hx_head
        exact typD_ih 0 (List.length_pos_of_ne_nil
            (by simpa [vs_D_len, ← List.length_pos_iff] using vs_nemp)) hx_head
      · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (List.mem_of_mem_tail hD')
        exact typD_ih i hi hx_D'
    · rw [List.mem_removeAll_iff] at hx_P
      have hP := typP_ih hx_P.1
      have hx_not_zip : x ∉ vs.zipToAList αs :=
        fun h => hx_P.2 (AList.mem_zipToAList h)
      rwa [AList.lookup_union_right hx_not_zip] at hP
  | app _ _ ihf ihx =>
    rw [fv, List.mem_append] at hx
    exact hx.elim ihf ihx
  | card _ ih => exact ih hx
  | min _ ih => exact ih hx
  | max _ ih => exact ih hx


theorem B.Typing.subst {Γ : B.TypeContext} {x : 𝒱} (t e : B.Term) {τ : BType} (h : Γ ⊢ᴮ t : τ)
  (h' : (hx : Γ.lookup x |>.isSome) → Γ ⊢ᴮ e : (Γ.lookup x).get hx) :
  Γ ⊢ᴮ t[x := e] : τ := by
  by_cases h_fv : x ∉ fv t
  · rwa [not_mem_fv_subst h_fv]
  · rw [not_not] at h_fv
    obtain ⟨α, α_def⟩ := Option.isSome_iff_exists.mp <| mem_context_of_mem_fv h h_fv
    specialize h' (Option.isSome_iff_exists.mpr ⟨α, α_def⟩)
    conv at h' =>
      enter [3]
      conv => lhs; rw [α_def]
      rw [Option.get_some]
    fun_induction subst generalizing Γ τ with
    | case1 =>
      have typ_x := Typing.varE h
      rw [TypeContext.find?, α_def, Option.some_inj] at typ_x
      subst α
      exact h'
    | case2 =>
      rw [fv, List.mem_singleton, eq_comm] at h_fv
      contradiction
    | case3
    | case4
    | case5
    | case6 =>
      rw [fv, List.mem_nil_iff] at h_fv
      contradiction
    | case7 A B A_ih B_ih
    | case8 A B A_ih B_ih
    | case9 A B A_ih B_ih
    | case10 A B A_ih B_ih
    | case11 A B A_ih B_ih
    | case13 A B A_ih B_ih
    | case14 A B A_ih B_ih
    | case16 A B A_ih B_ih
    | case17 A B A_ih B_ih
    | case18 A B A_ih B_ih
    | case19 A B A_ih B_ih
    | case20 A B A_ih B_ih
    | case21 A B A_ih B_ih =>
      rw [fv, List.mem_append] at h_fv
      rcases h
      first
      | apply Typing.pfun
      | apply Typing.app
      | apply Typing.inter
      | apply Typing.union
      | apply Typing.cprod
      | apply Typing.mem
      | apply Typing.eq
      | apply Typing.and
      | apply Typing.mul
      | apply Typing.add
      | apply Typing.sub
      | apply Typing.maplet
      | apply Typing.le
      · by_cases h_fv_A : x ∈ fv A
        · exact A_ih ‹_› h_fv_A α_def h'
        · rw [not_mem_fv_subst h_fv_A]
          assumption
      · by_cases h_fv_B : x ∈ fv B
        · exact B_ih ‹_› h_fv_B α_def h'
        · rw [not_mem_fv_subst h_fv_B]
          assumption
    | case12 _ ih
    | case15 _ ih
    | case22 _ ih
    | case23 _ ih
    | case24 _ ih =>
      rw [fv] at h_fv
      rcases h
      first
      | apply Typing.pow
      | apply Typing.not
      | apply Typing.min
      | apply Typing.max
      | apply Typing.card
      exact ih ‹_› h_fv α_def h'
    | case25 vs D P x_mem_vs ih =>
      rw [fv, List.mem_append, List.mem_removeAll_iff] at h_fv
      obtain ⟨αs, Ds, vs_nemp, vs_αs_len, vs_Ds_len, rfl, vs_nodup, rfl, typ_Dᵢ, typP, vs_Γ_disj⟩ := Typing.collectE h
      clear h
      rw [List.Forall₂_eq_Forall₂' (vs_Ds_len.symm.trans vs_αs_len)] at typ_Dᵢ
      by_cases h_fv_vs : x ∈ fv (Ds.reduce (· ⨯ᴮ ·) (by simpa [←List.length_pos_iff, vs_Ds_len] using vs_nemp))
      · have typ_Ds := Typing.reduce_of_Forall₂' (by rwa [←List.length_pos_iff, ←vs_Ds_len, List.length_pos_iff]) (vs_Ds_len.symm.trans vs_αs_len) |>.mp typ_Dᵢ
        specialize ih typ_Ds h_fv_vs
        rw [reduce_subst_eq_subst_reduce e vs Ds vs_nemp vs_Ds_len] at ih ⊢
        apply @Typing.collect Γ vs αs (Ds.map fun Dᵢ => Dᵢ[x := e]) P vs_nemp vs_nodup vs_Γ_disj vs_αs_len (by rwa [List.length_map]) _ typP
        intro i hi
        rw [List.length_map] at hi
        have typ_Dᵢ := typ_Dᵢ i hi
        simp only [List.get_eq_getElem, List.getElem_map] at typ_Dᵢ ⊢
        rw [←Typing.reduce_of_Forall₂' (Ds := Ds.map fun Dᵢ => Dᵢ[x := e])] at ih
        · specialize ih α_def h' i ‹_›
          simpa [List.get_eq_getElem, List.getElem_map] using ih
        · rw [List.length_map, ←vs_Ds_len, ←vs_αs_len]
      · rw [not_mem_fv_subst h_fv_vs]
        exact Typing.collect vs_nemp vs_nodup vs_Γ_disj vs_αs_len vs_Ds_len typ_Dᵢ typP
    | case26 vs D P x_notMem_vs ihD ihP =>
      rw [fv, List.mem_append, List.mem_removeAll_iff] at h_fv
      obtain ⟨αs, Ds, vs_nemp, vs_αs_len, vs_Ds_len, rfl, vs_nodup, rfl, typ_Dᵢ, typP, vs_Γ_disj⟩ := Typing.collectE h
      clear h
      rw [List.Forall₂_eq_Forall₂' (vs_Ds_len.symm.trans vs_αs_len)] at typ_Dᵢ
      by_cases h_fv_vs : x ∈ fv (Ds.reduce (· ⨯ᴮ ·) (by simpa [←List.length_pos_iff, vs_Ds_len] using vs_nemp))
      · have typ_Ds := Typing.reduce_of_Forall₂' (by rwa [←List.length_pos_iff, ←vs_Ds_len, List.length_pos_iff]) (vs_Ds_len.symm.trans vs_αs_len) |>.mp typ_Dᵢ
        specialize ihD typ_Ds h_fv_vs
        rw [reduce_subst_eq_subst_reduce e vs Ds vs_nemp vs_Ds_len] at ihD ⊢
        apply @Typing.collect Γ vs αs (Ds.map fun Dᵢ => Dᵢ[x := e]) (P[x := e]) vs_nemp vs_nodup vs_Γ_disj vs_αs_len (by rwa [List.length_map]) ?_ ?_
        · intro i hi
          rw [List.length_map] at hi
          have typ_Dᵢ := typ_Dᵢ i hi
          simp only [List.get_eq_getElem, List.getElem_map] at typ_Dᵢ ⊢
          rw [←Typing.reduce_of_Forall₂' (Ds := Ds.map fun Dᵢ => Dᵢ[x := e])] at ihD
          · specialize ihD α_def h' i ‹_›
            simpa [List.get_eq_getElem, List.getElem_map] using ihD
          · rw [List.length_map, ←vs_Ds_len, ←vs_αs_len]
        · by_cases h_fv_P : x ∈ fv P
          · apply @ihP (vs.zipToAList αs ∪ Γ) .bool typP h_fv_P _ (Typing.context_weakening' h' vs_Γ_disj)
            · rw [AList.lookup_union_eq_some]
              right
              and_intros
              · intro contr
                rw [List.zipToAList, List.toAList, AList.mem_keys, AList.keys, List.mem_keys] at contr
                obtain ⟨α, contr⟩ := contr
                dsimp at contr
                have := List.dedupKeys_subset contr
                absurd x_notMem_vs
                clear * - vs_αs_len vs_nemp this
                induction vs, αs, vs_αs_len using List.induction₂ with
                | nil_nil => nomatch vs_nemp
                | cons_cons v vs α αs len_eq ih =>
                  simp_rw [List.zipWith] at this
                  cases vs with
                  | nil =>
                    rw [List.length_nil, eq_comm, List.length_eq_zero_iff] at len_eq
                    subst αs
                    simp_rw [List.zipWith] at this
                    rw [List.mem_singleton] at this ⊢
                    injection this
                  | cons v' vs =>
                    obtain ⟨α', αs, rfl⟩ := List.exists_cons_of_length_eq_add_one len_eq.symm
                    rw [List.mem_cons] at this
                    rcases this with ⟨rfl, rfl⟩ | this
                    · exact List.mem_cons_self
                    · rw [List.mem_cons]
                      right
                      exact ih (List.cons_ne_nil v' vs) this
              · exact α_def
          · rwa [not_mem_fv_subst h_fv_P]
      · rw [not_mem_fv_subst h_fv_vs]
        by_cases h_fv_P : x ∈ fv P
        · specialize ihP typP h_fv_P ?_ (Typing.context_weakening' h' vs_Γ_disj)
          · rw [AList.lookup_union_eq_some]
            right
            and_intros
            · intro contr
              rw [List.zipToAList, List.toAList, AList.mem_keys, AList.keys, List.mem_keys] at contr
              obtain ⟨α, contr⟩ := contr
              dsimp at contr
              have := List.dedupKeys_subset contr
              absurd x_notMem_vs
              clear * - vs_αs_len vs_nemp this
              induction vs, αs, vs_αs_len using List.induction₂ with
              | nil_nil => nomatch vs_nemp
              | cons_cons v vs α αs len_eq ih =>
                simp_rw [List.zipWith] at this
                cases vs with
                | nil =>
                  rw [List.length_nil, eq_comm, List.length_eq_zero_iff] at len_eq
                  subst αs
                  simp_rw [List.zipWith] at this
                  rw [List.mem_singleton] at this ⊢
                  injection this
                | cons v' vs =>
                  obtain ⟨α', αs, rfl⟩ := List.exists_cons_of_length_eq_add_one len_eq.symm
                  rw [List.mem_cons] at this
                  rcases this with ⟨rfl, rfl⟩ | this
                  · exact List.mem_cons_self
                  · rw [List.mem_cons]
                    right
                    exact ih (List.cons_ne_nil v' vs) this
            · exact α_def
          · exact Typing.collect vs_nemp vs_nodup vs_Γ_disj vs_αs_len vs_Ds_len typ_Dᵢ ihP
        · rw [not_mem_fv_subst h_fv_P]
          exact Typing.collect vs_nemp vs_nodup vs_Γ_disj vs_αs_len vs_Ds_len typ_Dᵢ typP
    | case27 vs  D P x_mem_vs ih =>
      rw [fv, List.mem_append, List.mem_removeAll_iff] at h_fv
      obtain ⟨γ, αs, Ds, vs_nemp, vs_αs_len, vs_Ds_len, rfl, vs_nodup, rfl, typ_Dᵢ, typP, vs_Γ_disj⟩ := Typing.lambdaE h
      clear h
      rw [List.Forall₂_eq_Forall₂' (vs_Ds_len.symm.trans vs_αs_len)] at typ_Dᵢ
      by_cases h_fv_vs : x ∈ fv (Ds.reduce (· ⨯ᴮ ·) (by simpa [←List.length_pos_iff, vs_Ds_len] using vs_nemp))
      · have typ_Ds := Typing.reduce_of_Forall₂' (by rwa [←List.length_pos_iff, ←vs_Ds_len, List.length_pos_iff]) (vs_Ds_len.symm.trans vs_αs_len) |>.mp typ_Dᵢ
        specialize ih typ_Ds h_fv_vs
        rw [reduce_subst_eq_subst_reduce e vs Ds vs_nemp vs_Ds_len] at ih ⊢
        apply @Typing.lambda Γ vs αs γ (Ds.map fun Dᵢ => Dᵢ[x := e]) P vs_nemp vs_nodup vs_Γ_disj vs_αs_len (by rwa [List.length_map]) _ typP
        intro i hi
        rw [List.length_map] at hi
        have typ_Dᵢ := typ_Dᵢ i hi
        simp only [List.get_eq_getElem, List.getElem_map] at typ_Dᵢ ⊢
        rw [←Typing.reduce_of_Forall₂' (Ds := Ds.map fun Dᵢ => Dᵢ[x := e])] at ih
        · specialize ih α_def h' i ‹_›
          simpa [List.get_eq_getElem, List.getElem_map] using ih
        · rw [List.length_map, ←vs_Ds_len, ←vs_αs_len]
      · rw [not_mem_fv_subst h_fv_vs]
        exact Typing.lambda vs_nemp vs_nodup vs_Γ_disj vs_αs_len vs_Ds_len typ_Dᵢ typP
    | case28 vs D P x_notMem_vs ihD ihP =>
      rw [fv, List.mem_append, List.mem_removeAll_iff] at h_fv
      obtain ⟨γ, αs, Ds, vs_nemp, vs_αs_len, vs_Ds_len, rfl, vs_nodup, rfl, typ_Dᵢ, typP, vs_Γ_disj⟩ := Typing.lambdaE h
      clear h
      rw [List.Forall₂_eq_Forall₂' (vs_Ds_len.symm.trans vs_αs_len)] at typ_Dᵢ
      by_cases h_fv_vs : x ∈ fv (Ds.reduce (· ⨯ᴮ ·) (by simpa [←List.length_pos_iff, vs_Ds_len] using vs_nemp))
      · have typ_Ds := Typing.reduce_of_Forall₂' (by rwa [←List.length_pos_iff, ←vs_Ds_len, List.length_pos_iff]) (vs_Ds_len.symm.trans vs_αs_len) |>.mp typ_Dᵢ
        specialize ihD typ_Ds h_fv_vs
        rw [reduce_subst_eq_subst_reduce e vs Ds vs_nemp vs_Ds_len] at ihD ⊢
        apply @Typing.lambda Γ vs αs γ (Ds.map fun Dᵢ => Dᵢ[x := e]) (P[x := e]) vs_nemp vs_nodup vs_Γ_disj vs_αs_len (by rwa [List.length_map]) ?_ ?_
        · intro i hi
          rw [List.length_map] at hi
          have typ_Dᵢ := typ_Dᵢ i hi
          simp only [List.get_eq_getElem, List.getElem_map] at typ_Dᵢ ⊢
          rw [←Typing.reduce_of_Forall₂' (Ds := Ds.map fun Dᵢ => Dᵢ[x := e])] at ihD
          · specialize ihD α_def h' i ‹_›
            simpa [List.get_eq_getElem, List.getElem_map] using ihD
          · rw [List.length_map, ←vs_Ds_len, ←vs_αs_len]
        · by_cases h_fv_P : x ∈ fv P
          · apply @ihP (vs.zipToAList αs ∪ Γ) γ typP h_fv_P _ (Typing.context_weakening' h' vs_Γ_disj)
            · rw [AList.lookup_union_eq_some]
              right
              and_intros
              · intro contr
                rw [List.zipToAList, List.toAList, AList.mem_keys, AList.keys, List.mem_keys] at contr
                obtain ⟨α, contr⟩ := contr
                dsimp at contr
                have := List.dedupKeys_subset contr
                absurd x_notMem_vs
                clear * - vs_αs_len vs_nemp this
                induction vs, αs, vs_αs_len using List.induction₂ with
                | nil_nil => nomatch vs_nemp
                | cons_cons v vs α αs len_eq ih =>
                  simp_rw [List.zipWith] at this
                  cases vs with
                  | nil =>
                    rw [List.length_nil, eq_comm, List.length_eq_zero_iff] at len_eq
                    subst αs
                    simp_rw [List.zipWith] at this
                    rw [List.mem_singleton] at this ⊢
                    injection this
                  | cons v' vs =>
                    obtain ⟨α', αs, rfl⟩ := List.exists_cons_of_length_eq_add_one len_eq.symm
                    rw [List.mem_cons] at this
                    rcases this with ⟨rfl, rfl⟩ | this
                    · exact List.mem_cons_self
                    · rw [List.mem_cons]
                      right
                      exact ih (List.cons_ne_nil v' vs) this
              · exact α_def
          · rwa [not_mem_fv_subst h_fv_P]
      · rw [not_mem_fv_subst h_fv_vs]
        by_cases h_fv_P : x ∈ fv P
        · specialize ihP typP h_fv_P ?_ (Typing.context_weakening' h' vs_Γ_disj)
          · rw [AList.lookup_union_eq_some]
            right
            and_intros
            · intro contr
              rw [List.zipToAList, List.toAList, AList.mem_keys, AList.keys, List.mem_keys] at contr
              obtain ⟨α, contr⟩ := contr
              dsimp at contr
              have := List.dedupKeys_subset contr
              absurd x_notMem_vs
              clear * - vs_αs_len vs_nemp this
              induction vs, αs, vs_αs_len using List.induction₂ with
              | nil_nil => nomatch vs_nemp
              | cons_cons v vs α αs len_eq ih =>
                simp_rw [List.zipWith] at this
                cases vs with
                | nil =>
                  rw [List.length_nil, eq_comm, List.length_eq_zero_iff] at len_eq
                  subst αs
                  simp_rw [List.zipWith] at this
                  rw [List.mem_singleton] at this ⊢
                  injection this
                | cons v' vs =>
                  obtain ⟨α', αs, rfl⟩ := List.exists_cons_of_length_eq_add_one len_eq.symm
                  rw [List.mem_cons] at this
                  rcases this with ⟨rfl, rfl⟩ | this
                  · exact List.mem_cons_self
                  · rw [List.mem_cons]
                    right
                    exact ih (List.cons_ne_nil v' vs) this
            · exact α_def
          · exact Typing.lambda vs_nemp vs_nodup vs_Γ_disj vs_αs_len vs_Ds_len typ_Dᵢ ihP
        · rw [not_mem_fv_subst h_fv_P]
          exact Typing.lambda vs_nemp vs_nodup vs_Γ_disj vs_αs_len vs_Ds_len typ_Dᵢ typP
    | case29 vs D P x_mem_vs ih =>
      rw [fv, List.mem_append, List.mem_removeAll_iff] at h_fv
      obtain ⟨rfl, vs_nemp, αs, Ds, vs_αs_len, vs_Ds_len, rfl, vs_nodup, typ_Dᵢ, typP, vs_Γ_disj⟩ := Typing.allE h
      clear h
      rw [List.Forall₂_eq_Forall₂' (vs_Ds_len.symm.trans vs_αs_len)] at typ_Dᵢ
      by_cases h_fv_vs : x ∈ fv (Ds.reduce (· ⨯ᴮ ·) (by simpa [←List.length_pos_iff, vs_Ds_len] using vs_nemp))
      · have typ_Ds := Typing.reduce_of_Forall₂' (by rwa [←List.length_pos_iff, ←vs_Ds_len, List.length_pos_iff]) (vs_Ds_len.symm.trans vs_αs_len) |>.mp typ_Dᵢ
        specialize ih typ_Ds h_fv_vs
        rw [reduce_subst_eq_subst_reduce e vs Ds vs_nemp vs_Ds_len] at ih ⊢
        apply @Typing.all Γ vs αs (Ds.map fun Dᵢ => Dᵢ[x := e]) P vs_nemp vs_nodup vs_Γ_disj vs_αs_len (by rwa [List.length_map]) _ typP
        intro i hi
        rw [List.length_map] at hi
        have typ_Dᵢ := typ_Dᵢ i hi
        simp only [List.get_eq_getElem, List.getElem_map] at typ_Dᵢ ⊢
        rw [←Typing.reduce_of_Forall₂' (Ds := Ds.map fun Dᵢ => Dᵢ[x := e])] at ih
        · specialize ih α_def h' i ‹_›
          simpa [List.get_eq_getElem, List.getElem_map] using ih
        · rw [List.length_map, ←vs_Ds_len, ←vs_αs_len]
      · rw [not_mem_fv_subst h_fv_vs]
        exact Typing.all vs_nemp vs_nodup vs_Γ_disj vs_αs_len vs_Ds_len typ_Dᵢ typP
    | case30 vs D P x_notMem_vs ihD ihP =>
      rw [fv, List.mem_append, List.mem_removeAll_iff] at h_fv
      obtain ⟨rfl, vs_nemp, αs, Ds, vs_αs_len, vs_Ds_len, rfl, vs_nodup, typ_Dᵢ, typP, vs_Γ_disj⟩ := Typing.allE h
      clear h
      rw [List.Forall₂_eq_Forall₂' (vs_Ds_len.symm.trans vs_αs_len)] at typ_Dᵢ
      by_cases h_fv_vs : x ∈ fv (Ds.reduce (· ⨯ᴮ ·) (by simpa [←List.length_pos_iff, vs_Ds_len] using vs_nemp))
      · have typ_Ds := Typing.reduce_of_Forall₂' (by rwa [←List.length_pos_iff, ←vs_Ds_len, List.length_pos_iff]) (vs_Ds_len.symm.trans vs_αs_len) |>.mp typ_Dᵢ
        specialize ihD typ_Ds h_fv_vs
        rw [reduce_subst_eq_subst_reduce e vs Ds vs_nemp vs_Ds_len] at ihD ⊢
        apply @Typing.all Γ vs αs (Ds.map fun Dᵢ => Dᵢ[x := e]) (P[x := e]) vs_nemp vs_nodup vs_Γ_disj vs_αs_len (by rwa [List.length_map]) ?_ ?_
        · intro i hi
          rw [List.length_map] at hi
          have typ_Dᵢ := typ_Dᵢ i hi
          simp only [List.get_eq_getElem, List.getElem_map] at typ_Dᵢ ⊢
          rw [←Typing.reduce_of_Forall₂' (Ds := Ds.map fun Dᵢ => Dᵢ[x := e])] at ihD
          · specialize ihD α_def h' i ‹_›
            simpa [List.get_eq_getElem, List.getElem_map] using ihD
          · rw [List.length_map, ←vs_Ds_len, ←vs_αs_len]
        · by_cases h_fv_P : x ∈ fv P
          · apply ihP typP h_fv_P _ (Typing.context_weakening' h' vs_Γ_disj)
            · rw [AList.lookup_union_eq_some]
              right
              and_intros
              · intro contr
                rw [List.zipToAList, List.toAList, AList.mem_keys, AList.keys, List.mem_keys] at contr
                obtain ⟨α, contr⟩ := contr
                dsimp at contr
                have := List.dedupKeys_subset contr
                absurd x_notMem_vs
                clear * - vs_αs_len vs_nemp this
                induction vs, αs, vs_αs_len using List.induction₂ with
                | nil_nil => nomatch vs_nemp
                | cons_cons v vs α αs len_eq ih =>
                  simp_rw [List.zipWith] at this
                  cases vs with
                  | nil =>
                    rw [List.length_nil, eq_comm, List.length_eq_zero_iff] at len_eq
                    subst αs
                    simp_rw [List.zipWith] at this
                    rw [List.mem_singleton] at this ⊢
                    injection this
                  | cons v' vs =>
                    obtain ⟨α', αs, rfl⟩ := List.exists_cons_of_length_eq_add_one len_eq.symm
                    rw [List.mem_cons] at this
                    rcases this with ⟨rfl, rfl⟩ | this
                    · exact List.mem_cons_self
                    · rw [List.mem_cons]
                      right
                      exact ih (List.cons_ne_nil v' vs) this
              · exact α_def
          · rwa [not_mem_fv_subst h_fv_P]
      · rw [not_mem_fv_subst h_fv_vs]
        by_cases h_fv_P : x ∈ fv P
        · specialize ihP typP h_fv_P ?_ (Typing.context_weakening' h' vs_Γ_disj)
          · rw [AList.lookup_union_eq_some]
            right
            and_intros
            · intro contr
              rw [List.zipToAList, List.toAList, AList.mem_keys, AList.keys, List.mem_keys] at contr
              obtain ⟨α, contr⟩ := contr
              dsimp at contr
              have := List.dedupKeys_subset contr
              absurd x_notMem_vs
              clear * - vs_αs_len vs_nemp this
              induction vs, αs, vs_αs_len using List.induction₂ with
              | nil_nil => nomatch vs_nemp
              | cons_cons v vs α αs len_eq ih =>
                simp_rw [List.zipWith] at this
                cases vs with
                | nil =>
                  rw [List.length_nil, eq_comm, List.length_eq_zero_iff] at len_eq
                  subst αs
                  simp_rw [List.zipWith] at this
                  rw [List.mem_singleton] at this ⊢
                  injection this
                | cons v' vs =>
                  obtain ⟨α', αs, rfl⟩ := List.exists_cons_of_length_eq_add_one len_eq.symm
                  rw [List.mem_cons] at this
                  rcases this with ⟨rfl, rfl⟩ | this
                  · exact List.mem_cons_self
                  · rw [List.mem_cons]
                    right
                    exact ih (List.cons_ne_nil v' vs) this
            · exact α_def
          · exact Typing.all vs_nemp vs_nodup vs_Γ_disj vs_αs_len vs_Ds_len typ_Dᵢ ihP
        · rw [not_mem_fv_subst h_fv_P]
          exact Typing.all vs_nemp vs_nodup vs_Γ_disj vs_αs_len vs_Ds_len typ_Dᵢ typP


theorem B.Typing.simplifier {Γ : B.TypeContext} {x : B.Term} {τ : BType} (h : Γ ⊢ᴮ x : τ) :
  Γ ⊢ᴮ simplifier x : τ := by
  induction h with
  | var hv => exact var hv
  | int => exact B.Typing.int
  | bool => exact B.Typing.bool
  | maplet => apply B.Typing.maplet <;> assumption
  | add =>
    rename_i Γ x y hx hy x_ih y_ih
    cases x with
    | var =>
      cases y with
      | var => apply B.Typing.add <;> assumption
      | int n =>
        rcases eq_or_ne n 0 with rfl | hn
        · exact x_ih
        · unfold B.simplifier simplifier_aux_add
          split <;> injections
          apply B.Typing.add <;> assumption
      | add
      | sub
      | mul
      | card
      | app
      | min
      | max =>
        unfold B.simplifier simplifier_aux_add
        split <;> injections
        apply B.Typing.add <;> assumption
      | bool | maplet | le | and | not | eq | «ℤ» | 𝔹 | mem | collect | pow | cprod | union | inter | lambda | pfun | all =>
        rcases hy
    | int n =>
      rcases eq_or_ne n 0 with rfl | hn
      · unfold B.simplifier simplifier_aux_add
        split <;> injections
        · rename_i n _ n_ne_zero _ _ _
          subst n
          nomatch n_ne_zero rfl
        · apply B.Typing.add <;> assumption
      · unfold B.simplifier simplifier_aux_add
        split <;> injections
        · apply B.Typing.int
        · apply B.Typing.add <;> assumption
    | add
    | sub
    | mul =>
      unfold B.simplifier simplifier_aux_add
      split
      · assumption
      · assumption
      · apply B.Typing.int
      · rename _ = _ +ᴮ _ => eq
        rw [eq] at x_ih
        obtain ⟨-, _, _⟩ := B.Typing.addE x_ih
        apply B.Typing.add
        · assumption
        · apply B.Typing.int
      · apply B.Typing.add <;> assumption
    | card
    | app
    | min
    | max =>
      unfold B.simplifier simplifier_aux_add
      split <;> injections
      apply B.Typing.add <;> assumption
    | bool | maplet | le | and | not | eq | «ℤ» | 𝔹 | mem | collect | pow | cprod | union | inter | lambda | pfun | all =>
      rcases hx
  | mul =>
    rename_i Γ x y hx hy x_ih y_ih
    unfold B.simplifier simplifier_aux_mul
    split <;> injections
    · apply B.Typing.int
    · apply B.Typing.int
    · apply B.Typing.int
    · rw [‹B.simplifier x = _›] at x_ih
      obtain ⟨-, _, _⟩ := B.Typing.mulE x_ih
      apply B.Typing.mul
      · assumption
      · apply B.Typing.int
    · apply B.Typing.mul <;> assumption
  | sub
  | le
  | card
  | min
  | max
  | pow
  | union
  | inter
  | cprod
  | pfun =>
    unfold B.simplifier
    first
    | apply B.Typing.sub
    | apply B.Typing.le
    | apply B.Typing.card
    | apply B.Typing.min
    | apply B.Typing.max
    | apply B.Typing.pow
    | apply B.Typing.union
    | apply B.Typing.inter
    | apply B.Typing.cprod
    | apply B.Typing.pfun
    all_goals assumption
  | «ℤ» => exact B.Typing.ℤ
  | 𝔹 => exact B.Typing.𝔹
  | and hx hy x_ih y_ih =>
    unfold B.simplifier simplifier_aux_and
    split <;> injections
    · apply B.Typing.bool
    · apply B.Typing.bool
    · apply B.Typing.and <;> assumption
  | not =>
    unfold B.simplifier simplifier_aux_not
    split
    · apply B.Typing.bool
    · apply B.Typing.bool
    · rename B.simplifier _ = _ => eq
      rename _ ⊢ᴮ B.simplifier _ : _ => typ
      rw [eq] at typ
      obtain ⟨-, _, _⟩ := B.Typing.notE typ
      assumption
    · apply B.Typing.not
      assumption
  | eq hx hy x_ih y_ih =>
    unfold B.simplifier simplifier_aux_eq
    split using x_eq y_eq | y_eq _ | y_eq | x_eq _ _ | y_eq _ | x_eq _ _ _
    · split_ifs
      · apply B.Typing.bool
      · apply B.Typing.eq
        · rw [x_eq] at x_ih
          exact x_ih
        · rw [y_eq] at y_ih
          exact y_ih
    · apply B.Typing.eq
      · rw [y_eq] at y_ih
        exact y_ih
      · exact x_ih
    · rw [y_eq] at y_ih
      rcases y_ih
      exact x_ih
    · rw [x_eq] at x_ih
      rcases x_ih
      exact y_ih
    · rw [y_eq] at y_ih
      rcases y_ih
      exact B.Typing.not x_ih
    · rw [x_eq] at x_ih
      rcases x_ih
      exact B.Typing.not y_ih
    · split_ifs
      · exact B.Typing.bool
      · apply B.Typing.eq <;> assumption
  | mem hx hy x_ih y_ih =>
    unfold B.simplifier simplifier_aux_mem
    split
    · extract_lets
      split_ifs
      · apply B.Typing.and
        · apply B.Typing.mem
          · exact x_ih
          · rename B.simplifier _ = _ => eq
            rw [eq] at y_ih
            rcases y_ih
            rw [←reduce_of_Forall₂'] <;> assumption
        · rename_i Γ α t S u v vs D P simpS_eq xs fv_inter_empty xs_vs_len_and_vs_notMem_fv_P vs_len
          obtain ⟨xs_vs_len, vs_notMem_fv_P⟩ := xs_vs_len_and_vs_notMem_fv_P
          rw [simpS_eq] at y_ih
          apply Typing.collectE at y_ih
          obtain ⟨αs, Ds, vs_nemp, vs_αs_len, vs_Ds_len, ⟨⟩, vs_nodup, rfl, typDs, typP, vs_Γ_disj⟩ := y_ih
          obtain ⟨v, rfl⟩ := List.length_eq_one_iff.mp vs_len
          rw [List.head!_cons]
          simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq] at vs_Γ_disj vs_notMem_fv_P
          rw [not_mem_fv_subst vs_notMem_fv_P]
          apply Typing.context_strengthening' at typP
          apply typP
          intro
          rw [List.mem_singleton]
          rintro rfl
          exact vs_notMem_fv_P
      · apply B.Typing.and
        · apply B.Typing.mem
          · assumption
          · rename B.simplifier _ = _ => eq
            rw [eq] at y_ih
            rcases y_ih
            rw [←reduce_of_Forall₂'] <;> assumption
        · rename_i Γ α t S u v vs D P simpS_eq xs fv_inter_empty xs_vs_len_and_vs_notMem_fv_P vs_len
          obtain ⟨xs_vs_len, vs_notMem_fv_P⟩ := xs_vs_len_and_vs_notMem_fv_P
          rw [simpS_eq] at y_ih
          apply Typing.collectE at y_ih
          obtain ⟨αs, Ds, vs_nemp, vs_αs_len, vs_Ds_len, ⟨⟩, vs_nodup, rfl, typDs, typP, vs_Γ_disj⟩ := y_ih
          rw [not_mem_fv_substList vs_notMem_fv_P]
          exact context_strengthening' typP vs_notMem_fv_P
      · apply B.Typing.mem
        · assumption
        · rename B.simplifier _ = _ => eq
          rw [eq] at y_ih
          rcases y_ih
          apply Typing.collect <;> assumption
      · apply B.Typing.mem
        · assumption
        · rename B.simplifier _ = _ => eq
          rw [eq] at y_ih
          rcases y_ih
          apply Typing.collect <;> assumption
    · extract_lets
      rename_i Γ α t S u v x y vs D P eq' eq xs
      rename B.simplifier _ = _ => eq
      rw [eq] at y_ih
      rw [eq'] at x_ih
      obtain ⟨α, β, ⟨⟩, typx, typy⟩ := Typing.mapletE x_ih
      obtain ⟨γ, αs, Ds, vs_nemp, vs_αs_len, vs_Ds_len, ⟨⟩, vs_nodup, rfl, typDs, typP, vs_Γ_disj⟩ := Typing.lambdaE y_ih
      split_ifs with h_if
      · apply B.Typing.eq _ typy
        rw [not_mem_fv_substList] <;>
        · try apply Typing.context_strengthening' typP
          exact h_if.2.1
      · apply B.Typing.eq _ typy
        · apply B.Typing.app _ typx
          · apply Typing.lambda <;> first
              | assumption
              | exact (List.Forall₂_eq_Forall₂' (vs_Ds_len ▸ vs_αs_len)).mp typDs
    · apply B.Typing.mem <;> assumption
  | collect vs_nemp vs_nodup vs_Γ_disj vs_αs_len vs_D_len typD typP typD_ih typP_ih =>
    unfold B.simplifier simplifier_aux_collect
    split
    · rename B.simplifier _ = _ => eq
      rw [eq] at typP_ih
      rcases typP_ih
      rename_i αs D _ vs _ _ _

      admit -- induction D
    · admit -- induction vs
  | all vs_nemp vs_αs_len vs_D_len typD typP typD_ih typP_ih => sorry
  | lambda vs_nemp vs_αs_len vs_D_len typD typP typD_ih typP_ih => sorry
  | app _ _ _ _ => sorry

theorem Term.abstract.go.alt_def (vs : List 𝒱) (P : B.Term) {«Δ» : 𝒱 → Option B.Dom}
  (Δ_isSome : ∀ v ∈ fv P, v ∉ vs → («Δ» v).isSome = true) {ys : List Dom}
  (vs_ys_len : vs.length = ys.length)
  (pf : ∀ v ∈ fv P, (Function.updates «Δ» vs ys v).isSome = true) :
  ⟦(Term.abstract.go P vs «Δ» Δ_isSome).uncurry fun ⟨i, hi⟩ => ys[i]'(by rwa [vs_ys_len] at hi)⟧ᴮ =
  ⟦P.abstract (Function.updates «Δ» vs ys) pf⟧ᴮ := by
  induction vs, ys, vs_ys_len using List.induction₂ generalizing «Δ» with
  | nil_nil =>
    unfold Term.abstract.go
    simp only [Function.updates] at pf
    simp_rw [Function.OfArity.uncurry, List.length_nil, Function.FromTypes.uncurry, List.pure_def,
      List.bind_eq_flatMap, Function.updates]
  | cons_cons v₀ vs y₀ ys _ ih =>
    unfold Term.abstract.go
    simp only [List.pure_def, List.bind_eq_flatMap, List.flatMap_cons, List.cons_append,
      List.nil_append, Function.updates] at pf
    simp only [List.length_cons, Matrix.head_fin_const, List.pure_def, List.bind_eq_flatMap,
      List.flatMap_cons, List.cons_append, List.nil_append, Function.updates]

    simp only [List.pure_def, List.bind_eq_flatMap] at ih
    apply ih _ pf

theorem List.flatten_map_eq_map {α β} (xs : List α) {f : α → β}:
  (List.map ([f ·]) xs).flatten = List.map f xs := by
  simp [List.flatten_eq_flatMap, List.map_eq_flatMap, List.flatMap_assoc]

theorem BType.hasArity_of_foldl {α : BType} {αs : List BType} :
  (αs.foldl (· ×ᴮ ·) α).hasArity (αs.length + 1) := by
  induction αs using List.reverseRecOn generalizing α with
      | nil =>
        rw [List.foldl_nil, List.length_nil, zero_add, BType.hasArity]
        trivial
      | append_singleton αs _ ih =>
        rw [←List.concat_eq_append, List.foldl_cons_last, List.length_concat, BType.hasArity]
        exact ih

theorem ZFSet.hasArity_of_foldl_defaultZFSet (α₀ : BType) (αs : List BType) :
  (αs.foldl (· ×ᴮ ·) α₀).defaultZFSet.hasArity (αs.length + 1) := by
  induction αs using List.reverseRecOn generalizing α₀ with
  | nil =>
    rw [List.foldl_nil, List.length_nil, zero_add, ZFSet.hasArity]
    trivial
  | append_singleton αs α ih =>
    rw [←List.concat_eq_append, List.foldl_cons_last, List.length_concat, ZFSet.hasArity]
    split_ifs with h
    · rw [BType.defaultZFSet, π₁_pair]
      exact ih α₀
    · push_neg at h
      simp_rw [BType.defaultZFSet, ne_eq, ZFSet.pair_inj, not_and, forall_apply_eq_imp_iff, imp_false, forall_eq'] at h
    · rintro ⟨⟩

theorem Term.abstract.go.alt_def₂ (vs : List 𝒱) (P : B.Term) {α} {«Δ» : 𝒱 → _root_.Option α}
  (αs : List α) (vs_αs_len : vs.length = αs.length) (Δ_isSome : ∀ v ∈ fv P, v ∉ vs → («Δ» v).isSome = true)
  (αs_nemp : αs ≠ [])
  (tmp₁ :
    ∀ v ∈ fv P, (Function.updates «Δ» vs (List.map (some ·) αs) v).isSome = true) :
  ((Term.abstract.go P vs «Δ» Δ_isSome).uncurry fun ⟨i, hi⟩ => αs[i]'(by rwa [←vs_αs_len])) =
  (P.abstract (Function.updates «Δ» vs (αs.map (some ·))) tmp₁) := by
  induction vs, αs, vs_αs_len using List.induction₂ generalizing «Δ» with
  | nil_nil =>
    simp only [List.length_nil, List.map_nil, Term.abstract.go, Function.updates, Function.OfArity.uncurry, Function.FromTypes.uncurry]
  | cons_cons v₀ vs α₀ αs len_eq ih =>
    cases vs with
    | nil =>
      obtain ⟨⟩ : αs = [] := by rw [←List.length_eq_zero_iff, ←len_eq, List.length_nil]
      simp only [Function.OfArity.uncurry, List.length_cons, List.length_nil, Nat.reduceAdd,
        Term.abstract.go, Matrix.head_fin_const, Fin.val_eq_zero, List.getElem_cons_zero,
        Function.FromTypes.uncurry_apply_succ, Function.FromTypes.uncurry, List.map_cons,
        List.map_nil, Function.updates]
    | cons v₁ vs =>
      obtain ⟨α₁, αs, rfl⟩ := List.exists_cons_of_length_eq_add_one len_eq.symm
      conv =>
        lhs
        simp only [List.reduce_cons_cons]
        rw [Term.abstract.go, Function.OfArity.uncurry, Function.FromTypes.uncurry]
        simp only [List.length_cons, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.getElem_cons_zero,
          Function.FromTypes.uncurry_apply_succ]
      conv =>
        rhs
        simp [List.map_cons, Function.updates]
      simp_rw [List.length_cons, List.map_cons] at ih

      exact ih _ (List.cons_ne_nil α₁ αs) tmp₁

theorem denote_term_abstract_go_eq {vs : List 𝒱} {P : B.Term} {«Δ» : 𝒱 → Option Dom}
  (vs_nodup : vs.Nodup)
  (vs_nemp : vs ≠ [])
  (f : Fin vs.length → Dom)
  (pf :
    ∀ v ∈ fv P, (Function.updates «Δ» vs (List.ofFn fun i => some (f i)) v).isSome = true) :
  (fun pf_go => ⟦(Term.abstract.go P vs «Δ» pf_go).uncurry f⟧ᴮ) ≍
  fun pf => ⟦P.abstract (Function.updates «Δ» vs (List.ofFn fun i => some (f i))) pf⟧ᴮ := by
  apply Function.hfunext
  · ext
    constructor
    · intro
      exact pf
    · intro _ v hv v_notMem_vs
      specialize pf v hv
      rwa [Function.updates_eq_if, dite_cond_eq_false (eq_false v_notMem_vs)] at pf
      · rw [List.length_ofFn]
      · exact vs_nodup
  · intro pf' pf'' heq
    rw [heq_eq_eq]
    have := @Term.abstract.go.alt_def₂ vs P Dom «Δ» (List.ofFn f) (by rw [List.length_ofFn]) pf'
      (by rwa [←List.length_pos_iff, List.length_ofFn, List.length_pos_iff])
      (by
        intro v hv
        rw [Function.updates_eq_if]
        · split_ifs with v_mem_vs
          · simp only [List.getElem_map, List.getElem_ofFn, Option.isSome_some]
          · exact pf' v hv v_mem_vs
        · rw [List.length_map, List.length_ofFn]
        · exact vs_nodup)
    simp only [List.getElem_ofFn, Fin.eta] at this
    conv =>
      enter [1,1,2]
      eta_expand
    rw [this]
    congr
    ext1
    congr
    ext1
    simp only [List.getElem?_map, List.getElem?_ofFn, Option.map_dif]

theorem denote_term_abstract_go_eq_term_abstract {vs : List 𝒱} {P : B.Term} {«Δ» : 𝒱 → Option Dom}
  (vs_nodup : vs.Nodup)
  (vs_nemp : vs ≠ [])
  (f : Fin vs.length → Dom)
  (pf :
    ∀ v ∈ fv P, (Function.updates «Δ» vs (List.ofFn fun i => some (f i)) v).isSome = true) :
  ⟦(Term.abstract.go P vs «Δ» (by
    intro v hv hvs
    specialize pf v hv
    rwa [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup, dite_cond_eq_false (eq_false hvs)] at pf)).uncurry f⟧ᴮ =
  ⟦P.abstract (Function.updates «Δ» vs (List.ofFn fun i => some (f i))) pf⟧ᴮ := by
  have := denote_term_abstract_go_eq vs_nodup vs_nemp f pf
  exact congr_heq this (y := pf) (proof_irrel_heq _ _)

theorem BType.list_foldl_eq_fin_foldl {α₀ : BType} {αs : List BType} :
  List.foldl (fun x1 x2 => x1 ×ᴮ x2) α₀ αs = Fin.foldl αs.length (fun x i => x ×ᴮ αs[↑i]) α₀ := by
  induction αs using List.reverseRecOn generalizing α₀ with
  | nil => simp only [List.foldl_nil, List.length_nil, Fin.foldl_zero]
  | append_singleton αs α₁ ih =>
    simp_rw [←List.concat_eq_append, List.foldl_cons_last, List.length_concat, Fin.foldl_succ_last]
    simp [ih]

theorem BType.mem_get_of_mem_reduce_toZFSet {αs : List BType} (αs_nemp : αs ≠ []) {x} {i : Fin αs.length} (hx : x ∈ (αs.reduce (· ×ᴮ ·) αs_nemp).toZFSet) :
  x.get αs.length i ∈ αs[i].toZFSet := by
  obtain ⟨α₀, αs, rfl⟩ := List.ne_nil_iff_exists_cons.mp αs_nemp
  rw [List.reduce, List.head, List.tail] at hx
  induction αs using List.reverseRecOn generalizing α₀ x with
  | nil =>
    rw [List.foldl_nil] at hx
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, get.eq_1]
    obtain ⟨i, hi⟩ := i
    simp only [List.length_cons, List.length_nil, zero_add, Nat.lt_one_iff] at hi
    subst i
    simpa
  | append_singleton αs α₁ ih =>
    obtain ⟨i, hi⟩ := i
    simp only [List.length_cons, List.length_append, List.length_nil, zero_add, Nat.lt_succ] at hi
    rw [Nat.le_iff_lt_or_eq] at hi
    rw [←List.concat_eq_append, List.foldl_cons_last, BType.toZFSet, ZFSet.mem_prod] at hx
    obtain ⟨x₀, x₀_def, x₁, x₁_def, rfl⟩ := hx
    simp only [List.length_cons, Fin.getElem_fin]

    rcases hi with hi | rfl
    · have : (α₀ :: (αs ++ [α₁]))[i] = (α₀ :: αs)[i] := by
        cases i with
        | zero => iterate 2 rw [List.getElem_cons_zero]
        | succ i => exact List.getElem_append_left (Nat.lt_of_succ_lt_succ hi)
      rw [this]
      unfold ZFSet.get
      split using h _ | _ _ n i _ hlen heq
      · rw [List.length_append, List.length_cons, List.length_nil, zero_add, Nat.add_eq_right, Nat.add_eq_zero, List.length_eq_zero_iff] at h
        nomatch h.2
      · rw [List.length_append, List.length_cons, List.length_nil, zero_add, Nat.succ_eq_add_one, Nat.succ_inj, Nat.succ_inj] at hlen
        subst i
        rw [Fin.heq_ext_iff] at heq
        · dsimp at heq
          subst i
          split_ifs
          · subst_eqs
            nomatch lt_irrefl _ ‹_›
          · rw [π₁_pair]
            exact ih α₀ (List.cons_ne_nil _ _) x₀_def
        · rw [List.length_append, List.length_cons, List.length_nil]
    · simp only [List.getElem_cons_succ, le_refl, List.getElem_append_right, Nat.sub_self, List.getElem_cons_zero]
      unfold ZFSet.get
      simp
      split using h _ | _ n i _ hlen heq
      · rw [List.length_append, List.length_cons, List.length_nil, zero_add, Nat.add_eq_right, Nat.add_eq_zero, List.length_eq_zero_iff] at h
        nomatch h.2
      · split_ifs
        · exact x₁_def
        · simp only [List.length_append, List.length_cons, List.length_nil, zero_add,
          Nat.succ_eq_add_one, Nat.add_right_cancel_iff] at hlen
          subst i
          rename αs.length + 1 < _ => h_αs_len
          simp only [Nat.succ_eq_add_one] at heq
          rw [Fin.heq_ext_iff] at heq
          · dsimp at heq
            rename ¬_ = Fin.last _ => hi
            rw [Fin.ext_iff, ←heq] at hi
            contradiction
          · rw [List.length_append, List.length_cons, List.length_nil, zero_add, Nat.add_right_cancel_iff]

theorem ZFSet.ofFinDom_get {n : ℕ} {τ : BType}
  {x : ZFSet}
  (n_pos : 0 < n)
  (hx : ∀ i, x.get n i ∈ (τ.get n i).toZFSet)
  (x_hasArity : x.hasArity n)
  (τ_hasArity : τ.hasArity n) :
  (ZFSet.ofFinDom fun i => ⟨x.get n i, τ.get n i, hx i⟩) = x := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one.mpr n_pos
  rw [ofFinDom]
  induction n generalizing x τ with
  | zero =>
    rw [Fin.foldl_zero]
    rfl
  | succ n ih =>
    simp only [hasArity, if_false_right] at x_hasArity
    unfold BType.hasArity at τ_hasArity
    split at τ_hasArity using α β
    on_goal 2 => contradiction
    obtain ⟨⟨a, b, rfl⟩, a_hasArity⟩ := x_hasArity
    rw [π₁_pair] at a_hasArity

    rw [Fin.foldl_succ_last]
    simp only [Nat.zero_lt_succ, forall_const] at ih
    specialize ih (x := a) (τ := α) ?_ a_hasArity τ_hasArity
    · intro i
      specialize hx i.castSucc
      rw [get] at hx
      split_ifs at hx with contr
      · obtain ⟨i, hi⟩ := i
        simp [Fin.ext_iff] at contr
        subst i
        nomatch lt_irrefl _ hi
      · simp only [π₁_pair, Fin.castPred_castSucc] at hx
        have : α.get (n + 1) i = (α ×ᴮ β).get (n + 1 + 1) i.castSucc := by
          clear * - τ_hasArity
          rw [BType.get]
          split_ifs with hi
          · obtain ⟨i, hi⟩ := i
            dsimp at hi
            subst i
            nomatch lt_irrefl _ hi
          · rfl
        rwa [this]
    · simp
      exact ih
