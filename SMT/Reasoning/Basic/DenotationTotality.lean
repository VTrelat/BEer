/-
  # SMT Denotation Totality for Well-Typed Terms

  This file proves that well-typed SMT terms with covered free variables
  always denote (i.e., their denotation is `Option.some`), and that the
  denotation carries the correct SMT type tag.
-/
import SMT.Reasoning.Defs
import SMT.Reasoning.Lemmas

open SMT SMT.PHOAS Classical

noncomputable section

namespace SMT.RenamingContext

/-! ## Auxiliary Lemmas -/

/-- Unfolding `TypeContext.update` for a cons: inserting v₀→τ₀ first, then recursing on vs'. -/
private lemma TypeContext.update_cons (Γ : SMT.TypeContext)
    (v₀ : SMT.𝒱) (τ₀ : SMTType) (vs' : List SMT.𝒱) (τs' : List SMTType)
    (hlen' : vs'.length = τs'.length) :
    Γ.update (v₀ :: vs') (τ₀ :: τs') (by simp [hlen']) = SMT.TypeContext.update (Γ.insert v₀ τ₀) vs' τs' hlen' := by
  simp only [SMT.TypeContext.update, List.length_cons, Fin.foldl_succ, Fin.getElem_fin,
    Fin.val_zero, List.getElem_cons_zero, Fin.val_succ, List.getElem_cons_succ]

/-- Key type-matching lemma: if `v ∈ vs` and `d` comes from `Function.updates` while `τ'` comes
    from `TypeContext.update`, and the values `x i` have type `τs[i]`, then `d.snd.fst = τ'`. -/
private lemma Function.updates_type_matches
    {vs : List SMT.𝒱} {τs : List SMTType}
    (len_eq : vs.length = τs.length)
    {x : Fin vs.length → SMT.Dom}
    (hx : ∀ i, (x i).2.1 = τs[i]'(by omega))
    (Dc : SMT.RenamingContext.Context) (Γ : SMT.TypeContext)
    {v : SMT.𝒱} (hvs : v ∈ vs)
    {d : SMT.Dom}
    (hd : Function.updates Dc vs ((List.ofFn x).map Option.some) v = some d)
    {τ' : SMTType}
    (hlookup : (Γ.update vs τs len_eq).lookup v = some τ') :
    d.snd.fst = τ' := by
  induction vs, τs, len_eq using List.induction₂ generalizing Dc Γ v d τ' with
  | nil_nil => simp at hvs
  | cons_cons v₀ vs' τ₀ τs' hlen' ih =>
    simp only [List.mem_cons] at hvs
    -- Unfold Function.updates for the cons step by directly changing to the reduced form
    have hlist : (List.ofFn x).map Option.some =
        Option.some (x ⟨0, by simp⟩) :: (List.ofFn (fun i : Fin vs'.length => x i.succ)).map Option.some := by
      simp [List.ofFn_succ]
    rw [hlist] at hd
    -- Function.updates on cons-cons reduces definitionally; use change to expose the form
    change Function.updates (Function.update Dc v₀ (Option.some (x ⟨0, by simp⟩))) vs'
        ((List.ofFn (fun i : Fin vs'.length => x i.succ)).map Option.some) v = Option.some d at hd
    -- Unfold TypeContext.update for the cons step
    rw [TypeContext.update_cons _ _ _ _ _ hlen'] at hlookup
    -- Case split: v appears in the tail vs' (IH applies) or not (base case)
    by_cases hvs' : v ∈ vs'
    · -- Tail case: recurse on vs'
      exact ih (x := fun i => x i.succ) (fun i => hx i.succ)
               (Dc := Function.update Dc v₀ (some (x ⟨0, by simp⟩)))
               (Γ := Γ.insert v₀ τ₀) hvs' hd hlookup
    · -- Head case: v = v₀, v ∉ vs'
      have hv : v = v₀ := by
        rcases hvs with rfl | h
        · rfl
        · exact absurd h hvs'
      subst hv
      rw [Function.updates_of_not_mem _ _ _ _ hvs', Function.update_self] at hd
      rw [SMT.TypeContext.lookup_update _ _ _ _ _ hvs', AList.lookup_insert] at hlookup
      exact (Option.some_inj.mp hd).symm ▸ (Option.some_inj.mp hlookup) ▸ hx ⟨0, by simp⟩

/--
When `Dc` respects `Γ`, and we update `Dc` with well-typed values for fresh variables `vs`,
the result respects `Γ.update vs τs`.
-/
private theorem respectsTypeContext_updates
    {Dc : Context} {Γ : SMT.TypeContext}
    {vs : List SMT.𝒱} {τs : List SMTType}
    (len_eq : vs.length = τs.length)
    (hcompat : RespectsTypeContext Dc Γ)
    (_hfresh : ∀ v ∈ vs, v ∉ Γ)
    {x : Fin vs.length → SMT.Dom}
    (hx : ∀ i, (x i).2.1 = τs[i]'(by omega) ∧ (x i).1 ∈ (τs[i]'(by omega)).toZFSet) :
    RespectsTypeContext
      (Function.updates Dc vs ((List.ofFn x).map Option.some))
      (Γ.update vs τs) := by
  intro v τ' hlookup
  by_cases hvs : v ∈ vs
  · -- v is a bound variable; extract d from Function.updates
    have h_isSome := Function.updates_isSome_of_mem_map_some Dc vs (List.ofFn x) v hvs (by simp)
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp h_isSome
    refine ⟨d, hd, ?_⟩
    exact Function.updates_type_matches len_eq (fun i => (hx i).1) Dc Γ hvs hd hlookup
  · rw [SMT.TypeContext.lookup_update _ _ _ _ _ hvs] at hlookup
    rw [Function.updates_of_not_mem Dc vs _ v hvs]
    exact hcompat hlookup

private theorem allSome_exists_of_forall_exists {α : Type*}
    {l : List (Option α)} (hl : ∀ (x : Option α), x ∈ l → ∃ v, x = some v) :
    ∃ vs, l.allSome = some vs := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons a as ih =>
    have ha := hl a List.mem_cons_self
    obtain ⟨v, rfl⟩ := ha
    obtain ⟨vs, hvs⟩ := ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))
    refine ⟨v :: vs, ?_⟩
    show ((some v) :: as).mapM id = some (v :: vs)
    rw [List.mapM_cons]
    change ((id (some v)).bind fun a => (List.mapM id as).bind fun b => pure (a :: b)) =
      some (v :: vs)
    simp only [id, show List.mapM id as = some vs from hvs, Option.bind_some,
      Option.pure_def]

private theorem abstractList_denote_isSome
    (ts : List SMT.Term) {Dc : Context}
    (hden : ∀ (t : SMT.Term) (_ : t ∈ ts) (hc : CoversFV Dc t),
      ∃ D, ⟦t.abstract Dc hc⟧ˢ = some D)
    {Dc_fv : ∀ t ∈ ts, ∀ v ∈ fv t, (Dc v).isSome}
    (i : Fin ts.length) :
    ∃ D, ⟦SMT.Term.abstractList ts Dc Dc_fv i⟧ˢ = some D := by
  induction ts with
  | nil => exact i.elim0
  | cons t ts' iht =>
    simp only [SMT.Term.abstractList]
    split
    · exact hden t List.mem_cons_self _
    · rename_i h
      exact iht (fun t' ht' hc => hden t' (List.mem_cons_of_mem t ht') hc) (i.pred h)

/-- `Fin.foldr` over indices equals `List.foldr` over `dropLast` / `getLast`:
    `Fin.foldr (n-1) (fun ⟨i,_⟩ acc => τs[i].pair acc) τs[n-1] = τs.dropLast.foldr (.pair ·) τs.getLast`
    for any non-empty list `τs`. -/
private lemma foldr_fin_eq_foldr_list
    (τs : List SMTType) (hne : τs ≠ []) :
    Fin.foldr (τs.length - 1)
      (fun (i : Fin (τs.length - 1)) acc => (τs[i.1]'(by omega)).pair acc)
      (τs[τs.length - 1]'(Nat.sub_lt (List.length_pos_of_ne_nil hne) Nat.one_pos)) =
    τs.dropLast.foldr (fun τ acc => τ.pair acc) (τs.getLast hne) := by
  induction τs with
  | nil => exact absurd rfl hne
  | cons τ τs' ih =>
    match τs' with
    | [] => simp [Fin.foldr, List.dropLast, List.getLast]; rfl
    | τ' :: τs'' =>
      have hne' : τ' :: τs'' ≠ [] := List.cons_ne_nil _ _
      simp only [List.length_cons, Nat.add_sub_cancel,
        List.dropLast_cons₂, List.getLast_cons hne',
        List.foldr_cons, Fin.foldr_succ, List.getElem_cons_succ]
      congr 1
      exact ih hne'

/-! ## Main Theorem -/

/--
Well-typed SMT terms with type-compatible renaming contexts always denote,
and the resulting domain value carries the correct SMT type.
-/
theorem denote_exists_of_typing
    {Γ : SMT.TypeContext} {t : SMT.Term} {τ : SMTType}
    (htyp : Γ ⊢ˢ t : τ)
    {Dc : Context}
    (hcompat : RespectsTypeContext Dc Γ)
    (hcov : CoversFV Dc t) :
    ∃ D : SMT.Dom, ⟦t.abstract Dc hcov⟧ˢ = some D ∧ D.2.1 = τ := by
  induction htyp generalizing Dc with
  -- Variable
  | var Γ v τ hlookup =>
    obtain ⟨d, hd, hd_typ⟩ := hcompat hlookup
    refine ⟨d, ?_, hd_typ⟩
    rw [SMT.Term.abstract.eq_def, SMT.denote, Option.pure_def]
    congr 1
    exact Option.get_of_mem _ hd
  -- Integer literal
  | int Γ n =>
    refine ⟨⟨.ofInt n, .int, ZFSet.mem_ofInt_Int n⟩, ?_, rfl⟩
    rw [SMT.Term.abstract.eq_def, SMT.denote, Option.pure_def]
  -- Boolean literal
  | bool Γ b =>
    refine ⟨⟨ZFSet.ZFBool.ofBool b, .bool, ZFSet.ZFBool.mem_ofBool_𝔹 b⟩, ?_, rfl⟩
    rw [SMT.Term.abstract.eq_def, SMT.denote, Option.pure_def]
  -- Application
  | app Γ f x σ τ _htf _htx ihf ihx =>
    obtain ⟨⟨F, _, hF⟩, denf, htypf⟩ := ihf hcompat (fun v hv => hcov v (fv.mem_app (.inl hv)))
    obtain ⟨⟨X, _, hX⟩, denx, htypx⟩ := ihx hcompat (fun v hv => hcov v (fv.mem_app (.inr hv)))
    dsimp at htypf htypx; subst htypf; subst htypx
    rw [SMTType.toZFSet] at hF
    have hIsFunc := ZFSet.mem_funs.mp hF
    have hIsPFunc := ZFSet.is_func_is_pfunc hIsFunc
    have hX_dom : X ∈ F.Dom := by rw [ZFSet.is_func_dom_eq hIsFunc]; exact hX
    let Res := F.fapply hIsPFunc ⟨X, hX_dom⟩
    refine ⟨⟨Res.1, τ, Res.2⟩, ?_, rfl⟩
    rw [SMT.Term.abstract.eq_def, SMT.denote, denf, denx]
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, dite_true,
      dif_pos hIsPFunc, dif_pos hX_dom, Res]
  -- Lambda
  | lambda Γ vs τs t γ _hfresh _hfresh_bv len_pos len_eq _htyp_body ih_body =>
    -- The type function used in abstract
    let τs' : Fin vs.length → SMTType := fun ⟨i, hi⟩ => τs[i]'(by omega)
    -- The body under the binder, after abstract + go
    set go_body := SMT.Term.abstract.go t vs Dc
      (fun v hv h => hcov v (fv.mem_lambda ⟨hv, h⟩)) with go_body_def
    -- Helper: for well-typed args, the body denotes with the correct type
    have body_den_of_typed (x : Fin vs.length → SMT.Dom)
        (hx : ∀ i, (x i).2.1 = τs' i ∧ (x i).1 ∈ (τs' i).toZFSet) :
        ∃ D : SMT.Dom, ⟦go_body.uncurry x⟧ˢ = some D ∧ D.2.1 = γ := by
      have hlen : vs.length = (List.ofFn x).length := by simp
      set Dc' := Function.updates Dc vs ((List.ofFn x).map Option.some) with Dc'_def
      -- The key bridge: go.uncurry x = abstract under updates
      have hbridge : ∀ (hcov' : CoversFV Dc' t),
          ⟦go_body.uncurry x⟧ˢ = ⟦t.abstract Dc' hcov'⟧ˢ := by
        intro hcov'
        have hx_eq : x = fun ⟨i, hi⟩ => (List.ofFn x)[i] := by funext ⟨i, hi⟩; simp
        conv_lhs => rw [hx_eq, go_body_def]
        rw [SMT.Term.abstract.go.alt_def₂ vs t (List.ofFn x) hlen
            (fun v hv h => hcov v (fv.mem_lambda ⟨hv, h⟩))
            (Dc'_def ▸ hcov')]
      have hcompat' : RespectsTypeContext Dc' (Γ.update vs τs) :=
        Dc'_def ▸ respectsTypeContext_updates len_eq hcompat _hfresh hx
      have hcov' : CoversFV Dc' t := by
        intro v hv
        by_cases hvs : v ∈ vs
        · rw [Dc'_def]
          exact Function.updates_isSome_of_mem_map_some Dc vs (List.ofFn x) v hvs (by simp)
        · rw [Dc'_def, Function.updates_of_not_mem Dc vs _ v hvs]
          exact hcov v (fv.mem_lambda ⟨hv, hvs⟩)
      rw [hbridge hcov']
      exact ih_body hcompat' hcov'
    -- Now prove the three conditions for lambda denote
    have body_isSome : ∀ {x : Fin vs.length → SMT.Dom},
        (∀ i, (x i).2.1 = τs' i ∧ (x i).1 ∈ (τs' i).toZFSet) →
        (⟦go_body.uncurry x⟧ˢ).isSome := by
      intro x hx
      exact Option.isSome_iff_exists.mpr ((body_den_of_typed x hx).imp fun D ⟨hD, _⟩ => hD)
    have body_typ_det : ∀ x y : Fin vs.length → SMT.Dom,
        (hx : ∀ i, (x i).2.1 = τs' i ∧ (x i).1 ∈ (τs' i).toZFSet) →
        (hy : ∀ i, (y i).2.1 = τs' i ∧ (y i).1 ∈ (τs' i).toZFSet) →
        ((⟦go_body.uncurry x⟧ˢ).get (body_isSome hx)).2.1 =
        ((⟦go_body.uncurry y⟧ˢ).get (body_isSome hy)).2.1 := by
      intro x y hx hy
      have htypx := (body_den_of_typed x hx).choose_spec.2
      have hdenx := (body_den_of_typed x hx).choose_spec.1
      have htypy := (body_den_of_typed y hy).choose_spec.2
      have hdeny := (body_den_of_typed y hy).choose_spec.1
      rw [show (⟦go_body.uncurry x⟧ˢ).get _ =
        (body_den_of_typed x hx).choose from Option.get_of_mem _ hdenx,
        show (⟦go_body.uncurry y⟧ˢ).get _ =
        (body_den_of_typed y hy).choose from Option.get_of_mem _ hdeny]
      rw [htypx, htypy]
    -- The abstract of lambda gives: .lambda τs' go_body.uncurry
    have habst : (SMT.Term.lambda vs τs t).abstract Dc hcov =
        PHOAS.Term.lambda τs' go_body.uncurry := by
      show _ = PHOAS.Term.lambda (fun ⟨i, hi⟩ => τs[i]) go_body.uncurry
      rw [SMT.Term.abstract, dif_pos len_eq, go_body_def]
    -- Show the denotation is some D with the correct type
    suffices h : (⟦(SMT.Term.lambda vs τs t).abstract Dc hcov⟧ˢ).isSome by
      obtain ⟨D, hD⟩ := Option.isSome_iff_exists.mp h
      refine ⟨D, hD, ?_⟩
      -- Extract the type from the lambda denote
      rw [habst] at hD
      simp only [SMT.denote, dif_pos len_pos] at hD
      split_ifs at hD
      · simp only [Option.pure_def] at hD
        cases hD; dsimp
        -- The body output type γ_body = γ by IH
        -- The argument type τ_fin ≡ List.foldr version (Fin.foldr = List.foldr identity)
        congr 1
        · -- Fin.foldr on indices = List.foldr on dropLast/getLast
          have hτs_ne : τs ≠ [] := List.ne_nil_of_length_pos (by omega)
          -- The goal uses vs.length; convert to τs.length via len_eq
          have hlen_sub : vs.length - 1 = τs.length - 1 := by omega
          simp only [τs', hlen_sub]
          exact foldr_fin_eq_foldr_list τs hτs_ne
        · -- Body type = γ
          have hdef : ∀ i, (⟨(τs' i).defaultZFSet, τs' i,
              SMTType.mem_toZFSet_of_defaultZFSet⟩ : SMT.Dom).2.1 = τs' i ∧
            (⟨(τs' i).defaultZFSet, τs' i,
              SMTType.mem_toZFSet_of_defaultZFSet⟩ : SMT.Dom).1 ∈ (τs' i).toZFSet :=
            fun i => ⟨rfl, SMTType.mem_toZFSet_of_defaultZFSet⟩
          have ⟨Dd, hDd, htypd⟩ := body_den_of_typed _ hdef
          rw [show (⟦go_body.uncurry _⟧ˢ).get _ = Dd from Option.get_of_mem _ hDd]
          exact htypd
    rw [habst]
    show (SMT.denote (PHOAS.Term.lambda τs' go_body.uncurry)).isSome
    rw [SMT.denote, dif_pos len_pos]
    split_ifs
    · rfl
  -- Forall
  | «forall» Γ vs τs P _hfresh _hfresh_bv len_pos len_eq _htyp_body ih_body =>
    let τs' : Fin vs.length → SMTType := fun ⟨i, hi⟩ => τs[i]'(by omega)
    set go_body := SMT.Term.abstract.go P vs Dc
      (fun v hv h => hcov v (fv.mem_forall ⟨hv, h⟩)) with go_body_def
    have body_den_of_typed (x : Fin vs.length → SMT.Dom)
        (hx : ∀ i, (x i).2.1 = τs' i ∧ (x i).1 ∈ (τs' i).toZFSet) :
        ∃ D : SMT.Dom, ⟦go_body.uncurry x⟧ˢ = some D ∧ D.2.1 = .bool := by
      have hlen : vs.length = (List.ofFn x).length := by simp
      set Dc' := Function.updates Dc vs ((List.ofFn x).map Option.some) with Dc'_def
      have hbridge : ∀ (hcov' : CoversFV Dc' P),
          ⟦go_body.uncurry x⟧ˢ = ⟦P.abstract Dc' hcov'⟧ˢ := by
        intro hcov'
        have hx_eq : x = fun ⟨i, hi⟩ => (List.ofFn x)[i] := by funext ⟨i, hi⟩; simp
        conv_lhs => rw [hx_eq, go_body_def]
        rw [SMT.Term.abstract.go.alt_def₂ vs P (List.ofFn x) hlen
            (fun v hv h => hcov v (fv.mem_forall ⟨hv, h⟩))
            (Dc'_def ▸ hcov')]
      have hcompat' : RespectsTypeContext Dc' (Γ.update vs τs) :=
        Dc'_def ▸ respectsTypeContext_updates len_eq hcompat _hfresh hx
      have hcov' : CoversFV Dc' P := by
        intro v hv
        by_cases hvs : v ∈ vs
        · rw [Dc'_def]
          exact Function.updates_isSome_of_mem_map_some Dc vs (List.ofFn x) v hvs (by simp)
        · rw [Dc'_def, Function.updates_of_not_mem Dc vs _ v hvs]
          exact hcov v (fv.mem_forall ⟨hv, hvs⟩)
      rw [hbridge hcov']
      exact ih_body hcompat' hcov'
    have body_isSome : ∀ {x : Fin vs.length → SMT.Dom},
        (∀ i, (x i).2.1 = τs' i ∧ (x i).1 ∈ (τs' i).toZFSet) →
        (⟦go_body.uncurry x⟧ˢ).isSome := by
      intro x hx
      exact Option.isSome_iff_exists.mpr ((body_den_of_typed x hx).imp fun D ⟨hD, _⟩ => hD)
    have habst : (SMT.Term.forall vs τs P).abstract Dc hcov =
        PHOAS.Term.forall τs' go_body.uncurry := by
      show _ = PHOAS.Term.forall (fun ⟨i, hi⟩ => τs[i]) go_body.uncurry
      rw [SMT.Term.abstract, dif_pos len_eq, go_body_def]
    suffices h : (⟦(SMT.Term.forall vs τs P).abstract Dc hcov⟧ˢ).isSome by
      obtain ⟨D, hD⟩ := Option.isSome_iff_exists.mp h
      refine ⟨D, hD, ?_⟩
      -- D.2.1 = .bool follows from forall denote always returning .bool
      rw [habst] at hD
      show D.2.1 = .bool
      simp only [SMT.denote, dif_pos len_pos] at hD
      split_ifs at hD
      · simp only [Option.pure_def] at hD
        cases hD; rfl
    rw [habst]
    show (SMT.denote (PHOAS.Term.forall τs' go_body.uncurry)).isSome
    rw [SMT.denote, dif_pos len_pos]
    split_ifs
    · rfl
  -- Exists
  | «exists» Γ vs τs P _hfresh _hfresh_bv len_pos len_eq _htyp_body ih_body =>
    -- exists is defined as ¬(forall (¬ P))
    let τs' : Fin vs.length → SMTType := fun ⟨i, hi⟩ => τs[i]'(by omega)
    set go_body := SMT.Term.abstract.go P vs Dc
      (fun v hv h => hcov v (fv.mem_exists ⟨hv, h⟩)) with go_body_def
    -- Same body_den_of_typed as forall case
    have body_den_of_typed (x : Fin vs.length → SMT.Dom)
        (hx : ∀ i, (x i).2.1 = τs' i ∧ (x i).1 ∈ (τs' i).toZFSet) :
        ∃ D : SMT.Dom, ⟦go_body.uncurry x⟧ˢ = some D ∧ D.2.1 = .bool := by
      have hlen : vs.length = (List.ofFn x).length := by simp
      set Dc' := Function.updates Dc vs ((List.ofFn x).map Option.some) with Dc'_def
      have hbridge : ∀ (hcov' : CoversFV Dc' P),
          ⟦go_body.uncurry x⟧ˢ = ⟦P.abstract Dc' hcov'⟧ˢ := by
        intro hcov'
        have hx_eq : x = fun ⟨i, hi⟩ => (List.ofFn x)[i] := by funext ⟨i, hi⟩; simp
        conv_lhs => rw [hx_eq, go_body_def]
        rw [SMT.Term.abstract.go.alt_def₂ vs P (List.ofFn x) hlen
            (fun v hv h => hcov v (fv.mem_exists ⟨hv, h⟩))
            (Dc'_def ▸ hcov')]
      have hcompat' : RespectsTypeContext Dc' (Γ.update vs τs) :=
        Dc'_def ▸ respectsTypeContext_updates len_eq hcompat _hfresh hx
      have hcov' : CoversFV Dc' P := by
        intro v hv
        by_cases hvs : v ∈ vs
        · rw [Dc'_def]
          exact Function.updates_isSome_of_mem_map_some Dc vs (List.ofFn x) v hvs (by simp)
        · rw [Dc'_def, Function.updates_of_not_mem Dc vs _ v hvs]
          exact hcov v (fv.mem_exists ⟨hv, hvs⟩)
      rw [hbridge hcov']
      exact ih_body hcompat' hcov'
    -- The body of the negated forall (¬P) also denotes
    have neg_body_isSome : ∀ {x : Fin vs.length → SMT.Dom},
        (∀ i, (x i).2.1 = τs' i ∧ (x i).1 ∈ (τs' i).toZFSet) →
        (⟦¬ˢ' go_body.uncurry x⟧ˢ).isSome := by
      intro x hx
      obtain ⟨⟨X, _, hX⟩, hD, hDtyp⟩ := body_den_of_typed x hx
      dsimp at hDtyp; subst hDtyp
      rw [SMT.denote, hD]
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some]; rfl
    -- The abstract of exists is ¬(forall τs' (¬ body))
    have habst : (SMT.Term.exists vs τs P).abstract Dc hcov =
        PHOAS.Term.exists τs' go_body.uncurry := by
      show _ = PHOAS.Term.exists (fun ⟨i, hi⟩ => τs[i]) go_body.uncurry
      rw [SMT.Term.abstract, dif_pos len_eq, go_body_def]
    -- PHOAS.Term.exists = ¬(forall (¬ body))
    -- The inner forall denotes
    have forall_neg_isSome :
        (SMT.denote (PHOAS.Term.forall τs' (¬ˢ' go_body.uncurry ·))).isSome := by
      rw [SMT.denote, dif_pos len_pos]
      split_ifs
      · rfl
    -- The outer negation denotes
    have forall_neg_den : ∃ D : SMT.Dom,
        SMT.denote (PHOAS.Term.forall τs' (¬ˢ' go_body.uncurry ·)) = some D ∧
        D.2.1 = .bool := by
      obtain ⟨D, hD⟩ := Option.isSome_iff_exists.mp forall_neg_isSome
      refine ⟨D, hD, ?_⟩
      rw [SMT.denote, dif_pos len_pos] at hD
      split_ifs at hD
      · simp only [Option.pure_def] at hD; cases hD; rfl
    obtain ⟨⟨Z, _, hZ⟩, den_forall, htyp_forall⟩ := forall_neg_den
    dsimp at htyp_forall; subst htyp_forall
    refine ⟨⟨¬ᶻ Z, .bool, overloadUnaryOp_mem⟩, ?_, rfl⟩
    rw [habst]
    show SMT.denote (PHOAS.Term.exists τs' go_body.uncurry) = _
    simp only [PHOAS.Term.exists]
    rw [SMT.denote, den_forall]
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some]
  -- Equality
  | eq Γ t₁ t₂ σ _ht₁ _ht₂ ih₁ ih₂ =>
    obtain ⟨D₁, den₁, htyp₁⟩ := ih₁ hcompat (fun v hv => hcov v (fv.mem_eq (.inl hv)))
    obtain ⟨D₂, den₂, htyp₂⟩ := ih₂ hcompat (fun v hv => hcov v (fv.mem_eq (.inr hv)))
    obtain ⟨X, α, hX⟩ := D₁; dsimp at htyp₁; subst htyp₁
    obtain ⟨Y, β, hY⟩ := D₂; dsimp at htyp₂; subst htyp₂
    exact ⟨⟨X =ᶻ Y, .bool, overloadBinOp_mem hX hY⟩, by
      rw [SMT.Term.abstract.eq_def, SMT.denote, den₁, den₂]
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, dite_true], rfl⟩
  -- Conjunction
  | and Γ t₁ t₂ _ht₁ _ht₂ ih₁ ih₂ =>
    obtain ⟨D₁, den₁, htyp₁⟩ := ih₁ hcompat (fun v hv => hcov v (fv.mem_and (.inl hv)))
    obtain ⟨D₂, den₂, htyp₂⟩ := ih₂ hcompat (fun v hv => hcov v (fv.mem_and (.inr hv)))
    obtain ⟨P, α, hP⟩ := D₁; dsimp at htyp₁; subst htyp₁
    obtain ⟨Q, β, hQ⟩ := D₂; dsimp at htyp₂; subst htyp₂
    exact ⟨⟨P ⋀ᶻ Q, .bool, overloadBinOp_mem hP hQ⟩, by
      rw [SMT.Term.abstract.eq_def, SMT.denote, den₁, den₂]
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some,
        Option.failure_eq_none], rfl⟩
  -- Disjunction (or x y = ¬(¬x ∧ ¬y))
  | or Γ t₁ t₂ _ht₁ _ht₂ ih₁ ih₂ =>
    obtain ⟨D₁, den₁, htyp₁⟩ := ih₁ hcompat (fun v hv => hcov v (fv.mem_or (.inl hv)))
    obtain ⟨D₂, den₂, htyp₂⟩ := ih₂ hcompat (fun v hv => hcov v (fv.mem_or (.inr hv)))
    obtain ⟨P, α, hP⟩ := D₁; dsimp at htyp₁; subst htyp₁
    obtain ⟨Q, β, hQ⟩ := D₂; dsimp at htyp₂; subst htyp₂
    have hnotP : (¬ᶻ P) ∈ (ZFSet.𝔹 : ZFSet) := overloadUnaryOp_mem
    have hnotQ : (¬ᶻ Q) ∈ (ZFSet.𝔹 : ZFSet) := overloadUnaryOp_mem
    have hconj : ((¬ᶻ P) ⋀ᶻ (¬ᶻ Q)) ∈ (ZFSet.𝔹 : ZFSet) := overloadBinOp_mem hnotP hnotQ
    refine ⟨⟨¬ᶻ ((¬ᶻ P) ⋀ᶻ (¬ᶻ Q)), .bool, ?_⟩, ?_, rfl⟩
    · exact overloadUnaryOp_mem
    · rw [SMT.Term.abstract.eq_def]
      show SMT.denote (PHOAS.Term.or _ _) = _
      simp only [PHOAS.Term.or]
      rw [SMT.denote] -- outer ¬
      rw [SMT.denote] -- inner ∧
      rw [SMT.denote, den₁] -- ¬ lhs
      rw [SMT.denote, den₂] -- ¬ rhs
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some]
  -- Negation
  | not Γ t _ht ih =>
    obtain ⟨D, den, htyp_d⟩ := ih hcompat (fun v hv => hcov v (fv.mem_not hv))
    obtain ⟨X, α, hX⟩ := D; dsimp at htyp_d; subst htyp_d
    refine ⟨⟨¬ᶻ X, .bool, overloadUnaryOp_mem⟩, ?_, rfl⟩
    rw [SMT.Term.abstract.eq_def, SMT.denote, den]
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.failure_eq_none]
  -- Implication (imp x y = ¬(x ∧ ¬y))
  | imp Γ t₁ t₂ _ht₁ _ht₂ ih₁ ih₂ =>
    obtain ⟨D₁, den₁, htyp₁⟩ := ih₁ hcompat (fun v hv => hcov v (fv.mem_imp (.inl hv)))
    obtain ⟨D₂, den₂, htyp₂⟩ := ih₂ hcompat (fun v hv => hcov v (fv.mem_imp (.inr hv)))
    obtain ⟨P, α, hP⟩ := D₁; dsimp at htyp₁; subst htyp₁
    obtain ⟨Q, β, hQ⟩ := D₂; dsimp at htyp₂; subst htyp₂
    have hnotQ : (¬ᶻ Q) ∈ (ZFSet.𝔹 : ZFSet) := overloadUnaryOp_mem
    have hconj : (P ⋀ᶻ (¬ᶻ Q)) ∈ (ZFSet.𝔹 : ZFSet) := overloadBinOp_mem hP hnotQ
    refine ⟨⟨¬ᶻ (P ⋀ᶻ (¬ᶻ Q)), .bool, ?_⟩, ?_, rfl⟩
    · exact overloadUnaryOp_mem
    · rw [SMT.Term.abstract.eq_def]
      show SMT.denote (PHOAS.Term.imp _ _) = _
      simp only [PHOAS.Term.imp]
      rw [SMT.denote] -- outer ¬
      rw [SMT.denote, den₁] -- inner ∧ (lhs rewrite)
      rw [SMT.denote, den₂] -- ¬ rhs
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some]
  -- If-then-else
  | ite Γ c t e σ _hc _ht _he ihc iht ihe =>
    obtain ⟨Dc', denc, htypc⟩ := ihc hcompat (fun v hv => hcov v (fv.mem_ite (.inl hv)))
    obtain ⟨Dt, dent, htypt⟩ := iht hcompat (fun v hv => hcov v (fv.mem_ite (.inr (.inl hv))))
    obtain ⟨De, dene, htype⟩ := ihe hcompat (fun v hv => hcov v (fv.mem_ite (.inr (.inr hv))))
    obtain ⟨C, γ, hC⟩ := Dc'; dsimp at htypc; subst htypc
    rw [SMT.Term.abstract.eq_def, SMT.denote, denc]
    simp only [Option.bind_eq_bind, Option.bind_some, Option.failure_eq_none]
    split
    · exact ⟨Dt, dent, htypt⟩
    · exact ⟨De, dene, htype⟩
  -- Some
  | some Γ t σ _ht ih =>
    obtain ⟨D, den, htyp_d⟩ := ih hcompat (fun v hv => hcov v (fv.mem_some hv))
    obtain ⟨T, α, hTα⟩ := D; dsimp at htyp_d; subst htyp_d
    exact ⟨⟨(ZFSet.Option.some ⟨T, hTα⟩).1, α.option, SetLike.coe_mem _⟩, by
      rw [SMT.Term.abstract.eq_def, SMT.denote, den]
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some], rfl⟩
  -- None (as none (.option τ))
  | none Γ τ =>
    exact ⟨⟨(@ZFSet.Option.none τ.toZFSet).1, τ.option, SetLike.coe_mem _⟩, by
      rw [SMT.Term.abstract.eq_def, SMT.denote, Option.pure_def], rfl⟩
  -- The
  | the Γ t σ _ht ih =>
    obtain ⟨D, den, htyp_d⟩ := ih hcompat (fun v hv => hcov v (fv.mem_the hv))
    obtain ⟨T, α, hTα⟩ := D; dsimp at htyp_d; cases htyp_d
    exact ⟨⟨ZFSet.Option.the SMTType.toZFSet_nonempty ⟨T, hTα⟩, σ, SetLike.coe_mem _⟩, by
      rw [SMT.Term.abstract.eq_def, SMT.denote, den]
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some,
        Option.failure_eq_none], rfl⟩
  -- Pair
  | pair Γ t₁ τ₁ t₂ τ₂ _ht₁ _ht₂ ih₁ ih₂ =>
    obtain ⟨D₁, den₁, htyp₁⟩ := ih₁ hcompat (fun v hv => hcov v (fv.mem_pair (.inl hv)))
    obtain ⟨D₂, den₂, htyp₂⟩ := ih₂ hcompat (fun v hv => hcov v (fv.mem_pair (.inr hv)))
    obtain ⟨X, α, hX⟩ := D₁; dsimp at htyp₁; subst htyp₁
    obtain ⟨Y, β, hY⟩ := D₂; dsimp at htyp₂; subst htyp₂
    exact ⟨⟨X.pair Y, .pair α β, by rw [ZFSet.pair_mem_prod]; exact ⟨hX, hY⟩⟩, by
      rw [SMT.Term.abstract.eq_def, SMT.denote, den₁, den₂]
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some], rfl⟩
  -- Fst
  | fst Γ t σ τ _ht ih =>
    obtain ⟨D, den, htyp_d⟩ := ih hcompat (fun v hv => hcov v (fv.mem_fst hv))
    obtain ⟨T, α, hT⟩ := D; dsimp at htyp_d; cases htyp_d
    have hmem : T ∈ (SMTType.pair σ τ).toZFSet := hT
    rw [SMTType.toZFSet, ZFSet.mem_prod] at hmem
    obtain ⟨T₁, hT₁, T₂, hT₂, hTeq⟩ := hmem
    refine ⟨⟨T.π₁, σ, ?_⟩, ?_, rfl⟩
    · rw [hTeq, ZFSet.π₁_pair]; exact hT₁
    · rw [SMT.Term.abstract.eq_def, SMT.denote, den]
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some]
  -- Snd
  | snd Γ t σ τ _ht ih =>
    obtain ⟨D, den, htyp_d⟩ := ih hcompat (fun v hv => hcov v (fv.mem_snd hv))
    obtain ⟨T, α, hT⟩ := D; dsimp at htyp_d; cases htyp_d
    have hmem : T ∈ (SMTType.pair σ τ).toZFSet := hT
    rw [SMTType.toZFSet, ZFSet.mem_prod] at hmem
    obtain ⟨T₁, hT₁, T₂, hT₂, hTeq⟩ := hmem
    refine ⟨⟨T.π₂, τ, ?_⟩, ?_, rfl⟩
    · rw [hTeq, ZFSet.π₂_pair]; exact hT₂
    · rw [SMT.Term.abstract.eq_def, SMT.denote, den]
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some]
  -- Distinct
  | distinct Γ ts σ _hts ih =>
    -- Each element denotes by IH
    have hden_each : ∀ (t : SMT.Term) (ht : t ∈ ts) (hc : CoversFV Dc t),
        ∃ D, ⟦t.abstract Dc hc⟧ˢ = some D :=
      fun t ht hc => (ih t ht hcompat hc).imp fun D ⟨hD, _⟩ => hD
    -- Prove each element of the ofFn list denotes
    have hallSome : ∀ x ∈ List.ofFn (fun i => ⟦SMT.Term.abstractList ts Dc
        (fun t ht v hv => hcov v (fv.mem_distinct ⟨t, ht⟩ hv)) i⟧ˢ),
        ∃ v, x = some v := by
      intro x hx
      rw [List.mem_ofFn] at hx
      obtain ⟨i, rfl⟩ := hx
      exact abstractList_denote_isSome ts hden_each i
    obtain ⟨Ts, hTs⟩ := allSome_exists_of_forall_exists hallSome
    exact ⟨⟨SMT.denote_distinct Ts, .bool, SetLike.coe_mem _⟩, by
      rw [SMT.Term.abstract.eq_def, SMT.denote, hTs]
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some], rfl⟩
  -- Less-than-or-equal
  | le Γ t₁ t₂ _ht₁ _ht₂ ih₁ ih₂ =>
    obtain ⟨D₁, den₁, htyp₁⟩ := ih₁ hcompat (fun v hv => hcov v (fv.mem_le (.inl hv)))
    obtain ⟨D₂, den₂, htyp₂⟩ := ih₂ hcompat (fun v hv => hcov v (fv.mem_le (.inr hv)))
    obtain ⟨X, α, hX⟩ := D₁; dsimp at htyp₁; subst htyp₁
    obtain ⟨Y, β, hY⟩ := D₂; dsimp at htyp₂; subst htyp₂
    exact ⟨⟨X ≤ᶻ Y, .bool, overloadBinOp_mem hX hY⟩, by
      rw [SMT.Term.abstract.eq_def, SMT.denote, den₁, den₂]
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some,
        Option.failure_eq_none], rfl⟩
  -- Addition
  | add Γ t₁ t₂ _ht₁ _ht₂ ih₁ ih₂ =>
    obtain ⟨D₁, den₁, htyp₁⟩ := ih₁ hcompat (fun v hv => hcov v (fv.mem_add (.inl hv)))
    obtain ⟨D₂, den₂, htyp₂⟩ := ih₂ hcompat (fun v hv => hcov v (fv.mem_add (.inr hv)))
    obtain ⟨X, α, hX⟩ := D₁; dsimp at htyp₁; subst htyp₁
    obtain ⟨Y, β, hY⟩ := D₂; dsimp at htyp₂; subst htyp₂
    exact ⟨⟨X +ᶻ Y, .int, overloadBinOp_mem hX hY⟩, by
      rw [SMT.Term.abstract.eq_def, SMT.denote, den₁, den₂]
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some,
        Option.failure_eq_none], rfl⟩
  -- Subtraction
  | sub Γ t₁ t₂ _ht₁ _ht₂ ih₁ ih₂ =>
    obtain ⟨D₁, den₁, htyp₁⟩ := ih₁ hcompat (fun v hv => hcov v (fv.mem_sub (.inl hv)))
    obtain ⟨D₂, den₂, htyp₂⟩ := ih₂ hcompat (fun v hv => hcov v (fv.mem_sub (.inr hv)))
    obtain ⟨X, α, hX⟩ := D₁; dsimp at htyp₁; subst htyp₁
    obtain ⟨Y, β, hY⟩ := D₂; dsimp at htyp₂; subst htyp₂
    exact ⟨⟨X -ᶻ Y, .int, overloadBinOp_mem hX hY⟩, by
      rw [SMT.Term.abstract.eq_def, SMT.denote, den₁, den₂]
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some,
        Option.failure_eq_none], rfl⟩
  -- Multiplication
  | mul Γ t₁ t₂ _ht₁ _ht₂ ih₁ ih₂ =>
    obtain ⟨D₁, den₁, htyp₁⟩ := ih₁ hcompat (fun v hv => hcov v (fv.mem_mul (.inl hv)))
    obtain ⟨D₂, den₂, htyp₂⟩ := ih₂ hcompat (fun v hv => hcov v (fv.mem_mul (.inr hv)))
    obtain ⟨X, α, hX⟩ := D₁; dsimp at htyp₁; subst htyp₁
    obtain ⟨Y, β, hY⟩ := D₂; dsimp at htyp₂; subst htyp₂
    exact ⟨⟨X *ᶻ Y, .int, overloadBinOp_mem hX hY⟩, by
      rw [SMT.Term.abstract.eq_def, SMT.denote, den₁, den₂]
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some,
        Option.failure_eq_none], rfl⟩

/-! ## FV-restricted variant -/

/-- Type compatibility restricted to free variables of the term. -/
abbrev RespectsTypeContextOnFV (Dc : Context) (Γ : SMT.TypeContext) (t : SMT.Term) : Prop :=
  ∀ ⦃v : SMT.𝒱⦄ ⦃τ : SMTType⦄, v ∈ SMT.fv t → Γ.lookup v = some τ →
    ∃ d : SMT.Dom, Dc v = some d ∧ d.2.1 = τ

/--
Variant of `denote_exists_of_typing` that only requires type compatibility on free variables.
-/
theorem denote_exists_of_typing_fv
    {Γ : SMT.TypeContext} {t : SMT.Term} {τ : SMTType}
    (htyp : Γ ⊢ˢ t : τ)
    {Dc : Context}
    (hcompat : RespectsTypeContextOnFV Dc Γ t)
    (hcov : CoversFV Dc t) :
    ∃ D : SMT.Dom, ⟦t.abstract Dc hcov⟧ˢ = some D ∧ D.2.1 = τ := by
  -- Construct Dc' that agrees with Dc on fv(t) and uses defaults elsewhere
  let Dc' : Context := fun v =>
    if v ∈ SMT.fv t then Dc v
    else match Γ.lookup v with
      | some σ => some ⟨σ.defaultZFSet, σ, SMTType.mem_toZFSet_of_defaultZFSet⟩
      | none => none
  have hcov' : CoversFV Dc' t := by
    intro v hv; simp only [Dc', if_pos hv]; exact hcov v hv
  have hcompat' : RespectsTypeContext Dc' Γ := by
    intro v σ hlookup
    simp only [Dc']
    by_cases hvfv : v ∈ SMT.fv t
    · simp only [if_pos hvfv]
      exact hcompat hvfv hlookup
    · simp only [if_neg hvfv, hlookup]
      exact ⟨⟨σ.defaultZFSet, σ, SMTType.mem_toZFSet_of_defaultZFSet⟩, rfl, rfl⟩
  have hagree : AgreesOnFV Dc Dc' t := by
    intro v hv; simp only [Dc', if_pos hv]
  obtain ⟨D, hD, hty⟩ := denote_exists_of_typing htyp hcompat' hcov'
  refine ⟨D, ?_, hty⟩
  have heq := denote_congr_of_agreesOnFV (h1 := hcov) (h2 := hcov') hagree
  unfold denote at heq
  rw [heq]; exact hD

/-! ## Corollaries -/

/-- Well-typed terms with type-compatible contexts always denote. -/
theorem denote_isSome_of_typing
    {Γ : SMT.TypeContext} {t : SMT.Term} {τ : SMTType}
    (htyp : Γ ⊢ˢ t : τ)
    {Dc : Context}
    (hcompat : RespectsTypeContext Dc Γ)
    (hcov : CoversFV Dc t) :
    (⟦t.abstract Dc hcov⟧ˢ).isSome = true := by
  obtain ⟨D, hD, _⟩ := denote_exists_of_typing htyp hcompat hcov
  exact Option.isSome_iff_exists.mpr ⟨D, hD⟩

/-- Denotation of a well-typed term has the correct SMT type. -/
theorem denote_type_of_typing
    {Γ : SMT.TypeContext} {t : SMT.Term} {τ : SMTType}
    (htyp : Γ ⊢ˢ t : τ)
    {Dc : Context}
    (hcompat : RespectsTypeContext Dc Γ)
    (hcov : CoversFV Dc t)
    {D : SMT.Dom}
    (hden : ⟦t.abstract Dc hcov⟧ˢ = some D) :
    D.2.1 = τ := by
  obtain ⟨D', hD', htyp'⟩ := denote_exists_of_typing htyp hcompat hcov
  rw [hD'] at hden; cases hden; exact htyp'

end SMT.RenamingContext
