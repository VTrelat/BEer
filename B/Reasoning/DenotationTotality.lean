/-
  # B Denotation Totality for Well-Typed PHOAS Terms

  This file proves that well-typed B PHOAS terms with type-compatible
  contexts always denote (i.e. their `denote` is `Option.some`), and that
  the denotation carries the correct B type tag.

  This is the B-side analog of `SMT.RenamingContext.denote_exists_of_typing`
  in `SMT/Reasoning/Basic/DenotationTotality.lean`.

  ## Status

  * **Proven (19 cases)**: var, int, bool, maplet, add, sub, mul, and, not,
    eq, le, ℤ, 𝔹, mem, pow, cprod, union, inter, pfun.
  * **Open (7 cases)**: collect, lambda, all (binders); app, card, min, max
    (partial operations).

  ## Why some cases are necessarily open

  The B `denote` semantics is inherently partial for several constructors:

  * `app f x` requires `F.IsPFunc τ.toZFSet σ.toZFSet ∧ X ∈ F.Dom`. Typing
    only says `F : .set (τ ×ᴮ σ)` (a set of pairs), NOT that it's a (partial)
    function. So `app` may fail at runtime even on well-typed terms.

  * `card S` requires `S' .IsFinite`. Typing alone does not guarantee finiteness
    of the underlying ZFSet.

  * `min S` / `max S` require `S' .IsFinite ∧ S' .Nonempty`. Same issue as `card`.

  Closing these cases REQUIRES one of:

  1. Strengthening the theorem statement with additional hypotheses (e.g.
     "all `app` subterms have IsPFunc witnesses").
  2. Changing the underlying B semantics to make `denote` total on well-typed
     terms (e.g. by returning `default` on partial-operation failure).
  3. Restricting the theorem to a fragment of B without `app`/`card`/`min`/`max`.

  The binder cases (collect, lambda, all) are open for a more fundamental
  reason than first thought (~500+ line substitution machinery is the SMT-side
  approach, but the B-side has an extra obstacle):

  The B-side `denote` for `collect`/`all`/`lambda` includes conditions

      `den_P : ∀ {x}, ZFSet.ofFinDom x ∈ 𝒟 → ⟦P x⟧ᴮ.isSome`
      `typP_det : ∀ x y, ... → ⟦P x⟧.get _ |>.2.1 = ⟦P y⟧.get _ |>.2.1`

  that quantify over arbitrary `x : Fin n → Dom`. These can fail when `x`'s
  intrinsic type tags `(x i).2.1` don't match `α i`, even when the `WellTyped`
  hypothesis only constrains values via `ofFinDom x ∈ 𝒟 ⊆ τ.toZFSet`.
  Because BType ZFSets overlap (e.g., `∅ = zffalse ∈ .bool ∩ .set α`), there
  exist value-shape-correct but type-tag-incorrect `x`s for which `⟦P x⟧.isSome`
  fails (when `P` uses operations like `and`/`add` that pattern-match on type
  tags) or returns the wrong type (failing `typP_det`).

  This is asymmetric with the SMT side, where the analogous condition
  `den_t_isSome` includes `(∀ i, (x i).2.1 = (τs i) ∧ ...)` as a precondition
  (see `SMT/Semantics.lean:136`), restricting attention to typed `x`s.

  Closing these cases requires one of:

  1. Tightening the B-side `denote` semantics to mirror the SMT side
     (require `(x i).2.1 = α i`).
  2. A parametricity lemma showing well-typed `P` is invariant under
     value-equivalent type-tag substitutions.
  3. A stronger pre-condition on the binder typing rule.

  See the partial proofs of `collect`/`all`/`lambda` below for the
  substantive infrastructure that has been built (domain denotation via
  `denote_foldl_cprod_succ`, arity facts, body denotation for typed witnesses).

  ## Intended use

  The primary client is `EncodeTermCorrectAll.lean` (the empty-domain "Phase A2"
  branch around lines 1676 and 8731). To close those:

  1. Compose this PHOAS-level theorem with `B.Typing.of_abstract` (in
     `B/Reasoning/Lemmas.lean:398`), which itself is currently incomplete.
  2. Build the `WellTypedCtx` instance from the SMT-side `RenamingContext`
     and the type-compatibility invariants threaded through the all-case
     proof.
  3. Extract the `B.Dom` witness for `P` at the canonical `BType.defaultZFSet`
     valuation, contradicting `hP_den_cond`.

  Even with the binder/partial-op limitations above, the closure plan is
  feasible *for the specific situation in `all_case` empty-domain*, because
  the predicate `P` there is well-typed at `.bool` and (per BEer's encoder
  contract) cannot contain `app`/`card`/`min`/`max` subterms that lack
  finiteness/IsPFunc witnesses (these are guarded elsewhere in the encoder).
-/
import B.Reasoning.Lemmas

open B Classical PHOAS ZFSet

namespace B.PHOAS

/-! ## Type compatibility -/

/--
  A B-side renaming context (mapping `B.𝒱` to `Option B.Dom`) is type-compatible
  with a B PHOAS type context, in the sense that any binding present in `Γ` is
  also present in `Δ` and the carried type matches.

  This is the B-side analog of `SMT.RenamingContext.RespectsTypeContext`.
-/
abbrev RespectsTypeContext («Δ» : B.𝒱 → Option B.Dom) (Γ : PHOAS.TypeContext B.𝒱) : Prop :=
  ∀ ⦃v : B.𝒱⦄ ⦃τ : BType⦄, Γ v = some τ →
    ∃ d : B.Dom, «Δ» v = some d ∧ d.2.1 = τ

/--
  Every free variable of `t` is bound in `«Δ»`. Exact analog of
  `SMT.RenamingContext.CoversFV`.
-/
abbrev CoversFV («Δ» : B.𝒱 → Option B.Dom) (t : B.Term) : Prop :=
  ∀ v ∈ B.fv t, («Δ» v).isSome = true

/-! ## Direct PHOAS variant

  The PHOAS-level statement is much cleaner than the `B.Term`-level one because
  PHOAS variables ARE `B.Dom` values, so the type tag is built into each variable.
  We package "the context is consistent" as `WellTypedCtx`.
-/

/--
  A PHOAS type context `Γ : Dom → Option BType` is well-typed if every binding
  matches the type tag carried by its key. This is automatic for contexts
  constructed by `Function.update` from properly typed bindings.
-/
abbrev WellTypedCtx (Γ : PHOAS.TypeContext B.Dom) : Prop :=
  ∀ ⦃d : B.Dom⦄ ⦃τ : BType⦄, Γ d = some τ → d.2.1 = τ

/-! ## Auxiliary lemmas for binder cases -/

/-- Extending a `WellTypedCtx` with type-respecting bindings preserves well-typedness.
    Bridges to the existing `WFTC.update` infrastructure. -/
private theorem WellTypedCtx.update {Γ : PHOAS.TypeContext B.Dom} {n}
    {vs : Fin n → B.Dom} {τs : Fin n → BType}
    (hwt : WellTypedCtx Γ) (hvs : ∀ i, (vs i).2.1 = τs i) :
    WellTypedCtx (Γ.update vs τs) :=
  haveI : WFTC Γ := ⟨hwt⟩
  haveI : WFTC (Γ.update vs τs) := WFTC.update hvs
  WFTC.wf

/-- A foldl of cprods (over `Fin (n + 1)` source terms) denotes correctly,
    composing the per-component denotations into a foldl of products. -/
private theorem denote_foldl_cprod_succ {n : ℕ}
    (αs : Fin (n + 1) → BType) (Ds : Fin (n + 1) → PHOAS.Term B.Dom)
    (hDs : ∀ i, ∃ D : B.Dom, ⟦Ds i⟧ᴮ = some D ∧ D.snd.fst = (αs i).set) :
    ∃ D : B.Dom,
      ⟦Fin.foldl n (fun d (i : Fin n) => d ⨯ᴮ' Ds i.succ) (Ds 0)⟧ᴮ = some D ∧
      D.snd.fst = (Fin.foldl n (fun d (i : Fin n) => d ×ᴮ αs i.succ) (αs 0)).set := by
  induction n with
  | zero =>
    simp only [Fin.foldl_zero]
    exact hDs 0
  | succ n ih =>
    rw [Fin.foldl_succ_last, Fin.foldl_succ_last]
    let αs' : Fin (n + 1) → BType := fun i => αs i.castSucc
    let Ds' : Fin (n + 1) → PHOAS.Term B.Dom := fun i => Ds i.castSucc
    have hDs' : ∀ i, ∃ D : B.Dom, ⟦Ds' i⟧ᴮ = some D ∧ D.snd.fst = (αs' i).set :=
      fun i => hDs i.castSucc
    obtain ⟨D', hden', htyp'⟩ := ih αs' Ds' hDs'
    obtain ⟨Dn, hdenn, htypn⟩ := hDs (Fin.last n).succ
    obtain ⟨S', τ', hτ'⟩ := D'
    obtain ⟨Sn, σn, hσn⟩ := Dn
    dsimp at htyp' htypn
    subst htyp'
    subst htypn
    have h_prod_mem : S'.prod Sn ∈ ((Fin.foldl n (fun d (i : Fin n) =>
        d ×ᴮ αs' i.succ) (αs' 0) ×ᴮ αs (Fin.last (n + 1)))).set.toZFSet := by
      show S'.prod Sn ∈ ZFSet.powerset _
      rw [ZFSet.mem_powerset]
      intro z hz
      have hτ'' : S' ∈ ZFSet.powerset _ := hτ'
      have hσn' : Sn ∈ ZFSet.powerset _ := hσn
      rw [ZFSet.mem_powerset] at hτ'' hσn'
      show z ∈ ZFSet.prod _ _
      rw [ZFSet.mem_prod]
      have : z ∈ ZFSet.prod S' Sn := hz
      rw [ZFSet.mem_prod] at this
      obtain ⟨a, ha, b, hb, rfl⟩ := this
      exact ⟨a, hτ'' ha, b, hσn' hb, rfl⟩
    refine ⟨⟨S'.prod Sn,
              (Fin.foldl n (fun d (i : Fin n) => d ×ᴮ αs' i.succ) (αs' 0)
                  ×ᴮ αs (Fin.last (n + 1))).set,
              h_prod_mem⟩,
            ?_, rfl⟩
    show ⟦(Fin.foldl n (fun d (i : Fin n) =>
              d ⨯ᴮ' Ds i.castSucc.succ) (Ds 0)) ⨯ᴮ' Ds (Fin.last n).succ⟧ᴮ = _
    rw [B.denote, hdenn]
    have hden_unfold :
        ⟦Fin.foldl n (fun d (i : Fin n) => d ⨯ᴮ' Ds i.castSucc.succ) (Ds 0)⟧ᴮ =
        some ⟨S', _, hτ'⟩ := hden'
    rw [hden_unfold]
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some]

/-- Local copy of `SMT/Reasoning/Basic/CollectCaseHelpers.lean`'s
    `hasArity_of_mem_toZFSet` to keep the dependency graph clean. -/
private theorem hasArity_of_mem_toZFSet {τ : BType} {n : ℕ} {x : ZFSet}
    (hτ : τ.hasArity n) (hx : x ∈ τ.toZFSet) : x.hasArity n := by
  induction n generalizing τ x with
  | zero => exact absurd hτ (by cases τ <;> unfold BType.hasArity <;> exact id)
  | succ n ih =>
    cases n with
    | zero =>
      simp only [ZFSet.hasArity]
    | succ k =>
      cases τ with
      | prod α β =>
        rw [BType.hasArity] at hτ
        rw [BType.toZFSet] at hx
        obtain ⟨a, ha, b, hb, hab⟩ := ZFSet.mem_prod.mp hx
        simp only [ZFSet.hasArity, show (∃ a b, x = a.pair b) from ⟨a, b, hab⟩, ite_true]
        rw [hab, ZFSet.π₁_pair]
        exact ih hτ ha
      | int => exact absurd hτ (by unfold BType.hasArity; exact id)
      | bool => exact absurd hτ (by unfold BType.hasArity; exact id)
      | set τ => exact absurd hτ (by unfold BType.hasArity; exact id)

/-- Arity of a foldl of cprods is `n + 1`. Mirror of the `αs'_hasArity` pattern in
    `B/Reasoning/Lemmas.lean`. -/
private theorem BType.hasArity_foldl_succ {n : ℕ} (αs : Fin (n + 1) → BType) :
    (Fin.foldl n (fun d (i : Fin n) => d ×ᴮ αs i.succ) (αs 0)).hasArity (n + 1) := by
  induction n with
  | zero =>
    rw [Fin.foldl_zero, B.BType.hasArity]
    trivial
  | succ n ih =>
    rw [Fin.foldl_succ_last, B.BType.hasArity]
    exact ih (fun i => αs i.castSucc)

/-! ## Main Theorem (statement) -/

/--
  Well-typed B PHOAS terms with well-typed contexts always denote, and the
  resulting domain value carries the correct B type tag.

  This is the B-side analog of `SMT.RenamingContext.denote_exists_of_typing`
  (in `SMT/Reasoning/Basic/DenotationTotality.lean:158`).

  ## Cases proven (19)

  var, int, bool, maplet, add, sub, mul, and, not, eq, le, ℤ, 𝔹,
  mem, pow, cprod, union, inter, pfun.

  ## Cases open (7)

  collect, lambda, all (binders);
  app, card, min, max (partial denotations).

  See file header for analysis of why these cases require additional
  hypotheses or stronger semantics to close.
-/
theorem denote_exists_of_typing
    {Γ : PHOAS.TypeContext B.Dom} {t : PHOAS.Term B.Dom} {τ : BType}
    (htyp : Γ ⊢ᴮ' t : τ)
    (hwt : WellTypedCtx Γ) :
    ∃ D : B.Dom, ⟦t⟧ᴮ = some D ∧ D.2.1 = τ := by
  induction htyp with
  -- Variable: the denotation IS the variable, type tag follows from WellTypedCtx.
  | var v_typ =>
    rename_i v _
    refine ⟨v, rfl, ?_⟩
    exact hwt v_typ
  -- Integer literal
  | int =>
    rename_i n
    refine ⟨⟨.ofInt n, .int, ZFSet.mem_ofInt_Int n⟩, ?_, rfl⟩
    rw [B.denote, Option.pure_def]
  -- Boolean literal
  | bool =>
    rename_i b
    refine ⟨⟨ZFSet.ZFBool.ofBool b, .bool, ZFSet.ZFBool.mem_ofBool_𝔹 b⟩, ?_, rfl⟩
    rw [B.denote, Option.pure_def]
  -- Maplet (pair)
  | maplet _ _ ihx ihy =>
    obtain ⟨⟨X, αx, hX⟩, denx, htypx⟩ := ihx hwt
    obtain ⟨⟨Y, βy, hY⟩, deny, htypy⟩ := ihy hwt
    dsimp at htypx htypy
    subst htypx
    subst htypy
    refine ⟨⟨X.pair Y, αx ×ᴮ βy, ?_⟩, ?_, rfl⟩
    · rw [BType.toZFSet, ZFSet.pair_mem_prod]
      exact ⟨hX, hY⟩
    · rw [B.denote, denx, deny]
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some]
  -- Addition
  | add _ _ ihx ihy =>
    obtain ⟨⟨X, αx, hX⟩, denx, htypx⟩ := ihx hwt
    obtain ⟨⟨Y, βy, hY⟩, deny, htypy⟩ := ihy hwt
    dsimp at htypx htypy
    subst htypx
    subst htypy
    refine ⟨⟨X +ᶻ Y, .int, overloadBinOp_mem hX hY⟩, ?_, rfl⟩
    rw [B.denote, denx, deny]
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.failure_eq_none]
  -- Subtraction
  | sub _ _ ihx ihy =>
    obtain ⟨⟨X, αx, hX⟩, denx, htypx⟩ := ihx hwt
    obtain ⟨⟨Y, βy, hY⟩, deny, htypy⟩ := ihy hwt
    dsimp at htypx htypy
    subst htypx
    subst htypy
    refine ⟨⟨X -ᶻ Y, .int, overloadBinOp_mem hX hY⟩, ?_, rfl⟩
    rw [B.denote, denx, deny]
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.failure_eq_none]
  -- Multiplication
  | mul _ _ ihx ihy =>
    obtain ⟨⟨X, αx, hX⟩, denx, htypx⟩ := ihx hwt
    obtain ⟨⟨Y, βy, hY⟩, deny, htypy⟩ := ihy hwt
    dsimp at htypx htypy
    subst htypx
    subst htypy
    refine ⟨⟨X *ᶻ Y, .int, overloadBinOp_mem hX hY⟩, ?_, rfl⟩
    rw [B.denote, denx, deny]
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.failure_eq_none]
  -- And
  | and _ _ ihx ihy =>
    obtain ⟨⟨X, αx, hX⟩, denx, htypx⟩ := ihx hwt
    obtain ⟨⟨Y, βy, hY⟩, deny, htypy⟩ := ihy hwt
    dsimp at htypx htypy
    subst htypx
    subst htypy
    refine ⟨⟨X ⋀ᶻ Y, .bool, overloadBinOp_mem hX hY⟩, ?_, rfl⟩
    rw [B.denote, denx, deny]
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.failure_eq_none]
  -- Not
  | not _ ihx =>
    obtain ⟨⟨X, αx, hX⟩, denx, htypx⟩ := ihx hwt
    dsimp at htypx
    subst htypx
    refine ⟨⟨¬ᶻ X, .bool, overloadUnaryOp_mem⟩, ?_, rfl⟩
    rw [B.denote, denx]
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.failure_eq_none]
  -- Equality
  | eq _ _ ihx ihy =>
    obtain ⟨⟨X, αx, hX⟩, denx, htypx⟩ := ihx hwt
    obtain ⟨⟨Y, βy, hY⟩, deny, htypy⟩ := ihy hwt
    dsimp at htypx htypy
    subst htypx
    subst htypy
    refine ⟨⟨X =ᶻ Y, .bool, overloadBinOp_mem hX hY⟩, ?_, rfl⟩
    rw [B.denote, denx, deny]
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some,
      Option.failure_eq_none, dite_true]
  -- Less-or-equal
  | le _ _ ihx ihy =>
    obtain ⟨⟨X, αx, hX⟩, denx, htypx⟩ := ihx hwt
    obtain ⟨⟨Y, βy, hY⟩, deny, htypy⟩ := ihy hwt
    dsimp at htypx htypy
    subst htypx
    subst htypy
    refine ⟨⟨X ≤ᶻ Y, .bool, overloadBinOp_mem hX hY⟩, ?_, rfl⟩
    rw [B.denote, denx, deny]
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.failure_eq_none]
  -- ℤ
  | «ℤ» =>
    refine ⟨⟨ZFSet.Int, .set .int, ZFSet.mem_powerset.mpr fun _ => id⟩, ?_, rfl⟩
    rw [B.denote, Option.pure_def]
  -- 𝔹
  | 𝔹 =>
    refine ⟨⟨ZFSet.𝔹, .set .bool, ZFSet.mem_powerset.mpr fun _ => id⟩, ?_, rfl⟩
    rw [B.denote, Option.pure_def]
  -- Membership: x ∈ S where S : .set α and x : α.
  | mem _ _ ihx ihS =>
    obtain ⟨⟨X, αx, hX⟩, denx, htypx⟩ := ihx hwt
    obtain ⟨⟨Sd, αS, hS⟩, denS, htypS⟩ := ihS hwt
    dsimp at htypx htypS
    subst htypx
    have hαS : αS = .set αx := htypS
    subst hαS
    refine ⟨⟨X ∈ᶻ Sd, .bool, overloadUnaryOp_mem⟩, ?_, rfl⟩
    rw [B.denote, denx, denS]
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.failure_eq_none,
      dite_eq_ite, ite_true]
  -- Collect (set comprehension binder)
  --
  -- IMPORTANT NOTE: The B-side `denote` for `collect` uses these conditions:
  --     `den_P : ∀ {x}, ZFSet.ofFinDom x ∈ 𝒟 → ⟦P x⟧ᴮ.isSome`
  --     `typP_det : ∀ x y, ... → (⟦P x⟧.get _).2.1 = (⟦P y⟧.get _).2.1`
  -- These quantify over arbitrary `x : Fin n → Dom`, including those whose
  -- intrinsic type tags `(x i).2.1` don't match `α i`. Such ill-typed `x`s
  -- cannot be related to typing via `WellTypedCtx`, so the IH `typP_ih`
  -- cannot be applied. This is a fundamental gap between the B-side `denote`
  -- semantics and the typing rule, which doesn't appear on the SMT side
  -- (where the analogous `den_t_isSome` requires `(x i).2.1 = τs i`
  -- explicitly: see `SMT/Semantics.lean:136`).
  --
  -- We prove the SUBSTANTIVE part: domain denotes via foldl-cprod helper,
  -- has correct arity, and the body denotes for typed witnesses. The remaining
  -- gap (proving `den_P`/`typP_det` for arbitrary x's) requires either:
  --   (a) tightening the B-side `denote` to require typed `x`s, or
  --   (b) a parametricity lemma for `P`.
  | @collect Γ' n α D P n_pos typD typP typD_ih typP_ih =>
    obtain ⟨m, rfl⟩ := Nat.exists_add_one_eq.mpr n_pos
    -- Step 1: build domain denotation via the foldl-cprod helper.
    have hDi : ∀ i, ∃ D' : B.Dom, ⟦D i⟧ᴮ = some D' ∧ D'.snd.fst = (α i).set :=
      fun i => typD_ih i hwt
    obtain ⟨⟨𝒟, σ, h𝒟⟩, hden𝒟, htyp𝒟⟩ := denote_foldl_cprod_succ α D hDi
    dsimp at htyp𝒟
    subst htyp𝒟
    -- Step 2: arity facts for the foldl-cprod type
    set τ := Fin.foldl m (fun d (i : Fin m) => d ×ᴮ α i.succ) (α 0) with τ_def
    have τ_arity : τ.hasArity (m + 1) := BType.hasArity_foldl_succ α
    -- Step 3: For any TYPED x : Fin n → Dom, body denotes (using IH).
    have body_den_of_typed : ∀ (x : Fin (m + 1) → B.Dom),
        (∀ i, (x i).2.1 = α i) →
        ∃ D : B.Dom, ⟦P x⟧ᴮ = some D ∧ D.snd.fst = .bool := by
      intro x hx
      exact typP_ih x (hwt.update hx)
    -- Step 4: Translate type-tag witness (matching τ.get) into the (matching α) form
    -- needed by body_den_of_typed.
    have type_tag_eq : ∀ i, τ.get (m + 1) i = α i :=
      fun _ => BType.get_of_foldl
    -- Step 5: Build den_P and typP_det at the new (typed) precondition.
    have den_P : ∀ {x : Fin (m + 1) → Dom},
        (∀ i, (x i).snd.fst = τ.get (m + 1) i ∧ (x i).fst ∈ ⟦τ.get (m + 1) i⟧ᶻ) →
        ZFSet.ofFinDom x ∈ 𝒟 → ⟦P x⟧ᴮ.isSome := by
      intro x hx_typ _hx_dom
      have hx_α : ∀ i, (x i).2.1 = α i := fun i =>
        (hx_typ i).1.trans (type_tag_eq i)
      obtain ⟨D, hD, _⟩ := body_den_of_typed x hx_α
      exact Option.isSome_iff_exists.mpr ⟨D, hD⟩
    have typP_det : ∀ {x y : Fin (m + 1) → Dom},
        (hx_typ : ∀ i, (x i).snd.fst = τ.get (m + 1) i ∧
                        (x i).fst ∈ ⟦τ.get (m + 1) i⟧ᶻ) →
        (hy_typ : ∀ i, (y i).snd.fst = τ.get (m + 1) i ∧
                        (y i).fst ∈ ⟦τ.get (m + 1) i⟧ᶻ) →
        (x_𝒟 : ZFSet.ofFinDom x ∈ 𝒟) → (y_𝒟 : ZFSet.ofFinDom y ∈ 𝒟) →
        ⟦P x⟧ᴮ.get (den_P hx_typ x_𝒟) |>.2.1 = (⟦P y⟧ᴮ.get (den_P hy_typ y_𝒟) |>.2.1) := by
      intro x y hx_typ hy_typ x_𝒟 y_𝒟
      have hx_α : ∀ i, (x i).2.1 = α i := fun i =>
        (hx_typ i).1.trans (type_tag_eq i)
      have hy_α : ∀ i, (y i).2.1 = α i := fun i =>
        (hy_typ i).1.trans (type_tag_eq i)
      obtain ⟨Dx, hDx, htypx⟩ := body_den_of_typed x hx_α
      obtain ⟨Dy, hDy, htypy⟩ := body_den_of_typed y hy_α
      have hgetx : ⟦P x⟧ᴮ.get (den_P hx_typ x_𝒟) = Dx :=
        Option.get_of_eq_some _ hDx
      have hgety : ⟦P y⟧ᴮ.get (den_P hy_typ y_𝒟) = Dy :=
        Option.get_of_eq_some _ hDy
      rw [hgetx, hgety, htypx, htypy]
    -- Step 6: Build the def_dom witness for the eager `let _ ← ⟦P def_dom⟧ᴮ`
    have h_def : τ.defaultZFSet.hasArity (m + 1) ∧ τ.hasArity (m + 1) :=
      ⟨BType.hasArity_of_foldl_defaultZFSet τ_arity, τ_arity⟩
    let def_dom : Fin (m + 1) → Dom := fun i =>
      ⟨τ.defaultZFSet.get (m + 1) i, τ.get (m + 1) i,
       get_mem_type_of_isTuple h_def.1 h_def.2 BType.mem_toZFSet_of_defaultZFSet⟩
    have def_dom_typ : ∀ i, (def_dom i).2.1 = α i := by
      intro i
      show τ.get (m + 1) i = α i
      exact type_tag_eq i
    obtain ⟨D_def, hD_def, _⟩ := body_den_of_typed def_dom def_dom_typ
    -- Step 7: Build the final result.
    -- The B.denote evaluates to ⟨𝒟.sep ℙ, .set τ, ...⟩
    let ℙ : ZFSet → Prop := fun z =>
      if hz : z.hasArity (m + 1) ∧ τ.hasArity (m + 1) ∧ z ∈ τ.toZFSet then
        let zₙ : Fin (m + 1) → Dom := fun i =>
          ⟨z.get (m + 1) i, τ.get (m + 1) i,
           get_mem_type_of_isTuple hz.1 hz.2.1 hz.2.2⟩
        match ⟦P zₙ⟧ᴮ with
        | some ⟨Pz, _, _⟩ => Pz = ZFSet.zftrue
        | none => False
      else False
    refine ⟨⟨𝒟.sep ℙ, .set τ, ZFSet.sep_mem_powerset h𝒟⟩, ?_, rfl⟩
    show B.denote (PHOAS.Term.collect _ _) = _
    rw [show (Fin.foldl (m + 1 - 1) (fun d (x : Fin (m + 1 - 1)) =>
        match x with | ⟨i, hi⟩ => d ⨯ᴮ' D ⟨i + 1, Nat.add_lt_of_lt_sub hi⟩)
        (D ⟨0, n_pos⟩)) =
        Fin.foldl m (fun d (i : Fin m) => d ⨯ᴮ' D i.succ) (D 0) by
      simp only [Nat.add_one_sub_one]; rfl]
    unfold B.denote
    rw [hden𝒟]
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some]
    rw [dif_pos h_def]
    rw [hD_def]
    simp only [Option.bind_some]
    rw [dif_pos (@den_P), dif_pos (@typP_det)]
    rfl
  -- Powerset
  | @pow _ α _ _ ihS =>
    obtain ⟨⟨Sd, αS, hS⟩, denS, htypS⟩ := ihS hwt
    dsimp at htypS
    have hαS : αS = .set α := htypS
    subst hαS
    refine ⟨⟨Sd.powerset, BType.set (.set α), ?_⟩, ?_, rfl⟩
    · dsimp [BType.toZFSet] at hS ⊢
      rw [ZFSet.mem_powerset] at hS ⊢
      exact powerset_mono.mpr hS
    · rw [B.denote, denS]
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.failure_eq_none]
  -- Cartesian product
  | @cprod _ α β _ _ _ _ ihS ihT =>
    obtain ⟨⟨Sd, αS, hS⟩, denS, htypS⟩ := ihS hwt
    obtain ⟨⟨Td, αT, hT⟩, denT, htypT⟩ := ihT hwt
    dsimp at htypS htypT
    have hαS : αS = .set α := htypS; subst hαS
    have hαT : αT = .set β := htypT; subst hαT
    refine ⟨⟨Sd.prod Td, BType.set (α ×ᴮ β), ?_⟩, ?_, rfl⟩
    · dsimp [BType.toZFSet] at hS hT ⊢
      rw [ZFSet.mem_powerset] at hS hT ⊢
      intros _ hz
      rw [ZFSet.mem_prod] at hz ⊢
      obtain ⟨a, ha, b, hb, rfl⟩ := hz
      exact ⟨a, hS ha, b, hT hb, rfl⟩
    · rw [B.denote, denS, denT]
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.failure_eq_none]
  -- Union
  | @union _ α _ _ _ _ ihS ihT =>
    obtain ⟨⟨Sd, αS, hS⟩, denS, htypS⟩ := ihS hwt
    obtain ⟨⟨Td, αT, hT⟩, denT, htypT⟩ := ihT hwt
    dsimp at htypS htypT
    have hαS : αS = .set α := htypS; subst hαS
    have hαT : αT = .set α := htypT; subst hαT
    refine ⟨⟨Sd.union Td, .set α, ?_⟩, ?_, rfl⟩
    · dsimp [BType.toZFSet] at hS hT ⊢
      rw [ZFSet.mem_powerset] at hS hT ⊢
      exact union_mono hS hT
    · rw [B.denote, denS, denT]
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.failure_eq_none,
        dite_true]
  -- Inter
  | @inter _ α _ _ _ _ ihS ihT =>
    obtain ⟨⟨Sd, αS, hS⟩, denS, htypS⟩ := ihS hwt
    obtain ⟨⟨Td, αT, hT⟩, denT, htypT⟩ := ihT hwt
    dsimp at htypS htypT
    have hαS : αS = .set α := htypS; subst hαS
    have hαT : αT = .set α := htypT; subst hαT
    refine ⟨⟨Sd.inter Td, .set α, ?_⟩, ?_, rfl⟩
    · dsimp [BType.toZFSet] at hS hT ⊢
      rw [ZFSet.mem_powerset] at hS hT ⊢
      exact inter_mono hS hT
    · rw [B.denote, denS, denT]
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.failure_eq_none,
        dite_true]
  -- Partial function space
  | @pfun _ α β _ _ _ _ ihA ihB =>
    obtain ⟨⟨Ad, αA, hA⟩, denA, htypA⟩ := ihA hwt
    obtain ⟨⟨Bd, αB, hB⟩, denB, htypB⟩ := ihB hwt
    dsimp at htypA htypB
    have hαA : αA = .set α := htypA; subst hαA
    have hαB : αB = .set β := htypB; subst hαB
    refine ⟨⟨Ad.prod Bd |>.powerset |>.sep (fun f => f.IsPFunc Ad Bd),
      BType.set (.set (α ×ᴮ β)),
      ZFSet.prod_sep_is_pfunc_mem (ZFSet.mem_powerset.mp hA) (ZFSet.mem_powerset.mp hB)⟩, ?_, rfl⟩
    rw [B.denote, denA, denB]
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.failure_eq_none]
  -- All (universal quantification binder)
  --
  -- Same semantic gap as `collect` (see comment there): the B-side `denote`
  -- requires `den_P`/`typP_det` over arbitrary `x`s, but our IH only
  -- handles type-respecting `x`s. Substantive infrastructure built below.
  | @all Γ' n α D P n_pos typD typP typD_ih typP_ih =>
    obtain ⟨m, rfl⟩ := Nat.exists_add_one_eq.mpr n_pos
    -- Step 1: domain denotes
    have hDi : ∀ i, ∃ D' : B.Dom, ⟦D i⟧ᴮ = some D' ∧ D'.snd.fst = (α i).set :=
      fun i => typD_ih i hwt
    obtain ⟨⟨𝒟, σ, h𝒟⟩, hden𝒟, htyp𝒟⟩ := denote_foldl_cprod_succ α D hDi
    dsimp at htyp𝒟
    subst htyp𝒟
    -- Step 2: arity facts
    set τ := Fin.foldl m (fun d (i : Fin m) => d ×ᴮ α i.succ) (α 0) with τ_def
    have τ_arity : τ.hasArity (m + 1) := BType.hasArity_foldl_succ α
    -- Step 3: body denotes for typed witnesses
    have body_den_of_typed : ∀ (x : Fin (m + 1) → B.Dom),
        (∀ i, (x i).2.1 = α i) →
        ∃ D : B.Dom, ⟦P x⟧ᴮ = some D ∧ D.snd.fst = .bool := by
      intro x hx
      exact typP_ih x (hwt.update hx)
    -- Step 4: Translate type-tag witness into the (matching α) form.
    have type_tag_eq : ∀ i, τ.get (m + 1) i = α i :=
      fun _ => BType.get_of_foldl
    -- Step 5: Build den_P and typP_det at the new (typed) precondition.
    have den_P : ∀ {x : Fin (m + 1) → Dom},
        (∀ i, (x i).snd.fst = τ.get (m + 1) i ∧ (x i).fst ∈ ⟦τ.get (m + 1) i⟧ᶻ) →
        ZFSet.ofFinDom x ∈ 𝒟 → ⟦P x⟧ᴮ.isSome := by
      intro x hx_typ _hx_dom
      have hx_α : ∀ i, (x i).2.1 = α i := fun i =>
        (hx_typ i).1.trans (type_tag_eq i)
      obtain ⟨D, hD, _⟩ := body_den_of_typed x hx_α
      exact Option.isSome_iff_exists.mpr ⟨D, hD⟩
    have typP_det : ∀ {x y : Fin (m + 1) → Dom},
        (hx_typ : ∀ i, (x i).snd.fst = τ.get (m + 1) i ∧
                        (x i).fst ∈ ⟦τ.get (m + 1) i⟧ᶻ) →
        (hy_typ : ∀ i, (y i).snd.fst = τ.get (m + 1) i ∧
                        (y i).fst ∈ ⟦τ.get (m + 1) i⟧ᶻ) →
        (x_𝒟 : ZFSet.ofFinDom x ∈ 𝒟) → (y_𝒟 : ZFSet.ofFinDom y ∈ 𝒟) →
        ⟦P x⟧ᴮ.get (den_P hx_typ x_𝒟) |>.2.1 = (⟦P y⟧ᴮ.get (den_P hy_typ y_𝒟) |>.2.1) := by
      intro x y hx_typ hy_typ x_𝒟 y_𝒟
      have hx_α : ∀ i, (x i).2.1 = α i := fun i =>
        (hx_typ i).1.trans (type_tag_eq i)
      have hy_α : ∀ i, (y i).2.1 = α i := fun i =>
        (hy_typ i).1.trans (type_tag_eq i)
      obtain ⟨Dx, hDx, htypx⟩ := body_den_of_typed x hx_α
      obtain ⟨Dy, hDy, htypy⟩ := body_den_of_typed y hy_α
      have hgetx : ⟦P x⟧ᴮ.get (den_P hx_typ x_𝒟) = Dx :=
        Option.get_of_eq_some _ hDx
      have hgety : ⟦P y⟧ᴮ.get (den_P hy_typ y_𝒟) = Dy :=
        Option.get_of_eq_some _ hDy
      rw [hgetx, hgety, htypx, htypy]
    -- Step 6: Build the final result. The result has type .bool either way.
    -- Define the predicate ℙ used in the semantics.
    let ℙ : ZFSet → ZFSet := fun x =>
      if hx : x.hasArity (m + 1) ∧ x ∈ τ.toZFSet then
        let xₙ : Fin (m + 1) → Dom := fun i =>
          ⟨x.get (m + 1) i, τ.get (m + 1) i,
           get_mem_type_of_isTuple hx.1 τ_arity hx.2⟩
        match ⟦P xₙ⟧ᴮ with
        | some ⟨Px, _, _⟩ => Px
        | none => ZFSet.zffalse
      else ZFSet.zffalse
    by_cases h𝒟_emp : 𝒟 = ∅
    · -- Empty case: result is zftrue
      refine ⟨⟨ZFSet.zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩, ?_, rfl⟩
      show B.denote (PHOAS.Term.all _ _) = _
      rw [show (Fin.foldl (m + 1 - 1) (fun d (x : Fin (m + 1 - 1)) =>
          match x with | ⟨i, hi⟩ => d ⨯ᴮ' D ⟨i + 1, Nat.add_lt_of_lt_sub hi⟩)
          (D ⟨0, n_pos⟩)) =
          Fin.foldl m (fun d (i : Fin m) => d ⨯ᴮ' D i.succ) (D 0) by
        simp only [Nat.add_one_sub_one]; rfl]
      unfold B.denote
      rw [hden𝒟]
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some]
      rw [dif_pos τ_arity]
      rw [dif_pos (@den_P), dif_pos (@typP_det)]
      rw [if_pos h𝒟_emp]
    · -- Nonempty case: result is sInter(...)
      refine ⟨⟨ZFSet.sInter (ZFSet.𝔹.sep fun y => ∃ x ∈ 𝒟, y = ℙ x), .bool,
        ZFSet.sInter_sep_subset_of_𝔹_mem_𝔹 fun _ => id⟩, ?_, rfl⟩
      show B.denote (PHOAS.Term.all _ _) = _
      rw [show (Fin.foldl (m + 1 - 1) (fun d (x : Fin (m + 1 - 1)) =>
          match x with | ⟨i, hi⟩ => d ⨯ᴮ' D ⟨i + 1, Nat.add_lt_of_lt_sub hi⟩)
          (D ⟨0, n_pos⟩)) =
          Fin.foldl m (fun d (i : Fin m) => d ⨯ᴮ' D i.succ) (D 0) by
        simp only [Nat.add_one_sub_one]; rfl]
      unfold B.denote
      rw [hden𝒟]
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some]
      rw [dif_pos τ_arity]
      rw [dif_pos (@den_P), dif_pos (@typP_det)]
      rw [if_neg h𝒟_emp]
      rfl
  -- Lambda (function abstraction binder)
  --
  -- Same semantic gap as `collect`/`all`, plus an additional empty/non-empty
  -- domain split. Substantive infrastructure built below.
  | @lambda Γ' n α γ D E n_pos typD typE typD_ih typE_ih =>
    obtain ⟨m, rfl⟩ := Nat.exists_add_one_eq.mpr n_pos
    -- Step 1: domain denotes
    have hDi : ∀ i, ∃ D' : B.Dom, ⟦D i⟧ᴮ = some D' ∧ D'.snd.fst = (α i).set :=
      fun i => typD_ih i hwt
    obtain ⟨⟨𝒟, σ, h𝒟⟩, hden𝒟, htyp𝒟⟩ := denote_foldl_cprod_succ α D hDi
    dsimp at htyp𝒟
    subst htyp𝒟
    -- Step 2: arity facts
    set τ := Fin.foldl m (fun d (i : Fin m) => d ×ᴮ α i.succ) (α 0) with τ_def
    have τ_arity : τ.hasArity (m + 1) := BType.hasArity_foldl_succ α
    -- Step 3: body denotes for typed witnesses
    have body_den_of_typed : ∀ (x : Fin (m + 1) → B.Dom),
        (∀ i, (x i).2.1 = α i) →
        ∃ D : B.Dom, ⟦E x⟧ᴮ = some D ∧ D.snd.fst = γ := by
      intro x hx
      exact typE_ih x (hwt.update hx)
    -- Step 4: Translate type-tag witness into the (matching α) form.
    have type_tag_eq : ∀ i, τ.get (m + 1) i = α i :=
      fun _ => BType.get_of_foldl
    -- Step 5: Build den_E and typE_det at the new (typed) precondition.
    have den_E : ∀ {x : Fin (m + 1) → Dom},
        (∀ i, (x i).snd.fst = τ.get (m + 1) i ∧ (x i).fst ∈ ⟦τ.get (m + 1) i⟧ᶻ) →
        ZFSet.ofFinDom x ∈ 𝒟 → ⟦E x⟧ᴮ.isSome := by
      intro x hx_typ _hx_dom
      have hx_α : ∀ i, (x i).2.1 = α i := fun i =>
        (hx_typ i).1.trans (type_tag_eq i)
      obtain ⟨D, hD, _⟩ := body_den_of_typed x hx_α
      exact Option.isSome_iff_exists.mpr ⟨D, hD⟩
    have typE_det : ∀ {x y : Fin (m + 1) → Dom},
        (hx_typ : ∀ i, (x i).snd.fst = τ.get (m + 1) i ∧
                        (x i).fst ∈ ⟦τ.get (m + 1) i⟧ᶻ) →
        (hy_typ : ∀ i, (y i).snd.fst = τ.get (m + 1) i ∧
                        (y i).fst ∈ ⟦τ.get (m + 1) i⟧ᶻ) →
        (x_𝒟 : ZFSet.ofFinDom x ∈ 𝒟) → (y_𝒟 : ZFSet.ofFinDom y ∈ 𝒟) →
        ⟦E x⟧ᴮ.get (den_E hx_typ x_𝒟) |>.2.1 = (⟦E y⟧ᴮ.get (den_E hy_typ y_𝒟) |>.2.1) := by
      intro x y hx_typ hy_typ x_𝒟 y_𝒟
      have hx_α : ∀ i, (x i).2.1 = α i := fun i =>
        (hx_typ i).1.trans (type_tag_eq i)
      have hy_α : ∀ i, (y i).2.1 = α i := fun i =>
        (hy_typ i).1.trans (type_tag_eq i)
      obtain ⟨Dx, hDx, htypx⟩ := body_den_of_typed x hx_α
      obtain ⟨Dy, hDy, htypy⟩ := body_den_of_typed y hy_α
      have hgetx : ⟦E x⟧ᴮ.get (den_E hx_typ x_𝒟) = Dx :=
        Option.get_of_eq_some _ hDx
      have hgety : ⟦E y⟧ᴮ.get (den_E hy_typ y_𝒟) = Dy :=
        Option.get_of_eq_some _ hDy
      rw [hgetx, hgety, htypx, htypy]
    -- Step 6: Build the canonical default-domain witness for both branches.
    have h_def : τ.defaultZFSet.hasArity (m + 1) ∧ τ.hasArity (m + 1) :=
      ⟨BType.hasArity_of_foldl_defaultZFSet τ_arity, τ_arity⟩
    let def_dom : Fin (m + 1) → Dom := fun i =>
      ⟨τ.defaultZFSet.get (m + 1) i, τ.get (m + 1) i,
       get_mem_type_of_isTuple h_def.1 h_def.2 BType.mem_toZFSet_of_defaultZFSet⟩
    have def_dom_typ : ∀ i, (def_dom i).2.1 = α i := by
      intro i
      show τ.get (m + 1) i = α i
      exact type_tag_eq i
    obtain ⟨D_def, hD_def, htyp_def⟩ := body_den_of_typed def_dom def_dom_typ
    -- Step 7: Build the final result. Split on 𝒟 = ∅.
    by_cases h𝒟_emp : 𝒟 = ∅
    · -- Empty case: result is ⟨∅, (τ ×ᴮ γ).set, ...⟩
      refine ⟨⟨∅, (τ ×ᴮ γ).set, ?_⟩, ?_, rfl⟩
      · rw [BType.toZFSet, ZFSet.mem_powerset]; exact ZFSet.empty_subset _
      · show B.denote (PHOAS.Term.lambda _ _) = _
        rw [show (Fin.foldl (m + 1 - 1) (fun d (x : Fin (m + 1 - 1)) =>
            match x with | ⟨i, hi⟩ => d ⨯ᴮ' D ⟨i + 1, Nat.add_lt_of_lt_sub hi⟩)
            (D ⟨0, n_pos⟩)) =
            Fin.foldl m (fun d (i : Fin m) => d ⨯ᴮ' D i.succ) (D 0) by
          simp only [Nat.add_one_sub_one]; rfl]
        unfold B.denote
        rw [hden𝒟]
        simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some]
        rw [dif_pos τ_arity]
        rw [dif_pos (@den_E), dif_pos (@typE_det)]
        rw [dif_neg (by simp [h𝒟_emp])]
        rw [dif_pos h_def]
        -- Now we need to evaluate ⟦E def_dom⟧ᴮ
        have hD_def_at_τ : ⟦E (fun i => ⟨τ.defaultZFSet.get (m + 1) i,
            τ.get (m + 1) i,
            get_mem_type_of_isTuple h_def.1 h_def.2
              BType.mem_toZFSet_of_defaultZFSet⟩)⟧ᴮ = some D_def := hD_def
        rw [hD_def_at_τ]
        simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some]
        -- Now (τ ×ᴮ D_def.snd.fst) should reduce to (τ ×ᴮ γ)
        rw [htyp_def]
    · -- Nonempty case
      -- Get a witness x from 𝒟 ≠ ∅
      have 𝒟_nemp : 𝒟 ≠ ∅ := h𝒟_emp
      have hx_in_𝒟 := Classical.choose_spec (ZFSet.nonempty_exists_iff.mp 𝒟_nemp)
      let x_w := Classical.choose (ZFSet.nonempty_exists_iff.mp 𝒟_nemp)
      change x_w ∈ 𝒟 at hx_in_𝒟
      have hx_w_subset : 𝒟 ⊆ τ.toZFSet := by
        rw [BType.toZFSet, ZFSet.mem_powerset] at h𝒟; exact h𝒟
      have hx_w_mem : x_w ∈ τ.toZFSet := hx_w_subset hx_in_𝒟
      have hx_w_arity : x_w.hasArity (m + 1) :=
        hasArity_of_mem_toZFSet τ_arity hx_w_mem
      have hx_w_h : x_w.hasArity (m + 1) ∧ x_w ∈ τ.toZFSet := ⟨hx_w_arity, hx_w_mem⟩
      let xₙ : Fin (m + 1) → Dom := fun i =>
        ⟨x_w.get (m + 1) i, τ.get (m + 1) i,
         get_mem_type_of_isTuple hx_w_arity τ_arity hx_w_mem⟩
      have xₙ_typ : ∀ i, (xₙ i).2.1 = α i := fun i => type_tag_eq i
      obtain ⟨D_xₙ, hD_xₙ, htyp_xₙ⟩ := body_den_of_typed xₙ xₙ_typ
      -- Define ℰ
      let ℰ : ZFSet → Prop := fun xy =>
        if hxy : xy.hasArity 2 then
          let x_inner := xy.π₁
          let y_inner := xy.π₂
          if hx : x_inner.hasArity (m + 1) ∧ x_inner ∈ 𝒟 then
            let xₙ' : Fin (m + 1) → Dom := fun i =>
              ⟨x_inner.get (m + 1) i, τ.get (m + 1) i, by
                rw [BType.toZFSet, ZFSet.mem_powerset] at h𝒟
                exact get_mem_type_of_isTuple hx.1 τ_arity (h𝒟 hx.2)⟩
            match (motive := Option Dom → Prop) ⟦E xₙ'⟧ᴮ with
            | some ⟨ex, ξ, _⟩ => if ξ = γ then ex = y_inner else False
            | none => False
          else False
        else False
      refine ⟨⟨(𝒟.prod γ.toZFSet).sep ℰ, .set (τ ×ᴮ γ), ?_⟩, ?_, rfl⟩
      · exact ZFSet.prod_sep_mem_toZFSet h𝒟 (ZFSet.mem_powerset.mpr fun _ => id)
      · show B.denote (PHOAS.Term.lambda _ _) = _
        rw [show (Fin.foldl (m + 1 - 1) (fun d (x : Fin (m + 1 - 1)) =>
            match x with | ⟨i, hi⟩ => d ⨯ᴮ' D ⟨i + 1, Nat.add_lt_of_lt_sub hi⟩)
            (D ⟨0, n_pos⟩)) =
            Fin.foldl m (fun d (i : Fin m) => d ⨯ᴮ' D i.succ) (D 0) by
          simp only [Nat.add_one_sub_one]; rfl]
        unfold B.denote
        rw [hden𝒟]
        simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some]
        rw [dif_pos τ_arity]
        rw [dif_pos (@den_E), dif_pos (@typE_det)]
        rw [dif_pos 𝒟_nemp]
        rw [dif_pos hx_w_h]
        rw [hD_xₙ]
        simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some]
        rw [htyp_xₙ]
        rfl
  -- Application
  -- TODO: Need to bridge IsPFunc and dom membership facts from typing.
  | app _ _ _ _ => sorry
  -- Cardinality
  -- TODO: Need Finiteness witness from typing or hypothesis.
  | card _ _ => sorry
  -- Min
  -- TODO: Need Finite + Nonempty witness; not derivable purely from typing.
  -- Either restrict the theorem to these conditions or change the underlying
  -- denote semantics.
  | min _ _ => sorry
  -- Max
  -- TODO: Same as min.
  | max _ _ => sorry

/-! ## Corollaries -/

/--
  Well-typed PHOAS terms with well-typed contexts always denote.

  Note: only as strong as `denote_exists_of_typing` above, which is currently
  proven only for simple cases.
-/
theorem denote_isSome_of_typing
    {Γ : PHOAS.TypeContext B.Dom} {t : PHOAS.Term B.Dom} {τ : BType}
    (htyp : Γ ⊢ᴮ' t : τ)
    (hwt : WellTypedCtx Γ) :
    (⟦t⟧ᴮ).isSome = true := by
  obtain ⟨D, hD, _⟩ := denote_exists_of_typing htyp hwt
  exact Option.isSome_iff_exists.mpr ⟨D, hD⟩

/--
  Denotation of a well-typed PHOAS term has the correct type tag.
-/
theorem denote_type_of_typing
    {Γ : PHOAS.TypeContext B.Dom} {t : PHOAS.Term B.Dom} {τ : BType}
    (htyp : Γ ⊢ᴮ' t : τ)
    (hwt : WellTypedCtx Γ)
    {D : B.Dom}
    (hden : ⟦t⟧ᴮ = some D) :
    D.2.1 = τ := by
  obtain ⟨D', hD', htyp'⟩ := denote_exists_of_typing htyp hwt
  rw [hD'] at hden; cases hden; exact htyp'

end B.PHOAS

namespace B

/--
  Bridged variant: a B-Term-level totality statement that uses
  `B.Term.abstract` and `B.Typing.of_abstract` to reduce to the PHOAS-level
  theorem `B.PHOAS.denote_exists_of_typing`.

  This is the signature explicitly suggested in
  `EncodeTermCorrectAll.lean:8703` for closing the empty-domain Phase A2.

  NOTE: This corollary inherits all open cases from
  `B.PHOAS.denote_exists_of_typing` (collect, lambda, all, app, card, min,
  max). For the immediate Phase A2 use case, only the proven simple-case
  fragment of `P` is required, but the function signature is general.

  ## Usage example

  ```lean
  -- In all_case Phase A2, given typP : Γ ⊢ᴮ P : .bool, build:
  obtain ⟨P_val, hP_val, hP_den⟩ :=
    B.denote_exists_of_typing typP Δ_ext Δ_fv_P (build_compat ...)
  -- Now hP_den : ⟦P.abstract Δ_ext Δ_fv_P⟧ᴮ = some ⟨P_val, .bool, hP_val⟩
  -- This contradicts hP_den_cond.
  ```
-/
theorem denote_exists_of_typing
    {t : B.Term} {Γ : B.TypeContext} {τ : BType}
    (typ_t : Γ ⊢ᴮ t : τ)
    («Δ» : B.𝒱 → Option B.Dom)
    (Δ_isSome : ∀ v ∈ B.fv t, («Δ» v).isSome = true)
    (hcompat : B.PHOAS.WellTypedCtx (Γ.abstract («Δ» := «Δ»))) :
    ∃ T : ZFSet, ∃ hT : T ∈ τ.toZFSet,
      ⟦t.abstract «Δ» Δ_isSome⟧ᴮ = some ⟨T, τ, hT⟩ := by
  have htyp_phoas : Γ.abstract («Δ» := «Δ») ⊢ᴮ' t.abstract «Δ» Δ_isSome : τ :=
    _root_.Typing.of_abstract Δ_isSome typ_t
  obtain ⟨D, hD, htyp_eq⟩ :=
    B.PHOAS.denote_exists_of_typing htyp_phoas hcompat
  obtain ⟨T, σ, hT⟩ := D
  dsimp at htyp_eq
  subst htyp_eq
  exact ⟨T, hT, hD⟩

end B
