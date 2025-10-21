import SMT.Reasoning.Defs
import Std.Tactic.Do

set_option mvcgen.warning false

open Batteries Std.Do

theorem encode_type_context_subset (E : B.Env) :
  ⦃ λ _ ↦ ⌜True⌝ ⦄
  encodeTypeContext E
  ⦃ ⇓? () ⟨_, Γ⟩ => ⌜E.context.keys ⊆ Γ.keys⌝ ⦄ := by
  mintro pre
  unfold encodeTypeContext
  mvcgen

  case inv1 σ => exact ⇓? ⟨⟨pref, suff, eq⟩, ()⟩ ⟨E', Γ⟩ => ⌜pref.keys.Disjoint suff.keys ∧ pref.keys ⊆ Γ.keys⌝
  case vc1 _ pref cur suff eq _ fst _ _ snd _ inv ξ =>
    dsimp [ξ] at inv ⊢
    and_intros
    · intro v h
      rw [List.keys, List.mem_map] at h
      obtain ⟨⟨v, τ⟩, vτ_mem_pref_concat_cur, rfl⟩ := h
      rw [List.mem_append] at vτ_mem_pref_concat_cur
      rcases vτ_mem_pref_concat_cur with vτ_mem_pref | vτ_eq_cur
      · intro contr
        obtain ⟨disj, _⟩ := inv
        rw [List.disjoint_cons_right] at disj
        obtain ⟨_, disj⟩ := disj
        rw [List.disjoint_right] at disj
        nomatch disj contr <| List.mem_keys_of_mem vτ_mem_pref
      · intro contr
        have := List.NodupKeys.sublist (l₁ := cur :: suff) (List.sublist_append_right pref (cur :: suff)) <| eq ▸ E.context.nodupKeys
        rw [List.mem_singleton] at vτ_eq_cur
        subst cur
        rw [List.nodupKeys_cons] at this
        dsimp at this
        nomatch this.1 contr
    · rw [List.keys, List.map_append, List.map_singleton]
      rename EncoderState => σ
      obtain ⟨E', Γ⟩ := σ
      dsimp at inv ⊢
      rw [AList.keys_insert]
      intro z hz
      rw [List.mem_append, List.mem_singleton] at hz
      rcases hz with hz | rfl
      · rw [List.mem_cons, ←@not_not (z = _), ←imp_iff_not_or, ←ne_eq]
        intro z_neq
        refine (List.mem_erase_of_ne z_neq).mpr ?_
        apply inv.2 hz
      · exact List.mem_cons_self
  case vc6 => trivial
  case vc7 pref cur suff eq _ _ σ inv σ' =>
    dsimp [σ'] at inv ⊢
    and_intros
    · intro v h contr
      simp only [List.keys, List.map_append, List.map_cons, List.map_nil, List.mem_append,
        List.mem_map, Sigma.exists, exists_and_right, exists_eq_right, List.mem_cons,
        List.not_mem_nil, or_false] at h
      rcases h with ⟨τ, vτ_mem⟩ | rfl
      · obtain ⟨inv, _⟩ := inv
        rw [List.disjoint_cons_right] at inv
        exact inv.2 (List.mem_keys_of_mem vτ_mem) contr
      · have := List.NodupKeys.sublist (l₁ := cur :: suff) (List.sublist_append_right pref (cur :: suff)) <| eq ▸ E.context.nodupKeys
        rw [List.nodupKeys_cons] at this
        nomatch this.1 contr
    · rw [List.keys, List.map_append, List.map_singleton]
      rename EncoderState => σ
      obtain ⟨E', Γ⟩ := σ
      dsimp at inv ⊢
      rw [AList.keys_insert]
      intro z hz
      rw [List.mem_append, List.mem_singleton] at hz
      rcases hz with hz | rfl
      · rw [List.mem_cons, ←@not_not (z = _), ←imp_iff_not_or, ←ne_eq]
        intro z_neq
        refine (List.mem_erase_of_ne z_neq).mpr ?_
        apply inv.2 hz
      · exact List.mem_cons_self

  case vc8 σ => exact ⟨List.disjoint_nil_left _, List.nil_subset _⟩
  case vc9 h => exact And.casesOn h fun _ => id

  -- should not exist
  case vc2 => exact Encoder
  case vc3 => exact PostShape.arg EncoderState (PostShape.except String PostShape.pure)
  case vc4 => infer_instance
  case vc5 => infer_instance

theorem encode_type_context_keys_eq (E : B.Env) :
  ⦃ λ ⟨_, Γ⟩ ↦ ⌜Γ = ∅⌝ ⦄ encodeTypeContext E ⦃ ⇓? () ⟨_, Γ⟩ => ⌜E.context.keys = Γ.keys.reverse⌝ ⦄ := by
  unfold encodeTypeContext
  mvcgen
  case inv1 σ => exact ⇓? ⟨⟨pref, suff, eq⟩, ()⟩ ⟨E', Γ⟩ => ⌜pref.keys.Disjoint suff.keys ∧ pref.keys = Γ.keys.reverse⌝
  case vc1 pre cur suff eq _ _ _ _ _ σ inv ξ =>
    dsimp [ξ] at inv ⊢
    and_intros
    · rw [List.keys, List.map_append, List.disjoint_append_left, List.map_singleton, List.disjoint_cons_left]
      and_intros
      · exact List.disjoint_cons_right.mp inv.1 |>.2
      · have := List.NodupKeys.sublist (l₁ := cur :: suff) ?_ <| eq ▸ E.context.nodupKeys
        · rw [List.nodupKeys_cons] at this
          exact this.1
        · exact List.sublist_append_right pre (cur :: suff)
      · exact List.disjoint_nil_left (List.map Sigma.fst suff)
    · rw [List.keys, List.map_append, List.map_singleton, AList.keys_insert, List.reverse_cons, List.append_cancel_right_eq]
      rw [List.erase_of_not_mem]
      · exact inv.2
      · intro contr
        rw [←List.mem_reverse, ←inv.2] at contr
        nomatch List.disjoint_cons_right.mp inv.1 |>.1 contr
  case vc6 => trivial
  case vc7 pref cur suff eq _ _ _ inv ξ =>
    dsimp [ξ] at inv ⊢
    obtain ⟨pref_keys_disjoint, pref_keys_eq⟩ := inv
    and_intros
    · rw [List.keys, List.map_append, List.map_singleton, List.disjoint_append_left]
      and_intros
      · exact List.disjoint_of_disjoint_cons_right pref_keys_disjoint
      · have := List.NodupKeys.sublist (l₁ := cur :: suff) ?_ <| eq ▸ E.context.nodupKeys
        · rw [List.nodupKeys_cons] at this
          rw [List.disjoint_comm, List.disjoint_singleton]
          exact this.1
        · exact List.sublist_append_right pref (cur :: suff)
    · rw [List.keys, List.map_append, List.map_singleton, AList.keys_insert, List.reverse_cons, List.append_cancel_right_eq]
      rw [List.erase_of_not_mem]
      · exact pref_keys_eq
      · intro contr
        rw [←List.mem_reverse, ←pref_keys_eq] at contr
        nomatch List.disjoint_cons_right.mp pref_keys_disjoint |>.1 contr
  case vc8 pre =>
    dsimp
    rw [pre]
    exact ⟨List.disjoint_nil_left E.context.entries.keys, rfl⟩
  case vc9 inv =>
    rw [←inv.2]
    rfl
  -- should be inferred
  case vc2 =>
    exact Encoder
  case vc3 =>
    exact PostShape.arg EncoderState (PostShape.except String PostShape.pure)
  case vc4 =>
    infer_instance
  case vc5 =>
    infer_instance

@[spec]
theorem SMT.incrementFreshVarC_spec {n : ℕ} {Γ : TypeContext} :
  ⦃ λ ⟨E, Γ'⟩ ↦ ⌜E.freshvarsc = n ∧ Γ' = Γ ∧ n ≤ Γ'.keys.length⌝ ⦄
  SMT.incrementFreshVarC
  ⦃ ⇓ m ⟨E', Γ'⟩ => ⌜Γ' = Γ ∧ m + 1 = E'.freshvarsc ∧ m = n ∧ n ≤ Γ'.keys.length⌝ ⦄ := by
  unfold SMT.incrementFreshVarC
  mvcgen
  case vc1 S h E =>
    obtain ⟨rfl, rfl, hlen⟩ := h
    dsimp [E]
    and_intros
    · rfl
    · rfl
    · rfl
    · exact hlen

@[spec]
theorem SMT.freshVar_spec {Γ : TypeContext} {τ : SMTType} {name : String} {n : ℕ} :
  ⦃ λ ⟨E, Γ'⟩ ↦ ⌜Γ' = Γ ∧ E.freshvarsc = n ∧ n ≤ Γ.keys.length⌝⦄
  SMT.freshVar τ name
  ⦃ ⇓? v ⟨E', Γ'⟩ => ⌜Γ' = Γ.insert v τ ∧ v ∉ Γ ∧ E'.freshvarsc = n+1⌝ ⦄ := by
  unfold SMT.freshVar
  mstart
  mintro pre ∀S
  mpure pre
  obtain ⟨rfl, rfl, hlen⟩ := pre
  mspec SMT.incrementFreshVarC_spec (n := S.env.freshvarsc) (Γ := S.types)
  case post n =>
    mspec Std.Do.Spec.modifyGet_StateT
    mrename_i pre
    mintro ∀S'
    mpure pre
    obtain ⟨eq, inc_freshvarsc, rfl, hlen⟩ := pre
    split_ifs with h
    · mspec Std.Do.Spec.throw_StateT
    · mspec Std.Do.Spec.modifyGet_StateT
      mpure_intro

      set 𝓋 := (toString name ++ toString S.env.freshvarsc)
      have insert_eq : S'.types.insert 𝓋 τ = S.types.insert 𝓋 τ := by
        rw [eq]
      and_intros
      · exact insert_eq
      · rw [eq] at h
        intro contr
        contradiction
      · rw [←inc_freshvarsc]

@[spec]
theorem SMT.defineFun_spec {v : SMT.𝒱} {τ σ : SMTType} {d : Term} {decl : SMT.Chunk} {as : SMT.Stages} :
  ⦃ λ ⟨E, _⟩ ↦ ⌜E.declarations = decl ∧ E.asserts = as⌝ ⦄
  SMT.defineFun v τ σ d
  ⦃ ⇓ () ⟨E, _⟩ => ⌜E.declarations = (decl.concat <| .define_fun v τ σ d) ∧ E.asserts = as⌝ ⦄ := by
  unfold SMT.defineFun
  mvcgen
  case vc1 inv σ' =>
    obtain ⟨rfl, rfl⟩ := inv
    exact ⟨rfl, rfl⟩

@[spec]
theorem SMT.declareConst_spec {v : SMT.𝒱} {τ : SMTType} {decl : SMT.Chunk} {as : SMT.Stages}:
  ⦃ λ ⟨E, _⟩ ↦ ⌜E.declarations = decl ∧ E.asserts = as⌝ ⦄
  SMT.declareConst v τ
  ⦃ ⇓ () ⟨E, _⟩ => ⌜E.declarations = (decl.concat <| .declare_const v τ) ∧ E.asserts = as⌝ ⦄ := by
  unfold SMT.declareConst
  mvcgen
  case vc1 inv σ' =>
    obtain ⟨rfl, rfl⟩ := inv
    exact ⟨rfl, rfl⟩

@[spec]
theorem SMT.addAssert_spec_total {t : Term} {as : SMT.Stages} :
  ⦃λ ⟨E, _⟩ ↦ ⌜(∀ is, E.asserts ≠ .instr is) ∧ E.asserts = as⌝⦄
  SMT.addAssert t
  ⦃ ⇓ () ⟨E, _⟩ => ⌜E.asserts = addAssertAux as [.assert t]⌝⦄ := by
  unfold SMT.addAssert
  mintro pre
  mspec Std.Do.Spec.get_StateT
  mintro ∀ σ
  intro ⟨pre, rfl⟩
  split using eq | eq
  · exact pre _ eq
  · mstart
    mspec Std.Do.Spec.modifyGet_StateT
    mpure_intro
    rw [eq]

@[spec]
theorem SMT.addAssert_spec {t : Term} {decl : SMT.Chunk} {as : SMT.Stages} :
  ⦃λ ⟨E, _⟩ ↦ ⌜E.declarations = decl ∧ E.asserts = as⌝⦄
  SMT.addAssert t
  ⦃ ⇓? () ⟨E, _⟩ => ⌜E.declarations = decl ∧ E.asserts = addAssertAux as [.assert t]⌝⦄ := by
  unfold SMT.addAssert
  mvcgen
  case vc1 pre _ inv σ' =>
    and_intros
    · rw [←pre.1]
    · rw [←pre.2, inv]

@[spec]
theorem SMT.addSpec_spec {x! : SMT.𝒱} {x!_spec : Term} {decl : SMT.Chunk} {as : SMT.Stages} :
  ⦃ λ ⟨E, _⟩ ↦ ⌜E.declarations = decl ∧ E.asserts = as⌝ ⦄
  SMT.addSpec x! x!_spec
  ⦃ ⇓? () ⟨E, _⟩ => ⌜
    E.declarations = (decl.concat <| .define_fun s!"{x!}_spec" .unit .bool x!_spec) ∧
    E.asserts = addAssertAux as [.assert <| .var s!"{x!}_spec"]⌝⦄ := by
  unfold SMT.addSpec
  mstart
  mintro pre
  mintro ∀σ
  mpure pre
  obtain ⟨rfl, rfl⟩ := pre
  mspec SMT.defineFun_spec
  mintro ∀σ
  mspec SMT.addAssert_spec

@[spec]
theorem SMT.Term.getType_spec {Γ : TypeContext} {t : Term} {α : SMTType} (typ_t : Γ ⊢ t : α):
  ⦃ λ ⟨_, Γ'⟩ ↦ ⌜Γ' = Γ⌝ ⦄
  t.getType
  ⦃ ⇓? τ ⟨_, Γ'⟩ => ⌜Γ' = Γ ∧ τ = α⌝ ⦄ := by
  induction t using Term.rec' generalizing Γ α with
  | var v =>
    mintro pre ∀σ
    obtain ⟨E, Γ⟩ := σ
    intro h
    mstart
    unfold getType
    mvcgen
    apply Typing.varE at typ_t
    rw [h, typ_t, Option.get!_some]
    exact ⟨rfl, rfl⟩
  | int n =>
    mintro pre ∀σ
    obtain ⟨E, Γ⟩ := σ
    rintro rfl
    mstart
    unfold getType
    mvcgen
    obtain rfl := Typing.intE typ_t
    exact ⟨trivial, rfl⟩
  | bool b =>
    mintro pre ∀σ
    obtain ⟨E, Γ⟩ := σ
    rintro rfl
    mstart
    unfold getType
    mvcgen
    obtain rfl := Typing.boolE typ_t
    exact ⟨trivial, rfl⟩
  | app f x ihf ihx =>
    apply Typing.appE at typ_t
    obtain ⟨β, typ_f, typ_x⟩ := typ_t

    mstart
    mintro pre ∀σ₀
    mpure pre
    subst Γ
    unfold getType
    mspec ihf typ_f
    mrename_i pre
    mintro ∀σ₁
    mpure pre
    obtain ⟨pre, rfl⟩ := pre
    mspec ihx typ_x

    mrename_i pre
    mintro ∀σ₂
    mpure pre
    obtain ⟨pre, rfl⟩ := pre
    mvcgen
  | as t τ ih =>
    apply Typing.asE at typ_t
    obtain ⟨rfl, rfl, τ, rfl⟩ := typ_t

    mstart
    mintro pre ∀σ₁
    rintro ⟨⟩
    mstart
    mspec Std.Do.Spec.pure
  | eq t₁ t₂ _ _ =>
    apply Typing.eqE at typ_t
    obtain ⟨rfl, σ, typ_t₁, typ_t₂⟩ := typ_t
    mstart
    mintro pre ∀σ₀
    unfold getType
    mspec
  | and t₁ t₂ _ _ =>
    apply Typing.andE at typ_t
    obtain ⟨rfl, typ_t₁, typ_t₂⟩ := typ_t

    mstart
    mintro pre ∀σ₀
    unfold getType
    mspec
  | or t₁ t₂ _ _ =>
    apply Typing.orE at typ_t
    obtain ⟨rfl, typ_t₁, typ_t₂⟩ := typ_t

    mstart
    mintro pre ∀σ₀
    unfold getType
    mspec
  | not t _ =>
    apply Typing.notE at typ_t
    obtain ⟨rfl, typ_t⟩ := typ_t

    mstart
    mintro pre ∀σ₀
    unfold getType
    mspec
  | imp t₁ t₂ _ _ =>
    apply Typing.impE at typ_t
    obtain ⟨rfl, typ_t₁, typ_t₂⟩ := typ_t

    mstart
    mintro pre ∀σ₀
    unfold getType
    mspec
  | ite c t e ihc iht ihe =>
    apply Typing.iteE at typ_t
    obtain ⟨typ_c, typ_t, typ_e⟩ := typ_t

    mstart
    mintro pre ∀σ₀
    unfold getType
    mspec iht typ_t
  | some t ih =>
    apply Typing.someE at typ_t
    obtain ⟨τ, rfl, typ_t⟩ := typ_t

    mstart
    mintro pre ∀σ₀
    unfold getType
    mspec ih typ_t

    mrename_i pre
    mintro ∀σ₁
    mpure pre
    obtain ⟨pre, rfl⟩ := pre
    mspec
  | the t ih =>
    apply Typing.theE at typ_t

    mstart
    mintro pre ∀σ₀
    mpure pre
    subst Γ
    unfold getType
    mspec ih typ_t
    mintro ∀σ₁
    mrename_i pre
    mpure pre
    obtain ⟨pre, rfl⟩ := pre
    conv =>
      enter [2,1,1]
      dsimp
    mspec
  | pair t₁ t₂ iht₁ iht₂ =>
    apply Typing.pairE at typ_t
    obtain ⟨α, β, rfl, typ_t₁, typ_t₂⟩ := typ_t

    mstart
    mintro pre ∀σ₀
    mpure pre
    subst Γ
    unfold getType
    mspec iht₁ typ_t₁
    mrename_i pre
    mintro ∀σ₁
    mpure pre
    obtain ⟨pre, rfl⟩ := pre
    mspec iht₂ typ_t₂
    mintro ∀σ₂
    mrename_i pre
    mpure pre
    obtain ⟨pre, rfl⟩ := pre
    mspec
  | none => nomatch Typing.noneE typ_t
  | fst t ih
  | snd t ih =>
    first
    | apply Typing.fstE at typ_t
    | apply Typing.sndE at typ_t
    obtain ⟨σ, typ_t⟩ := typ_t

    mstart
    mintro pre ∀σ₀
    mpure pre
    subst Γ
    unfold getType
    mspec ih typ_t
    mintro ∀σ₁
    mrename_i pre
    mpure pre
    obtain ⟨pre, rfl⟩ := pre
    conv =>
      enter [2,1,1]
      dsimp
    mspec
  | distinct ts ih
  | le t₁ t₂ _ _
  | add t₁ t₂ _ _
  | sub t₁ t₂ _ _
  | mul t₁ t₂ _ _ =>
    first
    | apply Typing.distinctE at typ_t
    | apply Typing.leE at typ_t
    | apply Typing.addE at typ_t
    | apply Typing.subE at typ_t
    | apply Typing.mulE at typ_t
    obtain ⟨rfl, typ_t₁, typ_t₂⟩ := typ_t

    mstart
    mintro pre ∀σ₀
    unfold getType
    mspec
  | lambda vs τs f ih =>
    apply Typing.lambdaE at typ_t
    obtain ⟨len_pos, len_eq, γ, vs_Γ_disj, rfl, typ_f⟩ := typ_t

    mstart
    mintro pre ∀σ₀
    mpure pre
    subst Γ
    unfold getType
    conv =>
      enter [2,1,1]
      rw [dite_cond_eq_true (eq_true len_eq)]
    mspec Std.Do.Spec.get_StateT
    mspec Std.Do.Spec.modifyGet_StateT
    mspec ih typ_f

    mintro ∀σ₁
    mrename_i pre
    mpure pre
    obtain ⟨pre, ⟨⟩⟩ := pre

    split <;> mspec
  | «forall» vs τs t
  | «exists» v τs t =>
    first
    | apply Typing.forallE at typ_t
    | apply Typing.existsE at typ_t
    obtain ⟨rfl, vs_Γ_disj, len_pos, len_eq, typ_t⟩ := typ_t
    mstart
    mintro pre ∀σ₀
    unfold getType
    mspec

section encodeTerm_correct
open B SMT ZFSet

theorem encodeTerm_spec.ℤ.{u_1} {Λ : SMT.TypeContext} {n : ℕ} (E : B.Env) {α : BType}
  (typ_t : E.context ⊢ .ℤ : α) {«Δ» : B.𝒱 → Option B.Dom} (Δ_fv : ∀ v ∈ B.fv Term.ℤ, («Δ» v).isSome = true)
  {T : ZFSet.{u_1}} {hT : T ∈ ⟦α⟧ᶻ} (den_t : ⟦Term.ℤ.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, α, hT⟩) :
  ⦃fun ⟨E, Λ'⟩ ↦ ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ n ≤  Λ'.keys.length⌝⦄
    encodeTerm .ℤ E
  ⦃⇓? ⟨t', σ⟩ ⟨E', Γ'⟩ =>
    ⌜n ≤ E'.freshvarsc ∧ E'.freshvarsc ≤ Γ'.keys.length ∧ Γ' = Λ ∧
    σ = α.toSMTType ∧ Γ' ⊢ t' : σ ∧
    ∃ (hΔ : ∀ v ∈ SMT.fv t', (RenamingContext.toSMT «Δ» v).isSome = true),
      ∃ denT', ⟦t'.abstract (RenamingContext.toSMT «Δ») hΔ⟧ˢ = some denT' ∧ ⟨T, α, hT⟩ ≘ᶻ denT'⌝⦄ := by
  mstart
  mintro pre ∀S
  mpure pre
  obtain ⟨rfl, rfl, hlen⟩ := pre

  rw [encodeTerm]

  rw [B.Term.abstract, B.denote, Option.pure_def, Option.some_inj] at den_t
  injection den_t with T_eq heq
  subst T_eq
  injection heq with α_eq heq
  subst α_eq
  clear heq

  mspec Std.Do.Spec.get_StateT
  mspec freshVar_spec
  case post.success 𝓋 =>
    mrename_i pre
    mintro ∀S'
    mpure pre
    obtain ⟨types_eq, 𝓋_notMem, freshvarsc_eq⟩ := pre
    mspec Std.Do.Spec.modifyGet_StateT
    mspec Std.Do.Spec.pure
    mpure_intro
    and_intros
    · rw [freshvarsc_eq]
      apply Nat.le_refl
    · rw [freshvarsc_eq]
      exact hlen
    · trivial
    · rfl
    · apply SMT.Typing.lambda
      · intro _ h
        rw [List.mem_singleton] at h
        obtain ⟨⟩ := h
        exact 𝓋_notMem
      · apply Nat.zero_lt_succ
      · apply SMT.Typing.bool
      · rfl
    · exists ?_
      · intro v hv
        simp only [SMT.fv, List.mem_removeAll_iff] at hv
        nomatch hv.1
      · exists ⟨
          λᶻ: Int → 𝔹
            |   z ↦ zftrue,
          .fun .int .bool,
          ?_⟩
        · exact mem_funs_of_lambda fun _ ↦ ZFBool.zftrue_mem_𝔹
        · and_intros
          · rw [SMT.Term.abstract, dite_cond_eq_true (eq_true (by rfl))]
            simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Fin.val_eq_zero, List.getElem_cons_zero, SMT.Term.abstract.go, List.length_nil, List.length_cons, Nat.reduceAdd,
              Matrix.head_fin_const, SMT.Term.abstract]
            simp only [Function.OfArity.uncurry, Function.FromTypes.uncurry, Nat.reduceAdd]
            simp only [SMT.denote, gt_iff_lt, Nat.lt_add_one, ↓reduceDIte, mem_union, mem_prod, mem_singleton, exists_eq_left, Option.pure_def, Option.isSome_some, implies_true, Option.get_some, Nat.add_one_sub_one, Fin.zero_eta, Fin.isValue, ZFSet.get, get.eq_1, dite_eq_ite, Nat.sub_self, Fin.foldr_zero, Option.some.injEq]
            congr 1
            · rw [Fin.foldr_zero]
              simp only [hasArity, mem_union, mem_prod, mem_singleton,
                exists_eq_left, forall_const, true_and, SMTType.toZFSet]
              rw [ZFSet.lambda_ext_iff]
              · intro z hz
                split_ifs with h
                · rfl
                · rw [forall_const, true_and] at h
                  nomatch h hz
              · intro x hx
                split_ifs with h
                · exact ZFBool.mem_ofBool_𝔹 true
                · rw [forall_const, true_and] at h
                  nomatch h hx
            · congr 1
              · funext τ
                rw [Fin.foldr_zero]
                simp only [SMTType.toZFSet, hasArity, mem_union, mem_prod, mem_singleton, exists_eq_left, forall_const, true_and, eq_iff_iff]

                apply (Eq.to_iff <| congrArg (· ∈ ⟦τ⟧ᶻ) ·) --NOTE: engineering workaround
                rw [ZFSet.lambda_ext_iff]
                intro z hz
                split_ifs with h
                · rfl
                · rw [forall_const, true_and] at h
                  nomatch h hz
                · intro x hx
                  split_ifs with h
                  · exact ZFBool.mem_ofBool_𝔹 true
                  · rw [forall_const, true_and] at h
                    nomatch h hx
              · apply proof_irrel_heq
          · rfl
          · rw [retract]
            dsimp
            ext1 z
            iff_intro hz hz
            · rw [ZFSet.mem_sep] at hz
              obtain ⟨mem_int, _⟩ := hz
              exact mem_int
            · rw [ZFSet.mem_sep]
              apply And.intro hz
              simp only [BType.toZFSet, dite_cond_eq_true (eq_true hz)]
              rw [dite_cond_eq_true (eq_true ?_)]
              · rw [fapply_lambda (fun _ ↦ ZFBool.zftrue_mem_𝔹) (fapply_mem_range _ _)]
              · exact lambda_isFunc fun _ ↦ ZFBool.zftrue_mem_𝔹

theorem encodeTerm_spec.𝔹.{u_1} {Λ : SMT.TypeContext} {n : ℕ} (E : B.Env) {α : BType}
  (typ_t : E.context ⊢ .𝔹 : α) {«Δ» : B.𝒱 → Option B.Dom} (Δ_fv : ∀ v ∈ B.fv Term.𝔹, («Δ» v).isSome = true)
  {T : ZFSet.{u_1}} {hT : T ∈ ⟦α⟧ᶻ} (den_t : ⟦Term.𝔹.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩) :
  ⦃fun ⟨E, Λ'⟩ ↦ ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ n ≤  Λ'.keys.length⌝⦄
    encodeTerm Term.𝔹 E
  ⦃⇓? ⟨t', σ⟩ ⟨E', Γ'⟩ =>
    ⌜n ≤ E'.freshvarsc ∧ E'.freshvarsc ≤ Γ'.keys.length ∧ Γ' = Λ ∧
    σ = α.toSMTType ∧
    Γ' ⊢ t' : σ ∧
    ∃ (hΔ : ∀ v ∈ SMT.fv t', (RenamingContext.toSMT «Δ» v).isSome = true),
      ∃ denT',
        ⟦t'.abstract (RenamingContext.toSMT «Δ») hΔ⟧ˢ = some denT' ∧ ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT'⌝⦄ := by
  mstart
  mintro pre ∀S
  mpure pre
  obtain ⟨rfl, rfl, hlen⟩ := pre

  rw [encodeTerm]

  rw [B.Term.abstract, B.denote, Option.pure_def, Option.some_inj] at den_t
  injection den_t with T_eq heq
  subst T_eq
  injection heq with α_eq heq
  subst α_eq
  clear heq

  mspec Std.Do.Spec.get_StateT
  mspec freshVar_spec
  case post.success 𝓋 =>
    mrename_i pre
    mintro ∀S'
    mpure pre
    obtain ⟨types_eq, 𝓋_notMem, freshvarsc_eq⟩ := pre
    mspec Std.Do.Spec.modifyGet_StateT
    mspec Std.Do.Spec.pure
    mpure_intro
    and_intros
    · rw [freshvarsc_eq]
      apply Nat.le_refl
    · rw [freshvarsc_eq]
      exact hlen
    · trivial
    · rfl
    · apply SMT.Typing.lambda
      · intro _ h
        rw [List.mem_singleton] at h
        obtain ⟨⟩ := h
        exact 𝓋_notMem
      · apply Nat.zero_lt_succ
      · apply SMT.Typing.bool
      · rfl
    · exists ?_
      · intro v hv
        simp only [SMT.fv, List.mem_removeAll_iff] at hv
        nomatch hv.1
      · exists ⟨
          λᶻ: .𝔹 → .𝔹
            |   z ↦ zftrue,
          .fun .bool .bool,
          ?_⟩
        · exact mem_funs_of_lambda fun _ ↦ ZFBool.zftrue_mem_𝔹
        · and_intros
          · rw [SMT.Term.abstract, dite_cond_eq_true (eq_true (by rfl))]
            simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Fin.val_eq_zero, List.getElem_cons_zero, SMT.Term.abstract.go, List.length_nil, List.length_cons, Nat.reduceAdd,
              Matrix.head_fin_const, SMT.Term.abstract]
            simp only [Function.OfArity.uncurry, Function.FromTypes.uncurry, Nat.reduceAdd]
            simp only [SMT.denote, gt_iff_lt, Nat.lt_add_one, ↓reduceDIte, mem_insert_iff,
              subset_refl, subset_of_empty, mem_singleton, Option.pure_def, Option.isSome_some,
              implies_true, Option.get_some, Nat.add_one_sub_one, Fin.zero_eta, Fin.isValue,
              ZFSet.get, dite_eq_ite, Nat.sub_self, Fin.foldr_zero,
              Option.some.injEq]
            congr 1
            · rw [Fin.foldr_zero]
              simp only [SMTType.toZFSet, hasArity, forall_const, true_and]
              rw [ZFSet.lambda_ext_iff]
              · intro z hz
                split_ifs with h
                · rfl
                · rw [forall_const, true_and] at h
                  nomatch h hz
              · intro x hx
                split_ifs with h
                · exact ZFBool.mem_ofBool_𝔹 true
                · rw [forall_const, true_and] at h
                  nomatch h hx
            · congr 1
              · funext τ
                rw [Fin.foldr_zero]
                simp only [SMTType.toZFSet, hasArity, forall_const, true_and, eq_iff_iff]
                apply (Eq.to_iff <| congrArg (· ∈ ⟦τ⟧ᶻ) ·) --NOTE: engineering workaround
                rw [ZFSet.lambda_ext_iff]
                intro z hz
                split_ifs with h
                · rfl
                · rw [forall_const, true_and] at h
                  nomatch h hz
                · intro x hx
                  split_ifs with h
                  · exact ZFBool.mem_ofBool_𝔹 true
                  · rw [forall_const, true_and] at h
                    nomatch h hx
              · apply proof_irrel_heq
          · rfl
          · rw [retract]
            dsimp
            ext1 z
            iff_intro hz hz
            · rw [ZFSet.mem_sep] at hz
              obtain ⟨mem_int, _⟩ := hz
              exact mem_int
            · rw [ZFSet.mem_sep]
              apply And.intro hz
              simp only [BType.toZFSet, dite_cond_eq_true (eq_true hz)]
              rw [dite_cond_eq_true (eq_true ?_)]
              · rw [fapply_lambda (fun _ ↦ ZFBool.zftrue_mem_𝔹) (fapply_mem_range _ _)]
              · exact lambda_isFunc fun _ ↦ ZFBool.zftrue_mem_𝔹

theorem encodeTerm_spec.var.{u_1} {Λ : SMT.TypeContext} {n : ℕ} (v : B.𝒱) (E : B.Env) {α : BType}
  (typ_t : E.context ⊢ .var v : α) {«Δ» : B.𝒱 → Option B.Dom}
  (Δ_fv : ∀ v_1 ∈ B.fv (B.Term.var v), («Δ» v_1).isSome = true) {T : ZFSet.{u_1}} {hT : T ∈ ⟦α⟧ᶻ}
  (den_t : ⟦(B.Term.var v).abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, α, hT⟩) :
  ⦃fun ⟨E, Λ'⟩ ↦ ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ n ≤  Λ'.keys.length⌝⦄
    encodeTerm (.var v) E
  ⦃⇓? ⟨t', σ⟩ ⟨E', Γ'⟩ =>
    ⌜n ≤ E'.freshvarsc ∧ E'.freshvarsc ≤  Γ'.keys.length ∧
      Γ' = Λ ∧ σ = α.toSMTType ∧ Γ' ⊢ t' : σ ∧
      ∃ (hΔ : ∀ v ∈ SMT.fv t', (RenamingContext.toSMT «Δ» v).isSome = true),
      ∃ denT',
        ⟦t'.abstract (RenamingContext.toSMT «Δ») hΔ⟧ˢ = some denT' ∧ ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT'⌝⦄ := by
  mstart
  mintro pre ∀S
  mpure pre
  obtain ⟨rfl, rfl, hlen⟩ := pre

  rw [encodeTerm]
  mvcgen
  case vc1 τ' typ_t_enc τ typ_t τ'_eq =>
    subst τ'

    and_intros
    · apply Nat.le_refl
    · exact hlen
    · trivial
    · congr
      have τ_eq := @denote_welltyped_eq ((B.Term.var v).abstract «Δ» Δ_fv) T α hT ?_ den_t
      on_goal 2 =>
        unfold WellTyped'
        use E.context.abstract («Δ» := «Δ»), WFTC.of_abstract, τ
        exact @Typing.of_abstract (B.Dom) («Δ» := «Δ») ?_ (.var v) E.context τ Δ_fv (B.Typing.var typ_t)
      exact τ_eq
    · apply SMT.Typing.var
      exact typ_t_enc
    · rw [B.Term.abstract, B.denote, Option.pure_def, Option.some_get] at den_t
      have hΔ : ∀ v' ∈ SMT.fv (.var v), (RenamingContext.toSMT «Δ» v').isSome = true := by
        intro _ hv
        rw [SMT.fv, List.mem_singleton, eq_comm] at hv
        subst hv
        simp only [RenamingContext.toSMT, den_t, Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.isSome_some]

      set den₁ := RenamingContext.toSMT «Δ» v with den₁_def
      simp only [RenamingContext.toSMT, Option.pure_def, Option.bind_eq_bind] at den₁_def
      rw [den_t, Option.bind_some] at den₁_def

      use hΔ, den₁.get (Option.isSome_of_mem den₁_def)
      · unfold den₁ at den₁_def
        conv =>
          enter [1]
          change ?den_var
          conv =>
            enter [2]
            unfold den₁
            rw [Option.some_get, den₁_def]
          rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some_get, den₁_def, Option.some_inj, eq_self]
        rw [true_and]
        conv =>
          enter [2,1]
          unfold den₁
          rw [den₁_def]
        and_intros
        · rfl
        · exact retract_of_canonical α hT rfl

theorem encodeTerm_spec.int.{u_1} {Λ : SMT.TypeContext} {n_1 : ℕ} (n : ℤ) (E : B.Env) {α : BType}
  (typ_t : E.context ⊢ B.Term.int n : α) {«Δ» : B.𝒱 → Option B.Dom}
  (Δ_fv : ∀ v ∈ B.fv (B.Term.int n), («Δ» v).isSome = true) {T : ZFSet.{u_1}} {hT : T ∈ ⟦α⟧ᶻ}
  (den_t : ⟦(B.Term.int n).abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩) :
  ⦃fun ⟨E, Λ'⟩ ↦ ⌜Λ' = Λ ∧ E.freshvarsc = n_1 ∧ n_1 ≤  Λ'.keys.length⌝⦄
    encodeTerm (B.Term.int n) E
  ⦃⇓? ⟨t', σ⟩ ⟨E', Γ'⟩ =>
    ⌜n_1 ≤ E'.freshvarsc ∧ E'.freshvarsc ≤  Γ'.keys.length ∧ Γ' = Λ ∧
    σ = α.toSMTType ∧ Γ' ⊢ t' : σ ∧
    ∃ (hΔ : ∀ v ∈ SMT.fv t', (RenamingContext.toSMT «Δ» v).isSome = true),
      ∃ denT',
        ⟦t'.abstract (RenamingContext.toSMT «Δ») hΔ⟧ˢ = some denT' ∧ ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT'⌝⦄ := by
  mstart
  mintro pre ∀S
  mpure pre
  obtain ⟨rfl, rfl, hlen⟩ := pre

  rw [encodeTerm]
  mspec Std.Do.Spec.pure
  mpure_intro

  rw [B.Term.abstract, B.denote, Option.pure_def, Option.some_inj] at den_t
  injection den_t with T_eq heq
  subst T_eq
  injection heq with α_eq heq
  subst α_eq
  clear heq

  and_intros
  · apply Nat.le_refl
  · exact hlen
  · trivial
  · rfl
  · apply SMT.Typing.int
  · use ?_, ⟨ofInt n, .int, hT⟩
    · rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some_inj]
      and_intros
      · congr
      · rfl
      · rfl
    · intro v hv
      rw [SMT.fv, List.mem_nil_iff] at hv
      contradiction

theorem encodeTerm_spec.bool.{u_1} {Λ : SMT.TypeContext} {n : ℕ} (b : Bool) (E : B.Env) {α : BType}
  (typ_t : E.context ⊢ .bool b : α) {«Δ» : B.𝒱 → Option B.Dom}
  (Δ_fv : ∀ v ∈ B.fv (.bool b), («Δ» v).isSome = true) {T : ZFSet.{u_1}} {hT : T ∈ ⟦α⟧ᶻ}
  (den_t : ⟦(B.Term.bool b).abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, α, hT⟩) :
  ⦃fun ⟨E, Λ'⟩ ↦ ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ n ≤  Λ'.keys.length⌝⦄
    encodeTerm (B.Term.bool b) E
  ⦃⇓? ⟨t', σ⟩ ⟨E', Γ'⟩ =>
    ⌜n ≤ E'.freshvarsc ∧ E'.freshvarsc ≤ Γ'.keys.length ∧ Γ' = Λ ∧
    σ = α.toSMTType ∧
    Γ' ⊢ t' : σ ∧
    ∃ (hΔ : ∀ v ∈ SMT.fv t', (RenamingContext.toSMT «Δ» v).isSome = true),
      ∃ denT',
        ⟦t'.abstract (RenamingContext.toSMT «Δ») hΔ⟧ˢ = some denT' ∧ ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT'⌝⦄ := by
  mstart
  mintro pre ∀S
  mpure pre
  obtain ⟨rfl, rfl, hlen⟩ := pre

  rw [encodeTerm]
  mspec Std.Do.Spec.pure
  mpure_intro

  rw [B.Term.abstract, B.denote, Option.pure_def, Option.some_inj] at den_t
  injection den_t with T_eq heq
  subst T_eq
  injection heq with α_eq heq
  subst α_eq
  clear heq

  and_intros
  · apply Nat.le_refl
  · exact hlen
  · trivial
  · rfl
  · apply SMT.Typing.bool
  · use ?_, ⟨ZFBool.ofBool b, .bool, hT⟩
    · rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some_inj]
      and_intros
      · congr
      · rfl
      · rfl
    · intro v hv
      rw [SMT.fv, List.mem_nil_iff] at hv
      contradiction

theorem encodeTerm_spec.maplet.{u_1} {Λ : SMT.TypeContext} (x y : B.Term)
  (x_ih : ∀ (E : B.Env) {α : BType}, E.context ⊢ x : α →
    ∀ {«Δ» : B.𝒱 → Option B.Dom} (Δ_fv : ∀ v ∈ B.fv x, («Δ» v).isSome = true) {T : ZFSet.{u_1}}
      {hT : T ∈ ⟦α⟧ᶻ}, ⟦x.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩ → ∀ {n : ℕ},
          ⦃fun ⟨E, Λ'⟩ ↦ ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ n ≤  Λ'.keys.length⌝⦄
            encodeTerm x E
          ⦃⇓? (t', σ) ⟨E', Γ'⟩ =>
            ⌜n ≤ E'.freshvarsc ∧
                E'.freshvarsc ≤  Γ'.keys.length ∧
                  Γ' = Λ ∧
                    σ = α.toSMTType ∧
                      Γ' ⊢ t' : σ ∧
                        ∃ (hΔ : ∀ v ∈ SMT.fv t', (RenamingContext.toSMT «Δ» v).isSome = true),
                          ∃ denT',
                            ⟦t'.abstract (RenamingContext.toSMT «Δ») hΔ⟧ˢ = some denT' ∧
                              ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT'⌝⦄)
  (y_ih : ∀ (E : B.Env) {α : BType}, E.context ⊢ y : α →
    ∀ {«Δ» : B.𝒱 → Option B.Dom} (Δ_fv : ∀ v ∈ B.fv y, («Δ» v).isSome = true) {T : ZFSet.{u_1}}
      {hT : T ∈ ⟦α⟧ᶻ}, ⟦y.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩ → ∀ {n : ℕ},
        ⦃fun ⟨E, Λ'⟩ ↦ ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ n ≤  Λ'.keys.length⌝⦄
          encodeTerm y E
        ⦃⇓? (t', σ) ⟨E', Γ'⟩ =>
          ⌜n ≤ E'.freshvarsc ∧
              E'.freshvarsc ≤  Γ'.keys.length ∧
                Γ' = Λ ∧
                  σ = α.toSMTType ∧
                    Γ' ⊢ t' : σ ∧
                      ∃ (hΔ : ∀ v ∈ SMT.fv t', (RenamingContext.toSMT «Δ» v).isSome = true),
                        ∃ denT',
                          ⟦t'.abstract (RenamingContext.toSMT «Δ») hΔ⟧ˢ = some denT' ∧
                            ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT'⌝⦄)
  (E : B.Env) {α : BType} (typ_t : E.context ⊢ x ↦ᴮ y : α) {«Δ» : B.𝒱 → Option B.Dom}
  (Δ_fv : ∀ v ∈ B.fv (x ↦ᴮ y), («Δ» v).isSome = true) {T : ZFSet.{u_1}} {hT : T ∈ ⟦α⟧ᶻ}
  (den_t : ⟦(x ↦ᴮ y).abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩) {n : ℕ} :
  ⦃fun ⟨E, Λ'⟩ => ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ n ≤  Λ'.keys.length⌝⦄
    encodeTerm (x ↦ᴮ y) E
  ⦃⇓? (t', σ) ⟨E', Γ'⟩ =>
    ⌜n ≤ E'.freshvarsc ∧
        E'.freshvarsc ≤  Γ'.keys.length ∧
          Γ' = Λ ∧
            σ = α.toSMTType ∧
              Γ' ⊢ t' : σ ∧
                ∃ (hΔ : ∀ v ∈ SMT.fv t', (RenamingContext.toSMT «Δ» v).isSome = true),
                  ∃ denT',
                    ⟦t'.abstract (RenamingContext.toSMT «Δ») hΔ⟧ˢ = some denT' ∧ ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT'⌝⦄ := by
  mstart
  mintro pre ∀σ
  mpure pre
  obtain ⟨rfl, hlen⟩ := pre
  rw [encodeTerm]

  apply Typing.mapletE at typ_t
  obtain ⟨α, β, rfl, typ_x, typ_y⟩ := typ_t

  rw [B.Term.abstract, B.denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at den_t
  obtain ⟨⟨X, α', hX⟩, den_x, eq⟩ := den_t
  dsimp at eq
  rw [Option.bind_eq_some_iff] at eq
  obtain ⟨⟨Y, β', hY⟩, den_y, eq⟩ := eq
  rw [Option.some_inj] at eq
  dsimp at eq
  injection eq with T_eq heq
  subst T
  injection heq with eq heq
  injection eq with α'_eq β'_eq
  subst α' β'

  specialize x_ih (n := n) E typ_x («Δ» := «Δ») (fun v hv ↦ Δ_fv v (by rw [B.fv, List.mem_append]; exact Or.inl hv)) den_x
  mspec x_ih
  rename_i out_x
  obtain ⟨x_enc, α'⟩ := out_x
  mrename_i pre
  mintro ∀σ_x
  mpure pre
  dsimp at pre
  obtain ⟨n_le_σ_x_freshc, σ_x_freshc_le, σ_types_eq, rfl, typ_x_enc, hΔ_x_enc, ⟨Xenc, _, hXenc⟩, den_x_enc, ⟨rfl, retract_α_X_enc_eq_X⟩⟩ := pre

  specialize y_ih (n := σ_x.env.freshvarsc) E typ_y («Δ» := «Δ») (fun v hv ↦ Δ_fv v (by rw [B.fv, List.mem_append]; exact Or.inr hv)) den_y
  mspec y_ih
  rename_i out_y
  obtain ⟨y_enc, β'⟩ := out_y
  mrename_i pre
  mintro ∀σ_y
  mpure pre
  dsimp at pre
  obtain ⟨n_le, σ_y_freshc_le, pre, rfl, typ_y_enc, hΔ_y_enc, ⟨Yenc, _, hYenc⟩, den_y_enc, ⟨rfl, retract_β_Y_enc_eq_Y⟩⟩ := pre

  mspec Std.Do.Spec.pure
  mpure_intro
  and_intros
  · trans σ_x.env.freshvarsc
    · exact n_le_σ_x_freshc
    · exact n_le
  · exact σ_y_freshc_le
  · exact pre
  · congr
  · apply Typing.pair
    · rw [pre, ←σ_types_eq]
      exact typ_x_enc
    · exact typ_y_enc
  · exists ?_
    · intro v hv
      rw [SMT.fv, List.mem_append] at hv
      rcases hv with hv | hv
      · exact hΔ_x_enc v hv
      · exact hΔ_y_enc v hv
    · use ⟨Xenc.pair Yenc, α.toSMTType.pair β.toSMTType, by rw [SMTType.toZFSet, pair_mem_prod]; exact ⟨hXenc, hYenc⟩⟩
      and_intros
      · rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.bind_eq_bind, den_x_enc, Option.bind_some, den_y_enc]
        rfl
      · congr
      · unfold retract
        rw [π₁_pair, π₂_pair, pair_inj]
        exact ⟨retract_α_X_enc_eq_X, retract_β_Y_enc_eq_Y⟩

theorem encodeTerm_spec.add.{u_1} {Λ : SMT.TypeContext} (x y : B.Term)
  (x_ih : ∀ (E : B.Env) {α : BType}, E.context ⊢ x : α →
    ∀ {«Δ» : B.𝒱 → Option B.Dom} (Δ_fv : ∀ v ∈ B.fv x, («Δ» v).isSome = true) {T : ZFSet.{u_1}}
      {hT : T ∈ ⟦α⟧ᶻ}, ⟦x.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩ → ∀ {n : ℕ},
        ⦃fun ⟨E, Λ'⟩ => ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ n ≤  Λ'.keys.length⌝⦄
          encodeTerm x E
        ⦃⇓? (t', σ) ⟨E', Γ'⟩ =>
          ⌜n ≤ E'.freshvarsc ∧
              E'.freshvarsc ≤  Γ'.keys.length ∧
                Γ' = Λ ∧
                  σ = α.toSMTType ∧
                    Γ' ⊢ t' : σ ∧
                      ∃ (hΔ : ∀ v ∈ SMT.fv t', (RenamingContext.toSMT «Δ» v).isSome = true),
                        ∃ denT',
                          ⟦t'.abstract (RenamingContext.toSMT «Δ») hΔ⟧ˢ = some denT' ∧
                            ⟨T, α, hT⟩ ≘ᶻ denT'⌝⦄)
  (y_ih : ∀ (E : B.Env) {α : BType}, E.context ⊢ y : α →
    ∀ {«Δ» : B.𝒱 → Option B.Dom} (Δ_fv : ∀ v ∈ B.fv y, («Δ» v).isSome = true) {T : ZFSet.{u_1}}
      {hT : T ∈ ⟦α⟧ᶻ}, ⟦y.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩ → ∀ {n : ℕ},
        ⦃fun ⟨E, Λ'⟩ ↦ ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ n ≤  Λ'.keys.length⌝⦄
          encodeTerm y E
        ⦃⇓? (t', σ) ⟨E', Γ'⟩ =>
          ⌜n ≤ E'.freshvarsc ∧
              E'.freshvarsc ≤  Γ'.keys.length ∧
                Γ' = Λ ∧
                  σ = α.toSMTType ∧
                    Γ' ⊢ t' : σ ∧
                      ∃ (hΔ : ∀ v ∈ SMT.fv t', (RenamingContext.toSMT «Δ» v).isSome = true),
                        ∃ denT',
                          ⟦t'.abstract (RenamingContext.toSMT «Δ») hΔ⟧ˢ = some denT' ∧
                            ⟨T, α, hT⟩ ≘ᶻ denT'⌝⦄)
  (E : B.Env) {α : BType} (typ_t : E.context ⊢ x +ᴮ y : α) {«Δ» : B.𝒱 → Option B.Dom}
  (Δ_fv : ∀ v ∈ B.fv (x +ᴮ y), («Δ» v).isSome = true) {T : ZFSet.{u_1}} {hT : T ∈ ⟦α⟧ᶻ}
  (den_t : ⟦(x +ᴮ y).abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩) {n : ℕ} :
  ⦃fun ⟨E, Λ'⟩ => ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ n ≤  Λ'.keys.length⌝⦄
    encodeTerm (x +ᴮ y) E
  ⦃⇓? (t', σ) ⟨E', Γ'⟩ =>
    ⌜n ≤ E'.freshvarsc ∧
        E'.freshvarsc ≤  Γ'.keys.length ∧
          Γ' = Λ ∧
            σ = α.toSMTType ∧
              Γ' ⊢ t' : σ ∧
                ∃ (hΔ : ∀ v ∈ SMT.fv t', (RenamingContext.toSMT «Δ» v).isSome = true),
                  ∃ denT',
                    ⟦t'.abstract (RenamingContext.toSMT «Δ») hΔ⟧ˢ = some denT' ∧ ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT'⌝⦄ := by
  mstart
  mintro pre ∀σ
  mpure pre
  rw [encodeTerm]

  apply B.Typing.addE at typ_t
  obtain ⟨rfl, typ_x, typ_y⟩ := typ_t

  rw [B.Term.abstract, B.denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at den_t
  obtain ⟨⟨X, α, hX⟩, den_x, eq⟩ := den_t

  -- α = int
  have := denote_welltyped_eq
    (t := x.abstract («Δ» := «Δ»)
    (fun v hv ↦ Δ_fv v (by rw [B.fv, List.mem_append]; exact Or.inl hv)))
    ?_ den_x
  on_goal 2 =>
    use E.context.abstract («Δ» := «Δ»), WFTC.of_abstract, .int
    exact @Typing.of_abstract (B.Dom) («Δ» := «Δ») ?_ x E.context .int (fun v hv ↦ Δ_fv v (by rw [B.fv, List.mem_append]; exact Or.inl hv)) typ_x
  subst α


  dsimp at eq
  rw [Option.bind_eq_some_iff] at eq
  obtain ⟨⟨Y, β, hY⟩, den_y, eq⟩ := eq

  -- β = int
  have := denote_welltyped_eq
    (t := y.abstract («Δ» := «Δ»)
    (fun v hv ↦ Δ_fv v (by rw [B.fv, List.mem_append]; exact Or.inr hv)))
    ?_ den_y
  on_goal 2 =>
    use E.context.abstract («Δ» := «Δ»), WFTC.of_abstract, .int
    exact @Typing.of_abstract (B.Dom) («Δ» := «Δ») ?_ y E.context .int (fun v hv ↦ Δ_fv v (by rw [B.fv, List.mem_append]; exact Or.inr hv)) typ_y
  subst β

  rw [Option.some_inj] at eq
  injection eq with T_eq heq
  subst T
  clear heq

  specialize x_ih (n := n) E typ_x («Δ» := «Δ») (fun v hv ↦ Δ_fv v (by rw [B.fv, List.mem_append]; exact Or.inl hv)) den_x
  mspec x_ih
  rename_i out_x
  obtain ⟨x_enc, α'⟩ := out_x
  mrename_i pre
  mintro ∀σ_x
  mpure pre
  dsimp at pre
  obtain ⟨n_le, σ_x_freshc_le, rfl, rfl, typ_x_enc, hΔ_x_enc, ⟨Xenc, _, hXenc⟩, den_x_enc, ⟨rfl, retract_α_X_enc_eq_X⟩⟩ := pre

  conv =>
    enter [2,1,1]
    rw [BType.toSMTType]
    dsimp

  specialize y_ih (n := σ_x.env.freshvarsc) E typ_y («Δ» := «Δ») (fun v hv ↦ Δ_fv v (by rw [B.fv, List.mem_append]; exact Or.inr hv)) den_y
  mspec y_ih
  rename_i out_y
  obtain ⟨y_enc, β'⟩ := out_y
  mrename_i pre
  mintro ∀σ_y
  mpure pre
  dsimp at pre
  obtain ⟨σ_x_freshc_le_σ_y_freshc, σ_y_freshc_le, pre, rfl, typ_y_enc, hΔ_y_enc, ⟨Yenc, _, hYenc⟩, den_y_enc, ⟨rfl, retract_β_Y_enc_eq_Y⟩⟩ := pre

  mspec Std.Do.Spec.pure
  mpure_intro
  and_intros
  · trans σ_x.env.freshvarsc
    · exact n_le
    · exact σ_x_freshc_le_σ_y_freshc
  · exact σ_y_freshc_le
  · exact pre
  · congr
  · apply SMT.Typing.add
    · rw [pre]
      exact typ_x_enc
    · exact typ_y_enc
  · exists ?_
    · intro v hv
      rw [SMT.fv, List.mem_append] at hv
      rcases hv with hv | hv
      · exact hΔ_x_enc v hv
      · exact hΔ_y_enc v hv
    · use ⟨Xenc +ᶻ Yenc, .int, overloadBinOp_mem hXenc hYenc⟩
      and_intros
      · rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.bind_eq_bind, den_x_enc, Option.bind_some, den_y_enc]
        rfl
      · congr
      · dsimp [retract] at retract_α_X_enc_eq_X retract_β_Y_enc_eq_Y ⊢
        subst Xenc Yenc
        rfl

end encodeTerm_correct
