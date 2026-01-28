import SMT.Reasoning.Defs
import SMT.Reasoning.LooseningDefs
import Std.Tactic.Do

set_option mvcgen.warning false

open Std.Do

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

/-- Convenience predicate for “all free variables are mapped by a renaming”. -/
abbrev FVok («Δ» : SMT.𝒱 → Option SMT.Dom) (t : SMT.Term) : Prop :=
  ∀ v ∈ SMT.fv t, («Δ» v).isSome = true

open SMT ZFSet ShapeForcing in
/-- `loosen` returns a fresh variable `x! : β` and a Boolean equation `φ`
    that pins `x!` to be the semantic cast of `x : α` via the canonical ZF map. -/
@[spec]
theorem loosen_spec
  {Λ : SMT.TypeContext} {n : ℕ} {name : String}
  {x : SMT.Term} {α β : SMTType}
  (typ_x : Λ ⊢ x : α) (hTrue : (α ⊑ β) = true)
  («Δ» : B.𝒱 → Option B.Dom)
  (hx  : FVok (B.RenamingContext.toSMT «Δ») x) :
  ⦃ fun ⟨E, Λ'⟩ => ⌜ Λ' = Λ ∧ E.freshvarsc = n ∧ n ≤ Λ'.keys.length ⌝ ⦄
    loosen name x α β
  ⦃ ⇓? ⟨x!, φ⟩ ⟨E', Γ'⟩ =>
     ⌜ n ≤ E'.freshvarsc ∧ E'.freshvarsc ≤ Γ'.keys.length ∧
       Γ' = Λ.insert x! β ∧
       Γ' ⊢ (.var x!) : β ∧
       Γ' ⊢ φ : .bool ∧
       SMT.fv φ ⊆ SMT.fv x ∪ {x!} ∧
       -- Denotation adequacy: x! denotes the forward cast of the denotation of x,
       -- and φ holds (is zftrue) in every admissible renaming.
        ∃ (X Φ X' : SMT.Dom)
          (denx : ⟦x.abstract (B.RenamingContext.toSMT «Δ») hx⟧ˢ = some X)
          (denx! : ⟦(Term.var x!).abstract (Function.update (B.RenamingContext.toSMT «Δ») x! (some X')) (fun v hv ↦ by
            rw [fv, List.mem_singleton] at hv
            rw [hv, Function.update_self, Option.isSome_some])⟧ˢ = some X')
          (hφ : FVok (Function.update (B.RenamingContext.toSMT «Δ») x! (some X')) φ)
          (denφ : ⟦φ.abstract (Function.update (B.RenamingContext.toSMT «Δ») x! (some X')) hφ⟧ˢ = some Φ),
          (Φ.1 = zftrue →
            let ⟨F, hF⟩ := castZF_of_path (CastPath.of_true α β hTrue);
            X'.1 = @ᶻF ⟨X.1, by
              rw [is_func_dom_eq]
              let ⟨X, α', hX⟩ := X
              obtain ⟨⟩ := SMT.PHOAS.denote_welltyped_eq
                (t := x.abstract («Δ» := B.RenamingContext.toSMT «Δ») (fun v hv ↦ hx v hv))
                ⟨Λ.abstract (B.RenamingContext.toSMT «Δ»), PHOAS.WFTC.of_abstract, α, PHOAS.Typing.of_abstract hx typ_x⟩ denx
              exact hX⟩) ⌝ ⦄ := by
  induction typ_x generalizing β with
  | var Γ v α ih =>
    mstart
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, hlen⟩ := pre

    induction α generalizing β with
    | bool =>
      simp only [bool_cast_true_iff] at hTrue
      subst hTrue
      simp only [loosen]
      rw [ite_cond_eq_true _ _ (eq_true (by rw [BEq.rfl]))]
      mspec Std.Do.Spec.pure
      mspec SMT.freshVar_spec (τ := .bool) (name := name)
      rename_i x!
      mrename_i pre
      mintro ∀St'
      mpure pre
      obtain ⟨eq, x!_fresh, hfvc⟩ := pre
      mspec Std.Do.Spec.pure
      mpure_intro

      refine ⟨
        Nat.le.intro hfvc.symm, ?_, eq, ?_,
        Typing.bool St'.types true,
        by simp only [fv, List.cons_union, List.nil_union, List.nil_subset],
        (B.RenamingContext.toSMT «Δ» v).get (hx _ fv.mem_var),
        ?_⟩
      · rw [hfvc, eq]
        have : St.types.keys.erase x! = St.types.keys := by
          simpa only [List.erase_eq_self_iff]
        simpa only [AList.keys_insert, this, List.length_cons, Nat.add_le_add_iff_right, ge_iff_le]
      · rw [eq]
        apply Typing.var
        exact AList.lookup_insert St.types
      · use
          ?_,
          ?_,
          by rw [Term.abstract, denote, Option.pure_def, Option.some_inj],
          by
            rw [Term.abstract, denote, Option.pure_def, Option.some_inj]
            simp only [Function.update_self, Option.get_some],
          by simp only [FVok, fv, List.not_mem_nil, IsEmpty.forall_iff, implies_true],
          by rw [Term.abstract, denote, Option.pure_def, Option.some_inj]
        intros
        have mem_bool : ((B.RenamingContext.toSMT «Δ» v).get (hx _ fv.mem_var)).fst ∈ ⟦SMTType.bool⟧ᶻ := by
          obtain ⟨⟨V, τ, hV⟩, den_v⟩ := (hx _ fv.mem_var) |> Option.isSome_iff_exists.mp
          have eq := PHOAS.denote_welltyped_eq
            (t := (Term.var v).abstract (B.RenamingContext.toSMT «Δ») (fun v hv ↦ hx v hv))
            ⟨St.types.abstract (B.RenamingContext.toSMT «Δ»),
              PHOAS.WFTC.of_abstract, .bool,
              PHOAS.Typing.of_abstract hx (Typing.var St.types v SMTType.bool ih)⟩
            (T := V) (τ := τ) (hTτ := hV)
            (by rwa [Term.abstract, denote, Option.pure_def, Option.some_get])
          dsimp at eq
          subst τ
          conv =>
            enter [2,1,1]
            rw [den_v]
          rwa [Option.get_some]
        conv_rhs =>
          rw [fapply_eq_Image_singleton (Subtype.property _) mem_bool]
          conv =>
            enter [1,1,1]
            rw [castZF_of_path_id]
          rw [←fapply_eq_Image_singleton Id.IsFunc mem_bool,
            fapply_Id mem_bool]
    | int =>
      simp only [int_cast_true_iff] at hTrue
      subst hTrue
      simp only [loosen]
      rw [ite_cond_eq_true _ _ (eq_true (by rw [BEq.rfl]))]
      mspec Std.Do.Spec.pure
      mspec SMT.freshVar_spec (τ := .int) (name := name)
      rename_i x!
      mrename_i pre
      mintro ∀St'
      mpure pre
      obtain ⟨eq, x!_fresh, hfvc⟩ := pre
      mspec Std.Do.Spec.pure
      mpure_intro

      refine ⟨
        Nat.le.intro hfvc.symm, ?_, eq, ?_,
        Typing.bool St'.types true,
        by simp only [fv, List.cons_union, List.nil_union, List.nil_subset],
        (B.RenamingContext.toSMT «Δ» v).get (hx _ fv.mem_var),
        ?_⟩
      · rw [hfvc, eq]
        have : St.types.keys.erase x! = St.types.keys := by
          simpa only [List.erase_eq_self_iff]
        simpa only [AList.keys_insert, this, List.length_cons, Nat.add_le_add_iff_right, ge_iff_le]
      · rw [eq]
        apply Typing.var
        exact AList.lookup_insert St.types
      · use
          ?_,
          ?_,
          by rw [Term.abstract, denote, Option.pure_def, Option.some_inj],
          by
            rw [Term.abstract, denote, Option.pure_def, Option.some_inj]
            simp only [Function.update_self, Option.get_some],
          by simp only [FVok, fv, List.not_mem_nil, IsEmpty.forall_iff, implies_true],
          by rw [Term.abstract, denote, Option.pure_def, Option.some_inj]
        intros
        have mem_int : ((B.RenamingContext.toSMT «Δ» v).get (hx _ fv.mem_var)).fst ∈ ⟦SMTType.int⟧ᶻ := by
          obtain ⟨⟨V, τ, hV⟩, den_v⟩ := (hx _ fv.mem_var) |> Option.isSome_iff_exists.mp
          have eq := PHOAS.denote_welltyped_eq
            (t := (Term.var v).abstract (B.RenamingContext.toSMT «Δ») (fun v hv ↦ hx v hv))
            ⟨St.types.abstract (B.RenamingContext.toSMT «Δ»),
              PHOAS.WFTC.of_abstract, .int,
              PHOAS.Typing.of_abstract hx (Typing.var St.types v SMTType.int ih)⟩
            (T := V) (τ := τ) (hTτ := hV)
            (by rwa [Term.abstract, denote, Option.pure_def, Option.some_get])
          dsimp at eq
          subst τ
          conv =>
            enter [2,1,1]
            rw [den_v]
          rwa [Option.get_some]
        conv_rhs =>
          rw [fapply_eq_Image_singleton (Subtype.property _) mem_int]
          conv =>
            enter [1,1,1]
            rw [castZF_of_path_id]
          rw [←fapply_eq_Image_singleton Id.IsFunc mem_int,
            fapply_Id mem_int]
    | unit =>
      simp only [unit_cast_true_iff] at hTrue
      subst hTrue
      simp only [loosen]
      rw [ite_cond_eq_true _ _ (eq_true (by rw [BEq.rfl]))]
      mspec Std.Do.Spec.pure
      mspec SMT.freshVar_spec (τ := .unit) (name := name)
      rename_i x!
      mrename_i pre
      mintro ∀St'
      mpure pre
      obtain ⟨eq, x!_fresh, hfvc⟩ := pre
      mspec Std.Do.Spec.pure
      mpure_intro

      refine ⟨
        Nat.le.intro hfvc.symm, ?_, eq, ?_,
        Typing.bool St'.types true,
        by simp only [fv, List.cons_union, List.nil_union, List.nil_subset],
        (B.RenamingContext.toSMT «Δ» v).get (hx _ fv.mem_var),
        ?_⟩
      · rw [hfvc, eq]
        have : St.types.keys.erase x! = St.types.keys := by
          simpa only [List.erase_eq_self_iff]
        simpa only [AList.keys_insert, this, List.length_cons, Nat.add_le_add_iff_right, ge_iff_le]
      · rw [eq]
        apply Typing.var
        exact AList.lookup_insert St.types
      · use
          ?_,
          ?_,
          by rw [Term.abstract, denote, Option.pure_def, Option.some_inj],
          by
            rw [Term.abstract, denote, Option.pure_def, Option.some_inj]
            simp only [Function.update_self, Option.get_some],
          by simp only [FVok, fv, List.not_mem_nil, IsEmpty.forall_iff, implies_true],
          by rw [Term.abstract, denote, Option.pure_def, Option.some_inj]
        intros
        have mem_unit : ((B.RenamingContext.toSMT «Δ» v).get (hx _ fv.mem_var)).fst ∈ ⟦SMTType.unit⟧ᶻ := by
          obtain ⟨⟨V, τ, hV⟩, den_v⟩ := (hx _ fv.mem_var) |> Option.isSome_iff_exists.mp
          have eq := PHOAS.denote_welltyped_eq
            (t := (Term.var v).abstract (B.RenamingContext.toSMT «Δ») (fun v hv ↦ hx v hv))
            ⟨St.types.abstract (B.RenamingContext.toSMT «Δ»),
              PHOAS.WFTC.of_abstract, .unit,
              PHOAS.Typing.of_abstract hx (Typing.var St.types v SMTType.unit ih)⟩
            (T := V) (τ := τ) (hTτ := hV)
            (by rwa [Term.abstract, denote, Option.pure_def, Option.some_get])
          dsimp at eq
          subst τ
          conv =>
            enter [2,1,1]
            rw [den_v]
          rwa [Option.get_some]
        conv_rhs =>
          rw [fapply_eq_Image_singleton (Subtype.property _) mem_unit]
          conv =>
            enter [1,1,1]
            rw [castZF_of_path_id]
          rw [←fapply_eq_Image_singleton Id.IsFunc mem_unit,
            fapply_Id mem_unit]
    | pair α₁ α₂ α₁_ih α₂_ih =>
      simp only [pair_cast_true_iff] at hTrue
      obtain ⟨β₁, β₂, rfl, hα₁β₁, hα₂β₂⟩ := hTrue
      simp only [loosen]
      rw [ite_cond_eq_true _ _ (eq_true <| Bool.and_eq_true_iff.mp hTrue)]
      mspec Std.Do.Spec.pure
      mspec freshVar_spec
      rename_i x!
      mrename_i pre
      mintro ∀St'
      mpure pre
      obtain ⟨eq1, x!_fresh, hfvc1⟩ := pre
      -- specialize α₁_ih hα₁β₁
      -- specialize α₂_ih hα₂β₂
      clear α₁_ih α₂_ih
      split_ifs with h₁ h₂
      · simp only [beq_iff_eq] at h₁ h₂
        subst β₁ β₂
        mspec Std.Do.Spec.pure
        mpure_intro
        and_intros
        · exact Nat.le.intro hfvc1.symm
        · rw [hfvc1, eq1]
          have : St.types.keys.erase x! = St.types.keys := by
            simpa only [List.erase_eq_self_iff]
          simpa only [AList.keys_insert, this, List.length_cons, Nat.add_le_add_iff_right, ge_iff_le]
        · exact eq1
        · apply Typing.var
          rw [eq1]
          simp only [AList.lookup_insert]
        · rw [eq1]
          apply Typing.eq (τ := α₁.pair α₂)
          · apply Typing.var
            rw [AList.lookup_insert]
          · apply Typing.var
            rw [AList.lookup_insert_ne]
            · exact ih
            · rintro rfl
              rw [←AList.lookup_eq_none] at x!_fresh
              rw [x!_fresh] at ih
              nomatch ih
        · simp only [fv, List.cons_append, List.nil_append, List.cons_union, List.nil_union, List.cons_subset, List.mem_insert_iff, true_or, List.nil_subset, and_self, Singleton.singleton, List.mem_singleton, or_true]
        · let X := (B.RenamingContext.toSMT «Δ» v).get (hx _ fv.mem_var)
          have den_v : ⟦(Term.var v).abstract (B.RenamingContext.toSMT «Δ») hx⟧ˢ = X := by
            rw [Term.abstract, denote, Option.pure_def, Option.some_inj]
          have den_x! : ⟦(Term.var x!).abstract (Function.update (B.RenamingContext.toSMT «Δ») x! X) (fun v hv ↦ by
            rw [fv, List.mem_singleton] at hv
            rw [hv, Function.update_self, Option.isSome_some])⟧ˢ = some X := by
            rw [Term.abstract, denote, Option.pure_def, Option.some_inj]
            simp only [Function.update_self, Option.get_some]
          use X
          admit
      · admit
      · admit
      · admit
    | «fun» τ σ τ_ih σ_ih => sorry
    | option τ ih => sorry


  | int Γ n => sorry
  | bool Γ b => sorry
  | app Γ f x τ σ _ _ _ _ => sorry
  | lambda Γ vs τs t γ _ len_pos len_eq _ _ => sorry
  | «forall» Γ vs τs P _ len_pos len_eq _ _ => sorry
  | «exists» Γ vs τs P _ len_pos len_eq _ _ => sorry
  | eq Γ t₁ t₂ τ _ _ _ _ => sorry
  | and Γ t₁ t₂ _ _ _ _ => sorry
  | or Γ t₁ t₂ _ _ _ _ => sorry
  | not Γ t _ _ => sorry
  | imp Γ t₁ t₂ _ _ _ _ => sorry
  | ite Γ c t e τ _ _ _ _ _ _ => sorry
  | some Γ t τ _ _ => sorry
  | none Γ τ => sorry
  | the Γ t τ _ _ => sorry
  | pair Γ t₁ τ₁ t₂ τ₂ _ _ _ _ => sorry
  | fst Γ t τ σ _ _ => sorry
  | snd Γ t τ σ _ _ => sorry
  | distinct Γ ts τ _ _ => sorry
  | le Γ t₁ t₂ _ _ _ _ => sorry
  | add Γ t₁ t₂ _ _ _ _ => sorry
  | sub Γ t₁ t₂ _ _ _ _ => sorry
  | mul Γ t₁ t₂ _ _ _ _ => sorry

/--
TODO: Current state: skeleton for the proof, the correct statement still needs to be filled in.
-/
theorem castMembership_spec {α β : SMT.SMTType} {x S : SMT.Term} {Λ : SMT.TypeContext} {n : ℕ}
  (typ_x : Λ ⊢ x : α) (typ_S : Λ ⊢ S : β) :
  ⦃ λ ⟨E, Λ'⟩ ↦ ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ n ≤ Λ'.keys.length⌝ ⦄
    castMembership ⟨x, α⟩ ⟨S, β⟩
  ⦃ ⇓? ⟨t, τ⟩ ⟨E', Λ'⟩ =>
    ⌜n ≤ E'.freshvarsc ∧ E'.freshvarsc ≤ Λ'.keys.length ∧ Λ' = Λ ∧
    τ = .bool ∧ Λ' ⊢ t : .bool⌝ ⦄ := by
  induction β generalizing α x S Λ n with
  | bool | int | unit | option | pair =>
    mstart
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, hlen⟩ := pre
    unfold castMembership
    conv =>
      enter [2,1,1]
      dsimp
    mspec Std.Do.Spec.throw_StateT
  | «fun» τ σ τ_ih σ_ih =>
    mstart
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, hlen⟩ := pre
    unfold castMembership
    conv =>
      enter [2,1,1]
      dsimp
    split using _ _ case_eq | _ _ σ case_eq
    on_goal 3 => mspec Std.Do.Spec.throw_StateT
    · injection case_eq with τ_eq σ_eq
      subst σ_eq τ_eq
      split_ifs with eq_α_τ α_le_τ τ_le_α
      · mspec Std.Do.Spec.pure
        mpure_intro

        simp only [beq_iff_eq] at eq_α_τ
        subst α

        admit
      · admit
      · admit
      · mspec Std.Do.Spec.throw_StateT
    · injection case_eq with τ_eq σ_eq
      subst σ_eq τ_eq
      split using α β
      · split_ifs with α_eq_τ β_eq_σ β_le_σ σ_le_β α_le_τ β_eq_σ β_le_σ σ_le_β τ_le_α β_eq_σ β_le_σ σ_le_β
        · mspec Std.Do.Spec.pure
          mpure_intro

          simp only [beq_iff_eq] at α_eq_τ β_eq_σ
          subst α β

          admit
        · admit
        · admit
        · admit
        · admit
        · admit
        · admit
        · admit
        · admit
        · admit
        · admit
        · admit
        · admit
      · mspec Std.Do.Spec.throw_StateT

section encodeTerm_correct
open B SMT ZFSet

theorem encodeTerm_spec.ℤ.{u_1} {Λ : SMT.TypeContext} {n : ℕ} (E : B.Env) {α : BType}
  (typ_t : E.context ⊢ .ℤ : α) {«Δ» : B.𝒱 → Option B.Dom} (Δ_fv : ∀ v ∈ B.fv Term.ℤ, («Δ» v).isSome = true)
  {T : ZFSet.{u_1}} {hT : T ∈ ⟦α⟧ᶻ} (den_t : ⟦Term.ℤ.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, α, hT⟩) :
  ⦃fun ⟨E, Λ'⟩ ↦ ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ n ≤  Λ'.keys.length⌝⦄
    encodeTerm .ℤ E
  ⦃⇓? ⟨t', σ⟩ ⟨E', Γ'⟩ =>
    ⌜n ≤ E'.freshvarsc ∧ E'.freshvarsc ≤ Γ'.keys.length + 1 ∧ Γ' = Λ ∧
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
      exact Nat.le_add_right S.env.freshvarsc 1
    · rwa [freshvarsc_eq, Nat.add_le_add_iff_right]
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
    ⌜n ≤ E'.freshvarsc ∧ E'.freshvarsc ≤ Γ'.keys.length + 1 ∧ Γ' = Λ ∧
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
      exact Nat.le_add_right S.env.freshvarsc 1
    · rwa [freshvarsc_eq, Nat.add_le_add_iff_right]
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
  ⦃fun ⟨E', Λ'⟩ ↦ ⌜Λ' = Λ ∧ E'.freshvarsc = n ∧ n ≤  Λ'.keys.length⌝⦄
    encodeTerm (.var v) E
  ⦃⇓? ⟨t', σ⟩ ⟨E', Γ'⟩ =>
    ⌜n ≤ E'.freshvarsc ∧ E'.freshvarsc ≤  Γ'.keys.length ∧
      Γ' = Λ ∧ σ = α.toSMTType ∧ Γ' ⊢ t' : σ ∧
      ∃ (hΔ : ∀ v ∈ SMT.fv t', (RenamingContext.toSMT «Δ» v).isSome = true),
      ∃ denT',
        ⟦t'.abstract (RenamingContext.toSMT «Δ») hΔ⟧ˢ = some denT' ∧ ⟨T, α, hT⟩ ≘ᶻ denT'⌝⦄ := by
  mstart
  mintro pre ∀S
  mpure pre
  obtain ⟨rfl, rfl, hlen⟩ := pre

  rw [encodeTerm]
  mvcgen
  case vc1 τ τ_lookup =>
    and_intros
    · apply Nat.le_refl
    · exact hlen
    · trivial
    · rw [B.Term.abstract, B.denote, Option.pure_def, Option.some_get] at den_t
      have hΔ : ∀ v' ∈ SMT.fv (.var v), (RenamingContext.toSMT «Δ» v').isSome = true := by
        intro _ hv
        rw [SMT.fv, List.mem_singleton, eq_comm] at hv
        subst hv
        simp only [RenamingContext.toSMT, den_t, Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.isSome_some]

      set den₁ := RenamingContext.toSMT «Δ» v with den₁_def
      simp only [RenamingContext.toSMT, Option.pure_def, Option.bind_eq_bind] at den₁_def
      rw [den_t, Option.bind_some] at den₁_def

      have := @PHOAS.denote_welltyped_eq
        (t := (SMT.Term.var v).abstract (RenamingContext.toSMT «Δ») (fun v hv ↦ by apply hΔ; simpa only [B.fv, SMT.fv] using hv))
      simp [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some_get] at this
      dsimp [den₁] at den₁_def
      have := @this _ _ _ ?_ den₁_def
      on_goal 2 =>
        use S.types.abstract (RenamingContext.toSMT «Δ»), PHOAS.WFTC.of_abstract, τ
        apply SMT.PHOAS.Typing.of_abstract
        exact SMT.Typing.var S.types v τ τ_lookup
      exact this
    · apply SMT.Typing.var
      exact τ_lookup
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

theorem encodeTerm_spec.sub.{u_1} {Λ : SMT.TypeContext} (x y : B.Term)
  (x_ih :
    ∀ (E : B.Env) {α : BType},
      E.context ⊢ x : α →
        ∀ {«Δ» : B.𝒱 → _root_.Option B.Dom} (Δ_fv : ∀ v ∈ B.fv x, («Δ» v).isSome = true) {T : ZFSet.{u_1}}
          {hT : T ∈ ⟦α⟧ᶻ},
          ⟦x.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩ →
            ∀ {n : ℕ},
              ⦃fun x =>
                match x with
                | { env := E, types := Λ' } => ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ n ≤ (AList.keys Λ').length⌝⦄
                encodeTerm x E ⦃PostCond.mayThrow fun x x_1 =>
                  match x with
                  | (t', σ) =>
                    match x_1 with
                    | { env := E', types := Γ' } =>
                      ⌜n ≤ E'.freshvarsc ∧
                          E'.freshvarsc ≤ (AList.keys Γ').length ∧
                            Γ' = Λ ∧
                              σ = α.toSMTType ∧
                                Γ' ⊢ t' : σ ∧
                                  ∃ (hΔ : ∀ v ∈ SMT.fv t', (RenamingContext.toSMT «Δ» v).isSome = true),
                                    ∃ denT',
                                      ⟦t'.abstract (RenamingContext.toSMT «Δ») hΔ⟧ˢ = some denT' ∧
                                        ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT'⌝⦄)
  (y_ih :
    ∀ (E : B.Env) {α : BType},
      E.context ⊢ y : α →
        ∀ {«Δ» : B.𝒱 → _root_.Option B.Dom} (Δ_fv : ∀ v ∈ B.fv y, («Δ» v).isSome = true) {T : ZFSet.{u_1}}
          {hT : T ∈ ⟦α⟧ᶻ},
          ⟦y.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩ →
            ∀ {n : ℕ},
              ⦃fun x =>
                match x with
                | { env := E, types := Λ' } => ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ n ≤ (AList.keys Λ').length⌝⦄
                encodeTerm y E ⦃PostCond.mayThrow fun x x_1 =>
                  match x with
                  | (t', σ) =>
                    match x_1 with
                    | { env := E', types := Γ' } =>
                      ⌜n ≤ E'.freshvarsc ∧
                          E'.freshvarsc ≤ (AList.keys Γ').length ∧
                            Γ' = Λ ∧
                              σ = α.toSMTType ∧
                                Γ' ⊢ t' : σ ∧
                                  ∃ (hΔ : ∀ v ∈ SMT.fv t', (RenamingContext.toSMT «Δ» v).isSome = true),
                                    ∃ denT',
                                      ⟦t'.abstract (RenamingContext.toSMT «Δ») hΔ⟧ˢ = some denT' ∧
                                        ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT'⌝⦄)
  (E : B.Env) {α : BType} (typ_t : E.context ⊢ x -ᴮ y : α) {«Δ» : B.𝒱 → _root_.Option B.Dom}
  (Δ_fv : ∀ v ∈ B.fv (x -ᴮ y), («Δ» v).isSome = true) {T : ZFSet.{u_1}} {hT : T ∈ ⟦α⟧ᶻ}
  (den_t : ⟦(x -ᴮ y).abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩) {n : ℕ} :
  ⦃fun x =>
    match x with
    | { env := E, types := Λ' } => ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ n ≤ (AList.keys Λ').length⌝⦄
    encodeTerm (x -ᴮ y) E ⦃PostCond.mayThrow fun x x_1 =>
      match x with
      | (t', σ) =>
        match x_1 with
        | { env := E', types := Γ' } =>
          ⌜n ≤ E'.freshvarsc ∧
              E'.freshvarsc ≤ (AList.keys Γ').length ∧
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
  apply B.Typing.subE at typ_t
  obtain ⟨rfl, typ_x, typ_y⟩ := typ_t
  rw [B.Term.abstract, B.denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at den_t
  obtain ⟨⟨X, α, hX⟩, den_x, eq⟩ := den_t
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
  · rfl
  · apply SMT.Typing.sub
    · rw [pre]
      exact typ_x_enc
    · exact typ_y_enc
  · exists ?_
    · intro v hv
      rw [SMT.fv, List.mem_append] at hv
      rcases hv with hv | hv
      · exact hΔ_x_enc v hv
      · exact hΔ_y_enc v hv
    · use ⟨Xenc -ᶻ Yenc, .int, overloadBinOp_mem hXenc hYenc⟩
      and_intros
      · rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.bind_eq_bind, den_x_enc, Option.bind_some, den_y_enc]
        rfl
      · congr
      · dsimp [retract] at retract_α_X_enc_eq_X retract_β_Y_enc_eq_Y ⊢
        subst Xenc Yenc
        rfl

theorem encodeTerm_spec.mul.{u_1} {Λ : SMT.TypeContext} (x y : B.Term)
  (x_ih :
    ∀ (E : B.Env) {α : BType},
      E.context ⊢ x : α →
        ∀ {«Δ» : B.𝒱 → _root_.Option B.Dom} (Δ_fv : ∀ v ∈ B.fv x, («Δ» v).isSome = true) {T : ZFSet.{u_1}}
          {hT : T ∈ ⟦α⟧ᶻ},
          ⟦x.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩ →
            ∀ {n : ℕ},
              ⦃fun x =>
                match x with
                | { env := E, types := Λ' } => ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ n ≤ (AList.keys Λ').length⌝⦄
                encodeTerm x E ⦃PostCond.mayThrow fun x x_1 =>
                  match x with
                  | (t', σ) =>
                    match x_1 with
                    | { env := E', types := Γ' } =>
                      ⌜n ≤ E'.freshvarsc ∧
                          E'.freshvarsc ≤ (AList.keys Γ').length ∧
                            Γ' = Λ ∧
                              σ = α.toSMTType ∧
                                Γ' ⊢ t' : σ ∧
                                  ∃ (hΔ : ∀ v ∈ SMT.fv t', (RenamingContext.toSMT «Δ» v).isSome = true),
                                    ∃ denT',
                                      ⟦t'.abstract (RenamingContext.toSMT «Δ») hΔ⟧ˢ = some denT' ∧
                                        ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT'⌝⦄)
  (y_ih :
    ∀ (E : B.Env) {α : BType},
      E.context ⊢ y : α →
        ∀ {«Δ» : B.𝒱 → _root_.Option B.Dom} (Δ_fv : ∀ v ∈ B.fv y, («Δ» v).isSome = true) {T : ZFSet.{u_1}}
          {hT : T ∈ ⟦α⟧ᶻ},
          ⟦y.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩ →
            ∀ {n : ℕ},
              ⦃fun x =>
                match x with
                | { env := E, types := Λ' } => ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ n ≤ (AList.keys Λ').length⌝⦄
                encodeTerm y E ⦃PostCond.mayThrow fun x x_1 =>
                  match x with
                  | (t', σ) =>
                    match x_1 with
                    | { env := E', types := Γ' } =>
                      ⌜n ≤ E'.freshvarsc ∧
                          E'.freshvarsc ≤ (AList.keys Γ').length ∧
                            Γ' = Λ ∧
                              σ = α.toSMTType ∧
                                Γ' ⊢ t' : σ ∧
                                  ∃ (hΔ : ∀ v ∈ SMT.fv t', (RenamingContext.toSMT «Δ» v).isSome = true),
                                    ∃ denT',
                                      ⟦t'.abstract (RenamingContext.toSMT «Δ») hΔ⟧ˢ = some denT' ∧
                                        ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT'⌝⦄)
  (E : B.Env) {α : BType} (typ_t : E.context ⊢ x *ᴮ y : α) {«Δ» : B.𝒱 → _root_.Option B.Dom}
  (Δ_fv : ∀ v ∈ B.fv (x *ᴮ y), («Δ» v).isSome = true) {T : ZFSet.{u_1}} {hT : T ∈ ⟦α⟧ᶻ}
  (den_t : ⟦(x *ᴮ y).abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩) {n : ℕ} :
  ⦃fun x =>
    match x with
    | { env := E, types := Λ' } => ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ n ≤ (AList.keys Λ').length⌝⦄
    encodeTerm (x *ᴮ y) E ⦃PostCond.mayThrow fun x x_1 =>
      match x with
      | (t', σ) =>
        match x_1 with
        | { env := E', types := Γ' } =>
          ⌜n ≤ E'.freshvarsc ∧
              E'.freshvarsc ≤ (AList.keys Γ').length ∧
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
  apply B.Typing.mulE at typ_t
  obtain ⟨rfl, typ_x, typ_y⟩ := typ_t
  rw [B.Term.abstract, B.denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at den_t
  obtain ⟨⟨X, α, hX⟩, den_x, eq⟩ := den_t
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
  · rfl
  · apply SMT.Typing.mul
    · rw [pre]
      exact typ_x_enc
    · exact typ_y_enc
  · exists ?_
    · intro v hv
      rw [SMT.fv, List.mem_append] at hv
      rcases hv with hv | hv
      · exact hΔ_x_enc v hv
      · exact hΔ_y_enc v hv
    · use ⟨Xenc *ᶻ Yenc, .int, overloadBinOp_mem hXenc hYenc⟩
      and_intros
      · rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.bind_eq_bind, den_x_enc, Option.bind_some, den_y_enc]
        rfl
      · congr
      · dsimp [retract] at retract_α_X_enc_eq_X retract_β_Y_enc_eq_Y ⊢
        subst Xenc Yenc
        rfl


theorem encodeTerm_spec.mem.{u_1} {Λ : SMT.TypeContext} (x S : B.Term)
  (x_ih :
    ∀ (E : B.Env) {α : BType},
      E.context ⊢ x : α →
        ∀ {«Δ» : B.𝒱 → _root_.Option B.Dom} (Δ_fv : ∀ v ∈ B.fv x, («Δ» v).isSome = true) {T : ZFSet.{u_1}}
          {hT : T ∈ ⟦α⟧ᶻ},
          ⟦x.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩ →
            ∀ {n : ℕ},
              ⦃fun x =>
                match x with
                | { env := E, types := Λ' } => ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ n ≤ (AList.keys Λ').length⌝⦄
                encodeTerm x E ⦃PostCond.mayThrow fun x x_1 =>
                  match x with
                  | (t', σ) =>
                    match x_1 with
                    | { env := E', types := Γ' } =>
                      ⌜n ≤ E'.freshvarsc ∧
                          E'.freshvarsc ≤ (AList.keys Γ').length ∧
                            Γ' = Λ ∧
                              σ = α.toSMTType ∧
                                Γ' ⊢ t' : σ ∧
                                  ∃ (hΔ : ∀ v ∈ SMT.fv t', (RenamingContext.toSMT «Δ» v).isSome = true),
                                    ∃ denT',
                                      ⟦t'.abstract (RenamingContext.toSMT «Δ») hΔ⟧ˢ = some denT' ∧
                                        ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT'⌝⦄)
  (S_ih :
    ∀ (E : B.Env) {α : BType},
      E.context ⊢ S : α →
        ∀ {«Δ» : B.𝒱 → _root_.Option B.Dom} (Δ_fv : ∀ v ∈ B.fv S, («Δ» v).isSome = true) {T : ZFSet.{u_1}}
          {hT : T ∈ ⟦α⟧ᶻ},
          ⟦S.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩ →
            ∀ {n : ℕ},
              ⦃fun x =>
                match x with
                | { env := E, types := Λ' } => ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ n ≤ (AList.keys Λ').length⌝⦄
                encodeTerm S E ⦃PostCond.mayThrow fun x x_1 =>
                  match x with
                  | (t', σ) =>
                    match x_1 with
                    | { env := E', types := Γ' } =>
                      ⌜n ≤ E'.freshvarsc ∧
                          E'.freshvarsc ≤ (AList.keys Γ').length ∧
                            Γ' = Λ ∧
                              σ = α.toSMTType ∧
                                Γ' ⊢ t' : σ ∧
                                  ∃ (hΔ : ∀ v ∈ SMT.fv t', (RenamingContext.toSMT «Δ» v).isSome = true),
                                    ∃ denT',
                                      ⟦t'.abstract (RenamingContext.toSMT «Δ») hΔ⟧ˢ = some denT' ∧
                                        ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT'⌝⦄)
  (E : B.Env) {α : BType} (typ_t : E.context ⊢ x ∈ᴮ S : α) {«Δ» : B.𝒱 → _root_.Option B.Dom}
  (Δ_fv : ∀ v ∈ B.fv (x ∈ᴮ S), («Δ» v).isSome = true) {T : ZFSet.{u_1}} {hT : T ∈ ⟦α⟧ᶻ}
  (den_t : ⟦(x ∈ᴮ S).abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩) {n : ℕ} :
  ⦃fun ⟨E, Λ'⟩ => ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ n ≤ Λ'.keys.length⌝⦄
    encodeTerm (x ∈ᴮ S) E
  ⦃⇓? ⟨t', σ⟩ ⟨E', Γ'⟩ =>
    ⌜n ≤ E'.freshvarsc ∧ E'.freshvarsc ≤ Γ'.keys.length ∧ Γ' = Λ ∧
    σ = α.toSMTType ∧ Γ' ⊢ t' : σ ∧
    ∃ (hΔ : ∀ v ∈ SMT.fv t', (RenamingContext.toSMT «Δ» v).isSome = true), ∃ denT',
      ⟦t'.abstract (RenamingContext.toSMT «Δ») hΔ⟧ˢ = some denT' ∧ ⟨T, α, hT⟩ ≘ᶻ denT'⌝⦄ := by
  mstart
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, hlen⟩ := pre

  apply Typing.memE at typ_t
  obtain ⟨rfl, α, typ_x, typ_S⟩ := typ_t

  rw [B.Term.abstract, B.denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at den_t
  obtain ⟨⟨X, α', hX⟩, den_x, eq⟩ := den_t
  have α_eq := @denote_welltyped_eq
    (x.abstract «Δ» (fun v hv ↦ Δ_fv v (by rw [B.fv, List.mem_append]; exact Or.inl hv))) X α' hX ?_ den_x
  on_goal 2 =>
    use E.context.abstract («Δ» := «Δ»), WFTC.of_abstract, α
    exact @Typing.of_abstract (B.Dom) («Δ» := «Δ») ?_ x E.context α (fun v hv ↦ Δ_fv v (by rw [B.fv, List.mem_append]; exact Or.inl hv)) typ_x
  dsimp at α_eq
  subst α'

  dsimp at eq
  rw [Option.bind_eq_some_iff] at eq
  obtain ⟨⟨S', _, hS'⟩, den_S, eq⟩ := eq
  have α_set_eq := @denote_welltyped_eq
    (S.abstract «Δ» (fun v hv ↦ Δ_fv v (by rw [B.fv, List.mem_append]; exact Or.inr hv))) S' _ hS' ?_ den_S
  on_goal 2 =>
    use E.context.abstract («Δ» := «Δ»), WFTC.of_abstract, α.set
    exact @Typing.of_abstract (B.Dom) («Δ» := «Δ») ?_ S E.context α.set (fun v hv ↦ Δ_fv v (by rw [B.fv, List.mem_append]; exact Or.inr hv)) typ_S
  dsimp at α_set_eq
  subst α_set_eq

  dsimp at eq
  rw [ite_cond_eq_true _ _ (eq_true rfl), Option.some_inj] at eq
  injection eq with T_eq heq

  subst T_eq

  rw [encodeTerm]

  mspec x_ih E typ_x (fun v hv ↦ Δ_fv v (by rw [B.fv, List.mem_append]; exact Or.inl hv)) den_x
  rename_i out_x
  obtain ⟨x_enc, α'⟩ := out_x
  mrename_i pre
  mintro ∀St'
  mpure pre
  dsimp at pre
  obtain ⟨St_St'_fv, St'_fv_le, St_eq_St', rfl, typ_x_enc, ΔSMT_fv, ⟨Xenc, α', hXenc⟩, den_x_enc, ⟨rfl, retract_Xenc⟩⟩ := pre

  mspec S_ih E typ_S (fun v hv ↦ Δ_fv v (by rw [B.fv, List.mem_append]; exact Or.inr hv)) den_S
  rename_i out_S
  obtain ⟨S_enc, β'⟩ := out_S
  mrename_i pre
  mintro ∀St''
  mpure pre
  dsimp at pre
  obtain ⟨St'_St''_fv, St''_fv_le, St_eq_St'', rfl, typ_S_enc, ΔSMT_fv_S, ⟨Senc, β', hSenc⟩, den_S_enc, ⟨rfl, retract_Senc⟩⟩ := pre

  admit




end encodeTerm_correct
