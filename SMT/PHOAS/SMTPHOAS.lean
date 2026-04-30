import SMT.PHOAS.Basic
import SMT.Syntax
import Mathlib.Logic.Function.OfArity
import Mathlib.Data.Fin.Tuple.Curry

mutual
  /--
    `SMT.Term.abstract` translates a term from the concrete SMT language syntax to a PHOAS (Parametric Higher-Order Abstract Syntax) representation.

    The function recursively traverses the SMT term structure, applying the variable renaming `Δ` to variables
    and translating each SMT constructor to its corresponding PHOAS constructor. For binding constructs
    (forall, exists, lambda), it uses the helper function `go` to handle variable scoping.

  Note: This function is part of the translation from concrete SMT syntax to PHOAS representation,
  which enables easier manipulation and transformation of SMT terms while maintaining proper variable binding.
  This function must be close to the identity function on the PHOAS representation of SMT terms as one cannot
  prove that the translation is correct without a formal semantics of SMT terms.
  -/
  def SMT.Term.abstract {α} : (t : SMT.Term) → (Δ : SMT.𝒱 → Option α) → (∀ v ∈ fv t, (Δ v).isSome) → PHOAS.Term α
    | .var v, Δ, Δ_fv => .var <| (Δ v).get (Δ_fv v fv.mem_var)
    | .int n, _, Δ_fv => .int n
    | .bool b, _, Δ_fv => .bool b
    | x +ˢ y, Δ, Δ_fv => (x.abstract Δ (Δ_fv · <| fv.mem_add <| .inl ·)) +ˢ' (y.abstract Δ (Δ_fv · <| fv.mem_add <| .inr ·))
    | x -ˢ y, Δ, Δ_fv => (x.abstract Δ (Δ_fv · <| fv.mem_sub <| .inl ·)) -ˢ' (y.abstract Δ (Δ_fv · <| fv.mem_sub <| .inr ·))
    | x *ˢ y, Δ, Δ_fv => (x.abstract Δ (Δ_fv · <| fv.mem_mul <| .inl ·)) *ˢ' (y.abstract Δ (Δ_fv · <| fv.mem_mul <| .inr ·))
    | x ≤ˢ y, Δ, Δ_fv => (x.abstract Δ (Δ_fv · <| fv.mem_le <| .inl ·)) ≤ˢ' (y.abstract Δ (Δ_fv · <| fv.mem_le <| .inr ·))
    | x ∧ˢ y, Δ, Δ_fv => (x.abstract Δ (Δ_fv · <| fv.mem_and <| .inl ·)) ∧ˢ' (y.abstract Δ (Δ_fv · <| fv.mem_and <| .inr ·))
    | ¬ˢ x, Δ, Δ_fv => ¬ˢ' (x.abstract Δ (Δ_fv · <| fv.mem_not ·))
    | x =ˢ y, Δ, Δ_fv => (x.abstract Δ (Δ_fv · <| fv.mem_eq <| .inl ·)) =ˢ' (y.abstract Δ (Δ_fv · <| fv.mem_eq <| .inr ·))
    | .lambda vs τs P, Δ, Δ_fv =>
      if h_len : vs.length = τs.length then
        .lambda (n := vs.length) (λ ⟨i, hi⟩ => τs[i]) (go P vs Δ (λ v hv h => Δ_fv _ <| fv.mem_lambda ⟨hv, h⟩)).uncurry
      else unreachable!
    | .forall vs τs P, Δ, Δ_fv =>
      if h_len : vs.length = τs.length then
        .forall (n := vs.length) (λ ⟨i, hi⟩ => τs[i]) (go P vs Δ (λ v hv h => Δ_fv _ <| fv.mem_forall ⟨hv, h⟩)).uncurry
      else unreachable!
    | .exists vs τs P, Δ, Δ_fv =>
      if h_len : vs.length = τs.length then
        PHOAS.Term.exists (n := vs.length) (λ ⟨i, hi⟩ => τs[i]) (go P vs Δ (λ v hv h => Δ_fv _ <| fv.mem_exists ⟨hv, h⟩)).uncurry
      else unreachable!
    | .app f x, Δ, Δ_fv => .app (f.abstract Δ (Δ_fv · <| fv.mem_app <| .inl ·)) (x.abstract Δ (Δ_fv · <| fv.mem_app <| .inr ·))
    | distinct xs, Δ, Δ_fv => .distinct <| abstractList xs Δ (λ v hv => Δ_fv v <| fv.mem_distinct ⟨·, ·⟩ hv)
    | snd x, Δ, Δ_fv => .snd (x.abstract Δ (Δ_fv · <| fv.mem_snd ·))
    | fst x, Δ, Δ_fv => .fst (x.abstract Δ (Δ_fv · <| fv.mem_fst ·))
    | pair x y, Δ, Δ_fv => .pair (x.abstract Δ (Δ_fv · <| fv.mem_pair <| .inl ·)) (y.abstract Δ (Δ_fv · <| fv.mem_pair <| .inr ·))
    | the x, Δ, Δ_fv => .the (x.abstract Δ (Δ_fv · <| fv.mem_the ·))
    | some x, Δ, Δ_fv => .some (x.abstract Δ (Δ_fv · <| fv.mem_some ·))
    | ite c t e, Δ, Δ_fv => .ite (c.abstract Δ (Δ_fv · <| fv.mem_ite <| .inl ·)) (t.abstract Δ (Δ_fv · <| fv.mem_ite <| .inr <| .inl ·)) (e.abstract Δ (Δ_fv · <| fv.mem_ite <| .inr <| .inr ·))
    | imp x y, Δ, Δ_fv => (x.abstract Δ (Δ_fv · <| fv.mem_imp <| .inl ·)) ⇒ˢ' (y.abstract Δ (Δ_fv · <| fv.mem_imp <| .inr ·))
    | or x y, Δ, Δ_fv => (x.abstract Δ (Δ_fv · <| fv.mem_or <| .inl ·)) ∨ˢ' (y.abstract Δ (Δ_fv · <| fv.mem_or <| .inr ·))
    | as none (.option τ), Δ, Δ_fv => .none τ
    | as a _, Δ, Δ_fv => a.abstract Δ (Δ_fv · <| fv.mem_as ·)
    | none, _, _ => unreachable!
  where
    go (P : SMT.Term) : (vs : List SMT.𝒱) → (Δ : SMT.𝒱 → Option α) → (∀ v ∈ fv P, v ∉ vs → (Δ v).isSome) → Function.OfArity α (PHOAS.Term α) vs.length
    | [], Δ, Δ_fv => P.abstract Δ (λ v hv => Δ_fv v hv List.not_mem_nil)
    | v::vs, Δ, Δ_fv => λ y => go P vs (Function.update Δ v (.some y)) (by classical
      intro x h₁ h₂
      by_cases x = v
      · subst x
        specialize Δ_fv v h₁
        rw [←Classical.or_iff_not_imp_left] at Δ_fv
        rcases Δ_fv with Δ_fv | Δ_fv
        · exact Option.isSome_iff_exists.mpr ⟨y, Function.update_self v (.some y) Δ⟩
        · unfold Function.update
          split_ifs
          · rfl
          · contradiction
      · specialize Δ_fv x h₁ (List.not_mem_cons_of_ne_of_not_mem ‹_› h₂)
        obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp Δ_fv
        apply Option.isSome_iff_exists.mpr
        exists z
        unfold Function.update
        split_ifs
        exact hz)
  def SMT.Term.abstractList {α} (ts : List SMT.Term) (Δ : SMT.𝒱 → Option α) (Δ_fv : ∀ t ∈ ts, ∀ v ∈ fv t, (Δ v).isSome) : Fin ts.length → (PHOAS.Term α) :=
    match ts with
    | [] => nofun
    | t::ts => fun i ↦
      if h : i = ⟨0, Nat.zero_lt_succ ts.length⟩ then
        t.abstract Δ (Δ_fv t List.mem_cons_self)
      else SMT.Term.abstractList ts Δ (fun t' ht v hv ↦ Δ_fv t' (List.mem_cons_of_mem t ht) v hv) (i.pred h)
end
