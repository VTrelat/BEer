import B.PHOAS.Basic
import B.Syntax.Basic
import Mathlib.Data.Fin.Tuple.Curry

/--
  `B.Term.abstract` translates a term from the concrete B language syntax to a PHOAS (Parametric Higher-Order Abstract Syntax) representation.

  The function recursively traverses the B term structure, applying the variable renaming `Δ` to variables
  and translating each B constructor to its corresponding PHOAS constructor. For binding constructs
  (collect, lambda, all), it uses the helper function `go` to handle variable scoping.

Note: This function is part of the translation from concrete B syntax to PHOAS representation,
which enables easier manipulation and transformation of B terms while maintaining proper variable binding.
This function must be close to the identity function on the PHOAS representation of B terms as one cannot
prove that the translation is correct without a formal semantics of B terms.
-/
def B.Term.abstract {α} : (t : B.Term) → (Δ : B.𝒱 → Option α) → (∀ v ∈ fv t, (Δ v).isSome) → PHOAS.Term α
  | .var v, Δ, Δ_fv => .var <| (Δ v).get (Δ_fv v (List.mem_of_mem_head? rfl))
  | .int n, _, Δ_fv => .int n
  | .bool b, _, Δ_fv => .bool b
  | x ↦ᴮ y, Δ, Δ_fv => .maplet (x.abstract Δ (Δ_fv · <| fv.mem_maplet <| .inl ·)) (y.abstract Δ (Δ_fv · <| fv.mem_maplet <| .inr ·))
  | x +ᴮ y, Δ, Δ_fv => .add (x.abstract Δ (Δ_fv · <| fv.mem_add <| .inl ·)) (y.abstract Δ (Δ_fv · <| fv.mem_add <| .inr ·))
  | x -ᴮ y, Δ, Δ_fv => .sub (x.abstract Δ (Δ_fv · <| fv.mem_sub <| .inl ·)) (y.abstract Δ (Δ_fv · <| fv.mem_sub <| .inr ·))
  | x *ᴮ y, Δ, Δ_fv => .mul (x.abstract Δ (Δ_fv · <| fv.mem_mul <| .inl ·)) (y.abstract Δ (Δ_fv · <| fv.mem_mul <| .inr ·))
  | x ≤ᴮ y, Δ, Δ_fv => .le (x.abstract Δ (Δ_fv · <| fv.mem_le <| .inl ·)) (y.abstract Δ (Δ_fv · <| fv.mem_le <| .inr ·))
  | x ∧ᴮ y, Δ, Δ_fv => .and (x.abstract Δ (Δ_fv · <| fv.mem_and <| .inl ·)) (y.abstract Δ (Δ_fv · <| fv.mem_and <| .inr ·))
  | ¬ᴮ x, Δ, Δ_fv => .not (x.abstract Δ (Δ_fv · <| fv.mem_not ·))
  | x =ᴮ y, Δ, Δ_fv => .eq (x.abstract Δ (Δ_fv · <| fv.mem_eq <| .inl ·)) (y.abstract Δ (Δ_fv · <| fv.mem_eq <| .inr ·))
  | .ℤ, _, _ => .ℤ
  | .𝔹, _, _ => .𝔹
  | x ∈ᴮ S, Δ, Δ_fv => .mem (x.abstract Δ (Δ_fv · <| fv.mem_mem <| .inl ·)) (S.abstract Δ (Δ_fv · <| fv.mem_mem <| .inr ·))
  | .collect vs D P, Δ, Δ_fv => .collect (D.abstract Δ (Δ_fv · <| fv.mem_collect <| .inl ·)) (go P vs Δ (Δ_fv · <| fv.mem_collect <| Or.inr ⟨·, ·⟩)).uncurry
  | .lambda vs D P, Δ, Δ_fv => .lambda (D.abstract Δ (Δ_fv · <| fv.mem_collect <| .inl ·)) (go P vs Δ (Δ_fv · <| fv.mem_collect <| Or.inr ⟨·, ·⟩)).uncurry
  | .all vs D P, Δ, Δ_fv => .all (D.abstract Δ (Δ_fv · <| fv.mem_collect <| .inl ·)) (go P vs Δ (Δ_fv · <| fv.mem_collect <| Or.inr ⟨·, ·⟩)).uncurry
  | 𝒫ᴮ S, Δ, Δ_fv => .pow (S.abstract Δ (Δ_fv · <| fv.mem_pow ·))
  | S ⨯ᴮ T, Δ, Δ_fv => .cprod (S.abstract Δ (Δ_fv · <| fv.mem_cprod <| .inl ·)) (T.abstract Δ (Δ_fv · <| fv.mem_cprod <| .inr ·))
  | S ∪ᴮ T, Δ, Δ_fv => .union (S.abstract Δ (Δ_fv · <| fv.mem_union <| .inl ·)) (T.abstract Δ (Δ_fv · <| fv.mem_union <| .inr ·))
  | S ∩ᴮ T, Δ, Δ_fv => .inter (S.abstract Δ (Δ_fv · <| fv.mem_inter <| .inl ·)) (T.abstract Δ (Δ_fv · <| fv.mem_inter <| .inr ·))
  | |S|ᴮ, Δ, Δ_fv => .card (S.abstract Δ (Δ_fv · <| fv.mem_card ·))
  | .app f x, Δ, Δ_fv => .app (f.abstract Δ (Δ_fv · <| fv.mem_app <| .inl ·)) (x.abstract Δ (Δ_fv · <| fv.mem_app <| .inr ·))
  | .min S, Δ, Δ_fv => .min (S.abstract Δ (Δ_fv · <| fv.mem_min ·))
  | .max S, Δ, Δ_fv => .max (S.abstract Δ (Δ_fv · <| fv.mem_max ·))
  | A ⇸ᴮ B, Δ, Δ_fv => .pfun (A.abstract Δ (Δ_fv · <| fv.mem_pfun <| .inl ·)) (B.abstract Δ (Δ_fv · <| fv.mem_pfun <| .inr ·))
  where go (P : B.Term) : (vs : List B.𝒱) → (Δ : B.𝒱 → Option α) → (∀ v ∈ fv P, v ∉ vs → (Δ v).isSome) → Function.OfArity α (PHOAS.Term α) vs.length
    | [], Δ, Δ_fv => P.abstract Δ (λ v hv => Δ_fv v hv List.not_mem_nil)
    | v::vs, Δ, Δ_fv => λ y => go P vs (Function.update Δ v (some y)) (by
      intro x h₁ h₂
      by_cases x = v
      · subst x
        specialize Δ_fv v h₁
        rw [← Classical.or_iff_not_imp_left] at Δ_fv
        rcases Δ_fv with Δ_fv | Δ_fv
        · exact Option.isSome_iff_exists.mpr ⟨y, Function.update_self v (some y) Δ⟩
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
        exact hz
    )


-- #eval B.Term.abstract (.pow <| .collect ["x", "y"] (.ℤ ⨯ᴮ .ℤ) (.eq (.var "x") (.var "y")))
-- #eval B.Term.abstract (.lambda ["x", "y", "z"] (.ℤ ⨯ᴮ .ℤ ⨯ᴮ .𝔹) (.eq (.var "x") (.var "y")))
