import B.SemanticsPHOAS

/-
  # Well-Definedness of B PHOAS Terms

  `WellDefined` collects the side conditions under which every *partial*
  operation occurring in a B PHOAS term actually denotes. It is the B-method
  analogue of Atelier B's well-definedness proof obligations.

  B's `denote` is total on the structural constructors but partial on:

  * `app f x`  — needs `⟦f⟧ᴮ` to be a partial function (`IsPFunc`) with
    `⟦x⟧ᴮ` in its domain;
  * `card S`   — needs `⟦S⟧ᴮ` finite;
  * `min S` / `max S` — need `⟦S⟧ᴮ` finite and nonempty.

  `WellDefined` carries exactly those conditions (semantic — they refer to the
  denotations of subterms — since finiteness and domain membership are not
  syntactic). It is intended to be fed as an extra hypothesis into
  `B.PHOAS.denote_exists_of_typing`, closing its `app`/`card`/`min`/`max` cases.
-/

open B Classical PHOAS ZFSet

namespace B.PHOAS

/-- Well-definedness of a B PHOAS term: the partial operations `app`, `card`,
`min`, `max` carry the semantic side condition that makes them denote; every
other constructor just propagates well-definedness to its subterms. -/
def WellDefined : PHOAS.Term B.Dom → Prop
  | .var _ | .int _ | .bool _ | .ℤ | .𝔹 => True
  | .not x | .pow x => WellDefined x
  | .maplet x y | .add x y | .sub x y | .mul x y | .le x y | .and x y | .eq x y
  | .mem x y | .cprod x y | .union x y | .inter x y | .pfun x y =>
      WellDefined x ∧ WellDefined y
  | .collect D P | .lambda D P | .all D P =>
      WellDefined D ∧ ∀ vs, WellDefined (P vs)
  | .card S =>
      WellDefined S ∧ ∀ D, ⟦S⟧ᴮ = some D → D.1.IsFinite
  | .min S | .max S =>
      WellDefined S ∧ ∀ D, ⟦S⟧ᴮ = some D → D.1.IsFinite ∧ D.1.Nonempty
  | .app f x =>
      WellDefined f ∧ WellDefined x ∧
      ∀ Df Dx, ⟦f⟧ᴮ = some Df → ⟦x⟧ᴮ = some Dx →
        (∀ τ σ, Df.2.1 = .set (τ ×ᴮ σ) → Df.1.IsPFunc τ.toZFSet σ.toZFSet) ∧
          ∃ y, Dx.1.pair y ∈ Df.1

end B.PHOAS
