import B.Syntax.Basic
import Extra.Prettifier
import Extra.GetOption

namespace B

-- Disjunction
@[match_pattern]
def Term.or (x y : Term) := ¬ᴮ ((¬ᴮ x) ∧ᴮ (¬ᴮ y))
infixl:40 " ∨ᴮ " => Term.or

-- Implication
@[match_pattern]
def Term.imp (x y : Term) := (¬ᴮ x) ∨ᴮ y
infixr:20 " ⇒ᴮ " => Term.imp
-- Equivalence
@[match_pattern]
def Term.iff (x y : Term) := (x ⇒ᴮ y) ∧ᴮ (y ⇒ᴮ x)
infixr:20 " ⇔ᴮ " => Term.iff
@[match_pattern]
def Term.neq (x y : Term) := ¬ᴮ (x =ᴮ y)
infixl:40 " ≠ᴮ " => Term.neq

def Term.nexp (x : Term) : Nat → Term
  | 0 => .int 1
  | 1 => x
  | n + 1 => .mul x (Term.nexp x n)

def Term.exp (x : Term) (n : Int) : Term :=
  if npos : n < 0 then
    let m := n.toNat
    if m % 2 = 0 then Term.nexp x m else .int (-1) *ᴮ Term.nexp x m
  else Term.nexp x (n.toNat?.get (by
    rw [Int.not_gt_eq] at npos
    cases n
    · rfl
    · nomatch (Int.negSucc_not_nonneg _).mp npos))
infixl:200 "^ᴮ" => Term.exp

-- Existential
@[match_pattern]
def Term.exists (v : List 𝒱) (D P : Term) := ¬ᴮ (.all v D (¬ᴮ P))

-- Binary relation
@[match_pattern]
def Term.brel (x y : Term) := (x ⨯ᴮ y) ⇸ᴮ .𝔹

abbrev Term.MAXINT : Term := .int 2147483647
abbrev Term.MININT : Term := .int (-2147483647)
abbrev 𝒱.isReserved (v : 𝒱) : Bool := v ∈ ["NATURAL", "NAT", "NAT1", "INT", "INTEGER", "BOOL"]

partial def Term.pretty (b : Bool) : Term -> Nat -> Std.Format
  | .var v => λ _ => (bif b then if v.isReserved then RED else GREEN else id) v
  | .int n => λ _ => (bif b then BLUE else id) <| toString n
  | .bool x => λ _ => (bif b then BLUE else id) <| toString x
  | .ℤ => λ _ => (bif b then RED else id) "ℤ"
  | .𝔹 => λ _ => (bif b then RED else id) "𝔹"
  | .imp x y => «infixr» (Term.pretty b) 30 "⇒ᴮ" x y -- /!\ see manrefb p.198
  | .or x y => «infixl» (Term.pretty b) 40 "∨ᴮ" x y
  | .and x y => «infixl» (Term.pretty b) 40 "∧ᴮ" x y
  | .eq x y => «infix» (Term.pretty b) 40 "=ᴮ" x y
  | .mem x S => «infixl» (Term.pretty b) 120 "∈ᴮ" x S
  | .brel x y => «infix» (Term.pretty b) 125 "↔" x y
  | .pfun A B => «infixr» (Term.pretty b) 125 "⇸ᴮ" A B
  | .neq x y => «infix» (Term.pretty b) 160 "≠ᴮ" x y
  | .le x y => «infixl» (Term.pretty b) 160 "≤ᴮ" x y
  | .inter x y => «infixl» (Term.pretty b) 160 "∩ᴮ" x y
  | .union x y => «infixl» (Term.pretty b) 160 "∪ᴮ" x y
  | .maplet x y => «infixl» (Term.pretty b) 160 "↦ᴮ" x y
  | .add x y => «infixl» (Term.pretty b) 180 "+ᴮ" x y
  | .sub x y => «infixl» (Term.pretty b) 180 "-ᴮ" x y
  | .mul x y => «infixl» (Term.pretty b) 190 "*ᴮ" x y
  | .cprod x y => «infixl» (Term.pretty b) 190 "⨯ᴮ" x y
  | .exists v D P => binder (Term.pretty b) 250 "∃ᴮ " (v.map (bif b then GREEN else id)).toString' " ∈ᴮ " D ". " P ""
  | .not x => «prefix» (Term.pretty b) 250 "¬ᴮ" x
  | .all v D P => binder (Term.pretty b) 0 "∀ᴮ " (v.map (bif b then GREEN else id)).toString' " ∈ᴮ " D ". " P ""
  | .collect v D P => binder (Term.pretty b) 250 "{ " (v.map (bif b then GREEN else id)).toString' " ∈ᴮ " D " | " P " }"
  | .lambda v D P => binder (Term.pretty b) 0 "λᴮ " (v.map (bif b then GREEN else id)).toString' " ∈ᴮ " D ". " P ""
  | .app f x => λ _ => Term.pretty b f 300 ++ .paren (Term.pretty b x 0)
  | .pow S => «prefix» (Term.pretty b) 290 "𝒫 " S
  | .min S => «prefix» (Term.pretty b) 290 "min " S
  | .max S => «prefix» (Term.pretty b) 290 "max " S
  | .card S => λ _ => "‖" ++ Term.pretty b S 0 ++ "‖ᴮ"

end B

instance : ToString B.Term := ⟨(B.Term.pretty false · 0 |> ToString.toString)⟩
