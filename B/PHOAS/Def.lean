import B.PHOAS.Basic
import Extra.Prettifier
-- def plus : Term :=
--   .lambda λ x => .lambda λ y => .add (.var x) (.var y)

namespace B.PHOAS

partial def Term.pretty : Term String → Nat → Std.Format
  | .var v => λ _ => v
  | .int n => λ _ => toString n
  | .bool x => λ _ => toString x
  | .ℤ => λ _ => "ℤ"
  | .𝔹 => λ _ => "𝔹"
  | .and x y => «infixl» Term.pretty 40 "∧ᴮ" x y
  | .eq x y => «infix» Term.pretty 40 "=ᴮ" x y
  | .mem x S => «infixl» Term.pretty 120 "∈ᴮ" x S
  | .pfun A B => «infixr» Term.pretty 125 "⇸ᴮ" A B
  | .le x y => «infixl» Term.pretty 160 "≤ᴮ" x y
  | .inter x y => «infixl» Term.pretty 160 "∩ᴮ" x y
  | .union x y => «infixl» Term.pretty 160 "∪ᴮ" x y
  | .maplet x y => «infixl» Term.pretty 160 "↦ᴮ" x y
  | .add x y => «infixl» Term.pretty 180 "+ᴮ" x y
  | .sub x y => «infixl» Term.pretty 180 "-ᴮ" x y
  | .mul x y => «infixl» Term.pretty 190 "*ᴮ" x y
  | .cprod x y => «infixl» Term.pretty 190 "⨯ᴮ" x y
  | .not x => «prefix» Term.pretty 250 "¬ᴮ" x
  | @Term.all _ n D P =>
    let x (j : Fin n) := s!"𝐱{j.val.toSubscriptString}"
    let vars := ", ".intercalate (List.range n |>.attach.map (λ ⟨i, hi⟩ => x ⟨i, List.mem_range.mp hi⟩))
    binder Term.pretty 0 "∀ᴮ " vars " ∈ᴮ " D ". " (P x) ""
  | @Term.collect _ n D P =>
    let x (j : Fin n) := s!"𝐱{j.val.toSubscriptString}"
    let vars := ", ".intercalate (List.range n |>.attach.map (λ ⟨i, hi⟩ => x ⟨i, List.mem_range.mp hi⟩))
    binder Term.pretty 250 "{ " vars " ∈ᴮ " D " | " (P x) " }"
  | @Term.lambda _ n D P =>
    let x (j : Fin n) := s!"𝐱{j.val.toSubscriptString}"
    let vars := ", ".intercalate (List.range n |>.attach.map (λ ⟨i, hi⟩ => x ⟨i, List.mem_range.mp hi⟩))
    binder Term.pretty 0 "λᴮ " vars " ∈ᴮ " D ". " (P x) ""
  | .app f x => λ _ => Term.pretty f 300 ++ .paren (Term.pretty x 0)
  | .pow S => «prefix» Term.pretty 290 "𝒫 " S
  | .min S => «prefix» Term.pretty 290 "min " S
  | .max S => «prefix» Term.pretty 290 "max " S
  | .card S => λ _ => "|" ++ Term.pretty S 0 ++ "|ᴮ"

instance : ToString (Term String) := ⟨(Term.pretty · 0 |> ToString.toString)⟩

end B.PHOAS
