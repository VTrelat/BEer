import SMT.PHOAS.Def
import Extra.Prettifier

namespace SMT.PHOAS

private def binder {β} [ToString β] {α} (f : α -> Nat -> Std.Format) (p_op : Nat) (binder : String) (vars : List String) (dom : List β) (pred : α) : Nat -> Std.Format :=
  paren (· > p_op) (binder ++ " " ++ ", ".intercalate (vars.zipWith (λ v τ => s!"{v}:{τ}") dom) ++ ", " ++ f pred 0)

partial def Term.pretty : Term String → Nat → Std.Format
  | or x y => «infixl» Term.pretty 40 "∨ˢ" x y
  | imp x y => «infixl» Term.pretty 35 "⇒ˢ" x y
  | .var v => λ _ => v
  | .int n => λ _ => toString n
  | .bool x => λ _ => toString x
  | .and x y => «infixl» Term.pretty 40 "∧ˢ" x y
  | .eq x y => «infix» Term.pretty 40 "=ˢ" x y
  | .le x y => «infixl» Term.pretty 160 "≤ˢ" x y
  | .add x y => «infixl» Term.pretty 180 "+ˢ" x y
  | .sub x y => «infixl» Term.pretty 180 "-ˢ" x y
  | .mul x y => «infixl» Term.pretty 190 "*ˢ" x y
  -- | @Term.exists _ n τs P =>
  --   let x (j : Fin n) := s!"𝐱{j.val.toSubscriptString}"
  --   SMT.PHOAS.binder Term.pretty 0 "∃ˢ" (List.ofFn x) (List.ofFn τs) (P x)
  | .not x => «prefix» Term.pretty 250 "¬ˢ" x
  | @Term.forall String n τs P =>
    let x (j : Fin n) := s!"𝐱{j.val.toSubscriptString}"
    SMT.PHOAS.binder Term.pretty 0 "∀ˢ" (List.ofFn x) (List.ofFn τs) (P x)
  | @Term.lambda _ n τs P =>
    let x (j : Fin n) := s!"𝐱{j.val.toSubscriptString}"
    SMT.PHOAS.binder Term.pretty 0 "λˢ" (List.ofFn x) (List.ofFn τs) (P x)
  | .app f x => λ _ => f.pretty 300 ++ .paren (x.pretty 0)
  | distinct xs => λ _ => "𝐝𝐢𝐬𝐭𝐢𝐧𝐜𝐭" ++ .paren (", ".intercalate <| List.ofFn (fun i ↦ toString <| (xs i).pretty 0))
  | snd x => λ _ => "𝐬𝐧𝐝" ++ .paren (x.pretty 0)
  | fst x => λ _ => "𝐟𝐬𝐭" ++ .paren (x.pretty 0)
  | pair x y => λ _ => "𝐩𝐚𝐢𝐫" ++ .paren (x.pretty 0 ++ ", " ++ y.pretty 0)
  | none τ => λ _ => "𝐚𝐬 " ++ "𝐧𝐨𝐧𝐞" ++ " " ++ τ.toString
  | «()» => λ _ => "()"
  | the x => λ _ => "𝐭𝐡𝐞" ++ .paren (x.pretty 0)
  | some x => λ _ => "𝐬𝐨𝐦𝐞" ++ .paren (x.pretty 0)
  | ite c x y => λ _ => "𝐢𝐟 " ++ c.pretty 0 ++ " 𝐭𝐡𝐞𝐧 " ++ x.pretty 0 ++ " 𝐞𝐥𝐬𝐞 " ++ y.pretty 0

instance : ToString (Term String) := ⟨(Term.pretty · 0 |> ToString.toString)⟩

end SMT.PHOAS
