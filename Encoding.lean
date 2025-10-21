import B.Inference
open Batteries

section Test

private def lift_aux : BType → BTerm
  | .int => BTerm.ℤ
  | .bool => BTerm.𝔹
  | .set β => 𝒫 (lift_aux β)
  | β ×ᴮ γ => lift_aux β ⨯ᴮ lift_aux γ

def lift (e : BTerm) (pe : Γ ⊢ e : .set α) : BTerm :=
  match h₁ : e, h₂ : α, h₃ : pe with
  | S ⇸ᴮ T, .prod β γ, h =>
    lift S (by obtain ⟨_, ⟨⟩⟩ := h; assumption) ⇸ᴮ lift T (by obtain ⟨_, ⟨⟩⟩ := h; assumption)
  | _, _, _ => lift_aux α

def lift_impl (Γ : TypeContext) (e : BTerm) : BTerm :=
  match e with
  | .ℤ => BTerm.ℤ
  | .𝔹 => BTerm.𝔹
  | 𝒫 A => 𝒫 (lift_impl Γ A)
  | A ⨯ᴮ B => lift_impl Γ A ⨯ᴮ lift_impl Γ B
  | A ⇸ᴮ B => lift_impl Γ A ⇸ᴮ lift_impl Γ B
  | A ∪ᴮ _ | A ∩ᴮ _ | .collect _ A _ => lift_impl Γ A
  | .var v => match Γ.find? v with
    | some τ => match τ with
      | .set α => lift_aux α
      | α ×ᴮ β => lift_aux α ⨯ᴮ lift_aux β
      | _ => panic! s!"lift_impl: {v} is not a set or product type"
    | none => panic! s!"lift_impl: variable {v} not found"
  | _ => panic! "lift_impl: not implemented"

#eval @lift .nil .int (BTerm.collect "x" .ℤ ((.var "x") =ᴮ (.int 0))) (BTyping.collect (BTyping.ℤ) (BTyping.eq (BTyping.var (by rfl)) BTyping.int))
#eval @lift .nil (.set .int) (.collect "E" (𝒫 .ℤ) ((.var "E") =ᴮ (.ℤ))) (BTyping.collect (BTyping.pow BTyping.ℤ) (BTyping.eq (BTyping.var (by rfl)) BTyping.ℤ))


-- ⊢ {x ∈ ℤ | x = 0 ∨ x = 1} : 𝒫 .int --> ↑{x ∈ ℤ | x = 0 ∨ x = 1} = ℤ
#eval toString (BTerm.collect "x" .ℤ ((((.var "x") =ᴮ (.int 0))) ∨ᴮ ((.var "x") =ᴮ (.int 1))))
#eval @lift .nil .int (.collect "x" .ℤ ((((.var "x") =ᴮ (.int 0))) ∨ᴮ ((.var "x") =ᴮ (.int 1)))) (sorry)
#eval lift_impl .nil (.collect "x" .ℤ ((((.var "x") =ᴮ (.int 0))) ∨ᴮ ((.var "x") =ᴮ (.int 1))))

-- [(x, 𝒫 .int)] ⊢ x : 𝒫 .int --> ↑x = ℤ
#eval @lift (AssocList.nil.cons "x" (BType.set BType.int)) (.set .int) (BTerm.var "x") (sorry)
#eval lift_impl (AssocList.nil.cons "x" (BType.set BType.int)) (BTerm.var "x")

end Test

def encode {Env : BEnv} (ht : Env.context ⊢ x ∈ᴮ S : .bool) :=
  let S' := @lift_impl Env.context S
  {Env with types := Env.types ++ [x ∈ᴮ S']}


-- encode x ∈ {x ∈ ℤ | x = 0 ∨ x = 1} knowing [x : int]
#eval (@encode
  (.var "x")
  (.collect "x" .ℤ ((((.var "x") =ᴮ (.int 0))) ∨ᴮ ((.var "x") =ᴮ (.int 1))))
  {context := AssocList.nil.cons "x" BType.int, types := [.var "y" ∈ᴮ .ℤ], axioms := []}
  (BTyping.mem (BTyping.var (by rfl)) (BTyping.collect (BTyping.ℤ) (BTyping.or (BTyping.eq (BTyping.var (by rfl)) BTyping.int) (BTyping.eq (BTyping.var (by rfl)) BTyping.int))))).types

-- encode f ∈ {x ∈ {x ∈ ℤ | x = 0 ∨ x = 1} | ¬ x = 0} ⇸ {x ∈ ℤ | x = 0 ∨ x = 1} knowing [f : int -> int]
#eval (@encode
  (.var "f")
  ((.collect "x" (.collect "x" .ℤ ((((.var "x") =ᴮ (.int 0))) ∨ᴮ ((.var "x") =ᴮ (.int 1)))) ((¬ᴮ ((.var "x") =ᴮ (.int 0)))))
  ⇸ᴮ (.collect "x" .ℤ ((((.var "x") =ᴮ (.int 0))) ∨ᴮ ((.var "x") =ᴮ (.int 1)))))
  {context := AssocList.nil.cons "f" (BType.prod BType.int BType.int), types := [], axioms := []}
  (by admit)).types
