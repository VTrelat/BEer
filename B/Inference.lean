import B.Environment
import SMT.Typing
import Extra.Utils
open Batteries

namespace B

def setlift (Γ : TypeContext) (S : Term) : BType :=
  match S with
  | .ℤ => .int
  | .𝔹 => .bool
  | .collect _ S _ => setlift Γ S
  | .pow S => .set (setlift Γ S)
  | S ⨯ᴮ T => (setlift Γ S) ×ᴮ (setlift Γ T)
  | S ⇸ᴮ T => .set ((setlift Γ S) ×ᴮ (setlift Γ T))
  | .var v => match Γ.find? v with
    | some τ => τ
    | none => panic! "setlift: variable not found"
  | _ => panic! "setlift: not a set"

private def lift_aux : BType → Term
  | .int => Term.ℤ
  | .bool => Term.𝔹
  | .set β => 𝒫ᴮ (lift_aux β)
  | β ×ᴮ γ => lift_aux β ⨯ᴮ lift_aux γ

def setlifttoset (Γ : TypeContext) (S : Term) : Term :=
  match S with
  | .ℤ | .𝔹 => S
  | .collect _ S _ => setlifttoset Γ S
  | .pow S => 𝒫ᴮ (setlifttoset Γ S)
  | S ⨯ᴮ T => (setlifttoset Γ S) ⨯ᴮ (setlifttoset Γ T)
  | S ⇸ᴮ T => 𝒫ᴮ ((setlifttoset Γ S) ⨯ᴮ (setlifttoset Γ T))
  | .var v => match Γ.find? v with
    | some τ => lift_aux τ
    | none => panic! "setlift: variable not found"
  | _ => panic! "setlift: not a set"

def BTypeToSMTType : B.BType → SMT.SMTType
  | .int => .int
  | .bool => .bool
  | .set β => .fun (BTypeToSMTType β) .bool
  | β ×ᴮ γ => .pair (BTypeToSMTType β) (BTypeToSMTType γ)

-- #eval setlift AssocList.nil (.collect "x" (𝒫 .ℤ) (.eq (.var "x") (.ℤ)))

/-

/--
  Infers the type of x in the expression x ∈ᴮ S and returns the updated environment.
-/
def infer (x S : Term) (E : Env) : Env :=
  match x, S with
  | .var v, .ℤ => { E with context := AssocList.insert v .int E.context}
  | .var v, .𝔹 => { E with context := AssocList.insert v .bool E.context}
  | .var _, .collect _ D _ => infer x D {E with defs := E.defs ++ [x ∈ᴮ S]}
  | .var v, 𝒫 S => { E with context := AssocList.insert v (.set (setlift E.context S)) E.context}
  | .var v, S ⨯ᴮ T => { E with context := AssocList.insert v ((setlift E.context S) ×ᴮ (setlift E.context T)) E.context}
  | .var v, S ⇸ᴮ T =>
    let S' := setlift E.context S
    let T' := setlift E.context T
    -- let T'' := setlifttoset E.context T
    -- let τ := SMT.SMTType.option (BTypeToSMTType T')
    { E with
      context := AssocList.insert v (.set (S' ×ᴮ T')) E.context
      flags := v :: E.flags
      po := E.po ++ [(.var v) ∈ᴮ S ⇸ᴮ T]
    }
    /-
    { E with
      context := AssocList.insert v (.set (S' ×ᴮ T')) E.context
      flags := v :: E.flags
      invariants := E.invariants ++
        -- ∀ x ∈ ↑S. f x ≠ none → x ∈ S
        [.all "𝓍" (setlifttoset E.context S) (.imp (.neq (.app (.var v) (.var "𝓍")) (.var s!"none[{τ}]")) (.mem (.var "𝓍") S))] ++
        -- ∀ x ∈ ↑S. f x ≠ none → ∃ y ∈ T. f x = some y
        [.all "𝓍" (setlifttoset E.context S)
          (.imp
            (.neq (.app (.var v) (.var "𝓍")) (.var s!"none[{τ}]"))
            (.exists "𝓎" T''
              (if T = T'' then (.eq (.app (.var v) (.var "𝓍")) (.app (.var "some") (.var "𝓎")))
              else (.and (.mem (.var "𝓎") T) (.eq (.app (.var v) (.var "𝓍")) (.app (.var "some") (.var "𝓎")))))))] -- TODO: this has to go in the simplifier
    } -/
  | .var v, .var v' => match E.context.find? v' with
    | some τ => { E with context := AssocList.insert v τ E.context}
    | none => panic! "infer: variable not found"
  | _, _ => E

/--
  Given a context, a list of types and a list of invariants, we can infer the BEnv.
-/
def inferFromContext (E : Env) (assms : List Term) : Env :=
  match assms with
  | [] => E
  | t :: ts =>
    match t with
    | x ∈ᴮ S => inferFromContext (infer x S E) ts
    | _ => inferFromContext E ts

-- #eval (inferFromContext {} [ .var "f" ∈ᴮ (.collect "x" .ℤ (.eq (.var "x") (.int 0))) ⇸ᴮ .𝔹]).invariants

-/

end B
