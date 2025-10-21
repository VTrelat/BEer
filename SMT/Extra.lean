import SMT.Typing
import SMT.Environment
import Extra.Prettifier

namespace SMT
/-
protected def TypeContext.repr (a : TypeContext) (n : Nat) : Std.Format :=
  let _ : Lean.ToFormat (𝒱 × SMTType) := ⟨λ (v, τ) => repr v ++ " : " ++ τ.toString⟩
  match a, n with
  | .nil, _ => "[]"
  | as, _ => .bracket "[" (.joinSep as.toList ("," ++ .line)) "]"
instance : Repr TypeContext := ⟨TypeContext.repr⟩

instance : ToString TypeContext := ⟨λ Γ => "[" ++ (", ".intercalate (Γ.toList.map fun (v, τ) => v ++ " : " ++ toString τ)) ++ "]"⟩

-/
