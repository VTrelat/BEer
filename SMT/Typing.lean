import SMT.Syntax
import Extra.Utils

/-!
# SMT type contexts

`beer-lite` keeps only the *runtime* part of the SMT typing layer: the type
context the encoder uses to track the SMT type of every symbol in scope.
The `⊢ˢ` typing judgment, its inversion lemmas and the weakening /
strengthening theory live in the certified branch and are not needed to run
the translator.
-/

namespace SMT

/-- A hash map rather than an association list: the encoder inserts a binding
per fresh variable, which made every insert linear in the size of the context.
Iteration order is therefore unspecified — only the *set* of declarations
matters, since they all precede the assertions that use them. -/
abbrev TypeContext := Std.HashMap 𝒱 SMTType

def TypeContext.update (Γ : TypeContext) (vs : List 𝒱) (τs : List SMTType)
    (hlen : vs.length = τs.length := by assumption) : TypeContext :=
  Fin.foldl vs.length (fun Δ i ↦ Δ.insert vs[i] τs[i]) Γ

end SMT
