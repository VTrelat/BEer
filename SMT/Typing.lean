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

abbrev TypeContext := AList fun _ : 𝒱 ↦ SMTType

def TypeContext.update (Γ : TypeContext) (vs : List 𝒱) (τs : List SMTType)
    (hlen : vs.length = τs.length := by assumption) : TypeContext :=
  Fin.foldl vs.length (fun Δ i ↦ Δ.insert vs[i] τs[i]) Γ

end SMT
