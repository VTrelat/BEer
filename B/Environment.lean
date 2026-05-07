import B.Typing
import Extra.Utils

open Batteries

namespace B

structure SimpleGoal where
  hyps : List Term
  goal : Term

instance : ToString SimpleGoal where
  toString sg := s!"simple goal: {sg.hyps} ⊢ {sg.goal}"

structure ProofObligation where
  defs : List Term
  hyps : List Term
  goals : List SimpleGoal
  /-- Type bindings introduced *only* during this PO's decoding. Atelier B
  emits PO-local fresh names (e.g. `s392`) that may be reused across POs with
  different types. Keeping them here (rather than in the global `Env.context`)
  isolates each PO's namespace. -/
  localContext : TypeContext := ∅
  /-- Function-flag entries introduced only during this PO's decoding. -/
  localFlags : List 𝒱 := []

instance : ToString ProofObligation where
  toString po := s!"PO:\ndefs:\n{po.defs.printLines}\nhyps:\n{po.hyps.printLines}\n⊢\n{po.goals.printLines}"

instance : EmptyCollection ProofObligation where
  emptyCollection := { defs := [], hyps := [], goals := [], localContext := ∅, localFlags := [] }

abbrev TermContext := AList (λ _ : 𝒱 => Term)

structure Env where
  context : TypeContext := ∅
  flags : List 𝒱 := []
  freshvarsc : Nat := 0
  defs : TermContext := ∅
  po : List ProofObligation := []
  hypotheses : AssocList DefinitionType <| List Term := AssocList.nil
    |>.cons .ctx []
    |>.cons .seext []
    |>.cons .inv []
    |>.cons .ass []
    |>.cons .lprp []
    |>.cons .inprp []
    |>.cons .inext []
    |>.cons .cst []
    |>.cons .sets []
    |>.cons .mchcst []
    |>.cons .aprp []
    |>.cons .abs []
    |>.cons .imlprp []
    |>.cons .imprp []
    |>.cons .imext []
  distinct : List (List Term) := []
  finite : List Term := []

instance : Inhabited Env := ⟨{}⟩
instance : EmptyCollection Env where
  emptyCollection :=
  { context := (∅ : TypeContext).insert "n" .int |>.insert "b" .bool
    |>.insert "NATURAL" (.set .int)
    |>.insert "NATURAL1" (.set .int)
    |>.insert "NAT" (.set .int)
    |>.insert "NAT1" (.set .int)
    |>.insert "INT" (.set .int)
    |>.insert "INTEGER" (.set .int)
    |>.insert "BOOL" (.set .bool),
    defs := (∅ : TermContext)
      |>.insert "NATURAL" (.collect ["n"] .ℤ (.le (.int 0) (.var "n")))
      |>.insert "NATURAL1" (.collect ["n"] .ℤ (.le (.int 1) (.var "n")))
      |>.insert "NAT" (.collect ["n"] .ℤ (.and (.le (.int 0) (.var "n")) (.le (.var "n") (.int MAXINT))))
      |>.insert "NAT1" (.collect ["n"] .ℤ (.and (.le (.int 1) (.var "n")) (.le (.var "n") (.int MAXINT))))
      |>.insert "INT" (.collect ["n"] .ℤ (.and (.le (.int MININT) (.var "n")) (.le (.var "n") (.int MAXINT))))
      |>.insert "INTEGER" (.collect ["n"] .ℤ (.bool true))
      |>.insert "BOOL" (.collect ["b"] .𝔹 (.bool true)) -- TODO: add missing predefined sets
  }

def EnvToStringAux : AssocList DefinitionType (List Term) → String
  | .nil => ""
  | .cons k v hs => (if v.isEmpty then "" else s!"{nltab}{k}:{nl}{v.printLines}") ++ EnvToStringAux hs
  where nl := "\n"; nltab := nl++"  "

instance : ToString Env where
  toString E :=
    let nl := "\n"
    let nltab := nl++"  "
    s!"Env:{nltab}proof obligations:{nl}{E.po.printLines}{nl}"
      ++ EnvToStringAux E.hypotheses
      ++ s!"{nltab}distinct:{nl}{List.printLines E.distinct}"
      ++ s!"{nl++nltab}context: {E.context}{nltab}flags: {E.flags}{nltab}freshvarsc: {E.freshvarsc}"

end B
