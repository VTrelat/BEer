import POGReader
import SMT.Reasoning.ProofObligationUnion

open B

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do
    throw <| IO.userError message

private def isFunctionalUnionGoal (goal : B.SimpleGoal) : Bool :=
  match goal.goal with
  | .all [z]
      (.union (.var f) (.var g))
      (.mem (.var z') (.cprod (.var X) (.var Y))) =>
      z == z' && f == "f" && g == "g" && X == "X" && Y == "Y"
  | _ => false

private def isFunctionHypothesisFor (v : B.𝒱) : B.Term → Bool
  | .mem (.var w) (.pfun _ _) => w == v
  | .mem (.var w) (.collect _ (.pfun _ _) _) => w == v
  | _ => false

private def hasCoveredFunctionalUnionGoal
    (po : B.ProofObligation) : Bool :=
  po.goals.any fun goal =>
    isFunctionalUnionGoal goal &&
      (po.assumptionsFor goal).any (isFunctionHypothesisFor "f")

def main : IO Unit := do
  let pog ← (readPOG "Test/Union.pog").propagateError
  let ⟨(), state⟩ ←
    POGtoB pog |>.run ∅ |>.run |>.propagateError
  let E := state.env

  require (decide ("f" ∈ E.flags))
    "Union regression: f is no longer selected for function representation"
  require (decide ("g" ∉ E.flags))
    "Union regression: relational g was unexpectedly selected as a function"
  require (decide (E.context.lookup "f" =
      some (.set (.prod .int .int))))
    "Union regression: f no longer has relation type int ↔ int"
  require (decide (E.context.lookup "g" =
      some (.set (.prod .int .int))))
    "Union regression: g no longer has relation type int ↔ int"

  require (E.po.all fun po =>
      po.localFlags.all fun v => decide (v ∈ po.localContext))
    "Union regression: a PO-local function flag lacks a local type binding"
  require (E.flags.any fun v => decide (v ∉ E.context))
    "Union regression: expected decoder-bound helper flags disappeared"
  require (E.po.any hasCoveredFunctionalUnionGoal)
    "Union regression: functional-union goal or f function hypothesis missing"

  for po in E.po do
    for goal in po.goals do
      if isFunctionalUnionGoal goal then
        match goal.goal with
        | .all [z] _ _ =>
            require (decide (z ∉ E.flags))
              "Union regression: quantified union binder is flagged"
        | _ => unreachable!

  IO.println "Union representation structure: ok"
