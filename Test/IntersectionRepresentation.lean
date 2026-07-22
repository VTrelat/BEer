import POGReader
import Encoder.Loosening.Loosening
import SMT.Reasoning.ProofObligationRepresented

open SMT

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do
    throw <| IO.userError message

private def isGuardedOptionIntersection
    (left right : SMT.Term) (argTy retTy : SMTType) : SMT.Term → Bool
  | .lambda [x] [binderTy]
      (.ite
        (.eq (.app lhs (.var xGuardLeft))
          (.app rhs (.var xGuardRight)))
        (.app payload (.var xPayload))
        (.as .none (.option noneTy))) =>
      binderTy == argTy && noneTy == retTy &&
        x == xGuardLeft && x == xGuardRight && x == xPayload &&
        lhs == left && rhs == right && payload == left
  | _ => false

private def checkDirect : IO Unit := do
  let ty : SMTType := .fun .int (.option .bool)
  match (castInter (.var "S", ty) (.var "T", ty)).run
      (∅ : EncoderState) with
  | .error e =>
      throw <| IO.userError s!"direct option intersection failed: {e}"
  | .ok ((term, outTy), state) =>
      require (outTy == ty)
        "direct option intersection changed representation"
      require (isGuardedOptionIntersection (.var "S") (.var "T")
        .int .bool term)
        "direct option intersection is not the guarded option lambda"
      require state.env.declarations.isEmpty
        "direct option intersection unexpectedly emitted declarations"
      require state.types.keys.isEmpty
        "direct option intersection leaked its lambda binder into the context"

private def checkHeterogeneous : IO Unit := do
  -- A set of integer pairs can itself be represented either as an
  -- option-valued function or as a characteristic predicate.  Using those as
  -- outer function arguments forces a genuinely non-reflexive `.fun` cast.
  let innerFun : SMTType := .fun .int (.option .int)
  let innerGraph : SMTType := .fun (.pair .int .int) .bool
  let leftTy : SMTType := .fun innerFun (.option .int)
  let rightTy : SMTType := .fun innerGraph (.option .int)
  match (castInter (.var "S", leftTy) (.var "T", rightTy)).run
      (∅ : EncoderState) with
  | .error e =>
      throw <| IO.userError s!"heterogeneous option intersection failed: {e}"
  | .ok ((term, outTy), state) =>
      require (outTy == rightTy)
        "heterogeneous option intersection did not return the looser type"
      match state.env.declarations with
      | [.declare_const helper helperTy,
          .define_fun specName .unit .bool _] =>
          require (helperTy == rightTy)
            "heterogeneous option intersection declared the wrong helper type"
          require (specName == s!"{helper}_spec")
            "heterogeneous option intersection emitted the wrong helper spec"
          require (state.types.lookup helper == some rightTy)
            "heterogeneous option intersection did not retain its helper type"
          require (isGuardedOptionIntersection (.var helper) (.var "T")
            innerGraph .int term)
            "heterogeneous option intersection is not guarded at the looser type"
      | _ =>
          throw <| IO.userError
            "heterogeneous option intersection did not emit exactly one helper/spec pair"

private def isFunctionalIntersectionGoal (goal : B.SimpleGoal) : Bool :=
  match goal.goal with
  | .all [z]
      (.inter (.var f) (.var g))
      (.mem (.var z') (.cprod (.var X) (.var Y))) =>
      z == z' && f == "f" && g == "g" && X == "X" && Y == "Y"
  | _ => false

private def isFunctionHypothesisFor (v : B.𝒱) : B.Term → Bool
  | .mem (.var w) (.pfun _ _) => w == v
  | .mem (.var w) (.collect _ (.pfun _ _) _) => w == v
  | _ => false

private def hasCoveredFunctionalIntersectionGoal
    (po : B.ProofObligation) : Bool :=
  po.goals.any fun goal =>
    isFunctionalIntersectionGoal goal &&
      (po.assumptionsFor goal).any (isFunctionHypothesisFor "f") &&
      (po.assumptionsFor goal).any (isFunctionHypothesisFor "g")

private def checkPOG : IO Unit := do
  let pog ← (readPOG "Test/Intersection.pog").propagateError
  let ⟨(), state⟩ ←
    POGtoB pog |>.run ∅ |>.run |>.propagateError
  let E := state.env
  require (decide ("f" ∈ E.flags && "g" ∈ E.flags))
    "intersection MWE did not select both operands as functions"
  require (decide (E.context.lookup "f" =
      some (.set (.prod .int .int))))
    "intersection MWE decoded the wrong type for f"
  require (decide (E.context.lookup "g" =
      some (.set (.prod .int .int))))
    "intersection MWE decoded the wrong type for g"
  require (E.po.any hasCoveredFunctionalIntersectionGoal)
    "functional intersection goal or function hypotheses are missing"

def main : IO Unit := do
  checkDirect
  checkHeterogeneous
  checkPOG
  IO.println "Intersection representation branches and POG structure: ok"
