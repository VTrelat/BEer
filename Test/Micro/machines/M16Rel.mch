/* Principle: a relation stays a boolean graph over pairs — no functional
   representation is imposed on it. */
/* Check: declare-const rr \(-> \(Pair Int Int\) Bool\) */
MACHINE M16Rel
SETS XX; YY
CONSTANTS rr, aa, bb
PROPERTIES
  rr ∈ XX <-> YY ∧ aa ∈ XX ∧ bb ∈ YY ∧ (aa ↦ bb) ∈ rr
ASSERTIONS
  rr ⊆ XX × YY;
  ¬(rr = {})
END
