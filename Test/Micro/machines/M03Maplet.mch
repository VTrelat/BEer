/* Principle: a maplet is an SMT `Pair`, so equality of two maplets is componentwise. */
/* Check: \(and \(= aa cc\) \(= bb dd\)\) */
MACHINE M03Maplet
SETS XX; YY
CONSTANTS aa, bb, cc, dd
PROPERTIES
  aa ∈ XX ∧ bb ∈ YY ∧ cc ∈ XX ∧ dd ∈ YY ∧ (aa ↦ bb) = (cc ↦ dd)
ASSERTIONS
  aa = cc;
  bb = dd
END
