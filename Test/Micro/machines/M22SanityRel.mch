/* Principle: sanity sentinel — a relation may map one point to two values, so this
   is the exact non-theorem counterpart of M14PFun and it catches a flag analysis
   that wrongly commits a `<->` variable to the functional representation. */
/* Expect: goals sat */
/* Check: declare-const rr \(-> \(Pair Int Int\) Bool\) */
MACHINE M22SanityRel
SETS XX; YY
CONSTANTS rr, aa, bb, cc
PROPERTIES
  rr ∈ XX <-> YY ∧ aa ∈ XX ∧ bb ∈ YY ∧ cc ∈ YY ∧
  (aa ↦ bb) ∈ rr ∧ (aa ↦ cc) ∈ rr
ASSERTIONS
  bb = cc
END
