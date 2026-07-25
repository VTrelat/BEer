/* Principle: equality between a function and a relation — the flag analysis gives the
   `<->` variable the functional representation too, and both sides are then loosened
   to graphs for the comparison. */
/* Check: declare-const rr \(-> Int \(Option Int\)\) */
MACHINE M19EqRepr
SETS XX; YY
CONSTANTS ff, rr, aa, bb
PROPERTIES
  ff ∈ XX --> YY ∧ rr ∈ XX <-> YY ∧ ff = rr ∧
  aa ∈ XX ∧ bb ∈ YY ∧ (aa ↦ bb) ∈ rr
ASSERTIONS
  ff(aa) = bb
END
