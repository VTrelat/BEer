/* Principle: application of a total function goes through `the` on the option-valued
   representation, via a freshly declared application constant. */
/* Check: \(the \(app![0-9]+ aa\)\) */
MACHINE M15App
SETS XX; YY
CONSTANTS ff, aa
PROPERTIES
  ff ∈ XX --> YY ∧ aa ∈ XX
ASSERTIONS
  ff(aa) ∈ YY;
  (aa ↦ ff(aa)) ∈ ff
END
