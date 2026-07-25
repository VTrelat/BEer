/* Principle: BOOL maps to SMT Bool, and B equality on booleans is SMT `=`, so a
   boolean constant is asserted directly rather than through a coercion. */
/* Check: declare-const pp Bool */
/* Check: \(assert \(not pp\)\) */
MACHINE M02Bool
CONSTANTS pp, qq
PROPERTIES
  pp ∈ BOOL ∧ qq ∈ BOOL ∧ pp = TRUE
ASSERTIONS
  ¬(pp = FALSE);
  pp = TRUE ∧ (qq = TRUE ∨ qq = FALSE)
END
