/* Principle: integers map to SMT Int; add / sub / mul / le are direct. */
/* Check: \(\+ aa 1\) */
/* Check: \(\* 2 aa\) */
MACHINE M01Arith
CONSTANTS aa, bb
PROPERTIES
  aa ∈ ℤ ∧ bb ∈ ℤ ∧ aa ≤ bb
ASSERTIONS
  aa + 1 ≤ bb + 1;
  aa - bb ≤ 0;
  2 * aa ≤ 2 * bb
END
