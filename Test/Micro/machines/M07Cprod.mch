/* Principle: S × T is a predicate on pairs, reconstructed from the two components. */
/* Check: \(pair x[0-9]+ x[0-9]+\) */
MACHINE M07Cprod
SETS XX; YY
CONSTANTS ss, tt, aa, bb
PROPERTIES
  ss ⊆ XX ∧ tt ⊆ YY ∧ aa ∈ ss ∧ bb ∈ tt
ASSERTIONS
  (aa ↦ bb) ∈ ss × tt;
  ss × tt ⊆ XX × YY
END
