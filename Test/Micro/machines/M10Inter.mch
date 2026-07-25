/* Principle: intersection of two sets in the same representation is pointwise conjunction. */
/* Check: \(and \(ss xx\) \(tt xx\)\) */
MACHINE M10Inter
SETS XX
CONSTANTS ss, tt, xx
PROPERTIES
  ss ⊆ XX ∧ tt ⊆ XX ∧ xx ∈ ss ∩ tt
ASSERTIONS
  xx ∈ ss;
  ss ∩ tt ⊆ tt
END
