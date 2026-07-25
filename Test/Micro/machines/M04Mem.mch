/* Principle: a set is its characteristic predicate, so `∈` is plain application. */
/* Check: \(assert \(not \(tt xx\)\)\) */
MACHINE M04Mem
SETS XX
CONSTANTS ss, tt, xx
PROPERTIES
  ss ⊆ XX ∧ tt ⊆ XX ∧ xx ∈ ss ∧ ss ⊆ tt
ASSERTIONS
  xx ∈ tt
END
