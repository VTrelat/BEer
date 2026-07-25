/* Principle: union of two sets in the same representation is pointwise disjunction. */
/* Check: \(and \(not \(ss xx\)\) \(not \(tt xx\)\)\) */
MACHINE M08Union
SETS XX
CONSTANTS ss, tt, xx
PROPERTIES
  ss ⊆ XX ∧ tt ⊆ XX ∧ xx ∈ ss
ASSERTIONS
  xx ∈ ss ∪ tt;
  ss ⊆ ss ∪ tt
END
