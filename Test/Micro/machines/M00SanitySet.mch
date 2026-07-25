/* Principle: sanity sentinel — a non-theorem about sets must stay satisfiable, so
   an encoding whose hypotheses are contradictory (and which would therefore make
   every other machine trivially `unsat`) is caught here. */
/* Expect: goals sat */
/* Check: declare-const ss \(-> Int Bool\) */
MACHINE M00SanitySet
SETS XX
CONSTANTS ss, tt, xx
PROPERTIES
  ss ⊆ XX ∧ tt ⊆ XX ∧ xx ∈ ss ∪ tt
ASSERTIONS
  xx ∈ ss ∩ tt
END
