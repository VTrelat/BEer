/* Principle: POW(S) is a predicate over characteristic predicates, so discharging it
   needs a genuinely second-order quantifier over `(-> Int Bool)`. */
/* Check: exists \(\(x[0-9]+ \(-> Int Bool\)\)\) */
MACHINE M06Pow
SETS XX
CONSTANTS ss, tt
PROPERTIES
  ss ⊆ XX ∧ tt ⊆ XX
ASSERTIONS
  ss ∪ tt ∈ POW(XX);
  POW(ss) ⊆ POW(XX)
END
