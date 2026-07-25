/* Principle: a B universal quantifier becomes an SMT binder over the translated
   bound-variable type, with the guard as an implication. */
/* Check: \(exists \(\(x[0-9]+ Int\)\) \(and \(XX x[0-9]+\) \(not \(ss x[0-9]+\)\)\)\) */
MACHINE M17Forall
SETS XX
CONSTANTS ss
PROPERTIES
  ss ⊆ XX ∧ ∀ xx . (xx ∈ XX ⇒ xx ∈ ss)
ASSERTIONS
  XX ⊆ ss
END
