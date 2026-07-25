/* Principle: a B lambda is encoded option-valued — `some` inside the domain, `none`
   outside — rather than as a boolean graph. */
/* Check: declare-const ff \(-> Int \(Option Int\)\) */
/* Check: \(some \(\+ x[0-9]+ 1\)\) */
/* Check: \(as none \(Option Int\)\) */
MACHINE M13Lambda
CONSTANTS ff
PROPERTIES
  ff = %xx.(xx ∈ ℕ | xx + 1)
ASSERTIONS
  ff(3) = 4
END
