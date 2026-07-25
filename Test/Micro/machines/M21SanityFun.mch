/* Principle: sanity sentinel — two arbitrary total functions need not be equal, so an
   over-constrained option-valued function representation is caught here. */
/* Expect: goals sat */
/* Check: declare-const ff \(-> Int \(Option Int\)\) */
MACHINE M21SanityFun
SETS XX; YY
CONSTANTS ff, gg
PROPERTIES
  ff ∈ XX --> YY ∧ gg ∈ XX --> YY
ASSERTIONS
  ff = gg
END
