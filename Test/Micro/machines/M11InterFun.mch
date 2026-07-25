/* Principle: functional intersection — the intersection of two partial functions stays
   a partial function, encoded pointwise as `ite (f x = g x) (f x) none` instead of
   being demoted to a graph. */
/* Check: \(ite \(= \(ff \(fst [^)]*\)\) \(gg \(fst */
MACHINE M11InterFun
SETS XX; YY
CONSTANTS ff, gg
PROPERTIES
  ff ∈ XX +-> YY ∧ gg ∈ XX +-> YY
ASSERTIONS
  ff ∩ gg ∈ XX +-> YY
END
