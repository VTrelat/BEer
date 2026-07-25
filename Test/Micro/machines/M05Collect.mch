/* Principle: a set comprehension becomes a lambda-abstracted characteristic predicate. */
/* Check: \(= ss \(lambda \(\(x[0-9]+ Int\)\) \(not \(<= x[0-9]+ 0\)\)\)\) */
MACHINE M05Collect
CONSTANTS ss
PROPERTIES
  ss = {xx | xx ∈ ℤ ∧ 0 < xx}
ASSERTIONS
  5 ∈ ss;
  ¬(0 ∈ ss)
END
