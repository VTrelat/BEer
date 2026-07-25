/* Principle: min / max are encoded as constrained witnesses of the set, not as folds. */
/* Expect: BEer unsupported — the `.min` / `.max` branches are commented out in Encoder/Encoder.lean:325-326. */
MACHINE M20MinMax
CONSTANTS ss
PROPERTIES
  ss = {2, 5, 9}
ASSERTIONS
  min(ss) = 2;
  max(ss) = 9
END
