/* Principle: card is an uninterpreted measure constrained by the encoder's axioms. */
/* Expect: BEer unsupported — the `.card` branch is commented out in Encoder/Encoder.lean:229, so encodeTerm falls through to the catch-all at line 410. */
MACHINE M12Card
CONSTANTS ss
PROPERTIES
  ss = {1, 2, 3}
ASSERTIONS
  card(ss) = 3
END
