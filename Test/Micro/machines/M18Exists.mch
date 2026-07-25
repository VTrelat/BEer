/* Principle: an existential over a function witness stays in the higher-order
   fragment — the bound variable keeps the function type instead of being flattened. */
/* Expect: BEer incomplete — cvc5 does not synthesise the higher-order witness; both ppTrans variants discharge it after flattening to first order. */
/* Check: forall \(\(x[0-9]+ \(-> Int \(Option Int\)\)\)\) */
MACHINE M18Exists
SETS XX; YY
CONSTANTS ff, aa
PROPERTIES
  ff ∈ XX --> YY ∧ aa ∈ XX
ASSERTIONS
  ∃ gg . (gg ∈ XX --> YY ∧ gg(aa) = ff(aa))
END
