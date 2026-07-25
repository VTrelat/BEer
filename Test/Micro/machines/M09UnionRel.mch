/* Principle: union across representations — the total function is option-valued and
   must be loosened to a boolean graph before it can be unioned with a relation. */
/* Check: \(or \(union![0-9]+ x[0-9]+\) \(gg x[0-9]+\)\) */
MACHINE M09UnionRel
SETS XX; YY
CONSTANTS ff, gg
PROPERTIES
  ff ∈ XX --> YY ∧ gg ∈ XX <-> YY
ASSERTIONS
  ff ∪ gg ⊆ XX × YY
END
