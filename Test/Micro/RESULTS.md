# Atomic encoding regressions — BEer vs ppTrans

Each machine in `Test/Micro/machines` isolates one principle of the encoding.
Every proof obligation is a theorem, so **`unsat` on every goal is the expected
answer**: `sat` means the translation lost information, `unknown` means it is
incomplete. Solver: cvc5 `--incremental --mbqi --tlimit-per=3000`, answers
listed in file order, one token per `(check-sat)`.

The sentinel machines are deliberate non-theorems: for them `sat` is the expected
answer, and `unsat` would mean the encoded hypotheses are contradictory.

| machine | principle | BEer verdict | BEer | ppTrans (smt) | ppTrans (pog) |
|---|---|---|---|---|---|
| `M00SanitySet` | sanity sentinel — a non-theorem about sets must stay satisfiable, so an encoding whose hypotheses are contradictory (and which would therefore make every other machine trivially `unsat`) is caught here. **(sentinel: `sat` expected)** | PASS | sat (0.008s) | unknown(TIMEOUT) (3.014s) | unknown(TIMEOUT) (3.008s) |
| `M01Arith` | integers map to SMT Int; add / sub / mul / le are direct. | PASS | unsat unsat unsat (0.006s) | unsat unsat unsat (0.007s) | unsat unsat unsat (0.005s) |
| `M02Bool` | BOOL maps to SMT Bool, and B equality on booleans is SMT `=`, so a boolean constant is asserted directly rather than through a coercion. | PASS | unsat unsat (0.005s) | unsat unsat (0.007s) | unsat unsat (0.004s) |
| `M03Maplet` | a maplet is an SMT `Pair`, so equality of two maplets is componentwise. | PASS | unsat unsat (0.006s) | unsat unsat (0.009s) | unsat unsat (0.006s) |
| `M04Mem` | a set is its characteristic predicate, so `∈` is plain application. | PASS | unsat (0.006s) | unsat (0.009s) | unsat (0.007s) |
| `M05Collect` | a set comprehension becomes a lambda-abstracted characteristic predicate. | PASS | unsat unsat (0.006s) | unsat unsat (0.008s) | unsat unsat (0.005s) |
| `M06Pow` | POW(S) is a predicate over characteristic predicates, so discharging it needs a genuinely second-order quantifier over `(-> Int Bool)`. | PASS | unsat (0.007s) | unsat (0.010s) | unsat (0.007s) |
| `M07Cprod` | S × T is a predicate on pairs, reconstructed from the two components. | PASS | unsat unsat (0.007s) | unsat unsat (0.011s) | unsat unsat (0.008s) |
| `M08Union` | union of two sets in the same representation is pointwise disjunction. | PASS | unsat unsat (0.006s) | unsat unsat (0.008s) | unsat unsat (0.006s) |
| `M09UnionRel` | union across representations — the total function is option-valued and must be loosened to a boolean graph before it can be unioned with a relation. | PASS | unsat (0.010s) | unsat (0.012s) | unsat (0.011s) |
| `M10Inter` | intersection of two sets in the same representation is pointwise conjunction. | PASS | unsat unsat (0.006s) | unsat unsat (0.008s) | unsat unsat (0.006s) |
| `M11InterFun` | functional intersection — the intersection of two partial functions stays a partial function, encoded pointwise as `ite (f x = g x) (f x) none` instead of being demoted to a graph. | PASS | unsat (0.011s) | unsat (0.011s) | unsat (0.008s) |
| `M12Card` | card is an uninterpreted measure constrained by the encoder's axioms. | KNOWN GAP (ENCODE ERROR) | `error: Unsupported term ‖ss‖ᴮ ` | unknown(TIMEOUT) (3.029s) | sat (0.011s) |
| `M13Lambda` | a B lambda is encoded option-valued — `some` inside the domain, `none` outside — rather than as a boolean graph. | PASS | unsat (0.009s) | unsat (0.008s) | solver error |
| `M14PFun` | the partial function space X +-> Y is a predicate over option-valued functions, so functionality is built into the representation; membership of a maplet loosens that function to its graph. | PASS | unsat (0.008s) | unsat (0.012s) | unsat (0.009s) |
| `M15App` | application of a total function goes through `the` on the option-valued representation, via a freshly declared application constant. | PASS | unsat (0.028s) | unsat (0.009s) | unsat (0.006s) |
| `M16Rel` | a relation stays a boolean graph over pairs — no functional representation is imposed on it. | PASS | unsat unsat (0.007s) | unsat unsat (0.011s) | unsat unsat (0.008s) |
| `M17Forall` | a B universal quantifier becomes an SMT binder over the translated bound-variable type, with the guard as an implication. | PASS | unsat (0.006s) | unsat (0.008s) | unsat (0.006s) |
| `M18Exists` | an existential over a function witness stays in the higher-order fragment — the bound variable keeps the function type instead of being flattened. | KNOWN GAP (INCOMPLETE) | unknown(INCOMPLETE) (0.061s) | unsat (0.117s) | unsat (0.059s) |
| `M19EqRepr` | equality between a function and a relation — the flag analysis gives the `<->` variable the functional representation too, and both sides are then loosened to graphs for the comparison. | PASS | unsat (0.020s) | unsat (0.011s) | unsat (0.008s) |
| `M20MinMax` | min / max are encoded as constrained witnesses of the set, not as folds. | KNOWN GAP (ENCODE ERROR) | `error: Unsupported term min ss ` | unsat unsat (0.009s) | unsat unsat (0.006s) |
| `M21SanityFun` | sanity sentinel — two arbitrary total functions need not be equal, so an over-constrained option-valued function representation is caught here. **(sentinel: `sat` expected)** | PASS | sat (0.033s) | unknown(TIMEOUT) (3.058s) | unknown(TIMEOUT) (3.011s) |
| `M22SanityRel` | sanity sentinel — a relation may map one point to two values, so this is the exact non-theorem counterpart of M14PFun and it catches a flag analysis that wrongly commits a `<->` variable to the functional representation. **(sentinel: `sat` expected)** | PASS | sat (0.010s) | unknown(TIMEOUT) (3.038s) | unknown(TIMEOUT) (3.009s) |

## Known BEer gaps

- `M12Card`: KNOWN GAP (ENCODE ERROR) — the `.card` branch is commented out in Encoder/Encoder.lean:229, so encodeTerm falls through to the catch-all at line 410.
- `M18Exists`: KNOWN GAP (INCOMPLETE) — cvc5 does not synthesise the higher-order witness; both ppTrans variants discharge it after flattening to first order.
- `M20MinMax`: KNOWN GAP (ENCODE ERROR) — the `.min` / `.max` branches are commented out in Encoder/Encoder.lean:325-326.

Regenerate with `Test/Micro/run.sh`; `--check` exits non-zero on a BEer regression.
