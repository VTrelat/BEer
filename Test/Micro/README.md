# Atomic encoding regressions

Small, single-principle B machines used to check what the BEer encoding actually
produces, and to compare it against `ppTransSmt` on the same proof obligations.

Each machine in `machines/` isolates **one** principle of the encoding and is kept as
small as Atelier B allows while still generating a real proof obligation (assertions
that Atelier B considers obvious are discharged at PO-generation time and never reach
the encoder, so a few machines carry a slightly stronger goal than the principle
strictly needs).

## Running

```bash
Test/Micro/run.sh
```

`--pog` regenerates the `.pog` files first (needs Atelier B), `--check` turns the suite
into a gate that exits non-zero on a regression, and a bare machine name runs a subset:

```bash
Test/Micro/run.sh --check M09UnionRel M11InterFun
```

Overridable via the environment: `PPTRANS1`, `PPTRANS2`, `TIMEOUT` (ms per goal).
Results land in `results/` and a table is written to `RESULTS.md`.

## What a machine asserts

Every proof obligation is a theorem, so **`unsat` on every goal is the expected
answer**: `sat` means the translation lost information, `unknown` means it is
incomplete.

Three kinds of annotation can appear in a machine, before the `MACHINE` keyword:

| annotation | meaning |
|---|---|
| `/* Principle: … */` | what the machine isolates; shown in the report |
| `/* Expect: goals sat */` | this machine is a **sentinel**: the goal is a deliberate non-theorem, so `sat` is the expected answer and `unsat` would mean the encoded hypotheses are contradictory |
| `/* Expect: BEer <unsupported\|incomplete> — why */` | a known BEer limitation; a result no worse than this is not a regression, a better one is reported as `IMPROVED` |
| `/* Check: <extended regex> */` | pins the *shape* of the SMT BEer emits, not just the solver verdict; a failing check is a `SHAPE MISMATCH` |

The `Check:` lines are what make these tests about the *encoding* rather than about
cvc5: for instance `M13Lambda` requires the lambda to come out as
`(-> Int (Option Int))` with a `some`/`none` body, and `M16Rel` requires a relation to
stay a boolean graph `(-> (Pair Int Int) Bool)`. Fresh-name counters change between
runs, so patterns match `x[0-9]+` rather than literal names.

## The machines

| machine | principle |
|---|---|
| `M00SanitySet` | sentinel: set hypotheses are not contradictory |
| `M01Arith` | `Int`, `+`, `-`, `*`, `≤` |
| `M02Bool` | `BOOL` as SMT `Bool` |
| `M03Maplet` | maplet as `Pair`, componentwise equality |
| `M04Mem` | set as characteristic predicate, `∈` as application |
| `M05Collect` | comprehension as a lambda predicate |
| `M06Pow` | `POW` as a second-order predicate |
| `M07Cprod` | `×` as a predicate on pairs |
| `M08Union` | union as pointwise disjunction |
| `M09UnionRel` | union across representations (function loosened to graph) |
| `M10Inter` | intersection as pointwise conjunction |
| `M11InterFun` | functional intersection stays option-valued |
| `M12Card` | `card` |
| `M13Lambda` | lambda as an option-valued function |
| `M14PFun` | `+->` as a predicate over option-valued functions |
| `M15App` | application through `the` |
| `M16Rel` | `<->` stays a boolean graph |
| `M17Forall` | `∀` as an SMT binder |
| `M18Exists` | `∃` over a function witness stays higher-order |
| `M19EqRepr` | equality between a function and a relation (flags + loosening) |
| `M20MinMax` | `min` / `max` |
| `M21SanityFun` | sentinel: the function representation is not over-constrained |
| `M22SanityRel` | sentinel: a `<->` variable is not silently made functional |

`M14PFun` and `M22SanityRel` share the same goal, `bb = cc`, and differ only in whether
the constant is declared `+->` or `<->`; the first must be `unsat` and the second `sat`.
