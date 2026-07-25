# BEer — `beer-lite`

Repository root: `/Users/vtrelat/Documents/BEer`

## What this branch is

`beer-lite` is BEer with the correctness development removed. It keeps the
program — `.pog` in, SMT-LIB out — and trades the proofs for the ability to
extend the supported B fragment quickly.

The certified encoder lives on the other branch. **Do not port proofs here, and
do not try to keep the encoder proof-compatible.** Changing `encodeTerm`,
adding `B.Term` constructors, or changing the emitted SMT is expected work on
this branch.

## Pipeline

1. `readPOG` parses the XML (`POGReader/POGReader.lean`).
2. `POGtoB` builds a `B.Env` — operator tables are `String.toBinaryOp` /
   `String.toUnaryOp`, derived operators are in `POGReader/Builtins.lean`.
3. `encode` walks the environment (`Encoder/Encoder.lean`).
4. `EncoderState.toSMTFile` serialises, and `Main` prepends `prelude.smt`.

## Layout

- `B/Syntax/{Basic,Extra}.lean` — the B term language, `fv`/`bv`, notation,
  pretty printer.
- `B/Simplifier.lean` — `subst`, `substList`, `Term.simplify`.
- `B/Typing/Basic.lean` — `BType`, `TypeContext`.
- `POGReader/` — XML decoding and the operator tables.
- `SMT/Syntax.lean` — SMT terms and their printer.
- `SMT/Typing.lean` — the SMT type context (the `⊢ˢ` judgment is gone).
- `Encoder/Basic.lean` — encoder state, fresh variables, `Site`.
- `Encoder/Loosening/` — the cast/representation-join layer (`castEq`,
  `castApp`, `castMembership`, `castUnion`, `castInter`).
- `Encoder/Encoder.lean` — `encodeTerm` and the top-level passes.
- `prelude.smt` — the fixed SMT-LIB preamble.

## Two representations

A B set is a characteristic predicate `α → Bool`. A B set of pairs may instead
be stored as a partial function `α → Option β` when its variable is *flagged*
(see `B.Env.flags` and `encodeTypeContext`). The loosening layer converts
between representations; most encoder cases must handle both, or explicitly
reify the graph — see the `pow` and `closure` cases for the pattern.

## Adding an operator

Prefer deriving it in B — `POGReader/Builtins.lean` — over touching the
encoder. That needs no new constructor and no new SMT support.

A new primitive is warranted only when the operator is not first-order
definable (`card`, `min`, `max`, `finite`, `closure`). Then:

1. Add the `B.Term` constructor; the compiler lists every match to extend
   (`fv`, `bv`, `subst`, `simplifier`, the pretty printer, `B.Term.getType`).
2. Add an `encodeTerm` case. For anything set-indexed, use the `Site`
   mechanism: a fresh constant per occurrence plus first-order assertions,
   memoised on the encoded argument. Do **not** declare a higher-order symbol
   and quantify over sets — cvc5 will not instantiate it at a λ-term (measured:
   `unknown` where the first-order form gives `unsat`), and it has no
   parametric function declarations, only parametric datatypes.
3. If the operator is a fixed SMT symbol instead, add it to `prelude.smt` and
   emit `SMT.Term.builtin`.

Document any incompleteness at the definition, and say which direction it errs
in. Over-approximating an argument — as `closure` does — is sound for validity
checking; under-approximating is not.

## Validation

The tool is measured against the benchmark corpus, not against a proof:

```bash
.lake/build/bin/BEer --in <file.pog> --out /dev/null --prelude prelude.smt
```

Sweep the corpus before and after a change and compare the failure histogram —
the first error per file is what shifts. Running `cvc5` on a few produced files
is worth doing too: a file that translates but that no solver can use is not
progress.

## Constraints

- Keep the build green: `lake build`.
- No new `sorry`/`admit` — there are none left, and the remaining `theorem`s
  are only the ones the runtime definitions need.
- `POGReader.decodeTerm` has a hand-written `decreasing_by` whose bullets are
  positional. Adding or removing a recursive call inside it shifts the goals;
  add the matching bullet rather than restructuring the proof.
