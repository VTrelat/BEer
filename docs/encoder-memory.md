# Why `--per-goal` ran out of memory

Measured 2026-08-03 on `beer-lite`, from `7da3479`.

`BEer --per-goal` grew without bound on some inputs. On a 24 GB machine,
`0003/00341` — a 1.2 MB `.pog` — reached about 40 GB resident and drove it
16 GB into swap; `0003/00039` (2.5 MB) passed 3 GB. Both are in cluster 0003,
the 154 of the 326 campaign timeouts that neither `maxSiteLinks := 0` nor the
`fv` cache had reached.

## It is not accumulation across goals

The obvious reading — that `--per-goal` leaks state from one goal into the next —
is wrong. `perGoal` runs `encode one |>.run ∅` per goal, from an empty
`EncoderState`, and nothing outlives the iteration: no `IO.Ref`, no global memo,
no retained strings. Under a watchdog the baseline reaches 8 GB **inside a
single goal**: on `00341` it prints three goal lines and then grows past the cap
while encoding obligation 1 goal 0.

What `--per-goal` does is expose the cost. It re-encodes the whole global
context per goal, so an obligation that explodes is met once per goal of that
obligation rather than once per file.

## The encoder builds a DAG and substitution unfolded it

`encodeTerm` produces a **DAG**. A cast helper's specification, an encoded
domain, a site's argument are each reachable through many paths, and the encoder
depends on that sharing to keep an obligation roughly the size of the `.pog`.

`SMT.subst` allocated a fresh node for every node it visited — `.and a b`
became a *new* `.and` even when neither child moved. That replaces the DAG by
its tree unfolding. The quantifier, `collect` and `lambda` cases substitute once
per level of nesting, so each level unfolded what the level below had built and
the sizes compounded.

`sample` on the baseline puts the whole run in one chain:

```
encodeTerm → SMT.rescopeHelpers → Array.mapM → SMT.subst → SMT.subst → …
```

`rescopeHelpers` was the worst case. Its renaming was

```lean
helpers.foldl (fun acc h => subst h (.app (.var s!"{h}^") (.var z)) acc) t
```

— one full traversal *per helper*, rebuilding the term each time, applied to the
body and to every specification. The traversals went as the square of the helper
count, and every one of them destroyed sharing.

## Three changes

### 1. Sharing-preserving, simultaneous substitution (`Encoder/Simplifier.lean`)

`substAux` returns `Option Term`, `none` meaning *unchanged*, so a subterm no
substitution reaches keeps the node it already had; and it takes the whole
substitution as a map, in one traversal, instead of one variable per traversal.
`subst`, `substList` and `applySubst` are all defined through it.

`substList` is now simultaneous where it used to be a sequential fold. The two
differ only when a replacement mentions a later variable of the domain, and no
caller does that — each substitutes source binders by terms over
encoder-generated names — so where they disagree it is because the fold was
capturing.

This alone took `00341` from 8 GB and climbing to a flat 0.1 GB.

### 2. A size bound on sites (`SMT.maxSiteSize`, `Encoder/Basic.lean`)

With the memory bounded, the cost moved to `SMT.fv` under `recordSite`: a site
memoises its constant on the encoded set, and everything it costs is paid on
that set **unfolded** — `fv` walks it, `findSite` compares against it, and
`sitesOf` hands it to `subsetOf`, which inlines it twice into the next site's
specification. That last one is a feedback loop, and it is the mechanism behind
the exponential growth per goal recorded in `docs/`-adjacent notes.

`recordSite` now declines sets past `maxSiteSize`, checked before `fv` so an
oversized argument is not walked just to discover that it is oversized. A
declined site costs exactly what a site dropped by `hideCapturedSites` costs: a
second occurrence introduces a second constant and the cross-site facts are not
stated. Both are facts the solver never learns, never unsoundness.

### 3. A bound on what is carried into a binder (`SMT.maxTermSize`)

Sharing bounds the encoder's *memory*, but not what the output would be:
`Term.toString` has to unfold, because an SMT-LIB script is a tree. A body whose
unfolding is astronomical denotes a file that cannot be written or read, so the
honest outcome is an error naming the obligation.

`guardSize` is called from `rescopeHelpers` — on the body and on each
specification — and on the `spec_bodies` of the two `.all` branches. Those are
the levels at which the term compounds: a specification built at one level is
inlined into the formula the level above rewrites again. Placing it there rather
than at every binder case matters: at the binder cases it cost an extra full
traversal per binder, measured at **1.55×** on `00039`, where at the re-scoping
sites it rides along with a traversal that already happens and costs nothing
measurable.

`Term.sizeUpTo` counts through shared subterms once per occurrence — the
unfolding, not the DAG — and abandons at the limit, so it costs `limit` steps at
worst whatever it is given.

## Results

`--per-goal --out <dir> --prelude prelude.smt`, watchdog killing past 8 GB:

| file | | peak RSS | wall | goals |
|---|---|---|---|---|
| `0003/00341` (1.2 MB, 13 PO, 138 goals) | before | 8062 MB, still climbing | killed at 61 s | 3 |
| | after | **291 MB** | 92 s, completes | 138 reported, 125 emitted, 13 refused |
| `0003/00039` (2.5 MB, 56 PO, 530 goals) | before | 8042 MB, still climbing | killed at 322 s | 431 |
| | after | **496 MB** | 514 s, completes | 530 reported, 518 emitted, 12 refused |

The baseline figures are what the watchdog saw before killing at 8 GB, not a
plateau: on the unguarded machine `00341` reached about 40 GB. On `00039` the
baseline sits at ~560 MB through goal 416 and is at 3.5 GB by goal 431, which is
where it was killed.

Encode time per goal is unchanged — 293/296/297 ms on `00341`'s first three
goals against 305/311/325 ms for the baseline — and their output is
byte-identical.

### Corpus

Whole-file mode, `--out <file> --prelude prelude.smt`, per file a 30 s limit and
a 2 GB resident limit (`MEM` below is a file killed at that limit; the baseline
would otherwise have taken the machine down). Every eighth file of the corpus,
678 of them:

```
status  before: FAIL 84, MEM 28, OK 520, TIMEOUT 46
status  after:  FAIL 98, MEM  0, OK 525, TIMEOUT 55

transitions, non-identical only:
  MEM → FAIL 14   MEM → TIMEOUT 9   MEM → OK 5   OK → TIMEOUT 1   TIMEOUT → OK 1

OK in both: 519    byte-identical output: 518    differing: 1

peak RSS MB  before: median 79  p90 348  p99 1848  max 1903
peak RSS MB  after:  median 78  p90 297  p99  591  max 1098
over 1000 MB before: 30    after: 1
elapsed s    before: median 1  p90 22  p99 31
elapsed s    after:  median 1  p90 26  p99 31
```

Every `MEM` is gone and nothing else moved into a worse state. Five files that
used to exhaust the limit now translate. The two remaining transitions are one
file each way across the 30 s limit — `0016/00052` at 29 s before and 31 s after,
`0023/00202` at 31 s and 1169 MB before against 12 s and 228 MB after — the
first noise against a cap on a machine that was contended for, the second a real
gain. The failure histogram loses nothing: the 83 `records are not supported`
and the one `Real and float arithmetic` are the same files as before, and the 14
new failures are the guard.

The `elapsed` p90 moves the wrong way by 4 s, which is the same effect read from
the other end: nine obligations that used to be killed on memory at around 15 s
now run to the time limit instead.

Of the 519 files that translated under both, 518 are byte-identical and one —
`0023/00290` — is 4.4 MB where it was 5.6 MB. Rebuilding with `maxSiteSize`
raised out of reach reproduces the baseline byte for byte, which places the
difference entirely on that bound: the file loses the linking assertions of one
oversized `card` site. The substitution rewrite is output-preserving on every
file measured.

A separate run over all 878 files of clusters 0000–0001 at a 60 s limit found
the histogram identical in every cell (FAIL 650, OK 222, TIMEOUT 6), no
transitions, and all 222 outputs byte-identical. Those clusters are almost
entirely `records are not supported`, so they test that nothing moved rather
than that anything improved.

## Caveats

`maxTermSize` turns a class of runaway obligation from "exhausts the machine"
into "reports an error". That is a deliberate trade: the goals it refuses could
not have produced a usable script. Whether a *smaller* bound would be better is
open — nothing in the corpus sits near it, so it has not been calibrated against
anything except the runaway case.

Neither bound addresses why cluster 0003 blows up in the first place. The
encoder still builds terms whose unfolding is exponential in the nesting depth;
what changed is that it now notices.
