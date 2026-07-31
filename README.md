<img src="https://wakatime.com/badge/user/8d0110fb-6b70-4990-ab86-45c404715c2b/project/a38e0d01-6529-445e-b548-0eaa60613112.svg" alt="wakatime">

# <img src=".assets/beer.png" height="60px"> BEer

BEer (**B** **E**ncod**er**) translates Atelier B proof obligation `.pog` files into SMT-LIB v2.7 `.smt` files via a higher-order encoding.
The tool is implemented in Lean 4.

> **This is the `beer-lite` branch.**
> It carries the translator only: the correctness development for the encoder
> lives on the certified branch, and is not built here. Trading the proofs away
> buys the freedom to extend the supported B fragment quickly, which is what
> this branch is for.
>
> The core encoding is the one proved correct in the ABZ 2025 paper; the
> operators added here are *not* covered by that proof, and a few of them are
> deliberately incomplete (documented at each definition).

## Usage
```
BEer --in <input.pog> [--out <output.smt>] [--prelude <prelude.smt>]
```

By default the whole `.pog` becomes one script, its obligations and goals kept
apart by `push`/`pop` — so solving it needs cvc5's `--incremental`. Two flags
split it instead, `--out` then naming a directory:

| Flag | Writes | Notes |
| --- | --- | --- |
| `--per-po` | `po_<i>.smt2` | one file per proof obligation; its goals still bracketed |
| `--per-goal` | `po_<i>_goal_<j>.smt2` | one file per goal, a single `(check-sat)` and no `push`/`pop`, so no `--incremental` |

Both indices are 0-based in `.pog` order, matching ppTrans `-n`'s
`out-<PO>-<goal>.smt2`. Both report per-unit cost on stderr, and `--out
/dev/null` keeps that report without writing anything.

Each split script repeats the whole global context, `--per-goal` most of all:
one goal of the corpus's `0002/00041` is 10 MiB, so its 1033 goals come to
10.5 GiB. Stream them — emit, solve, discard — rather than writing a corpus to
disk.

`scripts/check-per-po.sh` and `scripts/check-per-goal.sh` check either split
against the whole-file encoding.

## Build
Clone this repository, install Lean 4, and build using lake.
```bash
cd BEer
lake build BEer
```
This may take about a few minutes, and should produce an executable `.lake/build/bin/BEer`.

## Paper
An online version of the paper is available [here](https://vtrelat.github.io/papers/abz25.pdf).

## Cite
```bib@
@inproceedings{DBLP:conf/zum/Trelat25,
  author       = {Vincent Tr{\'{e}}lat},
  editor       = {Michael Leuschel and
                  Fuyuki Ishikawa},
  title        = {Safely Encoding {B} Proof Obligations in {SMT-LIB}},
  booktitle    = {Rigorous State-Based Methods - 11th International Conference, {ABZ}
                  2025, D{\"{u}}sseldorf, Germany, June 10-13, 2025, Proceedings},
  series       = {Lecture Notes in Computer Science},
  volume       = {15728},
  pages        = {52--69},
  publisher    = {Springer},
  year         = {2025},
  url          = {https://doi.org/10.1007/978-3-031-94533-5\_4},
  doi          = {10.1007/978-3-031-94533-5\_4}
}
```
