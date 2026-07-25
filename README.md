<img src="https://wakatime.com/badge/user/8d0110fb-6b70-4990-ab86-45c404715c2b/project/a38e0d01-6529-445e-b548-0eaa60613112.svg" alt="wakatime">

# <img src=".assets/beer.png" height="60px"> BEer

BEer (**B** **E**ncod**er**) translates Atelier B proof obligation `.pog` files into SMT-LIB v2.7 `.smt` files via a higher-order encoding.
The tool is implemented in Lean 4.

> **This is the `beer-lite` branch.**
> It carries the translator only: the correctness development for the encoder
> lives on the certified branch, and is not built here. Trading the proofs away
> buys the freedom to extend the supported B fragment quickly, which is what
> this branch is for — see [Coverage](#coverage).
>
> The core encoding is the one proved correct in the ABZ 2025 paper; the
> operators added here are *not* covered by that proof, and a few of them are
> deliberately incomplete (documented at each definition).

## Usage
```
BEer --in <input.pog> [--out <output.smt>] [--prelude <prelude.smt>]
```

## Build
Clone this repository, install Lean 4, and build using lake.
```bash
cd BEer
lake build BEer
```
This may take about a few minutes, and should produce an executable `.lake/build/bin/BEer`.

## Coverage

Beyond the fragment of the certified encoder, this branch supports:

| Operator | Encoding |
| --- | --- |
| `/`, `mod` | `bdiv`/`bmod` in the prelude — B truncates towards zero, SMT-LIB `div`/`mod` are Euclidean |
| `**` | repeated multiplication for literal exponents, the axiomatised `bpow` otherwise |
| `card` | one integer constant per occurrence, with `0 ≤ ·`, `· = 0 ↔ ∅` and monotonicity against nearby cardinals |
| `min`, `max` | one integer constant per occurrence, guarded by non-emptiness and boundedness |
| `FIN`, enumerated sets | a boolean constant closed under subsets, replacing the B-Book injection into an initial segment of ℕ |
| `closure`, `closure1` | *some* transitive (resp. reflexive-transitive) relation containing the argument |
| `;`, `rel`, `fnc`, `<<:`, `/<<:` | derived, in B |
| `first`, `last`, `front`, `tail`, `rev`, `^`, `<-`, `->`, `/\|\`, `\\\|/` | derived, in B (a sequence is a function `1‥n → E`) |
| `UNION`, `INTER` | derived, in B |
| sequence literals, `EmptySeq` | derived, in B |

`card`, `min`, `max`, `finite` and `closure` cannot be prelude symbols: cvc5
supports parametric *datatypes* (`par`) but not parametric function
declarations, and a higher-order axiom quantified over sets is not instantiated
at a λ-term in practice. Each occurrence therefore gets its own constant and
first-order defining assertions, shared between occurrences of the same
argument.

Not supported: `iSIGMA`/`iPI`, `conc`, `iterate`, records (`Struct`), and real
arithmetic.

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
