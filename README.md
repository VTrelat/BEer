# <img src=".assets/beer.png" height="60px"> BEer

BEer (**B** **E**ncod**er**) translates Atelier B proof obligation `.pog` files into SMT-LIB v2.7 `.smt` files via a _certified_ higher-order encoding.
The tool is implemented in Lean and includes a proof of correctness of the encoding.

> [!WARNING]
> Proving the correctness of the translation is still ongoing work.

## Build
Clone this repository, install Lean 4, and build using lake.
```bash
cd BEer
lake build BEer
```
This may take about a few minutes, and should produce an executable `.lake/build/bin/BEer`.

## Paper
An online version of the paper is available on my [personal website](https://vtrelat.github.io/papers/abz25.pdf).

## Cite
```bib
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
