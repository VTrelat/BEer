#!/usr/bin/env bash

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

tmpdir="$(mktemp -d "${TMPDIR:-/tmp}/beer-intersection-representation.XXXXXX")"
trap 'rm -rf "$tmpdir"' EXIT

build_log="$tmpdir/lake-build.log"
if ! lake build BEer SMT.Reasoning.EncodeTermRepresented \
    >"$build_log" 2>&1; then
  cat "$build_log" >&2
  exit 1
fi

lake env lean --run Test/IntersectionRepresentation.lean

generated="$tmpdir/Intersection_ho.smt"
./.lake/build/bin/BEer \
  --in Test/Intersection.pog \
  --out "$generated" \
  --prelude prelude.smt

if ! rg -q -F '(ite (= (f (fst' "$generated" ||
   ! rg -q -F '(g (fst' "$generated" ||
   ! rg -q -F '(as none (Option Int))' "$generated"; then
  echo "Intersection regression: generated SMT lacks the guarded option-valued intersection" >&2
  exit 1
fi

solver_output="$(cvc5 --incremental --mbqi --tlimit-per=10000 "$generated")"
if [[ "$solver_output" != "unsat" ]]; then
  echo "Intersection regression: expected unsat, got: $solver_output" >&2
  exit 1
fi

echo "Intersection represented script: guarded option-valued function and unsat"
