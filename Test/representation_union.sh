#!/usr/bin/env bash

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

tmpdir="$(mktemp -d "${TMPDIR:-/tmp}/beer-union-representation.XXXXXX")"
trap 'rm -rf "$tmpdir"' EXIT

build_log="$tmpdir/lake-build.log"
if ! lake build BEer SMT.Reasoning.ProofObligationUnion \
    >"$build_log" 2>&1; then
  cat "$build_log" >&2
  exit 1
fi
lake env lean --run Test/UnionRepresentation.lean

generated="$tmpdir/Union_ho.smt"
./.lake/build/bin/BEer \
  --in Test/Union.pog \
  --out "$generated" \
  --prelude prelude.smt

expected_sha256="e93a29578ca1ee3d3fb2a175dbf6b3cef135a435855a05bf397c38f75b916a50"
if command -v shasum >/dev/null 2>&1; then
  actual_sha256="$(shasum -a 256 "$generated" | awk '{print $1}')"
elif command -v sha256sum >/dev/null 2>&1; then
  actual_sha256="$(sha256sum "$generated" | awk '{print $1}')"
else
  echo "Union regression: no SHA-256 utility found" >&2
  exit 1
fi
if [[ "$actual_sha256" != "$expected_sha256" ]]; then
  echo "Union regression: generated SMT bytes changed" >&2
  echo "expected sha256: $expected_sha256" >&2
  echo "actual sha256:   $actual_sha256" >&2
  exit 1
fi

solver_output="$(cvc5 --incremental --mbqi --tlimit-per=3000 "$generated")"
if [[ "$solver_output" != "unsat" ]]; then
  echo "Union regression: expected unsat, got: $solver_output" >&2
  exit 1
fi

echo "Union represented script: byte-identical and unsat"
