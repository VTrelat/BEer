#!/usr/bin/env bash

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

tmpdir="$(mktemp -d "${TMPDIR:-/tmp}/beer-lambda-representation.XXXXXX")"
trap 'rm -rf "$tmpdir"' EXIT

build_log="$tmpdir/lake-build.log"
if ! lake build BEer SMT.Reasoning.EncodeTermRepresented \
    >"$build_log" 2>&1; then
  cat "$build_log" >&2
  exit 1
fi

generated="$tmpdir/Demo2_ho.smt"
./.lake/build/bin/BEer \
  --in Test/Demo2.pog \
  --out "$generated" \
  --prelude prelude.smt

# `id(1..ub)` is decoded as a B lambda.  Its SMT body must return `some x`
# inside the source domain and `none` outside it, rather than a Boolean graph.
if ! rg -q '\(some \(fst' "$generated" ||
    ! rg -q '\(as none \(Option Int\)\)' "$generated"; then
  echo "Lambda regression: option-valued identity body not found" >&2
  exit 1
fi

expected_sha256="1a8f044573d706732577665376cbe871c5a3a6a0e4ab9df0408114725990b5dd"
if command -v shasum >/dev/null 2>&1; then
  actual_sha256="$(shasum -a 256 "$generated" | awk '{print $1}')"
elif command -v sha256sum >/dev/null 2>&1; then
  actual_sha256="$(sha256sum "$generated" | awk '{print $1}')"
else
  echo "Lambda regression: no SHA-256 utility found" >&2
  exit 1
fi
if [[ "$actual_sha256" != "$expected_sha256" ]]; then
  echo "Lambda regression: generated SMT bytes changed" >&2
  echo "expected sha256: $expected_sha256" >&2
  echo "actual sha256:   $actual_sha256" >&2
  exit 1
fi

solver_output="$(cvc5 --incremental --mbqi --tlimit-per=10000 "$generated")"
if [[ "$solver_output" != "unsat" ]]; then
  echo "Lambda regression: expected unsat, got: $solver_output" >&2
  exit 1
fi

echo "Lambda represented script: option-valued, byte-stable, and unsat"
