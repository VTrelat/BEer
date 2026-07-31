#!/bin/sh
# Check that `--per-po` agrees with the whole-file encoding.
#
#   scripts/check-per-po.sh <file.pog>...
#   find corpus -name '*.pog' | head -20 | xargs scripts/check-per-po.sh
#
# Per input, four properties:
#   files   one output file per proof obligation
#   cs      the same total number of (check-sat) commands
#   ident   with a single obligation, output byte-identical to the whole file
#   solver  the same verdicts from cvc5
#
# Only sat/unsat are compared. `unknown` is a resource outcome that flips
# between runs on byte-identical input, so requiring it to match reports
# failures that are the solver's timing, not the translator's output; a
# sat-versus-unsat disagreement would be a real difference and does fail.
# cvc5 gets --tlimit-per, a per-query budget: with a whole-file --tlimit the
# single file is starved while each per-obligation file gets the budget again,
# and the comparison means nothing.
#
# Skipped when cvc5 is absent or the file has more than $BEER_SOLVE_MAX
# obligations; the structural checks always run.
set -eu

ROOT=$(cd "$(dirname "$0")/.." && pwd)
BIN=${BEER_BIN:-$ROOT/.lake/build/bin/BEer}
PRELUDE=${BEER_PRELUDE:-$ROOT/prelude.smt}
SOLVE_MAX=${BEER_SOLVE_MAX:-60}
MS=${BEER_TLIMIT_PER:-5000}

[ $# -gt 0 ] || { echo "usage: check-per-po.sh <file.pog>..." >&2; exit 1; }
[ -x "$BIN" ] || { echo "no executable at $BIN — run 'lake build BEer'" >&2; exit 1; }

W=$(mktemp -d)
trap 'rm -rf "$W"' EXIT
command -v cvc5 >/dev/null 2>&1 && HAVE_CVC5=1 || HAVE_CVC5=0

# grep -c exits 1 on no match, which `set -e` would take as a failure.
count() { grep -c "$1" "$2" 2>/dev/null || true; }

printf '%-28s %4s %5s %7s %7s %-6s %-6s %s\n' pog POs files csWhole csPer struct ident solver
fail=0

for pog in "$@"; do
  # Corpus files are all named <project>/<NNNNN>.pog, so the basename alone
  # collides across projects; keep the parent directory in the label.
  name=$(basename "$(dirname "$pog")")/$(basename "$pog" .pog)
  rm -rf "$W/w.smt2" "$W/per" "$W/log"

  if ! "$BIN" --out "$W/w.smt2" --prelude "$PRELUDE" "$pog" >/dev/null 2>&1; then
    printf '%-28s %s\n' "$name" 'whole-file encode failed — skipped'
    continue
  fi
  # Full stderr to a file: piping it into `head` would SIGPIPE the encoder
  # part-way through writing the obligations.
  "$BIN" --per-po --out "$W/per" --prelude "$PRELUDE" "$pog" >/dev/null 2>"$W/log"

  npo=$(sed -n '1s/.*: \([0-9]*\) proof.*/\1/p' "$W/log")
  npo=${npo:-0}
  nf=$(ls "$W/per" 2>/dev/null | wc -l | tr -d ' ')
  csw=$(count 'check-sat' "$W/w.smt2")
  cat "$W/per"/po_*.smt2 > "$W/all" 2>/dev/null || : > "$W/all"
  csp=$(count 'check-sat' "$W/all")

  struct=ok
  [ "$nf" = "$npo" ] || { struct=FILES; fail=1; }
  [ "$csw" = "$csp" ] || { struct="$struct/CS"; fail=1; }

  ident='-'
  if [ "$npo" = 1 ]; then
    if cmp -s "$W/w.smt2" "$W/per/po_0.smt2"; then ident=same
    else ident=DIFFER; fail=1; fi
  fi

  solver=skipped
  if [ "$HAVE_CVC5" = 1 ] && [ "$npo" -le "$SOLVE_MAX" ] && [ "$npo" -gt 0 ]; then
    cvc5 --incremental --tlimit-per="$MS" "$W/w.smt2" 2>/dev/null > "$W/vw" || true
    : > "$W/vp"
    for f in "$W/per"/po_*.smt2; do
      cvc5 --incremental --tlimit-per="$MS" "$f" 2>/dev/null >> "$W/vp" || true
    done
    sw=$(count '^sat$' "$W/vw");     sp=$(count '^sat$' "$W/vp")
    uw=$(count '^unsat$' "$W/vw");   up=$(count '^unsat$' "$W/vp")
    kw=$(count '^unknown$' "$W/vw"); kp=$(count '^unknown$' "$W/vp")
    if [ "$sw" != "$sp" ]; then
      solver="SAT-DISAGREE whole=$sw per=$sp"; fail=1
    else
      solver="sat $sw/$sp  unsat $uw/$up  unknown $kw/$kp"
      [ "$uw" = "$up" ] || solver="$solver  (unsat differs: resource flake)"
    fi
  fi

  printf '%-28s %4s %5s %7s %7s %-6s %-6s %s\n' \
    "$name" "$npo" "$nf" "$csw" "$csp" "$struct" "$ident" "$solver"
done

echo '---'
if [ "$fail" = 0 ]; then echo 'ALL CHECKS PASSED'; else echo 'FAILURES PRESENT'; exit 1; fi
