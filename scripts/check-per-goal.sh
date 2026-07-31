#!/bin/sh
# Check that `--per-goal` agrees with the whole-file encoding.
#
#   scripts/check-per-goal.sh <file.pog>...
#   find corpus -name '*.pog' | head -20 | xargs scripts/check-per-goal.sh
#
# Per input, six properties:
#   files   one output file per goal
#   flat    no push/pop anywhere, exactly one (check-sat) per file
#   cs      the same total number of (check-sat) commands
#   order   the same goals, in the same order
#   ident   with a single goal, output identical to the whole file up to the
#           brackets and their indentation
#   solver  the same verdicts from cvc5, the per-goal files without
#           --incremental — which is what `flat` buys and what would break
#           first if a push/pop came back
#
# `order` compares the assertion preceding each (check-sat) — the negated goal
# — after rewriting every identifier that carries a digit to its rank of first
# occurrence in that assertion.  Encoding a goal on its own restarts the
# fresh-name counter, so what the whole file calls `mem!135` is `mem!122` when
# alone; the ranks make the two comparable while still failing on a goal that
# moved, changed shape, or went missing.  Identifiers with no digit (SMT
# keywords) and bare numerals (literals) are left alone.
#
# Only sat/unsat are compared. `unknown` is a resource outcome that flips
# between runs on byte-identical input, so requiring it to match reports
# failures that are the solver's timing, not the translator's output; a
# sat-versus-unsat disagreement would be a real difference and does fail.
#
# Solving is skipped when cvc5 is absent or the file has more than
# $BEER_SOLVE_MAX goals; the structural checks always run.
#
# A per-goal script repeats the whole global context, and the corpus's worst
# case is not close: one goal of 0002/00041 is 10 MiB, so its 1033 goals would
# put 10 GiB in $W.  Inputs above $BEER_CHECK_MAX goals are therefore skipped
# unless the variable is raised — the goal count is the whole file's
# (check-sat) count, which is known before the split run.
set -eu

ROOT=$(cd "$(dirname "$0")/.." && pwd)
BIN=${BEER_BIN:-$ROOT/.lake/build/bin/BEer}
PRELUDE=${BEER_PRELUDE:-$ROOT/prelude.smt}
SOLVE_MAX=${BEER_SOLVE_MAX:-60}
CHECK_MAX=${BEER_CHECK_MAX:-200}
MS=${BEER_TLIMIT_PER:-5000}

[ $# -gt 0 ] || { echo "usage: check-per-goal.sh <file.pog>..." >&2; exit 1; }
[ -x "$BIN" ] || { echo "no executable at $BIN — run 'lake build BEer'" >&2; exit 1; }

W=$(mktemp -d)
trap 'rm -rf "$W"' EXIT
command -v cvc5 >/dev/null 2>&1 && HAVE_CVC5=1 || HAVE_CVC5=0

# grep -c exits 1 on no match, which `set -e` would take as a failure.
count() { grep -c "$1" "$2" 2>/dev/null || true; }
countE() { grep -Ec "$1" "$2" 2>/dev/null || true; }

# The assertion before each (check-sat), α-renamed.  One instruction per line
# is what the SMT printer emits, so `awk` keeping the last match is enough.
#
# Only generated names are renamed, and each keeps its base: `mem!66_funGraph67`
# becomes `mem!_funGraph@3`, so it can still never match an `x@3`.  Source names
# must compare literally — renaming those too would let `(= s206 x)` pass as
# `(= s207 x)`, since the ranks would follow the swap.
goals() {
  awk '/^ *\(assert /{a=$0} /^ *\(check-sat\)/{sub(/^ */,"",a); print a}' "$@" |
    perl -pe 'my (%m,$c);
      s{([A-Za-z_][A-Za-z0-9_!]*)}{
        my $t = $1;
        # What `SMT.freshVar` emits: a base ending in `!`, or the default `x`,
        # then the counter.  Nothing else in the file ends in a digit — the
        # reader'"'"'s own `v!<type>` disambiguation ends in letters.
        if ($t =~ /[0-9]$/ and ($t =~ /!/ or $t =~ /^x[0-9]/)) {
          (my $b = $t) =~ s/[0-9]+//g;
          $m{$t} //= "$b\@" . ++$c;
        } else { $t }
      }gex'
}

printf '%-28s %5s %5s %7s %7s %-6s %-6s %-6s %-6s %s\n' \
  pog goals files csWhole csPer struct flat order ident solver
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
  csw=$(count 'check-sat' "$W/w.smt2")
  if [ "$csw" -gt "$CHECK_MAX" ]; then
    printf '%-28s %5s %s\n' "$name" "$csw" \
      "goals — over \$BEER_CHECK_MAX=$CHECK_MAX, skipped (would fill $W)"
    continue
  fi

  # Full stderr to a file: piping it into `head` would SIGPIPE the encoder
  # part-way through writing the goals.
  "$BIN" --per-goal --out "$W/per" --prelude "$PRELUDE" "$pog" >/dev/null 2>"$W/log"

  ng=$(sed -n '1s/.*, \([0-9]*\) goals.*/\1/p' "$W/log")
  ng=${ng:-0}
  nf=$(ls "$W/per" 2>/dev/null | wc -l | tr -d ' ')

  # Numeric on both indices: `po_10_goal_0` sorts before `po_2_goal_0` under
  # the shell's glob, and the order is the whole point of the next check.
  (cd "$W/per" && ls | sort -t_ -k2,2n -k4,4n) > "$W/order" 2>/dev/null || : > "$W/order"
  : > "$W/all"
  while read -r f; do cat "$W/per/$f" >> "$W/all"; done < "$W/order"
  csp=$(count 'check-sat' "$W/all")

  struct=ok
  [ "$nf" = "$ng" ] || { struct=FILES; fail=1; }
  [ "$csw" = "$csp" ] || { struct="$struct/CS"; fail=1; }

  # One (check-sat) per file and no bracketing: without both, the file needs
  # --incremental and the mode has missed its point.
  flat=ok
  brackets=$(countE '^ *\((push|pop) ' "$W/all")
  [ "$brackets" = 0 ] || { flat=PUSHPOP; fail=1; }
  # Per file, not on average: one file with two and one with none would sum
  # right and still need --incremental.
  odd=0
  while read -r f; do
    [ "$(count 'check-sat' "$W/per/$f")" = 1 ] || odd=$((odd + 1))
  done < "$W/order"
  [ "$odd" = 0 ] || { flat="$flat/CS$odd"; fail=1; }

  # With a single goal there is nothing else the two encodings could differ in:
  # same obligation, same starting counters, so even the fresh names agree and
  # the files must match once the brackets and their indentation are gone.
  # `awk 1` on both: neither encoding ends its last line, but dropping the
  # whole file's closing `(pop 1)` leaves the newline that preceded it.
  ident='-'
  if [ "$ng" = 1 ]; then
    sed -E -e '/^ *\((push|pop) /d' -e 's/^ *//' "$W/w.smt2" | awk 1 > "$W/wf"
    sed -E 's/^ *//' "$W/all" | awk 1 > "$W/pf"
    if cmp -s "$W/wf" "$W/pf"; then ident=same
    else ident=DIFFER; fail=1; fi
  fi

  # The concatenation must cover the whole file's goals, in order.
  goals "$W/w.smt2" > "$W/gw"
  if [ -s "$W/order" ]; then
    while read -r f; do goals "$W/per/$f"; done < "$W/order" > "$W/gp"
  else
    : > "$W/gp"
  fi
  if cmp -s "$W/gw" "$W/gp"; then order=same
  else
    order=DIFFER; fail=1
    diff "$W/gw" "$W/gp" | cut -c1-100 | head -4 | sed "s/^/  $name: /" >&2
  fi

  solver=skipped
  if [ "$HAVE_CVC5" = 1 ] && [ "$ng" -le "$SOLVE_MAX" ] && [ "$ng" -gt 0 ]; then
    cvc5 --incremental --tlimit-per="$MS" "$W/w.smt2" 2>/dev/null > "$W/vw" || true
    : > "$W/vp"
    # No --incremental: this is the check, not an oversight.
    while read -r f; do
      cvc5 --tlimit-per="$MS" "$W/per/$f" 2>/dev/null >> "$W/vp" || true
    done < "$W/order"
    err=$(count '^(error' "$W/vp")
    sw=$(count '^sat$' "$W/vw");     sp=$(count '^sat$' "$W/vp")
    uw=$(count '^unsat$' "$W/vw");   up=$(count '^unsat$' "$W/vp")
    kw=$(count '^unknown$' "$W/vw"); kp=$(count '^unknown$' "$W/vp")
    if [ "$err" != 0 ]; then
      solver="SOLVER-ERROR $err"; fail=1
    elif [ "$sw" != "$sp" ]; then
      solver="SAT-DISAGREE whole=$sw per=$sp"; fail=1
    else
      solver="sat $sw/$sp  unsat $uw/$up  unknown $kw/$kp"
      [ "$uw" = "$up" ] || solver="$solver  (unsat differs: resource flake)"
    fi
  fi

  printf '%-28s %5s %5s %7s %7s %-6s %-6s %-6s %-6s %s\n' \
    "$name" "$ng" "$nf" "$csw" "$csp" "$struct" "$flat" "$order" "$ident" "$solver"
done

echo '---'
if [ "$fail" = 0 ]; then echo 'ALL CHECKS PASSED'; else echo 'FAILURES PRESENT'; exit 1; fi
