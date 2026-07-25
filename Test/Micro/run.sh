#!/usr/bin/env bash
#
# Atomic encoding regression suite: BEer vs ppTrans.
#
# Each machine in Test/Micro/machines isolates one principle of the encoding, and
# every proof obligation it generates is a theorem, so `unsat` on every goal is
# the expected answer: `sat` means the translation lost information, `unknown`
# means it is incomplete.
#
# Sanity sentinels are non-theorems and declare the opposite expectation with
#   /* Expect: goals sat */
# They fail if the encoding proves them, which is how a contradictory or vacuous
# encoding — one that would make every other machine trivially `unsat` — is caught.
#
# A machine may also pin the *shape* of the encoding, not just the solver verdict,
# with one or more extended regexes matched against the SMT that BEer produces:
#   /* Check: declare-const ff \(-> Int \(Option Int\)\) */
# A failing check is reported as SHAPE MISMATCH: the representation moved.
#
# A machine may declare a known limitation on its second line, e.g.
#   /* Expect: BEer unsupported — card branch is commented out (Encoder/Encoder.lean:229) */
# Accepted expectations: unsat (default), incomplete, unsupported, unsound.
# A result at most as bad as the expectation is not a regression; a better one is
# reported as IMPROVED.
#
# Usage:
#   Test/Micro/run.sh                # run everything, write Test/Micro/RESULTS.md
#   Test/Micro/run.sh M09UnionRel    # run a subset
#   Test/Micro/run.sh --pog          # regenerate .pog files first (needs Atelier B)
#   Test/Micro/run.sh --check        # exit 1 on any BEer regression
#
# Environment overrides: PPTRANS1, PPTRANS2, TIMEOUT (ms per goal).
# Written for bash 3.2 (macOS system bash).

set -uo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$repo_root"

machines_dir="Test/Micro/machines"
results_dir="Test/Micro/results"
report="Test/Micro/RESULTS.md"

BEER="./.lake/build/bin/BEer"
PPTRANS1="${PPTRANS1:-$HOME/Documents/phd-b2smt/pptranssmt/PPTRANSSMT/ppTransSmt}"
PPTRANS2="${PPTRANS2:-$HOME/Documents/phd-b2smt/pptranspog/PPTRANSSMT/ppTransSmt}"
TIMEOUT="${TIMEOUT:-3000}"

GREEN=$'\033[1;32m'; RED=$'\033[1;31m'; ORANGE=$'\033[1;33m'; BLUE=$'\033[1;34m'; NC=$'\033[0m'

regen_pog=0
check_mode=0
selected=""
for arg in "$@"; do
  case "$arg" in
    --pog)   regen_pog=1 ;;
    --check) check_mode=1 ;;
    -h|--help) sed -n '2,23p' "$0"; exit 0 ;;
    *)       selected="$selected ${arg%.mch}" ;;
  esac
done

mkdir -p "$results_dir"
[ -x "$BEER" ] || { echo "missing $BEER — run: lake build BEer" >&2; exit 1; }

if [ -n "$selected" ]; then
  machines=""
  for m in $selected; do machines="$machines $machines_dir/$m.mch"; done
else
  machines="$(echo "$machines_dir"/*.mch)"
fi

# encode <tool> <pog> <out>  -> "ok" | "error: <msg>"
encode() {
  rm -f "$3"
  case "$1" in
    beer) log=$("$BEER" --in "$2" --out "$3" --prelude prelude.smt 2>&1) ;;
    pp1)  log=$("$PPTRANS1" -i "$2" -o "$3" 2>&1) ;;
    pp2)  log=$("$PPTRANS2" -i "$2" -o "$3" 2>&1) ;;
  esac
  if [ -s "$3" ]; then echo "ok"
  else echo "error: $(echo "$log" | tr '\n' ' ' | sed 's/.*: //' | cut -c1-90)"; fi
}

# solve <smt> <out> -> elapsed seconds on stdout, solver answers in <out>
solve() {
  TIMEFORMAT='%3R'
  t=$( { time cvc5 --incremental --mbqi --tlimit-per="$TIMEOUT" "$1" >"$2" 2>&1; } 2>&1 )
  echo "$t"
}

# answers <out> -> space-separated answers, one token per (check-sat)
answers() {
  [ -f "$1" ] || { echo ""; return; }
  sed 's/^unknown *(\(.*\))/unknown(\1)/' "$1" \
    | grep -E '^(unsat|sat|unknown)' | tr '\n' ' ' | sed 's/ *$//'
}

has_solver_error() { grep -q '^(error' "$1" 2>/dev/null; }

# colorize <answer> <wanted-answer>
colorize() {
  case "$1" in
    unknown*) printf '%s' "${ORANGE}$1${NC}" ;;
    "$2")     printf '%s' "${GREEN}$1${NC}" ;;
    *)        printf '%s' "${RED}$1${NC}" ;;
  esac
}

# status_of <encode-status> <answers> <out-file> <wanted-answer>
status_of() {
  case "$1" in ok) ;; *) echo "ENCODE ERROR"; return ;; esac
  if [ -z "$2" ]; then
    if has_solver_error "$3"; then echo "SOLVER ERROR"; else echo "NO GOAL"; fi
    return
  fi
  s="PASS"
  for a in $2; do
    case "$a" in
      "$4")        ;;
      unsat|sat)   s="UNSOUND" ;;
      unknown*)    [ "$s" = PASS ] && s="INCOMPLETE" ;;
      *)           s="SOLVER ERROR" ;;
    esac
  done
  echo "$s"
}

rank() { # higher is worse
  case "$1" in
    PASS) echo 0 ;; INCOMPLETE) echo 1 ;; "NO GOAL") echo 2 ;;
    "ENCODE ERROR") echo 3 ;; "SOLVER ERROR") echo 3 ;; UNSOUND) echo 4 ;; *) echo 4 ;;
  esac
}

expect_to_status() {
  case "$1" in
    incomplete)  echo "INCOMPLETE" ;;
    unsupported) echo "ENCODE ERROR" ;;
    unsound)     echo "UNSOUND" ;;
    *)           echo "PASS" ;;
  esac
}

# cell <status> <answers> <out-file> <wanted-answer>
cell() {
  case "$1" in ok) ;; *) printf '%s' "${RED}encode error${NC}"; return ;; esac
  if [ -z "$2" ]; then
    if has_solver_error "$3"; then printf '%s' "${RED}solver error${NC}"
    else printf '%s' "${ORANGE}no goal${NC}"; fi
    return
  fi
  out=""
  for a in $2; do out="$out$(colorize "$a" "$4") "; done
  printf '%s' "${out% }"
}

sep="$(printf '%.0s-' {1..100})"
rows_file="$(mktemp "${TMPDIR:-/tmp}/beer-micro-rows.XXXXXX")"
trap 'rm -f "$rows_file"' EXIT
regressions=0

printf '%-14s | %-8s | %-6s | %s\n' "machine" "goals" "time" "answers (one token per proof obligation)"
echo "$sep"

for mch in $machines; do
  name=$(basename "$mch" .mch)
  pog="$machines_dir/$name.pog"

  if [ "$regen_pog" = 1 ] || [ ! -f "$pog" ]; then
    ./Test/pog.sh "$mch" >/dev/null 2>&1
  fi
  if [ ! -f "$pog" ]; then
    printf '%-14s | %s\n' "$name" "${RED}no .pog (Atelier B failed)${NC}"
    echo "$name|(no .pog produced)|POG FAILED|-|-|-" >> "$rows_file"
    regressions=$((regressions + 1))
    continue
  fi

  principle=$(sed -n '/Principle:/,/\*\//p' "$mch" | tr '\n' ' ' \
              | sed 's|.*Principle: *||; s| *\*/.*||; s|  *| |g; s| *$||')
  expect=$(grep -m1 'Expect: *BEer' "$mch" | sed 's|.*Expect: *BEer *||; s| .*||')
  expect="${expect:-unsat}"
  expect_note=$(grep -m1 'Expect: *BEer' "$mch" | sed 's|.*Expect: *BEer *[a-z]* *||; s| *\*/||; s|^— *||')
  want=$(grep -m1 'Expect: *goals' "$mch" | sed 's|.*Expect: *goals *||; s| .*||; s|\*/||')
  want="${want:-unsat}"

  st_beer=$(encode beer "$pog" "$results_dir/${name}_ho.smt")
  st_pp1=$(encode pp1  "$pog" "$results_dir/${name}_pp.smt")
  st_pp2=$(encode pp2  "$pog" "$results_dir/${name}_pp2.smt")

  t_beer="-"; t_pp1="-"; t_pp2="-"
  [ "$st_beer" = ok ] && t_beer=$(solve "$results_dir/${name}_ho.smt"  "$results_dir/${name}_ho.out")
  [ "$st_pp1"  = ok ] && t_pp1=$(solve "$results_dir/${name}_pp.smt"  "$results_dir/${name}_pp.out")
  [ "$st_pp2"  = ok ] && t_pp2=$(solve "$results_dir/${name}_pp2.smt" "$results_dir/${name}_pp2.out")

  a_beer=$(answers "$results_dir/${name}_ho.out")
  a_pp1=$(answers "$results_dir/${name}_pp.out")
  a_pp2=$(answers "$results_dir/${name}_pp2.out")

  n_beer=$(echo $a_beer | wc -w | tr -d ' ')
  n_pp1=$(echo $a_pp1 | wc -w | tr -d ' ')
  n_pp2=$(echo $a_pp2 | wc -w | tr -d ' ')

  printf '%-14s | %-8s | %5ss | BEer         %s\n' "$name" "$n_beer/$n_pp1/$n_pp2" "$t_beer" "$(cell "$st_beer" "$a_beer" "$results_dir/${name}_ho.out" "$want")"
  printf '%-14s | %-8s | %5ss | ppTrans(smt) %s\n' "" "" "$t_pp1" "$(cell "$st_pp1" "$a_pp1" "$results_dir/${name}_pp.out" "$want")"
  printf '%-14s | %-8s | %5ss | ppTrans(pog) %s\n' "" "" "$t_pp2" "$(cell "$st_pp2" "$a_pp2" "$results_dir/${name}_pp2.out" "$want")"

  actual=$(status_of "$st_beer" "$a_beer" "$results_dir/${name}_ho.out" "$want")
  wanted=$(expect_to_status "$expect")

  # shape checks, against the SMT BEer produced
  bad_check=""
  if [ "$st_beer" = ok ]; then
    while IFS= read -r pat; do
      [ -n "$pat" ] || continue
      grep -Eq -- "$pat" "$results_dir/${name}_ho.smt" || bad_check="$pat"
    done <<EOF
$(grep '^/\* Check:' "$mch" | sed 's|^/\* Check: ||; s| \*/$||')
EOF
  fi

  ra=$(rank "$actual"); rw=$(rank "$wanted")
  if [ -n "$bad_check" ]; then
    verdict="SHAPE MISMATCH (\`$bad_check\` not found)"; regressions=$((regressions + 1))
    printf '%14s | %s\n' "" "${RED}SHAPE MISMATCH: no match for /$bad_check/${NC}"
  elif [ "$ra" -gt "$rw" ]; then
    verdict="REGRESSION ($actual)"; regressions=$((regressions + 1))
    printf '%14s | %s\n' "" "${RED}REGRESSION: $actual (expected $wanted)${NC}"
  elif [ "$ra" -lt "$rw" ]; then
    verdict="IMPROVED ($actual, expected $wanted)"
    printf '%14s | %s\n' "" "${BLUE}IMPROVED: $actual (expected $wanted) — update the Expect line${NC}"
  elif [ "$actual" = PASS ]; then
    verdict="PASS"
  else
    verdict="KNOWN GAP ($actual)"
    printf '%14s | %s\n' "" "${ORANGE}known gap: $actual${NC}"
  fi
  echo "$sep"

  fmt() { # fmt <status> <answers> <time> <out-file>
    case "$1" in
      ok) if [ -z "$2" ]; then
            if has_solver_error "$4"; then echo "solver error"; else echo "no goal"; fi
          else echo "$2 (${3}s)"; fi ;;
      *)  echo "\`${1}\`" ;;
    esac
  }
  [ "$want" = unsat ] || principle="$principle **(sentinel: \`$want\` expected)**"
  echo "$name|$principle|$verdict|$(fmt "$st_beer" "$a_beer" "$t_beer" "$results_dir/${name}_ho.out")|$(fmt "$st_pp1" "$a_pp1" "$t_pp1" "$results_dir/${name}_pp.out")|$(fmt "$st_pp2" "$a_pp2" "$t_pp2" "$results_dir/${name}_pp2.out")|$expect_note" >> "$rows_file"
done

{
  echo "# Atomic encoding regressions — BEer vs ppTrans"
  echo
  echo "Each machine in \`Test/Micro/machines\` isolates one principle of the encoding."
  echo "Every proof obligation is a theorem, so **\`unsat\` on every goal is the expected"
  echo "answer**: \`sat\` means the translation lost information, \`unknown\` means it is"
  echo "incomplete. Solver: cvc5 \`--incremental --mbqi --tlimit-per=${TIMEOUT}\`, answers"
  echo "listed in file order, one token per \`(check-sat)\`."
  echo
  echo "The sentinel machines are deliberate non-theorems: for them \`sat\` is the expected"
  echo "answer, and \`unsat\` would mean the encoded hypotheses are contradictory."
  echo
  echo "| machine | principle | BEer verdict | BEer | ppTrans (smt) | ppTrans (pog) |"
  echo "|---|---|---|---|---|---|"
  while IFS='|' read -r n p v b q1 q2 note; do
    echo "| \`$n\` | $p | $v | $b | $q1 | $q2 |"
  done < "$rows_file"
  echo
  echo "## Known BEer gaps"
  echo
  gap=0
  while IFS='|' read -r n p v b q1 q2 note; do
    case "$v" in
      "KNOWN GAP"*|"REGRESSION"*) echo "- \`$n\`: $v${note:+ — $note}"; gap=1 ;;
    esac
  done < "$rows_file"
  [ "$gap" = 0 ] && echo "None."
  echo
  echo "Regenerate with \`Test/Micro/run.sh\`; \`--check\` exits non-zero on a BEer regression."
} > "$report"

echo
echo "report: $report"
if [ "$regressions" -gt 0 ]; then
  printf '%s\n' "${RED}${regressions} regression(s)${NC}"
  [ "$check_mode" = 1 ] && exit 1
else
  printf '%s\n' "${GREEN}no regression${NC}"
fi
exit 0
