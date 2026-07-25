#!/bin/sh
# Measure translator coverage over a corpus of .pog files.
#
#   scripts/sweep.sh <corpus-dir> [out.tsv] [stride] [jobs]
#
# Writes one TSV row per file: <path> <OK|FAIL|TIMEOUT> <first error message>.
# `stride` samples every Nth file (default 1, i.e. all of them) — useful to keep
# a run cheap. Summarise a result with:
#
#   cut -f2 out.tsv | sort | uniq -c
#   grep -P '\tFAIL\t' out.tsv | cut -f3 | sed -E 's/[0-9]+//g' | sort | uniq -c | sort -rn
#
# Only the *first* error of each file is reported, so fixing one operator
# reshuffles the histogram rather than simply shrinking it.
set -eu

CORPUS=${1:?usage: sweep.sh <corpus-dir> [out.tsv] [stride] [jobs]}
OUT=${2:-sweep.tsv}
STRIDE=${3:-1}
JOBS=${4:-4}

ROOT=$(cd "$(dirname "$0")/.." && pwd)
BIN=${BEER_BIN:-$ROOT/.lake/build/bin/BEer}
PRELUDE=${BEER_PRELUDE:-$ROOT/prelude.smt}
LIMIT=${BEER_TIMEOUT:-60}

[ -x "$BIN" ] || { echo "no executable at $BIN — run 'lake build BEer'" >&2; exit 1; }

one=$(mktemp)
trap 'rm -f "$one"' EXIT
cat > "$one" <<EOF
#!/bin/sh
err=\$(timeout $LIMIT "$BIN" --in "\$1" --out /dev/null --prelude "$PRELUDE" 2>&1 >/dev/null)
case \$? in
  124) printf '%s\tTIMEOUT\t\n' "\$1" ;;
  0)   printf '%s\tOK\t\n' "\$1" ;;
  *)   printf '%s\tFAIL\t%s\n' "\$1" "\$(printf '%s' "\$err" | tr '\n' ' ' | sed 's/uncaught exception: //')" ;;
esac
EOF
chmod +x "$one"

find "$CORPUS" -name '*.pog' | sort | awk "(NR - 1) % $STRIDE == 0" |
  xargs -P "$JOBS" -n 1 "$one" > "$OUT"

echo "$(wc -l < "$OUT") files -> $OUT"
cut -f2 "$OUT" | sort | uniq -c
