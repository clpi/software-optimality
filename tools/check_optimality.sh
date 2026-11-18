#!/bin/sh
# Differential check of the executable guards against OptimalityInterface.
# Requires the Lean modules already compiled (./check.sh) and `lean` on PATH.
set -eu
cd "$(dirname "$0")/.."
LEAN="${LEAN:-lean}"
export LEAN_PATH=".:${LEAN_PATH:-}"
LEAN_OUT="$(mktemp)"
PY_OUT="$(mktemp)"
trap 'rm -f "$LEAN_OUT" "$PY_OUT"' EXIT HUP INT TERM
"$LEAN" --run CompositionCheck.lean >"$LEAN_OUT"
python3 tools/check_optimality.py >"$PY_OUT"
diff -u "$PY_OUT" "$LEAN_OUT"
grep -q 'regressing-frontier refuse' "$LEAN_OUT"
grep -q 'out-of-universe refuse' "$LEAN_OUT"
grep -q 'nonstrict-reduction refuse' "$LEAN_OUT"
