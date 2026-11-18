#!/bin/sh
set -eu
repo=$(CDPATH='' cd -- "$(dirname "$0")/.." && pwd)
pin=91563b8742cb97c13bb9eb7123b90e5cb3c31fcb
lean=$(command -v "${LEAN:-lean}")
case "$lean" in /*) ;; *) lean="$(pwd)/$lean" ;; esac
case "$("$lean" --version)" in
  *"version 4.19.0,"*"commit 6caaee842e94"*) ;;
  *) echo "The joint proof requires Lean 4.19.0 (6caaee842e94)." >&2; exit 1 ;;
esac
case "${1:-}" in ''|--benchmark|--exhaustive) ;; *) echo "usage: $0 [--benchmark|--exhaustive]" >&2; exit 2 ;; esac
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
trap 'exit 1' HUP INT TERM
if [ -n "${QUANTIFIABLE_SRC:-}" ]; then
  upstream=$(CDPATH='' cd -- "$QUANTIFIABLE_SRC" && pwd)
else
  upstream="$work/upstream"
  git init --quiet "$upstream"
  git -C "$upstream" fetch --quiet --depth=1 https://github.com/clpi/software-is-quantifiable.git "$pin"
  git -C "$upstream" checkout --quiet --detach FETCH_HEAD
fi
cd "$work"
mkdir -p SoftwareIsQuantifiable composition
cp "$repo"/*.lean "$repo/check.sh" .
cp "$repo"/composition/*.lean composition/
mkdir -p docs/covered-frontier
cp "$repo"/docs/covered-frontier/*.lean docs/covered-frontier/
cp "$upstream/SoftwareIsQuantifiable.lean" .
# Copy precisely the source set whose content hashes pin the public dependency.
for name in Interface Finiteness Fold Coloring Pareto Coverage Instance; do
  cp "$upstream/SoftwareIsQuantifiable/$name.lean" SoftwareIsQuantifiable/
done
sha256sum -c "$repo/composition/quantifiable.sha256"
if grep -En '(^|[^[:alnum:]_])(sorry|admit|axiom|native_decide)([^[:alnum:]_]|$)' SoftwareIsQuantifiable/*.lean composition/*.lean; then
  echo "Proof escape hatch in composition sources" >&2
  exit 1
fi
export LEAN="$lean" LEAN_PATH=.
for name in Interface Finiteness Fold Coloring Pareto Coverage Instance; do
  f=SoftwareIsQuantifiable/$name
  "$lean" -DwarningAsError=true -o "$f.olean" "$f.lean"
done
"$lean" -DwarningAsError=true -o SoftwareIsQuantifiable.olean SoftwareIsQuantifiable.lean
sh check.sh
for name in QualifiedClosure QualifiedSelection IntervalDominance LiveSelection IncrementalSelection TraceSafety Controls Benchmark AxiomAudit; do
  f="composition/$name"
  if "$lean" -DwarningAsError=true -o "$f.olean" "$f.lean" > module.log 2>&1; then
    cat module.log
  else
    cat module.log >&2
    exit 1
  fi
  if grep -Eq 'sorryAx|error:|warning:' module.log; then exit 1; fi
done
echo "Joint composition checks passed."
if [ "${1:-}" = --benchmark ]; then "$lean" --run composition/Benchmark.lean; fi

if [ "${1:-}" = --exhaustive ]; then "$lean" -DwarningAsError=true --run composition/ExhaustiveEdits.lean; fi
