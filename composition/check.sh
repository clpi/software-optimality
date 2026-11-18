#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
case "${1:-}" in ''|--benchmark|--exhaustive) ;; *) echo "usage: $0 [--benchmark|--exhaustive]" >&2; exit 2 ;; esac
lake_bin=${LAKE:-lake}
"$lake_bin" --wfail build -R -KwarningAsError=true
"$lake_bin" env sh composition/current/negative.sh
echo "Joint composition checks passed."
if [ "${1:-}" = --benchmark ]; then
  "$lake_bin" env lean --run composition/Benchmark.lean
fi

if [ "${1:-}" = --exhaustive ]; then
  "$lake_bin" env lean -DwarningAsError=true --run composition/ExhaustiveEdits.lean
fi
