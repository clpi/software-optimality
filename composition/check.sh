#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
case "${1:-}" in ''|--benchmark) ;; *) echo "usage: $0 [--benchmark]" >&2; exit 2 ;; esac
lake build -R -KwarningAsError=true
if [ "${1:-}" = --benchmark ]; then
  lake env lean --run composition/Benchmark.lean
fi
