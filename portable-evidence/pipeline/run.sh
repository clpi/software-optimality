#!/bin/sh
set -eu
cd "$(dirname "$0")"
python3 -m unittest -v test_pipeline.py
python3 -O -m unittest test_pipeline.py
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT HUP INT TERM
python3 pipeline.py fixtures/authority.json fixtures/ci.json fixtures/benchmark.json > "$scratch/projection.json"
cmp fixtures/projection.json "$scratch/projection.json"
python3 export_samples.py fixtures/authority.json fixtures/benchmark.json > "$scratch/samples.txt"
if command -v cc >/dev/null 2>&1; then
  cc -std=c99 -Wall -Wextra -Werror samples_check.c -o "$scratch/samples_check"
  "$scratch/samples_check" < "$scratch/samples.txt"
  if printf '1\n-1\n' | "$scratch/samples_check"; then exit 1; fi
  if printf '1\n3\n4\n' | "$scratch/samples_check"; then exit 1; fi
else
  printf '%s\n' 'C bridge skipped: no C compiler' >&2
fi
