#!/bin/sh
set -eu
cd "$(dirname "$0")"
lean_bin=${LEAN:-lean}
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT HUP INT TERM
"$lean_bin" --version
"$lean_bin" -DwarningAsError=true AdaptiveReads.lean
patch -s -o "$tmp/Changed.lean" AdaptiveReads.lean < mutation.patch
if "$lean_bin" -DwarningAsError=true "$tmp/Changed.lean" >"$tmp/control.log" 2>&1; then
  echo "Modified claim passed unexpectedly" >&2
  exit 1
fi
grep -q 'Changed.lean:.*error:' "$tmp/control.log"
echo "Rejected control: read bank 2 twice and omit bank 3."
