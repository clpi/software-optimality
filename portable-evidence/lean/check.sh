#!/bin/sh
set -eu
cd "$(dirname "$0")"
ROOT=$(pwd)
LEAN=${LEAN:-lean}
export LEAN
# Each gate operates in its own directory. No stale module can be reused.
gate() (
  cd "$1"
  if grep -En '\b(sorry|admit|axiom|native_decide)\b' PortableAdapter.lean Tests.lean; then
    echo 'Forbidden proof token (preflight)' >&2
    exit 1
  fi
  rm -f PortableAdapter.olean
  export LEAN_PATH=.
  "$LEAN" -DwarningAsError=true -o PortableAdapter.olean PortableAdapter.lean > proof.log 2>&1 || { cat proof.log; exit 1; }
  "$LEAN" -DwarningAsError=true Tests.lean >> proof.log 2>&1 || { cat proof.log; exit 1; }
  python3 - <<'PY' || exit 1
import re
from pathlib import Path
src=Path('PortableAdapter.lean').read_text()
log=Path('proof.log').read_text()
expected=set(re.findall(r'^theorem (\w+)',src,re.M))
seen={}
for name, deps in re.findall(r"'PortableAdapter\.(\w+)' depends on axioms: \[(.*?)\]",log):
    seen[name]={a.strip() for a in deps.split(',') if a.strip()}
for name in re.findall(r"'PortableAdapter\.(\w+)' does not depend on any axioms",log):
    seen[name]=set()
if set(seen)!=expected: raise SystemExit(f'Incomplete theorem dependency audit: {expected-set(seen)}')
for name,deps in seen.items():
    if deps-{'propext','Quot.sound','Classical.choice'}:
        raise SystemExit(f'Forbidden dependencies for {name}: {deps}')
print(f'Audited all {len(seen)} theorem dependency lists')
PY
  cat proof.log
)
gate "$ROOT"
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT HUP INT TERM
# Deliberately bad copies must fail the same gate used above.
for case in sorry custom_axiom false_proof scope_removed proposed_promoted; do
  dir="$TMP/$case"
  mkdir "$dir"
  cp PortableAdapter.lean Tests.lean "$dir/"
  python3 - "$dir" "$case" <<'PY'
import sys
from pathlib import Path
p=Path(sys.argv[1]); case=sys.argv[2]
if case=='sorry':
    with (p/'Tests.lean').open('a') as f: f.write('\nexample : False := by sorry\n')
elif case=='custom_axiom':
    with (p/'Tests.lean').open('a') as f: f.write('\naxiom invented : False\n')
elif case=='false_proof':
    with (p/'Tests.lean').open('a') as f: f.write('\nexample : False := by decide\n')
else:
    f=p/'PortableAdapter.lean'; text=f.read_text()
    old,new=(('r.context = a.context ∧ r.authorityDigest = a.digest ∧',
              'True ∧ r.authorityDigest = a.digest ∧') if case=='scope_removed' else
             ('r.classification = .observed)', 'r.classification = .proposed)'))
    if old not in text: raise SystemExit('Mutation did not apply')
    f.write_text(text.replace(old,new,1))
PY
  if gate "$dir" > "$dir/result.log" 2>&1; then
    echo "Negative control erroneously accepted: $case" >&2
    exit 1
  fi
  case "$case" in
    sorry|custom_axiom) grep -q 'Forbidden proof token (preflight)' "$dir/result.log" ;;
    *) grep -q 'error:' "$dir/result.log" ;;
  esac
  echo "REJECTED negative control: $case"
done
