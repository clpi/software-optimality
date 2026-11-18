#!/bin/sh
set -eu
cd "$(dirname "$0")"
LEAN=${LEAN:-lean}
mkdir -p evidence
"$LEAN" --version > evidence/version.txt
"$LEAN" --githash > evidence/commit.txt
grep -q '4.19.0' evidence/version.txt
test "$(cat evidence/commit.txt)" = 6caaee842e9495688c1567e78c0e68dbb96942aa
"$LEAN" -DwarningAsError=true fixtures/Kernel.lean > evidence/kernel.txt 2>&1
"$LEAN" fixtures/Axiom.lean > evidence/axiom.txt 2>&1
# Compatibility records admission; secure qualification is a separate policy.
"$LEAN" fixtures/Admission.lean > evidence/admission.txt 2>&1
if "$LEAN" -DwarningAsError=true fixtures/Admission.lean > evidence/admission-strict.txt 2>&1; then exit 1; fi
if "$LEAN" fixtures/Invalid.lean > evidence/invalid.txt 2>&1; then exit 1; fi
"$LEAN" --run fixtures/Program.lean > evidence/runtime.txt 2>&1
python3 - <<'PY'
from pathlib import Path
p=Path('evidence')
assert 'explicitAssumption' in (p/'axiom.txt').read_text()
assert 'sorryAx' in (p/'admission.txt').read_text()
assert 'warning:' in (p/'admission.txt').read_text()
assert 'error:' in (p/'admission-strict.txt').read_text()
assert 'error:' in (p/'invalid.txt').read_text()
assert (p/'runtime.txt').read_text().strip()=='lean-runtime-oracle'
assert (p/'kernel.txt').read_text().splitlines()[-1]=='12'
PY
