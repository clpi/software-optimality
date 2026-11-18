# Typed comparison publication verification

Publisher independently checked the integrated 20-module Lean 4.19.0 suite, all 25 ComparisonTests executable guards and 4 examples, plus 8 independent review guards and one proof. InvalidTransport.negative was compiled separately and correctly rejected: identity conversion cannot satisfy the fixed milliseconds/microseconds semantic interpretation.

Reviewed ComparisonContract.lean SHA-256: a34f87b6321e591bb08f49cdc1cb9ca69a0fa4946f11cbd17772e51977d85255.

Reproduce from repository root:

```sh
set -eu
./check.sh
LEAN_PATH=. lean -DwarningAsError=true docs/typed-comparison/ReviewControls.lean
```

The fixed meaning function and metricSound implication are application admission obligations, not selectable assertions supplied by an untrusted certificate. Contracts use exact IDs and integer samples; physical measurement truth, hash binding and runtime invariance remain external. All controls are synthetic. No benchmark speedup or universal optimum follows from the gate.
