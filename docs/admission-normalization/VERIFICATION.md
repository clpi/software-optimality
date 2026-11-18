# Admission normalization publication verification

Publisher independently built the integrated 18-module Lean 4.19.0 suite with warning-as-error and admission/error diagnostics rejected. AdmissionTests contains 18 executable guards and 5 proof examples. Additional independent review controls contain 8 executable guards and 2 scope/transfer proof examples.

Reviewed source SHA-256 values:

- Admission.lean: 2a4bfc44f7e5343ff01b2d253300d0240893c4686c8607eeca611dc1ce9dfe51
- AdmissionHypergraph.lean: d3377acc9cbac053dc5f24c8f60b86cd977083372223d32179a95ac60815f2c0
- AdmissionTests.lean: 46d4b392a705807d79cc699304bf32fa255b0e0f3837b41aa2aad09607c52146

Reproduce from repository root:

```sh
set -eu
./check.sh
LEAN_PATH=. lean -DwarningAsError=true docs/admission-normalization/ReviewControls.lean
LEAN_PATH=. lean -DwarningAsError=true docs/admission-normalization/ScopeControls.lean
```

All controls are synthetic, not production benchmark claims. Admission normalizes live membership and preserves provenance through derived hypergraph closure. Authorization, cryptographic identity binding and transfer-decoder semantic truth remain explicit inputs. Set membership is order-independent; serialized list ordering is not. This closes a reference-model normalization gap, not every production adapter obligation.
