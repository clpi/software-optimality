# Contextual dominance publication checks

Publisher independently checked all 15 modules through the repository fail-closed checker with Lean 4.19.0, plus the six independent Controls.lean proof examples. Source SHA-256: c7d84c02a5252341c4b9ce712409f75ce5248b6f524d4f4988bec86cd3754b38.

All six printed contextual theorem dependencies are axiom-free. Synthetic controls demonstrate why feasibility and contextual monotonicity are necessary, and distinguish exact preservation of frontier cost vectors from retention of every tied candidate identity. These are theorem/fixture checks, not runtime benchmarks.

Reproduce from repository root:

```sh
set -eu
./check.sh
LEAN_PATH=. lean -DwarningAsError=true -o ContextualDominance.olean ContextualDominance.lean
LEAN_PATH=. lean -DwarningAsError=true docs/contextual-dominance/Controls.lean
```

No admission-normalization work is included. The context/feasibility/cost adapters, representative coverage witnesses, and measured runtime fidelity remain external obligations, as detailed in SCOPE.md. Existing hypergraph and empirical artifacts are preserved.
