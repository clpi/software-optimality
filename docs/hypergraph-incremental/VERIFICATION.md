# Hypergraph incremental proof publication verification

Source SHA-256: `57d63384979e1fc78cf5ec0fb8fb7d58a60a1e04d3a74eed966b8d9e36d24ee1`.

Publisher independently ran Lean 4.19.0 on all 14 named proof modules with warnings treated as errors and checked every exit status. The separate ReviewControls.lean passed 17 proof examples and 9 executable guards. All tests here are synthetic; they are not production benchmarks.

Controls exercise conjunctive premises, unsupported cycles and retraction, old-topology invalidation, alternate support, edge kind/port replacement, and the raw-list identity boundary. Injected proof admission and injected compiler error were independently rejected with nonzero status. Their logs intentionally contain rejected diagnostics; success logs contain no admissions or errors.

Reproduce from repository root:

```sh
set -eu
./check.sh
LEAN_PATH=. lean -DwarningAsError=true -o HypergraphIncremental.olean HypergraphIncremental.lean
LEAN_PATH=. lean -DwarningAsError=true docs/hypergraph-incremental/ReviewControls.lean
```

The module and scope document distinguish semantic incremental equivalence from an optimized executable worklist; matrix updates still scan retained lists. Admission-normalized, unique scoped ledger identities are an external obligation. A duplicate raw record counts twice, withdrawing its ID removes both, and remove-then-add of the same ID reintroduces it. No idempotent raw ledger merge or permanent tombstone protocol is claimed.

Standard Lean foundational dependencies are disclosed by printed axiom inventories. No custom axiom, admitted proof, or native_decide shortcut is used. Existing files not listed in the publication change set remain unchanged.
