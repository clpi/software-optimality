# Portable evidence pipeline and checked admission model

This additive package connects recorded CI outcomes and raw benchmark samples to
one scoped directed hypergraph view, with a corresponding Lean model. It does not
replace the repository's existing qualification, closure or Pareto owners.

## Reproduce

With Python 3, a POSIX shell, optional C99 compiler, and Lean 4.19.0:

```sh
sh portable-evidence/pipeline/run.sh
LEAN=/path/to/lean sh portable-evidence/lean/check.sh
```

The Python runner tests normal and optimized interpreter modes, exact fixture
replay and the C sample-summary boundary (C is explicitly skipped without `cc`).
The Lean runner recompiles fresh, audits all 15 named theorem dependencies,
checks 21 guards plus a derivation example, and verifies five corruptions fail.
No network or foreign-code execution is required by these checks.

## Single input authority; distinct evidence classes

The external authority fixes artifact, lineage, environment, harness, workload,
venue and admitted subject mappings. Receipts retain source digest/index and
identity, and exact context mismatches fail. Test pass/fail observations are
separate; skip/error receipts do not produce support. Benchmark sample receipts
say only `measurement:<subject>`, not that an optimization improved performance.
Withdrawals remove an identified support from the current projection, while raw
history remains available. Inference requires authoritative conjunctive edges;
proposed tasks remain distinct from observed qualification.

`pipeline/reference_kernel.py` is a vendored, pinned small reference adapter,
not the production owner or a new authoritative graph. Incidence, observed and
qualified views are derived from the same input. Its fixture schedule/prospective
coverage is not a proof of future measured timing or universal Pareto dominance.

## What is proved, and what remains a boundary

`lean/PortableAdapter.lean` proves the executable typed model's normalization and
support extraction match its explicit declarative meaning, preserve context and
provenance, disallow synthetic-observation promotion, and compose with rooted
conjunctive derivations under merge/withdrawal. See [Lean scope](lean/SCOPE.md).
The Python implementation is tested, **not formally refined to Lean**. JSON,
canonical bytes, cryptographic hashes, observation truth, caller authorization,
subject mappings and inference-rule validity remain separately specified
boundaries. No claim of signatures, secure attestation, Idol/Lean equivalence,
whole-program correctness or all-workload dominance is made.

## Evidence

- Python: 15 tests in each of normal and optimized modes, exact fixture replay,
  C99 sample summary and malformed-input controls.
- Lean: fresh 4.19.0 build, all 15 theorem dependency lists, 21 executable guards,
  one rooted-derivation example, five expected-stage negative controls.
- Local independent review reran both packages before publication. Published
  check script differs from the reviewed local one only by defaulting to `lean`
  on PATH instead of an environment-specific absolute executable path; the
  complete published package was rerun after that packaging adjustment.
- Hash inventories are local artifact integrity aids, not author signatures.

Existing root files, module owners and default repository build remain unchanged;
these checks are intentionally independently runnable while the correspondence
boundary is explicit. The package is proposed as a draft PR, not merged.
