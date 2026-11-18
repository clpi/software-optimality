# Portable evidence adapters, version 1

Small runnable CI-result and raw benchmark importers, not a new solver or an
execution sandbox. Python 3 standard library; POSIX shell orchestration; optional
C99 sample-summary bridge. Run `./run.sh`, or:

```
python3 pipeline.py fixtures/authority.json fixtures/ci.json fixtures/benchmark.json
```

## Authority and composition

The caller supplies `portable-authority/v1` separately from untrusted result
files. Pin its SHA256 in your CI policy. It fixes six context IDs (artifact,
lineage, environment, harness, workload, venue), admitted subjects, test status
mappings, and the authoritative hypergraph schema. Context comparison is exact;
unknown fields, subjects, duplicate JSON keys, nonfinite numbers and malformed
records are refused. A context string is an identifier, not an attestation.
The adapter does not derive or verify the completeness of the dependency model.

`ci-results/v1` accepts records `{subject,status}` with pass/fail/skipped/error.
Pass and fail emit separate declared atoms; skipped/error retain receipts but
supply no successful support. Missing tests remain unsupported, not passed.
A suite's required tests must be expressed by conjunctive authority edges.
Pass records qualify exactly the declared case, not every input or entire release.

`benchmark-samples/v1` accepts `{subject,samples_ns}` with a nonempty list of
nonnegative integer nanoseconds. Zero is allowed for measurement resolution.
Its only direct atom is `measurement:<subject>`: measurement availability, NOT
speed, improvement or optimality. Raw samples remain intact. No automatic
conversion of samples into fixed deterministic future scheduling durations is
performed. Any performance threshold, experimental noise rule, environmental
comparability or prediction policy requires a separately specified checker.

Every record becomes a content-addressed `portable-receipt/v1` observed receipt,
including the exact original bytes' SHA256, record index, authority SHA256 and
complete context. Different byte encodings produce different provenance receipts.
Store original files beside receipts: a digest is not a substitute for the bytes.
Hashing is not source authentication, trustworthy timing, or semantic proof.
The local API re-imports source bytes rather than trusting submitted receipt IDs.

Union of repeated identical receipts is idempotent and insensitive to input-file
order. Historical receipts, inferred consequences and proposed tasks are three
separate fields over the SAME hypergraph, not independent mutable authorities.
Contradictory passing/failing observations yield conflict, not last-writer-wins.

## Projection and withdrawals

The normalized graph is compatible with the vendored, unchanged
`hyper-reference/reference.py` (here `reference_kernel.py`). Its environment key
is the digest of the full six-field context; lineage is also explicit. Every
rule and task inherits that scope. No cross-lineage evidence transfer is assumed.
`inferred_view` is Horn conjunction closure, not equality saturation.
`incidence` is derived with separate premise/head roles.
`proposed_tasks` are declared prospective actions, NOT observations or results.

`--withdraw receipt:...` is an authoritative caller operation. Unknown or duplicate
targets are refused. Original receipts remain immutable; graph support and its
consequences are recomputed without withdrawn supports. Withdrawing a skipped
receipt changes withdrawal metadata but no support, since none existed. Earlier
projection hashes remain reproducible. This is a snapshot withdrawal interface,
not a distributed authorization or revocation protocol.

## Practical closed loop

1. Pin authority and exact context in the orchestrator.
2. An existing CI/harness emits these strict result records; this adapter executes
   no code, commands, macros, network calls, or payload expressions.
3. Import raw bytes and archive the normalized projection with sources.
4. Inspect unsupported/conflict outcomes and the derived incidence/support paths.
5. Select an authorized proposed task in the external runner; its actual output
   reenters as a new observed receipt. The current package does not launch it.

The fixture composes one passing checkout receipt and three latency measurements
into a receipt-completeness qualification, not a latency qualification. A
withdrawal of the test retracts that derived qualification. Schedule optimization
can consume a declared graph through `reference_kernel.solve`; that routine is
exact only for its declared integer-duration model, not an empirical speed claim.

## Shell and C interoperability

`run.sh` contains no evaluation of input content, quotes paths, and uses a temporary
directory. `export_samples.py` validates complete input and exports a narrow ASCII
protocol: count line, then that many unsigned decimal nanosecond lines. The C99
checker rejects overflow, signs, trailing data and missing values and prints
count/min/max. It neither parses JSON nor independently authenticates receipts.
Python integers are arbitrary precision; the C bridge rejects values beyond
uint64 rather than truncating. Repeated samples remain repeated. Other languages
should use strict JSON decoding and the canonical ASCII JSON definition in
`pipeline.canonical`; do not hash pretty-print output as a receipt identity.

## Evidence and limits

15 Python tests run normally and with `-O`; shell reproduces the fixture byte for
byte, and the C bridge checks valid and malformed streams. The vendored kernel is
unchanged; compare SHA256 with its upstream local bundle. These are execution
tests, not a Lean proof of Python refinement. The companion adapter Lean model
(if distributed) must identify its bridge obligations explicitly. This package
makes no claim of Lean equivalence, universal performance dominance, or producer
honesty. The authority still must bind real software, harness and policy correctly.
