# Exact-byte replay deduplication: empirical before/after

An additive example for the existing portable evidence owner. It does not replace
the pipeline or introduce a competing graph/qualification authority.

## Run

From this directory: `python3 -m unittest -v`, `python3 -O -m unittest`,
`python3 measure.py > fresh-measurements.json`. Python standard library only.
The sibling `../pipeline` is required; baseline dependency at repository commit
`95df5fb7e922e7316b0ebe90b7847fd45a208d88` is unchanged.

## Change and preservation argument

The baseline imports all N delivery documents and unions normalized receipts by
identity. The wrapper removes exact-byte duplicate documents within one call,
then delegates all remaining work to the same baseline. Each unique document is
still validated. There is no persistent cache, no authority reuse across calls,
no subject-only key, no whitespace normalization, and no observation suppression
based on a hash alone (Python sets compare byte equality even on hash collision).

For fixed authority and withdrawal snapshot, deterministic import of equal bytes
yields equal receipts; duplicate insertion into the receipt map is idempotent.
The baseline already loses identical-delivery multiplicity and arrival order;
those are not fields in this projection. Removing those duplicate insertions
therefore preserves the map, sorted events,
withdrawal checks, graph, qualifications, proposed tasks, and projection hash.
An invalid unique document still fails. This is an engineering argument checked
by differential tests, not a new Lean refinement proof. The existing Lean
`PortableAdapter.duplicate_idempotent` is the corresponding typed-support lemma,
not proof that this Python wrapper implements it. Only immutable bytes are in
this wrapper's input contract; mutable bytearray is rejected.

### Explicit non-equivalence outside this API

An arrival audit/count view distinguishes `[receipt]` from `[receipt, receipt]`;
this projection does not. Do not use this wrapper to count independent runs or
arrival frequency. Distinct executions need distinct source provenance bytes
under BOTH versions; identical-byte independent executions are already collapsed
by the baseline. No optimization claim extends to a changed contract retaining
arrival multiplicity, side-effectful importers, or concurrently mutable authority.

## Recorded local experiment

`measurements.json` preserves all nine raw alternating-order paired timings per
workload, Python/platform, complete-build timed region, counts and projection
hash. Input construction and output-equivalence checking are outside timings;
one untimed warmup per variant precedes sampling. Ratios are ratios of medians,
not population speed guarantees. Workloads are synthetic replay patterns over
the repository's real adapter fixture, not a production trace or foreign solver.

- 1000 identical deliveries: median 92.103 ms baseline, 0.309 ms dedup, 297.76x.
- 1000 deliveries / 10 byte-distinct documents: 96.967 ms vs 1.399 ms, 69.30x.
- 100 distinct deliveries: 10.719 ms vs 9.968 ms, 1.08x; do NOT infer a benefit
  here from this small noisy difference. No import-work reduction on this case.

Logical import counts decrease exactly from N to U distinct documents. Extra
memory holds U byte references/set entries, and hashing/comparing bytes costs
work. All-unique traffic may regress. These measurements do not establish Pareto
dominance across workloads or other resource axes, nor future runtime bounds.

## Tests and counterfactuals

Nine tests in normal and optimized modes include all 121 sequences of length
0..4 over three source encodings, conflict retention, withdrawal, refusal,
changed authority, and byte-distinct provenance. The deliberately wrong
subject-only-cache counterfactual demonstrably loses a failing receipt: the
reference output comparison detects the difference. This catches the temptation
to make a faster but semantically invalid cache.

The source hashes in this directory's manifest bind this experiment only. Root
manifests/check owners are untouched. Raw timings are observed evidence, not a
new pass/fail qualification or a substitute for the test/benchmark source truth.
