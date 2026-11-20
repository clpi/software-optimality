# Loop-invariant authority hashing: measured CI batch example

Additive experiment, not a replacement owner. Baseline is the sibling
`../pipeline` at `clpi/software-optimality` commit
`95df5fb7e922e7316b0ebe90b7847fd45a208d88`. This example preserves the existing
receipt-map contract; it does not create a new authority, graph, or proof kernel.

## Reproduce

From this directory run `python3 -m unittest -v`, `python3 -O -m unittest`, and
`python3 measure.py > fresh-measurements.json`. Standard-library Python only.
`loaders.batch` constructs every synthetic fixture deterministically. Recorded
source/authority/projection digests bind those inputs and exact outputs.

## Implementation and correctness argument

`pipeline_hoisted.py` is a pinned experimental copy of the baseline with only:
1. Compute `authority_sha256 = digest(authority)` before the record loop.
2. Use that value in each receipt instead of recomputing it for each record.

A test enforces the exact two-line transformation against the sibling baseline;
if the owner changes, the experiment fails rather than silently drifting.
For an ordinary JSON authority dictionary held fixed throughout a synchronous
call, `digest(authority)` is deterministic and unchanged by the record loop.
Replacing its repeated evaluations with one therefore preserves every receipt,
source digest/index, receipt ID, normalized graph, qualification and projection
hash. Nothing else is cached. Changed authority on a subsequent call is hashed
again. Neither prior authorization nor stale measurements can be reused.

The claim excludes concurrently mutated authority, monkeypatched impure hash
functions, custom stateful dictionary objects, and other violations of the JSON
input contract. The extra digest evaluation for a zero-record document changes
work but not output. This is a differential-tested engineering argument, not a
formal Python refinement proof or a new Lean theorem. Existing model proofs retain
their original scope.

## Measured results

Nine alternating-order pairs, one warmup per variant, `perf_counter_ns`, complete
build timed. Fixture construction and output equality checks are outside the
timed region. All timed outputs were checked equal. Raw samples and environment
are retained in `measurements.json`.

| CI records | baseline median | hoisted median | ratio |
|---|---:|---:|---:|
| 1 | 0.162 ms | 0.161 ms | 1.00x |
| 100 | 9.686 ms | 3.894 ms | 2.49x |
| 1000 | 619.611 ms | 76.177 ms | 8.13x |

An independent reviewer reran the same experiment and observed a **one-record
regression**: baseline 142,586 ns versus hoisted 163,341 ns (0.873x ratio).
Their larger-case ratios were 2.513x at 100 records and 9.363x at 1000.
This is a second run, not a replacement for the original raw measurements.
The tiny-batch regression is retained explicitly: overhead and measurement noise
can outweigh any benefit. There is no universal speedup claim.

These are synthetic multi-test batches through the actual adapter, not a foreign
production workload or a guarantee of future speed. Each authority contains N
test mappings: repeated authority serialization adds approximately quadratic work
in N in the baseline. The import authority-digest invocation count is tested:
N versus one for a nonempty batch. Other receipt hashing, validation, graph and
qualification costs remain; no universal complexity bound for the whole pipeline
or Pareto dominance across all resource axes is claimed. One-record/no-benefit
control is retained instead of selectively reporting only improvements.

## Controls

Nine tests normally and with `-O`: exact-diff pinning; full projections for batch
sizes 0,1,2,10,100; all four statuses; all six context mismatch refusals; changed
authority invalidation; byte-distinct provenance and withdrawals; malformed JSON,
duplicate keys and invalid status refusals; explicit stale-authority-cache
counterfactual; instrumentation of actual authority-digest invocation counts.
The stale-cache oracle fails equivalence when old authority receipt IDs are reused.

This preserves baseline limitations: identical-byte duplicate deliveries already
collapse to one receipt identity, and the declared harness/source truth is not
authenticated here. Measurements remain observations rather than automatic
qualification of every runtime or a replacement for correctness tests.
