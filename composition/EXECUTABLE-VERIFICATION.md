# Executable hypergraph edits through release selection

This integration reconciles PR #5 (`ea053df55f88911b19815441182f20e083ecf4d8`) with
master `ec1eadda0a29d1b254a98feb5ad24911a095c454`. It preserves the canonical Lake
dependency and owners introduced since the original branch: `CanonicalDominance`,
the aligned identity frontier bridge, `ThreeValuedGate`, transfer and evidence
transport, worklist closure, strict schedules, linked certificates, scoped
compatibility, the historical-observability modules, historical ledger cuts, and the covered-frontier controls.
The canonical quantifiable dependency is merged commit
`d88acbdc3ba78fff994067d2c73bcc01622b3f61` (tree
`803ec87bd775cbcca5ba016f3e71d45b3ec3294e`).

## Reproduce

Use the pinned Lean 4.19.0 (`6caaee842e94`) toolchain:

```sh
sh check.sh
sh tools/check_optimality.sh
sh composition/check.sh --exhaustive
python3 examples/history_roundtrip.py --replay examples/history-recording.json
python3 examples/history_roundtrip.py --replay examples/history-recording.json --cut after
```

The joint command builds the canonical Lake target with warnings as errors,
checks transitive theorem dependencies, runs the existing six false-claim
refusals, and executes every ordered edit between the enumerated two-atom
snapshots. The dependency revision has one owner: the canonical Lake require and
manifest. The removed temporary-copy/checksum dependency runner remains removed.
The receipt under `composition/incremental/` binds the final source, dependency,
toolchain, commands, logs, outcomes, and manifest. The prior receipts under
`composition/current/` and `docs/covered-frontier/` retain their original pins.

## What the proof connects

1. **Admission.** The live decoder consumes normalized authorized claims after
   withdrawals and conflicts, producing roots and complete hyperedges. Physical
   truth, binding identities to executions, and the authorization source remain
   ingestion obligations.
2. **Invalidation.** Changed root memberships and every changed edge head seed
   the affected region, including empty-premise rules. The reference `dirty`
   derives transient unary arcs from both snapshots, and `dirty_exact` equates
   its result with the semantic affected region. The executable `update` now
   constructs only the new-rule arcs: `new_arcs_suffice` proves old-only
   propagation arcs redundant when every changed edge head is seeded. Finding
   those changes still reads both snapshots. `update_reference_exact` proves
   exact returned-list equality to the normalized old-and-new-arc reference
   because both stable filters depend only on invalidation membership. This removes the old-rule
   arc list and its concatenation from the update path; no timing or peak-memory
   improvement is inferred without measurement.
3. **Recomputation.** Each firing requires every premise and consumes one pending
   rule. `saturate_exact` proves least rooted closure. `update_exact` retains only
   unaffected cached facts and recomputes affected consequences. `State` carries
   a proof of API reachability, and `reachable_exact` covers every finite edit
   history. Exported `full` and `update` results erase duplicate facts, with
   membership-preservation and `Nodup` proofs. This prevents duplicate roots or
   repeated unchanged revisions from growing persistent cache storage.
   `reachable_length_eq_full` equates stored size with the unique full closure;
   `advance_same_length` proves unchanged revisions preserve cache length for
   every reachable state and every finite snapshot. Transient
   evaluator lists may still contain duplicates; normalization adds a list pass.
   Imported caches do not acquire validity merely by matching a key.
4. **Qualification.** `replay_agrees_with_coloring` relates cache membership to
   the public witness fold and Horn coloring. `selectCached_exact` uses the
   existing qualified selector, retaining validation, current contrary evidence,
   hard caps, metric directions, and incumbent eligibility.
5. **Selection.** `evaluate_exact` rereads the campaign, universe, catalogue and
   incumbent through a deterministic projection of the current snapshot. The
   complete optional ordered result equals full recomputation: `none` for invalid
   input or baseline, `some []` for a valid empty result, and every surviving tied
   candidate in input order. `live_revision` composes normalized ledger updates.
6. **Certificate.** `certificate_eq_full` preserves the existing three-way
   `ScopedFrontier.certifyClosed` verdict: invalid universe, refused certificate,
   and accepted certificate. The covered-generator and feasible-generator
   guarantees retain their explicit coverage and qualification premises.

`point_frontiers_agree` checks both point comparator projections. The canonical
public `Pareto.acceptsRelease` owns release admission; `release_gate_exact` only
projects its obligations through the existing point representation. The deleted
local release and behavior-retention functions are not restored.

## Counterexamples retained

| Shortcut | Executable witness and correction |
|---|---|
| Use binary arcs as evidence | A joint edge and two alternative edges have identical binary arcs but different conclusions from one root. Updates in both directions use the original complete premise sets. |
| Keep a withdrawn cycle warm | Old cached cyclic facts can sustain one another after their root disappears. Rebuilding affected facts from grounded support removes them. |
| Omit changed edge heads | Adding or deleting an empty-premise rule has no incoming arc. Its head must still seed invalidation. |
| Accumulate roots on unchanged updates | Repeating a singleton snapshot 100 times still stores one fact. Duplicate roots and duplicate or redundant rules also leave one copy of each derived fact. |
| Trust an arbitrary cache | Updating two empty snapshots with raw cache `[99]` retains the forged fact. The controls prove that cache is not reachable through `start` and `advance`. |
| Reuse an old frontier or policy | Withdrawing a dominator exposes another candidate; withdrawing validated ledger support can invalidate the incumbent on an unchanged closure. Selection rereads current inputs. |
| Delete equal-cost identities | The preserved aligned identity bridge and its controls retain distinct tied candidates. Profile equality does not justify identity deletion. |

The exhaustive harness enumerates all root subsets and all sets of positive
rules with canonical set-valued bodies over two atoms. It compares each update
with the independent powerset-model intersection, checking both membership and
unique cache size. General correctness, repeated
premises, and reordered lists follow from the theorem; this finite test does not
establish arbitrary-domain completeness by counting.

## Evidence boundaries

The original PR #5 reported archived campaign replays and earlier mutation
checks at its own source and dependency pins. Those historical results are not
fresh performance evidence for this integration. The unchanged archive importer
and campaign theorems remain in the default target. No new physical timing
campaign is performed here.

Exactness covers positive hypergraph membership and the declared comparison
policy. A relevant change must appear in the snapshot or in its freshly read
projection. Scope labels and execution IDs are supplied data until ingestion
validates them. Sequence multiplicity preserves occurrences of supplied run
values; it does not authenticate independent invocations. Catalogue completeness,
physical measurement truth, production-program equivalence, independent execution
origins, concurrency, and crash recovery require their own evidence. An edit can
invalidate the entire graph. No global Pareto optimum, native Idol producer
migration, or runtime speed claim follows from these proofs.
