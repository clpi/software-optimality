# Executable hypergraph edits through release selection

The public proof dependency is commit `91563b8742cb97c13bb9eb7123b90e5cb3c31fcb` of `clpi/software-is-quantifiable`. The optimality changes extend commit `064852fb7a83c7a17950a78b77860175f95e1290`. Both standalone packages and the joint proof build with Lean 4.19.0, commit `6caaee842e94`. The public and private sources are compiled together from source in the joint check.

## What the proof connects

1. **Admission.** The existing live decoder consumes authorized claims after normalization, withdrawals and conflicts. Decoding creates the current roots and complete hyperedges. Physical truth of an observation, identity binding, and authorization of its source remain obligations at ingestion.
2. **Invalidation.** Changed root memberships and the heads of changed hyperedges seed the affected region. The reference update derives unary dependency arcs from both hypergraphs. An empty-premise rule still seeds its head. The theorem `dirty_exact` equates the executable result with the inductively defined affected region.
3. **Recomputation.** The algorithm retains previously derived atoms outside that region, takes new roots, and evaluates original new rules with affected heads. Each firing requires all premises and consumes one pending rule. Induction over the remaining rules proves saturation equals the least rooted closure. Induction over reachable cache states then covers any finite sequence of insertions, replacements, and withdrawals. Duplicate and differently ordered facts have identical membership semantics.
4. **Qualification.** `replay_agrees_with_coloring` connects cache membership to the public witness fold and Horn coloring. `selectCached_exact` passes those facts through the existing release selector. Bounds, receipt validation, positive and contrary evidence, hard caps, metric directions, and incumbent eligibility retain their existing semantics.
5. **Selection.** `evaluate_exact` takes a deterministic function that reads the campaign, domain, catalogue and incumbent from the current graph. It proves exact equality of the optional ordered result with full recomputation. This includes `none` on invalid input, `some []` for a valid empty frontier, and all candidate ties and their input order. `live_revision` connects an admitted edit to the existing full live selector. `point_frontiers_agree` and `release_gates_agree` also check the two repositories’ public point comparators and release gates against one another.
6. **Optimality certificate.** `certificate_eq_full` proves the cached path gives the same three-way verdict as `ScopedFrontier.certifyClosed`. A malformed universe gives `none`, a refused certificate gives `some false`, and acceptance gives `some true`. On acceptance the existing certificate theorem identifies exactly the retained frontier of the named generator domain and supplies the scoped receipt obligations. Extending this to a larger external generator requires coverage and correct identification of its feasible alternatives.

## Counterfactuals

| Change or shortcut | Witness and resolution |
|---|---|
| Use the binary index as evidence | One joint edge `{a,b} → q` and two alternative edges `{a} → q`, `{b} → q` have identical binary arcs. With only root `a`, the joint graph withholds `q` and the alternatives derive it. Updating between the two gives the correct result in each direction. |
| Treat the old index as indispensable | Once **every changed edge head** is seeded, a propagation step on an old-only rule reaches a head already seeded by that deletion. Every surviving rule contributes the same arc to the new index. `new_arcs_suffice` proves new-arc propagation visits exactly the same atoms. Both snapshots still participate in finding the changes. |
| Warm-start a cycle after withdrawing its only root | With `a → b → a`, the stale facts keep each other live. Rebuilding affected facts from grounded support empties the cycle. With independent surviving support, grounded consequences return. |
| Trust an arbitrary old cache | With two empty, identical snapshots, passing raw cache `[99]` to `update` retains 99. The controls prove this cache cannot be reached through `start` and `advance`. An external cache loader would need its own validation. |
| Reuse the visible frontier or reuse the old contract | Withdrawing one dominator makes another candidate eligible for the output. Removing validated ledger records can invalidate the incumbent and yield `none` on the same closure. The selector rereads the current contract and all current catalogue entries. |
| Count names, ignore occurrences or scope | Runs [A,A,B] can be replaced by [A,B,B] while preserving distinct-name coverage. `orderings_exact` rejects the substitution. `scoped_recorded_exact` rejects a witness from a different named scope even when its local execution ID matches. |
| Infer actual coverage from an empty missing list | Omitting an execution from the manifest can make the audit pass. `Coverage.audit_complete` requires an independent equivalence between actual occurrences and manifest membership. |
| Promote a cost ranking to per-execution non-regression | Trade-offs remain possible on the exploratory Pareto frontier. The incumbent gate enforces the named no-worse policy. The interval gate is exact over independent Cartesian boxes. Paired scenarios can exclude the extremal pair. |

## Executed checks

From the repository root run the following with the pinned toolchain. To use a local public checkout, set `QUANTIFIABLE_SRC` to the exact dependency above.

```sh
lake --wfail build
./check.sh
./tools/check_optimality.sh
./composition/check.sh --exhaustive
```

The exhaustive run covers every root subset and every set of positive rules with canonical set-valued bodies over two atoms. There are four root choices and 256 rule choices. All 1,024 × 1,024 ordered edits agreed with the independent exhaustive-model intersection on both atoms. This includes simultaneous changes of many rules and roots. General correctness and repeated or reordered premise lists are covered by the theorem. Three deliberate definition changes failed proof checking when disjunction replaced conjunction, old cache facts were retained indiscriminately, or changed rule heads were omitted. On the pinned public sources, four further changes also failed their proofs: fabricate a matching record, skip its validator, drop the compute axis, or drop behavior inclusion. The joint checker audited the transitive logical dependencies of 1,391 theorem declarations in 37 modules against `propext`, `Classical.choice` and `Quot.sound`. Generated theorem declarations are included in its count.

## Archived campaign replay

All three archive blobs matched their Git object IDs. The archive checksum manifests and supplied receipt checkers passed. These results replay observations already collected. No new physical timing campaign was performed.

| Archive | Records checked | Outcome |
|---|---:|---|
| Original campaign | 36 subprocess records | An independent enumerator recovered all 120 two-worker ordered queues, their modeled costs and the four-member modeled frontier. |
| Four-arm ablation | 64 subprocess records | Reversing test order lost to original order under two workers in all four paired rounds. The deliberate order-dependent test retained the same collected IDs and failed under reversal. |
| Qualification campaign | 36 subprocess records | O1, O2 and R2 passed the named gate. On maximum observed suite wall time their costs in nanoseconds were 10,769,189,848, 6,240,471,073 and 9,146,680,841. O2 was the sole frontier member. Eight of its twelve paired subprocess times exceeded O1. |

The regenerated qualification report SHA-256 was `037ce2972cbf5bb72de79e24e3c914b4254406a488696a5e4e9f7b00eff50b73`. The policy SHA-256 was `44faa39b813fe8ff0571957fa2f535d2d6d022ebd765cf8c0d95296ef5d40416`. These match the bindings in `EligibleCampaign.lean`. Extraction and replay commands for the archives are in `evidence/README.md` and `evidence/QUALIFICATION-SCOPE.md`.

The exactness claim covers the admitted positive hypergraph and declared comparison policy. A changed observation, contract or symbol must be represented in the current snapshot or reread by its deterministic projection. Physical mediation, general program equivalence, completeness of an externally supplied implementation catalogue, and fresh performance or speedup claims require separate evidence. An edit may invalidate the entire graph.
