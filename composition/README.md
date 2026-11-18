# Composing qualification, selection, and trace proofs

For a finite catalogue, a proposed subset, and a transitive irreflexive
dominance relation, `checkCover_iff_same_frontier` proves a necessary
and sufficient condition for safe pruning. Every removed identity must have a
strictly better retained witness. This is an exact decision procedure for
preserving every frontier identity, including ties. It has no dependency on how
the search found the subset. It applies equally to exhaustive search, a human
proposal, a heuristic, or a learned generator. The existing final-frontier certificate also accepts exactly the complete set of surviving identities, by `certificate_iff_frontier`. Completeness of the original
catalogue for an application remains a separate obligation.

## Reproduce

Run `./composition/check.sh` with Lean 4.19.0. It fetches the pinned public
qualification proof and builds both source trees in an empty directory. For
offline verification, set `QUANTIFIABLE_SRC` to a checkout containing the
pinned source bytes. `LEAN` can name an absolute compiler path. The script
checks SHA-256 for all six upstream sources, runs the full optimality suite,
then checks the integration modules, controls, and benchmark source. Pass
`--benchmark` to collect a new timing table. The standalone offline suite
continues to run through `./check.sh`.

The public proof at `61de9b7364e0a8c5ddc2ab8d0a633d2920aa38cf` builds on its
own pinned Lean 4.15.0 and also compiles under the joint 4.19.0 kernel.
The upstream unused-variable warnings are present in the log. The new proof
modules and the private suite compile with warnings treated as errors.
Dependency prints for the joint theorems contain only the standard foundational
axioms. See [the checker output](CHECK.log) and [the source hashes](quantifiable.sha256).

## What the entry points establish

| Engineering decision | Executable or theorem | Guarantee and boundary |
|---|---|---|
| Which executions have evidence? | Public `Coverage.missing`, `missing_append` | The missing roster after merging two ledgers is their intersection of missing executions. The caller owns roster completeness, execution identity and witness validation. |
| Which claims are live? | `Admission.normalized`, `LiveSelection.select`, `selected_live` | Only authorized, unwithdrawn, uncontradicted claims feed the finite decoder. Every selected behavior has positive derivation and lacks its specified contrary in the decoded graph. Scope preservation and semantic validity of the decoder require evidence. |
| Which consequences follow? | `QualifiedClosure.checked`, `checked_exact`, `checked_none` | The list scan, public Horn coloring, private rooted derivations, semantic incremental update, and exhaustive model intersection agree in membership on bounded input. Both checked algorithms reject the same invalid inputs. Duplicate catalogue positions can survive in the output list. |
| What does a metric measure? | Existing `MetricRelevance` and `ComparisonContract`; `LiveSelection.typed_cover_exact` | Relevance coordinates retain their denominators. Typed observations share units, direction, aggregation, workload, venue and epoch by contract. Existing transports require a proof of meaning preservation. Typed pruning retains all optimal identities under that contract. Empirical causal attribution needs independent evidence. |
| Which release may replace an incumbent? | `QualifiedSelection.select`, `selection_exact`, `release_evidence` | The incumbent first qualifies. Every selected candidate meets the same behavior vocabulary, scoped round obligations and timing limits, has a validated ledger witness for every receipt, and has no worse recorded peak on each named timing metric. Then the complete eligible frontier is returned. `none` marks invalid input or incumbent; `some []` marks a valid empty result. |
| When may search prune a component or shard? | `FrontierComposition.checkCover`, `Cover.flatMap`, `partition_exact`, `selected_partition` | Transitive reductions and shard merges preserve frontier membership. A typed continuation may enumerate zero, one or many legal completions. Each discarded completion has to survive by identity or have a strictly superior completion. Shared capacities, effects and failure modes belong in that continuation. Repeated application handles arbitrary finite composition depth. |
| What if costs are uncertain? | `IntervalDominance.separates_iff`, `refinement`, `paired_exact` | Testing opposite corners is necessary and sufficient for strict dominance over independent closed interval boxes on the named axes. Narrower valid boxes preserve a verdict. Shared scenario identities can certify a pairing that overlapping marginal boxes lose. Probability or confidence for unseen scenarios needs a sampling model. |
| Can a finite release decision carry a property of an unbounded system? | `TraceSafety.Simulation.comp`, `selected_trace_safety` | If the selected fact decodes to a checked forward simulation and the specification satisfies a trace property, every finite execution trace of the implementation satisfies the translated property. State spaces and finite trace lengths are unrestricted. Root truth, rule soundness, the simulation and the specification property are explicit premises. |

The timing path uses the existing `ScopedFrontier.Contract` and `admitted` gate. Its peak adapter accepts minimized objective metrics with all their required rounds selected and takes the maximum recorded elapsed value per such metric. Hard-gate-only metrics stay outside ranking. Each
(metric, round) is required exactly once and each admitted elapsed value is
present. The theorem `peak_le_iff` connects a peak bound to every present reading of the metric. A smaller maximum can coexist with a slower individual round. Different metrics may be measured in one execution. Reusing that
execution as a second round of the same metric fails the gate. Distinct
execution IDs do not establish statistical independence. The gate checks the
supplied receipt-to-execution mapping and ledger predicate. An application
must establish their authenticity and the binding of IDs to configurations and
metric definitions. Catalogues involving maximization, unit conversion, or arbitrary
cost types can use the general typed comparator; the receipt-based peak selector
specifically minimizes elapsed metrics.

## Counterexamples and application

* In a compiler pipeline, a locally faster representation may lack the next
  pass's required interface. In the control fixture the cheaper component has
  no legal completion and deleting the more expensive component loses the only
  result. The final-catalogue certificate detects that loss.
* For two tasks behind a shared bottleneck, local costs 1 and 2 both become 5.
  Both plan IDs remain on the frontier. If the required observable is only the
  scalar value, projecting both to 5 permits deduplication. The existing
  contextual bound and vector theorems support that weaker requirement.
* In a release campaign, one plan is fastest in steady state but misses the
  incumbent's recovery latency. It is excluded before ranking. Withdrawing a
  joint premise removes one alternative despite its self-loop. Restoring an
  independent support brings it back; a live contrary bars it. After both
  dominators are withdrawn the incumbent returns.
* For a controller, a deadlocked implementation can forward-simulate a ticking
  specification while never ticking itself. This supplies a checked witness
  that prefix safety leaves a progress obligation. A deadline or eventual
  response claim needs an explicit progress, scheduling and time model.
* The existing foreign-test pilot is replayed through partitioned scoped
  selection and still returns O2. All new ledger and controller cases are
  synthetic. See [the release controls](Controls.lean) and [the trace control](TraceSafety.lean).

Three deliberate mutations were also exercised independently. Altering the
pinned coverage source failed its SHA-256 check. Replacing the bounded-input
test with `true` failed the closure refinement proof. Changing the bottleneck
frontier expectation to a single winner failed by kernel reduction.

## Cost and measurement

The original finite model intersection enumerates exactly
`2^u` positional subsets for a universe of length `u`. The scan makes
`u + 1` rounds. A round reads all rules against the previous fact list,
materializes the fired heads, and filters the universe. Every resulting
fact list has length at most `u` by `materialized_bound`. Under unit-cost
atom equality, ordinary linear membership, and a bounded initial root list,
this gives a polynomial upper bound in the input list lengths. No claim
of worklist optimality, sparse incremental runtime, or bounded comparator
cost for arbitrary user atoms follows.

The following are medians of five executions per size on the same shared
x86-64 Intel Xeon Platinum 8573C, Lean 4.19.0 `--run`. Each input is a synthetic
chain of unary rules. The harness checks exact outputs against the universe,
warms both paths once, alternates execution order, and times evaluation of
the returned list. Compilation and startup are outside the timer.
The ratio divides the separate medians.

| Chain facts | Materialized scan | Exhaustive reference | Reference / scan |
|---:|---:|---:|---:|
| 6 | 0.075230 ms | 0.936258 ms | 12.45× |
| 10 | 0.240809 ms | 18.341130 ms | 76.16× |
| 14 | 0.411892 ms | 569.602279 ms | 1,382.89× |

The raw timings are in [benchmark.csv](benchmark.csv). Other workload shapes,
concurrent updates, peak memory, production latency and comparisons with
optimized external solvers are unmeasured.

## Remaining proof obligations

| Extension | Evidence needed for a stronger verdict |
|---|---|
| Complete search over a deployment's implementations | An enumeration or abstraction theorem covering every admissible implementation, plus validated costs for the named hardware, workload and release window. Existing finite schedule enumeration covers its specified model. |
| Calibrated reliability under correlated faults | A justified joint scenario model or a statistical sampling design. Paired scenarios preserve known dependence; marginals alone cannot identify it. |
| Hard real-time response and availability | A clock, resource bounds, scheduling or fairness premises, and a progress proof that rules out the stopped-machine example. |
| Distributed incremental operation and crash recovery | A concrete index, serialization and recovery protocol with refinement to the normalized ledger and full recomputation, including concurrent withdrawal. The scan here recomputes. |
| Evidence from deployed software | Independently grounded execution roster, trusted measurement and validation, binding to policy and subject, and validated translation from events to roots, rules and simulations. |
