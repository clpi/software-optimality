# Machine-checked qualification, compounding, and finite Pareto selection

Language-independent Lean proofs with executable reference algorithms. Checked with Lean 4.19.0 (release commit `6caaee842e94`). The cross-repository interface uses the pinned `software-is-quantifiable` Lake dependency; no Mathlib is required. These are not proofs of an unrelated production implementation.

## Historical execution and observation planning

Recover every forced answer to a declared set of historical questions, retain counterexamples for ambiguous answers, and compute the Pareto frontier of adaptive observations and certified proof engines. The Lean checker and SQLite recorder support archived receipts, sparse inference, independent predictions, symbolic hooks and withdrawals. The reproducible example starts with an unlisted run and follows its status through receipt recovery and retraction. [Procedure, proofs and replay](docs/HISTORICAL-OBSERVABILITY.md).

## Reproduce

Install the official Lean 4.19.0 distribution and place its `bin` directory on PATH, then:

```sh
./check.sh
./composition/check.sh
```

Or select a specific executable:

```sh
LEAN=/path/to/lean ./check.sh
LAKE=/path/to/lake LEAN=/path/to/lean ./composition/check.sh
```

The script rejects source admissions/custom axioms, treats Lean warnings as errors, checks each compiler exit, and rejects admitted-axiom/error diagnostics. It compiles local dependencies and checks all named modules. Exit status zero is required; full captured output is in `CHECK.log`. `CHECK_CONTROLS.md` records negative controls confirming a deliberately admitted proof and an injected compiler error both stop the checker. `lean-toolchain` pins the version. Generated `.olean` files need not be committed.

## Checked theorem inventory

**What a nondominance certificate means.** A result in this repository is nondominance inside a supplied finite candidate list under a supplied integer cost model: the candidate belongs to that list, and no member of the same list is componentwise no worse and strictly better on one of the supplied axes. It is not a claim that the candidate is optimal among implementations outside the list, or that the cost model is the only relevant one. `accepted_improvement_if_checkerSound` concludes behavior preservation only by applying the passed-through hypothesis `checkerSound`; the theorem does not prove that checker.

### `Qualification.lean`: general derivation semantics

Exact scoped support atoms and finite-premise inference/transfer rules define rooted derivations. The kernel proves leastness, monotonicity, idempotence, exact cross-input compounding, order independence of sound exhaustive saturations, semantic soundness conditional on valid roots/rules, withdrawal containment, preservation of any surviving derivation subsystem, and impossibility of unsupported cyclic bootstrap. Each printed theorem in this module has an empty axiom dependency list.

The compounding identity is `C(B ∪ D) = C(C(B) ∪ C(D))`, interpreted as pointwise membership equivalence. In particular it does not claim `C(B ∪ D) = C(B) ∪ C(D)`; new cross-source consequences are retained.

### `ExecutableClosure.lean`: executable saturation with exact refinement

`close` enumerates all sublists of a finite universe, retains those containing the roots and closed under all rules, and returns the intersection of those models. All executable functions terminate by structural recursion. `close_exact` proves:

```
a ∈ close U B rules ↔ Derives B rules a
```

The explicit assumptions are decidable equality of atoms, all roots in U, and every admitted rule head in U. Rule premises need not be bounded: an outside premise cannot acquire support because all roots and heads are bounded. The same file proves `2^|U|` enumerated subset candidates (with positional multiplicity if U contains duplicates), closure of the result, preservation of roots, invariance under reordered/duplicated equivalent roots and rules, and monotonicity under root/rule inclusion. Withdrawal is the reverse-inclusion case.

**Use `checkedClose` at runtime, not raw `close`.** `checkedClose` validates that every root and rule head belongs to the named universe and returns `none` when invalid. `checkedClose_admitted` proves every `some out` satisfies the bounds and has exactly the inductively derivable members. `checkedClose_rejects` proves rejection iff those bounds fail. Executable regression guards cover both out-of-universe roots and heads. Raw `close` is a mathematical implementation under explicit preconditions: outside them its model list can be empty and its intersection vacuously return the entire universe, so it must not be exposed as a fail-closed API.

This is a deliberately exponential reference algorithm, not an optimized worklist. Its purpose is a complete executable specification with a checked bridge to the general derivation semantics. No unproved iteration cap or saturation heuristic is used. Three executable guards cover cross-source consequences, withdrawn support, and an unsupported cycle.

### `ExecutableIncremental.lean`: executable edits with exact cache refinement

`start` evaluates a snapshot and `advance` updates its proof-carrying cache. Changed roots and changed hyperedge heads seed invalidation. The reference `dirty` projects old and new hypergraphs, while `update` materializes only the new-rule arcs. `new_arcs_suffice` proves that propagation equivalent, and `update_reference_exact` proves equality to the normalized old-and-new-arc reference. Both snapshots still supply the change seeds. Recalculation fires the original complete conjunctive rules. `update_exact` proves membership agrees with full rooted derivation when the input cache is exact, and `reachable_exact` establishes that premise for every state produced by the API. Exported `full` and `update` caches erase repeated facts; `reachable_nodup` proves uniqueness across every API history. `reachable_length_eq_full` fixes stored size to the current closure, and `advance_same_length` proves unchanged revisions preserve cache length. Raw imported caches require their own validation.

`composition/IncrementalSelection.lean` passes those facts through the existing canonical release and frontier owners. `evaluate_exact` preserves the complete optional ordered selection result across every finite edit history, and `certificate_eq_full` preserves the existing covered-frontier certificate verdict, including refusal and invalid input. The projection must reread changed observations, policy, catalogue, and cost data from the current snapshot. These are reference algorithms with sequential-state proofs; no distributed publication protocol or measured performance improvement is asserted. [Verification and counterexamples](composition/EXECUTABLE-VERIFICATION.md) give the exact scope and commands.

### `FiniteQualification.lean`: exact qualification enumeration

Executable enumeration of all Boolean profiles of dimension n, proved count `2^n`, complete membership iff length n, and exact filtering under the supplied total Boolean evaluator. Completeness is a membership theorem, not inferred merely from counting candidates.

### `FiniteFrontier.lean`: Pareto selection and coloring

Executable filtering returns exactly candidates not dominated by any candidate in the named list. The provided strict Pareto comparator is checked against componentwise no-worse integer costs and at least one strictly better axis. Costs and finite axes are inputs; an axis to maximize must be normalized accordingly. The four-way support coloring distinguishes unknown, lawful, unlawful, and conflict; exact conflict/unknown characterizations are checked.

The frontier theorem is nondominance inside the supplied finite candidate list and measurements, under the supplied integer costs. `ThreeValuedGate.FiniteSpace.nothingOutside` says every implementation of the candidate type is in that list. `ThreeValuedGate.FiniteSpace.noCoverageGaps` says every listed implementation has a reading on every contract axis. `frontier_no_dominator` uses both premises. `nothingOutside_counterexample` and `noCoverageGaps_counterexample` show that dropping either premise leaves a frontier member that the two-valued cost order accepts as dominated. `absent_axis_admitted_by_two_valued_dominance` shows `ComparisonContract.dominates` accepts a missing coordinate because `cost` fills it with `0`. `unknown_blocks_dominance` is the local three-valued refusal. `unknown_blocks_dominance_canonical` sends that missing reading through `toProfile`, which drops it from the canonical vector, and then `Interface.dominates` fails. For every contract and every pair of equal-length integer lists, `known_dominates_iff_bool` matches `ComparisonContract.dominates` and `known_gate_matches_bool` matches the Bool cost comparison at each axis. `known_agrees_canonical` is that statement for nonnegative readings against `Interface.dominates` on the contract's measure space. `contractMin_agrees_canonical` is the one-axis example, obtained through `CanonicalDominance.Comparison.local_dominates_iff_canonical`.

### `FiniteSchedules.lean`: test ordering and parallel schedules

`enumerate` lists every assignment of one venue and one nonnegative integer start tick to each of the named jobs, up to the specified start horizon. Its completeness is proved by exact membership, not by assuming a generator sampled everything. `feasible` verifies list size, placement bounds, nonoverlap for each pair of jobs on the same capacity-one venue, and every listed dependency including endpoint bounds. `feasibleSchedules_exact` proves filtering returns exactly all schedules meeting this model. Durations are nonnegative integer inputs; the horizon bounds **start times**, not completion times. Venues are homogeneous in this model; shared/external resources need additional constraints. The pairwise ordering predicate treats zero-duration jobs literally and does not model every empty-interval convention; zero-duration dependency cycles can satisfy its non-strict precedence inequalities. Positive durations and acyclic dependencies should be enforced separately when required by a deployment.

`nondominatedInEnumeratedSchedulesUnderSuppliedIntegerCost` proves an accepted certificate designates a feasible schedule with no strict Pareto dominator among **all schedules of this enumerated model**, on the named axes and the supplied total integer cost function. `nondominatedInSuppliedFiniteList` is the same check for any supplied finite candidate list. Completeness of an externally generated candidate list must be established separately.

`queueFeasible_exact` supports external test runners with one ordered queue per venue: every numbered job occurs exactly once, there are no extra job ids, and the queue count matches the venue count. It does not assert arbitrary queue ordering preserves side effects. `accepted_improvement_if_checkerSound` proves feasibility and strict Pareto improvement on the supplied integer costs. Its behavior-preservation conjunct is exactly the passed-through hypothesis `checkerSound` applied to the certificate's Boolean; lower measured times do not discharge that hypothesis.

These theorems apply to schedules of foreign software tests without lowering their programs into an IR. They do not prove the foreign tests' semantic independence, their completeness as program specifications, or the empirical durations' future stability. Physical benchmark measurements and external queue enumeration remain separately qualified evidence.

### `ForeignCampaign.lean`: concrete foreign test-campaign certificate

Input durations (nanoseconds): click `1033599117`, attrs `687668287`, tomli `293138741`, packaging `6991879848`. The source campaign JSON SHA-256 is recorded in the module. The 120 supplied ordered two-worker queue candidates and expected metric rows are materialized as Lean data. The kernel checks there are 120 distinct candidates, each includes every job exactly once on two queues, and each supplied metric matches a fresh model calculation from the duration constants.

The modeled axes are makespan (maximum per-queue duration sum) and sum of all jobs' completion times. The chosen queues `[[packaging], [tomli, attrs, click]]` have costs `[6991879848, 10280231762]`, versus baseline `[[click, attrs, tomli, packaging], []]` costs `[9006285993, 13775558659]`. The kernel proves strict Pareto improvement over that baseline, nondomination of the chosen candidate, and exact equality of the computed frontier to the four supplied frontier schedules (including worker swaps).

The concrete calculation proofs use `by decide`, checked by Lean's kernel, not `native_decide`. This proves arithmetic, feasibility and ranking **for the imported candidate list and cost model**. The generic start-tick enumeration theorem does not establish completeness of the separate queue-list generator. Physical runs, timing medians, process isolation, and semantic equivalence of foreign test suites are independently collected observations, not consequences of the Lean ranking proof. In particular the measured parallel wall-clock percentage must not be described as a proven future speedup.

### `EligibleSchedules.lean`: hard observed admission before optimization

Tests and intent choose the comparison axes and the admission policy. Eligibility is separate from cost ranking: the executable gate requires feasibility, the provided observed-behavior predicate, and all required timing checks. `timedAdmission_exact` proves the required count is positive, exactly that many receipts exist, and every elapsed value is present and no greater than its declared per-receipt limit. A missing timing, empty zero-round campaign, or even one over-limit result is rejected. Equality at the limit is accepted; no hidden tolerance is applied.

`admittedNondominatedUnderSuppliedIntegerCost_exact` proves both admission of the selected candidate and absence of an admitted dominator on the supplied integer cost axes, inside the supplied finite list. `rejected_not_nondominated_under_supplied_integer_cost` prevents a lower cost from overriding a failed gate. `dominator_refutes_certificate` supplies the constructive counterexample check: an admitted strict dominator invalidates the claimed nondominance certificate.

Timing inputs can represent fixed ceilings or paired observed-baseline ceilings; the choice must be named by the policy. The theorem checks the recorded cases and does not predict unseen runs. A paired-baseline experiment is not presented as a user-authored absolute SLA. The observed-behavior Boolean is a policy input; validation of its underlying receipt contents is separate from treating it as evidence of universal behavior preservation.

### `EligibleCampaign.lean`: measured pilot and tested alternate

The concrete pilot has three plans: O1 original tests on one worker, O2 original tests on two workers, R2 reverse-collected tests on the same two-worker plan. Worker capacity is a constraint, not a quality axis. The sole objective is maximum observed wall-clock nanoseconds across three paired rounds. All three plans' imported per-job receipt flags report identical collected ids and phase/outcome/skip records plus successful exits; these Boolean receipt comparisons are inputs whose underlying raw files are audited separately.

Each round's hard cap is that round's observed O1 wall time: `[10769189848,7296152413,7966428370]`. O2 observations are `[5429128102,6128442901,6240471073]`; R2 observations are `[9146680841,6480720115,6777395883]`. The kernel checks receipt counts, behavioral flag conjunctions, every cap inequality, and exact gate admission. All three pass; **none of these observed candidates is gate-rejected**.

The kernel proves O2 is the singleton frontier of this admitted three-plan catalogue. Its maximum observed time is `6240471073 ns`, versus O1 `10769189848 ns` and R2 `9146680841 ns`. R2 is the actually executed alternate: admitted, but dominated, with O2 faster in every recorded paired round. That comparison is not a proof of physical causality or a forecast. A separate clearly named **synthetic** negative control exceeds one cap by one nanosecond and is proved rejected.

The source qualification JSON and policy hashes appear in the module. The hard gate was specified before the runs; the objective was corrected during the run before analysis to wall time only, preserving the earlier policy revision in the empirical artifacts. Do not describe the corrected objective as preregistered before all execution, or the paired-baseline caps as an absolute SLA provided by the user.

### `ScopedEvidence.lean`: identified evidence and policy-bound scope

The improved checker addresses a gap in the generic timing-list interface: duplicated or mis-scoped receipts must not count as independent observations. A scope key explicitly includes artifact, configuration, lineage, venue, harness, intent, policy and metric identity. Each required obligation names its scope, round and **policy-supplied** limit. Receipts carry their own unique ID, scope, round, observed-pass flag and optional measured elapsed time; they cannot choose their own cap.

`qualify_exact` proves the acceptance contract: nonempty requirement set; unique scope/round requirement keys; every required scope tied to the named policy; equal requirement/evidence counts; unique receipt IDs; and exactly one matching receipt for every requirement. `qualification_witnesses` exposes an actual matching receipt and its measured bound for each obligation. Wrong-scope receipt sets and conflicting matching duplicates are proved rejected. Synthetic executable controls cover missing receipt, duplicate round, repeated ID, wrong metric, wrong policy, and one-unit over-limit evidence.

These are opaque canonical identifiers: equality checking is proved, but cryptographic authenticity, parser correctness, whether a supplied policy ID really commits to its bytes, and observation instrumentation remain separate obligations. The suite-elapsed metric scope must not be transferred to per-job elapsed: the recorded pilot contains individual subprocess slowdowns even though the admitted suite elapsed improves. Cross-lineage reuse requires an explicit independently checked transfer; this checker never infers it from shared content alone. `qualification_sound_relative` makes semantic interpretation an explicit validation premise rather than assuming observed-pass means universal correctness.

### `LinearSelection.lean`: efficient scalar optimum, not all-pairs search

For the pilot's **single** declared wall-time objective, an eligible-list argmin replaces all-pairs dominance checking. The kernel proves its returned item is an admitted candidate with cost no greater than every admitted candidate. An instrumented version of the actual recursion is proved to return the same winner and perform exactly one comparison per tail element: n−1 comparisons on a nonempty n-candidate input. This count excludes gate evaluation, cost computation and data loading; it is not a physical runtime benchmark.

The internal one-winner helper retains the earlier candidate on equal costs and therefore is not identity-order-invariant. The public set-valued `allMinima` instead returns **all** tied scalar minima. `allMinima_exact` proves exact membership and `allMinima_order_independent` proves that membership is unchanged under any reordered/duplicated equivalent input catalogue. Output list serialization is not claimed identical; canonical serialization is a separate concern. The tie-preserving method adds a linear filter/equality pass after the n−1-comparison minimum pass. It is a scalar optimum set, not a general multi-axis Pareto frontier. `EligibleCampaign.linear_selector_agrees` also checks the internal helper agrees on the recorded pilot, which has a unique optimum.

### `ScopedSelection.lean` and `ScopedCampaign.lean`: the integration bridge

The final selection entry point **directly** uses `ScopedEvidence.qualify` as its gate; an unbound observed-pass Boolean cannot bypass scoped evidence validation. `certified_scoped_nondominated_under_supplied_integer_cost` connects an accepted certificate to actual witnesses for every selected candidate obligation and to absence of any qualified dominator inside that supplied list under the supplied integer costs. `selected_all_exact` and `selected_all_order_independent` connect the efficient all-ties scalar selection to qualification and prove membership invariant under equivalent catalogue order.

The concrete `ScopedCampaign` constructs identified, round-keyed obligations/receipts from the recorded three-plan pilot, including capacity and exact per-round job flags. Its policy ID is the imported policy digest represented as a natural number; the other scope IDs identify the pinned campaign fixture. The kernel checks all scoped admissions, O2's optimum certificate, singleton `selectAll` output, reordered-catalogue agreement, and witness extraction for every O2 requirement. Reused rounds and receipts from R2 presented against O2's configuration are concretely proved rejected.

The generic selector receives per-candidate policies and a numeric cost function; it does not itself prove those candidates share the same intent/metric/comparison contract. Ingestion must restrict a comparison catalogue to compatible policies and units. The concrete pilot does so by its single documented wall-time policy. `ScopedFrontier.lean` below derives its policy from a complete contract and named subject, and derives costs from the resulting qualified receipts.

This is a selected-evidence checker, not the raw append-only transport layer. Identical duplicate delivery must be deduplicated by receipt identity before constructing its selected evidence set. Policy digest authenticity, digest-to-content binding and current authorization/liveness still require trusted or separately checked ingestion. For example, changing a cap while reusing the same opaque policy identifier is not detected solely by identifier equality; the ingestion bridge must validate the committed policy bytes. No cryptographic correctness or live-policy lookup theorem is claimed here.

### `MetricRelevance.lean`: exact nonaggregated relevance profiles

A profile retains separate per-intent-part coordinates for direct contrast, composed-result change, admissible indirect mutation sensitivity, and observed outcome variability. `buildProfile` assembles these coordinates without inventing weights or a scalar quality score. Model-pair catalogues are deduplicated and filtered by an explicit per-part admissibility predicate **before** computing denominators.

`direct_exact` identifies single-metric contrasts in the supplied deterministic model: only that metric may change among the named metric coordinates, and the chosen intent part changes. `composition_irreducible` checks a multi-metric group changes the selected part while no proper subgroup has a changing alternative among the named states. Both are claims about the named model/functions, not proofs that every relevant real-world variable has been modeled or that hidden physical causes are absent.

`indirectRate_spec` restricts the denominator to admitted mutation records in the requested comparison scope and matched context, with unique comparison identities; confounded/unadmitted rows do not dilute the denominator, other scopes do not leak into it, and duplicate identities reject. Context matching is recorded comparison attribution, not proof that all physical nuisance variables were controlled.

Fractions are exact unreduced natural numerator/positive-denominator pairs, not floating estimates. `exactRate_spec` proves their exact counts, positive denominator and numerator bound. Empty evidence returns `none`, not zero. Rational equality uses cross multiplication and rejects zero denominators. Scoped failure counts are proved permutation invariant. Observed failure/disagreement rates and mixed-outcome labels reject duplicate observation identities; mixed labels are `none` for absent/conflicting evidence. Observation IDs identify repeats, whereas deduplicated model pairs identify model edges, not additional independent trials.

All new examples are **synthetic**, distinct from the foreign-code campaign. For intent `(latency ≤ 10 AND correct) OR fallback`, four named contexts yield direct latency-clause change `4/4` for 8→12, but composed-root pivotality `1/4`. A shared-dependency fixture `(m AND a) OR (m AND b) = m AND (a OR b)` is proved exactly, and changing m changes the root in `3/4` of the four named contexts, without double-counting its two syntax occurrences. Counting each named context once is the fixture sampling measure, not an imposed user preference weight. A separately named admitted mutation catalogue yields `1/2`; five same-scope observations yield failure `2/5` and unordered-pair disagreement `6/10`. These retain their different denominators and attribution types. They are not population probabilities, weighted utility or a causal-effect estimate. The exact profile and every fixture result are kernel-checked. No generic permutation theorem for pair-disagreement enumeration, normalization theorem for reduced rationals, or general statistical uncertainty theorem is claimed.

## Trust and precise boundary

No `sorry`, admissions, custom axioms, or `native_decide` shortcuts occur. Some finite-reference proofs use standard Lean foundational axioms `propext`, `Classical.choice`, and `Quot.sound` through library lemmas, as disclosed by `#print axioms` in `CHECK.log`. Classical reasoning is used in proofs, not to implement the executable algorithms.

Policies, scopes, lineages, opposite polarities and evidence identities can be encoded in atoms. Their validation is an explicit input obligation, not supplied by set closure. Runtime receipts are not automatically universal semantic proofs. Old evidence does not itself qualify a changed release; a current support or valid transfer derivation is required. Withdrawal filters live roots/rules and recomputes, preserving historical events; the current projection is not monotone when withdrawals occur.

Not proved here: runtime instrumentation fidelity, cryptographic hash binding, external policy authorization, complete language lowering, arbitrary test termination, universal behavior preservation, numerical confidence of measurements, efficient worklist refinement or tight complexity bounds, an incremental provenance/deletion implementation, incremental release monotonicity, or globally optimal software performance. `ImportBinding` and `GeneratorCoverage` are named premises, not theorems of those obligations. These are distinct obligations, not concealed assumptions of the proved closure/qualification results.

## Provenance

Official checker archive: https://github.com/leanprover/lean4/releases/download/v4.19.0/lean-4.19.0-linux.tar.zst

Checked executable SHA-256:
`92c3d35b5bfaa5e0fea413a775d504cf46cd95e1345df61c2274f76779e7e023`

See `SHA256SUMS` for source/check-output hashes.

## Publication scope clarification
The pilot timing gate is whole-suite wall time only: 8 of 12 O2 subprocess times were slower than paired O1 times. Three paired rounds and recorded inputs do not establish future or per-test no-regression. R2 was admitted but dominated, not rejected. Policy revision chronology has no signed precommit or independently authenticated timestamp. Scoped checker IDs and reported pass bits do not establish external receipt authenticity, policy authorization, liveness, or raw-ingestion fidelity. `allMinima` is permutation invariant in membership, not serialized list order or multiplicity. See docs/PROOF-DESIGN.md and evidence/ for exact scope.

### Hypergraph-derived incremental qualification and interaction views

`HypergraphIncremental.lean` adds a single authoritative directed hypergraph, derived dependency/incidence/interaction views, exact semantic incremental recomputation under root and topology changes, and agreement with the existing executable exhaustive closure. Joint premises remain conjunctive. Old and new topology both participate in invalidation; unsupported cycles cannot bootstrap after withdrawal.

Typed matrix cells count supporting live records by edge kind and both port roles/positions. Retained-plus-added counts and Boolean cells equal complete regeneration; alternate receipt support survives individual withdrawal. Deterministic qualification/profile projection preserves the full frontier result, including resurrection after withdrawal of a dominator.

This is a semantic refinement theorem, **not a fast executable worklist or sparse-matrix performance proof**. The raw record list counts multiplicity. Unique receipt identity, deduplication, scoped admission and withdrawal precedence must be enforced before the live snapshot is supplied. The same-ID remove-and-add operation permits reintroduction; it is not a permanent tombstone protocol. See [the exact scope](HYPERGRAPH_SCOPE.md) and [independent publication checks](docs/hypergraph-incremental/VERIFICATION.md).

### `OptimalityInterface.lean`: stable closure and Pareto-maximal interface

Downstream proofs import `OptimalityInterface` and use the `Optimality` namespace. `Composition.lean` holds the generic proofs; one import loads both. The closure operator is `Optimality.closure`, the least rooted derivation. It corresponds to `SoftwareIsQuantifiable.Coloring.Deriv`; `hornDeriv_iff_closure` is that equivalence, and `closure_operator_exact` is the snapshot computation corresponding to `SoftwareIsQuantifiable.Coloring.coloring` when every rule head lies in the named universe. `paretoMaximal` is the two-axis `Nat × Nat` frontier corresponding to `SoftwareIsQuantifiable.Pareto.dominates`. `noWorse` and `guardedMaximal` correspond to `Pareto.noWorse` and `admitted`. `GeneratorCoverage` is not `Coverage.PlatformPremise`; platform mediation is not assumed. `Fold.join` is root-set union before rules fire; `closure_compound` keeps cross-source consequences and is not that join.

| Claim | Lean form | Status |
|---|---|---|
| Closure is extensive, least, monotone, and idempotent | `closure_extensive`, `closure_least`, `closure_monotone`, `closure_idempotent` | PROVEN |
| Two sources and any finite family compound, keeping cross-source consequences | `closure_compound`, `closure_compound_finite` | PROVEN |
| Naive union of closures misses a cross-source consequence | `union_misses_cross_consequence` | DISPROVEN |
| Separated component closure factors through `sumRules`; a cross-summand rule does not | `closure_factors_left`, `closure_factors_right`, `separated_closure_conjoins`; `factorization_needs_separation` | PROVEN; separation is the `sumRules` premise. Unrestricted factoring is DISPROVEN |
| Reclosing under a richer rule set | `reclose_under_embedded_rules` | PROVEN under the named `embed` premise |
| Horn derivability agrees with closure; the executable close computes it inside the snapshot | `hornDeriv_iff_closure`, `closure_operator_exact` | PROVEN. The universe bound is the snapshot premise |
| Withdrawal adds no support; a live subsystem survives; empty-premise-free cycles do not bootstrap | `withdrawal_no_new_support`, `surviving_subsystem`, `no_bootstrap` | PROVEN |
| Two-axis maximal set matches strict Pareto, is nonempty, and excludes dominated outputs | `dominates_iff_strictPareto`, `paretoMaximal_exact`, `paretoMaximal_nonempty`, `paretoMaximal_not_dominated` | PROVEN |
| A maximal point can worsen an axis | `paretoMaximal_can_regress` | DISPROVEN as a release gate |
| Guarded maximal set is componentwise no worse and undominated | `guardedMaximal_sound`, `guardedMaximal_nonempty` | PROVEN |
| Overlapping bounds are not per-execution dominance | `not_per_execution_dominance` | DISPROVEN |
| Behavior retention and the release gate | `SoftwareIsQuantifiable.Pareto.noQualifiedBehaviorLost_iff`, `SoftwareIsQuantifiable.Pareto.acceptsRelease_iff` | PROVEN in `software-is-quantifiable` at `430340295c52a015772022b2b663d01120a3a747`. This repository does not restate them |
| Excluded candidates are dominated by a frontier member; a pruning certificate is sound | `frontier_covers`, `pruning_sound`, `pruning_sound_pareto`, `pruningOK_implies` | PROVEN. Arbitrary dominance needs the named transitivity premise; strict Pareto discharges it |
| Componentwise-sum product: joint frontier members are locally nondominated, and checking the product of local frontiers is sound | `joint_frontier_in_local_frontiers`, `reduced_product_sound`, `scalar_frontier_iff_allMinima` | PROVEN for componentwise sum. One-axis linear selection and the Pareto filter agree |
| Product of local frontiers is not automatically jointly nondominated | `product_of_frontiers_not_joint` | DISPROVEN |
| Strict local dominance need not lift through an aggregation that drops an axis | `strict_lift_needs_premise`; `reducedAllowed` refuses `projectFirst` | DISPROVEN without the strict-lift premise |
| A complexity-class tag is not generator coverage | `class_tag_is_not_coverage`, `coverage_omission_can_dominate`, `frontier_respects_coverage` | The tag claim is DISPROVEN. Transfer to an intended set is PROVEN only from the named `GeneratorCoverage` premise |
| Import identity transfers a frontier; a changed cost row does not | `frontier_transfers_under_import`, `import_mismatch_blocks_transfer` | Transfer is PROVEN from the named `ImportBinding` premise. Mismatch is DISPROVEN. Cryptographic binding is not proved |
| Canonical key sort preserves frontier membership | `canonical_frontier_mem` | PROVEN for membership. Equal keys do not determine a unique order |
| Two-valued dominance admits an absent axis | `ThreeValuedGate.absent_axis_admitted_by_two_valued_dominance` | DISPROVEN. `ComparisonContract.cost` fills a missing coordinate with `0` |
| An unknown verdict blocks local dominance | `ThreeValuedGate.unknown_blocks_dominance` | PROVEN |
| An unknown verdict blocks canonical dominance | `ThreeValuedGate.unknown_blocks_dominance_canonical` | PROVEN. `toProfile` drops the missing reading, so the profile does not cover `measureSpace` |
| Equal-length known lists match the Bool dominance | `ThreeValuedGate.known_dominates_iff_bool` | PROVEN for every contract |
| A known per-axis gate matches the Bool cost comparison | `ThreeValuedGate.known_gate_matches_bool` | PROVEN at every axis of every equal-length contract. `contractMin_gate_matches_bool` is the one-axis example |
| Nonnegative known readings match `Interface.dominates` | `ThreeValuedGate.known_agrees_canonical` | PROVEN for every contract. `contractMin_agrees_canonical` is the one-axis example through `CanonicalDominance.Comparison.local_dominates_iff_canonical` |
| Nothing outside the finite supplied list | `ThreeValuedGate.FiniteSpace.nothingOutside` | PREMISE of `frontier_no_dominator`. Dropping it is DISPROVEN by `nothingOutside_counterexample` |
| Listed candidates have a reading on every axis | `ThreeValuedGate.FiniteSpace.noCoverageGaps` | PREMISE of `frontier_no_dominator`. Dropping it is DISPROVEN by `noCoverageGaps_counterexample` |
| A frontier member is undominated by every implementation | `ThreeValuedGate.frontier_no_dominator` | PROVEN from both premises above |

`tools/check_optimality.sh` runs `CompositionCheck.lean` and `tools/check_optimality.py` on the same guards. Both must report acceptance of a no-worse release and refusal of a regressing frontier point, an out-of-universe root, and a project-first product reduction. This is not a proof of incremental release monotonicity.

Third-party scan checks are not a Lean build. The Lean build is `lake build` with warnings as errors, and `./check.sh`; their logs are `LAKE-BUILD.log` and `CHECK.log`.

### Contextual compositional dominance

`ContextualDominance.lean` proves reflexive/transitive context-wide replacement and a sufficient local-to-contextual rule requiring **both** feasibility preservation and monotone cost composition. Representative pruning preserves all attainable componentwise bounds and exactly the Pareto objective vectors when every feasible original candidate has a feasible retained no-worse representative. It need not retain every tied candidate identity.

Kernel-checked synthetic counterexamples show local speedup reversing under contention, a smaller local cost violating contextual feasibility, and strict local speedup becoming a global tie under parallel max composition. The theorem does not infer contextual obligations from hashes or isolated timings, synthesize coverage witnesses, or prove actual runtime improvements. See [scope](docs/contextual-dominance/SCOPE.md) and [checks](docs/contextual-dominance/VERIFICATION.md).

### Live-support admission and scoped hypergraph bridge

`Admission.lean` adds an executable derived live-support view: exact scoped keys, authorization-filtered events, duplicate-free support membership, conflicting-payload quarantine and withdrawal precedence. Replay and merge order preserve membership; a withdrawn key cannot resurrect, while a fresh support identity can be admitted. Raw events must be merged before normalization: unioning separately normalized live views can retain stale support.

`AdmissionHypergraph.lean` derives both roots and transfer/inference edges from those same live supports. Equal admitted provenance implies equal qualification closure. The scoped constructor retains the full key/payload in roots; qualification cannot enter an otherwise unsupported lineage without an admitted entering edge.

This supplies a checked reference normalization stage for the earlier hypergraph boundary, not a cryptographic/authorization service. Authorizer truth, immutable key binding, semantic transfer validity and decoder correctness remain obligations. Output membership, not list byte ordering, is canonical. See [scope](docs/admission-normalization/SCOPE.md) and [checks](docs/admission-normalization/VERIFICATION.md).

### Typed comparison contracts and composable transport

`ComparisonContract.lean` rejects numerical comparisons with mismatched metric/unit/direction/aggregation, workload, venue, epoch or ordered axes, and rejects malformed value-vector shapes. Compatible comparisons return exact strict Pareto dominance, with maximize axes normalized by integer negation. Incomparable (`none`) and compatible-but-nondominating (`some false`) remain distinct.

Proof-carrying transports preserve a fixed application meaning and compose into a shared target contract. `compareVia_semantic` transfers target numerical dominance to the application better-than relation only with its explicit `metricSound` theorem. Neither interpretation nor soundness may be invented by an untrusted certificate author. Synthetic unit-conversion and tradeoff controls are included. See [scope](docs/typed-comparison/SCOPE.md) and [verification](docs/typed-comparison/VERIFICATION.md).

### `ScopedFrontier.lean`: compatible contracts and evidence-derived objective coordinates

The selection adapter requires one shared immutable comparison contract: instance/alternative-space scope, intent, qualification policy, preservation contract, fixed venue/harness, metric IDs/units, every required obligation/round/exact limit, and ordered objective axes with directions. Subjects are named independently by the candidate catalogue (artifact, configuration, lineage). The expected policy is derived solely from that contract and subject; submitted input carries no separately editable policy. Hard qualification metrics may be outside the objective list. `admitted_obligation_witness` proves that all contract obligations have their exact scoped successful bounded receipts through the existing `ScopedEvidence.qualify` checker.

Each objective resolves one policy obligation and its exact matching qualified receipt; the measured value supplies that coordinate. Missing or ambiguous coordinates reject. There is no independent numeric vector or truncating zip. Maximized coordinates are negated once for the existing minimizing Pareto comparator. `admitted_cost_witness` proves every compared axis normalizes an actual scoped, observed-pass, bounded receipt value: the total accessor's fallback cannot stand in for missing admitted evidence.

Direction normalization is shared with the existing `ComparisonContract` owner. For an explicitly supplied typed contract with aligned metric IDs, units, directions, axis count and venue, `typedObservation` builds a shape-valid numeric observation from admitted receipts; the typed cost, dominance and direct-comparison results are proved equal to their scoped counterparts. Its admission proof qualifies the scoped contract, not arbitrary additional workload/epoch/aggregation labels in the supplied typed contract. Their semantic applicability remains a separate premise; intent/scope/round are not silently substituted for them. This adapter grants no automatic transport or cross-context qualification.

`selected_exact` characterizes the complete admitted catalogue frontier. A qualified strict dominator excludes a candidate; tied vectors retain every admitted candidate identity. Membership is invariant under equivalent reordered/duplicated catalogues; serialization and multiplicity remain list-dependent. `noRegression` separately checks every axis against a named qualified incumbent: a faster, larger nondominated candidate can still fail this replacement condition. The complete deterministic selection adapter has the same output when projected from incremental or full hypergraph qualification.

The same adapter also composes with the existing `AdmissionHypergraph`: equal admitted provenance gives the same selected catalogue under a deterministic qualification-to-input projection. Duplicate raw event replay and branch merge order therefore preserve selection. This reuses the live-support normalization and single hypergraph authority; decoder validity and interpretation of measurement receipts remain explicit premises.

Synthetic controls cover declared ms/ns mismatch, missing objective/non-objective receipts, omitted hard requirements, raised caps, changed venue/harness/lineage/intent/policy, foreign/mixed subjects, duplicate receipts, failed capability evidence, maximizing direction, empty/duplicate axes, ties, reorder, and a runtime/space tradeoff. Full contract contents and caps are checked, rather than trusting a candidate's unchanged policy ID. Unit and preservation IDs still require authenticated schema/content binding and validated semantics. The legacy `Receipt.elapsed` field supplies nonnegative measured quantities under an explicit metric schema; elapsed observations do not become memory/capability observations by relabeling them. See [the exact adapter scope](docs/SCOPED-FRONTIER.md).

The existing `FiniteFrontier.lean` owner also now checks retained-frontier certificates: every retained member is nondominated in the full named catalogue, and every omitted member has a retained strict dominator. `certified_frontier` proves exact frontier membership; `certified_coverage` supplies a no-worse retained representative for every catalogue point. `ScopedFrontier.certify` supplies the qualified consumer: it checks against the same admitted catalogue and measured cost contract, proves exact membership agreement with scoped selection, and exposes each retained point's hard-obligation witnesses. Unqualified retained points and omitted tied identities refuse. General contextual composition remains owned by `ContextualDominance.lean`, with feasibility preservation and objective monotonicity stated separately.

### Cross-repository qualification and compositional Pareto proofs

`lake build` has one dependency, `software-is-quantifiable` at
`430340295c52a015772022b2b663d01120a3a747`. The quantifiable package's
lakefile lists no dependency. The composition modules are roots of the
default target. The joint build connects admitted ledger
events, a bounded materialized closure scan, scoped release eligibility,
tie-preserving Pareto selection, interval and paired-scenario dominance, and
forward simulation of finite traces. The pruning checker accepts exactly
frontier-preserving subsets of a finite catalogue under a strict partial
order. See [the proof map, controls, measurements and limits](composition/README.md).

`SoftwareIsQuantifiable.Interface.dominates` and `Interface.noWorse`, at
`430340295c52a015772022b2b663d01120a3a747`, are the canonical profile order.
A reading vector that is shorter or longer than the measure space is not
`axesLe`. `Interface.releaseLe` and `Interface.releaseDominates` are that
order on symbol assemblies: each symbol occurs at most once, counting a
repeated copy, and every profile has one reading per axis.
`CanonicalDominance.lean` proves each local dominance predicate either
equivalent to the profile order on an explicit encoding, or a one-way
refinement together with a counterexample to the converse.
`Pareto.dominates` and `Pareto.noWorse` agree with the canonical order on
two nonnegative minimize axes when both profiles record observed behavior.
A one-symbol release of those profiles agrees with the same order.

Lean files under `docs/` stay out of the build. They are the negative and
publisher controls: `docs/admission-normalization/ReviewControls.lean`,
`docs/admission-normalization/ScopeControls.lean`,
`docs/contextual-dominance/Controls.lean`,
`docs/hypergraph-incremental/ReviewControls.lean`,
`docs/metric-relevance/BoundaryChecks.lean`,
`docs/typed-comparison/ReviewControls.lean`,
`docs/covered-frontier/Controls.lean`,
`docs/covered-frontier/Campaign.lean`, and
`docs/covered-frontier/ArchiveImport.lean`.

### `GeneralPareto.lean`: the general Pareto obligations, discharged

The general Pareto definition (named finite sets of assignments, workloads, venues; each execution carries a cost vector; a named aggregation per axis reduces a workload's executions under one assignment to one value; interval bounds are derived per assignment and axis; dominance is decided on bounds with three outcomes) carried two open proof obligations. This module discharges both, for integer costs.

Obligation 1 — bounds-derivation soundness: the derived interval for an assignment and axis is the minimum and maximum of the per-workload aggregated values; `bounds_sound` proves every collected value lies inside it, and `bounds_attained` proves each end of a nonempty interval is the aggregated value of a named workload (the discharge condition). `execution_le_bhi` extends the upper side to individual executions under the worst-case aggregation. Obligation 2 — aggregation well-definedness: `aggMax_perm`, `aggMin_perm`, and `aggSum_perm` prove the maximum, minimum, and sum aggregations are independent of the execution list's order, and the maximum/minimum characterizations prove each is a total function into `Option`, returning `none` exactly on the empty list — the unwitnessed cell.

The three-outcome decision on bounds is also proved: separation of the candidate's interval below the incumbent's on every axis, strict on one, implies every realized candidate vector strictly Pareto-dominates every realized incumbent vector (`separatedN_sound`, `separatedN_strictPareto`); overlap on any axis proves neither direction separated (`not_separatedN_of_overlap`) — the undecided case. `frontier_complete` proves every member of a named candidate list is in its strict-Pareto frontier or is strictly dominated by a frontier member. Not claimed: anything outside the named finite lists, anything about physical measurements, or a verdict for a non-separated pair beyond the proved overlap case.

### `FiniteFrontier.lean`: frontier completeness and selection on the frontier

Two general results now live in the frontier owner, and the earlier local copies are corollaries of them.

Frontier completeness: for any comparison that is irreflexive and transitive on the named list (off-list behaviour is unconstrained), every listed candidate is on the frontier or is dominated by a frontier member (`frontier_complete_of_strict`). Hence the frontier of a nonempty list is nonempty (`frontier_nonempty_of_strict`), the frontier always certifies itself (`frontier_certifies_of_strict`), and under strict Pareto dominance, which is proved irreflexive and transitive here, every listed point has a no-worse frontier representative with no certificate premise (`pareto_frontier_complete`, `pareto_frontier_nonempty`, `pareto_frontier_certifies`, `frontier_coverage`). `FrontierComposition.frontier_covers`, `Optimality.frontier_covers`, `GeneralPareto.frontier_complete` and `Optimality.paretoMaximal_nonempty` are now one-line corollaries.

Nonemptiness alone needs only a ranking, a score strictly decreasing along the comparison on the list, with no transitivity (`frontier_nonempty_of_ranked`).

Selection on the frontier: a point scoring no worse than each of its listed dominators, under an integer score strictly better on each of them, is on the frontier (`minimizer_on_frontier`). In this general form the statement is thin (its converse is immediate); the content is in the strict scores: an axis for the frontier over that single axis (`axis_strict`), and a positively weighted sum for the frontier over the supplied axes (`weighted_strict`). `ScopedSelection.selected_all_certified` and `selected_certified` give the qualified form: a scoped scalar selection carries a valid nondominance certificate, and `ScopedCampaign.scoped_nondominated_from_selection` derives the campaign's O2 certificate from its selection this way.

`FrontierObligationsControls.lean`, written by an independent reviewing agent that tried to break these statements, keeps the counterexamples in the gate: dropping irreflexivity or transitivity, an empty list, a constant score, a zero weight, a single-axis minimizer against a two-axis frontier, the converse of selection (a nonsupported frontier point minimizes no positively weighted sum), and truncating integer costs to naturals each break the corresponding statement. Not claimed: anything about candidates outside the named list, or that the supplied comparison means anything physical.

### `WorklistClosure.lean`: a verified worklist saturation

`ExecutableClosure.lean`'s reference saturation enumerates the powerset of the universe (2^|U| candidate subsets), by design. `WorklistClosure.lean` proves a worklist iteration computes the same closure: one step adds exactly the rule heads whose premises are all already present (`wstep_mem`); the iteration is a membership fixed point after at most |U| + 1 steps, by a counting argument (while unfixed, the count of universe members grows by at least one per step and is bounded by |U|); membership at any stage derives in `Qualification.Derives` (`witer_sound`) and every derivation lands in the fixed stage (`witer_complete`). The fail-closed checked worklist therefore returns exactly what the checked reference returns (`worklist_agrees_checked`), so the exponential reference remains usable as a small-case differential oracle. Not claimed: any complexity bound for the worklist itself (the count bounds iterations, not step cost), duplicate-freeness, or anything about inputs the checked boundary rejects.

### `StrictSchedules.lean`: positive durations and acyclicity inside the schedule model

`FiniteSchedules.lean` directs that positive durations and acyclic dependencies be enforced separately when required, and notes a zero-duration dependency cycle satisfies its feasibility predicate today. `StrictSchedules.lean` is that enforcement, carried inside the model: `feasibleStrict` conjoins feasibility with a decidable positivity check on every placed job, with exact characterizations of both (`positive_exact`, `feasibleStrict_iff`, `feasibleStrict_exact`). In a strictly feasible schedule every listed dependency is a strict precedence (`strict_precedence`), and acyclicity is then derived, not separately assumed: no strictly feasible schedule carries a dependency cycle (`no_dependency_cycle`). The zero-duration cycle stands in the guards as the control: feasible, not positive, not strictly feasible. Not claimed: anything about `feasible` alone, venues beyond the base model's homogeneous capacity, or shared and external resources, which the base model does not represent.
### `CheckedTransfer.lean`: checked cross-lineage transfer edges

The design's second proposed extension, proved against the derivation semantics. A transfer is a list of checked pairs, given as data in the same style as roots and rules; the transfer rules are exactly the pairs whose source is derivable in the source system, so an unchecked pair contributes nothing. The image of a target set under the checked pairs is exact (`image_exact`), monotone, and never exceeds the combined checked system: anything target-side reachable through checked transfers is derivable from the source roots under the source rules plus the checked transfer rules, so a transfer proves nothing the combined system does not (`transfer_never_exceeds`, resting on `Qualification.least`). Withdrawal is contained: withdrawing a source root retracts exactly the image part that loses support, and no transfer bootstraps a fact from nothing (`transfer_no_bootstrap`). The headline theorems are axiom-free. Not claimed: that any particular transfer is semantically justified — the pairs are checked data, and their justification is the same ingestion obligation as roots and rules.

### `EvidenceTransport.lean`: the dedupe transport bridge for scoped evidence

`ScopedEvidence.lean` names an ingestion duty: identical duplicate delivery must be deduplicated by receipt identity before its selected evidence set is constructed. This module proves that bridge in the module's own receipt types. Deduplication keeps the first delivery of each receipt identity; membership after dedupe is characterized honestly — a surviving receipt was delivered, and the first delivery of its identity survives — because conflicting duplicates (same identity, different contents) are not silently equated: the scoped qualifier already refuses them, and the bridge preserves that refusal. Dedupe is idempotent, is the identity on duplicate-free deliveries, produces duplicate-free identity lists, and the central bridge holds: qualifying the deduplicated delivery agrees exactly with qualifying the raw delivery (`qualify_dedupe_iff`), so the transport stage changes nothing the checker decides. Not claimed: anything about receipt authenticity or authorization, which stay named ingestion obligations.

### `LinkedCertificate.lean`: the principal linked certificate, and the generator coverage upgrade

The design's first proposed extension, proved for the eligible-schedules specialization, and its fifth (the coverage upgrade) for the one generator whose completeness is already proven. One acceptance predicate over a fixed instance yields the four clauses together (`principal`): the admission components of the eligible gate (observed-behavior bit, positive required count, exact receipt count, every elapsed value within its named limit); the scope statement — the timed-admission characterization instantiated at the instance, so the checker validated precisely the named receipt list against the named count and limits; feasibility in the finite schedule model; and membership in the declared alternative space with no gated candidate in it strictly dominating. Each clause is discharged by the earlier theorem that earned it; nothing is reproven. The boundary is stated in the module and stands: the observed-behavior predicate is a policy input, so the scope clause proven is exactness of the checked receipt list, not behavior preservation for unobserved cases. `generator_optimum` upgrades a certificate over the enumerated schedule catalogue to the absence of a dominator among all schedules of the model's shape, enumerated or not, through the enumeration's proven completeness. No upgrade is claimed for the foreign campaign's queue catalogue, whose exhaustiveness is not proven.

### `ScopedCompatibility.lean`: catalogue compatibility as a checked precondition

The generic selector in `ScopedSelection.lean` receives per-candidate policies and does not itself prove the candidates share one intent, metric, and policy contract; the readme has carried that restriction as an ingestion duty. This module makes it a checked precondition over the selector's own types: a catalogue is compatible when every candidate's derived policy agrees with the catalogue's reference policy on the full contract the representation carries (policy identity, intent, metric identity, and limits), the check is decidable and exact (`compatible_exact`), and over a compatible catalogue the certified optimum theorem holds in its original strength (`certified_scoped_optimum_compatible`). A mixed catalogue is refused by the check, with a two-candidate counterexample standing in the guards. The by-construction closure of the same point for the newer adapter lives in `ScopedFrontier.lean`, which derives the policy from one shared contract instead of checking submitted ones; this module closes it for the selector's existing entry point.
