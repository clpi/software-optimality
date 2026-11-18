# Machine-checked qualification, compounding, and finite Pareto selection

Language-independent Lean proofs with executable reference algorithms. Checked with Lean 4.19.0 (release commit `6caaee842e94`). No external packages or Mathlib. These are not proofs of an unrelated production implementation.

## Reproduce

Install the official Lean 4.19.0 distribution and place its `bin` directory on PATH, then:

```sh
./check.sh
```

Or select a specific executable:

```sh
LEAN=/path/to/lean ./check.sh
```

The script compiles `Qualification.olean` locally, then checks every file. Exit status zero is required; full captured output is in `CHECK.log`. `lean-toolchain` pins the version. Generated `.olean` files need not be committed.

## Checked theorem inventory

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

### `FiniteQualification.lean`: exact qualification enumeration

Executable enumeration of all Boolean profiles of dimension n, proved count `2^n`, complete membership iff length n, and exact filtering under the supplied total Boolean evaluator. Completeness is a membership theorem, not inferred merely from counting candidates.

### `FiniteFrontier.lean`: Pareto selection and coloring

Executable filtering returns exactly candidates not dominated by any candidate in the named list. The provided strict Pareto comparator is checked against componentwise no-worse integer costs and at least one strictly better axis. Costs and finite axes are inputs; an axis to maximize must be normalized accordingly. The four-way support coloring distinguishes unknown, lawful, unlawful, and conflict; exact conflict/unknown characterizations are checked.

The frontier theorem is relative to the supplied candidate universe and measurements. It does not assert that enumerated candidates include every possible implementation, or that the reference algorithm itself is Pareto optimal.

### `FiniteSchedules.lean`: test ordering and parallel schedules

`enumerate` lists every assignment of one venue and one nonnegative integer start tick to each of the named jobs, up to the specified start horizon. Its completeness is proved by exact membership, not by assuming a generator sampled everything. `feasible` verifies list size, placement bounds, nonoverlap for each pair of jobs on the same capacity-one venue, and every listed dependency including endpoint bounds. `feasibleSchedules_exact` proves filtering returns exactly all schedules meeting this model. Durations are nonnegative integer inputs; the horizon bounds **start times**, not completion times. Venues are homogeneous in this model; shared/external resources need additional constraints. The pairwise ordering predicate treats zero-duration jobs literally and does not model every empty-interval convention; zero-duration dependency cycles can satisfy its non-strict precedence inequalities. Positive durations and acyclic dependencies should be enforced separately when required by a deployment.

`certified_optimal` proves an accepted certificate designates a feasible schedule with no strict Pareto dominator among **all schedules of this enumerated model**, on the named axes and supplied total integer cost function. The generic `optimalCertificate` can also certify any supplied finite candidate list, but completeness of an externally generated candidate list must be established separately.

`queueFeasible_exact` supports external test runners with one ordered queue per venue: every numbered job occurs exactly once, there are no extra job ids, and the queue count matches the venue count. It does not assert arbitrary queue ordering preserves side effects. `accepted_improvement` proves feasibility and strict Pareto improvement plus behavioral preservation **when a supplied preservation certificate checker is sound**. This makes the separate preservation obligation explicit for test rewrites/reordering; lower measured times alone never discharge it.

These theorems apply to schedules of foreign software tests without lowering their programs into an IR. They do not prove the foreign tests' semantic independence, their completeness as program specifications, or the empirical durations' future stability. Physical benchmark measurements and external queue enumeration remain separately qualified evidence.

### `ForeignCampaign.lean`: concrete foreign test-campaign certificate

Input durations (nanoseconds): click `1033599117`, attrs `687668287`, tomli `293138741`, packaging `6991879848`. The source campaign JSON SHA-256 is recorded in the module. The 120 supplied ordered two-worker queue candidates and expected metric rows are materialized as Lean data. The kernel checks there are 120 distinct candidates, each includes every job exactly once on two queues, and each supplied metric matches a fresh model calculation from the duration constants.

The modeled axes are makespan (maximum per-queue duration sum) and sum of all jobs' completion times. The chosen queues `[[packaging], [tomli, attrs, click]]` have costs `[6991879848, 10280231762]`, versus baseline `[[click, attrs, tomli, packaging], []]` costs `[9006285993, 13775558659]`. The kernel proves strict Pareto improvement over that baseline, nondomination of the chosen candidate, and exact equality of the computed frontier to the four supplied frontier schedules (including worker swaps).

The concrete calculation proofs use `by decide`, checked by Lean's kernel, not `native_decide`. This proves arithmetic, feasibility and ranking **for the imported candidate list and cost model**. The generic start-tick enumeration theorem does not establish completeness of the separate queue-list generator. Physical runs, timing medians, process isolation, and semantic equivalence of foreign test suites are independently collected observations, not consequences of the Lean ranking proof. In particular the measured parallel wall-clock percentage must not be described as a proven future speedup.

### `EligibleSchedules.lean`: hard observed admission before optimization

Tests and intent choose the comparison axes and the admission policy. Eligibility is separate from cost ranking: the executable gate requires feasibility, the provided observed-behavior predicate, and all required timing checks. `timedAdmission_exact` proves the required count is positive, exactly that many receipts exist, and every elapsed value is present and no greater than its declared per-receipt limit. A missing timing, empty zero-round campaign, or even one over-limit result is rejected. Equality at the limit is accepted; no hidden tolerance is applied.

`optimumCertificate_exact` proves both admission of the selected candidate and absence of an admitted dominator on the chosen cost axes. `rejected_cannot_be_optimal` prevents a faster cost score from overriding a failed gate. `dominator_refutes_certificate` supplies the constructive counterexample check: an admitted strict dominator invalidates the claimed optimum.

Timing inputs can represent fixed ceilings or paired observed-baseline ceilings; the choice must be named by the policy. The theorem checks the recorded cases and does not predict unseen runs. A paired-baseline experiment is not presented as a user-authored absolute SLA. The observed-behavior Boolean is a policy input; validation of its underlying receipt contents is separate from treating it as evidence of universal behavior preservation.

### `EligibleCampaign.lean`: measured pilot and tested alternate

The concrete pilot has three plans: O1 original tests on one worker, O2 original tests on two workers, R2 reverse-collected tests on the same two-worker plan. Worker capacity is a constraint, not a quality axis. The sole objective is maximum observed wall-clock nanoseconds across three paired rounds. All three plans' imported per-job receipt flags report identical collected ids and phase/outcome/skip records plus successful exits; these Boolean receipt comparisons are inputs whose underlying raw files are audited separately.

Each round's hard cap is that round's observed O1 wall time: `[10769189848,7296152413,7966428370]`. O2 observations are `[5429128102,6128442901,6240471073]`; R2 observations are `[9146680841,6480720115,6777395883]`. The kernel checks receipt counts, behavioral flag conjunctions, every cap inequality, and exact gate admission. All three pass; **none of these observed candidates is gate-rejected**.

The kernel proves O2 is the singleton frontier of this admitted three-plan catalogue. Its maximum observed time is `6240471073 ns`, versus O1 `10769189848 ns` and R2 `9146680841 ns`. R2 is the actually executed alternate: admitted, but dominated, with O2 faster in every recorded paired round. That comparison is not a proof of physical causality or a forecast. A separate clearly named **synthetic** negative control exceeds one cap by one nanosecond and is proved rejected.

The source qualification JSON and policy hashes appear in the module. The hard gate was specified before the runs; the objective was corrected during the run before analysis to wall time only, preserving the earlier policy revision in the empirical artifacts. Do not describe the corrected objective as preregistered before all execution, or the paired-baseline caps as an absolute SLA provided by the user.

## Trust and precise boundary

No `sorry`, admissions, custom axioms, or `native_decide` shortcuts occur. Some finite-reference proofs use standard Lean foundational axioms `propext`, `Classical.choice`, and `Quot.sound` through library lemmas, as disclosed by `#print axioms` in `CHECK.log`. Classical reasoning is used in proofs, not to implement the executable algorithms.

Policies, scopes, lineages, opposite polarities and evidence identities can be encoded in atoms. Their validation is an explicit input obligation, not supplied by set closure. Runtime receipts are not automatically universal semantic proofs. Old evidence does not itself qualify a changed release; a current support or valid transfer derivation is required. Withdrawal filters live roots/rules and recomputes, preserving historical events; the current projection is not monotone when withdrawals occur.

Not proved here: runtime instrumentation fidelity, cryptographic hash binding, external policy authorization, complete language lowering, arbitrary test termination, universal behavior preservation, numerical confidence of measurements, efficient worklist refinement or tight complexity bounds, an incremental provenance/deletion implementation, or globally optimal software performance. These are distinct obligations, not concealed assumptions of the proved closure/qualification results.

## Provenance

Official checker archive: https://github.com/leanprover/lean4/releases/download/v4.19.0/lean-4.19.0-linux.tar.zst

Checked executable SHA-256:
`92c3d35b5bfaa5e0fea413a775d504cf46cd95e1345df61c2274f76779e7e023`

See `SHA256SUMS` for source/check-output hashes.

## Publication scope clarification

The hard timing gate is **whole-suite wall time only**. In the pilot, 8 of 12 individual O2 subprocess times were slower than their paired O1 times, despite every whole-suite gate passing. There is no per-test, per-job, CPU, memory, future-run or universal semantic no-regression guarantee. Three paired rounds and the recorded test inputs are the scope. Policy revision chronology is reported by the experiment files; no signed precommit or independently authenticated timestamp proves that chronology. R2 is admitted but dominated, not rejected. See evidence/ for immutable receipts, source pins, and reproduction scripts.
