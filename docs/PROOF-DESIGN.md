# Software optimality: stronger proof design, scope, and implications

## Purpose

Make qualification-preserving improvement mechanically checkable for existing software, its tests and stated intent, independent of language and independent of Idol. The selected axes come from those tests and intent. Behavioral qualification and declared timing invariants are admission conditions, never costs that a planner may trade away.

This document distinguishes independently checked v9 results from proposed extensions. All twelve v9 Lean modules were independently replayed successfully. Proposed theorems below are not claimed as checked.

## 1. Replace one large optimality claim with a linked certificate

A qualification/optimization instance has an immutable identity:

`K = (artifact/configuration roots, intent, policy, observation snapshot, venue model, candidate generator, equivalence rules, objective definitions)`.

The result is not merely `best = O2`. It is:

`K -> evidence admission -> behavior-preserving alternatives -> legal schedules -> costs -> frontier -> selected plan`.

Each arrow has its own checker and receipt. A root commits to contents; semantic claims are supplied by checked edges. Source identity, empirical result, semantic equivalence, and authorization remain distinct types even when they share a single underlying graph and aggregate root.

The principal theorem should have this shape:

For fixed K, if the checker accepts `(x, certificate)`, then
1. x meets every required qualification and hard timing constraint;
2. its behavior-preservation evidence is valid for precisely K's scope;
3. x is feasible under K's dependencies, venues, and interference constraints;
4. no admitted candidate in K's declared alternative space strictly dominates x on K's axes.

An additional coverage certificate upgrades a supplied catalogue frontier to the complete frontier of the declared generator. Optimization coverage concerns alternatives, not exhaustive program behavior.

## 2. Three layers of evidence, not three separate ledgers

### Observation

A receipt records the exact artifact, execution configuration, venue, harness, inputs/seed when relevant, test identity, phase/outcome, timing metric, round, and provenance. An observation establishes the recorded case. It does not silently become a law for all cases.

### Qualification

The policy determines which observations or proofs satisfy each obligation. It checks exact required keys, no duplicates, missing results, conflicting receipts, metric units and scope, and current liveness. A suite-level cap is not interchangeable with a per-test cap. Imported observations are not certified authentic merely because their arithmetic is checked.

### Derivation and transfer

Typed hyperedges carry a premise set, conclusion, rule/checker identity, and scope. Cross-lineage reuse is automatic when a checked transfer is applicable; lineage alone neither grants nor forbids reuse. A transfer must preserve the qualifications actually claimed, including relevant environment, effect and harness assumptions.

The same retained evidence can support several claims. Reusing evidence does not multiply independent empirical samples or authorize consuming a stateful resource twice.

## 3. Exact compounding and safe retraction

The current closure theorem already gives the useful identity:

`C(B ∪ D) = C(C(B) ∪ C(D))`.

This is stronger than simply unioning outputs: cross-source rules may yield additional consequences. It justifies separate collection/analysis followed by a combined closure, provided both sides use the same admitted rule semantics.

At snapshot S, filter live roots and authorized, premise-valid rules, then take the least rooted closure. Cycles cannot create support from nothing. A withdrawal invalidates each derivation using the withdrawn dependency, but an independent live derivation can preserve the same conclusion. Prior snapshot results remain immutable.

The historical event set grows monotonically. The current live qualification projection need not, because withdrawal is deliberately meaningful. Count thresholds and measurements require their own state, not a claim that all evidence stabilizes after the number of occupancy cells.

## 4. Composition of behavior and composition of optimality are different theorems

Behavioral composition requires a compatibility judgment. Useful admitted cases include disjoint effects, explicitly threaded state, and a checked joint pre/postcondition. Two passing operations on the same initial balance are not automatically a passing sequential transaction. Such an invalid composition is rejected before ranking.

For optimization, propose the following reusable decomposition theorem:

Let feasible joint alternatives be the Cartesian product `X1 × ... × Xk`. Suppose joint objective aggregation is coordinatewise monotone in every local objective vector, and every cross-component constraint has already been accounted for. Then removing a locally dominated alternative cannot remove every representative of a globally nondominated objective vector.

Reason: replace a dominated local choice by a no-worse one while holding all other choices fixed. Feasibility is preserved by the product assumption; monotonic aggregation preserves no-worse joint costs. Repeating obtains a joint alternative from the product of local frontiers.

Do NOT claim every product of local-frontier members is globally nondominated: global comparison is still required. Non-strict aggregation can collapse a local strict improvement to a tie, so preserve representatives and distinguish vector coverage from identity coverage.

If venues, setup state, queues or effects couple components, carry their interface state into the decomposition or solve the coupled block jointly. This is the exact criterion that makes decomposition a theorem rather than an optimization guess.

## 5. Stronger certificates with cheaper checking

The existing exhaustive frontier filter is an excellent reference oracle. Production search need not reproduce it literally.

Proposed certificate forms:
- **Feasible improvement:** candidate admission plus a checked strict-dominance vector against the baseline.
- **Catalogue optimum:** admission plus checked comparisons against each admitted catalogue member.
- **Generator optimum:** exhaustive coverage or certified branch pruning, with each omitted region carrying a sound objective lower bound showing it cannot dominate the selected candidate.
- **Frontier completeness:** coverage of admitted alternatives, nondomination of retained entries, and a retained dominator for every omitted admitted alternative.

For a finite strict Pareto order, a fully computed frontier dominates every excluded candidate through a descending chain ending at a frontier member. This is a useful additional theorem and produces concise exclusion explanations.

A bound used for pruning must be an actual bound in the named model. A learned estimate can prioritize search but cannot justify dropping a region. Use a verified worklist as a refinement of the current closure specification; keep the exponential reference as a small-case differential oracle.

## 6. Empirical invariants and counterfactuals

Time is measured in the exact unit and scope named by the policy. If elapsed time is constrained to be no greater than a baseline or ceiling, an over-cap run is rejected, regardless of other improvements. Selecting a faster suite does not establish that every subprocess or test got faster.

Separate three test families:
1. **Admitted counterfactual:** another qualified alternative, holding the intended comparison factors fixed. Compare the selected axes. An admitted strict dominator refutes an optimality certificate.
2. **Gate mutation:** wrong artifact/scope, duplicate receipt, stale transfer, altered outcome, missing timing, or one-nanosecond cap violation. It should be refused; it is not a legal Pareto tradeoff.
3. **Checker differential:** enumerate small instances independently, permute/duplicate inputs, remove premises, and compare the implementation against the proved reference.

Do not confuse an empirical counterfactual comparison with a causal effect estimate. If causal attribution is wanted, preregister the compared factor and balance/randomize nuisance order. Optimality of the recorded admissible catalogue does not itself require a causal attribution claim.

## 7. What the foreign experiments actually establish

The latest campaign tests O1, O2 and R2 across pinned click, attrs, tomli and packaging suites, with three observed rounds. All three meet the declared paired whole-suite timing caps and observed identity/outcome checks. On the sole axis, maximum observed suite wall time, the checked catalogue frontier is O2 alone:

- O1: 10,769,189,848 ns
- O2: 6,240,471,073 ns
- R2: 9,146,680,841 ns

R2 is an executed, admitted alternative with the same two-worker queues as O2 but reversed within-job collection. It is dominated on the recorded axis. The synthetic cap violation is a separate refusal test.

This directly supports a real use case: optimize test execution without compiler IR or source rewriting. It does not demonstrate source-rewrite certification yet. Whole-suite acceleration also does not establish per-job timing preservation: 8 of 12 O2 subprocess durations increased relative to O1. The scope must remain exactly whole-suite timing unless a new per-job invariant is actually measured and admitted.

## 8. Generality and practical implications

The theorem parameters are software-independent: a set of obligations, evidence keys, a candidate representation, legality/preservation checkers, and declared objective functions. Foreign test suites instantiate the same interfaces as native programs. No compiler IR is necessary to reorder test runners, select venues, share certified unchanged evidence, or compare qualified configurations.

Source rewriting is an extension at the preservation boundary, not a prerequisite. Add a language-specific equivalence or translation-validation certificate only when such alternatives are proposed. The optimizer and qualification algebra remain unchanged.

This makes the framework a reusable qualification-preserving optimizer, rather than a claim that one graph storage layout is universally fastest. Better search engines can be swapped in without enlarging the acceptance authority when their outputs still pass the same checker.

A deterministic display total order can be supplied by canonical identifiers for reproducibility. It must not be confused with Pareto dominance, which can leave alternatives incomparable. Tie-breaking is presentation or a separately declared selection policy.

## 9. Implementation priorities and status

**Already machine-checked in v7:** rooted closure and compounding; exact executable closure under checked bounds; Boolean profile enumeration; nondominated filtering; fixed schedule-model enumeration/feasibility; admission-before-ranking; concrete foreign model and measured-catalogue frontier arithmetic.

**Independently machine-checked in v9:** `ScopedEvidence.lean` validates typed scope, unique obligations/receipt IDs, exact required count, per-round matching, observed-pass and timing gates. `ScopedSelection.lean` directly gates eligible optimum selection through that checker. `ScopedCampaign.lean` instantiates the actual pilot and tests missing/failed chosen evidence with fallback to R2. `LinearSelection.lean` proves scalar argmin and exactly n−1 scalar comparisons for nonempty input; this is not a total-runtime bound. `allMinima` returns all scalar minima with membership permutation invariance; serialization order and duplicate multiplicity are retained. Canonical serialization needs a separate normalization step.

Exact ID comparison does not authenticate the referenced policy or receipt bytes. Policy authorization, liveness, raw-observation ingestion, compatible cross-policy cost definitions and semantic truth of imported pass bits remain external obligations. Repeated transport duplicates must be normalized upstream when ledger idempotence is desired; the selected-receipt checker rejects duplicate IDs.

**Next proof additions (not yet checked):**
1. General multi-axis frontier coverage and a certified pruning interface.
2. Separable composition of local objective-frontier representatives with coupling interfaces.
3. Performant worklist refinement of closure, including deletion/recomputation semantics.
4. Canonical serialized output refinement and authenticated import-to-model binding.

**Next engineering additions:**
1. Canonical receipt importer with schema/version, policy and source hashes; exact per-test requirements where the policy calls for them.
2. Durable raw traces and an independently reproducible import-to-Lean manifest.
3. Broader foreign campaigns using unchanged declared axes and hard invariants; report rejected alternatives as such.
4. One actual certified source rewrite, only after its preservation adapter exists.

The v9 bridge closes the modeled scoped-qualification-to-selection gap. The strongest next engineering deliverable is a replayable authenticated raw-observation-to-model importer; modeled pass bits remain supplied evidence, not kernel-authenticated physical facts.
