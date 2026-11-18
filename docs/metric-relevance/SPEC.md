# Exact, scoped metric-to-intent relevance

Status: proposed semantics with executable illustrative fixtures. Not a claim about measured production causal effects. Applies to any software qualification workflow, not specifically Idol.

## 1. Identity and input contract

A relevance result names `(intent composition, metric definition, artifact/configuration, venue, harness, policy, evidence snapshot, intervention catalogue)` by immutable identity. The intent supplies its clauses, AND/OR/threshold composition, declared axes and any preference ordering. No new utility weights or objectives are inferred. A total evaluator maps a recorded or explicitly modeled input assignment to the intent's result. Keep `unknown`, `conflict`, timeout and failed qualification distinct from success.

Each counterfactual row names both endpoints, exactly what may change, what is held invariant, its admissibility witness, and whether outcomes are modeled, proved, or observed. Exact enumeration over a catalogue is not evidence that the catalogue exhausts all admissible mutations. A completeness certificate is a separate field. Duplicate delivery of one receipt is idempotent; separate execution IDs remain separate repetitions.

## 2. The relevance profile, not a magic scalar

Return the following per clause and for the composed root. Keep counts and denominators, not just percentages.

* **Declared consumption:** the set of unique intent clauses reading the metric, with the expression and provenance. Graph reachability identifies candidates, not semantic contribution. Repeated paths do not multiply credit.
* **Direct pivotality:** for an admissible pair that changes the metric while keeping other evaluator inputs fixed, count whether the clause/root changes. Report `changed/eligible_pairs`. Also report signed transitions (`false→true`, `true→false`) and the complete transition matrix for nonbinary statuses. This can be zero at the root while nonzero at a leaf.
* **Compositional interaction:** for a declared baseline and an admissible full intervention cube over a metric group, evaluate every coalition. For each Boolean clause indicator f, the interaction of group T is `sum_{S subset T} (-1)^(|T|-|S|) f(S)`. This exact signed coefficient detects complementarity/redundancy relative to that baseline. It is not a probability or an apportioned scalar reward. Do not fabricate missing coalition outcomes. An interaction certificate reconstructs each coalition result from the coefficients. For partial catalogues return only supported pair comparisons, with uncovered cells explicit.
* **Indirect-mutation sensitivity:** over named admissible mutations of other components/inputs, recompute the metric and intent. Report a 2×2 table counting `(metric changed?, root changed?)`, plus signed/magnitude deltas in the metric's declared units. Changes in different units are not added. Mutation rows rejected by hard behavior or performance invariants cannot enter the qualified improvement frontier; retain their diagnostic outcomes separately.
* **Observed repeat instability:** group distinct executions by the exact fixed scope and controlled settings. For categorical outcomes with counts c_j and r total executions, the number of unordered disagreeing pairs is `(r²-sum_j c_j²)/2`; denominator is `r(r-1)/2`. This fraction is exact for the recorded executions. It is not the unknown future failure probability. Also retain full metric/outcome distributions and root-transition counts, so benign measurement jitter is not conflated with qualification flakiness. Missing data are explicit, not success or agreement.

For zero eligible pairs, pivotality is undefined with counts `0/0`, not zero relevance. Repeat disagreement is undefined for fewer than two runs. Never combine these denominators or collapse these axes without an explicitly declared aggregation rule. A displayed ordering may use declared lexicographic priorities or Pareto dominance; a stable ID tie-breaker is presentation, not relevance superiority.

## 3. Counterfactual attribution, without causal overclaim

For mutation z→z', denote metric m(z), other intent inputs x(z), and F(m,x). Record the actual before/after root values. Where admissible, also evaluate bridge `F(m(z), x(z'))`. For a numeric clause indicator, the algebraic identity

`F(m(z'),x(z')) - F(m(z),x(z))`
`= [F(m(z'),x(z')) - F(m(z),x(z'))] + [F(m(z),x(z')) - F(m(z),x(z))]`

separates a metric-changing comparison from a held-metric comparison. This is exact attribution *in the declared evaluator*. Its causal interpretation requires the interventions and held quantities to be physically/semantically meaningful. The alternative bridge generally gives a different allocation when interactions exist: report both or the interaction, not a falsely unique split. If a bridge is inadmissible, mark attribution unavailable rather than treating a real dependency as independently switchable.

## 4. Dependencies, compounding and withdrawal

Evidence union is idempotent on immutable receipt ID; changed payload under the same ID is conflict, never last-write-wins. Mutation pairs and repetition pairs have canonical IDs, so merging catalogues does not double-count. Derivations carry the exact premises and transfer certificates used. Apply the existing snapshot-liveness projection before forming denominators. Withdrawal removes dependent comparisons from the current profile while preserving historical results.

Partitioning is safe when it partitions *rows of the same scoped measure*: disjoint row counts add exactly. Overlapping partitions require set union/deduplication, not addition. Shared executions produce statistically dependent pairs; the finite counts stay exact, but independent-sample confidence claims are not licensed. Cross-scope totals must retain strata or use explicitly declared mixture weights.

## 5. Machine-checkable obligations

1. Evaluator totality on the admitted domain and fidelity of its intent composition.
2. Counterfactual admission preserves the designated held-input projection and hard constraints.
3. Counts equal filtered catalogue cardinalities and lie between zero and denominator.
4. Fractions agree with those counts, with explicit empty-domain cases.
5. Transition-table cells partition their admitted catalogue.
6. Receipt and pair canonicalization make merge associative, commutative and idempotent; permutation changes no profile.
7. Full-cube interaction coefficients reconstruct all coalition outcomes exactly.
8. Bridge decomposition telescopes exactly; no proof upgrades modeled or observed rows into experimentally established causation.
9. Profile equality under evidence reorder and duplicate delivery; liveness recomputation excludes all invalidated dependencies.

Computational cost is linear in explicit pair rows times evaluator cost, plus grouping/deduplication. Full k-factor interaction enumeration has 2^k cells; this is explicit rather than hidden in a subjective importance score. No machine proof should claim instrumentation truth or causal validity merely from arithmetic on receipts.

## 6. Illustrative checked fixtures

Intent `(latency <= 10 AND correct) OR fallback`, metric 8→12, contexts `(correct,fallback)` in `{false,true}²`: the latency leaf changes in 4/4; the composed root changes in 1/4. A fallback that is true masks the latency clause. These fractions describe uniformly counted named pairs, not a deployment input distribution.

AND coalition table `00→0, 10→0, 01→0, 11→1`: each singleton marginal at the baseline is zero, but the pair interaction is +1. OR table `00→0, 10→1, 01→1, 11→1`: singleton coefficients +1,+1 and pair interaction −1. This prevents calling individually masked metrics irrelevant to their composition.

Four indirect-mutation rows realize each joint cell once: change only latency (8→9) with same qualified root; change latency 8→12 with changed root; hold latency8 and change correctness with changed root; change only a declared auxiliary input with no metric/root change. Thus metric sensitivity 2/4, root sensitivity 2/4, joint-change 1/4, not a claim that every root change was caused by the metric.

Five same-scope observed results `[pass,pass,pass,fail,fail]`: 6 disagreeing unordered pairs out of 10. The empirical failure frequency is 2/5, a different measure. Duplicate receipt delivery changes neither. Two observations from another venue are another stratum, not silently extra repetitions.
