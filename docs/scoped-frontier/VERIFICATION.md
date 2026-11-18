# Scoped frontier verification

The final integrated source was checked against upstream base
`af23f5d27990c84ac392c156f4bef61f61b64767`, preserving its admission normalization,
scoped hypergraph, contextual dominance and typed comparison owners. The shared frontier
certificate extends `FiniteFrontier.lean`; no parallel composition module is
published.

## Executed checks

1. The repository `check.sh` completed all **21 modules** with exit status 0 using
   official Lean 4.19.0 and `warningAsError=true`. The checker executable SHA-256
   is `92c3d35b5bfaa5e0fea413a775d504cf46cd95e1345df61c2274f76779e7e023`.
   `PUBLISHER-CHECK.log` records actual output; `CHECK-RECEIPT.json` binds the
   checker, every module and output by SHA-256. No admitted-axiom, error or
   warning diagnostic appears. Printed dependencies are standard Lean logical
   axioms, not new assumptions or proof holes.
2. `ScopedFrontier.lean` executes **32 synthetic guards**. They include both
   admitted nondominated tradeoffs and refusals, contract-owned hard obligations,
   exact subject/context/caps, preserved ties and maximization direction. The
   scoped retained-set certificate accepts the full qualified frontier and
   refuses an unqualified retained member or an omitted tied identity. An
   additional control compares receipt-derived raw coordinates through the
   existing typed comparison owner.
3. `review.py` ran **eight negative controls**. Six deliberately false theorem
   claims were rejected by Lean because their propositions are false: accepting
   mismatched units, omitted non-objective capability evidence, raised caps,
   another venue, mixed subject evidence, or treating a runtime/space tradeoff as
   no regression. An isolated injected proof admission was rejected by the
   source scan; an isolated compiler type error was rejected by the compiler
   gate. Every expected rejection returned status 1, and the replay driver
   returned 0 only after checking those outcomes and diagnostic reasons.

To replay the refusal controls after the full module build:

```sh
python3 docs/scoped-frontier/review.py --lean /path/to/lean-4.19.0/bin/lean
```

`NEGATIVE-CONTROLS.json` records exact false-claim source text, exit status,
diagnostic hashes, checker/module hashes and the final source manifest. The
negative cases execute in temporary copies and do not alter the accepted source.
The initial diagnostic matcher expected a different wording; its first driver
run reported failure despite all eight expected nonzero exits. The matcher was
corrected to Lean's actual false-proposition diagnostic and all controls were
replayed successfully. No rejected driver run is relabeled as a pass.

## What was improved during review

The first adapter still accepted a candidate-supplied policy under a matching
opaque policy ID. Independent review demonstrated that a caller could omit a
non-objective obligation, raise caps, change context, or mix subjects while
editing that second policy. The accepted version eliminates that authority:
`expectedPolicy` derives requirements solely from the fixed comparison contract
and separately named catalogue subject. The general hard-obligation and
indexed-cost witness theorems cover this corrected implementation.

Upstream advanced during the work. Its existing contextual composition,
admission normalization and typed comparison modules were incorporated; the
proposed duplicate composition owner was removed. Typed direction normalization
is reused, and an explicit arithmetic adapter preserves the meanings of workload,
epoch and aggregation as separate premises. The final twenty-one-module check
and these negative controls apply to the reconciled source, not an earlier snapshot.

## Scope

These are formal-model and executable-checker results. They establish scoped
obligation/receipt matching, exact catalogue selection, and congruence through
the existing admission/qualification topology. They do not authenticate external
records, prove instrumentation accuracy, validate arbitrary semantic decoders,
infer future empirical bounds, establish complete software candidate coverage,
or measure an implementation's physical Pareto performance.
