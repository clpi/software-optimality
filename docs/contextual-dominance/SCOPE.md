# Contextual compositional dominance

## Checked result

`ContextualDominance.lean` checks with Lean 4.19 and Std only. All six explicitly printed theorem dependencies are axiom-free. Run `LEAN=/path/to/lean ./check.sh`. `CHECK.log` records the successful run.

Costs are vectors of natural numbers indexed by any axis type, with minimization orientation. Contexts and component identities are abstract types. A context may encode the entire remaining hypergraph, interfaces, venue placement, shared resources, effects and policy snapshot. This interpretation is an adapter obligation, not something this file derives from source code.

`Replaces feasible cost x y` means that in every context admitting y, x is admitted and every declared composed cost of x is no worse. The relation is reflexive and transitive. `monotone_context_replacement` derives this relation from a local no-worse comparison ONLY given explicit feasibility preservation and pointwise monotone composition. No theorem infers these obligations from hashes, local measurements, or incidence alone.

For pruning, retained candidates are a subset of the original candidates; every feasible original candidate must have a feasible retained no-worse representative. Under those obligations:

1. All achievable componentwise performance bounds are exactly preserved.
2. Every original Pareto point has a retained Pareto representative with exactly equal cost on every axis.
3. Every retained Pareto point is also original-Pareto.

Thus the objective-vector frontier is preserved exactly, without falsely promising preservation of all candidate identities. This theorem is applicable to finite search catalogues but does not implement enumeration, synthesize representative witnesses, or prove a particular search catalogue exhaustive.

## Kernel-checked counterexamples

- A component improves local time from 2 to 1 but incurs 100 additional contention time; its composed time is 101 versus 2. Local dominance alone does not license pruning.
- A context admitting only values at least 2 admits candidate 2, not candidate 1, despite 1's smaller local cost. Feasibility must be preserved.
- Parallel makespan max(1,10) = max(2,10). A strict local improvement becomes a global tie under monotone composition. Both distinct Bool candidates are Pareto-optimal in the original catalogue; retaining only true removes false's identity while keeping the attainable cost vector.

If the product promises *all* equally optimal configurations, retain equivalence-class preimages/backpointers. If it promises cost vectors plus representative configurations, the checked pruning guarantee suffices. Strict monotonicity, stronger than monotonicity, is needed to infer a strict global improvement directly from a strict local improvement.

## What remains external

- Sound attribution of topology/effects/interfaces to contexts.
- Fidelity and stability of measured costs. A deterministic comparison of receipts is not a proof of future runtime.
- Correct feasibility predicates and complete representation of interactions.
- Certified representative search and finite frontier enumeration.
- Incremental materialization equivalence to the authoritative hypergraph-derived view.
- Rational, signed, interval-valued, probabilistic, or maximization-axis adapters.

No independent graph or ledger is introduced. These functions and predicates can be derived views over the existing authoritative hypergraph. The proof is not a claim of universal practical speedup, or of globally exhaustive Pareto optimality across unspecified candidates.
