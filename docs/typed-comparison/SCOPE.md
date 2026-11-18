# Typed comparison contracts and composable transports

This module prevents accidental numerical comparisons across incompatible
measurement definitions. It is a derived qualification/comparison layer, not a
new evidence ledger, graph, or independent source of truth.

## Contract identity

Every `Contract` carries its ordered axis list, workload identity, venue
identity, and epoch identity. Each axis carries metric identity, unit identity,
orientation (minimize/maximize), and aggregation identity. IDs denote canonical,
versioned definitions, not unverified display labels. Finite lists carry exact
integer samples. Value list length must equal axis list length.

`direct` returns:
- `None`: the contracts differ in ANY field, or either value vector has the
  wrong shape. This is incomparable/invalid, not a comparison failure result.
- `Some true`: same contract, valid shapes, weak improvement on every axis and
  strict improvement on at least one axis.
- `Some false`: same contract, valid shapes, no strict dominance established.

The theorem `direct_improvement` checks this complete contract and Pareto claim.
Maximize axes are normalized by integer negation; arbitrary default scores or
weights are not introduced. Empty axis lists never establish strict dominance.
There is no conclusion of equivalence, deterioration, or regression from `false`.

## Explicit transport, not a permissive override

A `Transport meaning source target` is indexed by the EXACT source and target
contracts. It contains an executable conversion, a Lean proof of output shape,
and a Lean proof preserving the application's FIXED semantic interpretation.
Transport proofs compose transitively, including across multiple adapters.
The identity transport is supplied. `compareVia` converts both observations to
the same target contract and compares there. There is no arbitrary Boolean
'certified' flag bypassing contract equality.

`compareVia_exact` proves the precise target-axis dominance. `transported_meaning`
proves preservation of source interpretation. `compareVia_semantic` additionally
transfers any application-defined better-than relation back to source meanings
IF target numeric dominance is sound for that relation (`metricSound`). This
makes the semantic boundary explicit instead of treating numbers as self-validating.

Changing venue/workload/epoch requires an explicit transport just as unit
changes do. The theorem does not automatically manufacture such certificates.
The application's interpretation and metricSound theorem must be fixed and
versioned at admission, not freely supplied by an untrusted certificate author.
A constant bogus interpretation or false measurement model is NOT made true by
this module. Empirical observations, authorizer validity, contract content-ID
integrity, and applicability to physical runtime remain evidence obligations.
For cross-venue empirical transports, those obligations must be represented by
the admitted model and its qualification scope; no universal runtime invariance
is asserted.

## Integration

Use normalized admitted receipts from `Admission` as input, carrying canonical
contract and observation identities. Derive candidates/values from those same
records. Store/check transport derivations through the existing typed hypergraph
admission path, retaining source/target contracts and all premises. Do not merge
frontiers from incompatible contracts; either partition by exact contract or
explicitly transport to a shared target. This module proves the comparison gate;
it does not yet implement serialized transport certificate loading, hashes,
signatures, external measurement collectors, interval uncertainty, or retraction
of transport proof records. The existing hypergraph dependency/retraction layer
must track them.

## Tests and reproducibility

The integrated repository `./check.sh` builds dependencies before this module and ComparisonTests.lean, using Lean 4.19.0 with warnings as errors and proof-escape scans. The publisher verified the full suite in a separate source-copy directory. Existing proof sources are unmodified.

25 executable guards and 4 kernel examples cover direct improvement/nondominance,
all eight contract mismatch categories, short/long malformed vectors, empty
axes, maximize orientation, mixed axes, axis ordering, an actual exact
millisecond-to-microsecond conversion, composed transport, and rejection of an
invalid identity unit conversion. Counterexample: raw 2 < 3 does not justify
2 milliseconds < 3 microseconds. The direct gate rejects it; the correctly
transported comparison reports no dominance.

No runtime speedup or universal Pareto-optimality claim is made. Arithmetic is
exact over integers; applications needing rationals, intervals, quantiles, or
confidence bounds need their corresponding typed value/interpretation extension.
