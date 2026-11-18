# Scoped frontier comparison contract

`ScopedFrontier.lean` closes the explicit comparison-compatibility gap between
scoped qualification and multi-axis selection. It reuses `ScopedEvidence.qualify`,
`FiniteFrontier.strictPareto`/`frontier`, the existing hypergraph incremental
equivalence theorem, and `AdmissionHypergraph`'s live-support normalization bridge.
It introduces no alternate evidence ledger or inference relation.

## Relation to typed comparison and transport

`ComparisonContract.lean` owns raw vector compatibility, direction normalization,
and proof-carrying semantic transports. This module owns contract-derived hard
obligations, named subjects, and measured receipt selection. Both use the same
`ComparisonContract.normalize` primitive; these are successive validation
boundaries rather than competing definitions of numeric improvement.

`typedObservation` supplies the existing typed observation representation from
an admitted scoped input. `typed_cost_agrees`, `typed_dominance_agrees`, and
`typed_direct_agrees` prove arithmetic agreement under an explicit axis/venue
alignment for a supplied typed contract.

| Scoped information | Typed comparison information | Required relation |
|---|---|---|
| Ordered objective metric IDs | Ordered axis metric IDs | Exact index-by-index equality |
| Declared metric unit | Axis unit | A matching declared metric/unit witness |
| Minimize/maximize choice | `Direction` | Exact orientation; shared normalization |
| Fixed venue | Typed venue | Equality |
| Required observation round | Aggregation | No automatic mapping; the round selects the receipt |
| Intent and comparison scope | Workload and epoch | No automatic mapping; supplied typed meanings remain explicit |

The adapter does not prove the physical meaning of workload, epoch or aggregation
IDs, or turn them into aliases for intent, scope or round. Their applicability
must be established for the supplied contract. It also does not automatically
admit a `Transport` or move qualification across units/venues. Such transport
still needs the existing typed owner's fixed-meaning proof and the appropriate
admitted provenance. The raw `typedValues` projection alone is not qualification;
constructing `typedObservation` requires the scoped admission proof.
That proof qualifies the scoped contract. The resulting typed observation proves
numeric shape, not qualification under arbitrary additional workload, epoch or
aggregation labels; numeric alignment alone does not establish those meanings.

## Contract and admission

A shared immutable comparison contract names the instance/alternative space,
intent, qualification policy, preservation contract, fixed venue/harness, metric
identities and units, every required obligation with its round and exact limit,
and ordered objective axes. Each axis names a metric, a round, and whether its
value is minimized or maximized. Hard qualification obligations need not be
objective axes.

The candidate catalogue contains independently named subjects, each with its
artifact, configuration and lineage. Submitted input has only its declared
contract and receipts. `expectedPolicy` derives the complete policy from the
authoritative contract and the catalogue subject. The submitted input cannot
omit a requirement, raise its cap, select a different venue/harness, or mix
subjects by supplying a second policy under an unchanged policy ID.

Admission requires a nonempty objective list, unique metric identities, unique
metric/round axis and obligation keys, declared metrics for every obligation and
axis, exact contract equality, a present value for every axis, and the existing
scoped receipt checker on the derived policy. `admitted_obligation_witness`
proves every contract obligation has its exact successful bounded receipt,
including obligations outside the objective axes. A failed or missing capability
obligation remains a refusal even if all selected costs improve.

Each objective coordinate resolves exactly one policy obligation for its
metric/round, then exactly one receipt matching that obligation's full scope and
round. The objective value is that receipt's measured value. Missing or ambiguous
coordinates are refused. Multiple scoped observations sharing one metric/round
must use distinct metric identities or a separately qualified aggregate metric;
this adapter does not invent an aggregation.

There is no independently supplied numeric cost vector. No truncating vector zip
can omit an objective. Maximized values are negated once for the existing
minimizing Pareto comparator. The total cost accessor has defaults outside the
declared admitted domain; admission supplies a measured witness for every actual
axis, and selection compares only those axes of admitted candidates.

## Selection and replacement are separate

`selected_exact` proves that selection contains precisely the admitted catalogue
members with no admitted strict Pareto dominator. `selected_has_no_qualified_dominator`
and `dominator_excludes` expose the corresponding counterexample boundary.
`tied_member_retained` preserves every admitted candidate with an equal objective
vector. `selected_order_independent` proves membership unchanged by equivalent
reordered/duplicated catalogues; serialized list order and multiplicity are not
canonicalized.

`certify` checks a submitted retained set through the existing
`FiniteFrontier.certificate`, using this same admitted catalogue and measured
cost contract. `certified_select_exact` proves exact membership agreement with
`select`; retained points are admitted and every hard obligation has its scoped
receipt witness. A retained unqualified point and omission of a tied frontier
identity both refuse. Search cannot bypass qualification by presenting a raw
cost certificate to this entry point.

`noRegression` separately checks both inputs' qualification and no worse cost on
every declared axis against a named incumbent. A faster candidate using more
space can be nondominated and still fail this replacement condition. Frontier
membership never silently changes a no-regression policy into a weighted tradeoff.

`incremental_selection_exact` applies the existing exact hypergraph incremental
closure to any deterministic input projection, including this complete admission
and comparison adapter. Its output equals selection from full new closure.
This is a semantic equality, not a fast incremental frontier implementation or a
cost bound.

`admitted_provenance_selection_same` connects the existing live-support event
admission and hypergraph closure to this selection adapter: equal admitted event
provenance gives the same selected catalogue under any deterministic projection
of qualifications. `replay_selection_idempotent` and
`merge_selection_order_independent` specialize this to duplicated raw events and
branch merge order. Raw events still must be normalized through `Admission`;
unioning independently normalized live sets is not substituted. These results
are congruence through the existing decoder, not proof that arbitrary decoders or
receipt projections correctly interpret physical measurements.

## Coverage beyond a supplied catalogue

`certified_generator_exact` lifts the existing exact catalogue certificate to a
declared generator. `covers` requires that every catalogue member belongs to that
generator and that every omitted admitted generator member has a strict admitted
dominator in the catalogue. `dominates_trans` uses the existing no-worse-on-every-axis
and strict-on-at-least-one comparator to discharge outside-catalogue challengers.
The result preserves every nondominated identity, including ties. The generator
need not be finite, but its coverage premise must be proved. Search exhaustion,
an estimate, or a descending chain of omitted candidates cannot supply it: every
coverage witness must land in the named catalogue.

`checkCoverage` executes that obligation for a declared finite domain through
the existing `FrontierComposition.checkCover` owner, with admitted lists and an
additional check that all catalogue identities belong to the declared domain.
`certifyCovered` additionally checks the contract and existing retained-frontier
certificate. It rejects an empty-axis contract even when an empty result would
make a bare catalogue claim vacuous. The result is exact for **admitted** domain
members. A candidate without required measurements is not admitted; that fact
does not establish its infeasibility or exclusion from the physical search space.

`certified_feasible_generator_exact` provides the stronger boundary. The caller
supplies an independently specified feasible predicate and proves qualification
sound and complete for it throughout the generator. Therefore every feasible
candidate has admitted comparable cost evidence; absence of a measurement cannot
hide a feasible challenger. `checkQualification`, `certifyFeasible`, and
`certified_feasible_frontier` execute and establish this check for a finite domain.
The external feasible predicate cannot acquire its intended meaning merely by
being defined as receipt admission. A later pruning scheme using proved cost
bounds instead of complete observations must discharge its own coverage and
comparison obligations; the present checker does not invent missing values.

`certifyReplacement` adds a named admitted incumbent in the domain, a chosen
retained identity, the existing `noRegression` predicate, and strict improvement.
Its soundness theorem gives exact admitted-frontier membership and no-worse cost
on all declared axes with a strict win on one. `certifyFeasibleReplacement` adds
qualification completeness and yields the corresponding feasible-frontier
statement. An empty result, an equal-cost tie, or an incomparable tradeoff cannot
pass these replacement boundaries. These checks concern the named comparison
contract; physical observation authenticity and authorization remain external.

`incremental_generator_exact` and `incremental_feasible_generator_exact` compose
the respective claims with full-premise old/new hypergraph qualification.
`certifyClosed` is an executable adapter to `ExecutableClosure.checkedClose` and
the existing scoped finite certificate. `certifyClosed_exact` proves that the
computed membership predicate equals the incremental semantics and that the
retained set is the exact admitted-domain frontier. The obligation-witness
theorem retains the original scoped receipt/round/cap checks. The supplied input
projection must still interpret those facts soundly; an arbitrary projection
does not authenticate measurements. This adapter calls the exhaustive reference
closure, not a faster incremental implementation, and makes no cost claim.

The checks in `docs/covered-frontier/` include an actual archived-data case:
the original O1/O2/R2 campaign, its original maximum-observed-wall-time objective,
and the three prescribed rounds. `review.py` binds the archive, policy, and
qualification report to their pinned hashes and checks the Lean constants
against the report. `Campaign.lean` proves exhaustive coverage of that closed
recorded-candidate type and its exact qualified frontier. This is a replay of
imported observations, not a new experiment, an instance of an authenticated
hypergraph importer, or evidence about Idol performance.

## Executed synthetic controls

Module guards distinguish a declared millisecond profile from a nanosecond
contract even when the raw numbers would reverse their physical ranking. They
also cover absent objective or non-objective evidence, omission of a hard
obligation from the submitted contract, increased caps, changed venue/harness/
lineage/intent/policy, foreign and mixed subjects, duplicate receipts, failed
capability evidence, changed maximize direction, empty/duplicate axes, retained
ties, catalogue reorder, and the runtime/space tradeoff versus no-regression
distinction. These are synthetic checker controls, not software measurements.

## Remaining trust boundary

Metric/unit IDs and contract IDs are exact opaque identifiers. The full contract
contents, exact obligation caps and named subjects are checked in this adapter;
they are not replaced by equality of a caller's policy ID. Ingestion still must
authenticate receipt/contract contents, bind metric identities to actual unit
schemas, validate instrumentation, authorize the chosen comparison contract and
its subject catalogue, establish current liveness, and validate the declared
preservation contract. Changing a unit label while lying about the receipt's
physical measurement is outside identifier equality's guarantee. The theorem
does not infer capability or semantic equivalence from timings alone.

`Receipt.elapsed` remains the existing nonnegative measured-value field. Using it
for another declared metric requires the ingestion/schema adapter to establish
that meaning; the proof does not reinterpret arbitrary elapsed data as memory or
capability scores. Signed/interval/probabilistic objectives need an explicit
extension or qualified metric projection. The supplied catalogue's completeness
and coverage of real software are separate premises. Selection is a frontier for
that catalogue and contract, not global software optimality.
