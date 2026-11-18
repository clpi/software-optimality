# Current public interface integration

This integration starts at optimality commit
`b52c3170a6e108345bd5ada44ca7355dae55b395` and uses the canonical Lake dependency
on quantifiable commit `f370992611d8c722e4897e67dbb8eaecf3d872ed`. The real Git
checkout used by Lake is checked against the independently verified source
snapshot. The old temporary-copy runner and its separate dependency checksum
file remain removed.

## Reproduce

Use the pinned Lean 4.19.0 (`6caaee842e94`) toolchain:

```sh
sh check.sh
sh composition/check.sh
```

`LEAN` and `LAKE` can name absolute compiler and Lake paths. The joint command
runs the default Lake build with warnings treated as errors, then the six
intentional false-claim controls. Its Git dependency comes from `lakefile.lean`
and `lake-manifest.json`, with both revision fields pinned to the same commit.
No dependency override or fabricated checkout metadata was used for the recorded
run. No timing benchmark runs unless `--benchmark` is explicitly added.

The default Lake target retains every upstream root, including
`CanonicalDominance`, `WorklistClosure`, `StrictSchedules`, `CheckedTransfer`,
`EvidenceTransport`, `LinkedCertificate`, and `ScopedCompatibility`. It also
includes the new bridge and controls and all three existing covered-frontier
control/archive modules. `SoftwareOptimality` exports the bridge. `ROOT-CHECK.log`
records the existing standalone proof gate; `CHECK.log` records the Lake build
and the six expected false-proposition failures followed by joint success.

`RECEIPT.json` binds exact source hashes, the compiler, Lake, the actual dependency
HEAD and clean tracked source state, commands, outcomes, and theorem endpoints.
`UPSTREAM-RECEIPT.json` is the unchanged independent record of the public
repository's clean `lake --wfail build`, current Pareto controls, and axiom audit
of all 186 declared public theorems. `UPSTREAM-SNAPSHOT.json` binds all 41 tracked
Git blobs. `UPSTREAM-BUILD.log`, `UPSTREAM-AXIOMS.log`, and `UPSTREAM-PROBE.lean`
retain its build output and exact theorem inventory. Only the usual Lean
`propext`, `Classical.choice`, and `Quot.sound` occur in that inventory.
The public historical `verification/coverage/verify.py` deliberately rejects
newer source hashes; it is not presented as a current checker.

The existing examples are checked separately. `OPTIMALITY-EXAMPLE.log` records
the release-schedule proof: 23 to 16 model ticks, with a 16-tick critical-path
lower bound for every feasible schedule. `UPSTREAM-EXAMPLE.log` records the
ledger-repair proof: two named gaps require at least two appended records, and
repeating one repaired ID leaves the other gap. These are statements in their
declared models, with no production timing claim.

## What is connected

The upstream `QualifiedSelection.gate` already calls public
`noQualifiedBehaviorLost` with independently supplied requirements as
`PriorQualification` and computed facts as `BehaviorSubmission`. Its existing
`gate_exact` theorem still exposes required-behavior inclusion, scoped receipts,
validated ledger membership, execution/metric uniqueness, and absent contraries.
The duplicate local list-form release gate remains removed.

`InterfaceBridge` adapts public `Interface.dominates` to the existing
`FiniteFrontier` and `FrontierComposition` identity certificates. It keeps axis
polarity, full vector alignment, same-symbol comparison, observed-behavior
preservation, all-axis nonregression, and at least one strict improvement. It
uses the complete relation, not a measure-only helper. `two_axis_agrees` forwards
to `CanonicalDominance.Optimality.local_dominates_iff_canonical`; it does not
introduce another dominance or release authority.

Finite pruning preserves every frontier identity exactly when the existing
retained-witness check succeeds. The final certificate accepts exactly the full
nondominated identity set. Candidate IDs remain the carrier: distinct candidates
with equal profiles must both survive if nondominated.
`public_frontier_agrees` and `aligned_certificate_exact` apply the public
frontier's explicit alignment admission and prove exact correspondence with it.
The latter checks the existing finite certificate on the aligned catalogue;
it does not erase tied candidate identities when profiles map to equal values.

`InterfaceControls` applies the current public command-service `Instance` through
`QualifiedClosure`. Closing joined roots derives the full path; a missing joint
premise does not. The public theorem that separate colorings miss the joined
consequence is checked alongside this adapter.

## Positive and refusal controls

Controls cover mixed axis polarity, exact tied identities, dropped observed
behavior, an incomparable tradeoff, a different semantic symbol, malformed
reading length, empty axes, duplicate-symbol releases, and omitted qualified
behavior. The negative runner separately asks Lean to accept six false claims:
delete a tied identity; accept a behavior drop; improve despite a regressed
maximize axis; dominate with a malformed profile; derive a joint fact with a
missing premise; and retain a malformed profile after alignment admission.
Every claim must fail specifically because kernel reduction finds its proposition
false. Missing imports and unrelated compiler failures are rejected as invalid
control outcomes. Generated false claims live in an isolated temporary directory
while preserving the Lake environment's working directory.

## Limits

This is source-pinned proof conformance and composition. Profiles and their
observed bits remain supplied data. The bridge does not authenticate observations,
establish physical feasibility, establish a nonempty meaningful objective space,
or prove that the catalogue covers every possible implementation. Alignment
admission removes malformed profiles; different semantic symbols can remain
incomparable. An application must independently establish its comparison domain.
The canonical owner also keeps its explicit limits for signed costs and eligible
or default-observed profile transports; this adapter does not broaden them.

A finite frontier certificate is not a release certificate. The scoped
feasible-generator and named strict-replacement boundaries from PR #4 remain the
relevant obligations. All new controls use synthetic data. The original O1/O2/R2
archive certificate and earlier joint receipts retain their historical pins and
measurement scope. Nothing here is a fresh timing experiment, proof of the Idol
producer migration, or whole-Idol empirical Pareto certificate.
