# Covered frontier verification

Base: `clpi/software-optimality` commit
`97a5d7f3e68de47cd9eb26221b83e713121673fd`. The baseline source blobs were checked
against the upstream Git tree before modification. The existing proof owner is
`ScopedFrontier.lean`; its comparator, scoped receipt checker, hypergraph semantics,
and exhaustive closure are reused.
The reconciliation retains the newly landed `FrontierComposition` and
`GeneralPareto` checks. Finite pruning and transitivity adapt the existing
`FrontierComposition` owner, and the joint composition runner carries the new
registered controls into its temporary source tree.

## Reproduce

The joint receipt below is historical and can be replayed from optimality merge
`064852fb7a83c7a17950a78b77860175f95e1290`. Later updates to the joint dependency
are recorded separately in `composition/current/VERIFICATION.md`; they do not
change this receipt's source or dependency hashes.

Use the repository's `lean-toolchain` (Lean 4.19.0):

```sh
LEAN=/path/to/lean-4.19.0/bin/lean sh check.sh
LEAN=/path/to/lean-4.19.0/bin/lean python3 docs/covered-frontier/review.py
LEAN=/path/to/lean-4.19.0/bin/lean QUANTIFIABLE_SRC=/path/to/pinned/quantifiable sh composition/check.sh
```

`check.sh` includes the new positive/refusal controls, archived candidate proof,
and archive import assertions. `review.py` additionally requires deliberately
false coverage, tie-pruning, empty-contract, empty-replacement, tradeoff,
unknown-feasible-cost, and incomplete-premise claims to fail Lean checking. It
also checks that the existing runner rejects a proof escape and a compiler error.
The emitted `CHECK-RECEIPT.json` records source hashes, commands, exact outcomes,
toolchain, and the archived input identities. `PUBLISHER-CHECK.log` includes
theorems' logical dependencies; no custom assumptions or admitted proof escapes
are accepted by the runner. The usual Lean `propext`, `Quot.sound`, and, for the
existing classical incremental semantics, `Classical.choice` remain explicit.
`JOINT-RECEIPT.json` binds the successful cross-repository run and the existing
composition runner's content-pinned quantifiable dependency at commit
`61de9b7364e0a8c5ddc2ab8d0a633d2920aa38cf`. Its checked dependency is precisely the
root `SoftwareIsQuantifiable.lean` and the `Coloring`, `Coverage`, `Finiteness`,
`Fold`, and `Pareto` files named in `composition/quantifiable.sha256`. This run does
not cover later quantifiable commits or their new `Interface` and `Instance`
modules. On the optimality side, the full root and joint gates retain the
`Composition`, `OptimalityInterface`, and `CompositionCheck` owners at the pinned
base above, as well as `FrontierComposition` and `GeneralPareto`.
The joint runner retains
its pre-existing allowance for unused-variable diagnostics in upstream sources;
the owned optimality sources still compile with warnings as errors.

## Scope of the mathematical certificate

The general theorem preserves exactly the nondominated admitted identities of a
declared generator when the finite catalogue is sound and every omitted admitted
candidate has a strict admitted catalogue dominator. It does not assume the
generator finite or terminate an unsupported chain of omitted points. The
stronger feasible-generator theorem additionally requires qualification sound
and complete for an independently specified feasible predicate. The finite
checker rejects a feasible candidate with a missing measurement.

A frontier certificate alone can describe an empty frontier or retain an
incomparable tradeoff. The replacement certificate separately requires an
admitted named baseline in the domain, a retained chosen identity, no worse cost
on every declared axis, and strict improvement on at least one axis. Its feasible
form additionally checks qualification completeness.

The executable closure adapter is a reference computation of full-premise
qualification and exact admitted-domain frontier membership. The logical
incremental theorem proves agreement with full recomputation after additions or
withdrawals. Neither result claims an efficient incremental runtime. Projection
correctness, authenticated raw observations, current physical authority, metric
meaning, and the feasibility/coverage premises remain external obligations.
An arbitrary projector or a feasible predicate defined from missing receipts does
not establish those obligations.

## Existing concrete campaign

The concrete case uses the unchanged archived O1/O2/R2 campaign. O1 is the named
baseline; O2 is the recorded selected alternative; R2 is the actually executed
reverse-order alternative. All three are included in the declared candidate type
and catalogue. The objective remains **maximum observed end-to-end wall time in
nanoseconds over the three prescribed rounds**, with no added resource/quality
axis. Worker allocation remains metadata subject to the existing capacity gate.
The hard timing rule permits no increase against O1 in any paired round.

The archive Git blob is `d74b58fe93dd9454a1feae8aff6035d8872c6b99` at the pinned
base. The report SHA-256 is
`037ce2972cbf5bb72de79e24e3c914b4254406a488696a5e4e9f7b00eff50b73`; the policy
SHA-256 is `44faa39b813fe8ff0571957fa2f535d2d6d022ebd765cf8c0d95296ef5d40416`.
The verification receipt records the archive SHA-256 and exact values recovered
from it. `ArchiveImport.lean` is checked against the pinned JSON and proves the
existing Lean times, caps, receipt flags, worker allocations, admission bits, and
objective values agree. `Campaign.lean` proves coverage of that recorded candidate
type, exact frontier membership, and the named replacement with paired-round
nonregression.

This is replay of imported historical measurements over four pinned upstream
test subsets on one recorded host. It is not a new experiment, a proof of future
timing distributions, a universal semantic-equivalence proof, an authenticated
hypergraph importer, or a Pareto certificate for Idol. The separate synthetic
topology controls are rejection tests and do not contribute measured costs.
