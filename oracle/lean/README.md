# Lean compatibility and native improvement: owner handoff

This is a noncompeting, read-only owner inventory plus upstream oracle slice.
It is NOT an Idol implementation, a passed Idol differential test or a parity
certificate. No kernel, tokenizer, graph or realization owner has been edited.

## Snapshot and correction

Inspected clpi/idol main `107e52a970c437bd6a7aae44101df271d87c9120`,
`lib/lean/kernel.id`, `gate/composable.id`, root AGENTS and coordination map.
Existing owners are PR #2325 (merged export-cone checker), #2339 (honest refusal
labels), and #2344 (direct text table realization correction). The active lease
is not discoverable from repository files: coordination explicitly says use the
shared checkout's claim tool. No new live claim or outside-agent contact made.

#2339 reports a binder-context omission in `defeq` at `eq_of_heq`. Its suggestion
that a correction corrupts the heap is superseded by #2344's narrower diagnosis:
the string-table value was loaded in range but misclassified as an integer for
formatting; a typed read still recovered the characters. Do not cite confirmed
heap corruption. Do not infer from the string-table gate passing that the full
Lean cone or its mutant passes: those need their own checked outcomes.

The inspected kernel consumes pinned NDJSON export data, uses integer-kind tables,
and only authorizes three named axioms. That is not evidence of full `.lean`
source/workflow compatibility or canonical hypergraph integration per invocation.

## Three separate contracts (not three authorities)

**Compatibility/replay.** Pin Lean version/commit, dependency closure, toolchain,
options, source inputs, generated artifacts, plugin/runtime inputs and declared
observable protocol. Preserve accepted/rejected/error/admitted distinctions,
messages where contractually observable, elaborated names/types/bodies/universes,
axiom dependencies, and executable outcomes. For original `.lean` source or an
Idol-file replay, the identical named contract is checked. Reconstructing a term
from an export does not reproduce a macro, tactic, extension or IO side effect.
A source-level replay record must bind such effects or explicitly refuse replay.

**Backward compatibility.** Cover Lean CLI, imports/module environment, libraries,
Lake project/build/package behavior, extension APIs, editor/server protocol,
compiled/runtime/FFI behavior and artifact interoperability as separately named
surfaces. Dependency/version migration must not silently change definitions or
options. User-defined tactics/macros/plugins cannot disappear because a selected
kernel cone does not exercise them. `.olean` byte identity and logical import
interoperability are different requirements; declare which is required.

**Native improvement.** Use the same canonical Idol semantic graph as authority,
with compatibility a projection. Prove preservation on a specifically certified
subset and named observables, then separately measure chosen costs against a
pinned upstream oracle. A subset win neither establishes total compatibility nor
strict improvement on all axes. Preserve all ties on the certified frontier;
compare only matching workloads, venues, versions and resource policies. No
foreign prover may remain hidden as the production decision authority.

## Versioned upstream surface inventory

Primary executable evidence: Lean 4.19.0, commit
`6caaee842e9495688c1567e78c0e68dbb96942aa`; local binary SHA256
`92c3d35b5bfaa5e0fea413a775d504cf46cd95e1345df61c2274f76779e7e023`.
Sources in that release's `src/lean/Lean/` and CLI `--help` were inspected.
No row below is an achieved Idol parity claim.

| Surface | Existing evidence / outstanding conformance gate |
|---|---|
| Kernel levels and expressions | Export-cone implementation reports levels, binders, application, let, constants, sorts, recursors, projection, eta and natural literals. Exercise each constructor independently and under nested dependent binders; compare reduction and inferred type, not a pass label alone. |
| Declaration forms | Upstream `Declaration.lean` includes axiom, definition, theorem, opaque, quotient, mutual definition and inductive declarations. Must validate all metadata and reject malformed export references/types, not skip unknown fields. |
| Definitional equality | Check beta/zeta/iota/delta/eta, proof irrelevance, quotients, universe instantiation, transparency/reducibility hints, nested dependent context, recursion and literals. #2339 blocker belongs here. |
| Axioms/admissions | Upstream accepts explicit custom axioms; ordinary `sorry` is accepted with warning and dependency `sorryAx`. A hardcoded axiom whitelist is a secure qualification policy, NOT upstream compatibility. Both verdicts must be recorded. |
| Parser/elaborator | `.lean` syntax, notation, precedence, binder elaboration, coercions, typeclass search, overloading, metavariables, constraints, macros, tactics, attributes, quotations and namespace/scoping. Export import alone does not exercise these. |
| Environment/modules | Import dependency closure, environment extensions, options, private/auxiliary declarations, initializers and artifact versioning; serialize and reload with exact meaning. |
| Compilation/runtime | `#eval`, `--run`, compiled executable, IO/exception/exit behavior, numeric/string/container behavior, code generation, unsafe/partial code and external calls. Kernel proof checking is not this contract. |
| CLI/diagnostics | Output channels, locations/ranges, severity, exit status, options/limits, dependencies, profiling/statistics, parallel mode, JSON messages. Compare contractual fields; do not invent timing determinism. |
| Tooling/build | Lake build/test/package graph, incremental invalidation, language server/worker/editor, plugins/dynamic libraries and ecosystem APIs. Independent compatibility faces must remain independently usable. |
| Trust/policy | Record axioms, unsafe/partial boundaries, native computation trust and replay completeness. Native execution results cannot silently be promoted to kernel proof. |
| Shared graph | Every invocation emits or references canonical typed facts with source/artifact/world/proof lineage. Checked replay ties compatibility projections to that graph. Derived views cannot replace it with a shadow solver graph. |

Current status is partial/not demonstrated for these complete surfaces. Some
constructor-specific code exists; presence in source is not a passing conformance
result. A full finite release API inventory can be version-pinned; comprehensive
behavior equivalence still needs the actual semantics/translation proof and
adversarial testing, not just matching inventory cardinalities.

## Executable upstream slice included here

Run `LEAN=/path/to/lean sh oracle.sh`. It pins the exact upstream commit and
records outcomes in `evidence/` for positive kernel examples, explicit axioms,
admitted proof in normal and warning-as-error modes, an invalid term, and program
runtime output. These files intentionally contain an explicit axiom and `sorry`
as negative-policy/positive-compatibility fixtures; they are not claimed proofs.

The next owner's Idol test must run the same fixtures through the actual source
compatibility face, capture the same declared fields and identify any difference.
For exported/replayed Idol files additionally compare canonical declaration
meaning and trace/source links before and after serialization. A genuine case
must be accepted before a mutant-rejection result is credited. Add independent
mutants for type, proof, universe parameter, recursor rule, axiom label/body,
projection index, missing declaration, duplicate/conflicting identity and graph
provenance; unsupported must never become accepted by omission.

## Gate and receipt design for existing owner

One invocation receipt should bind mode, exact Idol+upstream versions, input and
dependency roots, option/world/venue scope, canonical graph root, replay recipe,
source-to-graph links, oracle result, Idol result, qualification policy result,
proof/counterexample references, and separately measured costs. Source comments
and formatting need preservation only when the selected replay contract observes
them; don't pretend semantic round-trip equals byte round-trip.

Acceptance is a conjunction: source compatibility, graph/translation fidelity,
trusted-policy verdict, required workflow conformance, and selected optimization
certificate. Do not collapse unsupported, admitted, unknown, error, unsafe,
policy-refused and valid into one Boolean. Optimized/native mode can improve the
certified subset without changing strict mode's observable semantics.

For benchmark costs, include loading/lowering/graph construction, checking,
replay and cache policy when they are part of the declared invocation. Record raw
paired observations and overhead separately. A proof of operation-count reduction
is not a physical timing theorem. Shared compiler/backend corrections must land
through the existing owner and its correctness gates before timing.

## Next nonduplicating action

Owner of #2339/#2344 should first rerun the real cone and independently derived
mutants after the binder-context and text-table corrections, retaining honest
status. Then add this upstream slice to the version-pinned conformance corpus and
expand by surface. Source `.lean` entrypoint, canonical graph integration and
upstream workflow coverage are distinct unresolved owners, not solved by relabeling
export acceptance. This handoff does not create a competing tracker or kernel.

Sources: https://github.com/clpi/idol/pull/2325,
https://github.com/clpi/idol/pull/2339,
https://github.com/clpi/idol/pull/2344,
https://github.com/leanprover/lean4/tree/v4.19.0/src/Lean,
https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/,
https://lean-lang.org/doc/reference/latest/Axioms/.
The executable release pin, not moving `latest` documentation, defines this slice.
