# Admission normalization: a prerequisite for compositional qualification

This implementation is a derived view on the same event records. It introduces
no independent graph, witness ledger, or source of authority.

## Executable construction

`Admission.lean` defines an exact `Key` containing lineage, content identity,
scope identity, and support identity. A payload names a subject, a support
polarity, and evidence identity. Numeric fields model already resolved typed
identities; they do not themselves verify Merkle membership or authenticity.

An authorization function is an explicit input, fixed for the named snapshot.
An event is admitted iff it occurs in the supplied event list AND that function
returns true. A support is live iff its claim is admitted, no withdrawal for
that exact key is admitted, and all admitted claims for that key agree on the
entire payload. Conflicting payloads quarantine that key; neither last-write-wins
nor arrival-order preference applies. A withdrawn key remains withdrawn. A
later reissue must have a fresh support identity, with its own admission.

`checkLive` is executable and proved equivalent to this predicate.
`normalized` extracts a duplicate-free list containing exactly the live keyed
payloads. The list is a SET REPRESENTATION: member content is canonical and
order independent; the output list's iteration order is not canonical byte
serialization. No canonical serialized Merkle root is claimed here.

## Machine-checked properties

- Same admitted events imply identical live support membership, even for two
  different authorizers whose admitted event sets coincide.
- Event permutation and branch merge order do not change live membership.
- Duplicate replay is idempotent; output supports have no duplicates.
- Each key has at most one live payload.
- An admitted withdrawal blocks its key and remains effective after append.
- An unauthorized event has no effect, including unauthorized withdrawals.
- Conflicting admitted payloads cannot both or individually qualify that key.
- `AdmissionHypergraph.lean` interprets both roots AND inference/transfer edges
  from these live supports in the existing `HypergraphIncremental.Hypergraph`.
  Equal admitted provenance implies identical root/edge relations and identical
  least qualification closure. Duplicate replay and merge-order invariance thus
  extend through all downstream inference, not merely the input table.

The generic decoder is a parameter; arbitrary external decoders are not proved
sound. The recommended `scopedGraph` instead fixes root interpretation to the
exact `(Key, Payload)` atom by construction. `scoped_root_exact` proves that no
root loses lineage/scope/payload. `lineage_isolation` proves that a lineage with
no live roots cannot acquire qualification unless an admitted hyperedge actually
enters it without an existing premise in that lineage. Explicit transfer or
zero-premise grant edges therefore remain necessary, not silently inferred from
shared content. Correctness of such a transfer's semantic justification is
still an admission obligation. Likewise authorization correctness, signature/hash
verification, evidence validity, benchmark comparability, and inference-rule
soundness remain external obligations. The bridge guarantees faithful use of
admitted provenance, not truth of a false admitted assertion.

## Counterexamples / regression controls

18 executable guards and 5 kernel-checked examples cover duplicate delivery,
conflicting payloads, both withdrawal/claim orderings, same-ID attempted
resurrection, authorized versus unauthorized withdrawal, fresh-ID reissue,
equal-content different-lineage isolation, differing-scope isolation, and a
counterexample to unioning normalized views. `[claim]` normalizes to one support,
`[withdraw]` to none, but their merged raw events normalize to none; unioning
the two normalized lists incorrectly retains a stale support.

Normalization is not monotone under event append. The underlying historical
event-set union is monotone, but its live projection can retract. For raw matrix
statistics based on receipt lists, use normalized supports FIRST to avoid
counting duplicate deliveries as independent corroboration. Distinct admitted
support IDs still represent distinct records; independence is not inferred.

## Reproducibility and costs

Run the integrated repository `./check.sh` using Lean 4.19.0. It compiles imported modules before admission modules, with warnings as errors and an admission scan. The publisher built in a separate directory from copied source; no old compiled admission dependencies were reused. Only standard Lean logical axioms printed by the checker are used; no custom axioms, proof holes, or native evaluation proof shortcuts. Original proof modules are unmodified. See VERIFICATION.md for independent controls.

This is a straightforward executable reference projection, not a performance
claim: candidate extraction/dedup and repeated live checks are quadratic in
receipt count in the worst case (identity equality costs excluded). A keyed
index can optimize it later against this exact reference semantics. No Pareto
optimality, cryptographic identity, production authorization service, or
benchmark speedup has been claimed or measured.
