# Hypergraph incremental proof scope

`HypergraphIncremental.lean`, Lean 4.19.0, extends the existing qualification proof.

## Proven

- One directed hypergraph is authoritative. Binary dependencies are a derived invalidation view; premise conjunction remains the inference rule. Incidence retains premise position versus head, and interactions retain their hyperedge and port roles.
- Affected closure includes changed root membership, changed edge membership (including empty-premise edges), and dependencies from both old and new hypergraphs.
- Reusing unaffected old derivations and reconstructing affected derivations from new roots and new affected-head rules equals a full least-derivation recomputation. Cycles have inductive/least support semantics; unsupported cycles cannot bootstrap after root withdrawal.
- This semantic incremental answer agrees with the existing executable exhaustive `ExecutableClosure.close` for admitted finite lists. This is not an implementation of a fast incremental worklist.
- Any deterministic profile projection of these qualifications gives the same frontier as projecting the full answer. An executable pair-update function and frontier filter equal fresh computation; withdrawn dominators resurrect retained candidates.
- A typed finite edge-record list carries receipt IDs. The semantic edge relation is derived existentially from currently live, kind-admitted records. Distinct records can support the same implication, so withdrawing one does not remove it while another remains.
- A finite matrix cell is a derived count of edge records matching kind and both port roles/positions. The retained-plus-added support count equals complete matrix regeneration. Boolean cells are count > 0. Tests cover two supports, removal of one, removal of all, replacement, changed kind and role/position.

## Not claimed

- No deployed ingestion, cryptographic authenticity checker, withdrawal authorization mechanism, or production incremental worklist is verified by this module.
- `Hypergraph`/`Affected` are proposition-level semantics. The exact closure theorem is not a performance bound. The affected region may include all atoms.
- Matrix update theorem recomputes support counts on retained records; it does not establish an optimized sparse-matrix cache implementation or complexity bound.
- Pair update computes the old dominance predicate when descriptors are unchanged; it is not a verified mutable cache/count data structure.
- Profile projection is supplied deterministically; the theorem does not validate how timings are measured, sampled, or predicted.
- Receipt IDs are exact Nat keys in this model. Unique assignment, scoped identity encoding, hash collision resistance, and construction of admitted edge kinds remain adapter obligations. The semantic relation intentionally collapses duplicate implications only AFTER live receipt selection.
- The relation has positive conjunctive inference. Nonmonotone qualification decisions can be deterministic projections AFTER closure; arbitrary recursive negation is not included.

No additional logical assumptions or admissions are introduced. Standard Lean logical dependencies are printed by the checker.
- `cellCount` counts list-record multiplicity, not distinct witness identities. A canonical authoritative receipt set must be deduplicated/admission-normalized before this view if unique-witness counts are intended. `editEdges` is the ordered operation remove-selected-old-records then append-added-records: it does not itself enforce ID freshness, withdrawal precedence, or an idempotent ledger join. Those are upstream live-snapshot admission obligations. Duplicate implication examples use DISTINCT receipt IDs.
