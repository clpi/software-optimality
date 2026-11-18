# Portable adapter model bridge (Lean 4.19.0)

This is a checked executable model of the portable pipeline adapter boundary,
not a proof of the Python implementation, JSON parser, SHA-256 or operating system.

## Input boundary

`Authority` is fixed outside the submitted receipts. It contains the exact six
context fields (artifact, lineage, environment, harness, workload, venue), its
identity digest, and subject-to-atom maps. These are selected policy inputs, not
facts authenticated by this module. Receipts retain the six context fields,
classification, subject, typed payload, raw-source digest, record index, authority
digest and receipt ID. Parser prerequisites are valid schema, nonempty identities,
canonical source/authority/receipt hash checks, integer validation and conflicting
receipt-ID rejection. The model intentionally has no hash injectivity assumption:
no theorem here establishes that SHA-256 binds those fields.

Withdrawal identifiers are an authoritative snapshot input, not untrusted events.
Their authorization and reference validation occur before this model. A withdrawal
removes exactly the matching receipt's current support; it does not erase history.

## Checked conclusions

- `normalize_exact`: executable filtered/deduplicated receipts coincide with
  source membership plus exact context/authority/observed-origin checks and absence
  of a receipt-ID tombstone.
- `supports_exact`: executable `filterMap` extraction coincides with the declarative
  support meaning. Full receipts accompany atoms, preserving provenance.
- Exact context and authority identity are retained; cross-lineage receipts and
  inferred/proposed records cannot become observations.
- Pass and fail statuses use separately supplied authority maps. Skipped/error
  records and empty measurements emit no support. A nonempty measurement can emit
  only `measurement:<subject>`, never a raw faster-than/performance claim.
- Duplicate deliveries are extensionally idempotent; raw receipt merge commutes
  and distributes over support union **at a common fixed authority/withdrawal
  snapshot**. List presentation order is not claimed canonical.
- Additional withdrawal IDs only remove supports. Conjunctive hyperedge proofs
  require all premises. Derivations are preserved under added roots with unchanged
  edges, and withdrawal-derived conclusions form a subset of the previous closure.
  A withdrawn origin need not remove a conclusion with another valid derivation.

`supports_exact` is an algorithm-to-semantics theorem over normalized typed input,
not merely an assertion that an output equals itself. However the atom-map
semantics are policy inputs: no theorem certifies that a test is an oracle for all
behavior or that measurement samples predict future performance.

## Composition boundaries

The edges in `Derives` are fixed authoritative inference rules. The pipeline must
scope them to the same context and must justify their domain semantics separately.
This file does not prove rule soundness, complete closure enumeration, equality
saturation, schedule optimality, caller identity, canonical bytes or a compiler
translation. Python model correspondence remains a tested bridge, not a formal
refinement proof. Do not promote independently validated model proofs to whole-
pipeline verification. Merge receipt history and withdrawals before recomputing;
union of stale normalized views can resurrect withdrawn support.

## Checks

Run `./check.sh` with Lean 4.19.0 (override `LEAN` if necessary). It scans
for proof-admission tokens before compilation, removes the cached module, compiles
with warnings as errors, and runs 21 kernel-evaluated guards plus one derivation
example. Every one of the 15 named theorems has a printed dependency list audited
against the Lean foundational-axiom allowlist. The current proofs use only
`propext` and `Quot.sound` (one theorem has no axioms).

The same gate is exercised on five disposable deliberately corrupted copies:
injected `sorry`, a custom axiom declaration, a false proof by `decide`, removing
the exact context check, and promoting proposed classification. All five are
rejected, and the checker fails if any is accepted. Token controls must fail at
preflight; semantic controls must produce a Lean error. These are executed controls,
not suggestions for future validation. They do not establish Python refinement.
