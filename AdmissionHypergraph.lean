import Admission
import HypergraphIncremental
namespace AdmissionHypergraph
open Admission

-- Decoders are views on the same admitted receipts, not a second source of
-- authority. They must retain scope or require checked transfer certificates.
structure Decoder (A : Type) where
  root : Key → Payload → A → Prop
  edge : Key → Payload → List A → A → Prop

def graph {A : Type} (d : Decoder A) (authorize : Event → Bool) (ledger : List Event) :
    HypergraphIncremental.Hypergraph A where
  roots a := ∃ k p, live authorize ledger k p ∧ d.root k p a
  edges ps a := ∃ k p, live authorize ledger k p ∧ d.edge k p ps a

theorem normalized_graph_same {A : Type} (d : Decoder A)
    (auth₁ auth₂ : Event → Bool) (xs ys : List Event)
    (same : ∀ e, admitted auth₁ xs e ↔ admitted auth₂ ys e) :
    (∀ a, (graph d auth₁ xs).roots a ↔ (graph d auth₂ ys).roots a) ∧
    (∀ ps a, (graph d auth₁ xs).edges ps a ↔ (graph d auth₂ ys).edges ps a) := by
  constructor
  · intro a
    simp only [graph]
    constructor
    · rintro ⟨k,p,hl,hd⟩
      exact ⟨k,p,(admitted_extensional auth₁ auth₂ xs ys same k p).mp hl,hd⟩
    · rintro ⟨k,p,hl,hd⟩
      exact ⟨k,p,(admitted_extensional auth₁ auth₂ xs ys same k p).mpr hl,hd⟩
  · intro ps a
    simp only [graph]
    constructor
    · rintro ⟨k,p,hl,hd⟩
      exact ⟨k,p,(admitted_extensional auth₁ auth₂ xs ys same k p).mp hl,hd⟩
    · rintro ⟨k,p,hl,hd⟩
      exact ⟨k,p,(admitted_extensional auth₁ auth₂ xs ys same k p).mpr hl,hd⟩

theorem qualification_same {A : Type} (d : Decoder A)
    (auth₁ auth₂ : Event → Bool) (xs ys : List Event)
    (same : ∀ e, admitted auth₁ xs e ↔ admitted auth₂ ys e) (a : A) :
    HypergraphIncremental.derives (graph d auth₁ xs) a ↔
    HypergraphIncremental.derives (graph d auth₂ ys) a := by
  have h := normalized_graph_same d auth₁ auth₂ xs ys same
  constructor
  · exact Qualification.monotone (fun x => (h.1 x).mp) (fun ps x => (h.2 ps x).mp) a
  · exact Qualification.monotone (fun x => (h.1 x).mpr) (fun ps x => (h.2 ps x).mpr) a

-- Duplicate event delivery cannot strengthen any derived qualification, even
-- when the duplicated receipt encoded an inference/transfer hyperedge.
theorem replay_idempotent {A : Type} (d : Decoder A) (auth : Event → Bool)
    (xs : List Event) (a : A) :
    HypergraphIncremental.derives (graph d auth (xs ++ xs)) a ↔
    HypergraphIncremental.derives (graph d auth xs) a := by
  apply qualification_same
  intro e
  simp [admitted]

theorem merge_order_independent {A : Type} (d : Decoder A) (auth : Event → Bool)
    (xs ys : List Event) (a : A) :
    HypergraphIncremental.derives (graph d auth (xs ++ ys)) a ↔
    HypergraphIncremental.derives (graph d auth (ys ++ xs)) a := by
  apply qualification_same
  intro e
  simp [admitted, or_comm]

-- Recommended scope-safe construction: roots retain the entire exact key and
-- payload. Cross-lineage conclusions require explicit admitted hyperedges.
abbrev ScopedAtom := Key × Payload

def scopedGraph (edge : Key → Payload → List ScopedAtom → ScopedAtom → Prop)
    (auth : Event → Bool) (ledger : List Event) : HypergraphIncremental.Hypergraph ScopedAtom :=
  graph ⟨fun k p a => a = (k,p), edge⟩ auth ledger

theorem scoped_root_exact (edge : Key → Payload → List ScopedAtom → ScopedAtom → Prop)
    (auth : Event → Bool) (ledger : List Event) (k : Key) (p : Payload) :
    (scopedGraph edge auth ledger).roots (k,p) ↔ live auth ledger k p := by
  simp only [scopedGraph, graph]
  constructor
  · rintro ⟨k',p',hl,he⟩
    cases he
    exact hl
  · intro h
    exact ⟨k,p,h,rfl⟩

-- Absent live roots in a lineage, it cannot acquire qualification merely from
-- shared content. A transfer (or a zero-premise grant) into that lineage must
-- actually be present among the admitted edges to evade this theorem's premise.
theorem lineage_isolation
    (edge : Key → Payload → List ScopedAtom → ScopedAtom → Prop)
    (auth : Event → Bool) (ledger : List Event) (lineage : Nat)
    (noRoots : ∀ k p, k.lineage = lineage → ¬ live auth ledger k p)
    (noEntering : ∀ ps a, (scopedGraph edge auth ledger).edges ps a →
      a.1.lineage = lineage → ∃ p ∈ ps, p.1.lineage = lineage) :
    ∀ a, HypergraphIncremental.derives (scopedGraph edge auth ledger) a →
      a.1.lineage ≠ lineage := by
  apply Qualification.least
  · intro a h ha
    exact noRoots a.1 a.2 ha ((scoped_root_exact edge auth ledger a.1 a.2).mp h)
  · intro ps a he hp ha
    obtain ⟨p,hm,hl⟩ := noEntering ps a he ha
    exact hp p hm hl

#print axioms scoped_root_exact
#print axioms lineage_isolation
#print axioms qualification_same
#print axioms replay_idempotent
#print axioms merge_order_independent
end AdmissionHypergraph
