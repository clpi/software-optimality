import composition.QualifiedSelection
import AdmissionHypergraph
import ComparisonContract

namespace LiveSelection
open Admission AdmissionHypergraph

structure Decoder (F : Type) where
  roots : Key × Payload → List F
  rules : Key × Payload → QualifiedClosure.Rules F

def Decoder.view (d : Decoder F) : AdmissionHypergraph.Decoder F where
  root k p a := a ∈ d.roots (k,p)
  edge k p ps a := (ps,a) ∈ d.rules (k,p)

private theorem normalized_members {A : Type} (decode : Key × Payload → List A)
    (auth : Event → Bool) (ledger : List Event) (x : A) :
    x ∈ (normalized auth ledger).flatMap decode ↔
    ∃ k p, live auth ledger k p ∧ x ∈ decode (k,p) := by
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨⟨k,p⟩,hk,hx⟩
    exact ⟨k,p,(normalized_exact ..).mp hk,hx⟩
  · rintro ⟨k,p,hk,hx⟩
    exact ⟨(k,p),(normalized_exact ..).mpr hk,hx⟩

theorem graph_agrees (d : Decoder F) (auth : Event → Bool) (ledger : List Event) (a : F) :
    let rows := normalized auth ledger
    HypergraphIncremental.derives (QualifiedClosure.graph (rows.flatMap d.roots) (rows.flatMap d.rules)) a ↔
    HypergraphIncremental.derives (AdmissionHypergraph.graph d.view auth ledger) a := by
  dsimp only
  constructor
  · exact Qualification.monotone (fun x => (normalized_members d.roots auth ledger x).mp)
      (fun ps x => (normalized_members d.rules auth ledger (ps,x)).mp) a
  · exact Qualification.monotone (fun x => (normalized_members d.roots auth ledger x).mpr)
      (fun ps x => (normalized_members d.rules auth ledger (ps,x)).mpr) a

def select [DecidableEq F] (d : Decoder F) (auth : Event → Bool) (ledger : List Event)
    (data : QualifiedSelection.Campaign C F) (u : List F) (catalogue : List C) (inc : C) :=
  let rows := normalized auth ledger
  QualifiedSelection.select data u (rows.flatMap d.roots) (rows.flatMap d.rules) catalogue inc

theorem selected_live [DecidableEq F] (d : Decoder F) (auth : Event → Bool) (ledger : List Event)
    (data : QualifiedSelection.Campaign C F) (u : List F) (catalogue out : List C) (inc c : C)
    (h : select d auth ledger data u catalogue inc = some out) (hc : c ∈ out) :
    ∀ b ∈ data.behaviors,
      HypergraphIncremental.derives (AdmissionHypergraph.graph d.view auth ledger) (data.supports c b) ∧
      ¬ HypergraphIncremental.derives (AdmissionHypergraph.graph d.view auth ledger) (data.refutes c b) := by
  let rows := normalized auth ledger
  let g := QualifiedClosure.graph (rows.flatMap d.roots) (rows.flatMap d.rules)
  obtain ⟨hp,hn,_⟩ := QualifiedSelection.release_evidence data u _ _ g catalogue out inc c h hc
  have eqv := fun f => (HypergraphIncremental.incremental_exact g g f).trans (graph_agrees d auth ledger f)
  intro b hb
  exact ⟨(eqv _).mp (hp _ (List.mem_map.mpr ⟨b,hb,rfl⟩)),
    fun he => hn _ (List.mem_map.mpr ⟨b,hb,rfl⟩) ((eqv _).mpr he)⟩

/-- Comparisons under a typed contract cover units, directions, aggregation,
    workload, venue and epoch. Values under a different contract first need
    an explicitly checked ComparisonContract.Transport. -/
theorem typed_cover_exact {A : Type} [DecidableEq A] (k : ComparisonContract.Contract)
    (obs : A → ComparisonContract.Observation k) (xs ys : List A) (hs : ∀ x ∈ ys, x ∈ xs) :
    let d := fun a b => ComparisonContract.dominates k (obs a).values (obs b).values
    FrontierComposition.checkCover d xs ys = true ↔ ∀ x,
      x ∈ FiniteFrontier.frontier xs d ↔ x ∈ FiniteFrontier.frontier ys d := by
  dsimp only
  apply FrontierComposition.checkCover_iff_same_frontier _ _ _ _ _ hs
  · intro a b c
    exact FrontierComposition.pareto_transitive (List.range k.axes.length) (ComparisonContract.cost k)
  · intro a
    exact FrontierComposition.pareto_irreflexive _ (ComparisonContract.cost k) (obs a).values

#print axioms graph_agrees
#print axioms selected_live
#print axioms typed_cover_exact
end LiveSelection
