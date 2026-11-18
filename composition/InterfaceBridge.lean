import SoftwareIsQuantifiable.Interface
import SoftwareIsQuantifiable.Pareto
import CanonicalDominance
import FrontierComposition

/- Adapter of the pinned public profile interface to the existing identity-based
   frontier certificates. Candidate identities are not replaced by profiles:
   different candidates with equal profiles remain different frontier members.
   These theorems compare supplied profiles. Qualification, physical observation,
   completeness of a search domain, and profile-to-contract alignment are separate
   obligations, as in the scoped feasible-generator certificate. -/
namespace InterfaceBridge
open SoftwareIsQuantifiable

variable {C Symbol Measure : Type} [DecidableEq Symbol]

def dominates (space : Interface.MeasureSpace Measure)
    (profile : C → Interface.Profile Symbol Measure) (a b : C) : Bool :=
  decide (Interface.dominates space (profile a) (profile b))

theorem dominates_exact (space : Interface.MeasureSpace Measure)
    (profile : C → Interface.Profile Symbol Measure) (a b : C) :
    dominates space profile a b = true ↔
      Interface.dominates space (profile a) (profile b) := by
  simp [dominates]

theorem dominates_transitive (space : Interface.MeasureSpace Measure)
    (profile : C → Interface.Profile Symbol Measure) :
    FrontierComposition.Transitive (dominates space profile) := by
  intro a b c hab hbc
  exact (dominates_exact space profile a c).mpr
    (Interface.dominates_trans
      ((dominates_exact space profile a b).mp hab)
      ((dominates_exact space profile b c).mp hbc))

theorem dominates_irreflexive (space : Interface.MeasureSpace Measure)
    (profile : C → Interface.Profile Symbol Measure) (a : C) :
    dominates space profile a a = false := by
  simp [dominates, Interface.not_dominates_self]

theorem frontier_exact (space : Interface.MeasureSpace Measure)
    (profile : C → Interface.Profile Symbol Measure) (catalogue : List C) (a : C) :
    a ∈ FiniteFrontier.frontier catalogue (dominates space profile) ↔
      a ∈ catalogue ∧ ∀ b ∈ catalogue,
        ¬ Interface.dominates space (profile b) (profile a) := by
  simp [FiniteFrontier.frontier_exact, dominates]

/-- A subset preserves exactly the frontier identities iff each omitted identity
    has a retained strict dominator. The public profile order supplies the laws;
    the existing generic certificate supplies the pruning decision. -/
theorem cover_exact [DecidableEq C] (space : Interface.MeasureSpace Measure)
    (profile : C → Interface.Profile Symbol Measure) (catalogue retained : List C)
    (subset : ∀ a ∈ retained, a ∈ catalogue) :
    FrontierComposition.checkCover (dominates space profile) catalogue retained = true ↔
      ∀ a, a ∈ FiniteFrontier.frontier catalogue (dominates space profile) ↔
        a ∈ FiniteFrontier.frontier retained (dominates space profile) :=
  FrontierComposition.checkCover_iff_same_frontier (dominates space profile)
    (dominates_transitive space profile) (dominates_irreflexive space profile)
    catalogue retained subset

/-- The final certificate is sound and complete for exact identity membership
    under this supplied profile relation, including tied and incomparable IDs. -/
theorem certificate_exact [DecidableEq C] (space : Interface.MeasureSpace Measure)
    (profile : C → Interface.Profile Symbol Measure) (catalogue retained : List C) :
    FiniteFrontier.certificate catalogue retained (dominates space profile) = true ↔
      ∀ a, a ∈ retained ↔ a ∈ catalogue ∧ ∀ b ∈ catalogue,
        ¬ Interface.dominates space (profile b) (profile a) := by
  rw [FrontierComposition.certificate_iff_frontier (dominates space profile)
    (dominates_transitive space profile) (dominates_irreflexive space profile)]
  simp only [frontier_exact]

/-- Match the current public frontier's explicit shape admission. This is a
    structural check only; it does not establish measurement truth or feasibility. -/
def alignedCatalogue (space : Interface.MeasureSpace Measure)
    (profile : C → Interface.Profile Symbol Measure) (catalogue : List C) : List C :=
  catalogue.filter (fun a => decide (Interface.aligned space (profile a)))

theorem aligned_frontier_exact (space : Interface.MeasureSpace Measure)
    (profile : C → Interface.Profile Symbol Measure) (catalogue : List C) (a : C) :
    a ∈ FiniteFrontier.frontier (alignedCatalogue space profile catalogue)
        (dominates space profile) ↔
      a ∈ catalogue ∧ Interface.aligned space (profile a) ∧ ∀ b ∈ catalogue,
        ¬ Interface.dominates space (profile b) (profile a) := by
  rw [frontier_exact]
  simp only [alignedCatalogue, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨ha, aligned⟩, hn⟩
    refine ⟨ha, aligned, ?_⟩
    intro b hb hd
    have fits := Interface.measuresLe_aligned hd.1.1
    exact hn b ⟨hb, fits.1⟩ hd
  · rintro ⟨ha, aligned, hn⟩
    exact ⟨⟨ha, aligned⟩, fun b hb => hn b hb.1⟩

/-- The public profile frontier and private identity frontier agree after the
    same alignment admission. Mapping may merge equal profiles; the identity
    membership on the left still retains every distinct candidate ID. -/
theorem public_frontier_agrees (space : Interface.MeasureSpace Measure)
    (profile : C → Interface.Profile Symbol Measure) (catalogue : List C) (a : C) :
    a ∈ FiniteFrontier.frontier (alignedCatalogue space profile catalogue)
        (dominates space profile) ↔
      a ∈ catalogue ∧ profile a ∈ Interface.frontier space (catalogue.map profile) := by
  rw [aligned_frontier_exact, Interface.frontier_exact]
  constructor
  · rintro ⟨ha, aligned, hn⟩
    refine ⟨ha, List.mem_map.mpr ⟨a, ha, rfl⟩, aligned, ?_⟩
    intro q hq
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hq
    exact hn b hb
  · rintro ⟨ha, _, aligned, hn⟩
    exact ⟨ha, aligned, fun b hb => hn (profile b) (List.mem_map.mpr ⟨b, hb, rfl⟩)⟩

theorem aligned_certificate_exact [DecidableEq C] (space : Interface.MeasureSpace Measure)
    (profile : C → Interface.Profile Symbol Measure) (catalogue retained : List C) :
    FiniteFrontier.certificate (alignedCatalogue space profile catalogue) retained
        (dominates space profile) = true ↔
      ∀ a, a ∈ retained ↔
        a ∈ catalogue ∧ profile a ∈ Interface.frontier space (catalogue.map profile) := by
  rw [FrontierComposition.certificate_iff_frontier (dominates space profile)
    (dominates_transitive space profile) (dominates_irreflexive space profile)]
  simp only [public_frontier_agrees]

/-- Existing two-axis optimality and the public stable profile interface use
    the same componentwise no-worse plus at-least-one-strict relation. -/
theorem two_axis_agrees (a b : Optimality.Point) :
    Optimality.dominates a b ↔
      Interface.dominates Pareto.costSpace (Pareto.profileOf a) (Pareto.profileOf b) :=
  CanonicalDominance.Optimality.local_dominates_iff_canonical a b

#print axioms dominates_transitive
#print axioms cover_exact
#print axioms certificate_exact
#print axioms public_frontier_agrees
#print axioms aligned_certificate_exact
#print axioms two_axis_agrees
end InterfaceBridge
