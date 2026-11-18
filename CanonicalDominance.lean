import SoftwareIsQuantifiable.Interface
import SoftwareIsQuantifiable.Pareto
import FiniteFrontier
import OptimalityInterface
import HypergraphIncremental
import EligibleCampaign
import ForeignCampaign
import ComparisonContract
import ScopedFrontier

open SoftwareIsQuantifiable

namespace CanonicalDominance

def oneSpace : Interface.MeasureSpace Unit :=
  [{ measure := (), polarity := .minimize }]

def oneProfile (n : Nat) : Interface.Profile Unit Unit where
  symbol := ()
  readings := [n]
  observed := true

theorem one_iff (m n : Nat) :
    m < n ↔ Interface.dominates oneSpace (oneProfile m) (oneProfile n) := by
  unfold Interface.dominates Interface.noWorse Interface.measuresLe Interface.strictlyBetter
    Interface.behaviorLe oneProfile oneSpace Interface.axesLe Interface.axesLt
    Interface.axisLe Interface.axisLt
  constructor
  · intro h
    exact ⟨⟨⟨rfl, ⟨Nat.le_of_lt h, trivial⟩⟩, fun _ => rfl⟩, Or.inl ⟨h, trivial⟩⟩
  · intro h
    rcases h.2 with ⟨hlt, _⟩ | ⟨_, hfalse⟩
    · exact hlt
    · exact False.elim hfalse

theorem one_releaseLe_iff (m n : Nat) :
    Interface.releaseLe oneSpace [oneProfile m] [oneProfile n] ↔
      Interface.noWorse oneSpace (oneProfile m) (oneProfile n) := by
  constructor
  · intro h
    obtain ⟨p, hp, hnw⟩ := h.2.2.2.2 (oneProfile n) (List.mem_singleton_self _)
    simp only [List.mem_singleton] at hp
    subst p
    exact hnw
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [Interface.uniqueSymbols]
    · simp [Interface.uniqueSymbols]
    · intro p hp
      simp only [List.mem_singleton] at hp
      subst p
      rfl
    · intro q hq
      simp only [List.mem_singleton] at hq
      subst q
      rfl
    · intro q hq
      simp only [List.mem_singleton] at hq
      subst q
      exact ⟨oneProfile m, List.mem_singleton_self _, h⟩

theorem one_release_iff (m n : Nat) :
    Interface.releaseDominates oneSpace [oneProfile m] [oneProfile n] ↔
      Interface.dominates oneSpace (oneProfile m) (oneProfile n) := by
  constructor
  · intro h
    obtain ⟨q, hq, p, hp, hdom⟩ := h.2
    simp only [List.mem_singleton] at hq hp
    subst q
    subst p
    exact hdom
  · intro h
    refine ⟨(one_releaseLe_iff m n).mpr h.1, ?_⟩
    exact ⟨oneProfile n, List.mem_singleton_self _, oneProfile m, List.mem_singleton_self _, h⟩

namespace Pareto

theorem local_dominates_iff_canonical (a b : SoftwareIsQuantifiable.Pareto.Point) :
    SoftwareIsQuantifiable.Pareto.dominates a b ↔
      Interface.dominates SoftwareIsQuantifiable.Pareto.costSpace
        (SoftwareIsQuantifiable.Pareto.profileOf a)
        (SoftwareIsQuantifiable.Pareto.profileOf b) :=
  SoftwareIsQuantifiable.Pareto.dominates_iff_interface a b

theorem local_noWorse_iff_canonical (a b : SoftwareIsQuantifiable.Pareto.Point) :
    SoftwareIsQuantifiable.Pareto.noWorse a b ↔
      Interface.noWorse SoftwareIsQuantifiable.Pareto.costSpace
        (SoftwareIsQuantifiable.Pareto.profileOf a)
        (SoftwareIsQuantifiable.Pareto.profileOf b) := by
  simp [SoftwareIsQuantifiable.Pareto.noWorse, Interface.noWorse, Interface.measuresLe,
    Interface.behaviorLe, SoftwareIsQuantifiable.Pareto.profileOf,
    SoftwareIsQuantifiable.Pareto.costSpace, Interface.axesLe, Interface.axisLe]

end Pareto

namespace Optimality

theorem local_dominates_iff_canonical (a b : Optimality.Point) :
    Optimality.dominates a b ↔
      Interface.dominates SoftwareIsQuantifiable.Pareto.costSpace
        (SoftwareIsQuantifiable.Pareto.profileOf a)
        (SoftwareIsQuantifiable.Pareto.profileOf b) := by
  rw [← Pareto.local_dominates_iff_canonical]
  simp [Optimality.dominates, SoftwareIsQuantifiable.Pareto.dominates]

theorem local_dominatesBool_iff_canonical (a b : Optimality.Point) :
    Optimality.dominatesBool a b = true ↔
      Interface.dominates SoftwareIsQuantifiable.Pareto.costSpace
        (SoftwareIsQuantifiable.Pareto.profileOf a)
        (SoftwareIsQuantifiable.Pareto.profileOf b) := by
  rw [Optimality.dominatesBool, decide_eq_true_eq, local_dominates_iff_canonical]

theorem local_noWorse_iff_canonical (a b : Optimality.Point) :
    Optimality.noWorse a b ↔
      Interface.noWorse SoftwareIsQuantifiable.Pareto.costSpace
        (SoftwareIsQuantifiable.Pareto.profileOf a)
        (SoftwareIsQuantifiable.Pareto.profileOf b) := by
  rw [← Pareto.local_noWorse_iff_canonical]
  simp [Optimality.noWorse, SoftwareIsQuantifiable.Pareto.noWorse]

theorem noWorse_needs_observed :
    Optimality.noWorse (0, 0) (1, 1) ∧
      ¬ Interface.noWorse SoftwareIsQuantifiable.Pareto.costSpace
        { SoftwareIsQuantifiable.Pareto.profileOf (0, 0) with observed := false }
        (SoftwareIsQuantifiable.Pareto.profileOf (1, 1)) := by
  refine ⟨⟨Nat.zero_le _, Nat.zero_le _⟩, ?_⟩
  intro h
  have := h.2 rfl
  cases this

end Optimality

namespace Eligible

def wall (c : EligibleCampaign.Candidate) : Nat :=
  (EligibleCampaign.times c).foldl max 0

theorem local_dominates_iff_canonical (y x : EligibleCampaign.Candidate) :
    EligibleCampaign.dominates y x = true ↔
      Interface.dominates oneSpace (oneProfile (wall y)) (oneProfile (wall x)) := by
  rw [EligibleCampaign.dominates, FiniteFrontier.pareto_exact, ← one_iff]
  constructor
  · intro h
    obtain ⟨i, hi, hlt⟩ := h.2
    simp only [List.mem_singleton] at hi
    subst i
    simpa [EligibleCampaign.cost, wall, Int.ofNat_lt] using hlt
  · intro h
    refine ⟨fun i hi => ?_, 0, by simp, ?_⟩
    · simp only [List.mem_singleton] at hi
      subst i
      simpa [EligibleCampaign.cost, wall, Int.ofNat_le] using Nat.le_of_lt h
    · simpa [EligibleCampaign.cost, wall, Int.ofNat_lt] using h

end Eligible

namespace Foreign

def makespan (qs : List (List Nat)) : Nat :=
  qs.foldl (fun m q => max m (ForeignCampaign.queueTime q)) 0

def flow (qs : List (List Nat)) : Nat :=
  (qs.map (ForeignCampaign.completionSum 0)).sum

theorem local_dominates_iff_canonical (y x : List (List Nat)) :
    ForeignCampaign.dominates y x = true ↔
      Interface.dominates SoftwareIsQuantifiable.Pareto.costSpace
        (SoftwareIsQuantifiable.Pareto.profileOf (makespan y, flow y))
        (SoftwareIsQuantifiable.Pareto.profileOf (makespan x, flow x)) := by
  rw [ForeignCampaign.dominates, FiniteFrontier.pareto_exact,
    ← SoftwareIsQuantifiable.Pareto.dominates_iff_interface]
  constructor
  · intro h
    have h0 : makespan y ≤ makespan x := by
      simpa [ForeignCampaign.cost, makespan, Int.ofNat_le] using h.1 0 (by simp)
    have h1 : flow y ≤ flow x := by
      simpa [ForeignCampaign.cost, flow, Int.ofNat_le] using h.1 1 (by simp)
    refine ⟨h0, h1, ?_⟩
    obtain ⟨i, hi, hlt⟩ := h.2
    have hi' : i = 0 ∨ i = 1 := by
      simpa [List.mem_cons, List.mem_nil_iff, or_false] using hi
    rcases hi' with rfl | rfl
    · exact Or.inl (by simpa [ForeignCampaign.cost, makespan, Int.ofNat_lt] using hlt)
    · exact Or.inr (by simpa [ForeignCampaign.cost, flow, Int.ofNat_lt] using hlt)
  · intro h
    refine ⟨?_, ?_⟩
    · intro i hi
      have hi' : i = 0 ∨ i = 1 := by
        simpa [List.mem_cons, List.mem_nil_iff, or_false] using hi
      rcases hi' with rfl | rfl
      · simpa [ForeignCampaign.cost, makespan, Int.ofNat_le] using h.1
      · simpa [ForeignCampaign.cost, flow, Int.ofNat_le] using h.2.1
    · rcases h.2.2 with hlt | hlt
      · exact ⟨0, by simp, by simpa [ForeignCampaign.cost, makespan, Int.ofNat_lt] using hlt⟩
      · exact ⟨1, by simp, by simpa [ForeignCampaign.cost, flow, Int.ofNat_lt] using hlt⟩

end Foreign

namespace Hypergraph

theorem local_dominates_iff_canonical (a b : Nat) :
    HypergraphIncremental.dominates ⟨true, [Int.ofNat a]⟩ ⟨true, [Int.ofNat b]⟩ = true ↔
      Interface.dominates oneSpace (oneProfile a) (oneProfile b) := by
  rw [← one_iff]
  simp [HypergraphIncremental.dominates, List.zip, List.all_cons, List.all_nil,
    List.any_cons, List.any_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq,
    Int.ofNat_le, Int.ofNat_lt]
  exact fun hlt => Nat.le_of_lt hlt

theorem refines_canonical (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : HypergraphIncremental.dominates ⟨true, [a]⟩ ⟨true, [b]⟩ = true) :
    Interface.dominates oneSpace (oneProfile a.toNat) (oneProfile b.toNat) := by
  rw [← Int.toNat_of_nonneg ha, ← Int.toNat_of_nonneg hb] at h
  exact (local_dominates_iff_canonical a.toNat b.toNat).mp h

theorem counterexample_eligible :
    let faster : HypergraphIncremental.Profile := ⟨false, [0]⟩
    let slower : HypergraphIncremental.Profile := ⟨true, [1]⟩
    HypergraphIncremental.dominates faster slower = false ∧
      Interface.dominates oneSpace (oneProfile 0) (oneProfile 1) := by
  decide

theorem negative_not_canonical :
    HypergraphIncremental.dominates ⟨true, [-1]⟩ ⟨true, [0]⟩ = true ∧
      ¬ Interface.dominates oneSpace (oneProfile ((-1).toNat)) (oneProfile 0) := by
  decide

end Hypergraph

namespace Comparison

def axisMin : ComparisonContract.Axis := ⟨0, 0, .minimize, 0⟩

def contractMin : ComparisonContract.Contract := ⟨[axisMin], 0, 0, 0⟩

theorem local_dominates_iff_canonical (x y : Nat) :
    ComparisonContract.dominates contractMin [Int.ofNat x] [Int.ofNat y] = true ↔
      Interface.dominates oneSpace (oneProfile x) (oneProfile y) := by
  rw [ComparisonContract.dominates, FiniteFrontier.pareto_exact, ← one_iff]
  simp [ComparisonContract.cost, ComparisonContract.normalize, contractMin, axisMin,
    List.range_succ, List.mem_singleton, Int.ofNat_le, Int.ofNat_lt]
  exact fun hlt => Nat.le_of_lt hlt

theorem negative_not_canonical :
    ComparisonContract.dominates contractMin [-1] [0] = true ∧
      ¬ Interface.dominates oneSpace (oneProfile ((-1).toNat)) (oneProfile 0) := by
  decide

def axisMax : ComparisonContract.Axis := ⟨0, 0, .maximize, 0⟩

def contractMax : ComparisonContract.Contract := ⟨[axisMax], 0, 0, 0⟩

theorem maximize_not_raw :
    ComparisonContract.dominates contractMax [1] [0] = true ∧
      ¬ Interface.dominates oneSpace (oneProfile 1) (oneProfile 0) := by
  decide

end Comparison

namespace Scoped

def metric : ScopedFrontier.Metric := ⟨0, 1⟩

def axis : ScopedFrontier.Axis := ⟨0, 0, true⟩

def obligation : ScopedFrontier.Obligation := ⟨0, 0, 100⟩

def contract : ScopedFrontier.Contract :=
  ⟨0, 0, 0, 0, 0, 0, [metric], [obligation], [axis]⟩

def subject (configuration : Nat) : ScopedFrontier.Subject := ⟨0, configuration, 0⟩

def scopeAt (configuration : Nat) : ScopedEvidence.Scope :=
  ScopedFrontier.expectedScope contract (subject configuration) 0

def input (s : ScopedFrontier.Subject) : ScopedFrontier.Input :=
  ⟨contract, [⟨0, scopeAt s.configuration, 0, true, some (s.configuration + 1)⟩]⟩

def small : ScopedFrontier.Subject := subject 0

def large : ScopedFrontier.Subject := subject 1

def axisMin : ScopedFrontier.Axis := ⟨0, 0, false⟩

def contractMin : ScopedFrontier.Contract :=
  ⟨0, 0, 0, 0, 0, 0, [metric], [obligation], [axisMin]⟩

def inputMin (s : ScopedFrontier.Subject) : ScopedFrontier.Input :=
  ⟨contractMin, [⟨0, ScopedFrontier.expectedScope contractMin (subject s.configuration) 0,
      0, true, some (s.configuration + 1)⟩]⟩

theorem minimize_iff_canonical :
    ScopedFrontier.dominates contractMin inputMin small large = true ↔
      Interface.dominates oneSpace (oneProfile 1) (oneProfile 2) := by
  decide

theorem maximize_not_minimize :
    ScopedFrontier.dominates contract input large small = true ∧
      ¬ Interface.dominates oneSpace
        (oneProfile ((ScopedFrontier.coordinate axis
          (ScopedFrontier.expectedPolicy contract large) (input large).receipts).getD 0))
        (oneProfile ((ScopedFrontier.coordinate axis
          (ScopedFrontier.expectedPolicy contract small) (input small).receipts).getD 0)) := by
  decide

end Scoped

#print axioms one_iff
#print axioms one_releaseLe_iff
#print axioms one_release_iff
#print axioms Pareto.local_dominates_iff_canonical
#print axioms Pareto.local_noWorse_iff_canonical
#print axioms Optimality.local_dominates_iff_canonical
#print axioms Optimality.local_dominatesBool_iff_canonical
#print axioms Optimality.local_noWorse_iff_canonical
#print axioms Optimality.noWorse_needs_observed
#print axioms Eligible.local_dominates_iff_canonical
#print axioms Foreign.local_dominates_iff_canonical
#print axioms Hypergraph.local_dominates_iff_canonical
#print axioms Hypergraph.refines_canonical
#print axioms Hypergraph.counterexample_eligible
#print axioms Hypergraph.negative_not_canonical
#print axioms Comparison.local_dominates_iff_canonical
#print axioms Comparison.negative_not_canonical
#print axioms Comparison.maximize_not_raw
#print axioms Scoped.minimize_iff_canonical
#print axioms Scoped.maximize_not_minimize

end CanonicalDominance
