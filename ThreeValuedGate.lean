import ComparisonContract
import SoftwareIsQuantifiable.Interface
import CanonicalDominance

open SoftwareIsQuantifiable

namespace ThreeValuedGate

inductive Verdict where
  | pass
  | fail
  | unknown
  deriving DecidableEq, Repr

def boolGate (ok : Bool) : Verdict :=
  if ok then .pass else .fail

def reading (xs : List (Option Int)) (i : Nat) : Option Int :=
  (xs[i]?).join

def axisVerdict (c : ComparisonContract.Contract) (x y : List (Option Int)) (i : Nat) : Verdict :=
  match c.axes[i]? with
  | none => .unknown
  | some axis =>
    match reading x i, reading y i with
    | some xv, some yv =>
      boolGate (decide (ComparisonContract.normalize axis.direction xv ≤
        ComparisonContract.normalize axis.direction yv))
    | _, _ => .unknown

def strictAxis (c : ComparisonContract.Contract) (x y : List (Option Int)) (i : Nat) : Prop :=
  match c.axes[i]?, reading x i, reading y i with
  | some axis, some xv, some yv =>
    ComparisonContract.normalize axis.direction xv <
      ComparisonContract.normalize axis.direction yv
  | _, _, _ => False

def dominates (c : ComparisonContract.Contract) (x y : List (Option Int)) : Prop :=
  (∀ i, i ∈ List.range c.axes.length → axisVerdict c x y i = .pass) ∧
  (∃ i, i ∈ List.range c.axes.length ∧ strictAxis c x y i)

def contractMin : ComparisonContract.Contract :=
  ⟨[⟨0, 0, .minimize, 0⟩], 0, 0, 0⟩

theorem absent_axis_admitted_by_two_valued_dominance :
    (([] : List Int)[0]? = none) ∧
      ComparisonContract.dominates contractMin [] [1] = true := by
  decide

theorem unknown_blocks_dominance
    (c : ComparisonContract.Contract) (x y : List (Option Int)) (i : Nat)
    (hi : i ∈ List.range c.axes.length)
    (hu : axisVerdict c x y i = .unknown)
    {Symbol Measure : Type}
    {space : Interface.MeasureSpace Measure}
    {p q : Interface.Profile Symbol Measure}
    (hm : ¬ Interface.aligned space p ∨ ¬ Interface.aligned space q) :
    ¬ dominates c x y ∧ ¬ Interface.dominates space p q := by
  constructor
  · intro h
    have hv := h.1 i hi
    rw [hu] at hv
    cases hv
  · intro hdom
    have hal := Interface.measuresLe_aligned hdom.1.1
    rcases hm with hp | hq
    · exact hp hal.1
    · exact hq hal.2

theorem known_agrees_canonical (a b : Nat) :
    dominates contractMin [some (Int.ofNat a)] [some (Int.ofNat b)] ↔
      Interface.dominates CanonicalDominance.oneSpace
        (CanonicalDominance.oneProfile a)
        (CanonicalDominance.oneProfile b) := by
  rw [← CanonicalDominance.one_iff]
  constructor
  · intro h
    obtain ⟨i, hi, hs⟩ := h.2
    have hi0 : i = 0 := by
      simp only [contractMin, List.length_cons, List.length_nil, List.mem_range] at hi
      omega
    subst hi0
    simpa [strictAxis, reading, contractMin, ComparisonContract.normalize, Int.ofNat_lt] using hs
  · intro h
    refine ⟨?_, 0, ?_, ?_⟩
    · intro i hi
      have hi0 : i = 0 := by
        simp only [contractMin, List.length_cons, List.length_nil, List.mem_range] at hi
        omega
      subst hi0
      simp [axisVerdict, boolGate, reading, contractMin, ComparisonContract.normalize,
        Int.ofNat_le, Nat.le_of_lt h]
    · simp [contractMin, List.mem_range]
    · simpa [strictAxis, reading, contractMin, ComparisonContract.normalize, Int.ofNat_lt] using h

theorem known_gate_matches_bool (v w : Int) :
    axisVerdict contractMin [some v] [some w] 0 =
      boolGate (decide (ComparisonContract.cost contractMin [v] 0 ≤
        ComparisonContract.cost contractMin [w] 0)) := by
  simp [axisVerdict, boolGate, reading, contractMin, ComparisonContract.cost,
    ComparisonContract.normalize, decide_eq_true_eq]

structure FiniteSpace where
  nothingOutside : Prop
  noCoverageGaps : Prop

theorem supplied_space_known_dominance
    (space : FiniteSpace)
    (hOut : space.nothingOutside)
    (hGap : space.noCoverageGaps)
    (a b : Nat)
    (h : dominates contractMin [some (Int.ofNat a)] [some (Int.ofNat b)]) :
    space.nothingOutside ∧ space.noCoverageGaps ∧
      Interface.dominates CanonicalDominance.oneSpace
        (CanonicalDominance.oneProfile a)
        (CanonicalDominance.oneProfile b) :=
  ⟨hOut, hGap, (known_agrees_canonical a b).mp h⟩

#print axioms absent_axis_admitted_by_two_valued_dominance
#print axioms unknown_blocks_dominance
#print axioms known_agrees_canonical
#print axioms known_gate_matches_bool
#print axioms supplied_space_known_dominance

end ThreeValuedGate
