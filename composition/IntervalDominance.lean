import SoftwareIsQuantifiable.Pareto
import FrontierComposition

namespace IntervalDominance
open SoftwareIsQuantifiable.Pareto

abbrev Box := Nat → Bounds

def inside (axes : List Nat) (box : Box) (v : Nat → Nat) : Prop :=
  ∀ i ∈ axes, (box i).lo ≤ v i ∧ v i ≤ (box i).hi

def separates (axes : List Nat) (left right : Box) : Bool :=
  FiniteFrontier.strictPareto axes (fun b i =>
    if b then Int.ofNat (left i).hi else Int.ofNat (right i).lo) true false

def better (axes : List Nat) (x y : Nat → Nat) : Prop :=
  (∀ i ∈ axes, x i ≤ y i) ∧ ∃ i ∈ axes, x i < y i

private theorem corners (axes : List Nat) (a b : Box) :
    separates axes a b = true ↔ better axes (fun i => (a i).hi) (fun i => (b i).lo) := by
  simp [separates, FiniteFrontier.pareto_exact, better]

/-- Exact universal dominance for independent closed interval boxes. The
    pessimistic and optimistic corners are legal realizations in this model. -/
theorem separates_iff (axes : List Nat) (a b : Box) :
    separates axes a b = true ↔
      ∀ x y, inside axes a x → inside axes b y → better axes x y := by
  rw [corners]
  constructor
  · rintro ⟨hw, i, hi, hs⟩ x y hx hy
    exact ⟨fun j hj => Nat.le_trans (hx j hj).2 (Nat.le_trans (hw j hj) (hy j hj).1),
      i, hi, Nat.lt_of_le_of_lt (hx i hi).2 (Nat.lt_of_lt_of_le hs (hy i hi).1)⟩
  · intro all
    exact all _ _ (fun i _ => ⟨(a i).valid, Nat.le_refl _⟩)
      (fun i _ => ⟨Nat.le_refl _, (b i).valid⟩)

theorem refinement (axes : List Nat) (a b a' b' : Box)
    (ha : ∀ i ∈ axes, (a i).lo ≤ (a' i).lo ∧ (a' i).hi ≤ (a i).hi)
    (hb : ∀ i ∈ axes, (b i).lo ≤ (b' i).lo ∧ (b' i).hi ≤ (b i).hi)
    (h : separates axes a b = true) : separates axes a' b' = true := by
  apply (separates_iff ..).mpr
  intro x y hx hy
  exact (separates_iff ..).mp h x y
    (fun i hi => ⟨Nat.le_trans (ha i hi).1 (hx i hi).1, Nat.le_trans (hx i hi).2 (ha i hi).2⟩)
    (fun i hi => ⟨Nat.le_trans (hb i hi).1 (hy i hi).1, Nat.le_trans (hy i hi).2 (hb i hi).2⟩)

def two (first second : Bounds) : Box := fun i => if i = 0 then first else second

theorem two_axis_agreement (atime acost btime bcost : Bounds) :
    separates [0, 1] (two atime acost) (two btime bcost) = true ↔
    separated atime acost btime bcost := by
  simp [corners, better, two, separated, and_assoc]

theorem separates_transitive (axes : List Nat) : FrontierComposition.Transitive (separates axes) := by
  intro a b c hab hbc
  obtain ⟨hw,i,hi,hs⟩ := (corners ..).mp hab
  obtain ⟨hw',_⟩ := (corners ..).mp hbc
  exact (corners ..).mpr
    ⟨fun j hj => Nat.le_trans (hw j hj) (Nat.le_trans (b j).valid (hw' j hj)),
     i, hi, Nat.lt_of_lt_of_le hs (Nat.le_trans (b i).valid (hw' i hi))⟩

theorem separates_irreflexive (axes : List Nat) (a : Box) : separates axes a a = false := by
  cases h : separates axes a a with
  | false => rfl
  | true =>
    obtain ⟨_,i,_,hs⟩ := (corners ..).mp h
    exact False.elim (Nat.not_lt_of_ge (a i).valid hs)

/-- A shared scenario keeps dependence between observations. Every named
    scenario must witness strict dominance, possibly on a different axis. -/
def paired {S : Type} (scenarios : List S) (axes : List Nat) (left right : S → Nat → Nat) :=
  !scenarios.isEmpty && scenarios.all (fun s => FiniteFrontier.strictPareto axes
    (fun b i => if b then Int.ofNat (left s i) else Int.ofNat (right s i)) true false)

theorem paired_exact {S : Type} (ss : List S) (axes : List Nat) (l r : S → Nat → Nat) :
    paired ss axes l r = true ↔ ss ≠ [] ∧ ∀ s ∈ ss, better axes (l s) (r s) := by
  cases ss <;> simp [paired, List.all_eq_true, FiniteFrontier.pareto_exact, better]

/-- In each coupled scenario the left latency is lower by one. Both marginal
    boxes overlap, so forgetting scenario identity loses that certificate. -/
example : paired [0,1] [0] (fun s _ => s) (fun s _ => s+1) = true ∧
    separates [0] (fun _ => ⟨0, 1, by decide⟩) (fun _ => ⟨1, 2, by decide⟩) = false :=
  by decide

#print axioms separates_iff
#print axioms paired_exact
#print axioms separates_transitive
#print axioms separates_irreflexive
#print axioms refinement
#print axioms two_axis_agreement
end IntervalDominance
