import Std
namespace FiniteFrontier
variable {A : Type}

-- dominates y x is the chosen total, reproducible comparison predicate.
-- When it represents strict Pareto dominance this is exactly the Pareto frontier.
def frontier (candidates : List A) (dominates : A → A → Bool) : List A :=
  candidates.filter (fun x => !(candidates.any (fun y => dominates y x)))

theorem frontier_exact (candidates : List A) (dominates : A → A → Bool) (x : A) :
    x ∈ frontier candidates dominates ↔
      x ∈ candidates ∧ ∀ y, y ∈ candidates → dominates y x = false := by
  simp [frontier, List.any_eq_true]

def strictPareto (axes : List Nat) (cost : A → Nat → Int) (y x : A) : Bool :=
  axes.all (fun i => decide (cost y i ≤ cost x i)) &&
  axes.any (fun i => decide (cost y i < cost x i))

theorem pareto_exact (axes : List Nat) (cost : A → Nat → Int) (y x : A) :
    strictPareto axes cost y x = true ↔
      (∀ i, i ∈ axes → cost y i ≤ cost x i) ∧
      (∃ i, i ∈ axes ∧ cost y i < cost x i) := by
  simp [strictPareto, List.all_eq_true, List.any_eq_true]

inductive Color where
  | unknown | lawful | unlawful | conflict
  deriving DecidableEq, Repr

def color : Bool → Bool → Color
  | false, false => .unknown
  | true, false => .lawful
  | false, true => .unlawful
  | true, true => .conflict

theorem conflict_exact (positive negative : Bool) :
    color positive negative = .conflict ↔ positive = true ∧ negative = true := by
  cases positive <;> cases negative <;> decide

theorem unknown_exact (positive negative : Bool) :
    color positive negative = .unknown ↔ positive = false ∧ negative = false := by
  cases positive <;> cases negative <;> decide

#print axioms frontier_exact
#print axioms pareto_exact
#print axioms conflict_exact
#print axioms unknown_exact
-- A retained point must be nondominated in the FULL named catalogue. Every
-- excluded point needs a retained strict dominator, not an estimated score.
def certificate [DecidableEq A] (catalogue retained : List A)
    (dominates : A → A → Bool) : Bool :=
  retained.all (fun x => catalogue.contains x &&
    !(catalogue.any (fun y => dominates y x))) &&
  catalogue.all (fun x => retained.contains x ||
    retained.any (fun y => dominates y x))

theorem certificate_exact [DecidableEq A] (catalogue retained : List A)
    (dominates : A → A → Bool) :
    certificate catalogue retained dominates = true ↔
      (∀ x, x ∈ retained → x ∈ catalogue ∧
        ∀ y, y ∈ catalogue → dominates y x = false) ∧
      (∀ x, x ∈ catalogue → x ∈ retained ∨
        ∃ y, y ∈ retained ∧ dominates y x = true) := by
  simp [certificate, List.all_eq_true, List.any_eq_true]

theorem certified_frontier [DecidableEq A] (catalogue retained : List A)
    (dominates : A → A → Bool)
    (valid : certificate catalogue retained dominates = true) (x : A) :
    x ∈ retained ↔ x ∈ FiniteFrontier.frontier catalogue dominates := by
  have checked := (certificate_exact catalogue retained dominates).mp valid
  constructor
  · intro hx
    exact (FiniteFrontier.frontier_exact catalogue dominates x).mpr (checked.1 x hx)
  · intro hx
    have point := (FiniteFrontier.frontier_exact catalogue dominates x).mp hx
    rcases checked.2 x point.1 with kept | ⟨y, hy, beats⟩
    · exact kept
    · have excluded := point.2 y (checked.1 y hy).1
      rw [excluded] at beats
      contradiction

-- A checked certificate supplies a no-worse retained representative of every
-- named point. Semantic qualification and universe coverage are caller premises.
theorem certified_coverage [DecidableEq A] (catalogue retained : List A)
    (axes : List Nat) (cost : A → Nat → Int)
    (valid : certificate catalogue retained (strictPareto axes cost) = true) :
    ∀ x, x ∈ catalogue → ∃ y, y ∈ retained ∧
      ∀ i, i ∈ axes → cost y i ≤ cost x i := by
  intro x hx
  have checked := (certificate_exact catalogue retained _).mp valid
  rcases checked.2 x hx with kept | ⟨y, hy, beats⟩
  · exact ⟨x, kept, fun _ _ => Int.le_refl _⟩
  · exact ⟨y, hy, ((pareto_exact axes cost y x).mp beats).1⟩

-- Equal-cost identities are part of the frontier: a strict-dominator
-- certificate cannot discard one merely by choosing a presentation tie-break.
private def certificateCost (x : Bool) (_ : Nat) : Int := if x then 1 else 0
example : certificate [false, true] [false] (strictPareto [0] certificateCost) = true := by decide
example : certificate [false, true] [true] (strictPareto [0] certificateCost) = false := by decide
example : certificate [false, true] [] (strictPareto [0] certificateCost) = false := by decide
example : certificate [false, true] [false]
    (strictPareto [0] (fun (_ : Bool) (_ : Nat) => (0 : Int))) = false := by decide
example : certificate [false, true] [false, true]
    (strictPareto [0] (fun (_ : Bool) (_ : Nat) => (0 : Int))) = true := by decide

#print axioms certificate_exact
#print axioms certified_frontier
#print axioms certified_coverage
end FiniteFrontier
