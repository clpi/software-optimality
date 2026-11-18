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
end FiniteFrontier
