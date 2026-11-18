/- Executable exhaustive qualification over n Boolean dimensions.
   accepts is executable and total. It is an input, not assumed to decide arbitrary semantics.
-/
namespace FiniteQualification

def candidates : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (candidates n).map (false :: ·) ++ (candidates n).map (true :: ·)

theorem candidates_length (n : Nat) : (candidates n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [candidates, ih, Nat.pow_succ, Nat.mul_two]

theorem candidates_exact (n : Nat) (xs : List Bool) :
    xs ∈ candidates n ↔ xs.length = n := by
  induction n generalizing xs with
  | zero => simp [candidates]
  | succ n ih =>
    cases xs with
    | nil => simp [candidates]
    | cons b bs =>
      cases b <;> simp [candidates, ih]

def qualify (n : Nat) (accepts : List Bool → Bool) : List (List Bool) :=
  (candidates n).filter accepts

theorem qualify_exact (n : Nat) (accepts : List Bool → Bool) (xs : List Bool) :
    xs ∈ qualify n accepts ↔ xs.length = n ∧ accepts xs = true := by
  simp [qualify, candidates_exact]

-- Explicitly check completeness, not merely the number of examined candidates.
#print axioms candidates_length
#print axioms candidates_exact
#print axioms qualify_exact
#eval (qualify 3 (fun xs => xs == [true, false, true]))
end FiniteQualification
