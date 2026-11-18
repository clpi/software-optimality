import FiniteSchedules
import Std
namespace EligibleSchedules
variable {T : Type} [DecidableEq T]

-- A hard timing constraint has no tolerance; absent measurement is not a pass.
def timingOK (elapsed : Option Nat) (limit : Nat) : Bool :=
  match elapsed with
  | none => false
  | some t => decide (t ≤ limit)

theorem timingOK_exact (elapsed : Option Nat) (limit : Nat) :
    timingOK elapsed limit = true ↔ ∃ t, elapsed = some t ∧ t ≤ limit := by
  cases elapsed <;> simp [timingOK]

-- Each required measurement has its own declared hard limit (e.g. paired baseline).
def timedAdmission (required : Nat) (checks : List (Option Nat × Nat)) : Bool :=
  decide (0 < required) && decide (checks.length = required) &&
    checks.all (fun c => timingOK c.1 c.2)

theorem timedAdmission_exact (required : Nat) (checks : List (Option Nat × Nat)) :
    timedAdmission required checks = true ↔
      0 < required ∧ checks.length = required ∧
      ∀ c, c ∈ checks → ∃ t, c.1 = some t ∧ t ≤ c.2 := by
  simp only [timedAdmission, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, timingOK_exact, and_assoc]

-- Feasibility, observed behavior admission, and hard timing are independent gates.
def eligible (feasible observed : T → Bool) (required : Nat)
    (checks : T → List (Option Nat × Nat)) (x : T) : Bool :=
  feasible x && observed x && timedAdmission required (checks x)

omit [DecidableEq T] in
theorem eligible_exact (feasible observed : T → Bool) (required : Nat)
    (checks : T → List (Option Nat × Nat)) (x : T) :
    eligible feasible observed required checks x = true ↔
      feasible x = true ∧ observed x = true ∧ 0 < required ∧
      (checks x).length = required ∧
      ∀ c, c ∈ checks x → ∃ t, c.1 = some t ∧ t ≤ c.2 := by
  simp only [eligible, Bool.and_eq_true, timedAdmission_exact, and_assoc]

def admitted (candidates : List T) (gate : T → Bool) := candidates.filter gate

def optimumCertificate (candidates : List T) (gate : T → Bool)
    (axes : List Nat) (cost : T → Nat → Int) (x : T) : Bool :=
  FiniteSchedules.optimalCertificate (admitted candidates gate)
    (FiniteFrontier.strictPareto axes cost) x

-- Optimality is ONLY over eligible candidates; cost cannot override rejection.
theorem optimumCertificate_exact (candidates : List T) (gate : T → Bool)
    (axes : List Nat) (cost : T → Nat → Int) (x : T) :
    optimumCertificate candidates gate axes cost x = true ↔
      (x ∈ candidates ∧ gate x = true) ∧
      ∀ y, y ∈ candidates → gate y = true →
        ¬ ((∀ i, i ∈ axes → cost y i ≤ cost x i) ∧
           (∃ i, i ∈ axes ∧ cost y i < cost x i)) := by
  rw [optimumCertificate, FiniteSchedules.optimalCertificate_exact]
  simp only [admitted, List.mem_filter]
  constructor
  · rintro ⟨hx, hn⟩
    refine ⟨hx, ?_⟩
    intro y hy hg hd
    have hf := hn y ⟨hy,hg⟩
    have ht := (FiniteFrontier.pareto_exact axes cost y x).mpr hd
    simp [hf] at ht
  · rintro ⟨hx, hn⟩
    refine ⟨hx, ?_⟩
    intro y hy
    cases h : FiniteFrontier.strictPareto axes cost y x
    · rfl
    · exact False.elim (hn y hy.1 hy.2 ((FiniteFrontier.pareto_exact axes cost y x).mp h))

theorem rejected_cannot_be_optimal (candidates : List T) (gate : T → Bool)
    (axes : List Nat) (cost : T → Nat → Int) (x : T) (h : gate x = false) :
    optimumCertificate candidates gate axes cost x = false := by
  cases hc : optimumCertificate candidates gate axes cost x
  · rfl
  · have hg := ((optimumCertificate_exact candidates gate axes cost x).mp hc).1.2
    simp [h] at hg

theorem dominator_refutes_certificate (candidates : List T) (gate : T → Bool)
    (axes : List Nat) (cost : T → Nat → Int) (x y : T)
    (hy : y ∈ candidates) (hg : gate y = true)
    (hd : FiniteFrontier.strictPareto axes cost y x = true) :
    optimumCertificate candidates gate axes cost x = false := by
  cases hc : optimumCertificate candidates gate axes cost x
  · rfl
  · exact False.elim (((optimumCertificate_exact candidates gate axes cost x).mp hc).2
      y hy hg ((FiniteFrontier.pareto_exact axes cost y x).mp hd))

#guard timingOK (some 101) 100 == false
#guard timingOK (some 100) 100 == true
#guard timingOK none 100 == false
#guard timedAdmission 3 [(some 80,100),(some 101,100),(some 90,100)] == false
#guard timedAdmission 3 [(some 80,100),(none,100),(some 90,100)] == false
#guard timedAdmission 0 [] == false
#print axioms timingOK_exact
#print axioms timedAdmission_exact
#print axioms eligible_exact
#print axioms optimumCertificate_exact
#print axioms rejected_cannot_be_optimal
#print axioms dominator_refutes_certificate
end EligibleSchedules
