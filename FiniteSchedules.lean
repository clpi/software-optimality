import FiniteFrontier
import Std
namespace FiniteSchedules
abbrev Placement := Nat × Nat -- venue, start tick
abbrev Schedule := List Placement

def tuples (choices : List Placement) : Nat → List Schedule
  | 0 => [[]]
  | n+1 => choices.flatMap (fun p => (tuples choices n).map (p :: ·))

theorem tuples_exact (choices : List Placement) (n : Nat) (s : Schedule) :
    s ∈ tuples choices n ↔ s.length = n ∧ ∀ p, p ∈ s → p ∈ choices := by
  induction n generalizing s with
  | zero => cases s <;> simp [tuples]
  | succ n ih =>
    cases s with
    | nil => simp [tuples]
    | cons p ps =>
      simp only [tuples, List.mem_flatMap, List.mem_map, List.cons.injEq,
        List.length_cons, Nat.succ.injEq]
      constructor
      · rintro ⟨x, hx, ys, hy, hxp, hys⟩
        subst x; subst ys
        obtain ⟨hl, hp⟩ := (ih ps).mp hy
        exact ⟨hl, fun y h => (List.mem_cons.mp h).elim (fun e => e ▸ hx) (hp y)⟩
      · rintro ⟨hl, hp⟩
        exact ⟨p, hp p (List.mem_cons_self), ps,
          (ih ps).mpr ⟨hl, fun y h => hp y (List.mem_cons_of_mem p h)⟩, rfl, rfl⟩

def choices (venues horizon : Nat) : List Placement :=
  (List.range venues).flatMap (fun v => (List.range (horizon+1)).map (v, ·))

theorem choices_exact (venues horizon : Nat) (p : Placement) :
    p ∈ choices venues horizon ↔ p.1 < venues ∧ p.2 ≤ horizon := by
  cases p with
  | mk v t => simp [choices, Nat.lt_succ_iff]

def enumerate (jobs venues horizon : Nat) := tuples (choices venues horizon) jobs

theorem enumerate_exact (jobs venues horizon : Nat) (s : Schedule) :
    s ∈ enumerate jobs venues horizon ↔
      s.length = jobs ∧ ∀ p, p ∈ s → p.1 < venues ∧ p.2 ≤ horizon := by
  simp only [enumerate, tuples_exact, choices_exact]

def venue (s : Schedule) (i : Nat) := (s.getD i (0,0)).1
 def start (s : Schedule) (i : Nat) := (s.getD i (0,0)).2

def feasible (jobs venues horizon : Nat) (duration : Nat → Nat)
    (deps : List (Nat × Nat)) (s : Schedule) : Bool :=
  decide (s.length = jobs) &&
  s.all (fun p => decide (p.1 < venues ∧ p.2 ≤ horizon)) &&
  (List.range jobs).all (fun i => (List.range jobs).all (fun j =>
    decide (i < j → venue s i = venue s j →
      start s i + duration i ≤ start s j ∨ start s j + duration j ≤ start s i))) &&
  deps.all (fun d => decide (d.1 < jobs ∧ d.2 < jobs ∧
    start s d.1 + duration d.1 ≤ start s d.2))

def Feasible (jobs venues horizon : Nat) (duration : Nat → Nat)
    (deps : List (Nat × Nat)) (s : Schedule) : Prop :=
  s.length = jobs ∧
  (∀ p, p ∈ s → p.1 < venues ∧ p.2 ≤ horizon) ∧
  (∀ i, i < jobs → ∀ j, j < jobs → i < j → venue s i = venue s j →
    start s i + duration i ≤ start s j ∨ start s j + duration j ≤ start s i) ∧
  (∀ d, d ∈ deps → d.1 < jobs ∧ d.2 < jobs ∧
    start s d.1 + duration d.1 ≤ start s d.2)

theorem feasible_exact (jobs venues horizon : Nat) (duration : Nat → Nat)
    (deps : List (Nat × Nat)) (s : Schedule) :
    feasible jobs venues horizon duration deps s = true ↔
      Feasible jobs venues horizon duration deps s := by
  simp only [feasible, Feasible, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq, List.mem_range, and_assoc]

def feasibleSchedules (jobs venues horizon : Nat) (duration : Nat → Nat)
    (deps : List (Nat × Nat)) :=
  (enumerate jobs venues horizon).filter (feasible jobs venues horizon duration deps)

theorem feasibleSchedules_exact (jobs venues horizon : Nat) (duration : Nat → Nat)
    (deps : List (Nat × Nat)) (s : Schedule) :
    s ∈ feasibleSchedules jobs venues horizon duration deps ↔
      Feasible jobs venues horizon duration deps s := by
  simp only [feasibleSchedules, List.mem_filter, enumerate_exact, feasible_exact]
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨⟨h.1, h.2.1⟩, h⟩

-- Membership in the supplied finite list, with no dominator inside that same list.
-- The dominance predicate is an input. It is not a claim of global optimality.
def nondominatedInSuppliedFiniteList {T : Type} [DecidableEq T] (candidates : List T)
    (dominates : T → T → Bool) (s : T) : Bool :=
  candidates.contains s && !(candidates.any (fun t => dominates t s))

theorem nondominatedInSuppliedFiniteList_exact {T : Type} [DecidableEq T] (candidates : List T)
    (dominates : T → T → Bool) (s : T) :
    nondominatedInSuppliedFiniteList candidates dominates s = true ↔
      s ∈ candidates ∧ ∀ t, t ∈ candidates → dominates t s = false := by
  simp [nondominatedInSuppliedFiniteList, List.any_eq_true]

-- Nondominated among every feasible schedule of this enumerated model, under the
-- supplied integer cost on the supplied axes. The list is the enumerator's output.
theorem nondominatedInEnumeratedSchedulesUnderSuppliedIntegerCost
    (jobs venues horizon : Nat) (duration : Nat → Nat)
    (deps : List (Nat × Nat)) (axes : List Nat) (cost : Schedule → Nat → Int)
    (s : Schedule)
    (h : nondominatedInSuppliedFiniteList (feasibleSchedules jobs venues horizon duration deps)
      (FiniteFrontier.strictPareto axes cost) s = true) :
    Feasible jobs venues horizon duration deps s ∧
    ∀ t, Feasible jobs venues horizon duration deps t →
      ¬ ((∀ i, i ∈ axes → cost t i ≤ cost s i) ∧
         (∃ i, i ∈ axes ∧ cost t i < cost s i)) := by
  obtain ⟨hs, hn⟩ := (nondominatedInSuppliedFiniteList_exact _ _ s).mp h
  refine ⟨(feasibleSchedules_exact _ _ _ _ _ s).mp hs, ?_⟩
  intro t ht hd
  have hf := hn t ((feasibleSchedules_exact _ _ _ _ _ t).mpr ht)
  have htrue := (FiniteFrontier.pareto_exact axes cost t s).mpr hd
  simp [hf] at htrue

-- Queue schedules used by external test runners: one serial queue per venue.
abbrev QueueSchedule := List (List Nat)

def queueFeasible (jobs venues : Nat) (qs : QueueSchedule) : Bool :=
  decide (qs.length = venues) && qs.flatten.all (fun j => decide (j < jobs)) &&
  (List.range jobs).all (fun j => decide (qs.flatten.count j = 1))

theorem queueFeasible_exact (jobs venues : Nat) (qs : QueueSchedule) :
    queueFeasible jobs venues qs = true ↔
    qs.length = venues ∧ (∀ j, j ∈ qs.flatten → j < jobs) ∧
      (∀ j, j < jobs → qs.flatten.count j = 1) := by
  simp only [queueFeasible, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq, List.mem_range, and_assoc]

-- Rewrites/reordering require an independently validated preservation certificate.
-- A lower measured cost alone does not establish behavior preservation.
def improvementCertificate {T : Type} (feasible : T → Bool)
    (preserves : T → T → Bool) (axes : List Nat) (cost : T → Nat → Int)
    (old new : T) : Bool :=
  feasible new && preserves old new && FiniteFrontier.strictPareto axes cost new old

theorem improvementCertificate_exact {T : Type} (feasible : T → Bool)
    (preserves : T → T → Bool) (axes : List Nat) (cost : T → Nat → Int)
    (old new : T) :
    improvementCertificate feasible preserves axes cost old new = true ↔
      feasible new = true ∧ preserves old new = true ∧
      (∀ i, i ∈ axes → cost new i ≤ cost old i) ∧
      (∃ i, i ∈ axes ∧ cost new i < cost old i) := by
  simp only [improvementCertificate, Bool.and_eq_true,
    FiniteFrontier.pareto_exact, and_assoc]

-- Behavior preservation in the conclusion is only `checkerSound` applied to the
-- Boolean the certificate already required. This theorem does not prove the checker.
theorem accepted_improvement_if_checkerSound {T : Type} (feasible : T → Bool)
    (preserves : T → T → Bool) (BehaviorPreserved : T → T → Prop)
    (checkerSound : ∀ old new, preserves old new = true → BehaviorPreserved old new)
    (axes : List Nat) (cost : T → Nat → Int) (old new : T)
    (h : improvementCertificate feasible preserves axes cost old new = true) :
    feasible new = true ∧ BehaviorPreserved old new ∧
      (∀ i, i ∈ axes → cost new i ≤ cost old i) ∧
      (∃ i, i ∈ axes ∧ cost new i < cost old i) := by
  obtain ⟨hf, hp, hc, hs⟩ := (improvementCertificate_exact feasible preserves axes cost old new).mp h
  exact ⟨hf, checkerSound old new hp, hc, hs⟩

#guard queueFeasible 4 2 [[0,2],[1,3]] == true
#guard queueFeasible 4 2 [[0,2],[1,1]] == false
#guard queueFeasible 4 2 [[0,2],[1,4]] == false
#guard feasible 2 2 2 (fun _ => 1) [] [(0,0),(1,0)] == true
#guard feasible 2 1 2 (fun _ => 1) [] [(0,0),(0,0)] == false
#guard feasible 2 2 2 (fun _ => 1) [(0,1)] [(0,0),(1,0)] == false

#print axioms queueFeasible_exact
#print axioms improvementCertificate_exact
#print axioms accepted_improvement_if_checkerSound
#print axioms tuples_exact
#print axioms enumerate_exact
#print axioms feasible_exact
#print axioms feasibleSchedules_exact
#print axioms nondominatedInSuppliedFiniteList_exact
#print axioms nondominatedInEnumeratedSchedulesUnderSuppliedIntegerCost
end FiniteSchedules
