import FiniteSchedules
import Std
/-
StrictSchedules: positive durations inside the finite schedule model.

`FiniteSchedules.feasible` enforces a dependency `(a, b)` only as
`start a + duration a ≤ start b`, and durations are natural numbers, zero
included. A dependency cycle whose jobs all have duration zero therefore
satisfies `feasible` today; the base file directs that positive durations
and acyclic dependencies be enforced separately when required. This module
is that separate enforcement, carried out inside the model:

Proven here:
- `positive` is the decidable check that every placed job has duration
  strictly greater than zero, with the exact characterization
  `positive_exact`.
- `feasibleStrict` is `feasible` conjoined with `positive`, with the exact
  characterization `feasibleStrict_iff`, and `feasibleStrict_exact`: the
  strict enumeration (the base enumeration filtered by `feasibleStrict`,
  equivalently the base feasible enumeration filtered by `positive`) holds
  exactly the schedules carrying the enumeration characterization, the base
  feasibility predicate, and positivity.
- `strict_precedence`: in a strictly feasible schedule every listed
  dependency is a strict precedence, `start a < start b`.
- `no_dependency_cycle`: no strictly feasible schedule carries a dependency
  cycle, where a cycle is a nonempty job list whose consecutive pairs and
  whose closing pair are all listed dependencies.

Not claimed:
- Nothing about `feasible` alone: without the positivity conjunct the
  zero-duration cycle in the guards below remains feasible in the base
  model, by design of that model.
- Nothing outside the finite bounds of the base model (finitely many jobs,
  venues, and a horizon), and nothing about cost, dominance, or optimality:
  this module adds no cost function and no optimality result.
- Positivity is a property of the given duration function at the placed
  jobs only; no duration function is constructed or repaired here.
-/
namespace StrictSchedules
open FiniteSchedules

/-- A schedule is positive when every placed job has strictly positive
duration. In the base representation a schedule is a list of placements
indexed by job, so the placed jobs are exactly the indices
`j < s.length`, and job `j` is positive when `0 < duration j`. -/
def positive (duration : Nat → Nat) (s : Schedule) : Bool :=
  (List.range s.length).all (fun j => decide (0 < duration j))

/-- The propositional form of `positive`: every placed job index has
strictly positive duration. -/
def Positive (duration : Nat → Nat) (s : Schedule) : Prop :=
  ∀ j, j < s.length → 0 < duration j

theorem positive_exact (duration : Nat → Nat) (s : Schedule) :
    positive duration s = true ↔ Positive duration s := by
  simp only [positive, Positive, List.all_eq_true, decide_eq_true_eq,
    List.mem_range]

/-- Strict feasibility: base feasibility conjoined with positivity, with
exactly the argument shape of `FiniteSchedules.feasible`. -/
def feasibleStrict (jobs venues horizon : Nat) (duration : Nat → Nat)
    (deps : List (Nat × Nat)) (s : Schedule) : Bool :=
  feasible jobs venues horizon duration deps s && positive duration s

theorem feasibleStrict_iff (jobs venues horizon : Nat) (duration : Nat → Nat)
    (deps : List (Nat × Nat)) (s : Schedule) :
    feasibleStrict jobs venues horizon duration deps s = true ↔
      Feasible jobs venues horizon duration deps s ∧ Positive duration s := by
  simp only [feasibleStrict, Bool.and_eq_true, feasible_exact, positive_exact]

/-- The strict enumeration: the base enumeration filtered by
`feasibleStrict`. -/
def feasibleStrictSchedules (jobs venues horizon : Nat) (duration : Nat → Nat)
    (deps : List (Nat × Nat)) :=
  (enumerate jobs venues horizon).filter
    (feasibleStrict jobs venues horizon duration deps)

/-- Filter composition: filtering the base enumeration by the conjunction
`feasibleStrict` is filtering the base feasible enumeration by `positive`.
This is `List.filter_filter` read in the direction the exactness proof
consumes. -/
theorem feasibleStrictSchedules_filter (jobs venues horizon : Nat)
    (duration : Nat → Nat) (deps : List (Nat × Nat)) :
    feasibleStrictSchedules jobs venues horizon duration deps =
      (feasibleSchedules jobs venues horizon duration deps).filter
        (positive duration) := by
  unfold feasibleStrictSchedules feasibleSchedules
  rw [List.filter_filter]
  apply List.filter_congr
  intro x _
  simp only [feasibleStrict, Bool.and_comm]

/-- Exactness of the strict enumeration: a schedule appears in it exactly
when it carries the base enumeration characterization (length and placement
bounds), the base feasibility predicate, and positivity. The first two
components are the content of `feasibleSchedules_exact` for the composed
filter; the enumeration characterization is restated explicitly because it
is part of that predicate, so this is the strongest exact form the pieces
support. -/
theorem feasibleStrict_exact (jobs venues horizon : Nat) (duration : Nat → Nat)
    (deps : List (Nat × Nat)) (s : Schedule) :
    s ∈ feasibleStrictSchedules jobs venues horizon duration deps ↔
      (s.length = jobs ∧ ∀ p, p ∈ s → p.1 < venues ∧ p.2 ≤ horizon) ∧
        Feasible jobs venues horizon duration deps s ∧
          Positive duration s := by
  rw [feasibleStrictSchedules_filter, List.mem_filter]
  constructor
  · rintro ⟨hfs, hpos⟩
    have hF := (feasibleSchedules_exact jobs venues horizon duration deps s).mp hfs
    have hP := (positive_exact duration s).mp hpos
    exact ⟨⟨hF.1, hF.2.1⟩, hF, hP⟩
  · rintro ⟨⟨hl, hb⟩, hF, hP⟩
    exact ⟨(feasibleSchedules_exact jobs venues horizon duration deps s).mpr hF,
      (positive_exact duration s).mpr hP⟩

/-- Strict precedence: in a strictly feasible schedule every listed
dependency starts strictly earlier at its source than at its target. The
base model gives `start a + duration a ≤ start b`; positivity gives
`0 < duration a`; the conclusion is the arithmetic combination. -/
theorem strict_precedence (jobs venues horizon : Nat) (duration : Nat → Nat)
    (deps : List (Nat × Nat)) (s : Schedule)
    (h : feasibleStrict jobs venues horizon duration deps s = true)
    (a b : Nat) (hdep : (a, b) ∈ deps) :
    start s a < start s b := by
  obtain ⟨hF, hP⟩ := (feasibleStrict_iff jobs venues horizon duration deps s).mp h
  have ha : a < jobs := (hF.2.2.2 (a, b) hdep).1
  have hle : start s a + duration a ≤ start s b :=
    (hF.2.2.2 (a, b) hdep).2.2
  have hpos : 0 < duration a := hP a (hF.1 ▸ ha)
  omega

/-- A consecutive-dependency chain over a job list: every consecutive pair
of the list is a listed dependency. A list of length below two is
vacuously a chain. -/
def Chain (deps : List (Nat × Nat)) : List Nat → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => (a, b) ∈ deps ∧ Chain deps (b :: rest)

/-- A dependency cycle presented as a job list `[a₁, ..., aₖ]` with
`k ≥ 1`: the list is `a₁ :: t` for some tail `t`, and the chain condition
is checked on the list extended by its own head, `l ++ [a₁]`, which checks
every consecutive pair of `l` together with the closing pair
`(aₖ, a₁)`. -/
def IsCycle (deps : List (Nat × Nat)) (l : List Nat) : Prop :=
  ∃ a t, l = a :: t ∧ Chain deps (l ++ [a])

/-- The path lemma: along any dependency path with at least one edge,
presented as `a :: t ++ [b]` (source `a`, intermediate jobs `t`, target
`b`), a strictly feasible schedule starts the source strictly before the
target. Induction on the intermediate list, chaining
`strict_precedence` one edge at a time. -/
theorem start_lt_of_chain (jobs venues horizon : Nat) (duration : Nat → Nat)
    (deps : List (Nat × Nat)) (s : Schedule)
    (h : feasibleStrict jobs venues horizon duration deps s = true) :
    ∀ (t : List Nat) (a b : Nat),
      Chain deps (a :: t ++ [b]) → start s a < start s b := by
  intro t
  induction t with
  | nil =>
    intro a b hc
    exact strict_precedence jobs venues horizon duration deps s h a b hc.1
  | cons c t ih =>
    intro a b hc
    have hac : (a, c) ∈ deps := hc.1
    have hcb : Chain deps (c :: t ++ [b]) := hc.2
    have h1 := strict_precedence jobs venues horizon duration deps s h a c hac
    have h2 := ih c b hcb
    omega

/-- No dependency cycle exists in a strictly feasible schedule: a cycle
would present its own head as a path from that head back to itself, and
the path lemma would give `start a < start a`. -/
theorem no_dependency_cycle (jobs venues horizon : Nat) (duration : Nat → Nat)
    (deps : List (Nat × Nat)) (s : Schedule)
    (h : feasibleStrict jobs venues horizon duration deps s = true) :
    ¬ ∃ l, IsCycle deps l := by
  rintro ⟨l, a, t, rfl, hc⟩
  have hlt := start_lt_of_chain jobs venues horizon duration deps s h t a a hc
  omega

-- The cycle predicate is not vacuous: it holds of the concrete instances
-- the guards below exclude on positivity grounds alone.
example : IsCycle [(0, 1), (1, 0)] [0, 1] := ⟨0, [1], rfl, by simp [Chain]⟩
example : IsCycle [(0, 0)] [0] := ⟨0, [], rfl, by simp [Chain]⟩

-- Negative control: a zero-duration two-job dependency cycle. Both jobs
-- sit at tick 0 on distinct venues, each dependency reads `0 + 0 ≤ 0`, so
-- the base checker holds of it, while strict feasibility refuses it
-- because neither placed job has positive duration.
#guard feasible 2 2 2 (fun _ => 0) [(0, 1), (1, 0)] [(0, 0), (1, 0)] == true
#guard positive (fun _ => 0) [(0, 0), (1, 0)] == false
#guard feasibleStrict 2 2 2 (fun _ => 0) [(0, 1), (1, 0)] [(0, 0), (1, 0)] == false

-- Positive control: the same shape with unit durations and a single
-- dependency is strictly feasible.
#guard positive (fun _ => 1) [(0, 0), (1, 1)] == true
#guard feasibleStrict 2 2 2 (fun _ => 1) [(0, 1)] [(0, 0), (1, 1)] == true

-- Enumeration controls on a one-job instance: the single placement is
-- strictly feasible at unit duration, and nothing survives at duration
-- zero; at horizon 1 both placements survive at unit duration.
#guard feasibleStrictSchedules 1 1 0 (fun _ => 1) [] == [[(0, 0)]]
#guard feasibleStrictSchedules 1 1 0 (fun _ => 0) [] == []
#guard (feasibleStrictSchedules 1 1 1 (fun _ => 1) []).length == 2
#guard feasibleStrictSchedules 2 2 2 (fun _ => 0) [(0, 1), (1, 0)] == []

#print axioms positive_exact
#print axioms feasibleStrict_iff
#print axioms feasibleStrict_exact
#print axioms strict_precedence
#print axioms no_dependency_cycle
end StrictSchedules
