import FiniteSchedules

namespace ReleaseSchedule
open FiniteSchedules

-- Compile, integration tests, format checks, package. Two interchangeable runners.
def duration : Nat → Nat
  | 0 => 5 | 1 => 9 | 2 => 7 | 3 => 2 | _ => 0

def edges : List (Nat × Nat) := [(0,1), (0,2), (1,3), (2,3)]
def serial : Schedule := [(0,0), (0,5), (0,14), (0,21)]
def parallelPlan : Schedule := [(0,0), (0,5), (1,5), (0,14)]
def doneAt (s : Schedule) := start s 3 + duration 3
def valid := feasible 4 2 21 duration edges

theorem before_after : valid serial = true ∧ valid parallelPlan = true ∧
    doneAt serial = 23 ∧ doneAt parallelPlan = 16 := by decide

-- The packing job is the sink. Its start is constrained by compile → test → pack.
-- This bound even holds if an arbitrary number of runners and start ticks are allowed.
theorem critical_path (s : Schedule) (r horizon : Nat)
    (h : Feasible 4 r horizon duration edges s) : doneAt parallelPlan ≤ doneAt s := by
  have a := (h.2.2.2 (0,1) (by decide)).2.2
  have b := (h.2.2.2 (1,3) (by decide)).2.2
  change start s 0 + 5 ≤ start s 1 at a
  change start s 1 + 9 ≤ start s 3 at b
  change 16 ≤ start s 3 + 2
  omega

-- Packaging a tick earlier breaks the test dependency even with a free runner.
theorem early_package_rejected :
    valid [(0,0), (0,5), (1,5), (1,13)] = false := by decide

#eval (doneAt serial, doneAt parallelPlan)
#print axioms before_after
#print axioms critical_path
#print axioms early_package_rejected
end ReleaseSchedule
