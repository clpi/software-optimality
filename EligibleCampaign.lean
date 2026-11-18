import EligibleSchedules
import LinearSelection
import Std
namespace EligibleCampaign
open EligibleSchedules
-- Source qualification.json SHA256: 037ce2972cbf5bb72de79e24e3c914b4254406a488696a5e4e9f7b00eff50b73
-- Policy SHA256: 44faa39b813fe8ff0571957fa2f535d2d6d022ebd765cf8c0d95296ef5d40416
-- This module checks imported observations, not their measurement/instrumentation truth.
inductive Candidate where
  | O1 | O2 | R2
  deriving DecidableEq, Repr

def catalogue : List Candidate := [.O1,.O2,.R2]
def times : Candidate → List Nat
  | .O1 => [10769189848, 7296152413, 7966428370]
  | .O2 => [5429128102, 6128442901, 6240471073]
  | .R2 => [9146680841, 6480720115, 6777395883]

def caps : List Nat := [10769189848,7296152413,7966428370]
def timingChecks (c : Candidate) : List (Option Nat × Nat) :=
  (times c).zip caps |>.map (fun p => (some p.1, p.2))

-- same collected ids, same phase/outcome/skip records, zero process exit.
def receiptFlags : Candidate → List (List (Bool × Bool × Bool))
  | .O1 => [[(true, true, true), (true, true, true), (true, true, true), (true, true, true)], [(true, true, true), (true, true, true), (true, true, true), (true, true, true)], [(true, true, true), (true, true, true), (true, true, true), (true, true, true)]]
  | .O2 => [[(true, true, true), (true, true, true), (true, true, true), (true, true, true)], [(true, true, true), (true, true, true), (true, true, true), (true, true, true)], [(true, true, true), (true, true, true), (true, true, true), (true, true, true)]]
  | .R2 => [[(true, true, true), (true, true, true), (true, true, true), (true, true, true)], [(true, true, true), (true, true, true), (true, true, true), (true, true, true)], [(true, true, true), (true, true, true), (true, true, true), (true, true, true)]]

def observed (c : Candidate) : Bool :=
  decide ((receiptFlags c).length = 3) &&
  (receiptFlags c).all (fun jobs => decide (jobs.length = 4) &&
    jobs.all (fun j => j.1 && j.2.1 && j.2.2))

def workers : Candidate → Nat
  | .O1 => 1
  | _ => 2
-- Worker slots are a feasibility constraint, NEVER an invented quality axis.
def capacityOK (c : Candidate) := decide (workers c ≤ 2)
def gate := eligible capacityOK observed 3 timingChecks
-- Sole policy objective: maximum observed wall time across the three rounds.
def cost (c : Candidate) (_axis : Nat) : Int :=
  Int.ofNat ((times c).foldl max 0)
def dominates := FiniteFrontier.strictPareto [0] cost

theorem all_receipt_lengths : catalogue.all (fun c => decide ((times c).length = 3)) = true := by decide

theorem all_observations_pass : catalogue.all observed = true := by decide
theorem all_hard_timing_pass : catalogue.all (fun c => timedAdmission 3 (timingChecks c)) = true := by decide
theorem all_admitted : catalogue.all gate = true := by decide

theorem chosen_qualified_optimum : optimumCertificate catalogue gate [0] cost .O2 = true := by decide

theorem optimum_semantics :
    (Candidate.O2 ∈ catalogue ∧ gate .O2 = true) ∧
    ∀ c, c ∈ catalogue → gate c = true →
      ¬ ((∀ i, i ∈ [0] → cost c i ≤ cost .O2 i) ∧
         (∃ i, i ∈ [0] ∧ cost c i < cost .O2 i)) :=
  (optimumCertificate_exact catalogue gate [0] cost .O2).mp chosen_qualified_optimum

theorem exact_eligible_frontier :
    FiniteFrontier.frontier (admitted catalogue gate) dominates = [.O2] := by decide

-- The actually executed reverse-order alternative passes the gate, but loses ranking.
theorem counterfactual_admitted : gate .R2 = true := by decide
theorem chosen_beats_counterfactual : dominates .O2 .R2 = true := by decide
theorem counterfactual_not_optimum : optimumCertificate catalogue gate [0] cost .R2 = false := by decide
theorem every_paired_counterfactual_slower :
    ((times .O2).zip (times .R2)).all (fun p => decide (p.1 < p.2)) = true := by decide

theorem exact_costs : [cost .O1 0,cost .O2 0,cost .R2 0] =
    [10769189848,6240471073,9146680841] := by decide

-- Negative control is explicitly synthetic, NOT an additional observed campaign run.
theorem synthetic_one_nanosecond_over_cap_rejected :
    timedAdmission 3 [(some 10769189849,10769189848),
      (some 6128442901,7296152413),(some 6240471073,7966428370)] = false := by decide

theorem linear_selector_agrees :
    LinearSelection.select (fun c => cost c 0) (catalogue.filter gate) = some .O2 := by decide

#print axioms linear_selector_agrees
#print axioms all_admitted
#print axioms chosen_qualified_optimum
#print axioms optimum_semantics
#print axioms exact_eligible_frontier
#print axioms counterfactual_admitted
#print axioms chosen_beats_counterfactual
#print axioms counterfactual_not_optimum
#print axioms every_paired_counterfactual_slower
#print axioms synthetic_one_nanosecond_over_cap_rejected
end EligibleCampaign
