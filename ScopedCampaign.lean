import EligibleCampaign
import ScopedSelection
import Std
namespace ScopedCampaign
open ScopedEvidence
open EligibleCampaign

def candidateId : Candidate → Nat
  | .O1 => 0
  | .O2 => 1
  | .R2 => 2
-- Policy identifier is the imported policy SHA256 interpreted as a natural number.
-- Other identifiers below name the one pinned campaign fixture, not extra observations.
def policyId : Nat := 31200114646914547494470762822340355260683199803510051633469791093255243564054

def subject (c : Candidate) : Scope :=
  ⟨1,candidateId c,1,1,1,1,policyId,1⟩

def scopedPolicy (c : Candidate) : Policy :=
  ⟨policyId,(List.range 3).map (fun round => ⟨subject c,round,caps.getD round 0⟩)⟩

def roundPass (c : Candidate) (round : Nat) : Bool :=
  let jobs := (receiptFlags c).getD round []
  capacityOK c && decide (jobs.length = 4) &&
    jobs.all (fun j => j.1 && j.2.1 && j.2.2)

def scopedReceipts (c : Candidate) : List Receipt :=
  (List.range 3).map (fun round =>
    ⟨candidateId c * 10 + round,subject c,round,roundPass c round,(times c)[round]?⟩)

def scalarCost (c : Candidate) := EligibleCampaign.cost c 0

theorem all_scoped_admitted : catalogue.all (fun c =>
    qualify (scopedPolicy c) (scopedReceipts c)) = true := by decide

theorem scoped_nondominated_under_supplied_integer_cost :
    ScopedSelection.certificate catalogue scopedPolicy scopedReceipts [0]
      EligibleCampaign.cost .O2 = true := by decide

-- Actual final entry point: complete tied minimum set, with qualification as gate.
theorem scoped_selection :
    ScopedSelection.selectAll catalogue scopedPolicy scopedReceipts scalarCost = [.O2] := by decide

theorem scoped_selection_reordered :
    ScopedSelection.selectAll [.R2,.O1,.O2] scopedPolicy scopedReceipts scalarCost = [.O2] := by decide

-- Structural cross-check of the certificate above: it follows from the scalar
-- selection through Obligation S on the one supplied axis, with no second
-- kernel evaluation of the dominance certificate.
theorem scoped_nondominated_from_selection :
    ScopedSelection.certificate catalogue scopedPolicy scopedReceipts [0]
      EligibleCampaign.cost .O2 = true :=
  ScopedSelection.selected_all_certified catalogue scopedPolicy scopedReceipts [0]
    EligibleCampaign.cost scalarCost .O2
    (fun y _ h => FiniteFrontier.axis_strict 0 EligibleCampaign.cost y .O2 h)
    (by rw [scoped_selection]; exact List.mem_singleton_self _)

theorem selected_obligations_have_witnesses :
    ∀ q, q ∈ (scopedPolicy .O2).required →
      ∃ r, r ∈ scopedReceipts .O2 ∧ r.scope = q.scope ∧ r.round = q.round ∧
        r.observedPass = true ∧ ∃ t, r.elapsed = some t ∧ t ≤ q.limit :=
  (ScopedSelection.certified_scoped_nondominated_under_supplied_integer_cost
    catalogue scopedPolicy scopedReceipts [0]
    EligibleCampaign.cost .O2 scoped_nondominated_under_supplied_integer_cost).2.2.1

theorem reused_round_rejected :
    qualify (scopedPolicy .O2) ((scopedReceipts .O2).map (fun r => {r with round := 0})) = false := by decide

theorem foreign_configuration_rejected :
    qualify (scopedPolicy .O2) (scopedReceipts .R2) = false := by decide

#print axioms all_scoped_admitted
#print axioms scoped_nondominated_under_supplied_integer_cost
#print axioms scoped_selection
#print axioms scoped_nondominated_from_selection
#print axioms scoped_selection_reordered
#print axioms selected_obligations_have_witnesses
#print axioms reused_round_rejected
#print axioms foreign_configuration_rejected
end ScopedCampaign
