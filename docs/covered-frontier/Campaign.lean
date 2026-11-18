import EligibleCampaign
import ScopedEvidence
import ScopedSelection
import Std

/- Existing archived campaign, with its original candidates and objective.
   This is not a new experiment or a certificate for Idol. Measurements and
   policy are imported by EligibleCampaign with their source hashes. -/
namespace CoveredCampaign
open EligibleCampaign

-- The declared type names ALL three recorded alternatives, not only the winner.
theorem declared_candidates_exhaustive (c : Candidate) : c ∈ catalogue := by
  cases c <;> decide

theorem all_declared_candidates_qualified (c : Candidate) : gate c = true := by
  cases c <;> decide

theorem archived_exact_certificate :
    FiniteFrontier.certificate catalogue [.O2] dominates = true := by decide

-- Universal over this closed recorded-candidate type. The objective remains
-- the existing maximum observed wall time over the three prescribed rounds.
theorem archived_frontier_exact (c : Candidate) :
    c = .O2 ↔ gate c = true ∧
      ∀ d : Candidate, gate d = true → dominates d c = false := by
  constructor
  · intro same
    subst c
    refine ⟨by decide, ?_⟩
    intro d _
    cases d <;> decide
  · rintro ⟨_, noneBetter⟩
    cases c with
    | O2 => rfl
    | O1 => have bad := noneBetter .O2 (by decide); contradiction
    | R2 => have bad := noneBetter .O2 (by decide); contradiction

-- A false claim about a recorded counterfactual must fail the same comparator.
theorem archived_counterfactual_does_not_dominate_winner :
    dominates .R2 .O2 = false := by decide

-- The named baseline is the policy's O1, and the full catalogue stays visible.
theorem archived_named_replacement :
    Candidate.O1 ∈ catalogue ∧ gate .O1 = true ∧ gate .O2 = true ∧
      FiniteFrontier.certificate catalogue [.O2] dominates = true ∧
      dominates .O2 .O1 = true := by decide

theorem archived_paired_round_nonregression :
    ((times .O2).zip (times .O1)).all (fun p => decide (p.1 ≤ p.2)) = true := by decide

#print axioms declared_candidates_exhaustive
#print axioms all_declared_candidates_qualified
#print axioms archived_exact_certificate
#print axioms archived_frontier_exact
#print axioms archived_named_replacement
#print axioms archived_paired_round_nonregression
end CoveredCampaign
