import ScopedFrontier
import Std

/- Synthetic adversarial controls for the declared-domain and closure boundary.
   These values are checker fixtures, not software performance observations. -/
namespace CoveredFrontierControls
open ScopedFrontier

def domain : List Subject := [0, 1, 2, 3].map fixtureSubject
def pruned : List Subject := [2, 3].map fixtureSubject

theorem strict_pruning_preserves_both_tied_identities :
    certifyCovered fixtureContract domain pruned pruned fixture = true := by decide

-- The old catalogue-only certificate cannot see a missing generator competitor.
theorem incomplete_catalogue_can_pass_its_local_check :
    certify fixtureContract ([0, 1].map fixtureSubject) ([0, 1].map fixtureSubject) fixture = true := by decide
theorem missing_generator_competitor_rejected :
    certifyCovered fixtureContract domain ([0, 1].map fixtureSubject)
      ([0, 1].map fixtureSubject) fixture = false := by decide

-- Cost-vector equality does not justify discarding a distinct frontier identity.
theorem omitted_tied_identity_rejected :
    checkCoverage fixtureContract domain [fixtureSubject 2] fixture = false := by decide
theorem foreign_catalogue_identity_rejected :
    checkCoverage fixtureContract [fixtureSubject 0] domain fixture = false := by decide

def emptyAxes : Contract := { fixtureContract with axes := [] }
def emptyAxesInput (s : Subject) : Input := { fixture s with contract := emptyAxes }
theorem invalid_empty_axis_contract_rejected :
    certifyCovered emptyAxes domain [] [] emptyAxesInput = false := by decide

-- Frontier completeness is different from permission to replace an incumbent.
theorem incomparable_tradeoff_remains_on_frontier :
    certifyCovered fixtureContract ([0, 1].map fixtureSubject)
      ([0, 1].map fixtureSubject) ([0, 1].map fixtureSubject) fixture = true := by decide
theorem tradeoff_does_not_establish_nonregression :
    noRegression fixtureContract (fixtureSubject 0) (fixtureSubject 1) fixture = false := by decide
theorem strict_replacement_certified :
    certifyReplacement fixtureContract domain pruned pruned fixture
      (fixtureSubject 0) (fixtureSubject 2) = true := by decide
theorem frontier_tradeoff_cannot_replace_incumbent :
    certifyReplacement fixtureContract ([0, 1].map fixtureSubject)
      ([0, 1].map fixtureSubject) ([0, 1].map fixtureSubject) fixture
      (fixtureSubject 0) (fixtureSubject 1) = false := by decide
theorem empty_domain_cannot_certify_replacement :
    certifyReplacement fixtureContract [] [] [] fixture
      (fixtureSubject 0) (fixtureSubject 2) = false := by decide
theorem equal_cost_is_not_strict_improvement :
    certifyReplacement fixtureContract domain pruned pruned fixture
      (fixtureSubject 2) (fixtureSubject 3) = false := by decide

-- Feasibility is fixed independently of whether a cost receipt is available.
def unknownDomain : List Subject := [0, 1, 2].map fixtureSubject
def unknownInput (s : Subject) : Input :=
  if s.artifact = 1 then fixtureInput s 7 7
  else if s.artifact = 2 then omittedMetric s 11 else fixture s
def independentlyFeasible (_ : Subject) : Bool := true
theorem admitted_frontier_does_not_cover_feasible_unknown :
    certifyReplacement fixtureContract unknownDomain unknownDomain [fixtureSubject 1]
      unknownInput (fixtureSubject 0) (fixtureSubject 1) = true := by decide
theorem missing_cost_blocks_feasible_frontier_claim :
    certifyFeasible fixtureContract unknownDomain unknownDomain [fixtureSubject 1]
      independentlyFeasible unknownInput = false := by decide
theorem missing_cost_blocks_feasible_replacement_claim :
    certifyFeasibleReplacement fixtureContract unknownDomain unknownDomain [fixtureSubject 1]
      independentlyFeasible unknownInput (fixtureSubject 0) (fixtureSubject 1) = false := by decide
theorem complete_qualified_domain_certifies_feasible_replacement :
    certifyFeasibleReplacement fixtureContract domain pruned pruned
      independentlyFeasible fixture (fixtureSubject 0) (fixtureSubject 2) = true := by decide

def pair : List Subject := [0, 2].map fixtureSubject
def fromFacts (facts : Nat → Bool) (s : Subject) : Input :=
  if s.artifact = 2 && !facts 2 then failedCapability s else fixture s

theorem one_missing_premise_retains_incumbent :
    certifyClosed [0, 1, 2] [0] [([0, 1], 2)] fixtureContract pair pair
      [fixtureSubject 0] fromFacts = some true := by decide
theorem complete_joint_support_selects_challenger :
    certifyClosed [0, 1, 2] [0, 1] [([0, 1], 2)] fixtureContract pair pair
      [fixtureSubject 2] fromFacts = some true := by decide
theorem stale_frontier_after_added_premise_rejected :
    certifyClosed [0, 1, 2] [0, 1] [([0, 1], 2)] fixtureContract pair pair
      [fixtureSubject 0] fromFacts = some false := by decide
theorem missing_premise_cannot_qualify_challenger :
    certifyClosed [0, 1, 2] [0] [([0, 1], 2)] fixtureContract pair pair
      [fixtureSubject 2] fromFacts = some false := by decide
theorem cyclic_support_does_not_survive_root_withdrawal :
    certifyClosed [0, 1, 2] [] [([0], 2), ([2], 0)] fixtureContract pair pair
      [fixtureSubject 0] fromFacts = some true := by decide
theorem malformed_closure_refuses_before_frontier :
    certifyClosed [0, 1] [0] [([0], 2)] fixtureContract pair pair
      [fixtureSubject 0] fromFacts = none := by decide

#print axioms strict_pruning_preserves_both_tied_identities
#print axioms missing_generator_competitor_rejected
#print axioms omitted_tied_identity_rejected
#print axioms invalid_empty_axis_contract_rejected
#print axioms strict_replacement_certified
#print axioms empty_domain_cannot_certify_replacement
#print axioms missing_cost_blocks_feasible_replacement_claim
#print axioms complete_joint_support_selects_challenger
#print axioms cyclic_support_does_not_survive_root_withdrawal
end CoveredFrontierControls
