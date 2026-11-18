import ScopedSelection
import Std
namespace ScopedCompatibility
open ScopedEvidence
variable {T : Type} [DecidableEq T]

/-!
Catalogue compatibility as a checked admission precondition.

Proven here: a comparison contract is the triple carried by a candidate's
policy — the policy identity, and the intent and metric identities named in
the scopes of that policy's requirements. `compatible` holds exactly when
every candidate in a catalogue projects to the one named contract, and
`compatibleSelf` holds exactly when a catalogue is empty or every candidate
projects to one shared contract. The scoped optimum theorem is strengthened
accordingly: an accepted certificate over a compatible catalogue designates
a winner that itself carries the named contract, as does every candidate.

Not claimed: the remaining scope coordinates (artifact, configuration,
lineage, venue, harness) are subject identity, not comparison contract —
candidates are expected to differ there, as the pilot's configurations do.
A policy with no requirements, or with requirements that disagree on
intent, metric, or the policy tie, projects to no contract and is refused.
Whether a named policy identity really commits to particular policy bytes,
and whether intent and metric identities are used consistently by the
ingestion pipeline beyond the requirements recorded here, remain ingestion
duties; identifier equality is checked, authenticity is not proved.
-/

/-- The comparison contract of a candidate: policy, intent, and metric
identities. Scope coordinates that identify the subject itself (artifact,
configuration, lineage, venue, harness) are deliberately excluded. -/
structure Contract where
  policy : Nat
  intent : Nat
  metric : Nat
  deriving DecidableEq, Repr

/-- The contract a single policy projects to. A policy projects to a
contract only when it names at least one requirement and every requirement
agrees on intent and metric and is tied to the policy identity; otherwise
it projects to `none`, so an internally mixed policy is never admitted
under any contract. -/
def contractOfPolicy (policy : Policy) : Option Contract :=
  match policy.required with
  | [] => none
  | q :: _ =>
      if policy.required.all (fun r =>
          decide (r.scope.intent = q.scope.intent ∧ r.scope.metric = q.scope.metric ∧
            r.scope.policy = policy.id))
        then some ⟨policy.id, q.scope.intent, q.scope.metric⟩
        else none

/-- The comparison contract carried by one candidate under the supplied
per-candidate policy assignment: the projection of its policy. -/
def contractOf (policies : T → Policy) (c : T) : Option Contract :=
  contractOfPolicy (policies c)

/-- Admission precondition: every candidate in the catalogue carries
exactly the named contract. -/
def compatible (candidates : List T) (policies : T → Policy) (contract : Contract) : Bool :=
  candidates.all (fun c => decide (contractOf policies c = some contract))

/-- Homogeneous form: the catalogue is empty, or every candidate carries
the first candidate's contract. A first candidate projecting to no
contract makes the whole catalogue incompatible. -/
def compatibleSelf (candidates : List T) (policies : T → Policy) : Bool :=
  match candidates with
  | [] => true
  | c :: _ =>
      match contractOf policies c with
      | some contract => compatible candidates policies contract
      | none => false

/-- A policy projects to a contract exactly when its identity is the
contract's policy, it names at least one requirement, and every one of
its requirements carries the contract's intent and metric and is tied to
the contract's policy. -/
theorem contractOfPolicy_exact (policy : Policy) (contract : Contract) :
    contractOfPolicy policy = some contract ↔
      policy.id = contract.policy ∧ policy.required ≠ [] ∧
        ∀ q, q ∈ policy.required →
          q.scope.intent = contract.intent ∧ q.scope.metric = contract.metric ∧
            q.scope.policy = contract.policy := by
  obtain ⟨pid, req⟩ := policy
  obtain ⟨cp, ci, cm⟩ := contract
  cases req with
  | nil => simp [contractOfPolicy]
  | cons q qs =>
      simp only [contractOfPolicy, List.all_eq_true, decide_eq_true_eq]
      by_cases hall : ∀ x, x ∈ q :: qs →
          x.scope.intent = q.scope.intent ∧ x.scope.metric = q.scope.metric ∧
            x.scope.policy = pid
      · rw [if_pos hall]
        simp only [Option.some.injEq, Contract.mk.injEq]
        constructor
        · rintro ⟨hid, hint, hmet⟩
          refine ⟨hid, by simp, fun r hrmem => ?_⟩
          have hr' := hall r hrmem
          exact ⟨hint ▸ hr'.1, hmet ▸ hr'.2.1, hid ▸ hr'.2.2⟩
        · rintro ⟨hid, -, hreq⟩
          have hq := hreq q (by simp)
          exact ⟨hid, hq.1, hq.2.1⟩
      · rw [if_neg hall]
        constructor
        · intro h; simp at h
        · rintro ⟨hid, -, hreq⟩
          exfalso
          apply hall
          intro r hrmem
          have hs := hreq r hrmem
          have hq := hreq q (by simp)
          exact ⟨hq.1 ▸ hs.1, hq.2.1 ▸ hs.2.1, hid ▸ hs.2.2⟩

omit [DecidableEq T] in
/-- Candidate form of `contractOfPolicy_exact`. -/
theorem contractOf_exact (policies : T → Policy) (c : T) (contract : Contract) :
    contractOf policies c = some contract ↔
      (policies c).id = contract.policy ∧ (policies c).required ≠ [] ∧
        ∀ q, q ∈ (policies c).required →
          q.scope.intent = contract.intent ∧ q.scope.metric = contract.metric ∧
            q.scope.policy = contract.policy :=
  contractOfPolicy_exact (policies c) contract

omit [DecidableEq T] in
/-- Characterization: a catalogue is compatible with a contract exactly
when every candidate in it carries that contract. -/
theorem compatible_exact (candidates : List T) (policies : T → Policy) (contract : Contract) :
    compatible candidates policies contract = true ↔
      ∀ c, c ∈ candidates → contractOf policies c = some contract := by
  simp [compatible, List.all_eq_true]

omit [DecidableEq T] in
/-- Rejection direction: one candidate carrying any other projection —
a different contract, or no contract at all — makes the checked entry
point refuse the catalogue under the named contract. -/
theorem compatible_rejects_mixed (candidates : List T) (policies : T → Policy)
    (contract : Contract) (c : T) (hc : c ∈ candidates)
    (hm : contractOf policies c ≠ some contract) :
    compatible candidates policies contract = false := by
  cases h : compatible candidates policies contract
  · rfl
  · exact absurd ((compatible_exact candidates policies contract).mp h c hc) hm

omit [DecidableEq T] in
/-- The homogeneous check holds exactly when the catalogue is empty or
some one contract is carried by every candidate in it. -/
theorem compatibleSelf_exact (candidates : List T) (policies : T → Policy) :
    compatibleSelf candidates policies = true ↔
      candidates = [] ∨ ∃ contract, compatible candidates policies contract = true := by
  cases candidates with
  | nil => simp [compatibleSelf]
  | cons c cs =>
      have hnone : contractOf policies c = none →
          compatibleSelf (c :: cs) policies = false := by
        intro hh; simp [compatibleSelf, hh]
      have hsome : ∀ k, contractOf policies c = some k →
          compatibleSelf (c :: cs) policies = compatible (c :: cs) policies k := by
        intro k hh; simp [compatibleSelf, hh]
      constructor
      · intro h
        cases hfirst : contractOf policies c with
        | none => rw [hnone hfirst] at h; simp at h
        | some contract =>
            exact Or.inr ⟨contract, by rw [← hsome contract hfirst]; exact h⟩
      · intro h
        cases h with
        | inl hnil => simp at hnil
        | inr hex =>
            obtain ⟨contract, hcomp⟩ := hex
            have hc := (compatible_exact (c :: cs) policies contract).mp hcomp c (by simp)
            rw [hsome contract hc]
            exact hcomp

omit [DecidableEq T] in
/-- Compatibility with a named contract implies the homogeneous check. -/
theorem compatibleSelf_of_compatible (candidates : List T) (policies : T → Policy)
    (contract : Contract) (h : compatible candidates policies contract = true) :
    compatibleSelf candidates policies = true :=
  (compatibleSelf_exact candidates policies).mpr
    (Or.inr ⟨contract, h⟩)

/-- The scoped optimum theorem, strengthened with the compatibility
admission precondition: an accepted certificate over a compatible
catalogue keeps every conclusion of `ScopedSelection.certified_scoped_nondominated_under_supplied_integer_cost`,
and additionally the designated candidate and every other candidate in
the catalogue carry the named contract. Mixed catalogues are refused by
`compatible_rejects_mixed` before this entry point can apply. -/
theorem certified_scoped_optimum_compatible (candidates : List T)
    (policies : T → Policy) (evidence : T → List Receipt) (axes : List Nat)
    (cost : T → Nat → Int) (x : T) (contract : Contract)
    (h : ScopedSelection.certificate candidates policies evidence axes cost x = true)
    (hcompat : compatible candidates policies contract = true) :
    (x ∈ candidates ∧ ScopedEvidence.qualify (policies x) (evidence x) = true ∧
    (∀ q, q ∈ (policies x).required →
      ∃ r, r ∈ evidence x ∧ r.scope = q.scope ∧ r.round = q.round ∧
        r.observedPass = true ∧ ∃ t, r.elapsed = some t ∧ t ≤ q.limit) ∧
    ∀ y, y ∈ candidates → ScopedEvidence.qualify (policies y) (evidence y) = true →
      ¬ ((∀ i, i ∈ axes → cost y i ≤ cost x i) ∧
         (∃ i, i ∈ axes ∧ cost y i < cost x i))) ∧
    contractOf policies x = some contract ∧
    ∀ c, c ∈ candidates → contractOf policies c = some contract := by
  have hbase := ScopedSelection.certified_scoped_nondominated_under_supplied_integer_cost candidates policies evidence
    axes cost x h
  have hall := (compatible_exact candidates policies contract).mp hcompat
  exact ⟨hbase, hall x hbase.1, hall⟩

-- Executable boundary controls (synthetic, not measurements).
-- A minimal two-candidate catalogue in the pilot's contract shape: the
-- candidates differ only in configuration (subject identity), while
-- policy, intent, and metric are shared. ScopedCampaign is not imported:
-- the repository ships no ScopedCampaign object file and its checker
-- compiles that module without one, so importing it would break the
-- standalone compile of this module.
def exampleScopeFor (c : Nat) : Scope := ⟨1, c, 1, 1, 1, 6, 7, 8⟩

def examplePolicyFor (c : Nat) : Policy :=
  ⟨7, [⟨exampleScopeFor c, 0, 100⟩, ⟨exampleScopeFor c, 1, 100⟩]⟩

def exampleCatalogue : List Nat := [0, 1]

def exampleContract : Contract := ⟨7, 6, 8⟩

/-- Negative-control fixture: candidate 1 measured under a different
metric identity, coherently in both of its requirements. -/
def exampleMetricPolicyFor (c : Nat) : Policy :=
  if c = 1 then
    ⟨7, [⟨{exampleScopeFor c with metric := 9}, 0, 100⟩,
      ⟨{exampleScopeFor c with metric := 9}, 1, 100⟩]⟩
  else examplePolicyFor c

/-- Negative-control fixture: candidate 1 measured under a different
policy identity, with its requirement scopes retied to that identity. -/
def examplePolicyIdPolicyFor (c : Nat) : Policy :=
  if c = 1 then
    ⟨9, [⟨{exampleScopeFor c with policy := 9}, 0, 100⟩,
      ⟨{exampleScopeFor c with policy := 9}, 1, 100⟩]⟩
  else examplePolicyFor c

#guard compatible exampleCatalogue examplePolicyFor exampleContract == true
#guard compatibleSelf exampleCatalogue examplePolicyFor == true
#guard compatible exampleCatalogue exampleMetricPolicyFor exampleContract == false
#guard compatibleSelf exampleCatalogue exampleMetricPolicyFor == false
#guard compatible exampleCatalogue examplePolicyIdPolicyFor exampleContract == false
#guard compatibleSelf exampleCatalogue examplePolicyIdPolicyFor == false
#guard compatible exampleCatalogue examplePolicyFor ⟨7, 6, 9⟩ == false
#guard compatible [] examplePolicyFor exampleContract == true

#print axioms contractOfPolicy_exact
#print axioms contractOf_exact
#print axioms compatible_exact
#print axioms compatible_rejects_mixed
#print axioms compatibleSelf_exact
#print axioms compatibleSelf_of_compatible
#print axioms certified_scoped_optimum_compatible
end ScopedCompatibility
