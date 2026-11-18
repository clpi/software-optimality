import EligibleSchedules
import Std
namespace ScopedEvidence

-- Opaque canonical identifiers. Equality binds claims; it does not prove hash authenticity.
structure Scope where
  artifact : Nat
  configuration : Nat
  lineage : Nat
  venue : Nat
  harness : Nat
  intent : Nat
  policy : Nat
  metric : Nat -- e.g. complete-suite elapsed versus one subprocess elapsed
  deriving DecidableEq, Repr

structure Requirement where
  scope : Scope
  round : Nat
  limit : Nat
  deriving DecidableEq, Repr

structure Receipt where
  id : Nat
  scope : Scope
  round : Nat
  observedPass : Bool
  elapsed : Option Nat
  deriving DecidableEq, Repr

structure Policy where
  id : Nat
  required : List Requirement
  deriving DecidableEq, Repr

def matchingKey (q : Requirement) (r : Receipt) : Bool :=
  decide (r.scope = q.scope ∧ r.round = q.round)

def checkRequirement (q : Requirement) (receipts : List Receipt) : Bool :=
  match receipts.filter (matchingKey q) with
  | [r] => r.observedPass && EligibleSchedules.timingOK r.elapsed q.limit
  | _ => false

theorem checkRequirement_exact (q : Requirement) (receipts : List Receipt) :
    checkRequirement q receipts = true ↔
      ∃ r, receipts.filter (matchingKey q) = [r] ∧ r.observedPass = true ∧
        ∃ t, r.elapsed = some t ∧ t ≤ q.limit := by
  unfold checkRequirement
  generalize hh : receipts.filter (matchingKey q) = hits
  cases hits with
  | nil => simp
  | cons r rs =>
    cases rs with
    | nil => simp [EligibleSchedules.timingOK_exact]
    | cons a rest => simp

theorem accepted_receipt_is_scoped (q : Requirement) (receipts : List Receipt)
    (h : checkRequirement q receipts = true) :
    ∃ r, r ∈ receipts ∧ r.scope = q.scope ∧ r.round = q.round ∧
      r.observedPass = true ∧ ∃ t, r.elapsed = some t ∧ t ≤ q.limit := by
  obtain ⟨r, hs, hp, ht⟩ := (checkRequirement_exact q receipts).mp h
  have hm : r ∈ receipts.filter (matchingKey q) := hs ▸ List.mem_cons_self
  obtain ⟨hr, hmatch⟩ := List.mem_filter.mp hm
  have he : r.scope = q.scope ∧ r.round = q.round := of_decide_eq_true hmatch
  exact ⟨r,hr,he.1,he.2,hp,ht⟩

-- Requirements must be nonempty, unambiguous, and tied to the named policy.
-- The supplied selected receipt set must have the same size and unique receipt IDs.
def qualify (policy : Policy) (receipts : List Receipt) : Bool :=
  decide (0 < policy.required.length) &&
  decide ((policy.required.map (fun q => (q.scope,q.round))).Nodup) &&
  policy.required.all (fun q => decide (q.scope.policy = policy.id)) &&
  decide (receipts.length = policy.required.length) &&
  decide ((receipts.map Receipt.id).Nodup) &&
  policy.required.all (fun q => checkRequirement q receipts)

theorem qualify_exact (policy : Policy) (receipts : List Receipt) :
    qualify policy receipts = true ↔
      0 < policy.required.length ∧
      (policy.required.map (fun q => (q.scope,q.round))).Nodup ∧
      (∀ q, q ∈ policy.required → q.scope.policy = policy.id) ∧
      receipts.length = policy.required.length ∧
      (receipts.map Receipt.id).Nodup ∧
      ∀ q, q ∈ policy.required → checkRequirement q receipts = true := by
  simp only [qualify, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, and_assoc]

-- Successful qualification carries a scoped timing witness for every obligation.
theorem qualification_witnesses (policy : Policy) (receipts : List Receipt)
    (h : qualify policy receipts = true) :
    ∀ q, q ∈ policy.required →
      ∃ r, r ∈ receipts ∧ r.scope = q.scope ∧ r.round = q.round ∧
        r.observedPass = true ∧ ∃ t, r.elapsed = some t ∧ t ≤ q.limit := by
  have hq := (qualify_exact policy receipts).mp h
  intro q hmem
  exact accepted_receipt_is_scoped q receipts (hq.2.2.2.2.2 q hmem)

-- Matching conflicting duplicates are rejected even if one receipt reports success.
theorem duplicate_match_rejected (q : Requirement) (receipts : List Receipt)
    (a b : Receipt) (rest : List Receipt)
    (h : receipts.filter (matchingKey q) = a :: b :: rest) :
    checkRequirement q receipts = false := by
  simp [checkRequirement, h]

-- No implicit qualification across content/lineage/venue/harness/policy/metric scopes.
theorem wrong_scope_rejected (q : Requirement) (receipts : List Receipt)
    (h : ∀ r, r ∈ receipts → r.scope ≠ q.scope) :
    checkRequirement q receipts = false := by
  cases hc : checkRequirement q receipts
  · rfl
  · obtain ⟨r, hr, hs, _⟩ := accepted_receipt_is_scoped q receipts hc
    exact False.elim (h r hr hs)

-- Semantic interpretation remains an explicit external validation obligation.
theorem qualification_sound_relative (policy : Policy) (receipts : List Receipt)
    (Holds : Requirement → Prop)
    (validation : ∀ q, q ∈ policy.required → ∀ r, r ∈ receipts →
      r.scope = q.scope → r.round = q.round → r.observedPass = true →
      (∃ t, r.elapsed = some t ∧ t ≤ q.limit) → Holds q)
    (h : qualify policy receipts = true) :
    ∀ q, q ∈ policy.required → Holds q := by
  intro q hq
  obtain ⟨r, hr, hs, hd, hp, ht⟩ := qualification_witnesses policy receipts h q hq
  exact validation q hq r hr hs hd hp ht

-- Executable boundary controls (synthetic, not measurements).
def exampleScope : Scope := ⟨1,2,3,4,5,6,7,8⟩
def examplePolicy : Policy := ⟨7,[⟨exampleScope,0,100⟩,⟨exampleScope,1,100⟩]⟩
def receipt0 : Receipt := ⟨10,exampleScope,0,true,some 90⟩
def receipt1 : Receipt := ⟨11,exampleScope,1,true,some 100⟩
#guard qualify examplePolicy [receipt0,receipt1] == true
#guard qualify examplePolicy [receipt0] == false
#guard qualify examplePolicy [receipt0,receipt0] == false
#guard qualify examplePolicy [receipt0,{receipt1 with id := 10}] == false
#guard qualify examplePolicy [receipt0,{receipt1 with elapsed := some 101}] == false
#guard qualify examplePolicy [receipt0,{receipt1 with scope := {exampleScope with metric := 9}}] == false
#guard qualify {examplePolicy with id := 9} [receipt0,receipt1] == false
#guard checkRequirement ⟨exampleScope,0,100⟩ [receipt0,{receipt0 with id := 12, observedPass := false}] == false

#print axioms checkRequirement_exact
#print axioms accepted_receipt_is_scoped
#print axioms qualify_exact
#print axioms qualification_witnesses
#print axioms duplicate_match_rejected
#print axioms wrong_scope_rejected
#print axioms qualification_sound_relative
end ScopedEvidence
