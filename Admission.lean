import Std
namespace Admission
structure Key where
  lineage : Nat
  content : Nat
  scope : Nat
  support : Nat
  deriving DecidableEq, Repr
structure Payload where
  subject : Nat
  polarity : Bool
  evidence : Nat
  deriving DecidableEq, Repr
inductive Event where
  | claim (key : Key) (payload : Payload)
  | withdraw (key : Key)
  deriving DecidableEq, Repr

def admitted (authorize : Event → Bool) (ledger : List Event) (e : Event) : Prop :=
  e ∈ ledger ∧ authorize e = true

def compatible (k : Key) (p : Payload) : Event → Prop
  | .claim k' p' => k' = k → p' = p
  | .withdraw _ => True
instance (k : Key) (p : Payload) (e : Event) : Decidable (compatible k p e) := by
  cases e <;> simp only [compatible] <;> infer_instance

def live (authorize : Event → Bool) (ledger : List Event) (k : Key) (p : Payload) : Prop :=
  admitted authorize ledger (.claim k p) ∧
  ¬ admitted authorize ledger (.withdraw k) ∧
  ∀ e ∈ ledger, authorize e = true → compatible k p e
instance (authorize : Event → Bool) (ledger : List Event) (k : Key) (p : Payload) :
    Decidable (live authorize ledger k p) := by
  letI : Decidable (∀ e ∈ ledger, authorize e = true → compatible k p e) :=
    List.decidableBAll (fun e => authorize e = true → compatible k p e) ledger
  unfold live admitted
  infer_instance

def checkLive (authorize : Event → Bool) (ledger : List Event) (k : Key) (p : Payload) : Bool :=
  decide (live authorize ledger k p)

theorem checkLive_correct (authorize : Event → Bool) (ledger : List Event) (k : Key) (p : Payload) :
    checkLive authorize ledger k p = true ↔ live authorize ledger k p := by
  simp [checkLive]

theorem extensional (authorize : Event → Bool) (xs ys : List Event)
    (same : ∀ e, e ∈ xs ↔ e ∈ ys) (k : Key) (p : Payload) :
    live authorize xs k p ↔ live authorize ys k p := by
  simp only [live, admitted]
  constructor
  · rintro ⟨hc, hw, hf⟩
    exact ⟨⟨(same _).mp hc.1, hc.2⟩,
      fun h => hw ⟨(same _).mpr h.1, h.2⟩,
      fun e he ha => hf e ((same e).mpr he) ha⟩
  · rintro ⟨hc, hw, hf⟩
    exact ⟨⟨(same _).mpr hc.1, hc.2⟩,
      fun h => hw ⟨(same _).mp h.1, h.2⟩,
      fun e he ha => hf e ((same e).mp he) ha⟩

theorem permutation_invariant (authorize : Event → Bool) {xs ys : List Event}
    (h : xs.Perm ys) (k : Key) (p : Payload) :
    checkLive authorize xs k p = checkLive authorize ys k p := by
  simp only [checkLive]
  congr 1
  exact propext (extensional authorize xs ys (fun _ => h.mem_iff) k p)

theorem merge_commutes (authorize : Event → Bool) (xs ys : List Event) (k : Key) (p : Payload) :
    checkLive authorize (xs ++ ys) k p = checkLive authorize (ys ++ xs) k p := by
  apply permutation_invariant
  exact List.perm_append_comm

theorem duplicate_idempotent (authorize : Event → Bool) (xs : List Event) (k : Key) (p : Payload) :
    checkLive authorize (xs ++ xs) k p = checkLive authorize xs k p := by
  simp only [checkLive]
  congr 1
  apply propext
  apply extensional
  simp

theorem payload_unique (authorize : Event → Bool) (ledger : List Event) (k : Key) (p q : Payload)
    (hp : live authorize ledger k p) (hq : live authorize ledger k q) : p = q := by
  exact (hp.2.2 (.claim k q) hq.1.1 hq.1.2 rfl).symm

theorem authorized_withdrawal_blocks (authorize : Event → Bool) (ledger : List Event) (k : Key) (p : Payload)
    (hw : admitted authorize ledger (.withdraw k)) : ¬ live authorize ledger k p := by
  intro h
  exact h.2.1 hw

theorem contradictory_claims_block (authorize : Event → Bool) (ledger : List Event) (k : Key) (p q : Payload)
    (hq : admitted authorize ledger (.claim k q)) (hne : q ≠ p) : ¬ live authorize ledger k p := by
  intro hp
  exact hne (hp.2.2 (.claim k q) hq.1 hq.2 rfl)

-- Withdrawals are permanent for this exact key, including its support identifier.
-- A reissued claim needs a fresh support identifier; it is not a resurrection.
theorem withdrawal_survives_append (authorize : Event → Bool) (xs ys : List Event) (k : Key) (p : Payload)
    (hw : admitted authorize xs (.withdraw k)) : ¬ live authorize (xs ++ ys) k p := by
  apply authorized_withdrawal_blocks
  exact ⟨List.mem_append_left _ hw.1, hw.2⟩

-- This is a derived finite set represented as a duplicate-free list. List order
-- is deliberately not the canonical serialization; extensional content is.
def candidates (ledger : List Event) : List (Key × Payload) :=
  ledger.filterMap (fun e => match e with
    | .claim k p => some (k, p)
    | .withdraw _ => none)
def unique {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | x :: xs => if x ∈ xs then unique xs else x :: unique xs

theorem mem_unique {α : Type} [DecidableEq α] (xs : List α) (a : α) :
    a ∈ unique xs ↔ a ∈ xs := by
  induction xs with
  | nil => simp [unique]
  | cons x xs ih =>
    simp only [unique]
    split
    · rename_i hx
      rw [ih, List.mem_cons]
      constructor
      · exact Or.inr
      · intro h
        rcases h with rfl | h
        · exact hx
        · exact h
    · simp [List.mem_cons, ih]

theorem unique_nodup {α : Type} [DecidableEq α] (xs : List α) : (unique xs).Nodup := by
  induction xs with
  | nil => simp [unique]
  | cons x xs ih =>
    simp only [unique]
    split
    · exact ih
    · rename_i hx
      exact List.nodup_cons.mpr ⟨fun h => hx ((mem_unique xs x).mp h), ih⟩

def normalized (authorize : Event → Bool) (ledger : List Event) : List (Key × Payload) :=
  (unique (candidates ledger)).filter (fun kp => checkLive authorize ledger kp.1 kp.2)

theorem mem_candidates (ledger : List Event) (k : Key) (p : Payload) :
    (k,p) ∈ candidates ledger ↔ Event.claim k p ∈ ledger := by
  simp only [candidates, List.mem_filterMap]
  constructor
  · rintro ⟨e, he, hm⟩
    cases e with
    | withdraw _ => simp at hm
    | claim k' p' =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩
      exact he
  · intro h
    exact ⟨.claim k p, h, rfl⟩

theorem normalized_exact (authorize : Event → Bool) (ledger : List Event) (k : Key) (p : Payload) :
    (k,p) ∈ normalized authorize ledger ↔ live authorize ledger k p := by
  simp only [normalized, List.mem_filter, mem_unique, checkLive_correct, mem_candidates]
  exact ⟨fun h => h.2, fun h => ⟨h.1.1,h⟩⟩

theorem normalized_nodup (authorize : Event → Bool) (ledger : List Event) :
    (normalized authorize ledger).Nodup := by
  apply List.Pairwise.filter
  exact unique_nodup _

-- Accepted provenance, rather than raw delivery order or unauthorized messages,
-- is sufficient to determine the complete normalized support set.
theorem admitted_extensional (auth₁ auth₂ : Event → Bool) (xs ys : List Event)
    (same : ∀ e, admitted auth₁ xs e ↔ admitted auth₂ ys e) (k : Key) (p : Payload) :
    live auth₁ xs k p ↔ live auth₂ ys k p := by
  constructor
  · rintro ⟨hc, hw, hf⟩
    refine ⟨(same _).mp hc, fun h => hw ((same _).mpr h), ?_⟩
    intro e he ha
    have h := (same e).mpr ⟨he, ha⟩
    exact hf e h.1 h.2
  · rintro ⟨hc, hw, hf⟩
    refine ⟨(same _).mpr hc, fun h => hw ((same _).mp h), ?_⟩
    intro e he ha
    have h := (same e).mp ⟨he, ha⟩
    exact hf e h.1 h.2

theorem unauthorized_event_ignored (auth : Event → Bool) (ledger : List Event)
    (e : Event) (denied : auth e = false) (k : Key) (p : Payload) :
    live auth (e :: ledger) k p ↔ live auth ledger k p := by
  apply admitted_extensional
  intro x
  simp only [admitted, List.mem_cons]
  constructor
  · rintro ⟨hx, ha⟩
    rcases hx with rfl | hx
    · simp [denied] at ha
    · exact ⟨hx,ha⟩
  · rintro ⟨hx,ha⟩
    exact ⟨Or.inr hx,ha⟩

#print axioms normalized_exact
#print axioms normalized_nodup
#print axioms duplicate_idempotent
#print axioms payload_unique
#print axioms withdrawal_survives_append
#print axioms unauthorized_event_ignored

-- Normalized views cannot be merged by union: a newly arrived withdrawal or
-- conflicting payload can invalidate a previously live support. Merge raw
-- append-only events, then normalize at the named authorization snapshot.
end Admission
