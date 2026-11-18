import Std
namespace PortableAdapter

structure Context where
  artifact : String
  lineage : String
  environment : String
  harness : String
  workload : String
  venue : String
  deriving DecidableEq, Repr

inductive Classification where
  | observed | inferred | proposed
  deriving DecidableEq, Repr
inductive Status where
  | pass | fail | skipped | error
  deriving DecidableEq, Repr
inductive Payload where
  | test (status : Status)
  | measurement (samples_ns : List Nat)
  deriving DecidableEq, Repr

structure Receipt where
  context : Context
  classification : Classification
  subject : String
  payload : Payload
  sourceDigest : String
  recordIndex : Nat
  authorityDigest : String
  id : String
  deriving DecidableEq, Repr

-- Authority is a fixed external input, not chosen by the submitted receipt.
structure Authority where
  context : Context
  digest : String
  passAtom : String → Option String
  failAtom : String → Option String
  measurementAtom : String → Option String

-- Raw syntax, canonical bytes, cryptographic identity and nonnegative integer
-- validation are parser obligations, not conclusions of this typed model.
def atom (a : Authority) (r : Receipt) : Option String :=
  match r.payload with
  | .test .pass => a.passAtom r.subject
  | .test .fail => a.failAtom r.subject
  | .test .skipped | .test .error => none
  | .measurement [] => none
  | .measurement (_ :: _) =>
    if a.measurementAtom r.subject = some ("measurement:" ++ r.subject)
    then some ("measurement:" ++ r.subject) else none

def valid (a : Authority) (r : Receipt) : Bool :=
  decide (r.context = a.context ∧ r.authorityDigest = a.digest ∧
    r.classification = .observed)

def live (a : Authority) (withdrawn : List String) (r : Receipt) : Bool :=
  valid a r && !withdrawn.contains r.id

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


-- Keep full receipts in the view, never merge equal atoms across lineage.
def normalize (a : Authority) (withdrawn : List String) (rs : List Receipt) : List Receipt :=
  unique (rs.filter (live a withdrawn))

def supports (a : Authority) (withdrawn : List String) (rs : List Receipt) :
    List (Receipt × String) :=
  (normalize a withdrawn rs).filterMap fun r => (atom a r).map (r, ·)

-- Independent declarative semantics: accepted source record, exact external
-- scope/authority, observed origin, no tombstone, authority-selected meaning.
def Meaning (a : Authority) (withdrawn : List String) (rs : List Receipt)
    (r : Receipt) (x : String) : Prop :=
  r ∈ rs ∧ r.context = a.context ∧ r.authorityDigest = a.digest ∧
  r.classification = .observed ∧ r.id ∉ withdrawn ∧ atom a r = some x

theorem normalize_exact (a : Authority) (ws : List String) (rs : List Receipt) (r : Receipt) :
    r ∈ normalize a ws rs ↔ r ∈ rs ∧ r.context = a.context ∧
    r.authorityDigest = a.digest ∧ r.classification = .observed ∧ r.id ∉ ws := by
  simp [normalize, mem_unique, live, valid, Bool.and_eq_true, and_assoc]

theorem supports_exact (a : Authority) (ws : List String) (rs : List Receipt)
    (r : Receipt) (x : String) : (r,x) ∈ supports a ws rs ↔ Meaning a ws rs r x := by
  simp only [supports, List.mem_filterMap]
  constructor
  · rintro ⟨r', hr, hx⟩
    cases ha : atom a r' with
    | none => simp [ha] at hx
    | some y =>
      simp only [ha, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hx
      rcases hx with ⟨rfl, rfl⟩
      exact ⟨(normalize_exact a ws rs r).mp hr |>.1,
        (normalize_exact a ws rs r).mp hr |>.2.1,
        (normalize_exact a ws rs r).mp hr |>.2.2.1,
        (normalize_exact a ws rs r).mp hr |>.2.2.2.1,
        (normalize_exact a ws rs r).mp hr |>.2.2.2.2, ha⟩
  · rintro ⟨hr,hc,ha,hk,hw,hx⟩
    exact ⟨r,(normalize_exact a ws rs r).mpr ⟨hr,hc,ha,hk,hw⟩, by simp [hx]⟩

theorem scope_preserved (a : Authority) (ws : List String) (rs : List Receipt)
    (r : Receipt) (x : String) (h : (r,x) ∈ supports a ws rs) :
    r.context = a.context ∧ r.authorityDigest = a.digest := by
  have h := (supports_exact a ws rs r x).mp h
  exact ⟨h.2.1,h.2.2.1⟩

theorem no_cross_lineage (a : Authority) (ws : List String) (rs : List Receipt)
    (r : Receipt) (x : String) (h : r.context.lineage ≠ a.context.lineage) :
    (r,x) ∉ supports a ws rs := by
  intro hm
  exact h (congrArg Context.lineage (scope_preserved a ws rs r x hm).1)

theorem no_promoted_proposal (a : Authority) (ws : List String) (rs : List Receipt)
    (r : Receipt) (x : String) (h : r.classification ≠ .observed) :
    (r,x) ∉ supports a ws rs := by
  intro hm
  exact h ((supports_exact a ws rs r x).mp hm).2.2.2.1

theorem tombstone_blocks (a : Authority) (ws : List String) (rs : List Receipt)
    (r : Receipt) (x : String) (h : r.id ∈ ws) : (r,x) ∉ supports a ws rs := by
  intro hm
  exact ((supports_exact a ws rs r x).mp hm).2.2.2.2.1 h

theorem duplicate_idempotent (a : Authority) (ws : List String) (rs : List Receipt)
    (r : Receipt) (x : String) :
    (r,x) ∈ supports a ws (rs ++ rs) ↔ (r,x) ∈ supports a ws rs := by
  simp [supports_exact, Meaning]

theorem merge_commutes (a : Authority) (ws : List String) (xs ys : List Receipt)
    (r : Receipt) (x : String) :
    (r,x) ∈ supports a ws (xs ++ ys) ↔ (r,x) ∈ supports a ws (ys ++ xs) := by
  simp only [supports_exact, Meaning, List.mem_append]
  exact and_congr_left (fun _ => or_comm)

theorem support_union (a : Authority) (ws : List String) (xs ys : List Receipt)
    (r : Receipt) (x : String) :
    (r,x) ∈ supports a ws (xs ++ ys) ↔
    (r,x) ∈ supports a ws xs ∨ (r,x) ∈ supports a ws ys := by
  simp only [supports_exact, Meaning, List.mem_append]
  exact or_and_right

theorem withdrawals_only_remove (a : Authority) (ws more : List String) (rs : List Receipt)
    (r : Receipt) (x : String) :
    (r,x) ∈ supports a (ws ++ more) rs → (r,x) ∈ supports a ws rs := by
  simp only [supports_exact, Meaning, List.mem_append, not_or]
  rintro ⟨hr,hc,ha,hk,hw,hx⟩
  exact ⟨hr,hc,ha,hk,hw.1,hx⟩

-- Inferred hypergraph nodes have an actual derivation rooted in admitted
-- receipts. An AND hyperedge requires every premise, not any one premise.
structure Edge where
  premises : List String
  conclusion : String
inductive Derives (roots : String → Prop) (edges : List Edge) : String → Prop where
  | root {x} : roots x → Derives roots edges x
  | step {e} : e ∈ edges → (∀ p ∈ e.premises, Derives roots edges p) →
      Derives roots edges e.conclusion

def roots (a : Authority) (ws : List String) (rs : List Receipt) (x : String) : Prop :=
  ∃ r, (r,x) ∈ supports a ws rs

theorem derivation_transport {R S : String → Prop} {edges : List Edge}
    (h : ∀ x, R x → S x) {x} (hx : Derives R edges x) : Derives S edges x := by
  induction hx with
  | root hr => exact .root (h _ hr)
  | step he _ ih => exact .step he ih

theorem merge_derivation_preserved (a : Authority) (ws : List String)
    (xs ys : List Receipt) (es : List Edge) (x : String)
    (h : Derives (roots a ws xs) es x) : Derives (roots a ws (xs ++ ys)) es x := by
  apply derivation_transport _ h
  intro y hy
  obtain ⟨r,hr⟩ := hy
  exact ⟨r,(support_union a ws xs ys r y).mpr (Or.inl hr)⟩

theorem withdrawal_derivation_subset (a : Authority) (ws more : List String)
    (rs : List Receipt) (es : List Edge) (x : String)
    (h : Derives (roots a (ws ++ more) rs) es x) : Derives (roots a ws rs) es x := by
  apply derivation_transport _ h
  intro y hy
  obtain ⟨r,hr⟩ := hy
  exact ⟨r,withdrawals_only_remove a ws more rs r y hr⟩

theorem measurement_not_performance (a : Authority) (r : Receipt) (ns : List Nat)
    (hp : r.payload = .measurement ns) (x : String) (h : atom a r = some x) :
    x = "measurement:" ++ r.subject := by
  cases ns with
  | nil => simp [atom, hp] at h
  | cons n ns =>
    simp only [atom, hp] at h
    split at h
    · exact (Option.some.inj h).symm
    · contradiction

#print axioms mem_unique
#print axioms normalize_exact
#print axioms supports_exact
#print axioms scope_preserved
#print axioms no_cross_lineage
#print axioms no_promoted_proposal
#print axioms tombstone_blocks
#print axioms duplicate_idempotent
#print axioms merge_commutes
#print axioms support_union
#print axioms withdrawals_only_remove
#print axioms derivation_transport
#print axioms merge_derivation_preserved
#print axioms withdrawal_derivation_subset
#print axioms measurement_not_performance
end PortableAdapter
