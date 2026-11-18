import ScopedEvidence
import Std
namespace EvidenceTransport

-- EvidenceTransport: the deduplication bridge between a raw append-only
-- delivery ledger and the selected evidence set that ScopedEvidence.qualify
-- checks.
--
-- Proven in this module:
-- * dedupe keeps the first delivery of each receipt identity
--   (ScopedEvidence.Receipt.id) and drops later deliveries of an identity
--   already seen.
-- * Identity-level membership is exact with no side condition: an identity
--   occurs in dedupe L exactly when it occurs in L (id_mem_dedupe).
-- * Receipt-level membership is stated under the explicit hypothesis
--   idsDetermine L: in L, one identity determines one receipt. Under that
--   hypothesis a dropped later delivery is value-equal to the kept first
--   delivery, so r ∈ dedupe L ↔ r ∈ L holds on the nose (mem_dedupe).
--   Without the hypothesis that equivalence is false for a conflicting
--   later delivery, and this module does not claim it: dedupe keeps the
--   first delivery, a conflicting later delivery is dropped, and the drop
--   stays detectable by comparing dedupe L against L (guards below).
-- * (dedupe L).map Receipt.id is duplicate-free (nodup_ids), dedupe is
--   idempotent (dedupe_idempotent), and dedupe is the identity on lists
--   whose identities are already unique (dedupe_of_nodup).
-- * Bridge, exact form (qualify_dedupe_iff): under idsDetermine L,
--   qualify policy (dedupe L) = true is equivalent to the qualify_exact
--   contract at the deduplicated list with the receipt side restated over
--   the raw ledger: the policy side and the distinct-identity count are
--   unchanged, and each obligation holds exactly when the raw ledger
--   contains a passing, in-limit receipt for it whose identity is the
--   only matching identity in the ledger (all deliveries of that identity
--   are then value-equal, by the hypothesis). The duplicate-free identity
--   conjunct of qualify_exact is discharged once and for all by nodup_ids
--   (qualify_dedupe_exact, no hypothesis), and every witness of a
--   transported qualification is an actual raw delivery
--   (transport_witnesses_in_raw, no hypothesis).
--
-- Not claimed: that transport validates conflicting duplicates. When two
-- deliveries share an identity but differ in content, dedupe keeps the
-- first and the transported verdict is the verdict on that first delivery
-- alone; it can differ from the verdict the conflicting content would
-- need, and the conflict remains visible in the raw ledger. Authenticity
-- of receipts, policy-byte binding, and ingestion fidelity are separate
-- obligations, exactly as in ScopedEvidence.

/-- Auxiliary deduplication carrying the identities already seen. Keeps the
first delivery of each identity and drops later deliveries of an identity
in `seen` or delivered earlier in the list. -/
def dedupeAux (seen : List Nat) : List ScopedEvidence.Receipt → List ScopedEvidence.Receipt
  | [] => []
  | r :: rest =>
    if r.id ∈ seen then dedupeAux seen rest
    else r :: dedupeAux (r.id :: seen) rest

/-- Deduplicate a raw delivery ledger by receipt identity: the first
delivery of each `Receipt.id` is kept, later deliveries of an identity
already seen are dropped. -/
def dedupe (L : List ScopedEvidence.Receipt) : List ScopedEvidence.Receipt :=
  dedupeAux [] L

/-- In `L`, one receipt identity determines one receipt: any two deliveries
in `L` sharing an identity are value-equal. This is the exact hypothesis
under which duplicate deliveries are identical duplicates. -/
def idsDetermine (L : List ScopedEvidence.Receipt) : Prop :=
  ∀ r₁ ∈ L, ∀ r₂ ∈ L, r₁.id = r₂.id → r₁ = r₂

theorem dedupeAux_subset : ∀ (seen : List Nat) (L : List ScopedEvidence.Receipt)
    (r : ScopedEvidence.Receipt), r ∈ dedupeAux seen L → r ∈ L := by
  intro seen L
  induction L generalizing seen with
  | nil =>
    intro r hr
    change r ∈ ([] : List ScopedEvidence.Receipt) at hr
    cases hr
  | cons a rest ih =>
    intro r hr
    have step : dedupeAux seen (a :: rest) =
        if a.id ∈ seen then dedupeAux seen rest
        else a :: dedupeAux (a.id :: seen) rest := rfl
    rw [step] at hr
    by_cases h : a.id ∈ seen
    · rw [if_pos h] at hr
      exact List.mem_cons_of_mem a (ih seen r hr)
    · rw [if_neg h] at hr
      rw [List.mem_cons] at hr ⊢
      rcases hr with rfl | hr
      · exact Or.inl rfl
      · exact Or.inr (ih _ r hr)

/-- Transport invents no receipts: every retained receipt was delivered. -/
theorem dedupe_subset (L : List ScopedEvidence.Receipt) (r : ScopedEvidence.Receipt) :
    r ∈ dedupe L → r ∈ L :=
  dedupeAux_subset [] L r

theorem dedupeAux_representative : ∀ (seen : List Nat) (L : List ScopedEvidence.Receipt)
    (s : ScopedEvidence.Receipt), s ∈ L → s.id ∉ seen →
    ∃ s₀, s₀ ∈ dedupeAux seen L ∧ s₀.id = s.id ∧ s₀ ∈ L := by
  intro seen L
  induction L generalizing seen with
  | nil => intro s hs; simp at hs
  | cons a rest ih =>
    intro s hs hseen
    rw [List.mem_cons] at hs
    have step : dedupeAux seen (a :: rest) =
        if a.id ∈ seen then dedupeAux seen rest
        else a :: dedupeAux (a.id :: seen) rest := rfl
    by_cases h : a.id ∈ seen
    · have hsrest : s ∈ rest := by
        rcases hs with rfl | hs'
        · exact absurd h hseen
        · exact hs'
      obtain ⟨s₀, hs₀, hid, hs₀L⟩ := ih seen s hsrest hseen
      refine ⟨s₀, ?_, hid, List.mem_cons_of_mem a hs₀L⟩
      rw [step, if_pos h]
      exact hs₀
    · by_cases hid : s.id = a.id
      · refine ⟨a, ?_, hid.symm, List.mem_cons_self⟩
        rw [step, if_neg h]
        exact List.mem_cons_self
      · have hsrest : s ∈ rest := by
          rcases hs with rfl | hs'
          · exact absurd rfl hid
          · exact hs'
        have hseen' : s.id ∉ a.id :: seen := by
          intro hm
          rw [List.mem_cons] at hm
          rcases hm with h1 | h2
          · exact hid h1
          · exact hseen h2
        obtain ⟨s₀, hs₀, hid0, hs₀L⟩ := ih (a.id :: seen) s hsrest hseen'
        refine ⟨s₀, ?_, hid0, List.mem_cons_of_mem a hs₀L⟩
        rw [step, if_neg h]
        exact List.mem_cons_of_mem a hs₀

theorem dedupeAux_nodup_ids : ∀ (seen : List Nat) (L : List ScopedEvidence.Receipt),
    seen.Nodup →
    ((dedupeAux seen L).map ScopedEvidence.Receipt.id).Nodup ∧
    ∀ i ∈ (dedupeAux seen L).map ScopedEvidence.Receipt.id, i ∉ seen := by
  intro seen L
  induction L generalizing seen with
  | nil =>
    intro _
    refine ⟨List.nodup_nil, ?_⟩
    intro i hi
    simp only [dedupeAux, List.map_nil] at hi
    cases hi
  | cons a rest ih =>
    intro hseen
    have step : dedupeAux seen (a :: rest) =
        if a.id ∈ seen then dedupeAux seen rest
        else a :: dedupeAux (a.id :: seen) rest := rfl
    by_cases h : a.id ∈ seen
    · rw [step, if_pos h]
      exact ih seen hseen
    · have hseen' : (a.id :: seen).Nodup := List.nodup_cons.mpr ⟨h, hseen⟩
      obtain ⟨hnd, hdisj⟩ := ih (a.id :: seen) hseen'
      rw [step, if_neg h]
      refine ⟨?_, ?_⟩
      · rw [List.map_cons, List.nodup_cons]
        exact ⟨fun hm => hdisj a.id hm List.mem_cons_self, hnd⟩
      · intro i hi
        rw [List.map_cons, List.mem_cons] at hi
        rcases hi with rfl | hi
        · exact h
        · intro hise
          exact hdisj i hi (List.mem_cons_of_mem a.id hise)

/-- The transported selected set always has duplicate-free receipt
identities: dedupe discharges the unique-ID conjunct of qualify_exact. -/
theorem nodup_ids (L : List ScopedEvidence.Receipt) :
    ((dedupe L).map ScopedEvidence.Receipt.id).Nodup :=
  (dedupeAux_nodup_ids [] L List.nodup_nil).1

theorem nodup_of_nodup_ids : ∀ (l : List ScopedEvidence.Receipt),
    (l.map ScopedEvidence.Receipt.id).Nodup → l.Nodup := by
  intro l
  induction l with
  | nil => intro _; exact List.nodup_nil
  | cons a rest ih =>
    intro h
    rw [List.map_cons, List.nodup_cons] at h
    rw [List.nodup_cons]
    exact ⟨fun ha => h.1 (List.mem_map.mpr ⟨a, ha, rfl⟩), ih h.2⟩

/-- The transported selected set is also duplicate-free as a list of
receipt values, since its identities are. -/
theorem dedupe_nodup (L : List ScopedEvidence.Receipt) : (dedupe L).Nodup :=
  nodup_of_nodup_ids (dedupe L) (nodup_ids L)

theorem dedupeAux_of_nodup : ∀ (seen : List Nat) (L : List ScopedEvidence.Receipt),
    (L.map ScopedEvidence.Receipt.id).Nodup → (∀ r ∈ L, r.id ∉ seen) →
    dedupeAux seen L = L := by
  intro seen L
  induction L generalizing seen with
  | nil => intro _ _; rfl
  | cons a rest ih =>
    intro hnd hseen
    have step : dedupeAux seen (a :: rest) =
        if a.id ∈ seen then dedupeAux seen rest
        else a :: dedupeAux (a.id :: seen) rest := rfl
    have ha : a.id ∉ seen := hseen a List.mem_cons_self
    rw [step, if_neg ha]
    have hnd' : (rest.map ScopedEvidence.Receipt.id).Nodup ∧
        a.id ∉ rest.map ScopedEvidence.Receipt.id := by
      rw [List.map_cons, List.nodup_cons] at hnd
      exact ⟨hnd.2, hnd.1⟩
    congr 1
    refine ih _ hnd'.1 ?_
    intro r hr hmem
    rw [List.mem_cons] at hmem
    rcases hmem with h1 | h2
    · exact hnd'.2 (List.mem_map.mpr ⟨r, hr, h1⟩)
    · exact hseen r (List.mem_cons_of_mem a hr) h2

/-- A ledger whose receipt identities are already unique is unchanged by
transport. -/
theorem dedupe_of_nodup (L : List ScopedEvidence.Receipt)
    (h : (L.map ScopedEvidence.Receipt.id).Nodup) : dedupe L = L :=
  dedupeAux_of_nodup [] L h (fun r _ => by simp)

/-- Transport is idempotent: deduplicating a deduplicated ledger changes
nothing. -/
theorem dedupe_idempotent (L : List ScopedEvidence.Receipt) :
    dedupe (dedupe L) = dedupe L :=
  dedupeAux_of_nodup [] (dedupe L) (nodup_ids L) (fun r _ => by simp)

/-- Identity-level membership is exact with no side condition: an identity
is delivered in the transported set exactly when it was delivered in the
raw ledger. -/
theorem id_mem_dedupe (L : List ScopedEvidence.Receipt) (i : Nat) :
    i ∈ (dedupe L).map ScopedEvidence.Receipt.id ↔
    i ∈ L.map ScopedEvidence.Receipt.id := by
  constructor
  · intro hi
    obtain ⟨r, hr, hri⟩ := List.mem_map.mp hi
    exact List.mem_map.mpr ⟨r, dedupe_subset L r hr, hri⟩
  · intro hi
    obtain ⟨s, hs, hsi⟩ := List.mem_map.mp hi
    obtain ⟨s₀, hs₀, hid, -⟩ := dedupeAux_representative [] L s hs (by simp)
    exact List.mem_map.mpr ⟨s₀, hs₀, hid.trans hsi⟩

/-- Receipt-level membership, under the hypothesis that identities
determine receipts in `L`: a receipt is in the transported set exactly
when it was delivered in the raw ledger. The hypothesis is what makes
this true: a dropped later delivery is value-equal to the kept first
delivery, so it remains a member by value. -/
theorem mem_dedupe (L : List ScopedEvidence.Receipt) (H : idsDetermine L)
    (r : ScopedEvidence.Receipt) :
    r ∈ dedupe L ↔ r ∈ L := by
  constructor
  · exact dedupe_subset L r
  · intro hr
    obtain ⟨s₀, hs₀, hid, hs₀L⟩ := dedupeAux_representative [] L r hr (by simp)
    have hsr : s₀ = r := H s₀ hs₀L r hr hid
    rwa [hsr] at hs₀

theorem eq_singleton_of_nodup (l : List ScopedEvidence.Receipt)
    (r : ScopedEvidence.Receipt) (hnd : l.Nodup) (hr : r ∈ l)
    (hall : ∀ x ∈ l, x = r) : l = [r] := by
  cases l with
  | nil => simp at hr
  | cons a rest =>
    cases rest with
    | nil =>
      have ha : a = r := hall a List.mem_cons_self
      rw [ha]
    | cons b rest =>
      have ha : a = r := hall a List.mem_cons_self
      have hb : b = r :=
        hall b (List.mem_cons_of_mem a List.mem_cons_self)
      rw [List.nodup_cons] at hnd
      have hab : a = b := ha.trans hb.symm
      have hmem : a ∈ b :: rest := by
        rw [hab]
        exact List.mem_cons_self
      exact absurd hmem hnd.1

/-- One obligation, transported: under idsDetermine L, the deduplicated
set has exactly one matching receipt for `q` (passing and in limit)
exactly when the raw ledger contains a passing, in-limit receipt for `q`
whose identity is the only matching identity in the ledger. Every other
delivery of that identity is value-equal to it, by the hypothesis. -/
theorem checkRequirement_dedupe_exact (q : ScopedEvidence.Requirement)
    (L : List ScopedEvidence.Receipt) (H : idsDetermine L) :
    ScopedEvidence.checkRequirement q (dedupe L) = true ↔
      ∃ r, r ∈ L ∧ ScopedEvidence.matchingKey q r = true ∧
        r.observedPass = true ∧
        (∃ t, r.elapsed = some t ∧ t ≤ q.limit) ∧
        ∀ s ∈ L, ScopedEvidence.matchingKey q s = true → s.id = r.id := by
  constructor
  · intro h
    obtain ⟨r, hfilter, hpass, ht⟩ :=
      (ScopedEvidence.checkRequirement_exact q (dedupe L)).mp h
    have hmem : r ∈ (dedupe L).filter (ScopedEvidence.matchingKey q) := by
      rw [hfilter]
      exact List.mem_cons_self
    obtain ⟨hrD, hrm⟩ := List.mem_filter.mp hmem
    refine ⟨r, dedupe_subset L r hrD, hrm, hpass, ht, ?_⟩
    intro s hsL hsm
    have hsD : s ∈ dedupe L := (mem_dedupe L H s).mpr hsL
    have hsf : s ∈ (dedupe L).filter (ScopedEvidence.matchingKey q) :=
      List.mem_filter.mpr ⟨hsD, hsm⟩
    rw [hfilter] at hsf
    have hsr : s = r := by simpa using hsf
    rw [hsr]
  · rintro ⟨r, hrL, hmatch, hpass, ht, huniq⟩
    apply (ScopedEvidence.checkRequirement_exact q (dedupe L)).mpr
    refine ⟨r, ?_, hpass, ht⟩
    apply eq_singleton_of_nodup
    · exact List.Sublist.nodup List.filter_sublist (dedupe_nodup L)
    · exact List.mem_filter.mpr ⟨(mem_dedupe L H r).mpr hrL, hmatch⟩
    · intro x hx
      obtain ⟨hxD, hxm⟩ := List.mem_filter.mp hx
      have hxL : x ∈ L := dedupe_subset L x hxD
      exact H x hxL r hrL (huniq x hxL hxm)

/-- The qualify_exact contract at the transported set, with no side
condition: transport always discharges the duplicate-free identity
conjunct, so acceptance is exactly the policy side, the
distinct-identity count, and one matching receipt per obligation in the
deduplicated set. -/
theorem qualify_dedupe_exact (policy : ScopedEvidence.Policy)
    (L : List ScopedEvidence.Receipt) :
    ScopedEvidence.qualify policy (dedupe L) = true ↔
      0 < policy.required.length ∧
      (policy.required.map (fun q => (q.scope, q.round))).Nodup ∧
      (∀ q ∈ policy.required, q.scope.policy = policy.id) ∧
      (dedupe L).length = policy.required.length ∧
      ∀ q ∈ policy.required, ScopedEvidence.checkRequirement q (dedupe L) = true := by
  constructor
  · intro h
    obtain ⟨h1, h2, h3, h4, -, h6⟩ :=
      (ScopedEvidence.qualify_exact policy (dedupe L)).mp h
    exact ⟨h1, h2, h3, h4, h6⟩
  · intro h
    obtain ⟨h1, h2, h3, h4, h6⟩ := h
    exact (ScopedEvidence.qualify_exact policy (dedupe L)).mpr
      ⟨h1, h2, h3, h4, nodup_ids L, h6⟩

/-- The bridge theorem. Under idsDetermine L (identities determine
receipts in the raw ledger, i.e. all duplicate deliveries are identical),
qualification of the transported set is exactly the qualify_exact
contract with its receipt side restated over the raw ledger: the policy
side and the distinct-identity count are as in qualify_dedupe_exact, and
each obligation holds exactly when the raw ledger contains a passing,
in-limit receipt for it whose identity is the only matching identity in
the ledger. -/
theorem qualify_dedupe_iff (policy : ScopedEvidence.Policy)
    (L : List ScopedEvidence.Receipt) (H : idsDetermine L) :
    ScopedEvidence.qualify policy (dedupe L) = true ↔
      0 < policy.required.length ∧
      (policy.required.map (fun q => (q.scope, q.round))).Nodup ∧
      (∀ q ∈ policy.required, q.scope.policy = policy.id) ∧
      (dedupe L).length = policy.required.length ∧
      ∀ q ∈ policy.required, ∃ r, r ∈ L ∧
        ScopedEvidence.matchingKey q r = true ∧ r.observedPass = true ∧
        (∃ t, r.elapsed = some t ∧ t ≤ q.limit) ∧
        ∀ s ∈ L, ScopedEvidence.matchingKey q s = true → s.id = r.id := by
  rw [qualify_dedupe_exact]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h1, h2, h3, h4, fun q hq =>
      (checkRequirement_dedupe_exact q L H).mp (h5 q hq)⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h1, h2, h3, h4, fun q hq =>
      (checkRequirement_dedupe_exact q L H).mpr (h5 q hq)⟩

/-- Soundness of transport, with no side condition: every obligation
witness of a transported qualification is an actual raw delivery, with
its scope, round, pass flag, and measured bound intact. -/
theorem transport_witnesses_in_raw (policy : ScopedEvidence.Policy)
    (L : List ScopedEvidence.Receipt)
    (h : ScopedEvidence.qualify policy (dedupe L) = true) :
    ∀ q ∈ policy.required, ∃ r, r ∈ L ∧ r.scope = q.scope ∧
      r.round = q.round ∧ r.observedPass = true ∧
      ∃ t, r.elapsed = some t ∧ t ≤ q.limit := by
  intro q hq
  obtain ⟨r, hr, hs, hd, hp, ht⟩ :=
    ScopedEvidence.qualification_witnesses policy (dedupe L) h q hq
  exact ⟨r, dedupe_subset L r hr, hs, hd, hp, ht⟩

-- Executable boundary controls (synthetic, not measurements).
/-- A one-obligation policy over the ScopedEvidence example scope. -/
def singlePolicy : ScopedEvidence.Policy :=
  ⟨7, [⟨ScopedEvidence.exampleScope, 0, 100⟩]⟩

/-- Same identity as ScopedEvidence.receipt0, conflicting content: the
recorded pass flag is flipped. -/
def conflictingReceipt : ScopedEvidence.Receipt :=
  { ScopedEvidence.receipt0 with observedPass := false }

-- Identical duplicate delivery normalizes away; first delivery is kept.
#guard decide (dedupe [ScopedEvidence.receipt0, ScopedEvidence.receipt0]
  = [ScopedEvidence.receipt0]) == true
#guard decide (dedupe [ScopedEvidence.receipt0, ScopedEvidence.receipt1,
  ScopedEvidence.receipt1]
  = [ScopedEvidence.receipt0, ScopedEvidence.receipt1]) == true
-- Already-unique ledgers are unchanged, and transport is idempotent.
#guard decide (dedupe [ScopedEvidence.receipt0, ScopedEvidence.receipt1]
  = [ScopedEvidence.receipt0, ScopedEvidence.receipt1]) == true
#guard decide (dedupe (dedupe [ScopedEvidence.receipt0, ScopedEvidence.receipt1,
  ScopedEvidence.receipt1, ScopedEvidence.receipt0])
  = [ScopedEvidence.receipt0, ScopedEvidence.receipt1]) == true
-- Negative control: transport preserves delivery order; it does not sort.
#guard decide (dedupe [ScopedEvidence.receipt0, ScopedEvidence.receipt1]
  = [ScopedEvidence.receipt1, ScopedEvidence.receipt0]) == false
-- The raw ledger with a duplicate delivery is rejected by qualify, while
-- the transported selected set is accepted.
#guard ScopedEvidence.qualify ScopedEvidence.examplePolicy
  [ScopedEvidence.receipt0, ScopedEvidence.receipt1, ScopedEvidence.receipt1] == false
#guard ScopedEvidence.qualify ScopedEvidence.examplePolicy
  (dedupe [ScopedEvidence.receipt0, ScopedEvidence.receipt1,
    ScopedEvidence.receipt1]) == true
-- Conflicting duplicates: the first delivery wins, in both orders, and
-- transport never upgrades a failing first delivery into a pass.
#guard decide (dedupe [conflictingReceipt, ScopedEvidence.receipt0]
  = [conflictingReceipt]) == true
#guard decide (dedupe [ScopedEvidence.receipt0, conflictingReceipt]
  = [ScopedEvidence.receipt0]) == true
#guard ScopedEvidence.qualify singlePolicy
  (dedupe [conflictingReceipt, ScopedEvidence.receipt0]) == false
#guard ScopedEvidence.qualify singlePolicy
  (dedupe [ScopedEvidence.receipt0, conflictingReceipt]) == true
#guard ScopedEvidence.qualify singlePolicy
  [conflictingReceipt, ScopedEvidence.receipt0] == false
-- The dropped conflicting delivery stays detectable: it is present in the
-- raw ledger and absent from the transported set.
#guard decide (ScopedEvidence.receipt0
  ∈ [conflictingReceipt, ScopedEvidence.receipt0]) == true
#guard decide (ScopedEvidence.receipt0
  ∈ dedupe [conflictingReceipt, ScopedEvidence.receipt0]) == false

#print axioms qualify_dedupe_iff
#print axioms dedupe_idempotent
end EvidenceTransport
