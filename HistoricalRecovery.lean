import HistoricalEvidence

namespace HistoricalEvidence
variable {W : Type}

/-- Discover names from any authorized live row, including unverified candidates
    and the premise ports of joint rules. The index carries no occurrence claim. -/
def discover (roster : List Run) (rs : List Row) :=
  Admission.unique (roster ++ (rs.flatMap (fun r => (r.head :: r.parents).map (fun a => a.question.run))))

theorem discover_exact (roster : List Run) (rs : List Row) (run : Run) :
    run ∈ discover roster rs ↔ run ∈ roster ∨
      ∃ r ∈ rs, ∃ a ∈ r.head :: r.parents, a.question.run = run := by
  simp [discover,Admission.mem_unique,List.mem_flatMap,List.mem_map,eq_comm]

def rowId : Event → Nat | .put r => r.id | .withdraw i => i

def nextId (events : List Event) : Nat :=
  events.foldr (fun e n => max (rowId e + 1) n) 0

theorem nextId_fresh (events : List Event) (e : Event) (h : e ∈ events) : rowId e < nextId events := by
  induction events with
  | nil => contradiction
  | cons a xs ih =>
    change rowId e < max (rowId a + 1) (nextId xs)
    rcases List.mem_cons.mp h with rfl | hx
    · exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
    · exact Nat.lt_of_lt_of_le (ih hx) (Nat.le_max_right _ _)

def consequences (ws : List W) (m : Model W) (check : Receipt → Bool)
    (rs : List Row) (q : Question) := diagnose m q (survivors ws m (roots check rs))

def derivedRow (id stamp : Nat) (version : String) (ps : List Atom) (q : Question)
    (v : Option Nat) : Row :=
  ⟨id,id,stamp,"finite-model",version,if ps.isEmpty then .symbolic else .sparse,ps,⟨q,v⟩,none⟩

def derive (ws : List W) (m : Model W) (version : String) (check : Receipt → Bool)
    (rs : List Row) (q : Question) (id stamp : Nat) : Option Row :=
  match consequences ws m check rs q with
  | .exact v => some (derivedRow id stamp version (roots check rs) q v)
  | _ => none

theorem derive_iff (ws : List W) (m : Model W) (version : String) (check : Receipt → Bool)
    (rs : List Row) (q : Question) (id stamp : Nat) (v : Option Nat) :
    derive ws m version check rs q id stamp = some (derivedRow id stamp version (roots check rs) q v) ↔
    let candidates := survivors ws m (roots check rs)
    candidates ≠ [] ∧ ∀ w ∈ candidates, m w q = v := by
  rw [← diagnose_exact]
  unfold derive consequences
  split <;> simp_all [derivedRow]

theorem derived_joins_closure (ws : List W) (m : Model W) (version : String) (check : Receipt → Bool)
    (rs : List Row) (q : Question) (id stamp : Nat) (v : Option Nat)
    (rowOK : derive ws m version check rs q id stamp =
      some (derivedRow id stamp version (roots check rs) q v)) :
    let r := derivedRow id stamp version (roots check rs) q v
    ⟨q,v⟩ ∈ solve ws m version check (rs ++ [r]) := by
  let ps := roots check rs
  let r := derivedRow id stamp version ps q v
  change r.head ∈ solve ws m version check (rs ++ [r])
  have uniform := ((derive_iff ..).mp rowOK).2
  have cert : implication ws m version r = true := by
    apply Bool.and_eq_true_iff.mpr
    constructor
    · apply decide_eq_true
      simp [r,derivedRow]
      split <;> rfl
    · apply List.all_eq_true.mpr
      intro w hw
      by_cases hp : consistentWith m ps w = true
      · have member : w ∈ survivors ws m ps := List.mem_filter.mpr ⟨hw,hp⟩
        have out := uniform w member
        simp [r,derivedRow,hp,holds,out]
      · have hf : consistentWith m ps w = false := Bool.eq_false_iff.mpr hp
        simp [r,derivedRow,hf]
  apply (solve_exact ..).mpr
  apply Qualification.Derives.step (ps := ps)
  · exact List.mem_map.mpr ⟨r,List.mem_filter.mpr ⟨by simp,cert⟩,rfl⟩
  · intro a ha
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ha
    exact .root (List.mem_map.mpr ⟨s,List.mem_filter.mpr
      ⟨List.mem_append_left _ (List.mem_filter.mp hs).1,(List.mem_filter.mp hs).2⟩,rfl⟩)

def backfillOne (ws : List W) (m : Model W) (version : String) (verify : Receipt → Bool)
    (auth : Event → Bool) (ledger : List Event) (q : Question) (stamp : Nat) : List Event :=
  match derive ws m version verify (live auth ledger) q (nextId ledger) stamp with
  | none => ledger
  | some r => append ledger (.put r)

theorem backfill_history_preserved (ws : List W) (m : Model W) (version : String) (verify : Receipt → Bool)
    (auth : Event → Bool) (ledger : List Event) (q : Question) (stamp : Nat) :
    (backfillOne ws m version verify auth ledger q stamp).take ledger.length = ledger := by
  unfold backfillOne
  split <;> simp [append_prefix]

theorem live_after_fresh (auth : Event → Bool) (log : List Event) (r : Row)
    (fresh : nextId log ≤ r.id) (authorized : auth (.put r) = true) (s : Row) :
    s ∈ live auth (append log (.put r)) ↔ s ∈ live auth log ∨ s = r := by
  have oldPut : ∀ t, Event.put t ∈ log.filter auth → t.id < r.id := by
    intro t h; exact Nat.lt_of_lt_of_le (nextId_fresh log (.put t) (List.mem_filter.mp h).1) fresh
  have oldDrop : Event.withdraw r.id ∉ log.filter auth := by
    intro h
    have bad := nextId_fresh log (.withdraw r.id) (List.mem_filter.mp h).1
    change r.id < nextId log at bad
    exact (Nat.not_lt_of_ge fresh) bad
  simp only [live_exact,append,List.filter_append,List.filter_cons_of_pos authorized,
    List.filter_nil,List.mem_append,List.mem_singleton,Event.put.injEq]
  constructor
  · rintro ⟨hp,hw,unique⟩
    rcases hp with old | eq
    · exact Or.inl ⟨old,fun h => hw (Or.inl h),fun t ht => unique t (Or.inl ht)⟩
    · exact Or.inr eq
  · rintro (⟨old,hw,unique⟩ | rfl)
    · refine ⟨Or.inl old,?_,?_⟩
      · rintro (h | h); exact hw h; contradiction
      · rintro t (ht | rfl) hid
        · exact unique t ht hid
        · exact False.elim (Nat.ne_of_lt (oldPut s old) hid.symm)
    · refine ⟨Or.inr rfl,?_,?_⟩
      · rintro (h | h); exact oldDrop h; contradiction
      · rintro t (ht | rfl) hid
        · exact False.elim (Nat.ne_of_lt (oldPut t ht) hid)
        · rfl

theorem backfill_publishes (ws : List W) (m : Model W) (version : String) (verify : Receipt → Bool)
    (auth : Event → Bool) (log : List Event) (q : Question) (stamp : Nat) (v : Option Nat)
    (certain : consequences ws m verify (live auth log) q = .exact v)
    (authorized : auth (.put (derivedRow (nextId log) stamp version (roots verify (live auth log)) q v)) = true) :
    let updated := backfillOne ws m version verify auth log q stamp
    ⟨q,v⟩ ∈ solve ws m version verify (live auth updated) := by
  let rs := live auth log
  let r := derivedRow (nextId log) stamp version (roots verify rs) q v
  have emitted : derive ws m version verify rs q (nextId log) stamp = some r := by
    simp [derive,rs,certain,r]
  change ⟨q,v⟩ ∈ solve ws m version verify (live auth (backfillOne ws m version verify auth log q stamp))
  have he : backfillOne ws m version verify auth log q stamp = append log (.put r) := by
    unfold backfillOne; rw [show derive ws m version verify (live auth log) q (nextId log) stamp = some r from emitted]
  rw [he]
  apply solve_mono_rows _ _ _ _ (rs ++ [r]) _ _ _ (derived_joins_closure ws m version verify rs q (nextId log) stamp v emitted)
  intro s hs
  exact (live_after_fresh auth log r (Nat.le_refl _) authorized s).mpr (by simpa [rs] using hs)

/-- Compute every missing, unanimous answer over a snapshot in one batch.
    Parent rows are shared across the batch. The allocator supplies distinct
    row IDs; catalogue membership is semantic even when queries repeat. -/
def batch (ws : List W) (m : Model W) (version : String) (check : Receipt → Bool)
    (rs : List Row) (todo : List (Question × Nat)) (stamp : Nat) : List Row :=
  let already := solve ws m version check rs
  (todo.filterMap (fun (q,i) => derive ws m version check rs q i stamp)).filter
    (fun r => decide (r.head ∉ already))

theorem batch_complete (ws : List W) (m : Model W) (version : String) (check : Receipt → Bool)
    (rs : List Row) (todo : List (Question × Nat)) (stamp id : Nat) (q : Question) (v : Option Nat)
    (asked : (q,id) ∈ todo) (consistent : survivors ws m (roots check rs) ≠ []) :
    let withProofs := rs ++ batch ws m version check rs todo stamp
    ⟨q,v⟩ ∈ solve ws m version check withProofs ↔
      ∀ w ∈ survivors ws m (roots check rs), m w q = v := by
  dsimp only
  constructor
  · intro ha w hw
    obtain ⟨member,observations⟩ := (survivors_exact ..).mp hw
    apply solve_sound ws m version check _ w member _ ha
    intro r hr good
    rcases List.mem_append.mp hr with old | generated
    · exact observations r.head (List.mem_map.mpr ⟨r,List.mem_filter.mpr ⟨old,good⟩,rfl⟩)
    · obtain ⟨⟨question,num⟩,_,hdr⟩ := List.mem_filterMap.mp (List.mem_filter.mp generated).1
      dsimp only at hdr
      unfold derive at hdr
      split at hdr
      next why =>
        cases hdr
        simp [derivedRow,measurement] at good
      all_goals contradiction
  · intro all
    by_cases old : Atom.mk q v ∈ solve ws m version check rs
    · exact solve_mono_rows _ _ _ _ rs _ (fun _ h => List.mem_append_left _ h) _ old
    · let r := derivedRow id stamp version (roots check rs) q v
      have emitted := (derive_iff ws m version check rs q id stamp v).mpr ⟨consistent,all⟩
      have hm : r ∈ batch ws m version check rs todo stamp :=
        List.mem_filter.mpr ⟨List.mem_filterMap.mpr ⟨(q,id),asked,emitted⟩,decide_eq_true old⟩
      apply solve_mono_rows _ _ _ _ (rs ++ [r]) _ _ _ (derived_joins_closure ws m version check rs q id stamp v emitted)
      intro s hs
      rcases List.mem_append.mp hs with orig | fresh
      · exact List.mem_append_left _ orig
      · have eq := List.mem_singleton.mp fresh
        exact List.mem_append_right _ (eq ▸ hm)

def commitRows (log : List Event) : List Row → List Event
  | [] => log
  | r :: rs => commitRows (append log (.put r)) rs

def ready (auth : Event → Bool) (log : List Event) : List Row → Bool
  | [] => true
  | r :: rs => decide (nextId log ≤ r.id) && auth (.put r) && ready auth (append log (.put r)) rs

theorem live_commit (auth : Event → Bool) (log : List Event) (rows : List Row)
    (ok : ready auth log rows = true) (r : Row) :
    r ∈ live auth (commitRows log rows) ↔ r ∈ live auth log ∨ r ∈ rows := by
  induction rows generalizing log with
  | nil => simp [commitRows]
  | cons a rest ih =>
    simp only [ready,Bool.and_eq_true,decide_eq_true_eq] at ok
    rw [commitRows,ih _ ok.2,live_after_fresh auth log a ok.1.1 ok.1.2 r]
    simp [or_assoc]

theorem published_batch_exact (ws : List W) (m : Model W) (version : String) (check : Receipt → Bool)
    (auth : Event → Bool) (log : List Event) (todo : List (Question × Nat)) (stamp id : Nat)
    (q : Question) (v : Option Nat) (asked : (q,id) ∈ todo)
    (consistent : survivors ws m (roots check (live auth log)) ≠ [])
    (ok : ready auth log (batch ws m version check (live auth log) todo stamp) = true) :
    let pending := batch ws m version check (live auth log) todo stamp
    ⟨q,v⟩ ∈ solve ws m version check (live auth (commitRows log pending)) ↔
      ∀ w ∈ survivors ws m (roots check (live auth log)), m w q = v := by
  let rs := live auth log
  let added := batch ws m version check rs todo stamp
  let stored := live auth (commitRows log added)
  have same (r : Row) : r ∈ stored ↔ r ∈ rs ++ added := by
    rw [List.mem_append]; exact live_commit auth log added ok r
  have sameAnswers : Atom.mk q v ∈ solve ws m version check stored ↔
      Atom.mk q v ∈ solve ws m version check (rs ++ added) :=
    ⟨solve_mono_rows _ _ _ _ _ _ (fun r => (same r).mp) _,
     solve_mono_rows _ _ _ _ _ _ (fun r => (same r).mpr) _⟩
  exact sameAnswers.trans (batch_complete ws m version check rs todo stamp id q v asked consistent)

/-- Mixed or empty possible-world support never generates a proof row. -/
theorem ambiguous_no_entry (ws : List W) (m : Model W) (version : String) (check : Receipt → Bool)
    (rs : List Row) (q : Question) (id stamp : Nat) (w z : W)
    (mixed : consequences ws m check rs q = .ambiguous w z) :
    derive ws m version check rs q id stamp = none := by simp [derive,mixed]

/-- Actual-world coverage may be a quotient: only the named observations and
    query must be preserved. No enumeration of every physical detail is needed. -/
theorem transport_recovery {Real : Type} (possible : Real → Prop) (actual : Real → Question → Option Nat)
    (abstracts : Real → W) (ws : List W) (m : Model W) (facts : List Atom) (q : Question) (v : Option Nat)
    (covered : ∀ x, possible x → abstracts x ∈ ws)
    (observations : ∀ x, possible x → ∀ a ∈ facts, actual x a.question = m (abstracts x) a.question)
    (query : ∀ x, possible x → actual x q = m (abstracts x) q)
    (proved : diagnose m q (survivors ws m facts) = .exact v)
    (x : Real) (hx : possible x) (consistent : ∀ a ∈ facts, actual x a.question = a.value) :
    actual x q = v := by
  apply (query x hx).trans
  apply ((diagnose_exact ..).mp proved).2
  exact (survivors_exact ..).mpr ⟨covered x hx,fun a ha => (observations x hx a ha).symm.trans (consistent a ha)⟩

def mistakeMass (ws : List W) (weight : W → Nat) (m : Model W) (q : Question) (v : Option Nat) :=
  ((ws.filter (fun w => decide (m w q ≠ v))).map weight).sum

/-- Separate predictive route: exact empirical/prior zero-one loss, all ties,
    and an empty output for zero mass. Weights need independent justification. -/
def bets (ws : List W) (weight : W → Nat) (m : Model W) (q : Question) :=
  if (ws.map weight).sum = 0 then [] else
    LinearSelection.allMinima (fun v => Int.ofNat (mistakeMass ws weight m q v))
      (Admission.unique (ws.map (fun w => m w q)))

theorem bet_exact (ws : List W) (weight : W → Nat) (m : Model W) (q : Question) (v : Option Nat) :
    v ∈ bets ws weight m q ↔ (ws.map weight).sum ≠ 0 ∧
      (∃ w ∈ ws, m w q = v) ∧
      ∀ w ∈ ws, mistakeMass ws weight m q v ≤ mistakeMass ws weight m q (m w q) := by
  unfold bets
  split
  next h => simp [h]
  next h =>
    have cast (x y : Nat) : Int.ofNat x ≤ Int.ofNat y ↔ x ≤ y := Int.ofNat_le
    simp [h,LinearSelection.allMinima_exact,Admission.mem_unique,List.mem_map,cast]

end HistoricalEvidence
