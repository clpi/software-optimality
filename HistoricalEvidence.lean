import LinearSelection
import FiniteFrontier
import Admission
import WorklistClosure
import HypergraphIncremental
import Lean.Data.Json

namespace HistoricalEvidence
open Lean

structure Run where
  system : String
  revision : String
  configuration : String
  occurrenceId : String
  deriving Repr, DecidableEq, ToJson, FromJson

inductive Field where
  | occurrence
  | attribute (name : String)
  deriving Repr, DecidableEq, ToJson, FromJson

structure Question where
  run : Run
  field : Field
  deriving Repr, DecidableEq, ToJson, FromJson

structure Atom where
  question : Question
  value : Option Nat
  deriving Repr, DecidableEq, ToJson, FromJson

/-- Absent runs have no attribute value. An occurrence query always has a Boolean code. -/
def reading (history : Run → Option (String → Nat)) (q : Question) : Option Nat :=
  match history q.run, q.field with
  | none, .occurrence => some 0
  | some _, .occurrence => some 1
  | none, .attribute _ => none
  | some f, .attribute n => some (f n)

inductive Route where
  | direct | backfill | hookSample
  | sparse | symbolic | replay | transfer
  | independentPrediction | discovery | hookPlan
  deriving Repr, DecidableEq, ToJson, FromJson

inductive Channel where | measurement | implication | advisory
  deriving Repr, DecidableEq, ToJson, FromJson

def Route.channel : Route → Channel
  | .direct | .backfill | .hookSample => .measurement
  | .sparse | .symbolic | .replay | .transfer => .implication
  | .independentPrediction | .discovery | .hookPlan => .advisory

structure Receipt where
  atom : Atom
  capturedAt : Nat
  source : String
  evidenceId : String
  hook : Bool
  deriving Repr, DecidableEq, ToJson, FromJson

structure Row where
  id : Nat
  bodyId : Nat
  appendedAt : Nat
  source : String
  model : String
  route : Route
  parents : List Atom
  head : Atom
  receipt : Option Receipt
  deriving Repr, DecidableEq, ToJson, FromJson

inductive Event where
  | put (row : Row)
  | withdraw (id : Nat)
  deriving Repr, DecidableEq, ToJson, FromJson

def append (ledger : List Event) (event : Event) := ledger ++ [event]

theorem append_prefix (ledger : List Event) (e : Event) :
    (append ledger e).take ledger.length = ledger := by simp [append]

private def key (id : Nat) : Admission.Key := ⟨0,0,0,id⟩
private def payload (r : Row) : Admission.Payload := ⟨0,true,r.bodyId⟩

def shadow : Event → Admission.Event
  | .put r => .claim (key r.id) (payload r)
  | .withdraw id => .withdraw (key id)

def rows (events : List Event) : List Row :=
  events.filterMap (fun e => match e with | .put r => some r | .withdraw _ => none)

theorem mem_rows (r : Row) (events : List Event) : r ∈ rows events ↔ Event.put r ∈ events := by
  simp only [rows, List.mem_filterMap]
  constructor
  · rintro ⟨e, he, hp⟩
    cases e with
    | put s => cases hp; exact he
    | withdraw _ => contradiction
  · intro h; exact ⟨.put r,h,rfl⟩

/-- Authorize whole events before projection. A repeated ID with different
    authorized bytes is quarantined even if the submitted body IDs collide. -/
def live (auth : Event → Bool) (ledger : List Event) : List Row :=
  let events := ledger.filter auth
  let rs := rows events
  (Admission.unique rs).filter (fun r =>
    Admission.checkLive (fun _ => true) (events.map shadow) (key r.id) (payload r) &&
    rs.all (fun s => decide (s.id = r.id → s = r)))

theorem live_origin (auth : Event → Bool) (ledger : List Event) (r : Row)
    (h : r ∈ live auth ledger) : Event.put r ∈ ledger ∧ auth (.put r) = true := by
  have hm := (List.mem_filter.mp h).1
  exact List.mem_filter.mp ((mem_rows r _).mp ((Admission.mem_unique _ _).mp hm))

theorem withdrawal_blocks (auth : Event → Bool) (ledger : List Event) (r : Row)
    (hw : .withdraw r.id ∈ ledger) (ha : auth (.withdraw r.id) = true) : r ∉ live auth ledger := by
  intro h
  have checked := (Bool.and_eq_true_iff.mp (List.mem_filter.mp h).2).1
  have active := (Admission.checkLive_correct ..).mp checked
  exact active.2.1 ⟨List.mem_map.mpr ⟨.withdraw r.id,List.mem_filter.mpr ⟨hw,ha⟩,rfl⟩,rfl⟩

theorem conflicting_body_blocks (auth : Event → Bool) (ledger : List Event) (r s : Row)
    (hs : .put s ∈ ledger) (ha : auth (.put s) = true) (hid : s.id = r.id) (hd : s ≠ r) :
    r ∉ live auth ledger := by
  intro h
  have all := List.all_eq_true.mp ((Bool.and_eq_true_iff.mp (List.mem_filter.mp h).2).2)
  exact hd ((of_decide_eq_true (all s ((mem_rows s _).mpr (List.mem_filter.mpr ⟨hs,ha⟩)))) hid)

theorem live_exact (auth : Event → Bool) (ledger : List Event) (r : Row) :
    r ∈ live auth ledger ↔ Event.put r ∈ ledger.filter auth ∧
      Event.withdraw r.id ∉ ledger.filter auth ∧
      ∀ s, Event.put s ∈ ledger.filter auth → s.id = r.id → s = r := by
  let events := ledger.filter auth
  constructor
  · intro h
    refine ⟨List.mem_filter.mpr (live_origin auth ledger r h),?_,?_⟩
    · intro hw
      exact withdrawal_blocks auth ledger r (List.mem_filter.mp hw).1 (List.mem_filter.mp hw).2 h
    · intro s hs hid
      have all := List.all_eq_true.mp ((Bool.and_eq_true_iff.mp (List.mem_filter.mp h).2).2)
      exact (of_decide_eq_true (all s ((mem_rows s _).mpr hs))) hid
  · rintro ⟨hm,hw,agree⟩
    refine List.mem_filter.mpr ⟨(Admission.mem_unique ..).mpr ((mem_rows r _).mpr hm),
      Bool.and_eq_true_iff.mpr ⟨(Admission.checkLive_correct ..).mpr ?_,?_⟩⟩
    · constructor
      · exact ⟨List.mem_map.mpr ⟨.put r,hm,rfl⟩,rfl⟩
      · constructor
        · rintro ⟨he,_⟩
          obtain ⟨e,hem,heq⟩ := List.mem_map.mp he
          cases e with
          | put _ => contradiction
          | withdraw i =>
            have hid : i = r.id := congrArg Admission.Key.support (Admission.Event.withdraw.inj heq)
            exact hw (hid ▸ hem)
        · intro e he _
          obtain ⟨ev,hev,rfl⟩ := List.mem_map.mp he
          cases ev with
          | withdraw _ => trivial
          | put s =>
            intro heq
            exact congrArg payload (agree s hev (congrArg Admission.Key.support heq))
    · apply List.all_eq_true.mpr
      intro s hs
      exact decide_eq_true (agree s ((mem_rows s _).mp hs))

def measurement (verify : Receipt → Bool) (r : Row) : Bool :=
  match r.receipt with
  | none => false
  | some w => decide (r.route.channel = .measurement ∧ r.parents = [] ∧
      w.atom = r.head ∧ w.source = r.source ∧ w.capturedAt ≤ r.appendedAt ∧
      (r.route = .hookSample → w.hook = true)) && verify w

theorem measurement_witness (verify : Receipt → Bool) (r : Row) (h : measurement verify r = true) :
    ∃ w, r.receipt = some w ∧ w.atom = r.head ∧ w.source = r.source ∧
      w.capturedAt ≤ r.appendedAt ∧ verify w = true ∧ r.route.channel = .measurement := by
  cases hw : r.receipt with
  | none => simp [measurement,hw] at h
  | some w =>
    simp only [measurement,hw,Bool.and_eq_true,decide_eq_true_eq] at h
    exact ⟨w,rfl,h.1.2.2.1,h.1.2.2.2.1,h.1.2.2.2.2.1,h.2,h.1.1⟩

variable {W : Type}

abbrev Model (W : Type) := W → Question → Option Nat

def holds (m : Model W) (w : W) (a : Atom) : Bool := decide (m w a.question = a.value)
def consistentWith (m : Model W) (facts : List Atom) (w : W) := facts.all (holds m w)
def survivors (worlds : List W) (m : Model W) (facts : List Atom) := worlds.filter (consistentWith m facts)

theorem survivors_exact (ws : List W) (m : Model W) (facts : List Atom) (w : W) :
    w ∈ survivors ws m facts ↔ w ∈ ws ∧ ∀ a ∈ facts, m w a.question = a.value := by
  simp [survivors,consistentWith,holds,List.all_eq_true]

/-- Empty support is inconsistent. Ambiguity carries two incompatible histories. -/
inductive Diagnosis (W : Type) where
  | inconsistent
  | exact (value : Option Nat)
  | ambiguous (left right : W)
  deriving Repr, DecidableEq

def diagnose (m : Model W) (q : Question) : List W → Diagnosis W
  | [] => .inconsistent
  | w :: ws =>
    match ws.find? (fun v => decide (m v q ≠ m w q)) with
    | none => .exact (m w q)
    | some v => .ambiguous w v

theorem diagnose_inconsistent (m : Model W) (q : Question) (ws : List W) :
    diagnose m q ws = .inconsistent ↔ ws = [] := by
  cases ws with
  | nil => simp [diagnose]
  | cons w ws => simp only [diagnose]; split <;> simp

theorem diagnose_exact (m : Model W) (q : Question) (ws : List W) (v : Option Nat) :
    diagnose m q ws = .exact v ↔ ws ≠ [] ∧ ∀ w ∈ ws, m w q = v := by
  cases ws with
  | nil => simp [diagnose]
  | cons w ws =>
    simp only [diagnose]
    split
    next hf =>
      have uniform : ∀ x ∈ ws, m x q = m w q := by
        simpa using List.find?_eq_none.mp hf
      simp only [Diagnosis.exact.injEq,List.cons_ne_nil,not_false_eq_true,true_and,List.forall_mem_cons]
      exact ⟨fun h => ⟨List.cons_ne_nil _ _,h,fun x hx => (uniform x hx).trans h⟩, fun h => h.2.1⟩
    next x hf =>
      have hx := List.mem_of_find?_eq_some hf
      have hv : m x q ≠ m w q := of_decide_eq_true (List.find?_some (p := fun v => decide (m v q ≠ m w q)) hf)
      constructor
      · intro h; contradiction
      · rintro ⟨_,h⟩
        exact False.elim (hv ((h x (List.mem_cons_of_mem _ hx)).trans (h w List.mem_cons_self).symm))

theorem ambiguous_witness (m : Model W) (q : Question) (ws : List W) (x y : W)
    (h : diagnose m q ws = .ambiguous x y) : x ∈ ws ∧ y ∈ ws ∧ m x q ≠ m y q := by
  cases ws with
  | nil => contradiction
  | cons w ws =>
    simp only [diagnose] at h
    split at h
    next => contradiction
    next z hz =>
      cases h
      exact ⟨List.mem_cons_self,List.mem_cons_of_mem _ (List.mem_of_find?_eq_some hz),
        Ne.symm (of_decide_eq_true (List.find?_some (p := fun v => decide (m v q ≠ m x q)) hz))⟩

/-- A concrete rule is authorized only for its pinned model; check its full
    antecedent and consequent against every named world. -/
def implication (ws : List W) (m : Model W) (version : String) (r : Row) :=
  decide (r.route.channel = .implication ∧ r.model = version ∧ r.receipt = none) &&
    ws.all (fun w => !(consistentWith m r.parents w) || holds m w r.head)

theorem implication_sound (ws : List W) (m : Model W) (version : String) (r : Row)
    (h : implication ws m version r = true) (w : W) (hw : w ∈ ws)
    (parents : ∀ p ∈ r.parents, m w p.question = p.value) : m w r.head.question = r.head.value := by
  have pass := List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).2 w hw
  have hp : consistentWith m r.parents w = true := by simpa [consistentWith,holds,List.all_eq_true] using parents
  simpa [hp,holds] using pass

def roots (verify : Receipt → Bool) (rs : List Row) := (rs.filter (measurement verify)).map Row.head
def rules (ws : List W) (m : Model W) (version : String) (rs : List Row) :=
  (rs.filter (implication ws m version)).map (fun r => (r.parents,r.head))

/-- Auto-generate the finite atom universe. All heads, roots and joint premises
    are retained; alternative row identities remain present in the ledger. -/
def atoms (rs : List Row) := Admission.unique (rs.flatMap (fun r => r.head :: r.parents))

def solve (ws : List W) (m : Model W) (version : String) (verify : Receipt → Bool)
    (rs : List Row) :=
  WorklistClosure.wclose (atoms rs) (roots verify rs) (rules ws m version rs)

def graph (ws : List W) (m : Model W) (version : String) (verify : Receipt → Bool)
    (rs : List Row) : HypergraphIncremental.Hypergraph Atom :=
  ⟨fun a => a ∈ roots verify rs, fun ps a => (ps,a) ∈ rules ws m version rs⟩

private theorem head_member (rs : List Row) (r : Row) (h : r ∈ rs) : r.head ∈ atoms rs :=
  (Admission.mem_unique ..).mpr (List.mem_flatMap.mpr ⟨r,h,List.mem_cons_self⟩)

theorem automatic_bounds (ws : List W) (m : Model W) (version : String) (verify : Receipt → Bool)
    (rs : List Row) :
    ExecutableClosure.boundedOK (atoms rs) (roots verify rs) (rules ws m version rs) = true := by
  apply (ExecutableClosure.boundedOK_exact ..).mpr
  constructor
  · intro x hx
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hx
    exact head_member rs r (List.mem_filter.mp hr).1
  · intro ps x hx
    obtain ⟨r,hr,he⟩ := List.mem_map.mp hx
    cases he
    exact head_member rs r (List.mem_filter.mp hr).1

theorem solve_exact (ws : List W) (m : Model W) (version : String) (verify : Receipt → Bool)
    (rs : List Row) (a : Atom) :
    a ∈ solve ws m version verify rs ↔ HypergraphIncremental.derives (graph ws m version verify rs) a := by
  obtain ⟨hb,hr⟩ := (ExecutableClosure.boundedOK_exact ..).mp (automatic_bounds ws m version verify rs)
  exact WorklistClosure.wclose_exact _ _ _ hb hr a

theorem solve_sound (ws : List W) (m : Model W) (version : String) (verify : Receipt → Bool)
    (rs : List Row) (w : W) (hw : w ∈ ws)
    (observed : ∀ r ∈ rs, measurement verify r = true → m w r.head.question = r.head.value)
    {a : Atom} (h : a ∈ solve ws m version verify rs) : m w a.question = a.value := by
  apply Qualification.soundness (TrueAt := fun a => m w a.question = a.value) _ _
    a ((solve_exact ..).mp h)
  · intro x hx
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hx
    obtain ⟨hm,ok⟩ := List.mem_filter.mp hr
    exact observed r hm ok
  · intro ps x hr hp
    obtain ⟨r,hm,he⟩ := List.mem_map.mp hr
    cases he
    exact implication_sound ws m version r (List.mem_filter.mp hm).2 w hw hp

theorem advisory_inert (ws : List W) (m : Model W) (v : String) (check : Receipt → Bool)
    (r : Row) (advisory : r.route.channel = .advisory) :
    measurement check r = false ∧ implication ws m v r = false := by
  constructor
  · cases h : r.receipt <;> simp [measurement,h,advisory]
  · simp [implication,advisory]

/-- Color evidence for an exact value independently from the route tag. -/
def color (facts : List Atom) (a : Atom) : FiniteFrontier.Color :=
  FiniteFrontier.color (decide (a ∈ facts))
    (facts.any (fun b => decide (b.question = a.question ∧ b.value ≠ a.value)))

theorem conflict_exact (facts : List Atom) (a : Atom) :
    color facts a = .conflict ↔ a ∈ facts ∧ ∃ b ∈ facts, b.question = a.question ∧ b.value ≠ a.value := by
  simp [color,FiniteFrontier.conflict_exact,List.any_eq_true]

def certified (ws : List W) (m : Model W) (version : String) (verify : Receipt → Bool)
    (auth : Event → Bool) (log : List Event) : Option (List Atom) :=
  let rs := live auth log
  if (survivors ws m (roots verify rs)).isEmpty then none else
    some (solve ws m version verify rs)

theorem certified_sound (ws : List W) (m : Model W) (version : String) (verify : Receipt → Bool)
    (auth : Event → Bool) (log : List Event) (out : List Atom)
    (ok : certified ws m version verify auth log = some out) :
    let possible := survivors ws m (roots verify (live auth log))
    possible ≠ [] ∧ ∀ w ∈ possible, ∀ a ∈ out, m w a.question = a.value := by
  unfold certified at ok
  dsimp only at ok ⊢
  split at ok
  next => contradiction
  next nonempty =>
    cases ok
    refine ⟨fun h => nonempty (by simp [h]),?_⟩
    intro w hw a ha
    obtain ⟨member,observations⟩ := (survivors_exact ..).mp hw
    apply solve_sound _ _ _ _ _ w member _ ha
    intro r hr hv
    exact observations r.head (List.mem_map.mpr ⟨r,List.mem_filter.mpr ⟨hr,hv⟩,rfl⟩)

theorem solve_mono_rows (ws : List W) (m : Model W) (version : String) (verify : Receipt → Bool)
    (xs ys : List Row) (sub : ∀ r ∈ xs, r ∈ ys) (a : Atom) :
    a ∈ solve ws m version verify xs → a ∈ solve ws m version verify ys := by
  rw [solve_exact,solve_exact]
  apply Qualification.monotone
  · intro x h
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp h
    exact List.mem_map.mpr ⟨r,List.mem_filter.mpr ⟨sub r (List.mem_filter.mp hr).1,(List.mem_filter.mp hr).2⟩,rfl⟩
  · intro ps x h
    obtain ⟨r,hr,he⟩ := List.mem_map.mp h
    exact List.mem_map.mpr ⟨r,List.mem_filter.mpr ⟨sub r (List.mem_filter.mp hr).1,(List.mem_filter.mp hr).2⟩,he⟩

end HistoricalEvidence
