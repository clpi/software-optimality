import Qualification
import FiniteFrontier
import ExecutableClosure
import Std

/- One authoritative directed hypergraph. Dependency and incidence are views,
   never alternative inference relations. Atoms include exact version/scope. -/
namespace HypergraphIncremental
variable {A : Type}

structure Hypergraph (A : Type) where
  roots : A → Prop
  edges : List A → A → Prop

def derives (g : Hypergraph A) := Qualification.Derives g.roots g.edges

-- The binary view is for invalidation only: firing still requires ALL premises.
def dependency (g : Hypergraph A) (p a : A) : Prop :=
  ∃ ps, g.edges ps a ∧ p ∈ ps

inductive Port where
  | head | premise (position : Nat)
  deriving DecidableEq

def incidence (g : Hypergraph A) (ps : List A) (a x : A) : Port → Prop
  | .head => g.edges ps a ∧ x = a
  | .premise i => g.edges ps a ∧ ps[i]? = some x

-- Co-participation retains the actual hyperedge and both directed port roles.
def interaction (g : Hypergraph A) (ps : List A) (a x y : A) (r s : Port) : Prop :=
  incidence g ps a x r ∧ incidence g ps a y s

theorem interaction_is_derived (g : Hypergraph A) (ps : List A)
    (a x y : A) (r s : Port) :
    interaction g ps a x y r s ↔ incidence g ps a x r ∧ incidence g ps a y s := Iff.rfl

-- Changes seed heads even for deleted/inserted zero-premise edges.
inductive Affected (old new : Hypergraph A) : A → Prop where
  | root {a} : (¬ (old.roots a ↔ new.roots a)) → Affected old new a
  | edge {ps a} : (¬ (old.edges ps a ↔ new.edges ps a)) → Affected old new a
  | downstream {p a} : Affected old new p →
      (dependency old p a ∨ dependency new p a) → Affected old new a

theorem affected_symm {old new : Hypergraph A} {a : A}
    (h : Affected old new a) : Affected new old a := by
  induction h with
  | root h => exact .root (fun h' => h h'.symm)
  | edge h => exact .edge (fun h' => h h'.symm)
  | downstream _ hd ih => exact .downstream ih hd.symm

theorem unchanged_derivation {old new : Hypergraph A} {a : A}
    (h : derives old a) : ¬ Affected old new a → derives new a := by
  classical
  induction h with
  | @root a hb =>
    intro hn
    have he : old.roots a ↔ new.roots a := Classical.byContradiction (fun hc => hn (.root hc))
    exact .root (he.mp hb)
  | @step ps a hr hp ih =>
    intro hn
    have he : old.edges ps a ↔ new.edges ps a := Classical.byContradiction (fun hc => hn (.edge hc))
    apply Qualification.Derives.step (he.mp hr)
    intro p hm
    apply ih p hm
    intro ha
    exact hn (.downstream ha (Or.inl ⟨ps, hr, hm⟩))

theorem unaffected_exact {old new : Hypergraph A} {a : A}
    (hn : ¬ Affected old new a) : derives old a ↔ derives new a := by
  constructor
  · intro h; exact unchanged_derivation h hn
  · intro h
    exact unchanged_derivation h (fun ha => hn (affected_symm ha))

-- Reuse only unaffected old facts; affected recursion is rebuilt inductively,
-- not warm-started from old derived facts. The only rules fired have affected heads.
def incremental (old new : Hypergraph A) : A → Prop :=
  Qualification.Derives
    (fun a => new.roots a ∨ (¬ Affected old new a ∧ derives old a))
    (fun ps a => new.edges ps a ∧ Affected old new a)

theorem incremental_exact (old new : Hypergraph A) (a : A) :
    incremental old new a ↔ derives new a := by
  constructor
  · intro h
    induction h with
    | root hb =>
      rcases hb with hb | ⟨hn, ho⟩
      · exact .root hb
      · exact (unaffected_exact hn).mp ho
    | step hr _ ih => exact .step hr.1 ih
  · intro h
    classical
    induction h with
    | root hb => exact .root (Or.inl hb)
    | @step ps a hr hp ih =>
      by_cases ha : Affected old new a
      · exact .step ⟨hr, ha⟩ ih
      · exact .root (Or.inr ⟨ha, (unaffected_exact ha).mpr (.step hr hp)⟩)

-- Bridge to the existing executable exhaustive checker, not a worklist runtime.
theorem executable_full_agrees [DecidableEq A] (old : Hypergraph A)
    (U B : List A) (rules : List (List A × A))
    (hb : ∀ a, a ∈ B → a ∈ U)
    (hr : ∀ ps a, (ps, a) ∈ rules → a ∈ U) (a : A) :
    incremental old ⟨fun x => x ∈ B, fun ps x => (ps, x) ∈ rules⟩ a ↔
      a ∈ ExecutableClosure.close U B rules := by
  exact (incremental_exact _ _ a).trans
    (ExecutableClosure.close_exact U B rules hb hr a).symm

-- This quantifies over cyclic hypergraphs too, without assuming acyclicity.
theorem retracted_cycles_do_not_bootstrap (old new : Hypergraph A)
    (empty : ∀ a, ¬ new.roots a)
    (needsInput : ∀ ps a, new.edges ps a → ∃ p, p ∈ ps) :
    ∀ a, ¬ incremental old new a := by
  intro a h
  have hn := (incremental_exact old new a).mp h
  exact Qualification.least (fun x hx => empty x hx)
    (fun ps x hr hp => let ⟨p, hm⟩ := needsInput ps x hr; hp p hm) a hn

-- View regeneration on unchanged edge rows is exact, including role/position.
theorem incidence_row_unchanged (old new : Hypergraph A) (ps : List A)
    (a x : A) (r : Port) (same : old.edges ps a ↔ new.edges ps a) :
    incidence old ps a x r ↔ incidence new ps a x r := by
  cases r <;> simp only [incidence, same]

noncomputable def patchedInteraction (old new : Hypergraph A) (ps : List A)
    (a x y : A) (r s : Port) : Prop := by
  classical
  exact if old.edges ps a ↔ new.edges ps a then interaction old ps a x y r s
  else interaction new ps a x y r s

theorem patchedInteraction_exact (old new : Hypergraph A) (ps : List A)
    (a x y : A) (r s : Port) :
    patchedInteraction old new ps a x y r s ↔ interaction new ps a x y r s := by
  classical
  unfold patchedInteraction
  split
  · rename_i h
    exact and_congr (incidence_row_unchanged old new ps a x r h)
      (incidence_row_unchanged old new ps a y s h)
  · exact Iff.rfl

-- Frontier cache is downstream of the same qualified projection; eligibility
-- and measured objective descriptors are explicit snapshot inputs here.
structure Profile where
  eligible : Bool
  costs : List Int
  deriving DecidableEq

def dominates (x y : Profile) : Bool :=
  x.eligible && y.eligible && decide (x.costs.length = y.costs.length) &&
  (x.costs.zip y.costs).all (fun p => decide (p.1 ≤ p.2)) &&
  (x.costs.zip y.costs).any (fun p => decide (p.1 < p.2))

def patchedDominance (old new : A → Profile) (x y : A) : Bool :=
  if old x = new x ∧ old y = new y then dominates (old x) (old y)
  else dominates (new x) (new y)

theorem patchedDominance_exact (old new : A → Profile) (x y : A) :
    patchedDominance old new x y = dominates (new x) (new y) := by
  unfold patchedDominance
  split
  · rename_i h; rw [h.1, h.2]
  · rfl

def frontier (U : List A) (p : A → Profile) : List A :=
  (U.filter (fun x => (p x).eligible)).filter
    (fun y => !(U.any (fun x => dominates (p x) (p y))))

def incrementalFrontier (U : List A) (old new : A → Profile) : List A :=
  (U.filter (fun x => (new x).eligible)).filter
    (fun y => !(U.any (fun x => patchedDominance old new x y)))

theorem incrementalFrontier_exact (U : List A) (old new : A → Profile) :
    incrementalFrontier U old new = frontier U new := by
  simp only [incrementalFrontier, frontier, patchedDominance_exact]

-- Any deterministic profile projection from qualifications, including
-- negative support/absence decisions evaluated AFTER closure, sees equal input.
theorem qualified_frontier_exact (old new : Hypergraph A) (U : List A)
    (project : (A → Prop) → A → Profile) :
    frontier U (project (incremental old new)) = frontier U (project (derives new)) := by
  have h : incremental old new = derives new := by
    funext a
    exact propext (incremental_exact old new a)
  rw [h]

-- A dominated candidate must be retained; when its dominator is withdrawn,
-- it returns without a new candidate discovery or fabricated observation.
def before : Bool → Profile
  | false => ⟨true, [1, 1]⟩
  | true => ⟨true, [2, 2]⟩
def after : Bool → Profile
  | false => ⟨false, [1, 1]⟩
  | true => ⟨true, [2, 2]⟩
example : frontier [false, true] before = [false] := by decide
example : incrementalFrontier [false, true] before after = [true] := by decide

-- Joint-premise control: incidence alone is not inference.
def joint : Hypergraph Nat :=
  ⟨fun a => a = 0, fun ps a => ps = [0, 1] ∧ a = 2⟩
example : dependency joint 0 2 := ⟨[0, 1], ⟨rfl, rfl⟩, by simp⟩
example : ¬ derives joint 2 := by
  intro h
  have hz : (2 : Nat) = 0 := Qualification.least (X := fun a => a = 0)
    (fun _ hx => hx) (by
      intro ps a hr hp
      rcases hr with ⟨rfl, rfl⟩
      have bad := hp 1 (by simp)
      contradiction) 2 h
  contradiction

-- Finite typed-edge matrix view. Each cell counts actual supporting edge
-- records. Withdrawal edits the authoritative records, not an independent bit.
structure TypedEdge where
  id : Nat
  kind : Nat
  premises : List Nat
  head : Nat
  deriving DecidableEq

-- Distinct receipt IDs may justify the same semantic implication. The
-- relation is re-derived from LIVE records; withdrawing one does not withdraw
-- the implication while another admitted record remains. Kind admission is
-- explicit rather than inferred from co-incidence.
def graphOfRecords (roots : Nat → Prop) (live : List TypedEdge)
    (admittedKind : Nat → Bool) : Hypergraph Nat :=
  ⟨roots, fun ps a => ∃ e, e ∈ live ∧ admittedKind e.kind = true ∧
      e.premises = ps ∧ e.head = a⟩

theorem graphOfRecords_edge_exact (roots : Nat → Prop) (live : List TypedEdge)
    (admittedKind : Nat → Bool) (ps : List Nat) (a : Nat) :
    (graphOfRecords roots live admittedKind).edges ps a ↔
      ∃ e, e ∈ live ∧ admittedKind e.kind = true ∧ e.premises = ps ∧ e.head = a := Iff.rfl

structure Cell where
  kind : Nat
  left : Nat
  right : Nat
  leftPort : Port
  rightPort : Port
  deriving DecidableEq

def atPort (e : TypedEdge) (x : Nat) : Port → Bool
  | .head => decide (x = e.head)
  | .premise i => decide (e.premises[i]? = some x)

def supportsCell (e : TypedEdge) (c : Cell) : Bool :=
  decide (e.kind = c.kind) && atPort e c.left c.leftPort && atPort e c.right c.rightPort

def cellCount (edges : List TypedEdge) (c : Cell) : Nat :=
  (edges.filter (fun e => supportsCell e c)).length

def matrixCell (edges : List TypedEdge) (c : Cell) : Bool :=
  decide (0 < cellCount edges c)

def retainEdges (edges : List TypedEdge) (withdraw : List Nat) : List TypedEdge :=
  edges.filter (fun e => !(withdraw.contains e.id))

def editEdges (edges : List TypedEdge) (withdraw : List Nat)
    (added : List TypedEdge) : List TypedEdge := retainEdges edges withdraw ++ added

-- Exactly the supporting retained and new records, including parallel edges.
def updatedCellCount (edges : List TypedEdge) (withdraw : List Nat)
    (added : List TypedEdge) (c : Cell) : Nat :=
  cellCount (retainEdges edges withdraw) c + cellCount added c

theorem matrix_update_exact (edges added : List TypedEdge) (withdraw : List Nat)
    (c : Cell) : updatedCellCount edges withdraw added c =
      cellCount (editEdges edges withdraw added) c := by
  simp [updatedCellCount, cellCount, editEdges, List.filter_append]

theorem matrix_bit_update_exact (edges added : List TypedEdge) (withdraw : List Nat)
    (c : Cell) : decide (0 < updatedCellCount edges withdraw added c) =
      matrixCell (editEdges edges withdraw added) c := by
  rw [matrix_update_exact]
  rfl

def edgeOne : TypedEdge := ⟨10, 7, [0, 1], 2⟩
def edgeTwo : TypedEdge := ⟨11, 7, [0, 1], 2⟩
def premiseHeadCell : Cell := ⟨7, 0, 2, .premise 0, .head⟩
#guard cellCount [edgeOne, edgeTwo] premiseHeadCell == 2
#guard matrixCell (editEdges [edgeOne, edgeTwo] [10] []) premiseHeadCell
#guard !(matrixCell (editEdges [edgeOne, edgeTwo] [10, 11] []) premiseHeadCell)
#guard !(matrixCell [edgeOne] { premiseHeadCell with kind := 8 })
#guard !(matrixCell [edgeOne] { premiseHeadCell with leftPort := .head })
#guard !(matrixCell [edgeOne] { premiseHeadCell with leftPort := .premise 1 })
#guard matrixCell (editEdges [edgeOne] [10] [edgeTwo]) premiseHeadCell

example : (graphOfRecords (fun _ => False)
    (editEdges [edgeOne, edgeTwo] [10] []) (fun _ => true)).edges [0, 1] 2 := by
  exact ⟨edgeTwo, by decide, rfl, rfl, rfl⟩
example : ¬ (graphOfRecords (fun _ => False)
    (editEdges [edgeOne, edgeTwo] [10, 11] []) (fun _ => true)).edges [0, 1] 2 := by
  intro ⟨e, he, _⟩
  have hempty : editEdges [edgeOne, edgeTwo] [10, 11] [] = [] := by decide
  rw [hempty] at he
  exact List.not_mem_nil he

#print axioms matrix_update_exact
#print axioms matrix_bit_update_exact
#print axioms executable_full_agrees
#print axioms qualified_frontier_exact
#print axioms unaffected_exact
#print axioms incremental_exact
#print axioms retracted_cycles_do_not_bootstrap
#print axioms patchedInteraction_exact
#print axioms incrementalFrontier_exact
end HypergraphIncremental
