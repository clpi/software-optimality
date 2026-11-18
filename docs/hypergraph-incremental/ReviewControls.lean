import HypergraphIncremental
open HypergraphIncremental

def cyclicOld : Hypergraph Nat := ⟨fun x => x = 0,
 fun ps h => (ps = [0] ∧ h = 1) ∨ (ps = [1] ∧ h = 0)⟩
def cyclicNew : Hypergraph Nat := ⟨fun _ => False, cyclicOld.edges⟩
example : derives cyclicOld 1 := .step (Or.inl ⟨rfl,rfl⟩) (by
 intro p hp; simp at hp; subst p; exact .root rfl)
example (x : Nat) : ¬ incremental cyclicOld cyclicNew x := by
 apply retracted_cycles_do_not_bootstrap cyclicOld cyclicNew (fun _ h => h) _ x
 intro ps h hr
 rcases hr with ⟨rfl,_⟩ | ⟨rfl,_⟩
 · exact ⟨0, by simp⟩
 · exact ⟨1, by simp⟩
def emptyEdge : Hypergraph Nat := ⟨fun _ => False, fun ps h => ps = [] ∧ h = 2⟩
def noEdges : Hypergraph Nat := ⟨fun _ => False, fun _ _ => False⟩
example : Affected emptyEdge noEdges 2 := .edge (ps := []) (by
 intro h; exact h.mp ⟨rfl,rfl⟩)
example : Affected noEdges emptyEdge 2 := affected_symm (by
 exact Affected.edge (ps := []) (by intro h; exact h.mp ⟨rfl,rfl⟩))
example : incremental noEdges emptyEdge 2 :=
 (incremental_exact _ _ _).mpr (.step ⟨rfl,rfl⟩ (by simp))
example : ¬ incremental emptyEdge noEdges 2 := by
 intro h
 have hn := (incremental_exact _ _ _).mp h
 exact Qualification.least (X := fun _ => False) (fun _ h => h)
   (fun _ _ h _ => h) 2 hn
-- Deleting one support path must preserve another surviving path.
def alternativeOld : Hypergraph Nat := ⟨fun x => x = 0 ∨ x = 1,
 fun ps h => (ps = [0] ∨ ps = [1]) ∧ h = 2⟩
def alternativeNew : Hypergraph Nat := ⟨fun x => x = 1, alternativeOld.edges⟩
example : incremental alternativeOld alternativeNew 2 := by
 apply (incremental_exact _ _ _).mpr
 exact .step ⟨Or.inr rfl,rfl⟩ (by
   intro p hp; simp at hp; subst p; exact .root rfl)
-- Deleted edge still propagates dirtiness through old topology.
def oldChain : Hypergraph Nat := ⟨fun x => x = 0, fun ps h => ps = [0] ∧ h = 1⟩
example : Affected oldChain noEdges 1 := by
 exact .downstream (.root (by intro h; exact h.mp rfl))
   (Or.inl ⟨[0],⟨rfl,rfl⟩, by simp⟩)
-- Role/position and repeated incidence remain distinct.
example : incidence joint [0,1] 2 1 (.premise 1) := ⟨⟨rfl,rfl⟩,rfl⟩
example : ¬ incidence joint [0,1] 2 1 (.premise 0) := by
 intro h; cases h.2
example : ¬ interaction noEdges [] 2 2 2 .head .head := by
 intro h; exact h.1.1
#print axioms incremental_exact
-- Existential binary matrix projection: alternate edge support survives deletion.
def cell (g : Hypergraph Nat) (x y : Nat) (r s : Port) : Prop :=
 ∃ ps h, interaction g ps h x y r s
def twoSupports : Hypergraph Nat := ⟨fun _ => False,
 fun ps h => (ps = [0] ∨ ps = [0,1]) ∧ h = 2⟩
def oneSupport : Hypergraph Nat := ⟨fun _ => False,
 fun ps h => ps = [0,1] ∧ h = 2⟩
example : cell twoSupports 0 2 (.premise 0) .head :=
 ⟨[0],2,⟨⟨⟨Or.inl rfl,rfl⟩,rfl⟩,⟨⟨Or.inl rfl,rfl⟩,rfl⟩⟩⟩
example : cell oneSupport 0 2 (.premise 0) .head :=
 ⟨[0,1],2,⟨⟨⟨rfl,rfl⟩,rfl⟩,⟨⟨rfl,rfl⟩,rfl⟩⟩⟩
example : ¬ cell noEdges 0 2 (.premise 0) .head := by
 rintro ⟨ps,h,hi⟩; exact hi.1.1
-- Reordering a premise list changes typed incidence, even at unchanged head.
def reordered : Hypergraph Nat := ⟨fun _ => False,
 fun ps h => ps = [1,0] ∧ h = 2⟩
example : ¬ cell reordered 0 2 (.premise 0) .head := by
 rintro ⟨ps,h,hi⟩
 obtain ⟨rfl,rfl⟩ := hi.1.1
 cases hi.1.2
example : cell reordered 0 2 (.premise 1) .head :=
 ⟨[1,0],2,⟨⟨⟨rfl,rfl⟩,rfl⟩,⟨⟨rfl,rfl⟩,rfl⟩⟩⟩
example : Affected oneSupport reordered 2 := .edge (ps := [0,1]) (by
 intro h
 have bad := (h.mp ⟨rfl,rfl⟩).1
 contradiction)
-- Receipt identity/admission boundaries: raw list multiplicity is intentional.
#guard cellCount [edgeOne,edgeOne] premiseHeadCell == 2
#guard !(matrixCell (editEdges [edgeOne,edgeOne] [10] []) premiseHeadCell)
#guard matrixCell (editEdges [edgeOne] [10] [edgeOne]) premiseHeadCell
-- Replacement changes typed view: old kind disappears, new kind appears.
#guard !(matrixCell (editEdges [edgeOne] [10] [{edgeOne with kind := 8}]) premiseHeadCell)
#guard matrixCell (editEdges [edgeOne] [10] [{edgeOne with kind := 8}]) {premiseHeadCell with kind := 8}
#guard updatedCellCount [edgeOne,edgeTwo] [10] [] premiseHeadCell == 1
#guard updatedCellCount [edgeOne,edgeTwo] [10,11] [] premiseHeadCell == 0
#guard updatedCellCount [edgeOne] [10] [{edgeTwo with premises := [1,0]}] premiseHeadCell == 0
#guard updatedCellCount [edgeOne] [10] [{edgeTwo with premises := [1,0]}] {premiseHeadCell with leftPort := .premise 1} == 1
