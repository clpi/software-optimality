import OptimalityInterface
import ExecutableIncremental
import composition.LiveSelection

namespace IncrementalSelection
open ExecutableIncremental QualifiedSelection
variable {C F : Type} [DecidableEq F]

/-- The release gate reads membership. An alternative representation of
    precisely the same facts must produce the same decision and ordering. -/
theorem choose_congr (data : Campaign C F) (xs ys : List F)
    (same : ∀ f, f ∈ xs ↔ f ∈ ys) (catalogue : List C) (inc : C) :
    choose data xs catalogue inc = choose data ys catalogue inc := by
  have gates (c : C) : gate data xs c = gate data ys c := by
    apply Bool.eq_iff_iff.mpr
    simp only [gate_exact,same]
  have admissions : admitted data xs inc = admitted data ys inc := by
    funext c
    simp only [admitted,gates]
  simp only [choose,admissions,gates]

def selectCached (data : Campaign C F) (u : List F) (state : State F)
    (catalogue : List C) (inc : C) : Option (List C) :=
  if ExecutableClosure.boundedOK u state.snapshot.roots state.snapshot.rules then
    choose data state.cache catalogue inc
  else none

theorem selectCached_exact (data : Campaign C F) (u : List F) (state : State F)
    (catalogue : List C) (inc : C) :
    selectCached data u state catalogue inc = QualifiedSelection.select data u
      state.snapshot.roots state.snapshot.rules catalogue inc := by
  unfold selectCached QualifiedSelection.select
  split
  next hb =>
    let s := state.snapshot
    let facts := QualifiedClosure.rounds u s.roots s.rules (u.length+1)
    have h : QualifiedClosure.checked u s.roots s.rules = some facts := by
      simp [QualifiedClosure.checked,s,hb,facts]
    change choose data state.cache catalogue inc = (QualifiedClosure.checked u s.roots s.rules).bind _
    rw [h]
    apply choose_congr
    intro a
    have eqv := (QualifiedClosure.checked_exact _ _ _ _ h s.graph a).1
    exact (reachable_exact state.history a).trans
      (eqv.trans (HypergraphIncremental.incremental_exact _ _ a)).symm
  next hb =>
    simp [QualifiedClosure.checked,hb]

/-- Compute the live graph once from the normalized event ledger. All reverse
    dependencies used by advance are derived from this and the old snapshot. -/
def snapshot (d : LiveSelection.Decoder F) (auth : Admission.Event → Bool)
    (ledger : List Admission.Event) : Snapshot F :=
  let rows := Admission.normalized auth ledger
  ⟨rows.flatMap d.roots,rows.flatMap d.rules⟩

/-- The projection may select new contract, measurements, universe, catalogue
    and incumbent at each revision. Equal outputs include both failure forms
    and the entire ordered list, even through withdrawals and changed costs. -/
theorem live_revision (old : State F) (d : LiveSelection.Decoder F)
    (auth : Admission.Event → Bool) (ledger : List Admission.Event)
    (data : Campaign C F) (u : List F) (catalogue : List C) (inc : C) :
    selectCached data u (advance old (snapshot d auth ledger)) catalogue inc =
      LiveSelection.select d auth ledger data u catalogue inc :=
  selectCached_exact _ _ _ _ _

/-- The campaign, finite domain, competitors and baseline are read from this
    revision of the authoritative graph. A caller can store the returned cache
    for the next revision. There is no independently maintained dependency input. -/
structure Release (C F : Type) where
  campaign : Campaign C F
  domain : List F
  catalogue : List C
  incumbent : C

def evaluate (old : State F) (s : Snapshot F) (read : Snapshot F → Release C F) :
    State F × Option (List C) :=
  let next := advance old s
  let r := read s
  (next, selectCached r.campaign r.domain next r.catalogue r.incumbent)

theorem evaluate_exact (old : State F) (s : Snapshot F) (read : Snapshot F → Release C F) :
    let r := read s
    (evaluate old s read).2 =
      QualifiedSelection.select r.campaign r.domain s.roots s.rules r.catalogue r.incumbent :=
  selectCached_exact _ _ _ _ _

theorem replay_agrees_with_coloring (state : State F) (a : F) :
    a ∈ state.cache ↔
      SoftwareIsQuantifiable.Coloring.coloring (QualifiedClosure.horn state.snapshot.rules)
        (state.snapshot.rules.map Prod.snd) (SoftwareIsQuantifiable.Fold.account state.snapshot.roots) a = true := by
  let s := state.snapshot
  have hb : ∀ r ∈ QualifiedClosure.horn s.rules, r.conclusion ∈ s.rules.map Prod.snd := by
    intro r hr
    obtain ⟨⟨ps,x⟩,hm,rfl⟩ := List.mem_map.mp hr
    exact List.mem_map_of_mem hm
  exact (reachable_exact state.history a).trans
    ((QualifiedClosure.derivations_agree s.roots s.rules a).symm.trans
      ⟨SoftwareIsQuantifiable.Coloring.coloring_complete _ _ _ hb a,
       SoftwareIsQuantifiable.Coloring.coloring_sound _ _ _ a⟩)

/-- Check both point interfaces in one kernel, including candidate
    order and ties. The implementations use different Boolean comparators. -/
theorem point_frontiers_agree (xs : List Optimality.Point) :
    Optimality.paretoMaximal xs = SoftwareIsQuantifiable.Pareto.frontier xs := by
  have cmp : Optimality.dominatesBool = SoftwareIsQuantifiable.Pareto.dominatesB := by
    funext a b
    apply Bool.eq_iff_iff.mpr
    rw [SoftwareIsQuantifiable.Pareto.dominatesB_iff]
    exact decide_eq_true_iff
  simp only [Optimality.paretoMaximal, FiniteFrontier.frontier, SoftwareIsQuantifiable.Pareto.frontier, cmp]

/-- The canonical public gate supplies release admission. This theorem only
    projects its obligations through the existing local point representation. -/
theorem release_gate_exact {B K : Type} [DecidableEq B] [DecidableEq K] (before after : K)
    (prior : SoftwareIsQuantifiable.Pareto.PriorQualification B)
    (offered : SoftwareIsQuantifiable.Pareto.BehaviorSubmission B) (inc out : Optimality.Point) :
    SoftwareIsQuantifiable.Pareto.acceptsRelease before after prior offered inc out = true ↔
      after = before ∧ (∀ b ∈ prior.qualified, b ∈ offered.offered) ∧ Optimality.noWorse out inc := by
  simpa only [Optimality.noWorse, SoftwareIsQuantifiable.Pareto.noWorse] using
    SoftwareIsQuantifiable.Pareto.acceptsRelease_iff before after prior offered inc out

/-- Feed the actual incremental result to the existing finite-generator
    coverage certificate. Invalid universe, refused certificate, and accepted
    certificate are three distinct results. -/
def certifyCached (state : State F) (u : List F) (k : ScopedFrontier.Contract)
    (domain catalogue retained : List ScopedFrontier.Subject)
    (project : (F → Bool) → ScopedFrontier.Subject → ScopedFrontier.Input) : Option Bool :=
  if ExecutableClosure.boundedOK u state.snapshot.roots state.snapshot.rules then
    some (ScopedFrontier.certifyCovered k domain catalogue retained
      (project (fun a => decide (a ∈ state.cache))))
  else none

theorem certificate_eq_full (state : State F) (u : List F) (k : ScopedFrontier.Contract)
    (domain catalogue retained : List ScopedFrontier.Subject)
    (project : (F → Bool) → ScopedFrontier.Subject → ScopedFrontier.Input) :
    certifyCached state u k domain catalogue retained project =
      ScopedFrontier.certifyClosed u state.snapshot.roots state.snapshot.rules k
        domain catalogue retained project := by
  let s := state.snapshot
  unfold certifyCached ScopedFrontier.certifyClosed
  split
  next ok =>
    let fullFacts := ExecutableClosure.close u s.roots s.rules
    have checked : ExecutableClosure.checkedClose u s.roots s.rules = some fullFacts := by
      simp [ExecutableClosure.checkedClose,s,ok,fullFacts]
    have spec := (ExecutableClosure.checkedClose_admitted _ _ _ _ checked).2.2
    have same : (fun a => decide (a ∈ state.cache)) = (fun a => decide (a ∈ fullFacts)) := by
      funext a
      apply Bool.eq_iff_iff.mpr
      simpa only [decide_eq_true_eq] using (reachable_exact state.history a).trans (spec a).symm
    simp only [s] at checked
    rw [checked,same]
    rfl
  next bad => simp [ExecutableClosure.checkedClose,bad]

#print axioms certificate_eq_full
#print axioms point_frontiers_agree
#print axioms release_gate_exact
#print axioms choose_congr
#print axioms selectCached_exact
#print axioms live_revision
#print axioms evaluate_exact
#print axioms replay_agrees_with_coloring
end IncrementalSelection
