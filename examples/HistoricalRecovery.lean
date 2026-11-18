import ObservationPublication
import HistoricalCertificates
open HistoricalEvidence ObservationPlanning

namespace HistoricalExample
def oldRun : Run := ⟨"build", "r1", "release", "unlisted-A"⟩
def newRun : Run := ⟨"build", "r2", "release", "run-B"⟩
def existQ := Question.mk oldRun .occurrence
def exitQ := Question.mk oldRun (.attribute "exit")
def fastQ := Question.mk oldRun (.attribute "fast")
def nextExit := Question.mk newRun (.attribute "exit")
def model (w : Nat) : Question → Option Nat := reading (fun r =>
  if r = newRun then some (fun _ => 0) else if r = oldRun ∧ w ≠ 0 then
    some (fun f => if f = "exit" then (if w = 1 then 0 else 1) else (if w = 1 then 1 else 0))
  else none)
def ws := [0,1,2]
def atom (q : Question) (v : Nat) : Atom := ⟨q,some v⟩
def receipt (q : Question) (v : Nat) (hook := false) : Receipt :=
  ⟨atom q v,10,"collector","external-evidence",hook⟩
def witness (id : Nat) (q : Question) (v : Nat) (route := Route.backfill) : Row :=
  ⟨id,id,20,"collector","v1",route,[],atom q v,some (receipt q v (route == .hookSample))⟩
def hint (route : Route) (id : Nat) (head : Atom) : Row :=
  ⟨id,id,20,"other-tool","v1",route,[],head,none⟩
def archive := witness 1 exitQ 0
def future := witness 2 nextExit 0 .hookSample
def trust (_ : Event) := true
def valid (w : Receipt) := decide (w ∈ [receipt exitQ 0,receipt nextExit 0 true,receipt exitQ 1])
def base : List Event := [.put archive, .put future]
def after := backfillOne ws model "v1" valid trust base fastQ 30
def qualified (log : List Event) := certified ws model "v1" valid trust log

example : consequences ws model valid [] existQ = .ambiguous 0 1 := by decide
example : consequences ws model valid [future] existQ = .ambiguous 0 1 := by decide
example : consequences ws model valid [archive] existQ = .exact (some 1) := by decide
example : (discover [] [hint .discovery 9 (atom existQ 1)]) = [oldRun] := by decide
example : qualified [.put (hint .discovery 9 (atom existQ 1))] = some [] := by decide
example : qualified [.put (hint .independentPrediction 3 (atom exitQ 0))] = some [] := by decide
example : qualified [.put (hint .hookPlan 4 (atom nextExit 0))] = some [] := by decide
example : measurement valid {archive with head := atom nextExit 0} = false := by decide
example : measurement valid {archive with appendedAt := 9} = false := by decide
example : qualified [.put archive,.put (witness 5 exitQ 1)] = none := by decide
example : color [atom exitQ 0,atom exitQ 1] (atom exitQ 0) = .conflict := by decide
example : qualified [.put archive,.put {archive with source := "altered"}] = some [] := by decide
example : qualified [.put archive,.put archive] = qualified [.put archive] := by decide
example : (qualified after).any (fun xs => decide (atom fastQ 1 ∈ xs)) = true := by decide
example : (qualified (append after (.withdraw 1))).any (fun xs => decide (atom fastQ 1 ∈ xs)) = false := by decide
example : atom nextExit 0 ∈ (qualified (append after (.withdraw 1))).getD [] := by decide
example : qualified [.put {hint .replay 6 (atom exitQ 0) with parents := [atom nextExit 0]} , .put future]
    = some [atom nextExit 0] := by decide
example : bets ws (fun w => if w = 2 then 5 else 1) model exitQ = [some 1] := by decide
example : bets ws (fun _ => 0) model exitQ = [] := by decide

-- With no measurements the model does entail the new status; it still leaves
-- the old status unresolved. Removing this model restriction removes the result.
example : consequences ws model valid [] nextExit = .exact (some 0) := by decide
example : (derive ws model "v1" valid [] nextExit 0 20).map Row.route = some .symbolic := by decide
example : color (roots valid []) (atom nextExit 0) = .unknown := by decide
example : consequences [] model valid [] exitQ = .inconsistent := by decide
example : (qualified [.put archive, .put {hint .transfer 7 (atom fastQ 1) with
    model := "stale", parents := [atom exitQ 0]}]).any (fun xs => decide (atom fastQ 1 ∈ xs)) = false := by decide

-- The late hook returns the same value in all worlds. An independently
-- retained historical bit separates absent from present; two more sensors
-- separate the underlying outcomes. Resource costs are modeled probe counts.
def probe : Nat → Nat → Bool
  | 0, _ => true
  | 1, w => decide (w ≠ 0)
  | 2, w => decide (w = 1)
  | _, w => decide (w = 2)
def decisionTree : Plan Nat := .probe 1 .stop (.probe 2 .stop .stop)
def resources (p : Plan Nat) (_ : Nat) : Int :=
  Int.ofNat ((ws.map (fun w => (transcript probe p w).length)).sum)
def objective := objectives ws [exitQ] model [0]
def mustResolve (p : Plan Nat) := resolves ws [exitQ] model probe p
#guard resolves ws [existQ] model probe (.probe 0 .stop .stop) = false
#guard mustResolve decisionTree
#guard decode ws model exitQ probe decisionTree (transcript probe decisionTree 1) = .exact (some 0)
#guard (plans [1,2] 2).length = 19
#guard (optimal [0] 2 mustResolve objective probe resources).isEmpty
#guard !(optimal [1,2] 2 mustResolve objective probe resources).isEmpty
#guard decisionTree ∈ optimal [1,2] 2 mustResolve objective probe resources
#guard resources decisionTree 0 = 5

-- A zero-measurement arithmetic invariant across every natural input.
def infiniteModel (n : Nat) (q : Question) : Option Nat :=
  if q = fastQ then some (if n + 1 > n then 1 else 0) else some n
def arithmetic := hint .symbolic 40 (atom fastQ 1)
def arithmeticProof : RuleProof (fun _ : Nat => True) infiniteModel "v1" where
  row := arithmetic
  shape := ⟨rfl,rfl,rfl⟩
  sound := by intro n _ _; simp [infiniteModel,arithmetic,hint,atom,Nat.lt_succ_self]
example : atom fastQ 1 ∈ closeRegistered [arithmeticProof] valid trust [.put arithmetic] := by decide
example : atom fastQ 1 ∉ closeRegistered [arithmeticProof] valid trust [.put arithmetic,.withdraw 40] := by decide

-- Two exact backends. Example prices are declared model costs.
private def jointCost (ep : Engine String × Plan Nat) (_ : Nat) : Int :=
  resources ep.2 0 + if ep.1.id = "worklist" then 0 else 10
#guard ((joint [worklistEngine,referenceEngine] [1,2] 2 (fun ep => mustResolve ep.2)
  objective probe jointCost).all (fun ep => ep.1.id == "worklist"))
#guard !((joint [worklistEngine,referenceEngine] [1,2] 2 (fun ep => mustResolve ep.2)
  objective probe jointCost).isEmpty)

#print axioms HistoricalEvidence.registered_sound
#print axioms HistoricalEvidence.live_exact
#print axioms HistoricalEvidence.derive_iff
#print axioms HistoricalEvidence.batch_complete
#print axioms HistoricalEvidence.published_batch_exact
#print axioms HistoricalEvidence.backfill_publishes
#print axioms HistoricalEvidence.advisory_inert
#print axioms HistoricalEvidence.certified_sound
#print axioms HistoricalEvidence.transport_recovery
#print axioms HistoricalEvidence.bet_exact
#print axioms ObservationPlanning.factorization
#print axioms ObservationPlanning.full_observability_iff
#print axioms ObservationPlanning.boundedCount_exact
#print axioms ObservationPlanning.dominates_axes
#print axioms ObservationPlanning.optimal_exact
#print axioms ObservationPlanning.joint_exact
#print axioms ObservationPlanning.joint_publication
#print axioms ObservationPlanning.engine_instantiates_exactly
end HistoricalExample
