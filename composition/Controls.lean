import composition.QualifiedSelection
import composition.IntervalDominance
import composition.LiveSelection
import ScopedCampaign

namespace CompositionControls
open QualifiedSelection

-- Four candidates for a two-metric release. Metric 0 is steady-state latency and metric 1
-- is recovery latency in this synthetic model; both must be minimized.
private def k : Contract := ⟨20,4,70,3,1,2,[⟨0,1⟩,⟨1,1⟩],[⟨0,0,50⟩,⟨1,0,50⟩],[⟨0,0,false⟩,⟨1,0,false⟩]⟩
private def subject (c : Nat) : Subject := ⟨5, c, 3⟩
private def values (c : Nat) : Nat × Nat :=
  match c with
  | 0 => (10,10)
  | 1 => (6,9)
  | 2 => (8,6)
  | _ => (1,11)
private def receipts (c : Nat) : List ScopedEvidence.Receipt :=
  [⟨2*c, scope k (subject c) 0, 0, true, some (values c).1⟩,
   ⟨2*c+1, scope k (subject c) 1, 0, true, some (values c).2⟩]
private def data : Campaign Nat Nat :=
  ⟨k, subject, (fun c => ⟨k, receipts c⟩), fun r => ⟨r.id⟩,
   (List.range 8).map (fun i => ⟨i,1⟩), fun w => decide (w.events > 0),
   [0], fun c b => 2*c+b, fun c b => 2*c+b+1⟩
private def u := List.range 10
private def rules : QualifiedClosure.Rules Nat := [([8,9],2), ([2],2)]
private def go (d : Campaign Nat Nat) (roots : List Nat) (catalogue := [0,1,2,3]) :=
  select d u roots rules catalogue 0

-- Candidate 3 is fastest but regresses on recovery latency. Both trade-offs 1 and 2 survive.
example : go data [0,4,6,8,9] = some [1,2] := by decide
-- Retracting one joint premise removes 1 despite its self-loop.
example : go data [0,4,6,8] = some [2] := by decide
-- An independent root supports 1 again; adding its contrary still vetoes it.
example : go data [0,2,4,6,8] = some [1,2] := by decide
example : go data [0,2,3,4,6,8] = some [2] := by decide
-- Both dominators withdrawn: the incumbent reappears.
example : go data [0,6,8] = some [0] := by decide
-- A valid empty catalogue differs from an invalid snapshot or invalid baseline.
example : go data [0] [] = some [] := by decide
example : go data [0,42] [] = none := by decide
example : go data [4] = none := by decide
-- Remove the live ledger rows for candidate 1; local pass bits remain true.
example : go {data with ledger := data.ledger.filter (fun w => w.exec != 2)}
    [0,4,6,8,9] = some [2] := by decide
-- One execution can supply different metrics. Two rounds of the same metric
-- cannot be discharged by mapping two receipt identities to one execution.
example : go {data with execution := fun _ => ⟨0⟩} [0,4,6,8,9] = some [1,2] := by decide
private def repeatK := {k with required := [⟨0,0,50⟩,⟨0,1,50⟩], axes := [⟨0,0,false⟩,⟨0,1,false⟩]}
private def repeatData : Campaign Nat Nat := {data with
  contract := repeatK
  inputs := fun c => ⟨repeatK, [⟨2*c,scope repeatK (subject c) 0,0,true,some 5⟩,
    ⟨2*c+1,scope repeatK (subject c) 0,1,true,some 6⟩]⟩
  execution := fun _ => ⟨0⟩}
example : go {repeatData with execution := fun r => ⟨r.id⟩} [0,4,6,8,9] = some [0,1,2,3] := by decide
example : peakPolicy {repeatK with axes := [⟨0,0,false⟩]} = false := by decide
example : peakPolicy {k with axes := [⟨0,0,true⟩]} = false := by decide
example : go repeatData [0,4,6,8,9] = none := by decide
example : go {data with contract := {k with policy := 71}} [0,4,6,8,9] = none := by decide
example : go {data with contract := {k with required := []}} [0,4,6,8,9] = none := by decide
example : QualifiedClosure.checked [0] [0] [([0],1)] = none := by decide
example : QualifiedClosure.checked [0,1] [] [([],1)] = some [1] := by decide
example : QualifiedClosure.checked [0,0,1] [] [([],0),([0],1)] = some [0,0,1] := by decide

-- Live events are decoded only after replay, conflict and withdrawal checks.
private def key (i : Nat) : Admission.Key := ⟨3,10,2,i⟩
private def payload (i : Nat) : Admission.Payload := ⟨i,true,1⟩
private def events := [0,2,4,6].map (fun i => Admission.Event.claim (key i) (payload i))
private def decoder : LiveSelection.Decoder Nat := ⟨fun row => [row.2.subject], fun _ => []⟩
private def liveRun (xs : List Admission.Event) :=
  LiveSelection.select decoder (fun _ => true) xs data u [0,1,2,3] 0
example : liveRun (events ++ events) = some [1,2] := by decide
example : liveRun (events ++ [.withdraw (key 2)]) = some [2] := by decide
example : liveRun (events ++ [.claim (key 2) (payload 7)]) = some [2] := by decide

-- With one timing metric across two rounds, a lower maximum can conceal
-- a regression in a particular round. Per-round caps remain independent.
example : [9,9].foldl max 0 < [8,10].foldl max 0 ∧ (9 : Nat) > 8 := by decide

private def lower (y x : Nat) := decide (y < x)
-- A cheaper local component lacks the required partner interface.
private def compatible : Nat → List Nat
  | 1 => []
  | _ => [7]
example : FrontierComposition.checkCover lower [1,2] [1] = true := by decide
example : FrontierComposition.checkCover lower ([1,2].flatMap compatible)
    ([1].flatMap compatible) = false := by decide
-- A shared bottleneck turns two different plans into tied optima.
private def bottleneck (y x : Nat) := decide (max 5 y < max 5 x)
example : FiniteFrontier.frontier [1,2] bottleneck = [1,2] := by decide
example : FrontierComposition.checkCover bottleneck [1,2] [1] = false := by decide
-- Projecting to the actual scalar value retains the complete value frontier.
example : FrontierComposition.checkCover lower ([1,2].map (max 5)) ([1].map (max 5)) = true := by decide
example : IntervalDominance.paired ([] : List Nat) [0] (fun _ _ => 0) (fun _ _ => 1) = false := by decide

-- Replay existing pilot rows through the partitioned frontier. No new physical runs.
open EligibleCampaign ScopedCampaign in
example : FiniteFrontier.frontier
    (FiniteFrontier.frontier ([Candidate.O1, .R2].filter
      (ScopedSelection.gate scopedPolicy scopedReceipts)) dominates ++
     FiniteFrontier.frontier ([Candidate.O2].filter
      (ScopedSelection.gate scopedPolicy scopedReceipts)) dominates) dominates = [.O2] := by decide
end CompositionControls
