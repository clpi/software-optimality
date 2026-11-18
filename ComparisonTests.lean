import ComparisonContract
namespace ComparisonTests
open ComparisonContract

def latency : Axis := ⟨10,1,.minimize,50⟩
def throughput : Axis := ⟨11,3,.maximize,51⟩
def base : Contract := ⟨[latency],100,200,300⟩
def micros : Contract := {base with axes := [{latency with unit := 2}]}
def axisChanged (a : Axis) : Contract := {base with axes := [a]}
def raw (c : Contract) (xs : List Int) : Raw := ⟨c,xs⟩

#guard direct (raw base [2]) (raw base [3]) == some true
#guard direct (raw base [3]) (raw base [2]) == some false
#guard direct (raw base [2]) (raw base [2]) == some false
#guard direct (raw base [2]) (raw micros [3000]) == none
#guard direct (raw base [2]) (raw (axisChanged {latency with metric := 99}) [3]) == none
#guard direct (raw base [2]) (raw (axisChanged {latency with direction := .maximize}) [3]) == none
#guard direct (raw base [2]) (raw (axisChanged {latency with aggregation := 99}) [3]) == none
#guard direct (raw base [2]) (raw {base with workload := 999} [3]) == none
#guard direct (raw base [2]) (raw {base with venue := 999} [3]) == none
#guard direct (raw base [2]) (raw {base with epoch := 999} [3]) == none
#guard direct (raw base []) (raw base [3]) == none
#guard direct (raw base [2]) (raw base []) == none
#guard direct (raw base [2,9]) (raw base [3]) == none
#guard direct (raw base [2]) (raw base [3,9]) == none
#guard direct (raw {base with axes := []} []) (raw {base with axes := []} []) == some false
#guard direct (raw (axisChanged throughput) [3]) (raw (axisChanged throughput) [2]) == some true
#guard direct (raw {base with axes := [latency,throughput]} [2,3])
  (raw {base with axes := [latency,throughput]} [3,2]) == some true
#guard direct (raw {base with axes := [latency,throughput]} [2,1])
  (raw {base with axes := [latency,throughput]} [3,2]) == some false
#guard direct (raw {base with axes := [latency,throughput]} [2,3])
  (raw {base with axes := [throughput,latency]} [3,2]) == none

-- Concrete exact unit interpretation, not an inferred empirical equivalence.
-- For this example contract's milliseconds, meaning is microseconds.
def meaning (c : Contract) (xs : List Int) : List Int :=
  if c = base then xs.map (fun x => x * 1000) else xs

def msToUs : Transport meaning base micros where
  convert xs := xs.map (fun x => x * 1000)
  shape xs h := by
    simpa [valid,base,micros] using h
  preserves xs _ := by
    simp [meaning]
    have h : micros ≠ base := by decide
    simp [h]

def obsMs : Observation base := ⟨[2],by decide⟩
def obsUs : Observation micros := ⟨[3000],by decide⟩
def usIdentity := Transport.identity meaning micros
#guard compareVia msToUs usIdentity obsMs obsUs == true
#guard (msToUs.apply obsMs).values == [2000]
#guard ((msToUs.compose usIdentity).apply obsMs).values == [2000]
example : meaning base obsMs.values = meaning micros (msToUs.apply obsMs).values :=
  transported_meaning msToUs obsMs

-- Counterexample: naive numeric comparison incorrectly concludes 2ms < 3us.
#guard (2 : Int) < 3
#guard direct (raw base [2]) (raw micros [3]) == none
#guard compareVia msToUs usIdentity ⟨[2],by decide⟩ ⟨[3],by decide⟩ == false
-- A deliberately invalid unit identity transport cannot preserve this meaning.
example : meaning base [2] ≠ meaning micros [2] := by decide

-- Same numeric units do not silently grant workload/venue/epoch transport.
example : direct (raw base [2]) (raw {base with venue := 201} [3]) = none := by decide
example : direct (raw base [2]) (raw {base with epoch := 301} [3]) = none := by decide
end ComparisonTests
