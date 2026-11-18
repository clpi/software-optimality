import composition.QualifiedClosure
import ExecutableClosure
import Std

/-- Compare the two bounded, executable implementations on the same Horn
    chain with one root. Measure complete evaluation of the returned list. -/
private def timed (action : Unit → Option (List Nat)) : IO (Nat × Nat) := do
  let start ← IO.monoNanosNow
  let n := ((action ()).getD []).length
  let stop ← IO.monoNanosNow
  return (stop-start,n)

def main : IO Unit := do
  IO.println "facts,round,first,scan_ns,reference_ns"
  for n in [6,10,14] do
    let u := List.range n
    let rules := (List.range (n-1)).map (fun i => ([i], i+1))
    let scan := fun () => QualifiedClosure.checked u [0] rules
    let reference := fun () => ExecutableClosure.checkedClose u [0] rules
    unless scan () == some u && reference () == some u do
      throw (IO.userError "wrong closure")
    for round in List.range 5 do
      let scanFirst := round % 2 == 0
      let (s, r) ← if scanFirst then do
        let s ← timed scan
        let r ← timed reference
        pure (s,r)
      else do
        let r ← timed reference
        let s ← timed scan
        pure (s,r)
      unless s.2 == n && r.2 == n do throw (IO.userError "wrong result size")
      IO.println s!"{n},{round},{if scanFirst then "scan" else "reference"},{s.1},{r.1}"
