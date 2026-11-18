import ExecutableIncremental
open ExecutableIncremental

private def atoms := [false,true]
private def possibleRules := (ExecutableClosure.subsets atoms).flatMap
  (fun ps => atoms.map (fun a => (ps,a)))

private structure Fixture where
  snapshot : Snapshot Bool
  cache : List Bool
  oracle : List Bool

private def fixtures : List Fixture := (ExecutableClosure.subsets atoms).flatMap (fun roots =>
  (ExecutableClosure.subsets possibleRules).map (fun rs =>
    let s := Snapshot.mk roots rs
    ⟨s, full s, ExecutableClosure.close atoms roots rs⟩))

-- Enumerate every root set and every set of conjunctive implications on
-- two atoms. Precompute the powerset-oracle answer once per snapshot.
def main : IO Unit := do
  let cases := fixtures.toArray
  let mut count := 0
  for hi : i in [:cases.size] do
    let old := cases[i]
    for hj : j in [:cases.size] do
      let new := cases[j]
      let got := update old.snapshot new.snapshot old.cache
      unless atoms.all (fun a => got.contains a == new.oracle.contains a) do
        throw (IO.userError s!"closure mismatch old={i} new={j}")
      count := count + 1
  unless cases.size == 1024 && count == 1048576 do
    throw (IO.userError s!"incomplete enumeration: {cases.size} snapshots, {count} edits")
  IO.println s!"{cases.size} snapshots; {count} ordered snapshot pairs agree with powerset closure."
