import OptimalityInterface

open Optimality

/-- Executable witness that the proved guards accept a no-worse release and
    refuse a Pareto trade, an out-of-universe closure, and a non-strict
    product reduction. Exit status is zero only when every refusal fires. -/
def main : IO UInt32 := do
  if acceptGuardedRelease && refusalRegressingFrontier && refusalOutOfUniverse &&
      refusalNonstrictReduction && acceptSumReduction then
    IO.println "guarded-release accept"
    IO.println "regressing-frontier refuse"
    IO.println "out-of-universe refuse"
    IO.println "nonstrict-reduction refuse"
    IO.println "sum-reduction accept"
    return 0
  else
    IO.println "checker disagreed with the proved guards"
    return 1
