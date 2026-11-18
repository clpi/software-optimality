import ComparisonTests
open ComparisonContract ComparisonTests
-- Negative samples remain exact signed comparisons; maximize reverses safely.
#guard direct (raw base [-3]) (raw base [-2]) == some true
#guard direct (raw (axisChanged throughput) [-3]) (raw (axisChanged throughput) [-2]) == some false
-- A joint tradeoff is nondominance, not a valid no-worse result.
#guard direct (raw {base with axes := [latency,throughput]} [1,1])
 (raw {base with axes := [latency,throughput]} [2,2]) == some false
#guard direct (raw {base with axes := [latency,throughput]} [2,2])
 (raw {base with axes := [latency,throughput]} [1,1]) == some false
-- Units must be converted in the right direction; equality is not strictness.
#guard compareVia msToUs usIdentity ⟨[2],by decide⟩ ⟨[2000],by decide⟩ == false
#guard compareVia msToUs usIdentity ⟨[3],by decide⟩ ⟨[2000],by decide⟩ == false
#guard compareVia msToUs usIdentity ⟨[-3],by decide⟩ ⟨[-2000],by decide⟩ == true
-- A transport preserves this declared full semantic vector, not just length.
example : ¬ (∀ xs, valid base xs → meaning base xs = meaning micros xs) := by
 intro h
 have bad := h [2] (by decide)
 have unequal : meaning base [2] ≠ meaning micros [2] := by decide
 exact unequal bad
-- Empty contract observations cannot claim strict improvement.
#guard direct (raw {base with axes := []} [1]) (raw {base with axes := []} []) == none
