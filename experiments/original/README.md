# Foreign-codebase schedule campaign: observed evidence and exact finite model

## Delivered result
Four pinned upstream Python repositories, eight actual upstream test files, 5,868 passing tests and two skipped tests in every campaign round. All 36 subprocess job runs succeeded. The alternative plan both reverses pytest's collected test order inside every job and executes jobs on two ordered queues concurrently. Exact collected node-ID multisets and reported (node-ID, phase, outcome) multisets matched all nine runs per repository. Reversal itself was checked against the original node-ID sequence.

Observed whole-campaign elapsed times, seconds:

| Round | Sequential original order | Concurrent reversed collection |
|---|---:|---:|
| 0 | 9.425403 | 6.521408 |
| 1 | 7.510873 | 6.906903 |
| 2 | 8.057266 | 5.877893 |
| Median | 8.057266 | 6.521408 |

The alternative's median is **19.06% lower (1.236× speedup)**. Three rounds, not a confidence-bound guarantee. Round order alternated to reduce ordering bias. Timing includes process startup. Shared-host contention, filesystem caches, and thermal/load variation remain uncontrolled. The two venues are local logical subprocess workers on the same machine, not remote hardware. This is not a cross-machine benchmark.

## Exact model and finite frontier
Use the median of three earlier sequential measurements per job as fixed integer nanosecond costs:

| ID | Job | Cost ns |
|---|---|---:|
| 0 | click | 1,033,599,117 |
| 1 | attrs | 687,668,287 |
| 2 | tomli | 293,138,741 |
| 3 | packaging | 6,991,879,848 |

Every job executes exactly once, each worker runs a serial queue, queues start together, and the model assumes duration independent of order/concurrency. There are exactly `4! × 5 = 120` ordered two-labeled-worker queue schedules, allowing empty queues and no idle gaps. `campaign.py` enumerates permutations and cut positions. `verify_receipt.py` independently enumerates all 16 assignments followed by permutations within each worker queue and checks equality, uniqueness, metrics, and frontier.

Axes minimized: modeled makespan and modeled sum of all job completion times. The exact four-member frontier (including symmetric venue swaps):

- `[[1,0],[2,3]]`, `[[2,3],[1,0]]`: `(7,285,018,589; 9,987,093,021)` ns.
- `[[2,1,0],[3]]`, `[[3],[2,1,0]]`: `(6,991,879,848; 10,280,231,762)` ns.

Chosen plan: packaging alone on worker 0; tomli then attrs then click on worker 1. This minimizes modeled makespan; another frontier point trades slightly more makespan for less total completion time. The baseline is click then attrs then tomli then packaging on one worker. No measured result was substituted for an unmeasured schedule: the 120-candidate frontier is explicitly a **cost-model** frontier. Only baseline and chosen schedules were executed three times. No claim that the observed performance frontier across all 120 schedules was measured, or that these schedules globally dominate all implementations.

## Sources and scope

- pallets/click `08b803cf32ceb2ae6a772c62d5da42757a897d44`: `tests/test_basic.py`, `tests/test_arguments.py` (315 pass).
- python-attrs/attrs `2a1fb86d44816afcc60e86d57956ce3604820326`: `tests/test_cmp.py`, `tests/test_converters.py` (116 pass).
- hukkin/tomli `43a86ade8b795c6ef9b4ec53372a607cd1ed426f`: `tests/test_error.py`, `tests/test_misc.py` (15 pass, 1 skip).
- pypa/packaging `6a69a83d8d89c6a01d554a8ad1b420cbb45fb4bc`: `tests/test_requirements.py`, `tests/test_errors.py` (5,422 pass, 1 skip).

These are test subsets, not full repository suites. An initial exploratory packaging version/requirements run also passed 56,939 tests, with one skip, in 48.92 seconds process wall time. The exploratory campaign was stopped during the second repetition and narrowed for turnaround; its partial logs are retained separately, not counted in the final campaign.

## What is and is not proved

Executed checks establish exact equality of observed selected IDs and outcomes, reversal, exhaustive candidate agreement, and exact arithmetic nondominance. They do not establish universal semantic independence of tests or source-program equivalence. Rewriting here is an execution-plan transformation (reorder collection and partition serial queues), **not source/test-body rewriting**. Production behavior, error-detection power, hidden side effects, remote venue portability, per-test independence, or universal performance improvement have not been proved. A finite schedule model is not a proof that every executable semantic property is decidable.

Generic Lean certificates are supplied separately by the proof task. Any concrete Lean receipt proves arithmetic/model membership/nondominance relative to its explicit candidate list and cost constants; it does not certify that the timing instrument or measured durations remain valid. The independent Python enumeration cross-check must not be described as a Lean completeness theorem.

## Reproduction and integrity

`reproduce.sh` fetches exactly the source commits, installs pinned runtime dependencies, and runs the campaign plus independent checker. Build-isolation toolchain dependencies are not fully hermetic. Use a fresh unpacked directory to preserve supplied receipts. Results retain raw logs, collected IDs, per-test outcomes, process commands/statuses, elapsed nanoseconds, environment versions, and source commits. `SHA256SUMS` binds delivered evidence bytes. No upstream source was edited or published.
