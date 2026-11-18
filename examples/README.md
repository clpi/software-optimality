# Release packaging on two CI runners

| Before | After |
|---|---|
| 23 ticks, serial | 16 ticks, parallel |

The build takes 5 ticks. Integration takes 9 and formatting takes 7. Both need the build. Packaging takes 2 and needs both checks. The winning schedule starts both checks at tick 5 and packages at tick 14.

## Why the bound holds

For any feasible schedule, the build → integration → package chain costs at least 5 + 9 + 2 = 16 ticks. The witness attains this lower bound on two runners. The bound even survives adding more runners or increasing the start horizon. Starting package at tick 13 violates a dependency.

## Replay

Run from the repository root with Lean 4.19.0 available.

```sh
sh examples/check.sh
```

The runner checks the [proof](ReleaseSchedule.lean) with warnings as errors and prints the computed result and theorem dependencies.

The [verification transcript](verification.txt) includes the observed outputs and the rejected counterexample mutation.

## Scope

Inputs are fixed positive durations, homogeneous capacity-one runners, and the four listed jobs. This measures schedule length in model ticks. Machine timing and resource contention need their own observations.
