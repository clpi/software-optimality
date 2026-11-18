# Four reads even with an adaptive solver

| Before | After |
|---|---|
| 4,096 individual sample reads | 4 bank-total reads |

A 4,096-sample window has four banks. A read may return any contiguous signed sum inside one bank. The solver may choose the next location using the actual answer to its last read.

## Derivation

Shift every prefix potential on one side of an untouched bank boundary by one. Every answer the solver obtained stays identical, so its entire adaptive transcript repeats, while the required total changes. This holds on every input. Reading each whole bank reaches the four-read floor.

## Replay

From the repository root run `sh examples/check.sh` to check both example series. To run this case alone use `sh examples/range-ledger/check.sh`. The [Lean proof](AdaptiveReads.lean) and [verification transcript](verification.txt) record the positive result and a rejected semantic mutation.

## Scope

Independent arbitrary signed samples, exact sums, a terminating deterministic reader, no cached cross-bank result, and one unit per scalar answer. Cross-bank receipts change the read catalog.
