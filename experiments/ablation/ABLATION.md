# Follow-up factorial ablation

The earlier pilot combined collection reversal with parallel scheduling. This follow-up separates those factors, retaining the source pins, upstream test subset, interpreter/environment, and fixed chosen two-worker plan. Four randomized paired rounds execute all four arms once per round:

- **O1**: original pytest collection; one worker, click → attrs → tomli → packaging.
- **R1**: reversed pytest collection in each repository; same one-worker job sequence.
- **O2**: original collection; worker 0 packaging, worker 1 tomli → attrs → click.
- **R2**: reversed collection; same two-worker queues.

Arm order is pseudorandom from stored seed 20261118. The plan is written before execution. The two-worker plan was fixed from the prior pilot, not selected using follow-up timings. There are 64 upstream subprocess jobs across 16 whole-campaign observations. Each job has a fresh process and separate pytest temporary directory. Foreign tracked files are unmodified. Venues are local logical workers sharing the same host, CPU, memory, installation, and filesystem, not independent remote systems.

## Observed results

| Arm | Round 0 | Round 1 | Round 2 | Round 3 | Median seconds |
|---|---:|---:|---:|---:|---:|
| O1 | 6.944977 | 7.810755 | 7.118541 | 7.611545 | 7.365043 |
| R1 | 7.288516 | 6.931033 | 7.577125 | 8.769548 | 7.432821 |
| O2 | 5.462468 | 6.171382 | 6.112741 | 7.130049 | 6.142061 |
| R2 | 6.447086 | 7.022657 | 6.206587 | 8.020068 | 6.734872 |

**The evidence favors original collection plus the two-worker schedule, not reversal.** O2 beats O1 in all four paired rounds: median paired reduction 17.56%, ratio-of-medians reduction 16.61%. These are two different descriptive summaries. R1 loses to O1 in three of four rounds (0.92% higher median), while R2 loses to O2 in all four rounds (9.65% higher median). The combined R2 alternative loses against O1 in one round; its median is 8.56% lower, not the 19.06% reduction observed in the earlier three-round pilot. All of those observations remain in the evidence. No significance or universal speedup claim is made.

Every full round/arm retains 5,868 passing and two skipped tests. The synthetic original-order control has two passes; reversal has one pass and one failure and is rejected by the qualification predicate.

## Evidence checking

`verify_ablation.py` independently checks all 64 successful executions against the reference collection. It checks exact test node IDs; every setup/call/teardown outcome and skip reason; exact forward/reverse sequence; raw stdout hashes; external witness JSON agreement; source cleanliness; and the complete randomized arm/round sequence. `ablation-results/summary.json` contains derived statistics. No failed or slower measured arm is dropped.

A separate synthetic negative control deliberately has two tests sharing a global list: a producer and dependent consumer. Forward collection passes; reverse collection fails despite identical test identities. The receipt qualification predicate explicitly rejects the latter. This demonstrates that identity preservation alone is insufficient and prevents the runner from silently qualifying a detected order dependency. It is not a claim to detect all latent nondeterminism or hidden dependencies.

## Interpretation

Metrics are measured subprocess wall time, including startup, instrumented witness logging, and scheduling overhead. This is a small paired descriptive sample, not statistical proof of speed or causal isolation from shared-host load. All raw observations, ranges, wins and losses are reported. Original/reversed factors separate test collection order from worker count, but the worker-count factor also includes the fixed queue partition and queue order; it does not isolate hardware concurrency from job scheduling order.

The generic/instantiated Lean frontier proof in the pilot remains a proof about prior fixed per-job cost constants and candidate schedules. It is not a proof that these new observed times equal that model, that collection reversal is universally semantics-preserving, or that the measured arm is a global Pareto optimum. This follow-up does not rewrite source or test bodies. Current outcome agreement is empirical, scoped to the selected tests and recorded environment. Tests that skip remain skipped, not passed.

Run `reproduce.sh` for pinned source/dependency setup in a fresh directory; then `reproduce_ablation.sh`. Preserve provided receipts before rerunning. Build isolation dependencies and execution host are not fully hermetic.

## Standalone reproduction package correction

This corrected archive includes `reproduce.sh` (pinned source checkout and dependency installation only), `dependencies.lock`, `reproduce_ablation.sh`, both runner/checker scripts, the pytest witness plugin, the negative-control test, and original receipts. No earlier pilot archive is needed. In a fresh unpacked directory run `bash reproduce.sh`, then `bash reproduce_ablation.sh`. Network access is required to fetch sources and packages. For offline validation of the existing receipts only, run `sha256sum -c ABLATION-SHA256SUMS` and `python3 verify_ablation.py`; neither needs foreign source checkouts or pytest. These offline commands were checked on the extracted corrected package.
