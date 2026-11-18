# Empirically admitted finite schedule optimization, with tested counterfactual

This experiment operationalizes the requested contract: preserve the selected tests' observed behavior and do not regress measured execution time. It does not attempt to characterize all software behavior. The selected test IDs, setup/call/teardown outcomes and skip reasons supply the preservation evidence; measured wall time supplies the objective and timing gate. Venue allocation is execution-plan metadata, **not an invented quality axis**.

## Declared gate and objective

Before execution the policy fixed: all processes must succeed; selected node-ID sets and complete phase outcomes/skip reasons must equal the baseline within each paired round; and every candidate's whole-suite wall time must be no greater than that round's baseline, with zero tolerance. This is an empirical no-observed-regression constraint, not a user-specified absolute SLA or a claim about future runs.

Three plans were fixed and each was actually run in three pseudorandomized paired rounds (seed 2026111802):

- O1: original test collection, one serial queue (click, attrs, tomli, packaging), baseline.
- O2: original collection, worker 0 packaging; worker 1 tomli, attrs, click.
- R2: same O2 queues, but reverse collected test order inside each suite. This is the **tested counterfactual**, not an imagined alternate.

The sole minimization objective is maximum observed end-to-end wall time across the three rounds. The initial recorded policy also included allocated workers as an axis. During execution, before result analysis, the user's clarification removed that axis; both policies and their hashes are retained, and the active policy records the revision. Hard admission constraints did not change. This explicit pilot aggregation is not asserted to be a complete account of software quality.

## Results

| Plan | Round 0 seconds | Round 1 | Round 2 | Maximum | Median | Admitted |
|---|---:|---:|---:|---:|---:|---|
| O1 | 10.769190 | 7.296152 | 7.966428 | 10.769190 | 7.966428 | Yes |
| O2 | 5.429128 | 6.128443 | 6.240471 | 6.240471 | 6.128443 | Yes |
| R2 | 9.146681 | 6.480720 | 6.777396 | 9.146681 | 6.777396 | Yes |

All 36 foreign-suite subprocess runs succeeded. Every complete plan/round had 5,868 passed tests and two skipped tests. Exact identities, every phase outcome, and skip reasons matched the paired baseline. O2 and R2 each met the hard time constraint in every round.

The finite admitted candidate set is `{O1,O2,R2}`; its nondominated set under the sole declared wall-time objective is `{O2}`. O2's observed maximum is 6.240471 seconds, versus baseline 10.769190; its median is 6.128443 seconds versus 7.966428. The raw baseline maximum is noticeably variable, so maximum-based improvement is a property of these receipts, not a robust speed guarantee.

**Counterfactual:** R2 preserves these observed outcomes and is admitted, but is slower than O2 in all three paired rounds. Its maximum is 9.146681 seconds. It is dominated on the declared objective and retained in the catalogue with that explanation, not deleted or mislabeled inadmissible. There are no rejected empirical candidates in this run. The earlier separately packaged order-dependency negative control demonstrates rejection; no failure was fabricated to populate this run's rejected set. Prior ablation losses remain in prior artifacts and are not superseded by this run.

## Proof/evidence boundary

`qualify_receipt.py` derives admission from actual complete raw receipts, checks raw stdout hashes and witness-file agreement, and computes the finite admitted frontier. The separate Lean concrete certificate checks integer gate comparisons and exact finite candidate nondomination from the admitted evidence facts; passing tests do not become a universal semantics theorem. There is no claim that this three-plan catalogue exhausts all possible schedules or behavior. The tested counterfactual supports a matched observed comparison, not a universal causal claim about reversal.

Source pins and selected files are the same as the prior four-repository pilot and are recorded in `qualification-results/ablation.json`. They are test subsets, not entire codebases. Foreign tracked source files remain unchanged. Local logical workers share a host; this is not remote cross-venue hardware. Test-body/source rewriting is not performed. Reproducible seed, recorded policy revisions, exact source commits, dependency lock, commands, outcomes and timing receipts are retained. Build isolation and host load are not hermetic.

## Reproduction

In a fresh unpacked directory: `bash reproduce.sh` fetches pinned source commits and installs dependencies; `bash reproduce_qualification.sh` reruns this experiment and qualification. Network is needed for setup. Existing evidence can be checked offline using `sha256sum -c QUALIFICATION-SHA256SUMS` and `python3 qualify_receipt.py`. Fresh runs overwrite result files; preserve the supplied receipts before rerunning.
