# Foreign-codebase evidence

Two independently checked, immutable pilot archives. Each contains receipts, raw logs, exact upstream commit references, checksums, checker and reproduction scripts. No upstream source tree, virtual environment or dependency binaries are included. Upstream license texts are preserved under third-party-notices/ (Click BSD, attrs and Tomli MIT, packaging Apache-2.0/BSD dual licensing). Scripts and docs are also browsable under experiments/.

| Archive | Scope |
| --- | --- |
| foreign-campaign-evidence.tar.gz | Four Python projects, selected eight test files, 36 job runs; 120-candidate cost model, four-member modeled frontier. Combined reversal+concurrency median wall-time reduction 19.06% across three rounds. |
| foreign-campaign-ablation-standalone.tar.gz | Same test subsets, controlled four-arm ablation, 64 jobs. Original-order concurrency lowered median wall time 16.61% vs sequential; reversal alone did not help (0.92% worse median), and reversal under concurrency was 9.65% worse. |

These are observed pilot results, not universal semantic independence or cross-hardware guarantees. No CPU, memory or general all-axis dominance claim is supported. Timing axes are not interchangeable with observed outcome preservation.

## Verify supplied evidence

Extract each archive into a separate fresh folder. Run its SHA256SUMS (or ABLATION-SHA256SUMS) check, then python3 verify_receipt.py or python3 verify_ablation.py. Reproduce scripts fetch exact upstream commits and dependencies and execute new tests. Reproduction downloads and runs third-party code; use a disposable environment. Never overwrite the supplied receipts with a new run. Copies under experiments/ omit large raw receipts: use the archives for offline verification.

The checksums below bind complete archives, not future runs. The newest hard-gate campaign is not part of these archives.
