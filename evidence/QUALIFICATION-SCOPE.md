# Reviewed qualification pilot

Archive: foreign-campaign-qualification.tar.gz; SHA256 5f2e3f1ce568e59e2bf1dbdc8703113f22bbef7c5358f14552917504f421075e.

Four pinned foreign Python projects, selected test inputs, three paired rounds, 36 subprocess jobs. Exact raw receipt hashes and recorded behavior checks passed independent review. O2 is the singleton frontier among O1/O2/R2 under the sole maximum-observed whole-suite-wall-time objective, after per-round baseline-relative suite-time eligibility. Worker capacity is a constraint, not a cost axis. R2 was actually run and admitted but dominated; only a separate synthetic +1ns counterexample was rejected.

Gate scope is whole-suite timing: 8 of 12 O2 subprocess times were individually slower than O1. This is not no-regression evidence for every job/test or CPU/memory, nor a promise about future runs or all semantics. Source revisions and policy digests are recorded; policy revision chronology has no signed precommit or independent timestamp authentication. The objective was revised during execution according to the retained experiment record.

Extract the archive into a fresh directory, verify QUALIFICATION-SHA256SUMS and run python3 qualify_receipt.py for receipt checks. Reproduction fetches pinned public source and executes it: use a disposable environment. Upstream license notices are included. Do not overwrite original evidence.
