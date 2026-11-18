# Checker failure controls

Run on a separate temporary copy, leaving the release sources unchanged.

1. Append `theorem forbidden_admission : False := by sorry` to `Qualification.lean`, then run `check.sh` with Lean 4.19.0. **Rejected with nonzero exit** by source escape-hatch guard, before proof compilation.
2. Restore `Qualification.lean`, append `#check intentionally_nonexistent_identifier`, then run `check.sh`. **Rejected with nonzero exit** on the compiler error; no later module or packaging command runs in the fail-fast flow.

Release validation and packaging use separate checked steps under `set -eu`:

```sh
set -eu
LEAN=/path/to/lean ./check.sh > CHECK.log 2>&1
if grep -Eq 'sorryAx|error:|warning:' CHECK.log; then exit 2; fi
sha256sum *.lean check.sh lean-toolchain CHECK.log README.md CHECK_CONTROLS.md > SHA256SUMS
```

The rejected intermediate v11 archive exposed a shell-status reporting flaw: its compiler failure was followed by a successful packaging command, masking the failure in the outer command status. It was never eligible for publication. v12 fixes the parenthesized Boolean theorem and strengthens the checker/package boundary. The release check must succeed independently; matching hashes alone never establishes proof success.
