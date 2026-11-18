# Native identity and topology validation

This independent receipt binds observations to Idol commit `ef3dbcfa847579df2c839bb73240242fe5ebdd4e` and tree `fffa952f1042e559441ef8cf252b847c3a3e7f02`. It is evidence for a specific source snapshot and execution route, not a full Idol build or pre-commit admission.

## Result

| Case | Compile | Link | Native execution | Assertions | Verdict |
| --- | --- | --- | --- | --- | --- |
| Topology | 0 | 0 | 0 | 13 PASS, 0 FAIL, `failures=0` | Passed the entire declared 13-assertion battery |
| Identity candidate | 1 | Not reached | Not reached | 0 of 58 reached | Native source realization refused |
| Identity baseline ablation | 1 | Not reached | Not reached | 0 of 58 reached | Sensitivity not established |
| Effects, graph, policy, policycone controls | Not run | Not run | Not run | Not observed | Skipped to preserve the receipt and cleanup deadline |

The topology battery exercised grounded conjunctions, unsupported cycles, partitioned evidence, replay, unknown/counterfactual roots, refusal to publish hypothetical support, independent alternatives, withdrawal, and preservation of historical proof/subject information. These 13 named assertions ran as an AArch64 Linux executable directly on an AArch64 host. The complete output is in `logs/topology-native.log`.

The identity candidate could not realize its reached `lib/compiler/effect.id` partition. The standalone owner diagnostic identifies `DNB001`, application 336, relation `get`, missing `expression-not-lowered:sequence`, consumer `native realization`, producer `dnir lower`, at `lowerExprCons()` in `graph/lower.zig:41561`. Its compile exited 1 in 3.77 s. The same test under the old two-owner source ablation also refused, ultimately with `RegisterExhausted`. Neither refusal is an assertion failure, an assertion pass, or a valid baseline sensitivity result. Both unresolved obligations remain explicit.

## Source and ablation boundary

All 2,805 selected source files were checked against Git blob identities before the archive was assembled. The source archive SHA256 is `1b831a99c5307f7d01226ed5638c09e0d5f53ea52689787d07e9c9bf946478c9`. After execution, all 2,805 files remained byte-identical to that archive. `source.json` carries the commit/tree, critical owner hashes, and baseline provenance.

The ablation uses baseline commit `fcb056649dd63dcd58dec32602917ebfcbf44bc9`, mechanically identified by the original identity work. Only `lib/compiler/effect.id` and `lib/compiler/graph.id` contents were replaced in an isolated source copy. Candidate and ablation used the same test bytes and the same seed compiler artifact. The test SHA256 is `7a9f5fed605a3a8906d337d41b279ebaea245508710802a8daf04848705123b9`. No test or production source was edited.

## Native execution route

The host is AArch64 Linux with glibc 2.41. The pinned x86 Zig `0.17.0-dev.1567+f0354179a` compiler ran under QEMU to build the AArch64 host compiler and two Zig-authored runtime objects. The Idol compiler, its direct-backend runtime generation, and the topology test executable ran directly on ARM, without QEMU around their execution.

The seed compiler SHA256 is `1ff13d9e4ab85b53944bcd063030972520f199f534cb876f9ba0bc54d409b244` (74,770,288 bytes, ELF machine 183). Its successful host build used `-ODebug -fstrip`, explicit installed ARM libc paths, and `-fno-lld`. The checked-in lexer/parser/case C bridge sources were built with native GCC and the flags declared in `build.zig`; test code was emitted by Idol's direct backend. The seed retains the build graph's empty embedded runtime and x86 projection placeholders, so this receipt does not claim a normal final host build.

To avoid rebuilding the entire host merely to embed runtime bytes, the harness used the source-defined executable-object handoff: `compile --no-cache --backend=direct --target native-exe --emit obj`. In this source version, the explicit legacy target retains the executable entry/graph path and `directLinkLine` closes over reached homes before the object output branch bypasses final linking. A fresh absolute `TMPDIR` isolated each case. The harness selected the actual bootstrap units requested by that invocation, replaced only their empty seed placeholders with the exact freshly generated runtime objects, and linked the emitted entry/home objects with the repository's AArch64 GNU ld recipe. It supplied the repository's startup object first and preserved the source libc/GCC tail. No zero-byte placeholder was linked and no missing source partition was invented. Exact argv, selected inputs, and object/executable hashes are in `run.json` and `attempts.json`.

## Preparatory failures and scope

The first host build failed because cross-target libc generation attempted to self-execute x86 child tools on ARM (`InvalidExe`). The explicit-system-libc retry reached LLVM emission but was terminated at the effective 900 s bound after a documented 600→900 s supervision extension. A contemplated 1,200 s extension did not take effect because the 900 s bound had already fired. The stripped-debug retry succeeded in 705.48 s. Its initial I/O runtime-object attempt hit the same x86 LLD self-exec restriction; adding `-fno-lld` to the runtime-object commands resolved it. Every actual command exit and raw diagnostic is retained.

The initial unsuccessful preparation was a solitary sequential build in the new sandbox. Subsequent heavy work used that sandbox's official `idol-lock` wrapper; its final observed state was FREE. The occupied shared local build lock was untouched. The native fixture refusals are distinct from these host-build/toolchain failures.

This receipt establishes only the named topology battery through this native route. It does not establish native identity assertions, baseline sensitivity, a complete producer migration to derivation-stable identities, a full standard-build gate, or global Pareto optimality. Formal sibling-repository proofs and their landing are separate evidence.

## Files

`run.json` contains per-case outcomes and native artifact provenance. `source.json` binds source and baseline owners. `ablation.json` records the controlled source substitution and unresolved outcome. `attempts.json` includes every bootstrap/runtime/case command and inner exit. `raw.json` preserves 120 exact remote text files, each with byte length and SHA256. `harness/` and `logs/` provide the main executable recipes and focused diagnostics in directly readable form. `resources.json` records the task-scoped provider resource and measured cost; final deletion is recorded in `cleanup.json`: the provider confirmed deletion and the subsequent status request returned 404, Box has been deleted. A private provider snapshot retained the verified seed checkpoint; that snapshot was deliberately kept. An attempted seed download through a protected external preview endpoint was rejected by automatic approval review as an unauthorized export. The preview was removed and the export route was not retried. `manifest.json` binds the published bundle files.
