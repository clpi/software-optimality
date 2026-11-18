# Fixed-law representation certificate

## Result

The Lean 4.19 kernel checked exact erasure and restoration of the repeated fixed
law fields in Idol's finite literal-binding record schema. The compact and
expanded typed records preserve exactly the same distinctions. The existing
public aligned-profile frontier certificate accepts the compact layout over the
expanded layout for the two supplied, executed byte-count fixtures.

This is a structural representation theorem and a two-fixture byte comparison.
It does not establish Zig-to-model conformance, a byte-codec proof, historical
origin authenticity, latency improvement, or optimality over all encodings.

## Reproduce

From the repository root, with the pinned Lean 4.19.0 toolchain available:

```sh
python3 composition/identity/replay.py
```

`LAKE` and `LEAN` may name alternative executable paths; otherwise the script
uses Lake and `PATH`. The script builds the proof's dependencies, checks the
pinned public dependency, kernel-checks the accepted module, and executes the
four exact stored negative sources. It validates their intended mathematical
diagnostics and refuses import, syntax, version and tool failures as evidence of
successful negative controls.

Each replay writes fresh logs to a temporary directory. `--output DIR` selects a
fresh output directory; an existing nonempty directory is refused. Historical
raw logs in this directory remain unchanged. The executed portable replay is
recorded in [replay/REPLAY.json](replay/REPLAY.json), alongside its raw logs. That
historical replay used the original `f3709926` dependency. The current script
pins `d88acbdc`; its fresh landing replay and verbatim output are retained in
the `landing_integration` block of [RECEIPT.json](RECEIPT.json).
An additional [tool-refusal control](tool-refusal/CONTROL.json) selected an
unavailable Lean executable. The harness refused before running any mathematical
control and did not count that tool failure as a successful proof rejection.

## Source binding

- Original checked formal baseline: `clpi/software-optimality`
  `ec1eadda0a29d1b254a98feb5ad24911a095c454`.
- Original checked public dependency: `clpi/software-is-quantifiable`
  `f370992611d8c722e4897e67dbb8eaecf3d872ed`; the checkout was clean and its
  revision matched the Lake lock and package declaration.
- New module: `composition/IdentityRepresentation.lean`, SHA-256
  `9996a284df731331863e336ef8e4eb83838598a61c762b359feb06528d9bd36d`.
- Integration: one import in `SoftwareOptimality.lean` and one root in
  `lakefile.lean`, preserving the current upstream historical and three-valued
  modules. Their exact before/after hashes are in `RECEIPT.json`.
- Measured Zig helper: `src/semantic_identity.zig`, SHA-256
  `d13c078e9e21e9e7b9fcbd6e67133fe0e2be75e14cc840adf67d87e0423e562a`.

The landing was rebased onto formal master
`e0d44612583031aa7545db0ad62678b1ade59404`, preserving its public dependency
`d88acbdc3ba78fff994067d2c73bcc01622b3f61` and executable incremental modules.
A fresh full **84-target Lake build**, kernel proof and all four exact negative
controls passed against that dependency. The proof module itself is unchanged.
The fresh source hashes, commands, exit codes and verbatim logs are included in
`RECEIPT.json` separately from the original receipts above.

[SOURCE-MANIFEST.json](SOURCE-MANIFEST.json) records the project's Lean source
hashes, the Lean and Lake executable hashes, and the clean public dependency
revision. The [proof source](../IdentityRepresentation.lean),
[root import](../../SoftwareOptimality.lean), and
[Lake target](../../lakefile.lean) are the integration files.

## Kernel statements

`erase_expand` and `expand_erase` prove both round trips for every typed record.
`erase_eq_iff` and `expand_eq_iff` consequently prove exact equality preservation
in both directions, including constructor roles. No hashing or fixture-limited
enumeration substitutes for these statements.

`all_record_observations_preserved` preserves every function of a complete
expanded record under erasure and restoration. The nominal binding, closed
definition, member and module theorems expose the individual dependencies:
binding origins, exact selected integers, observed member keys, and complete
member lists. The proof preserves list order and repetitions; the implementation's
canonical unordered-member admission remains separately checked.

`scoped_representation_certificate` combines reconstruction for every typed
record with the existing `InterfaceBridge.aligned_certificate_exact` result.
The public profile symbol contains the exact two typed fixture records. It does
not use a generic symbol that could silently describe another root or value.

The main theorems use only the standard `propext` and `Quot.sound` axioms.
The accepted source contains no custom axioms, admitted proofs or native-decision
shortcut. [KERNEL-PROOF.log](KERNEL-PROOF.log) records the kernel's dependency audit.

## Executed byte profiles

| Exact fixture axis | Expanded bytes | Compact bytes |
|---|---:|---:|
| Signed integer `-17` | 81 | 30 |
| Module origin `(domain, home)`, binding origin `(domain, a)`, member key `left`, selected integer `-17` | 436 | 231 |

The candidate domain contains both layouts. The certificate is therefore a
comparison against a concrete alternative, with scope limited to these two
declared axes. The expanded fixture bytes were constructed and counted by the
successful current helper test; this is not a timing comparison against a
previously deployed binary.

The independent native AArch64 helper artifact had SHA-256
`0ccb0e086746a18eceecb65a50546a96235c5ac2b4bb0a4ad9f91afdfcacca62`.
Its native execution returned zero and passed all nine helper tests. The raw
stderr log, containing both byte-count measurements, had SHA-256
`7a9b1f0131cecaabda29cb0e6f4c36f291313a64d0fddf706581b843e7614ce2`.
[RECEIPT.json](RECEIPT.json) binds those source, artifact, command and output
records. The [native source manifest](native-helper/sources.json),
[native attempts](native-helper/attempts.json), and
[raw native output](native-helper/native.stderr) preserve the original evidence.
The native code is cross-referenced by its exact helper source hash above and
the [identical published source](https://github.com/clpi/idol/blob/05f8cbe657bbaf4556a1fd778609b53704154c33/src/semantic_identity.zig)
at Idol commit `05f8cbe657bbaf4556a1fd778609b53704154c33`. The commit reference is
publication metadata and does not salt semantic identity.

## Actual Lean execution and negative controls

The exact toolchain was Lean 4.19.0, x86_64 Linux, commit `6caaee842e94`.
The original updated `lake build` completed all 79 targets, including the upstream
history executable and the existing tied-identity frontier controls. A separate
kernel invocation checked the new module with warnings treated as errors.

Four source mutations were executed independently and rejected:

| Mutation | Required failure observed |
|---|---|
| Replace retained binding origins with an empty origin | Binding round-trip proofs fail. |
| Replace every selected definition value with zero | Closed-definition round-trip proofs fail. |
| Add a second, changed semantic law while still erasing the law field | Restoration cannot recover the changed law. |
| Retain the expanded layout as the claimed frontier | The existing certificate evaluates to false. |

All four Lean processes exited nonzero with the relevant mathematical diagnostic.
These were proof rejections, not missing-import or toolchain failures. The replay
script, per-command exit codes, source hashes and raw logs are retained in this
directory. [KERNEL-AND-CONTROLS.json](KERNEL-AND-CONTROLS.json) is the historical
final control result; [LAKE-BUILD.json](LAKE-BUILD.json) and its
[raw log](LAKE-BUILD.log) record the full integration result. Absolute command
paths in these historical receipts are retained verbatim. New checkouts use the
portable [replay script](replay.py).

## Limits

The fixed rule basis is the single supported `idol/literal-binding/1` semantic
schema. Its removal is safe because restoration is exact within that domain;
the changed-law negative control demonstrates why the same erasure would be
unsound in a domain containing different rules.

The model includes all typed structural field values, so its bijection also
holds on any further admitted subset. It does not decide which source origins
are authentic, which byte strings are legal source names, or which module lists
pass the producer's duplicate and sorting checks. Those obligations remain at
their existing owners. Actual graph and CLI execution are separate production
validation results and are not inferred from this Lean certificate.
