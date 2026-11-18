#!/usr/bin/env python3
"""Replay the fixed-law proof and exactly four checked semantic mutations.

Use LAKE and LEAN to select executables, or let Lake/PATH select the pinned
toolchain. Output defaults to a fresh temporary directory so historical logs
remain unchanged. An explicit --output directory must not contain replay logs.
"""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import os
import re
import subprocess
import tempfile
import time


HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
SOURCE = REPO / "composition/IdentityRepresentation.lean"
DEPENDENCY = "d88acbdc3ba78fff994067d2c73bcc01622b3f61"
MUTATIONS = [
    (
        "NEGATIVE-DROP-ORIGIN",
        "def Expanded.Binding.erase (x : Expanded.Binding) : IdentityRepresentation.Binding := ⟨x.origin⟩",
        "def Expanded.Binding.erase (_x : Expanded.Binding) : IdentityRepresentation.Binding := ⟨⟨[], []⟩⟩",
        "tactic 'rfl' failed",
    ),
    (
        "NEGATIVE-DROP-SELECTED-VALUE",
        "  ⟨x.binding.erase, x.value.erase⟩",
        "  ⟨x.binding.erase, ⟨⟨0, by decide⟩⟩⟩",
        "payload := ⟨0,",
    ),
    (
        "NEGATIVE-DROP-CHANGED-LAW",
        "  | literalBindingV1\n",
        "  | literalBindingV1\n  | changedRule\n",
        "case mk.changedRule",
    ),
    (
        "NEGATIVE-KEEP-DOMINATED",
        "def retained : List Candidate := [.compact]",
        "def retained : List Candidate := [.expanded]",
        "fixtureCertificate = true\nis false",
    ),
]


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def intended_proof_failure(code, text, path, marker):
    """Do not count syntax, import, version, executable or process failures."""
    if code != 1 or marker not in text:
        return False
    errors = re.findall(r"^(.+?):\d+:\d+: error: (.*)$", text, re.MULTILINE)
    if not errors:
        return False
    for filename, diagnostic in errors:
        if (REPO / filename).resolve() != path.resolve():
            return False
        if not diagnostic.startswith((
            "tactic 'rfl' failed", "tactic 'decide' proved", "unsolved goals"
        )):
            return False
    return not any(problem in text for problem in (
        "unknown module", "unknown identifier", "invalid import", "object file",
        "No such file", "invalid constructor", "error: failed to"
    ))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="fresh output directory")
    args = parser.parse_args()
    out = (args.output or Path(tempfile.mkdtemp(prefix="identity-replay-"))).resolve()
    out.mkdir(parents=True, exist_ok=True)
    if any(out.iterdir()):
        raise SystemExit(f"Refusing to overwrite existing replay artifacts: {out}")
    lake = os.environ.get("LAKE", "lake")
    lean = os.environ.get("LEAN", "lean")
    source = SOURCE.read_text()
    if re.search(r"\b(sorry|admit|axiom|native_decide)\b", source):
        raise SystemExit("Refusing proof escape token in the accepted source")
    receipt = json.loads((HERE / "RECEIPT.json").read_text())
    recorded = next(row["sha256"] for row in receipt["owned_files"]
                    if row["path"] == "composition/IdentityRepresentation.lean")
    if sha256(SOURCE) != recorded:
        raise SystemExit("Accepted source differs from the recorded proof source")
    for name, original, replacement, _ in MUTATIONS:
        if source.count(original) != 1:
            raise SystemExit(f"Mutation target is not unique: {name}")
        if (HERE / (name + ".lean")).read_text() != source.replace(original, replacement):
            raise SystemExit(f"Stored negative source is not the exact mutation: {name}")
    if (REPO / "lean-toolchain").read_text().strip() != "leanprover/lean4:v4.19.0":
        raise SystemExit("This receipt requires the pinned Lean 4.19.0 toolchain")
    lock = json.loads((REPO / "lake-manifest.json").read_text())
    if not any(package.get("rev") == DEPENDENCY and
               "software-is-quantifiable" in package.get("name", "")
               for package in lock["packages"]):
        raise SystemExit("The public dependency revision does not match this receipt")

    runs = []

    def execute(name, command, path=None, marker=None, expected_text=None):
        started = datetime.datetime.now(datetime.timezone.utc).isoformat()
        clock = time.monotonic()
        try:
            process = subprocess.run(command, cwd=REPO, text=True,
                                     stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            code, text = process.returncode, process.stdout
        except OSError as error:
            code, text = None, f"Tool execution failed: {error}\n"
        (out / (name + ".log")).write_text(text)
        if marker is not None:
            accepted = intended_proof_failure(code, text, path, marker)
            category = "expected_proof_rejection" if accepted else "unexpected_failure"
        else:
            accepted = code == 0 and not any(
                token in text for token in ("sorryAx", "error:", "warning:")
            ) and (expected_text is None or expected_text in text)
            category = "passed" if accepted else "tool_or_proof_failure"
        run = {
            "name": name, "command": command, "cwd": str(REPO),
            "start_utc": started,
            "end_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
            "elapsed_seconds": time.monotonic() - clock, "exit_code": code,
            "expected_failure": marker is not None,
            "expected_diagnostic_marker": marker,
            "expected_outcome_observed": accepted, "classification": category,
            "source_sha256": sha256(path) if path is not None else None,
            "log": name + ".log", "log_sha256": sha256(out / (name + ".log")),
        }
        runs.append(run)
        print(f"{name}: {category} (exit {code})", flush=True)
        (out / "REPLAY.json").write_text(json.dumps({
            "script_sha256": sha256(Path(__file__)),
            "source_sha256": sha256(SOURCE),
            "dependency_commit": DEPENDENCY,
            "runs": runs,
            "all_expected_outcomes": all(row["expected_outcome_observed"] for row in runs),
        }, indent=2) + "\n")
        return accepted

    if not execute("TOOLCHAIN", [lake, "env", lean, "--version"],
                   expected_text="version 4.19.0"):
        raise SystemExit(2)
    if not execute("BUILD", [lake, "build", "composition.IdentityRepresentation"]):
        raise SystemExit(2)
    dependency = REPO / ".lake/packages/software-is-quantifiable"
    if not execute("DEPENDENCY", ["git", "-C", str(dependency), "rev-parse", "HEAD"],
                   expected_text=DEPENDENCY):
        raise SystemExit(2)
    if not execute("DEPENDENCY-CLEAN", ["git", "-C", str(dependency), "diff", "HEAD", "--exit-code"]):
        raise SystemExit(2)
    if not execute("KERNEL", [lake, "env", lean, "-DwarningAsError=true",
                              str(SOURCE.relative_to(REPO))], path=SOURCE):
        raise SystemExit(1)
    for name, _, _, marker in MUTATIONS:
        path = HERE / (name + ".lean")
        execute(name, [lake, "env", lean, "-DwarningAsError=true",
                       str(path.relative_to(REPO))], path=path, marker=marker)
    print(f"Replay artifacts: {out}")
    raise SystemExit(0 if all(row["expected_outcome_observed"] for row in runs) else 1)


if __name__ == "__main__":
    main()
