#!/usr/bin/env python3
"""Replay proofs, check archived imports, and require false claims to fail."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tarfile
import tempfile

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "docs/covered-frontier"
BASE = "97a5d7f3e68de47cd9eb26221b83e713121673fd"
ARCHIVE_BLOB = "d74b58fe93dd9454a1feae8aff6035d8872c6b99"
QUALIFICATION = "037ce2972cbf5bb72de79e24e3c914b4254406a488696a5e4e9f7b00eff50b73"
POLICY = "44faa39b813fe8ff0571957fa2f535d2d6d022ebd765cf8c0d95296ef5d40416"


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def imported_source():
    archive = ROOT / "evidence/foreign-campaign-qualification.tar.gz"
    raw = archive.read_bytes()
    blob = hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()
    if blob != ARCHIVE_BLOB:
        raise RuntimeError("archived campaign is not the pinned upstream blob")
    with tarfile.open(archive, "r:gz") as tar:
        def read(name, expected):
            rows = [m for m in tar.getmembers() if m.isfile() and m.name.endswith("/" + name)]
            if len(rows) != 1:
                raise RuntimeError("ambiguous archived input: " + name)
            data = tar.extractfile(rows[0]).read()
            if sha(data) != expected:
                raise RuntimeError("archived input hash mismatch: " + name)
            return json.loads(data)
        report = read("qualification.json", QUALIFICATION)
        policy = read("policy.json", POLICY)
    if report["policy_sha256"] != POLICY or policy["candidate_ids"] != ["O1", "O2", "R2"]:
        raise RuntimeError("campaign policy identity/candidate domain mismatch")
    if policy["axes"] != [{"name": "max_observed_elapsed_ns", "direction": "min"}]:
        raise RuntimeError("archived objective changed")
    if [r["id"] for r in report["candidates"]] != policy["candidate_ids"]:
        raise RuntimeError("archived candidate enumeration changed")
    source = ["import EligibleCampaign", "import Std", "open EligibleCampaign",
              "-- Generated from the pinned archived report; review.py verifies every byte.",
              "-- qualification.json SHA256: " + QUALIFICATION,
              "-- policy.json SHA256: " + POLICY]
    def boolean(value):
        if not isinstance(value, bool):
            raise RuntimeError("non-Boolean archived observation")
        return str(value).lower()
    for row in report["candidates"]:
        name = row["id"]
        times = row["times_ns"]
        checks = row["checks"]
        if len(times) != policy["rounds"] or len(checks) != policy["rounds"]:
            raise RuntimeError("archived round count mismatch")
        if row["metrics"] != [max(times)]:
            raise RuntimeError("archived objective does not match its aggregation")
        flags = []
        for index, check in enumerate(checks):
            if check["round"] != index or check["elapsed_ns"] != times[index]:
                raise RuntimeError("archived round or elapsed value mismatch")
            flags.append("[" + ", ".join(
                "(" + ", ".join(boolean(job[key]) for key in
                    ["same_ids", "same_phase_outcomes_skips", "exit_zero"]) + ")"
                for job in check["jobs"]) + "]")
        source.extend([
            f"example : times .{name} = {times} := by decide",
            f"example : caps = {row['caps_ns']} := by decide",
            f"example : receiptFlags .{name} = [{', '.join(flags)}] := by decide",
            f"example : workers .{name} = {row['worker_allocation']} := by decide",
            f"example : gate .{name} = {boolean(row['admitted'])} := by decide",
            f"example : cost .{name} 0 = {row['metrics'][0]} := by decide",
        ])
    return "\n".join(source) + "\n", {"archive_git_blob": blob, "archive_sha256": sha(raw),
        "qualification_sha256": QUALIFICATION, "policy_sha256": POLICY,
        "source_commit": BASE, "fresh_measurements": False,
        "objective": policy["axes"], "units": "nanoseconds as declared by elapsed_ns and policy",
        "baseline": policy["baseline"], "candidate_ids": policy["candidate_ids"],
        "rounds": policy["rounds"], "hard_constraints": policy["hard_constraints"],
        "recorded_candidates": [{key: row[key] for key in
            ["id", "admitted", "times_ns", "caps_ns", "metrics", "worker_allocation"]}
            for row in report["candidates"]], "scope": policy["scope"]}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--lean", default=os.environ.get("LEAN", "lean"))
    parser.add_argument("--write-import", action="store_true")
    args = parser.parse_args()
    source, archived = imported_source()
    imported = OUT / "ArchiveImport.lean"
    if args.write_import:
        imported.write_text(source)
        return
    if imported.read_text() != source:
        raise RuntimeError("ArchiveImport.lean differs from the pinned archive projection")
    env = dict(os.environ, LEAN=args.lean, LEAN_PATH=str(ROOT))
    version = subprocess.run([args.lean, "--version"], env=env, text=True,
        capture_output=True, check=True).stdout.strip()
    if "version 4.19.0," not in version:
        raise RuntimeError("unexpected Lean toolchain: " + version)
    records = []
    def run(label, command, expected_success, cwd=ROOT, marker=None):
        result = subprocess.run(command, cwd=cwd, env=env, text=True, capture_output=True)
        output = result.stdout + result.stderr
        log = OUT / (label + ".log")
        log.write_text(output)
        if expected_success:
            good = result.returncode == 0 and not any(x in output for x in ["error:", "warning:", "sorryAx"])
        else:
            good = result.returncode != 0 and (marker is None or marker in output)
        records.append({"name": label, "command": command, "exit_code": result.returncode,
            "expected_success": expected_success, "accepted": good, "log_sha256": sha(log.read_bytes())})
        if not good:
            raise RuntimeError(label + " did not satisfy its expected result; see " + str(log))
    run("PUBLISHER-CHECK", ["sh", "check.sh"], True)
    prefix = "import ScopedFrontier\nopen ScopedFrontier\n"
    cases = {
        "missing-generator": "example : checkCoverage fixtureContract ([0,1,2,3].map fixtureSubject) ([0,1].map fixtureSubject) fixture = true := by decide\n",
        "discarded-tie": "example : checkCoverage fixtureContract ([2,3].map fixtureSubject) [fixtureSubject 2] fixture = true := by decide\n",
        "empty-axes": "example : certifyCovered {fixtureContract with axes := []} [] [] [] fixture = true := by decide\n",
        "empty-replacement": "example : certifyReplacement fixtureContract [] [] [] fixture (fixtureSubject 0) (fixtureSubject 2) = true := by decide\n",
        "tradeoff-replacement": "example : certifyReplacement fixtureContract ([0,1].map fixtureSubject) ([0,1].map fixtureSubject) ([0,1].map fixtureSubject) fixture (fixtureSubject 0) (fixtureSubject 1) = true := by decide\n",
        "unknown-feasible-cost": "def missing (s : Subject) : Input := if s.artifact = 2 then omittedMetric s 11 else fixture s\nexample : certifyFeasible fixtureContract ([0,2].map fixtureSubject) ([0,2].map fixtureSubject) [fixtureSubject 0] (fun _ => true) missing = true := by decide\n",
        "joint-premise": "def project (facts : Nat → Bool) (s : Subject) : Input := if s.artifact = 2 && !facts 2 then failedCapability s else fixture s\nexample : certifyClosed [0,1,2] [0] [([0,1],2)] fixtureContract ([0,2].map fixtureSubject) ([0,2].map fixtureSubject) [fixtureSubject 2] project = some true := by decide\n",
    }
    with tempfile.TemporaryDirectory(prefix="covered-frontier-") as temp:
        scratch = Path(temp)
        for label, body in cases.items():
            path = scratch / "FalseClaim.lean"
            path.write_text(prefix + body)
            run("NEGATIVE-" + label, [args.lean, "-DwarningAsError=true", str(path)],
                False, marker="proved that the proposition")
        for file in ROOT.glob("*.lean"):
            shutil.copyfile(file, scratch / file.name)
        shutil.copyfile(ROOT / "check.sh", scratch / "check.sh")
        target = scratch / "FiniteQualification.lean"
        original = target.read_text()
        target.write_text(original + "\nexample : False := by sorry\n")
        run("NEGATIVE-admission", ["sh", "check.sh"], False, cwd=scratch,
            marker="Rejected prohibited proof escape hatch")
        target.write_text(original + "\nexample : Nat := \"deliberate compiler error\"\n")
        run("NEGATIVE-compiler-error", ["sh", "check.sh"], False, cwd=scratch, marker="error:")
    tracked = ["ScopedFrontier.lean", "check.sh", "composition/check.sh", "docs/SCOPED-FRONTIER.md",
        "docs/covered-frontier/Controls.lean", "docs/covered-frontier/Campaign.lean",
        "docs/covered-frontier/ArchiveImport.lean", "docs/covered-frontier/review.py"]
    receipt = {"base_commit": BASE, "toolchain": version,
        "sources": {p: sha((ROOT / p).read_bytes()) for p in tracked},
        "archived_campaign": archived, "checks": records,
        "scope": "Parameterized checked theorem and finite imported-data certificates; no whole-Idol or physical global optimality claim."}
    (OUT / "CHECK-RECEIPT.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print("All proof checks, archive import checks, and deliberate rejection controls passed.")


if __name__ == "__main__":
    main()
