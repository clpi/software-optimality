#!/usr/bin/env python3
"""Replay deliberate refusal controls against ScopedFrontier and check.sh."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

parser = argparse.ArgumentParser()
parser.add_argument("--lean", required=True)
args = parser.parse_args()
root = Path(__file__).resolve().parents[2]
out = Path(__file__).resolve().parent
lean = Path(args.lean).resolve()
def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

false_claims = {
    "wrong-unit": "admitted fixtureContract (fixtureSubject 4) (milliseconds (fixtureSubject 4)) = true",
    "missing-capability": "admitted fixtureContract (fixtureSubject 0) (omittedMetric (fixtureSubject 0) 12) = true",
    "raised-cap": "admitted fixtureContract (fixtureSubject 0) (raisedCap (fixtureSubject 0)) = true",
    "foreign-venue": "admitted fixtureContract (fixtureSubject 0) (changedScope (fixtureSubject 0) (fun s => {s with venue := 2})) = true",
    "mixed-subject": "admitted fixtureContract (fixtureSubject 0) (mixedSubject (fixtureSubject 0)) = true",
    "tradeoff-replacement": "noRegression fixtureContract (fixtureSubject 0) (fixtureSubject 1) fixture = true",
}
records = []
with tempfile.TemporaryDirectory(prefix="scoped-frontier-negative-") as tmp:
    work = Path(tmp)
    env = dict(os.environ, LEAN_PATH=str(root))
    for name, claim in false_claims.items():
        code = "import ScopedFrontier\nopen ScopedFrontier\nexample : " + claim + " := by decide\n"
        path = work / (name + ".lean")
        path.write_text(code)
        result = subprocess.run([str(lean), "-DwarningAsError=true", str(path)],
                                cwd=root, env=env, capture_output=True, text=True)
        output = result.stdout + result.stderr
        (out / ("NEGATIVE-" + name + ".log")).write_text(output)
        ok = result.returncode != 0 and "tactic 'decide' proved that the proposition" in output and "is false" in output
        records.append({"name": name, "expected": "proof of false claim rejected",
                        "exit": result.returncode, "passed": ok,
                        "source": code, "source_sha256": sha(path),
                        "output_sha256": sha(out / ("NEGATIVE-" + name + ".log"))})
    for name in ["admission", "compiler-error"]:
        case = work / name
        case.mkdir()
        for p in root.glob("*.lean"):
            shutil.copy2(p, case / p.name)
        shutil.copy2(root / "check.sh", case / "check.sh")
        if name == "admission":
            (case / "Admission.lean").write_text("example : False := by sorry\n")
        else:
            p = case / "Qualification.lean"
            p.write_text(p.read_text() + "\ndef injectedTypeError : Nat := true\n")
        result = subprocess.run(["sh", "check.sh"], cwd=case,
            env=dict(os.environ, LEAN=str(lean), LEAN_PATH=""),
            capture_output=True, text=True)
        output = result.stdout + result.stderr
        (out / ("NEGATIVE-" + name + ".log")).write_text(output)
        reason = "Rejected prohibited proof escape hatch" if name == "admission" else "type mismatch"
        ok = result.returncode != 0 and reason in output
        records.append({"name": name, "expected": "check.sh rejects " + name,
                        "exit": result.returncode, "passed": ok,
                        "output_sha256": sha(out / ("NEGATIVE-" + name + ".log"))})
summary = {
    "status": "passed" if all(r["passed"] for r in records) else "failed",
    "controls": records,
    "lean_sha256": sha(lean),
    "module_sha256": sha(root / "ScopedFrontier.lean"),
    "checker_sha256": sha(root / "check.sh"),
    "replay_sha256": sha(Path(__file__).resolve()),
    "source_sha256": {p.name: sha(p) for p in sorted(root.glob("*.lean"))},
}
(out / "NEGATIVE-CONTROLS.json").write_text(json.dumps(summary, indent=2) + "\n")
print(json.dumps({"status": summary["status"], "count": len(records),
                  "controls": [(r["name"], r["exit"], r["passed"]) for r in records]}))
raise SystemExit(0 if summary["status"] == "passed" else 1)
