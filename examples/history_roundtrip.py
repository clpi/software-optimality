"""Run two real child processes and check historical recovery from their captures."""

import argparse
import hashlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
RECORDER = ROOT / "tools/history.py"


def atom(run, field, value):
    return {"question": {"run": run, "field": "occurrence" if field is None else {"attribute": {"name": field}}},
            "value": value}


def run_demo(directory, save=None):
    def command(db, *args):
        return [sys.executable, str(RECORDER), "--db", str(directory / db), *map(str, args)]

    def call(db, *args):
        return json.loads(subprocess.check_output(command(db, *args), text=True))

    def launch(db):
        plan = call(db, "arm", "--system", "build", "--revision", "r1", "--configuration", "demo",
                    "--model", "exit-schema-1", "--equals", 7)["plan"]
        return call(db, "run", plan, "--", sys.executable, "-c", "raise SystemExit(7)")

    original = launch("old.db")
    newer = launch("current.db")
    old, new = original["run"], newer["run"]
    assert old != new and original["childReturncode"] == newer["childReturncode"] == 7
    capture = subprocess.check_output(command("old.db", "export", original["captureSha256"]))
    assert hashlib.sha256(capture).hexdigest() == original["captureSha256"]
    packet = directory / "archive.json"
    packet.write_bytes(capture)

    # This separate process sees only the prior model; it guesses wrongly.
    predicted = directory / "proposal.json"
    predictor = "import json,sys; print(json.dumps(dict(question=json.loads(sys.argv[1]),value=9)))"
    predicted.write_bytes(subprocess.check_output([sys.executable,"-c",predictor,
        json.dumps(atom(old, "process.status", 0)["question"])]))
    call("current.db", "suggest", predicted, "--source", "independent-prior-program", "--model", "prior-1")

    def facts(run, status):
        return [atom(run, None, int(status is not None)), atom(run, "process.status", status),
                atom(run, "status.eq.7", None if status is None else int(status == 7))]

    queries = [a["question"] for a in facts(old, 7)]
    worlds = [dict(name=name, weight=weight, assignments=facts(old, status) + facts(new, 7))
              for name, weight, status in [("absent",1,None),("exit-seven",2,7),("exit-nine",8,9)]]
    sensors = [dict(name="retained-start-index", availability="retainedRead",
                    question=queries[0], equalsValue=1, cost=1),
               dict(name="retained-status-index", availability="retainedRead",
                    question=queries[1], equalsValue=7, cost=1)]
    cfg = dict(model="exit-schema-1", prior="prior-1", roster=[new], questions=queries, worlds=worlds,
               planning=dict(sensors=sensors, depth=2, maxPlans=19, maxWorstCost=2, requireAll=True))
    model_file = directory / "campaign.json"
    model_file.write_text(json.dumps(cfg))
    before = call("current.db", "audit", model_file)
    assert old in before["namedRuns"] and old not in cfg["roster"]
    assert [q["diagnosis"]["status"] for q in before["queries"]] == ["ambiguous"] * 3
    assert before["queries"][1]["minimumLossGuesses"] == [9]
    assert before["planning"]["candidateCount"] == 19 and before["planning"]["frontier"]
    assert all(x["resolvesAll"] for x in before["planning"]["frontier"])
    assert all(a["question"]["run"] != old for a in before["closure"])
    assert not call("current.db", "audit", model_file)["newEntries"]

    refused = subprocess.run(command("current.db", "archive", packet, "--sha256", "0"*64), capture_output=True)
    assert refused.returncode != 0
    # A foreign collector may use different whitespace. Preserve its exact bytes.
    formatted = directory / "formatted.json"
    formatted.write_bytes((json.dumps(json.loads(capture), indent=2) + "\n").encode())
    foreign_digest = hashlib.sha256(formatted.read_bytes()).hexdigest()
    assert call("format.db", "archive", formatted, "--sha256", foreign_digest)["captureSha256"] == foreign_digest
    assert subprocess.check_output(command("format.db", "export", foreign_digest)) == formatted.read_bytes()
    call("current.db","archive",packet,"--sha256",original["captureSha256"])
    # Concurrent writers serialize the snapshot, fresh IDs and proof publication.
    jobs = [subprocess.Popen(command("current.db","audit",model_file), stdout=subprocess.PIPE,
                             stderr=subprocess.PIPE,text=True) for _ in range(2)]
    reports = []
    for job in jobs:
        out, err = job.communicate(timeout=60)
        assert job.returncode == 0, err
        reports.append(json.loads(out))
    assert sorted(len(r["newEntries"]) for r in reports) == [0,2]
    after = call("current.db","audit",model_file)
    assert [q["diagnosis"]["value"] for q in after["queries"]] == [1,7,1]
    old_guess = next(edge for edge in after["hyperedges"] if edge["entry"]["source"] == "independent-prior-program")
    assert old_guess["channel"] == "advisory" and old_guess["closureColor"] == "opposed"
    assert not old_guess["validatedImplication"] and not old_guess["validatedMeasurement"]
    assert after["compatibleWorlds"] == ["exit-seven"]
    assert after["planning"]["frontier"] == [dict(tree="stop",worstCost=0,worstReads=0,resolvesAll=True)]
    receipt = next(e["entry"] for e in after["hyperedges"] if e["entry"]["route"] == "backfill")
    call("current.db","withdraw",receipt["id"])
    withdrawn = call("current.db","audit",model_file)
    assert withdrawn["compatibleWorlds"] == before["compatibleWorlds"]
    assert all(a["question"]["run"] != old for a in withdrawn["closure"])
    assert [e["event"] for e in withdrawn["ledger"][:len(after["ledger"])]] == [e["event"] for e in after["ledger"]]
    assert any(e["entry"]["route"] == "hookSample" and e["validatedMeasurement"] for e in withdrawn["hyperedges"])

    if save:
        future_packet = json.loads(subprocess.check_output(command("current.db","export",newer["captureSha256"])))
        evidence = dict(campaign=cfg, events=[item["event"] for item in withdrawn["ledger"]],
                        cuts=dict(before=len(before["ledger"]), after=len(after["ledger"]),
                                  withdrawn=len(withdrawn["ledger"])),
                        captures=[json.loads(capture),future_packet])
        save.write_text(json.dumps(evidence,indent=2)+"\n")
    cfg["planning"]["maxPlans"] = 18
    model_file.write_text(json.dumps(cfg))
    rejected = subprocess.run(command("current.db","audit",model_file),capture_output=True,text=True)
    assert rejected.returncode != 0
    return dict(originalExit=original["childReturncode"], futureExit=newer["childReturncode"],
                possibleBefore=before["compatibleWorlds"], guess=before["queries"][1]["minimumLossGuesses"],
                enumerated=before["planning"]["candidateCount"], optimalPlansBefore=len(before["planning"]["frontier"]),
                recovered=[q["diagnosis"]["value"] for q in after["queries"]], concurrentNewRows=[0,2],
                optimumAfter="stop", possibleAfterWithdrawal=withdrawn["compatibleWorlds"])


def replay(source):
    rec = json.loads(source.read_text())
    receipts = []
    for packet in rec["captures"]:
        raw = json.dumps(packet, sort_keys=True, separators=(",",":"), ensure_ascii=False).encode()
        receipts.append(dict(atom=packet["atom"], capturedAt=packet["capturedAt"], source=packet["source"],
                             evidenceId=hashlib.sha256(raw).hexdigest(), hook=packet["hook"]))
    outcomes = {}
    with tempfile.TemporaryDirectory() as work:
        bundle = Path(work) / "input.json"
        for name, stop in rec["cuts"].items():
            events = rec["events"][:stop]
            bundle.write_text(json.dumps(dict(rec["campaign"], stamp=0, ledger=events, authorized=events,
                                               verifiedReceipts=receipts)))
            out = json.loads(subprocess.check_output([ROOT/".lake/build/bin/historyaudit",bundle],text=True))
            assert not out["newEntries"]
            outcomes[name] = (out["compatibleWorlds"], [q["diagnosis"] for q in out["queries"]])
        # With zero receipts, a model invariant still yields an empty-premise
        # proof. An agreed value disappears when an alternative history is added.
        campaign = rec["campaign"]
        new_run = campaign["roster"][0]
        invariant = atom(new_run, "process.status", 7)["question"]
        zero = dict(campaign, ledger=[], authorized=[], verifiedReceipts=[], stamp=0, planning=None,
                    questions=[invariant, campaign["questions"][1]])
        def check_zero():
            bundle.write_text(json.dumps(zero))
            return json.loads(subprocess.check_output([ROOT/".lake/build/bin/historyaudit",bundle], text=True))
        first = check_zero()
        assert [q["diagnosis"]["status"] for q in first["queries"]] == ["entailed","ambiguous"]
        fixed = next(edge for edge in first["hyperedges"] if edge["entry"]["route"] == "symbolic")
        assert fixed["entry"]["parents"] == [] and fixed["rawEvidenceColor"] == "unknown"
        assert fixed["closureColor"] == "supported" and fixed["validatedImplication"]
        alt = dict(campaign["worlds"][0], name="alternative-future",
                   assignments=[dict(a, value=8) if a["question"] == invariant else
                                dict(a, value=0) if a["question"] == atom(new_run, "status.eq.7", 0)["question"] else a
                                for a in campaign["worlds"][0]["assignments"]])
        zero["worlds"] = [*zero["worlds"], alt]
        assert check_zero()["queries"][0]["diagnosis"]["status"] == "ambiguous"
    assert outcomes["before"] == outcomes["withdrawn"]
    assert outcomes["after"][0] == ["exit-seven"]
    assert [d["value"] for d in outcomes["after"][1]] == [1,7,1]
    print("Recorded history verified at all three ledger cuts. Zero-receipt invariant and countermodel verified.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    args = parser.add_mutually_exclusive_group()
    args.add_argument("--save", type=Path)
    args.add_argument("--replay", type=Path)
    options = parser.parse_args()
    if options.replay:
        replay(options.replay)
    else:
        with tempfile.TemporaryDirectory() as folder:
            print(json.dumps(run_demo(Path(folder), options.save),indent=2))
