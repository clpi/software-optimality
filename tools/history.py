#!/usr/bin/env python3
"""Local append-only history recorder and adapter for the Lean historyaudit checker."""

import argparse
import hashlib
import json
import sqlite3
import subprocess
import sys
import tempfile
import time
import uuid
from pathlib import Path


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def attribute(run, name, value):
    return {"question": {"run": run, "field": {"attribute": {"name": name}}}, "value": value}


def connect(path):
    db = sqlite3.connect(path, timeout=60)
    db.executescript("""
        CREATE TABLE IF NOT EXISTS events (
            seq INTEGER PRIMARY KEY, ref INTEGER NOT NULL, event TEXT NOT NULL);
        CREATE TABLE IF NOT EXISTS captures (
            digest TEXT PRIMARY KEY, packet TEXT NOT NULL, receipt TEXT NOT NULL);
        CREATE TRIGGER IF NOT EXISTS preserve_events BEFORE UPDATE ON events
            BEGIN SELECT RAISE(ABORT,'immutable event'); END;
        CREATE TRIGGER IF NOT EXISTS retain_events BEFORE DELETE ON events
            BEGIN SELECT RAISE(ABORT,'immutable event'); END;
        CREATE TRIGGER IF NOT EXISTS preserve_captures BEFORE UPDATE ON captures
            BEGIN SELECT RAISE(ABORT,'immutable capture'); END;
        CREATE TRIGGER IF NOT EXISTS retain_captures BEFORE DELETE ON captures
            BEGIN SELECT RAISE(ABORT,'immutable capture'); END;
    """)
    return db


def next_id(db):
    return db.execute("SELECT COALESCE(MAX(ref)+1,0) FROM events").fetchone()[0]


def put(db, event):
    if "put" in event:
        ref = event["put"]["row"]["id"]
    else:
        ref = event["withdraw"]["id"]
    db.execute("INSERT INTO events(ref,event) VALUES(?,?)", (ref, canonical(event)))


def emit(db, route, head, source, model="", parents=None, receipt=None):
    ref = next_id(db)
    row = dict(id=ref, bodyId=ref, appendedAt=time.time_ns(), source=source,
               model=model, route=route, parents=parents or [], head=head, receipt=receipt)
    put(db, {"put": {"row": row}})
    return row


def events(db):
    return [json.loads(r[0]) for r in db.execute("SELECT event FROM events ORDER BY seq")]


def save_capture(db, packet, route, raw=None):
    material = canonical(packet) if raw is None else raw.decode("utf-8")
    key = digest(material.encode())
    existing = db.execute("SELECT packet FROM captures WHERE digest=?", (key,)).fetchone()
    if existing:
        if existing[0] != material:
            raise ValueError("capture digest collision")
        return key
    if packet["capturedAt"] > time.time_ns():
        raise ValueError("capture time is later than ingestion")
    receipt = dict(atom=packet["atom"], capturedAt=packet["capturedAt"], source=packet["source"],
                   evidenceId=key, hook=packet["hook"])
    db.execute("INSERT INTO captures VALUES(?,?,?)", (key, material, canonical(receipt)))
    emit(db, route, receipt["atom"], receipt["source"], receipt=receipt)
    return key


def validate_packet(p):
    if not isinstance(p, dict) or type(p.get("capturedAt")) is not int or p["capturedAt"] < 0:
        raise ValueError("invalid capture time")
    if type(p.get("source")) is not str or not p["source"] or type(p.get("hook")) is not bool:
        raise ValueError("invalid capture provenance")
    a = p["atom"]
    q = a["question"]
    if not all(isinstance(q["run"].get(k), str) and q["run"][k]
               for k in ("system", "revision", "configuration", "occurrenceId")):
        raise ValueError("incomplete run identity")
    if q["field"] != "occurrence" and not (
            isinstance(q["field"], dict) and isinstance(q["field"].get("attribute", {}).get("name"), str)):
        raise ValueError("invalid capture field")
    if a["value"] is not None and (type(a["value"]) is not int or a["value"] < 0):
        raise ValueError("invalid capture value")
    if q["field"] == "occurrence" and a["value"] not in (0, 1):
        raise ValueError("invalid occurrence value")


def capture_plan(db, plan_id):
    rows = [json.loads(r[0]) for r in db.execute("SELECT event FROM events WHERE ref=?", (plan_id,))]
    if len(rows) != 1 or "put" not in rows[0] or rows[0]["put"]["row"]["route"] != "hookPlan":
        raise ValueError("missing, conflicted, or withdrawn hook plan")
    return rows[0]["put"]["row"]


def audit(db, args):
    spec = json.loads(Path(args.campaign).read_text())
    log = events(db)
    receipts = [json.loads(r[0]) for r in db.execute("SELECT receipt FROM captures ORDER BY digest")]
    # The owner of this local database is the authority for its events.
    bundle = dict(spec, ledger=log, authorized=log, verifiedReceipts=receipts, stamp=time.time_ns())
    executable = Path(args.checker).resolve()
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory) / "input.json"
        path.write_text(canonical(bundle))
        result = subprocess.run([str(executable), str(path)], check=True, capture_output=True, text=True)
    report = json.loads(result.stdout)
    for event in report["newEntries"]:
        if event["put"]["row"]["id"] < next_id(db):
            raise ValueError("checker produced a stale or out-of-order event ID")
        put(db, event)
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--db", required=True)
    sub = parser.add_subparsers(dest="action", required=True)
    arm = sub.add_parser("arm", help="record a future process-status equality hook")
    for field in ("system", "revision", "configuration", "model"):
        arm.add_argument("--" + field, required=True)
    arm.add_argument("--equals", type=int, required=True)
    run = sub.add_parser("run", help="invoke a child once under a named hook")
    run.add_argument("plan", type=int)
    run.add_argument("command", nargs=argparse.REMAINDER)
    archive = sub.add_parser("archive", help="backfill a capture packet under an independently supplied SHA-256")
    archive.add_argument("file")
    archive.add_argument("--sha256", required=True)
    suggest = sub.add_parser("suggest", help="record an independent predictor's proposed atom")
    suggest.add_argument("atom", help="path to an atom JSON file")
    suggest.add_argument("--source", required=True)
    suggest.add_argument("--model", required=True)
    drop = sub.add_parser("withdraw")
    drop.add_argument("id", type=int)
    check = sub.add_parser("audit", help="append derived rows and return the colored hypergraph and plan frontier")
    check.add_argument("campaign")
    check.add_argument("--checker", default=str(Path(__file__).resolve().parents[1] / ".lake/build/bin/historyaudit"))
    export = sub.add_parser("export", help="export the exact stored capture packet as its original UTF-8 bytes")
    export.add_argument("digest")
    args = parser.parse_args()
    db = connect(args.db)
    try:
        if args.action == "run":
            plan = capture_plan(db, args.plan)
            cmd = args.command[1:] if args.command[:1] == ["--"] else args.command
            if not cmd:
                raise ValueError("missing child command")
            # No DB lock while the external child executes. If the plan is
            # withdrawn meanwhile, the completed capture still records its origin.
            run_id = dict(plan["head"]["question"]["run"], occurrenceId=str(uuid.uuid4()))
            completed = subprocess.run(cmd, stdout=sys.stderr, stderr=sys.stderr, check=False)
            code = completed.returncode if completed.returncode >= 0 else 256 - completed.returncode
            fact = attribute(run_id, "process.status", code)
            packet = dict(atom=fact, capturedAt=time.time_ns(), source=f"hook:{args.plan}",
                          hook=True, command=cmd, returncode=completed.returncode)
            db.execute("BEGIN IMMEDIATE")
            key = save_capture(db, packet, "hookSample")
            field = plan["head"]["question"]["field"]["attribute"]["name"]
            expected = int(field.removeprefix("status.eq."))
            symbolic = attribute(run_id, field, int(code == expected))
            emit(db, "symbolic", symbolic, f"hook:{args.plan}", plan["model"], [fact])
            output = dict(run=run_id, captureSha256=key, childReturncode=completed.returncode)
        else:
            db.execute("BEGIN IMMEDIATE")
            if args.action == "arm":
                if args.equals < 0:
                    raise ValueError("expected status must be nonnegative")
                target = dict(system=args.system, revision=args.revision, configuration=args.configuration,
                              occurrenceId="future:" + str(uuid.uuid4()))
                row = emit(db, "hookPlan", attribute(target, f"status.eq.{args.equals}", 1),
                           "local-hook-planner", args.model)
                output = dict(plan=row["id"])
            elif args.action == "archive":
                raw = Path(args.file).read_bytes()
                if digest(raw) != args.sha256.lower():
                    raise ValueError("archive digest mismatch")
                packet = json.loads(raw)
                validate_packet(packet)
                output = dict(captureSha256=save_capture(db, packet, "backfill", raw))
            elif args.action == "suggest":
                head = json.loads(Path(args.atom).read_text())
                validate_packet(dict(atom=head, capturedAt=0, source=args.source, hook=False))
                output = emit(db, "independentPrediction", head, args.source, args.model)
            elif args.action == "withdraw":
                if args.id < 0:
                    raise ValueError("negative ledger ID")
                put(db, {"withdraw": {"id": args.id}})
                output = dict(withdrawn=args.id)
            elif args.action == "export":
                result = db.execute("SELECT packet FROM captures WHERE digest=?", (args.digest,)).fetchone()
                if result is None:
                    raise ValueError("unknown capture")
                db.commit()
                sys.stdout.buffer.write(result[0].encode("utf-8"))
                return
            else:
                output = audit(db, args)
        db.commit()
        print(canonical(output))
    finally:
        db.close()


if __name__ == "__main__":
    main()
