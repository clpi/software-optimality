import ObservationPlanning

namespace HistoryAudit
open HistoricalEvidence Lean

structure World where
  name : String
  assignments : List Atom
  weight : Nat
  deriving Repr, DecidableEq, FromJson

inductive Availability where | retainedRead | futureHook | replayRead
  deriving Repr, DecidableEq, ToJson, FromJson

structure Sensor where
  name : String
  availability : Availability
  question : Question
  equalsValue : Option Nat
  cost : Nat
  deriving Repr, DecidableEq, ToJson, FromJson

structure Planning where
  sensors : List Sensor
  depth : Nat
  maxPlans : Nat
  maxWorstCost : Nat
  requireAll : Bool
  deriving FromJson

structure Bundle where
  model : String
  prior : String
  stamp : Nat
  worlds : List World
  roster : List Run
  questions : List Question
  ledger : List Event
  authorized : List Event
  verifiedReceipts : List Receipt
  planning : Option Planning := none
  deriving FromJson

private def lookup (w : World) (q : Question) :=
  (w.assignments.find? (fun a => decide (a.question = q))).map Atom.value

private def model (w : World) (q : Question) := (lookup w q).getD none

/-- Every queried attribute has an explicit occurrence coordinate. A missing
    column rejects the table; null is a modeled absent run, zero a measured value. -/
private def validWorld (questions : List Question) (w : World) : Bool :=
  decide ((w.assignments.map Atom.question).Nodup) &&
  questions.all (fun q => (lookup w q).isSome) &&
  w.assignments.all (fun a =>
    match a.question.field with
    | .occurrence => decide (a.value = some 0 ∨ a.value = some 1)
    | .attribute _ => lookup w ⟨a.question.run,.occurrence⟩ ==
        some (some (if a.value.isSome then 1 else 0)))

private def shade : FiniteFrontier.Color → String
  | .unknown => "unknown"
  | .lawful => "supported"
  | .unlawful => "opposed"
  | .conflict => "conflict"

private def diagnosisJson : Diagnosis World → Json
  | .inconsistent => Json.mkObj [("status","inconsistent")]
  | .exact v => Json.mkObj [("status","entailed"),("value",toJson v)]
  | .ambiguous x y => Json.mkObj [("status","ambiguous"),("countermodels",toJson [x.name,y.name])]

structure State where
  log : List Event
  approved : List Event
  added : List Event

private def appendLocal (s : State) (r : Row) : State :=
  let e := Event.put r
  ⟨append s.log e,s.approved ++ [e],s.added ++ [e]⟩

private def emitPrediction (b : Bundle) (state : State) (q : Question) : State := Id.run do
  let check := fun w => decide (w ∈ b.verifiedReceipts)
  let rs := live (fun e => decide (e ∈ state.approved)) state.log
  let ps := roots check rs
  let worlds := survivors b.worlds model ps
  match diagnose model q worlds with
  | .inconsistent => return state
  | .exact _ => return state
  | .ambiguous _ _ =>
    return (bets worlds World.weight model q).foldl (fun s v =>
      let a : Atom := ⟨q,v⟩
      if rs.any (fun r => decide (r.route = .independentPrediction ∧ r.head = a ∧
          r.source = b.prior ∧ r.model = b.model ∧ r.parents = ps)) then s else
        let id := nextId s.log
        appendLocal s ⟨id,id,b.stamp,b.prior,b.model,.independentPrediction,ps,a,none⟩) state

private def planReport (cfg : Planning) (worlds : List World) (qs : List Question) : Except String Json := do
  if worlds.isEmpty then return Json.mkObj [("status","inconsistent")]
  let names := cfg.sensors.map Sensor.name
  unless names.Nodup do throw "Duplicate sensor name"
  let some count := ObservationPlanning.boundedCount cfg.sensors.length cfg.depth cfg.maxPlans
    | throw "Plan budget exceeded before enumeration"
  let observe := fun (s : Nat) (w : World) => (cfg.sensors[s]?.any (fun sensor =>
    model w sensor.question == sensor.equalsValue))
  let limits := fun (p : ObservationPlanning.Plan Nat) =>
    let traces := worlds.map (ObservationPlanning.transcript observe p)
    (traces.foldl (fun acc tr => max acc ((tr.map (fun a => (cfg.sensors[a.1]?.map Sensor.cost).getD 0)).sum)) 0,
     traces.foldl (fun acc tr => max acc tr.length) 0)
  let cost := fun p (i : Nat) => Int.ofNat (if i = 0 then (limits p).1 else (limits p).2)
  let ok := fun p => decide ((limits p).1 ≤ cfg.maxWorstCost) &&
    (!cfg.requireAll || ObservationPlanning.resolves worlds qs model observe p)
  let frontier := ObservationPlanning.optimal (List.range names.length) (if names.isEmpty then 0 else cfg.depth) ok
    (ObservationPlanning.objectives worlds qs model [0,1]) observe cost
  return Json.mkObj [("status","complete"),("candidateCount",toJson count),
    ("sensors",toJson cfg.sensors),("frontier",toJson (frontier.map (fun p =>
      Json.mkObj [("tree",toJson p),("worstCost",toJson (limits p).1),("worstReads",toJson (limits p).2),
        ("resolvesAll",toJson (ObservationPlanning.resolves worlds qs model observe p))])))]

def analyze (b : Bundle) : Except String Json := do
  let initial := live (fun e => decide (e ∈ b.authorized)) b.ledger
  let relevant := initial.filter (fun r => decide (r.route.channel ≠ .advisory))
  let allQuestions := b.questions ++ (atoms relevant).map Atom.question ++
    (b.planning.map (fun cfg => cfg.sensors.map Sensor.question)).getD []
  unless (b.worlds.map World.name).Nodup && b.worlds.all (validWorld allQuestions) do
    throw "Incomplete or inconsistent world schema, duplicate name or coordinate"
  let check := fun w => decide (w ∈ b.verifiedReceipts)
  let planned := (Admission.unique b.questions).zipIdx (nextId b.ledger)
  let proofs := batch b.worlds model b.model check initial planned b.stamp
  let grant := fun e => decide (e ∈ b.authorized ++ proofs.map Event.put)
  unless ready grant b.ledger proofs do throw "Generated proof IDs failed append admission"
  let withProofs := proofs.foldl appendLocal ⟨b.ledger,b.authorized,[]⟩
  let state := b.questions.foldl (emitPrediction b) withProofs
  let auth := fun e => decide (e ∈ state.approved)
  let rs := live auth state.log
  let observed := roots check rs
  let possible := survivors b.worlds model observed
  let result := certified b.worlds model b.model check auth state.log
  let queries := b.questions.map (fun q => Json.mkObj [
    ("question",toJson q),("diagnosis",diagnosisJson (diagnose model q possible)),
    ("minimumLossGuesses",toJson (bets possible World.weight model q))])
  let edges := rs.map (fun r => Json.mkObj [
    ("entry",toJson r),("channel",toJson r.route.channel),
    ("validatedMeasurement",toJson (measurement check r)),
    ("validatedImplication",toJson (implication b.worlds model b.model r)),
    ("rawEvidenceColor",shade (color observed r.head)),
    ("closureColor",match result with | none => Json.null | some out => toJson (shade (color out r.head)))])
  let planning ← match b.planning with | none => pure Json.null | some cfg => planReport cfg possible b.questions
  let ledgerStatus := state.log.map (fun e => Json.mkObj [("event",toJson e),("authorized",toJson (auth e)),
    ("live",match e with | .put r => toJson (decide (r ∈ rs)) | .withdraw _ => Json.null)])
  return Json.mkObj [("planning",planning),("ledger",toJson ledgerStatus),("model",b.model),("prior",b.prior),
    ("namedRuns",toJson (discover b.roster rs)),("compatibleWorlds",toJson (possible.map World.name)),
    ("newEntries",toJson state.added),("queries",toJson queries),("hyperedges",toJson edges),
    ("closure",toJson result)]

end HistoryAudit

def main (args : List String) : IO UInt32 := do
  let [path] := args | throw (IO.userError "usage: historyaudit INPUT.json")
  let data ← IO.FS.readFile path
  match Lean.Json.parse data >>= Lean.fromJson? >>= HistoryAudit.analyze with
  | .error e => IO.eprintln e; return 1
  | .ok output => IO.println output.compress; return 0
