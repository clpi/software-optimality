import Lean
import SoftwareIsQuantifiable
import SoftwareOptimality
import composition.InterfaceControls
import docs.«covered-frontier».Controls
import docs.«covered-frontier».Campaign
import docs.«covered-frontier».ArchiveImport
import examples.ReleaseSchedule
open Lean Elab Command

-- Audit every theorem declaration in the named core/composition modules,
-- including private and generated names. Examples and executable guards are
-- checked separately by their registered build roots and runners.
run_cmd do
  let env ← getEnv
  let modules := [`Qualification,`FiniteQualification,`ExecutableClosure,`FiniteFrontier,
    `FiniteSchedules,`ForeignCampaign,`EligibleSchedules,`ScopedEvidence,`LinearSelection,
    `EligibleCampaign,`ScopedSelection,`ScopedCampaign,`MetricRelevance,`HypergraphIncremental,
    `ExecutableIncremental,`CheckedTransfer,`EvidenceTransport,`WorklistClosure,`StrictSchedules,
    `LinkedCertificate,`ScopedCompatibility,`ThreeValuedGate,`CanonicalDominance,
    `composition.InterfaceBridge,`composition.InterfaceControls,
    `docs.«covered-frontier».Controls,`docs.«covered-frontier».Campaign,
    `examples.ReleaseSchedule,`GeneralPareto,`Composition,`OptimalityInterface,`FrontierComposition,`ContextualDominance,`Admission,
    `AdmissionHypergraph,`ComparisonContract,`ScopedFrontier,
    `composition.QualifiedClosure,`composition.QualifiedSelection,`composition.IntervalDominance,
    `composition.LiveSelection,`composition.IncrementalSelection,`composition.TraceSafety,`SoftwareIsQuantifiable.Finiteness,
    `SoftwareIsQuantifiable.Fold,`SoftwareIsQuantifiable.Coloring,`SoftwareIsQuantifiable.Pareto,
    `SoftwareIsQuantifiable.Coverage,`SoftwareIsQuantifiable.Interface,`SoftwareIsQuantifiable.Instance]
  let allowed := [`propext,`Quot.sound,`Classical.choice]
  let mut total := 0
  for m in modules do
    let some idx := env.getModuleIdx? m | throwError "module missing: {m}"
    let mut count := 0
    for (name, info) in env.constants.toList do
      if env.getModuleIdxFor? name == some idx then
        if info.isTheorem then
          let deps ← collectAxioms name
          for d in deps do
            unless allowed.contains d do throwError "unexpected dependency {d} in {name}"
          count := count + 1
    if count == 0 then throwError "no theorems found in {m}"
    total := total + count
    logInfo m!"{m}: {count} theorem declarations"
  logInfo m!"{total} theorem declarations across {modules.length} modules passed the foundation check"
