import Lean
import composition.Controls
import composition.TraceSafety
import ContextualDominance
import AdmissionTests
import ComparisonTests
import FiniteQualification
import GeneralPareto
import OptimalityInterface
import CompositionCheck
import ForeignCampaign
import ScopedCampaign
import MetricRelevance
import SoftwareIsQuantifiable
open Lean Elab Command

-- Audit the transitive dependencies of every theorem in either source tree,
-- including private theorem names. Work from the defining module identity.
run_cmd do
  let env ← getEnv
  let modules := [`Qualification,`FiniteQualification,`ExecutableClosure,`FiniteFrontier,
    `FiniteSchedules,`ForeignCampaign,`EligibleSchedules,`ScopedEvidence,`LinearSelection,
    `EligibleCampaign,`ScopedSelection,`ScopedCampaign,`MetricRelevance,`HypergraphIncremental,
    `ExecutableIncremental,`GeneralPareto,`Composition,`OptimalityInterface,`FrontierComposition,`ContextualDominance,`Admission,
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
