import Lake
open Lake DSL

package «software-optimality» where
  version := v!"0.1.0"
  moreLeanArgs := #["-DwarningAsError=true"]

require «software-is-quantifiable» from git
  "https://github.com/clpi/software-is-quantifiable" @ "f370992611d8c722e4897e67dbb8eaecf3d872ed"

@[default_target]
lean_lib SoftwareOptimality where
  roots := #[
    `Qualification,
    `FiniteQualification,
    `ExecutableClosure,
    `WorklistClosure,
    `FiniteFrontier,
    `FiniteSchedules,
    `StrictSchedules,
    `ForeignCampaign,
    `EligibleSchedules,
    `ScopedEvidence,
    `CheckedTransfer,
    `EvidenceTransport,
    `LinearSelection,
    `EligibleCampaign,
    `LinkedCertificate,
    `ScopedSelection,
    `ScopedCompatibility,
    `ScopedCampaign,
    `MetricRelevance,
    `HypergraphIncremental,
    `ContextualDominance,
    `Admission,
    `AdmissionHypergraph,
    `AdmissionTests,
    `ComparisonContract,
    `ComparisonTests,
    `ThreeValuedGate,
    `FrontierComposition,
    `ScopedFrontier,
    `GeneralPareto,
    `Composition,
    `OptimalityInterface,
    `CompositionCheck,
    `composition.QualifiedClosure,
    `composition.QualifiedSelection,
    `composition.IntervalDominance,
    `composition.LiveSelection,
    `composition.TraceSafety,
    `composition.Controls,
    `composition.Benchmark,
    `CanonicalDominance,
    `composition.InterfaceBridge,
    `composition.InterfaceControls,
    `docs.«covered-frontier».Controls,
    `docs.«covered-frontier».Campaign,
    `docs.«covered-frontier».ArchiveImport,
    `examples.ReleaseSchedule,
    `SoftwareOptimality
  ]
