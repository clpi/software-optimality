import Lake
open Lake DSL

package «software-optimality» where
  version := v!"0.1.0"
  moreLeanArgs := #["-DwarningAsError=true"]

require «software-is-quantifiable» from git
  "https://github.com/clpi/software-is-quantifiable" @ "d88acbdc3ba78fff994067d2c73bcc01622b3f61"

@[default_target]
lean_lib SoftwareOptimality where
  roots := #[
    `Qualification,
    `FiniteQualification,
    `ExecutableClosure,
    `ClosureStrength,
    `ExecutableIncremental,
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
    `composition.IncrementalSelection,
    `composition.TraceSafety,
    `composition.Controls,
    `composition.Benchmark,
    `composition.ExhaustiveEdits,
    `composition.AxiomAudit,
    `CanonicalDominance,
    `composition.InterfaceBridge,
    `composition.IdentityRepresentation,
    `composition.InterfaceControls,
    `docs.«covered-frontier».Controls,
    `docs.«covered-frontier».Campaign,
    `docs.«covered-frontier».ArchiveImport,
    `HistoricalEvidence,
    `HistoricalRecovery,
    `HistoricalCertificates,
    `ObservationPlanning,
    `ObservationPublication,
    `examples.HistoricalRecovery,
    `examples.ReleaseSchedule,
    `SoftwareOptimality
  ]

@[default_target]
lean_exe historyaudit where
  root := `HistoryAudit
