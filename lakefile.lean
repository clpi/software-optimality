import Lake
open Lake DSL

package «software-optimality» where
  version := v!"0.1.0"
  moreLeanArgs := #["-DwarningAsError=true"]

require «software-is-quantifiable» from git
  "https://github.com/clpi/software-is-quantifiable" @ "430340295c52a015772022b2b663d01120a3a747"

@[default_target]
lean_lib SoftwareOptimality where
  roots := #[
    `Qualification,
    `FiniteQualification,
    `ExecutableClosure,
    `FiniteFrontier,
    `FiniteSchedules,
    `ForeignCampaign,
    `EligibleSchedules,
    `ScopedEvidence,
    `LinearSelection,
    `EligibleCampaign,
    `ScopedSelection,
    `ScopedCampaign,
    `MetricRelevance,
    `HypergraphIncremental,
    `ContextualDominance,
    `Admission,
    `AdmissionHypergraph,
    `AdmissionTests,
    `ComparisonContract,
    `ComparisonTests,
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
    `SoftwareOptimality
  ]
