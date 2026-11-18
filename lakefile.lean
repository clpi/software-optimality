import Lake
open Lake DSL

package «software-optimality» where
  version := v!"0.1.0"
  moreLeanArgs := #["-DwarningAsError=true"]

@[default_target]
lean_lib SoftwareOptimality where
  roots := #[
    `Qualification,
    `FiniteQualification,
    `ExecutableClosure,
    `ExecutableIncremental,
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
    `SoftwareOptimality
  ]
