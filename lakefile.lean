import Lake
open Lake DSL

package «software-optimality» where
  version := v!"0.1.0"

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
    `Composition,
    `OptimalityInterface,
    `CompositionCheck,
    `SoftwareOptimality
  ]
