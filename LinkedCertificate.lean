import EligibleSchedules
import EligibleCampaign
import Std
namespace LinkedCertificate

/-
Linked certificate (PROOF-DESIGN sections 1 and 5), eligible-schedules form.

What is proven here:
- `principal`: for a fixed schedule instance K, acceptance of (x, cert) by
  the single checker `ScheduleInstance.accepts` yields the four clauses of
  the design in this specialization: (1) the admission components of the
  eligible gate (observed-behavior bit, positive required count, exact
  receipt count, every elapsed value within its named limit); (2) the scope
  statement, which is exactly the `timedAdmission_exact` characterization
  instantiated at K: the checker validated precisely the receipt list
  `K.checks x` against `K.required` and its per-entry limits, no more and
  no less; (3) feasibility of x in the FiniteSchedules model (length,
  venue and horizon bounds, same-venue non-overlap, dependencies);
  (4) membership in the declared candidate list together with the absence
  of a gated candidate in that list strictly dominating x on K's axes.
  Each clause is discharged by the earlier theorem that earned it:
  `EligibleSchedules.admittedNondominatedUnderSuppliedIntegerCost_exact`,
  `EligibleSchedules.eligible_exact`,
  `EligibleSchedules.timedAdmission_exact`, and
  `FiniteSchedules.feasible_exact`. Nothing is reproven.
- `generator_optimum`: the coverage upgrade of section 5 for the one
  generator whose completeness is proven. Acceptance over the enumerated
  catalogue `FiniteSchedules.feasibleSchedules` yields the absence of a
  dominator among ALL schedules of the model's shape, enumerated or not,
  because `FiniteSchedules.feasibleSchedules_exact` places every feasible
  schedule in the enumeration. This is the gated companion of
  `FiniteSchedules.certified_optimal`, proved by the same enumeration
  route with the admission gate carried through.

What is NOT claimed:
- Clause (2) in the design's full sense exceeds what the eligible-schedules
  theorems check. The observed-behavior predicate is a policy input to the
  gate: whether its pass bit is semantically true of a real execution
  (receipt contents, collected identities, outcomes) is validated
  separately, for example by the receipt checks in EligibleCampaign and by
  ScopedEvidence, and is not re-proven here. The scope clause proven is
  exactness of the checked receipt list, not behavior preservation for
  unobserved cases, and no preservation claim is dressed up as checked.
- The coverage upgrade is proven for the FiniteSchedules enumeration only.
  The ForeignCampaign queue catalogue is a supplied list: its module checks
  a frontier over that list and explicitly does not prove that the list
  exhausts all queue schedules, so no generator upgrade is claimed there.
- Receipt-byte authentication, policy authorization, and liveness of the
  named policy remain external obligations, as in PROOF-DESIGN section 9.
  Costs and axes are instance inputs; dominance means strict Pareto
  dominance on the named axes only.
-/

/-- An optimization instance in the generic eligible-schedules shape: a
feasibility check, an observed-behavior policy predicate, the required
timing-receipt count together with the per-candidate receipt lists, the
declared candidate list (the alternative space), and the cost axes.
This mirrors the parameter shapes of `EligibleSchedules.admittedNondominatedUnderSuppliedIntegerCost`
and `EligibleSchedules.eligible` exactly. -/
structure Instance (T : Type) where
  /-- Feasibility check, the first component of the eligible gate. -/
  feasible : T → Bool
  /-- Observed-behavior policy predicate, the second gate component.
  A policy input: its semantic truth for a real execution is validated
  outside this module (see the header boundary note). -/
  observed : T → Bool
  /-- Number of timing receipts every candidate must supply. -/
  required : Nat
  /-- The named timing receipts of a candidate: elapsed value paired with
  its declared hard limit, in policy order. -/
  checks : T → List (Option Nat × Nat)
  /-- The declared alternative space for catalogue optimality. -/
  candidates : List T
  /-- The named cost axes for strict Pareto comparison. -/
  axes : List Nat
  /-- Cost of a candidate on an axis. -/
  cost : T → Nat → Int

/-- The instance's admission gate: feasibility, observed behavior, and the
hard timing receipts must all pass; cost plays no part in admission. -/
def gate {T : Type} (K : Instance T) : T → Bool :=
  EligibleSchedules.eligible K.feasible K.observed K.required K.checks

/-- The single acceptance predicate of the linked certificate: the optimum
certificate check of EligibleSchedules over the instance's declared
candidate list, under the instance's gate, axes, and cost. -/
def accepts {T : Type} [DecidableEq T] (K : Instance T) (x : T) : Bool :=
  EligibleSchedules.admittedNondominatedUnderSuppliedIntegerCost K.candidates (gate K) K.axes K.cost x

/-- Exact characterization of acceptance, assembled from
`EligibleSchedules.admittedNondominatedUnderSuppliedIntegerCost_exact` and
`EligibleSchedules.eligible_exact`: acceptance holds precisely when the
gate components pass for x, x is in the declared list, and no gated member
of that list strictly dominates x on the named axes. -/
theorem accepts_exact {T : Type} [DecidableEq T] (K : Instance T) (x : T) :
    accepts K x = true ↔
      (K.feasible x = true ∧ K.observed x = true ∧ 0 < K.required ∧
        (K.checks x).length = K.required ∧
        ∀ c, c ∈ K.checks x → ∃ t, c.1 = some t ∧ t ≤ c.2) ∧
      (x ∈ K.candidates ∧
        ∀ y, y ∈ K.candidates → gate K y = true →
          ¬ ((∀ i, i ∈ K.axes → K.cost y i ≤ K.cost x i) ∧
             (∃ i, i ∈ K.axes ∧ K.cost y i < K.cost x i))) := by
  constructor
  · intro h
    obtain ⟨⟨hxmem, hgate⟩, hnodom⟩ :=
      (EligibleSchedules.admittedNondominatedUnderSuppliedIntegerCost_exact K.candidates (gate K)
        K.axes K.cost x).mp h
    obtain ⟨hfeas, hobs, hpos, hlen, hall⟩ :=
      (EligibleSchedules.eligible_exact K.feasible K.observed K.required
        K.checks x).mp hgate
    exact ⟨⟨hfeas, hobs, hpos, hlen, hall⟩, ⟨hxmem, hnodom⟩⟩
  · rintro ⟨⟨hfeas, hobs, hpos, hlen, hall⟩, hxmem, hnodom⟩
    apply (EligibleSchedules.admittedNondominatedUnderSuppliedIntegerCost_exact K.candidates (gate K)
      K.axes K.cost x).mpr
    refine ⟨⟨hxmem, ?_⟩, hnodom⟩
    apply (EligibleSchedules.eligible_exact K.feasible K.observed K.required
      K.checks x).mpr
    exact ⟨hfeas, hobs, hpos, hlen, hall⟩

/-- A schedule instance: the FiniteSchedules model parameters (jobs,
venues, horizon, durations, dependencies) together with an admission
policy (observed-behavior predicate, required receipt count, receipt
lists), a declared candidate list, and the cost axes. -/
structure ScheduleInstance where
  /-- Number of jobs every schedule places. -/
  jobs : Nat
  /-- Number of venues. -/
  venues : Nat
  /-- Latest permitted start tick. -/
  horizon : Nat
  /-- Duration of each job. -/
  duration : Nat → Nat
  /-- Dependency pairs: the first job finishes before the second starts. -/
  deps : List (Nat × Nat)
  /-- Observed-behavior policy predicate (policy input, see header). -/
  observed : FiniteSchedules.Schedule → Bool
  /-- Number of timing receipts every candidate must supply. -/
  required : Nat
  /-- The named timing receipts of a candidate, elapsed against limit. -/
  checks : FiniteSchedules.Schedule → List (Option Nat × Nat)
  /-- The declared alternative space for catalogue optimality. -/
  candidates : List FiniteSchedules.Schedule
  /-- The named cost axes for strict Pareto comparison. -/
  axes : List Nat
  /-- Cost of a schedule on an axis. -/
  cost : FiniteSchedules.Schedule → Nat → Int

/-- The generic instance view of a schedule instance: feasibility is the
FiniteSchedules model check at the instance's own parameters. -/
def ScheduleInstance.toInstance (K : ScheduleInstance) :
    Instance FiniteSchedules.Schedule where
  feasible := FiniteSchedules.feasible K.jobs K.venues K.horizon K.duration K.deps
  observed := K.observed
  required := K.required
  checks := K.checks
  candidates := K.candidates
  axes := K.axes
  cost := K.cost

/-- Acceptance of a schedule under a schedule instance: the single
acceptance predicate `accepts` at the instance's generic view. -/
def ScheduleInstance.accepts (K : ScheduleInstance)
    (x : FiniteSchedules.Schedule) : Bool :=
  LinkedCertificate.accepts K.toInstance x

/-- The principal theorem, in the shape of PROOF-DESIGN section 1, for the
eligible-schedules specialization. If the checker accepts (x, cert) for the
fixed instance K, then:
(1) admission: the observed-behavior bit passes, the required count is
    positive, the receipt list has exactly the required length, and every
    elapsed value is present and within its named limit (the unfolding of
    timed admission by `EligibleSchedules.timedAdmission_exact`, reached
    through `EligibleSchedules.admittedNondominatedUnderSuppliedIntegerCost_exact`);
(2) scope: the admission evidence is exactly the instance's named receipts
    and limits — the `timedAdmission_exact` characterization itself,
    instantiated at K, is the scope statement: timed admission of x holds
    precisely for this receipt list, this count, and these limits. The
    semantic truth of the observed-behavior bit is a policy input and is
    not part of what is checked here (see the header boundary note);
(3) feasibility: x is feasible in the FiniteSchedules model at K's jobs,
    venues, horizon, durations, and dependencies (extracted from the gate
    through `FiniteSchedules.feasible_exact`);
(4) no gated candidate in K's declared alternative space strictly
    dominates x on K's axes (from
    `EligibleSchedules.admittedNondominatedUnderSuppliedIntegerCost_exact`). -/
theorem principal (K : ScheduleInstance) (x : FiniteSchedules.Schedule)
    (h : K.accepts x = true) :
    (K.observed x = true ∧ 0 < K.required ∧
      (K.checks x).length = K.required ∧
      ∀ c, c ∈ K.checks x → ∃ t, c.1 = some t ∧ t ≤ c.2) ∧
    (EligibleSchedules.timedAdmission K.required (K.checks x) = true ↔
      0 < K.required ∧ (K.checks x).length = K.required ∧
      ∀ c, c ∈ K.checks x → ∃ t, c.1 = some t ∧ t ≤ c.2) ∧
    FiniteSchedules.Feasible K.jobs K.venues K.horizon K.duration K.deps x ∧
    (x ∈ K.candidates ∧
      ∀ y, y ∈ K.candidates → gate K.toInstance y = true →
        ¬ ((∀ i, i ∈ K.axes → K.cost y i ≤ K.cost x i) ∧
           (∃ i, i ∈ K.axes ∧ K.cost y i < K.cost x i))) := by
  obtain ⟨⟨hfeasBool, hobs, hpos, hlen, hall⟩, hxmem, hnodom⟩ :=
    (accepts_exact K.toInstance x).mp h
  have hfeas : FiniteSchedules.Feasible K.jobs K.venues K.horizon
      K.duration K.deps x :=
    (FiniteSchedules.feasible_exact K.jobs K.venues K.horizon K.duration
      K.deps x).mp hfeasBool
  exact ⟨⟨hobs, hpos, hlen, hall⟩,
    EligibleSchedules.timedAdmission_exact K.required (K.checks x),
    hfeas, ⟨hxmem, hnodom⟩⟩

/-- Acceptance over the enumerated model: the optimum certificate whose
declared alternative space is the complete enumeration
`FiniteSchedules.feasibleSchedules` at the instance's model parameters,
under the instance's own gate, axes, and cost. -/
def generatorAccepts (K : ScheduleInstance) (x : FiniteSchedules.Schedule) :
    Bool :=
  EligibleSchedules.admittedNondominatedUnderSuppliedIntegerCost
    (FiniteSchedules.feasibleSchedules K.jobs K.venues K.horizon K.duration
      K.deps)
    (gate K.toInstance) K.axes K.cost x

/-- The coverage upgrade of PROOF-DESIGN section 5, for the proven-complete
generator. If x carries an optimum certificate over the enumerated model,
then x is feasible and gated, and there is no schedule s whatsoever — any
schedule of the model's shape, enumerated or not — such that s is feasible
in the model, s passes the same admission gate, and s strictly dominates x
on the named axes. Route: any feasible s lies in the enumeration by
`FiniteSchedules.feasibleSchedules_exact`, so the catalogue-level
no-dominator clause of `EligibleSchedules.admittedNondominatedUnderSuppliedIntegerCost_exact`
applies to it. Proven for the FiniteSchedules enumeration only; no
upgrade is claimed for the ForeignCampaign queue catalogue (see header). -/
theorem generator_optimum (K : ScheduleInstance)
    (x : FiniteSchedules.Schedule) (h : generatorAccepts K x = true) :
    FiniteSchedules.Feasible K.jobs K.venues K.horizon K.duration K.deps x ∧
    (K.observed x = true ∧ 0 < K.required ∧
      (K.checks x).length = K.required ∧
      ∀ c, c ∈ K.checks x → ∃ t, c.1 = some t ∧ t ≤ c.2) ∧
    ∀ s, FiniteSchedules.Feasible K.jobs K.venues K.horizon K.duration
        K.deps s →
      gate K.toInstance s = true →
      ¬ ((∀ i, i ∈ K.axes → K.cost s i ≤ K.cost x i) ∧
         (∃ i, i ∈ K.axes ∧ K.cost s i < K.cost x i)) := by
  obtain ⟨⟨hxmem, hgate⟩, hnodom⟩ :=
    (EligibleSchedules.admittedNondominatedUnderSuppliedIntegerCost_exact
      (FiniteSchedules.feasibleSchedules K.jobs K.venues K.horizon
        K.duration K.deps)
      (gate K.toInstance) K.axes K.cost x).mp h
  obtain ⟨hfeasBool, hobs, hpos, hlen, hall⟩ :=
    (EligibleSchedules.eligible_exact K.toInstance.feasible K.observed
      K.required K.checks x).mp hgate
  have hfeas : FiniteSchedules.Feasible K.jobs K.venues K.horizon
      K.duration K.deps x :=
    (FiniteSchedules.feasibleSchedules_exact K.jobs K.venues K.horizon
      K.duration K.deps x).mp hxmem
  refine ⟨hfeas, ⟨hobs, hpos, hlen, hall⟩, ?_⟩
  intro s hsFeas hsGate hd
  exact hnodom s
    ((FiniteSchedules.feasibleSchedules_exact K.jobs K.venues K.horizon
      K.duration K.deps s).mpr hsFeas) hsGate hd

/-- The recorded pilot of EligibleCampaign, viewed as a generic instance:
worker capacity as the feasibility check, the recorded receipt flags as
the observed-behavior predicate, three required receipts, and the sole
policy axis, maximum observed wall time. -/
def pilotInstance : Instance EligibleCampaign.Candidate where
  feasible := EligibleCampaign.capacityOK
  observed := EligibleCampaign.observed
  required := 3
  checks := EligibleCampaign.timingChecks
  candidates := EligibleCampaign.catalogue
  axes := [0]
  cost := EligibleCampaign.cost

/-- A minimal synthetic schedule instance for the guards: two jobs, two
venues, unit durations, no dependencies, one required receipt that every
candidate meets, and cost equal to the sum of start ticks on the sole
axis. The first listed candidate starts both jobs at tick zero on
different venues; the second delays one job; the third overlaps both jobs
on one venue at one tick and is therefore infeasible. -/
def sampleInstance : ScheduleInstance where
  jobs := 2
  venues := 2
  horizon := 2
  duration := fun _ => 1
  deps := []
  observed := fun _ => true
  required := 1
  checks := fun _ => [(some 5, 10)]
  candidates := [[(0, 0), (1, 0)], [(0, 0), (0, 1)], [(0, 0), (0, 0)]]
  axes := [0]
  cost := fun s _ => Int.ofNat (s.foldl (fun acc p => acc + p.2) 0)

-- Positive guard: the recorded pilot's optimum passes acceptance here.
#guard accepts pilotInstance EligibleCampaign.Candidate.O2 == true
-- Negative control: the gated pilot counterfactual R2 is dominated, so
-- its certificate is refused.
#guard accepts pilotInstance EligibleCampaign.Candidate.R2 == false
-- Positive guard: the synthetic optimum passes acceptance.
#guard sampleInstance.accepts [(0, 0), (1, 0)] == true
-- Negative control: the dominated synthetic candidate is refused.
#guard sampleInstance.accepts [(0, 0), (0, 1)] == false
-- Negative control: the gate-failing (infeasible) candidate is refused.
#guard sampleInstance.accepts [(0, 0), (0, 0)] == false
-- Positive guard: the synthetic optimum also carries the generator
-- certificate over the complete enumeration.
#guard generatorAccepts sampleInstance [(0, 0), (1, 0)] == true

#print axioms principal
#print axioms generator_optimum
end LinkedCertificate
