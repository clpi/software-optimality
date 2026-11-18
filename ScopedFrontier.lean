import ScopedSelection
import HypergraphIncremental
import AdmissionHypergraph
import ComparisonContract
import FrontierComposition
import Std

/- One comparison authority: the contract owns every obligation and its cap.
   A named subject supplies artifact/configuration/lineage. Input contains only
   receipts and its declared contract, never a second editable policy.
   Metric IDs require authenticated unit/schema binding at ingestion. -/
namespace ScopedFrontier
open ScopedEvidence

structure Metric where
  id : Nat
  unit : Nat
  deriving DecidableEq, Repr

structure Axis where
  metric : Nat
  round : Nat
  maximize : Bool
  deriving DecidableEq, Repr

structure Obligation where
  metric : Nat
  round : Nat
  limit : Nat
  deriving DecidableEq, Repr

structure Subject where
  artifact : Nat
  configuration : Nat
  lineage : Nat
  deriving DecidableEq, Repr

structure Contract where
  scope : Nat -- fixed comparison instance and named alternative-space semantics
  intent : Nat
  policy : Nat
  preservation : Nat -- behavior/effect compatibility contract
  venue : Nat
  harness : Nat
  metrics : List Metric -- hard qualification metrics need not be objective axes
  required : List Obligation
  axes : List Axis -- exact ordered, unaggregated objective coordinates
  deriving DecidableEq, Repr

structure Input where
  contract : Contract
  receipts : List Receipt
  deriving DecidableEq, Repr

def axisKey (a : Axis) := (a.metric, a.round)
def obligationKey (q : Obligation) := (q.metric, q.round)

def declared (k : Contract) (metric : Nat) : Bool :=
  k.metrics.any (fun m => decide (m.id = metric))

def contractOK (k : Contract) : Bool :=
  decide (0 < k.axes.length) && decide ((k.metrics.map Metric.id).Nodup) &&
  decide ((k.axes.map axisKey).Nodup) &&
  decide ((k.required.map obligationKey).Nodup) &&
  k.axes.all (fun a => declared k a.metric) &&
  k.required.all (fun q => declared k q.metric)

def expectedScope (k : Contract) (s : Subject) (metric : Nat) : Scope :=
  ⟨s.artifact, s.configuration, s.lineage, k.venue, k.harness, k.intent, k.policy, metric⟩

-- No candidate-controlled requirements, caps, venue, harness or subject rewrite.
def expectedPolicy (k : Contract) (s : Subject) : Policy :=
  ⟨k.policy, k.required.map (fun q => ⟨expectedScope k s q.metric, q.round, q.limit⟩)⟩

theorem expected_requirement_exact (k : Contract) (s : Subject) (q : Requirement) :
    q ∈ (expectedPolicy k s).required ↔
      ∃ o, o ∈ k.required ∧ q = ⟨expectedScope k s o.metric, o.round, o.limit⟩ := by
  simp only [expectedPolicy, List.mem_map]
  constructor
  · rintro ⟨o, ho, he⟩; exact ⟨o, ho, he.symm⟩
  · rintro ⟨o, ho, he⟩; exact ⟨o, ho, he.symm⟩

def requirementMatches (a : Axis) (q : Requirement) : Bool :=
  decide (q.scope.metric = a.metric ∧ q.round = a.round)

-- A coordinate names one authoritative obligation and its one exact receipt.
-- Multiple contexts at one metric/round require a separately qualified metric;
-- this adapter never aggregates them implicitly.
def coordinate (a : Axis) (p : Policy) (rs : List Receipt) : Option Nat :=
  match p.required.filter (requirementMatches a) with
  | [q] =>
    match rs.filter (matchingKey q) with
    | [r] => r.elapsed
    | _ => none
  | _ => none

theorem coordinate_exact (a : Axis) (p : Policy) (rs : List Receipt) (v : Nat) :
    coordinate a p rs = some v ↔
      ∃ q r, p.required.filter (requirementMatches a) = [q] ∧
        rs.filter (matchingKey q) = [r] ∧ r.elapsed = some v := by
  unfold coordinate
  generalize hq : p.required.filter (requirementMatches a) = qs
  cases qs with
  | nil => simp
  | cons q tail =>
    cases tail with
    | cons q' tail => simp
    | nil =>
      simp only [List.singleton_inj, exists_eq_left']
      generalize hr : rs.filter (matchingKey q) = hits
      cases hits with
      | nil => simp [hr]
      | cons r tail =>
        cases tail with
        | nil => simp [hr]
        | cons r' tail => simp [hr]

def aligned (k : Contract) (s : Subject) (x : Input) : Bool :=
  contractOK k && decide (x.contract = k) &&
  k.axes.all (fun a => (coordinate a (expectedPolicy k s) x.receipts).isSome)

def admitted (k : Contract) (s : Subject) (x : Input) : Bool :=
  aligned k s x && ScopedEvidence.qualify (expectedPolicy k s) x.receipts

theorem admitted_exact (k : Contract) (s : Subject) (x : Input) :
    admitted k s x = true ↔
      contractOK k = true ∧ x.contract = k ∧
      (∀ a, a ∈ k.axes → (coordinate a (expectedPolicy k s) x.receipts).isSome = true) ∧
      ScopedEvidence.qualify (expectedPolicy k s) x.receipts = true := by
  simp only [admitted, aligned, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, and_assoc]

theorem wrong_contract_rejected (k : Contract) (s : Subject) (x : Input)
    (h : x.contract ≠ k) : admitted k s x = false := by
  simp [admitted, aligned, h]

theorem wrong_metric_schema_rejected (k : Contract) (s : Subject) (x : Input)
    (h : x.contract.metrics ≠ k.metrics) : admitted k s x = false := by
  apply wrong_contract_rejected
  intro same
  exact h (congrArg Contract.metrics same)

theorem wrong_scope_rejected (k : Contract) (s : Subject) (x : Input)
    (q : Requirement) (hq : q ∈ (expectedPolicy k s).required)
    (bad : ∀ r, r ∈ x.receipts → r.scope ≠ q.scope) :
    admitted k s x = false := by
  cases ha : admitted k s x
  · rfl
  · have qualified := ((admitted_exact k s x).mp ha).2.2.2
    have good := ((ScopedEvidence.qualify_exact _ _).mp qualified).2.2.2.2.2 q hq
    have refused := ScopedEvidence.wrong_scope_rejected q x.receipts bad
    simp [refused] at good

-- Every objective value has a contract-owned, subject-scoped, bounded witness.
theorem admitted_coordinate_witness (k : Contract) (s : Subject) (x : Input) (a : Axis)
    (ha : a ∈ k.axes) (hx : admitted k s x = true) :
    ∃ o r v, o ∈ k.required ∧ r ∈ x.receipts ∧
      o.metric = a.metric ∧ o.round = a.round ∧
      r.scope = expectedScope k s o.metric ∧ r.round = o.round ∧ r.observedPass = true ∧
      r.elapsed = some v ∧ v ≤ o.limit ∧
      coordinate a (expectedPolicy k s) x.receipts = some v := by
  have h := (admitted_exact k s x).mp hx
  have hc := h.2.2.1 a ha
  cases hv : coordinate a (expectedPolicy k s) x.receipts with
  | none => simp [hv] at hc
  | some v =>
    obtain ⟨q, r, hq, hr, he⟩ := (coordinate_exact a (expectedPolicy k s) x.receipts v).mp hv
    have hqm : q ∈ (expectedPolicy k s).required.filter (requirementMatches a) := hq ▸ List.mem_cons_self
    obtain ⟨hqmem, hmatch⟩ := List.mem_filter.mp hqm
    have hqr : q.scope.metric = a.metric ∧ q.round = a.round := of_decide_eq_true hmatch
    have hrm : r ∈ x.receipts.filter (matchingKey q) := hr ▸ List.mem_cons_self
    obtain ⟨hrmem, hrmatch⟩ := List.mem_filter.mp hrm
    have hrr : r.scope = q.scope ∧ r.round = q.round := of_decide_eq_true hrmatch
    have checked := ((ScopedEvidence.qualify_exact _ _).mp h.2.2.2).2.2.2.2.2 q hqmem
    have bound : r.observedPass = true ∧ ∃ t, r.elapsed = some t ∧ t ≤ q.limit := by
      simpa only [ScopedEvidence.checkRequirement, hr, Bool.and_eq_true,
        EligibleSchedules.timingOK_exact] using checked
    obtain ⟨passed, t, ht, limit⟩ := bound
    have tv : t = v := Option.some.inj (ht.symm.trans he)
    subst t
    obtain ⟨o, ho, rfl⟩ := (expected_requirement_exact k s q).mp hqmem
    exact ⟨o, r, v, ho, hrmem, hqr.1, hqr.2, hrr.1, hrr.2, passed, he, limit, rfl⟩

-- Hard obligations outside the cost axes are mandatory too.
theorem admitted_obligation_witness (k : Contract) (s : Subject) (x : Input)
    (hx : admitted k s x = true) (o : Obligation) (ho : o ∈ k.required) :
    ∃ r, r ∈ x.receipts ∧ r.scope = expectedScope k s o.metric ∧ r.round = o.round ∧
      r.observedPass = true ∧ ∃ v, r.elapsed = some v ∧ v ≤ o.limit := by
  have qualified := ((admitted_exact k s x).mp hx).2.2.2
  apply ScopedEvidence.qualification_witnesses (expectedPolicy k s) x.receipts qualified
    ⟨expectedScope k s o.metric, o.round, o.limit⟩
  exact (expected_requirement_exact k s _).mpr ⟨o, ho, rfl⟩

def normalize (a : Axis) (v : Nat) : Int :=
  ComparisonContract.normalize
    (if a.maximize then .maximize else .minimize) (Int.ofNat v)

-- Defaults outside the admitted axis domain never stand in for missing evidence.
def cost (k : Contract) (s : Subject) (x : Input) (i : Nat) : Int :=
  match k.axes[i]? with
  | none => 0
  | some a => normalize a ((coordinate a (expectedPolicy k s) x.receipts).getD 0)

theorem admitted_cost_witness (k : Contract) (s : Subject) (x : Input) (i : Nat)
    (hi : i ∈ List.range k.axes.length) (hx : admitted k s x = true) :
    ∃ a o r v, k.axes[i]? = some a ∧ o ∈ k.required ∧ r ∈ x.receipts ∧
      o.metric = a.metric ∧ o.round = a.round ∧
      r.scope = expectedScope k s o.metric ∧ r.round = o.round ∧ r.observedPass = true ∧
      r.elapsed = some v ∧ v ≤ o.limit ∧ cost k s x i = normalize a v := by
  have hil : i < k.axes.length := List.mem_range.mp hi
  let a := k.axes[i]
  have hat : k.axes[i]? = some a := List.getElem?_eq_getElem hil
  obtain ⟨o, r, v, ho, hr, hm, hd, hs, hrr, hp, he, hl, hv⟩ :=
    admitted_coordinate_witness k s x a (List.mem_of_getElem? hat) hx
  exact ⟨a, o, r, v, hat, ho, hr, hm, hd, hs, hrr, hp, he, hl,
    by simp only [cost, hat, hv, Option.getD_some]⟩

-- Explicit numeric adapter to the existing typed comparison owner. Workload,
-- epoch and aggregation keep their supplied meanings: they are not aliases for
-- intent, scope or round. Their semantic applicability is an ingestion premise.
def alignedComparisonAxes (k : Contract) (c : ComparisonContract.Contract) : Prop :=
  c.axes.length = k.axes.length ∧ c.venue = k.venue ∧
  ∀ i, i ∈ List.range k.axes.length → ∃ a b,
    k.axes[i]? = some a ∧ c.axes[i]? = some b ∧ b.metric = a.metric ∧
    (∃ m, m ∈ k.metrics ∧ m.id = a.metric ∧ m.unit = b.unit) ∧
    b.direction = (if a.maximize then .maximize else .minimize)

def typedValues (k : Contract) (s : Subject) (x : Input) : List Int :=
  k.axes.map (fun a => Int.ofNat ((coordinate a (expectedPolicy k s) x.receipts).getD 0))

def typedObservation (k : Contract) (c : ComparisonContract.Contract) (s : Subject) (x : Input)
    (alignment : alignedComparisonAxes k c) (_qualified : admitted k s x = true) :
    ComparisonContract.Observation c :=
  ⟨typedValues k s x, by
    simpa only [ComparisonContract.valid, typedValues, List.length_map] using alignment.1.symm⟩

theorem typed_cost_agrees (k : Contract) (c : ComparisonContract.Contract) (s : Subject) (x : Input)
    (alignment : alignedComparisonAxes k c) (i : Nat) (hi : i ∈ List.range k.axes.length) :
    ComparisonContract.cost c (typedValues k s x) i = cost k s x i := by
  obtain ⟨a, b, ha, hb, _, _, direction⟩ := alignment.2.2 i hi
  simp only [ComparisonContract.cost, typedValues, List.getElem?_map, ha,
    Option.map_some, Option.getD_some, hb, cost, normalize, direction]
  rfl

def dominates (k : Contract) (input : Subject → Input) (y x : Subject) : Bool :=
  FiniteFrontier.strictPareto (List.range k.axes.length) (fun t => cost k t (input t)) y x

theorem typed_dominance_agrees (k : Contract) (c : ComparisonContract.Contract)
    (input : Subject → Input) (alignment : alignedComparisonAxes k c) (y x : Subject) :
    ComparisonContract.dominates c (typedValues k y (input y)) (typedValues k x (input x)) =
      dominates k input y x := by
  have equalTrue :
      ComparisonContract.dominates c (typedValues k y (input y)) (typedValues k x (input x)) = true ↔
      dominates k input y x = true := by
    rw [ComparisonContract.dominance_exact]
    change _ ↔ FiniteFrontier.strictPareto _ _ y x = true
    rw [FiniteFrontier.pareto_exact, alignment.1]
    constructor
    · rintro ⟨weak, i, hi, strict⟩
      constructor
      · intro j hj
        simpa only [typed_cost_agrees k c y (input y) alignment j hj,
          typed_cost_agrees k c x (input x) alignment j hj] using weak j hj
      · exact ⟨i, hi, by simpa only [typed_cost_agrees k c y (input y) alignment i hi,
          typed_cost_agrees k c x (input x) alignment i hi] using strict⟩
    · rintro ⟨weak, i, hi, strict⟩
      constructor
      · intro j hj
        simpa only [typed_cost_agrees k c y (input y) alignment j hj,
          typed_cost_agrees k c x (input x) alignment j hj] using weak j hj
      · exact ⟨i, hi, by simpa only [typed_cost_agrees k c y (input y) alignment i hi,
          typed_cost_agrees k c x (input x) alignment i hi] using strict⟩
  cases hl : ComparisonContract.dominates c (typedValues k y (input y)) (typedValues k x (input x)) <;>
    cases hr : dominates k input y x <;> simp_all

theorem typed_direct_agrees (k : Contract) (c : ComparisonContract.Contract)
    (input : Subject → Input) (alignment : alignedComparisonAxes k c) (y x : Subject)
    (hy : admitted k y (input y) = true) (hx : admitted k x (input x) = true) :
    ComparisonContract.direct ⟨c, typedValues k y (input y)⟩ ⟨c, typedValues k x (input x)⟩ =
      some (dominates k input y x) := by
  have sy := (typedObservation k c y (input y) alignment hy).shape
  have sx := (typedObservation k c x (input x) alignment hx).shape
  have compatible : c = c ∧ ComparisonContract.valid c (typedValues k y (input y)) ∧
      ComparisonContract.valid c (typedValues k x (input x)) := ⟨rfl, sy, sx⟩
  change (if c = c ∧ ComparisonContract.valid c (typedValues k y (input y)) ∧
      ComparisonContract.valid c (typedValues k x (input x)) then
    some (ComparisonContract.dominates c (typedValues k y (input y)) (typedValues k x (input x)))
    else none) = some (dominates k input y x)
  rw [if_pos compatible, typed_dominance_agrees k c input alignment y x]

-- The Subject catalogue is independent of the submitted receipt payloads.
def select (k : Contract) (candidates : List Subject) (input : Subject → Input) : List Subject :=
  FiniteFrontier.frontier (candidates.filter (fun x => admitted k x (input x))) (dominates k input)

-- Search may submit a retained set, but the existing certificate checks it
-- against the complete admitted catalogue under the same measured cost contract.
def certify (k : Contract) (candidates retained : List Subject) (input : Subject → Input) : Bool :=
  FiniteFrontier.certificate (candidates.filter (fun x => admitted k x (input x)))
    retained (dominates k input)

theorem selected_exact (k : Contract) (candidates : List Subject)
    (input : Subject → Input) (x : Subject) :
    x ∈ select k candidates input ↔
      (x ∈ candidates ∧ admitted k x (input x) = true) ∧
      ∀ y, y ∈ candidates → admitted k y (input y) = true → dominates k input y x = false := by
  rw [select, FiniteFrontier.frontier_exact]
  simp only [List.mem_filter]
  constructor
  · rintro ⟨hx, hn⟩; exact ⟨hx, fun y hy hg => hn y ⟨hy, hg⟩⟩
  · rintro ⟨hx, hn⟩; exact ⟨hx, fun y hy => hn y hy.1 hy.2⟩

theorem certified_select_exact (k : Contract) (candidates retained : List Subject)
    (input : Subject → Input) (valid : certify k candidates retained input = true) (x : Subject) :
    x ∈ retained ↔ x ∈ select k candidates input :=
  FiniteFrontier.certified_frontier _ retained (dominates k input) valid x

theorem certified_retained_admitted (k : Contract) (candidates retained : List Subject)
    (input : Subject → Input) (valid : certify k candidates retained input = true)
    (x : Subject) (hx : x ∈ retained) : admitted k x (input x) = true :=
  ((selected_exact k candidates input x).mp
    ((certified_select_exact k candidates retained input valid x).mp hx)).1.2

theorem certified_obligation_witness (k : Contract) (candidates retained : List Subject)
    (input : Subject → Input) (valid : certify k candidates retained input = true)
    (x : Subject) (hx : x ∈ retained) (o : Obligation) (ho : o ∈ k.required) :
    ∃ r, r ∈ (input x).receipts ∧ r.scope = expectedScope k x o.metric ∧ r.round = o.round ∧
      r.observedPass = true ∧ ∃ v, r.elapsed = some v ∧ v ≤ o.limit :=
  admitted_obligation_witness k x (input x)
    (certified_retained_admitted k candidates retained input valid x hx) o ho

theorem selected_has_no_qualified_dominator (k : Contract) (candidates : List Subject)
    (input : Subject → Input) (x y : Subject)
    (hx : x ∈ select k candidates input) (hy : y ∈ candidates)
    (hg : admitted k y (input y) = true) : dominates k input y x = false :=
  ((selected_exact k candidates input x).mp hx).2 y hy hg

theorem dominator_excludes (k : Contract) (candidates : List Subject)
    (input : Subject → Input) (x y : Subject) (hy : y ∈ candidates)
    (hg : admitted k y (input y) = true) (hd : dominates k input y x = true) :
    x ∉ select k candidates input := by
  intro hx
  have hf := selected_has_no_qualified_dominator k candidates input x y hx hy hg
  simp [hf] at hd

theorem selected_order_independent (k : Contract) (xs ys : List Subject)
    (input : Subject → Input) (same : ∀ x, x ∈ xs ↔ x ∈ ys) :
    ∀ x, x ∈ select k xs input ↔ x ∈ select k ys input := by
  intro x
  rw [selected_exact, selected_exact]
  constructor
  · rintro ⟨⟨hx, hg⟩, hn⟩
    exact ⟨⟨(same x).mp hx, hg⟩, fun y hy hygate => hn y ((same y).mpr hy) hygate⟩
  · rintro ⟨⟨hx, hg⟩, hn⟩
    exact ⟨⟨(same x).mpr hx, hg⟩, fun y hy hygate => hn y ((same y).mp hy) hygate⟩

theorem tied_member_retained (k : Contract) (candidates : List Subject)
    (input : Subject → Input) (x y : Subject) (hx : x ∈ select k candidates input)
    (hy : y ∈ candidates) (hg : admitted k y (input y) = true)
    (same : ∀ i, i ∈ List.range k.axes.length → cost k x (input x) i = cost k y (input y) i) :
    y ∈ select k candidates input := by
  apply (selected_exact k candidates input y).mpr
  refine ⟨⟨hy, hg⟩, ?_⟩
  intro z hz hzgate
  cases hd : dominates k input z y
  · rfl
  · have p := (FiniteFrontier.pareto_exact (List.range k.axes.length)
      (fun t => cost k t (input t)) z y).mp hd
    have dx : dominates k input z x = true := by
      apply (FiniteFrontier.pareto_exact (List.range k.axes.length)
        (fun t => cost k t (input t)) z x).mpr
      constructor
      · intro i hi; rw [same i hi]; exact p.1 i hi
      · obtain ⟨i, hi, hs⟩ := p.2
        exact ⟨i, hi, (same i hi).symm ▸ hs⟩
    have no := selected_has_no_qualified_dominator k candidates input x z hx hz hzgate
    simp [no] at dx

-- Nondomination permits tradeoffs; a named replacement policy may forbid them.
def noRegression (k : Contract) (incumbent candidate : Subject) (input : Subject → Input) : Bool :=
  admitted k incumbent (input incumbent) && admitted k candidate (input candidate) &&
  (List.range k.axes.length).all (fun i =>
    decide (cost k candidate (input candidate) i ≤ cost k incumbent (input incumbent) i))

theorem noRegression_exact (k : Contract) (incumbent candidate : Subject) (input : Subject → Input) :
    noRegression k incumbent candidate input = true ↔
      admitted k incumbent (input incumbent) = true ∧ admitted k candidate (input candidate) = true ∧
      ∀ i, i ∈ List.range k.axes.length →
        cost k candidate (input candidate) i ≤ cost k incumbent (input incumbent) i := by
  simp only [noRegression, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, and_assoc]

theorem incremental_selection_exact {A : Type}
    (old new : HypergraphIncremental.Hypergraph A) (k : Contract)
    (candidates : List Subject) (project : (A → Prop) → Subject → Input) :
    select k candidates (project (HypergraphIncremental.incremental old new)) =
      select k candidates (project (HypergraphIncremental.derives new)) := by
  have same : HypergraphIncremental.incremental old new = HypergraphIncremental.derives new := by
    funext a
    exact propext (HypergraphIncremental.incremental_exact old new a)
  rw [same]

-- Admitted event normalization feeds the existing authoritative hypergraph.
-- Any deterministic projection of its qualifications preserves selection when
-- admitted provenance is equal; decoder/measurement soundness stays explicit.
theorem admitted_provenance_selection_same {A : Type}
    (decoder : AdmissionHypergraph.Decoder A)
    (auth₁ auth₂ : Admission.Event → Bool) (xs ys : List Admission.Event)
    (same : ∀ e, Admission.admitted auth₁ xs e ↔ Admission.admitted auth₂ ys e)
    (k : Contract) (candidates : List Subject) (project : (A → Prop) → Subject → Input) :
    select k candidates (project (HypergraphIncremental.derives
      (AdmissionHypergraph.graph decoder auth₁ xs))) =
    select k candidates (project (HypergraphIncremental.derives
      (AdmissionHypergraph.graph decoder auth₂ ys))) := by
  have h : HypergraphIncremental.derives (AdmissionHypergraph.graph decoder auth₁ xs) =
      HypergraphIncremental.derives (AdmissionHypergraph.graph decoder auth₂ ys) := by
    funext a
    exact propext (AdmissionHypergraph.qualification_same decoder auth₁ auth₂ xs ys same a)
  rw [h]

theorem replay_selection_idempotent {A : Type} (decoder : AdmissionHypergraph.Decoder A)
    (auth : Admission.Event → Bool) (xs : List Admission.Event)
    (k : Contract) (candidates : List Subject) (project : (A → Prop) → Subject → Input) :
    select k candidates (project (HypergraphIncremental.derives
      (AdmissionHypergraph.graph decoder auth (xs ++ xs)))) =
    select k candidates (project (HypergraphIncremental.derives
      (AdmissionHypergraph.graph decoder auth xs))) := by
  apply admitted_provenance_selection_same
  intro e
  simp [Admission.admitted]

theorem merge_selection_order_independent {A : Type} (decoder : AdmissionHypergraph.Decoder A)
    (auth : Admission.Event → Bool) (xs ys : List Admission.Event)
    (k : Contract) (candidates : List Subject) (project : (A → Prop) → Subject → Input) :
    select k candidates (project (HypergraphIncremental.derives
      (AdmissionHypergraph.graph decoder auth (xs ++ ys)))) =
    select k candidates (project (HypergraphIncremental.derives
      (AdmissionHypergraph.graph decoder auth (ys ++ xs)))) := by
  apply admitted_provenance_selection_same
  intro e
  simp [Admission.admitted, or_comm]

-- A catalogue can cover a larger declared generator without enumerating it:
-- every omitted qualified identity needs a STRICT qualified catalogue
-- dominator. The witness lands in the catalogue, not an ungrounded chain of
-- further omitted points. Equal-cost identities cannot be discarded this way.
def covers (k : Contract) (generator : Subject → Prop)
    (catalogue : List Subject) (input : Subject → Input) : Prop :=
  (∀ x, x ∈ catalogue → generator x) ∧
  (∀ x, generator x → admitted k x (input x) = true →
    x ∈ catalogue ∨ ∃ y, y ∈ catalogue ∧ admitted k y (input y) = true ∧
      dominates k input y x = true)

def generatorFrontier (k : Contract) (generator : Subject → Prop)
    (input : Subject → Input) (x : Subject) : Prop :=
  generator x ∧ admitted k x (input x) = true ∧
    ∀ y, generator y → admitted k y (input y) = true → dominates k input y x = false

theorem dominates_trans (k : Contract) (input : Subject → Input) (z y x : Subject)
    (hzy : dominates k input z y = true) (hyx : dominates k input y x = true) :
    dominates k input z x = true :=
  FrontierComposition.pareto_transitive (List.range k.axes.length)
    (fun t => cost k t (input t)) hzy hyx

-- The generator need not be finite. Coverage is a theorem premise, never a
-- conclusion inferred from search exhaustion or missing measurements.
theorem certified_generator_exact (k : Contract) (generator : Subject → Prop)
    (catalogue retained : List Subject) (input : Subject → Input)
    (coverage : covers k generator catalogue input)
    (valid : certify k catalogue retained input = true) (x : Subject) :
    x ∈ retained ↔ generatorFrontier k generator input x := by
  constructor
  · intro hx
    have selected := (selected_exact k catalogue input x).mp
      ((certified_select_exact k catalogue retained input valid x).mp hx)
    refine ⟨coverage.1 x selected.1.1, selected.1.2, ?_⟩
    intro y hy qualified
    rcases coverage.2 y hy qualified with member | ⟨z, hz, qualifiedZ, beats⟩
    · exact selected.2 y member qualified
    · cases h : dominates k input y x
      · rfl
      · have zx := dominates_trans k input z y x beats h
        have no := selected.2 z hz qualifiedZ
        rw [no] at zx
        contradiction
  · rintro ⟨hx, qualified, no⟩
    have member : x ∈ catalogue := by
      rcases coverage.2 x hx qualified with member | ⟨y, hy, qualifiedY, beats⟩
      · exact member
      · have excluded := no y (coverage.1 y hy) qualifiedY
        rw [excluded] at beats
        contradiction
    apply (certified_select_exact k catalogue retained input valid x).mpr
    exact (selected_exact k catalogue input x).mpr
      ⟨⟨member, qualified⟩, fun y hy hq => no y (coverage.1 y hy) hq⟩

-- Finite coverage is executable. This checks the declared domain as well as
-- the retained catalogue; checking only the latter cannot establish coverage.
def checkCoverage (k : Contract) (domain catalogue : List Subject)
    (input : Subject → Input) : Bool :=
  catalogue.all (fun x => domain.contains x) &&
  FrontierComposition.checkCover (dominates k input)
    (domain.filter (fun x => admitted k x (input x)))
    (catalogue.filter (fun x => admitted k x (input x)))

theorem checkCoverage_exact (k : Contract) (domain catalogue : List Subject)
    (input : Subject → Input) :
    checkCoverage k domain catalogue input = true ↔
      covers k (fun x => x ∈ domain) catalogue input := by
  simp only [checkCoverage, Bool.and_eq_true, List.all_eq_true, List.contains_iff,
    FrontierComposition.checkCover_exact]
  constructor
  · rintro ⟨sound, covered⟩
    refine ⟨sound, ?_⟩
    intro x hx qualified
    rcases covered.replaces x (List.mem_filter.mpr ⟨hx, qualified⟩) with kept | ⟨y, hy, beats⟩
    · exact Or.inl (List.mem_filter.mp kept).1
    · have member := List.mem_filter.mp hy
      exact Or.inr ⟨y, member.1, member.2, beats⟩
  · rintro ⟨sound, covered⟩
    refine ⟨sound, ⟨?_, ?_⟩⟩
    · intro x hx
      have member := List.mem_filter.mp hx
      exact List.mem_filter.mpr ⟨sound x member.1, member.2⟩
    · intro x hx
      have member := List.mem_filter.mp hx
      rcases covered x member.1 member.2 with kept | ⟨y, hy, qualified, beats⟩
      · exact Or.inl (List.mem_filter.mpr ⟨kept, member.2⟩)
      · exact Or.inr ⟨y, List.mem_filter.mpr ⟨hy, qualified⟩, beats⟩

def certifyCovered (k : Contract) (domain catalogue retained : List Subject)
    (input : Subject → Input) : Bool :=
  contractOK k && checkCoverage k domain catalogue input &&
    certify k catalogue retained input

theorem certifyCovered_exact (k : Contract) (domain catalogue retained : List Subject)
    (input : Subject → Input) :
    certifyCovered k domain catalogue retained input = true ↔
      contractOK k = true ∧ covers k (fun x => x ∈ domain) catalogue input ∧
        certify k catalogue retained input = true := by
  simp only [certifyCovered, Bool.and_eq_true, checkCoverage_exact, and_assoc]

theorem certified_covered_frontier (k : Contract)
    (domain catalogue retained : List Subject) (input : Subject → Input)
    (valid : certifyCovered k domain catalogue retained input = true) (x : Subject) :
    x ∈ retained ↔ generatorFrontier k (fun x => x ∈ domain) input x := by
  have checked := (certifyCovered_exact k domain catalogue retained input).mp valid
  exact certified_generator_exact k _ catalogue retained input checked.2.1 checked.2.2 x

-- A complete frontier can be empty and can contain incomparable tradeoffs.
-- Replacing a named incumbent additionally needs membership, qualification,
-- no regression on every declared axis, and at least one strict improvement.
def certifyReplacement (k : Contract) (domain catalogue retained : List Subject)
    (input : Subject → Input) (incumbent candidate : Subject) : Bool :=
  certifyCovered k domain catalogue retained input && decide (incumbent ∈ domain) &&
    decide (candidate ∈ retained) && noRegression k incumbent candidate input &&
    dominates k input candidate incumbent

theorem certifyReplacement_sound (k : Contract) (domain catalogue retained : List Subject)
    (input : Subject → Input) (incumbent candidate : Subject)
    (valid : certifyReplacement k domain catalogue retained input incumbent candidate = true) :
    incumbent ∈ domain ∧ admitted k incumbent (input incumbent) = true ∧
      generatorFrontier k (fun x => x ∈ domain) input candidate ∧
      (∀ i, i ∈ List.range k.axes.length →
        cost k candidate (input candidate) i ≤ cost k incumbent (input incumbent) i) ∧
      (∃ i, i ∈ List.range k.axes.length ∧
        cost k candidate (input candidate) i < cost k incumbent (input incumbent) i) := by
  simp only [certifyReplacement, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at valid
  have replacement := (noRegression_exact k incumbent candidate input).mp valid.2.2.2.1
  have improvement := (FiniteFrontier.pareto_exact (List.range k.axes.length)
    (fun t => cost k t (input t)) candidate incumbent).mp valid.2.2.2.2
  exact ⟨valid.2.1, replacement.1,
    (certified_covered_frontier k domain catalogue retained input valid.1 candidate).mp valid.2.2.1,
    replacement.2.2, improvement.2⟩

-- A feasible-generator claim is stronger than an admitted-generator claim.
-- Feasibility is independently specified: missing receipts do not establish
-- infeasibility. Soundness AND completeness of qualification are required.
def feasibleFrontier (k : Contract) (generator feasible : Subject → Prop)
    (input : Subject → Input) (x : Subject) : Prop :=
  generator x ∧ feasible x ∧
    ∀ y, generator y → feasible y → dominates k input y x = false

theorem certified_feasible_generator_exact (k : Contract)
    (generator feasible : Subject → Prop) (catalogue retained : List Subject)
    (input : Subject → Input)
    (qualification : ∀ x, generator x → (admitted k x (input x) = true ↔ feasible x))
    (coverage : covers k generator catalogue input)
    (valid : certify k catalogue retained input = true) (x : Subject) :
    x ∈ retained ↔ feasibleFrontier k generator feasible input x := by
  have exact := certified_generator_exact k generator catalogue retained input coverage valid x
  constructor
  · intro hx
    obtain ⟨member, qualified, noneBetter⟩ := exact.mp hx
    exact ⟨member, (qualification x member).mp qualified,
      fun y hy feasibleY => noneBetter y hy ((qualification y hy).mpr feasibleY)⟩
  · rintro ⟨member, feasibleX, noneBetter⟩
    exact exact.mpr ⟨member, (qualification x member).mpr feasibleX,
      fun y hy qualified => noneBetter y hy ((qualification y hy).mp qualified)⟩

def checkQualification (k : Contract) (domain : List Subject)
    (feasible : Subject → Bool) (input : Subject → Input) : Bool :=
  domain.all (fun x => decide (admitted k x (input x) = feasible x))

theorem checkQualification_exact (k : Contract) (domain : List Subject)
    (feasible : Subject → Bool) (input : Subject → Input) :
    checkQualification k domain feasible input = true ↔
      ∀ x, x ∈ domain → (admitted k x (input x) = true ↔ feasible x = true) := by
  simp only [checkQualification, List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro same x hx
    rw [same x hx]
  · intro same x hx
    have agrees := same x hx
    cases qualified : admitted k x (input x) <;> cases possible : feasible x <;> simp_all

def certifyFeasible (k : Contract) (domain catalogue retained : List Subject)
    (feasible : Subject → Bool) (input : Subject → Input) : Bool :=
  certifyCovered k domain catalogue retained input &&
    checkQualification k domain feasible input

theorem certified_feasible_frontier (k : Contract)
    (domain catalogue retained : List Subject) (feasible : Subject → Bool)
    (input : Subject → Input)
    (valid : certifyFeasible k domain catalogue retained feasible input = true) (x : Subject) :
    x ∈ retained ↔ feasibleFrontier k (fun x => x ∈ domain) (fun x => feasible x = true) input x := by
  have checked : certifyCovered k domain catalogue retained input = true ∧
      checkQualification k domain feasible input = true := by
    simpa only [certifyFeasible, Bool.and_eq_true] using valid
  have covered := (certifyCovered_exact k domain catalogue retained input).mp checked.1
  exact certified_feasible_generator_exact k _ _ catalogue retained input
    ((checkQualification_exact k domain feasible input).mp checked.2) covered.2.1 covered.2.2 x

def certifyFeasibleReplacement (k : Contract) (domain catalogue retained : List Subject)
    (feasible : Subject → Bool) (input : Subject → Input) (incumbent candidate : Subject) : Bool :=
  certifyReplacement k domain catalogue retained input incumbent candidate &&
    checkQualification k domain feasible input

theorem certifyFeasibleReplacement_sound (k : Contract)
    (domain catalogue retained : List Subject) (feasible : Subject → Bool)
    (input : Subject → Input) (incumbent candidate : Subject)
    (valid : certifyFeasibleReplacement k domain catalogue retained feasible input incumbent candidate = true) :
    incumbent ∈ domain ∧ feasible incumbent = true ∧
      feasibleFrontier k (fun x => x ∈ domain) (fun x => feasible x = true) input candidate ∧
      (∀ i, i ∈ List.range k.axes.length →
        cost k candidate (input candidate) i ≤ cost k incumbent (input incumbent) i) ∧
      (∃ i, i ∈ List.range k.axes.length ∧
        cost k candidate (input candidate) i < cost k incumbent (input incumbent) i) := by
  have checked : certifyReplacement k domain catalogue retained input incumbent candidate = true ∧
      checkQualification k domain feasible input = true := by
    simpa only [certifyFeasibleReplacement, Bool.and_eq_true] using valid
  have qualified := (checkQualification_exact k domain feasible input).mp checked.2
  have replacement := certifyReplacement_sound k domain catalogue retained input incumbent candidate checked.1
  refine ⟨replacement.1, (qualified incumbent replacement.1).mp replacement.2.1,
    ?_, replacement.2.2.2⟩
  have selected := replacement.2.2.1
  exact ⟨selected.1, (qualified candidate selected.1).mp selected.2.1,
    fun y hy possible => selected.2.2 y hy ((qualified y hy).mpr possible)⟩

theorem incremental_generator_exact {A : Type}
    (old new : HypergraphIncremental.Hypergraph A) (k : Contract)
    (generator : Subject → Prop) (catalogue retained : List Subject)
    (project : (A → Prop) → Subject → Input)
    (coverage : covers k generator catalogue (project (HypergraphIncremental.incremental old new)))
    (valid : certify k catalogue retained (project (HypergraphIncremental.incremental old new)) = true)
    (x : Subject) :
    x ∈ retained ↔
      generatorFrontier k generator (project (HypergraphIncremental.derives new)) x := by
  have same : HypergraphIncremental.incremental old new = HypergraphIncremental.derives new := by
    funext a
    exact propext (HypergraphIncremental.incremental_exact old new a)
  rw [← same]
  exact certified_generator_exact k generator catalogue retained _ coverage valid x

theorem incremental_feasible_generator_exact {A : Type}
    (old new : HypergraphIncremental.Hypergraph A) (k : Contract)
    (generator feasible : Subject → Prop) (catalogue retained : List Subject)
    (project : (A → Prop) → Subject → Input)
    (qualification : ∀ x, generator x →
      (admitted k x (project (HypergraphIncremental.derives new) x) = true ↔ feasible x))
    (coverage : covers k generator catalogue (project (HypergraphIncremental.incremental old new)))
    (valid : certify k catalogue retained (project (HypergraphIncremental.incremental old new)) = true)
    (x : Subject) :
    x ∈ retained ↔ feasibleFrontier k generator feasible
      (project (HypergraphIncremental.derives new)) x := by
  have same : HypergraphIncremental.incremental old new = HypergraphIncremental.derives new := by
    funext a
    exact propext (HypergraphIncremental.incremental_exact old new a)
  rw [same] at coverage valid
  exact certified_feasible_generator_exact k generator feasible catalogue retained _
    qualification coverage valid x

-- Executable adapter to the existing bounded full-premise closure and scoped
-- certificate. Projection consumes exactly the computed membership predicate.
-- This is a reference checker, not a new worklist or a runtime speed claim.
def certifyClosed {A : Type} [DecidableEq A] (U B : List A)
    (rules : List (List A × A)) (k : Contract)
    (domain catalogue retained : List Subject)
    (project : (A → Bool) → Subject → Input) : Option Bool :=
  (ExecutableClosure.checkedClose U B rules).map (fun out =>
    certifyCovered k domain catalogue retained (project (fun a => decide (a ∈ out))))

theorem certifyClosed_exact {A : Type} [DecidableEq A] (old : HypergraphIncremental.Hypergraph A)
    (U B : List A) (rules : List (List A × A)) (k : Contract)
    (domain catalogue retained : List Subject) (project : (A → Bool) → Subject → Input)
    (valid : certifyClosed U B rules k domain catalogue retained project = some true) :
    ∃ out, ExecutableClosure.checkedClose U B rules = some out ∧ contractOK k = true ∧
      (∀ a, decide (a ∈ out) = true ↔ HypergraphIncremental.incremental old
        ⟨fun a => a ∈ B, fun ps a => (ps,a) ∈ rules⟩ a) ∧
      (∀ x, x ∈ retained ↔ generatorFrontier k (fun x => x ∈ domain)
        (project (fun a => decide (a ∈ out))) x) := by
  cases closed : ExecutableClosure.checkedClose U B rules with
  | none => simp [certifyClosed, closed] at valid
  | some out =>
    have certified : certifyCovered k domain catalogue retained
        (project (fun a => decide (a ∈ out))) = true := by
      simpa only [certifyClosed, closed, Option.map_some', Option.some.injEq] using valid
    have checked := (certifyCovered_exact k domain catalogue retained _).mp certified
    have derived := ExecutableClosure.checkedClose_admitted U B rules out closed
    refine ⟨out, rfl, checked.1, ?_, certified_covered_frontier k _ _ _ _ certified⟩
    intro a
    rw [decide_eq_true_eq]
    exact (derived.2.2 a).trans (HypergraphIncremental.incremental_exact old
      ⟨fun a => a ∈ B, fun ps a => (ps,a) ∈ rules⟩ a).symm

theorem certifyClosed_obligation_witness {A : Type} [DecidableEq A]
    (U B : List A) (rules : List (List A × A)) (k : Contract)
    (domain catalogue retained : List Subject) (project : (A → Bool) → Subject → Input)
    (valid : certifyClosed U B rules k domain catalogue retained project = some true)
    (x : Subject) (hx : x ∈ retained) (o : Obligation) (ho : o ∈ k.required) :
    ∃ out r, ExecutableClosure.checkedClose U B rules = some out ∧
      r ∈ (project (fun a => decide (a ∈ out)) x).receipts ∧
      r.scope = expectedScope k x o.metric ∧ r.round = o.round ∧ r.observedPass = true ∧
      ∃ v, r.elapsed = some v ∧ v ≤ o.limit := by
  cases closed : ExecutableClosure.checkedClose U B rules with
  | none => simp [certifyClosed, closed] at valid
  | some out =>
    have certified : certifyCovered k domain catalogue retained
        (project (fun a => decide (a ∈ out))) = true := by
      simpa only [certifyClosed, closed, Option.map_some', Option.some.injEq] using valid
    have checked := (certifyCovered_exact k domain catalogue retained _).mp certified
    obtain ⟨r, hr, hs, hd, hp, time⟩ := certified_obligation_witness
      k catalogue retained _ checked.2.2 x hx o ho
    exact ⟨out, r, rfl, hr, hs, hd, hp, time⟩

#print axioms dominates_trans
#print axioms certified_generator_exact
#print axioms checkCoverage_exact
#print axioms certifyCovered_exact
#print axioms certified_covered_frontier
#print axioms certifyReplacement_sound
#print axioms certified_feasible_generator_exact
#print axioms checkQualification_exact
#print axioms certified_feasible_frontier
#print axioms certifyFeasibleReplacement_sound
#print axioms incremental_generator_exact
#print axioms incremental_feasible_generator_exact
#print axioms certifyClosed_exact
#print axioms certifyClosed_obligation_witness

-- Synthetic controls; no physical measurement or universe-completeness claims.
def fixtureContract : Contract :=
  ⟨100, 6, 7, 20, 1, 1, [⟨10, 1⟩, ⟨11, 2⟩, ⟨12, 3⟩],
   [⟨10, 0, 10000⟩, ⟨11, 0, 10000⟩, ⟨12, 0, 10000⟩],
   [⟨10, 0, false⟩, ⟨11, 0, false⟩]⟩
def fixtureSubject (n : Nat) : Subject := ⟨n, n, 1⟩
def fixtureInput (s : Subject) (time space : Nat) : Input :=
  ⟨fixtureContract,
   [⟨s.artifact * 10, expectedScope fixtureContract s 10, 0, true, some time⟩,
    ⟨s.artifact * 10 + 1, expectedScope fixtureContract s 11, 0, true, some space⟩,
    ⟨s.artifact * 10 + 2, expectedScope fixtureContract s 12, 0, true, some 1⟩]⟩
def fixture (s : Subject) : Input :=
  if s.artifact = 0 then fixtureInput s 10 10
  else if s.artifact = 1 then fixtureInput s 5 15 else fixtureInput s 5 5

#guard admitted fixtureContract (fixtureSubject 0) (fixture (fixtureSubject 0))
#guard select fixtureContract ([0,1].map fixtureSubject) fixture == [0,1].map fixtureSubject
#guard !(noRegression fixtureContract (fixtureSubject 0) (fixtureSubject 1) fixture)
#guard select fixtureContract ([0,1,2,3].map fixtureSubject) fixture == [2,3].map fixtureSubject
#guard select fixtureContract ([3,1,2,0].map fixtureSubject) fixture == [3,2].map fixtureSubject
#guard noRegression fixtureContract (fixtureSubject 0) (fixtureSubject 2) fixture
def typedFixture : ComparisonContract.Contract :=
  ⟨[⟨10,1,.minimize,50⟩,⟨11,2,.minimize,50⟩],1001,1,2001⟩
#guard ComparisonContract.direct
  ⟨typedFixture,typedValues fixtureContract (fixtureSubject 2) (fixture (fixtureSubject 2))⟩
  ⟨typedFixture,typedValues fixtureContract (fixtureSubject 0) (fixture (fixtureSubject 0))⟩ == some true
#guard certify fixtureContract ([0,1,2,3].map fixtureSubject) ([2,3].map fixtureSubject) fixture
#guard !(certify fixtureContract ([0,1,2,3].map fixtureSubject) [fixtureSubject 2] fixture)

def milliseconds (s : Subject) : Input :=
  { fixtureInput s 1 5 with contract :=
    { fixtureContract with metrics := [⟨10,1000⟩,⟨11,2⟩,⟨12,3⟩] } }
def unitInputs (s : Subject) : Input :=
  if s.artifact = 4 then milliseconds s else fixtureInput s 500 5
#guard cost fixtureContract (fixtureSubject 4) (unitInputs (fixtureSubject 4)) 0 <
  cost fixtureContract (fixtureSubject 5) (unitInputs (fixtureSubject 5)) 0
#guard !(admitted fixtureContract (fixtureSubject 4) (milliseconds (fixtureSubject 4)))
#guard select fixtureContract ([4,5].map fixtureSubject) unitInputs == [fixtureSubject 5]
#guard !(certify fixtureContract ([4,5].map fixtureSubject) [fixtureSubject 4] unitInputs)

def omittedMetric (s : Subject) (metric : Nat) : Input :=
  let x := fixture s
  { x with receipts := x.receipts.filter (fun r => r.scope.metric != metric) }
#guard !(admitted fixtureContract (fixtureSubject 0) (omittedMetric (fixtureSubject 0) 11))
#guard !(admitted fixtureContract (fixtureSubject 0) (omittedMetric (fixtureSubject 0) 12))
def omittedObligation (s : Subject) : Input :=
  { omittedMetric s 12 with contract :=
    { fixtureContract with required := fixtureContract.required.filter (fun q => q.metric != 12) } }
#guard !(admitted fixtureContract (fixtureSubject 0) (omittedObligation (fixtureSubject 0)))

def raisedCap (s : Subject) : Input :=
  { fixtureInput s 10001 5 with contract :=
    { fixtureContract with required := fixtureContract.required.map (fun q => {q with limit := 20000}) } }
#guard !(admitted fixtureContract (fixtureSubject 0) (raisedCap (fixtureSubject 0)))
#guard !(admitted fixtureContract (fixtureSubject 0) (fixtureInput (fixtureSubject 0) 10001 5))

def changedScope (s : Subject) (change : Scope → Scope) : Input :=
  let x := fixture s
  { x with receipts := x.receipts.map (fun r => {r with scope := change r.scope}) }
#guard !(admitted fixtureContract (fixtureSubject 0)
  (changedScope (fixtureSubject 0) (fun s => {s with venue := 2})))
#guard !(admitted fixtureContract (fixtureSubject 0)
  (changedScope (fixtureSubject 0) (fun s => {s with harness := 2})))
#guard !(admitted fixtureContract (fixtureSubject 0)
  (changedScope (fixtureSubject 0) (fun s => {s with lineage := 2})))
#guard !(admitted fixtureContract (fixtureSubject 0)
  (changedScope (fixtureSubject 0) (fun s => {s with intent := 99})))
#guard !(admitted fixtureContract (fixtureSubject 0)
  (changedScope (fixtureSubject 0) (fun s => {s with policy := 99})))
#guard !(admitted fixtureContract (fixtureSubject 0) (fixture (fixtureSubject 1)))

def mixedSubject (s : Subject) : Input :=
  let x := fixture s
  { x with receipts := x.receipts.map (fun r =>
      if r.scope.metric = 11 then {r with scope := {r.scope with artifact := s.artifact + 1}} else r) }
#guard !(admitted fixtureContract (fixtureSubject 0) (mixedSubject (fixtureSubject 0)))

def duplicateReceipt (s : Subject) : Input :=
  let x := fixture s
  { x with receipts := x.receipts ++ x.receipts.take 1 }
#guard !(admitted fixtureContract (fixtureSubject 0) (duplicateReceipt (fixtureSubject 0)))

def failedCapability (s : Subject) : Input :=
  let x := fixture s
  { x with receipts := x.receipts.map (fun r => if r.scope.metric = 12 then {r with observedPass := false} else r) }
#guard !(admitted fixtureContract (fixtureSubject 2) (failedCapability (fixtureSubject 2)))

def maximizeContract : Contract :=
  {fixtureContract with axes := [⟨10,0,true⟩,⟨11,0,false⟩]}
def maximizeInput (s : Subject) : Input := {fixture s with contract := maximizeContract}
#guard cost maximizeContract (fixtureSubject 0) (maximizeInput (fixtureSubject 0)) 0 == -10
#guard !(admitted fixtureContract (fixtureSubject 0) (maximizeInput (fixtureSubject 0)))
def equalSpaceMaximize (s : Subject) : Input :=
  {fixtureInput s (if s.artifact = 0 then 10 else 5) 5 with contract := maximizeContract}
#guard select maximizeContract ([0,1].map fixtureSubject) equalSpaceMaximize == [fixtureSubject 0]
#guard !(admitted {fixtureContract with axes := []} (fixtureSubject 0) (fixture (fixtureSubject 0)))
#guard !(admitted {fixtureContract with axes := [⟨10,0,false⟩,⟨10,0,true⟩]}
  (fixtureSubject 0) (fixture (fixtureSubject 0)))

#print axioms expected_requirement_exact
#print axioms coordinate_exact
#print axioms admitted_exact
#print axioms admitted_obligation_witness
#print axioms admitted_coordinate_witness
#print axioms admitted_cost_witness
#print axioms typed_cost_agrees
#print axioms typed_dominance_agrees
#print axioms typed_direct_agrees
#print axioms wrong_metric_schema_rejected
#print axioms wrong_scope_rejected
#print axioms selected_exact
#print axioms certified_select_exact
#print axioms certified_retained_admitted
#print axioms certified_obligation_witness
#print axioms selected_has_no_qualified_dominator
#print axioms dominator_excludes
#print axioms selected_order_independent
#print axioms tied_member_retained
#print axioms noRegression_exact
#print axioms incremental_selection_exact
#print axioms admitted_provenance_selection_same
#print axioms replay_selection_idempotent
#print axioms merge_selection_order_independent
end ScopedFrontier
