import composition.QualifiedClosure
import SoftwareIsQuantifiable.Coverage
import SoftwareIsQuantifiable.Pareto
import ScopedFrontier
import FrontierComposition

namespace QualifiedSelection
open SoftwareIsQuantifiable

abbrev Contract := ScopedFrontier.Contract
abbrev Subject := ScopedFrontier.Subject
abbrev Obligation := ScopedFrontier.Obligation
abbrev scope := ScopedFrontier.expectedScope
abbrev policy := ScopedFrontier.expectedPolicy

variable {C F : Type} [DecidableEq F]

structure Campaign (C F : Type) where
  contract : Contract
  subject : C → Subject
  inputs : C → ScopedFrontier.Input
  execution : ScopedEvidence.Receipt → Coverage.Execution
  ledger : List Coverage.Witness
  valid : Coverage.Witness → Bool
  behaviors : List F
  supports : C → F → F
  refutes : C → F → F

def Campaign.receipts (data : Campaign C F) (c : C) := (data.inputs c).receipts

def Campaign.requires (data : Campaign C F) (c : C) := data.behaviors.map (data.supports c)
def Campaign.excludes (data : Campaign C F) (c : C) := data.behaviors.map (data.refutes c)

def axes (k : Contract) := k.axes.map ScopedFrontier.Axis.metric

/-- Peak comparison is an explicit adapter of the canonical round contract.
    Every selected metric must minimize and select every required round of
    that metric. Hard qualification-only metrics remain outside the objective. -/
def peakPolicy (k : Contract) : Bool :=
  k.axes.all (fun a => !a.maximize) && k.required.all (fun q =>
    decide (q.metric ∉ axes k) || k.axes.any (fun a => decide (a.metric = q.metric ∧ a.round = q.round)))

/-- Every admitted candidate supplies a measured value for every named axis.
    Each metric uses the maximum of its recorded round values in its own units. -/
def peak (data : Campaign C F) (c : C) (axis : Nat) : Int :=
  Int.ofNat (((data.receipts c).filterMap (fun r =>
    if r.scope.metric = axis then r.elapsed else none)).foldl max 0)

private theorem max_bounded (xs : List Nat) (seed limit : Nat) :
    xs.foldl max seed ≤ limit ↔ seed ≤ limit ∧ ∀ x ∈ xs, x ≤ limit := by
  induction xs generalizing seed with
  | nil => simp
  | cons a xs ih => simp [List.foldl, ih, Nat.max_le, and_assoc]

omit [DecidableEq F] in
/-- The aggregate upper bound is equivalent to bounding every present
    measurement of this metric. Admission supplies presence independently. -/
theorem peak_le_iff (data : Campaign C F) (c : C) (i limit : Nat) :
    peak data c i ≤ Int.ofNat limit ↔ ∀ r ∈ data.receipts c,
      r.scope.metric = i → ∀ t, r.elapsed = some t → t ≤ limit := by
  unfold peak
  have cast (x y : Nat) : Int.ofNat x ≤ Int.ofNat y ↔ x ≤ y := Int.ofNat_le
  rw [cast, max_bounded]
  simp only [Nat.zero_le, true_and]
  constructor
  · intro h r hr hi t ht
    apply h t
    exact List.mem_filterMap.mpr ⟨r, hr, by simp [hi, ht]⟩
  · intro h t ht
    obtain ⟨r, hr, hv⟩ := List.mem_filterMap.mp ht
    split at hv
    · rename_i hi
      exact h r hr hi t hv
    · contradiction

def gate (data : Campaign C F) (facts : List F) (c : C) : Bool :=
  let records := data.receipts c
  (peakPolicy data.contract && ScopedFrontier.admitted data.contract (data.subject c) (data.inputs c)) &&
  records.all (fun r => Coverage.recorded data.valid data.ledger (data.execution r)) &&
  decide ((records.map (fun r => ((data.execution r).id, r.scope.metric))).Nodup) &&
  Pareto.noQualifiedBehaviorLost ⟨data.requires c⟩ ⟨facts⟩ &&
  (data.excludes c).all (fun f => decide (f ∉ facts))

def admitted (data : Campaign C F) (facts : List F) (inc c : C) : Bool :=
  gate data facts c && (axes data.contract).all (fun i => decide (peak data c i ≤ peak data inc i))

/-- none means invalid closure input or an unqualified comparison baseline.
    some [] is a valid comparison with no admissible catalogue entries. -/
def select (data : Campaign C F) (u roots : List F) (rules : QualifiedClosure.Rules F)
    (catalogue : List C) (inc : C) : Option (List C) := do
  let facts ← QualifiedClosure.checked u roots rules
  if gate data facts inc then
    return FiniteFrontier.frontier (catalogue.filter (admitted data facts inc))
      (FiniteFrontier.strictPareto (axes data.contract) (peak data))
  else none

theorem gate_exact (data : Campaign C F) (facts : List F) (c : C) :
    gate data facts c = true ↔
      peakPolicy data.contract = true ∧ ScopedFrontier.admitted data.contract (data.subject c) (data.inputs c) = true ∧
      (∀ r ∈ data.receipts c, ∃ w ∈ data.ledger,
        data.valid w = true ∧ Coverage.Witnessed (data.execution r) w) ∧
      ((data.receipts c).map (fun r => ((data.execution r).id, r.scope.metric))).Nodup ∧
      (∀ f ∈ data.requires c, f ∈ facts) ∧ (∀ f ∈ data.excludes c, f ∉ facts) := by
  simp only [gate, Bool.and_eq_true, List.all_eq_true, Coverage.recorded_exact,
    decide_eq_true_eq, Pareto.noQualifiedBehaviorLost_iff, and_assoc]

/-- A timed requirement yields both a scoped receipt and an accepted witness
    from the supplied ledger for that receipt's mapped execution. -/
theorem observation (data : Campaign C F) (facts : List F) (c : C)
    (ok : gate data facts c = true) (q : Obligation) (hq : q ∈ data.contract.required) :
    ∃ r ∈ data.receipts c, r.scope = scope data.contract (data.subject c) q.metric ∧
      r.round = q.round ∧ r.observedPass = true ∧
      (∃ t, r.elapsed = some t ∧ t ≤ q.limit) ∧
      ∃ w ∈ data.ledger, data.valid w = true ∧ Coverage.Witnessed (data.execution r) w := by
  obtain ⟨_, admittedScope, recorded, _⟩ := (gate_exact data facts c).mp ok
  obtain ⟨r, hm, hs, hr, hp, ht⟩ :=
    ScopedFrontier.admitted_obligation_witness _ _ _ admittedScope q hq
  exact ⟨r, hm, hs, hr, hp, ht, recorded r hm⟩

theorem selection_exact (data : Campaign C F) (u roots : List F)
    (rules : QualifiedClosure.Rules F) (catalogue out : List C) (inc c : C)
    (success : select data u roots rules catalogue inc = some out) :
    ∃ facts, QualifiedClosure.checked u roots rules = some facts ∧ gate data facts inc = true ∧
      (c ∈ out ↔ (c ∈ catalogue ∧ admitted data facts inc c = true) ∧
        ∀ z, z ∈ catalogue → admitted data facts inc z = true →
          FiniteFrontier.strictPareto (axes data.contract) (peak data) z c = false) := by
  cases hc : QualifiedClosure.checked u roots rules with
  | none => simp [select, hc] at success
  | some facts =>
    cases hi : gate data facts inc with
    | false => simp [select, hc, hi] at success
    | true =>
      simp [select, hc, hi] at success
      subst out
      refine ⟨facts, rfl, hi, ?_⟩
      simp [FiniteFrontier.frontier_exact, List.mem_filter]

/-- The two proof developments meet at the selected candidate. Every required
    fact is rooted in the new graph, each excluded fact is absent, and no policy
    metric regresses relative to the qualified incumbent. -/
theorem release_evidence (data : Campaign C F) (u roots : List F)
    (rules : QualifiedClosure.Rules F) (old : HypergraphIncremental.Hypergraph F)
    (catalogue out : List C) (inc c : C)
    (success : select data u roots rules catalogue inc = some out) (hc : c ∈ out) :
    (∀ f ∈ data.requires c, HypergraphIncremental.incremental old (QualifiedClosure.graph roots rules) f) ∧
    (∀ f ∈ data.excludes c, ¬ HypergraphIncremental.incremental old (QualifiedClosure.graph roots rules) f) ∧
    (∀ i ∈ axes data.contract, peak data c i ≤ peak data inc i) ∧
    ∀ q ∈ data.contract.required,
      ∃ r ∈ data.receipts c, r.scope = scope data.contract (data.subject c) q.metric ∧
        r.round = q.round ∧ r.observedPass = true ∧
        (∃ t, r.elapsed = some t ∧ t ≤ q.limit) ∧
        ∃ w ∈ data.ledger, data.valid w = true ∧ Coverage.Witnessed (data.execution r) w := by
  obtain ⟨facts, hf, _, hex⟩ := selection_exact data u roots rules catalogue out inc c success
  have ha := (hex.mp hc).1.2
  simp only [admitted, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at ha
  obtain ⟨_, _, _, _, hp, hn⟩ := (gate_exact data facts c).mp ha.1
  have eqv := fun f => (QualifiedClosure.checked_exact u roots rules facts hf old f).1
  exact ⟨fun f h => (eqv f).mp (hp f h), fun f h hi => hn f h ((eqv f).mpr hi),
    ha.2, observation data facts c ha.1⟩

/-- Shards may be ranked independently after admission under this same
    contract. Taking their union and ranking again preserves every identity. -/
theorem selected_partition (data : Campaign C F) (facts : List F) (inc : C)
    (left right : List C) (c : C) :
    let focus := fun xs : List C => xs.filter (admitted data facts inc)
    let d := FiniteFrontier.strictPareto (axes data.contract) (peak data)
    c ∈ FiniteFrontier.frontier (focus (left ++ right)) d ↔
      c ∈ FiniteFrontier.frontier
        (FiniteFrontier.frontier (focus left) d ++ FiniteFrontier.frontier (focus right) d) d := by
  dsimp only
  rw [List.filter_append]
  exact FrontierComposition.partition_exact (FiniteFrontier.strictPareto (axes data.contract) (peak data)) (FrontierComposition.pareto_transitive (axes data.contract) (peak data))
    (FrontierComposition.pareto_irreflexive (axes data.contract) (peak data)) _ _ _

#print axioms selected_partition
#print axioms gate_exact
#print axioms peak_le_iff
#print axioms observation
#print axioms selection_exact
#print axioms release_evidence
end QualifiedSelection
