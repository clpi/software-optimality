import ExecutableClosure
import Std
namespace MetricRelevance

-- Separate coordinates, never a weighted or implicitly aggregated quality score.
abbrev Value := Nat → Nat → Int -- state -> metric -> value
abbrev Intent := Nat → Nat → Bool -- state -> intent part -> satisfaction

def changedOnly (metrics chosen : List Nat) (value : Value) (before after : Nat) : Bool :=
  metrics.all (fun m => chosen.contains m || decide (value before m = value after m))

theorem changedOnly_exact (metrics chosen : List Nat) (value : Value) (before after : Nat) :
    changedOnly metrics chosen value before after = true ↔
      ∀ m, m ∈ metrics → m ∈ chosen ∨ value before m = value after m := by
  simp [changedOnly,List.all_eq_true]

-- Direct relevance means a single-coordinate contrast in the named deterministic model.
def direct (metrics : List Nat) (value : Value) (intent : Intent)
    (metric part before after : Nat) : Bool :=
  metrics.contains metric && changedOnly metrics [metric] value before after &&
  decide (value before metric ≠ value after metric) &&
  decide (intent before part ≠ intent after part)

theorem direct_exact (metrics : List Nat) (value : Value) (intent : Intent)
    (metric part before after : Nat) :
    direct metrics value intent metric part before after = true ↔
      metric ∈ metrics ∧
      (∀ m, m ∈ metrics → m ∈ [metric] ∨ value before m = value after m) ∧
      value before metric ≠ value after metric ∧ intent before part ≠ intent after part := by
  simp only [direct,Bool.and_eq_true,List.contains_iff,changedOnly_exact,decide_eq_true_eq,and_assoc]

-- Minimal multi-coordinate effect relative to all states in the named model.
def composition (states metrics group : List Nat) (value : Value) (intent : Intent)
    (part before after : Nat) : Bool :=
  decide (group.Nodup) && decide (2 ≤ group.length) &&
  group.all (fun m => metrics.contains m) &&
  states.contains before && states.contains after &&
  changedOnly metrics group value before after &&
  decide (intent before part ≠ intent after part) &&
  (ExecutableClosure.subsets group).all (fun sub =>
    if sub.length < group.length then
      !(states.any (fun alternative => changedOnly metrics sub value before alternative &&
        decide (intent before part ≠ intent alternative part)))
    else true)

-- The irreducibility claim is exactly a finite search over proper subgroups and states.
theorem composition_irreducible (states metrics group : List Nat) (value : Value)
    (intent : Intent) (part before after : Nat)
    (h : composition states metrics group value intent part before after = true) :
    ∀ sub, sub ∈ ExecutableClosure.subsets group → sub.length < group.length →
      ∀ alternative, alternative ∈ states →
        changedOnly metrics sub value before alternative = true →
        intent before part = intent alternative part := by
  simp only [composition,Bool.and_eq_true] at h
  have hp := (List.all_eq_true.mp h.2)
  intro sub hs hlen alt ha hc
  have hh := hp sub hs
  simp [hlen] at hh
  exact hh alt ha hc


-- Controlled comparisons are labelled separately from uncontrolled observations.
structure Counterfactual where
  id : Nat
  beforeScope : Nat
  afterScope : Nat
  beforeContext : Nat
  afterContext : Nat
  mutationAdmitted : Bool
  beforeValue : Int
  afterValue : Int
  deriving DecidableEq, Repr

def admittedSensitivity (c : Counterfactual) : Bool :=
  decide (c.beforeScope = c.afterScope) &&
  decide (c.beforeContext = c.afterContext) &&
  c.mutationAdmitted && decide (c.beforeValue ≠ c.afterValue)

theorem admittedSensitivity_exact (c : Counterfactual) :
    admittedSensitivity c = true ↔
      c.beforeScope = c.afterScope ∧ c.beforeContext = c.afterContext ∧
      c.mutationAdmitted = true ∧ c.beforeValue ≠ c.afterValue := by
  simp only [admittedSensitivity,Bool.and_eq_true,decide_eq_true_eq,and_assoc]

-- Exact unreduced rational representation. None means no observations, NOT zero rate.
structure Fraction where
  numerator : Nat
  denominator : Nat
  deriving DecidableEq, Repr

def exactRate (events : List Bool) : Option Fraction :=
  if events.length = 0 then none else some ⟨events.count true,events.length⟩

theorem exactRate_spec (events : List Bool) (f : Fraction)
    (h : exactRate events = some f) :
    f.numerator = events.count true ∧ f.denominator = events.length ∧
      0 < f.denominator ∧ f.numerator ≤ f.denominator := by
  unfold exactRate at h
  split at h
  next hz => contradiction
  next hn =>
    have hf := Option.some.inj h
    cases hf
    exact ⟨rfl,rfl,Nat.pos_of_ne_zero hn,List.count_le_length⟩

-- Flakiness is exact failure count plus evidence of both outcomes, at one scope.
structure Observation where
  id : Nat
  scope : Nat
  passed : Bool
  deriving DecidableEq, Repr

def observedFailureRate (scope : Nat) (observations : List Observation) : Option Fraction :=
  let selected := observations.filter (fun o => decide (o.scope = scope))
  if (selected.map Observation.id).Nodup then
    exactRate (selected.map (fun o => !o.passed))
  else none

def observedMixed (scope : Nat) (observations : List Observation) : Option Bool :=
  let selected := observations.filter (fun o => decide (o.scope = scope))
  if (selected.map Observation.id).Nodup ∧ 0 < selected.length then
    some (selected.any Observation.passed && selected.any (fun o => !o.passed))
  else none


theorem observedFailureRate_spec (scope : Nat) (observations : List Observation) (f : Fraction)
    (h : observedFailureRate scope observations = some f) :
    let selected := observations.filter (fun o => decide (o.scope = scope))
    (selected.map Observation.id).Nodup ∧
    f.numerator = (selected.map (fun o => !o.passed)).count true ∧
    f.denominator = selected.length ∧ 0 < f.denominator ∧ f.numerator ≤ f.denominator := by
  unfold observedFailureRate at h
  dsimp only at h ⊢
  split at h
  next hn =>
    obtain ⟨ha,hb,hc,hd⟩ := exactRate_spec _ f h
    exact ⟨hn,ha,by simpa using hb,hc,hd⟩
  next hn => contradiction

theorem exactRate_permutation (xs ys : List Bool) (h : xs.Perm ys) :
    exactRate xs = exactRate ys := by
  simp only [exactRate,h.length_eq,h.count_eq true]

theorem observedFailureRate_permutation (scope : Nat) (xs ys : List Observation)
    (h : xs.Perm ys) : observedFailureRate scope xs = observedFailureRate scope ys := by
  have hp := h.filter (fun o => decide (o.scope = scope))
  have hi := hp.map Observation.id
  have ho := hp.map (fun o => !o.passed)
  simp only [observedFailureRate]
  simp only [hi.nodup_iff,exactRate_permutation _ _ ho]

-- Conditional denominator contains only admitted comparisons with matching context.
def controlled (c : Counterfactual) : Bool :=
  decide (c.beforeScope = c.afterScope ∧ c.beforeContext = c.afterContext) && c.mutationAdmitted

def indirectRate (scope context : Nat) (comparisons : List Counterfactual) : Option Fraction :=
  let selected := comparisons.filter (fun c => decide
    (c.beforeScope = scope ∧ c.afterScope = scope ∧
     c.beforeContext = context ∧ c.afterContext = context))
  if (selected.map Counterfactual.id).Nodup then
    exactRate ((selected.filter (fun c => c.mutationAdmitted)).map
      (fun c => decide (c.beforeValue ≠ c.afterValue)))
  else none

theorem indirectRate_spec (scope context : Nat) (comparisons : List Counterfactual) (f : Fraction)
    (h : indirectRate scope context comparisons = some f) :
    let selected := comparisons.filter (fun c => decide
      (c.beforeScope = scope ∧ c.afterScope = scope ∧
       c.beforeContext = context ∧ c.afterContext = context))
    let admitted := selected.filter (fun c => c.mutationAdmitted)
    (selected.map Counterfactual.id).Nodup ∧
      f.numerator = (admitted.map (fun c => decide (c.beforeValue ≠ c.afterValue))).count true ∧
      f.denominator = admitted.length ∧ 0 < f.denominator ∧ f.numerator ≤ f.denominator := by
  unfold indirectRate at h
  dsimp only at h ⊢
  split at h
  next hn =>
    obtain ⟨ha,hb,hc,hd⟩ := exactRate_spec _ f h
    exact ⟨hn,ha,by simpa using hb,hc,hd⟩
  next hn => contradiction

-- Unordered distinct-index pairs count each comparison once.
def disagreementRate (events : List Bool) : Option Fraction :=
  exactRate ((List.range events.length).flatMap (fun i =>
    (List.range i).map (fun j => decide (events.getD i false ≠ events.getD j false))))

def observedDisagreement (scope : Nat) (observations : List Observation) : Option Fraction :=
  let selected := observations.filter (fun o => decide (o.scope = scope))
  if (selected.map Observation.id).Nodup then disagreementRate (selected.map Observation.passed)
  else none

-- Keep every intent part and attribution coordinate separate. No scalar weighting.
structure RelevanceProfile where
  directByPart : List (Nat × Option Fraction)
  composedByPart : List (Nat × Option Fraction)
  indirect : Option Fraction
  observedFailure : Option Fraction
  observedDisagreement : Option Fraction
  observedMixedOutcomes : Option Bool
  deriving DecidableEq, Repr

def partRates (parts : List Nat) (pairs : List (Nat × Nat))
    (admissible changes : Nat → Nat → Nat → Bool) : List (Nat × Option Fraction) :=
  parts.map (fun part => (part,exactRate ((pairs.eraseDups.filter
    (fun p => admissible part p.1 p.2)).map (fun p => changes part p.1 p.2))))

def buildProfile (parts : List Nat) (pairs : List (Nat × Nat))
    (admissible directChange composedChange : Nat → Nat → Nat → Bool)
    (scope context : Nat) (comparisons : List Counterfactual)
    (observations : List Observation) : RelevanceProfile :=
  ⟨partRates parts pairs admissible directChange,
   partRates parts pairs admissible composedChange,
   indirectRate scope context comparisons,
   observedFailureRate scope observations,observedDisagreement scope observations,
   observedMixed scope observations⟩

-- A second synthetic fixture: intent = (latency<=10 AND correct) OR fallback.
-- Named contexts exhaust the four (correct,fallback) valuations.
def contexts : List (Bool × Bool) := [(false,false),(false,true),(true,false),(true,true)]
def latencyClause (latency : Nat) := decide (latency ≤ 10)
def rootIntent (latency : Nat) (context : Bool × Bool) :=
  (latencyClause latency && context.1) || context.2

theorem direct_leaf_rate : exactRate (contexts.map (fun _ =>
    decide (latencyClause 8 ≠ latencyClause 12))) = some ⟨4,4⟩ := by decide
theorem composed_root_pivotal_rate : exactRate (contexts.map (fun c =>
    decide (rootIntent 8 c ≠ rootIntent 12 c))) = some ⟨1,4⟩ := by decide

-- Shared-dependency fixture: equal-count named contexts, NOT preference weights.
def sharedRoot (m : Bool) (context : Bool × Bool) := m && (context.1 || context.2)

theorem shared_factorization (m a b : Bool) :
    ((m && a) || (m && b)) = (m && (a || b)) := by
  cases m <;> cases a <;> cases b <;> decide

theorem shared_dependency_pivotal_rate : exactRate (contexts.map (fun c =>
    decide (sharedRoot false c ≠ sharedRoot true c))) = some ⟨3,4⟩ := by decide

-- SYNTHETIC model fixture: four Boolean configurations, two metrics, two intent parts.
-- Part0 requires both metrics=1; part1 requires metric0=1.
def fixtureStates := [0,1,2,3]
def fixtureValue (s m : Nat) : Int :=
  if m = 0 then Int.ofNat (s % 2) else Int.ofNat (s / 2)
def fixtureIntent (s p : Nat) : Bool :=
  if p = 0 then decide (fixtureValue s 0 = 1 ∧ fixtureValue s 1 = 1)
  else decide (fixtureValue s 0 = 1)

theorem fixture_direct : direct [0,1] fixtureValue fixtureIntent 0 1 0 1 = true := by decide
theorem fixture_composition : composition fixtureStates [0,1] [0,1]
    fixtureValue fixtureIntent 0 0 3 = true := by decide

def fixtureObservations : List Observation :=
  [⟨1,7,true⟩,⟨2,7,false⟩,⟨3,7,true⟩,⟨4,7,false⟩,⟨5,7,true⟩,⟨6,8,false⟩]
theorem fixture_failure_rate : observedFailureRate 7 fixtureObservations = some ⟨2,5⟩ := by decide
theorem fixture_mixed : observedMixed 7 fixtureObservations = some true := by decide
theorem fixture_missing : observedFailureRate 9 fixtureObservations = none := by decide
theorem fixture_duplicate_rejected : observedFailureRate 7 [⟨1,7,true⟩,⟨1,7,false⟩] = none := by decide

theorem fixture_controlled : admittedSensitivity ⟨1,7,7,10,10,true,100,90⟩ = true := by decide
theorem fixture_confounded_rejected : admittedSensitivity ⟨1,7,7,10,11,true,100,90⟩ = false := by decide

def fixtureComparisons : List Counterfactual :=
  [⟨1,7,7,10,10,true,100,90⟩,⟨2,7,7,10,10,true,100,100⟩,
   ⟨3,7,7,10,11,true,100,80⟩,⟨4,7,7,10,10,false,100,80⟩]
theorem fixture_indirect_rate : indirectRate 7 10 fixtureComparisons = some ⟨1,2⟩ := by decide

def fixtureProfile : RelevanceProfile :=
  ⟨[(0,exactRate (contexts.map (fun _ => decide (latencyClause 8 ≠ latencyClause 12))))],
   [(0,exactRate (contexts.map (fun c => decide (rootIntent 8 c ≠ rootIntent 12 c))))],
   indirectRate 7 10 fixtureComparisons,observedFailureRate 7 fixtureObservations,
   observedDisagreement 7 fixtureObservations,observedMixed 7 fixtureObservations⟩

theorem fixture_profile_exact : fixtureProfile =
    ⟨[(0,some ⟨4,4⟩)],[(0,some ⟨1,4⟩)],some ⟨1,2⟩,some ⟨2,5⟩,some ⟨6,10⟩,some true⟩ := by decide

theorem fixture_disagreement : observedDisagreement 7 fixtureObservations = some ⟨6,10⟩ := by decide
#guard disagreementRate [] == none
#guard disagreementRate [true] == none
#guard observedDisagreement 7 [⟨1,7,true⟩,⟨1,7,false⟩] == none

-- Rational equality is exact cross multiplication with nonzero denominators.
def fractionEqual (a b : Fraction) : Bool :=
  decide (0 < a.denominator ∧ 0 < b.denominator ∧
    a.numerator * b.denominator = b.numerator * a.denominator)

theorem fractionEqual_exact (a b : Fraction) : fractionEqual a b = true ↔
    0 < a.denominator ∧ 0 < b.denominator ∧
      a.numerator * b.denominator = b.numerator * a.denominator := by
  simp only [fractionEqual,decide_eq_true_eq]
#guard fractionEqual ⟨4,4⟩ ⟨1,1⟩ == true
#guard fractionEqual ⟨0,0⟩ ⟨0,1⟩ == false

-- Regression guards for scope mixing, duplicated identity, and denominator contamination.
#guard indirectRate 7 10 [⟨1,7,7,10,10,true,100,90⟩,⟨2,8,8,10,10,true,100,100⟩] = some ⟨1,1⟩
#guard indirectRate 7 10 [⟨1,7,7,10,10,true,100,90⟩,⟨1,7,7,10,10,true,100,100⟩] = none
#guard observedMixed 7 [⟨1,7,true⟩,⟨1,7,false⟩] = none
#guard observedMixed 7 [] = none
#guard partRates [0] [(0,1),(0,1),(0,2)] (fun _ _ after => decide (after = 1))
    (fun _ _ _ => true) = [(0,some ⟨1,1⟩)]
#print axioms shared_factorization
#print axioms shared_dependency_pivotal_rate
#print axioms indirectRate_spec
#print axioms exactRate_permutation
#print axioms observedFailureRate_permutation
#print axioms fixture_disagreement
#print axioms fractionEqual_exact
#print axioms fixture_profile_exact
#print axioms fixture_indirect_rate
#print axioms observedFailureRate_spec
#print axioms direct_leaf_rate
#print axioms composed_root_pivotal_rate
#print axioms direct_exact
#print axioms composition_irreducible
#print axioms admittedSensitivity_exact
#print axioms exactRate_spec
#print axioms fixture_direct
#print axioms fixture_composition
#print axioms fixture_failure_rate
#print axioms fixture_controlled
#print axioms fixture_confounded_rejected
end MetricRelevance
