import Std
import FiniteFrontier
namespace ComparisonContract

inductive Direction where
  | minimize | maximize
  deriving DecidableEq, Repr

-- IDs denote versioned canonical definitions, not display strings.
structure Axis where
  metric : Nat
  unit : Nat
  direction : Direction
  aggregation : Nat
  deriving DecidableEq, Repr

structure Contract where
  axes : List Axis
  workload : Nat
  venue : Nat
  epoch : Nat
  deriving DecidableEq, Repr

structure Raw where
  contract : Contract
  values : List Int
  deriving DecidableEq, Repr

def valid (c : Contract) (xs : List Int) : Prop := xs.length = c.axes.length
instance (c : Contract) (xs : List Int) : Decidable (valid c xs) := inferInstanceAs (Decidable (xs.length = c.axes.length))

structure Observation (c : Contract) where
  values : List Int
  shape : valid c values

def cost (c : Contract) (xs : List Int) (i : Nat) : Int :=
  let v := xs[i]?.getD 0
  match c.axes[i]? with
  | some axis => match axis.direction with
    | .minimize => v
    | .maximize => -v
  | none => 0

def dominates (c : Contract) (x y : List Int) : Bool :=
  FiniteFrontier.strictPareto (List.range c.axes.length) (fun xs => cost c xs) x y

-- None means incomparable/malformed, NOT a negative result on dominance.
-- Some false means a valid comparison did not establish strict dominance.
def direct (x y : Raw) : Option Bool :=
  if x.contract = y.contract ∧ valid x.contract x.values ∧ valid y.contract y.values
  then some (dominates x.contract x.values y.values)
  else none

theorem direct_compatible (x y : Raw) (b : Bool) (h : direct x y = some b) :
    x.contract = y.contract ∧ valid x.contract x.values ∧ valid y.contract y.values := by
  unfold direct at h
  split at h
  · assumption
  · contradiction

theorem mismatch_refused (x y : Raw) (h : x.contract ≠ y.contract) : direct x y = none := by
  simp [direct,h]

theorem malformed_refused (x y : Raw)
    (h : ¬ valid x.contract x.values ∨ ¬ valid y.contract y.values) : direct x y = none := by
  rcases h with h | h <;> simp [direct,h]

theorem dominance_exact (c : Contract) (x y : List Int) :
    dominates c x y = true ↔
      (∀ i, i ∈ List.range c.axes.length → cost c x i ≤ cost c y i) ∧
      (∃ i, i ∈ List.range c.axes.length ∧ cost c x i < cost c y i) :=
  FiniteFrontier.pareto_exact _ _ _ _

theorem direct_improvement (x y : Raw) (h : direct x y = some true) :
    x.contract = y.contract ∧ valid x.contract x.values ∧ valid y.contract y.values ∧
    (∀ i, i ∈ List.range x.contract.axes.length → cost x.contract x.values i ≤ cost x.contract y.values i) ∧
    (∃ i, i ∈ List.range x.contract.axes.length ∧ cost x.contract x.values i < cost x.contract y.values i) := by
  have hc := direct_compatible x y true h
  have hd : dominates x.contract x.values y.values = true := by
    simpa only [direct, if_pos hc, Option.some.injEq] using h
  exact ⟨hc.1,hc.2.1,hc.2.2,(dominance_exact _ _ _).mp hd⟩

-- An explicit proof-carrying transport into a common comparison contract.
-- 'meaning' is fixed by the application. The semantic relation is a premise,
-- not derived from matching numeric samples or a Boolean certification flag.
structure Transport {Meaning : Type} (meaning : Contract → List Int → Meaning)
    (source target : Contract) where
  convert : List Int → List Int
  shape : ∀ xs, valid source xs → valid target (convert xs)
  preserves : ∀ xs, valid source xs → meaning source xs = meaning target (convert xs)

def Transport.apply {M : Type} {meaning : Contract → List Int → M} {s t : Contract}
    (proof : Transport meaning s t) (x : Observation s) : Observation t :=
  ⟨proof.convert x.values, proof.shape x.values x.shape⟩

def Transport.identity {M : Type} (meaning : Contract → List Int → M) (c : Contract) : Transport meaning c c where
  convert xs := xs
  shape _ h := h
  preserves _ _ := rfl

def Transport.compose {M : Type} {meaning : Contract → List Int → M} {s t u : Contract}
    (first : Transport meaning s t) (second : Transport meaning t u) : Transport meaning s u where
  convert xs := second.convert (first.convert xs)
  shape xs h := second.shape _ (first.shape xs h)
  preserves xs h := (first.preserves xs h).trans (second.preserves _ (first.shape xs h))

theorem transported_meaning {M : Type} {meaning : Contract → List Int → M} {s t : Contract}
    (proof : Transport meaning s t) (x : Observation s) :
    meaning s x.values = meaning t (proof.apply x).values := proof.preserves _ x.shape

def compareVia {M : Type} {meaning : Contract → List Int → M} {sx sy target : Contract}
    (px : Transport meaning sx target) (py : Transport meaning sy target)
    (x : Observation sx) (y : Observation sy) : Bool :=
  dominates target (px.apply x).values (py.apply y).values

theorem compareVia_exact {M : Type} {meaning : Contract → List Int → M} {sx sy target : Contract}
    (px : Transport meaning sx target) (py : Transport meaning sy target)
    (x : Observation sx) (y : Observation sy) :
    compareVia px py x y = true ↔
    (∀ i, i ∈ List.range target.axes.length →
      cost target (px.apply x).values i ≤ cost target (py.apply y).values i) ∧
    (∃ i, i ∈ List.range target.axes.length ∧
      cost target (px.apply x).values i < cost target (py.apply y).values i) :=
  dominance_exact _ _ _

-- If the target metric interpretation is sound for an application relation,
-- composed comparison transports that relation back to the source meanings.
-- This premise is necessary: matching numbers alone cannot validate a metric.
theorem compareVia_semantic {M : Type} {meaning : Contract → List Int → M}
    {sx sy target : Contract} (better : M → M → Prop)
    (metricSound : ∀ a b, valid target a → valid target b →
      dominates target a b = true → better (meaning target a) (meaning target b))
    (px : Transport meaning sx target) (py : Transport meaning sy target)
    (x : Observation sx) (y : Observation sy) (h : compareVia px py x y = true) :
    better (meaning sx x.values) (meaning sy y.values) := by
  have hb := metricSound (px.apply x).values (py.apply y).values
    (px.apply x).shape (py.apply y).shape h
  rw [← transported_meaning px x, ← transported_meaning py y] at hb
  exact hb

#print axioms compareVia_semantic
#print axioms direct_improvement
#print axioms mismatch_refused
#print axioms transported_meaning
#print axioms compareVia_exact
end ComparisonContract
