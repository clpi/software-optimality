import Composition
import Std

/- Stable import surface for downstream proofs.

   Import this module. The public names live in the `Optimality` namespace,
   including the closure and composition theorems defined in `Composition.lean`.

   Correspondence with `clpi/software-is-quantifiable` (public Lean 4):

   * `Optimality.closure` and `Optimality.HornDeriv` correspond to
     `SoftwareIsQuantifiable.Coloring.Deriv`. `hornDeriv_iff_closure` is the
     equivalence. `closure_operator_exact` corresponds to
     `SoftwareIsQuantifiable.Coloring.coloring`: both compute that derivability
     relation once every rule head lies in the named snapshot universe.
   * `Optimality.dominates`, `paretoMaximal`, `paretoMaximal_nonempty`, and
     `paretoMaximal_not_dominated` correspond to
     `SoftwareIsQuantifiable.Pareto.dominates`, `frontier_nonempty`, and
     `frontier_not_dominated`, specialized to the same two `Nat` axes.
   * `Optimality.noWorse`, `guardedMaximal`, and `guardedMaximal_sound`
     correspond to `SoftwareIsQuantifiable.Pareto.noWorse`, `admitted`, and
     `admitted_frontier_sound`.
   * `Optimality.paretoMaximal_can_regress` corresponds to
     `SoftwareIsQuantifiable.Pareto.frontier_can_regress`.
   * `Optimality.not_per_execution_dominance` corresponds to
     `SoftwareIsQuantifiable.Pareto.not_per_execution_dominance`.
   * Behavior retention and the release gate are
     `SoftwareIsQuantifiable.Pareto.noQualifiedBehaviorLost` and
     `SoftwareIsQuantifiable.Pareto.acceptsRelease`. This module does not
     restate them.
   * `Optimality.GeneratorCoverage` does not correspond to
     `SoftwareIsQuantifiable.Coverage.PlatformPremise`. Platform mediation is
     not assumed. Generator coverage is a separate named premise for transferring
     a catalogue frontier to an intended alternative set.
   * `SoftwareIsQuantifiable.Fold.join` is root-set union before rules fire.
     `closure_compound` keeps cross-source consequences and is not that join.
     `Finiteness` is inherited: every frontier here is a sublist of a supplied
     finite candidate list.

   This module does not prove incremental release monotonicity, incremental
   safety, or that a release process never regresses. Those are obligations of
   the downstream repositories, which may import the theorems below.
-/
namespace Optimality

/-- Two-axis cost point. Same carrier as `SoftwareIsQuantifiable.Pareto.Point`:
    time and compute, both `Nat`. -/
abbrev Point := Nat × Nat

/-- Same predicate as `SoftwareIsQuantifiable.Pareto.dominates`. -/
def dominates (a b : Point) : Prop :=
  a.1 ≤ b.1 ∧ a.2 ≤ b.2 ∧ (a.1 < b.1 ∨ a.2 < b.2)

theorem dominates_trans {a b c : Point} (hab : dominates a b) (hbc : dominates b c) :
    dominates a c := by
  obtain ⟨h1, h2, h3⟩ := hab
  obtain ⟨h4, h5, h6⟩ := hbc
  refine ⟨Nat.le_trans h1 h4, Nat.le_trans h2 h5, ?_⟩
  rcases h3 with h | h
  · exact Or.inl (Nat.lt_of_lt_of_le h h4)
  · rcases h6 with h' | h'
    · exact Or.inl (Nat.lt_of_le_of_lt h1 h')
    · exact Or.inr (Nat.lt_of_lt_of_le h h5)

def pointCost (p : Point) : Nat → Int
  | 0 => p.1
  | 1 => p.2
  | _ => 0

instance (a b : Point) : Decidable (dominates a b) :=
  inferInstanceAs (Decidable (a.1 ≤ b.1 ∧ a.2 ≤ b.2 ∧ (a.1 < b.1 ∨ a.2 < b.2)))

theorem dominates_iff_strictPareto (a b : Point) :
    FiniteFrontier.strictPareto [0, 1] pointCost a b = true ↔ dominates a b := by
  rw [FiniteFrontier.pareto_exact]
  constructor
  · intro h
    have h0 : a.1 ≤ b.1 := (Int.ofNat_le).mp (h.1 0 (by simp))
    have h1 : a.2 ≤ b.2 := (Int.ofNat_le).mp (h.1 1 (by simp))
    obtain ⟨i, hi, hlt⟩ := h.2
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact ⟨h0, h1, Or.inl ((Int.ofNat_lt).mp hlt)⟩
    · exact ⟨h0, h1, Or.inr ((Int.ofNat_lt).mp hlt)⟩
  · intro h
    refine ⟨?_, ?_⟩
    · intro i hi
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact (Int.ofNat_le).mpr h.1
      · exact (Int.ofNat_le).mpr h.2.1
    · rcases h.2.2 with hlt | hlt
      · exact ⟨0, by simp, (Int.ofNat_lt).mpr hlt⟩
      · exact ⟨1, by simp, (Int.ofNat_lt).mpr hlt⟩

def dominatesBool (a b : Point) : Bool :=
  decide (dominates a b)

theorem dominatesBool_eq_strictPareto (a b : Point) :
    dominatesBool a b = FiniteFrontier.strictPareto [0, 1] pointCost a b := by
  have hiff := dominates_iff_strictPareto a b
  cases h : FiniteFrontier.strictPareto [0, 1] pointCost a b <;>
    cases h' : dominatesBool a b
  · rfl
  · have hd : dominates a b := by simpa [dominatesBool, h'] using (of_decide_eq_true h')
    exact Bool.noConfusion ((hiff.mpr hd).symm.trans h)
  · have hnd : ¬ dominates a b := by
      simpa [dominatesBool, h'] using (of_decide_eq_false h')
    exact absurd (hiff.mp h) hnd
  · rfl

/-- Pareto-maximal set of a finite candidate list. Membership is exactly
    `FiniteFrontier.frontier` under two-axis dominance. -/
def paretoMaximal (candidates : List Point) : List Point :=
  FiniteFrontier.frontier candidates dominatesBool

theorem paretoMaximal_mem_iff (candidates : List Point) (x : Point) :
    x ∈ paretoMaximal candidates ↔
      x ∈ FiniteFrontier.frontier candidates (FiniteFrontier.strictPareto [0, 1] pointCost) := by
  have hfun : dominatesBool = FiniteFrontier.strictPareto [0, 1] pointCost := by
    funext a b
    exact dominatesBool_eq_strictPareto a b
  simp only [paretoMaximal, hfun]

theorem paretoMaximal_exact (candidates : List Point) (x : Point) :
    x ∈ paretoMaximal candidates ↔
      x ∈ candidates ∧ ∀ y, y ∈ candidates → ¬ dominates y x := by
  rw [paretoMaximal_mem_iff, FiniteFrontier.frontier_exact]
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro y hy hd
    have hb := h.2 y hy
    have ht := (dominates_iff_strictPareto y x).mpr hd
    simp [ht] at hb
  · intro h
    refine ⟨h.1, ?_⟩
    intro y hy
    cases ht : FiniteFrontier.strictPareto [0, 1] pointCost y x with
    | false => rfl
    | true =>
      exact False.elim (h.2 y hy ((dominates_iff_strictPareto y x).mp ht))

/-- Corresponds to `SoftwareIsQuantifiable.Pareto.frontier_nonempty`. -/
theorem paretoMaximal_nonempty (candidates : List Point) (h : candidates ≠ []) :
    ∃ y, y ∈ paretoMaximal candidates :=
  let ⟨y, hy⟩ := FiniteFrontier.pareto_frontier_nonempty [0, 1] pointCost candidates h
  ⟨y, (paretoMaximal_mem_iff candidates y).mpr hy⟩

/-- Corresponds to `SoftwareIsQuantifiable.Pareto.frontier_not_dominated`. -/
theorem paretoMaximal_not_dominated (candidates : List Point) (out inc : Point)
    (hout : out ∈ paretoMaximal candidates) (hinc : inc ∈ candidates) :
    ¬ dominates inc out :=
  (paretoMaximal_exact candidates out).mp hout |>.2 inc hinc

/-- Corresponds to `SoftwareIsQuantifiable.Pareto.noWorse`.
    Nondomination does not imply this: a frontier member may trade one axis. -/
def noWorse (candidate incumbent : Point) : Prop :=
  candidate.1 ≤ incumbent.1 ∧ candidate.2 ≤ incumbent.2

instance (a b : Point) : Decidable (noWorse a b) :=
  inferInstanceAs (Decidable (a.1 ≤ b.1 ∧ a.2 ≤ b.2))

def admitted (inc : Point) (candidates : List Point) : List Point :=
  candidates.filter (fun candidate => decide (noWorse candidate inc))

/-- Pareto-maximal set after the no-worse admission guard. -/
def guardedMaximal (inc : Point) (candidates : List Point) : List Point :=
  paretoMaximal (admitted inc candidates)

theorem admitted_noWorse {inc out : Point} {candidates : List Point}
    (h : out ∈ admitted inc candidates) : noWorse out inc := by
  have hmem := List.mem_filter.mp h
  simpa [decide_eq_true_eq] using hmem.2

/-- Corresponds to `SoftwareIsQuantifiable.Pareto.admitted_frontier_sound`.
    The guarded output is no worse than the incumbent on both axes, and no
    candidate from the original list dominates it. -/
theorem guardedMaximal_sound {inc out : Point} {candidates : List Point}
    (hout : out ∈ guardedMaximal inc candidates) :
    noWorse out inc ∧ ∀ z, z ∈ candidates → ¬ dominates z out := by
  have hexact := (paretoMaximal_exact (admitted inc candidates) out).mp hout
  have hnw := admitted_noWorse hexact.1
  refine ⟨hnw, ?_⟩
  intro z hz hd
  have hzi : noWorse z inc :=
    ⟨Nat.le_trans hd.1 hnw.1, Nat.le_trans hd.2.1 hnw.2⟩
  have hza : z ∈ admitted inc candidates := by
    simp [admitted, hz, hzi, decide_eq_true_eq]
  exact hexact.2 z hza hd

theorem guardedMaximal_nonempty {inc : Point} {candidates : List Point}
    (hinc : inc ∈ candidates) : ∃ out, out ∈ guardedMaximal inc candidates := by
  have hi : inc ∈ admitted inc candidates := by
    simp [admitted, noWorse, hinc, decide_eq_true_eq]
  have hn : admitted inc candidates ≠ [] := by
    intro hempty
    simp [hempty] at hi
  exact paretoMaximal_nonempty (admitted inc candidates) hn

/-- Disproof, same witnesses as `SoftwareIsQuantifiable.Pareto.frontier_can_regress`.
    Frontier membership alone is not a release gate. -/
theorem paretoMaximal_can_regress :
    let inc : Point := (1, 10)
    let out : Point := (10, 1)
    out ∈ paretoMaximal [inc, out] ∧ ¬ noWorse out inc := by
  decide

/-- Disproof, same witnesses as
    `SoftwareIsQuantifiable.Pareto.not_per_execution_dominance`.
    Overlapping bounds do not decide one execution. -/
theorem not_per_execution_dominance :
    ¬ ∀ x y : Point,
      (1 ≤ x.1 ∧ x.1 ≤ 100 ∧ x.2 = 0) →
      (2 ≤ y.1 ∧ y.1 ≤ 3 ∧ y.2 = 0) →
      y.1 < x.1 := by
  intro h
  have := h (1, 0) (3, 0) (by simp) (by simp)
  simp at this

def releaseAccepts (inc out : Point) (candidates : List Point) : Bool :=
  decide (out ∈ guardedMaximal inc candidates)

/-- A Pareto trade that worsens an axis is maximal and still refused by the guard. -/
def refusalRegressingFrontier : Bool :=
  !(releaseAccepts (1, 10) (10, 1) [(1, 10), (10, 1)]) &&
    ((paretoMaximal [(1, 10), (10, 1)]).contains (10, 1))

def acceptGuardedRelease : Bool :=
  releaseAccepts (10, 10) (1, 10) [(10, 10), (1, 10)]

def refusalOutOfUniverse : Bool :=
  (ExecutableClosure.checkedClose [0] [1] ([] : List (List Nat × Nat))).isNone

def refusalNonstrictReduction : Bool :=
  !(reducedAllowed .projectFirst)

def acceptSumReduction : Bool :=
  reducedAllowed .componentwiseSum

theorem refusal_regressing_frontier : refusalRegressingFrontier = true := by decide

theorem accept_guarded_release : acceptGuardedRelease = true := by decide

theorem refusal_out_of_universe : refusalOutOfUniverse = true := by decide

theorem refusal_nonstrict_reduction : refusalNonstrictReduction = true := by decide

theorem accept_sum_reduction : acceptSumReduction = true := by decide

#print axioms dominates_iff_strictPareto
#print axioms paretoMaximal_exact
#print axioms paretoMaximal_nonempty
#print axioms guardedMaximal_sound
#print axioms paretoMaximal_can_regress
#print axioms not_per_execution_dominance
#print axioms refusal_regressing_frontier
end Optimality
