import Std
namespace FiniteFrontier
variable {A : Type}

-- dominates y x is the chosen total, reproducible comparison predicate.
-- When it represents strict Pareto dominance this is exactly the Pareto frontier.
def frontier (candidates : List A) (dominates : A → A → Bool) : List A :=
  candidates.filter (fun x => !(candidates.any (fun y => dominates y x)))

theorem frontier_exact (candidates : List A) (dominates : A → A → Bool) (x : A) :
    x ∈ frontier candidates dominates ↔
      x ∈ candidates ∧ ∀ y, y ∈ candidates → dominates y x = false := by
  simp [frontier, List.any_eq_true]

def strictPareto (axes : List Nat) (cost : A → Nat → Int) (y x : A) : Bool :=
  axes.all (fun i => decide (cost y i ≤ cost x i)) &&
  axes.any (fun i => decide (cost y i < cost x i))

theorem pareto_exact (axes : List Nat) (cost : A → Nat → Int) (y x : A) :
    strictPareto axes cost y x = true ↔
      (∀ i, i ∈ axes → cost y i ≤ cost x i) ∧
      (∃ i, i ∈ axes ∧ cost y i < cost x i) := by
  simp [strictPareto, List.all_eq_true, List.any_eq_true]

inductive Color where
  | unknown | lawful | unlawful | conflict
  deriving DecidableEq, Repr

def color : Bool → Bool → Color
  | false, false => .unknown
  | true, false => .lawful
  | false, true => .unlawful
  | true, true => .conflict

theorem conflict_exact (positive negative : Bool) :
    color positive negative = .conflict ↔ positive = true ∧ negative = true := by
  cases positive <;> cases negative <;> decide

theorem unknown_exact (positive negative : Bool) :
    color positive negative = .unknown ↔ positive = false ∧ negative = false := by
  cases positive <;> cases negative <;> decide

#print axioms frontier_exact
#print axioms pareto_exact
#print axioms conflict_exact
#print axioms unknown_exact
-- A retained point must be nondominated in the FULL named catalogue. Every
-- excluded point needs a retained strict dominator, not an estimated score.
def certificate [DecidableEq A] (catalogue retained : List A)
    (dominates : A → A → Bool) : Bool :=
  retained.all (fun x => catalogue.contains x &&
    !(catalogue.any (fun y => dominates y x))) &&
  catalogue.all (fun x => retained.contains x ||
    retained.any (fun y => dominates y x))

theorem certificate_exact [DecidableEq A] (catalogue retained : List A)
    (dominates : A → A → Bool) :
    certificate catalogue retained dominates = true ↔
      (∀ x, x ∈ retained → x ∈ catalogue ∧
        ∀ y, y ∈ catalogue → dominates y x = false) ∧
      (∀ x, x ∈ catalogue → x ∈ retained ∨
        ∃ y, y ∈ retained ∧ dominates y x = true) := by
  simp [certificate, List.all_eq_true, List.any_eq_true]

theorem certified_frontier [DecidableEq A] (catalogue retained : List A)
    (dominates : A → A → Bool)
    (valid : certificate catalogue retained dominates = true) (x : A) :
    x ∈ retained ↔ x ∈ FiniteFrontier.frontier catalogue dominates := by
  have checked := (certificate_exact catalogue retained dominates).mp valid
  constructor
  · intro hx
    exact (FiniteFrontier.frontier_exact catalogue dominates x).mpr (checked.1 x hx)
  · intro hx
    have point := (FiniteFrontier.frontier_exact catalogue dominates x).mp hx
    rcases checked.2 x point.1 with kept | ⟨y, hy, beats⟩
    · exact kept
    · have excluded := point.2 y (checked.1 y hy).1
      rw [excluded] at beats
      contradiction

-- A checked certificate supplies a no-worse retained representative of every
-- named point. Semantic qualification and universe coverage are caller premises.
theorem certified_coverage [DecidableEq A] (catalogue retained : List A)
    (axes : List Nat) (cost : A → Nat → Int)
    (valid : certificate catalogue retained (strictPareto axes cost) = true) :
    ∀ x, x ∈ catalogue → ∃ y, y ∈ retained ∧
      ∀ i, i ∈ axes → cost y i ≤ cost x i := by
  intro x hx
  have checked := (certificate_exact catalogue retained _).mp valid
  rcases checked.2 x hx with kept | ⟨y, hy, beats⟩
  · exact ⟨x, kept, fun _ _ => Int.le_refl _⟩
  · exact ⟨y, hy, ((pareto_exact axes cost y x).mp beats).1⟩

-- Equal-cost identities are part of the frontier: a strict-dominator
-- certificate cannot discard one merely by choosing a presentation tie-break.
private def certificateCost (x : Bool) (_ : Nat) : Int := if x then 1 else 0
example : certificate [false, true] [false] (strictPareto [0] certificateCost) = true := by decide
example : certificate [false, true] [true] (strictPareto [0] certificateCost) = false := by decide
example : certificate [false, true] [] (strictPareto [0] certificateCost) = false := by decide
example : certificate [false, true] [false]
    (strictPareto [0] (fun (_ : Bool) (_ : Nat) => (0 : Int))) = false := by decide
example : certificate [false, true] [false, true]
    (strictPareto [0] (fun (_ : Bool) (_ : Nat) => (0 : Int))) = true := by decide

#print axioms certificate_exact
#print axioms certified_frontier
#print axioms certified_coverage
/- The two general Pareto obligations of the finite frontier, inferred from the
   local forms that restate or assume an instance of them: ScopedSelection and
   ScopedCampaign (a scalar selection and a separately checked nondominance
   certificate), FrontierComposition, Composition and GeneralPareto (three
   independent completeness proofs), and OptimalityInterface (nonemptiness).
   ScopedEvidence, LinearSelection and MetricRelevance state no dominance or
   frontier property.

   Obligation F (frontier completeness). For any comparison that is irreflexive
   and transitive on the named list (only on the list: off-list behaviour is
   unconstrained), every listed candidate is on the frontier or is dominated by
   a frontier member. Hence the frontier of a nonempty list is nonempty, the
   frontier certifies itself, and every listed point has a no-worse frontier
   representative under strict Pareto dominance, with no certificate premise.
   Nonemptiness alone needs less: a score that strictly decreases along the
   comparison on the list suffices, with no transitivity.

   Obligation S (selection lands on the frontier). A point that scores no
   worse than each of its listed dominators, under an integer score that is
   strictly better on each of them, is on the frontier. In this general form S
   is a thin lemma (FrontierObligationsControls.general_S_converse shows the
   converse is immediate); its content is in the strict scores: an axis for the
   frontier over that single axis, and a positively weighted sum over the
   supplied axes for the frontier over those axes.

   Not claimed: that minimizing one of several supplied axes reaches the
   frontier over all of them, that every frontier point minimizes some
   positively weighted sum (both refuted in FrontierObligationsControls),
   anything about candidates outside the named list, or that the supplied
   comparison means anything physical. -/

private theorem minimalBelow (d : A → A → Bool) (L : List A)
    (irr : ∀ a, a ∈ L → d a a = false)
    (tr : ∀ a b c, a ∈ L → b ∈ L → c ∈ L →
      d a b = true → d b c = true → d a c = true)
    (x : A) (hx : x ∈ L) (xs : List A) (sub : ∀ z, z ∈ xs → z ∈ L) :
    ∃ y, y ∈ L ∧ (y = x ∨ d y x = true) ∧ ∀ z, z ∈ xs → d z y = false := by
  induction xs with
  | nil => exact ⟨x, hx, Or.inl rfl, by simp⟩
  | cons a rest ih =>
    have haL : a ∈ L := sub a List.mem_cons_self
    obtain ⟨y, hyL, hbelow, hmin⟩ :=
      ih (fun z hz => sub z (List.mem_cons_of_mem a hz))
    cases ha : d a y with
    | false =>
      refine ⟨y, hyL, hbelow, ?_⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact ha
      · exact hmin z hz
    | true =>
      refine ⟨a, haL, Or.inr ?_, ?_⟩
      · rcases hbelow with rfl | hd
        · exact ha
        · exact tr a y x haL hyL hx ha hd
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact irr z haL
        · have hzL := sub z (List.mem_cons_of_mem a hz)
          cases hza : d z a with
          | false => rfl
          | true =>
            have ht := tr z a y hzL haL hyL hza ha
            simp [hmin z hz] at ht

/-- Obligation F: frontier completeness for any comparison that is irreflexive
    and transitive on the named list. -/
theorem frontier_complete_of_strict (L : List A) (d : A → A → Bool)
    (irr : ∀ a, a ∈ L → d a a = false)
    (tr : ∀ a b c, a ∈ L → b ∈ L → c ∈ L →
      d a b = true → d b c = true → d a c = true)
    (x : A) (hx : x ∈ L) :
    x ∈ frontier L d ∨ ∃ y, y ∈ frontier L d ∧ d y x = true := by
  obtain ⟨y, hyL, hbelow, hmin⟩ := minimalBelow d L irr tr x hx L (fun _ h => h)
  have hf : y ∈ frontier L d := (frontier_exact L d y).mpr ⟨hyL, hmin⟩
  rcases hbelow with rfl | hd
  · exact Or.inl hf
  · exact Or.inr ⟨y, hf, hd⟩

theorem frontier_nonempty_of_strict (L : List A) (d : A → A → Bool)
    (irr : ∀ a, a ∈ L → d a a = false)
    (tr : ∀ a b c, a ∈ L → b ∈ L → c ∈ L →
      d a b = true → d b c = true → d a c = true)
    (h : L ≠ []) : ∃ y, y ∈ frontier L d := by
  cases L with
  | nil => exact absurd rfl h
  | cons x xs =>
    rcases frontier_complete_of_strict (x :: xs) d irr tr x List.mem_cons_self with
      hf | ⟨y, hy, _⟩
    · exact ⟨x, hf⟩
    · exact ⟨y, hy⟩

/-- Under an order irreflexive and transitive on the list, the frontier
    certifies itself, so a certificate exists. Without transitivity none need
    exist (FrontierObligationsControls.need_trans_no_certificate). -/
theorem frontier_certifies_of_strict [DecidableEq A] (L : List A) (d : A → A → Bool)
    (irr : ∀ a, a ∈ L → d a a = false)
    (tr : ∀ a b c, a ∈ L → b ∈ L → c ∈ L →
      d a b = true → d b c = true → d a c = true) :
    certificate L (frontier L d) d = true :=
  (certificate_exact L (frontier L d) d).mpr
    ⟨fun x hx => (frontier_exact L d x).mp hx,
     fun x hx => frontier_complete_of_strict L d irr tr x hx⟩

theorem strictPareto_irrefl (axes : List Nat) (cost : A → Nat → Int) (x : A) :
    strictPareto axes cost x x = false := by
  cases h : strictPareto axes cost x x with
  | false => rfl
  | true =>
    obtain ⟨_, _, _, hlt⟩ := (pareto_exact axes cost x x).mp h
    exact absurd hlt (Int.lt_irrefl _)

theorem strictPareto_trans (axes : List Nat) (cost : A → Nat → Int) (x y z : A)
    (hxy : strictPareto axes cost x y = true)
    (hyz : strictPareto axes cost y z = true) :
    strictPareto axes cost x z = true := by
  obtain ⟨le1, i, hi, lt1⟩ := (pareto_exact axes cost x y).mp hxy
  obtain ⟨le2, _⟩ := (pareto_exact axes cost y z).mp hyz
  exact (pareto_exact axes cost x z).mpr
    ⟨fun j hj => Int.le_trans (le1 j hj) (le2 j hj),
     i, hi, Int.lt_of_lt_of_le lt1 (le2 i hi)⟩

/-- Obligation F for strict Pareto dominance: no premises. -/
theorem pareto_frontier_complete (axes : List Nat) (cost : A → Nat → Int)
    (L : List A) (x : A) (hx : x ∈ L) :
    x ∈ frontier L (strictPareto axes cost) ∨
      ∃ y, y ∈ frontier L (strictPareto axes cost) ∧ strictPareto axes cost y x = true :=
  frontier_complete_of_strict L _ (fun a _ => strictPareto_irrefl axes cost a)
    (fun a b c _ _ _ => strictPareto_trans axes cost a b c) x hx

theorem pareto_frontier_nonempty (axes : List Nat) (cost : A → Nat → Int)
    (L : List A) (h : L ≠ []) : ∃ y, y ∈ frontier L (strictPareto axes cost) :=
  frontier_nonempty_of_strict L _ (fun a _ => strictPareto_irrefl axes cost a)
    (fun a b c _ _ _ => strictPareto_trans axes cost a b c) h

theorem pareto_frontier_certifies [DecidableEq A] (axes : List Nat)
    (cost : A → Nat → Int) (L : List A) :
    certificate L (frontier L (strictPareto axes cost)) (strictPareto axes cost) = true :=
  frontier_certifies_of_strict L _ (fun a _ => strictPareto_irrefl axes cost a)
    (fun a b c _ _ _ => strictPareto_trans axes cost a b c)

/-- `certified_coverage` without its certificate premise. -/
theorem frontier_coverage (axes : List Nat) (cost : A → Nat → Int) (L : List A) :
    ∀ x, x ∈ L → ∃ y, y ∈ frontier L (strictPareto axes cost) ∧
      ∀ i, i ∈ axes → cost y i ≤ cost x i := by
  intro x hx
  rcases pareto_frontier_complete axes cost L x hx with hf | ⟨y, hy, hd⟩
  · exact ⟨x, hf, fun _ _ => Int.le_refl _⟩
  · exact ⟨y, hy, ((pareto_exact axes cost y x).mp hd).1⟩

/-- Obligation S: a point scoring no worse than each of its listed dominators,
    under a score strictly better on each of them, is on the frontier. Global
    minimality is not needed, only minimality against x's own dominators. -/
theorem minimizer_on_frontier (L : List A) (d : A → A → Bool) (s : A → Int)
    (x : A) (hx : x ∈ L) (hmin : ∀ y, y ∈ L → d y x = true → s x ≤ s y)
    (strict : ∀ y, y ∈ L → d y x = true → s y < s x) :
    x ∈ frontier L d := by
  refine (frontier_exact L d x).mpr ⟨hx, fun y hy => ?_⟩
  cases h : d y x with
  | false => rfl
  | true => exact absurd (Int.lt_of_lt_of_le (strict y hy h) (hmin y hy h)) (Int.lt_irrefl _)

private theorem exists_min (s : A → Int) : ∀ L : List A, L ≠ [] →
    ∃ x, x ∈ L ∧ ∀ y, y ∈ L → s x ≤ s y
  | [], h => absurd rfl h
  | [z], _ => ⟨z, by simp, by simp [Int.le_refl]⟩
  | z :: w :: rest, _ => by
    obtain ⟨m, hm, hmin⟩ := exists_min s (w :: rest) (by simp)
    by_cases hz : s z ≤ s m
    · refine ⟨z, by simp, fun y hy => ?_⟩
      rcases List.mem_cons.mp hy with rfl | hy
      · exact Int.le_refl _
      · exact Int.le_trans hz (hmin y hy)
    · refine ⟨m, List.mem_cons_of_mem z hm, fun y hy => ?_⟩
      rcases List.mem_cons.mp hy with rfl | hy
      · exact Int.le_of_lt (Int.lt_of_not_ge hz)
      · exact hmin y hy

/-- Nonemptiness from a ranking alone: a score strictly decreasing along the
    comparison on the list. No transitivity and no separate irreflexivity
    (the ranking implies irreflexivity on the list). Found by the independent
    counterexample attempt. -/
theorem frontier_nonempty_of_ranked (L : List A) (d : A → A → Bool) (s : A → Int)
    (rank : ∀ x y, x ∈ L → y ∈ L → d y x = true → s y < s x) (h : L ≠ []) :
    ∃ y, y ∈ frontier L d := by
  obtain ⟨x, hx, hmin⟩ := exists_min s L h
  exact ⟨x, minimizer_on_frontier L d s x hx (fun y hy _ => hmin y hy)
    (fun y hy hd => rank x y hx hy hd)⟩

/-- An axis is a strict score for strict Pareto dominance over that single
    axis (not over a longer axis list). -/
theorem axis_strict (i : Nat) (cost : A → Nat → Int) (y x : A)
    (h : strictPareto [i] cost y x = true) : cost y i < cost x i := by
  obtain ⟨_, j, hj, hlt⟩ := (pareto_exact [i] cost y x).mp h
  simp only [List.mem_singleton] at hj
  exact hj ▸ hlt

def weightedCost (axes : List Nat) (w : Nat → Int) (cost : A → Nat → Int) (x : A) : Int :=
  axes.foldr (fun i acc => w i * cost x i + acc) 0

private theorem weighted_le (axes : List Nat) (w : Nat → Int) (cost : A → Nat → Int)
    (y x : A) (pos : ∀ i, i ∈ axes → 0 < w i)
    (le : ∀ i, i ∈ axes → cost y i ≤ cost x i) :
    weightedCost axes w cost y ≤ weightedCost axes w cost x := by
  induction axes with
  | nil => exact Int.le_refl _
  | cons j js ih =>
    simp only [weightedCost, List.foldr_cons] at *
    have hj := Int.mul_le_mul_of_nonneg_left (le j List.mem_cons_self)
      (Int.le_of_lt (pos j List.mem_cons_self))
    have hr := ih (fun i hi => pos i (List.mem_cons_of_mem j hi))
      (fun i hi => le i (List.mem_cons_of_mem j hi))
    exact Int.add_le_add hj hr

/-- A positively weighted sum over the supplied axes is a strict score. -/
theorem weighted_strict (axes : List Nat) (w : Nat → Int) (cost : A → Nat → Int)
    (pos : ∀ i, i ∈ axes → 0 < w i) (y x : A)
    (h : strictPareto axes cost y x = true) :
    weightedCost axes w cost y < weightedCost axes w cost x := by
  obtain ⟨le, k, hk, hlt⟩ := (pareto_exact axes cost y x).mp h
  induction axes with
  | nil => simp at hk
  | cons j js ih =>
    simp only [weightedCost, List.foldr_cons] at *
    have posj := pos j List.mem_cons_self
    have pos' := fun i (hi : i ∈ js) => pos i (List.mem_cons_of_mem j hi)
    have le' := fun i (hi : i ∈ js) => le i (List.mem_cons_of_mem j hi)
    rcases List.mem_cons.mp hk with rfl | hk
    · exact Int.add_lt_add_of_lt_of_le (Int.mul_lt_mul_of_pos_left hlt posj)
        (weighted_le js w cost y x pos' le')
    · have hst : strictPareto js cost y x = true :=
        (pareto_exact js cost y x).mpr ⟨le', k, hk, hlt⟩
      exact Int.add_lt_add_of_le_of_lt
        (Int.mul_le_mul_of_nonneg_left (le j List.mem_cons_self) (Int.le_of_lt posj))
        (ih pos' hst le' hk)

theorem axis_minimizer_on_frontier (i : Nat) (cost : A → Nat → Int) (L : List A)
    (x : A) (hx : x ∈ L) (hmin : ∀ y, y ∈ L → cost x i ≤ cost y i) :
    x ∈ frontier L (strictPareto [i] cost) :=
  minimizer_on_frontier L _ (fun z => cost z i) x hx (fun y hy _ => hmin y hy)
    (fun y _ h => axis_strict i cost y x h)

theorem weighted_minimizer_on_frontier (axes : List Nat) (w : Nat → Int)
    (cost : A → Nat → Int) (pos : ∀ i, i ∈ axes → 0 < w i) (L : List A)
    (x : A) (hx : x ∈ L)
    (hmin : ∀ y, y ∈ L → weightedCost axes w cost x ≤ weightedCost axes w cost y) :
    x ∈ frontier L (strictPareto axes cost) :=
  minimizer_on_frontier L _ (weightedCost axes w cost) x hx (fun y hy _ => hmin y hy)
    (fun y _ h => weighted_strict axes w cost pos y x h)

#print axioms frontier_complete_of_strict
#print axioms frontier_nonempty_of_strict
#print axioms frontier_certifies_of_strict
#print axioms strictPareto_irrefl
#print axioms strictPareto_trans
#print axioms pareto_frontier_complete
#print axioms pareto_frontier_nonempty
#print axioms pareto_frontier_certifies
#print axioms frontier_coverage
#print axioms minimizer_on_frontier
#print axioms frontier_nonempty_of_ranked
#print axioms axis_strict
#print axioms weighted_strict
#print axioms axis_minimizer_on_frontier
#print axioms weighted_minimizer_on_frontier
end FiniteFrontier
