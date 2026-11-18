import Qualification
import FiniteFrontier
import LinearSelection
import ExecutableClosure
import Std

/- Generic closure, compounding, and Pareto composition.

   `closure` is the least rooted derivation. It is the same consequence
   relation as `SoftwareIsQuantifiable.Coloring.Deriv`: seed facts plus
   one application of a finite-premise Horn rule. `ExecutableClosure.close`
   is the exhaustive snapshot computation corresponding to
   `SoftwareIsQuantifiable.Coloring.coloring`, under the same snapshot
   side condition that every rule head lies in the named universe.

   This file does not prove incremental release monotonicity. Downstream
   release, certification, safety, and regression developments import the
   named theorems; they do not inherit those claims from the names alone.
-/
namespace Optimality

def closure {A : Type} (B : A → Prop) (R : List A → A → Prop) : A → Prop :=
  Qualification.Derives B R

theorem closure_extensive {A : Type} {B : A → Prop} {R : List A → A → Prop}
    {a : A} (h : B a) : closure B R a :=
  Qualification.Derives.root h

theorem closure_least {A : Type} {B : A → Prop} {R : List A → A → Prop}
    {X : A → Prop} (roots : ∀ a, B a → X a) (rules : Qualification.Closed R X) :
    ∀ a, closure B R a → X a :=
  Qualification.least roots rules

theorem closure_closed {A : Type} (B : A → Prop) (R : List A → A → Prop) :
    Qualification.Closed R (closure B R) :=
  Qualification.closed B R

theorem closure_monotone {A : Type} {B C : A → Prop} {R S : List A → A → Prop}
    (hb : ∀ a, B a → C a) (hr : ∀ ps a, R ps a → S ps a) :
    ∀ a, closure B R a → closure C S a :=
  Qualification.monotone hb hr

theorem closure_idempotent {A : Type} (B : A → Prop) (R : List A → A → Prop) (a : A) :
    closure (closure B R) R a ↔ closure B R a :=
  Qualification.idempotent B R a

theorem closure_compound {A : Type} (B C : A → Prop) (R : List A → A → Prop) (a : A) :
    closure (fun x => B x ∨ C x) R a ↔
      closure (fun x => closure B R x ∨ closure C R x) R a :=
  Qualification.compounding B C R a

def anyOf {A : Type} (ps : List (A → Prop)) (a : A) : Prop :=
  ∃ p, p ∈ ps ∧ p a

/-- Finite evidence sources compound. Closing the union equals closing the
    union of the already-closed sources, so cross-source consequences are kept.
    This is not the witness-set join `SoftwareIsQuantifiable.Fold.join`: that
    join is union of root identities before any rule fires. -/
theorem closure_compound_finite {A : Type} (ps : List (A → Prop))
    (R : List A → A → Prop) (a : A) :
    closure (anyOf ps) R a ↔
      closure (anyOf (ps.map (fun B => closure B R))) R a := by
  constructor
  · apply Qualification.monotone _ (fun _ _ h => h) a
    intro x hx
    rcases hx with ⟨B, hB, hxB⟩
    exact ⟨closure B R, List.mem_map.mpr ⟨B, hB, rfl⟩, closure_extensive hxB⟩
  · apply Qualification.least _ (Qualification.closed (anyOf ps) R) a
    intro x hx
    rcases hx with ⟨P, hP, hxP⟩
    rcases List.mem_map.mp hP with ⟨B, hB, rfl⟩
    exact Qualification.monotone (fun y hy => ⟨B, hB, hy⟩) (fun _ _ h => h) x hxP

theorem closure_order_independent {A : Type} {B : A → Prop} {R : List A → A → Prop}
    {X Y : A → Prop}
    (bx : ∀ a, B a → X a) (by_ : ∀ a, B a → Y a)
    (cx : Qualification.Closed R X) (cy : Qualification.Closed R Y)
    (sx : ∀ a, X a → closure B R a) (sy : ∀ a, Y a → closure B R a) :
    ∀ a, X a ↔ Y a :=
  Qualification.order_independent bx by_ cx cy sx sy

theorem closure_sound {A : Type} {B TrueAt : A → Prop} {R : List A → A → Prop}
    (validRoots : ∀ a, B a → TrueAt a) (validRules : Qualification.Closed R TrueAt) :
    ∀ a, closure B R a → TrueAt a :=
  Qualification.soundness validRoots validRules

def liveRoots {A : Type} (B withdrawn : A → Prop) : A → Prop :=
  Qualification.liveRoots B withdrawn

def liveRules {A : Type} (R withdrawn : List A → A → Prop) : List A → A → Prop :=
  Qualification.liveRules R withdrawn

theorem withdrawal_no_new_support {A : Type} (B withdrawn : A → Prop)
    (R deadRules : List A → A → Prop) :
    ∀ a, closure (liveRoots B withdrawn) (liveRules R deadRules) a → closure B R a :=
  Qualification.withdrawal_no_new_support B withdrawn R deadRules

theorem surviving_subsystem {A : Type} (B B0 withdrawn : A → Prop)
    (R R0 deadRules : List A → A → Prop)
    (rootsLive : ∀ a, B0 a → liveRoots B withdrawn a)
    (rulesLive : ∀ ps a, R0 ps a → liveRules R deadRules ps a) :
    ∀ a, closure B0 R0 a → closure (liveRoots B withdrawn) (liveRules R deadRules) a :=
  Qualification.surviving_subsystem B B0 withdrawn R R0 deadRules rootsLive rulesLive

theorem no_bootstrap {A : Type} (R : List A → A → Prop)
    (nonempty : ∀ ps a, R ps a → ∃ p, p ∈ ps) :
    ∀ a, ¬ closure (fun _ => False) R a :=
  Qualification.no_bootstrap R nonempty

/-- Premise `embed`: every locally authorized rule remains authorized in the
    joint rule set. Under that premise, closing under the local rules and then
    under the joint rules is the joint closure. -/
theorem reclose_under_embedded_rules {A : Type} (B : A → Prop)
    (R S : List A → A → Prop)
    (embed : ∀ ps a, R ps a → S ps a) (a : A) :
    closure (closure B R) S a ↔ closure B S a := by
  constructor
  · apply Qualification.least
    · intro x hx
      exact Qualification.monotone (fun _ h => h) embed x hx
    · exact Qualification.closed B S
  · apply Qualification.monotone
    · intro x hx
      exact closure_extensive hx
    · intro _ _ h
      exact h

/-- Component composition of closure. `sumRules` is the separation premise:
    a rule's premises and head lie in one summand. There is no cross-domain rule. -/
def sumRoots {A C : Type} (B : A → Prop) (D : C → Prop) : A ⊕ C → Prop
  | .inl a => B a
  | .inr c => D c

def sumRules {A C : Type} (R : List A → A → Prop) (S : List C → C → Prop) :
    List (A ⊕ C) → A ⊕ C → Prop
  | ps, .inl a => ∃ as, ps = as.map Sum.inl ∧ R as a
  | ps, .inr c => ∃ cs, ps = cs.map Sum.inr ∧ S cs c

private def projectLeft {A C : Type} (B : A → Prop) (R : List A → A → Prop) :
    A ⊕ C → Prop
  | .inl a => closure B R a
  | .inr _ => True

private def projectRight {A C : Type} (D : C → Prop) (S : List C → C → Prop) :
    A ⊕ C → Prop
  | .inl _ => True
  | .inr c => closure D S c

theorem closure_factors_left {A C : Type} (B : A → Prop) (D : C → Prop)
    (R : List A → A → Prop) (S : List C → C → Prop) (a : A) :
    closure (sumRoots B D) (sumRules R S) (Sum.inl a) ↔ closure B R a := by
  constructor
  · intro h
    have hall : ∀ s, closure (sumRoots B D) (sumRules R S) s → projectLeft B R s := by
      apply Qualification.least
      · intro s hs
        cases s with
        | inl x => exact closure_extensive hs
        | inr _ => trivial
      · intro ps s hr hp
        cases s with
        | inl x =>
          rcases hr with ⟨as, rfl, hR⟩
          apply Qualification.Derives.step hR
          intro p hm
          exact hp (Sum.inl p) (List.mem_map.mpr ⟨p, hm, rfl⟩)
        | inr _ => trivial
    exact hall (Sum.inl a) h
  · intro h
    induction h with
    | root hb => exact closure_extensive hb
    | @step ps a hr hp ih =>
      apply Qualification.Derives.step (ps := ps.map Sum.inl) (a := Sum.inl a)
      · exact ⟨ps, rfl, hr⟩
      · intro p hm
        rcases List.mem_map.mp hm with ⟨q, hq, rfl⟩
        exact ih q hq

theorem closure_factors_right {A C : Type} (B : A → Prop) (D : C → Prop)
    (R : List A → A → Prop) (S : List C → C → Prop) (c : C) :
    closure (sumRoots B D) (sumRules R S) (Sum.inr c) ↔ closure D S c := by
  constructor
  · intro h
    have hall : ∀ s, closure (sumRoots B D) (sumRules R S) s → projectRight D S s := by
      apply Qualification.least
      · intro s hs
        cases s with
        | inl _ => trivial
        | inr x => exact closure_extensive hs
      · intro ps s hr hp
        cases s with
        | inl _ => trivial
        | inr x =>
          rcases hr with ⟨cs, rfl, hS⟩
          apply Qualification.Derives.step hS
          intro p hm
          exact hp (Sum.inr p) (List.mem_map.mpr ⟨p, hm, rfl⟩)
    exact hall (Sum.inr c) h
  · intro h
    induction h with
    | root hb => exact closure_extensive hb
    | @step ps c hr hp ih =>
      apply Qualification.Derives.step (ps := ps.map Sum.inr) (a := Sum.inr c)
      · exact ⟨ps, rfl, hr⟩
      · intro p hm
        rcases List.mem_map.mp hm with ⟨q, hq, rfl⟩
        exact ih q hq

/-- The gates are premises: each must be proved equal to its component closure
    (for list gates, `closure_operator_exact` discharges that). Separation is
    `sumRules`. The conjunctive gate is then exactly joint derivability in each
    component. -/
theorem separated_closure_conjoins {α β : Type}
    (g1 : α → Bool) (g2 : β → Bool)
    (B1 : α → Prop) (R1 : List α → α → Prop)
    (B2 : β → Prop) (R2 : List β → β → Prop)
    (h1 : ∀ a, g1 a = true ↔ closure B1 R1 a)
    (h2 : ∀ b, g2 b = true ↔ closure B2 R2 b)
    (p : α × β) :
    (g1 p.1 && g2 p.2) = true ↔
      closure (sumRoots B1 B2) (sumRules R1 R2) (Sum.inl p.1) ∧
      closure (sumRoots B1 B2) (sumRules R1 R2) (Sum.inr p.2) := by
  simp only [Bool.and_eq_true]
  constructor
  · intro h
    exact ⟨(closure_factors_left B1 B2 R1 R2 p.1).mpr ((h1 p.1).mp h.1),
      (closure_factors_right B1 B2 R1 R2 p.2).mpr ((h2 p.2).mp h.2)⟩
  · intro h
    exact ⟨(h1 p.1).mpr ((closure_factors_left B1 B2 R1 R2 p.1).mp h.1),
      (h2 p.2).mpr ((closure_factors_right B1 B2 R1 R2 p.2).mp h.2)⟩

/-- Horn rules in the shape used by `SoftwareIsQuantifiable.Coloring.Rule`. -/
structure Horn (A : Type) where
  premises : List A
  conclusion : A

/-- Same constructors as `SoftwareIsQuantifiable.Coloring.Deriv`. -/
inductive HornDeriv {A : Type} (rules : List (Horn A)) (seed : A → Bool) : A → Prop where
  | seed {f : A} : seed f = true → HornDeriv rules seed f
  | apply {r : Horn A} : r ∈ rules →
      (∀ p, p ∈ r.premises → HornDeriv rules seed p) →
      HornDeriv rules seed r.conclusion

def hornRelation {A : Type} (rules : List (Horn A)) : List A → A → Prop :=
  fun ps a => ∃ r, r ∈ rules ∧ r.premises = ps ∧ r.conclusion = a

theorem hornDeriv_iff_closure {A : Type} (rules : List (Horn A)) (seed : A → Bool) (a : A) :
    HornDeriv rules seed a ↔ closure (fun x => seed x = true) (hornRelation rules) a := by
  constructor
  · intro h
    induction h with
    | seed hs => exact closure_extensive hs
    | @apply r hr hp ih =>
      apply Qualification.Derives.step
      · exact ⟨r, hr, rfl, rfl⟩
      · exact ih
  · intro h
    apply Qualification.least (X := HornDeriv rules seed) _ _ a h
    · intro x hx
      exact HornDeriv.seed hx
    · intro ps x hr hp
      rcases hr with ⟨r, hmem, hps, hconc⟩
      subst hps
      subst hconc
      exact HornDeriv.apply hmem hp

/-- Snapshot side condition, corresponding to `Coloring.coloring`'s universe
    hypothesis: every root and every rule head belongs to `U`. Premises outside
    `U` cannot acquire support. -/
theorem closure_operator_exact {A : Type} [DecidableEq A]
    (U B : List A) (rules : List (List A × A))
    (hb : ∀ a, a ∈ B → a ∈ U)
    (hr : ∀ ps a, (ps, a) ∈ rules → a ∈ U) (a : A) :
    a ∈ ExecutableClosure.close U B rules ↔
      closure (fun x => x ∈ B) (fun ps x => (ps, x) ∈ rules) a :=
  ExecutableClosure.close_exact U B rules hb hr a

/-- Disproof that naive union of closures computes joint closure.
    Atom 2 is a cross-source consequence of roots 0 and 1 together. -/
theorem union_misses_cross_consequence :
    (2 ∉ ExecutableClosure.close [0, 1, 2] [0] [([0, 1], 2)]) ∧
    (2 ∉ ExecutableClosure.close [0, 1, 2] [1] [([0, 1], 2)]) ∧
    (2 ∈ ExecutableClosure.close [0, 1, 2] [0, 1] [([0, 1], 2)]) := by
  decide

/-- Disproof that closure factors without the separation premise.
    The joint rule reads one premise from each summand. -/
theorem factorization_needs_separation :
    let jointRoots : Nat ⊕ Nat → Prop
      | .inl 0 => True
      | .inr 0 => True
      | _ => False
    let jointRules : List (Nat ⊕ Nat) → Nat ⊕ Nat → Prop
      | ps, .inl 1 => ps = [.inl 0, .inr 0]
      | _, _ => False
    closure jointRoots jointRules (Sum.inl 1) ∧
      ¬ closure (fun a : Nat => a = 0) (fun _ _ => False) 1 := by
  refine ⟨?_, ?_⟩
  · apply Qualification.Derives.step (ps := [.inl 0, .inr 0]) (a := Sum.inl 1)
    · rfl
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact closure_extensive trivial
      · exact closure_extensive trivial
  · intro h
    have : (1 : Nat) = 0 :=
      Qualification.least (X := fun a => a = 0) (fun _ hx => hx)
        (fun _ _ hr _ => False.elim hr) 1 h
    contradiction

def axisSum (axes : List Nat) (f : Nat → Int) : Int :=
  match axes with
  | [] => 0
  | i :: is => f i + axisSum is f

theorem axisSum_le (axes : List Nat) (f g : Nat → Int)
    (h : ∀ i, i ∈ axes → f i ≤ g i) :
    axisSum axes f ≤ axisSum axes g := by
  induction axes with
  | nil =>
    simp only [axisSum]
    exact Int.le_refl _
  | cons i is ih =>
    have hi := h i (List.mem_cons_self (a := i) (l := is))
    have hs := ih (fun j hj => h j (List.mem_cons_of_mem i hj))
    have h1 : f i + axisSum is f ≤ g i + axisSum is f := Int.add_le_add_right hi _
    have h2 : g i + axisSum is f ≤ g i + axisSum is g := Int.add_le_add_left hs _
    exact Int.le_trans h1 h2

theorem axisSum_lt (axes : List Nat) (f g : Nat → Int) (k : Nat)
    (hle : ∀ i, i ∈ axes → f i ≤ g i) (hk : k ∈ axes) (hlt : f k < g k) :
    axisSum axes f < axisSum axes g := by
  induction axes with
  | nil => cases hk
  | cons i is ih =>
    rcases List.mem_cons.mp hk with hki | hk
    · cases hki
      have hs := axisSum_le is f g (fun j hj => hle j (List.mem_cons_of_mem k hj))
      exact Int.add_lt_add_of_lt_of_le hlt hs
    · have hi := hle i (List.mem_cons_self (a := i) (l := is))
      have hs := ih (fun j hj => hle j (List.mem_cons_of_mem i hj)) hk
      have h1 : f i + axisSum is f < f i + axisSum is g := Int.add_lt_add_left hs _
      have h2 : f i + axisSum is g ≤ g i + axisSum is g := Int.add_le_add_right hi _
      exact Int.lt_of_lt_of_le h1 h2

theorem strictPareto_irrefl {α : Type} (axes : List Nat) (cost : α → Nat → Int) (x : α) :
    FiniteFrontier.strictPareto axes cost x x = false := by
  cases h : FiniteFrontier.strictPareto axes cost x x with
  | false => rfl
  | true =>
    obtain ⟨_, ⟨i, _, hlt⟩⟩ := (FiniteFrontier.pareto_exact axes cost x x).mp h
    exact absurd hlt (Int.lt_irrefl _)

theorem strictPareto_trans {α : Type} (axes : List Nat) (cost : α → Nat → Int)
    (x y z : α)
    (hxy : FiniteFrontier.strictPareto axes cost x y = true)
    (hyz : FiniteFrontier.strictPareto axes cost y z = true) :
    FiniteFrontier.strictPareto axes cost x z = true := by
  have hxy' := (FiniteFrontier.pareto_exact axes cost x y).mp hxy
  have hyz' := (FiniteFrontier.pareto_exact axes cost y z).mp hyz
  apply (FiniteFrontier.pareto_exact axes cost x z).mpr
  refine ⟨fun i hi => Int.le_trans (hxy'.1 i hi) (hyz'.1 i hi), ?_⟩
  obtain ⟨i, hi, hlt⟩ := hxy'.2
  exact ⟨i, hi, Int.lt_of_lt_of_le hlt (hyz'.1 i hi)⟩

def minAxisSum {α : Type} (axes : List Nat) (cost : α → Nat → Int) : List α → Int
  | [] => 0
  | [x] => axisSum axes (cost x)
  | x :: y :: ys =>
    min (axisSum axes (cost x)) (minAxisSum axes cost (y :: ys))

theorem minAxisSum_le {α : Type} (axes : List Nat) (cost : α → Nat → Int) :
    ∀ (xs : List α) (x : α), x ∈ xs →
      minAxisSum axes cost xs ≤ axisSum axes (cost x)
  | [], _, hx => by cases hx
  | [z], x, hx => by
      simp only [List.mem_singleton] at hx
      subst hx
      exact Int.le_refl _
  | z :: y :: ys, x, hx => by
      simp only [minAxisSum]
      rcases List.mem_cons.mp hx with hxz | hx
      · subst hxz
        exact Int.min_le_left _ _
      · exact Int.le_trans (Int.min_le_right _ _) (minAxisSum_le axes cost (y :: ys) x hx)

theorem axisSum_lt_of_pareto {α : Type} (axes : List Nat) (cost : α → Nat → Int)
    (y x : α) (h : FiniteFrontier.strictPareto axes cost y x = true) :
    axisSum axes (cost y) < axisSum axes (cost x) := by
  have h' := (FiniteFrontier.pareto_exact axes cost y x).mp h
  obtain ⟨k, hk, hlt⟩ := h'.2
  exact axisSum_lt axes (cost y) (cost x) k h'.1 hk hlt

/-- Every excluded candidate is strictly dominated by some frontier member.
    Dominance here is `FiniteFrontier.strictPareto`, which is irreflexive and
    transitive, so the descending chain of cost sums is finite. -/
theorem frontier_covers {α : Type} (axes : List Nat) (cost : α → Nat → Int)
    (candidates : List α) (x : α) (hx : x ∈ candidates) :
    x ∈ FiniteFrontier.frontier candidates (FiniteFrontier.strictPareto axes cost) ∨
      ∃ y, y ∈ FiniteFrontier.frontier candidates (FiniteFrontier.strictPareto axes cost) ∧
        FiniteFrontier.strictPareto axes cost y x = true := by
  classical
  let dom := FiniteFrontier.strictPareto axes cost
  let sum : α → Int := fun z => axisSum axes (cost z)
  let amin := minAxisSum axes cost candidates
  have hmin : ∀ z, z ∈ candidates → amin ≤ sum z :=
    fun z hz => minAxisSum_le axes cost candidates z hz
  let debt : α → Nat := fun z => (sum z - amin).toNat
  have debt_lt : ∀ y x, y ∈ candidates → x ∈ candidates → dom y x = true →
      debt y < debt x := by
    intro y x hy hx hdom
    have hsum : sum y < sum x := axisSum_lt_of_pareto axes cost y x hdom
    have hy0 : amin ≤ sum y := hmin y hy
    have hpos : 0 < sum x - amin := by omega
    have hdiff : sum y - amin < sum x - amin := by omega
    exact (Int.toNat_lt_toNat hpos).mpr hdiff
  suffices ∀ n x, x ∈ candidates → debt x ≤ n →
      x ∈ FiniteFrontier.frontier candidates dom ∨
        ∃ y, y ∈ FiniteFrontier.frontier candidates dom ∧ dom y x = true from
    this (debt x) x hx (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro x hx hdebt
    left
    rw [FiniteFrontier.frontier_exact]
    refine ⟨hx, ?_⟩
    intro y hy
    cases hdom : dom y x with
    | false => rfl
    | true =>
      exact absurd (Nat.lt_of_lt_of_le (debt_lt y x hy hx hdom) hdebt) (Nat.not_lt_zero _)
  | succ n ih =>
    intro x hx hdebt
    by_cases hsome : ∃ y, y ∈ candidates ∧ dom y x = true
    · obtain ⟨y, hy, hyd⟩ := hsome
      have hdy : debt y ≤ n :=
        Nat.lt_succ_iff.mp (Nat.lt_of_lt_of_le (debt_lt y x hy hx hyd) hdebt)
      rcases ih y hy hdy with hf | ⟨z, hz, hzd⟩
      · exact Or.inr ⟨y, hf, hyd⟩
      · exact Or.inr ⟨z, hz, strictPareto_trans axes cost z y x hzd hyd⟩
    · left
      rw [FiniteFrontier.frontier_exact]
      refine ⟨hx, ?_⟩
      intro y hy
      cases hdom : dom y x with
      | false => rfl
      | true => exact False.elim (hsome ⟨y, hy, hdom⟩)

def pruningOK_prop {α : Type} (candidates kept : List α) (selected : α)
    (dominates : α → α → Bool) : Prop :=
  selected ∈ kept ∧
  (∀ y, y ∈ kept → y ∈ candidates) ∧
  (∀ y, y ∈ kept → dominates y selected = false) ∧
  (∀ z, z ∈ candidates → z ∈ kept ∨ ∃ d, d ∈ kept ∧ dominates d z = true)

/-- Soundness uses transitivity of the supplied dominance predicate as a premise.
    `pruning_sound_pareto` discharges that premise for `strictPareto`. -/
theorem pruning_sound {α : Type} (candidates kept : List α) (selected : α)
    (dominates : α → α → Bool)
    (htrans : ∀ x y z, dominates x y = true → dominates y z = true → dominates x z = true)
    (hok : pruningOK_prop candidates kept selected dominates) :
    selected ∈ FiniteFrontier.frontier candidates dominates := by
  obtain ⟨hsel, hsub, hnd, hexp⟩ := hok
  rw [FiniteFrontier.frontier_exact]
  refine ⟨hsub selected hsel, ?_⟩
  intro y hy
  cases hdom : dominates y selected with
  | false => rfl
  | true =>
    rcases hexp y hy with hyk | ⟨d, hd, hdy⟩
    · exact Bool.noConfusion (hdom.symm.trans (hnd y hyk))
    · exact Bool.noConfusion ((htrans d y selected hdy hdom).symm.trans (hnd d hd))

theorem pruning_sound_pareto {α : Type} (axes : List Nat) (cost : α → Nat → Int)
    (candidates kept : List α) (selected : α)
    (hok : pruningOK_prop candidates kept selected (FiniteFrontier.strictPareto axes cost)) :
    selected ∈ FiniteFrontier.frontier candidates (FiniteFrontier.strictPareto axes cost) :=
  pruning_sound candidates kept selected _
    (fun x y z hxy hyz => strictPareto_trans axes cost x y z hxy hyz) hok

def pruningOK [DecidableEq α] (candidates kept : List α) (selected : α)
    (dominates : α → α → Bool) : Bool :=
  kept.contains selected &&
  kept.all (fun y => candidates.contains y && !(dominates y selected)) &&
  candidates.all (fun z => kept.contains z || kept.any (fun d => dominates d z))

theorem pruningOK_implies [DecidableEq α] (candidates kept : List α) (selected : α)
    (dominates : α → α → Bool) (h : pruningOK candidates kept selected dominates = true) :
    pruningOK_prop candidates kept selected dominates := by
  simp only [pruningOK, Bool.and_eq_true_iff, List.all_eq_true, List.contains_iff,
    List.any_eq_true, Bool.or_eq_true_iff] at h
  obtain ⟨⟨hsel, hkept⟩, hexp⟩ := h
  refine ⟨hsel, ?_, ?_, ?_⟩
  · intro y hy
    have hy' := hkept y hy
    simp only [Bool.and_eq_true_iff] at hy'
    exact hy'.1
  · intro y hy
    have hy' := hkept y hy
    simp only [Bool.and_eq_true_iff] at hy'
    cases hdom : dominates y selected with
    | false => rfl
    | true => simp [hdom] at hy'
  · intro z hz
    rcases hexp z hz with hz | ⟨d, hd, hdom⟩
    · exact Or.inl hz
    · exact Or.inr ⟨d, hd, hdom⟩

def pairs {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=
  xs.flatMap (fun x => ys.map (fun y => (x, y)))

theorem mem_pairs {α β : Type} (xs : List α) (ys : List β) (a : α) (b : β) :
    (a, b) ∈ pairs xs ys ↔ a ∈ xs ∧ b ∈ ys := by
  simp [pairs, List.mem_flatMap, List.mem_map]

/-- Componentwise sum of local integer costs. Strict local dominance lifts. -/
def pairCost {α β : Type} (c1 : α → Nat → Int) (c2 : β → Nat → Int)
    (p : α × β) (i : Nat) : Int :=
  c1 p.1 i + c2 p.2 i

theorem sum_lifts_left {α β : Type} (axes : List Nat)
    (c1 : α → Nat → Int) (c2 : β → Nat → Int) (a a' : α) (b : β)
    (h : FiniteFrontier.strictPareto axes c1 a' a = true) :
    FiniteFrontier.strictPareto axes (pairCost c1 c2) (a', b) (a, b) = true := by
  have h' := (FiniteFrontier.pareto_exact axes c1 a' a).mp h
  apply (FiniteFrontier.pareto_exact axes (pairCost c1 c2) (a', b) (a, b)).mpr
  refine ⟨?_, ?_⟩
  · intro i hi
    simpa [pairCost] using Int.add_le_add_right (h'.1 i hi) (c2 b i)
  · obtain ⟨i, hi, hlt⟩ := h'.2
    exact ⟨i, hi, by simpa [pairCost] using Int.add_lt_add_right hlt (c2 b i)⟩

theorem sum_lifts_right {α β : Type} (axes : List Nat)
    (c1 : α → Nat → Int) (c2 : β → Nat → Int) (a : α) (b b' : β)
    (h : FiniteFrontier.strictPareto axes c2 b' b = true) :
    FiniteFrontier.strictPareto axes (pairCost c1 c2) (a, b') (a, b) = true := by
  have h' := (FiniteFrontier.pareto_exact axes c2 b' b).mp h
  apply (FiniteFrontier.pareto_exact axes (pairCost c1 c2) (a, b') (a, b)).mpr
  refine ⟨?_, ?_⟩
  · intro i hi
    simpa [pairCost] using Int.add_le_add_left (h'.1 i hi) (c1 a i)
  · obtain ⟨i, hi, hlt⟩ := h'.2
    exact ⟨i, hi, by simpa [pairCost] using Int.add_lt_add_left hlt (c1 a i)⟩

/-- Under product feasibility (the candidate set is exactly `pairs`) and
    componentwise-sum aggregation, a jointly nondominated pair has both
    components locally nondominated. -/
theorem joint_frontier_in_local_frontiers {α β : Type} (axes : List Nat)
    (c1 : α → Nat → Int) (c2 : β → Nat → Int)
    (xs : List α) (ys : List β) (a : α) (b : β)
    (h : (a, b) ∈ FiniteFrontier.frontier (pairs xs ys)
      (FiniteFrontier.strictPareto axes (pairCost c1 c2))) :
    a ∈ FiniteFrontier.frontier xs (FiniteFrontier.strictPareto axes c1) ∧
      b ∈ FiniteFrontier.frontier ys (FiniteFrontier.strictPareto axes c2) := by
  have hexact := (FiniteFrontier.frontier_exact _ _ (a, b)).mp h
  have hmem := (mem_pairs xs ys a b).mp hexact.1
  refine ⟨?_, ?_⟩
  · rw [FiniteFrontier.frontier_exact]
    refine ⟨hmem.1, ?_⟩
    intro a' ha'
    cases hdom : FiniteFrontier.strictPareto axes c1 a' a with
    | false => rfl
    | true =>
      have hpair : (a', b) ∈ pairs xs ys := (mem_pairs xs ys a' b).mpr ⟨ha', hmem.2⟩
      have hlift := sum_lifts_left axes c1 c2 a a' b hdom
      have hbad := hexact.2 (a', b) hpair
      simp [hlift] at hbad
  · rw [FiniteFrontier.frontier_exact]
    refine ⟨hmem.2, ?_⟩
    intro b' hb'
    cases hdom : FiniteFrontier.strictPareto axes c2 b' b with
    | false => rfl
    | true =>
      have hpair : (a, b') ∈ pairs xs ys := (mem_pairs xs ys a b').mpr ⟨hmem.1, hb'⟩
      have hlift := sum_lifts_right axes c1 c2 a b b' hdom
      have hbad := hexact.2 (a, b') hpair
      simp [hlift] at hbad

/-- Reduced product check. Nondomination against the product of the local
    frontiers implies nondomination against the full product, for componentwise
    sum. Local frontier membership may be supplied by either checker in
    `scalar_frontier_iff_allMinima`. -/
theorem reduced_product_sound {α β : Type} (axes : List Nat)
    (c1 : α → Nat → Int) (c2 : β → Nat → Int)
    (xs : List α) (ys : List β) (p : α × β)
    (hp : p ∈ pairs xs ys)
    (hred : ∀ a b,
      a ∈ FiniteFrontier.frontier xs (FiniteFrontier.strictPareto axes c1) →
      b ∈ FiniteFrontier.frontier ys (FiniteFrontier.strictPareto axes c2) →
      FiniteFrontier.strictPareto axes (pairCost c1 c2) (a, b) p = false) :
    p ∈ FiniteFrontier.frontier (pairs xs ys)
      (FiniteFrontier.strictPareto axes (pairCost c1 c2)) := by
  rw [FiniteFrontier.frontier_exact]
  refine ⟨hp, ?_⟩
  intro q hq
  cases hdom : FiniteFrontier.strictPareto axes (pairCost c1 c2) q p with
  | false => rfl
  | true =>
    have hq' := (mem_pairs xs ys q.1 q.2).mp (by
      have hqe : (q.1, q.2) = q := Prod.ext rfl rfl
      simpa [hqe] using hq)
    have hqe : (q.1, q.2) = q := Prod.ext rfl rfl
    rcases frontier_covers axes c1 xs q.1 hq'.1 with ha | ⟨a', ha', hda⟩
    · rcases frontier_covers axes c2 ys q.2 hq'.2 with hb | ⟨b', hb', hdb⟩
      · have hbad := hred q.1 q.2 ha hb
        rw [hqe] at hbad
        exact Bool.noConfusion (hdom.symm.trans hbad)
      · have hlift := sum_lifts_right axes c1 c2 q.1 q.2 b' hdb
        rw [hqe] at hlift
        have hchain := strictPareto_trans axes (pairCost c1 c2) (q.1, b') q p hlift hdom
        have hbad := hred q.1 b' ha hb'
        exact Bool.noConfusion (hchain.symm.trans hbad)
    · rcases frontier_covers axes c2 ys q.2 hq'.2 with hb | ⟨b', hb', hdb⟩
      · have hlift := sum_lifts_left axes c1 c2 q.1 a' q.2 hda
        rw [hqe] at hlift
        have hchain := strictPareto_trans axes (pairCost c1 c2) (a', q.2) q p hlift hdom
        have hbad := hred a' q.2 ha' hb
        exact Bool.noConfusion (hchain.symm.trans hbad)
      · have hleft := sum_lifts_left axes c1 c2 q.1 a' q.2 hda
        rw [hqe] at hleft
        have hmid := strictPareto_trans axes (pairCost c1 c2) (a', q.2) q p hleft hdom
        have hright := sum_lifts_right axes c1 c2 a' q.2 b' hdb
        have hchain := strictPareto_trans axes (pairCost c1 c2) (a', b') (a', q.2) p hright hmid
        have hbad := hred a' b' ha' hb'
        exact Bool.noConfusion (hchain.symm.trans hbad)

def localCostA : Nat → Nat → Int
  | 0, 0 => 0
  | 0, 1 => 2
  | 1, 0 => 2
  | 1, 1 => 0
  | _, _ => 0

def localCostB : Nat → Nat → Int
  | 0, 0 => 0
  | 0, 1 => 2
  | 1, 0 => 1
  | 1, 1 => 0
  | _, _ => 0

/-- Disproof: the product of local frontier members need not be jointly
    nondominated. Both components below are locally nondominated, and the pair
    `(1, 0)` is jointly dominated by `(0, 1)` under componentwise sum. -/
theorem product_of_frontiers_not_joint :
    ((FiniteFrontier.frontier [0, 1] (FiniteFrontier.strictPareto [0, 1] localCostA)).contains 1 &&
      (FiniteFrontier.frontier [0, 1] (FiniteFrontier.strictPareto [0, 1] localCostB)).contains 0 &&
      FiniteFrontier.strictPareto [0, 1] (pairCost localCostA localCostB) (0, 1) (1, 0) &&
      !((FiniteFrontier.frontier (pairs [0, 1] [0, 1])
          (FiniteFrontier.strictPareto [0, 1] (pairCost localCostA localCostB))).contains (1, 0))
    ) = true := by
  decide

def regressLocal : Nat → Nat → Int
  | 0, 0 => 5
  | 0, 1 => 0
  | 1, 0 => 5
  | 1, 1 => 3
  | _, _ => 0

/-- Aggregation that forgets every axis except the first. -/
def projectFirstCost (x : Nat) : Nat → Int
  | 0 => regressLocal x 0
  | _ => 0

inductive AggKind where
  | componentwiseSum
  | projectFirst
  deriving DecidableEq

/-- The reduced product theorem is stated only for componentwise sum.
    Project-first is refused because strict local dominance need not lift. -/
def reducedAllowed : AggKind → Bool
  | .componentwiseSum => true
  | .projectFirst => false

theorem strict_lift_needs_premise :
    FiniteFrontier.strictPareto [0, 1] regressLocal 0 1 = true ∧
      FiniteFrontier.strictPareto [0, 1] projectFirstCost 0 1 = false ∧
      reducedAllowed .projectFirst = false := by
  decide

theorem one_axis_strict {α : Type} (cost : α → Int) (y x : α) :
    FiniteFrontier.strictPareto [0] (fun a _ => cost a) y x = true ↔ cost y < cost x := by
  rw [FiniteFrontier.pareto_exact]
  simp only [List.mem_singleton]
  constructor
  · intro h
    obtain ⟨_, rfl, hlt⟩ := h.2
    exact hlt
  · intro h
    exact ⟨fun i hi => by subst i; exact Int.le_of_lt h, ⟨0, rfl, h⟩⟩

/-- Cross-complexity agreement. On one axis the linear selector
    `LinearSelection.allMinima` and the general Pareto filter define the same set.
    A product may cite either checker for a one-axis component. -/
theorem scalar_frontier_iff_allMinima {α : Type} (cost : α → Int) (xs : List α) (x : α) :
    x ∈ FiniteFrontier.frontier xs (FiniteFrontier.strictPareto [0] (fun a _ => cost a)) ↔
      x ∈ LinearSelection.allMinima cost xs := by
  rw [FiniteFrontier.frontier_exact, LinearSelection.allMinima_exact]
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨hx, ?_⟩
    intro y hy
    have hnot : ¬ cost y < cost x := by
      intro hlt
      have ht := (one_axis_strict cost y x).mpr hlt
      have hf := h y hy
      simp [ht] at hf
    exact Int.not_lt.mp hnot
  · rintro ⟨hx, hmin⟩
    refine ⟨hx, ?_⟩
    intro y hy
    cases ht : FiniteFrontier.strictPareto [0] (fun a _ => cost a) y x with
    | false => rfl
    | true =>
      have hlt := (one_axis_strict cost y x).mp ht
      exact absurd (Int.lt_of_lt_of_le hlt (hmin y hy)) (Int.lt_irrefl _)

inductive ComplexityClass where
  | linearScalar
  | finiteEnumeration
  | product (left right : ComplexityClass)
  deriving DecidableEq

/-- Candidate-generator coverage. This is not
    `SoftwareIsQuantifiable.Coverage.PlatformPremise`: platform mediation is not
    assumed, and no theorem here derives it. -/
structure GeneratorCoverage {α : Type} (candidates : List α) (intended : α → Prop) : Prop where
  complete : ∀ x, intended x → x ∈ candidates
  sound : ∀ x, x ∈ candidates → intended x

theorem frontier_respects_coverage {α : Type} (candidates : List α) (intended : α → Prop)
    (cov : GeneratorCoverage candidates intended) (dominates : α → α → Bool) (x : α)
    (hx : x ∈ FiniteFrontier.frontier candidates dominates) :
    intended x ∧ ∀ y, intended y → dominates y x = false := by
  have h := (FiniteFrontier.frontier_exact candidates dominates x).mp hx
  exact ⟨cov.sound x h.1, fun y hy => h.2 y (cov.complete y hy)⟩

theorem coverage_omission_can_dominate :
    let cost : Nat → Nat → Int := fun n _ => Int.ofNat n
    let dom := FiniteFrontier.strictPareto [0] cost
    ((FiniteFrontier.frontier [1] dom).contains 1 &&
      dom 0 1 && !([1].contains 0)) = true := by
  decide

theorem class_tag_is_not_coverage :
    ¬ (∀ (candidates : List Nat) (intended : Nat → Prop),
        GeneratorCoverage candidates intended) := by
  intro h
  have hmem := (h [1] (fun n => n = 0 ∨ n = 1)).complete 0 (Or.inl rfl)
  simp at hmem

/-- Ingestion premise: the modeled cost row is the observed cost row.
    This is not a cryptographic binding theorem. -/
structure ImportBinding (observed modeled : List Int) : Prop where
  agrees : observed = modeled

theorem frontier_transfers_under_import {α : Type}
    (observed modeled : List Int) (bind : ImportBinding observed modeled)
    (cost : List Int → α → Nat → Int) (axes : List Nat) (xs : List α) :
    FiniteFrontier.frontier xs (FiniteFrontier.strictPareto axes (cost observed)) =
      FiniteFrontier.frontier xs (FiniteFrontier.strictPareto axes (cost modeled)) := by
  rw [bind.agrees]

def rowCost (row : List Int) (candidate _axis : Nat) : Int :=
  if candidate = 0 then row.getD 0 0 else row.getD 1 0

theorem import_mismatch_blocks_transfer :
    FiniteFrontier.frontier [0, 1] (FiniteFrontier.strictPareto [0] (rowCost [1, 5])) ≠
      FiniteFrontier.frontier [0, 1] (FiniteFrontier.strictPareto [0] (rowCost [4, 0])) := by
  decide

def insertKey {α : Type} (key : α → Nat) (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if key x ≤ key y then x :: y :: ys else y :: insertKey key x ys

def sortKey {α : Type} (key : α → Nat) : List α → List α
  | [] => []
  | x :: xs => insertKey key x (sortKey key xs)

theorem mem_insertKey {α : Type} (key : α → Nat) (x y : α) (ys : List α) :
    y ∈ insertKey key x ys ↔ y = x ∨ y ∈ ys := by
  induction ys with
  | nil => simp [insertKey]
  | cons z zs ih =>
    simp only [insertKey]
    split
    · simp
    · constructor
      · intro h
        rcases List.mem_cons.mp h with rfl | h
        · exact Or.inr List.mem_cons_self
        · rcases ih.mp h with rfl | h
          · exact Or.inl rfl
          · exact Or.inr (List.mem_cons_of_mem z h)
      · intro h
        rcases h with rfl | h
        · exact List.mem_cons_of_mem z (ih.mpr (Or.inl rfl))
        · rcases List.mem_cons.mp h with rfl | h
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem z (ih.mpr (Or.inr h))

theorem mem_sortKey {α : Type} (key : α → Nat) (y : α) (xs : List α) :
    y ∈ sortKey key xs ↔ y ∈ xs := by
  induction xs with
  | nil => simp [sortKey]
  | cons x xs ih =>
    simp only [sortKey, mem_insertKey, List.mem_cons, ih]

/-- Canonical serialization preserves frontier membership. It does not claim
    that equal keys produce a unique list order. -/
theorem canonical_frontier_mem {α : Type} (key : α → Nat) (candidates : List α)
    (dominates : α → α → Bool) (x : α) :
    x ∈ sortKey key (FiniteFrontier.frontier candidates dominates) ↔
      x ∈ FiniteFrontier.frontier candidates dominates :=
  mem_sortKey key x _

#print axioms closure_compound_finite
#print axioms closure_factors_left
#print axioms closure_factors_right
#print axioms factorization_needs_separation
#print axioms hornDeriv_iff_closure
#print axioms frontier_covers
#print axioms pruning_sound_pareto
#print axioms joint_frontier_in_local_frontiers
#print axioms reduced_product_sound
#print axioms product_of_frontiers_not_joint
#print axioms strict_lift_needs_premise
#print axioms scalar_frontier_iff_allMinima
#print axioms frontier_respects_coverage
#print axioms class_tag_is_not_coverage
#print axioms import_mismatch_blocks_transfer
#print axioms union_misses_cross_consequence
end Optimality
