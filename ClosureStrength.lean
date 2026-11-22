import Qualification
import ExecutableClosure

/- Strongest reachable forms of three shared-core results, each with the
   standing controls that show what it keeps is necessary.

   A proof point here is Pareto optimal within its variant lattice when
   (1) its conclusion is an equivalence or an exact equation, so no
   conclusion of the same shape is stronger, and (2) removing any one of its
   premises makes the statement false, witnessed by a kernel-checked
   counterexample.  Points that fail (2) are dominated: a premise-free form
   below replaces them, and the old statement is re-derived from it.

   Scope: optimality among premise subsets and conclusion forms of the stated
   theorem, not over every possible theorem. -/
namespace ClosureStrength
open Qualification

/-! ## 1. Compounding over any family of sources, each with its own rules

`Qualification.compounding` closes both inputs under one shared rule set.
Here every source carries its own rules and is saturated under them only;
the joint closure is still recovered after one reclosure.  Premise-free and
an equivalence. -/

section Compounding
universe u v
variable {A : Type u}

theorem compounding_family {I : Sort v} (B : I → A → Prop) (R : I → List A → A → Prop)
    (a : A) :
    Derives (fun x => ∃ i, B i x) (fun ps x => ∃ i, R i ps x) a ↔
      Derives (fun x => ∃ i, Derives (B i) (R i) x) (fun ps x => ∃ i, R i ps x) a := by
  constructor
  · apply monotone _ (fun _ _ h => h) a
    intro x ⟨i, h⟩; exact ⟨i, .root h⟩
  · apply least _ (closed _ _) a
    intro x ⟨i, h⟩
    exact monotone (fun _ h => ⟨i, h⟩) (fun _ _ h => ⟨i, h⟩) x h

theorem compounding_sources (B C : A → Prop) (R S : List A → A → Prop) (a : A) :
    Derives (fun x => B x ∨ C x) (fun ps x => R ps x ∨ S ps x) a ↔
      Derives (fun x => Derives B R x ∨ Derives C S x) (fun ps x => R ps x ∨ S ps x) a := by
  constructor
  · apply monotone _ (fun _ _ h => h) a
    intro x h; exact h.elim (fun hb => Or.inl (.root hb)) (fun hc => Or.inr (.root hc))
  · apply least _ (closed _ _) a
    intro x h
    exact h.elim (monotone (fun _ h => Or.inl h) (fun _ _ h => Or.inl h) x)
      (monotone (fun _ h => Or.inr h) (fun _ _ h => Or.inr h) x)

/-- Derivation is invariant under pointwise-equivalent roots and rules. -/
theorem derives_congr {B B' : A → Prop} {R R' : List A → A → Prop}
    (hb : ∀ x, B x ↔ B' x) (hr : ∀ ps x, R ps x ↔ R' ps x) (a : A) :
    Derives B R a ↔ Derives B' R' a :=
  ⟨monotone (fun x h => (hb x).mp h) (fun ps x h => (hr ps x).mp h) a,
   monotone (fun x h => (hb x).mpr h) (fun ps x h => (hr ps x).mpr h) a⟩

/-- The binary form is the family form at index `Bool`. -/
theorem sources_of_family (B C : A → Prop) (R S : List A → A → Prop) (a : A) :
    Derives (fun x => B x ∨ C x) (fun ps x => R ps x ∨ S ps x) a ↔
      Derives (fun x => Derives B R x ∨ Derives C S x) (fun ps x => R ps x ∨ S ps x) a := by
  have k := compounding_family (fun b : Bool => cond b B C) (fun b : Bool => cond b R S) a
  have rules : ∀ ps x, (R ps x ∨ S ps x) ↔ ∃ b : Bool, cond b R S ps x := fun _ _ =>
    ⟨fun h => h.elim (fun h => ⟨true, h⟩) (fun h => ⟨false, h⟩),
     fun ⟨b, h⟩ => by cases b; exact Or.inr h; exact Or.inl h⟩
  refine (derives_congr (fun _ => ?_) rules a).trans
    (k.trans (derives_congr (fun _ => ?_) (fun ps x => (rules ps x).symm) a))
  · exact ⟨fun h => h.elim (fun h => ⟨true, h⟩) (fun h => ⟨false, h⟩),
      fun ⟨b, h⟩ => by cases b; exact Or.inr h; exact Or.inl h⟩
  · exact ⟨fun ⟨b, h⟩ => by cases b; exact Or.inr h; exact Or.inl h,
      fun h => h.elim (fun h => ⟨true, h⟩) (fun h => ⟨false, h⟩)⟩

/-- `Qualification.compounding` is the shared-rule instance `R = S`. -/
theorem compounding_of_sources (B C : A → Prop) (R : List A → A → Prop) (a : A) :
    Derives (fun x => B x ∨ C x) R a ↔
      Derives (fun x => Derives B R x ∨ Derives C R x) R a := by
  have collapse : ∀ (X : A → Prop) x,
      Derives X (fun ps x => R ps x ∨ R ps x) x ↔ Derives X R x := fun X x =>
    ⟨monotone (fun _ h => h) (fun _ _ h => h.elim id id) x,
     monotone (fun _ h => h) (fun _ _ h => Or.inl h) x⟩
  rw [← collapse _ a, ← collapse (fun x => Derives B R x ∨ Derives C R x) a]
  exact compounding_sources B C R R a

end Compounding

/-! Controls: reclosure is necessary, and the per-source input is a different
object from the shared-rule input. -/

/-- Dropping reclosure: the union of per-source closures misses a joint
consequence. -/
theorem union_without_reclosure_fails :
    let B : Nat → Prop := fun x => x = 0
    let C : Nat → Prop := fun x => x = 1
    let R : List Nat → Nat → Prop := fun ps x => ps = [0, 1] ∧ x = 2
    let S : List Nat → Nat → Prop := fun _ _ => False
    Derives (fun x => B x ∨ C x) (fun ps x => R ps x ∨ S ps x) 2 ∧
      ¬ (Derives B R 2 ∨ Derives C S 2) := by
  intro B C R S
  refine ⟨.step (Or.inl ⟨rfl, rfl⟩) (fun p hp => ?_), ?_⟩
  · simp at hp
    rcases hp with rfl | rfl
    · exact .root (Or.inl rfl)
    · exact .root (Or.inr rfl)
  · rintro (h | h)
    · cases h with
      | root hb => exact absurd hb (by decide)
      | step hr hp =>
        obtain ⟨rfl, -⟩ := hr
        have h1 := hp 1 (by simp)
        cases h1 with
        | root hb => exact absurd hb (by decide)
        | step hr _ => exact absurd hr.2 (by decide)
    · cases h with
      | root hb => exact absurd hb (by decide)
      | step hr _ => exact hr

/-- Saturating a source under its own rules can miss what the joint rules
derive, so the per-source left input is not the shared-rule left input. -/
theorem per_source_input_differs :
    ¬ Derives (fun x : Nat => x = 0) (fun _ _ => False) 1 ∧
      Derives (fun x : Nat => x = 0) (fun ps x => False ∨ (ps = [0] ∧ x = 1)) 1 := by
  refine ⟨fun h => ?_, .step (Or.inr ⟨rfl, rfl⟩) (fun p hp => by simp at hp; subst hp; exact .root rfl)⟩
  cases h with
  | root hb => exact absurd hb (by decide)
  | step hr _ => exact hr

/-! ## 2. The executable closure is monotone with no domain premises

`ExecutableClosure.executable_monotone` assumes every root and rule head of
both inputs lies in the universe.  None of those four premises is needed:
growing roots or rules can only remove models, and the closure is the
intersection of the models, so it can only grow. -/

section Executable
variable {A : Type} [DecidableEq A]
open ExecutableClosure

theorem modelOK_anti {B C : List A} {R S : List (List A × A)}
    (rb : ∀ a, a ∈ B → a ∈ C) (rr : ∀ r, r ∈ R → r ∈ S) (X : List A)
    (h : modelOK C S X = true) : modelOK B R X = true := by
  simp only [modelOK, Bool.and_eq_true, List.all_eq_true] at h ⊢
  exact ⟨fun a ha => h.1 a (rb a ha), fun r hr => h.2 r (rr r hr)⟩

theorem close_monotone (U B C : List A) (R S : List (List A × A))
    (rootSubset : ∀ a, a ∈ B → a ∈ C)
    (ruleSubset : ∀ ps a, (ps, a) ∈ R → (ps, a) ∈ S) :
    ∀ a, a ∈ close U B R → a ∈ close U C S := by
  intro a h
  simp only [close, List.mem_filter, List.all_eq_true] at h ⊢
  refine ⟨h.1, fun X hx => h.2 X ?_⟩
  simp only [models, List.mem_filter] at hx ⊢
  exact ⟨hx.1, modelOK_anti rootSubset (fun r hr => ruleSubset r.1 r.2 hr) X hx.2⟩

/-- The old statement, re-derived: its four domain premises go unused. -/
theorem executable_monotone_of_free (U B C : List A) (R S : List (List A × A))
    (_hb : ∀ a, a ∈ B → a ∈ U) (_hc : ∀ a, a ∈ C → a ∈ U)
    (_hr : ∀ ps a, (ps,a) ∈ R → a ∈ U) (_hs : ∀ ps a, (ps,a) ∈ S → a ∈ U)
    (rootSubset : ∀ a, a ∈ B → a ∈ C)
    (ruleSubset : ∀ ps a, (ps,a) ∈ R → (ps,a) ∈ S) :
    ∀ a, a ∈ close U B R → a ∈ close U C S :=
  close_monotone U B C R S rootSubset ruleSubset

/-- Order independence, also with no domain premises. -/
theorem close_order_independent_free (U B C : List A) (R S : List (List A × A))
    (sameRoots : ∀ a, a ∈ B ↔ a ∈ C)
    (sameRules : ∀ ps a, (ps,a) ∈ R ↔ (ps,a) ∈ S) :
    ∀ a, a ∈ close U B R ↔ a ∈ close U C S := fun a =>
  ⟨close_monotone U B C R S (fun a => (sameRoots a).mp) (fun ps a => (sameRules ps a).mp) a,
   close_monotone U C B S R (fun a => (sameRoots a).mpr) (fun ps a => (sameRules ps a).mpr) a⟩

end Executable

/-! Controls: `close_exact` keeps both of its domain premises for a reason.
Each one dropped alone breaks exactness (the closure over-approximates when
no subset of the universe is a model). -/

theorem close_exact_needs_roots :
    3 ∈ ExecutableClosure.close [3] [5] [] ∧
      ¬ Derives (fun a : Nat => a ∈ [5]) (fun ps a => (ps, a) ∈ ([] : List (List Nat × Nat))) 3 := by
  refine ⟨by decide, fun h => ?_⟩
  cases h with
  | root hb => exact absurd hb (by decide)
  | step hr _ => exact absurd hr (by simp)

theorem close_exact_needs_heads :
    1 ∈ ExecutableClosure.close [0, 1] [0] [([0], 5)] ∧
      ¬ Derives (fun a : Nat => a ∈ [0]) (fun ps a => (ps, a) ∈ [([0], 5)]) 1 := by
  refine ⟨by decide, fun h => ?_⟩
  cases h with
  | root hb => exact absurd hb (by decide)
  | step hr _ => simp at hr

/-- The monotone conclusion cannot be an equality: appending can add. -/
theorem close_monotone_strict :
    ¬ (2 ∈ ExecutableClosure.close [0, 1, 2] [0] [([0, 1], 2)]) ∧
      2 ∈ ExecutableClosure.close [0, 1, 2] [0, 1] [([0, 1], 2)] := by
  decide

#print axioms compounding_family
#print axioms compounding_sources
#print axioms derives_congr
#print axioms sources_of_family
#print axioms compounding_of_sources
#print axioms union_without_reclosure_fails
#print axioms per_source_input_differs
#print axioms close_monotone
#print axioms executable_monotone_of_free
#print axioms close_order_independent_free
#print axioms close_exact_needs_roots
#print axioms close_exact_needs_heads
#print axioms close_monotone_strict
end ClosureStrength
