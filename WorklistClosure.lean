/- Worklist closure: a verified worklist refinement of the executable
   reference saturation in `ExecutableClosure`.

   What is proven here:
   - One worklist step adds exactly the rule heads whose premises are all
     already in the current state (`wstep_mem`).
   - Iterating that step from the roots is membership-monotone in the
     iteration count, stays inside the universe under the same boundedness
     hypotheses as the reference, and is a membership fixed point after at
     most `U.length + 1` iterations (`witer_fixed`): while the state is not
     fixed, the count of universe members in the state grows by at least
     one per step and is bounded by `U.length`.
   - The iteration is sound and complete for `Qualification.Derives`:
     membership at any stage derives (`witer_sound`), and every derivation
     lands in the fixed stage `U.length + 1` (`witer_complete`).
   - The checked worklist boundary therefore agrees exactly with the
     checked reference saturation (`worklist_agrees_checked`), so the
     exponential reference remains usable as a small-case differential
     oracle for the worklist.

   What is NOT claimed: no complexity bound is proven for the worklist
   (the fixed-point count bounds iterations, not the cost of a step), no
   list is claimed duplicate-free or sorted, and nothing is claimed about
   inputs whose roots or rule heads lie outside the universe beyond the
   checked boundary rejecting them.
-/
import Qualification
import ExecutableClosure

namespace WorklistClosure

variable {A : Type} [DecidableEq A]

/-- One worklist step: keep the current state and append the head of every
    rule whose premises are all already in the state. -/
def wstep (rules : List (List A × A)) (S : List A) : List A :=
  S ++ rules.filterMap
    (fun r => if r.1.all (fun p => decide (p ∈ S)) then some r.2 else none)

/-- Membership in one worklist step, stated without the implementation. -/
theorem wstep_mem {rules : List (List A × A)} {S : List A} {a : A} :
    a ∈ wstep rules S ↔
      a ∈ S ∨ ∃ r ∈ rules, r.2 = a ∧ ∀ p ∈ r.1, p ∈ S := by
  constructor
  · intro h
    simp only [wstep, List.mem_append, List.mem_filterMap] at h
    rcases h with h | ⟨r, hr, hstep⟩
    · exact Or.inl h
    · by_cases hall : r.1.all (fun p => decide (p ∈ S)) = true
      · rw [if_pos hall] at hstep
        refine Or.inr ⟨r, hr, Option.some.inj hstep, ?_⟩
        intro p hp
        have := List.all_eq_true.mp hall p hp
        exact of_decide_eq_true this
      · rw [if_neg hall] at hstep
        exact Option.noConfusion hstep
  · intro h
    simp only [wstep, List.mem_append, List.mem_filterMap]
    rcases h with h | ⟨r, hr, rfl, hprem⟩
    · exact Or.inl h
    · refine Or.inr ⟨r, hr, ?_⟩
      have hall : r.1.all (fun p => decide (p ∈ S)) = true := by
        rw [List.all_eq_true]
        intro p hp
        exact decide_eq_true (hprem p hp)
      rw [if_pos hall]

/-- The worklist iteration from the seed roots: stage `0` is the roots and
    each later stage is one `wstep` of the previous stage. -/
def witer (rules : List (List A × A)) (B : List A) : Nat → List A
  | 0 => B
  | n + 1 => wstep rules (witer rules B n)

/-- Unfolding equation for the successor stage. -/
theorem witer_succ (rules : List (List A × A)) (B : List A) (n : Nat) :
    witer rules B (n + 1) = wstep rules (witer rules B n) := rfl

/-- A worklist step never removes members. -/
theorem wstep_inflationary {rules : List (List A × A)} {S : List A} {a : A}
    (h : a ∈ S) : a ∈ wstep rules S :=
  (wstep_mem).mpr (Or.inl h)

/-- A worklist step is membership-monotone in the state. -/
theorem wstep_mono {rules : List (List A × A)} {S T : List A}
    (h : ∀ a, a ∈ S → a ∈ T) {a : A} (ha : a ∈ wstep rules S) :
    a ∈ wstep rules T := by
  rw [wstep_mem] at ha ⊢
  rcases ha with ha | ⟨r, hr, rfl, hprem⟩
  · exact Or.inl (h a ha)
  · exact Or.inr ⟨r, hr, rfl, fun p hp => h p (hprem p hp)⟩

/-- Two states with the same membership have steps with the same
    membership: the step depends only on the membership of its state. -/
theorem wstep_ext {rules : List (List A × A)} {S T : List A}
    (h : ∀ a, a ∈ S ↔ a ∈ T) {a : A} :
    a ∈ wstep rules S ↔ a ∈ wstep rules T := by
  constructor
  · exact wstep_mono (fun x hx => (h x).mp hx)
  · exact wstep_mono (fun x hx => (h x).mpr hx)

/-- Membership grows along the iteration: each stage is contained in the
    next one. -/
theorem witer_step_mono (rules : List (List A × A)) (B : List A) (n : Nat)
    {a : A} (h : a ∈ witer rules B n) : a ∈ witer rules B (n + 1) := by
  rw [witer_succ]
  exact wstep_inflationary h

/-- Membership grows with the iteration count. -/
theorem witer_mono {rules : List (List A × A)} {B : List A} {m n : Nat}
    (h : m ≤ n) {a : A} (ha : a ∈ witer rules B m) :
    a ∈ witer rules B n := by
  induction h with
  | refl => exact ha
  | step hmn ih => exact witer_step_mono rules B _ ih

/-- Under the reference boundedness hypotheses, every member of every
    stage is in the universe. -/
theorem witer_bounded {U B : List A} {rules : List (List A × A)}
    (rootsBounded : ∀ a, a ∈ B → a ∈ U)
    (headsBounded : ∀ ps a, (ps, a) ∈ rules → a ∈ U) :
    ∀ (n : Nat) {a : A}, a ∈ witer rules B n → a ∈ U := by
  intro n
  induction n with
  | zero => intro a ha; exact rootsBounded a ha
  | succ n ih =>
    intro a ha
    rw [witer_succ, wstep_mem] at ha
    rcases ha with ha | ⟨r, hr, rfl, -⟩
    · exact ih ha
    · exact headsBounded r.1 r.2 hr

/-- The count of universe members in a state: the termination measure for
    the iteration. It counts multiplicity in the universe list, which is
    all the argument needs. -/
def ucount (U S : List A) : Nat :=
  (U.filter (fun a => decide (a ∈ S))).length

omit [DecidableEq A] in
/-- Filtering a list by a pointwise weaker boolean predicate never gives
    a longer list. -/
theorem filter_length_mono {p q : A → Bool}
    (h : ∀ a, p a = true → q a = true) :
    ∀ {l : List A}, (l.filter p).length ≤ (l.filter q).length := by
  intro l
  induction l with
  | nil => simp
  | cons b bs ih =>
    cases hpb : p b <;> cases hqb : q b
    · rw [List.filter_cons_of_neg (by simp [hpb]),
        List.filter_cons_of_neg (by simp [hqb])]
      exact ih
    · rw [List.filter_cons_of_neg (by simp [hpb]),
        List.filter_cons_of_pos hqb, List.length_cons]
      omega
    · have htrue : q b = true := h b hpb
      rw [hqb] at htrue
      exact Bool.noConfusion htrue
    · rw [List.filter_cons_of_pos hpb, List.filter_cons_of_pos hqb,
        List.length_cons, List.length_cons]
      exact Nat.succ_le_succ ih

omit [DecidableEq A] in
/-- Filtering a list by a pointwise weaker boolean predicate gives a
    strictly longer list when some member of the list passes the stronger
    predicate but not the weaker one. -/
theorem filter_length_lt {p q : A → Bool}
    (h : ∀ a, p a = true → q a = true)
    {a0 : A} (hq : q a0 = true) (hp : p a0 = false) :
    ∀ {l : List A}, a0 ∈ l → (l.filter p).length < (l.filter q).length := by
  intro l
  induction l with
  | nil => intro hm; exact absurd hm (by simp)
  | cons b bs ih =>
    intro hm
    have hmono := filter_length_mono h (l := bs)
    simp only [List.mem_cons] at hm
    cases hpb : p b <;> cases hqb : q b
    · rcases hm with rfl | hm
      · rw [hqb] at hq; exact Bool.noConfusion hq
      · rw [List.filter_cons_of_neg (by simp [hpb]),
          List.filter_cons_of_neg (by simp [hqb])]
        exact ih hm
    · rw [List.filter_cons_of_neg (by simp [hpb]),
        List.filter_cons_of_pos hqb, List.length_cons]
      omega
    · have htrue : q b = true := h b hpb
      rw [hqb] at htrue
      exact Bool.noConfusion htrue
    · rcases hm with rfl | hm
      · rw [hpb] at hp; exact Bool.noConfusion hp
      · rw [List.filter_cons_of_pos hpb, List.filter_cons_of_pos hqb,
          List.length_cons, List.length_cons]
        exact Nat.succ_lt_succ (ih hm)

/-- The measure never exceeds the size of the universe. -/
theorem ucount_le (U S : List A) : ucount U S ≤ U.length :=
  List.length_filter_le _ _

/-- The measure is monotone in the state, membership-wise. -/
theorem ucount_mono {U S T : List A} (h : ∀ a, a ∈ S → a ∈ T) :
    ucount U S ≤ ucount U T :=
  filter_length_mono
    (fun a ha => decide_eq_true (h a (of_decide_eq_true ha)))

/-- The measure grows strictly when the state gains a universe member. -/
theorem ucount_lt_of_new {U S T : List A} {a0 : A}
    (h : ∀ a, a ∈ S → a ∈ T) (haU : a0 ∈ U) (haT : a0 ∈ T)
    (haS : a0 ∉ S) : ucount U S < ucount U T :=
  filter_length_lt
    (fun a ha => decide_eq_true (h a (of_decide_eq_true ha)))
    (decide_eq_true haT) (by simp [haS]) haU

/-- Once a stage is a membership fixed point, every later stage has
    exactly the same membership. -/
theorem witer_eq_of_fixed {rules : List (List A × A)} {B : List A} {m : Nat}
    (hfixed : ∀ a, a ∈ wstep rules (witer rules B m) ↔ a ∈ witer rules B m)
    {n : Nat} (hmn : m ≤ n) :
    ∀ a, a ∈ witer rules B n ↔ a ∈ witer rules B m := by
  induction hmn with
  | refl => intro a; exact Iff.rfl
  | step _ ih =>
    intro a
    rw [witer_succ]
    exact Iff.trans (wstep_ext ih) (hfixed a)

/-- The counting heart of the termination argument: at every stage, either
    some earlier stage was already a membership fixed point, or the
    measure has grown at least once per step taken. -/
theorem witer_progress {U B : List A} {rules : List (List A × A)}
    (rootsBounded : ∀ a, a ∈ B → a ∈ U)
    (headsBounded : ∀ ps a, (ps, a) ∈ rules → a ∈ U) :
    ∀ n, (∃ m ≤ n, ∀ a, a ∈ wstep rules (witer rules B m) ↔
            a ∈ witer rules B m) ∨
          n ≤ ucount U (witer rules B n) := by
  intro n
  induction n with
  | zero => exact Or.inr (Nat.zero_le _)
  | succ n ih =>
    rcases ih with ⟨m, hm, hfixed⟩ | hcnt
    · exact Or.inl ⟨m, Nat.le_succ_of_le hm, hfixed⟩
    · by_cases hall : ∀ a, a ∈ wstep rules (witer rules B n) →
          a ∈ witer rules B n
      · exact Or.inl ⟨n, Nat.le_succ n,
          fun a => ⟨hall a, fun ha => wstep_inflationary ha⟩⟩
      · obtain ⟨a, ha⟩ := Classical.not_forall.mp hall
        obtain ⟨haStep, haNot⟩ := not_imp.mp ha
        have haNext : a ∈ witer rules B (n + 1) := by
          rw [witer_succ]; exact haStep
        have haU : a ∈ U :=
          witer_bounded rootsBounded headsBounded (n + 1) haNext
        have hlt : ucount U (witer rules B n) <
            ucount U (witer rules B (n + 1)) :=
          ucount_lt_of_new (fun x hx => witer_step_mono rules B n hx)
            haU haNext haNot
        exact Or.inr (by omega)

/-- The stage `U.length + 1` is a membership fixed point of the worklist
    step: the measure would otherwise exceed the universe. -/
theorem witer_fixed {U B : List A} {rules : List (List A × A)}
    (rootsBounded : ∀ a, a ∈ B → a ∈ U)
    (headsBounded : ∀ ps a, (ps, a) ∈ rules → a ∈ U) :
    ∀ a, a ∈ wstep rules (witer rules B (U.length + 1)) ↔
      a ∈ witer rules B (U.length + 1) := by
  rcases witer_progress rootsBounded headsBounded (U.length + 1) with
    ⟨m, hm, hfixed⟩ | hcnt
  · intro a
    have heq : ∀ x, x ∈ witer rules B (U.length + 1) ↔
        x ∈ witer rules B m :=
      witer_eq_of_fixed hfixed hm
    exact Iff.trans (wstep_ext heq) (Iff.trans (hfixed a) (heq a).symm)
  · have hle := ucount_le U (witer rules B (U.length + 1))
    omega

/-- Every stage derives: soundness of the worklist iteration for the
    least-closure relation. -/
theorem witer_sound {B : List A} {rules : List (List A × A)} :
    ∀ (n : Nat) {a : A}, a ∈ witer rules B n →
      Qualification.Derives (fun a => a ∈ B)
        (fun ps a => (ps, a) ∈ rules) a := by
  intro n
  induction n with
  | zero => intro a ha; exact Qualification.Derives.root ha
  | succ n ih =>
    intro a ha
    rw [witer_succ, wstep_mem] at ha
    rcases ha with ha | ⟨r, hr, hEq, hprem⟩
    · exact ih ha
    · subst hEq
      apply Qualification.Derives.step (ps := r.1) (a := r.2)
      · simpa using hr
      · intro p hp; exact ih (hprem p hp)

/-- Every derivation lands in the fixed stage: completeness of the
    worklist iteration for the least-closure relation. The fixed stage
    contains the roots and is closed under the rules, membership-wise, so
    it contains the least closure. -/
theorem witer_complete {U B : List A} {rules : List (List A × A)}
    (rootsBounded : ∀ a, a ∈ B → a ∈ U)
    (headsBounded : ∀ ps a, (ps, a) ∈ rules → a ∈ U) {a : A}
    (h : Qualification.Derives (fun a => a ∈ B)
      (fun ps a => (ps, a) ∈ rules) a) :
    a ∈ witer rules B (U.length + 1) := by
  induction h with
  | root hb =>
    exact witer_mono (Nat.zero_le _) hb
  | step hr _hp ih =>
    apply (witer_fixed rootsBounded headsBounded _).mp
    rw [wstep_mem]
    exact Or.inr ⟨(_, _), hr, rfl, ih⟩

/-- The worklist closure result: the universe, filtered to the members of
    the fixed stage. Filtering by the universe is what makes the result a
    sublist of `U`, exactly like the reference result. -/
def wclose (U B : List A) (rules : List (List A × A)) : List A :=
  U.filter (fun a => decide (a ∈ witer rules B (U.length + 1)))

/-- The checked worklist boundary: reject out-of-universe roots or rule
    heads, using the reference boundary check, and otherwise return the
    worklist closure result. -/
def checkedWorklist (U B : List A) (rules : List (List A × A)) :
    Option (List A) :=
  if ExecutableClosure.boundedOK U B rules then some (wclose U B rules)
  else none

/-- Membership in the worklist closure result is exactly derivability,
    under the reference boundedness hypotheses. -/
theorem wclose_exact (U B : List A) (rules : List (List A × A))
    (rootsBounded : ∀ a, a ∈ B → a ∈ U)
    (headsBounded : ∀ ps a, (ps, a) ∈ rules → a ∈ U) (a : A) :
    a ∈ wclose U B rules ↔
      Qualification.Derives (fun a => a ∈ B)
        (fun ps a => (ps, a) ∈ rules) a := by
  constructor
  · intro h
    simp only [wclose, List.mem_filter, decide_eq_true_eq] at h
    exact witer_sound _ h.2
  · intro h
    have hw : a ∈ witer rules B (U.length + 1) :=
      witer_complete rootsBounded headsBounded h
    have hU : a ∈ U := witer_bounded rootsBounded headsBounded _ hw
    simp only [wclose, List.mem_filter, decide_eq_true_eq]
    exact ⟨hU, hw⟩

omit [DecidableEq A] in
/-- Two filters of the same list by boolean predicates that agree on
    every member of the list are equal. -/
theorem filter_eq_of_forall_mem {p q : A → Bool} {l : List A}
    (h : ∀ a, a ∈ l → (p a = true ↔ q a = true)) :
    l.filter p = l.filter q := by
  induction l with
  | nil => simp
  | cons b bs ih =>
    have hb := h b List.mem_cons_self
    have ih' := ih (fun a ha => h a (List.mem_cons_of_mem b ha))
    cases hpb : p b <;> cases hqb : q b
    · rw [List.filter_cons_of_neg (by simp [hpb]),
        List.filter_cons_of_neg (by simp [hqb]), ih']
    · simp [hpb, hqb] at hb
    · simp [hpb, hqb] at hb
    · rw [List.filter_cons_of_pos hpb, List.filter_cons_of_pos hqb, ih']

/-- The bridge: the checked worklist and the checked reference saturation
    are the same executable boundary. On the bounded side both results
    are the universe filtered by membership predicates that agree on
    every universe member, since both characterize derivability; on the
    unbounded side both reject. -/
theorem worklist_agrees_checked (U B : List A)
    (rules : List (List A × A)) :
    checkedWorklist U B rules = ExecutableClosure.checkedClose U B rules := by
  by_cases hbound : (∀ a, a ∈ B → a ∈ U) ∧
      (∀ ps a, (ps, a) ∈ rules → a ∈ U)
  · have hok : ExecutableClosure.boundedOK U B rules = true :=
      (ExecutableClosure.boundedOK_exact U B rules).mpr hbound
    have hcc : ExecutableClosure.checkedClose U B rules =
        some (ExecutableClosure.close U B rules) := by
      simp [ExecutableClosure.checkedClose, hok]
    obtain ⟨hb, hh, -⟩ :=
      ExecutableClosure.checkedClose_admitted U B rules _ hcc
    rw [hcc]
    show checkedWorklist U B rules = _
    unfold checkedWorklist
    rw [if_pos hok]
    congr 1
    apply filter_eq_of_forall_mem
    intro a haU
    constructor
    · intro hp
      have hd : Qualification.Derives (fun a => a ∈ B)
          (fun ps a => (ps, a) ∈ rules) a :=
        witer_sound _ (of_decide_eq_true hp)
      have hc : a ∈ ExecutableClosure.close U B rules :=
        (ExecutableClosure.close_exact U B rules hb hh a).mpr hd
      exact (List.mem_filter.mp hc).2
    · intro hq
      have hc : a ∈ ExecutableClosure.close U B rules :=
        List.mem_filter.mpr ⟨haU, hq⟩
      have hd : Qualification.Derives (fun a => a ∈ B)
          (fun ps a => (ps, a) ∈ rules) a :=
        (ExecutableClosure.close_exact U B rules hb hh a).mp hc
      exact decide_eq_true (witer_complete hb hh hd)
  · have hclose : ExecutableClosure.checkedClose U B rules = none :=
      (ExecutableClosure.checkedClose_rejects U B rules).mpr hbound
    have hwork : checkedWorklist U B rules = none := by
      unfold checkedWorklist
      by_cases hok : ExecutableClosure.boundedOK U B rules = true
      · exact absurd ((ExecutableClosure.boundedOK_exact U B rules).mp hok)
          hbound
      · rw [if_neg hok]
    rw [hwork, hclose]

#print axioms wclose_exact
#print axioms worklist_agrees_checked

#guard checkedWorklist [0] [1] [] == none
#guard checkedWorklist [0] [] [([], 1)] == none
#guard checkedWorklist [0, 1, 2] [0] [([0], 1), ([1], 2)] == some [0, 1, 2]
#guard checkedWorklist [0, 1, 2, 3] [0, 1] [([0, 1], 2), ([2], 3)] ==
  some [0, 1, 2, 3]
#guard checkedWorklist [0, 1, 2, 3] [0] [([0, 1], 2), ([2], 3)] == some [0]
#guard checkedWorklist [0, 1] [] [([0], 1), ([1], 0)] == some []
-- Differential control: the worklist and the reference agree on a
-- branching example where one rule's premise is absent (withdrawn), so
-- its head stays out while the other branch closes.
#guard checkedWorklist [0, 1, 2, 3] [0] [([0, 1], 2), ([0], 3)] ==
  ExecutableClosure.checkedClose [0, 1, 2, 3] [0] [([0, 1], 2), ([0], 3)]
#guard checkedWorklist [0, 1, 2, 3] [0] [([0, 1], 2), ([0], 3)] ==
  some [0, 3]

end WorklistClosure
