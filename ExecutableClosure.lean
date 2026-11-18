import Qualification
import Std
namespace ExecutableClosure
variable {A : Type} [DecidableEq A]

def subsets : List A → List (List A)
  | [] => [[]]
  | a :: as => subsets as ++ (subsets as).map (a :: ·)

omit [DecidableEq A] in
theorem subset_members {U X : List A} (h : X ∈ subsets U) :
    ∀ a, a ∈ X → a ∈ U := by
  induction U generalizing X with
  | nil => simp [subsets] at h; subst X; simp
  | cons b bs ih =>
    simp only [subsets, List.mem_append, List.mem_map] at h
    rcases h with h | ⟨Y, hy, rfl⟩
    · intro a ha; exact List.mem_cons_of_mem b (ih h a ha)
    · intro a ha
      simp only [List.mem_cons] at ha ⊢
      rcases ha with rfl | ha
      · exact Or.inl rfl
      · exact Or.inr (ih hy a ha)

omit [DecidableEq A] in
theorem filter_member (U : List A) (p : A → Bool) : U.filter p ∈ subsets U := by
  induction U with
  | nil => simp [subsets]
  | cons a as ih =>
    cases h : p a <;> simp [List.filter_cons, h, subsets, ih]

omit [DecidableEq A] in
theorem subsets_count (U : List A) : (subsets U).length = 2 ^ U.length := by
  induction U with
  | nil => rfl
  | cons a as ih => simp [subsets, ih, Nat.pow_succ, Nat.mul_two]

def ruleOK (X : List A) (r : List A × A) : Bool :=
  !(r.1.all (fun a => X.contains a)) || X.contains r.2

def modelOK (B : List A) (rules : List (List A × A)) (X : List A) : Bool :=
  B.all (fun a => X.contains a) && rules.all (ruleOK X)

def models (U B : List A) (rules : List (List A × A)) : List (List A) :=
  (subsets U).filter (modelOK B rules)

def close (U B : List A) (rules : List (List A × A)) : List A :=
  U.filter (fun a => (models U B rules).all (fun X => X.contains a))

theorem ruleOK_exact (X : List A) (r : List A × A) :
    ruleOK X r = true ↔ ((∀ a, a ∈ r.1 → a ∈ X) → r.2 ∈ X) := by
  simp [ruleOK, Bool.or_eq_true, List.all_eq_true, List.contains_iff]
  constructor
  · intro h hp
    rcases h with ⟨x, hx, hn⟩ | h
    · exact False.elim (hn (hp x hx))
    · exact h
  · intro h
    by_cases hp : ∀ a, a ∈ r.1 → a ∈ X
    · exact Or.inr (h hp)
    · obtain ⟨x, hx⟩ := Classical.not_forall.mp hp
      have hh := not_imp.mp hx
      exact Or.inl ⟨x, hh.1, hh.2⟩

theorem modelOK_exact (B : List A) (rules : List (List A × A)) (X : List A) :
    modelOK B rules X = true ↔
      (∀ a, a ∈ B → a ∈ X) ∧
      Qualification.Closed (fun ps a => (ps,a) ∈ rules) (fun a => a ∈ X) := by
  simp only [modelOK, Bool.and_eq_true, List.all_eq_true, List.contains_iff]
  constructor
  · rintro ⟨hb, hr⟩
    refine ⟨hb, ?_⟩
    intro ps a h hp
    exact (ruleOK_exact X (ps,a)).mp (hr (ps,a) h) hp
  · rintro ⟨hb, hr⟩
    refine ⟨hb, ?_⟩
    intro r h
    exact (ruleOK_exact X r).mpr (hr r.1 r.2 h)

theorem close_exact (U B : List A) (rules : List (List A × A))
    (rootsBounded : ∀ a, a ∈ B → a ∈ U)
    (headsBounded : ∀ ps a, (ps,a) ∈ rules → a ∈ U) (a : A) :
    a ∈ close U B rules ↔
      Qualification.Derives (fun a => a ∈ B) (fun ps a => (ps,a) ∈ rules) a := by
  classical
  let D := Qualification.Derives (fun a => a ∈ B) (fun ps a => (ps,a) ∈ rules)
  have db : ∀ a, D a → a ∈ U := by
    apply Qualification.least rootsBounded
    intro ps a h _
    exact headsBounded ps a h
  have exactModel : modelOK B rules (U.filter (fun a => decide (D a))) = true := by
    apply (modelOK_exact B rules _).mpr
    constructor
    · intro a ha
      simp only [List.mem_filter, decide_eq_true_eq]
      exact ⟨rootsBounded a ha, Qualification.Derives.root ha⟩
    · intro ps a hr hp
      simp only [List.mem_filter, decide_eq_true_eq] at hp ⊢
      exact ⟨headsBounded ps a hr, Qualification.Derives.step hr (fun p h => (hp p h).2)⟩
  constructor
  · intro h
    simp only [close, List.mem_filter, List.all_eq_true, List.contains_iff] at h
    have hm : U.filter (fun a => decide (D a)) ∈ models U B rules := by
      simp only [models, List.mem_filter]
      exact ⟨filter_member U _, exactModel⟩
    have hd := h.2 _ hm
    exact of_decide_eq_true (List.mem_filter.mp hd).2
  · intro h
    simp only [close, List.mem_filter, List.all_eq_true, List.contains_iff]
    refine ⟨db a h, ?_⟩
    intro X hx
    have hm : modelOK B rules X = true := (List.mem_filter.mp hx).2
    obtain ⟨hb, hr⟩ := (modelOK_exact B rules X).mp hm
    exact Qualification.least hb hr a h

-- The executable reference result is closed and includes every live root.
theorem close_is_closed (U B : List A) (rules : List (List A × A))
    (hb : ∀ a, a ∈ B → a ∈ U)
    (hr : ∀ ps a, (ps,a) ∈ rules → a ∈ U) :
    Qualification.Closed (fun ps a => (ps,a) ∈ rules)
      (fun a => a ∈ close U B rules) := by
  intro ps a h hp
  apply (close_exact U B rules hb hr a).mpr
  exact Qualification.Derives.step h (fun p hm => (close_exact U B rules hb hr p).mp (hp p hm))

theorem close_contains_roots (U B : List A) (rules : List (List A × A))
    (hb : ∀ a, a ∈ B → a ∈ U)
    (hr : ∀ ps a, (ps,a) ∈ rules → a ∈ U) :
    ∀ a, a ∈ B → a ∈ close U B rules := by
  intro a h
  exact (close_exact U B rules hb hr a).mpr (Qualification.Derives.root h)

-- Duplicated/reordered roots and rules have exactly the same executable result membership.
theorem close_order_independent (U B C : List A) (R S : List (List A × A))
    (hb : ∀ a, a ∈ B → a ∈ U) (hc : ∀ a, a ∈ C → a ∈ U)
    (hr : ∀ ps a, (ps,a) ∈ R → a ∈ U) (hs : ∀ ps a, (ps,a) ∈ S → a ∈ U)
    (sameRoots : ∀ a, a ∈ B ↔ a ∈ C)
    (sameRules : ∀ ps a, (ps,a) ∈ R ↔ (ps,a) ∈ S) :
    ∀ a, a ∈ close U B R ↔ a ∈ close U C S := by
  intro a
  rw [close_exact U B R hb hr a, close_exact U C S hc hs a]
  exact ⟨Qualification.monotone (fun a => (sameRoots a).mp) (fun ps a => (sameRules ps a).mp) a,
         Qualification.monotone (fun a => (sameRoots a).mpr) (fun ps a => (sameRules ps a).mpr) a⟩

-- Includes withdrawal as the case where the new live roots/rules are subsets.
theorem executable_monotone (U B C : List A) (R S : List (List A × A))
    (hb : ∀ a, a ∈ B → a ∈ U) (hc : ∀ a, a ∈ C → a ∈ U)
    (hr : ∀ ps a, (ps,a) ∈ R → a ∈ U) (hs : ∀ ps a, (ps,a) ∈ S → a ∈ U)
    (rootSubset : ∀ a, a ∈ B → a ∈ C)
    (ruleSubset : ∀ ps a, (ps,a) ∈ R → (ps,a) ∈ S) :
    ∀ a, a ∈ close U B R → a ∈ close U C S := by
  intro a h
  apply (close_exact U C S hc hs a).mpr
  exact Qualification.monotone rootSubset ruleSubset a ((close_exact U B R hb hr a).mp h)

-- Public boundary: reject malformed/out-of-universe roots or rule heads.
def boundedOK (U B : List A) (rules : List (List A × A)) : Bool :=
  B.all (fun a => U.contains a) && rules.all (fun r => U.contains r.2)

def checkedClose (U B : List A) (rules : List (List A × A)) : Option (List A) :=
  if boundedOK U B rules then some (close U B rules) else none

theorem boundedOK_exact (U B : List A) (rules : List (List A × A)) :
    boundedOK U B rules = true ↔
      (∀ a, a ∈ B → a ∈ U) ∧ (∀ ps a, (ps,a) ∈ rules → a ∈ U) := by
  simp only [boundedOK, Bool.and_eq_true, List.all_eq_true, List.contains_iff]
  constructor
  · rintro ⟨hb, hr⟩
    exact ⟨hb, fun ps a h => hr (ps,a) h⟩
  · rintro ⟨hb, hr⟩
    exact ⟨hb, fun r h => hr r.1 r.2 h⟩

theorem checkedClose_admitted (U B : List A) (rules : List (List A × A))
    (out : List A) (h : checkedClose U B rules = some out) :
    (∀ a, a ∈ B → a ∈ U) ∧ (∀ ps a, (ps,a) ∈ rules → a ∈ U) ∧
      (∀ a, a ∈ out ↔
        Qualification.Derives (fun a => a ∈ B) (fun ps a => (ps,a) ∈ rules) a) := by
  unfold checkedClose at h
  split at h
  next ok =>
    have he : close U B rules = out := Option.some.inj h
    obtain ⟨hb, hr⟩ := (boundedOK_exact U B rules).mp ok
    exact ⟨hb, hr, fun a => he ▸ close_exact U B rules hb hr a⟩
  next bad => contradiction

theorem checkedClose_rejects (U B : List A) (rules : List (List A × A)) :
    checkedClose U B rules = none ↔
      ¬ ((∀ a, a ∈ B → a ∈ U) ∧ (∀ ps a, (ps,a) ∈ rules → a ∈ U)) := by
  simp only [checkedClose]
  split
  next ok =>
    simp only [Option.some_ne_none, false_iff]
    exact fun hn => hn ((boundedOK_exact U B rules).mp ok)
  next bad =>
    simp only [true_iff]
    exact fun h => bad ((boundedOK_exact U B rules).mpr h)

#print axioms boundedOK_exact
#print axioms checkedClose_admitted
#print axioms checkedClose_rejects
#guard checkedClose [0] [1] [] == none
#guard checkedClose [0] [] [([],1)] == none
#guard checkedClose [0,1,2] [0] [([0],1), ([1],2)] == some [0,1,2]

#print axioms subsets_count
#print axioms executable_monotone
#print axioms close_exact
#print axioms close_is_closed
#print axioms close_contains_roots
#print axioms close_order_independent
#eval close [0,1,2,3] [0,1] [([0,1],2), ([2],3)]
#guard close [0,1,2,3] [0,1] [([0,1],2), ([2],3)] == [0,1,2,3]
#guard close [0,1,2,3] [0] [([0,1],2), ([2],3)] == [0]
#guard close [0,1] [] [([0],1), ([1],0)] == []
end ExecutableClosure
