/- General Pareto bounds, aggregations, and frontier completeness.

   This module discharges the two open proof obligations of the general
   Pareto definition, for a named finite snapshot: named assignments,
   named workloads, named axes, and, for each assignment and workload, a
   finite list of executions, where each execution carries an exact cost
   vector (a function from axis index to cost).

   Obligation 1 (derived bounds are sound and attained). For each
   assignment and axis, the per-workload aggregated values are collected
   and the derived interval bound is their minimum and maximum.
   `bounds_sound` proves every collected value lies in the derived
   interval, and `bounds_attained` proves each end of a nonempty
   interval is the aggregated value of a named workload in the list.

   Obligation 2 (aggregations are well-defined). The named aggregations
   are the maximum, the minimum, and the sum of a workload's axis costs.
   `aggMax_perm`, `aggMin_perm`, and `aggSum_perm` prove the aggregated
   value does not depend on the order of the execution list, and the
   maximum and minimum characterizations prove each is a total function
   into `Option`: defined on every execution list, returning `none`
   exactly on the empty list, which is exactly the unwitnessed cell (a
   workload with no executions under that assignment).

   The module also proves the three-outcome decision on derived bounds:
   if the candidate interval lies weakly below the incumbent interval on
   every named axis and strictly below on one, then every realized
   candidate vector is componentwise no worse and somewhere strictly
   better than every realized incumbent vector (`separatedN_sound`), and
   hence strictly Pareto-dominates it for the concrete comparator
   (`separatedN_strictPareto`); if the intervals overlap on some named
   axis, neither direction is separated (`not_separatedN_of_overlap`),
   which is the honest undecided case. Finally, `frontier_complete`
   proves frontier completeness for the concrete strict Pareto
   comparator: every member of a named candidate list is in the frontier
   or is strictly dominated by a member of the frontier.

   Costs here are integers, the established cost type of this
   repository. The theorems are stated for integer costs; the bounds and
   aggregation content is independent of the cost representation, in
   that it uses only the order on costs (and, for the sum, its addition)
   and no other integer-specific structure.

   Not claimed: anything about assignments, workloads, executions, or
   candidates outside the named finite lists; anything about physical
   measurements, their stability, or the software that produced the
   executions; that a non-separated pair of bounds is dominated or
   undominated (only the overlapping case is proved undecided); that any
   one aggregation is the canonical choice (the derived bounds in this
   module use the worst-case maximum aggregation); or that the frontier
   of a named list says anything about candidates not in that list. -/

import FiniteFrontier
import Std
namespace GeneralPareto

/-- The maximum of a list of integers, as an option: `none` on the empty
    list, and otherwise the greatest member of the list. -/
def lmax : List Int → Option Int
  | [] => none
  | x :: xs =>
    match lmax xs with
    | none => some x
    | some m => if x ≤ m then some m else some x

/-- The minimum of a list of integers, as an option: `none` on the empty
    list, and otherwise the least member of the list. -/
def lmin : List Int → Option Int
  | [] => none
  | x :: xs =>
    match lmin xs with
    | none => some x
    | some m => if m ≤ x then some m else some x

/-- The maximum is `none` exactly on the empty list. -/
theorem lmax_none (l : List Int) : lmax l = none ↔ l = [] := by
  induction l with
  | nil => simp [lmax]
  | cons x xs ih =>
    simp only [lmax]
    cases h : lmax xs with
    | none => simp
    | some m =>
      by_cases hle : x ≤ m <;> simp [hle]

/-- The minimum is `none` exactly on the empty list. -/
theorem lmin_none (l : List Int) : lmin l = none ↔ l = [] := by
  induction l with
  | nil => simp [lmin]
  | cons x xs ih =>
    simp only [lmin]
    cases h : lmin xs with
    | none => simp
    | some m =>
      by_cases hle : m ≤ x <;> simp [hle]

/-- Exact characterization of the maximum: `lmax l = some m` exactly
    when `m` is a member of `l` and every member of `l` is at most `m`. -/
theorem lmax_eq_some (l : List Int) (m : Int) :
    lmax l = some m ↔ m ∈ l ∧ ∀ x ∈ l, x ≤ m := by
  induction l generalizing m with
  | nil => simp [lmax]
  | cons a as ih =>
    simp only [lmax]
    cases hmax : lmax as with
    | none =>
      have has : as = [] := (lmax_none as).mp hmax
      subst has
      simp [lmax]
      constructor
      · intro h; exact ⟨h.symm, by omega⟩
      · intro h; exact h.1.symm
    | some n =>
      obtain ⟨hnmem, hnmax⟩ := (ih n).mp hmax
      by_cases hle : a ≤ n
      · simp only [hle, if_true]
        constructor
        · intro h
          have hm : m = n := (Option.some.inj h).symm
          subst hm
          constructor
          · exact List.mem_cons_of_mem a hnmem
          · intro x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · omega
            · exact hnmax x hx
        · intro h
          obtain ⟨hmem, hbound⟩ := h
          have h1 : n ≤ m := hbound n (List.mem_cons_of_mem a hnmem)
          have h2 : m ≤ n := by
            rcases List.mem_cons.mp hmem with rfl | hm
            · exact hle
            · exact hnmax m hm
          have hnm : n = m := by omega
          rw [hnm]
      · simp only [hle, if_false]
        have han : n < a := by omega
        constructor
        · intro h
          have hm : m = a := (Option.some.inj h).symm
          subst hm
          constructor
          · exact List.mem_cons_self
          · intro x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · omega
            · have hxn := hnmax x hx; omega
        · intro h
          obtain ⟨hmem, hbound⟩ := h
          have h1 : a ≤ m := hbound a List.mem_cons_self
          have h2 : m ≤ a := by
            rcases List.mem_cons.mp hmem with rfl | hm
            · omega
            · have hmn := hnmax m hm; omega
          have ham : a = m := by omega
          rw [ham]

/-- Exact characterization of the minimum: `lmin l = some m` exactly
    when `m` is a member of `l` and `m` is at most every member of `l`. -/
theorem lmin_eq_some (l : List Int) (m : Int) :
    lmin l = some m ↔ m ∈ l ∧ ∀ x ∈ l, m ≤ x := by
  induction l generalizing m with
  | nil => simp [lmin]
  | cons a as ih =>
    simp only [lmin]
    cases hmin : lmin as with
    | none =>
      have has : as = [] := (lmin_none as).mp hmin
      subst has
      simp [lmin]
      constructor
      · intro h; exact ⟨h.symm, by omega⟩
      · intro h; exact h.1.symm
    | some n =>
      obtain ⟨hnmem, hnmin⟩ := (ih n).mp hmin
      by_cases hle : n ≤ a
      · simp only [hle, if_true]
        constructor
        · intro h
          have hm : m = n := (Option.some.inj h).symm
          subst hm
          constructor
          · exact List.mem_cons_of_mem a hnmem
          · intro x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · omega
            · exact hnmin x hx
        · intro h
          obtain ⟨hmem, hbound⟩ := h
          have h1 : m ≤ n := hbound n (List.mem_cons_of_mem a hnmem)
          have h2 : n ≤ m := by
            rcases List.mem_cons.mp hmem with rfl | hm
            · exact hle
            · exact hnmin m hm
          have hnm : n = m := by omega
          rw [hnm]
      · simp only [hle, if_false]
        have hna : a < n := by omega
        constructor
        · intro h
          have hm : m = a := (Option.some.inj h).symm
          subst hm
          constructor
          · exact List.mem_cons_self
          · intro x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · omega
            · have hxn := hnmin x hx; omega
        · intro h
          obtain ⟨hmem, hbound⟩ := h
          have h1 : m ≤ a := hbound a List.mem_cons_self
          have h2 : a ≤ m := by
            rcases List.mem_cons.mp hmem with rfl | hm
            · omega
            · have hmn := hnmin m hm; omega
          have ham : a = m := by omega
          rw [ham]

/-- Worst-case aggregation: the maximum of a list of axis costs. -/
def aggMax (l : List Int) : Option Int := lmax l

/-- Best-case aggregation: the minimum of a list of axis costs. -/
def aggMin (l : List Int) : Option Int := lmin l

/-- Total aggregation: the sum of a list of axis costs. -/
def aggSum (l : List Int) : Int := l.sum

-- Totality of aggregation: `aggMax` and `aggMin` are total functions
-- from execution lists to `Option Int`, defined on every workload's
-- execution list; by `lmax_none` and `lmin_none` they return `none`
-- exactly on the empty list, which is exactly the unwitnessed cell.

/-- Well-definedness of the maximum aggregation: reordering a
    workload's execution list does not change its aggregated value.
    This is derived from the exact characterization `lmax_eq_some`. -/
theorem aggMax_perm {l₁ l₂ : List Int} (h : List.Perm l₁ l₂) :
    aggMax l₁ = aggMax l₂ := by
  cases h₁ : aggMax l₁ with
  | none =>
    have he₁ : l₁ = [] := (lmax_none l₁).mp h₁
    subst he₁
    have he₂ : l₂ = [] := h.symm.eq_nil
    subst he₂
    rfl
  | some m =>
    cases h₂ : aggMax l₂ with
    | none =>
      have he₂ : l₂ = [] := (lmax_none l₂).mp h₂
      subst he₂
      have he₁ : l₁ = [] := h.eq_nil
      subst he₁
      simp [aggMax, lmax] at h₁
    | some n =>
      obtain ⟨hmem, hmax⟩ := (lmax_eq_some l₁ m).mp h₁
      obtain ⟨hnmem, hnmax⟩ := (lmax_eq_some l₂ n).mp h₂
      have hmn₁ : m ≤ n := hnmax m (h.mem_iff.mp hmem)
      have hmn₂ : n ≤ m := hmax n (h.symm.mem_iff.mp hnmem)
      have hmn : m = n := by omega
      rw [hmn]

/-- Well-definedness of the minimum aggregation: reordering a
    workload's execution list does not change its aggregated value.
    This is derived from the exact characterization `lmin_eq_some`. -/
theorem aggMin_perm {l₁ l₂ : List Int} (h : List.Perm l₁ l₂) :
    aggMin l₁ = aggMin l₂ := by
  cases h₁ : aggMin l₁ with
  | none =>
    have he₁ : l₁ = [] := (lmin_none l₁).mp h₁
    subst he₁
    have he₂ : l₂ = [] := h.symm.eq_nil
    subst he₂
    rfl
  | some m =>
    cases h₂ : aggMin l₂ with
    | none =>
      have he₂ : l₂ = [] := (lmin_none l₂).mp h₂
      subst he₂
      have he₁ : l₁ = [] := h.eq_nil
      subst he₁
      simp [aggMin, lmin] at h₁
    | some n =>
      obtain ⟨hmem, hmin⟩ := (lmin_eq_some l₁ m).mp h₁
      obtain ⟨hnmem, hnmin⟩ := (lmin_eq_some l₂ n).mp h₂
      have hmn₁ : n ≤ m := hnmin m (h.mem_iff.mp hmem)
      have hmn₂ : m ≤ n := hmin n (h.symm.mem_iff.mp hnmem)
      have hmn : m = n := by omega
      rw [hmn]

/-- Well-definedness of the sum aggregation: reordering a workload's
    execution list does not change its aggregated value, by induction
    on the permutation derivation. -/
theorem aggSum_perm {l₁ l₂ : List Int} (h : List.Perm l₁ l₂) :
    aggSum l₁ = aggSum l₂ := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [aggSum, List.sum_cons] at ih ⊢; rw [ih]
  | swap x y l => simp only [aggSum, List.sum_cons]; omega
  | trans _ _ ih₁ ih₂ => rw [ih₁, ih₂]


section Bounds

variable {A W : Type}

/-- The axis-`i` costs of every execution of workload `w` under assignment
    `a`, in execution-list order. An aggregation is applied to this list. -/
def axisValues (execs : A → W → List (Nat → Int)) (a : A) (w : W)
    (i : Nat) : List Int :=
  (execs a w).map (fun v => v i)

/-- The per-workload worst-case aggregated values on axis `i` under
    assignment `a`, one for each witnessed workload, in workload order.
    Unwitnessed workloads (no executions) contribute no value. -/
def values (workloads : List W) (execs : A → W → List (Nat → Int))
    (a : A) (i : Nat) : List Int :=
  workloads.filterMap (fun w => aggMax (axisValues execs a w i))

/-- The derived lower bound on axis `i` under assignment `a`: the minimum
    of the per-workload aggregated values, if any value exists. -/
def blo (workloads : List W) (execs : A → W → List (Nat → Int))
    (a : A) (i : Nat) : Option Int :=
  lmin (values workloads execs a i)

/-- The derived upper bound on axis `i` under assignment `a`: the maximum
    of the per-workload aggregated values, if any value exists. -/
def bhi (workloads : List W) (execs : A → W → List (Nat → Int))
    (a : A) (i : Nat) : Option Int :=
  lmax (values workloads execs a i)

/-- Obligation 1, soundness: every per-workload aggregated value on an
    axis lies between the derived lower and upper bounds for that
    assignment and axis; in particular both bounds exist whenever a
    value exists. -/
theorem bounds_sound {workloads : List W} {execs : A → W → List (Nat → Int)}
    {a : A} {i : Nat} {v : Int} (hv : v ∈ values workloads execs a i) :
    ∃ lo hi, blo workloads execs a i = some lo ∧
      bhi workloads execs a i = some hi ∧ lo ≤ v ∧ v ≤ hi := by
  cases hlo : blo workloads execs a i with
  | none =>
    exfalso
    have hlo' : lmin (values workloads execs a i) = none := hlo
    have hempty : values workloads execs a i = [] := (lmin_none _).mp hlo'
    rw [hempty] at hv
    exact List.not_mem_nil hv
  | some lo =>
    cases hhi : bhi workloads execs a i with
    | none =>
      exfalso
      have hhi' : lmax (values workloads execs a i) = none := hhi
      have hempty : values workloads execs a i = [] := (lmax_none _).mp hhi'
      rw [hempty] at hv
      exact List.not_mem_nil hv
    | some hi =>
      have hlo' : lmin (values workloads execs a i) = some lo := hlo
      have hhi' : lmax (values workloads execs a i) = some hi := hhi
      obtain ⟨_, hlole⟩ := (lmin_eq_some _ lo).mp hlo'
      obtain ⟨_, hhile⟩ := (lmax_eq_some _ hi).mp hhi'
      exact ⟨lo, hi, rfl, rfl, hlole v hv, hhile v hv⟩

/-- Obligation 1, attainment (discharge): when the per-workload value
    list is nonempty, each derived bound is attained, in that there is
    a named workload in the workload list whose aggregated value equals
    the bound. -/
theorem bounds_attained {workloads : List W}
    {execs : A → W → List (Nat → Int)} {a : A} {i : Nat}
    (hne : values workloads execs a i ≠ []) :
    (∃ w, w ∈ workloads ∧ ∃ lo, blo workloads execs a i = some lo ∧
      aggMax (axisValues execs a w i) = some lo) ∧
    (∃ w, w ∈ workloads ∧ ∃ hi, bhi workloads execs a i = some hi ∧
      aggMax (axisValues execs a w i) = some hi) := by
  constructor
  · cases hlo : blo workloads execs a i with
    | none =>
      exfalso
      have hlo' : lmin (values workloads execs a i) = none := hlo
      exact hne ((lmin_none _).mp hlo')
    | some lo =>
      have hlo' : lmin (values workloads execs a i) = some lo := hlo
      obtain ⟨hlomem, _⟩ := (lmin_eq_some _ lo).mp hlo'
      simp only [values, List.mem_filterMap] at hlomem
      obtain ⟨w, hw, hagg⟩ := hlomem
      exact ⟨w, hw, lo, rfl, hagg⟩
  · cases hhi : bhi workloads execs a i with
    | none =>
      exfalso
      have hhi' : lmax (values workloads execs a i) = none := hhi
      exact hne ((lmax_none _).mp hhi')
    | some hi =>
      have hhi' : lmax (values workloads execs a i) = some hi := hhi
      obtain ⟨hhimem, _⟩ := (lmax_eq_some _ hi).mp hhi'
      simp only [values, List.mem_filterMap] at hhimem
      obtain ⟨w, hw, hagg⟩ := hhimem
      exact ⟨w, hw, hi, rfl, hagg⟩

/-- Every single execution cost is at most the derived upper bound:
    an execution's axis cost is at most its own workload's worst-case
    aggregated value, which is at most the maximum over all workloads. -/
theorem execution_le_bhi {workloads : List W}
    {execs : A → W → List (Nat → Int)} {a : A} {w : W} {i : Nat}
    {e : Nat → Int} (hw : w ∈ workloads) (he : e ∈ execs a w)
    (hne : values workloads execs a i ≠ []) :
    ∃ hi, bhi workloads execs a i = some hi ∧ e i ≤ hi := by
  have hev : e i ∈ axisValues execs a w i := by
    simp only [axisValues, List.mem_map]
    exact ⟨e, he, rfl⟩
  cases hagg : aggMax (axisValues execs a w i) with
  | none =>
    exfalso
    have hagg' : lmax (axisValues execs a w i) = none := hagg
    have hempty : axisValues execs a w i = [] := (lmax_none _).mp hagg'
    rw [hempty] at hev
    exact List.not_mem_nil hev
  | some m =>
    have hagg' : lmax (axisValues execs a w i) = some m := hagg
    obtain ⟨_, hmax⟩ := (lmax_eq_some _ m).mp hagg'
    have hmvals : m ∈ values workloads execs a i := by
      simp only [values, List.mem_filterMap]
      exact ⟨w, hw, hagg⟩
    cases hhi : bhi workloads execs a i with
    | none =>
      exfalso
      have hhi' : lmax (values workloads execs a i) = none := hhi
      exact hne ((lmax_none _).mp hhi')
    | some hi =>
      have hhi' : lmax (values workloads execs a i) = some hi := hhi
      obtain ⟨_, hhimax⟩ := (lmax_eq_some _ hi).mp hhi'
      have h₁ : e i ≤ m := hmax (e i) hev
      have h₂ : m ≤ hi := hhimax m hmvals
      exact ⟨hi, rfl, by omega⟩

end Bounds


/-- A cost vector `x` realizes the bound assignment `b` on `axes` when
    every named axis cost of `x` lies in the interval assigned by `b`. -/
def realizes (axes : List Nat) (b : Nat → Int × Int) (x : Nat → Int) :
    Prop :=
  ∀ i, i ∈ axes → (b i).1 ≤ x i ∧ x i ≤ (b i).2

/-- The candidate bound assignment `cb` is separated from the incumbent
    bound assignment `ib` on `axes` when the candidate interval lies
    weakly below the incumbent interval on every named axis and strictly
    below it on at least one named axis. -/
def separatedN (axes : List Nat) (cb ib : Nat → Int × Int) : Prop :=
  (∀ i, i ∈ axes → (cb i).2 ≤ (ib i).1) ∧
    (∃ i, i ∈ axes ∧ (cb i).2 < (ib i).1)

/-- Soundness of the separated outcome: separated bound assignments
    decide strict Pareto dominance for every pair of realized vectors,
    componentwise no worse on every named axis and strictly better on
    at least one named axis. -/
theorem separatedN_sound {axes : List Nat} {cb ib : Nat → Int × Int}
    {x y : Nat → Int} (hsep : separatedN axes cb ib)
    (hx : realizes axes cb x) (hy : realizes axes ib y) :
    (∀ i, i ∈ axes → x i ≤ y i) ∧ (∃ i, i ∈ axes ∧ x i < y i) := by
  constructor
  · intro i hi
    have h₁ : x i ≤ (cb i).2 := (hx i hi).2
    have h₂ : (cb i).2 ≤ (ib i).1 := hsep.1 i hi
    have h₃ : (ib i).1 ≤ y i := (hy i hi).1
    omega
  · obtain ⟨i, hi, hlt⟩ := hsep.2
    refine ⟨i, hi, ?_⟩
    have h₁ : x i ≤ (cb i).2 := (hx i hi).2
    have h₃ : (ib i).1 ≤ y i := (hy i hi).1
    omega

/-- The separated outcome, stated for the concrete strict Pareto
    comparator of `FiniteFrontier` with the identity cost function. -/
theorem separatedN_strictPareto {axes : List Nat}
    {cb ib : Nat → Int × Int} {x y : Nat → Int}
    (hsep : separatedN axes cb ib) (hx : realizes axes cb x)
    (hy : realizes axes ib y) :
    FiniteFrontier.strictPareto axes (fun v i => v i) x y = true := by
  apply (FiniteFrontier.pareto_exact axes (fun v i => v i) x y).mpr
  exact separatedN_sound hsep hx hy

/-- The undecided outcome is honest: if the two intervals overlap on
    some named axis, then neither bound assignment is separated from
    the other, so the bounds alone decide nothing in that case. -/
theorem not_separatedN_of_overlap {axes : List Nat}
    {cb ib : Nat → Int × Int} {i : Nat} (hi : i ∈ axes)
    (h₁ : (ib i).1 < (cb i).2) (h₂ : (cb i).1 < (ib i).2) :
    ¬ separatedN axes cb ib ∧ ¬ separatedN axes ib cb := by
  constructor
  · intro hsep
    have hle : (cb i).2 ≤ (ib i).1 := hsep.1 i hi
    omega
  · intro hsep
    have hle : (ib i).2 ≤ (cb i).1 := hsep.1 i hi
    omega


/-- Minimal-element lemma for a Boolean relation with no self-loops and
    transitive positive steps: every nonempty finite list has an element
    that no member of the list strictly precedes. -/
theorem exists_minimal {A : Type} {d : A → A → Bool}
    (hirr : ∀ x, d x x = false)
    (htrans : ∀ x y z, d x y = true → d y z = true → d x z = true) :
    ∀ L : List A, L ≠ [] →
      ∃ m, m ∈ L ∧ ∀ y, y ∈ L → d y m = false := by
  intro L
  induction L with
  | nil =>
    intro hne
    exfalso
    exact hne rfl
  | cons a as ih =>
    intro _
    cases as with
    | nil =>
      refine ⟨a, List.mem_cons_self, ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hirr y
      · exfalso
        exact List.not_mem_nil hy
    | cons b bs =>
      obtain ⟨m, hm_mem, hm_min⟩ := ih (by simp)
      by_cases hdam : d a m = true
      · refine ⟨a, List.mem_cons_self, ?_⟩
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy_tail
        · exact hirr y
        · cases hya : d y a with
          | false => rfl
          | true =>
            exfalso
            have hym : d y m = true := htrans y a m hya hdam
            have hyf : d y m = false := hm_min y hy_tail
            rw [hym] at hyf
            exact Bool.noConfusion hyf
      · refine ⟨m, List.mem_cons_of_mem a hm_mem, ?_⟩
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy_tail
        · cases hval : d y m with
          | false => rfl
          | true => exfalso; exact hdam hval
        · exact hm_min y hy_tail

/-- The strict Pareto comparator is irreflexive: no candidate strictly
    dominates itself, since that would require a strictly cheaper axis
    than itself. -/
theorem strictPareto_irrefl {A : Type} {axes : List Nat}
    {cost : A → Nat → Int} (x : A) :
    FiniteFrontier.strictPareto axes cost x x = false := by
  cases h : FiniteFrontier.strictPareto axes cost x x with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨_, _, _, hlt⟩ :=
      (FiniteFrontier.pareto_exact axes cost x x).mp h
    omega

/-- The strict Pareto comparator is transitive on its positive steps. -/
theorem strictPareto_trans {A : Type} {axes : List Nat}
    {cost : A → Nat → Int} {x y z : A}
    (hxy : FiniteFrontier.strictPareto axes cost x y = true)
    (hyz : FiniteFrontier.strictPareto axes cost y z = true) :
    FiniteFrontier.strictPareto axes cost x z = true := by
  apply (FiniteFrontier.pareto_exact axes cost x z).mpr
  obtain ⟨hxy_le, i, hi_axes, hi_lt⟩ :=
    (FiniteFrontier.pareto_exact axes cost x y).mp hxy
  obtain ⟨hyz_le, _⟩ :=
    (FiniteFrontier.pareto_exact axes cost y z).mp hyz
  constructor
  · intro j hj
    have h₁ : cost x j ≤ cost y j := hxy_le j hj
    have h₂ : cost y j ≤ cost z j := hyz_le j hj
    omega
  · refine ⟨i, hi_axes, ?_⟩
    have h₂ : cost y i ≤ cost z i := hyz_le i hi_axes
    omega

/-- Frontier completeness for the strict Pareto comparator: every member
    of a finite candidate list is either itself in the frontier or is
    strictly Pareto-dominated by a member of the frontier. -/
theorem frontier_complete {A : Type} {axes : List Nat}
    {cost : A → Nat → Int} {L : List A} {x : A} (hx : x ∈ L) :
    x ∈ FiniteFrontier.frontier L
        (fun y z => FiniteFrontier.strictPareto axes cost y z) ∨
      ∃ y, y ∈ FiniteFrontier.frontier L
          (fun y z => FiniteFrontier.strictPareto axes cost y z) ∧
        FiniteFrontier.strictPareto axes cost y x = true := by
  obtain ⟨m, hmS, hm_min⟩ :=
    @exists_minimal A (fun y z => FiniteFrontier.strictPareto axes cost y z)
      (fun v => strictPareto_irrefl v)
      (fun p q r hpq hqr => strictPareto_trans hpq hqr)
      (x :: L.filter (fun y => FiniteFrontier.strictPareto axes cost y x))
      (by simp)
  have hmL : m ∈ L := by
    rcases List.mem_cons.mp hmS with rfl | hm_tail
    · exact hx
    · exact (List.mem_filter.mp hm_tail).1
  have hmx : m = x ∨ FiniteFrontier.strictPareto axes cost m x = true := by
    rcases List.mem_cons.mp hmS with rfl | hm_tail
    · exact Or.inl rfl
    · exact Or.inr (List.mem_filter.mp hm_tail).2
  have hm_frontier : m ∈ FiniteFrontier.frontier L
      (fun y z => FiniteFrontier.strictPareto axes cost y z) := by
    apply (FiniteFrontier.frontier_exact L
      (fun y z => FiniteFrontier.strictPareto axes cost y z) m).mpr
    refine ⟨hmL, ?_⟩
    intro y hyL
    cases hym : FiniteFrontier.strictPareto axes cost y m with
    | false => rfl
    | true =>
      exfalso
      have hyx : FiniteFrontier.strictPareto axes cost y x = true := by
        rcases hmx with rfl | hdmx
        · exact hym
        · exact strictPareto_trans hym hdmx
      have hyS : y ∈ x :: L.filter
          (fun y => FiniteFrontier.strictPareto axes cost y x) :=
        List.mem_cons_of_mem x (List.mem_filter.mpr ⟨hyL, hyx⟩)
      have hyf : FiniteFrontier.strictPareto axes cost y m = false :=
        hm_min y hyS
      rw [hym] at hyf
      exact Bool.noConfusion hyf
  rcases hmx with rfl | hdmx
  · exact Or.inl hm_frontier
  · exact Or.inr ⟨m, hm_frontier, hdmx⟩


/-- A concrete cost vector for the executable guards: axis `0` costs
    `x`, and every other axis (in particular axis `1`) costs `y`. -/
def guardVec (x y : Int) : Nat → Int
  | 0 => x
  | _ => y

/-- A concrete snapshot for the executable guards: two assignments, two
    workloads, two axes. Assignment `0` runs workload `0` twice and
    workload `1` once; assignment `1` runs workload `0` once and
    workload `1` not at all, so that cell is unwitnessed. -/
def guardExecs : Nat → Nat → List (Nat → Int)
  | 0, 0 => [guardVec 3 5, guardVec 7 2]
  | 0, 1 => [guardVec 4 6]
  | 1, 0 => [guardVec 1 9]
  | _, _ => []

#print axioms lmax_eq_some
#print axioms aggMax_perm
#print axioms bounds_sound
#print axioms bounds_attained
#print axioms separatedN_sound
#print axioms frontier_complete

-- Derived bounds of the concrete snapshot, computed by the kernel.
#guard blo [0, 1] guardExecs 0 0 == some 4
#guard bhi [0, 1] guardExecs 0 0 == some 7
#guard blo [0, 1] guardExecs 0 1 == some 5
#guard bhi [0, 1] guardExecs 0 1 == some 6
#guard blo [0, 1] guardExecs 1 0 == some 1
#guard bhi [0, 1] guardExecs 1 0 == some 1
#guard blo [0, 1] guardExecs 1 1 == some 9
#guard bhi [0, 1] guardExecs 1 1 == some 9
-- A permuted execution list gives the same aggregated value.
#guard aggMax [7, 3] == aggMax [3, 7]
#guard aggMax (axisValues guardExecs 0 0 0) ==
  aggMax (axisValues guardExecs 0 0 0).reverse
-- Negative control: an empty execution list aggregates to `none`; in
-- the snapshot this is the unwitnessed workload `1` under assignment `1`.
#guard aggMax [] == none
#guard aggMax (axisValues guardExecs 1 1 0) == none


end GeneralPareto
