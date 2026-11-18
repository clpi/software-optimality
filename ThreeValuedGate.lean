import ComparisonContract
import SoftwareIsQuantifiable.Interface
import CanonicalDominance
import FiniteFrontier

open SoftwareIsQuantifiable

namespace ThreeValuedGate

inductive Verdict where
  | pass
  | fail
  | unknown
  deriving DecidableEq, Repr

def boolGate (ok : Bool) : Verdict :=
  if ok then .pass else .fail

def reading (xs : List (Option Int)) (i : Nat) : Option Int :=
  (xs[i]?).join

def axisVerdict (c : ComparisonContract.Contract) (x y : List (Option Int)) (i : Nat) : Verdict :=
  match c.axes[i]? with
  | none => .unknown
  | some axis =>
    match reading x i, reading y i with
    | some xv, some yv =>
      boolGate (decide (ComparisonContract.normalize axis.direction xv ≤
        ComparisonContract.normalize axis.direction yv))
    | _, _ => .unknown

def strictAxis (c : ComparisonContract.Contract) (x y : List (Option Int)) (i : Nat) : Prop :=
  match c.axes[i]?, reading x i, reading y i with
  | some axis, some xv, some yv =>
    ComparisonContract.normalize axis.direction xv <
      ComparisonContract.normalize axis.direction yv
  | _, _, _ => False

def dominates (c : ComparisonContract.Contract) (x y : List (Option Int)) : Prop :=
  (∀ i, i ∈ List.range c.axes.length → axisVerdict c x y i = .pass) ∧
  (∃ i, i ∈ List.range c.axes.length ∧ strictAxis c x y i)

def dominatesB (c : ComparisonContract.Contract) (x y : List (Option Int)) : Bool :=
  (List.range c.axes.length).all (fun i => axisVerdict c x y i == .pass) &&
  (List.range c.axes.length).any (fun i =>
    match c.axes[i]?, reading x i, reading y i with
    | some axis, some xv, some yv =>
      decide (ComparisonContract.normalize axis.direction xv <
        ComparisonContract.normalize axis.direction yv)
    | _, _, _ => false)

def directionPolarity : ComparisonContract.Direction → Interface.Polarity
  | .minimize => .minimize
  | .maximize => .maximize

def measureSpace (c : ComparisonContract.Contract) : Interface.MeasureSpace Unit :=
  c.axes.map fun a => ⟨(), directionPolarity a.direction⟩

def natOf (v : Option Int) : Option Nat :=
  match v with
  | some n => if 0 ≤ n then some n.toNat else none
  | none => none

def toReadings (c : ComparisonContract.Contract) (xs : List (Option Int)) : List Nat :=
  let opts := (List.range c.axes.length).map fun i => natOf (reading xs i)
  if opts.any (fun o => o.isNone) then [] else opts.filterMap id

def toProfile (c : ComparisonContract.Contract) (xs : List (Option Int)) :
    Interface.Profile Unit Unit where
  symbol := ()
  readings := toReadings c xs
  observed := true

def materialized (c : ComparisonContract.Contract) (xs : List (Option Int)) : List Int :=
  (List.range c.axes.length).map fun i => (reading xs i).getD 0

def contractMin : ComparisonContract.Contract :=
  ⟨[⟨0, 0, .minimize, 0⟩], 0, 0, 0⟩

theorem absent_axis_admitted_by_two_valued_dominance :
    (([] : List Int)[0]? = none) ∧
      ComparisonContract.dominates contractMin [] [1] = true := by
  decide

theorem unknown_blocks_dominance
    (c : ComparisonContract.Contract) (x y : List (Option Int)) (i : Nat)
    (hi : i ∈ List.range c.axes.length)
    (hu : axisVerdict c x y i = .unknown) :
    ¬ dominates c x y := by
  intro h
  have hv := h.1 i hi
  rw [hu] at hv
  cases hv

theorem toReadings_short_of_missing
    (c : ComparisonContract.Contract) (xs : List (Option Int)) (i : Nat)
    (hi : i < c.axes.length) (hr : reading xs i = none) :
    (toReadings c xs).length < c.axes.length := by
  have hf : natOf (reading xs i) = none := by simp [natOf, hr]
  have hmem : none ∈ (List.range c.axes.length).map (fun j => natOf (reading xs j)) :=
    List.mem_map.mpr ⟨i, List.mem_range.mpr hi, hf⟩
  have hany :
      ((List.range c.axes.length).map (fun j => natOf (reading xs j))).any
        (fun o => o.isNone) = true :=
    List.any_eq_true.mpr ⟨none, hmem, rfl⟩
  simp [toReadings, hany]
  omega

theorem unknown_is_missing
    (c : ComparisonContract.Contract) (x y : List (Option Int)) (i : Nat)
    (hi : i ∈ List.range c.axes.length)
    (hu : axisVerdict c x y i = .unknown) :
    reading x i = none ∨ reading y i = none := by
  have hlt : i < c.axes.length := List.mem_range.mp hi
  have hax : c.axes[i]? = some c.axes[i] := List.getElem?_eq_getElem hlt
  cases hxr : reading x i with
  | none => exact Or.inl rfl
  | some xv =>
    cases hyr : reading y i with
    | none => exact Or.inr rfl
    | some yv =>
      cases hdec : decide (ComparisonContract.normalize c.axes[i].direction xv ≤
          ComparisonContract.normalize c.axes[i].direction yv) <;>
        simp [axisVerdict, hax, hxr, hyr, boolGate, hdec] at hu

theorem unknown_blocks_dominance_canonical
    (c : ComparisonContract.Contract) (x y : List (Option Int)) (i : Nat)
    (hi : i ∈ List.range c.axes.length)
    (hu : axisVerdict c x y i = .unknown) :
    ¬ Interface.dominates (measureSpace c) (toProfile c x) (toProfile c y) := by
  intro hdom
  have hal := Interface.measuresLe_aligned hdom.1.1
  have hlen : (measureSpace c).length = c.axes.length := by
    simp [measureSpace, List.length_map]
  rcases unknown_is_missing c x y i hi hu with hr | hr
  · have hshort := toReadings_short_of_missing c x i (List.mem_range.mp hi) hr
    have : (toProfile c x).readings.length ≠ (measureSpace c).length := by
      simp [toProfile, hlen]
      omega
    exact this hal.1
  · have hshort := toReadings_short_of_missing c y i (List.mem_range.mp hi) hr
    have : (toProfile c y).readings.length ≠ (measureSpace c).length := by
      simp [toProfile, hlen]
      omega
    exact this hal.2

theorem reading_map_some (xs : List Int) (i : Nat) (hi : i < xs.length) :
    reading (xs.map some) i = some xs[i] := by
  simp [reading, List.getElem?_eq_getElem, hi, List.getElem?_map]

theorem cost_eq (c : ComparisonContract.Contract) (xs : List Int) (i : Nat)
    (hx : xs.length = c.axes.length) (hi : i < c.axes.length) :
    ComparisonContract.cost c xs i =
      ComparisonContract.normalize (c.axes[i]).direction xs[i] := by
  have hxs : xs[i]? = some xs[i] := List.getElem?_eq_getElem (by omega)
  have hax : c.axes[i]? = some c.axes[i] := List.getElem?_eq_getElem hi
  simp [ComparisonContract.cost, hxs, hax]

theorem verdict_eq_cost (c : ComparisonContract.Contract) (xs ys : List Int) (i : Nat)
    (hx : xs.length = c.axes.length) (hy : ys.length = c.axes.length)
    (hi : i < c.axes.length) :
    axisVerdict c (xs.map some) (ys.map some) i =
      boolGate (decide (ComparisonContract.cost c xs i ≤ ComparisonContract.cost c ys i)) := by
  have hax : c.axes[i]? = some c.axes[i] := List.getElem?_eq_getElem hi
  simp [axisVerdict, reading_map_some xs i (by omega), reading_map_some ys i (by omega),
    hax, cost_eq c xs i hx hi, cost_eq c ys i hy hi]

theorem known_gate_matches_bool
    (c : ComparisonContract.Contract) (xs ys : List Int) (i : Nat)
    (hx : xs.length = c.axes.length) (hy : ys.length = c.axes.length)
    (hi : i < c.axes.length) :
    axisVerdict c (xs.map some) (ys.map some) i =
      boolGate (decide (ComparisonContract.cost c xs i ≤ ComparisonContract.cost c ys i)) :=
  verdict_eq_cost c xs ys i hx hy hi

theorem strict_iff_cost (c : ComparisonContract.Contract) (xs ys : List Int) (i : Nat)
    (hx : xs.length = c.axes.length) (hy : ys.length = c.axes.length)
    (hi : i < c.axes.length) :
    strictAxis c (xs.map some) (ys.map some) i ↔
      ComparisonContract.cost c xs i < ComparisonContract.cost c ys i := by
  have hax : c.axes[i]? = some c.axes[i] := List.getElem?_eq_getElem hi
  simp [strictAxis, reading_map_some xs i (by omega), reading_map_some ys i (by omega),
    hax, cost_eq c xs i hx hi, cost_eq c ys i hy hi]

theorem pass_iff_cost (c : ComparisonContract.Contract) (xs ys : List Int) (i : Nat)
    (hx : xs.length = c.axes.length) (hy : ys.length = c.axes.length)
    (hi : i < c.axes.length) :
    axisVerdict c (xs.map some) (ys.map some) i = .pass ↔
      ComparisonContract.cost c xs i ≤ ComparisonContract.cost c ys i := by
  rw [verdict_eq_cost c xs ys i hx hy hi]
  cases h : decide (ComparisonContract.cost c xs i ≤ ComparisonContract.cost c ys i) <;>
    simp [boolGate, h, of_decide_eq_true, of_decide_eq_false]

theorem known_dominates_iff_bool
    (c : ComparisonContract.Contract) (xs ys : List Int)
    (hx : xs.length = c.axes.length) (hy : ys.length = c.axes.length) :
    dominates c (xs.map some) (ys.map some) ↔
      ComparisonContract.dominates c xs ys = true := by
  rw [ComparisonContract.dominates, FiniteFrontier.pareto_exact]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro i hi
      exact (pass_iff_cost c xs ys i hx hy (List.mem_range.mp hi)).mp (h.1 i hi)
    · obtain ⟨i, hi, hs⟩ := h.2
      exact ⟨i, hi, (strict_iff_cost c xs ys i hx hy (List.mem_range.mp hi)).mp hs⟩
  · intro h
    refine ⟨?_, ?_⟩
    · intro i hi
      exact (pass_iff_cost c xs ys i hx hy (List.mem_range.mp hi)).mpr (h.1 i hi)
    · obtain ⟨i, hi, hs⟩ := h.2
      exact ⟨i, hi, (strict_iff_cost c xs ys i hx hy (List.mem_range.mp hi)).mpr hs⟩

theorem normalize_le (d : ComparisonContract.Direction) (a b : Nat) :
    ComparisonContract.normalize d (Int.ofNat a) ≤ ComparisonContract.normalize d (Int.ofNat b) ↔
      Interface.axisLe (directionPolarity d) a b := by
  cases d with
  | minimize =>
    simp [ComparisonContract.normalize, directionPolarity, Interface.axisLe, Int.ofNat_le]
  | maximize =>
    simp [ComparisonContract.normalize, directionPolarity, Interface.axisLe, Int.neg_le_neg_iff,
      Int.ofNat_le]

theorem normalize_lt (d : ComparisonContract.Direction) (a b : Nat) :
    ComparisonContract.normalize d (Int.ofNat a) < ComparisonContract.normalize d (Int.ofNat b) ↔
      Interface.axisLt (directionPolarity d) a b := by
  cases d with
  | minimize =>
    simp [ComparisonContract.normalize, directionPolarity, Interface.axisLt, Int.ofNat_lt]
  | maximize =>
    simp [ComparisonContract.normalize, directionPolarity, Interface.axisLt, Int.neg_lt_neg_iff,
      Int.ofNat_lt]

theorem axesLe_iff (axes : List ComparisonContract.Axis) (xs ys : List Nat)
    (hx : xs.length = axes.length) (hy : ys.length = axes.length) :
    Interface.axesLe (axes.map fun a => (⟨(), directionPolarity a.direction⟩ : Interface.Axis Unit)) xs ys ↔
      ∀ i, (hi : i < axes.length) →
        Interface.axisLe (directionPolarity (axes[i]'hi).direction)
          (xs[i]'(by omega)) (ys[i]'(by omega)) := by
  induction axes generalizing xs ys with
  | nil =>
    simp at hx hy
    subst hx hy
    simp [Interface.axesLe]
  | cons a axes ih =>
    cases xs with
    | nil => simp at hx
    | cons x xs =>
      cases ys with
      | nil => simp at hy
      | cons y ys =>
        have hx' : xs.length = axes.length := by simp at hx; omega
        have hy' : ys.length = axes.length := by simp at hy; omega
        simp [Interface.axesLe, List.map_cons]
        constructor
        · intro h i hi
          cases i with
          | zero => simpa [directionPolarity] using h.1
          | succ i =>
            simpa [List.getElem_cons_succ] using (ih xs ys hx' hy').mp h.2 i (by omega)
        · intro h
          refine ⟨?_, (ih xs ys hx' hy').mpr ?_⟩
          · simpa [directionPolarity] using h 0 (by omega)
          · intro i hi
            simpa [List.getElem_cons_succ] using h (i + 1) (by omega)

theorem axesLt_iff (axes : List ComparisonContract.Axis) (xs ys : List Nat)
    (hx : xs.length = axes.length) (hy : ys.length = axes.length) :
    Interface.axesLt (axes.map fun a => (⟨(), directionPolarity a.direction⟩ : Interface.Axis Unit)) xs ys ↔
      (∀ i, (hi : i < axes.length) →
        Interface.axisLe (directionPolarity (axes[i]'hi).direction)
          (xs[i]'(by omega)) (ys[i]'(by omega))) ∧
      (∃ i, ∃ hi : i < axes.length,
        Interface.axisLt (directionPolarity (axes[i]'hi).direction)
          (xs[i]'(by omega)) (ys[i]'(by omega))) := by
  induction axes generalizing xs ys with
  | nil =>
    simp at hx hy
    subst hx hy
    simp [Interface.axesLt]
  | cons a axes ih =>
    cases xs with
    | nil => simp at hx
    | cons x xs =>
      cases ys with
      | nil => simp at hy
      | cons y ys =>
        have hx' : xs.length = axes.length := by simp at hx; omega
        have hy' : ys.length = axes.length := by simp at hy; omega
        simp [Interface.axesLt, List.map_cons]
        constructor
        · intro h
          cases h with
          | inl hlt =>
            have htail := (axesLe_iff axes xs ys hx' hy').mp hlt.2
            refine ⟨?_, 0, by omega, ?_⟩
            · intro i hi
              cases i with
              | zero => exact Interface.axisLt_le hlt.1
              | succ i => simpa [List.getElem_cons_succ] using htail i (by omega)
            · simpa [directionPolarity] using hlt.1
          | inr hle =>
            have htail := (ih xs ys hx' hy').mp hle.2
            refine ⟨?_, ?_⟩
            · intro i hi
              cases i with
              | zero => simpa [directionPolarity] using hle.1
              | succ i => simpa [List.getElem_cons_succ] using htail.1 i (by omega)
            · obtain ⟨i, hi, hlt⟩ := htail.2
              exact ⟨i + 1, by omega, by simpa [List.getElem_cons_succ] using hlt⟩
        · intro h
          have h0 := h.1 0 (by omega)
          by_cases hhead : Interface.axisLt (directionPolarity a.direction) x y
          · refine Or.inl ⟨?_, (axesLe_iff axes xs ys hx' hy').mpr ?_⟩
            · simpa [directionPolarity] using hhead
            · intro i hi
              simpa [List.getElem_cons_succ] using h.1 (i + 1) (by omega)
          · have hle : Interface.axisLe (directionPolarity a.direction) x y := h0
            refine Or.inr ⟨by simpa [directionPolarity] using hle, (ih xs ys hx' hy').mpr ?_⟩
            refine ⟨?_, ?_⟩
            · intro i hi
              simpa [List.getElem_cons_succ] using h.1 (i + 1) (by omega)
            · obtain ⟨i, hi, hlt⟩ := h.2
              cases i with
              | zero => exact False.elim (hhead (by simpa [directionPolarity] using hlt))
              | succ i => exact ⟨i, by omega, by simpa [List.getElem_cons_succ] using hlt⟩

theorem filterMap_some (xs : List Nat) : (xs.map some).filterMap id = xs := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [ih]

theorem reading_ofNat (xs : List Nat) (i : Nat) (hi : i < xs.length) :
    reading (xs.map fun n => some (Int.ofNat n)) i = some (Int.ofNat xs[i]) := by
  simp [reading, List.getElem?_map, List.getElem?_eq_getElem hi]

theorem toReadings_ofNat (c : ComparisonContract.Contract) (xs : List Nat)
    (hx : xs.length = c.axes.length) :
    toReadings c (xs.map fun n => some (Int.ofNat n)) = xs := by
  have hopts :
      (List.range c.axes.length).map
        (fun i => natOf (reading (xs.map fun n => some (Int.ofNat n)) i)) =
        xs.map some := by
    apply List.ext_getElem
    · simp [hx]
    · intro i hi _
      have hixs : i < xs.length := by simpa [hx] using hi
      simp only [List.getElem_map, List.getElem_range]
      rw [reading_ofNat xs i hixs]
      simp [natOf, Int.ofNat_nonneg]
  have hnot :
      ((List.range c.axes.length).map
        (fun i => natOf (reading (xs.map fun n => some (Int.ofNat n)) i))).any
        (fun o => o.isNone) = false := by
    rw [hopts]
    simp [List.any_eq_true]
  unfold toReadings
  simp only [hnot, Bool.false_eq_true, if_false]
  rw [hopts, filterMap_some]

theorem profile_dominates_iff (c : ComparisonContract.Contract) (xs ys : List Nat)
    (hx : xs.length = c.axes.length) (hy : ys.length = c.axes.length) :
    Interface.dominates (measureSpace c)
        (toProfile c (xs.map fun n => some (Int.ofNat n)))
        (toProfile c (ys.map fun n => some (Int.ofNat n))) ↔
      ComparisonContract.dominates c (xs.map Int.ofNat) (ys.map Int.ofNat) = true := by
  have hxp : (toProfile c (xs.map fun n => some (Int.ofNat n))).readings = xs := by
    simpa [toProfile] using toReadings_ofNat c xs hx
  have hyp : (toProfile c (ys.map fun n => some (Int.ofNat n))).readings = ys := by
    simpa [toProfile] using toReadings_ofNat c ys hy
  rw [ComparisonContract.dominates, FiniteFrontier.pareto_exact]
  constructor
  · intro h
    have hlt0 : Interface.axesLt (measureSpace c)
        (toProfile c (xs.map fun n => some (Int.ofNat n))).readings
        (toProfile c (ys.map fun n => some (Int.ofNat n))).readings := by
      simpa [Interface.strictlyBetter] using h.2
    have hlt : Interface.axesLt (measureSpace c) xs ys := by
      rw [← hxp, ← hyp]
      exact hlt0
    have hiff := (axesLt_iff c.axes xs ys hx hy).mp (by simpa [measureSpace] using hlt)
    refine ⟨?_, ?_⟩
    · intro i hi
      have hi' := List.mem_range.mp hi
      have hle := hiff.1 i hi'
      have hcost : ComparisonContract.normalize (c.axes[i]).direction (Int.ofNat xs[i]) ≤
          ComparisonContract.normalize (c.axes[i]).direction (Int.ofNat ys[i]) :=
        (normalize_le (c.axes[i]).direction xs[i] ys[i]).mpr hle
      simpa [cost_eq c (xs.map Int.ofNat) i (by simp [hx]) hi',
        cost_eq c (ys.map Int.ofNat) i (by simp [hy]) hi', List.getElem_map] using hcost
    · obtain ⟨i, hi, hlt'⟩ := hiff.2
      have hcost : ComparisonContract.normalize (c.axes[i]).direction (Int.ofNat xs[i]) <
          ComparisonContract.normalize (c.axes[i]).direction (Int.ofNat ys[i]) :=
        (normalize_lt (c.axes[i]).direction xs[i] ys[i]).mpr hlt'
      refine ⟨i, List.mem_range.mpr hi, ?_⟩
      simpa [cost_eq c (xs.map Int.ofNat) i (by simp [hx]) hi,
        cost_eq c (ys.map Int.ofNat) i (by simp [hy]) hi, List.getElem_map] using hcost
  · intro h
    have hlt : Interface.axesLt (measureSpace c) xs ys := by
      apply (axesLt_iff c.axes xs ys hx hy).mpr
      refine ⟨?_, ?_⟩
      · intro i hi
        have hmem : i ∈ List.range c.axes.length := List.mem_range.mpr hi
        have hle := h.1 i hmem
        have hnorm : ComparisonContract.normalize (c.axes[i]).direction (Int.ofNat xs[i]) ≤
            ComparisonContract.normalize (c.axes[i]).direction (Int.ofNat ys[i]) := by
          simpa [cost_eq c (xs.map Int.ofNat) i (by simp [hx]) hi,
            cost_eq c (ys.map Int.ofNat) i (by simp [hy]) hi, List.getElem_map] using hle
        exact (normalize_le (c.axes[i]).direction xs[i] ys[i]).mp hnorm
      · obtain ⟨i, hi, hlt⟩ := h.2
        have hi' := List.mem_range.mp hi
        have hnorm : ComparisonContract.normalize (c.axes[i]).direction (Int.ofNat xs[i]) <
            ComparisonContract.normalize (c.axes[i]).direction (Int.ofNat ys[i]) := by
          simpa [cost_eq c (xs.map Int.ofNat) i (by simp [hx]) hi',
            cost_eq c (ys.map Int.ofNat) i (by simp [hy]) hi', List.getElem_map] using hlt
        exact ⟨i, hi', (normalize_lt (c.axes[i]).direction xs[i] ys[i]).mp hnorm⟩
    have hltP : Interface.axesLt (measureSpace c)
        (toProfile c (xs.map fun n => some (Int.ofNat n))).readings
        (toProfile c (ys.map fun n => some (Int.ofNat n))).readings := by
      rw [hxp, hyp]
      exact hlt
    refine ⟨⟨⟨rfl, ?_⟩, fun _ => rfl⟩, hltP⟩
    rw [hxp, hyp]
    simpa [measureSpace] using Interface.axesLt_le (measureSpace c) xs ys hlt

theorem known_agrees_canonical
    (c : ComparisonContract.Contract) (xs ys : List Nat)
    (hx : xs.length = c.axes.length) (hy : ys.length = c.axes.length) :
    dominates c (xs.map fun n => some (Int.ofNat n)) (ys.map fun n => some (Int.ofNat n)) ↔
      Interface.dominates (measureSpace c)
        (toProfile c (xs.map fun n => some (Int.ofNat n)))
        (toProfile c (ys.map fun n => some (Int.ofNat n))) := by
  have hxmap : (xs.map fun n => some (Int.ofNat n)) = (xs.map Int.ofNat).map some := by
    simp [List.map_map]
  have hymap : (ys.map fun n => some (Int.ofNat n)) = (ys.map Int.ofNat).map some := by
    simp [List.map_map]
  rw [hxmap, hymap, known_dominates_iff_bool c (xs.map Int.ofNat) (ys.map Int.ofNat)
      (by simp [hx]) (by simp [hy]), ← hxmap, ← hymap]
  exact (profile_dominates_iff c xs ys hx hy).symm

theorem contractMin_agrees_canonical (a b : Nat) :
    dominates contractMin [some (Int.ofNat a)] [some (Int.ofNat b)] ↔
      Interface.dominates CanonicalDominance.oneSpace
        (CanonicalDominance.oneProfile a) (CanonicalDominance.oneProfile b) := by
  have ha : [some (Int.ofNat a)] = List.map some [Int.ofNat a] := rfl
  have hb : [some (Int.ofNat b)] = List.map some [Int.ofNat b] := rfl
  rw [ha, hb, known_dominates_iff_bool contractMin [Int.ofNat a] [Int.ofNat b]
      (by simp [contractMin]) (by simp [contractMin])]
  exact CanonicalDominance.Comparison.local_dominates_iff_canonical a b

theorem contractMin_gate_matches_bool (v w : Int) :
    axisVerdict contractMin [some v] [some w] 0 =
      boolGate (decide (ComparisonContract.cost contractMin [v] 0 ≤
        ComparisonContract.cost contractMin [w] 0)) :=
  known_gate_matches_bool contractMin [v] [w] 0 (by simp [contractMin]) (by simp [contractMin])
    (by simp [contractMin])

theorem dominatesB_iff (c : ComparisonContract.Contract) (x y : List (Option Int)) :
    dominatesB c x y = true ↔ dominates c x y := by
  simp only [dominatesB, dominates, Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    beq_iff_eq]
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    obtain ⟨i, hi, hs⟩ := h.2
    refine ⟨i, hi, ?_⟩
    have hlt : i < c.axes.length := List.mem_range.mp hi
    have hax : c.axes[i]? = some c.axes[i] := List.getElem?_eq_getElem hlt
    cases hxr : reading x i <;> cases hyr : reading y i <;>
      simp [hax, hxr, hyr, decide_eq_true_eq, strictAxis] at hs ⊢
    exact hs
  · intro h
    refine ⟨h.1, ?_⟩
    obtain ⟨i, hi, hs⟩ := h.2
    refine ⟨i, hi, ?_⟩
    have hlt : i < c.axes.length := List.mem_range.mp hi
    have hax : c.axes[i]? = some c.axes[i] := List.getElem?_eq_getElem hlt
    cases hxr : reading x i <;> cases hyr : reading y i <;>
      simp [strictAxis, hax, hxr, hyr] at hs
    simpa [hax, hxr, hyr, decide_eq_true_eq] using hs

theorem reading_materialized (c : ComparisonContract.Contract) (xs : List (Option Int))
    (i : Nat) (hi : i < c.axes.length) (hv : reading xs i ≠ none) :
    reading ((materialized c xs).map some) i = reading xs i := by
  have hlen : i < (materialized c xs).length := by
    simp [materialized, List.length_map, List.length_range, hi]
  have hget : (materialized c xs)[i] = (reading xs i).getD 0 := by
    simp [materialized, List.getElem_map, List.getElem_range]
  cases hr : reading xs i with
  | none => exact absurd hr hv
  | some v =>
    have : reading ((materialized c xs).map some) i = some (materialized c xs)[i] := by
      simp [reading, List.getElem?_map, List.getElem?_eq_getElem hlen]
    rw [this, hget, hr, Option.getD_some]

theorem dominates_materialized (c : ComparisonContract.Contract) (x y : List (Option Int))
    (hx : ∀ i, i < c.axes.length → reading x i ≠ none)
    (hy : ∀ i, i < c.axes.length → reading y i ≠ none) :
    dominates c x y ↔
      dominates c ((materialized c x).map some) ((materialized c y).map some) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro i hi
      have hi' := List.mem_range.mp hi
      have hv := h.1 i hi
      have hax : c.axes[i]? = some c.axes[i] := List.getElem?_eq_getElem hi'
      cases hxr : reading x i <;> cases hyr : reading y i <;>
        simp [axisVerdict, hax, hxr, hyr] at hv
      simp [axisVerdict, hax, reading_materialized c x i hi' (hx i hi'),
        reading_materialized c y i hi' (hy i hi'), hxr, hyr, hv]
    · obtain ⟨i, hi, hs⟩ := h.2
      refine ⟨i, hi, ?_⟩
      have hi' := List.mem_range.mp hi
      have hax : c.axes[i]? = some c.axes[i] := List.getElem?_eq_getElem hi'
      cases hxr : reading x i <;> cases hyr : reading y i <;>
        simp [strictAxis, hax, hxr, hyr] at hs
      simp [strictAxis, hax, reading_materialized c x i hi' (hx i hi'),
        reading_materialized c y i hi' (hy i hi'), hxr, hyr, hs]
  · intro h
    refine ⟨?_, ?_⟩
    · intro i hi
      have hi' := List.mem_range.mp hi
      have hv := h.1 i hi
      have hax : c.axes[i]? = some c.axes[i] := List.getElem?_eq_getElem hi'
      have hxr := reading_materialized c x i hi' (hx i hi')
      have hyr := reading_materialized c y i hi' (hy i hi')
      cases hxv : reading x i <;> cases hyv : reading y i <;>
        simp [hxv, hyv, hxr, hyr, axisVerdict, hax] at hv ⊢
      exact hv
    · obtain ⟨i, hi, hs⟩ := h.2
      refine ⟨i, hi, ?_⟩
      have hi' := List.mem_range.mp hi
      have hax : c.axes[i]? = some c.axes[i] := List.getElem?_eq_getElem hi'
      have hxr := reading_materialized c x i hi' (hx i hi')
      have hyr := reading_materialized c y i hi' (hy i hi')
      cases hxv : reading x i <;> cases hyv : reading y i <;>
        simp [hxv, hyv, hxr, hyr, strictAxis, hax] at hs ⊢
      exact hs

structure FiniteSpace (Impl : Type) (c : ComparisonContract.Contract) where
  candidates : List Impl
  readings : Impl → List (Option Int)
  nothingOutside : ∀ impl, impl ∈ candidates
  noCoverageGaps : ∀ x, x ∈ candidates → ∀ i, i < c.axes.length → reading (readings x) i ≠ none

theorem frontier_no_dominator
    {Impl : Type} {c : ComparisonContract.Contract}
    (space : FiniteSpace Impl c) (x : Impl)
    (hx : x ∈ FiniteFrontier.frontier space.candidates
      (fun y z => dominatesB c (space.readings y) (space.readings z))) :
    ∀ impl, ComparisonContract.dominates c
      (materialized c (space.readings impl))
      (materialized c (space.readings x)) = false := by
  intro impl
  have hxmem := ((FiniteFrontier.frontier_exact space.candidates
    (fun y z => dominatesB c (space.readings y) (space.readings z)) x).mp hx).1
  have hnot := ((FiniteFrontier.frontier_exact space.candidates
    (fun y z => dominatesB c (space.readings y) (space.readings z)) x).mp hx).2
    impl (space.nothingOutside impl)
  have hgapx := space.noCoverageGaps x hxmem
  have hgapi := space.noCoverageGaps impl (space.nothingOutside impl)
  have hdom : ¬ dominates c (space.readings impl) (space.readings x) := by
    intro h
    exact Bool.noConfusion (hnot.symm.trans ((dominatesB_iff c _ _).mpr h))
  cases hcmp : ComparisonContract.dominates c
      (materialized c (space.readings impl)) (materialized c (space.readings x)) with
  | false => rfl
  | true =>
    exact False.elim (hdom ((dominates_materialized c (space.readings impl)
      (space.readings x) hgapi hgapx).mpr
      ((known_dominates_iff_bool c (materialized c (space.readings impl))
        (materialized c (space.readings x))
        (by simp [materialized, List.length_map, List.length_range])
        (by simp [materialized, List.length_map, List.length_range])).mpr hcmp)))

inductive Sample where
  | slow
  | fast
  deriving DecidableEq, Repr

def outsideCandidates : List Sample := [.slow]

def outsideReadings : Sample → List (Option Int)
  | .slow => [some 1]
  | .fast => [some 0]

theorem nothingOutside_counterexample :
    .slow ∈ FiniteFrontier.frontier outsideCandidates
      (fun y z => dominatesB contractMin (outsideReadings y) (outsideReadings z)) ∧
      .fast ∉ outsideCandidates ∧
      ComparisonContract.dominates contractMin
        (materialized contractMin (outsideReadings .fast))
        (materialized contractMin (outsideReadings .slow)) = true := by
  decide

def gapCandidates : List Sample := [.slow, .fast]

def gapReadings : Sample → List (Option Int)
  | .slow => [some 1]
  | .fast => [none]

theorem noCoverageGaps_counterexample :
    (∀ impl : Sample, impl ∈ gapCandidates) ∧
      reading (gapReadings .fast) 0 = none ∧
      .slow ∈ FiniteFrontier.frontier gapCandidates
        (fun y z => dominatesB contractMin (gapReadings y) (gapReadings z)) ∧
      ComparisonContract.dominates contractMin
        (materialized contractMin (gapReadings .fast))
        (materialized contractMin (gapReadings .slow)) = true := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro impl
    cases impl <;> decide
  · decide
  · decide
  · decide

end ThreeValuedGate
