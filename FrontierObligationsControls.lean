import FiniteFrontier
/-! Independent counterexample controls for the two general Pareto obligations
    in FiniteFrontier.lean (frontier completeness F, selection-on-frontier S).
    Written by a separate reviewing agent that tried to break the statements;
    kept in the gate as standing controls.
    Every hypothesis drop below is a kernel-checked refutation of the weakened
    statement. Kernel-checked only: no proof escape hatches. -/
open FiniteFrontier

namespace FrontierObligationsControls

inductive P where | a | b | c | d | e
  deriving DecidableEq, Repr

open P

/-! ## 1. Non-vacuity: all hypotheses satisfiable, conclusion informative -/

-- Two axes, non-total (a, b, c pairwise incomparable), a duplicate (c twice),
-- a dominated point d (beaten by a and by c), negative costs.
def cost2 : P → Nat → Int
  | a, 0 => -5 | a, _ => 3
  | b, 0 => 3  | b, _ => -5
  | c, 0 => 2  | c, _ => 2
  | d, 0 => 3  | d, _ => 3
  | e, 0 => 9  | e, _ => 9

def L1 : List P := [a, b, c, c, d]

-- The frontier keeps both copies of c and drops d.
theorem nv_frontier : frontier L1 (strictPareto [0, 1] cost2) = [a, b, c, c] := by decide

-- F applied to the dominated point gives a frontier dominator (informative branch).
theorem nv_complete :
    d ∉ frontier L1 (strictPareto [0, 1] cost2) ∧
    ∃ y, y ∈ frontier L1 (strictPareto [0, 1] cost2) ∧ strictPareto [0, 1] cost2 y d = true := by
  refine ⟨by decide, ?_⟩
  rcases pareto_frontier_complete [0, 1] cost2 L1 d (by decide) with h | h
  · exact absurd h (by decide)
  · exact h

-- A general (non-Pareto) strict partial order: proper divisibility, smaller
-- divisor dominates. Off-list it is NOT irreflexive (0 dominates everything,
-- including itself) -- the theorem only needs the hypotheses on L.
def pdiv (y x : Nat) : Bool := y == 0 || (y != x && x % y == 0)
def LD : List Nat := [2, 3, 4, 6, 12]

theorem pdiv_irr : ∀ a, a ∈ LD → pdiv a a = false := by decide
theorem pdiv_tr : ∀ a b c, a ∈ LD → b ∈ LD → c ∈ LD →
    pdiv a b = true → pdiv b c = true → pdiv a c = true := by
  have h : ∀ a, a ∈ LD → ∀ b, b ∈ LD → ∀ c, c ∈ LD →
      (pdiv a b = true → pdiv b c = true → pdiv a c = true) := by decide
  exact fun a b c ha hb hc => h a ha b hb c hc
theorem pdiv_offlist_reflexive : pdiv 0 0 = true := by decide
theorem nv_pdiv_frontier : frontier LD pdiv = [2, 3] := by decide
theorem nv_pdiv_12 : ∃ y, y ∈ frontier LD pdiv ∧ pdiv y 12 = true := by
  rcases frontier_complete_of_strict LD pdiv pdiv_irr pdiv_tr 12 (by decide) with h | h
  · exact absurd h (by decide)
  · exact h
theorem nv_pdiv_cert : certificate LD (frontier LD pdiv) pdiv = true :=
  frontier_certifies_of_strict LD pdiv pdiv_irr pdiv_tr

-- S with positive weights (2, 1): the minimizer a is on the frontier while the
-- frontier also contains b and c, so the conclusion is not "everything".
def w12 : Nat → Int | 0 => 2 | _ => 1
theorem nv_weighted : a ∈ frontier L1 (strictPareto [0, 1] cost2) :=
  weighted_minimizer_on_frontier [0, 1] w12 cost2 (by decide) L1 a (by decide) (by decide)

/-! ## 2. Necessity of each hypothesis -/

-- Irreflexivity: the always-true comparison is transitive, the frontier of a
-- singleton is empty, so completeness and nonemptiness both fail.
theorem need_irr_complete : ¬ ∀ (L : List P) (dm : P → P → Bool),
    (∀ x y z, x ∈ L → y ∈ L → z ∈ L → dm x y = true → dm y z = true → dm x z = true) →
    ∀ x, x ∈ L → x ∈ frontier L dm ∨ ∃ y, y ∈ frontier L dm ∧ dm y x = true := by
  intro h
  have hx := h [a] (fun _ _ => true) (by intros; rfl) a (by decide)
  have hf : frontier [a] (fun _ _ => true) = [] := by decide
  rw [hf] at hx
  simp at hx

theorem need_irr_nonempty : ¬ ∀ (L : List P) (dm : P → P → Bool),
    (∀ x y z, x ∈ L → y ∈ L → z ∈ L → dm x y = true → dm y z = true → dm x z = true) →
    L ≠ [] → ∃ y, y ∈ frontier L dm := by
  intro h
  obtain ⟨y, hy⟩ := h [a] (fun _ _ => true) (by intros; rfl) (by decide)
  have hf : frontier [a] (fun _ _ => true) = [] := by decide
  rw [hf] at hy
  simp at hy

-- Transitivity (direct-dominator form): chain a -> b -> c, irreflexive,
-- not transitive. Frontier is [a]; c is beaten only by b, which is off the frontier.
def chain : P → P → Bool
  | a, b => true | b, c => true | _, _ => false
def L3 : List P := [a, b, c]

theorem chain_frontier : frontier L3 chain = [a] := by decide
theorem chain_irr : ∀ x, x ∈ L3 → chain x x = false := by decide

theorem need_trans_complete : ¬ ∀ (L : List P) (dm : P → P → Bool),
    (∀ x, x ∈ L → dm x x = false) →
    ∀ x, x ∈ L → x ∈ frontier L dm ∨ ∃ y, y ∈ frontier L dm ∧ dm y x = true := by
  intro h
  have hc := h L3 chain chain_irr c (by decide)
  rw [chain_frontier] at hc
  simp [chain] at hc

-- Without transitivity no certificate exists at all (not merely: the frontier
-- fails to certify itself), so "a certificate always exists" needs it.
theorem need_trans_certifies : certificate L3 (frontier L3 chain) chain = false := by decide

theorem need_trans_no_certificate : ∀ R : List P, certificate L3 R chain = false := by
  intro R
  cases hcert : certificate L3 R chain with
  | false => rfl
  | true =>
    have ⟨h1, h2⟩ := (certificate_exact L3 R chain).mp hcert
    rcases h2 c (by decide) with hc | ⟨y, hy, hyc⟩
    · have := (h1 c hc).2 b (by decide)
      simp [chain] at this
    · have hyL := (h1 y hy)
      cases y with
      | a => simp [chain] at hyc
      | b => have := hyL.2 a (by decide); simp [chain] at this
      | c => simp [chain] at hyc
      | d => simp [chain] at hyc
      | e => simp [chain] at hyc

-- Transitivity (nonemptiness): irreflexive 3-cycle, frontier empty.
def cyc : P → P → Bool
  | a, b => true | b, c => true | c, a => true | _, _ => false
theorem cyc_irr : ∀ x, x ∈ L3 → cyc x x = false := by decide
theorem need_trans_nonempty : ¬ ∀ (L : List P) (dm : P → P → Bool),
    (∀ x, x ∈ L → dm x x = false) → L ≠ [] → ∃ y, y ∈ frontier L dm := by
  intro h
  obtain ⟨y, hy⟩ := h L3 cyc cyc_irr (by decide)
  have hf : frontier L3 cyc = [] := by decide
  rw [hf] at hy
  simp at hy

-- L ≠ []: the empty list has an empty frontier even for strict Pareto.
theorem need_nonempty : ¬ ∃ y, y ∈ frontier ([] : List P) (strictPareto [0] cost2) := by
  simp [frontier]

-- S, strictness -> constant score: a minimizes the constant score but is
-- dominated by b on axis 0 (weakly monotone score is not enough).
def cost1 : P → Nat → Int
  | a, _ => 1 | b, _ => 0 | c, _ => 3 | d, _ => 2 | e, _ => 5
def L2 : List P := [a, b]

theorem need_strict_constant : ¬ ∀ (L : List P) (dm : P → P → Bool) (s : P → Int) (x : P),
    x ∈ L → (∀ y, y ∈ L → s x ≤ s y) → (∀ y, y ∈ L → dm y x = true → s y ≤ s x) →
    x ∈ frontier L dm := by
  intro h
  have := h L2 (strictPareto [0] cost1) (fun _ => 0) a (by decide) (by decide) (by decide)
  exact absurd this (by decide)

-- S, strictness -> weakly monotone, non-constant score (floor of half the cost).
def costH : P → Nat → Int
  | a, _ => 3 | b, _ => 2 | c, _ => 0 | d, _ => 7 | e, _ => 9
theorem need_strict_weak_monotone : ¬ ∀ (L : List P) (dm : P → P → Bool) (s : P → Int) (x : P),
    x ∈ L → (∀ y, y ∈ L → s x ≤ s y) → (∀ y, y ∈ L → dm y x = true → s y ≤ s x) →
    x ∈ frontier L dm := by
  intro h
  have := h [a, b, d] (strictPareto [0] costH) (fun z => costH z 0 / 2) a
    (by decide) (by decide) (by decide)
  exact absurd this (by decide)

-- S, minimality: a strict score is not enough without minimality.
theorem need_min : ¬ ∀ (L : List P) (dm : P → P → Bool) (s : P → Int) (x : P),
    x ∈ L → (∀ y, y ∈ L → dm y x = true → s y < s x) → x ∈ frontier L dm := by
  intro h
  have := h L2 (strictPareto [0] cost1) (fun z => cost1 z 0) a (by decide) (by decide)
  exact absurd this (by decide)

-- Weights: a = (0,1), b = (0,0); b dominates a on [0,1].
def costW : P → Nat → Int
  | a, 0 => 0 | a, _ => 1
  | b, _ => 0
  | c, _ => 4 | d, _ => 4 | e, _ => 4

theorem need_pos_zero_weight : ¬ ∀ (axes : List Nat) (w : Nat → Int) (cost : P → Nat → Int),
    (∀ i, i ∈ axes → 0 ≤ w i) → ∀ (L : List P) (x : P), x ∈ L →
    (∀ y, y ∈ L → weightedCost axes w cost x ≤ weightedCost axes w cost y) →
    x ∈ frontier L (strictPareto axes cost) := by
  intro h
  have := h [0, 1] (fun i => if i = 0 then 1 else 0) costW (by decide) L2 a (by decide)
    (by decide)
  exact absurd this (by decide)

theorem need_pos_negative_weight : ¬ ∀ (axes : List Nat) (w : Nat → Int) (cost : P → Nat → Int),
    ∀ (L : List P) (x : P), x ∈ L →
    (∀ y, y ∈ L → weightedCost axes w cost x ≤ weightedCost axes w cost y) →
    x ∈ frontier L (strictPareto axes cost) := by
  intro h
  have := h [0, 1] (fun i => if i = 0 then 1 else -1) costW L2 a (by decide) (by decide)
  exact absurd this (by decide)

-- Single axis: minimizing axis 0 does NOT put a point on the [0,1] frontier.
-- axis_minimizer_on_frontier is only about the frontier over [i] itself.
theorem need_single_axis_frontier : ¬ ∀ (axes : List Nat) (i : Nat) (cost : P → Nat → Int),
    i ∈ axes → ∀ (L : List P) (x : P), x ∈ L → (∀ y, y ∈ L → cost x i ≤ cost y i) →
    x ∈ frontier L (strictPareto axes cost) := by
  intro h
  have := h [0, 1] 0 costW (by decide) L2 a (by decide) (by decide)
  exact absurd this (by decide)

/-! ## 3. Encoding gaps -/

-- Empty axes: strictPareto [] never fires, so every frontier is the whole list
-- and every F/S statement over [] is trivially true.
theorem empty_axes (cost : P → Nat → Int) (L : List P) :
    frontier L (strictPareto [] cost) = L := by
  simp [frontier, strictPareto]

-- Duplicate axes change nothing for dominance.
theorem dup_axes (cost : P → Nat → Int) (y x : P) :
    strictPareto [0, 0] cost y x = strictPareto [0] cost y x := by
  simp [strictPareto]

-- Duplicate candidates: frontier keeps multiplicity, certificate (contains-based)
-- forgets it. Fine for membership claims, wrong for any count claim.
theorem dup_candidates_frontier :
    frontier [a, a, b] (strictPareto [0] cost1) = [b] ∧
    frontier [b, b, a] (strictPareto [0] cost1) = [b, b] := by decide
theorem dup_candidates_certificate :
    certificate [b, b, a] [b] (strictPareto [0] cost1) = true := by decide

-- Int vs Nat: truncating costs with Int.toNat preserves ≤ but not <.
def costNeg : P → Nat → Int
  | a, _ => -1 | b, _ => -2 | c, _ => 0 | d, _ => 0 | e, _ => 0
def costTrunc (z : P) (i : Nat) : Int := ((costNeg z i).toNat : Int)
theorem trunc_changes_frontier :
    frontier L2 (strictPareto [0] costNeg) = [b] ∧
    frontier L2 (strictPareto [0] costTrunc) = [a, b] := by decide
-- A truncated score is not strict, and its minimizer can be Int-dominated.
theorem trunc_score_breaks_S : ¬ ∀ (L : List P) (x : P), x ∈ L →
    (∀ y, y ∈ L → (costNeg x 0).toNat ≤ (costNeg y 0).toNat) →
    x ∈ frontier L (strictPareto [0] costNeg) := by
  intro h
  have := h L2 a (by decide) (by decide)
  exact absurd this (by decide)

/-! ## 4. Converse of S fails for weighted sums (non-supported frontier point) -/

def costC : P → Nat → Int
  | a, 0 => 0 | a, _ => 4
  | b, 0 => 4 | b, _ => 0
  | c, _ => 3
  | d, _ => 9 | e, _ => 9
def LC : List P := [a, b, c]

theorem converse_on_frontier : c ∈ frontier LC (strictPareto [0, 1] costC) := by decide

theorem converse_fails : ∀ w : Nat → Int, (∀ i, i ∈ [0, 1] → 0 < w i) →
    ¬ ∀ y, y ∈ LC → weightedCost [0, 1] w costC c ≤ weightedCost [0, 1] w costC y := by
  intro w hw h
  have h0 := hw 0 (by decide)
  have h1 := hw 1 (by decide)
  have ha := h a (by decide)
  have hb := h b (by decide)
  simp [weightedCost, costC] at ha hb
  omega

-- But the converse of the GENERAL S is trivially true (a constant score works,
-- because the strictness premise is vacuous at a frontier point). So
-- minimizer_on_frontier is equivalent to frontier membership; its content is
-- entirely in the axis/weighted instances.
theorem general_S_converse (L : List P) (dm : P → P → Bool) (x : P)
    (hx : x ∈ frontier L dm) :
    ∃ s : P → Int, x ∈ L ∧ (∀ y, y ∈ L → s x ≤ s y) ∧
      (∀ y, y ∈ L → dm y x = true → s y < s x) := by
  have ⟨hxL, hnd⟩ := (frontier_exact L dm x).mp hx
  refine ⟨fun _ => 0, hxL, fun _ _ => Int.le_refl _, fun y hy hd => ?_⟩
  rw [hnd y hy] at hd
  contradiction

/-! ## 5. Strengthenings found by this attempt now live in FiniteFrontier
    (`minimizer_on_frontier` with minimality only against x's own dominators,
    and `frontier_nonempty_of_ranked`). The chain below is ranked but not
    transitive: the ranked theorem covers it, `frontier_nonempty_of_strict`
    does not. -/

-- The chain is ranked but not transitive: the ranked version covers it, the
-- shipped frontier_nonempty_of_strict does not.
theorem chain_not_transitive : chain a b = true ∧ chain b c = true ∧ chain a c = false := by decide
theorem chain_ranked_nonempty : ∃ y, y ∈ frontier L3 chain :=
  frontier_nonempty_of_ranked L3 chain (fun | a => 0 | b => 1 | _ => 2)
    (by
      have h : ∀ x, x ∈ L3 → ∀ y, y ∈ L3 →
          (chain y x = true → (fun | a => (0 : Int) | b => 1 | _ => 2) y <
            (fun | a => (0 : Int) | b => 1 | _ => 2) x) := by decide
      exact fun x y hx hy => h x hx y hy)
    (by decide)

#print axioms need_irr_complete
#print axioms need_irr_nonempty
#print axioms need_trans_complete
#print axioms need_trans_no_certificate
#print axioms need_trans_nonempty
#print axioms need_nonempty
#print axioms need_strict_constant
#print axioms need_strict_weak_monotone
#print axioms need_min
#print axioms need_pos_zero_weight
#print axioms need_pos_negative_weight
#print axioms need_single_axis_frontier
#print axioms trunc_changes_frontier
#print axioms trunc_score_breaks_S
#print axioms converse_fails
#print axioms general_S_converse
#print axioms chain_ranked_nonempty
#print axioms nv_pdiv_cert
#print axioms nv_weighted

end FrontierObligationsControls
