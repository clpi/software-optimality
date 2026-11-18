import SoftwareIsQuantifiable.Coloring
import SoftwareIsQuantifiable.Fold
import HypergraphIncremental

namespace QualifiedClosure
open SoftwareIsQuantifiable

variable {A : Type} [DecidableEq A]

abbrev Rules (A : Type) := List (List A × A)

def horn (rules : Rules A) : List (Coloring.Rule A) :=
  rules.map (fun r => ⟨r.1, r.2⟩)

def graph (roots : List A) (rules : Rules A) : HypergraphIncremental.Hypergraph A :=
  ⟨fun a => a ∈ roots, fun ps a => (ps, a) ∈ rules⟩

theorem derivations_agree (roots : List A) (rules : Rules A) (a : A) :
    Coloring.Deriv (horn rules) (Fold.account roots) a ↔
    HypergraphIncremental.derives (graph roots rules) a := by
  constructor
  · intro h
    induction h with
    | seed h => exact .root (Fold.account_eq_true_iff.mp h)
    | apply hm _ ih =>
      obtain ⟨⟨ps, b⟩, hmem, heq⟩ := List.mem_map.mp hm
      cases heq
      exact .step hmem ih
  · intro h
    induction h with
    | root h => exact .seed (Fold.account_eq_true_iff.mpr h)
    | @step ps b hr _ ih =>
      apply Coloring.Deriv.apply (r := ⟨ps, b⟩) _ ih
      exact List.mem_map.mpr ⟨(ps, b), hr, rfl⟩

omit [DecidableEq A] in
private theorem boundedHeads (rules : Rules A) (u : List A)
    (hb : ∀ ps a, (ps, a) ∈ rules → a ∈ u) :
    ∀ r ∈ horn rules, r.conclusion ∈ u := by
  intro r hr
  obtain ⟨⟨ps,b⟩, hm, rfl⟩ := List.mem_map.mp hr
  exact hb ps b hm

def fired (rules : Rules A) (known : List A) : List A :=
  (rules.filter (fun r => r.1.all (fun p => decide (p ∈ known)))).map Prod.snd

def scan (u : List A) (rules : Rules A) (known : List A) : List A :=
  let heads := fired rules known
  u.filter (fun a => decide (a ∈ known ∨ a ∈ heads))

def rounds (u roots : List A) (rules : Rules A) : Nat → List A
  | 0 => roots
  | n + 1 => scan u rules (rounds u roots rules n)

theorem fired_exact (rules : Rules A) (known : List A) (a : A) :
    a ∈ fired rules known ↔ ∃ ps, (ps, a) ∈ rules ∧ ∀ p ∈ ps, p ∈ known := by
  simp only [fired, List.mem_map, List.mem_filter, List.all_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨ps,b⟩, ⟨hr,hp⟩, rfl⟩
    exact ⟨ps,hr,hp⟩
  · rintro ⟨ps,hr,hp⟩
    exact ⟨(ps,a),⟨hr,hp⟩,rfl⟩

private theorem one_step (rules : Rules A) (s : Coloring.State A) (a : A) :
    Coloring.step (horn rules) s a = true ↔
    s a = true ∨ ∃ ps, (ps,a) ∈ rules ∧ ∀ p ∈ ps, s p = true := by
  simp only [Coloring.step, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, Coloring.holds_eq_true]
  apply or_congr_right
  constructor
  · rintro ⟨r, hr, ha, hp⟩
    obtain ⟨⟨ps, b⟩, hm, rfl⟩ := List.mem_map.mp hr
    exact ⟨ps, ha ▸ hm, hp⟩
  · rintro ⟨ps, hr, hp⟩
    exact ⟨⟨ps, a⟩, List.mem_map.mpr ⟨(ps, a), hr, rfl⟩, rfl, hp⟩

theorem rounds_exact (u roots : List A) (rules : Rules A)
    (hb : ∀ a ∈ roots, a ∈ u) (hr : ∀ ps a, (ps,a) ∈ rules → a ∈ u)
    (n : Nat) (a : A) :
    a ∈ rounds u roots rules n ↔ Coloring.iter (horn rules) n (Fold.account roots) a = true := by
  induction n generalizing a with
  | zero => exact Fold.account_eq_true_iff.symm
  | succ n ih =>
    simp only [rounds, scan, List.mem_filter, decide_eq_true_eq, fired_exact,
      Coloring.iter, one_step, ← ih]
    constructor
    · exact And.right
    · intro h
      refine ⟨?_, h⟩
      rcases h with h | ⟨ps, hm, _⟩
      · cases n with
        | zero => exact hb a h
        | succ _ => exact (List.mem_filter.mp h).1
      · exact hr ps a hm

/-- Identical bounded-input check to the exhaustive reference. -/
def checked (u roots : List A) (rules : Rules A) : Option (List A) :=
  if ExecutableClosure.boundedOK u roots rules then some (rounds u roots rules (u.length+1))
  else none

theorem checked_none (u roots : List A) (rules : Rules A) :
    checked u roots rules = none ↔ ExecutableClosure.checkedClose u roots rules = none := by
  unfold checked ExecutableClosure.checkedClose
  split <;> simp

theorem checked_exact (u roots : List A) (rules : Rules A) (out : List A)
    (h : checked u roots rules = some out) (old : HypergraphIncremental.Hypergraph A) (a : A) :
    (a ∈ out ↔ HypergraphIncremental.incremental old (graph roots rules) a) ∧
    (a ∈ out ↔ a ∈ ExecutableClosure.close u roots rules) := by
  unfold checked at h
  split at h
  · rename_i ok
    cases h
    obtain ⟨hb,hr⟩ := (ExecutableClosure.boundedOK_exact u roots rules).mp ok
    have hcol : Coloring.coloring (horn rules) u (Fold.account roots) a = true ↔
        Coloring.Deriv (horn rules) (Fold.account roots) a :=
      ⟨Coloring.coloring_sound _ _ _ a,
       Coloring.coloring_complete _ _ _ (boundedHeads rules u hr) a⟩
    have eqv := (rounds_exact u roots rules hb hr (u.length+1) a).trans
      (hcol.trans (derivations_agree roots rules a))
    exact ⟨eqv.trans (HypergraphIncremental.incremental_exact _ _ _).symm,
      eqv.trans (ExecutableClosure.close_exact u roots rules hb hr a).symm⟩
  · contradiction

theorem materialized_bound (u roots : List A) (rules : Rules A) (n : Nat) :
    (rounds u roots rules (n+1)).length ≤ u.length := by
  apply List.length_filter_le

#print axioms derivations_agree
#print axioms rounds_exact
#print axioms checked_none
#print axioms checked_exact
#print axioms materialized_bound
end QualifiedClosure
