import Std

namespace ContextualDominance

abbrev Cost (Axis : Type) := Axis → Nat

def NoWorse {Axis : Type} (x y : Cost Axis) : Prop := ∀ a, x a ≤ y a

def StrictlyBetter {Axis : Type} (x y : Cost Axis) : Prop :=
  NoWorse x y ∧ ∃ a, x a < y a

-- The context can represent the entire rest of a component topology.
def Replaces {Ctx Component Axis : Type}
    (feasible : Ctx → Component → Prop) (cost : Ctx → Component → Cost Axis)
    (x y : Component) : Prop :=
  ∀ c, feasible c y → feasible c x ∧ NoWorse (cost c x) (cost c y)

theorem replacement_refl {Ctx Component Axis : Type}
    (feasible : Ctx → Component → Prop) (cost : Ctx → Component → Cost Axis)
    (x : Component) : Replaces feasible cost x x := by
  intro c h
  exact ⟨h, fun _ => Nat.le_refl _⟩

theorem replacement_trans {Ctx Component Axis : Type}
    {feasible : Ctx → Component → Prop} {cost : Ctx → Component → Cost Axis}
    {x y z : Component} (hxy : Replaces feasible cost x y)
    (hyz : Replaces feasible cost y z) : Replaces feasible cost x z := by
  intro c hz
  obtain ⟨hy, cy⟩ := hyz c hz
  obtain ⟨hx, cx⟩ := hxy c hy
  exact ⟨hx, fun a => Nat.le_trans (cx a) (cy a)⟩

-- Local metrics suffice ONLY with these explicit composition obligations.
theorem monotone_context_replacement {Ctx Component LocalAxis Axis : Type}
    (localCost : Component → Cost LocalAxis)
    (compose : Ctx → Cost LocalAxis → Cost Axis)
    (feasible : Ctx → Component → Prop)
    (feasibility : ∀ c x y, NoWorse (localCost x) (localCost y) →
      feasible c y → feasible c x)
    (monotonicity : ∀ c u v, NoWorse u v → NoWorse (compose c u) (compose c v))
    {x y : Component} (h : NoWorse (localCost x) (localCost y)) :
    Replaces feasible (fun c z => compose c (localCost z)) x y := by
  intro c hy
  exact ⟨feasibility c x y h hy, monotonicity c _ _ h⟩

-- This definition preserves *all achievable upper bounds*, not identities.
def Attains {Component Axis : Type} (members : Component → Prop)
    (feasible : Component → Prop) (cost : Component → Cost Axis)
    (bound : Cost Axis) : Prop :=
  ∃ x, members x ∧ feasible x ∧ NoWorse (cost x) bound

-- Every removed candidate has a feasible no-worse retained representative.
theorem pruning_preserves_attainable_bounds {Component Axis : Type}
    (original retained feasible : Component → Prop) (cost : Component → Cost Axis)
    (subset : ∀ x, retained x → original x)
    (coverage : ∀ y, original y → feasible y →
      ∃ x, retained x ∧ feasible x ∧ NoWorse (cost x) (cost y))
    (bound : Cost Axis) :
    Attains original feasible cost bound ↔ Attains retained feasible cost bound := by
  constructor
  · rintro ⟨y, hy, fy, cy⟩
    obtain ⟨x, hx, fx, cx⟩ := coverage y hy fy
    exact ⟨x, hx, fx, fun a => Nat.le_trans (cx a) (cy a)⟩
  · rintro ⟨x, hx, fx, cx⟩
    exact ⟨x, subset x hx, fx, cx⟩

def Pareto {Component Axis : Type} (members feasible : Component → Prop)
    (cost : Component → Cost Axis) (y : Component) : Prop :=
  members y ∧ feasible y ∧
    ∀ x, members x → feasible x → ¬ StrictlyBetter (cost x) (cost y)

-- A no-worse representative of an original Pareto point has the SAME costs.
theorem pareto_representative_same_cost {Component Axis : Type}
    {members feasible : Component → Prop} {cost : Component → Cost Axis}
    {x y : Component} (py : Pareto members feasible cost y)
    (mx : members x) (fx : feasible x) (nw : NoWorse (cost x) (cost y)) :
    ∀ a, cost x a = cost y a := by
  intro a
  apply Nat.le_antisymm (nw a)
  by_cases h : cost y a ≤ cost x a
  · exact h
  · have lt : cost x a < cost y a := Nat.lt_of_not_ge h
    exact False.elim (py.2.2 x mx fx ⟨nw, a, lt⟩)

-- Scoped preservation of Pareto objective vectors under representative pruning.
theorem pareto_vector_survives_pruning {Component Axis : Type}
    {original retained feasible : Component → Prop} {cost : Component → Cost Axis}
    (subset : ∀ x, retained x → original x)
    (coverage : ∀ y, original y → feasible y →
      ∃ x, retained x ∧ feasible x ∧ NoWorse (cost x) (cost y))
    {y : Component} (py : Pareto original feasible cost y) :
    ∃ x, Pareto retained feasible cost x ∧ ∀ a, cost x a = cost y a := by
  obtain ⟨x, rx, fx, nw⟩ := coverage y py.1 py.2.1
  have eqc := pareto_representative_same_cost py (subset x rx) fx nw
  refine ⟨x, ⟨rx, fx, ?_⟩, eqc⟩
  intro z rz fz better
  apply py.2.2 z (subset z rz) fz
  constructor
  · intro a
    rw [← eqc a]
    exact better.1 a
  · obtain ⟨a, ha⟩ := better.2
    exact ⟨a, by rw [← eqc a]; exact ha⟩

-- Retained Pareto points cannot be spurious under the same coverage obligation.
theorem retained_pareto_is_original {Component Axis : Type}
    {original retained feasible : Component → Prop} {cost : Component → Cost Axis}
    (subset : ∀ x, retained x → original x)
    (coverage : ∀ y, original y → feasible y →
      ∃ x, retained x ∧ feasible x ∧ NoWorse (cost x) (cost y))
    {x : Component} (px : Pareto retained feasible cost x) :
    Pareto original feasible cost x := by
  refine ⟨subset x px.1, px.2.1, ?_⟩
  intro y oy fy better
  obtain ⟨z, rz, fz, nw⟩ := coverage y oy fy
  apply px.2.2 z rz fz
  constructor
  · exact fun a => Nat.le_trans (nw a) (better.1 a)
  · obtain ⟨a, ha⟩ := better.2
    exact ⟨a, Nat.lt_of_le_of_lt (nw a) ha⟩

def localTime (x : Bool) : Nat := if x then 1 else 2
def contendedTime (x : Bool) : Nat := localTime x + if x then 100 else 0
example : localTime true < localTime false ∧
    contendedTime true > contendedTime false := by decide

-- Actual, kernel-reduced counterexamples: local improvement can reverse globally.
example : (1 : Nat) < 2 ∧ 101 > 2 := by decide
example : ¬ Replaces (fun (_ : Unit) (x : Nat) => x ≥ 2)
    (fun _ x (_ : Unit) => x) 1 2 := by
  intro h
  have bad := (h () (by decide)).1
  omega

-- Monotone max composition erases strictness and preserves two Pareto identities.
def capped (x : Bool) (_ : Unit) : Nat := max (if x then 1 else 2) 10
example : capped true = capped false := by funext a; cases a; rfl
example : Pareto (fun (_ : Bool) => True) (fun _ => True) capped false := by
  refine ⟨trivial, trivial, ?_⟩
  intro x _ _ h
  obtain ⟨a, ha⟩ := h.2
  cases x <;> cases a <;> simp [capped] at ha <;> omega
example : ¬ (fun (x : Bool) => x = true) false := by decide

#print axioms retained_pareto_is_original
#print axioms replacement_trans
#print axioms monotone_context_replacement
#print axioms pruning_preserves_attainable_bounds
#print axioms pareto_representative_same_cost
#print axioms pareto_vector_survives_pruning
end ContextualDominance
