import HypergraphIncremental

namespace ExecutableIncremental
open HypergraphIncremental
variable {A : Type} [DecidableEq A]

abbrev Rule (A : Type) := List A × A

structure Snapshot (A : Type) where
  roots : List A
  rules : List (Rule A)

def Snapshot.graph (s : Snapshot A) : Hypergraph A :=
  ⟨(· ∈ s.roots), fun ps a => (ps, a) ∈ s.rules⟩

def enabled (facts : List A) (r : Rule A) := r.1.all (fun x => decide (x ∈ facts))

private theorem shorter {rs : List (Rule A)} {r : Rule A} (hr : r ∈ rs) :
    (rs.erase r).length < rs.length := by
  rw [List.length_erase_of_mem hr]
  have := List.length_pos_of_mem hr
  omega

/-- Every firing consumes one pending rule. This list evaluator prioritizes
    auditability and does not require an externally supplied finite universe. -/
def saturate (facts : List A) (rs : List (Rule A)) : List A :=
  match _h : rs.find? (enabled facts) with
  | none => facts
  | some r => saturate (r.2 :: facts) (rs.erase r)
termination_by rs.length
decreasing_by exact shorter (List.mem_of_find?_eq_some (by assumption))

private theorem firing {facts : List A} {rs : List (Rule A)} {r : Rule A}
    (hr : r ∈ rs) (en : enabled facts r = true) (a : A) :
    derives (Snapshot.graph ⟨r.2 :: facts, rs.erase r⟩) a ↔
    derives (Snapshot.graph ⟨facts, rs⟩) a := by
  have ready : ∀ p ∈ r.1, p ∈ facts := by simpa [enabled] using en
  constructor
  · apply Qualification.least
    · intro x hx
      change x ∈ r.2 :: facts at hx
      rcases List.mem_cons.mp hx with h | h
      · subst x
        exact .step (ps := r.1) (by simpa using hr) (fun p hp => .root (ready p hp))
      · exact .root h
    · intro ps x h ih
      exact .step (List.mem_of_mem_erase h) ih
  · apply Qualification.least
    · intro x h
      exact .root (List.mem_cons_of_mem _ h)
    · intro ps x h ih
      by_cases same : (ps,x) = r
      · exact .root (List.mem_cons.mpr (Or.inl (congrArg Prod.snd same)))
      · exact .step ((List.mem_erase_of_ne same).mpr h) ih

theorem saturate_exact (facts : List A) (rs : List (Rule A)) (a : A) :
    a ∈ saturate facts rs ↔ derives (Snapshot.graph ⟨facts, rs⟩) a := by
  rw [saturate]
  split
  next h =>
    refine ⟨Qualification.Derives.root, Qualification.least (fun _ hx => hx) ?_ a⟩
    intro ps x hr hyp
    exact False.elim ((List.find?_eq_none.mp h) _ hr (by simpa [enabled] using hyp))
  next r h =>
    exact (saturate_exact _ _ a).trans (firing (List.mem_of_find?_eq_some h) (List.find?_some h) a)
termination_by rs.length
decreasing_by exact shorter (List.mem_of_find?_eq_some (by assumption))

def difference (xs ys : List A) := xs.filter (fun x => decide (x ∉ ys))
def changed (xs ys : List A) := difference xs ys ++ difference ys xs

private theorem mem_changed (xs ys : List A) (a : A) :
    a ∈ changed xs ys ↔ ¬ (a ∈ xs ↔ a ∈ ys) := by
  by_cases x : a ∈ xs <;> by_cases y : a ∈ ys <;> simp [changed, difference, x, y]

/-- Generated transiently from edges. Unary rules here propagate dirtiness only. -/
def arcs (rs : List (Rule A)) : List (Rule A) :=
  rs.flatMap (fun r => r.1.map (fun p => ([p], r.2)))

omit [DecidableEq A] in
private theorem mem_arcs (rs : List (Rule A)) (ps : List A) (a : A) :
    (ps,a) ∈ arcs rs ↔ ∃ p, ps = [p] ∧ ∃ body, (body,a) ∈ rs ∧ p ∈ body := by
  simp only [arcs, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨⟨body,x⟩, hr, p, hp, he⟩
    cases he
    exact ⟨p,rfl,body,hr,hp⟩
  · rintro ⟨p,rfl,body,hr,hp⟩
    exact ⟨(body,a),hr,p,hp,rfl⟩

def dirtySeeds (old new : Snapshot A) :=
  changed old.roots new.roots ++ (changed old.rules new.rules).map Prod.snd

def dirty (old new : Snapshot A) :=
  saturate (dirtySeeds old new) (arcs old.rules ++ arcs new.rules)

theorem dirty_exact (old new : Snapshot A) (a : A) :
    a ∈ dirty old new ↔ Affected old.graph new.graph a := by
  unfold dirty
  rw [saturate_exact]
  constructor
  · apply Qualification.least
    · intro x hx
      change x ∈ dirtySeeds old new at hx
      rcases List.mem_append.mp hx with hr | he
      · exact .root ((mem_changed _ _ _).mp hr)
      · obtain ⟨⟨ps,y⟩,hm,rfl⟩ := List.mem_map.mp he
        exact .edge ((mem_changed _ _ _).mp hm)
    · intro ps x he hp
      rcases List.mem_append.mp he with ho | hn
      · obtain ⟨p,rfl,body,hm,hi⟩ := (mem_arcs _ _ _).mp ho
        exact .downstream (hp p (by simp)) (Or.inl ⟨body,hm,hi⟩)
      · obtain ⟨p,rfl,body,hm,hi⟩ := (mem_arcs _ _ _).mp hn
        exact .downstream (hp p (by simp)) (Or.inr ⟨body,hm,hi⟩)
  · intro h
    induction h with
    | root hr => exact .root (List.mem_append.mpr (Or.inl ((mem_changed _ _ _).mpr hr)))
    | @edge ps x he =>
      exact .root (List.mem_append.mpr (Or.inr (List.mem_map.mpr
        ⟨(ps,x), (mem_changed _ _ _).mpr he, rfl⟩)))
    | @downstream p x _ dep ih =>
      apply Qualification.Derives.step (ps := [p])
      · apply List.mem_append.mpr
        rcases dep with ⟨body,he,hp⟩ | ⟨body,he,hp⟩
        · exact Or.inl ((mem_arcs _ _ _).mpr ⟨p,rfl,body,he,hp⟩)
        · exact Or.inr ((mem_arcs _ _ _).mpr ⟨p,rfl,body,he,hp⟩)
      · simpa using ih

/-- Once *every* changed rule head is already a seed, old-only arcs
    are redundant for propagation. Computing the seeds still reads both
    snapshots. This alternative is an extensional result about dirtiness. -/
theorem new_arcs_suffice (old new : Snapshot A) (a : A) :
    a ∈ saturate (dirtySeeds old new) (arcs new.rules) ↔ a ∈ dirty old new := by
  rw [saturate_exact,dirty_exact]
  constructor
  · intro h
    apply (dirty_exact old new a).mp
    unfold dirty
    rw [saturate_exact]
    exact Qualification.monotone (fun _ hx => hx)
      (fun _ _ he => List.mem_append.mpr (Or.inr he)) a h
  · intro h
    induction h with
    | root hr => exact .root (List.mem_append.mpr (Or.inl ((mem_changed _ _ _).mpr hr)))
    | @edge ps x he =>
      exact .root (List.mem_append.mpr (Or.inr (List.mem_map.mpr
        ⟨(ps,x), (mem_changed _ _ _).mpr he, rfl⟩)))
    | @downstream p x _ dep ih =>
      have follow (hn : dependency new.graph p x) :
          derives (Snapshot.graph ⟨dirtySeeds old new, arcs new.rules⟩) x := by
        obtain ⟨ps,he,hp⟩ := hn
        exact .step (ps := [p]) ((mem_arcs _ _ _).mpr ⟨p,rfl,ps,he,hp⟩) (by simpa using ih)
      rcases dep with ⟨ps,he,hp⟩ | hn
      · by_cases present : (ps,x) ∈ new.rules
        · exact follow ⟨ps,present,hp⟩
        · have changedRule : ¬ ((ps,x) ∈ old.rules ↔ (ps,x) ∈ new.rules) :=
            fun eqv => present (eqv.mp he)
          exact .root (List.mem_append.mpr (Or.inr (List.mem_map.mpr
            ⟨(ps,x), (mem_changed _ _ _).mpr changedRule,rfl⟩)))
      · exact follow hn

def update (old new : Snapshot A) (cache : List A) : List A :=
  let invalid := dirty old new
  saturate (new.roots ++ difference cache invalid)
    (new.rules.filter (fun r => decide (r.2 ∈ invalid)))

def Exact (s : Snapshot A) (cache : List A) := ∀ a, a ∈ cache ↔ derives s.graph a

theorem update_exact (old new : Snapshot A) (cache : List A) (hc : Exact old cache) :
    Exact new (update old new cache) := by
  have cache_spec : ∀ x, x ∈ cache ↔ derives old.graph x := hc
  intro a
  unfold update
  rw [saturate_exact, ← incremental_exact old.graph new.graph]
  apply Iff.intro
  · apply Qualification.monotone
    · intro x hx
      change x ∈ new.roots ++ difference cache (dirty old new) at hx
      simpa only [difference, List.mem_append, List.mem_filter, decide_eq_true_eq,
        dirty_exact, cache_spec, and_comm] using hx
    · intro ps x hx
      simpa only [Snapshot.graph, List.mem_filter, decide_eq_true_eq, dirty_exact] using hx
  · apply Qualification.monotone
    · intro x hx
      change x ∈ new.roots ++ difference cache (dirty old new)
      simpa only [difference, List.mem_append, List.mem_filter, decide_eq_true_eq,
        dirty_exact, cache_spec, and_comm] using hx
    · intro ps x hx
      simpa only [Snapshot.graph, List.mem_filter, decide_eq_true_eq, dirty_exact] using hx

def full (s : Snapshot A) := saturate s.roots s.rules

theorem full_exact (s : Snapshot A) : Exact s (full s) := saturate_exact _ _

/-- Reachable cache states start at a full evaluation and can only advance by update. -/
inductive Reachable : Snapshot A → List A → Prop where
  | initial (s) : Reachable s (full s)
  | advance {old cache} (valid : Reachable old cache) (new : Snapshot A) :
      Reachable new (update old new cache)

/-- Caches produced by this API carry their snapshot and a proof of origin.
    The proof is erased at runtime. -/
structure State (A : Type) [DecidableEq A] where
  snapshot : Snapshot A
  cache : List A
  history : Reachable snapshot cache

def start (s : Snapshot A) : State A := ⟨s, full s, .initial s⟩
def advance (s : State A) (next : Snapshot A) : State A :=
  ⟨next, update s.snapshot next s.cache, .advance s.history next⟩

theorem reachable_exact {s : Snapshot A} {cache} (h : Reachable s cache) : Exact s cache := by
  induction h with
  | initial s => exact full_exact s
  | advance _ _ ih => exact update_exact _ _ _ ih

theorem state_eq_full {s : Snapshot A} {cache} (h : Reachable s cache) :
    (fun a => decide (a ∈ cache)) = (fun a => decide (a ∈ full s)) := by
  funext a
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using (reachable_exact h a).trans (full_exact s a).symm

/-- Candidates, policy and axes can change at each revision. The projector
    observes set membership, so discovery order and duplicate facts are hidden. -/
theorem frontier_eq_full {C : Type} {s : Snapshot A} {cache} (h : Reachable s cache)
    (candidates : List C) (project : (A → Bool) → C → Profile) :
    frontier candidates (project (fun a => decide (a ∈ cache))) =
    frontier candidates (project (fun a => decide (a ∈ full s))) := by
  rw [state_eq_full h]

#print axioms saturate_exact
#print axioms dirty_exact
#print axioms new_arcs_suffice
#print axioms update_exact
#print axioms reachable_exact
#print axioms frontier_eq_full
end ExecutableIncremental
