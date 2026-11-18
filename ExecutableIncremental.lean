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

/-- Normalize stored fact lists without changing the set observed by selection. -/
private theorem eraseDups_loop_mem (xs acc : List A) (a : A) :
    a ∈ List.eraseDups.loop xs acc ↔ a ∈ xs ∨ a ∈ acc := by
  induction xs generalizing acc with
  | nil => simp [List.eraseDups.loop]
  | cons x xs ih =>
    simp only [List.eraseDups.loop, List.elem_eq_mem]
    split
    next yes =>
      rw [ih]
      have hx : x ∈ acc := of_decide_eq_true yes
      constructor
      · rintro (member | member)
        · exact Or.inl (List.mem_cons_of_mem x member)
        · exact Or.inr member
      · rintro (member | member)
        · rcases List.mem_cons.mp member with rfl | member
          · exact Or.inr hx
          · exact Or.inl member
        · exact Or.inr member
    next no =>
      rw [ih]
      simp only [List.mem_cons, or_assoc, or_left_comm]

private theorem eraseDups_mem (xs : List A) (a : A) :
    a ∈ xs.eraseDups ↔ a ∈ xs := by
  simpa only [List.eraseDups, List.not_mem_nil, or_false] using eraseDups_loop_mem xs [] a

private theorem eraseDups_loop_nodup (xs acc : List A) (h : acc.Nodup) :
    (List.eraseDups.loop xs acc).Nodup := by
  induction xs generalizing acc with
  | nil => simpa only [List.eraseDups.loop, List.Nodup, List.pairwise_reverse, ne_comm] using h
  | cons x xs ih =>
    simp only [List.eraseDups.loop, List.elem_eq_mem]
    split
    next yes => exact ih acc h
    next no =>
      apply ih
      exact List.nodup_cons.mpr ⟨by simpa using no, h⟩

private theorem eraseDups_nodup (xs : List A) : xs.eraseDups.Nodup :=
  eraseDups_loop_nodup xs [] List.nodup_nil


def update (old new : Snapshot A) (cache : List A) : List A :=
  let invalid := saturate (dirtySeeds old new) (arcs new.rules)
  (saturate (new.roots ++ difference cache invalid)
    (new.rules.filter (fun r => decide (r.2 ∈ invalid)))).eraseDups

/-- Dirtiness is consumed only by membership in the two stable filters. The
    new-only arc projection therefore preserves the exact normalized result,
    even before imposing the separate old-cache validity obligation. -/
theorem update_reference_exact (old new : Snapshot A) (cache : List A) :
    update old new cache =
      (saturate (new.roots ++ difference cache (dirty old new))
        (new.rules.filter (fun r => decide (r.2 ∈ dirty old new)))).eraseDups := by
  simp only [update, difference, new_arcs_suffice]

def Exact (s : Snapshot A) (cache : List A) := ∀ a, a ∈ cache ↔ derives s.graph a

theorem update_exact (old new : Snapshot A) (cache : List A) (hc : Exact old cache) :
    Exact new (update old new cache) := by
  have cache_spec : ∀ x, x ∈ cache ↔ derives old.graph x := hc
  intro a
  rw [update_reference_exact]
  rw [eraseDups_mem, saturate_exact, ← incremental_exact old.graph new.graph]
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

def full (s : Snapshot A) := (saturate s.roots s.rules).eraseDups

theorem full_exact (s : Snapshot A) : Exact s (full s) := by
  intro a
  exact (eraseDups_mem _ a).trans (saturate_exact _ _ a)

/-- Exported caches contain each fact at most once, even if input roots,
    rules, or imported caches repeat it. Temporary evaluator lists may repeat. -/
theorem full_nodup (s : Snapshot A) : (full s).Nodup := eraseDups_nodup _

theorem update_nodup (old new : Snapshot A) (cache : List A) :
    (update old new cache).Nodup := eraseDups_nodup _

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

theorem reachable_nodup {s : Snapshot A} {cache} (h : Reachable s cache) :
    cache.Nodup := by
  cases h with
  | initial s => exact full_nodup s
  | advance => exact update_nodup _ _ _

private theorem nodup_length_le (xs ys : List A) (unique : xs.Nodup)
    (subset : ∀ a ∈ xs, a ∈ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨absent, tailUnique⟩ := List.nodup_cons.mp unique
    have present : a ∈ ys := subset a List.mem_cons_self
    have tailSubset : ∀ b ∈ xs, b ∈ ys.erase a := by
      intro b hb
      have different : b ≠ a := by
        intro same
        subst b
        exact absent hb
      exact (List.mem_erase_of_ne different).mpr
        (subset b (List.mem_cons_of_mem _ hb))
    have smaller := ih (ys.erase a) tailUnique tailSubset
    have nonempty := List.length_pos_of_mem present
    rw [List.length_erase_of_mem present] at smaller
    simp only [List.length_cons]
    omega

private theorem exact_unique_length {s : Snapshot A}
    {xs ys : List A} (ux : xs.Nodup) (uy : ys.Nodup)
    (ex : Exact s xs)
    (ey : Exact s ys) : xs.length = ys.length := by
  apply Nat.le_antisymm
  · exact nodup_length_le xs ys ux (fun a ha => (ey a).mpr ((ex a).mp ha))
  · exact nodup_length_le ys xs uy (fun a ha => (ex a).mpr ((ey a).mp ha))


/-- A normalized reachable cache stores exactly one copy of each derivable fact.
    Its size depends on the current closure, not the number of past revisions. -/
theorem reachable_length_eq_full {s : Snapshot A} {cache} (h : Reachable s cache) :
    cache.length = (full s).length :=
  exact_unique_length (reachable_nodup h) (full_nodup s) (reachable_exact h) (full_exact s)

theorem advance_same_length (s : State A) :
    (advance s s.snapshot).cache.length = s.cache.length :=
  (reachable_length_eq_full (Reachable.advance s.history s.snapshot)).trans
    (reachable_length_eq_full s.history).symm

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
#print axioms update_reference_exact
#print axioms update_exact
#print axioms full_nodup
#print axioms update_nodup
#print axioms reachable_nodup
#print axioms reachable_length_eq_full
#print axioms advance_same_length
#print axioms reachable_exact
#print axioms frontier_eq_full
end ExecutableIncremental
