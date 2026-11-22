import FiniteFrontier

namespace FrontierComposition

variable {A B : Type}

/-- Removing candidates is justified by an actual retained, strictly better
    replacement for each missing identity. A tie alone cannot erase an identity. -/
structure Cover (d : A → A → Bool) (whole kept : List A) : Prop where
  subset : ∀ x ∈ kept, x ∈ whole
  replaces : ∀ x ∈ whole, x ∈ kept ∨ ∃ y ∈ kept, d y x = true

abbrev Transitive (d : A → A → Bool) :=
  ∀ {a b c}, d a b = true → d b c = true → d a c = true

def checkCover [DecidableEq A] (d : A → A → Bool) (whole kept : List A) : Bool :=
  kept.all (fun x => decide (x ∈ whole)) &&
    whole.all (fun x => decide (x ∈ kept) || kept.any (fun y => d y x))

theorem checkCover_exact [DecidableEq A] (d : A → A → Bool) (whole kept : List A) :
    checkCover d whole kept = true ↔ Cover d whole kept := by
  simp only [checkCover, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    decide_eq_true_eq, List.any_eq_true]
  exact ⟨fun ⟨hs, hr⟩ => ⟨hs, hr⟩, fun h => ⟨h.subset, h.replaces⟩⟩

theorem Cover.frontier_exact {d : A → A → Bool} {xs ys : List A}
    (h : Cover d xs ys) (tr : Transitive d) (x : A) :
    x ∈ FiniteFrontier.frontier xs d ↔ x ∈ FiniteFrontier.frontier ys d := by
  rw [FiniteFrontier.frontier_exact, FiniteFrontier.frontier_exact]
  constructor
  · rintro ⟨hx, hn⟩
    refine ⟨?_, fun z hz => hn z (h.subset z hz)⟩
    rcases h.replaces x hx with hk | ⟨z, hz, hd⟩
    · exact hk
    · simp [hn z (h.subset z hz)] at hd
  · rintro ⟨hx, hn⟩
    refine ⟨h.subset x hx, ?_⟩
    intro z hz
    cases hzx : d z x with
    | false => rfl
    | true =>
      rcases h.replaces z hz with hk | ⟨y, hy, hd⟩
      · simp [hn z hk] at hzx
      · have ht := tr hd hzx
        simp [hn y hy] at ht

theorem Cover.trans {d : A → A → Bool} {xs ys zs : List A}
    (first : Cover d xs ys) (second : Cover d ys zs) (tr : Transitive d) :
    Cover d xs zs := by
  refine ⟨fun x hx => first.subset x (second.subset x hx), ?_⟩
  intro x hx
  rcases first.replaces x hx with hy | ⟨y, hy, hd⟩
  · exact second.replaces x hy
  · right
    rcases second.replaces y hy with hz | ⟨z, hz, he⟩
    · exact ⟨y, hz, hd⟩
    · exact ⟨z, hz, tr he hd⟩

theorem Cover.append {d : A → A → Bool} {xs ys us vs : List A}
    (left : Cover d xs us) (right : Cover d ys vs) : Cover d (xs ++ ys) (us ++ vs) := by
  constructor
  · intro x hx
    exact List.mem_append.mpr ((List.mem_append.mp hx).imp (left.subset x) (right.subset x))
  · intro x hx
    rcases List.mem_append.mp hx with hl | hr
    · rcases left.replaces x hl with hu | ⟨y, hy, hd⟩
      · exact Or.inl (List.mem_append_left _ hu)
      · exact Or.inr ⟨y, List.mem_append_left _ hy, hd⟩
    · rcases right.replaces x hr with hv | ⟨y, hy, hd⟩
      · exact Or.inl (List.mem_append_right _ hv)
      · exact Or.inr ⟨y, List.mem_append_right _ hy, hd⟩

/-- Continuations return only legal completions. Each legal completion of a
    discarded candidate must survive by identity or have a better completion.
    Types, feasibility policies, and objective relations may change at the seam. -/
theorem Cover.flatMap {d : A → A → Bool} {e : B → B → Bool} {xs ys : List A}
    (h : Cover d xs ys) (finish : A → List B)
    (lift : ∀ y ∈ ys, ∀ x ∈ xs, d y x = true → ∀ b ∈ finish x,
      b ∈ finish y ∨ ∃ c ∈ finish y, e c b = true) :
    Cover e (xs.flatMap finish) (ys.flatMap finish) := by
  constructor
  · intro b hb
    obtain ⟨x, hx, hb⟩ := List.mem_flatMap.mp hb
    exact List.mem_flatMap.mpr ⟨x, h.subset x hx, hb⟩
  · intro b hb
    obtain ⟨x, hx, hb⟩ := List.mem_flatMap.mp hb
    rcases h.replaces x hx with hk | ⟨y, hy, hd⟩
    · exact Or.inl (List.mem_flatMap.mpr ⟨x, hk, hb⟩)
    · rcases lift y hy x hx hd b hb with hs | ⟨c, hc, he⟩
      · exact Or.inl (List.mem_flatMap.mpr ⟨y, hy, hs⟩)
      · exact Or.inr ⟨c, List.mem_flatMap.mpr ⟨y, hy, hc⟩, he⟩


theorem frontier_covers (d : A → A → Bool) (tr : Transitive d)
    (irr : ∀ a, d a a = false) (xs : List A) :
    Cover d xs (FiniteFrontier.frontier xs d) :=
  ⟨fun x hx => ((FiniteFrontier.frontier_exact _ _ x).mp hx).1,
   FiniteFrontier.frontier_complete_of_strict xs d (fun a _ => irr a)
     (fun _ _ _ _ _ _ hab hbc => tr hab hbc)⟩

/-- For a genuine subset of a finite catalogue this certificate is complete:
    every deletion preserving the entire frontier has a retained witness. -/
theorem checkCover_iff_same_frontier [DecidableEq A] (d : A → A → Bool)
    (tr : Transitive d) (irr : ∀ a, d a a = false) (xs ys : List A)
    (subset : ∀ x ∈ ys, x ∈ xs) :
    checkCover d xs ys = true ↔
    ∀ x, x ∈ FiniteFrontier.frontier xs d ↔ x ∈ FiniteFrontier.frontier ys d := by
  rw [checkCover_exact]
  constructor
  · exact fun h => h.frontier_exact tr
  · intro same
    have retain := fun x (hx : x ∈ FiniteFrontier.frontier xs d) =>
      ((FiniteFrontier.frontier_exact ys d x).mp ((same x).mp hx)).1
    refine ⟨subset, ?_⟩
    intro x hx
    rcases (frontier_covers d tr irr xs).replaces x hx with hk | ⟨y,hy,hd⟩
    · exact Or.inl (retain x hk)
    · exact Or.inr ⟨y, retain y hy, hd⟩

/-- The repository's final-frontier certificate is also complete under a
    strict partial order. A search engine may submit any ordering of the IDs. -/
theorem certificate_iff_frontier [DecidableEq A] (d : A → A → Bool)
    (tr : Transitive d) (irr : ∀ a, d a a = false) (xs ys : List A) :
    FiniteFrontier.certificate xs ys d = true ↔
      ∀ x, x ∈ ys ↔ x ∈ FiniteFrontier.frontier xs d := by
  constructor
  · exact fun h => FiniteFrontier.certified_frontier xs ys d h
  · intro same
    apply (FiniteFrontier.certificate_exact xs ys d).mpr
    refine ⟨fun x hx => (FiniteFrontier.frontier_exact xs d x).mp ((same x).mp hx), ?_⟩
    intro x hx
    rcases (frontier_covers d tr irr xs).replaces x hx with hf | ⟨y,hy,hd⟩
    · exact Or.inl ((same x).mpr hf)
    · exact Or.inr ⟨y,(same y).mpr hy,hd⟩

theorem partition_exact (d : A → A → Bool) (tr : Transitive d)
    (irr : ∀ a, d a a = false) (left right : List A) (x : A) :
    x ∈ FiniteFrontier.frontier (left ++ right) d ↔
    x ∈ FiniteFrontier.frontier
      (FiniteFrontier.frontier left d ++ FiniteFrontier.frontier right d) d :=
  ((frontier_covers d tr irr left).append (frontier_covers d tr irr right)).frontier_exact tr x

theorem pareto_transitive (axes : List Nat) (cost : A → Nat → Int) :
    Transitive (FiniteFrontier.strictPareto axes cost) := by
  intro a b c hab hbc
  obtain ⟨ab, i, hi, hs⟩ := (FiniteFrontier.pareto_exact ..).mp hab
  obtain ⟨bc, _⟩ := (FiniteFrontier.pareto_exact ..).mp hbc
  exact (FiniteFrontier.pareto_exact ..).mpr
    ⟨fun j hj => Int.le_trans (ab j hj) (bc j hj), i, hi, Int.lt_of_lt_of_le hs (bc i hi)⟩

theorem pareto_irreflexive (axes : List Nat) (cost : A → Nat → Int) (x : A) :
    FiniteFrontier.strictPareto axes cost x x = false := by
  simp [FiniteFrontier.strictPareto]

#print axioms checkCover_exact
#print axioms Cover.frontier_exact
#print axioms Cover.trans
#print axioms Cover.flatMap
#print axioms frontier_covers
#print axioms checkCover_iff_same_frontier
#print axioms certificate_iff_frontier
#print axioms partition_exact
#print axioms pareto_transitive
#print axioms pareto_irreflexive
end FrontierComposition
