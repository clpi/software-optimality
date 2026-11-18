import ContextualDominance
open ContextualDominance
-- Context-wide replacement cannot be justified by an isolated improvement.
example : ¬ Replaces (fun (_ : Unit) (_ : Bool) => True)
 (fun _ x (_ : Unit) => contendedTime x) true false := by
 intro h
 have bad := (h () trivial).2 ()
 simp [contendedTime,localTime] at bad
-- The max composition fixture preserves cost vectors but not all identities.
example : Pareto (fun (_ : Bool) => True) (fun _ => True) capped true := by
 refine ⟨trivial,trivial,?_⟩
 intro x _ _ h
 obtain ⟨a,ha⟩ := h.2
 cases x <;> cases a <;> simp [capped] at ha <;> omega
example : ∀ y : Bool, ∃ x : Bool, x = true ∧ NoWorse (capped x) (capped y) := by
 intro y; refine ⟨true,rfl,?_⟩
 intro a; cases y <;> cases a <;> decide
example : Attains (fun x : Bool => x = true) (fun _ => True) capped (fun _ => 10) := by
 exact ⟨true,rfl,trivial,fun a => by cases a; decide⟩
-- No representative coverage means pruning can genuinely lose an attainable bound.
example : ¬ Attains (fun _ : Bool => False) (fun _ => True) capped (fun _ => 10) := by
 rintro ⟨x,h,_⟩; exact h
-- Equal costs are not strict dominance.
example : ¬ StrictlyBetter (capped true) (capped false) := by
 rintro ⟨_,a,ha⟩; cases a; simp [capped] at ha; omega
