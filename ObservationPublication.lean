import ObservationPlanning

namespace ObservationPlanning
open HistoricalEvidence

/-- Equality of the readings along the realized path suffices, including for
    policies that never visit the same sensors on their other branches. -/
theorem realized_path (observe : S → W → Bool) (p : Plan S) (x y : W)
    (agrees : ∀ s b, (s,b) ∈ transcript observe p x → observe s y = b) :
    transcript observe p y = transcript observe p x := by
  induction p with
  | stop => simp [transcript]
  | probe s f t ihf iht =>
    have hs : observe s y = observe s x := agrees s (observe s x) (by simp [transcript])
    cases hx : observe s x with
    | false =>
      have hy := hs.trans hx
      have tail := ihf (fun a b h => agrees a b (by simp [transcript,hx,h]))
      simp [transcript,hx,hy,tail]
    | true =>
      have hy := hs.trans hx
      have tail := iht (fun a b h => agrees a b (by simp [transcript,hx,h]))
      simp [transcript,hx,hy,tail]

/-- Select from the full joint frontier. For its realized path, a domain
    adapter supplies receipts entailing each actual read. Publishing a fresh
    batch then makes the selected solver return exactly the actual query value.
    The table can describe histories across multiple systems and revisions. -/
theorem joint_publication [DecidableEq S] (worlds : List W) (m : Model W) (questions : List Question)
    (ss : List S) (n : Nat) (engines : List (Engine E)) (budget : Engine E × Plan S → Bool)
    (axes : List (Axis W Question)) (observe : S → W → Bool) (cost : Engine E × Plan S → Nat → Int)
    (e : Engine E) (p : Plan S)
    (chosen : (e,p) ∈ joint engines ss n (fun ep => budget ep && resolves worlds questions m observe ep.2)
      axes observe cost)
    (version : String) (verify : Receipt → Bool) (auth : Event → Bool) (log : List Event)
    (todo : List (Question × Nat)) (stamp : Nat) (q : Question) (id : Nat)
    (requested : q ∈ questions) (scheduled : (q,id) ∈ todo)
    (actual : W) (consistent : actual ∈ survivors worlds m (roots verify (live auth log)))
    (reads : ∀ w ∈ survivors worlds m (roots verify (live auth log)), ∀ s b,
      (s,b) ∈ transcript observe p actual → observe s w = b)
    (ok : ready auth log (batch worlds m version verify (live auth log) todo stamp) = true)
    (v : Option Nat) :
    let pending := batch worlds m version verify (live auth log) todo stamp
    let rs := live auth (commitRows log pending)
    ⟨q,v⟩ ∈ e.close (atoms rs) (rules worlds m version rs) (roots verify rs) ↔ v = m actual q := by
  dsimp only
  rw [e.refines _ _ _ (automatic_bounds ..)]
  change Atom.mk q v ∈ solve _ _ _ _ _ ↔ _
  have nonempty := List.ne_nil_of_mem consistent
  apply (published_batch_exact worlds m version verify auth log todo stamp id q v scheduled nonempty ok).trans
  have feasible := ((joint_exact ..).mp chosen).2.2.1
  have resolved := (Bool.and_eq_true_iff.mp feasible).2
  have unique := (resolves_exact ..).mp resolved q requested
  constructor
  · intro h
    exact (h actual consistent).symm
  · rintro rfl w hw
    exact unique w actual ((survivors_exact ..).mp hw).1 ((survivors_exact ..).mp consistent).1
      (realized_path observe p actual w (reads w hw))

end ObservationPlanning
