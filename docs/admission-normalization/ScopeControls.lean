import AdmissionHypergraph
import AdmissionTests
open Admission AdmissionTests AdmissionHypergraph
-- Identical content cannot cross lineage when no transfer edge is decoded.
def noEdge (_ : Key) (_ : Payload) (_ : List ScopedAtom) (_ : ScopedAtom) : Prop := False
example : ¬ HypergraphIncremental.derives (scopedGraph noEdge yes [c]) (kb,p) := by
 intro h
 have liveB : live yes [c] kb p := Qualification.least
  (X := fun a => live yes [c] a.1 a.2)
  (fun a hr => (scoped_root_exact noEdge yes [c] a.1 a.2).mp hr)
  (by intro ps a hr _; rcases hr with ⟨k,p,_,hf⟩; exact False.elim hf) (kb,p) h
 have hn : checkLive yes [c] kb p = false := by decide
 have ht := (checkLive_correct yes [c] kb p).mpr liveB
 rw [hn] at ht
 contradiction
-- An explicit live transfer edge can carry qualification across lineages.
def transfer (_ : Key) (_ : Payload) (ps : List ScopedAtom) (a : ScopedAtom) : Prop :=
 ps = [(ka,p)] ∧ a = (kb,p)
example : HypergraphIncremental.derives (scopedGraph transfer yes [c]) (kb,p) := by
 have hl : live yes [c] ka p := (checkLive_correct _ _ _ _).mp (by decide)
 apply Qualification.Derives.step (ps := [(ka,p)])
 · exact ⟨ka,p,hl,⟨rfl,rfl⟩⟩
 · intro a ha
   simp only [List.mem_singleton] at ha
   subst a
   exact .root ((scoped_root_exact transfer yes [c] ka p).mpr hl)
