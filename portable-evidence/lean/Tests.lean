import PortableAdapter
open PortableAdapter
namespace Tests
def context : Context := ⟨"artifact","lineage-A","env","harness","work","venue"⟩
def auth : Authority := ⟨context,"authority",fun _ => some "pass",fun _ => some "fail",fun s => some ("measurement:" ++ s)⟩
def r : Receipt := ⟨context,.observed,"case",.test .pass,"source",0,"authority","id"⟩
#guard normalize auth [] [r,r] == [r]
#guard supports auth [] [r] == [(r,"pass")]
#guard supports auth ["id"] [r] == []
#guard supports auth [] [{r with authorityDigest := "forged"}] == []
#guard supports auth [] [{r with context := {context with lineage := "B"}}] == []
#guard supports auth [] [{r with context := {context with artifact := "B"}}] == []
#guard supports auth [] [{r with context := {context with environment := "B"}}] == []
#guard supports auth [] [{r with context := {context with harness := "B"}}] == []
#guard supports auth [] [{r with context := {context with workload := "B"}}] == []
#guard supports auth [] [{r with context := {context with venue := "B"}}] == []
#guard supports auth [] [{r with classification := .proposed}] == []
#guard supports auth [] [{r with classification := .inferred}] == []
#guard supports auth [] [{r with payload := .test .skipped}] == []
#guard supports auth [] [{r with payload := .test .error}] == []
#guard atom auth {r with payload := .test .fail} == some "fail"
#guard atom auth {r with payload := .measurement []} == none
#guard atom auth {r with payload := .measurement [0,1,100]} == some "measurement:case"
#guard atom {auth with measurementAtom := fun _ => some "faster"} {r with payload := .measurement [1]} == none
#guard supports auth ["other-id"] [r] == [(r,"pass")]
-- Receipt emission preserves source/index, not just an untraceable atom.
#guard (supports auth [] [r]).head?.map (fun p => (p.1.sourceDigest,p.1.recordIndex)) == some ("source",0)
-- Withdrawing one origin need not remove a conclusion supported independently.
def r2 : Receipt := {r with id := "id2", sourceDigest := "source2"}
#guard supports auth ["id"] [r,r2] == [(r2,"pass")]
example : Derives (roots auth ["id"] [r,r2]) [] "pass" := by
  apply Derives.root
  exact ⟨r2, by decide⟩
end Tests
