import ScopedEvidence
import LinearSelection
import EligibleSchedules
namespace ScopedSelection
variable {T : Type} [DecidableEq T]

def gate (policies : T → ScopedEvidence.Policy)
    (evidence : T → List ScopedEvidence.Receipt) (x : T) :=
  ScopedEvidence.qualify (policies x) (evidence x)

def certificate (candidates : List T) (policies : T → ScopedEvidence.Policy)
    (evidence : T → List ScopedEvidence.Receipt) (axes : List Nat)
    (cost : T → Nat → Int) (x : T) :=
  EligibleSchedules.optimumCertificate candidates (gate policies evidence) axes cost x

theorem certified_scoped_optimum (candidates : List T) (policies : T → ScopedEvidence.Policy)
    (evidence : T → List ScopedEvidence.Receipt) (axes : List Nat)
    (cost : T → Nat → Int) (x : T)
    (h : certificate candidates policies evidence axes cost x = true) :
    x ∈ candidates ∧ ScopedEvidence.qualify (policies x) (evidence x) = true ∧
    (∀ q, q ∈ (policies x).required →
      ∃ r, r ∈ evidence x ∧ r.scope = q.scope ∧ r.round = q.round ∧
        r.observedPass = true ∧ ∃ t, r.elapsed = some t ∧ t ≤ q.limit) ∧
    ∀ y, y ∈ candidates → ScopedEvidence.qualify (policies y) (evidence y) = true →
      ¬ ((∀ i, i ∈ axes → cost y i ≤ cost x i) ∧
         (∃ i, i ∈ axes ∧ cost y i < cost x i)) := by
  obtain ⟨⟨hm,hq⟩,hn⟩ := (EligibleSchedules.optimumCertificate_exact candidates
    (gate policies evidence) axes cost x).mp h
  exact ⟨hm,hq,ScopedEvidence.qualification_witnesses (policies x) (evidence x) hq,hn⟩

def select (candidates : List T) (policies : T → ScopedEvidence.Policy)
    (evidence : T → List ScopedEvidence.Receipt) (cost : T → Int) :=
  LinearSelection.select cost (candidates.filter (gate policies evidence))

omit [DecidableEq T] in
theorem selected_scoped_minimum (candidates : List T) (policies : T → ScopedEvidence.Policy)
    (evidence : T → List ScopedEvidence.Receipt) (cost : T → Int) (x : T)
    (h : select candidates policies evidence cost = some x) :
    (x ∈ candidates ∧ ScopedEvidence.qualify (policies x) (evidence x) = true) ∧
    ∀ y, y ∈ candidates → ScopedEvidence.qualify (policies y) (evidence y) = true →
      cost x ≤ cost y :=
  LinearSelection.selected_eligible_minimum cost (gate policies evidence) candidates x h

def selectAll (candidates : List T) (policies : T → ScopedEvidence.Policy)
    (evidence : T → List ScopedEvidence.Receipt) (cost : T → Int) :=
  LinearSelection.allMinima cost (candidates.filter (gate policies evidence))

omit [DecidableEq T] in
theorem selected_all_exact (candidates : List T) (policies : T → ScopedEvidence.Policy)
    (evidence : T → List ScopedEvidence.Receipt) (cost : T → Int) (x : T) :
    x ∈ selectAll candidates policies evidence cost ↔
      (x ∈ candidates ∧ ScopedEvidence.qualify (policies x) (evidence x) = true) ∧
      ∀ y, y ∈ candidates → ScopedEvidence.qualify (policies y) (evidence y) = true →
        cost x ≤ cost y := by
  simp only [selectAll,LinearSelection.allMinima_exact,List.mem_filter,gate]
  constructor
  · rintro ⟨hx,hm⟩; exact ⟨hx,fun y hy hg => hm y ⟨hy,hg⟩⟩
  · rintro ⟨hx,hm⟩; exact ⟨hx,fun y hy => hm y hy.1 hy.2⟩

omit [DecidableEq T] in
theorem selected_all_order_independent (xs ys : List T)
    (policies : T → ScopedEvidence.Policy) (evidence : T → List ScopedEvidence.Receipt)
    (cost : T → Int) (same : ∀ x, x ∈ xs ↔ x ∈ ys) :
    ∀ x, x ∈ selectAll xs policies evidence cost ↔ x ∈ selectAll ys policies evidence cost := by
  apply LinearSelection.allMinima_order_independent
  intro x
  simp only [List.mem_filter,same]

#print axioms selected_all_exact
#print axioms selected_all_order_independent
#print axioms certified_scoped_optimum
#print axioms selected_scoped_minimum
end ScopedSelection
