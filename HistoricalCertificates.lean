import HistoricalEvidence

namespace HistoricalEvidence

/-- A registered Lean proof ranges over every admissible history, including
    infinite domains. Binding is to the complete typed row and model version. -/
structure RuleProof (possible : W → Prop) (m : Model W) (version : String) where
  row : Row
  shape : row.route.channel = .implication ∧ row.model = version ∧ row.receipt = none
  sound : ∀ w, possible w → (∀ a ∈ row.parents, m w a.question = a.value) →
    m w row.head.question = row.head.value

def RuleProof.fromFinite (ws : List W) (m : Model W) (v : String) (r : Row)
    (h : implication ws m v r = true) : RuleProof (fun w => w ∈ ws) m v :=
  ⟨r,of_decide_eq_true (Bool.and_eq_true_iff.mp h).1,implication_sound ws m v r h⟩

variable {W : Type} {possible : W → Prop} {m : Model W} {version : String}

def registered (ps : List (RuleProof possible m version)) (rs : List Row) :=
  let owners := ps.map RuleProof.row
  (rs.filter (fun r => decide (r ∈ owners))).map (fun r => (r.parents,r.head))

def closeRegistered (ps : List (RuleProof possible m version)) (verify : Receipt → Bool)
    (auth : Event → Bool) (log : List Event) :=
  let rs := live auth log
  WorklistClosure.wclose (atoms rs) (roots verify rs) (registered ps rs)

theorem registered_exact (ps : List (RuleProof possible m version)) (verify : Receipt → Bool)
    (auth : Event → Bool) (log : List Event) (a : Atom) :
    let rs := live auth log
    a ∈ closeRegistered ps verify auth log ↔ Qualification.Derives
      (fun x => x ∈ roots verify rs) (fun pre x => (pre,x) ∈ registered ps rs) a := by
  dsimp only
  apply WorklistClosure.wclose_exact
  · intro x hx
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hx
    exact (Admission.mem_unique ..).mpr (List.mem_flatMap.mpr ⟨r,(List.mem_filter.mp hr).1,List.mem_cons_self⟩)
  · intro pre x hx
    obtain ⟨r,hr,he⟩ := List.mem_map.mp hx
    cases he
    exact (Admission.mem_unique ..).mpr (List.mem_flatMap.mpr ⟨r,(List.mem_filter.mp hr).1,List.mem_cons_self⟩)

theorem registered_sound (ps : List (RuleProof possible m version)) (verify : Receipt → Bool)
    (auth : Event → Bool) (log : List Event) (w : W) (hw : possible w)
    (observed : ∀ r ∈ live auth log, measurement verify r = true → m w r.head.question = r.head.value)
    (a : Atom) (h : a ∈ closeRegistered ps verify auth log) : m w a.question = a.value := by
  apply Qualification.soundness (TrueAt := fun a => m w a.question = a.value) _ _ a ((registered_exact ..).mp h)
  · intro x hx
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hx
    exact observed r (List.mem_filter.mp hr).1 (List.mem_filter.mp hr).2
  · intro pre x hx hp
    obtain ⟨r,hr,he⟩ := List.mem_map.mp hx
    cases he
    obtain ⟨proof,_,rfl⟩ := List.mem_map.mp (of_decide_eq_true (List.mem_filter.mp hr).2)
    exact proof.sound w hw hp

end HistoricalEvidence
