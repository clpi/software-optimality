import composition.QualifiedSelection

namespace TraceSafety

structure Machine (S E : Type) where
  initial : S → Prop
  step : S → E → S → Prop

inductive Path {S E : Type} (m : Machine S E) : S → List E → S → Prop
  | nil (s) : Path m s [] s
  | cons : m.step s e t → Path m t es u → Path m s (e :: es) u

def admits (m : Machine S E) (trace : List E) : Prop :=
  ∃ s t, m.initial s ∧ Path m s trace t

/-- A forward simulation may translate events and change state representation.
    It retains the visible order of the translated events. -/
structure Simulation (m : Machine S E) (n : Machine T D) (view : E → D) where
  related : S → T → Prop
  initial : ∀ s, m.initial s → ∃ t, n.initial t ∧ related s t
  advance : ∀ s t, related s t → ∀ e s', m.step s e s' →
    ∃ t', n.step t (view e) t' ∧ related s' t'

theorem Simulation.path {m : Machine S E} {n : Machine T D} {view : E → D}
    (sim : Simulation m n view) {s es u} (p : Path m s es u) :
    ∀ t, sim.related s t → ∃ v, Path n t (es.map view) v ∧ sim.related u v := by
  induction p with
  | nil _ => exact fun t h => ⟨t,.nil _,h⟩
  | cons hs _ ih =>
    intro t hr
    obtain ⟨t', hstep, hrel⟩ := sim.advance _ t hr _ _ hs
    obtain ⟨v, hp, hv⟩ := ih t' hrel
    exact ⟨v,.cons hstep hp,hv⟩

theorem Simulation.trace {m : Machine S E} {n : Machine T D} {view : E → D}
    (sim : Simulation m n view) {es} (h : admits m es) : admits n (es.map view) := by
  obtain ⟨s, _, hi, hp⟩ := h
  obtain ⟨t, ht, hr⟩ := sim.initial s hi
  obtain ⟨v, hv, _⟩ := sim.path hp t hr
  exact ⟨t,v,ht,hv⟩

def Simulation.comp {m : Machine S E} {n : Machine T D} {p : Machine V L}
    {f : E → D} {g : D → L} (first : Simulation m n f) (second : Simulation n p g) :
    Simulation m p (g ∘ f) where
  related s v := ∃ t, first.related s t ∧ second.related t v
  initial s hs := by
    obtain ⟨t,ht,hst⟩ := first.initial s hs
    obtain ⟨v,hv,htv⟩ := second.initial t ht
    exact ⟨v,hv,t,hst,htv⟩
  advance s v h e s' hs := by
    obtain ⟨t,hst,htv⟩ := h
    obtain ⟨t',ht,hst'⟩ := first.advance s t hst e s' hs
    obtain ⟨v',hv,htv'⟩ := second.advance t v htv (f e) t' ht
    exact ⟨v',hv,t',hst',htv'⟩

/-- Semantic interpretation is an explicit obligation. It can carry a proof
    about an unbounded state system through a finite release catalogue. -/
theorem selected_trace_safety {C F S E T D : Type} [DecidableEq F]
    (data : QualifiedSelection.Campaign C F) (u roots : List F)
    (rules : QualifiedClosure.Rules F) (catalogue out : List C) (inc c : C)
    (success : QualifiedSelection.select data u roots rules catalogue inc = some out) (hc : c ∈ out)
    (b : F) (required : b ∈ data.behaviors) (truth : F → Prop)
    (rootValid : ∀ a, a ∈ roots → truth a)
    (ruleValid : Qualification.Closed (QualifiedClosure.graph roots rules).edges truth)
    (m : Machine S E) (n : Machine T D) (view : E → D)
    (decode : truth (data.supports c b) → Nonempty (Simulation m n view))
    (safe : List D → Prop) (spec : ∀ tr, admits n tr → safe tr) :
    ∀ tr, admits m tr → safe (tr.map view) := by
  let g := QualifiedClosure.graph roots rules
  have obligations := (QualifiedSelection.release_evidence data u roots rules g catalogue out inc c success hc).1
  have h := obligations (data.supports c b) (List.mem_map.mpr ⟨b,required,rfl⟩)
  have hd := (HypergraphIncremental.incremental_exact g g _).mp h
  obtain ⟨sim⟩ := decode (Qualification.soundness rootValid ruleValid _ hd)
  exact fun tr ht => spec _ (sim.trace ht)

-- A stopped implementation has only the empty trace. Forward simulation can
-- establish prefix safety even when the implementation can never make progress.
private def stopped : Machine Unit Unit := ⟨fun _ => True, fun _ _ _ => False⟩
private def ticking : Machine Unit Unit := ⟨fun _ => True, fun _ _ _ => True⟩
example : Nonempty (Simulation stopped ticking id) ∧ ¬ admits stopped [()] ∧ admits ticking [()] := by
  refine ⟨⟨⟨fun _ _ => True, fun _ _ => ⟨(), trivial, trivial⟩,
    fun _ _ _ _ _ h => False.elim h⟩⟩, ?_, ⟨(), (), trivial, .cons trivial (.nil _)⟩⟩
  rintro ⟨_, _, _, h⟩
  cases h with | cons hs _ => exact hs

#print axioms Simulation.trace
#print axioms Simulation.comp
#print axioms selected_trace_safety
end TraceSafety
