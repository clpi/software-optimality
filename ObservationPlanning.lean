import HistoricalRecovery
import FrontierComposition

namespace ObservationPlanning

variable {W S Q V : Type}

/-- Recoverability from an arbitrary observation, independently of catalogue size. -/
def Identifies (possible : W → Prop) (observe : W → S) (answer : W → V) :=
  ∀ x y, possible x → possible y → observe x = observe y → answer x = answer y

theorem factorization (possible : W → Prop) (observe : W → S) (answer : W → V) :
    Identifies possible observe answer ↔
      ∃ decode : S → Option V, ∀ w, possible w → decode (observe w) = some (answer w) := by
  classical
  constructor
  · intro h
    let decode := fun s => if ex : ∃ w, possible w ∧ observe w = s
      then some (answer (Classical.choose ex)) else none
    refine ⟨decode,?_⟩
    intro w hw
    have ex : ∃ v, possible v ∧ observe v = observe w := ⟨w,hw,rfl⟩
    simp only [decode,dif_pos ex,Option.some.injEq]
    exact h _ _ (Classical.choose_spec ex).1 hw (Classical.choose_spec ex).2
  · rintro ⟨decode,h⟩ x y hx hy same
    exact Option.some.inj ((h x hx).symm.trans ((congrArg decode same).trans (h y hy)))

theorem two_histories_refute (observe : W → S) (answer : W → V) (x y : W)
    (same : observe x = observe y) (different : answer x ≠ answer y) :
    ∀ guess : S → V, guess (observe x) ≠ answer x ∨ guess (observe y) ≠ answer y := by
  intro guess
  by_cases h : guess (observe x) = answer x
  · exact Or.inr (fun h' => different (h.symm.trans ((congrArg guess same).trans h')))
  · exact Or.inl h

inductive Plan (S : Type) where
  | stop
  | probe (sensor : S) (whenFalse whenTrue : Plan S)
  deriving Repr, DecidableEq, Lean.ToJson

def transcript (observe : S → W → Bool) : Plan S → W → List (S × Bool)
  | .stop, _ => []
  | .probe s f t, w =>
    let b := observe s w
    (s,b) :: transcript observe (if b then t else f) w
termination_by plan _ => sizeOf plan
decreasing_by split <;> decreasing_tactic

/-- Enumerate all binary policies up to a decision depth, including early
    stopping and repeated probes. Resource and admissibility constraints follow. -/
def plans (sensors : List S) : Nat → List (Plan S)
  | 0 => [.stop]
  | n+1 =>
    let sub := plans sensors n
    .stop :: sensors.flatMap (fun s => sub.flatMap (fun f => sub.map (Plan.probe s f)))

def planCount (sensorCount : Nat) : Nat → Nat
  | 0 => 1
  | n+1 => 1 + sensorCount * planCount sensorCount n * planCount sensorCount n

private theorem flat_count (xs : List A) (f : A → List B) (k : Nat)
    (each : ∀ x, (f x).length = k) : (xs.flatMap f).length = xs.length*k := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [each,ih,Nat.add_mul,Nat.add_comm]

theorem planCount_exact (ss : List S) (n : Nat) : (plans ss n).length = planCount ss.length n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [plans,List.length_cons]
    rw [flat_count ss _ ((plans ss n).length * (plans ss n).length) (fun _ =>
      flat_count (plans ss n) (fun f => (plans ss n).map (Plan.probe _ f)) _ (fun _ => List.length_map _))]
    simp [planCount,ih,Nat.mul_assoc,Nat.add_comm]

private def extend (k x : Nat) := 1 + k*x*x

private def grow (k : Nat) : Nat → Nat → Nat
  | 0,x => x
  | n+1,x => grow k n (extend k x)

private theorem grow_commutes (k n x : Nat) :
    grow k n (extend k x) = extend k (grow k n x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => exact ih (extend k x)

private theorem grow_count (k n : Nat) : grow k n 1 = planCount k n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [grow,planCount,← ih] using grow_commutes k n 1

private def boundedGrow (k cap : Nat) : Nat → Nat → Option Nat
  | 0,x => if x ≤ cap then some x else none
  | n+1,x => if x ≤ cap then boundedGrow k cap n (extend k x) else none

private theorem grow_ge (k n x : Nat) (hk : 0 < k) : x ≤ grow k n x := by
  have step (v : Nat) : v ≤ extend k v := by
    cases v with
    | zero => exact Nat.zero_le _
    | succ v =>
      have h1 : v+1 ≤ k*(v+1) := Nat.le_mul_of_pos_left _ hk
      have h2 : k*(v+1) ≤ k*(v+1)*(v+1) := Nat.le_mul_of_pos_right _ (Nat.zero_lt_succ _)
      unfold extend; omega
  induction n generalizing x with
  | zero => exact Nat.le_refl _
  | succ n ih => exact Nat.le_trans (step x) (ih _)

private theorem boundedGrow_exact (k cap n x : Nat) (hk : 0 < k) :
    boundedGrow k cap n x = if grow k n x ≤ cap then some (grow k n x) else none := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    by_cases h : x ≤ cap
    · simp [boundedGrow,grow,h,ih]
    · have hf : ¬ grow k (n+1) x ≤ cap := fun hg => h (Nat.le_trans (grow_ge k (n+1) x hk) hg)
      simp [boundedGrow,h,hf]

def boundedCount (k depth cap : Nat) : Option Nat :=
  if k = 0 then (if 1 ≤ cap then some 1 else none) else boundedGrow k cap depth 1

theorem boundedCount_exact (ss : List S) (n cap : Nat) :
    boundedCount ss.length n cap =
      if (plans ss n).length ≤ cap then some (plans ss n).length else none := by
  rw [planCount_exact]
  unfold boundedCount
  split
  next h =>
    have one : planCount 0 n = 1 := by cases n <;> simp [planCount]
    simp [h,one]
  next h => rw [boundedGrow_exact _ _ _ _ (Nat.pos_of_ne_zero h),grow_count]

def allowed (sensors : List S) : Nat → Plan S → Prop
  | _, .stop => True
  | 0, .probe .. => False
  | n+1, .probe s f t => s ∈ sensors ∧ allowed sensors n f ∧ allowed sensors n t

theorem plans_exact (sensors : List S) (n : Nat) (p : Plan S) :
    p ∈ plans sensors n ↔ allowed sensors n p := by
  induction n generalizing p with
  | zero => cases p <;> simp [plans,allowed]
  | succ n ih =>
    cases p with
    | stop => simp [plans,allowed]
    | probe s f t =>
      simp [plans,allowed,List.mem_flatMap,List.mem_map,ih,and_assoc]
      constructor
      · rintro ⟨_,hs,_,hf,_,ht,rfl,rfl,rfl⟩; exact ⟨hs,hf,ht⟩
      · rintro ⟨hs,hf,ht⟩; exact ⟨s,hs,f,hf,t,ht,rfl,rfl,rfl⟩

/-- Query-specific cross-world obligations, retaining each query and both
    worlds. Equal aggregate counts cannot substitute for the same distinctions. -/
structure Need (W Q : Type) where
  left : W
  right : W
  query : Q
  deriving Repr, DecidableEq

def needs [DecidableEq V] (ws : List W) (queries : List Q) (answer : W → Q → V) :=
  ws.flatMap (fun x => ws.flatMap (fun y =>
    (queries.filter (fun q => decide (answer x q ≠ answer y q))).map (Need.mk x y)))

theorem needs_exact [DecidableEq V] (ws : List W) (qs : List Q) (value : W → Q → V) (x y : W) (q : Q) :
    Need.mk x y q ∈ needs ws qs value ↔ x ∈ ws ∧ y ∈ ws ∧ q ∈ qs ∧ value x q ≠ value y q := by
  simp [needs,List.mem_flatMap,List.mem_map,and_assoc]
  constructor
  · rintro ⟨_,hx,_,hy,_,hq,hd,rfl,rfl,rfl⟩; exact ⟨hx,hy,hq,hd⟩
  · rintro ⟨hx,hy,hq,hd⟩; exact ⟨x,hx,y,hy,q,hq,hd,rfl,rfl,rfl⟩

def separates [DecidableEq S] (observe : S → W → Bool) (p : Plan S) (n : Need W Q) :=
  decide (transcript observe p n.left ≠ transcript observe p n.right)

def resolves [DecidableEq S] [DecidableEq V] (ws : List W) (qs : List Q)
    (value : W → Q → V) (observe : S → W → Bool) (p : Plan S) :=
  (needs ws qs value).all (separates observe p)

theorem resolves_exact [DecidableEq S] [DecidableEq V] (ws : List W) (qs : List Q)
    (value : W → Q → V) (observe : S → W → Bool) (p : Plan S) :
    resolves ws qs value observe p = true ↔ ∀ q ∈ qs,
      Identifies (fun w => w ∈ ws) (transcript observe p) (fun w => value w q) := by
  simp only [resolves,List.all_eq_true,separates,decide_eq_true_eq]
  constructor
  · intro h q hq x y hx hy same
    apply Classical.byContradiction
    intro bad
    exact h ⟨x,y,q⟩ ((needs_exact ..).mpr ⟨hx,hy,hq,bad⟩) same
  · intro h n hn same
    obtain ⟨hx,hy,hq,hd⟩ := (needs_exact ws qs value n.left n.right n.query).mp hn
    exact hd (h _ hq _ _ hx hy same)

def scanAll : List S → Plan S
  | [] => .stop
  | s :: ss => let tail := scanAll ss; .probe s tail tail

theorem scanAll_transcript (observe : S → W → Bool) (w : W) (ss : List S) :
    transcript observe (scanAll ss) w = ss.map (fun s => (s,observe s w)) := by
  induction ss with
  | nil => simp [scanAll,transcript]
  | cons s ss ih => simp [scanAll,transcript,ih]

theorem scan_allowed (ss all : List S) (subset : ∀ s ∈ ss, s ∈ all) :
    allowed all ss.length (scanAll ss) := by
  induction ss with
  | nil => trivial
  | cons s ss ih =>
    have tail := ih (fun t ht => subset t (List.mem_cons_of_mem _ ht))
    exact ⟨subset s List.mem_cons_self,tail,tail⟩

theorem indistinguishable_at_every_depth (ss : List S) (observe : S → W → Bool) (x y : W)
    (same : ∀ s ∈ ss, observe s x = observe s y) (n : Nat) (p : Plan S)
    (valid : allowed ss n p) : transcript observe p x = transcript observe p y := by
  induction n generalizing p with
  | zero => cases p with
            | stop => simp [transcript]
            | probe s f t => contradiction
  | succ n ih =>
    cases p with
    | stop => simp [transcript]
    | probe s f t =>
      obtain ⟨hs,hf,ht⟩ := valid
      simp only [transcript,same s hs]
      cases he : observe s y <;> simp [ih f hf,ih t ht]

/-- Without resource constraints, sensing all named deterministic probes once
    is already complete for existence of a solution at ANY finite depth. -/
theorem full_observability_iff [DecidableEq S] [DecidableEq V] (ss : List S) (ws : List W)
    (qs : List Q) (value : W → Q → V) (observe : S → W → Bool) :
    (∃ n p, allowed ss n p ∧ resolves ws qs value observe p = true) ↔
      (∀ x ∈ ws, ∀ y ∈ ws, (∀ s ∈ ss, observe s x = observe s y) →
        ∀ q ∈ qs, value x q = value y q) := by
  constructor
  · rintro ⟨n,p,valid,h⟩ x hx y hy same q hq
    exact (resolves_exact ..).mp h q hq x y hx hy
      (indistinguishable_at_every_depth ss observe x y same n p valid)
  · intro separatesAll
    refine ⟨ss.length,scanAll ss,scan_allowed ss ss (fun _ h => h),(resolves_exact ..).mpr ?_⟩
    intro q hq x y hx hy equal
    rw [scanAll_transcript,scanAll_transcript] at equal
    have pairs := List.map_inj_left.mp equal
    exact separatesAll x hx y hy (fun s hs => congrArg Prod.snd (pairs s hs)) q hq

/-- An executable decoder for each actual transcript. Empty and ambiguous
    fibers keep their distinct diagnoses. -/
def decode [DecidableEq S] (ws : List W) (m : HistoricalEvidence.Model W)
    (q : HistoricalEvidence.Question) (observe : S → W → Bool) (p : Plan S) (trace : List (S × Bool)) :=
  HistoricalEvidence.diagnose m q (ws.filter (fun w => decide (transcript observe p w = trace)))

theorem decode_correct [DecidableEq S] (ws : List W) (m : HistoricalEvidence.Model W)
    (qs : List HistoricalEvidence.Question) (observe : S → W → Bool) (p : Plan S)
    (h : resolves ws qs m observe p = true) (w : W) (hw : w ∈ ws) (q : HistoricalEvidence.Question)
    (hq : q ∈ qs) : decode ws m q observe p (transcript observe p w) = .exact (m w q) := by
  apply (HistoricalEvidence.diagnose_exact ..).mpr
  have hm : w ∈ ws.filter (fun x => decide (transcript observe p x = transcript observe p w)) :=
    List.mem_filter.mpr ⟨hw,by simp⟩
  refine ⟨fun he => ?_,?_⟩
  · rw [he] at hm; contradiction
  · intro x hx
    exact (resolves_exact ..).mp h q hq x w (List.mem_filter.mp hx).1 hw
      (of_decide_eq_true (List.mem_filter.mp hx).2)

inductive Axis (W Q : Type) where
  | distinguish (need : Need W Q)
  | resource (id : Nat)

def objectives [DecidableEq V] (ws : List W) (qs : List Q) (value : W → Q → V) (resources : List Nat) :
    List (Axis W Q) := (needs ws qs value).map Axis.distinguish ++ resources.map Axis.resource

def score [DecidableEq S] (observe : S → W → Bool) (cost : Plan S → Nat → Int) (p : Plan S) :
    Axis W Q → Int
  | .distinguish n => if separates observe p n then -1 else 0
  | .resource i => cost p i

def dominates [DecidableEq S] (axes : List (Axis W Q)) (observe : S → W → Bool)
    (cost : Plan S → Nat → Int) (p r : Plan S) :=
  let atIndex := fun plan (i : Nat) => (axes[i]?.map (score observe cost plan)).getD 0
  FiniteFrontier.strictPareto (List.range axes.length) atIndex p r

theorem dominates_axes [DecidableEq S] (axes : List (Axis W Q)) (observe : S → W → Bool)
    (cost : Plan S → Nat → Int) (p r : Plan S) :
    dominates axes observe cost p r = true ↔
      (∀ a ∈ axes, score observe cost p a ≤ score observe cost r a) ∧
      ∃ a ∈ axes, score observe cost p a < score observe cost r a := by
  unfold dominates
  rw [FiniteFrontier.pareto_exact]
  constructor
  · rintro ⟨le,i,hi,lt⟩
    have h := List.mem_range.mp hi
    refine ⟨?_,axes[i],List.getElem_mem h,by simpa [List.getElem?_eq_getElem h] using lt⟩
    intro a ha
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp ha
    simpa [List.getElem?_eq_getElem hj] using le j (List.mem_range.mpr hj)
  · rintro ⟨le,a,ha,lt⟩
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp ha
    refine ⟨?_,j,List.mem_range.mpr hj,by simpa [List.getElem?_eq_getElem hj] using lt⟩
    intro i hi
    have h := List.mem_range.mp hi
    simpa [List.getElem?_eq_getElem h] using le axes[i] (List.getElem_mem h)

def optimal [DecidableEq S] (sensors : List S) (depth : Nat) (feasible : Plan S → Bool)
    (axes : List (Axis W Q)) (observe : S → W → Bool) (cost : Plan S → Nat → Int) :=
  FiniteFrontier.frontier ((plans sensors depth).filter feasible) (dominates axes observe cost)

theorem optimal_exact [DecidableEq S] (sensors : List S) (n : Nat) (ok : Plan S → Bool)
    (axes : List (Axis W Q)) (observe : S → W → Bool) (cost : Plan S → Nat → Int) (p : Plan S) :
    p ∈ optimal sensors n ok axes observe cost ↔ allowed sensors n p ∧ ok p = true ∧
      ∀ r, allowed sensors n r → ok r = true → dominates axes observe cost r p = false := by
  simp [optimal,FiniteFrontier.frontier_exact,List.mem_filter,plans_exact,and_assoc]

theorem optimal_realizes_required [DecidableEq S] (ws : List W) (m : HistoricalEvidence.Model W)
    (qs : List HistoricalEvidence.Question) (sensors : List S) (n : Nat) (budget : Plan S → Bool)
    (axes : List (Axis W HistoricalEvidence.Question)) (observe : S → W → Bool)
    (cost : Plan S → Nat → Int) (p : Plan S)
    (hp : p ∈ optimal sensors n (fun r => budget r && resolves ws qs m observe r) axes observe cost) :
    ∀ w ∈ ws, ∀ q ∈ qs, decode ws m q observe p (transcript observe p w) = .exact (m w q) := by
  exact decode_correct ws m qs observe p (Bool.and_eq_true_iff.mp ((optimal_exact ..).mp hp).2.1).2

/-- The full observation/solver product allows arbitrary joint costs and
    compatibility. The implementation and observer choices remain distinct. -/
structure Engine (E : Type) where
  id : E
  close : List HistoricalEvidence.Atom → List (List HistoricalEvidence.Atom × HistoricalEvidence.Atom) →
    List HistoricalEvidence.Atom → List HistoricalEvidence.Atom
  refines : ∀ u rules roots, ExecutableClosure.boundedOK u roots rules = true →
    close u rules roots = WorklistClosure.wclose u roots rules

def worklistEngine : Engine String :=
  ⟨"worklist",fun u rules roots => WorklistClosure.wclose u roots rules,fun _ _ _ _ => rfl⟩

def referenceEngine : Engine String where
  id := "exhaustive"
  close := fun u rules roots => ExecutableClosure.close u roots rules
  refines := by
    intro u rules roots h
    have both := WorklistClosure.worklist_agrees_checked u roots rules
    simpa [WorklistClosure.checkedWorklist,ExecutableClosure.checkedClose,h] using both.symm

def joint [DecidableEq S] (engines : List (Engine E)) (ss : List S) (n : Nat)
    (ok : Engine E × Plan S → Bool) (axes : List (Axis W Q)) (observe : S → W → Bool)
    (cost : Engine E × Plan S → Nat → Int) :=
  let catalogue := engines.flatMap (fun e => (plans ss n).map (fun p => (e,p)))
  let value := fun (ep : Engine E × Plan S) (i : Nat) =>
    (axes[i]?.map (score observe (fun _ => cost ep) ep.2)).getD 0
  FiniteFrontier.frontier (catalogue.filter ok) (FiniteFrontier.strictPareto (List.range axes.length) value)

theorem joint_exact [DecidableEq S] (engines : List (Engine E)) (ss : List S) (n : Nat)
    (ok : Engine E × Plan S → Bool) (axes : List (Axis W Q)) (observe : S → W → Bool)
    (cost : Engine E × Plan S → Nat → Int) (e : Engine E) (p : Plan S) :
    let value := fun (ep : Engine E × Plan S) (i : Nat) =>
      (axes[i]?.map (score observe (fun _ => cost ep) ep.2)).getD 0
    (e,p) ∈ joint engines ss n ok axes observe cost ↔
      e ∈ engines ∧ allowed ss n p ∧ ok (e,p) = true ∧
      ∀ f ∈ engines, ∀ r, allowed ss n r → ok (f,r) = true →
        FiniteFrontier.strictPareto (List.range axes.length) value (f,r) (e,p) = false := by
  simp only [joint,FiniteFrontier.frontier_exact,List.mem_filter,List.mem_flatMap,List.mem_map,
    plans_exact,Prod.mk.injEq]
  constructor
  · rintro ⟨⟨⟨_,he,_,hp,rfl,rfl⟩,ho⟩,hn⟩
    exact ⟨he,hp,ho,fun f hf r hr ok' => hn (f,r) ⟨⟨f,hf,r,hr,rfl⟩,ok'⟩⟩
  · rintro ⟨he,hp,ho,hn⟩
    refine ⟨⟨⟨e,he,p,hp,rfl,rfl⟩,ho⟩,?_⟩
    rintro _ ⟨⟨f,hf,r,hr,rfl⟩,ok'⟩
    exact hn f hf r hr ok'

theorem engine_instantiates_exactly (e : Engine E) (ws : List W) (m : HistoricalEvidence.Model W)
    (v : String) (verify : HistoricalEvidence.Receipt → Bool) (rs : List HistoricalEvidence.Row)
    (a : HistoricalEvidence.Atom) :
    a ∈ e.close (HistoricalEvidence.atoms rs) (HistoricalEvidence.rules ws m v rs)
      (HistoricalEvidence.roots verify rs) ↔
    HypergraphIncremental.derives (HistoricalEvidence.graph ws m v verify rs) a := by
  rw [e.refines _ _ _ (HistoricalEvidence.automatic_bounds ws m v verify rs)]
  exact HistoricalEvidence.solve_exact ..

end ObservationPlanning
