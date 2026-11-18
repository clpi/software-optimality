/- Language-independent qualification closure. No additional axioms or admissions.
   A denotes exact scoped support atoms, including lineage and polarity.
   R is the admitted relation of finite-premise inference/transfer certificates.
-/
namespace Qualification
universe u
variable {A : Type u}

inductive Derives (B : A → Prop) (R : List A → A → Prop) : A → Prop where
  | root {a} : B a → Derives B R a
  | step {ps a} : R ps a → (∀ p, p ∈ ps → Derives B R p) → Derives B R a

def Closed (R : List A → A → Prop) (X : A → Prop) : Prop :=
  ∀ ps a, R ps a → (∀ p, p ∈ ps → X p) → X a

theorem least {B : A → Prop} {R : List A → A → Prop} {X : A → Prop}
    (roots : ∀ a, B a → X a) (rules : Closed R X) :
    ∀ a, Derives B R a → X a := by
  intro a h
  induction h with
  | root hb => exact roots _ hb
  | step hr _ ih => exact rules _ _ hr ih

theorem closed (B : A → Prop) (R : List A → A → Prop) :
    Closed R (Derives B R) := by
  intro ps a hr hp
  exact Derives.step hr hp

theorem monotone {B C : A → Prop} {R S : List A → A → Prop}
    (hb : ∀ a, B a → C a) (hr : ∀ ps a, R ps a → S ps a) :
    ∀ a, Derives B R a → Derives C S a := by
  apply least
  · intro a h; exact Derives.root (hb a h)
  · intro ps a h hp; exact Derives.step (hr ps a h) hp

theorem idempotent (B : A → Prop) (R : List A → A → Prop) (a : A) :
    Derives (Derives B R) R a ↔ Derives B R a := by
  constructor
  · exact least (fun _ h => h) (closed B R) a
  · exact Derives.root

-- Compounding preserves every cross-input inference, not just union of results.
theorem compounding (B C : A → Prop) (R : List A → A → Prop) (a : A) :
    Derives (fun x => B x ∨ C x) R a ↔
    Derives (fun x => Derives B R x ∨ Derives C R x) R a := by
  constructor
  · apply monotone _ (fun _ _ h => h) a
    intro x h
    cases h with
    | inl hb => exact Or.inl (Derives.root hb)
    | inr hc => exact Or.inr (Derives.root hc)
  · apply least _ (closed (fun x => B x ∨ C x) R) a
    intro x h
    cases h with
    | inl hb => exact monotone (fun _ h => Or.inl h) (fun _ _ h => h) x hb
    | inr hc => exact monotone (fun _ h => Or.inr h) (fun _ _ h => h) x hc

-- Any exhaustive sound saturation result equals the same least closure.
theorem order_independent {B : A → Prop} {R : List A → A → Prop}
    {X Y : A → Prop}
    (bx : ∀ a, B a → X a) (by_ : ∀ a, B a → Y a)
    (cx : Closed R X) (cy : Closed R Y)
    (sx : ∀ a, X a → Derives B R a)
    (sy : ∀ a, Y a → Derives B R a) :
    ∀ a, X a ↔ Y a := by
  intro a
  exact ⟨fun h => least by_ cy a (sx a h), fun h => least bx cx a (sy a h)⟩

-- Semantic truth is conditional on validated roots and inference certificates.
theorem soundness {B TrueAt : A → Prop} {R : List A → A → Prop}
    (validRoots : ∀ a, B a → TrueAt a) (validRules : Closed R TrueAt) :
    ∀ a, Derives B R a → TrueAt a := least validRoots validRules

-- Withdrawals filter live roots and certificates; no historical fact is deleted.
def liveRoots (B withdrawn : A → Prop) : A → Prop := fun a => B a ∧ ¬ withdrawn a

def liveRules (R : List A → A → Prop) (withdrawn : List A → A → Prop) :=
  fun ps a => R ps a ∧ ¬ withdrawn ps a

theorem withdrawal_no_new_support (B withdrawn : A → Prop)
    (R deadRules : List A → A → Prop) :
    ∀ a, Derives (liveRoots B withdrawn) (liveRules R deadRules) a → Derives B R a :=
  monotone (fun _ h => h.1) (fun _ _ h => h.1)

-- Any derivation in a still-live subsystem survives withdrawal elsewhere.
theorem surviving_subsystem (B B0 withdrawn : A → Prop)
    (R R0 deadRules : List A → A → Prop)
    (rootsLive : ∀ a, B0 a → liveRoots B withdrawn a)
    (rulesLive : ∀ ps a, R0 ps a → liveRules R deadRules ps a) :
    ∀ a, Derives B0 R0 a →
      Derives (liveRoots B withdrawn) (liveRules R deadRules) a :=
  monotone rootsLive rulesLive

-- Cycles alone cannot create support when every rule needs a premise.
theorem no_bootstrap (R : List A → A → Prop)
    (nonempty : ∀ ps a, R ps a → ∃ p, p ∈ ps) :
    ∀ a, ¬ Derives (fun _ => False) R a := by
  apply least (X := fun _ => False)
  · intro _ h; exact h
  · intro ps a hr hp
    obtain ⟨p, hm⟩ := nonempty ps a hr
    exact hp p hm

#print axioms least
#print axioms monotone
#print axioms idempotent
#print axioms compounding
#print axioms order_independent
#print axioms soundness
#print axioms withdrawal_no_new_support
#print axioms surviving_subsystem
#print axioms no_bootstrap
end Qualification
