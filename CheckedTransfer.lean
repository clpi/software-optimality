/- Checked cross-lineage transfer for the qualification closure.

Proven: the set a checked transfer claims from a source closure is exactly
the image of that closure under the checked relation; the image grows with
the support set; a target system whose only new roots are transferred
qualifications and whose only new rules are its own rules and the
single-premise transfer rules derives nothing beyond the combined system
that runs source rules, target rules and transfer rules side by side over
the union of the roots; the same exactness holds at the withdrawn (live)
source system, and the live image is contained in the full image, so
support that exists only in the withdrawn system contributes nothing
live; and a transfer creates no support from an unsupported cycle.

Not claimed: that any concrete pair of atoms is checked. Membership in
the transfer relation — agreement of environment, effect and harness
between the two lineages — is an input to this module, exactly as roots
and rules are inputs to Qualification. Lineage alone neither grants nor
forbids reuse; only membership in the checked relation does.
-/
import Qualification

namespace CheckedTransfer

universe u
variable {A : Type u}

/-- The single-premise rules induced by a checked transfer relation `T`:
`a` follows from the sole premise `b` exactly when the pair `b, a` is a
checked pair. -/
def transferRules (T : A → A → Prop) : List A → A → Prop :=
  fun ps a => ∃ b, ps = [b] ∧ T b a

/-- The qualifications a checked transfer claims from a support set `C`:
`a` is claimed exactly when some supported `b` is checked into `a`. -/
def image (T : A → A → Prop) (C : A → Prop) : A → Prop :=
  fun a => ∃ b, C b ∧ T b a

/-- Membership in a singleton list, proved by cases on the membership
derivation so that the transfer results below depend on no axioms at
all (the library form of this fact goes through propositional
extensionality). -/
theorem eq_of_mem_singleton {p b : A} (hp : p ∈ [b]) : p = b := by
  cases hp with
  | head => rfl
  | tail _ h => cases h

/-- The claimed set is exactly the image of the source closure: every
claimed qualification has a derived source premise checked into it, and
every such pair claims its target. No more, no less. -/
theorem image_exact (T : A → A → Prop) (B : A → Prop)
    (R : List A → A → Prop) (a : A) :
    image T (Qualification.Derives B R) a ↔
      ∃ b, Qualification.Derives B R b ∧ T b a :=
  Iff.rfl

/-- Enlarging the support set enlarges the claimed set. -/
theorem image_mono (T : A → A → Prop) {C C' : A → Prop}
    (h : ∀ x, C x → C' x) (a : A) :
    image T C a → image T C' a := by
  intro ha
  obtain ⟨b, hb, hT⟩ := ha
  exact ⟨b, h b hb, hT⟩

/-- A target derivation that takes transferred qualifications as roots
and transfer steps as rules never exceeds the combined system. The
containing predicate for the least principle is the combined closure
itself: it contains the target roots (target roots directly; a
transferred qualification by lifting its source derivation into the
combined system and taking one transfer step), and it is closed under
the target rules because both target rules and transfer rules are parts
of the combined rule relation. -/
theorem transfer_never_exceeds (T : A → A → Prop) (B B' : A → Prop)
    (R R' : List A → A → Prop) (a : A) :
    Qualification.Derives (fun x => B' x ∨ image T (Qualification.Derives B R) x)
        (fun ps y => R' ps y ∨ transferRules T ps y) a →
    Qualification.Derives (fun x => B x ∨ B' x)
        (fun ps y => R ps y ∨ R' ps y ∨ transferRules T ps y) a := by
  intro h
  refine Qualification.least (X := Qualification.Derives (fun x => B x ∨ B' x)
    (fun ps y => R ps y ∨ R' ps y ∨ transferRules T ps y)) ?_ ?_ a h
  · intro x hx
    cases hx with
    | inl hb' =>
      exact Qualification.Derives.root (Or.inr hb')
    | inr himg =>
      obtain ⟨b, hb, hT⟩ := himg
      have hbC : Qualification.Derives (fun x => B x ∨ B' x)
          (fun ps y => R ps y ∨ R' ps y ∨ transferRules T ps y) b :=
        Qualification.monotone (fun y hy => Or.inl hy)
          (fun ps y hy => Or.inl hy) b hb
      refine Qualification.Derives.step (ps := [b]) ?_ ?_
      · exact Or.inr (Or.inr ⟨b, rfl, hT⟩)
      · intro p hp
        have hp0 : p = b := eq_of_mem_singleton hp
        subst hp0
        exact hbC
  · intro ps x hr hp
    refine Qualification.closed _ _ ps x ?_ hp
    cases hr with
    | inl hR' => exact Or.inr (Or.inl hR')
    | inr hTr => exact Or.inr (Or.inr hTr)

/-- The image characterization at the withdrawn (live) source system:
the same exactness as `image_exact`, with live roots and live rules in
place of the full roots and rules. -/
theorem transfer_live_image_exact (T : A → A → Prop) (B : A → Prop)
    (w : A → Prop) (R : List A → A → Prop) (d : List A → A → Prop) (a : A) :
    image T (Qualification.Derives (Qualification.liveRoots B w)
        (Qualification.liveRules R d)) a ↔
      ∃ b, Qualification.Derives (Qualification.liveRoots B w)
        (Qualification.liveRules R d) b ∧ T b a :=
  image_exact T _ _ a

/-- Containment after withdrawal: the live image is contained in the
full image. So a transferred qualification whose source premise is
derivable only in the full system and not in the live system
contributes nothing to the live image through that premise: every live
claim is witnessed by a premise that is itself live. -/
theorem transfer_live_image_subset (T : A → A → Prop) (B : A → Prop)
    (w : A → Prop) (R : List A → A → Prop) (d : List A → A → Prop) (a : A) :
    image T (Qualification.Derives (Qualification.liveRoots B w)
        (Qualification.liveRules R d)) a →
    image T (Qualification.Derives B R) a :=
  image_mono T (fun x hx => Qualification.withdrawal_no_new_support B w R d x hx) a

/-- A transfer manufactures no support from an unsupported cycle: when
every source rule needs a premise, the empty-root source closure is
empty by `Qualification.no_bootstrap`, so its image is empty too. -/
theorem transfer_no_bootstrap (T : A → A → Prop) (R : List A → A → Prop)
    (nonempty : ∀ ps y, R ps y → ∃ p, p ∈ ps) (a : A) :
    ¬ image T (Qualification.Derives (fun _ => False) R) a := by
  intro h
  obtain ⟨b, hb, _hT⟩ := h
  exact Qualification.no_bootstrap R nonempty b hb

/-- Guard, positive: a qualification crosses lineages through a checked
pair and the combined system derives it. Source lineage: root `0` and
the rule `[0]` to `1`, so `1` is derived. Target lineage: root `5` and
the rule `[5]` to `6`. The checked relation holds of the pair `1, 2`,
so `2` — underivable in either lineage alone — is derived in the
combined system, via `transfer_never_exceeds` applied to the target
derivation that takes `2` as a transferred root. -/
example : Qualification.Derives (fun x : Nat => x = 0 ∨ x = 5)
    (fun ps y => (ps = [0] ∧ y = 1) ∨ (ps = [5] ∧ y = 6) ∨
      transferRules (fun b a => b = 1 ∧ a = 2) ps y) 2 := by
  have hsrc : Qualification.Derives (fun x : Nat => x = 0)
      (fun ps y => ps = [0] ∧ y = 1) 1 := by
    refine Qualification.Derives.step (ps := [0]) ⟨rfl, rfl⟩ ?_
    intro p hp
    have hp0 : p = 0 := eq_of_mem_singleton hp
    subst hp0
    exact Qualification.Derives.root rfl
  have htgt : Qualification.Derives
      (fun x : Nat => x = 5 ∨ image (fun b a => b = 1 ∧ a = 2)
        (Qualification.Derives (fun x : Nat => x = 0)
          (fun ps y => ps = [0] ∧ y = 1)) x)
      (fun ps y => (ps = [5] ∧ y = 6) ∨
        transferRules (fun b a => b = 1 ∧ a = 2) ps y) 2 := by
    refine Qualification.Derives.root ?_
    exact Or.inr ⟨1, hsrc, ⟨rfl, rfl⟩⟩
  exact transfer_never_exceeds (fun b a => b = 1 ∧ a = 2) (fun x : Nat => x = 0)
    (fun x : Nat => x = 5) (fun ps y => ps = [0] ∧ y = 1)
    (fun ps y => ps = [5] ∧ y = 6) 2 htgt

/-- Guard, negative: the atom `2` is reachable only through the pair
`1, 2`, which is not checked here — the checked relation holds of the
pair `1, 3` instead. So `2` is not derivable in the combined system:
the least principle with the containing predicate `fun x => x ≠ 2`
confines every derivation to atoms other than `2`, since the root `0`,
the rule head `1` and the one transfer head `3` all satisfy it. -/
example : ¬ Qualification.Derives (fun x : Nat => x = 0)
    (fun ps y => (ps = [0] ∧ y = 1) ∨
      transferRules (fun b a => b = 1 ∧ a = 3) ps y) 2 := by
  intro h
  have roots : ∀ x : Nat, x = 0 → x ≠ 2 := by
    intro x hx
    omega
  have rules : Qualification.Closed
      (fun ps y => (ps = [0] ∧ y = 1) ∨
        transferRules (fun b a => b = 1 ∧ a = 3) ps y)
      (fun x : Nat => x ≠ 2) := by
    intro ps y hr _hp
    show y ≠ 2
    cases hr with
    | inl h1 =>
      have hy : y = 1 := h1.2
      omega
    | inr htr =>
      obtain ⟨b, _hps, _hb, ha⟩ := htr
      omega
  have key := Qualification.least roots rules 2 h
  exact key rfl

#print axioms image_exact
#print axioms transfer_never_exceeds
#print axioms transfer_no_bootstrap
end CheckedTransfer
