import composition.InterfaceBridge

/- Exact structural compression for Idol's finite literal-binding schema.

   The expanded representation repeats the SAME immutable semantic rule basis
   in every binding, integer, definition and module. The compact representation
   omits only that fixed basis. Both contain every nominal origin, exact i64
   payload, observed member name, dependency, list position and repetition.

   This module proves a bijection of these typed records. It does not prove
   Zig parsing, framing, source admission, canonical member sorting, historical
   origin authenticity, or the implementation's conformance to this model.
   Additional admission predicates may restrict these structural records; the
   round trip preserves every predicate of the complete expanded record.

   The final certificate compares exactly TWO supplied byte profiles. The axes
   are the executed -17 integer fixture and one-member module fixture, in bytes.
   Their values were observed by the native semantic_identity.zig tests; the
   verification receipt binds the source and execution. Lean checks the supplied
   arithmetic and the existing public frontier certificate. It does not obtain
   physical observations from these numerals or claim a bound for other records,
   latency, memory residency, or the space of all possible encodings.
-/
namespace IdentityRepresentation
open SoftwareIsQuantifiable

abbrev Bytes := List UInt8
abbrev I64 := { value : Int // -(2 ^ 63 : Int) ≤ value ∧ value < (2 ^ 63 : Int) }

/-- Only this immutable rule basis is admitted by the supported schema. This
    is a semantic rule identity, not a compiler, document or codec revision. -/
inductive FixedLaw where
  | literalBindingV1
  deriving DecidableEq, Repr

structure Origin where
  domain : Bytes
  token : Bytes
  deriving DecidableEq, Repr

structure Binding where
  origin : Origin
  deriving DecidableEq, Repr

structure Integer where
  payload : I64
  deriving DecidableEq, Repr

structure Definition where
  binding : Binding
  value : Integer
  deriving DecidableEq, Repr

structure Member where
  name : Bytes
  definition : Definition
  deriving DecidableEq, Repr

structure Module where
  origin : Origin
  members : List Member
  deriving DecidableEq, Repr

namespace Expanded
structure Binding where
  law : FixedLaw
  origin : Origin
  deriving DecidableEq, Repr

structure Integer where
  law : FixedLaw
  payload : I64
  deriving DecidableEq, Repr

structure Definition where
  law : FixedLaw
  binding : Binding
  value : Integer
  deriving DecidableEq, Repr

structure Member where
  name : Bytes
  definition : Definition
  deriving DecidableEq, Repr

structure Module where
  law : FixedLaw
  origin : Origin
  members : List Member
  deriving DecidableEq, Repr
end Expanded

def Binding.expand (x : Binding) : Expanded.Binding :=
  ⟨.literalBindingV1, x.origin⟩
def Expanded.Binding.erase (x : Expanded.Binding) : IdentityRepresentation.Binding := ⟨x.origin⟩
def Integer.expand (x : Integer) : Expanded.Integer :=
  ⟨.literalBindingV1, x.payload⟩
def Expanded.Integer.erase (x : Expanded.Integer) : IdentityRepresentation.Integer := ⟨x.payload⟩
def Definition.expand (x : Definition) : Expanded.Definition :=
  ⟨.literalBindingV1, x.binding.expand, x.value.expand⟩
def Expanded.Definition.erase (x : Expanded.Definition) : IdentityRepresentation.Definition :=
  ⟨x.binding.erase, x.value.erase⟩
def Member.expand (x : Member) : Expanded.Member :=
  ⟨x.name, x.definition.expand⟩
def Expanded.Member.erase (x : Expanded.Member) : IdentityRepresentation.Member :=
  ⟨x.name, x.definition.erase⟩
def Module.expand (x : Module) : Expanded.Module :=
  ⟨.literalBindingV1, x.origin, x.members.map Member.expand⟩
def Expanded.Module.erase (x : Expanded.Module) : IdentityRepresentation.Module :=
  ⟨x.origin, x.members.map Expanded.Member.erase⟩

@[simp] theorem erase_expand_binding (x : Binding) : x.expand.erase = x := by
  cases x; rfl
@[simp] theorem expand_erase_binding (x : Expanded.Binding) : x.erase.expand = x := by
  rcases x with ⟨basis, root⟩
  cases basis; rfl
@[simp] theorem erase_expand_integer (x : Integer) : x.expand.erase = x := by
  cases x; rfl
@[simp] theorem expand_erase_integer (x : Expanded.Integer) : x.erase.expand = x := by
  rcases x with ⟨basis, payload⟩
  cases basis; rfl
@[simp] theorem erase_expand_definition (x : Definition) : x.expand.erase = x := by
  cases x
  simp [Definition.expand, Expanded.Definition.erase]
@[simp] theorem expand_erase_definition (x : Expanded.Definition) : x.erase.expand = x := by
  rcases x with ⟨basis, binder, value⟩
  cases basis
  simp [Definition.expand, Expanded.Definition.erase]
@[simp] theorem erase_expand_member (x : Member) : x.expand.erase = x := by
  cases x
  simp [Member.expand, Expanded.Member.erase]
@[simp] theorem expand_erase_member (x : Expanded.Member) : x.erase.expand = x := by
  cases x
  simp [Member.expand, Expanded.Member.erase]
@[simp] theorem erase_expand_module (x : Module) : x.expand.erase = x := by
  cases x
  simp [Module.expand, Expanded.Module.erase, List.map_map, Function.comp_def]
@[simp] theorem expand_erase_module (x : Expanded.Module) : x.erase.expand = x := by
  rcases x with ⟨basis, root, members⟩
  cases basis
  simp [Module.expand, Expanded.Module.erase, List.map_map, Function.comp_def]

/-- Constructor roles are part of the complete record; an origin, binding and
    definition do not become interchangeable when their payloads coincide. -/
inductive Record where
  | law
  | origin (value : Origin)
  | binding (value : Binding)
  | integer (value : Integer)
  | definition (value : Definition)
  | member (value : Member)
  | module (value : Module)
  deriving DecidableEq, Repr

inductive Expanded.Record where
  | law (basis : FixedLaw)
  | origin (value : Origin)
  | binding (value : Expanded.Binding)
  | integer (value : Expanded.Integer)
  | definition (value : Expanded.Definition)
  | member (value : Expanded.Member)
  | module (value : Expanded.Module)
  deriving DecidableEq, Repr

def Record.expand : Record → Expanded.Record
  | .law => .law .literalBindingV1
  | .origin x => .origin x
  | .binding x => .binding x.expand
  | .integer x => .integer x.expand
  | .definition x => .definition x.expand
  | .member x => .member x.expand
  | .module x => .module x.expand

def Expanded.Record.erase : Expanded.Record → IdentityRepresentation.Record
  | .law _ => .law
  | .origin x => .origin x
  | .binding x => .binding x.erase
  | .integer x => .integer x.erase
  | .definition x => .definition x.erase
  | .member x => .member x.erase
  | .module x => .module x.erase

@[simp] theorem erase_expand (x : Record) : x.expand.erase = x := by
  cases x <;> simp [Record.expand, Expanded.Record.erase]

@[simp] theorem expand_erase (x : Expanded.Record) : x.erase.expand = x := by
  cases x with
  | law basis => cases basis; rfl
  | origin x => rfl
  | binding x => simp [Record.expand, Expanded.Record.erase]
  | integer x => simp [Record.expand, Expanded.Record.erase]
  | definition x => simp [Record.expand, Expanded.Record.erase]
  | member x => simp [Record.expand, Expanded.Record.erase]
  | module x => simp [Record.expand, Expanded.Record.erase]

/-- Exact equality, in both directions, rather than equality of a digest or
    an observed result. The proof covers every typed record, not one fixture. -/
theorem erase_eq_iff (a b : Expanded.Record) : a.erase = b.erase ↔ a = b := by
  constructor
  · intro h
    have restored := congrArg Record.expand h
    simpa using restored
  · exact congrArg Expanded.Record.erase

theorem expand_eq_iff (a b : Record) : a.expand = b.expand ↔ a = b := by
  constructor
  · intro h
    have erased := congrArg Expanded.Record.erase h
    simpa using erased
  · exact congrArg Record.expand

/-- Every observation or admission predicate on the complete typed record is
    preserved by reconstruction. This supplies no external origin authority. -/
theorem all_record_observations_preserved {A : Sort _}
    (observe : Expanded.Record → A) (x : Expanded.Record) :
    observe x.erase.expand = observe x := by rw [expand_erase]

theorem nominal_binding_exact (a b : Origin) : Binding.mk a = Binding.mk b ↔ a = b := by
  simp

theorem binding_survives_definition_edit (root : Origin) (a b : Integer) :
    (Definition.mk ⟨root⟩ a).binding = (Definition.mk ⟨root⟩ b).binding := rfl

theorem closed_definition_exact (a b : Binding) (x y : Integer) :
    Definition.mk a x = Definition.mk b y ↔ a = b ∧ x = y := by simp

theorem member_dependencies_exact (a b : Bytes) (x y : Definition) :
    Member.mk a x = Member.mk b y ↔ a = b ∧ x = y := by simp

theorem module_dependencies_exact (a b : Origin) (x y : List Member) :
    Module.mk a x = Module.mk b y ↔ a = b ∧ x = y := by simp

theorem binding_and_definition_roles_distinct (binder : Binding) (value : Integer) :
    Record.binding binder ≠ Record.definition ⟨binder, value⟩ := by simp

/-- Negative control: deleting the nominal input would merge distinct complete
    definitions with equal literal contents. That deletion is not our erasure. -/
theorem deleting_nominal_input_loses_information
    (a b : Origin) (different : a ≠ b) (value : Integer) :
    (Definition.mk ⟨a⟩ value ≠ Definition.mk ⟨b⟩ value) ∧
      (Definition.mk ⟨a⟩ value).value = (Definition.mk ⟨b⟩ value).value := by
  constructor
  · intro merged
    exact different (congrArg (fun d : Definition => d.binding.origin) merged)
  · rfl

/-- Negative control outside the admitted basis: if rules could differ, dropping
    that input would lose information. The singleton FixedLaw is essential. -/
theorem arbitrary_rule_erasure_is_not_injective (value : I64) :
    ((0, value) : Nat × I64) ≠ (1, value) ∧
      ((0, value) : Nat × I64).2 = (1, value).2 := by simp

inductive Candidate where
  | expanded | compact
  deriving DecidableEq, Repr

/-- These axes name the two exact observed fixtures, not general codec costs. -/
inductive FixtureAxis where
  | integerMinus17Bytes
  | moduleDomainHomeLeftABytes
  deriving DecidableEq, Repr

def fixtureSpace : Interface.MeasureSpace FixtureAxis :=
  [⟨.integerMinus17Bytes, .minimize⟩, ⟨.moduleDomainHomeLeftABytes, .minimize⟩]

def fixtureInteger : Integer := ⟨⟨-17, by decide⟩⟩
def fixtureBinding : Binding :=
  ⟨⟨"domain".toUTF8.data.toList, "a".toUTF8.data.toList⟩⟩
def fixtureModule : Module :=
  ⟨⟨"domain".toUTF8.data.toList, "home".toUTF8.data.toList⟩,
    [⟨"left".toUTF8.data.toList, ⟨fixtureBinding, fixtureInteger⟩⟩]⟩

/-- The public profile symbol carries the complete typed records for the two
    measured projections. Changing a nominal root, member key or payload changes
    this symbol; the readings cannot silently speak about a different fixture. -/
def fixtureRecords : List Record := [.integer fixtureInteger, .module fixtureModule]

/-- Supplied executed byte counts. The receipt, not this definition, binds them
    to the native artifact. Typed preservation is proved independently above. -/
def fixtureProfile : Candidate → Interface.Profile (List Record) FixtureAxis
  | .expanded => ⟨fixtureRecords, [81, 436], true⟩
  | .compact => ⟨fixtureRecords, [30, 231], true⟩

def catalogue : List Candidate := [.expanded, .compact]
def retained : List Candidate := [.compact]
def fixtureDominates := InterfaceBridge.dominates fixtureSpace fixtureProfile

def reconstruct : Candidate → Expanded.Record → Expanded.Record
  | .expanded, x => x
  | .compact, x => x.erase.expand

theorem reconstruction_preserves_all_records (candidate : Candidate) (x : Expanded.Record) :
    reconstruct candidate x = x := by
  cases candidate with
  | expanded => rfl
  | compact => exact expand_erase x

def fixtureCertificate : Bool :=
  FiniteFrontier.certificate
    (InterfaceBridge.alignedCatalogue fixtureSpace fixtureProfile catalogue)
    retained fixtureDominates

theorem fixture_strict_improvement : fixtureDominates .compact .expanded = true := by decide
theorem fixture_certificate_accepted : fixtureCertificate = true := by decide

/-- Use the existing identity certificate and pinned public profile interface;
    no second Pareto checker is introduced by this representation example. -/
theorem public_fixture_frontier :
    ∀ candidate, candidate ∈ retained ↔ candidate ∈ catalogue ∧
      fixtureProfile candidate ∈ Interface.frontier fixtureSpace (catalogue.map fixtureProfile) :=
  (InterfaceBridge.aligned_certificate_exact fixtureSpace fixtureProfile catalogue retained).mp
    fixture_certificate_accepted

/-- The useful linked result: exact reconstruction for every typed record and
    the checked two-candidate frontier for exactly the two supplied byte axes. -/
theorem scoped_representation_certificate :
    (∀ candidate ∈ catalogue, ∀ x, reconstruct candidate x = x) ∧
    fixtureCertificate = true ∧
    (∀ candidate, candidate ∈ retained ↔ candidate ∈ catalogue ∧
      fixtureProfile candidate ∈ Interface.frontier fixtureSpace (catalogue.map fixtureProfile)) :=
  ⟨fun candidate _ x => reconstruction_preserves_all_records candidate x,
    fixture_certificate_accepted, public_fixture_frontier⟩

theorem dominated_expanded_frontier_refused :
    FiniteFrontier.certificate
      (InterfaceBridge.alignedCatalogue fixtureSpace fixtureProfile catalogue)
      [.expanded] fixtureDominates = false := by decide

theorem better_candidate_omission_refused :
    FrontierComposition.checkCover fixtureDominates catalogue [.expanded] = false := by decide

#print axioms erase_eq_iff
#print axioms all_record_observations_preserved
#print axioms deleting_nominal_input_loses_information
#print axioms scoped_representation_certificate
#print axioms dominated_expanded_frontier_refused
end IdentityRepresentation
