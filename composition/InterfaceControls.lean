import composition.InterfaceBridge
import composition.QualifiedClosure
import SoftwareIsQuantifiable.Instance

/- Synthetic interface controls. No readings here are physical measurements. -/
namespace InterfaceControls
open SoftwareIsQuantifiable

inductive Candidate where
  | incumbent | better | tied | drop | tradeoff | otherSymbol | malformed
  deriving DecidableEq, Repr

def space : Interface.MeasureSpace Nat :=
  [⟨0, .minimize⟩, ⟨1, .maximize⟩]

def profile : Candidate → Interface.Profile Nat Nat
  | .incumbent => ⟨0, [10, 10], true⟩
  | .better => ⟨0, [8, 12], true⟩
  | .tied => ⟨0, [8, 12], true⟩
  | .drop => ⟨0, [1, 20], false⟩
  | .tradeoff => ⟨0, [1, 9], true⟩
  | .otherSymbol => ⟨1, [1, 20], true⟩
  | .malformed => ⟨0, [1], true⟩

abbrev d := InterfaceBridge.dominates space profile

theorem mixed_polarity_improves : d .better .incumbent = true := by decide
theorem behavior_drop_refused : d .drop .incumbent = false := by decide
theorem tradeoff_refused : d .tradeoff .incumbent = false := by decide
theorem different_symbol_refused : d .otherSymbol .incumbent = false := by decide
theorem malformed_refused : d .malformed .incumbent = false := by decide
theorem equal_profile_not_strict : d .better .tied = false := by decide

theorem exact_identity_frontier :
    FiniteFrontier.certificate [.incumbent, .better, .tied] [.better, .tied] d = true := by
  decide

theorem discarded_tie_refused :
    FrontierComposition.checkCover d [.incumbent, .better, .tied] [.better] = false := by
  decide

theorem aligned_identity_frontier :
    FiniteFrontier.certificate
      (InterfaceBridge.alignedCatalogue space profile [.incumbent, .better, .tied, .malformed])
      [.better, .tied] d = true := by decide

theorem malformed_frontier_member_refused :
    FiniteFrontier.certificate
      (InterfaceBridge.alignedCatalogue space profile [.incumbent, .better, .tied, .malformed])
      [.better, .tied, .malformed] d = false := by decide

theorem duplicate_symbol_release_refused :
    ¬ Interface.releaseLe space [profile .better, profile .tied] [profile .incumbent] := by
  intro h
  have duplicate := h.1
  simp [Interface.uniqueSymbols, profile] at duplicate

theorem empty_axes_not_strict :
    InterfaceBridge.dominates ([] : Interface.MeasureSpace Nat)
      (fun (_ : Candidate) => (⟨0, [], true⟩ : Interface.Profile Nat Nat))
      .better .incumbent = false := by decide

/-- Exercise the current public instance through the private closure adapter.
    Both AND-premise rules are required; separate closures cannot replace the
    closure of joined roots. -/
def pathRules : QualifiedClosure.Rules Instance.Fact :=
  Instance.pathRules.map (fun r => (r.premises, r.conclusion))

def gateRoots : List Instance.Fact := [.tokenChecked, .signatureValid]
def commitRoots : List Instance.Fact := [.entryHashed]

theorem joined_path_qualified :
    QualifiedClosure.checked Instance.pathUniverse (gateRoots ++ commitRoots) pathRules =
      some Instance.pathUniverse := by decide

theorem missing_joint_premise_refused :
    (QualifiedClosure.checked Instance.pathUniverse gateRoots pathRules).map
      (fun facts => facts.contains .committed) = some false := by decide

theorem separate_colorings_miss_join :
    Coloring.joinSt (Coloring.coloring Instance.pathRules Instance.pathUniverse Instance.gateSeed)
      (Coloring.coloring Instance.pathRules Instance.pathUniverse Instance.commitSeed)
      .committed = false ∧
    Coloring.coloring Instance.pathRules Instance.pathUniverse
      (Coloring.joinSt Instance.gateSeed Instance.commitSeed) .committed = true :=
  Instance.not_coloring_distributes_on_path

theorem omitted_qualified_behavior_refused :
    Pareto.noQualifiedBehaviorLost Instance.priorBehaviors
      Instance.trimmedSubmission = false := by decide

#print axioms exact_identity_frontier
#print axioms discarded_tie_refused
#print axioms aligned_identity_frontier
#print axioms malformed_frontier_member_refused
#print axioms duplicate_symbol_release_refused
#print axioms joined_path_qualified
#print axioms missing_joint_premise_refused
#print axioms separate_colorings_miss_join
#print axioms omitted_qualified_behavior_refused
end InterfaceControls
