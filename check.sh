#!/bin/sh
set -eu
cd "$(dirname "$0")"
LEAN="${LEAN:-lean}"
export LEAN_PATH=".:${LEAN_PATH:-}"
# Reject source admissions/custom axioms, including those Lean would only warn about.
if grep -En '(^|[^[:alnum:]_])(sorry|admit|axiom|native_decide)([^[:alnum:]_]|$)' ./*.lean; then
  echo "Rejected prohibited proof escape hatch" >&2
  exit 1
fi
CHECK_TMP="$(mktemp)"
trap 'rm -f "$CHECK_TMP"' EXIT HUP INT TERM
run_lean() {
  if "$LEAN" -DwarningAsError=true "$@" >"$CHECK_TMP" 2>&1; then
    cat "$CHECK_TMP"
  else
    cat "$CHECK_TMP"
    return 1
  fi
  if grep -Eq 'sorryAx|error:|warning:' "$CHECK_TMP"; then
    echo "Rejected checker diagnostics/admitted axiom" >&2
    return 1
  fi
}
"$LEAN" --version
run_lean -o Qualification.olean Qualification.lean
run_lean -o FiniteQualification.olean FiniteQualification.lean
run_lean -o ExecutableClosure.olean ExecutableClosure.lean
run_lean -o FiniteFrontier.olean FiniteFrontier.lean
run_lean -o FrontierComposition.olean FrontierComposition.lean
run_lean -o FiniteSchedules.olean FiniteSchedules.lean
run_lean -o ForeignCampaign.olean ForeignCampaign.lean
run_lean -o EligibleSchedules.olean EligibleSchedules.lean
run_lean -o ScopedEvidence.olean ScopedEvidence.lean
run_lean -o LinearSelection.olean LinearSelection.lean
run_lean -o EligibleCampaign.olean EligibleCampaign.lean
run_lean -o ScopedSelection.olean ScopedSelection.lean
run_lean -o ScopedCampaign.olean ScopedCampaign.lean
run_lean -o MetricRelevance.olean MetricRelevance.lean
run_lean -o HypergraphIncremental.olean HypergraphIncremental.lean
run_lean -o ContextualDominance.olean ContextualDominance.lean
run_lean -o Admission.olean Admission.lean
run_lean -o AdmissionHypergraph.olean AdmissionHypergraph.lean
run_lean -o AdmissionTests.olean AdmissionTests.lean
run_lean -o ComparisonContract.olean ComparisonContract.lean
run_lean -o ComparisonTests.olean ComparisonTests.lean
run_lean -o ScopedFrontier.olean ScopedFrontier.lean
run_lean -o GeneralPareto.olean GeneralPareto.lean
run_lean -o Composition.olean Composition.lean
run_lean -o OptimalityInterface.olean OptimalityInterface.lean
run_lean -o CompositionCheck.olean CompositionCheck.lean
run_lean -o ExecutableIncremental.olean ExecutableIncremental.lean
run_lean docs/covered-frontier/Controls.lean
run_lean docs/covered-frontier/Campaign.lean
run_lean docs/covered-frontier/ArchiveImport.lean
