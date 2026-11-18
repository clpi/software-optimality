#!/bin/sh
set -eu
cd "$(dirname "$0")"
LEAN="${LEAN:-lean}"
export LEAN_PATH=".:${LEAN_PATH:-}"
"$LEAN" --version
"$LEAN" -o Qualification.olean Qualification.lean
"$LEAN" FiniteQualification.lean
"$LEAN" ExecutableClosure.lean
"$LEAN" -o FiniteFrontier.olean FiniteFrontier.lean
"$LEAN" -o FiniteSchedules.olean FiniteSchedules.lean
"$LEAN" ForeignCampaign.lean
"$LEAN" -o EligibleSchedules.olean EligibleSchedules.lean
"$LEAN" EligibleCampaign.lean
