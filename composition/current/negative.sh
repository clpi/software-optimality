#!/bin/sh
# Run in the joint runner's Lake environment; keep generated claims isolated.
set -eu
LEAN=${LEAN:-lean}
control_dir=$(mktemp -d)
trap 'rm -rf "$control_dir"' EXIT
trap 'exit 1' HUP INT TERM
reject() {
  name=$1
  cat > "$control_dir/NegativeInterface.lean"
  if "$LEAN" -DwarningAsError=true "$control_dir/NegativeInterface.lean" > "$control_dir/negative-$name.log" 2>&1; then
    echo "False interface claim unexpectedly accepted: $name" >&2
    exit 1
  fi
  if ! grep -q "tactic 'decide' proved that the proposition" "$control_dir/negative-$name.log" ||
      ! grep -q '^is false$' "$control_dir/negative-$name.log"; then
    cat "$control_dir/negative-$name.log" >&2
    echo "Unexpected rejection reason: $name" >&2
    exit 1
  fi
  echo "Expected rejection: $name"
  cat "$control_dir/negative-$name.log"
}

reject discarded-tie <<'LEAN'
import composition.InterfaceControls
open InterfaceControls
example : FrontierComposition.checkCover d [.incumbent, .better, .tied] [.better] = true := by
  decide
LEAN

reject behavior-drop <<'LEAN'
import composition.InterfaceControls
open InterfaceControls
example : d .drop .incumbent = true := by decide
LEAN

reject maximize-regression <<'LEAN'
import composition.InterfaceControls
open InterfaceControls
example : d .tradeoff .incumbent = true := by decide
LEAN

reject malformed-profile <<'LEAN'
import composition.InterfaceControls
open InterfaceControls
example : d .malformed .incumbent = true := by decide
LEAN

reject missing-joint-premise <<'LEAN'
import composition.InterfaceControls
open SoftwareIsQuantifiable InterfaceControls
example : (QualifiedClosure.checked Instance.pathUniverse gateRoots pathRules).map
    (fun facts => facts.contains .committed) = some true := by decide
LEAN

reject malformed-frontier-member <<'LEAN'
import composition.InterfaceControls
open InterfaceControls
example : FiniteFrontier.certificate
    (InterfaceBridge.alignedCatalogue space profile [.incumbent, .better, .tied, .malformed])
    [.better, .tied, .malformed] d = true := by decide
LEAN
