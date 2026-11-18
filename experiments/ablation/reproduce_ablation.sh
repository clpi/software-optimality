#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
# First run reproduce.sh in a fresh directory to fetch/install the pinned sources.
# Run here only after verifying those pins and Python dependency lock.
# Receipts are overwritten: use a fresh unpacked directory to retain originals.
env/bin/python ablation.py
env/bin/python verify_ablation.py
