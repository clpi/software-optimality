#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
env/bin/python qualification_experiment.py
env/bin/python qualify_receipt.py
