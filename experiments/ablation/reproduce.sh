#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
python3 -m venv env
repos=("pallets/click 08b803cf32ceb2ae6a772c62d5da42757a897d44" "python-attrs/attrs 2a1fb86d44816afcc60e86d57956ce3604820326" "hukkin/tomli 43a86ade8b795c6ef9b4ec53372a607cd1ed426f" "pypa/packaging 6a69a83d8d89c6a01d554a8ad1b420cbb45fb4bc")
for entry in "${repos[@]}"; do
 read -r repo sha <<< "$entry"; name=${repo##*/}
 if [[ ! -d "$name/.git" ]]; then git init "$name"; git -C "$name" remote add origin "https://github.com/$repo.git"; fi
 git -C "$name" fetch --depth 1 origin "$sha"; git -C "$name" checkout --detach "$sha"
done
env/bin/pip install -r dependencies.lock -e ./click -e ./attrs -e ./tomli -e ./packaging
