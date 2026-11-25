#!/usr/bin/env bash
set -euo pipefail
repo=/workspace/pequalnp-proofs
out=${1:?Supply an existing or new scratch output directory under /tmp/oec/pnp-swarm-2590-orch}
case "$out" in
  /tmp/oec/pnp-swarm-2590-orch/*) ;;
  *) echo 'Output must be in the authorized scratch directory.' >&2; exit 2 ;;
esac
cd "$repo/lean"
source /tmp/oec/pnp-swarm-2590-orch/lean-env.sh
python3 "$repo/results/swarm/prepare_remaining_one.py" --repo "$repo" --out "$out"
lake exe cache get > "$out/cache-get.log" 2>&1
for module in FoundationI0I3I4Audit I2Standalone N0CompleteAudit; do
  lake env lean -j1 -R "$out" -o "$out/$module.olean" "$out/$module.lean" > "$out/$module.log" 2>&1
done
lake env bash -c 'export LEAN_PATH="$1${LEAN_PATH:+:${LEAN_PATH}}"; shift; exec lean "$@"' _ "$out" -j1 -R "$out" -o "$out/RemainingOne.olean" "$out/RemainingOne.lean" > "$out/RemainingOne.log" 2>&1
