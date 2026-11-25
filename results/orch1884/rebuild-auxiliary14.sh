#!/usr/bin/env bash
set -euo pipefail

script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo_root=$(cd -- "${script_dir}/../.." && pwd)
module_root="${script_dir}/lemmas"
logs_dir="${1:-${script_dir}/rebuild-logs}"
lake_bin="${PEQUALNP_REAL_LAKE:-lake}"
mkdir -p -- "$logs_dir"
logs_dir=$(cd -- "$logs_dir" && pwd)
cd -- "${repo_root}/lean"
export LEAN_PATH="${module_root}${LEAN_PATH:+:${LEAN_PATH}}"

run_logged() {
  local label="$1"
  shift
  if "$@" > "${logs_dir}/${label}.stdout" 2> "${logs_dir}/${label}.stderr"; then
    printf 'PASS %s\n' "$label"
  else
    local result_code=$?
    printf 'FAIL %s exit=%s; complete logs: %s\n' "$label" "$result_code" "$logs_dir" >&2
    return "$result_code"
  fi
}

run_logged lake-version "$lake_bin" --version
run_logged cache "$lake_bin" exe cache get
run_logged project-helpers "$lake_bin" build \
  PEqualNP.Defs \
  PEqualNP.MetaComplexity.Helpers.Elim \
  PEqualNP.MetaComplexity.Helpers.LiftFixMain \
  PEqualNP.MetaComplexity.Helpers.LiveSize \
  PEqualNP.MetaComplexity.Helpers.LocClean \
  PEqualNP.MetaComplexity.Helpers.LowMergeWires \
  PEqualNP.MetaComplexity.Helpers.NormalFormLift \
  PEqualNP.MetaComplexity.Helpers.PermInputs

modules=(
  LeastLiftNormalization
  ClosedOrSet
  ClosedOrSafety
  StrongRelaxRows
  LeastGateFacts
  GeneralReaderStandalone
  SoleReaderFactor
  RelaxedFacts
  StrongRelaxOrSafety
  RelaxationSemantics
  ClosedRelaxOr
  ClosedRelaxOrGeneral
  EightExtension
  ElimManyCount
  Forced13Compile
  RestrictionEight
  UniqueReader
  PairReaderCharge
  SoleAndRestriction
  RelaxationFloor
)

for module in "${modules[@]}"; do
  run_logged "$module" "$lake_bin" env lean --root="$module_root" \
    -o "${module_root}/${module}.olean" "${module_root}/${module}.lean"
done

run_logged axioms "$lake_bin" env lean --stdin <<'LEAN'
import RelaxationFloor
#print axioms PEqualNP.Outside.L_meta_1884.RelaxationFloor.fourteen
LEAN

printf 'PASS auxiliary14; complete logs: %s\n' "$logs_dir"
