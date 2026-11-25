#!/usr/bin/env bash
set -euo pipefail

script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
logs_dir="${1:-${script_dir}/rebuild-two-filter-logs}"
source "${script_dir}/rebuild-auxiliary14.sh" "$logs_dir"

extra_modules=(
  SoleReaderFreeCore
  SafeNotRaise
  DirectFilterCore
  PairLocalization
  SharedFilter
  DirectFilterRows
  TwoFilterAuxBridge
  CanonicalTwoFilter
  TwoFilterSymmetry
  AllTwoFilters
  AllTwoFiltersOrders
)

for module in "${extra_modules[@]}"; do
  run_logged "$module" "$lake_bin" env lean --root="$module_root" \
    -o "${module_root}/${module}.olean" "${module_root}/${module}.lean"
done

run_logged two-filter-axioms "$lake_bin" env lean --stdin <<'LEAN'
import AllTwoFiltersOrders
#print axioms PEqualNP.Outside.L_meta_1884.AllTwoFiltersOrders.impossible
LEAN

printf 'PASS all ordered neighbor filters; complete logs: %s\n' "$logs_dir"
