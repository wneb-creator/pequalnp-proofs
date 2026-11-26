import Lean
import PEqualNP.Outside.L_meta_2373

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let target : Name := `PEqualNP.Outside.L_meta_2373
  let helper : Name := `PEqualNP.Outside.L_meta_2373_aux
  let mut found := false
  for idx in [:env.header.moduleNames.size] do
    if env.header.moduleNames[idx]! == target then
      found := true
      let data := env.header.moduleData[idx]!
      logInfo m!"AUDIT module={target} index={idx} declarations={data.constants.size}"
      let mut foreignCount : Nat := 0
      for c in data.constants do
        let userName := privateToUserName c.name
        unless target.isPrefixOf userName || helper.isPrefixOf userName do
          foreignCount := foreignCount + 1
          logInfo m!"FOREIGN {c.name} user={userName} kind={if c.isTheorem then "theorem" else "other"}"
      logInfo m!"FOREIGN_COUNT {foreignCount}"
  unless found do throwError "target module was not present"

#check PEqualNP.Outside.L_meta_2373_aux.matching_clause_count
#print axioms PEqualNP.Outside.L_meta_2373_aux.matching_clause_count
