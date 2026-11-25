import ExistingMonoNine
import Lean.Util.FoldConsts

open Lean Elab Command

run_cmd do
  let env := (← getEnv).setExporting false
  let prefix := "PEqualNP.Outside.L_meta_2590_aux.MonoNine"
  let roots := ["monoRoot", "input_list", "witnessB", "witnessB_sound", "raw_required", "reach_live", "projected_bound", "observe_proper", "Run.perm", "Run.two", "Run.stop", "kept", "map_kept", "kept_nd", "Reach.start", "mass_cons", "cost", "Constant", "supply", "restrictRows"]
  let mut todo := roots.map (fun n => (prefix ++ "." ++ n).toName)
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let c := todo.head!
    todo := todo.tail
    unless seen.contains c do
      seen := seen.insert c
      match env.find? c with
      | none => logInfo m!"MISSING {c}"
      | some ci =>
        for d in ci.getUsedConstantsAsSet.toList do
          if d.toString.startsWith prefix && !seen.contains d then
            todo := d :: todo
  for c in seen.toList do
    logInfo m!"DEP {c}"
