import Lean
import Lean.Util.FoldConsts

open Lean Elab Command

syntax (name := collectOwnDependencies) "collect_own_dependencies " ident " within " ident : command

elab_rules : command
  | `(collect_own_dependencies $root:ident within $pref:ident) => do
    let env ← getEnv
    let rootName := root.getId
    let prefixName := pref.getId
    unless (env.find? rootName).isSome do
      throwError "Unknown dependency root {rootName}"
    let mut modules := #[env.getModuleIdxFor? rootName]
    let mut todo := [rootName]
    let mut own : NameSet := {}
    let mut external : NameSet := {}
    while !todo.isEmpty do
      let n := todo.head!
      todo := todo.tail!
      if !own.contains n then
        let mid := env.getModuleIdxFor? n
        if prefixName.isPrefixOf n || modules.contains mid then
          own := own.insert n
          if !modules.contains mid then modules := modules.push mid
          match env.find? n with
          | none => throwError "Missing reachable constant {n}"
          | some info =>
            for dep in info.getUsedConstantsAsSet do
              todo := dep :: todo
        else
          external := external.insert n
    logInfo m!"DEPENDENCY_ROOT\t{rootName}"
    logInfo m!"DEPENDENCY_PREFIX\t{prefixName}"
    logInfo m!"DEPENDENCY_MODULES\t{modules.size}"
    logInfo m!"DEPENDENCY_OWN_COUNT\t{own.foldl (fun k _ => k + 1) (0 : Nat)}"
    for n in own do
      logInfo m!"OWN\t{n}"
    logInfo m!"DEPENDENCY_EXTERNAL_COUNT\t{external.foldl (fun k _ => k + 1) (0 : Nat)}"
