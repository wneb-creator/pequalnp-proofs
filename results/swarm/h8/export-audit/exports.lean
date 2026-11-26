import PEqualNP.Outside.L_meta_2373
import Lean

open Lean

run_meta do
  let env ← getEnv
  let some idx := env.getModuleIdx? `PEqualNP.Outside.L_meta_2373
    | throwError "Target module missing"
  let data := env.header.moduleData[idx]!
  let names := data.constNames.toList
  let extra := data.extraConstNames.toList
  let foreign := names.filter fun n =>
    (n.toString.splitOn "PEqualNP.Outside.L_meta_2373_aux").length == 1
  let foreignExtra := extra.filter fun n =>
    (n.toString.splitOn "PEqualNP.Outside.L_meta_2373_aux").length == 1
  let render (xs : List Name) := String.intercalate "\n" (xs.map Name.toString) ++ "\n"
  IO.FS.writeFile "/tmp/oec/pnp-swarm-2373-8/combined-review/exports/fixed/named.constants.txt" (render names)
  IO.FS.writeFile "/tmp/oec/pnp-swarm-2373-8/combined-review/exports/fixed/named.extra.txt" (render extra)
  IO.FS.writeFile "/tmp/oec/pnp-swarm-2373-8/combined-review/exports/fixed/named.foreign.txt" (render foreign)
  IO.FS.writeFile "/tmp/oec/pnp-swarm-2373-8/combined-review/exports/fixed/named.foreign-extra.txt" (render foreignExtra)
  logInfo m!"module=PEqualNP.Outside.L_meta_2373 index={idx} constants={names.length} extra={extra.length} foreign={foreign.length} foreignExtra={foreignExtra.length} namesAgree={data.constNames == data.constants.map ConstantInfo.name} isModule={data.isModule}"
  for n in foreign do
    let kind := match env.find? n with
      | some (.thmInfo _) => "theorem"
      | some (.defnInfo _) => "definition"
      | some (.axiomInfo _) => "axiom"
      | some _ => "other"
      | none => "missing"
    let owner := (env.getModuleIdxFor? n).map fun j => env.header.moduleNames[j]!
    logInfo m!"foreign: {n} kind={kind} finalOwner={owner}"
