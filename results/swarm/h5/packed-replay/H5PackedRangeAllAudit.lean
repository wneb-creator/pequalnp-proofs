import H5PackedRangeAll
import Lean

open Lean Elab Command
open PEqualNP.Outside.L_meta_2373_aux.Cert18.Replay.DirectMode.Packed.H5

example : block 3072 768 := rangeAll
example : ∀ i : Fin 5230, 3072 ≤ i.val → i.val < 3840 →
    PEqualNP.Outside.L_meta_2373_aux.Cert18.Replay.DirectMode.Packed.checkNode i = true :=
  checkedRange

#check @PEqualNP.Outside.L_meta_2373_aux.Cert18.Replay.DirectMode.Packed.H5.rangeAll
#check @PEqualNP.Outside.L_meta_2373_aux.Cert18.Replay.DirectMode.Packed.H5.checkedRange
#print axioms PEqualNP.Outside.L_meta_2373_aux.Cert18.Replay.DirectMode.Packed.H5.rangeAll
#print axioms PEqualNP.Outside.L_meta_2373_aux.Cert18.Replay.DirectMode.Packed.H5.checkedRange

run_cmd do
  let env := (← getEnv).setExporting false
  let modules : Array Name := #[`H5BlockSupport, `H5PackedRange3072, `H5PackedRange3136, `H5PackedRange3200, `H5PackedRange3264, `H5PackedRange3328, `H5PackedRange3392, `H5PackedRange3456, `H5PackedRange3520, `H5PackedRange3584, `H5PackedRange3648, `H5PackedRange3712, `H5PackedRange3776, `H5PackedRangeAll]
  let allowed := `PEqualNP.Outside.L_meta_2373_aux.Cert18.Replay.DirectMode.Packed.H5
  let roots := #[`PEqualNP.Outside.L_meta_2373_aux.Cert18.Replay.DirectMode.Packed.H5.rangeAll, `PEqualNP.Outside.L_meta_2373_aux.Cert18.Replay.DirectMode.Packed.H5.checkedRange]
  let mut declarations : Array Json := #[]
  let mut badAxioms : Array Name := #[]
  for name in roots do
    let some ci := env.find? name | throwError "Missing aggregate declaration"
    let axioms ← collectAxioms name
    for ax in axioms do
      if !(#[``propext, ``Classical.choice, ``Quot.sound]).contains ax then
        badAxioms := badAxioms.push ax
    logInfo m!"Aggregate type {name}: {ci.type}"
    declarations := declarations.push <| Json.mkObj [
      ("name", toJson name.toString), ("axioms", toJson (axioms.map Name.toString))]
  let mut reports : Array Json := #[]
  let mut foreign : Array String := #[]
  let mut wrongOwners : Array String := #[]
  for mod in modules do
    let some idx := env.getModuleIdx? mod | throwError "Missing range module"
    let data := env.header.moduleData[idx.toNat]!
    let mut names : Array String := #[]
    for ci in data.constants do
      let n := ci.name
      names := names.push n.toString
      if !allowed.isPrefixOf ((privateToUserName? n).getD n) then
        foreign := foreign.push n.toString
      if env.getModuleIdxFor? n != some idx then
        wrongOwners := wrongOwners.push n.toString
    reports := reports.push <| Json.mkObj [
      ("module", toJson mod.toString), ("kernelConstantCount", toJson data.constants.size),
      ("kernelConstants", toJson names), ("codegenExtraCount", toJson data.extraConstNames.size)]
  let result := Json.mkObj [
    ("checkerCommit", toJson "36375ce3bb56c227c81ecae98f6641800006b8c2"),
    ("start", toJson (3072 : Nat)), ("endExclusive", toJson (3840 : Nat)),
    ("expectedTypeElaborated", toJson true), ("declarations", Json.arr declarations),
    ("modules", Json.arr reports), ("foreignKernelExports", toJson foreign),
    ("ownerMismatches", toJson wrongOwners), ("disallowedAxioms", toJson (badAxioms.map Name.toString))]
  liftIO <| IO.FS.writeFile "/tmp/oec/pnp-swarm-2373-5/h5-packed-range/aggregate-audit.json" result.pretty
  unless foreign.isEmpty && wrongOwners.isEmpty && badAxioms.isEmpty do
    throwError "Aggregate audit failed; see aggregate-audit.json"
  logInfo "Range aggregate type, axioms, and module exports passed"
