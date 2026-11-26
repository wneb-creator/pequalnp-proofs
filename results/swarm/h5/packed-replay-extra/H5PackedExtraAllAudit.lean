import H5PackedExtraAll
import Lean

open Lean Elab Command
open PEqualNP.Outside.L_meta_2373_aux.Cert18.Replay.DirectMode.Packed.H5

example : block 3840 512 := rangeExtra
example : ∀ i : Fin 5230, 3840 ≤ i.val → i.val < 4352 →
    PEqualNP.Outside.L_meta_2373_aux.Cert18.Replay.DirectMode.Packed.checkNode i = true :=
  checkedExtraRange

#check @PEqualNP.Outside.L_meta_2373_aux.Cert18.Replay.DirectMode.Packed.H5.rangeExtra
#check @PEqualNP.Outside.L_meta_2373_aux.Cert18.Replay.DirectMode.Packed.H5.checkedExtraRange
#print axioms PEqualNP.Outside.L_meta_2373_aux.Cert18.Replay.DirectMode.Packed.H5.rangeExtra
#print axioms PEqualNP.Outside.L_meta_2373_aux.Cert18.Replay.DirectMode.Packed.H5.checkedExtraRange

run_cmd do
  let env := (← getEnv).setExporting false
  let modules : Array Name := #[`H5BlockSupport, `H5PackedRange3840, `H5PackedRange3904, `H5PackedRange3968, `H5PackedRange4032, `H5PackedRange4096, `H5PackedRange4160, `H5PackedRange4224, `H5PackedRange4288, `H5PackedExtraAll]
  let allowed := `PEqualNP.Outside.L_meta_2373_aux.Cert18.Replay.DirectMode.Packed.H5
  let roots := #[`PEqualNP.Outside.L_meta_2373_aux.Cert18.Replay.DirectMode.Packed.H5.rangeExtra, `PEqualNP.Outside.L_meta_2373_aux.Cert18.Replay.DirectMode.Packed.H5.checkedExtraRange]
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
    ("start", toJson (3840 : Nat)), ("endExclusive", toJson (4352 : Nat)),
    ("expectedTypeElaborated", toJson true), ("declarations", Json.arr declarations),
    ("modules", Json.arr reports), ("foreignKernelExports", toJson foreign),
    ("ownerMismatches", toJson wrongOwners), ("disallowedAxioms", toJson (badAxioms.map Name.toString))]
  liftIO <| IO.FS.writeFile "/tmp/oec/pnp-swarm-2373-5/h5-packed-range-extra/aggregate-audit.json" result.pretty
  unless foreign.isEmpty && wrongOwners.isEmpty && badAxioms.isEmpty do
    throwError "Aggregate audit failed; see aggregate-audit.json"
  logInfo "Range aggregate type, axioms, and module exports passed"
