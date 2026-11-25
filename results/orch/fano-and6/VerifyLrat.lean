import Std.Tactic.BVDecide.LRAT.Checker
import Std.Tactic.BVDecide.LRAT.Parser

open Std Sat Tactic.BVDecide

def parseCnf (text : String) : Except String (CNF Nat) := do
  let mut nvars := 0
  let mut expected := 0
  let mut header := false
  let mut clauses : Array (CNF.Clause Nat) := #[]
  for line in text.splitOn "\n" do
    let words := (line.splitOn " ").filter (fun s => !s.isEmpty)
    if words.isEmpty || words.head! == "c" then continue
    if words.head! == "p" then
      if header || words.length != 4 || words[1]! != "cnf" then throw "bad CNF header"
      let some nv := words[2]!.toNat? | throw "bad variable count"
      let some nc := words[3]!.toNat? | throw "bad clause count"
      nvars := nv
      expected := nc
      header := true
    else
      if !header || words.getLast! != "0" then throw "bad CNF clause line"
      let mut literals : List (Literal Nat) := []
      for word in words.dropLast do
        let some val := word.toInt? | throw "bad integer literal"
        if val == 0 || val.natAbs > nvars then throw "out-of-bounds literal"
        literals := (val.natAbs - 1, decide (val > 0)) :: literals
      clauses := clauses.push (CNF.Clause.ofLiterals literals.reverse)
  if !header || clauses.size != expected then throw "CNF clause count mismatch"
  return ⟨clauses⟩

def main (args : List String) : IO UInt32 := do
  let [cnfPath, proofPath] := args | throw (IO.userError "usage: VerifyLrat CNF LRAT")
  let rawCnf ← IO.FS.readFile cnfPath
  let .ok cnf := parseCnf rawCnf | throw (IO.userError "CNF parse failed")
  let rawProof ← IO.FS.readBinFile proofPath
  let .ok proof := LRAT.parseLRATProof rawProof | throw (IO.userError "LRAT parse failed")
  IO.println s!"parsed clauses={cnf.clauses.size} proof_steps={proof.size} proof_bytes={rawProof.size}"
  if LRAT.check proof cnf then
    IO.println "Std LRAT computational checker: VERIFIED UNSAT CNF"
    return 0
  else
    IO.eprintln "Std LRAT computational checker: REJECTED"
    return 1
