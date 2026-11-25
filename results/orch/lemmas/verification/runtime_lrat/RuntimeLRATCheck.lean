import Std.Tactic.BVDecide.LRAT.Checker
import Std.Tactic.BVDecide.LRAT.Parser

open Std.Sat Std.Tactic.BVDecide

def parseDimacs (text : String) : Except String (CNF Nat × Nat) := do
  let mut header : Option (Nat × Nat) := none
  let mut clauses : Array (CNF.Clause Nat) := #[]
  let mut pending : List (Literal Nat) := []
  for line in text.splitOn "\n" do
    let words := (line.splitOn " ").map (fun word => word.trimAscii.toString) |>.filter (· != "")
    match words with
    | [] => pure ()
    | "c" :: _ => pure ()
    | ["p", "cnf", ns, ms] =>
      if header.isSome then throw "Duplicate DIMACS header"
      let some n := ns.toNat? | throw "Invalid variable count"
      let some m := ms.toNat? | throw "Invalid clause count"
      header := some (n,m)
    | _ =>
      let some (n, _) := header | throw "Clause before DIMACS header"
      for word in words do
        let some lit := word.toInt? | throw "Invalid DIMACS literal"
        if lit == 0 then
          clauses := clauses.push (.ofLiterals pending.reverse)
          pending := []
        else
          if lit.natAbs > n then throw "DIMACS literal exceeds variable count"
          pending := (lit.natAbs - 1, lit > 0) :: pending
  let some (n,m) := header | throw "Missing DIMACS header"
  if !pending.isEmpty then throw "Unterminated DIMACS clause"
  if clauses.size != m then throw "DIMACS clause count mismatch"
  return (⟨clauses⟩, n)

def main (args : List String) : IO UInt32 := do
  let [cnfPath, proofPath] := args | throw (.userError "Expected CNF path and LRAT path")
  let text ← IO.FS.readFile cnfPath
  let (cnf, n) ← match parseDimacs text with
    | .ok result => pure result
    | .error message => throw (.userError message)
  let proof ← LRAT.loadLRATProof proofPath
  let mut next := cnf.clauses.size + 1
  for action in proof do
    match action with
    | .addEmpty id _ | .addRup id _ _ | .addRat id _ _ _ _ =>
      if id != next then throw (.userError s!"Nonsequential LRAT addition id {id}; expected {next}")
      next := next + 1
    | .del _ => pure ()
  IO.println s!"variables={n} clauses={cnf.clauses.size} actions={proof.size}"
  let accepted := LRAT.check proof cnf
  IO.println s!"Std.Tactic.BVDecide.LRAT.check={accepted}"
  IO.println "Scope: runtime evaluation of Lean's independently implemented, soundness-proved LRAT checker; no kernel proof of this input's UNSAT or circuit-encoding completeness is claimed."
  return if accepted then 0 else 1
