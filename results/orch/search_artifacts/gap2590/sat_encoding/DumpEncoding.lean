import PEqualNP.Defs

open PEqualNP.Defs.LratEncoding

def rows : List Nat := [3, 6, 12, 17, 24, 33, 50, 66, 69, 104, 116, 132, 138, 160, 201, 208, 264, 276, 288, 320, 385, 402, 521, 528, 548, 554, 576, 640, 770, 773]

def rowValue (r : Nat) : Bool := (r.testBit 0 && r.testBit 1) || (r.testBit 1 && r.testBit 2) || (r.testBit 2 && r.testBit 3) || (r.testBit 3 && r.testBit 4) || (r.testBit 4 && r.testBit 0) || (r.testBit 0 && r.testBit 5) || (r.testBit 1 && r.testBit 6) || (r.testBit 2 && r.testBit 7) || (r.testBit 3 && r.testBit 8) || (r.testBit 4 && r.testBit 9) || (r.testBit 5 && r.testBit 7) || (r.testBit 7 && r.testBit 9) || (r.testBit 9 && r.testBit 6) || (r.testBit 6 && r.testBit 8) || (r.testBit 8 && r.testBit 5)

def signedLiteral (l : Nat) : Int :=
  if l % 2 = 0 then Int.ofNat (l / 2) else -(Int.ofNat (l / 2))

def main : IO Unit := do
  let f := enc2 10 19 rowValue rows
  let maxVar := f.foldl (fun m cl => cl.foldl (fun m l => max m (l / 2)) m) 0
  IO.println ("p cnf " ++ toString maxVar ++ " " ++ toString f.length)
  for cl in f do
    IO.println (String.intercalate " " (cl.map (fun l => toString (signedLiteral l))) ++ " 0")
