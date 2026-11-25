import MonoEncodingDefs

open PEqualNP.Defs.LratEncoding
open PEqualNP.Outside.L_meta_1884.NormalizedEncoding

def signedLiteral (l : Nat) : Int :=
  if l % 2 = 0 then Int.ofNat (l / 2) else -(Int.ofNat (l / 2))

def main : IO Unit := do
  let f := enc2 11 18 rowValue freeRows
  let maxVar := f.foldl (fun m cl => cl.foldl (fun m l => max m (l / 2)) m) 0
  IO.println ("p cnf " ++ toString maxVar ++ " " ++ toString f.length)
  for cl in f do
    IO.println (String.intercalate " " (cl.map (fun l => toString (signedLiteral l))) ++ " 0")
