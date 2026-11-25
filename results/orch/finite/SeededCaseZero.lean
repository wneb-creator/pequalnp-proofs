import Mathlib.Data.Nat.Bitwise

namespace PEqualNP.Outside.L_meta_2592_aux.SeededMatch

abbrev Sig := ℕ

def inv (a : Sig) : Sig := a ^^^ 8191

def target : Sig := 30

def seeds : List Sig :=
  [0, 8191, 2726, 5446, 1642, 6538, 498, 7698,
    6142, 7166, 7934, 8158, 7630, 2042, 7802, 6650]

def generated (bank : List Sig) : List Sig :=
  bank ++ bank.map (fun a => inv a) ++
    bank.flatMap (fun a => bank.flatMap (fun b => [a &&& b, a ||| b]))

def choices (bank : List Sig) : List Sig := (generated bank).eraseDups

def noOne (bank : List Sig) : Bool := !(generated bank).contains target

def afterFirst (a : Sig) : Bool :=
  (choices (a :: seeds)).all fun b => noOne (b :: a :: seeds)

def noThree : Bool := (choices seeds).all afterFirst

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_0 : afterFirst 0 = true := by
  decide +kernel

end PEqualNP.Outside.L_meta_2592_aux.SeededMatch
