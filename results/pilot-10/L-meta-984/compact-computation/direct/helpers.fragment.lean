def qDirectInputs (bits : Nat) : Nat → List Nat → List Nat
  | _, [] => []
  | record, x :: xs => List.replicate (record &&& (2^bits-1)) x ++
      qDirectInputs bits (record >>> bits) xs

def qDirectOther (values valueBits indexBits : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | n+1, record =>
    let index := record &&& (2^indexBits-1)
    let rest := qDirectOther values valueBits indexBits n (record >>> indexBits)
    if index = 0 then rest else fld values valueBits (index-1) :: rest

def qDirectState (initial : List Nat) (countBits valueBits indexBits slots values record : Nat) : List Nat :=
  qDirectInputs countBits record initial ++
    qDirectOther values valueBits indexBits slots (record >>> (countBits * initial.length))
