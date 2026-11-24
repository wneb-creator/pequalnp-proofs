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
def qDirectStatePattern (initial : List Nat)
    (countBits patternBits patterns valueBits indexBits slots values record : Nat) : List Nat :=
  let headerBits := if patternBits = 0 then countBits * initial.length else patternBits
  let inputBits := if patternBits = 0 then countBits else 2
  let inputRecord := if patternBits = 0 then record else
    fld patterns (2 * initial.length) (record &&& (2^patternBits-1))
  qDirectInputs inputBits inputRecord initial ++
    qDirectOther values valueBits indexBits slots (record >>> headerBits)

def qGroupOffset (counts : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => qGroupOffset counts n + fld counts 12 n

def qGroupLocate (counts : Nat) : Nat → Nat → Nat → Nat × Nat
  | 0, g, j => (g,j)
  | n+1, g, j =>
    let size := fld counts 12 g
    if j < size then (g,j) else qGroupLocate counts n (g+1) (j-size)

def qGroupNoninputs (initial ws : List Nat) : Nat :=
  ws.countP (fun w => !(initial.contains w))

def qGroupedState (initial : List Nat) (groups valueBits indexBits patterns values counts specs : Nat)
    (records : List (List Nat)) (j : Nat) : List Nat :=
  let slot := qGroupLocate counts groups 0 j
  let g := slot.1
  let localIndex := slot.2
  let spec := fld specs 12 g
  let countBits := spec &&& 3
  let patternBits := (spec >>> 2) &&& 31
  let headerBits := if patternBits = 0 then countBits * initial.length else patternBits
  let width := headerBits + indexBits * g
  let record := fld ((records.getD g []).getD (localIndex/256) 0) width (localIndex%256)
  qDirectStatePattern initial countBits patternBits patterns valueBits indexBits g values record

def qGroupedIndex (initial : List Nat) (counts specs : Nat) (seeds : List Nat) (ws : List Nat) : Nat :=
  let g := qGroupNoninputs initial ws
  let n := fld counts 12 g
  let spec := fld specs 12 g
  let seedBits := (spec >>> 7) &&& 31
  let flag := 2^(seedBits-1)
  let h := hk ws
  let code := fld (seeds.getD g 0) seedBits (h % (max 1 ((n+3)/4)))
  qGroupOffset counts g +
    (if code ≥ flag then code-flag else ((h+code+317)^3 % 11400714819323198549) % n)
