import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2373.RectanglePackedBenchmark20

def packed : Nat := 0x45228920924a20944a44924945024929128a25224904904924929244a28940925025140a242249288251251409051089289a6a28904940d27104a44926930a25128928944a20928944a28944904d34945124a4289
def weight (r c : Nat) : Int := Int.ofNat ((packed >>> (3 * (r * 15 + c))) &&& 7) - 2

def rowScore (w : Nat → Nat → Int) (rows cols : List Nat) : Int :=
  cols.foldl (fun total c => total + max (rows.foldl (fun acc r => acc + w r c) 0) 0) 0

def rowCheck (w : Nat → Nat → Int) : List Nat → List Nat → List Nat → Int → Bool
  | [], selected, cols, cap => decide (rowScore w selected cols ≤ cap)
  | r :: rest, selected, cols, cap =>
      rowCheck w rest selected cols cap && rowCheck w rest (r :: selected) cols cap

def mask (n : Nat) : List Nat := (List.range 15).filter (fun i => n.testBit i)
def check (p n : Nat) (cap : Int) : Bool :=
  let rows := mask p
  let cols := mask n
  if rows.length ≤ cols.length then rowCheck weight rows [] cols cap
  else rowCheck (fun c r => weight r c) cols [] rows cap

def entries : List (Nat × Nat × Int) := [
(191,12885,16),
(375,6361,12),
(439,6365,11),
(439,12885,12),
(445,10953,12),
(445,14493,12),
(607,19750,16),
(695,12885,12),
(701,12445,12),
(829,10953,12),
(859,19750,12),
(926,13620,12),
(1278,11672,13),
(1341,10953,10),
(1454,11208,13),
(2231,12885,12),
(2237,10397,10),
(2365,10953,9),
(2383,18890,11),
(2485,10461,8)]
def checkEntry (r : Nat × Nat × Int) : Bool := check r.1 r.2.1 r.2.2
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma checked_profiles : entries.all checkEntry = true := by decide +kernel

end PEqualNP.Outside.L_meta_2373.RectanglePackedBenchmark20
