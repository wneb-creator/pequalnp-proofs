import Mathlib

namespace PEqualNP.Outside.L_meta_2592_aux

def finiteEdge (r : ℕ) : Bool :=
  (r.testBit 0 && r.testBit 1) ||
  (r.testBit 1 && r.testBit 2) ||
  (r.testBit 2 && r.testBit 3) ||
  (r.testBit 3 && r.testBit 4) ||
  (r.testBit 4 && r.testBit 0) ||
  (r.testBit 0 && r.testBit 5) ||
  (r.testBit 1 && r.testBit 6) ||
  (r.testBit 2 && r.testBit 7) ||
  (r.testBit 3 && r.testBit 8) ||
  (r.testBit 4 && r.testBit 9) ||
  (r.testBit 5 && r.testBit 7) ||
  (r.testBit 7 && r.testBit 9) ||
  (r.testBit 9 && r.testBit 6) ||
  (r.testBit 6 && r.testBit 8) ||
  (r.testBit 8 && r.testBit 5)

def finiteRows : List ℕ :=
  [3, 6, 12, 17, 24, 33, 50, 66, 69, 104, 116, 132, 138, 160, 201,
    208, 264, 276, 288, 320, 385, 402, 521, 528, 548, 554, 576, 640, 770, 773]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma finite_independent_count : ((List.range 1024).filter fun r => !finiteEdge r).length = 76 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma finite_rows_distinct : finiteRows.Nodup := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma finite_rows_bounded : ∀ r ∈ finiteRows, r < 1024 := by
  decide +kernel

end PEqualNP.Outside.L_meta_2592_aux
