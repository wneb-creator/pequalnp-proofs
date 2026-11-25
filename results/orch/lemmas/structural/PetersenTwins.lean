namespace PEqualNP.Outside.L_meta_2592_aux.PetersenTwins

def adjacentMask (v : Fin 10) : Nat :=
  [50, 69, 138, 276, 521, 385, 770, 548, 104, 208].getD v.val 0

def bits (mask : Nat) : Nat :=
  ((List.range 10).filter (fun v => mask.testBit v)).length

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem neighborhood_difference : ∀ u v : Fin 10, u ≠ v →
    4 ≤ bits (Nat.xor (adjacentMask u) (adjacentMask v)) := by
  decide

def residual (deleted : Fin 1024) (v : Fin 10) : Nat :=
  Nat.land (adjacentMask v) (Nat.xor 1023 deleted.val)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem no_twins_after_three : ∀ deleted : Fin 1024, bits deleted.val ≤ 3 →
    ∀ u v : Fin 10, u ≠ v → residual deleted u ≠ residual deleted v := by
  decide

end PEqualNP.Outside.L_meta_2592_aux.PetersenTwins
