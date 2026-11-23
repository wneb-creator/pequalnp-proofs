def C5_literalRoutes : List (List (Nat × Nat)) := [[(0x4,1),(0x10,2),(0x4,4),(0x12,2),(0x144,1)]]

def C5_literalOri : List Nat → List Nat := literalRouteOrient C5_literalRoutes

theorem C5_literalGood : literalRoutesGood 0x7f00 C5_literalRoutes = true := by decide +kernel

theorem C5_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0x7f00 s ws) :
    MonRun 0x7f00 s (C5_literalOri ws) :=
  literalRouteOrient_run h C5_literalRoutes C5_literalGood
