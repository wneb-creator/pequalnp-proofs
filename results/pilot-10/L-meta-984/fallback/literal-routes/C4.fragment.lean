def C4_literalRoutes : List (List (Nat × Nat)) := [[(0x4,1),(0x10,2),(0x4,4),(0x12,2),(0x144,1)]]

def C4_literalOri : List Nat → List Nat := literalRouteOrient C4_literalRoutes

theorem C4_literalGood : literalRoutesGood 0x7f00 C4_literalRoutes = true := by decide +kernel

theorem C4_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0x7f00 s ws) :
    MonRun 0x7f00 s (C4_literalOri ws) :=
  literalRouteOrient_run h C4_literalRoutes C4_literalGood
