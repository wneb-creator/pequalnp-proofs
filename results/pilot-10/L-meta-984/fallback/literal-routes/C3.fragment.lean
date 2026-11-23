def C3_literalRoutes : List (List (Nat × Nat)) := [[(0x4040,1),(0x1010,2),(0x404,4),(0x3232,2),(0x4040,1)]]

def C3_literalOri : List Nat → List Nat := literalRouteOrient C3_literalRoutes

theorem C3_literalGood : literalRoutesGood 0x7f00 C3_literalRoutes = true := by decide +kernel

theorem C3_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0x7f00 s ws) :
    MonRun 0x7f00 s (C3_literalOri ws) :=
  literalRouteOrient_run h C3_literalRoutes C3_literalGood
