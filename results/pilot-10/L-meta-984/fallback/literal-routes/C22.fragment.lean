def C22_literalRoutes : List (List (Nat × Nat)) := [[(0x1010,1),(0x2020,2),(0x200,4),(0x20,8),(0xa08,4),(0x2120,2),(0x1011,1)]]

def C22_literalOri : List Nat → List Nat := literalRouteOrient C22_literalRoutes

theorem C22_literalGood : literalRoutesGood 0x3fc0 C22_literalRoutes = true := by decide +kernel

theorem C22_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0x3fc0 s ws) :
    MonRun 0x3fc0 s (C22_literalOri ws) :=
  literalRouteOrient_run h C22_literalRoutes C22_literalGood
