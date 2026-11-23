def C15_literalRoutes : List (List (Nat × Nat)) := [[(0x4,1),(0x32,2),(0x404,1)]]

def C15_literalOri : List Nat → List Nat := literalRouteOrient C15_literalRoutes

theorem C15_literalGood : literalRoutesGood 0xff00 C15_literalRoutes = true := by decide +kernel

theorem C15_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0xff00 s ws) :
    MonRun 0xff00 s (C15_literalOri ws) :=
  literalRouteOrient_run h C15_literalRoutes C15_literalGood
