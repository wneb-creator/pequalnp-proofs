def C7_literalRoutes : List (List (Nat × Nat)) := [[(0x1004,1),(0x2000,2),(0x800,4),(0x2032,2),(0x1104,1)]]

def C7_literalOri : List Nat → List Nat := literalRouteOrient C7_literalRoutes

theorem C7_literalGood : literalRoutesGood 0x7f00 C7_literalRoutes = true := by decide +kernel

theorem C7_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0x7f00 s ws) :
    MonRun 0x7f00 s (C7_literalOri ws) :=
  literalRouteOrient_run h C7_literalRoutes C7_literalGood
