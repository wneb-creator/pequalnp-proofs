def C28_literalRoutes : List (List (Nat × Nat)) := [[(0x5550,1),(0x1010,2),(0x100,4),(0x10,8),(0x50e,4),(0x3210,2),(0x5550,1)]]

def C28_literalOri : List Nat → List Nat := literalRouteOrient C28_literalRoutes

theorem C28_literalGood : literalRoutesGood 0xff80 C28_literalRoutes = true := by decide +kernel

theorem C28_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0xff80 s ws) :
    MonRun 0xff80 s (C28_literalOri ws) :=
  literalRouteOrient_run h C28_literalRoutes C28_literalGood
