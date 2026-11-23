def C10_literalRoutes : List (List (Nat × Nat)) := [[(0x110,1),(0x20,2),(0x200,4),(0x20,8),(0x208,4),(0x20,2),(0x111,1)]]

def C10_literalOri : List Nat → List Nat := literalRouteOrient C10_literalRoutes

theorem C10_literalGood : literalRoutesGood 0x1fe0 C10_literalRoutes = true := by decide +kernel

theorem C10_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0x1fe0 s ws) :
    MonRun 0x1fe0 s (C10_literalOri ws) :=
  literalRouteOrient_run h C10_literalRoutes C10_literalGood
