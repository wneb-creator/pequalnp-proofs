def C23_literalRoutes : List (List (Nat × Nat)) := [[(0x50,1),(0x10,2),(0xe,4),(0x310,2),(0x1050,1)]]

def C23_literalOri : List Nat → List Nat := literalRouteOrient C23_literalRoutes

theorem C23_literalGood : literalRoutesGood 0x7f80 C23_literalRoutes = true := by decide +kernel

theorem C23_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0x7f80 s ws) :
    MonRun 0x7f80 s (C23_literalOri ws) :=
  literalRouteOrient_run h C23_literalRoutes C23_literalGood
