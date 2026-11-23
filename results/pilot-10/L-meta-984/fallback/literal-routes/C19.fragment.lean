def C19_literalRoutes : List (List (Nat × Nat)) := [[(0x4044,1),(0x2322,2),(0x4044,1)]]

def C19_literalOri : List Nat → List Nat := literalRouteOrient C19_literalRoutes

theorem C19_literalGood : literalRoutesGood 0x7f80 C19_literalRoutes = true := by decide +kernel

theorem C19_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0x7f80 s ws) :
    MonRun 0x7f80 s (C19_literalOri ws) :=
  literalRouteOrient_run h C19_literalRoutes C19_literalGood
