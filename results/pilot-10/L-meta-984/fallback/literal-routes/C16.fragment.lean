def C16_literalRoutes : List (List (Nat × Nat)) := []

def C16_literalOri : List Nat → List Nat := literalRouteOrient C16_literalRoutes

theorem C16_literalGood : literalRoutesGood 0x3fc0 C16_literalRoutes = true := by decide +kernel

theorem C16_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0x3fc0 s ws) :
    MonRun 0x3fc0 s (C16_literalOri ws) :=
  literalRouteOrient_run h C16_literalRoutes C16_literalGood
