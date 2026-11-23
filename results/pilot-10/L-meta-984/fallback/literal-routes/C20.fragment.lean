def C20_literalRoutes : List (List (Nat × Nat)) := []

def C20_literalOri : List Nat → List Nat := literalRouteOrient C20_literalRoutes

theorem C20_literalGood : literalRoutesGood 0x7f80 C20_literalRoutes = true := by decide +kernel

theorem C20_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0x7f80 s ws) :
    MonRun 0x7f80 s (C20_literalOri ws) :=
  literalRouteOrient_run h C20_literalRoutes C20_literalGood
