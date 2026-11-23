def C14_literalRoutes : List (List (Nat × Nat)) := [[(0x4,1),(0x100,2),(0x400,4),(0x40,8),(0x500,4),(0x322,2),(0x4,1)]]

def C14_literalOri : List Nat → List Nat := literalRouteOrient C14_literalRoutes

theorem C14_literalGood : literalRoutesGood 0x1fe0 C14_literalRoutes = true := by decide +kernel

theorem C14_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0x1fe0 s ws) :
    MonRun 0x1fe0 s (C14_literalOri ws) :=
  literalRouteOrient_run h C14_literalRoutes C14_literalGood
