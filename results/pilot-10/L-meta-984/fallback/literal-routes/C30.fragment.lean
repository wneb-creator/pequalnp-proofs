def C30_literalRoutes : List (List (Nat × Nat)) := [[(0x10040,1),(0x21020,2),(0x80000,8),(0x800,16),(0x80000,8),(0x302,4),(0x22021,2),(0x15150,1)]]

def C30_literalOri : List Nat → List Nat := literalRouteOrient C30_literalRoutes

theorem C30_literalGood : literalRoutesGood 0x1ff00 C30_literalRoutes = true := by decide +kernel

theorem C30_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0x1ff00 s ws) :
    MonRun 0x1ff00 s (C30_literalOri ws) :=
  literalRouteOrient_run h C30_literalRoutes C30_literalGood
