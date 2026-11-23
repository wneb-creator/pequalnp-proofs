def C12_literalRoutes : List (List (Nat × Nat)) := [[(0x400,1)],[(0x110,1),(0x20,2),(0x200,4),(0x20,8),(0x208,4),(0x20,2),(0x111,1)],[(0x110,1),(0x20,2),(0x200,4),(0x20,8),(0x208,4),(0x20,2),(0x511,1)]]

def C12_literalOri : List Nat → List Nat := literalRouteOrient C12_literalRoutes

theorem C12_literalGood : literalRoutesGood 0x1fe0 C12_literalRoutes = true := by decide +kernel

theorem C12_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0x1fe0 s ws) :
    MonRun 0x1fe0 s (C12_literalOri ws) :=
  literalRouteOrient_run h C12_literalRoutes C12_literalGood
