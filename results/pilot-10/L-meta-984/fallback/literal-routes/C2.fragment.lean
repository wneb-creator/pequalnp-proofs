def C2_literalRoutes : List (List (Nat × Nat)) := [[(0x1000,1),(0x2030,2),(0x80c,4),(0x2030,2),(0x5000,1)],[(0x100,1),(0x200,2),(0x800,4),(0x80,8),(0x800,4),(0x300,2),(0x115,1)],[(0x1100,1),(0x2030,2),(0x200,4),(0x20,8),(0xa0c,4),(0x2130,2),(0x5115,1)]]

def C2_literalOri : List Nat → List Nat := literalRouteOrient C2_literalRoutes

theorem C2_literalGood : literalRoutesGood 0xfe00 C2_literalRoutes = true := by decide +kernel

theorem C2_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0xfe00 s ws) :
    MonRun 0xfe00 s (C2_literalOri ws) :=
  literalRouteOrient_run h C2_literalRoutes C2_literalGood
