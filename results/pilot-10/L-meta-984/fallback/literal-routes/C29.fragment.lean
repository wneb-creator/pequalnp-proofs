def C29_literalRoutes : List (List (Nat × Nat)) := [[(0x1040,1),(0x2100,2),(0x400,4),(0x40,8),(0xc00,4),(0x2120,2),(0x5041,1)],[(0x4004,1),(0x2302,2),(0x4014,1)],[(0x5040,1),(0x2100,2),(0x400,4),(0x40,8),(0xc00,4),(0x3221,2),(0x1051,1)],[(0x1404,1),(0x800,4),(0x80,8),(0xa00,4),(0x1312,2),(0x5115,1)],[(0x5400,1),(0x800,4),(0x80,8),(0xa00,4),(0x1011,2),(0x5400,1)]]

def C29_literalOri : List Nat → List Nat := literalRouteOrient C29_literalRoutes

theorem C29_literalGood : literalRoutesGood 0xff80 C29_literalRoutes = true := by decide +kernel

theorem C29_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0xff80 s ws) :
    MonRun 0xff80 s (C29_literalOri ws) :=
  literalRouteOrient_run h C29_literalRoutes C29_literalGood
