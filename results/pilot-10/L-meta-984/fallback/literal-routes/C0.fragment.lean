def C0_literalRoutes : List (List (Nat × Nat)) := [[(0x20,2),(0xc,4),(0x10,2),(0x1054,1)],[(0x10,1),(0x20,2),(0x8,4),(0x20,2),(0x151,1)],[(0x40,1),(0x20,2),(0xc,4),(0x10,2),(0x1115,1)],[(0x4000,1),(0xb02,4),(0x11,2),(0x4000,1)],[(0x4054,1),(0x30,2),(0xb06,4),(0x13,2),(0x4100,1)],[(0x4000,1),(0x20,2),(0xb09,4),(0x3,2),(0x5054,1)],[(0x4054,1),(0xb05,4),(0x2,2),(0x5154,1)]]

def C0_literalOri : List Nat → List Nat := literalRouteOrient C0_literalRoutes

theorem C0_literalGood : literalRoutesGood 0x7f00 C0_literalRoutes = true := by decide +kernel

theorem C0_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0x7f00 s ws) :
    MonRun 0x7f00 s (C0_literalOri ws) :=
  literalRouteOrient_run h C0_literalRoutes C0_literalGood
