def C18_literalRoutes : List (List (Nat × Nat)) := [[(0x4000,1),(0x20,2),(0xc,4),(0x2010,2),(0x4454,1)],[(0x10,1),(0x20,2),(0x8,4),(0x20,2),(0x151,1)],[(0x4040,1),(0x20,2),(0xc,4),(0x2010,2),(0x4515,1)]]

def C18_literalOri : List Nat → List Nat := literalRouteOrient C18_literalRoutes

theorem C18_literalGood : literalRoutesGood 0xff00 C18_literalRoutes = true := by decide +kernel

theorem C18_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0xff00 s ws) :
    MonRun 0xff00 s (C18_literalOri ws) :=
  literalRouteOrient_run h C18_literalRoutes C18_literalGood
