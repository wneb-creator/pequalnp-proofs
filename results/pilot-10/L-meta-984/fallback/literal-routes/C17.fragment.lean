def C17_literalRoutes : List (List (Nat × Nat)) := [[(0x4000,1),(0x20,2),(0xc,4),(0x2010,2),(0x4054,1)],[(0x10,1),(0x20,2),(0x8,4),(0x20,2),(0x151,1)],[(0x4040,1),(0x20,2),(0xc,4),(0x2010,2),(0x4115,1)]]

def C17_literalOri : List Nat → List Nat := literalRouteOrient C17_literalRoutes

theorem C17_literalGood : literalRoutesGood 0xff00 C17_literalRoutes = true := by decide +kernel

theorem C17_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0xff00 s ws) :
    MonRun 0xff00 s (C17_literalOri ws) :=
  literalRouteOrient_run h C17_literalRoutes C17_literalGood
