def C21_literalRoutes : List (List (Nat × Nat)) := [[(0x4000,1),(0x20,2),(0xc,4),(0x2010,2),(0x4054,1)]]

def C21_literalOri : List Nat → List Nat := literalRouteOrient C21_literalRoutes

theorem C21_literalGood : literalRoutesGood 0xff00 C21_literalRoutes = true := by decide +kernel

theorem C21_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0xff00 s ws) :
    MonRun 0xff00 s (C21_literalOri ws) :=
  literalRouteOrient_run h C21_literalRoutes C21_literalGood
