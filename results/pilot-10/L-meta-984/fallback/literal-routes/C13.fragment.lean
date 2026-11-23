def C13_literalRoutes : List (List (Nat × Nat)) := [[(0x440,1),(0x220,2),(0x445,1)],[(0x100,1),(0x200,2),(0x800,4),(0x80,8),(0x800,4),(0x203,2),(0x1100,1)],[(0x440,1),(0x100,2),(0x400,4),(0x40,8),(0x400,4),(0x323,2),(0x1445,1)]]

def C13_literalOri : List Nat → List Nat := literalRouteOrient C13_literalRoutes

theorem C13_literalGood : literalRoutesGood 0x7f80 C13_literalRoutes = true := by decide +kernel

theorem C13_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0x7f80 s ws) :
    MonRun 0x7f80 s (C13_literalOri ws) :=
  literalRouteOrient_run h C13_literalRoutes C13_literalGood
