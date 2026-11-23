def C25_literalRoutes : List (List (Nat × Nat)) := [[(0x1010,1),(0x2020,2),(0x808,4),(0x3020,2),(0x1110,1)],[(0x5400,1),(0x220,2),(0x200,4),(0x20,8),(0xb0d,4),(0x231,2),(0x5414,1)],[(0x410,1),(0x800,4),(0x80,8),(0xf05,4),(0x1111,2),(0x410,1)]]

def C25_literalOri : List Nat → List Nat := literalRouteOrient C25_literalRoutes

theorem C25_literalGood : literalRoutesGood 0x7f80 C25_literalRoutes = true := by decide +kernel

theorem C25_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0x7f80 s ws) :
    MonRun 0x7f80 s (C25_literalOri ws) :=
  literalRouteOrient_run h C25_literalRoutes C25_literalGood
