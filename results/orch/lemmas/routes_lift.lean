namespace PEqualNP.Outside.L_meta_14985_aux.GraphTarget8
open PEqualNP.Outside.L_meta_14985_aux.LiveCircuits

def full8 : Sig := 0xfffffffffffffffafffffffffffefffafffffffefffffffaeeeeeeeeeeee0000fffffffffffffffafffffffffffefffafffffffefffffffaeeeeeeeeeeee0000

def cols8 : List Sig := inputs.take 8

def liftMoves : List Move := [
  ((inputs.getD 1 zero) &&& ~~~(inputs.getD 2 zero),
    ~~~(inputs.getD 1 zero) &&& (inputs.getD 2 zero), 2),
  ((inputs.getD 3 zero) &&& ~~~(inputs.getD 7 zero),
    ~~~(inputs.getD 3 zero) &&& (inputs.getD 7 zero), 120),
  ((inputs.getD 4 zero) &&& ~~~(inputs.getD 5 zero),
    ~~~(inputs.getD 4 zero) &&& (inputs.getD 5 zero), 16),
  ((inputs.getD 5 zero) &&& ~~~(inputs.getD 6 zero),
    ~~~(inputs.getD 5 zero) &&& (inputs.getD 6 zero), 32),
  ((inputs.getD 6 zero) &&& ~~~(inputs.getD 7 zero),
    ~~~(inputs.getD 6 zero) &&& (inputs.getD 7 zero), 64),
  (zero, inputs.getD 3 zero, 8)]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
lemma minimum : Lower true cols8 full8 10 := by
  have old : Lower true GraphTarget.cols7 GraphTarget.full 9 :=
    Certificate.complete TriangleBound.standardLower3
      CliqueBounds.standardLower4 CliqueBounds.standardLower5
  have h := lift_ok
    (ms := liftMoves) (T := full8) (raw := cols8)
    (base := GraphTarget.cols7) (G := GraphTarget.full)
    (xs := [(inputs.getD 3 zero, 64, 72)])
    (by decide +kernel)
    (by unfold proper; decide +kernel)
    (by unfold proper; decide +kernel) old
  simpa using h

end PEqualNP.Outside.L_meta_14985_aux.GraphTarget8
