import DynamicFastBase
namespace PEqualNP.Outside.L_meta_670_aux.PureCase159
open LiveCheck

def state : List Sig :=
  [raw0,raw1,raw2,raw3,raw4,raw5,raw6,raw7,raw8,
    bin false raw2 raw0,bin false raw3 raw1]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma checked : search 13 2 state = false := by decide +kernel

lemma impossible : Impossible 13 2 state :=
  exclude_search (by decide +kernel) checked

end PEqualNP.Outside.L_meta_670_aux.PureCase159
#print axioms PEqualNP.Outside.L_meta_670_aux.PureCase159.impossible
