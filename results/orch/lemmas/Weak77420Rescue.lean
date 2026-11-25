import Mono18FullProfiles
import RunCofactorCheck

namespace PEqualNP.Outside.L_meta_2373.Live1024.Weak77420Rescue

def a : Sig := bin 1 (inputs.getD 0 zero) (inputs.getD 1 zero)
def b : Sig := bin 1 (inputs.getD 3 zero) (inputs.getD 6 zero)
def c : Sig := bin 0 (inputs.getD 8 zero) b
def d : Sig := bin 1 (inputs.getD 9 zero) c
def e : Sig := bin 1 (inputs.getD 2 zero) d
def f : Sig := bin 0 a e

def roots : List Sig := [inputs.getD 0 zero, inputs.getD 1 zero, inputs.getD 2 zero,
  inputs.getD 3 zero, inputs.getD 4 zero, inputs.getD 5 zero, inputs.getD 6 zero,
  inputs.getD 7 zero, inputs.getD 8 zero, b, d, e, f]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma checked : runCofactorCheck false inputs (Mono18FullProfiles.domain 1089)
    (Mono18FullProfiles.bound 1089) 12 roots [] = true := by
  decide +kernel

lemma excluded {k : Nat} (cap : k ≤ 12) : ¬ Run false (observe graph) k (roots.map observe) :=
  runCofactorCheck_sound (Mono18FullProfiles.slice 1089) checked cap

end PEqualNP.Outside.L_meta_2373.Live1024.Weak77420Rescue
