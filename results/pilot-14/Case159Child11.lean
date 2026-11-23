import Case159Common
namespace PEqualNP.Outside.L_meta_670_aux.FiniteCase159
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma child11_checked : check 11 = true := by decide +kernel
lemma child11_excluded : LiveCheck.Impossible 12 (child 11).nots (child 11).wires :=
  check_sound 11 child11_checked
end PEqualNP.Outside.L_meta_670_aux.FiniteCase159
