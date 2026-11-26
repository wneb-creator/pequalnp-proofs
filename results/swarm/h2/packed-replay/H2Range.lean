import H2IntervalBridge
import H2Nodes1536_1539
import H2Nodes1540_1667
import H2Nodes1668_1795
import H2Nodes1796_1923
import H2Tail1924_2051
import H2Tail2052_2179
import H2Tail2180_2303

namespace H2PackedReplay
open PEqualNP.Outside.L_meta_2373_aux.Cert18.Replay.DirectMode.Packed
lemma checked (i : Fin 5230) (hlo : 1536 ≤ i.val) (hhi : i.val < 2304) :
    checkNode i = true := by
  by_cases h0 : i.val < 1540
  · exact check_interval 1536 4 nodes1536_1539 i hlo (by omega)
  by_cases h1 : i.val < 1668
  · exact check_interval 1540 128 nodes1540_1667 i (by omega) (by omega)
  by_cases h2 : i.val < 1796
  · exact check_interval 1668 128 nodes1668_1795 i (by omega) (by omega)
  by_cases h3 : i.val < 1924
  · exact check_interval 1796 128 nodes1796_1923 i (by omega) (by omega)
  by_cases h4 : i.val < 2052
  · exact check_interval 1924 128 tail1924_2051 i (by omega) (by omega)
  by_cases h5 : i.val < 2180
  · exact check_interval 2052 128 tail2052_2179 i (by omega) (by omega)
  exact check_interval 2180 124 tail2180_2303 i (by omega) hhi
end H2PackedReplay
#print axioms H2PackedReplay.checked
