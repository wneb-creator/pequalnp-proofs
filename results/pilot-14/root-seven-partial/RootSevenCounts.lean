import RootSevenLeafTest
namespace PEqualNP.Outside.L_meta_670_aux.RootSevenLeaf
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma counts : ∀ i : Fin 12, (proposals i.val).length = 9 := by
  intro i
  fin_cases i <;> decide +kernel
end PEqualNP.Outside.L_meta_670_aux.RootSevenLeaf
