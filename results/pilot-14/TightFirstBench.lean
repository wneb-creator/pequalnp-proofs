import TightFormulaTest
namespace PEqualNP.Outside.L_meta_670_aux.TightFormula
open LiveCheck
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma first_example : test 3 (phase (bin false raw0 raw1) :: raw.map phase) = false := by
  decide +kernel
end PEqualNP.Outside.L_meta_670_aux.TightFormula
