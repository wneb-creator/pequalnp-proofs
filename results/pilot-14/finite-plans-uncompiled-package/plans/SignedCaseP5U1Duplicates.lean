import SignedCaseP5U1Common
namespace PEqualNP.Outside.L_meta_670_aux.UnorderedFormula.FiniteP5U1
open LiveCheck TightFormula
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma duplicates (i : Fin state.length) :
    UnorderedFormula.test 4 (state[i] :: state) = false := by
  fin_cases i
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

end PEqualNP.Outside.L_meta_670_aux.UnorderedFormula.FiniteP5U1
