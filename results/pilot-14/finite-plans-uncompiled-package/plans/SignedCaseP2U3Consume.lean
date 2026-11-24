import SignedCaseP2U3Common
namespace PEqualNP.Outside.L_meta_670_aux.UnorderedFormula.FiniteP2U3
open LiveCheck TightFormula
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma consume (i : Fin (UnorderedPairs.steps state).length) :
    ((unionSep true (UnorderedPairs.steps state)[i] == top) &&
      UnorderedFormula.testOne 3 (UnorderedPairs.steps state)[i]) = false := by
  fin_cases i <;> decide +kernel

end PEqualNP.Outside.L_meta_670_aux.UnorderedFormula.FiniteP2U3
