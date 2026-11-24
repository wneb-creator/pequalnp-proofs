import SignedCaseP5U1Common
namespace PEqualNP.Outside.L_meta_670_aux.UnorderedFormula.FiniteP5U1
open LiveCheck TightFormula
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma keep (i : Fin (UnorderedPairs.keepSteps state).length) :
    ((unionSep true (UnorderedPairs.keepSteps state)[i] == top) &&
      UnorderedFormula.test 3 (UnorderedPairs.keepSteps state)[i]) = false := by
  fin_cases i <;> decide +kernel

end PEqualNP.Outside.L_meta_670_aux.UnorderedFormula.FiniteP5U1
