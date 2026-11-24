import UnorderedFirst01Common
namespace PEqualNP.Outside.L_meta_670_aux.UnorderedFormula
open LiveCheck TightFormula
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma first01_keep (i : Fin (UnorderedPairs.keepSteps first01).length) :
    ((unionSep true (UnorderedPairs.keepSteps first01)[i] == top) &&
      test 3 (UnorderedPairs.keepSteps first01)[i]) = false := by
  fin_cases i <;> decide +kernel
end PEqualNP.Outside.L_meta_670_aux.UnorderedFormula
