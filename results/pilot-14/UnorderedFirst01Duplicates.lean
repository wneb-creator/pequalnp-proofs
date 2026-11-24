import UnorderedFirst01Dup0
namespace PEqualNP.Outside.L_meta_670_aux.UnorderedFormula
open LiveCheck TightFormula
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma first01_duplicates (i : Fin first01.length) :
    test 4 (first01[i] :: first01) = false := by
  fin_cases i
  · exact first01_duplicate0
  all_goals decide +kernel
end PEqualNP.Outside.L_meta_670_aux.UnorderedFormula
