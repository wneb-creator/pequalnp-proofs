import UnorderedFirst01Common
namespace PEqualNP.Outside.L_meta_670_aux.UnorderedFormula
open LiveCheck TightFormula

def first01Dup0 : List Sig := first01[0] :: first01
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma first01_duplicate0_children (i : Fin (UnorderedPairs.steps first01Dup0).length) :
    ((unionSep true (UnorderedPairs.steps first01Dup0)[i] == top) &&
      test 3 (UnorderedPairs.steps first01Dup0)[i]) = false := by
  fin_cases i <;> decide +kernel

lemma first01_duplicate0 : test 4 first01Dup0 = false :=
  test_succ_false 3 first01Dup0 (by decide +kernel) first01_duplicate0_children

end PEqualNP.Outside.L_meta_670_aux.UnorderedFormula
