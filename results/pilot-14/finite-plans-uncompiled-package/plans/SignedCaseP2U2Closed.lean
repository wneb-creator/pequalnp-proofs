import SignedCaseP2U2Duplicates
import SignedCaseP2U2Consume
import SignedCaseP2U2Keep
namespace PEqualNP.Outside.L_meta_670_aux.UnorderedFormula.FiniteP2U2
open LiveCheck TightFormula
lemma excluded : UnorderedFormula.testOne 4 state = false :=
  testOne_succ_false 3 state (by decide +kernel) duplicates consume keep

end PEqualNP.Outside.L_meta_670_aux.UnorderedFormula.FiniteP2U2
