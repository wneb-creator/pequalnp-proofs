import SignedCaseP2U0Duplicates
import SignedCaseP2U0Consume
import SignedCaseP2U0Keep
namespace PEqualNP.Outside.L_meta_670_aux.UnorderedFormula.FiniteP2U0
open LiveCheck TightFormula
lemma excluded : UnorderedFormula.testOne 4 state = false :=
  testOne_succ_false 3 state (by decide +kernel) duplicates consume keep

end PEqualNP.Outside.L_meta_670_aux.UnorderedFormula.FiniteP2U0
