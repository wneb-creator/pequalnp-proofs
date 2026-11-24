import SignedCaseP0U0Duplicates
import SignedCaseP0U0Consume
import SignedCaseP0U0Keep
namespace PEqualNP.Outside.L_meta_670_aux.UnorderedFormula.FiniteP0U0
open LiveCheck TightFormula
lemma excluded : UnorderedFormula.testOne 4 state = false :=
  testOne_succ_false 3 state (by decide +kernel) duplicates consume keep

end PEqualNP.Outside.L_meta_670_aux.UnorderedFormula.FiniteP0U0
