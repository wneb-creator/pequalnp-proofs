import SignedCaseP5U3Duplicates
import SignedCaseP5U3Consume
import SignedCaseP5U3Keep
namespace PEqualNP.Outside.L_meta_670_aux.UnorderedFormula.FiniteP5U3
open LiveCheck TightFormula
lemma excluded : UnorderedFormula.testOne 4 state = false :=
  testOne_succ_false 3 state (by decide +kernel) duplicates consume keep

end PEqualNP.Outside.L_meta_670_aux.UnorderedFormula.FiniteP5U3
