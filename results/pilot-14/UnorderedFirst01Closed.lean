import UnorderedFirst01Consume
import UnorderedFirst01Keep
import UnorderedFirst01Duplicates
import UnorderedEndgameTest
namespace PEqualNP.Outside.L_meta_670_aux.UnorderedFormula
open LiveCheck TightFormula

lemma first01_excluded : testOne 4 first01 = false :=
  testOne_succ_false 3 first01 (by decide +kernel)
    first01_duplicates first01_consume first01_keep

lemma first01_representative_eq :
    first01 = (ops (phase (raw.getD 0 zero)) (phase (raw.getD 1 zero))).getD 2 zero :: inputs := by
  decide +kernel

lemma pair01_sign2 :
    testOne 4 ((ops (phase (raw.getD 0 zero)) (phase (raw.getD 1 zero))).getD 2 zero :: inputs) = false := by
  rw [← first01_representative_eq]
  exact first01_excluded

end PEqualNP.Outside.L_meta_670_aux.UnorderedFormula
