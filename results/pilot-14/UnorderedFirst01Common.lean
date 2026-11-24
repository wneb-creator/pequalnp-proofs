import UnorderedEmbeddingTest
namespace PEqualNP.Outside.L_meta_670_aux.UnorderedFormula
open LiveCheck TightFormula

def first01 : List Sig := phase (bin false raw0 raw1) :: raw.map phase
lemma first01_length : first01.length = 10 := by decide +kernel
lemma first01_consume_length : (UnorderedPairs.steps first01).length = 180 := by decide +kernel
lemma first01_keep_length : (UnorderedPairs.keepSteps first01).length = 360 := by decide +kernel

end PEqualNP.Outside.L_meta_670_aux.UnorderedFormula
