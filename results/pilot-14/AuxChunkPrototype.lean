import Mathlib
namespace PEqualNP.Outside.L_meta_670_aux.AuxChunkPrototype

def test (i : Nat) : Bool :=
  (List.range (i+1000)).sum == (i+1000)*(i+999)/2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma checks : ∀ i : Fin 8, test i.val = true := by
  intro i
  fin_cases i <;> as_aux_lemma => decide +kernel

#print axioms checks
#print prefix PEqualNP.Outside.L_meta_670_aux.AuxChunkPrototype
end PEqualNP.Outside.L_meta_670_aux.AuxChunkPrototype
