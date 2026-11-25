import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583

def cycle5Circuit : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [2, 5]⟩,
    ⟨.and, [4, 7]⟩, ⟨.and, [6, 8]⟩, ⟨.or, [9, 10]⟩], 11⟩

lemma cycle5Circuit_size : cycle5Circuit.size = 7 := rfl

lemma cycle5Circuit_ao : PEqualNP.TopForm.IsAO2 5 cycle5Circuit := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma cycle5Circuit_eval : ∀ z : Fin 5 → Bool,
    PEqualNP.MetaComplexity.circuitFun 5 cycle5Circuit z =
      (z 0 && z 1 || z 1 && z 2 || z 2 && z 3 || z 3 && z 4 || z 4 && z 0) := by
  decide

lemma cycle5Circuit_prime_pair :
    PEqualNP.ReadK.IsPrimeImplicant 5 cycle5Circuit ({0, 1} : Finset (Fin 5)) := by
  decide

lemma cycle5Circuit_reads_pair_false :
    PEqualNP.ReadK.readsAtMost cycle5Circuit 5
      (PEqualNP.ReadK.setList ({0, 1} : Finset (Fin 5))) 1 = false := by
  decide

lemma cycle5Circuit_not_read1 : ¬ PEqualNP.ReadK.IsReadK 5 cycle5Circuit 1 := by
  intro h
  have ht := h ({0, 1} : Finset (Fin 5)) cycle5Circuit_prime_pair
  have hf := cycle5Circuit_reads_pair_false
  exact Bool.noConfusion (hf.symm.trans ht)

end PEqualNP.Outside.L_meta_2583
