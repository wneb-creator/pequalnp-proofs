import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2582.Sanity

open PEqualNP.CircuitLowerBounds

def p4Short : Circuit :=
  ⟨[⟨.and, [1, 3]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [2, 3]⟩,
    ⟨.and, [5, 6]⟩], 7⟩

def p4Repeated : Circuit :=
  ⟨[⟨.and, [1, 3]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [2, 3]⟩,
    ⟨.and, [5, 6]⟩, ⟨.and, [6, 7]⟩], 8⟩

lemma p4Short_ao2 : PEqualNP.TopForm.IsAO2 4 p4Short := by decide

lemma p4Repeated_ao2 : PEqualNP.TopForm.IsAO2 4 p4Repeated := by decide

lemma p4_same_function :
    ∀ x : Fin 4 → Bool,
      PEqualNP.MetaComplexity.circuitFun 4 p4Short x =
        PEqualNP.MetaComplexity.circuitFun 4 p4Repeated x := by decide

lemma p4Short_read2 : PEqualNP.ReadK.IsReadK 4 p4Short 2 := by decide

lemma p4Repeated_prime :
    PEqualNP.ReadK.IsPrimeImplicant 4 p4Repeated ({1, 3} : Finset (Fin 4)) := by
  decide

lemma p4Repeated_bad_pair :
    PEqualNP.ReadK.readsAtMost p4Repeated 4 [1, 3] 2 = false := by decide

lemma p4Repeated_not_read2 : ¬ PEqualNP.ReadK.IsReadK 4 p4Repeated 2 := by
  intro h
  have pair := h ({1, 3} : Finset (Fin 4)) p4Repeated_prime
  have list_eq : PEqualNP.ReadK.setList ({1, 3} : Finset (Fin 4)) = [1, 3] := by
    decide
  rw [list_eq, p4Repeated_bad_pair] at pair
  contradiction

lemma p4_has_smaller_read2 :
    p4Short.size < p4Repeated.size ∧ PEqualNP.ReadK.IsReadK 4 p4Short 2 :=
  ⟨by decide, p4Short_read2⟩

end PEqualNP.Outside.L_meta_2582.Sanity
