import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2582.Local

open PEqualNP.CircuitLowerBounds

def p4Local : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [0, 5]⟩,
    ⟨.and, [4, 7]⟩, ⟨.and, [5, 6]⟩, ⟨.and, [8, 9]⟩], 10⟩

def p4Small : Circuit :=
  ⟨[⟨.and, [1, 3]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [2, 3]⟩,
    ⟨.and, [5, 6]⟩], 7⟩

def p4LocalWire (w : Fin 11) : Circuit := ⟨p4Local.gates, w.val⟩

lemma p4Local_ao2 : PEqualNP.TopForm.IsAO2 4 p4Local := by decide

lemma p4Local_same_function :
    ∀ x : Fin 4 → Bool,
      PEqualNP.MetaComplexity.circuitFun 4 p4Local x =
        PEqualNP.MetaComplexity.circuitFun 4 p4Small x := by decide

lemma p4Local_prime :
    PEqualNP.ReadK.IsPrimeImplicant 4 p4Local ({1, 3} : Finset (Fin 4)) := by
  decide

lemma p4Local_bad_pair :
    PEqualNP.ReadK.readsAtMost p4Local 4 [1, 3] 2 = false := by decide

lemma p4Local_not_read2 : ¬ PEqualNP.ReadK.IsReadK 4 p4Local 2 := by
  intro h
  have pair := h ({1, 3} : Finset (Fin 4)) p4Local_prime
  have list_eq : PEqualNP.ReadK.setList ({1, 3} : Finset (Fin 4)) = [1, 3] := by
    decide
  rw [list_eq, p4Local_bad_pair] at pair
  contradiction

lemma p4Local_all_wire_functions_distinct :
    ∀ i j : Fin 11, i ≠ j → ∃ x : Fin 4 → Bool,
      PEqualNP.MetaComplexity.circuitFun 4 (p4LocalWire i) x ≠
        PEqualNP.MetaComplexity.circuitFun 4 (p4LocalWire j) x := by decide

lemma p4Local_has_smaller_read2 :
    PEqualNP.TopForm.IsAO2 4 p4Small ∧ p4Small.size < p4Local.size ∧
      PEqualNP.ReadK.IsReadK 4 p4Small 2 := by decide

end PEqualNP.Outside.L_meta_2582.Local
