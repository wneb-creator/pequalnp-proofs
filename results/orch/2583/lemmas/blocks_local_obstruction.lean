import PEqualNP.Defs
import Mathlib

namespace PEqualNP.Outside.L_meta_2583_aux.Blocks

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def matchingCNF : Circuit :=
  { gates :=
      [⟨.or, [0, 1]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [2, 1]⟩,
       ⟨.or, [2, 3]⟩, ⟨.and, [4, 5]⟩, ⟨.and, [6, 7]⟩,
       ⟨.and, [8, 9]⟩]
    output := 10 }

def matchingDNF : Circuit :=
  { gates := [⟨.and, [0, 2]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [4, 5]⟩]
    output := 6 }

lemma matching_cnf_ao2 : PEqualNP.TopForm.IsAO2 4 matchingCNF := by decide

lemma matching_dnf_ao2 : PEqualNP.TopForm.IsAO2 4 matchingDNF := by decide

lemma matching_cnf_function :
    ∀ x : Fin 4 → Bool,
      circuitFun 4 matchingCNF x = ((x 0 && x 2) || (x 1 && x 3)) := by decide

lemma matching_dnf_function :
    ∀ x : Fin 4 → Bool,
      circuitFun 4 matchingDNF x = ((x 0 && x 2) || (x 1 && x 3)) := by decide

lemma matching_cnf_not_read_one : ¬ PEqualNP.ReadK.IsReadK 4 matchingCNF 1 := by decide

lemma matching_cnf_read_two : PEqualNP.ReadK.IsReadK 4 matchingCNF 2 := by decide

lemma matching_dnf_read_one : PEqualNP.ReadK.IsReadK 4 matchingDNF 1 := by decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
lemma matching_cnf_no_single_erasure :
    ∀ g : Fin 7, ∀ w : Fin 11, w.val < 4 + g.val →
      ∃ x : Fin 4 → Bool,
        circuitFun 4 (PEqualNP.CircuitMoves.eraseGate 4 matchingCNF g.val w.val) x ≠
          circuitFun 4 matchingCNF x := by decide

lemma matching_size_comparison : matchingDNF.size + 4 = matchingCNF.size := by decide

lemma matching_no_four_cycle :
    ∀ a b : Fin 2, a ≠ b → ¬ ∃ l : Fin 2, a = l ∧ b = l := by decide

end PEqualNP.Outside.L_meta_2583_aux.Blocks
