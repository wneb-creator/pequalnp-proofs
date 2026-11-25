import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2582.MatchingLocal

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def matchingCNF : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [3, 4]⟩,
    ⟨.or, [2, 6]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [5, 7]⟩,
    ⟨.or, [2, 8]⟩, ⟨.or, [5, 8]⟩, ⟨.or, [2, 9]⟩, ⟨.or, [5, 9]⟩,
    ⟨.and, [10, 11]⟩, ⟨.and, [12, 18]⟩, ⟨.and, [13, 19]⟩,
    ⟨.and, [14, 20]⟩, ⟨.and, [15, 21]⟩, ⟨.and, [16, 22]⟩,
    ⟨.and, [17, 23]⟩], 24⟩

def matchingDNF : Circuit :=
  ⟨[⟨.and, [0, 3]⟩, ⟨.and, [1, 4]⟩, ⟨.and, [2, 5]⟩,
    ⟨.or, [6, 7]⟩, ⟨.or, [9, 8]⟩], 10⟩

def matchingBypass (k : Fin 19) (side : Bool) : Circuit :=
  let b := (gateAt matchingCNF k).inputs.getD (if side then 1 else 0) 0
  ⟨matchingCNF.gates.set k ⟨.and, [b, b]⟩, matchingCNF.output⟩

def matchingWire (w : Fin 25) : Circuit := ⟨matchingCNF.gates, w.val⟩

lemma matchingCNF_ao : PEqualNP.TopForm.IsAO2 6 matchingCNF := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma matchingCNF_computes : ∀ x : Fin 6 → Bool,
    circuitFun 6 matchingCNF x =
      ((x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma matchingCNF_same_function : ∀ x : Fin 6 → Bool,
    circuitFun 6 matchingCNF x = circuitFun 6 matchingDNF x := by decide

lemma matchingCNF_prime :
    PEqualNP.ReadK.IsPrimeImplicant 6 matchingCNF ({0, 3} : Finset (Fin 6)) := by decide

lemma matchingCNF_bad_pair :
    PEqualNP.ReadK.readsAtMost matchingCNF 6 [0, 3] 2 = false := by decide

lemma matchingCNF_not_read2 : ¬ PEqualNP.ReadK.IsReadK 6 matchingCNF 2 := by
  intro h
  have pair := h ({0, 3} : Finset (Fin 6)) matchingCNF_prime
  have hlist : PEqualNP.ReadK.setList ({0, 3} : Finset (Fin 6)) = [0, 3] := by decide
  rw [hlist, matchingCNF_bad_pair] at pair
  contradiction

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma matchingCNF_no_operand_bypass : ∀ (k : Fin 19) (side : Bool),
    ∃ x : Fin 6 → Bool, circuitFun 6 (matchingBypass k side) x ≠ circuitFun 6 matchingCNF x := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma matchingCNF_distinct_wires : ∀ i j : Fin 25, i ≠ j →
    ∃ x : Fin 6 → Bool, circuitFun 6 (matchingWire i) x ≠ circuitFun 6 (matchingWire j) x := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma matchingCNF_smaller_read1 :
    PEqualNP.TopForm.IsAO2 6 matchingDNF ∧ matchingDNF.size = 5 ∧ matchingCNF.size = 19 ∧
      PEqualNP.ReadK.IsReadK 6 matchingDNF 1 := by decide

def matchingEarlierBypass (k : Fin 19) (b : Fin 25) : Circuit :=
  ⟨matchingCNF.gates.set k ⟨.and, [b.val, b.val]⟩, matchingCNF.output⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma matchingCNF_no_earlier_bypass : ∀ (k : Fin 19) (b : Fin 25), b.val < 6 + k.val →
    ∃ x : Fin 6 → Bool,
      circuitFun 6 (matchingEarlierBypass k b) x ≠ circuitFun 6 matchingCNF x := by
  decide

end PEqualNP.Outside.L_meta_2582.MatchingLocal
