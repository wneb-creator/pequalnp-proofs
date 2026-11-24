import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1425.Cert

open PEqualNP.CircuitLowerBounds

-- Explicit upper bounds only; no minimality or NOT-elimination claim.
def upperMono (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

def upperComputes (C : Circuit) (T : Nat) : Prop :=
  ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) =
    Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : Nat) else 0)

def upperCircuit0 : Circuit := ⟨[⟨.and, [1,4]⟩, ⟨.and, [2,5]⟩, ⟨.and, [3,6]⟩, ⟨.or, [1,2]⟩, ⟨.and, [0,8]⟩, ⟨.or, [7,9]⟩], 10⟩
theorem upperCircuit0_mono : upperMono upperCircuit0 := by
  simp [upperMono, upperCircuit0]
theorem upperCircuit0_computes : upperComputes upperCircuit0 0xe8a8a8a8 := by
  unfold upperComputes
  decide +kernel

def upperCircuit1 : Circuit := ⟨[⟨.or, [3,4]⟩, ⟨.and, [0,5]⟩, ⟨.and, [2,3]⟩, ⟨.and, [2,6]⟩, ⟨.or, [0,7]⟩, ⟨.and, [1,9]⟩, ⟨.or, [8,10]⟩], 11⟩
theorem upperCircuit1_mono : upperMono upperCircuit1 := by
  simp [upperMono, upperCircuit1]
theorem upperCircuit1_computes : upperComputes upperCircuit1 0xe8a8e888 := by
  unfold upperComputes
  decide +kernel

def upperCircuit2 : Circuit := ⟨[⟨.or, [0,2]⟩, ⟨.or, [3,4]⟩, ⟨.and, [1,6]⟩, ⟨.or, [1,6]⟩, ⟨.and, [0,8]⟩, ⟨.and, [2,9]⟩, ⟨.and, [5,7]⟩, ⟨.or, [10,11]⟩], 12⟩
theorem upperCircuit2_mono : upperMono upperCircuit2 := by
  simp [upperMono, upperCircuit2]
theorem upperCircuit2_computes : upperComputes upperCircuit2 0xe8e8e880 := by
  unfold upperComputes
  decide +kernel

def upperCircuit3 : Circuit := ⟨[⟨.and, [2,4]⟩, ⟨.and, [1,5]⟩, ⟨.or, [2,4]⟩, ⟨.and, [3,7]⟩, ⟨.and, [6,8]⟩, ⟨.or, [0,9]⟩, ⟨.or, [1,8]⟩, ⟨.or, [5,11]⟩, ⟨.and, [10,12]⟩], 13⟩
theorem upperCircuit3_mono : upperMono upperCircuit3 := by
  simp [upperMono, upperCircuit3]
theorem upperCircuit3_computes : upperComputes upperCircuit3 0xeaa8a888 := by
  unfold upperComputes
  decide +kernel

def upperCircuit4 : Circuit := ⟨[⟨.and, [1,3]⟩, ⟨.and, [2,5]⟩, ⟨.or, [0,6]⟩, ⟨.or, [2,3]⟩, ⟨.and, [4,8]⟩, ⟨.or, [1,9]⟩, ⟨.and, [7,10]⟩], 11⟩
theorem upperCircuit4_mono : upperMono upperCircuit4 := by
  simp [upperMono, upperCircuit4]
theorem upperCircuit4_computes : upperComputes upperCircuit4 0xeaa8c888 := by
  unfold upperComputes
  decide +kernel

def upperCircuit5 : Circuit := ⟨[⟨.and, [0,4]⟩, ⟨.or, [1,2]⟩, ⟨.and, [0,6]⟩, ⟨.and, [1,2]⟩, ⟨.or, [5,8]⟩, ⟨.and, [3,9]⟩, ⟨.or, [3,9]⟩, ⟨.and, [7,11]⟩, ⟨.or, [10,12]⟩], 13⟩
theorem upperCircuit5_mono : upperMono upperCircuit5 := by
  simp [upperMono, upperCircuit5]
theorem upperCircuit5_computes : upperComputes upperCircuit5 0xeaa8e880 := by
  unfold upperComputes
  decide +kernel

def upperCircuit6 : Circuit := ⟨[⟨.and, [0,1]⟩, ⟨.and, [1,3]⟩, ⟨.or, [5,6]⟩, ⟨.and, [2,7]⟩, ⟨.or, [4,6]⟩, ⟨.and, [0,9]⟩, ⟨.or, [8,10]⟩], 11⟩
theorem upperCircuit6_mono : upperMono upperCircuit6 := by
  simp [upperMono, upperCircuit6]
theorem upperCircuit6_computes : upperComputes upperCircuit6 0xeaaac880 := by
  unfold upperComputes
  decide +kernel

def upperCircuit7 : Circuit := ⟨[⟨.and, [0,3]⟩, ⟨.or, [2,4]⟩, ⟨.and, [5,6]⟩, ⟨.or, [2,5]⟩, ⟨.and, [1,8]⟩, ⟨.or, [7,9]⟩], 10⟩
theorem upperCircuit7_mono : upperMono upperCircuit7 := by
  simp [upperMono, upperCircuit7]
theorem upperCircuit7_computes : upperComputes upperCircuit7 0xeac0e8c0 := by
  unfold upperComputes
  decide +kernel

def upperCircuit8 : Circuit := ⟨[⟨.and, [0,3]⟩, ⟨.and, [0,4]⟩, ⟨.or, [1,5]⟩, ⟨.or, [2,6]⟩, ⟨.and, [7,8]⟩], 9⟩
theorem upperCircuit8_mono : upperMono upperCircuit8 := by
  simp [upperMono, upperCircuit8]
theorem upperCircuit8_computes : upperComputes upperCircuit8 0xeac8e0c0 := by
  unfold upperComputes
  decide +kernel

def upperCircuit9 : Circuit := ⟨[⟨.or, [0,2]⟩, ⟨.and, [1,5]⟩, ⟨.or, [1,3]⟩, ⟨.or, [3,4]⟩, ⟨.and, [6,8]⟩, ⟨.or, [2,4]⟩, ⟨.and, [7,10]⟩, ⟨.and, [0,11]⟩, ⟨.or, [9,12]⟩], 13⟩
theorem upperCircuit9_mono : upperMono upperCircuit9 := by
  simp [upperMono, upperCircuit9]
theorem upperCircuit9_computes : upperComputes upperCircuit9 0xeac8e880 := by
  unfold upperComputes
  decide +kernel

def upperBudget (T : Nat) : Nat :=
  if T = 0xe8a8a8a8 then 6 else
  if T = 0xe8a8e888 then 7 else
  if T = 0xe8e8e880 then 8 else
  if T = 0xeaa8a888 then 9 else
  if T = 0xeaa8c888 then 7 else
  if T = 0xeaa8e880 then 9 else
  if T = 0xeaaac880 then 7 else
  if T = 0xeac0e8c0 then 6 else
  if T = 0xeac8e0c0 then 5 else
  if T = 0xeac8e880 then 9 else
  0

theorem monotone_upper (T : Nat)
    (hT : T ∈ ({0xe8a8a8a8, 0xe8a8e888, 0xe8e8e880, 0xeaa8a888, 0xeaa8c888, 0xeaa8e880, 0xeaaac880, 0xeac0e8c0, 0xeac8e0c0, 0xeac8e880} : Finset Nat)) :
    ∃ C : Circuit, upperMono C ∧ C.gates.length = upperBudget T ∧ upperComputes C T := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hT
  rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨upperCircuit0, upperCircuit0_mono, by decide +kernel, upperCircuit0_computes⟩
  · exact ⟨upperCircuit1, upperCircuit1_mono, by decide +kernel, upperCircuit1_computes⟩
  · exact ⟨upperCircuit2, upperCircuit2_mono, by decide +kernel, upperCircuit2_computes⟩
  · exact ⟨upperCircuit3, upperCircuit3_mono, by decide +kernel, upperCircuit3_computes⟩
  · exact ⟨upperCircuit4, upperCircuit4_mono, by decide +kernel, upperCircuit4_computes⟩
  · exact ⟨upperCircuit5, upperCircuit5_mono, by decide +kernel, upperCircuit5_computes⟩
  · exact ⟨upperCircuit6, upperCircuit6_mono, by decide +kernel, upperCircuit6_computes⟩
  · exact ⟨upperCircuit7, upperCircuit7_mono, by decide +kernel, upperCircuit7_computes⟩
  · exact ⟨upperCircuit8, upperCircuit8_mono, by decide +kernel, upperCircuit8_computes⟩
  · exact ⟨upperCircuit9, upperCircuit9_mono, by decide +kernel, upperCircuit9_computes⟩

theorem monotone_equivalent_of_upperBudget_le (T : Nat)
    (hT : T ∈ ({0xe8a8a8a8, 0xe8a8e888, 0xe8e8e880, 0xeaa8a888, 0xeaa8c888, 0xeaa8e880, 0xeaaac880, 0xeac0e8c0, 0xeac8e0c0, 0xeac8e880} : Finset Nat))
    (gates : List Gate) (hsize : upperBudget T ≤ gates.length) :
    ∃ (gates' : List Gate) (o' : Nat),
      (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧
      ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) =
        Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : Nat) else 0) := by
  rcases monotone_upper T hT with ⟨C, hmono, hlen, heval⟩
  exact ⟨C.gates, C.output, hmono, hlen.le.trans hsize, heval⟩

end PEqualNP.Outside.L_meta_1425.Cert
