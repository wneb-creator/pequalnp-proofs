import PEqualNP.Defs

namespace CyclicPlaneAudit

def lines (w : Fin 13) : Finset (Fin 13) :=
  ({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + w)

example : ∀ w, (lines w).card = 4 := by decide

example : ∀ i j, i ≠ j → (lines i ∩ lines j).card = 1 := by decide

example : ∀ p, (Finset.univ.filter (fun w => p ∈ lines w)).card = 4 := by decide

example : ∀ w, (Finset.univ \ lines w).card = 9 := by decide

example : ∀ w p, p ∉ lines w → ((Finset.univ \ lines w).erase p).card = 8 := by decide

example : ∀ i j, i ≠ j → (lines i ∪ lines j).card = 7 := by decide

end CyclicPlaneAudit
