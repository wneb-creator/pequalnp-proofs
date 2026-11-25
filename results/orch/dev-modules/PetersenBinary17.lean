import FullRun
import FullRunLower17
import MiniNine

namespace PEqualNP.Outside.L_meta_2592

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma split_not_count (gs : List Gate) :
    gs.countP (fun g => !FullRun.isNot g) + (gs.filter FullRun.isNot).length = gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    cases h : FullRun.isNot g <;> simp_all <;> omega

lemma not_count_identification (C : Circuit) :
    (C.gates.filter FullRun.isNot).length = PEqualNP.NotBracket.notCount C := by
  unfold PEqualNP.NotBracket.notCount
  congr 2
  funext g
  unfold FullRun.isNot
  cases g.op <;> rfl

lemma petersen_binary_lower17_of_table
    (lower : SignedFloor.Lower true SignedFloor.inputs SignedFloor.graph 15)
    (C : Circuit) (fan : FanInTwo C)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = structuralEdge x) :
    17 + PEqualNP.NotBracket.notCount C ≤ C.size := by
  obtain ⟨k,hk,run⟩ := FullRun.circuit_run C fan computes
  have bound := FullRun.fullRun_lower17_of_deleted_lower
    (SignedFloor.functional_lower_of_table lower) k run
  have total := split_not_count C.gates
  rw [not_count_identification C] at total
  change 17 + PEqualNP.NotBracket.notCount C ≤ C.gates.length
  omega

end PEqualNP.Outside.L_meta_2592
