import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.ReadK

abbrev fanoIncidence (p l : Fin 7) : Prop :=
  p = l ∨ p = l + 1 ∨ p = l + 3

lemma fanoLineCard : ∀ l : Fin 7,
    (Finset.univ.filter (fun p => fanoIncidence p l)).card = 3 := by
  decide

lemma fanoUniqueLine : ∀ p p' : Fin 7, p ≠ p' →
    ∃! l : Fin 7, fanoIncidence p l ∧ fanoIncidence p' l := by
  unfold ExistsUnique
  decide

def fanoCircuit : Circuit :=
  ⟨[
    ⟨GateOp.or, [0, 1]⟩,
    ⟨GateOp.or, [14, 3]⟩,
    ⟨GateOp.and, [15, 7]⟩,
    ⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [17, 4]⟩,
    ⟨GateOp.and, [18, 8]⟩,
    ⟨GateOp.or, [2, 3]⟩,
    ⟨GateOp.or, [20, 5]⟩,
    ⟨GateOp.and, [21, 9]⟩,
    ⟨GateOp.or, [3, 4]⟩,
    ⟨GateOp.or, [23, 6]⟩,
    ⟨GateOp.and, [24, 10]⟩,
    ⟨GateOp.or, [4, 5]⟩,
    ⟨GateOp.or, [26, 0]⟩,
    ⟨GateOp.and, [27, 11]⟩,
    ⟨GateOp.or, [5, 6]⟩,
    ⟨GateOp.or, [29, 1]⟩,
    ⟨GateOp.and, [30, 12]⟩,
    ⟨GateOp.or, [6, 0]⟩,
    ⟨GateOp.or, [32, 2]⟩,
    ⟨GateOp.and, [33, 13]⟩,
    ⟨GateOp.or, [16, 19]⟩,
    ⟨GateOp.or, [35, 22]⟩,
    ⟨GateOp.or, [36, 25]⟩,
    ⟨GateOp.or, [37, 28]⟩,
    ⟨GateOp.or, [38, 31]⟩,
    ⟨GateOp.or, [39, 34]⟩
  ], 40⟩

lemma fanoCircuitSize : fanoCircuit.size = 27 := rfl

lemma fanoCircuitAO : IsAO2 14 fanoCircuit := by
  decide


end PEqualNP.Outside.L_meta_2583_aux
