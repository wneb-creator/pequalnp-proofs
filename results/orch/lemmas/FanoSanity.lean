import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4675_fano_sanity

open PEqualNP.CircuitLowerBounds

def fanoEdges : Finset (Fin 7 × Fin 7) := {(0, 0), (0, 4), (0, 6), (1, 0), (1, 1), (1, 5), (2, 1), (2, 2), (2, 6), (3, 0), (3, 2), (3, 3), (4, 1), (4, 3), (4, 4), (5, 2), (5, 4), (5, 5), (6, 3), (6, 5), (6, 6)}

def fanoCircuit : Circuit :=
  ⟨[
    ⟨.or, [7, 11]⟩,
    ⟨.or, [14, 13]⟩,
    ⟨.and, [0, 15]⟩,
    ⟨.or, [7, 8]⟩,
    ⟨.or, [17, 12]⟩,
    ⟨.and, [1, 18]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.or, [20, 13]⟩,
    ⟨.and, [2, 21]⟩,
    ⟨.or, [7, 9]⟩,
    ⟨.or, [23, 10]⟩,
    ⟨.and, [3, 24]⟩,
    ⟨.or, [8, 10]⟩,
    ⟨.or, [26, 11]⟩,
    ⟨.and, [4, 27]⟩,
    ⟨.or, [9, 11]⟩,
    ⟨.or, [29, 12]⟩,
    ⟨.and, [5, 30]⟩,
    ⟨.or, [10, 12]⟩,
    ⟨.or, [32, 13]⟩,
    ⟨.and, [6, 33]⟩,
    ⟨.or, [16, 19]⟩,
    ⟨.or, [35, 22]⟩,
    ⟨.or, [36, 25]⟩,
    ⟨.or, [37, 28]⟩,
    ⟨.or, [38, 31]⟩,
    ⟨.or, [39, 34]⟩], 40⟩

def fanoExpression (x : Fin 14 → Bool) : Bool :=
  x 0 && (x 7 || x 11 || x 13) ||
  x 1 && (x 7 || x 8 || x 12) ||
  x 2 && (x 8 || x 9 || x 13) ||
  x 3 && (x 7 || x 9 || x 10) ||
  x 4 && (x 8 || x 10 || x 11) ||
  x 5 && (x 9 || x 11 || x 12) ||
  x 6 && (x 10 || x 12 || x 13)

set_option maxHeartbeats 2000000 in
lemma fano_isAO2 : PEqualNP.TopForm.IsAO2 14 fanoCircuit := by decide

lemma fano_edge_count : fanoEdges.card = 21 := by decide

lemma fano_size : fanoCircuit.size = 27 := by rfl

set_option maxHeartbeats 2000000 in
lemma fano_no_four_cycle :
    ∀ (a a' : Fin 7) (b b' : Fin 7), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ fanoEdges ∧ (a, b') ∈ fanoEdges ∧
        (a', b) ∈ fanoEdges ∧ (a', b') ∈ fanoEdges) := by decide

set_option maxHeartbeats 2000000 in
lemma fano_no_mixing :
    PEqualNP.TwoColour.tCount 14 fanoCircuit (fun i => decide (7 ≤ i)) = 0 := by decide

set_option maxHeartbeats 2000000 in
lemma fano_eval (x : Fin 14 → Bool) :
    PEqualNP.MetaComplexity.circuitFun 14 fanoCircuit x = fanoExpression x := by
  simp [PEqualNP.MetaComplexity.circuitFun, Circuit.eval, Circuit.wires, fanoCircuit,
    fanoExpression, GateOp.eval, List.ofFn_succ, Bool.or_assoc]

set_option maxHeartbeats 2000000 in
lemma fano_computes :
    ∀ x : Fin 14 → Bool, PEqualNP.MetaComplexity.circuitFun 14 fanoCircuit x =
      decide (∃ (a : Fin 7) (b : Fin 7), (a, b) ∈ fanoEdges ∧
        x (Fin.castAdd 7 a) = true ∧ x (Fin.natAdd 7 b) = true) := by
  intro x
  rw [fano_eval]
  simp [fanoExpression, fanoEdges, Fin.exists_fin_succ, Bool.and_or_distrib_left, Bool.or_assoc]

end PEqualNP.Outside.L_meta_4675_fano_sanity
