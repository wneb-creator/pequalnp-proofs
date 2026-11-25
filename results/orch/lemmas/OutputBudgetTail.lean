namespace PEqualNP.Outside.L_meta_4970.OutputBoundary

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge

def andIndices (C : Circuit) : Finset ℕ :=
  (Finset.range C.size).filter fun j => (gateAt C j).op = GateOp.and

def outputOrIndices (n : ℕ) (C : Circuit) : Finset ℕ :=
  (Finset.range C.size).filter fun j =>
    (gateAt C j).op = GateOp.or ∧ OrReaches n C C.output j

lemma owned_and_boundary_budget (n : ℕ) (C : Circuit) (K B : Finset ℕ)
    (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hreject : ∀ v : Fin n, circuitFun n C (fun i => decide (i = v)) = false)
    (hK : ∀ j ∈ K, j < C.size ∧ (gateAt C j).op = GateOp.or ∧
      ∃ v : Fin n, OrSeparation.sep_W n C (fun i => decide (i = v)) (n + j) = true)
    (hB : ∀ j ∈ B, j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
      OrReaches n C C.output j) :
    K.card + (andIndices C).card + B.card ≤ C.size + 1 := by
  classical
  have hbo := output_and_boundary_card_le n C B hAO hB
  have hset : {j : ℕ | j < C.gates.length ∧ (gateAt C j).op = GateOp.or ∧
      OrReaches n C C.output j} = (↑(outputOrIndices n C) : Set ℕ) := by
    ext j
    simp [outputOrIndices, Circuit.size, and_assoc]
  rw [hset, Set.ncard_coe_finset] at hbo
  have hKA : Disjoint K (andIndices C) := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    have ho := (hK j hj).2.1
    have ha := (Finset.mem_filter.mp hk).2
    rw [ho] at ha
    exact GateOp.noConfusion ha
  have hKO : Disjoint K (outputOrIndices n C) := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    exact OrSeparation.singleton_true_excludes_output_or_closure n C hreject j
      (hK j hj).2.2 (Finset.mem_filter.mp hk).2.2
  have hAO' : Disjoint (andIndices C) (outputOrIndices n C) := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    have ha := (Finset.mem_filter.mp hj).2
    have ho := (Finset.mem_filter.mp hk).2.1
    rw [ha] at ho
    exact GateOp.noConfusion ho
  have hUO : Disjoint (K ∪ andIndices C) (outputOrIndices n C) := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    rcases Finset.mem_union.mp hj with hj | hj
    · exact Finset.disjoint_left.mp hKO hj hk
    · exact Finset.disjoint_left.mp hAO' hj hk
  have hsub : (K ∪ andIndices C) ∪ outputOrIndices n C ⊆ Finset.range C.size := by
    intro j hj
    rcases Finset.mem_union.mp hj with hj | hj
    · rcases Finset.mem_union.mp hj with hj | hj
      · exact Finset.mem_range.mpr (hK j hj).1
      · exact (Finset.mem_filter.mp hj).1
    · exact (Finset.mem_filter.mp hj).1
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hUO, Finset.card_union_of_disjoint hKA,
    Finset.card_range] at hc
  omega

end PEqualNP.Outside.L_meta_4970.OutputBoundary
