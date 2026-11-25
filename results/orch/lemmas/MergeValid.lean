import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2585.Merge

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
  PEqualNP.MetaComplexity.NestedCover

def shIdx (n s i : ℕ) : ℕ := if i < n then i else i + s

def shGate (n s : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (shIdx n s)⟩

def concat (n : ℕ) (C D : Circuit) : Circuit :=
  ⟨C.gates ++ D.gates.map (shGate n C.size), shIdx n C.size D.output⟩

lemma shIdx_lt (n s j i : ℕ) (hi : i < n + j) :
    shIdx n s i < n + s + j := by
  unfold shIdx
  split_ifs <;> omega

lemma concat_size (n : ℕ) (C D : Circuit) :
    (concat n C D).size = C.size + D.size := by
  simp [concat, Circuit.size]

lemma gateAt_concat_left (n : ℕ) (C D : Circuit) (j : ℕ)
    (hj : j < C.gates.length) : gateAt (concat n C D) j = gateAt C j := by
  exact List.getD_append _ _ _ _ hj

lemma gateAt_concat_right (n : ℕ) (C D : Circuit) (j : ℕ)
    (hj : j < D.gates.length) :
    gateAt (concat n C D) (C.gates.length + j) = shGate n C.size (gateAt D j) := by
  unfold gateAt concat
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp [List.getD_eq_getElem?_getD, hj]

lemma concat_valid (n : ℕ) (C D : Circuit)
    (hC : IsAO2 n C) (hD : IsAO2 n D) : IsAO2 n (concat n C D) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [concat, List.mem_append, List.mem_map] at hg
    rcases hg with hg | ⟨g, hg, rfl⟩
    · exact hC.1 g hg
    · exact hD.1 g hg
  · intro j hj i hi
    have hj' : j < C.gates.length + D.gates.length := by simpa [concat] using hj
    by_cases hjC : j < C.gates.length
    · rw [gateAt_concat_left n C D j hjC] at hi
      exact hC.2.1 j hjC i hi
    · let k := j - C.gates.length
      have hk : k < D.gates.length := by dsimp [k]; omega
      have hjk : j = C.gates.length + k := by dsimp [k]; omega
      rw [hjk, gateAt_concat_right n C D k hk] at hi
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hi
      have hb := shIdx_lt n C.size k a (hD.2.1 k hk a ha)
      simpa [Circuit.size, hjk, Nat.add_assoc] using hb
  · intro g hg
    simp only [concat, List.mem_append, List.mem_map] at hg
    rcases hg with hg | ⟨g, hg, rfl⟩
    · exact hC.2.2 g hg
    · simpa [shGate] using hD.2.2 g hg

lemma concat_output (n : ℕ) (C D : Circuit) (hD : D.output < n + D.size) :
    (concat n C D).output < n + (concat n C D).size := by
  change shIdx n C.size D.output < n + (concat n C D).size
  rw [concat_size]
  have h := shIdx_lt n C.size D.size D.output hD
  omega

end PEqualNP.Outside.L_meta_2585.Merge
