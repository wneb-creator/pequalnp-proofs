import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4675.Normalization

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.TwoColour

lemma no_twoColour_of_count_zero (n : ℕ) (C : Circuit) (s : ℕ → Bool)
    (hz : tCount n C s = 0) (g : ℕ) : ¬ IsTwoColour n C s g := by
  intro hg
  have he : twoColour n C s = ∅ := Finset.card_eq_zero.mp hz
  have hm : g ∈ twoColour n C s :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hg.1, hg⟩
  rw [he] at hm
  simpa using hm

lemma orIn_same_colour (n : ℕ) (C : Circuit) (s : ℕ → Bool)
    (hz : tCount n C s = 0) (g : ℕ) (hg : g < C.gates.length)
    (hop : (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = GateOp.or)
    (i j : Fin n) (hi : i ∈ orIn n C (n + g)) (hj : j ∈ orIn n C (n + g)) :
    s i = s j := by
  cases hci : s i <;> cases hcj : s j
  · rfl
  · exact False.elim (no_twoColour_of_count_zero n C s hz g
      ⟨hg, hop, ⟨i, hi, hci⟩, ⟨j, hj, hcj⟩⟩)
  · exact False.elim (no_twoColour_of_count_zero n C s hz g
      ⟨hg, hop, ⟨j, hj, hcj⟩, ⟨i, hi, hci⟩⟩)
  · rfl

lemma orIn_one_colour (n : ℕ) (C : Circuit) (s : ℕ → Bool)
    (hz : tCount n C s = 0) (g : ℕ) (hg : g < C.gates.length)
    (hop : (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = GateOp.or) :
    (∀ i ∈ orIn n C (n + g), s i = false) ∨
      (∀ i ∈ orIn n C (n + g), s i = true) := by
  by_cases h : ∃ i ∈ orIn n C (n + g), s i = true
  · obtain ⟨i, hi, hci⟩ := h
    right
    intro j hj
    exact (orIn_same_colour n C s hz g hg hop j i hj hi).trans hci
  · left
    intro i hi
    cases hci : s i
    · rfl
    · exact False.elim (h ⟨i, hi, hci⟩)

def maskedMix : Circuit :=
  ⟨[⟨GateOp.and, [0, 0]⟩, ⟨GateOp.and, [1, 1]⟩,
    ⟨GateOp.or, [2, 3]⟩], 4⟩

lemma maskedMix_ao : IsAO2 2 maskedMix := by decide

lemma maskedMix_count : tCount 2 maskedMix (fun i => decide (1 ≤ i)) = 0 := by decide

lemma maskedMix_reach : orIn 2 maskedMix 4 = ∅ := by decide

lemma maskedMix_semantics : ∀ x : Fin 2 → Bool,
    PEqualNP.MetaComplexity.circuitFun 2 maskedMix x = (x 0 || x 1) := by decide

def repeatedEdge : Circuit :=
  ⟨[⟨GateOp.and, [0, 0]⟩, ⟨GateOp.and, [2, 1]⟩], 3⟩

lemma repeatedEdge_ao : IsAO2 2 repeatedEdge := by decide

lemma repeatedEdge_count : tCount 2 repeatedEdge (fun i => decide (1 ≤ i)) = 0 := by decide

lemma repeatedEdge_semantics : ∀ x : Fin 2 → Bool,
    PEqualNP.MetaComplexity.circuitFun 2 repeatedEdge x = (x 0 && x 1) := by decide

lemma repeatedEdge_not_readOne : PEqualNP.ReadK.readsAtMost repeatedEdge 2 [0, 1] 1 = false := by decide

end PEqualNP.Outside.L_meta_4675.Normalization
