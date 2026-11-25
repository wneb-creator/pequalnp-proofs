import TightNotFirst

namespace PEqualNP.Outside.L_meta_10760_first

open PEqualNP.CircuitLowerBounds

def CC : List Gate := [
  ⟨.and, [0, 2]⟩,
  ⟨.and, [1, 4]⟩,
  ⟨.or, [0, 3]⟩,
  ⟨.and, [5, 9]⟩,
  ⟨.or, [0, 2]⟩,
  ⟨.or, [4, 6]⟩,
  ⟨.and, [11, 12]⟩,
  ⟨.or, [3, 5]⟩,
  ⟨.or, [1, 6]⟩,
  ⟨.and, [14, 15]⟩,
  ⟨.or, [7, 8]⟩,
  ⟨.or, [10, 13]⟩,
  ⟨.or, [17, 18]⟩,
  ⟨.or, [19, 16]⟩]

set_option maxRecDepth 100000 in
lemma dec_f : ∀ x : Fin 7 → Bool, decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) = f x := by decide +kernel

set_option maxRecDepth 100000 in
lemma CC_f : ∀ x : Fin 7 → Bool, Circuit.eval ⟨CC, 20⟩ (List.ofFn x) = f x := by decide +kernel

lemma CC_monotone : ∀ g ∈ CC, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  simp [CC]

lemma CC_length : CC.length = 14 := rfl


lemma replacement_from_one
    (hmin : Imp [] 0 13)
    (hnot : ∀ S : Finset ℕ, (S : Set ℕ) ⊆ C (mz 0) (WZ [] 0) → ¬ Live Z0 (mz 0) (tz 0) 13 1 S) :
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o hg hu hf
  rcases monotone_or_one gates hg hu with hm | hn
  · exact ⟨gates, o, hm, le_rfl, hf⟩
  · have hfan : PEqualNP.MetaComplexity.FanInTwo ⟨gates, o⟩ := by
      intro g hmem
      refine ⟨?_, (hg g hmem).2⟩
      rcases (hg g hmem).1 with e | e | e <;> simp [e]
    have hlr := bridge_ltr ⟨gates, o⟩ hfan (fun x => (hf x).trans (dec_f x))
    have h13 : 13 ≤ gates.length := by
      by_contra hlt
      obtain ⟨k, hk, t, ht, hbal, S, hS, hl⟩ := hlr
      exact hmin k (by change k ≤ gates.length at hk; omega) (hl.sol.mono le_rfl hS)
    have h14 : 14 ≤ gates.length := by
      by_contra hlt
      have hlen : gates.length = 13 := by omega
      have hLR : LTR (mz 0) (tz 0) 13 1 (C (mz 0) (WZ [] 0)) := by
        simpa only [PEqualNP.CircuitLowerBounds.Circuit.size, hlen, hn] using hlr
      obtain ⟨S, hS, hL⟩ := LTR.exact_counts hmin hLR
      exact hnot S hS hL
    exact ⟨CC, 20, CC_monotone, by simpa only [CC_length] using h14,
      fun x => (CC_f x).trans (dec_f x).symm⟩

end PEqualNP.Outside.L_meta_10760_first
