import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4970.H9RedTeam

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.TwoColour

def hiddenMixed : Circuit :=
  ⟨[⟨.and, [0, 0]⟩, ⟨.and, [1, 1]⟩, ⟨.or, [2, 3]⟩], 4⟩

lemma hiddenMixed_model : IsAO2 2 hiddenMixed := by decide +kernel

lemma hiddenMixed_tCount : tCount 2 hiddenMixed (fun i => decide (1 ≤ i)) = 0 := by
  decide +kernel

lemma hiddenMixed_function :
    ∀ x : Fin 2 → Bool, circuitFun 2 hiddenMixed x = (x 0 || x 1) := by
  decide +kernel

lemma hiddenMixed_reach : orIn 2 hiddenMixed 4 = ∅ := by decide +kernel

def hiddenMixedBypass : Circuit := ⟨[⟨.or, [0, 1]⟩], 2⟩

lemma hiddenMixedBypass_same :
    ∀ x : Fin 2 → Bool, circuitFun 2 hiddenMixedBypass x = circuitFun 2 hiddenMixed x := by
  decide +kernel

lemma hiddenMixedBypass_tCount :
    tCount 2 hiddenMixedBypass (fun i => decide (1 ≤ i)) = 1 := by decide +kernel

def deadStar : Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [0, 4]⟩, ⟨.or, [1, 2]⟩], 5⟩

lemma deadStar_model : IsAO2 3 deadStar := by decide +kernel

lemma deadStar_tCount : tCount 3 deadStar (fun i => decide (1 ≤ i)) = 0 := by
  decide +kernel

lemma deadStar_no_four_cycle :
    ∀ (a a' : Fin 1) (b b' : Fin 2), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ (Finset.univ : Finset (Fin 1 × Fin 2)) ∧
        (a, b') ∈ (Finset.univ : Finset (Fin 1 × Fin 2)) ∧
        (a', b) ∈ (Finset.univ : Finset (Fin 1 × Fin 2)) ∧
        (a', b') ∈ (Finset.univ : Finset (Fin 1 × Fin 2))) := by decide +kernel

lemma deadStar_function :
    ∀ x : Fin 3 → Bool, circuitFun 3 deadStar x =
      decide (∃ (a : Fin 1) (b : Fin 2), x (Fin.castAdd 2 a) = true ∧
        x (Fin.natAdd 1 b) = true) := by
  decide +kernel

lemma deadStar_served :
    ∀ (a : Fin 1) (b : Fin 2),
      ∃ (j : ℕ) (Q : Finset (Fin 2)),
        j < deadStar.gates.length ∧ (gateAt deadStar j).op = .or ∧
        2 ≤ Q.card ∧ b ∈ Q ∧
        (∀ b' ∈ Q, (a, b') ∈ (Finset.univ : Finset (Fin 1 × Fin 2))) ∧
        ∀ x : Fin 3 → Bool,
          (deadStar.wires (List.ofFn x)).getD (3 + j) false =
            decide (∃ b' ∈ Q, x (Fin.natAdd 1 b') = true) := by
  intro a b
  refine ⟨3, Finset.univ, by decide, rfl, by decide, Finset.mem_univ b, ?_, ?_⟩
  · intro b' hb'
    exact Finset.mem_univ (a, b')
  · decide +kernel

lemma deadStar_not_read : ∀ g ∈ deadStar.gates, 6 ∉ g.inputs := by decide +kernel

lemma deadStar_topOperand_not_pure :
    ∀ Q : Finset (Fin 3),
      ¬ (∀ x : Fin 3 → Bool,
        (deadStar.wires (List.ofFn x)).getD 4 false =
          decide (∃ i ∈ Q, x i = true)) := by
  decide +kernel

def disconnectedStars : Circuit :=
  ⟨[⟨.or, [1, 2]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [0, 5]⟩,
    ⟨.and, [0, 6]⟩, ⟨.or, [7, 8]⟩], 9⟩

lemma disconnectedStars_model : IsAO2 5 disconnectedStars := by decide +kernel

lemma disconnectedStars_tCount :
    tCount 5 disconnectedStars (fun i => decide (1 ≤ i)) = 0 := by decide +kernel

lemma disconnectedStars_function :
    ∀ x : Fin 5 → Bool, circuitFun 5 disconnectedStars x =
      (x 0 && (x 1 || x 2 || x 3 || x 4)) := by decide +kernel

lemma disconnectedStars_no_full_witness :
    ∀ j : Fin disconnectedStars.gates.length,
      ¬ (∀ x : Fin 5 → Bool,
        (disconnectedStars.wires (List.ofFn x)).getD (5 + j) false =
          (x 1 || x 2 || x 3 || x 4)) := by decide +kernel

lemma disconnectedStars_served :
    ∀ b : Fin 4, ∃ (j : Fin 2) (Q : Finset (Fin 4)),
      2 ≤ Q.card ∧ b ∈ Q ∧
      ∀ x : Fin 5 → Bool,
        (disconnectedStars.wires (List.ofFn x)).getD (5 + j) false =
          decide (∃ b' ∈ Q, x (Fin.natAdd 1 b') = true) := by decide +kernel

def mixedFanout : Circuit :=
  ⟨[⟨.and, [0, 0]⟩, ⟨.or, [4, 1]⟩, ⟨.or, [4, 2]⟩, ⟨.or, [4, 3]⟩,
    ⟨.or, [5, 6]⟩, ⟨.or, [8, 7]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [10, 3]⟩,
    ⟨.and, [0, 11]⟩, ⟨.and, [12, 9]⟩], 13⟩

lemma mixedFanout_model : IsAO2 4 mixedFanout := by decide +kernel

lemma mixedFanout_tCount : tCount 4 mixedFanout (fun i => decide (1 ≤ i)) = 0 := by
  decide +kernel

lemma mixedFanout_function :
    ∀ x : Fin 4 → Bool, circuitFun 4 mixedFanout x =
      (x 0 && (x 1 || x 2 || x 3)) := by decide +kernel

lemma mixedFanout_serving_star :
    ∀ x : Fin 4 → Bool, (mixedFanout.wires (List.ofFn x)).getD 11 false =
      (x 1 || x 2 || x 3) := by decide +kernel

lemma mixedFanout_edge_active :
    ∀ j : Fin mixedFanout.gates.length, ∃ b : Fin 3,
      (mixedFanout.wires (List.ofFn fun i : Fin 4 =>
        decide (i = 0 ∨ i = Fin.natAdd 1 b))).getD (4 + j) false = true := by
  decide +kernel

lemma mixedFanout_five_semantically_mixed :
    ∀ j : Fin 5,
      (mixedFanout.wires (List.ofFn fun i : Fin 4 => decide (i = 0))).getD
        (5 + j) false = true ∧
      ∃ b : Fin 3,
        (mixedFanout.wires (List.ofFn fun i : Fin 4 => decide (i = Fin.natAdd 1 b))).getD
          (5 + j) false = true := by decide +kernel

lemma mixedFanout_three_and :
    (mixedFanout.gates.filter fun g => match g.op with
      | .and => true
      | _ => false).length = 3 := by decide +kernel

end PEqualNP.Outside.L_meta_4970.H9RedTeam
