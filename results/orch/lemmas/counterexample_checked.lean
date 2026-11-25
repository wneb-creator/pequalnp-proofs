import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4970_aux

open PEqualNP.CircuitLowerBounds

def auditC : Circuit :=
  ⟨[⟨.or, [1, 2]⟩, ⟨.and, [3, 3]⟩, ⟨.or, [4, 4]⟩], 5⟩

lemma audit_isAO2 : PEqualNP.TopForm.IsAO2 3 auditC := by
  decide +kernel

lemma audit_tCount :
    PEqualNP.TwoColour.tCount 3 auditC (fun i => decide (1 ≤ i)) = 0 := by
  decide +kernel

lemma audit_star_function : ∀ x : Fin 3 → Bool,
    (auditC.wires (List.ofFn x)).getD 5 false = (x 1 || x 2) := by
  decide +kernel

lemma audit_or_reach_empty : PEqualNP.TopForm.orIn 3 auditC 5 = ∅ := by
  decide +kernel

def anchoredC : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.and, [1, 1]⟩, ⟨.and, [2, 2]⟩,
    ⟨.or, [5, 6]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [4, 7]⟩,
    ⟨.and, [7, 8]⟩, ⟨.and, [9, 10]⟩], 11⟩

def anchoredEdges : Finset (Fin 2 × Fin 2) := {(0, 0), (1, 0), (1, 1)}

lemma anchored_isAO2 : PEqualNP.TopForm.IsAO2 4 anchoredC := by
  decide +kernel

lemma anchored_tCount :
    PEqualNP.TwoColour.tCount 4 anchoredC (fun i => decide (2 ≤ i)) = 0 := by
  decide +kernel

lemma anchored_function : ∀ x : Fin 4 → Bool,
    PEqualNP.MetaComplexity.circuitFun 4 anchoredC x =
      decide (∃ (a b : Fin 2), (a, b) ∈ anchoredEdges ∧
        x (Fin.castAdd 2 a) = true ∧ x (Fin.natAdd 2 b) = true) := by
  decide +kernel

lemma anchored_no_four_cycle : ∀ (a a' b b' : Fin 2),
    a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ anchoredEdges ∧ (a, b') ∈ anchoredEdges ∧
        (a', b) ∈ anchoredEdges ∧ (a', b') ∈ anchoredEdges) := by
  decide +kernel

lemma anchored_cover_large : ∀ S : Finset (Fin 4),
    (∀ (a b : Fin 2), (a, b) ∈ anchoredEdges →
      Fin.castAdd 2 a ∈ S ∨ Fin.natAdd 2 b ∈ S) → 2 ≤ S.card := by
  decide +kernel

lemma anchored_one_empty_support :
    ((Finset.range anchoredC.gates.length).filter fun j =>
      ∀ i : Fin 4,
        (anchoredC.wires (List.ofFn fun k => decide (k = i))).getD (4 + j) false = false).card = 1 := by
  decide +kernel

lemma anchored_left_star : ∀ x : Fin 4 → Bool,
    (anchoredC.wires (List.ofFn x)).getD 4 false =
      decide (∃ a ∈ (Finset.univ : Finset (Fin 2)), x (Fin.castAdd 2 a) = true) := by
  decide +kernel

lemma anchored_right_star : ∀ x : Fin 4 → Bool,
    (anchoredC.wires (List.ofFn x)).getD 8 false =
      decide (∃ b ∈ (Finset.univ : Finset (Fin 2)), x (Fin.natAdd 2 b) = true) := by
  decide +kernel

lemma anchored_stars : ∀ (a b : Fin 2), (a, b) ∈ anchoredEdges →
    (∃ (j : ℕ) (Q : Finset (Fin 2)), j < anchoredC.gates.length ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt anchoredC j).op = GateOp.or ∧
      2 ≤ Q.card ∧ b ∈ Q ∧ (∀ b' ∈ Q, (a, b') ∈ anchoredEdges) ∧
      ∀ x : Fin 4 → Bool,
        (anchoredC.wires (List.ofFn x)).getD (4 + j) false =
          decide (∃ b' ∈ Q, x (Fin.natAdd 2 b') = true)) ∨
    (∃ (j : ℕ) (P : Finset (Fin 2)), j < anchoredC.gates.length ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt anchoredC j).op = GateOp.or ∧
      2 ≤ P.card ∧ a ∈ P ∧ (∀ a' ∈ P, (a', b) ∈ anchoredEdges) ∧
      ∀ x : Fin 4 → Bool,
        (anchoredC.wires (List.ofFn x)).getD (4 + j) false =
          decide (∃ a' ∈ P, x (Fin.castAdd 2 a') = true)) := by
  intro a b hab
  by_cases hb : b = 0
  · subst b
    exact Or.inr ⟨0, Finset.univ, by decide, rfl, by decide,
      Finset.mem_univ a, by decide, anchored_left_star⟩
  · have hb1 : b = 1 := by omega
    have ha1 : a = 1 := by simpa [anchoredEdges, hb1] using hab
    subst a
    subst b
    exact Or.inl ⟨4, Finset.univ, by decide, rfl, by decide,
      Finset.mem_univ 1, by decide, anchored_right_star⟩

end PEqualNP.Outside.L_meta_4970_aux
