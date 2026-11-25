import SelfChargedBudget
import Neighbourhoods
import EdgeSupportCard

namespace PEqualNP.Outside.L_meta_4970.EdgeSupport

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4970.SupportAccounting
open PEqualNP.Outside.L_meta_4970_aux

lemma pure_or_mem_charged (n : ℕ) (C : Circuit) (j : ℕ)
    (Q S : Finset (Fin n)) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hcard : 2 ≤ Q.card) (hQS : Q ⊆ S)
    (h : ∀ x : Fin n → Bool, PEqualNP.BlindGate.wireValue C n x (n + j) =
      decide (∃ i ∈ Q, x i = true)) : n + j ∈ charged n C S := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr (by omega), by omega, ?_, ?_, ?_⟩
  · exact pure_or_good n C (n + j) Q S (by omega) hQS h
  · simpa using hop
  · rw [pure_or_support n C (n + j) Q h]
    omega

lemma left_witness_covered (p l : ℕ) (E : Finset (Fin p × Fin l))
    (C : Circuit) (a : Fin p) (b : Fin l) (j : ℕ) (Q : Finset (Fin l))
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or)
    (hcard : 2 ≤ Q.card) (hb : b ∈ Q) (hQE : ∀ b' ∈ Q, (a, b') ∈ E)
    (h : ∀ x : Fin (p + l) → Bool,
      (C.wires (List.ofFn x)).getD (p + l + j) false =
        decide (∃ b' ∈ Q, x (Fin.natAdd p b') = true)) :
    Fin.natAdd p b ∈
      (charged (p + l) C (neighbours E (Fin.castAdd l a))).biUnion
        (singleSupport (p + l) C) := by
  classical
  let Q' : Finset (Fin (p + l)) := Q.image (Fin.natAdd p)
  have hsem : ∀ x : Fin (p + l) → Bool,
      PEqualNP.BlindGate.wireValue C (p + l) x (p + l + j) =
        decide (∃ i ∈ Q', x i = true) := by
    intro x
    simpa [PEqualNP.BlindGate.wireValue, Q'] using h x
  have hsub : Q' ⊆ neighbours E (Fin.castAdd l a) := by
    intro i hi
    obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hi
    rw [neighbours_left]
    exact Finset.mem_image.mpr ⟨b', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hQE b' hb'⟩, rfl⟩
  have hcard' : 2 ≤ Q'.card := by
    rw [show Q'.card = Q.card from Finset.card_image_of_injective Q (fun _ _ h => right_inj h)]
    exact hcard
  apply Finset.mem_biUnion.mpr
  refine ⟨p + l + j, pure_or_mem_charged (p + l) C j Q' _ hj hop hcard' hsub hsem, ?_⟩
  rw [pure_or_support (p + l) C (p + l + j) Q' hsem]
  exact Finset.mem_image.mpr ⟨b, hb, rfl⟩

lemma right_witness_covered (p l : ℕ) (E : Finset (Fin p × Fin l))
    (C : Circuit) (a : Fin p) (b : Fin l) (j : ℕ) (P : Finset (Fin p))
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or)
    (hcard : 2 ≤ P.card) (ha : a ∈ P) (hPE : ∀ a' ∈ P, (a', b) ∈ E)
    (h : ∀ x : Fin (p + l) → Bool,
      (C.wires (List.ofFn x)).getD (p + l + j) false =
        decide (∃ a' ∈ P, x (Fin.castAdd l a') = true)) :
    Fin.castAdd l a ∈
      (charged (p + l) C (neighbours E (Fin.natAdd p b))).biUnion
        (singleSupport (p + l) C) := by
  classical
  let P' : Finset (Fin (p + l)) := P.image (Fin.castAdd l)
  have hsem : ∀ x : Fin (p + l) → Bool,
      PEqualNP.BlindGate.wireValue C (p + l) x (p + l + j) =
        decide (∃ i ∈ P', x i = true) := by
    intro x
    simpa [PEqualNP.BlindGate.wireValue, P'] using h x
  have hsub : P' ⊆ neighbours E (Fin.natAdd p b) := by
    intro i hi
    obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp hi
    rw [neighbours_right]
    exact Finset.mem_image.mpr ⟨a', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPE a' ha'⟩, rfl⟩
  have hcard' : 2 ≤ P'.card := by
    rw [show P'.card = P.card from Finset.card_image_of_injective P (fun _ _ h => left_inj h)]
    exact hcard
  apply Finset.mem_biUnion.mpr
  refine ⟨p + l + j, pure_or_mem_charged (p + l) C j P' _ hj hop hcard' hsub hsem, ?_⟩
  rw [pure_or_support (p + l) C (p + l + j) P' hsem]
  exact Finset.mem_image.mpr ⟨a, ha, rfl⟩

lemma posted_edge_or_bound (p l : ℕ) (E : Finset (Fin p × Fin l))
    (C : Circuit) (hAO : IsAO2 (p + l) C)
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (hbare : ∀ a b, (a, b) ∈ E →
      (∃ (j : ℕ) (Q : Finset (Fin l)), j < C.gates.length ∧
        (gateAt C j).op = GateOp.or ∧ 2 ≤ Q.card ∧ b ∈ Q ∧
        (∀ b' ∈ Q, (a, b') ∈ E) ∧
        ∀ x : Fin (p + l) → Bool,
          (C.wires (List.ofFn x)).getD (p + l + j) false =
            decide (∃ b' ∈ Q, x (Fin.natAdd p b') = true)) ∨
      (∃ (j : ℕ) (P : Finset (Fin p)), j < C.gates.length ∧
        (gateAt C j).op = GateOp.or ∧ 2 ≤ P.card ∧ a ∈ P ∧
        (∀ a' ∈ P, (a', b) ∈ E) ∧
        ∀ x : Fin (p + l) → Bool,
          (C.wires (List.ofFn x)).getD (p + l + j) false =
            decide (∃ a' ∈ P, x (Fin.castAdd l a') = true))) :
    E.card ≤ 2 * (orWires (p + l) C).card := by
  classical
  let U := fun c => (charged (p + l) C (neighbours E c)).biUnion (singleSupport (p + l) C)
  have hcover : ∀ a b, (a, b) ∈ E →
      Fin.natAdd p b ∈ U (Fin.castAdd l a) ∨ Fin.castAdd l a ∈ U (Fin.natAdd p b) := by
    intro a b he
    rcases hbare a b he with hleft | hright
    · obtain ⟨j, Q, hj, hop, hcard, hb, hQE, hsem⟩ := hleft
      exact Or.inl (left_witness_covered p l E C a b j Q hj hop hcard hb hQE hsem)
    · obtain ⟨j, P, hj, hop, hcard, ha, hPE, hsem⟩ := hright
      exact Or.inr (right_witness_covered p l E C a b j P hj hop hcard ha hPE hsem)
  have hsum := self_charged_family_budget (p + l) C hAO Finset.univ (neighbours E) (by
    intro a ha b hb hab
    exact neighbours_inter_card E hfour a b hab)
  exact (edge_card_le_support_sum p l E U hcover).trans hsum

end PEqualNP.Outside.L_meta_4970.EdgeSupport
