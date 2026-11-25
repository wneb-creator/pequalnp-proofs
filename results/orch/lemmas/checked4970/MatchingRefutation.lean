import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4970.MatchingRefutation

open PEqualNP.CircuitLowerBounds

lemma matching_cover_card_le (p l : ℕ) (E M : Finset (Fin p × Fin l))
    (hME : M ⊆ E) (hleft : Set.InjOn Prod.fst (M : Set (Fin p × Fin l)))
    (hright : Set.InjOn Prod.snd (M : Set (Fin p × Fin l)))
    (S : Finset (Fin (p + l)))
    (hcover : ∀ (a : Fin p) (b : Fin l), (a, b) ∈ E →
      Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) : M.card ≤ S.card := by
  classical
  let pick (e : Fin p × Fin l) : Fin (p + l) :=
    if Fin.castAdd l e.1 ∈ S then Fin.castAdd l e.1 else Fin.natAdd p e.2
  have hmem : ∀ e ∈ M, pick e ∈ S := by
    intro e he
    have hc := hcover e.1 e.2 (hME he)
    dsimp only [pick]
    split_ifs with h
    · exact h
    · exact hc.resolve_left h
  have hinj : Set.InjOn pick (M : Set (Fin p × Fin l)) := by
    intro e he f hf hef
    by_cases heS : Fin.castAdd l e.1 ∈ S
    · by_cases hfS : Fin.castAdd l f.1 ∈ S
      · simp only [pick, heS, hfS, ↓reduceIte] at hef
        apply hleft he hf
        apply Fin.ext
        exact congrArg (fun z : Fin (p + l) => z.val) hef
      · simp only [pick, heS, hfS, ↓reduceIte] at hef
        have hv := congrArg (fun z : Fin (p + l) => z.val) hef
        have heLt := e.1.isLt
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
        omega
    · by_cases hfS : Fin.castAdd l f.1 ∈ S
      · simp only [pick, heS, hfS, ↓reduceIte] at hef
        have hv := congrArg (fun z : Fin (p + l) => z.val) hef
        have hfLt := f.1.isLt
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
        omega
      · simp only [pick, heS, hfS, ↓reduceIte] at hef
        apply hright he hf
        apply Fin.ext
        have hv := congrArg (fun z : Fin (p + l) => z.val) hef
        simp only [Fin.val_natAdd] at hv
        omega
  calc
    M.card = (M.image pick).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ S.card := Finset.card_le_card (by
      intro v hv
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hv
      exact hmem e he)

lemma no_cover_budget (p l : ℕ) (E M : Finset (Fin p × Fin l)) (C : Circuit)
    (hME : M ⊆ E) (hleft : Set.InjOn Prod.fst (M : Set (Fin p × Fin l)))
    (hright : Set.InjOn Prod.snd (M : Set (Fin p × Fin l)))
    (hsmall : C.size + 1 < E.card + M.card) :
    ¬ ∃ S : Finset (Fin (p + l)),
      (∀ (a : Fin p) (b : Fin l), (a, b) ∈ E →
        Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      E.card + S.card ≤ C.size + 1 := by
  rintro ⟨S, hcover, hbudget⟩
  have hm := matching_cover_card_le p l E M hME hleft hright S hcover
  omega

def postedStatement : Prop :=
  ∀ (p l : ℕ) (E : Finset (Fin p × Fin l)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' → ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E)) → PEqualNP.TopForm.IsAO2 (p + l) C → (∀ x : Fin (p + l) → Bool, PEqualNP.MetaComplexity.circuitFun (p + l) C x = decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧ x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)) → PEqualNP.TwoColour.tCount (p + l) C (fun i => decide (p ≤ i)) = 0 → (∀ (a : Fin p) (b : Fin l), (a, b) ∈ E → (∃ (j : ℕ) (Q : Finset (Fin l)), j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 2 ≤ Q.card ∧ b ∈ Q ∧ (∀ b' ∈ Q, (a, b') ∈ E) ∧ ∀ x : Fin (p + l) → Bool, (C.wires (List.ofFn x)).getD (p + l + j) false = decide (∃ b' ∈ Q, x (Fin.natAdd p b') = true)) ∨ (∃ (j : ℕ) (P : Finset (Fin p)), j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 2 ≤ P.card ∧ a ∈ P ∧ (∀ a' ∈ P, (a', b) ∈ E) ∧ ∀ x : Fin (p + l) → Bool, (C.wires (List.ofFn x)).getD (p + l + j) false = decide (∃ a' ∈ P, x (Fin.castAdd l a') = true))) → ∃ S : Finset (Fin (p + l)), (∀ (a : Fin p) (b : Fin l), (a, b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧ E.card + S.card ≤ C.size + 1

lemma conditional_refutation (p l : ℕ) (E M : Finset (Fin p × Fin l)) (C : Circuit)
    (hME : M ⊆ E) (hleft : Set.InjOn Prod.fst (M : Set (Fin p × Fin l)))
    (hright : Set.InjOn Prod.snd (M : Set (Fin p × Fin l)))
    (hfour : (∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' → ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E)))
    (hAO : PEqualNP.TopForm.IsAO2 (p + l) C)
    (hcompute : (∀ x : Fin (p + l) → Bool, PEqualNP.MetaComplexity.circuitFun (p + l) C x = decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧ x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)))
    (hzero : PEqualNP.TwoColour.tCount (p + l) C (fun i => decide (p ≤ i)) = 0)
    (hstars : (∀ (a : Fin p) (b : Fin l), (a, b) ∈ E → (∃ (j : ℕ) (Q : Finset (Fin l)), j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 2 ≤ Q.card ∧ b ∈ Q ∧ (∀ b' ∈ Q, (a, b') ∈ E) ∧ ∀ x : Fin (p + l) → Bool, (C.wires (List.ofFn x)).getD (p + l + j) false = decide (∃ b' ∈ Q, x (Fin.natAdd p b') = true)) ∨ (∃ (j : ℕ) (P : Finset (Fin p)), j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 2 ≤ P.card ∧ a ∈ P ∧ (∀ a' ∈ P, (a', b) ∈ E) ∧ ∀ x : Fin (p + l) → Bool, (C.wires (List.ofFn x)).getD (p + l + j) false = decide (∃ a' ∈ P, x (Fin.castAdd l a') = true))))
    (hsmall : C.size + 1 < E.card + M.card) : ¬ postedStatement := by
  intro hposted
  have hconclusion := hposted p l E C hfour hAO hcompute hzero hstars
  exact no_cover_budget p l E M C hME hleft hright hsmall hconclusion

end PEqualNP.Outside.L_meta_4970.MatchingRefutation
