import Shield
import Neighbourhoods
import AppendPairs
import PairDecomposition

namespace PEqualNP.Outside.L_meta_4970_aux.Transfer

open PEqualNP.CircuitLowerBounds

def Posted : Prop :=
  ∀ (p l : ℕ) (E : Finset (Fin p × Fin l)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' → ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E)) → PEqualNP.TopForm.IsAO2 (p + l) C → (∀ x : Fin (p + l) → Bool, PEqualNP.MetaComplexity.circuitFun (p + l) C x = decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧ x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)) → PEqualNP.TwoColour.tCount (p + l) C (fun i => decide (p ≤ i)) = 0 → (∀ (a : Fin p) (b : Fin l), (a, b) ∈ E → (∃ (j : ℕ) (Q : Finset (Fin l)), j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 2 ≤ Q.card ∧ b ∈ Q ∧ (∀ b' ∈ Q, (a, b') ∈ E) ∧ ∀ x : Fin (p + l) → Bool, (C.wires (List.ofFn x)).getD (p + l + j) false = decide (∃ b' ∈ Q, x (Fin.natAdd p b') = true)) ∨ (∃ (j : ℕ) (P : Finset (Fin p)), j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 2 ≤ P.card ∧ a ∈ P ∧ (∀ a' ∈ P, (a', b) ∈ E) ∧ ∀ x : Fin (p + l) → Bool, (C.wires (List.ofFn x)).getD (p + l + j) false = decide (∃ a' ∈ P, x (Fin.castAdd l a') = true))) → ∃ S : Finset (Fin (p + l)), (∀ (a : Fin p) (b : Fin l), (a, b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧ E.card + S.card ≤ C.size + 1

def Computes {p l : Nat} (E : Finset (Fin p × Fin l)) (C : Circuit) : Prop :=
  ∀ x : Fin (p + l) → Bool, PEqualNP.MetaComplexity.circuitFun (p + l) C x =
    decide (∃ a b, (a, b) ∈ E ∧ x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)

def Covers {p l : Nat} (E : Finset (Fin p × Fin l)) (S : Finset (Fin (p + l))) : Prop :=
  ∀ a b, (a, b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S

def NoFour {p l : Nat} (E : Finset (Fin p × Fin l)) : Prop :=
  ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
    ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E)

theorem singleton_false {p l : Nat} {E : Finset (Fin p × Fin l)} {C : Circuit}
    (comp : Computes E C) (i : Fin (p + l)) :
    PEqualNP.MetaComplexity.circuitFun (p + l) C (fun k => decide (k = i)) = false := by
  rw [comp]
  apply Bool.eq_false_iff.mpr
  intro ht
  obtain ⟨a, b, -, ha, hb⟩ := of_decide_eq_true ht
  simp only [decide_eq_true_eq] at ha hb
  exact left_right_ne a b (ha.trans hb.symm)

theorem output_valid {p l : Nat} {E : Finset (Fin p × Fin l)} {C : Circuit}
    (hne : E.Nonempty) (comp : Computes E C) : C.output < p + l + C.gates.length := by
  obtain ⟨⟨a, b⟩, hab⟩ := hne
  have ht : PEqualNP.MetaComplexity.circuitFun (p + l) C (fun _ => true) = true := by
    rw [comp]
    exact decide_eq_true ⟨a, b, hab, rfl, rfl⟩
  by_contra hn
  rw [Shield.circuitFun_W] at ht
  have hz := Shield.W_ge C.gates (List.ofFn (fun _ : Fin (p + l) => true)) C.output
    (by simp; omega)
  rw [hz] at ht
  exact Bool.false_ne_true ht

theorem size_positive {p l : Nat} {E : Finset (Fin p × Fin l)} {C : Circuit}
    (hne : E.Nonempty) (comp : Computes E C) : 1 ≤ C.size := by
  have ho := output_valid hne comp
  by_contra hn
  have hg : C.gates = [] := by
    apply List.length_eq_zero_iff.mp
    change ¬ 1 ≤ C.gates.length at hn
    omega
  have hlt : C.output < p + l := by simpa [hg] using ho
  have hs := singleton_false comp (⟨C.output, hlt⟩ : Fin (p + l))
  rw [Shield.circuitFun_W, hg, Shield.W_nil, Shield.ofFn_getD _ _ hlt] at hs
  simp at hs

theorem transfer_pair_cost (posted : Posted) {p l : Nat}
    (E : Finset (Fin p × Fin l)) (C : Circuit) (hne : E.Nonempty) (hfour : NoFour E)
    (hC : PEqualNP.TopForm.IsAO2 (p + l) C) (comp : Computes E C)
    (pairs : List (AppendPair.Pair p l))
    (hv : AppendPair.PairValid E pairs) (hc : AppendPair.PairCovers E pairs) :
    ∃ S : Finset (Fin (p + l)), Covers E S ∧
      E.card + S.card + 3 ≤ 6 * C.size + pairs.length := by
  obtain ⟨D, hD, hcost, hfun, hzero⟩ :=
    Shield.main_aux p l C hC (size_positive hne comp) (singleton_false comp)
  have hDC : Computes E D := by
    intro x
    rw [hfun]
    exact comp x
  obtain ⟨F, hF, hFzero, hFsize, hFfun, hstars⟩ :=
    AppendPair.append_main hD hzero (output_valid hne hDC) pairs hv hc
  have hFC : Computes E F := by
    intro x
    rw [hFfun]
    exact hDC x
  obtain ⟨S, hS, hb⟩ := posted p l E F hfour hF hFC hFzero
    (fun a b hab => Or.inl (hstars a b hab))
  exact ⟨S, hS, by omega⟩

theorem posted_implies_general_bound (posted : Posted) {p l : Nat}
    (E : Finset (Fin p × Fin l)) (C : Circuit) (hne : E.Nonempty) (hfour : NoFour E)
    (hC : PEqualNP.TopForm.IsAO2 (p + l) C) (comp : Computes E C)
    (heven : ∀ a : Fin p, Even (PairDecomposition.row E a).card) :
    ∃ S : Finset (Fin (p + l)), Covers E S ∧
      E.card + 2 * S.card + 6 ≤ 12 * C.size := by
  obtain ⟨pairs, hlen, hv, hc⟩ := PairDecomposition.pairs_of_even_rows E heven
  obtain ⟨S, hS, hb⟩ := transfer_pair_cost posted E C hne hfour hC comp pairs hv hc
  exact ⟨S, hS, by omega⟩

theorem posted_implies_cover_bound (posted : Posted) {p l : Nat}
    (E : Finset (Fin p × Fin l)) (C : Circuit) (hne : E.Nonempty) (hfour : NoFour E)
    (hC : PEqualNP.TopForm.IsAO2 (p + l) C) (comp : Computes E C)
    (heven : ∀ a : Fin p, Even (PairDecomposition.row E a).card)
    (t : Nat) (ht : ∀ S : Finset (Fin (p + l)), Covers E S → t ≤ S.card) :
    E.card + 2 * t + 6 ≤ 12 * C.size := by
  obtain ⟨S, hS, hb⟩ := posted_implies_general_bound posted E C hne hfour hC comp heven
  have hlow := ht S hS
  omega

end PEqualNP.Outside.L_meta_4970_aux.Transfer
