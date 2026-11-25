import PEqualNP.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace PEqualNP.Outside.L_meta_4675_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def thetaEdges : Finset (Fin 8 × Fin 8) :=
  {(0, 4), (0, 5), (0, 6), (1, 4), (1, 7), (2, 5), (2, 7), (3, 6), (3, 7)}

def thetaAdj (u v : Fin 8) : Prop := (u, v) ∈ thetaEdges ∨ (v, u) ∈ thetaEdges

instance (u v : Fin 8) : Decidable (thetaAdj u v) := by
  unfold thetaAdj
  infer_instance

def maskedTheta : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [8, 2]⟩, ⟨.or, [9, 3]⟩,
    ⟨.or, [4, 5]⟩, ⟨.or, [11, 6]⟩, ⟨.or, [12, 7]⟩,
    ⟨.and, [0, 13]⟩, ⟨.and, [1, 13]⟩, ⟨.and, [2, 13]⟩, ⟨.and, [3, 13]⟩,
    ⟨.and, [10, 4]⟩, ⟨.and, [10, 5]⟩, ⟨.and, [10, 6]⟩, ⟨.and, [10, 7]⟩,
    ⟨.or, [18, 19]⟩, ⟨.or, [22, 20]⟩, ⟨.and, [14, 23]⟩,
    ⟨.or, [18, 21]⟩, ⟨.and, [15, 25]⟩,
    ⟨.or, [19, 21]⟩, ⟨.and, [16, 27]⟩,
    ⟨.or, [20, 21]⟩, ⟨.and, [17, 29]⟩,
    ⟨.or, [24, 26]⟩, ⟨.or, [31, 28]⟩, ⟨.or, [32, 30]⟩], 33⟩

def thetaSupport (w : ℕ) : Finset (Fin 8) :=
  Finset.univ.filter fun u =>
    (maskedTheta.wires (List.ofFn fun v : Fin 8 => decide (v = u))).getD w false = true

def thetaStar (c : Fin 8) (w : ℕ) : Finset (Fin 8 × Fin 8) :=
  thetaEdges.filter fun e =>
    (c = e.1 ∧ e.2 ∈ thetaSupport w) ∨ (c = e.2 ∧ e.1 ∈ thetaSupport w)

lemma theta_card : thetaEdges.card = 9 := by decide

lemma theta_no_four_cycle : ∀ a a' b b' : Fin 8,
    a ≠ a' → b ≠ b' →
    ¬ ((a, b) ∈ thetaEdges ∧ (a, b') ∈ thetaEdges ∧
      (a', b) ∈ thetaEdges ∧ (a', b') ∈ thetaEdges) := by decide

lemma maskedTheta_ao : PEqualNP.TopForm.IsAO2 8 maskedTheta := by decide

lemma maskedTheta_computes : ∀ x : Fin 8 → Bool,
    maskedTheta.eval (List.ofFn x) =
      decide (∃ e ∈ thetaEdges, x e.1 = true ∧ x e.2 = true) := by decide

lemma maskedTheta_tCount :
    PEqualNP.TwoColour.tCount 8 maskedTheta (fun i => decide (4 ≤ i)) = 0 := by decide

lemma maskedTheta_and_singletons : ∀ k : Fin 26,
    (gateAt maskedTheta k).op = GateOp.and → thetaSupport (8 + k.val) = ∅ := by
  letI : DecidableEq GateOp := gateOpDecEq
  decide

lemma maskedTheta_safe_slot : ∀ (k : Fin 26) (w : Fin 34) (c : Fin 8),
    (gateAt maskedTheta k).op = GateOp.and →
    w.val ∈ (gateAt maskedTheta k).inputs →
    (thetaSupport w).Nonempty →
    (∀ u ∈ thetaSupport w, thetaAdj c u) → k.val = 6 + w.val ∧ w.val < 8 := by
  letI : DecidableEq GateOp := gateOpDecEq
  decide

lemma theta_input_star_card : ∀ (c u : Fin 8), (thetaStar c u.val).card ≤ 1 := by decide

lemma theta_eight_stars_insufficient (choose : Fin 8 → Fin 8) :
    ¬ thetaEdges ⊆ Finset.univ.biUnion (fun u : Fin 8 => thetaStar (choose u) u.val) := by
  intro hsub
  have hsum : (∑ u : Fin 8, (thetaStar (choose u) u.val).card) ≤ 8 := by
    calc
      _ ≤ ∑ _u : Fin 8, 1 := Finset.sum_le_sum fun u _ => theta_input_star_card (choose u) u
      _ = _ := by simp
  have hcard := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  rw [theta_card] at hcard
  omega

end PEqualNP.Outside.L_meta_4675_aux
