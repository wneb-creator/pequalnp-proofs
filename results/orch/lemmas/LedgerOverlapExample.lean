import Mathlib
import PEqualNP.Defs

-- This example refutes only a proposed remaining-gate ledger.
-- It satisfies the posted lower bound, as checked below.

namespace PEqualNP.Outside.L_meta_4970_aux

open PEqualNP.CircuitLowerBounds

private def overlapExample : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [3, 5]⟩,
    ⟨.and, [4, 6]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [3, 4]⟩], 9⟩

private def overlapEdges : Finset (Fin 3 × Fin 2) :=
  {(0, 0), (1, 0), (1, 1), (2, 1)}

lemma overlapExample_valid : PEqualNP.TopForm.IsAO2 5 overlapExample := by decide

lemma overlapExample_eval : ∀ x : Fin 5 → Bool,
    PEqualNP.MetaComplexity.circuitFun 5 overlapExample x =
      decide (∃ a : Fin 3, ∃ b : Fin 2, (a, b) ∈ overlapEdges ∧
        x (Fin.castAdd 2 a) = true ∧ x (Fin.natAdd 3 b) = true) := by decide

lemma overlapExample_tCount :
    PEqualNP.TwoColour.tCount 5 overlapExample (fun i => decide (3 ≤ i)) = 0 := by decide

lemma overlapExample_coverLower : ∀ S : Finset (Fin 5),
    (∀ (a : Fin 3) (b : Fin 2), (a, b) ∈ overlapEdges →
      Fin.castAdd 2 a ∈ S ∨ Fin.natAdd 3 b ∈ S) → 2 ≤ S.card := by decide

lemma overlapExample_roots : ∀ x : Fin 5 → Bool,
    (overlapExample.wires (List.ofFn x)).getD 5 false = (x 0 || x 1) ∧
    (overlapExample.wires (List.ofFn x)).getD 6 false = (x 1 || x 2) ∧
    (overlapExample.wires (List.ofFn x)).getD 10 false = (x 3 || x 4) := by decide

lemma overlapExample_budget : overlapExample.size = 6 ∧ overlapEdges.card = 4 ∧
    6 - 3 < 3 + 2 - 1 := by decide

private def overlapCentre : Fin 3 → Fin 5 := ![3, 4, 1]

private def overlapLeaves : Fin 3 → Finset (Fin 5) := ![{0, 1}, {1, 2}, {3, 4}]

private def overlapWire : Fin 3 → ℕ := ![5, 6, 10]

private def overlapSupport (w : ℕ) : Finset (Fin 5) :=
  Finset.univ.filter fun p =>
    (overlapExample.wires (List.ofFn (fun q : Fin 5 => decide (q = p)))).getD w false = true

private def overlapOwnedFlag (w : ℕ) : Bool :=
    match (PEqualNP.MetaComplexity.NestedCover.gateAt overlapExample (w - 5)).op with
    | .or => decide (∃ i : Fin 3, overlapSupport w ⊆ overlapLeaves i ∧
        2 ≤ (overlapSupport w).card)
    | _ => false

private def overlapOwnedOr : Finset ℕ :=
  (Finset.Ico 5 (5 + overlapExample.size)).filter fun w => overlapOwnedFlag w = true

private def overlapChosenWires : Finset ℕ := Finset.univ.image overlapWire

lemma overlapExample_noFourCycle : ∀ (a a' : Fin 3) (b b' : Fin 2),
    a ≠ a' → b ≠ b' → ¬ ((a, b) ∈ overlapEdges ∧ (a, b') ∈ overlapEdges ∧
      (a', b) ∈ overlapEdges ∧ (a', b') ∈ overlapEdges) := by decide

lemma overlapExample_witnessPure : ∀ (i : Fin 3) (x : Fin 5 → Bool),
    (overlapExample.wires (List.ofFn x)).getD (overlapWire i) false =
      decide (∃ p ∈ overlapLeaves i, x p = true) := by decide

lemma overlapExample_witnessGates : ∀ i : Fin 3,
    5 ≤ overlapWire i ∧ overlapWire i < 5 + overlapExample.size ∧
    (PEqualNP.MetaComplexity.NestedCover.gateAt overlapExample (overlapWire i - 5)).op =
      GateOp.or := by
  let _ : DecidableEq GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  decide

lemma overlapExample_witnessStars : ∀ (i : Fin 3), (overlapLeaves i).card = 2 ∧
    ∀ v ∈ overlapLeaves i, ∃ (a : Fin 3) (b : Fin 2), (a, b) ∈ overlapEdges ∧
      ((overlapCentre i = Fin.castAdd 2 a ∧ v = Fin.natAdd 3 b) ∨
        (overlapCentre i = Fin.natAdd 3 b ∧ v = Fin.castAdd 2 a)) := by decide

lemma overlapExample_witnessCover : ∀ (a : Fin 3) (b : Fin 2), (a, b) ∈ overlapEdges →
    ∃ i : Fin 3,
      (overlapCentre i = Fin.castAdd 2 a ∧ Fin.natAdd 3 b ∈ overlapLeaves i) ∨
      (overlapCentre i = Fin.natAdd 3 b ∧ Fin.castAdd 2 a ∈ overlapLeaves i) := by decide

lemma overlapExample_counts : overlapOwnedOr = {5, 6, 10} ∧
    overlapChosenWires = {5, 6, 10} ∧
    (∑ i : Fin 3, (overlapLeaves i).card) = 6 := by decide

lemma overlapExample_naiveLedgerFails :
    ¬ (overlapChosenWires.card + 2 ≤ overlapExample.size - overlapOwnedOr.card + 1) := by decide

lemma overlapExample_fullBoundHolds : ∃ S : Finset (Fin 5),
    (∀ (a : Fin 3) (b : Fin 2), (a, b) ∈ overlapEdges →
      Fin.castAdd 2 a ∈ S ∨ Fin.natAdd 3 b ∈ S) ∧
    S.card = 2 ∧ overlapEdges.card + S.card ≤ overlapExample.size + 1 := by
  refine ⟨{3, 4}, ?_⟩
  decide

end PEqualNP.Outside.L_meta_4970_aux
