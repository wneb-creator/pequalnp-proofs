import Mathlib.Data.Finset.Card
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4970

lemma star_centre_unique {p l : ℕ} {E : Finset (Fin p × Fin l)}
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {a a' : Fin p} {Q : Finset (Fin l)} (hQ : 2 ≤ Q.card)
    (ha : ∀ b ∈ Q, (a, b) ∈ E) (ha' : ∀ b ∈ Q, (a', b) ∈ E) : a = a' := by
  by_contra hne
  obtain ⟨b, hb, b', hb', hbb'⟩ := Finset.one_lt_card.mp
    (lt_of_lt_of_le (by decide : 1 < 2) hQ)
  exact hfour a a' b b' hne hbb' ⟨ha b hb, ha b' hb', ha' b hb, ha' b' hb'⟩

lemma reverse_star_centre_unique {p l : ℕ} {E : Finset (Fin p × Fin l)}
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {b b' : Fin l} {P : Finset (Fin p)} (hP : 2 ≤ P.card)
    (hb : ∀ a ∈ P, (a, b) ∈ E) (hb' : ∀ a ∈ P, (a, b') ∈ E) : b = b' := by
  by_contra hne
  obtain ⟨a, ha, a', ha', haa'⟩ := Finset.one_lt_card.mp
    (lt_of_lt_of_le (by decide : 1 < 2) hP)
  exact hfour a a' b b' haa' hne ⟨hb a ha, hb' a ha, hb a' ha', hb' a' ha'⟩

open PEqualNP.CircuitLowerBounds

def smallCircuit : Circuit :=
  ⟨[⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [6, 2]⟩,
    ⟨GateOp.or, [0, 7]⟩, ⟨GateOp.or, [8, 1]⟩,
    ⟨GateOp.and, [9, 4]⟩, ⟨GateOp.or, [7, 10]⟩,
    ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [0, 2]⟩], 11⟩

def smallEdges : Finset (Fin 3 × Fin 3) := {(0, 1), (1, 1), (2, 0), (2, 1)}

def smallGateValue (j : Fin 8) (x : Fin 6 → Bool) : Bool :=
  (smallCircuit.wires (List.ofFn x)).getD (6 + j.val) false

def smallSingletons (j : Fin 8) : Finset (Fin 6) :=
  Finset.univ.filter fun i => smallGateValue j (fun v => decide (v = i)) = true

lemma smallIsAO2 : PEqualNP.TopForm.IsAO2 6 smallCircuit := by decide +kernel

lemma smallAndCount : (smallCircuit.gates.countP fun g =>
    match g.op with | GateOp.and => true | _ => false) = 2 := by decide

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma smallNoTwoColour : PEqualNP.TwoColour.tCount 6 smallCircuit (fun i => decide (3 ≤ i)) = 0 := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma smallCorrect : ∀ x : Fin 6 → Bool, smallCircuit.eval (List.ofFn x) =
    decide (∃ a b : Fin 3, (a, b) ∈ smallEdges ∧
      x (Fin.castAdd 3 a) = true ∧ x (Fin.natAdd 3 b) = true) := by decide +kernel

lemma smallNoFourCycle : ∀ a a' b b' : Fin 3, a ≠ a' → b ≠ b' →
    ¬ ((a, b) ∈ smallEdges ∧ (a, b') ∈ smallEdges ∧
      (a', b) ∈ smallEdges ∧ (a', b') ∈ smallEdges) := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma smallPureRoots : ∀ j : Fin 8,
    ((match (PEqualNP.MetaComplexity.NestedCover.gateAt smallCircuit j.val).op with
        | GateOp.or => true | _ => false) = true ∧
      2 ≤ (smallSingletons j).card ∧ ∀ x : Fin 6 → Bool,
        smallGateValue j x = decide (∃ i ∈ smallSingletons j, x i = true)) ↔
    j = 0 ∨ j = 6 ∨ j = 7 := by decide +kernel

def smallRootEdges (j : Fin 8) : Finset (Fin 3 × Fin 3) :=
  if j = 0 then {(2, 0), (2, 1)}
  else if j = 6 then {(1, 1), (2, 1)}
  else if j = 7 then {(0, 1), (2, 1)}
  else ∅

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma smallRootCoverNeedsThree : ∀ R : Finset (Fin 8),
    smallEdges ⊆ R.biUnion smallRootEdges → 3 ≤ R.card := by decide +kernel

end PEqualNP.Outside.L_meta_4970
