import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1031.TwoJunk

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

lemma rectangle_exhausted {α : Type*} [DecidableEq α] (G : SimpleGraph α)
    (h4 : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (A B : Finset α) {a b : α} (ha : a ∈ A) (hb : b ∈ B)
    (hrow : ∀ v ∈ B, G.Adj a v) (hcol : ∀ u ∈ A, G.Adj u b) :
    ∀ u ∈ A, ∀ v ∈ B, G.Adj u v → u = a ∨ v = b := by
  intro u hu v hv huv
  exact (h4 a b u v (hrow b hb) (hcol u hu).symm huv (hrow v hv).symm).imp
    Eq.symm Eq.symm

lemma rectangle_edge_function {α : Type*} [DecidableEq α] (G : SimpleGraph α)
    (h4 : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (A B : Finset α) {a b : α} (ha : a ∈ A) (hb : b ∈ B)
    (hrow : ∀ v ∈ B, G.Adj a v) (hcol : ∀ u ∈ A, G.Adj u b)
    (x : α → Bool) :
    (∃ u ∈ A, ∃ v ∈ B, G.Adj u v ∧ x u = true ∧ x v = true) ↔
      (x a = true ∧ ∃ v ∈ B, x v = true) ∨
      (x b = true ∧ ∃ u ∈ A, x u = true) := by
  constructor
  · rintro ⟨u, hu, v, hv, huv, hxu, hxv⟩
    rcases rectangle_exhausted G h4 A B ha hb hrow hcol u hu v hv huv with rfl | rfl
    · exact Or.inl ⟨hxu, v, hv, hxv⟩
    · exact Or.inr ⟨hxv, u, hu, hxu⟩
  · rintro (⟨ha', v, hv, hv'⟩ | ⟨hb', u, hu, hu'⟩)
    · exact ⟨a, ha, v, hv, hrow v hv, ha', hv'⟩
    · exact ⟨u, hu, b, hb, hcol u hu, hu', hb'⟩

abbrev pathFour : SimpleGraph (Fin 4) := edgeGraph 4 [(0, 1), (1, 2), (2, 3)]

def branchingTwoJunk : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.or, [1, 3]⟩, ⟨.and, [4, 5]⟩,
    ⟨.or, [0, 3]⟩, ⟨.and, [6, 7]⟩, ⟨.and, [6, 1]⟩,
    ⟨.and, [8, 2]⟩, ⟨.or, [9, 10]⟩], 11⟩

def pathFourSmall : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.and, [1, 4]⟩, ⟨.and, [2, 3]⟩,
    ⟨.or, [5, 6]⟩], 7⟩

lemma pathFour_girth :
    (∀ a b c : Fin 4, pathFour.Adj a b → pathFour.Adj b c → ¬ pathFour.Adj c a) ∧
      PEqualNP.TopForm.NoFourCycle pathFour := by
  decide

lemma branchingTwoJunk_legal : PEqualNP.TopForm.IsAO2 4 branchingTwoJunk := by
  decide

lemma branchingTwoJunk_correct :
    ∀ x : Fin 4 → Bool, circuitFun 4 branchingTwoJunk x = graphFun pathFour ∅ x := by
  decide

lemma branchingTwoJunk_top : PEqualNP.TopForm.TopForm pathFour branchingTwoJunk := by
  decide

lemma branchingTwoJunk_junk : PEqualNP.TopForm.junk pathFour branchingTwoJunk = {2, 4} := by
  decide

lemma branchingTwoJunk_pivotal : ∀ j : Fin 8, ∃ u v : Fin 4, pathFour.Adj u v ∧
    circuitFun 4 ⟨branchingTwoJunk.gates.set j.val ⟨.or, []⟩, branchingTwoJunk.output⟩
      (pairInput u v) = false := by
  decide

lemma branchingTwoJunk_two_readers : PEqualNP.TopForm.readers 4 branchingTwoJunk 2 = {4, 5} := by
  decide

lemma branchingTwoJunk_not_single_reader :
    ¬ (∀ k < branchingTwoJunk.gates.length,
      4 + 2 ∈ (gateAt branchingTwoJunk k).inputs → k = 4) := by
  intro h
  have hf := h 5 (by decide) (by decide)
  omega

lemma pathFourSmall_legal : PEqualNP.TopForm.IsAO2 4 pathFourSmall := by
  decide

lemma pathFourSmall_correct : circuitFun 4 pathFourSmall = graphFun pathFour ∅ := by
  funext x
  revert x
  decide

lemma branchingTwoJunk_not_least : ¬ PEqualNP.TopForm.IsLeastAO pathFour branchingTwoJunk := by
  intro h
  have hs := h.2.2 pathFourSmall pathFourSmall_legal pathFourSmall_correct
  norm_num [Circuit.size, branchingTwoJunk, pathFourSmall] at hs

lemma branchingTwoJunk_lift_fixed :
    PEqualNP.Core.IsLiftFixedPoint pathFour branchingTwoJunk := by
  decide

lemma branchingTwoJunk_all_used : ∀ j < branchingTwoJunk.gates.length,
    PEqualNP.Core.InOutputCone 4 branchingTwoJunk j := by
  decide

lemma branchingTwoJunk_no_sound_operand : ∀ j < branchingTwoJunk.gates.length,
    (gateAt branchingTwoJunk j).op = GateOp.and →
      ∀ w ∈ (gateAt branchingTwoJunk j).inputs,
        ¬ (∀ x : Fin 4 → Bool,
          Circuit.eval ⟨branchingTwoJunk.gates, w⟩ (List.ofFn x) = true →
            graphFun pathFour ∅ x = true) := by
  intro j hj
  have hj8 : j < 8 := hj
  interval_cases j <;> norm_num [branchingTwoJunk, gateAt] <;> decide

lemma branchingTwoJunk_second_readers_literal : ∀ k < branchingTwoJunk.gates.length,
    k ≠ 4 → (gateAt branchingTwoJunk k).op = GateOp.and → ∀ i : Fin 2,
      PEqualNP.CleanedNonEdge.OrReaches 4 branchingTwoJunk
        (PEqualNP.TopForm.opnd branchingTwoJunk k i) 4 →
      PEqualNP.TopForm.BelowF pathFour branchingTwoJunk k ∧
        PEqualNP.TopForm.opnd branchingTwoJunk k (1 - i) < 4 := by
  intro k hk hne hop i hr
  have hk8 : k < 8 := hk
  interval_cases k <;> fin_cases i
  all_goals first
    | exact ⟨by decide, by decide⟩
    | (exfalso; revert hr; decide)
    | (exfalso; revert hop; decide)
    | (exfalso; exact hne rfl)

end PEqualNP.Outside.L_meta_1031.TwoJunk
