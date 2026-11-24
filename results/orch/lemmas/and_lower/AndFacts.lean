import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_670_aux.AndLower

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def target (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
  (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

private def graph : SimpleGraph (Fin 9) := SimpleGraph.fromRel fun a b =>
  (a.val, b.val) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5),
    (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)] : List (Nat × Nat))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxSize 10000 in
private theorem square_free : ∀ a b c d : Fin 9, a ≠ c → b ≠ d →
    ¬ (graph.Adj a b ∧ graph.Adj b c ∧ graph.Adj c d ∧ graph.Adj d a) := by
  simp only [graph, SimpleGraph.fromRel_adj]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxSize 10000 in
private theorem cover_five : ∀ S : Finset (Fin 9),
    (∀ u v : Fin 9, graph.Adj u v → u ∈ S ∨ v ∈ S) → 5 ≤ S.card := by
  simp only [graph, SimpleGraph.fromRel_adj]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxSize 10000 in
private theorem target_graph : ∀ x : Fin 9 → Bool,
    target x = true ↔ ∃ u v : Fin 9, graph.Adj u v ∧ x u = true ∧ x v = true := by
  simp only [graph, target, SimpleGraph.fromRel_adj]
  decide +kernel

private def isAndGate (g : Gate) : Bool :=
  @decide (g.op = GateOp.and) (PEqualNP.MetaComplexity.NestedCover.gateOpDecEq g.op GateOp.and)

private def andIndices : List Gate → Finset Nat
  | [] => ∅
  | g :: gs => if isAndGate g then
      insert 0 ((andIndices gs).image Nat.succ)
    else (andIndices gs).image Nat.succ

private theorem andIndices_mem (gs : List Gate) (j : Nat) (g : Gate)
    (hj : gs[j]? = some g) (hg : g.op = GateOp.and) : j ∈ andIndices gs := by
  induction gs generalizing j with
  | nil => simp at hj
  | cons a gs ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst a
      simp [andIndices, isAndGate, hg]
    | succ j =>
      have hj' : gs[j]? = some g := by simpa using hj
      have hm : j + 1 ∈ (andIndices gs).image Nat.succ :=
        Finset.mem_image.mpr ⟨j, ih j hj', rfl⟩
      simp only [andIndices]
      split
      · exact Finset.mem_insert_of_mem hm
      · exact hm

private theorem andIndices_card (gs : List Gate) :
    (andIndices gs).card = (gs.filter isAndGate).length := by
  classical
  induction gs with
  | nil => simp [andIndices]
  | cons g gs ih =>
    have hz : 0 ∉ (andIndices gs).image Nat.succ := by simp
    have hi : ((andIndices gs).image Nat.succ).card = (andIndices gs).card :=
      Finset.card_image_of_injective _ Nat.succ_injective
    by_cases hg : g.op = GateOp.and
    · simp [andIndices, isAndGate, hg, hz, hi, ih]
    · simp [andIndices, isAndGate, hg, hi, ih]

private theorem specialized (generic_and_lower : ∀ (n t : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), t ≤ 5 → (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → (∀ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S) → t ≤ S.card) → PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → ∀ A : Finset ℕ, (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A) → t ≤ A.card) (C : Circuit) (hm : Monotone2 C)
    (hf : circuitFun 9 C = target) : 5 ≤ PEqualNP.ReadTwo.nAnd C := by
  have hc : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 9, graph.Adj u v ∧ x u = true ∧ x v = true := by
    intro x
    have hx : C.eval (List.ofFn x) = target x := congrFun hf x
    rw [hx]
    exact target_graph x
  have h := generic_and_lower 9 5 graph C (by decide) square_free cover_five hm hc
    (andIndices C.gates) (andIndices_mem C.gates)
  rw [andIndices_card] at h
  have heq : (C.gates.filter isAndGate).length = PEqualNP.ReadTwo.nAnd C := by
    unfold PEqualNP.ReadTwo.nAnd
    congr 1
  rw [heq] at h
  exact h

end PEqualNP.Outside.L_meta_670_aux.AndLower
