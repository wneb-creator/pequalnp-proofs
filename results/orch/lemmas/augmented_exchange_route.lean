import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1772_aux.augmented

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

abbrev graph : SimpleGraph (Fin 12) := edgeGraph 12
  [(0,1),(2,3),(0,4),(2,4),(0,5),(3,5),(1,6),(2,6),(1,7),(3,7),
   (4,8),(5,9),(6,10),(7,11)]

def hybrid : Circuit := ⟨[
  ⟨.or,[0,2]⟩, ⟨.or,[0,3]⟩, ⟨.or,[1,2]⟩, ⟨.or,[1,3]⟩,
  ⟨.and,[12,13]⟩, ⟨.and,[14,15]⟩, ⟨.and,[16,17]⟩,
  ⟨.or,[12,8]⟩, ⟨.and,[4,19]⟩,
  ⟨.or,[13,9]⟩, ⟨.and,[5,21]⟩,
  ⟨.or,[14,10]⟩, ⟨.and,[6,23]⟩,
  ⟨.or,[15,11]⟩, ⟨.and,[7,25]⟩,
  ⟨.or,[18,20]⟩, ⟨.or,[27,22]⟩, ⟨.or,[28,24]⟩, ⟨.or,[29,26]⟩],30⟩

def repaired : Circuit := ⟨[
  ⟨.or,[0,2]⟩, ⟨.or,[0,3]⟩, ⟨.or,[1,2]⟩, ⟨.or,[1,3]⟩,
  ⟨.and,[0,1]⟩, ⟨.and,[2,3]⟩, ⟨.or,[16,17]⟩,
  ⟨.or,[12,8]⟩, ⟨.and,[4,19]⟩,
  ⟨.or,[13,9]⟩, ⟨.and,[5,21]⟩,
  ⟨.or,[14,10]⟩, ⟨.and,[6,23]⟩,
  ⟨.or,[15,11]⟩, ⟨.and,[7,25]⟩,
  ⟨.or,[18,20]⟩, ⟨.or,[27,22]⟩, ⟨.or,[28,24]⟩, ⟨.or,[29,26]⟩],30⟩

lemma hybrid_size : hybrid.size = 19 := rfl
lemma repaired_size : repaired.size = hybrid.size := rfl

lemma hybrid_mono : Monotone2 hybrid := by
  simp [Monotone2, hybrid]

lemma repaired_mono : Monotone2 repaired := by
  simp [Monotone2, repaired]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma triangle_free : ∀ a b c : Fin 12,
    graph.Adj a b → graph.Adj b c → ¬ graph.Adj c a := by
  intro a b c hab hbc hca
  fin_cases a <;> simp [graph, edgeGraph] at hab hbc hca <;> omega

def neighbors (a : Fin 12) : Finset (Fin 12) :=
  ![{1,4,5}, {0,6,7}, {3,4,6}, {2,5,7}, {0,2,8}, {0,3,9},
    {1,2,10}, {1,3,11}, {4}, {5}, {6}, {7}] a

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma adj_iff_neighbors (a b : Fin 12) : graph.Adj a b ↔ b ∈ neighbors a := by
  fin_cases a <;> fin_cases b <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma no_four : PEqualNP.TopForm.NoFourCycle graph := by
  intro a b hab
  have he : (Finset.univ.filter fun w => graph.Adj a w ∧ graph.Adj b w) =
      neighbors a ∩ neighbors b := by
    ext w
    simp [adj_iff_neighbors]
  rw [he]
  fin_cases a <;> fin_cases b <;> first | exact (hab rfl).elim | decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma hybrid_singletons :
    gateVal 12 hybrid 4 (pairInput (0 : Fin 12) 0) = true ∧
    gateVal 12 hybrid 5 (pairInput (1 : Fin 12) 1) = true := by
  constructor <;> rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma hybrid_unowned : (gateAt hybrid 6).op = GateOp.and ∧
    ∀ u v : Fin 12, graph.Adj u v → ¬ Owns 12 hybrid 6 u v := by
  refine ⟨rfl, ?_⟩
  intro u v _ ho
  have h4 := ho.2.2.2 4 (by decide) (by decide) rfl
  have h6 := ho.2.2.1
  have hv (x : Fin 12 → Bool) : gateVal 12 hybrid 6 x =
      (gateVal 12 hybrid 4 x && gateVal 12 hybrid 5 x) := by
    simp [gateVal, hybrid, Circuit.wires, GateOp.eval, List.ofFn_succ]
  rw [hv, h4] at h6
  cases h6

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma repaired_owned (j : ℕ) (u v : Fin 12) (hj : j < repaired.gates.length)
    (ha : (gateAt repaired j).op = GateOp.and)
    (hv : gateVal 12 repaired j (pairInput u v) = true) : Owns 12 repaired j u v := by
  refine ⟨hj, ha, hv, ?_⟩
  intro i hi hic hia
  have hbound : j ≤ 18 := by change j < 19 at hj; omega
  interval_cases j <;> simp [repaired, gateAt] at ha
  · change i ∈ ([] : List ℕ) at hic
    simp at hic
  · change i ∈ ([] : List ℕ) at hic
    simp at hic
  · change i ∈ [7,0] at hic
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hic
    rcases hic with rfl | rfl <;> cases hia
  · change i ∈ [9,1] at hic
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hic
    rcases hic with rfl | rfl <;> cases hia
  · change i ∈ [11,2] at hic
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hic
    rcases hic with rfl | rfl <;> cases hia
  · change i ∈ [13,3] at hic
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hic
    rcases hic with rfl | rfl <;> cases hia

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma repaired_ownership : ∀ j < repaired.gates.length,
    (gateAt repaired j).op = GateOp.and →
      ∃ u v : Fin 12, graph.Adj u v ∧ Owns 12 repaired j u v := by
  intro j hj ha
  apply (show (∃ u v : Fin 12, graph.Adj u v ∧ gateVal 12 repaired j (pairInput u v) = true) →
      ∃ u v : Fin 12, graph.Adj u v ∧ Owns 12 repaired j u v from ?_) ?_
  · rintro ⟨u,v,huv,hval⟩
    exact ⟨u,v,huv,repaired_owned j u v hj ha hval⟩
  · have hbound : j ≤ 18 := by change j < 19 at hj; omega
    interval_cases j <;> simp [repaired, gateAt] at ha
    · exact ⟨0, 1, by decide +kernel, rfl⟩
    · exact ⟨2, 3, by decide +kernel, rfl⟩
    · exact ⟨4, 8, by decide +kernel, rfl⟩
    · exact ⟨5, 9, by decide +kernel, rfl⟩
    · exact ⟨6, 10, by decide +kernel, rfl⟩
    · exact ⟨7, 11, by decide +kernel, rfl⟩

def formula (x : Fin 12 → Bool) : Bool :=
  ((((x 0 && x 1 || x 2 && x 3) || (x 4 && ((x 0 || x 2) || x 8))) ||
    (x 5 && ((x 0 || x 3) || x 9))) || (x 6 && ((x 1 || x 2) || x 10))) ||
    (x 7 && ((x 1 || x 3) || x 11))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma graph_formula (x : Fin 12 → Bool) : graphFun graph ∅ x = formula x := by
  simp [graphFun, adj_iff_neighbors, neighbors, Fin.exists_fin_succ, formula]
  generalize x 0 = b0, x 1 = b1, x 2 = b2, x 3 = b3, x 4 = b4, x 5 = b5,
    x 6 = b6, x 7 = b7, x 8 = b8, x 9 = b9, x 10 = b10, x 11 = b11
  simp [Bool.and_or_distrib_left, Bool.and_comm, Bool.or_comm, Bool.or_left_comm]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma hybrid_computes : circuitFun 12 hybrid = graphFun graph ∅ := by
  funext x
  rw [graph_formula]
  simp [circuitFun, hybrid, Circuit.eval, Circuit.wires, GateOp.eval, List.ofFn_succ, formula]
  generalize x 0 = b0, x 1 = b1, x 2 = b2, x 3 = b3, x 4 = b4, x 5 = b5,
    x 6 = b6, x 7 = b7, x 8 = b8, x 9 = b9, x 10 = b10, x 11 = b11
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> simp

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma repaired_computes : circuitFun 12 repaired = graphFun graph ∅ := by
  funext x
  rw [graph_formula]
  simp [circuitFun, repaired, Circuit.eval, Circuit.wires, GateOp.eval, List.ofFn_succ, formula]

end PEqualNP.Outside.L_meta_1772_aux.augmented
