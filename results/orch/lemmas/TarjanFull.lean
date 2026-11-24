import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3678

def tarjanCircuit : PEqualNP.CircuitLowerBounds.Circuit :=
  { gates := [
      ⟨.or, [5, 3]⟩,
      ⟨.or, [6, 4]⟩,
      ⟨.or, [7, 3]⟩,
      ⟨.or, [8, 4]⟩,
      ⟨.or, [0, 3]⟩,
      ⟨.or, [43, 1]⟩,
      ⟨.or, [44, 2]⟩,
      ⟨.or, [0, 4]⟩,
      ⟨.or, [46, 1]⟩,
      ⟨.or, [47, 2]⟩,
      ⟨.and, [45, 48]⟩,
      ⟨.or, [49, 9]⟩,
      ⟨.or, [49, 10]⟩,
      ⟨.or, [39, 50]⟩,
      ⟨.or, [40, 50]⟩,
      ⟨.or, [41, 51]⟩,
      ⟨.or, [42, 51]⟩,
      ⟨.or, [39, 11]⟩,
      ⟨.or, [40, 12]⟩,
      ⟨.or, [41, 13]⟩,
      ⟨.or, [42, 14]⟩,
      ⟨.or, [43, 15]⟩,
      ⟨.or, [44, 16]⟩,
      ⟨.or, [45, 17]⟩,
      ⟨.or, [46, 18]⟩,
      ⟨.or, [47, 19]⟩,
      ⟨.or, [48, 20]⟩,
      ⟨.or, [52, 21]⟩,
      ⟨.or, [53, 22]⟩,
      ⟨.or, [54, 23]⟩,
      ⟨.or, [55, 24]⟩,
      ⟨.and, [56, 25]⟩,
      ⟨.and, [57, 26]⟩,
      ⟨.and, [58, 27]⟩,
      ⟨.and, [59, 28]⟩,
      ⟨.and, [60, 29]⟩,
      ⟨.and, [61, 30]⟩,
      ⟨.and, [62, 31]⟩,
      ⟨.and, [63, 32]⟩,
      ⟨.and, [64, 33]⟩,
      ⟨.and, [65, 34]⟩,
      ⟨.and, [66, 35]⟩,
      ⟨.and, [67, 36]⟩,
      ⟨.and, [68, 37]⟩,
      ⟨.and, [69, 38]⟩,
      ⟨.or, [70, 71]⟩,
      ⟨.or, [84, 72]⟩,
      ⟨.or, [85, 73]⟩,
      ⟨.or, [86, 74]⟩,
      ⟨.or, [87, 75]⟩,
      ⟨.or, [88, 76]⟩,
      ⟨.or, [89, 77]⟩,
      ⟨.or, [90, 78]⟩,
      ⟨.or, [91, 79]⟩,
      ⟨.or, [92, 80]⟩,
      ⟨.or, [93, 81]⟩,
      ⟨.or, [94, 82]⟩,
      ⟨.or, [95, 83]⟩
    ]
    output := 96 }

def tarjanEdges : List (ℕ × ℕ) :=
  [(3, 25), (5, 25), (11, 25), (4, 26), (6, 26), (12, 26), (3, 27), (7, 27), (13, 27), (4, 28), (8, 28), (14, 28), (0, 29), (3, 29), (15, 29), (0, 30), (1, 30), (3, 30), (16, 30), (0, 31), (1, 31), (2, 31), (3, 31), (17, 31), (0, 32), (4, 32), (18, 32), (0, 33), (1, 33), (4, 33), (19, 33), (0, 34), (1, 34), (2, 34), (4, 34), (20, 34), (0, 35), (1, 35), (2, 35), (3, 35), (5, 35), (9, 35), (21, 35), (0, 36), (1, 36), (2, 36), (4, 36), (6, 36), (9, 36), (22, 36), (0, 37), (1, 37), (2, 37), (3, 37), (7, 37), (10, 37), (23, 37), (0, 38), (1, 38), (2, 38), (4, 38), (8, 38), (10, 38), (24, 38)]

abbrev tarjanGraph : SimpleGraph (Fin 39) := PEqualNP.EdgeOwnership.edgeGraph 39 tarjanEdges

lemma tarjan_size : tarjanCircuit.size = 58 := by decide

lemma tarjan_ao2 : PEqualNP.TopForm.IsAO2 39 tarjanCircuit := by decide

lemma tarjan_bipartite : ∀ u v : Fin 39, tarjanGraph.Adj u v →
    decide (u.val < 25) ≠ decide (v.val < 25) := by
  have he : ∀ e ∈ tarjanEdges, e.1 < 25 ∧ 25 ≤ e.2 := by decide
  intro u v h
  rcases h.2 with h | h
  · obtain ⟨hu, hv⟩ := he (u.val, v.val) h
    simp [hu, Nat.not_lt.mpr hv]
  · obtain ⟨hv, hu⟩ := he (v.val, u.val) h
    simp [hv, Nat.not_lt.mpr hu]

lemma graphFun_edgeGraph_list (n : ℕ) (edges : List (ℕ × ℕ))
    (he : ∀ e ∈ edges, e.1 < n ∧ e.2 < n ∧ e.1 ≠ e.2)
    (x : Fin n → Bool) :
    PEqualNP.MetaComplexity.NestedCover.graphFun (PEqualNP.EdgeOwnership.edgeGraph n edges) ∅ x =
      edges.any (fun e => (List.ofFn x).getD e.1 false && (List.ofFn x).getD e.2 false) := by
  apply Bool.eq_iff_iff.mpr
  simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, Finset.notMem_empty,
    false_and, exists_false, decide_false, Bool.false_or, decide_eq_true_eq,
    List.any_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨u, v, ⟨huv, hmem | hmem⟩, hu, hv⟩
    · refine ⟨(u.val, v.val), hmem, ?_, ?_⟩
      · simpa [List.getD_eq_getElem?_getD] using hu
      · simpa [List.getD_eq_getElem?_getD] using hv
    · refine ⟨(v.val, u.val), hmem, ?_, ?_⟩
      · simpa [List.getD_eq_getElem?_getD] using hv
      · simpa [List.getD_eq_getElem?_getD] using hu
  · rintro ⟨⟨a,b⟩, hab, ha, hb⟩
    obtain ⟨ha', hb', hne⟩ := he (a,b) hab
    refine ⟨⟨a, ha'⟩, ⟨b, hb'⟩, ⟨?_, Or.inl hab⟩, ?_, ?_⟩
    · simpa [Fin.ext_iff] using hne
    · simpa [List.getD_eq_getElem?_getD, ha'] using ha
    · simpa [List.getD_eq_getElem?_getD, hb'] using hb

lemma tarjan_edges_ok : ∀ e ∈ tarjanEdges, e.1 < 39 ∧ e.2 < 39 ∧ e.1 ≠ e.2 := by decide

lemma tarjan_y (a b c y z p u : Bool) :
    ((p || y) || (((((a || y) || b) || c) && (((a || z) || b) || c)) || u)) =
      (p || u || a || b || c || y) := by
  cases a <;> cases b <;> cases c <;> cases y <;> cases z <;> cases p <;> cases u <;> rfl

lemma tarjan_z (a b c y z p u : Bool) :
    ((p || z) || (((((a || y) || b) || c) && (((a || z) || b) || c)) || u)) =
      (p || u || a || b || c || z) := by
  cases a <;> cases b <;> cases c <;> cases y <;> cases z <;> cases p <;> cases u <;> rfl

set_option maxHeartbeats 4000000 in
lemma tarjan_fun : PEqualNP.MetaComplexity.circuitFun 39 tarjanCircuit =
    PEqualNP.MetaComplexity.NestedCover.graphFun tarjanGraph ∅ := by
  funext x
  rw [graphFun_edgeGraph_list 39 tarjanEdges tarjan_edges_ok]
  simp [PEqualNP.MetaComplexity.circuitFun, tarjanCircuit, PEqualNP.CircuitLowerBounds.Circuit.eval,
    PEqualNP.CircuitLowerBounds.Circuit.wires, PEqualNP.CircuitLowerBounds.GateOp.eval, tarjanEdges]
  rw [tarjan_y (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 9),
    tarjan_z (x 0) (x 1) (x 2) (x 3) (x 4) (x 6) (x 9),
    tarjan_y (x 0) (x 1) (x 2) (x 3) (x 4) (x 7) (x 10),
    tarjan_z (x 0) (x 1) (x 2) (x 3) (x 4) (x 8) (x 10)]
  generalize x (0 : Fin 39) = b0
  generalize x (1 : Fin 39) = b1
  generalize x (2 : Fin 39) = b2
  generalize x (3 : Fin 39) = b3
  generalize x (4 : Fin 39) = b4
  generalize x (5 : Fin 39) = b5
  generalize x (6 : Fin 39) = b6
  generalize x (7 : Fin 39) = b7
  generalize x (8 : Fin 39) = b8
  generalize x (9 : Fin 39) = b9
  generalize x (10 : Fin 39) = b10
  generalize x (11 : Fin 39) = b11
  generalize x (12 : Fin 39) = b12
  generalize x (13 : Fin 39) = b13
  generalize x (14 : Fin 39) = b14
  generalize x (15 : Fin 39) = b15
  generalize x (16 : Fin 39) = b16
  generalize x (17 : Fin 39) = b17
  generalize x (18 : Fin 39) = b18
  generalize x (19 : Fin 39) = b19
  generalize x (20 : Fin 39) = b20
  generalize x (21 : Fin 39) = b21
  generalize x (22 : Fin 39) = b22
  generalize x (23 : Fin 39) = b23
  generalize x (24 : Fin 39) = b24
  generalize x (25 : Fin 39) = b25
  generalize x (26 : Fin 39) = b26
  generalize x (27 : Fin 39) = b27
  generalize x (28 : Fin 39) = b28
  generalize x (29 : Fin 39) = b29
  generalize x (30 : Fin 39) = b30
  generalize x (31 : Fin 39) = b31
  generalize x (32 : Fin 39) = b32
  generalize x (33 : Fin 39) = b33
  generalize x (34 : Fin 39) = b34
  generalize x (35 : Fin 39) = b35
  generalize x (36 : Fin 39) = b36
  generalize x (37 : Fin 39) = b37
  generalize x (38 : Fin 39) = b38
  simp only [Bool.and_or_distrib_right]
  ac_rfl

end PEqualNP.Outside.L_meta_3678
