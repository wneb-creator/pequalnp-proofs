import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

namespace PEqualNP.Outside.L_meta_3566.DoubleLift

def baseEdges : List (Fin 8 × Fin 8) :=
  [(0, 4), (0, 6), (1, 5), (1, 6), (1, 7), (2, 6), (3, 7), (4, 7)]

def lower (v : Fin 8) : Fin 16 :=
  ⟨v.val, Nat.lt_trans v.isLt (by decide)⟩

def upper (v : Fin 8) : Fin 16 :=
  ⟨v.val + 8, Nat.add_lt_add_right v.isLt 8⟩

def doubleEdges : List (Fin 16 × Fin 16) :=
  baseEdges.flatMap fun uv => [(lower uv.1, upper uv.2), (lower uv.2, upper uv.1)]

def adjacencyBool (u v : Fin 16) : Bool :=
  doubleEdges.contains (u, v) || doubleEdges.contains (v, u)

def adjacencyBits (u v : Fin 16) : Bool :=
  (45938212404688224660688823459344804183317390199943558577277627156041584640 : Nat).testBit
    (16 * u.val + v.val)

lemma adjacency_bits : ∀ u v : Fin 16, adjacencyBool u v = adjacencyBits u v := by
  decide +kernel

lemma adjacency_symmetric : ∀ u v : Fin 16, adjacencyBool u v = adjacencyBool v u := by
  decide +kernel

lemma adjacency_irreflexive : ∀ u : Fin 16, adjacencyBool u u = false := by
  decide +kernel

lemma bipartite_sides : ∀ u v : Fin 16, adjacencyBool u v = true →
    (u.val < 8 ∧ 8 ≤ v.val) ∨ (v.val < 8 ∧ 8 ≤ u.val) := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
lemma no_four_cycle : ∀ a b : Fin 16, a ≠ b →
    (Finset.univ.filter fun w => adjacencyBool a w = true ∧ adjacencyBool b w = true).card ≤ 1 := by
  have fast : ∀ a b : Fin 16, a ≠ b →
      (Finset.univ.filter fun w => adjacencyBits a w = true ∧ adjacencyBits b w = true).card ≤ 1 := by
    decide +kernel
  simpa only [adjacency_bits] using fast

def graphFunction (x : Fin 16 → Bool) : Bool :=
  doubleEdges.any fun uv => x uv.1 && x uv.2

def naiveTerm (x : Fin 16 → Bool) : Bool :=
  x 2 && (x 14 || x 15) && (x 12 || x 14)

def badAssignment (v : Fin 16) : Bool :=
  [2, 12, 15].contains v

lemma bad_assignment_no_edge : graphFunction badAssignment = false := by
  decide +kernel

lemma bad_assignment_naive_term : naiveTerm badAssignment = true := by
  decide +kernel

lemma naive_term_does_not_imply_graph :
    ¬ (∀ x : Fin 16 → Bool, naiveTerm x = true → graphFunction x = true) := by
  intro h
  have bad := h badAssignment bad_assignment_naive_term
  rw [bad_assignment_no_edge] at bad
  cases bad

def withEdgeAdjacency (s t u v : Fin 16) : Bool :=
  adjacencyBool u v || (u == s && v == t) || (u == t && v == s)

lemma add_two_fifteen_cycle :
    ([2, 14, 1, 15] : List (Fin 16)).Nodup ∧
    withEdgeAdjacency 2 15 2 14 = true ∧
    withEdgeAdjacency 2 15 14 1 = true ∧
    withEdgeAdjacency 2 15 1 15 = true ∧
    withEdgeAdjacency 2 15 15 2 = true := by
  decide +kernel

lemma add_two_fifteen_common_neighbors :
    (Finset.univ.filter fun w =>
      withEdgeAdjacency 2 15 2 w = true ∧ withEdgeAdjacency 2 15 1 w = true).card = 2 := by
  decide +kernel

lemma add_two_twelve_cycle :
    ([2, 14, 0, 12] : List (Fin 16)).Nodup ∧
    withEdgeAdjacency 2 12 2 14 = true ∧
    withEdgeAdjacency 2 12 14 0 = true ∧
    withEdgeAdjacency 2 12 0 12 = true ∧
    withEdgeAdjacency 2 12 12 2 = true := by
  decide +kernel

lemma add_two_twelve_common_neighbors :
    (Finset.univ.filter fun w =>
      withEdgeAdjacency 2 12 2 w = true ∧ withEdgeAdjacency 2 12 0 w = true).card = 2 := by
  decide +kernel

end PEqualNP.Outside.L_meta_3566.DoubleLift
