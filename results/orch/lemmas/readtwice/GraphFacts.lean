import Mathlib.Combinatorics.SimpleGraph.Finite

namespace PEqualNP.Outside.L_meta_1890.ReadTwice

def pairs : List (Fin 10 × Fin 10) :=
  [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),
   (5,7),(7,9),(9,6),(6,8),(8,5)]

abbrev graph : SimpleGraph (Fin 10) :=
  SimpleGraph.fromRel (fun u v => (u,v) ∈ pairs)

def edge (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
set_option synthInstance.maxSize 100000 in
lemma no_triangle : ∀ a b c : Fin 10, ¬ (graph.Adj a b ∧ graph.Adj b c ∧ graph.Adj c a) := by
  simp only [graph, SimpleGraph.fromRel_adj]
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
set_option synthInstance.maxSize 100000 in
lemma no_square : ∀ a b c d : Fin 10, a ≠ c → b ≠ d →
    ¬ (graph.Adj a b ∧ graph.Adj b c ∧ graph.Adj c d ∧ graph.Adj d a) := by
  simp only [graph, SimpleGraph.fromRel_adj]
  decide +kernel


end PEqualNP.Outside.L_meta_1890.ReadTwice
