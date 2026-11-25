import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1031.PetersenOrCounterexample

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership

abbrev graph : SimpleGraph (Fin 8) :=
  edgeGraph 8 [(0, 4), (0, 5), (0, 7), (1, 3), (1, 5),
    (1, 6), (2, 3), (2, 4), (3, 7), (4, 6)]

def circuit : Circuit :=
  ⟨[⟨.or, [1, 4]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [3, 4]⟩,
    ⟨.and, [8, 9]⟩, ⟨.and, [11, 10]⟩, ⟨.or, [5, 12]⟩,
    ⟨.and, [6, 8]⟩, ⟨.and, [2, 10]⟩, ⟨.or, [14, 15]⟩,
    ⟨.or, [0, 1]⟩, ⟨.and, [13, 17]⟩, ⟨.and, [7, 9]⟩,
    ⟨.or, [18, 19]⟩, ⟨.or, [16, 20]⟩], 21⟩

lemma triangle_free :
    ∀ a b c : Fin 8, graph.Adj a b → graph.Adj b c → ¬ graph.Adj c a := by
  decide +kernel

lemma four_cycle_free :
    ∀ a b c d : Fin 8, graph.Adj a b → graph.Adj b c →
      graph.Adj c d → graph.Adj d a → a = c ∨ b = d := by
  decide +kernel

lemma computes_graph :
    ∀ x : Fin 8 → Bool, circuit.eval (List.ofFn x) =
      decide (∃ i j : Fin 8, graph.Adj i j ∧ x i = true ∧ x j = true) := by
  decide +kernel

lemma binary_monotone :
    ∀ g ∈ circuit.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma edge_count : graph.edgeFinset.card = 10 := by
  decide +kernel

def isOr (g : Gate) : Bool :=
  match g.op with
  | .or => true
  | _ => false

lemma or_count : (circuit.gates.filter isOr).length = 8 := by
  decide +kernel

lemma size_fourteen : circuit.size = 14 := by
  rfl

lemma violates_separate_or_bound :
    graph.edgeFinset.card > (circuit.gates.filter isOr).length + 1 := by
  rw [edge_count, or_count]
  omega

lemma disjoint_owned_edges :
    Owns 8 circuit 3 0 4 ∧ Owns 8 circuit 3 1 3 := by
  decide +kernel

end PEqualNP.Outside.L_meta_1031.PetersenOrCounterexample
