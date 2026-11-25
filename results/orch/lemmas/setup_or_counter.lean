import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1031.CounterOr

open PEqualNP.CircuitLowerBounds

def edgeList : List (Fin 8 × Fin 8) :=
  [(0, 1), (1, 2), (0, 5), (1, 6), (2, 7),
   (3, 5), (4, 6), (5, 7), (6, 3), (7, 4)]

abbrev adjacent (u v : Fin 8) : Prop :=
  (u, v) ∈ edgeList ∨ (v, u) ∈ edgeList

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
abbrev graph : SimpleGraph (Fin 8) where
  Adj := adjacent
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

def circuit : Circuit :=
  ⟨[⟨.or, [1, 5]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [5, 6]⟩,
    ⟨.and, [8, 9]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [4, 12]⟩,
    ⟨.or, [6, 7]⟩, ⟨.and, [13, 14]⟩, ⟨.and, [0, 8]⟩,
    ⟨.or, [15, 16]⟩, ⟨.and, [3, 10]⟩, ⟨.or, [17, 18]⟩,
    ⟨.and, [2, 9]⟩, ⟨.or, [19, 20]⟩], 21⟩

def orCount (C : Circuit) : ℕ :=
  C.gates.countP fun g => match g.op with | .or => true | _ => false

theorem binary_monotone :
    ∀ g ∈ circuit.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  simp [circuit]

theorem gate_count : circuit.size = 14 := rfl

theorem or_count : orCount circuit = 8 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem edge_count : graph.edgeFinset.card = 10 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem no_triangle :
    ∀ a b c : Fin 8, graph.Adj a b → graph.Adj b c → ¬graph.Adj c a := by
  letI : DecidableRel graph.Adj := fun u v => inferInstanceAs (Decidable (adjacent u v))
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem no_four_cycle :
    ∀ a b c d : Fin 8, a ≠ c → b ≠ d →
      graph.Adj a b → graph.Adj b c → graph.Adj c d → ¬graph.Adj d a := by
  letI : DecidableRel graph.Adj := fun u v => inferInstanceAs (Decidable (adjacent u v))
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem computes :
    ∀ x : Fin 8 → Bool, circuit.eval (List.ofFn x) =
      decide (∃ i j : Fin 8, graph.Adj i j ∧ x i = true ∧ x j = true) := by
  decide

theorem violates_or_edge_bound : orCount circuit < graph.edgeFinset.card - 1 := by
  rw [or_count, edge_count]
  decide

end PEqualNP.Outside.L_meta_1031.CounterOr
