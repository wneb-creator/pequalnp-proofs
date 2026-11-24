import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2028.PairOnly

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def hood : Fin 6 → ℕ := ![14, 21, 35, 1, 2, 4]

abbrev adj (u v : Fin 6) : Prop := (hood u).testBit v.val = true

def graph : SimpleGraph (Fin 6) where
  Adj := adj
  symm := ⟨by decide +kernel⟩
  loopless := ⟨by decide +kernel⟩

def edges : Finset (Sym2 (Fin 6)) :=
  {s(0, 1), s(0, 2), s(1, 2), s(0, 3), s(1, 4), s(2, 5)}

lemma edges_eq : graph.edgeSet = (edges : Set (Sym2 (Fin 6))) := by
  ext e
  induction e using Sym2.ind with
  | _ u v =>
    change adj u v ↔ s(u, v) ∈ edges
    revert u v
    decide +kernel

lemma edge_count : graph.edgeSet.ncard = 6 := by
  rw [edges_eq, Set.ncard_coe_finset]
  decide +kernel

lemma no_four_cycle : ∀ a b c d : Fin 6, a ≠ c → b ≠ d →
    graph.Adj a b → graph.Adj b c → graph.Adj c d → ¬ graph.Adj d a := by
  unfold graph
  decide +kernel

lemma has_cover : ∃ S : Finset (Fin 6),
    CoverPromise.IsVertexCover graph S ∧ S.card = 3 := by
  refine ⟨{0, 1, 2}, ?_, by decide +kernel⟩
  unfold CoverPromise.IsVertexCover graph
  decide +kernel

lemma cover_minimum : ∀ S : Finset (Fin 6),
    CoverPromise.IsVertexCover graph S → 3 ≤ S.card := by
  unfold CoverPromise.IsVertexCover graph
  decide +kernel

def circuit : Circuit where
  gates := [⟨.or, [0, 2]⟩, ⟨.or, [6, 4]⟩,
    ⟨.or, [0, 5]⟩, ⟨.or, [2, 3]⟩,
    ⟨.and, [8, 9]⟩, ⟨.or, [1, 10]⟩, ⟨.and, [7, 11]⟩]
  output := 12

lemma circuit_monotone : Monotone2 circuit := by
  simp [Monotone2, circuit]

lemma circuit_size : circuit.size = 7 := rfl

lemma pair_agreement : ∀ u v : Fin 6,
    circuit.eval (List.ofFn (fun i => decide (i = u ∨ i = v))) = true ↔
      graph.Adj u v := by
  unfold graph
  decide +kernel

def bad : Fin 6 → Bool := fun i => decide (3 ≤ i.val)

lemma bad_accepted : circuit.eval (List.ofFn bad) = true := by
  decide +kernel

lemma bad_independent : ¬ ∃ u v : Fin 6,
    graph.Adj u v ∧ bad u = true ∧ bad v = true := by
  unfold graph
  decide +kernel

lemma below_bound : circuit.size + 1 < graph.edgeSet.ncard + 3 := by
  rw [circuit_size, edge_count]
  decide

end PEqualNP.Outside.L_meta_2028.PairOnly
