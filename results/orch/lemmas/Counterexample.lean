import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1031

open PEqualNP.CircuitLowerBounds

lemma edgeless_least (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : ∀ u v : Fin n, ¬ G.Adj u v) :
    ∃ C : Circuit, C.gates = [] ∧
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) =
        decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) ∧
      ∀ D : Circuit, C.size ≤ D.size := by
  refine ⟨⟨[], n⟩, rfl, ?_, ?_⟩
  · intro x
    have hfalse : ¬ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true := by
      rintro ⟨i, j, hij, _, _⟩
      exact hG i j hij
    simp [Circuit.eval, Circuit.wires, List.getD_eq_getElem?_getD, hfalse]
  · intro D
    simp [Circuit.size]

end PEqualNP.Outside.L_meta_1031

namespace PEqualNP.Outside.L_meta_1031.Counterexample

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership

abbrev cycleFive : SimpleGraph (Fin 5) :=
  edgeGraph 5 [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]

def cycleFiveEight : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.or, [1, 3]⟩, ⟨.and, [5, 6]⟩,
    ⟨.or, [1, 2]⟩, ⟨.and, [7, 8]⟩, ⟨.or, [0, 3]⟩,
    ⟨.and, [4, 10]⟩, ⟨.or, [9, 11]⟩], 12⟩

lemma cycleFive_triangle_free :
    ∀ a b c : Fin 5, cycleFive.Adj a b → cycleFive.Adj b c → ¬ cycleFive.Adj c a := by
  decide

lemma cycleFive_four_cycle_free :
    ∀ a b c d : Fin 5, cycleFive.Adj a b → cycleFive.Adj b c →
      cycleFive.Adj c d → cycleFive.Adj d a → a = c ∨ b = d := by
  decide

lemma cycleFiveEight_correct :
    ∀ x : Fin 5 → Bool, cycleFiveEight.eval (List.ofFn x) =
      decide (∃ i j : Fin 5, cycleFive.Adj i j ∧ x i = true ∧ x j = true) := by
  decide

lemma cycleFiveEight_size : cycleFiveEight.size = 8 := by
  rfl

lemma cycleFiveEight_not_star : ¬ HasStarProfile 5 cycleFive cycleFiveEight := by
  decide

lemma cycleFiveEight_disjoint_owned :
    Owns 5 cycleFiveEight 2 0 1 ∧ Owns 5 cycleFiveEight 2 2 3 := by
  decide

lemma cycleFiveEight_empty_owner :
    ∀ u v : Fin 5, cycleFive.Adj u v → ¬ Owns 5 cycleFiveEight 4 u v := by
  decide

def cycleFiveSeven : Circuit :=
  ⟨[⟨.and, [0, 4]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [3, 6]⟩,
    ⟨.or, [0, 2]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [5, 9]⟩,
    ⟨.or, [7, 10]⟩], 11⟩

lemma cycleFiveSeven_correct :
    ∀ x : Fin 5 → Bool, cycleFiveSeven.eval (List.ofFn x) =
      decide (∃ i j : Fin 5, cycleFive.Adj i j ∧ x i = true ∧ x j = true) := by
  decide

lemma cycleFiveSeven_legal :
    ∀ g ∈ cycleFiveSeven.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      g.inputs.length ≤ 2 := by
  intro g hg
  simp only [cycleFiveSeven, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma cycleFiveEight_not_least :
    ¬ (∀ D : Circuit,
      (∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
      (∀ x : Fin 5 → Bool, D.eval (List.ofFn x) =
        decide (∃ i j : Fin 5, cycleFive.Adj i j ∧ x i = true ∧ x j = true)) →
      cycleFiveEight.size ≤ D.size) := by
  intro h
  have hb := h cycleFiveSeven cycleFiveSeven_legal cycleFiveSeven_correct
  norm_num [Circuit.size, cycleFiveEight, cycleFiveSeven] at hb

end PEqualNP.Outside.L_meta_1031.Counterexample
