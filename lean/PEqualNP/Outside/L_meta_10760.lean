import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10760

open PEqualNP.CircuitLowerBounds

def edgeFunction (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 2) || (x 1 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 5 && x 6)

def monotoneWitness : List Gate :=
  [
    ⟨GateOp.or, [0, 2]⟩,
    ⟨GateOp.or, [3, 5]⟩,
    ⟨GateOp.or, [7, 8]⟩,
    ⟨GateOp.and, [6, 9]⟩,
    ⟨GateOp.or, [1, 5]⟩,
    ⟨GateOp.and, [3, 11]⟩,
    ⟨GateOp.or, [0, 1]⟩,
    ⟨GateOp.or, [4, 5]⟩,
    ⟨GateOp.and, [13, 14]⟩,
    ⟨GateOp.or, [0, 4]⟩,
    ⟨GateOp.and, [2, 16]⟩,
    ⟨GateOp.or, [10, 12]⟩,
    ⟨GateOp.or, [15, 17]⟩,
    ⟨GateOp.or, [18, 19]⟩
  ]

lemma witness_size : monotoneWitness.length = 14 := rfl

lemma witness_allowed : ∀ g ∈ monotoneWitness,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  simp [monotoneWitness]

set_option maxHeartbeats 2000000 in
lemma witness_eval : ∀ x : Fin 7 → Bool,
    Circuit.eval ⟨monotoneWitness, 20⟩ (List.ofFn x) = edgeFunction x := by
  decide +kernel

set_option maxHeartbeats 2000000 in
lemma edgeFunction_posted : ∀ x : Fin 7 → Bool,
    decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) = edgeFunction x := by
  decide +kernel


def pairInput (i j : Fin 7) : Fin 7 → Bool :=
  fun k => decide (k = i ∨ k = j)

set_option maxHeartbeats 8000000 in
lemma positive_pair : ∀ x : Fin 7 → Bool, edgeFunction x = true →
    ∃ i j : Fin 7, i ≠ j ∧ pairInput i j ≤ x ∧ edgeFunction (pairInput i j) = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
lemma negative_pair : ∀ x : Fin 7 → Bool, edgeFunction x = false →
    ∃ i j : Fin 7, i ≠ j ∧ x ≤ pairInput i j ∧ edgeFunction (pairInput i j) = false := by
  decide +kernel

lemma pair_table_suffices (g : (Fin 7 → Bool) → Bool) (hg : Monotone g)
    (hpair : ∀ i j : Fin 7, i ≠ j → g (pairInput i j) = edgeFunction (pairInput i j)) :
    ∀ x : Fin 7 → Bool, g x = edgeFunction x := by
  intro x
  cases hx : edgeFunction x with
  | false =>
    obtain ⟨i, j, hij, hle, hf⟩ := negative_pair x hx
    have h := hg hle
    rw [hpair i j hij, hf] at h
    exact Bool.eq_false_of_le_false h
  | true =>
    obtain ⟨i, j, hij, hle, hf⟩ := positive_pair x hx
    have h := hg hle
    rw [hpair i j hij, hf] at h
    exact Bool.eq_true_of_true_le h

end PEqualNP.Outside.L_meta_10760
