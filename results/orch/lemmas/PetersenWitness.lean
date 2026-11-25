import PEqualNP.Defs

namespace PEqualNP.Outside.Pilot96Witness

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def petersen (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)

def witness : Circuit :=
  ⟨[
    ⟨.or, [0, 2]⟩,
    ⟨.or, [10, 6]⟩,
    ⟨.and, [1, 11]⟩,
    ⟨.or, [2, 4]⟩,
    ⟨.or, [13, 8]⟩,
    ⟨.and, [3, 14]⟩,
    ⟨.or, [0, 9]⟩,
    ⟨.and, [4, 16]⟩,
    ⟨.or, [0, 7]⟩,
    ⟨.or, [18, 8]⟩,
    ⟨.and, [5, 19]⟩,
    ⟨.or, [9, 8]⟩,
    ⟨.and, [6, 21]⟩,
    ⟨.or, [2, 9]⟩,
    ⟨.and, [7, 23]⟩,
    ⟨.or, [12, 15]⟩,
    ⟨.or, [25, 17]⟩,
    ⟨.or, [26, 20]⟩,
    ⟨.or, [27, 22]⟩,
    ⟨.or, [28, 24]⟩
  ], 29⟩

lemma witnessSize : witness.size = 20 := rfl

lemma witnessMonotone : Monotone2 witness := by
  simp [Monotone2, witness]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma witnessCorrect : ∀ x : Fin 10 → Bool, witness.eval (List.ofFn x) = petersen x := by
  intro x
  simp [witness, petersen, Circuit.eval, Circuit.wires, GateOp.eval,
    List.ofFn_succ, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
    Bool.or_assoc, Bool.or_left_comm, Bool.or_comm, Bool.and_comm]
  rw [Bool.and_comm (x 2) (x 1), Bool.and_comm (x 1) (x 0)]
  exact Bool.or_left_comm _ _ _


def edges : List (Fin 10 × Fin 10) :=
  [(0,1), (1,2), (2,3), (3,4), (4,0), (0,5), (1,6), (2,7),
   (3,8), (4,9), (5,7), (7,9), (9,6), (6,8), (8,5)]

lemma coverUpper :
    (∀ e ∈ edges, e.1 ∈ ({1, 3, 4, 5, 6, 7} : Finset (Fin 10)) ∨
      e.2 ∈ ({1, 3, 4, 5, 6, 7} : Finset (Fin 10))) ∧
    ({1, 3, 4, 5, 6, 7} : Finset (Fin 10)).card = 6 := by
  decide +kernel

end PEqualNP.Outside.Pilot96Witness
