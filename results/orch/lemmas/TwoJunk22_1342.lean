import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1342.TwoJunkWitness

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A checked near witness: size22, not the posted size21 conclusion.
def twoJunk22 : Circuit :=
  ⟨[⟨GateOp.or, [0, 8]⟩,
    ⟨GateOp.or, [4, 9]⟩,
    ⟨GateOp.and, [11, 12]⟩,
    ⟨GateOp.or, [8, 9]⟩,
    ⟨GateOp.and, [13, 14]⟩,
    ⟨GateOp.or, [7, 10]⟩,
    ⟨GateOp.or, [6, 9]⟩,
    ⟨GateOp.and, [16, 17]⟩,
    ⟨GateOp.or, [6, 7]⟩,
    ⟨GateOp.or, [3, 18]⟩,
    ⟨GateOp.and, [19, 20]⟩,
    ⟨GateOp.or, [4, 8]⟩,
    ⟨GateOp.and, [1, 22]⟩,
    ⟨GateOp.or, [2, 14]⟩,
    ⟨GateOp.and, [5, 24]⟩,
    ⟨GateOp.or, [0, 2]⟩,
    ⟨GateOp.or, [26, 4]⟩,
    ⟨GateOp.and, [10, 27]⟩,
    ⟨GateOp.or, [15, 21]⟩,
    ⟨GateOp.or, [29, 23]⟩,
    ⟨GateOp.or, [30, 25]⟩,
    ⟨GateOp.or, [31, 28]⟩], 32⟩

theorem twoJunk22_mono : Monotone2 twoJunk22 := by
  simp [Monotone2, twoJunk22]

theorem twoJunk22_size : twoJunk22.size = 22 := rfl

theorem twoJunk22_ao2 : PEqualNP.TopForm.IsAO2 11 twoJunk22 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem twoJunk22_exact : ∀ x : Fin 11 → Bool,
  twoJunk22.eval (List.ofFn x) = true ↔
  ∃ u v : Fin 11, (u.val, v.val) ∈
    ([(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
      (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] : List (ℕ × ℕ)) ∧
    x u = true ∧ x v = true := by
  intro x
  have identity (a b c d : Prop) :
      ((b ∨ a) ∧ (d ∨ c)) ∧ (a ∨ c) ↔ (a ∧ c ∨ a ∧ d ∨ b ∧ c) := by
    tauto
  have second (a b c d e : Prop) :
      (a ∨ b) ∧ (c ∨ ((b ∨ d) ∧ (a ∨ e))) ↔
        (a ∧ c ∨ b ∧ c ∨ a ∧ b ∨ a ∧ d ∨ b ∧ e) := by
    tauto
  simp [twoJunk22, Circuit.eval, Circuit.wires, GateOp.eval, List.ofFn_succ, Fin.exists_fin_succ]
  rw [identity, second]
  simp only [and_or_left]
  apply Iff.of_eq
  ac_rfl

def tail19 : Circuit := ⟨twoJunk22.gates.drop 3, twoJunk22.output⟩

theorem tail19_mono : Monotone2 tail19 := by
  simp [Monotone2, tail19, twoJunk22]

theorem tail19_size : tail19.size = 19 := rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem tail19_exact : ∀ x : Fin 11 → Bool,
  tail19.eval (List.ofFn x ++
    [x 0 || x 8, x 4 || x 9, (x 0 || x 8) && (x 4 || x 9)]) = true ↔
  ∃ u v : Fin 11, (u.val, v.val) ∈
    ([(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
      (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] : List (ℕ × ℕ)) ∧
    x u = true ∧ x v = true := by
  intro x
  have eq : tail19.eval (List.ofFn x ++
      [x 0 || x 8, x 4 || x 9, (x 0 || x 8) && (x 4 || x 9)]) =
      twoJunk22.eval (List.ofFn x) := by
    simp [tail19, twoJunk22, Circuit.eval, Circuit.wires, GateOp.eval, List.ofFn_succ]
  rw [eq]
  exact twoJunk22_exact x

end PEqualNP.Outside.L_meta_1342.TwoJunkWitness
