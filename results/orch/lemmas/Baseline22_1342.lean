import PEqualNP.Defs

-- Partial support only; the required size21 existence claim remains unresolved.

namespace PEqualNP.Outside.L_meta_1342

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def appendCircuits (A B : Circuit) : Circuit := ⟨A.gates ++ B.gates, B.output⟩

theorem eval_append (A B : Circuit) (x : List Bool) :
    (appendCircuits A B).eval x = B.eval (A.wires x) := by
  simp [appendCircuits, Circuit.eval, Circuit.wires, List.foldl_append]

theorem monotone_append (A B : Circuit) (ha : Monotone2 A) (hb : Monotone2 B) :
    Monotone2 (appendCircuits A B) := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact ha g hg
  · exact hb g hg

theorem size_append (A B : Circuit) :
    (appendCircuits A B).size = A.size + B.size := by
  simp [appendCircuits, Circuit.size]

def baseline : Circuit :=
  ⟨[⟨.or, [9, 10]⟩,
    ⟨.and, [0, 11]⟩,
    ⟨.or, [4, 8]⟩,
    ⟨.and, [1, 13]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.and, [3, 15]⟩,
    ⟨.or, [2, 8]⟩,
    ⟨.or, [17, 9]⟩,
    ⟨.and, [5, 18]⟩,
    ⟨.or, [6, 9]⟩,
    ⟨.and, [7, 20]⟩,
    ⟨.or, [4, 9]⟩,
    ⟨.and, [8, 22]⟩,
    ⟨.or, [2, 4]⟩,
    ⟨.or, [24, 6]⟩,
    ⟨.and, [10, 25]⟩,
    ⟨.or, [12, 14]⟩,
    ⟨.or, [27, 16]⟩,
    ⟨.or, [28, 19]⟩,
    ⟨.or, [29, 21]⟩,
    ⟨.or, [30, 23]⟩,
    ⟨.or, [31, 26]⟩], 32⟩

theorem baseline_monotone : Monotone2 baseline := by
  simp [Monotone2, baseline]

theorem baseline_size : baseline.size = 22 := by
  rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem baseline_correct : ∀ x : Fin 11 → Bool,
    (baseline.eval (List.ofFn x) = true ↔ ∃ u v : Fin 11,
      (u.val, v.val) ∈ ([(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),
        (3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] : List (ℕ × ℕ)) ∧
      x u = true ∧ x v = true) := by
  intro x
  simp [baseline, Circuit.eval, Circuit.wires, GateOp.eval, List.ofFn_succ, Fin.exists_fin_succ]
  <;> simp only [and_or_left, or_and_right]
  apply Iff.of_eq
  ac_rfl

end PEqualNP.Outside.L_meta_1342
