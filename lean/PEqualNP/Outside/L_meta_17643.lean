import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17643

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds in
def W : Circuit := ⟨[⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [27, 6]⟩, ⟨GateOp.or, [28, 12]⟩, ⟨GateOp.and, [29, 16]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [31, 7]⟩, ⟨GateOp.or, [32, 0]⟩, ⟨GateOp.and, [33, 17]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.or, [35, 10]⟩, ⟨GateOp.or, [36, 3]⟩, ⟨GateOp.and, [37, 20]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [39, 11]⟩, ⟨GateOp.or, [40, 4]⟩, ⟨GateOp.and, [41, 21]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [43, 12]⟩, ⟨GateOp.or, [44, 5]⟩, ⟨GateOp.and, [45, 22]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [47, 0]⟩, ⟨GateOp.or, [48, 6]⟩, ⟨GateOp.and, [49, 23]⟩, ⟨GateOp.or, [30, 34]⟩, ⟨GateOp.or, [51, 38]⟩, ⟨GateOp.or, [52, 42]⟩, ⟨GateOp.or, [53, 46]⟩, ⟨GateOp.or, [54, 50]⟩], 55⟩
def A (a b : Bool) : Bool := [a, b].all id
def O (a b : Bool) : Bool := [a, b].any id
theorem A_eq (a b : Bool) : A a b = (a && b) := by cases a <;> cases b <;> rfl
theorem O_eq (a b : Bool) : O a b = (a || b) := by cases a <;> cases b <;> rfl
theorem ev (x : Fin 26 → Bool) (h : Bool) : W.eval (List.ofFn x ++ [h]) = (O (O (O (O (O (A (O (O (O (x 3) (x 4)) (x 6)) (x 12)) (x 16)) (A (O (O (O (x 4) (x 5)) (x 7)) (x 0)) (x 17))) (A (O (O (O (x 7) (x 8)) (x 10)) (x 3)) (x 20))) (A (O (O (O (x 8) (x 9)) (x 11)) (x 4)) (x 21))) (A (O (O (O (x 9) (x 10)) (x 12)) (x 5)) (x 22))) (A (O (O (O (x 10) (x 11)) (x 0)) (x 6)) (x 23))) := by
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25] := by
    simp [List.ofFn_succ]
  rw [hl]
  simp only [W, Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.getD_cons_zero, List.getD_cons_succ, GateOp.eval, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id, Bool.or_false, Bool.and_true, A_eq, O_eq]

theorem aux : True := trivial

end PEqualNP.Outside.L_meta_17643

theorem PEqualNP.Outside.L_meta_17643 : ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (29 : ℕ) ∧ (27 : ℕ) ≤ x1.output ∧ x1.output < (27 : ℕ) + x1.size ∧ PEqualNP.TopForm.IsAO2 (27 : ℕ) x1 ∧ (∀ x2 ∈ x1.gates, x2.inputs.Nodup) ∧ ∀ (x2 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x2 ++ [x2 (1 : Fin (26 : ℕ)) || x2 (2 : Fin (26 : ℕ))]) = Bool.true ↔ ∃ (x3 : Fin (13 : ℕ)), ∃ x4 ∈ [(3 : Fin (13 : ℕ)), (4 : Fin (13 : ℕ)), (7 : Fin (13 : ℕ)), (8 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ)), (10 : Fin (13 : ℕ))], (x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ))) ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true := by
  refine ⟨L_meta_17643.W, by decide, by decide, by decide, ?_, ?_, ?_⟩
  · decide
  · decide
  · intro x
    rw [L_meta_17643.ev]
    simp only [L_meta_17643.A_eq, L_meta_17643.O_eq, Bool.or_eq_true, Bool.and_eq_true]
    constructor
    · intro h
      rcases h with (((((⟨(((h | h) | h) | h), hl⟩ | ⟨(((h | h) | h) | h), hl⟩) | ⟨(((h | h) | h) | h), hl⟩) | ⟨(((h | h) | h) | h), hl⟩) | ⟨(((h | h) | h) | h), hl⟩) | ⟨(((h | h) | h) | h), hl⟩)
      · exact ⟨3, 3, by decide, by decide, h, hl⟩
      · exact ⟨4, 3, by decide, by decide, h, hl⟩
      · exact ⟨6, 3, by decide, by decide, h, hl⟩
      · exact ⟨12, 3, by decide, by decide, h, hl⟩
      · exact ⟨4, 4, by decide, by decide, h, hl⟩
      · exact ⟨5, 4, by decide, by decide, h, hl⟩
      · exact ⟨7, 4, by decide, by decide, h, hl⟩
      · exact ⟨0, 4, by decide, by decide, h, hl⟩
      · exact ⟨7, 7, by decide, by decide, h, hl⟩
      · exact ⟨8, 7, by decide, by decide, h, hl⟩
      · exact ⟨10, 7, by decide, by decide, h, hl⟩
      · exact ⟨3, 7, by decide, by decide, h, hl⟩
      · exact ⟨8, 8, by decide, by decide, h, hl⟩
      · exact ⟨9, 8, by decide, by decide, h, hl⟩
      · exact ⟨11, 8, by decide, by decide, h, hl⟩
      · exact ⟨4, 8, by decide, by decide, h, hl⟩
      · exact ⟨9, 9, by decide, by decide, h, hl⟩
      · exact ⟨10, 9, by decide, by decide, h, hl⟩
      · exact ⟨12, 9, by decide, by decide, h, hl⟩
      · exact ⟨5, 9, by decide, by decide, h, hl⟩
      · exact ⟨10, 10, by decide, by decide, h, hl⟩
      · exact ⟨11, 10, by decide, by decide, h, hl⟩
      · exact ⟨0, 10, by decide, by decide, h, hl⟩
      · exact ⟨6, 10, by decide, by decide, h, hl⟩
    · rintro ⟨x3, x4, hx4, hc, h1, h2⟩
      have key : ∀ x3 x4 : Fin 13, x4 ∈ ([3, 4, 7, 8, 9, 10] : List (Fin 13)) → (x3 = x4 ∨ x3 = x4 + 1 ∨ x3 = x4 + 3 ∨ x3 = x4 + 9) →
          (x3, x4) ∈ ([(3, 3), (4, 3), (6, 3), (12, 3), (4, 4), (5, 4), (7, 4), (0, 4), (7, 7), (8, 7), (10, 7), (3, 7), (8, 8), (9, 8), (11, 8), (4, 8), (9, 9), (10, 9), (12, 9), (5, 9), (10, 10), (11, 10), (0, 10), (6, 10)] : List (Fin 13 × Fin 13)) := by decide
      have hm := key x3 x4 hx4 hc
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (⟨Or.inl (Or.inl (Or.inl h1)), h2⟩)))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (⟨Or.inl (Or.inl (Or.inr h1)), h2⟩)))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (⟨Or.inl (Or.inr h1), h2⟩)))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (⟨Or.inr h1, h2⟩)))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨Or.inl (Or.inl (Or.inl h1)), h2⟩))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨Or.inl (Or.inl (Or.inr h1)), h2⟩))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨Or.inl (Or.inr h1), h2⟩))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨Or.inr h1, h2⟩))))
      · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨Or.inl (Or.inl (Or.inl h1)), h2⟩)))
      · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨Or.inl (Or.inl (Or.inr h1)), h2⟩)))
      · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨Or.inl (Or.inr h1), h2⟩)))
      · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨Or.inr h1, h2⟩)))
      · exact Or.inl (Or.inl (Or.inr ⟨Or.inl (Or.inl (Or.inl h1)), h2⟩))
      · exact Or.inl (Or.inl (Or.inr ⟨Or.inl (Or.inl (Or.inr h1)), h2⟩))
      · exact Or.inl (Or.inl (Or.inr ⟨Or.inl (Or.inr h1), h2⟩))
      · exact Or.inl (Or.inl (Or.inr ⟨Or.inr h1, h2⟩))
      · exact Or.inl (Or.inr ⟨Or.inl (Or.inl (Or.inl h1)), h2⟩)
      · exact Or.inl (Or.inr ⟨Or.inl (Or.inl (Or.inr h1)), h2⟩)
      · exact Or.inl (Or.inr ⟨Or.inl (Or.inr h1), h2⟩)
      · exact Or.inl (Or.inr ⟨Or.inr h1, h2⟩)
      · exact Or.inr ⟨Or.inl (Or.inl (Or.inl h1)), h2⟩
      · exact Or.inr ⟨Or.inl (Or.inl (Or.inr h1)), h2⟩
      · exact Or.inr ⟨Or.inl (Or.inr h1), h2⟩
      · exact Or.inr ⟨Or.inr h1, h2⟩
