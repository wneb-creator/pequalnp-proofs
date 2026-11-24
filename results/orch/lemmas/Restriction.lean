import Mathlib

namespace PEqualNP.Outside.L_meta_3821_aux

def pet (x : Fin 10 → Bool) : Bool :=
  (List.finRange 5).any fun i =>
    x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1)) ||
    x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i) ||
    x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2))

def sigma0 : Equiv.Perm (Fin 10) where
  toFun := ![9, 4, 0, 1, 6, 7, 3, 5, 2, 8]
  invFun := ![2, 3, 8, 6, 1, 7, 4, 5, 9, 0]
  left_inv := by decide
  right_inv := by decide

def sigma1 : Equiv.Perm (Fin 10) where
  toFun := ![4, 9, 6, 1, 0, 3, 7, 8, 2, 5]
  invFun := ![4, 3, 8, 5, 0, 9, 2, 6, 7, 1]
  left_inv := by decide
  right_inv := by decide

def sigma2 : Equiv.Perm (Fin 10) where
  toFun := ![0, 4, 9, 6, 1, 5, 3, 7, 8, 2]
  invFun := ![0, 4, 9, 6, 1, 5, 3, 7, 8, 2]
  left_inv := by decide
  right_inv := by decide

def sigma3 : Equiv.Perm (Fin 10) where
  toFun := ![1, 0, 4, 9, 6, 2, 5, 3, 7, 8]
  invFun := ![1, 0, 5, 7, 2, 6, 4, 8, 9, 3]
  left_inv := by decide
  right_inv := by decide

def sigma4 : Equiv.Perm (Fin 10) where
  toFun := ![4, 0, 1, 6, 9, 3, 5, 2, 8, 7]
  invFun := ![1, 2, 7, 5, 0, 6, 3, 9, 8, 4]
  left_inv := by decide
  right_inv := by decide

def sigma5 : Equiv.Perm (Fin 10) where
  toFun := ![4, 0, 1, 2, 3, 9, 5, 6, 7, 8]
  invFun := ![1, 2, 3, 4, 0, 6, 7, 8, 9, 5]
  left_inv := by decide
  right_inv := by decide

def sigma6 : Equiv.Perm (Fin 10) where
  toFun := ![0, 4, 3, 2, 1, 5, 9, 8, 7, 6]
  invFun := ![0, 4, 3, 2, 1, 5, 9, 8, 7, 6]
  left_inv := by decide
  right_inv := by decide

def sigma7 : Equiv.Perm (Fin 10) where
  toFun := ![1, 0, 4, 3, 2, 6, 5, 9, 8, 7]
  invFun := ![1, 0, 4, 3, 2, 6, 5, 9, 8, 7]
  left_inv := by decide
  right_inv := by decide

def sigma8 : Equiv.Perm (Fin 10) where
  toFun := ![2, 1, 0, 4, 3, 7, 6, 5, 9, 8]
  invFun := ![2, 1, 0, 4, 3, 7, 6, 5, 9, 8]
  left_inv := by decide
  right_inv := by decide

def sigma9 : Equiv.Perm (Fin 10) where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
  left_inv := by decide
  right_inv := by decide

lemma pet_transitive (j : Fin 10) :
    ∃ s : Equiv.Perm (Fin 10), (∀ x : Fin 10 → Bool, pet (x ∘ s) = pet x) ∧
      s j = Fin.last 9 := by
  fin_cases j
  · refine ⟨sigma0, ?_, by decide⟩
    intro x
    change (((x 9 && x 4) || (x 9 && x 7) || (x 7 && x 5)) || (((x 4 && x 0) || (x 4 && x 3) || (x 3 && x 2)) || (((x 0 && x 1) || (x 0 && x 5) || (x 5 && x 8)) || (((x 1 && x 6) || (x 1 && x 2) || (x 2 && x 7)) || (((x 6 && x 9) || (x 6 && x 8) || (x 8 && x 3)) || false))))) = (((x 0 && x 1) || (x 0 && x 5) || (x 5 && x 7)) || (((x 1 && x 2) || (x 1 && x 6) || (x 6 && x 8)) || (((x 2 && x 3) || (x 2 && x 7) || (x 7 && x 9)) || (((x 3 && x 4) || (x 3 && x 8) || (x 8 && x 5)) || (((x 4 && x 0) || (x 4 && x 9) || (x 9 && x 6)) || false)))))
    simp only [Bool.or_false] <;> ac_rfl
  · refine ⟨sigma1, ?_, by decide⟩
    intro x
    change (((x 4 && x 9) || (x 4 && x 3) || (x 3 && x 8)) || (((x 9 && x 6) || (x 9 && x 7) || (x 7 && x 2)) || (((x 6 && x 1) || (x 6 && x 8) || (x 8 && x 5)) || (((x 1 && x 0) || (x 1 && x 2) || (x 2 && x 3)) || (((x 0 && x 4) || (x 0 && x 5) || (x 5 && x 7)) || false))))) = (((x 0 && x 1) || (x 0 && x 5) || (x 5 && x 7)) || (((x 1 && x 2) || (x 1 && x 6) || (x 6 && x 8)) || (((x 2 && x 3) || (x 2 && x 7) || (x 7 && x 9)) || (((x 3 && x 4) || (x 3 && x 8) || (x 8 && x 5)) || (((x 4 && x 0) || (x 4 && x 9) || (x 9 && x 6)) || false)))))
    simp only [Bool.or_false] <;> ac_rfl
  · refine ⟨sigma2, ?_, by decide⟩
    intro x
    change (((x 0 && x 4) || (x 0 && x 5) || (x 5 && x 7)) || (((x 4 && x 9) || (x 4 && x 3) || (x 3 && x 8)) || (((x 9 && x 6) || (x 9 && x 7) || (x 7 && x 2)) || (((x 6 && x 1) || (x 6 && x 8) || (x 8 && x 5)) || (((x 1 && x 0) || (x 1 && x 2) || (x 2 && x 3)) || false))))) = (((x 0 && x 1) || (x 0 && x 5) || (x 5 && x 7)) || (((x 1 && x 2) || (x 1 && x 6) || (x 6 && x 8)) || (((x 2 && x 3) || (x 2 && x 7) || (x 7 && x 9)) || (((x 3 && x 4) || (x 3 && x 8) || (x 8 && x 5)) || (((x 4 && x 0) || (x 4 && x 9) || (x 9 && x 6)) || false)))))
    simp only [Bool.or_false] <;> ac_rfl
  · refine ⟨sigma3, ?_, by decide⟩
    intro x
    change (((x 1 && x 0) || (x 1 && x 2) || (x 2 && x 3)) || (((x 0 && x 4) || (x 0 && x 5) || (x 5 && x 7)) || (((x 4 && x 9) || (x 4 && x 3) || (x 3 && x 8)) || (((x 9 && x 6) || (x 9 && x 7) || (x 7 && x 2)) || (((x 6 && x 1) || (x 6 && x 8) || (x 8 && x 5)) || false))))) = (((x 0 && x 1) || (x 0 && x 5) || (x 5 && x 7)) || (((x 1 && x 2) || (x 1 && x 6) || (x 6 && x 8)) || (((x 2 && x 3) || (x 2 && x 7) || (x 7 && x 9)) || (((x 3 && x 4) || (x 3 && x 8) || (x 8 && x 5)) || (((x 4 && x 0) || (x 4 && x 9) || (x 9 && x 6)) || false)))))
    simp only [Bool.or_false] <;> ac_rfl
  · refine ⟨sigma4, ?_, by decide⟩
    intro x
    change (((x 4 && x 0) || (x 4 && x 3) || (x 3 && x 2)) || (((x 0 && x 1) || (x 0 && x 5) || (x 5 && x 8)) || (((x 1 && x 6) || (x 1 && x 2) || (x 2 && x 7)) || (((x 6 && x 9) || (x 6 && x 8) || (x 8 && x 3)) || (((x 9 && x 4) || (x 9 && x 7) || (x 7 && x 5)) || false))))) = (((x 0 && x 1) || (x 0 && x 5) || (x 5 && x 7)) || (((x 1 && x 2) || (x 1 && x 6) || (x 6 && x 8)) || (((x 2 && x 3) || (x 2 && x 7) || (x 7 && x 9)) || (((x 3 && x 4) || (x 3 && x 8) || (x 8 && x 5)) || (((x 4 && x 0) || (x 4 && x 9) || (x 9 && x 6)) || false)))))
    simp only [Bool.or_false] <;> ac_rfl
  · refine ⟨sigma5, ?_, by decide⟩
    intro x
    change (((x 4 && x 0) || (x 4 && x 9) || (x 9 && x 6)) || (((x 0 && x 1) || (x 0 && x 5) || (x 5 && x 7)) || (((x 1 && x 2) || (x 1 && x 6) || (x 6 && x 8)) || (((x 2 && x 3) || (x 2 && x 7) || (x 7 && x 9)) || (((x 3 && x 4) || (x 3 && x 8) || (x 8 && x 5)) || false))))) = (((x 0 && x 1) || (x 0 && x 5) || (x 5 && x 7)) || (((x 1 && x 2) || (x 1 && x 6) || (x 6 && x 8)) || (((x 2 && x 3) || (x 2 && x 7) || (x 7 && x 9)) || (((x 3 && x 4) || (x 3 && x 8) || (x 8 && x 5)) || (((x 4 && x 0) || (x 4 && x 9) || (x 9 && x 6)) || false)))))
    simp only [Bool.or_false] <;> ac_rfl
  · refine ⟨sigma6, ?_, by decide⟩
    intro x
    change (((x 0 && x 4) || (x 0 && x 5) || (x 5 && x 8)) || (((x 4 && x 3) || (x 4 && x 9) || (x 9 && x 7)) || (((x 3 && x 2) || (x 3 && x 8) || (x 8 && x 6)) || (((x 2 && x 1) || (x 2 && x 7) || (x 7 && x 5)) || (((x 1 && x 0) || (x 1 && x 6) || (x 6 && x 9)) || false))))) = (((x 0 && x 1) || (x 0 && x 5) || (x 5 && x 7)) || (((x 1 && x 2) || (x 1 && x 6) || (x 6 && x 8)) || (((x 2 && x 3) || (x 2 && x 7) || (x 7 && x 9)) || (((x 3 && x 4) || (x 3 && x 8) || (x 8 && x 5)) || (((x 4 && x 0) || (x 4 && x 9) || (x 9 && x 6)) || false)))))
    simp only [Bool.or_false] <;> ac_rfl
  · refine ⟨sigma7, ?_, by decide⟩
    intro x
    change (((x 1 && x 0) || (x 1 && x 6) || (x 6 && x 9)) || (((x 0 && x 4) || (x 0 && x 5) || (x 5 && x 8)) || (((x 4 && x 3) || (x 4 && x 9) || (x 9 && x 7)) || (((x 3 && x 2) || (x 3 && x 8) || (x 8 && x 6)) || (((x 2 && x 1) || (x 2 && x 7) || (x 7 && x 5)) || false))))) = (((x 0 && x 1) || (x 0 && x 5) || (x 5 && x 7)) || (((x 1 && x 2) || (x 1 && x 6) || (x 6 && x 8)) || (((x 2 && x 3) || (x 2 && x 7) || (x 7 && x 9)) || (((x 3 && x 4) || (x 3 && x 8) || (x 8 && x 5)) || (((x 4 && x 0) || (x 4 && x 9) || (x 9 && x 6)) || false)))))
    simp only [Bool.or_false] <;> ac_rfl
  · refine ⟨sigma8, ?_, by decide⟩
    intro x
    change (((x 2 && x 1) || (x 2 && x 7) || (x 7 && x 5)) || (((x 1 && x 0) || (x 1 && x 6) || (x 6 && x 9)) || (((x 0 && x 4) || (x 0 && x 5) || (x 5 && x 8)) || (((x 4 && x 3) || (x 4 && x 9) || (x 9 && x 7)) || (((x 3 && x 2) || (x 3 && x 8) || (x 8 && x 6)) || false))))) = (((x 0 && x 1) || (x 0 && x 5) || (x 5 && x 7)) || (((x 1 && x 2) || (x 1 && x 6) || (x 6 && x 8)) || (((x 2 && x 3) || (x 2 && x 7) || (x 7 && x 9)) || (((x 3 && x 4) || (x 3 && x 8) || (x 8 && x 5)) || (((x 4 && x 0) || (x 4 && x 9) || (x 9 && x 6)) || false)))))
    simp only [Bool.or_false] <;> ac_rfl
  · refine ⟨sigma9, ?_, by decide⟩
    intro x
    change (((x 0 && x 1) || (x 0 && x 5) || (x 5 && x 7)) || (((x 1 && x 2) || (x 1 && x 6) || (x 6 && x 8)) || (((x 2 && x 3) || (x 2 && x 7) || (x 7 && x 9)) || (((x 3 && x 4) || (x 3 && x 8) || (x 8 && x 5)) || (((x 4 && x 0) || (x 4 && x 9) || (x 9 && x 6)) || false))))) = (((x 0 && x 1) || (x 0 && x 5) || (x 5 && x 7)) || (((x 1 && x 2) || (x 1 && x 6) || (x 6 && x 8)) || (((x 2 && x 3) || (x 2 && x 7) || (x 7 && x 9)) || (((x 3 && x 4) || (x 3 && x 8) || (x 8 && x 5)) || (((x 4 && x 0) || (x 4 && x 9) || (x 9 && x 6)) || false)))))
    simp only [Bool.or_false] <;> ac_rfl

lemma promise_essential (U : (Fin 10 → Bool) → Bool)
    (h : ∀ x : Fin 10 → Bool, pet x = false ∨ (List.ofFn x).count true ≤ 2 → U x = pet x)
    (i : Fin 10) : ∃ x : Fin 10 → Bool, U (Function.update x i (!x i)) ≠ U x := by
  fin_cases i
  · let x : Fin 10 → Bool := ![false, true, false, false, false, false, false, false, false, false]
    refine ⟨x, ?_⟩
    change U (Function.update x 0 (!x 0)) ≠ U x
    rw [h (Function.update x 0 (!x 0)) (Or.inr (by decide)), h x (Or.inr (by decide))]
    decide
  · let x : Fin 10 → Bool := ![true, false, false, false, false, false, false, false, false, false]
    refine ⟨x, ?_⟩
    change U (Function.update x 1 (!x 1)) ≠ U x
    rw [h (Function.update x 1 (!x 1)) (Or.inr (by decide)), h x (Or.inr (by decide))]
    decide
  · let x : Fin 10 → Bool := ![false, true, false, false, false, false, false, false, false, false]
    refine ⟨x, ?_⟩
    change U (Function.update x 2 (!x 2)) ≠ U x
    rw [h (Function.update x 2 (!x 2)) (Or.inr (by decide)), h x (Or.inr (by decide))]
    decide
  · let x : Fin 10 → Bool := ![false, false, true, false, false, false, false, false, false, false]
    refine ⟨x, ?_⟩
    change U (Function.update x 3 (!x 3)) ≠ U x
    rw [h (Function.update x 3 (!x 3)) (Or.inr (by decide)), h x (Or.inr (by decide))]
    decide
  · let x : Fin 10 → Bool := ![false, false, false, true, false, false, false, false, false, false]
    refine ⟨x, ?_⟩
    change U (Function.update x 4 (!x 4)) ≠ U x
    rw [h (Function.update x 4 (!x 4)) (Or.inr (by decide)), h x (Or.inr (by decide))]
    decide
  · let x : Fin 10 → Bool := ![true, false, false, false, false, false, false, false, false, false]
    refine ⟨x, ?_⟩
    change U (Function.update x 5 (!x 5)) ≠ U x
    rw [h (Function.update x 5 (!x 5)) (Or.inr (by decide)), h x (Or.inr (by decide))]
    decide
  · let x : Fin 10 → Bool := ![false, true, false, false, false, false, false, false, false, false]
    refine ⟨x, ?_⟩
    change U (Function.update x 6 (!x 6)) ≠ U x
    rw [h (Function.update x 6 (!x 6)) (Or.inr (by decide)), h x (Or.inr (by decide))]
    decide
  · let x : Fin 10 → Bool := ![false, false, false, false, false, true, false, false, false, false]
    refine ⟨x, ?_⟩
    change U (Function.update x 7 (!x 7)) ≠ U x
    rw [h (Function.update x 7 (!x 7)) (Or.inr (by decide)), h x (Or.inr (by decide))]
    decide
  · let x : Fin 10 → Bool := ![false, false, false, false, false, false, true, false, false, false]
    refine ⟨x, ?_⟩
    change U (Function.update x 8 (!x 8)) ≠ U x
    rw [h (Function.update x 8 (!x 8)) (Or.inr (by decide)), h x (Or.inr (by decide))]
    decide
  · let x : Fin 10 → Bool := ![false, false, false, false, false, false, false, true, false, false]
    refine ⟨x, ?_⟩
    change U (Function.update x 9 (!x 9)) ≠ U x
    rw [h (Function.update x 9 (!x 9)) (Or.inr (by decide)), h x (Or.inr (by decide))]
    decide

lemma promise_cofactors_nonconstant (U : (Fin 10 → Bool) → Bool)
    (h : ∀ x : Fin 10 → Bool, pet x = false ∨ (List.ofFn x).count true ≤ 2 → U x = pet x)
    (i : Fin 10) (b : Bool) :
    ∃ x y : Fin 10 → Bool, U (Function.update x i b) ≠ U (Function.update y i b) := by
  fin_cases i <;> cases b
  · let x : Fin 10 → Bool := ![false, false, false, false, false, true, false, true, false, false]
    let y : Fin 10 → Bool := fun _ => false
    refine ⟨x, y, ?_⟩
    change U (Function.update x 0 false) ≠ U (Function.update y 0 false)
    rw [h (Function.update x 0 false) (Or.inr (by decide)),
      h (Function.update y 0 false) (Or.inr (by decide))]
    decide
  · let x : Fin 10 → Bool := ![true, true, false, false, false, false, false, false, false, false]
    let y : Fin 10 → Bool := fun _ => false
    refine ⟨x, y, ?_⟩
    change U (Function.update x 0 true) ≠ U (Function.update y 0 true)
    rw [h (Function.update x 0 true) (Or.inr (by decide)),
      h (Function.update y 0 true) (Or.inr (by decide))]
    decide
  · let x : Fin 10 → Bool := ![true, false, false, false, false, true, false, false, false, false]
    let y : Fin 10 → Bool := fun _ => false
    refine ⟨x, y, ?_⟩
    change U (Function.update x 1 false) ≠ U (Function.update y 1 false)
    rw [h (Function.update x 1 false) (Or.inr (by decide)),
      h (Function.update y 1 false) (Or.inr (by decide))]
    decide
  · let x : Fin 10 → Bool := ![true, true, false, false, false, false, false, false, false, false]
    let y : Fin 10 → Bool := fun _ => false
    refine ⟨x, y, ?_⟩
    change U (Function.update x 1 true) ≠ U (Function.update y 1 true)
    rw [h (Function.update x 1 true) (Or.inr (by decide)),
      h (Function.update y 1 true) (Or.inr (by decide))]
    decide
  · let x : Fin 10 → Bool := ![true, true, false, false, false, false, false, false, false, false]
    let y : Fin 10 → Bool := fun _ => false
    refine ⟨x, y, ?_⟩
    change U (Function.update x 2 false) ≠ U (Function.update y 2 false)
    rw [h (Function.update x 2 false) (Or.inr (by decide)),
      h (Function.update y 2 false) (Or.inr (by decide))]
    decide
  · let x : Fin 10 → Bool := ![false, true, true, false, false, false, false, false, false, false]
    let y : Fin 10 → Bool := fun _ => false
    refine ⟨x, y, ?_⟩
    change U (Function.update x 2 true) ≠ U (Function.update y 2 true)
    rw [h (Function.update x 2 true) (Or.inr (by decide)),
      h (Function.update y 2 true) (Or.inr (by decide))]
    decide
  · let x : Fin 10 → Bool := ![true, true, false, false, false, false, false, false, false, false]
    let y : Fin 10 → Bool := fun _ => false
    refine ⟨x, y, ?_⟩
    change U (Function.update x 3 false) ≠ U (Function.update y 3 false)
    rw [h (Function.update x 3 false) (Or.inr (by decide)),
      h (Function.update y 3 false) (Or.inr (by decide))]
    decide
  · let x : Fin 10 → Bool := ![false, false, true, true, false, false, false, false, false, false]
    let y : Fin 10 → Bool := fun _ => false
    refine ⟨x, y, ?_⟩
    change U (Function.update x 3 true) ≠ U (Function.update y 3 true)
    rw [h (Function.update x 3 true) (Or.inr (by decide)),
      h (Function.update y 3 true) (Or.inr (by decide))]
    decide
  · let x : Fin 10 → Bool := ![true, true, false, false, false, false, false, false, false, false]
    let y : Fin 10 → Bool := fun _ => false
    refine ⟨x, y, ?_⟩
    change U (Function.update x 4 false) ≠ U (Function.update y 4 false)
    rw [h (Function.update x 4 false) (Or.inr (by decide)),
      h (Function.update y 4 false) (Or.inr (by decide))]
    decide
  · let x : Fin 10 → Bool := ![false, false, false, true, true, false, false, false, false, false]
    let y : Fin 10 → Bool := fun _ => false
    refine ⟨x, y, ?_⟩
    change U (Function.update x 4 true) ≠ U (Function.update y 4 true)
    rw [h (Function.update x 4 true) (Or.inr (by decide)),
      h (Function.update y 4 true) (Or.inr (by decide))]
    decide
  · let x : Fin 10 → Bool := ![true, true, false, false, false, false, false, false, false, false]
    let y : Fin 10 → Bool := fun _ => false
    refine ⟨x, y, ?_⟩
    change U (Function.update x 5 false) ≠ U (Function.update y 5 false)
    rw [h (Function.update x 5 false) (Or.inr (by decide)),
      h (Function.update y 5 false) (Or.inr (by decide))]
    decide
  · let x : Fin 10 → Bool := ![true, false, false, false, false, true, false, false, false, false]
    let y : Fin 10 → Bool := fun _ => false
    refine ⟨x, y, ?_⟩
    change U (Function.update x 5 true) ≠ U (Function.update y 5 true)
    rw [h (Function.update x 5 true) (Or.inr (by decide)),
      h (Function.update y 5 true) (Or.inr (by decide))]
    decide
  · let x : Fin 10 → Bool := ![true, true, false, false, false, false, false, false, false, false]
    let y : Fin 10 → Bool := fun _ => false
    refine ⟨x, y, ?_⟩
    change U (Function.update x 6 false) ≠ U (Function.update y 6 false)
    rw [h (Function.update x 6 false) (Or.inr (by decide)),
      h (Function.update y 6 false) (Or.inr (by decide))]
    decide
  · let x : Fin 10 → Bool := ![false, true, false, false, false, false, true, false, false, false]
    let y : Fin 10 → Bool := fun _ => false
    refine ⟨x, y, ?_⟩
    change U (Function.update x 6 true) ≠ U (Function.update y 6 true)
    rw [h (Function.update x 6 true) (Or.inr (by decide)),
      h (Function.update y 6 true) (Or.inr (by decide))]
    decide
  · let x : Fin 10 → Bool := ![true, true, false, false, false, false, false, false, false, false]
    let y : Fin 10 → Bool := fun _ => false
    refine ⟨x, y, ?_⟩
    change U (Function.update x 7 false) ≠ U (Function.update y 7 false)
    rw [h (Function.update x 7 false) (Or.inr (by decide)),
      h (Function.update y 7 false) (Or.inr (by decide))]
    decide
  · let x : Fin 10 → Bool := ![false, false, false, false, false, true, false, true, false, false]
    let y : Fin 10 → Bool := fun _ => false
    refine ⟨x, y, ?_⟩
    change U (Function.update x 7 true) ≠ U (Function.update y 7 true)
    rw [h (Function.update x 7 true) (Or.inr (by decide)),
      h (Function.update y 7 true) (Or.inr (by decide))]
    decide
  · let x : Fin 10 → Bool := ![true, true, false, false, false, false, false, false, false, false]
    let y : Fin 10 → Bool := fun _ => false
    refine ⟨x, y, ?_⟩
    change U (Function.update x 8 false) ≠ U (Function.update y 8 false)
    rw [h (Function.update x 8 false) (Or.inr (by decide)),
      h (Function.update y 8 false) (Or.inr (by decide))]
    decide
  · let x : Fin 10 → Bool := ![false, false, false, false, false, false, true, false, true, false]
    let y : Fin 10 → Bool := fun _ => false
    refine ⟨x, y, ?_⟩
    change U (Function.update x 8 true) ≠ U (Function.update y 8 true)
    rw [h (Function.update x 8 true) (Or.inr (by decide)),
      h (Function.update y 8 true) (Or.inr (by decide))]
    decide
  · let x : Fin 10 → Bool := ![true, true, false, false, false, false, false, false, false, false]
    let y : Fin 10 → Bool := fun _ => false
    refine ⟨x, y, ?_⟩
    change U (Function.update x 9 false) ≠ U (Function.update y 9 false)
    rw [h (Function.update x 9 false) (Or.inr (by decide)),
      h (Function.update y 9 false) (Or.inr (by decide))]
    decide
  · let x : Fin 10 → Bool := ![false, false, false, false, false, false, false, true, false, true]
    let y : Fin 10 → Bool := fun _ => false
    refine ⟨x, y, ?_⟩
    change U (Function.update x 9 true) ≠ U (Function.update y 9 true)
    rw [h (Function.update x 9 true) (Or.inr (by decide)),
      h (Function.update y 9 true) (Or.inr (by decide))]
    decide

end PEqualNP.Outside.L_meta_3821_aux
