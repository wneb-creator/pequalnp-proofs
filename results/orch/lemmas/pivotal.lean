import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1884

def edgeFunction (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def adjacent (i j : Fin 10) : Bool :=
  (([50, 69, 138, 276, 521, 385, 770, 548, 104, 208] : List ℕ).getD i.val 0).testBit j.val

set_option maxRecDepth 16000 in
set_option maxHeartbeats 3000000 in
lemma pivotalWitness : ∀ (i j k : Fin 10) (a b : Bool),
    i ≠ j → i ≠ k → j ≠ k → ¬ (a = true ∧ b = true ∧ adjacent j k = true) →
    ∃ l : Fin 10, ∀ z : Bool,
      edgeFunction (fun t => if t = i then z else if t = j then a else
        if t = k then b else decide (t = l)) = z := by
  decide +kernel

lemma pivotal (i j k : Fin 10) (a b : Bool)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (pins : ¬ (a = true ∧ b = true ∧ adjacent j k = true)) :
    ∃ x : Fin 10 → Bool, x j = a ∧ x k = b ∧
      ∀ z : Bool, edgeFunction (Function.update x i z) = z := by
  obtain ⟨l, hl⟩ := pivotalWitness i j k a b hij hik hjk pins
  let x : Fin 10 → Bool := fun t => if t = i then false else if t = j then a else
    if t = k then b else decide (t = l)
  refine ⟨x, by simp [x, Ne.symm hij], by simp [x, Ne.symm hik, Ne.symm hjk], ?_⟩
  intro z
  have update_eq : Function.update x i z =
      (fun t => if t = i then z else if t = j then a else
        if t = k then b else decide (t = l)) := by
    funext t
    by_cases h : t = i
    · subst t
      simp
    · simp [Function.update_of_ne h, x, h]
  rw [update_eq]
  exact hl z

end PEqualNP.Outside.L_meta_1884
