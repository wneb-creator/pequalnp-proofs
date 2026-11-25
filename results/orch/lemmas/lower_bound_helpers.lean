import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux

lemma erase_last_not_true {α : Type*} (f h : α → Bool) (G : α → Bool → Bool)
    (correct : ∀ x, G x (!h x) = f x)
    (mono : ∀ x, Monotone (G x))
    (contained : ∀ x, h x = true → f x = true) :
    ∀ x, G x true = f x := by
  intro x
  cases hh : h x with
  | false => simpa only [hh, Bool.not_false] using correct x
  | true =>
    have hc : G x false = true := by
      simpa only [hh, Bool.not_true, contained x hh] using correct x
    have hm := mono x (show false ≤ true by decide)
    rw [hc] at hm
    rw [contained x hh]
    cases hg : G x true <;> simp_all
    exact (by decide : ¬ ((true : Bool) ≤ false)) hm

lemma erase_last_not_false {α : Type*} (f h : α → Bool) (G : α → Bool → Bool)
    (correct : ∀ x, G x (!h x) = f x)
    (mono : ∀ x, Monotone (G x))
    (contained : ∀ x, f x = true → h x = true) :
    ∀ x, G x false = f x := by
  intro x
  cases hh : h x with
  | true => simpa only [hh, Bool.not_true] using correct x
  | false =>
    have hf : f x = false := by
      cases hfx : f x <;> simp_all
    have hc : G x true = false := by
      simpa only [hh, Bool.not_false, hf] using correct x
    have hm := mono x (show false ≤ true by decide)
    rw [hc] at hm
    rw [hf]
    cases hg : G x false <;> simp_all
    exact (by decide : ¬ ((true : Bool) ≤ false)) hm


def petersen (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def moveZero : Fin 10 → Fin 10 → Fin 10 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
    ![1, 2, 3, 4, 0, 6, 7, 8, 9, 5],
    ![2, 3, 4, 0, 1, 7, 8, 9, 5, 6],
    ![3, 4, 0, 1, 2, 8, 9, 5, 6, 7],
    ![4, 0, 1, 2, 3, 9, 5, 6, 7, 8],
    ![5, 7, 9, 6, 8, 0, 2, 4, 1, 3],
    ![6, 8, 5, 7, 9, 1, 3, 0, 2, 4],
    ![7, 9, 6, 8, 5, 2, 4, 1, 3, 0],
    ![8, 5, 7, 9, 6, 3, 0, 2, 4, 1],
    ![9, 6, 8, 5, 7, 4, 1, 3, 0, 2]]

lemma moveZero_zero : ∀ v : Fin 10, moveZero v 0 = v := by
  decide +kernel

lemma moveZero_bijective : ∀ v : Fin 10, Function.Bijective (moveZero v) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma petersen_moveZero : ∀ (v : Fin 10) (x : Fin 10 → Bool),
    petersen (fun i => x (moveZero v i)) = petersen x := by
  decide +kernel

end PEqualNP.Outside.L_meta_2592_aux
