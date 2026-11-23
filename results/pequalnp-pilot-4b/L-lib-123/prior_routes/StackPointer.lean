import Mathlib

namespace PriorRoutes

def stackCells (push : ℕ → Option Bool) (height : ℕ → ℕ) : ℕ → ℕ → Bool
  | 0 => fun _ => false
  | t + 1 => match push t with
    | none => stackCells push height t
    | some bit => Function.update (stackCells push height t) (height t) bit

lemma stackCells_push (push : ℕ → Option Bool) (height : ℕ → ℕ)
    (p : ℕ) (bit : Bool) (hp : push p = some bit) :
    stackCells push height (p + 1) (height p) = bit := by
  simp [stackCells, hp]

lemma stackCells_unchanged (push : ℕ → Option Bool) (height : ℕ → ℕ)
    (t index : ℕ) (hne : index ≠ height t) :
    stackCells push height (t + 1) index = stackCells push height t index := by
  simp only [stackCells]
  cases push t with
  | none => rfl
  | some bit => exact Function.update_of_ne hne _ _

lemma stackPointer_sound (push : ℕ → Option Bool) (height : ℕ → ℕ)
    (p t : ℕ) (bit : Bool) (hpt : p < t) (hp : push p = some bit)
    (hinterval : ∀ u, p < u → u ≤ t → height p < height u) :
    stackCells push height t (height p) = bit := by
  have hbase := stackCells_push push height p bit hp
  have hpreserve : ∀ u, p + 1 ≤ u → u ≤ t →
      stackCells push height u (height p) = bit := by
    intro u hu
    induction u, hu using Nat.le_induction with
    | base => intro _; exact hbase
    | succ u hu ih =>
      intro hut
      have hne : height p ≠ height u := Nat.ne_of_lt (hinterval u (by omega) (by omega))
      rw [stackCells_unchanged push height u (height p) hne]
      exact ih (by omega)
  exact hpreserve t (by omega) le_rfl

lemma stackPointer_top (push : ℕ → Option Bool) (height : ℕ → ℕ)
    (p t : ℕ) (bit : Bool) (hpt : p < t) (hp : push p = some bit)
    (hinterval : ∀ u, p < u → u ≤ t → height p < height u)
    (hheight : height t = height p + 1) :
    stackCells push height t (height t - 1) = bit := by
  have hind : height t - 1 = height p := by omega
  rw [hind]
  exact stackPointer_sound push height p t bit hpt hp hinterval

end PriorRoutes
