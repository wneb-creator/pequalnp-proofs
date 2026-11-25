import Mathlib.Data.Bool.Basic

namespace PEqualNP.Outside.L_meta_2590.EdgeAnd

def pair {α : Type} [DecidableEq α] (u v : α) : α → Bool :=
  fun i => decide (i = u ∨ i = v)

def raw {α : Type} (u v : α) (x : α → Bool) : Bool := x u && x v

lemma intersect_raw {α : Type} [DecidableEq α] {u v : α} (hne : u ≠ v)
    (h : (α → Bool) → Bool)
    (mono : ∀ x y, (∀ i, x i = true → y i = true) → h x = true → h y = true) :
    (fun x => raw u v x && h x) = raw u v ∨
      ∀ a b : α, (raw u v (pair a b) && h (pair a b)) = false := by
  by_cases hh : h (pair u v) = true
  · left
    funext x
    by_cases hx : raw u v x = true
    · have huv : x u = true ∧ x v = true := Bool.and_eq_true_iff.mp hx
      have hhx : h x = true := mono (pair u v) x (by
        intro i hi
        simp only [pair, decide_eq_true_eq] at hi
        rcases hi with rfl | rfl
        · exact huv.1
        · exact huv.2) hh
      rw [hx, hhx]
      rfl
    · cases he : raw u v x <;> simp_all
  · right
    intro a b
    cases he : raw u v (pair a b) && h (pair a b) with
    | false => rfl
    | true =>
      have hp := Bool.and_eq_true_iff.mp he
      have huv := Bool.and_eq_true_iff.mp hp.1
      have hu : u = a ∨ u = b := by simpa only [pair, decide_eq_true_eq] using huv.1
      have hv : v = a ∨ v = b := by simpa only [pair, decide_eq_true_eq] using huv.2
      have eq : pair a b = pair u v := by
        rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
        · exact False.elim (hne rfl)
        · rfl
        · funext i
          simp only [pair, or_comm]
        · exact False.elim (hne rfl)
      exact False.elim (hh (eq ▸ hp.2))

lemma fresh_productive_cannot_intersect_raw {α : Type} [DecidableEq α]
    {u v : α} (hne : u ≠ v) (h : (α → Bool) → Bool)
    (mono : ∀ x y, (∀ i, x i = true → y i = true) → h x = true → h y = true)
    (fresh : (fun x => raw u v x && h x) ≠ raw u v)
    (productive : ∃ a b : α, (raw u v (pair a b) && h (pair a b)) = true) : False := by
  rcases intersect_raw hne h mono with absorbed | killed
  · exact fresh absorbed
  · obtain ⟨a, b, hab⟩ := productive
    rw [killed a b] at hab
    contradiction

end PEqualNP.Outside.L_meta_2590.EdgeAnd
