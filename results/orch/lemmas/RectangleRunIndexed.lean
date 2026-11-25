import RectangleRun

namespace PEqualNP.Outside.L_meta_2373.RectangleRun

open Live1024

lemma map_sum_le {α : Type} (xs : List α) (f g : α → Int)
    (h : ∀ a ∈ xs, f a ≤ g a) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons a rest ih =>
    have one := h a (by simp)
    have tail := ih (fun v hv => h v (by simp [hv]))
    simpa only [List.map_cons, List.sum_cons] using add_le_add one tail

lemma tight_run_indexed {R α : Type} {p q : Nat} (P : Fin p → R) (N : Fin q → R)
    (weight : Fin p → Fin q → Int) (raw : α → Wire R) (caps : α → Int)
    (labels : List α) {goal k} (trace : Run false goal k (labels.map raw))
    (tight : labels.length = k + 1)
    (leaves : ∀ i ∈ labels, Bounds P N weight (raw i) (caps i)) :
    Bounds P N weight goal (labels.map caps).sum := by
  intro S T hs ht
  have bound := tight_run_bound P N weight trace (by simpa using tight) S T hs ht
  have leafsum : ((labels.map raw).map (measure P N weight)).sum ≤ (labels.map caps).sum := by
    rw [List.map_map]
    apply map_sum_le
    intro i hi
    exact measure_le (leaves i hi)
  exact bound.trans leafsum

end PEqualNP.Outside.L_meta_2373.RectangleRun
