import Mathlib

namespace PEqualNP.Outside.L_meta_1884

lemma move_or_to_output (a b : Bool) (continuation : Bool → Bool)
    (certified : b = true → continuation (a || b) = true) :
    continuation (a || b) = (continuation a || b) := by
  cases hb : b with
  | false => simp
  | true => simpa [hb] using certified hb

lemma move_and_to_output (a b : Bool) (continuation : Bool → Bool)
    (certified : b = false → continuation (a && b) = false) :
    continuation (a && b) = (continuation a && b) := by
  cases hb : b with
  | false => simpa [hb] using certified hb
  | true => simp

def edgeValueFrom {n : Nat} (edges : List (Fin n × Fin n))
    (x : Fin n → Bool) : Bool :=
  edges.any (fun e => x e.1 && x e.2)

lemma edge_tests_complete {n : Nat} (edges : List (Fin n × Fin n))
    (G : (Fin n → Bool) → Bool) (mono : Monotone G)
    (below : ∀ x, G x ≤ edgeValueFrom edges x)
    (tests : ∀ e ∈ edges, G (fun i => decide (i = e.1 ∨ i = e.2)) = true) :
    ∀ x, G x = edgeValueFrom edges x := by
  intro x
  apply le_antisymm (below x)
  apply Bool.le_iff_imp.mpr
  intro hx
  obtain ⟨e, he, hv⟩ := List.any_eq_true.mp hx
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hv
  have pair_le : (fun i => decide (i = e.1 ∨ i = e.2)) ≤ x := by
    intro i
    apply Bool.le_iff_imp.mpr
    intro hi
    rcases of_decide_eq_true hi with rfl | rfl
    · exact h1
    · exact h2
  exact Bool.le_iff_imp.mp (mono pair_le) (tests e he)

def pinnedEdgeInput {n : Nat} (p : Fin n) (b : Bool)
    (e : Fin n × Fin n) : Fin n → Bool :=
  fun i => if i = p then b else decide (i = e.1 ∨ i = e.2)

lemma pinned_edge_tests_complete {n : Nat} (edges : List (Fin n × Fin n))
    (p : Fin n) (G : (Fin n → Bool) → Bool)
    (mono : ∀ x y : Fin n → Bool, x p = y p → x ≤ y → G x ≤ G y)
    (below : ∀ x, G x ≤ edgeValueFrom edges x)
    (tests : ∀ e ∈ edges, ∀ b : Bool,
      G (pinnedEdgeInput p b e) = edgeValueFrom edges (pinnedEdgeInput p b e)) :
    ∀ x, G x = edgeValueFrom edges x := by
  intro x
  apply le_antisymm (below x)
  apply Bool.le_iff_imp.mpr
  intro hx
  obtain ⟨e, he, hv⟩ := List.any_eq_true.mp hx
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hv
  let y := pinnedEdgeInput p (x p) e
  have yp : y p = x p := by simp [y, pinnedEdgeInput]
  have yle : y ≤ x := by
    intro i
    by_cases hi : i = p
    · subst i
      exact le_of_eq yp
    · apply Bool.le_iff_imp.mpr
      intro hy
      have hy' : decide (i = e.1 ∨ i = e.2) = true := by
        simpa [y, pinnedEdgeInput, hi] using hy
      rcases of_decide_eq_true hy' with rfl | rfl
      · exact h1
      · exact h2
  have y1 : y e.1 = true := by
    by_cases h : e.1 = p
    · simpa [y, pinnedEdgeInput, h] using h1
    · simp [y, pinnedEdgeInput, h]
  have y2 : y e.2 = true := by
    by_cases h : e.2 = p
    · simpa [y, pinnedEdgeInput, h] using h2
    · simp [y, pinnedEdgeInput, h]
  have target_y : edgeValueFrom edges y = true :=
    List.any_eq_true.mpr ⟨e, he, by simp [y1, y2]⟩
  have gy : G y = true := (tests e he (x p)).trans target_y
  exact Bool.le_iff_imp.mp (mono y x yp yle) gy

end PEqualNP.Outside.L_meta_1884
