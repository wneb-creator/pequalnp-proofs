import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux.Negation

lemma remove_negation_true {α : Type} (f h : α → Bool) (G : α → Bool → Bool)
    (mono : ∀ x, G x false ≤ G x true)
    (correct : ∀ x, G x (!(h x)) = f x)
    (dominated : ∀ x, h x ≤ f x) : ∀ x, G x true = f x := by
  intro x
  have hm := mono x
  have hc := correct x
  have hd := dominated x
  cases hh : h x <;> cases hf : f x <;>
    cases hzero : G x false <;> cases hone : G x true <;> simp_all [Bool.le_iff_imp]

lemma remove_negation_false {α : Type} (f h : α → Bool) (G : α → Bool → Bool)
    (mono : ∀ x, G x false ≤ G x true)
    (correct : ∀ x, G x (!(h x)) = f x)
    (dominates : ∀ x, f x ≤ h x) : ∀ x, G x false = f x := by
  intro x
  have hm := mono x
  have hc := correct x
  have hd := dominates x
  cases hh : h x <;> cases hf : f x <;>
    cases hzero : G x false <;> cases hone : G x true <;> simp_all [Bool.le_iff_imp]

def edge (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def mask (n : ℕ) (i : Fin 10) : Bool := n.testBit i.val

def edges : List ℕ := [3, 6, 12, 24, 17, 33, 66, 132, 264, 528, 160, 640, 576, 320, 288]

def independent : List ℕ := [50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 1000000 in
lemma edge_mask : ∀ n ∈ edges, edge (mask n) = true := by
  decide +kernel

set_option maxRecDepth 2000 in
set_option maxHeartbeats 1000000 in
lemma independent_mask : ∀ n ∈ independent, edge (mask n) = false := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
lemma edge_witness : ∀ x : Fin 10 → Bool, edge x = true →
    ∃ n ∈ edges, mask n ≤ x := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
lemma independent_cover : ∀ x : Fin 10 → Bool, edge x = false →
    ∃ n ∈ independent, x ≤ mask n := by
  decide +kernel

lemma edge_le_iff (h : (Fin 10 → Bool) → Bool) (monotone : Monotone h) :
    (∀ x, edge x ≤ h x) ↔ ∀ n ∈ edges, h (mask n) = true := by
  constructor
  · intro dominated n hn
    have hx := dominated (mask n)
    rw [edge_mask n hn] at hx
    simpa [Bool.le_iff_imp] using hx
  · intro positive x
    cases hx : edge x with
    | false => simp
    | true =>
      obtain ⟨n, hn, hnx⟩ := edge_witness x hx
      have step := monotone hnx
      rw [positive n hn] at step
      simpa using step

lemma le_edge_iff (h : (Fin 10 → Bool) → Bool) (monotone : Monotone h) :
    (∀ x, h x ≤ edge x) ↔ ∀ n ∈ independent, h (mask n) = false := by
  constructor
  · intro dominated n hn
    have hx := dominated (mask n)
    rw [independent_mask n hn] at hx
    simpa [Bool.le_iff_imp] using hx
  · intro negative x
    cases hx : edge x with
    | true => simp
    | false =>
      obtain ⟨n, hn, hxn⟩ := independent_cover x hx
      have step := monotone hxn
      rw [negative n hn] at step
      simpa using step

lemma nonremovable_has_witnesses (h : (Fin 10 → Bool) → Bool)
    (G : (Fin 10 → Bool) → Bool → Bool) (monotone : Monotone h)
    (mono : ∀ x, G x false ≤ G x true)
    (correct : ∀ x, G x (!(h x)) = edge x)
    (needed_true : ¬ ∀ x, G x true = edge x)
    (needed_false : ¬ ∀ x, G x false = edge x) :
    (∃ n ∈ independent, h (mask n) = true) ∧
      ∃ n ∈ edges, h (mask n) = false := by
  have not_dominated : ¬ ∀ n ∈ independent, h (mask n) = false := by
    intro dominated
    exact needed_true (remove_negation_true edge h G mono correct
      ((le_edge_iff h monotone).mpr dominated))
  have not_dominates : ¬ ∀ n ∈ edges, h (mask n) = true := by
    intro dominates
    exact needed_false (remove_negation_false edge h G mono correct
      ((edge_le_iff h monotone).mpr dominates))
  push Not at not_dominated not_dominates
  obtain ⟨i, hi, hni⟩ := not_dominated
  obtain ⟨j, hj, hnj⟩ := not_dominates
  exact ⟨⟨i, hi, by simpa using hni⟩, j, hj, by simpa using hnj⟩

end PEqualNP.Outside.L_meta_2592_aux.Negation
