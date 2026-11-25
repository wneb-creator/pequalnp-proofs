import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux.SensitivityMask

def edge (x : Fin 9 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
    x 5 && x 7 || x 6 && x 8 || x 8 && x 5

abbrev sensitive (x : Fin 9 → Bool) : Prop :=
  edge x = false ∧ (x 4 || x 6 || x 7) = true

def pairEdge (i j : Fin 9) : Bool :=
  edge (fun k => decide (k = i ∨ k = j))

def patch (i j : Fin 9) (a b : Bool) (t : Fin 9) : Fin 9 → Bool :=
  fun k => (decide (k = i) && a) || (decide (k = j) && b) || decide (k = t)

lemma edge_monotone (x y : Fin 9 → Bool) (h : ∀ i, x i = true → y i = true) :
    edge x = true → edge y = true := by
  simp only [edge, Bool.or_eq_true, Bool.and_eq_true]
  aesop

lemma pair_implicant (i j : Fin 9) (he : pairEdge i j = true) (x : Fin 9 → Bool)
    (hi : x i = true) (hj : x j = true) : edge x = true := by
  apply edge_monotone (fun k => decide (k = i ∨ k = j)) x ?_ he
  intro k hk
  rcases of_decide_eq_true hk with rfl | rfl
  · exact hi
  · exact hj

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma projection_certificate : ∀ (i j : Fin 9) (a b : Bool), i ≠ j →
    (pairEdge i j = false ∨ (a && b) = false) →
    ([4, 6, 7] : List (Fin 9)).any (fun t =>
      decide (sensitive (patch i j a b t) ∧
        patch i j a b t i = a ∧ patch i j a b t j = b)) = true := by
  decide +kernel

lemma projection (i j : Fin 9) (a b : Bool) (different : i ≠ j)
    (allowed : pairEdge i j = false ∨ (a && b) = false) :
    ∃ x : Fin 9 → Bool, sensitive x ∧ x i = a ∧ x j = b := by
  obtain ⟨t, _, ht⟩ := List.any_eq_true.mp (projection_certificate i j a b different allowed)
  exact ⟨patch i j a b t, of_decide_eq_true ht⟩

lemma classify_mask (i j : Fin 9) (different : i ≠ j) (h : Bool → Bool → Bool)
    (constant : ∀ x : Fin 9 → Bool, sensitive x → h (x i) (x j) = true) :
    (∀ a b, h a b = true) ∨
      (pairEdge i j = true ∧ ∀ a b, h a b = !(a && b)) := by
  have force (a b : Bool) (allowed : pairEdge i j = false ∨ (a && b) = false) :
      h a b = true := by
    obtain ⟨x, hx, hi, hj⟩ := projection i j a b different allowed
    simpa only [hi, hj] using constant x hx
  have h00 : h false false = true := force false false (Or.inr rfl)
  have h01 : h false true = true := force false true (Or.inr rfl)
  have h10 : h true false = true := force true false (Or.inr rfl)
  by_cases h11 : h true true = true
  · left
    intro a b
    cases a <;> cases b <;> assumption
  · right
    have hedge : pairEdge i j = true := by
      cases he : pairEdge i j with
      | false => exact False.elim (h11 (force true true (Or.inl he)))
      | true => rfl
    refine ⟨hedge, ?_⟩
    have h11' : h true true = false := Bool.eq_false_iff.mpr h11
    intro a b
    cases a <;> cases b <;> simp only [Bool.false_and, Bool.true_and, Bool.not_false,
      Bool.not_true] <;> assumption

lemma negated_mask_implicant (i j : Fin 9) (different : i ≠ j)
    (h : Bool → Bool → Bool)
    (constant : ∀ x : Fin 9 → Bool, sensitive x → h (x i) (x j) = true) :
    ∀ x : Fin 9 → Bool, Bool.not (h (x i) (x j)) = true → edge x = true := by
  rcases classify_mask i j different h constant with trivial | ⟨he, shape⟩
  · intro x hx
    simp only [trivial, Bool.not_true] at hx
    contradiction
  · intro x hx
    rw [shape, Bool.not_not] at hx
    simp only [Bool.and_eq_true] at hx
    obtain ⟨hi, hj⟩ := hx
    exact pair_implicant i j he x hi hj

end PEqualNP.Outside.L_meta_2592_aux.SensitivityMask
