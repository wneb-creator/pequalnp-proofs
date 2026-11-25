import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2590_aux.ThreeNeighbors

lemma outside_pair {α : Type*} [DecidableEq α] (S : Finset α)
    (large : 3 ≤ S.card) (a b : α) : ∃ v ∈ S, v ≠ a ∧ v ≠ b := by
  classical
  by_contra no
  have subset : S ⊆ {a, b} := by
    intro v hv
    by_cases ha : v = a
    · simp [ha]
    by_cases hb : v = b
    · simp [hb]
    exact False.elim (no ⟨v, hv, ha, hb⟩)
  have bound := Finset.card_le_card subset
  have pair_bound : ({a, b} : Finset α).card ≤ 2 := by
    calc
      ({a, b} : Finset α).card ≤ 1 + ({b} : Finset α).card :=
        (Finset.card_insert_le a {b}).trans_eq (Nat.add_comm _ _)
      _ = 2 := by simp
  omega

def single {n : ℕ} (v : Fin n) : Fin n → Bool := fun i => decide (i = v)

lemma three_singletons_need_three_coordinates {n : ℕ}
    (S : Finset (Fin n)) (large : 3 ≤ S.card)
    (f : (Fin n → Bool) → Bool)
    (zero : f (fun _ => false) = false)
    (accepts : ∀ v ∈ S, f (single v) = true)
    (a b : Fin n)
    (depends : ∀ x y, x a = y a → x b = y b → f x = f y) : False := by
  obtain ⟨v, hv, ha, hb⟩ := outside_pair S large a b
  have same : f (single v) = f (fun _ => false) := by
    apply depends
    · simp [single, Ne.symm ha]
    · simp [single, Ne.symm hb]
  rw [accepts v hv, zero] at same
  cases same

lemma two_pin_signal_cannot_accept_three {n : ℕ}
    (S : Finset (Fin n)) (large : 3 ≤ S.card)
    (op : Bool → Bool → Bool) (a b : Fin n)
    (zero : op false false = false) :
    ¬ ∀ v ∈ S, op (single v a) (single v b) = true := by
  intro all
  apply three_singletons_need_three_coordinates S large
    (fun x => op (x a) (x b)) zero all a b
  intro x y ha hb
  rw [ha, hb]

end PEqualNP.Outside.L_meta_2590_aux.ThreeNeighbors
