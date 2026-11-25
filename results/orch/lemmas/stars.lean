import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4970

lemma left_star_unique {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hcycle : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {a a' : Fin p} (Q : Finset (Fin l)) (hQ : 2 ≤ Q.card)
    (hleft : ∀ b ∈ Q, (a, b) ∈ E) (hright : ∀ b ∈ Q, (a', b) ∈ E) :
    a = a' := by
  obtain ⟨b, hb, b', hb', hne⟩ := Finset.one_lt_card.mp hQ
  by_contra ha
  exact hcycle a a' b b' ha hne ⟨hleft b hb, hleft b' hb', hright b hb, hright b' hb'⟩

lemma right_star_unique {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hcycle : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {b b' : Fin l} (P : Finset (Fin p)) (hP : 2 ≤ P.card)
    (hleft : ∀ a ∈ P, (a, b) ∈ E) (hright : ∀ a ∈ P, (a, b') ∈ E) :
    b = b' := by
  obtain ⟨a, ha, a', ha', hne⟩ := Finset.one_lt_card.mp hP
  by_contra hb
  exact hcycle a a' b b' hne hb ⟨hleft a ha, hright a ha, hleft a' ha', hright a' ha'⟩

lemma left_star_inter_card_le_one {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hcycle : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {a a' : Fin p} (ha : a ≠ a') (Q R : Finset (Fin l))
    (hQ : ∀ b ∈ Q, (a, b) ∈ E) (hR : ∀ b ∈ R, (a', b) ∈ E) :
    (Q ∩ R).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro b hb b' hb'
  by_contra hne
  exact hcycle a a' b b' ha hne
    ⟨hQ b (Finset.mem_inter.mp hb).1, hQ b' (Finset.mem_inter.mp hb').1,
      hR b (Finset.mem_inter.mp hb).2, hR b' (Finset.mem_inter.mp hb').2⟩

lemma ownership_cover {p l : ℕ} (E : Finset (Fin p × Fin l))
    (own : Fin p × Fin l → Fin (p + l))
    (hown : ∀ e ∈ E,
      own e = Fin.castAdd l e.1 ∨ own e = Fin.natAdd p e.2) :
    ∀ a b, (a, b) ∈ E →
      Fin.castAdd l a ∈ E.image own ∨ Fin.natAdd p b ∈ E.image own := by
  intro a b hab
  have hm : own (a, b) ∈ E.image own := Finset.mem_image_of_mem own hab
  rcases hown (a, b) hab with h | h
  · exact Or.inl (h ▸ hm)
  · exact Or.inr (h ▸ hm)

lemma ownership_ledger {α β : Type*} [DecidableEq β]
    (E : Finset α) (own : α → β) :
    (∑ v ∈ E.image own, ((E.filter (fun e => own e = v)).card - 1)) +
      (E.image own).card = E.card := by
  have hpos : ∀ v ∈ E.image own, 1 ≤ (E.filter (fun e => own e = v)).card := by
    intro v hv
    obtain ⟨e, he, hev⟩ := Finset.mem_image.mp hv
    exact Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hev⟩⟩
  calc
    (∑ v ∈ E.image own, ((E.filter (fun e => own e = v)).card - 1)) +
        (E.image own).card =
        ∑ v ∈ E.image own, ((E.filter (fun e => own e = v)).card - 1 + 1) := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
    _ = ∑ v ∈ E.image own, (E.filter (fun e => own e = v)).card := by
      apply Finset.sum_congr rfl
      intro v hv
      exact Nat.sub_add_cancel (hpos v hv)
    _ = E.card := (Finset.card_eq_sum_card_image own E).symm

lemma right_or_injective {p l : ℕ} (Q R : Finset (Fin l))
    (h : ∀ x : Fin (p + l) → Bool,
      decide (∃ b ∈ Q, x (Fin.natAdd p b) = true) =
      decide (∃ b ∈ R, x (Fin.natAdd p b) = true)) : Q = R := by
  ext b
  have hx := h (fun i => decide (i = Fin.natAdd p b))
  simpa using hx

lemma left_or_injective {p l : ℕ} (P R : Finset (Fin p))
    (h : ∀ x : Fin (p + l) → Bool,
      decide (∃ a ∈ P, x (Fin.castAdd l a) = true) =
      decide (∃ a ∈ R, x (Fin.castAdd l a) = true)) : P = R := by
  ext a
  have hx := h (fun i => decide (i = Fin.castAdd l a))
  simpa using hx

lemma opposite_or_distinct {p l : ℕ} (P : Finset (Fin p)) (Q : Finset (Fin l))
    (hQ : Q.Nonempty) :
    ¬ (∀ x : Fin (p + l) → Bool,
      decide (∃ a ∈ P, x (Fin.castAdd l a) = true) =
      decide (∃ b ∈ Q, x (Fin.natAdd p b) = true)) := by
  intro h
  obtain ⟨b, hb⟩ := hQ
  have hx := h (fun i => decide (i = Fin.natAdd p b))
  have hne : ∀ a : Fin p, Fin.castAdd l a ≠ Fin.natAdd p b := by
    intro a ha
    have hv := congrArg Fin.val ha
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    omega
  simp [hne, hb] at hx

lemma same_right_or_center_unique {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hcycle : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {a a' : Fin p} (Q R : Finset (Fin l)) (hQ : 2 ≤ Q.card)
    (hleft : ∀ b ∈ Q, (a, b) ∈ E) (hright : ∀ b ∈ R, (a', b) ∈ E)
    (h : ∀ x : Fin (p + l) → Bool,
      decide (∃ b ∈ Q, x (Fin.natAdd p b) = true) =
      decide (∃ b ∈ R, x (Fin.natAdd p b) = true)) : a = a' := by
  have heq := right_or_injective Q R h
  subst R
  exact left_star_unique E hcycle Q hQ hleft hright

lemma singleton_bilinear_false {p l : ℕ} (E : Finset (Fin p × Fin l))
    (v : Fin (p + l)) :
    decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧
      decide (Fin.castAdd l a = v) = true ∧
      decide (Fin.natAdd p b = v) = true) = false := by
  apply decide_eq_false_iff_not.mpr
  rintro ⟨a, b, _, ha, hb⟩
  simp only [decide_eq_true_eq] at ha hb
  have hv := congrArg Fin.val (ha.trans hb.symm)
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

lemma singleton_not_below_bilinear {p l : ℕ} (E : Finset (Fin p × Fin l))
    (f : (Fin (p + l) → Bool) → Bool) (v : Fin (p + l))
    (hv : f (fun i => decide (i = v)) = true) :
    ¬ (∀ x : Fin (p + l) → Bool, f x = true →
      decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧
        x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true) = true) := by
  intro h
  have hx := h (fun i => decide (i = v)) hv
  rw [singleton_bilinear_false E v] at hx
  cases hx

lemma right_or_not_below_bilinear {p l : ℕ} (E : Finset (Fin p × Fin l))
    (Q : Finset (Fin l)) (hQ : Q.Nonempty) :
    ¬ (∀ x : Fin (p + l) → Bool,
      decide (∃ b ∈ Q, x (Fin.natAdd p b) = true) = true →
      decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧
        x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true) = true) := by
  obtain ⟨b, hb⟩ := hQ
  apply singleton_not_below_bilinear E
    (fun x => decide (∃ b' ∈ Q, x (Fin.natAdd p b') = true)) (Fin.natAdd p b)
  simp [hb]

lemma left_or_not_below_bilinear {p l : ℕ} (E : Finset (Fin p × Fin l))
    (P : Finset (Fin p)) (hP : P.Nonempty) :
    ¬ (∀ x : Fin (p + l) → Bool,
      decide (∃ a ∈ P, x (Fin.castAdd l a) = true) = true →
      decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧
        x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true) = true) := by
  obtain ⟨a, ha⟩ := hP
  apply singleton_not_below_bilinear E
    (fun x => decide (∃ a' ∈ P, x (Fin.castAdd l a') = true)) (Fin.castAdd l a)
  simp [ha]

lemma singleton_separates_gate_sets {p l : ℕ} {ι : Type*}
    (E : Finset (Fin p × Fin l)) (A B : Finset ι)
    (value : ι → (Fin (p + l) → Bool) → Bool)
    (hA : ∀ j ∈ A, ∃ v : Fin (p + l), value j (fun i => decide (i = v)) = true)
    (hB : ∀ j ∈ B, ∀ x : Fin (p + l) → Bool, value j x = true →
      decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧
        x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true) = true) :
    Disjoint A B := by
  apply Finset.disjoint_left.mpr
  intro j hjA hjB
  obtain ⟨v, hv⟩ := hA j hjA
  exact singleton_not_below_bilinear E (value j) v hv (hB j hjB)

end PEqualNP.Outside.L_meta_4970
