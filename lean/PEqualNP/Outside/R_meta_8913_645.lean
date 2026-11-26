import PEqualNP.Defs

set_option maxRecDepth 9000 in
set_option maxHeartbeats 2400000 in
theorem PEqualNP.Outside.R_meta_8913_645
    (normalize : (let I : Fin 13 → Fin 13 → Prop := fun p l => p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9;
      ∀ (n : ℕ) (X Y : Fin n → Finset (Fin 13)),
        (∀ p l : Fin 13, I p l → ∃ i, X i = {p} ∧ Y i = {l}) →
        (∀ P Q : Finset (Fin 13), (∀ p ∈ P, ∀ l ∈ Q, ¬I p l) → (∀ l : Fin 13, {p ∈ P | I p l}.card ≤ 2) →
          (∀ p : Fin 13, {l ∈ Q | I p l}.card ≤ 2) → ∃ i, X i = P ∧ Y i = Q) →
        have B : Set (Set (Fin n)) := {∅, Set.univ} ∪ Set.range fun v : Fin (13 + 13) =>
          {i : Fin n | Fin.addCases (fun p : Fin 13 => decide (p ∈ X i)) (fun l : Fin 13 => decide (l ∈ Y i)) v = true};
        ∀ s : List (Set (Fin n)),
          (∀ k : Fin s.length, let D := B ∪ {t | t ∈ s.take k};
            ∃ a ∈ D, ∃ b ∈ D, s.getD k ∅ = a ∪ b ∨ s.getD k ∅ = a ∩ b) →
          {i : Fin n | ∃ p l, I p l ∧ X i = {p} ∧ Y i = {l}} ∈ B ∪ {t | t ∈ s} →
          ∃ K : Finset (Finset (Fin 13) × Finset (Fin 13)),
            (∀ p l : Fin 13, (p,l) ∈ K.biUnion (fun t => t.1 ×ˢ t.2) ↔ I p l) ∧
            (K.sum fun t => t.1.card + t.2.card) ≤ s.length + 1))
    (intersection :
      let I : Fin 13 → Fin 13 → Prop := fun p l => p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
      ∀ p q l m : Fin 13, p ≠ q → I p l → I q l → I p m → I q m → l = m) :
    (let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); ∃ (x2 : ℕ) (x3 : Fin x2 → Finset (Fin (13 : ℕ))) (x4 : Fin x2 → Finset (Fin (13 : ℕ))) (x5 : Set (Fin x2)),   (∀ x6 ∈ x5, ∃ (x8 : Fin (13 : ℕ)) (x9 : Fin (13 : ℕ)), x1 x8 x9 ∧ x3 x6 = {x8} ∧ x4 x6 = {x9}) ∧     (∀ x6 ∉ x5, (∀ x8 ∈ x3 x6, ∀ x10 ∈ x4 x6, ¬x1 x8 x10) ∧ (∀ (x8 : Fin (13 : ℕ)), {x9 ∈ x3 x6 | x1 x9 x8}.card ≤ (2 : ℕ)) ∧ ∀ (x8 : Fin (13 : ℕ)), {x9 ∈ x4 x6 | x1 x8 x9}.card ≤ (2 : ℕ)) ∧       have x6 : Fin x2 → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x6 : Fin x2) (x7 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 ∈ x3 x6)) (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 ∈ x4 x6)) x7;       have x7 : Set (Set (Fin x2)) := {∅, Set.univ} ∪ Set.range fun (x7 : Fin ((13 : ℕ) + (13 : ℕ))) => {x8 : Fin x2 | x6 x8 x7 = Bool.true};       ∀ (x8 : List (Set (Fin x2))),         x8.length ≤ (63 : ℕ) →           (∀ (x10 : Fin x8.length),               have x11 : Set (Set (Fin x2)) := x7 ∪ {x11 : Set (Fin x2) | x11 ∈ List.take (↑x10) x8};               x8.getD ↑x10 ∅ ∉ x11 ∧ ∃ x12 ∈ x11, ∃ x13 ∈ x11, x8.getD ↑x10 ∅ = x12 ∪ x13 ∨ x8.getD ↑x10 ∅ = x12 ∩ x13) →             x5 ∉ x7 ∪ {x11 : Set (Fin x2) | x11 ∈ x8}) := by
  classical
  intro x1
  obtain ⟨m, X, Y, hcls, hpos, hneg⟩ : ∃ (m : ℕ) (X Y : Fin m → Finset (Fin 13)),
      (∀ i, (∃ p l, x1 p l ∧ X i = {p} ∧ Y i = {l}) ∨
        ((∀ p ∈ X i, ∀ l ∈ Y i, ¬x1 p l) ∧ (∀ l : Fin 13, {p ∈ X i | x1 p l}.card ≤ 2) ∧
          ∀ p : Fin 13, {l ∈ Y i | x1 p l}.card ≤ 2)) ∧
      (∀ p l : Fin 13, x1 p l → ∃ i, X i = {p} ∧ Y i = {l}) ∧
      (∀ P Q : Finset (Fin 13), (∀ p ∈ P, ∀ l ∈ Q, ¬x1 p l) → (∀ l : Fin 13, {p ∈ P | x1 p l}.card ≤ 2) →
        (∀ p : Fin 13, {l ∈ Q | x1 p l}.card ≤ 2) → ∃ i, X i = P ∧ Y i = Q) := by
    let e := Fintype.equivFin {t : Finset (Fin 13) × Finset (Fin 13) //
      (∃ p l, x1 p l ∧ t.1 = {p} ∧ t.2 = {l}) ∨
        ((∀ p ∈ t.1, ∀ l ∈ t.2, ¬x1 p l) ∧ (∀ l : Fin 13, {p ∈ t.1 | x1 p l}.card ≤ 2) ∧
          ∀ p : Fin 13, {l ∈ t.2 | x1 p l}.card ≤ 2)}
    refine ⟨_, fun i => (e.symm i).1.1, fun i => (e.symm i).1.2, fun i => (e.symm i).2, ?_, ?_⟩
    · intro p l h
      exact ⟨e ⟨({p}, {l}), Or.inl ⟨p, l, h, rfl, rfl⟩⟩, by simp⟩
    · intro P Q h1 h2 h3
      exact ⟨e ⟨(P, Q), Or.inr ⟨h1, h2, h3⟩⟩, by simp⟩
  refine ⟨m, X, Y, {i | ∃ p l, x1 p l ∧ X i = {p} ∧ Y i = {l}}, ?_, ?_, ?_⟩
  · intro i hi
    exact hi
  · intro i hi
    rcases hcls i with h | h
    · exact absurd h hi
    · exact h
  · intro x6 x7 s hlen hval hmem
    obtain ⟨K, hcover, hcost⟩ := normalize m X Y hpos hneg s (fun k => (hval k).2) hmem
    let E : Finset (Fin 13 × Fin 13) := Finset.univ.filter fun z => x1 z.1 z.2
    have total : E.card = 52 := by decide
    have covered : 52 ≤ K.sum (fun t => t.1.card * t.2.card) := by
      rw [← total]
      have eqE : K.biUnion (fun t => t.1 ×ˢ t.2) = E := by
        ext t
        simpa [E] using (hcover t.1 t.2)
      rw [← eqE]
      simpa only [Finset.card_product] using
        (Finset.card_biUnion_le (s := K) (t := fun t => t.1 ×ˢ t.2))
    have degreeP : ∀ p : Fin 13, (Finset.univ.filter fun l => x1 p l).card = 4 := by decide
    have degreeL : ∀ l : Fin 13, (Finset.univ.filter fun p => x1 p l).card = 4 := by decide
    have star (A B : Finset (Fin 13)) (complete : ∀ p ∈ A, ∀ l ∈ B, x1 p l) :
        5 * (A.card * B.card) ≤ 4 * (A.card + B.card) := by
      by_cases hA : A.Nonempty
      · obtain ⟨p, hp⟩ := hA
        by_cases hB : B.Nonempty
        · obtain ⟨l, hl⟩ := hB
          have aBound : A.card ≤ 4 := by
            rw [← degreeL l]
            exact Finset.card_le_card (fun a ha => Finset.mem_filter.mpr ⟨Finset.mem_univ _, complete a ha l hl⟩)
          have bBound : B.card ≤ 4 := by
            rw [← degreeP p]
            exact Finset.card_le_card (fun b hb => Finset.mem_filter.mpr ⟨Finset.mem_univ _, complete p hp b hb⟩)
          by_cases ha : A.card ≤ 1
          · have hpos := Finset.card_pos.mpr (show A.Nonempty from ⟨p,hp⟩)
            have e : A.card = 1 := by omega
            rw [e, one_mul]
            omega
          · obtain ⟨p₁, hp₁, p₂, hp₂, hne⟩ := Finset.one_lt_card.mp (Nat.lt_of_not_ge ha)
            have small : B.card ≤ 1 := Finset.card_le_one.mpr (fun l hl m hm =>
              intersection p₁ p₂ l m hne (complete p₁ hp₁ l hl) (complete p₂ hp₂ l hl)
                (complete p₁ hp₁ m hm) (complete p₂ hp₂ m hm))
            have hpos := Finset.card_pos.mpr (show B.Nonempty from ⟨l,hl⟩)
            have e : B.card = 1 := by omega
            rw [e, mul_one]
            omega
        · simp [Finset.not_nonempty_iff_eq_empty.mp hB]
      · simp [Finset.not_nonempty_iff_eq_empty.mp hA]
    have charge (t) (ht : t ∈ K) : 5 * (t.1.card * t.2.card) ≤ 4 * (t.1.card + t.2.card) := by
      apply star
      intro p hp l hl
      have h : (p,l) ∈ K.biUnion (fun t => t.1 ×ˢ t.2) :=
        Finset.mem_biUnion.mpr ⟨t,ht,Finset.mem_product.mpr ⟨hp,hl⟩⟩
      exact (hcover p l).mp h
    have weighted := Finset.sum_le_sum (s := K) charge
    simp only [← Finset.mul_sum] at weighted
    omega
