import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1031.PairThreeCNF

lemma disjoint_hits_bipartite {n : ℕ} (G : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) (hd : Disjoint A B)
    (hA : ∀ u v, G.Adj u v → u ∈ A ∨ v ∈ A)
    (hB : ∀ u v, G.Adj u v → u ∈ B ∨ v ∈ B) :
    ∃ s : Fin n → Bool, ∀ u v, G.Adj u v → s u ≠ s v := by
  classical
  refine ⟨fun v => decide (v ∈ A), ?_⟩
  intro u v huv
  rcases hA u v huv with hu | hv <;> rcases hB u v huv with hu' | hv'
  · exact (Finset.disjoint_left.mp hd hu hu').elim
  · have hn : v ∉ A := fun h => Finset.disjoint_left.mp hd h hv'
    simp [hu, hn]
  · have hn : u ∉ A := fun h => Finset.disjoint_left.mp hd h hu'
    simp [hv, hn]
  · exact (Finset.disjoint_left.mp hd hv hv').elim

lemma three_clause_disjoint {n : ℕ} (G : SimpleGraph (Fin n))
    (A B C : Finset (Fin n))
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hpair : ∀ u v, (u ∈ A ∨ v ∈ A) → (u ∈ B ∨ v ∈ B) →
      (u ∈ C ∨ v ∈ C) → G.Adj u v) :
    Disjoint A B ∨ Disjoint A C ∨ Disjoint B C := by
  classical
  by_contra h
  push Not at h
  obtain ⟨a, haA, haB⟩ := Finset.not_disjoint_iff.mp h.1
  obtain ⟨b, hbA, hbC⟩ := Finset.not_disjoint_iff.mp h.2.1
  obtain ⟨c, hcB, hcC⟩ := Finset.not_disjoint_iff.mp h.2.2
  exact htri a b c
    (hpair a b (Or.inl haA) (Or.inl haB) (Or.inr hbC))
    (hpair b c (Or.inl hbA) (Or.inr hcB) (Or.inl hbC))
    (hpair c a (Or.inr haA) (Or.inl hcB) (Or.inl hcC))

lemma three_clause_bipartite {n : ℕ} (G : SimpleGraph (Fin n))
    (A B C : Finset (Fin n))
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hrep : ∀ u v, G.Adj u v ↔
      (u ∈ A ∨ v ∈ A) ∧ (u ∈ B ∨ v ∈ B) ∧ (u ∈ C ∨ v ∈ C)) :
    ∃ s : Fin n → Bool, ∀ u v, G.Adj u v → s u ≠ s v := by
  have hdis := three_clause_disjoint G A B C htri
    (fun u v ha hb hc => (hrep u v).mpr ⟨ha, hb, hc⟩)
  rcases hdis with hAB | hAC | hBC
  · exact disjoint_hits_bipartite G A B hAB
      (fun u v h => ((hrep u v).mp h).1)
      (fun u v h => ((hrep u v).mp h).2.1)
  · exact disjoint_hits_bipartite G A C hAC
      (fun u v h => ((hrep u v).mp h).1)
      (fun u v h => ((hrep u v).mp h).2.2)
  · exact disjoint_hits_bipartite G B C hBC
      (fun u v h => ((hrep u v).mp h).2.1)
      (fun u v h => ((hrep u v).mp h).2.2)

lemma disjoint_three_clause_cover {n : ℕ} (G : SimpleGraph (Fin n))
    (A B C : Finset (Fin n)) (hd : Disjoint A B)
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d →
      G.Adj d a → a = c ∨ b = d)
    (hrep : ∀ u v, G.Adj u v ↔
      (u ∈ A ∨ v ∈ A) ∧ (u ∈ B ∨ v ∈ B) ∧ (u ∈ C ∨ v ∈ C)) :
    ∃ T : Finset (Fin n), T.card ≤ 2 ∧ ∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T := by
  classical
  by_cases hA : A.card ≤ 1
  · exact ⟨A, by omega, fun u v h => ((hrep u v).mp h).1⟩
  by_cases hB : B.card ≤ 1
  · exact ⟨B, by omega, fun u v h => ((hrep u v).mp h).2.1⟩
  obtain ⟨a, ha, a', ha', haa'⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
  obtain ⟨b, hb, b', hb', hbb'⟩ := Finset.one_lt_card.mp (by omega : 1 < B.card)
  have hAC : (A ∩ C).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro u hu v hv
    obtain ⟨huA, huC⟩ := Finset.mem_inter.mp hu
    obtain ⟨hvA, hvC⟩ := Finset.mem_inter.mp hv
    apply Or.resolve_right (hfour u b v b' ?_ ?_ ?_ ?_) hbb'
    · exact (hrep u b).mpr ⟨Or.inl huA, Or.inr hb, Or.inl huC⟩
    · exact (hrep b v).mpr ⟨Or.inr hvA, Or.inl hb, Or.inr hvC⟩
    · exact (hrep v b').mpr ⟨Or.inl hvA, Or.inr hb', Or.inl hvC⟩
    · exact (hrep b' u).mpr ⟨Or.inr huA, Or.inl hb', Or.inr huC⟩
  have hBC : (B ∩ C).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro u hu v hv
    obtain ⟨huB, huC⟩ := Finset.mem_inter.mp hu
    obtain ⟨hvB, hvC⟩ := Finset.mem_inter.mp hv
    apply Or.resolve_right (hfour u a v a' ?_ ?_ ?_ ?_) haa'
    · exact (hrep u a).mpr ⟨Or.inr ha, Or.inl huB, Or.inl huC⟩
    · exact (hrep a v).mpr ⟨Or.inl ha, Or.inr hvB, Or.inr hvC⟩
    · exact (hrep v a').mpr ⟨Or.inr ha', Or.inl hvB, Or.inl hvC⟩
    · exact (hrep a' u).mpr ⟨Or.inl ha', Or.inr huB, Or.inr huC⟩
  refine ⟨(A ∩ C) ∪ (B ∩ C), ?_, ?_⟩
  · have := Finset.card_union_le (A ∩ C) (B ∩ C)
    omega
  · intro u v huv
    have h := (hrep u v).mp huv
    have hnu : ¬ (u ∈ A ∧ u ∈ B) := fun h => Finset.disjoint_left.mp hd h.1 h.2
    have hnv : ¬ (v ∈ A ∧ v ∈ B) := fun h => Finset.disjoint_left.mp hd h.1 h.2
    simp only [Finset.mem_union, Finset.mem_inter]
    tauto

lemma three_clause_cover {n : ℕ} (G : SimpleGraph (Fin n))
    (A B C : Finset (Fin n))
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d →
      G.Adj d a → a = c ∨ b = d)
    (hrep : ∀ u v, G.Adj u v ↔
      (u ∈ A ∨ v ∈ A) ∧ (u ∈ B ∨ v ∈ B) ∧ (u ∈ C ∨ v ∈ C)) :
    ∃ T : Finset (Fin n), T.card ≤ 2 ∧ ∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T := by
  have hdis := three_clause_disjoint G A B C htri
    (fun u v ha hb hc => (hrep u v).mpr ⟨ha, hb, hc⟩)
  rcases hdis with hAB | hAC | hBC
  · exact disjoint_three_clause_cover G A B C hAB hfour hrep
  · apply disjoint_three_clause_cover G A C B hAC hfour
    intro u v
    rw [hrep]
    tauto
  · apply disjoint_three_clause_cover G B C A hBC hfour
    intro u v
    rw [hrep]
    tauto

lemma cross_card_le_one {n : ℕ} (G : SimpleGraph (Fin n))
    (U V : Finset (Fin n)) (hV : 1 < V.card)
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d →
      G.Adj d a → a = c ∨ b = d)
    (hcross : ∀ u ∈ U, ∀ v ∈ V, G.Adj u v) : U.card ≤ 1 := by
  obtain ⟨b, hb, b', hb', hbb'⟩ := Finset.one_lt_card.mp hV
  apply Finset.card_le_one.mpr
  intro a ha a' ha'
  exact (hfour a b a' b' (hcross a ha b hb) (hcross a' ha' b hb).symm
    (hcross a' ha' b' hb') (hcross a ha b' hb').symm).resolve_right hbb'

lemma singleton_cover_edge {n : ℕ} (G : SimpleGraph (Fin n))
    (T : Finset (Fin n)) (hT : T.card ≤ 1)
    (hcover : ∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T)
    (hne : ∃ u v, G.Adj u v) :
    ∃ u v, G.Adj u v ∧ ∀ p q, G.Adj p q → p = u ∨ p = v ∨ q = u ∨ q = v := by
  obtain ⟨u, v, huv⟩ := hne
  refine ⟨u, v, huv, ?_⟩
  intro p q hpq
  rcases hcover u v huv with hu | hv <;> rcases hcover p q hpq with hp | hq
  · exact Or.inl (Finset.card_le_one.mp hT p hp u hu)
  · exact Or.inr (Or.inr (Or.inl (Finset.card_le_one.mp hT q hq u hu)))
  · exact Or.inr (Or.inl (Finset.card_le_one.mp hT p hp v hv))
  · exact Or.inr (Or.inr (Or.inr (Finset.card_le_one.mp hT q hq v hv)))

lemma disjoint_three_clause_edge_cover {n : ℕ} (G : SimpleGraph (Fin n))
    (A B C : Finset (Fin n)) (hd : Disjoint A B)
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d →
      G.Adj d a → a = c ∨ b = d)
    (hrep : ∀ u v, G.Adj u v ↔
      (u ∈ A ∨ v ∈ A) ∧ (u ∈ B ∨ v ∈ B) ∧ (u ∈ C ∨ v ∈ C))
    (hne : ∃ u v, G.Adj u v) :
    ∃ u v, G.Adj u v ∧ ∀ p q, G.Adj p q → p = u ∨ p = v ∨ q = u ∨ q = v := by
  classical
  by_cases hA : A.card ≤ 1
  · exact singleton_cover_edge G A hA (fun u v h => ((hrep u v).mp h).1) hne
  by_cases hB : B.card ≤ 1
  · exact singleton_cover_edge G B hB (fun u v h => ((hrep u v).mp h).2.1) hne
  have hAC : (A ∩ C).card ≤ 1 := cross_card_le_one G (A ∩ C) B (by omega) hfour (by
    intro u hu v hv
    obtain ⟨huA, huC⟩ := Finset.mem_inter.mp hu
    exact (hrep u v).mpr ⟨Or.inl huA, Or.inr hv, Or.inl huC⟩)
  have hBC : (B ∩ C).card ≤ 1 := cross_card_le_one G (B ∩ C) A (by omega) hfour (by
    intro u hu v hv
    obtain ⟨huB, huC⟩ := Finset.mem_inter.mp hu
    exact (hrep u v).mpr ⟨Or.inr hv, Or.inl huB, Or.inl huC⟩)
  have hcover : ∀ u v, G.Adj u v → u ∈ (A ∩ C) ∪ (B ∩ C) ∨ v ∈ (A ∩ C) ∪ (B ∩ C) := by
    intro u v huv
    have h := (hrep u v).mp huv
    have hnu : ¬ (u ∈ A ∧ u ∈ B) := fun h => Finset.disjoint_left.mp hd h.1 h.2
    have hnv : ¬ (v ∈ A ∧ v ∈ B) := fun h => Finset.disjoint_left.mp hd h.1 h.2
    simp only [Finset.mem_union, Finset.mem_inter]
    tauto
  by_cases hX : (A ∩ C).Nonempty
  · by_cases hY : (B ∩ C).Nonempty
    · obtain ⟨a, ha⟩ := hX
      obtain ⟨b, hb⟩ := hY
      obtain ⟨haA, haC⟩ := Finset.mem_inter.mp ha
      obtain ⟨hbB, hbC⟩ := Finset.mem_inter.mp hb
      refine ⟨a, b, (hrep a b).mpr ⟨Or.inl haA, Or.inr hbB, Or.inl haC⟩, ?_⟩
      intro p q hpq
      rcases hcover p q hpq with hp | hq
      · rcases Finset.mem_union.mp hp with hp | hp
        · exact Or.inl (Finset.card_le_one.mp hAC p hp a ha)
        · exact Or.inr (Or.inl (Finset.card_le_one.mp hBC p hp b hb))
      · rcases Finset.mem_union.mp hq with hq | hq
        · exact Or.inr (Or.inr (Or.inl (Finset.card_le_one.mp hAC q hq a ha)))
        · exact Or.inr (Or.inr (Or.inr (Finset.card_le_one.mp hBC q hq b hb)))
    · have hY' : B ∩ C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hY
      apply singleton_cover_edge G (A ∩ C) hAC _ hne
      intro u v huv
      simpa [hY'] using hcover u v huv
  · have hX' : A ∩ C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hX
    apply singleton_cover_edge G (B ∩ C) hBC _ hne
    intro u v huv
    simpa [hX'] using hcover u v huv

lemma three_clause_edge_cover {n : ℕ} (G : SimpleGraph (Fin n))
    (A B C : Finset (Fin n))
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d →
      G.Adj d a → a = c ∨ b = d)
    (hrep : ∀ u v, G.Adj u v ↔
      (u ∈ A ∨ v ∈ A) ∧ (u ∈ B ∨ v ∈ B) ∧ (u ∈ C ∨ v ∈ C))
    (hne : ∃ u v, G.Adj u v) :
    ∃ u v, G.Adj u v ∧ ∀ p q, G.Adj p q → p = u ∨ p = v ∨ q = u ∨ q = v := by
  have hdis := three_clause_disjoint G A B C htri
    (fun u v ha hb hc => (hrep u v).mpr ⟨ha, hb, hc⟩)
  rcases hdis with hAB | hAC | hBC
  · exact disjoint_three_clause_edge_cover G A B C hAB hfour hrep hne
  · apply disjoint_three_clause_edge_cover G A C B hAC hfour _ hne
    intro u v
    rw [hrep]
    tauto
  · apply disjoint_three_clause_edge_cover G B C A hBC hfour _ hne
    intro u v
    rw [hrep]
    tauto

end PEqualNP.Outside.L_meta_1031.PairThreeCNF
