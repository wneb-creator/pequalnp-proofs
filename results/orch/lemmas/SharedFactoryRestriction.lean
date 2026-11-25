import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1772_aux.SharedFactoryRestriction

open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

def linear {n : ℕ} (A : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ a ∈ A, x a = true)

lemma common_neighbor_unique {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : NoFourCycle G) {a b p q : Fin n} (hab : a ≠ b)
    (hap : G.Adj a p) (hbp : G.Adj b p) (haq : G.Adj a q) (hbq : G.Adj b q) :
    p = q := by
  apply Finset.card_le_one.mp (hfour a b hab)
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hap, hbp⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, haq, hbq⟩

lemma cross_extras_adjacent {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A T : Finset (Fin n)) (v : Fin n)
    (sound : ∀ x : Fin n → Bool,
      (x v && linear A x && linear T x) = true → graphFun G ∅ x = true)
    {a t : Fin n} (ha : a ∈ A) (ht : t ∈ T)
    (hva : ¬ G.Adj v a) (hvt : ¬ G.Adj v t) : G.Adj a t := by
  let x : Fin n → Bool := fun z => decide (z = v ∨ z = a ∨ z = t)
  have aOn : linear A x = true := by
    simpa [linear, x] using
      (show ∃ z ∈ A, z = v ∨ z = a ∨ z = t from ⟨a, ha, Or.inr (Or.inl rfl)⟩)
  have tOn : linear T x = true := by
    simpa [linear, x] using
      (show ∃ z ∈ T, z = v ∨ z = a ∨ z = t from ⟨t, ht, Or.inr (Or.inr rfl)⟩)
  have yes : graphFun G ∅ x = true := sound x (by rw [aOn, tOn]; simp [x])
  obtain ⟨p, q, edge, hp, hq⟩ : ∃ p q, G.Adj p q ∧ x p = true ∧ x q = true := by
    simpa [graphFun] using yes
  have hp' : p = v ∨ p = a ∨ p = t := by simpa [x] using hp
  have hq' : q = v ∨ q = a ∨ q = t := by simpa [x] using hq
  rcases hp' with rfl | rfl | rfl <;> rcases hq' with rfl | rfl | rfl
  · exact False.elim (edge.ne rfl)
  · exact False.elim (hva edge)
  · exact False.elim (hvt edge)
  · exact False.elim (hva edge.symm)
  · exact False.elim (edge.ne rfl)
  · exact edge
  · exact False.elim (hvt edge.symm)
  · exact edge.symm
  · exact False.elim (edge.ne rfl)

lemma two_extras_force_other_center {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hfour : NoFourCycle G)
    (A T : Finset (Fin n)) (u v a b : Fin n)
    (ha : a ∈ A) (hb : b ∈ A) (different : a ≠ b)
    (hua : G.Adj u a) (hub : G.Adj u b)
    (hva : ¬ G.Adj v a) (hvb : ¬ G.Adj v b)
    (sound : ∀ x : Fin n → Bool,
      (x v && linear A x && linear T x) = true → graphFun G ∅ x = true) :
    ∀ t ∈ T, G.Adj v t ∨ t = u := by
  intro t ht
  by_cases hvt : G.Adj v t
  · exact Or.inl hvt
  · right
    exact common_neighbor_unique G hfour different
      (cross_extras_adjacent G A T v sound ha ht hva hvt)
      (cross_extras_adjacent G A T v sound hb ht hvb hvt) hua.symm hub.symm

lemma three_leaves_force_filter_support {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hfour : NoFourCycle G)
    (A T : Finset (Fin n)) (u v a b c : Fin n) (centers : u ≠ v)
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hua : G.Adj u a) (hub : G.Adj u b) (huc : G.Adj u c)
    (sound : ∀ x : Fin n → Bool,
      (x v && linear A x && linear T x) = true → graphFun G ∅ x = true) :
    ∀ t ∈ T, G.Adj v t ∨ t = u := by
  have atMostOne (p q : Fin n) (hpq : p ≠ q) (hup : G.Adj u p)
      (huq : G.Adj u q) (hvp : G.Adj v p) : ¬ G.Adj v q := by
    intro hvq
    exact centers (common_neighbor_unique G hfour hpq hup.symm huq.symm hvp.symm hvq.symm)
  by_cases hva : G.Adj v a
  · exact two_extras_force_other_center G hfour A T u v b c hb hc hbc hub huc
      (atMostOne a b hab hua hub hva) (atMostOne a c hac hua huc hva) sound
  · by_cases hvb : G.Adj v b
    · exact two_extras_force_other_center G hfour A T u v a c ha hc hac hua huc hva
        (atMostOne b c hbc hub huc hvb) sound
    · exact two_extras_force_other_center G hfour A T u v a b ha hb hab hua hub hva hvb sound

lemma filter_sound_after_center_deletion {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (T : Finset (Fin n)) (u v : Fin n)
    (support : ∀ t ∈ T, G.Adj v t ∨ t = u) :
    ∀ x : Fin n → Bool, x u = false →
      (x v && linear T x) = true → graphFun G ∅ x = true := by
  intro x off on
  have both : x v = true ∧ linear T x = true := by simpa using on
  obtain ⟨t, ht, active⟩ : ∃ t ∈ T, x t = true := by simpa [linear] using both.2
  rcases support t ht with edge | rfl
  · simpa [graphFun] using (show ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true from
      ⟨v, t, edge, both.1, active⟩)
  · rw [off] at active
    cases active

lemma exceptional_support_partition {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (A T : Finset (Fin n)) (u v : Fin n)
    (notAdjacent : ¬ G.Adj v u) (hu : u ∈ T)
    (sound : ∀ x : Fin n → Bool,
      (x v && linear A x && linear T x) = true → graphFun G ∅ x = true) :
    ∀ a ∈ A, G.Adj u a ∨ G.Adj v a := by
  intro a ha
  by_cases hva : G.Adj v a
  · exact Or.inr hva
  · exact Or.inl (cross_extras_adjacent G A T v sound ha hu hva notAdjacent).symm

lemma exceptional_center_unique {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hfour : NoFourCycle G)
    (A T S : Finset (Fin n)) (u v w a b : Fin n)
    (notV : ¬ G.Adj v u) (notW : ¬ G.Adj w u) (huT : u ∈ T) (huS : u ∈ S)
    (ha : a ∈ A) (hb : b ∈ A) (different : a ≠ b)
    (notA : ¬ G.Adj u a) (notB : ¬ G.Adj u b)
    (soundV : ∀ x : Fin n → Bool,
      (x v && linear A x && linear T x) = true → graphFun G ∅ x = true)
    (soundW : ∀ x : Fin n → Bool,
      (x w && linear A x && linear S x) = true → graphFun G ∅ x = true) : v = w := by
  have va := (exceptional_support_partition G A T u v notV huT soundV a ha).resolve_left notA
  have vb := (exceptional_support_partition G A T u v notV huT soundV b hb).resolve_left notB
  have wa := (exceptional_support_partition G A S u w notW huS soundW a ha).resolve_left notA
  have wb := (exceptional_support_partition G A S u w notW huS soundW b hb).resolve_left notB
  exact common_neighbor_unique G hfour different va.symm vb.symm wa.symm wb.symm

end PEqualNP.Outside.L_meta_1772_aux.SharedFactoryRestriction
