import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5012.OverlapCleaner

lemma common_adj {n : ℕ} (G : SimpleGraph (Fin n))
    (P Q W : Finset (Fin n))
    (hW : ∀ w ∈ W, ∀ p ∈ P, ∀ q ∈ Q, G.Adj p q ∨ G.Adj p w ∨ G.Adj q w)
    {r w : Fin n} (hr : r ∈ P ∩ Q) (hw : w ∈ W) : G.Adj r w := by
  rcases hW w hw r (Finset.mem_inter.mp hr).1 r (Finset.mem_inter.mp hr).2 with h | h | h
  · exact False.elim (G.irrefl h)
  · exact h
  · exact h

lemma left_adj {n : ℕ} (G : SimpleGraph (Fin n))
    (P Q W : Finset (Fin n))
    (hW : ∀ w ∈ W, ∀ p ∈ P, ∀ q ∈ Q, G.Adj p q ∨ G.Adj p w ∨ G.Adj q w)
    {w q : Fin n} (hw : w ∈ W) (hp : w ∈ P) (hq : q ∈ Q) : G.Adj w q := by
  rcases hW w hw w hp q hq with h | h | h
  · exact h
  · exact False.elim (G.irrefl h)
  · exact h.symm

lemma right_adj {n : ℕ} (G : SimpleGraph (Fin n))
    (P Q W : Finset (Fin n))
    (hW : ∀ w ∈ W, ∀ p ∈ P, ∀ q ∈ Q, G.Adj p q ∨ G.Adj p w ∨ G.Adj q w)
    {w p : Fin n} (hw : w ∈ W) (hq : w ∈ Q) (hp : p ∈ P) : G.Adj w p := by
  rcases hW w hw p hp w hq with h | h | h
  · exact h.symm
  · exact h.symm
  · exact False.elim (G.irrefl h)

lemma large_overlap_one_cleaner {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : PEqualNP.TopForm.NoFourCycle G) (P Q W : Finset (Fin n))
    (hW : ∀ w ∈ W, ∀ p ∈ P, ∀ q ∈ Q, G.Adj p q ∨ G.Adj p w ∨ G.Adj q w)
    (hI : 2 ≤ (P ∩ Q).card) : W.card ≤ 1 := by
  classical
  obtain ⟨r, hr, t, ht, hrt⟩ := Finset.one_lt_card.mp hI
  apply (Finset.card_le_card ?_).trans (hfour r t hrt)
  intro w hw
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨common_adj G P Q W hW hr hw, common_adj G P Q W hW ht hw⟩

lemma wide_arm_cleaners {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : PEqualNP.TopForm.NoFourCycle G) (P Q W : Finset (Fin n))
    (hW : ∀ w ∈ W, ∀ p ∈ P, ∀ q ∈ Q, G.Adj p q ∨ G.Adj p w ∨ G.Adj q w)
    (hP : 2 ≤ P.card) (hQ : 2 ≤ Q.card) :
    (W ∩ P).card ≤ 1 ∧ (W ∩ Q).card ≤ 1 := by
  classical
  constructor
  · obtain ⟨q, hq, q', hq', hqq⟩ := Finset.one_lt_card.mp hQ
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨haW, haP⟩ := Finset.mem_inter.mp ha
    obtain ⟨hbW, hbP⟩ := Finset.mem_inter.mp hb
    by_contra hab
    apply hqq
    apply Finset.card_le_one.mp (hfour a b hab)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨left_adj G P Q W hW haW haP hq, left_adj G P Q W hW hbW hbP hq⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨left_adj G P Q W hW haW haP hq', left_adj G P Q W hW hbW hbP hq'⟩
  · obtain ⟨p, hp, p', hp', hpp⟩ := Finset.one_lt_card.mp hP
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨haW, haQ⟩ := Finset.mem_inter.mp ha
    obtain ⟨hbW, hbQ⟩ := Finset.mem_inter.mp hb
    by_contra hab
    apply hpp
    apply Finset.card_le_one.mp (hfour a b hab)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨right_adj G P Q W hW haW haQ hp, right_adj G P Q W hW hbW hbQ hp⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨right_adj G P Q W hW haW haQ hp', right_adj G P Q W hW hbW hbQ hp'⟩

lemma overlap_cleaners_one_side {n : ℕ} (G : SimpleGraph (Fin n))
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (P Q W : Finset (Fin n))
    (hW : ∀ w ∈ W, ∀ p ∈ P, ∀ q ∈ Q, G.Adj p q ∨ G.Adj p w ∨ G.Adj q w)
    (hI : (P ∩ Q).Nonempty) : W ∩ P = ∅ ∨ W ∩ Q = ∅ := by
  classical
  by_cases hP : W ∩ P = ∅
  · exact Or.inl hP
  apply Or.inr
  obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hP
  obtain ⟨r, hr⟩ := hI
  apply Finset.not_nonempty_iff_eq_empty.mp
  intro hne
  obtain ⟨b, hb⟩ := hne
  obtain ⟨haW, haP⟩ := Finset.mem_inter.mp ha
  obtain ⟨hbW, hbQ⟩ := Finset.mem_inter.mp hb
  have hra := hbip r a (common_adj G P Q W hW hr haW)
  have hrb := hbip r b (common_adj G P Q W hW hr hbW)
  have hab := hbip a b (left_adj G P Q W hW haW haP hbQ)
  cases hrval : s r <;> cases haval : s a <;> cases hbval : s b <;> simp_all

lemma singleton_overlap_guarded_cover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (hfour : PEqualNP.TopForm.NoFourCycle G) (P Q W : Finset (Fin n))
    (hW : ∀ w ∈ W, ∀ p ∈ P, ∀ q ∈ Q, G.Adj p q ∨ G.Adj p w ∨ G.Adj q w)
    (hP : 2 ≤ P.card) (hQ : 2 ≤ Q.card) (r : Fin n) (hI : P ∩ Q = {r}) :
    let T := (W ∩ P) ∪ (W ∩ Q)
    T.card ≤ 1 ∧ (∀ t ∈ T, G.Adj r t) ∧
      ∀ u v, (u ∈ P ∨ v ∈ P) → (u ∈ Q ∨ v ∈ Q) → (u ∈ W ∨ v ∈ W) →
        u ∈ insert r T ∨ v ∈ insert r T := by
  classical
  dsimp only
  let T := (W ∩ P) ∪ (W ∩ Q)
  have hr : r ∈ P ∩ Q := by simp [hI]
  have hne : (P ∩ Q).Nonempty := ⟨r, hr⟩
  obtain ⟨hWP, hWQ⟩ := wide_arm_cleaners G hfour P Q W hW hP hQ
  have hT : T.card ≤ 1 := by
    rcases overlap_cleaners_one_side G s hbip P Q W hW hne with he | he
    · simpa [T, he] using hWQ
    · simpa [T, he] using hWP
  have hcov (u v : Fin n) (hu : u ∈ W)
      (hp : u ∈ P ∨ v ∈ P) (hq : u ∈ Q ∨ v ∈ Q) : u ∈ T ∨ v = r := by
    by_cases huP : u ∈ P
    · exact Or.inl (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hu, huP⟩))
    by_cases huQ : u ∈ Q
    · exact Or.inl (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hu, huQ⟩))
    apply Or.inr
    have hv : v ∈ P ∩ Q := Finset.mem_inter.mpr ⟨hp.resolve_left huP, hq.resolve_left huQ⟩
    simpa [hI] using hv
  refine ⟨hT, ?_, ?_⟩
  · intro t ht
    have htW : t ∈ W := by
      rcases Finset.mem_union.mp ht with h | h <;> exact (Finset.mem_inter.mp h).1
    exact common_adj G P Q W hW hr htW
  · intro u v hp hq hw
    rcases hw with hu | hv
    · rcases hcov u v hu hp hq with huT | hvR
      · exact Or.inl (Finset.mem_insert_of_mem huT)
      · exact Or.inr (by simp [hvR])
    · rcases hcov v u hv hp.symm hq.symm with hvT | huR
      · exact Or.inr (Finset.mem_insert_of_mem hvT)
      · exact Or.inl (by simp [huR])

lemma small_arm_cover {n : ℕ} (P Q : Finset (Fin n)) (hP : P.card ≤ 1) :
    ∃ K : Finset (Fin n), K.card ≤ 1 ∧
      ∀ u v, (u ∈ P ∨ v ∈ P) → (u ∈ Q ∨ v ∈ Q) → u ∈ K ∨ v ∈ K := by
  exact ⟨P, hP, fun _ _ hp _ => hp⟩

end PEqualNP.Outside.L_meta_5012.OverlapCleaner
