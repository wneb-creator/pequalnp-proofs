import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5012.CleanerDichotomy

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
  PEqualNP.MetaComplexity.NestedCover

lemma pure_product_wmax {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ) (P Q : Finset (Fin n))
    (hsem : ∀ x : Fin n → Bool, gateVal n C g x =
      (decide (∃ p ∈ P, x p = true) && decide (∃ q ∈ Q, x q = true)))
    (w : Fin n) :
    w ∈ wmax G C g ↔ ∀ p ∈ P, ∀ q ∈ Q,
      G.Adj p q ∨ G.Adj p w ∨ G.Adj q w := by
  simp only [wmax, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hw p hp q hq
    let x : Fin n → Bool := fun u => decide (u = p ∨ u = q ∨ u = w)
    have hgx : gateVal n C g x = true := by
      rw [hsem, Bool.and_eq_true]
      constructor
      · exact decide_eq_true (show ∃ a ∈ P, x a = true from ⟨p, hp, by simp [x]⟩)
      · exact decide_eq_true (show ∃ a ∈ Q, x a = true from ⟨q, hq, by simp [x]⟩)
    have hf := hw x hgx (by simp [x])
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq] at hf
    obtain ⟨u, v, huv, hu, hv⟩ := hf
    simp only [x, decide_eq_true_eq] at hu hv
    rcases hu with rfl | rfl | rfl
    · rcases hv with rfl | rfl | rfl
      · exact False.elim (G.irrefl huv)
      · exact Or.inl huv
      · exact Or.inr (Or.inl huv)
    · rcases hv with rfl | rfl | rfl
      · exact Or.inl huv.symm
      · exact False.elim (G.irrefl huv)
      · exact Or.inr (Or.inr huv)
    · rcases hv with rfl | rfl | rfl
      · exact Or.inr (Or.inl huv.symm)
      · exact Or.inr (Or.inr huv.symm)
      · exact False.elim (G.irrefl huv)
  · intro hw x hgx hxw
    rw [hsem, Bool.and_eq_true] at hgx
    obtain ⟨p, hp, hxp⟩ := of_decide_eq_true hgx.1
    obtain ⟨q, hq, hxq⟩ := of_decide_eq_true hgx.2
    have hed : ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
      rcases hw p hp q hq with hpq | hpw | hqw
      · exact ⟨p, q, hpq, hxp, hxq⟩
      · exact ⟨p, w, hpw, hxp, hxw⟩
      · exact ⟨q, w, hqw, hxq, hxw⟩
    simpa [graphFun] using hed

lemma cleaner_in_left {n : ℕ} (G : SimpleGraph (Fin n)) (P Q W : Finset (Fin n))
    (hW : ∀ w, w ∈ W ↔ ∀ p ∈ P, ∀ q ∈ Q,
      G.Adj p q ∨ G.Adj p w ∨ G.Adj q w)
    {w : Fin n} (hwW : w ∈ W) (hwP : w ∈ P) :
    ∀ q ∈ Q, G.Adj w q := by
  intro q hq
  rcases (hW w).mp hwW w hwP q hq with h | h | h
  · exact h
  · exact False.elim (G.irrefl h)
  · exact h.symm

lemma cleaner_in_right {n : ℕ} (G : SimpleGraph (Fin n)) (P Q W : Finset (Fin n))
    (hW : ∀ w, w ∈ W ↔ ∀ p ∈ P, ∀ q ∈ Q,
      G.Adj p q ∨ G.Adj p w ∨ G.Adj q w)
    {w : Fin n} (hwW : w ∈ W) (hwQ : w ∈ Q) :
    ∀ p ∈ P, G.Adj w p := by
  intro p hp
  rcases (hW w).mp hwW p hp w hwQ with h | h | h
  · exact h.symm
  · exact h.symm
  · exact False.elim (G.irrefl h)

lemma cleaner_centres_small {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (P Q W : Finset (Fin n))
    (hW : ∀ w, w ∈ W ↔ ∀ p ∈ P, ∀ q ∈ Q,
      G.Adj p q ∨ G.Adj p w ∨ G.Adj q w)
    (hP : 2 ≤ P.card) (hQ : 2 ≤ Q.card) :
    (W ∩ P).card ≤ 1 ∧ (W ∩ Q).card ≤ 1 := by
  constructor
  · obtain ⟨q, hq, q', hq', hqq'⟩ := Finset.one_lt_card.mp (by omega : 1 < Q.card)
    have hsub : W ∩ P ⊆ Finset.univ.filter (fun w => G.Adj q w ∧ G.Adj q' w) := by
      intro w hw
      obtain ⟨hwW, hwP⟩ := Finset.mem_inter.mp hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨(cleaner_in_left G P Q W hW hwW hwP q hq).symm,
        (cleaner_in_left G P Q W hW hwW hwP q' hq').symm⟩
    exact (Finset.card_le_card hsub).trans (h4 q q' hqq')
  · obtain ⟨p, hp, p', hp', hpp'⟩ := Finset.one_lt_card.mp (by omega : 1 < P.card)
    have hsub : W ∩ Q ⊆ Finset.univ.filter (fun w => G.Adj p w ∧ G.Adj p' w) := by
      intro w hw
      obtain ⟨hwW, hwQ⟩ := Finset.mem_inter.mp hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨(cleaner_in_right G P Q W hW hwW hwQ p hp).symm,
        (cleaner_in_right G P Q W hW hwW hwQ p' hp').symm⟩
    exact (Finset.card_le_card hsub).trans (h4 p p' hpp')

lemma touched_pair_covered {n : ℕ} (P Q W : Finset (Fin n)) (hPQ : Disjoint P Q)
    {u v : Fin n} (hp : u ∈ P ∨ v ∈ P) (hq : u ∈ Q ∨ v ∈ Q)
    (hw : u ∈ W ∨ v ∈ W) :
    u ∈ (W ∩ P) ∪ (W ∩ Q) ∨ v ∈ (W ∩ P) ∪ (W ∩ Q) := by
  have each : ∀ u v : Fin n, (u ∈ P ∨ v ∈ P) → (u ∈ Q ∨ v ∈ Q) → u ∈ P ∪ Q := by
    intro u v hp hq
    rcases hp with hp | hp
    · exact Finset.mem_union_left _ hp
    · rcases hq with hq | hq
      · exact Finset.mem_union_right _ hq
      · exact False.elim (Finset.disjoint_left.mp hPQ hp hq)
  rcases hw with hu | hv
  · left
    rcases Finset.mem_union.mp (each u v hp hq) with hp | hq
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hu, hp⟩)
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hu, hq⟩)
  · right
    rcases Finset.mem_union.mp (each v u hp.symm hq.symm) with hp | hq
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hv, hp⟩)
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hv, hq⟩)

lemma flag_or_one_centre {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (P Q W : Finset (Fin n))
    (hW : ∀ w, w ∈ W ↔ ∀ p ∈ P, ∀ q ∈ Q,
      G.Adj p q ∨ G.Adj p w ∨ G.Adj q w)
    (hP : 2 ≤ P.card) (hQ : 2 ≤ Q.card) :
    ((W ∩ P) ∪ (W ∩ Q)).card ≤ 1 ∨
      ∃ z zp : Fin n, G.Adj z zp ∧ z ∈ P ∧ zp ∈ Q ∧
        (∀ p ∈ P, G.Adj p zp) ∧ (∀ q ∈ Q, G.Adj q z) := by
  obtain ⟨hleft, hright⟩ := cleaner_centres_small G h4 P Q W hW hP hQ
  by_cases hl : (W ∩ P).Nonempty
  · by_cases hr : (W ∩ Q).Nonempty
    · right
      obtain ⟨z, hz⟩ := hl
      obtain ⟨hzW, hzP⟩ := Finset.mem_inter.mp hz
      obtain ⟨zp, hzp⟩ := hr
      obtain ⟨hzpW, hzpQ⟩ := Finset.mem_inter.mp hzp
      refine ⟨z, zp, cleaner_in_left G P Q W hW hzW hzP zp hzpQ, hzP, hzpQ, ?_, ?_⟩
      · intro p hp
        exact (cleaner_in_right G P Q W hW hzpW hzpQ p hp).symm
      · intro q hq
        exact (cleaner_in_left G P Q W hW hzW hzP q hq).symm
    · left
      rw [Finset.not_nonempty_iff_eq_empty.mp hr, Finset.union_empty]
      exact hleft
  · left
    rw [Finset.not_nonempty_iff_eq_empty.mp hl, Finset.empty_union]
    exact hright

lemma pure_product_pair {n : ℕ} (C : Circuit) (g : ℕ) (P Q : Finset (Fin n))
    (hsem : ∀ x : Fin n → Bool, gateVal n C g x =
      (decide (∃ p ∈ P, x p = true) && decide (∃ q ∈ Q, x q = true)))
    (u v : Fin n) :
    gateVal n C g (pairInput u v) = true ↔
      (u ∈ P ∨ v ∈ P) ∧ (u ∈ Q ∨ v ∈ Q) := by
  rw [hsem, Bool.and_eq_true]
  simp only [pairInput, decide_eq_true_eq, exists_or, and_or_left,
    exists_eq_right]

lemma pure_disjoint_guarded_cover {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (h4 : NoFourCycle G) (C : Circuit) (g : ℕ)
    (P Q : Finset (Fin n)) (hPQ : Disjoint P Q)
    (hP : 2 ≤ P.card) (hQ : 2 ≤ Q.card)
    (hsem : ∀ x : Fin n → Bool, gateVal n C g x =
      (decide (∃ p ∈ P, x p = true) && decide (∃ q ∈ Q, x q = true))) :
    (∃ K : Finset (Fin n), K ⊆ wmax G C g ∧ K.card ≤ 1 ∧
      ∀ u v, gateVal n C g (pairInput u v) = true →
        (u ∈ wmax G C g ∨ v ∈ wmax G C g) → u ∈ K ∨ v ∈ K) ∨
    ∃ z zp : Fin n, G.Adj z zp ∧ z ∈ P ∧ zp ∈ Q ∧
      (∀ p ∈ P, G.Adj p zp) ∧ (∀ q ∈ Q, G.Adj q z) := by
  have hW := pure_product_wmax G C g P Q hsem
  rcases flag_or_one_centre G h4 P Q (wmax G C g) hW hP hQ with hc | hf
  · left
    refine ⟨(wmax G C g ∩ P) ∪ (wmax G C g ∩ Q), ?_, hc, ?_⟩
    · intro u hu
      rcases Finset.mem_union.mp hu with hu | hu
      · exact (Finset.mem_inter.mp hu).1
      · exact (Finset.mem_inter.mp hu).1
    · intro u v hval htouch
      obtain ⟨hp, hq⟩ := (pure_product_pair C g P Q hsem u v).mp hval
      exact touched_pair_covered P Q (wmax G C g) hPQ hp hq htouch
  · exact .inr hf

end PEqualNP.Outside.L_meta_5012.CleanerDichotomy


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

namespace PEqualNP.Outside.L_meta_5012.ProductClassification

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
  PEqualNP.MetaComplexity.NestedCover

lemma pure_product_classification {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (h4 : NoFourCycle G)
    (C : Circuit) (g : ℕ) (P Q : Finset (Fin n))
    (hsem : ∀ x : Fin n → Bool, gateVal n C g x =
      (decide (∃ p ∈ P, x p = true) && decide (∃ q ∈ Q, x q = true))) :
    (∃ K : Finset (Fin n), K.card ≤ 1 ∧
      ∀ u v, gateVal n C g (pairInput u v) = true →
        (u ∈ wmax G C g ∨ v ∈ wmax G C g) → u ∈ K ∨ v ∈ K) ∨
    (2 ≤ P.card ∧ 2 ≤ Q.card ∧ Disjoint P Q ∧
      ∃ z zp : Fin n, G.Adj z zp ∧ z ∈ wmax G C g ∧ zp ∈ wmax G C g ∧
        z ∈ P ∧ zp ∈ Q ∧ (∀ p ∈ P, G.Adj p zp) ∧ (∀ q ∈ Q, G.Adj q z)) ∨
    (2 ≤ P.card ∧ 2 ≤ Q.card ∧
      ∃ r t : Fin n, P ∩ Q = {r} ∧ G.Adj r t ∧ t ∈ wmax G C g ∧
        r ∉ wmax G C g ∧
        ((wmax G C g ∩ P = {t} ∧ wmax G C g ∩ Q = ∅) ∨
          (wmax G C g ∩ Q = {t} ∧ wmax G C g ∩ P = ∅)) ∧
        ∀ u v, gateVal n C g (pairInput u v) = true →
          (u ∈ wmax G C g ∨ v ∈ wmax G C g) → u ∈ ({r, t} : Finset (Fin n)) ∨
            v ∈ ({r, t} : Finset (Fin n))) := by
  classical
  let W := wmax G C g
  have hW := CleanerDichotomy.pure_product_wmax G C g P Q hsem
  have hWforward : ∀ w ∈ W, ∀ p ∈ P, ∀ q ∈ Q,
      G.Adj p q ∨ G.Adj p w ∨ G.Adj q w := fun w hw => (hW w).mp hw
  have hpair := CleanerDichotomy.pure_product_pair C g P Q hsem
  by_cases hP : 2 ≤ P.card
  · by_cases hQ : 2 ≤ Q.card
    · by_cases hPQ : Disjoint P Q
      · rcases CleanerDichotomy.pure_disjoint_guarded_cover G h4 C g P Q hPQ hP hQ hsem with
          ⟨K, _, hK, hcov⟩ | ⟨z, zp, hzzp, hzP, hzpQ, hPzp, hQz⟩
        · exact Or.inl ⟨K, hK, hcov⟩
        · apply Or.inr ∘ Or.inl
          refine ⟨hP, hQ, hPQ, z, zp, hzzp, ?_, ?_, hzP, hzpQ, hPzp, hQz⟩
          · exact (hW z).mpr (fun p hp q hq => Or.inr (Or.inr (hQz q hq)))
          · exact (hW zp).mpr (fun p hp q hq => Or.inr (Or.inl (hPzp p hp)))
      · by_cases hIlarge : 2 ≤ (P ∩ Q).card
        · apply Or.inl
          refine ⟨W, OverlapCleaner.large_overlap_one_cleaner G h4 P Q W hWforward hIlarge, ?_⟩
          exact fun _ _ _ hw => hw
        · have hIne : P ∩ Q ≠ ∅ := by
            intro he
            exact hPQ (Finset.disjoint_iff_inter_eq_empty.mpr he)
          have hIcard : (P ∩ Q).card = 1 := by
            have hpos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hIne)
            omega
          obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hIcard
          let T := (W ∩ P) ∪ (W ∩ Q)
          obtain ⟨hTcard, hTadj, hTcov⟩ :=
            OverlapCleaner.singleton_overlap_guarded_cover G s hbip h4 P Q W hWforward hP hQ r hr
          by_cases hTempty : T = ∅
          · apply Or.inl
            refine ⟨{r}, by simp, ?_⟩
            intro u v hval htouch
            obtain ⟨hp, hq⟩ := (hpair u v).mp hval
            have hc := hTcov u v hp hq htouch
            change u ∈ insert r T ∨ v ∈ insert r T at hc
            simpa only [hTempty, Finset.insert_empty] using hc
          · have hTpos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hTempty)
            have hTone : T.card = 1 := by change T.card ≤ 1 at hTcard; omega
            obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hTone
            have htT : t ∈ T := by simp [ht]
            have htW : t ∈ W := by
              rcases Finset.mem_union.mp htT with htP | htQ <;>
                exact (Finset.mem_inter.mp ‹_›).1
            have hrI : r ∈ P ∩ Q := by simp [hr]
            have hrnot : r ∉ W := by
              intro hrW
              exact G.irrefl (OverlapCleaner.common_adj G P Q W hWforward hrI hrW)
            apply Or.inr ∘ Or.inr
            refine ⟨hP, hQ, r, t, hr, hTadj t htT, htW, hrnot, ?_, ?_⟩
            · rcases OverlapCleaner.overlap_cleaners_one_side G s hbip P Q W hWforward
                ⟨r, hrI⟩ with heP | heQ
              · exact Or.inr ⟨by simpa only [T, heP, Finset.empty_union] using ht, heP⟩
              · exact Or.inl ⟨by simpa only [T, heQ, Finset.union_empty] using ht, heQ⟩
            · intro u v hval htouch
              obtain ⟨hp, hq⟩ := (hpair u v).mp hval
              have hc := hTcov u v hp hq htouch
              change u ∈ insert r T ∨ v ∈ insert r T at hc
              simpa only [ht] using hc
    · apply Or.inl
      refine ⟨Q, by omega, ?_⟩
      intro u v hval _
      exact ((hpair u v).mp hval).2
  · apply Or.inl
    refine ⟨P, by omega, ?_⟩
    intro u v hval _
    exact ((hpair u v).mp hval).1

end PEqualNP.Outside.L_meta_5012.ProductClassification
