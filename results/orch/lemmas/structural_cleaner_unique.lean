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

lemma cleaner_pair_unique {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (P Q W : Finset (Fin n))
    (hW : ∀ w, w ∈ W ↔ ∀ p ∈ P, ∀ q ∈ Q,
      G.Adj p q ∨ G.Adj p w ∨ G.Adj q w)
    {p0 q0 r w w' : Fin n} (hp0 : p0 ∈ P) (hq0 : q0 ∈ Q) (hbad : ¬ G.Adj p0 q0)
    (hr : r ∈ W) (hw : w ∈ W) (hw' : w' ∈ W)
    (hpair : (r ∈ P ∨ w ∈ P) ∧ (r ∈ Q ∨ w ∈ Q))
    (hpair' : (r ∈ P ∨ w' ∈ P) ∧ (r ∈ Q ∨ w' ∈ Q)) : w = w' := by
  have no_overlap {t : Fin n} (ht : t ∈ W) : ¬ (t ∈ P ∧ t ∈ Q) := by
    rintro ⟨htP, htQ⟩
    exact G.irrefl (cleaner_in_left G P Q W hW ht htP t htQ)
  have hrPQ : r ∈ P ∨ r ∈ Q := by
    by_cases hrP : r ∈ P
    · exact Or.inl hrP
    by_cases hrQ : r ∈ Q
    · exact Or.inr hrQ
    exact False.elim (no_overlap hw ⟨hpair.1.resolve_left hrP, hpair.2.resolve_left hrQ⟩)
  rcases hrPQ with hrP | hrQ
  · have hrnotQ : r ∉ Q := fun hrQ => no_overlap hr ⟨hrP, hrQ⟩
    have hwQ := hpair.2.resolve_left hrnotQ
    have hw'Q := hpair'.2.resolve_left hrnotQ
    have hrp0 : r ≠ p0 := by
      intro heq
      subst p0
      exact hbad (cleaner_in_left G P Q W hW hr hrP q0 hq0)
    apply Finset.card_le_one.mp (h4 r p0 hrp0)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨(cleaner_in_right G P Q W hW hw hwQ r hrP).symm,
        (cleaner_in_right G P Q W hW hw hwQ p0 hp0).symm⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨(cleaner_in_right G P Q W hW hw' hw'Q r hrP).symm,
        (cleaner_in_right G P Q W hW hw' hw'Q p0 hp0).symm⟩
  · have hrnotP : r ∉ P := fun hrP => no_overlap hr ⟨hrP, hrQ⟩
    have hwP := hpair.1.resolve_left hrnotP
    have hw'P := hpair'.1.resolve_left hrnotP
    have hrq0 : r ≠ q0 := by
      intro heq
      subst q0
      exact hbad (cleaner_in_right G P Q W hW hr hrQ p0 hp0).symm
    apply Finset.card_le_one.mp (h4 r q0 hrq0)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨(cleaner_in_left G P Q W hW hw hwP r hrQ).symm,
        (cleaner_in_left G P Q W hW hw hwP q0 hq0).symm⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨(cleaner_in_left G P Q W hW hw' hw'P r hrQ).symm,
        (cleaner_in_left G P Q W hW hw' hw'P q0 hq0).symm⟩

lemma dirty_product_bad_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ) (P Q : Finset (Fin n))
    (hsem : ∀ x : Fin n → Bool, gateVal n C g x =
      (decide (∃ p ∈ P, x p = true) && decide (∃ q ∈ Q, x q = true)))
    (hbad : ¬ BelowF G C g) : ∃ p ∈ P, ∃ q ∈ Q, ¬ G.Adj p q := by
  classical
  unfold BelowF at hbad
  push Not at hbad
  obtain ⟨x, hgx, hfx⟩ := hbad
  rw [hsem, Bool.and_eq_true] at hgx
  obtain ⟨p, hp, hpx⟩ := of_decide_eq_true hgx.1
  obtain ⟨q, hq, hqx⟩ := of_decide_eq_true hgx.2
  refine ⟨p, hp, q, hq, ?_⟩
  intro hpq
  apply hfx
  have he : ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := ⟨p, q, hpq, hpx, hqx⟩
  simpa [graphFun] using he

lemma dirty_cleaner_pairs_unique {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (C : Circuit) (g : ℕ) (P Q : Finset (Fin n))
    (hsem : ∀ x : Fin n → Bool, gateVal n C g x =
      (decide (∃ p ∈ P, x p = true) && decide (∃ q ∈ Q, x q = true)))
    (hbad : ¬ BelowF G C g) {r w w' : Fin n}
    (hr : r ∈ wmax G C g) (hw : w ∈ wmax G C g) (hw' : w' ∈ wmax G C g)
    (hpair : gateVal n C g (pairInput r w) = true)
    (hpair' : gateVal n C g (pairInput r w') = true) : w = w' := by
  obtain ⟨p, hp, q, hq, hpq⟩ := dirty_product_bad_pair G C g P Q hsem hbad
  exact cleaner_pair_unique G h4 P Q (wmax G C g) (pure_product_wmax G C g P Q hsem)
    hp hq hpq hr hw hw' ((pure_product_pair C g P Q hsem r w).mp hpair)
      ((pure_product_pair C g P Q hsem r w').mp hpair')

lemma singleton_joint_cleaner {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g h : ℕ) (r : Fin n)
    (hsing : ∀ x : Fin n → Bool, x r = true → gateVal n C g x = true)
    (hjoint : ∀ x : Fin n → Bool, gateVal n C g x = true →
      gateVal n C h x = true → graphFun G ∅ x = true) : r ∈ wmax G C h := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ r, ?_⟩
  intro x hhx hrx
  exact hjoint x (hsing x hrx) hhx

lemma singleton_joint_other_guarded_card {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (h4 : NoFourCycle G) (C : Circuit) (g h : ℕ)
    (r : Fin n) (P Q : Finset (Fin n))
    (hsem : ∀ x : Fin n → Bool, gateVal n C h x =
      (decide (∃ p ∈ P, x p = true) && decide (∃ q ∈ Q, x q = true)))
    (hbad : ¬ BelowF G C h)
    (hsing : ∀ x : Fin n → Bool, x r = true → gateVal n C g x = true)
    (hjoint : ∀ x : Fin n → Bool, gateVal n C g x = true →
      gateVal n C h x = true → graphFun G ∅ x = true) :
    ((wmax G C h).filter (fun w => gateVal n C h (pairInput r w) = true)).card ≤ 1 := by
  have hr := singleton_joint_cleaner G C g h r hsing hjoint
  apply Finset.card_le_one.mpr
  intro w hw w' hw'
  obtain ⟨hw, hpair⟩ := Finset.mem_filter.mp hw
  obtain ⟨hw', hpair'⟩ := Finset.mem_filter.mp hw'
  exact dirty_cleaner_pairs_unique G h4 C h P Q hsem hbad hr hw hw' hpair hpair'

end PEqualNP.Outside.L_meta_5012.CleanerDichotomy
