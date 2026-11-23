import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1020

namespace Pilot5bMeta1020NearStar

lemma line_unique {n m : ℕ} (T : Fin m → Finset (Fin n))
    (hT : ∀ i j, i ≠ j → (T i ∩ T j).card ≤ 1)
    (S : Finset (Fin n)) (hS : 10 ≤ S.card)
    {l l' : Fin m} (hl : (S \ T l).card ≤ 4) (hl' : (S \ T l').card ≤ 4) :
    l = l' := by
  by_contra hne
  have hsub : S ⊆ (T l ∩ T l') ∪ ((S \ T l) ∪ (S \ T l')) := by
    intro p hp
    by_cases hpl : p ∈ T l
    · by_cases hpl' : p ∈ T l'
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hpl, hpl'⟩)
      · exact Finset.mem_union_right _ (Finset.mem_union_right _
          (Finset.mem_sdiff.mpr ⟨hp, hpl'⟩))
    · exact Finset.mem_union_right _ (Finset.mem_union_left _
        (Finset.mem_sdiff.mpr ⟨hp, hpl⟩))
  have hc := Finset.card_le_card hsub
  have hu := Finset.card_union_le (T l ∩ T l') ((S \ T l) ∪ (S \ T l'))
  have hv := Finset.card_union_le (S \ T l) (S \ T l')
  have ht := hT l l' hne
  omega

lemma descend {n : ℕ} (S : ℕ → Finset (Fin n)) (G : Finset ℕ)
    (kids : ℕ → Finset ℕ)
    (hlt : ∀ g ∈ G, ∀ c ∈ kids g, c < g)
    (hunion : ∀ g ∈ G, S g = (kids g).biUnion S)
    (hlarge : ∀ g, 10 ≤ (S g).card → g ∈ G) :
    ∀ w (p : Fin n), p ∈ S w → 10 ≤ (S w).card →
      ∃ g ∈ G, 10 ≤ (S g).card ∧ S g ⊆ S w ∧
        ∃ c ∈ kids g, p ∈ S c ∧ (S c).card ≤ 9 := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro p hp hw
    have hg : w ∈ G := hlarge w hw
    have hp' : p ∈ (kids w).biUnion S := by rwa [← hunion w hg]
    obtain ⟨c, hc, hpc⟩ := Finset.mem_biUnion.mp hp'
    have hsub : S c ⊆ S w := by
      intro q hq
      rw [hunion w hg]
      exact Finset.mem_biUnion.mpr ⟨c, hc, hq⟩
    by_cases hcsmall : (S c).card ≤ 9
    · exact ⟨w, hg, hw, Finset.Subset.refl _, c, hc, hpc, hcsmall⟩
    · obtain ⟨g, hgG, hgbig, hgs, d, hd, hpd, hdsmall⟩ :=
        ih c (hlt w hg c hc) p hpc (by omega)
      exact ⟨g, hgG, hgbig, hgs.trans hsub, d, hd, hpd, hdsmall⟩

theorem count {n m K : ℕ} (T : Fin m → Finset (Fin n))
    (hT : ∀ i j, i ≠ j → (T i ∩ T j).card ≤ 1)
    (S : ℕ → Finset (Fin n)) (G : Finset ℕ) (kids : ℕ → Finset ℕ)
    (hkids : ∀ g ∈ G, (kids g).card ≤ 2)
    (hlt : ∀ g ∈ G, ∀ c ∈ kids g, c < g)
    (hunion : ∀ g ∈ G, S g = (kids g).biUnion S)
    (hlarge : ∀ g, 10 ≤ (S g).card → g ∈ G)
    (root : Fin K → ℕ) (line : Fin K → Fin m)
    (hnear : ∀ j, (S (root j) \ T (line j)).card ≤ 4) :
    ((Finset.univ : Finset (Fin K)).biUnion fun j =>
      (S (root j)).image (fun p => (p, line j))).card ≤ 18 * G.card + 9 * K := by
  classical
  let L : ℕ → Finset (Fin m) := fun g => Finset.univ.filter fun l =>
    10 ≤ (S g).card ∧ (S g \ T l).card ≤ 4
  let small : ℕ → Finset (Fin n) := fun c => if (S c).card ≤ 9 then S c else ∅
  let C : ℕ → ℕ → Finset (Fin n × Fin m) := fun g c =>
    (L g).biUnion fun l => (small c).image (fun p => (p, l))
  let Big : Finset (Fin n × Fin m) := G.biUnion fun g => (kids g).biUnion (C g)
  let Small : Finset (Fin n × Fin m) := Finset.univ.biUnion fun j : Fin K =>
    if (S (root j)).card ≤ 9 then (S (root j)).image (fun p => (p, line j)) else ∅
  have hL : ∀ g, (L g).card ≤ 1 := by
    intro g
    apply Finset.card_le_one.mpr
    intro l hl l' hl'
    obtain ⟨_, hbig, hnear⟩ := Finset.mem_filter.mp hl
    obtain ⟨_, _, hnear'⟩ := Finset.mem_filter.mp hl'
    exact line_unique T hT (S g) hbig hnear hnear'
  have hsmall : ∀ c, (small c).card ≤ 9 := by
    intro c
    simp only [small]
    split_ifs with h
    · exact h
    · simp
  have hC : ∀ g c, (C g c).card ≤ 9 := by
    intro g c
    have hb := Finset.card_biUnion_le_card_mul (L g)
      (fun l => (small c).image (fun p => (p, l))) 9
      (fun _ _ => Finset.card_image_le.trans (hsmall c))
    have hl := hL g
    dsimp only [C]
    omega
  have hBig : Big.card ≤ 18 * G.card := by
    have hb := Finset.card_biUnion_le_card_mul G
      (fun g => (kids g).biUnion (C g)) 18 (by
        intro g hg
        have hc := Finset.card_biUnion_le_card_mul (kids g) (C g) 9 (fun c _ => hC g c)
        have hk := hkids g hg
        omega)
    dsimp only [Big]
    omega
  have hSmall : Small.card ≤ 9 * K := by
    have hs := Finset.card_biUnion_le_card_mul (Finset.univ : Finset (Fin K))
      (fun j => if (S (root j)).card ≤ 9 then
        (S (root j)).image (fun p => (p, line j)) else ∅) 9 (by
          intro j _
          split_ifs with h
          · exact Finset.card_image_le.trans h
          · simp)
    simpa only [Small, Finset.card_univ, Fintype.card_fin, Nat.mul_comm] using hs
  have hsub : ((Finset.univ : Finset (Fin K)).biUnion fun j =>
      (S (root j)).image (fun p => (p, line j))) ⊆ Small ∪ Big := by
    intro e he
    obtain ⟨j, _, hjp⟩ := Finset.mem_biUnion.mp he
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hjp
    by_cases hj : (S (root j)).card ≤ 9
    · apply Finset.mem_union_left
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, by
        simp only [ite_eq_left hj]
        exact Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩
    · obtain ⟨g, hg, hgbig, hgs, c, hc, hpc, hcsmall⟩ :=
        descend S G kids hlt hunion hlarge (root j) p hp (by omega)
      have hgn : (S g \ T (line j)).card ≤ 4 := by
        refine (Finset.card_le_card ?_).trans (hnear j)
        intro q hq
        obtain ⟨hqS, hqT⟩ := Finset.mem_sdiff.mp hq
        exact Finset.mem_sdiff.mpr ⟨hgs hqS, hqT⟩
      apply Finset.mem_union_right
      refine Finset.mem_biUnion.mpr ⟨g, hg, Finset.mem_biUnion.mpr ⟨c, hc, ?_⟩⟩
      refine Finset.mem_biUnion.mpr ⟨line j, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgbig, hgn⟩
      · apply Finset.mem_image.mpr
        refine ⟨p, ?_, rfl⟩
        simpa only [small, ite_eq_left hcsmall] using hpc
  have hb := Finset.card_le_card hsub
  have hu := Finset.card_union_le Small Big
  omega

theorem count_subset {n m K : ℕ} (T : Fin m → Finset (Fin n))
    (hT : ∀ i j, i ≠ j → (T i ∩ T j).card ≤ 1)
    (S : ℕ → Finset (Fin n)) (G : Finset ℕ) (kids : ℕ → Finset ℕ)
    (hkids : ∀ g ∈ G, (kids g).card ≤ 2)
    (hlt : ∀ g ∈ G, ∀ c ∈ kids g, c < g)
    (hunion : ∀ g ∈ G, S g = (kids g).biUnion S)
    (hlarge : ∀ g, 10 ≤ (S g).card → g ∈ G)
    (root : Fin K → ℕ) (line : Fin K → Fin m)
    (hnear : ∀ j, (S (root j) \ T (line j)).card ≤ 4)
    (E : Finset (Fin n × Fin m))
    (hcover : ∀ e ∈ E, ∃ j, e.2 = line j ∧ e.1 ∈ S (root j)) :
    E.card ≤ 18 * G.card + 9 * K := by
  classical
  refine (Finset.card_le_card ?_).trans
    (count T hT S G kids hkids hlt hunion hlarge root line hnear)
  intro e he
  obtain ⟨j, hj, hp⟩ := hcover e he
  refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, ?_⟩
  exact Finset.mem_image.mpr ⟨e.1, hp, by cases e; simp_all⟩

end Pilot5bMeta1020NearStar

namespace Pilot5bMeta1020PrunedNearStar


def pruned {n : ℕ} (S : ℕ → Finset (Fin n)) (G : Finset ℕ)
    (kids : ℕ → Finset ℕ) (w : ℕ) : Finset (Fin n) :=
  if w ∈ G then
    (kids w).biUnion fun c => if _h : c < w then pruned S G kids c else ∅
  else if (S w).card ≤ 9 then S w else ∅
termination_by w

lemma pruned_or {n : ℕ} (S : ℕ → Finset (Fin n)) (G : Finset ℕ)
    (kids : ℕ → Finset ℕ) (w : ℕ) (hw : w ∈ G)
    (hlt : ∀ c ∈ kids w, c < w) :
    pruned S G kids w = (kids w).biUnion (pruned S G kids) := by
  rw [pruned, ite_eq_left hw]
  apply Finset.biUnion_congr rfl
  intro c hc
  simp only [dite_eq_left (hlt c hc)]

lemma pruned_leaf {n : ℕ} (S : ℕ → Finset (Fin n)) (G : Finset ℕ)
    (kids : ℕ → Finset ℕ) (w : ℕ) (hw : w ∉ G) :
    pruned S G kids w = if (S w).card ≤ 9 then S w else ∅ := by
  rw [pruned, ite_eq_right hw]

lemma pruned_subset {n : ℕ} (S : ℕ → Finset (Fin n)) (G : Finset ℕ)
    (kids : ℕ → Finset ℕ)
    (hlt : ∀ g ∈ G, ∀ c ∈ kids g, c < g)
    (hunion : ∀ g ∈ G, S g = (kids g).biUnion S) :
    ∀ w, pruned S G kids w ⊆ S w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w ∈ G
    · rw [pruned_or S G kids w hw (hlt w hw)]
      intro p hp
      obtain ⟨c, hc, hpc⟩ := Finset.mem_biUnion.mp hp
      rw [hunion w hw]
      exact Finset.mem_biUnion.mpr ⟨c, hc, ih c (hlt w hw c hc) hpc⟩
    · rw [pruned_leaf S G kids w hw]
      split_ifs
      · exact Finset.Subset.refl _
      · exact Finset.empty_subset _

lemma pruned_large {n : ℕ} (S : ℕ → Finset (Fin n)) (G : Finset ℕ)
    (kids : ℕ → Finset ℕ) (w : ℕ)
    (hw : 10 ≤ (pruned S G kids w).card) : w ∈ G := by
  by_contra hn
  rw [pruned_leaf S G kids w hn] at hw
  split_ifs at hw with h
  · omega
  · simp at hw

lemma pruned_near {n m : ℕ} (S : ℕ → Finset (Fin n)) (G : Finset ℕ)
    (kids : ℕ → Finset ℕ)
    (hlt : ∀ g ∈ G, ∀ c ∈ kids g, c < g)
    (hunion : ∀ g ∈ G, S g = (kids g).biUnion S)
    (T : Fin m → Finset (Fin n)) (w : ℕ) (l : Fin m)
    (hnear : (S w \ T l).card ≤ 4) :
    (pruned S G kids w \ T l).card ≤ 4 := by
  refine (Finset.card_le_card ?_).trans hnear
  intro p hp
  obtain ⟨hps, hpt⟩ := Finset.mem_sdiff.mp hp
  exact Finset.mem_sdiff.mpr ⟨pruned_subset S G kids hlt hunion w hps, hpt⟩

lemma preserve {n m : ℕ} (S : ℕ → Finset (Fin n)) (G L : Finset ℕ)
    (kids : ℕ → Finset ℕ) (A : ℕ → Finset (Fin n))
    (hlt : ∀ g ∈ G, ∀ c ∈ kids g, c < g)
    (hunion : ∀ g ∈ G, S g = (kids g).biUnion S)
    (hlabel : ∀ g, g ∉ G → (S g).Nonempty → g ∈ L ∧ S g ⊆ A g)
    (T : Fin m → Finset (Fin n)) (r : ℕ) (l : Fin m) (p : Fin n)
    (hnear : (S r \ T l).card ≤ 4)
    (hexcl : ∀ g ∈ L, p ∈ A g → (A g ∩ T l).card ≤ 3) :
    ∀ w, S w ⊆ S r → p ∈ S w → p ∈ pruned S G kids w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwr hp
    by_cases hw : w ∈ G
    · have hp' : p ∈ (kids w).biUnion S := by rwa [← hunion w hw]
      obtain ⟨c, hc, hpc⟩ := Finset.mem_biUnion.mp hp'
      have hcw : S c ⊆ S w := by
        intro q hq
        rw [hunion w hw]
        exact Finset.mem_biUnion.mpr ⟨c, hc, hq⟩
      rw [pruned_or S G kids w hw (hlt w hw)]
      exact Finset.mem_biUnion.mpr
        ⟨c, hc, ih c (hlt w hw c hc) (hcw.trans hwr) hpc⟩
    · obtain ⟨hwL, hwa⟩ := hlabel w hw ⟨p, hp⟩
      have hinside : (S w ∩ T l).card ≤ 3 := by
        refine (Finset.card_le_card ?_).trans (hexcl w hwL (hwa hp))
        intro q hq
        obtain ⟨hqs, hqt⟩ := Finset.mem_inter.mp hq
        exact Finset.mem_inter.mpr ⟨hwa hqs, hqt⟩
      have houtside : (S w \ T l).card ≤ 4 := by
        refine (Finset.card_le_card ?_).trans hnear
        intro q hq
        obtain ⟨hqs, hqt⟩ := Finset.mem_sdiff.mp hq
        exact Finset.mem_sdiff.mpr ⟨hwr hqs, hqt⟩
      have hcover : S w ⊆ (S w ∩ T l) ∪ (S w \ T l) := by
        intro q hq
        by_cases hqt : q ∈ T l
        · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hq, hqt⟩)
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hq, hqt⟩)
      have hc := Finset.card_le_card hcover
      have hu := Finset.card_union_le (S w ∩ T l) (S w \ T l)
      have hs : (S w).card ≤ 9 := by omega
      simpa only [pruned_leaf S G kids w hw, ite_eq_left hs] using hp

theorem count_residual {n m K : ℕ} (T : Fin m → Finset (Fin n))
    (hT : ∀ i j, i ≠ j → (T i ∩ T j).card ≤ 1)
    (S : ℕ → Finset (Fin n)) (G L : Finset ℕ) (kids : ℕ → Finset ℕ)
    (A : ℕ → Finset (Fin n))
    (hkids : ∀ g ∈ G, (kids g).card ≤ 2)
    (hlt : ∀ g ∈ G, ∀ c ∈ kids g, c < g)
    (hunion : ∀ g ∈ G, S g = (kids g).biUnion S)
    (hlabel : ∀ g, g ∉ G → (S g).Nonempty → g ∈ L ∧ S g ⊆ A g)
    (root : Fin K → ℕ) (line : Fin K → Fin m)
    (hnear : ∀ j, (S (root j) \ T (line j)).card ≤ 4)
    (E : Finset (Fin n × Fin m))
    (hcover : ∀ e ∈ E, ∃ j, e.2 = line j ∧ e.1 ∈ S (root j))
    (hexcl : ∀ e ∈ E, ∀ g ∈ L, e.1 ∈ A g → (A g ∩ T e.2).card ≤ 3) :
    E.card ≤ 18 * G.card + 9 * K := by
  apply Pilot5bMeta1020NearStar.count_subset T hT (pruned S G kids) G kids hkids hlt
    (fun g hg => pruned_or S G kids g hg (hlt g hg))
    (pruned_large S G kids) root line
    (fun j => pruned_near S G kids hlt hunion T (root j) (line j) (hnear j)) E
  intro e he
  obtain ⟨j, hj, hp⟩ := hcover e he
  refine ⟨j, hj, ?_⟩
  apply preserve S G L kids A hlt hunion hlabel T (root j) (line j) e.1 (hnear j)
    (fun g hg hpg => by simpa only [← hj] using hexcl e he g hg hpg)
    (root j) (Finset.Subset.refl _) hp

end Pilot5bMeta1020PrunedNearStar



namespace BlockedPairs

lemma filter_product_card_le_rows
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (P : Finset α) (Q : Finset β) (R : α → β → Prop) [DecidableRel R] (k : ℕ)
    (h : ∀ p ∈ P, (Q.filter (R p)).card ≤ k) :
    ((P.product Q).filter (fun e => R e.1 e.2)).card ≤ P.card * k := by
  classical
  let rows : α → Finset (α × β) := fun p => (Q.filter (R p)).image (fun q => (p, q))
  have hsub : (P.product Q).filter (fun e => R e.1 e.2) ⊆ P.biUnion rows := by
    intro e he
    obtain ⟨he, hR⟩ := Finset.mem_filter.mp he
    obtain ⟨hp, hq⟩ := Finset.mem_product.mp he
    apply Finset.mem_biUnion.mpr
    refine ⟨e.1, hp, ?_⟩
    exact Finset.mem_image.mpr ⟨e.2, Finset.mem_filter.mpr ⟨hq, hR⟩, rfl⟩
  calc
    ((P.product Q).filter (fun e => R e.1 e.2)).card ≤ (P.biUnion rows).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ p ∈ P, (rows p).card := Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ P, k := by
      apply Finset.sum_le_sum
      intro p hp
      exact Finset.card_image_le.trans (h p hp)
    _ = P.card * k := by simp

lemma filter_product_card_le_columns
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (P : Finset α) (Q : Finset β) (R : α → β → Prop) [DecidableRel R] (k : ℕ)
    (h : ∀ q ∈ Q, (P.filter (fun p => R p q)).card ≤ k) :
    ((P.product Q).filter (fun e => R e.1 e.2)).card ≤ Q.card * k := by
  classical
  let cols : β → Finset (α × β) := fun q => (P.filter (fun p => R p q)).image (fun p => (p, q))
  have hsub : (P.product Q).filter (fun e => R e.1 e.2) ⊆ Q.biUnion cols := by
    intro e he
    obtain ⟨he, hR⟩ := Finset.mem_filter.mp he
    obtain ⟨hp, hq⟩ := Finset.mem_product.mp he
    apply Finset.mem_biUnion.mpr
    refine ⟨e.2, hq, ?_⟩
    exact Finset.mem_image.mpr ⟨e.1, Finset.mem_filter.mpr ⟨hp, hR⟩, rfl⟩
  calc
    ((P.product Q).filter (fun e => R e.1 e.2)).card ≤ (Q.biUnion cols).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ q ∈ Q, (cols q).card := Finset.card_biUnion_le
    _ ≤ ∑ _q ∈ Q, k := by
      apply Finset.sum_le_sum
      intro q hq
      exact Finset.card_image_le.trans (h q hq)
    _ = Q.card * k := by simp

lemma product_card_le_of_all_blocked
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (P : Finset α) (Q : Finset β) (B₁ B₂ : α → β → Prop)
    [DecidableRel B₁] [DecidableRel B₂]
    (h₁ : ∀ p ∈ P, (Q.filter (B₁ p)).card ≤ 2)
    (h₂ : ∀ q ∈ Q, (P.filter (fun p => B₂ p q)).card ≤ 2)
    (hblock : ∀ p ∈ P, ∀ q ∈ Q, B₁ p q ∨ B₂ p q) :
    P.card * Q.card ≤ 2 * P.card + 2 * Q.card := by
  classical
  have hsub : P.product Q ⊆
      ((P.product Q).filter (fun e => B₁ e.1 e.2)) ∪
      ((P.product Q).filter (fun e => B₂ e.1 e.2)) := by
    intro e he
    obtain ⟨hp, hq⟩ := Finset.mem_product.mp he
    rcases hblock e.1 hp e.2 hq with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he, h⟩)
  have hcard := Finset.card_le_card hsub
  have hu := Finset.card_union_le
    ((P.product Q).filter (fun e => B₁ e.1 e.2))
    ((P.product Q).filter (fun e => B₂ e.1 e.2))
  have hr := filter_product_card_le_rows P Q B₁ 2 h₁
  have hc := filter_product_card_le_columns P Q B₂ 2 h₂
  simp only [Finset.product_eq_sprod, Finset.card_product] at hcard hr hc hu
  omega

lemma exists_unblocked_pair
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (P : Finset α) (Q : Finset β) (B₁ B₂ : α → β → Prop)
    [DecidableRel B₁] [DecidableRel B₂]
    (hP : 5 ≤ P.card) (hQ : 5 ≤ Q.card)
    (h₁ : ∀ p ∈ P, (Q.filter (B₁ p)).card ≤ 2)
    (h₂ : ∀ q ∈ Q, (P.filter (fun p => B₂ p q)).card ≤ 2) :
    ∃ p ∈ P, ∃ q ∈ Q, ¬ B₁ p q ∧ ¬ B₂ p q := by
  classical
  by_contra hn
  have hb : ∀ p ∈ P, ∀ q ∈ Q, B₁ p q ∨ B₂ p q := by
    intro p hp q hq
    by_contra h
    push Not at h
    exact hn ⟨p, hp, q, hq, h⟩
  have hcard := product_card_le_of_all_blocked P Q B₁ B₂ h₁ h₂ hb
  have hP' : (5 : ℤ) ≤ P.card := by exact_mod_cast hP
  have hQ' : (5 : ℤ) ≤ Q.card := by exact_mod_cast hQ
  have hcard' : (P.card : ℤ) * Q.card ≤ 2 * P.card + 2 * Q.card := by
    exact_mod_cast hcard
  have hprod : (0 : ℤ) ≤ ((P.card : ℤ) - 5) * ((Q.card : ℤ) - 5) :=
    mul_nonneg (by omega) (by omega)
  nlinarith

lemma one_card_le_four_of_all_blocked
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (P : Finset α) (Q : Finset β) (B₁ B₂ : α → β → Prop)
    [DecidableRel B₁] [DecidableRel B₂]
    (h₁ : ∀ p ∈ P, (Q.filter (B₁ p)).card ≤ 2)
    (h₂ : ∀ q ∈ Q, (P.filter (fun p => B₂ p q)).card ≤ 2)
    (hblock : ∀ p ∈ P, ∀ q ∈ Q, B₁ p q ∨ B₂ p q) :
    P.card ≤ 4 ∨ Q.card ≤ 4 := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨p, hp, q, hq, h₁', h₂'⟩ :=
    exists_unblocked_pair P Q B₁ B₂ (by omega) (by omega) h₁ h₂
  exact (hblock p hp q hq).elim h₁' h₂'

lemma exists_pair_avoiding_small_sets
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (P : Finset α) (Q : Finset β)
    (blockQ : α → Finset β) (blockP : β → Finset α)
    (hP : 5 ≤ P.card) (hQ : 5 ≤ Q.card)
    (h₁ : ∀ p ∈ P, (blockQ p).card ≤ 2)
    (h₂ : ∀ q ∈ Q, (blockP q).card ≤ 2) :
    ∃ p ∈ P, ∃ q ∈ Q, q ∉ blockQ p ∧ p ∉ blockP q := by
  apply exists_unblocked_pair P Q (fun p q => q ∈ blockQ p)
    (fun p q => p ∈ blockP q) hP hQ
  · intro p hp
    apply le_trans (Finset.card_le_card ?_) (h₁ p hp)
    intro q hq
    exact (Finset.mem_filter.mp hq).2
  · intro q hq
    apply le_trans (Finset.card_le_card ?_) (h₂ q hq)
    intro p hp
    exact (Finset.mem_filter.mp hp).2

lemma one_card_le_four_of_all_mem_blocked
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (P : Finset α) (Q : Finset β)
    (blockQ : α → Finset β) (blockP : β → Finset α)
    (h₁ : ∀ p ∈ P, (blockQ p).card ≤ 2)
    (h₂ : ∀ q ∈ Q, (blockP q).card ≤ 2)
    (hblock : ∀ p ∈ P, ∀ q ∈ Q, q ∈ blockQ p ∨ p ∈ blockP q) :
    P.card ≤ 4 ∨ Q.card ≤ 4 := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨p, hp, q, hq, h₁', h₂'⟩ :=
    exists_pair_avoiding_small_sets P Q blockQ blockP (by omega) (by omega) h₁ h₂
  exact (hblock p hp q hq).elim h₁' h₂'

end BlockedPairs


namespace SourceQueries

variable {P L : Type*} [DecidableEq L]

def LinearPencils (A : P → Finset L) : Prop :=
  ∀ p q, p ≠ q → (A p ∩ A q).card ≤ 1

lemma query_inter_subset (A : P → Finset L) (Q : Finset L) (a b p : P)
    (hQ : Q ⊆ A a ∪ A b) :
    Q ∩ A p ⊆ (A a ∩ A p) ∪ (A b ∩ A p) := by
  intro l hl
  obtain ⟨hlQ, hlp⟩ := Finset.mem_inter.mp hl
  rcases Finset.mem_union.mp (hQ hlQ) with hla | hlb
  · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hla, hlp⟩)
  · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hlb, hlp⟩)

lemma heavy_owner_eq (A : P → Finset L) (hA : LinearPencils A)
    (Q : Finset L) (a b p : P) (hQ : Q ⊆ A a ∪ A b)
    (hp : 3 ≤ (Q ∩ A p).card) : p = a ∨ p = b := by
  classical
  by_contra h
  push Not at h
  have ha := hA a p (Ne.symm h.1)
  have hb := hA b p (Ne.symm h.2)
  have hsub := Finset.card_le_card (query_inter_subset A Q a b p hQ)
  have hunion := Finset.card_union_le (A a ∩ A p) (A b ∩ A p)
  omega

lemma heavy_owners_subset [Fintype P] [DecidableEq P] (A : P → Finset L)
    (hA : LinearPencils A) (Q : Finset L) (a b : P)
    (hQ : Q ⊆ A a ∪ A b) :
    Finset.univ.filter (fun p => 3 ≤ (Q ∩ A p).card) ⊆ ({a, b} : Finset P) := by
  classical
  intro p hp
  have heq := heavy_owner_eq A hA Q a b p hQ (Finset.mem_filter.mp hp).2
  simpa only [Finset.mem_insert, Finset.mem_singleton] using heq

lemma heavy_owners_card [Fintype P] (A : P → Finset L)
    (hA : LinearPencils A) (Q : Finset L)
    (hQ : ∃ a b, Q ⊆ A a ∪ A b) :
    (Finset.univ.filter (fun p => 3 ≤ (Q ∩ A p).card)).card ≤ 2 := by
  classical
  obtain ⟨a, b, hQ⟩ := hQ
  have hsub := Finset.card_le_card (heavy_owners_subset A hA Q a b hQ)
  have hpair : ({a, b} : Finset P).card ≤ 2 := by
    exact le_trans (Finset.card_insert_le a {b}) (by simp)
  omega

lemma query_card_le_inter_sum (A : P → Finset L) (Q : Finset L) (p q : P)
    (hQ : Q ⊆ A p ∪ A q) :
    Q.card ≤ (Q ∩ A p).card + (Q ∩ A q).card := by
  have hsub : Q ⊆ (Q ∩ A p) ∪ (Q ∩ A q) := by
    intro l hl
    rcases Finset.mem_union.mp (hQ hl) with hp | hq
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hl, hp⟩)
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hl, hq⟩)
  exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)

lemma other_owner_heavy (A : P → Finset L) (Q : Finset L) (p q : P)
    (hlarge : 5 ≤ Q.card) (hp : (Q ∩ A p).card ≤ 2)
    (hQ : Q ⊆ A p ∪ A q) : 3 ≤ (Q ∩ A q).card := by
  have hcard := query_card_le_inter_sum A Q p q hQ
  omega

noncomputable def blockers [Fintype P] (A : P → Finset L) (Q : Finset L) : Finset P := by
  classical
  exact if ∃ a b, Q ⊆ A a ∪ A b then
    Finset.univ.filter (fun p => 3 ≤ (Q ∩ A p).card) else ∅

lemma blockers_card [Fintype P] (A : P → Finset L)
    (hA : LinearPencils A) (Q : Finset L) : (blockers A Q).card ≤ 2 := by
  classical
  unfold blockers
  split_ifs with hQ
  · exact heavy_owners_card A hA Q hQ
  · simp

lemma mem_blockers_iff [Fintype P] (A : P → Finset L) (Q : Finset L) (p : P) :
    p ∈ blockers A Q ↔ (∃ a b, Q ⊆ A a ∪ A b) ∧ 3 ≤ (Q ∩ A p).card := by
  classical
  unfold blockers
  split_ifs <;> simp_all

lemma exists_outside_two [Fintype P] (A : P → Finset L) (Q : Finset L) (p q : P)
    (hlarge : 5 ≤ Q.card) (hp : p ∉ blockers A Q) (hq : q ∉ blockers A Q) :
    ∃ l ∈ Q, l ∉ A p ∧ l ∉ A q := by
  classical
  by_contra h
  push Not at h
  have hQ : Q ⊆ A p ∪ A q := by
    intro l hl
    rw [Finset.mem_union]
    by_cases hlp : l ∈ A p
    · exact Or.inl hlp
    · exact Or.inr (h l hl hlp)
  have hcover : ∃ a b, Q ⊆ A a ∪ A b := ⟨p, q, hQ⟩
  have hp2 : (Q ∩ A p).card ≤ 2 := by
    by_contra hp2
    exact hp ((mem_blockers_iff A Q p).mpr ⟨hcover, by omega⟩)
  have hq3 := other_owner_heavy A Q p q hlarge hp2 hQ
  exact hq ((mem_blockers_iff A Q q).mpr ⟨hcover, hq3⟩)

lemma linearPencils_of_noRect [Fintype L] (I : P → L → Prop) [DecidableRel I]
    (hI : ∀ p q l u, p ≠ q → l ≠ u → ¬ (I p l ∧ I p u ∧ I q l ∧ I q u)) :
    LinearPencils (fun p => Finset.univ.filter (I p)) := by
  intro p q hpq
  rw [Finset.card_le_one]
  intro l hl u hu
  by_contra hlu
  have hl' : I p l ∧ I q l := by simpa only [Finset.mem_inter, Finset.mem_filter,
    Finset.mem_univ, true_and] using hl
  have hu' : I p u ∧ I q u := by simpa only [Finset.mem_inter, Finset.mem_filter,
    Finset.mem_univ, true_and] using hu
  exact hI p q l u hpq hlu ⟨hl'.1, hu'.1, hl'.2, hu'.2⟩


end SourceQueries


namespace Pilot5bMeta1020FirstQuery

open Finset

variable {P L G : Type*} [Fintype P] [Fintype L] [DecidableEq P] [DecidableEq L]
  [DecidableEq G]

def fiber (I : P → L → Prop) [DecidableRel I] (S : Finset P)
    (E : Finset (P × L)) (l : L) : Finset P :=
  S.filter fun p => I p l ∧ (p, l) ∉ E

lemma fiber_small (I : P → L → Prop) [DecidableRel I] (S : Finset P)
    (E : Finset (P × L)) (l : L)
    (hheavy : ∀ p ∈ S, I p l → 4 ≤ (S.filter fun q => I q l).card → (p, l) ∈ E) :
    (fiber I S E l).card ≤ 3 := by
  by_cases hlarge : 4 ≤ (S.filter fun q => I q l).card
  · have hempty : fiber I S E l = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      obtain ⟨hpS, hpI, hpE⟩ := Finset.mem_filter.mp hp
      exact hpE (hheavy p hpS hpI hlarge)
    simp [hempty]
  · have hsub : fiber I S E l ⊆ S.filter fun q => I q l := by
      intro p hp
      obtain ⟨hpS, hpI, _⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨hpS, hpI⟩
    have := Finset.card_le_card hsub
    omega

def smallPairs (I : P → L → Prop) [DecidableRel I]
    (gs : Finset G) (S : G → Finset P) (A : G → Finset L)
    (E : Finset (P × L)) : Finset (P × L) :=
  Finset.univ.filter fun e => e ∉ E ∧ I e.1 e.2 ∧
    ∃ g ∈ gs, e.1 ∈ S g ∧ e.2 ∈ A g ∧ (A g).card ≤ 4

lemma smallPairs_bound_of_fibers (I : P → L → Prop) [DecidableRel I]
    (gs : Finset G) (S : G → Finset P) (A : G → Finset L)
    (E : Finset (P × L))
    (hfiber : ∀ g ∈ gs, ∀ l, (fiber I (S g) E l).card ≤ 3) :
    (smallPairs I gs S A E).card ≤ 12 * gs.card := by
  classical
  let B : G → Finset (P × L) := fun g =>
    if (A g).card ≤ 4 then
      (A g).biUnion fun l => (fiber I (S g) E l).image fun p => (p, l)
    else ∅
  have hB : ∀ g ∈ gs, (B g).card ≤ 12 := by
    intro g hg
    dsimp only [B]
    split_ifs with hsmall
    · have hcard := Finset.card_biUnion_le_card_mul (A g)
        (fun l => (fiber I (S g) E l).image fun p => (p, l)) 3 (by
          intro l _
          exact Finset.card_image_le.trans (hfiber g hg l))
      omega
    · simp
  have hsub : smallPairs I gs S A E ⊆ gs.biUnion B := by
    intro e he
    obtain ⟨_, heE, heI, g, hg, hp, hl, hsmall⟩ := Finset.mem_filter.mp he
    apply Finset.mem_biUnion.mpr
    refine ⟨g, hg, ?_⟩
    simp only [B, if_pos hsmall, Finset.mem_biUnion]
    refine ⟨e.2, hl, Finset.mem_image.mpr ⟨e.1, ?_, by simp⟩⟩
    exact Finset.mem_filter.mpr ⟨hp, heI, heE⟩
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_biUnion_le_card_mul gs B 12 hB).trans (by omega))

theorem small_first_query_bound (I : P → L → Prop) [DecidableRel I]
    (gs : Finset G) (S : G → Finset P) (A : G → Finset L)
    (E : Finset (P × L))
    (hheavy : ∀ g ∈ gs, ∀ l p, p ∈ S g → I p l →
      4 ≤ ((S g).filter fun q => I q l).card → (p, l) ∈ E) :
    (smallPairs I gs S A E).card ≤ 12 * gs.card := by
  apply smallPairs_bound_of_fibers I gs S A E
  intro g hg l
  exact fiber_small I (S g) E l fun p hp hI hcard => hheavy g hg l p hp hI hcard

def pencil (I : P → L → Prop) [DecidableRel I] (p : P) : Finset L :=
  Finset.univ.filter (I p)

def coveredByTwo (I : P → L → Prop) [DecidableRel I] (A : Finset L) : Prop :=
  ∃ T : Finset P, T.card ≤ 2 ∧ A ⊆ T.biUnion (pencil I)

def goodFirst (I : P → L → Prop) [DecidableRel I] (A : Finset L) (p : P) : Prop :=
  5 ≤ A.card ∧ ¬ (coveredByTwo I A ∧ 3 ≤ (A.filter (I p)).card)

noncomputable def ownHeavyPairs (I : P → L → Prop) [DecidableRel I]
    (gs : Finset G) (A : G → Finset L) : Finset (P × L) := by
  classical
  exact Finset.univ.filter fun e => I e.1 e.2 ∧ ∃ g ∈ gs,
    e.2 ∈ A g ∧ coveredByTwo I (A g) ∧ 3 ≤ ((A g).filter (I e.1)).card

lemma goodFirst_of_uncharged (I : P → L → Prop) [DecidableRel I]
    (gs : Finset G) (S : G → Finset P) (A : G → Finset L)
    (E : Finset (P × L)) (p : P) (l : L) (g : G)
    (hg : g ∈ gs) (hp : p ∈ S g) (hl : l ∈ A g) (hI : I p l)
    (hE : (p, l) ∉ E)
    (hsmall : (p, l) ∉ smallPairs I gs S A E)
    (hown : (p, l) ∉ ownHeavyPairs I gs A) : goodFirst I (A g) p := by
  classical
  constructor
  · by_contra! hc
    apply hsmall
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hE, hI,
      g, hg, hp, hl, by omega⟩
  · rintro ⟨hcover, hheavy⟩
    apply hown
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hI,
      g, hg, hl, hcover, hheavy⟩

section Network

variable (I : P → L → Prop) [DecidableRel I]
  (orG labelG : Finset ℕ) (kids : ℕ → Finset ℕ) (child : ℕ → ℕ)
  (alive retained : ℕ → Finset P) (bare : ℕ → Finset L)
  (row : ℕ → P → Finset L)
  (or_lower : ∀ i ∈ orG, ∀ c ∈ kids i, c < i)
  (label_lower : ∀ i ∈ labelG, child i < i)
  (retained_or : ∀ i ∈ orG, ∀ p, p ∈ retained i ↔ ∃ c ∈ kids i, p ∈ retained c)
  (retained_label : ∀ i ∈ labelG, ∀ p, p ∈ retained i ↔ p ∈ alive i ∧
    (p ∈ retained (child i) ∨ goodFirst I (bare (child i)) p))
  (retained_other : ∀ i, i ∉ orG → i ∉ labelG → retained i = ∅)
  (row_or : ∀ i ∈ orG, ∀ p l, l ∈ row i p ↔ ∃ c ∈ kids i, l ∈ row c p)
  (row_label : ∀ i ∈ labelG, ∀ p l, l ∈ row i p ↔ p ∈ alive i ∧ l ∈ row (child i) p)
  (row_other : ∀ i, i ∉ orG → i ∉ labelG → ∀ p, row i p = bare i)
  (bare_or : ∀ i ∈ orG, ∀ l, l ∈ bare i ↔ ∃ c ∈ kids i, l ∈ bare c)
  (bare_sub_row : ∀ i p, bare i ⊆ row i p)

include or_lower label_lower row_or row_label row_other bare_or bare_sub_row in
theorem first_origin (i : ℕ) (p : P) (l : L) (hl : l ∈ row i p) :
    l ∈ bare i ∨ ∃ g ∈ labelG, p ∈ alive g ∧ l ∈ bare (child g) ∧
      bare (child g) ⊆ row i p := by
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    by_cases hor : i ∈ orG
    · obtain ⟨c, hc, hlc⟩ := (row_or i hor p l).mp hl
      rcases ih c (or_lower i hor c hc) hlc with hbare | ⟨g, hg, hpa, hline, hsub⟩
      · exact Or.inl ((bare_or i hor l).mpr ⟨c, hc, hbare⟩)
      · refine Or.inr ⟨g, hg, hpa, hline, ?_⟩
        intro u hu
        exact (row_or i hor p u).mpr ⟨c, hc, hsub hu⟩
    · by_cases hlabel : i ∈ labelG
      · obtain ⟨hpa, hlc⟩ := (row_label i hlabel p l).mp hl
        rcases ih (child i) (label_lower i hlabel) hlc with hbare | ⟨g, hg, hpag, hline, hsub⟩
        · refine Or.inr ⟨i, hlabel, hpa, hbare, ?_⟩
          intro u hu
          exact (row_label i hlabel p u).mpr ⟨hpa, bare_sub_row (child i) p hu⟩
        · refine Or.inr ⟨g, hg, hpag, hline, ?_⟩
          intro u hu
          exact (row_label i hlabel p u).mpr ⟨hpa, hsub hu⟩
      · exact Or.inl (by simpa only [row_other i hor hlabel p] using hl)

include or_lower label_lower retained_or retained_label retained_other row_or row_label
  bare_sub_row in
theorem retained_origin (i : ℕ) (p : P) (hp : p ∈ retained i) :
    ∃ g ∈ labelG, p ∈ alive g ∧ goodFirst I (bare (child g)) p ∧
      bare (child g) ⊆ row i p := by
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    by_cases hor : i ∈ orG
    · obtain ⟨c, hc, hpc⟩ := (retained_or i hor p).mp hp
      obtain ⟨g, hg, hpa, hgood, hsub⟩ := ih c (or_lower i hor c hc) hpc
      refine ⟨g, hg, hpa, hgood, ?_⟩
      intro l hl
      exact (row_or i hor p l).mpr ⟨c, hc, hsub hl⟩
    · by_cases hlabel : i ∈ labelG
      · obtain ⟨hpa, hprev | hgood⟩ := (retained_label i hlabel p).mp hp
        · obtain ⟨g, hg, hpag, hgood, hsub⟩ := ih (child i) (label_lower i hlabel) hprev
          refine ⟨g, hg, hpag, hgood, ?_⟩
          intro l hl
          exact (row_label i hlabel p l).mpr ⟨hpa, hsub hl⟩
        · refine ⟨i, hlabel, hpa, hgood, ?_⟩
          intro l hl
          exact (row_label i hlabel p l).mpr ⟨hpa, bare_sub_row (child i) p hl⟩
      · rw [retained_other i hor hlabel] at hp
        exact (Finset.notMem_empty _ hp).elim

include or_lower label_lower retained_or retained_label row_or row_label row_other bare_or in
theorem uncharged_pair_retained (E : Finset (P × L)) (p : P) (l : L)
    (hI : I p l) (hE : (p, l) ∉ E)
    (hsmall : (p, l) ∉ smallPairs I labelG alive (fun g => bare (child g)) E)
    (hown : (p, l) ∉ ownHeavyPairs I labelG (fun g => bare (child g))) :
    ∀ i, l ∈ row i p → l ∉ bare i → p ∈ retained i := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hl hbare
    by_cases hor : i ∈ orG
    · obtain ⟨c, hc, hlc⟩ := (row_or i hor p l).mp hl
      have hbc : l ∉ bare c := fun h => hbare ((bare_or i hor l).mpr ⟨c, hc, h⟩)
      exact (retained_or i hor p).mpr ⟨c, hc, ih c (or_lower i hor c hc) hlc hbc⟩
    · by_cases hlabel : i ∈ labelG
      · obtain ⟨hpa, hlc⟩ := (row_label i hlabel p l).mp hl
        apply (retained_label i hlabel p).mpr
        refine ⟨hpa, ?_⟩
        by_cases hbc : l ∈ bare (child i)
        · exact Or.inr (goodFirst_of_uncharged I labelG alive
            (fun g => bare (child g)) E p l i hlabel hpa hbc hI hE hsmall hown)
        · exact Or.inl (ih (child i) (label_lower i hlabel) hlc hbc)
      · rw [row_other i hor hlabel p] at hl
        exact (hbare hl).elim

end Network

end Pilot5bMeta1020FirstQuery

namespace MarkerNearStar

open SourceQueries
open BlockedPairs

variable {Point Line : Type*} [Fintype Point] [DecidableEq Line]

def outside (A : Point → Finset Line) (l : Line) (P : Finset Point) : Finset Point :=
  P.filter (fun p => l ∉ A p)

def HasOrigin (A : Point → Finset Line) (row : Point → Finset Line) (p : Point) : Prop :=
  ∃ S : Finset Line, 5 ≤ S.card ∧ p ∉ blockers A S ∧ S ⊆ row p

lemma two_factor_near_star_of_queries
    (A : Point → Finset Line) (hA : LinearPencils A)
    (l : Line) (P Q : Finset Point)
    (rowP rowQ queryP queryQ : Point → Finset Line)
    (hP : ∀ p ∈ P, 5 ≤ (queryP p).card ∧
      p ∉ blockers A (queryP p) ∧ queryP p ⊆ rowP p)
    (hQ : ∀ q ∈ Q, 5 ≤ (queryQ q).card ∧
      q ∉ blockers A (queryQ q) ∧ queryQ q ⊆ rowQ q)
    (hsound : ∀ p ∈ P, l ∉ A p → ∀ q ∈ Q, l ∉ A q →
      ∀ u ∈ rowP p, ∀ v ∈ rowQ q,
        u ∉ A p → u ∉ A q → v ∉ A p → v ∉ A q → False) :
    (outside A l P).card ≤ 4 ∨ (outside A l Q).card ≤ 4 := by
  classical
  apply one_card_le_four_of_all_mem_blocked (outside A l P) (outside A l Q)
    (fun p => blockers A (queryP p)) (fun q => blockers A (queryQ q))
  · intro p _
    exact blockers_card A hA (queryP p)
  · intro q _
    exact blockers_card A hA (queryQ q)
  · intro p hp q hq
    obtain ⟨hpP, hpl⟩ := Finset.mem_filter.mp hp
    obtain ⟨hqQ, hql⟩ := Finset.mem_filter.mp hq
    obtain ⟨hpLarge, hpOwn, hpRow⟩ := hP p hpP
    obtain ⟨hqLarge, hqOwn, hqRow⟩ := hQ q hqQ
    by_contra hn
    push Not at hn
    obtain ⟨u, hu, hup, huq⟩ :=
      exists_outside_two A (queryP p) p q hpLarge hpOwn hn.1
    obtain ⟨v, hv, hvq, hvp⟩ :=
      exists_outside_two A (queryQ q) q p hqLarge hqOwn hn.2
    exact hsound p hpP hpl q hqQ hql u (hpRow hu) v (hqRow hv) hup huq hvp hvq

lemma two_factor_near_star
    (A : Point → Finset Line) (hA : LinearPencils A)
    (l : Line) (P Q : Finset Point) (rowP rowQ : Point → Finset Line)
    (hP : ∀ p ∈ P, HasOrigin A rowP p)
    (hQ : ∀ q ∈ Q, HasOrigin A rowQ q)
    (hsound : ∀ p ∈ P, l ∉ A p → ∀ q ∈ Q, l ∉ A q →
      ∀ u ∈ rowP p, ∀ v ∈ rowQ q,
        u ∉ A p → u ∉ A q → v ∉ A p → v ∉ A q → False) :
    (outside A l P).card ≤ 4 ∨ (outside A l Q).card ≤ 4 := by
  classical
  let queryP : Point → Finset Line := fun p =>
    if hp : p ∈ P then Classical.choose (hP p hp) else ∅
  let queryQ : Point → Finset Line := fun q =>
    if hq : q ∈ Q then Classical.choose (hQ q hq) else ∅
  apply two_factor_near_star_of_queries A hA l P Q rowP rowQ queryP queryQ
  · intro p hp
    simpa only [queryP, dite_eq_left hp] using Classical.choose_spec (hP p hp)
  · intro q hq
    simpa only [queryQ, dite_eq_left hq] using Classical.choose_spec (hQ q hq)
  · exact hsound

lemma one_factor_star
    (A : Point → Finset Line) (l : Line) (P : Finset Point)
    (row : Point → Finset Line)
    (hP : ∀ p ∈ P, HasOrigin A row p)
    (hsound : ∀ p ∈ P, l ∉ A p → ∀ u ∈ row p, u ∉ A p → False) :
    ∀ p ∈ P, l ∈ A p := by
  intro p hp
  by_contra hpl
  obtain ⟨S, hS, hpS, hrow⟩ := hP p hp
  obtain ⟨u, hu, hup, _⟩ := exists_outside_two A S p p hS hpS hpS
  exact hsound p hp hpl u (hrow hu) hup

lemma one_factor_outside_empty
    (A : Point → Finset Line) (l : Line) (P : Finset Point)
    (row : Point → Finset Line)
    (hP : ∀ p ∈ P, HasOrigin A row p)
    (hsound : ∀ p ∈ P, l ∉ A p → ∀ u ∈ row p, u ∉ A p → False) :
    outside A l P = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨hpP, hpl⟩ := Finset.mem_filter.mp hp
  exact hpl (one_factor_star A l P row hP hsound p hpP)

lemma one_factor_outside_card_zero
    (A : Point → Finset Line) (l : Line) (P : Finset Point)
    (row : Point → Finset Line)
    (hP : ∀ p ∈ P, HasOrigin A row p)
    (hsound : ∀ p ∈ P, l ∉ A p → ∀ u ∈ row p, u ∉ A p → False) :
    (outside A l P).card = 0 := by
  rw [one_factor_outside_empty A l P row hP hsound]
  rfl

end MarkerNearStar

namespace MarkerNearStar

open Pilot5bMeta1020FirstQuery
open SourceQueries

variable {Point Line Gate : Type*}
  [Fintype Point] [Fintype Line] [DecidableEq Point] [DecidableEq Line]

omit [Fintype Point] in
lemma pair_cover_is_coveredByTwo
    (I : Point → Line → Prop) [DecidableRel I]
    (S : Finset Line) (a b : Point)
    (h : S ⊆ pencil I a ∪ pencil I b) : coveredByTwo I S := by
  refine ⟨{a, b}, ?_, ?_⟩
  · exact (Finset.card_insert_le a {b}).trans (by simp)
  · intro l hl
    rcases Finset.mem_union.mp (h hl) with ha | hb
    · exact Finset.mem_biUnion.mpr ⟨a, by simp, ha⟩
    · exact Finset.mem_biUnion.mpr ⟨b, by simp, hb⟩

lemma goodFirst_not_blocker
    (I : Point → Line → Prop) [DecidableRel I]
    (S : Finset Line) (p : Point) (h : goodFirst I S p) :
    p ∉ blockers (pencil I) S := by
  intro hp
  obtain ⟨⟨a, b, hcover⟩, hheavy⟩ := (mem_blockers_iff (pencil I) S p).mp hp
  have heq : S ∩ pencil I p = S.filter (I p) := by
    ext l
    simp [pencil]
  rw [heq] at hheavy
  exact h.2 ⟨pair_cover_is_coveredByTwo I S a b hcover, hheavy⟩

lemma hasOrigin_of_goodFirst
    (I : Point → Line → Prop) [DecidableRel I]
    (row : Point → Finset Line) (p : Point) (S : Finset Line)
    (h : goodFirst I S p) (hsub : S ⊆ row p) :
    HasOrigin (pencil I) row p :=
  ⟨S, h.1, goodFirst_not_blocker I S p h, hsub⟩

lemma hasOrigin_of_retained_origin
    (I : Point → Line → Prop) [DecidableRel I]
    (labelG : Finset Gate) (alive : Gate → Finset Point)
    (query : Gate → Finset Line) (row : Point → Finset Line) (p : Point)
    (h : ∃ g ∈ labelG, p ∈ alive g ∧ goodFirst I (query g) p ∧ query g ⊆ row p) :
    HasOrigin (pencil I) row p := by
  obtain ⟨g, _, _, hgood, hsub⟩ := h
  exact hasOrigin_of_goodFirst I row p (query g) hgood hsub

lemma two_factor_near_star_of_retained_origins
    (I : Point → Line → Prop) [DecidableRel I]
    (hI : ∀ p q l u, p ≠ q → l ≠ u → ¬ (I p l ∧ I p u ∧ I q l ∧ I q u))
    (l : Line) (P Q : Finset Point) (rowP rowQ : Point → Finset Line)
    (labelG : Finset Gate) (alive : Gate → Finset Point) (query : Gate → Finset Line)
    (hP : ∀ p ∈ P, ∃ g ∈ labelG,
      p ∈ alive g ∧ goodFirst I (query g) p ∧ query g ⊆ rowP p)
    (hQ : ∀ q ∈ Q, ∃ g ∈ labelG,
      q ∈ alive g ∧ goodFirst I (query g) q ∧ query g ⊆ rowQ q)
    (hsound : ∀ p ∈ P, ¬ I p l → ∀ q ∈ Q, ¬ I q l →
      ∀ u ∈ rowP p, ∀ v ∈ rowQ q,
        ¬ I p u → ¬ I q u → ¬ I p v → ¬ I q v → False) :
    (P.filter (fun p => ¬ I p l)).card ≤ 4 ∨
      (Q.filter (fun q => ¬ I q l)).card ≤ 4 := by
  have hnear := two_factor_near_star (pencil I) (linearPencils_of_noRect I hI)
    l P Q rowP rowQ
    (fun p hp => hasOrigin_of_retained_origin I labelG alive query rowP p (hP p hp))
    (fun q hq => hasOrigin_of_retained_origin I labelG alive query rowQ q (hQ q hq))
    (by
      intro p hp hpl q hq hql u hu v hv hup huq hvp hvq
      exact hsound p hp (by simpa [pencil] using hpl)
        q hq (by simpa [pencil] using hql) u hu v hv
        (by simpa [pencil] using hup) (by simpa [pencil] using huq)
        (by simpa [pencil] using hvp) (by simpa [pencil] using hvq))
  simpa only [outside, pencil, Finset.mem_filter, Finset.mem_univ, true_and] using hnear

lemma one_factor_star_of_retained_origins
    (I : Point → Line → Prop) [DecidableRel I]
    (l : Line) (P : Finset Point) (row : Point → Finset Line)
    (labelG : Finset Gate) (alive : Gate → Finset Point) (query : Gate → Finset Line)
    (hP : ∀ p ∈ P, ∃ g ∈ labelG,
      p ∈ alive g ∧ goodFirst I (query g) p ∧ query g ⊆ row p)
    (hsound : ∀ p ∈ P, ¬ I p l → ∀ u ∈ row p, ¬ I p u → False) :
    ∀ p ∈ P, I p l := by
  have hstar := one_factor_star (pencil I) l P row
    (fun p hp => hasOrigin_of_retained_origin I labelG alive query row p (hP p hp))
    (by
      intro p hp hpl u hu hup
      exact hsound p hp (by simpa [pencil] using hpl)
        u hu (by simpa [pencil] using hup))
  simpa only [pencil, Finset.mem_filter, Finset.mem_univ, true_and] using hstar

end MarkerNearStar

namespace MarkerNearStar

variable {Point Line Gate : Type*} [DecidableEq Point] [DecidableEq Line]

def MonoEval (f : Finset Point → Finset Line → Bool) : Prop :=
  ∀ X X' Y Y', X ⊆ X' → Y ⊆ Y' → f X Y = true → f X' Y' = true

def SoundMarker (I : Point → Line → Prop) (l : Line)
    (f g : Finset Point → Finset Line → Bool) : Prop :=
  ∀ X Y, l ∈ Y → f X Y = true → g X Y = true → ∃ p ∈ X, ∃ u ∈ Y, I p u

lemma marker_no_restoration
    (I : Point → Line → Prop) (l : Line)
    (f g : Finset Point → Finset Line → Bool)
    (hfmono : MonoEval f) (hgmono : MonoEval g) (hsound : SoundMarker I l f g)
    (p q : Point) (u v : Line) (hf : f {p} {u} = true) (hg : g {q} {v} = true)
    (hpl : ¬ I p l) (hql : ¬ I q l)
    (hpu : ¬ I p u) (hqu : ¬ I q u) (hpv : ¬ I p v) (hqv : ¬ I q v) : False := by
  have hf' : f {p, q} {l, u, v} = true :=
    hfmono {p} {p, q} {u} {l, u, v} (by simp) (by simp) hf
  have hg' : g {p, q} {l, u, v} = true :=
    hgmono {q} {p, q} {v} {l, u, v} (by simp) (by simp) hg
  obtain ⟨r, hr, s, hs, hI⟩ := hsound {p, q} {l, u, v} (by simp) hf' hg'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr hs
  rcases hr with rfl | rfl
  · rcases hs with rfl | rfl | rfl
    · exact hpl hI
    · exact hpu hI
    · exact hpv hI
  · rcases hs with rfl | rfl | rfl
    · exact hql hI
    · exact hqu hI
    · exact hqv hI

lemma marker_one_no_restoration
    (I : Point → Line → Prop) (l : Line)
    (f g : Finset Point → Finset Line → Bool)
    (hfmono : MonoEval f) (hgmono : MonoEval g) (hsound : SoundMarker I l f g)
    (hbare : g ∅ {l} = true)
    (p : Point) (u : Line) (hf : f {p} {u} = true)
    (hpl : ¬ I p l) (hpu : ¬ I p u) : False := by
  have hg : g {p} {l} = true := hgmono ∅ {p} {l} {l} (by simp) (by simp) hbare
  exact marker_no_restoration I l f g hfmono hgmono hsound p p u l hf hg
    hpl hpl hpu hpu hpl hpl

lemma two_factor_near_star_of_marker_semantics
    [Fintype Point] [Fintype Line]
    (I : Point → Line → Prop) [DecidableRel I]
    (hI : ∀ p q l u, p ≠ q → l ≠ u → ¬ (I p l ∧ I p u ∧ I q l ∧ I q u))
    (l : Line) (P Q : Finset Point) (rowP rowQ : Point → Finset Line)
    (labelG : Finset Gate) (alive : Gate → Finset Point) (query : Gate → Finset Line)
    (hP : ∀ p ∈ P, ∃ a ∈ labelG, p ∈ alive a ∧
      Pilot5bMeta1020FirstQuery.goodFirst I (query a) p ∧ query a ⊆ rowP p)
    (hQ : ∀ q ∈ Q, ∃ a ∈ labelG, q ∈ alive a ∧
      Pilot5bMeta1020FirstQuery.goodFirst I (query a) q ∧ query a ⊆ rowQ q)
    (f g : Finset Point → Finset Line → Bool)
    (hfmono : MonoEval f) (hgmono : MonoEval g) (hsound : SoundMarker I l f g)
    (hrowP : ∀ p u, u ∈ rowP p → f {p} {u} = true)
    (hrowQ : ∀ q v, v ∈ rowQ q → g {q} {v} = true) :
    (P.filter (fun p => ¬ I p l)).card ≤ 4 ∨
      (Q.filter (fun q => ¬ I q l)).card ≤ 4 := by
  apply two_factor_near_star_of_retained_origins I hI l P Q rowP rowQ
    labelG alive query hP hQ
  intro p _ hpl q _ hql u hu v hv hpu hqu hpv hqv
  exact marker_no_restoration I l f g hfmono hgmono hsound p q u v
    (hrowP p u hu) (hrowQ q v hv) hpl hql hpu hqu hpv hqv

lemma one_factor_star_of_marker_semantics
    [Fintype Point] [Fintype Line]
    (I : Point → Line → Prop) [DecidableRel I]
    (l : Line) (P : Finset Point) (row : Point → Finset Line)
    (labelG : Finset Gate) (alive : Gate → Finset Point) (query : Gate → Finset Line)
    (hP : ∀ p ∈ P, ∃ a ∈ labelG, p ∈ alive a ∧
      Pilot5bMeta1020FirstQuery.goodFirst I (query a) p ∧ query a ⊆ row p)
    (f g : Finset Point → Finset Line → Bool)
    (hfmono : MonoEval f) (hgmono : MonoEval g) (hsound : SoundMarker I l f g)
    (hbare : g ∅ {l} = true)
    (hrow : ∀ p u, u ∈ row p → f {p} {u} = true) :
    ∀ p ∈ P, I p l := by
  apply one_factor_star_of_retained_origins I l P row labelG alive query hP
  intro p _ hpl u hu hpu
  exact marker_one_no_restoration I l f g hfmono hgmono hsound hbare p u
    (hrow p u hu) hpl hpu

end MarkerNearStar

namespace HonestMarkers

variable {N : ℕ}

def pencil (I : Fin N → Fin N → Prop) [DecidableRel I] (p : Fin N) : Finset (Fin N) :=
  Finset.univ.filter (I p)

lemma mem_pencil (I : Fin N → Fin N → Prop) [DecidableRel I] (p l : Fin N) :
    l ∈ pencil I p ↔ I p l := by
  simp [pencil]

lemma honest_factor
    (P A B C : Finset (Fin N))
    (hs : ∀ a ∈ A, ∀ b ∈ B, ∀ c ∈ C, a ∈ P ∨ b ∈ P ∨ c ∈ P) :
    A ⊆ P ∨ B ⊆ P ∨ C ⊆ P := by
  classical
  by_contra hn
  have hnA := (not_or.mp hn).1
  have hnB := (not_or.mp (not_or.mp hn).2).1
  have hnC := (not_or.mp (not_or.mp hn).2).2
  obtain ⟨a, ha, hna⟩ := Finset.not_subset.mp hnA
  obtain ⟨b, hb, hnb⟩ := Finset.not_subset.mp hnB
  obtain ⟨c, hc, hnc⟩ := Finset.not_subset.mp hnC
  rcases hs a ha b hb c hc with h | h | h
  · exact hna h
  · exact hnb h
  · exact hnc h

lemma honest_source_small_or_heavy
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (p : Fin N) (A : Finset (Fin N)) (hA : A ⊆ pencil I p) :
    A.card ≤ 4 ∨
      (5 ≤ A.card ∧ 3 ≤ (A.filter (I p)).card ∧
        ∃ T : Finset (Fin N), T.card ≤ 2 ∧
          ∀ l ∈ A, ∃ q ∈ T, I q l) := by
  classical
  by_cases hs : A.card ≤ 4
  · exact Or.inl hs
  · right
    have hfilter : A.filter (I p) = A := by
      apply Finset.filter_eq_self.mpr
      intro l hl
      exact (mem_pencil I p l).mp (hA hl)
    refine ⟨by omega, ?_, {p}, by simp, ?_⟩
    · rw [hfilter]
      omega
    · intro l hl
      exact ⟨p, Finset.mem_singleton_self p, (mem_pencil I p l).mp (hA hl)⟩

lemma bare_query_dichotomy
    (P A : Finset (Fin N)) (l : Fin N) (hl : l ∈ A) (hA : A ⊆ P) :
    (2 ≤ A.card ∧ A ⊆ P ∧ l ∈ A) ∨ A = {l} := by
  classical
  by_cases htwo : 2 ≤ A.card
  · exact Or.inl ⟨htwo, hA, hl⟩
  · right
    apply Finset.Subset.antisymm
    · intro a ha
      exact Finset.mem_singleton.mpr
        ((Finset.card_le_one.mp (by omega : A.card ≤ 1)) a ha l hl)
    · exact Finset.singleton_subset_iff.mpr hl

lemma honest_accept_cover
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (labels : Finset ℕ) (alive query bare : ℕ → Finset (Fin N))
    (row : ℕ → Fin N → Finset (Fin N))
    (hbare : ∀ r p, bare r ⊆ row r p)
    (horigin : ∀ r p l, l ∈ row r p →
      l ∈ bare r ∨ ∃ g ∈ labels,
        p ∈ alive g ∧ l ∈ query g ∧ query g ⊆ row r p)
    (r : ℕ) (p l : Fin N) (hl : l ∈ row r p)
    (hh : row r p ⊆ pencil I p) :
    (∃ g ∈ labels, p ∈ alive g ∧ l ∈ query g ∧
      ((query g).card ≤ 4 ∨
        (5 ≤ (query g).card ∧ 3 ≤ ((query g).filter (I p)).card ∧
          ∃ T : Finset (Fin N), T.card ≤ 2 ∧
            ∀ u ∈ query g, ∃ q ∈ T, I q u))) ∨
      (2 ≤ (bare r).card ∧ bare r ⊆ pencil I p ∧ l ∈ bare r) ∨ bare r = {l} := by
  classical
  rcases horigin r p l hl with hb | ⟨g, hg, hp, hq, hsub⟩
  · exact Or.inr (bare_query_dichotomy (pencil I p) (bare r) l hb
      (Finset.Subset.trans (hbare r p) hh))
  · exact Or.inl ⟨g, hg, hp, hq,
      honest_source_small_or_heavy I p (query g) (Finset.Subset.trans hsub hh)⟩

lemma triple_honest_accept_cover
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (labels : Finset ℕ) (alive query bare : ℕ → Finset (Fin N))
    (row : ℕ → Fin N → Finset (Fin N))
    (hbare : ∀ r p, bare r ⊆ row r p)
    (horigin : ∀ r p l, l ∈ row r p →
      l ∈ bare r ∨ ∃ g ∈ labels,
        p ∈ alive g ∧ l ∈ query g ∧ query g ⊆ row r p)
    (a b c : ℕ) (p l : Fin N)
    (ha : l ∈ row a p) (hb : l ∈ row b p) (hc : l ∈ row c p)
    (hs : ∀ u ∈ row a p, ∀ v ∈ row b p, ∀ w ∈ row c p,
      I p u ∨ I p v ∨ I p w) :
    ∃ r ∈ ({a, b, c} : Finset ℕ),
      (∃ g ∈ labels, p ∈ alive g ∧ l ∈ query g ∧
        ((query g).card ≤ 4 ∨
          (5 ≤ (query g).card ∧ 3 ≤ ((query g).filter (I p)).card ∧
            ∃ T : Finset (Fin N), T.card ≤ 2 ∧
              ∀ u ∈ query g, ∃ q ∈ T, I q u))) ∨
        (2 ≤ (bare r).card ∧ bare r ⊆ pencil I p ∧ l ∈ bare r) ∨ bare r = {l} := by
  classical
  have hh := honest_factor (pencil I p) (row a p) (row b p) (row c p) (by
    intro u hu v hv w hw
    simpa only [mem_pencil] using hs u hu v hv w hw)
  rcases hh with hh | hh | hh
  · exact ⟨a, by simp, honest_accept_cover I labels alive query bare row hbare horigin
      a p l ha hh⟩
  · exact ⟨b, by simp, honest_accept_cover I labels alive query bare row hbare horigin
      b p l hb hh⟩
  · exact ⟨c, by simp, honest_accept_cover I labels alive query bare row hbare horigin
      c p l hc hh⟩

lemma singleton_markers_card
    {K : ℕ} (bare : ℕ → Finset (Fin N)) (roots : Fin K → Fin 3 → ℕ) :
    ((Finset.univ : Finset ((Fin K × Fin 3) × Fin N)).filter
      (fun x => bare (roots x.1.1 x.1.2) = {x.2})).card ≤ 3 * K := by
  classical
  let jobs := (Finset.univ : Finset ((Fin K × Fin 3) × Fin N)).filter
    (fun x => bare (roots x.1.1 x.1.2) = {x.2})
  have hcard : jobs.card ≤ (Finset.univ : Finset (Fin K × Fin 3)).card := by
    apply Finset.card_le_card_of_injOn (fun x => x.1)
    · intro x hx
      exact Finset.mem_univ _
    · intro x hx y hy hxy
      change x.1 = y.1 at hxy
      have hx' := (Finset.mem_filter.mp hx).2
      have hy' := (Finset.mem_filter.mp hy).2
      have hsingle : ({x.2} : Finset (Fin N)) = {y.2} := by
        rw [← hx', ← hy', hxy]
      exact Prod.ext hxy (Finset.singleton_injective hsingle)
  simpa [jobs, Nat.mul_comm] using hcard

end HonestMarkers
namespace Pilot5bMeta1020TripleCounting

open MarkerNearStar

theorem semantic_marker_root_choice
    {Point Line Gate : Type*}
    [Fintype Point] [Fintype Line] [DecidableEq Point] [DecidableEq Line]
    (I : Point → Line → Prop) [DecidableRel I]
    (hI : ∀ p q l u, p ≠ q → l ≠ u → ¬ (I p l ∧ I p u ∧ I q l ∧ I q u))
    (S : ℕ → Finset Point) (row : ℕ → Point → Finset Line)
    (bare : ℕ → Finset Line)
    (labelG : Finset Gate) (alive : Gate → Finset Point) (query : Gate → Finset Line)
    (horigin : ∀ r p, p ∈ S r → ∃ g ∈ labelG,
      p ∈ alive g ∧ Pilot5bMeta1020FirstQuery.goodFirst I (query g) p ∧
        query g ⊆ row r p)
    (F : ℕ → Finset Point → Finset Line → Bool)
    (hmono : ∀ r, MonoEval (F r))
    (hrow : ∀ r p u, u ∈ row r p → F r {p} {u} = true)
    (hbare : ∀ r l, l ∈ bare r ↔ F r ∅ {l} = true)
    (a b : ℕ) (l : Line) (hsound : SoundMarker I l (F a) (F b))
    (E : Finset Point)
    (hkeepA : l ∉ bare a → E ⊆ S a)
    (hkeepB : l ∉ bare b → E ⊆ S b) :
    ∃ r ∈ ({a, b} : Finset ℕ),
      ((S r).filter (fun p => ¬ I p l)).card ≤ 4 ∧ E ⊆ S r := by
  classical
  have hnoboth : ¬ (l ∈ bare a ∧ l ∈ bare b) := by
    rintro ⟨ha, hb⟩
    obtain ⟨p, hp, u, hu, hpu⟩ :=
      hsound ∅ {l} (by simp) ((hbare a l).mp ha) ((hbare b l).mp hb)
    exact Finset.notMem_empty p hp
  have star_small (r : ℕ) (hstar : ∀ p ∈ S r, I p l) :
      ((S r).filter (fun p => ¬ I p l)).card ≤ 4 := by
    have hempty : (S r).filter (fun p => ¬ I p l) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact (Finset.mem_filter.mp hp).2 (hstar p (Finset.mem_filter.mp hp).1)
    simp [hempty]
  by_cases ha : l ∈ bare a
  · have hstar : ∀ p ∈ S b, I p l :=
      one_factor_star_of_marker_semantics I l (S b) (row b) labelG alive query
        (fun p hp => horigin b p hp) (F b) (F a) (hmono b) (hmono a)
        (fun X Y hl hb ha' => hsound X Y hl ha' hb)
        ((hbare a l).mp ha) (hrow b)
    exact ⟨b, by simp, star_small b hstar,
      hkeepB (fun hb => hnoboth ⟨ha, hb⟩)⟩
  by_cases hb : l ∈ bare b
  · have hstar : ∀ p ∈ S a, I p l :=
      one_factor_star_of_marker_semantics I l (S a) (row a) labelG alive query
        (fun p hp => horigin a p hp) (F a) (F b) (hmono a) (hmono b)
        hsound ((hbare b l).mp hb) (hrow a)
    exact ⟨a, by simp, star_small a hstar, hkeepA ha⟩
  have hnear := two_factor_near_star_of_marker_semantics I hI l (S a) (S b)
    (row a) (row b) labelG alive query
    (fun p hp => horigin a p hp) (fun p hp => horigin b p hp)
    (F a) (F b) (hmono a) (hmono b) hsound (hrow a) (hrow b)
  rcases hnear with h | h
  · exact ⟨a, by simp, h, hkeepA ha⟩
  · exact ⟨b, by simp, h, hkeepB hb⟩

end Pilot5bMeta1020TripleCounting
namespace Pilot5bMeta1020TripleCounting

open MarkerNearStar

def otherA (i : Fin 3) : Fin 3 := if i = 0 then 1 else 0

def otherB (i : Fin 3) : Fin 3 := if i = 2 then 1 else 2

theorem honest_rows {Point Line : Type*} [DecidableEq Point] [DecidableEq Line]
    {K : ℕ} (I : Point → Line → Prop) (roots : Fin K → Fin 3 → ℕ)
    (F : ℕ → Finset Point → Finset Line → Bool)
    (hmono : ∀ r, MonoEval (F r))
    (hsound : ∀ j X Y, (∀ i : Fin 3, F (roots j i) X Y = true) →
      ∃ p ∈ X, ∃ l ∈ Y, I p l)
    (row : ℕ → Point → Finset Line)
    (hrow : ∀ r p l, l ∈ row r p → F r {p} {l} = true)
    (j : Fin K) (p : Point) (u v w : Line)
    (hu : u ∈ row (roots j 0) p)
    (hv : v ∈ row (roots j 1) p)
    (hw : w ∈ row (roots j 2) p) : I p u ∨ I p v ∨ I p w := by
  have h0 : F (roots j 0) {p} {u, v, w} = true :=
    hmono (roots j 0) {p} {p} {u} {u, v, w} (by simp) (by simp)
      (hrow (roots j 0) p u hu)
  have h1 : F (roots j 1) {p} {u, v, w} = true :=
    hmono (roots j 1) {p} {p} {v} {u, v, w} (by simp) (by simp)
      (hrow (roots j 1) p v hv)
  have h2 : F (roots j 2) {p} {u, v, w} = true :=
    hmono (roots j 2) {p} {p} {w} {u, v, w} (by simp) (by simp)
      (hrow (roots j 2) p w hw)
  have hall : ∀ i : Fin 3, F (roots j i) {p} {u, v, w} = true := by
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  obtain ⟨q, hq, l, hl, hI⟩ := hsound j {p} {u, v, w} hall
  have hqp : q = p := Finset.mem_singleton.mp hq
  subst q
  simp only [Finset.mem_insert, Finset.mem_singleton] at hl
  rcases hl with rfl | rfl | rfl
  · exact Or.inl hI
  · exact Or.inr (Or.inl hI)
  · exact Or.inr (Or.inr hI)

theorem rotated_marker_sound_of_mem
    {Point Line : Type*} [DecidableEq Point] [DecidableEq Line]
    {K : ℕ} (I : Point → Line → Prop) (roots : Fin K → Fin 3 → ℕ)
    (F : ℕ → Finset Point → Finset Line → Bool)
    (hmono : ∀ r, MonoEval (F r))
    (hsound : ∀ j X Y, (∀ i : Fin 3, F (roots j i) X Y = true) →
      ∃ p ∈ X, ∃ l ∈ Y, I p l)
    (bare : ℕ → Finset Line)
    (hbare : ∀ r l, l ∈ bare r ↔ F r ∅ {l} = true)
    (j : Fin K) (i : Fin 3) (l : Line) (hl : l ∈ bare (roots j i)) :
    SoundMarker I l (F (roots j (otherA i))) (F (roots j (otherB i))) := by
  intro X Y hlY ha hb
  have hm : F (roots j i) X Y = true :=
    hmono (roots j i) ∅ X {l} Y (by simp)
      (Finset.singleton_subset_iff.mpr hlY) ((hbare (roots j i) l).mp hl)
  apply hsound j X Y
  intro t
  fin_cases i <;> fin_cases t <;> simp_all [otherA, otherB]

theorem rotated_marker_sound
    {Point Line : Type*} [DecidableEq Point] [DecidableEq Line]
    {K : ℕ} (I : Point → Line → Prop) (roots : Fin K → Fin 3 → ℕ)
    (F : ℕ → Finset Point → Finset Line → Bool)
    (hmono : ∀ r, MonoEval (F r))
    (hsound : ∀ j X Y, (∀ i : Fin 3, F (roots j i) X Y = true) →
      ∃ p ∈ X, ∃ l ∈ Y, I p l)
    (bare : ℕ → Finset Line)
    (hbare : ∀ r l, l ∈ bare r ↔ F r ∅ {l} = true)
    (j : Fin K) (i : Fin 3) (l : Line) (hbl : bare (roots j i) = {l}) :
    SoundMarker I l (F (roots j (otherA i))) (F (roots j (otherB i))) := by
  apply rotated_marker_sound_of_mem I roots F hmono hsound bare hbare j i l
  simp [hbl]

end Pilot5bMeta1020TripleCounting

namespace Pilot5bMeta1020FinalBudget

lemma five_union_bound {α : Type*} [DecidableEq α]
    (E F A H B R : Finset α) (P M O T K : ℕ)
    (hcover : E ⊆ F ∪ A ∪ H ∪ B ∪ R)
    (hF : F.card ≤ 18 * P) (hA : A.card ≤ 12 * M)
    (hH : H.card ≤ 8 * T) (hB : B.card ≤ 2 * T)
    (hR : R.card ≤ 18 * O + 27 * K) (hMO : M + O ≤ T) :
    E.card ≤ 18 * P + 28 * T + 27 * K := by
  have h0 := Finset.card_le_card hcover
  have h1 := Finset.card_union_le F A
  have h2 := Finset.card_union_le (F ∪ A) H
  have h3 := Finset.card_union_le (F ∪ A ∪ H) B
  have h4 := Finset.card_union_le (F ∪ A ∪ H ∪ B) R
  omega

lemma normalized_bound (E P T K g0 g1 g2 J f S : ℕ)
    (hE : E ≤ 18 * P + 28 * T + 27 * K)
    (hP : P ≤ g0 + g1)
    (hT : T + f ≤ 1 + g1 + 3 * g2 + J)
    (hK : K ≤ J + f) (hS : g0 + g1 + g2 ≤ S) :
    E ≤ 84 * S + 55 * J + 28 := by
  omega

lemma final_bound (E P T K g0 g1 g2 J f S N : ℕ)
    (hE : E ≤ 18 * P + 28 * T + 27 * K)
    (hP : P ≤ g0 + g1)
    (hT : T + f ≤ 1 + g1 + 3 * g2 + J)
    (hK : K ≤ J + f) (hS : g0 + g1 + g2 ≤ S) (hJ : 1 ≤ J) :
    E ≤ 100 * (S + J) + 4 * N := by
  have h := normalized_bound E P T K g0 g1 g2 J f S hE hP hT hK hS
  omega

end Pilot5bMeta1020FinalBudget
namespace Pilot5bMeta1020TripleCounting

lemma count_residual_fintype {n m : ℕ} {J : Type*} [Fintype J]
    (T : Fin m → Finset (Fin n))
    (hT : ∀ i j, i ≠ j → (T i ∩ T j).card ≤ 1)
    (S : ℕ → Finset (Fin n)) (G L : Finset ℕ) (kids : ℕ → Finset ℕ)
    (A : ℕ → Finset (Fin n))
    (hkids : ∀ g ∈ G, (kids g).card ≤ 2)
    (hlt : ∀ g ∈ G, ∀ c ∈ kids g, c < g)
    (hunion : ∀ g ∈ G, S g = (kids g).biUnion S)
    (hlabel : ∀ g, g ∉ G → (S g).Nonempty → g ∈ L ∧ S g ⊆ A g)
    (root : J → ℕ) (line : J → Fin m)
    (hnear : ∀ j, (S (root j) \ T (line j)).card ≤ 4)
    (E : Finset (Fin n × Fin m))
    (hcover : ∀ e ∈ E, ∃ j, e.2 = line j ∧ e.1 ∈ S (root j))
    (hexcl : ∀ e ∈ E, ∀ g ∈ L, e.1 ∈ A g → (A g ∩ T e.2).card ≤ 3) :
    E.card ≤ 18 * G.card + 9 * Fintype.card J := by
  classical
  let e := Fintype.equivFin J
  apply Pilot5bMeta1020PrunedNearStar.count_residual T hT S G L kids A
    hkids hlt hunion hlabel (fun j => root (e.symm j)) (fun j => line (e.symm j))
    (fun j => hnear (e.symm j)) E ?_ hexcl
  intro p hp
  obtain ⟨j, hl, hs⟩ := hcover p hp
  exact ⟨e j, by simpa using hl, by simpa using hs⟩

lemma choose_marker_root {n : ℕ}
    (S : ℕ → Finset (Fin n)) (outside : ℕ → ℕ)
    (a b : ℕ) (bareA bareB : Prop) (E : Finset (Fin n))
    (hnoboth : ¬ (bareA ∧ bareB))
    (hnear : outside a ≤ 4 ∨ outside b ≤ 4)
    (hbareA : bareA → outside b ≤ 4)
    (hbareB : bareB → outside a ≤ 4)
    (hkeepA : ¬ bareA → E ⊆ S a)
    (hkeepB : ¬ bareB → E ⊆ S b) :
    ∃ r ∈ ({a, b} : Finset ℕ), outside r ≤ 4 ∧ E ⊆ S r := by
  classical
  by_cases ha : bareA
  · exact ⟨b, by simp, hbareA ha, hkeepB (fun hb => hnoboth ⟨ha, hb⟩)⟩
  by_cases hb : bareB
  · exact ⟨a, by simp, hbareB hb, hkeepA ha⟩
  rcases hnear with h | h
  · exact ⟨a, by simp, h, hkeepA ha⟩
  · exact ⟨b, by simp, h, hkeepB hb⟩

theorem residual_marker_cover {N K : ℕ}
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (labels : Finset ℕ) (alive query bare : ℕ → Finset (Fin N))
    (row : ℕ → Fin N → Finset (Fin N))
    (roots : Fin K → Fin 3 → ℕ)
    (F B : Finset (Fin N × Fin N))
    (hbare : ∀ r p, bare r ⊆ row r p)
    (horigin : ∀ r p l, l ∈ row r p →
      l ∈ bare r ∨ ∃ g ∈ labels,
        p ∈ alive g ∧ l ∈ query g ∧ query g ⊆ row r p)
    (hlarge : ∀ r p l, 2 ≤ (bare r).card →
      (∀ u ∈ bare r, I p u) → l ∈ bare r → (p, l) ∈ B)
    (hsound : ∀ j p, ∀ u ∈ row (roots j 0) p, ∀ v ∈ row (roots j 1) p,
      ∀ w ∈ row (roots j 2) p, I p u ∨ I p v ∨ I p w)
    (p l : Fin N) (hI : I p l)
    (hc : ∃ j, ∀ i, l ∈ row (roots j i) p)
    (hF : (p, l) ∉ F)
    (hsmall : (p, l) ∉ Pilot5bMeta1020FirstQuery.smallPairs I labels alive query F)
    (hown : (p, l) ∉ Pilot5bMeta1020FirstQuery.ownHeavyPairs I labels query)
    (hB : (p, l) ∉ B) :
    ∃ j i, bare (roots j i) = {l} ∧ ∀ t, l ∈ row (roots j t) p := by
  classical
  obtain ⟨j, hj⟩ := hc
  obtain ⟨r, hr, hs | hb | hsingle⟩ :=
    HonestMarkers.triple_honest_accept_cover
      I labels alive query bare row hbare horigin
      (roots j 0) (roots j 1) (roots j 2) p l (hj 0) (hj 1) (hj 2) (hsound j p)
  · obtain ⟨g, hg, hp, hl, hcard | ⟨_, hheavy, T, hT, hcover⟩⟩ := hs
    · exact (hsmall (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hF, hI, g, hg, hp, hl, hcard⟩)).elim
    · apply (hown _).elim
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, hI, g, hg, hl, ?_, hheavy⟩
      refine ⟨T, hT, ?_⟩
      intro u hu
      obtain ⟨q, hq, hqu⟩ := hcover u hu
      exact Finset.mem_biUnion.mpr ⟨q, hq, by
        simpa [Pilot5bMeta1020FirstQuery.pencil] using hqu⟩
  · exact (hB (hlarge r p l hb.1 (fun u hu =>
      (HonestMarkers.mem_pencil I p u).mp (hb.2.1 hu))
      hb.2.2)).elim
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨j, 0, hsingle, hj⟩
    · exact ⟨j, 1, hsingle, hj⟩
    · exact ⟨j, 2, hsingle, hj⟩

theorem residual_count {N K : ℕ}
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hI : ∀ p q l u, p ≠ q → l ≠ u → ¬ (I p l ∧ I p u ∧ I q l ∧ I q u))
    (hT : ∀ l u, l ≠ u →
      ((Finset.univ.filter fun p => I p l) ∩ (Finset.univ.filter fun p => I p u)).card ≤ 1)
    (S : ℕ → Finset (Fin N)) (orG labelG : Finset ℕ) (kids : ℕ → Finset ℕ)
    (alive query bare : ℕ → Finset (Fin N)) (row : ℕ → Fin N → Finset (Fin N))
    (hkids : ∀ g ∈ orG, (kids g).card ≤ 2)
    (hlt : ∀ g ∈ orG, ∀ c ∈ kids g, c < g)
    (hunion : ∀ g ∈ orG, S g = (kids g).biUnion S)
    (hlabel : ∀ g, g ∉ orG → (S g).Nonempty → g ∈ labelG ∧ S g ⊆ alive g)
    (horigin : ∀ r p, p ∈ S r → ∃ g ∈ labelG,
      p ∈ alive g ∧ Pilot5bMeta1020FirstQuery.goodFirst I (query g) p ∧ query g ⊆ row r p)
    (F : ℕ → Finset (Fin N) → Finset (Fin N) → Bool)
    (hmono : ∀ r, MarkerNearStar.MonoEval (F r))
    (hrow : ∀ r p u, u ∈ row r p → F r {p} {u} = true)
    (hbare : ∀ r l, l ∈ bare r ↔ F r ∅ {l} = true)
    (roots : Fin K → Fin 3 → ℕ)
    (hsound : ∀ j X Y, (∀ i, F (roots j i) X Y = true) →
      ∃ p ∈ X, ∃ l ∈ Y, I p l)
    (E : Finset (Fin N × Fin N))
    (hcover : ∀ e ∈ E, ∃ j i, bare (roots j i) = {e.2} ∧
      ∀ t, e.2 ∈ row (roots j t) e.1)
    (hkeep : ∀ e ∈ E, ∀ r, e.2 ∈ row r e.1 → e.2 ∉ bare r → e.1 ∈ S r)
    (hexcl : ∀ e ∈ E, ∀ g ∈ labelG, e.1 ∈ alive g →
      ((alive g).filter fun p => I p e.2).card ≤ 3) :
    E.card ≤ 18 * orG.card + 27 * K := by
  classical
  let jobs := (Finset.univ : Finset ((Fin K × Fin 3) × Fin N)).filter
    (fun x => bare (roots x.1.1 x.1.2) = {x.2})
  let Job := {j // j ∈ jobs}
  let points (j : Job) : Finset (Fin N) := Finset.univ.filter fun p =>
    (p, j.val.2) ∈ E ∧ ∀ t, j.val.2 ∈ row (roots j.val.1.1 t) p
  have hchoice (j : Job) : ∃ r ∈
      ({roots j.val.1.1 (otherA j.val.1.2), roots j.val.1.1 (otherB j.val.1.2)} : Finset ℕ),
      ((S r).filter (fun p => ¬ I p j.val.2)).card ≤ 4 ∧ points j ⊆ S r := by
    have hj : bare (roots j.val.1.1 j.val.1.2) = {j.val.2} :=
      (Finset.mem_filter.mp j.property).2
    apply semantic_marker_root_choice I hI S row bare labelG alive query horigin
      F hmono hrow hbare (roots j.val.1.1 (otherA j.val.1.2))
      (roots j.val.1.1 (otherB j.val.1.2)) j.val.2
      (rotated_marker_sound I roots F hmono hsound bare hbare j.val.1.1 j.val.1.2 j.val.2 hj)
      (points j)
    · intro hb p hp
      obtain ⟨he, hr⟩ := (Finset.mem_filter.mp hp).2
      exact hkeep (p, j.val.2) he _ (hr _) hb
    · intro hb p hp
      obtain ⟨he, hr⟩ := (Finset.mem_filter.mp hp).2
      exact hkeep (p, j.val.2) he _ (hr _) hb
  let selected : Job → ℕ := fun j => Classical.choose (hchoice j)
  have hselected (j : Job) :
      ((S (selected j)).filter (fun p => ¬ I p j.val.2)).card ≤ 4 ∧
        points j ⊆ S (selected j) := (Classical.choose_spec (hchoice j)).2
  have hcount : E.card ≤ 18 * orG.card + 9 * Fintype.card Job := by
    apply count_residual_fintype (fun l => Finset.univ.filter fun p => I p l) hT
      S orG labelG kids alive hkids hlt hunion hlabel selected (fun j => j.val.2) ?_ E ?_ ?_
    · intro j
      have heq : S (selected j) \ (Finset.univ.filter fun p => I p j.val.2) =
          (S (selected j)).filter fun p => ¬ I p j.val.2 := by
        ext p
        simp
      rw [heq]
      exact (hselected j).1
    · intro e he
      obtain ⟨j, i, hs, hr⟩ := hcover e he
      let d : Job := ⟨((j, i), e.2), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩⟩
      refine ⟨d, rfl, (hselected d).2 ?_⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, he, hr⟩
    · intro e he g hg hp
      have heq : alive g ∩ (Finset.univ.filter fun p => I p e.2) =
          (alive g).filter fun p => I p e.2 := by
        ext p
        simp
      rw [heq]
      exact hexcl e he g hg hp
  have hjobs : Fintype.card Job ≤ 3 * K := by
    simpa only [Job, Fintype.card_coe, jobs] using
      HonestMarkers.singleton_markers_card bare roots
  omega

theorem abstract_count {N K : ℕ}
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hI : ∀ p q l u, p ≠ q → l ≠ u → ¬ (I p l ∧ I p u ∧ I q l ∧ I q u))
    (hT : ∀ l u, l ≠ u →
      ((Finset.univ.filter fun p => I p l) ∩ (Finset.univ.filter fun p => I p u)).card ≤ 1)
    (S : ℕ → Finset (Fin N)) (orG labelG : Finset ℕ) (kids : ℕ → Finset ℕ)
    (alive query bare : ℕ → Finset (Fin N)) (row : ℕ → Fin N → Finset (Fin N))
    (hkids : ∀ g ∈ orG, (kids g).card ≤ 2)
    (hlt : ∀ g ∈ orG, ∀ c ∈ kids g, c < g)
    (hunion : ∀ g ∈ orG, S g = (kids g).biUnion S)
    (hlabel : ∀ g, g ∉ orG → (S g).Nonempty → g ∈ labelG ∧ S g ⊆ alive g)
    (hbarow : ∀ r p, bare r ⊆ row r p)
    (hfirst : ∀ r p l, l ∈ row r p → l ∈ bare r ∨
      ∃ g ∈ labelG, p ∈ alive g ∧ l ∈ query g ∧ query g ⊆ row r p)
    (horigin : ∀ r p, p ∈ S r → ∃ g ∈ labelG,
      p ∈ alive g ∧ Pilot5bMeta1020FirstQuery.goodFirst I (query g) p ∧ query g ⊆ row r p)
    (F : ℕ → Finset (Fin N) → Finset (Fin N) → Bool)
    (hmono : ∀ r, MarkerNearStar.MonoEval (F r))
    (hrow : ∀ r p u, u ∈ row r p → F r {p} {u} = true)
    (hbare : ∀ r l, l ∈ bare r ↔ F r ∅ {l} = true)
    (roots : Fin K → Fin 3 → ℕ)
    (hsound : ∀ j X Y, (∀ i, F (roots j i) X Y = true) →
      ∃ p ∈ X, ∃ l ∈ Y, I p l)
    (F3 B : Finset (Fin N × Fin N)) (P T : ℕ)
    (hF3 : F3.card ≤ 18 * P)
    (hheavy : ∀ g ∈ labelG, ∀ l p, p ∈ alive g → I p l →
      4 ≤ ((alive g).filter fun q => I q l).card → (p, l) ∈ F3)
    (hB : B.card ≤ 2 * T)
    (hlarge : ∀ r p l, 2 ≤ (bare r).card →
      (∀ u ∈ bare r, I p u) → l ∈ bare r → (p, l) ∈ B)
    (hown : (Pilot5bMeta1020FirstQuery.ownHeavyPairs I labelG query).card ≤ 8 * T)
    (hcounts : labelG.card + orG.card ≤ T)
    (hretain : ∀ p l, I p l → (p, l) ∉ F3 →
      (p, l) ∉ Pilot5bMeta1020FirstQuery.smallPairs I labelG alive query F3 →
      (p, l) ∉ Pilot5bMeta1020FirstQuery.ownHeavyPairs I labelG query →
      ∀ r, l ∈ row r p → l ∉ bare r → p ∈ S r)
    (E : Finset (Fin N × Fin N))
    (hE : ∀ e ∈ E, I e.1 e.2 ∧ ∃ j, ∀ i, e.2 ∈ row (roots j i) e.1) :
    E.card ≤ 18 * P + 28 * T + 27 * K := by
  classical
  let A := Pilot5bMeta1020FirstQuery.smallPairs I labelG alive query F3
  let H := Pilot5bMeta1020FirstQuery.ownHeavyPairs I labelG query
  let R := E \ (F3 ∪ A ∪ H ∪ B)
  have hA : A.card ≤ 12 * labelG.card :=
    Pilot5bMeta1020FirstQuery.small_first_query_bound I labelG alive query F3 hheavy
  have hr (e : Fin N × Fin N) (he : e ∈ R) :
      e ∈ E ∧ e ∉ F3 ∧ e ∉ A ∧ e ∉ H ∧ e ∉ B := by
    simpa only [R, Finset.mem_sdiff, Finset.mem_union, not_or, and_assoc] using he
  have hR : R.card ≤ 18 * orG.card + 27 * K := by
    apply residual_count I hI hT S orG labelG kids alive query bare row hkids hlt
      hunion hlabel horigin F hmono hrow hbare roots hsound R
    · intro e he
      obtain ⟨heE, heF, heA, heH, heB⟩ := hr e he
      obtain ⟨hei, hec⟩ := hE e heE
      exact residual_marker_cover I labelG alive query bare row roots F3 B
        hbarow hfirst hlarge
        (fun j p u hu v hv w hw => honest_rows I roots F hmono hsound row hrow j p u v w hu hv hw)
        e.1 e.2 hei hec heF heA heH heB
    · intro e he r hrowr hbarer
      obtain ⟨heE, heF, heA, heH, _⟩ := hr e he
      exact hretain e.1 e.2 (hE e heE).1 heF heA heH r hrowr hbarer
    · intro e he g hg hp
      obtain ⟨heE, heF, _, _, _⟩ := hr e he
      by_contra! hc
      exact heF (hheavy g hg e.2 e.1 hp (hE e heE).1 (by omega))
  apply Pilot5bMeta1020FinalBudget.five_union_bound E F3 A H B R P labelG.card orG.card T K
    ?_ hF3 hA hown hB hR hcounts
  intro e he
  by_cases hmem : e ∈ F3 ∪ A ∪ H ∪ B
  · exact Finset.mem_union_left _ hmem
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨he, hmem⟩)

end Pilot5bMeta1020TripleCounting

namespace Pilot5bMeta1020Linear

abbrev Instruction := List ℕ ⊕ (ℕ × ℕ)

def step (labels : ℕ → Bool) (w : List Bool) : Instruction → Bool
  | Sum.inl rs => (rs.map fun r => w.getD r false).any id
  | Sum.inr (a, r) => labels a && w.getD r false

def run (gs : List Instruction) (labels : ℕ → Bool) (y : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [step labels w g]) y

lemma run_cons (g : Instruction) (gs : List Instruction) (labels : ℕ → Bool)
    (y : List Bool) :
    run (g :: gs) labels y = run gs labels (y ++ [step labels y g]) := rfl

lemma run_append (gs hs : List Instruction) (labels : ℕ → Bool) (y : List Bool) :
    run (gs ++ hs) labels y = run hs labels (run gs labels y) := by
  simp [run, List.foldl_append]

lemma run_prefix (gs : List Instruction) (labels : ℕ → Bool) :
    ∀ y : List Bool, ∃ t, run gs labels y = y ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro y; exact ⟨[], by simp [run], rfl⟩
  | cons g gs ih =>
    intro y
    obtain ⟨t, ht, hl⟩ := ih (y ++ [step labels y g])
    refine ⟨step labels y g :: t, ?_, by simp [hl]⟩
    rw [run_cons, ht]
    simp

lemma run_length (gs : List Instruction) (labels : ℕ → Bool) (y : List Bool) :
    (run gs labels y).length = y.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := run_prefix gs labels y
  simp [ht, hl]

lemma run_getD_lt (gs : List Instruction) (labels : ℕ → Bool) (y : List Bool)
    (w : ℕ) (hw : w < y.length) :
    (run gs labels y).getD w false = y.getD w false := by
  obtain ⟨t, ht, _⟩ := run_prefix gs labels y
  rw [ht, List.getD_append _ _ _ _ hw]

lemma run_getD_ge (gs : List Instruction) (labels : ℕ → Bool) (y : List Bool)
    (w : ℕ) (hw : y.length + gs.length ≤ w) :
    (run gs labels y).getD w false = false := by
  apply List.getD_eq_default
  simpa only [run_length] using hw

lemma run_snoc (gs : List Instruction) (g : Instruction) (labels : ℕ → Bool)
    (y : List Bool) :
    run (gs ++ [g]) labels y = run gs labels y ++ [step labels (run gs labels y) g] := by
  simp [run, List.foldl_append]

lemma snoc_read_old (gs : List Instruction) (g : Instruction) (labels : ℕ → Bool)
    (y : List Bool) (w : ℕ) (hw : w < y.length + gs.length) :
    (run (gs ++ [g]) labels y).getD w false = (run gs labels y).getD w false := by
  rw [run_snoc, List.getD_append _ _ _ _ (by simpa only [run_length] using hw)]

lemma snoc_read_new (gs : List Instruction) (g : Instruction) (labels : ℕ → Bool)
    (y : List Bool) :
    (run (gs ++ [g]) labels y).getD (y.length + gs.length) false =
      step labels (run gs labels y) g := by
  rw [run_snoc, List.getD_append_right _ _ _ _ (by simp [run_length])]
  simp [run_length]

def queryStep {n : ℕ} (labels : ℕ → Bool) (w : List (Finset (Fin n))) :
    Instruction → Finset (Fin n)
  | Sum.inl rs => rs.toFinset.biUnion fun r => w.getD r ∅
  | Sum.inr (a, r) => if labels a then w.getD r ∅ else ∅

def queryRun {n : ℕ} (gs : List Instruction) (labels : ℕ → Bool)
    (w : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun w g => w ++ [queryStep labels w g]) w

noncomputable def hits {n : ℕ} (y : Fin n → Bool) (S : Finset (Fin n)) : Bool :=
  S.toList.any y

lemma hits_true {n : ℕ} (y : Fin n → Bool) (S : Finset (Fin n)) :
    hits y S = true ↔ ∃ l ∈ S, y l = true := by
  simp [hits]

@[local simp] lemma hits_empty {n : ℕ} (y : Fin n → Bool) : hits y ∅ = false := by
  simp [hits]

@[local simp] lemma hits_singleton {n : ℕ} (y : Fin n → Bool) (l : Fin n) :
    hits y {l} = y l := by
  apply Bool.eq_iff_iff.mpr
  simp [hits_true]

lemma map_hits_getD {n : ℕ} (y : Fin n → Bool)
    (w : List (Finset (Fin n))) (r : ℕ) :
    (w.map (hits y)).getD r false = hits y (w.getD r ∅) := by
  induction w generalizing r with
  | nil => simp
  | cons S w ih =>
    cases r with
    | zero => rfl
    | succ r => exact ih r

lemma hits_queryStep {n : ℕ} (labels : ℕ → Bool) (y : Fin n → Bool)
    (w : List (Finset (Fin n))) (g : Instruction) :
    hits y (queryStep labels w g) = step labels (w.map (hits y)) g := by
  apply Bool.eq_iff_iff.mpr
  cases g with
  | inl rs =>
    simp only [queryStep, step, hits_true, Finset.mem_biUnion,
      List.mem_toFinset, List.any_eq_true, List.mem_map, id_eq]
    constructor
    · rintro ⟨l, ⟨r, hr, hl⟩, hy⟩
      refine ⟨(w.map (hits y)).getD r false, ⟨r, hr, rfl⟩, ?_⟩
      rw [map_hits_getD]
      exact (hits_true y _).mpr ⟨l, hl, hy⟩
    · rintro ⟨b, ⟨r, hr, rfl⟩, hb⟩
      rw [map_hits_getD] at hb
      obtain ⟨l, hl, hy⟩ := (hits_true y _).mp hb
      exact ⟨l, ⟨r, hr, hl⟩, hy⟩
  | inr ar =>
    rcases ar with ⟨a, r⟩
    cases ha : labels a with
    | false => simp [queryStep, step, ha]
    | true =>
      change hits y (if labels a then w.getD r ∅ else ∅) = true ↔
        (labels a && (w.map (hits y)).getD r false) = true
      rw [ha]
      simp only [Bool.true_and, ite_true]
      rw [map_hits_getD]

lemma run_queries {n : ℕ} (gs : List Instruction) (labels : ℕ → Bool)
    (y : Fin n → Bool) (w : List (Finset (Fin n))) :
    run gs labels (w.map (hits y)) = (queryRun gs labels w).map (hits y) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change run gs labels (w.map (hits y) ++ [step labels (w.map (hits y)) g]) =
      (queryRun gs labels (w ++ [queryStep labels w g])).map (hits y)
    rw [← hits_queryStep]
    simpa only [List.map_append, List.map_singleton] using ih (w ++ [queryStep labels w g])

def queries {n : ℕ} (gs : List Instruction) (labels : ℕ → Bool) :
    List (Finset (Fin n)) :=
  queryRun gs labels (List.ofFn fun l : Fin n => {l})

lemma run_input_queries {n : ℕ} (gs : List Instruction) (labels : ℕ → Bool)
    (y : Fin n → Bool) :
    run gs labels (List.ofFn y) = (queries gs labels).map (hits y) := by
  have h := run_queries gs labels y (List.ofFn fun l : Fin n => {l})
  simpa only [queries, List.map_ofFn, Function.comp_def, hits_singleton] using h

lemma wire_query {n : ℕ} (gs : List Instruction) (labels : ℕ → Bool)
    (y : Fin n → Bool) (w : ℕ) :
    (run gs labels (List.ofFn y)).getD w false =
      hits y ((queries gs labels).getD w ∅) := by
  rw [run_input_queries, map_hits_getD]

lemma wire_true {n : ℕ} (gs : List Instruction) (labels : ℕ → Bool)
    (y : Fin n → Bool) (w : ℕ) :
    (run gs labels (List.ofFn y)).getD w false = true ↔
      ∃ l ∈ (queries gs labels).getD w ∅, y l = true := by
  rw [wire_query, hits_true]

lemma wire_zero {n : ℕ} (gs : List Instruction) (labels : ℕ → Bool) (w : ℕ) :
    (run gs labels (List.ofFn fun _ : Fin n => false)).getD w false = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨l, _, hl⟩ := (wire_true (n := n) gs labels (fun _ => false) w).mp h
  contradiction

lemma wire_singleton {n : ℕ} (gs : List Instruction) (labels : ℕ → Bool)
    (l : Fin n) (w : ℕ) :
    (run gs labels (List.ofFn fun t => decide (t = l))).getD w false = true ↔
      l ∈ (queries gs labels).getD w ∅ := by
  rw [wire_true]
  simp

end Pilot5bMeta1020Linear

namespace Pilot5bMeta1020Linear

lemma cleaning_getD_mono {u v : List Bool}
    (h : List.Forall₂ (fun a b => a = true → b = true) u v) (r : ℕ) :
    u.getD r false = true → v.getD r false = true := by
  induction h generalizing r with
  | nil => simp
  | cons hab huv ih =>
    cases r with
    | zero => exact hab
    | succ r => exact ih r

lemma cleaning_step_mono (L L' : ℕ → Bool)
    (hL : ∀ a, L a = true → L' a = true)
    {u v : List Bool}
    (huv : List.Forall₂ (fun a b => a = true → b = true) u v)
    (g : Instruction) : step L u g = true → step L' v g = true := by
  cases g with
  | inl rs =>
    simp only [step, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨b, ⟨r, hr, rfl⟩, hb⟩
    exact ⟨_, ⟨r, hr, rfl⟩, cleaning_getD_mono huv r hb⟩
  | inr ar =>
    rcases ar with ⟨a, r⟩
    simp only [step, Bool.and_eq_true]
    exact fun h => ⟨hL a h.1, cleaning_getD_mono huv r h.2⟩

lemma cleaning_run_rel (gs : List Instruction) (L L' : ℕ → Bool)
    (hL : ∀ a, L a = true → L' a = true)
    {u v : List Bool}
    (huv : List.Forall₂ (fun a b => a = true → b = true) u v) :
    List.Forall₂ (fun a b => a = true → b = true)
      (run gs L u) (run gs L' v) := by
  induction gs generalizing u v with
  | nil => exact huv
  | cons g gs ih =>
    change List.Forall₂ (fun a b => a = true → b = true)
      (run gs L (u ++ [step L u g])) (run gs L' (v ++ [step L' v g]))
    exact ih (List.rel_append huv (.cons (cleaning_step_mono L L' hL huv g) .nil))

lemma cleaning_run_mono {n : ℕ} (gs : List Instruction) (L L' : ℕ → Bool)
    (hL : ∀ a, L a = true → L' a = true)
    (y y' : Fin n → Bool) (hy : ∀ l, y l = true → y' l = true) (r : ℕ) :
    (run gs L (List.ofFn y)).getD r false = true →
      (run gs L' (List.ofFn y')).getD r false = true := by
  apply cleaning_getD_mono (cleaning_run_rel gs L L' hL ?_) r
  apply List.forall₂_iff_get.mpr
  refine ⟨by simp, ?_⟩
  intro i hi hi'
  simpa using hy ⟨i, by simpa using hi⟩

noncomputable def maxNonneighbors {n : ℕ}
    (I : Fin n → Fin n → Prop) (S : Finset (Fin n)) (p : Fin n) : Bool := by
  classical
  exact decide (∀ l ∈ S, ¬ I p l)

def labelDead3 {n : ℕ} (I : Fin n → Fin n → Prop)
    (L : ℕ → (Fin n → Bool) → Bool) (a : ℕ) : Prop :=
  ∃ S : Finset (Fin n), S.card ≤ 3 ∧ L a (maxNonneighbors I S) = false

noncomputable def cleanedLabels {n : ℕ} (I : Fin n → Fin n → Prop)
    (L : ℕ → (Fin n → Bool) → Bool) (a : ℕ) (x : Fin n → Bool) : Bool := by
  classical
  exact if labelDead3 I L a then L a x else true

def LabelMonotone {n : ℕ} (L : ℕ → (Fin n → Bool) → Bool) : Prop :=
  ∀ a x x', (∀ p, x p = true → x' p = true) → L a x = true → L a x' = true

def LinearTripleSound {n : ℕ} (I : Fin n → Fin n → Prop)
    (gs : List Instruction) (L : ℕ → (Fin n → Bool) → Bool)
    (r0 r1 r2 : ℕ) : Prop :=
  ∀ x y : Fin n → Bool,
    (run gs (fun a => L a x) (List.ofFn y)).getD r0 false = true →
    (run gs (fun a => L a x) (List.ofFn y)).getD r1 false = true →
    (run gs (fun a => L a x) (List.ofFn y)).getD r2 false = true →
    ∃ p l, I p l ∧ x p = true ∧ y l = true

lemma cleanedLabels_mono {n : ℕ} (I : Fin n → Fin n → Prop)
    (L : ℕ → (Fin n → Bool) → Bool) (hL : LabelMonotone L) :
    LabelMonotone (cleanedLabels I L) := by
  classical
  intro a x x' hxx'
  by_cases ha : labelDead3 I L a
  · simpa [cleanedLabels, ha] using hL a x x' hxx'
  · simp [cleanedLabels, ha]

lemma cleanedLabels_ge {n : ℕ} (I : Fin n → Fin n → Prop)
    (L : ℕ → (Fin n → Bool) → Bool) (a : ℕ) (x : Fin n → Bool) :
    L a x = true → cleanedLabels I L a x = true := by
  classical
  by_cases ha : labelDead3 I L a <;> simp [cleanedLabels, ha]

lemma cleaned_wire_preserved {n : ℕ} (I : Fin n → Fin n → Prop)
    (gs : List Instruction) (L : ℕ → (Fin n → Bool) → Bool)
    (x y : Fin n → Bool) (r : ℕ) :
    (run gs (fun a => L a x) (List.ofFn y)).getD r false = true →
      (run gs (fun a => cleanedLabels I L a x) (List.ofFn y)).getD r false = true :=
  cleaning_run_mono gs _ _ (fun a => cleanedLabels_ge I L a x) y y (fun _ => id) r

lemma cleanedLabels_at_small_dead_input {n : ℕ} (I : Fin n → Fin n → Prop)
    (L : ℕ → (Fin n → Bool) → Bool) (S : Finset (Fin n)) (hS : S.card ≤ 3)
    (a : ℕ) :
    cleanedLabels I L a (maxNonneighbors I S) = L a (maxNonneighbors I S) := by
  classical
  by_cases ha : labelDead3 I L a
  · simp [cleanedLabels, ha]
  · have ht : L a (maxNonneighbors I S) = true :=
      Bool.eq_true_of_not_eq_false (fun hf => ha ⟨S, hS, hf⟩)
    simp [cleanedLabels, ha, ht]

lemma retained_label_false_empty {n : ℕ} (I : Fin n → Fin n → Prop)
    (L : ℕ → (Fin n → Bool) → Bool) (hL : LabelMonotone L)
    (a : ℕ) (ha : labelDead3 I L a) : L a (fun _ => false) = false := by
  obtain ⟨S, _, hfalse⟩ := ha
  apply Bool.eq_false_of_not_eq_true
  intro ht
  have hm := hL a (fun _ => false) (maxNonneighbors I S) (by simp) ht
  simp [hfalse] at hm

theorem cleaned_triple_sound {n : ℕ} (I : Fin n → Fin n → Prop)
    (gs : List Instruction) (L : ℕ → (Fin n → Bool) → Bool)
    (hL : LabelMonotone L) (r0 r1 r2 : ℕ)
    (hsound : LinearTripleSound I gs L r0 r1 r2) :
    LinearTripleSound I gs (cleanedLabels I L) r0 r1 r2 := by
  classical
  intro x y h0 h1 h2
  by_contra hbad
  obtain ⟨l0, hm0, hy0⟩ := (wire_true gs (fun a => cleanedLabels I L a x) y r0).mp h0
  obtain ⟨l1, hm1, hy1⟩ := (wire_true gs (fun a => cleanedLabels I L a x) y r1).mp h1
  obtain ⟨l2, hm2, hy2⟩ := (wire_true gs (fun a => cleanedLabels I L a x) y r2).mp h2
  let S : Finset (Fin n) := {l0, l1, l2}
  have hS : S.card ≤ 3 := by
    calc
      S.card ≤ ({l1, l2} : Finset (Fin n)).card + 1 := Finset.card_insert_le _ _
      _ ≤ ({l2} : Finset (Fin n)).card + 1 + 1 :=
        Nat.add_le_add_right (Finset.card_insert_le _ _) 1
      _ = 3 := by simp
  let ys : Fin n → Bool := fun l => decide (l ∈ S)
  let xs := maxNonneighbors I S
  have hSY : ∀ l ∈ S, y l = true := by
    intro l hl
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl
    · exact hy0
    · exact hy1
    · exact hy2
  have hx : ∀ p, x p = true → xs p = true := by
    intro p hp
    simp only [xs, maxNonneighbors, decide_eq_true_eq]
    intro l hl hI
    exact hbad ⟨p, l, hI, hp, hSY l hl⟩
  have ht0 : (run gs (fun a => cleanedLabels I L a x) (List.ofFn ys)).getD r0 false = true := by
    apply (wire_true gs _ ys r0).mpr
    exact ⟨l0, hm0, by simp [ys, S]⟩
  have ht1 : (run gs (fun a => cleanedLabels I L a x) (List.ofFn ys)).getD r1 false = true := by
    apply (wire_true gs _ ys r1).mpr
    exact ⟨l1, hm1, by simp [ys, S]⟩
  have ht2 : (run gs (fun a => cleanedLabels I L a x) (List.ofFn ys)).getD r2 false = true := by
    apply (wire_true gs _ ys r2).mpr
    exact ⟨l2, hm2, by simp [ys, S]⟩
  have label_eq : (fun a => cleanedLabels I L a xs) = (fun a => L a xs) := by
    funext a
    exact cleanedLabels_at_small_dead_input I L S hS a
  have lift (r : ℕ)
      (ht : (run gs (fun a => cleanedLabels I L a x) (List.ofFn ys)).getD r false = true) :
      (run gs (fun a => L a xs) (List.ofFn ys)).getD r false = true := by
    have hm := cleaning_run_mono gs _ _
      (fun a => cleanedLabels_mono I L hL a x xs hx) ys ys (fun _ => id) r ht
    simpa only [label_eq] using hm
  obtain ⟨p, l, hI, hp, hl⟩ := hsound xs ys (lift r0 ht0) (lift r1 ht1) (lift r2 ht2)
  have hpn : ∀ l ∈ S, ¬ I p l := of_decide_eq_true hp
  have hls : l ∈ S := of_decide_eq_true hl
  exact hpn l hls hI

end Pilot5bMeta1020Linear

namespace Pilot5bMeta1020LinearDAG

open Pilot5bMeta1020Linear
open Pilot5bMeta1020FirstQuery

def query {N : ℕ} (gs : List Instruction) (labels : ℕ → Bool) (w : ℕ) : Finset (Fin N) :=
  (queries gs labels).getD w ∅

def gateAt (gs : List Instruction) (N w : ℕ) : Instruction :=
  gs.getD (w - N) (Sum.inl [])

def queryOp {N : ℕ} (labels : ℕ → Bool) (read : ℕ → Finset (Fin N)) :
    Instruction → Finset (Fin N)
  | .inl rs => rs.toFinset.biUnion read
  | .inr (a, r) => if labels a then read r else ∅

lemma queryRun_cons {N : ℕ} (g : Instruction) (gs : List Instruction)
    (labels : ℕ → Bool) (w : List (Finset (Fin N))) :
    queryRun (g :: gs) labels w = queryRun gs labels (w ++ [queryStep labels w g]) := rfl

lemma queryRun_length {N : ℕ} (gs : List Instruction) (labels : ℕ → Bool)
    (w : List (Finset (Fin N))) : (queryRun gs labels w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [queryRun]
  | cons g gs ih => rw [queryRun_cons, ih]; simp; omega

lemma queryRun_getD {N : ℕ} (gs : List Instruction) (labels : ℕ → Bool)
    (w : List (Finset (Fin N))) (r : ℕ) (hr : r < w.length) :
    (queryRun gs labels w).getD r ∅ = w.getD r ∅ := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [queryRun_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hr]

lemma queryRun_split {N : ℕ} (gs : List Instruction) (labels : ℕ → Bool)
    (w : List (Finset (Fin N))) (j : ℕ) :
    queryRun gs labels w = queryRun (gs.drop j) labels (queryRun (gs.take j) labels w) := by
  simpa only [queryRun, List.foldl_append] using congrArg
    (fun hs : List Instruction => queryRun hs labels w) (List.take_append_drop j gs).symm

lemma query_input {N : ℕ} (gs : List Instruction) (labels : ℕ → Bool) (p : Fin N) :
    query gs labels p = {p} := by
  unfold query queries
  rw [queryRun_getD _ _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  simp

lemma query_missing {N : ℕ} (gs : List Instruction) (labels : ℕ → Bool) (w : ℕ)
    (hw : N + gs.length ≤ w) : query (N := N) gs labels w = ∅ := by
  unfold query queries
  exact List.getD_eq_default _ _ (by simpa [queryRun_length] using hw)

lemma query_gate {N : ℕ} (gs : List Instruction) (labels : ℕ → Bool) (w : ℕ)
    (hn : N ≤ w) (hw : w < N + gs.length) :
    query gs labels w = queryOp labels
      (fun r => if r < w then query (N := N) gs labels r else ∅) (gateAt gs N w) := by
  let j := w - N
  have hj : j < gs.length := by dsimp [j]; omega
  let g := gs[j]
  let initial : List (Finset (Fin N)) := List.ofFn fun l : Fin N => {l}
  let earlier := queryRun (gs.take j) labels initial
  have plen : earlier.length = w := by
    simp [earlier, initial, queryRun_length, Nat.min_eq_left hj.le, j]
    omega
  have split : queryRun gs labels initial =
      queryRun (g :: gs.drop (j + 1)) labels earlier := by
    rw [queryRun_split gs labels initial j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r ∅ =
      if r < w then query (N := N) gs labels r else ∅ := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r ∅ = (queryRun gs labels initial).getD r ∅
      rw [split]
      exact (queryRun_getD _ labels earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  have hg : gateAt gs N w = g := List.getD_eq_getElem _ _ hj
  rw [hg]
  change (queryRun gs labels initial).getD w ∅ = _
  rw [split, queryRun_cons, queryRun_getD _ _ _ _ (by simp [plen]),
    List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero]
  cases g <;> simp only [queryStep, queryOp, read]

lemma gateAt_first (gs : List Instruction) (hhead : gs.head? = some (Sum.inl [])) (N : ℕ) :
    gateAt gs N N = Sum.inl [] := by
  cases gs with
  | nil => simp at hhead
  | cons g gs =>
    have hg : g = Sum.inl [] := by simpa using hhead
    simp [gateAt, hg]

lemma head_nonempty (gs : List Instruction) (hhead : gs.head? = some (Sum.inl [])) :
    0 < gs.length := by
  cases gs <;> simp_all

lemma query_false_wire {N : ℕ} (gs : List Instruction)
    (hhead : gs.head? = some (Sum.inl [])) (labels : ℕ → Bool) :
    query (N := N) gs labels N = ∅ := by
  rw [query_gate gs labels N (by omega) (by have := head_nonempty gs hhead; omega),
    gateAt_first gs hhead N]
  simp [queryOp]

def IsOr (α : ℕ → Bool) : Instruction → Prop
  | .inl _ => True
  | .inr (a, _) => α a = true

def IsLabel (α : ℕ → Bool) : Instruction → Prop
  | .inl _ => False
  | .inr (a, _) => α a = false

noncomputable def orG (gs : List Instruction) (N : ℕ) (α : ℕ → Bool) : Finset ℕ := by
  classical
  exact (Finset.Ico N (N + gs.length)).filter fun w => IsOr α (gateAt gs N w)

noncomputable def labelG (gs : List Instruction) (N : ℕ) (α : ℕ → Bool) : Finset ℕ := by
  classical
  exact (Finset.Ico N (N + gs.length)).filter fun w => IsLabel α (gateAt gs N w)

def clamp (N w r : ℕ) : ℕ := if r < w then r else N

def child (gs : List Instruction) (N w : ℕ) : ℕ :=
  match gateAt gs N w with
  | .inl _ => N
  | .inr (_, r) => clamp N w r

def labelID (gs : List Instruction) (N w : ℕ) : ℕ :=
  match gateAt gs N w with
  | .inl _ => 0
  | .inr (a, _) => a

def kids (gs : List Instruction) (N w : ℕ) : Finset ℕ :=
  match gateAt gs N w with
  | .inl rs => rs.toFinset.filter (· < w)
  | .inr (_, r) => {clamp N w r}

lemma gateAt_mem (gs : List Instruction) (N w : ℕ)
    (hn : N ≤ w) (hw : w < N + gs.length) : gateAt gs N w ∈ gs := by
  have hj : w - N < gs.length := by omega
  rw [gateAt, List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem _

lemma label_after_first (gs : List Instruction)
    (hhead : gs.head? = some (Sum.inl [])) (N w a r : ℕ)
    (hn : N ≤ w) (hgate : gateAt gs N w = Sum.inr (a, r)) : N < w := by
  by_contra h
  have heq : w = N := by omega
  rw [heq, gateAt_first gs hhead N] at hgate
  contradiction

lemma clamp_lower (N w r : ℕ) (h : N < w) : clamp N w r < w := by
  unfold clamp
  split_ifs <;> omega

lemma query_clamp {N : ℕ} (gs : List Instruction)
    (hhead : gs.head? = some (Sum.inl [])) (labels : ℕ → Bool) (w r : ℕ) :
    query (N := N) gs labels (clamp N w r) =
      if r < w then query gs labels r else ∅ := by
  unfold clamp
  split_ifs
  · rfl
  · exact query_false_wire gs hhead labels

lemma or_lower (gs : List Instruction) (hhead : gs.head? = some (Sum.inl []))
    (N : ℕ) (α : ℕ → Bool) :
    ∀ w ∈ orG gs N α, ∀ c ∈ kids gs N w, c < w := by
  classical
  intro w hw c hc
  obtain ⟨hwI, _⟩ := Finset.mem_filter.mp hw
  have hwn := (Finset.mem_Ico.mp hwI).1
  cases hgate : gateAt gs N w with
  | inl rs =>
    have hc' : c ∈ rs.toFinset.filter (· < w) := by simpa only [kids, hgate] using hc
    exact (Finset.mem_filter.mp hc').2
  | inr ar =>
    rcases ar with ⟨a, r⟩
    have hcw : c = clamp N w r := by simpa only [kids, hgate, Finset.mem_singleton] using hc
    rw [hcw]
    exact clamp_lower N w r (label_after_first gs hhead N w a r hwn hgate)

lemma label_lower (gs : List Instruction) (hhead : gs.head? = some (Sum.inl []))
    (N : ℕ) (α : ℕ → Bool) :
    ∀ w ∈ labelG gs N α, child gs N w < w := by
  classical
  intro w hw
  obtain ⟨hwI, hkind⟩ := Finset.mem_filter.mp hw
  have hwn := (Finset.mem_Ico.mp hwI).1
  cases hgate : gateAt gs N w with
  | inl rs => simp [IsLabel, hgate] at hkind
  | inr ar =>
    rcases ar with ⟨a, r⟩
    simp only [child, hgate]
    exact clamp_lower N w r (label_after_first gs hhead N w a r hwn hgate)

lemma gates_disjoint (gs : List Instruction) (N : ℕ) (α : ℕ → Bool) :
    Disjoint (orG gs N α) (labelG gs N α) := by
  classical
  apply Finset.disjoint_left.mpr
  intro w ho hl
  have ho' := (Finset.mem_filter.mp ho).2
  have hl' := (Finset.mem_filter.mp hl).2
  cases hgate : gateAt gs N w with
  | inl rs => simp [IsLabel, hgate] at hl'
  | inr ar =>
    rcases ar with ⟨a, r⟩
    simp only [IsOr, hgate] at ho'
    simp only [IsLabel, hgate] at hl'
    rw [ho'] at hl'
    contradiction

lemma gate_partition (gs : List Instruction) (N : ℕ) (α : ℕ → Bool) (w : ℕ)
    (hw : w ∈ Finset.Ico N (N + gs.length)) :
    w ∈ orG gs N α ∨ w ∈ labelG gs N α := by
  classical
  cases hgate : gateAt gs N w with
  | inl rs => exact Or.inl (Finset.mem_filter.mpr ⟨hw, by simp [IsOr, hgate]⟩)
  | inr ar =>
    rcases ar with ⟨a, r⟩
    cases ha : α a
    · exact Or.inr (Finset.mem_filter.mpr ⟨hw, by simp [IsLabel, hgate, ha]⟩)
    · exact Or.inl (Finset.mem_filter.mpr ⟨hw, by simp [IsOr, hgate, ha]⟩)

lemma gate_counts (gs : List Instruction) (N : ℕ) (α : ℕ → Bool) :
    (orG gs N α).card + (labelG gs N α).card = gs.length := by
  classical
  have heq : orG gs N α ∪ labelG gs N α = Finset.Ico N (N + gs.length) := by
    ext w
    constructor
    · intro hw
      rcases Finset.mem_union.mp hw with hw | hw <;> exact (Finset.mem_filter.mp hw).1
    · intro hw
      exact Finset.mem_union.mpr (gate_partition gs N α w hw)
  rw [← Finset.card_union_of_disjoint (gates_disjoint gs N α), heq]
  simp

lemma kids_card (gs : List Instruction) (N : ℕ) (α : ℕ → Bool)
    (hfanin : ∀ rs, Sum.inl rs ∈ gs → rs.length ≤ 2) :
    ∀ w ∈ orG gs N α, (kids gs N w).card ≤ 2 := by
  classical
  intro w hw
  obtain ⟨hwI, _⟩ := Finset.mem_filter.mp hw
  obtain ⟨hwn, hwb⟩ := Finset.mem_Ico.mp hwI
  cases hgate : gateAt gs N w with
  | inl rs =>
    have hlen := hfanin rs (by simpa only [hgate] using gateAt_mem gs N w hwn hwb)
    simp only [kids, hgate]
    exact (Finset.card_filter_le _ _).trans ((List.toFinset_card_le _).trans hlen)
  | inr ar => simp [kids, hgate]

lemma query_or_eq {N : ℕ} (gs : List Instruction)
    (hhead : gs.head? = some (Sum.inl [])) (α β : ℕ → Bool)
    (hαβ : ∀ a, α a = true → β a = true) (w : ℕ) (hw : w ∈ orG gs N α) :
    query gs β w = (kids gs N w).biUnion (query (N := N) gs β) := by
  classical
  obtain ⟨hwI, hkind⟩ := Finset.mem_filter.mp hw
  obtain ⟨hwn, hwb⟩ := Finset.mem_Ico.mp hwI
  rw [query_gate gs β w hwn hwb]
  cases hgate : gateAt gs N w with
  | inl rs =>
    simp only [queryOp, kids, hgate]
    ext l
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · rintro ⟨r, hr, hl⟩
      by_cases hrw : r < w
      · exact ⟨r, ⟨hr, hrw⟩, by simpa only [ite_eq_left hrw] using hl⟩
      · simp [hrw] at hl
    · rintro ⟨r, ⟨hr, hrw⟩, hl⟩
      exact ⟨r, hr, by simpa only [ite_eq_left hrw] using hl⟩
  | inr ar =>
    rcases ar with ⟨a, r⟩
    have ha : α a = true := by simpa only [IsOr, hgate] using hkind
    have hb := hαβ a ha
    simp only [queryOp, hb, ite_true, kids, hgate, Finset.singleton_biUnion]
    exact (query_clamp gs hhead β w r).symm

lemma query_label_eq {N : ℕ} (gs : List Instruction)
    (hhead : gs.head? = some (Sum.inl [])) (α β : ℕ → Bool)
    (w : ℕ) (hw : w ∈ labelG gs N α) :
    query (N := N) gs β w =
      if β (labelID gs N w) then query gs β (child gs N w) else ∅ := by
  classical
  obtain ⟨hwI, hkind⟩ := Finset.mem_filter.mp hw
  obtain ⟨hwn, hwb⟩ := Finset.mem_Ico.mp hwI
  rw [query_gate gs β w hwn hwb]
  cases hgate : gateAt gs N w with
  | inl rs => simp [IsLabel, hgate] at hkind
  | inr ar =>
    rcases ar with ⟨a, r⟩
    simp only [queryOp, labelID, child, hgate]
    rw [query_clamp gs hhead β w r]

lemma query_other_eq {N : ℕ} (gs : List Instruction) (α β γ : ℕ → Bool)
    (w : ℕ) (hor : w ∉ orG gs N α) (hlab : w ∉ labelG gs N α) :
    query (N := N) gs β w = query gs γ w := by
  by_cases hwn : w < N
  · exact (query_input gs β ⟨w, hwn⟩).trans (query_input gs γ ⟨w, hwn⟩).symm
  · have hwb : N + gs.length ≤ w := by
      by_contra h
      rcases gate_partition gs N α w (Finset.mem_Ico.mpr ⟨by omega, by omega⟩) with ho | hl
      · exact hor ho
      · exact hlab hl
    rw [query_missing gs β w hwb, query_missing gs γ w hwb]

lemma query_mono {N : ℕ} (gs : List Instruction) (α β : ℕ → Bool)
    (h : ∀ a, α a = true → β a = true) (w : ℕ) :
    query (N := N) gs α w ⊆ query gs β w := by
  intro l hl
  have hv := (wire_singleton gs α l w).mpr hl
  have hm := cleaning_run_mono gs α β h (fun t => decide (t = l))
    (fun t => decide (t = l)) (fun _ => id) w hv
  exact (wire_singleton gs β l w).mp hm

def bare {N : ℕ} (gs : List Instruction) (α : ℕ → Bool) : ℕ → Finset (Fin N) :=
  query gs α

def row {N : ℕ} (gs : List Instruction) (L : ℕ → (Fin N → Bool) → Bool)
    (w : ℕ) (p : Fin N) : Finset (Fin N) :=
  query gs (fun a => L a (fun q => decide (q = p))) w

def alive {N : ℕ} (gs : List Instruction) (L : ℕ → (Fin N → Bool) → Bool)
    (w : ℕ) : Finset (Fin N) :=
  Finset.univ.filter fun p => L (labelID gs N w) (fun q => decide (q = p)) = true

lemma bare_or_law {N : ℕ} (gs : List Instruction)
    (hhead : gs.head? = some (Sum.inl [])) (α : ℕ → Bool)
    (w : ℕ) (hw : w ∈ orG gs N α) (l : Fin N) :
    l ∈ bare gs α w ↔ ∃ c ∈ kids gs N w, l ∈ bare gs α c := by
  change l ∈ query gs α w ↔ _
  rw [query_or_eq gs hhead α α (fun _ => id) w hw]
  exact Finset.mem_biUnion

lemma row_or_law {N : ℕ} (gs : List Instruction)
    (hhead : gs.head? = some (Sum.inl [])) (α : ℕ → Bool)
    (L : ℕ → (Fin N → Bool) → Bool)
    (hα : ∀ a x, α a = true → L a x = true)
    (w : ℕ) (hw : w ∈ orG gs N α) (p l : Fin N) :
    l ∈ row gs L w p ↔ ∃ c ∈ kids gs N w, l ∈ row gs L c p := by
  change l ∈ query gs (fun a => L a (fun q => decide (q = p))) w ↔ _
  rw [query_or_eq gs hhead α _ (fun a => hα a _) w hw]
  exact Finset.mem_biUnion

lemma row_label_law {N : ℕ} (gs : List Instruction)
    (hhead : gs.head? = some (Sum.inl [])) (α : ℕ → Bool)
    (L : ℕ → (Fin N → Bool) → Bool)
    (w : ℕ) (hw : w ∈ labelG gs N α) (p l : Fin N) :
    l ∈ row gs L w p ↔ p ∈ alive gs L w ∧ l ∈ row gs L (child gs N w) p := by
  change l ∈ query gs (fun a => L a (fun q => decide (q = p))) w ↔ _
  rw [query_label_eq gs hhead α _ w hw]
  by_cases h : L (labelID gs N w) (fun q => decide (q = p)) = true
  · simp [h, alive, row]
  · simp [h, alive, row]

lemma row_other_law {N : ℕ} (gs : List Instruction) (α : ℕ → Bool)
    (L : ℕ → (Fin N → Bool) → Bool) (w : ℕ)
    (hor : w ∉ orG gs N α) (hlab : w ∉ labelG gs N α) (p : Fin N) :
    row gs L w p = bare gs α w :=
  query_other_eq gs α _ α w hor hlab

lemma bare_sub_row {N : ℕ} (gs : List Instruction) (α : ℕ → Bool)
    (L : ℕ → (Fin N → Bool) → Bool)
    (hα : ∀ a x, α a = true → L a x = true) (w : ℕ) (p : Fin N) :
    bare gs α w ⊆ row gs L w p :=
  query_mono gs α _ (fun a => hα a _) w

lemma bare_label_empty {N : ℕ} (gs : List Instruction)
    (hhead : gs.head? = some (Sum.inl [])) (α : ℕ → Bool)
    (w : ℕ) (hw : w ∈ labelG gs N α) : bare (N := N) gs α w = ∅ := by
  classical
  have hk := (Finset.mem_filter.mp hw).2
  have hf : α (labelID gs N w) = false := by
    cases he : gateAt gs N w with
    | inl rs => simp [IsLabel, he] at hk
    | inr ar => simpa [IsLabel, labelID, he] using hk
  exact (query_label_eq gs hhead α α w hw).trans (by simp [hf])


open Classical

noncomputable def retained {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (gs : List Instruction) (α : ℕ → Bool) (L : ℕ → (Fin N → Bool) → Bool)
    (w : ℕ) : Finset (Fin N) := by
  classical
  exact Nat.strongRecOn w fun i prev =>
    if i ∈ orG gs N α then
      (kids gs N i).biUnion fun c => if h : c < i then prev c h else ∅
    else if i ∈ labelG gs N α then
      (alive gs L i).filter fun p =>
        (if h : child gs N i < i then p ∈ prev (child gs N i) h else False) ∨
          goodFirst I (bare gs α (child gs N i)) p
    else ∅

lemma retained_eq {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (gs : List Instruction) (α : ℕ → Bool) (L : ℕ → (Fin N → Bool) → Bool)
    (w : ℕ) :
    retained I gs α L w =
    if w ∈ orG gs N α then
      (kids gs N w).biUnion fun c => if c < w then retained I gs α L c else ∅
    else if w ∈ labelG gs N α then
      (alive gs L w).filter fun p =>
        (if child gs N w < w then p ∈ retained I gs α L (child gs N w) else False) ∨
          goodFirst I (bare gs α (child gs N w)) p
    else ∅ := by
  classical
  unfold retained
  rw [Nat.strongRecOn_eq]
  rfl

lemma retained_or_law {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (gs : List Instruction) (hhead : gs.head? = some (Sum.inl []))
    (α : ℕ → Bool) (L : ℕ → (Fin N → Bool) → Bool)
    (w : ℕ) (hw : w ∈ orG gs N α) (p : Fin N) :
    p ∈ retained I gs α L w ↔ ∃ c ∈ kids gs N w, p ∈ retained I gs α L c := by
  classical
  rw [retained_eq, ite_eq_left hw]
  simp only [Finset.mem_biUnion]
  constructor
  · rintro ⟨c, hc, hp⟩
    exact ⟨c, hc, by simpa [or_lower gs hhead N α w hw c hc] using hp⟩
  · rintro ⟨c, hc, hp⟩
    exact ⟨c, hc, by simpa [or_lower gs hhead N α w hw c hc] using hp⟩

lemma retained_label_law {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (gs : List Instruction) (hhead : gs.head? = some (Sum.inl []))
    (α : ℕ → Bool) (L : ℕ → (Fin N → Bool) → Bool)
    (w : ℕ) (hw : w ∈ labelG gs N α) (p : Fin N) :
    p ∈ retained I gs α L w ↔ p ∈ alive gs L w ∧
      (p ∈ retained I gs α L (child gs N w) ∨
        goodFirst I (bare gs α (child gs N w)) p) := by
  classical
  have hn : w ∉ orG gs N α := fun ho => Finset.disjoint_left.mp (gates_disjoint gs N α) ho hw
  rw [retained_eq, ite_eq_right hn, ite_eq_left hw]
  simp only [Finset.mem_filter, ite_eq_left (label_lower gs hhead N α w hw)]

lemma retained_other_law {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (gs : List Instruction) (α : ℕ → Bool) (L : ℕ → (Fin N → Bool) → Bool)
    (w : ℕ) (hor : w ∉ orG gs N α) (hlab : w ∉ labelG gs N α) :
    retained I gs α L w = ∅ := by
  classical
  rw [retained_eq, ite_eq_right hor, ite_eq_right hlab]

lemma first_origin {N : ℕ} (gs : List Instruction)
    (hhead : gs.head? = some (Sum.inl [])) (α : ℕ → Bool)
    (L : ℕ → (Fin N → Bool) → Bool)
    (hα : ∀ a x, α a = true → L a x = true)
    (i : ℕ) (p l : Fin N) (hl : l ∈ row gs L i p) :
    l ∈ bare gs α i ∨ ∃ g ∈ labelG gs N α, p ∈ alive gs L g ∧
      l ∈ bare gs α (child gs N g) ∧ bare gs α (child gs N g) ⊆ row gs L i p := by
  exact Pilot5bMeta1020FirstQuery.first_origin
    (orG gs N α) (labelG gs N α) (kids gs N) (child gs N)
    (alive gs L) (bare gs α) (row gs L)
    (or_lower gs hhead N α) (label_lower gs hhead N α)
    (row_or_law gs hhead α L hα) (row_label_law gs hhead α L)
    (row_other_law gs α L) (bare_or_law gs hhead α) (bare_sub_row gs α L hα) i p l hl

lemma retained_origin {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (gs : List Instruction) (hhead : gs.head? = some (Sum.inl [])) (α : ℕ → Bool)
    (L : ℕ → (Fin N → Bool) → Bool)
    (hα : ∀ a x, α a = true → L a x = true)
    (i : ℕ) (p : Fin N) (hp : p ∈ retained I gs α L i) :
    ∃ g ∈ labelG gs N α, p ∈ alive gs L g ∧ goodFirst I (bare gs α (child gs N g)) p ∧
      bare gs α (child gs N g) ⊆ row gs L i p := by
  exact Pilot5bMeta1020FirstQuery.retained_origin I
    (orG gs N α) (labelG gs N α) (kids gs N) (child gs N)
    (alive gs L) (retained I gs α L) (bare gs α) (row gs L)
    (or_lower gs hhead N α) (label_lower gs hhead N α)
    (retained_or_law I gs hhead α L) (retained_label_law I gs hhead α L)
    (retained_other_law I gs α L)
    (row_or_law gs hhead α L hα) (row_label_law gs hhead α L)
    (bare_sub_row gs α L hα) i p hp

lemma uncharged_pair_retained {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (gs : List Instruction) (hhead : gs.head? = some (Sum.inl [])) (α : ℕ → Bool)
    (L : ℕ → (Fin N → Bool) → Bool)
    (hα : ∀ a x, α a = true → L a x = true)
    (E : Finset (Fin N × Fin N)) (p l : Fin N) (hI : I p l) (hE : (p, l) ∉ E)
    (hsmall : (p, l) ∉ smallPairs I (labelG gs N α) (alive gs L)
      (fun g => bare gs α (child gs N g)) E)
    (hown : (p, l) ∉ ownHeavyPairs I (labelG gs N α)
      (fun g => bare gs α (child gs N g)))
    (i : ℕ) (hl : l ∈ row gs L i p) (hbare : l ∉ bare gs α i) :
    p ∈ retained I gs α L i := by
  exact Pilot5bMeta1020FirstQuery.uncharged_pair_retained I
    (orG gs N α) (labelG gs N α) (kids gs N) (child gs N)
    (alive gs L) (retained I gs α L) (bare gs α) (row gs L)
    (or_lower gs hhead N α) (label_lower gs hhead N α)
    (retained_or_law I gs hhead α L) (retained_label_law I gs hhead α L)
    (row_or_law gs hhead α L hα) (row_label_law gs hhead α L)
    (row_other_law gs α L) (bare_or_law gs hhead α)
    E p l hI hE hsmall hown i hl hbare

end Pilot5bMeta1020LinearDAG

namespace Pilot5bMeta1020DeadCover
open PEqualNP.CircuitLowerBounds
def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma gate_inputs {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ r ∈ P, r < w) ∧
      ∀ (x y : Fin n → Bool), (∀ r ∈ P, value C x r = true → value C y r = true) →
        value C x w = true → value C y w = true := by
  let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem _)
  let P := g.inputs.toFinset.filter (· < w)
  refine ⟨P, (Finset.card_filter_le _ _).trans ((List.toFinset_card_le g.inputs).trans hlen), ?_, ?_⟩
  · exact fun r hr => (Finset.mem_filter.mp hr).2
  · intro x y hxy hx
    have step (r) (hr : r ∈ g.inputs) :
        (if r < w then value C x r else false) = true →
        (if r < w then value C y r else false) = true := by
      by_cases h : r < w
      · simpa [h] using hxy r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr,h⟩)
      · simp [h]
    have form (z : Fin n → Bool) :
        value C z w = g.op.eval (g.inputs.map fun r => if r < w then value C z r else false) :=
      gate_value C z w hn hw
    rw [form x] at hx
    rw [form y]
    rcases hop with hop|hop
    · simp only [hop, GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hx ⊢
      intro b hb
      obtain ⟨r,hr,rfl⟩ := hb
      exact step r hr (hx _ ⟨r,hr,rfl⟩)
    · simp only [hop, GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hx ⊢
      obtain ⟨b,⟨r,hr,rfl⟩,hv⟩ := hx
      exact ⟨_, ⟨r,hr,rfl⟩, step r hr hv⟩

lemma value_mono {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using hxy p
    by_cases hw : w < n + C.size
    · obtain ⟨P, _, hP, hstep⟩ := gate_inputs C hG w (by omega) hw
      exact hstep x y fun r hr => ih r (hP r hr)
    · simp [missing_value C x w (by omega)]

def support {n : ℕ} (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p => value C (fun q => decide (q = p)) w = true)

lemma mem_support {n : ℕ} (C : Circuit) (w : ℕ) (p : Fin n) :
    p ∈ support C w ↔ value C (fun q => decide (q = p)) w = true := by
  simp [support]

lemma support_gate {n : ℕ} (C : Circuit) (w : ℕ) (h : 2 ≤ (support (n := n) C w).card) :
    n ≤ w ∧ w < n + C.size := by
  constructor
  · by_contra! hw
    let p : Fin n := ⟨w, hw⟩
    have hs : support C w ⊆ {p} := by
      intro q hq
      have hv := (mem_support C w q).mp hq
      change value C (fun r => decide (r = q)) p = true at hv
      simpa [input_value, eq_comm] using hv
    have hb := Finset.card_le_card hs
    simp at hb
    omega
  · by_contra! hw
    have hs : support (n := n) C w = ∅ := by
      ext q
      simp [mem_support, missing_value C _ w hw]
    simp [hs] at h

abbrev good (C : Circuit) := ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

def bit {n : ℕ} (A : Finset (Fin n)) (v : Fin n) : Bool := decide (v ∈ A)

def psupport {n : ℕ} (C : Circuit) (P : Finset (Fin n)) (w : ℕ) := support C w ∩ P

noncomputable def kids {n : ℕ} (C : Circuit) (hg : good C) (w : ℕ) : Finset ℕ :=
  if h : n ≤ w ∧ w < n + C.size then (gate_inputs (n := n) C hg w h.1 h.2).choose else ∅

lemma kids_spec {n : ℕ} (C : Circuit) (hg : good C) (w : ℕ) :
    (kids (n := n) C hg w).card ≤ 2 ∧
    (∀ c ∈ kids (n := n) C hg w, c < w) ∧
    (n ≤ w → w < n + C.size → ∀ x y : Fin n → Bool,
      (∀ c ∈ kids (n := n) C hg w, value C x c = true → value C y c = true) →
      value C x w = true → value C y w = true) := by
  unfold kids
  split_ifs with h
  · have hs := (gate_inputs (n := n) C hg w h.1 h.2).choose_spec
    exact ⟨hs.1, hs.2.1, fun _ _ => hs.2.2⟩
  · exact ⟨by simp, by simp, fun hn hw => (h ⟨hn, hw⟩).elim⟩

lemma differing_child {n : ℕ} (C : Circuit) (hg : good C) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) (x y : Fin n → Bool)
    (hx : value C x w = true) (hy : value C y w = false) :
    ∃ c ∈ kids (n := n) C hg w, value C x c = true ∧ value C y c = false := by
  by_contra! h
  have ht := (kids_spec (n := n) C hg w).2.2 hn hw x y (by
    intro c hc hcx
    exact Bool.eq_true_of_not_eq_false (h c hc hcx)) hx
  simp [hy] at ht

def deadInput {n m : ℕ} (P : Finset (Fin n)) (T : Fin m → Finset (Fin n))
    (S : Finset (Fin m)) : Fin n → Bool := bit (P \ S.biUnion T)

def dead {n m : ℕ} (C : Circuit) (P : Finset (Fin n))
    (T : Fin m → Finset (Fin n)) (d w : ℕ) : Prop :=
  ∃ S : Finset (Fin m), S.card ≤ d ∧ value C (deadInput P T S) w = false

lemma dead_of_false {n m : ℕ} (C : Circuit) (hg : good C) (P : Finset (Fin n))
    (T : Fin m → Finset (Fin n)) (d w : ℕ) (S : Finset (Fin m))
    (hS : S.card ≤ d) (y : Fin n → Bool) (hy : value C y w = false)
    (hcover : ∀ p ∈ P, p ∉ S.biUnion T → y p = true) : dead C P T d w := by
  refine ⟨S, hS, ?_⟩
  apply Bool.eq_false_of_not_eq_true
  intro hpos
  have hm := value_mono C hg (deadInput P T S) y (by
    intro p hp
    have hp' : p ∈ P \ S.biUnion T := of_decide_eq_true hp
    exact hcover p (Finset.mem_sdiff.mp hp').1 (Finset.mem_sdiff.mp hp').2) w hpos
  simp [hy] at hm

lemma alive_covered {n m : ℕ} (C : Circuit) (hg : good C) (P : Finset (Fin n))
    (T : Fin m → Finset (Fin n)) (S : Finset (Fin m)) (w : ℕ)
    (hw : value C (deadInput P T S) w = false) :
    psupport C P w ⊆ S.biUnion T := by
  intro p hp
  by_contra hnot
  have hpos := (mem_support C w p).mp (Finset.mem_inter.mp hp).1
  have hm := value_mono C hg (fun q => decide (q = p)) (deadInput P T S) (by
    intro q hq
    have eq : q = p := of_decide_eq_true hq
    subst q
    simp [deadInput, bit, (Finset.mem_inter.mp hp).2, hnot]) w hpos
  simp [hw] at hm

lemma heavy_lines {n m : ℕ} (C : Circuit) (hg : good C) (P : Finset (Fin n))
    (T : Fin m → Finset (Fin n))
    (hT : ∀ i j, i ≠ j → (T i ∩ T j).card ≤ 1)
    (d w : ℕ) (hw : dead C P T d w) :
    (Finset.univ.filter fun l => d + 1 ≤ (psupport C P w ∩ T l).card).card ≤ d := by
  classical
  obtain ⟨S, hS, hfalse⟩ := hw
  refine (Finset.card_le_card (t := S) ?_).trans hS
  intro l hl
  have hlarge := (Finset.mem_filter.mp hl).2
  by_contra hnot
  have hsub : psupport C P w ∩ T l ⊆ S.biUnion (fun s => T s ∩ T l) := by
    intro p hp
    obtain ⟨s, hs, hps⟩ := Finset.mem_biUnion.mp
      (alive_covered C hg P T S w hfalse (Finset.mem_inter.mp hp).1)
    exact Finset.mem_biUnion.mpr ⟨s, hs, Finset.mem_inter.mpr ⟨hps, (Finset.mem_inter.mp hp).2⟩⟩
  have hb := Finset.card_biUnion_le_card_mul S (fun s => T s ∩ T l) 1 (by
    intro s hs
    exact hT s l (fun h => hnot (h ▸ hs)))
  have hc := Finset.card_le_card hsub
  simp only [mul_one] at hb
  omega

lemma projected_support_gate {n : ℕ} (C : Circuit) (P : Finset (Fin n)) (w : ℕ)
    (h : 2 ≤ (psupport C P w).card) : n ≤ w ∧ w < n + C.size :=
  support_gate C w (h.trans (Finset.card_le_card Finset.inter_subset_left))

lemma charge {n m : ℕ} (C : Circuit) (hg : good C) (P : Finset (Fin n))
    (T : Fin m → Finset (Fin n)) (d : ℕ) (hd : 1 ≤ d)
    (G : Finset ℕ)
    (hdown : ∀ g ∈ G, ∀ c ∈ kids (n := n) C hg g, n ≤ c → c ∈ G)
    (p : Fin n) (l : Fin m) (S : Finset (Fin m)) :
    ∀ w, w ∈ G → p ∈ psupport C P w →
      value C (deadInput P T S) w = false → d + 1 ≤ (psupport C P w ∩ T l).card →
      ∃ g ∈ G, value C (deadInput P T S) g = false ∧
        d + 1 ≤ (psupport C P g ∩ T l).card ∧
        ∃ c ∈ kids (n := n) C hg g, p ∈ psupport C P c ∧
          (psupport C P c ∩ T l).card ≤ d := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hp hfalse hlarge
    have hgate := projected_support_gate C P w (by
      have hle := Finset.card_le_card (Finset.inter_subset_left (s₁ := psupport C P w) (s₂ := T l))
      omega)
    obtain ⟨c, hc, hcpos, hcfalse⟩ := differing_child C hg w hgate.1 hgate.2
      (fun q => decide (q = p)) (deadInput P T S)
      ((mem_support C w p).mp (Finset.mem_inter.mp hp).1) hfalse
    have hpc : p ∈ psupport C P c :=
      Finset.mem_inter.mpr ⟨(mem_support C c p).mpr hcpos, (Finset.mem_inter.mp hp).2⟩
    by_cases hclarge : d + 1 ≤ (psupport C P c ∩ T l).card
    · have hcgate := projected_support_gate C P c (by
        have hle := Finset.card_le_card (Finset.inter_subset_left (s₁ := psupport C P c) (s₂ := T l))
        omega)
      exact ih c ((kids_spec C hg w).2.1 c hc) (hdown w hw c hc hcgate.1) hpc hcfalse hclarge
    · exact ⟨w, hw, hfalse, hlarge, c, hc, hpc, by omega⟩

noncomputable def counted {n m : ℕ} (C : Circuit) (P : Finset (Fin n))
    (T : Fin m → Finset (Fin n)) (G : Finset ℕ) (d : ℕ) : Finset (Fin n × Fin m) := by
  classical
  exact Finset.univ.filter fun e => e.1 ∈ T e.2 ∧ ∃ w ∈ G,
    dead C P T d w ∧ e.1 ∈ psupport C P w ∧ d + 1 ≤ (psupport C P w ∩ T e.2).card

theorem dead_cover_bound {n m : ℕ} (C : Circuit) (hg : good C) (P : Finset (Fin n))
    (T : Fin m → Finset (Fin n))
    (hT : ∀ i j, i ≠ j → (T i ∩ T j).card ≤ 1)
    (d : ℕ) (hd : 1 ≤ d) (G : Finset ℕ)
    (hdown : ∀ g ∈ G, ∀ c ∈ kids (n := n) C hg g, n ≤ c → c ∈ G) :
    (counted C P T G d).card ≤ (2 * d * d) * G.card := by
  classical
  let Lg : ℕ → Finset (Fin m) := fun g => Finset.univ.filter fun l =>
    d + 1 ≤ (psupport C P g ∩ T l).card ∧ dead C P T d g
  let Tc : Fin m → ℕ → Finset (Fin n × Fin m) := fun l c =>
    if (psupport C P c ∩ T l).card ≤ d then
      (psupport C P c ∩ T l).image (fun p => (p, l)) else ∅
  have hLg : ∀ g, (Lg g).card ≤ d := by
    intro g
    by_cases hdead : dead C P T d g
    · have heq : Lg g = Finset.univ.filter (fun l => d + 1 ≤ (psupport C P g ∩ T l).card) := by
        ext l
        simp [Lg, hdead]
      rw [heq]
      exact heavy_lines C hg P T hT d g hdead
    · simp [Lg, hdead]
  have hTc : ∀ l c, (Tc l c).card ≤ d := by
    intro l c
    simp only [Tc]
    split_ifs with h
    · exact Finset.card_image_le.trans h
    · simp
  have hsub : counted C P T G d ⊆ G.biUnion
      (fun g => (Lg g).biUnion (fun l => (kids (n := n) C hg g).biUnion (fun c => Tc l c))) := by
    intro e he
    obtain ⟨_, heT, w, hw, ⟨S, hS, hfalse⟩, hp, hlarge⟩ := Finset.mem_filter.mp he
    obtain ⟨g, hgG, hgfalse, hglarge, c, hc, hpc, hcsmall⟩ :=
      charge C hg P T d hd G hdown e.1 e.2 S w hw hp hfalse hlarge
    refine Finset.mem_biUnion.mpr ⟨g, hgG, Finset.mem_biUnion.mpr
      ⟨e.2, ?_, Finset.mem_biUnion.mpr ⟨c, hc, ?_⟩⟩⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hglarge, S, hS, hgfalse⟩
    · simp only [Tc, ite_eq_left hcsmall, Finset.mem_image]
      exact ⟨e.1, Finset.mem_inter.mpr ⟨hpc, heT⟩, rfl⟩
  refine (Finset.card_le_card hsub).trans ?_
  refine (Finset.card_biUnion_le_card_mul G _ (2 * d * d) ?_).trans (by rw [Nat.mul_comm])
  intro g _
  refine (Finset.card_biUnion_le_card_mul (Lg g) _ (2 * d) ?_).trans ?_
  · intro l _
    refine (Finset.card_biUnion_le_card_mul (kids (n := n) C hg g) _ d (fun c _ => hTc l c)).trans ?_
    exact Nat.mul_le_mul_right d (kids_spec (n := n) C hg g).1
  · have hb := Nat.mul_le_mul_right (2 * d) (hLg g)
    nlinarith

theorem three_line_bound {n m : ℕ} (C : Circuit) (hg : good C) (P : Finset (Fin n))
    (T : Fin m → Finset (Fin n))
    (hT : ∀ i j, i ≠ j → (T i ∩ T j).card ≤ 1)
    (G : Finset ℕ)
    (hdown : ∀ g ∈ G, ∀ c ∈ kids (n := n) C hg g, n ≤ c → c ∈ G) :
    (counted C P T G 3).card ≤ 18 * G.card := by
  simpa using dead_cover_bound C hg P T hT 3 (by omega) G hdown

theorem all_gates_dead_cover_bound {n m : ℕ} (C : Circuit) (hg : good C)
    (P : Finset (Fin n)) (T : Fin m → Finset (Fin n))
    (hT : ∀ i j, i ≠ j → (T i ∩ T j).card ≤ 1) (d : ℕ) (hd : 1 ≤ d) :
    (counted C P T (Finset.Ico n (n + C.size)) d).card ≤ (2 * d * d) * C.size := by
  have hdown : ∀ g ∈ Finset.Ico n (n + C.size),
      ∀ c ∈ kids (n := n) C hg g, n ≤ c → c ∈ Finset.Ico n (n + C.size) := by
    intro g hgG c hc hcn
    have hclt := (kids_spec (n := n) C hg g).2.1 c hc
    exact Finset.mem_Ico.mpr ⟨hcn, lt_trans hclt (Finset.mem_Ico.mp hgG).2⟩
  simpa using dead_cover_bound C hg P T hT d hd (Finset.Ico n (n + C.size)) hdown

theorem all_gates_three_line_bound {n m : ℕ} (C : Circuit) (hg : good C)
    (P : Finset (Fin n)) (T : Fin m → Finset (Fin n))
    (hT : ∀ i j, i ≠ j → (T i ∩ T j).card ≤ 1) :
    (counted C P T (Finset.Ico n (n + C.size)) 3).card ≤ 18 * C.size := by
  simpa using all_gates_dead_cover_bound C hg P T hT 3 (by omega)

end Pilot5bMeta1020DeadCover

namespace Pilot5bMeta1020FirstQuery

open PEqualNP.CircuitLowerBounds

theorem or_value_source {N : ℕ} (B : Circuit)
    (hOR : ∀ g ∈ B.gates, g.op = GateOp.or) (x : Fin N → Bool) :
    ∀ w, Pilot5bMeta1020DeadCover.value B x w = true →
      ∃ p : Fin N, x p = true ∧
        Pilot5bMeta1020DeadCover.value B (fun q => decide (q = p)) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hx
    by_cases hn : w < N
    · let p : Fin N := ⟨w, hn⟩
      refine ⟨p, ?_, ?_⟩
      · change Pilot5bMeta1020DeadCover.value B x p = true at hx
        simpa only [Pilot5bMeta1020DeadCover.input_value] using hx
      · change Pilot5bMeta1020DeadCover.value B (fun q => decide (q = p)) p = true
        simp only [Pilot5bMeta1020DeadCover.input_value, decide_true]
    · by_cases hw : w < N + B.size
      · let g := B.gates[w - N]'(by unfold Circuit.size at hw; omega)
        have hop : g.op = GateOp.or := hOR g (List.getElem_mem _)
        have form (z : Fin N → Bool) :
            Pilot5bMeta1020DeadCover.value B z w =
              g.op.eval (g.inputs.map fun r =>
                if r < w then Pilot5bMeta1020DeadCover.value B z r else false) :=
          Pilot5bMeta1020DeadCover.gate_value B z w (by omega) hw
        rw [form x] at hx
        simp only [hop, GateOp.eval, List.any_map, List.any_eq_true,
          Function.comp_apply, id] at hx
        obtain ⟨r, hr, hrv⟩ := hx
        have hrw : r < w := by
          by_contra h
          simp [h] at hrv
        have hrtrue : Pilot5bMeta1020DeadCover.value B x r = true := by
          simpa only [ite_eq_left hrw] using hrv
        obtain ⟨p, hp, hpv⟩ := ih r hrw hrtrue
        refine ⟨p, hp, ?_⟩
        rw [form]
        simp only [hop, GateOp.eval, List.any_map, List.any_eq_true,
          Function.comp_apply, id]
        exact ⟨r, hr, by simpa only [ite_eq_left hrw] using hpv⟩
      · rw [Pilot5bMeta1020DeadCover.missing_value B x w (by omega)] at hx
        contradiction

theorem or_query_semantics {N : ℕ} (B : Circuit)
    (hB : Pilot5bMeta1020DeadCover.good B)
    (hOR : ∀ g ∈ B.gates, g.op = GateOp.or) (w : ℕ) (x : Fin N → Bool) :
    Pilot5bMeta1020DeadCover.value B x w = true ↔
      ∃ p ∈ Pilot5bMeta1020DeadCover.support B w, x p = true := by
  constructor
  · intro hx
    obtain ⟨p, hp, hpv⟩ := or_value_source B hOR x w hx
    exact ⟨p, (Pilot5bMeta1020DeadCover.mem_support B w p).mpr hpv, hp⟩
  · rintro ⟨p, hp, hpx⟩
    apply Pilot5bMeta1020DeadCover.value_mono B hB (fun q => decide (q = p)) x _ w
      ((Pilot5bMeta1020DeadCover.mem_support B w p).mp hp)
    intro q hq
    have hqp : q = p := of_decide_eq_true hq
    simpa only [hqp] using hpx

theorem own_heavy_bound {N : ℕ} {G : Type*} [DecidableEq G]
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (B : Circuit) (hB : Pilot5bMeta1020DeadCover.good B)
    (hI : ∀ p q, p ≠ q → (pencil I p ∩ pencil I q).card ≤ 1)
    (gs : Finset G) (A : G → Finset (Fin N)) (wire : G → ℕ)
    (hA : ∀ g ∈ gs, A g = Pilot5bMeta1020DeadCover.support B (wire g))
    (hquery : ∀ g ∈ gs, ∀ x : Fin N → Bool,
      Pilot5bMeta1020DeadCover.value B x (wire g) = true ↔ ∃ l ∈ A g, x l = true) :
    (ownHeavyPairs I gs A).card ≤ 8 * B.size := by
  classical
  let E := Pilot5bMeta1020DeadCover.counted B Finset.univ (pencil I)
    (Finset.Ico N (N + B.size)) 2
  have hsub : (ownHeavyPairs I gs A).image Prod.swap ⊆ E := by
    intro e he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨_, hIa, g, hg, hline, ⟨T, hTc, hcover⟩, hheavy⟩ := Finset.mem_filter.mp ha
    have hproj : Pilot5bMeta1020DeadCover.psupport B Finset.univ (wire g) = A g := by
      simp only [Pilot5bMeta1020DeadCover.psupport, Finset.inter_univ, ← hA g hg]
    have hcard : 2 ≤ (Pilot5bMeta1020DeadCover.support (n := N) B (wire g)).card := by
      have hle := Finset.card_filter_le (A g) (I a.1)
      rw [← hA g hg]
      omega
    have hgate := Pilot5bMeta1020DeadCover.support_gate B (wire g) hcard
    have hfalse : Pilot5bMeta1020DeadCover.value B
        (Pilot5bMeta1020DeadCover.deadInput Finset.univ (pencil I) T) (wire g) = false := by
      apply Bool.eq_false_iff.mpr
      intro hv
      obtain ⟨l, hl, hlt⟩ := (hquery g hg _).mp hv
      have hbad := hcover hl
      simpa [Pilot5bMeta1020DeadCover.deadInput, Pilot5bMeta1020DeadCover.bit, hbad] using hlt
    have hinter : (A g ∩ pencil I a.1) = (A g).filter (I a.1) := by
      ext l
      simp [pencil]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, wire g, Finset.mem_Ico.mpr hgate, ?_, ?_, ?_⟩
    · simpa [pencil] using hIa
    · exact ⟨T, hTc, hfalse⟩
    · change a.2 ∈ Pilot5bMeta1020DeadCover.psupport B Finset.univ (wire g)
      rw [hproj]
      exact hline
    · change 2 + 1 ≤ (Pilot5bMeta1020DeadCover.psupport B Finset.univ (wire g) ∩ pencil I a.1).card
      rw [hproj, hinter]
      exact hheavy
  have hinj : Function.Injective (Prod.swap : Fin N × Fin N → Fin N × Fin N) := by
    intro a b h
    simpa using congrArg Prod.swap h
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj] at hcard
  exact hcard.trans (by
    simpa only [E] using Pilot5bMeta1020DeadCover.all_gates_dead_cover_bound
      B hB Finset.univ (pencil I) hI 2 (by omega))

theorem own_heavy_bound_of_or {N : ℕ} {G : Type*} [DecidableEq G]
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (B : Circuit) (hB : Pilot5bMeta1020DeadCover.good B)
    (hOR : ∀ g ∈ B.gates, g.op = GateOp.or)
    (hI : ∀ p q, p ≠ q → (pencil I p ∩ pencil I q).card ≤ 1)
    (gs : Finset G) (A : G → Finset (Fin N)) (wire : G → ℕ)
    (hA : ∀ g ∈ gs, A g = Pilot5bMeta1020DeadCover.support B (wire g)) :
    (ownHeavyPairs I gs A).card ≤ 8 * B.size := by
  apply own_heavy_bound I B hB hI gs A wire hA
  intro g hg x
  simpa only [hA g hg] using or_query_semantics B hB hOR (wire g) x

end Pilot5bMeta1020FirstQuery


namespace Pilot5bMeta1020BareCircuit

open PEqualNP.CircuitLowerBounds Pilot5bMeta1020Linear

def bareGate (labels : ℕ → Bool) : Instruction → Gate
  | Sum.inl rs => ⟨GateOp.or, rs⟩
  | Sum.inr (a, r) => ⟨GateOp.or, if labels a then [r] else []⟩

def bareCircuit (gs : List Instruction) (labels : ℕ → Bool) : Circuit :=
  ⟨gs.map (bareGate labels), 0⟩

@[local simp] lemma bareGate_op (labels : ℕ → Bool) (g : Instruction) :
    (bareGate labels g).op = GateOp.or := by
  cases g <;> rfl

lemma bareGate_eval (labels : ℕ → Bool) (w : List Bool) (g : Instruction) :
    (bareGate labels g).op.eval ((bareGate labels g).inputs.map fun r => w.getD r false) =
      step labels w g := by
  cases g with
  | inl rs => rfl
  | inr ar =>
    rcases ar with ⟨a, r⟩
    cases ha : labels a <;> simp [bareGate, step, GateOp.eval, ha]

lemma wires_eq (gs : List Instruction) (labels : ℕ → Bool) (y : List Bool) :
    (bareCircuit gs labels).wires y = run gs labels y := by
  induction gs generalizing y with
  | nil => rfl
  | cons g gs ih =>
    change (bareCircuit gs labels).wires
        (y ++ [(bareGate labels g).op.eval
          ((bareGate labels g).inputs.map fun r => y.getD r false)]) =
      run gs labels (y ++ [step labels y g])
    rw [bareGate_eval]
    exact ih _

@[local simp] lemma size_eq (gs : List Instruction) (labels : ℕ → Bool) :
    (bareCircuit gs labels).size = gs.length := by
  simp [bareCircuit, Circuit.size]

lemma monotone2 (gs : List Instruction) (labels : ℕ → Bool)
    (hfan : ∀ rs, Sum.inl rs ∈ gs → rs.length ≤ 2) :
    PEqualNP.MetaComplexity.Monotone2 (bareCircuit gs labels) := by
  intro g hg
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hg
  constructor
  · simp
  · cases i with
    | inl rs => exact hfan rs hi
    | inr ar =>
      rcases ar with ⟨a, r⟩
      cases ha : labels a <;> simp [bareGate, ha]

lemma wire_query {n : ℕ} (gs : List Instruction) (labels : ℕ → Bool)
    (y : Fin n → Bool) (w : ℕ) :
    ((bareCircuit gs labels).wires (List.ofFn y)).getD w false =
      hits y ((queries gs labels).getD w ∅) := by
  rw [wires_eq, Pilot5bMeta1020Linear.wire_query]

lemma wire_true {n : ℕ} (gs : List Instruction) (labels : ℕ → Bool)
    (y : Fin n → Bool) (w : ℕ) :
    ((bareCircuit gs labels).wires (List.ofFn y)).getD w false = true ↔
      ∃ l ∈ (queries gs labels).getD w ∅, y l = true := by
  rw [wires_eq, Pilot5bMeta1020Linear.wire_true]

lemma singleton_true {n : ℕ} (gs : List Instruction) (labels : ℕ → Bool)
    (p : Fin n) (w : ℕ) :
    ((bareCircuit gs labels).wires
      (List.ofFn (fun q : Fin n => decide (q = p)))).getD w false = true ↔
        p ∈ (queries gs labels).getD w ∅ := by
  rw [wire_true]
  simp

lemma singleton_support_eq {n : ℕ} (gs : List Instruction) (labels : ℕ → Bool)
    (w : ℕ) :
    (Finset.univ.filter fun p : Fin n =>
      ((bareCircuit gs labels).wires
        (List.ofFn (fun q : Fin n => decide (q = p)))).getD w false = true) =
      (queries gs labels).getD w ∅ := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, singleton_true]

end Pilot5bMeta1020BareCircuit

namespace Pilot5bMeta1020FirstQuery

open PEqualNP.CircuitLowerBounds

noncomputable def honestLargeQueryPairs {N : ℕ}
    (I : Fin N → Fin N → Prop) [DecidableRel I] (B : Circuit) :
    Finset (Fin N × Fin N) := by
  classical
  exact Finset.univ.filter fun e => ∃ w : ℕ,
    e.2 ∈ Pilot5bMeta1020DeadCover.support B w ∧
    Pilot5bMeta1020DeadCover.support B w ⊆ pencil I e.1 ∧
    2 ≤ (Pilot5bMeta1020DeadCover.support (n := N) B w).card

lemma mem_honestLargeQueryPairs {N : ℕ}
    (I : Fin N → Fin N → Prop) [DecidableRel I] (B : Circuit)
    (p l : Fin N) :
    (p, l) ∈ honestLargeQueryPairs I B ↔ ∃ w : ℕ,
      l ∈ Pilot5bMeta1020DeadCover.support B w ∧
      Pilot5bMeta1020DeadCover.support B w ⊆ pencil I p ∧
      2 ≤ (Pilot5bMeta1020DeadCover.support (n := N) B w).card := by
  classical
  simp [honestLargeQueryPairs]

theorem honest_large_query_bound {N : ℕ}
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (B : Circuit) (hB : Pilot5bMeta1020DeadCover.good B)
    (hOR : ∀ g ∈ B.gates, g.op = GateOp.or)
    (hI : ∀ p q, p ≠ q → (pencil I p ∩ pencil I q).card ≤ 1) :
    (honestLargeQueryPairs I B).card ≤ 2 * B.size := by
  classical
  let E := Pilot5bMeta1020DeadCover.counted B Finset.univ (pencil I)
    (Finset.Ico N (N + B.size)) 1
  have hsub : (honestLargeQueryPairs I B).image Prod.swap ⊆ E := by
    intro e he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨w, hl, hcover, hlarge⟩ := (mem_honestLargeQueryPairs I B a.1 a.2).mp ha
    have hgate := Pilot5bMeta1020DeadCover.support_gate B w hlarge
    have hproj : Pilot5bMeta1020DeadCover.psupport B Finset.univ w =
        Pilot5bMeta1020DeadCover.support (n := N) B w := by
      simp [Pilot5bMeta1020DeadCover.psupport]
    have hfalse : Pilot5bMeta1020DeadCover.value B
        (Pilot5bMeta1020DeadCover.deadInput Finset.univ (pencil I) {a.1}) w = false := by
      apply Bool.eq_false_iff.mpr
      intro hv
      obtain ⟨l, hls, hlt⟩ := (or_query_semantics B hB hOR w _).mp hv
      have hbad : l ∈ ({a.1} : Finset (Fin N)).biUnion (pencil I) :=
        Finset.mem_biUnion.mpr ⟨a.1, by simp, hcover hls⟩
      have hlt' : l ∈ Finset.univ \ ({a.1} : Finset (Fin N)).biUnion (pencil I) :=
        of_decide_eq_true hlt
      exact (Finset.mem_sdiff.mp hlt').2 hbad
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, hcover hl, w, Finset.mem_Ico.mpr hgate, ?_, ?_, ?_⟩
    · exact ⟨{a.1}, by simp, hfalse⟩
    · change a.2 ∈ Pilot5bMeta1020DeadCover.psupport B Finset.univ w
      simpa only [hproj] using hl
    · change 1 + 1 ≤ (Pilot5bMeta1020DeadCover.psupport B Finset.univ w ∩ pencil I a.1).card
      rw [hproj, Finset.inter_eq_left.mpr hcover]
      exact hlarge
  have hinj : Function.Injective (Prod.swap : Fin N × Fin N → Fin N × Fin N) := by
    intro a b h
    simpa using congrArg Prod.swap h
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj] at hcard
  exact hcard.trans (by
    simpa [E] using Pilot5bMeta1020DeadCover.all_gates_dead_cover_bound
      B hB Finset.univ (pencil I) hI 1 (by omega))

lemma honest_large_query_mem {N : ℕ}
    (I : Fin N → Fin N → Prop) [DecidableRel I] (B : Circuit)
    (Q : Finset (Fin N)) (w : ℕ)
    (hQ : Q = Pilot5bMeta1020DeadCover.support B w)
    (p l : Fin N) (hl : l ∈ Q) (hcover : Q ⊆ pencil I p) (hlarge : 2 ≤ Q.card) :
    (p, l) ∈ honestLargeQueryPairs I B := by
  apply (mem_honestLargeQueryPairs I B p l).mpr
  exact ⟨w, hQ ▸ hl, hQ ▸ hcover, hQ ▸ hlarge⟩

noncomputable def honestLargePairs {N : ℕ} {G : Type*} [DecidableEq G]
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (gs : Finset G) (A : G → Finset (Fin N)) : Finset (Fin N × Fin N) := by
  classical
  exact Finset.univ.filter fun e => ∃ g ∈ gs,
    e.2 ∈ A g ∧ A g ⊆ pencil I e.1 ∧ 2 ≤ (A g).card

lemma honest_large_selected_subset {N : ℕ} {G : Type*} [DecidableEq G]
    (I : Fin N → Fin N → Prop) [DecidableRel I] (B : Circuit)
    (gs : Finset G) (A : G → Finset (Fin N)) (wire : G → ℕ)
    (hA : ∀ g ∈ gs, A g = Pilot5bMeta1020DeadCover.support B (wire g)) :
    honestLargePairs I gs A ⊆ honestLargeQueryPairs I B := by
  classical
  intro e he
  obtain ⟨_, g, hg, hl, hcover, hlarge⟩ := Finset.mem_filter.mp he
  exact honest_large_query_mem I B (A g) (wire g) (hA g hg) e.1 e.2 hl hcover hlarge

theorem honest_large_selected_bound {N : ℕ} {G : Type*} [DecidableEq G]
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (B : Circuit) (hB : Pilot5bMeta1020DeadCover.good B)
    (hOR : ∀ g ∈ B.gates, g.op = GateOp.or)
    (hI : ∀ p q, p ≠ q → (pencil I p ∩ pencil I q).card ≤ 1)
    (gs : Finset G) (A : G → Finset (Fin N)) (wire : G → ℕ)
    (hA : ∀ g ∈ gs, A g = Pilot5bMeta1020DeadCover.support B (wire g)) :
    (honestLargePairs I gs A).card ≤ 2 * B.size :=
  (Finset.card_le_card (honest_large_selected_subset I B gs A wire hA)).trans
    (honest_large_query_bound I B hB hOR hI)

theorem honest_large_bound_of_witnesses {N : ℕ}
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (B : Circuit) (hB : Pilot5bMeta1020DeadCover.good B)
    (hOR : ∀ g ∈ B.gates, g.op = GateOp.or)
    (hI : ∀ p q, p ≠ q → (pencil I p ∩ pencil I q).card ≤ 1)
    (T : Finset (Fin N × Fin N))
    (hT : ∀ e ∈ T, ∃ w : ℕ,
      e.2 ∈ Pilot5bMeta1020DeadCover.support B w ∧
      Pilot5bMeta1020DeadCover.support B w ⊆ pencil I e.1 ∧
      2 ≤ (Pilot5bMeta1020DeadCover.support (n := N) B w).card) :
    T.card ≤ 2 * B.size := by
  apply (Finset.card_le_card (show T ⊆ honestLargeQueryPairs I B from ?_)).trans
    (honest_large_query_bound I B hB hOR hI)
  intro e he
  exact (mem_honestLargeQueryPairs I B e.1 e.2).mpr (hT e he)

end Pilot5bMeta1020FirstQuery

namespace Pilot5bMeta1020DegreeZeroCover
open PEqualNP.CircuitLowerBounds
def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma gate_inputs {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧
      (∀ r ∈ P, r ∈ (C.gates[w - n]'(by unfold Circuit.size at hw; omega)).inputs) ∧ (∀ r ∈ P, r < w) ∧
      ∀ (x y : Fin n → Bool), (∀ r ∈ P, value C x r = true → value C y r = true) →
        value C x w = true → value C y w = true := by
  let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem _)
  let P := g.inputs.toFinset.filter (· < w)
  refine ⟨P, (Finset.card_filter_le _ _).trans ((List.toFinset_card_le g.inputs).trans hlen), ?_, ?_, ?_⟩
  · exact fun r hr => List.mem_toFinset.mp (Finset.mem_filter.mp hr).1
  · exact fun r hr => (Finset.mem_filter.mp hr).2
  · intro x y hxy hx
    have step (r) (hr : r ∈ g.inputs) :
        (if r < w then value C x r else false) = true →
        (if r < w then value C y r else false) = true := by
      by_cases h : r < w
      · simpa [h] using hxy r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr,h⟩)
      · simp [h]
    have form (z : Fin n → Bool) :
        value C z w = g.op.eval (g.inputs.map fun r => if r < w then value C z r else false) :=
      gate_value C z w hn hw
    rw [form x] at hx
    rw [form y]
    rcases hop with hop|hop
    · simp only [hop, GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hx ⊢
      intro b hb
      obtain ⟨r,hr,rfl⟩ := hb
      exact step r hr (hx _ ⟨r,hr,rfl⟩)
    · simp only [hop, GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hx ⊢
      obtain ⟨b,⟨r,hr,rfl⟩,hv⟩ := hx
      exact ⟨_, ⟨r,hr,rfl⟩, step r hr hv⟩

lemma value_mono {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using hxy p
    by_cases hw : w < n + C.size
    · obtain ⟨P, _, _, hP, hstep⟩ := gate_inputs C hG w (by omega) hw
      exact hstep x y fun r hr => ih r (hP r hr)
    · simp [missing_value C x w (by omega)]

def support {n : ℕ} (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p => value C (fun q => decide (q = p)) w = true)

lemma mem_support {n : ℕ} (C : Circuit) (w : ℕ) (p : Fin n) :
    p ∈ support C w ↔ value C (fun q => decide (q = p)) w = true := by
  simp [support]

lemma support_gate {n : ℕ} (C : Circuit) (w : ℕ) (h : 2 ≤ (support (n := n) C w).card) :
    n ≤ w ∧ w < n + C.size := by
  constructor
  · by_contra! hw
    let p : Fin n := ⟨w, hw⟩
    have hs : support C w ⊆ {p} := by
      intro q hq
      have hv := (mem_support C w q).mp hq
      change value C (fun r => decide (r = q)) p = true at hv
      simpa [input_value, eq_comm] using hv
    have hb := Finset.card_le_card hs
    simp at hb
    omega
  · by_contra! hw
    have hs : support (n := n) C w = ∅ := by
      ext q
      simp [mem_support, missing_value C _ w hw]
    simp [hs] at h

abbrev good (C : Circuit) := ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

def bit {n : ℕ} (A : Finset (Fin n)) (v : Fin n) : Bool := decide (v ∈ A)

def psupport {n : ℕ} (C : Circuit) (P : Finset (Fin n)) (w : ℕ) := support C w ∩ P

noncomputable def kids {n : ℕ} (C : Circuit) (hg : good C) (w : ℕ) : Finset ℕ :=
  if h : n ≤ w ∧ w < n + C.size then (gate_inputs (n := n) C hg w h.1 h.2).choose else ∅

lemma kids_spec {n : ℕ} (C : Circuit) (hg : good C) (w : ℕ) :
    (kids (n := n) C hg w).card ≤ 2 ∧
    (∀ c ∈ kids (n := n) C hg w, c < w) ∧
    (n ≤ w → w < n + C.size → ∀ x y : Fin n → Bool,
      (∀ c ∈ kids (n := n) C hg w, value C x c = true → value C y c = true) →
      value C x w = true → value C y w = true) := by
  unfold kids
  split_ifs with h
  · have hs := (gate_inputs (n := n) C hg w h.1 h.2).choose_spec
    exact ⟨hs.1, hs.2.2.1, fun _ _ => hs.2.2.2⟩
  · exact ⟨by simp, by simp, fun hn hw => (h ⟨hn, hw⟩).elim⟩

lemma differing_child {n : ℕ} (C : Circuit) (hg : good C) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) (x y : Fin n → Bool)
    (hx : value C x w = true) (hy : value C y w = false) :
    ∃ c ∈ kids (n := n) C hg w, value C x c = true ∧ value C y c = false := by
  by_contra! h
  have ht := (kids_spec (n := n) C hg w).2.2 hn hw x y (by
    intro c hc hcx
    exact Bool.eq_true_of_not_eq_false (h c hc hcx)) hx
  simp [hy] at ht

def deadInput {n m : ℕ} (P : Finset (Fin n)) (T : Fin m → Finset (Fin n))
    (S : Finset (Fin m)) : Fin n → Bool := bit (P \ S.biUnion T)

def dead {n m : ℕ} (C : Circuit) (P : Finset (Fin n))
    (T : Fin m → Finset (Fin n)) (d w : ℕ) : Prop :=
  ∃ S : Finset (Fin m), S.card ≤ d ∧ value C (deadInput P T S) w = false

lemma dead_of_false {n m : ℕ} (C : Circuit) (hg : good C) (P : Finset (Fin n))
    (T : Fin m → Finset (Fin n)) (d w : ℕ) (S : Finset (Fin m))
    (hS : S.card ≤ d) (y : Fin n → Bool) (hy : value C y w = false)
    (hcover : ∀ p ∈ P, p ∉ S.biUnion T → y p = true) : dead C P T d w := by
  refine ⟨S, hS, ?_⟩
  apply Bool.eq_false_of_not_eq_true
  intro hpos
  have hm := value_mono C hg (deadInput P T S) y (by
    intro p hp
    have hp' : p ∈ P \ S.biUnion T := of_decide_eq_true hp
    exact hcover p (Finset.mem_sdiff.mp hp').1 (Finset.mem_sdiff.mp hp').2) w hpos
  simp [hy] at hm

lemma alive_covered {n m : ℕ} (C : Circuit) (hg : good C) (P : Finset (Fin n))
    (T : Fin m → Finset (Fin n)) (S : Finset (Fin m)) (w : ℕ)
    (hw : value C (deadInput P T S) w = false) :
    psupport C P w ⊆ S.biUnion T := by
  intro p hp
  by_contra hnot
  have hpos := (mem_support C w p).mp (Finset.mem_inter.mp hp).1
  have hm := value_mono C hg (fun q => decide (q = p)) (deadInput P T S) (by
    intro q hq
    have eq : q = p := of_decide_eq_true hq
    subst q
    simp [deadInput, bit, (Finset.mem_inter.mp hp).2, hnot]) w hpos
  simp [hw] at hm

lemma heavy_lines {n m : ℕ} (C : Circuit) (hg : good C) (P : Finset (Fin n))
    (T : Fin m → Finset (Fin n))
    (hT : ∀ i j, i ≠ j → (T i ∩ T j).card ≤ 1)
    (d w : ℕ) (hw : dead C P T d w) :
    (Finset.univ.filter fun l => d + 1 ≤ (psupport C P w ∩ T l).card).card ≤ d := by
  classical
  obtain ⟨S, hS, hfalse⟩ := hw
  refine (Finset.card_le_card (t := S) ?_).trans hS
  intro l hl
  have hlarge := (Finset.mem_filter.mp hl).2
  by_contra hnot
  have hsub : psupport C P w ∩ T l ⊆ S.biUnion (fun s => T s ∩ T l) := by
    intro p hp
    obtain ⟨s, hs, hps⟩ := Finset.mem_biUnion.mp
      (alive_covered C hg P T S w hfalse (Finset.mem_inter.mp hp).1)
    exact Finset.mem_biUnion.mpr ⟨s, hs, Finset.mem_inter.mpr ⟨hps, (Finset.mem_inter.mp hp).2⟩⟩
  have hb := Finset.card_biUnion_le_card_mul S (fun s => T s ∩ T l) 1 (by
    intro s hs
    exact hT s l (fun h => hnot (h ▸ hs)))
  have hc := Finset.card_le_card hsub
  simp only [mul_one] at hb
  omega

lemma projected_support_gate {n : ℕ} (C : Circuit) (P : Finset (Fin n)) (w : ℕ)
    (h : 2 ≤ (psupport C P w).card) : n ≤ w ∧ w < n + C.size :=
  support_gate C w (h.trans (Finset.card_le_card Finset.inter_subset_left))

lemma charge {n m : ℕ} (C : Circuit) (hg : good C) (P : Finset (Fin n))
    (T : Fin m → Finset (Fin n)) (d : ℕ) (hd : 1 ≤ d)
    (G : Finset ℕ)
    (hdown : ∀ g ∈ G, ∀ c ∈ kids (n := n) C hg g, n ≤ c → c ∈ G)
    (p : Fin n) (l : Fin m) (S : Finset (Fin m)) :
    ∀ w, w ∈ G → p ∈ psupport C P w →
      value C (deadInput P T S) w = false → d + 1 ≤ (psupport C P w ∩ T l).card →
      ∃ g ∈ G, value C (deadInput P T S) g = false ∧
        d + 1 ≤ (psupport C P g ∩ T l).card ∧
        ∃ c ∈ kids (n := n) C hg g, p ∈ psupport C P c ∧
          (psupport C P c ∩ T l).card ≤ d := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hp hfalse hlarge
    have hgate := projected_support_gate C P w (by
      have hle := Finset.card_le_card (Finset.inter_subset_left (s₁ := psupport C P w) (s₂ := T l))
      omega)
    obtain ⟨c, hc, hcpos, hcfalse⟩ := differing_child C hg w hgate.1 hgate.2
      (fun q => decide (q = p)) (deadInput P T S)
      ((mem_support C w p).mp (Finset.mem_inter.mp hp).1) hfalse
    have hpc : p ∈ psupport C P c :=
      Finset.mem_inter.mpr ⟨(mem_support C c p).mpr hcpos, (Finset.mem_inter.mp hp).2⟩
    by_cases hclarge : d + 1 ≤ (psupport C P c ∩ T l).card
    · have hcgate := projected_support_gate C P c (by
        have hle := Finset.card_le_card (Finset.inter_subset_left (s₁ := psupport C P c) (s₂ := T l))
        omega)
      exact ih c ((kids_spec C hg w).2.1 c hc) (hdown w hw c hc hcgate.1) hpc hcfalse hclarge
    · exact ⟨w, hw, hfalse, hlarge, c, hc, hpc, by omega⟩

noncomputable def counted {n m : ℕ} (C : Circuit) (P : Finset (Fin n))
    (T : Fin m → Finset (Fin n)) (G : Finset ℕ) (d : ℕ) : Finset (Fin n × Fin m) := by
  classical
  exact Finset.univ.filter fun e => e.1 ∈ T e.2 ∧ ∃ w ∈ G,
    dead C P T d w ∧ e.1 ∈ psupport C P w ∧ d + 1 ≤ (psupport C P w ∩ T e.2).card

theorem dead_cover_bound {n m : ℕ} (C : Circuit) (hg : good C) (P : Finset (Fin n))
    (T : Fin m → Finset (Fin n))
    (hT : ∀ i j, i ≠ j → (T i ∩ T j).card ≤ 1)
    (d : ℕ) (hd : 1 ≤ d) (G : Finset ℕ)
    (hdown : ∀ g ∈ G, ∀ c ∈ kids (n := n) C hg g, n ≤ c → c ∈ G) :
    (counted C P T G d).card ≤ (2 * d * d) * G.card := by
  classical
  let Lg : ℕ → Finset (Fin m) := fun g => Finset.univ.filter fun l =>
    d + 1 ≤ (psupport C P g ∩ T l).card ∧ dead C P T d g
  let Tc : Fin m → ℕ → Finset (Fin n × Fin m) := fun l c =>
    if (psupport C P c ∩ T l).card ≤ d then
      (psupport C P c ∩ T l).image (fun p => (p, l)) else ∅
  have hLg : ∀ g, (Lg g).card ≤ d := by
    intro g
    by_cases hdead : dead C P T d g
    · have heq : Lg g = Finset.univ.filter (fun l => d + 1 ≤ (psupport C P g ∩ T l).card) := by
        ext l
        simp [Lg, hdead]
      rw [heq]
      exact heavy_lines C hg P T hT d g hdead
    · simp [Lg, hdead]
  have hTc : ∀ l c, (Tc l c).card ≤ d := by
    intro l c
    simp only [Tc]
    split_ifs with h
    · exact Finset.card_image_le.trans h
    · simp
  have hsub : counted C P T G d ⊆ G.biUnion
      (fun g => (Lg g).biUnion (fun l => (kids (n := n) C hg g).biUnion (fun c => Tc l c))) := by
    intro e he
    obtain ⟨_, heT, w, hw, ⟨S, hS, hfalse⟩, hp, hlarge⟩ := Finset.mem_filter.mp he
    obtain ⟨g, hgG, hgfalse, hglarge, c, hc, hpc, hcsmall⟩ :=
      charge C hg P T d hd G hdown e.1 e.2 S w hw hp hfalse hlarge
    refine Finset.mem_biUnion.mpr ⟨g, hgG, Finset.mem_biUnion.mpr
      ⟨e.2, ?_, Finset.mem_biUnion.mpr ⟨c, hc, ?_⟩⟩⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hglarge, S, hS, hgfalse⟩
    · simp only [Tc, ite_eq_left hcsmall, Finset.mem_image]
      exact ⟨e.1, Finset.mem_inter.mpr ⟨hpc, heT⟩, rfl⟩
  refine (Finset.card_le_card hsub).trans ?_
  refine (Finset.card_biUnion_le_card_mul G _ (2 * d * d) ?_).trans (by rw [Nat.mul_comm])
  intro g _
  refine (Finset.card_biUnion_le_card_mul (Lg g) _ (2 * d) ?_).trans ?_
  · intro l _
    refine (Finset.card_biUnion_le_card_mul (kids (n := n) C hg g) _ d (fun c _ => hTc l c)).trans ?_
    exact Nat.mul_le_mul_right d (kids_spec (n := n) C hg g).1
  · have hb := Nat.mul_le_mul_right (2 * d) (hLg g)
    nlinarith

theorem three_line_bound {n m : ℕ} (C : Circuit) (hg : good C) (P : Finset (Fin n))
    (T : Fin m → Finset (Fin n))
    (hT : ∀ i j, i ≠ j → (T i ∩ T j).card ≤ 1)
    (G : Finset ℕ)
    (hdown : ∀ g ∈ G, ∀ c ∈ kids (n := n) C hg g, n ≤ c → c ∈ G) :
    (counted C P T G 3).card ≤ 18 * G.card := by
  simpa using dead_cover_bound C hg P T hT 3 (by omega) G hdown

theorem all_gates_dead_cover_bound {n m : ℕ} (C : Circuit) (hg : good C)
    (P : Finset (Fin n)) (T : Fin m → Finset (Fin n))
    (hT : ∀ i j, i ≠ j → (T i ∩ T j).card ≤ 1) (d : ℕ) (hd : 1 ≤ d) :
    (counted C P T (Finset.Ico n (n + C.size)) d).card ≤ (2 * d * d) * C.size := by
  have hdown : ∀ g ∈ Finset.Ico n (n + C.size),
      ∀ c ∈ kids (n := n) C hg g, n ≤ c → c ∈ Finset.Ico n (n + C.size) := by
    intro g hgG c hc hcn
    have hclt := (kids_spec (n := n) C hg g).2.1 c hc
    exact Finset.mem_Ico.mpr ⟨hcn, lt_trans hclt (Finset.mem_Ico.mp hgG).2⟩
  simpa using dead_cover_bound C hg P T hT d hd (Finset.Ico n (n + C.size)) hdown

theorem all_gates_three_line_bound {n m : ℕ} (C : Circuit) (hg : good C)
    (P : Finset (Fin n)) (T : Fin m → Finset (Fin n))
    (hT : ∀ i j, i ≠ j → (T i ∩ T j).card ≤ 1) :
    (counted C P T (Finset.Ico n (n + C.size)) 3).card ≤ 18 * C.size := by
  simpa using all_gates_dead_cover_bound C hg P T hT 3 (by omega)

lemma kids_actual {n : ℕ} (C : Circuit) (hg : good C) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) (c : ℕ)
    (hc : c ∈ kids (n := n) C hg w) :
    c ∈ (C.gates[w - n]'(by unfold Circuit.size at hw; omega)).inputs := by
  have hh : n ≤ w ∧ w < n + C.size := ⟨hn, hw⟩
  have hs := (gate_inputs (n := n) C hg w hn hw).choose_spec
  have hc' : c ∈ (gate_inputs (n := n) C hg w hn hw).choose := by
    simpa only [kids, dite_eq_left hh] using hc
  exact hs.2.1 c hc'

def drun (gs : List Gate) (d : List ℕ) : List ℕ :=
  gs.foldl (fun d g => d ++ [g.lineDegree d]) d

lemma drun_cons (g : Gate) (gs : List Gate) (d : List ℕ) :
    drun (g :: gs) d = drun gs (d ++ [g.lineDegree d]) := rfl

lemma drun_length (gs : List Gate) (d : List ℕ) :
    (drun gs d).length = d.length + gs.length := by
  induction gs generalizing d with
  | nil => simp [drun]
  | cons g gs ih => rw [drun_cons, ih]; simp; omega

lemma drun_getD (gs : List Gate) (d : List ℕ) (w : ℕ) (hw : w < d.length) :
    (drun gs d).getD w 0 = d.getD w 0 := by
  induction gs generalizing d with
  | nil => rfl
  | cons g gs ih =>
    rw [drun_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma drun_split (gs : List Gate) (d : List ℕ) (j : ℕ) :
    drun gs d = drun (gs.drop j) (drun (gs.take j) d) := by
  simpa only [drun, List.foldl_append] using
    congrArg (fun l : List Gate => drun l d) (List.take_append_drop j gs).symm

lemma le_foldr_max {l : List ℕ} {a : ℕ} (h : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 h with h | h
    · subst h; exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

lemma input_le_lineDegree (g : Gate) (d : List ℕ) (c : ℕ) (hc : c ∈ g.inputs) :
    d.getD c 0 ≤ g.lineDegree d := by
  have hm : d.getD c 0 ∈ g.inputs.map (fun i => d.getD i 0) :=
    List.mem_map.mpr ⟨c, hc, rfl⟩
  unfold Gate.lineDegree
  split_ifs
  · exact List.le_sum_of_mem hm
  · exact le_foldr_max hm

lemma actual_child_degree_le (C : Circuit) (n : ℕ) (marked : Finset ℕ)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size) (c : ℕ)
    (hc : c ∈ (C.gates[w - n]'(by unfold Circuit.size at hw; omega)).inputs)
    (hcw : c < w) :
    (C.lineDegrees n marked).getD c 0 ≤ (C.lineDegrees n marked).getD w 0 := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let initial := (List.range n).map fun i => if i ∈ marked then 1 else 0
  let earlier := drun (C.gates.take j) initial
  have plen : earlier.length = w := by
    simp [earlier, initial, drun_length, Nat.min_eq_left hj.le, j]; omega
  have split : drun C.gates initial = drun (g :: C.gates.drop (j + 1)) earlier := by
    rw [drun_split C.gates initial j, List.drop_eq_getElem_cons hj]
  have hcval : (C.lineDegrees n marked).getD c 0 = earlier.getD c 0 := by
    change (drun C.gates initial).getD c 0 = _
    rw [split]
    exact drun_getD _ earlier c (by simpa only [plen] using hcw)
  have hwval : (C.lineDegrees n marked).getD w 0 = g.lineDegree earlier := by
    change (drun C.gates initial).getD w 0 = _
    rw [split, drun_cons]
    rw [drun_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
    simp only [plen, Nat.sub_self, List.getD_cons_zero]
  rw [hcval, hwval]
  exact input_le_lineDegree g earlier c hc

noncomputable def zeroGates (C : Circuit) (n : ℕ) (marked : Finset ℕ) : Finset ℕ :=
  (Finset.Ico n (n + C.size)).filter fun w => (C.lineDegrees n marked).getD w 0 = 0

lemma zeroGates_down {n : ℕ} (C : Circuit) (hg : good C) (marked : Finset ℕ) :
    ∀ w ∈ zeroGates C n marked, ∀ c ∈ kids (n := n) C hg w,
      n ≤ c → c ∈ zeroGates C n marked := by
  intro w hw c hc hcn
  obtain ⟨hwI, hwz⟩ := Finset.mem_filter.mp hw
  obtain ⟨hwn, hwb⟩ := Finset.mem_Ico.mp hwI
  have hcw := (kids_spec (n := n) C hg w).2.1 c hc
  have hcle := actual_child_degree_le C n marked w hwn hwb c
    (kids_actual C hg w hwn hwb c hc) hcw
  exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hcn, lt_trans hcw hwb⟩, by omega⟩

theorem degree_zero_dead_cover_bound {n m : ℕ} (C : Circuit) (hg : good C)
    (P : Finset (Fin n)) (T : Fin m → Finset (Fin n))
    (hT : ∀ i j, i ≠ j → (T i ∩ T j).card ≤ 1)
    (marked : Finset ℕ) (d : ℕ) (hd : 1 ≤ d) :
    (counted C P T (zeroGates C n marked) d).card ≤
      (2 * d * d) * (zeroGates C n marked).card :=
  dead_cover_bound C hg P T hT d hd (zeroGates C n marked) (zeroGates_down C hg marked)

theorem degree_zero_three_line_bound {n m : ℕ} (C : Circuit) (hg : good C)
    (P : Finset (Fin n)) (T : Fin m → Finset (Fin n))
    (hT : ∀ i j, i ≠ j → (T i ∩ T j).card ≤ 1) (marked : Finset ℕ) :
    (counted C P T (zeroGates C n marked) 3).card ≤
      18 * (zeroGates C n marked).card := by
  simpa using degree_zero_dead_cover_bound C hg P T hT marked 3 (by omega)

end Pilot5bMeta1020DegreeZeroCover

namespace Pilot5bMeta1020LowDegreeCover

open PEqualNP.CircuitLowerBounds
open Pilot5bMeta1020DegreeZeroCover

def lowGates (C : Circuit) (n : ℕ) (marked : Finset ℕ) (k : ℕ) : Finset ℕ :=
  (Finset.Ico n (n + C.size)).filter fun w => (C.lineDegrees n marked).getD w 0 ≤ k

lemma lowGates_down {n : ℕ} (C : Circuit) (hg : good C) (marked : Finset ℕ) (k : ℕ) :
    ∀ w ∈ lowGates C n marked k, ∀ c ∈ kids (n := n) C hg w,
      n ≤ c → c ∈ lowGates C n marked k := by
  intro w hw c hc hcn
  obtain ⟨hwI, hwd⟩ := Finset.mem_filter.mp hw
  obtain ⟨hwn, hwb⟩ := Finset.mem_Ico.mp hwI
  have hcw := (kids_spec (n := n) C hg w).2.1 c hc
  have hcle := actual_child_degree_le C n marked w hwn hwb c
    (kids_actual C hg w hwn hwb c hc) hcw
  exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hcn, lt_trans hcw hwb⟩, hcle.trans hwd⟩

theorem low_degree_three_line_bound {n m : ℕ} (C : Circuit) (hg : good C)
    (P : Finset (Fin n)) (T : Fin m → Finset (Fin n))
    (hT : ∀ i j, i ≠ j → (T i ∩ T j).card ≤ 1) (marked : Finset ℕ) (k : ℕ) :
    (counted C P T (lowGates C n marked k) 3).card ≤
      18 * (lowGates C n marked k).card := by
  simpa using dead_cover_bound C hg P T hT 3 (by omega)
    (lowGates C n marked k) (lowGates_down C hg marked k)

lemma lowGates_one_card (C : Circuit) (n : ℕ) (marked : Finset ℕ) :
    (lowGates C n marked 1).card = (zeroGates C n marked).card +
      ((Finset.Ico n (n + C.size)).filter fun w => (C.lineDegrees n marked).getD w 0 = 1).card := by
  let one := (Finset.Ico n (n + C.size)).filter fun w =>
    (C.lineDegrees n marked).getD w 0 = 1
  have heq : lowGates C n marked 1 = zeroGates C n marked ∪ one := by
    ext w
    simp only [lowGates, zeroGates, one, Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hw, hd⟩
      by_cases h0 : (C.lineDegrees n marked).getD w 0 = 0
      · exact Or.inl ⟨hw, h0⟩
      · exact Or.inr ⟨hw, by omega⟩
    · rintro (⟨hw, hd⟩ | ⟨hw, hd⟩) <;> exact ⟨hw, by omega⟩
  have hd : Disjoint (zeroGates C n marked) one := by
    apply Finset.disjoint_left.mpr
    intro w hw0 hw1
    have h0 := (Finset.mem_filter.mp hw0).2
    have h1 := (Finset.mem_filter.mp hw1).2
    omega
  rw [heq, Finset.card_union_of_disjoint hd]

def pointEmbedding (N : ℕ) : Fin N ↪ Fin (N + N) :=
  ⟨Fin.castAdd N, fun _ _ h => Fin.ext (by simpa using congrArg Fin.val h)⟩

def pointLift {N : ℕ} (S : Finset (Fin N)) : Finset (Fin (N + N)) :=
  S.map (pointEmbedding N)

def pointInputs (N : ℕ) : Finset (Fin (N + N)) := pointLift Finset.univ

def pointLine {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (l : Fin N) : Finset (Fin (N + N)) :=
  pointLift (Finset.univ.filter fun p => I p l)

lemma mem_pointLift_point {N : ℕ} (S : Finset (Fin N)) (p : Fin N) :
    Fin.castAdd N p ∈ pointLift S ↔ p ∈ S := by
  constructor
  · intro hp
    obtain ⟨q, hq, heq⟩ := Finset.mem_map.mp hp
    have hqp : q = p := (pointEmbedding N).injective heq
    simpa only [hqp] using hq
  · intro hp
    exact Finset.mem_map.mpr ⟨p, hp, rfl⟩

lemma not_mem_pointLift_line {N : ℕ} (S : Finset (Fin N)) (l : Fin N) :
    Fin.natAdd N l ∉ pointLift S := by
  intro hl
  obtain ⟨p, _, heq⟩ := Finset.mem_map.mp hl
  have hv := congrArg Fin.val heq
  change p.val = N + l.val at hv
  have := p.isLt
  omega

def pointAlive {N : ℕ} (C : Circuit) (w : ℕ) : Finset (Fin N) :=
  Finset.univ.filter fun p => value C (fun v => decide (v = Fin.castAdd N p)) w = true

lemma ofFn_pointOnly {N : ℕ} (x : Fin N → Bool) :
    List.ofFn (Fin.addCases x (fun _ : Fin N => false)) =
      List.ofFn x ++ List.replicate N false := by
  change List.ofFn (Fin.append x (fun _ : Fin N => false)) = _
  rw [List.ofFn_fin_append]
  simp

lemma pointOnly_singleton {N : ℕ} (p : Fin N) :
    Fin.addCases (fun q => decide (q = p)) (fun _ : Fin N => false) =
      fun v => decide (v = Fin.castAdd N p) := by
  funext v
  by_cases hv : v.val < N
  · let q : Fin N := ⟨v.val, hv⟩
    have heq : v = Fin.castAdd N q := Fin.ext rfl
    rw [heq, Fin.addCases_left]
    congr 1
    exact propext ⟨fun h => congrArg (Fin.castAdd N) h,
      fun h => Fin.ext (congrArg (fun z : Fin (N + N) => z.val) h)⟩
  · let l : Fin N := ⟨v.val - N, by have := v.isLt; omega⟩
    have heq : v = Fin.natAdd N l := Fin.ext (by dsimp [l]; omega)
    rw [heq, Fin.addCases_right]
    have hne : Fin.natAdd N l ≠ Fin.castAdd N p := by
      intro heq
      have hv := congrArg Fin.val heq
      change N + l.val = p.val at hv
      have := p.isLt
      omega
    simp only [hne, decide_false]

lemma mem_pointAlive_list {N : ℕ} (C : Circuit) (w : ℕ) (p : Fin N) :
    p ∈ pointAlive C w ↔
      (C.wires (List.ofFn (fun q : Fin N => decide (q = p)) ++
        List.replicate N false)).getD w false = true := by
  change p ∈ (Finset.univ.filter fun q => value C (fun v => decide (v = Fin.castAdd N q)) w = true) ↔ _
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  change (C.wires (List.ofFn (fun v => decide (v = Fin.castAdd N p)))).getD w false = true ↔ _
  rw [← pointOnly_singleton, ofFn_pointOnly]

lemma pointAlive_lift {N : ℕ} (C : Circuit) (w : ℕ) :
    pointLift (pointAlive C w) = psupport C (pointInputs N) w := by
  ext v
  constructor
  · intro hv
    obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hv
    apply Finset.mem_inter.mpr
    refine ⟨(mem_support C w _).mpr (Finset.mem_filter.mp hp).2, ?_⟩
    exact Finset.mem_map.mpr ⟨p, Finset.mem_univ _, rfl⟩
  · intro hv
    obtain ⟨hs, hp⟩ := Finset.mem_inter.mp hv
    obtain ⟨p, _, rfl⟩ := Finset.mem_map.mp hp
    exact Finset.mem_map.mpr ⟨p, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (mem_support C w _).mp hs⟩, rfl⟩

lemma pointAlive_card {N : ℕ} (C : Circuit) (w : ℕ) :
    (pointAlive (N := N) C w).card = (psupport C (pointInputs N) w).card := by
  rw [← pointAlive_lift]
  exact (Finset.card_map _).symm

lemma pointAlive_line_card {N : ℕ} (C : Circuit) (w : ℕ)
    (I : Fin N → Fin N → Prop) [DecidableRel I] (l : Fin N) :
    ((pointAlive C w).filter fun p => I p l).card =
      (psupport C (pointInputs N) w ∩ pointLine I l).card := by
  rw [← pointAlive_lift]
  change _ = ((pointAlive C w).map (pointEmbedding N) ∩
    (Finset.univ.filter fun p => I p l).map (pointEmbedding N)).card
  rw [← Finset.map_inter, Finset.card_map]
  congr 1
  ext p
  simp

lemma pointLine_linear {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hI : ∀ p q l u, p ≠ q → l ≠ u → ¬ (I p l ∧ I p u ∧ I q l ∧ I q u)) :
    ∀ l u, l ≠ u → (pointLine I l ∩ pointLine I u).card ≤ 1 := by
  intro l u hlu
  unfold pointLine pointLift
  rw [← Finset.map_inter, Finset.card_map, Finset.card_le_one]
  intro p hp q hq
  by_contra hpq
  have hp' : I p l ∧ I p u := by simpa using hp
  have hq' : I q l ∧ I q u := by simpa using hq
  exact hI p q l u hpq hlu ⟨hp'.1, hp'.2, hq'.1, hq'.2⟩

def pointNegative {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (S : Finset (Fin N)) : Fin (N + N) → Bool :=
  Fin.addCases (fun p => decide (∀ l ∈ S, ¬ I p l)) (fun _ => false)

lemma pointNegative_value_list {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (w : ℕ) (S : Finset (Fin N)) :
    value C (pointNegative I S) w =
      (C.wires (List.ofFn (fun p => decide (∀ l ∈ S, ¬ I p l)) ++
        List.replicate N false)).getD w false := by
  change (C.wires (List.ofFn (Fin.addCases (fun p => decide (∀ l ∈ S, ¬ I p l))
    (fun _ : Fin N => false)))).getD w false = _
  rw [ofFn_pointOnly]

lemma pointNegative_eq {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (S : Finset (Fin N)) :
    pointNegative I S = deadInput (pointInputs N) (pointLine I) S := by
  funext v
  refine Fin.addCases ?_ ?_ v
  · intro p
    simp only [pointNegative, Fin.addCases_left, deadInput, bit, Finset.mem_sdiff,
      pointInputs, mem_pointLift_point, Finset.mem_univ, true_and]
    congr 1
    simp only [Finset.mem_biUnion, pointLine, mem_pointLift_point, Finset.mem_filter,
      Finset.mem_univ, true_and, not_exists, not_and]
  · intro l
    simp only [pointNegative, Fin.addCases_right, deadInput, bit, Finset.mem_sdiff,
      pointInputs, not_mem_pointLift_line, false_and, decide_false]

lemma dead_of_pointNegative {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (w : ℕ) (S : Finset (Fin N)) (hS : S.card ≤ 3)
    (hf : value C (pointNegative I S) w = false) :
    dead C (pointInputs N) (pointLine I) 3 w := by
  exact ⟨S, hS, by simpa only [pointNegative_eq] using hf⟩

noncomputable def pointF3 {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) : Finset (Fin N × Fin N) := by
  classical
  exact Finset.univ.filter fun e => I e.1 e.2 ∧ ∃ w,
    (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD w 0 ≤ 1 ∧
    dead C (pointInputs N) (pointLine I) 3 w ∧ e.1 ∈ pointAlive C w ∧
    4 ≤ ((pointAlive C w).filter fun p => I p e.2).card

theorem pointF3_bound {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hI : ∀ p q l u, p ≠ q → l ≠ u → ¬ (I p l ∧ I p u ∧ I q l ∧ I q u))
    (C : Circuit) (hg : good C) :
    (pointF3 I C).card ≤
      18 * (lowGates C (N + N) (Finset.Ico N (N + N)) 1).card := by
  classical
  let f : Fin N × Fin N → Fin (N + N) × Fin N :=
    fun e => (Fin.castAdd N e.1, e.2)
  have hinj : Function.Injective f := by
    intro a b h
    have hp : a.1 = b.1 := (pointEmbedding N).injective (congrArg Prod.fst h)
    have hl : a.2 = b.2 := congrArg (fun z : Fin (N + N) × Fin N => z.2) h
    exact Prod.ext hp hl
  have hsub : (pointF3 I C).image f ⊆ counted C (pointInputs N) (pointLine I)
      (lowGates C (N + N) (Finset.Ico N (N + N)) 1) 3 := by
    intro e he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨_, hIa, w, hwd, hdead, hpa, hlarge⟩ := Finset.mem_filter.mp ha
    have hlarge' : 4 ≤ (psupport C (pointInputs N) w ∩ pointLine I a.2).card := by
      simpa only [pointAlive_line_card] using hlarge
    have hprojected : 2 ≤ (psupport C (pointInputs N) w).card := by
      have hh := Finset.card_le_card (Finset.inter_subset_left
        (s₁ := psupport C (pointInputs N) w) (s₂ := pointLine I a.2))
      omega
    have hgate := projected_support_gate C (pointInputs N) w hprojected
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, w, ?_, hdead, ?_, hlarge'⟩
    · change Fin.castAdd N a.1 ∈ pointLine I a.2
      exact (mem_pointLift_point _ _).mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hIa⟩)
    · exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr hgate, hwd⟩
    · change Fin.castAdd N a.1 ∈ psupport C (pointInputs N) w
      rw [← pointAlive_lift]
      exact (mem_pointLift_point _ _).mpr hpa
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj] at hcard
  exact hcard.trans (low_degree_three_line_bound C hg (pointInputs N) (pointLine I)
    (pointLine_linear I hI) (Finset.Ico N (N + N)) 1)

end Pilot5bMeta1020LowDegreeCover

namespace Pilot5bMeta1020PointLabels

open PEqualNP.CircuitLowerBounds
open Pilot5bMeta1020Linear
open Pilot5bMeta1020DegreeZeroCover
open Pilot5bMeta1020LowDegreeCover

def Z {N : ℕ} (C : Circuit) (a : ℕ) (x : Fin N → Bool) : Bool :=
  (C.wires (List.ofFn x ++ List.replicate N false)).getD a false

lemma Z_eq_value {N : ℕ} (C : Circuit) (a : ℕ) (x : Fin N → Bool) :
    Z C a x = value C (Fin.addCases x (fun _ : Fin N => false)) a := by
  simp only [Z, value, ofFn_pointOnly]

lemma Z_monotone {N : ℕ} (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C) :
    LabelMonotone (Z (N := N) C) := by
  have hg : good C := by
    intro g hg
    obtain ⟨hop, hlen⟩ := hm g hg
    exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hop, hlen⟩
  intro a x x' hxx' hx
  rw [Z_eq_value] at hx ⊢
  apply value_mono C hg _ _ ?_ a hx
  intro v
  refine Fin.addCases ?_ ?_ v
  · intro p
    simpa only [Fin.addCases_left] using hxx' p
  · intro l
    simp only [Fin.addCases_right, Bool.false_eq_true, IsEmpty.forall_iff]

lemma cleaned_false_labelDead3 {N : ℕ} (I : Fin N → Fin N → Prop)
    (L : ℕ → (Fin N → Bool) → Bool) (a : ℕ) (x : Fin N → Bool)
    (hf : cleanedLabels I L a x = false) : labelDead3 I L a := by
  classical
  by_contra hn
  simp [cleanedLabels, hn] at hf

lemma cleaned_eq_of_false {N : ℕ} (I : Fin N → Fin N → Prop)
    (L : ℕ → (Fin N → Bool) → Bool) (a : ℕ) (x₀ : Fin N → Bool)
    (hf : cleanedLabels I L a x₀ = false) (x : Fin N → Bool) :
    cleanedLabels I L a x = L a x := by
  classical
  simp only [cleanedLabels, ite_eq_left (cleaned_false_labelDead3 I L a x₀ hf)]

lemma Z_singleton_support_eq_pointAlive {N : ℕ} (C : Circuit) (a : ℕ) :
    (Finset.univ.filter fun p : Fin N => Z C a (fun q => decide (q = p)) = true) =
      pointAlive C a := by
  apply Finset.ext
  intro p
  constructor
  · intro hp
    exact (mem_pointAlive_list C a p).mpr (Finset.mem_filter.mp hp).2
  · intro hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mem_pointAlive_list C a p).mp hp⟩

lemma cleaned_singleton_support_eq_pointAlive {N : ℕ}
    (I : Fin N → Fin N → Prop) (C : Circuit) (a : ℕ)
    (hα : cleanedLabels I (Z C) a (fun _ => false) = false) :
    (Finset.univ.filter fun p : Fin N =>
      cleanedLabels I (Z C) a (fun q => decide (q = p)) = true) = pointAlive C a := by
  calc
    _ = Finset.univ.filter (fun p : Fin N => Z C a (fun q => decide (q = p)) = true) := by
      apply Finset.filter_congr
      intro p _
      rw [cleaned_eq_of_false I (Z C) a (fun _ => false) hα]
    _ = pointAlive C a := Z_singleton_support_eq_pointAlive C a

lemma labelDead3_dead {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (a : ℕ) (ha : labelDead3 I (Z C) a) :
    dead C (pointInputs N) (pointLine I) 3 a := by
  classical
  obtain ⟨S, hS, hf⟩ := ha
  apply dead_of_pointNegative I C a S hS
  rw [pointNegative_value_list]
  have heq : maxNonneighbors I S = (fun p => decide (∀ l ∈ S, ¬ I p l)) := by
    funext p
    by_cases hp : ∀ l ∈ S, ¬ I p l <;> simp [maxNonneighbors, hp]
  change (C.wires (List.ofFn (maxNonneighbors I S) ++ List.replicate N false)).getD a false = false at hf
  rw [heq] at hf
  exact hf

lemma cleaned_false_dead {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (a : ℕ) (x : Fin N → Bool)
    (hf : cleanedLabels I (Z C) a x = false) :
    dead C (pointInputs N) (pointLine I) 3 a :=
  labelDead3_dead I C a (cleaned_false_labelDead3 I (Z C) a x hf)

lemma cleaned_heavy_mem_pointF3 {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (a : ℕ)
    (ha : (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD a 0 ≤ 1)
    (hα : cleanedLabels I (Z C) a (fun _ => false) = false)
    (p l : Fin N) (hI : I p l)
    (hp : cleanedLabels I (Z C) a (fun q => decide (q = p)) = true)
    (hlarge : 4 ≤ ((Finset.univ.filter fun q : Fin N =>
      cleanedLabels I (Z C) a (fun r => decide (r = q)) = true).filter
        fun q => I q l).card) :
    (p, l) ∈ pointF3 I C := by
  classical
  have heq := cleaned_singleton_support_eq_pointAlive I C a hα
  have hp' : p ∈ pointAlive C a := by
    rw [← heq]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩
  have hlarge' : 4 ≤ ((pointAlive C a).filter fun q => I q l).card := by
    simpa only [heq] using hlarge
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hI, a, ha,
    cleaned_false_dead I C a (fun _ => false) hα, hp', hlarge'⟩

end Pilot5bMeta1020PointLabels

namespace Pilot5bMeta1020LinearTripleBound

open PEqualNP.CircuitLowerBounds Pilot5bMeta1020Linear
open Pilot5bMeta1020FirstQuery

lemma line_inter_bound {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hI : ∀ p q l u, p ≠ q → l ≠ u → ¬ (I p l ∧ I p u ∧ I q l ∧ I q u)) :
    ∀ l u, l ≠ u →
      ((Finset.univ.filter fun p => I p l) ∩ (Finset.univ.filter fun p => I p u)).card ≤ 1 := by
  intro l u hlu
  rw [Finset.card_le_one]
  intro p hp q hq
  by_contra hpq
  have hp' : I p l ∧ I p u := by simpa using hp
  have hq' : I q l ∧ I q u := by simpa using hq
  exact hI p q l u hpq hlu ⟨hp'.1, hp'.2, hq'.1, hq'.2⟩

lemma pencil_inter_bound {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hI : ∀ p q l u, p ≠ q → l ≠ u → ¬ (I p l ∧ I p u ∧ I q l ∧ I q u)) :
    ∀ p q, p ≠ q → (pencil I p ∩ pencil I q).card ≤ 1 := by
  intro p q hpq
  rw [Finset.card_le_one]
  intro l hl u hu
  by_contra hlu
  have hl' : I p l ∧ I q l := by simpa [pencil] using hl
  have hu' : I p u ∧ I q u := by simpa [pencil] using hu
  exact hI p q l u hpq hlu ⟨hl'.1, hu'.1, hl'.2, hu'.2⟩

def eval {N : ℕ} (gs : List Instruction) (L : ℕ → (Fin N → Bool) → Bool)
    (r : ℕ) (X Y : Finset (Fin N)) : Bool :=
  (run gs (fun a => L a (fun p => decide (p ∈ X)))
    (List.ofFn fun l => decide (l ∈ Y))).getD r false

lemma eval_mono {N : ℕ} (gs : List Instruction) (L : ℕ → (Fin N → Bool) → Bool)
    (hL : LabelMonotone L) (r : ℕ) :
    MarkerNearStar.MonoEval (eval gs L r) := by
  intro X X' Y Y' hX hY ht
  exact cleaning_run_mono gs _ _
    (fun a => hL a _ _ (fun p hp => decide_eq_true (hX (of_decide_eq_true hp))))
    _ _ (fun l hl => decide_eq_true (hY (of_decide_eq_true hl))) r ht

lemma row_eval {N : ℕ} (gs : List Instruction) (L : ℕ → (Fin N → Bool) → Bool)
    (r : ℕ) (p l : Fin N) :
    l ∈ Pilot5bMeta1020LinearDAG.row gs L r p ↔ eval gs L r {p} {l} = true := by
  simpa only [Pilot5bMeta1020LinearDAG.row, Pilot5bMeta1020LinearDAG.query,
    eval, Finset.mem_singleton] using
    (wire_singleton gs (fun a => L a (fun q => decide (q = p))) l r).symm

lemma bare_eval {N : ℕ} (gs : List Instruction) (L : ℕ → (Fin N → Bool) → Bool)
    (r : ℕ) (l : Fin N) :
    l ∈ Pilot5bMeta1020LinearDAG.bare gs (fun a => L a (fun _ => false)) r ↔
      eval gs L r ∅ {l} = true := by
  simpa only [Pilot5bMeta1020LinearDAG.bare, Pilot5bMeta1020LinearDAG.query,
    eval, Finset.mem_singleton, Finset.notMem_empty, decide_false] using
    (wire_singleton gs (fun a => L a (fun _ => false)) l r).symm

lemma bare_support {N : ℕ} (gs : List Instruction) (α : ℕ → Bool) (r : ℕ) :
    Pilot5bMeta1020LinearDAG.bare (N := N) gs α r =
      Pilot5bMeta1020DeadCover.support (Pilot5bMeta1020BareCircuit.bareCircuit gs α) r := by
  exact (Pilot5bMeta1020BareCircuit.singleton_support_eq gs α r).symm

theorem clean_linear_triple_bound {N K : ℕ}
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hI : ∀ p q l u, p ≠ q → l ≠ u → ¬ (I p l ∧ I p u ∧ I q l ∧ I q u))
    (gs : List Instruction) (hhead : gs.head? = some (Sum.inl []))
    (hfanin : ∀ rs, Sum.inl rs ∈ gs → rs.length ≤ 2)
    (L : ℕ → (Fin N → Bool) → Bool) (hL : LabelMonotone L)
    (roots : Fin K → Fin 3 → ℕ)
    (hsound : ∀ j, LinearTripleSound I gs L (roots j 0) (roots j 1) (roots j 2))
    (F3 : Finset (Fin N × Fin N)) (P : ℕ) (hF3 : F3.card ≤ 18 * P)
    (hheavy : ∀ g ∈ Pilot5bMeta1020LinearDAG.labelG gs N (fun a => L a (fun _ => false)),
      ∀ l p, p ∈ Pilot5bMeta1020LinearDAG.alive gs L g → I p l →
      4 ≤ ((Pilot5bMeta1020LinearDAG.alive gs L g).filter fun q => I q l).card → (p, l) ∈ F3)
    (E : Finset (Fin N × Fin N))
    (hE : ∀ e ∈ E, I e.1 e.2 ∧ ∃ j, ∀ i,
      (run gs (fun a => L a (fun p => decide (p = e.1)))
        (List.ofFn fun l => decide (l = e.2))).getD (roots j i) false = true) :
    E.card ≤ 18 * P + 28 * gs.length + 27 * K := by
  classical
  let α : ℕ → Bool := fun a => L a (fun _ => false)
  have hα : ∀ a x, α a = true → L a x = true :=
    fun a x => hL a _ x (by simp)
  let S := Pilot5bMeta1020LinearDAG.retained I gs α L
  let O := Pilot5bMeta1020LinearDAG.orG gs N α
  let G := Pilot5bMeta1020LinearDAG.labelG gs N α
  let kids := Pilot5bMeta1020LinearDAG.kids gs N
  let child := Pilot5bMeta1020LinearDAG.child gs N
  let alive := Pilot5bMeta1020LinearDAG.alive gs L
  let bare := Pilot5bMeta1020LinearDAG.bare (N := N) gs α
  let row := Pilot5bMeta1020LinearDAG.row gs L
  let B := Pilot5bMeta1020BareCircuit.bareCircuit gs α
  have hB : Pilot5bMeta1020DeadCover.good B :=
    Pilot5bMeta1020BareCircuit.monotone2 gs α hfanin
  have hOR : ∀ g ∈ B.gates, g.op = GateOp.or := by
    intro g hg
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
    exact Pilot5bMeta1020BareCircuit.bareGate_op α a
  have hsupport (r : ℕ) : bare r = Pilot5bMeta1020DeadCover.support B r := bare_support gs α r
  refine Pilot5bMeta1020TripleCounting.abstract_count I hI (line_inter_bound I hI)
    S O G kids alive (fun g => bare (child g)) bare row
    (Pilot5bMeta1020LinearDAG.kids_card gs N α hfanin)
    (Pilot5bMeta1020LinearDAG.or_lower gs hhead N α) ?_ ?_
    (Pilot5bMeta1020LinearDAG.bare_sub_row gs α L hα)
    (Pilot5bMeta1020LinearDAG.first_origin gs hhead α L hα)
    (Pilot5bMeta1020LinearDAG.retained_origin I gs hhead α L hα)
    (eval gs L) (eval_mono gs L hL) (fun r p u => (row_eval gs L r p u).mp)
    (bare_eval gs L) roots ?_ F3 (honestLargeQueryPairs I B) P gs.length
    hF3 hheavy ?_ ?_ ?_ ?_
    (Pilot5bMeta1020LinearDAG.uncharged_pair_retained I gs hhead α L hα F3) E ?_
  · intro g hg
    ext p
    exact (Pilot5bMeta1020LinearDAG.retained_or_law I gs hhead α L g hg p).trans
      Finset.mem_biUnion.symm
  · intro g hg hn
    have hgl : g ∈ G := by
      by_contra hgl
      have he := Pilot5bMeta1020LinearDAG.retained_other_law I gs α L g hg hgl
      exact hn.ne_empty he
    refine ⟨hgl, ?_⟩
    intro p hp
    exact ((Pilot5bMeta1020LinearDAG.retained_label_law I gs hhead α L g hgl p).mp hp).1
  · intro j X Y hj
    obtain ⟨p, l, hi, hp, hl⟩ := hsound j _ _ (hj 0) (hj 1) (hj 2)
    exact ⟨p, of_decide_eq_true hp, l, of_decide_eq_true hl, hi⟩
  · simpa only [B, Pilot5bMeta1020BareCircuit.size_eq] using
      honest_large_query_bound I B hB hOR (pencil_inter_bound I hI)
  · intro r p l hlarge hcover hl
    apply (mem_honestLargeQueryPairs I B p l).mpr
    refine ⟨r, hsupport r ▸ hl, ?_, hsupport r ▸ hlarge⟩
    intro u hu
    have hu' : u ∈ bare r := (hsupport r).symm ▸ hu
    simpa [pencil] using hcover u hu'
  · simpa only [B, Pilot5bMeta1020BareCircuit.size_eq] using
      own_heavy_bound_of_or I B hB hOR (pencil_inter_bound I hI)
        G (fun g => bare (child g)) child (fun g _ => hsupport (child g))
  · have hc := Pilot5bMeta1020LinearDAG.gate_counts gs N α
    change (Pilot5bMeta1020LinearDAG.labelG gs N α).card +
      (Pilot5bMeta1020LinearDAG.orG gs N α).card ≤ gs.length
    omega
  · intro e he
    obtain ⟨hi, j, hj⟩ := hE e he
    refine ⟨hi, j, ?_⟩
    intro i
    exact (wire_singleton gs (fun a => L a (fun p => decide (p = e.1))) e.2
      (roots j i)).mp (hj i)

theorem linear_triple_bound {N K : ℕ}
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hI : ∀ p q l u, p ≠ q → l ≠ u → ¬ (I p l ∧ I p u ∧ I q l ∧ I q u))
    (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (gs : List Instruction) (hhead : gs.head? = some (Sum.inl []))
    (hfanin : ∀ rs, Sum.inl rs ∈ gs → rs.length ≤ 2)
    (hdegree : ∀ a r, Sum.inr (a, r) ∈ gs →
      (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD a 0 ≤ 1)
    (roots : Fin K → Fin 3 → ℕ)
    (hsound : ∀ j, LinearTripleSound I gs (Pilot5bMeta1020PointLabels.Z C)
      (roots j 0) (roots j 1) (roots j 2))
    (E : Finset (Fin N × Fin N))
    (hE : ∀ e ∈ E, I e.1 e.2 ∧ ∃ j, ∀ i,
      (run gs (fun a => Pilot5bMeta1020PointLabels.Z C a (fun p => decide (p = e.1)))
        (List.ofFn fun l => decide (l = e.2))).getD (roots j i) false = true) :
    E.card ≤
      18 * (Pilot5bMeta1020LowDegreeCover.lowGates C (N + N) (Finset.Ico N (N + N)) 1).card +
      28 * gs.length + 27 * K := by
  classical
  let Z := Pilot5bMeta1020PointLabels.Z (N := N) C
  let L := cleanedLabels I Z
  have hZ : LabelMonotone Z := Pilot5bMeta1020PointLabels.Z_monotone C hC
  have hL : LabelMonotone L := cleanedLabels_mono I Z hZ
  have hg : Pilot5bMeta1020DegreeZeroCover.good C := hC
  refine clean_linear_triple_bound I hI gs hhead hfanin L hL roots
    (fun j => cleaned_triple_sound I gs Z hZ (roots j 0) (roots j 1) (roots j 2) (hsound j))
    (Pilot5bMeta1020LowDegreeCover.pointF3 I C) _
    (Pilot5bMeta1020LowDegreeCover.pointF3_bound I hI C hg) ?_ E ?_
  · intro g hgl l p hp hi hlarge
    obtain ⟨hgI, hkind⟩ := Finset.mem_filter.mp hgl
    obtain ⟨hgn, hgb⟩ := Finset.mem_Ico.mp hgI
    cases hgate : Pilot5bMeta1020LinearDAG.gateAt gs N g with
    | inl rs => simp [Pilot5bMeta1020LinearDAG.IsLabel, hgate] at hkind
    | inr ar =>
      rcases ar with ⟨a, r⟩
      have hmem : Sum.inr (a, r) ∈ gs := by
        rw [← hgate]
        exact Pilot5bMeta1020LinearDAG.gateAt_mem gs N g hgn hgb
      have hfalse : L a (fun _ => false) = false := by
        simpa only [Pilot5bMeta1020LinearDAG.IsLabel, hgate] using hkind
      apply Pilot5bMeta1020PointLabels.cleaned_heavy_mem_pointF3 I C a
        (hdegree a r hmem) hfalse p l hi
      · simpa only [Pilot5bMeta1020LinearDAG.alive, Pilot5bMeta1020LinearDAG.labelID,
          hgate, Finset.mem_filter, Finset.mem_univ, true_and] using hp
      · simpa only [Pilot5bMeta1020LinearDAG.alive, Pilot5bMeta1020LinearDAG.labelID,
          hgate] using hlarge
  · intro e he
    obtain ⟨hi, j, hj⟩ := hE e he
    refine ⟨hi, j, ?_⟩
    intro i
    exact cleaned_wire_preserved I gs Z _ _ (roots j i) (hj i)

end Pilot5bMeta1020LinearTripleBound




namespace Pilot5bMeta1020Forward

open PEqualNP.CircuitLowerBounds
open Pilot5bMeta1020Linear

abbrev State := List Instruction × (List ℕ × List ℕ)

def net (s : State) : List Instruction := s.1
def one (s : State) : List ℕ := s.2.1
def degrees (s : State) : List ℕ := s.2.2

def initial (N : ℕ) : State :=
  ([Sum.inl []],
    (List.replicate N N ++ List.range N,
     List.replicate N 0 ++ List.replicate N 1))

def labelRead (zeroLabel : ℕ) (s : State) (r : ℕ) : ℕ :=
  if r < (one s).length then r else zeroLabel

def payload (N zeroLabel : ℕ) (s : State) (g : Gate) : List Instruction :=
  let d := g.lineDegree (degrees s)
  let a := fun r => (one s).getD r N
  let z := labelRead zeroLabel s
  if d = 1 ∨ d = 2 then
    match g.op, g.inputs with
    | .or, rs => [Sum.inl (rs.map a)]
    | .and, [r] => [Sum.inl [a r]]
    | .and, [r, t] =>
        if (degrees s).getD r 0 = 1 ∧ (degrees s).getD t 0 = 1 then
          [Sum.inr (z r, a t), Sum.inr (z t, a r),
            Sum.inl [N + (net s).length, N + (net s).length + 1]]
        else if (degrees s).getD r 0 = 0 then [Sum.inr (z r, a t)]
        else if (degrees s).getD t 0 = 0 then [Sum.inr (z t, a r)]
        else []
    | _, _ => []
  else []

def out (N zeroLabel : ℕ) (s : State) (g : Gate) : ℕ :=
  let ps := payload N zeroLabel s g
  if ps = [] then N else N + (net s).length + ps.length - 1

def advance (N zeroLabel : ℕ) (s : State) (g : Gate) : State :=
  (net s ++ payload N zeroLabel s g,
    (one s ++ [out N zeroLabel s g],
     degrees s ++ [g.lineDegree (degrees s)]))

def build (N zeroLabel : ℕ) (gs : List Gate) : State :=
  gs.foldl (advance N zeroLabel) (initial N)

def normalize (N : ℕ) (C : Circuit) : State :=
  build N (N + N + C.size) C.gates

def forwardWeight (s : State) (g : Gate) : ℕ :=
  let d := g.lineDegree (degrees s)
  if d = 1 then 1 else if d = 2 then
    match g.op, g.inputs with
    | .and, [r, t] =>
      if (degrees s).getD r 0 = 1 ∧ (degrees s).getD t 0 = 1 then 3 else 1
    | _, _ => 1
  else 0

lemma advance_net (N z : ℕ) (s : State) (g : Gate) :
    net (advance N z s g) = net s ++ payload N z s g := rfl

lemma advance_one (N z : ℕ) (s : State) (g : Gate) :
    one (advance N z s g) = one s ++ [out N z s g] := rfl

lemma advance_degrees (N z : ℕ) (s : State) (g : Gate) :
    degrees (advance N z s g) = degrees s ++ [g.lineDegree (degrees s)] := rfl

lemma payload_length_le_three (N z : ℕ) (s : State) (g : Gate) :
    (payload N z s g).length ≤ 3 := by
  unfold payload
  dsimp only
  split_ifs
  all_goals try split
  all_goals try split_ifs
  all_goals simp_all

lemma payload_length_le_weight (N z : ℕ) (s : State) (g : Gate) :
    (payload N z s g).length ≤ forwardWeight s g := by
  unfold payload forwardWeight
  dsimp only
  split_ifs
  all_goals try split
  all_goals try split_ifs
  all_goals simp_all [Gate.lineDegree]

lemma weight_le_three (s : State) (g : Gate) : forwardWeight s g ≤ 3 := by
  unfold forwardWeight
  dsimp only
  split_ifs
  all_goals try split
  all_goals try split_ifs
  all_goals omega

lemma build_one_length (N z : ℕ) (gs : List Gate) :
    (one (build N z gs)).length = N + N + gs.length := by
  have hgen : ∀ (s : State),
      (one (gs.foldl (advance N z) s)).length = (one s).length + gs.length := by
    induction gs with
    | nil => intro s; simp
    | cons g gs ih =>
      intro s
      rw [List.foldl_cons, ih, advance_one]
      simp
      omega
  simpa [build, initial, one, List.length_replicate, List.length_range, Nat.add_assoc]
    using hgen (initial N)

lemma build_degrees_length (N z : ℕ) (gs : List Gate) :
    (degrees (build N z gs)).length = N + N + gs.length := by
  have hgen : ∀ (s : State),
      (degrees (gs.foldl (advance N z) s)).length = (degrees s).length + gs.length := by
    induction gs with
    | nil => intro s; simp
    | cons g gs ih =>
      intro s
      rw [List.foldl_cons, ih, advance_degrees]
      simp
      omega
  simpa [build, initial, degrees, List.length_replicate, Nat.add_assoc]
    using hgen (initial N)

lemma build_net_length (N z : ℕ) (gs : List Gate) :
    (net (build N z gs)).length ≤ 1 + 3 * gs.length := by
  have hgen : ∀ (s : State),
      (net (gs.foldl (advance N z) s)).length ≤ (net s).length + 3 * gs.length := by
    induction gs with
    | nil => intro s; simp
    | cons g gs ih =>
      intro s
      rw [List.foldl_cons]
      have h := ih (advance N z s g)
      rw [advance_net, List.length_append] at h
      have hp := payload_length_le_three N z s g
      simp only [List.length_cons]
      omega
  simpa [build, initial, net] using hgen (initial N)

def coefficient (g : Gate) (Z P : ℕ → Bool) : Bool :=
  match g.op, g.inputs with
  | .or, rs => (rs.map P).any id
  | .and, [] => false
  | .and, [r] => P r
  | .and, [r, t] => (Z r && P t) || (P r && Z t)
  | _, _ => false

lemma coefficient_congr (g : Gate) (Z P Z' P' : ℕ → Bool)
    (hZ : ∀ r ∈ g.inputs, Z r = Z' r)
    (hP : ∀ r ∈ g.inputs, P r = P' r) :
    coefficient g Z P = coefficient g Z' P' := by
  rcases g with ⟨op, rs⟩
  cases op with
  | or =>
    simp only [coefficient]
    congr 1
    apply List.map_congr_left
    intro r hr
    exact hP r hr
  | and =>
    cases rs with
    | nil => rfl
    | cons r rs =>
      cases rs with
      | nil => exact hP r (by simp)
      | cons t rs =>
        cases rs with
        | nil =>
          simp only [coefficient]
          rw [hZ r (by simp), hZ t (by simp), hP r (by simp), hP t (by simp)]
        | cons u rs => rfl
  | not => rfl
  | mod n => rfl
  | maj => rfl

lemma coefficient_zero_of_children (g : Gate) (Z P : ℕ → Bool)
    (hP : ∀ r ∈ g.inputs, P r = false) : coefficient g Z P = false := by
  have heq := coefficient_congr g Z P Z (fun _ => false)
    (fun _ _ => rfl) hP
  rw [heq]
  rcases g with ⟨op, rs⟩
  cases op with
  | or => simp [coefficient]
  | and =>
    cases rs with
    | nil => rfl
    | cons r rs =>
      cases rs with
      | nil => rfl
      | cons t rs => cases rs <;> simp [coefficient]
  | not => rfl
  | mod n => rfl
  | maj => rfl

lemma run_one_read (g : Instruction) (labels : ℕ → Bool) (v : List Bool) :
    (run [g] labels v).getD v.length false = step labels v g := by
  simpa [run] using snoc_read_new [] g labels v

lemma run_two_labels_or (labels : ℕ → Bool) (v : List Bool)
    (a b c d : ℕ) (hb : b < v.length) (hd : d < v.length) :
    (run [Sum.inr (a, b), Sum.inr (c, d),
      Sum.inl [v.length, v.length + 1]] labels v).getD (v.length + 2) false =
      ((labels a && v.getD b false) || (labels c && v.getD d false)) := by
  have hlast := snoc_read_new [Sum.inr (a, b), Sum.inr (c, d)]
    (Sum.inl [v.length, v.length + 1]) labels v
  have hfirst := snoc_read_old [Sum.inr (a, b)] (Sum.inr (c, d)) labels v
    v.length (by simp)
  have hsecond := snoc_read_new [Sum.inr (a, b)] (Sum.inr (c, d)) labels v
  have hbase := run_one_read (Sum.inr (a, b)) labels v
  have hold := run_getD_lt [Sum.inr (a, b)] labels v d hd
  simp only [List.length_cons, List.length_nil, Nat.add_zero, Nat.zero_add,
    List.cons_append, List.nil_append] at hlast hfirst hsecond
  change (run [Sum.inr (a, b), Sum.inr (c, d),
    Sum.inl [v.length, v.length + 1]] labels v).getD (v.length + 2) false = _ at hlast
  rw [hlast]
  simp only [step, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
    id_eq, Bool.or_false] at hfirst hsecond hbase ⊢
  rw [hfirst, hbase, hsecond, hold]

lemma payload_value (N zeroLabel : ℕ) (s : State) (g : Gate)
    (labels : ℕ → Bool) (v : List Bool)
    (hlen : v.length = N + (net s).length)
    (hfalse : v.getD N false = false)
    (hN : N < v.length)
    (hmap : ∀ r, (one s).getD r N < v.length)
    (hzero : ∀ r, (degrees s).getD r 0 = 0 →
      v.getD ((one s).getD r N) false = false)
    (hmono : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hfan : g.inputs.length ≤ 2) :
    (run (payload N zeroLabel s g) labels v).getD (out N zeroLabel s g) false =
      if g.lineDegree (degrees s) = 1 ∨ g.lineDegree (degrees s) = 2 then
        coefficient g (fun r => labels (labelRead zeroLabel s r))
          (fun r => v.getD ((one s).getD r N) false)
      else false := by
  classical
  by_cases hdeg : g.lineDegree (degrees s) = 1 ∨ g.lineDegree (degrees s) = 2
  · rw [if_pos hdeg]
    rcases g with ⟨op, rs⟩
    rcases hmono with hop | hop <;> dsimp only at hop hfan <;> subst op
    · cases rs with
      | nil => simp [Gate.lineDegree] at hdeg
      | cons r rs =>
        cases rs with
        | nil =>
          have hp : payload N zeroLabel s ⟨.and, [r]⟩ =
              [Sum.inl [(one s).getD r N]] := by
            simp only [payload, hdeg, ↓reduceIte]
          rw [show out N zeroLabel s ⟨.and, [r]⟩ = v.length by
            simp only [out, hp, List.cons_ne_nil, ↓reduceIte,
              List.length_cons, List.length_nil]
            omega]
          rw [hp, run_one_read]
          simp only [step, coefficient, List.map_cons, List.map_nil,
            List.any_cons, List.any_nil, id_eq, Bool.or_false]
        | cons t rs =>
          cases rs with
          | cons u rs => simp at hfan
          | nil =>
            have hd : (degrees s).getD r 0 + (degrees s).getD t 0 = 1 ∨
                (degrees s).getD r 0 + (degrees s).getD t 0 = 2 := by
              simpa [Gate.lineDegree] using hdeg
            by_cases hf : (degrees s).getD r 0 = 1 ∧ (degrees s).getD t 0 = 1
            · have hp : payload N zeroLabel s ⟨.and, [r, t]⟩ =
                  [Sum.inr (labelRead zeroLabel s r, (one s).getD t N),
                   Sum.inr (labelRead zeroLabel s t, (one s).getD r N),
                   Sum.inl [v.length, v.length + 1]] := by
                simp only [payload, hdeg, ↓reduceIte, hf, hlen] <;> simp
              rw [show out N zeroLabel s ⟨.and, [r, t]⟩ = v.length + 2 by
                simp only [out, hp, List.cons_ne_nil, ↓reduceIte,
                  List.length_cons, List.length_nil]
                omega]
              rw [hp, run_two_labels_or labels v _ _ _ _ (hmap t) (hmap r)]
              simp [coefficient, Bool.and_comm]
            · have hz : (degrees s).getD r 0 = 0 ∨ (degrees s).getD t 0 = 0 := by omega
              rcases hz with hz | hz
              · have hp : payload N zeroLabel s ⟨.and, [r, t]⟩ =
                    [Sum.inr (labelRead zeroLabel s r, (one s).getD t N)] := by
                  simp only [payload, hdeg, ↓reduceIte, hf, hz] <;> simp
                rw [show out N zeroLabel s ⟨.and, [r, t]⟩ = v.length by
                  simp only [out, hp, List.cons_ne_nil, ↓reduceIte,
                    List.length_cons, List.length_nil]
                  omega]
                rw [hp, run_one_read]
                simp only [step, coefficient]
                rw [hzero r hz]
                simp
              · have hr : (degrees s).getD r 0 ≠ 0 := by omega
                have hp : payload N zeroLabel s ⟨.and, [r, t]⟩ =
                    [Sum.inr (labelRead zeroLabel s t, (one s).getD r N)] := by
                  simp only [payload, hdeg, ↓reduceIte, hf, hr, hz] <;> simp
                rw [show out N zeroLabel s ⟨.and, [r, t]⟩ = v.length by
                  simp only [out, hp, List.cons_ne_nil, ↓reduceIte,
                    List.length_cons, List.length_nil]
                  omega]
                rw [hp, run_one_read]
                simp only [step, coefficient]
                rw [hzero t hz]
                simp [Bool.and_comm]
    · have hp : payload N zeroLabel s ⟨.or, rs⟩ =
          [Sum.inl (rs.map fun r => (one s).getD r N)] := by
        simp only [payload, hdeg, ↓reduceIte]
      rw [show out N zeroLabel s ⟨.or, rs⟩ = v.length by
        simp only [out, hp, List.cons_ne_nil, ↓reduceIte,
          List.length_cons, List.length_nil]
        omega]
      rw [hp, run_one_read]
      simp [step, coefficient, List.map_map, Function.comp_def]
  · simpa only [payload, out, hdeg, ↓reduceIte, run, List.foldl_nil] using hfalse

lemma advance_correct (N zeroLabel : ℕ) (s : State) (g : Gate)
    (labels : ℕ → Bool) (v P : List Bool)
    (hlen : v.length = N + (net s).length)
    (hdlen : (degrees s).length = (one s).length)
    (hplen : P.length = (one s).length)
    (hfalse : v.getD N false = false)
    (hN : N < v.length)
    (hmap : ∀ r, (one s).getD r N < v.length)
    (hzero : ∀ r, (degrees s).getD r 0 = 0 →
      v.getD ((one s).getD r N) false = false)
    (hold : ∀ r, (degrees s).getD r 0 ≤ 2 →
      v.getD ((one s).getD r N) false = P.getD r false)
    (hchild : ∀ r ∈ g.inputs, (degrees s).getD r 0 ≤ g.lineDegree (degrees s))
    (hmono : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hfan : g.inputs.length ≤ 2) :
    ∀ r, (degrees (advance N zeroLabel s g)).getD r 0 ≤ 2 →
      (run (payload N zeroLabel s g) labels v).getD
          ((one (advance N zeroLabel s g)).getD r N) false =
        (P ++ [coefficient g (fun t => labels (labelRead zeroLabel s t))
          (fun t => P.getD t false)]).getD r false := by
  intro r hr
  by_cases hlt : r < (one s).length
  · have hd : (degrees (advance N zeroLabel s g)).getD r 0 =
        (degrees s).getD r 0 := by
      rw [advance_degrees, List.getD_append _ _ _ _ (by omega)]
    rw [hd] at hr
    rw [advance_one, List.getD_append _ _ _ _ hlt,
      run_getD_lt _ _ _ _ (hmap r), List.getD_append _ _ _ _ (by omega)]
    exact hold r hr
  · by_cases heq : r = (one s).length
    · subst r
      have hd : (degrees (advance N zeroLabel s g)).getD (one s).length 0 =
          g.lineDegree (degrees s) := by
        rw [advance_degrees, List.getD_append_right _ _ _ _ (by omega)]
        simp only [hdlen, Nat.sub_self, List.getD_cons_zero]
      rw [hd] at hr
      rw [advance_one, List.getD_append_right _ _ _ _ (by omega)]
      simp only [Nat.sub_self, List.getD_cons_zero]
      rw [List.getD_append_right _ _ _ _ (by omega)]
      simp only [hplen, Nat.sub_self, List.getD_cons_zero]
      rw [payload_value N zeroLabel s g labels v hlen hfalse hN hmap hzero hmono hfan]
      by_cases hz : g.lineDegree (degrees s) = 0
      · have hc : coefficient g (fun t => labels (labelRead zeroLabel s t))
            (fun t => P.getD t false) = false := by
          apply coefficient_zero_of_children
          intro t ht
          have hdt : (degrees s).getD t 0 = 0 := by
            have := hchild t ht
            omega
          rw [← hold t (by omega), hzero t hdt]
        rw [hz, hc]
        simp
      · have hp : g.lineDegree (degrees s) = 1 ∨ g.lineDegree (degrees s) = 2 := by omega
        rw [if_pos hp]
        apply coefficient_congr
        · intro t ht; rfl
        · intro t ht
          exact hold t ((hchild t ht).trans hr)
    · have hge : (one s).length + 1 ≤ r := by omega
      have hm : (one (advance N zeroLabel s g)).getD r N = N := by
        apply List.getD_eq_default
        simp only [advance_one, List.length_append, List.length_singleton]
        exact hge
      have hp : (P ++ [coefficient g (fun t => labels (labelRead zeroLabel s t))
          (fun t => P.getD t false)]).getD r false = false := by
        apply List.getD_eq_default
        simp only [List.length_append, List.length_singleton, hplen]
        exact hge
      rw [hm, hp, run_getD_lt _ _ _ _ hN, hfalse]

end Pilot5bMeta1020Forward

namespace Pilot5bMeta1020Forward

open PEqualNP.CircuitLowerBounds
open Pilot5bMeta1020Linear

lemma fold_degrees (N z : ℕ) (gs : List Gate) (s : State) :
    degrees (gs.foldl (advance N z) s) =
      gs.foldl (fun d g => d ++ [g.lineDegree d]) (degrees s) := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih, advance_degrees]
    rfl

lemma build_degrees_eq (N z : ℕ) (gs : List Gate) :
    degrees (build N z gs) = gs.foldl (fun d g => d ++ [g.lineDegree d])
      (List.replicate N 0 ++ List.replicate N 1) := by
  exact fold_degrees N z gs (initial N)

lemma initial_degrees_eq (N : ℕ) :
    degrees (initial N) =
      (List.range (N + N)).map (fun i => if i ∈ Finset.Ico N (N + N) then 1 else 0) := by
  change List.replicate N 0 ++ List.replicate N 1 = _
  rw [List.range_add, List.map_append, List.map_map]
  have hleft : (List.range N).map (fun i => if i ∈ Finset.Ico N (N + N) then 1 else 0) =
      List.replicate N 0 := by
    have h : (List.range N).map (fun i => if i ∈ Finset.Ico N (N + N) then 1 else 0) =
        (List.range N).map (fun _ => 0) := by
      apply List.map_congr_left
      intro i hi
      have hi' := List.mem_range.mp hi
      simp only [Finset.mem_Ico]
      split_ifs <;> omega
    simpa using h
  have hright : (List.range N).map
      ((fun i => if i ∈ Finset.Ico N (N + N) then 1 else 0) ∘ (fun i => N + i)) =
      List.replicate N 1 := by
    have h : (List.range N).map
        ((fun i => if i ∈ Finset.Ico N (N + N) then 1 else 0) ∘ (fun i => N + i)) =
        (List.range N).map (fun _ => 1) := by
      apply List.map_congr_left
      intro i hi
      have hi' := List.mem_range.mp hi
      simp only [Function.comp_apply, Finset.mem_Ico]
      split_ifs <;> omega
    simpa using h
  rw [hleft, hright]

lemma normalize_degrees_eq (N : ℕ) (C : Circuit) :
    degrees (normalize N C) = C.lineDegrees (N + N) (Finset.Ico N (N + N)) := by
  rw [normalize, build, fold_degrees, initial_degrees_eq]
  rfl

lemma fold_net_append (N z : ℕ) (gs : List Gate) (s : State) :
    ∃ t, net (gs.foldl (advance N z) s) = net s ++ t := by
  induction gs generalizing s with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨t, ht⟩ := ih (advance N z s g)
    refine ⟨payload N z s g ++ t, ?_⟩
    rw [List.foldl_cons, ht, advance_net, List.append_assoc]

lemma fold_one_append (N z : ℕ) (gs : List Gate) (s : State) :
    ∃ t, one (gs.foldl (advance N z) s) = one s ++ t ∧ t.length = gs.length := by
  induction gs generalizing s with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    obtain ⟨t, ht, hl⟩ := ih (advance N z s g)
    refine ⟨out N z s g :: t, ?_, by simp [hl]⟩
    rw [List.foldl_cons, ht, advance_one]
    simp only [List.append_assoc, List.singleton_append]

lemma fold_degrees_append (N z : ℕ) (gs : List Gate) (s : State) :
    ∃ t, degrees (gs.foldl (advance N z) s) = degrees s ++ t ∧ t.length = gs.length := by
  induction gs generalizing s with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    obtain ⟨t, ht, hl⟩ := ih (advance N z s g)
    refine ⟨g.lineDegree (degrees s) :: t, ?_, by simp [hl]⟩
    rw [List.foldl_cons, ht, advance_degrees]
    simp only [List.append_assoc, List.singleton_append]

lemma fold_one_getD_old (N z : ℕ) (gs : List Gate) (s : State) (r d : ℕ)
    (hr : r < (one s).length) :
    (one (gs.foldl (advance N z) s)).getD r d = (one s).getD r d := by
  obtain ⟨t, ht, _⟩ := fold_one_append N z gs s
  rw [ht, List.getD_append _ _ _ _ hr]

lemma fold_degrees_getD_old (N z : ℕ) (gs : List Gate) (s : State) (r d : ℕ)
    (hr : r < (degrees s).length) :
    (degrees (gs.foldl (advance N z) s)).getD r d = (degrees s).getD r d := by
  obtain ⟨t, ht, _⟩ := fold_degrees_append N z gs s
  rw [ht, List.getD_append _ _ _ _ hr]

lemma build_append (N z : ℕ) (gs hs : List Gate) :
    build N z (gs ++ hs) = hs.foldl (advance N z) (build N z gs) := by
  simp only [build, List.foldl_append]

lemma build_snoc (N z : ℕ) (gs : List Gate) (g : Gate) :
    build N z (gs ++ [g]) = advance N z (build N z gs) g := by
  rw [build_append]
  rfl

lemma build_one_getD_prefix (N z : ℕ) (gs hs : List Gate) (r d : ℕ)
    (hr : r < N + N + gs.length) :
    (one (build N z (gs ++ hs))).getD r d = (one (build N z gs)).getD r d := by
  rw [build_append]
  apply fold_one_getD_old
  simpa only [build_one_length] using hr

lemma build_degrees_getD_prefix (N z : ℕ) (gs hs : List Gate) (r d : ℕ)
    (hr : r < N + N + gs.length) :
    (degrees (build N z (gs ++ hs))).getD r d = (degrees (build N z gs)).getD r d := by
  rw [build_append]
  apply fold_degrees_getD_old
  simpa only [build_degrees_length] using hr

lemma build_net_false_prefix (N z : ℕ) (gs : List Gate) :
    ∃ t, net (build N z gs) = Sum.inl [] :: t := by
  obtain ⟨t, ht⟩ := fold_net_append N z gs (initial N)
  exact ⟨t, by simpa only [build, initial, net, List.singleton_append] using ht⟩

lemma build_net_pos (N z : ℕ) (gs : List Gate) : 0 < (net (build N z gs)).length := by
  obtain ⟨t, ht⟩ := build_net_false_prefix N z gs
  simp [ht]

def OneBound (N : ℕ) (s : State) : Prop :=
  ∀ r ∈ one s, r < N + (net s).length

lemma initial_one_bound (N : ℕ) : OneBound N (initial N) := by
  intro r hr
  change r ∈ List.replicate N N ++ List.range N at hr
  change r < N + 1
  rcases List.mem_append.mp hr with h | h
  · have hrN := List.eq_of_mem_replicate h
    omega
  · have hrN := List.mem_range.mp h
    omega

lemma out_bound (N z : ℕ) (s : State) (g : Gate) (hs : 0 < (net s).length) :
    out N z s g < N + (net (advance N z s g)).length := by
  rw [advance_net, List.length_append]
  unfold out
  dsimp only
  split_ifs with h
  · simp only [h, List.length_nil]
    omega
  · have hp : 0 < (payload N z s g).length := List.length_pos_iff.mpr h
    omega

lemma advance_one_bound (N z : ℕ) (s : State) (g : Gate)
    (hs : 0 < (net s).length) (hb : OneBound N s) : OneBound N (advance N z s g) := by
  intro r hr
  rw [advance_one, List.mem_append, List.mem_singleton] at hr
  rcases hr with hr | rfl
  · have h := hb r hr
    rw [advance_net, List.length_append]
    omega
  · exact out_bound N z s g hs

lemma fold_net_pos (N z : ℕ) (gs : List Gate) (s : State)
    (hs : 0 < (net s).length) : 0 < (net (gs.foldl (advance N z) s)).length := by
  obtain ⟨t, ht⟩ := fold_net_append N z gs s
  rw [ht, List.length_append]
  omega

lemma fold_one_bound (N z : ℕ) (gs : List Gate) (s : State)
    (hs : 0 < (net s).length) (hb : OneBound N s) :
    OneBound N (gs.foldl (advance N z) s) := by
  induction gs generalizing s with
  | nil => exact hb
  | cons g gs ih =>
    rw [List.foldl_cons]
    apply ih
    · rw [advance_net, List.length_append]
      omega
    · exact advance_one_bound N z s g hs hb

lemma build_one_bound (N z : ℕ) (gs : List Gate) : OneBound N (build N z gs) :=
  fold_one_bound N z gs (initial N) (by simp [initial, net]) (initial_one_bound N)

lemma getD_bound_of_mem (xs : List ℕ) (d b : ℕ)
    (hm : ∀ r ∈ xs, r < b) (hd : d < b) (r : ℕ) : xs.getD r d < b := by
  induction xs generalizing r with
  | nil => simpa using hd
  | cons a xs ih =>
    cases r with
    | zero => exact hm a (by simp)
    | succ r =>
      exact ih (fun t ht => hm t (by simp [ht])) r

lemma build_one_getD_bound (N z : ℕ) (gs : List Gate) (r : ℕ) :
    (one (build N z gs)).getD r N < N + (net (build N z gs)).length := by
  apply getD_bound_of_mem
  · exact build_one_bound N z gs
  · have h := build_net_pos N z gs
    omega

lemma normalize_one_getD_bound (N : ℕ) (C : Circuit) (r : ℕ) :
    (one (normalize N C)).getD r N < N + (net (normalize N C)).length :=
  build_one_getD_bound N (N + N + C.size) C.gates r

lemma initial_one_point (N p : ℕ) (hp : p < N) :
    (one (initial N)).getD p N = N := by
  change (List.replicate N N ++ List.range N).getD p N = N
  rw [List.getD_append _ _ _ _ (by simpa using hp)]
  exact List.getD_replicate N hp

lemma initial_one_line (N l : ℕ) (hl : l < N) :
    (one (initial N)).getD (N + l) N = l := by
  change (List.replicate N N ++ List.range N).getD (N + l) N = l
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_replicate, Nat.add_sub_cancel_left]
  rw [List.getD_eq_getElem _ _ (by simpa using hl)]
  exact List.getElem_range _

lemma build_one_point (N z : ℕ) (gs : List Gate) (p : ℕ) (hp : p < N) :
    (one (build N z gs)).getD p N = N := by
  change (one (gs.foldl (advance N z) (initial N))).getD p N = N
  rw [fold_one_getD_old N z gs (initial N) p N (by simp [initial, one]; omega)]
  exact initial_one_point N p hp

lemma build_one_line (N z : ℕ) (gs : List Gate) (l : ℕ) (hl : l < N) :
    (one (build N z gs)).getD (N + l) N = l := by
  change (one (gs.foldl (advance N z) (initial N))).getD (N + l) N = l
  rw [fold_one_getD_old N z gs (initial N) (N + l) N (by simp [initial, one]; omega)]
  exact initial_one_line N l hl

lemma labelRead_of_lt (z : ℕ) (s : State) (r : ℕ) (hr : r < (one s).length) :
    labelRead z s r = r := by simp [labelRead, hr]

lemma labelRead_of_ge (z : ℕ) (s : State) (r : ℕ) (hr : (one s).length ≤ r) :
    labelRead z s r = z := by simp [labelRead, Nat.not_lt.mpr hr]

lemma build_labelRead_of_ge (N z : ℕ) (gs : List Gate) (r : ℕ)
    (hr : N + N + gs.length ≤ r) : labelRead z (build N z gs) r = z := by
  apply labelRead_of_ge
  simpa only [build_one_length] using hr

def ZeroMap (N : ℕ) (s : State) : Prop :=
  ∀ r, (degrees s).getD r 0 = 0 → (one s).getD r N = N

lemma initial_zero_map (N : ℕ) : ZeroMap N (initial N) := by
  intro r hd
  change (List.replicate N 0 ++ List.replicate N 1).getD r 0 = 0 at hd
  change (List.replicate N N ++ List.range N).getD r N = N
  by_cases hr : r < N
  · rw [List.getD_append _ _ _ _ (by simpa using hr)]
    exact List.getD_replicate N hr
  · have hNr : N ≤ r := by omega
    by_cases hr2 : r < N + N
    · rw [List.getD_append_right _ _ _ _ (by simpa using hNr)] at hd
      simp only [List.length_replicate] at hd
      rw [List.getD_replicate 1 (by omega : r - N < N)] at hd
      omega
    · apply List.getD_eq_default
      simp only [List.length_append, List.length_replicate, List.length_range]
      omega

lemma out_of_zero_degree (N z : ℕ) (s : State) (g : Gate)
    (hd : g.lineDegree (degrees s) = 0) : out N z s g = N := by
  have hp : payload N z s g = [] := by simp [payload, hd]
  simp [out, hp]

lemma structure_getD_snoc_length {α : Type*} (xs : List α) (a d : α) :
    (xs ++ [a]).getD xs.length d = a := by
  rw [List.getD_append_right _ _ _ _ (Nat.le_refl _)]
  simp

lemma advance_zero_map (N z : ℕ) (s : State) (g : Gate)
    (hlen : (one s).length = (degrees s).length) (hz : ZeroMap N s) :
    ZeroMap N (advance N z s g) := by
  intro r hd
  by_cases hr : r < (one s).length
  · rw [advance_one, List.getD_append _ _ _ _ hr]
    rw [advance_degrees, List.getD_append _ _ _ _ (by omega)] at hd
    exact hz r hd
  · by_cases he : r = (one s).length
    · subst r
      rw [advance_one, structure_getD_snoc_length]
      rw [advance_degrees, hlen, structure_getD_snoc_length] at hd
      exact out_of_zero_degree N z s g hd
    · apply List.getD_eq_default
      rw [advance_one, List.length_append, List.length_singleton]
      omega

lemma fold_zero_map (N z : ℕ) (gs : List Gate) (s : State)
    (hlen : (one s).length = (degrees s).length) (hz : ZeroMap N s) :
    ZeroMap N (gs.foldl (advance N z) s) := by
  induction gs generalizing s with
  | nil => exact hz
  | cons g gs ih =>
    rw [List.foldl_cons]
    apply ih
    · simp only [advance_one, advance_degrees, List.length_append,
        List.length_singleton, hlen]
    · exact advance_zero_map N z s g hlen hz

lemma build_zero_map (N z : ℕ) (gs : List Gate) : ZeroMap N (build N z gs) := by
  apply fold_zero_map N z gs (initial N)
  · simp [initial, one, degrees]
  · exact initial_zero_map N

lemma build_one_eq_false_of_degree_zero (N z : ℕ) (gs : List Gate) (r : ℕ)
    (hd : (degrees (build N z gs)).getD r 0 = 0) :
    (one (build N z gs)).getD r N = N := build_zero_map N z gs r hd

lemma normalize_one_eq_false_of_degree_zero (N : ℕ) (C : Circuit) (r : ℕ)
    (hd : (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD r 0 = 0) :
    (one (normalize N C)).getD r N = N := by
  apply build_zero_map N (N + N + C.size) C.gates r
  change (degrees (normalize N C)).getD r 0 = 0
  rw [normalize_degrees_eq]
  exact hd

lemma build_false_wire (N z : ℕ) (gs : List Gate) (labels : ℕ → Bool)
    (y : List Bool) (hy : y.length = N) :
    (run (net (build N z gs)) labels y).getD N false = false := by
  obtain ⟨t, ht⟩ := build_net_false_prefix N z gs
  rw [ht, run_cons]
  change (run t labels (y ++ [false])).getD N false = false
  rw [run_getD_lt _ _ _ _ (by simp [hy])]
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp [hy]

lemma normalize_false_wire (N : ℕ) (C : Circuit) (labels : ℕ → Bool)
    (y : List Bool) (hy : y.length = N) :
    (run (net (normalize N C)) labels y).getD N false = false :=
  build_false_wire N (N + N + C.size) C.gates labels y hy

lemma initial_map_value (N : ℕ) (labels : ℕ → Bool) (y : List Bool) (hy : y.length = N) :
    ∀ r, (run (net (initial N)) labels y).getD ((one (initial N)).getD r N) false =
      (List.replicate N false ++ y).getD r false := by
  intro r
  have hfalse : (run (net (initial N)) labels y).getD N false = false := by
    simpa only [build, List.foldl_nil] using build_false_wire N 0 [] labels y hy
  by_cases hr : r < N
  · rw [initial_one_point N r hr, hfalse,
      List.getD_append _ _ _ _ (by simpa using hr), List.getD_replicate false hr]
  · have hNr : N ≤ r := by omega
    by_cases hr2 : r < N + N
    · have hl : r - N < N := by omega
      have he : N + (r - N) = r := by omega
      have hm := initial_one_line N (r - N) hl
      rw [he] at hm
      rw [hm, run_getD_lt _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by simpa using hNr)]
      simp only [List.length_replicate]
    · have hm : (one (initial N)).getD r N = N := by
        apply List.getD_eq_default
        simp only [initial, one, List.length_append, List.length_replicate, List.length_range]
        omega
      rw [hm, hfalse]
      symm
      apply List.getD_eq_default
      simp only [List.length_append, List.length_replicate, hy]
      omega

def forkAt (d : List ℕ) (g : Gate) : Bool :=
  if g.lineDegree d = 2 then
    match g.op, g.inputs with
    | .and, [r, t] => decide (d.getD r 0 = 1 ∧ d.getD t 0 = 1)
    | _, _ => false
  else false

def degreeCountFrom (k : ℕ) : List ℕ → List Gate → ℕ
  | _, [] => 0
  | d, g :: gs => (if g.lineDegree d = k then 1 else 0) +
      degreeCountFrom k (d ++ [g.lineDegree d]) gs

def forkCountFrom : List ℕ → List Gate → ℕ
  | _, [] => 0
  | d, g :: gs => (if forkAt d g then 1 else 0) +
      forkCountFrom (d ++ [g.lineDegree d]) gs

def degreeCount (N k : ℕ) (gs : List Gate) : ℕ :=
  degreeCountFrom k (degrees (initial N)) gs

def forkCount (N : ℕ) (gs : List Gate) : ℕ :=
  forkCountFrom (degrees (initial N)) gs

lemma forwardWeight_eq_classified (s : State) (g : Gate) :
    forwardWeight s g =
      (if g.lineDegree (degrees s) = 1 then 1 else 0) +
      (if g.lineDegree (degrees s) = 2 then 1 else 0) +
      2 * (if forkAt (degrees s) g then 1 else 0) := by
  unfold forwardWeight forkAt
  dsimp only
  split_ifs
  all_goals try split
  all_goals try split_ifs
  all_goals simp_all

lemma forkAt_true_degree_two (d : List ℕ) (g : Gate) (hf : forkAt d g = true) :
    g.lineDegree d = 2 := by
  unfold forkAt at hf
  split_ifs at hf with hd
  exact hd

lemma forkAt_iff (d : List ℕ) (g : Gate) : forkAt d g = true ↔
    ∃ r t, g.op = GateOp.and ∧ g.inputs = [r, t] ∧
      d.getD r 0 = 1 ∧ d.getD t 0 = 1 := by
  classical
  constructor
  · intro hf
    unfold forkAt at hf
    split_ifs at hf
    split at hf
    · rename_i r t hop hrs
      exact ⟨r, t, hop, hrs, by simpa using hf⟩
    · contradiction
  · rintro ⟨r, t, hop, hrs, hr, ht⟩
    have hd : g.lineDegree d = 2 := by
      unfold Gate.lineDegree
      rw [hop, hrs]
      simp only [ite_true, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      rw [hr, ht]
    rw [forkAt, ite_eq_left hd, hop, hrs]
    exact decide_eq_true ⟨hr, ht⟩

lemma fold_net_length_classified (N z : ℕ) (gs : List Gate) (s : State) :
    (net (gs.foldl (advance N z) s)).length ≤ (net s).length +
      degreeCountFrom 1 (degrees s) gs + degreeCountFrom 2 (degrees s) gs +
      2 * forkCountFrom (degrees s) gs := by
  induction gs generalizing s with
  | nil => simp [degreeCountFrom, forkCountFrom]
  | cons g gs ih =>
    have h := ih (advance N z s g)
    rw [advance_net, List.length_append, advance_degrees] at h
    have hp := payload_length_le_weight N z s g
    rw [forwardWeight_eq_classified] at hp
    simp only [List.foldl_cons, degreeCountFrom, forkCountFrom]
    omega

lemma build_net_length_classified (N z : ℕ) (gs : List Gate) :
    (net (build N z gs)).length ≤
      1 + degreeCount N 1 gs + degreeCount N 2 gs + 2 * forkCount N gs := by
  simpa only [build, degreeCount, forkCount, initial, net, List.length_singleton]
    using fold_net_length_classified N z gs (initial N)

lemma normalize_net_length_classified (N : ℕ) (C : Circuit) :
    (net (normalize N C)).length ≤ 1 + degreeCount N 1 C.gates +
      degreeCount N 2 C.gates + 2 * forkCount N C.gates :=
  build_net_length_classified N (N + N + C.size) C.gates

lemma forkCountFrom_le_degree_two (d : List ℕ) (gs : List Gate) :
    forkCountFrom d gs ≤ degreeCountFrom 2 d gs := by
  induction gs generalizing d with
  | nil => rfl
  | cons g gs ih =>
    have h := ih (d ++ [g.lineDegree d])
    have hstep : (if forkAt d g then 1 else 0) ≤ (if g.lineDegree d = 2 then 1 else 0) := by
      by_cases hf : forkAt d g = true
      · simp [hf, forkAt_true_degree_two d g hf]
      · simp [hf]
    simp only [forkCountFrom, degreeCountFrom]
    omega

lemma forkCount_le_degree_two (N : ℕ) (gs : List Gate) :
    forkCount N gs ≤ degreeCount N 2 gs := forkCountFrom_le_degree_two _ _

lemma degree_counts_le_length (d : List ℕ) (gs : List Gate) :
    degreeCountFrom 0 d gs + degreeCountFrom 1 d gs + degreeCountFrom 2 d gs ≤ gs.length := by
  induction gs generalizing d with
  | nil => rfl
  | cons g gs ih =>
    have h := ih (d ++ [g.lineDegree d])
    simp only [degreeCountFrom, List.length_cons]
    split_ifs <;> omega

lemma degreeCount_zero_one_two_le_length (N : ℕ) (gs : List Gate) :
    degreeCount N 0 gs + degreeCount N 1 gs + degreeCount N 2 gs ≤ gs.length :=
  degree_counts_le_length _ _

end Pilot5bMeta1020Forward


namespace OneLineCoefficient

open PEqualNP.CircuitLowerBounds

def value (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def coeff (g : Gate) (z p : List Bool) : Bool :=
  match g.op, g.inputs with
  | .or, ins => (ins.map fun i => p.getD i false).any id
  | .and, [] => false
  | .and, [a] => p.getD a false
  | .and, [a, b] =>
      (z.getD a false && p.getD b false) || (p.getD a false && z.getD b false)
  | _, _ => false

def At (z p w : Bool) (d : ℕ) : Prop :=
  (z = true → w = true) ∧ (p = true → w = true) ∧
  (d = 0 → p = false) ∧ (d ≤ 1 → w = (z || p))

lemma at_false : At false false false 0 := by simp [At]

lemma at_and {za pa wa zb pb wb : Bool} {da db : ℕ}
    (ha : At za pa wa da) (hb : At zb pb wb db) :
    At (za && zb) ((za && pb) || (pa && zb)) (wa && wb) (da + db) := by
  obtain ⟨hza, hpa, hpa0, ha1⟩ := ha
  obtain ⟨hzb, hpb, hpb0, hb1⟩ := hb
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    rw [Bool.and_eq_true] at h
    obtain ⟨ha, hb⟩ := h
    simpa only [Bool.and_eq_true] using And.intro (hza ha) (hzb hb)
  · intro h
    rw [Bool.or_eq_true] at h
    rcases h with h | h
    · rw [Bool.and_eq_true] at h
      obtain ⟨ha, hb⟩ := h
      simpa only [Bool.and_eq_true] using And.intro (hza ha) (hpb hb)
    · rw [Bool.and_eq_true] at h
      obtain ⟨ha, hb⟩ := h
      simpa only [Bool.and_eq_true] using And.intro (hpa ha) (hzb hb)
  · intro h
    have ha0 : da = 0 := by omega
    have hb0 : db = 0 := by omega
    simp [hpa0 ha0, hpb0 hb0]
  · intro h
    have ha' : da ≤ 1 := by omega
    have hb' : db ≤ 1 := by omega
    rw [ha1 ha', hb1 hb']
    have hz : da = 0 ∨ db = 0 := by omega
    rcases hz with hz | hz
    · rw [hpa0 hz]
      cases za <;> cases zb <;> cases pb <;> rfl
    · rw [hpb0 hz]
      cases za <;> cases zb <;> cases pa <;> rfl

lemma at_or {za pa wa zb pb wb : Bool} {da db : ℕ}
    (ha : At za pa wa da) (hb : At zb pb wb db) :
    At (za || zb) (pa || pb) (wa || wb) (max da db) := by
  obtain ⟨hza, hpa, hpa0, ha1⟩ := ha
  obtain ⟨hzb, hpb, hpb0, hb1⟩ := hb
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    rw [Bool.or_eq_true] at h
    rcases h with h | h
    · simpa only [Bool.or_eq_true] using Or.inl (b := wb = true) (hza h)
    · simpa only [Bool.or_eq_true] using Or.inr (a := wa = true) (hzb h)
  · intro h
    rw [Bool.or_eq_true] at h
    rcases h with h | h
    · simpa only [Bool.or_eq_true] using Or.inl (b := wb = true) (hpa h)
    · simpa only [Bool.or_eq_true] using Or.inr (a := wa = true) (hpb h)
  · intro h
    have ha0 : da = 0 := by omega
    have hb0 : db = 0 := by omega
    simp [hpa0 ha0, hpb0 hb0]
  · intro h
    have ha' : da ≤ 1 := le_trans (le_max_left _ _) h
    have hb' : db ≤ 1 := le_trans (le_max_right _ _) h
    rw [ha1 ha', hb1 hb']
    cases za <;> cases zb <;> cases pa <;> cases pb <;> rfl

def AllAt (z p w : List Bool) (d : List ℕ) : Prop :=
  ∀ i, At (z.getD i false) (p.getD i false) (w.getD i false) (d.getD i 0)

lemma gate_at (g : Gate) (z p w : List Bool) (d : List ℕ)
    (hm : g.op = .and ∨ g.op = .or) (hl : g.inputs.length ≤ 2)
    (h : AllAt z p w d) :
    At (value g z) (coeff g z p) (value g w) (g.lineDegree d) := by
  rcases g with ⟨op, ins⟩
  change op = .and ∨ op = .or at hm
  change ins.length ≤ 2 at hl
  rcases hm with rfl | rfl
  · cases ins with
    | nil => simp [At, value, coeff, GateOp.eval, Gate.lineDegree]
    | cons a as =>
      cases as with
      | nil => simpa [value, coeff, GateOp.eval, Gate.lineDegree] using h a
      | cons b bs =>
        cases bs with
        | nil => simpa [value, coeff, GateOp.eval, Gate.lineDegree] using at_and (h a) (h b)
        | cons c cs => simp only [List.length_cons] at hl; omega
  · cases ins with
    | nil => simp [At, value, coeff, GateOp.eval, Gate.lineDegree]
    | cons a as =>
      cases as with
      | nil => simpa [value, coeff, GateOp.eval, Gate.lineDegree] using h a
      | cons b bs =>
        cases bs with
        | nil => simpa [value, coeff, GateOp.eval, Gate.lineDegree] using at_or (h a) (h b)
        | cons c cs => simp only [List.length_cons] at hl; omega

lemma gate_coeff_sound (g : Gate) (z p w : List Bool) (d : List ℕ)
    (hm : g.op = .and ∨ g.op = .or) (hl : g.inputs.length ≤ 2)
    (h : AllAt z p w d) : coeff g z p = true → value g w = true :=
  (gate_at g z p w d hm hl h).2.1

lemma gate_coeff_zero (g : Gate) (z p w : List Bool) (d : List ℕ)
    (hm : g.op = .and ∨ g.op = .or) (hl : g.inputs.length ≤ 2)
    (h : AllAt z p w d) : g.lineDegree d = 0 → coeff g z p = false :=
  (gate_at g z p w d hm hl h).2.2.1

lemma gate_coeff_complete (g : Gate) (z p w : List Bool) (d : List ℕ)
    (hm : g.op = .and ∨ g.op = .or) (hl : g.inputs.length ≤ 2)
    (h : AllAt z p w d) (hd : g.lineDegree d ≤ 1)
    (hw : value g w = true) (hz : value g z = false) : coeff g z p = true := by
  have heq := (gate_at g z p w d hm hl h).2.2.2 hd
  simpa [hw, hz] using heq.symm

lemma input_degree_le (g : Gate) (d : List ℕ) (r : ℕ)
    (hm : g.op = .and ∨ g.op = .or) (hl : g.inputs.length ≤ 2)
    (hr : r ∈ g.inputs) : d.getD r 0 ≤ g.lineDegree d := by
  rcases g with ⟨op, ins⟩
  change op = .and ∨ op = .or at hm
  change ins.length ≤ 2 at hl
  change r ∈ ins at hr
  rcases hm with rfl | rfl
  · cases ins with
    | nil => simp at hr
    | cons a as =>
      cases as with
      | nil =>
        simp only [List.mem_singleton] at hr
        subst r
        simp [Gate.lineDegree]
      | cons b bs =>
        cases bs with
        | nil =>
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> simp [Gate.lineDegree]
        | cons c cs => simp only [List.length_cons] at hl; omega

  · cases ins with
    | nil => simp at hr
    | cons a as =>
      cases as with
      | nil =>
        simp only [List.mem_singleton] at hr
        subst r
        simp [Gate.lineDegree]
      | cons b bs =>
        cases bs with
        | nil =>
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> simp [Gate.lineDegree]
        | cons c cs => simp only [List.length_cons] at hl; omega

lemma coeff_congr (g : Gate) (z p z' p' : List Bool)
    (hz : ∀ r ∈ g.inputs, z.getD r false = z'.getD r false)
    (hp : ∀ r ∈ g.inputs, p.getD r false = p'.getD r false) :
    coeff g z p = coeff g z' p' := by
  rcases g with ⟨op, ins⟩
  cases op with
  | and =>
    cases ins with
    | nil => rfl
    | cons a as =>
      cases as with
      | nil => exact hp a (by simp)
      | cons b bs =>
        cases bs with
        | nil => simp only [coeff, hz a (by simp), hz b (by simp), hp a (by simp), hp b (by simp)]
        | cons c cs => rfl
  | or =>
    change (ins.map (fun r => p.getD r false)).any id = (ins.map (fun r => p'.getD r false)).any id
    congr 1
    apply List.map_congr_left
    intro r hr
    exact hp r hr
  | not => rfl
  | mod m => rfl
  | maj => rfl

lemma coeff_false_of_reads (g : Gate) (z p : List Bool)
    (hp : ∀ r ∈ g.inputs, p.getD r false = false) : coeff g z p = false := by
  rcases g with ⟨op, ins⟩
  cases op with
  | and =>
    cases ins with
    | nil => rfl
    | cons a as =>
      cases as with
      | nil => exact hp a (by simp)
      | cons b bs =>
        cases bs with
        | nil =>
          change ((z.getD a false && p.getD b false) || (p.getD a false && z.getD b false)) = false
          rw [hp a (by simp), hp b (by simp)]
          simp
        | cons c cs => rfl
  | or =>
    have heq : ins.map (fun r => p.getD r false) = ins.map (fun _ => false) := by
      apply List.map_congr_left
      intro r hr
      exact hp r hr
    change (ins.map (fun r => p.getD r false)).any id = false
    rw [heq]
    simp
  | not => rfl
  | mod m => rfl
  | maj => rfl

lemma coeff_zero_of_reads (g : Gate) (z p : List Bool) (d : List ℕ)
    (hm : g.op = .and ∨ g.op = .or) (hl : g.inputs.length ≤ 2)
    (hp : ∀ r ∈ g.inputs, d.getD r 0 = 0 → p.getD r false = false)
    (hd : g.lineDegree d = 0) : coeff g z p = false := by
  apply coeff_false_of_reads
  intro r hr
  apply hp r hr
  have hle := input_degree_le g d r hm hl hr
  omega

lemma append_allAt (z p w : List Bool) (d : List ℕ)
    (hzp : z.length = p.length) (hzw : z.length = w.length) (hzd : z.length = d.length)
    (h : AllAt z p w d) (zn pn wn : Bool) (dn : ℕ) (hn : At zn pn wn dn) :
    AllAt (z ++ [zn]) (p ++ [pn]) (w ++ [wn]) (d ++ [dn]) := by
  intro i
  by_cases hi : i < z.length
  · have hip : i < p.length := by omega
    have hiw : i < w.length := by omega
    have hid : i < d.length := by omega
    rw [List.getD_append z [zn] false i hi, List.getD_append p [pn] false i hip,
      List.getD_append w [wn] false i hiw, List.getD_append d [dn] 0 i hid]
    exact h i
  · by_cases he : i = z.length
    · have hp : p.length ≤ i := by omega
      have hw : w.length ≤ i := by omega
      have hd : d.length ≤ i := by omega
      rw [List.getD_append_right z [zn] false i (by omega),
        List.getD_append_right p [pn] false i hp,
        List.getD_append_right w [wn] false i hw,
        List.getD_append_right d [dn] 0 i hd]
      have ez : i - z.length = 0 := by omega
      have ep : i - p.length = 0 := by omega
      have ew : i - w.length = 0 := by omega
      have ed : i - d.length = 0 := by omega
      simpa only [ez, ep, ew, ed, List.getD_cons_zero] using hn
    · have hz : (z ++ [zn]).length ≤ i := by simp only [List.length_append, List.length_singleton]; omega
      have hp : (p ++ [pn]).length ≤ i := by simp only [List.length_append, List.length_singleton]; omega
      have hw : (w ++ [wn]).length ≤ i := by simp only [List.length_append, List.length_singleton]; omega
      have hd : (d ++ [dn]).length ≤ i := by simp only [List.length_append, List.length_singleton]; omega
      rw [List.getD_eq_default _ _ hz, List.getD_eq_default _ _ hp,
        List.getD_eq_default _ _ hw, List.getD_eq_default _ _ hd]
      exact at_false

abbrev State := List Bool × List Bool × List Bool × List ℕ

def step (s : State) (g : Gate) : State :=
  (s.1 ++ [value g s.1],
    s.2.1 ++ [coeff g s.1 s.2.1],
    s.2.2.1 ++ [value g s.2.2.1],
    s.2.2.2 ++ [g.lineDegree s.2.2.2])

def Valid (s : State) : Prop :=
  s.1.length = s.2.1.length ∧ s.1.length = s.2.2.1.length ∧
  s.1.length = s.2.2.2.length ∧ AllAt s.1 s.2.1 s.2.2.1 s.2.2.2

lemma step_valid (s : State) (g : Gate) (hs : Valid s)
    (hm : g.op = .and ∨ g.op = .or) (hl : g.inputs.length ≤ 2) : Valid (step s g) := by
  rcases s with ⟨z, p, w, d⟩
  rcases hs with ⟨hzp, hzw, hzd, h⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [step, List.length_append, List.length_singleton] using congrArg (fun n => n + 1) hzp
  · simpa only [step, List.length_append, List.length_singleton] using congrArg (fun n => n + 1) hzw
  · simpa only [step, List.length_append, List.length_singleton] using congrArg (fun n => n + 1) hzd
  · exact append_allAt z p w d hzp hzw hzd h _ _ _ _ (gate_at g z p w d hm hl h)

lemma fold_valid (gs : List Gate) (s : State) (hs : Valid s)
    (hm : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) :
    Valid (gs.foldl step s) := by
  induction gs generalizing s with
  | nil => exact hs
  | cons g gs ih =>
    have hg := hm g List.mem_cons_self
    exact ih (step s g) (step_valid s g hs hg.1 hg.2)
      (fun h hh => hm h (List.mem_cons_of_mem g hh))

def run (gs : List Gate) (z p w : List Bool) (d : List ℕ) : State :=
  gs.foldl step (z, p, w, d)

lemma run_valid (gs : List Gate) (z p w : List Bool) (d : List ℕ)
    (hzp : z.length = p.length) (hzw : z.length = w.length) (hzd : z.length = d.length)
    (h : AllAt z p w d)
    (hm : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) :
    Valid (run gs z p w d) :=
  fold_valid gs (z, p, w, d) ⟨hzp, hzw, hzd, h⟩ hm

lemma fold_lengths (gs : List Gate) (s : State) :
    (gs.foldl step s).1.length = s.1.length + gs.length ∧
    (gs.foldl step s).2.1.length = s.2.1.length + gs.length ∧
    (gs.foldl step s).2.2.1.length = s.2.2.1.length + gs.length ∧
    (gs.foldl step s).2.2.2.length = s.2.2.2.length + gs.length := by
  induction gs generalizing s with
  | nil => simp
  | cons g gs ih =>
    simpa only [List.foldl_cons, List.length_cons, step, List.length_append,
      List.length_singleton, List.length_nil, Nat.zero_add, Nat.add_assoc, Nat.add_comm 1] using ih (step s g)

lemma fold_p_getD (gs : List Gate) (s : State) (i : ℕ) (hi : i < s.2.1.length) :
    (gs.foldl step s).2.1.getD i false = s.2.1.getD i false := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih =>
    have hi' : i < (step s g).2.1.length := by simp only [step, List.length_append, List.length_singleton]; omega
    change (gs.foldl step (step s g)).2.1.getD i false = s.2.1.getD i false
    rw [ih (step s g) hi']
    exact List.getD_append _ _ _ _ hi

lemma fold_z_getD (gs : List Gate) (s : State) (i : ℕ) (hi : i < s.1.length) :
    (gs.foldl step s).1.getD i false = s.1.getD i false := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih =>
    have hi' : i < (step s g).1.length := by simp only [step, List.length_append, List.length_singleton]; omega
    change (gs.foldl step (step s g)).1.getD i false = s.1.getD i false
    rw [ih (step s g) hi']
    exact List.getD_append _ _ _ _ hi

lemma fold_prefix_p_getD (pre post : List Gate) (s : State) (i : ℕ)
    (hi : i < (pre.foldl step s).2.1.length) :
    ((pre ++ post).foldl step s).2.1.getD i false = (pre.foldl step s).2.1.getD i false := by
  rw [List.foldl_append]
  exact fold_p_getD post (pre.foldl step s) i hi

lemma fold_prefix_z_getD (pre post : List Gate) (s : State) (i : ℕ)
    (hi : i < (pre.foldl step s).1.length) :
    ((pre ++ post).foldl step s).1.getD i false = (pre.foldl step s).1.getD i false := by
  rw [List.foldl_append]
  exact fold_z_getD post (pre.foldl step s) i hi

lemma fold_zero_eq (gs : List Gate) (s : State) :
    (gs.foldl step s).1 = gs.foldl (fun z g => z ++ [value g z]) s.1 := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih => simpa only [List.foldl_cons, step] using ih (step s g)

lemma fold_full_eq (gs : List Gate) (s : State) :
    (gs.foldl step s).2.2.1 = gs.foldl (fun w g => w ++ [value g w]) s.2.2.1 := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih => simpa only [List.foldl_cons, step] using ih (step s g)

lemma fold_degree_eq (gs : List Gate) (s : State) :
    (gs.foldl step s).2.2.2 = gs.foldl (fun d g => d ++ [g.lineDegree d]) s.2.2.2 := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih => simpa only [List.foldl_cons, step] using ih (step s g)

lemma run_zero_circuit (C : Circuit) (z p w : List Bool) (d : List ℕ) :
    (run C.gates z p w d).1 = C.wires z :=
  fold_zero_eq C.gates (z, p, w, d)

lemma run_full_circuit (C : Circuit) (z p w : List Bool) (d : List ℕ) :
    (run C.gates z p w d).2.2.1 = C.wires w :=
  fold_full_eq C.gates (z, p, w, d)

lemma at_point (b : Bool) : At b false b 0 := by cases b <;> simp [At]

lemma at_line (b : Bool) : At false b b 1 := by cases b <;> simp [At]

def initial (x y : List Bool) : State :=
  (x ++ List.replicate y.length false,
    List.replicate x.length false ++ y,
    x ++ y,
    List.replicate x.length 0 ++ List.replicate y.length 1)

lemma initial_allAt (x y : List Bool) :
    AllAt (x ++ List.replicate y.length false) (List.replicate x.length false ++ y)
      (x ++ y) (List.replicate x.length 0 ++ List.replicate y.length 1) := by
  intro i
  by_cases hi : i < x.length
  · rw [List.getD_append x _ false i hi,
      List.getD_append (List.replicate x.length false) y false i (by simpa using hi),
      List.getD_append x y false i hi,
      List.getD_append (List.replicate x.length 0) _ 0 i (by simpa using hi),
      List.getD_replicate false hi, List.getD_replicate 0 hi]
    exact at_point (x.getD i false)
  · by_cases hj : i - x.length < y.length
    · rw [List.getD_append_right x _ false i (by omega),
        List.getD_append_right (List.replicate x.length false) y false i (by simpa using Nat.le_of_not_gt hi),
        List.getD_append_right x y false i (by omega),
        List.getD_append_right (List.replicate x.length 0) _ 0 i (by simpa using Nat.le_of_not_gt hi)]
      simp only [List.length_replicate]
      rw [List.getD_replicate false hj, List.getD_replicate 1 hj]
      exact at_line (y.getD (i - x.length) false)
    · have hxy : x.length + y.length ≤ i := by omega
      have hz : (x ++ List.replicate y.length false).length ≤ i := by simpa using hxy
      have hp : (List.replicate x.length false ++ y).length ≤ i := by simpa using hxy
      have hw : (x ++ y).length ≤ i := by simpa using hxy
      have hd : (List.replicate x.length 0 ++ List.replicate y.length 1).length ≤ i := by simpa using hxy
      rw [List.getD_eq_default _ _ hz, List.getD_eq_default _ _ hp,
        List.getD_eq_default _ _ hw, List.getD_eq_default _ _ hd]
      exact at_false

lemma initial_valid (x y : List Bool) : Valid (initial x y) := by
  refine ⟨by simp [initial], by simp [initial], by simp [initial], ?_⟩
  exact initial_allAt x y

lemma circuit_fold_valid (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (x y : List Bool) : Valid (C.gates.foldl step (initial x y)) := by
  apply fold_valid C.gates (initial x y) (initial_valid x y)
  intro g hg
  obtain ⟨hop, hlen⟩ := hm g hg
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hop, hlen⟩

lemma at_coeff_complete {z p w : Bool} {d : ℕ} (h : At z p w d)
    (hd : d ≤ 1) (hw : w = true) (hz : z = false) : p = true := by
  have heq := h.2.2.2 hd
  simpa [hw, hz] using heq.symm

lemma at_zero_value {z p w : Bool} {d : ℕ} (h : At z p w d) (hd : d = 0) : w = z := by
  have heq := h.2.2.2 (by omega : d ≤ 1)
  simpa [h.2.2.1 hd] using heq

end OneLineCoefficient

namespace Pilot5bMeta1020Forward

open PEqualNP.CircuitLowerBounds
open Pilot5bMeta1020Linear

abbrev CoeffState := OneLineCoefficient.State
abbrev coeffStep := OneLineCoefficient.step
abbrev CoeffValid := OneLineCoefficient.Valid

lemma coefficient_eq_list (g : Gate) (Z P : List Bool) :
    coefficient g (fun r => Z.getD r false) (fun r => P.getD r false) =
      OneLineCoefficient.coeff g Z P := by
  rcases g with ⟨op, rs⟩
  cases op with
  | or => rfl
  | and =>
    cases rs with
    | nil => rfl
    | cons r rs =>
      cases rs with
      | nil => rfl
      | cons t rs => cases rs <;> rfl
  | not => rfl
  | mod n => rfl
  | maj => rfl

lemma labels_agree_prefix (z : ℕ) (gs : List Gate) (s : State) (c : CoeffState)
    (labels : ℕ → Bool)
    (hz : c.1.length + gs.length ≤ z)
    (hlen : (one s).length = c.1.length)
    (hl : ∀ r, labels r = (gs.foldl coeffStep c).1.getD r false) (r : ℕ) :
    labels (labelRead z s r) = c.1.getD r false := by
  by_cases hr : r < (one s).length
  · rw [labelRead_of_lt z s r hr, hl]
    exact OneLineCoefficient.fold_z_getD gs c r (by omega)
  · rw [labelRead_of_ge z s r (by omega), hl]
    have hz' : (gs.foldl coeffStep c).1.length ≤ z := by
      rw [(OneLineCoefficient.fold_lengths gs c).1]
      exact hz
    rw [List.getD_eq_default _ _ hz', List.getD_eq_default _ _ (by omega : c.1.length ≤ r)]

lemma fold_map_correct (N z : ℕ) (gs : List Gate) (s : State) (c : CoeffState)
    (labels : ℕ → Bool) (y : List Bool)
    (hy : y.length = N) (hc : CoeffValid c)
    (hd : degrees s = c.2.2.2) (hlen : (one s).length = c.1.length)
    (hn : 0 < (net s).length) (hb : OneBound N s) (hzm : ZeroMap N s)
    (hz : c.1.length + gs.length ≤ z)
    (hl : ∀ r, labels r = (gs.foldl coeffStep c).1.getD r false)
    (hf : (run (net s) labels y).getD N false = false)
    (hmap : ∀ r, (degrees s).getD r 0 ≤ 2 →
      (run (net s) labels y).getD ((one s).getD r N) false = c.2.1.getD r false)
    (hm : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) :
    ∀ r, (degrees (gs.foldl (advance N z) s)).getD r 0 ≤ 2 →
      (run (net (gs.foldl (advance N z) s)) labels y).getD
          ((one (gs.foldl (advance N z) s)).getD r N) false =
        (gs.foldl coeffStep c).2.1.getD r false := by
  induction gs generalizing s c with
  | nil => exact hmap
  | cons g gs ih =>
    have hg := hm g List.mem_cons_self
    have hc' : CoeffValid (coeffStep c g) :=
      OneLineCoefficient.step_valid c g hc hg.1 hg.2
    have hd' : degrees (advance N z s g) = (coeffStep c g).2.2.2 := by
      simp only [advance_degrees, coeffStep,
        OneLineCoefficient.step, hd]
    have hlen' : (one (advance N z s g)).length = (coeffStep c g).1.length := by
      simp only [advance_one, coeffStep,
        OneLineCoefficient.step,
        List.length_append, List.length_singleton, hlen]
    have hn' : 0 < (net (advance N z s g)).length := by
      rw [advance_net, List.length_append]
      omega
    have hb' := advance_one_bound N z s g hn hb
    have hzm' := advance_zero_map N z s g (by rw [hd]; exact hlen.trans hc.2.2.1) hzm
    have hz' : (coeffStep c g).1.length + gs.length ≤ z := by
      have hclen : (coeffStep c g).1.length = c.1.length + 1 := by
        simp [coeffStep, OneLineCoefficient.step]
      rw [hclen]
      simp only [List.length_cons] at hz
      omega
    have hl' : ∀ r, labels r = (gs.foldl coeffStep (coeffStep c g)).1.getD r false := hl
    have hvlen : (run (net s) labels y).length = N + (net s).length := by
      rw [run_length, hy]
    have hN : N < (run (net s) labels y).length := by rw [hvlen]; omega
    have hbget : ∀ r, (one s).getD r N < (run (net s) labels y).length := by
      intro r
      rw [hvlen]
      exact getD_bound_of_mem (one s) N (N + (net s).length) hb (by omega) r
    have hf' : (run (net (advance N z s g)) labels y).getD N false = false := by
      rw [advance_net, run_append, run_getD_lt _ _ _ _ hN, hf]
    have hlocal := advance_correct N z s g labels (run (net s) labels y) c.2.1
      hvlen (by rw [hd]; exact hc.2.2.1.symm.trans hlen.symm)
      (hc.1.symm.trans hlen.symm) hf hN hbget
      (fun r hr => by rw [hzm r hr]; exact hf) hmap
      (fun r hr => OneLineCoefficient.input_degree_le
        g (degrees s) r hg.1 hg.2 hr) hg.1 hg.2
    have hco : coefficient g (fun r => labels (labelRead z s r))
        (fun r => c.2.1.getD r false) =
          OneLineCoefficient.coeff g c.1 c.2.1 := by
      rw [← coefficient_eq_list]
      apply coefficient_congr
      · intro r hr
        exact labels_agree_prefix z (g :: gs) s c labels hz hlen hl r
      · intro r hr; rfl
    have hmap' : ∀ r, (degrees (advance N z s g)).getD r 0 ≤ 2 →
        (run (net (advance N z s g)) labels y).getD
            ((one (advance N z s g)).getD r N) false =
          (coeffStep c g).2.1.getD r false := by
      intro r hr
      rw [advance_net, run_append]
      simpa only [coeffStep, OneLineCoefficient.step, hco]
        using hlocal r hr
    exact ih (advance N z s g) (coeffStep c g) hc' hd' hlen' hn' hb' hzm'
      hz' hl' hf' hmap' (fun h hh => hm h (List.mem_cons_of_mem g hh))

def pointLabels (N : ℕ) (C : Circuit) (x : List Bool) : ℕ → Bool :=
  fun r => (C.wires (x ++ List.replicate N false)).getD r false

def coefficientState (C : Circuit) (x y : List Bool) : CoeffState :=
  C.gates.foldl coeffStep (OneLineCoefficient.initial x y)

lemma coefficientState_zero (N : ℕ) (C : Circuit) (x y : List Bool)
    (hy : y.length = N) :
    (coefficientState C x y).1 = C.wires (x ++ List.replicate N false) := by
  unfold coefficientState
  rw [OneLineCoefficient.fold_zero_eq]
  simp only [OneLineCoefficient.initial, hy]
  rfl

lemma coefficientState_full (C : Circuit) (x y : List Bool) :
    (coefficientState C x y).2.2.1 = C.wires (x ++ y) := by
  unfold coefficientState
  rw [OneLineCoefficient.fold_full_eq]
  rfl

lemma coefficientState_degrees (N : ℕ) (C : Circuit) (x y : List Bool)
    (hx : x.length = N) (hy : y.length = N) :
    (coefficientState C x y).2.2.2 =
      C.lineDegrees (N + N) (Finset.Ico N (N + N)) := by
  unfold coefficientState
  rw [OneLineCoefficient.fold_degree_eq]
  change C.gates.foldl (fun d g => d ++ [g.lineDegree d])
      (List.replicate x.length 0 ++ List.replicate y.length 1) = _
  rw [hx, hy]
  change C.gates.foldl (fun d g => d ++ [g.lineDegree d]) (degrees (initial N)) = _
  rw [initial_degrees_eq N]
  rfl

lemma normalize_correct (N : ℕ) (C : Circuit)
    (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (r : ℕ) (hr : (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD r 0 ≤ 2) :
    (run (net (normalize N C)) (pointLabels N C x) y).getD
        ((one (normalize N C)).getD r N) false =
      (coefficientState C x y).2.1.getD r false := by
  have h := fold_map_correct N (N + N + C.size) C.gates (initial N)
    (OneLineCoefficient.initial x y)
    (pointLabels N C x) y hy
    (OneLineCoefficient.initial_valid x y)
    (by simp [initial, degrees, OneLineCoefficient.initial, hx, hy])
    (by simp [initial, one, OneLineCoefficient.initial, hx, hy])
    (by simp [initial, net]) (initial_one_bound N) (initial_zero_map N)
    (by simp [OneLineCoefficient.initial, hx, hy, Circuit.size])
    (by
      intro i
      change (C.wires (x ++ List.replicate N false)).getD i false =
        (coefficientState C x y).1.getD i false
      rw [coefficientState_zero N C x y hy])
    (by
      simpa only [build, List.foldl_nil] using
        build_false_wire N (N + N + C.size) [] (pointLabels N C x) y hy)
    (by
      intro i hi
      simpa only [OneLineCoefficient.initial, hx] using
        initial_map_value N (pointLabels N C x) y hy i)
    (by
      intro g hg
      obtain ⟨hop, hfan⟩ := hm g hg
      exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hop, hfan⟩)
    r
  apply h
  change (degrees (normalize N C)).getD r 0 ≤ 2
  rw [normalize_degrees_eq]
  exact hr

lemma normalize_sound (N : ℕ) (C : Circuit)
    (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (r : ℕ) (hr : (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD r 0 ≤ 2)
    (hv : (run (net (normalize N C)) (pointLabels N C x) y).getD
      ((one (normalize N C)).getD r N) false = true) :
    (C.wires (x ++ y)).getD r false = true := by
  rw [normalize_correct N C hm x y hx hy r hr] at hv
  have ha := (OneLineCoefficient.circuit_fold_valid C hm x y).2.2.2 r
  have hw := ha.2.1 hv
  change (coefficientState C x y).2.2.1.getD r false = true at hw
  rw [coefficientState_full] at hw
  exact hw

lemma normalize_complete_degree_one (N : ℕ) (C : Circuit)
    (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (r : ℕ) (hr : (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD r 0 ≤ 1)
    (hw : (C.wires (x ++ y)).getD r false = true)
    (hz : (C.wires (x ++ List.replicate N false)).getD r false = false) :
    (run (net (normalize N C)) (pointLabels N C x) y).getD
      ((one (normalize N C)).getD r N) false = true := by
  rw [normalize_correct N C hm x y hx hy r (by omega)]
  have ha := (OneLineCoefficient.circuit_fold_valid C hm x y).2.2.2 r
  apply OneLineCoefficient.at_coeff_complete ha
  · change (coefficientState C x y).2.2.2.getD r 0 ≤ 1
    rw [coefficientState_degrees N C x y hx hy]
    exact hr
  · change (coefficientState C x y).2.2.1.getD r false = true
    rw [coefficientState_full]
    exact hw
  · change (coefficientState C x y).1.getD r false = false
    rw [coefficientState_zero N C x y hy]
    exact hz

end Pilot5bMeta1020Forward
namespace Pilot5bMeta1020Forward

open PEqualNP.CircuitLowerBounds
open Pilot5bMeta1020Linear

def pointList {N : ℕ} (z : Fin (N + N) → Bool) : List Bool :=
  List.ofFn (fun p : Fin N => z (Fin.castAdd N p))

def lineList {N : ℕ} (z : Fin (N + N) → Bool) : List Bool :=
  List.ofFn (fun l : Fin N => z (Fin.natAdd N l))

lemma ofFn_split {N : ℕ} (z : Fin (N + N) → Bool) :
    List.ofFn z = pointList z ++ lineList z := by
  exact List.ofFn_add (f := z)

lemma pointList_length {N : ℕ} (z : Fin (N + N) → Bool) :
    (pointList z).length = N := by simp [pointList]

lemma lineList_length {N : ℕ} (z : Fin (N + N) → Bool) :
    (lineList z).length = N := by simp [lineList]

def pairInput {N : ℕ} (p l : Fin N) : Fin (N + N) → Bool :=
  fun v => if v = Fin.castAdd N p then true
    else if v = Fin.natAdd N l then true else false

def pointInput {N : ℕ} (p : Fin N) : Fin (N + N) → Bool :=
  fun v => decide (v = Fin.castAdd N p)

lemma castAdd_ne_natAdd {N : ℕ} (p l : Fin N) :
    Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

lemma pairInput_point {N : ℕ} (p l q : Fin N) :
    pairInput p l (Fin.castAdd N q) = decide (q = p) := by
  simp only [pairInput, castAdd_ne_natAdd, ↓reduceIte, Fin.castAdd_inj]
  split <;> simp_all

lemma pairInput_line {N : ℕ} (p l u : Fin N) :
    pairInput p l (Fin.natAdd N u) = decide (u = l) := by
  have hn : Fin.natAdd N u ≠ Fin.castAdd N p := (castAdd_ne_natAdd p u).symm
  simp only [pairInput, hn, ↓reduceIte, Fin.natAdd_inj]
  split <;> simp_all

lemma pointInput_point {N : ℕ} (p q : Fin N) :
    pointInput p (Fin.castAdd N q) = decide (q = p) := by
  simp [pointInput]

lemma pointInput_line {N : ℕ} (p u : Fin N) :
    pointInput p (Fin.natAdd N u) = false := by
  have hn : Fin.natAdd N u ≠ Fin.castAdd N p := (castAdd_ne_natAdd p u).symm
  simp only [pointInput, hn, decide_false]

lemma pointList_pair {N : ℕ} (p l : Fin N) :
    pointList (pairInput p l) = List.ofFn (fun q : Fin N => decide (q = p)) := by
  simp only [pointList, pairInput_point]

lemma lineList_pair {N : ℕ} (p l : Fin N) :
    lineList (pairInput p l) = List.ofFn (fun u : Fin N => decide (u = l)) := by
  simp only [lineList, pairInput_line]

lemma pointInput_list {N : ℕ} (p : Fin N) :
    List.ofFn (pointInput p) =
      List.ofFn (fun q : Fin N => decide (q = p)) ++ List.replicate N false := by
  rw [ofFn_split]
  simp only [pointList, lineList, pointInput_point, pointInput_line, List.ofFn_const]

lemma pairInput_list {N : ℕ} (p l : Fin N) :
    List.ofFn (pairInput p l) =
      List.ofFn (fun q : Fin N => decide (q = p)) ++
        List.ofFn (fun u : Fin N => decide (u = l)) := by
  rw [ofFn_split, pointList_pair, lineList_pair]

lemma normalize_sound_fn (N : ℕ) (C : Circuit)
    (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (z : Fin (N + N) → Bool) (r : ℕ)
    (hr : (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD r 0 ≤ 2)
    (hv : (run (net (normalize N C)) (pointLabels N C (pointList z))
      (lineList z)).getD ((one (normalize N C)).getD r N) false = true) :
    (C.wires (List.ofFn z)).getD r false = true := by
  rw [ofFn_split]
  exact normalize_sound N C hm (pointList z) (lineList z)
    (pointList_length z) (lineList_length z) r hr hv

lemma normalize_complete_pair (N : ℕ) (C : Circuit)
    (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (p l : Fin N) (r : ℕ)
    (hr : (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD r 0 ≤ 1)
    (hw : (C.wires (List.ofFn (pairInput p l))).getD r false = true)
    (hz : (C.wires (List.ofFn (pointInput p))).getD r false = false) :
    (run (net (normalize N C))
      (pointLabels N C (List.ofFn (fun q : Fin N => decide (q = p))))
      (List.ofFn (fun u : Fin N => decide (u = l)))).getD
        ((one (normalize N C)).getD r N) false = true := by
  rw [pairInput_list] at hw
  rw [pointInput_list] at hz
  exact normalize_complete_degree_one N C hm _ _ (by simp) (by simp) r hr hw hz

end Pilot5bMeta1020Forward


namespace Pilot5bMeta1020OrAggregate

open Pilot5bMeta1020Linear

def appendOrs (n : ℕ) (gs : List Instruction) (r : ℕ) : List ℕ → List Instruction × ℕ
  | [] => (gs, r)
  | s :: rs => appendOrs n (gs ++ [Sum.inl [r, s]]) (n + gs.length) rs

def aggregate (n : ℕ) (gs : List Instruction) : List ℕ → List Instruction × ℕ
  | [] => (gs, n)
  | r :: rs => appendOrs n gs r rs

@[local simp] lemma aggregate_nil (n : ℕ) (gs : List Instruction) :
    aggregate n gs [] = (gs, n) := rfl

@[local simp] lemma aggregate_singleton (n : ℕ) (gs : List Instruction) (r : ℕ) :
    aggregate n gs [r] = (gs, r) := rfl

lemma appendOrs_extension (n : ℕ) (gs : List Instruction) (r : ℕ) (rs : List ℕ) :
    ∃ hs : List Instruction, (appendOrs n gs r rs).1 = gs ++ hs ∧
      hs.length = rs.length ∧ ∀ g ∈ hs, ∃ us, g = Sum.inl us ∧ us.length = 2 := by
  induction rs generalizing gs r with
  | nil => exact ⟨[], by simp [appendOrs], rfl, by simp⟩
  | cons s rs ih =>
    obtain ⟨hs, heq, hlen, hor⟩ := ih (gs ++ [Sum.inl [r, s]]) (n + gs.length)
    refine ⟨Sum.inl [r, s] :: hs, ?_, by simp [hlen], ?_⟩
    · simpa only [appendOrs, List.append_assoc, List.singleton_append] using heq
    · intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact ⟨[r, s], rfl, rfl⟩
      · exact hor g hg

lemma aggregate_extension (n : ℕ) (gs : List Instruction) (rs : List ℕ) :
    ∃ hs : List Instruction, (aggregate n gs rs).1 = gs ++ hs ∧
      hs.length = rs.length - 1 ∧
      ∀ g ∈ hs, ∃ us, g = Sum.inl us ∧ us.length = 2 := by
  cases rs with
  | nil => exact ⟨[], by simp, rfl, by simp⟩
  | cons r rs => simpa only [aggregate, List.length_cons, Nat.add_sub_cancel] using
      appendOrs_extension n gs r rs

lemma aggregate_length (n : ℕ) (gs : List Instruction) (rs : List ℕ) :
    (aggregate n gs rs).1.length = gs.length + (rs.length - 1) := by
  obtain ⟨hs, heq, hlen, _⟩ := aggregate_extension n gs rs
  simp [heq, hlen]

lemma aggregate_prefix (n : ℕ) (gs : List Instruction) (rs : List ℕ) :
    gs <+: (aggregate n gs rs).1 := by
  obtain ⟨hs, heq, _, _⟩ := aggregate_extension n gs rs
  exact ⟨hs, heq.symm⟩

lemma appendOrs_root_valid (n : ℕ) (gs : List Instruction) (r : ℕ) (rs : List ℕ)
    (hr : r < n + gs.length) :
    (appendOrs n gs r rs).2 < n + (appendOrs n gs r rs).1.length := by
  induction rs generalizing gs r with
  | nil => exact hr
  | cons s rs ih =>
    apply ih
    simp

lemma aggregate_root_valid (n : ℕ) (gs : List Instruction) (rs : List ℕ)
    (hz : gs.head? = some (Sum.inl []))
    (hrs : ∀ r ∈ rs, r < n + gs.length) :
    (aggregate n gs rs).2 < n + (aggregate n gs rs).1.length := by
  cases rs with
  | nil =>
    have hpos : 0 < gs.length := by
      cases gs with
      | nil => simp at hz
      | cons g gs => simp
    simpa only [aggregate] using (show n < n + gs.length by omega)
  | cons r rs => exact appendOrs_root_valid n gs r rs (hrs r (by simp))

lemma aggregate_old_read (n : ℕ) (gs : List Instruction) (rs : List ℕ)
    (labels : ℕ → Bool) (y : List Bool) (hy : y.length = n)
    (w : ℕ) (hw : w < n + gs.length) :
    (run (aggregate n gs rs).1 labels y).getD w false =
      (run gs labels y).getD w false := by
  obtain ⟨hs, heq, _, _⟩ := aggregate_extension n gs rs
  rw [heq, run_append]
  apply run_getD_lt
  simpa only [run_length, hy] using hw

lemma false_wire (n : ℕ) (gs : List Instruction)
    (hz : gs.head? = some (Sum.inl []))
    (labels : ℕ → Bool) (y : List Bool) (hy : y.length = n) :
    (run gs labels y).getD n false = false := by
  cases gs with
  | nil => simp at hz
  | cons g gs =>
    have hg : g = Sum.inl [] := Option.some.inj hz
    subst g
    rw [run_cons]
    simp only [step, List.map_nil, List.any_nil]
    rw [run_getD_lt gs labels (y ++ [false]) n (by simp [hy])]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp [hy]

lemma appendOrs_true (n : ℕ) (labels : ℕ → Bool) (y : List Bool) (hy : y.length = n)
    (gs : List Instruction) (r : ℕ) (rs : List ℕ)
    (hr : r < n + gs.length) (hrs : ∀ s ∈ rs, s < n + gs.length) :
    (run (appendOrs n gs r rs).1 labels y).getD (appendOrs n gs r rs).2 false = true ↔
      (run gs labels y).getD r false = true ∨
        ∃ s ∈ rs, (run gs labels y).getD s false = true := by
  induction rs generalizing gs r with
  | nil => simp [appendOrs]
  | cons s rs ih =>
    have hs : s < n + gs.length := hrs s (by simp)
    have htail : ∀ t ∈ rs, t < n + (gs ++ [Sum.inl [r, s]]).length := by
      intro t ht
      have h := hrs t (by simp [ht])
      simpa only [List.length_append, List.length_singleton] using (show t < n + (gs.length + 1) by omega)
    have hnew : n + gs.length < n + (gs ++ [Sum.inl [r, s]]).length := by simp
    rw [appendOrs, ih _ _ hnew htail]
    have hnewval : (run (gs ++ [Sum.inl [r, s]]) labels y).getD (n + gs.length) false =
        ((run gs labels y).getD r false || (run gs labels y).getD s false) := by
      simpa [hy, step] using snoc_read_new gs (Sum.inl [r, s]) labels y
    rw [hnewval, Bool.or_eq_true]
    have hold (t : ℕ) (ht : t ∈ rs) :
        (run (gs ++ [Sum.inl [r, s]]) labels y).getD t false =
          (run gs labels y).getD t false := by
      apply snoc_read_old
      have h := hrs t (by simp [ht])
      simpa only [hy] using h
    constructor
    · rintro ((hr | hs) | ⟨t, ht, hv⟩)
      · exact Or.inl hr
      · exact Or.inr ⟨s, by simp, hs⟩
      · exact Or.inr ⟨t, by simp [ht], (hold t ht) ▸ hv⟩
    · rintro (hr | ⟨t, ht, htval⟩)
      · exact Or.inl (Or.inl hr)
      · rcases List.mem_cons.mp ht with hts | ht
        · subst t
          exact Or.inl (Or.inr htval)
        · exact Or.inr ⟨t, ht, (hold t ht).symm ▸ htval⟩

lemma aggregate_true (n : ℕ) (gs : List Instruction) (rs : List ℕ)
    (hz : gs.head? = some (Sum.inl []))
    (hrs : ∀ r ∈ rs, r < n + gs.length)
    (labels : ℕ → Bool) (y : List Bool) (hy : y.length = n) :
    (run (aggregate n gs rs).1 labels y).getD (aggregate n gs rs).2 false = true ↔
      ∃ r ∈ rs, (run gs labels y).getD r false = true := by
  cases rs with
  | nil =>
    change (run gs labels y).getD n false = true ↔
      ∃ r ∈ ([] : List ℕ), (run gs labels y).getD r false = true
    rw [false_wire n gs hz labels y hy]
    simp
  | cons r rs =>
    rw [aggregate, appendOrs_true n labels y hy gs r rs (hrs r (by simp))
      (fun s hs => hrs s (by simp [hs]))]
    simp

lemma aggregate_fanin (n : ℕ) (gs : List Instruction) (rs : List ℕ)
    (hfan : ∀ us, Sum.inl us ∈ gs → us.length ≤ 2) :
    ∀ us, Sum.inl us ∈ (aggregate n gs rs).1 → us.length ≤ 2 := by
  obtain ⟨hs, heq, _, hor⟩ := aggregate_extension n gs rs
  intro us hu
  rw [heq] at hu
  rcases List.mem_append.mp hu with hu | hu
  · exact hfan us hu
  · obtain ⟨vs, he, hv⟩ := hor (Sum.inl us) hu
    have huvs : us = vs := Sum.inl.inj he
    simp [huvs, hv]

lemma aggregate_head (n : ℕ) (gs : List Instruction) (rs : List ℕ)
    (hz : gs.head? = some (Sum.inl [])) :
    (aggregate n gs rs).1.head? = some (Sum.inl []) := by
  obtain ⟨hs, heq, _, _⟩ := aggregate_extension n gs rs
  rw [heq]
  cases gs with
  | nil => simp at hz
  | cons g gs => simpa using hz

end Pilot5bMeta1020OrAggregate

namespace Pilot5bMeta1020Reverse

open Pilot5bMeta1020Linear Pilot5bMeta1020OrAggregate

abbrev State := List Instruction × ((ℕ → ℕ) × (ℕ → ℕ))

def net (s : State) : List Instruction := s.1
def context (s : State) : ℕ → ℕ := s.2.1
def message (s : State) : ℕ → ℕ := s.2.2

def initial (n : ℕ) (gs : List Instruction) : State := (gs, (fun _ => n, fun _ => n))

def incoming (seeds edges : List (ℕ × ℕ)) (messages : ℕ → ℕ) (v : ℕ) : List ℕ :=
  ((seeds.filter fun e => decide (e.1 = v)).map Prod.snd) ++
    ((edges.filter fun e => decide (e.2 = v)).map fun e => messages e.1)

def incomingCount (seeds edges : List (ℕ × ℕ)) (v : ℕ) : ℕ :=
  (seeds.filter fun e => decide (e.1 = v)).length +
    (edges.filter fun e => decide (e.2 = v)).length

lemma incoming_length (seeds edges : List (ℕ × ℕ)) (messages : ℕ → ℕ) (v : ℕ) :
    (incoming seeds edges messages v).length = incomingCount seeds edges v := by
  simp [incoming, incomingCount]

lemma mem_incoming (seeds edges : List (ℕ × ℕ)) (messages : ℕ → ℕ) (v r : ℕ) :
    r ∈ incoming seeds edges messages v ↔
      (∃ e ∈ seeds, e.1 = v ∧ e.2 = r) ∨
      (∃ e ∈ edges, e.2 = v ∧ messages e.1 = r) := by
  simp [incoming, and_assoc]

def step (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (v : ℕ) (s : State) : State :=
  let a := aggregate n (net s) (incoming seeds edges (message s) v)
  match weight v with
  | none => (a.1, (Function.update (context s) v a.2, Function.update (message s) v a.2))
  | some z => (a.1 ++ [Sum.inr (z, a.2)],
      (Function.update (context s) v a.2,
       Function.update (message s) v (n + a.1.length)))

def build (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ) : ℕ → State → State
  | 0, s => s
  | k + 1, s => build n seeds edges weight k (step n seeds edges weight k s)

def valid (n : ℕ) (s : State) : Prop :=
  (net s).head? = some (Sum.inl []) ∧
    (∀ v, context s v < n + (net s).length) ∧
    (∀ v, message s v < n + (net s).length)

lemma initial_valid (n : ℕ) (gs : List Instruction)
    (h : gs.head? = some (Sum.inl [])) : valid n (initial n gs) := by
  have hp : 0 < gs.length := by
    cases gs with
    | nil => simp at h
    | cons g gs => simp
  exact ⟨h, fun _ => by simpa [initial, context, net] using (show n < n + gs.length by omega),
    fun _ => by simpa [initial, message, net] using (show n < n + gs.length by omega)⟩

lemma incoming_valid (n : ℕ) (seeds edges : List (ℕ × ℕ)) (v : ℕ) (s : State)
    (hs : valid n s) (hseeds : ∀ e ∈ seeds, e.2 < n + (net s).length) :
    ∀ r ∈ incoming seeds edges (message s) v, r < n + (net s).length := by
  intro r hr
  rcases (mem_incoming seeds edges (message s) v r).mp hr with h | h
  · obtain ⟨e, he, _, rfl⟩ := h
    exact hseeds e he
  · obtain ⟨e, _, _, rfl⟩ := h
    exact hs.2.2 e.1

lemma step_extension (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (v : ℕ) (s : State) :
    ∃ hs, net (step n seeds edges weight v s) = net s ++ hs := by
  obtain ⟨hs, h, _, _⟩ := aggregate_extension n (net s) (incoming seeds edges (message s) v)
  cases hw : weight v with
  | none => exact ⟨hs, by simpa [step, net, hw] using h⟩
  | some z =>
    refine ⟨hs ++ [Sum.inr (z, (aggregate n (net s) (incoming seeds edges (message s) v)).2)], ?_⟩
    simp only [step, hw, net]
    simp only [net] at h
    rw [h, List.append_assoc]

lemma step_length (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (v : ℕ) (s : State) :
    (net (step n seeds edges weight v s)).length =
      (net s).length + (incomingCount seeds edges v - 1) +
        (if (weight v).isSome then 1 else 0) := by
  cases hw : weight v <;>
    simp [step, net, hw, aggregate_length, incoming_length]

lemma step_length_le (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (v : ℕ) (s : State) :
    (net s).length ≤ (net (step n seeds edges weight v s)).length := by
  rw [step_length]
  omega

lemma step_old_read (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (v : ℕ) (s : State) (labels : ℕ → Bool) (y : List Bool) (hy : y.length = n)
    (r : ℕ) (hr : r < n + (net s).length) :
    (run (net (step n seeds edges weight v s)) labels y).getD r false =
      (run (net s) labels y).getD r false := by
  obtain ⟨hs, he⟩ := step_extension n seeds edges weight v s
  rw [he, run_append]
  exact run_getD_lt hs labels _ r (by simpa only [run_length, hy] using hr)

lemma step_context_eq (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (v : ℕ) (s : State) :
    context (step n seeds edges weight v s) v =
      (aggregate n (net s) (incoming seeds edges (message s) v)).2 := by
  cases hw : weight v <;> simp [step, context, hw]

lemma step_context_ne (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (v : ℕ) (s : State) (u : ℕ) (hu : u ≠ v) :
    context (step n seeds edges weight v s) u = context s u := by
  cases hw : weight v <;> simp [step, context, hw, hu]

lemma step_message_ne (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (v : ℕ) (s : State) (u : ℕ) (hu : u ≠ v) :
    message (step n seeds edges weight v s) u = message s u := by
  cases hw : weight v <;> simp [step, message, hw, hu]

lemma step_valid (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (v : ℕ) (s : State) (hs : valid n s)
    (hseeds : ∀ e ∈ seeds, e.2 < n + (net s).length) :
    valid n (step n seeds edges weight v s) := by
  let a := aggregate n (net s) (incoming seeds edges (message s) v)
  have ha : a.2 < n + a.1.length :=
    aggregate_root_valid n (net s) _ hs.1 (incoming_valid n seeds edges v s hs hseeds)
  have hh : a.1.head? = some (Sum.inl []) := aggregate_head n (net s) _ hs.1
  have hl : (net s).length ≤ a.1.length := by
    dsimp [a]
    rw [aggregate_length]
    omega
  cases hw : weight v with
  | none =>
    change (net (step n seeds edges weight v s)).head? = _ ∧ _
    refine ⟨by simpa only [step, net, hw, a] using hh, ?_, ?_⟩
    · intro u
      simp only [context, step, hw, net]
      change Function.update (context s) v a.2 u < n + a.1.length
      by_cases hu : u = v
      · simpa [hu] using ha
      · simpa [hu] using (show context s u < n + a.1.length by have := hs.2.1 u; omega)
    · intro u
      simp only [message, step, hw, net]
      change Function.update (message s) v a.2 u < n + a.1.length
      by_cases hu : u = v
      · simpa [hu] using ha
      · simpa [hu] using (show message s u < n + a.1.length by have := hs.2.2 u; omega)
  | some z =>
    have hhead : (a.1 ++ [Sum.inr (z, a.2)]).head? = some (Sum.inl []) := by
      cases he : a.1 with
      | nil => simp [he] at hh
      | cons g gs => simpa [he] using hh
    refine ⟨by simpa only [step, net, hw, a] using hhead, ?_, ?_⟩
    · intro u
      simp only [context, step, hw, net]
      change Function.update (context s) v a.2 u < n + (a.1 ++ [Sum.inr (z, a.2)]).length
      simp only [List.length_append, List.length_singleton]
      by_cases hu : u = v
      · simpa [hu] using (show a.2 < n + (a.1.length + 1) by omega)
      · simpa [hu] using (show context s u < n + (a.1.length + 1) by have := hs.2.1 u; omega)
    · intro u
      simp only [message, step, hw, net]
      change Function.update (message s) v (n + a.1.length) u <
        n + (a.1 ++ [Sum.inr (z, a.2)]).length
      simp only [List.length_append, List.length_singleton]
      by_cases hu : u = v
      · simp [hu]
      · simpa [hu] using (show message s u < n + (a.1.length + 1) by have := hs.2.2 u; omega)

def weightValue (labels : ℕ → Bool) (weight : ℕ → Option ℕ) (v : ℕ) : Bool :=
  (weight v).elim true labels

lemma step_context_true (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (v : ℕ) (s : State) (hs : valid n s)
    (hseeds : ∀ e ∈ seeds, e.2 < n + (net s).length)
    (labels : ℕ → Bool) (y : List Bool) (hy : y.length = n) :
    (run (net (step n seeds edges weight v s)) labels y).getD
      (context (step n seeds edges weight v s) v) false = true ↔
        ∃ r ∈ incoming seeds edges (message s) v,
          (run (net s) labels y).getD r false = true := by
  let rs := incoming seeds edges (message s) v
  have hrs := incoming_valid n seeds edges v s hs hseeds
  have ht := aggregate_true n (net s) rs hs.1 hrs labels y hy
  have hr := aggregate_root_valid n (net s) rs hs.1 hrs
  rw [step_context_eq]
  cases hw : weight v with
  | none => simpa only [step, net, hw, rs] using ht
  | some z =>
    change (run (net (step n seeds edges weight v s)) labels y).getD
      (aggregate n (net s) rs).2 false = true ↔ _
    have hn : net (step n seeds edges weight v s) =
        (aggregate n (net s) rs).1 ++ [Sum.inr (z, (aggregate n (net s) rs).2)] := by
      simp only [step, net, hw, rs]
    rw [hn, snoc_read_old _ _ labels y _ (by simpa only [hy] using hr)]
    exact ht

lemma step_message_true (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (v : ℕ) (s : State) (hs : valid n s)
    (hseeds : ∀ e ∈ seeds, e.2 < n + (net s).length)
    (labels : ℕ → Bool) (y : List Bool) (hy : y.length = n) :
    (run (net (step n seeds edges weight v s)) labels y).getD
      (message (step n seeds edges weight v s) v) false = true ↔
        weightValue labels weight v = true ∧
        (run (net (step n seeds edges weight v s)) labels y).getD
          (context (step n seeds edges weight v s) v) false = true := by
  let a := aggregate n (net s) (incoming seeds edges (message s) v)
  have ha : a.2 < n + a.1.length :=
    aggregate_root_valid n (net s) _ hs.1 (incoming_valid n seeds edges v s hs hseeds)
  cases hw : weight v with
  | none => simp [step, net, context, message, hw, weightValue]
  | some z =>
    simp only [step, net, context, message, hw, Function.update_self, weightValue,
      Option.elim_some]
    change (run (a.1 ++ [Sum.inr (z, a.2)]) labels y).getD (n + a.1.length) false = true ↔
      labels z = true ∧ (run (a.1 ++ [Sum.inr (z, a.2)]) labels y).getD a.2 false = true
    have hn := snoc_read_new a.1 (Sum.inr (z, a.2)) labels y
    rw [hy] at hn
    rw [hn, snoc_read_old _ _ labels y _ (by simpa only [hy] using ha)]
    simp [Pilot5bMeta1020Linear.step]

lemma step_context_read_ne (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (v : ℕ) (s : State) (hs : valid n s) (labels : ℕ → Bool)
    (y : List Bool) (hy : y.length = n) (u : ℕ) (hu : u ≠ v) :
    (run (net (step n seeds edges weight v s)) labels y).getD
      (context (step n seeds edges weight v s) u) false =
        (run (net s) labels y).getD (context s u) false := by
  rw [step_context_ne _ _ _ _ _ _ _ hu]
  exact step_old_read n seeds edges weight v s labels y hy _ (hs.2.1 u)

lemma step_message_read_ne (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (v : ℕ) (s : State) (hs : valid n s) (labels : ℕ → Bool)
    (y : List Bool) (hy : y.length = n) (u : ℕ) (hu : u ≠ v) :
    (run (net (step n seeds edges weight v s)) labels y).getD
      (message (step n seeds edges weight v s) u) false =
        (run (net s) labels y).getD (message s u) false := by
  rw [step_message_ne _ _ _ _ _ _ _ hu]
  exact step_old_read n seeds edges weight v s labels y hy _ (hs.2.2 u)

end Pilot5bMeta1020Reverse


namespace Pilot5bMeta1020ReverseRecurrence

def descend {σ : Type*} (step : ℕ → σ → σ) : ℕ → σ → σ
  | 0, s => s
  | k + 1, s => descend step k (step k s)

def Correct {σ : Type*} (V : ℕ) (ctx msg : σ → ℕ → Bool)
    (weight target : ℕ → Bool) (k : ℕ) (s : σ) : Prop :=
  ∀ u, k ≤ u → u < V → ctx s u = target u ∧ msg s u = (weight u && target u)

lemma descend_invariant {σ : Type*} (V : ℕ) (step : ℕ → σ → σ)
    (ctx msg : σ → ℕ → Bool) (weight target : ℕ → Bool) (Valid : σ → Prop)
    (hvalid : ∀ v, v < V → ∀ s, Valid s → Valid (step v s))
    (hother : ∀ v, v < V → ∀ s, Valid s → ∀ u, u ≠ v →
      ctx (step v s) u = ctx s u ∧ msg (step v s) u = msg s u)
    (hnew : ∀ v, v < V → ∀ s, Valid s →
      (∀ u, v < u → u < V → msg s u = (weight u && target u)) →
      ctx (step v s) v = target v ∧ msg (step v s) v = (weight v && target v)) :
    ∀ k, k ≤ V → ∀ s, Valid s → Correct V ctx msg weight target k s →
      Valid (descend step k s) ∧ Correct V ctx msg weight target 0 (descend step k s) := by
  intro k
  induction k with
  | zero =>
    intro _ s hs hc
    exact ⟨hs, hc⟩
  | succ k ih =>
    intro hk s hs hc
    have hkv : k < V := by omega
    have hn := hnew k hkv s hs (by
      intro u hku hu
      exact (hc u (by omega) hu).2)
    have hnext : Correct V ctx msg weight target k (step k s) := by
      intro u hku hu
      by_cases huk : u = k
      · subst u
        exact hn
      · obtain ⟨hctx, hmsg⟩ := hother k hkv s hs u huk
        obtain ⟨hct, hmt⟩ := hc u (by omega) hu
        exact ⟨hctx.trans hct, hmsg.trans hmt⟩
    exact ih (by omega) (step k s) (hvalid k hkv s hs) hnext

def incomingValue (edges : List (ℕ × ℕ)) (v : ℕ) (msg : ℕ → Bool) : Bool :=
  edges.any fun e => decide (e.2 = v) && msg e.1

lemma incoming_congr (V : ℕ) (edges : List (ℕ × ℕ))
    (hedge : ∀ e ∈ edges, e.2 < e.1 ∧ e.1 < V)
    (v : ℕ) (msg msg' : ℕ → Bool)
    (hmsg : ∀ u, v < u → u < V → msg u = msg' u) :
    incomingValue edges v msg = incomingValue edges v msg' := by
  have hpoint : ∀ e ∈ edges,
      (decide (e.2 = v) && msg e.1) = (decide (e.2 = v) && msg' e.1) := by
    intro e he
    by_cases hev : e.2 = v
    · obtain ⟨hlt, hb⟩ := hedge e he
      have hp : v < e.1 := by omega
      simp [hev, hmsg e.1 hp hb]
    · simp [hev]
  apply Bool.eq_iff_iff.mpr
  simp only [incomingValue, List.any_eq_true]
  constructor
  · rintro ⟨e, he, hv⟩
    exact ⟨e, he, (hpoint e he) ▸ hv⟩
  · rintro ⟨e, he, hv⟩
    exact ⟨e, he, (hpoint e he).symm ▸ hv⟩

theorem descend_recurrence {σ : Type*} (V : ℕ) (step : ℕ → σ → σ)
    (ctx msg : σ → ℕ → Bool) (weight target seed : ℕ → Bool)
    (edges : List (ℕ × ℕ)) (Valid : σ → Prop)
    (hedge : ∀ e ∈ edges, e.2 < e.1 ∧ e.1 < V)
    (hvalid : ∀ v, v < V → ∀ s, Valid s → Valid (step v s))
    (hother : ∀ v, v < V → ∀ s, Valid s → ∀ u, u ≠ v →
      ctx (step v s) u = ctx s u ∧ msg (step v s) u = msg s u)
    (hctx : ∀ v, v < V → ∀ s, Valid s →
      ctx (step v s) v = (seed v || incomingValue edges v (msg s)))
    (hmsg : ∀ v, v < V → ∀ s, Valid s →
      msg (step v s) v = (weight v && ctx (step v s) v))
    (htarget : ∀ v, v < V →
      target v = (seed v || incomingValue edges v (fun u => weight u && target u)))
    (initial : σ) (hinitial : Valid initial) :
    Valid (descend step V initial) ∧
      ∀ u, u < V → ctx (descend step V initial) u = target u ∧
        msg (descend step V initial) u = (weight u && target u) := by
  have hn : ∀ v, v < V → ∀ s, Valid s →
      (∀ u, v < u → u < V → msg s u = (weight u && target u)) →
      ctx (step v s) v = target v ∧ msg (step v s) v = (weight v && target v) := by
    intro v hv s hs hparents
    have hc : ctx (step v s) v = target v := by
      rw [hctx v hv s hs,
        incoming_congr V edges hedge v (msg s) (fun u => weight u && target u) hparents]
      exact (htarget v hv).symm
    exact ⟨hc, by rw [hmsg v hv s hs, hc]⟩
  obtain ⟨hf, hc⟩ := descend_invariant V step ctx msg weight target Valid hvalid hother hn
    V le_rfl initial hinitial (by
      intro u hlu huu
      omega)
  exact ⟨hf, fun u hu => hc u (Nat.zero_le _) hu⟩

end Pilot5bMeta1020ReverseRecurrence


namespace Pilot5bMeta1020ReverseCorrectness

open Pilot5bMeta1020Linear Pilot5bMeta1020Reverse

abbrev read (labels : ℕ → Bool) (y : List Bool) (s : State) (w : ℕ) : Bool :=
  (run (net s) labels y).getD w false

abbrev ctxRead (labels : ℕ → Bool) (y : List Bool) (s : State) (v : ℕ) : Bool :=
  read labels y s (context s v)

abbrev msgRead (labels : ℕ → Bool) (y : List Bool) (s : State) (v : ℕ) : Bool :=
  read labels y s (message s v)

def seedValue (seeds : List (ℕ × ℕ)) (baseRead : ℕ → Bool) (v : ℕ) : Bool :=
  seeds.any fun e => decide (e.1 = v) && baseRead e.2

lemma seedValue_true (seeds : List (ℕ × ℕ)) (baseRead : ℕ → Bool) (v : ℕ) :
    seedValue seeds baseRead v = true ↔
      ∃ e ∈ seeds, e.1 = v ∧ baseRead e.2 = true := by
  simp [seedValue]

lemma incomingValue_true (edges : List (ℕ × ℕ)) (values : ℕ → Bool) (v : ℕ) :
    Pilot5bMeta1020ReverseRecurrence.incomingValue edges v values = true ↔
      ∃ e ∈ edges, e.2 = v ∧ values e.1 = true := by
  simp [Pilot5bMeta1020ReverseRecurrence.incomingValue]

def Stable (n : ℕ) (seeds : List (ℕ × ℕ)) (labels : ℕ → Bool)
    (y : List Bool) (baseRead : ℕ → Bool) (s : State) : Prop :=
  valid n s ∧ ∀ e ∈ seeds,
    e.2 < n + (net s).length ∧ read labels y s e.2 = baseRead e.2

lemma stable_step (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (labels : ℕ → Bool) (y : List Bool) (hy : y.length = n)
    (baseRead : ℕ → Bool) (v : ℕ) (s : State)
    (hs : Stable n seeds labels y baseRead s) :
    Stable n seeds labels y baseRead (Pilot5bMeta1020Reverse.step n seeds edges weight v s) := by
  refine ⟨step_valid n seeds edges weight v s hs.1 (fun e he => (hs.2 e he).1), ?_⟩
  intro e he
  obtain ⟨hev, her⟩ := hs.2 e he
  have hlen := step_length_le n seeds edges weight v s
  refine ⟨by omega, ?_⟩
  exact (step_old_read n seeds edges weight v s labels y hy e.2 hev).trans her

lemma context_step (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (labels : ℕ → Bool) (y : List Bool) (hy : y.length = n)
    (baseRead : ℕ → Bool) (v : ℕ) (s : State)
    (hs : Stable n seeds labels y baseRead s) :
    ctxRead labels y (Pilot5bMeta1020Reverse.step n seeds edges weight v s) v =
      (seedValue seeds baseRead v ||
        Pilot5bMeta1020ReverseRecurrence.incomingValue edges v (msgRead labels y s)) := by
  apply Bool.eq_iff_iff.mpr
  rw [step_context_true n seeds edges weight v s hs.1
    (fun e he => (hs.2 e he).1) labels y hy]
  rw [Bool.or_eq_true, seedValue_true, incomingValue_true]
  constructor
  · rintro ⟨r, hr, hv⟩
    rcases (mem_incoming seeds edges (message s) v r).mp hr with hh | hh
    · obtain ⟨e, he, hev, rfl⟩ := hh
      exact Or.inl ⟨e, he, hev, (hs.2 e he).2 ▸ hv⟩
    · obtain ⟨e, he, hev, rfl⟩ := hh
      exact Or.inr ⟨e, he, hev, hv⟩
  · rintro (⟨e, he, hev, hv⟩ | ⟨e, he, hev, hv⟩)
    · refine ⟨e.2, (mem_incoming seeds edges (message s) v e.2).mpr
        (Or.inl ⟨e, he, hev, rfl⟩), ?_⟩
      change read labels y s e.2 = true
      rw [(hs.2 e he).2]
      exact hv
    · exact ⟨message s e.1, (mem_incoming seeds edges (message s) v _).mpr
        (Or.inr ⟨e, he, hev, rfl⟩), hv⟩

lemma message_step (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (labels : ℕ → Bool) (y : List Bool) (hy : y.length = n)
    (baseRead : ℕ → Bool) (v : ℕ) (s : State)
    (hs : Stable n seeds labels y baseRead s) :
    msgRead labels y (Pilot5bMeta1020Reverse.step n seeds edges weight v s) v =
      (weightValue labels weight v &&
        ctxRead labels y (Pilot5bMeta1020Reverse.step n seeds edges weight v s) v) := by
  apply Bool.eq_iff_iff.mpr
  rw [Bool.and_eq_true]
  exact step_message_true n seeds edges weight v s hs.1
    (fun e he => (hs.2 e he).1) labels y hy

lemma build_eq_descend (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (k : ℕ) (s : State) :
    build n seeds edges weight k s =
      Pilot5bMeta1020ReverseRecurrence.descend
        (Pilot5bMeta1020Reverse.step n seeds edges weight) k s := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => exact ih _

theorem build_correct (n V : ℕ) (seeds edges : List (ℕ × ℕ))
    (weight : ℕ → Option ℕ) (labels : ℕ → Bool) (y : List Bool) (hy : y.length = n)
    (baseRead target : ℕ → Bool)
    (hedge : ∀ e ∈ edges, e.2 < e.1 ∧ e.1 < V)
    (htarget : ∀ v, v < V → target v =
      (seedValue seeds baseRead v ||
        Pilot5bMeta1020ReverseRecurrence.incomingValue edges v
          (fun u => weightValue labels weight u && target u)))
    (initial : State) (hinitial : Stable n seeds labels y baseRead initial) :
    Stable n seeds labels y baseRead (build n seeds edges weight V initial) ∧
      ∀ u, u < V →
        ctxRead labels y (build n seeds edges weight V initial) u = target u ∧
        msgRead labels y (build n seeds edges weight V initial) u =
          (weightValue labels weight u && target u) := by
  have h := Pilot5bMeta1020ReverseRecurrence.descend_recurrence V
    (Pilot5bMeta1020Reverse.step n seeds edges weight) (ctxRead labels y) (msgRead labels y)
    (weightValue labels weight) target (seedValue seeds baseRead) edges
    (Stable n seeds labels y baseRead) hedge
    (fun v _ s hs => stable_step n seeds edges weight labels y hy baseRead v s hs)
    (fun v _ s hs u hu => ⟨
      step_context_read_ne n seeds edges weight v s hs.1 labels y hy u hu,
      step_message_read_ne n seeds edges weight v s hs.1 labels y hy u hu⟩)
    (fun v _ s hs => context_step n seeds edges weight labels y hy baseRead v s hs)
    (fun v _ s hs => message_step n seeds edges weight labels y hy baseRead v s hs)
    htarget initial hinitial
  simpa only [build_eq_descend] using h

lemma stable_initial (n : ℕ) (gs : List Instruction) (seeds : List (ℕ × ℕ))
    (hz : gs.head? = some (Sum.inl []))
    (hseeds : ∀ e ∈ seeds, e.2 < n + gs.length)
    (labels : ℕ → Bool) (y : List Bool) :
    Stable n seeds labels y (fun r => (run gs labels y).getD r false) (initial n gs) := by
  refine ⟨initial_valid n gs hz, ?_⟩
  intro e he
  exact ⟨hseeds e he, rfl⟩

end Pilot5bMeta1020ReverseCorrectness


namespace Pilot5bMeta1020Weighted

def activeEdge (edges : List (ℕ × ℕ)) (weightEval : ℕ → Bool)
    (u v : ℕ) : Prop := (u, v) ∈ edges ∧ weightEval u = true

def seedReachable (edges : List (ℕ × ℕ)) (weightEval : ℕ → Bool)
    (seeds : List (ℕ × ℕ)) (seedEval : ℕ → Bool) (v : ℕ) : Prop :=
  ∃ s ∈ seeds, seedEval s.2 = true ∧
    Relation.ReflTransGen (activeEdge edges weightEval) s.1 v

noncomputable def target (edges : List (ℕ × ℕ)) (weightEval : ℕ → Bool)
    (seeds : List (ℕ × ℕ)) (seedEval : ℕ → Bool) (v : ℕ) : Bool := by
  classical
  exact decide (seedReachable edges weightEval seeds seedEval v)

@[local simp] lemma target_true (edges : List (ℕ × ℕ)) (weightEval : ℕ → Bool)
    (seeds : List (ℕ × ℕ)) (seedEval : ℕ → Bool) (v : ℕ) :
    target edges weightEval seeds seedEval v = true ↔
      seedReachable edges weightEval seeds seedEval v := by
  classical
  simp [target]

theorem target_recurrence (edges : List (ℕ × ℕ)) (weightEval : ℕ → Bool)
    (seeds : List (ℕ × ℕ)) (seedEval : ℕ → Bool) (v : ℕ) :
    target edges weightEval seeds seedEval v = true ↔
      (∃ s ∈ seeds, s.1 = v ∧ seedEval s.2 = true) ∨
      ∃ e ∈ edges, e.2 = v ∧ weightEval e.1 = true ∧
        target edges weightEval seeds seedEval e.1 = true := by
  constructor
  · intro ht
    obtain ⟨s, hs, hb, hp⟩ := (target_true edges weightEval seeds seedEval v).mp ht
    rcases hp.cases_tail with h | ⟨u, hsu, huv⟩
    · exact Or.inl ⟨s, hs, h.symm, hb⟩
    · refine Or.inr ⟨(u, v), huv.1, rfl, huv.2, ?_⟩
      exact (target_true edges weightEval seeds seedEval u).mpr ⟨s, hs, hb, hsu⟩
  · rintro (⟨s, hs, hv, hb⟩ | ⟨e, he, hv, hw, hu⟩)
    · apply (target_true edges weightEval seeds seedEval v).mpr
      refine ⟨s, hs, hb, ?_⟩
      simpa only [hv] using
        (Relation.ReflTransGen.refl : Relation.ReflTransGen (activeEdge edges weightEval) s.1 s.1)
    · obtain ⟨s, hs, hb, hsu⟩ := (target_true edges weightEval seeds seedEval e.1).mp hu
      apply (target_true edges weightEval seeds seedEval v).mpr
      refine ⟨s, hs, hb, hsu.tail ?_⟩
      exact ⟨by simpa only [← hv] using he, hw⟩

theorem target_recurrence_eq (edges : List (ℕ × ℕ)) (weightEval : ℕ → Bool)
    (seeds : List (ℕ × ℕ)) (seedEval : ℕ → Bool) (v : ℕ) :
    target edges weightEval seeds seedEval v =
      ((seeds.any fun s => decide (s.1 = v) && seedEval s.2) ||
        (edges.any fun e => decide (e.2 = v) &&
          (weightEval e.1 && target edges weightEval seeds seedEval e.1))) := by
  apply Bool.eq_iff_iff.mpr
  rw [target_recurrence]
  simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]

lemma target_of_seed (edges : List (ℕ × ℕ)) (weightEval : ℕ → Bool)
    (seeds : List (ℕ × ℕ)) (seedEval : ℕ → Bool) (s : ℕ × ℕ)
    (hs : s ∈ seeds) (hb : seedEval s.2 = true) :
    target edges weightEval seeds seedEval s.1 = true :=
  (target_true edges weightEval seeds seedEval s.1).mpr ⟨s, hs, hb, .refl⟩

lemma target_of_edge (edges : List (ℕ × ℕ)) (weightEval : ℕ → Bool)
    (seeds : List (ℕ × ℕ)) (seedEval : ℕ → Bool) (u v : ℕ)
    (he : (u, v) ∈ edges) (hw : weightEval u = true)
    (hu : target edges weightEval seeds seedEval u = true) :
    target edges weightEval seeds seedEval v = true :=
  (target_recurrence edges weightEval seeds seedEval v).mpr
    (Or.inr ⟨(u, v), he, rfl, hw, hu⟩)

lemma rtc_backward {α : Type*} {R : α → α → Prop} {F : α → Prop}
    (hstep : ∀ u v, R u v → F v → F u) {s v : α}
    (hpath : Relation.ReflTransGen R s v) : F v → F s := by
  induction hpath with
  | refl => exact id
  | @tail u v hsu huv ih => exact fun hv => ih (hstep u v huv hv)

theorem backward_propagation (edges : List (ℕ × ℕ)) (weightEval : ℕ → Bool)
    (F : ℕ → Prop)
    (hstep : ∀ u v, (u, v) ∈ edges → weightEval u = true → F v → F u)
    {s v : ℕ} (hpath : Relation.ReflTransGen (activeEdge edges weightEval) s v)
    (hv : F v) : F s :=
  rtc_backward (fun u v h => hstep u v h.1 h.2) hpath hv

lemma target_backward_seed (edges : List (ℕ × ℕ)) (weightEval : ℕ → Bool)
    (seeds : List (ℕ × ℕ)) (seedEval : ℕ → Bool) (F : ℕ → Prop)
    (hstep : ∀ u v, (u, v) ∈ edges → weightEval u = true → F v → F u)
    (v : ℕ) (ht : target edges weightEval seeds seedEval v = true) (hv : F v) :
    ∃ s ∈ seeds, seedEval s.2 = true ∧ F s.1 := by
  obtain ⟨s, hs, hb, hpath⟩ := (target_true edges weightEval seeds seedEval v).mp ht
  exact ⟨s, hs, hb, backward_propagation edges weightEval F hstep hpath hv⟩

lemma rtc_forward {α : Type*} {R : α → α → Prop} {F : α → Prop}
    (hstep : ∀ u v, R u v → F u → F v) {s v : α}
    (hpath : Relation.ReflTransGen R s v) : F s → F v := by
  induction hpath with
  | refl => exact id
  | @tail u v hsu huv ih => exact fun hs => hstep u v huv (ih hs)

theorem target_cover (edges : List (ℕ × ℕ)) (weightEval : ℕ → Bool)
    (seeds : List (ℕ × ℕ)) (seedEval : ℕ → Bool) (F : ℕ → Prop)
    (hseed : ∀ s ∈ seeds, seedEval s.2 = true → F s.1)
    (hstep : ∀ u v, (u, v) ∈ edges → weightEval u = true → F u → F v)
    (v : ℕ) (ht : target edges weightEval seeds seedEval v = true) : F v := by
  obtain ⟨s, hs, hb, hpath⟩ := (target_true edges weightEval seeds seedEval v).mp ht
  exact rtc_forward (fun u v h => hstep u v h.1 h.2) hpath (hseed s hs hb)

lemma target_true_iff_seed_of_no_active_incoming
    (edges : List (ℕ × ℕ)) (weightEval : ℕ → Bool)
    (seeds : List (ℕ × ℕ)) (seedEval : ℕ → Bool) (v : ℕ)
    (hin : ∀ u, ¬ activeEdge edges weightEval u v) :
    target edges weightEval seeds seedEval v = true ↔
      ∃ s ∈ seeds, s.1 = v ∧ seedEval s.2 = true := by
  rw [target_recurrence]
  constructor
  · rintro (hs | ⟨e, he, hv, hw, _⟩)
    · exact hs
    · exact (hin e.1 ⟨by simpa only [← hv] using he, hw⟩).elim
  · exact Or.inl

lemma target_true_iff_seed_of_no_incoming
    (edges : List (ℕ × ℕ)) (weightEval : ℕ → Bool)
    (seeds : List (ℕ × ℕ)) (seedEval : ℕ → Bool) (v : ℕ)
    (hin : ∀ e ∈ edges, e.2 ≠ v) :
    target edges weightEval seeds seedEval v = true ↔
      ∃ s ∈ seeds, s.1 = v ∧ seedEval s.2 = true := by
  apply target_true_iff_seed_of_no_active_incoming
  intro u hu
  exact hin (u, v) hu.1 rfl

lemma target_false_of_no_incoming_no_seed
    (edges : List (ℕ × ℕ)) (weightEval : ℕ → Bool)
    (seeds : List (ℕ × ℕ)) (seedEval : ℕ → Bool) (v : ℕ)
    (hin : ∀ e ∈ edges, e.2 ≠ v)
    (hseed : ∀ s ∈ seeds, s.1 = v → seedEval s.2 = false) :
    target edges weightEval seeds seedEval v = false := by
  apply Bool.eq_false_of_not_eq_true
  intro ht
  obtain ⟨s, hs, hv, hb⟩ :=
    (target_true_iff_seed_of_no_incoming edges weightEval seeds seedEval v hin).mp ht
  simp [hseed s hs hv] at hb

@[local simp] lemma target_empty_seeds (edges : List (ℕ × ℕ)) (weightEval : ℕ → Bool)
    (seedEval : ℕ → Bool) (v : ℕ) : target edges weightEval [] seedEval v = false := by
  classical
  simp [target, seedReachable]

lemma target_empty_edges (weightEval : ℕ → Bool)
    (seeds : List (ℕ × ℕ)) (seedEval : ℕ → Bool) (v : ℕ) :
    target [] weightEval seeds seedEval v = true ↔
      ∃ s ∈ seeds, s.1 = v ∧ seedEval s.2 = true :=
  target_true_iff_seed_of_no_incoming [] weightEval seeds seedEval v (by simp)

end Pilot5bMeta1020Weighted


namespace Pilot5bMeta1020ReverseWeightedCorrectness

open Pilot5bMeta1020Linear Pilot5bMeta1020Reverse Pilot5bMeta1020ReverseCorrectness

 theorem build_weighted (n V : ℕ) (seeds edges : List (ℕ × ℕ))
    (weight : ℕ → Option ℕ) (labels : ℕ → Bool) (y : List Bool) (hy : y.length = n)
    (baseRead : ℕ → Bool)
    (hedge : ∀ e ∈ edges, e.2 < e.1 ∧ e.1 < V)
    (s : State) (hs : Stable n seeds labels y baseRead s) :
    Stable n seeds labels y baseRead (build n seeds edges weight V s) ∧
      ∀ u, u < V →
        ctxRead labels y (build n seeds edges weight V s) u =
          Pilot5bMeta1020Weighted.target edges (weightValue labels weight) seeds baseRead u ∧
        msgRead labels y (build n seeds edges weight V s) u =
          (weightValue labels weight u &&
            Pilot5bMeta1020Weighted.target edges (weightValue labels weight) seeds baseRead u) := by
  apply build_correct n V seeds edges weight labels y hy baseRead
    (Pilot5bMeta1020Weighted.target edges (weightValue labels weight) seeds baseRead) hedge
    (fun v _ => ?_) s hs
  exact Pilot5bMeta1020Weighted.target_recurrence_eq edges (weightValue labels weight)
    seeds baseRead v

 theorem build_initial (n V : ℕ) (gs : List Instruction) (seeds edges : List (ℕ × ℕ))
    (weight : ℕ → Option ℕ) (labels : ℕ → Bool) (y : List Bool) (hy : y.length = n)
    (hz : gs.head? = some (Sum.inl []))
    (hseeds : ∀ e ∈ seeds, e.2 < n + gs.length)
    (hedge : ∀ e ∈ edges, e.2 < e.1 ∧ e.1 < V) :
    valid n (build n seeds edges weight V (initial n gs)) ∧
      ∀ u, u < V →
        ctxRead labels y (build n seeds edges weight V (initial n gs)) u =
          Pilot5bMeta1020Weighted.target edges (weightValue labels weight) seeds
            (fun r => (run gs labels y).getD r false) u ∧
        msgRead labels y (build n seeds edges weight V (initial n gs)) u =
          (weightValue labels weight u &&
            Pilot5bMeta1020Weighted.target edges (weightValue labels weight) seeds
              (fun r => (run gs labels y).getD r false) u) := by
  have h := build_weighted n V seeds edges weight labels y hy
    (fun r => (run gs labels y).getD r false) hedge (initial n gs)
    (stable_initial n gs seeds hz hseeds labels y)
  exact ⟨h.1.1, h.2⟩

 theorem context_true_iff (n V : ℕ) (gs : List Instruction) (seeds edges : List (ℕ × ℕ))
    (weight : ℕ → Option ℕ) (labels : ℕ → Bool) (y : List Bool) (hy : y.length = n)
    (hz : gs.head? = some (Sum.inl []))
    (hseeds : ∀ e ∈ seeds, e.2 < n + gs.length)
    (hedge : ∀ e ∈ edges, e.2 < e.1 ∧ e.1 < V) (v : ℕ) (hv : v < V) :
    ctxRead labels y (build n seeds edges weight V (initial n gs)) v = true ↔
      Pilot5bMeta1020Weighted.seedReachable edges (weightValue labels weight) seeds
        (fun r => (run gs labels y).getD r false) v := by
  rw [((build_initial n V gs seeds edges weight labels y hy hz hseeds hedge).2 v hv).1]
  exact Pilot5bMeta1020Weighted.target_true edges (weightValue labels weight) seeds
    (fun r => (run gs labels y).getD r false) v

end Pilot5bMeta1020ReverseWeightedCorrectness


namespace ReverseBudget

lemma aggregate_pred_budget {α : Type*} [DecidableEq α]
    (V F : Finset α) (n : α → ℕ) (hF : F ⊆ V)
    (hn : ∀ v ∈ F, 1 ≤ n v) :
    (∑ v ∈ V, (n v - 1)) + F.card ≤ ∑ v ∈ V, n v := by
  classical
  have hcount : (∑ v ∈ V, if v ∈ F then (1 : ℕ) else 0) = F.card := by
    have hfilter : V.filter (fun v => v ∈ F) = F := by
      ext v
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨hF h, h⟩⟩
    rw [← Finset.sum_filter]
    simp [hfilter]
  rw [← hcount, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro v hv
  by_cases hf : v ∈ F
  · simp only [hf, ↓reduceIte]
    have := hn v hf
    omega
  · simp [hf]

lemma positive_network_budget
    (g1 m k f J f' hCost kCost total : ℕ)
    (hh : hCost ≤ m + k + 3 * f)
    (hk : kCost + f' ≤ 2 * m + 2 * k + J)
    (ht : total ≤ g1 + hCost + kCost) :
    total + f' ≤ g1 + 3 * (m + k + f) + J := by
  omega

lemma final_budget
    (s J g0 g1 g2 s0 s1 jobs forks : ℕ)
    (h0 : s0 ≤ g0 + g1)
    (h1 : s1 + forks ≤ g1 + 3 * g2 + J)
    (hj : jobs ≤ J + forks)
    (hg : g0 + g1 + g2 ≤ s) :
    18 * s0 + 28 * s1 + 27 * jobs ≤ 84 * s + 55 * J := by
  omega

lemma posted_budget
    (s J N s0 s1 jobs forks g0 g1 g2 : ℕ)
    (h0 : s0 ≤ g0 + g1)
    (h1 : s1 + forks ≤ g1 + 3 * g2 + J)
    (hj : jobs ≤ J + forks)
    (hg : g0 + g1 + g2 ≤ s) :
    18 * s0 + 28 * s1 + 27 * jobs ≤ 100 * (s + J) + 4 * N := by
  have := final_budget s J g0 g1 g2 s0 s1 jobs forks h0 h1 hj hg
  omega

end ReverseBudget

namespace ReverseBudget

def incomingAt {α : Type*} (target : α → ℕ) (xs : List α) (v : ℕ) : ℕ :=
  (xs.filter fun x => decide (target x = v)).length

lemma incomingAt_cons {α : Type*} (target : α → ℕ) (a : α) (xs : List α) (v : ℕ) :
    incomingAt target (a :: xs) v =
      (if target a = v then 1 else 0) + incomingAt target xs v := by
  by_cases h : target a = v <;> simp [incomingAt, h, Nat.add_comm]

lemma incomingAt_sum {α : Type*} (target : α → ℕ) (xs : List α) (B : ℕ) :
    (∑ v ∈ Finset.range B, incomingAt target xs v) =
      (xs.filter fun x => decide (target x < B)).length := by
  induction xs with
  | nil => simp [incomingAt]
  | cons a xs ih =>
    simp_rw [incomingAt_cons]
    rw [Finset.sum_add_distrib, ih]
    have hdelta : (∑ v ∈ Finset.range B, if target a = v then (1 : ℕ) else 0) =
        if target a < B then 1 else 0 := by
      simp [eq_comm]
    rw [hdelta]
    by_cases h : target a < B <;> simp [h, Nat.add_comm]

theorem incomingAt_sum_le {α : Type*} (target : α → ℕ) (xs : List α) (B : ℕ) :
    (∑ v ∈ Finset.range B, incomingAt target xs v) ≤ xs.length := by
  rw [incomingAt_sum]
  exact List.length_filter_le _ _

theorem incomingAt_sum_eq {α : Type*} (target : α → ℕ) (xs : List α) (B : ℕ)
    (h : ∀ x ∈ xs, target x < B) :
    (∑ v ∈ Finset.range B, incomingAt target xs v) = xs.length := by
  rw [incomingAt_sum]
  congr 1
  exact List.filter_eq_self.mpr (by intro x hx; exact decide_eq_true (h x hx))

def messageCount (seeds edges : List (ℕ × ℕ)) (v : ℕ) : ℕ :=
  incomingAt Prod.fst seeds v + incomingAt Prod.snd edges v

def incomingMessages (seeds edges : List (ℕ × ℕ)) (message : ℕ → ℕ) (v : ℕ) : List ℕ :=
  ((seeds.filter fun e => decide (e.1 = v)).map Prod.snd) ++
    ((edges.filter fun e => decide (e.2 = v)).map fun e => message e.1)

lemma incomingMessages_length (seeds edges : List (ℕ × ℕ)) (message : ℕ → ℕ) (v : ℕ) :
    (incomingMessages seeds edges message v).length = messageCount seeds edges v := by
  simp [incomingMessages, messageCount, incomingAt]

theorem messageCount_sum_le (seeds edges : List (ℕ × ℕ)) (B : ℕ) :
    (∑ v ∈ Finset.range B, messageCount seeds edges v) ≤ seeds.length + edges.length := by
  simp only [messageCount, Finset.sum_add_distrib]
  exact Nat.add_le_add (incomingAt_sum_le Prod.fst seeds B) (incomingAt_sum_le Prod.snd edges B)

theorem messageCount_sum_eq (seeds edges : List (ℕ × ℕ)) (B : ℕ)
    (hseeds : ∀ e ∈ seeds, e.1 < B) (hedges : ∀ e ∈ edges, e.2 < B) :
    (∑ v ∈ Finset.range B, messageCount seeds edges v) = seeds.length + edges.length := by
  simp only [messageCount, Finset.sum_add_distrib]
  rw [incomingAt_sum_eq Prod.fst seeds B hseeds, incomingAt_sum_eq Prod.snd edges B hedges]

theorem static_aggregate_budget (seeds edges : List (ℕ × ℕ)) (B : ℕ)
    (usedForks : Finset ℕ) (hF : usedForks ⊆ Finset.range B)
    (hpositive : ∀ v ∈ usedForks, 1 ≤ messageCount seeds edges v) :
    (∑ v ∈ Finset.range B, (messageCount seeds edges v - 1)) + usedForks.card ≤
      seeds.length + edges.length := by
  exact (aggregate_pred_budget (Finset.range B) usedForks (messageCount seeds edges) hF hpositive).trans
    (messageCount_sum_le seeds edges B)

theorem static_net_budget (seeds edges : List (ℕ × ℕ)) (B : ℕ)
    (usedForks : Finset ℕ) (hF : usedForks ⊆ Finset.range B)
    (hpositive : ∀ v ∈ usedForks, 1 ≤ messageCount seeds edges v)
    (initial final weighted : ℕ)
    (hcost : final ≤ initial +
      (∑ v ∈ Finset.range B, (messageCount seeds edges v - 1)) + weighted) :
    final + usedForks.card ≤ initial + seeds.length + edges.length + weighted := by
  have := static_aggregate_budget seeds edges B usedForks hF hpositive
  omega

lemma foldl_cost_bound {σ α : Type*} (step : σ → α → σ) (measure : σ → ℕ)
    (cost : α → ℕ) (xs : List α)
    (hstep : ∀ a ∈ xs, ∀ s, measure (step s a) ≤ measure s + cost a) (s : σ) :
    measure (xs.foldl step s) ≤ measure s + (xs.map cost).sum := by
  induction xs generalizing s with
  | nil => simp
  | cons a xs ih =>
    have htail : ∀ b ∈ xs, ∀ t, measure (step t b) ≤ measure t + cost b := by
      intro b hb t
      exact hstep b (List.mem_cons_of_mem a hb) t
    have hh := hstep a (by simp) s
    have ht := ih htail (step s a)
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    omega

lemma range_cost_sum (cost : ℕ → ℕ) (B : ℕ) :
    ((List.range B).map cost).sum = ∑ v ∈ Finset.range B, cost v := by
  induction B with
  | zero => simp
  | succ B ih => simp [List.range_succ, Finset.sum_range_succ, ih]

lemma descending_cost_sum (cost : ℕ → ℕ) (B : ℕ) :
    ((List.range B).reverse.map cost).sum = ∑ v ∈ Finset.range B, cost v := by
  simpa only [List.map_reverse, List.sum_reverse] using range_cost_sum cost B

theorem descending_reverse_budget {σ : Type*}
    (step : σ → ℕ → σ) (measure : σ → ℕ)
    (seeds edges : List (ℕ × ℕ)) (weighted : ℕ → ℕ) (B : ℕ)
    (usedForks : Finset ℕ) (hF : usedForks ⊆ Finset.range B)
    (hpositive : ∀ v ∈ usedForks, 1 ≤ messageCount seeds edges v)
    (hstep : ∀ v ∈ Finset.range B, ∀ s,
      measure (step s v) ≤ measure s + (messageCount seeds edges v - 1) + weighted v)
    (s : σ) :
    measure ((List.range B).reverse.foldl step s) + usedForks.card ≤
      measure s + seeds.length + edges.length + ∑ v ∈ Finset.range B, weighted v := by
  have hfold := foldl_cost_bound step measure
    (fun v => (messageCount seeds edges v - 1) + weighted v) (List.range B).reverse
    (by
      intro v hv t
      have hv' : v ∈ Finset.range B := by simpa using hv
      have hh := hstep v hv' t
      omega) s
  rw [descending_cost_sum, Finset.sum_add_distrib] at hfold
  have hsum := static_aggregate_budget seeds edges B usedForks hF hpositive
  omega

end ReverseBudget

namespace Pilot5bMeta1020ReverseStructure

open Pilot5bMeta1020Linear Pilot5bMeta1020OrAggregate Pilot5bMeta1020Reverse

lemma build_extension (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (k : ℕ) (s : State) :
    ∃ hs, net (build n seeds edges weight k s) = net s ++ hs := by
  induction k generalizing s with
  | zero => exact ⟨[], by simp [build]⟩
  | succ k ih =>
    obtain ⟨hs, he⟩ := step_extension n seeds edges weight k s
    obtain ⟨ts, ht⟩ := ih (step n seeds edges weight k s)
    exact ⟨hs ++ ts, by simpa only [build, he, List.append_assoc] using ht⟩

lemma build_prefix (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (k : ℕ) (s : State) : net s <+: net (build n seeds edges weight k s) := by
  obtain ⟨hs, he⟩ := build_extension n seeds edges weight k s
  exact ⟨hs, he.symm⟩

lemma build_old_read (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (k : ℕ) (s : State) (labels : ℕ → Bool) (y : List Bool) (hy : y.length = n)
    (r : ℕ) (hr : r < n + (net s).length) :
    (run (net (build n seeds edges weight k s)) labels y).getD r false =
      (run (net s) labels y).getD r false := by
  obtain ⟨hs, he⟩ := build_extension n seeds edges weight k s
  rw [he, run_append]
  exact run_getD_lt hs labels _ r (by simpa only [run_length, hy] using hr)

lemma step_fanin (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (v : ℕ) (s : State) (hfan : ∀ us, Sum.inl us ∈ net s → us.length ≤ 2) :
    ∀ us, Sum.inl us ∈ net (step n seeds edges weight v s) → us.length ≤ 2 := by
  have ha := aggregate_fanin n (net s) (incoming seeds edges (message s) v) hfan
  cases hw : weight v with
  | none => simpa only [Pilot5bMeta1020Reverse.step, net, hw] using ha
  | some z =>
    intro us hu
    simp only [Pilot5bMeta1020Reverse.step, hw, net, List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hu
    exact ha us hu

lemma build_fanin (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (k : ℕ) (s : State) (hfan : ∀ us, Sum.inl us ∈ net s → us.length ≤ 2) :
    ∀ us, Sum.inl us ∈ net (build n seeds edges weight k s) → us.length ≤ 2 := by
  induction k generalizing s with
  | zero => exact hfan
  | succ k ih =>
    exact ih (step n seeds edges weight k s) (step_fanin n seeds edges weight k s hfan)

lemma build_length (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (k : ℕ) (s : State) :
    (net (build n seeds edges weight k s)).length = (net s).length +
      ∑ v ∈ Finset.range k, ((incomingCount seeds edges v - 1) +
        (if (weight v).isSome then 1 else 0)) := by
  induction k generalizing s with
  | zero => simp [build]
  | succ k ih =>
    rw [build, ih, step_length, Finset.sum_range_succ]
    omega

lemma build_length_le (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (k : ℕ) (s : State) :
    (net s).length ≤ (net (build n seeds edges weight k s)).length := by
  rw [build_length]
  omega

def weightedCount (weight : ℕ → Option ℕ) (k : ℕ) : ℕ :=
  ∑ v ∈ Finset.range k, if (weight v).isSome then 1 else 0

def usedForks (seeds edges : List (ℕ × ℕ)) (forks : Finset ℕ) : Finset ℕ :=
  forks.filter fun v => 0 < incomingCount seeds edges v

lemma weightedCount_eq_card (weight : ℕ → Option ℕ) (k : ℕ) :
    weightedCount weight k = ((Finset.range k).filter fun v => (weight v).isSome).card := by
  classical
  simp [weightedCount, Finset.sum_boole]

lemma incomingCount_eq_messageCount (seeds edges : List (ℕ × ℕ)) (v : ℕ) :
    incomingCount seeds edges v =
      ReverseBudget.messageCount seeds edges v := rfl

lemma build_budget_used (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (k : ℕ) (s : State) (F : Finset ℕ) (hF : F ⊆ Finset.range k)
    (hpositive : ∀ v ∈ F, 0 < incomingCount seeds edges v) :
    (net (build n seeds edges weight k s)).length + F.card ≤
      (net s).length + seeds.length + edges.length + weightedCount weight k := by
  apply ReverseBudget.static_net_budget
    seeds edges k F hF
  · intro v hv
    simpa only [← incomingCount_eq_messageCount] using (Nat.succ_le_iff.mpr (hpositive v hv))
  · rw [build_length, Finset.sum_add_distrib]
    simp only [weightedCount, incomingCount_eq_messageCount]
    omega

lemma build_budget (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (k : ℕ) (s : State) (forks : Finset ℕ) (hF : forks ⊆ Finset.range k) :
    (net (build n seeds edges weight k s)).length + (usedForks seeds edges forks).card ≤
      (net s).length + seeds.length + edges.length + weightedCount weight k := by
  apply build_budget_used n seeds edges weight k s (usedForks seeds edges forks)
  · exact fun _ hv => hF (Finset.mem_filter.mp hv).1
  · exact fun _ hv => (Finset.mem_filter.mp hv).2

end Pilot5bMeta1020ReverseStructure


namespace Pilot5bMeta1020Fold

open PEqualNP.CircuitLowerBounds

def grow {α β : Type*} (f : List α → β → α) (gs : List β) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [f w g]) w

theorem grow_append {α β : Type*} (f : List α → β → α)
    (gs hs : List β) (w : List α) :
    grow f (gs ++ hs) w = grow f hs (grow f gs w) := by
  simp [grow, List.foldl_append]

theorem grow_prefix {α β : Type*} (f : List α → β → α) (gs : List β) :
    ∀ w : List α, ∃ t : List α, grow f gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [grow], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [f w g])
    refine ⟨f w g :: t, ?_, by simp [hl]⟩
    change grow f gs (w ++ [f w g]) = w ++ f w g :: t
    rw [ht]
    simp

theorem grow_length {α β : Type*} (f : List α → β → α)
    (gs : List β) (w : List α) :
    (grow f gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := grow_prefix f gs w
  rw [ht]
  simp [hl]

theorem grow_getD_lt {α β : Type*} (f : List α → β → α)
    (gs : List β) (w : List α) (i : ℕ) (d : α) (h : i < w.length) :
    (grow f gs w).getD i d = w.getD i d := by
  obtain ⟨t, ht, _⟩ := grow_prefix f gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem grow_getD_ge {α β : Type*} (f : List α → β → α)
    (gs : List β) (w : List α) (i : ℕ) (d : α)
    (h : w.length + gs.length ≤ i) :
    (grow f gs w).getD i d = d := by
  apply List.getD_eq_default
  simpa only [grow_length] using h

theorem grow_snoc {α β : Type*} (f : List α → β → α)
    (gs : List β) (g : β) (w : List α) :
    grow f (gs ++ [g]) w = grow f gs w ++ [f (grow f gs w) g] := by
  simp [grow, List.foldl_append]

theorem grow_gate {α β : Type*} (f : List α → β → α)
    (gs : List β) (w : List α) (d : α) (j : ℕ) (hj : j < gs.length) :
    (grow f gs w).getD (w.length + j) d = f (grow f (gs.take j) w) gs[j] := by
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by simp
  set A := grow f (gs.take j) w with hA
  have hAl : A.length = w.length + j := by
    rw [hA, grow_length]
    simp
    omega
  have hw : grow f gs w = grow f (gs.drop (j + 1)) (A ++ [f A gs[j]]) := by
    conv_lhs => rw [hsplit]
    rw [grow_append]
    rfl
  rw [hw, grow_getD_lt _ _ _ _ _ (by simp [hAl]),
    List.getD_append_right _ _ _ _ (by omega)]
  simp [hAl]

theorem grow_take_read {α β : Type*} (f : List α → β → α)
    (gs : List β) (w : List α) (d : α) (j i : ℕ) (hj : j ≤ gs.length) :
    (grow f (gs.take j) w).getD i d =
      if i < w.length + j then (grow f gs w).getD i d else d := by
  have hlen : (grow f (gs.take j) w).length = w.length + j := by
    rw [grow_length, List.length_take, Nat.min_eq_left hj]
  by_cases hi : i < w.length + j
  · rw [ite_eq_left hi]
    conv_rhs => rw [← List.take_append_drop j gs, grow_append]
    exact (grow_getD_lt _ _ _ _ _ (by omega)).symm
  · rw [ite_eq_right hi]
    apply List.getD_eq_default
    omega

def gateValue (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def initialDegrees (n : ℕ) (marked : Finset ℕ) : List ℕ :=
  (List.range n).map fun i => if i ∈ marked then 1 else 0

theorem wires_eq_grow (C : Circuit) (x : List Bool) :
    C.wires x = grow gateValue C.gates x := rfl

theorem lineDegrees_eq_grow (C : Circuit) (n : ℕ) (marked : Finset ℕ) :
    C.lineDegrees n marked = grow (fun d g => g.lineDegree d) C.gates
      (initialDegrees n marked) := rfl

@[local simp] theorem initialDegrees_length (n : ℕ) (marked : Finset ℕ) :
    (initialDegrees n marked).length = n := by simp [initialDegrees]

theorem wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.size := by
  rw [wires_eq_grow, grow_length]
  rfl

theorem lineDegrees_length (C : Circuit) (n : ℕ) (marked : Finset ℕ) :
    (C.lineDegrees n marked).length = n + C.size := by
  rw [lineDegrees_eq_grow, grow_length, initialDegrees_length]
  rfl

theorem wires_input (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false := grow_getD_lt _ _ _ _ _ hi

theorem wires_gate_prefix (C : Circuit) (x : List Bool)
    (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false =
      gateValue (grow gateValue (C.gates.take j) x) C.gates[j] :=
  grow_gate _ _ _ _ _ hj

theorem lineDegrees_gate_prefix (C : Circuit) (n : ℕ) (marked : Finset ℕ)
    (j : ℕ) (hj : j < C.gates.length) :
    (C.lineDegrees n marked).getD (n + j) 0 =
      C.gates[j].lineDegree
        (grow (fun d g => g.lineDegree d) (C.gates.take j) (initialDegrees n marked)) := by
  rw [lineDegrees_eq_grow]
  simpa only [initialDegrees_length] using
    grow_gate (fun d g => g.lineDegree d) C.gates (initialDegrees n marked) 0 j hj

theorem wires_gate (C : Circuit) (x : List Bool)
    (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false =
      C.gates[j].op.eval (C.gates[j].inputs.map fun i =>
        if i < x.length + j then (C.wires x).getD i false else false) := by
  rw [wires_gate_prefix C x j hj]
  unfold gateValue
  congr 1
  apply List.map_congr_left
  intro i _
  exact grow_take_read _ _ _ _ j i (Nat.le_of_lt hj)

end Pilot5bMeta1020Fold

namespace OriginalGraph

open PEqualNP.CircuitLowerBounds
open OneLineCoefficient

def bound (N : ℕ) (C : Circuit) : ℕ := N + N + C.size

def degrees (N : ℕ) (C : Circuit) : List ℕ :=
  C.lineDegrees (N + N) (Finset.Ico N (N + N))

def degree (N : ℕ) (C : Circuit) (r : ℕ) : ℕ := (degrees N C).getD r 0

def readDegree (N : ℕ) (C : Circuit) (w r : ℕ) : ℕ :=
  if r < w then degree N C r else 0

def gateAt (N : ℕ) (C : Circuit) (w : ℕ) : Option Gate :=
  if N + N ≤ w then C.gates[w - (N + N)]? else none

def children (N : ℕ) (C : Circuit) (w : ℕ) : List ℕ :=
  match gateAt N C w with
  | none => []
  | some g => if degree N C w = 2 then
      g.inputs.filter (fun r => decide (r < w ∧ degree N C r = 2)) else []

def edges (N : ℕ) (C : Circuit) : List (ℕ × ℕ) :=
  (List.range (bound N C)).flatMap (fun w => (children N C w).map (fun r => (w, r)))

def weight (N : ℕ) (C : Circuit) (w : ℕ) : Option ℕ :=
  match gateAt N C w with
  | none => none
  | some g => if degree N C w = 2 then
      match g.op with
      | .and => (g.inputs.find? (fun r => decide (readDegree N C w r = 0))).map
          (fun r => if r < w then r else bound N C)
      | _ => none
    else none

def ForkWith (N : ℕ) (C : Circuit) (w a b : ℕ) : Prop :=
  ∃ g, gateAt N C w = some g ∧ g.op = .and ∧ g.inputs = [a, b] ∧
    readDegree N C w a = 1 ∧ readDegree N C w b = 1

def Fork (N : ℕ) (C : Circuit) (w : ℕ) : Prop := ∃ a b, ForkWith N C w a b

def gateWeight (g : Gate) (d : List ℕ) : Option ℕ :=
  match g.op with
  | .and => g.inputs.find? (fun r => decide (d.getD r 0 = 0))
  | _ => none

def active (z : List Bool) (v : Option ℕ) : Bool :=
  v.elim true (fun r => z.getD r false)

lemma value_and_pair (a b : ℕ) (w : List Bool) :
    value ⟨.and, [a, b]⟩ w = (w.getD a false && w.getD b false) := by
  simp only [value, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
    List.all_nil, id_eq, Bool.and_true]

lemma gateWeight_pair (a b : ℕ) (d : List ℕ) :
    gateWeight ⟨.and, [a, b]⟩ d =
      if d.getD a 0 = 0 then some a else if d.getD b 0 = 0 then some b else none := by
  by_cases ha : d.getD a 0 = 0 <;> by_cases hb : d.getD b 0 = 0 <;>
    simp only [gateWeight, List.find?_cons, List.find?_nil, ha, hb,
      decide_true, decide_false, ite_true, ite_false]

lemma gateWeight_single (a : ℕ) (d : List ℕ) :
    gateWeight ⟨.and, [a]⟩ d = if d.getD a 0 = 0 then some a else none := by
  by_cases ha : d.getD a 0 = 0 <;>
    simp only [gateWeight, List.find?_cons, List.find?_nil, ha,
      decide_true, decide_false, ite_true, ite_false]

lemma gate_up (g : Gate) (z p w : List Bool) (d : List ℕ)
    (hm : g.op = .and ∨ g.op = .or) (hl : g.inputs.length ≤ 2)
    (h : AllAt z p w d) (hd : g.lineDegree d = 2)
    (r : ℕ) (hr : r ∈ g.inputs) (hrd : d.getD r 0 = 2)
    (hrw : w.getD r false = true) (hz : active z (gateWeight g d) = true) :
    value g w = true := by
  rcases g with ⟨op, ins⟩
  change op = .and ∨ op = .or at hm
  change ins.length ≤ 2 at hl
  change r ∈ ins at hr
  rcases hm with rfl | rfl
  · cases ins with
    | nil => simp at hr
    | cons a as =>
      cases as with
      | nil =>
        simp only [List.mem_singleton] at hr
        subst r
        simpa [value, GateOp.eval] using hrw
      | cons b bs =>
        cases bs with
        | nil =>
          have hab : d.getD a 0 + d.getD b 0 = 2 := by simpa [Gate.lineDegree] using hd
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · have hb0 : d.getD b 0 = 0 := by omega
            have hzb : z.getD b false = true := by
              rw [gateWeight_pair, hrd, hb0] at hz
              exact hz
            have hwb := (h b).1 hzb
            rw [value_and_pair, hrw, hwb]
            rfl
          · have ha0 : d.getD a 0 = 0 := by omega
            have hza : z.getD a false = true := by
              rw [gateWeight_pair, ha0] at hz
              exact hz
            have hwa := (h a).1 hza
            rw [value_and_pair, hwa, hrw]
            rfl
        | cons c cs => simp only [List.length_cons] at hl; omega
  · have hmem : true ∈ ins.map (fun i => w.getD i false) := List.mem_map.mpr ⟨r, hr, hrw⟩
    simpa [value, GateOp.eval, List.any_eq_true] using hmem

lemma fork_coeff_true {za pa wa zb pb wb : Bool}
    (ha : At za pa wa 1) (hb : At zb pb wb 1)
    (hw : (wa && wb) = true) (hz : (za && zb) = false)
    (hp : ((za && pb) || (pa && zb)) = false) : pa = true ∧ pb = true := by
  have hea := ha.2.2.2 (by omega)
  have heb := hb.2.2.2 (by omega)
  rw [Bool.and_eq_true] at hw
  obtain ⟨rfl, rfl⟩ := hw
  clear ha hb
  cases za <;> cases zb <;> cases pa <;> cases pb <;>
    first | contradiction | exact ⟨rfl, rfl⟩

lemma gate_down (g : Gate) (z p w : List Bool) (d : List ℕ)
    (hm : g.op = .and ∨ g.op = .or) (hl : g.inputs.length ≤ 2)
    (h : AllAt z p w d) (hd : g.lineDegree d = 2)
    (hw : value g w = true) (hz : value g z = false) (hp : coeff g z p = false) :
    (∃ a b, g.op = .and ∧ g.inputs = [a, b] ∧ d.getD a 0 = 1 ∧ d.getD b 0 = 1 ∧
      p.getD a false = true ∧ p.getD b false = true) ∨
    ∃ r ∈ g.inputs, d.getD r 0 = 2 ∧ w.getD r false = true ∧
      z.getD r false = false ∧ p.getD r false = false ∧ active z (gateWeight g d) = true := by
  rcases g with ⟨op, ins⟩
  change op = .and ∨ op = .or at hm
  change ins.length ≤ 2 at hl
  rcases hm with rfl | rfl
  · cases ins with
    | nil => simp [Gate.lineDegree] at hd
    | cons a as =>
      cases as with
      | nil =>
        have ha2 : d.getD a 0 = 2 := by simpa [Gate.lineDegree] using hd
        right
        refine ⟨a, by simp, ha2, ?_, ?_, ?_, ?_⟩
        · simpa [value, GateOp.eval] using hw
        · simpa [value, GateOp.eval] using hz
        · simpa [coeff] using hp
        · rw [gateWeight_single, ha2]
          rfl
      | cons b bs =>
        cases bs with
        | nil =>
          have hab : d.getD a 0 + d.getD b 0 = 2 := by simpa [Gate.lineDegree] using hd
          have hwpair : w.getD a false = true ∧ w.getD b false = true := by
            simpa only [value_and_pair, Bool.and_eq_true] using hw
          have hwa := hwpair.1
          have hwb := hwpair.2
          by_cases ha0 : d.getD a 0 = 0
          · have hb2 : d.getD b 0 = 2 := by omega
            have hza : z.getD a false = true := (at_zero_value (h a) ha0).symm.trans hwa
            have hpa : p.getD a false = false := (h a).2.2.1 ha0
            right
            refine ⟨b, by simp, hb2, hwb, ?_, ?_, ?_⟩
            · rw [value_and_pair, hza] at hz
              exact hz
            · change ((z.getD a false && p.getD b false) || (p.getD a false && z.getD b false)) = false at hp
              rw [hza, hpa] at hp
              simpa only [Bool.true_and, Bool.false_and, Bool.or_false] using hp
            · rw [gateWeight_pair, ha0]
              exact hza
          · by_cases hb0 : d.getD b 0 = 0
            · have ha2 : d.getD a 0 = 2 := by omega
              have hzb : z.getD b false = true := (at_zero_value (h b) hb0).symm.trans hwb
              have hpb : p.getD b false = false := (h b).2.2.1 hb0
              right
              refine ⟨a, by simp, ha2, hwa, ?_, ?_, ?_⟩
              · rw [value_and_pair, hzb] at hz
                simpa only [Bool.and_true] using hz
              · change ((z.getD a false && p.getD b false) || (p.getD a false && z.getD b false)) = false at hp
                rw [hzb, hpb] at hp
                simpa only [Bool.and_false, Bool.and_true, Bool.false_or] using hp
              · rw [gateWeight_pair, ha2, hb0]
                exact hzb
            · have ha1 : d.getD a 0 = 1 := by omega
              have hb1 : d.getD b 0 = 1 := by omega
              left
              refine ⟨a, b, rfl, rfl, ha1, hb1, ?_⟩
              apply fork_coeff_true (by simpa only [ha1] using h a) (by simpa only [hb1] using h b)
              · simpa [value, GateOp.eval] using hw
              · simpa [value, GateOp.eval] using hz
              · exact hp
        | cons c cs => simp only [List.length_cons] at hl; omega
  · have hsome : ∃ r ∈ ins, w.getD r false = true := by simpa [value, GateOp.eval, List.any_eq_true] using hw
    obtain ⟨r, hr, hrw⟩ := hsome
    have hrz : z.getD r false = false := by
      have hall : ∀ r ∈ ins, z.getD r false = false := by simpa [value, GateOp.eval, List.any_eq_false] using hz
      exact hall r hr
    have hrp : p.getD r false = false := by
      have hall : ∀ r ∈ ins, p.getD r false = false := by simpa [coeff, List.any_eq_false] using hp
      exact hall r hr
    have hrle : d.getD r 0 ≤ 2 := by
      have he := input_degree_le ⟨.or, ins⟩ d r (Or.inr rfl) hl hr
      omega
    have hr2 : d.getD r 0 = 2 := by
      by_contra hh
      have hle : d.getD r 0 ≤ 1 := by omega
      have he := (h r).2.2.2 hle
      rw [hrw, hrz, hrp] at he
      contradiction
    exact Or.inr ⟨r, hr, hr2, hrw, hrz, hrp, by simp [active, gateWeight]⟩

lemma getD_take_guard {α : Type*} (xs : List α) (n i : ℕ) (d : α) :
    (xs.take n).getD i d = if i < n then xs.getD i d else d := by
  by_cases hi : i < n
  · rw [ite_eq_left hi]
    change ((xs.take n)[i]?).getD d = (xs[i]?).getD d
    rw [List.getElem?_take_of_lt hi]
  · rw [ite_eq_right hi]
    apply List.getD_eq_default
    have hn : (xs.take n).length ≤ n := by simp
    omega

lemma take_allAt (z p w : List Bool) (d : List ℕ) (n : ℕ) (h : AllAt z p w d) :
    AllAt (z.take n) (p.take n) (w.take n) (d.take n) := by
  intro i
  simp only [getD_take_guard]
  by_cases hi : i < n
  · simpa only [ite_eq_left hi] using h i
  · simpa only [ite_eq_right hi] using at_false

lemma fold_p_extends (gs : List Gate) (s : State) :
    ∃ t, (gs.foldl step s).2.1 = s.2.1 ++ t ∧ t.length = gs.length := by
  induction gs generalizing s with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    obtain ⟨t, ht, hlen⟩ := ih (step s g)
    refine ⟨coeff g s.1 s.2.1 :: t, ?_, by simp [hlen]⟩
    change (gs.foldl step (step s g)).2.1 = _
    rw [ht]
    simp [step, List.append_assoc]

lemma fold_z_extends (gs : List Gate) (s : State) :
    ∃ t, (gs.foldl step s).1 = s.1 ++ t ∧ t.length = gs.length := by
  induction gs generalizing s with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    obtain ⟨t, ht, hlen⟩ := ih (step s g)
    refine ⟨value g s.1 :: t, ?_, by simp [hlen]⟩
    change (gs.foldl step (step s g)).1 = _
    rw [ht]
    simp [step, List.append_assoc]

lemma fold_p_take (gs : List Gate) (s : State) (j : ℕ) (hj : j ≤ gs.length) :
    ((gs.take j).foldl step s).2.1 = (gs.foldl step s).2.1.take (s.2.1.length + j) := by
  have hlen : ((gs.take j).foldl step s).2.1.length = s.2.1.length + j := by
    simpa only [List.length_take, Nat.min_eq_left hj] using (fold_lengths (gs.take j) s).2.1
  obtain ⟨t, ht, _⟩ := fold_p_extends (gs.drop j) ((gs.take j).foldl step s)
  have heq : (gs.foldl step s).2.1 = ((gs.take j).foldl step s).2.1 ++ t := by
    conv_lhs => rw [← List.take_append_drop j gs, List.foldl_append]
    exact ht
  rw [heq, ← hlen]
  simp

lemma fold_z_take (gs : List Gate) (s : State) (j : ℕ) (hj : j ≤ gs.length) :
    ((gs.take j).foldl step s).1 = (gs.foldl step s).1.take (s.1.length + j) := by
  have hlen : ((gs.take j).foldl step s).1.length = s.1.length + j := by
    simpa only [List.length_take, Nat.min_eq_left hj] using (fold_lengths (gs.take j) s).1
  obtain ⟨t, ht, _⟩ := fold_z_extends (gs.drop j) ((gs.take j).foldl step s)
  have heq : (gs.foldl step s).1 = ((gs.take j).foldl step s).1 ++ t := by
    conv_lhs => rw [← List.take_append_drop j gs, List.foldl_append]
    exact ht
  rw [heq, ← hlen]
  simp

lemma fold_p_gate (gs : List Gate) (s : State) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl step s).2.1.getD (s.2.1.length + j) false =
      coeff gs[j] ((gs.take j).foldl step s).1 ((gs.take j).foldl step s).2.1 := by
  let pre := (gs.take j).foldl step s
  have hlen : pre.2.1.length = s.2.1.length + j := by
    simpa only [pre, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)] using
      (fold_lengths (gs.take j) s).2.1
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by simp
  have hfull : gs.foldl step s = (gs.drop (j + 1)).foldl step (step pre gs[j]) := by
    conv_lhs => rw [hsplit, List.foldl_append]
    rfl
  rw [hfull, fold_p_getD _ _ _ (by simp only [step, List.length_append, List.length_singleton]; omega)]
  change (pre.2.1 ++ [coeff gs[j] pre.1 pre.2.1]).getD (s.2.1.length + j) false = _
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp [hlen, pre]

lemma fold_p_gate_take (gs : List Gate) (s : State) (j : ℕ) (hj : j < gs.length)
    (hlen : s.1.length = s.2.1.length) :
    (gs.foldl step s).2.1.getD (s.2.1.length + j) false =
      coeff gs[j] ((gs.foldl step s).1.take (s.2.1.length + j))
        ((gs.foldl step s).2.1.take (s.2.1.length + j)) := by
  rw [fold_p_gate gs s j hj, fold_z_take gs s j (Nat.le_of_lt hj),
    fold_p_take gs s j (Nat.le_of_lt hj), hlen]

lemma grow_take_eq {α β : Type*} (f : List α → β → α) (gs : List β)
    (xs : List α) (j : ℕ) (hj : j ≤ gs.length) :
    Pilot5bMeta1020Fold.grow f (gs.take j) xs =
      (Pilot5bMeta1020Fold.grow f gs xs).take (xs.length + j) := by
  obtain ⟨t, ht, _⟩ := Pilot5bMeta1020Fold.grow_prefix f (gs.drop j)
    (Pilot5bMeta1020Fold.grow f (gs.take j) xs)
  have hlen : (Pilot5bMeta1020Fold.grow f (gs.take j) xs).length = xs.length + j := by
    simp only [Pilot5bMeta1020Fold.grow_length, List.length_take, Nat.min_eq_left hj]
  have heq : Pilot5bMeta1020Fold.grow f gs xs =
      Pilot5bMeta1020Fold.grow f (gs.take j) xs ++ t := by
    conv_lhs => rw [← List.take_append_drop j gs, Pilot5bMeta1020Fold.grow_append]
    exact ht
  rw [heq, ← hlen]
  simp

lemma wires_gate_take (C : Circuit) (xs : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires xs).getD (xs.length + j) false = value C.gates[j] ((C.wires xs).take (xs.length + j)) := by
  rw [Pilot5bMeta1020Fold.wires_gate_prefix C xs j hj,
    grow_take_eq _ _ _ _ (Nat.le_of_lt hj)]
  rfl

lemma degrees_gate_take (N : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    degree N C (N + N + j) = C.gates[j].lineDegree ((degrees N C).take (N + N + j)) := by
  unfold degree degrees
  rw [Pilot5bMeta1020Fold.lineDegrees_gate_prefix C (N + N) _ j hj,
    grow_take_eq _ _ _ _ (Nat.le_of_lt hj), Pilot5bMeta1020Fold.initialDegrees_length]
  rfl

lemma initial_degrees (N : ℕ) :
    Pilot5bMeta1020Fold.initialDegrees (N + N) (Finset.Ico N (N + N)) =
      List.replicate N 0 ++ List.replicate N 1 := by
  unfold Pilot5bMeta1020Fold.initialDegrees
  rw [List.range_add, List.map_append, List.map_map]
  have h0 : (List.range N).map (fun i => if i ∈ Finset.Ico N (N + N) then 1 else 0) =
      List.replicate N 0 := by
    calc
      _ = (List.range N).map (fun _ => 0) := by
        apply List.map_congr_left
        intro i hi
        have hi' := List.mem_range.mp hi
        have hn : i ∉ Finset.Ico N (N + N) := by simp only [Finset.mem_Ico]; omega
        simp only [ite_eq_right hn]
      _ = _ := by simp
  have h1 : (List.range N).map (fun i => if N + i ∈ Finset.Ico N (N + N) then 1 else 0) =
      List.replicate N 1 := by
    calc
      _ = (List.range N).map (fun _ => 1) := by
        apply List.map_congr_left
        intro i hi
        have hi' := List.mem_range.mp hi
        have hn : N + i ∈ Finset.Ico N (N + N) := by simp only [Finset.mem_Ico]; omega
        simp only [ite_eq_left hn]
      _ = _ := by simp
  exact congrArg₂ List.append h0 h1

def fullState (C : Circuit) (x y : List Bool) : State := C.gates.foldl step (initial x y)

def zeroValues (N : ℕ) (C : Circuit) (x : List Bool) : List Bool :=
  C.wires (x ++ List.replicate N false)

def positiveValues (C : Circuit) (x y : List Bool) : List Bool := (fullState C x y).2.1

def fullValues (C : Circuit) (x y : List Bool) : List Bool := C.wires (x ++ y)

lemma fullState_zero (N : ℕ) (C : Circuit) (x y : List Bool) (hy : y.length = N) :
    (fullState C x y).1 = zeroValues N C x := by
  rw [fullState, fold_zero_eq]
  simp only [initial, hy]
  rfl

lemma fullState_full (C : Circuit) (x y : List Bool) :
    (fullState C x y).2.2.1 = fullValues C x y :=
  fold_full_eq C.gates (initial x y)

lemma fullState_degrees (N : ℕ) (C : Circuit) (x y : List Bool)
    (hx : x.length = N) (hy : y.length = N) :
    (fullState C x y).2.2.2 = degrees N C := by
  rw [fullState, fold_degree_eq]
  simp only [initial, hx, hy]
  rw [← initial_degrees N]
  rfl

lemma actual_allAt (N : ℕ) (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N) :
    AllAt (zeroValues N C x) (positiveValues C x y) (fullValues C x y) (degrees N C) := by
  have h := (circuit_fold_valid C hm x y).2.2.2
  change AllAt (fullState C x y).1 (positiveValues C x y) (fullState C x y).2.2.1
    (fullState C x y).2.2.2 at h
  rwa [fullState_zero N C x y hy, fullState_full C x y, fullState_degrees N C x y hx hy] at h

lemma positive_gate_take (N : ℕ) (C : Circuit) (x y : List Bool)
    (hx : x.length = N) (hy : y.length = N) (j : ℕ) (hj : j < C.gates.length) :
    (positiveValues C x y).getD (N + N + j) false =
      coeff C.gates[j] ((zeroValues N C x).take (N + N + j))
        ((positiveValues C x y).take (N + N + j)) := by
  have heq := fold_p_gate_take C.gates (initial x y) j hj (by simp [initial])
  change (positiveValues C x y).getD _ false = coeff _ ((fullState C x y).1.take _)
    ((positiveValues C x y).take _) at heq
  rw [fullState_zero N C x y hy] at heq
  simpa only [initial, List.length_append, List.length_replicate, hx, hy] using heq

lemma prefix_degree_read (N : ℕ) (C : Circuit) (j r : ℕ) (hj : j ≤ C.gates.length) :
    (Pilot5bMeta1020Fold.grow (fun d g => g.lineDegree d) (C.gates.take j)
      (Pilot5bMeta1020Fold.initialDegrees (N + N) (Finset.Ico N (N + N)))).getD r 0 =
      readDegree N C (N + N + j) r := by
  rw [grow_take_eq _ _ _ _ hj, Pilot5bMeta1020Fold.initialDegrees_length,
    getD_take_guard]
  rfl

lemma take_degree_read (N : ℕ) (C : Circuit) (w r : ℕ) :
    ((degrees N C).take w).getD r 0 = readDegree N C w r :=
  getD_take_guard (degrees N C) w r 0

lemma gateAt_index (N : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt N C (N + N + j) = some C.gates[j] := by
  simp [gateAt, hj]

lemma gateAt_some (N : ℕ) (C : Circuit) (w : ℕ) (g : Gate)
    (hg : gateAt N C w = some g) :
    ∃ j : ℕ, ∃ hj : j < C.gates.length, w = N + N + j ∧ C.gates[j] = g := by
  unfold gateAt at hg
  split_ifs at hg with hw
  · obtain ⟨hj, heq⟩ := List.getElem?_eq_some_iff.mp hg
    exact ⟨w - (N + N), hj, by omega, heq⟩

lemma gateAt_degree (N : ℕ) (C : Circuit) (w : ℕ) (g : Gate)
    (hg : gateAt N C w = some g) :
    degree N C w = g.lineDegree ((degrees N C).take w) := by
  obtain ⟨j, hj, rfl, rfl⟩ := gateAt_some N C w g hg
  exact degrees_gate_take N C j hj

lemma gateAt_mono (N : ℕ) (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (w : ℕ) (g : Gate) (hg : gateAt N C w = some g) :
    (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  obtain ⟨j, hj, _, rfl⟩ := gateAt_some N C w g hg
  obtain ⟨hop, hlen⟩ := hm C.gates[j] (List.getElem_mem hj)
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hop, hlen⟩

lemma fork_degree (N : ℕ) (C : Circuit) (w : ℕ) (hf : Fork N C w) : degree N C w = 2 := by
  obtain ⟨a, b, g, hg, hop, hins, ha, hb⟩ := hf
  rw [gateAt_degree N C w g hg]
  rcases g with ⟨op, ins⟩
  change op = .and at hop
  change ins = [a, b] at hins
  subst op
  subst ins
  simp only [Gate.lineDegree, ite_true, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, take_degree_read, ha, hb]
  rfl

lemma children_of_gateAt (N : ℕ) (C : Circuit) (w r : ℕ) (g : Gate)
    (hg : gateAt N C w = some g) (hd : degree N C w = 2) :
    r ∈ children N C w ↔ r ∈ g.inputs ∧ r < w ∧ degree N C r = 2 := by
  simp [children, hg, hd]

lemma mem_edges (N : ℕ) (C : Circuit) (w r : ℕ) :
    (w, r) ∈ edges N C ↔ w < bound N C ∧ r ∈ children N C w := by
  simp [edges]

lemma degrees_length (N : ℕ) (C : Circuit) : (degrees N C).length = bound N C :=
  Pilot5bMeta1020Fold.lineDegrees_length C (N + N) _

lemma zeroValues_length (N : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = N) :
    (zeroValues N C x).length = bound N C := by
  simp only [zeroValues, Pilot5bMeta1020Fold.wires_length, List.length_append,
    List.length_replicate, hx, bound]

lemma fullValues_length (N : ℕ) (C : Circuit) (x y : List Bool)
    (hx : x.length = N) (hy : y.length = N) : (fullValues C x y).length = bound N C := by
  simp only [fullValues, Pilot5bMeta1020Fold.wires_length, List.length_append, hx, hy, bound]

lemma positiveValues_length (N : ℕ) (C : Circuit) (x y : List Bool)
    (hx : x.length = N) (hy : y.length = N) : (positiveValues C x y).length = bound N C := by
  have h := (fold_lengths C.gates (initial x y)).2.1
  simpa only [positiveValues, fullState, initial, List.length_append, List.length_replicate,
    hx, hy, bound, Circuit.size] using h

lemma degree_input_le_one (N : ℕ) (C : Circuit) (r : ℕ) (hr : r < N + N) :
    degree N C r ≤ 1 := by
  unfold degree degrees
  rw [Pilot5bMeta1020Fold.lineDegrees_eq_grow,
    Pilot5bMeta1020Fold.grow_getD_lt _ _ _ _ _ (by simpa only [Pilot5bMeta1020Fold.initialDegrees_length] using hr)]
  rw [List.getD_eq_getElem _ _ (by simpa only [Pilot5bMeta1020Fold.initialDegrees_length] using hr)]
  simp only [Pilot5bMeta1020Fold.initialDegrees, List.getElem_map, List.getElem_range]
  split_ifs <;> omega

lemma degree_two_bounds (N : ℕ) (C : Circuit) (w : ℕ) (hd : degree N C w = 2) :
    N + N ≤ w ∧ w < bound N C := by
  constructor
  · by_contra h
    have he := degree_input_le_one N C w (by omega)
    omega
  · by_contra h
    have he : degree N C w = 0 :=
      List.getD_eq_default (degrees N C) 0 (by rw [degrees_length]; omega)
    omega

lemma degree_two_gateAt (N : ℕ) (C : Circuit) (w : ℕ) (hd : degree N C w = 2) :
    ∃ g, gateAt N C w = some g := by
  obtain ⟨hlo, hhi⟩ := degree_two_bounds N C w hd
  have hj : w - (N + N) < C.gates.length := by unfold bound Circuit.size at hhi; omega
  refine ⟨C.gates[w - (N + N)], ?_⟩
  have heq : w = N + N + (w - (N + N)) := by omega
  conv_lhs => rw [heq]
  exact gateAt_index N C (w - (N + N)) hj

lemma children_spec (N : ℕ) (C : Circuit) (w r : ℕ) (hr : r ∈ children N C w) :
    ∃ g, gateAt N C w = some g ∧ degree N C w = 2 ∧ r ∈ g.inputs ∧
      r < w ∧ degree N C r = 2 := by
  cases hg : gateAt N C w with
  | none => simp [children, hg] at hr
  | some g =>
    by_cases hd : degree N C w = 2
    · exact ⟨g, rfl, hd, (children_of_gateAt N C w r g hg hd).mp hr⟩
    · simp [children, hg, hd] at hr

lemma edge_bounds (N : ℕ) (C : Circuit) (w r : ℕ) (he : (w, r) ∈ edges N C) :
    r < w ∧ w < bound N C ∧ degree N C w = 2 ∧ degree N C r = 2 := by
  obtain ⟨hw, hr⟩ := (mem_edges N C w r).mp he
  obtain ⟨g, _, hd, _, hlt, hr2⟩ := children_spec N C w r hr
  exact ⟨hlt, hw, hd, hr2⟩

lemma fork_children (N : ℕ) (C : Circuit) (w a b : ℕ) (hf : ForkWith N C w a b) :
    a < w ∧ b < w ∧ w < bound N C ∧ degree N C a = 1 ∧ degree N C b = 1 := by
  have hwa := degree_two_bounds N C w (fork_degree N C w ⟨a, b, hf⟩)
  obtain ⟨g, hg, _, _, ha, hb⟩ := hf
  have hal : a < w := by unfold readDegree at ha; split_ifs at ha; omega
  have hbl : b < w := by unfold readDegree at hb; split_ifs at hb; omega
  exact ⟨hal, hbl, hwa.2, by simpa only [readDegree, ite_eq_left hal] using ha,
    by simpa only [readDegree, ite_eq_left hbl] using hb⟩

lemma weight_gateAt (N : ℕ) (C : Circuit) (w : ℕ) (g : Gate)
    (hg : gateAt N C w = some g) (hd : degree N C w = 2) :
    weight N C w = (gateWeight g ((degrees N C).take w)).map
      (fun r => if r < w then r else bound N C) := by
  have hfun : (fun r => decide (readDegree N C w r = 0)) =
      (fun r => decide (((degrees N C).take w).getD r 0 = 0)) := by
    funext r
    rw [take_degree_read]
  unfold weight
  simp only [hg, hd, ite_true]
  cases hop : g.op <;> simp only [hop, gateWeight, hfun, Option.map_none]

lemma active_weight (N : ℕ) (C : Circuit) (w : ℕ) (g : Gate) (z : List Bool)
    (hz : z.length = bound N C) (hg : gateAt N C w = some g) (hd : degree N C w = 2) :
    active z (weight N C w) = active (z.take w) (gateWeight g ((degrees N C).take w)) := by
  rw [weight_gateAt N C w g hg hd]
  cases hv : gateWeight g ((degrees N C).take w) with
  | none => rfl
  | some r =>
    simp only [Option.map_some, active, Option.elim_some, getD_take_guard]
    by_cases hr : r < w
    · simp only [ite_eq_left hr]
    · simp only [ite_eq_right hr]
      exact List.getD_eq_default z false (by omega)

lemma gateAt_full (N : ℕ) (C : Circuit) (x y : List Bool)
    (hx : x.length = N) (hy : y.length = N) (w : ℕ) (g : Gate)
    (hg : gateAt N C w = some g) :
    (fullValues C x y).getD w false = value g ((fullValues C x y).take w) := by
  obtain ⟨j, hj, rfl, rfl⟩ := gateAt_some N C w g hg
  simpa only [fullValues, List.length_append, hx, hy] using wires_gate_take C (x ++ y) j hj

lemma gateAt_zero (N : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = N)
    (w : ℕ) (g : Gate) (hg : gateAt N C w = some g) :
    (zeroValues N C x).getD w false = value g ((zeroValues N C x).take w) := by
  obtain ⟨j, hj, rfl, rfl⟩ := gateAt_some N C w g hg
  simpa only [zeroValues, List.length_append, List.length_replicate, hx] using
    wires_gate_take C (x ++ List.replicate N false) j hj

lemma gateAt_positive (N : ℕ) (C : Circuit) (x y : List Bool)
    (hx : x.length = N) (hy : y.length = N) (w : ℕ) (g : Gate)
    (hg : gateAt N C w = some g) :
    (positiveValues C x y).getD w false =
      coeff g ((zeroValues N C x).take w) ((positiveValues C x y).take w) := by
  obtain ⟨j, hj, rfl, rfl⟩ := gateAt_some N C w g hg
  exact positive_gate_take N C x y hx hy j hj

lemma edge_up (N : ℕ) (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (w r : ℕ) (he : (w, r) ∈ edges N C)
    (hz : active (zeroValues N C x) (weight N C w) = true)
    (hr : (fullValues C x y).getD r false = true) :
    (fullValues C x y).getD w false = true := by
  obtain ⟨_, hc⟩ := (mem_edges N C w r).mp he
  obtain ⟨g, hg, hd, hri, hlt, hr2⟩ := children_spec N C w r hc
  obtain ⟨hgm, hgl⟩ := gateAt_mono N C hm w g hg
  have hat := take_allAt _ _ _ _ w (actual_allAt N C hm x y hx hy)
  have hgd : g.lineDegree ((degrees N C).take w) = 2 := by rwa [← gateAt_degree N C w g hg]
  have hrd : ((degrees N C).take w).getD r 0 = 2 := by
    rw [take_degree_read, readDegree, ite_eq_left hlt]
    exact hr2
  have hrw : ((fullValues C x y).take w).getD r false = true := by
    rw [getD_take_guard, ite_eq_left hlt]
    exact hr
  rw [active_weight N C w g _ (zeroValues_length N C x hx) hg hd] at hz
  rw [gateAt_full N C x y hx hy w g hg]
  exact gate_up g _ _ _ _ hgm hgl hat hgd r hri hrd hrw hz

lemma fork_full (N : ℕ) (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (w a b : ℕ) (hf : ForkWith N C w a b)
    (ha : (positiveValues C x y).getD a false = true)
    (hb : (positiveValues C x y).getD b false = true) :
    (fullValues C x y).getD w false = true := by
  have hc := fork_children N C w a b hf
  have hi := actual_allAt N C hm x y hx hy
  have hwa := (hi a).2.1 ha
  have hwb := (hi b).2.1 hb
  obtain ⟨g, hg, hop, hins, _, _⟩ := hf
  rw [gateAt_full N C x y hx hy w g hg]
  rcases g with ⟨op, ins⟩
  change op = .and at hop
  change ins = [a, b] at hins
  subst op
  subst ins
  rw [value_and_pair, getD_take_guard, getD_take_guard, ite_eq_left hc.1,
    ite_eq_left hc.2.1, hwa, hwb]
  rfl

def Residual (N : ℕ) (C : Circuit) (x y : List Bool) (w : ℕ) : Prop :=
  degree N C w = 2 ∧ (fullValues C x y).getD w false = true ∧
    (zeroValues N C x).getD w false = false ∧ (positiveValues C x y).getD w false = false

def ActiveEdge (N : ℕ) (C : Circuit) (x : List Bool) (w r : ℕ) : Prop :=
  (w, r) ∈ edges N C ∧ active (zeroValues N C x) (weight N C w) = true

lemma edge_down (N : ℕ) (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (w : ℕ) (hw : Residual N C x y w) :
    (∃ a b, ForkWith N C w a b ∧ (positiveValues C x y).getD a false = true ∧
      (positiveValues C x y).getD b false = true) ∨
    ∃ r, ActiveEdge N C x w r ∧ Residual N C x y r := by
  obtain ⟨hd, hw, hz, hp⟩ := hw
  obtain ⟨g, hg⟩ := degree_two_gateAt N C w hd
  obtain ⟨hgm, hgl⟩ := gateAt_mono N C hm w g hg
  have hat := take_allAt _ _ _ _ w (actual_allAt N C hm x y hx hy)
  have hgd : g.lineDegree ((degrees N C).take w) = 2 := by rwa [← gateAt_degree N C w g hg]
  rw [gateAt_full N C x y hx hy w g hg] at hw
  rw [gateAt_zero N C x hx w g hg] at hz
  rw [gateAt_positive N C x y hx hy w g hg] at hp
  rcases gate_down g _ _ _ _ hgm hgl hat hgd hw hz hp with hf | he
  · obtain ⟨a, b, hop, hins, ha1, hb1, hpa, hpb⟩ := hf
    have hal : a < w := by rw [take_degree_read] at ha1; unfold readDegree at ha1; split_ifs at ha1; omega
    have hbl : b < w := by rw [take_degree_read] at hb1; unfold readDegree at hb1; split_ifs at hb1; omega
    left
    refine ⟨a, b, ⟨g, hg, hop, hins, ?_, ?_⟩, ?_, ?_⟩
    · rwa [take_degree_read] at ha1
    · rwa [take_degree_read] at hb1
    · simpa only [getD_take_guard, ite_eq_left hal] using hpa
    · simpa only [getD_take_guard, ite_eq_left hbl] using hpb
  · obtain ⟨r, hri, hr2, hrw, hrz, hrp, hweight⟩ := he
    have hrl : r < w := by rw [take_degree_read] at hr2; unfold readDegree at hr2; split_ifs at hr2; omega
    have hrd : degree N C r = 2 := by
      simpa only [take_degree_read, readDegree, ite_eq_left hrl] using hr2
    right
    refine ⟨r, ⟨?_, ?_⟩, hrd, ?_, ?_, ?_⟩
    · apply (mem_edges N C w r).mpr
      exact ⟨(degree_two_bounds N C w hd).2,
        (children_of_gateAt N C w r g hg hd).mpr ⟨hri, hrl, hrd⟩⟩
    · rwa [active_weight N C w g _ (zeroValues_length N C x hx) hg hd]
    · simpa only [getD_take_guard, ite_eq_left hrl] using hrw
    · simpa only [getD_take_guard, ite_eq_left hrl] using hrz
    · simpa only [getD_take_guard, ite_eq_left hrl] using hrp

lemma fork_descent (N : ℕ) (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (w : ℕ) (hw : Residual N C x y w) :
    ∃ v a b, Relation.ReflTransGen (ActiveEdge N C x) w v ∧ ForkWith N C v a b ∧
      (positiveValues C x y).getD a false = true ∧ (positiveValues C x y).getD b false = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rcases edge_down N C hm x y hx hy w hw with hf | he
    · obtain ⟨a, b, hf, ha, hb⟩ := hf
      exact ⟨w, a, b, .refl, hf, ha, hb⟩
    · obtain ⟨r, he, hr⟩ := he
      obtain ⟨v, a, b, hpath, hf, ha, hb⟩ := ih r (edge_bounds N C w r he.1).1 hr
      exact ⟨v, a, b, Relation.ReflTransGen.head he hpath, hf, ha, hb⟩

lemma path_up (N : ℕ) (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (w v : ℕ) (hp : Relation.ReflTransGen (ActiveEdge N C x) w v)
    (hv : (fullValues C x y).getD v false = true) : (fullValues C x y).getD w false = true := by
  induction hp using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head he _ ih => exact edge_up N C hm x y hx hy _ _ he.1 he.2 ih

lemma gateWeight_some_zero (g : Gate) (d : List ℕ) (r : ℕ)
    (hr : gateWeight g d = some r) : d.getD r 0 = 0 := by
  cases hop : g.op with
  | and =>
    simp only [gateWeight, hop] at hr
    exact of_decide_eq_true (List.find?_eq_some_iff_append.mp hr).1
  | or => simp [gateWeight, hop] at hr
  | not => simp [gateWeight, hop] at hr
  | mod m => simp [gateWeight, hop] at hr
  | maj => simp [gateWeight, hop] at hr

lemma weight_some_degree (N : ℕ) (C : Circuit) (w a : ℕ)
    (hw : weight N C w = some a) : degree N C a = 0 := by
  cases hg : gateAt N C w with
  | none => simp [weight, hg] at hw
  | some g =>
    by_cases hd : degree N C w = 2
    · rw [weight_gateAt N C w g hg hd] at hw
      obtain ⟨r, hr, heq⟩ := Option.map_eq_some_iff.mp hw
      have hr0 := gateWeight_some_zero g ((degrees N C).take w) r hr
      by_cases hrl : r < w
      · simp only [ite_eq_left hrl] at heq
        subst a
        simpa only [take_degree_read, readDegree, ite_eq_left hrl] using hr0
      · simp only [ite_eq_right hrl] at heq
        subst a
        exact List.getD_eq_default (degrees N C) 0 (by rw [degrees_length])
    · simp [weight, hg, hd] at hw

end OriginalGraph

namespace Pilot5bMeta1020OriginalNormalization

open PEqualNP.CircuitLowerBounds Pilot5bMeta1020Linear

abbrev F := Pilot5bMeta1020Forward.normalize
abbrev fnet (N : ℕ) (C : Circuit) := Pilot5bMeta1020Forward.net (F N C)
abbrev fmap (N : ℕ) (C : Circuit) (r : ℕ) :=
  (Pilot5bMeta1020Forward.one (F N C)).getD r N
abbrev OBound := OriginalGraph.bound
abbrev OEdges := OriginalGraph.edges
abbrev OWeight := OriginalGraph.weight
abbrev OFork := OriginalGraph.Fork
abbrev OForkWith := OriginalGraph.ForkWith
abbrev ODegree := OriginalGraph.degree

def seeds {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ) : List (ℕ × ℕ) :=
  List.ofFn fun j => (fa j, fmap N C (fb j))

def state {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ) :
    Pilot5bMeta1020Reverse.State :=
  Pilot5bMeta1020Reverse.build N (seeds N C fa fb) (OEdges N C) (OWeight N C)
    (OBound N C) (Pilot5bMeta1020Reverse.initial N (fnet N C))

def net {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ) : List Instruction :=
  Pilot5bMeta1020Reverse.net (state N C fa fb)

def context {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ) (w : ℕ) : ℕ :=
  Pilot5bMeta1020Reverse.context (state N C fa fb) w

noncomputable def forks (N : ℕ) (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range (OBound N C)).filter (OFork N C)

noncomputable def usedForks {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ) : Finset ℕ :=
  Pilot5bMeta1020ReverseStructure.usedForks (seeds N C fa fb) (OEdges N C) (forks N C)

def forkInputs (N : ℕ) (C : Circuit) (w : ℕ) : List ℕ :=
  ((OriginalGraph.gateAt N C w).map Gate.inputs).getD []

def forkLeft (N : ℕ) (C : Circuit) (w : ℕ) : ℕ :=
  (forkInputs N C w).getD 0 (OBound N C)

def forkRight (N : ℕ) (C : Circuit) (w : ℕ) : ℕ :=
  (forkInputs N C w).getD 1 (OBound N C)

abbrev Triple := ℕ × ℕ × ℕ

def bulkJob {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ) (j : Fin J) : Triple :=
  (fmap N C (fa j), fmap N C (fb j), fmap N C (fb j))

def forkJob {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ) (w : ℕ) : Triple :=
  (fmap N C (forkLeft N C w), fmap N C (forkRight N C w), context N C fa fb w)

noncomputable def jobs {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ) : List Triple :=
  List.ofFn (bulkJob N C fa fb) ++
    (usedForks N C fa fb).toList.map (forkJob N C fa fb)

lemma seeds_length {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ) :
    (seeds N C fa fb).length = J := by simp [seeds]

lemma mem_seeds {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ) (e : ℕ × ℕ) :
    e ∈ seeds N C fa fb ↔ ∃ j, e = (fa j, fmap N C (fb j)) := by
  simp [seeds, eq_comm]

lemma seeds_bound {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ) :
    ∀ e ∈ seeds N C fa fb, e.2 < N + (fnet N C).length := by
  intro e he
  obtain ⟨j, rfl⟩ := (mem_seeds N C fa fb e).mp he
  exact Pilot5bMeta1020Forward.normalize_one_getD_bound N C (fb j)

lemma forward_head (N : ℕ) (C : Circuit) : (fnet N C).head? = some (Sum.inl []) := by
  obtain ⟨t, ht⟩ := Pilot5bMeta1020Forward.build_net_false_prefix N (N + N + C.size) C.gates
  change (Pilot5bMeta1020Forward.net
    (Pilot5bMeta1020Forward.build N (N + N + C.size) C.gates)).head? = _
  rw [ht]
  rfl

lemma old_read {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ)
    (labels : ℕ → Bool) (y : List Bool) (hy : y.length = N) (r : ℕ) :
    (run (net N C fa fb) labels y).getD (fmap N C r) false =
      (run (fnet N C) labels y).getD (fmap N C r) false := by
  exact Pilot5bMeta1020ReverseStructure.build_old_read N (seeds N C fa fb)
    (OEdges N C) (OWeight N C) (OBound N C)
    (Pilot5bMeta1020Reverse.initial N (fnet N C)) labels y hy (fmap N C r)
    (Pilot5bMeta1020Forward.normalize_one_getD_bound N C r)

lemma jobs_length {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ) :
    (jobs N C fa fb).length = J + (usedForks N C fa fb).card := by
  simp [jobs]

lemma mem_jobs {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ) (t : Triple) :
    t ∈ jobs N C fa fb ↔ (∃ j, t = bulkJob N C fa fb j) ∨
      ∃ w ∈ usedForks N C fa fb, t = forkJob N C fa fb w := by
  simp [jobs, eq_comm]

lemma mem_forks (N : ℕ) (C : Circuit) (w : ℕ) :
    w ∈ forks N C ↔ w < OBound N C ∧ OFork N C w := by
  classical
  simp [forks]

lemma mem_usedForks {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ) (w : ℕ) :
    w ∈ usedForks N C fa fb ↔ w < OBound N C ∧ OFork N C w ∧
      0 < Pilot5bMeta1020Reverse.incomingCount (seeds N C fa fb) (OEdges N C) w := by
  classical
  simp [usedForks, Pilot5bMeta1020ReverseStructure.usedForks, mem_forks, and_assoc]

lemma fork_spec (N : ℕ) (C : Circuit) (w : ℕ) (hf : OFork N C w) :
    OForkWith N C w (forkLeft N C w) (forkRight N C w) := by
  obtain ⟨a, b, g, hg, ho, hi, ha, hb⟩ := hf
  have hl : forkLeft N C w = a := by simp [forkLeft, forkInputs, hg, hi]
  have hr : forkRight N C w = b := by simp [forkRight, forkInputs, hg, hi]
  exact hl ▸ hr ▸ ⟨g, hg, ho, hi, ha, hb⟩


lemma edge_bounds (N : ℕ) (C : Circuit) :
    ∀ e ∈ OEdges N C, e.2 < e.1 ∧ e.1 < OBound N C := by
  rintro ⟨w, r⟩ he
  obtain ⟨hw, hr⟩ := (OriginalGraph.mem_edges N C w r).mp he
  refine ⟨?_, hw⟩
  cases hg : OriginalGraph.gateAt N C w with
  | none => simp [OriginalGraph.children, hg] at hr
  | some g =>
    by_cases hd : ODegree N C w = 2
    · exact ((OriginalGraph.children_of_gateAt N C w r g hg hd).mp hr).2.1
    · simp [OriginalGraph.children, hg, hd] at hr

lemma context_reachable {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ)
    (labels : ℕ → Bool) (y : List Bool) (hy : y.length = N) (w : ℕ)
    (hw : w < OBound N C) :
    (run (net N C fa fb) labels y).getD (context N C fa fb w) false = true ↔
      Pilot5bMeta1020Weighted.seedReachable (OEdges N C)
        (Pilot5bMeta1020Reverse.weightValue labels (OWeight N C)) (seeds N C fa fb)
        (fun r => (run (fnet N C) labels y).getD r false) w := by
  exact Pilot5bMeta1020ReverseWeightedCorrectness.context_true_iff N (OBound N C)
    (fnet N C) (seeds N C fa fb) (OEdges N C) (OWeight N C) labels y hy
    (forward_head N C) (seeds_bound N C fa fb) (edge_bounds N C) w hw

lemma reachable_incoming_positive (edges seeds : List (ℕ × ℕ))
    (weightEval seedEval : ℕ → Bool) (w : ℕ)
    (hr : Pilot5bMeta1020Weighted.seedReachable edges weightEval seeds seedEval w) :
    0 < Pilot5bMeta1020Reverse.incomingCount seeds edges w := by
  have ht := (Pilot5bMeta1020Weighted.target_true edges weightEval seeds seedEval w).mpr hr
  have hd := (Pilot5bMeta1020Weighted.target_recurrence edges weightEval seeds seedEval w).mp ht
  by_contra hp
  have hz : Pilot5bMeta1020Reverse.incomingCount seeds edges w = 0 := by omega
  simp only [Pilot5bMeta1020Reverse.incomingCount, Nat.add_eq_zero,
    List.length_eq_zero_iff] at hz
  rcases hd with ⟨s, hs, hsw, _⟩ | ⟨e, he, hew, _, _⟩
  · have hm : s ∈ seeds.filter (fun e => decide (e.1 = w)) := by simp [hs, hsw]
    rw [hz.1] at hm
    simp at hm
  · have hm : e ∈ edges.filter (fun e => decide (e.2 = w)) := by simp [he, hew]
    rw [hz.2] at hm
    simp at hm

def Fires (read : ℕ → Bool) (t : Triple) : Prop :=
  read t.1 = true ∧ read t.2.1 = true ∧ read t.2.2 = true

lemma bulk_sound {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ)
    (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (hda : ∀ j, ODegree N C (fa j) ≤ 2) (hdb : ∀ j, ODegree N C (fb j) ≤ 1)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N) (j : Fin J)
    (hf : Fires (fun r => (run (net N C fa fb)
      (Pilot5bMeta1020Forward.pointLabels N C x) y).getD r false)
      (bulkJob N C fa fb j)) :
    (C.wires (x ++ y)).getD (fa j) false = true ∧
      (C.wires (x ++ y)).getD (fb j) false = true := by
  rcases hf with ⟨ha, hb, _⟩
  change (run (net N C fa fb) _ y).getD (fmap N C (fa j)) false = true at ha
  change (run (net N C fa fb) _ y).getD (fmap N C (fb j)) false = true at hb
  rw [old_read N C fa fb _ y hy] at ha hb
  exact ⟨Pilot5bMeta1020Forward.normalize_sound N C hm x y hx hy (fa j) (hda j) ha,
    Pilot5bMeta1020Forward.normalize_sound N C hm x y hx hy (fb j) (Nat.le_trans (hdb j) (by omega)) hb⟩


lemma mapped_positive (N : ℕ) (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N) (r : ℕ)
    (hr : ODegree N C r ≤ 2) :
    (run (fnet N C) (Pilot5bMeta1020Forward.pointLabels N C x) y).getD
      (fmap N C r) false =
      (OriginalGraph.positiveValues C x y).getD r false :=
  Pilot5bMeta1020Forward.normalize_correct N C hm x y hx hy r hr

lemma fork_left_eq (N : ℕ) (C : Circuit) (w a b : ℕ) (hf : OForkWith N C w a b) :
    forkLeft N C w = a := by
  obtain ⟨g, hg, _, hi, _, _⟩ := hf
  simp [forkLeft, forkInputs, hg, hi]

lemma fork_right_eq (N : ℕ) (C : Circuit) (w a b : ℕ) (hf : OForkWith N C w a b) :
    forkRight N C w = b := by
  obtain ⟨g, hg, _, hi, _, _⟩ := hf
  simp [forkRight, forkInputs, hg, hi]

lemma fork_sound {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ)
    (hm : PEqualNP.MetaComplexity.Monotone2 C) (hdb : ∀ j, ODegree N C (fb j) ≤ 1)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N) (w : ℕ)
    (hw : w ∈ usedForks N C fa fb)
    (hf : Fires (fun r => (run (net N C fa fb)
      (Pilot5bMeta1020Forward.pointLabels N C x) y).getD r false)
      (forkJob N C fa fb w)) :
    ∃ j, (C.wires (x ++ y)).getD (fa j) false = true ∧
      (C.wires (x ++ y)).getD (fb j) false = true := by
  obtain ⟨hwlt, hwfork, _⟩ := (mem_usedForks N C fa fb w).mp hw
  have hspec := fork_spec N C w hwfork
  have hc := OriginalGraph.fork_children N C w _ _ hspec
  rcases hf with ⟨ha, hb, hk⟩
  change (run (net N C fa fb) _ y).getD (fmap N C (forkLeft N C w)) false = true at ha
  change (run (net N C fa fb) _ y).getD (fmap N C (forkRight N C w)) false = true at hb
  change (run (net N C fa fb) _ y).getD (context N C fa fb w) false = true at hk
  rw [old_read N C fa fb _ y hy, mapped_positive N C hm x y hx hy _ (Nat.le_trans (Nat.le_of_eq hc.2.2.2.1) (by omega))] at ha
  rw [old_read N C fa fb _ y hy, mapped_positive N C hm x y hx hy _ (Nat.le_trans (Nat.le_of_eq hc.2.2.2.2) (by omega))] at hb
  have hwfull := OriginalGraph.fork_full
    N C hm x y hx hy w _ _ hspec ha hb
  obtain ⟨e, he, hseed, hpath⟩ :=
    (context_reachable N C fa fb _ y hy w hwlt).mp hk
  obtain ⟨j, rfl⟩ := (mem_seeds N C fa fb e).mp he
  have hfull := OriginalGraph.path_up
    N C hm x y hx hy (fa j) w hpath hwfull
  refine ⟨j, hfull, ?_⟩
  exact Pilot5bMeta1020Forward.normalize_sound N C hm x y hx hy (fb j)
    (Nat.le_trans (hdb j) (by omega)) hseed

lemma jobs_sound {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ)
    (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (hda : ∀ j, ODegree N C (fa j) ≤ 2) (hdb : ∀ j, ODegree N C (fb j) ≤ 1)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (t : Triple) (ht : t ∈ jobs N C fa fb)
    (hf : Fires (fun r => (run (net N C fa fb)
      (Pilot5bMeta1020Forward.pointLabels N C x) y).getD r false) t) :
    ∃ j, (C.wires (x ++ y)).getD (fa j) false = true ∧
      (C.wires (x ++ y)).getD (fb j) false = true := by
  rcases (mem_jobs N C fa fb t).mp ht with ⟨j, rfl⟩ | ⟨w, hw, rfl⟩
  · exact ⟨j, bulk_sound N C fa fb hm hda hdb x y hx hy j hf⟩
  · exact fork_sound N C fa fb hm hdb x y hx hy w hw hf

lemma jobs_cover {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ)
    (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (hda : ∀ j, ODegree N C (fa j) ≤ 2) (hdb : ∀ j, ODegree N C (fb j) ≤ 1)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N) (j : Fin J)
    (ha : (C.wires (x ++ y)).getD (fa j) false = true)
    (hb : (C.wires (x ++ y)).getD (fb j) false = true)
    (hza : (C.wires (x ++ List.replicate N false)).getD (fa j) false = false)
    (hzb : (C.wires (x ++ List.replicate N false)).getD (fb j) false = false) :
    ∃ t ∈ jobs N C fa fb, Fires (fun r => (run (net N C fa fb)
      (Pilot5bMeta1020Forward.pointLabels N C x) y).getD r false) t := by
  have hpb := Pilot5bMeta1020Forward.normalize_complete_degree_one
    N C hm x y hx hy (fb j) (hdb j) hb hzb
  have hpb' : (run (net N C fa fb) (Pilot5bMeta1020Forward.pointLabels N C x) y).getD
      (fmap N C (fb j)) false = true := by
    rw [old_read N C fa fb _ y hy]
    exact hpb
  by_cases hpa : (run (fnet N C) (Pilot5bMeta1020Forward.pointLabels N C x) y).getD
      (fmap N C (fa j)) false = true
  · refine ⟨bulkJob N C fa fb j, (mem_jobs N C fa fb _).mpr (Or.inl ⟨j, rfl⟩), ?_⟩
    refine ⟨?_, hpb', hpb'⟩
    change (run (net N C fa fb) _ y).getD (fmap N C (fa j)) false = true
    rw [old_read N C fa fb _ y hy]
    exact hpa
  · have hpa0 : (run (fnet N C) (Pilot5bMeta1020Forward.pointLabels N C x) y).getD
        (fmap N C (fa j)) false = false := Bool.eq_false_iff.mpr hpa
    have hda2 : ODegree N C (fa j) = 2 := by
      by_contra hn
      have hle : ODegree N C (fa j) ≤ 1 := by have := hda j; omega
      exact hpa (Pilot5bMeta1020Forward.normalize_complete_degree_one
        N C hm x y hx hy (fa j) hle ha hza)
    have hpzero : (OriginalGraph.positiveValues C x y).getD
        (fa j) false = false := by
      rw [← mapped_positive N C hm x y hx hy (fa j) (hda j)]
      exact hpa0
    obtain ⟨w, a, b, hpath, hf, hpa, hpb⟩ :=
      OriginalGraph.fork_descent N C hm x y hx hy (fa j)
        ⟨hda2, ha, hza, hpzero⟩
    have hc := OriginalGraph.fork_children N C w a b hf
    have hr : Pilot5bMeta1020Weighted.seedReachable (OEdges N C)
        (Pilot5bMeta1020Reverse.weightValue (Pilot5bMeta1020Forward.pointLabels N C x) (OWeight N C))
        (seeds N C fa fb)
        (fun r => (run (fnet N C) (Pilot5bMeta1020Forward.pointLabels N C x) y).getD r false) w :=
      ⟨(fa j, fmap N C (fb j)), (mem_seeds N C fa fb _).mpr ⟨j, rfl⟩,
        Pilot5bMeta1020Forward.normalize_complete_degree_one N C hm x y hx hy (fb j) (hdb j) hb hzb,
        hpath⟩
    have hw : w ∈ usedForks N C fa fb := (mem_usedForks N C fa fb w).mpr
      ⟨hc.2.2.1, ⟨a, b, hf⟩, reachable_incoming_positive _ _ _ _ w hr⟩
    refine ⟨forkJob N C fa fb w,
      (mem_jobs N C fa fb _).mpr (Or.inr ⟨w, hw, rfl⟩), ?_⟩
    refine ⟨?_, ?_, (context_reachable N C fa fb _ y hy w hc.2.2.1).mpr hr⟩
    · change (run (net N C fa fb) _ y).getD (fmap N C (forkLeft N C w)) false = true
      rw [fork_left_eq N C w a b hf, old_read N C fa fb _ y hy,
        mapped_positive N C hm x y hx hy a (Nat.le_trans (Nat.le_of_eq hc.2.2.2.1) (by omega))]
      exact hpa
    · change (run (net N C fa fb) _ y).getD (fmap N C (forkRight N C w)) false = true
      rw [fork_right_eq N C w a b hf, old_read N C fa fb _ y hy,
        mapped_positive N C hm x y hx hy b (Nat.le_trans (Nat.le_of_eq hc.2.2.2.2) (by omega))]
      exact hpb

end Pilot5bMeta1020OriginalNormalization

namespace Pilot5bMeta1020OriginalNormalization

open PEqualNP.CircuitLowerBounds Pilot5bMeta1020Linear

def tripleRoots (t : Triple) : Fin 3 → ℕ := ![t.1, t.2.1, t.2.2]

noncomputable def roots {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ)
    (j : Fin (jobs N C fa fb).length) : Fin 3 → ℕ :=
  tripleRoots (jobs N C fa fb)[j]

lemma tripleRoots_fires (t : Triple) (read : ℕ → Bool) :
    (∀ i, read (tripleRoots t i) = true) ↔ Fires read t := by
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2⟩
  · rintro ⟨ha, hb, hc⟩ i
    fin_cases i
    · exact ha
    · exact hb
    · exact hc

lemma roots_fires {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ)
    (j : Fin (jobs N C fa fb).length) (read : ℕ → Bool) :
    (∀ i, read (roots N C fa fb j i) = true) ↔ Fires read (jobs N C fa fb)[j] :=
  tripleRoots_fires _ _

lemma exists_roots_iff {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ)
    (read : ℕ → Bool) :
    (∃ j, ∀ i, read (roots N C fa fb j i) = true) ↔
      ∃ t ∈ jobs N C fa fb, Fires read t := by
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨(jobs N C fa fb)[j], List.get_mem _ j, (roots_fires N C fa fb j read).mp hj⟩
  · rintro ⟨t, ht, hf⟩
    obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp ht
    refine ⟨⟨j, hj⟩, (roots_fires N C fa fb ⟨j, hj⟩ read).mpr ?_⟩
    change Fires read (jobs N C fa fb)[j]
    rw [hget]
    exact hf

lemma roots_sound {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ)
    (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (hda : ∀ j, ODegree N C (fa j) ≤ 2) (hdb : ∀ j, ODegree N C (fb j) ≤ 1)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (j : Fin (jobs N C fa fb).length)
    (hf : ∀ i, (run (net N C fa fb) (Pilot5bMeta1020Forward.pointLabels N C x) y).getD
      (roots N C fa fb j i) false = true) :
    ∃ k, (C.wires (x ++ y)).getD (fa k) false = true ∧
      (C.wires (x ++ y)).getD (fb k) false = true :=
  jobs_sound N C fa fb hm hda hdb x y hx hy _ (List.get_mem _ j)
    ((roots_fires N C fa fb j _).mp hf)

lemma roots_sound_functions {J : ℕ} (N : ℕ) (I : Fin N → Fin N → Prop)
    (C : Circuit) (fa fb : Fin J → ℕ)
    (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (hda : ∀ j, ODegree N C (fa j) ≤ 2) (hdb : ∀ j, ODegree N C (fb j) ≤ 1)
    (hsound : ∀ j (z : Fin (N + N) → Bool),
      (C.wires (List.ofFn z)).getD (fa j) false = true →
      (C.wires (List.ofFn z)).getD (fb j) false = true →
      ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (x y : Fin N → Bool) (j : Fin (jobs N C fa fb).length)
    (hf : ∀ i, (run (net N C fa fb)
      (Pilot5bMeta1020Forward.pointLabels N C (List.ofFn x)) (List.ofFn y)).getD
      (roots N C fa fb j i) false = true) :
    ∃ p l, I p l ∧ x p = true ∧ y l = true := by
  obtain ⟨k, ha, hb⟩ := roots_sound N C fa fb hm hda hdb
    (List.ofFn x) (List.ofFn y) (by simp) (by simp) j hf
  rw [← List.ofFn_fin_append] at ha hb
  obtain ⟨p, l, hi, hp, hl⟩ := hsound k (Fin.append x y) ha hb
  exact ⟨p, l, hi, by simpa only [Fin.append_left] using hp,
    by simpa only [Fin.append_right] using hl⟩

lemma roots_cover_pair {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ)
    (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (hda : ∀ j, ODegree N C (fa j) ≤ 2) (hdb : ∀ j, ODegree N C (fb j) ≤ 1)
    (p l : Fin N) (j : Fin J)
    (ha : (C.wires (List.ofFn (Pilot5bMeta1020Forward.pairInput p l))).getD (fa j) false = true)
    (hb : (C.wires (List.ofFn (Pilot5bMeta1020Forward.pairInput p l))).getD (fb j) false = true)
    (hza : (C.wires (List.ofFn (Pilot5bMeta1020Forward.pointInput p))).getD (fa j) false = false)
    (hzb : (C.wires (List.ofFn (Pilot5bMeta1020Forward.pointInput p))).getD (fb j) false = false) :
    ∃ k, ∀ i, (run (net N C fa fb)
      (Pilot5bMeta1020Forward.pointLabels N C (List.ofFn (fun q => decide (q = p))))
      (List.ofFn (fun u => decide (u = l)))).getD (roots N C fa fb k i) false = true := by
  apply (exists_roots_iff N C fa fb (fun r =>
    (run (net N C fa fb)
      (Pilot5bMeta1020Forward.pointLabels N C (List.ofFn (fun q => decide (q = p))))
      (List.ofFn (fun u => decide (u = l)))).getD r false)).mpr
  rw [Pilot5bMeta1020Forward.pairInput_list] at ha hb
  rw [Pilot5bMeta1020Forward.pointInput_list] at hza hzb
  exact jobs_cover N C fa fb hm hda hdb _ _ (by simp) (by simp) j ha hb hza hzb

end Pilot5bMeta1020OriginalNormalization
namespace Pilot5bMeta1020Forward

open PEqualNP.CircuitLowerBounds
open Pilot5bMeta1020Linear

lemma payload_or_fanin (N z : ℕ) (s : State) (g : Gate)
    (hfan : g.inputs.length ≤ 2) (rs : List ℕ)
    (hmem : Sum.inl rs ∈ payload N z s g) : rs.length ≤ 2 := by
  unfold payload at hmem
  dsimp only at hmem
  split_ifs at hmem
  all_goals try split at hmem
  all_goals try split_ifs at hmem
  all_goals simp_all

lemma payload_label_origin (N z : ℕ) (s : State) (g : Gate) (a r : ℕ)
    (hmem : Sum.inr (a, r) ∈ payload N z s g) :
    ∃ i, a = labelRead z s i ∧ (degrees s).getD i 0 ≤ 1 := by
  unfold payload at hmem
  dsimp only at hmem
  split_ifs at hmem
  all_goals try split at hmem
  all_goals try split_ifs at hmem
  all_goals simp_all
  all_goals aesop

lemma fold_net_mem_origin (N z : ℕ) (gs : List Gate) (s : State) (ins : Instruction)
    (hmem : ins ∈ net (gs.foldl (advance N z) s)) :
    ins ∈ net s ∨ ∃ pre g post, gs = pre ++ g :: post ∧
      ins ∈ payload N z (pre.foldl (advance N z) s) g := by
  induction gs generalizing s with
  | nil => exact Or.inl hmem
  | cons g gs ih =>
    rw [List.foldl_cons] at hmem
    rcases ih (advance N z s g) hmem with h | ⟨pre, g', post, hgs, hp⟩
    · rw [advance_net, List.mem_append] at h
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr ⟨[], g, gs, rfl, h⟩
    · refine Or.inr ⟨g :: pre, g', post, ?_, ?_⟩
      · simp only [List.cons_append, hgs]
      · simpa only [List.foldl_cons] using hp

lemma build_net_mem_origin (N z : ℕ) (gs : List Gate) (ins : Instruction)
    (hmem : ins ∈ net (build N z gs)) :
    ins = Sum.inl [] ∨ ∃ pre g post, gs = pre ++ g :: post ∧
      ins ∈ payload N z (build N z pre) g := by
  rcases fold_net_mem_origin N z gs (initial N) ins hmem with h | h
  · exact Or.inl (by simpa only [initial, net, List.mem_singleton] using h)
  · exact Or.inr h

lemma normalize_or_fanin (N : ℕ) (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (rs : List ℕ) (hmem : Sum.inl rs ∈ net (normalize N C)) : rs.length ≤ 2 := by
  rcases build_net_mem_origin N (N + N + C.size) C.gates (Sum.inl rs) hmem with
    h | ⟨pre, g, post, hgs, hp⟩
  · have hrs : rs = [] := Sum.inl.inj h
    simp [hrs]
  · have hg : g ∈ C.gates := by rw [hgs]; simp
    exact payload_or_fanin N (N + N + C.size) (build N (N + N + C.size) pre)
      g (hC g hg).2 rs hp

lemma normalize_label_degree_le_one (N : ℕ) (C : Circuit) (a r : ℕ)
    (hmem : Sum.inr (a, r) ∈ net (normalize N C)) :
    (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD a 0 ≤ 1 := by
  rcases build_net_mem_origin N (N + N + C.size) C.gates (Sum.inr (a, r)) hmem with
    h | ⟨pre, g, post, hgs, hp⟩
  · contradiction
  · obtain ⟨i, ha, hi⟩ := payload_label_origin N (N + N + C.size)
      (build N (N + N + C.size) pre) g a r hp
    rw [← normalize_degrees_eq]
    by_cases hir : i < (one (build N (N + N + C.size) pre)).length
    · rw [ha, labelRead_of_lt _ _ _ hir]
      have hprefix : (degrees (normalize N C)).getD i 0 =
          (degrees (build N (N + N + C.size) pre)).getD i 0 := by
        change (degrees (build N (N + N + C.size) C.gates)).getD i 0 = _
        rw [hgs]
        apply build_degrees_getD_prefix
        simpa only [build_one_length] using hir
      rw [hprefix]
      exact hi
    · rw [ha, labelRead_of_ge _ _ _ (Nat.le_of_not_gt hir)]
      have hzero : (degrees (normalize N C)).getD (N + N + C.size) 0 = 0 := by
        apply List.getD_eq_default
        simp only [normalize, build_degrees_length, Circuit.size]
        omega
      rw [hzero]
      omega

end Pilot5bMeta1020Forward
namespace Pilot5bMeta1020Forward

open PEqualNP.CircuitLowerBounds

def degreeTrace : List ℕ → List Gate → List ℕ
  | _, [] => []
  | d, g :: gs => g.lineDegree d :: degreeTrace (d ++ [g.lineDegree d]) gs

lemma degreeTrace_length (d : List ℕ) (gs : List Gate) :
    (degreeTrace d gs).length = gs.length := by
  induction gs generalizing d with
  | nil => rfl
  | cons g gs ih => simp only [degreeTrace, List.length_cons, ih]

lemma degreeFold_eq_append_trace (d : List ℕ) (gs : List Gate) :
    gs.foldl (fun d g => d ++ [g.lineDegree d]) d = d ++ degreeTrace d gs := by
  induction gs generalizing d with
  | nil => simp [degreeTrace]
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [degreeTrace, List.append_assoc, List.singleton_append]

lemma degreeCountFrom_eq_trace_count (k : ℕ) (d : List ℕ) (gs : List Gate) :
    degreeCountFrom k d gs = (degreeTrace d gs).count k := by
  induction gs generalizing d with
  | nil => rfl
  | cons g gs ih =>
    simp only [degreeCountFrom, degreeTrace, List.count_cons, beq_iff_eq, ih]
    omega

lemma list_count_eq_index_card (xs : List ℕ) (k : ℕ) :
    xs.count k = ((Finset.range xs.length).filter (fun i => xs.getD i 0 = k)).card := by
  rw [Finset.card_filter]
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.count_cons, List.length_cons, Finset.sum_range_succ',
      List.getD_cons_succ, List.getD_cons_zero, beq_iff_eq, ih]

lemma list_count_eq_Ico_append_card (d xs : List ℕ) (k : ℕ) :
    xs.count k = ((Finset.Ico d.length (d.length + xs.length)).filter
      (fun w => (d ++ xs).getD w 0 = k)).card := by
  rw [list_count_eq_index_card]
  apply Finset.card_bij (fun i _ => d.length + i)
  · intro i hi
    obtain ⟨hir, hik⟩ := Finset.mem_filter.mp hi
    have hi' := Finset.mem_range.mp hir
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    · rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]
      exact hik
  · intro i _ j _ hij
    omega
  · intro w hw
    obtain ⟨hwr, hwk⟩ := Finset.mem_filter.mp hw
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hwr
    have hmem : w - d.length ∈ (Finset.range xs.length).filter (fun i => xs.getD i 0 = k) := by
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_range.mpr (by omega)
      · rw [List.getD_append_right _ _ _ _ hlo] at hwk
        exact hwk
    exact ⟨w - d.length, hmem, by omega⟩

lemma original_degrees_append_trace (N : ℕ) (C : Circuit) :
    C.lineDegrees (N + N) (Finset.Ico N (N + N)) =
      degrees (initial N) ++ degreeTrace (degrees (initial N)) C.gates := by
  rw [← normalize_degrees_eq, normalize, build, fold_degrees, degreeFold_eq_append_trace]

lemma degreeCount_eq_global_card (N k : ℕ) (C : Circuit) :
    degreeCount N k C.gates =
      ((Finset.Ico (N + N) (N + N + C.size)).filter
        (fun w => (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD w 0 = k)).card := by
  rw [degreeCount, degreeCountFrom_eq_trace_count, list_count_eq_Ico_append_card]
  rw [← original_degrees_append_trace N C]
  simp only [initial, degrees, List.length_append, List.length_replicate,
    degreeTrace_length, Circuit.size]

lemma degreeCount_zero_one_eq_low_card (N : ℕ) (C : Circuit) :
    degreeCount N 0 C.gates + degreeCount N 1 C.gates =
      ((Finset.Ico (N + N) (N + N + C.size)).filter
        (fun w => (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD w 0 ≤ 1)).card := by
  let D := C.lineDegrees (N + N) (Finset.Ico N (N + N))
  let S := Finset.Ico (N + N) (N + N + C.size)
  have heq : S.filter (fun w => D.getD w 0 ≤ 1) =
      S.filter (fun w => D.getD w 0 = 0) ∪ S.filter (fun w => D.getD w 0 = 1) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hw, hd⟩
      have hcases : D.getD w 0 = 0 ∨ D.getD w 0 = 1 := by omega
      exact hcases.elim (fun h => Or.inl ⟨hw, h⟩) (fun h => Or.inr ⟨hw, h⟩)
    · rintro (⟨hw, hd⟩ | ⟨hw, hd⟩) <;> exact ⟨hw, by omega⟩
  have hd : Disjoint (S.filter (fun w => D.getD w 0 = 0))
      (S.filter (fun w => D.getD w 0 = 1)) := by
    apply Finset.disjoint_left.mpr
    intro w h0 h1
    have h0' := (Finset.mem_filter.mp h0).2
    have h1' := (Finset.mem_filter.mp h1).2
    omega
  change degreeCount N 0 C.gates + degreeCount N 1 C.gates =
    (S.filter (fun w => D.getD w 0 ≤ 1)).card
  rw [heq, Finset.card_union_of_disjoint hd, degreeCount_eq_global_card,
    degreeCount_eq_global_card]

lemma original_input_degree_le_one (N : ℕ) (C : Circuit) (w : ℕ) (hw : w < N + N) :
    (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD w 0 ≤ 1 := by
  rw [original_degrees_append_trace,
    List.getD_append _ _ _ _ (by simpa [initial, degrees] using hw)]
  have hm : ∀ r ∈ degrees (initial N), r < 2 := by
    intro r hr
    change r ∈ List.replicate N 0 ++ List.replicate N 1 at hr
    rcases List.mem_append.mp hr with h | h
    · have := List.eq_of_mem_replicate h
      omega
    · have := List.eq_of_mem_replicate h
      omega
  have h := getD_bound_of_mem (degrees (initial N)) 0 2 hm (by omega) w
  omega

lemma degreeCount_two_eq_range_card (N : ℕ) (C : Circuit) :
    degreeCount N 2 C.gates =
      ((Finset.range (N + N + C.size)).filter
        (fun w => (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD w 0 = 2)).card := by
  rw [degreeCount_eq_global_card]
  congr 1
  ext w
  simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_range]
  constructor
  · exact fun h => ⟨h.1.2, h.2⟩
  · rintro ⟨hw, hd⟩
    have hlo : N + N ≤ w := by
      by_contra hn
      have hi := original_input_degree_le_one N C w (by omega)
      omega
    exact ⟨⟨hlo, hw⟩, hd⟩

end Pilot5bMeta1020Forward
namespace Pilot5bMeta1020Forward

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_1020

def forkTrace : List ℕ → List Gate → List Bool
  | _, [] => []
  | d, g :: gs => forkAt d g :: forkTrace (d ++ [g.lineDegree d]) gs

lemma forkTrace_length (d : List ℕ) (gs : List Gate) :
    (forkTrace d gs).length = gs.length := by
  induction gs generalizing d with
  | nil => rfl
  | cons g gs ih => simp only [forkTrace, List.length_cons, ih]

lemma forkCountFrom_eq_trace_count (d : List ℕ) (gs : List Gate) :
    forkCountFrom d gs = (forkTrace d gs).count true := by
  induction gs generalizing d with
  | nil => rfl
  | cons g gs ih =>
    simp only [forkCountFrom, forkTrace, List.count_cons, beq_iff_eq, ih]
    omega

lemma list_bool_count_true_eq_index_card (xs : List Bool) :
    xs.count true = ((Finset.range xs.length).filter (fun i => xs.getD i false = true)).card := by
  rw [Finset.card_filter]
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.count_cons, List.length_cons, Finset.sum_range_succ',
      List.getD_cons_succ, List.getD_cons_zero, beq_iff_eq, ih]

lemma forkTrace_getD (d : List ℕ) (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    (forkTrace d gs).getD j false =
      forkAt ((gs.take j).foldl (fun d g => d ++ [g.lineDegree d]) d) gs[j] := by
  induction gs generalizing d j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero => rfl
    | succ j =>
      have hj' : j < gs.length := by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hj
      simpa only [forkTrace, List.getD_cons_succ, List.take_succ_cons,
        List.foldl_cons, List.getElem_cons_succ] using ih (d ++ [g.lineDegree d]) j hj'

lemma degree_prefix_read_global (N : ℕ) (C : Circuit) (j r : ℕ)
    (hj : j ≤ C.gates.length) :
    ((C.gates.take j).foldl (fun d g => d ++ [g.lineDegree d])
      (degrees (initial N))).getD r 0 = OriginalGraph.readDegree N C (N + N + j) r := by
  simpa only [Pilot5bMeta1020Fold.grow, Pilot5bMeta1020Fold.initialDegrees,
    ← initial_degrees_eq N] using OriginalGraph.prefix_degree_read N C j r hj

lemma forkAt_prefix_iff_global (N : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    forkAt ((C.gates.take j).foldl (fun d g => d ++ [g.lineDegree d])
      (degrees (initial N))) C.gates[j] = true ↔ OriginalGraph.Fork N C (N + N + j) := by
  rw [forkAt_iff]
  constructor
  · rintro ⟨a, b, hop, hins, ha, hb⟩
    refine ⟨a, b, C.gates[j], OriginalGraph.gateAt_index N C j hj, hop, hins, ?_, ?_⟩
    · rwa [← degree_prefix_read_global N C j a hj.le]
    · rwa [← degree_prefix_read_global N C j b hj.le]
  · rintro ⟨a, b, g, hg, hop, hins, ha, hb⟩
    rw [OriginalGraph.gateAt_index N C j hj] at hg
    have heq : C.gates[j] = g := Option.some.inj hg
    subst g
    refine ⟨a, b, hop, hins, ?_, ?_⟩
    · rwa [degree_prefix_read_global N C j a hj.le]
    · rwa [degree_prefix_read_global N C j b hj.le]

open Classical in
lemma forkCount_eq_gate_index_card (N : ℕ) (C : Circuit) :
    forkCount N C.gates = ((Finset.range C.gates.length).filter
      (fun j => OriginalGraph.Fork N C (N + N + j))).card := by
  classical
  rw [forkCount, forkCountFrom_eq_trace_count, list_bool_count_true_eq_index_card]
  congr 1
  rw [forkTrace_length]
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hj, hf⟩
    refine ⟨hj, ?_⟩
    rw [forkTrace_getD _ _ _ hj] at hf
    exact (forkAt_prefix_iff_global N C j hj).mp hf
  · rintro ⟨hj, hf⟩
    refine ⟨hj, ?_⟩
    rw [forkTrace_getD _ _ _ hj]
    exact (forkAt_prefix_iff_global N C j hj).mpr hf

open Classical in
lemma forkCount_eq_global_fork_card (N : ℕ) (C : Circuit) :
    forkCount N C.gates = ((Finset.range (OriginalGraph.bound N C)).filter
      (OriginalGraph.Fork N C)).card := by
  classical
  rw [forkCount_eq_gate_index_card]
  apply Finset.card_bij (fun j _ => N + N + j)
  · intro j hj
    obtain ⟨hjr, hjf⟩ := Finset.mem_filter.mp hj
    have hj' := Finset.mem_range.mp hjr
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, hjf⟩
    simp only [OriginalGraph.bound, Circuit.size]
    omega
  · intro i _ j _ hij
    omega
  · intro w hw
    obtain ⟨hwr, hwf⟩ := Finset.mem_filter.mp hw
    have hlo : N + N ≤ w := by
      obtain ⟨a, b, g, hg, _⟩ := hwf
      obtain ⟨j, _, hweq, _⟩ := OriginalGraph.gateAt_some N C w g hg
      omega
    have hhi := Finset.mem_range.mp hwr
    have hj : w - (N + N) < C.gates.length := by
      simp only [OriginalGraph.bound, Circuit.size] at hhi
      omega
    have heq : N + N + (w - (N + N)) = w := by omega
    have hmem : w - (N + N) ∈ (Finset.range C.gates.length).filter
        (fun j => OriginalGraph.Fork N C (N + N + j)) := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, by rwa [heq]⟩
    exact ⟨w - (N + N), hmem, heq⟩

end Pilot5bMeta1020Forward
namespace GraphBudget

open Classical

open PEqualNP.CircuitLowerBounds
open OriginalGraph


lemma filter_two_find_zero (rs : List ℕ) (d : ℕ → ℕ) (hl : rs.length ≤ 2) :
    (rs.filter fun r => decide (d r = 2)).length +
      (if (rs.find? fun r => decide (d r = 0)).isSome then 1 else 0) ≤ 2 := by
  cases rs with
  | nil => simp
  | cons a rs =>
    cases rs with
    | nil =>
      by_cases ha0 : d a = 0 <;> by_cases ha2 : d a = 2 <;>
        simp_all
    | cons b rs =>
      cases rs with
      | nil =>
        by_cases ha0 : d a = 0 <;> by_cases ha2 : d a = 2 <;>
          by_cases hb0 : d b = 0 <;> by_cases hb2 : d b = 2 <;>
          simp_all
      | cons c cs => simp only [List.length_cons] at hl; omega

lemma clipped_two_iff (N : ℕ) (C : Circuit) (w r : ℕ) :
    readDegree N C w r = 2 ↔ r < w ∧ degree N C r = 2 := by
  unfold readDegree
  split_ifs with hr <;> simp_all

lemma gateAt_mem (N : ℕ) (C : Circuit) (w : ℕ) (g : Gate)
    (hg : gateAt N C w = some g) : g ∈ C.gates := by
  unfold gateAt at hg
  split_ifs at hg
  exact List.mem_of_getElem? hg

lemma local_cost_le_two (N : ℕ) (C : Circuit) (w : ℕ)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    (children N C w).length + (if (weight N C w).isSome then 1 else 0) ≤ 2 := by
  cases hg : gateAt N C w with
  | none => simp [children, weight, hg]
  | some g =>
    have hl := hfan g (gateAt_mem N C w g hg)
    by_cases hd : degree N C w = 2
    · have he : (g.inputs.filter fun r => decide (r < w ∧ degree N C r = 2)) =
          (g.inputs.filter fun r => decide (readDegree N C w r = 2)) := by
        apply List.filter_congr
        intro r hr
        simp only [clipped_two_iff]
      cases hop : g.op with
      | and =>
        simp only [children, weight, hg, hd, ite_true, hop]
        rw [he]
        simpa using filter_two_find_zero g.inputs (readDegree N C w) hl
      | or | not | mod _ | maj =>
        simpa [children, weight, hg, hd, hop] using
          (List.length_filter_le (fun r => decide (r < w ∧ degree N C r = 2)) g.inputs).trans hl
    · simp [children, weight, hg, hd]

lemma local_cost_zero_of_fork (N : ℕ) (C : Circuit) (w : ℕ) (hf : Fork N C w) :
    (children N C w).length + (if (weight N C w).isSome then 1 else 0) = 0 := by
  obtain ⟨a, b, g, hg, hop, hins, ha, hb⟩ := hf
  have ha2 : ¬ (a < w ∧ degree N C a = 2) := by
    rw [← clipped_two_iff]
    omega
  have hb2 : ¬ (b < w ∧ degree N C b = 2) := by
    rw [← clipped_two_iff]
    omega
  by_cases hd : degree N C w = 2 <;>
    simp [children, weight, hg, hd, hop, hins, ha, hb, ha2, hb2]

lemma local_cost_zero_of_not_two (N : ℕ) (C : Circuit) (w : ℕ)
    (hd : degree N C w ≠ 2) :
    (children N C w).length + (if (weight N C w).isSome then 1 else 0) = 0 := by
  cases hg : gateAt N C w <;> simp [children, weight, hg, hd]

lemma local_cost_bound (N : ℕ) (C : Circuit) (w : ℕ)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    (children N C w).length + (if (weight N C w).isSome then 1 else 0) ≤
      if degree N C w = 2 ∧ ¬ Fork N C w then 2 else 0 := by
  classical
  by_cases hd : degree N C w = 2
  · by_cases hf : Fork N C w
    · rw [local_cost_zero_of_fork N C w hf]
      simp [hf]
    · simpa [hd, hf] using local_cost_le_two N C w hfan
  · rw [local_cost_zero_of_not_two N C w hd]
    simp [hd]

noncomputable def degreeTwo (N : ℕ) (C : Circuit) : Finset ℕ :=
  (Finset.range (bound N C)).filter fun w => degree N C w = 2

noncomputable def forks (N : ℕ) (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range (bound N C)).filter fun w => Fork N C w

def weightedVertices (N : ℕ) (C : Circuit) : Finset ℕ :=
  (Finset.range (bound N C)).filter fun w => (weight N C w).isSome

lemma forks_subset_range (N : ℕ) (C : Circuit) :
    forks N C ⊆ Finset.range (bound N C) := by
  classical
  exact Finset.filter_subset _ _

lemma used_forks_subset (N : ℕ) (C : Circuit) (p : ℕ → Prop) [DecidablePred p] :
    (forks N C).filter p ⊆ forks N C := Finset.filter_subset _ _

lemma edges_length (N : ℕ) (C : Circuit) :
    (edges N C).length = ∑ w ∈ Finset.range (bound N C), (children N C w).length := by
  simp only [edges, List.length_flatMap, List.length_map]
  exact ReverseBudget.range_cost_sum _ _

lemma weighted_card (N : ℕ) (C : Circuit) :
    (weightedVertices N C).card =
      ∑ w ∈ Finset.range (bound N C), if (weight N C w).isSome then 1 else 0 := by
  simp [weightedVertices, Finset.sum_boole]

lemma graph_cost_sdiff (N : ℕ) (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    (edges N C).length + (weightedVertices N C).card ≤
      2 * (degreeTwo N C \ forks N C).card := by
  classical
  rw [edges_length, weighted_card, ← Finset.sum_add_distrib]
  have hc : degreeTwo N C \ forks N C =
      (Finset.range (bound N C)).filter fun w => degree N C w = 2 ∧ ¬ Fork N C w := by
    ext w
    simp only [degreeTwo, forks, Finset.mem_sdiff, Finset.mem_filter]
    tauto
  rw [hc, Finset.card_filter]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro w hw
  have hh := local_cost_bound N C w hfan
  split_ifs at hh ⊢ <;> omega

lemma graph_cost_of_subset (N : ℕ) (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hfork : forks N C ⊆ degreeTwo N C) :
    (edges N C).length + (weightedVertices N C).card ≤
      2 * ((degreeTwo N C).card - (forks N C).card) := by
  simpa only [Finset.card_sdiff_of_subset hfork] using graph_cost_sdiff N C hfan

lemma fork_lt_bound (N : ℕ) (C : Circuit) (w : ℕ) (hf : Fork N C w) :
    w < bound N C := by
  obtain ⟨a, b, g, hg, _, _, _, _⟩ := hf
  obtain ⟨j, hj, hw, _⟩ := gateAt_some N C w g hg
  simp only [bound, Circuit.size]
  omega

lemma forks_subset_degreeTwo (N : ℕ) (C : Circuit) :
    forks N C ⊆ degreeTwo N C := by
  intro w hw
  obtain ⟨hr, hf⟩ := Finset.mem_filter.mp hw
  exact Finset.mem_filter.mpr ⟨hr, fork_degree N C w hf⟩

lemma graph_cost (N : ℕ) (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    (edges N C).length + (weightedVertices N C).card ≤
      2 * ((degreeTwo N C).card - (forks N C).card) :=
  graph_cost_of_subset N C hfan (forks_subset_degreeTwo N C)

lemma graph_cost_monotone (N : ℕ) (C : Circuit)
    (hm : PEqualNP.MetaComplexity.Monotone2 C) :
    (edges N C).length + (weightedVertices N C).card ≤
      2 * ((degreeTwo N C).card - (forks N C).card) :=
  graph_cost N C (fun g hg => (hm g hg).2)

lemma graph_cost_sum (N : ℕ) (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    (edges N C).length +
      (∑ w ∈ Finset.range (bound N C), if (weight N C w).isSome then 1 else 0) ≤
      2 * ((degreeTwo N C).card - (forks N C).card) := by
  rw [← weighted_card]
  exact graph_cost N C hfan

end GraphBudget
namespace GraphReverseBudget

open PEqualNP.CircuitLowerBounds
open OriginalGraph
open GraphBudget

lemma weightedCount_eq (N : ℕ) (C : Circuit) :
    Pilot5bMeta1020ReverseStructure.weightedCount (weight N C) (bound N C) =
      (weightedVertices N C).card := by
  exact (weighted_card N C).symm

lemma reverse_budget (N : ℕ) (C : Circuit) (seeds : List (ℕ × ℕ))
    (s : Pilot5bMeta1020Reverse.State)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    (Pilot5bMeta1020Reverse.net
      (Pilot5bMeta1020Reverse.build N seeds (edges N C) (weight N C) (bound N C) s)).length +
      (Pilot5bMeta1020ReverseStructure.usedForks seeds (edges N C) (forks N C)).card ≤
    (Pilot5bMeta1020Reverse.net s).length + seeds.length +
      2 * ((degreeTwo N C).card - (forks N C).card) := by
  have h := Pilot5bMeta1020ReverseStructure.build_budget N seeds (edges N C) (weight N C)
    (bound N C) s (forks N C) (forks_subset_range N C)
  rw [weightedCount_eq] at h
  have hc := graph_cost N C hfan
  omega

lemma normalized_reverse_budget (N : ℕ) (C : Circuit) (seeds : List (ℕ × ℕ))
    (s : Pilot5bMeta1020Reverse.State) (g1 g2 : ℕ)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hdegree : (degreeTwo N C).card = g2)
    (hbase : (Pilot5bMeta1020Reverse.net s).length ≤
      1 + g1 + g2 + 2 * (forks N C).card) :
    (Pilot5bMeta1020Reverse.net
      (Pilot5bMeta1020Reverse.build N seeds (edges N C) (weight N C) (bound N C) s)).length +
      (Pilot5bMeta1020ReverseStructure.usedForks seeds (edges N C) (forks N C)).card ≤
    1 + g1 + 3 * g2 + seeds.length := by
  have h := reverse_budget N C seeds s hfan
  have hf := Finset.card_le_card (forks_subset_degreeTwo N C)
  rw [hdegree] at h hf
  omega

end GraphReverseBudget
namespace Pilot5bMeta1020ReverseStructure

open Pilot5bMeta1020Linear Pilot5bMeta1020OrAggregate Pilot5bMeta1020Reverse

lemma aggregate_label_origin (n : ℕ) (gs : List Instruction) (rs : List ℕ) (a r : ℕ)
    (h : Sum.inr (a, r) ∈ (aggregate n gs rs).1) : Sum.inr (a, r) ∈ gs := by
  obtain ⟨hs, heq, _, hor⟩ := aggregate_extension n gs rs
  rw [heq] at h
  rcases List.mem_append.mp h with h | h
  · exact h
  · obtain ⟨us, he, _⟩ := hor (Sum.inr (a, r)) h
    cases he

lemma step_label_origin (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (v : ℕ) (s : State) (a r : ℕ)
    (h : Sum.inr (a, r) ∈ net (Pilot5bMeta1020Reverse.step n seeds edges weight v s)) :
    Sum.inr (a, r) ∈ net s ∨ weight v = some a := by
  cases hw : weight v with
  | none =>
    left
    apply aggregate_label_origin n (net s) (incoming seeds edges (message s) v) a r
    simpa only [Pilot5bMeta1020Reverse.step, hw, net] using h
  | some z =>
    simp only [Pilot5bMeta1020Reverse.step, hw, net, List.mem_append, List.mem_singleton] at h
    rcases h with h | h
    · exact Or.inl (aggregate_label_origin n (net s) (incoming seeds edges (message s) v) a r h)
    · have he : a = z := congrArg Prod.fst (Sum.inr.inj h)
      exact Or.inr (by simp only [he])

lemma build_label_origin (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (k : ℕ) (s : State) (a r : ℕ)
    (h : Sum.inr (a, r) ∈ net (build n seeds edges weight k s)) :
    Sum.inr (a, r) ∈ net s ∨ ∃ v < k, weight v = some a := by
  induction k generalizing s with
  | zero => exact Or.inl h
  | succ k ih =>
    change Sum.inr (a, r) ∈ net (build n seeds edges weight k
      (Pilot5bMeta1020Reverse.step n seeds edges weight k s)) at h
    rcases ih (Pilot5bMeta1020Reverse.step n seeds edges weight k s) h with h | h
    · rcases step_label_origin n seeds edges weight k s a r h with h | h
      · exact Or.inl h
      · exact Or.inr ⟨k, by omega, h⟩
    · obtain ⟨v, hv, he⟩ := h
      exact Or.inr ⟨v, by omega, he⟩

lemma build_label_property (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (k : ℕ) (s : State) (P : ℕ → Prop)
    (hs : ∀ a r, Sum.inr (a, r) ∈ net s → P a)
    (hw : ∀ v < k, ∀ a, weight v = some a → P a) :
    ∀ a r, Sum.inr (a, r) ∈ net (build n seeds edges weight k s) → P a := by
  intro a r h
  rcases build_label_origin n seeds edges weight k s a r h with h | h
  · exact hs a r h
  · obtain ⟨v, hv, he⟩ := h
    exact hw v hv a he

end Pilot5bMeta1020ReverseStructure

namespace Pilot5bMeta1020OriginalNormalization

open PEqualNP.CircuitLowerBounds Pilot5bMeta1020Linear

lemma net_head {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ) :
    (net N C fa fb).head? = some (Sum.inl []) := by
  obtain ⟨hs, he⟩ := Pilot5bMeta1020ReverseStructure.build_extension N
    (seeds N C fa fb) (OEdges N C) (OWeight N C) (OBound N C)
    (Pilot5bMeta1020Reverse.initial N (fnet N C))
  change (Pilot5bMeta1020Reverse.net _).head? = _
  unfold state
  rw [he]
  change (fnet N C ++ hs).head? = _
  have hh := forward_head N C
  cases hg : fnet N C with
  | nil => simp [hg] at hh
  | cons g gs => simpa only [hg, List.cons_append, List.head?_cons] using hh

lemma net_or_fanin {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ)
    (hm : PEqualNP.MetaComplexity.Monotone2 C) (rs : List ℕ)
    (hr : Sum.inl rs ∈ net N C fa fb) : rs.length ≤ 2 := by
  exact Pilot5bMeta1020ReverseStructure.build_fanin N (seeds N C fa fb)
    (OEdges N C) (OWeight N C) (OBound N C)
    (Pilot5bMeta1020Reverse.initial N (fnet N C))
    (Pilot5bMeta1020Forward.normalize_or_fanin N C hm) rs hr

lemma net_label_degree_le_one {J : ℕ} (N : ℕ) (C : Circuit)
    (fa fb : Fin J → ℕ) (a r : ℕ) (hr : Sum.inr (a, r) ∈ net N C fa fb) :
    ODegree N C a ≤ 1 := by
  rcases Pilot5bMeta1020ReverseStructure.build_label_origin N (seeds N C fa fb)
      (OEdges N C) (OWeight N C) (OBound N C)
      (Pilot5bMeta1020Reverse.initial N (fnet N C)) a r hr with hf | hw
  · exact Pilot5bMeta1020Forward.normalize_label_degree_le_one N C a r hf
  · obtain ⟨w, _, hw⟩ := hw
    have hd := OriginalGraph.weight_some_degree N C w a hw
    exact Nat.le_trans (Nat.le_of_eq hd) (by omega)

lemma degreeTwo_card_eq_count (N : ℕ) (C : Circuit) :
    (GraphBudget.degreeTwo N C).card =
      Pilot5bMeta1020Forward.degreeCount N 2 C.gates := by
  exact (Pilot5bMeta1020Forward.degreeCount_two_eq_range_card N C).symm

lemma forks_card_eq_count (N : ℕ) (C : Circuit) :
    (GraphBudget.forks N C).card =
      Pilot5bMeta1020Forward.forkCount N C.gates := by
  exact (Pilot5bMeta1020Forward.forkCount_eq_global_fork_card N C).symm

lemma net_length_add_usedForks_le {J : ℕ} (N : ℕ) (C : Circuit)
    (fa fb : Fin J → ℕ) (hm : PEqualNP.MetaComplexity.Monotone2 C) :
    (net N C fa fb).length + (usedForks N C fa fb).card ≤
      1 + Pilot5bMeta1020Forward.degreeCount N 1 C.gates +
        3 * Pilot5bMeta1020Forward.degreeCount N 2 C.gates + J := by
  have hb := Pilot5bMeta1020Forward.normalize_net_length_classified N C
  rw [← forks_card_eq_count N C] at hb
  have h := GraphReverseBudget.normalized_reverse_budget
    N C (seeds N C fa fb) (Pilot5bMeta1020Reverse.initial N (fnet N C))
    (Pilot5bMeta1020Forward.degreeCount N 1 C.gates)
    (Pilot5bMeta1020Forward.degreeCount N 2 C.gates)
    (fun g hg => (hm g hg).2) (degreeTwo_card_eq_count N C) hb
  change (net N C fa fb).length + (usedForks N C fa fb).card ≤
    1 + Pilot5bMeta1020Forward.degreeCount N 1 C.gates +
      3 * Pilot5bMeta1020Forward.degreeCount N 2 C.gates + (seeds N C fa fb).length at h
  simpa only [seeds_length] using h

end Pilot5bMeta1020OriginalNormalization
end PEqualNP.Outside.L_meta_1020

open PEqualNP.Outside.L_meta_1020

theorem PEqualNP.Outside.L_meta_1020 :
∀ (N Jn : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (Ckt : PEqualNP.CircuitLowerBounds.Circuit) (fa fb : Fin Jn → ℕ) (fr : ℕ), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 Ckt → (∀ jd : Fin Jn, (Ckt.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (fa jd) 0 ≤ 2 ∧ (Ckt.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (fb jd) 0 ≤ 1) → (∀ (jb : Fin Jn) (zz : Fin (N + N) → Bool), (Ckt.wires (List.ofFn zz)).getD (fa jb) false = true → (Ckt.wires (List.ofFn zz)).getD (fb jb) false = true → ∃ (pa lb : Fin N), I pa lb ∧ zz (Fin.castAdd N pa) = true ∧ zz (Fin.natAdd N lb) = true) → (Finset.univ.filter (fun e2 : Fin N × Fin N => I e2.1 e2.2 ∧ (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD fr false = false ∧ (∃ jc : Fin Jn, (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fa jc) false = true ∧ (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fb jc) false = true) ∧ ∀ jk : Fin Jn, (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fa jk) false = true → (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fb jk) false = true → (Ckt.wires (List.ofFn (fun vp : Fin (N + N) => decide (vp = Fin.castAdd N e2.1)))).getD (fa jk) false = false ∧ (Ckt.wires (List.ofFn (fun vp : Fin (N + N) => decide (vp = Fin.castAdd N e2.1)))).getD (fb jk) false = false)).card ≤ 100 * (Ckt.size + Jn) + 4 * N := by
  intro N Jn I _ Ckt fa fb fr hI hm hd hsound
  classical
  by_cases hJ : Jn = 0
  · subst Jn
    simp
  · let E : Finset (Fin N × Fin N) := Finset.univ.filter fun e =>
      I e.1 e.2 ∧
      (Ckt.wires (List.ofFn (Pilot5bMeta1020Forward.pairInput e.1 e.2))).getD fr false = false ∧
      (∃ j : Fin Jn,
        (Ckt.wires (List.ofFn (Pilot5bMeta1020Forward.pairInput e.1 e.2))).getD (fa j) false = true ∧
        (Ckt.wires (List.ofFn (Pilot5bMeta1020Forward.pairInput e.1 e.2))).getD (fb j) false = true) ∧
      ∀ j : Fin Jn,
        (Ckt.wires (List.ofFn (Pilot5bMeta1020Forward.pairInput e.1 e.2))).getD (fa j) false = true →
        (Ckt.wires (List.ofFn (Pilot5bMeta1020Forward.pairInput e.1 e.2))).getD (fb j) false = true →
        (Ckt.wires (List.ofFn (Pilot5bMeta1020Forward.pointInput e.1))).getD (fa j) false = false ∧
        (Ckt.wires (List.ofFn (Pilot5bMeta1020Forward.pointInput e.1))).getD (fb j) false = false
    change E.card ≤ 100 * (Ckt.size + Jn) + 4 * N
    have hda : ∀ j, Pilot5bMeta1020OriginalNormalization.ODegree N Ckt (fa j) ≤ 2 :=
      fun j => (hd j).1
    have hdb : ∀ j, Pilot5bMeta1020OriginalNormalization.ODegree N Ckt (fb j) ≤ 1 :=
      fun j => (hd j).2
    have hcount : E.card ≤
        18 * (Pilot5bMeta1020LowDegreeCover.lowGates Ckt (N + N) (Finset.Ico N (N + N)) 1).card +
        28 * (Pilot5bMeta1020OriginalNormalization.net N Ckt fa fb).length +
        27 * (Pilot5bMeta1020OriginalNormalization.jobs N Ckt fa fb).length := by
      refine Pilot5bMeta1020LinearTripleBound.linear_triple_bound I hI Ckt hm
        (Pilot5bMeta1020OriginalNormalization.net N Ckt fa fb)
        (Pilot5bMeta1020OriginalNormalization.net_head N Ckt fa fb)
        (Pilot5bMeta1020OriginalNormalization.net_or_fanin N Ckt fa fb hm)
        ?_ (Pilot5bMeta1020OriginalNormalization.roots N Ckt fa fb) ?_ E ?_
      · intro a r hr
        exact Pilot5bMeta1020OriginalNormalization.net_label_degree_le_one N Ckt fa fb a r hr
      · intro j x y h0 h1 h2
        apply Pilot5bMeta1020OriginalNormalization.roots_sound_functions
          N I Ckt fa fb hm hda hdb hsound x y j
        intro i
        fin_cases i
        · exact h0
        · exact h1
        · exact h2
      · intro e he
        obtain ⟨hi, _, ⟨j, ha, hb⟩, hz⟩ := (Finset.mem_filter.mp he).2
        obtain ⟨hza, hzb⟩ := hz j ha hb
        exact ⟨hi, Pilot5bMeta1020OriginalNormalization.roots_cover_pair
          N Ckt fa fb hm hda hdb e.1 e.2 j ha hb hza hzb⟩
    apply Pilot5bMeta1020FinalBudget.final_bound E.card
      (Pilot5bMeta1020LowDegreeCover.lowGates Ckt (N + N) (Finset.Ico N (N + N)) 1).card
      (Pilot5bMeta1020OriginalNormalization.net N Ckt fa fb).length
      (Pilot5bMeta1020OriginalNormalization.jobs N Ckt fa fb).length
      (Pilot5bMeta1020Forward.degreeCount N 0 Ckt.gates)
      (Pilot5bMeta1020Forward.degreeCount N 1 Ckt.gates)
      (Pilot5bMeta1020Forward.degreeCount N 2 Ckt.gates) Jn
      (Pilot5bMeta1020OriginalNormalization.usedForks N Ckt fa fb).card Ckt.size N
      hcount
    · exact Nat.le_of_eq (Pilot5bMeta1020Forward.degreeCount_zero_one_eq_low_card N Ckt).symm
    · exact Pilot5bMeta1020OriginalNormalization.net_length_add_usedForks_le N Ckt fa fb hm
    · exact Nat.le_of_eq (Pilot5bMeta1020OriginalNormalization.jobs_length N Ckt fa fb)
    · exact Pilot5bMeta1020Forward.degreeCount_zero_one_two_le_length N Ckt.gates
    · omega
