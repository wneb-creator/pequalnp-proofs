import Mathlib
import PEqualNP.Defs

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

/-- Retain small leaves and propagate unions through earlier OR children. -/
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



namespace PEqualNP.Outside.L_meta_1020.BlockedPairs

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

end PEqualNP.Outside.L_meta_1020.BlockedPairs


namespace PEqualNP.Outside.L_meta_1020.SourceQueries

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


end PEqualNP.Outside.L_meta_1020.SourceQueries


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

namespace PEqualNP.Outside.L_meta_1020.MarkerNearStar

open PEqualNP.Outside.L_meta_1020.SourceQueries
open PEqualNP.Outside.L_meta_1020.BlockedPairs

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

end PEqualNP.Outside.L_meta_1020.MarkerNearStar

namespace PEqualNP.Outside.L_meta_1020.MarkerNearStar

open Pilot5bMeta1020FirstQuery
open PEqualNP.Outside.L_meta_1020.SourceQueries

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

end PEqualNP.Outside.L_meta_1020.MarkerNearStar

namespace PEqualNP.Outside.L_meta_1020.MarkerNearStar

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

end PEqualNP.Outside.L_meta_1020.MarkerNearStar

namespace PEqualNP.Outside.L_meta_1020.HonestMarkers

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

end PEqualNP.Outside.L_meta_1020.HonestMarkers
namespace Pilot5bMeta1020TripleCounting

open PEqualNP.Outside.L_meta_1020.MarkerNearStar

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

open PEqualNP.Outside.L_meta_1020.MarkerNearStar

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
    PEqualNP.Outside.L_meta_1020.HonestMarkers.triple_honest_accept_cover
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
      (PEqualNP.Outside.L_meta_1020.HonestMarkers.mem_pencil I p u).mp (hb.2.1 hu))
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
    (hmono : ∀ r, PEqualNP.Outside.L_meta_1020.MarkerNearStar.MonoEval (F r))
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
      PEqualNP.Outside.L_meta_1020.HonestMarkers.singleton_markers_card bare roots
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
    (hmono : ∀ r, PEqualNP.Outside.L_meta_1020.MarkerNearStar.MonoEval (F r))
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

@[simp] lemma hits_empty {n : ℕ} (y : Fin n → Bool) : hits y ∅ = false := by
  simp [hits]

@[simp] lemma hits_singleton {n : ℕ} (y : Fin n → Bool) (l : Fin n) :
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

attribute [local instance] Classical.propDecidable

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

/-! Adapter to append after the LinearNetwork declarations. -/
namespace Pilot5bMeta1020BareCircuit

open PEqualNP.CircuitLowerBounds Pilot5bMeta1020Linear

def bareGate (labels : ℕ → Bool) : Instruction → Gate
  | Sum.inl rs => ⟨GateOp.or, rs⟩
  | Sum.inr (a, r) => ⟨GateOp.or, if labels a then [r] else []⟩

def bareCircuit (gs : List Instruction) (labels : ℕ → Bool) : Circuit :=
  ⟨gs.map (bareGate labels), 0⟩

@[simp] lemma bareGate_op (labels : ℕ → Bool) (g : Instruction) :
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

@[simp] lemma size_eq (gs : List Instruction) (labels : ℕ → Bool) :
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
    PEqualNP.Outside.L_meta_1020.MarkerNearStar.MonoEval (eval gs L r) := by
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
