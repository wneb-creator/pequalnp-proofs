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