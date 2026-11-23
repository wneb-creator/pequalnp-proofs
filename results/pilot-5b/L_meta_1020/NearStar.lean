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
