import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1465

-- two tournaments on 0..6: out c p is the set of points beaten by p
def out (c : Bool) (p : ℕ) : List ℕ :=
  match c, p with
  | true, 0 => [1, 3, 5]
  | true, 1 => [2, 3, 6]
  | true, 2 => [0, 5, 6]
  | true, 3 => [2, 4, 5]
  | true, 4 => [0, 1, 2]
  | true, 5 => [1, 4, 6]
  | true, 6 => [0, 3, 4]
  | false, 0 => [1, 3, 6]
  | false, 1 => [2, 3, 5]
  | false, 2 => [0, 5, 6]
  | false, 3 => [2, 4, 6]
  | false, 4 => [0, 1, 2]
  | false, 5 => [0, 3, 4]
  | false, 6 => [1, 4, 5]
  | _, _ => []

def domb (c : Bool) (u : Finset ℕ) : Bool :=
  decide (∃ p ∈ Finset.range 7, p ∉ u ∧ ∀ y ∈ u, y ∈ out c p)

theorem anti : ∀ c : Bool, ∀ p ∈ Finset.range 7, ∀ y ∈ Finset.range 7,
    y ∈ out c p → p ∉ out c y := by decide

theorem fact1 : ∀ c : Bool, ∀ u ∈ (Finset.range 7).powerset, u.card ≤ 2 → domb c u = true := by
  decide +kernel

theorem fact2 : ∀ c : Bool, domb c {0, 1, 2} = true ∧ domb c {0, 3, 4} = true := by
  decide +kernel

theorem fact3 : ∀ u ∈ (Finset.range 7).powerset, u.card = 3 → (u ∩ {0, 1, 2}).card = 1 →
    (u ∩ {0, 3, 4}).card = 1 → domb true u = false →
    domb false u = true ∧
    ∀ v ∈ (Finset.range 7).powerset, v.card = 3 → (v ∩ {0, 1, 2}).card = 1 →
      (v ∩ {0, 3, 4}).card = 1 → (u ∩ v).card = 1 → domb false v = true := by
  decide +kernel

theorem label (n : ℕ) (F A B : Finset (Fin n)) (hF : F.card = 7) (hA : A ⊆ F) (hB : B ⊆ F) :
    ∃ g : Fin n → ℕ, Function.Injective g ∧ (∀ a ∈ F, g a < 7) ∧ (∀ k < 7, ∃ a ∈ F, g a = k) ∧
      (∀ a ∈ A, g a < A.card) ∧
      (∀ a ∈ B, g a < (A ∩ B).card ∨ (A.card ≤ g a ∧ g a < A.card + (B \ A).card)) := by
  classical
  obtain ⟨l, hl⟩ : ∃ l : List (Fin n), l = (A ∩ B).toList ++ ((A \ B).toList ++
    ((B \ A).toList ++ (F \ (A ∪ B)).toList)) := ⟨_, rfl⟩
  have hmem : ∀ a, a ∈ l ↔ a ∈ F := by
    intro a
    have h1 := @hA a
    have h2 := @hB a
    simp only [hl, List.mem_append, Finset.mem_toList, Finset.mem_inter, Finset.mem_sdiff,
      Finset.mem_union]
    tauto
  have hnd : l.Nodup := by
    rw [hl]
    simp only [List.nodup_append, Finset.nodup_toList, Finset.mem_toList, Finset.mem_inter,
      Finset.mem_sdiff, Finset.mem_union, List.mem_append, true_and]
    and_intros
    all_goals
      intro a ha b hb hab
      subst hab
      tauto
  have hlen : l.length = 7 := by
    rw [← hF, ← List.toFinset_card_of_nodup hnd]
    congr 1
    ext a
    simp [hmem]
  have hcA : (A ∩ B).card + (A \ B).card = A.card := by
    have := Finset.card_sdiff_add_card_inter A B
    omega
  refine ⟨fun a => if a ∈ F then l.idxOf a else 7 + a.val, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    simp only at hab
    by_cases ha : a ∈ F
    · have ha' : l.idxOf a < 7 := by
        rw [← hlen]
        exact List.idxOf_lt_length_iff.mpr ((hmem a).mpr ha)
      by_cases hb : b ∈ F
      · simp only [ha, hb, ↓reduceIte] at hab
        exact (List.idxOf_inj ((hmem a).mpr ha)).mp hab
      · simp only [ha, hb, ↓reduceIte] at hab
        omega
    · by_cases hb : b ∈ F
      · have hb' : l.idxOf b < 7 := by
          rw [← hlen]
          exact List.idxOf_lt_length_iff.mpr ((hmem b).mpr hb)
        simp only [ha, hb, ↓reduceIte] at hab
        omega
      · simp only [ha, hb, ↓reduceIte] at hab
        apply Fin.ext
        omega
  · intro a ha
    simp only [ha, ↓reduceIte]
    rw [← hlen]
    exact List.idxOf_lt_length_iff.mpr ((hmem a).mpr ha)
  · intro k hk
    have hk' : k < l.length := by omega
    refine ⟨l[k], (hmem _).mp (List.getElem_mem hk'), ?_⟩
    have hin := (hmem _).mp (List.getElem_mem hk')
    simp only [hin, ↓reduceIte]
    exact hnd.idxOf_getElem k hk'
  · intro a ha
    have hin := hA ha
    simp only [hin, ↓reduceIte]
    by_cases hb : a ∈ B
    · have h1 : a ∈ (A ∩ B).toList := by simp [ha, hb]
      rw [hl, List.idxOf_append_of_mem h1]
      have := List.idxOf_lt_length_iff.mpr h1
      rw [Finset.length_toList] at this
      omega
    · have h1 : a ∉ (A ∩ B).toList := by simp [hb]
      have h2 : a ∈ (A \ B).toList := by simp [ha, hb]
      rw [hl, List.idxOf_append_of_notMem h1, List.idxOf_append_of_mem h2]
      have := List.idxOf_lt_length_iff.mpr h2
      rw [Finset.length_toList] at this
      rw [Finset.length_toList]
      omega
  · intro a hb
    have hin := hB hb
    simp only [hin, ↓reduceIte]
    by_cases ha : a ∈ A
    · left
      have h1 : a ∈ (A ∩ B).toList := by simp [ha, hb]
      rw [hl, List.idxOf_append_of_mem h1]
      have := List.idxOf_lt_length_iff.mpr h1
      rw [Finset.length_toList] at this
      exact this
    · right
      have h1 : a ∉ (A ∩ B).toList := by simp [ha]
      have h2 : a ∉ (A \ B).toList := by simp [ha]
      have h3 : a ∈ (B \ A).toList := by simp [ha, hb]
      rw [hl, List.idxOf_append_of_notMem h1, List.idxOf_append_of_notMem h2,
        List.idxOf_append_of_mem h3]
      have := List.idxOf_lt_length_iff.mpr h3
      rw [Finset.length_toList] at this
      rw [Finset.length_toList, Finset.length_toList]
      omega

theorem finish (n m : ℕ) (S : Fin m → Finset (Fin n)) (F : Finset (Fin n)) (g : Fin n → ℕ)
    (hlt : ∀ a ∈ F, g a < 7) (hsurj : ∀ k < 7, ∃ a ∈ F, g a = k) (c : Bool)
    (hdom : ∀ i : Fin m, domb c ((S i ∩ F).image g) = true) :
    ∃ (r : Fin n → Fin n → Prop) (f : Fin m → Fin n), (∀ a b : Fin n, r a b → ¬ r b a) ∧
      ∀ i : Fin m, f i ∈ F ∧ f i ∉ S i ∧ ∀ y ∈ S i ∩ F, r (f i) y := by
  have h : ∀ i : Fin m, ∃ q, q ∈ F ∧ q ∉ S i ∧ ∀ y ∈ S i ∩ F, g y ∈ out c (g q) := by
    intro i
    have h1 := hdom i
    unfold domb at h1
    rw [decide_eq_true_eq] at h1
    obtain ⟨p, hp, hpu, hall⟩ := h1
    obtain ⟨q, hqF, hq⟩ := hsurj p (Finset.mem_range.mp hp)
    refine ⟨q, hqF, ?_, ?_⟩
    · intro hqS
      apply hpu
      rw [← hq]
      exact Finset.mem_image_of_mem g (Finset.mem_inter.mpr ⟨hqS, hqF⟩)
    · intro y hy
      rw [hq]
      exact hall _ (Finset.mem_image_of_mem g hy)
  choose f hf using h
  refine ⟨fun a b => a ∈ F ∧ b ∈ F ∧ g b ∈ out c (g a), f, ?_, ?_⟩
  · rintro a b ⟨ha, hb, hab⟩ ⟨_, _, hba⟩
    exact anti c (g a) (Finset.mem_range.mpr (hlt a ha)) (g b)
      (Finset.mem_range.mpr (hlt b hb)) hab hba
  · intro i
    refine ⟨(hf i).1, (hf i).2.1, ?_⟩
    intro y hy
    exact ⟨(hf i).1, (Finset.mem_inter.mp hy).2, (hf i).2.2 y hy⟩

end PEqualNP.Outside.L_meta_1465

theorem PEqualNP.Outside.L_meta_1465 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (F : Finset (Fin n)),
    F.card = 7 → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) →
    (∀ i : Fin m, (S i ∩ F).card ≤ 3) →
    (∀ i j : Fin m, i ≠ j → (S i ∩ F).card = 3 → (S j ∩ F).card = 3 → (S i ∩ S j ∩ F).Nonempty) →
    ∃ (r : Fin n → Fin n → Prop) (f : Fin m → Fin n), (∀ a b : Fin n, r a b → ¬ r b a) ∧
      ∀ i : Fin m, f i ∈ F ∧ f i ∉ S i ∧ ∀ y ∈ S i ∩ F, r (f i) y := by
  classical
  intro n m S F hF hlin h3 hmeet
  -- generic facts for a labelling g
  have key : ∀ g : Fin n → ℕ, Function.Injective g → (∀ a ∈ F, g a < 7) →
      (∀ i : Fin m, ((S i ∩ F).image g).card = (S i ∩ F).card ∧
        (S i ∩ F).image g ∈ (Finset.range 7).powerset) ∧
      (∀ i j : Fin m, i ≠ j → (S i ∩ F).card = 3 → (S j ∩ F).card = 3 →
        ((S i ∩ F).image g ∩ (S j ∩ F).image g).card = 1) := by
    intro g hinj hlt
    refine ⟨fun i => ⟨Finset.card_image_of_injective _ hinj, ?_⟩, ?_⟩
    · rw [Finset.mem_powerset]
      intro x hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_range.mpr (hlt a (Finset.mem_inter.mp ha).2)
    · intro i j hij hi hj
      rw [← Finset.image_inter _ _ hinj, Finset.card_image_of_injective _ hinj]
      have h1 : (S i ∩ F ∩ (S j ∩ F)).card ≤ 1 := by
        refine le_trans (Finset.card_le_card ?_) (hlin i j hij)
        intro x hx
        simp only [Finset.mem_inter] at hx ⊢
        tauto
      have h2 : 0 < (S i ∩ F ∩ (S j ∩ F)).card := by
        obtain ⟨x, hx⟩ := hmeet i j hij hi hj
        refine Finset.card_pos.mpr ⟨x, ?_⟩
        simp only [Finset.mem_inter] at hx ⊢
        tauto
      omega
  by_cases hex : ∃ i1 : Fin m, (S i1 ∩ F).card = 3
  · obtain ⟨i1, hi1⟩ := hex
    by_cases hex2 : ∃ i2 : Fin m, i2 ≠ i1 ∧ (S i2 ∩ F).card = 3
    · obtain ⟨i2, hne, hi2⟩ := hex2
      obtain ⟨g, hinj, hlt, hsurj, hgA, hgB⟩ := PEqualNP.Outside.L_meta_1465.label n F
        (S i1 ∩ F) (S i2 ∩ F) hF Finset.inter_subset_right Finset.inter_subset_right
      obtain ⟨hk1, hk2⟩ := key g hinj hlt
      have hAB : (S i1 ∩ F ∩ (S i2 ∩ F)).card = 1 := by
        have h1 : (S i1 ∩ F ∩ (S i2 ∩ F)).card ≤ 1 := by
          refine le_trans (Finset.card_le_card ?_) (hlin i1 i2 (Ne.symm hne))
          intro x hx
          simp only [Finset.mem_inter] at hx ⊢
          tauto
        have h2 : 0 < (S i1 ∩ F ∩ (S i2 ∩ F)).card := by
          obtain ⟨x, hx⟩ := hmeet i1 i2 (Ne.symm hne) hi1 hi2
          refine Finset.card_pos.mpr ⟨x, ?_⟩
          simp only [Finset.mem_inter] at hx ⊢
          tauto
        omega
      have hBA : ((S i2 ∩ F) \ (S i1 ∩ F)).card = 2 := by
        have := Finset.card_sdiff_add_card_inter (S i2 ∩ F) (S i1 ∩ F)
        rw [Finset.inter_comm (S i2 ∩ F) (S i1 ∩ F)] at this
        omega
      rw [hi1] at hgA
      rw [hAB, hi1, hBA] at hgB
      have e1 : (S i1 ∩ F).image g = {0, 1, 2} := by
        apply Finset.eq_of_subset_of_card_le
        · intro x hx
          obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
          have := hgA a ha
          simp only [Finset.mem_insert, Finset.mem_singleton]
          omega
        · rw [(hk1 i1).1, hi1]
          decide
      have e2 : (S i2 ∩ F).image g = {0, 3, 4} := by
        apply Finset.eq_of_subset_of_card_le
        · intro x hx
          obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
          have := hgB a ha
          simp only [Finset.mem_insert, Finset.mem_singleton]
          omega
        · rw [(hk1 i2).1, hi2]
          decide
      have cond : ∀ j : Fin m, j ≠ i1 → j ≠ i2 → (S j ∩ F).card = 3 →
          ((S j ∩ F).image g ∩ {0, 1, 2}).card = 1 ∧
          ((S j ∩ F).image g ∩ {0, 3, 4}).card = 1 := by
        intro j hj1 hj2 hj
        rw [← e1, ← e2]
        exact ⟨hk2 j i1 hj1 hj hi1, hk2 j i2 hj2 hj hi2⟩
      by_cases hc : ∃ j : Fin m, j ≠ i1 ∧ j ≠ i2 ∧ (S j ∩ F).card = 3 ∧
          PEqualNP.Outside.L_meta_1465.domb true ((S j ∩ F).image g) = false
      · obtain ⟨j, hj1, hj2, hj, hjd⟩ := hc
        have hf3 := PEqualNP.Outside.L_meta_1465.fact3 _ (hk1 j).2 ((hk1 j).1.trans hj)
          (cond j hj1 hj2 hj).1 (cond j hj1 hj2 hj).2 hjd
        refine PEqualNP.Outside.L_meta_1465.finish n m S F g hlt hsurj false ?_
        intro i
        by_cases hi : (S i ∩ F).card = 3
        · by_cases hii1 : i = i1
          · rw [hii1, e1]
            exact (PEqualNP.Outside.L_meta_1465.fact2 false).1
          · by_cases hii2 : i = i2
            · rw [hii2, e2]
              exact (PEqualNP.Outside.L_meta_1465.fact2 false).2
            · by_cases hij : i = j
              · rw [hij]
                exact hf3.1
              · exact hf3.2 _ (hk1 i).2 ((hk1 i).1.trans hi) (cond i hii1 hii2 hi).1
                  (cond i hii1 hii2 hi).2 (hk2 j i (Ne.symm hij) hj hi)
        · have := h3 i
          exact PEqualNP.Outside.L_meta_1465.fact1 false _ (hk1 i).2 (by
            rw [(hk1 i).1]
            omega)
      · refine PEqualNP.Outside.L_meta_1465.finish n m S F g hlt hsurj true ?_
        intro i
        by_cases hi : (S i ∩ F).card = 3
        · by_cases hii1 : i = i1
          · rw [hii1, e1]
            exact (PEqualNP.Outside.L_meta_1465.fact2 true).1
          · by_cases hii2 : i = i2
            · rw [hii2, e2]
              exact (PEqualNP.Outside.L_meta_1465.fact2 true).2
            · by_contra hcon
              exact hc ⟨i, hii1, hii2, hi, Bool.eq_false_of_not_eq_true hcon⟩
        · have := h3 i
          exact PEqualNP.Outside.L_meta_1465.fact1 true _ (hk1 i).2 (by
            rw [(hk1 i).1]
            omega)
    · obtain ⟨g, hinj, hlt, hsurj, hgA, -⟩ := PEqualNP.Outside.L_meta_1465.label n F
        (S i1 ∩ F) (S i1 ∩ F) hF Finset.inter_subset_right Finset.inter_subset_right
      obtain ⟨hk1, -⟩ := key g hinj hlt
      rw [hi1] at hgA
      have e1 : (S i1 ∩ F).image g = {0, 1, 2} := by
        apply Finset.eq_of_subset_of_card_le
        · intro x hx
          obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
          have := hgA a ha
          simp only [Finset.mem_insert, Finset.mem_singleton]
          omega
        · rw [(hk1 i1).1, hi1]
          decide
      refine PEqualNP.Outside.L_meta_1465.finish n m S F g hlt hsurj true ?_
      intro i
      by_cases hii1 : i = i1
      · rw [hii1, e1]
        exact (PEqualNP.Outside.L_meta_1465.fact2 true).1
      · have := h3 i
        have hi : (S i ∩ F).card ≠ 3 := fun h => hex2 ⟨i, hii1, h⟩
        exact PEqualNP.Outside.L_meta_1465.fact1 true _ (hk1 i).2 (by
          rw [(hk1 i).1]
          omega)
  · obtain ⟨g, hinj, hlt, hsurj, -, -⟩ := PEqualNP.Outside.L_meta_1465.label n F
      ∅ ∅ hF (Finset.empty_subset _) (Finset.empty_subset _)
    obtain ⟨hk1, -⟩ := key g hinj hlt
    refine PEqualNP.Outside.L_meta_1465.finish n m S F g hlt hsurj true ?_
    intro i
    have := h3 i
    have hi : (S i ∩ F).card ≠ 3 := fun h => hex ⟨i, h⟩
    exact PEqualNP.Outside.L_meta_1465.fact1 true _ (hk1 i).2 (by
      rw [(hk1 i).1]
      omega)
