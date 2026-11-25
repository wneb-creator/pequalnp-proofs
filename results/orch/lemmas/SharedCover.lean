import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2732_aux.Frontier

def insertion {n : ℕ} (k N : ℕ) (S : ℕ → Finset (Fin n)) (a b : ℕ → ℕ) (A : ℕ → Bool) : Finset ℕ :=
  (Finset.range N).filter fun w => k ≤ w ∧ A w = false ∧ S w ≠ ∅ ∧
    (S (a w) = ∅ ∨ S (b w) = ∅)

def emptyChild {n : ℕ} (S : ℕ → Finset (Fin n)) (a b : ℕ → ℕ) (w : ℕ) : ℕ :=
  if S (a w) = ∅ then a w else b w

def boundary {n : ℕ} (k N : ℕ) (S : ℕ → Finset (Fin n)) (a b : ℕ → ℕ) (A : ℕ → Bool) : Finset ℕ :=
  (insertion k N S a b A).image (emptyChild S a b)

lemma boundary_card {n : ℕ} (k N : ℕ) (S : ℕ → Finset (Fin n)) (a b : ℕ → ℕ) (A : ℕ → Bool) :
    (boundary k N S a b A).card ≤ (insertion k N S a b A).card := Finset.card_image_le

lemma boundary_spec {n : ℕ} (k N : ℕ) (S : ℕ → Finset (Fin n)) (a b : ℕ → ℕ) (A : ℕ → Bool)
    (hparents : ∀ w, k ≤ w → w < N → a w < w ∧ b w < w)
    (j : ℕ) (hj : j ∈ boundary k N S a b A) : j < N ∧ S j = ∅ := by
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hj
  obtain ⟨hwN, hwk, _, _, he⟩ : w < N ∧ k ≤ w ∧ A w = false ∧ S w ≠ ∅ ∧
      (S (a w) = ∅ ∨ S (b w) = ∅) := by simpa [insertion] using hw
  have hp := hparents w hwk hwN
  by_cases ha : S (a w) = ∅
  · simp only [emptyChild, ite_eq_left ha]
    exact ⟨by omega, ha⟩
  · simp only [emptyChild, ite_eq_right ha]
    exact ⟨by omega, he.resolve_left ha⟩

lemma insertion_no_growth {n : ℕ} (k N : ℕ) (S : ℕ → Finset (Fin n)) (a b : ℕ → ℕ) (A : ℕ → Bool)
    (hunion : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (w : ℕ) (hw : w ∈ insertion k N S a b A) : S w = S (a w) ∨ S w = S (b w) := by
  obtain ⟨hwN, hwk, hwA, _, he⟩ : w < N ∧ k ≤ w ∧ A w = false ∧ S w ≠ ∅ ∧
      (S (a w) = ∅ ∨ S (b w) = ∅) := by simpa [insertion] using hw
  have hu := hunion w hwk hwN hwA
  rcases he with ha | hb
  · exact Or.inr (by simpa only [ha, Finset.empty_union] using hu)
  · exact Or.inl (by simpa only [hb, Finset.union_empty] using hu)

lemma pair_hit_boundary (n k N : ℕ) (S : ℕ → Finset (Fin n))
    (H : ℕ → Fin n → Fin n → Prop) (a b : ℕ → ℕ) (A : ℕ → Bool)
    (hinput : ∀ w u v, w < k → H w u v → u ∈ S w ∨ v ∈ S w)
    (hparents : ∀ w, k ≤ w → w < N → a w < w ∧ b w < w)
    (hzero : ∀ w, k ≤ w → w < N → A w = true → S w = ∅)
    (hunion : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (horH : ∀ w u v, k ≤ w → w < N → A w = false → H w u v → H (a w) u v ∨ H (b w) u v)
    (r : ℕ) (hr : r < N) (hne : S r ≠ ∅) (u v : Fin n)
    (hpair : H r u v) (hu : u ∉ S r) (hv : v ∉ S r) :
    ∃ j ∈ boundary k N S a b A, H j u v := by
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    by_cases hk : k ≤ r
    · have hp := hparents r hk hr
      have hop : A r = false := by
        cases he : A r with
        | false => rfl
        | true => exact (hne (hzero r hk hr he)).elim
      have hs := hunion r hk hr hop
      have hnuA : u ∉ S (a r) := fun h => hu (hs ▸ Finset.mem_union_left _ h)
      have hnvA : v ∉ S (a r) := fun h => hv (hs ▸ Finset.mem_union_left _ h)
      have hnuB : u ∉ S (b r) := fun h => hu (hs ▸ Finset.mem_union_right _ h)
      have hnvB : v ∉ S (b r) := fun h => hv (hs ▸ Finset.mem_union_right _ h)
      rcases horH r u v hk hr hop hpair with hA | hB
      · by_cases hz : S (a r) = ∅
        · have hi : r ∈ insertion k N S a b A := by simp [insertion, hr, hk, hop, hne, hz]
          refine ⟨emptyChild S a b r, Finset.mem_image_of_mem _ hi, ?_⟩
          simpa only [emptyChild, ite_eq_left hz] using hA
        · exact ih (a r) hp.1 (by omega) hz hA hnuA hnvA
      · by_cases hz : S (b r) = ∅
        · have ha : S (a r) ≠ ∅ := by
            intro he
            exact hne (by simpa only [he, hz, Finset.empty_union] using hs)
          have hi : r ∈ insertion k N S a b A := by simp [insertion, hr, hk, hop, hne, hz]
          refine ⟨emptyChild S a b r, Finset.mem_image_of_mem _ hi, ?_⟩
          simpa only [emptyChild, ite_eq_right ha] using hB
        · exact ih (b r) hp.2 (by omega) hz hB hnuB hnvB
    · rcases hinput r u v (by omega) hpair with h | h
      · exact (hu h).elim
      · exact (hv h).elim

end PEqualNP.Outside.L_meta_2732_aux.Frontier

namespace PEqualNP.Outside.L_meta_2732_aux.Frontier

lemma countUnion {α : Type*} [DecidableEq α] (support : ℕ → Finset α)
    (paid : Finset ℕ) (m : ℕ)
    (step : ∀ w < m, 1 < (support w).card → ∃ cs : Finset ℕ,
      cs ⊆ Finset.range w ∧ support w ⊆ cs.biUnion support ∧
      cs.card ≤ 1 + (if w ∈ paid then 1 else 0))
    (roots : Finset ℕ) (hr : roots ⊆ Finset.range m) :
    (roots.biUnion support).card ≤ roots.card + ((Finset.range m) ∩ paid).card := by
  classical
  induction m generalizing roots with
  | zero =>
    have : roots = ∅ := by simpa using hr
    simp [this]
  | succ m ih =>
    have old := ih (fun w hw => step w (by omega))
    have hpre : roots.erase m ⊆ Finset.range m := by
      intro w hw
      have ⟨hne, hmem⟩ := Finset.mem_erase.mp hw
      have hlt := Finset.mem_range.mp (hr hmem)
      exact Finset.mem_range.mpr (by omega)
    have hcost : ((Finset.range (m + 1)) ∩ paid).card =
        ((Finset.range m) ∩ paid).card + (if m ∈ paid then 1 else 0) := by
      by_cases h : m ∈ paid
      · have he : Finset.range (m + 1) ∩ paid = insert m (Finset.range m ∩ paid) := by
          ext w
          by_cases hw : w = m <;> simp [Finset.range_add_one, hw, h]
        simp [he, h]
      · have he : Finset.range (m + 1) ∩ paid = Finset.range m ∩ paid := by
          ext w
          by_cases hw : w = m <;> simp [Finset.range_add_one, hw, h]
        simp [he, h]
    rw [hcost]
    by_cases hm : m ∈ roots
    · have hrins := Finset.insert_erase hm
      have hroots : (roots.erase m).card + 1 = roots.card :=
        Finset.card_erase_add_one hm
      by_cases hb : 1 < (support m).card
      · obtain ⟨cs, hcpre, hcov, hcard⟩ := step m (by omega) hb
        have hsub : roots.biUnion support ⊆ ((roots.erase m) ∪ cs).biUnion support := by
          intro a ha
          obtain ⟨w, hw, haw⟩ := Finset.mem_biUnion.mp ha
          by_cases heq : w = m
          · subst w
            obtain ⟨v, hv, hav⟩ := Finset.mem_biUnion.mp (hcov haw)
            exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_union_right _ hv, hav⟩
          · exact Finset.mem_biUnion.mpr
              ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨heq, hw⟩), haw⟩
        have hh := old ((roots.erase m) ∪ cs) (Finset.union_subset hpre hcpre)
        have hh' := Finset.card_le_card hsub
        have hu := Finset.card_union_le (roots.erase m) cs
        omega
      · have hh := old (roots.erase m) hpre
        have he : roots.biUnion support = support m ∪ (roots.erase m).biUnion support := by
          conv_lhs => rw [← hrins]
          rw [Finset.biUnion_insert]
        rw [he]
        have hu := Finset.card_union_le (support m) ((roots.erase m).biUnion support)
        omega
    · rw [Finset.erase_eq_of_notMem hm] at hpre
      have hh := old roots hpre
      omega

lemma dag_union_bound {α : Type*} [DecidableEq α] (f : ℕ → Finset α) (R B : Finset ℕ)
    (step : ∀ i, 1 < (f i).card → (∃ a < i, f i ⊆ f a) ∨
      (i ∈ B ∧ ∃ a < i, ∃ b < i, f i ⊆ f a ∪ f b)) :
    (R.biUnion f).card ≤ R.card + B.card := by
  classical
  let m := R.sup id + 1
  have hr : R ⊆ Finset.range m := by
    intro w hw
    have h : w ≤ R.sup id := Finset.le_sup (f := id) hw
    exact Finset.mem_range.mpr (by dsimp [m]; omega)
  have haux : (R.biUnion f).card ≤ R.card + (Finset.range m ∩ B).card := by
    apply countUnion f B m _ R hr
    intro i _ hi
    rcases step i hi with ⟨a, ha, hsub⟩ | ⟨hiB, a, ha, b, hb, hsub⟩
    · refine ⟨{a}, ?_, ?_, ?_⟩
      · simpa using ha
      · simpa using hsub
      · simp
    · refine ⟨{a,b}, ?_, ?_, ?_⟩
      · intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact Finset.mem_range.mpr ha
        · rw [Finset.mem_singleton.mp hw]
          exact Finset.mem_range.mpr hb
      · simpa using hsub
      · simp only [hiB, ite_true]
        exact Finset.card_le_two
  have hl := Finset.card_le_card (Finset.inter_subset_right (s₁ := Finset.range m) (s₂ := B))
  omega


end PEqualNP.Outside.L_meta_2732_aux.Frontier

namespace PEqualNP.Outside.L_meta_2732_aux.Frontier

def coverCert {n : ℕ} (k N : ℕ) (S : ℕ → Finset (Fin n))
    (a b : ℕ → ℕ) (A : ℕ → Bool)
    (ha : ∀ w, k ≤ w → w < N → a w < w)
    (hb : ∀ w, k ≤ w → w < N → b w < w) (w : ℕ) : Finset (Fin n) :=
  if (S w).card ≤ 1 then
    if _hg : k ≤ w ∧ w < N then
      if A w = true then
        if (S (a w)).card ≤ 1 then coverCert k N S a b A ha hb (a w)
        else coverCert k N S a b A ha hb (b w)
      else if w ∈ insertion k N S a b A then
        if S (a w) = ∅ then coverCert k N S a b A ha hb (b w)
        else coverCert k N S a b A ha hb (a w)
      else coverCert k N S a b A ha hb (a w) ∪ coverCert k N S a b A ha hb (b w)
    else S w
  else ∅
termination_by w
decreasing_by all_goals first | exact ha _ _hg.1 _hg.2 | exact hb _ _hg.1 _hg.2

lemma lift_covered {α : Type*} [DecidableEq α] (X Y T : Finset α) (u v : α)
    (hXY : X ⊆ Y ∪ T) (h : (u ∈ X ∨ v ∈ X) ∨ (u ∈ T ∨ v ∈ T)) :
    (u ∈ Y ∨ v ∈ Y) ∨ (u ∈ T ∨ v ∈ T) := by
  rcases h with (h | h) | h
  · rcases Finset.mem_union.mp (hXY h) with h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl h)
  · rcases Finset.mem_union.mp (hXY h) with h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inr h)
  · exact Or.inr h

lemma shared_boundary_cover (n k N : ℕ) (S : ℕ → Finset (Fin n))
    (H : ℕ → Fin n → Fin n → Prop) (a b : ℕ → ℕ) (A : ℕ → Bool)
    (hinput : ∀ w u v, w < k → H w u v → u ∈ S w ∨ v ∈ S w)
    (ha : ∀ w, k ≤ w → w < N → a w < w)
    (hb : ∀ w, k ≤ w → w < N → b w < w)
    (horS : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (horH : ∀ w u v, k ≤ w → w < N → A w = false → H w u v → H (a w) u v ∨ H (b w) u v)
    (handS : ∀ w, k ≤ w → w < N → A w = true → (S (a w)).card ≤ 1 ∨ (S (b w)).card ≤ 1)
    (handH : ∀ w u v, k ≤ w → w < N → A w = true → H w u v → H (a w) u v ∧ H (b w) u v) :
    ∃ T : Finset (Fin n),
      (∀ j ∈ boundary k N S a b A, ∀ u v, H j u v → u ∈ T ∨ v ∈ T) ∧
      T.card ≤ ((insertion k N S a b A) ∪ ((Finset.range N).filter fun w =>
        k ≤ w ∧ A w = false ∧ (S w).card ≤ 1)).card := by
  let I := insertion k N S a b A
  let R := boundary k N S a b A
  let small := (Finset.range N).filter fun w => k ≤ w ∧ A w = false ∧ (S w).card ≤ 1
  let B := small \ I
  let f := coverCert k N S a b A ha hb
  let T := R.biUnion f
  have feq (w : ℕ) : f w =
      if (S w).card ≤ 1 then
        if k ≤ w ∧ w < N then
          if A w = true then
            if (S (a w)).card ≤ 1 then f (a w) else f (b w)
          else if w ∈ I then
            if S (a w) = ∅ then f (b w) else f (a w)
          else f (a w) ∪ f (b w)
        else S w
      else ∅ := by exact coverCert.eq_1 ..
  have rootsub (j : ℕ) (hj : j ∈ R) : f j ⊆ T := by
    intro u hu
    exact Finset.mem_biUnion.mpr ⟨j, hj, hu⟩
  have hit : ∀ w, w < N → (S w).card ≤ 1 → ∀ u v, H w u v →
      (u ∈ f w ∨ v ∈ f w) ∨ (u ∈ T ∨ v ∈ T) := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw ht u v hwuv
      by_cases hkw : k ≤ w
      · have hia := ha w hkw hw
        have hib := hb w hkw hw
        cases hop : A w with
        | false =>
          have hu := horS w hkw hw hop
          have hta : (S (a w)).card ≤ 1 := by
            apply (Finset.card_le_card _).trans ht
            rw [hu]
            exact Finset.subset_union_left
          have htb : (S (b w)).card ≤ 1 := by
            apply (Finset.card_le_card _).trans ht
            rw [hu]
            exact Finset.subset_union_right
          have embedA : f (a w) ⊆ f w ∪ T := by
            by_cases hi : w ∈ I
            · by_cases hz : S (a w) = ∅
              · apply Finset.Subset.trans (rootsub (a w) ?_) Finset.subset_union_right
                have hm := Finset.mem_image_of_mem (emptyChild S a b) hi
                simpa only [R, boundary, I, emptyChild, ite_eq_left hz] using hm
              · rw [feq w, ite_eq_left ht, ite_eq_left ⟨hkw, hw⟩,
                  ite_eq_right (by simp [hop]), ite_eq_left hi, ite_eq_right hz]
                exact Finset.subset_union_left
            · rw [feq w, ite_eq_left ht, ite_eq_left ⟨hkw, hw⟩,
                ite_eq_right (by simp [hop]), ite_eq_right hi]
              exact Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left
          have embedB : f (b w) ⊆ f w ∪ T := by
            by_cases hi : w ∈ I
            · by_cases hz : S (a w) = ∅
              · rw [feq w, ite_eq_left ht, ite_eq_left ⟨hkw, hw⟩,
                  ite_eq_right (by simp [hop]), ite_eq_left hi, ite_eq_left hz]
                exact Finset.subset_union_left
              · apply Finset.Subset.trans (rootsub (b w) ?_) Finset.subset_union_right
                have hm := Finset.mem_image_of_mem (emptyChild S a b) hi
                simpa only [R, boundary, I, emptyChild, ite_eq_right hz] using hm
            · rw [feq w, ite_eq_left ht, ite_eq_left ⟨hkw, hw⟩,
                ite_eq_right (by simp [hop]), ite_eq_right hi]
              exact Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left
          rcases horH w u v hkw hw hop hwuv with h | h
          · exact lift_covered _ _ T u v embedA (ih _ hia (hia.trans hw) hta u v h)
          · exact lift_covered _ _ T u v embedB (ih _ hib (hib.trans hw) htb u v h)
        | true =>
          have hh := handH w u v hkw hw hop hwuv
          rw [feq w, ite_eq_left ht, ite_eq_left ⟨hkw, hw⟩, ite_eq_left hop]
          by_cases htA : (S (a w)).card ≤ 1
          · rw [ite_eq_left htA]
            exact ih _ hia (hia.trans hw) htA u v hh.1
          · rw [ite_eq_right htA]
            exact ih _ hib (hib.trans hw) ((handS w hkw hw hop).resolve_left htA) u v hh.2
      · rw [feq w, ite_eq_left ht, ite_eq_right (fun h => hkw h.1)]
        exact Or.inl (hinput w u v (by omega) hwuv)
  have hstep (w : ℕ) (hw : 1 < (f w).card) :
      (∃ j < w, f w ⊆ f j) ∨ (w ∈ B ∧ ∃ i < w, ∃ j < w, f w ⊆ f i ∪ f j) := by
    have ht : (S w).card ≤ 1 := by
      by_contra ht
      rw [feq w, ite_eq_right ht] at hw
      simp at hw
    have hg : k ≤ w ∧ w < N := by
      by_contra h
      rw [feq w, ite_eq_left ht, ite_eq_right h] at hw
      omega
    have hia := ha w hg.1 hg.2
    have hib := hb w hg.1 hg.2
    cases hop : A w with
    | false =>
      by_cases hi : w ∈ I
      · left
        by_cases hz : S (a w) = ∅
        · refine ⟨b w, hib, ?_⟩
          rw [feq w, ite_eq_left ht, ite_eq_left hg, ite_eq_right (by simp [hop]), ite_eq_left hi, ite_eq_left hz]
        · refine ⟨a w, hia, ?_⟩
          rw [feq w, ite_eq_left ht, ite_eq_left hg, ite_eq_right (by simp [hop]), ite_eq_left hi, ite_eq_right hz]
      · right
        refine ⟨Finset.mem_sdiff.mpr ⟨?_, hi⟩, a w, hia, b w, hib, ?_⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hg.2, hg.1, hop, ht⟩
        · rw [feq w, ite_eq_left ht, ite_eq_left hg, ite_eq_right (by simp [hop]), ite_eq_right hi]
    | true =>
      left
      by_cases htA : (S (a w)).card ≤ 1
      · refine ⟨a w, hia, ?_⟩
        rw [feq w, ite_eq_left ht, ite_eq_left hg, ite_eq_left hop, ite_eq_left htA]
      · refine ⟨b w, hib, ?_⟩
        rw [feq w, ite_eq_left ht, ite_eq_left hg, ite_eq_left hop, ite_eq_right htA]
  refine ⟨T, ?_, ?_⟩
  · intro j hj u v hh
    have hs := boundary_spec k N S a b A (fun w hk hN => ⟨ha w hk hN, hb w hk hN⟩) j hj
    rcases hit j hs.1 (by simp [hs.2]) u v hh with (hu | hv) | h
    · exact Or.inl (rootsub j hj hu)
    · exact Or.inr (rootsub j hj hv)
    · exact h
  · have hbnd := dag_union_bound f R B hstep
    have hr := boundary_card k N S a b A
    have hcard : I.card + B.card = (I ∪ small).card := by
      dsimp [B]
      have hdis : Disjoint I (small \ I) := by
        apply Finset.disjoint_left.mpr
        intro w hi hw
        exact (Finset.mem_sdiff.mp hw).2 hi
      rw [← Finset.card_union_of_disjoint hdis]
      congr 1
      ext w
      by_cases hi : w ∈ I <;> simp [hi]
    change T.card ≤ (I ∪ small).card
    change R.card ≤ I.card at hr
    change T.card ≤ R.card + B.card at hbnd
    omega

end PEqualNP.Outside.L_meta_2732_aux.Frontier

namespace PEqualNP.Outside.L_meta_2732_aux.Frontier

lemma positive_shared_cover (n k N : ℕ) (S : ℕ → Finset (Fin n))
    (H : ℕ → Fin n → Fin n → Prop) (a b : ℕ → ℕ) (A : ℕ → Bool)
    (hinput : ∀ w u v, w < k → H w u v → u ∈ S w ∨ v ∈ S w)
    (hparents : ∀ w, k ≤ w → w < N → a w < w ∧ b w < w)
    (hzero : ∀ w, k ≤ w → w < N → A w = true → S w = ∅)
    (horS : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (horH : ∀ w u v, k ≤ w → w < N → A w = false → H w u v → H (a w) u v ∨ H (b w) u v)
    (handS : ∀ w, k ≤ w → w < N → A w = true → (S (a w)).card ≤ 1 ∨ (S (b w)).card ≤ 1)
    (handH : ∀ w u v, k ≤ w → w < N → A w = true → H w u v → H (a w) u v ∧ H (b w) u v) :
    ∃ T : Finset (Fin n),
      (∀ r < N, S r ≠ ∅ → ∀ u v, H r u v → u ∉ S r → v ∉ S r → u ∈ T ∨ v ∈ T) ∧
      T.card ≤ ((insertion k N S a b A) ∪ ((Finset.range N).filter fun w =>
        k ≤ w ∧ A w = false ∧ (S w).card ≤ 1)).card := by
  obtain ⟨T, hT, hcard⟩ := shared_boundary_cover n k N S H a b A hinput
    (fun w hk hN => (hparents w hk hN).1) (fun w hk hN => (hparents w hk hN).2)
    horS horH handS handH
  refine ⟨T, ?_, hcard⟩
  intro r hr hs u v hh hu hv
  obtain ⟨j, hj, hhit⟩ := pair_hit_boundary n k N S H a b A hinput hparents hzero horS horH
    r hr hs u v hh hu hv
  exact hT j hj u v hhit

lemma reserved_not_growth {n : ℕ} (k N : ℕ) (S : ℕ → Finset (Fin n)) (a b : ℕ → ℕ) (A : ℕ → Bool)
    (hunion : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (w : ℕ) (hw : w ∈ (insertion k N S a b A) ∪ ((Finset.range N).filter fun w =>
      k ≤ w ∧ A w = false ∧ (S w).card ≤ 1)) :
    S w = S (a w) ∨ S w = S (b w) ∨ (S w).card ≤ 1 := by
  rcases Finset.mem_union.mp hw with hi | hs
  · rcases insertion_no_growth k N S a b A hunion w hi with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Finset.mem_filter.mp hs).2.2.2)

end PEqualNP.Outside.L_meta_2732_aux.Frontier
