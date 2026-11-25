import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2732_aux.CleanFrontier

def insertion {n : ℕ} (k N : ℕ) (S : ℕ → Finset (Fin n)) (a b : ℕ → ℕ)
    (A D : ℕ → Bool) : Finset ℕ :=
  (Finset.range N).filter fun w => k ≤ w ∧ A w = false ∧ S w ≠ ∅ ∧
    ((S (a w) = ∅ ∧ D (a w) = false) ∨ (S (b w) = ∅ ∧ D (b w) = false))

def emptyChild {n : ℕ} (S : ℕ → Finset (Fin n)) (a b : ℕ → ℕ) (D : ℕ → Bool) (w : ℕ) : ℕ :=
  if S (a w) = ∅ ∧ D (a w) = false then a w else b w

def boundary {n : ℕ} (k N : ℕ) (S : ℕ → Finset (Fin n)) (a b : ℕ → ℕ)
    (A D : ℕ → Bool) : Finset ℕ :=
  (insertion k N S a b A D).image (emptyChild S a b D)

lemma boundary_card {n : ℕ} (k N : ℕ) (S : ℕ → Finset (Fin n)) (a b : ℕ → ℕ) (A D : ℕ → Bool) :
    (boundary k N S a b A D).card ≤ (insertion k N S a b A D).card := Finset.card_image_le

lemma boundary_spec {n : ℕ} (k N : ℕ) (S : ℕ → Finset (Fin n)) (a b : ℕ → ℕ) (A D : ℕ → Bool)
    (hparents : ∀ w, k ≤ w → w < N → a w < w ∧ b w < w)
    (j : ℕ) (hj : j ∈ boundary k N S a b A D) : j < N ∧ S j = ∅ ∧ D j = false := by
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hj
  obtain ⟨hwN, hwk, _, _, he⟩ : w < N ∧ k ≤ w ∧ A w = false ∧ S w ≠ ∅ ∧
      ((S (a w) = ∅ ∧ D (a w) = false) ∨ (S (b w) = ∅ ∧ D (b w) = false)) :=
    by simpa [insertion] using hw
  have hp := hparents w hwk hwN
  by_cases ha : S (a w) = ∅ ∧ D (a w) = false
  · simp only [emptyChild, ite_eq_left ha]
    exact ⟨by omega, ha⟩
  · simp only [emptyChild, ite_eq_right ha]
    exact ⟨by omega, he.resolve_left ha⟩

lemma insertion_no_growth {n : ℕ} (k N : ℕ) (S : ℕ → Finset (Fin n)) (a b : ℕ → ℕ) (A D : ℕ → Bool)
    (hunion : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (w : ℕ) (hw : w ∈ insertion k N S a b A D) : S w = S (a w) ∨ S w = S (b w) := by
  obtain ⟨hwN, hwk, hwA, _, he⟩ : w < N ∧ k ≤ w ∧ A w = false ∧ S w ≠ ∅ ∧
      ((S (a w) = ∅ ∧ D (a w) = false) ∨ (S (b w) = ∅ ∧ D (b w) = false)) :=
    by simpa [insertion] using hw
  have hu := hunion w hwk hwN hwA
  rcases he with ha | hb
  · exact Or.inr (by simpa only [ha.1, Finset.empty_union] using hu)
  · exact Or.inl (by simpa only [hb.1, Finset.union_empty] using hu)

lemma pair_hit_boundary (n k N : ℕ) (S : ℕ → Finset (Fin n))
    (H : ℕ → Fin n → Fin n → Prop) (a b : ℕ → ℕ) (A D : ℕ → Bool)
    (hinput : ∀ w u v, w < k → H w u v → u ∈ S w ∨ v ∈ S w)
    (hparents : ∀ w, k ≤ w → w < N → a w < w ∧ b w < w)
    (hzero : ∀ w, k ≤ w → w < N → A w = true → D w = false → S w = ∅)
    (hunion : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (horH : ∀ w u v, k ≤ w → w < N → A w = false → H w u v → H (a w) u v ∨ H (b w) u v)
    (horD : ∀ w, k ≤ w → w < N → A w = false → D w = (D (a w) || D (b w)))
    (r : ℕ) (hr : r < N) (hne : S r ≠ ∅) (hdr : D r = false) (u v : Fin n)
    (hpair : H r u v) (hu : u ∉ S r) (hv : v ∉ S r) :
    ∃ j ∈ boundary k N S a b A D, j < r ∧ H j u v := by
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    by_cases hk : k ≤ r
    · have hp := hparents r hk hr
      have hop : A r = false := by
        cases he : A r with
        | false => rfl
        | true => exact (hne (hzero r hk hr he hdr)).elim
      have hd : D (a r) = false ∧ D (b r) = false := by
        have hh : (D (a r) || D (b r)) = false := (horD r hk hr hop).symm.trans hdr
        cases hA : D (a r) <;> cases hB : D (b r) <;> simp [hA, hB] at hh ⊢
      have hs := hunion r hk hr hop
      have hnuA : u ∉ S (a r) := fun h => hu (hs ▸ Finset.mem_union_left _ h)
      have hnvA : v ∉ S (a r) := fun h => hv (hs ▸ Finset.mem_union_left _ h)
      have hnuB : u ∉ S (b r) := fun h => hu (hs ▸ Finset.mem_union_right _ h)
      have hnvB : v ∉ S (b r) := fun h => hv (hs ▸ Finset.mem_union_right _ h)
      rcases horH r u v hk hr hop hpair with hA | hB
      · by_cases hz : S (a r) = ∅
        · have hi : r ∈ insertion k N S a b A D := by simp [insertion, hr, hk, hop, hne, hz, hd.1]
          have hc : S (a r) = ∅ ∧ D (a r) = false := ⟨hz, hd.1⟩
          refine ⟨emptyChild S a b D r, Finset.mem_image_of_mem _ hi, ?_⟩
          simpa only [emptyChild, ite_eq_left hc] using And.intro hp.1 hA
        · obtain ⟨j, hj, hjr, hhit⟩ := ih (a r) hp.1 (by omega) hz hd.1 hA hnuA hnvA
          exact ⟨j, hj, hjr.trans hp.1, hhit⟩
      · by_cases hz : S (b r) = ∅
        · have ha : ¬ (S (a r) = ∅ ∧ D (a r) = false) := by
            intro he
            exact hne (by simpa only [he.1, hz, Finset.empty_union] using hs)
          have hi : r ∈ insertion k N S a b A D := by simp [insertion, hr, hk, hop, hne, hz, hd.2]
          refine ⟨emptyChild S a b D r, Finset.mem_image_of_mem _ hi, ?_⟩
          simpa only [emptyChild, ite_eq_right ha] using And.intro hp.2 hB
        · obtain ⟨j, hj, hjr, hhit⟩ := ih (b r) hp.2 (by omega) hz hd.2 hB hnuB hnvB
          exact ⟨j, hj, hjr.trans hp.2, hhit⟩
    · rcases hinput r u v (by omega) hpair with h | h
      · exact (hu h).elim
      · exact (hv h).elim

end PEqualNP.Outside.L_meta_2732_aux.CleanFrontier


namespace PEqualNP.Outside.L_meta_2732_aux.SelectedParent

def useLeft {n : ℕ} (S : ℕ → Finset (Fin n)) (a b : ℕ → ℕ) (D : ℕ → Bool) (w : ℕ) : Prop :=
  (S (a w)).card ≤ 1 ∧ (D (a w) = false ∨ 1 < (S (b w)).card)

def chosen {n : ℕ} (S : ℕ → Finset (Fin n)) (a b : ℕ → ℕ) (D : ℕ → Bool) (w : ℕ) : ℕ :=
  @ite ℕ (useLeft S a b D w) (by unfold useLeft; infer_instance) (a w) (b w)

def opposite {n : ℕ} (S : ℕ → Finset (Fin n)) (a b : ℕ → ℕ) (D : ℕ → Bool) (w : ℕ) : ℕ :=
  @ite ℕ (useLeft S a b D w) (by unfold useLeft; infer_instance) (b w) (a w)

lemma chosen_small {n : ℕ} (S : ℕ → Finset (Fin n)) (a b : ℕ → ℕ) (D : ℕ → Bool) (w : ℕ)
    (hsmall : (S (a w)).card ≤ 1 ∨ (S (b w)).card ≤ 1) :
    (S (chosen S a b D w)).card ≤ 1 := by
  by_cases h : useLeft S a b D w
  · rw [chosen, ite_eq_left h]
    exact h.1
  · rw [chosen, ite_eq_right h]
    by_contra hb
    have hb' : 1 < (S (b w)).card := by omega
    have ha : (S (a w)).card ≤ 1 := hsmall.resolve_right hb
    exact h ⟨ha, Or.inr hb'⟩

lemma chosen_earlier {n : ℕ} (S : ℕ → Finset (Fin n)) (a b : ℕ → ℕ) (D : ℕ → Bool) (w : ℕ)
    (ha : a w < w) (hb : b w < w) : chosen S a b D w < w := by
  by_cases h : useLeft S a b D w <;> simp only [chosen, h, ite_true, ite_false] <;> assumption

lemma chosen_dirty_opposite_large {n : ℕ} (S : ℕ → Finset (Fin n)) (a b : ℕ → ℕ)
    (D : ℕ → Bool) (w : ℕ) (hclean : D (a w) = false ∨ D (b w) = false)
    (hdirty : D (chosen S a b D w) = true) :
    D (opposite S a b D w) = false ∧ 1 < (S (opposite S a b D w)).card := by
  by_cases h : useLeft S a b D w
  · rw [chosen, ite_eq_left h] at hdirty
    rw [opposite, ite_eq_left h]
    have ha : D (a w) ≠ false := by rw [hdirty]; decide
    exact ⟨hclean.resolve_left ha, h.2.resolve_left ha⟩
  · rw [chosen, ite_eq_right h] at hdirty
    rw [opposite, ite_eq_right h]
    have hb : D (b w) ≠ false := by rw [hdirty]; decide
    have ha : D (a w) = false := hclean.resolve_right hb
    refine ⟨ha, ?_⟩
    by_contra hn
    have hs : (S (a w)).card ≤ 1 := by omega
    exact h ⟨hs, Or.inl ha⟩

lemma chosen_hit {n : ℕ} (S : ℕ → Finset (Fin n)) (a b : ℕ → ℕ) (D : ℕ → Bool)
    (H : ℕ → Fin n → Fin n → Prop) (w : ℕ) (u v : Fin n)
    (ha : H (a w) u v) (hb : H (b w) u v) : H (chosen S a b D w) u v := by
  by_cases h : useLeft S a b D w <;> simp only [chosen, h, ite_true, ite_false] <;> assumption

end PEqualNP.Outside.L_meta_2732_aux.SelectedParent

namespace PEqualNP.Outside.L_meta_2732_aux.SelectedGraph

def children {n : ℕ} (k N d : ℕ) (S : ℕ → Finset (Fin n)) (a b : ℕ → ℕ)
    (A D : ℕ → Bool) (w : ℕ) : Finset ℕ :=
  if k ≤ w ∧ w < N ∧ w ≠ d then
    if A w = true then {SelectedParent.chosen S a b D w}
    else if w ∈ CleanFrontier.insertion k N S a b A D then
      if S (a w) = ∅ ∧ D (a w) = false then {b w} else {a w}
    else {a w, b w}
  else ∅

lemma child_spec {n : ℕ} (k N d : ℕ) (S : ℕ → Finset (Fin n)) (a b : ℕ → ℕ)
    (A D : ℕ → Bool) (w q : ℕ) (hq : q ∈ children k N d S a b A D w) :
    (k ≤ w ∧ w < N ∧ w ≠ d) ∧ (q = a w ∨ q = b w) := by
  by_cases hv : k ≤ w ∧ w < N ∧ w ≠ d
  · refine ⟨hv, ?_⟩
    by_cases ha : A w = true
    · have he : q = SelectedParent.chosen S a b D w := by simpa [children, hv, ha] using hq
      rw [he]
      by_cases h : SelectedParent.useLeft S a b D w <;> simp [SelectedParent.chosen, h]
    · by_cases hi : w ∈ CleanFrontier.insertion k N S a b A D
      · by_cases hz : S (a w) = ∅ ∧ D (a w) = false
        · have he : q = b w := by simpa [children, hv, ha, hi, hz] using hq
          exact Or.inr he
        · have he : q = a w := by simpa [children, hv, ha, hi, hz] using hq
          exact Or.inl he
      · simpa [children, hv, ha, hi] using hq
  · simp [children, hv] at hq

lemma child_earlier {n : ℕ} (k N d : ℕ) (S : ℕ → Finset (Fin n)) (a b : ℕ → ℕ)
    (A D : ℕ → Bool) (hparents : ∀ w, k ≤ w → w < N → a w < w ∧ b w < w)
    (w q : ℕ) (hq : q ∈ children k N d S a b A D w) : q < w := by
  obtain ⟨hv, hq⟩ := child_spec k N d S a b A D w q hq
  have hp := hparents w hv.1 hv.2.1
  rcases hq with rfl | rfl
  · exact hp.1
  · exact hp.2

lemma dirty_child {n : ℕ} (k N d : ℕ) (S : ℕ → Finset (Fin n)) (a b : ℕ → ℕ)
    (A D : ℕ → Bool)
    (hinput : ∀ w < k, D w = false)
    (hparents : ∀ w, k ≤ w → w < N → a w < w ∧ b w < w)
    (handD : ∀ w, k ≤ w → w < N → w ≠ d → A w = true → D w = false)
    (horD : ∀ w, k ≤ w → w < N → A w = false → D w = (D (a w) || D (b w)))
    (w : ℕ) (hw : w < N) (hd : w ≠ d) (hD : D w = true) :
    ∃ q ∈ children k N d S a b A D w, q < w ∧ D q = true := by
  have hk : k ≤ w := by
    by_contra hn
    have hf := hinput w (by omega)
    rw [hf] at hD
    cases hD
  have ha : A w = false := by
    cases hop : A w with
    | false => rfl
    | true =>
      have hf := handD w hk hw hd hop
      rw [hf] at hD
      cases hD
  have hor : D (a w) = true ∨ D (b w) = true := by
    have hh : (D (a w) || D (b w)) = true := (horD w hk hw ha).symm.trans hD
    simpa only [Bool.or_eq_true] using hh
  have hv : k ≤ w ∧ w < N ∧ w ≠ d := ⟨hk, hw, hd⟩
  have hp := hparents w hk hw
  by_cases hi : w ∈ CleanFrontier.insertion k N S a b A D
  · by_cases hz : S (a w) = ∅ ∧ D (a w) = false
    · have hb : D (b w) = true := hor.resolve_left (by simp [hz.2])
      refine ⟨b w, ?_, hp.2, hb⟩
      simp [children, hv, ha, hi, hz]
    · have hzB : S (b w) = ∅ ∧ D (b w) = false := by
        have hm := (Finset.mem_filter.mp hi).2.2.2.2
        exact hm.resolve_left hz
      have hA : D (a w) = true := hor.resolve_right (by simp [hzB.2])
      refine ⟨a w, ?_, hp.1, hA⟩
      simp [children, hv, ha, hi, hz]
  · rcases hor with hA | hB
    · refine ⟨a w, ?_, hp.1, hA⟩
      simp [children, hv, ha, hi]
    · refine ⟨b w, ?_, hp.2, hB⟩
      simp [children, hv, ha, hi]

lemma clean_to_dirty_is_and {n : ℕ} (k N d : ℕ) (S : ℕ → Finset (Fin n)) (a b : ℕ → ℕ)
    (A D : ℕ → Bool)
    (horD : ∀ w, k ≤ w → w < N → A w = false → D w = (D (a w) || D (b w)))
    (w q : ℕ) (hq : q ∈ children k N d S a b A D w) (hw : D w = false) (hdq : D q = true) :
    A w = true ∧ q = SelectedParent.chosen S a b D w := by
  obtain ⟨hv, hp⟩ := child_spec k N d S a b A D w q hq
  have ha : A w = true := by
    cases hop : A w with
    | true => rfl
    | false =>
      have hh := horD w hv.1 hv.2.1 hop
      rw [hw] at hh
      rcases hp with rfl | rfl <;> simp [hdq] at hh
  refine ⟨ha, ?_⟩
  simpa [children, hv, ha] using hq

lemma child_small {n : ℕ} (k N d : ℕ) (S : ℕ → Finset (Fin n)) (a b : ℕ → ℕ)
    (A D : ℕ → Bool)
    (handS : ∀ w, k ≤ w → w < N → w ≠ d → A w = true →
      (S (a w)).card ≤ 1 ∨ (S (b w)).card ≤ 1)
    (horS : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (w q : ℕ) (hq : q ∈ children k N d S a b A D w) (hs : (S w).card ≤ 1) :
    (S q).card ≤ 1 := by
  obtain ⟨hv, hp⟩ := child_spec k N d S a b A D w q hq
  cases hop : A w with
  | true =>
    have hsel : q = SelectedParent.chosen S a b D w := by simpa [children, hv, hop] using hq
    rw [hsel]
    exact SelectedParent.chosen_small S a b D w (handS w hv.1 hv.2.1 hv.2.2 hop)
  | false =>
    have hu := horS w hv.1 hv.2.1 hop
    apply (Finset.card_le_card _).trans hs
    rw [hu]
    rcases hp with rfl | rfl
    · exact Finset.subset_union_left
    · exact Finset.subset_union_right

lemma hit_step_or_boundary {n : ℕ} (k N d : ℕ) (S : ℕ → Finset (Fin n)) (a b : ℕ → ℕ)
    (A D : ℕ → Bool) (H : ℕ → Fin n → Fin n → Prop)
    (hparents : ∀ w, k ≤ w → w < N → a w < w ∧ b w < w)
    (handH : ∀ w u v, k ≤ w → w < N → w ≠ d → A w = true → H w u v → H (a w) u v ∧ H (b w) u v)
    (horH : ∀ w u v, k ≤ w → w < N → A w = false → H w u v → H (a w) u v ∨ H (b w) u v)
    (w : ℕ) (hk : k ≤ w) (hw : w < N) (hd : w ≠ d) (u v : Fin n) (hhit : H w u v) :
    (∃ q ∈ children k N d S a b A D w, H q u v) ∨
      (∃ q ∈ CleanFrontier.boundary k N S a b A D, q < w ∧ H q u v) := by
  have hv : k ≤ w ∧ w < N ∧ w ≠ d := ⟨hk, hw, hd⟩
  have hp := hparents w hk hw
  cases hop : A w with
  | true =>
    left
    refine ⟨SelectedParent.chosen S a b D w, by simp [children, hv, hop], ?_⟩
    have hh := handH w u v hk hw hd hop hhit
    exact SelectedParent.chosen_hit S a b D H w u v hh.1 hh.2
  | false =>
    rcases horH w u v hk hw hop hhit with hA | hB
    · by_cases hi : w ∈ CleanFrontier.insertion k N S a b A D
      · by_cases hz : S (a w) = ∅ ∧ D (a w) = false
        · right
          refine ⟨a w, ?_, hp.1, hA⟩
          have hm := Finset.mem_image_of_mem (CleanFrontier.emptyChild S a b D) hi
          simpa only [CleanFrontier.boundary, CleanFrontier.emptyChild, ite_eq_left hz] using hm
        · left
          exact ⟨a w, by simp [children, hv, hop, hi, hz], hA⟩
      · left
        exact ⟨a w, by simp [children, hv, hop, hi], hA⟩
    · by_cases hi : w ∈ CleanFrontier.insertion k N S a b A D
      · by_cases hz : S (a w) = ∅ ∧ D (a w) = false
        · left
          exact ⟨b w, by simp [children, hv, hop, hi, hz], hB⟩
        · right
          refine ⟨b w, ?_, hp.2, hB⟩
          have hm := Finset.mem_image_of_mem (CleanFrontier.emptyChild S a b D) hi
          simpa only [CleanFrontier.boundary, CleanFrontier.emptyChild, ite_eq_right hz] using hm
      · left
        exact ⟨b w, by simp [children, hv, hop, hi], hB⟩

end PEqualNP.Outside.L_meta_2732_aux.SelectedGraph

namespace PEqualNP.Outside.L_meta_2732_aux.SelectedDirtyPaths

theorem selected_path_to_dirty (V : Finset ℕ) (C : ℕ → Finset ℕ)
    (D : ℕ → Prop) (d : ℕ)
    (step : ∀ w ∈ V, D w → w ≠ d → ∃ q ∈ V, q < w ∧ q ∈ C w ∧ D q) :
    ∀ w ∈ V, D w → ∃ (m : ℕ) (f : ℕ → ℕ), f 0 = w ∧ f m = d ∧
      (∀ i ≤ m, f i ∈ V ∧ D (f i)) ∧ (∀ i < m, f (i + 1) ∈ C (f i)) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hD
    by_cases hd : w = d
    · subst w
      exact ⟨0, fun _ => d, rfl, rfl, fun _ _ => ⟨hw, hD⟩, by omega⟩
    · obtain ⟨q, hqV, hqw, hqC, hqD⟩ := step w hw hD hd
      obtain ⟨m, f, hf0, hfm, hfV, hfC⟩ := ih q hqw hqV hqD
      let g : ℕ → ℕ := fun i => match i with
        | 0 => w
        | j + 1 => f j
      refine ⟨m + 1, g, rfl, ?_, ?_, ?_⟩
      · simpa only [g] using hfm
      · intro i hi
        cases i with
        | zero => exact ⟨hw, hD⟩
        | succ j => exact hfV j (by omega)
      · intro i hi
        cases i with
        | zero => simpa only [g, hf0] using hqC
        | succ j => exact hfC j (by omega)


end PEqualNP.Outside.L_meta_2732_aux.SelectedDirtyPaths

namespace PEqualNP.Outside.L_meta_2732_aux.SelectedGraph

lemma accepting_path_from_minimal_root {n : ℕ} (k N d : ℕ) (S : ℕ → Finset (Fin n))
    (a b : ℕ → ℕ) (A D : ℕ → Bool) (H : ℕ → Fin n → Fin n → Prop)
    (F : ℕ → Finset (Fin n)) (R : Finset ℕ) (T : Finset (Fin n))
    (hparents : ∀ w, k ≤ w → w < N → a w < w ∧ b w < w)
    (hinput : ∀ w u v, w < k → H w u v → u ∈ S w ∨ v ∈ S w)
    (handH : ∀ w u v, k ≤ w → w < N → w ≠ d → A w = true → H w u v → H (a w) u v ∧ H (b w) u v)
    (horH : ∀ w u v, k ≤ w → w < N → A w = false → H w u v → H (a w) u v ∨ H (b w) u v)
    (hbase : ∀ w < k, S w ⊆ F w)
    (hlabel : ∀ w q, q ∈ children k N d S a b A D w → F q ⊆ F w)
    (hroot : ∀ r ∈ R, r < N ∧ F r ⊆ T)
    (hboundary : CleanFrontier.boundary k N S a b A D ⊆ R)
    (u v : Fin n) (haccept : ∃ r ∈ R, H r u v) (hu : u ∉ T) (hv : v ∉ T) :
    ∃ r ∈ R, (∀ j ∈ R, j < r → ¬ H j u v) ∧
      ∃ (m : ℕ) (f : ℕ → ℕ), f 0 = r ∧ f m = d ∧
      (∀ i ≤ m, f i ≤ r ∧ f i < N ∧ H (f i) u v ∧ u ∉ F (f i) ∧ v ∉ F (f i)) ∧
      (∀ i < m, f (i + 1) ∈ children k N d S a b A D (f i)) := by
  classical
  let r := Nat.find haccept
  have hr : r ∈ R ∧ H r u v := Nat.find_spec haccept
  have hrN := (hroot r hr.1).1
  let P := fun w => w ≤ r ∧ H w u v ∧ u ∉ F w ∧ v ∉ F w
  have step : ∀ w ∈ Finset.range N, P w → w ≠ d →
      ∃ q ∈ Finset.range N, q < w ∧ q ∈ children k N d S a b A D w ∧ P q := by
    intro w hw hP hwd
    have hwN := Finset.mem_range.mp hw
    have hk : k ≤ w := by
      by_contra hn
      have hwk : w < k := by omega
      rcases hinput w u v hwk hP.2.1 with h | h
      · exact hP.2.2.1 (hbase w hwk h)
      · exact hP.2.2.2 (hbase w hwk h)
    rcases hit_step_or_boundary k N d S a b A D H hparents handH horH
      w hk hwN hwd u v hP.2.1 with ⟨q, hq, hhit⟩ | ⟨q, hq, hqw, hhit⟩
    · have hqw := child_earlier k N d S a b A D hparents w q hq
      refine ⟨q, Finset.mem_range.mpr (by omega), hqw, hq, ?_⟩
      exact ⟨by have := hP.1; omega, hhit,
        fun h => hP.2.2.1 (hlabel w q hq h), fun h => hP.2.2.2 (hlabel w q hq h)⟩
    · have hqr : q < r := by have := hP.1; omega
      exact (Nat.find_min haccept hqr ⟨hboundary hq, hhit⟩).elim
  have hPr : P r := ⟨le_rfl, hr.2, fun h => hu ((hroot r hr.1).2 h),
    fun h => hv ((hroot r hr.1).2 h)⟩
  obtain ⟨m, f, hf0, hfm, hfV, hfstep⟩ := SelectedDirtyPaths.selected_path_to_dirty
    (Finset.range N) (children k N d S a b A D) P d step r (Finset.mem_range.mpr hrN) hPr
  refine ⟨r, hr.1, ?_, m, f, hf0, hfm, ?_, hfstep⟩
  · intro j hj hjr hh
    exact Nat.find_min haccept hjr ⟨hj, hh⟩
  · intro i hi
    have h := hfV i hi
    exact ⟨h.2.1, Finset.mem_range.mp h.1, h.2.2⟩

end PEqualNP.Outside.L_meta_2732_aux.SelectedGraph
