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

namespace PEqualNP.Outside.L_meta_2732_aux.SelectedDirtyPaths

theorem path_flag_transition (P : ℕ → Prop) :
    ∀ m, ¬ P 0 → P m → ∃ i < m, ¬ P i ∧ P (i + 1) := by
  classical
  intro m
  induction m with
  | zero =>
    intro hzero hlast
    exact (hzero hlast).elim
  | succ m ih =>
    intro hzero hlast
    by_cases hm : P m
    · obtain ⟨i, him, hni, hnext⟩ := ih hzero hm
      exact ⟨i, by omega, hni, hnext⟩
    · exact ⟨m, by omega, hm, hlast⟩

end PEqualNP.Outside.L_meta_2732_aux.SelectedDirtyPaths

namespace PEqualNP.Outside.L_meta_2732_aux.SelectedGraph

lemma root_cover_from_raw_filters {n : ℕ} (k N d : ℕ) (S : ℕ → Finset (Fin n))
    (a b : ℕ → ℕ) (A D : ℕ → Bool) (H : ℕ → Fin n → Fin n → Prop)
    (F : ℕ → Finset (Fin n)) (V R : Finset ℕ) (T Z : Finset (Fin n))
    (hparents : ∀ w, k ≤ w → w < N → a w < w ∧ b w < w)
    (hinput : ∀ w u v, w < k → H w u v → u ∈ S w ∨ v ∈ S w)
    (handH : ∀ w u v, k ≤ w → w < N → w ≠ d → A w = true → H w u v → H (a w) u v ∧ H (b w) u v)
    (horH : ∀ w u v, k ≤ w → w < N → A w = false → H w u v → H (a w) u v ∨ H (b w) u v)
    (horS : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (horD : ∀ w, k ≤ w → w < N → A w = false → D w = (D (a w) || D (b w)))
    (hzero : ∀ w, k ≤ w → w < N → A w = true → D w = false → S w = ∅)
    (hclean : ∀ w, k ≤ w → w < N → w ≠ d → A w = true → D (a w) = false ∨ D (b w) = false)
    (hbase : ∀ w < k, S w ⊆ F w)
    (hlabel : ∀ w q, q ∈ children k N d S a b A D w → F q ⊆ F w)
    (hroot : ∀ r ∈ R, r < N ∧ F r ⊆ T ∧ D r = false)
    (hboundary : CleanFrontier.boundary k N S a b A D ⊆ R)
    (hRV : R ⊆ V)
    (hVC : ∀ w ∈ V, ∀ q ∈ children k N d S a b A D w, q ∈ V)
    (hdk : k ≤ d) (hdN : d < N) (hDd : D d = true)
    (hda : D (a d) = false) (hdb : D (b d) = false)
    (hsa : S (a d) ≠ ∅) (hsb : S (b d) ≠ ∅)
    (hdirtyH : ∀ u v, H d u v → H (a d) u v ∧ H (b d) u v)
    (hZ : Z ⊆ F d)
    (hraw : ∀ w ∈ V, k ≤ w → w < N → w ≠ d → A w = true → D w = false →
      D (SelectedParent.chosen S a b D w) = true → ∀ u v,
      (u ∈ S (a d) ∨ v ∈ S (a d)) → (u ∈ S (b d) ∨ v ∈ S (b d)) →
      (u ∈ S (SelectedParent.opposite S a b D w) ∨ v ∈ S (SelectedParent.opposite S a b D w)) →
      u ∈ Z ∨ v ∈ Z) :
    ∀ r ∈ R, ∀ u v, H r u v → u ∈ T ∨ v ∈ T := by
  intro r0 hr0 u v hh0
  by_contra hmiss
  have hu : u ∉ T := fun h => hmiss (Or.inl h)
  have hv : v ∉ T := fun h => hmiss (Or.inr h)
  obtain ⟨r, hr, hmin, m, f, hf0, hfm, hf, hfstep⟩ := accepting_path_from_minimal_root
    k N d S a b A D H F R T hparents hinput handH horH hbase hlabel
      (fun w hw => ⟨(hroot w hw).1, (hroot w hw).2.1⟩) hboundary u v ⟨r0, hr0, hh0⟩ hu hv
  have hfLive : ∀ i, i ≤ m → f i ∈ V := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [hf0]
      exact hRV hr
    | succ i ih =>
      intro him
      exact hVC (f i) (ih (by omega)) (f (i + 1)) (hfstep i (by omega))
  have meets (w : ℕ) (hw : w < N) (hwr : w ≤ r) (hs : S w ≠ ∅)
      (hD : D w = false) (hh : H w u v) : u ∈ S w ∨ v ∈ S w := by
    by_contra hn
    have hnu : u ∉ S w := fun h => hn (Or.inl h)
    have hnv : v ∉ S w := fun h => hn (Or.inr h)
    obtain ⟨j, hj, hjw, hjH⟩ := CleanFrontier.pair_hit_boundary n k N S H a b A D
      hinput hparents hzero horS horH horD w hw hs hD u v hh hnu hnv
    exact hmin j (hboundary hj) (hjw.trans_le hwr) hjH
  have hdr : d ≤ r := by simpa only [hfm] using (hf m le_rfl).1
  have hdH : H d u v := by simpa only [hfm] using (hf m le_rfl).2.2.1
  have hdmiss : u ∉ F d ∧ v ∉ F d := by simpa only [hfm] using (hf m le_rfl).2.2.2
  have hdp := hparents d hdk hdN
  have hdh := hdirtyH u v hdH
  have hA := meets (a d) (by omega) (by omega) hsa hda hdh.1
  have hB := meets (b d) (by omega) (by omega) hsb hdb hdh.2
  have hfD0 : ¬ D (f 0) = true := by
    rw [hf0, (hroot r hr).2.2]
    decide
  have hfDm : D (f m) = true := by simpa only [hfm] using hDd
  obtain ⟨i, him, hnot, hyes⟩ := SelectedDirtyPaths.path_flag_transition
    (fun i => D (f i) = true) m hfD0 hfDm
  have hiD : D (f i) = false := by
    cases he : D (f i) with
    | false => rfl
    | true => exact (hnot he).elim
  have hqi := hfstep i him
  obtain ⟨hwi, _⟩ := child_spec k N d S a b A D (f i) (f (i + 1)) hqi
  obtain ⟨hAnd, hchosen⟩ := clean_to_dirty_is_and k N d S a b A D horD
    (f i) (f (i + 1)) hqi hiD hyes
  have hchosenD : D (SelectedParent.chosen S a b D (f i)) = true := by rw [← hchosen]; exact hyes
  have hopp := SelectedParent.chosen_dirty_opposite_large S a b D (f i)
    (hclean (f i) hwi.1 hwi.2.1 hwi.2.2 hAnd) hchosenD
  have hconsH := (hf i (by omega)).2.2.1
  have hboth := handH (f i) u v hwi.1 hwi.2.1 hwi.2.2 hAnd hconsH
  have hcp := hparents (f i) hwi.1 hwi.2.1
  have hoppH : H (SelectedParent.opposite S a b D (f i)) u v := by
    by_cases hleft : SelectedParent.useLeft S a b D (f i)
    · simpa only [SelectedParent.opposite, ite_eq_left hleft] using hboth.2
    · simpa only [SelectedParent.opposite, ite_eq_right hleft] using hboth.1
  have hopplt : SelectedParent.opposite S a b D (f i) < f i := by
    by_cases hleft : SelectedParent.useLeft S a b D (f i)
    · simpa only [SelectedParent.opposite, ite_eq_left hleft] using hcp.2
    · simpa only [SelectedParent.opposite, ite_eq_right hleft] using hcp.1
  have hoppne : S (SelectedParent.opposite S a b D (f i)) ≠ ∅ := by
    intro he
    have hc := hopp.2
    simp only [he, Finset.card_empty] at hc
    omega
  have hfi := hf i (by omega)
  have hS := meets (SelectedParent.opposite S a b D (f i)) (by omega) (by omega)
    hoppne hopp.1 hoppH
  rcases hraw (f i) (hfLive i (by omega)) hwi.1 hwi.2.1 hwi.2.2 hAnd hiD hchosenD u v hA hB hS with h | h
  · exact hdmiss.1 (hZ h)
  · exact hdmiss.2 (hZ h)

end PEqualNP.Outside.L_meta_2732_aux.SelectedGraph


namespace PEqualNP.Outside.L_meta_2732_aux.SelectedLabels

noncomputable def labels {α : Type*} [DecidableEq α] (k d : ℕ)
    (S : ℕ → Finset α) (Z : Finset α) (C : ℕ → Finset ℕ)
    (earlier : ∀ w q, q ∈ C w → q < w) (w : ℕ) : Finset α :=
  if w = d then Z else if w < k then S w else
    (C w).attach.biUnion fun q => labels k d S Z C earlier q.1
termination_by w
decreasing_by exact earlier _ _ q.2

lemma labels_dirty {α : Type*} [DecidableEq α] (k d : ℕ)
    (S : ℕ → Finset α) (Z : Finset α) (C : ℕ → Finset ℕ)
    (earlier : ∀ w q, q ∈ C w → q < w) :
    labels k d S Z C earlier d = Z := by
  rw [labels, ite_eq_left rfl]

lemma labels_base {α : Type*} [DecidableEq α] (k d : ℕ)
    (S : ℕ → Finset α) (Z : Finset α) (C : ℕ → Finset ℕ)
    (earlier : ∀ w q, q ∈ C w → q < w) (hdk : k ≤ d)
    (w : ℕ) (hw : w < k) : labels k d S Z C earlier w = S w := by
  have hwd : w ≠ d := by omega
  rw [labels, ite_eq_right hwd, ite_eq_left hw]

lemma child_label_subset {α : Type*} [DecidableEq α] (k d : ℕ)
    (S : ℕ → Finset α) (Z : Finset α) (C : ℕ → Finset ℕ)
    (earlier : ∀ w q, q ∈ C w → q < w)
    (base_empty : ∀ w < k, C w = ∅) (dirty_empty : C d = ∅)
    (w q : ℕ) (hq : q ∈ C w) :
    labels k d S Z C earlier q ⊆ labels k d S Z C earlier w := by
  have hwd : w ≠ d := by intro h; subst w; simp [dirty_empty] at hq
  have hwk : ¬ w < k := by intro h; simp [base_empty w h] at hq
  have heq : labels k d S Z C earlier w =
      (C w).attach.biUnion fun p => labels k d S Z C earlier p.1 := by
    rw [labels, ite_eq_right hwd, ite_eq_right hwk]
  rw [heq]
  intro x hx
  exact Finset.mem_biUnion.mpr ⟨⟨q, hq⟩, Finset.mem_attach _ _, hx⟩

lemma labels_internal_subset {α : Type*} [DecidableEq α] (k d : ℕ)
    (S : ℕ → Finset α) (Z : Finset α) (C : ℕ → Finset ℕ)
    (earlier : ∀ w q, q ∈ C w → q < w)
    (base_empty : ∀ w < k, C w = ∅) (dirty_empty : C d = ∅)
    (w : ℕ) (hw : C w ≠ ∅) :
    labels k d S Z C earlier w ⊆ (C w).biUnion (labels k d S Z C earlier) := by
  have hwd : w ≠ d := by intro h; subst w; exact hw dirty_empty
  have hwk : ¬ w < k := by intro h; exact hw (base_empty w h)
  have heq : labels k d S Z C earlier w =
      (C w).attach.biUnion fun p => labels k d S Z C earlier p.1 := by
    rw [labels, ite_eq_right hwd, ite_eq_right hwk]
  rw [heq]
  intro x hx
  obtain ⟨p, _, hxp⟩ := Finset.mem_biUnion.mp hx
  exact Finset.mem_biUnion.mpr ⟨p.1, p.2, hxp⟩

lemma labels_leaf_small {α : Type*} [DecidableEq α] (k d : ℕ)
    (S : ℕ → Finset α) (Z : Finset α) (C : ℕ → Finset ℕ)
    (earlier : ∀ w q, q ∈ C w → q < w)
    (small : ∀ w < k, (S w).card ≤ 1)
    (w : ℕ) (hw : C w = ∅) (hwd : w ≠ d) :
    (labels k d S Z C earlier w).card ≤ 1 := by
  by_cases hwk : w < k
  · rw [labels, ite_eq_right hwd, ite_eq_left hwk]
    exact small w hwk
  · rw [labels, ite_eq_right hwd, ite_eq_right hwk]
    have hempty : ((C w).attach.biUnion fun q => labels k d S Z C earlier q.1) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro x hx
      obtain ⟨q, _, _⟩ := Finset.mem_biUnion.mp hx
      obtain ⟨q, hq⟩ := q
      exact Finset.notMem_empty q (hw ▸ hq)
    rw [hempty, Finset.card_empty]
    omega

end PEqualNP.Outside.L_meta_2732_aux.SelectedLabels


namespace PEqualNP.Outside.L_meta_2732_aux.LiveDagCredit

theorem extra_arc_leaf_budget (V R L B : Finset ℕ) (C : ℕ → Finset ℕ)
    (hR : R ⊆ V) (hL : L ⊆ V)
    (hleaf : ∀ p ∈ L, C p = ∅)
    (hbranch : ∀ p ∈ V, p ∉ L → (C p).card ≤ 1 + (if p ∈ B then 1 else 0))
    (hlive : ∀ v ∈ V, v ∉ R → ∃ p ∈ V, v ∈ C p)
    (hextra : (∃ r ∈ R, ∃ p ∈ V, r ∈ C p) ∨
      (∃ p ∈ V, ∃ q ∈ V, ∃ v, p ≠ q ∧ v ∈ C p ∧ v ∈ C q)) :
    L.card + 1 ≤ R.card + B.card := by
  classical
  let E : Finset (ℕ × ℕ) := V.biUnion fun p => (C p).image fun v => (p,v)
  let D := E.image Prod.snd
  have memE (p v : ℕ) (hp : p ∈ V) (hv : v ∈ C p) : (p,v) ∈ E :=
    Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩
  have memD (p v : ℕ) (hp : p ∈ V) (hv : v ∈ C p) : v ∈ D :=
    Finset.mem_image.mpr ⟨(p,v), memE p v hp hv, rfl⟩
  have hsub : V \ R ⊆ D := by
    intro v hv
    obtain ⟨hvV, hvR⟩ := Finset.mem_sdiff.mp hv
    obtain ⟨p, hp, hvp⟩ := hlive v hvV hvR
    exact memD p v hp hvp
  have hlower : (V \ R).card + 1 ≤ E.card := by
    rcases hextra with ⟨r, hr, p, hp, hrp⟩ | ⟨p, hp, q, hq, v, hpq, hvp, hvq⟩
    · have hsub' : insert r (V \ R) ⊆ D :=
        Finset.insert_subset_iff.mpr ⟨memD p r hp hrp, hsub⟩
      have hnot : r ∉ V \ R := by simp [hr]
      have hcard := Finset.card_le_card hsub'
      have himage : D.card ≤ E.card := Finset.card_image_le
      rw [Finset.card_insert_of_notMem hnot] at hcard
      omega
    · have hlt : D.card < E.card := by
        have hle : D.card ≤ E.card := Finset.card_image_le
        have hne : D.card ≠ E.card := by
          intro heq
          have hinj : Set.InjOn (fun z : ℕ × ℕ => z.2) (E : Set (ℕ × ℕ)) :=
            Finset.card_image_iff.mp heq
          have he := hinj (memE p v hp hvp) (memE q v hq hvq) rfl
          exact hpq (congrArg Prod.fst he)
        omega
      have hcard := Finset.card_le_card hsub
      omega
  have harcs : E.card ≤ ∑ p ∈ V, (C p).card := by
    calc
      E.card ≤ ∑ p ∈ V, ((C p).image fun v => (p,v)).card := Finset.card_biUnion_le
      _ ≤ _ := Finset.sum_le_sum fun _ _ => Finset.card_image_le
  have hdegree : ∀ p ∈ V, (C p).card + (if p ∈ L then 1 else 0) ≤
      1 + (if p ∈ B then 1 else 0) := by
    intro p hp
    by_cases hl : p ∈ L
    · simp [hl, hleaf p hl]
    · simpa only [hl, ite_false, Nat.add_zero] using hbranch p hp hl
  have hfL : V.filter (fun p => p ∈ L) = L := by
    ext p
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hL h, h⟩⟩
  have hsL : (∑ p ∈ V, if p ∈ L then 1 else 0) = L.card := by
    rw [← Finset.card_filter, hfL]
  have hsB : (∑ p ∈ V, if p ∈ B then 1 else 0) ≤ B.card := by
    rw [← Finset.card_filter]
    exact Finset.card_le_card fun _ h => (Finset.mem_filter.mp h).2
  have hsum := Finset.sum_le_sum hdegree
  simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one] at hsum
  rw [hsL] at hsum
  have hVR := Finset.card_sdiff_add_card_eq_card hR
  omega

theorem labels_covered_by_leaves {α : Type*} [DecidableEq α]
    (V L : Finset ℕ) (C : ℕ → Finset ℕ) (f : ℕ → Finset α)
    (hchild : ∀ p ∈ V, ∀ q ∈ C p, q ∈ V ∧ q < p)
    (hstep : ∀ p ∈ V, p ∉ L → f p ⊆ (C p).biUnion f) :
    ∀ p ∈ V, f p ⊆ L.biUnion f := by
  intro p
  induction p using Nat.strong_induction_on with
  | ind p ih =>
    intro hp a ha
    by_cases hl : p ∈ L
    · exact Finset.mem_biUnion.mpr ⟨p, hl, ha⟩
    · obtain ⟨q, hq, haq⟩ := Finset.mem_biUnion.mp (hstep p hp hl ha)
      obtain ⟨hqV, hqp⟩ := hchild p hp q hq
      exact ih q hqp hqV haq

theorem extra_arc_double_leaf_bound {α : Type*} [DecidableEq α]
    (V R L B : Finset ℕ) (C : ℕ → Finset ℕ) (f : ℕ → Finset α) (d : ℕ)
    (hR : R ⊆ V) (hL : L ⊆ V)
    (hleaf : ∀ p ∈ L, C p = ∅)
    (hbranch : ∀ p ∈ V, p ∉ L → (C p).card ≤ 1 + (if p ∈ B then 1 else 0))
    (hlive : ∀ v ∈ V, v ∉ R → ∃ p ∈ V, v ∈ C p)
    (hextra : (∃ r ∈ R, ∃ p ∈ V, r ∈ C p) ∨
      (∃ p ∈ V, ∃ q ∈ V, ∃ v, p ≠ q ∧ v ∈ C p ∧ v ∈ C q))
    (hchild : ∀ p ∈ V, ∀ q ∈ C p, q ∈ V ∧ q < p)
    (hstep : ∀ p ∈ V, p ∉ L → f p ⊆ (C p).biUnion f)
    (hsmall : ∀ p ∈ L, p ≠ d → (f p).card ≤ 1)
    (hdouble : (f d).card ≤ 2) :
    (R.biUnion f).card ≤ R.card + B.card := by
  classical
  have hcover := labels_covered_by_leaves V L C f hchild hstep
  have hsub : R.biUnion f ⊆ L.biUnion f := by
    intro a ha
    obtain ⟨p, hp, hap⟩ := Finset.mem_biUnion.mp ha
    exact hcover p (hR hp) hap
  have hsize : ∀ p ∈ L, (f p).card ≤ 1 + (if p = d then 1 else 0) := by
    intro p hp
    by_cases hd : p = d
    · simpa [hd] using hdouble
    · simpa [hd] using hsmall p hp hd
  have hsum := Finset.sum_le_sum hsize
  simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one] at hsum
  have hfilter : L.filter (fun p => p = d) ⊆ {d} := by
    intro p hp
    exact Finset.mem_singleton.mpr (Finset.mem_filter.mp hp).2
  have hbonus : (∑ p ∈ L, if p = d then 1 else 0) ≤ 1 := by
    rw [← Finset.card_filter]
    simpa using Finset.card_le_card hfilter
  have hleaves : (L.biUnion f).card ≤ L.card + 1 :=
    Finset.card_biUnion_le.trans (by omega)
  have hcredit := extra_arc_leaf_budget V R L B C hR hL hleaf hbranch hlive hextra
  exact (Finset.card_le_card hsub).trans (hleaves.trans hcredit)

end PEqualNP.Outside.L_meta_2732_aux.LiveDagCredit

namespace PEqualNP.Outside.L_meta_2732_aux.SelectedGraph

lemma fork_cover_bound {n : ℕ} (k N d : ℕ) (S : ℕ → Finset (Fin n))
    (a b : ℕ → ℕ) (A D : ℕ → Bool) (H : ℕ → Fin n → Fin n → Prop)
    (V R B : Finset ℕ) (Z : Finset (Fin n))
    (hparents : ∀ w, k ≤ w → w < N → a w < w ∧ b w < w)
    (hinput : ∀ w u v, w < k → H w u v → u ∈ S w ∨ v ∈ S w)
    (handH : ∀ w u v, k ≤ w → w < N → w ≠ d → A w = true → H w u v → H (a w) u v ∧ H (b w) u v)
    (horH : ∀ w u v, k ≤ w → w < N → A w = false → H w u v → H (a w) u v ∨ H (b w) u v)
    (horS : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (horD : ∀ w, k ≤ w → w < N → A w = false → D w = (D (a w) || D (b w)))
    (hzero : ∀ w, k ≤ w → w < N → A w = true → D w = false → S w = ∅)
    (hclean : ∀ w, k ≤ w → w < N → w ≠ d → A w = true → D (a w) = false ∨ D (b w) = false)
    (hroot : ∀ r ∈ R, r < N ∧ D r = false)
    (hboundary : CleanFrontier.boundary k N S a b A D ⊆ R)
    (hRV : R ⊆ V)
    (hVC : ∀ w ∈ V, ∀ q ∈ children k N d S a b A D w, q ∈ V)
    (hsmall : ∀ w < k, (S w).card ≤ 1)
    (hbranch : ∀ w ∈ V, children k N d S a b A D w ≠ ∅ →
      (children k N d S a b A D w).card ≤ 1 + (if w ∈ B then 1 else 0))
    (hlive : ∀ w ∈ V, w ∉ R → ∃ p ∈ V, w ∈ children k N d S a b A D p)
    (hextra : (∃ r ∈ R, ∃ p ∈ V, r ∈ children k N d S a b A D p) ∨
      (∃ p ∈ V, ∃ q ∈ V, ∃ v, p ≠ q ∧
        v ∈ children k N d S a b A D p ∧ v ∈ children k N d S a b A D q))
    (hdk : k ≤ d) (hdN : d < N) (hDd : D d = true)
    (hda : D (a d) = false) (hdb : D (b d) = false)
    (hsa : S (a d) ≠ ∅) (hsb : S (b d) ≠ ∅)
    (hdirtyH : ∀ u v, H d u v → H (a d) u v ∧ H (b d) u v)
    (hZ : Z.card ≤ 2)
    (hraw : ∀ w ∈ V, k ≤ w → w < N → w ≠ d → A w = true → D w = false →
      D (SelectedParent.chosen S a b D w) = true → ∀ u v,
      (u ∈ S (a d) ∨ v ∈ S (a d)) → (u ∈ S (b d) ∨ v ∈ S (b d)) →
      (u ∈ S (SelectedParent.opposite S a b D w) ∨ v ∈ S (SelectedParent.opposite S a b D w)) →
      u ∈ Z ∨ v ∈ Z) :
    ∃ T : Finset (Fin n), T.card ≤ R.card + B.card ∧
      ∀ r ∈ R, ∀ u v, H r u v → u ∈ T ∨ v ∈ T := by
  classical
  let C := children k N d S a b A D
  let earlier : ∀ w q, q ∈ C w → q < w := child_earlier k N d S a b A D hparents
  let F := SelectedLabels.labels k d S Z C earlier
  let L := V.filter fun w => C w = ∅
  let T := R.biUnion F
  have base_empty : ∀ w < k, C w = ∅ := by
    intro w hw
    have hn : ¬ (k ≤ w ∧ w < N ∧ w ≠ d) := by omega
    simp only [C, children, ite_eq_right hn]
  have dirty_empty : C d = ∅ := by simp [C, children]
  have hcard : T.card ≤ R.card + B.card := by
    apply LiveDagCredit.extra_arc_double_leaf_bound V R L B C F d hRV
    · exact Finset.filter_subset _ _
    · intro p hp
      exact (Finset.mem_filter.mp hp).2
    · intro p hp hn
      have he : C p ≠ ∅ := fun he => hn (Finset.mem_filter.mpr ⟨hp, he⟩)
      exact hbranch p hp he
    · exact hlive
    · exact hextra
    · intro p hp q hq
      exact ⟨hVC p hp q hq, earlier p q hq⟩
    · intro p hp hn
      have he : C p ≠ ∅ := fun he => hn (Finset.mem_filter.mpr ⟨hp, he⟩)
      exact SelectedLabels.labels_internal_subset k d S Z C earlier base_empty dirty_empty p he
    · intro p hp hpd
      exact SelectedLabels.labels_leaf_small k d S Z C earlier hsmall p
        (Finset.mem_filter.mp hp).2 hpd
    · change (SelectedLabels.labels k d S Z C earlier d).card ≤ 2
      rw [SelectedLabels.labels_dirty]
      exact hZ
  refine ⟨T, hcard, ?_⟩
  apply root_cover_from_raw_filters k N d S a b A D H F V R T Z hparents hinput
    handH horH horS horD hzero hclean _ _ _ hboundary hRV hVC
    hdk hdN hDd hda hdb hsa hsb hdirtyH _ hraw
  · intro w hw
    change S w ⊆ SelectedLabels.labels k d S Z C earlier w
    rw [SelectedLabels.labels_base k d S Z C earlier hdk w hw]
  · exact SelectedLabels.child_label_subset k d S Z C earlier base_empty dirty_empty
  · intro r hr
    refine ⟨(hroot r hr).1, ?_, (hroot r hr).2⟩
    intro u hu
    exact Finset.mem_biUnion.mpr ⟨r, hr, hu⟩
  · change Z ⊆ SelectedLabels.labels k d S Z C earlier d
    rw [SelectedLabels.labels_dirty]

end PEqualNP.Outside.L_meta_2732_aux.SelectedGraph
