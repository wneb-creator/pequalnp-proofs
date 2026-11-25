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
