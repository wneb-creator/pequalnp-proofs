import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2732_aux.TwoPathFork

theorem fork_of_two_paths (V : Finset ℕ) (C : ℕ → Finset ℕ)
    (f g : ℕ → ℕ) (m n : ℕ)
    (hfV : ∀ i ≤ m, f i ∈ V) (hgV : ∀ j ≤ n, g j ∈ V)
    (hf : ∀ i < m, f (i + 1) ∈ C (f i))
    (hg : ∀ j < n, g (j + 1) ∈ C (g j))
    (hend : f m = g n)
    (hfirst : ∀ j ≤ n, f 0 ≠ g j)
    (hsecond : ∀ i ≤ m, g 0 ≠ f i) :
    ∃ p ∈ V, ∃ q ∈ V, ∃ v, p ≠ q ∧ v ∈ C p ∧ v ∈ C q := by
  classical
  have hex : ∃ i, i ≤ m ∧ ∃ j, j ≤ n ∧ f i = g j :=
    ⟨m, le_rfl, n, le_rfl, hend⟩
  let k := Nat.find hex
  obtain ⟨hkm, j, hjn, hkj⟩ := Nat.find_spec hex
  change k ≤ m at hkm
  change f k = g j at hkj
  have hkpos : 0 < k := by
    by_contra h
    have hk : k = 0 := by omega
    exact hfirst j hjn (hk ▸ hkj)
  have hjpos : 0 < j := by
    by_contra h
    have hj : j = 0 := by omega
    exact hsecond k hkm (hj ▸ hkj.symm)
  have hpred : k - 1 < k := by omega
  have hneq : f (k - 1) ≠ g (j - 1) := by
    intro heq
    exact Nat.find_min hex hpred ⟨by omega, j - 1, by omega, heq⟩
  refine ⟨f (k - 1), hfV _ (by omega), g (j - 1), hgV _ (by omega), f k, hneq, ?_, ?_⟩
  · have h := hf (k - 1) (by omega)
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ k)] using h
  · have h := hg (j - 1) (by omega)
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ j), hkj] using h

end PEqualNP.Outside.L_meta_2732_aux.TwoPathFork

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

theorem clean_consumer_path (V : Finset ℕ) (C : ℕ → Finset ℕ)
    (D : ℕ → Prop) (d : ℕ)
    (step : ∀ w ∈ V, D w → w ≠ d → ∃ q ∈ V, q < w ∧ q ∈ C w ∧ D q)
    (p : ℕ) (hp : p ∈ V) (hchild : ∃ q ∈ V, q ∈ C p ∧ D q) :
    ∃ (m : ℕ) (f : ℕ → ℕ), 0 < m ∧ f 0 = p ∧ f m = d ∧
      (∀ i ≤ m, f i ∈ V) ∧ (∀ i, 0 < i → i ≤ m → D (f i)) ∧
      (∀ i < m, f (i + 1) ∈ C (f i)) := by
  obtain ⟨q, hqV, hqC, hqD⟩ := hchild
  obtain ⟨m, f, hf0, hfm, hfV, hfC⟩ := selected_path_to_dirty V C D d step q hqV hqD
  let g : ℕ → ℕ := fun i => match i with
    | 0 => p
    | j + 1 => f j
  refine ⟨m + 1, g, by omega, rfl, ?_, ?_, ?_, ?_⟩
  · simpa only [g] using hfm
  · intro i hi
    cases i with
    | zero => exact hp
    | succ j => exact (hfV j (by omega)).1
  · intro i hi him
    cases i with
    | zero => omega
    | succ j => exact (hfV j (by omega)).2
  · intro i hi
    cases i with
    | zero => simpa only [g, hf0] using hqC
    | succ j => exact hfC j (by omega)

theorem two_clean_consumers_fork (V : Finset ℕ) (C : ℕ → Finset ℕ)
    (D : ℕ → Prop) (d : ℕ)
    (step : ∀ w ∈ V, D w → w ≠ d → ∃ q ∈ V, q < w ∧ q ∈ C w ∧ D q)
    (p q : ℕ) (hp : p ∈ V) (hq : q ∈ V) (hpq : p ≠ q)
    (hpD : ¬ D p) (hqD : ¬ D q)
    (hpchild : ∃ a ∈ V, a ∈ C p ∧ D a)
    (hqchild : ∃ a ∈ V, a ∈ C q ∧ D a) :
    ∃ a ∈ V, ∃ b ∈ V, ∃ v, a ≠ b ∧ v ∈ C a ∧ v ∈ C b := by
  obtain ⟨m, f, hm, hf0, hfm, hfV, hfD, hfC⟩ :=
    clean_consumer_path V C D d step p hp hpchild
  obtain ⟨n, g, hn, hg0, hgn, hgV, hgD, hgC⟩ :=
    clean_consumer_path V C D d step q hq hqchild
  apply TwoPathFork.fork_of_two_paths V C f g m n hfV hgV hfC hgC (hfm.trans hgn.symm)
  · intro j hj heq
    cases j with
    | zero => exact hpq (hf0.symm.trans (heq.trans hg0))
    | succ j =>
      have hd := hgD (j + 1) (by omega) hj
      exact hpD ((heq.symm.trans hf0) ▸ hd)
  · intro i hi heq
    cases i with
    | zero => exact hpq (hf0.symm.trans (heq.symm.trans hg0))
    | succ i =>
      have hd := hfD (i + 1) (by omega) hi
      exact hqD ((heq.symm.trans hg0) ▸ hd)

theorem live_dirty_has_clean_transition (V R : Finset ℕ) (C : ℕ → Finset ℕ)
    (D : ℕ → Prop)
    (hroots : ∀ r ∈ R, ¬ D r)
    (hlive : ∀ v ∈ V, v ∉ R → ∃ p ∈ V, v ∈ C p)
    (hearlier : ∀ p ∈ V, ∀ q ∈ C p, q < p)
    (hdirty : ∃ d ∈ V, D d) :
    ∃ p ∈ V, ¬ D p ∧ ∃ q ∈ V, q ∈ C p ∧ D q := by
  classical
  let W := V.filter D
  have hW : W.Nonempty := by
    obtain ⟨d, hd, hD⟩ := hdirty
    exact ⟨d, Finset.mem_filter.mpr ⟨hd, hD⟩⟩
  let w := W.max' hW
  have hwW : w ∈ W := Finset.max'_mem W hW
  obtain ⟨hwV, hwD⟩ := Finset.mem_filter.mp hwW
  have hwR : w ∉ R := fun h => hroots w h hwD
  obtain ⟨p, hpV, hwp⟩ := hlive w hwV hwR
  have hlt : w < p := hearlier p hpV w hwp
  have hpD : ¬ D p := by
    intro hD
    have hpW : p ∈ W := Finset.mem_filter.mpr ⟨hpV, hD⟩
    have hle : p ≤ w := Finset.le_max' W p hpW
    omega
  exact ⟨p, hpV, hpD, w, hwV, hwp, hwD⟩

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
