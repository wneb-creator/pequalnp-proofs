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
