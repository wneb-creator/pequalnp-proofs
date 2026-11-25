import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2732_aux.FirstMixedGrowth

theorem first_mixed_growth {n : ℕ} (G : SimpleGraph (Fin n))
    (triangle : ∀ u v w, G.Adj u v → G.Adj v w → ¬ G.Adj u w)
    (k N r : ℕ) (S : ℕ → Finset (Fin n)) (a b : ℕ → ℕ) (A : ℕ → Bool)
    (hr : r < N)
    (hinput : ∀ w < k, (S w).card ≤ 1)
    (hparents : ∀ w, k ≤ w → w < N → a w < w ∧ b w < w)
    (hand : ∀ w, k ≤ w → w < N → A w = true → (S w).card ≤ 1)
    (hmixed : ∃ u ∈ S r, ∃ v ∈ S r, G.Adj u v) :
    ∃ w, k ≤ w ∧ w ≤ r ∧ w < N ∧ A w = false ∧ 1 < (S w).card ∧
      S w ≠ S (a w) ∧ S w ≠ S (b w) ∧ ¬ ∃ c, ∀ x ∈ S w, G.Adj c x := by
  classical
  have hex : ∃ w, w ≤ r ∧ ∃ u ∈ S w, ∃ v ∈ S w, G.Adj u v :=
    ⟨r, le_rfl, hmixed⟩
  let w := Nat.find hex
  obtain ⟨hwr, u, hu, v, hv, huv⟩ := Nat.find_spec hex
  change w ≤ r at hwr
  change u ∈ S w at hu
  change v ∈ S w at hv
  have hwN : w < N := by omega
  have hne : u ≠ v := fun h => G.loopless.irrefl v (h ▸ huv)
  have hbig : 1 < (S w).card := Finset.one_lt_card.mpr ⟨u, hu, v, hv, hne⟩
  have hkw : k ≤ w := by
    by_contra h
    have hs := hinput w (by omega)
    omega
  have hA : A w = false := by
    cases he : A w with
    | false => rfl
    | true => have hs := hand w hkw hwN he; omega
  obtain ⟨ha, hb⟩ := hparents w hkw hwN
  have hdiff (j : ℕ) (hj : j < w) : S w ≠ S j := by
    intro hS
    exact Nat.find_min hex hj ⟨by omega, u, hS ▸ hu, v, hS ▸ hv, huv⟩
  refine ⟨w, hkw, hwr, hwN, hA, hbig, hdiff _ ha, hdiff _ hb, ?_⟩
  rintro ⟨c, hc⟩
  exact triangle u v c huv (hc v hv).symm (hc u hu).symm

end PEqualNP.Outside.L_meta_2732_aux.FirstMixedGrowth
