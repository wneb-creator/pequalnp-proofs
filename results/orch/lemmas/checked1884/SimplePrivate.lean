import PetersenGeometry

namespace PEqualNP.Outside.L_meta_1884_aux.SimplePrivate

open PEqualNP.Outside.L_meta_2590_aux.Surplus

lemma simple_has_pure_exception {D : Dag} (h : StrictLive 10 D) (hD : Correct D)
    (v : Fin 10) (hv : ∀ t, Adj v t → t ∈ ineligSet 10 D)
    {c : Fin 10} (hc : c ∈ eligSet 10 D) (hcv : c ≠ v)
    (hs : ∃ Z, ∀ e ∈ sem_W 10 D c, e ≠ Z → v ∈ supp 10 D (src D e)) :
    ∃ Z, Z ∈ sem_W 10 D c ∧ supp 10 D (src D Z) = {c} ∧
      ∀ e ∈ sem_W 10 D c, e ≠ Z → v ∈ supp 10 D (src D e) := by
  classical
  obtain ⟨Z, hZ⟩ := hs
  obtain ⟨e, he, hev⟩ := sem_antichain sem_petersen_gr h.1 hD hcv
  have heZ : e = Z := by
    by_contra hne
    exact hev (hZ e he hne)
  subst e
  have hcZ := (sem_mem_W.mp he).2.1
  refine ⟨Z, he, Finset.Subset.antisymm ?_ (Finset.singleton_subset_iff.mpr hcZ), hZ⟩
  intro t ht
  rw [Finset.mem_singleton]
  by_contra htc
  by_cases hi : t ∈ ineligSet 10 D
  · have hp := sem_inelig_pure sem_petersen_gr h.1 hD hi ht
    rw [hp, Finset.mem_singleton] at hcZ
    exact htc hcZ.symm
  · have hvt : ¬ Adj v t := fun ha => hi (hv t ha)
    obtain ⟨f, hf, hfv, hft⟩ := sem_pg_cover_free h hD hcv (Ne.symm htc) hvt
    by_cases hfZ : f = Z
    · exact hft (hfZ.symm ▸ ht)
    · exact hfv (hZ f hf hfZ)

end PEqualNP.Outside.L_meta_1884_aux.SimplePrivate
