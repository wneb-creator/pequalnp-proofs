import SimplePrivate

namespace PEqualNP.Outside.L_meta_1884_aux.SimpleAdjacency

open PEqualNP.Outside.L_meta_2590_aux.Surplus

lemma edge_slot_avoids_pivot {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}
    (hS : Strict n D) {pos : Fin n → ℕ × Bool} (hp : k4_Pos n G D pos)
    (v : Fin n) (hW : sem_W n D v ⊆ (ineligSet n D).image pos)
    (hm : merges n D (carrierT n D {v}) = ∅)
    {c y : Fin n} {e : ℕ × Bool} (he : e ∈ sem_W n D c)
    (hf : sem_bar e ∈ sem_W n D y) (hy : y ∈ eligSet n D) :
    v ∉ supp n D (src D e) := by
  classical
  intro hva
  have hj := (sem_mem_W.mp he).1
  have hand := sem_W_and hS he
  have hyb := (sem_mem_W.mp hf).2.1
  by_cases hvb : v ∈ supp n D (src D (sem_bar e))
  · have hab : v ∈ supp n D (opA D e.1) ∧ v ∈ supp n D (opB D e.1) := by
      obtain ⟨j, s⟩ := e
      cases s <;> simp only [src, sem_bar, Bool.not_false, Bool.not_true] at hva hvb ⊢
      · exact ⟨hva, hvb⟩
      · exact ⟨hvb, hva⟩
    have hout : v ∈ supp n D (n + e.1) := by
      rw [sem_supp_and hS hj hand]
      exact Finset.mem_inter.mpr hab
    have hmerge : e.1 ∈ merges n D (carrierT n D {v}) := by
      rw [merges, Finset.mem_filter, Finset.mem_range]
      exact ⟨hj, sem_mem_carrier1.mpr hout,
        sem_mem_carrier1.mpr hab.1, sem_mem_carrier1.mpr hab.2⟩
    rw [hm] at hmerge
    exact Finset.notMem_empty _ hmerge
  · have hout : v ∉ supp n D (n + e.1) := by
      intro hvout
      apply hvb
      exact sem_supp_and_sub hS hj hand (!e.2) hvout
    have hev : e ∈ sem_W n D v := sem_mem_W.mpr ⟨hj, hva, hout⟩
    obtain ⟨i, hi, hie⟩ := Finset.mem_image.mp (hW hev)
    have hs : supp n D (src D (sem_bar (pos i))) = {i} := (hp.1 i hi).2.2.2
    rw [← hie, hs, Finset.mem_singleton] at hyb
    exact sem_mem_inelig.mp hi (hyb ▸ hy)

lemma simple_adjacent_impossible {D : Dag} (h : StrictLive 10 D) (hD : Correct D)
    (v : Fin 10) (hv : ∀ t, Adj v t → t ∈ ineligSet 10 D)
    {pos : Fin 10 → ℕ × Bool} (hp : k4_Pos 10 Adj D pos)
    (hW : sem_W 10 D v ⊆ (ineligSet 10 D).image pos)
    (hm : merges 10 D (carrierT 10 D {v}) = ∅)
    {c d t : Fin 10} (hc : c ∈ eligSet 10 D) (hd : d ∈ eligSet 10 D)
    (ht : t ∈ eligSet 10 D) (hcv : c ≠ v) (hdv : d ≠ v)
    (hcd : Adj c d) (hct : Adj c t) (htd : t ≠ d)
    (hsc : ∃ Z, ∀ e ∈ sem_W 10 D c, e ≠ Z → v ∈ supp 10 D (src D e))
    (hsd : ∃ Z, ∀ e ∈ sem_W 10 D d, e ≠ Z → v ∈ supp 10 D (src D e)) : False := by
  obtain ⟨Zc, hZc, hpC, hC⟩ := SimplePrivate.simple_has_pure_exception h hD v hv hc hcv hsc
  obtain ⟨Zd, hZd, hpD, hDe⟩ := SimplePrivate.simple_has_pure_exception h hD v hv hd hdv hsd
  obtain ⟨e, he, hf, -, -, -⟩ := sem_edge_slots sem_petersen_gr h.1 hD hcd
  have hev := edge_slot_avoids_pivot h.1 hp v hW hm he hf hd
  have hfv := edge_slot_avoids_pivot h.1 hp v hW hm hf
    (by simpa only [sem_bar_bar] using he) hc
  have heZ : e = Zc := by by_contra hne; exact hev (hC e he hne)
  have hfZ : sem_bar e = Zd := by by_contra hne; exact hfv (hDe _ hf hne)
  obtain ⟨f, hf1, hf2, -, -, -⟩ := sem_edge_slots sem_petersen_gr h.1 hD hct
  have hfv2 := edge_slot_avoids_pivot h.1 hp v hW hm hf1 hf2 ht
  have hfZc : f = Zc := by by_contra hne; exact hfv2 (hC _ hf1 hne)
  have htm := (sem_mem_W.mp hf2).2.1
  have hfe : f = e := hfZc.trans heZ.symm
  rw [hfe, hfZ, hpD, Finset.mem_singleton] at htm
  exact htd htm

end PEqualNP.Outside.L_meta_1884_aux.SimpleAdjacency
