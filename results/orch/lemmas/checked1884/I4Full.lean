import I4Bridge

namespace PEqualNP.Outside.L_meta_1884_aux.I4Full

open PEqualNP.Outside.L_meta_2590_aux.Surplus
open PEqualNP.Outside.L_meta_1884_aux.I4Bridge

theorem assigned_singleton {D : Dag}
    (h : StrictLive 10 D) (hD : Correct D)
    {pos : Fin 10 → Nat × Bool} (hpos : k4_Pos 10 Adj D pos)
    {i : Fin 10} (hi : i ∈ ineligSet 10 D) :
    sem_W 10 D i = {sem_bar (pos i)} := by
  obtain ⟨e, _, _, _, _, _, hWe, _⟩ := sem_inelig_consumer sem_petersen_gr h hD hi
  change sem_W 10 D i = {e} at hWe
  have hmem : sem_bar (pos i) ∈ sem_W 10 D i := by
    obtain ⟨hp, hp0, _, hbar⟩ := hpos.1 i hi
    apply sem_mem_W.mpr
    refine ⟨hp, ?_, ?_⟩
    · change i ∈ supp 10 D (src D ((pos i).1, !(pos i).2))
      rw [hbar]
      exact Finset.mem_singleton_self _
    · change i ∉ supp 10 D (10 + (pos i).1)
      rw [hp0]
      exact Finset.notMem_empty _
  rw [hWe, Finset.mem_singleton] at hmem
  rw [hWe, hmem]

theorem saturated_full {D : Dag}
    (h : StrictLive 10 D) (hD : Correct D)
    (b : Fin 10 → Nat) (hb : PureBranch 10 D b)
    {pos : Fin 10 → Nat × Bool} (hpos : k4_Pos 10 Adj D pos)
    (hne : ∀ x ∈ eligSet 10 D, (profile D b x).Nonempty)
    (hz : Bzero 10 D = 0)
    {c y : Fin 10} (hc : c ∈ eligSet 10 D) (hy : y ∈ eligSet 10 D) (hcy : Adj c y)
    (hsat : (centers D b c).card = (profile D b c).card + 1)
    {i : Fin 10} (hi : i ∈ ineligSet 10 D) (hic : Adj i c) :
    ∀ t, t ∈ supp 10 D (src D (pos i)) ↔ Adj i t := by
  obtain ⟨e, he, _, hep, _, hey, _⟩ :=
    MatchingPrivate.eligible_edge_private_pair sem_petersen_gr h hD hpos hc hy hcy
  obtain ⟨hsub, hcard⟩ := center_image h hD b hb hpos hne hc
  have hnot : e ∉ (centers D b c).image pos := by
    intro hec
    obtain ⟨j, hj, hje⟩ := Finset.mem_image.mp hec
    exact hep (Finset.mem_image.mpr ⟨j, (Finset.mem_filter.mp hj).1, hje⟩)
  have hflow := sem_code_count sem_petersen_gr h hD b hb c
  have hint : ({c} ∩ eligSet 10 D).card = 1 := by simp [hc]
  rw [hint] at hflow
  change _ + _ = _ + (profile D b c).card at hflow
  have hEq : insert e ((centers D b c).image pos) = sem_W 10 D c :=
    Finset.eq_of_subset_of_card_le (Finset.insert_subset he hsub) (by
      rw [Finset.card_insert_of_notMem hnot, hcard, hsat]
      omega)
  have full := full_gen sem_petersen_gr h hD hz hi (assigned_singleton h hD hpos hi) hic
  rw [sem_bar_bar] at full
  apply full
  intro p hp hpi hbad
  rw [← hEq, Finset.mem_insert] at hp
  rcases hp with rfl | hp
  · have hyi : y = i := Finset.mem_singleton.mp (hbad hey)
    exact (sem_mem_inelig.mp hi) (hyi ▸ hy)
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp
    have hjI := (Finset.mem_filter.mp hj).1
    have hbar := (hpos.1 j hjI).2.2.2
    change supp 10 D (src D ((pos j).1, !(pos j).2)) ⊆ {i} at hbad
    rw [hbar] at hbad
    have hji : j = i := Finset.mem_singleton.mp (hbad (Finset.mem_singleton_self _))
    apply hpi
    change (pos j).1 = (pos i).1
    rw [hji]

theorem inclusion_conflict {D : Dag}
    (h : StrictLive 10 D) (hD : Correct D)
    (b : Fin 10 → Nat) (hb : PureBranch 10 D b)
    {pos : Fin 10 → Nat × Bool} (hpos : k4_Pos 10 Adj D pos)
    (hne : ∀ x ∈ eligSet 10 D, (profile D b x).Nonempty)
    (hz : Bzero 10 D = 0)
    {v y x c i : Fin 10}
    (hv : v ∈ eligSet 10 D) (hy : y ∈ eligSet 10 D) (hvy : Adj v y)
    (hx : x ∈ eligSet 10 D) (hc : c ∈ eligSet 10 D)
    (hi : i ∈ ineligSet 10 D) (hiv : Adj i v) (hix : Adj i x) (hic : ¬ Adj i c)
    (hsat : (centers D b v).card = (profile D b v).card + 1)
    (hsub : profile D b x ⊆ profile D b c) : False := by
  have full := saturated_full h hD b hb hpos hne hz hv hy hvy hsat hi hiv
  have hpc := profile_assigned h hD b hb hpos hx hc (hne x hx) hsub hi hix
  exact hic ((full c).mp (sem_mem_W.mp hpc).2.1)

end PEqualNP.Outside.L_meta_1884_aux.I4Full
