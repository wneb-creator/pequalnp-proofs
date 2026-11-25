import PetersenGeometry

namespace PEqualNP.Outside.L_meta_2590_aux.Surplus

 theorem two_ineligible_neighbors_code_ge_three {D : Dag}
    (h : StrictLive 10 D) (hD : Correct D) {i j x : Fin 10}
    (hi : i ∈ ineligSet 10 D) (hj : j ∈ ineligSet 10 D)
    (hij : i ≠ j) (hix : Adj i x) (hjx : Adj j x) :
    3 ≤ (sem_W 10 D x).card := by
  obtain ⟨e, he, _, hse, he0, hne, hWe, _⟩ :=
    sem_inelig_consumer sem_petersen_gr h hD hi
  obtain ⟨f, hf, _, hsf, hf0, hnf, hWf, _⟩ :=
    sem_inelig_consumer sem_petersen_gr h hD hj
  have hxe : sem_bar e ∈ sem_W 10 D x := sem_mem_W.mpr
    ⟨he, hne x hix, by change x ∉ supp 10 D (10 + e.1); rw [he0]; exact Finset.notMem_empty _⟩
  have hxf : sem_bar f ∈ sem_W 10 D x := sem_mem_W.mpr
    ⟨hf, hnf x hjx, by change x ∉ supp 10 D (10 + f.1); rw [hf0]; exact Finset.notMem_empty _⟩
  have hxi : x ≠ i := by
    rintro rfl
    exact adj_irrefl x hix
  by_contra hc
  have hc2 : (sem_W 10 D x).card ≤ 2 := by omega
  obtain ⟨Z, _, hW, _, hZ⟩ := sem_pg_private_slot h hD hi hxi hWe hxe hc2
  rw [hW, Finset.mem_insert, Finset.mem_singleton] at hxf
  rcases hxf with hfe | hfZ
  · have hfe' : f = e := by
      have hh := congrArg sem_bar hfe
      simpa only [sem_bar_bar] using hh
    have hh : ({j} : Finset (Fin 10)) = {i} := by
      rw [← hsf, hfe', hse]
    exact hij (Finset.singleton_injective hh).symm
  · have hh := hZ j hj f hWf
    exact hh (by rw [← hfZ]; rfl)

 theorem four_orbit_two_ineligible_neighbors :
    ∀ x : Fin 10, x ∉ ({2, 4, 5, 6} : Finset (Fin 10)) →
      ∃ i ∈ ({2, 4, 5, 6} : Finset (Fin 10)),
        ∃ j ∈ ({2, 4, 5, 6} : Finset (Fin 10)),
          i ≠ j ∧ Adj i x ∧ Adj j x := by decide +kernel

 theorem four_orbit_code_ge_three {D : Dag}
    (h : StrictLive 10 D) (hD : Correct D)
    (hI : ineligSet 10 D = ({2, 4, 5, 6} : Finset (Fin 10)))
    {x : Fin 10} (hx : x ∈ eligSet 10 D) :
    3 ≤ (sem_W 10 D x).card := by
  have hxn : x ∉ ({2, 4, 5, 6} : Finset (Fin 10)) := by
    rw [← hI]
    exact fun hh => (sem_mem_inelig.mp hh) hx
  obtain ⟨i, hi, j, hj, hij, hix, hjx⟩ := four_orbit_two_ineligible_neighbors x hxn
  rw [← hI] at hi hj
  exact two_ineligible_neighbors_code_ge_three h hD hi hj hij hix hjx

 theorem four_orbit_residual_incidence {D : Dag}
    (h : StrictLive 10 D) (hD : Correct D)
    (hI : ineligSet 10 D = ({2, 4, 5, 6} : Finset (Fin 10)))
    (b : Fin 10 → Nat) (hb : PureBranch 10 D b)
    {x : Fin 10} (hx : x ∈ eligSet 10 D) :
    1 ≤ ((residualUnits 10 D b).filter (fun u => x ∈ supp 10 D u.1)).card := by
  have hc := four_orbit_code_ge_three h hD hI hx
  have hcount := sem_code_count sem_petersen_gr h hD b hb x
  have hint : ({x} ∩ eligSet 10 D).card = 1 := by simp [hx]
  rw [hint] at hcount
  omega

end PEqualNP.Outside.L_meta_2590_aux.Surplus
