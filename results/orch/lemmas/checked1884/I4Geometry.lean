import I4Full

namespace PEqualNP.Outside.L_meta_1884_aux.I4Geometry

open PEqualNP.Outside.L_meta_2590_aux.Surplus
open PEqualNP.Outside.L_meta_1884_aux.I4Bridge

def I : Finset (Fin 10) := {2, 4, 5, 6}
def E : Finset (Fin 10) := {0, 1, 3, 7, 8, 9}
def neighbors (x : Fin 10) : Finset (Fin 10) := I.filter fun i => pg_adjB i x = true

def vertex (e : Fin 6) : Fin 10 :=
  ([3, 7, 1, 0, 9, 8] : List (Fin 10)).getD e.val 0

def center (i : Fin 4) : Fin 10 :=
  ([2, 4, 5, 6] : List (Fin 10)).getD i.val 0

theorem vertex_bijection : Function.Injective vertex ∧
    ∀ x : Fin 10, x ∈ E ↔ ∃ e : Fin 6, vertex e = x := by decide +kernel

theorem center_bijection : Function.Injective center ∧
    ∀ x : Fin 10, x ∈ I ↔ ∃ i : Fin 4, center i = x := by decide +kernel

theorem finite_geometry : E.card = 6 ∧ I.card = 4 ∧
    (E.biUnion neighbors).card = 4 ∧
    (∀ x ∈ E, ∀ y ∈ E, x ≠ y → 3 ≤ (neighbors x ∪ neighbors y).card) ∧
    (∀ x ∈ E, ∃ y ∈ E, pg_adjB x y = true) := by decide +kernel

theorem eligibility {D : Dag} (hI : ineligSet 10 D = I) : eligSet 10 D = E := by
  classical
  ext x
  have hcomp : ∀ x : Fin 10, x ∉ I ↔ x ∈ E := by decide +kernel
  rw [← hcomp x, ← hI, sem_mem_inelig]
  simp

set_option synthInstance.maxSize 12000 in
theorem two_neighbors : ∀ x : Fin 10, x ∈ E →
    ∃ i ∈ I, ∃ j ∈ I, i ≠ j ∧ pg_adjB i x = true ∧ pg_adjB j x = true := by
  decide +kernel

theorem two_neighbors_code {D : Dag}
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

theorem profile_nonempty {D : Dag}
    (h : StrictLive 10 D) (hD : Correct D) (hI : ineligSet 10 D = I)
    (b : Fin 10 → Nat) (hb : PureBranch 10 D b) :
    ∀ x ∈ eligSet 10 D, (profile D b x).Nonempty := by
  intro x hx
  have hxE : x ∈ E := eligibility hI ▸ hx
  obtain ⟨i, hi, j, hj, hij, hix, hjx⟩ := two_neighbors x hxE
  rw [← hI] at hi hj
  have hc := two_neighbors_code h hD hi hj hij hix hjx
  have hcount := sem_code_count sem_petersen_gr h hD b hb x
  have hint : ({x} ∩ eligSet 10 D).card = 1 := by simp [hx]
  rw [hint] at hcount
  change _ + _ = _ + (profile D b x).card at hcount
  apply Finset.card_pos.mp
  omega

theorem centers_biUnion {D : Dag} (hI : ineligSet 10 D = I)
    (b : Fin 10 → Nat) (c : Fin 10) :
    centers D b c = (E.filter fun x => profile D b x ⊆ profile D b c).biUnion neighbors := by
  classical
  ext i
  simp only [centers, hI, eligibility hI, neighbors, Finset.mem_filter, Finset.mem_biUnion]
  constructor
  · rintro ⟨hi, x, hx, hsub, hix⟩
    exact ⟨x, ⟨hx, hsub⟩, hi, hix⟩
  · rintro ⟨x, ⟨hx, hsub⟩, hi, hix⟩
    exact ⟨hi, x, hx, hsub, hix⟩

end PEqualNP.Outside.L_meta_1884_aux.I4Geometry
