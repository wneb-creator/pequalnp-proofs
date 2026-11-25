import PetersenGeometry

namespace PEqualNP.Outside.L_meta_1884.SixOrbit

open PEqualNP.Outside.L_meta_2590_aux.Surplus

def pairI : Finset (Fin 10) := {0, 2}
def pairT (s : Bool) : Finset (Fin 10) := if s then {1, 3, 5} else {1, 4, 7}
def pairA (s : Bool) (f : Fin 10) : Finset (Fin 10) :=
  if s then
    if f = 1 then {3, 5, 6} else if f = 3 then {1, 4, 5} else {1, 3, 7}
  else
    if f = 1 then {4, 6, 7} else if f = 4 then {1, 3, 7} else {1, 4, 5}

lemma two_ineligible_neighbors_three {D : Dag}
    (h : StrictLive 10 D) (hD : Correct D) {i j x : Fin 10}
    (hi : i ∈ ineligSet 10 D) (hj : j ∈ ineligSet 10 D)
    (hij : i ≠ j) (hix : Adj i x) (hjx : Adj j x) :
    3 ≤ (sem_W 10 D x).card := by
  obtain ⟨e, he, _, hse, he0, hne, hWe, _⟩ := sem_inelig_consumer sem_petersen_gr h hD hi
  obtain ⟨f, hf, _, hsf, hf0, hnf, hWf, _⟩ := sem_inelig_consumer sem_petersen_gr h hD hj
  have hxe : sem_bar e ∈ sem_W 10 D x := sem_mem_W.mpr
    ⟨he, hne x hix, by change x ∉ supp 10 D (10 + e.1); rw [he0]; exact Finset.notMem_empty _⟩
  have hxf : sem_bar f ∈ sem_W 10 D x := sem_mem_W.mpr
    ⟨hf, hnf x hjx, by change x ∉ supp 10 D (10 + f.1); rw [hf0]; exact Finset.notMem_empty _⟩
  have hxi : x ≠ i := by rintro rfl; exact adj_irrefl x hix
  by_contra hc
  obtain ⟨Z, _, hW, _, hZ⟩ := sem_pg_private_slot h hD hi hxi hWe hxe (by omega)
  rw [hW, Finset.mem_insert, Finset.mem_singleton] at hxf
  rcases hxf with hfe | hfZ
  · have hfe' : f = e := by simpa only [sem_bar_bar] using congrArg sem_bar hfe
    have hh : ({j} : Finset (Fin 10)) = {i} := by rw [← hsf, hfe', hse]
    exact hij (Finset.singleton_injective hh).symm
  · exact hZ j hj f hWf (by rw [← hfZ]; rfl)

lemma common_code_obstruction {D : Dag} (h : StrictLive 10 D) (hD : Correct D)
    (b : Fin 10 → ℕ) (hb : sem_MinBranch 10 D b)
    (hone : Bplus 10 D = (eligSet 10 D).card + 1)
    {x c a : Fin 10} (hxc : x ≠ c) (hxa : x ≠ a) (hca : ¬ Adj c a)
    (hx : 3 ≤ (sem_W 10 D x).card)
    {Y : ℕ × Bool} (hY : Y ∈ sem_W 10 D x)
    (hYa : a ∈ supp 10 D (src D Y)) (hYc : c ∉ supp 10 D (src D Y)) :
    (sem_W 10 D c).card ≤ 2 := by
  classical
  by_contra hc
  have hc3 : 3 ≤ (sem_W 10 D c).card := by omega
  have hrc : (residualUnits 10 D b).card = 1 := by
    have := card_residual h.1 b (sem_minBranch_pure hb)
    omega
  obtain ⟨u, hres⟩ := Finset.card_eq_one.mp hrc
  have hxc3 := (sem_saturated sem_petersen_gr h hD b (sem_minBranch_pure hb) hres hx).1
  obtain ⟨P, Q, hPQ, hall⟩ := sem_common_terminals sem_petersen_gr h hD b hb hone
    ({x, c} : Finset (Fin 10)) (by simp) (by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact hx
      · exact hc3)
  have hPx := (hall x (by simp)).1
  have hQx := (hall x (by simp)).2
  have hPc := (sem_mem_W.mp (hall c (by simp)).1).2.1
  have hQc := (sem_mem_W.mp (hall c (by simp)).2).2.1
  have hYP : Y ≠ P := by rintro rfl; exact hYc hPc
  have hYQ : Y ≠ Q := by rintro rfl; exact hYc hQc
  have hPneQ : P ≠ Q := fun he => hPQ (congrArg Prod.fst he)
  have hW : sem_W 10 D x = {Y, P, Q} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl <;> assumption
    · rw [hxc3]
      simp [hYP, hYQ, hPneQ]
  obtain ⟨e, he, hec, hea⟩ := sem_pg_cover_free h hD hxc hxa hca
  rw [hW, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl
  · exact hea hYa
  · exact hec hPc
  · exact hec hQc

lemma pair_orbit_impossible {D : Dag} (h : StrictLive 10 D) (hD : Correct D)
    (hsize : D.length ≤ 18) (hI : ineligSet 10 D = pairI) : False := by
  classical
  have hG := sem_petersen_gr
  obtain ⟨b, hbm⟩ := sem_exists_minBranch hG h.1 hD
  have hb := sem_minBranch_pure hbm
  obtain ⟨pos, hpos⟩ := k4_assigned hG h hD
  have hi0 : (0 : Fin 10) ∈ ineligSet 10 D := by rw [hI]; decide
  have hi2 : (2 : Fin 10) ∈ ineligSet 10 D := by rw [hI]; decide
  have hp : (eligSet 10 D).card = 8 := by
    have he := Finset.card_le_univ (eligSet 10 D)
    have hc : (ineligSet 10 D).card + (eligSet 10 D).card = 10 := by
      rw [ineligSet, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
        Fintype.card_fin]
      simp only [Fintype.card_fin] at he
      omega
    rw [hI, show pairI.card = 2 by decide] at hc
    omega
  have hJ (s : Bool) : ∀ i ∈ pairI, i ∈ ineligSet 10 D ∧
      (∃ a ∈ pairT s, Adj i a) ∧ ∀ f ∈ pairT s, ∃ a ∈ pairA s f, Adj i a := by
    intro i hi
    refine ⟨by rw [hI]; exact hi, ?_⟩
    have hc : ∀ s i, i ∈ pairI → (∃ a ∈ pairT s, Adj i a) ∧
        ∀ f ∈ pairT s, ∃ a ∈ pairA s f, Adj i a := by decide +kernel
    exact hc s i hi
  have hA (s : Bool) : ∀ f ∈ pairT s,
      (∀ a ∈ pairA s f, ∀ c ∈ pairA s f, ¬ Adj a c) ∧
      (pairT s).erase f ⊆ pairA s f ∧ ∃ a ∈ pairA s f, Adj f a := by
    have hc : ∀ s f, f ∈ pairT s →
        (∀ a ∈ pairA s f, ∀ c ∈ pairA s f, ¬ Adj a c) ∧
        (pairT s).erase f ⊆ pairA s f ∧ ∃ a ∈ pairA s f, Adj f a := by decide +kernel
    exact hc s
  have hbound := tri_bound hG h hD b hb hpos (pairT false) pairI (pairA false) (hJ false) (hA false)
    (x := (1 : Fin 10)) (y := (4 : Fin 10)) (z := (7 : Fin 10))
    (by decide : pairT false = {1, 4, 7}) (by decide) (by decide) (by decide)
    ((hpos.1 0 hi0).2.2.1 1 (by decide)) ((hpos.1 0 hi0).2.2.1 4 (by decide))
    ((hpos.1 2 hi2).2.2.1 1 (by decide)) ((hpos.1 2 hi2).2.2.1 7 (by decide))
  have hs := surplus_identity h
  have hsplit := totalSurplus_split 10 D
  rw [hp, show pairI.card = 2 by decide] at hbound
  have hzero : Bzero 10 D = 0 := by omega
  have hB : Bplus 10 D = 9 := by omega
  have hone : Bplus 10 D = (eligSet 10 D).card + 1 := by omega
  have hocc (s : Bool) : ∀ i ∈ pairI,
      sup_Occ 10 D (pairT s) ((pairT s).filter (Adj i)) := by
    intro i hi
    have hii : i ∈ ineligSet 10 D := by rw [hI]; exact hi
    have chain := sem_noempty_chain_out hG h hD hzero hii
    have hind : ∀ a ∈ pairT s, ∀ c ∈ pairT s, ¬ Adj a c := by
      have hc : ∀ s a, a ∈ pairT s → ∀ c ∈ pairT s, ¬ Adj a c := by decide +kernel
      exact hc s
    obtain ⟨j, t, hj, ht, hc, he⟩ := sem_exact_nbhd hG h.1 hD (pairT s) hind chain
    refine ⟨src D (j, t), ?_⟩
    ext a
    simp only [Finset.mem_inter, Finset.mem_filter]
    exact ⟨fun ha => ⟨ha.2, (he a ha.2).mp ha.1⟩, fun ha => ⟨(he a ha.1).mpr ha.2, ha.1⟩⟩
  have hfull (s : Bool) : ∀ w, ¬ pairT s ⊆ supp 10 D w := by
    let F : Finset (Finset (Fin 10)) :=
      {(pairT s).filter (Adj 0), (pairT s).filter (Adj 2)}
    have hF : ∀ M ∈ F, M.card = 2 ∧ sup_Occ 10 D (pairT s) M := by
      intro M hM
      simp only [F, Finset.mem_insert, Finset.mem_singleton] at hM
      rcases hM with rfl | rfl
      · refine ⟨?_, hocc s 0 (by decide)⟩
        cases s <;> decide
      · refine ⟨?_, hocc s 2 (by decide)⟩
        cases s <;> decide
    have hFc : F.card = 2 := by cases s <;> decide
    have hTc : (pairT s).card = 3 := by cases s <;> decide
    exact (tri_sat hG h hD b hb hpos (pairT s) pairI (pairA s) (hJ s) (hA s) F hF hTc (by
      rw [hB, hp, hFc, hTc, show pairI.card = 2 by decide])).1
  obtain ⟨e0, he0, _, hse0, hz0, hn0, hWe0, _⟩ := sem_inelig_consumer hG h hD hi0
  obtain ⟨e2, he2, _, hse2, hz2, hn2, hWe2, _⟩ := sem_inelig_consumer hG h hD hi2
  have hY0 (x : Fin 10) (hx : Adj 0 x) : sem_bar e0 ∈ sem_W 10 D x :=
    sem_mem_W.mpr ⟨he0, hn0 x hx, by change x ∉ supp 10 D (10 + e0.1); rw [hz0]; simp⟩
  have hY2 (x : Fin 10) (hx : Adj 2 x) : sem_bar e2 ∈ sem_W 10 D x :=
    sem_mem_W.mpr ⟨he2, hn2 x hx, by change x ∉ supp 10 D (10 + e2.1); rw [hz2]; simp⟩
  have hW1 : 3 ≤ (sem_W 10 D 1).card :=
    two_ineligible_neighbors_three h hD hi0 hi2 (by decide) (by decide) (by decide)
  have h3 : (sem_W 10 D 3).card ≤ 2 :=
    common_code_obstruction h hD b hbm hone (x := 1) (c := 3) (a := 5)
      (by decide) (by decide) (by decide) hW1 (hY0 1 (by decide)) (hn0 5 (by decide)) (by
        intro hc
        apply hfull true (src D (sem_bar e0))
        intro a ha
        simp only [pairT, ↓reduceIte, Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl | rfl
        · exact hn0 1 (by decide)
        · exact hc
        · exact hn0 5 (by decide))
  have h4 : (sem_W 10 D 4).card ≤ 2 :=
    common_code_obstruction h hD b hbm hone (x := 1) (c := 4) (a := 7)
      (by decide) (by decide) (by decide) hW1 (hY2 1 (by decide)) (hn2 7 (by decide)) (by
        intro hc
        apply hfull false (src D (sem_bar e2))
        intro a ha
        simp only [pairT, Bool.false_eq_true, ↓reduceIte, Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl | rfl
        · exact hn2 1 (by decide)
        · exact hc
        · exact hn2 7 (by decide))
  obtain ⟨Z3, hZ3, hW3, hp3, _⟩ := sem_pg_private_slot h hD hi2 (by decide : (3 : Fin 10) ≠ 2)
    hWe2 (hY2 3 (by decide)) h3
  obtain ⟨Z4, hZ4, hW4, hp4, _⟩ := sem_pg_private_slot h hD hi0 (by decide : (4 : Fin 10) ≠ 0)
    hWe0 (hY0 4 (by decide)) h4
  have edge3 (v : Fin 10) (hv : Adj 3 v) (hv2 : v ≠ 2) : sem_bar Z3 ∈ sem_W 10 D v := by
    obtain ⟨e, he, hev, -, -, -⟩ := sem_edge_slots hG h.1 hD hv
    rw [hW3, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · have hv' := (sem_mem_W.mp hev).2.1
      rw [sem_bar_bar, hse2, Finset.mem_singleton] at hv'
      exact (hv2 hv').elim
    · exact hev
  have hm4 := edge3 4 (by decide) (by decide)
  rw [hW4, Finset.mem_insert, Finset.mem_singleton] at hm4
  have hz : sem_bar Z3 = Z4 := by
    rcases hm4 with he | he
    · have he' : Z3 = e0 := by simpa only [sem_bar_bar] using congrArg sem_bar he
      have hz3m : Z3 ∈ sem_W 10 D 3 := by rw [hW3]; simp
      have hv := (sem_mem_W.mp hz3m).2.1
      rw [he', hse0, Finset.mem_singleton] at hv
      exact (by decide : (3 : Fin 10) ≠ 0) hv |>.elim
    · exact he
  exact hp4 8 (by decide) (hz ▸ edge3 8 (by decide) (by decide))

end PEqualNP.Outside.L_meta_1884.SixOrbit
