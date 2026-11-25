import PetersenSurplus

namespace PEqualNP.Outside.L_meta_2590_aux.Surplus

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def pg_adjB (u v : Fin 10) : Bool :=
  (([50, 69, 138, 276, 521, 385, 770, 548, 104, 208] : List Nat).getD u.val 0).testBit v.val

abbrev Adj (u v : Fin 10) : Prop := pg_adjB u v = true

theorem pg_adjB_iff (u v : Fin 10) : pg_adjB u v = true ↔ Adj u v := Iff.rfl

theorem adj_symm : ∀ u v : Fin 10, Adj u v → Adj v u := by decide +kernel

theorem adj_irrefl : ∀ u : Fin 10, ¬ Adj u u := by decide +kernel

theorem sem_petersen_gr : sem_Gr Adj :=
  ⟨adj_symm, adj_irrefl, by decide +kernel, by decide +kernel⟩

def Correct (D : Dag) : Prop := sem_Comp 10 Adj D

theorem sem_petersen_comp {D : Dag} (h : Correct D) : sem_Comp 10 Adj D := h

def IsCover (S : Finset (Fin 10)) : Prop := ∀ u v : Fin 10, Adj u v → u ∈ S ∨ v ∈ S

def IsIndep (I : Finset (Fin 10)) : Prop := ∀ u ∈ I, ∀ v ∈ I, ¬ Adj u v

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem indep_card_le_four : ∀ I : Finset (Fin 10), IsIndep I → I.card ≤ 4 := by
  unfold IsIndep
  decide +kernel

theorem elig_independent {D : Dag} (h : StrictLive 10 D) (hD : Correct D) :
    IsIndep (ineligSet 10 D) := by
  intro u hu v hv huv
  rcases sem_elig_cover sem_petersen_gr h hD huv with he | he
  · exact (sem_mem_inelig.mp hu) he
  · exact (sem_mem_inelig.mp hv) he

theorem pg_budget {D : Dag} (h : StrictLive 10 D) (hD : Correct D) (hsize : D.length ≤ 19) :
    totalSurplus 10 D ≤ 10 ∧ 6 ≤ (eligSet 10 D).card ∧
      (eligSet 10 D).card ≤ Bplus 10 D := by
  have hs := surplus_identity h
  have hi := indep_card_le_four _ (elig_independent h hD)
  have hc : (ineligSet 10 D).card + (eligSet 10 D).card = 10 := by
    rw [ineligSet, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
    have he := Finset.card_le_univ (eligSet 10 D)
    simp only [Fintype.card_fin] at he
    omega
  obtain ⟨b, hb⟩ := sem_exists_pureBranch sem_petersen_gr h.1 hD
  exact ⟨by omega, by omega, elig_le_Bplus h.1 b hb⟩

theorem sem_pg_third : ∀ x a b : Fin 10, x ≠ a → x ≠ b → pg_adjB a b = false →
    ∃ y, pg_adjB x y = true ∧ pg_adjB y a = false ∧ pg_adjB y b = false := by decide +kernel

theorem sem_pg_two_nbrs : ∀ i x : Fin 10, ∃ r s, r ≠ s ∧ pg_adjB i r = true ∧
    pg_adjB i s = true ∧ r ≠ x ∧ s ≠ x := by decide +kernel

theorem sem_pg_common : ∀ r s t i : Fin 10, r ≠ s → pg_adjB i r = true → pg_adjB i s = true →
    pg_adjB t r = true → pg_adjB t s = true → t = i := by decide +kernel

theorem sem_adjB_false {u v : Fin 10} : pg_adjB u v = false ↔ ¬ Adj u v := by
  rw [← pg_adjB_iff, Bool.not_eq_true]



theorem sem_pg_cover_free {D : Dag} (h : StrictLive 10 D) (hD : Correct D) {x a b : Fin 10}
    (hxa : x ≠ a) (hxb : x ≠ b) (hab : ¬ Adj a b) :
    ∃ e, e ∈ sem_W 10 D x ∧ a ∉ supp 10 D (src D e) ∧ b ∉ supp 10 D (src D e) := by
  obtain ⟨y, h1, h2, h3⟩ := sem_pg_third x a b hxa hxb (sem_adjB_false.mpr hab)
  exact sem_cover_free sem_petersen_gr h.1 (sem_petersen_comp hD) hab ((pg_adjB_iff x y).mp h1)
    (sem_adjB_false.mp h2) (sem_adjB_false.mp h3)





theorem sem_pg_private_slot {D : Dag} (h : StrictLive 10 D) (hD : Correct D) {i x : Fin 10}
    (hi : i ∈ ineligSet 10 D) (hxi : x ≠ i) {e : ℕ × Bool} (he : sem_W 10 D i = {e})
    (hY : sem_bar e ∈ sem_W 10 D x) (hc : (sem_W 10 D x).card ≤ 2) :
    ∃ Z, Z ≠ sem_bar e ∧ sem_W 10 D x = {sem_bar e, Z} ∧ (∀ t, t ≠ x → Z ∉ sem_W 10 D t) ∧
      ∀ i' ∈ ineligSet 10 D, ∀ e', sem_W 10 D i' = {e'} → Z.1 ≠ e'.1 := by
  have hG := sem_petersen_gr
  have hC := sem_petersen_comp hD
  have hS := h.1
  have hcons : ∀ i' ∈ ineligSet 10 D, ∀ e', sem_W 10 D i' = {e'} →
      supp 10 D (src D e') = {i'} ∧ supp 10 D (10 + e'.1) = ∅ ∧
        ∀ q, Adj i' q → q ∈ supp 10 D (src D (sem_bar e')) := by
    intro i' hi' e' he'
    obtain ⟨e0, -, -, hsrc0, hemp0, hnb0, hx0, -⟩ := sem_inelig_consumer hG h hC hi'
    have h1 : ({e'} : Finset (ℕ × Bool)) = {e0} := he'.symm.trans hx0
    have h2 : e' = e0 := Finset.singleton_injective h1
    subst h2
    exact ⟨hsrc0, hemp0, hnb0⟩
  obtain ⟨hsrc, -, hYn⟩ := hcons i hi e he
  obtain ⟨r, s, hrs, hir, his, hrx, hsx⟩ := sem_pg_two_nbrs i x
  rw [pg_adjB_iff] at hir his
  obtain ⟨Z, hZ, hZr⟩ := sem_antichain hG hS hC (x := x) (a := r) (Ne.symm hrx)
  have hZY : Z ≠ sem_bar e := by
    rintro rfl
    exact hZr (hYn r hir)
  have hW : sem_W 10 D x = {sem_bar e, Z} := by
    symm
    refine Finset.eq_of_subset_of_card_le (fun f hf => ?_) ?_
    · rw [Finset.mem_insert, Finset.mem_singleton] at hf
      rcases hf with rfl | rfl
      · exact hY
      · exact hZ
    · rw [Finset.card_pair (Ne.symm hZY)]; exact hc
  have hpriv : ∀ t, t ≠ x → Z ∉ sem_W 10 D t := by
    intro t htx hZt
    have key : ∀ q, q ≠ x → q ∈ supp 10 D (src D (sem_bar e)) → Adj q t := by
      intro q hqx hq
      by_contra hqt
      obtain ⟨f, hf, h1, h2⟩ := sem_pg_cover_free h hD (x := x) (a := q) (b := t)
        (Ne.symm hqx) (Ne.symm htx) hqt
      rw [hW, Finset.mem_insert, Finset.mem_singleton] at hf
      rcases hf with rfl | rfl
      · exact h1 hq
      · exact h2 (sem_mem_W.mp hZt).2.1
    have hrt := adj_symm _ _ (key r hrx (hYn r hir))
    have hst := adj_symm _ _ (key s hsx (hYn s his))
    have hti : t = i := sem_pg_common r s t i hrs ((pg_adjB_iff _ _).mpr hir)
      ((pg_adjB_iff _ _).mpr his) ((pg_adjB_iff _ _).mpr hrt) ((pg_adjB_iff _ _).mpr hst)
    rw [hti, he, Finset.mem_singleton] at hZt
    have hx2 := (sem_mem_W.mp hZ).2.1
    rw [hZt, hsrc, Finset.mem_singleton] at hx2
    exact hxi hx2
  refine ⟨Z, hZY, hW, hpriv, ?_⟩
  intro i' hi' e' he' hgate
  obtain ⟨-, hemp', hYn'⟩ := hcons i' hi' e' he'
  have hxi' : x ≠ i' := by
    intro hc
    have h1 : (sem_W 10 D x).card = 2 := by rw [hW, Finset.card_pair (Ne.symm hZY)]
    rw [hc, he', Finset.card_singleton] at h1
    omega
  rcases sem_same_gate hgate.symm with h1 | h1
  · exact hpriv i' (Ne.symm hxi') (by rw [he', Finset.mem_singleton]; exact h1)
  · obtain ⟨r', s', hrs', hir', his', hrx', -⟩ := sem_pg_two_nbrs i' x
    rw [pg_adjB_iff] at hir'
    refine hpriv r' hrx' (sem_mem_W.mpr ⟨(sem_mem_W.mp hZ).1, ?_, ?_⟩)
    · rw [h1]; exact hYn' r' hir'
    · rw [hgate, hemp']; exact Finset.notMem_empty _

end PEqualNP.Outside.L_meta_2590_aux.Surplus
