import PetersenGeometry

namespace PEqualNP.Outside.L_meta_2590_aux.Surplus

theorem all_eligible_budget {D : Dag} (h : StrictLive 10 D) (hD : Correct D)
    (hsize : D.length ≤ 19) (hall : eligSet 10 D = Finset.univ) :
    totalSurplus 10 D = 10 ∧ Bplus 10 D = 10 ∧ Bzero 10 D = 0 := by
  obtain ⟨h10, -, hp⟩ := pg_budget h hD hsize
  rw [hall, Finset.card_univ, Fintype.card_fin] at hp
  have split := totalSurplus_split 10 D
  omega

theorem all_eligible_residual {D : Dag} (h : StrictLive 10 D) (hD : Correct D)
    (hsize : D.length ≤ 19) (hall : eligSet 10 D = Finset.univ)
    (b : Fin 10 → Nat) (hb : PureBranch 10 D b) :
    residualUnits 10 D b = ∅ := by
  have hc := card_residual h.1 b hb
  rw [hall, Finset.card_univ, Fintype.card_fin,
    (all_eligible_budget h hD hsize hall).2.1] at hc
  exact Finset.card_eq_zero.mp (by omega)

theorem all_eligible_codes {D : Dag} (h : StrictLive 10 D) (hD : Correct D)
    (hsize : D.length ≤ 19) (hall : eligSet 10 D = Finset.univ) (x : Fin 10) :
    (sem_W 10 D x).card + (merges 10 D (carrierT 10 D {x})).card = 2 := by
  obtain ⟨b, hb⟩ := sem_exists_pureBranch sem_petersen_gr h.1 hD
  have hc := sem_code_count sem_petersen_gr h hD b hb x
  simpa [hall, all_eligible_residual h hD hsize hall b hb] using hc

theorem all_eligible_branches {D : Dag} (h : StrictLive 10 D) (hD : Correct D)
    (hsize : D.length ≤ 19) (hall : eligSet 10 D = Finset.univ)
    (b : Fin 10 → Nat) (hb : PureBranch 10 D b) {w : Nat}
    (hw : 2 ≤ fanout D w) :
    ∃ v : Fin 10, w = b v ∧ fanout D w = 2 ∧ supp 10 D w = {v} := by
  have hz := (all_eligible_budget h hD hsize hall).2.2
  have hsupp := sem_bzero_branch h.1 hz hw
  have hinner : w ∈ inner 10 D :=
    sb_mem_inner.mpr (lt_of_fanout_pos h.1 (by omega))
  have hres := all_eligible_residual h hD hsize hall b hb
  have reserve {j : Nat} (hj : j + 1 < fanout D w) :
      (⟨w, j⟩ : Sigma fun _ : Nat => Nat) ∈ reservedUnits 10 D b := by
    have hu : (⟨w, j⟩ : Sigma fun _ : Nat => Nat) ∈ unitsPlus 10 D :=
      Finset.mem_filter.mpr ⟨mem_units.mpr ⟨hinner, hj⟩, hsupp⟩
    by_contra hn
    have hm : (⟨w, j⟩ : Sigma fun _ : Nat => Nat) ∈ residualUnits 10 D b :=
      Finset.mem_sdiff.mpr ⟨hu, hn⟩
    rw [hres] at hm
    exact Finset.notMem_empty _ hm
  obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp (reserve (j := 0) (by omega))
  have hwv : w = b v := (congrArg Sigma.fst heq).symm
  have htwo : fanout D w = 2 := by
    by_contra hn
    obtain ⟨u, -, heq'⟩ := Finset.mem_image.mp (reserve (j := 1) (by omega))
    have bad : (0 : Nat) = 1 := congrArg (fun x : Sigma fun _ : Nat => Nat => x.2) heq'
    omega
  exact ⟨v, hwv, htwo, hwv ▸ (hb v hv).2⟩

end PEqualNP.Outside.L_meta_2590_aux.Surplus
