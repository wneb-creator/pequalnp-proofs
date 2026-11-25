
theorem pilotP10_Bplus_ge13 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hI : ineligSet 14 D = {0,1,2,3}) : 13 ≤ Bplus 14 D := by
  by_contra hn
  obtain ⟨r,hr⟩ := pilotP10_constraints h hD hI (by omega)
  exact p10_no_finset_constraints r hr

theorem pilotP10_Bzero_le1 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hI : ineligSet 14 D = {0,1,2,3}) (hS : totalSurplus 14 D ≤ 14) :
    Bzero 14 D ≤ 1 := by
  have lower := pilotP10_Bplus_ge13 h hD hI
  have split := totalSurplus_split 14 D
  omega
