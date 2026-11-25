theorem equality_m9_two_missing_impossible {D : Dag}
    (h : StrictLive 14 D) (hD : Correct D) (h14 : totalSurplus 14 D ≤ 14)
    (hI : ineligSet 14 D = {0,1,2,5,11})
    (hM : equality_missing_cap D = {2,5}) : False :=
  equality_m9_two_missing_impossible_of_certificate m9_point_empty h hD h14 hI hM

theorem equality_m9_any_two_missing_impossible {D : Dag}
    (h : StrictLive 14 D) (hD : Correct D) (h14 : totalSurplus 14 D ≤ 14)
    (hI : ineligSet 14 D = {0,1,2,5,11})
    (two : (equality_missing_cap D).card = 2) : False :=
  equality_m9_any_two_missing_of_canonical (fun h hD h14 hI hM =>
    equality_m9_two_missing_impossible h hD h14 hI hM) h hD h14 hI two
