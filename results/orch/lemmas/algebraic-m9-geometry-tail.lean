def equality_m9_line : Fin 6 → Fin 14 := ![7,8,10,13,9,12]

def equality_m9_point : Fin 4 → Fin 14 := ![0,1,2,5]

theorem equality_m9_line_injective : Function.Injective equality_m9_line := by decide +kernel

theorem equality_m9_point_injective : Function.Injective equality_m9_point := by decide +kernel

theorem equality_m9_adjacency : ∀ i : Fin 4, ∀ t : Fin 6,
    t ∈ m9_neighbors i ↔ hc_adjB (equality_m9_point i) (equality_m9_line t) = true := by
  decide +kernel

def equality_m9_cofactor : Fin 6 → List ℕ := ![[2,4,5,6,13,12,8,10,11,9],
  [1,3,4,5,7,13,9,11,12,10],
  [1,2,3,6,13,7,9,12,8,11],
  [0,3,5,6,7,10,8,12,11,9],
  [0,2,3,4,8,7,10,12,13,11],
  [0,1,4,6,7,10,8,13,9,11]]

theorem equality_m9_cf_good : ∀ t : Fin 6,
    cf_good (equality_m9_line t) (equality_m9_cofactor t) := by decide +kernel

