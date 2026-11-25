import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_2590_aux.Shape

def full (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
  (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) ||
  (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)

def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)

lemma same (y : Fin 9 → Bool) : full (Fin.lastCases false y) = edge y := by
  have h0 : Fin.lastCases false y (0 : Fin 10) = y (0 : Fin 9) := by
    exact Fin.lastCases_castSucc (0 : Fin 9)
  have h1 : Fin.lastCases false y (1 : Fin 10) = y (1 : Fin 9) := by
    exact Fin.lastCases_castSucc (1 : Fin 9)
  have h2 : Fin.lastCases false y (2 : Fin 10) = y (2 : Fin 9) := by
    exact Fin.lastCases_castSucc (2 : Fin 9)
  have h3 : Fin.lastCases false y (3 : Fin 10) = y (3 : Fin 9) := by
    exact Fin.lastCases_castSucc (3 : Fin 9)
  have h4 : Fin.lastCases false y (4 : Fin 10) = y (4 : Fin 9) := by
    exact Fin.lastCases_castSucc (4 : Fin 9)
  have h5 : Fin.lastCases false y (5 : Fin 10) = y (5 : Fin 9) := by
    exact Fin.lastCases_castSucc (5 : Fin 9)
  have h6 : Fin.lastCases false y (6 : Fin 10) = y (6 : Fin 9) := by
    exact Fin.lastCases_castSucc (6 : Fin 9)
  have h7 : Fin.lastCases false y (7 : Fin 10) = y (7 : Fin 9) := by
    exact Fin.lastCases_castSucc (7 : Fin 9)
  have h8 : Fin.lastCases false y (8 : Fin 10) = y (8 : Fin 9) := by
    exact Fin.lastCases_castSucc (8 : Fin 9)
  have h9 : Fin.lastCases false y (9 : Fin 10) = false := by
    exact Fin.lastCases_last
  simp only [full, edge, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    Bool.and_false, Bool.false_and, Bool.or_false]
end PEqualNP.Outside.L_meta_2590_aux.Shape
