import Mathlib

namespace PEqualNP.Outside.L_meta_1477.Hyperoval

def incidenceEdges : List (ℕ × ℕ) :=
  [(0, 21), (0, 26), (0, 28), (0, 38), (0, 41), (1, 21), (1, 22), (1, 27), (1, 29), (1, 39), (2, 22), (2, 23), (2, 28), (2, 30), (2, 40), (3, 23), (3, 24), (3, 29), (3, 31), (3, 41), (4, 21), (4, 24), (4, 25), (4, 30), (4, 32), (5, 22), (5, 25), (5, 26), (5, 31), (5, 33), (6, 23), (6, 26), (6, 27), (6, 32), (6, 34), (7, 24), (7, 27), (7, 28), (7, 33), (7, 35), (8, 25), (8, 28), (8, 29), (8, 34), (8, 36), (9, 26), (9, 29), (9, 30), (9, 35), (9, 37), (10, 27), (10, 30), (10, 31), (10, 36), (10, 38), (11, 28), (11, 31), (11, 32), (11, 37), (11, 39), (12, 29), (12, 32), (12, 33), (12, 38), (12, 40), (13, 30), (13, 33), (13, 34), (13, 39), (13, 41), (14, 21), (14, 31), (14, 34), (14, 35), (14, 40), (15, 22), (15, 32), (15, 35), (15, 36), (15, 41), (16, 21), (16, 23), (16, 33), (16, 36), (16, 37), (17, 22), (17, 24), (17, 34), (17, 37), (17, 38), (18, 23), (18, 25), (18, 35), (18, 38), (18, 39), (19, 24), (19, 26), (19, 36), (19, 39), (19, 40), (20, 25), (20, 27), (20, 37), (20, 40), (20, 41)]

def pointMap : Fin 6 → Fin 42 := ![0, 1, 2, 3, 10, 19]

def lineMap : Fin 15 → Fin 42 :=
  ![21, 28, 41, 38, 26, 22, 29, 27, 39, 23, 30, 40, 31, 24, 36]

def pairEnds : Fin 15 → Fin 6 × Fin 6 :=
  ![(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4),
    (1, 5), (2, 3), (2, 4), (2, 5), (3, 4), (3, 5), (4, 5)]

lemma pointMap_injective : Function.Injective pointMap := by decide

lemma lineMap_injective : Function.Injective lineMap := by decide

lemma pairEnds_distinct (j : Fin 15) : (pairEnds j).1 ≠ (pairEnds j).2 := by
  fin_cases j <;> decide

lemma pairEnds_exhaust (i j : Fin 6) (hij : i < j) :
    ∃ k : Fin 15, pairEnds k = (i, j) := by
  revert j
  fin_cases i <;> decide

lemma incidence_iff (i : Fin 6) (j : Fin 15) :
    ((pointMap i).val, (lineMap j).val) ∈ incidenceEdges ↔
      i = (pairEnds j).1 ∨ i = (pairEnds j).2 := by
  fin_cases i <;> fin_cases j <;> decide

lemma incidence_no_extra_line (i : Fin 6) (j : Fin 42)
    (h : ((pointMap i).val, j.val) ∈ incidenceEdges) :
    ∃ k : Fin 15, lineMap k = j := by
  revert j
  fin_cases i <;> decide

def points : Finset (Fin 21) := {0, 1, 2, 3, 10, 19}

def secants : Finset (Fin 21) := {0, 1, 2, 3, 5, 6, 7, 8, 9, 10, 15, 17, 18, 19, 20}

def incidentPoints (j : Fin 21) : Finset (Fin 21) :=
  points.filter (fun i => (i.val, j.val + 21) ∈ incidenceEdges)

lemma points_card : points.card = 6 := by decide

lemma secants_card : secants.card = 15 := by decide

lemma incidentPoints_card (j : Fin 21) :
    (incidentPoints j).card = if j ∈ secants then 2 else 0 := by
  fin_cases j <;> decide

end PEqualNP.Outside.L_meta_1477.Hyperoval
