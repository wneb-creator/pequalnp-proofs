import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1896_aux.FourRows

abbrev incidence (p l : Fin 13) : Prop := p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9

def points (a : Fin 4) : Finset (Fin 13) :=
  ([{0, 1, 2}, {3, 4, 5}, {6, 8, 12}, {7, 9, 10, 11}] : List (Finset (Fin 13))).getD a.val ∅

def row (a : Fin 4) (v : Fin 26) : Bool :=
  decide (v.val ∈ ([[0, 1, 2, 16, 20, 21, 22], [3, 4, 5, 19, 23, 24, 25], [6, 8, 12, 13, 14, 15, 17], [7, 9, 10, 11, 16, 18, 25]] : List (List ℕ)).getD a.val [])

def rowInput (X : Finset (Fin 13)) (v : Fin 26) : Bool :=
  decide ((∃ p ∈ X, v = Fin.castAdd 13 p) ∨
    ∃ l : Fin 13, v = Fin.natAdd 13 l ∧ ∀ p ∈ X, ¬incidence p l)

def admissible (X : Finset (Fin 13)) : Prop :=
  (∀ p ∉ X, ∃ l : Fin 13, (∀ q ∈ X, ¬incidence q l) ∧ incidence p l) ∧
  (¬∃ l : Fin 13, ∀ p ∈ X, incidence p l) ∧
  ¬∃ p : Fin 13, ∀ l : Fin 13, (∀ q ∈ X, ¬incidence q l) → incidence p l

def missing (a : Fin 4) : Finset (Fin 26) := Finset.univ.filter fun v => row a v = false

def pairInput (p l : Fin 13) (v : Fin 26) : Bool :=
  decide (v = Fin.castAdd 13 p ∨ v = Fin.natAdd 13 l)

def edgeFor (a : Fin 4) (v : Fin 26) : Fin 13 × Fin 13 :=
  ([
    (0, 0), (0, 0), (0, 0), (3, 3), (4, 3), (5, 9), (6, 3), (7, 7), (8, 7), (9, 8), (10, 7), (11, 8), (12, 3),
    (0, 0), (1, 1), (2, 2), (0, 0), (0, 4), (1, 5), (2, 6), (0, 0), (0, 0), (0, 0), (0, 10), (1, 11), (0, 12),
    (0, 10), (1, 11), (2, 6), (0, 0), (0, 0), (0, 0), (6, 6), (7, 6), (8, 12), (9, 6), (10, 10), (11, 10), (12, 11),
    (3, 0), (4, 1), (3, 2), (3, 3), (4, 4), (5, 5), (0, 0), (3, 7), (4, 8), (5, 9), (0, 0), (0, 0), (0, 0),
    (0, 0), (1, 0), (2, 1), (3, 0), (4, 1), (5, 2), (0, 0), (7, 4), (0, 0), (9, 0), (10, 1), (11, 2), (0, 0),
    (0, 0), (0, 0), (0, 0), (6, 3), (0, 0), (6, 5), (6, 6), (8, 7), (8, 8), (12, 9), (6, 10), (12, 11), (8, 12),
    (0, 12), (1, 5), (2, 12), (3, 3), (4, 3), (5, 5), (6, 3), (0, 0), (8, 5), (0, 0), (0, 0), (0, 0), (12, 3),
    (9, 0), (10, 1), (11, 2), (0, 0), (7, 4), (0, 0), (7, 6), (7, 7), (9, 8), (9, 9), (10, 10), (7, 11), (0, 0)] : List (Fin 13 × Fin 13)).getD (26 * a.val + v.val) (0, 0)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
set_option synthInstance.maxSize 100000 in
lemma rows_admissible : ∀ a : Fin 4, admissible (points a) := by
  unfold admissible
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_eq : ∀ a : Fin 4, row a = rowInput (points a) := by decide +kernel

set_option maxRecDepth 10000 in
lemma missing_card : ∀ a : Fin 4, (missing a).card = 19 := by decide +kernel

set_option maxRecDepth 10000 in
lemma rows_cover : ∀ v : Fin 26, ∃ a : Fin 4, row a v = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
set_option synthInstance.maxSize 100000 in
lemma edgeFor_ok : ∀ (a : Fin 4) (v : Fin 26), row a v = false →
    incidence (edgeFor a v).1 (edgeFor a v).2 ∧
      ∀ w : Fin 26, row a w = false →
        pairInput (edgeFor a v).1 (edgeFor a v).2 w = true → w = v := by
  decide +kernel

end PEqualNP.Outside.L_meta_1896_aux.FourRows
