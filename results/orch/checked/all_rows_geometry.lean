import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1896_aux.AllRows

abbrev R := Fin 36 × Fin 13

abbrev incidence (p l : Fin 13) : Prop := p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9

def points (a : R) : Finset (Fin 13) :=
  ((([
    [{0, 1, 2}, {0, 2, 3}, {1, 2, 3}, {0, 1, 4}, {0, 2, 4}, {0, 3, 4}, {1, 3, 4}, {2, 3, 4}, {0, 2, 3, 4}, {0, 1, 5}, {0, 2, 5}, {1, 2, 5}, {0, 1, 2, 5}],
    [{0, 3, 5}, {1, 3, 5}, {1, 4, 5}, {2, 4, 5}, {3, 4, 5}, {1, 3, 4, 5}, {0, 1, 6}, {0, 2, 6}, {1, 2, 6}, {0, 1, 2, 6}, {0, 3, 6}, {1, 3, 6}, {2, 3, 6}],
    [{0, 2, 3, 6}, {1, 2, 3, 6}, {0, 4, 6}, {1, 4, 6}, {0, 1, 4, 6}, {2, 4, 6}, {0, 2, 4, 6}, {0, 5, 6}, {2, 5, 6}, {0, 2, 5, 6}, {3, 5, 6}, {0, 3, 5, 6}, {4, 5, 6}],
    [{2, 4, 5, 6}, {0, 1, 7}, {0, 2, 7}, {1, 2, 7}, {0, 1, 2, 7}, {0, 3, 7}, {1, 3, 7}, {2, 3, 7}, {0, 2, 3, 7}, {1, 2, 3, 7}, {1, 4, 7}, {2, 4, 7}, {3, 4, 7}],
    [{1, 3, 4, 7}, {2, 3, 4, 7}, {1, 5, 7}, {2, 5, 7}, {1, 2, 5, 7}, {3, 5, 7}, {1, 3, 5, 7}, {0, 6, 7}, {1, 6, 7}, {0, 1, 6, 7}, {3, 6, 7}, {0, 3, 6, 7}, {1, 3, 6, 7}],
    [{4, 6, 7}, {1, 4, 6, 7}, {5, 6, 7}, {3, 5, 6, 7}, {0, 1, 8}, {1, 2, 8}, {0, 3, 8}, {1, 3, 8}, {2, 3, 8}, {1, 2, 3, 8}, {0, 4, 8}, {1, 4, 8}, {0, 1, 4, 8}],
    [{2, 4, 8}, {3, 4, 8}, {0, 3, 4, 8}, {1, 3, 4, 8}, {2, 3, 4, 8}, {0, 5, 8}, {2, 5, 8}, {3, 5, 8}, {0, 3, 5, 8}, {4, 5, 8}, {2, 4, 5, 8}, {3, 4, 5, 8}, {0, 6, 8}],
    [{2, 6, 8}, {3, 6, 8}, {0, 3, 6, 8}, {2, 3, 6, 8}, {4, 6, 8}, {0, 4, 6, 8}, {2, 4, 6, 8}, {0, 7, 8}, {1, 7, 8}, {0, 1, 7, 8}, {2, 7, 8}, {1, 2, 7, 8}, {4, 7, 8}],
    [{1, 4, 7, 8}, {2, 4, 7, 8}, {5, 7, 8}, {2, 5, 7, 8}, {6, 7, 8}, {0, 6, 7, 8}, {4, 6, 7, 8}, {0, 2, 9}, {1, 2, 9}, {2, 3, 9}, {0, 4, 9}, {1, 4, 9}, {2, 4, 9}],
    [{0, 2, 4, 9}, {3, 4, 9}, {2, 3, 4, 9}, {0, 5, 9}, {1, 5, 9}, {2, 5, 9}, {0, 2, 5, 9}, {1, 2, 5, 9}, {3, 5, 9}, {4, 5, 9}, {1, 4, 5, 9}, {2, 4, 5, 9}, {3, 4, 5, 9}],
    [{0, 6, 9}, {1, 6, 9}, {3, 6, 9}, {4, 6, 9}, {0, 4, 6, 9}, {1, 4, 6, 9}, {5, 6, 9}, {0, 5, 6, 9}, {3, 5, 6, 9}, {4, 5, 6, 9}, {0, 7, 9}, {1, 7, 9}, {3, 7, 9}],
    [{4, 7, 9}, {1, 4, 7, 9}, {3, 4, 7, 9}, {5, 7, 9}, {1, 5, 7, 9}, {3, 5, 7, 9}, {0, 8, 9}, {1, 8, 9}, {2, 8, 9}, {1, 2, 8, 9}, {3, 8, 9}, {2, 3, 8, 9}, {5, 8, 9}],
    [{0, 5, 8, 9}, {2, 5, 8, 9}, {3, 5, 8, 9}, {6, 8, 9}, {0, 6, 8, 9}, {3, 6, 8, 9}, {7, 8, 9}, {0, 7, 8, 9}, {1, 7, 8, 9}, {5, 7, 8, 9}, {0, 1, 10}, {0, 2, 10}, {0, 3, 10}],
    [{1, 3, 10}, {2, 3, 10}, {0, 2, 3, 10}, {0, 4, 10}, {3, 4, 10}, {0, 3, 4, 10}, {0, 5, 10}, {1, 5, 10}, {0, 1, 5, 10}, {2, 5, 10}, {0, 2, 5, 10}, {3, 5, 10}, {0, 3, 5, 10}],
    [{1, 3, 5, 10}, {4, 5, 10}, {3, 4, 5, 10}, {1, 6, 10}, {2, 6, 10}, {3, 6, 10}, {1, 3, 6, 10}, {2, 3, 6, 10}, {4, 6, 10}, {5, 6, 10}, {2, 5, 6, 10}, {3, 5, 6, 10}, {4, 5, 6, 10}],
    [{0, 7, 10}, {1, 7, 10}, {0, 1, 7, 10}, {2, 7, 10}, {0, 2, 7, 10}, {4, 7, 10}, {5, 7, 10}, {1, 5, 7, 10}, {2, 5, 7, 10}, {6, 7, 10}, {1, 6, 7, 10}, {4, 6, 7, 10}, {5, 6, 7, 10}],
    [{0, 8, 10}, {1, 8, 10}, {0, 1, 8, 10}, {2, 8, 10}, {4, 8, 10}, {0, 4, 8, 10}, {5, 8, 10}, {0, 5, 8, 10}, {2, 5, 8, 10}, {4, 5, 8, 10}, {6, 8, 10}, {2, 6, 8, 10}, {4, 6, 8, 10}],
    [{0, 9, 10}, {1, 9, 10}, {2, 9, 10}, {0, 2, 9, 10}, {3, 9, 10}, {2, 3, 9, 10}, {4, 9, 10}, {0, 4, 9, 10}, {3, 4, 9, 10}, {6, 9, 10}, {1, 6, 9, 10}, {3, 6, 9, 10}, {4, 6, 9, 10}],
    [{7, 9, 10}, {0, 7, 9, 10}, {1, 7, 9, 10}, {4, 7, 9, 10}, {8, 9, 10}, {0, 8, 9, 10}, {1, 8, 9, 10}, {2, 8, 9, 10}, {6, 8, 9, 10}, {0, 1, 11}, {0, 2, 11}, {1, 2, 11}, {0, 1, 2, 11}],
    [{0, 3, 11}, {1, 3, 11}, {0, 4, 11}, {1, 4, 11}, {0, 1, 4, 11}, {2, 4, 11}, {0, 2, 4, 11}, {3, 4, 11}, {0, 3, 4, 11}, {1, 3, 4, 11}, {0, 5, 11}, {1, 5, 11}, {0, 1, 5, 11}],
    [{4, 5, 11}, {1, 4, 5, 11}, {1, 6, 11}, {2, 6, 11}, {1, 2, 6, 11}, {3, 6, 11}, {1, 3, 6, 11}, {4, 6, 11}, {1, 4, 6, 11}, {2, 4, 6, 11}, {5, 6, 11}, {4, 5, 6, 11}, {0, 7, 11}],
    [{2, 7, 11}, {0, 2, 7, 11}, {3, 7, 11}, {0, 3, 7, 11}, {4, 7, 11}, {2, 4, 7, 11}, {3, 4, 7, 11}, {5, 7, 11}, {6, 7, 11}, {3, 6, 7, 11}, {4, 6, 7, 11}, {5, 6, 7, 11}, {0, 8, 11}],
    [{1, 8, 11}, {0, 1, 8, 11}, {2, 8, 11}, {1, 2, 8, 11}, {3, 8, 11}, {0, 3, 8, 11}, {1, 3, 8, 11}, {5, 8, 11}, {0, 5, 8, 11}, {6, 8, 11}, {2, 6, 8, 11}, {3, 6, 8, 11}, {7, 8, 11}],
    [{0, 7, 8, 11}, {2, 7, 8, 11}, {5, 7, 8, 11}, {6, 7, 8, 11}, {0, 9, 11}, {1, 9, 11}, {2, 9, 11}, {0, 2, 9, 11}, {1, 2, 9, 11}, {3, 9, 11}, {5, 9, 11}, {0, 5, 9, 11}, {1, 5, 9, 11}],
    [{6, 9, 11}, {1, 6, 9, 11}, {3, 6, 9, 11}, {5, 6, 9, 11}, {7, 9, 11}, {0, 7, 9, 11}, {3, 7, 9, 11}, {5, 7, 9, 11}, {1, 10, 11}, {2, 10, 11}, {3, 10, 11}, {1, 3, 10, 11}, {4, 10, 11}],
    [{3, 4, 10, 11}, {5, 10, 11}, {1, 5, 10, 11}, {4, 5, 10, 11}, {7, 10, 11}, {2, 7, 10, 11}, {4, 7, 10, 11}, {5, 7, 10, 11}, {8, 10, 11}, {1, 8, 10, 11}, {2, 8, 10, 11}, {5, 8, 10, 11}, {9, 10, 11}],
    [{1, 9, 10, 11}, {2, 9, 10, 11}, {3, 9, 10, 11}, {7, 9, 10, 11}, {0, 1, 12}, {1, 2, 12}, {0, 3, 12}, {1, 3, 12}, {2, 3, 12}, {1, 2, 3, 12}, {0, 4, 12}, {1, 4, 12}, {0, 1, 4, 12}],
    [{2, 4, 12}, {0, 5, 12}, {1, 5, 12}, {0, 1, 5, 12}, {2, 5, 12}, {1, 2, 5, 12}, {3, 5, 12}, {0, 3, 5, 12}, {1, 3, 5, 12}, {4, 5, 12}, {1, 4, 5, 12}, {2, 4, 5, 12}, {0, 6, 12}],
    [{1, 6, 12}, {0, 1, 6, 12}, {2, 6, 12}, {1, 2, 6, 12}, {5, 6, 12}, {0, 5, 6, 12}, {2, 5, 6, 12}, {0, 7, 12}, {2, 7, 12}, {3, 7, 12}, {0, 3, 7, 12}, {2, 3, 7, 12}, {4, 7, 12}],
    [{2, 4, 7, 12}, {5, 7, 12}, {2, 5, 7, 12}, {3, 5, 7, 12}, {6, 7, 12}, {0, 6, 7, 12}, {5, 6, 7, 12}, {1, 8, 12}, {3, 8, 12}, {1, 3, 8, 12}, {4, 8, 12}, {1, 4, 8, 12}, {5, 8, 12}],
    [{3, 5, 8, 12}, {4, 5, 8, 12}, {6, 8, 12}, {7, 8, 12}, {4, 7, 8, 12}, {5, 7, 8, 12}, {6, 7, 8, 12}, {0, 9, 12}, {1, 9, 12}, {2, 9, 12}, {1, 2, 9, 12}, {3, 9, 12}, {2, 3, 9, 12}],
    [{4, 9, 12}, {0, 4, 9, 12}, {1, 4, 9, 12}, {2, 4, 9, 12}, {6, 9, 12}, {0, 6, 9, 12}, {1, 6, 9, 12}, {7, 9, 12}, {0, 7, 9, 12}, {3, 7, 9, 12}, {4, 7, 9, 12}, {8, 9, 12}, {1, 8, 9, 12}],
    [{3, 8, 9, 12}, {6, 8, 9, 12}, {7, 8, 9, 12}, {0, 10, 12}, {1, 10, 12}, {0, 1, 10, 12}, {2, 10, 12}, {3, 10, 12}, {0, 3, 10, 12}, {1, 3, 10, 12}, {2, 3, 10, 12}, {4, 10, 12}, {0, 4, 10, 12}],
    [{6, 10, 12}, {1, 6, 10, 12}, {2, 6, 10, 12}, {7, 10, 12}, {0, 7, 10, 12}, {2, 7, 10, 12}, {4, 7, 10, 12}, {6, 7, 10, 12}, {8, 10, 12}, {1, 8, 10, 12}, {4, 8, 10, 12}, {6, 8, 10, 12}, {0, 11, 12}],
    [{2, 11, 12}, {3, 11, 12}, {0, 3, 11, 12}, {4, 11, 12}, {0, 4, 11, 12}, {2, 4, 11, 12}, {5, 11, 12}, {0, 5, 11, 12}, {4, 5, 11, 12}, {6, 11, 12}, {2, 6, 11, 12}, {5, 6, 11, 12}, {8, 11, 12}],
    [{3, 8, 11, 12}, {5, 8, 11, 12}, {6, 8, 11, 12}, {9, 11, 12}, {0, 9, 11, 12}, {2, 9, 11, 12}, {3, 9, 11, 12}, {6, 9, 11, 12}, {10, 11, 12}, {2, 10, 11, 12}, {3, 10, 11, 12}, {4, 10, 11, 12}, {8, 10, 11, 12}]] : List (List (Finset (Fin 13)))).getD a.1.val []).getD a.2.val ∅)

def row (a : R) (v : Fin 26) : Bool :=
  decide (v.val ∈ (([
    [[0, 1, 2, 16, 20, 21, 22], [0, 2, 3, 18, 21, 22, 24], [1, 2, 3, 17, 21, 22, 23], [0, 1, 4, 15, 19, 20, 22], [0, 2, 4, 18, 20, 22, 24], [0, 3, 4, 18, 19, 22, 24], [1, 3, 4, 19, 22, 23, 25], [2, 3, 4, 18, 22, 23, 24], [0, 2, 3, 4, 18, 22, 24], [0, 1, 5, 16, 19, 20, 21], [0, 2, 5, 16, 20, 21, 24], [1, 2, 5, 16, 20, 21, 23], [0, 1, 2, 5, 16, 20, 21]],
    [[0, 3, 5, 14, 19, 21, 24], [1, 3, 5, 19, 21, 23, 25], [1, 4, 5, 19, 20, 23, 25], [2, 4, 5, 13, 20, 23, 24], [3, 4, 5, 19, 23, 24, 25], [1, 3, 4, 5, 19, 23, 25], [0, 1, 6, 15, 20, 21, 22], [0, 2, 6, 20, 21, 22, 24], [1, 2, 6, 17, 20, 21, 22], [0, 1, 2, 6, 20, 21, 22], [0, 3, 6, 14, 21, 22, 24], [1, 3, 6, 17, 21, 22, 25], [2, 3, 6, 17, 21, 22, 24]],
    [[0, 2, 3, 6, 21, 22, 24], [1, 2, 3, 6, 17, 21, 22], [0, 4, 6, 15, 20, 22, 24], [1, 4, 6, 15, 20, 22, 25], [0, 1, 4, 6, 15, 20, 22], [2, 4, 6, 13, 20, 22, 24], [0, 2, 4, 6, 20, 22, 24], [0, 5, 6, 14, 20, 21, 24], [2, 5, 6, 13, 20, 21, 24], [0, 2, 5, 6, 20, 21, 24], [3, 5, 6, 14, 21, 24, 25], [0, 3, 5, 6, 14, 21, 24], [4, 5, 6, 13, 20, 24, 25]],
    [[2, 4, 5, 6, 13, 20, 24], [0, 1, 7, 15, 16, 21, 22], [0, 2, 7, 16, 18, 21, 22], [1, 2, 7, 16, 21, 22, 23], [0, 1, 2, 7, 16, 21, 22], [0, 3, 7, 14, 18, 21, 22], [1, 3, 7, 21, 22, 23, 25], [2, 3, 7, 18, 21, 22, 23], [0, 2, 3, 7, 18, 21, 22], [1, 2, 3, 7, 21, 22, 23], [1, 4, 7, 15, 22, 23, 25], [2, 4, 7, 13, 18, 22, 23], [3, 4, 7, 18, 22, 23, 25]],
    [[1, 3, 4, 7, 22, 23, 25], [2, 3, 4, 7, 18, 22, 23], [1, 5, 7, 16, 21, 23, 25], [2, 5, 7, 13, 16, 21, 23], [1, 2, 5, 7, 16, 21, 23], [3, 5, 7, 14, 21, 23, 25], [1, 3, 5, 7, 21, 23, 25], [0, 6, 7, 14, 15, 21, 22], [1, 6, 7, 15, 21, 22, 25], [0, 1, 6, 7, 15, 21, 22], [3, 6, 7, 14, 21, 22, 25], [0, 3, 6, 7, 14, 21, 22], [1, 3, 6, 7, 21, 22, 25]],
    [[4, 6, 7, 13, 15, 22, 25], [1, 4, 6, 7, 15, 22, 25], [5, 6, 7, 13, 14, 21, 25], [3, 5, 6, 7, 14, 21, 25], [0, 1, 8, 15, 16, 19, 22], [1, 2, 8, 16, 17, 22, 23], [0, 3, 8, 14, 19, 22, 24], [1, 3, 8, 17, 19, 22, 23], [2, 3, 8, 17, 22, 23, 24], [1, 2, 3, 8, 17, 22, 23], [0, 4, 8, 15, 19, 22, 24], [1, 4, 8, 15, 19, 22, 23], [0, 1, 4, 8, 15, 19, 22]],
    [[2, 4, 8, 13, 22, 23, 24], [3, 4, 8, 19, 22, 23, 24], [0, 3, 4, 8, 19, 22, 24], [1, 3, 4, 8, 19, 22, 23], [2, 3, 4, 8, 22, 23, 24], [0, 5, 8, 14, 16, 19, 24], [2, 5, 8, 13, 16, 23, 24], [3, 5, 8, 14, 19, 23, 24], [0, 3, 5, 8, 14, 19, 24], [4, 5, 8, 13, 19, 23, 24], [2, 4, 5, 8, 13, 23, 24], [3, 4, 5, 8, 19, 23, 24], [0, 6, 8, 14, 15, 22, 24]],
    [[2, 6, 8, 13, 17, 22, 24], [3, 6, 8, 14, 17, 22, 24], [0, 3, 6, 8, 14, 22, 24], [2, 3, 6, 8, 17, 22, 24], [4, 6, 8, 13, 15, 22, 24], [0, 4, 6, 8, 15, 22, 24], [2, 4, 6, 8, 13, 22, 24], [0, 7, 8, 14, 15, 16, 22], [1, 7, 8, 15, 16, 22, 23], [0, 1, 7, 8, 15, 16, 22], [2, 7, 8, 13, 16, 22, 23], [1, 2, 7, 8, 16, 22, 23], [4, 7, 8, 13, 15, 22, 23]],
    [[1, 4, 7, 8, 15, 22, 23], [2, 4, 7, 8, 13, 22, 23], [5, 7, 8, 13, 14, 16, 23], [2, 5, 7, 8, 13, 16, 23], [6, 7, 8, 13, 14, 15, 22], [0, 6, 7, 8, 14, 15, 22], [4, 6, 7, 8, 13, 15, 22], [0, 2, 9, 16, 18, 20, 24], [1, 2, 9, 16, 17, 20, 23], [2, 3, 9, 17, 18, 23, 24], [0, 4, 9, 15, 18, 20, 24], [1, 4, 9, 15, 20, 23, 25], [2, 4, 9, 18, 20, 23, 24]],
    [[0, 2, 4, 9, 18, 20, 24], [3, 4, 9, 18, 23, 24, 25], [2, 3, 4, 9, 18, 23, 24], [0, 5, 9, 14, 16, 20, 24], [1, 5, 9, 16, 20, 23, 25], [2, 5, 9, 16, 20, 23, 24], [0, 2, 5, 9, 16, 20, 24], [1, 2, 5, 9, 16, 20, 23], [3, 5, 9, 14, 23, 24, 25], [4, 5, 9, 20, 23, 24, 25], [1, 4, 5, 9, 20, 23, 25], [2, 4, 5, 9, 20, 23, 24], [3, 4, 5, 9, 23, 24, 25]],
    [[0, 6, 9, 14, 15, 20, 24], [1, 6, 9, 15, 17, 20, 25], [3, 6, 9, 14, 17, 24, 25], [4, 6, 9, 15, 20, 24, 25], [0, 4, 6, 9, 15, 20, 24], [1, 4, 6, 9, 15, 20, 25], [5, 6, 9, 14, 20, 24, 25], [0, 5, 6, 9, 14, 20, 24], [3, 5, 6, 9, 14, 24, 25], [4, 5, 6, 9, 20, 24, 25], [0, 7, 9, 14, 15, 16, 18], [1, 7, 9, 15, 16, 23, 25], [3, 7, 9, 14, 18, 23, 25]],
    [[4, 7, 9, 15, 18, 23, 25], [1, 4, 7, 9, 15, 23, 25], [3, 4, 7, 9, 18, 23, 25], [5, 7, 9, 14, 16, 23, 25], [1, 5, 7, 9, 16, 23, 25], [3, 5, 7, 9, 14, 23, 25], [0, 8, 9, 14, 15, 16, 24], [1, 8, 9, 15, 16, 17, 23], [2, 8, 9, 16, 17, 23, 24], [1, 2, 8, 9, 16, 17, 23], [3, 8, 9, 14, 17, 23, 24], [2, 3, 8, 9, 17, 23, 24], [5, 8, 9, 14, 16, 23, 24]],
    [[0, 5, 8, 9, 14, 16, 24], [2, 5, 8, 9, 16, 23, 24], [3, 5, 8, 9, 14, 23, 24], [6, 8, 9, 14, 15, 17, 24], [0, 6, 8, 9, 14, 15, 24], [3, 6, 8, 9, 14, 17, 24], [7, 8, 9, 14, 15, 16, 23], [0, 7, 8, 9, 14, 15, 16], [1, 7, 8, 9, 15, 16, 23], [5, 7, 8, 9, 14, 16, 23], [0, 1, 10, 15, 16, 19, 21], [0, 2, 10, 16, 18, 21, 24], [0, 3, 10, 18, 19, 21, 24]],
    [[1, 3, 10, 17, 19, 21, 25], [2, 3, 10, 17, 18, 21, 24], [0, 2, 3, 10, 18, 21, 24], [0, 4, 10, 15, 18, 19, 24], [3, 4, 10, 18, 19, 24, 25], [0, 3, 4, 10, 18, 19, 24], [0, 5, 10, 16, 19, 21, 24], [1, 5, 10, 16, 19, 21, 25], [0, 1, 5, 10, 16, 19, 21], [2, 5, 10, 13, 16, 21, 24], [0, 2, 5, 10, 16, 21, 24], [3, 5, 10, 19, 21, 24, 25], [0, 3, 5, 10, 19, 21, 24]],
    [[1, 3, 5, 10, 19, 21, 25], [4, 5, 10, 13, 19, 24, 25], [3, 4, 5, 10, 19, 24, 25], [1, 6, 10, 15, 17, 21, 25], [2, 6, 10, 13, 17, 21, 24], [3, 6, 10, 17, 21, 24, 25], [1, 3, 6, 10, 17, 21, 25], [2, 3, 6, 10, 17, 21, 24], [4, 6, 10, 13, 15, 24, 25], [5, 6, 10, 13, 21, 24, 25], [2, 5, 6, 10, 13, 21, 24], [3, 5, 6, 10, 21, 24, 25], [4, 5, 6, 10, 13, 24, 25]],
    [[0, 7, 10, 15, 16, 18, 21], [1, 7, 10, 15, 16, 21, 25], [0, 1, 7, 10, 15, 16, 21], [2, 7, 10, 13, 16, 18, 21], [0, 2, 7, 10, 16, 18, 21], [4, 7, 10, 13, 15, 18, 25], [5, 7, 10, 13, 16, 21, 25], [1, 5, 7, 10, 16, 21, 25], [2, 5, 7, 10, 13, 16, 21], [6, 7, 10, 13, 15, 21, 25], [1, 6, 7, 10, 15, 21, 25], [4, 6, 7, 10, 13, 15, 25], [5, 6, 7, 10, 13, 21, 25]],
    [[0, 8, 10, 15, 16, 19, 24], [1, 8, 10, 15, 16, 17, 19], [0, 1, 8, 10, 15, 16, 19], [2, 8, 10, 13, 16, 17, 24], [4, 8, 10, 13, 15, 19, 24], [0, 4, 8, 10, 15, 19, 24], [5, 8, 10, 13, 16, 19, 24], [0, 5, 8, 10, 16, 19, 24], [2, 5, 8, 10, 13, 16, 24], [4, 5, 8, 10, 13, 19, 24], [6, 8, 10, 13, 15, 17, 24], [2, 6, 8, 10, 13, 17, 24], [4, 6, 8, 10, 13, 15, 24]],
    [[0, 9, 10, 15, 16, 18, 24], [1, 9, 10, 15, 16, 17, 25], [2, 9, 10, 16, 17, 18, 24], [0, 2, 9, 10, 16, 18, 24], [3, 9, 10, 17, 18, 24, 25], [2, 3, 9, 10, 17, 18, 24], [4, 9, 10, 15, 18, 24, 25], [0, 4, 9, 10, 15, 18, 24], [3, 4, 9, 10, 18, 24, 25], [6, 9, 10, 15, 17, 24, 25], [1, 6, 9, 10, 15, 17, 25], [3, 6, 9, 10, 17, 24, 25], [4, 6, 9, 10, 15, 24, 25]],
    [[7, 9, 10, 15, 16, 18, 25], [0, 7, 9, 10, 15, 16, 18], [1, 7, 9, 10, 15, 16, 25], [4, 7, 9, 10, 15, 18, 25], [8, 9, 10, 15, 16, 17, 24], [0, 8, 9, 10, 15, 16, 24], [1, 8, 9, 10, 15, 16, 17], [2, 8, 9, 10, 16, 17, 24], [6, 8, 9, 10, 15, 17, 24], [0, 1, 11, 16, 19, 20, 22], [0, 2, 11, 16, 18, 20, 22], [1, 2, 11, 16, 17, 20, 22], [0, 1, 2, 11, 16, 20, 22]],
    [[0, 3, 11, 14, 18, 19, 22], [1, 3, 11, 17, 19, 22, 25], [0, 4, 11, 18, 19, 20, 22], [1, 4, 11, 19, 20, 22, 25], [0, 1, 4, 11, 19, 20, 22], [2, 4, 11, 13, 18, 20, 22], [0, 2, 4, 11, 18, 20, 22], [3, 4, 11, 18, 19, 22, 25], [0, 3, 4, 11, 18, 19, 22], [1, 3, 4, 11, 19, 22, 25], [0, 5, 11, 14, 16, 19, 20], [1, 5, 11, 16, 19, 20, 25], [0, 1, 5, 11, 16, 19, 20]],
    [[4, 5, 11, 13, 19, 20, 25], [1, 4, 5, 11, 19, 20, 25], [1, 6, 11, 17, 20, 22, 25], [2, 6, 11, 13, 17, 20, 22], [1, 2, 6, 11, 17, 20, 22], [3, 6, 11, 14, 17, 22, 25], [1, 3, 6, 11, 17, 22, 25], [4, 6, 11, 13, 20, 22, 25], [1, 4, 6, 11, 20, 22, 25], [2, 4, 6, 11, 13, 20, 22], [5, 6, 11, 13, 14, 20, 25], [4, 5, 6, 11, 13, 20, 25], [0, 7, 11, 14, 16, 18, 22]],
    [[2, 7, 11, 13, 16, 18, 22], [0, 2, 7, 11, 16, 18, 22], [3, 7, 11, 14, 18, 22, 25], [0, 3, 7, 11, 14, 18, 22], [4, 7, 11, 13, 18, 22, 25], [2, 4, 7, 11, 13, 18, 22], [3, 4, 7, 11, 18, 22, 25], [5, 7, 11, 13, 14, 16, 25], [6, 7, 11, 13, 14, 22, 25], [3, 6, 7, 11, 14, 22, 25], [4, 6, 7, 11, 13, 22, 25], [5, 6, 7, 11, 13, 14, 25], [0, 8, 11, 14, 16, 19, 22]],
    [[1, 8, 11, 16, 17, 19, 22], [0, 1, 8, 11, 16, 19, 22], [2, 8, 11, 13, 16, 17, 22], [1, 2, 8, 11, 16, 17, 22], [3, 8, 11, 14, 17, 19, 22], [0, 3, 8, 11, 14, 19, 22], [1, 3, 8, 11, 17, 19, 22], [5, 8, 11, 13, 14, 16, 19], [0, 5, 8, 11, 14, 16, 19], [6, 8, 11, 13, 14, 17, 22], [2, 6, 8, 11, 13, 17, 22], [3, 6, 8, 11, 14, 17, 22], [7, 8, 11, 13, 14, 16, 22]],
    [[0, 7, 8, 11, 14, 16, 22], [2, 7, 8, 11, 13, 16, 22], [5, 7, 8, 11, 13, 14, 16], [6, 7, 8, 11, 13, 14, 22], [0, 9, 11, 14, 16, 18, 20], [1, 9, 11, 16, 17, 20, 25], [2, 9, 11, 16, 17, 18, 20], [0, 2, 9, 11, 16, 18, 20], [1, 2, 9, 11, 16, 17, 20], [3, 9, 11, 14, 17, 18, 25], [5, 9, 11, 14, 16, 20, 25], [0, 5, 9, 11, 14, 16, 20], [1, 5, 9, 11, 16, 20, 25]],
    [[6, 9, 11, 14, 17, 20, 25], [1, 6, 9, 11, 17, 20, 25], [3, 6, 9, 11, 14, 17, 25], [5, 6, 9, 11, 14, 20, 25], [7, 9, 11, 14, 16, 18, 25], [0, 7, 9, 11, 14, 16, 18], [3, 7, 9, 11, 14, 18, 25], [5, 7, 9, 11, 14, 16, 25], [1, 10, 11, 16, 17, 19, 25], [2, 10, 11, 13, 16, 17, 18], [3, 10, 11, 17, 18, 19, 25], [1, 3, 10, 11, 17, 19, 25], [4, 10, 11, 13, 18, 19, 25]],
    [[3, 4, 10, 11, 18, 19, 25], [5, 10, 11, 13, 16, 19, 25], [1, 5, 10, 11, 16, 19, 25], [4, 5, 10, 11, 13, 19, 25], [7, 10, 11, 13, 16, 18, 25], [2, 7, 10, 11, 13, 16, 18], [4, 7, 10, 11, 13, 18, 25], [5, 7, 10, 11, 13, 16, 25], [8, 10, 11, 13, 16, 17, 19], [1, 8, 10, 11, 16, 17, 19], [2, 8, 10, 11, 13, 16, 17], [5, 8, 10, 11, 13, 16, 19], [9, 10, 11, 16, 17, 18, 25]],
    [[1, 9, 10, 11, 16, 17, 25], [2, 9, 10, 11, 16, 17, 18], [3, 9, 10, 11, 17, 18, 25], [7, 9, 10, 11, 16, 18, 25], [0, 1, 12, 15, 19, 20, 21], [1, 2, 12, 17, 20, 21, 23], [0, 3, 12, 14, 18, 19, 21], [1, 3, 12, 17, 19, 21, 23], [2, 3, 12, 17, 18, 21, 23], [1, 2, 3, 12, 17, 21, 23], [0, 4, 12, 15, 18, 19, 20], [1, 4, 12, 15, 19, 20, 23], [0, 1, 4, 12, 15, 19, 20]],
    [[2, 4, 12, 13, 18, 20, 23], [0, 5, 12, 14, 19, 20, 21], [1, 5, 12, 19, 20, 21, 23], [0, 1, 5, 12, 19, 20, 21], [2, 5, 12, 13, 20, 21, 23], [1, 2, 5, 12, 20, 21, 23], [3, 5, 12, 14, 19, 21, 23], [0, 3, 5, 12, 14, 19, 21], [1, 3, 5, 12, 19, 21, 23], [4, 5, 12, 13, 19, 20, 23], [1, 4, 5, 12, 19, 20, 23], [2, 4, 5, 12, 13, 20, 23], [0, 6, 12, 14, 15, 20, 21]],
    [[1, 6, 12, 15, 17, 20, 21], [0, 1, 6, 12, 15, 20, 21], [2, 6, 12, 13, 17, 20, 21], [1, 2, 6, 12, 17, 20, 21], [5, 6, 12, 13, 14, 20, 21], [0, 5, 6, 12, 14, 20, 21], [2, 5, 6, 12, 13, 20, 21], [0, 7, 12, 14, 15, 18, 21], [2, 7, 12, 13, 18, 21, 23], [3, 7, 12, 14, 18, 21, 23], [0, 3, 7, 12, 14, 18, 21], [2, 3, 7, 12, 18, 21, 23], [4, 7, 12, 13, 15, 18, 23]],
    [[2, 4, 7, 12, 13, 18, 23], [5, 7, 12, 13, 14, 21, 23], [2, 5, 7, 12, 13, 21, 23], [3, 5, 7, 12, 14, 21, 23], [6, 7, 12, 13, 14, 15, 21], [0, 6, 7, 12, 14, 15, 21], [5, 6, 7, 12, 13, 14, 21], [1, 8, 12, 15, 17, 19, 23], [3, 8, 12, 14, 17, 19, 23], [1, 3, 8, 12, 17, 19, 23], [4, 8, 12, 13, 15, 19, 23], [1, 4, 8, 12, 15, 19, 23], [5, 8, 12, 13, 14, 19, 23]],
    [[3, 5, 8, 12, 14, 19, 23], [4, 5, 8, 12, 13, 19, 23], [6, 8, 12, 13, 14, 15, 17], [7, 8, 12, 13, 14, 15, 23], [4, 7, 8, 12, 13, 15, 23], [5, 7, 8, 12, 13, 14, 23], [6, 7, 8, 12, 13, 14, 15], [0, 9, 12, 14, 15, 18, 20], [1, 9, 12, 15, 17, 20, 23], [2, 9, 12, 17, 18, 20, 23], [1, 2, 9, 12, 17, 20, 23], [3, 9, 12, 14, 17, 18, 23], [2, 3, 9, 12, 17, 18, 23]],
    [[4, 9, 12, 15, 18, 20, 23], [0, 4, 9, 12, 15, 18, 20], [1, 4, 9, 12, 15, 20, 23], [2, 4, 9, 12, 18, 20, 23], [6, 9, 12, 14, 15, 17, 20], [0, 6, 9, 12, 14, 15, 20], [1, 6, 9, 12, 15, 17, 20], [7, 9, 12, 14, 15, 18, 23], [0, 7, 9, 12, 14, 15, 18], [3, 7, 9, 12, 14, 18, 23], [4, 7, 9, 12, 15, 18, 23], [8, 9, 12, 14, 15, 17, 23], [1, 8, 9, 12, 15, 17, 23]],
    [[3, 8, 9, 12, 14, 17, 23], [6, 8, 9, 12, 14, 15, 17], [7, 8, 9, 12, 14, 15, 23], [0, 10, 12, 15, 18, 19, 21], [1, 10, 12, 15, 17, 19, 21], [0, 1, 10, 12, 15, 19, 21], [2, 10, 12, 13, 17, 18, 21], [3, 10, 12, 17, 18, 19, 21], [0, 3, 10, 12, 18, 19, 21], [1, 3, 10, 12, 17, 19, 21], [2, 3, 10, 12, 17, 18, 21], [4, 10, 12, 13, 15, 18, 19], [0, 4, 10, 12, 15, 18, 19]],
    [[6, 10, 12, 13, 15, 17, 21], [1, 6, 10, 12, 15, 17, 21], [2, 6, 10, 12, 13, 17, 21], [7, 10, 12, 13, 15, 18, 21], [0, 7, 10, 12, 15, 18, 21], [2, 7, 10, 12, 13, 18, 21], [4, 7, 10, 12, 13, 15, 18], [6, 7, 10, 12, 13, 15, 21], [8, 10, 12, 13, 15, 17, 19], [1, 8, 10, 12, 15, 17, 19], [4, 8, 10, 12, 13, 15, 19], [6, 8, 10, 12, 13, 15, 17], [0, 11, 12, 14, 18, 19, 20]],
    [[2, 11, 12, 13, 17, 18, 20], [3, 11, 12, 14, 17, 18, 19], [0, 3, 11, 12, 14, 18, 19], [4, 11, 12, 13, 18, 19, 20], [0, 4, 11, 12, 18, 19, 20], [2, 4, 11, 12, 13, 18, 20], [5, 11, 12, 13, 14, 19, 20], [0, 5, 11, 12, 14, 19, 20], [4, 5, 11, 12, 13, 19, 20], [6, 11, 12, 13, 14, 17, 20], [2, 6, 11, 12, 13, 17, 20], [5, 6, 11, 12, 13, 14, 20], [8, 11, 12, 13, 14, 17, 19]],
    [[3, 8, 11, 12, 14, 17, 19], [5, 8, 11, 12, 13, 14, 19], [6, 8, 11, 12, 13, 14, 17], [9, 11, 12, 14, 17, 18, 20], [0, 9, 11, 12, 14, 18, 20], [2, 9, 11, 12, 17, 18, 20], [3, 9, 11, 12, 14, 17, 18], [6, 9, 11, 12, 14, 17, 20], [10, 11, 12, 13, 17, 18, 19], [2, 10, 11, 12, 13, 17, 18], [3, 10, 11, 12, 17, 18, 19], [4, 10, 11, 12, 13, 18, 19], [8, 10, 11, 12, 13, 17, 19]]] : List (List (List ℕ))).getD a.1.val []).getD a.2.val [])

def rowInput (X : Finset (Fin 13)) (v : Fin 26) : Bool :=
  decide ((∃ p ∈ X, v = Fin.castAdd 13 p) ∨
    ∃ l : Fin 13, v = Fin.natAdd 13 l ∧ ∀ p ∈ X, ¬incidence p l)

def admissible (X : Finset (Fin 13)) : Prop :=
  (∀ p ∉ X, ∃ l : Fin 13, (∀ q ∈ X, ¬incidence q l) ∧ incidence p l) ∧
  (¬∃ l : Fin 13, ∀ p ∈ X, incidence p l) ∧
  ¬∃ p : Fin 13, ∀ l : Fin 13, (∀ q ∈ X, ¬incidence q l) → incidence p l

def missing (a : R) : Finset (Fin 26) := Finset.univ.filter fun v => row a v = false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma admissible_0 : ∀ i : Fin 13, admissible (points (0, i)) := by
  unfold admissible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma admissible_1 : ∀ i : Fin 13, admissible (points (1, i)) := by
  unfold admissible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma admissible_2 : ∀ i : Fin 13, admissible (points (2, i)) := by
  unfold admissible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma admissible_3 : ∀ i : Fin 13, admissible (points (3, i)) := by
  unfold admissible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma admissible_4 : ∀ i : Fin 13, admissible (points (4, i)) := by
  unfold admissible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma admissible_5 : ∀ i : Fin 13, admissible (points (5, i)) := by
  unfold admissible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma admissible_6 : ∀ i : Fin 13, admissible (points (6, i)) := by
  unfold admissible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma admissible_7 : ∀ i : Fin 13, admissible (points (7, i)) := by
  unfold admissible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma admissible_8 : ∀ i : Fin 13, admissible (points (8, i)) := by
  unfold admissible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma admissible_9 : ∀ i : Fin 13, admissible (points (9, i)) := by
  unfold admissible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma admissible_10 : ∀ i : Fin 13, admissible (points (10, i)) := by
  unfold admissible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma admissible_11 : ∀ i : Fin 13, admissible (points (11, i)) := by
  unfold admissible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma admissible_12 : ∀ i : Fin 13, admissible (points (12, i)) := by
  unfold admissible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma admissible_13 : ∀ i : Fin 13, admissible (points (13, i)) := by
  unfold admissible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma admissible_14 : ∀ i : Fin 13, admissible (points (14, i)) := by
  unfold admissible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma admissible_15 : ∀ i : Fin 13, admissible (points (15, i)) := by
  unfold admissible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma admissible_16 : ∀ i : Fin 13, admissible (points (16, i)) := by
  unfold admissible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma admissible_17 : ∀ i : Fin 13, admissible (points (17, i)) := by
  unfold admissible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma admissible_18 : ∀ i : Fin 13, admissible (points (18, i)) := by
  unfold admissible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma admissible_19 : ∀ i : Fin 13, admissible (points (19, i)) := by
  unfold admissible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma admissible_20 : ∀ i : Fin 13, admissible (points (20, i)) := by
  unfold admissible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma admissible_21 : ∀ i : Fin 13, admissible (points (21, i)) := by
  unfold admissible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma admissible_22 : ∀ i : Fin 13, admissible (points (22, i)) := by
  unfold admissible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma admissible_23 : ∀ i : Fin 13, admissible (points (23, i)) := by
  unfold admissible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma admissible_24 : ∀ i : Fin 13, admissible (points (24, i)) := by
  unfold admissible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma admissible_25 : ∀ i : Fin 13, admissible (points (25, i)) := by
  unfold admissible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma admissible_26 : ∀ i : Fin 13, admissible (points (26, i)) := by
  unfold admissible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma admissible_27 : ∀ i : Fin 13, admissible (points (27, i)) := by
  unfold admissible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma admissible_28 : ∀ i : Fin 13, admissible (points (28, i)) := by
  unfold admissible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma admissible_29 : ∀ i : Fin 13, admissible (points (29, i)) := by
  unfold admissible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma admissible_30 : ∀ i : Fin 13, admissible (points (30, i)) := by
  unfold admissible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma admissible_31 : ∀ i : Fin 13, admissible (points (31, i)) := by
  unfold admissible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma admissible_32 : ∀ i : Fin 13, admissible (points (32, i)) := by
  unfold admissible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma admissible_33 : ∀ i : Fin 13, admissible (points (33, i)) := by
  unfold admissible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma admissible_34 : ∀ i : Fin 13, admissible (points (34, i)) := by
  unfold admissible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma admissible_35 : ∀ i : Fin 13, admissible (points (35, i)) := by
  unfold admissible
  decide +kernel

lemma rows_admissible : ∀ r : R, admissible (points r) := by
  have h : ∀ g : Fin 36, ∀ i : Fin 13, admissible (points (g, i)) := by
    exact (Fin.cases admissible_0 (Fin.cases admissible_1 (Fin.cases admissible_2 (Fin.cases admissible_3 (Fin.cases admissible_4 (Fin.cases admissible_5 (Fin.cases admissible_6 (Fin.cases admissible_7 (Fin.cases admissible_8 (Fin.cases admissible_9 (Fin.cases admissible_10 (Fin.cases admissible_11 (Fin.cases admissible_12 (Fin.cases admissible_13 (Fin.cases admissible_14 (Fin.cases admissible_15 (Fin.cases admissible_16 (Fin.cases admissible_17 (Fin.cases admissible_18 (Fin.cases admissible_19 (Fin.cases admissible_20 (Fin.cases admissible_21 (Fin.cases admissible_22 (Fin.cases admissible_23 (Fin.cases admissible_24 (Fin.cases admissible_25 (Fin.cases admissible_26 (Fin.cases admissible_27 (Fin.cases admissible_28 (Fin.cases admissible_29 (Fin.cases admissible_30 (Fin.cases admissible_31 (Fin.cases admissible_32 (Fin.cases admissible_33 (Fin.cases admissible_34 (Fin.cases admissible_35 (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))
  rintro ⟨g, i⟩
  exact h g i

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma row_eq_0 : ∀ i : Fin 13, row (0, i) = rowInput (points (0, i)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma row_eq_1 : ∀ i : Fin 13, row (1, i) = rowInput (points (1, i)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma row_eq_2 : ∀ i : Fin 13, row (2, i) = rowInput (points (2, i)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma row_eq_3 : ∀ i : Fin 13, row (3, i) = rowInput (points (3, i)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma row_eq_4 : ∀ i : Fin 13, row (4, i) = rowInput (points (4, i)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma row_eq_5 : ∀ i : Fin 13, row (5, i) = rowInput (points (5, i)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma row_eq_6 : ∀ i : Fin 13, row (6, i) = rowInput (points (6, i)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma row_eq_7 : ∀ i : Fin 13, row (7, i) = rowInput (points (7, i)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma row_eq_8 : ∀ i : Fin 13, row (8, i) = rowInput (points (8, i)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma row_eq_9 : ∀ i : Fin 13, row (9, i) = rowInput (points (9, i)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma row_eq_10 : ∀ i : Fin 13, row (10, i) = rowInput (points (10, i)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma row_eq_11 : ∀ i : Fin 13, row (11, i) = rowInput (points (11, i)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma row_eq_12 : ∀ i : Fin 13, row (12, i) = rowInput (points (12, i)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma row_eq_13 : ∀ i : Fin 13, row (13, i) = rowInput (points (13, i)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma row_eq_14 : ∀ i : Fin 13, row (14, i) = rowInput (points (14, i)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma row_eq_15 : ∀ i : Fin 13, row (15, i) = rowInput (points (15, i)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma row_eq_16 : ∀ i : Fin 13, row (16, i) = rowInput (points (16, i)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma row_eq_17 : ∀ i : Fin 13, row (17, i) = rowInput (points (17, i)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma row_eq_18 : ∀ i : Fin 13, row (18, i) = rowInput (points (18, i)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma row_eq_19 : ∀ i : Fin 13, row (19, i) = rowInput (points (19, i)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma row_eq_20 : ∀ i : Fin 13, row (20, i) = rowInput (points (20, i)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma row_eq_21 : ∀ i : Fin 13, row (21, i) = rowInput (points (21, i)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma row_eq_22 : ∀ i : Fin 13, row (22, i) = rowInput (points (22, i)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma row_eq_23 : ∀ i : Fin 13, row (23, i) = rowInput (points (23, i)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma row_eq_24 : ∀ i : Fin 13, row (24, i) = rowInput (points (24, i)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma row_eq_25 : ∀ i : Fin 13, row (25, i) = rowInput (points (25, i)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma row_eq_26 : ∀ i : Fin 13, row (26, i) = rowInput (points (26, i)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma row_eq_27 : ∀ i : Fin 13, row (27, i) = rowInput (points (27, i)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma row_eq_28 : ∀ i : Fin 13, row (28, i) = rowInput (points (28, i)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma row_eq_29 : ∀ i : Fin 13, row (29, i) = rowInput (points (29, i)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma row_eq_30 : ∀ i : Fin 13, row (30, i) = rowInput (points (30, i)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma row_eq_31 : ∀ i : Fin 13, row (31, i) = rowInput (points (31, i)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma row_eq_32 : ∀ i : Fin 13, row (32, i) = rowInput (points (32, i)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma row_eq_33 : ∀ i : Fin 13, row (33, i) = rowInput (points (33, i)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma row_eq_34 : ∀ i : Fin 13, row (34, i) = rowInput (points (34, i)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma row_eq_35 : ∀ i : Fin 13, row (35, i) = rowInput (points (35, i)) := by
  decide +kernel

lemma row_eq : ∀ r : R, row r = rowInput (points r) := by
  have h : ∀ g : Fin 36, ∀ i : Fin 13, row (g, i) = rowInput (points (g, i)) := by
    exact (Fin.cases row_eq_0 (Fin.cases row_eq_1 (Fin.cases row_eq_2 (Fin.cases row_eq_3 (Fin.cases row_eq_4 (Fin.cases row_eq_5 (Fin.cases row_eq_6 (Fin.cases row_eq_7 (Fin.cases row_eq_8 (Fin.cases row_eq_9 (Fin.cases row_eq_10 (Fin.cases row_eq_11 (Fin.cases row_eq_12 (Fin.cases row_eq_13 (Fin.cases row_eq_14 (Fin.cases row_eq_15 (Fin.cases row_eq_16 (Fin.cases row_eq_17 (Fin.cases row_eq_18 (Fin.cases row_eq_19 (Fin.cases row_eq_20 (Fin.cases row_eq_21 (Fin.cases row_eq_22 (Fin.cases row_eq_23 (Fin.cases row_eq_24 (Fin.cases row_eq_25 (Fin.cases row_eq_26 (Fin.cases row_eq_27 (Fin.cases row_eq_28 (Fin.cases row_eq_29 (Fin.cases row_eq_30 (Fin.cases row_eq_31 (Fin.cases row_eq_32 (Fin.cases row_eq_33 (Fin.cases row_eq_34 (Fin.cases row_eq_35 (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))
  rintro ⟨g, i⟩
  exact h g i

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma missing_0 : ∀ i : Fin 13, (missing (0, i)).card = 19 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma missing_1 : ∀ i : Fin 13, (missing (1, i)).card = 19 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma missing_2 : ∀ i : Fin 13, (missing (2, i)).card = 19 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma missing_3 : ∀ i : Fin 13, (missing (3, i)).card = 19 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma missing_4 : ∀ i : Fin 13, (missing (4, i)).card = 19 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma missing_5 : ∀ i : Fin 13, (missing (5, i)).card = 19 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma missing_6 : ∀ i : Fin 13, (missing (6, i)).card = 19 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma missing_7 : ∀ i : Fin 13, (missing (7, i)).card = 19 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma missing_8 : ∀ i : Fin 13, (missing (8, i)).card = 19 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma missing_9 : ∀ i : Fin 13, (missing (9, i)).card = 19 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma missing_10 : ∀ i : Fin 13, (missing (10, i)).card = 19 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma missing_11 : ∀ i : Fin 13, (missing (11, i)).card = 19 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma missing_12 : ∀ i : Fin 13, (missing (12, i)).card = 19 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma missing_13 : ∀ i : Fin 13, (missing (13, i)).card = 19 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma missing_14 : ∀ i : Fin 13, (missing (14, i)).card = 19 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma missing_15 : ∀ i : Fin 13, (missing (15, i)).card = 19 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma missing_16 : ∀ i : Fin 13, (missing (16, i)).card = 19 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma missing_17 : ∀ i : Fin 13, (missing (17, i)).card = 19 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma missing_18 : ∀ i : Fin 13, (missing (18, i)).card = 19 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma missing_19 : ∀ i : Fin 13, (missing (19, i)).card = 19 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma missing_20 : ∀ i : Fin 13, (missing (20, i)).card = 19 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma missing_21 : ∀ i : Fin 13, (missing (21, i)).card = 19 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma missing_22 : ∀ i : Fin 13, (missing (22, i)).card = 19 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma missing_23 : ∀ i : Fin 13, (missing (23, i)).card = 19 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma missing_24 : ∀ i : Fin 13, (missing (24, i)).card = 19 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma missing_25 : ∀ i : Fin 13, (missing (25, i)).card = 19 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma missing_26 : ∀ i : Fin 13, (missing (26, i)).card = 19 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma missing_27 : ∀ i : Fin 13, (missing (27, i)).card = 19 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma missing_28 : ∀ i : Fin 13, (missing (28, i)).card = 19 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma missing_29 : ∀ i : Fin 13, (missing (29, i)).card = 19 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma missing_30 : ∀ i : Fin 13, (missing (30, i)).card = 19 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma missing_31 : ∀ i : Fin 13, (missing (31, i)).card = 19 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma missing_32 : ∀ i : Fin 13, (missing (32, i)).card = 19 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma missing_33 : ∀ i : Fin 13, (missing (33, i)).card = 19 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma missing_34 : ∀ i : Fin 13, (missing (34, i)).card = 19 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma missing_35 : ∀ i : Fin 13, (missing (35, i)).card = 19 := by
  decide +kernel

lemma missing_card : ∀ r : R, (missing r).card = 19 := by
  have h : ∀ g : Fin 36, ∀ i : Fin 13, (missing (g, i)).card = 19 := by
    exact (Fin.cases missing_0 (Fin.cases missing_1 (Fin.cases missing_2 (Fin.cases missing_3 (Fin.cases missing_4 (Fin.cases missing_5 (Fin.cases missing_6 (Fin.cases missing_7 (Fin.cases missing_8 (Fin.cases missing_9 (Fin.cases missing_10 (Fin.cases missing_11 (Fin.cases missing_12 (Fin.cases missing_13 (Fin.cases missing_14 (Fin.cases missing_15 (Fin.cases missing_16 (Fin.cases missing_17 (Fin.cases missing_18 (Fin.cases missing_19 (Fin.cases missing_20 (Fin.cases missing_21 (Fin.cases missing_22 (Fin.cases missing_23 (Fin.cases missing_24 (Fin.cases missing_25 (Fin.cases missing_26 (Fin.cases missing_27 (Fin.cases missing_28 (Fin.cases missing_29 (Fin.cases missing_30 (Fin.cases missing_31 (Fin.cases missing_32 (Fin.cases missing_33 (Fin.cases missing_34 (Fin.cases missing_35 (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))
  rintro ⟨g, i⟩
  exact h g i

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma single_0 : (Finset.univ.filter fun r : R => row r (0 : Fin 26) = true).card = 126 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma single_1 : (Finset.univ.filter fun r : R => row r (1 : Fin 26) = true).card = 126 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma single_2 : (Finset.univ.filter fun r : R => row r (2 : Fin 26) = true).card = 126 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma single_3 : (Finset.univ.filter fun r : R => row r (3 : Fin 26) = true).card = 126 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma single_4 : (Finset.univ.filter fun r : R => row r (4 : Fin 26) = true).card = 126 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma single_5 : (Finset.univ.filter fun r : R => row r (5 : Fin 26) = true).card = 126 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma single_6 : (Finset.univ.filter fun r : R => row r (6 : Fin 26) = true).card = 126 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma single_7 : (Finset.univ.filter fun r : R => row r (7 : Fin 26) = true).card = 126 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma single_8 : (Finset.univ.filter fun r : R => row r (8 : Fin 26) = true).card = 126 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma single_9 : (Finset.univ.filter fun r : R => row r (9 : Fin 26) = true).card = 126 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma single_10 : (Finset.univ.filter fun r : R => row r (10 : Fin 26) = true).card = 126 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma single_11 : (Finset.univ.filter fun r : R => row r (11 : Fin 26) = true).card = 126 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma single_12 : (Finset.univ.filter fun r : R => row r (12 : Fin 26) = true).card = 126 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma single_13 : (Finset.univ.filter fun r : R => row r (13 : Fin 26) = true).card = 126 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma single_14 : (Finset.univ.filter fun r : R => row r (14 : Fin 26) = true).card = 126 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma single_15 : (Finset.univ.filter fun r : R => row r (15 : Fin 26) = true).card = 126 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma single_16 : (Finset.univ.filter fun r : R => row r (16 : Fin 26) = true).card = 126 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma single_17 : (Finset.univ.filter fun r : R => row r (17 : Fin 26) = true).card = 126 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma single_18 : (Finset.univ.filter fun r : R => row r (18 : Fin 26) = true).card = 126 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma single_19 : (Finset.univ.filter fun r : R => row r (19 : Fin 26) = true).card = 126 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma single_20 : (Finset.univ.filter fun r : R => row r (20 : Fin 26) = true).card = 126 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma single_21 : (Finset.univ.filter fun r : R => row r (21 : Fin 26) = true).card = 126 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma single_22 : (Finset.univ.filter fun r : R => row r (22 : Fin 26) = true).card = 126 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma single_23 : (Finset.univ.filter fun r : R => row r (23 : Fin 26) = true).card = 126 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma single_24 : (Finset.univ.filter fun r : R => row r (24 : Fin 26) = true).card = 126 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma single_25 : (Finset.univ.filter fun r : R => row r (25 : Fin 26) = true).card = 126 := by
  decide +kernel

lemma singleton_touch : ∀ v : Fin 26, (Finset.univ.filter fun r : R => row r v = true).card = 126 := by
  exact (Fin.cases single_0 (Fin.cases single_1 (Fin.cases single_2 (Fin.cases single_3 (Fin.cases single_4 (Fin.cases single_5 (Fin.cases single_6 (Fin.cases single_7 (Fin.cases single_8 (Fin.cases single_9 (Fin.cases single_10 (Fin.cases single_11 (Fin.cases single_12 (Fin.cases single_13 (Fin.cases single_14 (Fin.cases single_15 (Fin.cases single_16 (Fin.cases single_17 (Fin.cases single_18 (Fin.cases single_19 (Fin.cases single_20 (Fin.cases single_21 (Fin.cases single_22 (Fin.cases single_23 (Fin.cases single_24 (Fin.cases single_25 (fun i => Fin.elim0 i)))))))))))))))))))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma pair_0 : ∀ v : Fin 26, (0 : Fin 26) ≠ v → 204 ≤ (Finset.univ.filter fun r : R => row r (0 : Fin 26) = true ∨ row r v = true).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma pair_1 : ∀ v : Fin 26, (1 : Fin 26) ≠ v → 204 ≤ (Finset.univ.filter fun r : R => row r (1 : Fin 26) = true ∨ row r v = true).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma pair_2 : ∀ v : Fin 26, (2 : Fin 26) ≠ v → 204 ≤ (Finset.univ.filter fun r : R => row r (2 : Fin 26) = true ∨ row r v = true).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma pair_3 : ∀ v : Fin 26, (3 : Fin 26) ≠ v → 204 ≤ (Finset.univ.filter fun r : R => row r (3 : Fin 26) = true ∨ row r v = true).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma pair_4 : ∀ v : Fin 26, (4 : Fin 26) ≠ v → 204 ≤ (Finset.univ.filter fun r : R => row r (4 : Fin 26) = true ∨ row r v = true).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma pair_5 : ∀ v : Fin 26, (5 : Fin 26) ≠ v → 204 ≤ (Finset.univ.filter fun r : R => row r (5 : Fin 26) = true ∨ row r v = true).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma pair_6 : ∀ v : Fin 26, (6 : Fin 26) ≠ v → 204 ≤ (Finset.univ.filter fun r : R => row r (6 : Fin 26) = true ∨ row r v = true).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma pair_7 : ∀ v : Fin 26, (7 : Fin 26) ≠ v → 204 ≤ (Finset.univ.filter fun r : R => row r (7 : Fin 26) = true ∨ row r v = true).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma pair_8 : ∀ v : Fin 26, (8 : Fin 26) ≠ v → 204 ≤ (Finset.univ.filter fun r : R => row r (8 : Fin 26) = true ∨ row r v = true).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma pair_9 : ∀ v : Fin 26, (9 : Fin 26) ≠ v → 204 ≤ (Finset.univ.filter fun r : R => row r (9 : Fin 26) = true ∨ row r v = true).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma pair_10 : ∀ v : Fin 26, (10 : Fin 26) ≠ v → 204 ≤ (Finset.univ.filter fun r : R => row r (10 : Fin 26) = true ∨ row r v = true).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma pair_11 : ∀ v : Fin 26, (11 : Fin 26) ≠ v → 204 ≤ (Finset.univ.filter fun r : R => row r (11 : Fin 26) = true ∨ row r v = true).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma pair_12 : ∀ v : Fin 26, (12 : Fin 26) ≠ v → 204 ≤ (Finset.univ.filter fun r : R => row r (12 : Fin 26) = true ∨ row r v = true).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma pair_13 : ∀ v : Fin 26, (13 : Fin 26) ≠ v → 204 ≤ (Finset.univ.filter fun r : R => row r (13 : Fin 26) = true ∨ row r v = true).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma pair_14 : ∀ v : Fin 26, (14 : Fin 26) ≠ v → 204 ≤ (Finset.univ.filter fun r : R => row r (14 : Fin 26) = true ∨ row r v = true).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma pair_15 : ∀ v : Fin 26, (15 : Fin 26) ≠ v → 204 ≤ (Finset.univ.filter fun r : R => row r (15 : Fin 26) = true ∨ row r v = true).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma pair_16 : ∀ v : Fin 26, (16 : Fin 26) ≠ v → 204 ≤ (Finset.univ.filter fun r : R => row r (16 : Fin 26) = true ∨ row r v = true).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma pair_17 : ∀ v : Fin 26, (17 : Fin 26) ≠ v → 204 ≤ (Finset.univ.filter fun r : R => row r (17 : Fin 26) = true ∨ row r v = true).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma pair_18 : ∀ v : Fin 26, (18 : Fin 26) ≠ v → 204 ≤ (Finset.univ.filter fun r : R => row r (18 : Fin 26) = true ∨ row r v = true).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma pair_19 : ∀ v : Fin 26, (19 : Fin 26) ≠ v → 204 ≤ (Finset.univ.filter fun r : R => row r (19 : Fin 26) = true ∨ row r v = true).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma pair_20 : ∀ v : Fin 26, (20 : Fin 26) ≠ v → 204 ≤ (Finset.univ.filter fun r : R => row r (20 : Fin 26) = true ∨ row r v = true).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma pair_21 : ∀ v : Fin 26, (21 : Fin 26) ≠ v → 204 ≤ (Finset.univ.filter fun r : R => row r (21 : Fin 26) = true ∨ row r v = true).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma pair_22 : ∀ v : Fin 26, (22 : Fin 26) ≠ v → 204 ≤ (Finset.univ.filter fun r : R => row r (22 : Fin 26) = true ∨ row r v = true).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma pair_23 : ∀ v : Fin 26, (23 : Fin 26) ≠ v → 204 ≤ (Finset.univ.filter fun r : R => row r (23 : Fin 26) = true ∨ row r v = true).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma pair_24 : ∀ v : Fin 26, (24 : Fin 26) ≠ v → 204 ≤ (Finset.univ.filter fun r : R => row r (24 : Fin 26) = true ∨ row r v = true).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma pair_25 : ∀ v : Fin 26, (25 : Fin 26) ≠ v → 204 ≤ (Finset.univ.filter fun r : R => row r (25 : Fin 26) = true ∨ row r v = true).card := by
  decide +kernel

lemma pair_touch : ∀ u v : Fin 26, u ≠ v → 204 ≤ (Finset.univ.filter fun r : R => row r u = true ∨ row r v = true).card := by
  exact (Fin.cases pair_0 (Fin.cases pair_1 (Fin.cases pair_2 (Fin.cases pair_3 (Fin.cases pair_4 (Fin.cases pair_5 (Fin.cases pair_6 (Fin.cases pair_7 (Fin.cases pair_8 (Fin.cases pair_9 (Fin.cases pair_10 (Fin.cases pair_11 (Fin.cases pair_12 (Fin.cases pair_13 (Fin.cases pair_14 (Fin.cases pair_15 (Fin.cases pair_16 (Fin.cases pair_17 (Fin.cases pair_18 (Fin.cases pair_19 (Fin.cases pair_20 (Fin.cases pair_21 (Fin.cases pair_22 (Fin.cases pair_23 (Fin.cases pair_24 (Fin.cases pair_25 (fun i => Fin.elim0 i)))))))))))))))))))))))))))

end PEqualNP.Outside.L_meta_1896_aux.AllRows
