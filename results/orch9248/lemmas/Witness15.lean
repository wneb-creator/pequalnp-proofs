import RUPHarness

namespace PEqualNP.Outside.L_meta_9248.Witness15

open PEqualNP.ProofComplexity PEqualNP.Search
open PEqualNP.Outside.L_meta_9248.RUPHarness

def steps : List (List (Literal Board) × List Nat) :=
  ([
    ([3, 30, 24, 16], [15, 16, 17, 3, 18, 27, 30, 32, 2, 34, 36, 39, 1, 5, 11, 4, 43]),
    ([23, 12, 10], [36, 39, 1, 5, 9, 10, 11, 42, 43, 45, 0, 26, 27, 3, 22, 24, 4, 28]),
    ([37, 23], [28, 31, 33, 34, 36, 39, 42, 43, 46, 15, 0, 5, 6, 7, 3, 8, 19, 20]),
    ([7, 34, 26, 32], [35, 36, 37, 38, 4, 28, 31, 33, 34, 3, 7, 10, 1, 12, 2, 15, 19]),
    ([26, 28, 7], [35, 36, 37, 3, 7, 10, 12, 14, 38, 48, 18, 21, 1, 23, 2, 25, 29]),
    ([35, 12, 20], [18, 21, 23, 24, 46, 2, 6, 9, 1, 12, 13, 35, 0, 27, 3, 28, 40]),
    ([19, 28, 4], [16, 19, 22, 23, 49, 0, 5, 6, 7, 3, 8, 40, 1, 29, 31, 4, 42, 44]),
    ([21, 26, 2], [26, 29, 32, 33, 49, 0, 5, 6, 7, 3, 8, 40, 1, 19, 21, 4, 42, 44]),
    ([35], [18, 21, 23, 24, 52, 50, 25, 30, 31, 49, 0, 5, 6, 2, 7, 3, 8, 39, 42]),
    ([23], [36, 39, 42, 43, 47, 53, 4, 8, 11, 13, 14, 45, 0, 25, 1, 19, 20, 3, 26, 27]),
    ([11], [15, 19, 20, 21, 52, 54, 2, 6, 9, 12, 13, 48, 0, 25, 27, 3, 28, 4, 40, 44]),
    ([37], [28, 31, 33, 34, 47, 50, 51, 2, 6, 9, 12, 13, 55, 1, 35, 0, 17, 3, 40]),
    ([13], [25, 29, 30, 31, 51, 53, 54, 2, 6, 9, 12, 13, 4, 38, 0, 15, 17, 3, 40, 44]),
    ([14], [53, 54, 55, 56, 57, 1, 5, 9, 10, 11, 4, 38, 44, 45, 0, 26, 2, 22, 3, 27]),
    ([], [53, 54, 55, 56, 57, 58, 35, 40, 41, 4, 8, 11, 13, 14, 45, 0, 26, 2, 22, 3, 27])
  ] : List (List Nat × List Nat)).map (fun p => (p.1.map readLiteral, p.2))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem checked : verify input steps = true := by decide +kernel

theorem run : IsRUPRun (PHP 5 4) (learned steps []) := validated_run steps checked

theorem contains_empty : (∅ : Clause Board) ∈ learned steps [] := by decide +kernel

theorem count : (learned steps []).length = 15 := by decide +kernel

end PEqualNP.Outside.L_meta_9248.Witness15
