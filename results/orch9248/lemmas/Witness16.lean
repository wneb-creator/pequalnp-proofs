import RUPHarness

namespace PEqualNP.Outside.L_meta_9248.Witness16

open PEqualNP.ProofComplexity PEqualNP.Search
open PEqualNP.Outside.L_meta_9248.RUPHarness

def steps : List (List (Literal Board) × List Nat) :=
  ([
    ([4, 0, 15, 32], [35, 0, 15, 16, 17, 18, 39, 40, 41, 4, 31, 33, 2, 9, 12, 3, 34]),
    ([4, 12, 17], [6, 9, 12, 13, 45, 1, 15, 0, 19, 20, 21, 36, 37, 3, 32, 34, 4, 38]),
    ([31, 20, 12, 4], [37, 40, 42, 44, 46, 2, 16, 0, 5, 1, 7, 8, 19]),
    ([27, 16, 12, 20], [17, 20, 22, 2, 24, 36, 39, 1, 5, 0, 10, 11, 27, 28, 4, 42, 43]),
    ([36, 3, 14, 38], [15, 16, 17, 18, 4, 8, 11, 1, 13, 14, 25, 29, 2, 30, 3, 36, 42]),
    ([23, 36, 4], [36, 39, 42, 43, 49, 0, 5, 6, 7, 8, 4, 21, 1, 23, 24, 3, 29, 30]),
    ([37], [28, 31, 33, 34, 46, 47, 48, 3, 7, 10, 14, 45, 1, 15, 0, 19, 2, 21, 36]),
    ([18, 13, 2], [25, 29, 30, 31, 50, 2, 6, 0, 9, 12, 13, 35, 37, 3, 20, 24, 4, 38]),
    ([34, 2, 15], [35, 39, 40, 41, 51, 4, 8, 0, 11, 13, 14, 25, 26, 2, 19, 22, 3, 27]),
    ([27], [17, 20, 22, 24, 51, 52, 53, 1, 5, 9, 10, 11, 4, 38, 0, 26, 2, 27, 42, 43]),
    ([19, 0, 32], [16, 19, 22, 23, 51, 4, 38, 0, 25, 26, 27, 41, 1, 9, 10, 3, 42, 44]),
    ([5, 16, 18], [25, 26, 2, 27, 28, 36, 39, 42, 43, 48, 3, 7, 10, 1, 14, 4, 15, 21]),
    ([29], [27, 30, 32, 34, 46, 47, 48, 50, 2, 16, 19, 23, 53, 1, 5, 0, 10, 11, 4, 38]),
    ([33], [8, 11, 13, 14, 51, 54, 57, 3, 37, 40, 42, 44, 49, 0, 25, 1, 19, 2, 21, 26]),
    ([31], [37, 40, 42, 44, 51, 49, 54, 57, 58, 4, 21, 23, 52, 1, 5, 0, 9, 2, 10, 26]),
    ([], [51, 54, 57, 58, 59, 3, 7, 10, 12, 55, 56, 45, 50, 2, 29, 1, 15, 0, 21, 4, 38])
  ] : List (List Nat × List Nat)).map (fun p => (p.1.map readLiteral, p.2))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem checked : verify input steps = true := by decide +kernel

theorem run : IsRUPRun (PHP 5 4) (learned steps []) := validated_run steps checked

theorem contains_empty : (∅ : Clause Board) ∈ learned steps [] := by decide +kernel

theorem count : (learned steps []).length = 16 := by decide +kernel

end PEqualNP.Outside.L_meta_9248.Witness16
