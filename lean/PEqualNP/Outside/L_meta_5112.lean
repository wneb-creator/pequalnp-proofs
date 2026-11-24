import Mathlib.Data.Nat.Bitwise

namespace PEqualNP.Outside.L_meta_5112_aux

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma fifteen_gates : ∃ (x1 : List (Bool × ℕ × ℕ)), (1 : ℕ) ≤ x1.length ∧ x1.length ≤ (15 : ℕ) ∧ (List.foldl (fun (x2 : List ℕ) (x3 : Bool × ℕ × ℕ) => x2 ++ [if x3.1 = Bool.true then x2.getD x3.2.1 (0 : ℕ) ||| x2.getD x3.2.2 (0 : ℕ) else x2.getD x3.2.1 (0 : ℕ) &&& x2.getD x3.2.2 (0 : ℕ)]) [(256463372304 : ℕ), (8521482511360 : ℕ), (14003410187716736 : ℕ), (55389823206179104 : ℕ), (155696362464215096 : ℕ), (218994303131713984 : ℕ), (183565875465424384 : ℕ), (229736628136996864 : ℕ), (270286071508729856 : ℕ), (288160007409369088 : ℕ), (192860064594267704 : ℕ), (288166778660192704 : ℕ), (283797140973809664 : ℕ)] x1).getD ((13 : ℕ) + x1.length - (1 : ℕ)) (0 : ℕ) = (1764784 : ℕ) := by
  refine ⟨[(true, 4, 8), (true, 13, 9), (false, 0, 14), (true, 6, 7), (true, 16, 9), (false, 1, 17), (true, 5, 6), (true, 19, 8), (false, 2, 20), (true, 4, 5), (true, 22, 7), (false, 3, 23), (true, 15, 18), (true, 25, 21), (true, 26, 24)], ?_⟩
  decide

end PEqualNP.Outside.L_meta_5112_aux
