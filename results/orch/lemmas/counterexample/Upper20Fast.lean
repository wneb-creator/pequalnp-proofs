import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1890_upper_fast

def upper20 : PEqualNP.CircuitLowerBounds.Circuit :=
  { gates := [
      ⟨.or, [1, 4]⟩,
      ⟨.or, [11, 5]⟩,
      ⟨.and, [0, 12]⟩,
      ⟨.or, [2, 6]⟩,
      ⟨.and, [1, 14]⟩,
      ⟨.or, [2, 4]⟩,
      ⟨.or, [16, 8]⟩,
      ⟨.and, [3, 17]⟩,
      ⟨.or, [2, 5]⟩,
      ⟨.or, [19, 9]⟩,
      ⟨.and, [7, 20]⟩,
      ⟨.or, [6, 5]⟩,
      ⟨.and, [8, 22]⟩,
      ⟨.or, [4, 6]⟩,
      ⟨.and, [9, 24]⟩,
      ⟨.or, [13, 15]⟩,
      ⟨.or, [26, 18]⟩,
      ⟨.or, [27, 21]⟩,
      ⟨.or, [28, 23]⟩,
      ⟨.or, [29, 25]⟩],
    output := 30 }

lemma upper20_size : upper20.size = 20 := rfl

lemma upper20_fan : PEqualNP.MetaComplexity.FanInTwo upper20 := by
  simp [PEqualNP.MetaComplexity.FanInTwo, upper20]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma upper20_eval : ∀ x : Fin 10 → Bool, upper20.eval (List.ofFn x ++ [x 0 && x 2]) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) := by
  intro x
  have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9] := rfl
  rw [hx]
  generalize x 0 = a, x 1 = b, x 2 = c, x 3 = d, x 4 = e, x 5 = f, x 6 = g, x 7 = h, x 8 = i, x 9 = j
  revert a b c d e f g h i j
  decide +kernel

end PEqualNP.Outside.L_meta_1890_upper_fast
