import BinarySeventeen

namespace PEqualNP.Outside.L_meta_2592_aux.SeventeenCorollaries

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_7493.CircuitProof
open PEqualNP.Outside.L_meta_2592_aux.Restriction

lemma count_partition (gs : List Gate) :
    nonNotCount gs + (gs.filter (fun g => isNotGate g.op)).length = gs.length := by
  rw [← List.countP_eq_length_filter]
  induction gs with
  | nil => simp [nonNotCount]
  | cons g gs ih =>
    simp only [nonNotCount, List.countP_cons, List.length_cons] at ih ⊢
    cases h : isNotGate g.op <;> simp [h] <;> omega

lemma nonNotCount_add_notCount (C : Circuit) :
    nonNotCount C.gates + PEqualNP.NotBracket.notCount C = C.size := by
  have eq : (C.gates.filter (fun g => isNotGate g.op)).length =
      PEqualNP.NotBracket.notCount C := by
    unfold PEqualNP.NotBracket.notCount
    congr 2
    funext g
    cases g.op <;> rfl
  simpa only [eq, Circuit.size] using count_partition C.gates

theorem size_floor (C : Circuit) (fan : FanInTwo C)
    (correct : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x) :
    17 + PEqualNP.NotBracket.notCount C ≤ C.size := by
  have floor := BinarySeventeen.binary_floor C fan correct
  have total := nonNotCount_add_notCount C
  omega

theorem not_count_at_most_two (C : Circuit) (fan : FanInTwo C)
    (correct : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x)
    (small : C.size ≤ 19) : PEqualNP.NotBracket.notCount C ≤ 2 := by
  have floor := size_floor C fan correct
  omega

theorem three_nots_impossible (C : Circuit) (fan : FanInTwo C)
    (small : C.size ≤ 19) (many : 3 ≤ PEqualNP.NotBracket.notCount C) :
    ¬ ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x := by
  intro correct
  have upper := not_count_at_most_two C fan correct small
  omega

end PEqualNP.Outside.L_meta_2592_aux.SeventeenCorollaries
