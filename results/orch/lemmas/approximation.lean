import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def approximatePetersen : Circuit :=
  ⟨[
    ⟨.or, [3, 7]⟩,
    ⟨.or, [10, 1]⟩,
    ⟨.or, [9, 1]⟩,
    ⟨.or, [8, 12]⟩,
    ⟨.and, [11, 13]⟩,
    ⟨.or, [3, 9]⟩,
    ⟨.or, [0, 15]⟩,
    ⟨.or, [7, 0]⟩,
    ⟨.or, [8, 17]⟩,
    ⟨.and, [16, 14]⟩,
    ⟨.or, [19, 5]⟩,
    ⟨.and, [4, 16]⟩,
    ⟨.and, [13, 6]⟩,
    ⟨.and, [2, 11]⟩,
    ⟨.or, [21, 23]⟩,
    ⟨.and, [18, 20]⟩,
    ⟨.or, [22, 24]⟩,
    ⟨.or, [26, 25]⟩], 27⟩

lemma approximatePetersen_size : approximatePetersen.size = 18 := rfl

lemma approximatePetersen_fan : FanInTwo approximatePetersen := by
  simp [FanInTwo, approximatePetersen]

def petersenFunction (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
    x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma approximateBooleanIdentity : ∀ a b c d e f g h i j : Bool,
    (((i || (j || b)) && g ||
      (e && (a || (d || j)) || c && ((d || h) || b))) ||
      (i || (h || a)) && ((a || (d || j)) && (((d || h) || b) && (i || (j || b))) || f)) =
    ((a && b || b && c || c && d || d && e || e && a ||
      a && f || b && g || c && h || d && i || e && j ||
      f && h || h && j || j && g || g && i || i && f) ||
      (b && d && h) || (a && h && i) || (a && d && j) || (b && i && j)) := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma approximatePetersen_eval : ∀ x : Fin 10 → Bool,
    approximatePetersen.eval (List.ofFn x) =
      (petersenFunction x || (x 1 && x 3 && x 7) || (x 0 && x 7 && x 8) ||
        (x 0 && x 3 && x 9) || (x 1 && x 8 && x 9)) := by
  intro x
  have hinput : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9] := rfl
  rw [hinput]
  simpa [approximatePetersen, Circuit.eval, Circuit.wires, GateOp.eval, petersenFunction,
    Bool.and_assoc, Bool.or_assoc] using
    approximateBooleanIdentity (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9)

lemma approximatePetersen_misses :
    approximatePetersen.eval (List.ofFn (fun i : Fin 10 => decide (i = 1 ∨ i = 3 ∨ i = 7))) ≠
      petersenFunction (fun i : Fin 10 => decide (i = 1 ∨ i = 3 ∨ i = 7)) := by
  rw [approximatePetersen_eval]
  decide

end PEqualNP.Outside.L_meta_2592_aux
