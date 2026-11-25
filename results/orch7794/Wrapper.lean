import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7794.WrapperTest
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)

lemma wrapper (no : ¬ HasCircuitSize 9 edge 15) :
have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size = (15 : ℕ) → ∃ (x5 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn x5) ≠ x1 x5 := by
  dsimp only
  intro C legal size
  by_contra! all
  apply no
  refine ⟨C,legal,size.le,?_⟩
  intro x
  convert all x using 1 <;> norm_num [edge,Fin.ofNat,Bool.or_assoc]

end PEqualNP.Outside.L_meta_7794.WrapperTest
