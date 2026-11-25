import Bound17
import PrefixNot

namespace PEqualNP.Outside.L_meta_1884_aux.FreeNotFloor

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2592
open PEqualNP.Outside.L_meta_1884.PrefixNot

lemma canonical_floor (C : Circuit) (hc : FanInTwo C)
    (he : ∀ x : Fin 10 → Bool,
      C.eval (List.ofFn x ++ [!(x 0)]) = Extended.f10 x) :
    17 + PEqualNP.NotBracket.notCount C ≤ C.size := by
  exact transfer_not_floor 17 Extended.f10 binary_floor17 C hc he

lemma canonical_cases (C : Circuit) (hc : FanInTwo C) (hs : C.size ≤ 18)
    (he : ∀ x : Fin 10 → Bool,
      C.eval (List.ofFn x ++ [!(x 0)]) = Extended.f10 x) :
    (PEqualNP.NotBracket.notCount C = 0 ∧ 17 ≤ C.size ∧ C.size ≤ 18) ∨
    (PEqualNP.NotBracket.notCount C = 1 ∧ C.size = 18) := by
  have hb := canonical_floor C hc he
  omega

lemma exclude_two_internal_nots (C : Circuit) (hc : FanInTwo C)
    (hs : C.size ≤ 18) (hn : 2 ≤ PEqualNP.NotBracket.notCount C) :
    ∃ x : Fin 10 → Bool,
      C.eval (List.ofFn x ++ [!(x 0)]) ≠ Extended.f10 x := by
  by_contra h
  push Not at h
  have hb := canonical_floor C hc h
  omega

lemma exclude_sixteen (C : Circuit) (hc : FanInTwo C) (hs : C.size ≤ 16) :
    ∃ x : Fin 10 → Bool,
      C.eval (List.ofFn x ++ [!(x 0)]) ≠ Extended.f10 x := by
  by_contra h
  push Not at h
  have hb := canonical_floor C hc h
  omega

end PEqualNP.Outside.L_meta_1884_aux.FreeNotFloor
