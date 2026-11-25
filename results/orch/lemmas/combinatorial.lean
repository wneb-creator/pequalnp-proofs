import Mathlib.Data.Bool.Basic

namespace PEqualNP.Outside.L_meta_1884

lemma move_or_to_output (a b : Bool) (continuation : Bool → Bool)
    (certified : b = true → continuation (a || b) = true) :
    continuation (a || b) = (continuation a || b) := by
  cases hb : b with
  | false => simp
  | true => simpa [hb] using certified hb

lemma move_and_to_output (a b : Bool) (continuation : Bool → Bool)
    (certified : b = false → continuation (a && b) = false) :
    continuation (a && b) = (continuation a && b) := by
  cases hb : b with
  | false => simpa [hb] using certified hb
  | true => simp

end PEqualNP.Outside.L_meta_1884
