import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2602_aux

lemma two_and_one_use_trace : ∀ up ul vp vl ap al bp bl : Bool,
    (((up && vp) || ap) && bp) = false →
    (((ul && vl) || al) && bl) = false →
    ((((up || ul) && (vp || vl)) || ap || al) && (bp || bl)) = true →
    ((((up && vp) || ap) && bl) ||
      (((up && vl) || (ul && vp) || al) && bp)) = true ∨
    ((((ul && vl) || al) && bp) ||
      (((up && vl) || (ul && vp) || ap) && bl)) = true := by
  decide

lemma repeated_factor_is_clean (D A B F : Prop)
    (clean : ((D ∨ A) ∧ (D ∨ B)) → F) : D → F := by
  intro hD
  exact clean ⟨Or.inl hD, Or.inl hD⟩

end PEqualNP.Outside.L_meta_2602_aux
