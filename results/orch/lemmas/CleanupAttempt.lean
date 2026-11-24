import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3679

lemma cleanup_row0 (b0 b9 b11 b25 : Bool) :
    (((b0 || b9) || b11) && b25) =
      ((b25 && b0) || (b25 && b9) || (b25 && b11)) := by
  simp? [Bool.and_or_distrib_left, Bool.and_or_distrib_right, Bool.and_comm]

end PEqualNP.Outside.L_meta_3679
