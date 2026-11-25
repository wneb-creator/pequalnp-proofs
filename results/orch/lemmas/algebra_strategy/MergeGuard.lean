import Mathlib

namespace PEqualNP.Outside.L_meta_650_aux.MergeGuard

/-- Three pairwise merged rectangles recover the OR of three arbitrary stars. -/
theorem triangle_guard : ∀ a b c u v w : Bool,
    ((a && u) || (b && v) || (c && w)) =
      ((((a || b) && (u || v)) || (c && w)) &&
       (((a || c) && (u || w)) || (b && v)) &&
       (((b || c) && (v || w)) || (a && u))) := by
  decide

end PEqualNP.Outside.L_meta_650_aux.MergeGuard
