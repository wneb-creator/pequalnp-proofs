import Mathlib

namespace PEqualNP.Outside.L_meta_2592.ReadTwoCofactors

lemma or_negative_leaf_replacement :
    ∀ (A B H : Bool → Bool), Monotone A → Monotone B → Monotone H →
      Monotone (fun b => H (A b || B (!b))) →
      ∀ b, H (A b || B (!b)) = H (A b || B true) := by
  decide +kernel

lemma and_negative_leaf_replacement :
    ∀ (A B H : Bool → Bool), Monotone A → Monotone B → Monotone H →
      Monotone (fun b => H (A b && B (!b))) →
      ∀ b, H (A b && B (!b)) = H (A b && B false) := by
  decide +kernel

end PEqualNP.Outside.L_meta_2592.ReadTwoCofactors
