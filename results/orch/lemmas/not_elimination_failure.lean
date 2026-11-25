import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux

lemma polarized_repair_failure :
    ∀ (G : Bool → Bool → Bool) (a b x : Bool),
      (∀ p, Monotone (G p)) → G a b ≤ G true false →
      G (x || a) ((!x) && b) ≠ G (x || a) b →
      a = false ∧ b = true ∧ x = true ∧
        G false true = false ∧ G true false = false ∧ G true true = true := by
  decide

end PEqualNP.Outside.L_meta_2592_aux
