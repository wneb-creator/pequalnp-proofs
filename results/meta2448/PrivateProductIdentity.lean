import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2448_aux.PrivateExchange

lemma product_with_literal_context (a b A B : Bool)
    (ha : a = true → A = true) (hb : b = true → B = true) :
    ((A && B) && (a || b)) = ((a && B) || (b && A)) := by
  cases a <;> cases b <;> cases A <;> cases B <;> simp_all

lemma shared_literal_absorption (a A B : Bool) :
    ((a || A) && (a || B)) = (a || (A && B)) := by
  cases a <;> cases A <;> cases B <;> rfl

lemma path_four_identity (a b c d : Bool) :
    (((a || c) && (b || d)) && (b || c)) =
      ((b && (a || c)) || (c && (b || d))) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

end PEqualNP.Outside.L_meta_2448_aux.PrivateExchange
