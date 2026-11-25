import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux

lemma fourStarsCover (a b c d e f : Bool) :
    ((a || b || c) && (a || d || e) && (f || e || c) && (f || b || d)) =
      ((a && f) || (b && e) || (c && d) || (a && b && c) ||
        (a && d && e) || (f && e && c) || (f && b && d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> rfl

lemma fourStarsLoseMatching (g : Bool → Bool → Bool → Bool → Bool) :
    ¬ ∀ a b c d e f : Bool,
      g (a || b || c) (a || d || e) (f || e || c) (f || b || d) =
        ((a && f) || (b && e) || (c && d)) := by
  intro h
  have hgood : g true true true true = true :=
    h true false false false false true
  have hbad : g true true true true = false :=
    h false true false true false true
  rw [hgood] at hbad
  cases hbad

end PEqualNP.Outside.L_meta_2592_aux
