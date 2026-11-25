import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_650

lemma filtered_pair_shorter (p q u v t : Bool) :
    (((p || q) && ((u || v) || t)) && ((q || u) || t)) =
      (((p || q) && (u || t)) || (q && v)) := by decide +revert

lemma filtered_pair_split (p q u v t : Bool) :
    (((p || q) && (u || t)) || (q && v)) =
      ((((p || q) && t) || (p && u) || (q && v)) || (q && u)) := by decide +revert

lemma move_one_leaf (q a u v s z : Bool) :
    ((q && v) || (a && (u || v || s || z))) =
      ((v && (q || a)) || (a && (u || s || z))) := by decide +revert

lemma move_two_leaves (p q a u v s z : Bool) :
    ((p && u) || (q && v) || (a && (u || v || s || z))) =
      ((u && (p || a)) || (v && (q || a)) || (a && (s || z))) := by decide +revert

end PEqualNP.Outside.L_meta_650
