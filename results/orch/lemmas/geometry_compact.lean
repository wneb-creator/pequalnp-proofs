import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2602_aux

def incidence (p l : Fin 13) : Prop :=
  p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9

lemma incidence_sub_right (p m l : Fin 13) :
    incidence (p - l) (m - l) ↔ incidence p m := by
  simp only [incidence, sub_add_eq_add_sub, sub_left_inj]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxSize 4096 in
lemma incidence_no_rectangle_zero : ∀ p q d : Fin 13,
    p ≠ q → d ≠ 0 → incidence p 0 → incidence p d → incidence q 0 →
    ¬ incidence q d := by
  unfold incidence
  decide

lemma incidence_no_rectangle : ∀ p q l m : Fin 13,
    p ≠ q → l ≠ m → incidence p l → incidence p m → incidence q l →
    ¬ incidence q m := by
  intro p q l m hpq hlm hpl hpm hql hqm
  have hpq' : p - l ≠ q - l := by
    intro h
    exact hpq (sub_left_inj.mp h)
  have hdm : m - l ≠ 0 := sub_ne_zero.mpr hlm.symm
  have hpl' : incidence (p - l) 0 := by
    simpa only [sub_self] using (incidence_sub_right p l l).mpr hpl
  have hql' : incidence (q - l) 0 := by
    simpa only [sub_self] using (incidence_sub_right q l l).mpr hql
  exact incidence_no_rectangle_zero (p - l) (q - l) (m - l) hpq' hdm
    hpl' ((incidence_sub_right p m l).mpr hpm)
    hql' ((incidence_sub_right q m l).mpr hqm)

end PEqualNP.Outside.L_meta_2602_aux
