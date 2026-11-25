namespace PEqualNP.Outside.L_meta_2592_aux.Duplicate

open PEqualNP.Outside.L_meta_2592.Signed
open PEqualNP.Outside.L_meta_2592_aux.PairSeparation
open PEqualNP.Outside.L_meta_2592_aux.FirstGateCases

lemma first_wire_unique (D : U2Circuit) (hmin : IsMinU2 pet D)
    (j : ℕ) (hj : j < D.gates.length) (hpos : 0 < j) :
    ¬ ∀ x : Fin 10 → Bool, u2Val D.gates x (10 + j) = u2Val D.gates x 10 := by
  intro he
  have hd := deleteGateAt_spec D hmin.1 j hj (Sum.inr (10, false))
    (by simp [refWf]; omega) (fun x => by
      simp only [refEval]
      rw [u2Val_take D.gates x j 10 (by omega) (by omega)]
      simpa using (he x).symm)
  have hm := hmin.2.2 _ hd.1 (fun x => (hd.2.2 x).trans (hmin.2.1 x))
  omega

lemma no_later_first_pair (floor : ZeroFloor) (D : U2Circuit) (hmin : IsMinU2 pet D)
    (small : D.gates.length ≤ 17) (h0 : 0 < D.gates.length)
    (j : ℕ) (hj : j < D.gates.length) (hpos : 0 < j) :
    ¬ ((D.gates[j].a = D.gates[0].a ∨ D.gates[j].b = D.gates[0].a) ∧
      (D.gates[j].a = D.gates[0].b ∨ D.gates[j].b = D.gates[0].b)) := by
  rintro ⟨ha | ha, hb | hb⟩
  · exact min_no_self hmin 0 h0 (ha.symm.trans hb)
  · obtain ⟨pa, pb, all⟩ := first_sources_negative_everywhere floor D hmin small h0
    have hjpa := (all j hj).1 ha
    have hjpb := (all j hj).2.2.2 hb
    apply first_wire_unique D hmin j hj hpos
    intro x
    have hfirst := u2Val_gate D.gates x 0 h0 (hmin.1.1 0 h0).1 (hmin.1.1 0 h0).2
    have hlater := u2Val_gate D.gates x j hj (hmin.1.1 j hj).1 (hmin.1.1 j hj).2
    rw [hlater, hfirst]
    simp only [ha, hb, pa, pb, hjpa, hjpb]
  · obtain ⟨pa, pb, all⟩ := first_sources_negative_everywhere floor D hmin small h0
    have hjpa := (all j hj).2.2.1 hb
    have hjpb := (all j hj).2.1 ha
    apply first_wire_unique D hmin j hj hpos
    intro x
    have hfirst := u2Val_gate D.gates x 0 h0 (hmin.1.1 0 h0).1 (hmin.1.1 0 h0).2
    have hlater := u2Val_gate D.gates x j hj (hmin.1.1 j hj).1 (hmin.1.1 j hj).2
    rw [hlater, hfirst]
    simp only [ha, hb, pa, pb, hjpa, hjpb, Bool.and_comm]
  · exact min_no_self hmin 0 h0 (ha.symm.trans hb)

lemma future_readers_distinct (floor : ZeroFloor) (D : U2Circuit) (hmin : IsMinU2 pet D)
    (small : D.gates.length ≤ 17) (h0 : 0 < D.gates.length)
    (j k : ℕ) (hj : j < D.gates.length) (hk : k < D.gates.length)
    (hpos : 0 < j)
    (hja : D.gates[j].a = D.gates[0].a ∨ D.gates[j].b = D.gates[0].a)
    (hkb : D.gates[k].a = D.gates[0].b ∨ D.gates[k].b = D.gates[0].b) : j ≠ k := by
  intro he
  subst k
  exact no_later_first_pair floor D hmin small h0 j hj hpos ⟨hja, hkb⟩

end PEqualNP.Outside.L_meta_2592_aux.Duplicate
