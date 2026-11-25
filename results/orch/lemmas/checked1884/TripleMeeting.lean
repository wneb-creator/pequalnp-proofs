import PetersenGeometry

namespace PEqualNP.Outside.L_meta_1884_aux.PivotMeeting

open PEqualNP.Outside.L_meta_2590_aux.Surplus

lemma joint_three {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}
    (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    (v : Fin n) {c d : Fin n} (hcd : G c d) :
    ∃ j, j < D.length ∧ tag D j = true ∧
      v ∉ supp n D (n + j) ∧ c ∉ supp n D (n + j) ∧ d ∉ supp n D (n + j) ∧
      (v ∈ supp n D (opA D j) ∨ c ∈ supp n D (opA D j) ∨ d ∈ supp n D (opA D j)) ∧
      (v ∈ supp n D (opB D j) ∨ c ∈ supp n D (opB D j) ∨ d ∈ supp n D (opB D j)) := by
  classical
  have hex : ∃ w, val D (sem_two c d) w = true ∧
      v ∉ supp n D w ∧ c ∉ supp n D w ∧ d ∉ supp n D w :=
    ⟨outW n D, (hC _).2 (sem_two_edge hcd), by rw [sem_supp_out hG hC]; simp⟩
  obtain ⟨hw, hv, hc, hd⟩ := Nat.find_spec hex
  have hmin : ∀ a, a < Nat.find hex → val D (sem_two c d) a = true →
      v ∈ supp n D a ∨ c ∈ supp n D a ∨ d ∈ supp n D a := by
    intro a ha hva
    by_contra hm
    push Not at hm
    exact Nat.find_min hex ha ⟨hva, hm⟩
  generalize Nat.find hex = w at hw hv hc hd hmin
  have hlt : w < n + D.length := by
    by_contra hno
    rw [val_ge D _ w (by omega)] at hw
    exact Bool.false_ne_true hw
  have hn : n ≤ w := by
    by_contra hno
    have hwlt : w < n := by omega
    have hs : supp n D w = {⟨w, hwlt⟩} := supp_input D ⟨w, hwlt⟩
    rw [hs, Finset.mem_singleton] at hc hd
    rw [val_input D _ w hwlt] at hw
    simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at hw
    rcases hw with hh | hh
    · exact hc hh.symm
    · exact hd hh.symm
  obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
  have hj : j < D.length := by omega
  obtain ⟨ha, hb, -⟩ := hS j hj
  rw [val_gate hS _ j hj] at hw
  cases ht : tag D j
  · exfalso
    rw [ht, gop_false, Bool.or_eq_true] at hw
    rw [sem_supp_or hS hj ht, Finset.mem_union, not_or] at hv hc hd
    rcases hw with hwa | hwb
    · rcases hmin _ ha hwa with hh | hh | hh
      · exact hv.1 hh
      · exact hc.1 hh
      · exact hd.1 hh
    · rcases hmin _ hb hwb with hh | hh | hh
      · exact hv.2 hh
      · exact hc.2 hh
      · exact hd.2 hh
  · rw [ht, gop_true, Bool.and_eq_true] at hw
    exact ⟨j, hj, ht, hv, hc, hd, hmin _ ha hw.1, hmin _ hb hw.2⟩

end PEqualNP.Outside.L_meta_1884_aux.PivotMeeting
