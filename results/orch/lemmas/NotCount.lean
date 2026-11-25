import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10760

open PEqualNP.CircuitLowerBounds

noncomputable def notCount (gs : List Gate) : ℕ := by
  classical
  exact gs.countP (fun g => decide (g.op = GateOp.not))

lemma unique_not_count (gs : List Gate)
    (h : ∀ i j : Fin gs.length,
      (gs.get i).op = GateOp.not → (gs.get j).op = GateOp.not → i = j) :
    notCount gs ≤ 1 := by
  classical
  unfold notCount
  induction gs with
  | nil => simp
  | cons g gs ih =>
    by_cases hg : g.op = GateOp.not
    · have hz : gs.countP (fun g => decide (g.op = GateOp.not)) = 0 := by
        apply List.countP_eq_zero.mpr
        intro a ha
        simp only [decide_eq_true_eq]
        intro haNot
        obtain ⟨i, hi⟩ := List.mem_iff_get.mp ha
        have hiNot : (gs.get i).op = GateOp.not := by rw [hi]; exact haNot
        have hh := h ⟨0, by simp⟩ i.succ (by simpa using hg)
          (by simpa using hiNot)
        have hv := congrArg Fin.val hh
        simp at hv
      simp [List.countP_cons, hg, hz]
    · have ht : ∀ i j : Fin gs.length,
          (gs.get i).op = GateOp.not → (gs.get j).op = GateOp.not → i = j := by
        intro i j hi hj
        exact Fin.succ_inj.mp (h i.succ j.succ (by simpa using hi) (by simpa using hj))
      simpa [List.countP_cons, hg] using ih ht

end PEqualNP.Outside.L_meta_10760
