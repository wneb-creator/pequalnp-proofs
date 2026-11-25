import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2056

def reviewAdjacent (u v : Fin 26) : Prop :=
  (u.val < 13 ∧ 13 ≤ v.val ∧ (u.val + v.val) % 13 ∈ [0, 1, 3, 9]) ∨
  (v.val < 13 ∧ 13 ≤ u.val ∧ (u.val + v.val) % 13 ∈ [0, 1, 3, 9])

lemma reviewAdjacent_irrefl : ∀ u : Fin 26, ¬ reviewAdjacent u u := by
  unfold reviewAdjacent
  decide +kernel

lemma reviewAdjacent_symm : ∀ u v : Fin 26,
    reviewAdjacent u v ↔ reviewAdjacent v u := by
  unfold reviewAdjacent
  decide +kernel

set_option synthInstance.maxSize 1000 in
lemma reviewPrivateNeighbor : ∀ u v : Fin 26, u ≠ v →
    ∃ w : Fin 26, w ≠ v ∧ reviewAdjacent u w ∧ ¬ reviewAdjacent v w := by
  unfold reviewAdjacent
  decide +kernel


def pairAssignment (p q z : Fin 26) : Bool :=
  decide (z = p ∨ z = q)

lemma pairAssignment_nonedge (p q v w : Fin 26)
    (hpq : reviewAdjacent p q) (hvw : v ≠ w)
    (hnot : ¬ reviewAdjacent v w) :
    (pairAssignment p q v && pairAssignment p q w) = false := by
  have hboth : ¬ ((v = p ∨ v = q) ∧ (w = p ∨ w = q)) := by
    rintro ⟨hvp | hvq, hwp | hwq⟩
    · exact hvw (hvp.trans hwp.symm)
    · exact hnot (by simpa only [hvp, hwq] using hpq)
    · exact hnot (by
        simpa only [hvq, hwp] using (reviewAdjacent_symm p q).mp hpq)
    · exact hvw (hvq.trans hwq.symm)
  by_cases hv : v = p ∨ v = q
  · have hw : ¬ (w = p ∨ w = q) := fun hw => hboth ⟨hv, hw⟩
    simp [pairAssignment, hw]
  · simp [pairAssignment, hv]

lemma productiveBranch_positive (p q u v w : Fin 26)
    (hpq : reviewAdjacent p q) (hvw : v ≠ w)
    (hnot : ¬ reviewAdjacent v w) :
    (pairAssignment p q w && (pairAssignment p q u || pairAssignment p q v)) =
      (pairAssignment p q w && pairAssignment p q u) := by
  have h := pairAssignment_nonedge p q v w hpq hvw hnot
  cases hv : pairAssignment p q v <;>
    cases hw : pairAssignment p q w <;> simp_all

lemma productiveBranch_le (x : Fin 26 → Bool) (u v w : Fin 26) :
    (x w && x u) ≤ (x w && (x u || x v)) := by
  cases hw : x w <;> cases hu : x u <;> cases hv : x v <;> decide


end PEqualNP.Outside.L_meta_2056
