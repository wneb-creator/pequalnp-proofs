import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1031.FirstJunk

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge

lemma coneStep_bounded (n : ℕ) (cs : List (List ℕ)) (g : Gate)
    (hcs : ∀ k i, i ∈ cs.getD k [] → i < k) :
    ∀ k i, i ∈ (coneStep n cs g).getD k [] → i < k := by
  intro k i hi
  by_cases hk : k < cs.length
  · have hkeep : (coneStep n cs g).getD k [] = cs.getD k [] := by
      simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hk]
    exact hcs k i (hkeep ▸ hi)
  · by_cases he : k = cs.length
    · subst k
      have hlast : (coneStep n cs g).getD cs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
            (fun w => (w - n) :: cs.getD (w - n) []) := by
        simp [coneStep, List.getD_eq_getElem?_getD]
      rw [hlast] at hi
      obtain ⟨w, hw, hi⟩ := List.mem_flatMap.mp hi
      have hw' : n ≤ w ∧ w < n + cs.length :=
        of_decide_eq_true (List.mem_filter.mp hw).2
      rcases List.mem_cons.mp hi with rfl | hi
      · omega
      · have hlt := hcs (w - n) i hi
        omega
    · have hge : (coneStep n cs g).length ≤ k := by
        simp only [coneStep, List.length_append, List.length_singleton]
        omega
      rw [List.getD_eq_default _ _ hge] at hi
      simp at hi

lemma coneFold_bounded (n : ℕ) (gs : List Gate) (cs : List (List ℕ))
    (hcs : ∀ k i, i ∈ cs.getD k [] → i < k) :
    ∀ k i, i ∈ (gs.foldl (coneStep n) cs).getD k [] → i < k := by
  induction gs generalizing cs with
  | nil => exact hcs
  | cons g gs ih =>
    exact ih (coneStep n cs g) (coneStep_bounded n cs g hcs)

lemma inCone_lt (n : ℕ) (C : Circuit) {i j : ℕ} (h : InCone n C i j) : i < j := by
  exact coneFold_bounded n C.gates [] (by simp) j i h

lemma junk_mem_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (i : ℕ) :
    i ∈ junk G C ↔ i < C.gates.length ∧ (gateAt C i).op = GateOp.and ∧ ¬ BelowF G C i := by
  classical
  unfold junk gatesWhere
  rw [Finset.mem_filter, Finset.mem_range]
  unfold IsDirtyAnd IsDirty BelowF
  constructor
  · rintro ⟨hi, hop, _, x, hx, hF⟩
    refine ⟨hi, hop, ?_⟩
    intro h
    have ht := h x hx
    rw [hF] at ht
    cases ht
  · rintro ⟨hi, hop, h⟩
    push Not at h
    obtain ⟨x, hx, hF⟩ := h
    exact ⟨hi, hop, hi, x, hx, Bool.eq_false_iff.mpr hF⟩

lemma first_junk_no_and_ancestor {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hT : TopForm G C) {g : ℕ}
    (hg : g ∈ junk G C) (hfirst : ∀ i ∈ junk G C, g ≤ i) :
    ∀ i < C.gates.length, (gateAt C i).op = GateOp.and → ¬ InCone n C i g := by
  obtain ⟨hglt, hgop, _⟩ := (junk_mem_iff G C g).mp hg
  intro i hi hop hcone
  by_cases hB : BelowF G C i
  · exact hT i hi g hglt hop hB hgop hcone
  · have himem := (junk_mem_iff G C i).mpr ⟨hi, hop, hB⟩
    have hle := hfirst i himem
    have hlt := inCone_lt n C hcone
    omega

lemma exists_junk_no_and_ancestor {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hT : TopForm G C)
    (hJ : (junk G C).Nonempty) :
    ∃ g ∈ junk G C, ∀ i < C.gates.length,
      (gateAt C i).op = GateOp.and → ¬ InCone n C i g := by
  refine ⟨(junk G C).min' hJ, Finset.min'_mem _ hJ, ?_⟩
  exact first_junk_no_and_ancestor G C hT (Finset.min'_mem _ hJ)
    (fun i hi => Finset.min'_le _ i hi)

end PEqualNP.Outside.L_meta_1031.FirstJunk
