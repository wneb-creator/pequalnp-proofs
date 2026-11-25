import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4675.ConeAPI

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
  PEqualNP.Outside.L_meta_4675.OneJunk

def WireCone (n : ℕ) (C : Circuit) (w k : ℕ) : Prop :=
  w = n + k ∨ (n ≤ w ∧ InCone n C k (w - n))

lemma wireCone_bound (n : ℕ) (C : Circuit) (w k : ℕ) (h : WireCone n C w k) : n + k ≤ w := by
  rcases h with h | ⟨hn, hc⟩
  · omega
  · have := inCone_lt n C (w - n) k hc
    omega

lemma cones_append_prefix (n : ℕ) (gs hs : List Gate) (k : ℕ) (hk : k < gs.length) :
    (cones n ⟨gs ++ hs, 0⟩).getD k [] = (cones n ⟨gs, 0⟩).getD k [] := by
  let f : List (List ℕ) → Gate → List ℕ := fun cs g =>
    (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
      (fun w => (w - n) :: cs.getD (w - n) [])
  have hlen : (cones n ⟨gs, 0⟩).length = gs.length := cones_length n ⟨gs, 0⟩
  have hp := (foldl_append_spec f hs (cones n ⟨gs, 0⟩)).2.1 k (by rw [hlen]; exact hk)
  have he : (fun cs g => cs ++ [f cs g]) = coneStep n := rfl
  rw [he] at hp
  change ((gs ++ hs).foldl (coneStep n) []).getD k [] =
    (gs.foldl (coneStep n) []).getD k []
  rw [List.foldl_append]
  simpa only [List.getD_eq_getElem?_getD, cones] using congrArg (fun z => z.getD []) hp

lemma wireCone_append_prefix (n : ℕ) (gs hs : List Gate) (w : ℕ) (hw : w < n + gs.length)
    (k : ℕ) : WireCone n ⟨gs ++ hs, 0⟩ w k ↔ WireCone n ⟨gs, 0⟩ w k := by
  by_cases hn : n ≤ w
  · have hk : w - n < gs.length := by omega
    simp only [WireCone, hn, true_and, InCone, cones_append_prefix n gs hs (w - n) hk]
  · simp [WireCone, hn]

lemma wireCone_of_input (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (w : ℕ) (hw : w ∈ (gateAt C j).inputs) (hwb : w < n + j)
    (k : ℕ) (hc : WireCone n C w k) : WireCone n C (n + j) k := by
  right
  refine ⟨by omega, ?_⟩
  rw [Nat.add_sub_cancel_left]
  rcases hc with he | ⟨hn, hcone⟩
  · subst w
    exact inCone_of_input n C k j hj (by omega) hw
  · have he : w = n + (w - n) := by omega
    exact inCone_trans_of_input n C k (w - n) j hj (by omega) (by rwa [← he]) hcone

lemma wireCone_gate_iff (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (k : ℕ) :
    WireCone n C (n + j) k ↔ k = j ∨
      ∃ w ∈ (gateAt C j).inputs, w < n + j ∧ WireCone n C w k := by
  constructor
  · rintro (he | ⟨_, hc⟩)
    · left; omega
    · rw [Nat.add_sub_cancel_left] at hc
      unfold InCone at hc
      rw [cones_getD_eq n C j hj, List.mem_flatMap] at hc
      obtain ⟨w, hw, hc⟩ := hc
      simp only [List.mem_filter, decide_eq_true_eq] at hw
      refine Or.inr ⟨w, hw.1, hw.2.2, ?_⟩
      simp only [List.mem_cons] at hc
      rcases hc with he | hc
      · left; omega
      · exact Or.inr ⟨hw.2.1, hc⟩
  · rintro (rfl | ⟨w, hw, hwb, hc⟩)
    · exact Or.inl rfl
    · exact wireCone_of_input n C j hj w hw hwb k hc

end PEqualNP.Outside.L_meta_4675.ConeAPI
