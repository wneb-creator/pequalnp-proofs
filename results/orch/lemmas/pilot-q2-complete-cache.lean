import PNPQ2Residual
import PNPQ2FActualFinal
import PNPQ2FFinite
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace PEqualNP.Outside.L_meta_6659_aux
lemma qa_q2_conditional_exclusion {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hI : ineligSet 14 D = {0,1,2,3})
    (hM : equality_missing_points D = {2,4,5,6})
    (hplus : Bplus 14 D ≤ 13) (hS : totalSurplus 14 D ≤ 14)
    (certificate : ∀ s a b c, q2f_certificate s a b c = true) : False := by
  classical
  have lower := q2f_circuit_Bplus_lower h hD hI hM certificate
  have exactplus : Bplus 14 D = 13 := Nat.le_antisymm hplus lower
  have lineP : ∀ t : Fin 7, qa_line t ∈ sem_hw_opp 0 := by decide +kernel
  have mask_eq (w : ℕ) :
      equality_mask_pull q2f_line_embed (supp 14 D w ∩ sem_hw_opp 0) = qa_mask D w := by
    ext t
    simp only [equality_mask_pull,qa_mask,Finset.mem_filter,Finset.mem_univ,true_and,
      Finset.mem_inter]
    change (qa_line t ∈ supp 14 D w ∧ qa_line t ∈ sem_hw_opp 0) ↔ qa_line t ∈ supp 14 D w
    simp only [lineP t,and_true]
  have occurs : ∀ i ∈ ({0,1,3} : Finset (Fin 4)), ∃ w, qa_mask D w = qa_nb i := by
    intro i hi
    let q : Fin 7 := ⟨i.val,by omega⟩
    have pt : os_pt q = qa_point i := by apply Fin.ext; rfl
    have notmissing : q ∉ equality_missing_points D := by
      rw [hM]
      exact (by decide +kernel : ∀ i ∈ ({0,1,3} : Finset (Fin 4)),
        (Fin.castLE (by decide) i : Fin 7) ∉ ({2,4,5,6} : Finset (Fin 7))) i hi
    have occurrence : sup_Occ 14 D (sem_hw_opp 0) (sem_hw_nb (os_pt q)) := by
      by_contra absent
      exact notmissing (Finset.mem_filter.mpr ⟨Finset.mem_univ _,absent⟩)
    obtain ⟨w,hw⟩ := occurrence
    refine ⟨w,?_⟩
    ext t
    simp only [qa_mask,Finset.mem_filter,Finset.mem_univ,true_and]
    have same : qa_line t ∈ supp 14 D w ↔ qa_line t ∈ sem_hw_nb (os_pt q) := by
      rw [← hw]
      simp only [Finset.mem_inter,lineP t,and_true]
    rw [same,pt]
    exact (by decide +kernel : ∀ i : Fin 4, ∀ t : Fin 7,
      qa_line t ∈ sem_hw_nb (qa_point i) ↔ t ∈ qa_nb i) i t
  obtain ⟨S,_,large⟩ := q2f_circuit_large_masks h hD hI hM hplus certificate
  apply qa_circuit_residual_exclusion h hD hI exactplus hS occurs
  refine ⟨S,?_⟩
  intro w
  have hw := large w
  dsimp only at hw
  rw [mask_eq w] at hw
  have h0 : cap7_decode 11 = qa_nb 0 := by decide +kernel
  have h1 : cap7_decode 69 = qa_nb 1 := by decide +kernel
  have h3 : cap7_decode 49 = qa_nb 3 := by decide +kernel
  simpa only [h0,h1,h3] using hw

theorem qa_q2_exclusion {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hI : ineligSet 14 D = {0,1,2,3})
    (hM : equality_missing_points D = {2,4,5,6})
    (hplus : Bplus 14 D ≤ 13) (hS : totalSurplus 14 D ≤ 14) : False := by
  exact qa_q2_conditional_exclusion h hD hI hM hplus hS q2f_certificate_all

end PEqualNP.Outside.L_meta_6659_aux
