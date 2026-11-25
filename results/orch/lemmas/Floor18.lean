import Retention
import Restriction

namespace PEqualNP.Outside.L_meta_2592_aux.SignedFloor

lemma selected_pin_zero (j : Fin 10) :
    restrictRows (rowsFor j) (Extended.observe (Extended.pins.getD j.val Extended.zero)) =
      (fun _ => false) := by
  rw [observe_projectFor, projectFor_pin]
  funext r
  simp [observe, bit, zero]

lemma firstNonOrFloor {k U a b d}
    (apin : a ∈ Extended.pins) (bpin : b ∈ Extended.pins) (hab : a ≠ b)
    (hd : Extended.allowed true d) (nonOr : d ≠ 1)
    (uraw : ∀ z ∈ U, z ∈ Extended.pins)
    (fresh : Extended.bin d a b ∉ insert a (insert b U))
    (tail : Extended.Live true Extended.target k (insert (Extended.bin d a b) U)) :
    18 ≤ k + 1 := by
  classical
  have dsmall : d < 4 := by rcases hd with h | ⟨_, h⟩ <;> omega
  have retained := Extended.first_both_retained apin bpin hab hd uraw tail
  let rest := ((U.erase a).erase b).toList
  let ka := decide (a ∈ U)
  let kb := decide (b ∈ U)
  let bank := kept ka a (kept kb b rest)
  let front := Extended.bin d a b :: bank
  have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
  have ar : a ∉ rest := by simp [rest]
  have br : b ∉ rest := by simp [rest]
  have hr : rest.Nodup := Finset.nodup_toList _
  have bm := kept_nd kb b rest hr br
  have am : a ∉ kept kb b rest := by cases h : kb <;> simp [kept, h, hab, ar]
  have ndBank : bank.Nodup := kept_nd ka a _ bm am
  have bankFin : bank.toFinset = U := by
    change (kept ka a (kept kb b rest)).toFinset = U
    rw [Extended.kept_fin, Extended.kept_fin, er]
    ext z
    by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;>
      by_cases za : z = a <;> by_cases zb : z = b <;> simp_all [ka, kb]
  have nf : Extended.bin d a b ∉ bank := by
    intro hz
    exact fresh (Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (bankFin ▸ List.mem_toFinset.mpr hz)))
  have nd : front.Nodup := List.nodup_cons.mpr ⟨nf, ndBank⟩
  have eqFront : front.toFinset = insert (Extended.bin d a b) U := by
    simp [front, bankFin]
  have tailRun := Extended.list_run tail front nd eqFront
  change Run true (Extended.observe Extended.target) k
    ((Extended.bin d a b :: kept ka a (kept kb b rest)).map Extended.observe) at tailRun
  rw [List.map_cons, map_kept, map_kept, Extended.obs_bin] at tailRun
  have choice : ∃ j : Fin 10,
      ((Constant (restrictRows (rowsFor j) (Extended.observe a)) ∧ ka = true) ∨
       (Constant (restrictRows (rowsFor j) (Extended.observe b)) ∧ kb = true)) ∧
      Constant (restrictRows (rowsFor j) (comb d (Extended.observe a) (Extended.observe b))) := by
    have dc : d = 0 ∨ d = 2 ∨ d = 3 := by omega
    rcases dc with rfl | rfl | rfl
    · obtain ⟨j, hj⟩ := pin_index a apin
      have hz : restrictRows (rowsFor j) (Extended.observe a) = (fun _ => false) := by
        rw [← hj]
        exact selected_pin_zero j
      refine ⟨j, ⟨Or.inl ⟨⟨false, hz⟩, by simp [ka, retained.1]⟩, ?_⟩⟩
      rw [restrict_comb, hz]
      exact ⟨false, by funext r; simp [comb, combine]⟩
    · obtain ⟨j, hj⟩ := pin_index a apin
      have hz : restrictRows (rowsFor j) (Extended.observe a) = (fun _ => false) := by
        rw [← hj]
        exact selected_pin_zero j
      refine ⟨j, ⟨Or.inl ⟨⟨false, hz⟩, by simp [ka, retained.1]⟩, ?_⟩⟩
      rw [restrict_comb, hz]
      exact ⟨false, by funext r; simp [comb, combine]⟩
    · obtain ⟨j, hj⟩ := pin_index b bpin
      have hz : restrictRows (rowsFor j) (Extended.observe b) = (fun _ => false) := by
        rw [← hj]
        exact selected_pin_zero j
      refine ⟨j, ⟨Or.inr ⟨⟨false, hz⟩, by simp [kb, retained.2]⟩, ?_⟩⟩
      rw [restrict_comb, hz]
      exact ⟨false, by funext r; simp [comb, combine]⟩
  obtain ⟨j, hconstant, hresult⟩ := choice
  have supplyRoots : supply true (inputs.map observe)
      (((Extended.observe a :: Extended.observe b :: rest.map Extended.observe)).map
        (restrictRows (rowsFor j))) := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    rcases List.mem_cons.mp hw with rfl | hw
    · exact restriction_of_pin_is_available j a apin
    rcases List.mem_cons.mp hw with rfl | hw
    · exact restriction_of_pin_is_available j b bpin
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hw
    apply restriction_of_pin_is_available j z
    apply uraw z
    have hfin : z ∈ (U.erase a).erase b := by simpa [rest] using hz
    exact (Finset.mem_erase.mp (Finset.mem_erase.mp hfin).2).2
  have same := restriction_of_goal j
  have need := projected_bound_retained_result (rowsFor j) hd tailRun
    (same ▸ observe_proper graph_proper) Reach.start supplyRoots hconstant hresult
    (L := 15) (same ▸ nineFloor)
  omega

end PEqualNP.Outside.L_meta_2592_aux.SignedFloor
