import Floor18
import OrFirst

namespace PEqualNP.Outside.L_meta_2592_aux.SignedFloor

lemma firstOrSecondAndFloor {k U a b c d}
    (apin : a ∈ Extended.pins) (bpin : b ∈ Extended.pins) (cpin : c ∈ Extended.pins)
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (hhc : Extended.bin 1 a b ≠ c)
    (hd : Extended.allowed true d) (ops : d = 0 ∨ d = 3)
    (uraw : ∀ z ∈ U, z ∈ Extended.pins ∨ z = Extended.bin 1 a b)
    (fresh : Extended.bin d (Extended.bin 1 a b) c ∉ insert (Extended.bin 1 a b) (insert c U))
    (tail : Extended.Live true Extended.target k (insert (Extended.bin d (Extended.bin 1 a b) c) U)) :
    18 ≤ k + 2 := by
  classical
  let h := Extended.bin 1 a b
  have hmc : h ≠ c := hhc
  have dsmall : d < 4 := by rcases ops with rfl | rfl <;> decide
  have retained := Extended.or_second_pin_retained apin bpin cpin hab hca hcb dsmall uraw tail
  let rest := ((U.erase h).erase c).toList
  let kh := decide (h ∈ U)
  let kc := decide (c ∈ U)
  let bank := kept kh h (kept kc c rest)
  let front := Extended.bin d h c :: bank
  have er : rest.toFinset = (U.erase h).erase c := by simp [rest]
  have ar : h ∉ rest := by simp [rest]
  have br : c ∉ rest := by simp [rest]
  have hr : rest.Nodup := Finset.nodup_toList _
  have bm := kept_nd kc c rest hr br
  have am : h ∉ kept kc c rest := by cases h : kc <;> simp [kept, h, hmc, ar]
  have ndBank : bank.Nodup := kept_nd kh h _ bm am
  have bankFin : bank.toFinset = U := by
    change (kept kh h (kept kc c rest)).toFinset = U
    rw [Extended.kept_fin, Extended.kept_fin, er]
    ext z
    by_cases aa : h ∈ U <;> by_cases bb : c ∈ U <;>
      by_cases za : z = h <;> by_cases zb : z = c <;> simp_all [kh, kc]
  have nf : Extended.bin d h c ∉ bank := by
    intro hz
    exact fresh (Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (bankFin ▸ List.mem_toFinset.mpr hz)))
  have nd : front.Nodup := List.nodup_cons.mpr ⟨nf, ndBank⟩
  have eqFront : front.toFinset = insert (Extended.bin d h c) U := by
    simp [front, bankFin]
  have tailRun := Extended.list_run tail front nd eqFront
  change Run true (Extended.observe Extended.target) k
    ((Extended.bin d h c :: kept kh h (kept kc c rest)).map Extended.observe) at tailRun
  rw [List.map_cons, map_kept, map_kept, Extended.obs_bin] at tailRun
  obtain ⟨j, hj⟩ := pin_index c cpin
  have hz : restrictRows (rowsFor j) (Extended.observe c) = (fun _ => false) := by
    rw [← hj]
    exact selected_pin_zero j
  have hconstant :
      (Constant (restrictRows (rowsFor j) (Extended.observe h)) ∧ kh = true) ∨
      (Constant (restrictRows (rowsFor j) (Extended.observe c)) ∧ kc = true) := by
    exact Or.inr ⟨⟨false, hz⟩, by simp [kc, retained]⟩
  have hresult : Constant
      (restrictRows (rowsFor j) (comb d (Extended.observe h) (Extended.observe c))) := by
    rw [restrict_comb, hz]
    rcases ops with rfl | rfl
    all_goals exact ⟨false, by funext r; simp [comb, combine]⟩
  let pa := restrictRows (rowsFor j) (Extended.observe a)
  let pb := restrictRows (rowsFor j) (Extended.observe b)
  let projectBank := combine true pa pb :: inputs.map observe
  have hproject : restrictRows (rowsFor j) (Extended.observe h) = combine true pa pb := by
    change restrictRows (rowsFor j) (Extended.observe (Extended.bin 1 a b)) = combine true pa pb
    rw [Extended.obs_bin, restrict_comb]
    rfl
  have reach : Reach true (inputs.map observe) 1 projectBank :=
    Reach.two true Reach.start (restriction_of_pin_is_available j a apin)
      (restriction_of_pin_is_available j b bpin)
  have availOfRaw : ∀ z, z ∈ Extended.pins ∨ z = h →
      Available true projectBank (restrictRows (rowsFor j) (Extended.observe z)) := by
    intro z hz
    rcases hz with hpin | rfl
    · exact available_cons _ (restriction_of_pin_is_available j z hpin)
    · rw [hproject]
      exact Or.inl (by simp [projectBank])
  have supplyRoots : supply true projectBank
      ((Extended.observe h :: Extended.observe c :: rest.map Extended.observe).map
        (restrictRows (rowsFor j))) := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    rcases List.mem_cons.mp hw with rfl | hw
    · exact availOfRaw h (Or.inr rfl)
    rcases List.mem_cons.mp hw with rfl | hw
    · exact availOfRaw c (Or.inl cpin)
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hw
    apply availOfRaw z
    apply uraw z
    have hfin : z ∈ (U.erase h).erase c := by simpa [rest] using hz
    exact (Finset.mem_erase.mp (Finset.mem_erase.mp hfin).2).2
  have same := restriction_of_goal j
  have need := projected_bound_retained_result (rowsFor j) hd tailRun
    (same ▸ observe_proper graph_proper) reach supplyRoots hconstant hresult
    (L := 15) (same ▸ nineFloor)
  omega

end PEqualNP.Outside.L_meta_2592_aux.SignedFloor
