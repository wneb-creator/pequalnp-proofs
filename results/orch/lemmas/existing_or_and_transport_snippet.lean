namespace PEqualNP.Outside.L_meta_2592_aux.Binary16

open PEqualNP.Outside.L_meta_2592_aux

lemma suffixSixteenOrAnd_any (a b c : Fin 10) (hac : a ≠ c) (hbc : b ≠ c)
    (t : Fin 2) (k : ℕ) (S : Finset Extended.Sig)
    (run : Extended.Live true Extended.target k S)
    (hextra : Extended.bin (2 * t.val) (inputPin c) (inputPin a ||| inputPin b) ∈ S)
    (raw : ∀ v ∈ S, v ∈ Extended.pins ++ [inputPin a ||| inputPin b,
      Extended.bin (2 * t.val) (inputPin c) (inputPin a ||| inputPin b)]) : 16 ≤ k := by
  classical
  obtain ⟨hzero,hsecond,hbij,hadj⟩ := pairMove_properties c a (Ne.symm hac)
  let e : Fin 10 ≃ Fin 10 := Equiv.ofBijective (pairMove c a) hbij
  have ec : e.symm c = 0 := by
    apply e.injective
    simpa [e] using hzero.symm
  have ea : e.symm a ≠ 0 := by
    intro hh
    apply hac
    exact e.symm.injective (hh.trans ec.symm)
  have eb : e.symm b ≠ 0 := by
    intro hh
    apply hbc
    exact e.symm.injective (hh.trans ec.symm)
  have haPos : 0 < (e.symm a).val := by
    by_contra hn
    apply ea
    apply Fin.ext
    simp only [Fin.val_zero]
    omega
  have hbPos : 0 < (e.symm b).val := by
    by_contra hn
    apply eb
    apply Fin.ext
    simp only [Fin.val_zero]
    omega
  let i : Fin 9 := ⟨(e.symm a).val - 1, by have := (e.symm a).isLt; omega⟩
  let j : Fin 9 := ⟨(e.symm b).val - 1, by have := (e.symm b).isLt; omega⟩
  have ei : inputPin (e.symm a) = orAndPin i := by
    unfold inputPin orAndPin
    congr 1
    dsimp [i]
    omega
  have ej : inputPin (e.symm b) = orAndPin j := by
    unfold inputPin orAndPin
    congr 1
    dsimp [j]
    omega
  have hp : ∀ x : Fin 10 → Bool,
      edgeFunction (fun q => x (e.symm q)) = edgeFunction x := by
    intro x
    have hh := edgeFunction_pairMove c a (Ne.symm hac) (fun q => x (e.symm q))
    change edgeFunction (fun q => x (e.symm (e q))) =
      edgeFunction (fun q => x (e.symm q)) at hh
    simpa only [Equiv.symm_apply_apply] using hh.symm
  let φ : Extended.Sig → Extended.Sig := RowEncoding.transform e.symm
  have moved := map_live run φ (RowEncoding.transform_injective e.symm e.symm.surjective)
    (RowEncoding.transform_zero e.symm) (RowEncoding.transform_one e.symm)
    (transform_bin e.symm)
  have ht : φ Extended.target = Extended.target := transform_target e.symm hp
  rw [ht] at moved
  have hseed : φ (inputPin a ||| inputPin b) = orAndSeed i j := by
    change RowEncoding.transform e.symm (inputPin a ||| inputPin b) = _
    rw [RowEncoding.transform_or,transform_pin,transform_pin,ei,ej]
    rfl
  have hx : φ (Extended.bin (2 * t.val) (inputPin c) (inputPin a ||| inputPin b)) =
      orAndExtra i j t := by
    change RowEncoding.transform e.symm (Extended.bin (2 * t.val) (inputPin c)
      (inputPin a ||| inputPin b)) = _
    rw [transform_bin,transform_pin,ec]
    change Extended.bin (2 * t.val) Extended.first (φ (inputPin a ||| inputPin b)) = _
    rw [hseed]
    rfl
  apply suffixSixteenOrAnd i j t moved
  · intro v hv
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    rcases List.mem_append.mp (raw w hw) with hr | hr
    · obtain ⟨q,rfl⟩ := member_pin hr
      apply List.mem_append_left
      change RowEncoding.transform e.symm (inputPin q) ∈ Extended.pins
      rw [transform_pin]
      exact pin_mem _
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · rw [hseed]
        simp
      · rw [hx]
        simp
  · exact hx ▸ Finset.mem_image.mpr ⟨_,hextra,rfl⟩

end PEqualNP.Outside.L_meta_2592_aux.Binary16
