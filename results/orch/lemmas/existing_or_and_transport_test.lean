import Binary17Integration
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PEqualNP.Outside.L_meta_2592_aux.Binary16

def orAndPin (i : Fin 9) : Extended.Sig := Extended.pins.getD (i.val + 1) Extended.zero

def orAndSeed (i j : Fin 9) : Extended.Sig := orAndPin i ||| orAndPin j

def orAndExtra (i j : Fin 9) (t : Fin 2) : Extended.Sig :=
  Extended.bin (2 * t.val) Extended.first (orAndSeed i j)

def orAndWitnessA (i j : Fin 9) (t : Fin 2) : Extended.Row :=
  ([16, 128, 16, 48, 16, 128, 16, 64, 64, 16, 16, 20, 16, 65, 16, 72, 16, 18, 16, 48, 16, 48, 16, 48, 16, 48, 64, 16, 16, 20, 16, 48, 16, 48, 16, 18, 16, 128, 16, 48, 16, 272, 16, 64, 64, 16, 16, 20, 16, 65, 16, 72, 16, 18, 16, 64, 16, 48, 16, 64, 16, 64, 128, 16, 16, 20, 16, 64, 16, 64, 16, 18, 64, 16, 64, 16, 64, 16, 128, 16, 64, 16, 64, 16, 64, 16, 64, 16, 64, 16, 16, 20, 16, 20, 16, 20, 16, 20, 64, 16, 16, 20, 16, 20, 16, 20, 16, 18, 16, 65, 16, 48, 16, 65, 16, 64, 64, 16, 16, 20, 16, 65, 16, 65, 16, 18, 16, 72, 16, 48, 16, 72, 16, 64, 64, 16, 16, 20, 16, 65, 16, 72, 16, 18, 16, 18, 16, 18, 16, 18, 16, 18, 64, 16, 16, 18, 16, 18, 16, 18, 16, 18] : List Extended.Row).getD ((i.val * 9 + j.val) * 2 + t.val) 0

def orAndWitnessB (i j : Fin 9) (t : Fin 2) : Extended.Row := orAndWitnessA i j t + 512

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma orAndWitness : ∀ (i j : Fin 9) (t : Fin 2),
    Extended.bit (orAndWitnessA i j t) Extended.target ≠
      Extended.bit (orAndWitnessB i j t) Extended.target ∧
    (Extended.pins ++ [orAndSeed i j, orAndExtra i j t]).all (fun a =>
      (Extended.bit (orAndWitnessA i j t) a == Extended.bit (orAndWitnessB i j t) a) ||
      (a == Extended.first)) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma orAndProjects : ∀ (i j : Fin 9) (t : Fin 2),
    projected (orAndExtra i j t) = zero ∧ orAndExtra i j t ≠ Extended.first ∧
    (Extended.pins ++ [orAndSeed i j, orAndExtra i j t]).all (fun a =>
      (projected a == zero) || inputs.contains (projected a) ||
      (projected a == projected (orAndSeed i j))) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma orAndPinProjects : ∀ i : Fin 9, projected (orAndPin i) ∈ inputs := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma orAndSeedProjects : ∀ i j : Fin 9,
    projected (orAndSeed i j) = bin 1 (projected (orAndPin i)) (projected (orAndPin j)) := by
  decide +kernel

lemma suffixSixteenOrAnd (i j : Fin 9) (t : Fin 2) {k S}
    (run : Extended.Live true Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ Extended.pins ++ [orAndSeed i j, orAndExtra i j t])
    (hextra : orAndExtra i j t ∈ S) : 16 ≤ k := by
  classical
  have hfirst : Extended.first ∈ S := by
    obtain ⟨a, ha, hchange⟩ := Extended.live_row_difference run (orAndWitness i j t).1
    have chk := List.all_eq_true.mp (orAndWitness i j t).2 a (raw a ha)
    simp only [Bool.or_eq_true, beq_iff_eq] at chk
    exact chk.resolve_left hchange ▸ ha
  have hne := (orAndProjects i j t).2.1
  let front := Extended.first :: orAndExtra i j t ::
    ((S.erase Extended.first).erase (orAndExtra i j t)).toList
  have nd : front.Nodup := by
    simp [front, hne, Ne.symm hne]
    exact Finset.nodup_toList _
  have eqS : front.toFinset = S := by
    ext a
    by_cases ha : a = Extended.first <;> by_cases hb : a = orAndExtra i j t <;>
      simp [front, ha, hb, hfirst, hextra]
  have hrun := Extended.list_run run front nd eqS
  have same : restrictRows embed (Extended.observe Extended.target) = observe graph := by
    rw [observe_projected]
    exact congrArg observe (by decide +kernel)
  have isZero : observe zero = fun _ => false := by funext r; simp [observe, bit, zero]
  let bank := observe (projected (orAndSeed i j)) :: inputs.map observe
  have paid : Reach true (inputs.map observe) 1 bank := by
    dsimp [bank]
    rw [orAndSeedProjects, obs_bin]
    change Reach true (inputs.map observe) 1
      (combine true (observe (projected (orAndPin i))) (observe (projected (orAndPin j))) :: inputs.map observe)
    exact Reach.two true Reach.start
      (Or.inl (List.mem_map.mpr ⟨_, orAndPinProjects i, rfl⟩))
      (Or.inl (List.mem_map.mpr ⟨_, orAndPinProjects j, rfl⟩))
  have supplyRoots : supply true bank
      ((front.map Extended.observe).map (restrictRows embed)) := by
    intro v hv
    obtain ⟨_, hin, rfl⟩ := List.mem_map.mp hv
    obtain ⟨a, hmFront, rfl⟩ := List.mem_map.mp hin
    rw [observe_projected]
    have hh := List.all_eq_true.mp (orAndProjects i j t).2.2 a
      (raw a (eqS ▸ List.mem_toFinset.mpr hmFront))
    simp only [Bool.or_eq_true, beq_iff_eq] at hh
    rcases hh with (hz | hm) | he
    · exact Or.inr (Or.inl ⟨false, hz ▸ isZero⟩)
    · exact Or.inl (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨_, by simpa using hm, rfl⟩))
    · exact Or.inl (he ▸ List.mem_cons_self)
  have need := projected_bound embed hrun (same ▸ observe_proper graph_proper)
    paid supplyRoots (L := 15) (same ▸ nineFloor)
  have charge : 2 ≤ mass ((front.map Extended.observe).map (restrictRows embed)) := by
    have ac : Constant (restrictRows embed (Extended.observe Extended.first)) := by
      rw [observe_projected, show projected Extended.first = zero by decide +kernel]
      exact ⟨false, isZero⟩
    have bc : Constant (restrictRows embed (Extended.observe (orAndExtra i j t))) := by
      rw [observe_projected, (orAndProjects i j t).1]
      exact ⟨false, isZero⟩
    simp [front, mass_cons, cost, ac, bc]
    omega
  omega

end PEqualNP.Outside.L_meta_2592_aux.Binary16

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
