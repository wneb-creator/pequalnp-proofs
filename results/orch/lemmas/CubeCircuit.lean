import NegOrReassociate

namespace PEqualNP.Outside.L_meta_2592.FewNot.Extended

open PEqualNP.CircuitLowerBounds

lemma negative_or_cube_floor_all {a b c : Sig}
    (ha : a ∈ pins) (hb : b ∈ pins) (hc : c ∈ pins)
    {k : Nat} {S : Finset Sig} (run : Live true target k S)
    (raw : ∀ v ∈ S, v ∈ pins ∨ v = bin 2 c (bin 1 a b)) : 16 ≤ k := by
  by_cases h : c = a
  · have hz : bin 2 c (bin 1 a b) = zero := by
      apply bit_ext
      intro r
      simp only [h,bit_bin,bit_zero]
      cases bit r a <;> cases bit r b <;> decide
    have floor := PEqualNP.Outside.L_meta_2592.FewNot.pins_seventeen run (by
      intro v hv
      rcases raw v hv with hp | he
      · exact hp
      · exact False.elim ((live_proper run v hv).1 (he.trans hz)))
    omega
  · exact negative_or_cube_floor ha hb hc h run raw

lemma cube_row_inputs (r : Row) : pins.map (bit r) = List.ofFn (assign r) := by
  rw [← PEqualNP.Outside.L_meta_2592.FewNot.pins_ofFn,List.map_ofFn]
  rfl

lemma free_negative_or_cube_floor (i j l : Fin 10) (C : Circuit)
    (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 10 → Bool,
      C.eval (List.ofFn x ++ [x l && !(x i || x j)]) = f10 x) :
    16 ≤ C.gates.countP (fun g => !isNot g) := by
  let a := PEqualNP.Outside.L_meta_2592.FewNot.pin i
  let b := PEqualNP.Outside.L_meta_2592.FewNot.pin j
  let c := PEqualNP.Outside.L_meta_2592.FewNot.pin l
  let z := bin 2 c (bin 1 a b)
  let roots := pins ++ [z]
  have ha : a ∈ pins := PEqualNP.Outside.L_meta_2592.FewNot.pin_mem i
  have hb : b ∈ pins := PEqualNP.Outside.L_meta_2592.FewNot.pin_mem j
  have hc : c ∈ pins := PEqualNP.Outside.L_meta_2592.FewNot.pin_mem l
  have row (r : Row) : roots.map (bit r) =
      List.ofFn (assign r) ++ [assign r l && !(assign r i || assign r j)] := by
    simp only [roots,List.map_append,List.map_cons,List.map_nil,cube_row_inputs]
    congr 2
    simp [z,c,a,b,bit_bin,assign,PEqualNP.Outside.L_meta_2592.FewNot.pin]
  have he : (execute C.gates roots).getD C.output zero = target := by
    apply bit_ext
    intro r
    rw [← b_read,execute_bits _ _ _ (fun g hg => (legal g hg).1)]
    change (C.wires (roots.map (bit r))).getD C.output false = _
    rw [row]
    exact (computes _).trans (rowTarget r).symm
  have hp : proper target := by unfold proper; decide +kernel
  have out := get_rep (u := true) (execute C.gates roots) C.output
  rw [he] at out
  unfold Repr at out
  rw [nrm_id (show bit 0 target = false by decide +kernel)] at out
  obtain ⟨k,S,hk,run,hS⟩ := extract C.gates roots legal (u := true) (by simp) hp
    (out.resolve_right (fun h => h hp))
  have normal : roots.map (nrm true) = roots := by
    have eq : roots.map (nrm true) = roots.map id := by
      apply List.map_congr_left
      intro v hv
      apply nrm_id
      simp only [roots,List.mem_append,List.mem_singleton] at hv
      rcases hv with hv | rfl
      · exact pin_zero_bit hv
      · simp [z,bit_bin,pin_zero_bit ha,pin_zero_bit hb,pin_zero_bit hc]
    rw [eq,List.map_id]
  rw [normal] at hS
  have floor := negative_or_cube_floor_all ha hb hc run (by
    intro v hv
    simpa [roots,z] using hS v hv)
  exact floor.trans hk

end PEqualNP.Outside.L_meta_2592.FewNot.Extended
