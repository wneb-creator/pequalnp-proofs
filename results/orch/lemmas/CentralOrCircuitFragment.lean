namespace PEqualNP.Outside.L_meta_2592.Signed.Extended

lemma realizeCentralOrs (C : PEqualNP.CircuitLowerBounds.Circuit)
    (legal : PEqualNP.MetaComplexity.FanInTwo C) (i : Fin 10) (leaves : List (Fin 10))
    (computes : ∀ x : Fin 10 → Bool,
      C.eval (List.ofFn x ++ leaves.map (fun w => x i || x w)) = f10 x) :
    ∃ k S, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true target k S ∧
      ∀ v ∈ S, v ∈ pins ∨ ∃ w ∈ leaves,
        v = bin 1 (pins.getD i.val zero) (pins.getD w.val zero) := by
  let extra := pins ++ leaves.map (fun w => bin 1 (pins.getD i.val zero) (pins.getD w.val zero))
  have rowPins : ∀ r : Row, pins.map (bit r) = List.ofFn (assign r) := by
    intro r
    conv_lhs => rw [pins_as_ofFn]
    simp only [List.map_ofFn]
    rfl
  have rowExtra : ∀ r : Row, extra.map (bit r) =
      List.ofFn (assign r) ++ leaves.map (fun w => assign r i || assign r w) := by
    intro r
    simp only [extra, List.map_append, List.map_map, rowPins]
    congr 1
    apply List.map_congr_left
    intro w hw
    simp [Function.comp_def, bit_bin, assign]
  have he : (execute C.gates extra).getD C.output zero = target := by
    apply bit_ext
    intro r
    rw [← b_read, execute_bits _ _ _ (fun g hg => (legal g hg).1)]
    change (C.wires (extra.map (bit r))).getD C.output false = _
    rw [rowExtra]
    exact (computes _).trans (rowTarget r).symm
  have hp : proper target := by unfold proper; decide +kernel
  have out := get_rep (u := true) (execute C.gates extra) C.output
  rw [he] at out
  unfold Repr at out
  rw [nrm_id (show bit 0 target = false by decide +kernel)] at out
  obtain ⟨k, S, hk, run, hs⟩ := extract C.gates extra legal (u := true) (by simp) hp
    (out.resolve_right (fun h => h hp))
  have pinZeros : ∀ q : Fin 10, bit 0 (pins.getD q.val zero) = false := by decide +kernel
  have pinsPlain : pins.all plainWord = true := by decide +kernel
  have ns : extra.all plainWord = true := by
    simp only [extra, List.all_append, pinsPlain, Bool.true_and, List.all_map,
      List.all_eq_true]
    intro w hw
    change !(bit 0 (bin 1 (pins.getD i.val zero) (pins.getD w.val zero))) = true
    rw [bit_bin, pinZeros i, pinZeros w]
    rfl
  rw [nrm_map ns] at hs
  refine ⟨k, S, hk, run, ?_⟩
  intro v hv
  rcases List.mem_append.mp (hs v hv) with ordinary | supplied
  · exact Or.inl ordinary
  · obtain ⟨w, hw, eq⟩ := List.mem_map.mp supplied
    exact Or.inr ⟨w, hw, eq.symm⟩

end PEqualNP.Outside.L_meta_2592.Signed.Extended

namespace PEqualNP.Outside.L_meta_2592.Signed

lemma triple_or_binary (C : PEqualNP.CircuitLowerBounds.Circuit)
    (legal : PEqualNP.MetaComplexity.FanInTwo C) (i j c d : Fin 10)
    (nd : ([i,j,c,d] : List (Fin 10)).Nodup)
    (jc : Extended.petAdjacent j c = false) (jd : Extended.petAdjacent j d = false)
    (cd : Extended.petAdjacent c d = false)
    (neighbor : Extended.petAdjacent i j = true ∨ Extended.petAdjacent i c = true ∨
      Extended.petAdjacent i d = true)
    (computes : ∀ x : Fin 10 → Bool,
      C.eval (List.ofFn x ++ [x i || x j, x i || x c, x i || x d]) = Extended.f10 x) :
    16 + PEqualNP.NotBracket.notCount C ≤ C.size := by
  obtain ⟨k, S, hk, run, raw⟩ := Extended.realizeCentralOrs C legal i [j,c,d] computes
  have floor := triple_or_floor i j c d nd jc jd cd neighbor raw run
  have sameNot :
      (fun g : PEqualNP.CircuitLowerBounds.Gate => @decide
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.not)
        (PEqualNP.CircuitLowerBounds.lineDegreeGateOpDecEq g.op PEqualNP.CircuitLowerBounds.GateOp.not)) = Extended.isNot := by
    funext g
    obtain ⟨op, operands⟩ := g
    cases op <;> rfl
  have negSame : (fun g : PEqualNP.CircuitLowerBounds.Gate => decide (¬ Extended.isNot g = true)) =
      (fun g => !Extended.isNot g) := by
    funext g
    cases Extended.isNot g <;> rfl
  have count := List.length_eq_countP_add_countP Extended.isNot (l := C.gates)
  rw [negSame] at count
  unfold PEqualNP.NotBracket.notCount PEqualNP.CircuitLowerBounds.Circuit.size
  rw [sameNot, ← List.countP_eq_length_filter]
  omega

end PEqualNP.Outside.L_meta_2592.Signed
