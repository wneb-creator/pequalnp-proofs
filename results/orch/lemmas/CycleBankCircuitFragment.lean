namespace PEqualNP.Outside.L_meta_2592.Signed.Extended

def cycleFn (x : Fin 6 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
  (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 0)
def cycleAssign (r : Row) (q : Fin 6) : Bool := bit r (cyclePin q)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma cycle_target_bits : ∀ r : Row, bit r cycleTarget = cycleFn (cycleAssign r) := by
  decide +kernel

lemma realizeCycleBank (C : PEqualNP.CircuitLowerBounds.Circuit)
    (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 6 → Bool,
      C.eval (List.ofFn x ++ [x 0 || x 3, x 1 || x 4, x 2 || x 5]) = cycleFn x) :
    ∃ k S, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true cycleTarget k S ∧
      ∀ v ∈ S, v ∈ cyclePins ∨ v ∈ oppositeBank := by
  let extra := cyclePins ++ oppositeBank
  have pinsEq : cyclePins = List.ofFn cyclePin := by decide +kernel
  have rowPins : ∀ r : Row, cyclePins.map (bit r) = List.ofFn (cycleAssign r) := by
    intro r
    rw [pinsEq, List.map_ofFn]
    rfl
  have rowExtra : ∀ r : Row, extra.map (bit r) = List.ofFn (cycleAssign r) ++
      [cycleAssign r 0 || cycleAssign r 3, cycleAssign r 1 || cycleAssign r 4,
        cycleAssign r 2 || cycleAssign r 5] := by
    intro r
    simp only [extra, List.map_append, rowPins, oppositeBank, List.map_cons, List.map_nil,
      bit_bin]
    rfl
  have he : (execute C.gates extra).getD C.output zero = cycleTarget := by
    apply bit_ext
    intro r
    rw [← b_read, execute_bits _ _ _ (fun g hg => (legal g hg).1)]
    change (C.wires (extra.map (bit r))).getD C.output false = _
    rw [rowExtra]
    exact (computes _).trans (cycle_target_bits r).symm
  have hp : proper cycleTarget := by unfold proper; decide +kernel
  have out := get_rep (u := true) (execute C.gates extra) C.output
  rw [he] at out
  unfold Repr at out
  rw [nrm_id (show bit 0 cycleTarget = false by decide +kernel)] at out
  obtain ⟨k, S, hk, run, hs⟩ := extract C.gates extra legal (u := true) (by simp) hp
    (out.resolve_right (fun h => h hp))
  have ns : extra.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at hs
  exact ⟨k, S, hk, run, fun v hv => List.mem_append.mp (hs v hv)⟩

end PEqualNP.Outside.L_meta_2592.Signed.Extended

namespace PEqualNP.Outside.L_meta_2592.Signed

lemma cycle_bank_binary (C : PEqualNP.CircuitLowerBounds.Circuit)
    (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 6 → Bool,
      C.eval (List.ofFn x ++ [x 0 || x 3, x 1 || x 4, x 2 || x 5]) = Extended.cycleFn x) :
    7 + PEqualNP.NotBracket.notCount C ≤ C.size := by
  obtain ⟨k, S, hk, run, raw⟩ := Extended.realizeCycleBank C legal computes
  have floor := cycle_bank_floor raw run
  have sameNot :
      (fun g : PEqualNP.CircuitLowerBounds.Gate => @decide
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.not)
        (PEqualNP.CircuitLowerBounds.lineDegreeGateOpDecEq g.op
          PEqualNP.CircuitLowerBounds.GateOp.not)) = Extended.isNot := by
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
