import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux.Pad

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def shiftWire (n i : ℕ) : ℕ := if i < n then i else i + 1

def shiftGate (n : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (shiftWire n)⟩

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

def padNot (n : ℕ) (C : Circuit) : Circuit :=
  ⟨⟨GateOp.not, []⟩ :: C.gates.map (shiftGate n), shiftWire n C.output⟩

lemma readShift (xs ys : List Bool) (i : ℕ) :
    (xs ++ true :: ys).getD (shiftWire xs.length i) false =
      (xs ++ ys).getD i false := by
  induction xs generalizing i with
  | nil => simp [shiftWire]
  | cons a xs ih =>
    cases i with
    | zero => simp [shiftWire]
    | succ i =>
      by_cases h : i < xs.length
      · simpa [shiftWire, h, Nat.succ_lt_succ_iff] using ih i
      · simpa [shiftWire, h, Nat.succ_lt_succ_iff, Nat.add_assoc] using ih i

lemma runShift (gs : List Gate) (xs ys : List Bool) :
    ∃ zs, run gs (xs ++ ys) = xs ++ zs ∧
      run (gs.map (shiftGate xs.length)) (xs ++ true :: ys) = xs ++ true :: zs := by
  induction gs generalizing ys with
  | nil => exact ⟨ys, rfl, rfl⟩
  | cons g gs ih =>
    let v := g.op.eval (g.inputs.map fun i => (xs ++ ys).getD i false)
    obtain ⟨zs, orig, shifted⟩ := ih (ys ++ [v])
    have value : (shiftGate xs.length g).op.eval
        ((shiftGate xs.length g).inputs.map fun i => (xs ++ true :: ys).getD i false) = v := by
      dsimp [shiftGate, v]
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact readShift xs ys i
    refine ⟨zs, ?_, ?_⟩
    · simpa only [run, List.foldl_cons, v, List.append_assoc] using orig
    · change run (gs.map (shiftGate xs.length))
        ((xs ++ true :: ys) ++ [(shiftGate xs.length g).op.eval
          ((shiftGate xs.length g).inputs.map fun i => (xs ++ true :: ys).getD i false)]) = _
      rw [value]
      simpa only [List.append_assoc, List.cons_append] using shifted

lemma padNot_eval (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (padNot n C).eval (List.ofFn x) = C.eval (List.ofFn x) := by
  let xs := List.ofFn x
  have len : xs.length = n := List.length_ofFn
  obtain ⟨zs, orig, shifted⟩ := runShift C.gates xs []
  have orig' : run C.gates xs = xs ++ zs := by simpa using orig
  have shifted' : run (C.gates.map (shiftGate n)) (xs ++ [true]) = xs ++ true :: zs := by
    simpa only [len, List.append_nil] using shifted
  change (run (C.gates.map (shiftGate n)) (xs ++ [true])).getD
    (shiftWire n C.output) false = (run C.gates xs).getD C.output false
  rw [orig', shifted']
  simpa only [len] using readShift xs zs C.output

lemma padNot_size (n : ℕ) (C : Circuit) : (padNot n C).size = C.size + 1 := by
  simp [padNot, Circuit.size]

lemma padNot_hasNot (n : ℕ) (C : Circuit) :
    ∃ g ∈ (padNot n C).gates, g.op = GateOp.not :=
  ⟨⟨GateOp.not, []⟩, List.mem_cons_self, rfl⟩

lemma padNot_fan (n : ℕ) (C : Circuit) (fan : FanInTwo C) : FanInTwo (padNot n C) := by
  intro g mem
  rcases List.mem_cons.mp mem with rfl | mem
  · simp
  · obtain ⟨h, hm, he⟩ := List.mem_map.mp mem
    subst g
    obtain ⟨basis, arity⟩ := fan h hm
    exact ⟨basis, by simpa [shiftGate] using arity⟩

lemma padNot_last (n : ℕ) (C : Circuit) (positive : 0 < C.size)
    (last : C.output + 1 = n + C.size) :
    (padNot n C).output + 1 = n + (padNot n C).size := by
  have after : ¬ C.output < n := by omega
  rw [padNot_size]
  simp only [padNot, shiftWire, ite_eq_right after]
  omega

end PEqualNP.Outside.L_meta_2592_aux.Pad
