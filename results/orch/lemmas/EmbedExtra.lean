import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_2592

def extraIndex (n i : ℕ) : ℕ := if i < n then i else i + 1

def extraGate (n : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (extraIndex n)⟩

def extraCircuit (n : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.map (extraGate n), extraIndex n C.output⟩

lemma extra_read (xs ys : List Bool) (b : Bool) (i : ℕ) :
    (xs ++ b :: ys).getD (extraIndex xs.length i) false =
      (xs ++ ys).getD i false := by
  unfold extraIndex
  split_ifs with h
  · rw [List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ h]
  · rw [List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega)]
    have eq : i + 1 - xs.length = (i - xs.length) + 1 := by omega
    rw [eq]
    simp

def extraStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma extra_step (xs ys : List Bool) (b : Bool) (g : Gate) :
    extraStep (xs ++ b :: ys) (extraGate xs.length g) =
      xs ++ b :: (ys ++ [g.op.eval (g.inputs.map fun i => (xs ++ ys).getD i false)]) := by
  simp only [extraStep, extraGate, List.map_map, Function.comp_def]
  have values : g.inputs.map (fun i => (xs ++ b :: ys).getD (extraIndex xs.length i) false) =
      g.inputs.map (fun i => (xs ++ ys).getD i false) := by
    apply List.map_congr_left
    intro i hi
    exact extra_read xs ys b i
  change (xs ++ b :: ys) ++ [_] = _
  rw [values]
  simp only [List.append_assoc, List.cons_append]

lemma extra_fold (gs : List Gate) (xs ys : List Bool) (b : Bool) :
    ∃ zs : List Bool,
      gs.foldl extraStep (xs ++ ys) = xs ++ zs ∧
      (gs.map (extraGate xs.length)).foldl extraStep (xs ++ b :: ys) = xs ++ b :: zs := by
  induction gs generalizing ys with
  | nil => exact ⟨ys, rfl, rfl⟩
  | cons g gs ih =>
    obtain ⟨zs, old, new⟩ := ih
      (ys ++ [g.op.eval (g.inputs.map fun i => (xs ++ ys).getD i false)])
    refine ⟨zs, ?_, ?_⟩
    · simpa only [List.foldl_cons, extraStep, List.append_assoc] using old
    · simpa only [List.map_cons, List.foldl_cons, extra_step] using new

lemma extra_eval (C : Circuit) (xs : List Bool) (b : Bool) :
    (extraCircuit xs.length C).eval (xs ++ [b]) = C.eval xs := by
  obtain ⟨zs, old, new⟩ := extra_fold C.gates xs [] b
  simp only [List.append_nil] at old new
  change ((C.gates.map (extraGate xs.length)).foldl extraStep (xs ++ [b])).getD
      (extraIndex xs.length C.output) false = (C.gates.foldl extraStep xs).getD C.output false
  rw [old, new]
  exact extra_read xs zs b C.output

lemma extra_eval_ofFn (n : ℕ) (C : Circuit) (x : Fin n → Bool) (b : Bool) :
    (extraCircuit n C).eval (List.ofFn x ++ [b]) = C.eval (List.ofFn x) := by
  simpa only [List.length_ofFn] using extra_eval C (List.ofFn x) b

lemma extra_fan (n : ℕ) (C : Circuit) (fan : FanInTwo C) :
    FanInTwo (extraCircuit n C) := by
  intro g hg
  obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hg
  simpa only [extraGate, List.length_map] using fan h hh

lemma extra_size (n : ℕ) (C : Circuit) : (extraCircuit n C).size = C.size := by
  simp only [extraCircuit, Circuit.size, List.length_map]

lemma extra_not_count (n : ℕ) (C : Circuit) :
    PEqualNP.NotBracket.notCount (extraCircuit n C) = PEqualNP.NotBracket.notCount C := by
  unfold PEqualNP.NotBracket.notCount extraCircuit
  rw [List.filter_map]
  simp only [extraGate, List.length_map, Function.comp_def]
  congr 2

end PEqualNP.Outside.L_meta_2592
