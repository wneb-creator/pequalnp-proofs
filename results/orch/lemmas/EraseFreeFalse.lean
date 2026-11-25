import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux.EraseFalse

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def eraseWire (n budget i : ℕ) : ℕ :=
  if i < n then i else if i = n then n + budget else i - 1

def eraseGate (n budget : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (eraseWire n budget)⟩

def run (gs : List Gate) (xs : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) xs

def eraseFalse (n : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.map (eraseGate n C.size), eraseWire n C.size C.output⟩

lemma readErase (xs ys : List Bool) (budget i : ℕ) (small : ys.length ≤ budget) :
    (xs ++ ys).getD (eraseWire xs.length budget i) false =
      (xs ++ false :: ys).getD i false := by
  unfold eraseWire
  by_cases before : i < xs.length
  · rw [ite_eq_left before, List.getD_append _ _ _ _ before,
      List.getD_append _ _ _ _ before]
  · rw [ite_eq_right before]
    by_cases atFalse : i = xs.length
    · subst i
      rw [ite_eq_left rfl]
      rw [List.getD_eq_default _ _ (by simp only [List.length_append]; omega)]
      rw [List.getD_append_right _ _ _ _ (by omega)]
      simp
    · rw [ite_eq_right atFalse]
      have after : xs.length < i := by omega
      rw [List.getD_append_right _ _ _ _ (by omega)]
      rw [List.getD_append_right _ _ _ _ (by omega)]
      have index : i - xs.length = (i - 1 - xs.length) + 1 := by omega
      rw [index, List.getD_cons_succ]

lemma runErase (gs : List Gate) (xs ys : List Bool) (budget : ℕ)
    (small : ys.length + gs.length ≤ budget) :
    ∃ zs, run gs (xs ++ false :: ys) = xs ++ false :: zs ∧
      run (gs.map (eraseGate xs.length budget)) (xs ++ ys) = xs ++ zs ∧
      zs.length = ys.length + gs.length := by
  induction gs generalizing ys with
  | nil => exact ⟨ys, rfl, rfl, by simp⟩
  | cons g gs ih =>
    let v := g.op.eval (g.inputs.map fun i => (xs ++ false :: ys).getD i false)
    have bound : (ys ++ [v]).length + gs.length ≤ budget := by
      simp only [List.length_append, List.length_cons, List.length_nil] at small ⊢
      omega
    obtain ⟨zs, orig, erased, length⟩ := ih (ys ++ [v]) bound
    have value : (eraseGate xs.length budget g).op.eval
        ((eraseGate xs.length budget g).inputs.map fun i => (xs ++ ys).getD i false) = v := by
      dsimp [eraseGate, v]
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact readErase xs ys budget i (by simp only [List.length_cons] at small; omega)
    refine ⟨zs, ?_, ?_, ?_⟩
    · simpa only [run, List.foldl_cons, v, List.append_assoc, List.cons_append] using orig
    · change run (gs.map (eraseGate xs.length budget))
        ((xs ++ ys) ++ [(eraseGate xs.length budget g).op.eval
          ((eraseGate xs.length budget g).inputs.map fun i => (xs ++ ys).getD i false)]) = _
      rw [value]
      simpa only [List.append_assoc] using erased
    · simp only [List.length_append, List.length_cons, List.length_nil] at length ⊢
      omega

lemma eraseFalse_eval (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (eraseFalse n C).eval (List.ofFn x) = C.eval (List.ofFn x ++ [false]) := by
  let xs := List.ofFn x
  have len : xs.length = n := List.length_ofFn
  obtain ⟨zs, orig, erased, length⟩ := runErase C.gates xs [] C.size (by simp [Circuit.size])
  have orig' : run C.gates (xs ++ [false]) = xs ++ false :: zs := by
    simpa only [List.append_nil] using orig
  have erased' : run (C.gates.map (eraseGate n C.size)) xs = xs ++ zs := by
    simpa only [len, List.append_nil] using erased
  change (run (C.gates.map (eraseGate n C.size)) xs).getD
    (eraseWire n C.size C.output) false = (run C.gates (xs ++ [false])).getD C.output false
  rw [orig', erased']
  have bound : zs.length ≤ C.size := by simpa [Circuit.size] using length.le
  simpa only [len] using readErase xs zs C.size C.output bound

lemma eraseFalse_size (n : ℕ) (C : Circuit) : (eraseFalse n C).size = C.size := by
  simp [eraseFalse, Circuit.size]

lemma eraseFalse_ops (n : ℕ) (C : Circuit) :
    (eraseFalse n C).gates.map Gate.op = C.gates.map Gate.op := by
  simp [eraseFalse, eraseGate, List.map_map, Function.comp_def]

lemma eraseFalse_notCount (n : ℕ) (C : Circuit) :
    PEqualNP.NotBracket.notCount (eraseFalse n C) = PEqualNP.NotBracket.notCount C := by
  simp [PEqualNP.NotBracket.notCount, eraseFalse, eraseGate, List.filter_map, Function.comp_def]
  rfl

lemma eraseFalse_fan (n : ℕ) (C : Circuit) (fan : FanInTwo C) :
    FanInTwo (eraseFalse n C) := by
  intro g mem
  obtain ⟨h, hm, he⟩ := List.mem_map.mp mem
  subst g
  obtain ⟨basis, arity⟩ := fan h hm
  exact ⟨basis, by simpa [eraseGate] using arity⟩

lemma eraseFalse_hasNot (n : ℕ) (C : Circuit)
    (hasNot : ∃ g ∈ C.gates, g.op = .not) :
    ∃ g ∈ (eraseFalse n C).gates, g.op = .not := by
  obtain ⟨g, mem, op⟩ := hasNot
  exact ⟨eraseGate n C.size g, List.mem_map.mpr ⟨g, mem, rfl⟩, op⟩

lemma eraseFalse_last (n : ℕ) (C : Circuit) (positive : 0 < C.size)
    (last : C.output + 1 = n + 1 + C.size) :
    (eraseFalse n C).output + 1 = n + (eraseFalse n C).size := by
  have before : ¬ C.output < n := by omega
  have atFalse : ¬ C.output = n := by omega
  rw [eraseFalse_size]
  simp only [eraseFalse, eraseWire, ite_eq_right before, ite_eq_right atFalse]
  omega

end PEqualNP.Outside.L_meta_2592_aux.EraseFalse
