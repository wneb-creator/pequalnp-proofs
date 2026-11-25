import PEqualNP.Defs

namespace PEqualNP.Outside.OutputPruning

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (x ++ [_])).length = _
    rw [ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

lemma run_getD (gs : List Gate) (x : List Bool) (o : ℕ) (ho : o < x.length) :
    (run gs x).getD o false = x.getD o false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (x ++ [_])).getD o false = _
    rw [ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ ho

lemma eval_append (gs hs : List Gate) (x : List Bool) (o : ℕ)
    (ho : o < x.length + gs.length) :
    (Circuit.mk (gs ++ hs) o).eval x = (Circuit.mk gs o).eval x := by
  change (run (gs ++ hs) x).getD o false = (run gs x).getD o false
  change ((gs ++ hs).foldl _ x).getD o false = _
  rw [List.foldl_append]
  exact run_getD hs (run gs x) o (by simpa only [run_length] using ho)

def prune (n : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.take (C.output + 1 - n), C.output⟩

lemma prune_size (n : ℕ) (C : Circuit) (hout : C.output < n + C.size) :
    (prune n C).size = C.output + 1 - n := by
  change (C.gates.take (C.output + 1 - n)).length = _
  rw [List.length_take, Nat.min_eq_left]
  change C.output + 1 - n ≤ C.size
  omega

lemma prune_fanInTwo (n : ℕ) (C : Circuit) (hfan : FanInTwo C) :
    FanInTwo (prune n C) := by
  intro g hg
  exact hfan g (List.mem_of_mem_take hg)

lemma prune_legal (n : ℕ) (C : Circuit)
    (hlegal : ∀ j : ℕ, let g := C.gates.getD j ⟨.or, []⟩
      (∀ i ∈ g.inputs, i < n + j) ∧ (g.op = .not → g.inputs.length ≤ 1)) :
    ∀ j : ℕ, let g := (prune n C).gates.getD j ⟨.or, []⟩
      (∀ i ∈ g.inputs, i < n + j) ∧ (g.op = .not → g.inputs.length ≤ 1) := by
  intro j
  dsimp only
  by_cases hj : j < (prune n C).gates.length
  · have hC : j < C.gates.length :=
      hj.trans_le (List.length_take_le' _ _)
    have he : (prune n C).gates.getD j ⟨.or, []⟩ = C.gates.getD j ⟨.or, []⟩ := by
      rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hC]
      exact List.getElem_take
    rw [he]
    exact hlegal j
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hj)]
    simp

lemma prune_eval (n : ℕ) (C : Circuit) (hin : n ≤ C.output)
    (hout : C.output < n + C.size) (x : Fin n → Bool) :
    (prune n C).eval (List.ofFn x) = C.eval (List.ofFn x) := by
  have hlen := prune_size n C hout
  have ho : C.output < (List.ofFn x).length +
      (C.gates.take (C.output + 1 - n)).length := by
    change (C.gates.take (C.output + 1 - n)).length = _ at hlen
    simp only [List.length_ofFn, hlen]
    omega
  have eq := eval_append (C.gates.take (C.output + 1 - n))
    (C.gates.drop (C.output + 1 - n)) (List.ofFn x) C.output ho
  rw [List.take_append_drop] at eq
  exact eq.symm

lemma prune_properties (n : ℕ) (C : Circuit) (hfan : FanInTwo C)
    (hin : n ≤ C.output) (hout : C.output < n + C.size)
    (hnot : ∃ g ∈ C.gates, g.op = GateOp.not) :
    FanInTwo (prune n C) ∧ (prune n C).size ≤ C.size ∧
      (prune n C).output + 1 = n + (prune n C).size ∧
      ((∃ g ∈ (prune n C).gates, g.op = GateOp.not) ∨
        (prune n C).size < C.size) ∧
      ∀ x : Fin n → Bool, (prune n C).eval (List.ofFn x) = C.eval (List.ofFn x) := by
  have hlen := prune_size n C hout
  have hsmall : (prune n C).size ≤ C.size := by rw [hlen]; omega
  refine ⟨prune_fanInTwo n C hfan, hsmall, ?_, ?_, prune_eval n C hin hout⟩
  · change C.output + 1 = _
    rw [hlen]
    omega
  · by_cases hlt : (prune n C).size < C.size
    · exact Or.inr hlt
    · left
      have htake : C.gates.take (C.output + 1 - n) = C.gates := by
        apply List.take_of_length_le
        change C.size ≤ C.output + 1 - n
        omega
      simpa only [prune, htake] using hnot

end PEqualNP.Outside.OutputPruning
