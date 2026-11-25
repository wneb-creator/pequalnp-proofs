import PEqualNP.Defs

namespace PEqualNP.Outside.Pilot96Truncate

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma runLength (gs : List Gate) (w : List Bool) :
    (Circuit.wires ⟨gs, 0⟩ w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [Circuit.wires]
  | cons g gs ih =>
    change (Circuit.wires ⟨gs, 0⟩
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).length = _
    rw [ih]
    simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

lemma runExtends (gs : List Gate) (w : List Bool) :
    ∃ tail : List Bool, Circuit.wires ⟨gs, 0⟩ w = w ++ tail := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp [Circuit.wires]⟩
  | cons g gs ih =>
    obtain ⟨tail, ht⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    exact ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: tail, by
      simpa only [Circuit.wires, List.foldl_cons, List.append_assoc,
        List.singleton_append] using ht⟩

lemma evalAppend {pre post : List Gate} {out : ℕ} {w : List Bool}
    (ho : out < w.length + pre.length) :
    Circuit.eval ⟨pre ++ post, out⟩ w = Circuit.eval ⟨pre, out⟩ w := by
  obtain ⟨tail, ht⟩ := runExtends post (Circuit.wires ⟨pre, 0⟩ w)
  unfold Circuit.eval Circuit.wires
  rw [List.foldl_append]
  change (Circuit.wires ⟨post, 0⟩ (Circuit.wires ⟨pre, 0⟩ w)).getD out false = _
  rw [ht, List.getD_append _ _ _ _ (by rw [runLength]; exact ho)]
  rfl

lemma evalTake (C : Circuit) (k : ℕ) (w : List Bool)
    (ho : C.output < w.length + (C.gates.take k).length) :
    C.eval w = Circuit.eval ⟨C.gates.take k, C.output⟩ w := by
  have h := evalAppend (post := C.gates.drop k) ho
  simpa only [List.take_append_drop] using h


lemma evalInput (C : Circuit) (w : List Bool) (ho : C.output < w.length) :
    C.eval w = w.getD C.output false := by
  obtain ⟨tail, ht⟩ := runExtends C.gates w
  change (Circuit.wires ⟨C.gates, 0⟩ w).getD C.output false = _
  rw [ht, List.getD_append _ _ _ _ ho]

lemma evalBeyond (C : Circuit) (w : List Bool) (ho : w.length + C.size ≤ C.output) :
    C.eval w = false := by
  change (Circuit.wires ⟨C.gates, 0⟩ w).getD C.output false = _
  apply List.getD_eq_default
  rw [runLength]
  exact ho

lemma outputBounds (n : ℕ) (f : (Fin n → Bool) → Bool) (C : Circuit)
    (correct : ∀ x, C.eval (List.ofFn x) = f x)
    (nonzero : ∃ x, f x = true)
    (notInput : ∀ i : Fin n, ∃ x, f x ≠ x i) :
    n ≤ C.output ∧ C.output < n + C.size := by
  constructor
  · by_contra! ho
    obtain ⟨x, hx⟩ := notInput ⟨C.output, ho⟩
    apply hx
    rw [← correct x, evalInput C _ (by simpa)]
    rw [List.getD_eq_getElem _ _ (by simpa)]
    simp
  · by_contra! ho
    obtain ⟨x, hx⟩ := nonzero
    have he := evalBeyond C (List.ofFn x) (by simpa using ho)
    rw [correct x, hx] at he
    contradiction

lemma truncateOutput (n : ℕ) (C : Circuit) (fan : FanInTwo C)
    (hasNot : ∃ g ∈ C.gates, g.op = .not)
    (lower : n ≤ C.output) (upper : C.output < n + C.size) :
    ∃ D : Circuit, FanInTwo D ∧ D.size ≤ C.size ∧
      D.output + 1 = n + D.size ∧
      ((∃ g ∈ D.gates, g.op = .not) ∨ D.size < C.size) ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  let k := C.output + 1 - n
  have hk : k ≤ C.gates.length := by change k ≤ C.size; unfold k; omega
  let D : Circuit := ⟨C.gates.take k, C.output⟩
  have dlen : D.size = k := by simp [D, Circuit.size, Nat.min_eq_left hk]
  refine ⟨D, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    apply fan g
    exact List.mem_of_mem_take hg
  · rw [dlen]
    exact hk
  · change C.output + 1 = n + D.size
    rw [dlen]
    unfold k
    omega
  · by_cases hnot : ∃ g ∈ D.gates, g.op = .not
    · exact Or.inl hnot
    · right
      rw [dlen]
      by_contra! hle
      have he : k = C.gates.length := by change C.gates.length ≤ k at hle; omega
      have same : D.gates = C.gates := by simp [D, he]
      exact hnot (same.symm ▸ hasNot)
  · intro x
    apply (evalTake C k (List.ofFn x) ?_).symm
    simp only [List.length_ofFn, List.length_take]
    rw [Nat.min_eq_left hk]
    unfold k
    omega

end PEqualNP.Outside.Pilot96Truncate
