import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4675.Buffer

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.TwoColour

def bufferGate (i : ℕ) : Gate := ⟨GateOp.and, [i, i]⟩

def bufferGates (n : ℕ) : List Gate := (List.range n).map bufferGate

def shiftGate (n : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (n + ·)⟩

def buffered (n : ℕ) (C : Circuit) : Circuit :=
  ⟨bufferGates n ++ C.gates.map (shiftGate n), n + C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma buffered_size (n : ℕ) (C : Circuit) : (buffered n C).size = n + C.size := by
  simp [buffered, bufferGates, Circuit.size]

lemma prefix_getD (x w : List Bool) (i : ℕ) :
    (x ++ w).getD (x.length + i) false = w.getD i false := by
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp

lemma shift_step (x w : List Bool) (g : Gate) :
    step (x ++ w) (shiftGate x.length g) = x ++ step w g := by
  simp only [step, shiftGate, List.map_map]
  have h : g.inputs.map (fun i => (x ++ w).getD (x.length + i) false) =
      g.inputs.map (fun i => w.getD i false) := by
    apply List.map_congr_left
    intro i _
    exact prefix_getD x w i
  simp only [Function.comp_def]
  rw [h]
  exact List.append_assoc _ _ _

lemma shift_fold (gs : List Gate) (x w : List Bool) :
    (gs.map (shiftGate x.length)).foldl step (x ++ w) = x ++ gs.foldl step w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [shift_step, ih]

lemma buffer_fold (x : List Bool) (k : ℕ) (hk : k ≤ x.length) :
    (bufferGates k).foldl step x = x ++ x.take k := by
  induction k with
  | zero => simp [bufferGates]
  | succ k ih =>
    have hlt : k < x.length := by omega
    have hle : k ≤ x.length := by omega
    have hb : bufferGates (k + 1) = bufferGates k ++ [bufferGate k] := by
      simp [bufferGates, List.range_succ]
    rw [hb, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [ih hle]
    simp only [step, bufferGate, List.map_cons, List.map_nil, GateOp.eval,
      List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.and_self]
    rw [List.getD_append _ _ _ _ hlt, List.getD_eq_getElem _ _ hlt]
    rw [List.append_assoc, List.take_concat_get' x k hlt]

lemma buffered_wires (C : Circuit) (x : List Bool) :
    (buffered x.length C).wires x = x ++ C.wires x := by
  change (bufferGates x.length ++ C.gates.map (shiftGate x.length)).foldl step x =
    x ++ C.gates.foldl step x
  rw [List.foldl_append, buffer_fold x x.length le_rfl, List.take_length, shift_fold]

lemma buffered_fun (n : ℕ) (C : Circuit) : circuitFun n (buffered n C) = circuitFun n C := by
  funext x
  have hx : (List.ofFn x).length = n := by simp
  change ((buffered n C).wires (List.ofFn x)).getD (n + C.output) false =
    (C.wires (List.ofFn x)).getD C.output false
  have hh := buffered_wires C (List.ofFn x)
  simp only [List.length_ofFn] at hh
  rw [hh]
  simpa using prefix_getD (List.ofFn x) (C.wires (List.ofFn x)) C.output

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
    Option.getD_some]
  exact List.getElem_mem hj

lemma buffered_or_inputs (n : ℕ) (C : Circuit) {g : Gate}
    (hg : g ∈ (buffered n C).gates) (ho : g.op = GateOp.or) :
    ∀ i ∈ g.inputs, n ≤ i := by
  simp only [buffered, List.mem_append] at hg
  rcases hg with hg | hg
  · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hg
    cases ho
  · obtain ⟨g, _, rfl⟩ := List.mem_map.mp hg
    intro i hi
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
    omega

lemma buffered_orIn (n : ℕ) (C : Circuit) (w : ℕ) (hw : n ≤ w) :
    orIn n (buffered n C) w = ∅ := by
  apply Finset.ext
  intro i
  constructor
  · intro hi
    exfalso
    simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rcases hi with hi | ⟨k, hk, _, hop, hi⟩
    · have := i.isLt
      omega
    · have hge := buffered_or_inputs n C (gateAt_mem hk) hop i hi
      exact (Nat.not_le_of_gt i.isLt) hge
  · simp

lemma buffered_tCount (n : ℕ) (C : Circuit) (s : ℕ → Bool) :
    tCount n (buffered n C) s = 0 := by
  unfold tCount twoColour
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro g _ hg
  rcases hg.2.2.1 with ⟨i, hi, _⟩
  rw [buffered_orIn n C (n + g) (by omega)] at hi
  simp at hi

lemma buffered_gateAt_left (n : ℕ) (C : Circuit) {j : ℕ} (hj : j < n) :
    gateAt (buffered n C) j = bufferGate j := by
  simp [gateAt, buffered, bufferGates, List.getD_eq_getElem?_getD,
    List.getElem?_append, hj]

lemma buffered_gateAt_right (n : ℕ) (C : Circuit) {j : ℕ} (hj : j < C.gates.length) :
    gateAt (buffered n C) (n + j) = shiftGate n (gateAt C j) := by
  simp [gateAt, buffered, bufferGates, List.getD_eq_getElem?_getD,
    hj]

lemma buffered_isAO2 (n : ℕ) (C : Circuit) (h : IsAO2 n C) :
    IsAO2 n (buffered n C) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [buffered, List.mem_append] at hg
    rcases hg with hg | hg
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hg
      exact Or.inl rfl
    · obtain ⟨g, hmem, rfl⟩ := List.mem_map.mp hg
      exact h.1 g hmem
  · intro j hj i hi
    by_cases hjn : j < n
    · rw [buffered_gateAt_left n C hjn] at hi
      simp [bufferGate] at hi
      subst i
      omega
    · obtain ⟨k, rfl⟩ : ∃ k, j = n + k := ⟨j - n, by omega⟩
      have hk : k < C.gates.length := by
        change n + k < (buffered n C).size at hj
        rw [buffered_size] at hj
        exact Nat.lt_of_add_lt_add_left hj
      rw [buffered_gateAt_right n C hk] at hi
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hi
      have ha' := h.2.1 k hk a ha
      omega
  · intro g hg
    simp only [buffered, List.mem_append] at hg
    rcases hg with hg | hg
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hg
      rfl
    · obtain ⟨g, hmem, rfl⟩ := List.mem_map.mp hg
      simpa [shiftGate] using h.2.2 g hmem

lemma buffered_exists (n : ℕ) (C : Circuit) (h : IsAO2 n C) (s : ℕ → Bool) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size = C.size + n ∧
      circuitFun n D = circuitFun n C ∧ tCount n D s = 0 := by
  refine ⟨buffered n C, buffered_isAO2 n C h, ?_, buffered_fun n C, buffered_tCount n C s⟩
  rw [buffered_size, Nat.add_comm]

end PEqualNP.Outside.L_meta_4675.Buffer
