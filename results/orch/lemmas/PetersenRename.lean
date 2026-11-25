import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2590_aux.Rename

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership

variable {n : Nat}

def mapWire (σ : Equiv.Perm (Fin n)) (i : Nat) : Nat :=
  if hi : i < n then (σ ⟨i, hi⟩).val else i

@[simp] lemma mapWire_fin (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    mapWire σ i.val = (σ i).val := by
  simp [mapWire, i.isLt]

lemma mapWire_eq_self (σ : Equiv.Perm (Fin n)) (i : Nat) (hi : n ≤ i) :
    mapWire σ i = i := by
  simp [mapWire, Nat.not_lt_of_ge hi]

lemma mapWire_lt (σ : Equiv.Perm (Fin n)) (i m : Nat) (hm : n ≤ m) :
    mapWire σ i < m ↔ i < m := by
  by_cases hi : i < n
  · have hσ := (σ ⟨i, hi⟩).isLt
    simp only [mapWire, dite_eq_left hi]
    omega
  · rw [mapWire_eq_self σ i (by omega)]

@[simp] lemma mapWire_symm_apply (σ : Equiv.Perm (Fin n)) (i : Nat) :
    mapWire σ.symm (mapWire σ i) = i := by
  by_cases hi : i < n
  · let j : Fin n := ⟨i, hi⟩
    change mapWire σ.symm (mapWire σ j.val) = j.val
    simp
  · rw [mapWire_eq_self σ i (by omega), mapWire_eq_self σ.symm i (by omega)]

lemma mapWire_injective (σ : Equiv.Perm (Fin n)) : Function.Injective (mapWire σ) := by
  intro i j h
  simpa only [mapWire_symm_apply] using congrArg (mapWire σ.symm) h

def renameGate (σ : Equiv.Perm (Fin n)) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (mapWire σ)⟩

def rename (σ : Equiv.Perm (Fin n)) (C : Circuit) : Circuit :=
  ⟨C.gates.map (renameGate σ), mapWire σ C.output⟩

@[simp] lemma renameGate_op (σ : Equiv.Perm (Fin n)) (g : Gate) :
    (renameGate σ g).op = g.op := rfl

@[simp] lemma renameGate_inputs (σ : Equiv.Perm (Fin n)) (g : Gate) :
    (renameGate σ g).inputs = g.inputs.map (mapWire σ) := rfl

@[simp] lemma rename_gates (σ : Equiv.Perm (Fin n)) (C : Circuit) :
    (rename σ C).gates = C.gates.map (renameGate σ) := rfl

@[simp] lemma rename_output (σ : Equiv.Perm (Fin n)) (C : Circuit) :
    (rename σ C).output = mapWire σ C.output := rfl

@[simp] lemma size_rename (σ : Equiv.Perm (Fin n)) (C : Circuit) :
    (rename σ C).size = C.size := by simp [Circuit.size]

@[simp] lemma getGate_rename (σ : Equiv.Perm (Fin n)) (C : Circuit) (j : Nat) :
    (rename σ C).gates[j]? = (C.gates[j]?).map (renameGate σ) := by simp

lemma gateAt_rename (σ : Equiv.Perm (Fin n)) (C : Circuit) (j : Nat) :
    gateAt (rename σ C) j = renameGate σ (gateAt C j) := by
  let d : Gate := ⟨GateOp.or, []⟩
  change (C.gates.map (renameGate σ)).getD j (renameGate σ d) = renameGate σ (C.gates.getD j d)
  exact List.getD_map _ _ _

lemma isAO2_rename (σ : Equiv.Perm (Fin n)) (C : Circuit) (h : IsAO2 n C) :
    IsAO2 n (rename σ C) := by
  obtain ⟨hop, hback, hlen⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    exact hop g' hg'
  · intro j hj i hi
    have hj' : j < C.gates.length := by simpa using hj
    rw [gateAt_rename, renameGate_inputs] at hi
    obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hi
    exact (mapWire_lt σ i' (n + j) (Nat.le_add_right n j)).mpr (hback j hj' i' hi')
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    simpa only [renameGate_inputs, List.length_map] using hlen g' hg'

lemma nodup_rename (σ : Equiv.Perm (Fin n)) (C : Circuit)
    (h : ∀ g ∈ C.gates, g.inputs.Nodup) : ∀ g ∈ (rename σ C).gates, g.inputs.Nodup := by
  intro g hg
  obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
  exact List.Nodup.map (mapWire_injective σ) (h g' hg')

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma fold_rename (σ : Equiv.Perm (Fin n)) (gs : List Gate) :
    ∀ (w w' : List Bool), w'.length = w.length → n ≤ w.length →
      (∀ i, w'.getD (mapWire σ i) false = w.getD i false) → ∀ i,
      ((gs.map (renameGate σ)).foldl step w').getD (mapWire σ i) false =
        (gs.foldl step w).getD i false := by
  induction gs with
  | nil => intro w w' _ _ h i; exact h i
  | cons g gs ih =>
    intro w w' hl hn h
    simp only [List.map_cons, List.foldl_cons]
    have hv : (renameGate σ g).op.eval ((renameGate σ g).inputs.map fun i => w'.getD i false)
        = g.op.eval (g.inputs.map fun i => w.getD i false) := by
      simp only [renameGate_op, renameGate_inputs, List.map_map]
      congr 1
      apply List.map_congr_left
      intro j _
      exact h j
    refine ih _ _ (by simp [step, hl]) (by simp [step]; omega) ?_
    intro i
    simp only [step, hv]
    by_cases hi : i < w.length
    · have his : mapWire σ i < w'.length := by rw [hl]; exact (mapWire_lt σ i _ hn).mpr hi
      rw [List.getD_append _ _ _ _ his, List.getD_append _ _ _ _ hi, h i]
    · rw [mapWire_eq_self σ i (by omega), List.getD_append_right _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by omega), hl]

private lemma ofFn_getD (x : Fin n → Bool) (i : Nat) :
    (List.ofFn x).getD i false = if hi : i < n then x ⟨i, hi⟩ else false := by
  by_cases hi : i < n <;> simp [List.getD_eq_getElem?_getD, hi]

lemma wires_rename (σ : Equiv.Perm (Fin n)) (C : Circuit) (x : Fin n → Bool) (i : Nat) :
    ((rename σ C).wires (List.ofFn x)).getD (mapWire σ i) false =
      (C.wires (List.ofFn (x ∘ σ))).getD i false := by
  apply fold_rename σ C.gates _ _ (by simp) (by simp)
  intro j
  rw [ofFn_getD, ofFn_getD]
  by_cases hj : j < n
  · let k : Fin n := ⟨j, hj⟩
    change (if h : mapWire σ k.val < n then x ⟨mapWire σ k.val, h⟩ else false) =
      (if h : k.val < n then (x ∘ σ) ⟨k.val, h⟩ else false)
    simp [k.isLt, (σ k).isLt]
  · rw [mapWire_eq_self σ j (by omega), dite_eq_right hj, dite_eq_right hj]

lemma wires_rename_symm (σ : Equiv.Perm (Fin n)) (C : Circuit) (x : Fin n → Bool) (i : Nat) :
    ((rename σ C).wires (List.ofFn (x ∘ σ.symm))).getD (mapWire σ i) false =
      (C.wires (List.ofFn x)).getD i false := by
  rw [wires_rename]
  have h : (x ∘ σ.symm) ∘ σ = x := by funext j; simp
  rw [h]

lemma eval_rename (σ : Equiv.Perm (Fin n)) (C : Circuit) (x : Fin n → Bool) :
    (rename σ C).eval (List.ofFn x) = C.eval (List.ofFn (x ∘ σ)) :=
  wires_rename σ C x C.output

lemma eval_rename_symm (σ : Equiv.Perm (Fin n)) (C : Circuit) (x : Fin n → Bool) :
    (rename σ C).eval (List.ofFn (x ∘ σ.symm)) = C.eval (List.ofFn x) :=
  wires_rename_symm σ C x C.output


def target (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
    x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def moves : Fin 10 → Fin 10 → Fin 10 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
    ![4, 0, 5, 8, 3, 9, 1, 7, 6, 2],
    ![7, 5, 0, 1, 2, 9, 8, 4, 6, 3],
    ![9, 6, 1, 0, 4, 7, 8, 2, 5, 3],
    ![4, 9, 7, 5, 0, 3, 6, 2, 8, 1],
    ![5, 8, 3, 2, 7, 0, 6, 4, 1, 9],
    ![2, 1, 6, 8, 3, 7, 0, 9, 5, 4],
    ![2, 3, 4, 9, 7, 1, 8, 0, 6, 5],
    ![6, 8, 3, 4, 9, 1, 5, 2, 0, 7],
    ![2, 7, 9, 6, 1, 3, 5, 4, 8, 0]]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma moves_bijective : ∀ i : Fin 10, Function.Bijective (moves i) := by
  decide +kernel

noncomputable def symmetry (i : Fin 10) : Equiv.Perm (Fin 10) :=
  Equiv.ofBijective (moves i) (moves_bijective i)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma symmetry_zero : ∀ i : Fin 10, symmetry i i = 0 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma symmetry_target : ∀ (i : Fin 10) (x : Fin 10 → Bool),
    target (x ∘ symmetry i) = target x := by
  decide +kernel

lemma count_map_injective (f : ℕ → ℕ) (hf : Function.Injective f)
    (xs : List ℕ) (i : ℕ) : (xs.map f).count (f i) = xs.count i := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [List.count_cons, hf.eq_iff, ih]

lemma count_rename (σ : Equiv.Perm (Fin n)) (C : Circuit) (i : ℕ) :
    ((rename σ C).gates.flatMap Gate.inputs).count (mapWire σ i) =
      (C.gates.flatMap Gate.inputs).count i := by
  have eq : (rename σ C).gates.flatMap Gate.inputs =
      (C.gates.flatMap Gate.inputs).map (mapWire σ) := by
    simp [rename, renameGate, List.flatMap_map, List.map_flatMap, Function.comp_def]
  rw [eq]
  exact count_map_injective _ (mapWire_injective σ) _ i

lemma monotone_rename (σ : Equiv.Perm (Fin n)) (C : Circuit)
    (h : PEqualNP.MetaComplexity.Monotone2 C) :
    PEqualNP.MetaComplexity.Monotone2 (rename σ C) := by
  intro g hg
  obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
  simpa [renameGate] using h g' hg'

lemma unique_input_to_zero (C : Circuit) (i : Fin 10)
    (ao : IsAO2 10 C) (nodup : ∀ g ∈ C.gates, g.inputs.Nodup)
    (correct : ∀ x, C.eval (List.ofFn x) = target x)
    (unique : (C.gates.flatMap Gate.inputs).count i.val = 1) :
    ∃ D : Circuit, IsAO2 10 D ∧ (∀ g ∈ D.gates, g.inputs.Nodup) ∧
      D.size = C.size ∧ (∀ x, D.eval (List.ofFn x) = target x) ∧
      (D.gates.flatMap Gate.inputs).count 0 = 1 := by
  let σ := symmetry i
  refine ⟨rename σ C, isAO2_rename σ C ao, nodup_rename σ C nodup,
    size_rename σ C, ?_, ?_⟩
  · intro x
    rw [eval_rename, correct]
    exact symmetry_target i x
  · have eq := count_rename σ C i.val
    have zi : mapWire σ i.val = 0 := by
      rw [mapWire_fin]
      exact congrArg Fin.val (symmetry_zero i)
    rw [zi, unique] at eq
    exact eq

end PEqualNP.Outside.L_meta_2590_aux.Rename
