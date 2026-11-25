import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2732_aux

open PEqualNP.CircuitLowerBounds

def fdStep {n : ℕ} (W : (Fin n → Bool) → List Bool) (g : Gate) :
    (Fin n → Bool) → List Bool :=
  fun y => W y ++ [g.op.eval (g.inputs.map fun i => (W y).getD i false)]

def fdForcing {n : ℕ} (W : (Fin n → Bool) → List Bool) (x : Fin n → Bool) : Prop :=
  ∀ i, (W x).getD i false = true → ∃ j : Fin n, x j = true ∧
    ∀ y : Fin n → Bool, y j = true → (W y).getD i false = true

lemma fdForcing_inputs {n : ℕ} (x : Fin n → Bool) :
    fdForcing (fun y : Fin n → Bool => List.ofFn y) x := by
  intro i hi
  have hn : i < n := by
    by_contra h
    rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt h)] at hi
    contradiction
  refine ⟨⟨i, hn⟩, ?_, ?_⟩
  · simpa [List.getD_eq_getElem?_getD, hn] using hi
  · intro y hy
    simpa [List.getD_eq_getElem?_getD, hn] using hy

lemma fdForcing_step {n : ℕ} (W : (Fin n → Bool) → List Bool)
    (x : Fin n → Bool) (L : ℕ) (lengths : ∀ y, (W y).length = L)
    (g : Gate) (basis : g.op = GateOp.and ∨ g.op = GateOp.or)
    (clean : g.op = GateOp.and →
      g.op.eval (g.inputs.map fun i => (W x).getD i false) = false)
    (forcing : fdForcing W x) : fdForcing (fdStep W g) x := by
  have old (y : Fin n → Bool) (i : ℕ) (hi : i < L) :
      (fdStep W g y).getD i false = (W y).getD i false := by
    exact List.getD_append _ _ _ _ (by simpa [lengths] using hi)
  have fresh (y : Fin n → Bool) :
      (fdStep W g y).getD L false =
        g.op.eval (g.inputs.map fun i => (W y).getD i false) := by
    rw [fdStep, List.getD_append_right _ _ _ _ (by simp [lengths])]
    simp [lengths]
  intro i hi
  by_cases hlt : i < L
  · rw [old x i hlt] at hi
    obtain ⟨j, hj, hforce⟩ := forcing i hi
    exact ⟨j, hj, fun y hy => (old y i hlt).trans (hforce y hy)⟩
  · have heq : i = L := by
      by_contra hne
      have hle : (fdStep W g x).length ≤ i := by
        simp only [fdStep, List.length_append, List.length_singleton, lengths]
        omega
      rw [List.getD_eq_default _ _ hle] at hi
      contradiction
    subst i
    rw [fresh x] at hi
    rcases basis with hand | hor
    · rw [clean hand] at hi
      contradiction
    · have hex : ∃ k ∈ g.inputs, (W x).getD k false = true := by
        simpa [hor, GateOp.eval] using hi
      obtain ⟨k, hk, hkx⟩ := hex
      obtain ⟨j, hj, hforce⟩ := forcing k hkx
      refine ⟨j, hj, ?_⟩
      intro y hy
      rw [fresh y, hor]
      change (g.inputs.map fun i => (W y).getD i false).any id = true
      apply List.any_eq_true.mpr
      exact ⟨true, List.mem_map.mpr ⟨k, hk, hforce y hy⟩, rfl⟩

lemma fdForcing_fold {n : ℕ} (gs : List Gate)
    (W : (Fin n → Bool) → List Bool) (x : Fin n → Bool) (L : ℕ)
    (lengths : ∀ y, (W y).length = L)
    (basis : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (clean : ∀ pre g post, gs = pre ++ g :: post → g.op = GateOp.and →
      g.op.eval (g.inputs.map fun i => ((pre.foldl fdStep W) x).getD i false) = false)
    (forcing : fdForcing W x) : fdForcing (gs.foldl fdStep W) x := by
  induction gs generalizing W L with
  | nil => exact forcing
  | cons g gs ih =>
      rw [List.foldl_cons]
      apply ih (fdStep W g) (L + 1)
      · intro y
        simp [fdStep, lengths]
      · intro h hh
        exact basis h (List.mem_cons_of_mem g hh)
      · intro pre h post heq hop
        exact clean (g :: pre) h post (by simp [heq]) hop
      · apply fdForcing_step W x L lengths g (basis g (by simp))
        · intro hop
          exact clean [] g gs rfl hop
        · exact forcing

lemma fdAnd_pairWitness {n : ℕ} (W : (Fin n → Bool) → List Bool)
    (x : Fin n → Bool) (forcing : fdForcing W x) (a b : ℕ)
    (hit : GateOp.and.eval [(W x).getD a false, (W x).getD b false] = true) :
    ∃ j k : Fin n, x j = true ∧ x k = true ∧
      GateOp.and.eval
        [(W (fun i => decide (i = j ∨ i = k))).getD a false,
         (W (fun i => decide (i = j ∨ i = k))).getD b false] = true := by
  have hab : (W x).getD a false = true ∧ (W x).getD b false = true := by
    simpa [GateOp.eval] using hit
  obtain ⟨j, hj, hja⟩ := forcing a hab.1
  obtain ⟨k, hk, hkb⟩ := forcing b hab.2
  refine ⟨j, k, hj, hk, ?_⟩
  have ha := hja (fun i => decide (i = j ∨ i = k)) (by simp)
  have hb := hkb (fun i => decide (i = j ∨ i = k)) (by simp)
  simp only [GateOp.eval, List.all_cons, List.all_nil, id_eq, ha, hb, Bool.and_self]

lemma fdFold_apply {n : ℕ} (gs : List Gate)
    (W : (Fin n → Bool) → List Bool) (y : Fin n → Bool) :
    (gs.foldl fdStep W) y =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (W y) := by
  induction gs generalizing W with
  | nil => rfl
  | cons g gs ih =>
      simp only [List.foldl_cons]
      exact ih (fdStep W g)

lemma firstDirtyAnd_pairWitness {n : ℕ} (C : Circuit) (x : Fin n → Bool)
    (basis : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (clean : ∀ pre g post, C.gates = pre ++ g :: post → g.op = GateOp.and →
      g.op.eval (g.inputs.map fun i =>
        ((Circuit.mk pre 0).wires (List.ofFn x)).getD i false) = false)
    (a b : ℕ)
    (hit : GateOp.and.eval [(C.wires (List.ofFn x)).getD a false,
      (C.wires (List.ofFn x)).getD b false] = true) :
    ∃ j k : Fin n, x j = true ∧ x k = true ∧
      GateOp.and.eval
        [(C.wires (List.ofFn (fun i => decide (i = j ∨ i = k)))).getD a false,
         (C.wires (List.ofFn (fun i => decide (i = j ∨ i = k)))).getD b false] = true := by
  let W := C.gates.foldl fdStep (fun y : Fin n → Bool => List.ofFn y)
  have wires (y : Fin n → Bool) : W y = C.wires (List.ofFn y) := by
    exact fdFold_apply C.gates (fun y => List.ofFn y) y
  have forcing : fdForcing W x := by
    apply fdForcing_fold C.gates (fun y => List.ofFn y) x n
    · intro y
      simp
    · exact basis
    · intro pre g post heq hop
      simpa only [fdFold_apply, Circuit.wires] using clean pre g post heq hop
    · exact fdForcing_inputs x
  have hit' : GateOp.and.eval [(W x).getD a false, (W x).getD b false] = true := by
    simpa only [wires] using hit
  simpa only [wires] using fdAnd_pairWitness W x forcing a b hit'

lemma firstDirtyAnd_falsePair {n : ℕ} (C : Circuit) (x : Fin n → Bool)
    (F : (Fin n → Bool) → Bool)
    (mono : ∀ u v, (∀ i, u i = true → v i = true) → F u = true → F v = true)
    (hx : F x = false)
    (basis : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (clean : ∀ pre g post, C.gates = pre ++ g :: post → g.op = GateOp.and →
      g.op.eval (g.inputs.map fun i =>
        ((Circuit.mk pre 0).wires (List.ofFn x)).getD i false) = false)
    (a b : ℕ)
    (hit : GateOp.and.eval [(C.wires (List.ofFn x)).getD a false,
      (C.wires (List.ofFn x)).getD b false] = true) :
    ∃ j k : Fin n, F (fun i => decide (i = j ∨ i = k)) = false ∧
      GateOp.and.eval
        [(C.wires (List.ofFn (fun i => decide (i = j ∨ i = k)))).getD a false,
         (C.wires (List.ofFn (fun i => decide (i = j ∨ i = k)))).getD b false] = true := by
  obtain ⟨j, k, hj, hk, hpair⟩ := firstDirtyAnd_pairWitness C x basis clean a b hit
  refine ⟨j, k, ?_, hpair⟩
  cases hF : F (fun i => decide (i = j ∨ i = k)) with
  | false => rfl
  | true =>
      have hsub : ∀ i : Fin n, decide (i = j ∨ i = k) = true → x i = true := by
        intro i hi
        have hmem : i = j ∨ i = k := of_decide_eq_true hi
        rcases hmem with rfl | rfl
        · exact hj
        · exact hk
      have htrue := mono (fun i => decide (i = j ∨ i = k)) x hsub hF
      rw [hx] at htrue
      contradiction

end PEqualNP.Outside.L_meta_2732_aux
