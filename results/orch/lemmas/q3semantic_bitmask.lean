import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583.Q3Semantic

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

def evalGates (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma evalGates_length (gs : List Gate) (w : List Bool) :
    (evalGates gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [evalGates]
  | cons g gs ih =>
    simp only [evalGates, List.foldl_cons] at ih ⊢
    rw [ih]
    simp
    omega

lemma evalGates_append (gs1 gs2 : List Gate) (w : List Bool) :
    evalGates (gs1 ++ gs2) w = evalGates gs2 (evalGates gs1 w) := by
  simp [evalGates, List.foldl_append]

lemma evalGates_getD_lt (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < w.length) :
    (evalGates gs w).getD k false = w.getD k false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [evalGates, List.foldl_cons] at ih ⊢
    have hk' : k < (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length := by
      simp
      omega
    rw [ih _ hk']
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

lemma evalGates_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (evalGates gs w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i => (evalGates (gs.take j) w).getD i false) := by
  have hsplit : gs = gs.take j ++ [gs[j]] ++ gs.drop (j + 1) := by
    have h1 := List.take_append_drop j gs
    have h2 : gs.drop j = gs[j] :: gs.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simp
  conv_lhs => rw [hsplit]
  rw [evalGates_append, evalGates_append]
  set w1 := evalGates (gs.take j) w
  have hw1 : w1.length = w.length + j := by
    rw [evalGates_length, List.length_take]
    omega
  have hlt : w.length + j < (evalGates [gs[j]] w1).length := by
    rw [evalGates_length, hw1]
    simp
  rw [evalGates_getD_lt _ _ _ hlt]
  simp only [evalGates, List.foldl_cons, List.foldl_nil]
  rw [← hw1]
  simp [List.getD_eq_getElem?_getD]

lemma gateAt_eq_getElem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma wires_getD_gate (n : ℕ) (C : Circuit) (hRB : ReadsBack n C)
    (x : List Bool) (hx : x.length = n) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (n + j) false =
      (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i => (C.wires x).getD i false) := by
  change (evalGates C.gates x).getD (n + j) false = _
  have h1 := evalGates_getD_gate C.gates x j hj
  rw [hx] at h1
  rw [h1]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi_lt : i < n + j := by
    have := hRB j hj i
    rw [gateAt_eq_getElem C j hj] at this
    exact this hi
  have hlen : (evalGates (C.gates.take j) x).length = n + j := by
    rw [evalGates_length, hx, List.length_take]
    omega
  have hsplit : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
  symm
  change (evalGates C.gates x).getD i false = (evalGates (C.gates.take j) x).getD i false
  conv_lhs => rw [hsplit, evalGates_append]
  exact evalGates_getD_lt (C.gates.drop j) (evalGates (C.gates.take j) x) i (by omega)

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List ℕ) (f g : ℕ → Bool) (hfg : ∀ u ∈ l, f u = true → g u = true) :
    op.eval (l.map f) = true → op.eval (l.map g) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
    intro hf b hb
    rcases hb with ⟨u, hu, rfl⟩
    exact hfg u hu (hf (f u) ⟨u, hu, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨b, ⟨u, hu, rfl⟩, hfu⟩
    exact ⟨g u, ⟨u, hu, rfl⟩, hfg u hu hfu⟩

lemma wires_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    (C.wires (List.ofFn x)).getD i false = x i := by
  change (evalGates C.gates (List.ofFn x)).getD i false = _
  rw [evalGates_getD_lt C.gates (List.ofFn x) i (by simpa using i.isLt)]
  simp [List.getD_eq_getElem?_getD]

lemma wire_mono (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) :
    ∀ k < n + C.gates.length, (C.wires (List.ofFn x)).getD k false = true →
      (C.wires (List.ofFn y)).getD k false = true := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro hk htrue
    by_cases hkn : k < n
    · have hx := wires_input n C x ⟨k, hkn⟩
      have hy := wires_input n C y ⟨k, hkn⟩
      exact hy.trans (hxy _ (hx.symm.trans htrue))
    · let j := k - n
      have hkj : k = n + j := by omega
      have hj : j < C.gates.length := by omega
      rw [hkj, wires_getD_gate n C hAO.2.1 _ List.length_ofFn j hj] at htrue ⊢
      apply gateOp_eval_mono _ (hAO.1 _ (List.getElem_mem hj)) _ _ _ ?_ htrue
      intro u hu huTrue
      have hu_lt : u < n + j := by
        have hh := hAO.2.1 j hj u
        rw [gateAt_eq_getElem C j hj] at hh
        exact hh hu
      exact ih u (by omega) (by omega) huTrue

lemma output_lt_of_true (n : ℕ) (C : Circuit) (x : Fin n → Bool)
    (htrue : PEqualNP.MetaComplexity.circuitFun n C x = true) :
    C.output < n + C.gates.length := by
  have hlen : (C.wires (List.ofFn x)).length = n + C.gates.length := by
    change (evalGates C.gates (List.ofFn x)).length = n + C.gates.length
    simpa using evalGates_length C.gates (List.ofFn x)
  by_contra h
  have hout : (C.wires (List.ofFn x)).length ≤ C.output := by omega
  change (C.wires (List.ofFn x)).getD C.output false = true at htrue
  rw [List.getD_eq_default _ _ hout] at htrue
  cases htrue


lemma circuit_mono (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true)
    (hx : circuitFun n C x = true) : circuitFun n C y = true :=
  wire_mono n C hAO x y hxy C.output (output_lt_of_true n C x hx) hx

def incidenceValue {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (z : Fin (N + N) → Bool) : Bool :=
  decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
    z (Fin.natAdd N l) = true)

def canonicalNegative {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (A : Finset (Fin N)) : Fin (N + N) → Bool :=
  Fin.addCases (fun p => decide (p ∈ A))
    (fun l => decide (∀ p ∈ A, ¬ I p l))

lemma canonicalNegative_false {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (A : Finset (Fin N)) : incidenceValue I (canonicalNegative I A) = false := by
  apply decide_eq_false
  rintro ⟨p, l, hi, hp, hl⟩
  have hp' : p ∈ A := by
    simpa only [canonicalNegative, Fin.addCases_left, decide_eq_true_eq] using hp
  have hl' : ∀ p ∈ A, ¬ I p l := by
    simpa only [canonicalNegative, Fin.addCases_right, decide_eq_true_eq] using hl
  exact hl' p hp' hi

lemma below_canonicalNegative {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (z : Fin (N + N) → Bool) (hz : incidenceValue I z = false) :
    ∀ i, z i = true → canonicalNegative I
      (Finset.univ.filter fun p => z (Fin.castAdd N p) = true) i = true := by
  have hno : ¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
      z (Fin.natAdd N l) = true := by
    simpa only [incidenceValue, decide_eq_false_iff_not] using hz
  intro i hi
  cases i using Fin.addCases with
  | left p =>
    simpa only [canonicalNegative, Fin.addCases_left, decide_eq_true_eq,
      Finset.mem_filter, Finset.mem_univ, true_and] using hi
  | right l =>
    simp only [canonicalNegative, Fin.addCases_right, decide_eq_true_eq]
    intro p hp hpl
    have hp' : z (Fin.castAdd N p) = true := (Finset.mem_filter.mp hp).2
    exact hno ⟨p, l, hpl, hp', hi⟩

lemma semantics_of_boundary {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (F : (Fin (N + N) → Bool) → Bool)
    (hmono : ∀ x y, (∀ i, x i = true → y i = true) → F x = true → F y = true)
    (hpos : ∀ p l : Fin N, I p l →
      F (pairInput (Fin.castAdd N p) (Fin.natAdd N l)) = true)
    (hneg : ∀ A : Finset (Fin N), F (canonicalNegative I A) = false) :
    ∀ z, F z = incidenceValue I z := by
  intro z
  cases hz : incidenceValue I z
  · cases hf : F z
    · rfl
    · have hle := below_canonicalNegative I z hz
      have htrue := hmono z _ hle hf
      rw [hneg] at htrue
      cases htrue
  · have hex : ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
        z (Fin.natAdd N l) = true := of_decide_eq_true hz
    obtain ⟨p, l, hi, hp, hl⟩ := hex
    apply hmono _ z ?_ (hpos p l hi)
    intro i hii
    simp only [pairInput, decide_eq_true_eq] at hii
    rcases hii with rfl | rfl
    · exact hp
    · exact hl

lemma ao2_semantics_of_boundary {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hAO : IsAO2 (N + N) C)
    (hpos : ∀ p l : Fin N, I p l →
      circuitFun (N + N) C (pairInput (Fin.castAdd N p) (Fin.natAdd N l)) = true)
    (hneg : ∀ A : Finset (Fin N),
      circuitFun (N + N) C (canonicalNegative I A) = false) :
    ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
        z (Fin.natAdd N l) = true) :=
  semantics_of_boundary I (circuitFun (N + N) C) (circuit_mono (N + N) C hAO) hpos hneg

abbrev q3Incidence (p l : Fin 13) : Prop :=
  p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9

lemma q3_parameters : 2 ≤ (3 : ℕ) ∧ 13 = 3 ^ 2 + 3 + 1 := by decide

lemma q3_columns : ∀ l : Fin 13,
    (Finset.univ.filter fun p => q3Incidence p l).card = 3 + 1 := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma q3_unique_line : ∀ p p' : Fin 13, p ≠ p' →
    ∃! l : Fin 13, q3Incidence p l ∧ q3Incidence p' l := by
  unfold ExistsUnique
  decide

lemma q3_positive_count :
    ((Finset.univ : Finset (Fin 13 × Fin 13)).filter
      (fun e => q3Incidence e.1 e.2)).card = 52 := by decide

lemma q3_negative_count : Fintype.card (Finset (Fin 13)) = 8192 := by simp

def maskSet {N : ℕ} (b : BitVec N) : Finset (Fin N) :=
  Finset.univ.filter fun p => b.getLsbD p.val = true

def setMask {N : ℕ} (A : Finset (Fin N)) : BitVec N :=
  (BitVec.ofBoolListLE (List.ofFn fun p : Fin N => decide (p ∈ A))).cast List.length_ofFn

lemma maskSet_setMask {N : ℕ} (A : Finset (Fin N)) : maskSet (setMask A) = A := by
  ext p
  simp only [maskSet, Finset.mem_filter, Finset.mem_univ, true_and, setMask,
    BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

def canonicalMask {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (b : BitVec N) : Fin (N + N) → Bool :=
  Fin.addCases (fun p => b.getLsbD p.val)
    (fun l => decide (∀ p : Fin N, b.getLsbD p.val = true → ¬ I p l))

lemma canonicalMask_eq {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (b : BitVec N) : canonicalMask I b = canonicalNegative I (maskSet b) := by
  funext i
  cases i using Fin.addCases <;>
    simp [canonicalMask, canonicalNegative, maskSet]

lemma ao2_semantics_of_masks {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hAO : IsAO2 (N + N) C)
    (hpos : ∀ p l : Fin N, I p l →
      circuitFun (N + N) C (pairInput (Fin.castAdd N p) (Fin.natAdd N l)) = true)
    (hneg : ∀ b : BitVec N, circuitFun (N + N) C (canonicalMask I b) = false) :
    ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
        z (Fin.natAdd N l) = true) := by
  apply ao2_semantics_of_boundary I C hAO hpos
  intro A
  simpa only [canonicalMask_eq, maskSet_setMask] using hneg (setMask A)

end PEqualNP.Outside.L_meta_2583.Q3Semantic
