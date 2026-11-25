import Mathlib.Data.List.GetD
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4970

namespace Interval

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (x : List Bool) : List Bool := gs.foldl step x

lemma run_append (gs hs : List Gate) (x : List Bool) :
    run (gs ++ hs) x = run hs (run gs x) := by
  simp [run, List.foldl_append]

lemma run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = step (run gs x) g := by
  simp [run, List.foldl_append]

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih =>
      change (run gs (step x g)).length = _
      rw [ih]
      simp [step]
      omega

lemma getD_append_left (a b : List Bool) (i : ℕ) (hi : i < a.length) :
    (a ++ b).getD i false = a.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_right (a b : List Bool) (i : ℕ) (hi : a.length ≤ i) :
    (a ++ b).getD i false = b.getD (i - a.length) false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

lemma getD_ge (a : List Bool) (i : ℕ) (hi : a.length ≤ i) :
    a.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma getD_snoc (a : List Bool) (b : Bool) (i : ℕ) :
    (a ++ [b]).getD i false = if i = a.length then b else a.getD i false := by
  by_cases hi : i < a.length
  · rw [getD_append_left _ _ _ hi, ite_eq_right (by omega)]
  · rw [getD_append_right _ _ _ (by omega)]
    by_cases he : i = a.length
    · simp [he]
    · rw [ite_eq_right he]
      rw [getD_ge [b] (i - a.length) (by simp only [List.length_singleton]; omega)]
      rw [getD_ge a i (by omega)]

lemma gateAt_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j ∈ C.gates := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma no_direct_left_tCount_zero (p l : ℕ) (C : Circuit)
    (h : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or →
      ∀ i ∈ (gateAt C j).inputs, p ≤ i) :
    PEqualNP.TwoColour.tCount (p + l) C (fun i => decide (p ≤ i)) = 0 := by
  classical
  unfold PEqualNP.TwoColour.tCount PEqualNP.TwoColour.twoColour
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro g hg hmix
  obtain ⟨_, _, ⟨i, hi, hcol⟩, _⟩ := hmix
  have hlt : (i : ℕ) < p := by simpa using hcol
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  obtain heq | ⟨j, hj, _, hop, hin⟩ := hi
  · have := i.isLt
    omega
  · have := h j hj hop i hin
    omega

def copies (a k : ℕ) : List Gate :=
  (List.range k).map fun i => ⟨GateOp.and, [a + i, a + i]⟩

lemma copies_length (a k : ℕ) : (copies a k).length = k := by simp [copies]

lemma copies_succ (a k : ℕ) :
    copies a (k + 1) = copies a k ++ [⟨GateOp.and, [a + k, a + k]⟩] := by
  simp [copies, List.range_succ]

lemma copies_run (a k : ℕ) (x : List Bool) (hk : a + k ≤ x.length) :
    run (copies a k) x = x ++ (x.drop a).take k := by
  induction k with
  | zero => simp [copies, run]
  | succ k ih =>
      rw [copies_succ, run_snoc, ih (by omega)]
      have hi : a + k < x.length := by omega
      have hd : k < (x.drop a).length := by simp; omega
      have hv : (x ++ (x.drop a).take k).getD (a + k) false = (x.drop a)[k] := by
        rw [getD_append_left _ _ _ hi]
        simp [List.getD_eq_getElem?_getD, hi]
      simp only [step, List.map_cons, List.map_nil, hv, GateOp.eval, List.all_cons,
        List.all_nil, id_eq, Bool.and_true, Bool.and_self]
      rw [List.take_succ_eq_append_getElem hd, List.append_assoc]

def redirect (n a k w : ℕ) : ℕ :=
  if a ≤ w ∧ w < a + k then n + (w - a) else if w < n then w else k + w

def redirectGate (n a k : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (redirect n a k)⟩

def transform (n a k : ℕ) (C : Circuit) : Circuit :=
  ⟨copies a k ++ C.gates.map (redirectGate n a k), redirect n a k C.output⟩

lemma redirect_avoids (n a k w : ℕ) (h : a + k ≤ n) :
    ¬ (a ≤ redirect n a k w ∧ redirect n a k w < a + k) := by
  unfold redirect
  split_ifs <;> omega

lemma redirect_gate_wire (n a k j : ℕ) (h : a + k ≤ n) :
    redirect n a k (n + j) = k + (n + j) := by
  simp [redirect, show ¬ (a ≤ n + j ∧ n + j < a + k) by omega,
    show ¬ n + j < n by omega]

lemma redirect_eq_last (n a k j w : ℕ) (h : a + k ≤ n) :
    redirect n a k w = n + k + j ↔ w = n + j := by
  unfold redirect
  split_ifs <;> omega

lemma redirect_initial (n a k : ℕ) (h : a + k ≤ n)
    (x : List Bool) (hx : x.length = n) (w : ℕ) :
    (run (copies a k) x).getD (redirect n a k w) false = x.getD w false := by
  rw [copies_run _ _ _ (by omega)]
  unfold redirect
  split_ifs with hw hn
  · rw [getD_append_right _ _ _ (by omega)]
    have hwk : w - a < k := by omega
    have hwa : a + (w - a) = w := by omega
    simp only [hx, Nat.add_sub_cancel_left]
    simp [List.getD_eq_getElem?_getD, hwk, List.getElem?_drop, hwa]
  · exact getD_append_left _ _ _ (by omega)
  · rw [getD_ge (x ++ (x.drop a).take k) (k + w) (by simp only [List.length_append, List.length_take, List.length_drop, hx]; omega)]
    exact (getD_ge x w (by omega)).symm

lemma redirect_run (n a k : ℕ) (h : a + k ≤ n) (gs : List Gate)
    (x : List Bool) (hx : x.length = n) (w : ℕ) :
    (run (copies a k ++ gs.map (redirectGate n a k)) x).getD (redirect n a k w) false =
      (run gs x).getD w false := by
  induction gs using List.reverseRecOn generalizing w with
  | nil => simpa [run] using redirect_initial n a k h x hx w
  | append_singleton gs g ih =>
      have hv : g.op.eval (g.inputs.map fun i =>
          (run (copies a k ++ gs.map (redirectGate n a k)) x).getD (redirect n a k i) false) =
          g.op.eval (g.inputs.map fun i => (run gs x).getD i false) := by
        congr 1
        apply List.map_congr_left
        intro i _
        exact ih i
      simp only [List.map_append, List.map_cons, List.map_nil, ← List.append_assoc,
        run_snoc, step, redirectGate, List.map_map]
      rw [getD_snoc, getD_snoc]
      have hlen : (run (copies a k ++ gs.map (redirectGate n a k)) x).length =
          n + k + gs.length := by simp [run_length, hx, copies_length, Nat.add_assoc]
      have hlen' : (run gs x).length = n + gs.length := by rw [run_length, hx]
      simp only [hlen, hlen', redirect_eq_last n a k gs.length w h]
      split_ifs
      · exact hv
      · exact ih w

lemma transform_wires (n a k : ℕ) (h : a + k ≤ n)
    (C : Circuit) (x : Fin n → Bool) (w : ℕ) :
    ((transform n a k C).wires (List.ofFn x)).getD (redirect n a k w) false =
      (C.wires (List.ofFn x)).getD w false := by
  exact redirect_run n a k h C.gates (List.ofFn x) (by simp) w

lemma transform_fun (n a k : ℕ) (h : a + k ≤ n) (C : Circuit) :
    circuitFun n (transform n a k C) = circuitFun n C := by
  funext x
  exact transform_wires n a k h C x C.output

lemma transform_size (n a k : ℕ) (C : Circuit) :
    (transform n a k C).size = C.size + k := by
  simp [transform, Circuit.size, copies_length, Nat.add_comm]

lemma gateAt_transform_before (n a k : ℕ) (C : Circuit) (j : ℕ) (hj : j < k) :
    gateAt (transform n a k C) j = ⟨GateOp.and, [a + j, a + j]⟩ := by
  simp only [gateAt, transform, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (show j < (copies a k).length by simpa [copies_length] using hj)]
  simp [copies, hj]

lemma gateAt_transform_after (n a k : ℕ) (C : Circuit) (j : ℕ)
    (hj : j < C.gates.length) :
    gateAt (transform n a k C) (k + j) = redirectGate n a k (gateAt C j) := by
  simp [gateAt, transform, List.getD_eq_getElem?_getD, copies_length, hj]

lemma redirect_lt (n a k j w : ℕ) (_h : a + k ≤ n) (hw : w < n + j) :
    redirect n a k w < n + (k + j) := by
  unfold redirect
  split_ifs <;> omega

lemma transform_ao2 (n a k : ℕ) (h : a + k ≤ n) (C : Circuit)
    (hC : PEqualNP.TopForm.IsAO2 n C) :
    PEqualNP.TopForm.IsAO2 n (transform n a k C) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    change g ∈ copies a k ++ C.gates.map (redirectGate n a k) at hg
    rcases List.mem_append.mp hg with hg | hg
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hg
      exact Or.inl rfl
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hg
      exact hC.1 u hu
  · intro j hj i hi
    have hlen : (transform n a k C).gates.length = k + C.gates.length := by
      simp [transform, copies_length]
    by_cases hjk : j < k
    · rw [gateAt_transform_before n a k C j hjk] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hi
      subst i
      omega
    · obtain ⟨q, rfl⟩ : ∃ q, j = k + q := ⟨j - k, by omega⟩
      have hq : q < C.gates.length := by omega
      rw [gateAt_transform_after n a k C q hq] at hi
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hi
      exact redirect_lt n a k q w h (hC.2.1 q hq w hw)
  · intro g hg
    change g ∈ copies a k ++ C.gates.map (redirectGate n a k) at hg
    rcases List.mem_append.mp hg with hg | hg
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hg
      rfl
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hg
      simpa [redirectGate] using hC.2.2 u hu

lemma transform_or_avoids (n a k : ℕ) (h : a + k ≤ n) (C : Circuit) :
    ∀ j < (transform n a k C).gates.length,
      (gateAt (transform n a k C) j).op = GateOp.or →
      ∀ i ∈ (gateAt (transform n a k C) j).inputs, ¬ (a ≤ i ∧ i < a + k) := by
  intro j hj hop i hi
  have hg := gateAt_mem (transform n a k C) j hj
  change gateAt (transform n a k C) j ∈ copies a k ++ C.gates.map (redirectGate n a k) at hg
  rcases List.mem_append.mp hg with hg | hg
  · obtain ⟨q, _, heq⟩ := List.mem_map.mp hg
    rw [← heq] at hop
    cases hop
  · obtain ⟨g, _, heq⟩ := List.mem_map.mp hg
    rw [← heq] at hi
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hi
    exact redirect_avoids n a k w h

lemma no_direct_right_tCount_zero (p l : ℕ) (C : Circuit)
    (h : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or →
      ∀ i ∈ (gateAt C j).inputs, ¬ (p ≤ i ∧ i < p + l)) :
    PEqualNP.TwoColour.tCount (p + l) C (fun i => decide (p ≤ i)) = 0 := by
  classical
  unfold PEqualNP.TwoColour.tCount PEqualNP.TwoColour.twoColour
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro g hg hmix
  obtain ⟨_, _, _, ⟨i, hi, hcol⟩⟩ := hmix
  have hle : p ≤ (i : ℕ) := by simpa using hcol
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  obtain heq | ⟨j, hj, _, hop, hin⟩ := hi
  · have := i.isLt
    omega
  · exact h j hj hop i hin ⟨hle, i.isLt⟩

lemma transform_left_tCount (p l : ℕ) (C : Circuit) :
    PEqualNP.TwoColour.tCount (p + l) (transform (p + l) 0 p C)
      (fun i => decide (p ≤ i)) = 0 := by
  apply no_direct_left_tCount_zero
  intro j hj hop i hi
  have h := transform_or_avoids (p + l) 0 p (by omega) C j hj hop i hi
  omega

lemma transform_right_tCount (p l : ℕ) (C : Circuit) :
    PEqualNP.TwoColour.tCount (p + l) (transform (p + l) p l C)
      (fun i => decide (p ≤ i)) = 0 := by
  apply no_direct_right_tCount_zero
  exact transform_or_avoids (p + l) p l (by omega) C

lemma transform_gate (n a k : ℕ) (h : a + k ≤ n)
    (C : Circuit) (x : Fin n → Bool) (j : ℕ) :
    ((transform n a k C).wires (List.ofFn x)).getD (n + (k + j)) false =
      (C.wires (List.ofFn x)).getD (n + j) false := by
  have hw := transform_wires n a k h C x (n + j)
  rw [redirect_gate_wire n a k j h] at hw
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw

lemma transform_or_witness (n a k : ℕ) (h : a + k ≤ n) (C : Circuit)
    (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or)
    (f : (Fin n → Bool) → Bool)
    (hf : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + j) false = f x) :
    ∃ q : ℕ, q < (transform n a k C).gates.length ∧
      (gateAt (transform n a k C) q).op = GateOp.or ∧
      ∀ x : Fin n → Bool,
        ((transform n a k C).wires (List.ofFn x)).getD (n + q) false = f x := by
  refine ⟨k + j, ?_, ?_, ?_⟩
  · simpa [transform, copies_length] using Nat.add_lt_add_left hj k
  · rw [gateAt_transform_after n a k C j hj]
    exact hop
  · intro x
    rw [transform_gate n a k h C x j, hf x]

lemma exists_zero_mixed_min (p l : ℕ) (C : Circuit)
    (hC : PEqualNP.TopForm.IsAO2 (p + l) C) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (p + l) D ∧ D.size = C.size + min p l ∧
      circuitFun (p + l) D = circuitFun (p + l) C ∧
      PEqualNP.TwoColour.tCount (p + l) D (fun i => decide (p ≤ i)) = 0 ∧
      (∀ j < C.gates.length, (gateAt D (min p l + j)).op = (gateAt C j).op) ∧
      (∀ (j : ℕ) (x : Fin (p + l) → Bool),
        (D.wires (List.ofFn x)).getD (p + l + (min p l + j)) false =
          (C.wires (List.ofFn x)).getD (p + l + j) false) := by
  by_cases hp : p ≤ l
  · rw [Nat.min_eq_left hp]
    refine ⟨transform (p + l) 0 p C, transform_ao2 _ _ _ (by omega) C hC,
      transform_size _ _ _ C, transform_fun _ _ _ (by omega) C,
      transform_left_tCount p l C, ?_, ?_⟩
    · intro j hj
      rw [gateAt_transform_after (p + l) 0 p C j hj]
      rfl
    · intro j x
      exact transform_gate (p + l) 0 p (by omega) C x j
  · rw [Nat.min_eq_right (by omega)]
    refine ⟨transform (p + l) p l C, transform_ao2 _ _ _ (by omega) C hC,
      transform_size _ _ _ C, transform_fun _ _ _ (by omega) C,
      transform_right_tCount p l C, ?_, ?_⟩
    · intro j hj
      rw [gateAt_transform_after (p + l) p l C j hj]
      rfl
    · intro j x
      exact transform_gate (p + l) p l (by omega) C x j

end Interval

namespace Degenerate

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edgeFunction {p l : ℕ} (E : Finset (Fin p × Fin l))
    (x : Fin (p + l) → Bool) : Bool :=
  decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧
    x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)

lemma left_ne_right {p l : ℕ} (a : Fin p) (b : Fin l) :
    Fin.castAdd l a ≠ Fin.natAdd p b := by
  intro h
  have hh := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hh
  omega

lemma edgeFunction_singleton_false {p l : ℕ} (E : Finset (Fin p × Fin l))
    (i : Fin (p + l)) : edgeFunction E (fun k => decide (k = i)) = false := by
  simp only [edgeFunction, decide_eq_false_iff_not]
  rintro ⟨a, b, _, ha, hb⟩
  simp only [decide_eq_true_eq] at ha hb
  exact left_ne_right a b (ha.trans hb.symm)

lemma fold_length (gs : List Gate) (x : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).length =
      x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

lemma fold_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) x).getD i false =
      x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
      simp only [List.foldl_cons]
      rw [ih _ (by simp only [List.length_append, List.length_singleton]; omega)]
      exact List.getD_append _ _ _ _ hi

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length :=
  fold_length C.gates x

lemma circuit_input {n : ℕ} (C : Circuit) (hi : C.output < n) (x : Fin n → Bool) :
    circuitFun n C x = x ⟨C.output, hi⟩ := by
  change (C.wires (List.ofFn x)).getD C.output false = _
  rw [Circuit.wires, fold_input C.gates _ _ (by simpa using hi)]
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

lemma output_not_input {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit)
    (hc : ∀ x : Fin (p + l) → Bool, circuitFun (p + l) C x = edgeFunction E x) :
    p + l ≤ C.output := by
  by_contra h
  have hi : C.output < p + l := by omega
  let i : Fin (p + l) := ⟨C.output, hi⟩
  have hh := hc (fun k => decide (k = i))
  rw [circuit_input C hi, edgeFunction_singleton_false] at hh
  simp [i] at hh

lemma edgeFunction_all_true {p l : ℕ} (E : Finset (Fin p × Fin l))
    (he : E.Nonempty) : edgeFunction E (fun _ => true) = true := by
  obtain ⟨⟨a, b⟩, hab⟩ := he
  simp only [edgeFunction, decide_eq_true_eq]
  exact ⟨a, b, hab, trivial, trivial⟩

lemma empty_of_invalid_output {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit)
    (hc : ∀ x : Fin (p + l) → Bool, circuitFun (p + l) C x = edgeFunction E x)
    (hout : p + l + C.gates.length ≤ C.output) : E = ∅ := by
  by_contra he
  have hen : E.Nonempty := Finset.nonempty_iff_ne_empty.mpr he
  have hh := hc (fun _ => true)
  rw [edgeFunction_all_true E hen] at hh
  change (C.wires (List.ofFn (fun _ : Fin (p + l) => true))).getD C.output false = true at hh
  rw [List.getD_eq_default _ _ (by rw [wires_length]; simpa using hout)] at hh
  contradiction

lemma nonempty_output_gate {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit)
    (hc : ∀ x : Fin (p + l) → Bool, circuitFun (p + l) C x = edgeFunction E x)
    (he : E.Nonempty) : ∃ j < C.gates.length, C.output = p + l + j := by
  have hlo := output_not_input E C hc
  have hhi : C.output < p + l + C.gates.length := by
    by_contra h
    have := empty_of_invalid_output E C hc (by omega)
    exact he.ne_empty this
  exact ⟨C.output - (p + l), by omega, by omega⟩

lemma two_neighbors_of_served {p l : ℕ} (E : Finset (Fin p × Fin l))
    (a : Fin p) (b : Fin l)
    (hs : (∃ Q : Finset (Fin l), 2 ≤ Q.card ∧ b ∈ Q ∧ ∀ b' ∈ Q, (a, b') ∈ E) ∨
      (∃ P : Finset (Fin p), 2 ≤ P.card ∧ a ∈ P ∧ ∀ a' ∈ P, (a', b) ∈ E)) :
    (∃ b' : Fin l, b' ≠ b ∧ (a, b') ∈ E) ∨
      (∃ a' : Fin p, a' ≠ a ∧ (a', b) ∈ E) := by
  rcases hs with ⟨Q, hQ, _, hsub⟩ | ⟨P, hP, _, hsub⟩
  · obtain ⟨b', hb', hne⟩ := Finset.exists_mem_ne (by omega : 1 < Q.card) b
    exact Or.inl ⟨b', hne, hsub b' hb'⟩
  · obtain ⟨a', ha', hne⟩ := Finset.exists_mem_ne (by omega : 1 < P.card) a
    exact Or.inr ⟨a', hne, hsub a' ha'⟩

lemma two_edges_of_served {p l : ℕ} (E : Finset (Fin p × Fin l))
    (a : Fin p) (b : Fin l) (hab : (a, b) ∈ E)
    (hs : (∃ Q : Finset (Fin l), 2 ≤ Q.card ∧ b ∈ Q ∧ ∀ b' ∈ Q, (a, b') ∈ E) ∨
      (∃ P : Finset (Fin p), 2 ≤ P.card ∧ a ∈ P ∧ ∀ a' ∈ P, (a', b) ∈ E)) :
    2 ≤ E.card := by
  have hh : 1 < E.card := by
    rcases two_neighbors_of_served E a b hs with ⟨b', hne, hb'⟩ | ⟨a', hne, ha'⟩
    · apply Finset.one_lt_card.mpr
      refine ⟨(a, b'), hb', (a, b), hab, ?_⟩
      intro heq
      exact hne (congrArg Prod.snd heq)
    · apply Finset.one_lt_card.mpr
      refine ⟨(a', b), ha', (a, b), hab, ?_⟩
      intro heq
      exact hne (congrArg Prod.fst heq)
  omega

lemma nonempty_sides {p l : ℕ} (E : Finset (Fin p × Fin l)) (he : E.Nonempty) :
    0 < p ∧ 0 < l := by
  obtain ⟨⟨a, b⟩, _⟩ := he
  have ha := a.isLt
  have hb := b.isLt
  constructor <;> omega

lemma empty_bound {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit)
    (he : E = ∅) : ∃ S : Finset (Fin (p + l)),
    (∀ (a : Fin p) (b : Fin l), (a, b) ∈ E →
      Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧ E.card + S.card ≤ C.size + 1 := by
  refine ⟨∅, ?_, ?_⟩
  · simp [he]
  · simp [he]

end Degenerate

namespace TinyKernel

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.TwoColour

def edges : Finset (Fin 2 × Fin 3) := {(0, 0), (0, 1), (1, 0), (1, 2)}

def circuit : Circuit :=
  ⟨[⟨.and, [0, 0]⟩, ⟨.and, [1, 1]⟩,
    ⟨.or, [2, 3]⟩, ⟨.or, [2, 4]⟩,
    ⟨.or, [5, 6]⟩, ⟨.or, [5, 8]⟩,
    ⟨.or, [7, 6]⟩, ⟨.or, [7, 8]⟩,
    ⟨.and, [9, 10]⟩, ⟨.and, [11, 12]⟩,
    ⟨.and, [13, 14]⟩], 15⟩

def edgeFun (x : Fin 5 → Bool) : Bool :=
  decide (∃ a : Fin 2, ∃ b : Fin 3, (a, b) ∈ edges ∧
    x (Fin.castAdd 3 a) = true ∧ x (Fin.natAdd 2 b) = true)

def wire (j : Fin 11) (x : Fin 5 → Bool) : Bool :=
  (circuit.wires (List.ofFn x)).getD (5 + j) false

lemma no_four : ∀ a a' : Fin 2, ∀ b b' : Fin 3,
    a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ edges ∧ (a, b') ∈ edges ∧ (a', b) ∈ edges ∧ (a', b') ∈ edges) := by
  decide +kernel

lemma ao2 : IsAO2 5 circuit := by decide +kernel

lemma exact_output : ∀ x : Fin 5 → Bool, circuitFun 5 circuit x = edgeFun x := by
  decide +kernel

lemma no_mixed : tCount 5 circuit (fun i => decide (2 ≤ i)) = 0 := by
  decide +kernel

lemma left_star : ∀ x : Fin 5 → Bool,
    wire 2 x = decide (∃ b ∈ ({0, 1} : Finset (Fin 3)), x (Fin.natAdd 2 b) = true) := by
  decide +kernel

lemma right_star : ∀ x : Fin 5 → Bool,
    wire 3 x = decide (∃ b ∈ ({0, 2} : Finset (Fin 3)), x (Fin.natAdd 2 b) = true) := by
  decide +kernel

lemma served : ∀ a : Fin 2, ∀ b : Fin 3, (a, b) ∈ edges →
    ∃ j : Fin 11, ∃ Q : Finset (Fin 3),
      (gateAt circuit j).op = GateOp.or ∧ 2 ≤ Q.card ∧ b ∈ Q ∧
      (∀ b' ∈ Q, (a, b') ∈ edges) ∧
      ∀ x : Fin 5 → Bool, wire j x = decide (∃ b' ∈ Q, x (Fin.natAdd 2 b') = true) := by
  have h : ∀ a : Fin 2, ∀ b : Fin 3, (a, b) ∈ edges →
      2 ≤ (if a = 0 then ({0, 1} : Finset (Fin 3)) else {0, 2}).card ∧
      b ∈ (if a = 0 then ({0, 1} : Finset (Fin 3)) else {0, 2}) ∧
      (∀ b' ∈ (if a = 0 then ({0, 1} : Finset (Fin 3)) else {0, 2}), (a, b') ∈ edges) ∧
      ∀ x : Fin 5 → Bool, wire (if a = 0 then 2 else 3) x =
        decide (∃ b' ∈ (if a = 0 then ({0, 1} : Finset (Fin 3)) else {0, 2}),
          x (Fin.natAdd 2 b') = true) := by
    decide +kernel
  intro a b hab
  refine ⟨if a = 0 then 2 else 3, if a = 0 then {0, 1} else {0, 2}, ?_, h a b hab⟩
  split <;> rfl

lemma every_gate_active : ∀ j : Fin 11, ∃ a : Fin 2, ∃ b : Fin 3,
    (a, b) ∈ edges ∧
      wire j (fun i => decide (i = Fin.castAdd 3 a ∨ i = Fin.natAdd 2 b)) = true := by
  decide +kernel

lemma only_final_below : ∀ j : Fin 11,
    (∀ x : Fin 5 → Bool, wire j x = true → edgeFun x = true) ↔ j = 10 := by
  decide +kernel

lemma no_single_vertex_cover : ∀ v : Fin 5, ∃ a : Fin 2, ∃ b : Fin 3,
    (a, b) ∈ edges ∧ Fin.castAdd 3 a ≠ v ∧ Fin.natAdd 2 b ≠ v := by
  decide +kernel

lemma two_vertex_cover : ∀ a : Fin 2, ∀ b : Fin 3, (a, b) ∈ edges →
    Fin.castAdd 3 a ∈ ({0, 1} : Finset (Fin 5)) ∨ Fin.natAdd 2 b ∈ ({0, 1} : Finset (Fin 5)) := by
  decide +kernel

lemma cover_card_ge_two (S : Finset (Fin 5))
    (h : ∀ a : Fin 2, ∀ b : Fin 3, (a, b) ∈ edges →
      Fin.castAdd 3 a ∈ S ∨ Fin.natAdd 2 b ∈ S) : 2 ≤ S.card := by
  have h01 := h 0 1 (by decide +kernel)
  have h12 := h 1 2 (by decide +kernel)
  have hh : 1 < S.card := by
    rcases h01 with h0 | h3 <;> rcases h12 with h1 | h4
    · exact Finset.one_lt_card.mpr ⟨_, h0, _, h1, by decide +kernel⟩
    · exact Finset.one_lt_card.mpr ⟨_, h0, _, h4, by decide +kernel⟩
    · exact Finset.one_lt_card.mpr ⟨_, h3, _, h1, by decide +kernel⟩
    · exact Finset.one_lt_card.mpr ⟨_, h3, _, h4, by decide +kernel⟩
  omega

end TinyKernel


namespace ColourCertificate

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.TwoColour

lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [PEqualNP.CleanedNonEdge.orStep]
    omega

lemma orSets_length (n : ℕ) (C : Circuit) :
    (PEqualNP.CleanedNonEdge.orSets n C).length = C.gates.length := by
  unfold PEqualNP.CleanedNonEdge.orSets
  rw [orSets_len]; simp

lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (PEqualNP.CleanedNonEdge.orStep n (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD k [] =
          (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD k [] := by
      intro k hk
      simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (PEqualNP.CleanedNonEdge.orStep n
            (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD (w - n) []) := by
          simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (PEqualNP.CleanedNonEdge.orStep n
            (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (PEqualNP.CleanedNonEdge.orStep n
          (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD j [] = [] := by
        simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma orSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (PEqualNP.CleanedNonEdge.orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
        x ∈ (PEqualNP.CleanedNonEdge.orSets n C).getD (w - n) []) := by
  have h := orSets_char n C.gates x k
  unfold PEqualNP.CleanedNonEdge.orSets gateAt
  rw [h]
  constructor
  · rintro ⟨_, h3⟩; exact h3
  · intro h3; exact ⟨hk, h3⟩

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + k) g ↔ k < C.gates.length ∧
      (g = k ∨ ((gateAt C k).op = GateOp.or ∧
        ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ PEqualNP.CleanedNonEdge.OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold PEqualNP.CleanedNonEdge.OrReaches PEqualNP.CleanedNonEdge.orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

lemma orReaches_self (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + j) j :=
  (orReaches_iff n C j j).mpr ⟨hj, Or.inl rfl⟩

lemma orReaches_step (n : ℕ) (C : Circuit) (j i g : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (h : PEqualNP.CleanedNonEdge.OrReaches n C i g) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + j) g :=
  (orReaches_iff n C j g).mpr ⟨hj, Or.inr ⟨hop, i, hi, hlt, h⟩⟩

lemma orIn_mem_filter {α : Type} (p : α → Prop) (d : DecidablePred p) (s : Finset α) (a : α) :
    a ∈ @Finset.filter α p d s ↔ a ∈ s ∧ p a :=
  @Finset.mem_filter α p d s a

lemma mem_orIn (n : ℕ) (C : Circuit) (w : ℕ) (i : Fin n) :
    i ∈ PEqualNP.TopForm.orIn n C w ↔ ((i : ℕ) = w ∨ ∃ k < C.gates.length,
      PEqualNP.CleanedNonEdge.OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧
        (i : ℕ) ∈ (gateAt C k).inputs) := by
  unfold PEqualNP.TopForm.orIn
  exact ⟨fun h => ((orIn_mem_filter _ _ _ _).1 h).2,
    fun h => (orIn_mem_filter _ _ _ _).2 ⟨Finset.mem_univ _, h⟩⟩

lemma orIn_self (n : ℕ) (C : Circuit) (i : Fin n) : i ∈ PEqualNP.TopForm.orIn n C i :=
  (mem_orIn n C i i).mpr (Or.inl rfl)

lemma orIn_up (n : ℕ) (C : Circuit) (j i : ℕ) (a : Fin n) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (h : a ∈ PEqualNP.TopForm.orIn n C i) : a ∈ PEqualNP.TopForm.orIn n C (n + j) := by
  rw [mem_orIn] at h ⊢
  right
  rcases h with h | ⟨k, hk, hr, hopk, hin⟩
  · exact ⟨j, hj, orReaches_self n C j hj, hop, by rw [h]; exact hi⟩
  · exact ⟨k, hk, orReaches_step n C j i k hj hop hi hlt hr, hopk, hin⟩


lemma orReaches_colour (n : ℕ) (C : Circuit) (κ : ℕ → Option Bool)
    (hor : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or →
      ∀ w ∈ (gateAt C j).inputs, ∀ c, κ w = some c → κ (n + j) = some c)
    (k : ℕ) (c : Bool) (hc : κ (n + k) = some c) :
    ∀ w, OrReaches n C w k → κ w = some c := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hr
    have hnw : n ≤ w := hr.1
    obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    obtain ⟨hj, heq | ⟨hop, u, hu, hlt, hur⟩⟩ := (orReaches_iff n C j k).mp hr
    · simpa only [heq] using hc
    · exact hor j hj hop u hu c (ih u hlt hur)

lemma orIn_colour (n : ℕ) (C : Circuit) (color : ℕ → Bool) (κ : ℕ → Option Bool)
    (hin : ∀ i < n, κ i = some (color i))
    (hor : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or →
      ∀ w ∈ (gateAt C j).inputs, ∀ c, κ w = some c → κ (n + j) = some c)
    (w : ℕ) (i : Fin n) (hi : i ∈ orIn n C w) : κ w = some (color i) := by
  rcases (mem_orIn n C w i).mp hi with heq | ⟨k, hk, hr, hop, hmem⟩
  · rw [← heq]
    exact hin i i.isLt
  · exact orReaches_colour n C κ hor k (color i)
      (hor k hk hop i hmem (color i) (hin i i.isLt)) w hr

lemma certificate_tCount_zero (n : ℕ) (C : Circuit) (color : ℕ → Bool)
    (κ : ℕ → Option Bool)
    (hin : ∀ i < n, κ i = some (color i))
    (hor : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or →
      ∀ w ∈ (gateAt C j).inputs, ∀ c, κ w = some c → κ (n + j) = some c) :
    tCount n C color = 0 := by
  unfold tCount
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  rcases (Finset.mem_filter.mp hj).2 with ⟨_, _, ⟨a, ha, hca⟩, ⟨b, hb, hcb⟩⟩
  have h1 := orIn_colour n C color κ hin hor (n + j) a ha
  have h2 := orIn_colour n C color κ hin hor (n + j) b hb
  rw [hca] at h1
  rw [hcb] at h2
  exact Bool.false_ne_true (Option.some.inj (h1.symm.trans h2))

end ColourCertificate

namespace GateMask

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_4970.Interval

lemma run_prefix (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
      change (run gs (step x g)).getD i false = _
      rw [ih _ (by simp only [step, List.length_append, List.length_singleton]; omega)]
      exact getD_append_left _ _ _ hi

def lookup (n : ℕ) (D : List Gate) (R : List ℕ) (w : ℕ) : ℕ :=
  if w < n then w else n + R.getD (w - n) D.length

def block (m u v : ℕ) (op : GateOp) (b : Bool) : List Gate :=
  if b then [⟨GateOp.and, [u, u]⟩, ⟨op, [m, v]⟩] else [⟨op, [u, v]⟩]

def extra (b : Bool) : ℕ := if b then 1 else 0

def advance (n : ℕ) (flags : ℕ → Bool) (st : List Gate × List ℕ) (g : Gate) :
    List Gate × List ℕ :=
  let u := lookup n st.1 st.2 (g.inputs.getD 0 0)
  let v := lookup n st.1 st.2 (g.inputs.getD 1 0)
  let b := flags st.2.length
  (st.1 ++ block (n + st.1.length) u v g.op b,
    st.2 ++ [st.1.length + extra b])

def build (n : ℕ) (flags : ℕ → Bool) (gs : List Gate) : List Gate × List ℕ :=
  gs.foldl (advance n flags) ([], [])

def transform (n : ℕ) (flags : ℕ → Bool) (C : Circuit) : Circuit :=
  let st := build n flags C.gates
  ⟨st.1, lookup n st.1 st.2 C.output⟩

lemma build_snoc (n : ℕ) (flags : ℕ → Bool) (gs : List Gate) (g : Gate) :
    build n flags (gs ++ [g]) = advance n flags (build n flags gs) g := by
  simp [build, List.foldl_append]

lemma block_length (m u v : ℕ) (op : GateOp) (b : Bool) :
    (block m u v op b).length = 1 + extra b := by
  cases b <;> simp [block, extra]

lemma block_run (w : List Bool) (u v : ℕ) (_hu : u < w.length) (hv : v < w.length)
    (op : GateOp) (b : Bool) :
    run (block w.length u v op b) w =
      w ++ ((if b then [w.getD u false] else []) ++
        [op.eval [w.getD u false, w.getD v false]]) := by
  cases b with
  | false => rfl
  | true =>
      change run [⟨GateOp.and, [u, u]⟩, ⟨op, [w.length, v]⟩] w =
        w ++ ([w.getD u false] ++ [op.eval [w.getD u false, w.getD v false]])
      simp only [run, List.foldl_cons, List.foldl_nil,
        step, List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
        id_eq, Bool.and_true, Bool.and_self]
      rw [getD_snoc, ite_eq_left rfl, getD_append_left _ _ _ hv]
      simp [List.append_assoc]

lemma block_value (w : List Bool) (u v : ℕ) (hu : u < w.length) (hv : v < w.length)
    (op : GateOp) (b : Bool) :
    (run (block w.length u v op b) w).getD (w.length + extra b) false =
      op.eval [w.getD u false, w.getD v false] := by
  rw [block_run w u v hu hv op b]
  cases b <;> simp [extra, List.getD_eq_getElem?_getD]

lemma lookup_input (n : ℕ) (D : List Gate) (R : List ℕ) (w : ℕ) (hw : w < n) :
    lookup n D R w = w := by simp [lookup, hw]

lemma lookup_gate (n : ℕ) (D : List Gate) (R : List ℕ) (j : ℕ) :
    lookup n D R (n + j) = n + R.getD j D.length := by simp [lookup]

lemma lookup_lt (n : ℕ) (D : List Gate) (R : List ℕ)
    (hR : ∀ j < R.length, R.getD j D.length < D.length)
    (w : ℕ) (hw : w < n + R.length) : lookup n D R w < n + D.length := by
  unfold lookup
  split_ifs with hn
  · omega
  · have h := hR (w - n) (by omega)
    omega

lemma lookup_old (n : ℕ) (D B : List Gate) (R : List ℕ) (q w : ℕ)
    (hw : w < n + R.length) :
    lookup n (D ++ B) (R ++ [q]) w = lookup n D R w := by
  unfold lookup
  split_ifs with hn
  · rfl
  · have hj : w - n < R.length := by omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj, hj]

lemma lookup_last (n : ℕ) (D B : List Gate) (R : List ℕ) (q : ℕ) :
    lookup n (D ++ B) (R ++ [q]) (n + R.length) = n + q := by
  simp [lookup, List.getD_eq_getElem?_getD]

lemma lookup_outside (n : ℕ) (D : List Gate) (R : List ℕ) (w : ℕ)
    (hw : n + R.length ≤ w) : lookup n D R w = n + D.length := by
  simp [lookup, show ¬ w < n by omega, List.getD_eq_getElem?_getD,
    List.getElem?_eq_none (show R.length ≤ w - n by omega)]

def Good (n : ℕ) (gs D : List Gate) (R : List ℕ) : Prop :=
  R.length = gs.length ∧
  (∀ j < R.length, R.getD j D.length < D.length) ∧
  (∀ (x : List Bool), x.length = n → ∀ w < n + gs.length,
    (run D x).getD (lookup n D R w) false = (run gs x).getD w false)

def BinaryBack (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j < gs.length, (gs.getD j ⟨GateOp.or, []⟩).inputs.length = 2 ∧
    ∀ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, w < n + j

lemma build_good (n : ℕ) (flags : ℕ → Bool) (gs : List Gate) (hgs : BinaryBack n gs) :
    Good n gs (build n flags gs).1 (build n flags gs).2 := by
  induction gs using List.reverseRecOn with
  | nil =>
      refine ⟨rfl, ?_, ?_⟩
      · simp [build]
      · intro x hx w hw
        simp only [List.length_nil, Nat.add_zero] at hw
        simp [build, lookup, hw, run]
  | append_singleton gs g ih =>
      have hpre : BinaryBack n gs := by
        intro j hj
        have h := hgs j (by simp; omega)
        simpa [List.getD_eq_getElem?_getD, List.getElem?_append_left hj, hj] using h
      have hlast := hgs gs.length (by simp)
      simp only [List.getD_eq_getElem?_getD] at hlast
      simp at hlast
      obtain ⟨u, v, huv⟩ := List.length_eq_two.mp hlast.1
      have hu : u < n + gs.length := hlast.2 u (by rw [huv]; simp)
      have hv : v < n + gs.length := hlast.2 v (by rw [huv]; simp)
      have ih' := ih hpre
      generalize hst : build n flags gs = st at ih'
      obtain ⟨D, R⟩ := st
      dsimp only [Good] at ih'
      obtain ⟨hRlen, hR, hsem⟩ := ih'
      let b := flags R.length
      let U := lookup n D R u
      let V := lookup n D R v
      let B := block (n + D.length) U V g.op b
      have hstep : build n flags (gs ++ [g]) = (D ++ B, R ++ [D.length + extra b]) := by
        rw [build_snoc, hst]
        simp [advance, huv, U, V, B, b]
      rw [hstep]
      refine ⟨by simp [hRlen], ?_, ?_⟩
      · intro j hj
        by_cases hjR : j < R.length
        · have hold := hR j hjR
          simpa [List.getD_eq_getElem?_getD, List.getElem?_append_left hjR, hjR,
            B, block_length] using Nat.lt_add_right (1 + extra b) hold
        · have heq : j = R.length := by simp only [List.length_append, List.length_singleton] at hj; omega
          subst j
          simp [List.getD_eq_getElem?_getD, B, block_length]
      · intro x hx w hw
        have hU : U < (run D x).length := by
          rw [run_length, hx]
          exact lookup_lt n D R hR u (by omega)
        have hV : V < (run D x).length := by
          rw [run_length, hx]
          exact lookup_lt n D R hR v (by omega)
        by_cases hwold : w < n + gs.length
        · rw [lookup_old n D B R _ w (by omega), run_append]
          rw [run_prefix B (run D x) _ (by rw [run_length, hx]; exact lookup_lt n D R hR w (by omega))]
          rw [hsem x hx w hwold, run_snoc]
          exact (getD_append_left _ _ _ (by rw [run_length, hx]; exact hwold)).symm
        · have heq : w = n + gs.length := by simp only [List.length_append, List.length_singleton] at hw; omega
          subst w
          rw [← hRlen, lookup_last, run_append]
          have hwl : (run D x).length = n + D.length := by rw [run_length, hx]
          have hb := block_value (run D x) U V hU hV g.op b
          rw [hwl] at hb
          change (run B (run D x)).getD (n + (D.length + extra b)) false = _
          rw [show n + (D.length + extra b) = n + D.length + extra b by omega, hb]
          rw [hsem x hx u hu, hsem x hx v hv, run_snoc]
          simp [step, huv, run_length, hx, hRlen]


lemma build_lengths (n : ℕ) (flags : ℕ → Bool) (gs : List Gate) :
    (build n flags gs).2.length = gs.length ∧
    (build n flags gs).1.length = gs.length +
      ((Finset.range gs.length).filter fun j => flags j = true).card := by
  induction gs using List.reverseRecOn with
  | nil => simp [build]
  | append_singleton gs g ih =>
      rw [build_snoc]
      generalize hst : build n flags gs = st at ih
      obtain ⟨D, R⟩ := st
      dsimp only at ih
      obtain ⟨hR, hD⟩ := ih
      have hc : ((Finset.range (gs.length + 1)).filter fun j => flags j = true).card =
          ((Finset.range gs.length).filter fun j => flags j = true).card + extra (flags gs.length) := by
        rw [Finset.range_add_one, Finset.filter_insert]
        cases hf : flags gs.length <;>
          simp [hf, extra, Finset.mem_filter, Finset.mem_range]
      constructor
      · simp [advance, hR]
      · simp only [advance, List.length_append, block_length, List.length_cons, List.length_nil]
        rw [hR, hD, hc]
        omega

lemma transform_wires (n : ℕ) (flags : ℕ → Bool) (C : Circuit)
    (hC : BinaryBack n C.gates) (x : Fin n → Bool) (w : ℕ) :
    ((transform n flags C).wires (List.ofFn x)).getD
      (lookup n (build n flags C.gates).1 (build n flags C.gates).2 w) false =
      (C.wires (List.ofFn x)).getD w false := by
  have hgood := build_good n flags C.gates hC
  by_cases hw : w < n + C.gates.length
  · exact hgood.2.2 (List.ofFn x) (by simp) w hw
  · have ho : n + (build n flags C.gates).2.length ≤ w := by rw [hgood.1]; omega
    rw [lookup_outside n _ _ w ho]
    change (run (build n flags C.gates).1 (List.ofFn x)).getD _ false =
      (run C.gates (List.ofFn x)).getD w false
    rw [getD_ge _ _ (by rw [run_length]; simp), getD_ge _ _ (by rw [run_length]; simp; omega)]

lemma transform_fun (n : ℕ) (flags : ℕ → Bool) (C : Circuit)
    (hC : BinaryBack n C.gates) :
    circuitFun n (transform n flags C) = circuitFun n C := by
  funext x
  exact transform_wires n flags C hC x C.output

lemma transform_size (n : ℕ) (flags : ℕ → Bool) (C : Circuit) :
    (transform n flags C).size = C.size +
      ((Finset.range C.gates.length).filter fun j => flags j = true).card := by
  exact (build_lengths n flags C.gates).2

def Legal (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j < gs.length, let g := gs.getD j ⟨GateOp.or, []⟩
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 ∧
      ∀ w ∈ g.inputs, w < n + j

lemma legal_binaryBack (n : ℕ) (gs : List Gate) (h : Legal n gs) : BinaryBack n gs := by
  intro j hj
  exact (h j hj).2

lemma legal_prefix (n : ℕ) (gs hs : List Gate) (h : Legal n (gs ++ hs)) : Legal n gs := by
  intro j hj
  have hh := h j (by simp; omega)
  simpa [List.getD_eq_getElem?_getD, List.getElem?_append_left hj, hj] using hh

lemma block_legal (m u v : ℕ) (op : GateOp) (b : Bool)
    (hu : u < m) (hv : v < m) (hop : op = GateOp.and ∨ op = GateOp.or) :
    Legal m (block m u v op b) := by
  intro j hj
  cases b with
  | false =>
      have hj0 : j = 0 := by simp [block] at hj; omega
      subst j
      simp [block, hop, hu, hv]
  | true =>
      have hj01 : j = 0 ∨ j = 1 := by simp [block] at hj; omega
      rcases hj01 with rfl | rfl
      · simp [block]
        omega
      · simp [block, hop]
        omega

lemma legal_append (n : ℕ) (gs hs : List Gate) (hgs : Legal n gs)
    (hhs : Legal (n + gs.length) hs) : Legal n (gs ++ hs) := by
  intro j hj
  by_cases hjg : j < gs.length
  · simpa [List.getD_eq_getElem?_getD, List.getElem?_append_left hjg, hjg] using hgs j hjg
  · have hge : gs.length ≤ j := by omega
    have hjh : j - gs.length < hs.length := by simp only [List.length_append] at hj; omega
    have h := hhs (j - gs.length) hjh
    simpa [List.getD_eq_getElem?_getD, List.getElem?_append_right hge,
      Nat.add_assoc, Nat.add_sub_of_le hge] using h

lemma build_legal (n : ℕ) (flags : ℕ → Bool) (gs : List Gate) (hgs : Legal n gs) :
    Legal n (build n flags gs).1 := by
  induction gs using List.reverseRecOn with
  | nil => simp [build, Legal]
  | append_singleton gs g ih =>
      have hpre := legal_prefix n gs [g] hgs
      have hlast := hgs gs.length (by simp)
      simp at hlast
      obtain ⟨u, v, huv⟩ := List.length_eq_two.mp hlast.2.1
      have hu : u < n + gs.length := hlast.2.2 u (by rw [huv]; simp)
      have hv : v < n + gs.length := hlast.2.2 v (by rw [huv]; simp)
      have hgood := build_good n flags gs (legal_binaryBack n gs hpre)
      have hlegal := ih hpre
      rw [build_snoc]
      generalize hst : build n flags gs = st at hgood hlegal
      obtain ⟨D, R⟩ := st
      dsimp only [Good] at hgood
      change Legal n D at hlegal
      apply legal_append n D _ hlegal
      apply block_legal
      · exact lookup_lt n D R hgood.2.1 _ (by simpa [hgood.1, huv] using hu)
      · exact lookup_lt n D R hgood.2.1 _ (by simpa [hgood.1, huv] using hv)
      · exact hlast.1

lemma ao2_legal (n : ℕ) (C : Circuit) (h : PEqualNP.TopForm.IsAO2 n C) : Legal n C.gates := by
  intro j hj
  have hmem := gateAt_mem C j hj
  exact ⟨h.1 _ hmem, h.2.2 _ hmem, h.2.1 j hj⟩

lemma legal_ao2 (n : ℕ) (C : Circuit) (h : Legal n C.gates) : PEqualNP.TopForm.IsAO2 n C := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    have hh := (h j hj).1
    simpa [List.getD_eq_getElem?_getD, hj] using hh
  · intro j hj w hw
    exact (h j hj).2.2 w hw
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    have hh := (h j hj).2.1
    simpa [List.getD_eq_getElem?_getD, hj] using hh

lemma transform_ao2 (n : ℕ) (flags : ℕ → Bool) (C : Circuit)
    (hC : PEqualNP.TopForm.IsAO2 n C) : PEqualNP.TopForm.IsAO2 n (transform n flags C) := by
  exact legal_ao2 n _ (build_legal n flags C.gates (ao2_legal n C hC))

end GateMask

namespace GateMask

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_4970.Interval

lemma block_op (m u v : ℕ) (op : GateOp) (b : Bool) :
    ((block m u v op b).getD (extra b) ⟨GateOp.or, []⟩).op = op := by
  cases b <;> rfl

lemma build_gate_op (n : ℕ) (flags : ℕ → Bool) (gs : List Gate) (hgs : Legal n gs) :
    ∀ j < gs.length,
      ((build n flags gs).1.getD
        ((build n flags gs).2.getD j (build n flags gs).1.length) ⟨GateOp.or, []⟩).op =
          (gs.getD j ⟨GateOp.or, []⟩).op := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
      have hpre := legal_prefix n gs [g] hgs
      have hgood := build_good n flags gs (legal_binaryBack n gs hpre)
      have ih' := ih hpre
      generalize hst : build n flags gs = st at hgood ih'
      obtain ⟨D, R⟩ := st
      obtain ⟨hRlen, hR, _⟩ := hgood
      dsimp only at hRlen hR ih'
      let b := flags R.length
      let U := lookup n D R (g.inputs.getD 0 0)
      let V := lookup n D R (g.inputs.getD 1 0)
      let B := block (n + D.length) U V g.op b
      have hstep : build n flags (gs ++ [g]) = (D ++ B, R ++ [D.length + extra b]) := by
        rw [build_snoc, hst]
        rfl
      rw [hstep]
      intro j hj
      by_cases hjold : j < gs.length
      · have hjR : j < R.length := by omega
        have hq := hR j hjR
        have hmap : (R ++ [D.length + extra b]).getD j (D ++ B).length =
            R.getD j D.length := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hjR, hjR]
        have hget : (D ++ B).getD (R.getD j D.length) ⟨GateOp.or, []⟩ =
            D.getD (R.getD j D.length) ⟨GateOp.or, []⟩ := by
          simp only [List.getD_eq_getElem?_getD]
          have hq' : R[j]?.getD D.length < D.length := by
            simpa only [List.getD_eq_getElem?_getD] using hq
          rw [List.getElem?_append_left hq']
        have horig : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hjold]
        rw [hmap, hget, horig]
        exact ih' j hjold
      · have heq : j = gs.length := by simp only [List.length_append, List.length_singleton] at hj; omega
        subst j
        have hmap : (R ++ [D.length + extra b]).getD gs.length (D ++ B).length =
            D.length + extra b := by
          rw [← hRlen]
          simp [List.getD_eq_getElem?_getD]
        have horig : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
          simp [List.getD_eq_getElem?_getD]
        rw [hmap, horig]
        simp only [List.getD_eq_getElem?_getD,
          List.getElem?_append_right (show D.length ≤ D.length + extra b by omega),
          Nat.add_sub_cancel_left]
        have hb := block_op (n + D.length) U V g.op b
        change (B[extra b]?.getD ⟨GateOp.or, []⟩).op = _
        simpa only [B, List.getD_eq_getElem?_getD] using hb

lemma transform_or_witness (n : ℕ) (flags : ℕ → Bool) (C : Circuit)
    (hC : PEqualNP.TopForm.IsAO2 n C) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (f : (Fin n → Bool) → Bool)
    (hf : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + j) false = f x) :
    ∃ k, k < (transform n flags C).gates.length ∧
      (gateAt (transform n flags C) k).op = GateOp.or ∧
      ∀ x : Fin n → Bool,
        ((transform n flags C).wires (List.ofFn x)).getD (n + k) false = f x := by
  let D := (build n flags C.gates).1
  let R := (build n flags C.gates).2
  let k := R.getD j D.length
  have hlegal := ao2_legal n C hC
  have hb := legal_binaryBack n C.gates hlegal
  have hgood := build_good n flags C.gates hb
  have hjR : j < R.length := by dsimp [R]; rw [hgood.1]; exact hj
  refine ⟨k, hgood.2.1 j hjR, ?_, ?_⟩
  · have h := build_gate_op n flags C.gates hlegal j hj
    change (gateAt (transform n flags C) k).op = (gateAt C j).op at h
    exact h.trans hop
  · intro x
    have h := transform_wires n flags C hb x (n + j)
    rw [lookup_gate] at h
    exact h.trans (hf x)

end GateMask

namespace GateMaskColor

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.TwoColour
open PEqualNP.Outside.L_meta_4970.GateMask
open PEqualNP.Outside.L_meta_4970.ColourCertificate

def readLabel (n : ℕ) (color : ℕ → Bool) (K : List (Option Bool)) (w : ℕ) : Option Bool :=
  if w < n then some (color w) else K.getD (w - n) none

def mergeLabel (u v : Option Bool) : Option Bool :=
  match u with
  | none => v
  | some c => some c

def nextLabel (op : GateOp) (b : Bool) (u v : Option Bool) : Option Bool :=
  @ite (Option Bool) (op = GateOp.or) (gateOpDecEq op GateOp.or)
    (if b then v else mergeLabel u v) none

def labelBlock (op : GateOp) (b : Bool) (u v : Option Bool) : List (Option Bool) :=
  if b then [none, nextLabel op b u v] else [nextLabel op b u v]

def Compatible (u v : Option Bool) : Prop :=
  ∀ c d, u = some c → v = some d → c = d

lemma mergeLabel_children (u v : Option Bool) (h : Compatible u v) (c : Bool) :
    u = some c ∨ v = some c → mergeLabel u v = some c := by
  intro hc
  cases u with
  | none => simpa [mergeLabel] using hc
  | some d =>
      rcases hc with hc | hc
      · simpa [mergeLabel] using hc
      · have heq := h d c rfl hc
        simp [mergeLabel, heq]

lemma nextLabel_witness (op : GateOp) (b : Bool) (u v : Option Bool) (c : Bool)
    (h : nextLabel op b u v = some c) :
    op = GateOp.or ∧ (u = some c ∨ v = some c) := by
  unfold nextLabel at h
  split_ifs at h with hop hb
  · exact ⟨hop, Or.inr h⟩
  · refine ⟨hop, ?_⟩
    cases u with
    | none => exact Or.inr h
    | some d => exact Or.inl h

lemma labelBlock_length (op : GateOp) (b : Bool) (u v : Option Bool) :
    (labelBlock op b u v).length = 1 + extra b := by
  cases b <;> simp [labelBlock, extra]

lemma readLabel_input (n : ℕ) (color : ℕ → Bool) (K : List (Option Bool))
    (w : ℕ) (hw : w < n) : readLabel n color K w = some (color w) := by
  simp [readLabel, hw]

lemma readLabel_old (n : ℕ) (color : ℕ → Bool) (K L : List (Option Bool))
    (w : ℕ) (hw : w < n + K.length) :
    readLabel n color (K ++ L) w = readLabel n color K w := by
  unfold readLabel
  split_ifs with hn
  · rfl
  · have hj : w - n < K.length := by omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj, hj]

lemma readLabel_at (n : ℕ) (color : ℕ → Bool) (K L : List (Option Bool)) (j : ℕ) :
    readLabel n color (K ++ L) (n + K.length + j) = L.getD j none := by
  simp [readLabel, List.getD_eq_getElem?_getD, Nat.add_assoc,
    List.getElem?_append_right (show K.length ≤ K.length + j by omega)]

lemma readLabel_last (n : ℕ) (color : ℕ → Bool) (K : List (Option Bool))
    (op : GateOp) (b : Bool) (u v : Option Bool) :
    readLabel n color (K ++ labelBlock op b u v) (n + K.length + extra b) =
      nextLabel op b u v := by
  rw [readLabel_at]
  cases b <;> simp [labelBlock, extra]

def Cert (n : ℕ) (color : ℕ → Bool) (D : List Gate) (K : List (Option Bool)) : Prop :=
  ∀ j < D.length, (D.getD j ⟨GateOp.or, []⟩).op = GateOp.or →
    ∀ w ∈ (D.getD j ⟨GateOp.or, []⟩).inputs, ∀ c,
      readLabel n color K w = some c → readLabel n color K (n + j) = some c

lemma cert_append (n : ℕ) (color : ℕ → Bool) (D : List Gate) (K : List (Option Bool))
    (hlen : K.length = D.length) (hlegal : Legal n D) (hcert : Cert n color D K)
    (u v : ℕ) (hu : u < n + D.length) (hv : v < n + D.length)
    (op : GateOp) (b : Bool)
    (hcompat : op = GateOp.or → b = false → Compatible (readLabel n color K u) (readLabel n color K v)) :
    Cert n color (D ++ block (n + D.length) u v op b)
      (K ++ labelBlock op b (readLabel n color K u) (readLabel n color K v)) := by
  intro j hj hop w hw c hc
  by_cases hjD : j < D.length
  · have hget : (D ++ block (n + D.length) u v op b).getD j ⟨GateOp.or, []⟩ =
        D.getD j ⟨GateOp.or, []⟩ := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hjD, hjD]
    rw [hget] at hop hw
    have hwlt := (hlegal j hjD).2.2 w hw
    rw [readLabel_old _ _ _ _ _ (by omega)] at hc
    rw [readLabel_old _ _ _ _ _ (by omega)]
    exact hcert j hjD hop w hw c hc
  · obtain ⟨q, rfl⟩ : ∃ q, j = D.length + q := ⟨j - D.length, by omega⟩
    have hq : q < (block (n + D.length) u v op b).length := by
      simp only [List.length_append] at hj
      omega
    have hget : (D ++ block (n + D.length) u v op b).getD (D.length + q) ⟨GateOp.or, []⟩ =
        (block (n + D.length) u v op b).getD q ⟨GateOp.or, []⟩ := by
      simp [List.getD_eq_getElem?_getD,
        List.getElem?_append_right (show D.length ≤ D.length + q by omega)]
    rw [hget] at hop hw
    cases b with
    | false =>
        have hq0 : q = 0 := by simpa [block] using hq
        subst q
        simp only [block, Bool.false_eq_true, ite_false, List.getD_cons_zero] at hop hw
        subst op
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · rw [readLabel_old _ _ _ _ _ (by omega)] at hc
          simpa [hlen, labelBlock, nextLabel, extra, Nat.add_assoc] using
            (readLabel_last n color K GateOp.or false _ _).trans
              (mergeLabel_children _ _ (hcompat rfl rfl) c (Or.inl hc))
        · rw [readLabel_old _ _ _ _ _ (by omega)] at hc
          simpa [hlen, labelBlock, nextLabel, extra, Nat.add_assoc] using
            (readLabel_last n color K GateOp.or false _ _).trans
              (mergeLabel_children _ _ (hcompat rfl rfl) c (Or.inr hc))
    | true =>
        have hq01 : q = 0 ∨ q = 1 := by simp [block] at hq; omega
        rcases hq01 with rfl | rfl
        · simp [block] at hop
        · simp only [block, ite_true, List.getD_cons_succ, List.getD_cons_zero] at hop hw
          subst op
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
          rcases hw with rfl | rfl
          · have hh := readLabel_at n color K
                (labelBlock GateOp.or true (readLabel n color K u) (readLabel n color K v)) 0
            have hnone : readLabel n color (K ++ labelBlock GateOp.or true (readLabel n color K u) (readLabel n color K v)) (n + D.length) = none := by
              simpa [hlen, labelBlock] using hh
            rw [hnone] at hc
            cases hc
          · rw [readLabel_old _ _ _ _ _ (by omega)] at hc
            have hh := readLabel_last n color K GateOp.or true
              (readLabel n color K u) (readLabel n color K w)
            have hh' : readLabel n color (K ++ labelBlock GateOp.or true
                (readLabel n color K u) (readLabel n color K w)) (n + (D.length + 1)) =
                readLabel n color K w := by
              simpa only [nextLabel, ite_eq_left rfl, ite_true, extra, hlen, Nat.add_assoc] using hh
            exact hh'.trans hc


def paintAdvance (n : ℕ) (flags color : ℕ → Bool)
    (st : (List Gate × List ℕ) × List (Option Bool)) (g : Gate) :
    (List Gate × List ℕ) × List (Option Bool) :=
  let U := lookup n st.1.1 st.1.2 (g.inputs.getD 0 0)
  let V := lookup n st.1.1 st.1.2 (g.inputs.getD 1 0)
  (advance n flags st.1 g, st.2 ++ labelBlock g.op (flags st.1.2.length)
    (readLabel n color st.2 U) (readLabel n color st.2 V))

def paintBuild (n : ℕ) (flags color : ℕ → Bool) (gs : List Gate) :
    (List Gate × List ℕ) × List (Option Bool) :=
  gs.foldl (paintAdvance n flags color) (([], []), [])

lemma paintBuild_snoc (n : ℕ) (flags color : ℕ → Bool) (gs : List Gate) (g : Gate) :
    paintBuild n flags color (gs ++ [g]) =
      paintAdvance n flags color (paintBuild n flags color gs) g := by
  simp [paintBuild, List.foldl_append]

lemma paintBuild_first (n : ℕ) (flags color : ℕ → Bool) (gs : List Gate) :
    (paintBuild n flags color gs).1 = build n flags gs := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
      rw [paintBuild_snoc, build_snoc]
      change advance n flags (paintBuild n flags color gs).1 g = _
      rw [ih]

def PaintGood (n : ℕ) (color : ℕ → Bool) (C : Circuit) (gs : List Gate)
    (st : (List Gate × List ℕ) × List (Option Bool)) : Prop :=
  st.2.length = st.1.1.length ∧ Cert n color st.1.1 st.2 ∧
  ∀ w < n + gs.length, ∀ c, readLabel n color st.2 (lookup n st.1.1 st.1.2 w) = some c →
    ∃ i : Fin n, i ∈ orIn n C w ∧ color i = c

lemma orIn_color_unique (n : ℕ) (color : ℕ → Bool) (C : Circuit) (j : ℕ)
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or)
    (hn : ¬ IsTwoColour n C color j) (a b : Fin n)
    (ha : a ∈ orIn n C (n + j)) (hb : b ∈ orIn n C (n + j)) : color a = color b := by
  cases hca : color a <;> cases hcb : color b
  · rfl
  · exact False.elim (hn ⟨hj, hop, ⟨a, ha, hca⟩, ⟨b, hb, hcb⟩⟩)
  · exact False.elim (hn ⟨hj, hop, ⟨b, hb, hcb⟩, ⟨a, ha, hca⟩⟩)
  · rfl

lemma paint_good (n : ℕ) (flags color : ℕ → Bool) (C : Circuit)
    (hC : IsAO2 n C)
    (hflags : ∀ j < C.gates.length, flags j = false → ¬ IsTwoColour n C color j)
    (gs : List Gate) (hp : ∃ post, C.gates = gs ++ post) :
    PaintGood n color C gs (paintBuild n flags color gs) := by
  induction gs using List.reverseRecOn with
  | nil =>
      refine ⟨rfl, ?_, ?_⟩
      · simp [paintBuild, Cert]
      · intro w hw c hc
        have hw' : w < n := by simpa using hw
        have heq : color w = c := by
          simpa [paintBuild, lookup, readLabel, hw'] using hc
        exact ⟨⟨w, hw'⟩, orIn_self n C ⟨w, hw'⟩, heq⟩
  | append_singleton gs g ih =>
      obtain ⟨post, hp⟩ := hp
      have hp' : C.gates = gs ++ (g :: post) := by simpa [List.append_assoc] using hp
      have hj : gs.length < C.gates.length := by rw [hp']; simp
      have hgj : gateAt C gs.length = g := by
        simp [gateAt, hp', List.getD_eq_getElem?_getD]
      have hgmem : g ∈ C.gates := by rw [hp']; simp
      obtain ⟨u, v, huv⟩ := List.length_eq_two.mp (hC.2.2 g hgmem)
      have hu : u < n + gs.length := by
        apply hC.2.1 gs.length hj u
        rw [hgj, huv]
        simp
      have hv : v < n + gs.length := by
        apply hC.2.1 gs.length hj v
        rw [hgj, huv]
        simp
      have hpre : Legal n gs := by
        apply legal_prefix n gs (g :: post)
        rw [← hp']
        exact ao2_legal n C hC
      have hgood := build_good n flags gs (legal_binaryBack n gs hpre)
      have hlegal := build_legal n flags gs hpre
      have ih' := ih ⟨g :: post, hp'⟩
      have hfirst := paintBuild_first n flags color gs
      generalize hst : paintBuild n flags color gs = st at ih' hfirst
      obtain ⟨⟨D,R⟩,K⟩ := st
      change (D,R) = build n flags gs at hfirst
      rw [← hfirst] at hgood hlegal
      dsimp only [Good] at hgood
      dsimp only [PaintGood] at ih'
      change Legal n D at hlegal
      obtain ⟨hRlen, hR, hsem⟩ := hgood
      obtain ⟨hKlen, hcert, hwit⟩ := ih'
      let b := flags R.length
      let U := lookup n D R u
      let V := lookup n D R v
      let B := block (n + D.length) U V g.op b
      let L := labelBlock g.op b (readLabel n color K U) (readLabel n color K V)
      have hU : U < n + D.length := lookup_lt n D R hR u (by omega)
      have hV : V < n + D.length := lookup_lt n D R hR v (by omega)
      have hstep : paintBuild n flags color (gs ++ [g]) =
          ((D ++ B, R ++ [D.length + extra b]), K ++ L) := by
        rw [paintBuild_snoc, hst]
        simp [paintAdvance, advance, huv, U, V, B, L, b]
      rw [hstep]
      have hcompat : g.op = GateOp.or → b = false →
          Compatible (readLabel n color K U) (readLabel n color K V) := by
        intro hop hb c d hc hd
        obtain ⟨a, ha, hca⟩ := hwit u hu c hc
        obtain ⟨a', ha', hca'⟩ := hwit v hv d hd
        have hop' : (gateAt C gs.length).op = GateOp.or := by rw [hgj]; exact hop
        have hia : u ∈ (gateAt C gs.length).inputs := by rw [hgj, huv]; simp
        have hib : v ∈ (gateAt C gs.length).inputs := by rw [hgj, huv]; simp
        have h1 := orIn_up n C gs.length u a hj hop' hia hu ha
        have h2 := orIn_up n C gs.length v a' hj hop' hib hv ha'
        have hn := hflags gs.length hj (by simpa [b, hRlen] using hb)
        exact hca.symm.trans ((orIn_color_unique n color C gs.length hj hop' hn a a' h1 h2).trans hca')
      refine ⟨?_, ?_, ?_⟩
      · simp [L, B, labelBlock_length, block_length, hKlen]
      · exact cert_append n color D K hKlen hlegal hcert U V hU hV g.op b hcompat
      · intro w hw c hc
        by_cases hold : w < n + gs.length
        · rw [lookup_old n D B R _ w (by omega)] at hc
          rw [readLabel_old n color K L _ (by rw [hKlen]; exact lookup_lt n D R hR w (by omega))] at hc
          exact hwit w hold c hc
        · have heq : w = n + gs.length := by simp only [List.length_append, List.length_singleton] at hw; omega
          subst w
          rw [← hRlen, lookup_last] at hc
          have hlast := readLabel_last n color K g.op b (readLabel n color K U) (readLabel n color K V)
          have hn : nextLabel g.op b (readLabel n color K U) (readLabel n color K V) = some c := by
            rw [hKlen] at hlast
            exact hlast.symm.trans (by simpa [L, Nat.add_assoc] using hc)
          obtain ⟨hop, huc | hvc⟩ := nextLabel_witness g.op b _ _ c hn
          · obtain ⟨a, ha, hca⟩ := hwit u hu c huc
            refine ⟨a, ?_, hca⟩
            apply orIn_up n C gs.length u a hj (by rw [hgj]; exact hop) _ hu ha
            rw [hgj, huv]; simp
          · obtain ⟨a, ha, hca⟩ := hwit v hv c hvc
            refine ⟨a, ?_, hca⟩
            apply orIn_up n C gs.length v a hj (by rw [hgj]; exact hop) _ hv ha
            rw [hgj, huv]; simp

lemma transform_tCount_zero (n : ℕ) (flags color : ℕ → Bool) (C : Circuit)
    (hC : IsAO2 n C)
    (hflags : ∀ j < C.gates.length, flags j = false → ¬ IsTwoColour n C color j) :
    tCount n (transform n flags C) color = 0 := by
  have hp := paint_good n flags color C hC hflags C.gates ⟨[], by simp⟩
  have hf := paintBuild_first n flags color C.gates
  generalize hst : paintBuild n flags color C.gates = st at hp hf
  obtain ⟨⟨D,R⟩,K⟩ := st
  dsimp only [PaintGood] at hp
  change (D,R) = build n flags C.gates at hf
  unfold transform
  rw [← hf]
  apply certificate_tCount_zero n _ color (readLabel n color K)
  · intro i hi
    exact readLabel_input n color K i hi
  · exact hp.2.1

end GateMaskColor

namespace TCount

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.TwoColour
open PEqualNP.Outside.L_meta_4970.GateMask
open PEqualNP.Outside.L_meta_4970.GateMaskColor

def flags (n : ℕ) (C : Circuit) (color : ℕ → Bool) (j : ℕ) : Bool :=
  decide (IsTwoColour n C color j)

lemma flags_count (n : ℕ) (C : Circuit) (color : ℕ → Bool) :
    ((Finset.range C.gates.length).filter fun j => flags n C color j = true).card =
      tCount n C color := by
  simp only [flags, decide_eq_true_eq, tCount, twoColour]

lemma flags_adequate (n : ℕ) (C : Circuit) (color : ℕ → Bool) :
    ∀ j < C.gates.length, flags n C color j = false → ¬ IsTwoColour n C color j := by
  intro j _ hj
  simpa only [flags, decide_eq_false_iff_not] using hj

lemma exists_zero_mixed_tCount (n : ℕ) (C : Circuit) (color : ℕ → Bool)
    (hC : IsAO2 n C) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size = C.size + tCount n C color ∧
      circuitFun n D = circuitFun n C ∧ tCount n D color = 0 ∧
      ∀ (j : ℕ), j < C.gates.length → (gateAt C j).op = GateOp.or →
        ∀ f : (Fin n → Bool) → Bool,
          (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + j) false = f x) →
          ∃ k : ℕ, k < D.gates.length ∧ (gateAt D k).op = GateOp.or ∧
            ∀ x : Fin n → Bool, (D.wires (List.ofFn x)).getD (n + k) false = f x := by
  let D := transform n (flags n C color) C
  refine ⟨D, transform_ao2 n _ C hC, ?_, ?_, ?_, ?_⟩
  · exact (transform_size n _ C).trans (congrArg (C.size + ·) (flags_count n C color))
  · exact transform_fun n _ C (legal_binaryBack n C.gates (ao2_legal n C hC))
  · exact transform_tCount_zero n _ color C hC (flags_adequate n C color)
  · intro j hj hop f hf
    exact transform_or_witness n _ C hC j hj hop f hf

end TCount

end PEqualNP.Outside.L_meta_4970
