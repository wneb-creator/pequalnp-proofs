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

end PEqualNP.Outside.L_meta_4970
