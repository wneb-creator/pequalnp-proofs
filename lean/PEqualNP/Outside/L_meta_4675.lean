import PEqualNP.Defs
import Mathlib.Tactic.Push

namespace PEqualNP.Outside.L_meta_4675

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.TwoColour

lemma no_mixed_or {n : ℕ} {C : Circuit} {colour : ℕ → Bool}
    (ht : tCount n C colour = 0) {g : ℕ} (hg : g < C.gates.length)
    (hop : (gateAt C g).op = GateOp.or) {i j : Fin n}
    (hi : i ∈ orIn n C (n + g)) (hj : j ∈ orIn n C (n + g))
    (hci : colour i = false) (hcj : colour j = true) : False := by
  have hmem : g ∈ twoColour n C colour :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hg,
      hg, hop, ⟨i, hi, hci⟩, ⟨j, hj, hcj⟩⟩
  have hempty : twoColour n C colour = ∅ := Finset.card_eq_zero.mp ht
  simpa [hempty] using hmem

lemma no_point_line_or {p l : ℕ} {C : Circuit}
    (ht : tCount (p + l) C (fun i => decide (p ≤ i)) = 0)
    {g : ℕ} (hg : g < C.gates.length) (hop : (gateAt C g).op = GateOp.or)
    {a : Fin p} {b : Fin l}
    (ha : Fin.castAdd l a ∈ orIn (p + l) C (p + l + g))
    (hb : Fin.natAdd p b ∈ orIn (p + l) C (p + l + g)) : False := by
  apply no_mixed_or ht hg hop ha hb
  · simp only [Fin.coe_castAdd, decide_eq_false_iff_not, not_le]
    exact a.isLt
  · simp

end PEqualNP.Outside.L_meta_4675

namespace PEqualNP.Outside.L_meta_4675.Reuse

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadK

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl
lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega
lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key
def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false
lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl
lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]
lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj
lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)
lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega
lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj
lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [ite_eq_right hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩
lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
    · rw [ite_eq_right hlt] at h'; cases h'
  · intro h i hi
    rw [ite_eq_left (h i hi).1]; exact (h i hi).2
lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]
lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl
lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega
lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega
lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma inCone_trans (n : ℕ) (C : Circuit) (a k : ℕ) (hak : InCone n C a k) :
    ∀ j, InCone n C k j → InCone n C a j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k2, hk2, hin, h3 | h3⟩ := h
    · subst h3
      rw [inCone_iff]
      exact ⟨h0, k, hk2, hin, Or.inr hak⟩
    · rw [inCone_iff]
      exact ⟨h0, k2, hk2, hin, Or.inr (ih k2 hk2 h3)⟩

def reachable (n : ℕ) (C : Circuit) (k : ℕ) : Prop :=
  k < C.gates.length ∧ (n + k = C.output ∨ InCone n C k (C.output - n))

lemma reachable_child {n : ℕ} {C : Circuit} (rb : ReadsBack n C)
    {k j : ℕ} (hk : reachable n C k) (hj : n + j ∈ (gateAt C k).inputs) :
    reachable n C j := by
  have hlt := rb k hk.1 (n + j) hj
  have hbound := hk.1
  refine ⟨by omega, Or.inr ?_⟩
  have hcone : InCone n C j k := (inCone_iff n C j k).2
    ⟨hk.1, j, by omega, hj, Or.inl rfl⟩
  rcases hk.2 with h | h
  · rwa [show C.output - n = k by omega]
  · exact inCone_trans n C j k hcone _ h

lemma cone_reader {n : ℕ} {C : Circuit} {i j : ℕ} (h : InCone n C i j) :
    ∃ k, k < C.gates.length ∧ (k = j ∨ InCone n C k j) ∧
      n + i ∈ (gateAt C k).inputs := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    obtain ⟨hj, k, hkj, hin, rfl | hc⟩ := (inCone_iff n C i j).1 h
    · exact ⟨j, hj, Or.inl rfl, hin⟩
    · obtain ⟨l, hl, rfl | hlc, hread⟩ := ih k hkj hc
      · exact ⟨l, hl, Or.inr ((inCone_iff n C l j).2
          ⟨hj, l, hkj, hin, Or.inl rfl⟩), hread⟩
      · exact ⟨l, hl, Or.inr ((inCone_iff n C l j).2
          ⟨hj, k, hkj, hin, Or.inr hlc⟩), hread⟩

lemma reachable_reader {n : ℕ} {C : Circuit} {i : ℕ}
    (hi : reachable n C i) (hne : i ≠ C.output - n) :
    ∃ k, reachable n C k ∧ n + i ∈ (gateAt C k).inputs := by
  rcases hi.2 with he | hc
  · omega
  · obtain ⟨k, hk, hr | hr, hin⟩ := cone_reader hc
    · have hn : n ≤ C.output := by
        by_contra h
        obtain ⟨_, j, hj, _, _⟩ := (inCone_iff n C i (C.output - n)).1 hc
        omega
      exact ⟨k, ⟨hk, Or.inl (by omega)⟩, hin⟩
    · exact ⟨k, ⟨hk, Or.inr hr⟩, hin⟩

def singletonSupport (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun u => val C (List.ofFn (pairInput u u)) w = true

lemma mem_support {n : ℕ} {C : Circuit} {w : ℕ} {u : Fin n} :
    u ∈ singletonSupport n C w ↔ val C (List.ofFn (pairInput u u)) w = true := by
  simp [singletonSupport]

lemma support_input {n : ℕ} {C : Circuit} (u : Fin n) :
    singletonSupport n C u.val = {u} := by
  ext v
  rw [mem_support, val_ofFn]
  simp [pairInput, eq_comm]

lemma support_or {n : ℕ} {C : Circuit} (rb : ReadsBack n C)
    {k : ℕ} (hk : k < C.gates.length) (hop : (gateAt C k).op = GateOp.or) (u : Fin n) :
    u ∈ singletonSupport n C (n + k) ↔
      ∃ w ∈ (gateAt C k).inputs, u ∈ singletonSupport n C w := by
  simp only [mem_support, val_or (by simp : (List.ofFn (pairInput u u)).length = n) hk hop]
  exact ⟨fun ⟨w, hw, _, ht⟩ => ⟨w, hw, ht⟩, fun ⟨w, hw, ht⟩ => ⟨w, hw, rb k hk w hw, ht⟩⟩

lemma gate_op {C : Circuit} (hm : Monotone2 C) {k : ℕ} (hk : k < C.gates.length) :
    (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or := by
  simpa using (hm _ (gateAt_mem hk)).1

lemma input_card {C : Circuit} (hm : Monotone2 C) {k : ℕ} (hk : k < C.gates.length) :
    (gateAt C k).inputs.toFinset.card ≤ 2 :=
  (List.toFinset_card_le _).trans (hm _ (gateAt_mem hk)).2

noncomputable def births (n : ℕ) (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter fun k =>
    reachable n C k ∧ (gateAt C k).op = GateOp.and ∧
      ∃ a b, (gateAt C k).inputs = [a, b] ∧
        (singletonSupport n C a).Nonempty ∧ (singletonSupport n C b).Nonempty

lemma mem_births {n : ℕ} {C : Circuit} {k : ℕ} :
    k ∈ births n C ↔ reachable n C k ∧ (gateAt C k).op = GateOp.and ∧
      ∃ a b, (gateAt C k).inputs = [a, b] ∧
        (singletonSupport n C a).Nonempty ∧ (singletonSupport n C b).Nonempty := by
  classical
  simp only [births, Finset.mem_filter, Finset.mem_range]
  exact ⟨And.right, fun h => ⟨h.1.1, h⟩⟩

def positiveInputs (n : ℕ) (C : Circuit) (k : ℕ) : Finset ℕ := by
  classical
  exact (gateAt C k).inputs.toFinset.filter fun w => (singletonSupport n C w).Nonempty

lemma mem_positiveInputs {n : ℕ} {C : Circuit} {k w : ℕ} :
    w ∈ positiveInputs n C k ↔ w ∈ (gateAt C k).inputs ∧ (singletonSupport n C w).Nonempty := by
  classical
  simp [positiveInputs]

noncomputable def merges (n : ℕ) (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter fun k =>
    reachable n C k ∧ (gateAt C k).op = GateOp.or ∧
      1 < (singletonSupport n C (n + k)).card ∧ 1 < (positiveInputs n C k).card

lemma mem_merges {n : ℕ} {C : Circuit} {k : ℕ} :
    k ∈ merges n C ↔ reachable n C k ∧ (gateAt C k).op = GateOp.or ∧
      1 < (singletonSupport n C (n + k)).card ∧ 1 < (positiveInputs n C k).card := by
  classical
  simp only [merges, Finset.mem_filter, Finset.mem_range]
  exact ⟨And.right, fun h => ⟨h.1.1, h⟩⟩

-- Each reachable wire with empty singleton support other than the output
-- is read by some reachable gate. Counting these reads pays for connecting
-- the edge-producing AND gates, even when the circuit shares subcircuits.
lemma gate_budget {n : ℕ} {C : Circuit} (hm : Monotone2 C) (rb : ReadsBack n C)
    (hclean : ∀ k, reachable n C k → (gateAt C k).op = GateOp.and →
      singletonSupport n C (n + k) = ∅) :
    2 * (births n C).card + (merges n C).card ≤ C.size + 1 := by
  classical
  let R := (Finset.range C.gates.length).filter (reachable n C)
  let Z := R.filter fun k => singletonSupport n C (n + k) = ∅
  let D := fun k => (gateAt C k).inputs.toFinset.filter fun w =>
    n ≤ w ∧ singletonSupport n C w = ∅
  let E := fun k => (D k).image fun w => w - n
  have hR (k) : k ∈ R ↔ reachable n C k := by
    simp only [R, Finset.mem_filter, Finset.mem_range]
    exact ⟨And.right, fun h => ⟨h.1, h⟩⟩
  have hZ (k) : k ∈ Z ↔ k ∈ R ∧ singletonSupport n C (n + k) = ∅ := Finset.mem_filter
  have hread : Z.erase (C.output - n) ⊆ R.biUnion E := by
    intro j hj
    obtain ⟨hne, hz⟩ := Finset.mem_erase.1 hj
    obtain ⟨k, hk, hin⟩ := reachable_reader ((hR j).1 ((hZ j).1 hz).1) hne
    refine Finset.mem_biUnion.2 ⟨k, (hR k).2 hk, Finset.mem_image.2 ⟨n + j, ?_, by omega⟩⟩
    exact Finset.mem_filter.2 ⟨List.mem_toFinset.2 hin, by omega, ((hZ j).1 hz).2⟩
  have hsum : Z.card ≤ (∑ k ∈ R, (D k).card) + 1 := by
    calc
      Z.card ≤ (Z.erase (C.output - n)).card + 1 := by
        by_cases h : C.output - n ∈ Z
        · exact Nat.le_of_eq (Finset.card_erase_add_one h).symm
        · rw [Finset.erase_eq_of_notMem h]; omega
      _ ≤ (R.biUnion E).card + 1 := Nat.add_le_add_right (Finset.card_le_card hread) _
      _ ≤ (∑ k ∈ R, (E k).card) + 1 := Nat.add_le_add_right Finset.card_biUnion_le _
      _ ≤ _ := Nat.add_le_add_right (Finset.sum_le_sum fun _ _ => Finset.card_image_le) _
  have hlocal : ∀ k ∈ R, (D k).card + 2 * (if k ∈ births n C then 1 else 0) +
      (if k ∈ merges n C then 1 else 0) ≤ 1 + (if k ∈ Z then 1 else 0) := by
    intro k hk
    have hr := (hR k).1 hk
    have hdp : Disjoint (D k) (positiveInputs n C k) := by
      rw [Finset.disjoint_left]
      intro w hd hp
      have he := (Finset.mem_filter.1 hd).2.2
      simpa [he] using (mem_positiveInputs.1 hp).2
    have hcap : (D k).card + (positiveInputs n C k).card ≤ 2 := by
      rw [← Finset.card_union_of_disjoint hdp]
      exact (Finset.card_le_card (Finset.union_subset
        (Finset.filter_subset _ _) (Finset.filter_subset _ _))).trans (input_card hm hr.1)
    by_cases hb : k ∈ births n C
    · obtain ⟨_, hop, a, b, hab, ha, hb'⟩ := mem_births.1 hb
      have hz := (hZ k).2 ⟨hk, hclean k hr hop⟩
      have hl : k ∉ merges n C := by
        intro h
        have hh := (mem_merges.1 h).2.1
        rw [hop] at hh
        cases hh
      have hd : D k = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.2
        intro w hw
        have hw' := Finset.mem_filter.1 hw
        have hh : w = a ∨ w = b := by simpa [hab] using hw'.1
        rcases hh with rfl | rfl
        · simp [hw'.2.2] at ha
        · simp [hw'.2.2] at hb'
      simp [hb, hz, hl, hd]
    · by_cases hl : k ∈ merges n C
      · have hpos := (mem_merges.1 hl).2.2.2
        simp only [hb, hl, ite_false, ite_true, Nat.mul_zero, Nat.add_zero]
        split_ifs <;> omega
      · by_cases hz : k ∈ Z
        · simp only [hb, hl, hz, ite_false, ite_true, Nat.mul_zero, Nat.add_zero]
          omega
        · have hs : (singletonSupport n C (n + k)).Nonempty :=
            Finset.nonempty_iff_ne_empty.2 fun h => hz ((hZ k).2 ⟨hk, h⟩)
          have hop : (gateAt C k).op = GateOp.or :=
            (gate_op hm hr.1).resolve_left fun h => hs.ne_empty (hclean k hr h)
          obtain ⟨u, hu⟩ := hs
          obtain ⟨w, hw, huw⟩ := (support_or rb hr.1 hop u).1 hu
          have hpos := Finset.card_pos.2 ⟨w, mem_positiveInputs.2 ⟨hw, u, huw⟩⟩
          simp only [hb, hl, hz, ite_false, Nat.mul_zero, Nat.add_zero]
          omega
  have count (T : Finset ℕ) (hT : T ⊆ R) :
      (∑ k ∈ R, if k ∈ T then 1 else 0) = T.card := by
    rw [← Finset.card_filter]
    congr 1
    ext k
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun h => ⟨hT h, h⟩⟩
  have hB : births n C ⊆ R := fun _ h => (hR _).2 (mem_births.1 h).1
  have hL : merges n C ⊆ R := fun _ h => (hR _).2 (mem_merges.1 h).1
  have h := Finset.sum_le_sum hlocal
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    count _ hB, count _ hL, Finset.sum_add_distrib,
    count Z (Finset.filter_subset _ _)] at h
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at h
  have hRc : R.card ≤ C.size := by
    change R.card ≤ C.gates.length
    exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
  omega

noncomputable def mergePool {n : ℕ} (C : Circuit) (G : SimpleGraph (Fin n))
    (c : Fin n) (m : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range m).filter fun k => k ∈ merges n C ∧
    ∀ v ∈ singletonSupport n C (n + k), G.Adj c v

lemma mem_mergePool {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} {c : Fin n}
    {m k : ℕ} : k ∈ mergePool C G c m ↔ k < m ∧ k ∈ merges n C ∧
      ∀ v ∈ singletonSupport n C (n + k), G.Adj c v := by
  classical
  simp [mergePool]

-- Expand the largest root with wide singleton support into its positive inputs.
-- A two-input expansion can add one root and is charged to that OR gate.
lemma leaf_budget {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} {c : Fin n}
    (hm : Monotone2 C) (rb : ReadsBack n C)
    (hclean : ∀ k, reachable n C k → (gateAt C k).op = GateOp.and →
      singletonSupport n C (n + k) = ∅)
    (m : ℕ) (roots : Finset ℕ)
    (hvalid : ∀ w ∈ roots, w < n ∨ reachable n C (w - n))
    (hadj : ∀ w ∈ roots, ∀ v ∈ singletonSupport n C w, G.Adj c v)
    (hbound : ∀ w ∈ roots, 1 < (singletonSupport n C w).card → w < n + m) :
    (roots.biUnion (singletonSupport n C)).card ≤ roots.card + (mergePool C G c m).card := by
  classical
  induction m generalizing roots with
  | zero =>
    have hsmall : ∀ w ∈ roots, (singletonSupport n C w).card ≤ 1 := by
      intro w hw
      by_contra! hb
      have hw' := hbound w hw hb
      have hs := support_input (C := C) (⟨w, by omega⟩ : Fin n)
      simp [hs] at hb
    calc
      _ ≤ ∑ w ∈ roots, (singletonSupport n C w).card := Finset.card_biUnion_le
      _ ≤ ∑ _w ∈ roots, 1 := Finset.sum_le_sum hsmall
      _ = _ := by simp [mergePool]
  | succ m ih =>
    have hpool : mergePool C G c m ⊆ mergePool C G c (m + 1) := by
      intro k hk
      obtain ⟨hk, hh⟩ := mem_mergePool.1 hk
      exact mem_mergePool.2 ⟨by omega, hh⟩
    by_cases htop : n + m ∈ roots ∧ 1 < (singletonSupport n C (n + m)).card
    · obtain ⟨hmem, hlarge⟩ := htop
      have hr : reachable n C m := by
        rcases hvalid _ hmem with h | h
        · omega
        · simpa using h
      have hor : (gateAt C m).op = GateOp.or := (gate_op hm hr.1).resolve_left fun h => by
        simp [hclean m hr h] at hlarge
      let P := positiveInputs n C m
      let T := roots.erase (n + m) ∪ P
      have hback : ∀ w ∈ P, w < n + m :=
        fun w hw => rb m hr.1 w (mem_positiveInputs.1 hw).1
      have hup : ∀ w ∈ P, singletonSupport n C w ⊆ singletonSupport n C (n + m) := by
        intro w hw u hu
        exact (support_or rb hr.1 hor u).2 ⟨w, (mem_positiveInputs.1 hw).1, hu⟩
      have hTvalid : ∀ w ∈ T, w < n ∨ reachable n C (w - n) := by
        intro w hw
        rcases Finset.mem_union.1 hw with hw | hw
        · exact hvalid _ (Finset.mem_of_mem_erase hw)
        · by_cases hn : w < n
          · exact Or.inl hn
          · exact Or.inr (reachable_child rb hr (by
              rw [show n + (w - n) = w by omega]
              exact (mem_positiveInputs.1 hw).1))
      have hTadj : ∀ w ∈ T, ∀ v ∈ singletonSupport n C w, G.Adj c v := by
        intro w hw v hv
        rcases Finset.mem_union.1 hw with hw | hw
        · exact hadj _ (Finset.mem_of_mem_erase hw) v hv
        · exact hadj _ hmem v (hup _ hw hv)
      have hTbound : ∀ w ∈ T, 1 < (singletonSupport n C w).card → w < n + m := by
        intro w hw hcard
        rcases Finset.mem_union.1 hw with hw | hw
        · have hlt := hbound w (Finset.mem_of_mem_erase hw) hcard
          have hne := (Finset.mem_erase.1 hw).1
          omega
        · exact hback w hw
      have hsub : roots.biUnion (singletonSupport n C) ⊆ T.biUnion (singletonSupport n C) := by
        intro u hu
        obtain ⟨w, hw, huw⟩ := Finset.mem_biUnion.1 hu
        by_cases he : w = n + m
        · subst w
          obtain ⟨a, ha, hua⟩ := (support_or rb hr.1 hor u).1 huw
          exact Finset.mem_biUnion.2 ⟨a, Finset.mem_union_right _
            (mem_positiveInputs.2 ⟨ha, u, hua⟩), hua⟩
        · exact Finset.mem_biUnion.2 ⟨w, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨he, hw⟩), huw⟩
      have hfirst := (Finset.card_le_card hsub).trans (ih T hTvalid hTadj hTbound)
      have hTcard := Finset.card_union_le (roots.erase (n + m)) P
      have herase := Finset.card_erase_add_one hmem
      have hPc : P.card ≤ 2 := (Finset.card_filter_le _ _).trans (input_card hm hr.1)
      by_cases hp : 1 < P.card
      · have hnew : m ∈ mergePool C G c (m + 1) := mem_mergePool.2
          ⟨by omega, mem_merges.2 ⟨hr, hor, hlarge, hp⟩, hadj _ hmem⟩
        have hn : m ∉ mergePool C G c m := fun h => (Nat.lt_irrefl m) (mem_mergePool.1 h).1
        have hsubpool : insert m (mergePool C G c m) ⊆ mergePool C G c (m + 1) :=
          Finset.insert_subset_iff.2 ⟨hnew, hpool⟩
        have hinc := Finset.card_le_card hsubpool
        rw [Finset.card_insert_of_notMem hn] at hinc
        change T.card ≤ (roots.erase (n + m)).card + P.card at hTcard
        omega
      · have hinc := Finset.card_le_card hpool
        change T.card ≤ (roots.erase (n + m)).card + P.card at hTcard
        omega
    · have hnew : ∀ w ∈ roots, 1 < (singletonSupport n C w).card → w < n + m := by
        intro w hw hw'
        have hlt := hbound w hw hw'
        have hne : w ≠ n + m := fun he => htop ⟨he ▸ hw, he ▸ hw'⟩
        omega
      have hfirst := ih roots hvalid hadj hnew
      have hinc := Finset.card_le_card hpool
      omega

lemma pair_mono {n : ℕ} {C : Circuit} (hm : Monotone2 C)
    {x y : Fin n → Bool} (hxy : ∀ u, x u = true → y u = true) :
    ∀ w, val C (List.ofFn x) w = true → val C (List.ofFn y) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hinput : w < n
    · let u : Fin n := ⟨w, hinput⟩
      change val C (List.ofFn x) u.val = true at hw
      change val C (List.ofFn y) u.val = true
      rw [val_ofFn] at *
      exact hxy u hw
    · have hwlt : w < n + C.gates.length := by
        by_contra! h
        rw [val_ge (by simp : (List.ofFn x).length = n) h] at hw
        cases hw
      obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      rcases gate_op hm hk with hop | hop
      · apply (val_and (by simp) hk hop).2
        intro i hi
        obtain ⟨hlt, ht⟩ := (val_and (by simp) hk hop).1 hw i hi
        exact ⟨hlt, ih i hlt ht⟩
      · obtain ⟨i, hi, hlt, ht⟩ := (val_or (by simp) hk hop).1 hw
        exact (val_or (by simp) hk hop).2 ⟨i, hi, hlt, ih i hlt ht⟩

lemma crossing {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)}
    (hm : Monotone2 C) (rb : ReadsBack n C)
    (hsafe : ∀ k, reachable n C k → (gateAt C k).op = GateOp.and →
      ∀ u v, gateVal n C k (pairInput u v) = true → G.Adj u v)
    {k a b : ℕ} (hk : reachable n C k) (hop : (gateAt C k).op = GateOp.and)
    (hab : (gateAt C k).inputs = [a,b]) :
    ∀ u ∈ singletonSupport n C a, ∀ v ∈ singletonSupport n C b, G.Adj u v := by
  intro u hu v hv
  apply hsafe k hk hop u v
  rw [gateVal_eq_val]
  apply (val_and (by simp) hk.1 hop).2
  intro w hw
  refine ⟨rb k hk.1 w hw, ?_⟩
  have hw' : w = a ∨ w = b := by simpa [hab] using hw
  rcases hw' with rfl | rfl
  · exact pair_mono hm (by intro i; simp [pairInput]; exact Or.inl) _ (mem_support.1 hu)
  · exact pair_mono hm (by intro i; simp [pairInput]; exact Or.inr) _ (mem_support.1 hv)

lemma birth_route {n : ℕ} {C : Circuit} (hm : Monotone2 C) (rb : ReadsBack n C)
    (hclean : ∀ k, reachable n C k → (gateAt C k).op = GateOp.and →
      singletonSupport n C (n + k) = ∅)
    (hempty : ∀ k, reachable n C k → (gateAt C k).op = GateOp.and →
      gateVal n C k (fun _ => false) = false)
    (u v : Fin n) :
    ∀ w, (w < n ∨ reachable n C (w - n)) → val C (List.ofFn (pairInput u v)) w = true →
      (∃ k ∈ births n C, ∀ a ∈ (gateAt C k).inputs,
        u ∈ singletonSupport n C a ∨ v ∈ singletonSupport n C a) ∨
      u ∈ singletonSupport n C w ∨ v ∈ singletonSupport n C w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw ht
    by_cases hi : w < n
    · let t : Fin n := ⟨w, hi⟩
      change val C (List.ofFn (pairInput u v)) t.val = true at ht
      change _ ∨ u ∈ singletonSupport n C t.val ∨ v ∈ singletonSupport n C t.val
      rw [val_ofFn] at ht
      rw [support_input]
      have he : t = u ∨ t = v := of_decide_eq_true ht
      exact Or.inr (he.imp (fun h => Finset.mem_singleton.2 h.symm) (fun h => Finset.mem_singleton.2 h.symm))
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : reachable n C k := by simpa using hw.resolve_left hi
      have sub (a) (ha : a ∈ (gateAt C k).inputs)
          (ht' : val C (List.ofFn (pairInput u v)) a = true) := by
        apply ih a (rb k hk.1 a ha) _ ht'
        by_cases hn : a < n
        · exact Or.inl hn
        · exact Or.inr (reachable_child rb hk (by rwa [show n + (a - n) = a by omega]))
      rcases gate_op hm hk.1 with hop | hop
      · by_cases hborn : ∃ k ∈ births n C, ∀ a ∈ (gateAt C k).inputs,
            u ∈ singletonSupport n C a ∨ v ∈ singletonSupport n C a
        · exact Or.inl hborn
        · have hone : ∀ a ∈ (gateAt C k).inputs,
              u ∈ singletonSupport n C a ∨ v ∈ singletonSupport n C a :=
            fun a ha => (sub a ha ((val_and (by simp) hk.1 hop).1 ht a ha).2).resolve_left hborn
          have hno (t : Fin n) : ¬ ∀ a ∈ (gateAt C k).inputs, t ∈ singletonSupport n C a := by
            intro h
            have hh := (val_and (by simp) hk.1 hop).2 (fun a ha => ⟨rb k hk.1 a ha,
              mem_support.1 (h a ha)⟩ : ∀ a ∈ (gateAt C k).inputs,
                a < n + k ∧ val C (List.ofFn (pairInput t t)) a = true)
            have hs := mem_support.2 hh
            simp [hclean k hk hop] at hs
          have hlen := (hm _ (gateAt_mem hk.1)).2
          generalize he : (gateAt C k).inputs = l at hlen
          cases l with
          | nil =>
            have hz := hempty k hk hop
            rw [gateVal_eq_val, (show val C (List.ofFn (fun _ : Fin n => false)) (n + k) = true from
              (val_and (by simp) hk.1 hop).2 (by simp [he]))] at hz
            cases hz
          | cons a as =>
            cases as with
            | nil =>
              rcases hone a (by simp [he]) with ha | ha
              · exact (hno u (by simpa [he] using ha)).elim
              · exact (hno v (by simpa [he] using ha)).elim
            | cons b bs =>
              have hb0 : bs = [] := List.length_eq_zero_iff.1 (by simp only [List.length_cons] at hlen; omega)
              subst bs
              have nonemp (a) (ha : a ∈ (gateAt C k).inputs) :
                  (singletonSupport n C a).Nonempty := by
                rcases hone a ha with hu | hv
                · exact ⟨u, hu⟩
                · exact ⟨v, hv⟩
              exact Or.inl ⟨k, mem_births.2 ⟨hk, hop, a, b, he,
                nonemp a (by simp [he]), nonemp b (by simp [he])⟩, hone⟩
      · obtain ⟨a, ha, _, ht'⟩ := (val_or (by simp) hk.1 hop).1 ht
        rcases sub a ha ht' with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl ((support_or rb hk.1 hop u).2 ⟨a, ha, h⟩))
        · exact Or.inr (Or.inr ((support_or rb hk.1 hop v).2 ⟨a, ha, h⟩))

lemma birth_star {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)}
    (hm : Monotone2 C) (rb : ReadsBack n C)
    (hsafe : ∀ k, reachable n C k → (gateAt C k).op = GateOp.and →
      ∀ u v, gateVal n C k (pairInput u v) = true → G.Adj u v)
    (hcommon : ∀ c d v w : Fin n, c ≠ d → v ≠ w →
      G.Adj c v → G.Adj c w → G.Adj d v → G.Adj d w → False)
    {k : ℕ} (hk : k ∈ births n C) :
    ∃ (c : Fin n) (w : ℕ), w ∈ (gateAt C k).inputs ∧
      (∀ v ∈ singletonSupport n C w, G.Adj c v) ∧
      ∀ u v : Fin n, (∀ a ∈ (gateAt C k).inputs,
        u ∈ singletonSupport n C a ∨ v ∈ singletonSupport n C a) →
        (u = c ∧ v ∈ singletonSupport n C w) ∨ (v = c ∧ u ∈ singletonSupport n C w) := by
  obtain ⟨hr, hop, a, b, hab, ha, hb⟩ := mem_births.1 hk
  have hex := crossing hm rb hsafe hr hop hab
  have hsmall : (singletonSupport n C a).card ≤ 1 ∨ (singletonSupport n C b).card ≤ 1 := by
    by_contra! h
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.1 h.1
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 h.2
    exact hcommon u v x y huv hxy (hex u hu x hx) (hex u hu y hy) (hex v hv x hx) (hex v hv y hy)
  have star (s w : ℕ) (hs : (singletonSupport n C s).Nonempty)
      (hcard : (singletonSupport n C s).card ≤ 1)
      (hsin : s ∈ (gateAt C k).inputs) (hwin : w ∈ (gateAt C k).inputs)
      (hcross : ∀ u ∈ singletonSupport n C s, ∀ v ∈ singletonSupport n C w, G.Adj u v) :
      ∃ (c : Fin n) (w : ℕ), w ∈ (gateAt C k).inputs ∧
        (∀ v ∈ singletonSupport n C w, G.Adj c v) ∧
        ∀ u v : Fin n, (∀ a ∈ (gateAt C k).inputs,
          u ∈ singletonSupport n C a ∨ v ∈ singletonSupport n C a) →
          (u = c ∧ v ∈ singletonSupport n C w) ∨ (v = c ∧ u ∈ singletonSupport n C w) := by
    obtain ⟨c, hc⟩ := hs
    have heq : ∀ t ∈ singletonSupport n C s, t = c :=
      fun t ht => Finset.card_le_one.1 hcard t ht c hc
    refine ⟨c, w, hwin, hcross c hc, ?_⟩
    intro u v h
    rcases h s hsin with hu | hv
    · left
      refine ⟨heq u hu, (h w hwin).resolve_left fun hw => ?_⟩
      exact G.irrefl (hcross u hu u hw)
    · right
      refine ⟨heq v hv, (h w hwin).resolve_right fun hw => ?_⟩
      exact G.irrefl (hcross v hv v hw)
  rcases hsmall with h | h
  · exact star a b ha h (by simp [hab]) (by simp [hab]) hex
  · exact star b a hb h (by simp [hab]) (by simp [hab]) (fun u hu v hv => (hex v hv u hu).symm)

def edgeKey {n : ℕ} (c v : Fin n) : Fin n × Fin n := (min c v, max c v)

lemma edgeKey_comm {n : ℕ} (c v : Fin n) : edgeKey c v = edgeKey v c := by
  simp only [edgeKey, min_comm c v, max_comm c v]

lemma graph_budget {n : ℕ} {C : Circuit} (G : SimpleGraph (Fin n)) (seed : Fin n)
    (hm : Monotone2 C) (rb : ReadsBack n C)
    (hsafe : ∀ k, reachable n C k → (gateAt C k).op = GateOp.and →
      ∀ u v, gateVal n C k (pairInput u v) = true → G.Adj u v)
    (hempty : ∀ k, reachable n C k → (gateAt C k).op = GateOp.and →
      gateVal n C k (fun _ => false) = false)
    (hcommon : ∀ c d v w : Fin n, c ≠ d → v ≠ w →
      G.Adj c v → G.Adj c w → G.Adj d v → G.Adj d w → False)
    (hout : singletonSupport n C C.output = ∅)
    (hpair : ∀ u v, G.Adj u v → C.eval (List.ofFn (pairInput u v)) = true)
    (E : Finset (Fin n × Fin n))
    (hE : ∀ p ∈ E, G.Adj p.1 p.2 ∧ p.1 ≤ p.2) :
    ∃ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
      T.card ≤ (births n C).card ∧ E.card + (births n C).card ≤ C.size + 1 := by
  classical
  have hclean (k) (hk : reachable n C k) (hop : (gateAt C k).op = GateOp.and) :
      singletonSupport n C (n + k) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.2
    intro u hu
    exact G.irrefl (hsafe k hk hop u u (mem_support.1 hu))
  let B := births n C
  let star (k : ℕ) (hk : k ∈ B) := birth_star hm rb hsafe hcommon hk
  let c (k : ℕ) := if hk : k ∈ B then (star k hk).choose else seed
  let w (k : ℕ) := if hk : k ∈ B then (star k hk).choose_spec.choose else 0
  have choose_spec (k) (hk : k ∈ B) :
    w k ∈ (gateAt C k).inputs ∧
      (∀ v ∈ singletonSupport n C (w k), G.Adj (c k) v) ∧
      ∀ u v : Fin n, (∀ a ∈ (gateAt C k).inputs,
        u ∈ singletonSupport n C a ∨ v ∈ singletonSupport n C a) →
        (u = c k ∧ v ∈ singletonSupport n C (w k)) ∨ (v = c k ∧ u ∈ singletonSupport n C (w k)) := by
    simpa only [c, w, dite_eq_left hk] using (star k hk).choose_spec.choose_spec
  have cover (u v) (huv : G.Adj u v) :
      ∃ k ∈ B, (u = c k ∧ v ∈ singletonSupport n C (w k)) ∨
        (v = c k ∧ u ∈ singletonSupport n C (w k)) := by
    have hv := hpair u v huv
    rw [eval_eq_val] at hv
    have hl : C.output < n + C.gates.length := by
      by_contra! hh
      rw [val_ge (by simp : (List.ofFn (pairInput u v)).length = n) hh] at hv
      cases hv
    have hn : n ≤ C.output := by
      by_contra! hh
      have he := support_input (C := C) (⟨C.output, hh⟩ : Fin n)
      rw [hout] at he
      exact (Finset.singleton_nonempty _).ne_empty he.symm
    have hr : reachable n C (C.output - n) := ⟨by omega, Or.inl (by omega)⟩
    rcases birth_route hm rb hclean hempty u v C.output (Or.inr hr) hv with h | h
    · obtain ⟨k, hk, ha⟩ := h
      exact ⟨k, hk, (choose_spec k hk).2.2 u v ha⟩
    · simp [hout] at h
  let T := B.image c
  let fiber (u : Fin n) := B.filter fun k => c k = u
  let roots (u : Fin n) := (fiber u).image w
  let leaves (u : Fin n) := (roots u).biUnion (singletonSupport n C)
  have hcov : ∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T := by
    intro u v huv
    obtain ⟨k, hk, ⟨rfl, _⟩ | ⟨rfl, _⟩⟩ := cover u v huv
    · exact Or.inl (Finset.mem_image_of_mem c hk)
    · exact Or.inr (Finset.mem_image_of_mem c hk)
  have hEsub : E ⊆ T.biUnion (fun t => (leaves t).image (edgeKey t)) := by
    rintro ⟨u, v⟩ hp
    obtain ⟨huv, huv'⟩ := hE _ hp
    obtain ⟨k, hk, h⟩ := cover u v huv
    have hroot : w k ∈ roots (c k) := Finset.mem_image_of_mem w (Finset.mem_filter.2 ⟨hk, rfl⟩)
    refine Finset.mem_biUnion.2 ⟨c k, Finset.mem_image_of_mem c hk, ?_⟩
    have hkey : edgeKey u v = (u, v) := by simp [edgeKey, min_eq_left huv', max_eq_right huv']
    rcases h with ⟨he, h⟩ | ⟨he, h⟩
    · exact Finset.mem_image.2 ⟨v, Finset.mem_biUnion.2 ⟨w k, hroot, h⟩, by rwa [← he]⟩
    · exact Finset.mem_image.2 ⟨u, Finset.mem_biUnion.2 ⟨w k, hroot, h⟩, by rwa [← he, edgeKey_comm]⟩
  have hleaf (t : Fin n) : (leaves t).card ≤ (fiber t).card +
      (mergePool C G t C.gates.length).card := by
    have hr (a) (ha : a ∈ roots t) : ∃ k ∈ B, c k = t ∧ w k = a := by
      obtain ⟨k, hk, he⟩ := Finset.mem_image.1 ha
      exact ⟨k, (Finset.mem_filter.1 hk).1, (Finset.mem_filter.1 hk).2, he⟩
    have h := leaf_budget (G := G) (c := t) hm rb hclean C.gates.length (roots t) (by
      intro a ha
      obtain ⟨k, hk, _, rfl⟩ := hr a ha
      by_cases hn : w k < n
      · exact Or.inl hn
      · apply Or.inr
        exact reachable_child rb (mem_births.1 hk).1 (by
          rw [show n + (w k - n) = w k by omega]
          exact (choose_spec k hk).1)) (by
      intro a ha v hv
      obtain ⟨k, hk, rfl, rfl⟩ := hr a ha
      exact (choose_spec k hk).2.1 v hv) (by
      intro a ha _
      obtain ⟨k, hk, _, rfl⟩ := hr a ha
      have hk' := (mem_births.1 hk).1.1
      have := rb k hk' (w k) (choose_spec k hk).1
      omega)
    exact h.trans (Nat.add_le_add_right Finset.card_image_le _)
  have hdisjFib : (T : Set (Fin n)).PairwiseDisjoint fiber := by
    intro a _ b _ hab
    rw [Function.onFun, Finset.disjoint_left]
    intro k hka hkb
    exact hab ((Finset.mem_filter.1 hka).2.symm.trans (Finset.mem_filter.1 hkb).2)
  have hsumB : (∑ t ∈ T, (fiber t).card) = B.card := by
    rw [← Finset.card_biUnion hdisjFib]
    congr 1
    ext k
    constructor
    · intro hk
      obtain ⟨_, _, hf⟩ := Finset.mem_biUnion.1 hk
      exact (Finset.mem_filter.1 hf).1
    · intro hk
      exact Finset.mem_biUnion.2 ⟨c k, Finset.mem_image_of_mem c hk, Finset.mem_filter.2 ⟨hk, rfl⟩⟩
  have hdisjPool : (T : Set (Fin n)).PairwiseDisjoint (fun t => mergePool C G t C.gates.length) := by
    intro a _ b _ hab
    rw [Function.onFun, Finset.disjoint_left]
    intro k hka hkb
    obtain ⟨_, hk, ha⟩ := mem_mergePool.1 hka
    have hb := (mem_mergePool.1 hkb).2.2
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.1 (mem_merges.1 hk).2.2.1
    exact hcommon a b u v hab huv (ha u hu) (ha v hv) (hb u hu) (hb v hv)
  have hsumL : (∑ t ∈ T, (mergePool C G t C.gates.length).card) ≤ (merges n C).card := by
    rw [← Finset.card_biUnion hdisjPool]
    apply Finset.card_le_card
    intro k hk
    obtain ⟨t, _, ht⟩ := Finset.mem_biUnion.1 hk
    exact (mem_mergePool.1 ht).2.1
  have hEL : E.card ≤ B.card + (merges n C).card := by
    calc
      _ ≤ (T.biUnion fun t => (leaves t).image (edgeKey t)).card := Finset.card_le_card hEsub
      _ ≤ ∑ t ∈ T, ((leaves t).image (edgeKey t)).card := Finset.card_biUnion_le
      _ ≤ ∑ t ∈ T, (leaves t).card := Finset.sum_le_sum fun _ _ => Finset.card_image_le
      _ ≤ ∑ t ∈ T, ((fiber t).card + (mergePool C G t C.gates.length).card) :=
        Finset.sum_le_sum fun t _ => hleaf t
      _ ≤ _ := by rw [Finset.sum_add_distrib, hsumB]; exact Nat.add_le_add_left hsumL _
  have hgate := gate_budget hm rb hclean
  change 2 * B.card + (merges n C).card ≤ C.size + 1 at hgate
  exact ⟨T, hcov, Finset.card_image_le, by change E.card + B.card ≤ C.size + 1; omega⟩

private lemma no_four_cycle {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hNoC4 : NoFourCycle G) {a b w1 w2 : Fin n} (hab : a ≠ b) (hw : w1 ≠ w2)
    (haw1 : G.Adj a w1) (haw2 : G.Adj a w2) (hbw1 : G.Adj b w1) (hbw2 : G.Adj b w2) : False := by
  have hle : (Finset.univ.filter fun w => G.Adj a w ∧ G.Adj b w).card ≤ 1 := hNoC4 a b hab
  have h1 : w1 ∈ Finset.univ.filter fun w => G.Adj a w ∧ G.Adj b w := by
    simp [haw1, hbw1]
  have h2 : w2 ∈ Finset.univ.filter fun w => G.Adj a w ∧ G.Adj b w := by
    simp [haw2, hbw2]
  have hgt : 1 < (Finset.univ.filter fun w => G.Adj a w ∧ G.Adj b w).card :=
    Finset.one_lt_card.mpr ⟨w1, h1, w2, h2, hw⟩
  omega

private def edgeTrue {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : Prop :=
  ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true

private lemma graph_true {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {x : Fin n → Bool} : graphFun G ∅ x = true ↔ edgeTrue G x := by
  simp [graphFun, edgeTrue]

private lemma edge_true_pair {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n} :
    edgeTrue G (pairInput u v) ↔ G.Adj u v := by
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    simp only [pairInput, decide_eq_true_eq] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, by simp [pairInput], by simp [pairInput]⟩

def cross {m n : ℕ} (E : Finset (Fin m × Fin n)) : (Fin m ⊕ Fin n) → (Fin m ⊕ Fin n) → Prop
  | .inl p, .inr q => (p,q) ∈ E
  | .inr q, .inl p => (p,q) ∈ E
  | _, _ => False

def graph {m n : ℕ} (E : Finset (Fin m × Fin n)) : SimpleGraph (Fin (m+n)) where
  Adj u v := cross E (finSumFinEquiv.symm u) (finSumFinEquiv.symm v)
  symm := ⟨by
    intro u v
    cases finSumFinEquiv.symm u <;> cases finSumFinEquiv.symm v <;> simp [cross]⟩
  loopless := ⟨by
    intro u
    cases finSumFinEquiv.symm u <;> simp [cross]⟩

lemma noRectangle {m n : ℕ} (E : Finset (Fin m × Fin n))
    (hf : ∀ a b c d, a ≠ b → c ≠ d → ¬ ((a,c) ∈ E ∧ (a,d) ∈ E ∧ (b,c) ∈ E ∧ (b,d) ∈ E)) :
    @PEqualNP.TopForm.NoFourCycle _ (graph E) (Classical.decRel _) := by
  classical
  intro a b hab
  apply Finset.card_le_one.mpr
  intro u hu v hv
  obtain ⟨hau,hbu⟩ := (Finset.mem_filter.mp hu).2
  obtain ⟨hav,hbv⟩ := (Finset.mem_filter.mp hv).2
  by_contra huv
  cases a using Fin.addCases <;> cases b using Fin.addCases <;>
    cases u using Fin.addCases <;> cases v using Fin.addCases <;>
    simp [graph,cross] at hau hbu hav hbv hab huv
  all_goals apply hf _ _ _ _ (by assumption) (by assumption) <;> exact ⟨by assumption,by assumption,by assumption,by assumption⟩


lemma clean_bound (p l : ℕ) (E : Finset (Fin p × Fin l)) (C : Circuit)
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (hao : IsAO2 (p + l) C)
    (hcomp : ∀ x : Fin (p + l) → Bool, circuitFun (p + l) C x =
      decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧
        x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true))
    (hclean : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ x : Fin (p + l) → Bool, gateVal (p + l) C j x = true →
        circuitFun (p + l) C x = true) :
    ∃ S : Finset (Fin (p + l)),
      (∀ (a : Fin p) (b : Fin l), (a, b) ∈ E →
        Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      E.card + S.card ≤ C.size + 1 := by
  classical
  by_cases he : E = ∅
  · subst E
    exact ⟨∅, by simp, by simp⟩
  obtain ⟨⟨a, b⟩, hab⟩ := Finset.nonempty_iff_ne_empty.mpr he
  let G := graph E
  letI : DecidableRel G.Adj := Classical.decRel _
  have hrel (x : Fin (p + l) → Bool) :
      (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧
        x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true) ↔ edgeTrue G x := by
    constructor
    · rintro ⟨a, b, he, ha, hb⟩
      exact ⟨Fin.castAdd l a, Fin.natAdd p b, by simpa [G, graph, cross] using he, ha, hb⟩
    · rintro ⟨u, v, huv, hu, hv⟩
      cases u using Fin.addCases <;> cases v using Fin.addCases <;>
        simp [G, graph, cross] at huv
      · exact ⟨_, _, huv, hu, hv⟩
      · exact ⟨_, _, huv, hv, hu⟩
  have hsound (x : Fin (p + l) → Bool) (hx : circuitFun (p + l) C x = true) :
      edgeTrue G x := by
    rw [hcomp, decide_eq_true_eq] at hx
    exact (hrel x).1 hx
  have hm : Monotone2 C := by
    intro g hg
    exact ⟨by simpa using hao.1 g hg, (hao.2.2 g hg).le⟩
  have hsafe : ∀ j, reachable (p + l) C j → (gateAt C j).op = GateOp.and →
      ∀ u v, gateVal (p + l) C j (pairInput u v) = true → G.Adj u v := by
    intro j hj hop u v hv
    exact edge_true_pair.1 (hsound _ (hclean j hj.1 hop _ hv))
  have hempty : ∀ j, reachable (p + l) C j → (gateAt C j).op = GateOp.and →
      gateVal (p + l) C j (fun _ => false) = false := by
    intro j hj hop
    cases hv : gateVal (p + l) C j (fun _ => false)
    · rfl
    · obtain ⟨u, v, _, hu, _⟩ := hsound _ (hclean j hj.1 hop _ hv)
      cases hu
  have hout : singletonSupport (p + l) C C.output = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.2
    intro u hu
    have hv : circuitFun (p + l) C (pairInput u u) = true := mem_support.1 hu
    exact G.irrefl (edge_true_pair.1 (hsound _ hv))
  have hpair : ∀ u v, G.Adj u v → C.eval (List.ofFn (pairInput u v)) = true := by
    intro u v huv
    change circuitFun (p + l) C (pairInput u v) = true
    rw [hcomp, decide_eq_true_eq]
    exact (hrel _).2 (edge_true_pair.2 huv)
  let embed : Fin p × Fin l → Fin (p + l) × Fin (p + l) :=
    fun e => (Fin.castAdd l e.1, Fin.natAdd p e.2)
  have hinj : Function.Injective embed := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ he
    have h₁ := congrArg Prod.fst he
    have h₂ := congrArg Prod.snd he
    exact Prod.ext (by simpa [embed] using h₁) (by simpa [embed] using h₂)
  have hE : ∀ e ∈ E.image embed, G.Adj e.1 e.2 ∧ e.1 ≤ e.2 := by
    intro e he
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.1 he
    constructor
    · simpa [embed, G, graph, cross] using hab
    · change (Fin.castAdd l a : Fin (p + l)) ≤ Fin.natAdd p b
      change a.val ≤ p + b.val
      omega
  obtain ⟨S, hcover, hS, hbudget⟩ := graph_budget G (Fin.castAdd l a) hm hao.2.1
    hsafe hempty (fun _ _ _ _ => no_four_cycle (noRectangle E hfour))
    hout hpair (E.image embed) hE
  refine ⟨S, ?_, ?_⟩
  · intro a b hab
    exact hcover _ _ (by simpa [G, graph, cross] using hab)
  · rw [Finset.card_image_of_injective _ hinj] at hbudget
    omega

end PEqualNP.Outside.L_meta_4675.Reuse

namespace PEqualNP.Outside.L_meta_4675_aux

lemma rectangle_subsingleton {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (A : Finset (Fin p)) (B : Finset (Fin l))
    (hrect : ∀ a ∈ A, ∀ b ∈ B, (a, b) ∈ E) :
    (∀ a ∈ A, ∀ a' ∈ A, a = a') ∨ (∀ b ∈ B, ∀ b' ∈ B, b = b') := by
  classical
  by_cases hA : ∀ a ∈ A, ∀ a' ∈ A, a = a'
  · exact Or.inl hA
  · right
    push_neg at hA
    obtain ⟨a, ha, a', ha', haa'⟩ := hA
    intro b hb b' hb'
    by_contra hbb'
    exact hfour a a' b b' haa' hbb'
      ⟨hrect a ha b hb, hrect a ha b' hb',
       hrect a' ha' b hb, hrect a' ha' b' hb'⟩

lemma rectangle_card_le_one {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (A : Finset (Fin p)) (B : Finset (Fin l))
    (hrect : ∀ a ∈ A, ∀ b ∈ B, (a, b) ∈ E) :
    A.card ≤ 1 ∨ B.card ≤ 1 := by
  rcases rectangle_subsingleton E hfour A B hrect with hA | hB
  · exact Or.inl (Finset.card_le_one.mpr hA)
  · exact Or.inr (Finset.card_le_one.mpr hB)

lemma rectangle_singleton {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (A : Finset (Fin p)) (B : Finset (Fin l))
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hrect : ∀ a ∈ A, ∀ b ∈ B, (a, b) ∈ E) :
    (∃ a, A = {a}) ∨ (∃ b, B = {b}) := by
  rcases rectangle_card_le_one E hfour A B hrect with ha | hb
  · left
    exact Finset.card_eq_one.mp (by have := hA.card_pos; omega)
  · right
    exact Finset.card_eq_one.mp (by have := hB.card_pos; omega)

lemma rectangle_cost {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (A : Finset (Fin p)) (B : Finset (Fin l))
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hrect : ∀ a ∈ A, ∀ b ∈ B, (a, b) ∈ E) :
    (A ×ˢ B).card = A.card + B.card - 1 := by
  rcases rectangle_singleton E hfour A B hA hB hrect with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · simp
  · simp

lemma rectangle_has_centre {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (A : Finset (Fin p)) (B : Finset (Fin l))
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hrect : ∀ a ∈ A, ∀ b ∈ B, (a, b) ∈ E) :
    ∃ c : Fin (p + l), ∀ a ∈ A, ∀ b ∈ B,
      Fin.castAdd l a = c ∨ Fin.natAdd p b = c := by
  rcases rectangle_singleton E hfour A B hA hB hrect with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · refine ⟨Fin.castAdd l a, ?_⟩
    intro a' ha' b hb
    have : a' = a := Finset.mem_singleton.mp ha'
    exact Or.inl (congrArg (Fin.castAdd l) this)
  · refine ⟨Fin.natAdd p b, ?_⟩
    intro a ha b' hb'
    have : b' = b := Finset.mem_singleton.mp hb'
    exact Or.inr (congrArg (Fin.natAdd p) this)


lemma rectangle_family_cover {p l : ℕ} {ι : Type*} [DecidableEq ι]
    (E : Finset (Fin p × Fin l))
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (I : Finset ι) (A : ι → Finset (Fin p)) (B : ι → Finset (Fin l))
    (hA : ∀ i ∈ I, (A i).Nonempty) (hB : ∀ i ∈ I, (B i).Nonempty)
    (hrect : ∀ i ∈ I, ∀ a ∈ A i, ∀ b ∈ B i, (a, b) ∈ E) :
    ∃ S : Finset (Fin (p + l)),
      (∀ i ∈ I, ∀ a ∈ A i, ∀ b ∈ B i,
        Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      (I.biUnion fun i => A i ×ˢ B i).card + S.card ≤
        ∑ i ∈ I, ((A i).card + (B i).card) := by
  classical
  revert hA hB hrect
  induction I using Finset.induction_on with
  | empty =>
    intro hA hB hrect
    exact ⟨∅, by simp, by simp⟩
  | @insert i I hi ih =>
    intro hA hB hrect
    obtain ⟨S, hScover, hScost⟩ := ih
      (fun j hj => hA j (Finset.mem_insert_of_mem hj))
      (fun j hj => hB j (Finset.mem_insert_of_mem hj))
      (fun j hj => hrect j (Finset.mem_insert_of_mem hj))
    have hai := hA i (Finset.mem_insert_self i I)
    have hbi := hB i (Finset.mem_insert_self i I)
    have hri := hrect i (Finset.mem_insert_self i I)
    obtain ⟨c, hc⟩ := rectangle_has_centre E hfour (A i) (B i) hai hbi hri
    refine ⟨insert c S, ?_, ?_⟩
    · intro j hj a ha b hb
      rcases Finset.mem_insert.mp hj with rfl | hj
      · rcases hc a ha b hb with h | h
        · exact Or.inl (Finset.mem_insert.mpr (Or.inl h))
        · exact Or.inr (Finset.mem_insert.mpr (Or.inl h))
      · rcases hScover j hj a ha b hb with h | h
        · exact Or.inl (Finset.mem_insert_of_mem h)
        · exact Or.inr (Finset.mem_insert_of_mem h)
    · have hR : ((insert i I).biUnion fun j => A j ×ˢ B j).card ≤
          (A i ×ˢ B i).card + (I.biUnion fun j => A j ×ˢ B j).card := by
        rw [Finset.biUnion_insert]
        exact Finset.card_union_le _ _
      have hS : (insert c S).card ≤ S.card + 1 := Finset.card_insert_le _ _
      have hcost : (A i ×ˢ B i).card + 1 = (A i).card + (B i).card := by
        rw [rectangle_cost E hfour (A i) (B i) hai hbi hri]
        have ha := hai.card_pos
        omega
      rw [Finset.sum_insert hi]
      omega

lemma rectangle_cover_bound {p l : ℕ} {ι : Type*} [DecidableEq ι]
    (E : Finset (Fin p × Fin l))
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (I : Finset ι) (A : ι → Finset (Fin p)) (B : ι → Finset (Fin l))
    (hA : ∀ i ∈ I, (A i).Nonempty) (hB : ∀ i ∈ I, (B i).Nonempty)
    (hrect : ∀ i ∈ I, ∀ a ∈ A i, ∀ b ∈ B i, (a, b) ∈ E)
    (hcover : ∀ a b, (a, b) ∈ E → ∃ i ∈ I, a ∈ A i ∧ b ∈ B i) :
    ∃ S : Finset (Fin (p + l)),
      (∀ a b, (a, b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      E.card + S.card ≤ ∑ i ∈ I, ((A i).card + (B i).card) := by
  classical
  obtain ⟨S, hScover, hScost⟩ := rectangle_family_cover E hfour I A B hA hB hrect
  refine ⟨S, ?_, ?_⟩
  · intro a b hab
    obtain ⟨i, hi, ha, hb⟩ := hcover a b hab
    exact hScover i hi a ha b hb
  · have hsub : E ⊆ I.biUnion (fun i => A i ×ˢ B i) := by
      intro e he
      obtain ⟨i, hi, ha, hb⟩ := hcover e.1 e.2 he
      exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_product.mpr ⟨ha, hb⟩⟩
    exact le_trans (Nat.add_le_add_right (Finset.card_le_card hsub) S.card) hScost

end PEqualNP.Outside.L_meta_4675_aux

namespace PEqualNP.Outside.L_meta_4675.Normalize

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadK

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl
lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega
lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key
def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false
lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl
lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]
lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj
lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)
lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega
lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj
lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [ite_eq_right hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩
lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
    · rw [ite_eq_right hlt] at h'; cases h'
  · intro h i hi
    rw [ite_eq_left (h i hi).1]; exact (h i hi).2
lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]
lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl
private def edgeTrue {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : Prop :=
  ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true

private lemma graph_true {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {x : Fin n → Bool} : graphFun G ∅ x = true ↔ edgeTrue G x := by
  simp [graphFun, edgeTrue]

private lemma edge_true_pair {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n} :
    edgeTrue G (pairInput u v) ↔ G.Adj u v := by
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    simp only [pairInput, decide_eq_true_eq] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, by simp [pairInput], by simp [pairInput]⟩

private def dirty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : ℕ) : Prop :=
  (gateAt C j).op = GateOp.and ∧ ¬ BelowF G C j

private noncomputable def repair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (pick : ℕ → Fin n × Fin n) : Circuit := by
  classical
  exact ⟨(List.range C.gates.length).map fun j =>
    if dirty G C j then ⟨GateOp.and, [(pick j).1.val, (pick j).2.val]⟩ else gateAt C j,
    C.output⟩

private lemma repair_len {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (pick : ℕ → Fin n × Fin n) :
    (repair G C pick).gates.length = C.gates.length := by
  simp [repair]

private lemma repair_gate {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (pick : ℕ → Fin n × Fin n) {j : ℕ} (hj : j < C.gates.length) :
    gateAt (repair G C pick) j =
      @ite Gate (dirty G C j) (Classical.propDecidable _)
        ⟨GateOp.and, [(pick j).1.val, (pick j).2.val]⟩ (gateAt C j) := by
  classical
  have hj' : j < (repair G C pick).gates.length := by rwa [repair_len]
  rw [gateAt_eq hj']
  simp [repair]

private lemma repair_ao {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hC : IsAO2 n C) (pick : ℕ → Fin n × Fin n) :
    IsAO2 n (repair G C pick) := by
  classical
  have hgate (j : ℕ) (hj : j < (repair G C pick).gates.length) :
      ((gateAt (repair G C pick) j).op = GateOp.and ∨
        (gateAt (repair G C pick) j).op = GateOp.or) ∧
      (gateAt (repair G C pick) j).inputs.length = 2 ∧
      ∀ w ∈ (gateAt (repair G C pick) j).inputs, w < n + j := by
    rw [repair_len] at hj
    rw [repair_gate pick hj]
    split_ifs
    · refine ⟨Or.inl rfl, rfl, ?_⟩
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · have := (pick j).1.isLt
        omega
      · have := (pick j).2.isLt
        omega
    · exact ⟨hC.1 _ (gateAt_mem hj), hC.2.2 _ (gateAt_mem hj), hC.2.1 j hj⟩
  refine ⟨?_, fun j hj => (hgate j hj).2.2, ?_⟩
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    rw [← gateAt_eq hj]
    exact (hgate j hj).1
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    rw [← gateAt_eq hj]
    exact (hgate j hj).2.1

private lemma repair_kept {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (pick : ℕ → Fin n × Fin n) {j : ℕ} (hj : j < C.gates.length)
    (h : ¬ dirty G C j) : gateAt (repair G C pick) j = gateAt C j := by
  classical
  rw [repair_gate pick hj, ite_eq_right h]

private lemma repair_replaced_val {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (pick : ℕ → Fin n × Fin n) {j : ℕ} (hj : j < C.gates.length)
    (hd : dirty G C j) (x : Fin n → Bool) :
    val (repair G C pick) (List.ofFn x) (n + j) = true ↔
      x (pick j).1 = true ∧ x (pick j).2 = true := by
  classical
  have hj' : j < (repair G C pick).gates.length := by rwa [repair_len]
  have hg := (repair_gate (G := G) pick hj).trans (ite_eq_left hd)
  rw [val_and (by simp) hj' (congrArg Gate.op hg), hg]
  have h₁ : (pick j).1.val < n + j := by have := (pick j).1.isLt; omega
  have h₂ : (pick j).2.val < n + j := by have := (pick j).2.isLt; omega
  simp [h₁, h₂, val_ofFn]

private lemma repair_compare {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hC : IsAO2 n C) (pick : ℕ → Fin n × Fin n)
    (x : Fin n → Bool) (forward : Bool)
    (hreplaced : ∀ j < C.gates.length, dirty G C j →
      if forward then
        val C (List.ofFn x) (n + j) = true → val (repair G C pick) (List.ofFn x) (n + j) = true
      else
        val (repair G C pick) (List.ofFn x) (n + j) = true → val C (List.ofFn x) (n + j) = true) :
    ∀ w : ℕ, if forward then
      val C (List.ofFn x) w = true → val (repair G C pick) (List.ofFn x) w = true
    else
      val (repair G C pick) (List.ofFn x) w = true → val C (List.ofFn x) w = true := by
  let D := repair G C pick
  let xs := List.ofFn x
  have hl : D.gates.length = C.gates.length := repair_len G C pick
  have hx : xs.length = n := List.length_ofFn
  have transfer (A B : Circuit) (heq : A.gates.length = C.gates.length)
      (heq' : B.gates.length = C.gates.length)
      (hkeep : ∀ j < C.gates.length, ¬ dirty G C j →
        gateAt A j = gateAt C j ∧ gateAt B j = gateAt C j)
      (hchange : ∀ j < C.gates.length, dirty G C j →
        val A xs (n + j) = true → val B xs (n + j) = true) :
      ∀ w, val A xs w = true → val B xs w = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro ht
      by_cases hi : w < n
      · rwa [val_input hx hi, ← val_input (C := A) hx hi]
      by_cases hj : w < n + C.gates.length
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hi)
        have hj' : j < C.gates.length := by omega
        by_cases hd : dirty G C j
        · exact hchange j hj' hd ht
        obtain ⟨ha, hb⟩ := hkeep j hj' hd
        have hjA : j < A.gates.length := by rwa [heq]
        have hjB : j < B.gates.length := by rwa [heq']
        rcases hC.1 _ (gateAt_mem hj') with op | op
        · rw [val_and hx hjA (by rwa [ha]), ha] at ht
          rw [val_and hx hjB (by rwa [hb]), hb]
          exact fun i hi => ⟨(ht i hi).1, ih i (ht i hi).1 (ht i hi).2⟩
        · rw [val_or hx hjA (by rwa [ha]), ha] at ht
          rw [val_or hx hjB (by rwa [hb]), hb]
          obtain ⟨i, hi, hlt, hv⟩ := ht
          exact ⟨i, hi, hlt, ih i hlt hv⟩
      · rw [val_ge hx (by omega)] at ht
        cases ht
  cases forward
  · exact transfer D C hl rfl (fun j hj hn => ⟨repair_kept pick hj hn, rfl⟩) hreplaced
  · exact transfer C D rfl hl (fun j hj hn => ⟨rfl, repair_kept pick hj hn⟩) hreplaced


lemma val_mono {n : ℕ} {C : Circuit} (hC : IsAO2 n C)
    {x y : Fin n → Bool} (hxy : ∀ i, x i = true → y i = true) :
    ∀ w, val C (List.ofFn x) w = true → val C (List.ofFn y) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hi : w < n
    · rw [val_input (by simp) hi] at hw ⊢
      have hx : (List.ofFn x).getD w false = x ⟨w, hi⟩ := by
        simp [List.getD_eq_getElem?_getD, hi]
      have hy : (List.ofFn y).getD w false = y ⟨w, hi⟩ := by
        simp [List.getD_eq_getElem?_getD, hi]
      rw [hx] at hw
      rw [hy]
      exact hxy _ hw
    by_cases hj : w < n + C.gates.length
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hi)
      have hj' : j < C.gates.length := by omega
      rcases hC.1 _ (gateAt_mem hj') with hop | hop
      · rw [val_and (by simp) hj' hop] at hw ⊢
        exact fun i hi => ⟨(hw i hi).1, ih i (hw i hi).1 (hw i hi).2⟩
      · rw [val_or (by simp) hj' hop] at hw ⊢
        obtain ⟨i, hi, hlt, hv⟩ := hw
        exact ⟨i, hi, hlt, ih i hlt hv⟩
    · rw [val_ge (n := n) (by simp) (by omega)] at hw
      cases hw

lemma erase_edge_inactive_dirty {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hC : IsAO2 n C)
    (hcomp : circuitFun n C = graphFun G ∅)
    (hne : ∃ a b, G.Adj a b)
    (hdead : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ¬ BelowF G C j → ∀ a b, G.Adj a b → gateVal n C j (pairInput a b) = false) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size = C.size ∧
      circuitFun n D = graphFun G ∅ ∧
      ∀ j < D.gates.length, (gateAt D j).op = GateOp.and → BelowF G D j := by
  classical
  obtain ⟨a, b, hab⟩ := hne
  let pick : ℕ → Fin n × Fin n := fun _ => (a, b)
  let D := repair G C pick
  have hD : IsAO2 n D := repair_ao hC pick
  have reflect (x : Fin n → Bool) (hn : graphFun G ∅ x ≠ true) (w : ℕ) :
      val D (List.ofFn x) w = true → val C (List.ofFn x) w = true :=
    repair_compare hC pick x false (by
      intro j hj hd hv
      have hp := (repair_replaced_val pick hj hd x).1 hv
      exact (hn (graph_true.2 ⟨a, b, hab, hp.1, hp.2⟩)).elim) w
  have clean : ∀ j < D.gates.length, (gateAt D j).op = GateOp.and → BelowF G D j := by
    intro j hj hop x hv
    have hj' : j < C.gates.length := by rwa [repair_len] at hj
    by_cases hd : dirty G C j
    · have hp := (repair_replaced_val pick hj' hd x).1 hv
      exact graph_true.2 ⟨a, b, hab, hp.1, hp.2⟩
    · have hop' : (gateAt C j).op = GateOp.and := by
        rwa [repair_kept pick hj' hd] at hop
      by_contra hn
      have hbelow : BelowF G C j := by
        by_contra h
        exact hd ⟨hop', h⟩
      exact hn (hbelow x (reflect x hn (n + j) hv))
  have keep_pair (u v : Fin n) (huv : G.Adj u v) :
      circuitFun n D (pairInput u v) = true := by
    have hc : circuitFun n C (pairInput u v) = true := by
      rw [hcomp]
      exact graph_true.2 (edge_true_pair.2 huv)
    exact repair_compare hC pick (pairInput u v) true (by
      intro j hj hd hv
      have hh := hdead j hj hd.1 hd.2 u v huv
      change gateVal n C j (pairInput u v) = true at hv
      rw [hh] at hv
      cases hv) C.output hc
  have eq : circuitFun n D = graphFun G ∅ := by
    funext x
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hx
      by_contra hn
      have h := reflect x hn C.output hx
      change circuitFun n C x = true at h
      rw [hcomp] at h
      exact hn h
    · intro hx
      obtain ⟨u, v, huv, hu, hv⟩ := graph_true.1 hx
      apply val_mono hD (x := pairInput u v) (y := x) ?_ C.output (keep_pair u v huv)
      intro i hi
      simp only [pairInput, decide_eq_true_eq] at hi
      rcases hi with rfl | rfl
      · exact hu
      · exact hv
  exact ⟨D, hD, repair_len G C pick, eq, clean⟩

end PEqualNP.Outside.L_meta_4675.Normalize

namespace PEqualNP.Outside.L_meta_4675.Fragment

lemma same_colour_disjoint_no_pair {α : Type*} [DecidableEq α]
    (A B : Finset α) (colour : α → Bool) (u v : α)
    (hdisj : Disjoint A B)
    (hmono : ∀ a ∈ A, ∀ b ∈ B, colour a = colour b)
    (hdiff : colour u ≠ colour v) :
    ¬ ((u ∈ A ∨ v ∈ A) ∧ (u ∈ B ∨ v ∈ B)) := by
  rintro ⟨hu | hv, hu' | hv'⟩
  · exact Finset.disjoint_left.1 hdisj hu hu'
  · exact hdiff (hmono u hu v hv')
  · exact hdiff (hmono v hv u hu').symm
  · exact Finset.disjoint_left.1 hdisj hv hv'

lemma same_colour_disjoint_fragment {α : Type*} [DecidableEq α]
    (A B : Finset α) (colour : α → Bool) (u v : α) (P Q : Prop)
    (hdisj : Disjoint A B)
    (hmono : ∀ a ∈ A, ∀ b ∈ B, colour a = colour b)
    (hdiff : colour u ≠ colour v) :
    ((u ∈ A ∨ v ∈ A) ∨ P) ∧ ((u ∈ B ∨ v ∈ B) ∨ Q) → P ∨ Q := by
  rintro ⟨ha | hp, hb | hq⟩
  · exact (same_colour_disjoint_no_pair A B colour u v hdisj hmono hdiff ⟨ha, hb⟩).elim
  · exact Or.inr hq
  · exact Or.inl hp
  · exact Or.inl hp

lemma safe_fragment_replacement (F X Y : Prop)
    (hX : X → F) (hY : Y → F) : X ∨ Y → F := by
  rintro (hx | hy)
  · exact hX hx
  · exact hY hy

end PEqualNP.Outside.L_meta_4675.Fragment

namespace PEqualNP.Outside.L_meta_4675_aux

def p4Circuit : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.and, [1, 3]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [5, 6]⟩], 7⟩

def p4Edges : Finset (Fin 2 × Fin 2) := {(0, 0), (0, 1), (1, 1)}

lemma p4_no_four_cycle :
    ∀ (a a' : Fin 2) (b b' : Fin 2), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ p4Edges ∧ (a, b') ∈ p4Edges ∧
         (a', b) ∈ p4Edges ∧ (a', b') ∈ p4Edges) := by
  decide

lemma p4_is_ao : PEqualNP.TopForm.IsAO2 4 p4Circuit := by
  decide

lemma p4_computes :
    ∀ x : Fin (2 + 2) → Bool,
      PEqualNP.MetaComplexity.circuitFun (2 + 2) p4Circuit x =
        decide (∃ (a : Fin 2) (b : Fin 2), (a, b) ∈ p4Edges ∧
          x (Fin.castAdd 2 a) = true ∧ x (Fin.natAdd 2 b) = true) := by
  decide

lemma p4_no_two_colour :
    PEqualNP.TwoColour.tCount 4 p4Circuit (fun i => decide (2 ≤ i)) = 0 := by
  decide

lemma p4_not_read_one : ¬ PEqualNP.ReadK.IsReadK 4 p4Circuit 1 := by
  decide

def p4BufferedCircuit : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.and, [0, 0]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [4, 5]⟩,
    ⟨.or, [2, 3]⟩, ⟨.and, [6, 7]⟩], 8⟩

lemma p4_buffered_is_ao : PEqualNP.TopForm.IsAO2 4 p4BufferedCircuit := by
  decide

lemma p4_buffered_computes :
    ∀ x : Fin (2 + 2) → Bool,
      PEqualNP.MetaComplexity.circuitFun (2 + 2) p4BufferedCircuit x =
        decide (∃ (a : Fin 2) (b : Fin 2), (a, b) ∈ p4Edges ∧
          x (Fin.castAdd 2 a) = true ∧ x (Fin.natAdd 2 b) = true) := by
  decide

lemma p4_buffered_no_two_colour :
    PEqualNP.TwoColour.tCount 4 p4BufferedCircuit (fun i => decide (2 ≤ i)) = 0 := by
  decide

lemma p4_buffered_dirty_at_zero :
    PEqualNP.EdgeOwnership.gateVal 4 p4BufferedCircuit 0
      (fun i => decide (i = 0)) = true ∧
    PEqualNP.MetaComplexity.circuitFun 4 p4BufferedCircuit
      (fun i => decide (i = 0)) = false := by
  decide

lemma p4_buffered_accepts_two_repeated_edges :
    PEqualNP.EdgeOwnership.gateVal 4 p4BufferedCircuit 0
      (PEqualNP.EdgeOwnership.pairInput 0 2) = true ∧
    PEqualNP.EdgeOwnership.gateVal 4 p4BufferedCircuit 0
      (PEqualNP.EdgeOwnership.pairInput 0 3) = true ∧
    PEqualNP.ReadK.readsAtMost p4BufferedCircuit 4 [0, 2] 1 = false ∧
    PEqualNP.ReadK.readsAtMost p4BufferedCircuit 4 [0, 3] 1 = false := by
  decide

end PEqualNP.Outside.L_meta_4675_aux

namespace PEqualNP.Outside.L_meta_4675.OrInvariant

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.TwoColour

def SameOr (g h : Gate) : Prop :=
  g.op = h.op ∧ (g.op = GateOp.or → g.inputs = h.inputs)

lemma sameOr_refl (g : Gate) : SameOr g g := ⟨rfl, fun _ => rfl⟩

lemma sameOr_symm {g h : Gate} (heq : SameOr g h) : SameOr h g := by
  refine ⟨heq.1.symm, ?_⟩
  intro hop
  exact (heq.2 (heq.1.trans hop)).symm

lemma step_eq (n : ℕ) (cs : List (List ℕ)) {g h : Gate} (heq : SameOr g h) :
    orStep n cs g = orStep n cs h := by
  by_cases hop : g.op = GateOp.or
  · have hop' : h.op = GateOp.or := heq.1.symm.trans hop
    simp only [orStep, hop, hop', ↓reduceIte, heq.2 hop]
  · have hop' : h.op ≠ GateOp.or := fun hh => hop (heq.1.trans hh)
    simp only [orStep, hop, hop', ↓reduceIte]

lemma fold_eq (n : ℕ) {gs hs : List Gate} (heq : List.Forall₂ SameOr gs hs)
    (cs : List (List ℕ)) : gs.foldl (orStep n) cs = hs.foldl (orStep n) cs := by
  induction heq generalizing cs with
  | nil => rfl
  | cons hhead htail ih =>
    simp only [List.foldl_cons]
    rw [step_eq n cs hhead]
    exact ih _

lemma getD_same {gs hs : List Gate} (heq : List.Forall₂ SameOr gs hs)
    (j : ℕ) : SameOr (gs.getD j ⟨GateOp.or, []⟩) (hs.getD j ⟨GateOp.or, []⟩) := by
  induction heq generalizing j with
  | nil => simpa using sameOr_refl ⟨GateOp.or, []⟩
  | cons hhead htail ih =>
    cases j with
    | zero => simpa using hhead
    | succ j => simpa using ih j

lemma orSets_eq (n : ℕ) {C D : Circuit} (heq : List.Forall₂ SameOr C.gates D.gates) :
    orSets n C = orSets n D := fold_eq n heq []

lemma reaches_iff (n : ℕ) {C D : Circuit} (heq : List.Forall₂ SameOr C.gates D.gates)
    (w j : ℕ) : OrReaches n C w j ↔ OrReaches n D w j := by
  simp only [OrReaches, orSets_eq n heq]

lemma orIn_subset (n : ℕ) {C D : Circuit} (heq : List.Forall₂ SameOr C.gates D.gates)
    (w : ℕ) : orIn n C w ⊆ orIn n D w := by
  intro i hi
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  rcases hi with hinput | ⟨j, hj, hreach, hop, hin⟩
  · exact Or.inl hinput
  · have hgate : SameOr (gateAt C j) (gateAt D j) := getD_same heq j
    refine Or.inr ⟨j, ?_, (reaches_iff n heq w j).1 hreach, hgate.1.symm.trans hop, ?_⟩
    · rwa [← heq.length_eq]
    · rwa [← hgate.2 hop]

lemma orIn_eq (n : ℕ) {C D : Circuit} (heq : List.Forall₂ SameOr C.gates D.gates)
    (w : ℕ) : orIn n C w = orIn n D w := by
  apply Finset.Subset.antisymm (orIn_subset n heq w)
  exact orIn_subset n (heq.flip.imp (fun _ _ h => sameOr_symm h)) w

lemma twoColour_iff (n : ℕ) {C D : Circuit} (heq : List.Forall₂ SameOr C.gates D.gates)
    (colour : ℕ → Bool) (j : ℕ) :
    IsTwoColour n C colour j ↔ IsTwoColour n D colour j := by
  have hgate : SameOr (gateAt C j) (gateAt D j) := getD_same heq j
  simp only [IsTwoColour, heq.length_eq, hgate.1, orIn_eq n heq]

lemma tCount_eq (n : ℕ) {C D : Circuit} (heq : List.Forall₂ SameOr C.gates D.gates)
    (colour : ℕ → Bool) : tCount n C colour = tCount n D colour := by
  unfold tCount twoColour
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range, heq.length_eq, twoColour_iff n heq]

end PEqualNP.Outside.L_meta_4675.OrInvariant

namespace PEqualNP.Outside.L_meta_4675.Normalize

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

lemma repair_tCount {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (pick : ℕ → Fin n × Fin n) (colour : ℕ → Bool) :
    PEqualNP.TwoColour.tCount n (repair G C pick) colour =
      PEqualNP.TwoColour.tCount n C colour := by
  classical
  have hrel : List.Forall₂ OrInvariant.SameOr C.gates (repair G C pick).gates := by
    apply List.forall₂_of_length_eq_of_get (repair_len G C pick).symm
    intro j hjC hjD
    change OrInvariant.SameOr C.gates[j] (repair G C pick).gates[j]
    rw [← gateAt_eq hjC, ← gateAt_eq hjD, repair_gate pick hjC]
    split_ifs with hd
    · refine ⟨hd.1, ?_⟩
      intro hop
      rw [hd.1] at hop
      cases hop
    · exact OrInvariant.sameOr_refl _
  exact (OrInvariant.tCount_eq n hrel colour).symm

end PEqualNP.Outside.L_meta_4675.Normalize

namespace PEqualNP.Outside.L_meta_4675.Restricted

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma inactive_dirty_bound (p l : ℕ) (E : Finset (Fin p × Fin l)) (C : Circuit)
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (hao : IsAO2 (p + l) C)
    (hcomp : ∀ x : Fin (p + l) → Bool, circuitFun (p + l) C x =
      decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧
        x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true))
    (htc : PEqualNP.TwoColour.tCount (p + l) C (fun i => decide (p ≤ i)) = 0)
    (hdead : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ¬ (∀ x : Fin (p + l) → Bool, gateVal (p + l) C j x = true →
        circuitFun (p + l) C x = true) →
      ∀ (a : Fin p) (b : Fin l), (a, b) ∈ E →
        gateVal (p + l) C j (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) = false) :
    ∃ S : Finset (Fin (p + l)),
      (∀ (a : Fin p) (b : Fin l), (a, b) ∈ E →
        Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      E.card + S.card ≤ C.size + 1 := by
  classical
  by_cases he : E = ∅
  · subst E
    exact ⟨∅, by simp, by simp⟩
  obtain ⟨⟨a, b⟩, hab⟩ := Finset.nonempty_iff_ne_empty.mpr he
  let G := Reuse.graph E
  letI : DecidableRel G.Adj := Classical.decRel _
  have hrel (x : Fin (p + l) → Bool) :
      (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧
        x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true) ↔
        ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
    constructor
    · rintro ⟨a, b, he, ha, hb⟩
      exact ⟨Fin.castAdd l a, Fin.natAdd p b,
        by simpa [G, Reuse.graph, Reuse.cross] using he, ha, hb⟩
    · rintro ⟨u, v, huv, hu, hv⟩
      cases u using Fin.addCases <;> cases v using Fin.addCases <;>
        simp [G, Reuse.graph, Reuse.cross] at huv
      · exact ⟨_, _, huv, hu, hv⟩
      · exact ⟨_, _, huv, hv, hu⟩
  have hgraph : circuitFun (p + l) C = graphFun G ∅ := by
    funext x
    apply Bool.eq_iff_iff.mpr
    rw [hcomp, decide_eq_true_eq]
    simpa [graphFun] using hrel x
  have hne : ∃ u v, G.Adj u v :=
    ⟨Fin.castAdd l a, Fin.natAdd p b, by simpa [G, Reuse.graph, Reuse.cross] using hab⟩
  have hswap (u v : Fin (p + l)) : pairInput u v = pairInput v u := by
    funext w
    simp only [pairInput]
    congr 1
    exact propext or_comm
  have hinactive : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ¬ BelowF G C j → ∀ u v, G.Adj u v →
        gateVal (p + l) C j (pairInput u v) = false := by
    intro j hj hop hn u v huv
    have hn' : ¬ (∀ x : Fin (p + l) → Bool, gateVal (p + l) C j x = true →
        circuitFun (p + l) C x = true) := by
      simpa only [hgraph, BelowF] using hn
    cases u using Fin.addCases <;> cases v using Fin.addCases <;>
      simp [G, Reuse.graph, Reuse.cross] at huv
    · exact hdead j hj hop hn' _ _ huv
    · rw [hswap]
      exact hdead j hj hop hn' _ _ huv
  obtain ⟨D, hD, hsize, hDcomp, hclean⟩ :=
    Normalize.erase_edge_inactive_dirty G C hao hgraph hne hinactive
  have hcompD (x : Fin (p + l) → Bool) : circuitFun (p + l) D x =
      decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧
        x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true) := by
    rw [hDcomp]
    apply Bool.eq_iff_iff.mpr
    simpa [graphFun] using (hrel x).symm
  have hcleanD : ∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
      ∀ x : Fin (p + l) → Bool, gateVal (p + l) D j x = true →
        circuitFun (p + l) D x = true := by
    intro j hj hop x hx
    rw [hDcomp]
    exact hclean j hj hop x hx
  obtain ⟨S, hcover, hbound⟩ := Reuse.clean_bound p l E D hfour hD hcompD hcleanD
  exact ⟨S, hcover, by simpa [hsize] using hbound⟩

end PEqualNP.Outside.L_meta_4675.Restricted

namespace PEqualNP.Outside.L_meta_4675_aux

lemma member_ne_of_card_two {α : Type*} [DecidableEq α]
    (S : Finset α) (hS : 2 ≤ S.card) (a : α) : ∃ b ∈ S, b ≠ a := by
  classical
  by_contra h
  have heq : ∀ b ∈ S, b = a := by
    intro b hb
    by_contra hba
    exact h ⟨b, hb, hba⟩
  have hcard : S.card ≤ 1 := Finset.card_le_one.mpr (by
    intro b hb c hc
    exact (heq b hb).trans (heq c hc).symm)
  omega

lemma reader_novel_column {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (A Q : Finset (Fin p)) (B P : Finset (Fin l))
    (hQ : 2 ≤ Q.card) (hP : P.Nonempty)
    (hrow : ∀ a ∈ A, a ∈ Q → ∀ b ∈ B, (a, b) ∈ E)
    (hbase : ∀ q ∈ Q, ∀ t ∈ P, (q, t) ∈ E)
    (htriple : ∀ a ∈ A, ∀ b ∈ B, ∀ q ∈ Q, (a, b) ∈ E ∨ (q, b) ∈ E)
    (a : Fin p) (ha : a ∈ A) (haQ : a ∈ Q)
    (b : Fin l) (hb : b ∈ B) (hbP : b ∉ P) :
    ∀ a' ∈ A, (a', b) ∈ E := by
  obtain ⟨t, ht⟩ := hP
  obtain ⟨q, hq, hqa⟩ := member_ne_of_card_two Q hQ a
  have htb : t ≠ b := by
    intro h
    exact hbP (h ▸ ht)
  have hqb : (q, b) ∉ E := by
    intro h
    exact hfour a q t b hqa.symm htb
      ⟨hbase a haQ t ht, hrow a ha haQ b hb, hbase q hq t ht, h⟩
  intro a' ha'
  exact (htriple a' ha' b hb q hq).resolve_right hqb

lemma reader_novel_at_most_one {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (A Q : Finset (Fin p)) (B P : Finset (Fin l))
    (hA : 2 ≤ A.card) (hB : 2 ≤ B.card) (hQ : 2 ≤ Q.card) (hP : P.Nonempty)
    (hrow : ∀ a ∈ A, a ∈ Q → ∀ b ∈ B, (a, b) ∈ E)
    (hbase : ∀ q ∈ Q, ∀ t ∈ P, (q, t) ∈ E)
    (htriple : ∀ a ∈ A, ∀ b ∈ B, ∀ q ∈ Q, (a, b) ∈ E ∨ (q, b) ∈ E) :
    ((A ∩ Q) ×ˢ (B \ P)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro x hx y hy
  simp only [Finset.mem_product, Finset.mem_inter, Finset.mem_sdiff] at hx hy
  have hxcol := reader_novel_column E hfour A Q B P hQ hP hrow hbase htriple
    x.1 hx.1.1 hx.1.2 x.2 hx.2.1 hx.2.2
  have hycol := reader_novel_column E hfour A Q B P hQ hP hrow hbase htriple
    y.1 hy.1.1 hy.1.2 y.2 hy.2.1 hy.2.2
  obtain ⟨b, hb, hbx⟩ := member_ne_of_card_two B hB x.2
  have hxy : x.1 = y.1 := by
    by_contra h
    exact hfour x.1 y.1 x.2 b h hbx.symm
      ⟨hrow x.1 hx.1.1 hx.1.2 x.2 hx.2.1, hrow x.1 hx.1.1 hx.1.2 b hb,
       hrow y.1 hy.1.1 hy.1.2 x.2 hx.2.1, hrow y.1 hy.1.1 hy.1.2 b hb⟩
  obtain ⟨a, ha, hax⟩ := member_ne_of_card_two A hA x.1
  have hxy' : x.2 = y.2 := by
    by_contra h
    exact hfour x.1 a x.2 y.2 hax.symm h
      ⟨hxcol x.1 hx.1.1, hycol x.1 hx.1.1, hxcol a ha, hycol a ha⟩
  exact Prod.ext hxy hxy'

def rectangleCorners {p l : ℕ} (E : Finset (Fin p × Fin l))
    (A : Finset (Fin p)) (B : Finset (Fin l)) : Finset (Fin p × Fin l) :=
  (A.filter fun a => ∀ b ∈ B, (a, b) ∈ E) ×ˢ
    (B.filter fun b => ∀ a ∈ A, (a, b) ∈ E)

lemma rectangle_corners_at_most_one {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (A : Finset (Fin p)) (B : Finset (Fin l))
    (hA : 2 ≤ A.card) (hB : 2 ≤ B.card) :
    (rectangleCorners E A B).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  simp only [rectangleCorners, Finset.mem_product, Finset.mem_filter] at hx hy
  obtain ⟨b, hb, hbx⟩ := member_ne_of_card_two B hB x.2
  have hxy : x.1 = y.1 := by
    by_contra h
    exact hfour x.1 y.1 x.2 b h hbx.symm
      ⟨hx.1.2 x.2 hx.2.1, hx.1.2 b hb, hy.1.2 x.2 hx.2.1, hy.1.2 b hb⟩
  obtain ⟨a, ha, hax⟩ := member_ne_of_card_two A hA x.1
  have hxy' : x.2 = y.2 := by
    by_contra h
    exact hfour x.1 a x.2 y.2 hax.symm h
      ⟨hx.2.2 x.1 hx.1.1, hy.2.2 x.1 hx.1.1, hx.2.2 a ha, hy.2.2 a ha⟩
  exact Prod.ext hxy hxy'

lemma reader_novel_subset_corners {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (A Q : Finset (Fin p)) (B P : Finset (Fin l))
    (hQ : 2 ≤ Q.card) (hP : P.Nonempty)
    (hrow : ∀ a ∈ A, a ∈ Q → ∀ b ∈ B, (a, b) ∈ E)
    (hbase : ∀ q ∈ Q, ∀ t ∈ P, (q, t) ∈ E)
    (htriple : ∀ a ∈ A, ∀ b ∈ B, ∀ q ∈ Q, (a, b) ∈ E ∨ (q, b) ∈ E) :
    (A ∩ Q) ×ˢ (B \ P) ⊆ rectangleCorners E A B := by
  intro x hx
  simp only [Finset.mem_product, Finset.mem_inter, Finset.mem_sdiff] at hx
  simp only [rectangleCorners, Finset.mem_product, Finset.mem_filter]
  exact ⟨⟨hx.1.1, hrow x.1 hx.1.1 hx.1.2⟩,
    hx.2.1, reader_novel_column E hfour A Q B P hQ hP hrow hbase htriple
      x.1 hx.1.1 hx.1.2 x.2 hx.2.1 hx.2.2⟩

lemma readers_share_at_most_one_novel_edge {p l : ℕ} {ι : Type*}
    [DecidableEq ι] (E : Finset (Fin p × Fin l))
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (A : Finset (Fin p)) (B : Finset (Fin l))
    (hA : 2 ≤ A.card) (hB : 2 ≤ B.card)
    (I : Finset ι) (Q : ι → Finset (Fin p)) (P : ι → Finset (Fin l))
    (hQ : ∀ i ∈ I, 2 ≤ (Q i).card) (hP : ∀ i ∈ I, (P i).Nonempty)
    (hrow : ∀ i ∈ I, ∀ a ∈ A, a ∈ Q i → ∀ b ∈ B, (a, b) ∈ E)
    (hbase : ∀ i ∈ I, ∀ q ∈ Q i, ∀ t ∈ P i, (q, t) ∈ E)
    (htriple : ∀ i ∈ I, ∀ a ∈ A, ∀ b ∈ B, ∀ q ∈ Q i,
      (a, b) ∈ E ∨ (q, b) ∈ E) :
    (I.biUnion fun i => (A ∩ Q i) ×ˢ (B \ P i)).card ≤ 1 := by
  apply le_trans (Finset.card_le_card ?_) (rectangle_corners_at_most_one E hfour A B hA hB)
  intro x hx
  obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hx
  exact reader_novel_subset_corners E hfour A (Q i) B (P i) (hQ i hi) (hP i hi)
    (hrow i hi) (hbase i hi) (htriple i hi) hxi

lemma reader_pairs_difference {p l : ℕ} (A Q : Finset (Fin p)) (B P : Finset (Fin l)) :
    ((A ∩ Q) ×ˢ B ∪ Q ×ˢ P) \ (Q ×ˢ P) = (A ∩ Q) ×ˢ (B \ P) := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_product, Finset.mem_inter]
  tauto

lemma reader_adjacencies_of_clean {p l : ℕ} (E : Finset (Fin p × Fin l))
    (A Q : Finset (Fin p)) (B P : Finset (Fin l))
    (hclean : ∀ (X : Finset (Fin p)) (Y : Finset (Fin l)),
      (((A ∩ X).Nonempty ∧ (B ∩ Y).Nonempty) ∨ (P ∩ Y).Nonempty) →
      (Q ∩ X).Nonempty → ∃ a ∈ X, ∃ b ∈ Y, (a, b) ∈ E) :
    (∀ a ∈ A, a ∈ Q → ∀ b ∈ B, (a, b) ∈ E) ∧
    (∀ q ∈ Q, ∀ t ∈ P, (q, t) ∈ E) ∧
    (∀ a ∈ A, ∀ b ∈ B, ∀ q ∈ Q, (a, b) ∈ E ∨ (q, b) ∈ E) := by
  constructor
  · intro a ha haQ b hb
    obtain ⟨a', ha', b', hb', he⟩ := hclean {a} {b}
      (Or.inl ⟨⟨a, Finset.mem_inter.mpr ⟨ha, by simp⟩⟩,
        ⟨b, Finset.mem_inter.mpr ⟨hb, by simp⟩⟩⟩)
      ⟨a, Finset.mem_inter.mpr ⟨haQ, by simp⟩⟩
    have ea : a' = a := Finset.mem_singleton.mp ha'
    have eb : b' = b := Finset.mem_singleton.mp hb'
    simpa only [ea, eb] using he
  constructor
  · intro q hq t ht
    obtain ⟨q', hq', t', ht', he⟩ := hclean {q} {t}
      (Or.inr ⟨t, Finset.mem_inter.mpr ⟨ht, by simp⟩⟩)
      ⟨q, Finset.mem_inter.mpr ⟨hq, by simp⟩⟩
    have eq : q' = q := Finset.mem_singleton.mp hq'
    have et : t' = t := Finset.mem_singleton.mp ht'
    simpa only [eq, et] using he
  · intro a ha b hb q hq
    obtain ⟨a', ha', b', hb', he⟩ := hclean {a, q} {b}
      (Or.inl ⟨⟨a, Finset.mem_inter.mpr ⟨ha, by simp⟩⟩,
        ⟨b, Finset.mem_inter.mpr ⟨hb, by simp⟩⟩⟩)
      ⟨q, Finset.mem_inter.mpr ⟨hq, by simp⟩⟩
    have eb : b' = b := Finset.mem_singleton.mp hb'
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha'
    rcases ha' with rfl | rfl
    · exact Or.inl (by simpa only [eb] using he)
    · exact Or.inr (by simpa only [eb] using he)

lemma clean_reader_novel_subset_corners {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (A Q : Finset (Fin p)) (B P : Finset (Fin l))
    (hQ : 2 ≤ Q.card) (hP : P.Nonempty)
    (hclean : ∀ (X : Finset (Fin p)) (Y : Finset (Fin l)),
      (((A ∩ X).Nonempty ∧ (B ∩ Y).Nonempty) ∨ (P ∩ Y).Nonempty) →
      (Q ∩ X).Nonempty → ∃ a ∈ X, ∃ b ∈ Y, (a, b) ∈ E) :
    ((A ∩ Q) ×ˢ B ∪ Q ×ˢ P) \ (Q ×ˢ P) ⊆ rectangleCorners E A B := by
  rw [reader_pairs_difference]
  obtain ⟨hrow, hbase, htriple⟩ := reader_adjacencies_of_clean E A Q B P hclean
  exact reader_novel_subset_corners E hfour A Q B P hQ hP hrow hbase htriple

end PEqualNP.Outside.L_meta_4675_aux

namespace PEqualNP.Outside.L_meta_4675_aux

lemma clean_product_neighbourhood_witness {α β ι : Type*} [DecidableEq ι]
    (R : α → β → Prop) (I : Finset ι) (A : ι → Finset α) (B : ι → Finset β)
    (hclean : ∀ (x : α → Bool) (y : β → Bool),
      (∀ i ∈ I, ∃ a ∈ A i, x a = true) →
      (∀ i ∈ I, ∃ b ∈ B i, y b = true) →
      ∃ a b, R a b ∧ x a = true ∧ y b = true)
    (b : β) (hb : ∀ i ∈ I, b ∈ B i) :
    ∃ i ∈ I, ∀ a ∈ A i, R a b := by
  classical
  by_contra hn
  have hw : ∀ i ∈ I, ∃ a ∈ A i, ¬ R a b := by
    intro i hi
    by_contra ha
    apply hn
    refine ⟨i, hi, ?_⟩
    intro a hai
    by_contra hr
    exact ha ⟨a, hai, hr⟩
  obtain ⟨a, b', hab, hax, hby⟩ := hclean
    (fun a => decide (¬ R a b)) (fun b' => decide (b' = b))
    (fun i hi => by
      obtain ⟨a, hai, har⟩ := hw i hi
      exact ⟨a, hai, by simp [har]⟩)
    (fun i hi => ⟨b, hb i hi, by simp⟩)
  have hb' : b' = b := by simpa using hby
  subst b'
  have hnot : ¬ R a b := by simpa using hax
  exact hnot hab

lemma large_set_common_neighbour_unique {α β : Type*}
    (R : α → β → Prop)
    (hfour : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ (R a b ∧ R a b' ∧ R a' b ∧ R a' b'))
    (A : Finset α) (hA : 1 < A.card)
    (b b' : β) (hb : ∀ a ∈ A, R a b) (hb' : ∀ a ∈ A, R a b') : b = b' := by
  obtain ⟨a, ha, a', ha', haa'⟩ := Finset.one_lt_card.mp hA
  by_contra hbb'
  exact hfour a a' b b' haa' hbb' ⟨hb a ha, hb' a ha, hb a' ha', hb' a' ha'⟩

lemma large_set_neighbourhood_cover_bound {α β ι : Type*} [DecidableEq ι]
    (R : α → β → Prop)
    (hfour : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ (R a b ∧ R a b' ∧ R a' b ∧ R a' b'))
    (I : Finset ι) (A : ι → Finset α) (T : Finset β)
    (hA : ∀ i ∈ I, 1 < (A i).card)
    (hcover : ∀ b ∈ T, ∃ i ∈ I, ∀ a ∈ A i, R a b) : T.card ≤ I.card := by
  classical
  let U : ι → Finset β := fun i => T.filter fun b => ∀ a ∈ A i, R a b
  have hsub : T ⊆ I.biUnion U := by
    intro b hb
    obtain ⟨i, hi, hAi⟩ := hcover b hb
    exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨hb, hAi⟩⟩
  have hU : ∀ i ∈ I, (U i).card ≤ 1 := by
    intro i hi
    apply Finset.card_le_one.mpr
    intro b hb b' hb'
    exact large_set_common_neighbour_unique R hfour (A i) (hA i hi) b b'
      (Finset.mem_filter.mp hb).2 (Finset.mem_filter.mp hb').2
  calc
    T.card ≤ (I.biUnion U).card := Finset.card_le_card hsub
    _ ≤ ∑ i ∈ I, (U i).card := Finset.card_biUnion_le
    _ ≤ ∑ i ∈ I, (1 : ℕ) := Finset.sum_le_sum hU
    _ = I.card := by simp

lemma clean_product_common_lines_bound {α β ι : Type*} [DecidableEq ι]
    (R : α → β → Prop)
    (hfour : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ (R a b ∧ R a b' ∧ R a' b ∧ R a' b'))
    (I : Finset ι) (A : ι → Finset α) (B : ι → Finset β) (T : Finset β)
    (hA : ∀ i ∈ I, 1 < (A i).card)
    (hT : ∀ b ∈ T, ∀ i ∈ I, b ∈ B i)
    (hclean : ∀ (x : α → Bool) (y : β → Bool),
      (∀ i ∈ I, ∃ a ∈ A i, x a = true) →
      (∀ i ∈ I, ∃ b ∈ B i, y b = true) →
      ∃ a b, R a b ∧ x a = true ∧ y b = true) : T.card ≤ I.card := by
  apply large_set_neighbourhood_cover_bound R hfour I A T hA
  intro b hb
  exact clean_product_neighbourhood_witness R I A B hclean b (hT b hb)

lemma clean_product_common_points_bound {α β ι : Type*} [DecidableEq ι]
    (R : α → β → Prop)
    (hfour : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ (R a b ∧ R a b' ∧ R a' b ∧ R a' b'))
    (I : Finset ι) (A : ι → Finset α) (B : ι → Finset β) (T : Finset α)
    (hB : ∀ i ∈ I, 1 < (B i).card)
    (hT : ∀ a ∈ T, ∀ i ∈ I, a ∈ A i)
    (hclean : ∀ (x : α → Bool) (y : β → Bool),
      (∀ i ∈ I, ∃ a ∈ A i, x a = true) →
      (∀ i ∈ I, ∃ b ∈ B i, y b = true) →
      ∃ a b, R a b ∧ x a = true ∧ y b = true) : T.card ≤ I.card := by
  have hfour' : ∀ b b' a a', b ≠ b' → a ≠ a' →
      ¬ (R a b ∧ R a' b ∧ R a b' ∧ R a' b') := by
    intro b b' a a' hbb' haa' h
    exact hfour a a' b b' haa' hbb' ⟨h.1, h.2.2.1, h.2.1, h.2.2.2⟩
  apply clean_product_common_lines_bound (fun b a => R a b) hfour' I B A T hB hT
  intro y x hY hX
  obtain ⟨a, b, hab, hax, hby⟩ := hclean x y hX hY
  exact ⟨b, a, hab, hby, hax⟩

end PEqualNP.Outside.L_meta_4675_aux

namespace PEqualNP.Outside.L_meta_4675.FlagCover

def flag {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (x : α → Bool) (y : β → Bool) : Bool :=
  decide ((∃ a ∈ A, x a = true) ∧ (∃ b ∈ B, y b = true))

lemma active_neighbourhood_witness {α β ι : Type*} [DecidableEq α] [DecidableEq β]
    (R : α → β → Prop) (A : ι → Finset α) (B : ι → Finset β)
    (F : (ι → Bool) → Bool)
    (hmono : ∀ u v, (∀ i, u i = true → v i = true) → F u = true → F v = true)
    (hsound : ∀ (x : α → Bool) (y : β → Bool),
      F (fun i => flag (A i) (B i) x y) = true →
      ∃ a b, R a b ∧ x a = true ∧ y b = true)
    (a : α) (b : β)
    (hpair : F (fun i => decide (a ∈ A i ∧ b ∈ B i)) = true) :
    ∃ i, a ∈ A i ∧ b ∈ B i ∧ ∀ a' ∈ A i, R a' b := by
  classical
  by_contra hn
  have hflags : ∀ i, decide (a ∈ A i ∧ b ∈ B i) = true →
      flag (A i) (B i) (fun a' => decide (¬ R a' b))
        (fun b' => decide (b' = b)) = true := by
    intro i hi
    have hai : a ∈ A i ∧ b ∈ B i := of_decide_eq_true hi
    have hw : ∃ a' ∈ A i, ¬ R a' b := by
      by_contra hw
      apply hn
      refine ⟨i, hai.1, hai.2, ?_⟩
      intro a' ha'
      by_contra hR
      exact hw ⟨a', ha', hR⟩
    obtain ⟨a', ha', hR⟩ := hw
    apply decide_eq_true
    exact ⟨⟨a', ha', by simp [hR]⟩, ⟨b, hai.2, by simp⟩⟩
  have hf := hmono _ _ hflags hpair
  obtain ⟨a', b', hR, hx, hy⟩ := hsound _ _ hf
  have hb' : b' = b := by simpa using hy
  subst b'
  have hnR : ¬ R a' b := by simpa using hx
  exact hnR hR

lemma clean_rectangle_cover {α β ι : Type*} [DecidableEq α] [DecidableEq β]
    (R : α → β → Prop) [DecidableRel R]
    (A : ι → Finset α) (B : ι → Finset β) (F : (ι → Bool) → Bool)
    (hmono : ∀ u v, (∀ i, u i = true → v i = true) → F u = true → F v = true)
    (hsound : ∀ (x : α → Bool) (y : β → Bool),
      F (fun i => flag (A i) (B i) x y) = true →
      ∃ a b, R a b ∧ x a = true ∧ y b = true)
    (hcomplete : ∀ a b, R a b → F (fun i => decide (a ∈ A i ∧ b ∈ B i)) = true) :
    ∀ a b, R a b ↔ ∃ i, a ∈ A i ∧ b ∈ (B i).filter (fun b => ∀ a' ∈ A i, R a' b) := by
  intro a b
  constructor
  · intro hab
    obtain ⟨i, hai, hbi, hRi⟩ := active_neighbourhood_witness R A B F hmono hsound a b
      (hcomplete a b hab)
    exact ⟨i, hai, Finset.mem_filter.mpr ⟨hbi, hRi⟩⟩
  · rintro ⟨i, hai, hbi⟩
    exact (Finset.mem_filter.mp hbi).2 a hai

lemma cleaned_line_side_card_le_one {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R : α → β → Prop) [DecidableRel R]
    (hfour : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ (R a b ∧ R a b' ∧ R a' b ∧ R a' b'))
    (A : Finset α) (B : Finset β) (hA : 1 < A.card) :
    (B.filter fun b => ∀ a ∈ A, R a b).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro b hb b' hb'
  obtain ⟨a, ha, a', ha', haa'⟩ := Finset.one_lt_card.mp hA
  by_contra hbb'
  have hR := (Finset.mem_filter.mp hb).2
  have hR' := (Finset.mem_filter.mp hb').2
  exact hfour a a' b b' haa' hbb'
    ⟨hR a ha, hR' a ha, hR a' ha', hR' a' ha'⟩

lemma clean_star_cover {α β ι : Type*} [DecidableEq α] [DecidableEq β]
    (R : α → β → Prop) [DecidableRel R]
    (hfour : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ (R a b ∧ R a b' ∧ R a' b ∧ R a' b'))
    (A : ι → Finset α) (B : ι → Finset β) (F : (ι → Bool) → Bool)
    (hbig : ∀ i, 1 < (A i).card)
    (hmono : ∀ u v, (∀ i, u i = true → v i = true) → F u = true → F v = true)
    (hsound : ∀ (x : α → Bool) (y : β → Bool),
      F (fun i => flag (A i) (B i) x y) = true →
      ∃ a b, R a b ∧ x a = true ∧ y b = true)
    (hcomplete : ∀ a b, R a b → F (fun i => decide (a ∈ A i ∧ b ∈ B i)) = true) :
    ∃ D : ι → Finset β,
      (∀ i, D i ⊆ B i ∧ (D i).card ≤ 1) ∧
      (∀ a b, R a b ↔ ∃ i, a ∈ A i ∧ b ∈ D i) := by
  refine ⟨fun i => (B i).filter (fun b => ∀ a ∈ A i, R a b), ?_, ?_⟩
  · intro i
    exact ⟨Finset.filter_subset _ _, cleaned_line_side_card_le_one R hfour (A i) (B i) (hbig i)⟩
  · exact clean_rectangle_cover R A B F hmono hsound hcomplete


lemma active_neighbourhood_witness_dual {α β ι : Type*} [DecidableEq α] [DecidableEq β]
    (R : α → β → Prop) (A : ι → Finset α) (B : ι → Finset β)
    (F : (ι → Bool) → Bool)
    (hmono : ∀ u v, (∀ i, u i = true → v i = true) → F u = true → F v = true)
    (hsound : ∀ (x : α → Bool) (y : β → Bool),
      F (fun i => flag (A i) (B i) x y) = true →
      ∃ a b, R a b ∧ x a = true ∧ y b = true)
    (a : α) (b : β)
    (hpair : F (fun i => decide (a ∈ A i ∧ b ∈ B i)) = true) :
    ∃ i, a ∈ A i ∧ b ∈ B i ∧ ∀ b' ∈ B i, R a b' := by
  have hs : ∀ (y : β → Bool) (x : α → Bool),
      F (fun i => flag (B i) (A i) y x) = true →
      ∃ b a, R a b ∧ y b = true ∧ x a = true := by
    intro y x hf
    have he : (fun i => flag (B i) (A i) y x) = (fun i => flag (A i) (B i) x y) := by
      funext i
      by_cases hX : ∃ a ∈ A i, x a = true <;>
        by_cases hY : ∃ b ∈ B i, y b = true <;> simp [flag, hX, hY]
    have hf' : F (fun i => flag (A i) (B i) x y) = true := by
      rwa [he] at hf
    obtain ⟨a, b, hab, hax, hby⟩ := hsound x y hf'
    exact ⟨b, a, hab, hby, hax⟩
  have hp : F (fun i => decide (b ∈ B i ∧ a ∈ A i)) = true := by
    simpa only [and_comm] using hpair
  obtain ⟨i, hbi, hai, hR⟩ := active_neighbourhood_witness (fun b a => R a b)
    B A F hmono hs b a hp
  exact ⟨i, hai, hbi, hR⟩

lemma active_certificate_cases {α β ι : Type*} [DecidableEq α] [DecidableEq β]
    (R : α → β → Prop) (A : ι → Finset α) (B : ι → Finset β)
    (F : (ι → Bool) → Bool)
    (hmono : ∀ u v, (∀ i, u i = true → v i = true) → F u = true → F v = true)
    (hsound : ∀ (x : α → Bool) (y : β → Bool),
      F (fun i => flag (A i) (B i) x y) = true →
      ∃ a b, R a b ∧ x a = true ∧ y b = true)
    (a : α) (b : β)
    (hpair : F (fun i => decide (a ∈ A i ∧ b ∈ B i)) = true) :
    (∃ i, a ∈ A i ∧ b ∈ B i ∧ 1 < (A i).card ∧ ∀ a' ∈ A i, R a' b) ∨
    (∃ i, a ∈ A i ∧ b ∈ B i ∧ 1 < (B i).card ∧ ∀ b' ∈ B i, R a b') ∨
    (∃ i j, A i = {a} ∧ B j = {b} ∧ b ∈ B i ∧ a ∈ A j) := by
  obtain ⟨i, hai, hbi, hRi⟩ := active_neighbourhood_witness R A B F hmono hsound a b hpair
  by_cases hAi : 1 < (A i).card
  · exact Or.inl ⟨i, hai, hbi, hAi, hRi⟩
  obtain ⟨j, haj, hbj, hRj⟩ := active_neighbourhood_witness_dual R A B F hmono hsound a b hpair
  by_cases hBj : 1 < (B j).card
  · exact Or.inr (Or.inl ⟨j, haj, hbj, hBj, hRj⟩)
  right
  right
  refine ⟨i, j, ?_, ?_, hbi, haj⟩
  · apply Finset.eq_singleton_iff_unique_mem.mpr
    exact ⟨hai, fun a' ha' => Finset.card_le_one.mp (by omega) a' ha' a hai⟩
  · apply Finset.eq_singleton_iff_unique_mem.mpr
    exact ⟨hbj, fun b' hb' => Finset.card_le_one.mp (by omega) b' hb' b hbj⟩

end PEqualNP.Outside.L_meta_4675.FlagCover

namespace PEqualNP.Outside.L_meta_4675.FlagCover

lemma finite_centres {α β : Type*} [DecidableEq α] [DecidableEq β] [Inhabited β]
    (R : α → β → Prop) (G : Finset ℕ) (A : ℕ → Finset α) (D : ℕ → Finset β)
    (hcard : ∀ i ∈ G, (D i).card ≤ 1)
    (hrect : ∀ i ∈ G, ∀ a ∈ A i, ∀ b ∈ D i, R a b)
    (hcover : ∀ a b, R a b → ∃ i ∈ G, a ∈ A i ∧ b ∈ D i) :
    ∃ (J : Finset ℕ) (c : ℕ → β),
      J ⊆ G ∧
      (∀ i ∈ J, D i = {c i}) ∧
      (∀ a b, R a b → ∃ i ∈ J, a ∈ A i ∧ b = c i) ∧
      (∀ i ∈ J, ∀ a ∈ A i, R a (c i)) := by
  classical
  let J := G.filter fun i => (D i).Nonempty
  let c : ℕ → β := fun i => if h : (D i).Nonempty then h.choose else default
  have hJ : ∀ i, i ∈ J ↔ i ∈ G ∧ (D i).Nonempty := by
    intro i
    exact Finset.mem_filter
  have hc : ∀ i ∈ J, c i ∈ D i := by
    intro i hi
    have hn := (hJ i).mp hi |>.2
    simp only [c, dif_pos hn]
    exact hn.choose_spec
  have hsingle : ∀ i ∈ J, D i = {c i} := by
    intro i hi
    apply Finset.eq_singleton_iff_unique_mem.mpr
    exact ⟨hc i hi, fun b hb => Finset.card_le_one.mp
      (hcard i ((hJ i).mp hi).1) b hb (c i) (hc i hi)⟩
  refine ⟨J, c, Finset.filter_subset _ _, hsingle, ?_, ?_⟩
  · intro a b hab
    obtain ⟨i, hi, hai, hbi⟩ := hcover a b hab
    have hiJ : i ∈ J := (hJ i).mpr ⟨hi, ⟨b, hbi⟩⟩
    refine ⟨i, hiJ, hai, ?_⟩
    rw [hsingle i hiJ] at hbi
    exact Finset.mem_singleton.mp hbi
  · intro i hi a hai
    exact hrect i ((hJ i).mp hi).1 a hai (c i) (hc i hi)

end PEqualNP.Outside.L_meta_4675.FlagCover

namespace PEqualNP.Outside.L_meta_4675.Reuse

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma certificate_budget {n : ℕ} {C : Circuit} (G : SimpleGraph (Fin n))
    (hm : Monotone2 C) (rb : ReadsBack n C)
    (hclean : ∀ k, reachable n C k → (gateAt C k).op = GateOp.and →
      singletonSupport n C (n + k) = ∅)
    (hcommon : ∀ c d v w : Fin n, c ≠ d → v ≠ w →
      G.Adj c v → G.Adj c w → G.Adj d v → G.Adj d w → False)
    (B : Finset ℕ) (hB : B ⊆ births n C)
    (c : ℕ → Fin n) (w : ℕ → ℕ)
    (choose_spec : ∀ k ∈ B, w k ∈ (gateAt C k).inputs ∧
      ∀ v ∈ singletonSupport n C (w k), G.Adj (c k) v)
    (cover : ∀ u v, G.Adj u v → ∃ k ∈ B,
      (u = c k ∧ v ∈ singletonSupport n C (w k)) ∨
      (v = c k ∧ u ∈ singletonSupport n C (w k)))
    (E : Finset (Fin n × Fin n))
    (hE : ∀ p ∈ E, G.Adj p.1 p.2 ∧ p.1 ≤ p.2) :
    ∃ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
      T.card ≤ B.card ∧ E.card + B.card ≤ C.size + 1 := by
  classical
  let T := B.image c
  let fiber (u : Fin n) := B.filter fun k => c k = u
  let roots (u : Fin n) := (fiber u).image w
  let leaves (u : Fin n) := (roots u).biUnion (singletonSupport n C)
  have hcov : ∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T := by
    intro u v huv
    obtain ⟨k, hk, ⟨rfl, _⟩ | ⟨rfl, _⟩⟩ := cover u v huv
    · exact Or.inl (Finset.mem_image_of_mem c hk)
    · exact Or.inr (Finset.mem_image_of_mem c hk)
  have hEsub : E ⊆ T.biUnion (fun t => (leaves t).image (edgeKey t)) := by
    rintro ⟨u, v⟩ hp
    obtain ⟨huv, huv'⟩ := hE _ hp
    obtain ⟨k, hk, h⟩ := cover u v huv
    have hroot : w k ∈ roots (c k) := Finset.mem_image_of_mem w (Finset.mem_filter.2 ⟨hk, rfl⟩)
    refine Finset.mem_biUnion.2 ⟨c k, Finset.mem_image_of_mem c hk, ?_⟩
    have hkey : edgeKey u v = (u, v) := by simp [edgeKey, min_eq_left huv', max_eq_right huv']
    rcases h with ⟨he, h⟩ | ⟨he, h⟩
    · exact Finset.mem_image.2 ⟨v, Finset.mem_biUnion.2 ⟨w k, hroot, h⟩, by rwa [← he]⟩
    · exact Finset.mem_image.2 ⟨u, Finset.mem_biUnion.2 ⟨w k, hroot, h⟩, by rwa [← he, edgeKey_comm]⟩
  have hleaf (t : Fin n) : (leaves t).card ≤ (fiber t).card +
      (mergePool C G t C.gates.length).card := by
    have hr (a) (ha : a ∈ roots t) : ∃ k ∈ B, c k = t ∧ w k = a := by
      obtain ⟨k, hk, he⟩ := Finset.mem_image.1 ha
      exact ⟨k, (Finset.mem_filter.1 hk).1, (Finset.mem_filter.1 hk).2, he⟩
    have h := leaf_budget (G := G) (c := t) hm rb hclean C.gates.length (roots t) (by
      intro a ha
      obtain ⟨k, hk, _, rfl⟩ := hr a ha
      by_cases hn : w k < n
      · exact Or.inl hn
      · apply Or.inr
        exact reachable_child rb (mem_births.1 (hB hk)).1 (by
          rw [show n + (w k - n) = w k by omega]
          exact (choose_spec k hk).1)) (by
      intro a ha v hv
      obtain ⟨k, hk, rfl, rfl⟩ := hr a ha
      exact (choose_spec k hk).2 v hv) (by
      intro a ha _
      obtain ⟨k, hk, _, rfl⟩ := hr a ha
      have hk' := (mem_births.1 (hB hk)).1.1
      have := rb k hk' (w k) (choose_spec k hk).1
      omega)
    exact h.trans (Nat.add_le_add_right Finset.card_image_le _)
  have hdisjFib : (T : Set (Fin n)).PairwiseDisjoint fiber := by
    intro a _ b _ hab
    rw [Function.onFun, Finset.disjoint_left]
    intro k hka hkb
    exact hab ((Finset.mem_filter.1 hka).2.symm.trans (Finset.mem_filter.1 hkb).2)
  have hsumB : (∑ t ∈ T, (fiber t).card) = B.card := by
    rw [← Finset.card_biUnion hdisjFib]
    congr 1
    ext k
    constructor
    · intro hk
      obtain ⟨_, _, hf⟩ := Finset.mem_biUnion.1 hk
      exact (Finset.mem_filter.1 hf).1
    · intro hk
      exact Finset.mem_biUnion.2 ⟨c k, Finset.mem_image_of_mem c hk, Finset.mem_filter.2 ⟨hk, rfl⟩⟩
  have hdisjPool : (T : Set (Fin n)).PairwiseDisjoint (fun t => mergePool C G t C.gates.length) := by
    intro a _ b _ hab
    rw [Function.onFun, Finset.disjoint_left]
    intro k hka hkb
    obtain ⟨_, hk, ha⟩ := mem_mergePool.1 hka
    have hb := (mem_mergePool.1 hkb).2.2
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.1 (mem_merges.1 hk).2.2.1
    exact hcommon a b u v hab huv (ha u hu) (ha v hv) (hb u hu) (hb v hv)
  have hsumL : (∑ t ∈ T, (mergePool C G t C.gates.length).card) ≤ (merges n C).card := by
    rw [← Finset.card_biUnion hdisjPool]
    apply Finset.card_le_card
    intro k hk
    obtain ⟨t, _, ht⟩ := Finset.mem_biUnion.1 hk
    exact (mem_mergePool.1 ht).2.1
  have hEL : E.card ≤ B.card + (merges n C).card := by
    calc
      _ ≤ (T.biUnion fun t => (leaves t).image (edgeKey t)).card := Finset.card_le_card hEsub
      _ ≤ ∑ t ∈ T, ((leaves t).image (edgeKey t)).card := Finset.card_biUnion_le
      _ ≤ ∑ t ∈ T, (leaves t).card := Finset.sum_le_sum fun _ _ => Finset.card_image_le
      _ ≤ ∑ t ∈ T, ((fiber t).card + (mergePool C G t C.gates.length).card) :=
        Finset.sum_le_sum fun t _ => hleaf t
      _ ≤ _ := by rw [Finset.sum_add_distrib, hsumB]; exact Nat.add_le_add_left hsumL _
  have hgate := gate_budget hm rb hclean
  have hBcard : B.card ≤ (births n C).card := Finset.card_le_card hB
  exact ⟨T, hcov, Finset.card_image_le, by change E.card + B.card ≤ C.size + 1; omega⟩

end PEqualNP.Outside.L_meta_4675.Reuse

namespace PEqualNP.Outside.L_meta_4675.Reuse

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

noncomputable def reachableGates (n : ℕ) (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter (reachable n C)

noncomputable def andInputCount (n : ℕ) (C : Circuit) (k : ℕ) : ℕ := by
  classical
  exact if (gateAt C k).op = GateOp.and then (positiveInputs n C k).card else 0

lemma positive_gate_budget {n : ℕ} {C : Circuit} (hm : Monotone2 C) (rb : ReadsBack n C)
    (hclean : ∀ k, reachable n C k → (gateAt C k).op = GateOp.and →
      singletonSupport n C (n + k) = ∅) :
    (∑ k ∈ reachableGates n C, andInputCount n C k) +
      (merges n C).card ≤ C.size + 1 := by
  classical
  let R := (Finset.range C.gates.length).filter (reachable n C)
  let Z := R.filter fun k => singletonSupport n C (n + k) = ∅
  let D := fun k => (gateAt C k).inputs.toFinset.filter fun w =>
    n ≤ w ∧ singletonSupport n C w = ∅
  let E := fun k => (D k).image fun w => w - n
  have hR (k) : k ∈ R ↔ reachable n C k := by
    simp only [R, Finset.mem_filter, Finset.mem_range]
    exact ⟨And.right, fun h => ⟨h.1, h⟩⟩
  have hZ (k) : k ∈ Z ↔ k ∈ R ∧ singletonSupport n C (n + k) = ∅ := Finset.mem_filter
  have hread : Z.erase (C.output - n) ⊆ R.biUnion E := by
    intro j hj
    obtain ⟨hne, hz⟩ := Finset.mem_erase.1 hj
    obtain ⟨k, hk, hin⟩ := reachable_reader ((hR j).1 ((hZ j).1 hz).1) hne
    refine Finset.mem_biUnion.2 ⟨k, (hR k).2 hk, Finset.mem_image.2 ⟨n + j, ?_, by omega⟩⟩
    exact Finset.mem_filter.2 ⟨List.mem_toFinset.2 hin, by omega, ((hZ j).1 hz).2⟩
  have hsum : Z.card ≤ (∑ k ∈ R, (D k).card) + 1 := by
    calc
      Z.card ≤ (Z.erase (C.output - n)).card + 1 := by
        by_cases h : C.output - n ∈ Z
        · exact Nat.le_of_eq (Finset.card_erase_add_one h).symm
        · rw [Finset.erase_eq_of_notMem h]; omega
      _ ≤ (R.biUnion E).card + 1 := Nat.add_le_add_right (Finset.card_le_card hread) _
      _ ≤ (∑ k ∈ R, (E k).card) + 1 := Nat.add_le_add_right Finset.card_biUnion_le _
      _ ≤ _ := Nat.add_le_add_right (Finset.sum_le_sum fun _ _ => Finset.card_image_le) _
  have hlocal : ∀ k ∈ R, (D k).card + andInputCount n C k +
      (if k ∈ merges n C then 1 else 0) ≤ 1 + (if k ∈ Z then 1 else 0) := by
    intro k hk
    have hr := (hR k).1 hk
    have hdp : Disjoint (D k) (positiveInputs n C k) := by
      rw [Finset.disjoint_left]
      intro w hd hp
      have he := (Finset.mem_filter.1 hd).2.2
      simpa [he] using (mem_positiveInputs.1 hp).2
    have hcap : (D k).card + (positiveInputs n C k).card ≤ 2 := by
      rw [← Finset.card_union_of_disjoint hdp]
      exact (Finset.card_le_card (Finset.union_subset
        (Finset.filter_subset _ _) (Finset.filter_subset _ _))).trans (input_card hm hr.1)
    by_cases ha : (gateAt C k).op = GateOp.and
    · have hz := (hZ k).2 ⟨hk, hclean k hr ha⟩
      have hl : k ∉ merges n C := by
        intro h
        have hh := (mem_merges.1 h).2.1
        rw [ha] at hh
        cases hh
      simpa [andInputCount, ha, hz, hl] using hcap
    · by_cases hl : k ∈ merges n C
      · have hpos := (mem_merges.1 hl).2.2.2
        simp only [andInputCount, ha, hl, ite_false, ite_true, Nat.add_zero]
        split_ifs <;> omega
      · by_cases hz : k ∈ Z
        · simp only [andInputCount, ha, hl, hz, ite_false, ite_true, Nat.add_zero]
          omega
        · have hs : (singletonSupport n C (n + k)).Nonempty :=
            Finset.nonempty_iff_ne_empty.2 fun h => hz ((hZ k).2 ⟨hk, h⟩)
          have hop : (gateAt C k).op = GateOp.or := (gate_op hm hr.1).resolve_left ha
          obtain ⟨u, hu⟩ := hs
          obtain ⟨w, hw, huw⟩ := (support_or rb hr.1 hop u).1 hu
          have hpos := Finset.card_pos.2 ⟨w, mem_positiveInputs.2 ⟨hw, u, huw⟩⟩
          simp only [andInputCount, ha, hl, hz, ite_false, Nat.add_zero]
          omega
  have count (T : Finset ℕ) (hT : T ⊆ R) :
      (∑ k ∈ R, if k ∈ T then 1 else 0) = T.card := by
    rw [← Finset.card_filter]
    congr 1
    ext k
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun h => ⟨hT h, h⟩⟩
  have hL : merges n C ⊆ R := fun _ h => (hR _).2 (mem_merges.1 h).1
  have h := Finset.sum_le_sum hlocal
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, count _ hL,
    Finset.sum_add_distrib, count Z (Finset.filter_subset _ _)] at h
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at h
  have hRc : R.card ≤ C.size := by
    change R.card ≤ C.gates.length
    exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
  change (∑ k ∈ R, andInputCount n C k) + (merges n C).card ≤ C.size + 1
  omega

end PEqualNP.Outside.L_meta_4675.Reuse

namespace PEqualNP.Outside.L_meta_4675.Normalize

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma erase_unique_edge_dirty {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hC : IsAO2 n C)
    (hcomp : circuitFun n C = graphFun G ∅)
    (hne : ∃ a b, G.Adj a b)
    (hunique : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ¬ BelowF G C j → ∀ u v a b, G.Adj u v → G.Adj a b →
      gateVal n C j (pairInput u v) = true → gateVal n C j (pairInput a b) = true →
        s(u, v) = s(a, b))
    (colour : ℕ → Bool) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size = C.size ∧
      circuitFun n D = graphFun G ∅ ∧
      (∀ j < D.gates.length, (gateAt D j).op = GateOp.and → BelowF G D j) ∧
      PEqualNP.TwoColour.tCount n D colour = PEqualNP.TwoColour.tCount n C colour := by
  classical
  obtain ⟨a, b, hab⟩ := hne
  let hit (j : ℕ) (e : Fin n × Fin n) : Prop :=
    G.Adj e.1 e.2 ∧ gateVal n C j (pairInput e.1 e.2) = true
  let pick : ℕ → Fin n × Fin n := fun j => if h : ∃ e, hit j e then h.choose else (a, b)
  have pick_hit (j : ℕ) (e : Fin n × Fin n) (he : hit j e) : hit j (pick j) := by
    have hex : ∃ e, hit j e := ⟨e, he⟩
    simpa only [pick, dif_pos hex] using hex.choose_spec
  have pick_adj (j : ℕ) : G.Adj (pick j).1 (pick j).2 := by
    by_cases hex : ∃ e, hit j e
    · exact (pick_hit j hex.choose hex.choose_spec).1
    · simpa only [pick, dif_neg hex] using hab
  let D := repair G C pick
  have hD : IsAO2 n D := repair_ao hC pick
  have reflect (x : Fin n → Bool) (hn : graphFun G ∅ x ≠ true) (w : ℕ) :
      val D (List.ofFn x) w = true → val C (List.ofFn x) w = true :=
    repair_compare hC pick x false (by
      intro j hj hd hv
      have hp := (repair_replaced_val pick hj hd x).1 hv
      exact (hn (graph_true.2 ⟨_, _, pick_adj j, hp.1, hp.2⟩)).elim) w
  have clean : ∀ j < D.gates.length, (gateAt D j).op = GateOp.and → BelowF G D j := by
    intro j hj hop x hv
    have hj' : j < C.gates.length := by rwa [repair_len] at hj
    by_cases hd : dirty G C j
    · have hp := (repair_replaced_val pick hj' hd x).1 hv
      exact graph_true.2 ⟨_, _, pick_adj j, hp.1, hp.2⟩
    · have hop' : (gateAt C j).op = GateOp.and := by
        rwa [repair_kept pick hj' hd] at hop
      by_contra hn
      have hbelow : BelowF G C j := by
        by_contra h
        exact hd ⟨hop', h⟩
      exact hn (hbelow x (reflect x hn (n + j) hv))
  have keep_pair (u v : Fin n) (huv : G.Adj u v) :
      circuitFun n D (pairInput u v) = true := by
    have hc : circuitFun n C (pairInput u v) = true := by
      rw [hcomp]
      exact graph_true.2 (edge_true_pair.2 huv)
    exact repair_compare hC pick (pairInput u v) true (by
      intro j hj hd hv
      change gateVal n C j (pairInput u v) = true at hv
      have hh := pick_hit j (u, v) ⟨huv, hv⟩
      have heq : s((pick j).1, (pick j).2) = s(u, v) :=
        hunique j hj hd.1 hd.2 _ _ u v hh.1 huv hh.2 hv
      apply (repair_replaced_val pick hj hd _).2
      rcases Sym2.eq_iff.1 heq with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> simp [h₁, h₂, pairInput])
      C.output hc
  have eq : circuitFun n D = graphFun G ∅ := by
    funext x
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hx
      by_contra hn
      have h := reflect x hn C.output hx
      change circuitFun n C x = true at h
      rw [hcomp] at h
      exact hn h
    · intro hx
      obtain ⟨u, v, huv, hu, hv⟩ := graph_true.1 hx
      apply val_mono hD (x := pairInput u v) (y := x) ?_ C.output (keep_pair u v huv)
      intro i hi
      simp only [pairInput, decide_eq_true_eq] at hi
      rcases hi with rfl | rfl
      · exact hu
      · exact hv
  exact ⟨D, hD, repair_len G C pick, eq, clean, repair_tCount G C pick colour⟩

private lemma sorted_edges {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ∃ E : Finset (Fin n × Fin n), E.card = G.edgeFinset.card ∧
      ∀ p ∈ E, G.Adj p.1 p.2 ∧ p.1 ≤ p.2 := by
  let E := Finset.univ.filter fun p : Fin n × Fin n => G.Adj p.1 p.2 ∧ p.1 ≤ p.2
  refine ⟨E, ?_, fun p hp => (Finset.mem_filter.1 hp).2⟩
  apply Finset.card_bij (fun p _ => s(p.1, p.2))
  · exact fun p hp => SimpleGraph.mem_edgeFinset.2 (Finset.mem_filter.1 hp).2.1
  · intro a ha b hb hab
    rcases Sym2.eq_iff.1 hab with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Prod.ext h₁ h₂
    · have hle₁ := (Finset.mem_filter.1 ha).2.2
      have hle₂ := (Finset.mem_filter.1 hb).2.2
      have he : b.1 = b.2 := le_antisymm hle₂ (by rwa [h₁, h₂] at hle₁)
      exact Prod.ext (h₁.trans he.symm) (h₂.trans he)
  · intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have h := SimpleGraph.mem_edgeFinset.1 he
      rcases le_total u v with huv | hvu
      · exact ⟨(u, v), Finset.mem_filter.2 ⟨Finset.mem_univ _, h, huv⟩, rfl⟩
      · exact ⟨(v, u), Finset.mem_filter.2 ⟨Finset.mem_univ _, h.symm, hvu⟩, Sym2.eq_swap⟩

lemma unique_dirty_graph_bound {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hfour : NoFourCycle G)
    (hC : IsAO2 n C) (hcomp : circuitFun n C = graphFun G ∅)
    (hne : ∃ a b, G.Adj a b)
    (hunique : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ¬ BelowF G C j → ∀ u v a b, G.Adj u v → G.Adj a b →
      gateVal n C j (pairInput u v) = true → gateVal n C j (pairInput a b) = true →
        s(u, v) = s(a, b)) :
    ∃ S : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ S ∨ v ∈ S) ∧
      G.edgeFinset.card + S.card ≤ C.size + 1 := by
  classical
  obtain ⟨u, v, huv⟩ := hne
  obtain ⟨D, hD, hsize, hDcomp, hclean, _⟩ :=
    erase_unique_edge_dirty G C hC hcomp ⟨u, v, huv⟩ hunique (fun _ => false)
  have hm : Monotone2 D := by
    intro g hg
    exact ⟨by simpa using hD.1 g hg, (hD.2.2 g hg).le⟩
  obtain ⟨E, hcard, hE⟩ := sorted_edges G
  obtain ⟨T, hcover, hT, hbound⟩ := Reuse.graph_budget (C := D) G u hm hD.2.1
    (fun j hj hop a b ht => edge_true_pair.1 (graph_true.1 (hclean j hj.1 hop _ ht)))
    (by
      intro j hj hop
      cases h : gateVal n D j (fun _ => false)
      · rfl
      · obtain ⟨a, b, _, ha, _⟩ := graph_true.1 (hclean j hj.1 hop _ h)
        cases ha)
    (fun _ _ _ _ => Reuse.no_four_cycle hfour)
    (by
      apply Finset.eq_empty_iff_forall_notMem.2
      intro a ha
      have hh : circuitFun n D (pairInput a a) = true := Reuse.mem_support.1 ha
      rw [hDcomp] at hh
      exact G.irrefl (edge_true_pair.1 (graph_true.1 hh)))
    (by
      intro a b hab
      change circuitFun n D (pairInput a b) = true
      rw [hDcomp]
      exact graph_true.2 (edge_true_pair.2 hab)) E hE
  refine ⟨T, hcover, ?_⟩
  rw [hcard] at hbound
  omega

end PEqualNP.Outside.L_meta_4675.Normalize

namespace PEqualNP.Outside.L_meta_4675.Reuse

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadK

lemma support_false_under {n : ℕ} {C : Circuit} (hm : Monotone2 C)
    (x : Fin n → Bool) (w : ℕ) (hw : val C (List.ofFn x) w = false) :
    ∀ u ∈ singletonSupport n C w, x u = false := by
  intro u hu
  cases hxu : x u
  · rfl
  · have hxy : ∀ v, pairInput u u v = true → x v = true := by
      intro v hv
      have hvu : v = u := by simpa [pairInput] using hv
      simpa only [hvu] using hxu
    have hh := pair_mono hm hxy w (mem_support.1 hu)
    rw [hw] at hh
    cases hh

lemma reachable_difference_or_slot {n : ℕ} {C : Circuit}
    (hm : Monotone2 C) (rb : ReadsBack n C) (x y : Fin n → Bool) :
    ∀ w, w < n + C.gates.length → (n ≤ w → reachable n C (w - n)) →
      val C (List.ofFn x) w = true → val C (List.ofFn y) w = false →
      (∃ u ∈ singletonSupport n C w, x u = true) ∨
      ∃ k, reachable n C k ∧ (gateAt C k).op = GateOp.and ∧
        ∃ v ∈ (gateAt C k).inputs,
          (∃ u ∈ singletonSupport n C v, x u = true) ∧
          ∀ u ∈ singletonSupport n C v, y u = false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hwb hreach hx hy
    by_cases hin : w < n
    · left
      let u : Fin n := ⟨w, hin⟩
      refine ⟨u, ?_, ?_⟩
      · change u ∈ singletonSupport n C u.val
        rw [support_input]
        simp
      · change val C (List.ofFn x) u.val = true at hx
        simpa only [val_ofFn] using hx
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      have hr : reachable n C k := by simpa using hreach (by omega)
      have hchild : ∀ v ∈ (gateAt C k).inputs, n ≤ v → reachable n C (v - n) := by
        intro v hv hvn
        apply reachable_child rb hr
        simpa only [Nat.add_sub_of_le hvn] using hv
      rcases gate_op hm hk with hop | hop
      · have hoperand : ∃ v ∈ (gateAt C k).inputs, val C (List.ofFn y) v = false := by
          by_contra hn
          have hh := (val_and (by simp : (List.ofFn y).length = n) hk hop).2 (by
            intro v hv
            refine ⟨((val_and (by simp) hk hop).1 hx v hv).1, ?_⟩
            cases hyv : val C (List.ofFn y) v
            · exact (hn ⟨v, hv, hyv⟩).elim
            · rfl)
          rw [hy] at hh
          cases hh
        obtain ⟨v, hv, hvy⟩ := hoperand
        have hvx := (val_and (by simp) hk hop).1 hx v hv
        rcases ih v hvx.1 (by omega) (hchild v hv) hvx.2 hvy with hu | hs
        · exact Or.inr ⟨k, hr, hop, v, hv, hu, support_false_under hm y v hvy⟩
        · exact Or.inr hs
      · obtain ⟨v, hv, hvlt, hvx⟩ := (val_or (by simp) hk hop).1 hx
        have hvy : val C (List.ofFn y) v = false := by
          cases hyv : val C (List.ofFn y) v
          · rfl
          · have hh := (val_or (by simp) hk hop).2 ⟨v, hv, hvlt, hyv⟩
            rw [hy] at hh
            cases hh
        rcases ih v hvlt (by omega) (hchild v hv) hvx hvy with ⟨u, hu, hux⟩ | hs
        · exact Or.inl ⟨u, (support_or rb hk hop u).2 ⟨v, hv, hu⟩, hux⟩
        · exact Or.inr hs

lemma reachable_distinguishing_and_operand {n : ℕ} {C : Circuit}
    (hm : Monotone2 C) (rb : ReadsBack n C) (x y : Fin n → Bool)
    (hout : singletonSupport n C C.output = ∅)
    (hx : C.eval (List.ofFn x) = true) (hy : C.eval (List.ofFn y) = false) :
    ∃ k, reachable n C k ∧ (gateAt C k).op = GateOp.and ∧
      ∃ w ∈ (gateAt C k).inputs,
        (∃ u ∈ singletonSupport n C w, x u = true) ∧
        ∀ u ∈ singletonSupport n C w, y u = false := by
  have hwlt : C.output < n + C.gates.length := by
    by_contra! hh
    rw [eval_eq_val, val_ge (by simp : (List.ofFn x).length = n) hh] at hx
    cases hx
  have hreach : n ≤ C.output → reachable n C (C.output - n) := by
    intro hn
    exact ⟨by omega, Or.inl (by omega)⟩
  rcases reachable_difference_or_slot hm rb x y C.output hwlt hreach hx hy with hu | hs
  · simpa [hout] using hu
  · exact hs

lemma graph_actual_slot {n : ℕ} {C : Circuit} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (colour : Fin n → Bool) (hm : Monotone2 C) (rb : ReadsBack n C)
    (hcross : ∀ u v, G.Adj u v → colour u ≠ colour v)
    (hcorrect : ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
      decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true))
    (hmono : ∀ w u v, u ∈ singletonSupport n C w → v ∈ singletonSupport n C w →
      colour u = colour v)
    (a b : Fin n) (hab : G.Adj a b) :
    ∃ k, reachable n C k ∧ (gateAt C k).op = GateOp.and ∧
      ∃ w ∈ (gateAt C k).inputs, a ∈ singletonSupport n C w ∧
        ∀ u ∈ singletonSupport n C w, G.Adj u b := by
  classical
  let y : Fin n → Bool := fun u => decide (u = b ∨ colour u = colour a ∧ ¬ G.Adj u b)
  have hyb : y b = true := by simp [y]
  have hneg : C.eval (List.ofFn y) = false := by
    rw [hcorrect, decide_eq_false_iff_not]
    rintro ⟨u, v, huv, hu, hv⟩
    simp only [y, decide_eq_true_eq] at hu hv
    rcases hu with rfl | ⟨hu, hub⟩ <;> rcases hv with rfl | ⟨hv, hvb⟩
    · exact G.irrefl huv
    · exact hvb huv.symm
    · exact hub huv
    · exact hcross u v huv (hu.trans hv.symm)
  have hpos : C.eval (List.ofFn (pairInput a b)) = true := by
    rw [hcorrect, decide_eq_true_eq]
    exact ⟨a, b, hab, by simp [pairInput], by simp [pairInput]⟩
  have hout : singletonSupport n C C.output = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.2
    intro u hu
    have hv : C.eval (List.ofFn (pairInput u u)) = true := mem_support.1 hu
    rw [hcorrect, decide_eq_true_eq] at hv
    obtain ⟨v, w, hvw, hv, hw⟩ := hv
    have hvu : v = u := by simpa [pairInput] using hv
    have hwu : w = u := by simpa [pairInput] using hw
    subst v
    subst w
    exact G.irrefl hvw
  obtain ⟨k, hk, hop, w, hw, ⟨u, hu, hux⟩, hy⟩ :=
    reachable_distinguishing_and_operand hm rb (pairInput a b) y hout hpos hneg
  have hua : u = a := by
    have huab : u = a ∨ u = b := by simpa [pairInput] using hux
    rcases huab with he | he
    · exact he
    · subst u
      have hh := hy b hu
      rw [hyb] at hh
      cases hh
  subst u
  refine ⟨k, hk, hop, w, hw, hu, ?_⟩
  intro u hu'
  by_contra hnu
  have hyu : y u = true := by
    simp only [y, decide_eq_true_eq]
    exact Or.inr ⟨hmono w u a hu' hu, hnu⟩
  rw [hy u hu'] at hyu
  cases hyu

end PEqualNP.Outside.L_meta_4675.Reuse

namespace PEqualNP.Outside.L_meta_4675.FanoSanity

open PEqualNP.CircuitLowerBounds

def fanoEdges : Finset (Fin 7 × Fin 7) := {(0, 0), (0, 4), (0, 6), (1, 0), (1, 1), (1, 5), (2, 1), (2, 2), (2, 6), (3, 0), (3, 2), (3, 3), (4, 1), (4, 3), (4, 4), (5, 2), (5, 4), (5, 5), (6, 3), (6, 5), (6, 6)}

def fanoCircuit : Circuit :=
  ⟨[
    ⟨.or, [7, 11]⟩,
    ⟨.or, [14, 13]⟩,
    ⟨.and, [0, 15]⟩,
    ⟨.or, [7, 8]⟩,
    ⟨.or, [17, 12]⟩,
    ⟨.and, [1, 18]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.or, [20, 13]⟩,
    ⟨.and, [2, 21]⟩,
    ⟨.or, [7, 9]⟩,
    ⟨.or, [23, 10]⟩,
    ⟨.and, [3, 24]⟩,
    ⟨.or, [8, 10]⟩,
    ⟨.or, [26, 11]⟩,
    ⟨.and, [4, 27]⟩,
    ⟨.or, [9, 11]⟩,
    ⟨.or, [29, 12]⟩,
    ⟨.and, [5, 30]⟩,
    ⟨.or, [10, 12]⟩,
    ⟨.or, [32, 13]⟩,
    ⟨.and, [6, 33]⟩,
    ⟨.or, [16, 19]⟩,
    ⟨.or, [35, 22]⟩,
    ⟨.or, [36, 25]⟩,
    ⟨.or, [37, 28]⟩,
    ⟨.or, [38, 31]⟩,
    ⟨.or, [39, 34]⟩], 40⟩

def fanoExpression (x : Fin 14 → Bool) : Bool :=
  x 0 && (x 7 || x 11 || x 13) ||
  x 1 && (x 7 || x 8 || x 12) ||
  x 2 && (x 8 || x 9 || x 13) ||
  x 3 && (x 7 || x 9 || x 10) ||
  x 4 && (x 8 || x 10 || x 11) ||
  x 5 && (x 9 || x 11 || x 12) ||
  x 6 && (x 10 || x 12 || x 13)

set_option maxHeartbeats 2000000 in
lemma fano_isAO2 : PEqualNP.TopForm.IsAO2 14 fanoCircuit := by decide

lemma fano_edge_count : fanoEdges.card = 21 := by decide

lemma fano_size : fanoCircuit.size = 27 := by rfl

set_option maxHeartbeats 2000000 in
lemma fano_no_four_cycle :
    ∀ (a a' : Fin 7) (b b' : Fin 7), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ fanoEdges ∧ (a, b') ∈ fanoEdges ∧
        (a', b) ∈ fanoEdges ∧ (a', b') ∈ fanoEdges) := by decide

set_option maxHeartbeats 2000000 in
lemma fano_no_mixing :
    PEqualNP.TwoColour.tCount 14 fanoCircuit (fun i => decide (7 ≤ i)) = 0 := by decide

set_option maxHeartbeats 2000000 in
lemma fano_eval (x : Fin 14 → Bool) :
    PEqualNP.MetaComplexity.circuitFun 14 fanoCircuit x = fanoExpression x := by
  simp [PEqualNP.MetaComplexity.circuitFun, Circuit.eval, Circuit.wires, fanoCircuit,
    fanoExpression, GateOp.eval, List.ofFn_succ, Bool.or_assoc]

set_option maxHeartbeats 2000000 in
lemma fano_computes :
    ∀ x : Fin 14 → Bool, PEqualNP.MetaComplexity.circuitFun 14 fanoCircuit x =
      decide (∃ (a : Fin 7) (b : Fin 7), (a, b) ∈ fanoEdges ∧
        x (Fin.castAdd 7 a) = true ∧ x (Fin.natAdd 7 b) = true) := by
  intro x
  rw [fano_eval]
  simp [fanoExpression, fanoEdges, Fin.exists_fin_succ, Bool.and_or_distrib_left, Bool.or_assoc]

end PEqualNP.Outside.L_meta_4675.FanoSanity

namespace PEqualNP.Outside.L_meta_4675.MatchingSanity

lemma matching_cover_lower (p : ℕ) (S : Finset (Fin (p + p)))
    (h : ∀ a : Fin p, Fin.castAdd p a ∈ S ∨ Fin.natAdd p a ∈ S) :
    p ≤ S.card := by
  classical
  let f : Fin p → Fin (p + p) := fun a =>
    if Fin.castAdd p a ∈ S then Fin.castAdd p a else Fin.natAdd p a
  have hf : Function.Injective f := by
    intro a b hab
    have ha := a.isLt
    have hb := b.isLt
    apply Fin.ext
    dsimp [f] at hab
    split_ifs at hab <;>
      have hv := congrArg Fin.val hab <;>
      simp only [Fin.coe_castAdd, Fin.coe_natAdd] at hv <;>
      omega
  have hmem : ∀ a, f a ∈ S := by
    intro a
    dsimp [f]
    split_ifs with ha
    · exact ha
    · exact (h a).resolve_left ha
  have hs : Finset.univ.image f ⊆ S := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨a, _, rfl⟩
    exact hmem a
  have hc := Finset.card_le_card hs
  rw [Finset.card_image_of_injective _ hf] at hc
  simpa only [Finset.card_univ, Fintype.card_fin] using hc

end PEqualNP.Outside.L_meta_4675.MatchingSanity

namespace PEqualNP.Outside.L_meta_4675.FanoCleanLower

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
  PEqualNP.TopForm PEqualNP.Outside.L_meta_4675.FanoSanity

lemma diagonal_edges : ∀ a : Fin 7, (a, a) ∈ fanoEdges := by decide

lemma cover_lower (S : Finset (Fin 14))
    (hc : ∀ a b : Fin 7, (a, b) ∈ fanoEdges →
      Fin.castAdd 7 a ∈ S ∨ Fin.natAdd 7 b ∈ S) : 7 ≤ S.card := by
  exact PEqualNP.Outside.L_meta_4675.MatchingSanity.matching_cover_lower 7 S
    (fun a => hc a a (diagonal_edges a))

lemma clean_lower_bound (C : Circuit) (hao : IsAO2 14 C)
    (hcomp : ∀ x : Fin 14 → Bool, circuitFun 14 C x =
      decide (∃ (a : Fin 7) (b : Fin 7), (a, b) ∈ fanoEdges ∧
        x (Fin.castAdd 7 a) = true ∧ x (Fin.natAdd 7 b) = true))
    (hclean : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ x : Fin 14 → Bool, gateVal 14 C j x = true → circuitFun 14 C x = true) :
    27 ≤ C.size := by
  obtain ⟨S, hcover, hbudget⟩ :=
    PEqualNP.Outside.L_meta_4675.Reuse.clean_bound 7 7 fanoEdges C
      fano_no_four_cycle hao hcomp hclean
  have hS := cover_lower S hcover
  rw [fano_edge_count] at hbudget
  omega

lemma small_has_dirty (C : Circuit) (hao : IsAO2 14 C)
    (hcomp : ∀ x : Fin 14 → Bool, circuitFun 14 C x =
      decide (∃ (a : Fin 7) (b : Fin 7), (a, b) ∈ fanoEdges ∧
        x (Fin.castAdd 7 a) = true ∧ x (Fin.natAdd 7 b) = true))
    (hsize : C.size ≤ 26) :
    ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧
      ∃ x : Fin 14 → Bool, gateVal 14 C j x = true ∧ circuitFun 14 C x ≠ true := by
  classical
  by_contra h
  have hclean : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ x : Fin 14 → Bool, gateVal 14 C j x = true → circuitFun 14 C x = true := by
    intro j hj hop x hx
    by_contra hout
    exact h ⟨j, hj, hop, x, hx, hout⟩
  have hb := clean_lower_bound C hao hcomp hclean
  omega

end PEqualNP.Outside.L_meta_4675.FanoCleanLower
