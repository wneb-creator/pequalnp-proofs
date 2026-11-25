import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583

namespace GeneralGateBudget

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
      singletonSupport n C (n + k) = ∅ ∧
      ∃ a b, (gateAt C k).inputs = [a, b] ∧
        (singletonSupport n C a).Nonempty ∧ (singletonSupport n C b).Nonempty

lemma mem_births {n : ℕ} {C : Circuit} {k : ℕ} :
    k ∈ births n C ↔ reachable n C k ∧ (gateAt C k).op = GateOp.and ∧
      singletonSupport n C (n + k) = ∅ ∧
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

lemma gate_budget {n : ℕ} {C : Circuit} (hm : Monotone2 C) (rb : ReadsBack n C)
    :
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
    · obtain ⟨_, hop, hempty, a, b, hab, ha, hb'⟩ := mem_births.1 hb
      have hz := (hZ k).2 ⟨hk, hempty⟩
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
          obtain ⟨u, hu⟩ := hs
          rcases gate_op hm hr.1 with hop | hop
          · have hd : D k = ∅ := by
              apply Finset.eq_empty_iff_forall_notMem.2
              intro w hw
              have hw' := Finset.mem_filter.1 hw
              have hval := (val_and (by simp : (List.ofFn (pairInput u u)).length = n)
                hr.1 hop).1 (mem_support.1 hu) w (List.mem_toFinset.1 hw'.1)
              have huw : u ∈ singletonSupport n C w := mem_support.2 hval.2
              simpa [hw'.2.2] using huw
            simp [hb, hl, hz, hd]
          · obtain ⟨w, hw, huw⟩ := (support_or rb hr.1 hop u).1 hu
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

end GeneralGateBudget

namespace PurePointBudget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_2583.GeneralGateBudget

noncomputable def orPool {n : ℕ} (C : Circuit) (x : Fin n → Bool) (m : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range m).filter fun k => (gateAt C k).op = GateOp.or ∧
    1 < (singletonSupport n C (n + k)).card ∧ val C (List.ofFn x) (n + k) = false

lemma mem_orPool {n : ℕ} {C : Circuit} {x : Fin n → Bool} {m k : ℕ} :
    k ∈ orPool C x m ↔ k < m ∧ (gateAt C k).op = GateOp.or ∧
      1 < (singletonSupport n C (n + k)).card ∧ val C (List.ofFn x) (n + k) = false := by
  classical
  simp [orPool]

def complementInput {n : ℕ} (S : Finset (Fin n)) : Fin n → Bool :=
  fun p => decide (p ∉ S)

lemma support_subset_of_false {n : ℕ} {C : Circuit} (hm : Monotone2 C)
    {S : Finset (Fin n)} {w : ℕ} (hw : val C (List.ofFn (complementInput S)) w = false) :
    singletonSupport n C w ⊆ S := by
  intro p hp
  by_contra hnot
  have hle : ∀ i, pairInput p p i = true → complementInput S i = true := by
    intro i hi
    have hip : i = p := by simpa [pairInput] using hi
    simp [complementInput, hip, hnot]
  have ht := pair_mono hm hle w (mem_support.1 hp)
  rw [hw] at ht
  cases ht

lemma orPool_disjoint {n : ℕ} {C : Circuit} (hm : Monotone2 C)
    {S T : Finset (Fin n)} (hST : (S ∩ T).card ≤ 1) (m : ℕ) :
    Disjoint (orPool C (complementInput S) m) (orPool C (complementInput T) m) := by
  apply Finset.disjoint_left.2
  intro k hkS hkT
  obtain ⟨_, _, hlarge, hS⟩ := mem_orPool.1 hkS
  obtain ⟨_, _, _, hT⟩ := mem_orPool.1 hkT
  have hsub : singletonSupport n C (n + k) ⊆ S ∩ T :=
    Finset.subset_inter (support_subset_of_false hm hS) (support_subset_of_false hm hT)
  have hcard := (Finset.card_le_card hsub).trans hST
  omega

end PurePointBudget

namespace MergeFrontier

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership GeneralGateBudget

noncomputable def pool {n : ℕ} (C : Circuit) (x : Fin n → Bool) (m : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range m).filter fun k => reachable n C k ∧
    (gateAt C k).op = GateOp.or ∧ 1 < (singletonSupport n C (n+k)).card ∧
    1 < (positiveInputs n C k).card ∧ val C (List.ofFn x) (n+k) = false

lemma mem_pool {n : ℕ} {C : Circuit} {x : Fin n → Bool} {m k : ℕ} :
    k ∈ pool C x m ↔ k < m ∧ reachable n C k ∧
      (gateAt C k).op = GateOp.or ∧ 1 < (singletonSupport n C (n+k)).card ∧
      1 < (positiveInputs n C k).card ∧ val C (List.ofFn x) (n+k) = false := by
  classical
  simp [pool]

lemma frontier_budget {n : ℕ} {C : Circuit} (hm : Monotone2 C) (rb : ReadsBack n C)
    (x : Fin n → Bool) (m : ℕ) (roots : Finset ℕ)
    (hvalid : ∀ w ∈ roots, w < n + C.gates.length)
    (hfalse : ∀ w ∈ roots, val C (List.ofFn x) w = false)
    (hreach : ∀ w ∈ roots, n ≤ w → reachable n C (w-n))
    (hbound : ∀ w ∈ roots, 1 < (singletonSupport n C w).card → w < n + m) :
    (roots.biUnion (singletonSupport n C)).card ≤ roots.card + (pool C x m).card := by
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
      _ = _ := by simp [pool]
  | succ m ih =>
    have hpool : pool C x m ⊆ pool C x (m + 1) := by
      intro k hk
      obtain ⟨hk, hh⟩ := mem_pool.1 hk
      exact mem_pool.2 ⟨by omega, hh⟩
    by_cases htop : n + m ∈ roots ∧ 1 < (singletonSupport n C (n + m)).card
    · obtain ⟨hmem, hlarge⟩ := htop
      have hmC : m < C.gates.length := by have := hvalid _ hmem; omega
      rcases gate_op hm hmC with hand | hor
      · have hex : ∃ a ∈ (gateAt C m).inputs, val C (List.ofFn x) a = false := by
          by_contra! h
          have ht : val C (List.ofFn x) (n + m) = true :=
            (val_and (by simp) hmC hand).2 fun a ha =>
              ⟨rb m hmC a ha, Bool.eq_true_of_not_eq_false (h a ha)⟩
          rw [hfalse _ hmem] at ht
          cases ht
        obtain ⟨a, ha, hfa⟩ := hex
        let T := roots.erase (n + m) ∪ {a}
        have haback : a < n + m := rb m hmC a ha
        have hTvalid : ∀ w ∈ T, w < n + C.gates.length := by
          intro w hw
          rcases Finset.mem_union.1 hw with hw | hw
          · exact hvalid _ (Finset.mem_of_mem_erase hw)
          · have : w = a := Finset.mem_singleton.1 hw
            omega
        have hTfalse : ∀ w ∈ T, val C (List.ofFn x) w = false := by
          intro w hw
          rcases Finset.mem_union.1 hw with hw | hw
          · exact hfalse _ (Finset.mem_of_mem_erase hw)
          · simpa only [Finset.mem_singleton.1 hw] using hfa
        have hTreach : ∀ w ∈ T, n ≤ w → reachable n C (w-n) := by
          intro w hw hn
          rcases Finset.mem_union.mp hw with hw | hw
          · exact hreach w (Finset.mem_of_mem_erase hw) hn
          · have he : w = a := Finset.mem_singleton.mp hw
            have htopreach : reachable n C m := by
              simpa using hreach (n+m) hmem (by omega)
            subst w
            have heq : n + (a-n) = a := by omega
            apply reachable_child rb htopreach
            simpa only [heq] using ha
        have hTbound : ∀ w ∈ T, 1 < (singletonSupport n C w).card → w < n + m := by
          intro w hw hcard
          rcases Finset.mem_union.1 hw with hw | hw
          · have hlt := hbound w (Finset.mem_of_mem_erase hw) hcard
            have hne := (Finset.mem_erase.1 hw).1
            omega
          · have : w = a := Finset.mem_singleton.1 hw
            omega
        have hsub : roots.biUnion (singletonSupport n C) ⊆ T.biUnion (singletonSupport n C) := by
          intro u hu
          obtain ⟨w, hw, huw⟩ := Finset.mem_biUnion.1 hu
          by_cases he : w = n + m
          · subst w
            have hua : u ∈ singletonSupport n C a := mem_support.2
              ((val_and (by simp) hmC hand).1 (mem_support.1 huw) a ha).2
            exact Finset.mem_biUnion.2 ⟨a, Finset.mem_union_right _ (Finset.mem_singleton_self _), hua⟩
          · exact Finset.mem_biUnion.2 ⟨w, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨he, hw⟩), huw⟩
        have hfirst := (Finset.card_le_card hsub).trans (ih T hTvalid hTfalse hTreach hTbound)
        have hTcard := Finset.card_union_le (roots.erase (n + m)) {a}
        have herase := Finset.card_erase_add_one hmem
        have hinc := Finset.card_le_card hpool
        simp only [Finset.card_singleton] at hTcard
        change T.card ≤ (roots.erase (n + m)).card + 1 at hTcard
        omega
      · let P := positiveInputs n C m
        let T := roots.erase (n + m) ∪ P
        have hback : ∀ w ∈ P, w < n + m :=
          fun w hw => rb m hmC w (mem_positiveInputs.1 hw).1
        have hTvalid : ∀ w ∈ T, w < n + C.gates.length := by
          intro w hw
          rcases Finset.mem_union.1 hw with hw | hw
          · exact hvalid _ (Finset.mem_of_mem_erase hw)
          · have := hback w hw
            omega
        have hTfalse : ∀ w ∈ T, val C (List.ofFn x) w = false := by
          intro w hw
          rcases Finset.mem_union.1 hw with hw | hw
          · exact hfalse _ (Finset.mem_of_mem_erase hw)
          · cases hf : val C (List.ofFn x) w with
            | false => rfl
            | true =>
              have ht : val C (List.ofFn x) (n + m) = true :=
                (val_or (by simp) hmC hor).2
                  ⟨w, (mem_positiveInputs.1 hw).1, hback w hw, hf⟩
              rw [hfalse _ hmem] at ht
              cases ht
        have hTreach : ∀ w ∈ T, n ≤ w → reachable n C (w-n) := by
          intro w hw hn
          rcases Finset.mem_union.mp hw with hw | hw
          · exact hreach w (Finset.mem_of_mem_erase hw) hn
          · have htopreach : reachable n C m := by
              simpa using hreach (n+m) hmem (by omega)
            have heq : n + (w-n) = w := by omega
            apply reachable_child rb htopreach
            simpa only [heq] using (mem_positiveInputs.mp hw).1
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
            obtain ⟨a, ha, hua⟩ := (support_or rb hmC hor u).1 huw
            exact Finset.mem_biUnion.2 ⟨a, Finset.mem_union_right _
              (mem_positiveInputs.2 ⟨ha, u, hua⟩), hua⟩
          · exact Finset.mem_biUnion.2 ⟨w, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨he, hw⟩), huw⟩
        have hfirst := (Finset.card_le_card hsub).trans (ih T hTvalid hTfalse hTreach hTbound)
        have hTcard := Finset.card_union_le (roots.erase (n + m)) P
        have herase := Finset.card_erase_add_one hmem
        have hPc : P.card ≤ 2 := (Finset.card_filter_le _ _).trans (input_card hm hmC)
        by_cases hpos : 1 < P.card
        · have htopreach : reachable n C m := by
            simpa using hreach (n+m) hmem (by omega)
          have hnew : m ∈ pool C x (m+1) :=
            mem_pool.mpr ⟨by omega, htopreach, hor, hlarge, hpos, hfalse _ hmem⟩
          have hn : m ∉ pool C x m := fun h => (Nat.lt_irrefl m) (mem_pool.mp h).1
          have hsubpool : insert m (pool C x m) ⊆ pool C x (m+1) :=
            Finset.insert_subset_iff.mpr ⟨hnew, hpool⟩
          have hinc := Finset.card_le_card hsubpool
          rw [Finset.card_insert_of_notMem hn] at hinc
          change T.card ≤ (roots.erase (n+m)).card + P.card at hTcard
          omega
        · have hinc := Finset.card_le_card hpool
          change T.card ≤ (roots.erase (n+m)).card + P.card at hTcard
          omega

    · have hnew : ∀ w ∈ roots, 1 < (singletonSupport n C w).card → w < n + m := by
        intro w hw hw'
        have hlt := hbound w hw hw'
        have hne : w ≠ n + m := fun he => htop ⟨he ▸ hw, he ▸ hw'⟩
        omega
      have hfirst := ih roots hvalid hfalse hreach hnew
      have hinc := Finset.card_le_card hpool
      omega

lemma pool_subset_orPool {n : ℕ} (C : Circuit) (x : Fin n → Bool) (m : ℕ) :
    pool C x m ⊆ PurePointBudget.orPool C x m := by
  intro k hk
  obtain ⟨hkm, _, hop, hlarge, _, hf⟩ := mem_pool.mp hk
  exact PurePointBudget.mem_orPool.mpr ⟨hkm, hop, hlarge, hf⟩

lemma pool_subset_merges {n : ℕ} (C : Circuit) (x : Fin n → Bool) (m : ℕ) :
    pool C x m ⊆ GeneralGateBudget.merges n C := by
  intro k hk
  obtain ⟨_, hr, hop, hlarge, hpos, _⟩ := mem_pool.mp hk
  exact GeneralGateBudget.mem_merges.mpr ⟨hr, hop, hlarge, hpos⟩

lemma multi_frontier_merge_budget {n : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] {C : Circuit}
    (hm : Monotone2 C) (rb : ReadsBack n C)
    (U S : ι → Finset (Fin n)) (roots : ι → Finset ℕ)
    (hroot : ∀ i w, w ∈ roots i → w < n + C.gates.length)
    (hreach : ∀ i w, w ∈ roots i → n ≤ w → reachable n C (w-n))
    (hfalse : ∀ i w, w ∈ roots i →
      val C (List.ofFn (PurePointBudget.complementInput (U i))) w = false)
    (hcovered : ∀ i, S i ⊆ (roots i).biUnion (singletonSupport n C))
    (hpair : ∀ i j, i ≠ j → (U i ∩ U j).card ≤ 1) :
    (∑ i, (S i).card) ≤ (∑ i, (roots i).card) + (GeneralGateBudget.merges n C).card := by
  classical
  let pools := fun i => pool C (PurePointBudget.complementInput (U i)) C.gates.length
  have hind (i : ι) : (S i).card ≤ (roots i).card + (pools i).card := by
    apply (Finset.card_le_card (hcovered i)).trans
    apply frontier_budget hm rb (PurePointBudget.complementInput (U i)) C.gates.length
      (roots i) (hroot i) (hfalse i) (hreach i)
    intro w hw _
    exact hroot i w hw
  have hdis : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint pools := by
    intro i _ j _ hij
    exact (PurePointBudget.orPool_disjoint hm (hpair i j hij) C.gates.length).mono
      (pool_subset_orPool _ _ _) (pool_subset_orPool _ _ _)
  have hsub : Finset.univ.biUnion pools ⊆ GeneralGateBudget.merges n C := by
    intro k hk
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hk
    exact pool_subset_merges _ _ _ hi
  calc
    _ ≤ ∑ i, ((roots i).card + (pools i).card) := Finset.sum_le_sum fun i _ => hind i
    _ = (∑ i, (roots i).card) + (Finset.univ.biUnion pools).card := by
      rw [Finset.sum_add_distrib, Finset.card_biUnion hdis]
    _ ≤ _ := Nat.add_le_add_left (Finset.card_le_card hsub) _

lemma covered_edges_and_centers_budget {n : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] {C : Circuit}
    (hm : Monotone2 C) (rb : ReadsBack n C)
    (U S : ι → Finset (Fin n)) (roots : ι → Finset ℕ)
    (hroot : ∀ i w, w ∈ roots i → w < n + C.gates.length)
    (hreach : ∀ i w, w ∈ roots i → n ≤ w → reachable n C (w-n))
    (hfalse : ∀ i w, w ∈ roots i →
      val C (List.ofFn (PurePointBudget.complementInput (U i))) w = false)
    (hcovered : ∀ i, S i ⊆ (roots i).biUnion (singletonSupport n C))
    (hpair : ∀ i j, i ≠ j → (U i ∩ U j).card ≤ 1)
    (edgeCount : ℕ)
    (hcover : edgeCount ≤ ∑ i, (S i).card)
    (hroots : (∑ i, (roots i).card) ≤ (GeneralGateBudget.births n C).card)
    (hcenters : Fintype.card ι ≤ (GeneralGateBudget.births n C).card) :
    edgeCount + Fintype.card ι - 1 ≤ C.size := by
  have hfrontier := multi_frontier_merge_budget hm rb U S roots hroot hreach hfalse
    hcovered hpair
  have hbudget := GeneralGateBudget.gate_budget hm rb
  omega

end MergeFrontier

namespace SeparatedOperands

variable {P L : Type*}

def Separates (f : (P → Bool) → (L → Bool) → Bool) : Prop :=
  ∀ x y, f x y = (f x (fun _ => false) || f (fun _ => false) y)

def Mono (f : (P → Bool) → (L → Bool) → Bool) : Prop :=
  ∀ x x' y y', (∀ p, x p = true → x' p = true) →
    (∀ l, y l = true → y' l = true) → f x y = true → f x' y' = true

def PurePoint (f : (P → Bool) → (L → Bool) → Bool) : Prop :=
  ∀ x y, f x y = f x (fun _ => false)

def PureLine (f : (P → Bool) → (L → Bool) → Bool) : Prop :=
  ∀ x y, f x y = f (fun _ => false) y

lemma pure_point_of_false_line_max
    (f : (P → Bool) → (L → Bool) → Bool) (hs : Separates f) (hm : Mono f)
    (hmax : f (fun _ => false) (fun _ => true) = false) : PurePoint f := by
  intro x y
  have hy : f (fun _ => false) y = false := by
    cases he : f (fun _ => false) y
    · rfl
    · have ht := hm (fun _ => false) (fun _ => false) y (fun _ => true)
        (fun _ h => h) (fun _ _ => rfl) he
      rw [hmax] at ht
      cases ht
  rw [hs x y, hy, Bool.or_false]

lemma pure_line_of_false_point_max
    (f : (P → Bool) → (L → Bool) → Bool) (hs : Separates f) (hm : Mono f)
    (hmax : f (fun _ => true) (fun _ => false) = false) : PureLine f := by
  intro x y
  have hx : f x (fun _ => false) = false := by
    cases he : f x (fun _ => false)
    · rfl
    · have ht := hm x (fun _ => true) (fun _ => false) (fun _ => false)
        (fun _ _ => rfl) (fun _ h => h) he
      rw [hmax] at ht
      cases ht
  rw [hs x y, hx, Bool.false_or]

lemma clean_separated_operands_opposite
    (f g : (P → Bool) → (L → Bool) → Bool)
    (hsf : Separates f) (hsg : Separates g) (hmf : Mono f) (hmg : Mono g)
    (hpoints : (f (fun _ => true) (fun _ => false) &&
      g (fun _ => true) (fun _ => false)) = false)
    (hlines : (f (fun _ => false) (fun _ => true) &&
      g (fun _ => false) (fun _ => true)) = false)
    (huse : ∃ x y, f x y = true ∧ g x y = true) :
    (PurePoint f ∧ PureLine g) ∨ (PureLine f ∧ PurePoint g) := by
  obtain ⟨x, y, hf, hg⟩ := huse
  cases hp : f (fun _ => true) (fun _ => false)
  · have hfl := pure_line_of_false_point_max f hsf hmf hp
    have hflmax : f (fun _ => false) (fun _ => true) = true := by
      apply hmf (fun _ => false) (fun _ => false) y (fun _ => true)
        (fun _ h => h) (fun _ _ => rfl)
      simpa only [hfl x y] using hf
    have hglmax : g (fun _ => false) (fun _ => true) = false := by
      simpa only [hflmax, Bool.true_and] using hlines
    exact Or.inr ⟨hfl, pure_point_of_false_line_max g hsg hmg hglmax⟩
  · have hgpmax : g (fun _ => true) (fun _ => false) = false := by
      simpa only [hp, Bool.true_and] using hpoints
    have hgl := pure_line_of_false_point_max g hsg hmg hgpmax
    have hglmax : g (fun _ => false) (fun _ => true) = true := by
      apply hmg (fun _ => false) (fun _ => false) y (fun _ => true)
        (fun _ h => h) (fun _ _ => rfl)
      simpa only [hgl x y] using hg
    have hflmax : f (fun _ => false) (fun _ => true) = false := by
      simpa only [hglmax, Bool.and_true] using hlines
    exact Or.inl ⟨pure_point_of_false_line_max f hsf hmf hflmax, hgl⟩

end SeparatedOperands

namespace MonochromaticTopBridge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm GeneralGateBudget SeparatedOperands

def wireFn {n : ℕ} (P : Finset (Fin n)) (C : Circuit) (w : ℕ)
    (x y : Fin n → Bool) : Bool :=
  val C (List.ofFn fun v => if v ∈ P then x v else y v) w

lemma wire_mono {n : ℕ} (P : Finset (Fin n)) (C : Circuit) (hm : Monotone2 C) (w : ℕ) :
    Mono (wireFn P C w) := by
  intro x x' y y' hx hy
  apply pair_mono hm
  intro v hv
  by_cases hp : v ∈ P
  · simpa only [hp, ite_true] using hx v (by simpa only [hp, ite_true] using hv)
  · simpa only [hp, ite_false] using hy v (by simpa only [hp, ite_false] using hv)

lemma pure_separates {P L : Type*} (f : (P → Bool) → (L → Bool) → Bool)
    (hm : Mono f) (hp : PurePoint f ∨ PureLine f) : Separates f := by
  intro x y
  rcases hp with hp | hp
  · rw [hp x y, hp (fun _ => false) y]
    cases h0 : f (fun _ => false) (fun _ => false)
    · simp
    · have hx := hm (fun _ => false) x (fun _ => false) (fun _ => false)
        (fun _ h => Bool.noConfusion h) (fun _ h => h) h0
      simp [hx]
  · rw [hp x y, hp x (fun _ => false)]
    cases h0 : f (fun _ => false) (fun _ => false)
    · simp
    · have hy := hm (fun _ => false) (fun _ => false) (fun _ => false) y
        (fun _ h => h) (fun _ h => Bool.noConfusion h) h0
      simp [hy]

lemma or_separates {P L : Type*} (f g : (P → Bool) → (L → Bool) → Bool)
    (hf : Separates f) (hg : Separates g) : Separates (fun x y => f x y || g x y) := by
  intro x y
  change (f x y || g x y) =
    ((f x (fun _ => false) || g x (fun _ => false)) ||
      (f (fun _ => false) y || g (fun _ => false) y))
  rw [hf x y, hg x y]
  cases f x (fun _ => false) <;> cases f (fun _ => false) y <;>
    cases g x (fun _ => false) <;> cases g (fun _ => false) y <;> rfl

lemma input_separates {n : ℕ} (P : Finset (Fin n)) (C : Circuit) (w : ℕ) (hw : w < n) :
    Separates (wireFn P C w) := by
  intro x y
  have hv (a b : Fin n → Bool) : wireFn P C w a b =
      (if (⟨w,hw⟩ : Fin n) ∈ P then a ⟨w,hw⟩ else b ⟨w,hw⟩) := by
    exact val_ofFn C _ ⟨w,hw⟩
  simp only [hv]
  split <;> simp

lemma ao_mono {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) : Monotone2 C := by
  intro g hg
  exact ⟨by simpa using hAO.1 g hg, (hAO.2.2 g hg).le⟩

lemma list_two {α : Type*} {l : List α} (h : l.length = 2) : ∃ a b, l = [a,b] := by
  cases l with
  | nil => simp at h
  | cons a t =>
    cases t with
    | nil => simp at h
    | cons b t =>
      cases t with
      | nil => exact ⟨a,b,rfl⟩
      | cons c t => simp at h

lemma two_inputs {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (k : ℕ) (hk : k < C.gates.length) :
    ∃ a b, (gateAt C k).inputs = [a,b] ∧ a < n+k ∧ b < n+k := by
  have hl : (gateAt C k).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hk)
  obtain ⟨a,b,hab⟩ := list_two hl
  exact ⟨a,b,hab,hAO.2.1 k hk a (by simp [hab]),hAO.2.1 k hk b (by simp [hab])⟩

lemma wire_or {n : ℕ} (P : Finset (Fin n)) (C : Circuit)
    (k a b : ℕ) (hk : k < C.gates.length) (hop : (gateAt C k).op = .or)
    (hab : (gateAt C k).inputs = [a,b]) (ha : a < n+k) (hb : b < n+k) :
    wireFn P C (n+k) = fun x y => wireFn P C a x y || wireFn P C b x y := by
  funext x y
  unfold wireFn
  rw [val_gate (by simp) hk, hop, hab]
  simp [GateOp.eval,ha,hb]

lemma ancestors_separate {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P : Finset (Fin n)) (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C)
    (hdirty : ∀ k < C.gates.length, (gateAt C k).op = .and → ¬ BelowF G C k →
      Separates (wireFn P C (n+k)))
    (j : ℕ) (hj : j < C.gates.length) (hjop : (gateAt C j).op = .and) :
    ∀ w, w < n+j → (n ≤ w → InCone n C (w-n) j) → Separates (wireFn P C w) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hc
    by_cases hin : w < n
    · exact input_separates P C w hin
    obtain ⟨k,rfl⟩ : ∃ k, w = n+k := ⟨w-n,by omega⟩
    have hk : k < C.gates.length := by omega
    have hcone : InCone n C k j := by simpa using hc (by omega)
    rcases gate_op (ao_mono hAO) hk with hop | hop
    · apply hdirty k hk hop
      intro hbelow
      exact hTop k hk j hj hop hbelow hjop hcone
    · obtain ⟨a,b,hab,ha,hb⟩ := two_inputs hAO k hk
      have hchild (u : ℕ) (hu : u ∈ (gateAt C k).inputs) (hnu : n ≤ u) :
          InCone n C (u-n) j := by
        have hback := hAO.2.1 k hk u hu
        have he : n+(u-n)=u := by omega
        have huc : InCone n C (u-n) k := (inCone_iff n C (u-n) k).mpr
          ⟨hk,u-n,by omega,by simpa only [he] using hu,Or.inl rfl⟩
        exact inCone_trans n C (u-n) k huc j hcone
      have hsa := ih a ha (by omega) (hchild a (by simp [hab]))
      have hsb := ih b hb (by omega) (hchild b (by simp [hab]))
      rw [wire_or P C k a b hk hop hab ha hb]
      exact or_separates _ _ hsa hsb

lemma operand_separates {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P : Finset (Fin n)) (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C)
    (hdirty : ∀ k < C.gates.length, (gateAt C k).op = .and → ¬ BelowF G C k →
      Separates (wireFn P C (n+k)))
    (j : ℕ) (hj : j < C.gates.length) (hjop : (gateAt C j).op = .and)
    (w : ℕ) (hw : w ∈ (gateAt C j).inputs) : Separates (wireFn P C w) := by
  apply ancestors_separate G P C hAO hTop hdirty j hj hjop w (hAO.2.1 j hj w hw)
  intro hn
  have he : n+(w-n)=w := by omega
  apply (inCone_iff n C (w-n) j).mpr
  refine ⟨hj,w-n,by have := hAO.2.1 j hj w hw; omega,?_,Or.inl rfl⟩
  simpa only [he] using hw

lemma wire_and {n : ℕ} (P : Finset (Fin n)) (C : Circuit)
    (k a b : ℕ) (hk : k < C.gates.length) (hop : (gateAt C k).op = .and)
    (hab : (gateAt C k).inputs = [a,b]) (ha : a < n+k) (hb : b < n+k) :
    wireFn P C (n+k) = fun x y => wireFn P C a x y && wireFn P C b x y := by
  funext x y
  unfold wireFn
  rw [val_gate (by simp) hk, hop, hab]
  simp [GateOp.eval,ha,hb]

lemma bipartite_masks_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P : Finset (Fin n))
    (hbip : ∀ u v, G.Adj u v → (u ∈ P ↔ v ∉ P)) :
    graphFun G ∅ (fun v => if v ∈ P then true else false) = false ∧
    graphFun G ∅ (fun v => if v ∈ P then false else true) = false := by
  constructor
  · by_contra hf
    have ht := Bool.eq_true_of_not_eq_false hf
    obtain ⟨u,v,huv,hu,hv⟩ : ∃ u v, G.Adj u v ∧ u ∈ P ∧ v ∈ P := by
      simpa [graphFun] using ht
    exact (hbip u v huv).mp hu hv
  · by_contra hf
    have ht := Bool.eq_true_of_not_eq_false hf
    obtain ⟨u,v,huv,hu,hv⟩ : ∃ u v, G.Adj u v ∧ u ∉ P ∧ v ∉ P := by
      simpa [graphFun] using ht
    exact hu ((hbip u v huv).mpr hv)

lemma below_rejects {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : ℕ) (hb : BelowF G C j) (x : Fin n → Bool)
    (hf : graphFun G ∅ x = false) : val C (List.ofFn x) (n+j) = false := by
  cases he : val C (List.ofFn x) (n+j)
  · rfl
  · have ht := hb x (by simpa only [gateVal_eq_val] using he)
    rw [hf] at ht
    cases ht

lemma useful_top_operands_opposite {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P : Finset (Fin n)) (C : Circuit) (hAO : IsAO2 n C)
    (hbip : ∀ u v, G.Adj u v → (u ∈ P ↔ v ∉ P))
    (hsep : ∀ k < C.gates.length, (gateAt C k).op = .and →
      ∀ w ∈ (gateAt C k).inputs, Separates (wireFn P C w))
    (j a b : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = .and)
    (hab : (gateAt C j).inputs = [a,b]) (hbelow : BelowF G C j)
    (huse : ∃ x : Fin n → Bool, gateVal n C j x = true) :
    (PurePoint (wireFn P C a) ∧ PureLine (wireFn P C b)) ∨
    (PureLine (wireFn P C a) ∧ PurePoint (wireFn P C b)) := by
  have ha : a < n+j := hAO.2.1 j hj a (by simp [hab])
  have hb : b < n+j := hAO.2.1 j hj b (by simp [hab])
  have hfn := wire_and P C j a b hj hop hab ha hb
  have hsepA := hsep j hj hop a (by simp [hab])
  have hsepB := hsep j hj hop b (by simp [hab])
  obtain ⟨hpoint, hline⟩ := bipartite_masks_false G P hbip
  apply clean_separated_operands_opposite _ _ hsepA hsepB
    (wire_mono P C (ao_mono hAO) a) (wire_mono P C (ao_mono hAO) b)
  · have h := below_rejects G C j hbelow _ hpoint
    change wireFn P C (n+j) (fun _ => true) (fun _ => false) = false at h
    simpa only [hfn] using h
  · have h := below_rejects G C j hbelow _ hline
    change wireFn P C (n+j) (fun _ => false) (fun _ => true) = false at h
    simpa only [hfn] using h
  · obtain ⟨x,hx⟩ := huse
    have hw : wireFn P C (n+j) x x = true := by
      simpa [wireFn, gateVal_eq_val] using hx
    rw [hfn] at hw
    exact ⟨x,x,by simpa using hw⟩

lemma point_operand_false_complement {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P : Finset (Fin n)) (C : Circuit) (hAO : IsAO2 n C)
    (hbip : ∀ u v, G.Adj u v → (u ∈ P ↔ v ∉ P))
    (j a b : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = .and)
    (hinputs : ∀ w ∈ (gateAt C j).inputs, w = a ∨ w = b) (hbelow : BelowF G C j)
    (hpure : PurePoint (wireFn P C a)) (c : Fin n) (hc : c ∉ P)
    (hcenter : c ∈ singletonSupport n C b) :
    val C (List.ofFn (PurePointBudget.complementInput
      (Finset.univ.filter fun v => G.Adj c v))) a = false := by
  classical
  let U : Finset (Fin n) := Finset.univ.filter fun v => G.Adj c v
  let x : Fin n → Bool := PurePointBudget.complementInput U
  change val C (List.ofFn x) a = false
  by_contra hf
  have ha := Bool.eq_true_of_not_eq_false hf
  let z : Fin n → Bool := fun v => if v ∈ P then x v else pairInput c c v
  have haz : val C (List.ofFn z) a = true := by
    change wireFn P C a x (pairInput c c) = true
    rw [hpure x (pairInput c c), ← hpure x x]
    simpa [wireFn] using ha
  have hcz : ∀ v, pairInput c c v = true → z v = true := by
    intro v hv
    have he : v = c := by simpa [pairInput] using hv
    subst v
    simp [z,hc,pairInput]
  have hbz := pair_mono (ao_mono hAO) hcz b (mem_support.mp hcenter)
  have ht : val C (List.ofFn z) (n+j) = true := by
    apply (val_and (by simp) hj hop).mpr
    intro w hw
    have hback := hAO.2.1 j hj w hw
    rcases hinputs w hw with rfl | rfl
    · exact ⟨hback,haz⟩
    · exact ⟨hback,hbz⟩
  have hgraph := hbelow z (by simpa only [gateVal_eq_val] using ht)
  obtain ⟨u,v,huv,hu,hv⟩ : ∃ u v, G.Adj u v ∧ z u = true ∧ z v = true := by
    simpa [graphFun] using hgraph
  by_cases huP : u ∈ P
  · have hvP : v ∉ P := (hbip u v huv).mp huP
    have hvc : v = c := by simpa [z,hvP,pairInput] using hv
    have huc : ¬ G.Adj c u := by
      simpa [z,huP,x,PurePointBudget.complementInput,U] using hu
    subst v
    exact huc huv.symm
  · have hvP : v ∈ P := by
      by_contra hvP
      exact huP ((hbip u v huv).mpr hvP)
    have huc : u = c := by simpa [z,huP,pairInput] using hu
    have hvc : ¬ G.Adj c v := by
      simpa [z,hvP,x,PurePointBudget.complementInput,U] using hv
    subst u
    exact hvc huv

lemma zero_wire {n : ℕ} (C : Circuit) (hAO : IsAO2 n C) :
    ∀ w, w < n+C.gates.length → val C (List.ofFn (fun _ : Fin n => false)) w = false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hin : w < n
    · simpa using (val_input (C := C) (x := List.ofFn (fun _ : Fin n => false)) (by simp) hin)
    obtain ⟨k,rfl⟩ : ∃ k, w=n+k := ⟨w-n,by omega⟩
    have hk : k < C.gates.length := by omega
    obtain ⟨a,b,hab,ha,hb⟩ := two_inputs hAO k hk
    have hfa := ih a ha (by omega)
    have hfb := ih b hb (by omega)
    change wireFn (∅ : Finset (Fin n)) C (n+k) (fun _ => false) (fun _ => false) = false
    rcases gate_op (ao_mono hAO) hk with hop | hop
    · rw [wire_and ∅ C k a b hk hop hab ha hb]
      simp only [wireFn,ite_self,hfa,hfb]
      rfl
    · rw [wire_or ∅ C k a b hk hop hab ha hb]
      simp only [wireFn,ite_self,hfa,hfb]
      rfl

lemma pure_point_support {n : ℕ} (P : Finset (Fin n)) (C : Circuit) (hAO : IsAO2 n C)
    (w : ℕ) (hw : w < n+C.gates.length) (hpure : PurePoint (wireFn P C w)) :
    singletonSupport n C w ⊆ P := by
  intro u hu
  by_contra huP
  have he : (fun v => if v ∈ P then pairInput u u v else false) =
      (fun _ : Fin n => false) := by
    funext v
    by_cases hv : v = u
    · subst v
      simp [huP]
    · simp [pairInput,hv]
  have hh := hpure (pairInput u u) (pairInput u u)
  have ht := mem_support.mp hu
  have hz := zero_wire C hAO w hw
  simp only [wireFn,ite_self] at hh
  rw [he,hz] at hh
  rw [hh] at ht
  cases ht

lemma wireFn_compl {n : ℕ} (P : Finset (Fin n)) (C : Circuit) (w : ℕ)
    (x y : Fin n → Bool) : wireFn Pᶜ C w x y = wireFn P C w y x := by
  unfold wireFn
  congr 2
  funext v
  by_cases hv : v ∈ P <;> simp [hv]

lemma pure_line_compl {n : ℕ} (P : Finset (Fin n)) (C : Circuit) (w : ℕ)
    (h : PureLine (wireFn P C w)) : PurePoint (wireFn Pᶜ C w) := by
  intro x y
  simp only [wireFn_compl]
  exact h y x

lemma pure_point_compl {n : ℕ} (P : Finset (Fin n)) (C : Circuit) (w : ℕ)
    (h : PurePoint (wireFn P C w)) : PureLine (wireFn Pᶜ C w) := by
  intro x y
  simp only [wireFn_compl]
  exact h y x

lemma bipartite_compl {n : ℕ} (G : SimpleGraph (Fin n)) (P : Finset (Fin n))
    (h : ∀ u v, G.Adj u v → (u ∈ P ↔ v ∉ P)) :
    ∀ u v, G.Adj u v → (u ∈ Pᶜ ↔ v ∉ Pᶜ) := by
  intro u v huv
  simpa using not_congr (h u v huv)

lemma pure_line_support {n : ℕ} (P : Finset (Fin n)) (C : Circuit) (hAO : IsAO2 n C)
    (w : ℕ) (hw : w < n+C.gates.length) (hpure : PureLine (wireFn P C w)) :
    singletonSupport n C w ⊆ Pᶜ :=
  pure_point_support Pᶜ C hAO w hw (pure_line_compl P C w hpure)

lemma line_operand_false_complement {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P : Finset (Fin n)) (C : Circuit) (hAO : IsAO2 n C)
    (hbip : ∀ u v, G.Adj u v → (u ∈ P ↔ v ∉ P))
    (j a b : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = .and)
    (hinputs : ∀ w ∈ (gateAt C j).inputs, w = a ∨ w = b) (hbelow : BelowF G C j)
    (hpure : PureLine (wireFn P C a)) (c : Fin n) (hc : c ∈ P)
    (hcenter : c ∈ singletonSupport n C b) :
    val C (List.ofFn (PurePointBudget.complementInput
      (Finset.univ.filter fun v => G.Adj c v))) a = false := by
  exact point_operand_false_complement G Pᶜ C hAO (bipartite_compl G P hbip)
    j a b hj hop hinputs hbelow (pure_line_compl P C a hpure) c (by simpa) hcenter

lemma pure_top_guard {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P : Finset (Fin n)) (C : Circuit) (hAO : IsAO2 n C)
    (hbip : ∀ u v, G.Adj u v → (u ∈ P ↔ v ∉ P))
    (j s w : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = .and)
    (hpair : (gateAt C j).inputs = [s,w] ∨ (gateAt C j).inputs = [w,s])
    (hbelow : BelowF G C j)
    (hopposite : (PurePoint (wireFn P C s) ∧ PureLine (wireFn P C w)) ∨
      (PureLine (wireFn P C s) ∧ PurePoint (wireFn P C w)))
    (c : Fin n) (hcenter : c ∈ singletonSupport n C s) :
    val C (List.ofFn (PurePointBudget.complementInput
      (Finset.univ.filter fun v => G.Adj c v))) w = false := by
  have hinputs : ∀ a ∈ (gateAt C j).inputs, a = w ∨ a = s := by
    intro a ha
    rcases hpair with h | h <;> simp [h] at ha
    · exact ha.symm
    · exact ha
  have hs : s < n+C.gates.length := by
    have hsinput : s ∈ (gateAt C j).inputs := by rcases hpair with h | h <;> simp [h]
    have := hAO.2.1 j hj s hsinput
    omega
  rcases hopposite with h | h
  · exact line_operand_false_complement G P C hAO hbip j w s hj hop hinputs hbelow
      h.2 c (pure_point_support P C hAO s hs h.1 hcenter) hcenter
  · exact point_operand_false_complement G P C hAO hbip j w s hj hop hinputs hbelow
      h.2 c (by simpa using pure_line_support P C hAO s hs h.1 hcenter) hcenter

end MonochromaticTopBridge

namespace StarFrontierBridge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership GeneralGateBudget

def neighbors {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : Fin n) : Finset (Fin n) := Finset.univ.filter (G.Adj c)

def edgeKey {n : ℕ} (c v : Fin n) : Fin n × Fin n := (min c v, max c v)

lemma edgeKey_comm {n : ℕ} (c v : Fin n) : edgeKey c v = edgeKey v c := by
  simp only [edgeKey, min_comm c v, max_comm c v]

lemma graph_budget_of_star_roots {n : ℕ} {C : Circuit}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hm : Monotone2 C) (rb : ReadsBack n C)
    (hcommon : ∀ c d : Fin n, c ≠ d → (neighbors G c ∩ neighbors G d).card ≤ 1)
    (B : Finset ℕ) (hB : B ⊆ births n C) (c : ℕ → Fin n) (w : ℕ → ℕ)
    (hinput : ∀ k ∈ B, w k ∈ (gateAt C k).inputs)
    (hfalse : ∀ k ∈ B,
      val C (List.ofFn (PurePointBudget.complementInput (neighbors G (c k)))) (w k) = false)
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
  have hr (t : Fin n) (a : ℕ) (ha : a ∈ roots t) :
      ∃ k ∈ B, c k = t ∧ w k = a := by
    obtain ⟨k, hk, he⟩ := Finset.mem_image.1 ha
    exact ⟨k, (Finset.mem_filter.1 hk).1, (Finset.mem_filter.1 hk).2, he⟩
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
  have hsumRoots : (∑ t ∈ T, (roots t).card) ≤ B.card := by
    rw [← hsumB]
    exact Finset.sum_le_sum fun t _ => Finset.card_image_le
  have hfront : (∑ t ∈ T, (leaves t).card) ≤
      (∑ t ∈ T, (roots t).card) + (merges n C).card := by
    have h := MergeFrontier.multi_frontier_merge_budget (ι := T) hm rb
      (fun t => neighbors G t.val) (fun t => leaves t.val) (fun t => roots t.val)
      (by
        intro t a ha
        obtain ⟨k,hk,_,rfl⟩ := hr t.val a ha
        have hkC := (mem_births.1 (hB hk)).1.1
        have := rb k hkC (w k) (hinput k hk)
        omega)
      (by
        intro t a ha hn
        obtain ⟨k,hk,_,rfl⟩ := hr t.val a ha
        apply reachable_child rb (mem_births.1 (hB hk)).1
        simpa only [show n + (w k - n) = w k by omega] using hinput k hk)
      (by
        intro t a ha
        obtain ⟨k,hk,hc,rfl⟩ := hr t.val a ha
        simpa only [hc] using hfalse k hk)
      (fun _ => Finset.Subset.refl _)
      (by
        intro t t' hne
        exact hcommon t.val t'.val (fun h => hne (Subtype.ext h)))
    rw [Finset.sum_coe_sort T (fun t => (leaves t).card),
      Finset.sum_coe_sort T (fun t => (roots t).card)] at h
    exact h
  have hEL : E.card ≤ B.card + (merges n C).card := by
    calc
      _ ≤ (T.biUnion fun t => (leaves t).image (edgeKey t)).card := Finset.card_le_card hEsub
      _ ≤ ∑ t ∈ T, ((leaves t).image (edgeKey t)).card := Finset.card_biUnion_le
      _ ≤ ∑ t ∈ T, (leaves t).card := Finset.sum_le_sum fun _ _ => Finset.card_image_le
      _ ≤ (∑ t ∈ T, (roots t).card) + (merges n C).card := hfront
      _ ≤ B.card + (merges n C).card := Nat.add_le_add_right hsumRoots _
  have hgate := GeneralGateBudget.gate_budget hm rb
  have hBc := Finset.card_le_card hB
  exact ⟨T,hcov,Finset.card_image_le,by omega⟩


lemma selected_birth_star {n : ℕ} {C : Circuit}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hcommon : ∀ c d : Fin n, c ≠ d → (neighbors G c ∩ neighbors G d).card ≤ 1)
    {k : ℕ} (hk : k ∈ births n C)
    (hcross : ∀ a b, (gateAt C k).inputs = [a,b] →
      ∀ u ∈ singletonSupport n C a, ∀ v ∈ singletonSupport n C b, G.Adj u v)
    (hguard : ∀ c s w, ((gateAt C k).inputs = [s,w] ∨ (gateAt C k).inputs = [w,s]) →
      singletonSupport n C s = {c} →
      val C (List.ofFn (PurePointBudget.complementInput (neighbors G c))) w = false) :
    ∃ (c : Fin n) (w : ℕ), w ∈ (gateAt C k).inputs ∧
      val C (List.ofFn (PurePointBudget.complementInput (neighbors G c))) w = false ∧
      ∀ u v : Fin n, (∀ a ∈ (gateAt C k).inputs,
        u ∈ singletonSupport n C a ∨ v ∈ singletonSupport n C a) →
        (u = c ∧ v ∈ singletonSupport n C w) ∨ (v = c ∧ u ∈ singletonSupport n C w) := by
  classical
  obtain ⟨hr,hop,hempty,a,b,hab,ha,hb⟩ := mem_births.1 hk
  have hex := hcross a b hab
  have hsmall : (singletonSupport n C a).card ≤ 1 ∨ (singletonSupport n C b).card ≤ 1 := by
    by_contra! h
    obtain ⟨u,hu,v,hv,huv⟩ := Finset.one_lt_card.1 h.1
    obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.1 h.2
    have hc := hcommon u v huv
    have hxm : x ∈ neighbors G u ∩ neighbors G v := by simp [neighbors,hex u hu x hx,hex v hv x hx]
    have hym : y ∈ neighbors G u ∩ neighbors G v := by simp [neighbors,hex u hu y hy,hex v hv y hy]
    exact hxy (Finset.card_le_one.1 hc x hxm y hym)
  have star (s w : ℕ) (hs : (singletonSupport n C s).Nonempty)
      (hcard : (singletonSupport n C s).card ≤ 1)
      (hpair : (gateAt C k).inputs = [s,w] ∨ (gateAt C k).inputs = [w,s])
      (hsin : s ∈ (gateAt C k).inputs) (hwin : w ∈ (gateAt C k).inputs)
      (hx : ∀ u ∈ singletonSupport n C s, ∀ v ∈ singletonSupport n C w, G.Adj u v) :
      ∃ (c : Fin n) (w : ℕ), w ∈ (gateAt C k).inputs ∧
        val C (List.ofFn (PurePointBudget.complementInput (neighbors G c))) w = false ∧
        ∀ u v : Fin n, (∀ a ∈ (gateAt C k).inputs,
          u ∈ singletonSupport n C a ∨ v ∈ singletonSupport n C a) →
          (u = c ∧ v ∈ singletonSupport n C w) ∨ (v = c ∧ u ∈ singletonSupport n C w) := by
    obtain ⟨c,hc⟩ := hs
    have heq : ∀ t ∈ singletonSupport n C s, t = c :=
      fun t ht => Finset.card_le_one.1 hcard t ht c hc
    have hsEq : singletonSupport n C s = {c} := by
      ext t
      simp only [Finset.mem_singleton]
      exact ⟨heq t,fun he => he ▸ hc⟩
    refine ⟨c,w,hwin,hguard c s w hpair hsEq,?_⟩
    intro u v h
    rcases h s hsin with hu | hv
    · left
      refine ⟨heq u hu,(h w hwin).resolve_left fun hw => ?_⟩
      exact G.irrefl (hx u hu u hw)
    · right
      refine ⟨heq v hv,(h w hwin).resolve_right fun hw => ?_⟩
      exact G.irrefl (hx v hv v hw)
  rcases hsmall with h | h
  · exact star a b ha h (Or.inl hab) (by simp [hab]) (by simp [hab]) hex
  · exact star b a hb h (Or.inr hab) (by simp [hab]) (by simp [hab])
      (fun u hu v hv => (hex v hv u hu).symm)

lemma graph_budget_of_selected_births {n : ℕ} {C : Circuit}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (seed : Fin n)
    (hm : Monotone2 C) (rb : ReadsBack n C)
    (hcommon : ∀ c d : Fin n, c ≠ d → (neighbors G c ∩ neighbors G d).card ≤ 1)
    (B : Finset ℕ) (hB : B ⊆ births n C)
    (hcross : ∀ k ∈ B, ∀ a b, (gateAt C k).inputs = [a,b] →
      ∀ u ∈ singletonSupport n C a, ∀ v ∈ singletonSupport n C b, G.Adj u v)
    (hguard : ∀ k ∈ B, ∀ c s w,
      ((gateAt C k).inputs = [s,w] ∨ (gateAt C k).inputs = [w,s]) →
      singletonSupport n C s = {c} →
      val C (List.ofFn (PurePointBudget.complementInput (neighbors G c))) w = false)
    (hcover : ∀ u v, G.Adj u v → ∃ k ∈ B,
      ∀ a ∈ (gateAt C k).inputs, u ∈ singletonSupport n C a ∨ v ∈ singletonSupport n C a)
    (E : Finset (Fin n × Fin n))
    (hE : ∀ p ∈ E, G.Adj p.1 p.2 ∧ p.1 ≤ p.2) :
    ∃ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
      T.card ≤ B.card ∧ E.card + B.card ≤ C.size + 1 := by
  classical
  let star (k : ℕ) (hk : k ∈ B) :=
    selected_birth_star G hcommon (hB hk) (hcross k hk) (hguard k hk)
  let c (k : ℕ) := if hk : k ∈ B then (star k hk).choose else seed
  let w (k : ℕ) := if hk : k ∈ B then (star k hk).choose_spec.choose else 0
  have choose_spec (k) (hk : k ∈ B) :
      w k ∈ (gateAt C k).inputs ∧
      val C (List.ofFn (PurePointBudget.complementInput (neighbors G (c k)))) (w k) = false ∧
      ∀ u v : Fin n, (∀ a ∈ (gateAt C k).inputs,
        u ∈ singletonSupport n C a ∨ v ∈ singletonSupport n C a) →
        (u = c k ∧ v ∈ singletonSupport n C (w k)) ∨
        (v = c k ∧ u ∈ singletonSupport n C (w k)) := by
    simpa only [c,w,dite_eq_left hk] using (star k hk).choose_spec.choose_spec
  apply graph_budget_of_star_roots G hm rb hcommon B hB c w
    (fun k hk => (choose_spec k hk).1) (fun k hk => (choose_spec k hk).2.1) ?_ E hE
  intro u v huv
  obtain ⟨k,hk,ha⟩ := hcover u v huv
  exact ⟨k,hk,(choose_spec k hk).2.2 u v ha⟩

end StarFrontierBridge

namespace UsefulBirthCoverage

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm GeneralGateBudget
open SeparatedOperands MonochromaticTopBridge

lemma graph_singleton_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u : Fin n) : graphFun G ∅ (pairInput u u) = false := by
  classical
  simp [graphFun,pairInput]

lemma graph_pair_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) : graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  classical
  simp [graphFun,pairInput,or_and_right,and_or_left,exists_or,G.adj_comm]

lemma clean_and_route {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (u v : Fin n) :
    ∀ w, (w < n ∨ reachable n C (w-n)) →
      (∀ x : Fin n → Bool, val C (List.ofFn x) w = true → graphFun G ∅ x = true) →
      val C (List.ofFn (pairInput u v)) w = true →
      ∃ k, reachable n C k ∧ (gateAt C k).op = .and ∧ BelowF G C k ∧
        val C (List.ofFn (pairInput u v)) (n+k) = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hvalid hbelow htrue
    by_cases hi : w < n
    · let t : Fin n := ⟨w,hi⟩
      have ht : val C (List.ofFn (pairInput t t)) w = true := by
        change val C (List.ofFn (pairInput t t)) t.val = true
        rw [val_ofFn]
        simp [pairInput]
      have hf := hbelow (pairInput t t) ht
      rw [graph_singleton_false] at hf
      cases hf
    · obtain ⟨k,rfl⟩ : ∃ k, w = n+k := ⟨w-n,by omega⟩
      have hk : reachable n C k := by simpa using hvalid.resolve_left hi
      rcases gate_op (ao_mono hAO) hk.1 with hand | hor
      · exact ⟨k,hk,hand,fun x hx => hbelow x hx,htrue⟩
      · obtain ⟨a,ha,halt,hat⟩ := (val_or (by simp) hk.1 hor).mp htrue
        apply ih a halt
        · by_cases hn : a < n
          · exact Or.inl hn
          · exact Or.inr (reachable_child hAO.2.1 hk
              (by simpa only [show n+(a-n)=a by omega] using ha))
        · intro x hx
          apply hbelow x
          exact (val_or (by simp) hk.1 hor).mpr ⟨a,ha,halt,hx⟩
        · exact hat

lemma edge_clean_top {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C)
    (hcorrect : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = graphFun G ∅ x)
    (u v : Fin n) (huv : G.Adj u v) :
    ∃ k, reachable n C k ∧ (gateAt C k).op = .and ∧ BelowF G C k ∧
      val C (List.ofFn (pairInput u v)) (n+k) = true := by
  have ht : val C (List.ofFn (pairInput u v)) C.output = true := by
    rw [← eval_eq_val,hcorrect]
    exact (graph_pair_true G u v).mpr huv
  have hv : C.output < n+C.gates.length := by
    by_contra! h
    rw [val_ge (by simp) h] at ht
    cases ht
  apply clean_and_route G C hAO u v C.output ?_ ?_ ht
  · by_cases hn : C.output < n
    · exact Or.inl hn
    · exact Or.inr ⟨by omega,Or.inl (by omega)⟩
  · intro x hx
    simpa only [← eval_eq_val,hcorrect] using hx

lemma pair_point_mask {n : ℕ} (P : Finset (Fin n)) (u v : Fin n)
    (hu : u ∈ P) (hv : v ∉ P) :
    (fun z => if z ∈ P then pairInput u v z else false) = pairInput u u := by
  funext z
  by_cases hzu : z = u
  · subst z
    simp [pairInput,hu]
  · by_cases hzv : z = v
    · subst z
      simp [pairInput,hv,hzu]
    · simp [pairInput,hzu,hzv]

lemma pair_line_mask {n : ℕ} (P : Finset (Fin n)) (u v : Fin n)
    (hu : u ∈ P) (hv : v ∉ P) :
    (fun z => if z ∈ P then false else pairInput u v z) = pairInput v v := by
  funext z
  by_cases hzu : z = u
  · subst z
    have huv : u ≠ v := fun h => hv (h ▸ hu)
    simp [pairInput,hu,huv]
  · by_cases hzv : z = v
    · subst z
      simp [pairInput,hv]
    · simp [pairInput,hzu,hzv]

lemma pure_point_pair {n : ℕ} (P : Finset (Fin n)) (C : Circuit) (w : ℕ)
    (hp : PurePoint (wireFn P C w)) (u v : Fin n) (hu : u ∈ P) (hv : v ∉ P) :
    val C (List.ofFn (pairInput u v)) w = val C (List.ofFn (pairInput u u)) w := by
  have h := hp (pairInput u v) (pairInput u v)
  simpa only [wireFn,ite_self,pair_point_mask P u v hu hv] using h

lemma pure_line_pair {n : ℕ} (P : Finset (Fin n)) (C : Circuit) (w : ℕ)
    (hp : PureLine (wireFn P C w)) (u v : Fin n) (hu : u ∈ P) (hv : v ∉ P) :
    val C (List.ofFn (pairInput u v)) w = val C (List.ofFn (pairInput v v)) w := by
  have h := hp (pairInput u v) (pairInput u v)
  simpa only [wireFn,ite_self,pair_line_mask P u v hu hv] using h


lemma pure_pair_support {n : ℕ} (G : SimpleGraph (Fin n))
    (P : Finset (Fin n)) (C : Circuit) (w : ℕ)
    (hbip : ∀ u v, G.Adj u v → (u ∈ P ↔ v ∉ P))
    (hp : PurePoint (wireFn P C w) ∨ PureLine (wireFn P C w))
    (u v : Fin n) (huv : G.Adj u v)
    (ht : val C (List.ofFn (pairInput u v)) w = true) :
    u ∈ singletonSupport n C w ∨ v ∈ singletonSupport n C w := by
  have help (u v : Fin n) (hu : u ∈ P) (hv : v ∉ P)
      (ht : val C (List.ofFn (pairInput u v)) w = true) :
      u ∈ singletonSupport n C w ∨ v ∈ singletonSupport n C w := by
    rcases hp with hp | hp
    · left
      apply mem_support.mpr
      rw [← pure_point_pair P C w hp u v hu hv]
      exact ht
    · right
      apply mem_support.mpr
      rw [← pure_line_pair P C w hp u v hu hv]
      exact ht
  by_cases hu : u ∈ P
  · exact help u v hu ((hbip u v huv).mp hu) ht
  · have hv : v ∈ P := (hbip v u huv.symm).mpr hu
    have hswap : pairInput u v = pairInput v u := by
      funext z
      simp [pairInput,or_comm]
    exact (help v u hv hu (by simpa only [← hswap] using ht)).symm

lemma clean_top_pair_supports {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P : Finset (Fin n)) (C : Circuit) (hAO : IsAO2 n C)
    (hbip : ∀ u v, G.Adj u v → (u ∈ P ↔ v ∉ P))
    (hsep : ∀ k < C.gates.length, (gateAt C k).op = .and →
      ∀ w ∈ (gateAt C k).inputs, Separates (wireFn P C w))
    (k : ℕ) (hk : k < C.gates.length) (hop : (gateAt C k).op = .and)
    (hbelow : BelowF G C k) (u v : Fin n) (huv : G.Adj u v)
    (ht : val C (List.ofFn (pairInput u v)) (n+k) = true) :
    ∀ w ∈ (gateAt C k).inputs,
      u ∈ singletonSupport n C w ∨ v ∈ singletonSupport n C w := by
  obtain ⟨a,b,hab,ha,hb⟩ := two_inputs hAO k hk
  have hp := useful_top_operands_opposite G P C hAO hbip hsep
    k a b hk hop hab hbelow ⟨pairInput u v,ht⟩
  intro w hw
  have hwt := ((val_and (by simp) hk hop).mp ht w hw).2
  have hwab : w = a ∨ w = b := by simpa [hab] using hw
  apply pure_pair_support G P C w hbip ?_ u v huv hwt
  rcases hwab with rfl | rfl
  · exact hp.imp And.left And.left
  · exact hp.symm.imp And.right And.right

noncomputable def usefulTops {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter fun k =>
    reachable n C k ∧ (gateAt C k).op = .and ∧ BelowF G C k ∧
      ∃ u v, G.Adj u v ∧ val C (List.ofFn (pairInput u v)) (n+k) = true

lemma mem_usefulTops {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (k : ℕ) : k ∈ usefulTops G C ↔
    reachable n C k ∧ (gateAt C k).op = .and ∧ BelowF G C k ∧
      ∃ u v, G.Adj u v ∧ val C (List.ofFn (pairInput u v)) (n+k) = true := by
  classical
  simp only [usefulTops,Finset.mem_filter,Finset.mem_range]
  exact ⟨And.right,fun h => ⟨h.1.1,h⟩⟩

lemma usefulTops_subset_births {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P : Finset (Fin n)) (C : Circuit) (hAO : IsAO2 n C)
    (hbip : ∀ u v, G.Adj u v → (u ∈ P ↔ v ∉ P))
    (hsep : ∀ k < C.gates.length, (gateAt C k).op = .and →
      ∀ w ∈ (gateAt C k).inputs, Separates (wireFn P C w)) : usefulTops G C ⊆ births n C := by
  intro k hk
  obtain ⟨hr,hop,hbelow,u,v,huv,ht⟩ := (mem_usefulTops G C k).mp hk
  have hsupports := clean_top_pair_supports G P C hAO hbip hsep
    k hr.1 hop hbelow u v huv ht
  have hnonempty (w : ℕ) (hw : w ∈ (gateAt C k).inputs) :
      (singletonSupport n C w).Nonempty := by
    rcases hsupports w hw with hu | hv
    · exact ⟨u,hu⟩
    · exact ⟨v,hv⟩
  have hempty : singletonSupport n C (n+k) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro t ht
    have hf := hbelow (pairInput t t) (mem_support.mp ht)
    rw [graph_singleton_false] at hf
    cases hf
  obtain ⟨a,b,hab,_,_⟩ := two_inputs hAO k hr.1
  exact mem_births.mpr ⟨hr,hop,hempty,a,b,hab,
    hnonempty a (by simp [hab]),hnonempty b (by simp [hab])⟩

lemma usefulTops_cover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P : Finset (Fin n)) (C : Circuit) (hAO : IsAO2 n C)
    (hbip : ∀ u v, G.Adj u v → (u ∈ P ↔ v ∉ P))
    (hsep : ∀ k < C.gates.length, (gateAt C k).op = .and →
      ∀ w ∈ (gateAt C k).inputs, Separates (wireFn P C w))
    (hcorrect : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = graphFun G ∅ x) :
    ∀ u v, G.Adj u v → ∃ k ∈ usefulTops G C,
      ∀ a ∈ (gateAt C k).inputs,
        u ∈ singletonSupport n C a ∨ v ∈ singletonSupport n C a := by
  intro u v huv
  obtain ⟨k,hr,hop,hbelow,ht⟩ := edge_clean_top G C hAO hcorrect u v huv
  refine ⟨k,(mem_usefulTops G C k).mpr ⟨hr,hop,hbelow,u,v,huv,ht⟩,?_⟩
  exact clean_top_pair_supports G P C hAO hbip hsep k hr.1 hop hbelow u v huv ht

lemma usefulTops_crossing {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) :
    ∀ k ∈ usefulTops G C, ∀ a b, (gateAt C k).inputs = [a,b] →
      ∀ u ∈ singletonSupport n C a, ∀ v ∈ singletonSupport n C b, G.Adj u v := by
  intro k hk a b hab u hu v hv
  obtain ⟨hr,hop,hbelow,_⟩ := (mem_usefulTops G C k).mp hk
  apply (graph_pair_true G u v).mp
  apply hbelow (pairInput u v)
  rw [gateVal_eq_val]
  apply (val_and (by simp) hr.1 hop).mpr
  intro w hw
  refine ⟨hAO.2.1 k hr.1 w hw,?_⟩
  have hwab : w = a ∨ w = b := by simpa [hab] using hw
  rcases hwab with rfl | rfl
  · exact pair_mono (ao_mono hAO) (by intro i; simp [pairInput]; exact Or.inl) _ (mem_support.mp hu)
  · exact pair_mono (ao_mono hAO) (by intro i; simp [pairInput]; exact Or.inr) _ (mem_support.mp hv)

end UsefulBirthCoverage

namespace SeparableDirtyBound

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm GeneralGateBudget
open SeparatedOperands MonochromaticTopBridge StarFrontierBridge UsefulBirthCoverage

lemma useful_top_guard {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P : Finset (Fin n)) (C : Circuit) (hAO : IsAO2 n C)
    (hbip : ∀ u v, G.Adj u v → (u ∈ P ↔ v ∉ P))
    (hsep : ∀ k < C.gates.length, (gateAt C k).op = .and →
      ∀ w ∈ (gateAt C k).inputs, Separates (wireFn P C w)) :
    ∀ k ∈ usefulTops G C, ∀ c s w,
      ((gateAt C k).inputs = [s,w] ∨ (gateAt C k).inputs = [w,s]) →
      singletonSupport n C s = {c} →
      val C (List.ofFn (PurePointBudget.complementInput (neighbors G c))) w = false := by
  intro k hk c s w hpair hc
  obtain ⟨hr,hop,hbelow,u,v,huv,ht⟩ := (mem_usefulTops G C k).mp hk
  apply pure_top_guard G P C hAO hbip k s w hr.1 hop hpair hbelow ?_ c (by simp [hc])
  rcases hpair with hpair | hpair
  · exact useful_top_operands_opposite G P C hAO hbip hsep
      k s w hr.1 hop hpair hbelow ⟨pairInput u v,ht⟩
  · have h := useful_top_operands_opposite G P C hAO hbip hsep
      k w s hr.1 hop hpair hbelow ⟨pairInput u v,ht⟩
    rcases h with ⟨hw,hs⟩ | ⟨hw,hs⟩
    · exact Or.inr ⟨hs,hw⟩
    · exact Or.inl ⟨hs,hw⟩

lemma separated_operands_graph_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P : Finset (Fin n)) (seed : Fin n) (C : Circuit)
    (hAO : IsAO2 n C)
    (hbip : ∀ u v, G.Adj u v → (u ∈ P ↔ v ∉ P))
    (hcommon : ∀ c d : Fin n, c ≠ d → (neighbors G c ∩ neighbors G d).card ≤ 1)
    (hsep : ∀ k < C.gates.length, (gateAt C k).op = .and →
      ∀ w ∈ (gateAt C k).inputs, Separates (wireFn P C w))
    (hcorrect : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = graphFun G ∅ x)
    (E : Finset (Fin n × Fin n))
    (hE : ∀ p ∈ E, G.Adj p.1 p.2 ∧ p.1 ≤ p.2) :
    ∃ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
      E.card + T.card ≤ C.size + 1 := by
  obtain ⟨T,hT,hTB,hEB⟩ := graph_budget_of_selected_births G seed
    (ao_mono hAO) hAO.2.1 hcommon (usefulTops G C)
    (usefulTops_subset_births G P C hAO hbip hsep)
    (usefulTops_crossing G C hAO)
    (useful_top_guard G P C hAO hbip hsep)
    (usefulTops_cover G P C hAO hbip hsep hcorrect) E hE
  exact ⟨T,hT,by omega⟩

lemma separable_dirty_graph_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P : Finset (Fin n)) (seed : Fin n) (C : Circuit)
    (hAO : IsAO2 n C) (hTop : TopForm G C)
    (hbip : ∀ u v, G.Adj u v → (u ∈ P ↔ v ∉ P))
    (hcommon : ∀ c d : Fin n, c ≠ d → (neighbors G c ∩ neighbors G d).card ≤ 1)
    (hdirty : ∀ k < C.gates.length, (gateAt C k).op = .and → ¬ BelowF G C k →
      Separates (wireFn P C (n+k)))
    (hcorrect : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = graphFun G ∅ x)
    (E : Finset (Fin n × Fin n))
    (hE : ∀ p ∈ E, G.Adj p.1 p.2 ∧ p.1 ≤ p.2) :
    ∃ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
      E.card + T.card ≤ C.size + 1 := by
  exact separated_operands_graph_bound G P seed C hAO hbip hcommon
    (fun k hk hop w hw => operand_separates G P C hAO hTop hdirty k hk hop w hw)
    hcorrect E hE

end SeparableDirtyBound

lemma rectangle_degenerate {N : ℕ} {I : Fin N → Fin N → Prop}
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    {p p' l l' : Fin N} (hpl : I p l) (hpl' : I p l')
    (hp'l : I p' l) (hp'l' : I p' l') : p = p' ∨ l = l' := by
  by_cases hp : p = p'
  · exact Or.inl hp
  · obtain ⟨k, _, hk⟩ := hu p p' hp
    exact Or.inr ((hk l ⟨hpl, hp'l⟩).trans (hk l' ⟨hpl', hp'l'⟩).symm)

lemma point_lines_card {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hc : ∀ l : Fin N, (Finset.univ.filter fun p => I p l).card = q + 1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (p : Fin N) : (Finset.univ.filter fun l => I p l).card = q + 1 := by
  classical
  let L := Finset.univ.filter fun l => I p l
  let R := fun l => (Finset.univ.filter fun x => I x l).erase p
  have hcover : L.biUnion R = Finset.univ.erase p := by
    ext x
    constructor
    · intro hx
      obtain ⟨l, _, hx⟩ := Finset.mem_biUnion.mp hx
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hx).1, Finset.mem_univ _⟩
    · intro hx
      have hxp := (Finset.mem_erase.mp hx).1
      obtain ⟨l, hl, _⟩ := hu p x hxp.symm
      exact Finset.mem_biUnion.mpr ⟨l, by simp [L, hl.1], by simp [R, hxp, hl.2]⟩
  have hd : (L : Set (Fin N)).PairwiseDisjoint R := by
    intro l hl l' hl' hne
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    have hpx : p ≠ x := (Finset.mem_erase.mp hx).1.symm
    have hlp : I p l := (Finset.mem_filter.mp hl).2
    have hlp' : I p l' := (Finset.mem_filter.mp hl').2
    have hlx : I x l := (Finset.mem_filter.mp (Finset.mem_erase.mp hx).2).2
    have hlx' : I x l' := (Finset.mem_filter.mp (Finset.mem_erase.mp hx').2).2
    exact hne ((rectangle_degenerate hu hlp hlp' hlx hlx').resolve_left hpx)
  have hr (l : Fin N) (hl : l ∈ L) : (R l).card = q := by
    have hp : p ∈ Finset.univ.filter fun x => I x l := by
      simpa only [L, Finset.mem_filter, Finset.mem_univ, true_and] using hl
    simp only [R, Finset.card_erase_of_mem hp, hc]
    omega
  have he := Finset.card_biUnion hd
  rw [hcover, Finset.card_erase_of_mem (Finset.mem_univ p)] at he
  simp only [Finset.card_univ, Fintype.card_fin] at he
  have hsum : ∑ l ∈ L, (R l).card = L.card * q := by
    simp only [Finset.sum_congr rfl hr, Finset.sum_const, smul_eq_mul]
  rw [hsum] at he
  have : L.card * q = (q + 1) * q := by
    rw [← he, hN]
    simp only [Nat.add_sub_cancel]
    ring
  exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < q) this

lemma plane_cover_bound {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hc : ∀ l : Fin N, (Finset.univ.filter fun p => I p l).card = q + 1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (A B : Finset (Fin N)) (hcover : ∀ p l, I p l → p ∈ A ∨ l ∈ B) :
    N ≤ A.card + B.card := by
  classical
  have hr := point_lines_card I hq hN hc hu
  have hrows (p : Fin N) : (∑ l : Fin N, if I p l then (1 : ℕ) else 0) = q + 1 := by
    simpa using hr p
  have hcols (l : Fin N) : (∑ p : Fin N, if I p l then (1 : ℕ) else 0) = q + 1 := by
    simpa using hc l
  have hineq : N * (q + 1) ≤ (A.card + B.card) * (q + 1) := by
    calc
      N * (q + 1) = ∑ p : Fin N, ∑ l : Fin N, if I p l then (1 : ℕ) else 0 := by
        simp [hrows]
      _ ≤ ∑ p : Fin N, ∑ l : Fin N,
          ((if p ∈ A then (if I p l then (1 : ℕ) else 0) else 0) +
            (if l ∈ B then (if I p l then (1 : ℕ) else 0) else 0)) := by
        apply Finset.sum_le_sum
        intro p _
        apply Finset.sum_le_sum
        intro l _
        by_cases hi : I p l
        · rcases hcover p l hi with hp | hl
          · simp [hi, hp]
          · simp [hi, hl]
        · simp [hi]
      _ = (A.card + B.card) * (q + 1) := by
        simp only [Finset.sum_add_distrib]
        have ha : (∑ p : Fin N, ∑ l : Fin N,
            if p ∈ A then (if I p l then (1 : ℕ) else 0) else 0) = A.card * (q + 1) := by
          simp [Finset.sum_ite_irrel, hrows]
        have hb : (∑ p : Fin N, ∑ l : Fin N,
            if l ∈ B then (if I p l then (1 : ℕ) else 0) else 0) = B.card * (q + 1) := by
          rw [Finset.sum_comm]
          simp [Finset.sum_ite_irrel, hcols]
        rw [ha, hb, Nat.add_mul]
  exact Nat.le_of_mul_le_mul_right hineq (by omega)

namespace PlaneSeparableBound


def directed {n : ℕ} (I : Fin n → Fin n → Prop) (x y : ℕ) :=
  ∃ p l, x = p.val ∧ y = n + l.val ∧ I p l

def adj {n : ℕ} (I : Fin n → Fin n → Prop) (x y : ℕ) :=
  directed I x y ∨ directed I y x

lemma adj_sym {n : ℕ} {I : Fin n → Fin n → Prop} {x y} (h : adj I x y) :
    adj I y x := h.symm

lemma sides {n : ℕ} {I : Fin n → Fin n → Prop} {x y} (h : directed I x y) :
    x < n ∧ n ≤ y := by
  obtain ⟨p,l,rfl,rfl,_⟩ := h
  exact ⟨p.isLt, Nat.le_add_right ..⟩

lemma adj_irrefl {n : ℕ} {I : Fin n → Fin n → Prop} (x : ℕ) : ¬ adj I x x := by
  intro h
  have h' := sides (h.elim id id)
  omega

lemma rectangle {n : ℕ} {I : Fin n → Fin n → Prop}
    (hu : ∀ p p' : Fin n, p ≠ p' → ∃! l, I p l ∧ I p' l)
    {x z y v} (a : directed I x y) (b : directed I z y)
    (c : directed I x v) (d : directed I z v) : x = z ∨ y = v := by
  obtain ⟨p,l,rfl,rfl,ap⟩ := a
  obtain ⟨s,l',rfl,e,bs⟩ := b
  have el : l = l' := Fin.ext (Nat.add_left_cancel e)
  subst l'
  obtain ⟨p',k,f,rfl,cp⟩ := c
  have ep : p = p' := Fin.ext f
  subst p'
  obtain ⟨s',k',g,j,ds⟩ := d
  have es : s = s' := Fin.ext g
  have ek : k = k' := Fin.ext (Nat.add_left_cancel j)
  subst s'
  subst k'
  by_cases h : p = s
  · exact Or.inl (congrArg Fin.val h)
  · obtain ⟨_,_,uniq⟩ := hu p s h
    exact Or.inr (congrArg (fun t : Fin n => n + t.val)
      ((uniq l ⟨ap,bs⟩).trans (uniq k ⟨cp,ds⟩).symm))

lemma adj_unique {n : ℕ} {I : Fin n → Fin n → Prop}
    (hu : ∀ p p' : Fin n, p ≠ p' → ∃! l, I p l ∧ I p' l) : ∀ {x z y v}, x ≠ z → adj I x y → adj I z y → adj I x v → adj I z v → y = v := by
  intro x z y v hn a b c d
  rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;> rcases d with d | d
  all_goals first
    | exact (rectangle hu a b c d).resolve_left hn
    | exact (rectangle hu a c b d).resolve_right hn
    | have := sides a; have := sides b; have := sides c; have := sides d; omega


noncomputable def allEdges {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] : Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun e => I e.1 e.2)

lemma allEdges_card {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (q : ℕ)
    (hL : ∀ l, (Finset.univ.filter (fun p => I p l)).card = q + 1) :
    (allEdges I).card = N * (q + 1) := by
  classical
  let F (l : Fin N) : Finset (Fin N × Fin N) :=
    (Finset.univ.filter (fun p => I p l)).map ⟨fun p => (p, l), fun _ _ h => congrArg Prod.fst h⟩
  have hF (l : Fin N) (e : Fin N × Fin N) : e ∈ F l ↔ I e.1 l ∧ e.2 = l := by
    constructor
    · intro he
      obtain ⟨p, hp, ht⟩ := Finset.mem_map.mp he
      change (p, l) = e at ht
      rw [← ht]
      exact ⟨(Finset.mem_filter.mp hp).2, rfl⟩
    · rintro ⟨hi, hh⟩
      refine Finset.mem_map.mpr ⟨e.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, ?_⟩
      exact Prod.ext rfl hh.symm
  have heq : allEdges I = Finset.univ.biUnion F := by
    ext e
    simp only [allEdges, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, hF]
    exact ⟨fun h => ⟨e.2, h, rfl⟩, fun ⟨l, hi, he⟩ => he ▸ hi⟩
  rw [heq, Finset.card_biUnion]
  · simp [F, hL]
  · intro l _ l' _ hne
    refine Finset.disjoint_left.mpr ?_
    intro e he he'
    exact hne (((hF l e).mp he).2.symm.trans ((hF l' e).mp he').2)


def incidenceGraph {N : ℕ} (I : Fin N → Fin N → Prop) : SimpleGraph (Fin (N + N)) where
  Adj a b := adj I a.val b.val
  symm := ⟨fun _ _ h => adj_sym h⟩
  loopless := ⟨fun a => adj_irrefl a.val⟩

open Classical in
lemma incidence_noFour {N : ℕ} (I : Fin N → Fin N → Prop)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l, I p l ∧ I p' l) :
    PEqualNP.TopForm.NoFourCycle (incidenceGraph I) := by
  intro a b hn
  apply Finset.card_le_one.mpr
  intro y hy v hv
  apply Fin.ext
  exact adj_unique hu (fun h => hn (Fin.ext h))
    (Finset.mem_filter.mp hy).2.1 (Finset.mem_filter.mp hy).2.2
    (Finset.mem_filter.mp hv).2.1 (Finset.mem_filter.mp hv).2.2

lemma incidence_formula {N : ℕ} (I : Fin N → Fin N → Prop) (x : Fin (N + N) → Bool) :
    (∃ u v : Fin (N + N), (incidenceGraph I).Adj u v ∧ x u = true ∧ x v = true) ↔
      (∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) := by
  constructor
  · rintro ⟨u,v,h,hu,hv⟩
    rcases h with h | h
    · obtain ⟨p,l,hp,hl,hi⟩ := h
      have ep : u = Fin.castAdd N p := Fin.ext hp
      have el : v = Fin.natAdd N l := Fin.ext hl
      exact ⟨p,l,hi,ep ▸ hu,el ▸ hv⟩
    · obtain ⟨p,l,hp,hl,hi⟩ := h
      have ep : v = Fin.castAdd N p := Fin.ext hp
      have el : u = Fin.natAdd N l := Fin.ext hl
      exact ⟨p,l,hi,ep ▸ hv,el ▸ hu⟩
  · rintro ⟨p,l,hi,hp,hl⟩
    exact ⟨Fin.castAdd N p,Fin.natAdd N l,Or.inl ⟨p,l,rfl,rfl,hi⟩,hp,hl⟩

lemma incidence_cover_count {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hc : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (T : Finset (Fin (N + N)))
    (hT : ∀ u v, (incidenceGraph I).Adj u v → u ∈ T ∨ v ∈ T) : N ≤ T.card := by
  classical
  let A : Finset (Fin N) := Finset.univ.filter (fun p => Fin.castAdd N p ∈ T)
  let B : Finset (Fin N) := Finset.univ.filter (fun l => Fin.natAdd N l ∈ T)
  have hab : N ≤ A.card + B.card := plane_cover_bound I hq hN hc hu A B (by
    intro p l hi
    have h := hT (Fin.castAdd N p) (Fin.natAdd N l) (Or.inl ⟨p,l,rfl,rfl,hi⟩)
    simpa only [A,B,Finset.mem_filter,Finset.mem_univ,true_and] using h)
  have hd : Disjoint (A.image (Fin.castAdd N)) (B.image (Fin.natAdd N)) := by
    apply Finset.disjoint_left.mpr
    intro v hv hv'
    obtain ⟨p,_,hp⟩ := Finset.mem_image.mp hv
    obtain ⟨l,_,hl⟩ := Finset.mem_image.mp hv'
    have h := congrArg Fin.val (hp.trans hl.symm)
    change p.val = N + l.val at h
    have := p.isLt
    omega
  have hs : A.image (Fin.castAdd N) ∪ B.image (Fin.natAdd N) ⊆ T := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hv
      exact (Finset.mem_filter.mp hp).2
    · obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hv
      exact (Finset.mem_filter.mp hl).2
  have ha : Function.Injective (Fin.castAdd N : Fin N → Fin (N + N)) := by
    intro p p' h
    have hv := congrArg Fin.val h
    exact Fin.ext hv
  have hb : Function.Injective (Fin.natAdd N : Fin N → Fin (N + N)) := by
    intro l l' h
    exact Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))
  have hs' := Finset.card_le_card hs
  rw [Finset.card_union_of_disjoint hd, Finset.card_image_of_injective _ ha,
    Finset.card_image_of_injective _ hb] at hs'
  exact hab.trans hs'

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm GeneralGateBudget
open SeparatedOperands MonochromaticTopBridge StarFrontierBridge SeparableDirtyBound

noncomputable def pointSide (N : ℕ) : Finset (Fin (N+N)) :=
  Finset.univ.filter fun u => u.val < N

lemma incidence_bipartite {N : ℕ} (I : Fin N → Fin N → Prop) :
    ∀ u v, (incidenceGraph I).Adj u v → (u ∈ pointSide N ↔ v ∉ pointSide N) := by
  intro u v huv
  change adj I u.val v.val at huv
  simp only [pointSide,Finset.mem_filter,Finset.mem_univ,true_and]
  rcases huv with ⟨p,l,hu,hv,hi⟩ | ⟨p,l,hv,hu,hi⟩ <;>
    have := p.isLt <;> omega

open Classical in
lemma incidence_common {N : ℕ} (I : Fin N → Fin N → Prop)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l, I p l ∧ I p' l) :
    ∀ c d : Fin (N+N), c ≠ d →
      (neighbors (incidenceGraph I) c ∩ neighbors (incidenceGraph I) d).card ≤ 1 := by
  intro c d hcd
  apply Finset.card_le_one.mpr
  intro x hx y hy
  have hx' : (incidenceGraph I).Adj c x ∧ (incidenceGraph I).Adj d x := by
    simpa [neighbors] using hx
  have hy' : (incidenceGraph I).Adj c y ∧ (incidenceGraph I).Adj d y := by
    simpa [neighbors] using hy
  exact Fin.ext (adj_unique hu (fun h => hcd (Fin.ext h)) hx'.1 hx'.2 hy'.1 hy'.2)

open Classical in
lemma plane_separated_operands_lower {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit)
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hc : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (hAO : IsAO2 (N+N) C)
    (hsep : ∀ k < C.gates.length, (gateAt C k).op = .and →
      ∀ w ∈ (gateAt C k).inputs, Separates (wireFn (pointSide N) C w))
    (hfun : ∀ z : Fin (N+N) → Bool, circuitFun (N+N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) :
    N * (q+2) - 1 ≤ C.size := by
  classical
  let embed : Fin N × Fin N → Fin (N+N) × Fin (N+N) :=
    fun e => (Fin.castAdd N e.1,Fin.natAdd N e.2)
  let E := (allEdges I).image embed
  have hembed : Function.Injective embed := by
    intro e e' he
    apply Prod.ext
    · exact Fin.ext (congrArg (fun z : Fin (N+N) × Fin (N+N) => z.1.val) he)
    · exact Fin.ext (Nat.add_left_cancel (congrArg (fun z : Fin (N+N) × Fin (N+N) => z.2.val) he))
  have hEcard : E.card = N*(q+1) := by
    change ((allEdges I).image embed).card = N*(q+1)
    rw [Finset.card_image_of_injective _ hembed,allEdges_card I q hc]
  have hE : ∀ e ∈ E, (incidenceGraph I).Adj e.1 e.2 ∧ e.1 ≤ e.2 := by
    intro e he
    obtain ⟨⟨p,l⟩,hi,rfl⟩ := Finset.mem_image.mp he
    have hpl : I p l := by simpa [allEdges] using hi
    refine ⟨Or.inl ⟨p,l,rfl,rfl,hpl⟩,?_⟩
    change p.val ≤ N+l.val
    have := p.isLt
    omega
  have hcorrect : ∀ z : Fin (N+N) → Bool,
      C.eval (List.ofFn z) = graphFun (incidenceGraph I) ∅ z := by
    intro z
    have hz := hfun z
    change C.eval (List.ofFn z) = _ at hz
    rw [hz]
    simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or]
    exact decide_eq_decide.mpr (incidence_formula I z).symm
  let seed : Fin (N+N) := ⟨0,by omega⟩
  obtain ⟨T,hT,hbound⟩ := separated_operands_graph_bound (incidenceGraph I)
    (pointSide N) seed C hAO (incidence_bipartite I) (incidence_common I hu)
    hsep hcorrect E hE
  have ht := incidence_cover_count I hq hN hc hu T hT
  have hm : N*(q+2) = N*(q+1)+N := by ring
  omega

open Classical in
lemma plane_separable_dirty_lower {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit)
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hc : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (hAO : IsAO2 (N+N) C)
    (hTop : TopForm (incidenceGraph I) C)
    (hdirty : ∀ k < C.gates.length, (gateAt C k).op = .and →
      ¬ BelowF (incidenceGraph I) C k →
      Separates (wireFn (pointSide N) C (N+N+k)))
    (hfun : ∀ z : Fin (N+N) → Bool, circuitFun (N+N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) :
    N * (q+2) - 1 ≤ C.size := by
  apply plane_separated_operands_lower I C hq hN hc hu hAO ?_ hfun
  intro k hk hop w hw
  exact operand_separates (incidenceGraph I) (pointSide N) C hAO hTop hdirty k hk hop w hw

end PlaneSeparableBound
end PEqualNP.Outside.L_meta_2583

namespace PEqualNP.Outside.L_meta_2583.ExactReductionChildren
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open GeneralGateBudget MonochromaticTopBridge PlaneSeparableBound
lemma lower_finset : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (C : Circuit),
      2 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      IsAO2 (N + N) C →
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
        decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
          z (Fin.natAdd N l) = true)) →
      (∀ g ∈ C.gates, g.op = GateOp.and → ∀ w ∈ g.inputs,
        let V : (Fin (N + N) → Bool) → Bool :=
          fun z => (C.wires (List.ofFn z)).getD w false
        ∀ z : Fin (N + N) → Bool,
          V z = (V (fun i => if i.val < N then z i else false) ||
            V (fun i => if N ≤ i.val then z i else false))) → N * (q + 2) - 1 ≤ C.size := by
  intro q N I inst C hq hN hL hPair hAO hfun hsep
  apply plane_separated_operands_lower I C hq hN hL hPair hAO ?_ hfun
  intro k hk hop w hw x y
  have h := hsep (gateAt C k) (gateAt_mem hk) hop w hw
    (fun i => if i.val < N then x i else y i)
  have hp : (fun i : Fin (N+N) =>
      if i.val < N then (if i.val < N then x i else y i) else false) =
      (fun i => if i.val < N then x i else false) := by
    funext i
    by_cases hi : i.val < N <;> simp [hi]
  have hl : (fun i : Fin (N+N) =>
      if N ≤ i.val then (if i.val < N then x i else y i) else false) =
      (fun i => if i.val < N then false else y i) := by
    funext i
    by_cases hi : i.val < N
    · simp [hi,show ¬ N ≤ i.val by omega]
    · simp [hi,show N ≤ i.val by omega]
  dsimp only at h
  rw [hp,hl] at h
  simpa only [wireFn,pointSide,Finset.mem_filter,Finset.mem_univ,true_and,val] using h
end PEqualNP.Outside.L_meta_2583.ExactReductionChildren

namespace PEqualNP.Outside.L_meta_2583.ExactReductionChildren
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
lemma lower : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (C : Circuit),
      2 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      IsAO2 (N + N) C →
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
        decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
          z (Fin.natAdd N l) = true)) →
      (∀ g ∈ C.gates, g.op = GateOp.and → ∀ w ∈ g.inputs,
        let V : (Fin (N + N) → Bool) → Bool :=
          fun z => (C.wires (List.ofFn z)).getD w false
        ∀ z : Fin (N + N) → Bool,
          V z = (V (fun i => if i.val < N then z i else false) ||
            V (fun i => if N ≤ i.val then z i else false))) → N * (q + 2) - 1 ≤ C.size := by
  intro q N I inst C hq hN hL hPair hAO hfun hsep
  have hL' : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q+1 := by
    intro l
    simpa only [Fintype.card_subtype] using hL l
  exact lower_finset q N I C hq hN hL' hPair hAO hfun hsep
end PEqualNP.Outside.L_meta_2583.ExactReductionChildren
