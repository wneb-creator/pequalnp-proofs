import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.BitVec
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583

namespace Repair

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

lemma no_four_cycle {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
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

lemma foldl_append_length {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β) :
    (l.foldl (fun w g => w ++ [f w g]) acc).length = acc.length + l.length := by
  induction l generalizing acc with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, List.length_append, List.length_singleton]
    omega

lemma foldl_append_getD_lt {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β)
    (d : β) (k : ℕ) (hk : k < acc.length) :
    (l.foldl (fun w g => w ++ [f w g]) acc).getD k d = acc.getD k d := by
  induction l generalizing acc with
  | nil => rfl
  | cons a t ih =>
    simp only [List.foldl_cons]
    have hk' : k < (acc ++ [f acc a]).length := by
      rw [List.length_append, List.length_singleton]
      omega
    rw [ih (acc ++ [f acc a]) hk']
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left hk]

lemma foldl_append_getD_gate {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β)
    (d : β) (j : ℕ) (hj : j < l.length) (defaultA : α) :
    (l.foldl (fun w g => w ++ [f w g]) acc).getD (acc.length + j) d =
      f ((l.take j).foldl (fun w g => w ++ [f w g]) acc) (l.getD j defaultA) := by
  have hsplit : l = l.take j ++ l[j] :: l.drop (j + 1) := by
    have h1 := (List.take_append_drop j l).symm
    have h2 : l.drop j = l[j] :: l.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [← h2]
    exact h1
  have hget : l.getD j defaultA = l[j] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    rfl
  rw [hget]
  conv_lhs => rw [hsplit]
  rw [List.foldl_append, List.foldl_cons]
  set pre := (l.take j).foldl (fun w g => w ++ [f w g]) acc
  have hprelen : pre.length = acc.length + j := by
    rw [foldl_append_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hlt : acc.length + j < (pre ++ [f pre l[j]]).length := by
    rw [List.length_append, List.length_singleton, hprelen]
    omega
  rw [foldl_append_getD_lt f (l.drop (j + 1)) (pre ++ [f pre l[j]]) d (acc.length + j) hlt]
  rw [List.getD_eq_getElem?_getD, ← hprelen]
  simp

lemma foldl_append_take_getD {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β)
    (d : β) (j i : ℕ) (hj : j ≤ l.length) (hi : i < acc.length + j) :
    ((l.take j).foldl (fun w g => w ++ [f w g]) acc).getD i d =
      (l.foldl (fun w g => w ++ [f w g]) acc).getD i d := by
  have hsplit : l = l.take j ++ l.drop j := (List.take_append_drop j l).symm
  conv_rhs => rw [hsplit, List.foldl_append]
  have hprelen : ((l.take j).foldl (fun w g => w ++ [f w g]) acc).length = acc.length + j := by
    rw [foldl_append_length, List.length_take, Nat.min_eq_left hj]
  rw [foldl_append_getD_lt f (l.drop j) _ d i (hprelen ▸ hi)]

lemma inputs_eq_pair {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
  have hmem : gateAt C j ∈ C.gates := by
    unfold gateAt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    exact List.getElem_mem hj
  have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 _ hmem
  unfold opnd
  rcases h : (gateAt C j).inputs with _ | ⟨x, _ | ⟨y, _ | _⟩⟩
  · simp [h] at hlen
  · simp [h] at hlen
  · simp
  · simp [h] at hlen

lemma opnd_mem_inputs {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b ∈ (gateAt C j).inputs := by
  rw [inputs_eq_pair hAO hj]
  fin_cases b <;> simp

lemma opnd_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b < n + j :=
  hAO.2.1 j hj _ (opnd_mem_inputs hAO hj b)

lemma mem_insertNew {A : List (List ℕ)} {u v : List ℕ} :
    v ∈ insertNew A u ↔ v ∈ A ∨ v = u := by
  unfold insertNew
  split_ifs with h
  · constructor
    · intro hv; exact Or.inl hv
    · rintro (hv | rfl)
      · exact hv
      · exact h
  · simp

lemma mem_foldl_insertNew {l acc : List (List ℕ)} {v : List ℕ} :
    v ∈ l.foldl insertNew acc ↔ v ∈ acc ∨ v ∈ l := by
  induction l generalizing acc with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, List.mem_cons]
    rw [ih, mem_insertNew]
    tauto

lemma mem_andStep {k : ℕ} {A B : List (List ℕ)} {v : List ℕ} :
    v ∈ andStep k A B ↔ ∃ u ∈ A, ∃ w ∈ B, v = capAdd k u w := by
  unfold andStep
  rw [mem_foldl_insertNew]
  simp only [List.not_mem_nil, false_or, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨u, hu, w, hw, rfl⟩
    exact ⟨u, hu, w, hw, rfl⟩
  · rintro ⟨u, hu, w, hw, rfl⟩
    exact ⟨u, hu, w, hw, rfl⟩

lemma readVectors_length (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) :
    (readVectors C n S k).length = n + C.gates.length := by
  unfold readVectors
  rw [foldl_append_length, List.length_map, List.length_range]

lemma readVectors_getD_ge (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ)
    {w : ℕ} (hw : n + C.gates.length ≤ w) :
    (readVectors C n S k).getD w [] = [] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · rw [readVectors_length]; exact hw

lemma readVectors_getD_lt (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ)
    {w : ℕ} (hw : w < n) :
    (readVectors C n S k).getD w [] = leafVectors S k w := by
  unfold readVectors
  have hlt : w < ((List.range n).map (leafVectors S k)).length := by
    rw [List.length_map, List.length_range]; exact hw
  rw [foldl_append_getD_lt _ C.gates ((List.range n).map (leafVectors S k)) [] w hlt]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
  simp

lemma readVectors_getD_gate {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (S : List ℕ) (k : ℕ) {j : ℕ} (hj : j < C.gates.length) :
    (readVectors C n S k).getD (n + j) [] =
      let ins := (gateAt C j).inputs.map fun i => (readVectors C n S k).getD i []
      match (gateAt C j).op with
      | GateOp.or => ins.foldl (fun acc A => A.foldl insertNew acc) []
      | GateOp.and => ins.foldl (andStep k) [S.map fun _ => 0]
      | _ => [] := by
  let step : List (List (List ℕ)) → Gate → List (List ℕ) := fun R g =>
    match g.op with
    | GateOp.or => (g.inputs.map fun i => R.getD i []).foldl (fun acc A => A.foldl insertNew acc) []
    | GateOp.and => (g.inputs.map fun i => R.getD i []).foldl (andStep k) [S.map fun _ => 0]
    | _ => []
  have hrv : readVectors C n S k =
      C.gates.foldl (fun R g => R ++ [step R g]) ((List.range n).map (leafVectors S k)) := rfl
  rw [hrv]
  have hgate := foldl_append_getD_gate step
    C.gates ((List.range n).map (leafVectors S k)) [] j hj ⟨GateOp.or, []⟩
  rw [List.length_map, List.length_range] at hgate
  rw [hgate]
  have hmap :
      (gateAt C j).inputs.map (fun i =>
        ((C.gates.take j).foldl (fun R g => R ++ [step R g])
          ((List.range n).map (leafVectors S k))).getD i []) =
      (gateAt C j).inputs.map (fun i =>
        (C.gates.foldl (fun R g => R ++ [step R g])
          ((List.range n).map (leafVectors S k))).getD i []) := by
    apply List.map_congr_left
    intro i hi
    have hilt : i < ((List.range n).map (leafVectors S k)).length + j := by
      rw [List.length_map, List.length_range]
      exact hAO.2.1 j hj i hi
    exact foldl_append_take_getD step C.gates ((List.range n).map (leafVectors S k)) [] j i
      (Nat.le_of_lt hj) hilt
  change (match (gateAt C j).op with
    | GateOp.or =>
      ((gateAt C j).inputs.map fun i => _).foldl (fun acc (A : List (List ℕ)) => A.foldl insertNew acc) []
    | GateOp.and =>
      ((gateAt C j).inputs.map fun i => _).foldl (andStep k) [S.map fun _ => 0]
    | _ => []) = _
  rw [hmap]

lemma mem_readVectors_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (S : List ℕ) (k : ℕ) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (v : List ℕ) :
    v ∈ (readVectors C n S k).getD (n + j) [] ↔
      v ∈ (readVectors C n S k).getD (opnd C j 0) [] ∨
      v ∈ (readVectors C n S k).getD (opnd C j 1) [] := by
  rw [readVectors_getD_gate hAO S k hj, hop, inputs_eq_pair hAO hj]
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
  rw [mem_foldl_insertNew, mem_foldl_insertNew]
  simp

lemma mem_readVectors_and {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (S : List ℕ) (k : ℕ) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) (v : List ℕ) :
    v ∈ (readVectors C n S k).getD (n + j) [] ↔
      ∃ u0 ∈ (readVectors C n S k).getD (opnd C j 0) [],
      ∃ u1 ∈ (readVectors C n S k).getD (opnd C j 1) [],
        v = capAdd k (capAdd k (S.map fun _ => 0) u0) u1 := by
  rw [readVectors_getD_gate hAO S k hj, hop, inputs_eq_pair hAO hj]
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
  rw [mem_andStep]
  constructor
  · rintro ⟨t, ht, u1, hu1, rfl⟩
    rw [mem_andStep] at ht
    rcases ht with ⟨z, hz, u0, hu0, rfl⟩
    rw [List.mem_singleton] at hz
    subst hz
    exact ⟨u0, hu0, u1, hu1, rfl⟩
  · rintro ⟨u0, hu0, u1, hu1, rfl⟩
    refine ⟨capAdd k (S.map fun _ => 0) u0, ?_, u1, hu1, rfl⟩
    rw [mem_andStep]
    exact ⟨S.map fun _ => 0, List.mem_singleton_self _, u0, hu0, rfl⟩

lemma readVectors_pair_inv {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {p q : Fin n} (hpq : p ≠ q) :
    ∀ w : ℕ, ∀ v ∈ (readVectors C n [p.val, q.val] 1).getD w [],
      ∃ a b : ℕ, v = [a, b] ∧ a ≤ 2 ∧ b ≤ 2 ∧ 1 ≤ a + b := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro v hv
    by_cases hlt : w < n
    · rw [readVectors_getD_lt C n [p.val, q.val] 1 hlt] at hv
      unfold leafVectors at hv
      split_ifs at hv with hmem
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        simp only [List.mem_singleton, List.map_cons, List.map_nil] at hv
        rcases hmem with rfl | rfl
        · have hne : q.val ≠ p.val := fun h => hpq (Fin.ext h.symm)
          simp only [ite_true, hne, ite_false] at hv
          exact ⟨1, 0, hv, by omega, by omega, by omega⟩
        · have hne : p.val ≠ q.val := fun h => hpq (Fin.ext h)
          simp only [hne, ite_false, ite_true] at hv
          exact ⟨0, 1, hv, by omega, by omega, by omega⟩
      · simp at hv
    · by_cases hge : n + C.gates.length ≤ w
      · rw [readVectors_getD_ge C n [p.val, q.val] 1 hge] at hv
        simp at hv
      · set j := w - n
        have hw : w = n + j := by omega
        have hj : j < C.gates.length := by omega
        have hmem : gateAt C j ∈ C.gates := by
          unfold gateAt
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
          exact List.getElem_mem hj
        rw [hw] at hv
        rcases hAO.1 _ hmem with hop | hop
        · rw [mem_readVectors_and hAO [p.val, q.val] 1 hj hop] at hv
          rcases hv with ⟨u0, hu0, u1, hu1, rfl⟩
          rcases ih _ (hw ▸ opnd_lt hAO hj 0) u0 hu0 with ⟨a0, b0, rfl, ha0, hb0, hs0⟩
          rcases ih _ (hw ▸ opnd_lt hAO hj 1) u1 hu1 with ⟨a1, b1, rfl, ha1, hb1, hs1⟩
          refine ⟨min (min (0 + a0) 2 + a1) 2, min (min (0 + b0) 2 + b1) 2, ?_,
            Nat.min_le_right _ _, Nat.min_le_right _ _, by omega⟩
          simp [capAdd]
        · rw [mem_readVectors_or hAO [p.val, q.val] 1 hj hop] at hv
          rcases hv with h0 | h1
          · exact ih _ (hw ▸ opnd_lt hAO hj 0) v h0
          · exact ih _ (hw ▸ opnd_lt hAO hj 1) v h1

def edgeTrue {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : Prop :=
  ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true

lemma graph_true {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {x : Fin n → Bool} : graphFun G ∅ x = true ↔ edgeTrue G x := by
  simp [graphFun, edgeTrue]

lemma edge_true_pair {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n} :
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

def dirty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : ℕ) : Prop :=
  (gateAt C j).op = GateOp.and ∧ ¬ BelowF G C j

def badHit {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (j : ℕ) (p : Fin n × Fin n) : Prop :=
  G.Adj p.1 p.2 ∧ readsAtMost C n [p.1.val, p.2.val] 1 = false ∧
    gateVal n C j (pairInput p.1 p.2) = true

noncomputable def selectEdge {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (fallback : Fin n × Fin n) (j : ℕ) : Fin n × Fin n := by
  classical
  exact if h : ∃ p, badHit G C j p then h.choose else fallback

lemma select_hit {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    {fallback : Fin n × Fin n} {j : ℕ} {p : Fin n × Fin n}
    (h : badHit G C j p) : badHit G C j (selectEdge G C fallback j) := by
  classical
  have hex : ∃ p, badHit G C j p := ⟨p, h⟩
  simpa only [selectEdge, dite_eq_left hex] using hex.choose_spec

lemma select_adj {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    {fallback : Fin n × Fin n} (hf : G.Adj fallback.1 fallback.2) (j : ℕ) :
    G.Adj (selectEdge G C fallback j).1 (selectEdge G C fallback j).2 := by
  classical
  by_cases h : ∃ p, badHit G C j p
  · exact (select_hit (fallback := fallback) h.choose_spec).1
  · simpa only [selectEdge, dite_eq_right h] using hf

noncomputable def repair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (pick : ℕ → Fin n × Fin n) : Circuit := by
  classical
  exact ⟨(List.range C.gates.length).map fun j =>
    if dirty G C j then ⟨GateOp.and, [(pick j).1.val, (pick j).2.val]⟩ else gateAt C j,
    C.output⟩

lemma repair_len {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (pick : ℕ → Fin n × Fin n) :
    (repair G C pick).gates.length = C.gates.length := by
  simp [repair]

lemma repair_gate {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (pick : ℕ → Fin n × Fin n) {j : ℕ} (hj : j < C.gates.length) :
    gateAt (repair G C pick) j =
      @ite Gate (dirty G C j) (Classical.propDecidable _)
        ⟨GateOp.and, [(pick j).1.val, (pick j).2.val]⟩ (gateAt C j) := by
  classical
  have hj' : j < (repair G C pick).gates.length := by rwa [repair_len]
  rw [gateAt_eq hj']
  simp [repair]

lemma repair_ao {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
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

lemma repair_kept {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (pick : ℕ → Fin n × Fin n) {j : ℕ} (hj : j < C.gates.length)
    (h : ¬ dirty G C j) : gateAt (repair G C pick) j = gateAt C j := by
  classical
  rw [repair_gate pick hj, ite_eq_right h]

lemma repair_replaced_val {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
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

lemma repair_compare {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
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

lemma repair_read_vector {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hC : IsAO2 n C) (pick : ℕ → Fin n × Fin n)
    {u v : Fin n} (hne : u ≠ v) :
    ∀ w a b : ℕ, a ≤ 1 → b ≤ 1 →
      [a, b] ∈ (readVectors C n [u.val, v.val] 1).getD w [] →
      (a + b ≤ 1 ∨ ∀ x : Fin n → Bool, val C (List.ofFn x) w = true → graphFun G ∅ x = true) →
      val (repair G C pick) (List.ofFn (pairInput u v)) w = true := by
  let D := repair G C pick
  let xs := List.ofFn (pairInput u v)
  have hx : xs.length = n := List.length_ofFn
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro a b ha hb hv hsafe
    by_cases hi : w < n
    · rw [readVectors_getD_lt C n _ 1 hi] at hv
      unfold leafVectors at hv
      split_ifs at hv with he
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl <;> simp [val_ofFn, pairInput]
      · simp at hv
    by_cases hj : w < n + C.gates.length
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hi)
      have hj' : j < C.gates.length := by omega
      have hjD : j < D.gates.length := by rwa [repair_len]
      rcases hC.1 _ (gateAt_mem hj') with hop | hop
      · rw [mem_readVectors_and hC _ _ hj' hop] at hv
        obtain ⟨x, hxv, y, hyv, hsum⟩ := hv
        have h0 := opnd_lt hC hj' 0
        have h1 := opnd_lt hC hj' 1
        obtain ⟨a₀, b₀, rfl, ha₀, hb₀, hn₀⟩ := readVectors_pair_inv hC hne _ _ hxv
        obtain ⟨a₁, b₁, rfl, ha₁, hb₁, hn₁⟩ := readVectors_pair_inv hC hne _ _ hyv
        simp only [capAdd, List.map_cons, List.map_nil, List.zipWith_cons_cons,
          List.zipWith_nil_right, List.cons.injEq, and_true] at hsum
        have htotal : a = a₀ + a₁ ∧ b = b₀ + b₁ := by omega
        have hbelow : BelowF G C j := by
          intro z hz
          exact (hsafe.resolve_left (by omega)) z hz
        have hg : gateAt D j = gateAt C j :=
          repair_kept pick hj' (fun hd => hd.2 hbelow)
        change val D xs (n + j) = true
        rw [val_and hx hjD (by rwa [hg]), hg, inputs_eq_pair hC hj']
        intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · exact ⟨h0, ih _ h0 a₀ b₀ (by omega) (by omega) hxv (Or.inl (by omega))⟩
        · exact ⟨h1, ih _ h1 a₁ b₁ (by omega) (by omega) hyv (Or.inl (by omega))⟩
      · rw [mem_readVectors_or hC _ _ hj' hop] at hv
        have hg : gateAt D j = gateAt C j :=
          repair_kept pick hj' (fun hd => by cases hop.symm.trans hd.1)
        change val D xs (n + j) = true
        rw [val_or hx hjD (by rwa [hg]), hg]
        have step (k : Fin 2) (hk : [a, b] ∈
            (readVectors C n [u.val, v.val] 1).getD (opnd C j k) []) :
            ∃ i ∈ (gateAt C j).inputs, i < n + j ∧ val D xs i = true := by
          have hm := opnd_mem_inputs hC hj' k
          have lt := opnd_lt hC hj' k
          refine ⟨_, hm, lt, ih _ lt a b ha hb hk (hsafe.imp_right ?_)⟩
          intro h x hval
          exact h x ((val_or (by simp) hj' hop).2 ⟨_, hm, lt, hval⟩)
        exact hv.elim (step 0) (step 1)
    · rw [readVectors_getD_ge C n _ 1 (by omega)] at hv
      simp at hv

lemma repair_read_one {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hC : IsAO2 n C) (pick : ℕ → Fin n × Fin n)
    (hc : circuitFun n C = graphFun G ∅) {u v : Fin n} (hne : u ≠ v)
    (hread : readsAtMost C n [u.val, v.val] 1 = true) :
    circuitFun n (repair G C pick) (pairInput u v) = true := by
  obtain ⟨l, hl, hle⟩ := List.any_eq_true.1 hread
  obtain ⟨a, b, rfl, _, _, _⟩ := readVectors_pair_inv hC hne _ _ hl
  have hbound : a ≤ 1 ∧ b ≤ 1 := by simpa using hle
  exact repair_read_vector hC pick hne _ _ _ hbound.1 hbound.2 hl (Or.inr (by
    intro x hx
    rw [← hc]
    exact hx))

lemma repaired_graph {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hC : IsAO2 n C) (hc : circuitFun n C = graphFun G ∅)
    (fallback : Fin n × Fin n) (hf : G.Adj fallback.1 fallback.2)
    (hu : ∀ j < C.gates.length, dirty G C j →
      ∀ p q, badHit G C j p → badHit G C j q → s(p.1, p.2) = s(q.1, q.2)) :
    let pick := selectEdge G C fallback
    let D := repair G C pick
    (∀ j < D.gates.length, (gateAt D j).op = GateOp.and → BelowF G D j) ∧
    (∀ u v, G.Adj u v → circuitFun n D (pairInput u v) = true) ∧
    (∀ x : Fin n → Bool, circuitFun n D x = true → graphFun G ∅ x = true) := by
  intro pick D
  have hp : ∀ j, G.Adj (pick j).1 (pick j).2 := select_adj hf
  have hreflect (x : Fin n → Bool) (hn : graphFun G ∅ x ≠ true) (w : ℕ) :
      val D (List.ofFn x) w = true → val C (List.ofFn x) w = true :=
    repair_compare hC pick x false (by
      intro j hj hd hval
      have hpv := (repair_replaced_val pick hj hd x).1 hval
      exact (hn (graph_true.2 ⟨_, _, hp j, hpv.1, hpv.2⟩)).elim) w
  refine ⟨?_, ?_, ?_⟩
  · intro j hj hop x hv
    have hj' : j < C.gates.length := by rwa [repair_len] at hj
    by_cases hd : dirty G C j
    · have h := (repair_replaced_val pick hj' hd x).1 hv
      exact graph_true.2 ⟨_, _, hp j, h.1, h.2⟩
    · have hop' : (gateAt C j).op = GateOp.and := by
        rwa [repair_kept pick hj' hd] at hop
      by_contra hn
      have hbelow : BelowF G C j := by
        by_contra h
        exact hd ⟨hop', h⟩
      exact hn (hbelow x (hreflect x hn (n + j) hv))
  · intro u v huv
    cases hread : readsAtMost C n [u.val, v.val] 1
    · have htrue : circuitFun n C (pairInput u v) = true := by
        rw [hc]
        exact graph_true.2 (edge_true_pair.2 huv)
      exact repair_compare hC pick (pairInput u v) true (by
        intro j hj hd hv
        have hhit : badHit G C j (u, v) := ⟨huv, hread, hv⟩
        have hs : s((pick j).1, (pick j).2) = s(u, v) :=
          hu j hj hd _ _ (select_hit (fallback := fallback) hhit) hhit
        apply (repair_replaced_val pick hj hd _).2
        rcases Sym2.eq_iff.1 hs with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> simp [h₁, h₂, pairInput]
      ) C.output htrue
    · exact repair_read_one hC pick hc (G.ne_of_adj huv) hread
  · intro x hx
    by_contra hn
    have h := hreflect x hn C.output hx
    change circuitFun n C x = true at h
    rw [hc] at h
    exact hn h

lemma sorted_edges {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
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

lemma main_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hfour : NoFourCycle G) (hne : G.edgeFinset.Nonempty)
    (hC : IsAO2 n C) (hc : circuitFun n C = graphFun G ∅)
    (hu : ∀ j < C.gates.length, dirty G C j →
      ∀ p q, badHit G C j p → badHit G C j q → s(p.1, p.2) = s(q.1, q.2)) :
    ∃ T : Finset (Fin n), G.IsVertexCover ↑T ∧ G.edgeFinset.card + T.card ≤ C.size + 1 := by
  classical
  obtain ⟨e, he⟩ := hne
  induction e using Sym2.ind with
  | _ u v =>
    have hadj := SimpleGraph.mem_edgeFinset.1 he
    let pick := selectEdge G C (u, v)
    let D := repair G C pick
    have hD : IsAO2 n D := repair_ao hC pick
    obtain ⟨hclean, hpair, hfun⟩ := repaired_graph hC hc (u, v) hadj hu
    have hm : Monotone2 D := by
      intro g hg
      exact ⟨by simpa using hD.1 g hg, (hD.2.2 g hg).le⟩
    obtain ⟨E, hcard, hE⟩ := sorted_edges G
    obtain ⟨T, hcover, hT, hbound⟩ := graph_budget (C := D) G u hm hD.2.1
      (fun j hj hop a b ht => edge_true_pair.1 (graph_true.1 (hclean j hj.1 hop _ ht)))
      (by
        intro j hj hop
        cases h : gateVal n D j (fun _ => false)
        · rfl
        · obtain ⟨a, b, hab, ha, hb⟩ := graph_true.1 (hclean j hj.1 hop _ h)
          cases ha)
      (fun _ _ _ _ => no_four_cycle hfour)
      (by
        apply Finset.eq_empty_iff_forall_notMem.2
        intro a ha
        have hh : circuitFun n D (pairInput a a) = true := mem_support.1 ha
        exact G.irrefl (edge_true_pair.1 (graph_true.1 (hfun _ hh))))
      hpair E hE
    refine ⟨T, ?_, ?_⟩
    · exact hcover
    · have hlen : D.size = C.size := repair_len G C pick
      omega


lemma clean_certificate {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsAO2 n C) (hc : circuitFun n C = graphFun G ∅)
    (fallback : Fin n × Fin n) (hf : G.Adj fallback.1 fallback.2)
    (hu : ∀ j < C.gates.length, dirty G C j →
      ∀ p q, badHit G C j p → badHit G C j q → s(p.1, p.2) = s(q.1, q.2)) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size = C.size ∧ circuitFun n D = circuitFun n C ∧
      ∀ j < D.gates.length, (gateAt D j).op = GateOp.and → BelowF G D j := by
  classical
  let pick := selectEdge G C fallback
  let D := repair G C pick
  have hD : IsAO2 n D := repair_ao hC pick
  obtain ⟨hclean, hpairs, hsound⟩ := repaired_graph hC hc fallback hf hu
  have hm : Monotone2 D := by
    intro g hg
    exact ⟨by simpa using hD.1 g hg, (hD.2.2 g hg).le⟩
  have hsame : circuitFun n D = graphFun G ∅ := by
    funext x
    apply Bool.eq_iff_iff.mpr
    constructor
    · exact hsound x
    · intro hx
      obtain ⟨u, v, huv, hu, hv⟩ := graph_true.mp hx
      have hmono : ∀ w, pairInput u v w = true → x w = true := by
        intro w hw
        simp only [pairInput, decide_eq_true_eq] at hw
        rcases hw with rfl | rfl
        · exact hu
        · exact hv
      exact pair_mono hm hmono D.output (hpairs u v huv)
  exact ⟨D, hD, repair_len G C pick, hsame.trans hc.symm, hclean⟩

lemma bad_hit_collision_of_cover_lower_bound {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hfour : NoFourCycle G) (hne : G.edgeFinset.Nonempty)
    (hC : IsAO2 n C) (hc : circuitFun n C = graphFun G ∅)
    (k : ℕ) (hcover : ∀ T : Finset (Fin n), G.IsVertexCover ↑T → k ≤ T.card)
    (hsmall : C.size + 1 < G.edgeFinset.card + k) :
    ∃ j < C.gates.length, dirty G C j ∧ ∃ p q,
      badHit G C j p ∧ badHit G C j q ∧ s(p.1, p.2) ≠ s(q.1, q.2) := by
  classical
  by_contra h
  have hu : ∀ j < C.gates.length, dirty G C j →
      ∀ p q, badHit G C j p → badHit G C j q → s(p.1, p.2) = s(q.1, q.2) := by
    intro j hj hd p q hp hq
    by_contra he
    exact h ⟨j, hj, hd, p, q, hp, hq, he⟩
  obtain ⟨T, hT, hbound⟩ := main_bound G C hfour hne hC hc hu
  have hk := hcover T hT
  omega

end Repair

namespace StructuralAbsorption

open PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover

lemma monotone_source_witness {α β : Type*} [Fintype α] [DecidableEq α]
    (A : β → Finset α) (S : α → Prop) [DecidablePred S]
    (f : (β → Bool) → Bool) (hmono : Monotone f) (x : α)
    (hx : f (fun i => decide (x ∈ A i)) = true)
    (hbelow : ∀ v : α → Bool,
      f (fun i => decide (∃ p ∈ A i, v p = true)) = true →
      ∃ p, S p ∧ v p = true) :
    ∃ i, x ∈ A i ∧ ∀ p ∈ A i, S p := by
  classical
  by_contra h
  push Not at h
  let v : α → Bool := fun p => decide (¬ S p)
  have hle : (fun i => decide (x ∈ A i)) ≤
      (fun i => decide (∃ p ∈ A i, v p = true)) := by
    intro i
    by_cases hxi : x ∈ A i
    · obtain ⟨p, hp, hnot⟩ := h i hxi
      have hex : ∃ p ∈ A i, v p = true := ⟨p, hp, by simp [v, hnot]⟩
      simp [hxi, hex]
    · simp [hxi]
  have hf : f (fun i => decide (∃ p ∈ A i, v p = true)) = true := by
    exact le_antisymm (Bool.le_true _) (by simpa only [hx] using hmono hle)
  obtain ⟨p, hSp, hvp⟩ := hbelow v hf
  have hnSp : ¬ S p := by simpa [v] using hvp
  exact hnSp hSp

lemma common_center_eq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hC4 : NoFourCycle G) {x y a w : Fin n} (hxy : x ≠ y)
    (hax : G.Adj a x) (hay : G.Adj a y)
    (hwx : G.Adj w x) (hwy : G.Adj w y) : w = a := by
  apply Finset.card_le_one.mp (hC4 x y hxy) w
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hwx.symm, hwy.symm⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hax.symm, hay.symm⟩

lemma monotone_shared_star_center {n : ℕ} {ι : Type*}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hC4 : NoFourCycle G)
    (A : ι → Finset (Fin n)) (center : ι → Fin n)
    (hstar : ∀ i p, p ∈ A i → G.Adj (center i) p)
    (hlarge : ∀ i, 1 < (A i).card) (f : (ι → Bool) → Bool) (hmono : Monotone f)
    (x w : Fin n) (hx : f (fun i => decide (x ∈ A i)) = true)
    (hbelow : ∀ v : Fin n → Bool,
      f (fun i => decide (∃ p ∈ A i, v p = true)) = true →
      ∃ p, G.Adj w p ∧ v p = true) :
    ∃ i, x ∈ A i ∧ center i = w := by
  obtain ⟨i, hxi, hsub⟩ := monotone_source_witness A (G.Adj w) f hmono x hx (by
    intro v hv
    apply hbelow v
    convert hv using 1
    congr 1
    funext i
    simp)
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (hlarge i)
  exact ⟨i, hxi, (common_center_eq G hC4 hpq
    (hstar i p hp) (hstar i q hq) (hsub p hp) (hsub q hq)).symm⟩

lemma shared_star_computation_center {n : ℕ} {ι : Type*}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hC4 : NoFourCycle G)
    (A : ι → Finset (Fin n)) (center : ι → Fin n)
    (hstar : ∀ i p, p ∈ A i → G.Adj (center i) p)
    (hlarge : ∀ i, 1 < (A i).card)
    (hind : ∀ p q : Fin n, (∃ i, p ∈ A i) → (∃ j, q ∈ A j) → ¬ G.Adj p q)
    (f : (ι → Bool) → Bool) (hmono : Monotone f) (x w : Fin n)
    (hwoutside : ∀ i, w ∉ A i) (hx : f (fun i => decide (x ∈ A i)) = true)
    (hbelow : ∀ v : Fin n → Bool,
      f (fun i => decide (∃ p ∈ A i, v p = true)) = true → v w = true →
      graphFun G ∅ v = true) :
    ∃ i, x ∈ A i ∧ center i = w := by
  classical
  refine monotone_shared_star_center G hC4 A center hstar hlarge f hmono x w hx ?_
  intro v hv
  let u : Fin n → Bool := fun p => decide (p = w) || (v p && decide (∃ i, p ∈ A i))
  have hu : (fun i => decide (∃ p ∈ A i, u p = true)) =
      (fun i => decide (∃ p ∈ A i, v p = true)) := by
    funext i
    apply Bool.decide_congr
    constructor
    · rintro ⟨p, hp, hup⟩
      have hpw : p ≠ w := fun heq => hwoutside i (heq ▸ hp)
      exact ⟨p, hp, by simpa [u, hpw, show ∃ j, p ∈ A j from ⟨i, hp⟩] using hup⟩
    · rintro ⟨p, hp, hvp⟩
      exact ⟨p, hp, by simp [u, hvp, show ∃ j, p ∈ A j from ⟨i, hp⟩]⟩
  have hfu : f (fun i => decide (∃ p ∈ A i, u p = true)) = true := by
    rw [hu]
    exact hv
  have hgraph := hbelow u hfu (by simp [u])
  have hedge : ∃ p q : Fin n, G.Adj p q ∧ u p = true ∧ u q = true := by
    simpa [graphFun] using hgraph
  obtain ⟨p, q, hpq, hup, huq⟩ := hedge
  have hp : p = w ∨ v p = true ∧ ∃ i, p ∈ A i := by simpa [u] using hup
  have hq : q = w ∨ v q = true ∧ ∃ j, q ∈ A j := by simpa [u] using huq
  rcases hp with rfl | ⟨hvp, hp⟩ <;> rcases hq with rfl | ⟨hvq, hq⟩
  · exact (G.loopless.irrefl _ hpq).elim
  · exact ⟨q, hpq, hvq⟩
  · exact ⟨p, hpq.symm, hvp⟩
  · exact (hind p q hp hq hpq).elim

lemma shared_or_absorption_center {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hC4 : NoFourCycle G) {x y z a b w : Fin n}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : ¬ G.Adj y z)
    (hax : G.Adj a x) (hay : G.Adj a y)
    (hbx : G.Adj b x) (hbz : G.Adj b z) (hwx : G.Adj w x)
    (hbelow : ∀ v : Fin n → Bool,
      ((v x || v y) && (v x || v z) && v w) = true → graphFun G ∅ v = true) :
    w = a ∨ w = b := by
  classical
  by_contra hne
  have hwa : w ≠ a := fun h => hne (Or.inl h)
  have hwb : w ≠ b := fun h => hne (Or.inr h)
  have hwy : ¬ G.Adj w y := fun h =>
    hwa (common_center_eq G hC4 hxy hax hay hwx h)
  have hwz : ¬ G.Adj w z := fun h =>
    hwb (common_center_eq G hC4 hxz hbx hbz hwx h)
  let v : Fin n → Bool := fun t => decide (t = y ∨ t = z ∨ t = w)
  have hvy : v y = true := by simp [v]
  have hvz : v z = true := by simp [v]
  have hvw : v w = true := by simp [v]
  have htrue := hbelow v (by simp [hvy, hvz, hvw])
  have hex : ∃ u t : Fin n, G.Adj u t ∧ v u = true ∧ v t = true := by
    simpa [graphFun] using htrue
  obtain ⟨u, t, hut, hu, ht⟩ := hex
  have hu' : u = y ∨ u = z ∨ u = w := by simpa [v] using hu
  have ht' : t = y ∨ t = z ∨ t = w := by simpa [v] using ht
  rcases hu' with rfl | rfl | rfl <;> rcases ht' with rfl | rfl | rfl
  · exact G.loopless.irrefl _ hut
  · exact hyz hut
  · exact hwy hut.symm
  · exact hyz hut.symm
  · exact G.loopless.irrefl _ hut
  · exact hwz hut.symm
  · exact hwy hut
  · exact hwz hut
  · exact G.loopless.irrefl _ hut

end StructuralAbsorption

namespace ReducedCheck

def avoidingRight {n m : ℕ} (I : Fin n → Fin m → Prop) [DecidableRel I]
    (P : Finset (Fin n)) : Finset (Fin m) :=
  Finset.univ.filter fun l => ∀ p ∈ P, ¬ I p l

def closureLeft {n m : ℕ} (I : Fin n → Fin m → Prop) [DecidableRel I]
    (P : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun p => ∀ l ∈ avoidingRight I P, ¬ I p l

lemma mem_avoidingRight {n m : ℕ} (I : Fin n → Fin m → Prop) [DecidableRel I]
    (P : Finset (Fin n)) (l : Fin m) :
    l ∈ avoidingRight I P ↔ ∀ p ∈ P, ¬ I p l := by
  simp [avoidingRight]

lemma mem_closureLeft {n m : ℕ} (I : Fin n → Fin m → Prop) [DecidableRel I]
    (P : Finset (Fin n)) (p : Fin n) :
    p ∈ closureLeft I P ↔ ∀ l ∈ avoidingRight I P, ¬ I p l := by
  simp [closureLeft]

lemma subset_closureLeft {n m : ℕ} (I : Fin n → Fin m → Prop) [DecidableRel I]
    (P : Finset (Fin n)) : P ⊆ closureLeft I P := by
  intro p hp
  apply (mem_closureLeft I P p).2
  intro l hl
  exact (mem_avoidingRight I P l).1 hl p hp

lemma avoidingRight_closureLeft {n m : ℕ} (I : Fin n → Fin m → Prop)
    [DecidableRel I] (P : Finset (Fin n)) :
    avoidingRight I (closureLeft I P) = avoidingRight I P := by
  ext l
  constructor
  · intro hl
    apply (mem_avoidingRight I P l).2
    intro p hp
    exact (mem_avoidingRight I (closureLeft I P) l).1 hl p
      (subset_closureLeft I P hp)
  · intro hl
    apply (mem_avoidingRight I (closureLeft I P) l).2
    intro p hp
    exact (mem_closureLeft I P p).1 hp l hl

lemma closureLeft_idem {n m : ℕ} (I : Fin n → Fin m → Prop) [DecidableRel I]
    (P : Finset (Fin n)) : closureLeft I (closureLeft I P) = closureLeft I P := by
  ext p
  simp only [mem_closureLeft, avoidingRight_closureLeft]

def independentInput {n m : ℕ} (I : Fin n → Fin m → Prop) [DecidableRel I]
    (P : Finset (Fin n)) : Sum (Fin n) (Fin m) → Bool :=
  Sum.elim (fun p => decide (p ∈ P)) (fun l => decide (l ∈ avoidingRight I P))

def edgeInput {n m : ℕ} (p : Fin n) (l : Fin m) : Sum (Fin n) (Fin m) → Bool :=
  Sum.elim (fun a => decide (a = p)) (fun b => decide (b = l))

lemma exact_certificate {n m : ℕ} (I : Fin n → Fin m → Prop) [DecidableRel I]
    (f : (Sum (Fin n) (Fin m) → Bool) → Bool)
    (hmono : ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true)
    (hpos : ∀ p l, I p l → f (edgeInput p l) = true)
    (hneg : ∀ P : Finset (Fin n), closureLeft I P = P →
      f (independentInput I P) = false) :
    ∀ z, f z = decide (∃ p l, I p l ∧ z (Sum.inl p) = true ∧
      z (Sum.inr l) = true) := by
  intro z
  by_cases h : ∃ p l, I p l ∧ z (Sum.inl p) = true ∧ z (Sum.inr l) = true
  · rw [decide_eq_true h]
    obtain ⟨p, l, hI, hp, hl⟩ := h
    apply hmono (edgeInput p l) z _ (hpos p l hI)
    intro i hi
    cases i with
    | inl a =>
      have ha : a = p := by simpa [edgeInput] using hi
      simpa [ha] using hp
    | inr b =>
      have hb : b = l := by simpa [edgeInput] using hi
      simpa [hb] using hl
  · rw [decide_eq_false h]
    let P := Finset.univ.filter fun p : Fin n => z (Sum.inl p) = true
    have hext : ∀ i, z i = true → independentInput I (closureLeft I P) i = true := by
      intro i hi
      cases i with
      | inl p =>
        apply decide_eq_true
        exact subset_closureLeft I P (by simp [P, hi])
      | inr l =>
        apply decide_eq_true
        rw [avoidingRight_closureLeft]
        apply (mem_avoidingRight I P l).2
        intro p hp hI
        have hp' : z (Sum.inl p) = true := (Finset.mem_filter.1 hp).2
        exact h ⟨p, l, hI, hp', hi⟩
    cases hf : f z with
    | false => rfl
    | true =>
      have ht := hmono z (independentInput I (closureLeft I P)) hext hf
      rw [hneg _ (closureLeft_idem I P)] at ht
      cases ht

def fanoIncidence (p l : Fin 7) : Prop :=
  (p.val + 7 - l.val) % 7 = 0 ∨ (p.val + 7 - l.val) % 7 = 1 ∨
    (p.val + 7 - l.val) % 7 = 3

abbrev fanoDecidable : DecidableRel fanoIncidence := by
  intro p l
  unfold fanoIncidence
  infer_instance

def fanoClosedPoints : Finset (Finset (Fin 7)) :=
  @Finset.filter (Finset (Fin 7))
    (fun P => @closureLeft 7 7 fanoIncidence fanoDecidable P = P)
    (fun _ => inferInstance) Finset.univ.powerset

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma fano_closed_count : fanoClosedPoints.card = 37 := by
  decide +kernel

set_option maxRecDepth 10000 in
lemma fano_edge_count :
    (@Finset.filter (Fin 7 × Fin 7) (fun e => fanoIncidence e.1 e.2)
      (fun e => fanoDecidable e.1 e.2) Finset.univ).card = 21 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma fano_plane :
    (∀ l : Fin 7, (@Finset.filter (Fin 7) (fun p => fanoIncidence p l)
      (fun p => fanoDecidable p l) Finset.univ).card = 3) ∧
    (∀ p p' : Fin 7, p ≠ p' → ∃! l : Fin 7,
      fanoIncidence p l ∧ fanoIncidence p' l) := by
  unfold fanoIncidence ExistsUnique
  decide +kernel

end ReducedCheck


namespace CircuitCheckWrapper

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.Outside.L_meta_2583.ReducedCheck

def liftInput {n m : ℕ} (z : Sum (Fin n) (Fin m) → Bool) : Fin (n + m) → Bool :=
  Fin.addCases (fun p => z (Sum.inl p)) (fun l => z (Sum.inr l))

def lowerInput {n m : ℕ} (z : Fin (n + m) → Bool) : Sum (Fin n) (Fin m) → Bool :=
  Sum.elim (fun p => z (Fin.castAdd m p)) (fun l => z (Fin.natAdd n l))

lemma lift_lower {n m : ℕ} (z : Fin (n + m) → Bool) :
    liftInput (lowerInput z) = z := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro p
    simp [liftInput, lowerInput]
  · intro l
    simp [liftInput, lowerInput]

lemma ao2_monotone2 {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) : Monotone2 C := by
  intro g hg
  refine ⟨?_, (hAO.2.2 g hg).le⟩
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hAO.1 g hg

lemma circuitFun_lift_mono {n m : ℕ} {C : Circuit} (hAO : IsAO2 (n + m) C)
    {x y : Sum (Fin n) (Fin m) → Bool}
    (hxy : ∀ i, x i = true → y i = true)
    (hx : circuitFun (n + m) C (liftInput x) = true) :
    circuitFun (n + m) C (liftInput y) = true := by
  apply PEqualNP.Outside.L_meta_2583.Repair.pair_mono (ao2_monotone2 hAO) ?_ C.output hx
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro p hp
    simpa [liftInput] using hxy (Sum.inl p) (by simpa [liftInput] using hp)
  · intro l hl
    simpa [liftInput] using hxy (Sum.inr l) (by simpa [liftInput] using hl)

lemma ao2_exact_certificate {n m : ℕ} (I : Fin n → Fin m → Prop) [DecidableRel I]
    (C : Circuit) (hAO : IsAO2 (n + m) C)
    (hpos : ∀ p l, I p l → circuitFun (n + m) C (liftInput (edgeInput p l)) = true)
    (hneg : ∀ P : Finset (Fin n), closureLeft I P = P →
      circuitFun (n + m) C (liftInput (independentInput I P)) = false) :
    ∀ z : Fin (n + m) → Bool,
      circuitFun (n + m) C z = decide (∃ p l, I p l ∧
        z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true) := by
  have hcert := exact_certificate I
    (fun v => circuitFun (n + m) C (liftInput v))
    (fun x y hxy hx => circuitFun_lift_mono hAO hxy hx) hpos hneg
  intro z
  have hz := hcert (lowerInput z)
  rw [lift_lower] at hz
  exact hz.trans (Bool.decide_congr (by rfl))

end CircuitCheckWrapper


namespace PurePointBudget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_2583.Repair

noncomputable def orPool {n : ℕ} (C : Circuit) (x : Fin n → Bool) (m : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range m).filter fun k => (gateAt C k).op = GateOp.or ∧
    1 < (singletonSupport n C (n + k)).card ∧ val C (List.ofFn x) (n + k) = false

lemma mem_orPool {n : ℕ} {C : Circuit} {x : Fin n → Bool} {m k : ℕ} :
    k ∈ orPool C x m ↔ k < m ∧ (gateAt C k).op = GateOp.or ∧
      1 < (singletonSupport n C (n + k)).card ∧ val C (List.ofFn x) (n + k) = false := by
  classical
  simp [orPool]

lemma frontier_budget {n : ℕ} {C : Circuit} (hm : Monotone2 C) (rb : ReadsBack n C)
    (x : Fin n → Bool) (m : ℕ) (roots : Finset ℕ)
    (hvalid : ∀ w ∈ roots, w < n + C.gates.length)
    (hfalse : ∀ w ∈ roots, val C (List.ofFn x) w = false)
    (hbound : ∀ w ∈ roots, 1 < (singletonSupport n C w).card → w < n + m) :
    (roots.biUnion (singletonSupport n C)).card ≤ roots.card + (orPool C x m).card := by
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
      _ = _ := by simp [orPool]
  | succ m ih =>
    have hpool : orPool C x m ⊆ orPool C x (m + 1) := by
      intro k hk
      obtain ⟨hk, hh⟩ := mem_orPool.1 hk
      exact mem_orPool.2 ⟨by omega, hh⟩
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
        have hfirst := (Finset.card_le_card hsub).trans (ih T hTvalid hTfalse hTbound)
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
        have hfirst := (Finset.card_le_card hsub).trans (ih T hTvalid hTfalse hTbound)
        have hTcard := Finset.card_union_le (roots.erase (n + m)) P
        have herase := Finset.card_erase_add_one hmem
        have hPc : P.card ≤ 2 := (Finset.card_filter_le _ _).trans (input_card hm hmC)
        have hnew : m ∈ orPool C x (m + 1) :=
          mem_orPool.2 ⟨by omega, hor, hlarge, hfalse _ hmem⟩
        have hn : m ∉ orPool C x m := fun h => (Nat.lt_irrefl m) (mem_orPool.1 h).1
        have hsubpool : insert m (orPool C x m) ⊆ orPool C x (m + 1) :=
          Finset.insert_subset_iff.2 ⟨hnew, hpool⟩
        have hinc := Finset.card_le_card hsubpool
        rw [Finset.card_insert_of_notMem hn] at hinc
        change T.card ≤ (roots.erase (n + m)).card + P.card at hTcard
        omega
    · have hnew : ∀ w ∈ roots, 1 < (singletonSupport n C w).card → w < n + m := by
        intro w hw hw'
        have hlt := hbound w hw hw'
        have hne : w ≠ n + m := fun he => htop ⟨he ▸ hw, he ▸ hw'⟩
        omega
      have hfirst := ih roots hvalid hfalse hnew
      have hinc := Finset.card_le_card hpool
      omega

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

lemma computes_or_budget {n : ℕ} {C : Circuit} (hm : Monotone2 C) (rb : ReadsBack n C)
    (S : Finset (Fin n)) (w : ℕ) (hvalid : w < n + C.gates.length)
    (hcomp : ∀ z : Fin n → Bool, val C (List.ofFn z) w = decide (∃ p ∈ S, z p = true)) :
    S.card - 1 ≤ (orPool C (complementInput S) C.gates.length).card := by
  classical
  have hs : singletonSupport n C w = S := by
    ext p
    rw [mem_support, hcomp]
    simp [pairInput, eq_comm]
  have hf : val C (List.ofFn (complementInput S)) w = false := by
    rw [hcomp]
    simp [complementInput]
  have hb := frontier_budget hm rb (complementInput S) C.gates.length {w}
    (by simpa using hvalid) (by simpa using hf)
    (by intro u hu _; simpa only [Finset.mem_singleton.1 hu] using hvalid)
  simp only [Finset.singleton_biUnion, hs, Finset.card_singleton] at hb
  omega

noncomputable def orGates (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter fun k => (gateAt C k).op = GateOp.or

lemma multioutput_or_budget {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {C : Circuit} (hm : Monotone2 C) (rb : ReadsBack n C)
    (S : ι → Finset (Fin n)) (output : ι → ℕ)
    (hvalid : ∀ i, output i < n + C.gates.length)
    (hcomp : ∀ i (z : Fin n → Bool),
      val C (List.ofFn z) (output i) = decide (∃ p ∈ S i, z p = true))
    (hpair : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) :
    (∑ i, ((S i).card - 1)) ≤ (orGates C).card := by
  classical
  let pools := fun i => orPool C (complementInput (S i)) C.gates.length
  have hdis : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint pools := by
    intro i _ j _ hij
    exact orPool_disjoint hm (hpair i j hij) C.gates.length
  have hsub : Finset.univ.biUnion pools ⊆ orGates C := by
    intro k hk
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.1 hk
    obtain ⟨hk, hop, _⟩ := mem_orPool.1 hi
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hk, hop⟩
  calc
    _ ≤ ∑ i, (pools i).card := Finset.sum_le_sum fun i _ =>
      computes_or_budget hm rb (S i) (output i) (hvalid i) (hcomp i)
    _ = (Finset.univ.biUnion pools).card := (Finset.card_biUnion hdis).symm
    _ ≤ _ := Finset.card_le_card hsub

lemma incidence_or_budget {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hsize : ∀ l : Fin N, (Finset.univ.filter fun p => I p l).card = q + 1)
    (hunique : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    {C : Circuit} (hm : Monotone2 C) (rb : ReadsBack N C) (output : Fin N → ℕ)
    (hvalid : ∀ l, output l < N + C.gates.length)
    (hcomp : ∀ l (z : Fin N → Bool),
      val C (List.ofFn z) (output l) = decide (∃ p, I p l ∧ z p = true)) :
    N * q ≤ (orGates C).card := by
  classical
  let S : Fin N → Finset (Fin N) := fun l => Finset.univ.filter fun p => I p l
  have hpair : ∀ l l', l ≠ l' → (S l ∩ S l').card ≤ 1 := by
    intro l l' hll
    apply Finset.card_le_one.2
    intro p hp p' hp'
    by_contra hpp
    have hpI : I p l ∧ I p l' := by simpa [S] using hp
    have hp'I : I p' l ∧ I p' l' := by simpa [S] using hp'
    obtain ⟨a, _, ha⟩ := hunique p p' hpp
    exact hll ((ha l ⟨hpI.1, hp'I.1⟩).trans (ha l' ⟨hpI.2, hp'I.2⟩).symm)
  have hcomp' : ∀ l (z : Fin N → Bool),
      val C (List.ofFn z) (output l) = decide (∃ p ∈ S l, z p = true) := by
    intro l z
    exact (hcomp l z).trans (Bool.decide_congr (by simp [S]))
  have hb := multioutput_or_budget hm rb S output hvalid hcomp' hpair
  have hcards : ∀ l, (S l).card = q + 1 := hsize
  simpa [hcards] using hb

end PurePointBudget


namespace CofactorSharing

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.Outside.L_meta_2583.Repair
open PEqualNP.Outside.L_meta_2583.PurePointBudget

def gates : List Gate :=
  [⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [0, 6]⟩,
   ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.and, [1, 8]⟩,
   ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [2, 10]⟩,
   ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.or, [12, 11]⟩]

def baseCircuit : Circuit := ⟨gates, 13⟩

def cutCircuit (l : Fin 3) : Circuit :=
  ⟨(List.ofFn fun j : Fin 3 =>
    (⟨if j = l then GateOp.and else GateOp.or, []⟩ : Gate)) ++ gates, 13⟩

lemma base_ao2 : IsAO2 6 baseCircuit := by decide +kernel

lemma base_correct : ∀ z : Fin 6 → Bool,
    circuitFun 6 baseCircuit z = decide (∃ p l : Fin 3, p ≠ l ∧
      z (Fin.castAdd 3 p) = true ∧ z (Fin.natAdd 3 l) = true) := by
  decide +kernel

lemma cuts_are_cofactors : ∀ (l : Fin 3) (x : Fin 3 → Bool),
    circuitFun 3 (cutCircuit l) x =
      circuitFun 6 baseCircuit (CircuitCheckWrapper.liftInput
        (Sum.elim x (fun j : Fin 3 => decide (j = l)))) := by
  decide +kernel

lemma cuts_correct : ∀ (l : Fin 3) (x : Fin 3 → Bool),
    circuitFun 3 (cutCircuit l) x = decide (∃ p : Fin 3, p ≠ l ∧ x p = true) := by
  decide +kernel

lemma cuts_monotone : ∀ l : Fin 3, Monotone2 (cutCircuit l) ∧ ReadsBack 3 (cutCircuit l) := by
  intro l
  fin_cases l <;> constructor
  all_goals
    simp [Monotone2, ReadsBack, cutCircuit, gates, gateAt, List.ofFn_succ] <;> decide +kernel

lemma target_intersection_small :
    (({1, 2} : Finset (Fin 3)) ∩ {0, 2}).card = 1 := by decide +kernel

lemma cofactor_pools_overlap :
    ¬ Disjoint
      (orPool (cutCircuit 0) (complementInput ({1, 2} : Finset (Fin 3))) 11)
      (orPool (cutCircuit 1) (complementInput ({0, 2} : Finset (Fin 3))) 11) := by
  intro h
  have h0 : 10 ∈ orPool (cutCircuit 0) (complementInput ({1, 2} : Finset (Fin 3))) 11 := by
    apply mem_orPool.2
    refine ⟨by decide, rfl, ?_, ?_⟩ <;> decide +kernel
  have h1 : 10 ∈ orPool (cutCircuit 1) (complementInput ({0, 2} : Finset (Fin 3))) 11 := by
    apply mem_orPool.2
    refine ⟨by decide, rfl, ?_, ?_⟩ <;> decide +kernel
  exact Finset.disjoint_left.1 h h0 h1

end CofactorSharing


namespace Repair

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadK

lemma repair_sound_and_clean {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsAO2 n C) (hc : circuitFun n C = graphFun G ∅)
    (pick : ℕ → Fin n × Fin n) (hp : ∀ j, G.Adj (pick j).1 (pick j).2) :
    (∀ x : Fin n → Bool, circuitFun n (repair G C pick) x = true → graphFun G ∅ x = true) ∧
    (∀ j < (repair G C pick).gates.length,
      (gateAt (repair G C pick) j).op = GateOp.and → BelowF G (repair G C pick) j) := by
  let D := repair G C pick
  have hreflect (x : Fin n → Bool) (hn : graphFun G ∅ x ≠ true) (w : ℕ) :
      val D (List.ofFn x) w = true → val C (List.ofFn x) w = true :=
    repair_compare hC pick x false (by
      intro j hj hd hv
      have hpv := (repair_replaced_val pick hj hd x).1 hv
      exact (hn (graph_true.2 ⟨_, _, hp j, hpv.1, hpv.2⟩)).elim) w
  constructor
  · intro x hx
    by_contra hn
    have h := hreflect x hn C.output hx
    change circuitFun n C x = true at h
    rw [hc] at h
    exact hn h
  · intro j hj hop x hv
    have hj' : j < C.gates.length := by rwa [repair_len] at hj
    by_cases hd : dirty G C j
    · have h := (repair_replaced_val pick hj' hd x).1 hv
      exact graph_true.2 ⟨_, _, hp j, h.1, h.2⟩
    · have hop' : (gateAt C j).op = GateOp.and := by rwa [repair_kept pick hj' hd] at hop
      by_contra hn
      have hbelow : BelowF G C j := by
        by_contra h
        exact hd ⟨hop', h⟩
      exact hn (hbelow x (hreflect x hn (n + j) hv))

lemma repair_certificate_of_bad_edges {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hC : IsAO2 n C)
    (hc : circuitFun n C = graphFun G ∅) (pick : ℕ → Fin n × Fin n)
    (hp : ∀ j, G.Adj (pick j).1 (pick j).2)
    (hbad : ∀ u v, G.Adj u v → readsAtMost C n [u.val, v.val] 1 = false →
      circuitFun n (repair G C pick) (pairInput u v) = true) :
    IsAO2 n (repair G C pick) ∧ (repair G C pick).size = C.size ∧
    circuitFun n (repair G C pick) = circuitFun n C ∧
    (∀ j < (repair G C pick).gates.length,
      (gateAt (repair G C pick) j).op = GateOp.and → BelowF G (repair G C pick) j) := by
  let D := repair G C pick
  have hD : IsAO2 n D := repair_ao hC pick
  obtain ⟨hsound, hclean⟩ := repair_sound_and_clean G C hC hc pick hp
  have hpair (u v : Fin n) (huv : G.Adj u v) : circuitFun n D (pairInput u v) = true := by
    cases hread : readsAtMost C n [u.val, v.val] 1 with
    | false => exact hbad u v huv hread
    | true => exact repair_read_one hC pick hc (G.ne_of_adj huv) hread
  have hm : Monotone2 D := CircuitCheckWrapper.ao2_monotone2 hD
  refine ⟨hD, repair_len G C pick, ?_, hclean⟩
  funext x
  rw [hc]
  apply Bool.eq_iff_iff.2
  constructor
  · exact hsound x
  · intro hx
    obtain ⟨u, v, huv, hu, hv⟩ := graph_true.1 hx
    apply pair_mono hm _ D.output (hpair u v huv)
    intro w hw
    simp only [pairInput, decide_eq_true_eq] at hw
    rcases hw with rfl | rfl
    · exact hu
    · exact hv

end Repair


namespace ProjectedBudget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_2583.Repair
open PEqualNP.Outside.L_meta_2583.PurePointBudget

noncomputable def positiveSupportInputs {α : Type*} (C : Circuit)
    (support : ℕ → Finset α) (k : ℕ) : Finset ℕ := by
  classical
  exact (gateAt C k).inputs.toFinset.filter fun w => (support w).Nonempty

lemma mem_positiveSupportInputs {α : Type*} {C : Circuit} {support : ℕ → Finset α}
    {k w : ℕ} : w ∈ positiveSupportInputs C support k ↔
    w ∈ (gateAt C k).inputs ∧ (support w).Nonempty := by
  classical
  simp [positiveSupportInputs]

noncomputable def supportOrPool {n : ℕ} {α : Type*} (C : Circuit)
    (support : ℕ → Finset α) (x : Fin n → Bool) (m : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range m).filter fun k => (gateAt C k).op = GateOp.or ∧
    1 < (support (n + k)).card ∧ val C (List.ofFn x) (n + k) = false

lemma mem_supportOrPool {n : ℕ} {α : Type*} {C : Circuit} {support : ℕ → Finset α}
    {x : Fin n → Bool} {m k : ℕ} :
    k ∈ supportOrPool C support x m ↔ k < m ∧ (gateAt C k).op = GateOp.or ∧
      1 < (support (n + k)).card ∧ val C (List.ofFn x) (n + k) = false := by
  classical
  simp [supportOrPool]

lemma support_frontier_budget {n : ℕ} {α : Type*} [DecidableEq α] {C : Circuit}
    (hm : Monotone2 C) (rb : ReadsBack n C) (support : ℕ → Finset α)
    (hinput : ∀ w, w < n → (support w).card ≤ 1)
    (hAndSupport : ∀ k, k < C.gates.length → (gateAt C k).op = GateOp.and →
      ∀ w ∈ (gateAt C k).inputs, support (n + k) ⊆ support w)
    (hOrSupport : ∀ k, k < C.gates.length → (gateAt C k).op = GateOp.or →
      ∀ u, u ∈ support (n + k) ↔ ∃ w ∈ (gateAt C k).inputs, u ∈ support w)
    (x : Fin n → Bool) (m : ℕ) (roots : Finset ℕ)
    (hvalid : ∀ w ∈ roots, w < n + C.gates.length)
    (hfalse : ∀ w ∈ roots, val C (List.ofFn x) w = false)
    (hbound : ∀ w ∈ roots, 1 < (support w).card → w < n + m) :
    (roots.biUnion (support)).card ≤ roots.card + (supportOrPool C support x m).card := by
  classical
  induction m generalizing roots with
  | zero =>
    have hsmall : ∀ w ∈ roots, (support w).card ≤ 1 := by
      intro w hw
      by_contra! hb
      have hw' := hbound w hw hb
      have hs := hinput w (by omega)
      omega
    calc
      _ ≤ ∑ w ∈ roots, (support w).card := Finset.card_biUnion_le
      _ ≤ ∑ _w ∈ roots, 1 := Finset.sum_le_sum hsmall
      _ = _ := by simp [supportOrPool]
  | succ m ih =>
    have hpool : supportOrPool C support x m ⊆ supportOrPool C support x (m + 1) := by
      intro k hk
      obtain ⟨hk, hh⟩ := mem_supportOrPool.1 hk
      exact mem_supportOrPool.2 ⟨by omega, hh⟩
    by_cases htop : n + m ∈ roots ∧ 1 < (support (n + m)).card
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
        have hTbound : ∀ w ∈ T, 1 < (support w).card → w < n + m := by
          intro w hw hcard
          rcases Finset.mem_union.1 hw with hw | hw
          · have hlt := hbound w (Finset.mem_of_mem_erase hw) hcard
            have hne := (Finset.mem_erase.1 hw).1
            omega
          · have : w = a := Finset.mem_singleton.1 hw
            omega
        have hsub : roots.biUnion (support) ⊆ T.biUnion (support) := by
          intro u hu
          obtain ⟨w, hw, huw⟩ := Finset.mem_biUnion.1 hu
          by_cases he : w = n + m
          · subst w
            have hua : u ∈ support a := hAndSupport m hmC hand a ha huw
            exact Finset.mem_biUnion.2 ⟨a, Finset.mem_union_right _ (Finset.mem_singleton_self _), hua⟩
          · exact Finset.mem_biUnion.2 ⟨w, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨he, hw⟩), huw⟩
        have hfirst := (Finset.card_le_card hsub).trans (ih T hTvalid hTfalse hTbound)
        have hTcard := Finset.card_union_le (roots.erase (n + m)) {a}
        have herase := Finset.card_erase_add_one hmem
        have hinc := Finset.card_le_card hpool
        simp only [Finset.card_singleton] at hTcard
        change T.card ≤ (roots.erase (n + m)).card + 1 at hTcard
        omega
      · let P := positiveSupportInputs C support m
        let T := roots.erase (n + m) ∪ P
        have hback : ∀ w ∈ P, w < n + m :=
          fun w hw => rb m hmC w (mem_positiveSupportInputs.1 hw).1
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
                  ⟨w, (mem_positiveSupportInputs.1 hw).1, hback w hw, hf⟩
              rw [hfalse _ hmem] at ht
              cases ht
        have hTbound : ∀ w ∈ T, 1 < (support w).card → w < n + m := by
          intro w hw hcard
          rcases Finset.mem_union.1 hw with hw | hw
          · have hlt := hbound w (Finset.mem_of_mem_erase hw) hcard
            have hne := (Finset.mem_erase.1 hw).1
            omega
          · exact hback w hw
        have hsub : roots.biUnion (support) ⊆ T.biUnion (support) := by
          intro u hu
          obtain ⟨w, hw, huw⟩ := Finset.mem_biUnion.1 hu
          by_cases he : w = n + m
          · subst w
            obtain ⟨a, ha, hua⟩ := (hOrSupport m hmC hor u).1 huw
            exact Finset.mem_biUnion.2 ⟨a, Finset.mem_union_right _
              (mem_positiveSupportInputs.2 ⟨ha, u, hua⟩), hua⟩
          · exact Finset.mem_biUnion.2 ⟨w, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨he, hw⟩), huw⟩
        have hfirst := (Finset.card_le_card hsub).trans (ih T hTvalid hTfalse hTbound)
        have hTcard := Finset.card_union_le (roots.erase (n + m)) P
        have herase := Finset.card_erase_add_one hmem
        have hPc : P.card ≤ 2 := (Finset.card_filter_le _ _).trans (input_card hm hmC)
        have hnew : m ∈ supportOrPool C support x (m + 1) :=
          mem_supportOrPool.2 ⟨by omega, hor, hlarge, hfalse _ hmem⟩
        have hn : m ∉ supportOrPool C support x m := fun h => (Nat.lt_irrefl m) (mem_supportOrPool.1 h).1
        have hsubpool : insert m (supportOrPool C support x m) ⊆ supportOrPool C support x (m + 1) :=
          Finset.insert_subset_iff.2 ⟨hnew, hpool⟩
        have hinc := Finset.card_le_card hsubpool
        rw [Finset.card_insert_of_notMem hn] at hinc
        change T.card ≤ (roots.erase (n + m)).card + P.card at hTcard
        omega
    · have hnew : ∀ w ∈ roots, 1 < (support w).card → w < n + m := by
        intro w hw hw'
        have hlt := hbound w hw hw'
        have hne : w ≠ n + m := fun he => htop ⟨he ▸ hw, he ▸ hw'⟩
        omega
      have hfirst := ih roots hvalid hfalse hnew
      have hinc := Finset.card_le_card hpool
      omega

def projectedSupport (n : ℕ) (C : Circuit) (V : Finset (Fin n)) (w : ℕ) : Finset (Fin n) :=
  singletonSupport n C w ∩ V

lemma projectedSupport_input {n : ℕ} {C : Circuit} (V : Finset (Fin n))
    (w : ℕ) (hw : w < n) : (projectedSupport n C V w).card ≤ 1 := by
  have hs := support_input (C := C) (⟨w, hw⟩ : Fin n)
  calc
    _ ≤ (singletonSupport n C w).card := Finset.card_le_card Finset.inter_subset_left
    _ = 1 := by rw [hs]; rfl

lemma projectedSupport_and {n : ℕ} {C : Circuit} (V : Finset (Fin n))
    {k : ℕ} (hk : k < C.gates.length) (hop : (gateAt C k).op = GateOp.and)
    {w : ℕ} (hw : w ∈ (gateAt C k).inputs) :
    projectedSupport n C V (n + k) ⊆ projectedSupport n C V w := by
  intro p hp
  obtain ⟨hp, hV⟩ := Finset.mem_inter.1 hp
  have ht := ((val_and (by simp) hk hop).1 (mem_support.1 hp) w hw).2
  exact Finset.mem_inter.2 ⟨mem_support.2 ht, hV⟩

lemma projectedSupport_or {n : ℕ} {C : Circuit} (rb : ReadsBack n C)
    (V : Finset (Fin n)) {k : ℕ} (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (p : Fin n) :
    p ∈ projectedSupport n C V (n + k) ↔
      ∃ w ∈ (gateAt C k).inputs, p ∈ projectedSupport n C V w := by
  simp only [projectedSupport, Finset.mem_inter, support_or rb hk hop]
  aesop

def projectedComplementInput {n : ℕ} (V S : Finset (Fin n)) : Fin n → Bool :=
  fun p => decide (p ∈ V ∧ p ∉ S)

noncomputable def projectedOrPool {n : ℕ} (C : Circuit) (V S : Finset (Fin n))
    (m : ℕ) : Finset ℕ :=
  supportOrPool C (projectedSupport n C V) (projectedComplementInput V S) m

lemma projectedSupport_subset_of_false {n : ℕ} {C : Circuit} (hm : Monotone2 C)
    {V S : Finset (Fin n)} {w : ℕ}
    (hw : val C (List.ofFn (projectedComplementInput V S)) w = false) :
    projectedSupport n C V w ⊆ S ∩ V := by
  intro p hp
  obtain ⟨hp, hpV⟩ := Finset.mem_inter.1 hp
  refine Finset.mem_inter.2 ⟨?_, hpV⟩
  by_contra hnot
  have hle : ∀ i, pairInput p p i = true → projectedComplementInput V S i = true := by
    intro i hi
    have hip : i = p := by simpa [pairInput] using hi
    simp [projectedComplementInput, hip, hpV, hnot]
  have ht := pair_mono hm hle w (mem_support.1 hp)
  rw [hw] at ht
  cases ht

lemma projectedOrPool_disjoint {n : ℕ} {C : Circuit} (hm : Monotone2 C)
    {V S T : Finset (Fin n)} (hST : ((S ∩ V) ∩ (T ∩ V)).card ≤ 1) (m : ℕ) :
    Disjoint (projectedOrPool C V S m) (projectedOrPool C V T m) := by
  apply Finset.disjoint_left.2
  intro k hkS hkT
  obtain ⟨_, _, hlarge, hS⟩ := mem_supportOrPool.1 hkS
  obtain ⟨_, _, _, hT⟩ := mem_supportOrPool.1 hkT
  have hsub : projectedSupport n C V (n + k) ⊆ (S ∩ V) ∩ (T ∩ V) :=
    Finset.subset_inter (projectedSupport_subset_of_false hm hS)
      (projectedSupport_subset_of_false hm hT)
  have hcard := (Finset.card_le_card hsub).trans hST
  omega

lemma point_projected_disjoint {n : ℕ} {C : Circuit} (hm : Monotone2 C)
    {V W S : Finset (Fin n)} (hWV : Disjoint W V) (m : ℕ) :
    Disjoint (orPool C (complementInput W) m) (projectedOrPool C V S m) := by
  apply Finset.disjoint_left.2
  intro k hkW hkS
  obtain ⟨_, _, _, hW⟩ := mem_orPool.1 hkW
  obtain ⟨_, _, hlarge, _⟩ := mem_supportOrPool.1 hkS
  have hempty : projectedSupport n C V (n + k) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.2
    intro p hp
    obtain ⟨hp, hpV⟩ := Finset.mem_inter.1 hp
    exact Finset.disjoint_left.1 hWV (support_subset_of_false hm hW hp) hpV
  simp [hempty] at hlarge

lemma computes_projected_or_budget {n : ℕ} {C : Circuit}
    (hm : Monotone2 C) (rb : ReadsBack n C) (V S : Finset (Fin n))
    (w : ℕ) (hvalid : w < n + C.gates.length)
    (hcomp : ∀ z : Fin n → Bool, val C (List.ofFn z) w = decide (∃ p ∈ S, z p = true)) :
    (S ∩ V).card - 1 ≤ (projectedOrPool C V S C.gates.length).card := by
  classical
  have hs : projectedSupport n C V w = S ∩ V := by
    have hs' : singletonSupport n C w = S := by
      ext p
      rw [mem_support, hcomp]
      simp [pairInput, eq_comm]
    simp [projectedSupport, hs']
  have hf : val C (List.ofFn (projectedComplementInput V S)) w = false := by
    rw [hcomp]
    apply decide_eq_false
    rintro ⟨p, hp, hxp⟩
    have hxp' : p ∈ V ∧ p ∉ S := by simpa [projectedComplementInput] using hxp
    exact hxp'.2 hp
  have hb := support_frontier_budget hm rb (projectedSupport n C V)
    (projectedSupport_input V)
    (fun _ hk hop _ hw => projectedSupport_and V hk hop hw)
    (fun _ hk hop p => projectedSupport_or rb V hk hop p)
    (projectedComplementInput V S) C.gates.length {w}
    (by simpa using hvalid) (by simpa using hf)
    (by intro u hu _; simpa only [Finset.mem_singleton.1 hu] using hvalid)
  simp only [Finset.singleton_biUnion, hs, Finset.card_singleton] at hb
  change (S ∩ V).card - 1 ≤ (supportOrPool C (projectedSupport n C V)
    (projectedComplementInput V S) C.gates.length).card
  omega

lemma split_multioutput_or_budget {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {C : Circuit} (hm : Monotone2 C) (rb : ReadsBack n C)
    (V : Finset (Fin n)) (S : ι → Finset (Fin n)) (output : ι → ℕ)
    (hvalid : ∀ i, output i < n + C.gates.length)
    (hcomp : ∀ i (z : Fin n → Bool),
      val C (List.ofFn z) (output i) = decide (∃ p ∈ S i, z p = true))
    (hpair : ∀ i j, i ≠ j → ((S i ∩ V) ∩ (S j ∩ V)).card ≤ 1)
    (W : Finset (Fin n)) (w : ℕ) (hWV : Disjoint W V)
    (hwvalid : w < n + C.gates.length)
    (hwcomp : ∀ z : Fin n → Bool, val C (List.ofFn z) w = decide (∃ p ∈ W, z p = true)) :
    (∑ i, ((S i ∩ V).card - 1)) + (W.card - 1) ≤ (orGates C).card := by
  classical
  let pools := fun i => projectedOrPool C V (S i) C.gates.length
  let U := Finset.univ.biUnion pools
  let P := orPool C (complementInput W) C.gates.length
  have hdis : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint pools := by
    intro i _ j _ hij
    exact projectedOrPool_disjoint hm (hpair i j hij) C.gates.length
  have hsum : (∑ i, ((S i ∩ V).card - 1)) ≤ U.card := by
    calc
      _ ≤ ∑ i, (pools i).card := Finset.sum_le_sum fun i _ =>
        computes_projected_or_budget hm rb V (S i) (output i) (hvalid i) (hcomp i)
      _ = _ := (Finset.card_biUnion hdis).symm
  have hpoint : W.card - 1 ≤ P.card :=
    computes_or_budget hm rb W w hwvalid hwcomp
  have hUP : Disjoint U P := by
    apply Finset.disjoint_left.2
    intro k hkU hkP
    obtain ⟨i, _, hki⟩ := Finset.mem_biUnion.1 hkU
    exact Finset.disjoint_left.1 (point_projected_disjoint hm hWV C.gates.length) hkP hki
  have hsub : U ∪ P ⊆ orGates C := by
    intro k hk
    rcases Finset.mem_union.1 hk with hk | hk
    · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.1 hk
      obtain ⟨hk, hop, _⟩ := mem_supportOrPool.1 hi
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hk, hop⟩
    · obtain ⟨hk, hop, _⟩ := mem_orPool.1 hk
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hk, hop⟩
  calc
    _ ≤ U.card + P.card := Nat.add_le_add hsum hpoint
    _ = (U ∪ P).card := (Finset.card_union_of_disjoint hUP).symm
    _ ≤ _ := Finset.card_le_card hsub

end ProjectedBudget


namespace LinearExtraction

open PEqualNP.CircuitLowerBounds

def fw {α : Type} (f : List α → Gate → α) (gs : List Gate) (init : List α) : List α :=
  gs.foldl (fun w g => w ++ [f w g]) init

lemma fw_nil {α : Type} (f : List α → Gate → α) (init : List α) : fw f [] init = init := rfl

lemma fw_cons {α : Type} (f : List α → Gate → α) (g : Gate) (gs : List Gate) (init : List α) :
    fw f (g :: gs) init = fw f gs (init ++ [f init g]) := rfl

lemma fw_append {α : Type} (f : List α → Gate → α) (gs hs : List Gate) (init : List α) :
    fw f (gs ++ hs) init = fw f hs (fw f gs init) := by
  simp [fw, List.foldl_append]

lemma fw_snoc {α : Type} (f : List α → Gate → α) (gs : List Gate) (g : Gate) (init : List α) :
    fw f (gs ++ [g]) init = fw f gs init ++ [f (fw f gs init) g] := by
  rw [fw_append]; rfl

lemma fw_length {α : Type} (f : List α → Gate → α) (gs : List Gate) (init : List α) :
    (fw f gs init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp [fw_nil]
  | cons g gs ih => rw [fw_cons, ih]; simp; omega

lemma fw_prefix {α : Type} (f : List α → Gate → α) (gs : List Gate) (init : List α) :
    ∃ r, fw f gs init = init ++ r := by
  induction gs generalizing init with
  | nil => exact ⟨[], by simp [fw_nil]⟩
  | cons g gs ih =>
    obtain ⟨r, hr⟩ := ih (init ++ [f init g])
    exact ⟨[f init g] ++ r, by rw [fw_cons, hr]; simp⟩

lemma getD_append_left' {α : Type} (l r : List α) (i : ℕ) (d : α) (h : i < l.length) :
    (l ++ r).getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_take' {α : Type} (l : List α) (m i : ℕ) (d : α) :
    (l.take m).getD i d = if i < m then l.getD i d else d := by
  split_ifs with h
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

lemma fw_take {α : Type} (f : List α → Gate → α) (gs : List Gate) (init : List α) (j : ℕ)
    (hj : j ≤ gs.length) :
    (fw f gs init).take (init.length + j) = fw f (gs.take j) init := by
  have h := List.take_append_drop j gs
  conv_lhs => rw [← h, fw_append]
  obtain ⟨r, hr⟩ := fw_prefix f (gs.drop j) (fw f (gs.take j) init)
  rw [hr]
  have hl : (fw f (gs.take j) init).length = init.length + j := by
    rw [fw_length]; simp; omega
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]

lemma fw_getD_gate {α : Type} (f : List α → Gate → α) (gs : List Gate) (init : List α) (j : ℕ)
    (hj : j < gs.length) (d : α) :
    (fw f gs init).getD (init.length + j) d =
      f ((fw f gs init).take (init.length + j)) gs[j] := by
  rw [fw_take f gs init j hj.le]
  have h : gs = gs.take j ++ [gs[j]] ++ gs.drop (j + 1) := by
    simp
  conv_lhs => rw [h, fw_append, fw_snoc]
  obtain ⟨r, hr⟩ := fw_prefix f (gs.drop (j + 1)) (fw f (gs.take j) init ++ [f (fw f (gs.take j) init) gs[j]])
  rw [hr]
  have hl : (fw f (gs.take j) init).length = init.length + j := by
    rw [fw_length]; simp; omega
  rw [getD_append_left' _ _ _ _ (by simp; omega)]
  simp [List.getD_eq_getElem?_getD, hl]

section C

variable (P L : ℕ) (C : Circuit)

def deg (i : ℕ) : ℕ := (C.lineDegrees (P + L) (Finset.Ico P (P + L))).getD i 0

def val (x : Fin P → Bool) (y : Fin L → Bool) (i : ℕ) : Bool :=
  (C.wires (List.ofFn x ++ List.ofFn y)).getD i false

lemma lineDegrees_eq : C.lineDegrees (P + L) (Finset.Ico P (P + L)) =
    fw (fun d g => g.lineDegree d) C.gates
      ((List.range (P + L)).map fun i => if i ∈ Finset.Ico P (P + L) then 1 else 0) := rfl

lemma wires_eq (z : List Bool) : C.wires z =
    fw (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false)) C.gates z := rfl

lemma deg_input (i : ℕ) (hi : i < P + L) : deg P L C i = if P ≤ i then 1 else 0 := by
  unfold deg
  rw [lineDegrees_eq]
  obtain ⟨r, hr⟩ := fw_prefix (fun d g => g.lineDegree d) C.gates
    ((List.range (P + L)).map fun i => if i ∈ Finset.Ico P (P + L) then 1 else 0)
  rw [hr, getD_append_left' _ _ _ _ (by simp; omega)]
  simp [List.getD_eq_getElem?_getD, hi]

lemma deg_point (i : ℕ) (hi : i < P) : deg P L C i = 0 := by
  rw [deg_input P L C i (by omega)]; simp; omega

lemma deg_line (i : ℕ) (hi : P ≤ i) (hi2 : i < P + L) : deg P L C i = 1 := by
  rw [deg_input P L C i hi2]; simp [hi]

lemma deg_ge (i : ℕ) (hi : P + L + C.gates.length ≤ i) : deg P L C i = 0 := by
  unfold deg
  apply List.getD_eq_default
  rw [lineDegrees_eq, fw_length]; simp; omega

lemma deg_gate_eq (j : ℕ) (hj : j < C.gates.length) :
    deg P L C (P + L + j) =
      C.gates[j].lineDegree ((C.lineDegrees (P + L) (Finset.Ico P (P + L))).take (P + L + j)) := by
  have h := fw_getD_gate (fun d g => g.lineDegree d) C.gates
    ((List.range (P + L)).map fun i => if i ∈ Finset.Ico P (P + L) then 1 else 0) j hj 0
  simp only [List.length_map, List.length_range] at h
  unfold deg
  rw [lineDegrees_eq, h]

lemma deg_gate_and (j : ℕ) (hj : j < C.gates.length) (hop : C.gates[j].op = GateOp.and) :
    deg P L C (P + L + j) =
      (C.gates[j].inputs.map fun i => if i < P + L + j then deg P L C i else 0).sum := by
  rw [deg_gate_eq P L C j hj]
  unfold Gate.lineDegree
  rw [ite_eq_left hop]
  simp only [getD_take']
  rfl

lemma deg_gate_or (j : ℕ) (hj : j < C.gates.length) (hop : C.gates[j].op = GateOp.or) :
    deg P L C (P + L + j) =
      (C.gates[j].inputs.map fun i => if i < P + L + j then deg P L C i else 0).foldr max 0 := by
  rw [deg_gate_eq P L C j hj]
  unfold Gate.lineDegree
  rw [ite_eq_right (by rw [hop]; exact fun h => GateOp.noConfusion h)]
  simp only [getD_take']
  rfl

lemma val_input (x : Fin P → Bool) (y : Fin L → Bool) (i : ℕ) (hi : i < P + L) :
    val P L C x y i = (List.ofFn x ++ List.ofFn y).getD i false := by
  unfold val
  rw [wires_eq]
  obtain ⟨r, hr⟩ := fw_prefix (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false))
    C.gates (List.ofFn x ++ List.ofFn y)
  rw [hr, getD_append_left' _ _ _ _ (by simp; omega)]

lemma val_point (x : Fin P → Bool) (y : Fin L → Bool) (i : ℕ) (hi : i < P) :
    val P L C x y i = x ⟨i, hi⟩ := by
  rw [val_input P L C x y i (by omega), List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by simp; exact hi)]
  simp [hi]

lemma val_line (x : Fin P → Bool) (y : Fin L → Bool) (i : ℕ) (hi : P ≤ i) (hi2 : i < P + L) :
    val P L C x y i = y ⟨i - P, by omega⟩ := by
  rw [val_input P L C x y i hi2]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; exact hi)]
  have h3 : i - (List.ofFn x).length < L := by simp; omega
  simp only [List.getElem?_ofFn, List.length_ofFn]
  simp [show i - P < L by omega]

lemma val_ge (x : Fin P → Bool) (y : Fin L → Bool) (i : ℕ) (hi : P + L + C.gates.length ≤ i) :
    val P L C x y i = false := by
  unfold val
  apply List.getD_eq_default
  rw [wires_eq, fw_length]; simp; omega

lemma val_gate (x : Fin P → Bool) (y : Fin L → Bool) (j : ℕ) (hj : j < C.gates.length) :
    val P L C x y (P + L + j) =
      C.gates[j].op.eval (C.gates[j].inputs.map fun i => if i < P + L + j then val P L C x y i else false) := by
  have h := fw_getD_gate (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false)) C.gates
    (List.ofFn x ++ List.ofFn y) j hj false
  simp only [List.length_append, List.length_ofFn] at h
  unfold val
  rw [wires_eq, h]
  simp only [getD_take']

end C

lemma le_foldr_max (l : List ℕ) (a : ℕ) (h : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with h | h
    · subst h; exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

lemma foldr_max_eq_zero (l : List ℕ) (h : l.foldr max 0 = 0) (a : ℕ) (ha : a ∈ l) : a = 0 := by
  have := le_foldr_max l a ha; omega

section Deg

variable (P L : ℕ) (C : Circuit)

lemma op_cases (hm : IsMonotoneCircuit C) (j : ℕ) (hj : j < C.gates.length) :
    C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or :=
  hm _ (List.getElem_mem hj)

lemma deg_le_of_input (hm : IsMonotoneCircuit C) (j : ℕ) (hj : j < C.gates.length) (i : ℕ)
    (hi : i ∈ C.gates[j].inputs) (hlt : i < P + L + j) :
    deg P L C i ≤ deg P L C (P + L + j) := by
  have hmem : deg P L C i ∈ (C.gates[j].inputs.map fun i => if i < P + L + j then deg P L C i else 0) :=
    List.mem_map.mpr ⟨i, hi, by simp [hlt]⟩
  rcases op_cases C hm j hj with hop | hop
  · rw [deg_gate_and P L C j hj hop]; exact List.le_sum_of_mem hmem
  · rw [deg_gate_or P L C j hj hop]; exact le_foldr_max _ _ hmem

abbrev Rel (P L : ℕ) (C : Circuit) : ℕ → ℕ → Prop :=
  fun a1 b1 : ℕ => a1 < b1 ∧ ∃ i1 : Fin C.gates.length, b1 = P + L + i1.val ∧ a1 ∈ (C.gates.get i1).inputs

lemma deg_le_of_rel (hm : IsMonotoneCircuit C) (a b : ℕ) (h : Rel P L C a b) :
    deg P L C a ≤ deg P L C b := by
  obtain ⟨hab, i, rfl, hmem⟩ := h
  exact deg_le_of_input P L C hm i.val i.isLt a hmem hab

lemma deg_le_of_reach (hm : IsMonotoneCircuit C) (a b : ℕ)
    (h : Relation.ReflTransGen (Rel P L C) a b) : deg P L C a ≤ deg P L C b := by
  induction h with
  | refl => exact le_refl _
  | tail _ hr ih => exact le_trans ih (deg_le_of_rel P L C hm _ _ hr)

end Deg

section Phase1

variable (P L : ℕ) (C : Circuit)

def evf : List Bool → Gate → Bool := fun w g => g.op.eval (g.inputs.map fun i => w.getD i false)

def dw (gs : List Gate) (z : List Bool) : List Bool := fw evf gs z

lemma dw_length (gs : List Gate) (z : List Bool) : (dw gs z).length = z.length + gs.length :=
  fw_length _ _ _

lemma dw_getD_append (gs r : List Gate) (z : List Bool) (i : ℕ) (hi : i < z.length + gs.length) :
    (dw (gs ++ r) z).getD i false = (dw gs z).getD i false := by
  unfold dw
  rw [fw_append]
  obtain ⟨t, ht⟩ := fw_prefix evf r (fw evf gs z)
  rw [ht, getD_append_left' _ _ _ _ (by rw [fw_length]; exact hi)]

lemma dw_getD_snoc (gs : List Gate) (g : Gate) (z : List Bool) :
    (dw (gs ++ [g]) z).getD (z.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (dw gs z).getD i false) := by
  unfold dw
  rw [fw_snoc]
  have hl := fw_length evf gs z
  simp [List.getD_eq_getElem?_getD, hl]
  rfl

lemma dw_getD_input (gs : List Gate) (z : List Bool) (i : ℕ) (hi : i < z.length) :
    (dw gs z).getD i false = z.getD i false := by
  unfold dw
  obtain ⟨t, ht⟩ := fw_prefix evf gs z
  rw [ht, getD_append_left' _ _ _ _ hi]

lemma dw_getD_ge (gs : List Gate) (z : List Bool) (i : ℕ) (hi : z.length + gs.length ≤ i) :
    (dw gs z).getD i false = false := by
  apply List.getD_eq_default; rw [dw_length]; exact hi

lemma dw_point (gs : List Gate) (x : Fin P → Bool) (i : ℕ) (hi : i < P) :
    (dw gs (List.ofFn x)).getD i false = x ⟨i, hi⟩ := by
  rw [dw_getD_input _ _ _ (by simp; exact hi)]
  simp [List.getD_eq_getElem?_getD, hi]

def rank (k : ℕ) : ℕ := ((Finset.range k).filter fun j => deg P L C (P + L + j) = 0).card

lemma rank_succ (k : ℕ) : rank P L C (k + 1) = rank P L C k + if deg P L C (P + L + k) = 0 then 1 else 0 := by
  unfold rank
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · simp

lemma rank_mono (j k : ℕ) (h : j ≤ k) : rank P L C j ≤ rank P L C k := by
  unfold rank
  apply Finset.card_le_card
  intro a; simp; omega

lemma rank_lt (j k : ℕ) (h : j < k) (hd : deg P L C (P + L + j) = 0) : rank P L C j < rank P L C k := by
  have h1 := rank_succ P L C j
  rw [ite_eq_left hd] at h1
  have h2 := rank_mono P L C (j + 1) k h
  omega

def dflt : Gate := ⟨GateOp.or, []⟩

def gt (j : ℕ) : Gate := C.gates.getD j dflt

lemma gt_eq (j : ℕ) (hj : j < C.gates.length) : gt C j = C.gates[j] := by
  simp [gt, List.getD_eq_getElem?_getD, hj]

def sig (j i : ℕ) : ℕ :=
  if i < P then i else if i < P + L + j then P + rank P L C (i - (P + L)) else P + rank P L C j

def copyGate (j : ℕ) : Gate := ⟨(gt C j).op, (gt C j).inputs.map (sig P L C j)⟩

def phase1 (k : ℕ) : List Gate :=
  (List.range k).filterMap fun j => if deg P L C (P + L + j) = 0 then some (copyGate P L C j) else none

lemma phase1_succ (k : ℕ) : phase1 P L C (k + 1) =
    phase1 P L C k ++ (if deg P L C (P + L + k) = 0 then [copyGate P L C k] else []) := by
  unfold phase1
  rw [List.range_succ, List.filterMap_append]
  split_ifs with h <;> simp [h]

lemma phase1_length (k : ℕ) : (phase1 P L C k).length = rank P L C k := by
  induction k with
  | zero => simp [phase1, rank]
  | succ k ih =>
    rw [phase1_succ, rank_succ, List.length_append, ih]
    split_ifs <;> simp

lemma phase1_val (hm : IsMonotoneCircuit C) (x : Fin P → Bool) (y : Fin L → Bool) (k : ℕ)
    (hk : k ≤ C.gates.length) (j : ℕ) (hj : j < k) (hd : deg P L C (P + L + j) = 0) :
    (dw (phase1 P L C k) (List.ofFn x)).getD (P + rank P L C j) false = val P L C x y (P + L + j) := by
  induction k generalizing j with
  | zero => omega
  | succ k ih =>
    rw [phase1_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
    · rw [dw_getD_append _ _ _ _ (by rw [phase1_length]; simp; exact rank_lt P L C j k hj hd)]
      exact ih (by omega) j hj hd
    · subst hj
      rw [ite_eq_left hd]
      have hl : (List.ofFn x).length + (phase1 P L C j).length = P + rank P L C j := by
        rw [phase1_length]; simp
      rw [← hl, dw_getD_snoc, val_gate P L C x y j (by omega)]
      unfold copyGate
      rw [gt_eq C j (by omega)]
      simp only [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i hi
      simp only [Function.comp]
      unfold sig
      by_cases h1 : i < P
      · rw [ite_eq_left h1, ite_eq_left (show i < P + L + j by omega), dw_point P _ x i h1, val_point P L C x y i h1]
      · by_cases h2 : i < P + L + j
        · have hdi : deg P L C i = 0 := by
            have := deg_le_of_input P L C hm j (by omega) i hi h2; omega
          have hiL : P + L ≤ i := by
            by_contra hc
            have := deg_line P L C i (by omega) (by omega); omega
          simp only [h1, h2, ite_false, ite_true]
          have hk' := ih (by omega) (i - (P + L)) (by omega) (by rw [show P + L + (i - (P + L)) = i by omega]; exact hdi)
          rw [show P + L + (i - (P + L)) = i by omega] at hk'
          exact hk'
        · simp only [h1, h2, ite_false]
          rw [dw_getD_ge]
          rw [phase1_length]; simp

end Phase1

section Phase2

variable (P L : ℕ) (C : Circuit)


def vEv (gs : List Gate) (x : Fin P → Bool) : Option ℕ → Bool
  | none => true
  | some i => (dw gs (List.ofFn x)).getD i false

def aEv (gs : List Gate) (x : Fin P → Bool) : Option (Option ℕ) → Bool
  | none => false
  | some c => vEv P gs x c

def Valid (gs : List Gate) (c : Option ℕ) : Prop := ∀ b, c = some b → b < P + gs.length

def push (s : (List Gate × (ℕ → Option (Option ℕ)))) (v : ℕ) (c : Option ℕ) : (List Gate × (ℕ → Option (Option ℕ))) :=
  match s.2 v, c with
  | none, _ => (s.1, Function.update s.2 v (some c))
  | some none, _ => s
  | some (some _), none => (s.1, Function.update s.2 v (some none))
  | some (some a), some b =>
    (s.1 ++ [⟨GateOp.or, [a, b]⟩], Function.update s.2 v (some (some (P + s.1.length))))

def GoodGates (r : List Gate) : Prop :=
  ∀ g ∈ r, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

lemma goodGates_append (a b : List Gate) (ha : GoodGates a) (hb : GoodGates b) : GoodGates (a ++ b) := by
  intro g hg
  rcases List.mem_append.mp hg with h | h
  · exact ha g h
  · exact hb g h

lemma vEv_append (gs r : List Gate) (x : Fin P → Bool) (c : Option ℕ) (hc : Valid P gs c) :
    vEv P (gs ++ r) x c = vEv P gs x c := by
  cases c with
  | none => rfl
  | some b =>
    simp only [vEv]
    exact dw_getD_append gs r _ b (by simp; exact hc b rfl)

lemma aEv_append (gs r : List Gate) (x : Fin P → Bool) (a : Option (Option ℕ))
    (ha : ∀ c, a = some c → Valid P gs c) :
    aEv P (gs ++ r) x a = aEv P gs x a := by
  cases a with
  | none => rfl
  | some c => exact vEv_append P gs r x c (ha c rfl)

lemma valid_append (gs r : List Gate) (c : Option ℕ) (hc : Valid P gs c) : Valid P (gs ++ r) c := by
  intro b hb; have := hc b hb; simp; omega

lemma push_fst (s : (List Gate × (ℕ → Option (Option ℕ)))) (v : ℕ) (c : Option ℕ) :
    ∃ r, (push P s v c).1 = s.1 ++ r ∧ r.length ≤ (if s.2 v = none then 0 else 1) ∧ GoodGates r := by
  unfold push
  rcases h : s.2 v with _ | _ | a <;> rcases c with _ | b <;> simp only [reduceCtorEq, ↓reduceIte]
  · exact ⟨[], by simp, by simp, by simp [GoodGates]⟩
  · exact ⟨[], by simp, by simp, by simp [GoodGates]⟩
  · exact ⟨[], by simp, by simp, by simp [GoodGates]⟩
  · exact ⟨[], by simp, by simp, by simp [GoodGates]⟩
  · exact ⟨[], by simp, by simp, by simp [GoodGates]⟩
  · exact ⟨[⟨GateOp.or, [a, b]⟩], by simp, by simp, by simp [GoodGates]⟩

lemma push_snd_other (s : (List Gate × (ℕ → Option (Option ℕ)))) (v : ℕ) (c : Option ℕ) (u : ℕ) (hu : u ≠ v) :
    (push P s v c).2 u = s.2 u := by
  unfold push
  rcases h : s.2 v with _ | _ | a <;> rcases c with _ | b <;> simp [Function.update_of_ne hu]

lemma push_snd_self (s : (List Gate × (ℕ → Option (Option ℕ)))) (v : ℕ) (c : Option ℕ) : (push P s v c).2 v ≠ none := by
  unfold push
  rcases h : s.2 v with _ | _ | a <;> rcases c with _ | b <;> simp [h]

lemma push_keep (s : (List Gate × (ℕ → Option (Option ℕ)))) (v : ℕ) (c : Option ℕ) (u : ℕ) (hu : s.2 u ≠ none) :
    (push P s v c).2 u ≠ none := by
  by_cases h : u = v
  · subst h; exact push_snd_self P s u c
  · rw [push_snd_other P s v c u h]; exact hu

def RefsOK (s : (List Gate × (ℕ → Option (Option ℕ)))) : Prop := ∀ v c, s.2 v = some c → Valid P s.1 c

lemma valid_none (gs : List Gate) : Valid P gs none := by
  intro b hb; simp at hb

lemma push_refs (s : (List Gate × (ℕ → Option (Option ℕ)))) (v : ℕ) (c : Option ℕ) (hs : RefsOK P s) (hc : Valid P s.1 c) :
    RefsOK P (push P s v c) := by
  intro u d hd
  by_cases huv : u = v
  · subst huv
    unfold push at hd ⊢
    rcases h : s.2 u with _ | _ | a <;> rcases c with _ | b <;>
      simp only [h, Function.update_self, Option.some.injEq] at hd ⊢
    · subst hd; exact valid_none P _
    · subst hd; exact hc
    · exact hs u _ (by rw [h, hd])
    · exact hs u _ (by rw [h, hd])
    · subst hd; exact valid_none P _
    · subst hd; intro b' hb'; simp at hb' ⊢; omega
  · obtain ⟨r, hr, -, -⟩ := push_fst P s v c
    rw [push_snd_other P s v c u huv] at hd
    rw [hr]
    exact valid_append P _ _ _ (hs u d hd)

lemma push_sem (s : (List Gate × (ℕ → Option (Option ℕ)))) (v : ℕ) (c : Option ℕ) (hs : RefsOK P s) (hc : Valid P s.1 c)
    (x : Fin P → Bool) (u : ℕ) :
    aEv P (push P s v c).1 x ((push P s v c).2 u) =
      if u = v then (aEv P s.1 x (s.2 v) || vEv P s.1 x c) else aEv P s.1 x (s.2 u) := by
  by_cases huv : u = v
  · subst huv
    rw [ite_eq_left rfl]
    unfold push
    rcases h : s.2 u with _ | _ | a <;> rcases c with _ | b <;>
      simp only [h, Function.update_self]
    · simp [aEv, vEv]
    · simp [aEv]
    · simp [aEv, vEv]
    · simp [aEv, vEv]
    · simp [aEv, vEv]
    · have ha := hs u (some a) h a rfl
      have hb := hc b rfl
      have hl : (List.ofFn x).length + s.1.length = P + s.1.length := by simp
      simp only [aEv, vEv]
      rw [← hl, dw_getD_snoc]
      simp only [List.map_cons, List.map_nil]
      simp [GateOp.eval]
  · obtain ⟨r, hr, -, -⟩ := push_fst P s v c
    rw [ite_eq_right huv, push_snd_other P s v c u huv, hr]
    exact aEv_append P _ _ _ _ (fun d hd => hs u d hd)

lemma push_count (s : (List Gate × (ℕ → Option (Option ℕ)))) (v : ℕ) (c : Option ℕ) (K : ℕ) :
    (push P s v c).1.length + ((Finset.range K).filter fun u => (push P s v c).2 u ≠ none).card ≤
      s.1.length + ((Finset.range K).filter fun u => s.2 u ≠ none).card + 1 := by
  obtain ⟨r, hr, hrl, -⟩ := push_fst P s v c
  rw [hr, List.length_append]
  by_cases h : s.2 v = none
  · rw [ite_eq_left h] at hrl
    have hsub : ((Finset.range K).filter fun u => (push P s v c).2 u ≠ none) ⊆
        insert v ((Finset.range K).filter fun u => s.2 u ≠ none) := by
      intro u hu
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert] at hu ⊢
      by_cases huv : u = v
      · left; exact huv
      · right; rw [push_snd_other P s v c u huv] at hu; exact hu
    have := Finset.card_le_card hsub
    have := Finset.card_insert_le v ((Finset.range K).filter fun u => s.2 u ≠ none)
    omega
  · rw [ite_eq_right h] at hrl
    have hsub : ((Finset.range K).filter fun u => (push P s v c).2 u ≠ none) ⊆
        ((Finset.range K).filter fun u => s.2 u ≠ none) := by
      intro u hu
      simp only [Finset.mem_filter, Finset.mem_range] at hu ⊢
      by_cases huv : u = v
      · subst huv; exact ⟨hu.1, h⟩
      · rw [push_snd_other P s v c u huv] at hu; exact hu
    have := Finset.card_le_card hsub
    omega

end Phase2

section Step

variable (P L : ℕ) (C : Circuit)

def Pre (s : (List Gate × (ℕ → Option (Option ℕ)))) : Prop := ∃ r, s.1 = phase1 P L C C.gates.length ++ r

lemma pre_append (s : (List Gate × (ℕ → Option (Option ℕ)))) (r : List Gate) (h : Pre P L C s) (a : ℕ → Option (Option ℕ)) :
    Pre P L C (s.1 ++ r, a) := by
  obtain ⟨q, hq⟩ := h
  exact ⟨q ++ r, by simp [hq]⟩

lemma sig_valid (s : (List Gate × (ℕ → Option (Option ℕ)))) (hs : Pre P L C s) (j : ℕ) (hj : j < C.gates.length) (f : ℕ)
    (hf : f < P + L + j) (hd : deg P L C f = 0) : sig P L C j f < P + s.1.length := by
  obtain ⟨q, hq⟩ := hs
  rw [hq, List.length_append, phase1_length]
  unfold sig
  by_cases h1 : f < P
  · rw [ite_eq_left h1]; omega
  · rw [ite_eq_right h1, ite_eq_left hf]
    have hiL : P + L ≤ f := by
      by_contra hc
      have := deg_line P L C f (by omega) (by omega); omega
    have := rank_lt P L C (f - (P + L)) C.gates.length (by omega)
      (by rw [show P + L + (f - (P + L)) = f by omega]; exact hd)
    omega

lemma sig_val (hm : IsMonotoneCircuit C) (s : (List Gate × (ℕ → Option (Option ℕ)))) (hs : Pre P L C s) (j : ℕ) (hj : j < C.gates.length)
    (f : ℕ) (hf : f < P + L + j) (hd : deg P L C f = 0) (x : Fin P → Bool) (y : Fin L → Bool) :
    (dw s.1 (List.ofFn x)).getD (sig P L C j f) false = val P L C x y f := by
  have hv := sig_valid P L C s hs j hj f hf hd
  obtain ⟨q, hq⟩ := hs
  unfold sig at hv ⊢
  by_cases h1 : f < P
  · rw [ite_eq_left h1, dw_point P _ x f h1, val_point P L C x y f h1]
  · rw [ite_eq_right h1, ite_eq_left hf] at hv ⊢
    have hiL : P + L ≤ f := by
      by_contra hc
      have := deg_line P L C f (by omega) (by omega); omega
    have hr := rank_lt P L C (f - (P + L)) C.gates.length (by omega)
      (by rw [show P + L + (f - (P + L)) = f by omega]; exact hd)
    rw [hq, dw_getD_append _ _ _ _ (by simp [phase1_length]; exact hr)]
    rw [phase1_val P L C hm x y C.gates.length le_rfl (f - (P + L)) (by omega)
      (by rw [show P + L + (f - (P + L)) = f by omega]; exact hd)]
    rw [show P + L + (f - (P + L)) = f by omega]

lemma val_indep (hm : IsMonotoneCircuit C) (x : Fin P → Bool) (y y' : Fin L → Bool) (i : ℕ)
    (hd : deg P L C i = 0) : val P L C x y i = val P L C x y' i := by
  by_cases h1 : i < P
  · rw [val_point P L C x y i h1, val_point P L C x y' i h1]
  · by_cases h2 : i < P + L
    · have := deg_line P L C i (by omega) h2; omega
    · by_cases h3 : i < P + L + C.gates.length
      · have e := fun yy => phase1_val P L C hm x yy C.gates.length le_rfl (i - (P + L)) (by omega)
          (by rw [show P + L + (i - (P + L)) = i by omega]; exact hd)
        rw [show P + L + (i - (P + L)) = i by omega] at e
        rw [← e y, ← e y']
      · rw [val_ge P L C x y i (by omega), val_ge P L C x y' i (by omega)]

def andTerm (j : ℕ) (s : (List Gate × (ℕ → Option (Option ℕ)))) (c : Option ℕ) (f : ℕ) : (List Gate × (ℕ → Option (Option ℕ))) × Option ℕ :=
  if f < P + L + j then
    match c with
    | none => (s, some (sig P L C j f))
    | some cw => ((s.1 ++ [⟨GateOp.and, [cw, sig P L C j f]⟩], s.2), some (P + s.1.length))
  else ((s.1 ++ [⟨GateOp.or, []⟩], s.2), some (P + s.1.length))

lemma andTerm_fst (j : ℕ) (s : (List Gate × (ℕ → Option (Option ℕ)))) (c : Option ℕ) (f : ℕ) :
    ∃ r, (andTerm P L C j s c f).1.1 = s.1 ++ r ∧ r.length ≤ 1 ∧ GoodGates r ∧
      (andTerm P L C j s c f).1.2 = s.2 := by
  unfold andTerm
  split_ifs
  · rcases c with _ | cw
    · exact ⟨[], by simp, by simp, by simp [GoodGates], rfl⟩
    · exact ⟨_, rfl, by simp, by simp [GoodGates], rfl⟩
  · exact ⟨_, rfl, by simp, by simp [GoodGates], rfl⟩

lemma andTerm_valid (j : ℕ) (hj : j < C.gates.length) (s : (List Gate × (ℕ → Option (Option ℕ)))) (hs : Pre P L C s) (c : Option ℕ)
    (hc : Valid P s.1 c) (f : ℕ) (hf : f < P + L + j → deg P L C f = 0) :
    Valid P (andTerm P L C j s c f).1.1 (andTerm P L C j s c f).2 := by
  unfold andTerm
  split_ifs with h
  · rcases c with _ | cw
    · intro b hb; simp at hb; subst hb; exact sig_valid P L C s hs j hj f h (hf h)
    · intro b hb; simp at hb ⊢; omega
  · intro b hb; simp at hb ⊢; omega

lemma andTerm_val (hm : IsMonotoneCircuit C) (j : ℕ) (hj : j < C.gates.length) (s : (List Gate × (ℕ → Option (Option ℕ))))
    (hs : Pre P L C s) (c : Option ℕ) (hc : Valid P s.1 c) (f : ℕ)
    (hf : f < P + L + j → deg P L C f = 0) (x : Fin P → Bool) (y : Fin L → Bool) :
    vEv P (andTerm P L C j s c f).1.1 x (andTerm P L C j s c f).2 =
      (vEv P s.1 x c && if f < P + L + j then val P L C x y f else false) := by
  have hl : (List.ofFn x).length + s.1.length = P + s.1.length := by simp
  unfold andTerm
  split_ifs with h
  · rcases c with _ | cw
    · simp only [vEv, Bool.true_and]
      exact sig_val P L C hm s hs j hj f h (hf h) x y
    · simp only [vEv]
      rw [← hl, dw_getD_snoc]
      simp only [List.map_cons, List.map_nil]
      rw [sig_val P L C hm s hs j hj f h (hf h) x y]
      simp [GateOp.eval]
  · simp only [vEv, Bool.and_false]
    rw [← hl, dw_getD_snoc]
    simp [GateOp.eval]

def orFold (j : ℕ) (c : Option ℕ) (l : List ℕ) (s : (List Gate × (ℕ → Option (Option ℕ)))) : (List Gate × (ℕ → Option (Option ℕ))) :=
  l.foldl (fun s i => if i < P + L + j ∧ deg P L C i = 1 then push P s i c else s) s

lemma orFold_cons (j : ℕ) (c : Option ℕ) (i : ℕ) (l : List ℕ) (s : (List Gate × (ℕ → Option (Option ℕ)))) :
    orFold P L C j c (i :: l) s =
      orFold P L C j c l (if i < P + L + j ∧ deg P L C i = 1 then push P s i c else s) := rfl

lemma orFold_fst (j : ℕ) (c : Option ℕ) (l : List ℕ) (s : (List Gate × (ℕ → Option (Option ℕ)))) :
    ∃ r, (orFold P L C j c l s).1 = s.1 ++ r ∧ r.length ≤ l.length ∧ GoodGates r := by
  induction l generalizing s with
  | nil => exact ⟨[], by simp [orFold], by simp, by simp [GoodGates]⟩
  | cons i l ih =>
    rw [orFold_cons]
    split_ifs
    · obtain ⟨r1, h1, l1, g1⟩ := push_fst P s i c
      obtain ⟨r2, h2, l2, g2⟩ := ih (push P s i c)
      refine ⟨r1 ++ r2, by rw [h2, h1]; simp, ?_, goodGates_append _ _ g1 g2⟩
      simp; split_ifs at l1 <;> omega
    · obtain ⟨r2, h2, l2, g2⟩ := ih s
      exact ⟨r2, h2, by simp; omega, g2⟩

lemma orFold_keep (j : ℕ) (c : Option ℕ) (l : List ℕ) (s : (List Gate × (ℕ → Option (Option ℕ)))) (u : ℕ) (hu : s.2 u ≠ none) :
    (orFold P L C j c l s).2 u ≠ none := by
  induction l generalizing s with
  | nil => exact hu
  | cons i l ih =>
    rw [orFold_cons]
    split_ifs
    · exact ih _ (push_keep P s i c u hu)
    · exact ih _ hu

lemma orFold_hit (j : ℕ) (c : Option ℕ) (l : List ℕ) (s : (List Gate × (ℕ → Option (Option ℕ)))) (u : ℕ) (hu : u ∈ l)
    (hy : u < P + L + j ∧ deg P L C u = 1) : (orFold P L C j c l s).2 u ≠ none := by
  induction l generalizing s with
  | nil => simp at hu
  | cons i l ih =>
    rw [orFold_cons]
    rcases List.mem_cons.mp hu with h | h
    · subst h
      rw [ite_eq_left hy]
      exact orFold_keep P L C j c l _ u (push_snd_self P s u c)
    · exact ih _ h

lemma orFold_refs (j : ℕ) (c : Option ℕ) (l : List ℕ) (s : (List Gate × (ℕ → Option (Option ℕ)))) (hs : RefsOK P s)
    (hc : Valid P s.1 c) : RefsOK P (orFold P L C j c l s) ∧ Valid P (orFold P L C j c l s).1 c := by
  induction l generalizing s with
  | nil => exact ⟨hs, hc⟩
  | cons i l ih =>
    rw [orFold_cons]
    split_ifs
    · apply ih
      · exact push_refs P s i c hs hc
      · obtain ⟨r, hr, -, -⟩ := push_fst P s i c
        rw [hr]; exact valid_append P _ _ _ hc
    · exact ih s hs hc

lemma orFold_count (j : ℕ) (c : Option ℕ) (l : List ℕ) (s : (List Gate × (ℕ → Option (Option ℕ)))) (K : ℕ) :
    (orFold P L C j c l s).1.length + ((Finset.range K).filter fun u => (orFold P L C j c l s).2 u ≠ none).card ≤
      s.1.length + ((Finset.range K).filter fun u => s.2 u ≠ none).card + l.length := by
  induction l generalizing s with
  | nil => exact Nat.le_add_right _ _
  | cons i l ih =>
    rw [orFold_cons]
    split_ifs
    · have := ih (push P s i c)
      have := push_count P s i c K
      rw [List.length_cons]; omega
    · have := ih s
      rw [List.length_cons]; omega

lemma orFold_sem (j : ℕ) (c : Option ℕ) (l : List ℕ) (s : (List Gate × (ℕ → Option (Option ℕ)))) (hs : RefsOK P s)
    (hc : Valid P s.1 c) (x : Fin P → Bool) (u : ℕ) :
    aEv P (orFold P L C j c l s).1 x ((orFold P L C j c l s).2 u) =
      (aEv P s.1 x (s.2 u) || (vEv P s.1 x c && decide (u ∈ l ∧ u < P + L + j ∧ deg P L C u = 1))) := by
  induction l generalizing s with
  | nil => simp [orFold]
  | cons i l ih =>
    rw [orFold_cons]
    split_ifs with hy
    · have hr := push_refs P s i c hs hc
      obtain ⟨r, hrr, -, -⟩ := push_fst P s i c
      have hc' : Valid P (push P s i c).1 c := by rw [hrr]; exact valid_append P _ _ _ hc
      rw [ih _ hr hc', push_sem P s i c hs hc x u, hrr, vEv_append P _ _ _ _ hc]
      by_cases hui : u = i
      · subst hui; simp only [ite_true]
        cases aEv P s.1 x (s.2 u) <;> cases vEv P s.1 x c <;> simp [hy]
      · rw [ite_eq_right hui]; simp [hui]
    · rw [ih s hs hc]
      by_cases hui : u = i
      · subst hui; simp [hy]
      · simp [hui]

end Step

section Gate

variable (P L : ℕ) (C : Circuit)

def stepGate (j : ℕ) (s : (List Gate × (ℕ → Option (Option ℕ)))) : (List Gate × (ℕ → Option (Option ℕ))) :=
  if deg P L C (P + L + j) = 1 then
    match s.2 (P + L + j) with
    | none => s
    | some c =>
      match (gt C j).op, (gt C j).inputs with
      | GateOp.or, l => orFold P L C j c l s
      | GateOp.and, [a] => if a < P + L + j ∧ deg P L C a = 1 then push P s a c else s
      | GateOp.and, [a, b] =>
          if a < P + L + j ∧ deg P L C a = 1 then
            push P (andTerm P L C j s c b).1 a (andTerm P L C j s c b).2
          else if b < P + L + j ∧ deg P L C b = 1 then
            push P (andTerm P L C j s c a).1 b (andTerm P L C j s c a).2
          else s
      | _, _ => s
  else s

lemma stepGate_id (j : ℕ) (s : (List Gate × (ℕ → Option (Option ℕ)))) (h : deg P L C (P + L + j) ≠ 1 ∨ s.2 (P + L + j) = none) :
    stepGate P L C j s = s := by
  unfold stepGate
  rcases h with h | h
  · rw [ite_eq_right h]
  · split_ifs
    · rw [h]
    · rfl

lemma stepGate_shape (hm : IsMonotoneCircuit C) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (j : ℕ) (hj : j < C.gates.length) (s : (List Gate × (ℕ → Option (Option ℕ)))) (c : Option ℕ)
    (hd : deg P L C (P + L + j) = 1) (hc : s.2 (P + L + j) = some c) :
    (C.gates[j].op = GateOp.or ∧ stepGate P L C j s = orFold P L C j c C.gates[j].inputs s) ∨
    (∃ a, C.gates[j].op = GateOp.and ∧ C.gates[j].inputs = [a] ∧ a < P + L + j ∧ deg P L C a = 1 ∧
      stepGate P L C j s = push P s a c) ∨
    (∃ a b, C.gates[j].op = GateOp.and ∧ C.gates[j].inputs = [a, b] ∧ a < P + L + j ∧ deg P L C a = 1 ∧
      (b < P + L + j → deg P L C b = 0) ∧
      stepGate P L C j s = push P (andTerm P L C j s c b).1 a (andTerm P L C j s c b).2) ∨
    (∃ a b, C.gates[j].op = GateOp.and ∧ C.gates[j].inputs = [b, a] ∧ a < P + L + j ∧ deg P L C a = 1 ∧
      (b < P + L + j → deg P L C b = 0) ∧
      stepGate P L C j s = push P (andTerm P L C j s c b).1 a (andTerm P L C j s c b).2) := by
  have hfj := hfan _ (List.getElem_mem hj)
  rcases op_cases C hm j hj with hop | hop
  · have hdeg := deg_gate_and P L C j hj hop
    have hst : stepGate P L C j s = match GateOp.and, C.gates[j].inputs with
      | GateOp.or, l => orFold P L C j c l s
      | GateOp.and, [a] => if a < P + L + j ∧ deg P L C a = 1 then push P s a c else s
      | GateOp.and, [a, b] =>
          if a < P + L + j ∧ deg P L C a = 1 then
            push P (andTerm P L C j s c b).1 a (andTerm P L C j s c b).2
          else if b < P + L + j ∧ deg P L C b = 1 then
            push P (andTerm P L C j s c a).1 b (andTerm P L C j s c a).2
          else s
      | _, _ => s := by
      unfold stepGate
      rw [ite_eq_left hd, hc, gt_eq C j hj, hop]
    rcases hl : C.gates[j].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨e, rest⟩⟩⟩
    · rw [hl] at hdeg; simp at hdeg; omega
    · rw [hl] at hdeg hst
      simp at hdeg
      have ha : a < P + L + j ∧ deg P L C a = 1 := by
        by_cases h : a < P + L + j
        · rw [ite_eq_left h] at hdeg; exact ⟨h, by omega⟩
        · rw [ite_eq_right h] at hdeg; omega
      right; left
      refine ⟨a, hop, rfl, ha.1, ha.2, ?_⟩
      rw [hst]; simp only []; rw [ite_eq_left ha]
    · rw [hl] at hdeg hst
      simp at hdeg
      by_cases ha : a < P + L + j ∧ deg P L C a = 1
      · right; right; left
        refine ⟨a, b, hop, rfl, ha.1, ha.2, ?_, ?_⟩
        · intro hb; rw [ite_eq_left ha.1, ite_eq_left hb] at hdeg; omega
        · rw [hst]; simp only []; rw [ite_eq_left ha]
      · have hb : b < P + L + j ∧ deg P L C b = 1 := by
          by_cases h1 : a < P + L + j
          · rw [ite_eq_left h1] at hdeg
            by_cases h2 : b < P + L + j
            · rw [ite_eq_left h2] at hdeg
              have : deg P L C a ≠ 1 := fun h => ha ⟨h1, h⟩
              have h3 : deg P L C a = 0 := by omega
              exact ⟨h2, by omega⟩
            · rw [ite_eq_right h2] at hdeg; exact absurd ⟨h1, by omega⟩ ha
          · rw [ite_eq_right h1] at hdeg
            by_cases h2 : b < P + L + j
            · rw [ite_eq_left h2] at hdeg; exact ⟨h2, by omega⟩
            · rw [ite_eq_right h2] at hdeg; omega
        right; right; right
        refine ⟨b, a, hop, rfl, hb.1, hb.2, ?_, ?_⟩
        · intro ha'; rw [ite_eq_left ha', ite_eq_left hb.1] at hdeg; omega
        · rw [hst]; simp only []; rw [ite_eq_right ha, ite_eq_left hb]
    · rw [hl] at hfj; simp at hfj
  · left
    refine ⟨hop, ?_⟩
    unfold stepGate
    rw [ite_eq_left hd, hc, gt_eq C j hj, hop]

end Gate

section Main

variable (P L : ℕ) (C : Circuit)

lemma eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ) (f g : ℕ → Bool)
    (hfg : ∀ a ∈ l, f a = true → g a = true) (h : op.eval (l.map f) = true) :
    op.eval (l.map g) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id] at h ⊢
    rintro _ ⟨a, ha, rfl⟩
    exact hfg a ha (h _ ⟨a, ha, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id] at h ⊢
    obtain ⟨_, ⟨a, ha, rfl⟩, h2⟩ := h
    exact ⟨_, ⟨a, ha, rfl⟩, hfg a ha h2⟩

lemma val_mono (hm : IsMonotoneCircuit C) (x : Fin P → Bool) (y y' : Fin L → Bool)
    (hy : ∀ u, y u = true → y' u = true) (i : ℕ) (h : val P L C x y i = true) :
    val P L C x y' i = true := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases h1 : i < P
    · rw [val_point P L C x y i h1] at h; rw [val_point P L C x y' i h1]; exact h
    · by_cases h2 : i < P + L
      · rw [val_line P L C x y i (by omega) h2] at h; rw [val_line P L C x y' i (by omega) h2]
        exact hy _ h
      · by_cases h3 : i < P + L + C.gates.length
        · have e : i = P + L + (i - (P + L)) := by omega
          rw [e, val_gate P L C x y _ (by omega)] at h
          rw [e, val_gate P L C x y' _ (by omega)]
          refine eval_mono _ (op_cases C hm _ (by omega)) _ _ _ ?_ h
          intro a _ ha
          by_cases hai : a < P + L + (i - (P + L))
          · rw [ite_eq_left hai] at ha ⊢; exact ih a (by omega) ha
          · rw [ite_eq_right hai] at ha; exact absurd ha (by simp)
        · rw [val_ge P L C x y i (by omega)] at h; exact absurd h (by simp)

lemma phase1_good (hm : IsMonotoneCircuit C) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (k : ℕ)
    (hk : k ≤ C.gates.length) : GoodGates (phase1 P L C k) := by
  induction k with
  | zero => simp [phase1, GoodGates]
  | succ k ih =>
    rw [phase1_succ]
    apply goodGates_append _ _ (ih (by omega))
    split_ifs
    · intro g hg
      simp only [List.mem_singleton] at hg
      subst hg
      unfold copyGate
      rw [gt_eq C k (by omega)]
      exact ⟨op_cases C hm k (by omega), by simp; exact hfan _ (List.getElem_mem (by omega))⟩
    · simp [GoodGates]

def init : (List Gate × (ℕ → Option (Option ℕ))) := (phase1 P L C C.gates.length,
  fun v => if v = C.output ∧ deg P L C v = 1 ∧ v < P + L + C.gates.length then some none else none)

def S : ℕ → (List Gate × (ℕ → Option (Option ℕ)))
  | 0 => init P L C
  | m + 1 => stepGate P L C (C.gates.length - 1 - m) (S m)

def Yc (m : ℕ) : ℕ :=
  ((Finset.range C.gates.length).filter fun j => C.gates.length - m ≤ j ∧ deg P L C (P + L + j) = 1).card

def F (s : (List Gate × (ℕ → Option (Option ℕ)))) (K : ℕ) (x : Fin P → Bool) (y : Fin L → Bool) : Prop :=
  ∃ v < K, deg P L C v = 1 ∧ aEv P s.1 x (s.2 v) = true ∧ val P L C x y v = true

def Cnt (s : (List Gate × (ℕ → Option (Option ℕ)))) (K : ℕ) : ℕ := ((Finset.range K).filter fun u => s.2 u ≠ none).card

def Inv (m : ℕ) (s : (List Gate × (ℕ → Option (Option ℕ)))) : Prop :=
  Pre P L C s ∧ RefsOK P s ∧ GoodGates s.1 ∧
  s.1.length + Cnt s (P + L + C.gates.length - m) ≤ rank P L C C.gates.length + Yc P L C m + 1 ∧
  (∀ x y, val P L C x y C.output = true ↔
    (val P L C x (fun _ => false) C.output = true ∨ F P L C s (P + L + C.gates.length - m) x y)) ∧
  (∀ v, deg P L C v = 1 → Relation.ReflTransGen (Rel P L C) v C.output →
    v < P + L + C.gates.length - m →
    (v = C.output ∨ ∃ g, Rel P L C v g ∧ Relation.ReflTransGen (Rel P L C) g C.output ∧
      P + L + C.gates.length - m ≤ g) → s.2 v ≠ none)

lemma F_succ (s : (List Gate × (ℕ → Option (Option ℕ)))) (p : ℕ) (x : Fin P → Bool) (y : Fin L → Bool) :
    F P L C s (p + 1) x y ↔ F P L C s p x y ∨
      (deg P L C p = 1 ∧ aEv P s.1 x (s.2 p) = true ∧ val P L C x y p = true) := by
  constructor
  · rintro ⟨v, hv, h⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hv with hv | rfl
    · exact Or.inl ⟨v, hv, h⟩
    · exact Or.inr h
  · rintro (⟨v, hv, h⟩ | h)
    · exact ⟨v, by omega, h⟩
    · exact ⟨p, by omega, h⟩

lemma deg_out_le (hl : HasLineDegree (P + L) (Finset.Ico P (P + L)) C 1) : deg P L C C.output ≤ 1 := hl

lemma inv_zero (hm : IsMonotoneCircuit C) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hl : HasLineDegree (P + L) (Finset.Ico P (P + L)) C 1) : Inv P L C 0 (init P L C) := by
  have hdo := deg_out_le P L C hl
  refine ⟨⟨[], by simp [init]⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro v c hc
    simp only [init] at hc
    split_ifs at hc
    · simp at hc; subst hc; exact valid_none P _
  · exact phase1_good P L C hm hfan _ le_rfl
  · have h1 : Yc P L C 0 = 0 := by
      unfold Yc; rw [Finset.card_eq_zero]; ext j; simp; omega
    have h2 : Cnt (init P L C) (P + L + C.gates.length - 0) ≤ 1 := by
      unfold Cnt
      have : ((Finset.range (P + L + C.gates.length - 0)).filter fun u => (init P L C).2 u ≠ none) ⊆
          {C.output} := by
        intro u hu
        rw [Finset.mem_filter] at hu
        obtain ⟨-, hu⟩ := hu
        simp only [init] at hu
        split_ifs at hu with h
        · simp [h.1]
        · simp at hu
      exact le_trans (Finset.card_le_card this) (by simp)
    simp only [init, phase1_length] at h2 ⊢
    rw [h1]; omega
  · intro x y
    by_cases ho : deg P L C C.output = 1 ∧ C.output < P + L + C.gates.length
    · constructor
      · intro h; right
        exact ⟨C.output, by omega, ho.1, by simp [init, ho, aEv, vEv], h⟩
      · rintro (h | ⟨v, -, -, ha, h⟩)
        · exact val_mono P L C hm x _ y (by simp) _ h
        · simp only [init] at ha
          split_ifs at ha with hh
          · rw [hh.1] at h; exact h
          · simp [aEv] at ha
    · have hd0 : deg P L C C.output = 0 := by
        by_cases hlt : C.output < P + L + C.gates.length
        · have : deg P L C C.output ≠ 1 := fun h => ho ⟨h, hlt⟩
          omega
        · exact deg_ge P L C _ (by omega)
      rw [val_indep P L C hm x y (fun _ => false) _ hd0]
      constructor
      · intro h; left; exact h
      · rintro (h | ⟨v, -, hv1, ha, -⟩)
        · exact h
        · simp only [init] at ha
          split_ifs at ha with hh
          · obtain ⟨e, h2, h3⟩ := hh
            subst e
            exact absurd ⟨h2, h3⟩ ho
          · simp [aEv] at ha
  · intro v hv1 _ hvK hor
    rcases hor with rfl | ⟨g, ⟨_, i, rfl, _⟩, _, hg⟩
    · simp [init, hv1, show C.output < P + L + C.gates.length by omega]
    · omega

end Main

section Sem

variable (P L : ℕ) (C : Circuit)

lemma val_or (x : Fin P → Bool) (y : Fin L → Bool) (j : ℕ) (hj : j < C.gates.length)
    (hop : C.gates[j].op = GateOp.or) :
    val P L C x y (P + L + j) = true ↔
      ∃ i ∈ C.gates[j].inputs, i < P + L + j ∧ val P L C x y i = true := by
  rw [val_gate P L C x y j hj, hop]
  simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
  constructor
  · rintro ⟨_, ⟨i, hi, rfl⟩, h⟩
    by_cases hlt : i < P + L + j
    · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [ite_eq_right hlt] at h; exact absurd h (by simp)
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨_, ⟨i, hi, rfl⟩, by rw [ite_eq_left hlt]; exact h⟩

lemma val_and (x : Fin P → Bool) (y : Fin L → Bool) (j : ℕ) (hj : j < C.gates.length)
    (hop : C.gates[j].op = GateOp.and) :
    val P L C x y (P + L + j) =
      (C.gates[j].inputs.map fun i => if i < P + L + j then val P L C x y i else false).all id := by
  rw [val_gate P L C x y j hj, hop]; rfl

lemma aEv_stable (s : (List Gate × (ℕ → Option (Option ℕ)))) (r : List Gate) (hs : RefsOK P s) (x : Fin P → Bool) (u : ℕ) :
    aEv P (s.1 ++ r) x (s.2 u) = aEv P s.1 x (s.2 u) :=
  aEv_append P _ _ _ _ (fun d hd => hs u d hd)

lemma push_case_sem (s s1 : (List Gate × (ℕ → Option (Option ℕ)))) (r : List Gate) (h1 : s1.1 = s.1 ++ r) (h2 : s1.2 = s.2)
    (hs : RefsOK P s) (τ : Option ℕ)
    (hτ : Valid P s1.1 τ) (a p : ℕ) (hap : a < p) (hda : deg P L C a = 1) (hdp : deg P L C p = 1)
    (x : Fin P → Bool) (y : Fin L → Bool)
    (hkey : (aEv P s.1 x (s.2 p) = true ∧ val P L C x y p = true) ↔
      (vEv P s1.1 x τ = true ∧ val P L C x y a = true)) :
    (F P L C s p x y ∨ (deg P L C p = 1 ∧ aEv P s.1 x (s.2 p) = true ∧ val P L C x y p = true)) ↔
      F P L C (push P s1 a τ) p x y := by
  have hs1 : RefsOK P s1 := fun v c hc => by
    rw [h2] at hc; rw [h1]; exact valid_append P _ _ _ (hs v c hc)
  have hst : ∀ u, aEv P s1.1 x (s1.2 u) = aEv P s.1 x (s.2 u) := by
    intro u; rw [h1, h2]; exact aEv_stable P s r hs x u
  have hsem := fun u => push_sem P s1 a τ hs1 hτ x u
  constructor
  · rintro (⟨v, hv, hdv, hav, hval⟩ | ⟨-, hcv, hvp⟩)
    · refine ⟨v, hv, hdv, ?_, hval⟩
      rw [hsem v]
      split_ifs with hva
      · subst hva; rw [hst]; simp [hav]
      · rw [hst]; exact hav
    · obtain ⟨h1', h2'⟩ := hkey.mp ⟨hcv, hvp⟩
      refine ⟨a, hap, hda, ?_, h2'⟩
      rw [hsem a, ite_eq_left rfl]; simp [h1']
  · rintro ⟨v, hv, hdv, hav, hval⟩
    rw [hsem v] at hav
    split_ifs at hav with hva
    · subst hva
      rw [hst] at hav
      rcases Bool.or_eq_true_iff.mp hav with h | h
      · exact Or.inl ⟨v, hv, hdv, h, hval⟩
      · obtain ⟨h1', h2'⟩ := hkey.mpr ⟨h, hval⟩
        exact Or.inr ⟨hdp, h1', h2'⟩
    · rw [hst] at hav
      exact Or.inl ⟨v, hv, hdv, hav, hval⟩

lemma cnt_succ (s : (List Gate × (ℕ → Option (Option ℕ)))) (p : ℕ) : Cnt s (p + 1) = Cnt s p + if s.2 p ≠ none then 1 else 0 := by
  unfold Cnt
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · simp

lemma yc_succ (m : ℕ) (hm : m < C.gates.length) :
    Yc P L C (m + 1) = Yc P L C m + if deg P L C (P + L + (C.gates.length - 1 - m)) = 1 then 1 else 0 := by
  unfold Yc
  split_ifs with hd
  · have e : ((Finset.range C.gates.length).filter fun j => C.gates.length - (m + 1) ≤ j ∧ deg P L C (P + L + j) = 1) =
        insert (C.gates.length - 1 - m)
          ((Finset.range C.gates.length).filter fun j => C.gates.length - m ≤ j ∧ deg P L C (P + L + j) = 1) := by
      ext j'
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
      constructor
      · rintro ⟨h1, h2, h3⟩
        by_cases e : j' = C.gates.length - 1 - m
        · left; exact e
        · right; exact ⟨h1, by omega, h3⟩
      · rintro (rfl | ⟨h1, h2, h3⟩)
        · exact ⟨by omega, by omega, hd⟩
        · exact ⟨h1, by omega, h3⟩
    rw [e, Finset.card_insert_of_notMem (by simp; omega)]
  · have e : ((Finset.range C.gates.length).filter fun j => C.gates.length - (m + 1) ≤ j ∧ deg P L C (P + L + j) = 1) =
        ((Finset.range C.gates.length).filter fun j => C.gates.length - m ≤ j ∧ deg P L C (P + L + j) = 1) := by
      ext j'
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨h1, h2, h3⟩
        by_cases e : j' = C.gates.length - 1 - m
        · subst e; exact absurd h3 hd
        · exact ⟨h1, by omega, h3⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, by omega, h3⟩
    rw [e]; simp

lemma reach_step (hm : IsMonotoneCircuit C) (hl : HasLineDegree (P + L) (Finset.Ico P (P + L)) C 1)
    (j : ℕ) (hj : j < C.gates.length) (s s' : (List Gate × (ℕ → Option (Option ℕ))))
    (hreach : ∀ v, deg P L C v = 1 → Relation.ReflTransGen (Rel P L C) v C.output →
      v < P + L + j + 1 →
      (v = C.output ∨ ∃ g, Rel P L C v g ∧ Relation.ReflTransGen (Rel P L C) g C.output ∧
        P + L + j + 1 ≤ g) → s.2 v ≠ none)
    (hkeep : ∀ u, s.2 u ≠ none → s'.2 u ≠ none)
    (hhit : deg P L C (P + L + j) = 1 → s.2 (P + L + j) ≠ none →
      ∀ v ∈ C.gates[j].inputs, v < P + L + j → deg P L C v = 1 → s'.2 v ≠ none) :
    ∀ v, deg P L C v = 1 → Relation.ReflTransGen (Rel P L C) v C.output →
      v < P + L + j →
      (v = C.output ∨ ∃ g, Rel P L C v g ∧ Relation.ReflTransGen (Rel P L C) g C.output ∧
        P + L + j ≤ g) → s'.2 v ≠ none := by
  intro v hdv hR hvp hor
  rcases hor with rfl | ⟨g, hRg, hRgo, hg⟩
  · exact hkeep _ (hreach _ hdv hR (by omega) (Or.inl rfl))
  · by_cases hgp : g = P + L + j
    · subst hgp
      have hdo := deg_out_le P L C hl
      have h1 := deg_le_of_rel P L C hm _ _ hRg
      have h2 := deg_le_of_reach P L C hm _ _ hRgo
      have hdp : deg P L C (P + L + j) = 1 := by omega
      have hne : s.2 (P + L + j) ≠ none := by
        apply hreach _ hdp hRgo (by omega)
        rcases Relation.ReflTransGen.cases_head hRgo with h | ⟨c, hc, hc2⟩
        · exact Or.inl h
        · exact Or.inr ⟨c, hc, hc2, by have := hc.1; omega⟩
      obtain ⟨hvlt, i, hi, hmem⟩ := hRg
      have hij : i.val = j := by omega
      have : C.gates.get i = C.gates[j] := by
        rw [List.get_eq_getElem]; congr 1
      rw [this] at hmem
      exact hhit hdp hne v hmem hvlt hdv
    · exact hkeep _ (hreach _ hdv hR (by omega) (Or.inr ⟨g, hRg, hRgo, by omega⟩))

end Sem

section StepInv

variable (P L : ℕ) (C : Circuit)

lemma pre_of (s s' : (List Gate × (ℕ → Option (Option ℕ)))) (r : List Gate) (h : s'.1 = s.1 ++ r) (hp : Pre P L C s) : Pre P L C s' := by
  obtain ⟨q, hq⟩ := hp
  exact ⟨q ++ r, by rw [h, hq]; simp⟩

lemma inv_step (hm : IsMonotoneCircuit C) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hl : HasLineDegree (P + L) (Finset.Ico P (P + L)) C 1) (m : ℕ) (hmt : m < C.gates.length)
    (s : (List Gate × (ℕ → Option (Option ℕ)))) (hs : Inv P L C m s) :
    Inv P L C (m + 1) (stepGate P L C (C.gates.length - 1 - m) s) := by
  obtain ⟨hpre, hrefs, hgood, hcnt, hsem, hreach⟩ := hs
  have hYc := yc_succ P L C m hmt
  generalize hjd : C.gates.length - 1 - m = j at hYc ⊢
  have hj : j < C.gates.length := by omega
  have hK : P + L + C.gates.length - m = P + L + j + 1 := by omega
  have hK' : P + L + C.gates.length - (m + 1) = P + L + j := by omega
  rw [hK] at hcnt hsem hreach
  unfold Inv
  rw [hK']
  have hCnt := cnt_succ s (P + L + j)
  have H0 : ∀ x v, v < P + L + j + 1 → deg P L C v = 1 → aEv P s.1 x (s.2 v) = true →
      val P L C x (fun _ => false) v = true → val P L C x (fun _ => false) C.output = true :=
    fun x v hv hd ha h0 => (hsem x (fun _ => false)).mpr (Or.inr ⟨v, hv, hd, ha, h0⟩)
  by_cases hact : deg P L C (P + L + j) = 1 ∧ s.2 (P + L + j) ≠ none
  · obtain ⟨hdp, hne⟩ := hact
    obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp hne
    have hvc : Valid P s.1 c := hrefs _ c hc
    have hcv : ∀ x, aEv P s.1 x (s.2 (P + L + j)) = vEv P s.1 x c := by intro x; rw [hc]; rfl
    rw [ite_eq_left hdp] at hYc
    rw [ite_eq_left hne] at hCnt
    rcases stepGate_shape P L C hm hfan j hj s c hdp hc with
      ⟨hop, hst⟩ | ⟨a, hop, hin, hap, hda, hst⟩ | ⟨a, b, hop, hin, hap, hda, hb, hst⟩ |
      ⟨a, b, hop, hin, hap, hda, hb, hst⟩
    ·
      rw [hst]
      obtain ⟨r, hr, hrl, hgr⟩ := orFold_fst P L C j c C.gates[j].inputs s
      have hlen : C.gates[j].inputs.length ≤ 2 := hfan _ (List.getElem_mem hj)
      refine ⟨pre_of P L C s _ r hr hpre, (orFold_refs P L C j c _ s hrefs hvc).1,
        by rw [hr]; exact goodGates_append _ _ hgood hgr, ?_, ?_, ?_⟩
      · have := orFold_count P L C j c C.gates[j].inputs s (P + L + j)
        unfold Cnt at *; omega
      · intro x y
        rw [hsem x y, F_succ]
        have hos := fun u => orFold_sem P L C j c C.gates[j].inputs s hrefs hvc x u
        constructor
        · rintro (h0 | (⟨v, hv, hdv, hav, hval⟩ | ⟨-, hap', hvp⟩))
          · exact Or.inl h0
          · right; refine ⟨v, hv, hdv, ?_, hval⟩; rw [hos v]; simp [hav]
          · rw [hcv] at hap'
            obtain ⟨i, hi, hip, hvi⟩ := (val_or P L C x y j hj hop).mp hvp
            have hdi := deg_le_of_input P L C hm j hj i hi hip
            by_cases hdi1 : deg P L C i = 1
            · right; refine ⟨i, hip, hdi1, ?_, hvi⟩; rw [hos i]; simp [hap', hi, hip, hdi1]
            · left
              have hdi0 : deg P L C i = 0 := by omega
              rw [val_indep P L C hm x y (fun _ => false) i hdi0] at hvi
              apply H0 x (P + L + j) (by omega) hdp (by rw [hcv]; exact hap')
              exact (val_or P L C x _ j hj hop).mpr ⟨i, hi, hip, hvi⟩
        · rintro (h0 | ⟨v, hv, hdv, hav, hval⟩)
          · exact Or.inl h0
          · right
            rw [hos v] at hav
            rcases Bool.or_eq_true_iff.mp hav with h | h
            · exact Or.inl ⟨v, hv, hdv, h, hval⟩
            · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
              obtain ⟨h1, h2, -, -⟩ := h
              exact Or.inr ⟨hdp, by rw [hcv]; exact h1, (val_or P L C x y j hj hop).mpr ⟨v, h2, hv, hval⟩⟩
      · exact reach_step P L C hm hl j hj s _ hreach
          (fun u hu => orFold_keep P L C j c _ s u hu)
          (fun _ _ v hv hvp hdv => orFold_hit P L C j c _ s v hv ⟨hvp, hdv⟩)
    ·
      rw [hst]
      obtain ⟨r, hr, hrl, hgr⟩ := push_fst P s a c
      refine ⟨pre_of P L C s _ r hr hpre, push_refs P s a c hrefs hvc,
        by rw [hr]; exact goodGates_append _ _ hgood hgr, ?_, ?_, ?_⟩
      · have := push_count P s a c (P + L + j)
        unfold Cnt at *; omega
      · intro x y
        rw [hsem x y, F_succ]
        have key := push_case_sem P L C s s [] (by simp) rfl hrefs c hvc a (P + L + j) hap hda hdp x y
          (by rw [hcv, val_and P L C x y j hj hop, hin]; simp [hap])
        rw [key]
      · exact reach_step P L C hm hl j hj s _ hreach
          (fun u hu => push_keep P s a c u hu)
          (fun _ _ v hv _ _ => by rw [hin] at hv; simp at hv; subst hv; exact push_snd_self P s v c)
    ·
      rw [hst]
      obtain ⟨r1, hr1, hrl1, hgr1, h2⟩ := andTerm_fst P L C j s c b
      obtain ⟨r, hr, hrl, hgr⟩ := push_fst P (andTerm P L C j s c b).1 a (andTerm P L C j s c b).2
      have hs1 : RefsOK P (andTerm P L C j s c b).1 := fun v d hd => by
        rw [h2] at hd; rw [hr1]; exact valid_append P _ _ _ (hrefs v d hd)
      have hτ := andTerm_valid P L C j hj s hpre c hvc b hb
      refine ⟨pre_of P L C s _ (r1 ++ r) (by rw [hr, hr1]; simp) hpre, push_refs P _ a _ hs1 hτ,
        by rw [hr, hr1]; exact goodGates_append _ _ (goodGates_append _ _ hgood hgr1) hgr, ?_, ?_, ?_⟩
      · have := push_count P (andTerm P L C j s c b).1 a (andTerm P L C j s c b).2 (P + L + j)
        have e1 : (andTerm P L C j s c b).1.1.length = s.1.length + r1.length := by rw [hr1]; simp
        unfold Cnt at *; rw [h2] at this; omega
      · intro x y
        rw [hsem x y, F_succ]
        have key := push_case_sem P L C s (andTerm P L C j s c b).1 r1 hr1 h2 hrefs _ hτ a (P + L + j)
          hap hda hdp x y (by
            rw [hcv, andTerm_val P L C hm j hj s hpre c hvc b hb x y, val_and P L C x y j hj hop, hin]
            simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id, ite_eq_left hap,
              Bool.and_true, Bool.and_eq_true]
            tauto)
        rw [key]
      · exact reach_step P L C hm hl j hj s _ hreach
          (fun u hu => push_keep P _ a _ u (by rw [h2]; exact hu))
          (fun _ _ v hv hvp hdv => by
            rw [hin] at hv; simp at hv
            rcases hv with rfl | rfl
            · exact push_snd_self P _ v _
            · have := hb hvp; omega)
    ·
      rw [hst]
      obtain ⟨r1, hr1, hrl1, hgr1, h2⟩ := andTerm_fst P L C j s c b
      obtain ⟨r, hr, hrl, hgr⟩ := push_fst P (andTerm P L C j s c b).1 a (andTerm P L C j s c b).2
      have hs1 : RefsOK P (andTerm P L C j s c b).1 := fun v d hd => by
        rw [h2] at hd; rw [hr1]; exact valid_append P _ _ _ (hrefs v d hd)
      have hτ := andTerm_valid P L C j hj s hpre c hvc b hb
      refine ⟨pre_of P L C s _ (r1 ++ r) (by rw [hr, hr1]; simp) hpre, push_refs P _ a _ hs1 hτ,
        by rw [hr, hr1]; exact goodGates_append _ _ (goodGates_append _ _ hgood hgr1) hgr, ?_, ?_, ?_⟩
      · have := push_count P (andTerm P L C j s c b).1 a (andTerm P L C j s c b).2 (P + L + j)
        have e1 : (andTerm P L C j s c b).1.1.length = s.1.length + r1.length := by rw [hr1]; simp
        unfold Cnt at *; rw [h2] at this; omega
      · intro x y
        rw [hsem x y, F_succ]
        have key := push_case_sem P L C s (andTerm P L C j s c b).1 r1 hr1 h2 hrefs _ hτ a (P + L + j)
          hap hda hdp x y (by
            rw [hcv, andTerm_val P L C hm j hj s hpre c hvc b hb x y, val_and P L C x y j hj hop, hin]
            simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id, ite_eq_left hap,
              Bool.and_true, Bool.and_eq_true]
            tauto)
        rw [key]
      · exact reach_step P L C hm hl j hj s _ hreach
          (fun u hu => push_keep P _ a _ u (by rw [h2]; exact hu))
          (fun _ _ v hv hvp hdv => by
            rw [hin] at hv; simp at hv
            rcases hv with rfl | rfl
            · have := hb hvp; omega
            · exact push_snd_self P _ v _)
  ·
    have hst := stepGate_id P L C j s (by
      by_cases h : deg P L C (P + L + j) = 1
      · right; by_contra h'; exact hact ⟨h, h'⟩
      · left; exact h)
    rw [hst]
    refine ⟨hpre, hrefs, hgood, ?_, ?_, ?_⟩
    · split_ifs at hYc hCnt <;> omega
    · intro x y
      rw [hsem x y, F_succ]
      constructor
      · rintro (h0 | h | ⟨hd, ha, -⟩)
        · exact Or.inl h0
        · exact Or.inr h
        · have : s.2 (P + L + j) = none := by by_contra h'; exact hact ⟨hd, h'⟩
          rw [this] at ha; simp [aEv] at ha
      · rintro (h0 | h)
        · exact Or.inl h0
        · exact Or.inr (Or.inl h)
    · exact reach_step P L C hm hl j hj s s hreach (fun u hu => hu)
        (fun hd hne => absurd ⟨hd, hne⟩ hact)

end StepInv

section Final

variable (P L : ℕ) (C : Circuit)

lemma inv_all (hm : IsMonotoneCircuit C) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hl : HasLineDegree (P + L) (Finset.Ico P (P + L)) C 1) (m : ℕ) (hmt : m ≤ C.gates.length) :
    Inv P L C m (S P L C m) := by
  induction m with
  | zero => exact inv_zero P L C hm hfan hl
  | succ m ih => exact inv_step P L C hm hfan hl m (by omega) _ (ih (by omega))

def oIdx (s : (List Gate × (ℕ → Option (Option ℕ)))) (u : ℕ) : ℕ :=
  match s.2 u with
  | some (some w) => w
  | _ => P + s.1.length

lemma aEv_read (s : (List Gate × (ℕ → Option (Option ℕ)))) (x : Fin P → Bool) (u : ℕ) :
    aEv P s.1 x (s.2 u) = true ↔
      (s.2 u = some none ∨ (dw s.1 (List.ofFn x)).getD (oIdx P s u) false = true) := by
  unfold oIdx
  rcases h : s.2 u with _ | _ | w
  · simp only [aEv, reduceCtorEq, false_or, Bool.false_eq_true, false_iff]
    rw [dw_getD_ge _ _ _ (by simp)]; simp
  · simp [aEv, vEv]
  · simp [aEv, vEv]

lemma rank_add_yc : rank P L C C.gates.length + Yc P L C C.gates.length ≤ C.gates.length := by
  unfold rank Yc
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.range C.gates.length) (fun j => deg P L C (P + L + j) = 0)
  have hsub : ((Finset.range C.gates.length).filter fun j =>
      C.gates.length - C.gates.length ≤ j ∧ deg P L C (P + L + j) = 1) ⊆
      ((Finset.range C.gates.length).filter fun j => ¬ deg P L C (P + L + j) = 0) := by
    intro j hj
    simp only [Finset.mem_filter] at hj ⊢
    exact ⟨hj.1, by omega⟩
  have := Finset.card_le_card hsub
  simp only [Finset.card_range] at h
  omega

end Final

section OrBudget

variable (P L : ℕ) (C : Circuit)

def orCount (gs : List Gate) : ℕ :=
  gs.countP fun g => match g.op with
    | GateOp.or => true
    | _ => false

lemma orCount_append (a b : List Gate) :
    orCount (a ++ b) = orCount a + orCount b := by
  simp [orCount, List.countP_append]

lemma push_or_delta (s : List Gate × (ℕ → Option (Option ℕ))) (v : ℕ) (c : Option ℕ) :
    orCount (push P s v c).1 + s.1.length = orCount s.1 + (push P s v c).1.length := by
  unfold push
  split <;> simp [orCount, Nat.add_assoc, Nat.add_comm]

lemma push_or_count (s : List Gate × (ℕ → Option (Option ℕ))) (v : ℕ) (c : Option ℕ) (K : ℕ) :
    orCount (push P s v c).1 + Cnt (push P s v c) K ≤ orCount s.1 + Cnt s K + 1 := by
  have h₁ := push_count P s v c K
  have h₂ := push_or_delta P s v c
  unfold Cnt
  omega

lemma andTerm_or_count (j : ℕ) (s : List Gate × (ℕ → Option (Option ℕ)))
    (c : Option ℕ) (f : ℕ) (hf : f < P + L + j) :
    orCount (andTerm P L C j s c f).1.1 = orCount s.1 ∧
      (andTerm P L C j s c f).1.2 = s.2 := by
  unfold andTerm
  rw [ite_eq_left hf]
  cases c <;> simp [orCount]

lemma orFold_or_count (j : ℕ) (c : Option ℕ) (l : List ℕ)
    (s : List Gate × (ℕ → Option (Option ℕ))) (K : ℕ) :
    orCount (orFold P L C j c l s).1 + Cnt (orFold P L C j c l s) K ≤
      orCount s.1 + Cnt s K + l.length := by
  induction l generalizing s with
  | nil => simp [orFold]
  | cons i l ih =>
    rw [orFold_cons]
    split_ifs
    · have := ih (push P s i c)
      have := push_or_count P s i c K
      rw [List.length_cons]
      omega
    · have := ih s
      rw [List.length_cons]
      omega

lemma step_or_count (hm : IsMonotoneCircuit C)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (P + L) C)
    (j : ℕ) (hj : j < C.gates.length) (s : List Gate × (ℕ → Option (Option ℕ))) :
    orCount (stepGate P L C j s).1 + Cnt (stepGate P L C j s) (P + L + j) ≤
      orCount s.1 + Cnt s (P + L + j + 1) +
        (if deg P L C (P + L + j) = 1 then orCount [gt C j] else 0) := by
  have hcnt := cnt_succ s (P + L + j)
  by_cases hd : deg P L C (P + L + j) = 1
  · rw [ite_eq_left hd]
    cases hc : s.2 (P + L + j) with
    | none =>
      rw [stepGate_id P L C j s (Or.inr hc)]
      simp only [hc, ne_eq, not_true_eq_false, ite_false, Nat.add_zero] at hcnt
      omega
    | some c =>
      simp only [hc, ne_eq, reduceCtorEq, not_false_eq_true, ite_true] at hcnt
      have hread : ∀ i ∈ C.gates[j].inputs, i < P + L + j := by
        simpa [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hj] using hrb j hj
      rcases stepGate_shape P L C hm hfan j hj s c hd hc with hor | hand | hand | hand
      · obtain ⟨hop, hs⟩ := hor
        rw [hs]
        have hb := orFold_or_count P L C j c C.gates[j].inputs s (P + L + j)
        have hf := hfan C.gates[j] (List.getElem_mem hj)
        have ho : orCount [gt C j] = 1 := by simp [gt_eq C j hj, orCount, hop]
        omega
      · obtain ⟨a, hop, hin, ha, hda, hs⟩ := hand
        rw [hs]
        have hb := push_or_count P s a c (P + L + j)
        have ho : orCount [gt C j] = 0 := by simp [gt_eq C j hj, orCount, hop]
        omega
      · obtain ⟨a, b, hop, hin, ha, hda, hdb, hs⟩ := hand
        rw [hs]
        have hb := hread b (by simp [hin])
        obtain ⟨ho', hr'⟩ := andTerm_or_count P L C j s c b hb
        have he : Cnt (andTerm P L C j s c b).1 (P + L + j) = Cnt s (P + L + j) := by
          unfold Cnt
          rw [hr']
        have hpush := push_or_count P (andTerm P L C j s c b).1 a (andTerm P L C j s c b).2 (P + L + j)
        have ho : orCount [gt C j] = 0 := by simp [gt_eq C j hj, orCount, hop]
        omega
      · obtain ⟨a, b, hop, hin, ha, hda, hdb, hs⟩ := hand
        rw [hs]
        have hb := hread b (by simp [hin])
        obtain ⟨ho', hr'⟩ := andTerm_or_count P L C j s c b hb
        have he : Cnt (andTerm P L C j s c b).1 (P + L + j) = Cnt s (P + L + j) := by
          unfold Cnt
          rw [hr']
        have hpush := push_or_count P (andTerm P L C j s c b).1 a (andTerm P L C j s c b).2 (P + L + j)
        have ho : orCount [gt C j] = 0 := by simp [gt_eq C j hj, orCount, hop]
        omega
  · rw [ite_eq_right hd, stepGate_id P L C j s (Or.inl hd)]
    omega

def orDebit (k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range k, if deg P L C (P + L + j) = 1 then orCount [gt C j] else 0

lemma orDebit_zero : orDebit P L C 0 = 0 := by simp [orDebit]

lemma orDebit_succ (k : ℕ) :
    orDebit P L C (k + 1) = orDebit P L C k +
      (if deg P L C (P + L + k) = 1 then orCount [gt C k] else 0) := by
  simp [orDebit, Finset.sum_range_succ]

lemma or_budget_invariant (hm : IsMonotoneCircuit C)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (P + L) C)
    (m : ℕ) (hm' : m ≤ C.gates.length) :
    orCount (S P L C m).1 + Cnt (S P L C m) (P + L + C.gates.length - m) +
      orDebit P L C (C.gates.length - m) ≤
      orCount (phase1 P L C C.gates.length) + orDebit P L C C.gates.length + 1 := by
  induction m with
  | zero =>
    simp only [S, Nat.sub_zero]
    have hcnt : Cnt (init P L C) (P + L + C.gates.length) ≤ 1 := by
      unfold Cnt
      have hs : ((Finset.range (P + L + C.gates.length)).filter
          fun u => (init P L C).2 u ≠ none) ⊆ {C.output} := by
        intro u hu
        simp only [Finset.mem_filter] at hu
        simp only [init] at hu
        split_ifs at hu with h
        · simpa using h.1
        · simp at hu
      have := Finset.card_le_card hs
      simpa using this
    change orCount (phase1 P L C C.gates.length) + _ + _ ≤ _
    omega
  | succ m ih =>
    have hm0 : m < C.gates.length := by omega
    have hi := ih (by omega)
    have hs := step_or_count P L C hm hfan hrb (C.gates.length - 1 - m) (by omega) (S P L C m)
    have hd := orDebit_succ P L C (C.gates.length - 1 - m)
    have hindex : C.gates.length - 1 - m + 1 = C.gates.length - m := by omega
    rw [hindex] at hd
    simp only [S]
    have hindexA : P + L + (C.gates.length - 1 - m) = P + L + C.gates.length - (m + 1) := by omega
    have hindexB : P + L + (C.gates.length - 1 - m) + 1 = P + L + C.gates.length - m := by omega
    have hindexC : C.gates.length - 1 - m = C.gates.length - (m + 1) := by omega
    rw [hindexB, hindexA] at hs
    rw [hindexC] at hd hs ⊢
    have hindexD : P + L + (C.gates.length - (m + 1)) = P + L + C.gates.length - (m + 1) := by omega
    rw [hindexD] at hd
    omega

lemma phase1_debit_le (k : ℕ) (hk : k ≤ C.gates.length) :
    orCount (phase1 P L C k) + orDebit P L C k ≤ orCount (C.gates.take k) := by
  induction k with
  | zero => simp [phase1, orDebit, orCount]
  | succ k ih =>
    have ih' := ih (by omega)
    rw [phase1_succ, orDebit_succ, List.take_succ_eq_append_getElem (by omega), orCount_append, orCount_append]
    have hcopy : orCount [copyGate P L C k] = orCount [gt C k] := by simp [orCount, copyGate]
    have hgt := gt_eq C k (by omega)
    by_cases hz : deg P L C (P + L + k) = 0
    · have ho : deg P L C (P + L + k) ≠ 1 := by omega
      rw [ite_eq_left hz, ite_eq_right ho, hcopy, hgt]
      omega
    · rw [ite_eq_right hz]
      have hempty : orCount [] = 0 := by simp [orCount]
      rw [hempty]
      split_ifs
      · rw [hgt]; omega
      · omega

lemma final_or_budget (hm : IsMonotoneCircuit C)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (P + L) C) :
    orCount (S P L C C.gates.length).1 + Cnt (S P L C C.gates.length) (P + L) ≤
      orCount C.gates + 1 := by
  have hi := or_budget_invariant P L C hm hfan hrb C.gates.length le_rfl
  have hp := phase1_debit_le P L C C.gates.length le_rfl
  simp only [Nat.add_sub_cancel, Nat.sub_self, orDebit_zero, Nat.add_zero, List.take_length] at hi hp
  omega

lemma reachable_or_budget (hm : IsMonotoneCircuit C)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (P + L) C)
    (hl : HasLineDegree (P + L) (Finset.Ico P (P + L)) C 1)
    (N : Finset (Fin L))
    (hN : ∀ u ∈ N, Relation.ReflTransGen (Rel P L C) (P + u.val) C.output) :
    orCount (S P L C C.gates.length).1 + N.card ≤ orCount C.gates + 1 := by
  obtain ⟨_, _, _, _, _, hreach⟩ := inv_all P L C hm hfan hl C.gates.length le_rfl
  have hN' : N.card ≤ Cnt (S P L C C.gates.length) (P + L) := by
    unfold Cnt
    apply Finset.card_le_card_of_injOn (fun u : Fin L => P + u.val)
    · intro u hu
      have hR := hN u hu
      apply Finset.mem_coe.mpr
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr (by change P + u.val < P + L; omega), ?_⟩
      apply hreach (P + u.val) (deg_line P L C _ (by omega) (by omega)) hR (by omega)
      rcases Relation.ReflTransGen.cases_head hR with h | ⟨c, hc, hc2⟩
      · exact Or.inl h
      · exact Or.inr ⟨c, hc, hc2, by obtain ⟨_, i, rfl, _⟩ := hc; omega⟩
    · intro a _ b _ h
      exact Fin.ext (by simpa using h)
  have := final_or_budget P L C hm hfan hrb
  omega

end OrBudget

section Backward

variable (P L : ℕ) (C : Circuit)

def Back (P : ℕ) (gs : List Gate) : Prop :=
  ∀ j (hj : j < gs.length), ∀ i ∈ gs[j].inputs, i < P + j

lemma back_snoc (gs : List Gate) (g : Gate) (hb : Back P gs)
    (hg : ∀ i ∈ g.inputs, i < P + gs.length) : Back P (gs ++ [g]) := by
  intro j hj i hi
  by_cases h : j < gs.length
  · rw [List.getElem_append_left h] at hi
    exact hb j h i hi
  · have hj' : j = gs.length := by
      simp only [List.length_append, List.length_singleton] at hj
      omega
    subst hj'
    rw [List.getElem_append_right (by omega)] at hi
    simpa using hg i (by simpa using hi)

lemma phase1_back (hm : IsMonotoneCircuit C)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (P + L) C)
    (k : ℕ) (hk : k ≤ C.gates.length) : Back P (phase1 P L C k) := by
  induction k with
  | zero => simp [phase1, Back]
  | succ k ih =>
    rw [phase1_succ]
    split_ifs with hd
    · apply back_snoc P _ _ (ih (by omega))
      intro i hi
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hi
      have hak : a < P + L + k := by
        apply hrb k (by omega) a
        simpa [PEqualNP.MetaComplexity.NestedCover.gateAt, gt, dflt] using ha
      have hmem : a ∈ C.gates[k].inputs := by simpa [gt_eq C k (by omega)] using ha
      have hda := deg_le_of_input P L C hm k (by omega) a hmem hak
      rw [hd] at hda
      rw [phase1_length]
      unfold sig
      split_ifs with hpa
      · omega
      · have hline : P + L ≤ a := by
          by_contra h
          have := deg_line P L C a (by omega) (by omega)
          omega
        have hr := rank_lt P L C (a - (P + L)) k (by omega)
          (by rw [show P + L + (a - (P + L)) = a by omega]; omega)
        omega
    · simpa using ih (by omega)

lemma push_back (s : List Gate × (ℕ → Option (Option ℕ))) (v : ℕ) (c : Option ℕ)
    (hb : Back P s.1) (hs : RefsOK P s) (hc : Valid P s.1 c) : Back P (push P s v c).1 := by
  unfold push
  rcases h : s.2 v with _ | _ | a <;> rcases c with _ | b <;> simp only
  · exact hb
  · exact hb
  · exact hb
  · exact hb
  · exact hb
  · apply back_snoc P _ _ hb
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hia | hib
    · subst i; exact hs v (some a) h a rfl
    · subst i; exact hc b rfl

lemma andTerm_back (j : ℕ) (hj : j < C.gates.length)
    (s : List Gate × (ℕ → Option (Option ℕ))) (c : Option ℕ) (f : ℕ)
    (hb : Back P s.1) (hs : Pre P L C s) (hc : Valid P s.1 c)
    (hf : f < P + L + j) (hd : deg P L C f = 0) :
    Back P (andTerm P L C j s c f).1.1 := by
  unfold andTerm
  rw [ite_eq_left hf]
  cases c with
  | none => exact hb
  | some cw =>
    apply back_snoc P _ _ hb
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hia | hib
    · subst i; exact hc cw rfl
    · subst i; exact sig_valid P L C s hs j hj f hf hd

lemma andTerm_refs (j : ℕ) (s : List Gate × (ℕ → Option (Option ℕ)))
    (c : Option ℕ) (f : ℕ) (hs : RefsOK P s) : RefsOK P (andTerm P L C j s c f).1 := by
  obtain ⟨r, hr, _, _, hsame⟩ := andTerm_fst P L C j s c f
  intro v d hd
  rw [hsame] at hd
  rw [hr]
  exact valid_append P _ _ _ (hs v d hd)

lemma orFold_back (j : ℕ) (c : Option ℕ) (l : List ℕ)
    (s : List Gate × (ℕ → Option (Option ℕ))) (hb : Back P s.1)
    (hs : RefsOK P s) (hc : Valid P s.1 c) : Back P (orFold P L C j c l s).1 := by
  induction l generalizing s with
  | nil => exact hb
  | cons i l ih =>
    rw [orFold_cons]
    split_ifs
    · apply ih
      · exact push_back P s i c hb hs hc
      · exact push_refs P s i c hs hc
      · obtain ⟨r, hr, _, _⟩ := push_fst P s i c
        rw [hr]
        exact valid_append P _ _ _ hc
    · exact ih s hb hs hc

lemma step_back (hm : IsMonotoneCircuit C)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (P + L) C)
    (j : ℕ) (hj : j < C.gates.length) (s : List Gate × (ℕ → Option (Option ℕ)))
    (hb : Back P s.1) (hpre : Pre P L C s) (href : RefsOK P s) :
    Back P (stepGate P L C j s).1 := by
  by_cases hd : deg P L C (P + L + j) = 1
  · cases hc : s.2 (P + L + j) with
    | none => rw [stepGate_id P L C j s (Or.inr hc)]; exact hb
    | some c =>
      have hcv := href (P + L + j) c hc
      have hread : ∀ i ∈ C.gates[j].inputs, i < P + L + j := by
        simpa [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hj] using hrb j hj
      rcases stepGate_shape P L C hm hfan j hj s c hd hc with hor | hand | hand | hand
      · rw [hor.2]
        exact orFold_back P L C j c _ s hb href hcv
      · obtain ⟨a, _, _, _, _, hst⟩ := hand
        rw [hst]
        exact push_back P s a c hb href hcv
      · obtain ⟨a, b, _, hin, _, _, hdb, hst⟩ := hand
        rw [hst]
        have hblt := hread b (by simp [hin])
        exact push_back P _ a _
          (andTerm_back P L C j hj s c b hb hpre hcv hblt (hdb hblt))
          (andTerm_refs P L C j s c b href)
          (andTerm_valid P L C j hj s hpre c hcv b hdb)
      · obtain ⟨a, b, _, hin, _, _, hdb, hst⟩ := hand
        rw [hst]
        have hblt := hread b (by simp [hin])
        exact push_back P _ a _
          (andTerm_back P L C j hj s c b hb hpre hcv hblt (hdb hblt))
          (andTerm_refs P L C j s c b href)
          (andTerm_valid P L C j hj s hpre c hcv b hdb)
  · rw [stepGate_id P L C j s (Or.inl hd)]
    exact hb

lemma extracted_back (hm : IsMonotoneCircuit C)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (P + L) C)
    (hl : HasLineDegree (P + L) (Finset.Ico P (P + L)) C 1)
    (m : ℕ) (hm' : m ≤ C.gates.length) : Back P (S P L C m).1 := by
  induction m with
  | zero => exact phase1_back P L C hm hrb C.gates.length le_rfl
  | succ m ih =>
    obtain ⟨hpre, href, _⟩ := inv_all P L C hm hfan hl m (by omega)
    exact step_back P L C hm hfan hrb _ (by omega) _ (ih (by omega)) hpre href

end Backward

lemma extraction (P L : ℕ) (C : Circuit) (N : Finset (Fin L))
    (hm : IsMonotoneCircuit C) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (P + L) C)
    (hl : HasLineDegree (P + L) (Finset.Ico P (P + L)) C 1)
    (hN : ∀ u ∈ N, Relation.ReflTransGen (Rel P L C) (P + u.val) C.output) :
    ∃ (D : Circuit) (T : Finset (Fin L)) (o : Fin L → ℕ),
      IsMonotoneCircuit D ∧ (∀ g ∈ D.gates, g.inputs.length ≤ 2) ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack P D ∧
      D.size + N.card ≤ C.size + 1 ∧ orCount D.gates + N.card ≤ orCount C.gates + 1 ∧
      ∀ (x : Fin P → Bool) (y : Fin L → Bool),
        C.eval (List.ofFn x ++ List.ofFn y) =
          (C.eval (List.ofFn x ++ List.ofFn (fun _ : Fin L => false)) ||
            decide (∃ u : Fin L, y u = true ∧
              (u ∈ T ∨ (D.wires (List.ofFn x)).getD (o u) false = true))) := by
  obtain ⟨_, _, hgood, hcnt, hsem, hreach⟩ := inv_all P L C hm hfan hl C.gates.length le_rfl
  refine ⟨⟨(S P L C C.gates.length).1, 0⟩,
    Finset.univ.filter (fun u : Fin L => (S P L C C.gates.length).2 (P + u.val) = some none),
    fun u => oIdx P (S P L C C.gates.length) (P + u.val), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg; exact (hgood g hg).1
  · intro g hg; exact (hgood g hg).2
  · intro j hj i hi
    apply extracted_back P L C hm hfan hrb hl C.gates.length le_rfl j hj i
    simpa [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hj] using hi
  · have hN' : N.card ≤ Cnt (S P L C C.gates.length) (P + L + C.gates.length - C.gates.length) := by
      unfold Cnt
      apply Finset.card_le_card_of_injOn (fun u : Fin L => P + u.val)
      · intro u hu
        have hR := hN u hu
        apply Finset.mem_coe.mpr
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_range.mpr (by change P + u.val < P + L + C.gates.length - C.gates.length; omega), ?_⟩
        apply hreach (P + u.val) (deg_line P L C _ (by omega) (by omega)) hR (by omega)
        rcases Relation.ReflTransGen.cases_head hR with h | ⟨c, hc, hc2⟩
        · exact Or.inl h
        · exact Or.inr ⟨c, hc, hc2, by obtain ⟨_, i, rfl, _⟩ := hc; omega⟩
      · intro a _ b _ h
        exact Fin.ext (by simpa using h)
    have hry := rank_add_yc P L C
    change (S P L C C.gates.length).1.length + N.card ≤ C.gates.length + 1
    omega
  · exact reachable_or_budget P L C hm hfan hrb hl N hN
  · intro x y
    change val P L C x y C.output =
      (val P L C x (fun _ => false) C.output || _)
    apply Bool.eq_iff_iff.mpr
    rw [hsem x y]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    apply or_congr_right
    constructor
    · rintro ⟨v, hv, hdv, hav, hval⟩
      have hvP : P ≤ v := by
        by_contra h
        rw [deg_point P L C v (by omega)] at hdv
        omega
      rw [val_line P L C x y v hvP (by omega)] at hval
      refine ⟨⟨v - P, by omega⟩, hval, ?_⟩
      have ev : P + (v - P) = v := by omega
      rcases (aEv_read P _ x v).mp hav with h | h
      · left; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; rw [ev]; exact h
      · right; simp only []; rw [ev]; exact h
    · rintro ⟨u, hyu, hu⟩
      refine ⟨P + u.val, by omega, deg_line P L C _ (by omega) (by omega),
        (aEv_read P _ x _).mpr ?_, ?_⟩
      · rcases hu with h | h
        · left; simpa using h
        · right; exact h
      · rw [val_line P L C x y (P + u.val) (by omega) (by omega)]
        have he : (⟨P + u.val - P, by omega⟩ : Fin L) = u := Fin.ext (by simp)
        rw [he]; exact hyu

end LinearExtraction


namespace LinearIncidenceBudget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_2583.LinearExtraction

lemma val_eq_of_unreachable (P L : ℕ) (C : Circuit)
    (x : Fin P → Bool) (y y' : Fin L → Bool) (u : Fin L)
    (hy : ∀ l, l ≠ u → y l = y' l) (w : ℕ)
    (hn : ¬ Relation.ReflTransGen (Rel P L C) (P + u.val) w) :
    val P L C x y w = val P L C x y' w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hp : w < P
    · rw [val_point P L C x y w hp, val_point P L C x y' w hp]
    · by_cases hl : w < P + L
      · rw [val_line P L C x y w (by omega) hl, val_line P L C x y' w (by omega) hl]
        apply hy
        intro he
        have he' : P + u.val = w := by have := congrArg Fin.val he; simp only at this; omega
        exact hn (he' ▸ Relation.ReflTransGen.refl)
      · by_cases hg : w < P + L + C.gates.length
        · have hw : w = P + L + (w - (P + L)) := by omega
          rw [hw, val_gate P L C x y _ (by omega), val_gate P L C x y' _ (by omega)]
          congr 1
          apply List.map_congr_left
          intro a ha
          by_cases ha' : a < P + L + (w - (P + L))
          · simp only [ite_eq_left ha']
            apply ih a (by omega)
            intro hr
            apply hn
            exact hr.tail ⟨by omega, ⟨w - (P + L), by omega⟩, hw, ha⟩
          · simp only [ite_eq_right ha']
        · rw [val_ge P L C x y w (by omega), val_ge P L C x y' w (by omega)]

lemma all_lines_reachable {P L : ℕ} (I : Fin P → Fin L → Prop) [DecidableRel I]
    (C : Circuit) (hne : ∀ l, ∃ p, I p l)
    (hc : ∀ (x : Fin P → Bool) (y : Fin L → Bool),
      C.eval (List.ofFn x ++ List.ofFn y) = decide (∃ p l, I p l ∧ x p = true ∧ y l = true)) :
    ∀ l : Fin L, Relation.ReflTransGen (Rel P L C) (P + l.val) C.output := by
  intro l
  by_contra hn
  have he := val_eq_of_unreachable P L C (fun _ => true) (fun k => decide (k = l))
    (fun _ => false) l (by intro k hk; simp [hk]) C.output hn
  change C.eval (List.ofFn (fun _ : Fin P => true) ++ List.ofFn (fun k : Fin L => decide (k = l))) =
    C.eval (List.ofFn (fun _ : Fin P => true) ++ List.ofFn (fun _ : Fin L => false)) at he
  rw [hc, hc] at he
  obtain ⟨p, hp⟩ := hne l
  simp at he
  exact he p hp

noncomputable def orPrefix (C : Circuit) (k : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range k).filter fun j => (gateAt C j).op = GateOp.or

lemma orCount_prefix (C : Circuit) (k : ℕ) (hk : k ≤ C.gates.length) :
    orCount (C.gates.take k) = (orPrefix C k).card := by
  classical
  unfold orPrefix
  induction k with
  | zero => simp [orCount]
  | succ k ih =>
    rw [List.take_succ_eq_append_getElem (by omega), orCount_append, ih (by omega),
      Finset.range_add_one, Finset.filter_insert]
    have he := Repair.gateAt_eq (C := C) (j := k) (by omega)
    by_cases hop : (gateAt C k).op = GateOp.or
    · rw [ite_eq_left hop, Finset.card_insert_of_notMem (by simp)]
      have hs : orCount [C.gates[k]] = 1 := by simp [orCount, ← he, hop]
      omega
    · rw [ite_eq_right hop]
      have hs : orCount [C.gates[k]] = 0 := by
        cases he' : C.gates[k].op <;> simp_all [orCount]
      omega

lemma orCount_eq_orGates (C : Circuit) : orCount C.gates = (PurePointBudget.orGates C).card := by
  simpa [PurePointBudget.orGates, orPrefix] using orCount_prefix C C.gates.length le_rfl

lemma coefficient_network {P L : ℕ} (I : Fin P → Fin L → Prop) [DecidableRel I]
    (C : Circuit) (hne : ∀ l, ∃ p, I p l)
    (hm : IsMonotoneCircuit C) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hrb : ReadsBack (P + L) C)
    (hl : HasLineDegree (P + L) (Finset.Ico P (P + L)) C 1)
    (hc : ∀ (x : Fin P → Bool) (y : Fin L → Bool),
      C.eval (List.ofFn x ++ List.ofFn y) = decide (∃ p l, I p l ∧ x p = true ∧ y l = true)) :
    ∃ (D : Circuit) (o : Fin L → ℕ), Monotone2 D ∧ ReadsBack P D ∧
      orCount D.gates + L ≤ orCount C.gates + 1 ∧
      (∀ l, o l < P + D.gates.length) ∧
      ∀ l (x : Fin P → Bool), Repair.val D (List.ofFn x) (o l) = decide (∃ p, I p l ∧ x p = true) := by
  classical
  obtain ⟨D, T, o, hDm, hDf, hDr, _, hDo, hsem⟩ :=
    extraction P L C Finset.univ hm hfan hrb hl
      (by intro l _; exact all_lines_reachable I C hne hc l)
  have hT : ∀ l, l ∉ T := by
    intro l ht
    have he := hsem (fun _ => false) (fun k => decide (k = l))
    rw [hc, hc] at he
    simp at he
    exact he.1 ht
  have ho : ∀ l (x : Fin P → Bool), Repair.val D (List.ofFn x) (o l) = decide (∃ p, I p l ∧ x p = true) := by
    intro l x
    have he := hsem x (fun k => decide (k = l))
    rw [hc, hc] at he
    have hleft : (∃ p k, I p k ∧ x p = true ∧ decide (k = l) = true) ↔ ∃ p, I p l ∧ x p = true := by
      simp
    have hright : (∃ u : Fin L, decide (u = l) = true ∧
        (u ∈ T ∨ (D.wires (List.ofFn x)).getD (o u) false = true)) ↔
        (D.wires (List.ofFn x)).getD (o l) false = true := by
      simp [hT]
    simp only [hleft, hright, Bool.false_eq_true, and_false, exists_false, decide_false, Bool.false_or] at he
    simpa [Repair.val] using he.symm
  refine ⟨D, o, ?_, hDr, ?_, ?_, ho⟩
  · intro g hg
    exact ⟨by simpa using hDm g hg, hDf g hg⟩
  · simpa using hDo
  · intro l
    by_contra hn
    have hv := Repair.val_ge (n := P) (C := D) (x := List.ofFn (fun _ : Fin P => true))
      (by simp) (u := o l) (by omega)
    rw [ho] at hv
    obtain ⟨p, hp⟩ := hne l
    simp at hv
    exact hv p hp

lemma incidence_or_budget {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit)
    (hsize : ∀ l : Fin N, (Finset.univ.filter fun p => I p l).card = q + 1)
    (hunique : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (hm : IsMonotoneCircuit C) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hrb : ReadsBack (N + N) C)
    (hl : HasLineDegree (N + N) (Finset.Ico N (N + N)) C 1)
    (hc : ∀ (x y : Fin N → Bool), C.eval (List.ofFn x ++ List.ofFn y) =
      decide (∃ p l, I p l ∧ x p = true ∧ y l = true)) :
    N * (q + 1) ≤ orCount C.gates + 1 := by
  have hne : ∀ l, ∃ p, I p l := by
    intro l
    have hp : 0 < (Finset.univ.filter fun p => I p l).card := by rw [hsize]; omega
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hp
    exact ⟨p, (Finset.mem_filter.mp hp).2⟩
  obtain ⟨D, o, hDm, hDr, hDo, hov, hoc⟩ := coefficient_network I C hne hm hfan hrb hl hc
  have hb := PurePointBudget.incidence_or_budget I hsize hunique hDm hDr o hov hoc
  rw [← orCount_eq_orGates] at hb
  simp only [Nat.mul_add, Nat.mul_one]
  omega

lemma posted_incidence_or_budget {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit)
    (hsize : ∀ l : Fin N, (Finset.univ.filter fun p => I p l).card = q + 1)
    (hunique : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (hC : PEqualNP.TopForm.IsAO2 (N + N) C)
    (hl : HasLineDegree (N + N) (Finset.Ico N (N + N)) C 1)
    (hc : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) :
    N * (q + 1) ≤ (PurePointBudget.orGates C).card + 1 := by
  rw [← orCount_eq_orGates]
  apply incidence_or_budget I C hsize hunique
  · exact hC.1
  · intro g hg; exact Nat.le_of_eq (hC.2.2 g hg)
  · exact hC.2.1
  · exact hl
  · intro x y
    have he := hc (Fin.append x y)
    have happ : List.ofFn (Fin.append x y) = List.ofFn x ++ List.ofFn y := by
      rw [List.ofFn_add]
      congr 1
      · congr 1
        funext i
        exact Fin.append_left x y i
      · congr 1
        funext i
        exact Fin.append_right x y i
    simpa only [circuitFun, happ, Fin.append_left, Fin.append_right] using he

end LinearIncidenceBudget



namespace LinearAnd

section SourceLinearTranspose

namespace PlaneArcTranspose

inductive LinearOp where
  | add (u v : ℕ)
  | scale (u scalar : ℕ)
  | copy (u : ℕ)
  | zero

def LinearOp.edge (op : LinearOp) (scalar : ℕ → Prop) (src : ℕ) : Prop :=
  match op with
  | .add u v => src = u ∨ src = v
  | .scale u s => src = u ∧ scalar s
  | .copy u => src = u
  | .zero => False

def LinearOp.eval (op : LinearOp) (scalar state : ℕ → Prop) : Prop :=
  match op with
  | .add u v => state u ∨ state v
  | .scale u s => state u ∧ scalar s
  | .copy u => state u
  | .zero => False

lemma eval_iff_edge (op : LinearOp) (scalar state : ℕ → Prop) :
    op.eval scalar state ↔ ∃ src, op.edge scalar src ∧ state src := by
  cases op with
  | add u v =>
    simp only [LinearOp.eval, LinearOp.edge]
    constructor
    · rintro (h | h)
      · exact ⟨u, Or.inl rfl, h⟩
      · exact ⟨v, Or.inr rfl, h⟩
    · rintro ⟨j, (rfl | rfl), hj⟩
      · exact Or.inl hj
      · exact Or.inr hj
  | scale u s => simp [LinearOp.eval, LinearOp.edge, and_assoc, and_comm]
  | copy u => simp [LinearOp.eval, LinearOp.edge]
  | zero => simp [LinearOp.eval, LinearOp.edge]

structure Assignment where
  dst : ℕ
  op : LinearOp

def Assignment.push (a : Assignment) (scalar state : ℕ → Prop) (w : ℕ) : Prop :=
  if w = a.dst then a.op.eval scalar state else state w

def Assignment.pull (a : Assignment) (scalar demand : ℕ → Prop) (w : ℕ) : Prop :=
  (w ≠ a.dst ∧ demand w) ∨ (demand a.dst ∧ a.op.edge scalar w)

def forward (scalar : ℕ → Prop) (ops : List Assignment) (state : ℕ → Prop) : ℕ → Prop :=
  ops.foldl (fun st a => a.push scalar st) state

def reverse (scalar : ℕ → Prop) (ops : List Assignment) (demand : ℕ → Prop) : ℕ → Prop :=
  ops.foldr (fun a st => a.pull scalar st) demand

lemma transpose_step (a : Assignment) (scalar state demand : ℕ → Prop) :
    (∃ w, demand w ∧ a.push scalar state w) ↔ (∃ w, a.pull scalar demand w ∧ state w) := by
  constructor
  · rintro ⟨w, hd, hv⟩
    by_cases h : w = a.dst
    · subst w
      obtain ⟨src, he, hs⟩ := (eval_iff_edge _ _ _).mp
        (show a.op.eval scalar state from by simpa [Assignment.push] using hv)
      exact ⟨src, Or.inr ⟨hd, he⟩, hs⟩
    · exact ⟨w, Or.inl ⟨h, hd⟩, by simpa [Assignment.push, h] using hv⟩
  · rintro ⟨w, (⟨hne, hd⟩ | ⟨hd, he⟩), hs⟩
    · exact ⟨w, hd, by simpa [Assignment.push, hne] using hs⟩
    · exact ⟨a.dst, hd, by simpa [Assignment.push] using
        (eval_iff_edge a.op scalar state).mpr ⟨w, he, hs⟩⟩

lemma transpose (ops : List Assignment) (scalar state demand : ℕ → Prop) :
    (∃ w, demand w ∧ forward scalar ops state w) ↔
      (∃ w, reverse scalar ops demand w ∧ state w) := by
  induction ops generalizing state with
  | nil => rfl
  | cons a ops ih =>
    change (∃ w, demand w ∧ forward scalar ops (a.push scalar state) w) ↔
        ∃ w, a.pull scalar (reverse scalar ops demand) w ∧ state w
    exact (ih _).trans (transpose_step a _ _ _)

lemma transpose_coefficient (ops : List Assignment) (scalar : ℕ → Prop) (src dst : ℕ) :
    forward scalar ops (fun w => w = src) dst ↔ reverse scalar ops (fun w => w = dst) src := by
  simpa using transpose ops scalar (fun w => w = src) (fun w => w = dst)

lemma reverse_adds {ι : Type*} (V : Finset ι) (uses : ι → ℕ)
    (inputs adds scales aliases : ℕ)
    (live : ∀ v ∈ V, 1 ≤ uses v)
    (vertices : V.card = inputs + adds + scales + aliases)
    (edges : ∑ v ∈ V, uses v = 2 * adds + scales + aliases + 1) :
    (∑ v ∈ V, (uses v - 1)) + inputs = adds + 1 := by
  have h : ∑ v ∈ V, ((uses v - 1) + 1) = ∑ v ∈ V, uses v :=
    Finset.sum_congr rfl (fun v hv => Nat.sub_add_cancel (live v hv))
  rw [Finset.sum_add_distrib] at h
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at h
  omega

end PlaneArcTranspose

end SourceLinearTranspose


namespace CircuitNormalization

namespace Deg2

open PEqualNP.CircuitLowerBounds

inductive G where
  | and (a b : ℕ)
  | or (a b : ℕ)
  | cst (v : Bool)
  deriving DecidableEq, Repr

def G.kids : G → List ℕ
  | .and a b => [a, b]
  | .or a b => [a, b]
  | .cst _ => []

structure Dag (N : ℕ) where

  gates : List G

  out : ℕ

namespace Dag

variable {N : ℕ}

def size (D : Dag N) : ℕ := D.gates.length

def gateAt (D : Dag N) (i : ℕ) : Option G :=
  if N + N ≤ i then D.gates[i - (N + N)]? else none

def val (D : Dag N) (x : Fin (N + N) → Bool) (i : ℕ) : Bool :=
  if h : i < N + N then x ⟨i, h⟩ else
  match D.gates[i - (N + N)]? with
  | some (.and a b) =>
      (if _ : a < i then D.val x a else false) && (if _ : b < i then D.val x b else false)
  | some (.or a b) =>
      (if _ : a < i then D.val x a else false) || (if _ : b < i then D.val x b else false)
  | some (.cst v) => v
  | none => false
termination_by i

def deg (D : Dag N) (i : ℕ) : ℕ :=
  if i < N + N then (if N ≤ i then 1 else 0) else
  match D.gates[i - (N + N)]? with
  | some (.and a b) =>
      (if _ : a < i then D.deg a else 0) + (if _ : b < i then D.deg b else 0)
  | some (.or a b) =>
      max (if _ : a < i then D.deg a else 0) (if _ : b < i then D.deg b else 0)
  | some (.cst _) => 0
  | none => 0
termination_by i

def WF (D : Dag N) : Prop := ∀ i g, D.gateAt i = some g → ∀ c ∈ g.kids, c < i

end Dag

def trGate (i : ℕ) (g : Gate) : G :=
  match g.op, g.inputs with
  | .and, [] => .cst true
  | .or, [] => .cst false
  | .and, [a] => if a < i then .or a a else .cst false
  | .or, [a] => if a < i then .or a a else .cst false
  | .and, [a, b] => if a < i ∧ b < i then .and a b else .cst false
  | .or, [a, b] =>
      if a < i ∧ b < i then .or a b else if a < i then .or a a
      else if b < i then .or b b else .cst false
  | _, _ => .cst false

def ofCircuit (N : ℕ) (C : Circuit) : Dag N :=
  { gates := C.gates.mapIdx (fun j g => trGate (N + N + j) g), out := C.output }

def lineMarks (N : ℕ) : Finset ℕ := Finset.Ico N (N + N)

end Deg2

namespace Deg2.Api

open PEqualNP.CircuitLowerBounds

variable {N : ℕ}

lemma gateAt_some {D : Dag N} {i : ℕ} {g : G} (h : D.gateAt i = some g) :
    N + N ≤ i ∧ D.gates[i - (N + N)]? = some g := by
  unfold Dag.gateAt at h
  split_ifs at h with hi
  exact ⟨hi, h⟩

lemma card03a_size (C : Circuit) : (ofCircuit N C).size = C.size := by
  simp [Dag.size, ofCircuit, Circuit.size]

lemma trGate_kids (i : ℕ) (g : Gate) : ∀ c ∈ (trGate i g).kids, c < i := by
  intro c hc
  unfold trGate at hc
  split at hc <;> (try split_ifs at hc) <;> simp_all [G.kids] <;> omega

lemma card03b_wf (C : Circuit) : (ofCircuit N C).WF := by
  intro i g hg c hc
  obtain ⟨hi, hg⟩ := gateAt_some hg
  simp only [ofCircuit, List.getElem?_mapIdx] at hg
  cases h : C.gates[i - (N + N)]? with
  | none => rw [h] at hg; cases hg
  | some g0 =>
    rw [h] at hg
    simp only [Option.map_some, Option.some.injEq] at hg
    subst hg
    have := trGate_kids _ g0 c hc
    omega

end Deg2.Api

namespace LineDegTest

open PEqualNP.CircuitLowerBounds

def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

def Dg (gs : List Gate) (n : ℕ) (marked : Finset ℕ) : List ℕ :=
  gs.foldl (fun d g => d ++ [g.lineDegree d])
    ((List.range n).map fun i => if i ∈ marked then 1 else 0)

lemma W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]

lemma Dg_snoc (gs : List Gate) (g : Gate) (n : ℕ) (marked : Finset ℕ) :
    Dg (gs ++ [g]) n marked = Dg gs n marked ++ [g.lineDegree (Dg gs n marked)] := by
  simp [Dg, List.foldl_append]

lemma W_length (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_snoc]; simp [ih]; omega

lemma Dg_length (gs : List Gate) (n : ℕ) (marked : Finset ℕ) :
    (Dg gs n marked).length = n + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Dg]
  | append_singleton gs g ih => rw [Dg_snoc]; simp [ih]; omega

lemma getD_snoc {α : Type} (l : List α) (a d : α) (t : ℕ) :
    (l ++ [a]).getD t d =
      if t < l.length then l.getD t d else if t = l.length then a else d := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h1 : t < l.length
  · rw [ite_eq_left h1, List.getElem?_append_left h1]
  · rw [ite_eq_right h1, List.getElem?_append_right (by omega)]
    by_cases h2 : t = l.length
    · subst h2; simp
    · rw [ite_eq_right h2]
      have : t - l.length ≠ 0 := by omega
      simp [List.getElem?_cons, this]

lemma ofFn_getD {n : ℕ} (f : Fin n → Bool) (k : ℕ) :
    (List.ofFn f).getD k false = if h : k < n then f ⟨k, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases h : k < n <;> simp [h]

end LineDegTest

namespace Deg2.Bridge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

variable {N : ℕ}

lemma api_prefix (D D' : Dag N) (h : D.gates <+: D'.gates) (i : ℕ) (hi : i < N + N + D.size)
    (x : Fin (N + N) → Bool) : D'.val x i = D.val x i ∧ D'.deg i = D.deg i := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    have hv : ∀ a, (if _ : a < i then D'.val x a else false) =
        (if _ : a < i then D.val x a else false) := by
      intro a
      split_ifs with ha
      · exact (ih a ha (by omega)).1
      · rfl
    have hd : ∀ a, (if _ : a < i then D'.deg a else 0) = (if _ : a < i then D.deg a else 0) := by
      intro a
      split_ifs with ha
      · exact (ih a ha (by omega)).2
      · rfl
    have hg : ¬ i < N + N → D'.gates[i - (N + N)]? = D.gates[i - (N + N)]? := by
      intro h0
      obtain ⟨t, ht⟩ := h
      rw [← ht, List.getElem?_append_left (by unfold Dag.size at hi; omega)]
    constructor
    · conv_lhs => rw [Dag.val]
      conv_rhs => rw [Dag.val]
      split_ifs with h0
      · rfl
      · rw [hg h0]
        cases D.gates[i - (N + N)]? with
        | none => rfl
        | some g =>
          cases g with
          | and a b => dsimp only; rw [hv a, hv b]
          | or a b => dsimp only; rw [hv a, hv b]
          | cst v => rfl
    · conv_lhs => rw [Dag.deg]
      conv_rhs => rw [Dag.deg]
      by_cases h0 : i < N + N
      · rw [ite_eq_left h0, ite_eq_left h0]
      · rw [ite_eq_right h0, ite_eq_right h0, hg h0]
        cases D.gates[i - (N + N)]? with
        | none => rfl
        | some g =>
          cases g with
          | and a b => dsimp only; rw [hd a, hd b]
          | or a b => dsimp only; rw [hd a, hd b]
          | cst v => rfl

def gval (r : ℕ → Bool) : G → Bool
  | .and a b => r a && r b
  | .or a b => r a || r b
  | .cst v => v

def gdeg (r : ℕ → ℕ) : G → ℕ
  | .and a b => r a + r b
  | .or a b => max (r a) (r b)
  | .cst _ => 0

lemma val_deg_ge (D : Dag N) {i : ℕ} (hi : N + N + D.size ≤ i) (x : Fin (N + N) → Bool) :
    D.val x i = false ∧ D.deg i = 0 := by
  have hn : D.gates[i - (N + N)]? = none := by
    rw [List.getElem?_eq_none]; unfold Dag.size at hi; omega
  constructor
  · rw [Dag.val, dif_neg (by omega), hn]
  · rw [Dag.deg, ite_eq_right (by omega), hn]

lemma top_snoc (D D' : Dag N) (g : G) (h : D'.gates = D.gates ++ [g]) (x : Fin (N + N) → Bool) :
    D'.val x (N + N + D.size) =
        gval (fun a => if _ : a < N + N + D.size then D.val x a else false) g ∧
      D'.deg (N + N + D.size) = gdeg (fun a => if _ : a < N + N + D.size then D.deg a else 0) g := by
  have hp : D.gates <+: D'.gates := h ▸ List.prefix_append _ _
  have hv : ∀ a, (if _ : a < N + N + D.size then D'.val x a else false) =
      (if _ : a < N + N + D.size then D.val x a else false) := by
    intro a
    split_ifs with ha
    · exact (api_prefix D D' hp a ha x).1
    · rfl
  have hd : ∀ a, (if _ : a < N + N + D.size then D'.deg a else 0) =
      (if _ : a < N + N + D.size then D.deg a else 0) := by
    intro a
    split_ifs with ha
    · exact (api_prefix D D' hp a ha x).2
    · rfl
  have hg : D'.gates[N + N + D.size - (N + N)]? = some g := by
    rw [h, Nat.add_sub_cancel_left, List.getElem?_append_right (by unfold Dag.size; omega)]
    simp [Dag.size]
  constructor
  · rw [Dag.val, dif_neg (by omega), hg]
    cases g with
    | and a b => dsimp only; rw [hv a, hv b]; rfl
    | or a b => dsimp only; rw [hv a, hv b]; rfl
    | cst v => rfl
  · rw [Dag.deg, ite_eq_right (by omega), hg]
    cases g with
    | and a b => dsimp only; rw [hd a, hd b]; rfl
    | or a b => dsimp only; rw [hd a, hd b]; rfl
    | cst v => rfl

lemma getD_ge_false {l : List Bool} {k : ℕ} (h : l.length ≤ k) : l.getD k false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

lemma getD_ge_zero {l : List ℕ} {k : ℕ} (h : l.length ≤ k) : l.getD k 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

lemma trGate_val (i : ℕ) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (r : ℕ → Bool) (hr : ∀ k, i ≤ k → r k = false) :
    gval r (trGate i g) = g.op.eval (g.inputs.map r) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hl⟩ := hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · rcases hop with rfl | rfl <;> simp [trGate, gval, GateOp.eval]
  · rcases hop with rfl | rfl <;> simp only [trGate] <;>
      (split_ifs with ha
       · simp [gval, GateOp.eval]
       · simp [gval, GateOp.eval, hr a (by omega)])
  · rcases hop with rfl | rfl <;> simp only [trGate] <;> split_ifs with h1 h2 h3 <;>
      simp only [gval, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.any_cons,
        List.all_nil, List.any_nil, id, Bool.and_true, Bool.or_false]
    · by_cases ha : a < i
      · rw [hr b (by omega), Bool.and_false]
      · rw [hr a (by omega), Bool.false_and]
    · rw [hr b (by omega), Bool.or_false, Bool.or_self]
    · rw [hr a (by omega), Bool.false_or, Bool.or_self]
    · rw [hr a (by omega), hr b (by omega), Bool.or_false]
  · simp at hl

lemma gdeg_mono {r r' : ℕ → ℕ} (h : ∀ k, r k ≤ r' k) (g : G) : gdeg r g ≤ gdeg r' g := by
  cases g with
  | and a b => exact Nat.add_le_add (h a) (h b)
  | or a b => exact max_le_max (h a) (h b)
  | cst v => exact le_rfl

lemma trGate_deg (i : ℕ) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (d : List ℕ) : gdeg (fun k => d.getD k 0) (trGate i g) ≤ g.lineDegree d := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hl⟩ := hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · rcases hop with rfl | rfl <;> simp [trGate, gdeg]
  · rcases hop with rfl | rfl <;> simp only [trGate] <;> split_ifs with ha <;>
      simp [gdeg, Gate.lineDegree]
  · rcases hop with rfl | rfl <;> simp only [trGate] <;> split_ifs with h1 h2 h3 <;>
      simp [gdeg, Gate.lineDegree]
  · simp at hl

open LineDegTest in

lemma card03c_val (C : Circuit) (hC : Monotone2 C) (x : Fin (N + N) → Bool) (i : ℕ) :
    (ofCircuit N C).val x i = (C.wires (List.ofFn x)).getD i false := by
  obtain ⟨gs, o⟩ := C
  induction gs using List.reverseRecOn generalizing i with
  | nil =>
    change _ = (List.ofFn x).getD i false
    rw [ofFn_getD, Dag.val]
    split_ifs with h
    · rfl
    · simp [ofCircuit]
  | append_singleton gs g ih =>
    have ih := fun k => ih k (fun g' hg' => hC g' (List.mem_append_left _ hg'))
    have hgC := hC g (List.mem_append_right _ (List.mem_singleton_self g))
    have hsz : (ofCircuit N ⟨gs, o⟩).size = gs.length := by simp [ofCircuit, Dag.size]
    have hgates : (ofCircuit N ⟨gs ++ [g], o⟩).gates =
        (ofCircuit N ⟨gs, o⟩).gates ++ [trGate (N + N + (ofCircuit N ⟨gs, o⟩).size) g] := by
      rw [hsz]; simp [ofCircuit, List.mapIdx_concat]
    have hlen : (W gs (List.ofFn x)).length = N + N + (ofCircuit N ⟨gs, o⟩).size := by
      rw [W_length, hsz]; simp
    change _ = (W (gs ++ [g]) (List.ofFn x)).getD i false
    rw [W_snoc, getD_snoc, hlen]
    rcases lt_trichotomy i (N + N + (ofCircuit N ⟨gs, o⟩).size) with h | rfl | h
    · rw [ite_eq_left h, (api_prefix _ _ (hgates ▸ List.prefix_append _ _) i h x).1]
      exact ih i
    · rw [ite_eq_right (lt_irrefl _), ite_eq_left rfl, (top_snoc _ _ _ hgates x).1]
      have hr : (fun a => if _ : a < N + N + (ofCircuit N ⟨gs, o⟩).size then
          (ofCircuit N ⟨gs, o⟩).val x a else false) = fun a => (W gs (List.ofFn x)).getD a false := by
        funext a
        split_ifs with ha
        · exact ih a
        · exact (getD_ge_false (by omega)).symm
      rw [hr]
      exact trGate_val _ g hgC _ (fun k hk => getD_ge_false (by omega))
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      refine (val_deg_ge _ ?_ x).1
      unfold Dag.size; rw [hgates]; simp only [List.length_append, List.length_singleton]
      unfold Dag.size at h; omega

open LineDegTest in

lemma card03d_deg (C : Circuit) (hC : Monotone2 C) (i : ℕ) :
    (ofCircuit N C).deg i ≤ (C.lineDegrees (N + N) (lineMarks N)).getD i 0 := by
  obtain ⟨gs, o⟩ := C
  induction gs using List.reverseRecOn generalizing i with
  | nil =>
    change _ ≤ (Dg [] (N + N) (lineMarks N)).getD i 0
    rw [Dag.deg]
    by_cases h : i < N + N
    · rw [ite_eq_left h]
      simp [Dg, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, h, lineMarks]
    · rw [ite_eq_right h]
      simp [ofCircuit]
  | append_singleton gs g ih =>
    have ih := fun k => ih k (fun g' hg' => hC g' (List.mem_append_left _ hg'))
    have hgC := hC g (List.mem_append_right _ (List.mem_singleton_self g))
    have hsz : (ofCircuit N ⟨gs, o⟩).size = gs.length := by simp [ofCircuit, Dag.size]
    have hgates : (ofCircuit N ⟨gs ++ [g], o⟩).gates =
        (ofCircuit N ⟨gs, o⟩).gates ++ [trGate (N + N + (ofCircuit N ⟨gs, o⟩).size) g] := by
      rw [hsz]; simp [ofCircuit, List.mapIdx_concat]
    have hlen : (Dg gs (N + N) (lineMarks N)).length = N + N + (ofCircuit N ⟨gs, o⟩).size := by
      rw [Dg_length, hsz]
    change _ ≤ (Dg (gs ++ [g]) (N + N) (lineMarks N)).getD i 0
    rw [Dg_snoc, getD_snoc, hlen]
    rcases lt_trichotomy i (N + N + (ofCircuit N ⟨gs, o⟩).size) with h | rfl | h
    · rw [ite_eq_left h, (api_prefix _ _ (hgates ▸ List.prefix_append _ _) i h (fun _ => false)).2]
      exact ih i
    · rw [ite_eq_right (lt_irrefl _), ite_eq_left rfl, (top_snoc _ _ _ hgates (fun _ => false)).2]
      refine le_trans (gdeg_mono (r' := fun k => (Dg gs (N + N) (lineMarks N)).getD k 0) ?_ _)
        (trGate_deg _ g hgC _)
      intro a
      split_ifs with ha
      · exact ih a
      · exact Nat.zero_le _
    · rw [(val_deg_ge _ ?_ (fun _ => false)).2]
      · exact Nat.zero_le _
      unfold Dag.size; rw [hgates]; simp only [List.length_append, List.length_singleton]
      unfold Dag.size at h; omega

end Deg2.Bridge

namespace Deg2

variable {N : ℕ}

lemma circ_val_input (D : Dag N) (x : Fin (N + N) → Bool) {i : ℕ} (hi : i < N + N) :
    D.val x i = x ⟨i, hi⟩ := by
  rw [Dag.val, dif_pos hi]

lemma circ_deg_input (D : Dag N) {i : ℕ} (hi : i < N + N) :
    D.deg i = if N ≤ i then 1 else 0 := by
  rw [Dag.deg, ite_eq_left hi]

end Deg2

namespace Deg2.Forms

variable {N : ℕ}

lemma val_and {D : Dag N} {i a b : ℕ} (hg : D.gateAt i = some (.and a b)) (ha : a < i)
    (hb : b < i) (x : Fin (N + N) → Bool) : D.val x i = (D.val x a && D.val x b) := by
  obtain ⟨hi, hg⟩ := Api.gateAt_some hg
  rw [Dag.val, dif_neg (by omega), hg]
  simp only [dif_pos ha, dif_pos hb]

lemma val_or {D : Dag N} {i a b : ℕ} (hg : D.gateAt i = some (.or a b)) (ha : a < i)
    (hb : b < i) (x : Fin (N + N) → Bool) : D.val x i = (D.val x a || D.val x b) := by
  obtain ⟨hi, hg⟩ := Api.gateAt_some hg
  rw [Dag.val, dif_neg (by omega), hg]
  simp only [dif_pos ha, dif_pos hb]

lemma deg_and {D : Dag N} {i a b : ℕ} (hg : D.gateAt i = some (.and a b)) (ha : a < i)
    (hb : b < i) : D.deg i = D.deg a + D.deg b := by
  obtain ⟨hi, hg⟩ := Api.gateAt_some hg
  rw [Dag.deg, ite_eq_right (by omega), hg]
  simp only [dif_pos ha, dif_pos hb]

lemma deg_or {D : Dag N} {i a b : ℕ} (hg : D.gateAt i = some (.or a b)) (ha : a < i)
    (hb : b < i) : D.deg i = max (D.deg a) (D.deg b) := by
  obtain ⟨hi, hg⟩ := Api.gateAt_some hg
  rw [Dag.deg, ite_eq_right (by omega), hg]
  simp only [dif_pos ha, dif_pos hb]

end Deg2.Forms

end CircuitNormalization

section SourceNormalizedCompile

namespace PlaneArcTranspose

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_2583.LinearAnd.CircuitNormalization.Deg2

def codeGate (degree : ℕ → ℕ) : G → LinearOp
  | .cst _ => .zero
  | .and a b =>
    if degree a = 0 then
      if degree b = 0 then .zero else .scale b a
    else if degree b = 0 then .scale a b else .zero
  | .or a b =>
    if degree a = 0 then
      if degree b = 0 then .zero else .copy b
    else if degree b = 0 then .copy a else .add a b

def codeAt {N : ℕ} (D : Dag N) (w : ℕ) : LinearOp :=
  match D.gateAt w with
  | some gate => codeGate D.deg gate
  | none => .zero

def compilePrefix {N : ℕ} (D : Dag N) : ℕ → List Assignment
  | 0 => []
  | t+1 => compilePrefix D t ++ [⟨N+N+t, codeAt D (N+N+t)⟩]

def compile {N : ℕ} (D : Dag N) := compilePrefix D D.size

def zeroLines {N : ℕ} (x : Fin (N+N) → Bool) (p : Fin (N+N)) : Bool :=
  if p.val < N then x p else false

def activeLines {N : ℕ} (x : Fin (N+N) → Bool) (w : ℕ) : Prop :=
  ∃ h : w < N+N, N ≤ w ∧ x ⟨w,h⟩ = true

def scalarVal {N : ℕ} (D : Dag N) (x : Fin (N+N) → Bool) (w : ℕ) : Prop :=
  D.val (zeroLines x) w = true

private def Invariant (d : ℕ) (v z f : Prop) : Prop :=
  (d = 0 → (v ↔ z) ∧ ¬ f) ∧ (d ≤ 1 → (v ↔ z ∨ f))

private lemma join_and {a b : ℕ} (d : ℕ → ℕ) (v z f : ℕ → Prop)
    (ha : Invariant (d a) (v a) (z a) (f a))
    (hb : Invariant (d b) (v b) (z b) (f b)) :
    Invariant (d a+d b) (v a ∧ v b) (z a ∧ z b) ((codeGate d (.and a b)).eval z f) := by
  unfold Invariant at *
  by_cases h₁ : d a = 0 <;> by_cases h₂ : d b = 0 <;>
    simp [codeGate, h₁, h₂, LinearOp.eval] <;> grind

private lemma join_or {a b : ℕ} (d : ℕ → ℕ) (v z f : ℕ → Prop)
    (ha : Invariant (d a) (v a) (z a) (f a))
    (hb : Invariant (d b) (v b) (z b) (f b)) :
    Invariant (max (d a) (d b)) (v a ∨ v b) (z a ∨ z b) ((codeGate d (.or a b)).eval z f) := by
  unfold Invariant at *
  by_cases h₁ : d a = 0 <;> by_cases h₂ : d b = 0 <;>
    simp [codeGate, h₁, h₂, LinearOp.eval, max_le_iff] <;> grind

private lemma prefix_correct {N : ℕ} (D : Dag N) (wf : D.WF) (x : Fin (N+N) → Bool)
    (t w : ℕ) (hw : w < N+N+t) :
    Invariant (D.deg w) (D.val x w = true) (scalarVal D x w)
      (forward (scalarVal D x) (compilePrefix D t) (activeLines x) w) := by
  induction t generalizing w with
  | zero =>
    have hinput : w < N+N := by omega
    by_cases hp : w < N <;>
      simp [compilePrefix, forward, scalarVal, circ_val_input D _ hinput,
        circ_deg_input D hinput, zeroLines, activeLines, Invariant, hp,
        show (N ≤ w) = (¬ w < N) from propext (by omega), hinput]
  | succ t ih =>
    let u := N+N+t
    let st := forward (scalarVal D x) (compilePrefix D t) (activeLines x)
    have hstep (r) : forward (scalarVal D x) (compilePrefix D (t+1)) (activeLines x) r =
        (if r = u then (codeAt D u).eval (scalarVal D x) st else st r) := by
      simp [compilePrefix, forward, List.foldl_append, Assignment.push, st, u]
    rw [hstep]
    by_cases h : w = u
    · subst w
      rw [ite_eq_left rfl]
      cases hg : D.gateAt u with
      | none =>
        have hn : N+N ≤ u := by dsimp [u]; omega
        have hl : D.gates[u-(N+N)]? = none := by simpa [Dag.gateAt, hn] using hg
        simp [codeAt, hg, LinearOp.eval, Invariant, Dag.deg, Dag.val, scalarVal, hn.not_gt, hl]
      | some g =>
        cases g with
        | cst b =>
          obtain ⟨hn, hl⟩ := Api.gateAt_some hg
          simp [codeAt, hg, codeGate, LinearOp.eval, Invariant, Dag.deg, Dag.val, scalarVal,
            hn.not_gt, hl]
        | and a b =>
          have ha := wf u _ hg a (by simp [G.kids])
          have hb := wf u _ hg b (by simp [G.kids])
          have he := @join_and a b D.deg (fun r => D.val x r = true) (scalarVal D x) st
            (ih a ha) (ih b hb)
          simpa only [codeAt, hg, Forms.deg_and hg ha hb, Forms.val_and hg ha hb,
            scalarVal, Bool.and_eq_true_iff] using he
        | or a b =>
          have ha := wf u _ hg a (by simp [G.kids])
          have hb := wf u _ hg b (by simp [G.kids])
          have he := @join_or a b D.deg (fun r => D.val x r = true) (scalarVal D x) st
            (ih a ha) (ih b hb)
          simpa only [codeAt, hg, Forms.deg_or hg ha hb, Forms.val_or hg ha hb,
            scalarVal, Bool.or_eq_true] using he
    · rw [ite_eq_right h]
      exact ih w (by dsimp [u] at h; omega)

lemma compiled_value {N : ℕ} (D : Dag N) (wf : D.WF) (x : Fin (N+N) → Bool)
    (w : ℕ) (hw : w < N+N+D.size) (hdeg : D.deg w ≤ 1) :
    D.val x w = true ↔ scalarVal D x w ∨ forward (scalarVal D x) (compile D) (activeLines x) w :=
  (prefix_correct D wf x D.size w hw).2 hdeg

def pointOnly {N : ℕ} (x : Fin N → Bool) : Fin (N+N) → Bool := Fin.addCases x (fun _ => false)

def oneLine {N : ℕ} (x : Fin N → Bool) (i : Fin N) : Fin (N+N) → Bool :=
  Fin.addCases x (fun j => decide (j = i))

lemma zero_oneLine {N : ℕ} (x : Fin N → Bool) (i : Fin N) :
    zeroLines (oneLine x i) = pointOnly x := by
  funext k
  refine Fin.addCases (fun p => ?_) (fun w => ?_) k
  · simp [zeroLines, oneLine, pointOnly]
  · simp only [zeroLines, pointOnly, Fin.val_natAdd, Fin.addCases_right]
    rw [ite_eq_right (by omega)]

lemma active_oneLine {N : ℕ} (x : Fin N → Bool) (i : Fin N) :
    activeLines (oneLine x i) = (fun w => w = N+i.val) := by
  funext w; apply propext; constructor
  · rintro ⟨hw, hn, hv⟩
    let j : Fin N := ⟨w-N,by omega⟩
    have eq : (⟨w,hw⟩ : Fin (N+N)) = Fin.natAdd N j := Fin.ext (by dsimp [j]; omega)
    rw [eq] at hv
    have he : j = i := by simpa only [oneLine, Fin.addCases_right, decide_eq_true_eq] using hv
    have hi := congrArg Fin.val he
    dsimp [j] at hi
    omega
  · rintro rfl
    refine ⟨by omega,by omega,?_⟩
    change oneLine x i (Fin.natAdd N i) = true
    simp only [oneLine, Fin.addCases_right, decide_eq_true_eq]

def pointScalar {N : ℕ} (D : Dag N) (x : Fin N → Bool) (w : ℕ) : Prop :=
  D.val (pointOnly x) w = true

lemma circuit_coefficient {N : ℕ} (C : Circuit) (x : Fin N → Bool) (i : Fin N)
    (mono : PEqualNP.MetaComplexity.Monotone2 C)
    (hdeg : HasLineDegree (N+N) (Finset.Ico N (N+N)) C 1)
    (hw : C.output < N+N+C.size) (hoff : C.eval (List.ofFn (pointOnly x)) = false) :
    let D := ofCircuit N C
    C.eval (List.ofFn (oneLine x i)) = true ↔
      forward (pointScalar D x) (compile D) (fun w => w = N+i.val) C.output := by
  let D := ofCircuit N C
  have hd : D.deg C.output ≤ 1 := (Bridge.card03d_deg C mono C.output).trans hdeg
  have hv := compiled_value D (Api.card03b_wf C) (oneLine x i) C.output
    (by simpa [D, Api.card03a_size] using hw) hd
  have hz : scalarVal D (oneLine x i) = pointScalar D x := by
    funext w; simp only [scalarVal, pointScalar, zero_oneLine]
  rw [hz, active_oneLine] at hv
  have hdead : ¬ pointScalar D x C.output := by
    change ¬ (ofCircuit N C).val (pointOnly x) C.output = true
    rw [Bridge.card03c_val C mono]
    change ¬ C.eval (List.ofFn (pointOnly x)) = true
    simp [hoff]
  rw [or_iff_right hdead] at hv
  have hactual := Bridge.card03c_val C mono (oneLine x i) C.output
  change D.val (oneLine x i) C.output = C.eval (List.ofFn (oneLine x i)) at hactual
  rw [hactual] at hv
  exact hv

end PlaneArcTranspose

end SourceNormalizedCompile

section SourceFirstMultiplier

namespace PlaneArcFirst

open PlaneArcTranspose

def disabled : ℕ → Prop := fun _ => False

lemma eval_mono (op : LinearOp) {f g a b : ℕ → Prop}
    (hf : ∀ i, f i → g i) (ha : ∀ i, a i → b i) :
    op.eval f a → op.eval g b := by
  cases op with
  | add u v => exact Or.imp (ha u) (ha v)
  | scale u s => exact And.imp (ha u) (hf s)
  | copy u => exact ha u
  | zero => exact id

lemma push_mono (a : Assignment) {f g x y : ℕ → Prop}
    (hf : ∀ i, f i → g i) (hx : ∀ i, x i → y i) :
    ∀ w, a.push f x w → a.push g y w := by
  intro w
  by_cases eq : w = a.dst
  · simpa [Assignment.push, eq] using (eval_mono a.op hf hx)
  · simpa [Assignment.push, eq] using hx w

lemma forward_mono (ops : List Assignment) {f g x y : ℕ → Prop}
    (hf : ∀ i, f i → g i) (hx : ∀ i, x i → y i) :
    ∀ w, forward f ops x w → forward g ops y w := by
  induction ops generalizing x y with
  | nil => exact hx
  | cons a l ih => exact ih (push_mono a hf hx)

structure Cut (ops : List Assignment) where
  pre : List Assignment
  a : Assignment
  post : List Assignment
  ordered : ops = pre ++ a :: post

def Cut.idx {ops} (k : Cut ops) : Fin ops.length :=
  ⟨k.pre.length, lt_of_lt_of_eq (b := (k.pre ++ k.a :: k.post).length)
    (by simp) (congrArg List.length k.ordered.symm)⟩

lemma Cut.idx_injective (ops) : Function.Injective (Cut.idx (ops := ops)) := by
  rintro ⟨p,a,q,h⟩ ⟨p',a',q',h'⟩ he
  have hl : p.length = p'.length := congrArg Fin.val he
  have eq : p ++ a :: q = p' ++ a' :: q' := h.symm.trans h'
  have hp := congrArg (List.take p.length) eq
  have lhs : (p ++ a :: q).take p.length = p := by simp
  have rhs : (p' ++ a' :: q').take p.length = p' := by rw [hl]; simp
  rw [lhs,rhs] at hp
  subst p'
  have rest := List.append_cancel_left eq
  obtain ⟨rfl,rfl⟩ := List.cons.inj rest
  rfl

def Cut.raw {ops} (k : Cut ops) (src : ℕ) : Prop :=
  ∃ u s, k.a.op = .scale u s ∧ forward disabled k.pre (fun w => w = src) u

def Cut.active {ops} (k : Cut ops) (scalar : ℕ → Prop) (out : ℕ) : Prop :=
  ∃ u s, k.a.op = .scale u s ∧ scalar s ∧
    reverse scalar k.post (fun w => w = out) k.a.dst

lemma trace_first (ops : List Assignment) (scalar state demand : ℕ → Prop)
    (yes : ∃ w, demand w ∧ forward scalar ops state w)
    (no : ¬ ∃ w, demand w ∧ forward disabled ops state w) :
    ∃ (k : Cut ops) (u s : ℕ), k.a.op = .scale u s ∧ forward disabled k.pre state u ∧
      scalar s ∧ reverse scalar k.post demand k.a.dst := by
  classical
  induction ops generalizing state with
  | nil => exact False.elim (no yes)
  | cons a rest ih =>
    by_cases mixed : ∃ w, demand w ∧ forward scalar rest (a.push disabled state) w
    · obtain ⟨k,u,s,ho,hpre,hscalar,hsuf⟩ := ih _ mixed no
      exact ⟨⟨a :: k.pre,k.a,k.post,by simpa using congrArg (List.cons a) k.ordered⟩,
        u,s,ho,hpre,hscalar,hsuf⟩
    · have y := (transpose rest scalar (a.push scalar state) demand).mp yes
      have n : ¬ ∃ w, reverse scalar rest demand w ∧ a.push disabled state w :=
        fun h => mixed ((transpose rest scalar (a.push disabled state) demand).mpr h)
      obtain ⟨w, hsuf, hval⟩ := y
      have eq : w = a.dst := by
        by_contra ne
        exact n ⟨w, hsuf, by simpa [Assignment.push, ne] using hval⟩
      subst w
      have eg : a.op.eval scalar state := by simpa [Assignment.push] using hval
      have en : ¬ a.op.eval disabled state := fun h =>
        n ⟨a.dst, hsuf, by simpa [Assignment.push] using h⟩
      cases ho : a.op with
      | add u v => exact False.elim (en (by simpa [ho,LinearOp.eval] using eg))
      | copy u => exact False.elim (en (by simpa [ho,LinearOp.eval] using eg))
      | zero => exact False.elim (by simpa [ho,LinearOp.eval] using eg)
      | scale u s =>
        obtain ⟨hv,hscalar⟩ : state u ∧ scalar s := by simpa [ho,LinearOp.eval] using eg
        exact ⟨⟨[],a,rest,rfl⟩,u,s,ho,hv,hscalar,hsuf⟩

lemma combine {ops} (k : Cut ops) (src out : ℕ) (scalar : ℕ → Prop)
    (hr : k.raw src) (hp : k.active scalar out) :
    forward scalar ops (fun i => i = src) out := by
  obtain ⟨u,s,ho,hraw⟩ := hr
  obtain ⟨u',s',ho',hs,hpath⟩ := hp
  obtain ⟨rfl,rfl⟩ := LinearOp.scale.inj (ho.symm.trans ho')
  have pref : forward scalar k.pre (fun i => i = src) u :=
    forward_mono k.pre (fun _ h => False.elim h) (fun _ h => h) u hraw
  let st := forward scalar k.pre (fun i => i = src)
  have pushed : k.a.push scalar st k.a.dst :=
    by simpa [Assignment.push,ho,LinearOp.eval,st] using And.intro pref hs
  have tail := (transpose k.post scalar (k.a.push scalar st) (fun w => w = out)).mpr
    ⟨k.a.dst,hpath,pushed⟩
  obtain ⟨_,rfl,good⟩ := tail
  rw [k.ordered]
  simpa [forward, List.foldl_append, st] using good

lemma scale_cover {ι : Type*} (ops : List Assignment) (src : ι → ℕ) (out : ℕ)
    (scalar : ι → ℕ → Prop) (M : ι → ι → Prop)
    (sound : ∀ i p, forward (scalar p) ops (fun w => w = src i) out → M i p)
    (diag : ∀ i, forward (scalar i) ops (fun w => w = src i) out)
    (missing : ∀ i, ∃ p, ¬ M i p) :
    (∀ (k : Cut ops) i p, k.raw (src i) → k.active (scalar p) out → M i p) ∧
    (∀ i, ∃ k : Cut ops, k.raw (src i) ∧ k.active (scalar i) out) := by
  constructor
  · intro k i p hr ha
    exact sound i p (combine k _ _ _ hr ha)
  · intro i
    obtain ⟨p,neg⟩ := missing i
    have no : ¬ forward disabled ops (fun w => w = src i) out :=
      fun y => neg (sound i p (forward_mono ops (fun _ h => False.elim h) (fun _ h => h) out y))
    have ey : ∃ w, (w = out) ∧ forward (scalar i) ops (fun w => w = src i) w :=
      ⟨out, rfl, diag i⟩
    have en : ¬ ∃ w, (w = out) ∧ forward disabled ops (fun w => w = src i) w := by
      rintro ⟨_,rfl,h⟩
      exact no h
    obtain ⟨k,u,s,ho,hw,hp,hr⟩ := trace_first ops (scalar i) _ _ ey en
    exact ⟨k,⟨u,s,ho,hw⟩,⟨u,s,ho,hp,hr⟩⟩

def isScale (a : Assignment) : Bool :=
  match a.op with
  | .scale _ _ => true
  | _ => false

lemma Cut.get_idx {ops} (k : Cut ops) : ops[k.idx] = k.a := by
  obtain ⟨pre,a,post,rfl⟩ := k
  simp [Cut.idx]

lemma count_scales {ι : Type*} [Fintype ι] (ops : List Assignment)
    (src : ι → ℕ) (out : ℕ) (scalar : ι → ℕ → Prop) (M : ι → ι → Prop)
    (sound : ∀ i p, forward (scalar p) ops (fun w => w = src i) out → M i p)
    (diag : ∀ i, forward (scalar i) ops (fun w => w = src i) out)
    (missing : ∀ i, ∃ p, ¬ M i p) (cross : ∀ i j, M i j → M j i → i = j) :
    Fintype.card ι ≤ (Finset.univ.filter (fun j : Fin ops.length => isScale ops[j])).card := by
  classical
  obtain ⟨hr,hd⟩ := scale_cover ops src out scalar M sound diag missing
  choose pick hraw hact using hd
  let B := Finset.univ.filter (fun j : Fin ops.length => isScale ops[j])
  have mem (i : ι) : (pick i).idx ∈ B := by
    obtain ⟨u,s,ho,_⟩ := hraw i
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    change isScale ops[(pick i).idx] = true
    rw [Cut.get_idx]
    simp [isScale,ho]
  let f : ι → B := fun i => ⟨(pick i).idx,mem i⟩
  have hinj : Function.Injective f := by
    intro i j hij
    have eq := Cut.idx_injective ops (show (pick i).idx = (pick j).idx from
      congrArg Subtype.val hij)
    exact cross i j (hr (pick i) _ _ (hraw i) (eq ▸ hact j))
      (hr (pick j) j i (hraw j) (by rw [←eq]; exact hact i))
  calc
    Fintype.card ι ≤ Fintype.card B := Fintype.card_le_of_injective f hinj
    _ = B.card := Fintype.card_coe B

end PlaneArcFirst

end SourceFirstMultiplier

section OriginalAndBudget

open PEqualNP.CircuitLowerBounds
open PlaneArcTranspose PlaneArcFirst CircuitNormalization.Deg2

def andCount (gs : List Gate) : ℕ :=
  gs.countP fun g => match g.op with
    | GateOp.and => true
    | _ => false

lemma countP_eq_sum_get {α : Type*} (p : α → Bool) (xs : List α) :
    xs.countP p = ∑ i : Fin xs.length, if p xs[i] = true then 1 else 0 := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    rw [List.countP_cons]
    simp only [List.length_cons, Fin.sum_univ_succ]
    change xs.countP p + (if p a = true then 1 else 0) =
      (if p a = true then 1 else 0) + ∑ i : Fin xs.length, if p xs[i] = true then 1 else 0
    rw [← ih]
    by_cases hp : p a = true <;> simp [hp, Nat.add_comm]

lemma scales_eq_countP (ops : List Assignment) :
    (Finset.univ.filter (fun j : Fin ops.length => isScale ops[j])).card = ops.countP isScale := by
  classical
  rw [countP_eq_sum_get, Finset.card_eq_sum_ones, Finset.sum_filter]

lemma codeGate_scale_and (d : ℕ → ℕ) (g : G) (dst : ℕ)
    (h : isScale ⟨dst, codeGate d g⟩ = true) : ∃ a b, g = .and a b := by
  cases g with
  | and a b => exact ⟨a, b, rfl⟩
  | or a b =>
    by_cases ha : d a = 0 <;> by_cases hb : d b = 0 <;> simp [codeGate, isScale, ha, hb] at h
  | cst v => simp [codeGate, isScale] at h

lemma trGate_and_op (i : ℕ) (g : Gate) (a b : ℕ) (h : trGate i g = .and a b) :
    g.op = GateOp.and := by
  unfold trGate at h
  split at h <;> (try split_ifs at h) <;> cases h <;> assumption

lemma codeAt_ofCircuit (N : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    codeAt (ofCircuit N C) (N + N + j) =
      codeGate (ofCircuit N C).deg (trGate (N + N + j) C.gates[j]) := by
  simp [codeAt, Dag.gateAt, ofCircuit, List.getElem?_mapIdx, hj]

lemma compilePrefix_scales_le (N : ℕ) (C : Circuit) (k : ℕ) (hk : k ≤ C.gates.length) :
    (compilePrefix (ofCircuit N C) k).countP isScale ≤ andCount (C.gates.take k) := by
  induction k with
  | zero => simp [compilePrefix, andCount]
  | succ k ih =>
    have ih' := ih (by omega)
    rw [compilePrefix, List.countP_append, List.take_succ_eq_append_getElem (by omega)]
    have ha : andCount (C.gates.take k ++ [C.gates[k]]) =
        andCount (C.gates.take k) + andCount [C.gates[k]] := by
      unfold andCount
      rw [List.countP_append]
    rw [ha]
    by_cases hs : isScale ⟨N + N + k, codeAt (ofCircuit N C) (N + N + k)⟩ = true
    · have hc := hs
      rw [codeAt_ofCircuit N C k (by omega)] at hc
      obtain ⟨a, b, hg⟩ := codeGate_scale_and _ _ _ hc
      have hop := trGate_and_op _ _ a b hg
      have hc₁ : ([⟨N + N + k, codeAt (ofCircuit N C) (N + N + k)⟩] : List Assignment).countP isScale = 1 := by simp [hs]
      have hc₂ : andCount [C.gates[k]] = 1 := by simp [andCount, hop]
      rw [hc₁, hc₂]
      omega
    · have hc₁ : ([⟨N + N + k, codeAt (ofCircuit N C) (N + N + k)⟩] : List Assignment).countP isScale = 0 := by simp [hs]
      rw [hc₁]
      omega

lemma compiled_scales_le_andCount (N : ℕ) (C : Circuit) :
    (Finset.univ.filter (fun j : Fin (compile (ofCircuit N C)).length =>
      isScale (compile (ofCircuit N C))[j])).card ≤ andCount C.gates := by
  rw [scales_eq_countP]
  simpa [compile, Api.card03a_size, Circuit.size] using
    compilePrefix_scales_le N C C.gates.length le_rfl

end OriginalAndBudget

end LinearAnd


namespace PlaneMatching

lemma deg_le (q N : ℕ) (S : Fin N → Finset (Fin N)) (hq : 0 < q) (hN : N = q ^ 2 + q + 1)
    (hS : ∀ l, (S l).card = q + 1)
    (hU : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, p ∈ S l ∧ p' ∈ S l) (p : Fin N) :
    (Finset.univ.filter (fun l : Fin N => p ∈ S l)).card ≤ q + 1 := by
  classical
  set L := Finset.univ.filter (fun l : Fin N => p ∈ S l) with hL
  have hsub : L.biUnion (fun l => (S l).erase p) ⊆ Finset.univ.erase p := by
    intro x hx
    simp only [Finset.mem_biUnion, Finset.mem_erase] at hx
    obtain ⟨_, _, hx, _⟩ := hx
    exact Finset.mem_erase.mpr ⟨hx, Finset.mem_univ _⟩
  have hdisj : (L : Set (Fin N)).PairwiseDisjoint (fun l => (S l).erase p) := by
    intro i hi j hj hij
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, hL] at hi hj
    rw [Function.onFun, Finset.disjoint_left]
    intro x hxi hxj
    rw [Finset.mem_erase] at hxi hxj
    obtain ⟨l, _, hl⟩ := hU p x (Ne.symm hxi.1)
    exact hij ((hl i ⟨hi, hxi.2⟩).trans (hl j ⟨hj, hxj.2⟩).symm)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdisj] at hcard
  have hterm : ∀ l ∈ L, ((S l).erase p).card = q := by
    intro l hl
    simp only [hL, Finset.mem_filter, Finset.mem_univ, true_and] at hl
    rw [Finset.card_erase_of_mem hl, hS l]
    simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem
    (Finset.mem_univ p), Finset.card_univ, Fintype.card_fin] at hcard
  have h1 : N - 1 = (q + 1) * q := by
    rw [hN, Nat.add_sub_cancel]; ring
  rw [h1] at hcard
  exact Nat.le_of_mul_le_mul_right hcard hq

lemma hall_lines (q N : ℕ) (S : Fin N → Finset (Fin N)) (hq : 0 < q) (hN : N = q ^ 2 + q + 1)
    (hS : ∀ l, (S l).card = q + 1)
    (hU : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, p ∈ S l ∧ p' ∈ S l) :
    ∃ σ : Fin N → Fin N, Function.Injective σ ∧ ∀ l, σ l ∈ S l := by
  classical
  apply (Finset.all_card_le_biUnion_card_iff_exists_injective S).mp
  intro B
  set U := B.biUnion S with hUdef
  have h1 : ∑ l ∈ B, (U ∩ S l).card = B.card * (q + 1) := by
    rw [Finset.sum_congr rfl (fun l hl => by
      rw [Finset.inter_eq_right.mpr (Finset.subset_biUnion_of_mem S hl), hS]),
      Finset.sum_const, smul_eq_mul]
  have h2 : ∑ l ∈ B, (U ∩ S l).card = ∑ p ∈ U, (B.filter (fun l => p ∈ S l)).card := by
    simp_rw [← Finset.filter_mem_eq_inter, Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  have h3 : ∑ p ∈ U, (B.filter (fun l => p ∈ S l)).card ≤ U.card * (q + 1) := by
    have := Finset.sum_le_card_nsmul U (fun p => (B.filter (fun l => p ∈ S l)).card) (q + 1)
      (fun p _ => le_trans (Finset.card_le_card
        (Finset.filter_subset_filter _ (Finset.subset_univ B))) (deg_le q N S hq hN hS hU p))
    simpa [smul_eq_mul] using this
  have h4 : B.card * (q + 1) ≤ U.card * (q + 1) := by omega
  exact Nat.le_of_mul_le_mul_right h4 (Nat.succ_pos q)

lemma lines_card (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (hq : 2 ≤ q)
    (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) (c : Fin N) :
    (Finset.univ.filter (fun l => I c l)).card = q + 1 := by
  have e : (Finset.univ.filter (fun l => I c l)).biUnion
      (fun l => (Finset.univ.filter (fun p => I p l)).erase c) = Finset.univ.erase c := by
    ext p
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase, and_true]
    constructor
    · rintro ⟨l, _, hp, _⟩
      exact hp
    · intro hp
      obtain ⟨l, ⟨h1, h2⟩, _⟩ := hu p c hp
      exact ⟨l, h2, hp, h1⟩
  have hd : ∀ l ∈ Finset.univ.filter (fun l => I c l), ∀ l' ∈ Finset.univ.filter (fun l => I c l),
      l ≠ l' → Disjoint ((Finset.univ.filter (fun p => I p l)).erase c)
        ((Finset.univ.filter (fun p => I p l')).erase c) := by
    intro l hl1 l' hl1' hne
    rw [Finset.disjoint_left]
    intro p hp hp'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at hl1 hl1' hp hp'
    obtain ⟨l0, _, hun⟩ := hu p c hp.1
    exact hne ((hun l ⟨hp.2, hl1⟩).trans (hun l' ⟨hp'.2, hl1'⟩).symm)
  have hc := Finset.card_biUnion hd
  rw [e] at hc
  have hs : ∀ l ∈ Finset.univ.filter (fun l => I c l),
      ((Finset.univ.filter (fun p => I p l)).erase c).card = q := by
    intro l hl1
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl1
    rw [Finset.card_erase_of_mem (by simp [hl1]), hl l]
    rfl
  rw [Finset.sum_congr rfl hs, Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ c),
    Finset.card_univ, Fintype.card_fin] at hc
  have h3 : (Finset.univ.filter (fun l => I c l)).card * q = (q + 1) * q := by
    rw [← hc, hN]
    have : q ^ 2 + q + 1 - 1 = (q + 1) * q := by
      rw [Nat.add_sub_cancel]
      ring
    exact this
  exact Nat.eq_of_mul_eq_mul_right (by omega) h3

lemma exists_incidence_equiv (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hcol : ∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1)
    (hjoin : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) :
    ∃ f : Fin N ≃ Fin N, ∀ l, I (f l) l := by
  classical
  let S : Fin N → Finset (Fin N) := fun l => Finset.univ.filter (fun p => I p l)
  have hS : ∀ l, (S l).card = q + 1 := by
    intro l
    simpa [S, Fintype.card_subtype] using hcol l
  have hU : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, p ∈ S l ∧ p' ∈ S l := by
    simpa [S] using hjoin
  obtain ⟨σ, hσ, hmem⟩ := hall_lines q N S (by omega) hN hS hU
  let f : Fin N ≃ Fin N := Equiv.ofBijective σ (Finite.injective_iff_bijective.mp hσ)
  refine ⟨f, fun l => ?_⟩
  simpa [f, S] using hmem l

end PlaneMatching


namespace LinearAndIncidence

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_2583.LinearAnd.PlaneArcTranspose
open PEqualNP.Outside.L_meta_2583.LinearAnd.PlaneArcFirst
open PEqualNP.Outside.L_meta_2583.LinearAnd.CircuitNormalization.Deg2

lemma pointOnly_false {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit)
    (hc : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    (x : Fin N → Bool) : C.eval (List.ofFn (pointOnly x)) = false := by
  have he := hc (pointOnly x)
  simp only [circuitFun, pointOnly, Fin.addCases_left, Fin.addCases_right] at he
  simpa using he

lemma oneLine_incidence {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit)
    (hc : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    (p l : Fin N) :
    C.eval (List.ofFn (oneLine (fun v => decide (v = p)) l)) = decide (I p l) := by
  have he := hc (oneLine (fun v => decide (v = p)) l)
  simp only [circuitFun, oneLine, Fin.addCases_left, Fin.addCases_right] at he
  simpa using he

lemma forward_incidence {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hm : Monotone2 C)
    (hl : HasLineDegree (N + N) (Finset.Ico N (N + N)) C 1)
    (hw : C.output < N + N + C.size)
    (hc : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    (p l : Fin N) :
    forward (pointScalar (ofCircuit N C) (fun v => decide (v = p)))
      (compile (ofCircuit N C)) (fun w => w = N + l.val) C.output ↔ I p l := by
  have hco := circuit_coefficient C (fun v => decide (v = p)) l hm hl hw
    (pointOnly_false I C hc _)
  have he := oneLine_incidence I C hc p l
  simpa only [he, decide_eq_true_eq] using hco.symm

lemma valid_output {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hne : ∃ p l, I p l)
    (hc : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) :
    C.output < N + N + C.size := by
  obtain ⟨p, l, hp⟩ := hne
  have ht := oneLine_incidence I C hc p l
  rw [decide_eq_true hp] at ht
  by_contra hn
  have hf := Repair.val_ge (n := N + N) (C := C)
    (x := List.ofFn (oneLine (fun v => decide (v = p)) l)) (by simp)
    (u := C.output) (by simpa [Circuit.size] using Nat.le_of_not_gt hn)
  change C.eval _ = false at hf
  rw [ht] at hf
  contradiction

lemma scales_of_matching {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hm : Monotone2 C)
    (hl : HasLineDegree (N + N) (Finset.Ico N (N + N)) C 1)
    (hw : C.output < N + N + C.size)
    (hc : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    (f : Fin N ≃ Fin N) (hf : ∀ l, I (f l) l)
    (hmissing : ∀ l, ∃ p, ¬ I p l)
    (hunique : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) :
    N ≤ (Finset.univ.filter (fun j : Fin (compile (ofCircuit N C)).length =>
      isScale (compile (ofCircuit N C))[j])).card := by
  classical
  have hs := count_scales (compile (ofCircuit N C)) (fun l : Fin N => N + l.val) C.output
    (fun k : Fin N => pointScalar (ofCircuit N C) (fun p => decide (p = f k)))
    (fun l k => I (f k) l)
    (by intro l k h; exact (forward_incidence I C hm hl hw hc (f k) l).mp h)
    (by intro l; exact (forward_incidence I C hm hl hw hc (f l) l).mpr (hf l))
    (by
      intro l
      obtain ⟨p, hp⟩ := hmissing l
      exact ⟨f.symm p, by simpa using hp⟩)
    (by
      intro i j hij hji
      by_contra hne
      have hpne : f i ≠ f j := fun h => hne (f.injective h)
      obtain ⟨l, _, huniq⟩ := hunique (f i) (f j) hpne
      exact hne ((huniq i ⟨hf i, hij⟩).trans (huniq j ⟨hji, hf j⟩).symm))
  simpa using hs

lemma missing_of_plane {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hsize : ∀ l : Fin N, (Finset.univ.filter fun p => I p l).card = q + 1) :
    ∀ l, ∃ p, ¬ I p l := by
  classical
  intro l
  by_contra hn
  have hall : ∀ p, I p l := by simpa using hn
  have hs := hsize l
  simp [hall] at hs
  nlinarith

lemma and_budget_of_matching {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 (N + N) C)
    (hl : HasLineDegree (N + N) (Finset.Ico N (N + N)) C 1)
    (hc : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    (f : Fin N ≃ Fin N) (hf : ∀ l, I (f l) l)
    (hmissing : ∀ l, ∃ p, ¬ I p l)
    (hunique : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) :
    N ≤ LinearAnd.andCount C.gates := by
  by_cases hz : N = 0
  · subst N; exact Nat.zero_le _
  have hm : Monotone2 C := by
    intro g hg
    exact ⟨by simpa using hC.1 g hg, Nat.le_of_eq (hC.2.2 g hg)⟩
  let i : Fin N := ⟨0, by omega⟩
  have hw := valid_output I C ⟨f i, i, hf i⟩ hc
  have hs := scales_of_matching I C hm hl hw hc f hf hmissing hunique
  exact hs.trans (LinearAnd.compiled_scales_le_andCount N C)

lemma count_partition (gs : List Gate)
    (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    LinearAnd.andCount gs + LinearExtraction.orCount gs = gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have hi := ih (by intro g hg; exact hm g (List.mem_cons_of_mem _ hg))
    rcases hm g (List.mem_cons_self) with ha | ho
    · simp [LinearAnd.andCount, LinearExtraction.orCount, ha] at hi ⊢ <;> omega
    · simp [LinearAnd.andCount, LinearExtraction.orCount, ho] at hi ⊢ <;> omega

lemma size_budget_of_matching {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit)
    (hsize : ∀ l : Fin N, (Finset.univ.filter fun p => I p l).card = q + 1)
    (hunique : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (hC : PEqualNP.TopForm.IsAO2 (N + N) C)
    (hl : HasLineDegree (N + N) (Finset.Ico N (N + N)) C 1)
    (hc : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    (f : Fin N ≃ Fin N) (hf : ∀ l, I (f l) l)
    (hmissing : ∀ l, ∃ p, ¬ I p l) :
    N * (q + 2) ≤ C.size + 1 := by
  have ha := and_budget_of_matching I C hC hl hc f hf hmissing hunique
  have ho := LinearIncidenceBudget.posted_incidence_or_budget I C hsize hunique hC hl hc
  rw [← LinearIncidenceBudget.orCount_eq_orGates] at ho
  have hp := count_partition C.gates hC.1
  change N * (q + 2) ≤ C.gates.length + 1
  simp only [Nat.mul_add, Nat.mul_one] at ho ⊢
  omega

lemma posted_plane_size_bound (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hsize : ∀ l : Fin N, (Finset.univ.filter fun p => I p l).card = q + 1)
    (hunique : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (hC : PEqualNP.TopForm.IsAO2 (N + N) C)
    (hl : HasLineDegree (N + N) (Finset.Ico N (N + N)) C 1)
    (hc : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) :
    N * (q + 2) ≤ C.size + 1 := by
  classical
  obtain ⟨f, hf⟩ := PlaneMatching.exists_incidence_equiv q N I hq hN
    (by intro l; simpa [Fintype.card_subtype] using hsize l) hunique
  exact size_budget_of_matching I C hsize hunique hC hl hc f hf
    (missing_of_plane I hq hN hsize)

end LinearAndIncidence


namespace PathDegreeObstruction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

abbrev pathGraph : SimpleGraph (Fin 4) := edgeGraph 4 [(0, 2), (1, 2), (1, 3)]

def repeatedLineCircuit : Circuit :=
  ⟨[⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [0, 2]⟩,
    ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.and, [4, 6]⟩], 7⟩

def linearCircuit : Circuit :=
  ⟨[⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [1, 4]⟩,
    ⟨GateOp.and, [0, 2]⟩, ⟨GateOp.or, [5, 6]⟩], 7⟩

lemma path_no_four_cycle : NoFourCycle pathGraph := by decide +kernel

lemma repeated_ao2 : IsAO2 4 repeatedLineCircuit := by decide +kernel

lemma repeated_size : repeatedLineCircuit.size = 4 := by decide +kernel

lemma repeated_correct : ∀ z : Fin 4 → Bool,
    circuitFun 4 repeatedLineCircuit z = graphFun pathGraph ∅ z := by decide +kernel

lemma repeated_incidence : ∀ z : Fin (2 + 2) → Bool,
    circuitFun 4 repeatedLineCircuit z = decide (∃ p l : Fin 2,
      (p = 1 ∨ l = 0) ∧ z (Fin.castAdd 2 p) = true ∧ z (Fin.natAdd 2 l) = true) := by
  decide +kernel

lemma repeated_line_degree :
    (repeatedLineCircuit.lineDegrees 4 (Finset.Ico 2 4)).getD repeatedLineCircuit.output 0 = 2 := by
  decide +kernel

lemma repeated_not_linear : ¬ HasLineDegree 4 (Finset.Ico 2 4) repeatedLineCircuit 1 := by
  decide +kernel

lemma inner_and_below : BelowF pathGraph repeatedLineCircuit 1 := by decide +kernel

lemma inner_and_in_cone : InCone 4 repeatedLineCircuit 1 3 := by decide +kernel

lemma repeated_not_top_form : ¬ TopForm pathGraph repeatedLineCircuit := by decide +kernel

lemma linear_normalization : IsAO2 4 linearCircuit ∧ linearCircuit.size = 4 ∧
    HasLineDegree 4 (Finset.Ico 2 4) linearCircuit 1 ∧
    ∀ z : Fin 4 → Bool, circuitFun 4 linearCircuit z = circuitFun 4 repeatedLineCircuit z := by
  decide +kernel

def topFormCircuit : Circuit :=
  ⟨[⟨GateOp.or, [2, 1]⟩, ⟨GateOp.or, [0, 1]⟩,
    ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [2, 3]⟩,
    ⟨GateOp.and, [6, 7]⟩], 8⟩

lemma top_form_counterexample : IsAO2 4 topFormCircuit ∧ topFormCircuit.size = 5 ∧
    TopForm pathGraph topFormCircuit ∧ ¬ HasLineDegree 4 (Finset.Ico 2 4) topFormCircuit 1 ∧
    ∀ z : Fin 4 → Bool, circuitFun 4 topFormCircuit z = graphFun pathGraph ∅ z := by
  decide +kernel

lemma top_form_line_degree :
    (topFormCircuit.lineDegrees 4 (Finset.Ico 2 4)).getD topFormCircuit.output 0 = 2 := by
  decide +kernel

lemma top_form_inner_and_dirty : ¬ BelowF pathGraph topFormCircuit 2 := by decide +kernel

end PathDegreeObstruction


namespace PartialPointBudget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_2583.Repair
open PEqualNP.Outside.L_meta_2583.PurePointBudget

lemma accepted_subset_target {n : ℕ} {C : Circuit} (hm : Monotone2 C)
    (U S : Finset (Fin n)) (roots : Finset ℕ)
    (haccept : ∀ p ∈ S, ∃ w ∈ roots, val C (List.ofFn (pairInput p p)) w = true)
    (hfalse : ∀ w ∈ roots, val C (List.ofFn (complementInput U)) w = false) : S ⊆ U := by
  intro p hp
  obtain ⟨w, hw, hval⟩ := haccept p hp
  exact support_subset_of_false hm (hfalse w hw) (mem_support.2 hval)

lemma grouped_partial_or_budget {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {C : Circuit} (hm : Monotone2 C) (rb : ReadsBack n C)
    (U S : ι → Finset (Fin n)) (roots : ι → Finset ℕ)
    (hvalid : ∀ i, ∀ w ∈ roots i, w < n + C.gates.length)
    (haccept : ∀ i, ∀ p ∈ S i, ∃ w ∈ roots i,
      val C (List.ofFn (pairInput p p)) w = true)
    (hfalse : ∀ i, ∀ w ∈ roots i, val C (List.ofFn (complementInput (U i))) w = false)
    (hpair : ∀ i j, i ≠ j → (U i ∩ U j).card ≤ 1) :
    (∑ i, ((S i).card - (roots i).card)) ≤ (orGates C).card := by
  classical
  let pools := fun i => orPool C (complementInput (U i)) C.gates.length
  have hlocal : ∀ i, (S i).card - (roots i).card ≤ (pools i).card := by
    intro i
    have hsub : S i ⊆ (roots i).biUnion (singletonSupport n C) := by
      intro p hp
      obtain ⟨w, hw, hv⟩ := haccept i p hp
      exact Finset.mem_biUnion.2 ⟨w, hw, mem_support.2 hv⟩
    have hcard := Finset.card_le_card hsub
    have hb := frontier_budget hm rb (complementInput (U i)) C.gates.length (roots i)
      (hvalid i) (hfalse i) (fun w hw _ => hvalid i w hw)
    dsimp only [pools]
    omega
  have hdis : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint pools := by
    intro i _ j _ hij
    exact orPool_disjoint hm (hpair i j hij) C.gates.length
  have hsub : Finset.univ.biUnion pools ⊆ orGates C := by
    intro k hk
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.1 hk
    obtain ⟨hk, hop, _⟩ := mem_orPool.1 hi
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hk, hop⟩
  calc
    _ ≤ ∑ i, (pools i).card := Finset.sum_le_sum fun i _ => hlocal i
    _ = (Finset.univ.biUnion pools).card := (Finset.card_biUnion hdis).symm
    _ ≤ _ := Finset.card_le_card hsub

lemma grouped_or_budget {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {C : Circuit} (hm : Monotone2 C) (rb : ReadsBack n C)
    (U : ι → Finset (Fin n)) (roots : ι → Finset ℕ)
    (hvalid : ∀ i, ∀ w ∈ roots i, w < n + C.gates.length)
    (hfalse : ∀ i, ∀ w ∈ roots i, val C (List.ofFn (complementInput (U i))) w = false)
    (hpair : ∀ i j, i ≠ j → (U i ∩ U j).card ≤ 1) :
    (∑ i, (((roots i).biUnion (singletonSupport n C)).card - (roots i).card)) ≤
      (orGates C).card := by
  apply grouped_partial_or_budget hm rb U _ roots hvalid _ hfalse hpair
  intro i p hp
  obtain ⟨w, hw, hp⟩ := Finset.mem_biUnion.1 hp
  exact ⟨w, hw, mem_support.1 hp⟩

lemma partial_output_or_budget {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {C : Circuit} (hm : Monotone2 C) (rb : ReadsBack n C)
    (U S : ι → Finset (Fin n)) (output : ι → ℕ)
    (hvalid : ∀ i, output i < n + C.gates.length)
    (haccept : ∀ i, ∀ p ∈ S i, val C (List.ofFn (pairInput p p)) (output i) = true)
    (hfalse : ∀ i, val C (List.ofFn (complementInput (U i))) (output i) = false)
    (hpair : ∀ i j, i ≠ j → (U i ∩ U j).card ≤ 1) :
    (∑ i, ((S i).card - 1)) ≤ (orGates C).card := by
  have hb := grouped_partial_or_budget hm rb U S (fun i => {output i})
    (by intro i w hw; simpa only [Finset.mem_singleton.1 hw] using hvalid i)
    (by intro i p hp; exact ⟨output i, Finset.mem_singleton_self _, haccept i p hp⟩)
    (by intro i w hw; simpa only [Finset.mem_singleton.1 hw] using hfalse i) hpair
  simpa only [Finset.card_singleton] using hb

end PartialPointBudget


namespace PackedEval

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm

def gate (w : List ℕ) (g : Gate) : ℕ :=
  match g.op with
  | .and => (w.getD (g.inputs.getD 0 0) 0) &&& (w.getD (g.inputs.getD 1 0) 0)
  | .or => (w.getD (g.inputs.getD 0 0) 0) ||| (w.getD (g.inputs.getD 1 0) 0)
  | _ => 0

def wires (C : Circuit) (w : List ℕ) : List ℕ :=
  C.gates.foldl (fun w g => w ++ [gate w g]) w

def eval (C : Circuit) (w : List ℕ) : ℕ :=
  (wires C w).getD C.output 0

lemma testBit_getD (w : List ℕ) (r i : ℕ) :
    (w.getD i 0).testBit r = (w.map fun a => a.testBit r).getD i false := by
  induction w generalizing i with
  | nil => simp
  | cons a w ih =>
    cases i with
    | zero => simp
    | succ i => simpa using ih i

lemma gate_testBit (w : List ℕ) (g : Gate) (r : ℕ)
    (hop : g.op = .and ∨ g.op = .or) (hlen : g.inputs.length = 2) :
    (gate w g).testBit r =
      g.op.eval (g.inputs.map fun i => (w.map fun a => a.testBit r).getD i false) := by
  obtain ⟨a, b, hi⟩ := List.length_eq_two.mp hlen
  have ha := testBit_getD w r a
  have hb := testBit_getD w r b
  rcases hop with hop | hop
  · simpa [gate, hop, hi, GateOp.eval] using congrArg₂ (fun a b : Bool => a && b) ha hb
  · simpa [gate, hop, hi, GateOp.eval] using congrArg₂ (fun a b : Bool => a || b) ha hb

lemma fold_testBit (gs : List Gate) (w : List ℕ) (r : ℕ)
    (hgs : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) :
    (gs.foldl (fun w g => w ++ [gate w g]) w).map (fun a => a.testBit r) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (w.map fun a => a.testBit r) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have hg := hgs g (by simp)
    have hs : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 :=
      fun g h => hgs g (by simp [h])
    simp only [List.foldl_cons]
    rw [ih _ hs]
    simp only [List.map_append, List.map_cons, List.map_nil, gate_testBit w g r hg.1 hg.2]

lemma wires_testBit (C : Circuit) (w : List ℕ) (r : ℕ)
    (hC : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) :
    (wires C w).map (fun a => a.testBit r) = C.wires (w.map fun a => a.testBit r) :=
  fold_testBit C.gates w r hC

lemma eval_testBit (C : Circuit) (w : List ℕ) (r : ℕ)
    (hC : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) :
    (eval C w).testBit r = C.eval (w.map fun a => a.testBit r) := by
  rw [eval, testBit_getD, wires_testBit C w r hC]
  rfl

lemma eval_testBit_of_isAO2 (n : ℕ) (C : Circuit) (w : List ℕ) (r : ℕ)
    (hC : IsAO2 n C) :
    (eval C w).testBit r = C.eval (w.map fun a => a.testBit r) :=
  eval_testBit C w r (fun g hg => ⟨hC.1 g hg, hC.2.2 g hg⟩)

end PackedEval


namespace PackedColumns

def col : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, j =>
    if j < n then
      let v := col n j
      v ||| (v <<< (2 ^ n))
    else if j = n then
      ((2 ^ (2 ^ n) - 1) <<< (2 ^ n))
    else 0

lemma col_testBit (n j : ℕ) (hj : j < n) (r : ℕ) :
    (col n j).testBit r = (decide (r < 2 ^ n) && r.testBit j) := by
  induction n generalizing j r with
  | zero => omega
  | succ n ih =>
    have hp : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [pow_succ]; omega
    by_cases hjn : j < n
    · rw [col, ite_eq_left hjn]
      simp only [Nat.testBit_lor, Nat.testBit_shiftLeft, ih j hjn]
      by_cases hr : r < 2 ^ n
      · have hn : ¬ 2 ^ n ≤ r := by omega
        have hr' : r < 2 ^ (n + 1) := by omega
        simp [hr, hn, hr']
      · have hn : 2 ^ n ≤ r := by omega
        have he : r.testBit j = (r - 2 ^ n).testBit j := by
          have h := Nat.testBit_two_pow_add_gt hjn (r - 2 ^ n)
          rw [Nat.add_sub_of_le hn] at h
          exact h
        by_cases hr' : r < 2 ^ (n + 1)
        · have hd : r - 2 ^ n < 2 ^ n := by omega
          simp [hr, hn, hr', hd, he]
        · have hd : ¬ r - 2 ^ n < 2 ^ n := by omega
          simp [hr, hn, hr', hd]
    · have he : j = n := by omega
      subst j
      simp only [col, Nat.lt_irrefl, ite_false, ite_true,
        Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
      by_cases hr : r < 2 ^ n
      · have hn : ¬ 2 ^ n ≤ r := by omega
        have hb := Nat.testBit_lt_two_pow hr
        simp [hn, hb]
      · have hn : 2 ^ n ≤ r := by omega
        by_cases hr' : r < 2 ^ (n + 1)
        · have hd : r - 2 ^ n < 2 ^ n := by omega
          have hb := Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt hn hr'
          simp [hn, hr', hd, hb]
        · have hd : ¬ r - 2 ^ n < 2 ^ n := by omega
          simp [hn, hr', hd]

lemma col_testBit_lt (n j r : ℕ) (hj : j < n) (hr : r < 2 ^ n) :
    (col n j).testBit r = r.testBit j := by
  simp [col_testBit n j hj r, hr]

lemma col_testBit_ge (n j r : ℕ) (hj : j < n) (hr : 2 ^ n ≤ r) :
    (col n j).testBit r = false := by
  simp [col_testBit n j hj r, Nat.not_lt_of_ge hr]

lemma col_lt (n j : ℕ) (hj : j < n) : col n j < 2 ^ (2 ^ n) := by
  apply Nat.lt_pow_two_of_testBit
  intro r hr
  exact col_testBit_ge n j r hj hr

lemma col_eq_zero (n j : ℕ) (hj : n ≤ j) : col n j = 0 := by
  cases n with
  | zero => rfl
  | succ n =>
    have hlt : ¬ j < n := by omega
    have hne : j ≠ n := by omega
    simp [col, hlt, hne]

lemma col_testBit_all (n j r : ℕ) :
    (col n j).testBit r = (decide (j < n) && decide (r < 2 ^ n) && r.testBit j) := by
  by_cases hj : j < n
  · simp [col_testBit n j hj r, hj]
  · simp [col_eq_zero n j (by omega), hj]

end PackedColumns


namespace PackedLineColumns

def joinWords (ws : List Nat) : Nat := ws.foldr (· ||| ·) 0

lemma joinWords_bit (ws : List Nat) (r : Nat) :
    (joinWords ws).testBit r = ws.any (fun w => w.testBit r) := by
  induction ws with
  | nil => simp [joinWords]
  | cons w ws ih => simpa [joinWords, Nat.testBit_lor] using congrArg (fun b => w.testBit r || b) ih

def lineWord {n m : Nat} (I : Fin n → Fin m → Prop) [DecidableRel I]
    (cols : Fin n → Nat) (l : Fin m) : Nat :=
  Nat.ldiff (2 ^ (2 ^ n) - 1) (joinWords (List.ofFn (fun p => if I p l then cols p else 0)))

lemma lineWord_bit {n m : Nat} (I : Fin n → Fin m → Prop) [DecidableRel I]
    (cols : Fin n → Nat) (r : Fin (2 ^ n)) (l : Fin m)
    (hc : ∀ p : Fin n, (cols p).testBit r.val = r.val.testBit p.val) :
    (lineWord I cols l).testBit r.val =
      decide (∀ p : Fin n, I p l → r.val.testBit p.val = false) := by
  have hnot (b : Bool) : (!b) = true ↔ b = false := by cases b <;> decide
  apply Bool.eq_iff_iff.mpr
  simp only [lineWord, Nat.testBit_ldiff, Nat.testBit_two_pow_sub_one, r.isLt,
    decide_true, Bool.true_and, joinWords_bit, hnot, decide_eq_true_eq,
    List.any_eq_false, List.forall_mem_ofFn_iff]
  constructor
  · intro h p hp
    simpa [hp, hc] using h p
  · intro h p
    by_cases hp : I p l
    · simp [hp, hc, h p hp]
    · simp [hp]

end PackedLineColumns


namespace PackedInputCode

def code {n : Nat} (x : Fin n → Bool) : Fin (2 ^ n) :=
  ⟨(BitVec.ofBoolListLE (List.ofFn x)).toNat, by
    simpa using (BitVec.ofBoolListLE (List.ofFn x)).isLt⟩

lemma code_bit {n : Nat} (x : Fin n → Bool) (i : Fin n) :
    (code x).val.testBit i.val = x i := by
  unfold code
  rw [BitVec.testBit_toNat, BitVec.getLsbD_ofBoolListLE]
  simp [List.getD_eq_getElem?_getD]

end PackedInputCode


namespace PackedBoundary

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.Outside.L_meta_2583.ReducedCheck
open PEqualNP.Outside.L_meta_2583.CircuitCheckWrapper

lemma input_bits {n m : ℕ} (I : Fin n → Fin m → Prop) [DecidableRel I]
    (w : List ℕ) (hlen : w.length = n + m)
    (hpoint : ∀ (r : Fin (2 ^ n)) (p : Fin n),
      (w.getD p.val 0).testBit r.val = r.val.testBit p.val)
    (hline : ∀ (r : Fin (2 ^ n)) (l : Fin m),
      (w.getD (n + l.val) 0).testBit r.val =
        decide (∀ p : Fin n, I p l → r.val.testBit p.val = false))
    (P : Finset (Fin n)) :
    w.map (fun a => a.testBit (PackedInputCode.code (fun p => decide (p ∈ P))).val) =
      List.ofFn (liftInput (independentInput I P)) := by
  let r := PackedInputCode.code (fun p => decide (p ∈ P))
  have hwire : ∀ i : Fin (n + m), (w.getD i.val 0).testBit r.val =
      liftInput (independentInput I P) i := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro p
      simpa [r, liftInput, independentInput] using
        (hpoint r p).trans (PackedInputCode.code_bit (fun p => decide (p ∈ P)) p)
    · intro l
      have hwline : (w.getD (n + l.val) 0).testBit r.val =
          decide (l ∈ avoidingRight I P) := by
        rw [hline r l]
        congr 1
        apply propext
        rw [mem_avoidingRight]
        constructor
        · intro h p hp hI
          have hf := h p hI
          simpa [r, PackedInputCode.code_bit, hp] using hf
        · intro h p hI
          have hp : p ∉ P := fun hp => h p hp hI
          simp [r, PackedInputCode.code_bit, hp]
      simpa [liftInput, independentInput] using hwline
  apply List.ext_getElem
  · simpa using hlen
  · intro i hi hj
    have hwi : i < w.length := by simpa using hi
    have hib : i < n + m := by simpa [hlen] using hwi
    simpa [List.getD_eq_getElem?_getD, hwi] using hwire ⟨i, hib⟩

lemma independent_false_of_packed_zero {n m : ℕ} (I : Fin n → Fin m → Prop)
    [DecidableRel I] (C : Circuit) (hAO : IsAO2 (n + m) C)
    (w : List ℕ) (hlen : w.length = n + m)
    (hpoint : ∀ (r : Fin (2 ^ n)) (p : Fin n),
      (w.getD p.val 0).testBit r.val = r.val.testBit p.val)
    (hline : ∀ (r : Fin (2 ^ n)) (l : Fin m),
      (w.getD (n + l.val) 0).testBit r.val =
        decide (∀ p : Fin n, I p l → r.val.testBit p.val = false))
    (hzero : PackedEval.eval C w = 0) :
    ∀ P : Finset (Fin n), circuitFun (n + m) C (liftInput (independentInput I P)) = false := by
  intro P
  have h := PackedEval.eval_testBit_of_isAO2 (n + m) C w
    (PackedInputCode.code (fun p => decide (p ∈ P))).val hAO
  rw [hzero, input_bits I w hlen hpoint hline P] at h
  simpa [circuitFun] using h.symm

end PackedBoundary
end PEqualNP.Outside.L_meta_2583
